import os
import re
import sys
import time
import uuid
import locale
import shutil
import atexit
import sqlite3
import threading
import subprocess
import collections
import urllib.parse

from functools import lru_cache


class DiagnosticCollector(object):
    """Collects structured diagnostic information during package resolution."""

    def __init__(self):
        self.entry_failures = []
        self.missing_deps = []
        self.unavailable = []
        self.conflicts = []
        self.xor_violations = []
        self.unsat_core = []
        self.candidate_versions = {}
        self.rejection_reasons = []
        self.downgrades = []  # [(pkg, skipped_versions, chosen_version, reasons)]

    def _append_unique(self, collection, item):
        if item not in collection:
            collection.append(item)

    def add_entry_failure(self, pkg, versions_tried, reason):
        # Keep only the latest (most complete) failure per package
        self.entry_failures = [(p, v, r) for p, v, r in self.entry_failures if p != pkg]
        self.entry_failures.append((pkg, list(versions_tried), reason))

    def add_downgrade(self, pkg, skipped_versions, chosen_version, reasons):
        # Keep only the latest downgrade per package (progressive solve calls multiple times)
        self.downgrades = [(p, s, c, r) for p, s, c, r in self.downgrades if p != pkg]
        self.downgrades.append((pkg, list(skipped_versions), chosen_version, list(reasons)))

    def add_missing_dep(self, requester_pkg, requester_ver, dep_name, dep_cons=None):
        self._append_unique(self.missing_deps, (requester_pkg, requester_ver, dep_name, dep_cons))

    def add_unavailable(self, pkg, ver, required_by, required_cons=None):
        self._append_unique(self.unavailable, (pkg, ver, required_by, required_cons))

    def add_conflict(self, pkg_a, ver_a, pkg_b, ver_b, reason="ban"):
        self._append_unique(self.conflicts, (pkg_a, ver_a, pkg_b, ver_b, reason))

    def add_xor_violation(self, pkg, ver, xor_group, matched_count):
        self._append_unique(self.xor_violations, (pkg, ver, list(xor_group), matched_count))

    def add_unsat_core_entry(self, pkg, ver):
        self._append_unique(self.unsat_core, (pkg, ver))

    def set_candidate_versions(self, visited):
        self.candidate_versions = {pkg: list(vers) for pkg, vers in visited.items()}

    def add_rejection(self, solution, reason):
        # Deduplicate by reason string (same root cause)
        for _, existing_reason in self.rejection_reasons:
            if existing_reason == reason:
                return
        self.rejection_reasons.append((collections.OrderedDict(solution), reason))

    def has_diagnostics(self):
        return bool(
            self.entry_failures
            or self.missing_deps
            or self.unavailable
            or self.conflicts
            or self.xor_violations
            or self.unsat_core
            or self.rejection_reasons
        )

    def _format_constraint(self, constraint):
        if not constraint:
            return ""
        if isinstance(constraint, (list, tuple)):
            parts = []
            for item in constraint:
                if isinstance(item, (list, tuple)) and len(item) >= 3:
                    flag, tags, path = item[:3]
                    if path:
                        parts.append("@{}".format(path))
                    elif flag and tags is not None:
                        parts.append("{}{}".format(flag, tags))
                    elif tags is not None:
                        parts.append(str(tags))
                    else:
                        parts.append("any version")
                else:
                    parts.append(str(item))
            return ", ".join(parts)
        return str(constraint)

    def _format_versions(self, versions):
        return ", ".join(str(ver) for ver in versions)

    def format_report(self, verbose=False):
        """Format diagnostics into human-readable report for stderr.

        verbose=False (- mode): concise summary of root cause only.
        verbose=True  (+ mode): full conflict analysis with all details.
        """
        lines = [""]

        if self.entry_failures:
            if verbose:
                lines.append("[Entry Package Failures]")
            for pkg, versions, reason in self.entry_failures:
                if verbose:
                    lines.append("  Package '{}' cannot be satisfied:".format(pkg))
                    if versions:
                        if len(versions) > 5:
                            shown = self._format_versions(versions[:5])
                            lines.append("    Candidate versions: {} ... ({} total)".format(shown, len(versions)))
                        else:
                            lines.append("    Candidate versions: {}".format(self._format_versions(versions)))
                    else:
                        lines.append("    No candidate versions found in any package path")
                    available_versions = self.candidate_versions.get(pkg, []) if self.candidate_versions else []
                    if available_versions:
                        if len(available_versions) > 5:
                            shown = self._format_versions(available_versions[:5])
                            lines.append(
                                "    Available versions: {} ... ({} total)".format(shown, len(available_versions))
                            )
                        else:
                            lines.append("    Available versions: {}".format(self._format_versions(available_versions)))
                    reason_parts = reason.split("; ")
                    unique_reasons = {}
                    version_set = set(str(v) for v in versions)
                    for part in reason_parts:
                        parts = part.split(" ", 1)
                        if len(parts) == 2 and parts[0] in version_set:
                            r = parts[1]
                            if r not in unique_reasons:
                                unique_reasons[r] = []
                            unique_reasons[r].append(parts[0])
                        else:
                            unique_reasons[part] = []
                    for r, vers in unique_reasons.items():
                        if vers and len(vers) > 3:
                            lines.append("    {} (all {} versions)".format(r, len(vers)))
                        elif vers:
                            lines.append("    {} ({})".format(r, ", ".join(vers)))
                        else:
                            lines.append("    {}".format(r))
                else:
                    if versions:
                        lines.append(
                            "  -> '{}' no satisfiable version (tried: {})".format(
                                pkg, ", ".join(str(v) for v in versions[:3])
                            )
                        )
                    else:
                        lines.append("  -> '{}' not found in any package path".format(pkg))

        if self.unsat_core:
            if verbose:
                lines.append("")
                lines.append("[Conflict Core]")
                lines.append("  The following package selections cannot coexist:")
                for pkg, ver in self.unsat_core:
                    lines.append("  - {} = {}".format(pkg, ver))
            else:
                core_str = ", ".join("{}={}".format(p, v) for p, v in self.unsat_core[:5])
                lines.append("  -> Conflict core: {}".format(core_str))

        if self.missing_deps:
            if verbose:
                lines.append("")
                lines.append("[req() - Missing Dependencies]")
                for req_pkg, req_ver, dep_name, dep_cons in self.missing_deps:
                    cons_str = self._format_constraint(dep_cons)
                    cons_str = " {}".format(cons_str) if cons_str else ""
                    lines.append("  {}/{} declares req('{}{}')".format(req_pkg, req_ver, dep_name, cons_str))
                    lines.append("    -> No matching version found; no alt() provider available")
            else:
                for req_pkg, req_ver, dep_name, dep_cons in self.missing_deps[:3]:
                    cons_str = self._format_constraint(dep_cons)
                    cons_str = "({})".format(cons_str) if cons_str else ""
                    lines.append(
                        "  -> [req] {}/{} req('{}'{}) - not found".format(
                            req_pkg, req_ver, dep_name, " {}".format(cons_str) if cons_str else ""
                        )
                    )
                if len(self.missing_deps) > 3:
                    lines.append("  -> ... and {} more unresolved req()".format(len(self.missing_deps) - 3))

        if self.unavailable:
            if verbose:
                lines.append("")
                lines.append("[ava() - Availability Not Satisfied]")
                by_required = collections.OrderedDict()
                for pkg, ver, required_by, required_cons in self.unavailable:
                    if required_by not in by_required:
                        by_required[required_by] = []
                    by_required[required_by].append((pkg, ver, required_cons))
                for required_by, dependents in by_required.items():
                    lines.append("  '{}' is not in the resolved set, but declared via ava():".format(required_by))
                    for pkg, ver, required_cons in dependents[:5]:
                        cons_str = self._format_constraint(required_cons)
                        if cons_str and cons_str != "any version":
                            lines.append("    - {}/{} ava('{}{}')".format(pkg, ver, required_by, cons_str))
                        else:
                            lines.append("    - {}/{} ava('{}')".format(pkg, ver, required_by))
                    if len(dependents) > 5:
                        lines.append("    ... and {} more packages".format(len(dependents) - 5))
            else:
                by_required = {}
                for pkg, ver, required_by, _ in self.unavailable:
                    if required_by not in by_required:
                        by_required[required_by] = 0
                    by_required[required_by] += 1
                for required_by, count in list(by_required.items())[:3]:
                    lines.append(
                        "  -> [ava] '{}' not present ({} package{} declare ava('{}'))".format(
                            required_by, count, "s" if count > 1 else "", required_by
                        )
                    )
                if len(by_required) > 3:
                    lines.append("  -> ... and {} more unmet ava()".format(len(by_required) - 3))

        if self.conflicts:
            if verbose:
                lines.append("")
                lines.append("[ban() - Package Conflicts]")
                for pkg_a, ver_a, pkg_b, ver_b, reason in self.conflicts:
                    lines.append("  {}/{} declares ban('{}')".format(pkg_a, ver_a, pkg_b))
                    lines.append("    -> but {}/{} is selected in the solution".format(pkg_b, ver_b))
            else:
                for pkg_a, ver_a, pkg_b, ver_b, reason in self.conflicts[:3]:
                    lines.append(
                        "  -> [ban] {}/{} ban('{}') - but {}/{} is selected".format(pkg_a, ver_a, pkg_b, pkg_b, ver_b)
                    )
                if len(self.conflicts) > 3:
                    lines.append("  -> ... and {} more ban() conflicts".format(len(self.conflicts) - 3))

        if self.xor_violations:
            if verbose:
                lines.append("")
                lines.append("[xor() - Exclusive-OR Violations]")
                for pkg, ver, xor_group, matched in self.xor_violations:
                    lines.append("  {}/{} declares xor({})".format(pkg, ver, ", ".join(str(g) for g in xor_group)))
                    lines.append("    -> Expected exactly 1 match, got {}".format(matched))
            else:
                for pkg, ver, xor_group, matched in self.xor_violations[:2]:
                    lines.append(
                        "  -> [xor] {}/{} xor({}) expects 1 match, got {}".format(
                            pkg, ver, ", ".join(str(g) for g in xor_group), matched
                        )
                    )

        if verbose:
            if self.rejection_reasons:
                lines.append("")
                lines.append("[Solution Rejection Details]")
                for sol, reason in self.rejection_reasons[:10]:
                    pkgs_str = ", ".join("{}={}".format(k, v) for k, v in list(sol.items())[:6])
                    suffix = "..." if len(sol) > 6 else ""
                    lines.append("  Solution ({}{}): {}".format(pkgs_str, suffix, reason))
                if len(self.rejection_reasons) > 10:
                    lines.append("  ... and {} more rejected solutions".format(len(self.rejection_reasons) - 10))

            if self.candidate_versions:
                relevant_pkgs = set()
                for pkg, _, _ in self.entry_failures:
                    relevant_pkgs.add(pkg)
                for _, _, dep_name, _ in self.missing_deps:
                    relevant_pkgs.add(dep_name)
                for pkg, ver, req_by, _ in self.unavailable:
                    relevant_pkgs.add(pkg)
                    relevant_pkgs.add(req_by)
                for pkg_a, _, pkg_b, _, _ in self.conflicts:
                    relevant_pkgs.add(pkg_a)
                    relevant_pkgs.add(pkg_b)
                if not relevant_pkgs:
                    relevant_pkgs = set(self.candidate_versions.keys())
                filtered = {k: v for k, v in self.candidate_versions.items() if k in relevant_pkgs}
                if filtered:
                    lines.append("")
                    lines.append("[Candidate Versions]")
                    for pkg, vers in sorted(filtered.items()):
                        rendered = self._format_versions(vers) if vers else "<none>"
                        lines.append("  {}: {}".format(pkg, rendered))
        else:
            if not any(
                [
                    self.entry_failures,
                    self.missing_deps,
                    self.unavailable,
                    self.conflicts,
                    self.xor_violations,
                    self.unsat_core,
                ]
            ):
                lines.append("  -> No single root cause identified; constraints are collectively unsatisfiable")
            lines.append("  Use '+' separator for full conflict analysis.")

        lines.append("")
        return "\n".join(lines)


class Solver(object):
    def __init__(self, parent, config, environ):
        self.parent = parent
        self.config = config
        self.environ = environ
        self.diagnostics = DiagnosticCollector()
        self.enable_sat = False
        try:
            import pysat

            storage_path = environ(config.Env.STORAGE_PATH).getenv()
            if storage_path:
                environ(config.Env.PACKAGE_PATH).insert(storage_path)
            self.enable_sat = True
        except Exception:
            self.enable_sat = False

    def _diagnostics(self):
        if not hasattr(self, "diagnostics") or self.diagnostics is None:
            self.diagnostics = DiagnosticCollector()
        return self.diagnostics

    def _collect_candidate_versions(self, original_visited):
        candidate_versions = collections.OrderedDict((pkg, list(vers)) for pkg, vers in original_visited.items())
        package_state = getattr(self.parent, "package_state", {})
        available_versions = package_state.get("available", {}) if package_state else {}
        for name, vers in available_versions.items():
            if name not in candidate_versions or not candidate_versions[name]:
                candidate_versions[name] = list(vers)
        for provider_pkg, ver_dict in self.parent.filters.get("alt", {}).items():
            for _, raw_alt in ver_dict.items():
                for pkgs in raw_alt:
                    name, _, _, _ = self.parent.resolve_argv(pkgs)
                    if not candidate_versions.get(name):
                        candidate_versions[name] = []
                    provider_info = "{}@{}".format(pkgs, provider_pkg)
                    if provider_info not in candidate_versions[name]:
                        candidate_versions[name].append(provider_info)
        return candidate_versions

    def collect_verbose_info(self, original_visited):
        diagnostics = self._diagnostics()
        if self.config.VERBOSE == "+":
            diagnostics.set_candidate_versions(self._collect_candidate_versions(original_visited))

        package_graph = getattr(self.parent, "package_graph", {})
        graphed = package_graph.get("graphed", {})
        package_state = getattr(self.parent, "package_state", {})
        initial_names = set(package_state.get("init", [])) if package_state else set()

        for pkg, vers in original_visited.items():
            if not vers and (not initial_names or pkg in initial_names):
                diagnostics.add_entry_failure(
                    pkg,
                    [],
                    "No candidate versions were found after applying the requested constraints.",
                )
                continue

            for ver in vers:
                current_meta = graphed.get(pkg, {}).get(ver, {})

                req_relations = self.parent.resolve_filter(pkg, ver, "req")
                raw_reqs = current_meta.get("req", [])
                all_req_cons = self.parent.combine_argv([{s: self.parent.resolve_argv(s)} for s in raw_reqs])
                for dep_name, dep_tags in req_relations.items():
                    if dep_tags:
                        continue
                    dep_cons = all_req_cons.get(dep_name)
                    alt_providers = False
                    if dep_cons:
                        alt_providers = self.check_alt_providers(dep_name, dep_cons, original_visited)
                    if not alt_providers:
                        diagnostics.add_missing_dep(pkg, ver, dep_name, dep_cons)

                ava_relations = self.parent.resolve_filter(pkg, ver, "ava")
                raw_ava = current_meta.get("ava", [])
                all_ava_cons = self.parent.combine_argv([{s: self.parent.resolve_argv(s)} for s in raw_ava])
                if ava_relations:
                    unsatisfied_ava = []
                    found_ava_satisfier = False
                    for dep_name, dep_tags in ava_relations.items():
                        dep_cons = all_ava_cons.get(dep_name)
                        if dep_tags:
                            found_ava_satisfier = True
                            break
                        alt_providers = False
                        if dep_cons:
                            alt_providers = self.check_alt_providers(dep_name, dep_cons, original_visited)
                        if alt_providers:
                            found_ava_satisfier = True
                            break
                        unsatisfied_ava.append((dep_name, dep_cons))
                    if not found_ava_satisfier:
                        for dep_name, dep_cons in unsatisfied_ava:
                            diagnostics.add_unavailable(pkg, ver, dep_name, dep_cons)

                ban_relations = self.parent.resolve_filter(pkg, ver, "ban")
                for dep_name, dep_tags in ban_relations.items():
                    for dep_ver in dep_tags:
                        diagnostics.add_conflict(pkg, ver, dep_name, dep_ver, "ban constraint")

                xor_relations = self.parent.resolve_filter(pkg, ver, "xor")
                raw_xor = current_meta.get("exor", [])
                for xor_group in raw_xor:
                    matched_count = 0
                    for xor_pkg_string in xor_group:
                        xor_pkg_name, flag, xor_tags, path = self.parent.resolve_argv(xor_pkg_string)
                        matched_count += len(xor_relations.get(xor_pkg_name, []))
                        dep_cons = [(flag, xor_tags, path)]
                        if self.check_alt_providers(xor_pkg_name, dep_cons, original_visited):
                            matched_count += 1
                    if xor_group and matched_count == 0:
                        diagnostics.add_xor_violation(pkg, ver, xor_group, matched_count)

    def check_alt_providers(self, dep_name, dep_cons, original_visited):
        for provider_pkg, ver_dict in self.parent.filters["alt"].items():
            if provider_pkg not in original_visited:
                continue
            for provider_ver, _ in ver_dict.items():
                if provider_ver not in original_visited[provider_pkg]:
                    continue
                alt_cons_map = self.parent.resolve_filter(provider_pkg, provider_ver, "alt")
                if dep_name not in alt_cons_map:
                    continue
                alt_cons = alt_cons_map[dep_name]
                if self.parent.rules_compatible(dep_cons, alt_cons):
                    return True
        return False

    def collect_alt_providers(self, dep_name, dep_cons, var_map, rel_var_map):
        substitutes = []
        for provider_pkg, ver_dict in self.parent.filters["alt"].items():
            for provider_ver, _ in ver_dict.items():
                if (provider_pkg, provider_ver) not in rel_var_map:
                    continue
                alt_cons_map = rel_var_map[(provider_pkg, provider_ver)]["alt"]
                if dep_name not in alt_cons_map:
                    continue
                alt_cons = alt_cons_map[dep_name]
                if self.parent.rules_compatible(dep_cons, alt_cons):
                    satisfier_var = var_map.get((provider_pkg, provider_ver))
                    if satisfier_var:
                        substitutes.append(satisfier_var)
        return list(set(substitutes))

    def record_sat_unsat_core(self, core, rev_var_map):
        if not core:
            return []
        core_entries = []
        for literal in core:
            pkg_ver = rev_var_map.get(abs(literal))
            if not pkg_ver:
                continue
            pkg, ver = pkg_ver
            self._diagnostics().add_unsat_core_entry(pkg, ver)
            core_entries.append((pkg, ver))
        return core_entries

    def get_sat_core(self, sat_solver):
        try:
            return sat_solver.get_core()
        except Exception:
            return []

    def describe_sat_core(self, core, rev_var_map):
        core_entries = self.record_sat_unsat_core(core, rev_var_map)
        return ["{}={}".format(pkg, ver) for pkg, ver in core_entries]

    def _infer_version_failure(self, pkg, ver, rel_var_map, locked_solution):
        """Infer why a specific version cannot be selected when unsat core is empty."""
        if not rel_var_map:
            return "has unsatisfiable constraints"
        rels = rel_var_map.get((pkg, ver))
        if not rels:
            return "has unsatisfiable constraints"
        # Check ava: are required packages missing from visited?
        ava_issues = []
        for dep_name, dep_tags in rels.get("ava", {}).items():
            if not dep_tags:
                ava_issues.append(dep_name)
        if ava_issues:
            return "needs {} present".format(", ".join("'{}'".format(a) for a in ava_issues))
        # Check req: are required deps missing?
        req_issues = []
        for dep_name, dep_tags in rels.get("req", {}).items():
            if not dep_tags:
                req_issues.append(dep_name)
        if req_issues:
            return "requires {} (not available)".format(", ".join("'{}'".format(r) for r in req_issues))
        # Check ban: does it conflict with locked entries?
        ban_issues = []
        for dep_name, dep_tags in rels.get("ban", {}).items():
            if dep_name in locked_solution and locked_solution[dep_name] in dep_tags:
                ban_issues.append("{}={}".format(dep_name, locked_solution[dep_name]))
        if ban_issues:
            return "conflicts with {}".format(", ".join(ban_issues))
        return "has dependencies with unsatisfiable constraints (see below)"

    def collect_sat_unsat_core(self, constraints, assumptions, rev_var_map):
        from pysat.solvers import Solver as SATSolver

        with SATSolver(bootstrap_with=constraints) as sat_solver:
            if sat_solver.solve(assumptions=assumptions or []):
                return []
            return self.record_sat_unsat_core(self.get_sat_core(sat_solver), rev_var_map)

    def collect_limit_versions(self, visited, max_versions_limit, min_versions_limit, level_info):
        result = dict()
        for pkg, vers in visited.items():
            sorted_vers = self.parent.custom_sort(vers)
            level_data = level_info.get(pkg, 0) if level_info else 0
            if isinstance(level_data, tuple):
                level, position = level_data
            else:
                level, position = level_data, 0
            keep_count = max(min_versions_limit, max_versions_limit // (2**level))
            if level == 0 and position > 0:
                entry_penalty = min(position, max(0, keep_count - min_versions_limit))
                keep_count -= entry_penalty
            result[pkg] = sorted_vers[-keep_count:]
        return result

    def collect_progressively_solve(self, entry_names, solver_function, fallback_solver_function=None):
        try:
            max_versions_limit = int(self.environ(self.config.Env.PACKAGE_TAGS).getenv())
        except (AttributeError, TypeError):
            max_versions_limit = 10
        min_versions_limit = max(1, max_versions_limit // 2)

        if fallback_solver_function is None:
            fallback_solver_function = solver_function

        original_visited = self.parent.package_graph["visited"]
        levels = self.build_levels(entry_names, original_visited)
        solution_weights = self.build_solution_weights(entry_names, levels, original_visited)
        best_solution = None
        best_objective = None
        optimal_signature = self.build_solution_signature(None, entry_names, original_visited)

        for n in range(min_versions_limit, max_versions_limit + 1):
            visited_subset = self.collect_limit_versions(
                original_visited,
                n,
                min_versions_limit,
                level_info=levels,
            )
            solution = solver_function(entry_names, visited=visited_subset)
            if solution:
                objective = self.build_solution_objective(
                    solution,
                    entry_names,
                    levels,
                    original_visited,
                    solution_weights=solution_weights,
                )
                if best_objective is None or objective > best_objective:
                    best_solution = solution
                    best_objective = objective
                if objective[0] == optimal_signature:
                    return solution
        if best_solution:
            return best_solution
        solution = fallback_solver_function(entry_names, visited=original_visited)
        if solution:
            return solution
        self.collect_verbose_info(original_visited)

    def collect_solution(self, entry_names):
        self.diagnostics = DiagnosticCollector()
        if self.enable_sat:
            best_solution = self.collect_progressively_solve(entry_names, self.build_solution_sat)
        else:
            best_solution = self.collect_progressively_solve(entry_names, self.build_solution_dfs)
        return best_solution

    def build_solution_sat(self, entry_names, visited):
        from pysat.formula import WCNF
        from pysat.examples.rc2 import RC2

        var_map, rev_var_map, rel_var_map = self.build_map_data(visited)
        constraints = self.build_constraints(entry_names, var_map, rel_var_map, visited)
        levels = self.build_levels(entry_names, visited)
        locked_entries = self.build_entry_solution_sat(
            entry_names, visited, var_map, constraints, rev_var_map, rel_var_map
        )
        if locked_entries is None:
            return None
        entry_assumptions = [var_map[(pkg, ver)] for pkg, ver in locked_entries.items() if (pkg, ver) in var_map]
        feasible_tail_versions = self.build_feasible_solution_versions_sat(
            visited,
            var_map,
            constraints,
            assumptions=entry_assumptions,
            package_names=[pkg for pkg in visited if pkg not in entry_names and len(visited.get(pkg, [])) > 1],
        )
        solution_weights = self.build_tail_solution_weights(
            entry_names,
            levels,
            visited,
            feasible_versions=feasible_tail_versions,
        )

        if not solution_weights:
            model = self.build_sat_model(constraints, assumptions=entry_assumptions)
            if model is None:
                self.collect_sat_unsat_core(constraints, entry_assumptions, rev_var_map)
            return self.build_solution_from_model(model, rev_var_map, entry_names, rel_var_map, levels)

        wcnf = WCNF()
        for clause in constraints:
            wcnf.append(clause)
        for assumption in entry_assumptions:
            wcnf.append([assumption])
        soft_weights = self.build_solution_softweights(var_map, solution_weights)
        for (pkg, ver), var in var_map.items():
            if var in soft_weights:
                wcnf.append([var], soft_weights[var])
        with RC2(wcnf) as rc2_solver:
            model = rc2_solver.compute()
            if model is None:
                self.collect_sat_unsat_core(constraints, entry_assumptions, rev_var_map)
            return self.build_solution_from_model(model, rev_var_map, entry_names, rel_var_map, levels)

    def build_sat_model(self, constraints, assumptions=None):
        from pysat.solvers import Solver as SATSolver

        with SATSolver(bootstrap_with=constraints) as sat_solver:
            if sat_solver.solve(assumptions=assumptions or []):
                return sat_solver.get_model()

    def build_solution_from_model(self, model, rev_var_map, entry_names, rel_var_map, levels):
        if model is None:
            return None
        solution = collections.OrderedDict()
        for idx in model:
            if idx > 0 and idx in rev_var_map:
                pkg, ver = rev_var_map[idx]
                solution[pkg] = ver
        solution = self.build_prune_solution(solution, entry_names, rel_var_map)
        solution = self.build_sort_solution(solution, levels)
        return solution

    def build_feasible_solution_versions_sat(self, visited, var_map, constraints, assumptions=None, package_names=None):
        from pysat.solvers import Solver as SATSolver

        if package_names is None:
            package_names = visited.keys()
        package_names = set(package_names)
        feasible_versions = {}
        with SATSolver(bootstrap_with=constraints) as sat_solver:
            base_assumptions = assumptions or []
            for pkg, versions in visited.items():
                if pkg not in package_names:
                    continue
                allowed_versions = []
                for version in self.parent.custom_sort(versions):
                    sat_var = var_map.get((pkg, version))
                    if sat_var is None:
                        continue
                    if sat_solver.solve(assumptions=base_assumptions + [sat_var]):
                        allowed_versions.append(version)
                feasible_versions[pkg] = allowed_versions
        return feasible_versions

    def build_entry_solution_sat(self, entry_names, visited, var_map, constraints, rev_var_map=None, rel_var_map=None):
        from pysat.solvers import Solver as SATSolver

        if rev_var_map is None:
            rev_var_map = {var: pkg_ver for pkg_ver, var in var_map.items()}
        locked_solution = collections.OrderedDict()
        assumptions = []
        with SATSolver(bootstrap_with=constraints) as sat_solver:
            for name in entry_names:
                versions = self.parent.custom_sort(visited.get(name, []))
                if not versions:
                    self._diagnostics().add_entry_failure(
                        name, [], "No candidate versions found for this entry package."
                    )
                    return None
                chosen_version = None
                tried_versions = []
                version_reasons = []
                for version in reversed(versions):
                    tried_versions.append(version)
                    sat_var = var_map.get((name, version))
                    if sat_var is None:
                        version_reasons.append("{} is not present in the SAT variable map".format(version))
                        continue
                    if sat_solver.solve(assumptions=assumptions + [sat_var]):
                        assumptions.append(sat_var)
                        locked_solution[name] = version
                        chosen_version = version
                        # Warn if we skipped higher versions (downgrade)
                        if tried_versions[:-1]:  # there were skipped versions before this one
                            skipped = tried_versions[:-1]
                            reasons_for_skipped = version_reasons[: len(skipped)]
                            self._diagnostics().add_downgrade(name, skipped, chosen_version, reasons_for_skipped)
                        break
                    core_description = self.describe_sat_core(self.get_sat_core(sat_solver), rev_var_map)
                    # Filter out self-references from core (not useful)
                    core_description = [c for c in core_description if not c.startswith("{}=".format(name))]
                    if core_description:
                        version_reasons.append("{} conflicts with {}".format(version, ", ".join(core_description)))
                    else:
                        # Try to infer reason from package relations
                        inferred = self._infer_version_failure(name, version, rel_var_map, locked_solution)
                        version_reasons.append("{} {}".format(version, inferred))
                if chosen_version is None:
                    reason = "; ".join(version_reasons)
                    if not reason:
                        reason = "All candidate versions conflict with already locked entries or package constraints."
                    self._diagnostics().add_entry_failure(name, tried_versions, reason)
                    return None
        return locked_solution

    def build_map_data(self, visited):
        idx = 1
        var_map, rev_var_map, rel_var_map = {}, {}, {}
        for pkg, vers in visited.items():
            for ver in vers:
                var_map[(pkg, ver)] = idx
                rev_var_map[idx] = (pkg, ver)
                rel_var_map[(pkg, ver)] = {
                    "req": self.parent.resolve_filter(pkg, ver, "req"),
                    "ava": self.parent.resolve_filter(pkg, ver, "ava"),
                    "ban": self.parent.resolve_filter(pkg, ver, "ban"),
                    "alt": self.parent.resolve_filter(pkg, ver, "alt"),
                    "xor": self.parent.resolve_filter(pkg, ver, "xor"),
                }
                idx += 1
        return var_map, rev_var_map, rel_var_map

    def build_solution_weight(self, pkg, ver, levels, visited):
        sorted_vers = self.parent.custom_sort(visited.get(pkg, []))
        rank = sorted_vers.index(ver)
        lvl, pos = levels.get(pkg)
        return (100 - pos) * 10000 + (100 - lvl) * 100 + rank

    def build_solution_steps(self, entry_names, levels, visited):
        base_bound = 0
        for pkg, vers in visited.items():
            if pkg not in levels:
                continue
            if not vers:
                continue
            pkg_bound = max(self.build_solution_weight(pkg, ver, levels, visited) for ver in vers)
            base_bound += pkg_bound

        steps = {}
        tail_bound = base_bound
        for name in reversed(entry_names):
            versions = visited.get(name, [])
            max_rank = max(len(versions) - 1, 0)
            step = tail_bound + 1
            steps[name] = step
            tail_bound += step * max_rank
        return steps

    def build_solution_weights(self, entry_names, levels, visited):
        steps = self.build_solution_steps(entry_names, levels, visited)
        weights = {}
        for pkg, vers in visited.items():
            if pkg not in levels:
                continue
            sorted_vers = self.parent.custom_sort(vers)
            for rank, ver in enumerate(sorted_vers):
                weight = self.build_solution_weight(pkg, ver, levels, visited)
                if pkg in steps:
                    weight += rank * steps[pkg]
                weights[(pkg, ver)] = weight
        return weights

    def build_tail_solution_weights(self, entry_names, levels, visited, feasible_versions=None):
        entry_set = set(entry_names)
        all_weights = self.build_solution_weights(entry_names, levels, visited)
        feasible_versions = feasible_versions or {}
        tail_weights = {}
        for (pkg, ver), weight in all_weights.items():
            if pkg in entry_set:
                continue
            allowed_versions = feasible_versions.get(pkg, visited.get(pkg, []))
            if len(allowed_versions) <= 1:
                continue
            if ver not in allowed_versions:
                continue
            tail_weights[(pkg, ver)] = weight
        return tail_weights

    def build_solution_score(self, solution, entry_names, levels, visited, solution_weights=None):
        if solution_weights is None:
            solution_weights = self.build_solution_weights(entry_names, levels, visited)
        return sum(solution_weights.get((pkg, ver), 0) for pkg, ver in solution.items())

    def build_solution_objective(self, solution, entry_names, levels, visited, solution_weights=None):
        signature = self.build_solution_signature(solution, entry_names, visited)
        score = self.build_solution_score(
            solution,
            entry_names,
            levels,
            visited,
            solution_weights=solution_weights,
        )
        return signature, score

    def build_solution_signature(self, solution, entry_names, visited):
        signature = []
        for name in entry_names:
            versions = self.parent.custom_sort(visited.get(name, []))
            if solution is None:
                signature.append(max(len(versions) - 1, -1))
                continue
            chosen_version = solution.get(name)
            if chosen_version not in versions:
                signature.append(-1)
                continue
            signature.append(versions.index(chosen_version))
        return tuple(signature)

    def build_solution_softweights(self, var_map, solution_weights):
        soft_weights = {}
        for (pkg, ver), var in var_map.items():
            if (pkg, ver) in solution_weights:
                soft_weights[var] = solution_weights[(pkg, ver)]
        return soft_weights

    def build_levels(self, entry_names, visited):
        levels = {}
        queue = collections.deque()
        for i, name in enumerate(entry_names):
            levels[name] = (0, i)
            queue.append((name, 0, i))
        while queue:
            pkg, lvl, _ = queue.popleft()
            versions = visited.get(pkg, [])
            for ver in versions:
                reqs = self.parent.resolve_filter(pkg, ver, "req")
                for dep_index, dep_name in enumerate(reqs.keys()):
                    if dep_name not in levels:
                        levels[dep_name] = (lvl + 1, dep_index)
                        queue.append((dep_name, lvl + 1, dep_index))
                xors = self.parent.resolve_filter(pkg, ver, "xor")
                for dep_index, dep_name in enumerate(xors.keys()):
                    if dep_name not in levels:
                        levels[dep_name] = (lvl + 1, dep_index)
                        queue.append((dep_name, lvl + 1, dep_index))
        return levels

    def build_ban_clause(self, current_pkg, constraint, var_map, rel_var_map):
        _ = rel_var_map
        _, _, p_var = current_pkg
        ban_name, ban_tags = constraint
        clauses = []
        for ban_tag in ban_tags:
            if (ban_name, ban_tag) in var_map:
                banned_var = var_map[(ban_name, ban_tag)]
                clause = [-p_var, -banned_var]
                clauses.append(clause)
        return clauses

    def build_req_clause(self, current_pkg, constraint, var_map, rel_var_map):
        pkg, ver, p_var = current_pkg
        dep_name, dep_tags_list = constraint
        direct_providers = [var_map[(dep_name, ver_tag)] for ver_tag in dep_tags_list if (dep_name, ver_tag) in var_map]
        if direct_providers:
            return [-p_var] + direct_providers
        else:
            raw_meta = self.parent.package_graph["graphed"][pkg][ver]["req"]
            all_req_cons = self.parent.combine_argv([{s: self.parent.resolve_argv(s)} for s in raw_meta])
            dep_cons = all_req_cons.get(dep_name)
            if not dep_cons:
                return [-p_var]
            substitutes = self.collect_alt_providers(dep_name, dep_cons, var_map, rel_var_map)
            if substitutes:
                return [-p_var] + substitutes
            else:
                return [-p_var]

    def build_ava_clause(self, current_pkg, ava_relations, var_map, rel_var_map):
        pkg, ver, p_var = current_pkg
        all_clause = [-p_var]
        all_providers = set()
        for dep_name, dep_tags_list in ava_relations.items():
            for ver_tag in dep_tags_list:
                if (dep_name, ver_tag) in var_map:
                    all_providers.add(var_map[(dep_name, ver_tag)])
            raw_meta = self.parent.package_graph["graphed"][pkg][ver]["ava"]
            all_ava_cons = self.parent.combine_argv([{s: self.parent.resolve_argv(s)} for s in raw_meta])
            dep_cons = all_ava_cons.get(dep_name)
            if dep_cons:
                substitutes = self.collect_alt_providers(dep_name, dep_cons, var_map, rel_var_map)
                all_providers.update(substitutes)
        all_clause.extend(list(all_providers))
        return all_clause

    def build_xor_clause(self, current_pkg, xor_relations, var_map, rel_var_map):
        all_clauses = []
        pkg, ver, p_var = current_pkg
        eraw_meta = self.parent.package_graph["graphed"][pkg][ver]["exor"]
        for xor_group in eraw_meta:
            if not xor_group:
                continue
            group_vars = []
            for xor_pkg_string in xor_group:
                xor_pkg_name, flag, tags, path = self.parent.resolve_argv(xor_pkg_string)
                all_providers_for_this_pkg = set()

                allowed_tags = xor_relations.get(xor_pkg_name, [])
                for tag in allowed_tags:
                    if (xor_pkg_name, tag) in var_map:
                        all_providers_for_this_pkg.add(var_map[(xor_pkg_name, tag)])

                dep_cons = [(flag, tags, path)]
                substitutes = self.collect_alt_providers(xor_pkg_name, dep_cons, var_map, rel_var_map)
                for sub_var in substitutes:
                    all_providers_for_this_pkg.add(sub_var)

                group_vars.extend(list(all_providers_for_this_pkg))
            group_vars = list(set(group_vars))
            if group_vars:
                all_clauses.append([-p_var] + group_vars)

                for i in range(len(group_vars)):
                    for j in range(i + 1, len(group_vars)):
                        all_clauses.append([-p_var, -group_vars[i], -group_vars[j]])
            else:
                all_clauses.append([-p_var])
        return all_clauses

    def build_constraints(self, entry_names, var_map, rel_var_map, visited):
        wcnf = list()
        for name, vers in visited.items():
            for i in range(len(vers)):
                for j in range(i + 1, len(vers)):
                    clause = [-var_map[(name, vers[i])], -var_map[(name, vers[j])]]
                    wcnf.append(clause)

        for name in entry_names:
            if name not in visited:
                continue
            clause = [var_map[(name, ver)] for ver in visited[name] if (name, ver) in var_map]
            wcnf.append(clause)

        for (pkg, ver), rels in rel_var_map.items():
            v = var_map[(pkg, ver)]
            for dep_name, dep_tags in rels["ban"].items():
                clause = self.build_ban_clause((pkg, ver, v), (dep_name, dep_tags), var_map, rel_var_map)
                wcnf.extend(clause)

            for dep_name, dep_tags in rels["req"].items():
                clause = self.build_req_clause((pkg, ver, v), (dep_name, dep_tags), var_map, rel_var_map)
                wcnf.append(clause)

            if rels["ava"]:
                clause = self.build_ava_clause((pkg, ver, v), rels["ava"], var_map, rel_var_map)
                wcnf.append(clause)

            if rels["xor"]:
                clause = self.build_xor_clause((pkg, ver, v), rels["xor"], var_map, rel_var_map)
                wcnf.extend(clause)

        return wcnf

    def build_prune_solution(self, solution, entry_names, rel_var_map):
        reverse_dep_map = collections.defaultdict(set)
        for (pkg, ver), meta in rel_var_map.items():
            reqs = meta.get("req", {})
            for dep_pkg, dep_vers in reqs.items():
                for dep_ver in dep_vers:
                    reverse_dep_map[(dep_pkg, dep_ver)].add((pkg, ver))
            xors = meta.get("xor", {})
            for dep_pkg, dep_vers in xors.items():
                for dep_ver in dep_vers:
                    reverse_dep_map[(dep_pkg, dep_ver)].add((pkg, ver))
        while True:
            pruned_list = []
            for pkg, ver in list(solution.items()):
                if pkg in entry_names:
                    continue
                reverse_deps = reverse_dep_map.get((pkg, ver), set())
                if not reverse_deps & solution.items():
                    pruned_list.append(pkg)

            if not pruned_list:
                break
            for pkg in pruned_list:
                del solution[pkg]
        return solution

    def build_sort_solution(self, solution, levels):
        level_groups = collections.defaultdict(list)
        for pkg, ver in solution.items():
            if pkg in levels:
                lvl, pos = levels.get(pkg)
                level_groups[lvl].append((pkg, ver, pos))
        sorted_solution_items = []
        for lvl in sorted(level_groups.keys()):
            sorted_layer = sorted(level_groups[lvl], key=lambda x: (x[2], x[0]))
            sorted_solution_items.extend((pkg, ver) for pkg, ver, _ in sorted_layer)
        solution = collections.OrderedDict(sorted_solution_items)
        return solution

    def build_solution_dfs(self, entry_names, visited):
        original_visited = self.parent.package_graph["visited"]
        self.parent.package_graph["visited"] = visited
        all_solutions = self.build_all_solutions(entry_names)
        valid_solutions = self.build_valid_solutions(all_solutions)
        self.parent.package_graph["visited"] = original_visited
        if valid_solutions:
            levels = self.build_levels(entry_names, visited)
            solutions_sorted = sorted(
                valid_solutions,
                key=self.build_solution_priority(entry_names, levels, visited),
                reverse=True,
            )
            best_solution = solutions_sorted[0]
            return best_solution

    def build_all_solutions(self, entry_names, picked=None):
        if picked is None:
            picked = collections.OrderedDict()
        for name, tags in picked.items():
            banned_deps = self.parent.resolve_filter(name, tags, "ban")
            for banned_name, banned_versions in banned_deps.items():
                if banned_name in picked and picked[banned_name] in banned_versions:
                    return

        current_names = [name for name in entry_names if name not in picked]
        if not current_names:
            resolve_reqs = collections.defaultdict(set)
            for name, tags in picked.items():
                reqs = self.parent.resolve_filter(name, tags, "req")
                for dep_name, dep_tags_list in reqs.items():
                    if dep_name not in picked:
                        resolve_reqs[dep_name].update(dep_tags_list)

            if not resolve_reqs:
                yield picked
                return
            else:
                yield from self.build_all_solutions(list(resolve_reqs.keys()), picked)
                return
        current_name = current_names[0]
        remaining_names = current_names[1:]
        for version in self.parent.package_graph["visited"].get(current_name, []):
            new_picked = collections.OrderedDict(picked)
            new_picked[current_name] = version
            yield from self.build_all_solutions(remaining_names, new_picked)

    def build_solution_priority(self, entry_names, levels, visited):
        solution_weights = self.build_solution_weights(entry_names, levels, visited)

        def solution_key(sol):
            return self.build_solution_objective(
                sol,
                entry_names,
                levels,
                visited,
                solution_weights=solution_weights,
            )

        return solution_key

    def build_valid_solutions(self, solutions):
        def is_valid_solution(self, sol):
            selected_visited = collections.defaultdict(list)
            for pkg, ver in sol.items():
                selected_visited[pkg].append(ver)

            for name, tags in sol.items():
                current_meta = self.parent.package_graph["graphed"].get(name, {}).get(tags, {})
                resolve_reqs = self.parent.resolve_filter(name, tags, "req")
                if resolve_reqs:
                    raw_reqs = current_meta.get("req", [])
                    all_req_cons = self.parent.combine_argv([{s: self.parent.resolve_argv(s)} for s in raw_reqs])
                    for dep_name, dep_tags_list in resolve_reqs.items():
                        if dep_name in sol and sol[dep_name] in dep_tags_list:
                            continue
                        dep_cons = all_req_cons.get(dep_name)
                        if dep_cons and self.check_alt_providers(dep_name, dep_cons, selected_visited):
                            continue
                        self._diagnostics().add_missing_dep(name, tags, dep_name, dep_cons)
                        selected_version = sol.get(dep_name)
                        if selected_version:
                            reason = (
                                "{}/{} requires '{}' but selected version '{}' does not match the constraint"
                            ).format(name, tags, dep_name, selected_version)
                        else:
                            reason = "{}/{} requires '{}' but it is not selected".format(name, tags, dep_name)
                        return False, reason

                resolve_ava = self.parent.resolve_filter(name, tags, "ava")
                if not resolve_ava:
                    resolve_ava = {}
                if resolve_ava:
                    raw_ava = current_meta.get("ava", [])
                    all_ava_cons = self.parent.combine_argv([{s: self.parent.resolve_argv(s)} for s in raw_ava])
                    found_one_valid_ava = False
                    unsatisfied_ava = []
                    for dep_name, dep_tags_list in resolve_ava.items():
                        if dep_name in sol and sol[dep_name] in dep_tags_list:
                            found_one_valid_ava = True
                            break
                        dep_cons = all_ava_cons.get(dep_name)
                        if dep_cons and self.check_alt_providers(dep_name, dep_cons, selected_visited):
                            found_one_valid_ava = True
                            break
                        unsatisfied_ava.append((dep_name, dep_cons))
                    if not found_one_valid_ava:
                        for dep_name, dep_cons in unsatisfied_ava:
                            self._diagnostics().add_unavailable(name, tags, dep_name, dep_cons)
                        reason = "{}/{} requires at least one ava() relation, but none are satisfied".format(
                            name,
                            tags,
                        )
                        return False, reason

                resolve_ban = self.parent.resolve_filter(name, tags, "ban")
                for dep_name, dep_tags_list in resolve_ban.items():
                    if dep_name in sol and sol[dep_name] in dep_tags_list:
                        self._diagnostics().add_conflict(name, tags, dep_name, sol[dep_name], "ban constraint")
                        reason = "{}/{} bans {}/{}".format(name, tags, dep_name, sol[dep_name])
                        return False, reason

                resolve_xor = self.parent.resolve_filter(name, tags, "xor")
                raw_xor = current_meta.get("exor", [])
                for xor_group in raw_xor:
                    matched_count = 0
                    for xor_pkg_string in xor_group:
                        xor_pkg_name, flag, xor_tags, path = self.parent.resolve_argv(xor_pkg_string)
                        allowed_tags = resolve_xor.get(xor_pkg_name, [])
                        if xor_pkg_name in sol and sol[xor_pkg_name] in allowed_tags:
                            matched_count += 1
                            continue
                        dep_cons = [(flag, xor_tags, path)]
                        if self.check_alt_providers(xor_pkg_name, dep_cons, selected_visited):
                            matched_count += 1
                    if raw_xor and matched_count != 1:
                        self._diagnostics().add_xor_violation(name, tags, xor_group, matched_count)
                        reason = "{}/{} requires exactly one xor() match from [{}], got {}".format(
                            name,
                            tags,
                            ", ".join(xor_group),
                            matched_count,
                        )
                        return False, reason
            return True, None

        valid_solutions = list()
        for sol in solutions:
            if self.parent.solution:
                val_solution = self.parent.solution.copy()
                val_solution.update(sol)
            else:
                val_solution = sol
            is_valid, rejection_reason = is_valid_solution(self, val_solution)
            if is_valid:
                valid_solutions.append(sol)
            elif rejection_reason:
                self._diagnostics().add_rejection(val_solution, rejection_reason)
        return valid_solutions


class Locker(object):
    def __init__(self):
        self._locks = dict()
        self._lock = threading.Lock()

    def _get_lock_file(self, base_path, tags, action):
        return os.path.join(base_path, ".{}.{}.lock".format(tags, action))

    def __enter__(self):
        lock_dir = os.path.dirname(self.lock_path)
        if not os.path.exists(lock_dir):
            os.makedirs(lock_dir, exist_ok=True)

        start_time = time.time()
        max_wait_time = 10
        wait_time = 1

        while True:
            try:
                with self._lock:
                    if self.lock_path not in self._locks:
                        fd = os.open(self.lock_path, os.O_CREAT | os.O_EXCL | os.O_RDWR)
                        self._locks[self.lock_path] = fd
                        return self
            except FileExistsError:
                if time.time() - start_time > self.timeout:
                    try:
                        os.remove(self.lock_path)
                    except Exception:
                        pass
                sys.stdout.write(
                    "[{} {}] Progress: Wait {:.0f}s for {}...\r".format(
                        self.name, self.tags, time.time() - start_time, self.action
                    )
                )
                sys.stdout.flush()
                time.sleep(wait_time)
                wait_time = min(wait_time * 2, max_wait_time)

    def __exit__(self, *_):
        with self._lock:
            if self.lock_path in self._locks:
                try:
                    os.close(self._locks[self.lock_path])
                    os.remove(self.lock_path)
                except Exception:
                    pass
                del self._locks[self.lock_path]

    def start(self, base_path, tags, action, timeout=60):
        self.lock_path = self._get_lock_file(base_path, tags, action)
        self.tags = tags
        self.action = action
        self.timeout = timeout
        self.name = os.path.basename(base_path)
        return self


class Loader(object):
    def __init__(self, **kwargs):
        self.start_time = 0
        self.object_name = str()
        self.last_output_time = 0
        self.output_interval = 0.5
        self.total_bytes = 0
        self.sync_bytes = 0
        self.kwargs = kwargs
        self.action = kwargs.get("action")

    def set_meta(self, object_name, total_length):
        self.start_time = time.time()
        self.object_name = object_name
        self.total_bytes = total_length
        self.last_output_time = self.start_time

    def update(self, sync_bytes):
        self.sync_bytes += sync_bytes
        current_time = time.time()
        elapsed_time = current_time - self.start_time
        if self.sync_bytes == self.total_bytes or current_time - self.last_output_time >= self.output_interval:
            progress = (self.sync_bytes / self.total_bytes) * 100
            if elapsed_time == 0:
                speed = 0
            else:
                speed = self.sync_bytes / elapsed_time
            speed_display = self._format_bytes(speed) + "/s"
            total_display = self._format_bytes(self.total_bytes)
            info_str = "[{} {}] Progress: {:.0f}% {}: {} Speed: {}\r".format(
                self.kwargs.get("name"),
                self.kwargs.get("tags"),
                progress,
                self.action,
                total_display,
                speed_display,
            )
            if progress == 100:
                info_str = "\r" + info_str[0:-1] + "\n"
            sys.stdout.write(info_str)
            sys.stdout.flush()
            self.last_output_time = current_time

    def _format_bytes(self, byte):
        if byte > 1024**2:
            return "{:.2f}MB".format(byte / 1024**2)
        elif byte > 1024:
            return "{:.2f}KB".format(byte / 1024)
        else:
            return "{:.2f}B".format(byte)


class Packer(object):
    def __init__(self, **kwargs):
        self.last_output_time = 0
        self.output_interval = 0.5
        self.title = "[{} {}] Progress: ".format(kwargs.get("name"), kwargs.get("tags"))
        self.progress_regex = re.compile(r"^\d+%\s+.*")
        self.action = ""

    def unpack(self, archive_pkg, output_dir):
        self.action = "Unpacking"
        cmd_str = "7z x {} -tzip -bsp1 -aoa -o{}".format(archive_pkg, output_dir)
        self._run_process(cmd_str)

    def pack(self, archive_dir, output_pkg):
        self.action = "Packing"
        cmd_str = "7z a {} {}/* -tzip -bsp1".format(output_pkg, archive_dir)
        self._run_process(cmd_str)

    def _run_process(self, cmd_str):
        process = subprocess.Popen(
            cmd_str,
            shell=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            bufsize=1,
            encoding=locale.getpreferredencoding(False),
        )

        if process.stdout:
            thread = threading.Thread(target=self._read_output, args=(process.stdout,))
            thread.start()

        return_code = process.wait()

        if process.stdout:
            thread.join()

        if return_code != 0:
            print(f"\nError: {self.action} failed with code {return_code}.")

    def _read_output(self, stream):
        if sys.platform.startswith("win"):
            for line in iter(stream.readline, ""):
                if line.strip():
                    self._parse_output(line.strip())
        else:
            line = str()
            buffer = str()
            while True:
                chunk = stream.read(1)
                if not chunk:
                    break
                if chunk == "\r" or chunk == "\n":
                    if buffer:
                        self._parse_output(buffer.strip())
                        buffer = str()
                elif chunk == "\b":
                    line += buffer[-1]
                    buffer = buffer[:-1]
                else:
                    if line.strip():
                        buffer = line[::-1]
                        self._parse_output(buffer.strip())
                    line = str()
                    buffer += chunk

    def _parse_output(self, line):
        current_time = time.time()

        if self.progress_regex.match(line):
            linelist = line.split()
            if not linelist:
                return

            progress = linelist[0]
            filecount = linelist[1] if len(linelist) > 1 else ""

            if current_time - self.last_output_time >= self.output_interval:

                filecount_str = ": {}".format(filecount) if filecount else ""
                stdout_str = "\r{}{} {}{}\r".format(self.title, progress, self.action, filecount_str)

                sys.stdout.write(stdout_str)
                sys.stdout.flush()
                self.last_output_time = current_time

        elif line.startswith("Files:"):
            progress = "100%"
            filecount = line.split(":")[-1].strip()
            stdout_str = "\r{}{} {}: {}\n".format(self.title, progress, self.action, filecount)
            sys.stdout.write(stdout_str)
            sys.stdout.flush()


class Client(object):
    __message = True

    def __init__(self, url, config=None, environ=None):
        super(Client, self).__init__()
        self.environ = environ
        self.config = config
        self.client = None
        self.logged = True
        if not url:
            self._message("Url not exist")
            self.logged = False
            return
        if self.environ(self.config.Env.OFFLINE_MODE).getenv() == "1":
            self._message("Switch to local mode")
            self.logged = False
            return
        self.parsed_url(url)
        if not self.check_net(self.scheme, self.host, self.port):
            self._message("Network unavailable fallback to local mode")
            self.logged = False
            return

    def _message(self, message):
        if self.config.VERBOSE == "+" and Client.__message:
            sys.stdout.write("Info: {}\n".format(message))
            sys.stdout.flush()
        Client.__message = False

    def check_net(self, scheme, host, port):
        import requests

        ping_url = "{}://{}:{}/ping".format(scheme, host, port)
        try:
            resp = requests.get(ping_url, timeout=0.5)
            if resp.status_code in (200, 204, 403):
                return True
            else:
                return False
        except requests.RequestException:
            return False

    def parsed_url(self, url):
        url = url.strip('"')
        parse = urllib.parse.urlparse(url)
        query_params = urllib.parse.parse_qs(parse.query)
        self.host, self.port = parse.netloc.split(":")
        self.netloc = parse.netloc
        if not self.port:
            self.port = "80"
        if parse.scheme == "http":
            self.secure = False
        else:
            self.secure = True
        self.scheme = parse.scheme
        self.bucket = parse.path.strip("/")
        self.access = query_params.get("access", [None])[0]
        self.secret = query_params.get("secret", [None])[0]


class APIClient(Client):
    def __init__(self, url, config=None, environ=None):
        super(APIClient, self).__init__(url, config, environ)
        if self.logged is False:
            return
        from requests import adapters, Session

        self.metadata_timeout = 1.0
        adapter = adapters.HTTPAdapter(pool_connections=3, pool_maxsize=300, max_retries=0)
        self.client = Session()
        self.client.mount("http://", adapter)
        self.client.mount("https://", adapter)
        self.client.headers.update(
            {
                "Access-Key": self.access,
                "Secret-Key": self.secret,
                "Content-Type": "application/json",
            }
        )
        self.base_url = "{scheme}://{netloc}/{bucket}".format(
            scheme=self.scheme, netloc=self.netloc, bucket=self.bucket
        )

    def _get_json_list(self, url_path, key):
        try:
            url = "{}/{}".format(self.base_url, url_path)
            response = self.client.get(url, timeout=self.metadata_timeout)
            response.raise_for_status()
            value = response.json().get(key)
            return list(value) if value is not None else list()
        except Exception:
            self._message("API unavailable fallback to local mode")
            return list()

    @lru_cache()
    def get_nodes(self):
        return self._get_json_list("nodes/names", "names")

    @lru_cache()
    def get_tags(self, name):
        return self._get_json_list("nodes/{}/tags".format(name), "tags")

    def get_batch_tags(self, names):
        """Batch query: get tags for multiple packages in one request.
        Returns dict {name: [tags]} or empty dict on failure.
        """
        try:
            url = "{base_url}/nodes/batch/tags".format(base_url=self.base_url)
            response = self.client.post(url, json={"names": names}, timeout=self.metadata_timeout * 2)
            response.raise_for_status()
            result = response.json()
            return result.get("results", {})
        except Exception:
            return {}

    @lru_cache()
    def get_node_properties(self, name, tags):
        try:
            url = "{base_url}/nodes/{name}/{tags}".format(base_url=self.base_url, name=name, tags=tags)
            response = self.client.get(url, timeout=self.metadata_timeout)
            response.raise_for_status()
            result = response.json()
            return result.get("properties", {})
        except Exception:
            self._message("API unavailable fallback to local mode")
            return dict()

    @lru_cache()
    def get_args(self, name, tags, args):
        props = self.get_node_properties(name, tags)
        value = props.get(args)
        if value is None:
            return list()
        return value

    def set_info(self, name, tags):
        try:
            url = "{base_url}/nodes/{name}/{tags}".format(base_url=self.base_url, name=name, tags=tags)
            response = self.client.post(url, timeout=self.metadata_timeout)
            response.raise_for_status()
            return response.json()
        except Exception:
            self._message("API unavailable fallback to local mode")
            return dict()

    def exec_cql(self, cql):
        try:
            url = "{base_url}/cypher/exec".format(base_url=self.base_url)
            response = self.client.post(url, json={"cql": cql}, timeout=self.metadata_timeout)
            result = response.json()
            if "error" in result:
                error_info = "exec: %s error:%s" % (cql, result.get("error"))
                raise Exception(error_info)
            response.raise_for_status()
            value = result.get("args")
            if value is None:
                return str()
            return value
        except Exception:
            self._message("API unavailable fallback to local mode")
            return str()

    def llm_chat(self, data):
        try:
            url = "{base_url}/llm/chat".format(base_url=self.base_url)
            if data.get("stream", True):
                response = self.client.post(url, json=data, stream=True, timeout=60)
                response.raise_for_status()

                def stream_generator():
                    for line in response.iter_lines(decode_unicode=True):
                        if line:
                            yield line

                return stream_generator()
            else:
                response = self.client.post(url, json=data, timeout=120)
                response.raise_for_status()
                return response.json()
        except Exception:
            self._message("API unavailable fallback to local mode")
            return str()


class S3Client(Client):
    def __init__(self, url, config=None, environ=None):
        super(S3Client, self).__init__(url, config, environ)
        from minio import Minio

        if self.logged is False:
            return

        self.client = Minio(
            self.netloc,
            access_key=self.access,
            secret_key=self.secret,
            secure=self.secure,
        )

    def upload(self, local_path, minio_path, **kwargs):
        progress = Loader(**kwargs, action="Upload")
        total = os.path.getsize(local_path)
        progress.set_meta(minio_path, total)
        if not self.client.bucket_exists(self.bucket):
            self.client.make_bucket(self.bucket)
        self.client.fput_object(self.bucket, minio_path, local_path, progress=progress)

    def download(self, minio_path, local_path, **kwargs):
        progress = Loader(**kwargs, action="Download")
        tmp_path = kwargs.get("tmp_path", str())
        stat = self.client.stat_object(self.bucket, minio_path)
        progress.set_meta(minio_path, stat.size)
        self.client.fget_object(
            self.bucket,
            minio_path,
            local_path,
            tmp_file_path=tmp_path,
            progress=progress,
        )

    def pack(self, archive_dir, output_pkg, **kwargs):
        packer = Packer(**kwargs)
        packer.pack(archive_dir, output_pkg)

    def unpack(self, archive_pkg, output_dir, **kwargs):
        packer = Packer(**kwargs)
        packer.unpack(archive_pkg, output_dir)

    def get_etag(self, minio_path):
        stat = self.client.stat_object(self.bucket, minio_path)
        return stat.etag


class DBPool(object):
    _instances = {}
    _lock = threading.Lock()

    def __new__(cls, db_path, max_connections=10):
        normalized_path = os.path.normcase(os.path.normpath(db_path))
        with cls._lock:
            if normalized_path not in cls._instances:
                instance = super(DBPool, cls).__new__(cls)
                instance.db_path = db_path
                instance.max_connections = max_connections
                instance._connections = []
                instance._in_use = set()
                instance._pool_lock = threading.Lock()
                cls._instances[normalized_path] = instance
            return cls._instances[normalized_path]

    def _create_connection(self):
        conn = sqlite3.connect(self.db_path, check_same_thread=False)
        return conn

    def get_connection(self):
        with self._pool_lock:
            for conn in self._connections:
                if conn not in self._in_use:
                    self._in_use.add(conn)
                    return conn

            if len(self._connections) < self.max_connections:
                conn = self._create_connection()
                self._connections.append(conn)
                self._in_use.add(conn)
                return conn

            while True:
                for conn in self._connections:
                    if conn not in self._in_use:
                        self._in_use.add(conn)
                        return conn
                time.sleep(0.1)

    def release_connection(self, conn):
        with self._pool_lock:
            if conn in self._in_use:
                self._in_use.remove(conn)

    def close_all(self):
        with self._pool_lock:
            for conn in self._connections:
                try:
                    conn.close()
                except Exception:
                    pass
            self._connections.clear()
            self._in_use.clear()


class DBContext(object):
    def __init__(self, pool):
        self.pool = pool
        self.conn = None
        self.cursor = None

    def __enter__(self):
        self.conn = self.pool.get_connection()
        self.cursor = self.conn.cursor()
        return self.conn, self.cursor

    def __exit__(self, exc_type, exc_val, exc_tb):
        if self.cursor:
            self.cursor.close()
        if self.conn:
            if exc_type:
                self.conn.rollback()
            self.pool.release_connection(self.conn)


class DBManage(object):
    def __init__(self, config, environ):
        self.storage_path = environ(config.Env.STORAGE_PATH).getenv()
        os.makedirs(self.storage_path, exist_ok=True)
        self.db_pool = DBPool(os.path.join(self.storage_path, ".db"))
        self.__init_db()
        atexit.register(self.close)

    def close(self):
        if hasattr(self, "db_pool"):
            self.db_pool.close_all()

    def __get_db(self):
        return DBContext(self.db_pool)

    def __init_db(self):
        try:
            with self.__get_db() as (db, cursor):
                cursor.execute("""
                    CREATE TABLE IF NOT EXISTS caches (
                        name TEXT,
                        tags TEXT,
                        etag TEXT NOT NULL,
                        timestamp INTEGER,
                        PRIMARY KEY (name, tags)
                    )
                """)
                db.commit()
                return True
        except sqlite3.Error as e:
            return False

    def write_db_etag(self, name, tags, etag):
        try:
            with self.__get_db() as (db, cursor):
                current_time = int(time.time())
                cursor.execute(
                    """
                    INSERT OR REPLACE INTO caches 
                    (name, tags, etag, timestamp)
                    VALUES (?, ?, ?, ?)
                """,
                    (name, tags, etag, current_time),
                )
                db.commit()
                return True
        except sqlite3.Error as e:
            return False

    def query_db_etag(self, name, tags):
        try:
            with self.__get_db() as (db, cursor):
                cursor.execute(
                    """
                    SELECT etag 
                    FROM caches 
                    WHERE name = ? AND tags = ?
                """,
                    (name, tags),
                )
                result = cursor.fetchone()
                return result[0] if result else None
        except sqlite3.Error as e:
            return False

    def update_timestamp(self, name, tags):
        try:
            with self.__get_db() as (db, cursor):
                current_time = int(time.time())
                cursor.execute(
                    """
                    UPDATE caches 
                    SET timestamp = ?
                    WHERE name = ? AND tags = ?
                """,
                    (current_time, name, tags),
                )
                db.commit()
                return cursor.rowcount > 0
        except sqlite3.Error as e:
            return False

    def autoclean_caches(self, days=30):
        cleaned = False
        deadline = int(time.time()) - days * 86400
        with self.__get_db() as (db, cursor):
            cursor.execute(
                """
                SELECT name, tags 
                FROM caches 
                WHERE timestamp < ?
            """,
                (deadline,),
            )
            rows = cursor.fetchall()
            if not rows:
                return True
            for name, tags in rows:
                pkg_path = os.path.join(self.storage_path, name, tags)
                base_path = os.path.dirname(pkg_path)
                if os.path.exists(pkg_path):
                    print("AutoClean: ", name, tags, pkg_path)
                    try:
                        temp_tags = "." + tags + "." + uuid.uuid1().hex
                        temp_path = os.path.join(base_path, temp_tags)
                        os.rename(pkg_path, temp_path)
                        for i in os.listdir(base_path):
                            if i.startswith("." + tags + "."):
                                full_path = os.path.join(base_path, i)
                                shutil.rmtree(full_path)
                        if os.path.exists(base_path) and not os.listdir(base_path):
                            os.rmdir(base_path)
                        cleaned = True
                    except Exception:
                        continue
                else:
                    cleaned = True
                if cleaned:
                    cursor.execute(
                        """
                        DELETE FROM caches 
                        WHERE name = ? AND tags = ?
                        """,
                        (name, tags),
                    )
            db.commit()
            return True


class Syncer(object):
    def __new__(cls, config, environ, thispath):
        instance = super(Syncer, cls).__new__(cls)
        try:
            import minio
            import requests
        except ImportError as e:
            if config.VERBOSE == "+":
                sys.stdout.write("Info: Syncer unavailable ({})\n".format(e))
                sys.stdout.flush()
            return None
        instance.config = config
        instance.environ = environ
        instance.thispath = thispath
        instance.storage_path = environ(instance.config.Env.STORAGE_PATH).getenv()
        instance.dbmanage = DBManage(config, environ)
        instance.locker = Locker()

        instance.max_client = 10
        instance.s3_client = S3Client(
            instance.environ(instance.config.Env.STORAGE_URL).getenv(),
            instance.config,
            instance.environ,
        )
        instance.api_client = APIClient(
            instance.environ(instance.config.Env.RESTAPI_URL).getenv(),
            instance.config,
            instance.environ,
        )

        if all(
            (
                instance.s3_client.logged,
                instance.api_client.logged,
            )
        ):
            return instance
        return None

    def set_s3(self, url):
        return S3Client(url, self.config, self.environ)

    def set_api(self, url):
        return APIClient(url, self.config, self.environ)

    def get_tags(self, name):
        # Lazy batch prefetch: first call triggers bulk fetch of all known packages
        if not hasattr(self, "_tags_cache"):
            self._tags_cache = {}
            self._tags_prefetched = False
        if not self._tags_prefetched:
            self._tags_prefetched = True
            all_names = self.first_api_client("get_nodes")
            if all_names:
                batch_result = self.first_api_client("get_batch_tags", all_names)
                if isinstance(batch_result, dict):
                    self._tags_cache = batch_result
        if name in self._tags_cache:
            return self._tags_cache[name]
        # Fallback to single query for packages not in prefetch
        result = self.first_api_client("get_tags", name)
        self._tags_cache[name] = result
        return result

    def get_batch_tags(self, names):
        """Batch query: get tags for multiple packages in one request."""
        result = self.first_api_client("get_batch_tags", names)
        if isinstance(result, dict):
            return result
        return {}

    def get_args(self, name, tags, args):
        result = self.first_api_client("get_args", name, tags, args)
        return result

    def update_timestamp(self, name, tags):
        result = self.first_api_client("set_info", name, tags)
        return result

    def first_api_client(self, method_name, *args, **kwargs):
        try:
            method = getattr(self.api_client, method_name)
            result = method(*args, **kwargs)
            if result:
                return result
        except Exception:
            pass
        main_env_value = self.config.Env.RESTAPI_URL
        deadline = time.time() + 3.0  # total timeout for all fallback attempts
        for i in range(1, self.max_client + 1):
            if time.time() > deadline:
                break
            api_env_value = self.environ(main_env_value + str(i)).getenv()
            if not api_env_value:
                continue
            new_api_client = APIClient(api_env_value, self.config, self.environ)
            if new_api_client.logged is False:
                continue
            try:
                method = getattr(new_api_client, method_name)
                result = method(*args, **kwargs)
                if result:
                    return result
            except Exception:
                continue
        return list()

    def first_s3_client(self, method_name, *args, **kwargs):
        """Try primary S3 client, then fallback to numbered alternates."""
        try:
            result = getattr(self.s3_client, method_name)(*args, **kwargs)
            return result, self.s3_client
        except Exception:
            pass
        main_env_value = self.config.Env.STORAGE_URL
        for i in range(1, self.max_client + 1):
            s3_env_value = self.environ(main_env_value + str(i)).getenv()
            if not s3_env_value:
                continue
            new_s3_client = S3Client(s3_env_value, self.config, self.environ)
            if new_s3_client.logged is False:
                continue
            try:
                result = getattr(new_s3_client, method_name)(*args, **kwargs)
                return result, new_s3_client
            except Exception:
                continue
        return None, None

    def sync_pkgs(self, path):
        self.src_pkg = None
        this = self.thispath(path)
        if os.path.exists(this.root):
            if not self.clean_pkgs(path):
                return False
        name, tags, root = this.name, this.tags, this.root
        if self.src_pkg:
            src_pkg = self.src_pkg
        else:
            src_pkg = self.get_args(name, tags, "src")
        if not src_pkg:
            return False
        src_etag, s3_client = self.first_s3_client("get_etag", src_pkg)
        if src_etag is None:
            return False
        self.cache_pkgs(name, tags, root, src_pkg, src_etag, s3_client)
        return True

    def cache_pkgs(self, name, tags, root, src_pkg, src_etag, s3_client=None):
        if not s3_client:
            s3_client = self.s3_client
        base_path = os.path.dirname(root)
        tar_pkg = root + ".pkg"
        cache_pkg = os.path.join(base_path, ".{}.{}.part.minio".format(tags, src_etag))
        if not os.path.exists(tar_pkg):
            with self.locker.start(base_path, tags, "download"):
                if not os.path.exists(tar_pkg):
                    s3_client.download(src_pkg, tar_pkg, tmp_path=cache_pkg, name=name, tags=tags)
        cache_dir = os.path.join(base_path, ".{}.{}.part.unpack".format(tags, src_etag))
        if not os.path.exists(root):
            with self.locker.start(base_path, tags, "unpacking"):
                if not os.path.exists(root):
                    s3_client.unpack(tar_pkg, cache_dir, name=name, tags=tags)
                    if os.name == "posix":
                        os.system("chmod -R +x {}".format(cache_dir))
                    self.dbmanage.write_db_etag(name, tags, src_etag)
                    os.rename(cache_dir, root)
                if os.path.exists(tar_pkg):
                    os.remove(tar_pkg)

    def clean_pkgs(self, path):
        this = self.thispath(path)
        base_path = os.path.dirname(this.root)
        base_norm = os.path.normcase(os.path.normpath(base_path))
        storage_norm = os.path.normcase(os.path.normpath(self.storage_path))
        if base_norm != storage_norm and not base_norm.startswith(storage_norm + os.sep):
            return False
        name, tags, root = this.name, this.tags, this.root
        src_pkg = self.get_args(name, tags, "src")
        if not src_pkg:
            return False
        self.src_pkg = src_pkg
        if os.path.exists(root):
            tar_etag = self.dbmanage.query_db_etag(name, tags)
            src_etag, _ = self.first_s3_client("get_etag", self.src_pkg)
            if src_etag is not None and tar_etag == src_etag:
                return False
        temp_tags = "." + tags + "." + uuid.uuid1().hex
        temp_root = os.path.join(base_path, temp_tags)
        try:
            os.rename(root, temp_root)
        except Exception:
            return False
        if self.config.VERBOSE == "+":
            sys.stdout.write("[{} {}] Update: {}\n".format(name, tags, root))
            sys.stdout.flush()
        for i in os.listdir(base_path):
            if i.startswith("." + tags + "."):
                try:
                    shutil.rmtree(os.path.join(base_path, i))
                except Exception:
                    pass
        return True
