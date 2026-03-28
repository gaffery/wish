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


class Solver(object):
    def __init__(self, parent, config, environ):
        self.parent = parent
        self.config = config
        self.enable_sat = False
        try:
            import pysat

            storage_path = environ(config.Env.STORAGE_PATH).getenv()
            if storage_path:
                environ(config.Env.PACKAGE_PATH).insert(storage_path)
            self.enable_sat = True
        except Exception:
            self.enable_sat = False

    def collect_verbose_info(self, original_visited):
        if self.config.VERBOSE == "+":
            from pprint import pformat

            relation = dict()
            for pkg, vers in original_visited.items():
                for ver in vers:
                    if (pkg, ver) not in relation:
                        relation[(pkg, ver)] = {}

                    for key in ("req", "ava", "ban", "alt", "xor"):
                        val = self.parent.resolve_filter(pkg, ver, key)
                        raw_meta = self.parent.package_graph["graphed"][pkg][ver][key]
                        all_cons = self.parent.combine_argv([{s: self.parent.resolve_argv(s)} for s in raw_meta])
                        if val:
                            relation[(pkg, ver)][key] = raw_meta
                        if key == "req":
                            for name, tags in val.items():
                                if tags:
                                    continue
                                dep_cons = all_cons.get(name)
                                alt_providers = False
                                if dep_cons:
                                    alt_providers = self.check_alt_providers(name, dep_cons, original_visited)
                                if alt_providers:
                                    continue
                                if "error" not in relation[(pkg, ver)]:
                                    relation[(pkg, ver)]["error"] = {}
                                if "missing" not in relation[(pkg, ver)]["error"]:
                                    relation[(pkg, ver)]["error"]["missing"] = []
                                relation[(pkg, ver)]["error"]["missing"].append(name)
                        elif key == "ava":
                            for name, tags in val.items():
                                if tags:
                                    break
                                dep_cons = all_cons.get(name)
                                alt_providers = False
                                if dep_cons:
                                    alt_providers = self.check_alt_providers(name, dep_cons, original_visited)
                                if alt_providers:
                                    break
                                if "error" not in relation[(pkg, ver)]:
                                    relation[(pkg, ver)]["error"] = {}
                                if "unavailable" not in relation[(pkg, ver)]["error"]:
                                    relation[(pkg, ver)]["error"]["unavailable"] = []
                                relation[(pkg, ver)]["error"]["unavailable"].append(name)
                        elif key == "ban":
                            for name, tags in val.items():
                                if tags:
                                    if "error" not in relation[(pkg, ver)]:
                                        relation[(pkg, ver)]["error"] = {}
                                    if "conflict" not in relation[(pkg, ver)]["error"]:
                                        relation[(pkg, ver)]["error"]["conflict"] = []
                                    relation[(pkg, ver)]["error"]["conflict"].append(name)

            for provider_pkg, ver_dict in self.parent.filters["alt"].items():
                for _, raw_alt in ver_dict.items():
                    for pkgs in raw_alt:
                        name, _, _, _ = self.parent.resolve_argv(pkgs)
                        if not original_visited.get(name):
                            original_visited[name] = []
                        original_visited[name].append("{}@{}".format(pkgs, provider_pkg))
            original_relation = {k: v for k, v in relation.items() if "error" in v}
            visited_info_str = pformat(dict(original_visited), indent=2, width=80)
            relation_info_str = pformat(dict(original_relation), indent=2, width=80)

            output_message = (
                "[Visited Packages and Versions]\n"
                "The solver considered the following packages and versions:\n"
                "{visited_info}\n\n"
                "[Relation and Error Info]\n"
                "The relationships and detected error for each package version are as follows:\n"
                "{relation_info}\n\n"
            ).format(visited_info=visited_info_str, relation_info=relation_info_str)
            sys.stdout.write(output_message)
            sys.stdout.flush()

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
        min_versions_limit = 5
        max_versions_limit = 10

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
        solution = fallback_solver_function(entry_names, visited=original_visited)
        if solution:
            return solution
        if best_solution:
            return best_solution
        self.collect_verbose_info(original_visited)

    def collect_solution(self, entry_names):
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
        locked_entries = self.build_entry_solution_sat(entry_names, visited, var_map, constraints)
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

    def build_entry_solution_sat(self, entry_names, visited, var_map, constraints):
        from pysat.solvers import Solver as SATSolver

        locked_solution = collections.OrderedDict()
        assumptions = []
        with SATSolver(bootstrap_with=constraints) as sat_solver:
            for name in entry_names:
                versions = self.parent.custom_sort(visited.get(name, []))
                if not versions:
                    return None
                chosen_version = None
                for version in reversed(versions):
                    sat_var = var_map.get((name, version))
                    if sat_var is None:
                        continue
                    if sat_solver.solve(assumptions=assumptions + [sat_var]):
                        assumptions.append(sat_var)
                        locked_solution[name] = version
                        chosen_version = version
                        break
                if chosen_version is None:
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
                        return False

                resolve_ava = self.parent.resolve_filter(name, tags, "ava")
                if not resolve_ava:
                    resolve_ava = {}
                if resolve_ava:
                    raw_ava = current_meta.get("ava", [])
                    all_ava_cons = self.parent.combine_argv([{s: self.parent.resolve_argv(s)} for s in raw_ava])
                    found_one_valid_ava = False
                    for dep_name, dep_tags_list in resolve_ava.items():
                        if dep_name in sol and sol[dep_name] in dep_tags_list:
                            found_one_valid_ava = True
                            break
                        dep_cons = all_ava_cons.get(dep_name)
                        if dep_cons and self.check_alt_providers(dep_name, dep_cons, selected_visited):
                            found_one_valid_ava = True
                            break
                    if not found_one_valid_ava:
                        return False

                resolve_ban = self.parent.resolve_filter(name, tags, "ban")
                for dep_name, dep_tags_list in resolve_ban.items():
                    if dep_name in sol and sol[dep_name] in dep_tags_list:
                        return False

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
                        return False
            return True

        valid_solutions = list()
        for sol in solutions:
            if self.parent.solution:
                val_solution = self.parent.solution.copy()
                val_solution.update(sol)
            else:
                val_solution = sol
            if is_valid_solution(self, val_solution):
                valid_solutions.append(sol)
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

        adapter = adapters.HTTPAdapter(pool_connections=3, pool_maxsize=300, max_retries=3)
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

    @lru_cache()
    def get_nodes(self):
        try:
            url = "{base_url}/nodes/names".format(base_url=self.base_url)
            response = self.client.get(url)
            response.raise_for_status()
            result = response.json()
            value = result.get("names")
            if value is None:
                return list()
            return list(value)
        except Exception:
            self._message("API unavailable fallback to local mode")
            return list()

    @lru_cache()
    def get_tags(self, name):
        try:
            url = "{base_url}/nodes/{name}/tags".format(base_url=self.base_url, name=name)
            response = self.client.get(url)
            response.raise_for_status()
            result = response.json()
            value = result.get("tags")
            if value is None:
                return list()
            return list(value)
        except Exception:
            self._message("API unavailable fallback to local mode")
            return list()

    @lru_cache()
    def get_node_properties(self, name, tags):
        try:
            url = "{base_url}/nodes/{name}/{tags}".format(base_url=self.base_url, name=name, tags=tags)
            response = self.client.get(url)
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
            response = self.client.post(url)
            response.raise_for_status()
            return response.json()
        except Exception:
            self._message("API unavailable fallback to local mode")
            return dict()

    def exec_cql(self, cql):
        try:
            url = "{base_url}/cypher/exec".format(base_url=self.base_url)
            response = self.client.post(url, json={"cql": cql})
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
                cursor.execute(
                    """
                    CREATE TABLE IF NOT EXISTS caches (
                        name TEXT,
                        tags TEXT,
                        etag TEXT NOT NULL,
                        timestamp INTEGER,
                        PRIMARY KEY (name, tags)
                    )
                """
                )
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
        except ImportError:
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
        result = self.first_api_client("get_tags", name)
        return result

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
        for i in range(1, self.max_client + 1):
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

        try:
            src_etag = self.s3_client.get_etag(src_pkg)
            self.cache_pkgs(name, tags, root, src_pkg, src_etag)
            return True
        except Exception:
            main_env_value = self.config.Env.STORAGE_URL
            for i in range(1, self.max_client + 1):
                s3_env_value = self.environ(main_env_value + str(i)).getenv()
                if not s3_env_value:
                    continue
                new_s3_client = S3Client(s3_env_value, self.config, self.environ)
                if new_s3_client.logged is False:
                    continue
                try:
                    src_etag = new_s3_client.get_etag(src_pkg)
                    self.cache_pkgs(name, tags, root, src_pkg, src_etag, new_s3_client)
                    return True
                except Exception:
                    continue
            return False

    def cache_pkgs(self, name, tags, root, src_pkg, src_etag, new_s3_client=None):
        if new_s3_client:
            s3_client = new_s3_client
        else:
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
            try:
                src_etag = self.s3_client.get_etag(self.src_pkg)
                if tar_etag == src_etag:
                    return False
            finally:
                main_env_value = self.config.Env.STORAGE_URL
                for i in range(1, self.max_client + 1):
                    s3_env_value = self.environ(main_env_value + str(i)).getenv()
                    if not s3_env_value:
                        continue
                    new_s3_client = S3Client(s3_env_value, self.config, self.environ)
                    if new_s3_client.logged is False:
                        continue
                    try:
                        src_etag = new_s3_client.get_etag(self.src_pkg)
                        if tar_etag == src_etag:
                            return False
                    except Exception:
                        continue
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
