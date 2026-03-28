import collections
import ast
import contextlib
import importlib
import io
import os
import shutil
import sqlite3
import subprocess
import sys
import tempfile
import types
import unittest
from unittest import mock

import src.wish as wish_module
import src.wishapi as wishapi_module
from src.wish import Config, Environ, Extractor, Nickname, Require, Resolve, Thispath
from src.wishapi import DBContext, DBManage, DBPool, Locker, Solver, Syncer


class SolverLogicTests(unittest.TestCase):
    def parse_argv(self, argv):
        resolve_list = argv.split("@", 1)
        name = resolve_list.pop(0)
        flag, tags = None, None
        path = resolve_list[0] if resolve_list else None
        for flag_str in ("==", ">=", "<=", "!=", "=", ">", "<"):
            if flag_str in name:
                name, tags = name.split(flag_str, 1)
                flag = flag_str
                break
        return name, flag, tags, path

    def combine_argv(self, items):
        combined = {}
        for item in items:
            for _, parsed in item.items():
                name, flag, tags, path = parsed
                combined.setdefault(name, []).append((flag, tags, path))
        return combined

    def make_solver(
        self,
        visited=None,
        graphed=None,
        filters=None,
        resolve_filter_map=None,
        solution=None,
        rules_compatible=None,
    ):
        resolve_filter_map = resolve_filter_map or {}
        solver = Solver.__new__(Solver)
        solver.parent = types.SimpleNamespace(
            custom_sort=lambda values: sorted(values),
            package_graph={"visited": visited or {}, "graphed": graphed or {}},
            solution=solution,
            filters=filters or {"alt": {}},
            resolve_filter=lambda pkg, ver, key: resolve_filter_map.get((pkg, ver, key), {}),
            combine_argv=self.combine_argv,
            resolve_argv=self.parse_argv,
            rules_compatible=rules_compatible or (lambda left, right: left == right),
        )
        solver.collect_verbose_info = lambda original_visited: None
        return solver

    def normalize_clauses(self, clauses):
        return {tuple(sorted(clause)) for clause in clauses}

    def test_collect_limit_versions_respects_level_caps(self):
        solver = self.make_solver()
        visited = {
            "entry": list(range(1, 13)),
            "dep": list(range(1, 13)),
            "leaf": list(range(1, 13)),
        }

        limited = solver.collect_limit_versions(visited, 10, 5, {"entry": 0, "dep": 1, "leaf": 2})

        self.assertEqual(list(range(3, 13)), limited["entry"])
        self.assertEqual(list(range(8, 13)), limited["dep"])
        self.assertEqual(list(range(8, 13)), limited["leaf"])

    def test_collect_limit_versions_prioritizes_earlier_entries(self):
        solver = self.make_solver()
        visited = {
            "alpha": list(range(1, 13)),
            "beta": list(range(1, 13)),
            "gamma": list(range(1, 13)),
            "dep": list(range(1, 13)),
        }

        limited = solver.collect_limit_versions(
            visited,
            10,
            5,
            {"alpha": (0, 0), "beta": (0, 1), "gamma": (0, 2), "dep": (1, 0)},
        )

        self.assertEqual(list(range(3, 13)), limited["alpha"])
        self.assertEqual(list(range(4, 13)), limited["beta"])
        self.assertEqual(list(range(5, 13)), limited["gamma"])
        self.assertEqual(list(range(8, 13)), limited["dep"])

    def test_build_levels_tracks_req_and_xor_dependencies(self):
        visited = {"entry": ["1"], "dep": ["1"], "backend": ["1"]}
        resolve_filter_map = {
            ("entry", "1", "req"): {"dep": ["1"]},
            ("entry", "1", "xor"): {"backend": ["1"]},
        }
        solver = self.make_solver(visited=visited, resolve_filter_map=resolve_filter_map)

        levels = solver.build_levels(["entry"], visited)

        self.assertEqual((0, 0), levels["entry"])
        self.assertEqual((1, 0), levels["dep"])
        self.assertEqual((1, 0), levels["backend"])

    def test_collect_alt_providers_returns_matching_provider_vars(self):
        solver = self.make_solver(filters={"alt": {"provider": {"1": ["virtual>=1"]}}})
        var_map = {("provider", "1"): 9}
        rel_var_map = {("provider", "1"): {"alt": {"virtual": [(">=", "1", None)]}}}

        providers = solver.collect_alt_providers("virtual", [(">=", "1", None)], var_map, rel_var_map)

        self.assertEqual({9}, set(providers))

    def test_build_ban_clause_creates_negated_pairs(self):
        solver = self.make_solver()

        clauses = solver.build_ban_clause(("pkg", "1", 7), ("banpkg", ["1", "2"]), {("banpkg", "1"): 11, ("banpkg", "2"): 12}, {})

        self.assertEqual([[-7, -11], [-7, -12]], clauses)

    def test_build_req_clause_uses_direct_providers(self):
        solver = self.make_solver()
        var_map = {("dep", "1"): 8, ("dep", "2"): 9}

        clause = solver.build_req_clause(("pkg", "1", 3), ("dep", ["1", "2"]), var_map, {})

        self.assertEqual([-3, 8, 9], clause)

    def test_build_req_clause_falls_back_to_alt_providers(self):
        graphed = {"pkg": {"1": {"req": ["virtual>=1"], "ava": [], "ban": [], "alt": [], "xor": [], "exor": []}}}
        filters = {"alt": {"provider": {"1": ["virtual>=1"]}}}
        solver = self.make_solver(visited={"pkg": ["1"]}, graphed=graphed, filters=filters)
        var_map = {("provider", "1"): 8}
        rel_var_map = {("provider", "1"): {"alt": {"virtual": [(">=", "1", None)]}}}

        clause = solver.build_req_clause(("pkg", "1", 3), ("virtual", []), var_map, rel_var_map)

        self.assertEqual([-3, 8], clause)

    def test_build_ava_clause_merges_direct_and_alt_providers(self):
        graphed = {"pkg": {"1": {"req": [], "ava": ["virtual>=1"], "ban": [], "alt": [], "xor": [], "exor": []}}}
        filters = {"alt": {"provider": {"1": ["virtual>=1"]}}}
        solver = self.make_solver(visited={"pkg": ["1"]}, graphed=graphed, filters=filters)
        var_map = {("virtual", "1"): 5, ("provider", "1"): 6}
        rel_var_map = {("provider", "1"): {"alt": {"virtual": [(">=", "1", None)]}}}

        clause = solver.build_ava_clause(("pkg", "1", 4), {"virtual": ["1"]}, var_map, rel_var_map)

        self.assertEqual({-4, 5, 6}, set(clause))

    def test_build_xor_clause_creates_choice_and_exclusion_clauses(self):
        graphed = {"pkg": {"1": {"req": [], "ava": [], "ban": [], "alt": [], "xor": [], "exor": [["backendA", "backendB"]]}}}
        solver = self.make_solver(visited={"pkg": ["1"]}, graphed=graphed)
        var_map = {("backendA", "1"): 5, ("backendB", "1"): 6}

        clauses = solver.build_xor_clause(
            ("pkg", "1", 4),
            {"backendA": ["1"], "backendB": ["1"]},
            var_map,
            {},
        )

        self.assertEqual({(-6, -5, -4), (-4, 5, 6)}, self.normalize_clauses(clauses))

    def test_build_constraints_aggregates_core_clauses(self):
        visited = {
            "entry": ["1", "2"],
            "dep": ["1"],
            "ava": ["1"],
            "backendA": ["1"],
            "backendB": ["1"],
            "conflict": ["1"],
        }
        graphed = {
            "entry": {
                "1": {
                    "req": ["dep"],
                    "ava": ["ava"],
                    "ban": ["conflict"],
                    "alt": [],
                    "xor": [],
                    "exor": [["backendA", "backendB"]],
                },
                "2": {"req": [], "ava": [], "ban": [], "alt": [], "xor": [], "exor": []},
            }
        }
        solver = self.make_solver(visited=visited, graphed=graphed)
        var_map = {
            ("entry", "1"): 1,
            ("entry", "2"): 2,
            ("dep", "1"): 3,
            ("ava", "1"): 4,
            ("backendA", "1"): 5,
            ("backendB", "1"): 6,
            ("conflict", "1"): 7,
        }
        rel_var_map = {
            ("entry", "1"): {
                "req": {"dep": ["1"]},
                "ava": {"ava": ["1"]},
                "ban": {"conflict": ["1"]},
                "alt": {},
                "xor": {"backendA": ["1"], "backendB": ["1"]},
            },
            ("entry", "2"): {"req": {}, "ava": {}, "ban": {}, "alt": {}, "xor": {}},
            ("dep", "1"): {"req": {}, "ava": {}, "ban": {}, "alt": {}, "xor": {}},
            ("ava", "1"): {"req": {}, "ava": {}, "ban": {}, "alt": {}, "xor": {}},
            ("backendA", "1"): {"req": {}, "ava": {}, "ban": {}, "alt": {}, "xor": {}},
            ("backendB", "1"): {"req": {}, "ava": {}, "ban": {}, "alt": {}, "xor": {}},
            ("conflict", "1"): {"req": {}, "ava": {}, "ban": {}, "alt": {}, "xor": {}},
        }

        clauses = solver.build_constraints(["entry"], var_map, rel_var_map, visited)
        normalized = self.normalize_clauses(clauses)

        self.assertIn((-2, -1), normalized)
        self.assertIn((1, 2), normalized)
        self.assertIn((-7, -1), normalized)
        self.assertIn((-1, 3), normalized)
        self.assertIn((-1, 4), normalized)
        self.assertIn((-1, 5, 6), normalized)
        self.assertIn((-6, -5, -1), normalized)

    def test_entry_version_weight_outranks_dependency_depth_gain(self):
        solver = self.make_solver()
        visited = {"entry": [1, 2], "dep": [1, 2]}
        levels = {"entry": (0, 0), "dep": (3, 0)}

        weights = solver.build_solution_weights(["entry"], levels, visited)

        entry_gain = weights[("entry", 2)] - weights[("entry", 1)]
        dep_gain = weights[("dep", 2)] - weights[("dep", 1)]
        self.assertGreater(entry_gain, dep_gain)

    def test_build_solution_steps_ignores_empty_candidate_lists(self):
        solver = self.make_solver()
        visited = {"entry": [1, 2], "filtered": []}
        levels = {"entry": (0, 0), "filtered": (1, 0)}

        steps = solver.build_solution_steps(["entry"], levels, visited)

        self.assertIn("entry", steps)
        self.assertNotIn("filtered", steps)

    def test_dfs_priority_prefers_newer_entry_solution(self):
        solver = self.make_solver()
        visited = {"entry": [1, 2], "dep": [1, 2]}
        levels = {"entry": (0, 0), "dep": (3, 0)}
        solution_key = solver.build_solution_priority(["entry"], levels, visited)

        newer_entry = {"entry": 2, "dep": 1}
        older_entry = {"entry": 1, "dep": 2}

        self.assertGreater(solution_key(newer_entry), solution_key(older_entry))

    def test_dfs_priority_uses_score_within_same_solution_signature(self):
        solver = self.make_solver()
        visited = {"entry": [1, 2], "dep": [1, 2]}
        levels = {"entry": (0, 0), "dep": (3, 0)}
        solution_key = solver.build_solution_priority(["entry"], levels, visited)

        stronger_dependency = {"entry": 2, "dep": 2}
        weaker_dependency = {"entry": 2, "dep": 1}

        self.assertGreater(solution_key(stronger_dependency), solution_key(weaker_dependency))

    def test_dfs_priority_uses_entry_order_for_multi_entry_signature(self):
        solver = self.make_solver()
        visited = {"alpha": [1, 2], "beta": [1, 2]}
        levels = {"alpha": (0, 0), "beta": (0, 1)}

        alpha_first_key = solver.build_solution_priority(["alpha", "beta"], levels, visited)
        beta_first_key = solver.build_solution_priority(["beta", "alpha"], levels, visited)

        newer_alpha = {"alpha": 2, "beta": 1}
        newer_beta = {"alpha": 1, "beta": 2}

        self.assertGreater(alpha_first_key(newer_alpha), alpha_first_key(newer_beta))
        self.assertGreater(beta_first_key(newer_beta), beta_first_key(newer_alpha))

    def test_dfs_priority_uses_later_entry_as_signature_tiebreak(self):
        solver = self.make_solver()
        visited = {"alpha": [1, 2], "beta": [1, 2], "dep": [1, 2]}
        levels = {"alpha": (0, 0), "beta": (0, 1), "dep": (1, 0)}
        solution_key = solver.build_solution_priority(["alpha", "beta"], levels, visited)

        stronger_second_entry = {"alpha": 2, "beta": 2, "dep": 1}
        weaker_second_entry = {"alpha": 2, "beta": 1, "dep": 2}

        self.assertGreater(solution_key(stronger_second_entry), solution_key(weaker_second_entry))

    def test_build_solution_dfs_uses_shared_priority_model(self):
        visited = {"entry": [1, 2], "dep": [1, 2]}
        solver = self.make_solver(visited=visited)

        def build_all_solutions(entry_names, picked=None):
            _ = entry_names, picked
            yield collections.OrderedDict([("entry", 1), ("dep", 2)])
            yield collections.OrderedDict([("entry", 2), ("dep", 1)])

        solver.build_all_solutions = build_all_solutions

        best_solution = solver.build_solution_dfs(["entry"], visited)

        self.assertEqual(collections.OrderedDict([("entry", 2), ("dep", 1)]), best_solution)
        self.assertEqual(visited, solver.parent.package_graph["visited"])

    def test_build_entry_solution_sat_uses_request_order(self):
        try:
            importlib.import_module("pysat.formula")
        except ModuleNotFoundError:
            self.skipTest("pysat is not available in the current test environment")

        visited = {"alpha": ["1", "2"], "beta": ["1", "2"], "shared": ["1", "2"]}
        graphed = {
            "alpha": {
                "1": {"req": ["shared==1"], "ava": [], "ban": [], "alt": [], "xor": [], "exor": []},
                "2": {"req": ["shared==2"], "ava": [], "ban": [], "alt": [], "xor": [], "exor": []},
            },
            "beta": {
                "1": {"req": ["shared==2"], "ava": [], "ban": [], "alt": [], "xor": [], "exor": []},
                "2": {"req": ["shared==1"], "ava": [], "ban": [], "alt": [], "xor": [], "exor": []},
            },
            "shared": {
                "1": {"req": [], "ava": [], "ban": [], "alt": [], "xor": [], "exor": []},
                "2": {"req": [], "ava": [], "ban": [], "alt": [], "xor": [], "exor": []},
            },
        }
        resolve_filter_map = {
            ("alpha", "1", "req"): {"shared": ["1"]},
            ("alpha", "2", "req"): {"shared": ["2"]},
            ("beta", "1", "req"): {"shared": ["2"]},
            ("beta", "2", "req"): {"shared": ["1"]},
        }
        solver = self.make_solver(visited=visited, graphed=graphed, resolve_filter_map=resolve_filter_map)
        var_map, _, rel_var_map = solver.build_map_data(visited)
        constraints = solver.build_constraints(["alpha", "beta"], var_map, rel_var_map, visited)

        locked = solver.build_entry_solution_sat(["alpha", "beta"], visited, var_map, constraints)

        self.assertEqual(collections.OrderedDict([("alpha", "2"), ("beta", "1")]), locked)

    def test_build_entry_solution_sat_downgrades_first_entry_when_latest_breaks_global_solve(self):
        try:
            importlib.import_module("pysat.formula")
        except ModuleNotFoundError:
            self.skipTest("pysat is not available in the current test environment")

        visited = {"alpha": ["1", "2"], "beta": ["1"], "shared": ["1", "2"]}
        graphed = {
            "alpha": {
                "1": {"req": ["shared==1"], "ava": [], "ban": [], "alt": [], "xor": [], "exor": []},
                "2": {"req": ["shared==2"], "ava": [], "ban": [], "alt": [], "xor": [], "exor": []},
            },
            "beta": {
                "1": {"req": ["shared==1"], "ava": [], "ban": [], "alt": [], "xor": [], "exor": []},
            },
            "shared": {
                "1": {"req": [], "ava": [], "ban": [], "alt": [], "xor": [], "exor": []},
                "2": {"req": [], "ava": [], "ban": [], "alt": [], "xor": [], "exor": []},
            },
        }
        resolve_filter_map = {
            ("alpha", "1", "req"): {"shared": ["1"]},
            ("alpha", "2", "req"): {"shared": ["2"]},
            ("beta", "1", "req"): {"shared": ["1"]},
        }
        solver = self.make_solver(visited=visited, graphed=graphed, resolve_filter_map=resolve_filter_map)
        var_map, _, rel_var_map = solver.build_map_data(visited)
        constraints = solver.build_constraints(["alpha", "beta"], var_map, rel_var_map, visited)

        locked = solver.build_entry_solution_sat(["alpha", "beta"], visited, var_map, constraints)

        self.assertEqual(collections.OrderedDict([("alpha", "1"), ("beta", "1")]), locked)

    def test_build_feasible_solution_versions_sat_filters_tail_versions(self):
        try:
            importlib.import_module("pysat.formula")
        except ModuleNotFoundError:
            self.skipTest("pysat is not available in the current test environment")

        visited = {"alpha": ["1"], "beta": ["1"], "shared": ["1", "2"], "addon": ["1", "2"]}
        graphed = {
            "alpha": {
                "1": {"req": ["shared==1", "addon>=1"], "ava": [], "ban": [], "alt": [], "xor": [], "exor": []},
            },
            "beta": {
                "1": {"req": ["shared==1"], "ava": [], "ban": [], "alt": [], "xor": [], "exor": []},
            },
            "shared": {
                "1": {"req": [], "ava": [], "ban": [], "alt": [], "xor": [], "exor": []},
                "2": {"req": [], "ava": [], "ban": [], "alt": [], "xor": [], "exor": []},
            },
            "addon": {
                "1": {"req": [], "ava": [], "ban": [], "alt": [], "xor": [], "exor": []},
                "2": {"req": [], "ava": [], "ban": [], "alt": [], "xor": [], "exor": []},
            },
        }
        resolve_filter_map = {
            ("alpha", "1", "req"): {"shared": ["1"], "addon": ["1", "2"]},
            ("beta", "1", "req"): {"shared": ["1"]},
        }
        solver = self.make_solver(visited=visited, graphed=graphed, resolve_filter_map=resolve_filter_map)
        var_map, _, rel_var_map = solver.build_map_data(visited)
        constraints = solver.build_constraints(["alpha", "beta"], var_map, rel_var_map, visited)
        entry_assumptions = [var_map[("alpha", "1")], var_map[("beta", "1")]]

        feasible_versions = solver.build_feasible_solution_versions_sat(
            visited,
            var_map,
            constraints,
            assumptions=entry_assumptions,
            package_names=["shared", "addon"],
        )

        self.assertEqual(["1"], feasible_versions["shared"])
        self.assertEqual(["1", "2"], feasible_versions["addon"])

    def test_build_tail_solution_weights_skips_singleton_or_infeasible_tail_versions(self):
        solver = self.make_solver()
        visited = {"entry": [1, 2], "dep": [1, 2], "fixed": [1, 2], "leaf": [1]}
        levels = {"entry": (0, 0), "dep": (1, 0), "fixed": (1, 1), "leaf": (2, 0)}

        tail_weights = solver.build_tail_solution_weights(
            ["entry"],
            levels,
            visited,
            feasible_versions={"dep": [1, 2], "fixed": [2], "leaf": [1]},
        )

        self.assertIn(("dep", 1), tail_weights)
        self.assertIn(("dep", 2), tail_weights)
        self.assertNotIn(("fixed", 1), tail_weights)
        self.assertNotIn(("fixed", 2), tail_weights)
        self.assertNotIn(("leaf", 1), tail_weights)

    def test_build_valid_solutions_respects_ava_and_parent_solution(self):
        resolve_filter_map = {
            ("pkg", "1", "ava"): {"provider": ["1"]},
            ("pkg", "2", "ava"): {"provider": ["2"]},
        }
        solver = self.make_solver(resolve_filter_map=resolve_filter_map, solution={"provider": "1"})
        solutions = [collections.OrderedDict([("pkg", "1")]), collections.OrderedDict([("pkg", "2")])]

        valid = solver.build_valid_solutions(iter(solutions))

        self.assertEqual([collections.OrderedDict([("pkg", "1")])], valid)

    def test_build_valid_solutions_allows_req_via_alt_provider(self):
        graphed = {
            "consumer": {"1": {"req": ["virt>=1"], "ava": [], "ban": [], "alt": [], "xor": [], "exor": []}},
            "provider": {"1": {"req": [], "ava": [], "ban": [], "alt": ["virt>=1"], "xor": [], "exor": []}},
        }
        filters = {"alt": {"provider": {"1": ["virt>=1"]}}}
        resolve_filter_map = {
            ("consumer", "1", "req"): {"virt": []},
            ("provider", "1", "alt"): {"virt": [(">=", "1", None)]},
        }
        solver = self.make_solver(
            visited={"consumer": ["1"], "provider": ["1"]},
            graphed=graphed,
            filters=filters,
            resolve_filter_map=resolve_filter_map,
        )
        solutions = [collections.OrderedDict([("consumer", "1"), ("provider", "1")])]

        valid = solver.build_valid_solutions(iter(solutions))

        self.assertEqual(solutions, valid)

    def test_build_valid_solutions_rejects_xor_multi_match(self):
        graphed = {
            "pkg": {"1": {"req": [], "ava": [], "ban": [], "alt": [], "xor": [], "exor": [["backendA", "backendB"]]}},
        }
        resolve_filter_map = {("pkg", "1", "xor"): {"backendA": ["1"], "backendB": ["1"]}}
        solver = self.make_solver(
            visited={"pkg": ["1"], "backendA": ["1"], "backendB": ["1"]},
            graphed=graphed,
            resolve_filter_map=resolve_filter_map,
        )
        invalid = collections.OrderedDict([("pkg", "1"), ("backendA", "1"), ("backendB", "1")])
        valid = collections.OrderedDict([("pkg", "1"), ("backendA", "1")])

        solutions = solver.build_valid_solutions(iter([invalid, valid]))

        self.assertEqual([valid], solutions)

    def test_build_prune_solution_removes_orphaned_packages(self):
        solver = self.make_solver()
        solution = collections.OrderedDict([("entry", "1"), ("dep", "1"), ("leaf", "1")])
        rel_var_map = {
            ("entry", "1"): {"req": {"dep": ["1"]}, "xor": {}},
            ("dep", "1"): {"req": {}, "xor": {}},
            ("leaf", "1"): {"req": {}, "xor": {}},
        }

        pruned = solver.build_prune_solution(solution, ["entry"], rel_var_map)

        self.assertEqual(collections.OrderedDict([("entry", "1"), ("dep", "1")]), pruned)

    def test_build_prune_solution_keeps_xor_referenced_packages(self):
        solver = self.make_solver()
        solution = collections.OrderedDict([("entry", "1"), ("backend", "1")])
        rel_var_map = {
            ("entry", "1"): {"req": {}, "xor": {"backend": ["1"]}},
            ("backend", "1"): {"req": {}, "xor": {}},
        }

        pruned = solver.build_prune_solution(solution, ["entry"], rel_var_map)

        self.assertEqual(solution, pruned)

    def test_build_sort_solution_orders_by_level_then_position(self):
        solver = self.make_solver()
        solution = collections.OrderedDict([("depb", "1"), ("entry", "1"), ("leaf", "1"), ("depa", "1")])
        levels = {"entry": (0, 0), "depa": (1, 0), "depb": (1, 1), "leaf": (2, 0)}

        sorted_solution = solver.build_sort_solution(solution, levels)

        self.assertEqual(["entry", "depa", "depb", "leaf"], list(sorted_solution.keys()))

    def test_progressive_solve_widens_until_optimal_entry_solution_found(self):
        visited = {"entry": list(range(1, 13))}
        solver = self.make_solver(visited)
        solver.build_levels = lambda entry_names, visited: {"entry": (0, 0)}
        calls = []

        def solver_function(entry_names, visited):
            calls.append(len(visited["entry"]))
            if len(visited["entry"]) == 7:
                return {"entry": visited["entry"][-2]}
            if len(visited["entry"]) == 8:
                return {"entry": visited["entry"][-1]}
            return None

        result = solver.collect_progressively_solve(["entry"], solver_function)

        self.assertEqual({"entry": 12}, result)
        self.assertEqual([5, 6, 7, 8], calls)

    def test_progressive_solve_stops_after_first_optimal_entry_subset(self):
        visited = {
            "entry": list(range(1, 13)),
            "dep": list(range(1, 13)),
        }
        solver = self.make_solver(visited)
        solver.build_levels = lambda entry_names, visited: {"entry": (0, 0), "dep": (1, 0)}
        calls = []

        def solver_function(entry_names, visited):
            calls.append((len(visited["entry"]), len(visited["dep"])))
            if len(visited["entry"]) == 5:
                return {"entry": visited["entry"][-1], "dep": visited["dep"][-1]}
            raise AssertionError("solver should stop after the first optimal entry subset")

        result = solver.collect_progressively_solve(["entry"], solver_function)

        self.assertEqual({"entry": 12, "dep": 12}, result)
        self.assertEqual([(5, 5)], calls)

    def test_progressive_solve_falls_back_to_full_visited(self):
        visited = {"entry": list(range(1, 13))}
        solver = self.make_solver(visited)
        solver.build_levels = lambda entry_names, visited: {"entry": (0, 0)}
        calls = []

        def solver_function(entry_names, visited):
            calls.append(len(visited["entry"]))
            if len(visited["entry"]) == 12:
                return {"entry": visited["entry"][-1]}
            return None

        result = solver.collect_progressively_solve(["entry"], solver_function)

        self.assertEqual({"entry": 12}, result)
        self.assertEqual([5, 6, 7, 8, 9, 10, 12], calls)

    def test_progressive_solve_uses_custom_full_fallback_solver(self):
        visited = {"entry": list(range(1, 13))}
        solver = self.make_solver(visited)
        solver.build_levels = lambda entry_names, visited: {"entry": (0, 0)}
        subset_calls = []
        fallback_calls = []

        def subset_solver(entry_names, visited):
            _ = entry_names
            subset_calls.append(len(visited["entry"]))
            return None

        def fallback_solver(entry_names, visited):
            _ = entry_names
            fallback_calls.append(len(visited["entry"]))
            return {"entry": visited["entry"][-1]}

        result = solver.collect_progressively_solve(
            ["entry"],
            subset_solver,
            fallback_solver_function=fallback_solver,
        )

        self.assertEqual({"entry": 12}, result)
        self.assertEqual([5, 6, 7, 8, 9, 10], subset_calls)
        self.assertEqual([12], fallback_calls)

    def test_progressive_subset_keeps_dependency_floor_until_full_fallback(self):
        visited = {
            "entry": list(range(1, 13)),
            "dep": list(range(1, 13)),
        }
        solver = self.make_solver(visited)
        solver.build_levels = lambda entry_names, visited: {"entry": (0, 0), "dep": (1, 0)}
        subset_sizes = []

        def solver_function(entry_names, visited):
            subset_sizes.append((len(visited["entry"]), len(visited["dep"])))
            return None

        result = solver.collect_progressively_solve(["entry"], solver_function)

        self.assertIsNone(result)
        self.assertEqual(
            [(5, 5), (6, 5), (7, 5), (8, 5), (9, 5), (10, 5), (12, 12)],
            subset_sizes,
        )

    def test_progressive_solve_collects_verbose_info_when_unsolved(self):
        visited = {"entry": list(range(1, 13))}
        solver = self.make_solver(visited)
        solver.build_levels = lambda entry_names, visited: {"entry": (0, 0)}
        verbose_calls = []
        solver.collect_verbose_info = lambda original_visited: verbose_calls.append(original_visited)

        result = solver.collect_progressively_solve(["entry"], lambda entry_names, visited: None)

        self.assertIsNone(result)
        self.assertEqual([visited], verbose_calls)

    def test_collect_solution_uses_sat_for_full_fallback_when_sat_enabled(self):
        visited = {"entry": list(range(1, 13))}
        solver = self.make_solver(visited)
        solver.enable_sat = True
        solver.build_levels = lambda entry_names, visited: {"entry": (0, 0)}
        sat_calls = []

        def sat_solver(entry_names, visited):
            _ = entry_names
            sat_calls.append(len(visited["entry"]))
            if len(visited["entry"]) == 12:
                return collections.OrderedDict([("entry", visited["entry"][-1])])
            return None

        solver.build_solution_sat = sat_solver

        result = solver.collect_solution(["entry"])

        self.assertEqual({"entry": 12}, result)
        self.assertEqual([5, 6, 7, 8, 9, 10, 12], sat_calls)

    def test_collect_solution_uses_dfs_only_when_sat_disabled(self):
        visited = {"entry": list(range(1, 13))}
        solver = self.make_solver(visited)
        solver.enable_sat = False
        solver.build_levels = lambda entry_names, visited: {"entry": (0, 0)}
        dfs_calls = []

        def dfs_solver(entry_names, visited):
            _ = entry_names
            dfs_calls.append(len(visited["entry"]))
            return {"entry": visited["entry"][-1]}

        solver.build_solution_dfs = dfs_solver

        result = solver.collect_solution(["entry"])

        self.assertEqual({"entry": 12}, result)
        self.assertEqual([5], dfs_calls)


class WishCoreLogicTests(unittest.TestCase):
    def setUp(self):
        self._saved_env = {
            Config.Env.PACKAGE_PATH: os.environ.get(Config.Env.PACKAGE_PATH),
            Config.Env.PACKAGE_ROOT: os.environ.get(Config.Env.PACKAGE_ROOT),
            Config.Env.STORAGE_PATH: os.environ.get(Config.Env.STORAGE_PATH),
            Config.Env.DEVELOP_PATH: os.environ.get(Config.Env.DEVELOP_PATH),
            Config.Env.DEVELOP_MODE: os.environ.get(Config.Env.DEVELOP_MODE),
            Config.Env.OFFLINE_MODE: os.environ.get(Config.Env.OFFLINE_MODE),
            Config.Env.INHERIT_MODE: os.environ.get(Config.Env.INHERIT_MODE),
            Config.Env.ALIAS_PREFIX + "demo": os.environ.get(Config.Env.ALIAS_PREFIX + "demo"),
            "WISH_TEST_ENV": os.environ.get("WISH_TEST_ENV"),
        }
        self._saved_verbose = Config.VERBOSE

    def tearDown(self):
        for key, value in self._saved_env.items():
            if value is None:
                os.environ.pop(key, None)
            else:
                os.environ[key] = value
        setattr(Config, "VERBOSE", self._saved_verbose)
        self.reset_dbpool()

    def reset_dbpool(self):
        instances = getattr(DBPool, "_instances", None)
        if instances is not None:
            for pool in list(instances.values()):
                pool.close_all()
            instances.clear()

    def make_local_syncer(self, storage_path, s3_client=None, api_client=None, get_args_result="src.pkg"):
        os.environ[Config.Env.STORAGE_PATH] = storage_path
        syncer = object.__new__(Syncer)
        syncer.__dict__["config"] = Config
        syncer.__dict__["environ"] = Environ
        syncer.__dict__["thispath"] = Thispath
        syncer.__dict__["storage_path"] = storage_path
        syncer.__dict__["dbmanage"] = DBManage(Config, Environ)
        syncer.__dict__["locker"] = Locker()
        syncer.__dict__["max_client"] = 10
        syncer.__dict__["src_pkg"] = None
        syncer.__dict__["api_client"] = api_client or types.SimpleNamespace(logged=True)
        syncer.__dict__["s3_client"] = s3_client or types.SimpleNamespace(
            logged=True,
            get_etag=lambda src_pkg: "etag-1",
            download=lambda *args, **kwargs: None,
            unpack=lambda *args, **kwargs: None,
        )
        syncer.get_args = lambda name, tags, args: get_args_result
        return syncer

    def test_resolve_argv_parses_flags_and_path(self):
        resolver = Resolve()

        self.assertEqual(("pkg", ">=", "1.2", "C:/demo"), resolver.resolve_argv("pkg>=1.2@C:/demo"))
        self.assertEqual(("pkg", None, None, None), resolver.resolve_argv("pkg"))

    def test_combine_argv_prefers_path_and_exact_matches(self):
        resolver = Resolve()

        combined = resolver.combine_argv(
            [
                {0: resolver.resolve_argv("pkg=1.2")},
                {1: resolver.resolve_argv("pkg==1.2.3")},
                {2: resolver.resolve_argv("pkg@C:/demo")},
            ]
        )
        exact_only = resolver.combine_argv(
            [
                {0: resolver.resolve_argv("pkg=1.2")},
                {1: resolver.resolve_argv("pkg==1.2.3")},
            ]
        )

        self.assertEqual([(None, None, "C:/demo")], combined["pkg"])
        self.assertEqual([("==", "1.2.3", None)], exact_only["pkg"])

    def test_version_key_and_convert_rule_build_expected_intervals(self):
        resolver = Resolve()

        self.assertEqual([(1, 1), (0, "."), (1, 2), (0, "a"), (1, 3)], resolver.version_key("1.2a3"))
        exact_interval = resolver.convert_rule(("==", "1.2", None))
        prefix_interval = resolver.convert_rule(("=", "1.2", None))
        exclude_rule = resolver.convert_rule(("!=", "1.2", None))

        self.assertEqual(exact_interval[0], exact_interval[1])
        self.assertEqual([(1, 1), (0, "."), (1, 3)], prefix_interval[1])
        self.assertEqual("not", exclude_rule[0])

    def test_rules_compatible_detects_overlap_and_conflict(self):
        resolver = Resolve()

        self.assertTrue(resolver.rules_compatible([(">=", "1.0", None)], [("<", "3.0", None)]))
        self.assertFalse(resolver.rules_compatible([(">=", "3.0", None)], [("<", "3.0", None)]))

    def test_resolve_tags_supports_prefix_and_comparison_filters(self):
        resolver = Resolve()
        tags = ["1.1", "1.2", "1.2.1", "1.3"]

        self.assertEqual(["1.2", "1.2.1"], resolver.resolve_tags("=", "1.2", tags))
        self.assertEqual(["1.2", "1.2.1", "1.3"], resolver.resolve_tags(">=", "1.2", tags))

    def test_match_ranges_and_group_ranges_filter_expected_versions(self):
        resolver = Resolve()
        groups = resolver.group_ranges([(">=", "1.0", None), ("<", "2.0", None), ("==", "3.0", None)])

        matched = resolver.match_ranges(["0.9", "1.5", "2.0", "3.0"], groups)

        self.assertEqual([[("==", "3.0", None)], [(">=", "1.0", None), ("<", "2.0", None)]], groups)
        self.assertEqual(["1.5", "3.0"], matched)

    def test_environ_mutations_persist_in_order(self):
        env = Environ("WISH_TEST_ENV")

        self.assertTrue(env.setenv("A", "B", "A"))
        self.assertEqual(["A", "B"], Environ("WISH_TEST_ENV").envlist())

        env = Environ("WISH_TEST_ENV")
        self.assertTrue(env.insert("Z"))
        self.assertTrue(env.append("C"))
        self.assertTrue(env.remove("B"))
        self.assertTrue(env.unload("Z"))

        self.assertEqual(["A", "C"], Environ("WISH_TEST_ENV").envlist())

    def test_extractor_collects_selected_top_level_calls(self):
        tree = ast.parse("req('a')\nother()\nava('b')\n")
        extractor = Extractor("req", "ava")

        new_tree = extractor.visit(tree)

        self.assertEqual(["req", "ava"], [call.func.id for call in extractor.calls])
        self.assertEqual(1, len(new_tree.body))

    def test_thispath_and_nickname_operate_on_wish_env(self):
        package_root = os.path.join(os.getcwd(), "_wish_pkg_root")
        package_path = os.path.join(os.getcwd(), "_wish_pkg_path")
        target_path = os.path.join(package_path, "demo", "1.0", Config.PACKAGE_NAME)
        os.environ[Config.Env.PACKAGE_PATH] = package_path
        os.environ.pop(Config.Env.PACKAGE_ROOT, None)

        thispath = Thispath(target_path, env=True)
        Nickname.set("demo", "wish-demo")
        command = ["demo", "--help"]
        Nickname.replace(command)

        self.assertEqual("demo", thispath.name)
        self.assertEqual("1.0", thispath.tags)
        self.assertIn(os.path.join(package_path, "demo", "1.0"), Environ(Config.Env.PACKAGE_ROOT).envlist())
        self.assertEqual({"1.0": os.path.join(package_path, "demo", "1.0")}, thispath.envs("demo"))
        self.assertEqual(["wish-demo", "--help"], command)

    def test_process_paths_reverses_execution_order_and_updates_timestamps(self):
        require = Require()
        sync_calls = []
        db_calls = []
        require.solution = collections.OrderedDict([("root", "1"), ("dep", "2")])
        require.package_graph["graphed"].clear()
        require.package_graph["graphed"].update({
            "root": {"1": {"path": "root-path"}},
            "dep": {"2": {"path": "dep-path"}},
        })
        require.__dict__["syncer"] = types.SimpleNamespace(update_timestamp=lambda name, tags: sync_calls.append((name, tags)))
        require.__dict__["dbmanage"] = types.SimpleNamespace(update_timestamp=lambda name, tags: db_calls.append((name, tags)))

        paths = require.process_paths()

        self.assertEqual(["dep-path", "root-path"], paths)
        self.assertEqual([("root", "1"), ("dep", "2")], sync_calls)
        self.assertEqual([("root", "1"), ("dep", "2")], db_calls)

    def test_clear_inherit_removes_all_matching_paths_and_empty_vars(self):
        temp_dir = tempfile.mkdtemp(prefix="wish-clear-")
        try:
            package_root = os.path.join(temp_dir, "demo", "1")
            os.makedirs(package_root, exist_ok=True)
            with open(os.path.join(package_root, Config.PACKAGE_NAME), "w", encoding="utf-8") as file:
                file.write("")
            other_path = os.path.join(temp_dir, "other")
            os.makedirs(other_path, exist_ok=True)
            os.environ[Config.Env.INHERIT_MODE] = "0"
            os.environ[Config.Env.PACKAGE_PATH] = temp_dir
            os.environ[Config.Env.PACKAGE_ROOT] = package_root
            os.environ["WISH_CLEAR_TEST_PATH"] = os.pathsep.join(
                [os.path.join(package_root, "bin"), os.path.join(package_root, "lib"), other_path]
            )
            os.environ["WISH_CLEAR_TEST_ONLY"] = os.path.join(package_root, "only")

            Require().clear_inherit("demo", ["1"])

            self.assertEqual(other_path, os.environ["WISH_CLEAR_TEST_PATH"])
            self.assertNotIn("WISH_CLEAR_TEST_ONLY", os.environ)
        finally:
            os.environ.pop("WISH_CLEAR_TEST_PATH", None)
            os.environ.pop("WISH_CLEAR_TEST_ONLY", None)
            shutil.rmtree(temp_dir, ignore_errors=True)

    def test_clear_inherit_respects_inherit_mode_enabled(self):
        temp_dir = tempfile.mkdtemp(prefix="wish-inherit-")
        try:
            package_root = os.path.join(temp_dir, "demo", "1")
            os.makedirs(package_root, exist_ok=True)
            with open(os.path.join(package_root, Config.PACKAGE_NAME), "w", encoding="utf-8") as file:
                file.write("")
            keep_path = os.path.join(package_root, "bin")
            os.environ[Config.Env.INHERIT_MODE] = "1"
            os.environ[Config.Env.PACKAGE_PATH] = temp_dir
            os.environ[Config.Env.PACKAGE_ROOT] = package_root
            os.environ["WISH_KEEP_TEST_PATH"] = keep_path

            Require().clear_inherit("demo", ["1"])

            self.assertEqual(keep_path, os.environ["WISH_KEEP_TEST_PATH"])
        finally:
            os.environ.pop("WISH_KEEP_TEST_PATH", None)
            shutil.rmtree(temp_dir, ignore_errors=True)

    def test_clear_inherit_preserves_overlapping_tag_roots(self):
        temp_dir = tempfile.mkdtemp(prefix="wish-overlap-")
        try:
            root_one = os.path.join(temp_dir, "demo", "1")
            root_ten = os.path.join(temp_dir, "demo", "10")
            for package_root in (root_one, root_ten):
                os.makedirs(package_root, exist_ok=True)
                with open(os.path.join(package_root, Config.PACKAGE_NAME), "w", encoding="utf-8") as file:
                    file.write("")
            keep_path = os.path.join(root_ten, "bin")
            os.environ[Config.Env.INHERIT_MODE] = "0"
            os.environ[Config.Env.PACKAGE_PATH] = temp_dir
            os.environ[Config.Env.PACKAGE_ROOT] = os.pathsep.join([root_one, root_ten])
            os.environ["WISH_OVERLAP_TEST_PATH"] = os.pathsep.join([os.path.join(root_one, "bin"), keep_path])

            Require().clear_inherit("demo", ["1"])

            self.assertEqual(keep_path, os.environ["WISH_OVERLAP_TEST_PATH"])
        finally:
            os.environ.pop("WISH_OVERLAP_TEST_PATH", None)
            shutil.rmtree(temp_dir, ignore_errors=True)

    def test_exec_path_strips_dsl_calls_and_exposes_init_alias_and_env(self):
        temp_dir = tempfile.mkdtemp(prefix="wish-exec-")
        try:
            package_root = os.path.join(temp_dir, "demo", "1")
            os.makedirs(package_root, exist_ok=True)
            package_file = os.path.join(package_root, Config.PACKAGE_NAME)
            with open(package_file, "w", encoding="utf-8") as file:
                file.write(
                    'req("ghost")\n'
                    'env("WISH_EXEC_MARK").setenv("ready")\n'
                    'env("WISH_INIT_MARK").setenv("1" if this.init else "0")\n'
                    'alias("wish-exec", "python")\n'
                )
            os.environ[Config.Env.PACKAGE_PATH] = temp_dir
            os.environ[Config.Env.DEVELOP_MODE] = "2"

            Require().exec_path(package_file)

            self.assertEqual("ready", os.environ["WISH_EXEC_MARK"])
            self.assertEqual("1", os.environ["WISH_INIT_MARK"])
            self.assertEqual("python", os.environ[Config.Env.ALIAS_PREFIX + "wish-exec"])
            self.assertIn(package_root, Environ(Config.Env.PACKAGE_ROOT).envlist())
        finally:
            os.environ.pop("WISH_EXEC_MARK", None)
            os.environ.pop("WISH_INIT_MARK", None)
            os.environ.pop(Config.Env.ALIAS_PREFIX + "wish-exec", None)
            shutil.rmtree(temp_dir, ignore_errors=True)

    def test_exec_path_raises_network_error_for_missing_package_file(self):
        temp_dir = tempfile.mkdtemp(prefix="wish-network-")
        try:
            os.environ[Config.Env.PACKAGE_PATH] = temp_dir
            missing_path = os.path.join(temp_dir, "demo", "1", Config.PACKAGE_NAME)

            with contextlib.redirect_stderr(io.StringIO()):
                with self.assertRaises(SystemExit) as context:
                    Require().exec_path(missing_path)

            self.assertEqual(3, context.exception.code)
        finally:
            shutil.rmtree(temp_dir, ignore_errors=True)

    def test_exec_path_raises_config_error_for_invalid_package_syntax(self):
        temp_dir = tempfile.mkdtemp(prefix="wish-config-")
        try:
            package_root = os.path.join(temp_dir, "demo", "1")
            os.makedirs(package_root, exist_ok=True)
            package_file = os.path.join(package_root, Config.PACKAGE_NAME)
            with open(package_file, "w", encoding="utf-8") as file:
                file.write("def broken(:\n")
            os.environ[Config.Env.PACKAGE_PATH] = temp_dir

            stderr = io.StringIO()
            with contextlib.redirect_stderr(stderr):
                with self.assertRaises(SystemExit) as context:
                    Require().exec_path(package_file)

            self.assertEqual(2, context.exception.code)
            self.assertIn(package_file, stderr.getvalue())
        finally:
            shutil.rmtree(temp_dir, ignore_errors=True)

    def test_main_inserts_develop_path_when_enabled(self):
        temp_dir = tempfile.mkdtemp(prefix="wish-main-dev-")
        try:
            shared_path = os.path.join(temp_dir, "shared")
            develop_path = os.path.join(temp_dir, "develop")
            os.environ[Config.Env.PACKAGE_PATH] = shared_path
            os.environ[Config.Env.DEVELOP_PATH] = develop_path
            os.environ[Config.Env.DEVELOP_MODE] = "1"
            os.environ[Config.Env.OFFLINE_MODE] = "0"
            os.environ[Config.Env.INHERIT_MODE] = "0"

            with mock.patch.object(wish_module.Require, "exec") as exec_mock, mock.patch.object(
                wish_module.os, "system", return_value=0
            ), mock.patch.object(wish_module.sys, "argv", ["wish.py", "demo", "-", "python", "-V"]):
                with self.assertRaises(SystemExit) as context:
                    wish_module.main()

            self.assertEqual(0, context.exception.code)
            self.assertEqual([develop_path, shared_path], Environ(Config.Env.PACKAGE_PATH).envlist())
            exec_mock.assert_called_once_with("demo")
        finally:
            shutil.rmtree(temp_dir, ignore_errors=True)

    def test_main_removes_develop_path_when_disabled(self):
        temp_dir = tempfile.mkdtemp(prefix="wish-main-nodev-")
        try:
            shared_path = os.path.join(temp_dir, "shared")
            develop_path = os.path.join(temp_dir, "develop")
            os.environ[Config.Env.PACKAGE_PATH] = os.pathsep.join([develop_path, shared_path])
            os.environ[Config.Env.DEVELOP_PATH] = develop_path
            os.environ[Config.Env.DEVELOP_MODE] = "0"
            os.environ[Config.Env.OFFLINE_MODE] = "0"
            os.environ[Config.Env.INHERIT_MODE] = "0"

            with mock.patch.object(wish_module.Require, "exec") as exec_mock, mock.patch.object(
                wish_module.os, "system", return_value=0
            ), mock.patch.object(wish_module.sys, "argv", ["wish.py", "demo", "-", "python", "-V"]):
                with self.assertRaises(SystemExit) as context:
                    wish_module.main()

            self.assertEqual(0, context.exception.code)
            self.assertEqual([shared_path], Environ(Config.Env.PACKAGE_PATH).envlist())
            exec_mock.assert_called_once_with("demo")
        finally:
            shutil.rmtree(temp_dir, ignore_errors=True)

    def test_main_propagates_command_exit_code(self):
        with mock.patch.object(wish_module.Require, "exec") as exec_mock, mock.patch.object(
            wish_module.os, "system", return_value=512
        ), mock.patch.object(wish_module.sys, "argv", ["wish.py", "demo", "-", "python", "-V"]):
            with self.assertRaises(SystemExit) as context:
                wish_module.main()

        self.assertEqual(2, context.exception.code)
        exec_mock.assert_called_once_with("demo")

    def test_main_without_package_args_raises_no_param(self):
        stderr = io.StringIO()
        with mock.patch.object(wish_module.sys, "argv", ["wish.py"]), contextlib.redirect_stderr(stderr):
            with self.assertRaises(SystemExit) as context:
                wish_module.main()

        self.assertEqual(1, context.exception.code)
        self.assertIn("Package name must be specified", stderr.getvalue())

    def test_locker_context_creates_and_removes_lock_file(self):
        temp_dir = tempfile.mkdtemp(prefix="wish-lock-")
        try:
            locker = Locker()
            lock_path = locker._get_lock_file(temp_dir, "1", "download")

            with locker.start(temp_dir, "1", "download", timeout=1):
                self.assertTrue(os.path.exists(lock_path))

            self.assertFalse(os.path.exists(lock_path))
        finally:
            shutil.rmtree(temp_dir, ignore_errors=True)

    def test_locker_reclaims_stale_lock_after_timeout(self):
        temp_dir = tempfile.mkdtemp(prefix="wish-stale-lock-")
        try:
            locker = Locker()
            lock_path = locker._get_lock_file(temp_dir, "1", "download")
            os.makedirs(temp_dir, exist_ok=True)
            with open(lock_path, "w", encoding="utf-8") as file:
                file.write("stale")

            with mock.patch.object(wishapi_module.time, "sleep", return_value=None), contextlib.redirect_stdout(io.StringIO()):
                with locker.start(temp_dir, "1", "download", timeout=-1):
                    self.assertTrue(os.path.exists(lock_path))

            self.assertFalse(os.path.exists(lock_path))
        finally:
            shutil.rmtree(temp_dir, ignore_errors=True)

    def test_dbmanage_roundtrip_etag_and_timestamp_update(self):
        temp_dir = tempfile.mkdtemp(prefix="wish-db-")
        try:
            os.environ[Config.Env.STORAGE_PATH] = temp_dir
            manage = DBManage(Config, Environ)

            self.assertTrue(manage.write_db_etag("demo", "1", "etag-1"))
            self.assertEqual("etag-1", manage.query_db_etag("demo", "1"))
            self.assertTrue(manage.update_timestamp("demo", "1"))
            self.assertFalse(manage.update_timestamp("missing", "1"))
            manage.close()
        finally:
            shutil.rmtree(temp_dir, ignore_errors=True)

    def test_dbpool_uses_distinct_instances_per_database_path(self):
        temp_dir = tempfile.mkdtemp(prefix="wish-dbpool-")
        try:
            first_path = os.path.join(temp_dir, "first.db")
            second_path = os.path.join(temp_dir, "second.db")

            pool1 = DBPool(first_path, max_connections=1)
            pool2 = DBPool(second_path, max_connections=1)

            self.assertIsNot(pool1, pool2)
            self.assertEqual(first_path, getattr(pool1, "db_path"))
            self.assertEqual(second_path, getattr(pool2, "db_path"))
        finally:
            shutil.rmtree(temp_dir, ignore_errors=True)

    def test_dbcontext_rolls_back_and_releases_connection_on_exception(self):
        temp_dir = tempfile.mkdtemp(prefix="wish-dbctx-")
        try:
            db_path = os.path.join(temp_dir, "ctx.db")
            pool = DBPool(db_path, max_connections=1)

            with DBContext(pool) as (db, cursor):
                cursor.execute("CREATE TABLE sample (value INTEGER)")
                db.commit()

            with self.assertRaises(RuntimeError):
                with DBContext(pool) as (db, cursor):
                    cursor.execute("INSERT INTO sample(value) VALUES (1)")
                    raise RuntimeError("rollback")

            with sqlite3.connect(db_path) as conn:
                count = conn.execute("SELECT COUNT(*) FROM sample").fetchone()[0]

            self.assertEqual(0, count)
            self.assertFalse(getattr(pool, "_in_use"))
        finally:
            shutil.rmtree(temp_dir, ignore_errors=True)

    def test_dbmanage_autoclean_removes_stale_cache_and_db_entry(self):
        temp_dir = tempfile.mkdtemp(prefix="wish-autoclean-")
        try:
            os.environ[Config.Env.STORAGE_PATH] = temp_dir
            manage = DBManage(Config, Environ)
            pkg_path = os.path.join(temp_dir, "demo", "1")
            os.makedirs(pkg_path, exist_ok=True)
            self.assertTrue(manage.write_db_etag("demo", "1", "etag-1"))

            db_path = os.path.join(temp_dir, ".db")
            with sqlite3.connect(db_path) as conn:
                conn.execute("UPDATE caches SET timestamp = 0 WHERE name = ? AND tags = ?", ("demo", "1"))
                conn.commit()

            with contextlib.redirect_stdout(io.StringIO()):
                self.assertTrue(manage.autoclean_caches(days=30))
            self.assertFalse(os.path.exists(pkg_path))
            self.assertIsNone(manage.query_db_etag("demo", "1"))
            manage.close()
        finally:
            shutil.rmtree(temp_dir, ignore_errors=True)

    def test_dbmanage_instances_remain_isolated_across_storage_roots(self):
        temp_dir = tempfile.mkdtemp(prefix="wish-db-isolated-")
        try:
            storage_a = os.path.join(temp_dir, "storage-a")
            storage_b = os.path.join(temp_dir, "storage-b")

            os.environ[Config.Env.STORAGE_PATH] = storage_a
            manage_a = DBManage(Config, Environ)
            self.assertTrue(manage_a.write_db_etag("demo", "1", "etag-a"))

            os.environ[Config.Env.STORAGE_PATH] = storage_b
            manage_b = DBManage(Config, Environ)
            self.assertIsNone(manage_b.query_db_etag("demo", "1"))
            self.assertTrue(manage_b.write_db_etag("demo", "2", "etag-b"))

            self.assertEqual("etag-a", manage_a.query_db_etag("demo", "1"))
            self.assertIsNone(manage_a.query_db_etag("demo", "2"))
            self.assertEqual("etag-b", manage_b.query_db_etag("demo", "2"))

            manage_a.close()
            manage_b.close()
        finally:
            shutil.rmtree(temp_dir, ignore_errors=True)

    def test_dbmanage_autoclean_removes_missing_path_db_entry(self):
        temp_dir = tempfile.mkdtemp(prefix="wish-autoclean-missing-")
        try:
            os.environ[Config.Env.STORAGE_PATH] = temp_dir
            manage = DBManage(Config, Environ)
            self.assertTrue(manage.write_db_etag("ghost", "1", "etag-ghost"))

            db_path = os.path.join(temp_dir, ".db")
            with sqlite3.connect(db_path) as conn:
                conn.execute("UPDATE caches SET timestamp = 0 WHERE name = ? AND tags = ?", ("ghost", "1"))
                conn.commit()

            with contextlib.redirect_stdout(io.StringIO()):
                self.assertTrue(manage.autoclean_caches(days=30))
            self.assertIsNone(manage.query_db_etag("ghost", "1"))
            manage.close()
        finally:
            shutil.rmtree(temp_dir, ignore_errors=True)

    def test_dbmanage_autoclean_handles_multiple_stale_rows(self):
        temp_dir = tempfile.mkdtemp(prefix="wish-autoclean-multi-")
        try:
            os.environ[Config.Env.STORAGE_PATH] = temp_dir
            manage = DBManage(Config, Environ)
            existing_path = os.path.join(temp_dir, "demo", "1")
            os.makedirs(existing_path, exist_ok=True)
            self.assertTrue(manage.write_db_etag("demo", "1", "etag-1"))
            self.assertTrue(manage.write_db_etag("ghost", "2", "etag-2"))

            db_path = os.path.join(temp_dir, ".db")
            with sqlite3.connect(db_path) as conn:
                conn.execute("UPDATE caches SET timestamp = 0")
                conn.commit()

            with contextlib.redirect_stdout(io.StringIO()):
                self.assertTrue(manage.autoclean_caches(days=30))

            self.assertFalse(os.path.exists(existing_path))
            self.assertIsNone(manage.query_db_etag("demo", "1"))
            self.assertIsNone(manage.query_db_etag("ghost", "2"))
            manage.close()
        finally:
            shutil.rmtree(temp_dir, ignore_errors=True)

    def test_syncer_cache_pkgs_writes_etag_and_removes_tar_file(self):
        temp_dir = tempfile.mkdtemp(prefix="wish-sync-cache-")
        try:
            storage_path = os.path.join(temp_dir, "storage")
            root = os.path.join(storage_path, "demo", "1")

            def download(src_pkg, tar_pkg, tmp_path=None, name=None, tags=None):
                _ = src_pkg, tmp_path, name, tags
                os.makedirs(os.path.dirname(tar_pkg), exist_ok=True)
                with open(tar_pkg, "w", encoding="utf-8") as file:
                    file.write("pkg")

            def unpack(tar_pkg, cache_dir, name=None, tags=None):
                _ = tar_pkg, name, tags
                os.makedirs(cache_dir, exist_ok=True)
                with open(os.path.join(cache_dir, "payload.txt"), "w", encoding="utf-8") as file:
                    file.write("ok")

            syncer = self.make_local_syncer(
                storage_path,
                s3_client=types.SimpleNamespace(logged=True, get_etag=lambda src_pkg: "etag-1", download=download, unpack=unpack),
            )

            syncer.cache_pkgs("demo", "1", root, "src.pkg", "etag-1")

            self.assertTrue(os.path.exists(root))
            self.assertFalse(os.path.exists(root + ".pkg"))
            self.assertEqual("etag-1", getattr(syncer, "dbmanage").query_db_etag("demo", "1"))
            getattr(syncer, "dbmanage").close()
        finally:
            shutil.rmtree(temp_dir, ignore_errors=True)

    def test_syncer_clean_pkgs_skips_when_etag_matches(self):
        temp_dir = tempfile.mkdtemp(prefix="wish-sync-clean-")
        try:
            storage_path = os.path.join(temp_dir, "storage")
            os.environ[Config.Env.PACKAGE_PATH] = temp_dir
            root = os.path.join(storage_path, "demo", "1")
            os.makedirs(root, exist_ok=True)
            package_file = os.path.join(root, Config.PACKAGE_NAME)
            with open(package_file, "w", encoding="utf-8") as file:
                file.write("")

            syncer = self.make_local_syncer(
                storage_path,
                s3_client=types.SimpleNamespace(logged=True, get_etag=lambda src_pkg: "etag-1", download=lambda *a, **k: None, unpack=lambda *a, **k: None),
            )
            self.assertTrue(getattr(syncer, "dbmanage").write_db_etag("demo", "1", "etag-1"))

            result = syncer.clean_pkgs(package_file)

            self.assertFalse(result)
            self.assertTrue(os.path.exists(root))
            getattr(syncer, "dbmanage").close()
        finally:
            shutil.rmtree(temp_dir, ignore_errors=True)

    def test_syncer_clean_pkgs_respects_storage_root_boundary(self):
        temp_dir = tempfile.mkdtemp(prefix="wish-sync-boundary-")
        try:
            storage_path = os.path.join(temp_dir, "storage")
            sibling_root = os.path.join(temp_dir, "storage-other", "demo", "1")
            os.environ[Config.Env.PACKAGE_PATH] = temp_dir
            os.makedirs(sibling_root, exist_ok=True)
            package_file = os.path.join(sibling_root, Config.PACKAGE_NAME)
            with open(package_file, "w", encoding="utf-8") as file:
                file.write("")

            syncer = self.make_local_syncer(
                storage_path,
                s3_client=types.SimpleNamespace(logged=True, get_etag=lambda src_pkg: "etag-new", download=lambda *a, **k: None, unpack=lambda *a, **k: None),
            )

            result = syncer.clean_pkgs(package_file)

            self.assertFalse(result)
            self.assertTrue(os.path.exists(sibling_root))
            getattr(syncer, "dbmanage").close()
        finally:
            shutil.rmtree(temp_dir, ignore_errors=True)

    def test_syncer_first_api_client_uses_fallback_endpoint(self):
        temp_dir = tempfile.mkdtemp(prefix="wish-sync-api-")
        try:
            storage_path = os.path.join(temp_dir, "storage")
            os.environ[Config.Env.RESTAPI_URL + "1"] = "http://fallback:80"
            primary_api = types.SimpleNamespace(logged=True, get_tags=lambda name: [])
            syncer = self.make_local_syncer(storage_path, api_client=primary_api)

            fallback_api = types.SimpleNamespace(logged=True, get_tags=lambda name: ["1", "2"])
            with mock.patch.object(wishapi_module, "APIClient", return_value=fallback_api):
                result = syncer.first_api_client("get_tags", "demo")

            self.assertEqual(["1", "2"], result)
            getattr(syncer, "dbmanage").close()
        finally:
            os.environ.pop(Config.Env.RESTAPI_URL + "1", None)
            shutil.rmtree(temp_dir, ignore_errors=True)

    def test_syncer_first_api_client_recovers_from_primary_exception(self):
        temp_dir = tempfile.mkdtemp(prefix="wish-sync-api-exc-")
        try:
            storage_path = os.path.join(temp_dir, "storage")
            os.environ[Config.Env.RESTAPI_URL + "1"] = "http://fallback:80"

            def broken_get_tags(name):
                raise RuntimeError("primary api failed")

            primary_api = types.SimpleNamespace(logged=True, get_tags=broken_get_tags)
            syncer = self.make_local_syncer(storage_path, api_client=primary_api)
            fallback_api = types.SimpleNamespace(logged=True, get_tags=lambda name: ["fallback"])

            with mock.patch.object(wishapi_module, "APIClient", return_value=fallback_api):
                result = syncer.first_api_client("get_tags", "demo")

            self.assertEqual(["fallback"], result)
            getattr(syncer, "dbmanage").close()
        finally:
            os.environ.pop(Config.Env.RESTAPI_URL + "1", None)
            shutil.rmtree(temp_dir, ignore_errors=True)

    def test_syncer_sync_pkgs_uses_fallback_storage_client(self):
        temp_dir = tempfile.mkdtemp(prefix="wish-sync-s3-")
        try:
            storage_path = os.path.join(temp_dir, "storage")
            os.environ[Config.Env.PACKAGE_PATH] = storage_path
            os.environ[Config.Env.STORAGE_URL + "1"] = "http://fallback:9000"
            package_file = os.path.join(storage_path, "demo", "1", Config.PACKAGE_NAME)

            primary_s3 = types.SimpleNamespace(
                logged=True,
                get_etag=lambda src_pkg: (_ for _ in ()).throw(RuntimeError("primary failed")),
                download=lambda *a, **k: None,
                unpack=lambda *a, **k: None,
            )

            def download(src_pkg, tar_pkg, tmp_path=None, name=None, tags=None):
                _ = src_pkg, tmp_path, name, tags
                os.makedirs(os.path.dirname(tar_pkg), exist_ok=True)
                with open(tar_pkg, "w", encoding="utf-8") as file:
                    file.write("pkg")

            def unpack(tar_pkg, cache_dir, name=None, tags=None):
                _ = tar_pkg, name, tags
                os.makedirs(cache_dir, exist_ok=True)
                with open(os.path.join(cache_dir, "payload.txt"), "w", encoding="utf-8") as file:
                    file.write("ok")

            syncer = self.make_local_syncer(storage_path, s3_client=primary_s3)
            fallback_s3 = types.SimpleNamespace(logged=True, get_etag=lambda src_pkg: "etag-fallback", download=download, unpack=unpack)

            with mock.patch.object(wishapi_module, "S3Client", return_value=fallback_s3):
                result = syncer.sync_pkgs(package_file)

            self.assertTrue(result)
            self.assertTrue(os.path.exists(os.path.join(storage_path, "demo", "1")))
            self.assertEqual("etag-fallback", getattr(syncer, "dbmanage").query_db_etag("demo", "1"))
            getattr(syncer, "dbmanage").close()
        finally:
            os.environ.pop(Config.Env.STORAGE_URL + "1", None)
            shutil.rmtree(temp_dir, ignore_errors=True)

    def test_dbmanage_autoclean_preserves_later_row_when_cleanup_fails(self):
        temp_dir = tempfile.mkdtemp(prefix="wish-autoclean-partial-")
        try:
            os.environ[Config.Env.STORAGE_PATH] = temp_dir
            manage = DBManage(Config, Environ)
            first_path = os.path.join(temp_dir, "demo", "1")
            second_path = os.path.join(temp_dir, "demo", "2")
            os.makedirs(first_path, exist_ok=True)
            os.makedirs(second_path, exist_ok=True)
            self.assertTrue(manage.write_db_etag("demo", "1", "etag-1"))
            self.assertTrue(manage.write_db_etag("demo", "2", "etag-2"))

            db_path = os.path.join(temp_dir, ".db")
            with sqlite3.connect(db_path) as conn:
                conn.execute("UPDATE caches SET timestamp = 0")
                conn.commit()

            real_rename = wishapi_module.os.rename

            def rename_once_fail(src, dst):
                if src == second_path:
                    raise OSError("rename blocked")
                return real_rename(src, dst)

            with mock.patch.object(wishapi_module.os, "rename", side_effect=rename_once_fail), contextlib.redirect_stdout(io.StringIO()):
                self.assertTrue(manage.autoclean_caches(days=30))

            self.assertIsNone(manage.query_db_etag("demo", "1"))
            self.assertIsNotNone(manage.query_db_etag("demo", "2"))
            self.assertTrue(os.path.exists(second_path))
            manage.close()
        finally:
            shutil.rmtree(temp_dir, ignore_errors=True)


class WishIntegrationTests(unittest.TestCase):
    def setUp(self):
        self.repo_root = os.path.dirname(os.path.dirname(__file__))
        self._saved_env = {
            key: os.environ.get(key)
            for key in (
                Config.Env.PACKAGE_PATH,
                Config.Env.STORAGE_PATH,
                Config.Env.OFFLINE_MODE,
                Config.Env.DEVELOP_MODE,
                Config.Env.INHERIT_MODE,
                Config.Env.PACKAGE_ROOT,
                Config.Env.PACKAGE_EXTRA,
            )
        }
        self.temp_dir = tempfile.mkdtemp(prefix="wish-int-")
        self.package_root = os.path.join(self.temp_dir, "packages")
        self.storage_root = os.path.join(self.temp_dir, "storage")
        os.makedirs(self.package_root, exist_ok=True)
        os.makedirs(self.storage_root, exist_ok=True)

    def tearDown(self):
        for key, value in self._saved_env.items():
            if value is None:
                os.environ.pop(key, None)
            else:
                os.environ[key] = value
        shutil.rmtree(self.temp_dir, ignore_errors=True)

    def write_package(self, name, tag, content):
        package_dir = os.path.join(self.package_root, name, tag)
        os.makedirs(package_dir, exist_ok=True)
        with open(os.path.join(package_dir, Config.PACKAGE_NAME), "w", encoding="utf-8") as file:
            file.write(content)

    def configure_env(self):
        os.environ[Config.Env.PACKAGE_PATH] = self.package_root
        os.environ[Config.Env.STORAGE_PATH] = self.storage_root
        os.environ[Config.Env.OFFLINE_MODE] = "1"
        os.environ[Config.Env.DEVELOP_MODE] = "0"
        os.environ[Config.Env.INHERIT_MODE] = "0"
        os.environ.pop(Config.Env.PACKAGE_ROOT, None)
        os.environ.pop(Config.Env.PACKAGE_EXTRA, None)

    def make_require(self, enable_sat):
        require = Require()

        def load_solver():
            require.solver = Solver(require, Config, Environ)
            require.solver.enable_sat = enable_sat

        require.load_solver = load_solver
        require.load_dbmanage = lambda: setattr(require, "dbmanage", None)
        require.load_syncer = lambda: setattr(require, "syncer", None)
        return require

    def require_pysat(self):
        try:
            importlib.import_module("pysat.formula")
        except ModuleNotFoundError:
            self.skipTest("pysat is not available in the current test environment")

    def build_solver_regression_repo(self):
        self.write_package("root", "1", 'req("dep==10")\n')
        self.write_package("root", "2", 'req("dep==1")\n')
        for version in range(1, 11):
            self.write_package("dep", str(version), "")

    def build_multi_entry_regression_repo(self):
        self.write_package("alpha", "1", 'req("shared==1")\n')
        self.write_package("alpha", "2", 'req("shared==2")\n')
        self.write_package("beta", "1", 'req("shared==2")\n')
        self.write_package("beta", "2", 'req("shared==1")\n')
        for version in range(1, 3):
            self.write_package("shared", str(version), "")

    def build_entry_feasibility_repo(self):
        self.write_package("alpha", "1", 'req("shared==1")\n')
        self.write_package("alpha", "2", 'req("shared==2")\n')
        self.write_package("beta", "1", 'req("shared==1")\n')
        for version in range(1, 3):
            self.write_package("shared", str(version), "")

    def assert_latest_entry_solution(self, enable_sat):
        self.configure_env()
        self.build_solver_regression_repo()
        require = self.make_require(enable_sat)

        solution = require.process_pkgs(["root"], syncer=False)

        self.assertEqual("2", solution["root"])
        self.assertEqual("1", solution["dep"])

    def assert_multi_entry_solution(self, enable_sat, entry_names, expected):
        self.configure_env()
        self.build_multi_entry_regression_repo()
        require = self.make_require(enable_sat)

        solution = require.process_pkgs(entry_names, syncer=False)

        self.assertEqual(expected, dict(solution))

    def assert_entry_feasibility_solution(self, enable_sat):
        self.configure_env()
        self.build_entry_feasibility_repo()
        require = self.make_require(enable_sat)

        solution = require.process_pkgs(["alpha", "beta"], syncer=False)

        self.assertEqual({"alpha": "1", "beta": "1", "shared": "1"}, dict(solution))

    def test_integration_sat_prefers_latest_entry_after_full_fallback(self):
        self.require_pysat()
        self.assert_latest_entry_solution(enable_sat=True)

    def test_integration_dfs_prefers_latest_entry_after_full_fallback(self):
        self.assert_latest_entry_solution(enable_sat=False)

    def test_integration_sat_prefers_first_requested_entry_in_multi_entry_solve(self):
        self.require_pysat()
        self.assert_multi_entry_solution(
            enable_sat=True,
            entry_names=["alpha", "beta"],
            expected={"alpha": "2", "beta": "1", "shared": "2"},
        )

    def test_integration_dfs_prefers_first_requested_entry_in_multi_entry_solve(self):
        self.assert_multi_entry_solution(
            enable_sat=False,
            entry_names=["alpha", "beta"],
            expected={"alpha": "2", "beta": "1", "shared": "2"},
        )

    def test_integration_sat_respects_multi_entry_request_order(self):
        self.require_pysat()
        self.assert_multi_entry_solution(
            enable_sat=True,
            entry_names=["beta", "alpha"],
            expected={"beta": "2", "alpha": "1", "shared": "1"},
        )

    def test_integration_dfs_respects_multi_entry_request_order(self):
        self.assert_multi_entry_solution(
            enable_sat=False,
            entry_names=["beta", "alpha"],
            expected={"beta": "2", "alpha": "1", "shared": "1"},
        )

    def test_integration_sat_downgrades_first_entry_when_latest_blocks_remaining_entries(self):
        self.require_pysat()
        self.assert_entry_feasibility_solution(enable_sat=True)

    def test_integration_dfs_downgrades_first_entry_when_latest_blocks_remaining_entries(self):
        self.assert_entry_feasibility_solution(enable_sat=False)

    def test_integration_resolve_pending_loads_matching_extension(self):
        platform_name = sorted(Config.Platform()["platform"])[0]
        self.configure_env()
        self.write_package("base", "1", 'ext("addon@platform=%s")\n' % platform_name)
        self.write_package("addon", "1", 'env("WISH_EXT_MARK").setenv("enabled")\n')

        require = self.make_require(enable_sat=False)
        solution = require.process_pkgs(["base"], syncer=False)

        self.assertEqual("1", solution["base"])
        self.assertEqual("1", solution["addon"])

    def test_integration_cli_exec_sets_runtime_environment(self):
        self.configure_env()
        self.write_package("tool", "1", 'env("WISH_INTEGRATION_MARK").setenv("ready")\n')
        script_path = os.path.join(self.temp_dir, "print_mark.py")
        with open(script_path, "w", encoding="utf-8") as file:
            file.write('import os\nprint(os.getenv("WISH_INTEGRATION_MARK"))\n')
        env = os.environ.copy()
        command = [
            sys.executable,
            os.path.join(self.repo_root, "src", "wish.py"),
            "tool",
            "-",
            "python",
            script_path,
        ]

        result = subprocess.run(command, cwd=self.repo_root, capture_output=True, text=True, env=env)

        self.assertEqual(0, result.returncode)
        self.assertEqual("ready", result.stdout.strip())

    def test_integration_sat_alt_provider_satisfies_virtual_requirement(self):
        self.require_pysat()
        self.configure_env()
        self.write_package("root", "1", 'req("consumer", "provider")\n')
        self.write_package("consumer", "1", 'req("virt>=1")\n')
        self.write_package("provider", "1", 'alt("virt>=1")\n')

        require = self.make_require(enable_sat=True)
        solution = require.process_pkgs(["root"], syncer=False)

        self.assertEqual("1", solution["root"])
        self.assertEqual("1", solution["consumer"])
        self.assertEqual("1", solution["provider"])

    def test_integration_ava_filters_unavailable_versions(self):
        platform_name = sorted(Config.Platform()["platform"])[0]
        self.configure_env()
        self.write_package("app", "1", 'req("dep")\n')
        self.write_package("dep", "1", 'ava("platform=__never__")\n')
        self.write_package("dep", "2", 'ava("platform=%s")\n' % platform_name)

        require = self.make_require(enable_sat=False)
        solution = require.process_pkgs(["app"], syncer=False)

        self.assertEqual("1", solution["app"])
        self.assertEqual("2", solution["dep"])

    def test_integration_pending_extension_respects_ban_conflict(self):
        self.configure_env()
        platform_name = sorted(Config.Platform()["platform"])[0]
        self.write_package("base", "1", 'ban("addon")\next("addon@platform=%s")\n' % platform_name)
        self.write_package("addon", "1", 'env("WISH_PENDING_BAN").setenv("bad")\n')

        require = self.make_require(enable_sat=False)

        with contextlib.redirect_stderr(io.StringIO()):
            with self.assertRaises(SystemExit) as context:
                require.process_pkgs(["base"], syncer=False)

        self.assertEqual(5, context.exception.code)

    def test_integration_pending_extension_uses_alt_provider_trigger(self):
        self.require_pysat()
        self.configure_env()
        self.write_package("root", "1", 'req("base", "provider")\n')
        self.write_package("base", "1", 'ext("addon@virt>=1")\n')
        self.write_package("provider", "1", 'alt("virt>=1")\n')
        self.write_package("addon", "1", 'env("WISH_ALT_EXT_MARK").setenv("yes")\n')

        require = self.make_require(enable_sat=True)
        solution = require.process_pkgs(["root"], syncer=False)

        self.assertEqual("1", solution["root"])
        self.assertEqual("1", solution["base"])
        self.assertEqual("1", solution["provider"])
        self.assertEqual("1", solution["addon"])


if __name__ == "__main__":
    unittest.main()
