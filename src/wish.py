# -*- coding:utf-8
import os
import sys
import ast
import time
import operator
import platform
import traceback
import collections


class Config(object):
    VERBOSE = "-"
    PACKAGE_NAME = "package.py"

    class Platform(object):
        _platform_dict = None

        def __new__(cls):
            if cls._platform_dict is None:
                native_platform = sys.platform
                native_arch = platform.machine()
                if native_platform == "win32":
                    alias_platform = "windows"
                elif native_platform == "darwin":
                    alias_platform = "macos"
                elif native_platform.startswith("linux"):
                    alias_platform = "linux"
                elif native_platform.startswith("freebsd"):
                    alias_platform = "freebsd"
                else:
                    alias_platform = native_platform

                if native_arch in ("AMD64", "x86_64"):
                    alias_arch = "x86_64"
                elif native_arch in ("aarch64", "ARM64"):
                    alias_arch = "arm64"
                elif native_arch in ("i386", "i686", "x86"):
                    alias_arch = "x86"
                else:
                    alias_arch = native_arch
                cls._platform_dict = {
                    "platform": {native_platform, alias_platform},
                    "arch": {native_arch, alias_arch},
                    "release": {platform.release()},
                }
            return cls._platform_dict

    class Env(object):
        ALIAS_PREFIX = "WISH_ALIAS_"
        RESTAPI_URL = "WISH_RESTAPI_URL"
        STORAGE_URL = "WISH_STORAGE_URL"

        PACKAGE_ROOT = "WISH_PACKAGE_ROOT"
        PACKAGE_PATH = "WISH_PACKAGE_PATH"
        STORAGE_PATH = "WISH_STORAGE_PATH"
        DEVELOP_PATH = "WISH_DEVELOP_PATH"

        LOCK_MODE = "WISH_LOCK_MODE"
        DEVELOP_MODE = "WISH_DEVELOP_MODE"
        OFFLINE_MODE = "WISH_OFFLINE_MODE"

        PACKAGE_EXTRA = "WISH_PACKAGE_EXTRA"

    class Msg(object):
        MESSAGES = {
            "NO_PARAM": {
                "code": 1,
                "message": (
                    "Package name must be specified\n"
                    "Format example:wish name(required)@path(optional)=tags(optional) - cmd(optional)\n"
                    "Default tag = Get latest minor version\n"
                    "Use < instead of = to get lower version\n"
                    "Use > instead of = to get higher version\n"
                    "Use == instead of = to specify absolute version\n"
                    "Use != instead of = to exclude specific version\n"
                    "Use <= instead of = to get less than or equal version\n"
                    "Use >= instead of = to get greater than or equal version\n"
                    "Use + instead of - to get verbose information\n"
                ),
            },
            "CONFIG_ERROR": {
                "code": 2,
                "message": (
                    "Path: {}\n"
                    "Details: {}\n"
                    "Package defined specific keywords and modules\n"
                    "ban: Block with specific package\n"
                    "req: Require with specific packages\n"
                    "ext: extended with specific packages\n"
                    "ava: Available with specific packages\n"
                    "alt: Alternative with specific package\n"
                    "xor: Exclusive OR with specific packages\n"
                    "env: Environment variable operation module\n"
                    "alias: Alias for command\n"
                    "this: Information about current package, "
                    "including this.name, this.tags, this.root, this.init etc.\n"
                ),
            },
            "NETWORK_ERROR": {
                "code": 3,
                "message": (
                    "Error: Can not resolve network conditions: {} {} {}\n"
                    "Please check if network is connected or client is logged in\n"
                ),
            },
            "SPECPATH_ERROR": {
                "code": 4,
                "message": (
                    "Error: Specified {} path {} error\n"
                    "The specified path not exist or not a package path\n"
                    "Please check path exist or is a package path(need package.py)\n"
                ),
            },
            "RESOLVE_ERROR": {
                "code": 5,
                "message": (
                    "Error: Cannot resolve {} conditions\n"
                    "Please check requested package exists or package request conditions are met\n"
                ),
            },
            "PENDING_ERROR": {
                "code": 6,
                "message": (
                    "Error: Failed to auto-activate extension package '{}'\n"
                    "The extension package could not be resolved or its activation conditions were not met.\n"
                    "Please check if the extension conditions or the main package environment are correct.\n"
                    "Extension request info:\n{}\n"
                ),
            },
            "UNDEFINED": {
                "code": 255,
                "message": (
                    "Error: Undefined error type\n" "Error code: {}\n" "This may be a bug, please report this issue\n"
                ),
            },
        }

        @classmethod
        def error(cls, code_name, *args):
            error_info = cls.MESSAGES.get(code_name)
            if not error_info:
                error_info = cls.MESSAGES["UNDEFINED"]
            message = error_info["message"].format(*args)
            sys.stderr.write(message)
            sys.stderr.flush()
            sys.exit(error_info["code"])


class Environ(object):
    def __init__(self, name):
        self.__ename = name
        self.__elist = list()
        if os.environ.get(name):
            self.__elist = os.environ.get(name).split(os.pathsep)

    def environ_set(func):
        def wrapper(self, *args):
            if not args:
                return False
            func(self, *args)
            if self.__elist:
                target_env = list(set(self.__elist))
                target_env.sort(key=self.__elist.index)
                target_env = list(map(os.path.expandvars, target_env))
                os.environ[self.__ename] = os.pathsep.join(target_env)
            else:
                self.unset()
            return True

        return wrapper

    def envlist(self):
        return self.__elist

    def getenv(self):
        if self.__elist:
            return os.pathsep.join(self.__elist)

    def unset(self):
        if os.environ.get(self.__ename):
            return os.environ.pop(self.__ename)

    @environ_set
    def setenv(self, *args):
        self.__elist = list(args)

    @environ_set
    def insert(self, *args):
        self.__elist[:0] = args

    @environ_set
    def append(self, *args):
        self.__elist.extend(args)

    @environ_set
    def remove(self, *args):
        self.__elist = [i for i in self.__elist if i not in args]

    @environ_set
    def unload(self, *args):
        self.__elist = [i for i in self.__elist if not i.startswith(args)]


class Extractor(ast.NodeTransformer):
    def __init__(self, *func_names):
        self.func_names = set(func_names)
        self.calls = list()

    def visit_Expr(self, node):
        if isinstance(node.value, ast.Call):
            if isinstance(node.value.func, ast.Name):
                if node.value.func.id in self.func_names:
                    self.calls.append(node.value)
                    return None
        return self.generic_visit(node)


class Thispath(object):
    def __init__(self, path, env=False, init=False):
        self.init = init
        plist = path.split(os.sep)
        self.root = os.path.dirname(path)
        if self.part(path):
            self.name = plist[-3]
            self.tags = plist[-2]
        else:
            self.name = plist[-2]
            self.tags = None
        if env:
            Environ(Config.Env.PACKAGE_ROOT).append(self.root)

    def part(self, path):
        third_partys = Environ(Config.Env.PACKAGE_PATH).envlist()
        for party in third_partys:
            if path.startswith(party):
                return True

    def envs(self, name):
        tags_dict = dict()
        for root in Environ(Config.Env.PACKAGE_ROOT).envlist():
            plist = root.split(os.sep)
            pname = plist[-2]
            if pname == name:
                ptags = plist[-1]
                tags_dict[ptags] = root
        return tags_dict


class Nickname(object):
    @staticmethod
    def set(new_name, old_name):
        Environ(Config.Env.ALIAS_PREFIX + new_name).setenv(old_name)

    @staticmethod
    def replace(command_list):
        if command_list:
            cmd = command_list[0]
            alias_cmd = Environ(Config.Env.ALIAS_PREFIX + cmd).getenv()
            if alias_cmd:
                command_list[0] = alias_cmd


class Resolve(object):
    _MIN_V = object()
    _MAX_V = object()

    def __init__(self):
        self.operators = {
            "==": operator.eq,
            "!=": operator.ne,
            "<=": operator.le,
            ">=": operator.ge,
            "<": operator.lt,
            ">": operator.gt,
        }
        self.filters = {
            "req": dict(),
            "ava": dict(),
            "ban": dict(),
            "alt": dict(),
            "xor": dict(),
        }
        self.package_state = {
            "init": list(),
            "args": list(),
            "adap": list(),
        }

        self.package_graph = {
            "graphed": collections.OrderedDict(),
            "visited": collections.OrderedDict(),
            "pending": collections.OrderedDict(),
        }

    def safe_open(self, path):
        with open(path, "r", encoding="utf-8") as file:
            content = file.read()
            return content

    def safe_exists(self, path):
        if not os.path.exists(path):
            return False
        return os.path.realpath(path) == path

    def custom_sort(self, tags_list):
        def key_func(tag):
            parts = []
            for part in tag.split("."):
                if part.isdigit():
                    parts.append((1, int(part)))
                else:
                    parts.append((0, part))
            return parts

        return sorted(tags_list, key=key_func)

    def combine_cons(self, args):
        common_keys = set.intersection(*(set(d.keys()) for d in args))
        combined = collections.OrderedDict()
        for key in common_keys:
            seen = {}
            combined[key] = []
            for d in args:
                if key not in d:
                    continue
                for item in d[key]:
                    if item in seen:
                        continue
                    seen[item] = True
                    combined[key].append(item)
        return combined

    def combine_argv(self, pkgs):
        comb_dict = dict()
        for i in pkgs:
            for _, (name, flag, tags, path) in i.items():
                if name in comb_dict:
                    comb_list = comb_dict[name]
                else:
                    comb_list = list()
                comb_list.append((flag, tags, path))
                comb_dict[name] = self.prioriy_flag(comb_list)
        return comb_dict

    def prioriy_flag(self, clist):
        seen = set()
        clist = [i for i in clist if i not in seen and not seen.add(i)]
        prioriy = [(flag, tags, path) for (flag, tags, path) in clist if path]
        if prioriy:
            return [prioriy[-1]]
        prioriy = [(flag, tags, path) for (flag, tags, path) in clist if flag == "=="]
        if prioriy:
            return [prioriy[-1]]
        flag_order = (">=", "<=", "!=", ">", "<", "=")
        prioriy = [(flag, tags, path) for (flag, tags, path) in clist if flag in flag_order]
        if prioriy:
            return prioriy
        prioriy = [(flag, tags, path) for (flag, tags, path) in clist if flag is None]
        if prioriy:
            return prioriy

    def resolve_argv(self, argv):
        resolve_list = argv.split("@", 1)
        name = resolve_list.pop(0)
        flag, tags = None, None
        path = resolve_list[0] if resolve_list else None
        flag_order = ("==", ">=", "<=", "!=", "=", ">", "<")
        for flag_str in flag_order:
            if flag_str in name:
                name, tags = name.split(flag_str, 1)
                flag = flag_str
                break
        return name, flag, tags, path

    def version_key(self, tags):
        if tags is None:
            return
        processed_parts = list()
        current_num = ""
        current_str = ""

        for char in tags:
            if char.isdigit():
                if current_str:
                    processed_parts.append((0, current_str))
                    current_str = ""
                current_num += char
            else:
                if current_num:
                    processed_parts.append((1, int(current_num)))
                    current_num = ""
                current_str += char

        if current_num:
            processed_parts.append((1, int(current_num)))
        if current_str:
            processed_parts.append((0, current_str))
        return processed_parts

    def calculate_prefix_key(self, version_key):
        key_copy = list(version_key)
        for i in range(len(key_copy) - 1, -1, -1):
            part_type, part_value = key_copy[i]
            if part_type == 1:
                key_copy[i] = (1, part_value + 1)
                return key_copy[: i + 1]
        return self._MAX_V

    def convert_rule(self, rule):
        flag, version_str, _ = rule
        try:
            version = self.version_key(version_str)
        except (ValueError, TypeError):
            return (self._MIN_V, self._MAX_V, True, True)

        if flag == "==":
            return (version, version, True, True)
        elif flag == "=":
            return (version, self.calculate_prefix_key(version), True, False)
        elif flag == ">=":
            return (version, self._MAX_V, True, True)
        elif flag == ">":
            return (version, self._MAX_V, False, True)
        elif flag == "<=":
            return (self._MIN_V, version, True, True)
        elif flag == "<":
            return (self._MIN_V, version, True, False)
        elif flag == "!=":
            return ("not", version)
        return (self._MIN_V, self._MAX_V, True, True)

    def calculate_interval(self, int1, int2):
        l1, u1, li1, ui1 = int1
        l2, u2, li2, ui2 = int2

        if l1 is self._MIN_V:
            new_lower, new_lower_incl = l2, li2
        elif l2 is self._MIN_V:
            new_lower, new_lower_incl = l1, li1
        else:
            if l1 > l2:
                new_lower, new_lower_incl = l1, li1
            elif l2 > l1:
                new_lower, new_lower_incl = l2, li2
            else:
                new_lower, new_lower_incl = l1, li1 and li2

        if u1 is self._MAX_V:
            new_upper, new_upper_incl = u2, ui2
        elif u2 is self._MAX_V:
            new_upper, new_upper_incl = u1, ui1
        else:
            if u1 < u2:
                new_upper, new_upper_incl = u1, ui1
            elif u2 < u1:
                new_upper, new_upper_incl = u2, ui2
            else:
                new_upper, new_upper_incl = u1, ui1 and ui2

        if new_lower is not self._MIN_V and new_upper is not self._MAX_V:
            if new_lower > new_upper:
                return None
            if new_lower == new_upper and not (new_lower_incl and new_upper_incl):
                return None
        return (new_lower, new_upper, new_lower_incl, new_upper_incl)

    def rules_compatible(self, rules1, rules2):
        all_range_rules = [r for r in rules1 if r[0] != "!="] + [r for r in rules2 if r[0] != "!="]
        final_interval = (self._MIN_V, self._MAX_V, True, True)
        for rule in all_range_rules:
            rule_interval = self.convert_rule(rule)
            if rule_interval[0] == "not":
                continue
            final_interval = self.calculate_interval(final_interval, rule_interval)
            if final_interval is None:
                return False
        return final_interval is not None

    def resolve_tags(self, flag, tags, tags_list):
        filter_list = list()
        if not tags_list:
            return filter_list
        if not all(tags_list):
            return filter_list
        tags_list = self.custom_sort(tags_list)
        if not any((tags, flag)):
            return tags_list
        parsed_tags = self.version_key(tags)
        if not parsed_tags:
            return filter_list
        parsed_tags_list = [self.version_key(t) for t in tags_list]
        if flag == "=":
            for i, t in enumerate(parsed_tags_list):
                if t[0][0] == 0 and parsed_tags[0][0] == 0:
                    if t[0][1].startswith(parsed_tags[0][1]) and t[1 : len(parsed_tags)] == parsed_tags[1:]:
                        filter_list.append(tags_list[i])
                else:
                    if t[: len(parsed_tags)] == parsed_tags:
                        filter_list.append(tags_list[i])
        else:
            filter_list = [tags_list[i] for i, t in enumerate(parsed_tags_list) if self.operators[flag](t, parsed_tags)]
        return filter_list

    def match_ranges(self, tags_list, cons):
        matching_pkgs = list()
        for tags in tags_list:
            tags_parsed = self.version_key(tags)
            for con in cons:
                valid_list = list()
                for op, ver, _ in con:
                    ver_parsed = self.version_key(ver)
                    if op is None:
                        is_valid = True
                    elif op == "=":
                        is_valid = tags_parsed[: len(ver_parsed)] == ver_parsed
                    else:
                        is_valid = self.operators[op](tags_parsed, ver_parsed)
                    valid_list.append(is_valid)
                if all(valid_list):
                    matching_pkgs.append(tags)
                    break
        return matching_pkgs

    def group_ranges(self, cons):
        valid_groups = list()
        current_group = list()
        for condition in cons:
            op = condition[0]
            if op in [">", ">="]:
                if current_group:
                    valid_groups.append(current_group)
                current_group = [condition]
            elif op in ["<", "<="]:
                current_group.append(condition)
            else:
                valid_groups.append([condition])
        if current_group:
            valid_groups.append(current_group)
        return valid_groups


class Acquire(Resolve):
    def __init__(self):
        super(Acquire, self).__init__()
        self.syncer = None
        self.solver = None

    def parse_docs(self, path):
        if self.safe_exists(path):
            try:
                tree = ast.parse(self.safe_open(path))
                return ast.get_docstring(tree)
            except Exception:
                err = "".join(traceback.format_exception(*sys.exc_info()))
                Config.Msg.error("CONFIG_ERROR", path, err)

    def parse_argv(self, path, argv, extend=True):
        result = list()

        if self.safe_exists(path):
            try:
                tree = ast.parse(self.safe_open(path))
                extractor = Extractor(argv)
                extractor.visit(tree)
                for call in extractor.calls:
                    if extend:
                        result.extend([ast.literal_eval(arg) for arg in call.args])
                    else:
                        result.append([ast.literal_eval(arg) for arg in call.args])
            except Exception:
                err = "".join(traceback.format_exception(*sys.exc_info()))
                Config.Msg.error("CONFIG_ERROR", path, err)
        else:
            this = Thispath(path)
            name, tags = this.name, this.tags
            if self.syncer:
                if extend:
                    result.extend(self.syncer.get_args(name, tags, argv))
                else:
                    result.append(self.syncer.get_args(name, tags, argv))
            else:
                Config.Msg.error("NETWORK_ERROR", argv, name, tags)
        return result

    def resolve_spec(self, name, path):
        flag, tags = None, None
        resolve_dict = dict()
        if self.safe_exists(path):
            flag = "=="
            tags = os.path.basename(path)
            path = os.path.dirname(path)
            tags_list = self.resolve_vers(path, tags, flag)
            if tags_list:
                for tags in tags_list:
                    resolve_dict[tags] = [path]
                return resolve_dict
        Config.Msg.error("SPECPATH_ERROR", name, path)

    def resolve_vers(self, path, tags, flag):
        tags_list = list()
        for i in os.listdir(path):
            if i.startswith("."):
                continue
            if os.path.isdir(os.path.join(path, i)):
                package_file = os.path.join(path, i, Config.PACKAGE_NAME)
                if self.safe_exists(package_file):
                    tags_list.append(i)
        if tags_list:
            tags_list = self.resolve_tags(flag, tags, tags_list)
        return tags_list

    def resolve_cons(self, name, flag, tags, path):
        if path:
            return self.resolve_spec(name, path)
        resolve_dict = dict()
        storage_party = Environ(Config.Env.STORAGE_PATH).getenv()
        if self.syncer:
            tags_list = self.syncer.get_tags(name)
            tags_list = self.resolve_tags(flag, tags, tags_list)
            path = os.path.join(storage_party, name)
            for tag in tags_list:
                if resolve_dict.get(tag):
                    resolve_dict[tag].append(path)
                else:
                    resolve_dict[tag] = [path]
        third_partys = Environ(Config.Env.PACKAGE_PATH).envlist()
        for thirdparty in third_partys:
            if not self.safe_exists(thirdparty):
                continue
            path = os.path.join(thirdparty, name)
            if not self.safe_exists(path):
                continue
            tags_list = self.resolve_vers(path, tags, flag)
            if tags_list:
                for tag in tags_list:
                    if resolve_dict.get(tag):
                        resolve_dict[tag].append(path)
                    else:
                        resolve_dict[tag] = [path]
        return resolve_dict

    def resolve_filter(self, name, tags, key):
        resolve_dict = dict()
        key_filter = self.filters[key]
        platform_info = Config.Platform()
        if name in key_filter and tags in key_filter[name]:
            args = key_filter[name][tags]
            pkgs = self.combine_argv([{v: self.resolve_argv(v)} for v in args])
            for kname, kcons in pkgs.items():
                if kname in platform_info:
                    if not self.resolve_architecture(kname, kcons, platform_info):
                        return {kname: list()}
                    continue
                if kname not in self.package_graph["visited"]:
                    if key in ("alt",):
                        resolve_dict[kname] = kcons
                        continue
                    resolve_dict[kname] = list()
                    continue
                ktags_list = self.package_graph["visited"][kname]
                if key in ("req", "ban", "xor"):
                    for kc in kcons:
                        ktags_list = self.resolve_tags(kc[0], kc[1], ktags_list)
                if key in ("ava",):
                    group_cons = self.group_ranges(kcons)
                    ktags_list = self.match_ranges(ktags_list, group_cons)
                resolve_dict[kname] = ktags_list
        return resolve_dict

    def update_filter(self, name, tags, key):
        if name not in self.package_graph["graphed"]:
            return
        if self.package_graph["graphed"][name][tags][key]:
            if not self.filters[key].get(name):
                self.filters[key][name] = dict()
            if not self.filters[key][name].get(tags):
                self.filters[key][name][tags] = list()
            self.filters[key][name][tags] = self.package_graph["graphed"][name][tags][key]

    def build_filter(self, name_list=None):
        if name_list is None:
            name_list = list(self.package_graph["visited"].keys())
        for name in name_list:
            if name not in self.package_graph["visited"]:
                continue
            tags_list = self.package_graph["visited"][name]
            if not tags_list:
                continue
            for tags in tags_list:
                self.update_filter(name, tags, "req")
                self.update_filter(name, tags, "ava")
                self.update_filter(name, tags, "ban")
                self.update_filter(name, tags, "alt")
                self.update_filter(name, tags, "xor")

    def clear_inherit(self, name, tags_list):
        inherit_pkgs = Environ(Config.Env.PACKAGE_ROOT).envlist()
        inherit_pkgs = [os.path.join(i, Config.PACKAGE_NAME) for i in inherit_pkgs]
        for path in inherit_pkgs:
            this = Thispath(path)
            if this.name != name:
                continue
            if this.tags not in tags_list:
                continue
            for k, v in os.environ.items():
                if not v:
                    continue
                rm_flag = False
                v_list = list()
                v_list = v.split(os.pathsep)
                for sv in v_list:
                    if sv.startswith(this.root):
                        rm_flag = True
                        v_list.remove(sv)
                if rm_flag:
                    if v_list:
                        os.environ[k] = os.pathsep.join(v_list)
                    else:
                        os.environ.pop(k)

    def load_syncer(self):
        try:
            from wishapi import Syncer

            self.syncer = Syncer(Config, Environ, Thispath)
        except Exception:
            err = "".join(traceback.format_exception(*sys.exc_info()))
            if Config.VERBOSE == "+":
                sys.stdout.write(err)
                sys.stdout.flush()
            self.syncer = None

    def load_solver(self):
        try:
            from wishapi import Solver

            self.solver = Solver(self, Config, Environ)
        except Exception:
            err = "".join(traceback.format_exception(*sys.exc_info()))
            if Config.VERBOSE == "+":
                sys.stdout.write(err)
                sys.stdout.flush()
            self.solver = None

    def load_dbmanage(self):
        try:
            from wishapi import DBManage

            self.dbmanage = DBManage(Config, Environ)
        except Exception:
            err = "".join(traceback.format_exception(*sys.exc_info()))
            if Config.VERBOSE == "+":
                sys.stdout.write(err)
                sys.stdout.flush()
            self.dbmanage = None


class Require(Acquire):
    def __init__(self):
        super(Require, self).__init__()

    def resolve_pkgs(self, args):
        if args in self.package_state["args"]:
            return
        self.package_state["args"].append(args)
        pkgs = self.combine_argv([{argv: self.resolve_argv(argv)} for argv in args])
        if not self.package_state["init"]:
            self.package_state["init"] = list(pkgs.keys())
        for name, cons in pkgs.items():
            if name not in self.package_graph["graphed"]:
                self.package_graph["graphed"][name] = dict()
            if name not in self.package_graph["visited"]:
                self.package_graph["visited"][name] = list()
            vers = self.combine_cons([self.resolve_cons(name, *co) for co in cons])
            if name in self.package_state["init"]:
                init_tags = self.package_graph["visited"][name]
                if init_tags:
                    vers = {tags: path for tags, path in vers.items() if tags in init_tags}
                    self.package_graph["visited"][name] = list(vers.keys())
            for tags, paths in vers.items():
                path = os.path.join(paths[-1], tags, Config.PACKAGE_NAME)
                avas = self.parse_argv(path, "ava")
                if not self.resolve_platform(avas):
                    continue
                if name not in self.package_graph["visited"]:
                    self.package_graph["visited"][name] = list()
                if tags in self.package_graph["graphed"][name]:
                    continue
                reqs = self.parse_argv(path, "req")
                exts = self.parse_argv(path, "ext")
                bans = self.parse_argv(path, "ban")
                alts = self.parse_argv(path, "alt")
                xors = self.parse_argv(path, "xor")
                exors = self.parse_argv(path, "xor", extend=False)
                tags_dict = {
                    "ava": avas,
                    "req": reqs,
                    "ext": exts,
                    "ban": bans,
                    "alt": alts,
                    "xor": xors,
                    "exor": exors,
                    "path": path,
                }
                self.package_graph["graphed"][name][tags] = tags_dict
                self.package_graph["visited"][name].append(tags)
                self.vis_extra(exts, name, tags)
                if reqs:
                    self.resolve_pkgs(reqs)
                if xors:
                    self.resolve_pkgs(xors)

    def vis_extra(self, exts, name, tags):

        enable_extra_pkgs = Environ(Config.Env.PACKAGE_EXTRA).envlist()
        for args in exts:
            if "@" in args:
                if self.package_graph["pending"].get(name) is None:
                    self.package_graph["pending"][name] = dict()
                if self.package_graph["pending"][name].get(tags) is None:
                    self.package_graph["pending"][name][tags] = list()
                self.package_graph["pending"][name][tags].append(args)
            else:
                ext_name = self.resolve_argv(args)[0]
                if ext_name in enable_extra_pkgs:
                    if self.package_graph["pending"].get(ext_name) is None:
                        self.package_graph["pending"][ext_name] = dict()
                    if self.package_graph["pending"][ext_name].get(tags) is None:
                        self.package_graph["pending"][ext_name][tags] = list()
                    self.package_graph["pending"][ext_name][tags].append(args)

    def resolve_platform(self, args):
        platform_info = Config.Platform()
        pkgs = self.combine_argv([{argv: self.resolve_argv(argv)} for argv in args])
        for name, cons in pkgs.items():
            if name in platform_info:
                if not self.resolve_architecture(name, cons, platform_info):
                    return False
        return True

    def resolve_architecture(self, name, cons, platform_info):
        for flag, tags, _ in cons:
            if not self.resolve_tags(flag, tags, platform_info[name]):
                return False
        return True

    def resolve_pending(self, solution):
        sub_solution = collections.OrderedDict()
        filter_pending = list()
        for name, tags in solution.items():
            if name not in self.package_graph["pending"]:
                continue
            if tags not in self.package_graph["pending"][name]:
                continue
            filter_pending.extend(self.package_graph["pending"][name][tags])

        args = list()
        enas = collections.OrderedDict()
        for argv in filter_pending:
            if "@" in argv:
                argv, enav = argv.split("@")
                if enas.get(argv) is None:
                    enas[argv] = list()
                enas[argv].append(enav)
            else:
                args.append(argv)

        platform_info = Config.Platform()
        for ext_name, ext_env in enas.items():
            env_pkgs = self.combine_argv([{argv: self.resolve_argv(argv)} for argv in ext_env])
            for name, cons in env_pkgs.items():
                if name in platform_info:
                    if self.resolve_architecture(name, cons, platform_info):
                        args.append(ext_name)
                elif name in solution.keys():
                    tags_list = [solution[name]]
                    for c in cons:
                        tags_list = self.resolve_tags(c[0], c[1], tags_list)
                    if tags_list:
                        args.append(ext_name)

        if args:
            self.resolve_pkgs(args)
            pkgs = self.combine_argv([{argv: self.resolve_argv(argv)} for argv in args])
            names = list(pkgs.keys())
            for name in names:
                if name not in self.package_graph["visited"]:
                    Config.Msg.error("PENDING_ERROR", name, pkgs.get(name))
                if not self.package_graph["visited"][name]:
                    Config.Msg.error("PENDING_ERROR", name, pkgs.get(name))
            self.build_filter(names)
            sub_solution = self.solver.collect_solution(names)
            if not sub_solution:
                Config.Msg.error("RESOLVE_ERROR", names)
        return sub_solution

    def process_pkgs(self, args, syncer=True):
        self.solution = None
        self.load_solver()
        self.load_dbmanage()
        if syncer:
            self.load_syncer()
        self.resolve_pkgs(args)
        self.build_filter()
        for name in self.package_state["init"]:
            if name not in self.package_graph["visited"]:
                Config.Msg.error("RESOLVE_ERROR", name)
            if not self.package_graph["visited"][name]:
                Config.Msg.error("RESOLVE_ERROR", name)
        names = self.package_state["init"]
        self.solution = self.solver.collect_solution(names)
        if not self.solution:
            Config.Msg.error("RESOLVE_ERROR", names)
        sub_solution = self.resolve_pending(self.solution)
        self.solution = {**sub_solution, **self.solution}
        return self.solution

    def process_paths(self):
        self.path_list = list()
        for k, v in self.solution.items():
            graphed = self.package_graph["graphed"]
            if self.syncer:
                self.syncer.update_timestamp(k, v)
            if self.dbmanage:
                self.dbmanage.update_timestamp(k, v)
            self.path_list.append(graphed[k][v]["path"])
        self.path_list.reverse()
        return self.path_list

    def exec_path(self, path):
        init = False
        this = Thispath(path)
        if self.syncer:
            init = self.syncer.sync_pkgs(path)
        if not self.safe_exists(path):
            Config.Msg.error("NETWORK_ERROR", "req", this.name, this.tags)
        try:
            extractor = Extractor("req", "ava", "ext", "ban", "alt", "xor")
            tree = ast.parse(self.safe_open(path))
            ast_obj = extractor.visit(tree)
            code_obj = compile(ast_obj, filename=path, mode="exec")
            if Config.VERBOSE == "+":
                sys.stdout.write("Setup Path: {}\n".format(path))
                sys.stdout.flush()
            this = Thispath(path, env=True, init=init)
            modules = {
                "this": this,
                "env": Environ,
                "alias": Nickname.set,
                "__file__": path,
            }
            exec(code_obj, modules)
        except Exception:
            err = "".join(traceback.format_exception(*sys.exc_info()))
            Config.Msg.error("CONFIG_ERROR", path, err)

    def exec_reqs(self):
        for path in self.path_list:
            self.exec_path(path)
        inherit_pkgs = Environ(Config.Env.PACKAGE_ROOT).envlist()
        for path in inherit_pkgs:
            this = Thispath(os.path.join(path, Config.PACKAGE_NAME))
            if this.name not in self.package_graph["visited"]:
                self.clear_inherit(this.name, [this.tags])

    def exec(self, *args):
        if not args:
            Config.Msg.error("NO_PARAM")
        self.process_pkgs(args)
        self.process_paths()
        self.exec_reqs()


def main():
    command_list = list()
    command_argv = list()
    mark_list = ("-", "+")
    start_time = time.time()
    argv_list = sys.argv[1:]
    command = os.environ.get("SHELL")
    if not Environ(Config.Env.OFFLINE_MODE).getenv():
        Environ(Config.Env.OFFLINE_MODE).setenv("0")
    if not Environ(Config.Env.DEVELOP_MODE).getenv():
        Environ(Config.Env.DEVELOP_MODE).setenv("0")
    if not Environ(Config.Env.PACKAGE_PATH).getenv():
        Environ(Config.Env.PACKAGE_PATH).setenv(os.path.join(os.path.expanduser("~"), ".packages"))
    develop_path = Environ(Config.Env.DEVELOP_PATH).getenv()
    if develop_path:
        if Environ(Config.Env.DEVELOP_MODE).getenv() == "0":
            Environ(Config.Env.PACKAGE_PATH).remove(develop_path)
        else:
            Environ(Config.Env.PACKAGE_PATH).insert(develop_path)
    mark_info = {argv_list.index(i): i for i in mark_list if i in argv_list}
    if mark_info:
        Config.VERBOSE = mark_info.get(sorted(mark_info.keys())[0])
        num = argv_list.index(Config.VERBOSE) + 1
        command_list = argv_list[num:]
        command_argv = argv_list[: argv_list.index(Config.VERBOSE)]
    if Config.VERBOSE == "+":
        sys.stdout.write("Run: wish {}\n".format((" ").join(argv_list)))
        sys.stdout.flush()
    Require().exec(*command_argv)
    if Config.VERBOSE == "+":
        sys.stdout.write("Total Time: {:.2f}s\n".format(time.time() - start_time))
        sys.stdout.flush()
    Nickname.replace(command_list)
    command = (" ").join(command_list)
    exit_code = os.system(command)
    sys.exit(exit_code >> 8)


if __name__ == "__main__":
    main()
