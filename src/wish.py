# -*- coding:utf-8
import os
import sys
import ast
import time
import operator
import traceback
import collections


class Config(object):
    VERBOSE = "+"
    PLATFORM_KEY = "platform"
    PACKAGE_NAME = "package.py"

    class Env(object):
        ALIAS_PREFIX = "WISH_ALIAS_"
        RESTAPI_URL = "WISH_RESTAPI_URL"
        STORAGE_URL = "WISH_STORAGE_URL"
        PACKAGE_ROOT = "WISH_PACKAGE_ROOT"
        PACKAGE_PATH = "WISH_PACKAGE_PATH"
        STORAGE_PATH = "WISH_STORAGE_PATH"
        DEVELOP_PATH = "WISH_DEVELOP_PATH"
        PACKAGE_MODE = "WISH_PACKAGE_MODE"
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
                    "req: Require with specific packages\n"
                    "ext: extended with specific packages\n"
                    "ava: Available with specific packages\n"
                    "env: Environment variable operation module\n"
                    "ban: Block with specific package\n"
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
                    "resolve info:\n{}\n"
                ),
            },
            "UNDEFINED": {
                "code": 255,
                "message": (
                    "Error: Undefined error type\n"
                    "Error code: {}\n"
                    "This may be a bug, please report this issue\n"
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
        plist = path.split(os.sep)
        self.init = init
        self.name = plist[-3]
        self.tags = plist[-2]
        self.root = os.path.dirname(path)
        if env:
            Environ(Config.Env.PACKAGE_ROOT).append(self.root)

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
        }
        self.package_state = {
            "init": list(),
            "args": list(),
            "adap": list(),
        }

        self.package_graph = {
            "graphed": collections.OrderedDict(),
            "visited": collections.OrderedDict(),
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
        prioriy = [
            (flag, tags, path) for (flag, tags, path) in clist if flag in flag_order
        ]
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
                    processed_parts.append(current_str)
                    current_str = ""
                current_num += char
            else:
                if current_num:
                    processed_parts.append(int(current_num))
                    current_num = ""
                current_str += char

        if current_num:
            processed_parts.append(int(current_num))
        if current_str:
            processed_parts.append(current_str)

        return processed_parts

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
            filter_list = [
                tags_list[i]
                for i, t in enumerate(parsed_tags_list)
                if t[: len(parsed_tags)] == parsed_tags
            ]
        else:
            filter_list = [
                tags_list[i]
                for i, t in enumerate(parsed_tags_list)
                if self.operators[flag](t, parsed_tags)
            ]
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
            op = condition[1]
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

    def build_info(self, name):
        def get_version_info(pkg_name):
            if pkg_name not in self.package_graph.get("graphed", {}):
                return None, []
            available_vers = sorted(
                list(self.package_graph["graphed"][pkg_name].keys())
            )
            current_ver = None
            if (
                pkg_name in self.package_graph.get("visited", {})
                and self.package_graph["visited"][pkg_name]
            ):
                current_ver = self.package_graph["visited"][pkg_name][-1]
            else:
                current_ver = available_vers[-1] if available_vers else None
            return current_ver, available_vers

        def analyze_failure(pkg_name, version):
            if not version:
                return []

            reasons = []
            pkg_info = self.package_graph["graphed"][pkg_name][version]

            if "ava" in pkg_info:
                for req in pkg_info["ava"]:
                    req_name = self.resolve_argv(req)[0]
                    if req_name != Config.PLATFORM_KEY:
                        if (
                            req_name not in self.package_graph.get("visited", {})
                            or not self.package_graph["visited"][req_name]
                        ):
                            reasons.append("Availability requirement not met: %s" % req)
            if "req" in pkg_info:
                for req in pkg_info["req"]:
                    req_name = self.resolve_argv(req)[0]
                    if req_name not in self.package_graph.get("graphed", {}):
                        reasons.append("Required package not found: %s" % req)
                    elif (
                        req_name not in self.package_graph.get("visited", {})
                        or not self.package_graph["visited"][req_name]
                    ):
                        reasons.append(("dep", req_name, req))
            return reasons

        def build_tree(pkg_name, prefix="", visited=None):
            if visited is None:
                visited = set()
            visited.add(pkg_name)
            ver, _ = get_version_info(pkg_name)
            lines = ["%s%s (%s)" % (prefix, pkg_name, ver or None)]
            if (
                pkg_name not in self.package_graph.get("visited", {})
                or not self.package_graph["visited"][pkg_name]
            ):
                reasons = analyze_failure(pkg_name, ver)
                next_prefix = prefix + "  "

                for reason in reasons:
                    if isinstance(reason, tuple) and reason[0] == "dep":
                        _, dep_name, req = reason
                        lines.extend(
                            build_tree(dep_name, next_prefix + "└─ ", visited.copy())
                        )
                        lines.append("%s   req(%s)" % (next_prefix, req))
                    else:
                        lines.append("%s%s" % (next_prefix, reason))

            return lines

        return "\n".join(build_tree(name))


class Acquire(Resolve):
    def __init__(self):
        super(Acquire, self).__init__()
        self.syncer = None

    def parse_argv(self, path, argv):
        result = list()

        if self.safe_exists(path):
            try:
                tree = ast.parse(self.safe_open(path))
                extractor = Extractor(argv)
                extractor.visit(tree)
                for call in extractor.calls:
                    result.extend([ast.literal_eval(arg) for arg in call.args])
            except Exception:
                err = "".join(traceback.format_exception(*sys.exc_info()))
                Config.Msg.error("CONFIG_ERROR", path, err)
        else:
            this = Thispath(path)
            name, tags = this.name, this.tags
            if self.syncer:
                result.extend(self.syncer.get_args(name, tags, argv))
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

    def resolve_filter(self, name, tags, key, key_filter):
        resolve_dict = dict()
        if name in key_filter and tags in key_filter[name]:
            args = key_filter[name][tags]
            pkgs = self.combine_argv([{v: self.resolve_argv(v)} for v in args])
            for kname, kcons in pkgs.items():
                if kname == Config.PLATFORM_KEY:
                    continue
                if kname not in self.package_graph["visited"]:
                    resolve_dict[kname] = list()
                    continue
                ktags_list = self.package_graph["visited"][kname]
                if key in ("req", "ban"):
                    for kc in kcons:
                        ktags_list = self.resolve_tags(kc[0], kc[1], ktags_list)
                if key in ("ava"):
                    group_cons = self.group_ranges(kcons)
                    ktags_list = self.match_ranges(ktags_list, group_cons)
                resolve_dict[kname] = ktags_list
        return resolve_dict

    def recursion_tags(self, name, tags, real_visited):
        if real_visited.get(name):
            if tags not in real_visited[name]:
                real_visited[name].append(tags)
        else:
            real_visited[name] = [tags]
        resolve_req = self.resolve_filter(name, tags, "req", self.filters["req"])
        for rname, rtags_list in resolve_req.items():
            if rtags_list:
                rtags = rtags_list[-1]
                if real_visited.get(rname):
                    if rtags in real_visited[rname]:
                        continue
                    real_visited[rname].append(rtags)
                else:
                    real_visited[rname] = [rtags]
                self.recursion_tags(rname, rtags, real_visited)
            else:
                real_visited[rname] = rtags_list
        resolve_ava = self.resolve_filter(name, tags, "ava", self.filters["ava"])
        for aname, atags_list in resolve_ava.items():
            if atags_list:
                atags = atags_list[-1]
                if real_visited.get(aname):
                    if atags in real_visited[aname]:
                        continue
                    real_visited[aname].append(atags)
                else:
                    real_visited[aname] = [atags]
                self.recursion_tags(aname, atags, real_visited)
            else:
                real_visited[aname] = atags_list

    def update_filter(self, name, tags, key):
        if self.package_graph["graphed"][name][tags][key]:
            if not self.filters[key].get(name):
                self.filters[key][name] = dict()
            if not self.filters[key][name].get(tags):
                self.filters[key][name][tags] = list()
            self.filters[key][name][tags] = self.package_graph["graphed"][name][tags][
                key
            ]

    def ban_inherit(self, name, tags_list):
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

    def vis_inherit(self, vis_exists):
        inherit_pkgs = Environ(Config.Env.PACKAGE_ROOT).envlist()
        inherit_pkgs = [os.path.join(i, Config.PACKAGE_NAME) for i in inherit_pkgs]
        inherit_pkgs.reverse()
        for path in inherit_pkgs:
            if self.safe_exists(path):
                this = Thispath(path)
                if this.name not in vis_exists:
                    vis_exists[this.name] = [this.tags]
        return vis_exists

    def load_syncer(self):
        try:
            from wishapi import Syncer

            self.syncer = Syncer(Config, Environ, Thispath)
        except Exception:
            err = "".join(traceback.format_exception(*sys.exc_info()))
            if Config.VERBOSE == "+":
                sys.stdout.write("Load Error:\n")
                sys.stdout.write(err)
                sys.stdout.flush()
            self.syncer = None


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
            vers = self.combine_cons([self.resolve_cons(name, *co) for co in cons])
            for tags, paths in vers.items():
                path = os.path.join(paths[-1], tags, Config.PACKAGE_NAME)
                avas = self.parse_argv(path, "ava")
                if not self.resolve_platform(avas):
                    continue
                if name not in self.package_graph["visited"]:
                    self.package_graph["visited"][name] = list()
                if tags in self.package_graph["visited"][name]:
                    continue
                reqs = self.parse_argv(path, "req")
                exts = self.parse_argv(path, "ext")
                bans = self.parse_argv(path, "ban")
                tags_dict = {
                    "ava": avas,
                    "req": reqs,
                    "ext": exts,
                    "ban": bans,
                    "path": path,
                }
                self.package_graph["graphed"][name][tags] = tags_dict
                self.package_graph["visited"][name].append(tags)
                e_reqs = self.vis_extra(exts)
                if e_reqs:
                    reqs.extend(e_reqs)
                self.resolve_pkgs(reqs)

    def vis_extra(self, exts):
        reqs = list()
        enable_extra_pkgs = Environ(Config.Env.PACKAGE_EXTRA).envlist()
        for args in exts:
            if "@" in args:
                args, enas = args.split("@")
            else:
                enas = None
            name = self.resolve_argv(args)[0]
            if args in reqs:
                continue
            if name in enable_extra_pkgs:
                reqs.append(args)
            if self.resolve_autoadd(enas):
                reqs.append(args)
        return reqs

    def resolve_platform(self, args):
        pkgs = self.combine_argv([{argv: self.resolve_argv(argv)} for argv in args])
        for name, cons in pkgs.items():
            if name != Config.PLATFORM_KEY:
                continue
            if sys.platform not in [c[1] for c in cons]:
                return False
        return True

    def resolve_autoadd(self, argv):
        if argv is None:
            return False
        pkgs = self.combine_argv([{argv: self.resolve_argv(argv)}])
        for name, cons in pkgs.items():
            if name == Config.PLATFORM_KEY:
                if sys.platform in [c[1] for c in cons]:
                    return True
            else:
                current_visited = dict()
                self.vis_inherit(current_visited)
                if name not in current_visited:
                    continue
                for c in cons:
                    tags_list = self.resolve_tags(c[0], c[1], current_visited[name])
                    if tags_list:
                        return True
        return False

    def adaptive_tags(self, name, tags_list):
        if name in self.package_state["adap"]:
            return
        self.package_state["adap"].append(name)
        ctags_list = self.custom_sort(tags_list)
        while ctags_list:
            select_tags = True
            tags = ctags_list.pop()
            resolve_ava = self.resolve_filter(name, tags, "ava", self.filters["ava"])
            if resolve_ava:
                for aname, atags_list in resolve_ava.items():
                    if atags_list:
                        self.adaptive_tags(aname, atags_list)
                    else:
                        select_tags = False
            resolve_req = self.resolve_filter(name, tags, "req", self.filters["req"])
            if resolve_req:
                for rname, rtags_list in resolve_req.items():
                    if rtags_list:
                        self.adaptive_tags(rname, rtags_list)
                    else:
                        select_tags = False
            if select_tags:
                self.package_graph["visited"][name] = ctags_list + [tags]
                break
            if not ctags_list:
                self.package_graph["visited"][name] = ctags_list

    def exec_path(self, path):
        init = False
        this = Thispath(path)
        if self.syncer:
            init = self.syncer.sync_pkgs(path)
        if not self.safe_exists(path):
            Config.Msg.error("NETWORK_ERROR", "req", this.name, this.tags)
        try:
            extractor = Extractor("req", "ava", "ext", "ban")
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

    def apply_filter(self, real_visited):
        ban_data = dict()
        for name, tags_list in real_visited.items():
            if not tags_list:
                Config.Msg.error("RESOLVE_ERROR", name, self.build_info(name))
            tags = tags_list[-1]
            resolve_ban = self.resolve_filter(name, tags, "ban", self.filters["ban"])
            for bname, btags_list in resolve_ban.items():
                if not btags_list:
                    continue
                if bname not in ban_data:
                    ban_data[bname] = list()
                for i in btags_list:
                    ban_data[bname].append(i)
        for bname, blist in ban_data.items():
            self.ban_inherit(bname, blist)
            if bname not in real_visited:
                continue
            tags_list = real_visited[bname]
            for i in tags_list:
                if i in blist:
                    real_visited[bname].remove(i)
            if not real_visited[bname]:
                real_visited.pop(bname)
        return real_visited

    def process_pkgs(self, args, syncer=True):
        if syncer:
            self.load_syncer()
        self.resolve_pkgs(args)
        for name in self.package_graph["visited"].keys():
            tags_list = self.package_graph["visited"][name]
            if not tags_list:
                continue
            for tags in tags_list:
                self.update_filter(name, tags, "req")
                self.update_filter(name, tags, "ava")
                self.update_filter(name, tags, "ban")
        self.vis_inherit(self.package_graph["visited"])
        for name, tags_list in self.package_graph["visited"].items():
            self.adaptive_tags(name, tags_list)
        real_visited = collections.OrderedDict()
        for name in self.package_state["init"]:
            if name not in self.package_graph["visited"]:
                Config.Msg.error("RESOLVE_ERROR", name, self.build_info(name))
            if not self.package_graph["visited"][name]:
                Config.Msg.error("RESOLVE_ERROR", name, self.build_info(name))
            tags = self.package_graph["visited"][name][-1]
            self.recursion_tags(name, tags, real_visited)
        self.package_graph["visited"] = self.apply_filter(real_visited)
        return self.package_graph["visited"]

    def process_paths(self):
        self.path_list = list()
        for k, v in self.package_graph["visited"].items():
            graphed = self.package_graph["graphed"]
            v = self.custom_sort(v)
            if k in graphed:
                if self.syncer:
                    self.syncer.update_timestamp(k, v[-1])
                self.path_list.append(graphed[k][v[-1]]["path"])
        self.path_list.reverse()
        return self.path_list

    def exec_reqs(self):
        for path in self.path_list:
            self.exec_path(path)

    def exec(self, *args):
        if not args:
            Config.Msg.error("NO_PARAM")
        self.process_pkgs(args)
        self.process_paths()
        self.exec_reqs()


def main():
    command_list = list()
    mark_list = ("-", "+")
    start_time = time.time()
    argv_list = sys.argv[1:]
    command = os.environ.get("SHELL")
    if not Environ(Config.Env.PACKAGE_PATH).getenv():
        Environ(Config.Env.PACKAGE_PATH).setenv(
            os.path.join(os.path.expanduser("~"), ".packages")
        )
    if not Environ(Config.Env.PACKAGE_MODE).getenv():
        Environ(Config.Env.PACKAGE_MODE).setenv("0")
    storage_path = Environ(Config.Env.STORAGE_PATH).getenv()
    if storage_path:
        Environ(Config.Env.PACKAGE_PATH).insert(storage_path)
    develop_path = Environ(Config.Env.DEVELOP_PATH).getenv()
    if develop_path:
        if Environ(Config.Env.PACKAGE_MODE).getenv() == "0":
            Environ(Config.Env.PACKAGE_PATH).remove(develop_path)
        else:
            Environ(Config.Env.PACKAGE_PATH).insert(develop_path)
    mark_info = {argv_list.index(i): i for i in mark_list if i in argv_list}
    if mark_info:
        Config.VERBOSE = mark_info.get(sorted(mark_info.keys())[0])
        num = argv_list.index(Config.VERBOSE) + 1
        command_list = argv_list[num:]
        argv_list = argv_list[: argv_list.index(Config.VERBOSE)]
    Require().exec(*argv_list)
    if Config.VERBOSE == "+":
        sys.stdout.write("Total Time:  {:.2f}s\n".format(time.time() - start_time))
        sys.stdout.flush()
    Nickname.replace(command_list)
    command = (" ").join(command_list)
    exit_code = os.system(command)
    sys.exit(exit_code >> 8)


if __name__ == "__main__":
    main()
