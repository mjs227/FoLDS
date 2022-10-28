
import copy
import re


class PMRS:
    def __init__(self, quants=None, preds=None, weight=1):
        self.quants = quants if quants else []
        self.preds = preds if preds else []
        self.weight = weight
        self.var_history = []

    def __lt__(self, p):
        _, self_scope = self.pure_TL_rstr(scope=True)
        p_rstr = p.pure_TL_rstr()

        return pmrs_as_str(self_scope) == pmrs_as_str(p_rstr)

    def resolve_TLE(self, cnt, fai):
        if self.quants[0].kind == 'u':
            raise NotImplementedError

        e = self.quants[0].bvar

        if self.quants[0].kind == 'e_pass':
            e.name = 'EX_PASS'
        elif re.search(r'^x\d+', e.name):
            e.name = 'ex_' + str(cnt) + fai
            cnt += 1

        e.binder, self.quants = None, self.quants[1:]

        return e.name, cnt

    def pure_TL_rstr(self, scope=False):
        return self.pure_rstr_scope(0, scope=scope)

    def pure_rstr_scope(self, q_index, scope=False):
        if not self.quants[q_index].kind == 'u':
            raise NotImplementedError

        new_rstr_set = set(self.quants[q_index].rstr)
        scope_set = set(self.quants[q_index].scope)
        prstr_set, q_set = set(), set()
        rstr_set = set()

        while not len(new_rstr_set) == len(rstr_set):  # TODO: clean this up
            rstr_set = copy.deepcopy(new_rstr_set)

            for p in self.preds:
                if p in new_rstr_set:
                    added = True
                    temp_q_set = set()

                    for a in p.args:
                        if a.binder and not a.binder == self.quants[q_index]:
                            vs = set(a.predicates)

                            if len(vs.intersection(new_rstr_set)) > 0 and len(vs.intersection(scope_set)) == 0:
                                temp_q_set.add(a.binder)
                                new_rstr_set = new_rstr_set.union(vs)
                            else:
                                added = False
                                break

                    if added:
                        prstr_set.add(p)
                        q_set = q_set.union(temp_q_set)

        tl_rstr = PMRS(
            quants=[self.quants[i] for i in range(len(self.quants)) if self.quants[i] in q_set and not i == q_index],
            preds=[p for p in self.preds if p in prstr_set]
        )
        tl_rstr.var_history = list(self.var_history)

        if scope:
            tl_scope = PMRS(
                quants=[self.quants[i] for i in range(len(self.quants)) if not (self.quants[i] in q_set or i == q_index)],
                preds=[p for p in self.preds if p not in prstr_set],
                weight=self.weight
            )
            tl_scope.var_history = list(self.var_history)

            return tl_rstr, tl_scope

        return tl_rstr

    def TL_scope_rstr_as_str(self):
        bvar = self.quants[0].bvar.name
        self.quants[0].bvar.name = 'TL_bvar'
        strs = tuple(map(pmrs_as_str, self.pure_rstr_scope(0, scope=True)))
        self.quants[0].bvar.name = bvar

        return strs

    def __str__(self):
        return pmrs_as_str(self, debug=True)


class Quant:
    def __init__(self, bvar=None, rstr=None, scope=None, kind=None, pol=True):
        self.bvar = bvar
        self.rstr = rstr if rstr else []
        self.scope = scope
        self.kind = kind
        self.pol = pol
        self.coref = None

    def leq(self, q):
        return (not len(set(self.scope).intersection(set(q.rstr))) == 0) and len(set(self.rstr).intersection(set(q.scope))) == 0

    def to_json(self, preds):
        return {
            'kind': self.kind,
            'rstr': [preds.index(p) for p in self.rstr],
            'scope': [preds.index(p) for p in self.scope]
        }


class EP:
    def __init__(self, head='', args=None, pol=True):
        self.head = head
        self.args = args if args else []
        self.pol = pol

    def binders(self):
        for a in self.args:
            if a.binder:
                yield a.binder

    def __lt__(self, e):
        return self.head < e.head

    def to_json(self, quants, preds):
        return {
            'head': self.head,
            'pol': 'T' if self.pol else 'F',
            'args': [a.to_json(quants, preds) for a in self.args]
        }


class Entity:
    def __init__(self, name='', binder=None, predicates=None):
        self.name = name
        self.binder = binder
        self.predicates = predicates if predicates else []
        self.coref = None

    def to_json(self, quants):
        return {
            'name': self.name,
            'binder': quants.index(self.binder) if self.binder else 'NONE'
        }


class ConnPMRS:
    def __init__(self):
        self.quants = set()
        self.preds = set()

    def get_connected_components(self, pmrs):
        if len(pmrs.quants) == 0:
            yield pmrs
        elif len(pmrs.quants) == 1:
            vs = set(pmrs.quants[0].bvar.predicates)
            # vs = set(pmrs.quants[0].var_scope())

            if len(vs) == len(pmrs.preds):
                yield pmrs
            else:
                yield PMRS(quants=pmrs.quants, preds=[p for p in pmrs.preds if p in vs])
                yield PMRS(preds=[p for p in pmrs.preds if p not in vs])
        else:
            self.__gcc_rec__(pmrs.quants[0])

            yield PMRS(
                quants=[q for q in pmrs.quants if q in self.quants],
                preds=[p for p in pmrs.preds if p in self.preds]
            )

            if not (len(self.quants) == len(pmrs.quants) and len(self.preds) == len(pmrs.preds)):
                new_pmrs = PMRS(
                    quants=[q for q in pmrs.quants if q not in self.quants],
                    preds=[p for p in pmrs.preds if p not in self.preds]
                )
                self.quants.clear()
                self.preds.clear()

                for x in self.get_connected_components(new_pmrs):
                    yield x

    def __gcc_rec__(self, node):
        # set_1, set_2, fn = (self.quants, self.preds, lambda x: x.var_scope()) if type(node) is Quant else (self.preds, self.quants, lambda x: x.binders())
        set_1, set_2, fn = (self.quants, self.preds, lambda x: x.bvar.predicates) if type(node) is Quant else (self.preds, self.quants, lambda x: x.binders())
        set_1.add(node)

        for y in fn(node):
            if y not in set_2:
                self.__gcc_rec__(y)


class PO_node:
    def __init__(self, label):
        self.label = label
        self.rstr_str, self.scope_str = label.TL_scope_rstr_as_str()


class EvalPO:
    def __init__(self):
        self.terminals = set()
        self.rstr_dict = {}
        self.scope_dict = {}

    def insert_sorted(self, pmrs):
        n = PO_node(pmrs)
        remove_terminals = set()
        in_scope_dict = True

        if n.rstr_str not in self.scope_dict.keys():
            self.terminals.add(n)
            in_scope_dict = False

        if n.scope_str in self.rstr_dict.keys():
            rstr_dict_scope_str = self.rstr_dict[n.scope_str]

            for m in rstr_dict_scope_str:  # n < m
                if m in self.terminals and not (in_scope_dict and m in self.scope_dict[n.rstr_str]):
                    remove_terminals.add(m)

            if in_scope_dict and self.scope_dict[n.rstr_str] <= rstr_dict_scope_str:
                self.terminals.add(n)

        for k, d in [(n.scope_str, self.scope_dict), (n.rstr_str, self.rstr_dict)]:
            if k in d.keys():
                d[k].add(n)
            else:
                d.update({k: {n}})

        self.terminals = self.terminals - remove_terminals

    def pop_terminals(self):
        out0, out1, out_dict, new_terminals = [], [], {}, set()

        for n in self.terminals:
            if len(self.rstr_dict[n.rstr_str]) == 1:
                out0.append(n.label)
            else:
                out1.append(n.label)

            if n.rstr_str not in out_dict.keys():
                out_dict.update({n.rstr_str: len(self.rstr_dict[n.rstr_str]) == 1})

            for k, d in [(n.rstr_str, self.rstr_dict), (n.scope_str, self.scope_dict)]:
                if len(d[k]) == 1:
                    d.pop(k)
                else:
                    d[k] = d[k] - {n}

            if n.scope_str in self.rstr_dict.keys():
                for m in self.rstr_dict[n.scope_str] - self.terminals:
                    terminal = True

                    if m.rstr_str in self.scope_dict.keys():
                        for k in self.scope_dict[m.rstr_str]:
                            if not (k.rstr_str in self.scope_dict.keys() and m in self.scope_dict[k.rstr_str]):
                                terminal = False
                                break

                    if terminal:
                        new_terminals.add(m)

        if len(new_terminals) == 0:
            for k in self.rstr_dict.keys():
                new_terminals = new_terminals.union(self.rstr_dict[k])

            self.scope_dict.clear()
            self.rstr_dict.clear()
            self.terminals.clear()

            for x in new_terminals:
                self.insert_sorted(x)

            if len(self.terminals) == 0:
                self.terminals = new_terminals
        else:
            self.terminals = new_terminals

        return out0 + out1, out_dict


class Predicate:
    def __init__(self):
        self.args = []
        self.inst_dict = {}

    def create_instance(self, ep, weight):
        args = ep.args
        arg_label = []

        for i in range(len(args)):
            if i == len(self.args):
                self.args.append({args[i].name})
            else:
                self.args[i].add(args[i].name)

            arg_label.append(args[i].name)

        arg_label = tuple(arg_label)

        if arg_label not in self.inst_dict.keys():
            self.inst_dict.update({arg_label: [0, 0]})

        self.inst_dict[arg_label][0 if ep.pol else 1] += weight

        return arg_label

    def print_str(self, head):
        out_str = ''

        for k in self.inst_dict.keys():
            out_str += head + (('(' + k[0] + ')') if len(k) == 1 else str(k).replace('\'', '').replace(' ', '')) + ': ' + str(tuple(self.inst_dict[k])) + '\n'

        return out_str

    def check_val(self, ep):
        arg_list = tuple([ep.args[i].name for i in range(len(ep.args))])

        if arg_list in self.inst_dict.keys():
            x = self.inst_dict[arg_list]

            return x[0] / (x[0] + x[1])

        return None


class CorefCluster:
    def __init__(self):
        self.main_path = {}
        self.main_ent = None
        self.inst = []

    def update_main(self, path, branch, terminal):
        if len(path) == 0 and terminal:
            self.main_path.update({'': branch})
        else:
            self.__update_main_rec__(path, self.main_path, branch, terminal)

    def __update_main_rec__(self, path, main_path, branch, terminal):
        if len(path) == 0:
            raise Exception
        elif len(path) == 1:
            if terminal:
                main_path.update({path[0]: branch})
            else:
                if path[0] in main_path.keys():
                    main_path[path[0]].update({branch: {}})
                else:
                    main_path.update({path[0]: {branch: {}}})
        else:
            if path[0] not in main_path.keys():
                main_path.update({path[0]: {}})

            self.__update_main_rec__(path[1:], main_path[path[0]], branch, terminal)

    def check_main(self, path):
        if self.main_ent:
            return self.main_ent
        elif len(path) == 0:
            path = ['']
        elif len(path) == 1 and path[0] in self.main_path.keys():
            return self.main_path[path[0]]

        out_0, out_1 = self.__search_main__(path, self.main_path)

        return out_0 if out_0 is not None else out_1

    def __search_main__(self, path, main_path):
        if type(main_path) is str:
            return None, main_path

        if path[0] in main_path.keys():
            if len(path) == 1:
                if type(main_path[path[0]]) is str:
                    return main_path[path[0]], None

                return None, None

            return self.__check_main_rec__(path[1:], main_path[path[0]])

        out_0, out_1 = None, None

        for k in main_path.keys():
            out_0_temp, out_1_temp = self.__search_main__(path, main_path[k])
            out_0 = out_0_temp if out_0_temp is not None else out_0
            out_1 = out_1_temp if out_1_temp is not None else out_1

        return out_0, out_1

    def __check_main_rec__(self, path, main_path):
        if type(main_path) is str:
            return None, main_path

        if len(path) > 0 and path[0] in main_path.keys():
            if len(path) == 1 and type(main_path[path[0]]) is str:
                return main_path[path[0]], None

            return self.__check_main_rec__(path[1:], main_path[path[0]])

        return None, None

    def to_json(self):
        return {
            'main_ent': self.main_ent,
            'main_path': self.main_path,
            'inst': self.inst
        }

    def from_json(self, json_file):
        self.main_ent = json_file['main_ent']
        self.main_path = json_file['main_path']
        self.inst = json_file['inst']


def pmrs_as_str(pmrs, debug=False):
    out_str = '['
    bvars = {}

    for i in range(len(pmrs.quants)):
        if debug:
            out_str += pmrs.quants[i].kind + ','
        else:
            out_str += pmrs.quants[i].kind[0]

        bvars.update({pmrs.quants[i].bvar.name: ('qbv_' + str(i), pmrs.quants[i])})

    if debug and len(out_str) > 1:
        out_str = out_str[:-1]

    out_str += ']'

    for p in pmrs.preds:
        out_str += '.' + ('' if p.pol or not debug else '-') + p.head + '|'

        for arg in p.args:
            if arg.name in bvars.keys():
                bvar_name, quant = bvars[arg.name]

                if debug:
                    if arg.binder == quant:
                        out_str += bvar_name + ('_r|' if p in arg.binder.rstr else '|')
                    else:
                        out_str += arg.name + '(BU)|'
                else:
                    out_str += bvar_name + ('_r|' if p in arg.binder.rstr else '|')
            else:
                out_str += arg.name + '|'

    return out_str + ((' -- ' + str([q.coref for q in pmrs.quants])) if debug else '')
