
import re
import copy
import ParserStructures as ps


class Parser:
    def __init__(self, lmtzr, mrs_ops, mofy_dofw, tb_to_wn, f_index, a_index, dt, td):
        self.lmtzr = lmtzr
        self.mrs_ops = mrs_ops
        self.mofy_dofw = mofy_dofw
        self.tb_to_wn = tb_to_wn
        self.fa_index = (f_index, a_index)
        self.index = '_' + str(f_index) + '_' + str(a_index)
        self.dt, self.td = dt, td
        self.nq_pmrs, self.e_pmrs, self.pro_pmrs = [], [], []
        self.u_pmrs = ps.EvalPO()
        self.doc_dict, self.coref_data = {'SYMBOLS': {}}, {'GOOD': set(), 'TYPE': {}, 'CLUSTERS': {}}

    def parse(self, mrs_data):  # returns PMRSs and coref data
        coref_eq = {}
        all_pmrs, good_pmrs = [], set()
        and_or_err, pmrs_err = 0, 0

        for i in range(len(mrs_data)):
            mrs = mrs_data[i]
            qeq_dict, rels = mrs['qeq'], mrs['relations']

            try:
                and_or = self.and_or_res(rels, qeq_dict)
            except:
                and_or = []
                and_or_err += 1

            for m in and_or:
                try:
                    pmrs_list, all_coref_data, coref_eq = self.mrs_to_pmrs(m, qeq_dict, coref_eq, self.fa_index)
                except:
                    pmrs_list, all_coref_data = [], {}
                    pmrs_err += 1

                self.coref_data['TYPE'] = {**self.coref_data['TYPE'], **all_coref_data}
                all_pmrs += pmrs_list

        for i in range(len(all_pmrs)):
            p = all_pmrs[i]
            legal, good_coref = True, set()

            for q in p.quants:
                if q.coref is not None:
                    while q.coref in coref_eq.keys():
                        q.coref = coref_eq[q.coref]

                    if not q.kind == 'p':
                        good_coref.add(q.coref)

            for pr in p.preds:
                for a in pr.args:
                    if a.coref:
                        while a.coref[0] in coref_eq.keys():
                            a.coref = (coref_eq[a.coref[0]], a.coref[1])

                        coref_index, main = a.coref

                        if coref_index not in self.coref_data['CLUSTERS'].keys():
                            self.coref_data['CLUSTERS'].update({coref_index: ps.CorefCluster()})

                        if main:
                            self.coref_data['CLUSTERS'][coref_index].main_ent = a.name
                            good_coref.add(coref_index)
                        else:
                            self.coref_data['CLUSTERS'][coref_index].inst.append(a.name)

            for j in range(len(p.quants)):
                if p.quants[j].coref is not None and p.quants[j].kind == 'u':
                    rstr = p.pure_rstr_scope(j)

                    for pr in rstr.preds:
                        for a in pr.args:
                            if not (a == p.quants[j].bvar) and a.binder and a.binder.coref == p.quants[j].coref:
                                legal = False
                                break

                        if not legal:
                            break

                    if not legal:
                        break

            if legal:
                self.coref_data.update({'GOOD': self.coref_data['GOOD'].union(good_coref)})
                good_pmrs.add(i)

        for i in range(len(all_pmrs)):
            if i in good_pmrs:
                p = all_pmrs[i]

                for j in range(len(p.quants)):
                    if p.quants[j].kind == 'u' and p.quants[j].coref is not None:
                        rstr_j = p.pure_rstr_scope(j)
                        rstr_j_copy = copy.deepcopy(rstr_j)
                        self.coref_data['CLUSTERS'].update({
                            p.quants[j].coref: (
                                p.quants[j].bvar.name,
                                [k for k in range(len(rstr_j.preds)) if rstr_j.preds[k] in p.quants[j].rstr], rstr_j_copy)
                        })

        replaced = True

        while replaced:
            replaced = False

            for i in range(len(all_pmrs)):
                if i in good_pmrs:
                    p = all_pmrs[i]

                    for j in range(len(p.quants)):
                        q = p.quants[j]

                        if q.kind == 'p' and q.coref in self.coref_data['CLUSTERS'].keys() and type(self.coref_data['CLUSTERS'][q.coref]) is tuple:  # coref. is univ.
                            coref_bvar, rstr_list, coreferent = self.coref_data['CLUSTERS'][q.coref]
                            replaced, q.kind, q.coref = True, 'u', None
                            coref_pmrs, p_rstr = copy.deepcopy(coreferent), copy.deepcopy(q.rstr)
                            q.bvar.predicates = [pr for pr in q.bvar.predicates if pr not in q.rstr]
                            p.preds = [pr for pr in p.preds if pr not in q.rstr]
                            q.rstr.clear()
                            q.rstr = [coref_pmrs.preds[k] for k in rstr_list]

                            for rp in q.rstr:
                                for k in range(len(rp.args)):
                                    if rp.args[k].name == coref_bvar:
                                        rp.args[k] = q.bvar
                                        q.bvar.predicates.append(rp)

                            p.preds += coref_pmrs.preds
                            q.scope += p_rstr
                            p.preds.sort()
                            q.bvar.predicates.sort()
                            q.rstr.sort()
                            q.scope.sort()
                            p.quants = p.quants[:j + 1] + coref_pmrs.quants + p.quants[j + 1:]

        for i in range(len(all_pmrs)):
            if i in good_pmrs:
                p = all_pmrs[i]

                if len(p.quants) == 0:
                    self.nq_pmrs.append(p)
                elif p.quants[0].kind == 'u':
                    self.u_pmrs.insert_sorted(p)
                elif p.quants[0].kind == 'p':
                    self.pro_pmrs.append(p)
                else:
                    self.e_pmrs.append(p)

        coref_pop = set()

        for k, cl in self.coref_data['CLUSTERS'].items():
            if type(cl) is not tuple:
                if cl.main_ent:
                    for instance in cl.inst:
                        instance.name = cl.main_ent

                    cl.inst.clear()
            else:
                coref_pop.add(k)

        for k in coref_pop:
            self.coref_data['CLUSTERS'].pop(k)

        ex_count, self.pro_pmrs = self.remove_non_universals(0)
        terminate, check_count, pro_len_store = False, False, 0
        err_cnt = 10000

        while not (len(self.u_pmrs.terminals) + len(self.pro_pmrs) == 0 or terminate):
            err_cnt -= 1
            u_temp, u_pmrs_data = self.u_pmrs.pop_terminals()
            run, i = True, 0
            len_pro, len_u, len_e, len_nq = len(self.pro_pmrs), len(u_temp), len(self.e_pmrs), len(self.nq_pmrs)

            if err_cnt == 0:
                raise NotImplementedError

            if check_count:
                if pro_len_store == len_pro:
                    terminate = True

                pro_len_store = len_pro

            if len_u == 0 and len_e == 0 and len_nq == 0:
                check_count = True

            now = self.dt.now()

            while i < len(u_temp) and run:
                if self.dt.now() - now >= self.td:
                    raise NotImplementedError

                for x, run_ in self.res_TLU(u_temp[i], u_pmrs_data):
                    if len(x.quants) == 0:
                        self.nq_pmrs.append(x)
                    elif x.quants[0].kind == 'u':
                        self.u_pmrs.insert_sorted(x)
                    elif x.quants[0].kind == 'p':
                        self.pro_pmrs.append(x)
                    else:
                        self.e_pmrs.append(x)

                    run = run_

                i += 1

            for u in u_temp[i:]:
                self.u_pmrs.insert_sorted(u)

            ex_count, self.pro_pmrs = self.remove_non_universals(ex_count)

        return self.clean_doc_dict()

    def remove_non_universals(self, count):
        unreachable_coref, err_cnt = [], 20000

        while not len(self.e_pmrs) + len(self.pro_pmrs) + len(self.nq_pmrs) == 0:
            err_cnt -= 1

            if err_cnt == 0:
                raise NotImplementedError

            e_temp = copy.deepcopy(self.e_pmrs)
            self.e_pmrs.clear()
            self.pro_pmrs += unreachable_coref

            for p in e_temp:
                top_quant = p.quants[0]
                var_name, count = p.resolve_TLE(count, self.index)
                remove_preds = ps.PMRS(weight=p.weight)

                for pr in p.preds:
                    remove = True

                    for a in pr.args:
                        if a.binder is not None or (a.coref and not a.coref[1]):
                            remove = False
                            break

                    if remove:
                        remove_preds.preds.append(pr)

                p.preds = [pr for pr in p.preds if pr not in remove_preds.preds]
                self.update_doc_dict(remove_preds)

                if top_quant.coref is not None:
                    if top_quant.coref in self.coref_data['CLUSTERS'].keys():
                        cluster = self.coref_data['CLUSTERS'][top_quant.coref]

                        if type(cluster) is ps.CorefCluster:
                            cluster.update_main(p.var_history, var_name, True)
                    else:
                        cluster = ps.CorefCluster()
                        cluster.update_main(p.var_history, var_name, True)
                        self.coref_data['CLUSTERS'].update({top_quant.coref: cluster})

                if len(p.quants) == 0:
                    self.nq_pmrs.append(p)
                elif p.quants[0].kind == 'u':
                    self.u_pmrs.insert_sorted(p)
                elif p.quants[0].kind == 'p':
                    self.pro_pmrs.append(p)
                else:
                    self.e_pmrs.append(p)

            unreachable_coref = self.check_coref()
            self.pro_pmrs.clear()

            for p in self.nq_pmrs:
                coref_args = False

                for pr in p.preds:
                    for a in pr.args:
                        if (a.coref is not None) and (not a.coref[1]):
                            coref_args = True
                            p.quants.append(ps.Quant(kind='p', bvar=a, rstr=[], scope=[pr_ for pr_ in a.predicates]))
                            a.binder, p.quants[-1].coref = p.quants[-1], a.coref[0]
                            a.coref = None

                if coref_args:
                    self.pro_pmrs.append(p)
                else:
                    self.update_doc_dict(p)

            self.nq_pmrs.clear()

        return count, unreachable_coref

    def and_or_res(self, mrs, qeq_dict):
        i, l_mrs, r_mrs = 0, [], []
        no_conj, len_mrs = True, len(mrs)
        udef_q = set()

        while i < len_mrs and no_conj:
            if 'coref' in mrs[i].keys() and type(mrs[i]['coref'][0]) is int:
                mrs[i].update({'coref': (str(mrs[i]['coref'][0]) + self.index, mrs[i]['coref'][1])})

            if mrs[i]['predicate'] == 'udef_q':
                udef_q.add(mrs[i]['arguments']['ARG0'])

            if mrs[i]['predicate'] == '_but_c_not':
                if 'L-INDEX' in mrs[i]['arguments'].keys():
                    mrs[i].update({
                        'predicate': '_but+not_c',
                        'arguments': {
                            'ARG0': mrs[i]['arguments']['ARG0'],
                            'L-INDEX': mrs[i]['arguments']['R-INDEX'],
                            'R-INDEX': mrs[i]['arguments']['L-INDEX']
                        }
                    })
                else:
                    mrs[i].update({'predicate': 'INVALID'})
            elif mrs[i]['predicate'] == '_to+name+a+few_c':
                if 'L-INDEX' in mrs[i]['arguments'].keys():
                    mrs[i].update({
                        'predicate': '_be_v_id',
                        'arguments': {
                            'ARG1': mrs[i]['arguments']['ARG0'],
                            'ARG2': mrs[i]['arguments']['L-INDEX']
                        }
                    })
                else:
                    mrs[i].update({'predicate': 'INVALID'})

            if mrs[i]['predicate'] in self.mrs_ops['conn']:
                if 'L-INDEX' in mrs[i]['arguments'].keys():  # and 'L-HNDL' not in mrs[i]['arguments'].keys():
                    arg0, neg_conn = mrs[i]['arguments']['ARG0'], mrs[i]['predicate'] in self.mrs_ops['neg_conn']
                    l_index, r_index = mrs[i]['arguments']['L-INDEX'], mrs[i]['arguments']['R-INDEX']
                    index_set = {l_index, r_index}
                    no_conj, quants = False, {}
                    arg0 = mrs[i]['arguments']['ARG0']

                    if arg0[0] == 'e':
                        if neg_conn:
                            if 'L-HNDL' in mrs[i]['arguments'].keys():
                                mrs.append({
                                    'label': mrs[i]['label'],
                                    'predicate': 'neg',
                                    'arguments': {'ARG1': mrs[i]['arguments']['R-HNDL']}
                                })
                                index_set = {l_index}
                            else:
                                neg_conn = False

                        handle_args, handle_cands = [], set()

                        for j in range(len(mrs)):
                            if not j == i:
                                new_args, inst = {}, False

                                for k in mrs[j]['arguments'].keys():
                                    if mrs[j]['arguments'][k] in index_set:
                                        new_args.update({k: arg0})
                                        handle_cands.add(mrs[j]['label'])
                                        inst = True
                                    else:
                                        if mrs[j]['arguments'][k][0] == 'h':
                                            handle_args.append((j, k, mrs[j]['arguments'][k]))

                                        new_args.update({k: mrs[j]['arguments'][k]})

                                mrs[j].update({'arguments': new_args})

                                if inst:
                                    mrs[j].update({'label': mrs[i]['label']})

                        if not neg_conn:
                            for j, k, h in handle_args:
                                if h in handle_cands or (h in qeq_dict.keys() and qeq_dict[h] in handle_cands):
                                    mrs[j]['arguments'].update({k: mrs[i]['label']})

                        return self.and_or_res(mrs[:i] + mrs[i + 1:], qeq_dict)
                    elif arg0[0] in {'x', 'i'}:
                        if neg_conn and r_index[0] == 'x':
                            r_mrs.append({
                                'label': mrs[i]['label'],
                                'predicate': '_not_x_deg',
                                'arguments': {'ARG0': r_index}
                            })

                        lower_conj = arg0 not in udef_q

                        for j in range(len(mrs)):
                            quant = is_type(mrs[j]['predicate'], 'q')
                            l_mrs_j, r_mrs_j = copy.deepcopy(mrs[j]), copy.deepcopy(mrs[j])
                            valid, tl_quant = False, False

                            if lower_conj and quant:
                                valid = True

                                if mrs[j]['arguments']['ARG0'] == arg0:
                                    l_mrs_j['arguments'].update({'ARG0': l_index})
                                    r_mrs_j['arguments'].update({'ARG0': r_index})
                                    tl_quant = 'coref' not in mrs[j].keys()
                                elif mrs[j]['arguments']['ARG0'] in {l_index, r_index}:
                                    continue
                            elif not ((quant and mrs[j]['arguments']['ARG0'] == arg0) or j == i):
                                valid = True

                            if valid:
                                quant, bvar = quant and not mrs[j]['predicate'] in self.mrs_ops['proper'], ''
                                l_add, r_add = True, True

                                for k in mrs[j]['arguments'].keys():
                                    arg_k = mrs[j]['arguments'][k]

                                    if arg_k == arg0:
                                        l_mrs_j['arguments'].update({k: l_index})
                                        r_mrs_j['arguments'].update({k: r_index})
                                    elif arg_k == l_index:
                                        r_add = False
                                    elif arg_k == r_index:
                                        l_add = False
                                    elif arg_k[0] == 'x' and quant:
                                        bvar = arg_k

                                if l_add:
                                    l_mrs.append(l_mrs_j)

                                if r_add:
                                    r_mrs.append(r_mrs_j)

                                if quant and l_add and r_add and not tl_quant:
                                    quants.update({bvar: (len(l_mrs) - 1, len(r_mrs) - 1)})

                        for k in quants.keys():
                            l_k, r_k = quants[k]

                            if 'coref' in l_mrs[l_k].keys():
                                c_i, main = l_mrs[l_k]['coref']

                                if main:
                                    r_mrs[r_k].update({'coref': (c_i, False)})
                            elif not (l_mrs[l_k]['predicate'] == 'pronoun_q' or l_mrs[l_k]['predicate'] in self.mrs_ops['univ'].union(self.mrs_ops['neg_exist'])):
                                c_i = str(int(str(self.dt.now()).split(' ')[1].replace(':', '').replace('.', '')) + 500)  # +500 ensures no collision w/ "real" coref
                                l_mrs[l_k].update({'coref': (c_i + self.index, True)})
                                r_mrs[r_k].update({'coref': (c_i + self.index, False)})
                    else:
                        raise NotImplementedError
                else:
                    mrs = mrs[:i] + mrs[i + 1:]
                    i -= 1
                    len_mrs -= 1

            i += 1

        return [self.compound_res(mrs)] if no_conj else (self.and_or_res(l_mrs, qeq_dict) + self.and_or_res(r_mrs, qeq_dict))

    def compound_res(self, mrs):
        chains, ne_dict, nmlz_dict = [], {}, {}

        for n in range(len(mrs)):
            m = mrs[n]
            p = m['predicate']

            if p == 'compound':
                ins = False
                m_tuple = (m['label'], m['arguments']['ARG1'], m['arguments']['ARG2'])

                for i in range(len(chains)):
                    if chains[i][0][1] == m_tuple[2]:
                        chains[i] = [m_tuple] + chains[i]
                        ins = True
                        break
                    elif chains[i][len(chains[i]) - 1][2] == m_tuple[1]:
                        chains[i].append(m_tuple)
                        ins = True
                        break

                if not ins:
                    chains.append([m_tuple])
            elif p in self.mrs_ops['named']:
                ne_dict.update({m['arguments']['ARG0']: (m['arguments']['CARG'], n)})
            elif p == 'nominalization':
                ne_dict.update({m['arguments']['ARG0']: ('', -1)})
                nmlz_dict.update({m['arguments']['ARG1']: m['arguments']['ARG0']})
            elif not (is_type(p, 'q') or is_type(p, 'p')):  # ...) and p[0] == '_'
                unary, var = False, ''

                for k in m['arguments'].keys():
                    if re.search(r'^x\d+', m['arguments'][k]):
                        if unary:
                            unary = False
                            break
                        else:
                            unary = True
                            var = m['arguments'][k]

                if unary and (is_type(p, 'n') or var not in ne_dict.keys()):
                    ne_dict.update({var: (p, n)})

        if len(chains) == 0:
            return mrs

        chain_vars, top_chain_vars, unused_chain_vars = {}, set(), {}
        top_used_chains, bottom_used_chains, new_chains = set(), set(), []

        for c in chains:
            if c[0][1] in top_used_chains:
                top = c[0][1]
                unused_chain_vars.update({c[0][2]: top})

                for t in c[1:]:
                    unused_chain_vars.update({t[1]: top, t[2]: top})
            elif c[-1][2] not in bottom_used_chains:
                top = c[0][1]
                top_chain_vars.add(top)
                chain_vars.update({c[0][2]: top})
                top_used_chains.add(c[0][1])
                bottom_used_chains.add(c[-1][2])
                new_chains.append(c)

                for t in c[1:]:
                    chain_vars.update({t[1]: top, t[2]: top})

        chain_handles = {c[0][0]: c for c in new_chains}
        ne_dict = {k: ne_dict[k] for k in ne_dict.keys() if k in chain_vars.keys() or k in top_chain_vars}
        chain_preds = {ne_dict[k][1] for k in ne_dict.keys() if k in chain_vars.keys() or k in top_chain_vars}
        ne_dict = {k: ne_dict[k][0] for k in ne_dict.keys()}
        chain_indices, chain_quants, new_mrs = {}, [], []

        for i in range(len(mrs)):
            m = mrs[i]

            if m['predicate'] == 'compound':
                if m['label'] in chain_handles.keys():
                    chain_indices.update({chain_handles[m['label']][0][1]: len(new_mrs)})
                    new_mrs.append({'label': m['label']})
            elif m['label'] in nmlz_dict.keys() and is_type(m['predicate'], 'v'):
                var_name = nmlz_dict[m['label']]

                try:
                    new_arg = {next(k for k in m['arguments'].keys() if k[0] == 'A' and m['arguments'][k][0] in {'x', 'u', 'i', 'p', 'h'}): var_name}
                except StopIteration:
                    new_arg = {}

                for k, a in m['arguments'].items():
                    if a == var_name:
                        new_arg.clear()
                        new_arg.update({k: var_name})

                if len(new_arg) == 1 and var_name in chain_vars.keys():
                    new_arg.update({list(new_arg.keys())[0]: chain_vars[var_name]})
                    new_mrs.append({
                        'label': m['label'],
                        'predicate': m['predicate'],
                        'arguments': {**m['arguments'], **new_arg}
                    })
                else:
                    new_mrs.append(m)
            elif is_type(m['predicate'], 'q'):
                if m['arguments']['ARG0'] in top_chain_vars:
                    chain_quants.append((m['arguments']['ARG0'], m['predicate'] in self.mrs_ops['proper']))
                    new_mrs.append(m)
                elif not ('ARG0' in m['arguments'].keys() and m['arguments']['ARG0'] in chain_vars.keys()):
                    new_mrs.append(m)
            elif not (m['predicate'] == 'nominalization' or i in chain_preds):
                new_args = {}

                for k, a in m['arguments'].items():
                    if a in chain_vars.keys():
                        new_args.update({k: chain_vars[a]})
                    elif a in unused_chain_vars.keys():
                        new_args.update({k: unused_chain_vars[a]})

                m.update({'arguments': {**m['arguments'], **new_args}})
                new_mrs.append(m)

        for bvar, is_proper in chain_quants:
            mrs_i = chain_indices[bvar]

            if is_proper:
                new_mrs[mrs_i].update({
                    'predicate': 'named',
                    'arguments': {
                        'CARG': chain_label_rec(ne_dict, chain_handles[new_mrs[mrs_i]['label']], ''),
                        'ARG0': bvar
                    }
                })
            else:
                new_mrs[mrs_i].update({
                    'predicate': chain_label_rec(ne_dict, chain_handles[new_mrs[mrs_i]['label']], ''),
                    'arguments': {'ARG0': bvar}
                })

        return new_mrs

    def mrs_to_pmrs(self, mrs, qeq_dict, coref_eq, fa_index):
        entities, preds = {}, {}
        quants, neg = [], []
        _not_x_deg, _not_h_deg = [], set()
        be_ent, be_quant, be_handles = set(), set(), {}
        pmrs = ps.PMRS()
        proper_q, named = set(), []
        event_dict, neg_events = {}, []
        modals = {}
        all_coref, coref_eq = {}, coref_eq
        subtype_ignore, as_ignore, as_probation, prep_ignore = set(), set(), set(), set()
        mrs_i, len_mrs = 0, len(mrs)

        while mrs_i < len_mrs:
            m = mrs[mrs_i]
            p = m['predicate'] if 'predicate' in m.keys() else 'INVALID'

            if p == 'loc_nonsp' and not len([k for k in m['arguments'].keys() if not m['arguments'][k][0] == 'e']) == 2:
                p = 'INVALID'
            elif p == '_have_v_prd':
                mrs[mrs_i].update({'predicate': '_have_v_1'})
                mrs[mrs_i]['arguments'].pop('ARG3')
                m = mrs[mrs_i]
                p = m['predicate'] if 'predicate' in m.keys() else 'INVALID'
            elif p in {'card', 'ord', 'minute', 'numbered_hour', 'timezone_p'}:
                try:
                    new_arg = next(k for k in m['arguments'].keys() if m['arguments'][k][0] == 'x' and not k == 'CARG')
                    m.update({
                        'arguments': {
                            'CARG': m['arguments']['CARG'].replace(',', '') + '_' + p,
                            'ARG0': m['arguments'][new_arg]
                        }
                    })
                except StopIteration:
                    p = 'INVALID'
            elif p == 'appos':
                p = '_be_v_id'
            elif p in self.mofy_dofw.keys():
                m['arguments'].update({'CARG': self.mofy_dofw[p][m['arguments']['CARG']]})
                var_name = m['arguments']['ARG0']

                if var_name in be_ent:
                    proper_q.add(entities[var_name].name)
                else:
                    proper_q.add(var_name)

                    if var_name not in entities.keys():
                        entities.update({var_name: ps.Entity(name=var_name)})
            elif p == 'poss':
                x_args = [k for k in m['arguments'].keys() if not m['arguments'][k][0] == 'e']

                if len(x_args) == 2:
                    x_args.sort()
                    m.update({'arguments': {'ARG0': m['arguments'][x_args[1]], 'ARG1': m['arguments'][x_args[0]]}})
                    p = 'have'
                else:
                    p = 'INVALID'
            elif p == '_not+well+off_a_1':
                if 'ARG1' in m['arguments'].keys() and m['arguments']['ARG1'][0] == 'x':
                    p, arg1 = 'neg', m['arguments']['ARG1']
                    m.update({'ARG1': m['label']})
                    new_ep = {
                        'label': m['label'],
                        'predicate': 'well+off_a_1',
                        'arguments': {'ARG0': arg1}
                    }
                    mrs = mrs[:mrs_i + 1] + [new_ep] + mrs[mrs_i + 1:]
                else:
                    p = 'INVALID'
            elif p == 'id':
                p = '_id'

            if p not in self.mrs_ops['ignore']:
                if p in self.mrs_ops['subtype'] and mrs_i not in subtype_ignore:
                    arg_keys = [k for k in m['arguments'].keys() if m['arguments'][k][0] in {'x', 'i', 'u'}]
                    arg_keys.sort()

                    if len(arg_keys) == 2:
                        mrs[mrs_i].update({
                            'predicate': '_be_v_id',
                            'arguments': {
                                'ARG1': m['arguments'][arg_keys[0]],
                                'ARG2': m['arguments'][arg_keys[1]]
                            }
                        })
                    else:
                        subtype_ignore.add(mrs_i)

                    mrs_i -= 1
                elif p in self.mrs_ops['as'] and p + ' ' + m['label'] not in as_ignore:
                    arg_keys_e = [k for k in m['arguments'].keys() if m['arguments'][k][0] == 'e']
                    arg_keys_x = [k for k in m['arguments'].keys() if m['arguments'][k][0] in {'x', 'i', 'u'}]
                    arg_keys_e.sort()
                    arg_keys_x.sort()

                    if len(arg_keys_e) > 1 and len(arg_keys_x) > 0:
                        arg_e, arg_2 = m['arguments'][arg_keys_e[1]], m['arguments'][arg_keys_x[0]]

                        if arg_e in event_dict.keys():
                            arg_1, found = '', False

                            for pr_h in event_dict[arg_e]:
                                if pr_h in preds.keys():
                                    for pr in preds[pr_h]:
                                        for a in pr.args:
                                            if re.search(r'^x\d+', a.name):
                                                found, arg_1 = True, a.name
                                                break

                                        if found:
                                            break

                                if found:
                                    break

                            if not found:
                                arg_1 = preds[list(event_dict[arg_e])[0]][0].args[0].name

                            mrs[mrs_i].update({'predicate': '_be_v_id', 'arguments': {'ARG1': arg_1, 'ARG2': arg_2}})
                            mrs_i -= 1
                        elif mrs_i < len_mrs - 1:
                            if p + ' ' + m['label'] in as_probation:
                                as_ignore.add(p + ' ' + m['label'])
                            else:
                                mrs = mrs[:mrs_i] + mrs[mrs_i + 1:] + [m]
                                mrs_i -= 1
                                as_probation.add(p + ' ' + m['label'])
                    elif len(arg_keys_x) > 2:
                        as_ignore.add(p + ' ' + m['label'])
                        mrs_i -= 1
                elif is_type(p, 'p'):
                    if len([k for k in m['arguments'].keys() if not m['arguments'][k][0] == 'e']) > 1:
                        mrs[mrs_i].update({'predicate': mrs[mrs_i]['predicate'].replace('_p', '')})
                        mrs_i -= 1
                    elif p + ' ' + m['label'] in prep_ignore:
                        args = m['arguments']
                        arg_keys = list(args.keys())
                        arg_keys.sort()

                        if len(arg_keys) > 2 and args[arg_keys[0]][0] == 'e' and args[arg_keys[1]][0] == 'e' and \
                                args[arg_keys[2]][0] in {'x', 'i', 'p', 'h', 'u'}:
                            arg_e, arg_x, found = args[arg_keys[1]], args[arg_keys[2]], False

                            if arg_e in event_dict.keys():
                                for pr_h in event_dict[args[arg_keys[1]]]:
                                    if pr_h in preds.keys():
                                        for pr in preds[pr_h]:
                                            if len(pr.args) == 1 and re.search(r'^x\d+', pr.args[0].name):
                                                arg_e, found = pr.args[0].name, True
                                                break
                                            elif not arg_e[0] == 'x':
                                                new_arg = [x.name for x in pr.args if x.name[0] == 'x']
                                                arg_e = new_arg[0] if new_arg else pr.args[0].name

                                    if found:
                                        break

                            if arg_e[0] == 'e':
                                mrs = mrs[:mrs_i] + mrs[mrs_i + 1:]
                                len_mrs -= 1
                            else:
                                mrs[mrs_i]['arguments'].update({arg_keys[1]: arg_e, arg_keys[2]: arg_x})
                        else:
                            mrs = mrs[:mrs_i] + mrs[mrs_i + 1:]
                            len_mrs -= 1

                        mrs_i -= 1
                    else:
                        prep_ignore.add(p + ' ' + m['label'])
                        mrs = mrs[:mrs_i] + mrs[mrs_i + 1:] + [m]
                        mrs_i -= 1
                elif p in self.mrs_ops['named']:
                    if m['arguments']['ARG0'][0] == 'x':
                        named.append(mrs_i)
                elif p[-8:] == '_v_modal':
                    for k in m['arguments'].keys():
                        if m['arguments'][k][0] == 'h':
                            modals.update({m['label']: m['arguments'][k]})
                            break
                elif is_type(p, 'q'):
                    if 'ARG0' in m['arguments'].keys() and m['arguments']['ARG0'][0] == 'x':
                        bvar = m['arguments']['ARG0']

                        if 'coref' in m.keys() and m['coref'][1] and bvar in be_ent:  # bvar is main referent
                            ent = entities[bvar]
                            c_i, _ = m['coref']

                            if ent.binder and not (ent.binder.coref is None or ent.binder.kind == 'p'):  # ent.binder is main referent
                                coref_eq.update({m['coref'][0]: ent.binder.coref})
                            elif ent.coref and ent.coref[1]:  # ent is main referent
                                coref_eq.update({m['coref'][0]: ent.coref[0]})
                            else:  # ent is not main referent
                                if ent.binder:
                                    if p in self.mrs_ops['univ']:
                                        ent.binder.kind = 'u'
                                    elif p in self.mrs_ops['exist']:
                                        ent.binder.kind = 'e'
                                    elif p in self.mrs_ops['neg_exist']:
                                        ent.binder.kind, ent.binder.pol = 'u', False
                                    elif p in self.mrs_ops['remove_q']:
                                        ent.binder.kind = 'r'
                                    else:
                                        if p not in self.mrs_ops['proper']:
                                            print(p)

                                        raise NotImplementedError

                                    ent.binder.coref = m['coref'][0]
                                else:
                                    ent.coref = m['coref']

                        if p in self.mrs_ops['proper']:
                            if bvar in be_ent:
                                proper_q.add(entities[bvar].name)
                            else:
                                proper_q.add(bvar)

                                if bvar not in entities.keys():
                                    entities.update({bvar: ps.Entity(name=bvar)})

                            if 'coref' in m.keys():
                                entities[bvar].coref = m['coref']
                        else:
                            kind, pol = '', True
                            coref, coref_inst = None, False

                            if p in self.mrs_ops['univ']:
                                kind = 'u'
                            elif p in self.mrs_ops['exist']:
                                kind = 'e'
                            elif p in self.mrs_ops['neg_exist']:
                                kind, pol = 'u', False
                            elif p in self.mrs_ops['remove_q']:
                                kind = 'r'
                            else:
                                print(p)
                                raise NotImplementedError

                            if 'coref' in m.keys():
                                coref, coref_inst = m['coref']
                                coref_inst = not coref_inst
                            elif p == 'pronoun_q':
                                coref, coref_inst = 0, True  # -1, True

                            if not (coref is None or coref_inst):
                                all_coref.update({coref: kind})

                            if bvar not in be_ent:
                                if bvar in entities.keys():
                                    if entities[bvar].coref:  # already encountered 'bvar is entities[bvar]'
                                        c_i, is_main = entities[bvar].coref

                                        if 'coref' in m.keys():
                                            if m['coref'][0] == c_i:
                                                m.update({'coref': (m['coref'][0], m['coref'][1] or is_main)})
                                            elif is_main and m['coref'][1]:
                                                coref_eq.update({c_i: m['coref'][0]})
                                        elif is_main:
                                            m.update({'coref': (c_i, True)})

                                    entities[bvar].coref = None
                                else:
                                    entities.update({bvar: ps.Entity(name=bvar)})

                                q = ps.Quant(bvar=entities[bvar])

                                if coref_inst:
                                    q.kind = 'p'  # "pronoun"
                                else:
                                    q.kind, q.pol = kind, pol

                                q.coref = coref
                                entities[bvar].binder = q
                                quants.append((m['label'], m['arguments']['RSTR'], q))
                elif p in self.mrs_ops['neg']:
                    neg.append(m['arguments']['ARG1'])
                elif p in self.mrs_ops['neg_xh']:
                    h_type = True

                    for arg_n in m['arguments'].keys():
                        if m['arguments'][arg_n][0] == 'x' and not arg_n == 'CARG':
                            arg = m['arguments'][arg_n]

                            if arg not in entities.keys():
                                entities.update({arg: ps.Entity(name=arg)})

                            _not_x_deg.append(entities[arg])
                            h_type = False
                            break

                    if h_type:
                        _not_h_deg.add(m['label'])
                elif p in self.mrs_ops['neg_e']:
                    if 'ARG1' in m['arguments'].keys():
                        neg_events.append(m['arguments']['ARG1'])
                elif is_type(p, 'id'):
                    arg1 = m['arguments']['ARG1']
                    arg2 = m['arguments']['ARG2']

                    if arg1[0] == 'x' and arg2[0] == 'x' and not \
                            (arg1 == arg2 or (arg1 in entities.keys() and arg2 in entities.keys() and entities[arg1] == entities[arg2])):
                        if arg1 not in entities.keys():
                            entities.update({arg1: ps.Entity(name=arg1)})

                        if arg2 in entities.keys():
                            if arg2 in proper_q:
                                proper_q.add(arg1)
                            elif entities[arg2].binder:
                                be_quant.add(entities[arg2].binder)
                            else:
                                be_ent.add(arg2)

                            for pr in entities[arg2].predicates:
                                entities[arg1].predicates.append(pr)

                                for i in range(len(pr.args)):
                                    if pr.args[i] == entities[arg2]:
                                        pr.args[i] = entities[arg1]
                        else:
                            be_ent.add(arg2)

                        entities.update({arg2: entities[arg1]})
                        be_handles.update({m['label']: (len(pmrs.preds), entities[arg1])})
                else:
                    ep = ps.EP(head=p)
                    arg_keys = list(m['arguments'].keys())
                    arg_keys.sort()
                    x_valid = False
                    events = []

                    for k in arg_keys:
                        arg_k = m['arguments'][k]

                        if arg_k[0] in {'u', 'i', 'x', 'p', 'h'}:
                            x_valid = True

                            if arg_k[0] in {'u', 'p', 'h'}:
                                arg_k = 'i' + str(int(str(self.dt.now()).split(' ')[1].replace(':', '').replace('.', '')) + 50)

                            if arg_k not in entities.keys():
                                entities.update({arg_k: ps.Entity(name=arg_k)})

                            ent = entities[arg_k]
                            ent.predicates.append(ep)
                            ep.args.append(ent)
                        elif arg_k[0] == 'e':
                            events.append(arg_k)

                    if x_valid:
                        if m['label'] in preds.keys():
                            preds[m['label']].append(ep)
                        else:
                            preds.update({m['label']: [ep]})

                        if p in {'_without', 'without'}:
                            ep.head, ep.pol = 'with', False

                        pmrs.preds.append(ep)

                        for e in events:
                            if e in event_dict.keys():
                                event_dict[e].add(m['label'])
                            else:
                                event_dict.update({e: {m['label']}})

            mrs_i += 1

        for e_k in entities.keys():
            if not e_k[0] == 'x':
                q = ps.Quant(bvar=entities[e_k], kind='e_pass')
                entities[e_k].binder = q
                quants.append(('NA', 'NA', q))

        neg_event_to_handle = set()

        for n in neg_events:
            if n in event_dict.keys():
                neg_event_to_handle = neg_event_to_handle.union(event_dict[n])

        neg += list(neg_event_to_handle)

        for i in named:
            m = mrs[i]

            if entities[m['arguments']['ARG0']].name in proper_q:
                ent = entities[m['arguments']['ARG0']]
                ent.name = m['arguments']['CARG'].lower()

                if ent.coref and not ent.coref[1]:
                    q = ps.Quant(bvar=ent, kind='p')
                    ent.binder, q.coref = q, ent.coref[0]
                    ent.coref = None
                    quants.append(('NA', 'NA', q))
                else:
                    proper_q.add(m['arguments']['ARG0'])
            else:
                arg0 = entities[m['arguments']['ARG0']]
                ep = ps.EP(head=m['arguments']['CARG'].lower(), args=[arg0])
                arg0.predicates.append(ep)
                pmrs.preds.append(ep)

                if arg0.binder:
                    arg0.binder.rstr.append(ep)

                if m['label'] in preds.keys():
                    preds[m['label']].append(ep)
                else:
                    preds.update({m['label']: [ep]})

        for i in range(len(neg)):
            n, pr = neg[i], None

            if n in modals.keys():
                n = modals[n]
            elif n in qeq_dict.keys() and qeq_dict[n] in modals.keys():
                n = modals[qeq_dict[n]]

            if n in preds.keys():
                pr = preds[n]
            elif n in qeq_dict.keys() and qeq_dict[n] in preds.keys():
                pr = preds[qeq_dict[n]]
            else:
                if n in qeq_dict.keys() and qeq_dict[n] in be_handles.keys():
                    n = qeq_dict[n]

                if n in be_handles.keys():
                    ind, e = be_handles[n]

                    for p in pmrs.preds[ind:]:
                        if e in p.args:
                            p.pol = not p.pol

            if pr is not None:
                for p in pr:
                    p.pol = not p.pol

        for n in _not_x_deg:
            if n.binder:
                if n.binder.kind == 'u':
                    n.binder.kind = 'e'
                elif n.binder.kind == 'e':
                    n.binder.kind = 'u'

                n.binder.pol = not n.binder.pol
            else:
                for pr in n.predicates:
                    pr.pol = not pr.pol

        for q_h, r_h, q in quants:
            if not (q in be_quant or q.bvar.name in proper_q):
                if r_h in preds.keys():
                    q.rstr += preds[r_h]
                elif r_h in qeq_dict.keys() and qeq_dict[r_h] in preds.keys():
                    q.rstr += preds[qeq_dict[r_h]]

                if not (q.kind == 'u' and len(q.rstr) == 0):
                    q.scope = [p for p in q.bvar.predicates if p not in q.rstr and p in pmrs.preds]

                    if len(q.scope) > 0:
                        if q_h in _not_h_deg:
                            if q.kind == 'u':
                                q.kind = 'e'
                            elif q.kind == 'e':
                                q.kind = 'u'

                            q.pol = not q.pol

                        if not q.pol:
                            for p in q.scope:
                                p.pol = not p.pol

                        pmrs.quants.append(q)
                    elif len(q.rstr) > 0 and not (q.kind == 'u' or q_h in _not_h_deg):
                        pmrs.quants.append(q)

        conn, out = ps.ConnPMRS(), []

        for x in conn.get_connected_components(pmrs):
            legal = True

            if len(x.quants) == 0:
                illegal = set()

                for i in range(len(x.preds)):
                    for a in x.preds[i].args:
                        if re.search(r'^[xuiph]\d+', a.name):
                            illegal.add(i)
                            break

                x.preds = [x.preds[i] for i in range(len(x.preds)) if i not in illegal]
            else:
                for p in x.preds:
                    for a in p.args:
                        if re.search(r'^[xuiph]\d+', a.name) and a.binder not in x.quants:
                            legal = False
                            break

                    if not legal:
                        break

                if legal:
                    if x.quants[0].kind == 'r':
                        legal = False
                    else:
                        new_quants = [x.quants[0]]

                        for q in x.quants[1:]:
                            if q.kind == 'r':
                                legal = False
                                break

                            if q.leq(new_quants[-1]):
                                new_quants.append(q)
                            elif new_quants[0].leq(q) or q.kind == 'u':
                                new_quants = [q] + new_quants
                            else:
                                new_quants.append(q)

                        x.quants = new_quants

            if legal and not len(x.preds) == 0:
                x.preds.sort()
                x.fa_index = fa_index
                out.append(x)

                for p in x.preds:
                    p.head = self.clean_str(p.head, len(p.args))

                    for a in p.args:
                        a.name = self.clean_str(a.name, -1)

        return out, all_coref, coref_eq

    def clean_str(self, name, len_args):
        if len_args == -1 and re.search(r'^[xi]\d+', name):
            return name

        name_list_temp, name_list = name.split('-'), []

        for i in range(len(name_list_temp)):
            if '/' in name_list_temp[i]:
                new_name_list = name_list_temp[i].split('/')

                if len(new_name_list) == 2:
                    if new_name_list[1][-8:] == '_unknown':
                        new_name_list[1] = new_name_list[1][:-8]

                    name_list_temp[i] = new_name_list[0] + '-' + new_name_list[1]

            name_list += name_list_temp[i].split('/')[0].replace('_', '-').replace('+', '-').replace('.', '-').split('-')

        i = 0

        while i < len(name_list):
            if len(name_list[i]) == 0:
                name_list = name_list[:i] + name_list[i + 1:]

            i += 1

        if len(name_list) == 0:
            new_name = self.lmtzr.lemmatize(name)

            return (new_name + '_' + str(len_args)) if len_args > 0 else new_name
        elif len(name_list) == 1:
            new_name = self.lmtzr.lemmatize(name_list[0])

            return (new_name + '_' + str(len_args)) if len_args > 0 else new_name

        out = ''

        for i in range(len(name_list)):
            if name_list[i].isalnum() and name_list[i] not in {'n', 'v', 'a', 'c', 'x', 'unspec', 'nn', 'jj', 'vb', 'u'}:
                if i < len(name_list) - 1 and name_list[i + 1] in self.tb_to_wn.keys():
                    out += self.lmtzr.lemmatize(name_list[i], pos=self.tb_to_wn[name_list[i + 1]]) + '-'
                else:
                    out += self.lmtzr.lemmatize(name_list[i]) + '-'

        while out[-1] == '-':
            out = out[:-1]

        return out + (('_' + str(len_args)) if len_args > 0 else '')

    def update_doc_dict(self, pmrs):
        w = pmrs.weight

        for p in pmrs.preds:
            if p.head in self.doc_dict.keys():
                pri = self.doc_dict[p.head].create_instance(p, w)
            else:
                pred = ps.Predicate()
                pri = pred.create_instance(p, w)
                self.doc_dict.update({p.head: pred})

            for a in p.args:
                if a.name in self.doc_dict['SYMBOLS'].keys():
                    self.doc_dict['SYMBOLS'][a.name].add((p.head, pri))
                else:
                    self.doc_dict['SYMBOLS'].update({a.name: {(p.head, pri)}})

    def check_coref(self):
        unreachable_coref = []

        while not len(self.pro_pmrs) == 0:
            pro_temp = copy.deepcopy(self.pro_pmrs)
            self.pro_pmrs.clear()

            for p in pro_temp:
                unreachable = True

                if p.quants[0].coref in self.coref_data['CLUSTERS'].keys():
                    coreferent = self.coref_data['CLUSTERS'][p.quants[0].coref]
                    main_ref = coreferent.check_main(p.var_history)

                    if main_ref is not None:
                        p.quants[0].bvar.name, p.quants[0].bvar.binder = main_ref, None
                        p.quants, unreachable = p.quants[1:], False
                elif p.quants[0].coref not in self.coref_data['GOOD']:
                    p.quants[0].kind = self.coref_data['TYPE'][p.quants[0].coref] if p.quants[0].coref in self.coref_data['TYPE'].keys() else 'e'
                    self.coref_data['GOOD'].add(p.quants[0].coref)
                    unreachable = False

                if unreachable:
                    unreachable_coref.append(p)
                else:
                    if len(p.quants) == 0:
                        self.nq_pmrs.append(p)
                    elif p.quants[0].kind == 'u':
                        self.u_pmrs.insert_sorted(p)
                    elif p.quants[0].kind == 'p':
                        self.pro_pmrs.append(p)
                    else:
                        self.e_pmrs.append(p)

        return unreachable_coref

    def res_TLU(self, pmrs, u_pmrs_data):
        pmrs_copy = copy.deepcopy(pmrs)
        pmrs_rstr = pmrs_copy.pure_TL_rstr()
        sym, rstr_sat = None, True

        for p in pmrs_rstr.preds:
            if p.head in self.doc_dict.keys():
                p_obj = self.doc_dict[p.head]

                for i in range(len(p.args)):
                    if p.args[i].binder == pmrs_copy.quants[0]:
                        if sym is None:
                            sym = p_obj.args[i]
                        else:
                            sym = sym.intersection(p_obj.args[i])
            else:
                rstr_sat = False
                break

        if rstr_sat and sym is not None:
            rstr_sat, sym = False, sym - {'EX_PASS'}

            for k in sym:
                pmrs_k = copy.deepcopy(pmrs)
                pmrs_k.quants[0].bvar.name = k
                pmrs_k.quants[0].bvar.binder = None
                pmrs_k_rstr, pmrs_k_scope = pmrs_k.pure_TL_rstr(scope=True)
                pmrs_k_rstr.var_history.append(k)
                pmrs_k_scope.var_history.append(k)
                w_k = self.eval_pmrs(pmrs_k_rstr)

                if w_k == -1:  # waiting for coreferent
                    rstr_sat = True

                    yield pmrs, True
                elif not (w_k is None or w_k == 0):
                    rstr_sat = True
                    pmrs_k_scope.weight = pmrs_k_scope.weight * w_k

                    yield pmrs_k_scope, True

        if not rstr_sat:
            pmrs.quants[0].kind = 'e'

            yield pmrs, u_pmrs_data[pmrs_copy.TL_scope_rstr_as_str()[0]]

    def eval_pmrs(self, pmrs):
        if len(pmrs.quants) == 0:
            min_val = None

            for p in pmrs.preds:
                val = self.eval_EP(p)

                if val is None:
                    return None

                if not p.pol:
                    val = 1 - val

                if min_val is None:
                    min_val = val
                elif val < min_val:
                    min_val = val

            return min_val

        if pmrs.quants[0].kind == 'p':
            if pmrs.quants[0].coref in self.coref_data['CLUSTERS'].keys():
                coreferent = self.coref_data['CLUSTERS'][pmrs.quants[0].coref]
                main_ref = coreferent.check_main(pmrs.var_history)

                if main_ref is not None:
                    e = pmrs.quants[0].bvar
                    e.name, e.binder = main_ref, None
                    pmrs.quants = pmrs.quants[1:]

                    return self.eval_pmrs(pmrs)

                return -1
            elif pmrs.quants[0].coref in self.coref_data['GOOD']:
                return -1
            else:
                if pmrs.quants[0].coref in self.coref_data['TYPE'].keys():
                    pmrs.quants[0].kind = self.coref_data['TYPE'][pmrs.quants[0].coref]
                    self.coref_data['GOOD'].add(pmrs.quants[0].coref)

                    return -1
                else:
                    pmrs.quants[0].kind, pmrs.quants[0].coref = 'e', None

                    return self.eval_pmrs(pmrs)
        elif pmrs.quants[0].kind == 'u':
            pmrs_copy = copy.deepcopy(pmrs)
            _, pmrs_scope = pmrs_copy.pure_TL_rstr(scope=True)
            sym, val, scope_sat = None, None, True

            for p in pmrs_scope.preds:
                if p.head in self.doc_dict.keys():
                    p_obj = self.doc_dict[p.head]

                    for i in range(len(p.args)):
                        if p.args[i].binder == pmrs_copy.quants[0]:
                            if sym is None:
                                sym = p_obj.args[i]
                            else:
                                sym = sym.intersection(p_obj.args[i])
                else:
                    scope_sat = False
                    break

            if scope_sat and sym:
                for k in sym:
                    pmrs_k = copy.deepcopy(pmrs)
                    pmrs_k.quants[0].bvar.name = k
                    pmrs_k.quants[0].bvar.binder = None
                    pmrs_k_rstr, pmrs_k_scope = pmrs_k.pure_TL_rstr(scope=True)
                    rstr_val = self.eval_pmrs(pmrs_k_rstr)

                    if rstr_val is not None:
                        scope_val = self.eval_pmrs(pmrs_k_scope)

                        if rstr_val == -1 or scope_val == -1:
                            return -1

                        if scope_val is not None:
                            k_val = 1 - min(rstr_val, 1 - scope_val)

                            if val is None or k_val < val:
                                val = k_val

            return val
        elif pmrs.quants[0].kind == 'e_pass':
            pmrs.quants[0].kind = 'e'

            return self.eval_pmrs(pmrs)
        else:  # existential
            max_ent, max_pmrs, val, sym, vscope_sat = None, None, None, None, True
            coref_id = pmrs.quants[0].coref

            for p in pmrs.preds:
                if p.head in self.doc_dict.keys():
                    p_obj = self.doc_dict[p.head]

                    for i in range(len(p.args)):
                        if p.args[i].binder == pmrs.quants[0]:
                            if sym is None:
                                sym = p_obj.args[i]
                            else:
                                sym = sym.intersection(p_obj.args[i])
                else:
                    vscope_sat = False
                    break

            if vscope_sat and sym:
                for k in sym:
                    pmrs_k = copy.deepcopy(pmrs)
                    pmrs_k.quants[0].bvar.name = k
                    pmrs_k.quants[0].bvar.binder = None
                    pmrs_k.quants = pmrs_k.quants[1:]
                    k_val = self.eval_pmrs(pmrs_k)

                    if k_val is not None:
                        if val is None or val < k_val:
                            val, max_pmrs, max_ent = k_val, pmrs_k, k

                if not (coref_id is None or max_pmrs is None):
                    if coref_id not in self.coref_data['CLUSTERS'].keys():
                        self.coref_data['CLUSTERS'].update({coref_id: ps.CorefCluster()})

                    self.coref_data['CLUSTERS'][coref_id].update_main(max_pmrs.var_history, max_ent, True)

            return val

    def eval_EP(self, ep):
        if ep.head in self.doc_dict.keys():
            return self.doc_dict[ep.head].check_val(ep)

        return None

    def clean_doc_dict(self):
        new_doc_dict = {}

        for k in self.doc_dict.keys():
            pr = ps.Predicate()

            if not k == 'SYMBOLS':
                for args in self.doc_dict[k].inst_dict.keys():
                    for a in list(args):
                        if (not re.match(r'^ex_\d+_\d+$', a) or a == 'EX_PASS') or (a in self.doc_dict['SYMBOLS'].keys() and len(self.doc_dict['SYMBOLS'][a]) > 1):
                            pr.inst_dict.update({args: self.doc_dict[k].inst_dict[args]})
                            break

            if len(pr.inst_dict) > 0:
                new_doc_dict.update({k: pr})

        return new_doc_dict


def is_type(pred, t):
    return pred[-(len(t) + 1):] == '_' + t or '_' + t + '_' in pred


def chain_label_rec(ne, chain, name):
    if len(chain) == 1:
        l = [ne[chain[0][i]] if chain[0][i] in ne.keys() else '*unk*' for i in [1, 2]]
        out = (l[1] + '-' + l[0] + '-' + name)[:-1].lower()

        return out[1:] if out[0] == '-' else out
    else:
        return chain_label_rec(ne, chain[1:], (ne[chain[0][1]] if chain[0][1] in ne.keys() else '*unk*') + '-' + name)
