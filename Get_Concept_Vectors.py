
import json
import pickle
from tqdm import tqdm


class LLNode:
    def __init__(self, id_, val):
        self.id, self.value = id_, val
        self.next = None


class LinkedList:
    def __init__(self):
        self.start, self.end, self.length = None, None, 0
        self.nodes = {}

    def insert_sorted(self, n):
        if n.id in self.nodes.keys():
            m = self.nodes[n.id]
            m.value[0] += n.value[0]
            m.value[1] += n.value[1]
        else:
            self.nodes.update({n.id: n})

            if self.start is None:
                self.start = n
                self.end = n
            elif n.id < self.start.id:
                n.next = self.start
                self.start = n
            elif n.id > self.end.id:
                self.end.next = n
                self.end = n
            else:
                m = self.start

                while m.next.id < n.id:
                    m = m.next

                n.next = m.next
                m.next = n

    def to_json(self):
        out, n = [], self.start

        while n:
            out.append([n.id, n.value[0], n.value[1]])
            n = n.next

        return {'list': out, 'len': len(out)}

    def from_json(self, json_file):
        json_list, self.length = json_file['list'], json_file['len']

        if len(json_list) > 0:
            self.start = LLNode(json_list[0][0], json_list[0][1:])
            n = self.start

            for jl in json_list[1:]:
                if not jl[1] + jl[2] == 0:
                    n.next = LLNode(jl[0], jl[1:])
                    n = n.next

            self.end = n


def atomic_decomposition(item, main_e):
    pred, args = item[0], item[1:]
    out, ind_list_master = [], set(range(len(args)))

    for i in range(len(args)):
        if args[i] == main_e:
            ind_list = ind_list_master - {i}
            ps_list = powerset(ind_list)

            for j in ps_list:
                out_str, no_ex_pass = '(', True

                for k in range(len(args)):
                    if k == i:
                        out_str += '#,'
                    elif k in j:
                        out_str += '_,'
                    elif args[k] == 'EX_PASS':
                        no_ex_pass = False
                        break
                    else:
                        out_str += args[k] + ','

                if no_ex_pass:
                    out.append((pred + out_str[:len(out_str) - 1] + ')', args[i]))

                    if not j == ind_list:
                        out.append(('_' + out_str[:len(out_str) - 1] + ')', args[i]))

    return out


def powerset(a):
    s = list(a)
    x_, out = len(s), []

    for i in range(1 << x_):
        out.append({s[j] for j in range(x_) if (i & (1 << j))})

    return out


# WORD = 'leopard'
# TERMS = {'leopard-1_1', 'leopard-1-cat-1_1'}

with open('/home/mj/Desktop/McRae/concepts_features_dict.pkl', 'rb') as f:
    file = pickle.load(f)

with open('/home/mj/Desktop/McRae/concepts_mrs_equiv_copy', 'r') as f:
    readlines = f.readlines()

with open('/home/mj/Desktop/McRae_v2/analysis_all_copy.json', 'r') as f:
    analysis_dict_1 = json.load(f)

with open('/home/mj/Desktop/McRae_v2/analysis_all.json', 'r') as f:
    analysis_dict_2 = json.load(f)

for line in readlines:
    if '*' in line:
        line_split = line.replace('*', '').split('=')
        concept = line_split[0].strip()

        if analysis_dict_1[concept]['rho'] - analysis_dict_2[concept]['rho'] > 0:
            mrs_equiv = line_split[1].replace('\'', '').replace(' ', '').strip().split(',')
            file['con_feat'][concept].update({'mrs_equiv': mrs_equiv})

# with open('/home/mj/Desktop/McRae_v2/concepts_features_dict_test.pkl', 'rb') as f:
#     file = pickle.load(f)

print('loading paths...')

with open('/home/mj/Desktop/Phase2_1/paths.json') as f:
    paths = json.load(f)

# with open('/home/mj/Desktop/McRae/context_back.json', 'r') as f:
#     context_back = json.load(f)
#
# with open('/home/mj/Desktop/McRae/symbol_back.json', 'r') as f:
#     symbol_back = json.load(f)
#
# symbols = {symbol_back[i]: (i, LinkedList()) for i in range(len(symbol_back))}
# contexts = {context_back[i]: (i, LinkedList()) for i in range(len(context_back))}

print('done!')

terms, terms_inv = set(), {}

for concept in tqdm(file['con_feat'].keys()):
    terms = terms.union(set(file['con_feat'][concept]['mrs_equiv']))

    for term in file['con_feat'][concept]['mrs_equiv']:
        if term in terms_inv.keys():
            terms_inv[term].add(concept)
        else:
            terms_inv.update({term: {concept}})

# terms, terms_inv = TERMS, {term: {WORD} for term in TERMS}
entities, new_paths = {}, {}

for path in tqdm(paths):
    if path[0] in terms and len(path) == 3 and path[2][1] == 0 and (not path[1] == 'EX_PASS'):
        if path[0] in entities.keys():
            entities[path[0]].add(path[1])
        else:
            entities.update({path[0]: {path[1]}})

        new_paths.update({path[1]: []})

entities_inv = {}

for term in entities.keys():
    for e in entities[term]:
        if e in entities_inv.keys():
            entities_inv[e].add(term)
        else:
            entities_inv.update({e: {term}})

entity_set = set()
ent_to_con = {}

for term in entities.keys():
    entity_set = entity_set.union(entities[term])

for ent in entity_set:
    con_set = set()

    for term in entities_inv[ent]:
        for concept in terms_inv[term]:
            con_set.add(concept)

    ent_to_con.update({ent: list(con_set)})

for path in tqdm(paths):
    e_int = set(path[1:-1]).intersection(entity_set)

    for ent in e_int:
        new_paths[ent].append(path)

concept_vectors = {concept: LinkedList() for concept in file['con_feat'].keys()}
symbols, contexts, symbol_back, context_back = {}, {}, [], []
# concept_vectors = {WORD: LinkedList()}
lt_10_cnt = 0

for main_ent in tqdm(new_paths.keys()):
    if len(new_paths[main_ent]) < 10:  # 6
        lt_10_cnt += 1

        for path in new_paths[main_ent]:
            value, ad_p = path[-1], atomic_decomposition(path[:-1], main_ent)

            for context, symbol in ad_p:
                if context in contexts.keys():
                    context_id, _ = contexts[context]
                else:
                    context_back.append(context)
                    context_id = len(contexts)
                    contexts.update({context: (context_id, LinkedList())})

                if symbol not in symbols.keys():
                    symbol_back.append(symbol)
                    symbol_id = len(symbols)
                    symbols.update({symbol: (symbol_id, LinkedList())})

                if symbol in ent_to_con.keys():
                    for concept in ent_to_con[symbol]:
                        concept_vectors[concept].insert_sorted(LLNode(context_id, value))

print(lt_10_cnt)

max_id = 0

for c in tqdm(file['con_feat'].keys()):
    n_ = concept_vectors[c].start

    while n_:
        x, y = n_.value[0], n_.value[1]
        n_.value[0] = x / (x + y)
        n_.value[1] = ((x ** 2) + (y ** 2)) ** .5
        max_id = max(n_.id, max_id)
        n_ = n_.next

doc_freq_dict = [0.0 for _ in range(max_id + 1)]

for c in tqdm(file['con_feat'].keys()):
    c_vec = concept_vectors[c]
    n_, norm_sum = c_vec.start, 0

    while n_:
        doc_freq_dict[n_.id] += n_.value[1]
        norm_sum += n_.value[1] ** 2
        n_ = n_.next

    n_ = c_vec.start
    norm_sum = norm_sum ** .5

    while n_:
        n_.value[1] = n_.value[1] / norm_sum
        n_ = n_.next

    feat_vec = file['con_feat'][c]['ff_vector']
    fc_vec = []

    for fv_j in range(len(feat_vec)):
        if feat_vec[fv_j] == 0:
            fc_vec.append(None)
        else:
            x = feat_vec[fv_j] * 30
            y = 30 - x
            v = complex(x, y)
            fc_vec.append(v / abs(v))

    file['con_feat'][c].update({
        'cc_vector': c_vec.to_json(),
        'fc_vector': fc_vec
    })

test_vec = LinkedList()
test_vec.from_json(file['con_feat']['accordion']['cc_vector'])

print(test_vec.length)

test_list, n_ = [], test_vec.start

while n_:
    test_list.append((n_.id, n_.value))
    n_ = n_.next

print(test_list)

with open('/home/mj/Desktop/McRae_v2/concepts_features_dict_lt_10_copy.pkl', 'wb') as f:
    pickle.dump(file, f)

# with open('/home/mj/Desktop/McRae/context_back.json', 'w') as f:
#     json.dump(context_back, f)
#
# with open('/home/mj/Desktop/McRae/symbol_back.json', 'w') as f:
#     json.dump(symbol_back, f)

with open('/home/mj/Desktop/McRae_v2/context_df_lt_10_copy.json', 'w') as f:
    json.dump(doc_freq_dict, f)
