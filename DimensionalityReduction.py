
import pickle
import json
import math
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
        self.length += 1

        if self.start is None:
            self.start = n
            self.end = n
            self.nodes.update({n.id: n})
        elif n.id < self.start.id:
            n.next = self.start
            self.start = n
            self.nodes.update({n.id: n})
        elif n.id > self.end.id:
            self.end.next = n
            self.end = n
            self.nodes.update({n.id: n})
        else:
            m = self.start

            while m.id < n.id:
                m = m.next

            if m.id == n.id:
                self.length -= 1
                m.value[0] += n.value[0]
                m.value[1] += n.value[1]
            else:
                n.next = m.next
                m.next = n
                self.nodes.update({n.id: n})

    def add(self, other_list):
        n = other_list.start

        while n:
            m = LLNode(n.id, n.value)
            self.insert_sorted(m)
            n = n.next

    def from_json(self, json_file):
        json_list, self.length = json_file['list'], json_file['len']

        if len(json_list) > 0:
            self.start = LLNode(json_list[0][0], json_list[0][1:])
            self.nodes.update({json_list[0][0]: self.start})
            n = self.start

            for jl in json_list[1:]:
                if not jl[2] == 0:
                    n.next = LLNode(jl[0], jl[1:])
                    self.nodes.update({jl[0]: n.next})
                    n = n.next

            self.end = n

    def to_json(self):
        out, n = [], self.start

        while n:
            out.append([n.id, n.value[0], n.value[1]])
            n = n.next

        return {'list': out, 'len': len(out)}


def delta(c1_id, c2_id):
    c1, c2 = context_vecs[c1_id], context_vecs[c2_id]
    ovl_num, ovl_den = 0, 0
    node_int = set(c1.nodes.keys()).intersection(set(c2.nodes.keys()))

    for n_id in node_int:
        ovl_num += min(abs(c1.nodes[n_id].value), abs(c2.nodes[n_id].value))
        ovl_den += max(abs(c1.nodes[n_id].value), abs(c2.nodes[n_id].value))

    for n_id in set(c1.nodes.keys()) - node_int:
        ovl_den += abs(c1.nodes[n_id].value)

    for n_id in set(c2.nodes.keys()) - node_int:
        ovl_den += abs(c2.nodes[n_id].value)

    return 0 if ovl_den == 0 else (ovl_num / ovl_den)


K = 2000  # 375 min

with open('/home/mj/Desktop/McRae_v2/concepts_features_dict_lt_10_copy.pkl', 'rb') as f:
    cf_dict = pickle.load(f)

context_vecs, cf_keys = {}, list(cf_dict['con_feat'].keys())

print('generating context vectors...')

for i in tqdm(range(len(cf_keys))):
    cc_vec = LinkedList()
    cc_vec.from_json(cf_dict['con_feat'][cf_keys[i]]['cc_vector'])
    cc_n = cc_vec.start

    while cc_n:
        re_val = cc_n.value[0]
        im_val = 1 - re_val

        if 0 < re_val < 1:
            angle = math.atan(im_val / re_val)
            re_val = math.cos(angle)
            im_val = math.sin(angle)

        cc_n.value = complex(re_val, im_val) * cc_n.value[1]
        cc_m = LLNode(i, cc_n.value)

        if cc_n.id not in context_vecs.keys():
            context_vecs.update({cc_n.id: LinkedList()})

        context_vecs[cc_n.id].insert_sorted(cc_m)
        cc_n = cc_n.next

    cf_dict['con_feat'][cf_keys[i]].update({'cc_vector': cc_vec})

print('done!')

dim_indices, theta = [], [0 for _ in range(len(context_vecs))]
# mag_list = [0 for _ in range(len(context_vecs))]
max_con, max_val = None, 0

print('running theta-clustering...')
print('   first pass...')
print('      finding D1...')

# for context in tqdm(context_vecs.keys()):
#     total_mag, c_n = 0, context_vecs[context].start
#
#     while c_n:
#         total_mag += abs(c_n.value)
#         c_n = c_n.next
#
#     # mag_list[context] = total_mag
#
#     if total_mag > max_val:
#         max_con, max_val = context, total_mag

for context in tqdm(context_vecs.keys()):
    if context_vecs[context].length > max_val:
        max_con, max_val = context, context_vecs[context].length

print('      done!')
print('      calculating initial max_theta...')

dim_indices.append(max_con)
max_theta_con, max_theta = None, 0

for context in tqdm(context_vecs.keys()):
    theta[context] = 1 - delta(context, max_con)

    if theta[context] * context_vecs[context].length > max_theta:
        max_theta_con, max_theta = context, theta[context] * context_vecs[context].length

print('      done! max_theta = ' + str(max_theta) + ', max_theta context = ' + str(max_theta_con))

max_con = max_theta_con
dim_indices.append(max_con)

for i in range(2, K):
    max_theta_con, max_theta = None, 0

    print('   pass ' + str(i) + ':')

    for context in tqdm(context_vecs.keys()):
        theta[context] -= theta[context] * delta(context, max_con)
        t_ = theta[context] * context_vecs[context].length

        if t_ > max_theta:
            max_theta_con, max_theta = context, t_

    max_con = max_theta_con
    dim_indices.append(max_con)

    print('   max_theta = ' + str(max_theta) + ', max_theta context = ' + str(max_theta_con))

print('done!')
print('re-aligning & norming concept vectors...')

doc_freq_dict = [0.0 for _ in range(K)]

for concept in tqdm(cf_dict['con_feat'].keys()):
    cc_vec = cf_dict['con_feat'][concept]['cc_vector']
    new_vec, norm_sum = LinkedList(), 0

    for i in range(len(dim_indices)):
        cc_n = cc_vec.start
        new_coord = complex(0, 0)

        while cc_n:
            new_coord += cc_n.value * delta(cc_n.id, dim_indices[i])
            cc_n = cc_n.next

        if not new_coord == 0:
            x_, y_ = new_coord.real, new_coord.imag
            mag = ((x_ ** 2) + (y_ ** 2)) ** .5
            doc_freq_dict[i] += mag
            norm_sum += mag ** 2
            new_vec.insert_sorted(LLNode(i, [x_ / (x_ + y_), mag]))

    norm_sum = norm_sum ** .5
    cc_n = new_vec.start

    while cc_n:
        cc_n.value[1] = cc_n.value[1] / norm_sum
        cc_n = cc_n.next

    cf_dict['con_feat'][concept].update({'cc_vector': new_vec.to_json()})

print('done!')
print('test vector:\n')

test_vec = LinkedList()
test_vec.from_json(cf_dict['con_feat']['accordion']['cc_vector'])

print(test_vec.length)

test_list, n_ = [], test_vec.start

while n_:
    test_list.append((n_.id, n_.value))
    n_ = n_.next

print(test_list)
print('\ndumping data...')

with open('/home/mj/Desktop/McRae_v2/concepts_features_dict_DR_2k.pkl', 'wb') as f:
    pickle.dump(cf_dict, f)

with open('/home/mj/Desktop/McRae_v2/context_df_DR_2k.json', 'w') as f:
    json.dump(doc_freq_dict, f)

print('done!')
