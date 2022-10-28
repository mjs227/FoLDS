
import json
import pickle
import pandas
import math
import random
from scipy.stats import spearmanr
from tqdm import tqdm
from datetime import datetime


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
        elif n.id < self.start.id:
            n.next = self.start
            self.start = n
        elif n.id > self.end.id:
            self.end.next = n
            self.end = n
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


class OrderedNode:
    def __init__(self, id_, val):
        self.id, self.value = id_, val

    def __lt__(self, node):
        return self.value < node.value


class OrderedComplex:
    def __init__(self, val):
        self.value = val

    def __lt__(self, node):
        return abs(self.value) < abs(node.value)


def sim_metric(x, y):
    x_keys, y_keys = set(x.nodes.keys()), set(y.nodes.keys())
    node_int = x_keys.intersection(y_keys)

    if len(node_int) == 0:
        return None

    re, im = 0, 0
    x_sum, ovl_sum = 0, 0

    for n_id in node_int:
        idf = math.log(MAX_DOC_FREQ / doc_freq_dict[n_id], 2)
        n_x, n_y = x.nodes[n_id], y.nodes[n_id]
        ovl_sum += min(n_x.value[1], n_y.value[1]) * idf
        x_sum += n_x.value[1] * idf
        re_val = max(n_x.value[0], 1 - abs(n_x.value[0] - n_y.value[0]))
        im += 1 - re_val
        re += re_val * idf

        # im += 1 - min(n_y.value[0], n_x.value[0])
        # re += 1 - min(n_y.value[0], 1 - n_x.value[0]) * idf

        # im_val = min(n_y.value[0], 1 - n_x.value[0])
        # im += im_val  # * idf
        # re += (1 - im_val)   # * idf

    for n_id in x_keys - set(node_int):
        idf = math.log(MAX_DOC_FREQ / doc_freq_dict[n_id], 2)
        x_sum += x.nodes[n_id].value[1] * idf

    if x_sum == 0 or ovl_sum == 0:
        return None

    ovl = ovl_sum / x_sum
    value = complex(re, im)

    return (value / abs(value)) * ovl


def get_sim(w_1, w_2):
    if w_1 in sim_dict.keys():
        if w_2 in sim_dict[w_1].keys():
            sim = sim_dict[w_1][w_2]
        else:
            sim = sim_metric(key_dict[w_1], cf_dict['con_feat'][w_2]['cc_vector'])
            sim_dict[w_1].update({w_2: sim})
    else:
        sim = sim_metric(key_dict[w_1], cf_dict['con_feat'][w_2]['cc_vector'])
        sim_dict.update({w_1: {w_2: sim}})

    return sim if sim else None


def concreteness(sim, val):
    re_sim = sim.real / (sim.real + sim.imag)
    # re_val = val.real / (val.real + val.imag)

    return abs(.5 - re_sim) * 2  # min(abs(.5 - re_sim), abs(.5 - re_val)) * 2


def infer(con, k_words, top_k=5):
    out = [[] for _ in range(NUM_FEATURES)]

    for w_features, w_feat_vec, w_sim in k_words:
        sim = get_sim(con, w_sim)

        if sim is not None:
            for f_i in range(NUM_FEATURES):
                if str(f_i) in w_features:
                    w_val = w_feat_vec[f_i]
                    w_val_r = w_val / (w_val.real + w_val.imag)
                    w_val = complex(1 + w_val_r, 1 - w_val_r)
                    w_val = w_val / abs(w_val)
                else:
                    w_val = complex(0, 1)

                w_val_pred = w_val * sim
                # out[f_i].append(OrderedComplex(complex(max(w_val_pred.real, 0), w_val_pred.imag)))
                out[f_i].append(OrderedComplex(complex(abs(w_val_pred.real), abs(w_val_pred.imag))))

    out_ = [complex(0, 0) for _ in range(NUM_FEATURES)]

    for f_i in range(NUM_FEATURES):
        out[f_i].sort()
        out_[f_i] = sum(x.value for x in out[f_i][-1 * top_k:])

    return out_


def norm_vals(in_vals, thrsh):
    out = [0 if (abs(x.imag) + abs(x.real) == 0 or abs(x) <= thrsh) else (abs(x.real) / (abs(x.imag) + abs(x.real))) for x in in_vals]

    return out


def evaluate(predicted, actual, floor=0.0, thrsh=0.0):
    pred_ordered, pred_r = [], []
    pred_norm = norm_vals(predicted, thrsh)
    norm_max, norm_min = 0, 1

    for x in pred_norm:
        norm_max = max(norm_max, x)
        norm_min = min(norm_min, x)

    max_min = norm_max - norm_min
    max_min = max_min if max_min > 0 else 1

    for f_i in range(len(pred_norm)):
        # pred_val = pred_norm[f_i] - norm_min
        # pred_val = pred_val / max_min
        # pred_val = 0 if pred_val < floor else pred_val
        # pred_ordered.append(OrderedNode(str(f_i), pred_val))
        # pred_r.append(pred_val)
        pred_val = 0 if pred_norm[f_i] < floor else pred_norm[f_i]
        pred_r.append(pred_val)
        pred_ordered.append(OrderedNode(str(f_i), pred_val))

    pred_ordered.sort()
    pred_ordered.reverse()
    prec_set, prec_cnt, prec_score = set(actual['features'].keys()), 0, 0

    for i in range(len(pred_ordered)):
        if pred_ordered[i].id in prec_set:
            prec_cnt += 1
            prec_score += prec_cnt / (i + 1)

    s_r_df = pandas.DataFrame({'predicted': pred_r, 'actual': actual['ff_vector']})
    rho, _ = spearmanr(s_r_df['predicted'], s_r_df['actual'])

    if math.isnan(rho):
        return evaluate(prop_freq_c, actual, floor=floor, thrsh=thrsh)

    return prec_score / len(prec_set), rho, pred_r


RNDM = False

print('loading data...')

with open('/home/mj/Desktop/McRae_v2/fold_words.json', 'r') as f:
    folds = json.load(f)

if RNDM:
    r_fold = random.choice(list(range(len(folds))))
    folds = [folds[r_fold]]

    print(r_fold)

with open('/home/mj/Desktop/McRae_v2/concepts_features_dict_lt_10.pkl', 'rb') as f:
    cf_dict = pickle.load(f)

with open('/home/mj/Desktop/McRae_v2/concepts_features_dict_lt_10.pkl', 'rb') as f:
    key_dict = pickle.load(f)

with open('/home/mj/Desktop/McRae_v2/context_df_lt_10.json', 'r') as f:
    doc_freq_dict = json.load(f)

with open('/home/mj/Desktop/McRae_v2/analysis_all.json', 'r') as f:
    prev_a = json.load(f)

with open('/home/mj/Desktop/McRae_v2/transfer_dict.json', 'r') as f:
    transfer_dict = json.load(f)

print('done!')

known_words_master = set(cf_dict['con_feat'].keys())
NUM_FEATURES = 2526
MAX_LEN, MIN_LEN = 0, 1000
MAX_DOC_FREQ = max(doc_freq_dict) + 1

feat_list_db = ['' for _ in range(NUM_FEATURES)]

for f_k in cf_dict['feat_ids'].keys():
    feat_list_db[cf_dict['feat_ids'][f_k]] = f_k

print('generating vectors...')
vec_lens = []
max_vl = 0
prop_freq = [0 for _ in range(NUM_FEATURES)]
prop_freq_c = [complex(0, 0) for _ in range(NUM_FEATURES)]

for concept in tqdm(cf_dict['con_feat'].keys()):
    cc_vec = LinkedList()
    cc_vec.from_json(cf_dict['con_feat'][concept]['cc_vector'])
    cf_dict['con_feat'][concept].update({'cc_vector': cc_vec})
    MAX_LEN = max(cc_vec.length, MAX_LEN)
    MIN_LEN = min(cc_vec.length, MIN_LEN)

    for feat in cf_dict['con_feat'][concept]['features'].keys():
        prop_freq[int(feat)] += 1

    # key_vec = LinkedList()
    # key_vec.from_json(key_dict[concept])
    key_dict.update({concept: cc_vec})

max_pf = max(prop_freq)

for feat in range(NUM_FEATURES):
    prop_freq[feat] = prop_freq[feat] / max_pf
    prop_freq_c[feat] = complex(prop_freq[feat], 1 - prop_freq[feat])
    prop_freq_c[feat] = prop_freq_c[feat] / abs(prop_freq_c[feat])

no_sim = {'zucchini', 'projector', 'microwave'}
avg_prec, spearman_rho = [], []
sim_dict = {}
analysis_dict = {word: {} for word in cf_dict['con_feat'].keys() if word not in no_sim}
total_del_sr = 0

for fold_i in range(len(folds)):
    print('FOLD ' + str(fold_i) + ':')
    fold = folds[fold_i]
    fold_set = set(fold)
    known_words_index = known_words_master - fold_set
    known_words = [(set(cf_dict['con_feat'][c]['features'].keys()), cf_dict['con_feat'][c]['fc_vector'], c) for c in cf_dict['con_feat'].keys() if c not in fold_set]
    avg_prec_fold, spearman_rho_fold = [], []

    for word in fold:
        if word not in prev_a.keys():
            prev_a.update({word: {'ap': 0, 'rho': 0}})

        if word not in no_sim:
            pred_c_vec = infer(word, known_words, top_k=25)  # 45
            a_p, s_r, pred_r_vec = evaluate(pred_c_vec, cf_dict['con_feat'][word], floor=0.15, thrsh=0.0)
            prev_ap, prev_sr = prev_a[word]['ap'], prev_a[word]['rho']
            avg_prec_fold.append(a_p)
            spearman_rho_fold.append(s_r)
            ap_fold_val, sr_fold_val = sum(avg_prec_fold) / len(avg_prec_fold), sum(spearman_rho_fold) / len(spearman_rho_fold)
            del_ap = a_p - prev_ap
            del_ap_str = ('+' if del_ap > 0 else '') + str(del_ap)
            del_sr = s_r - prev_sr
            total_del_sr += del_sr
            del_sr_str = ('+' if del_sr > 0 else '') + str(del_sr) + ' (' + ('+' if total_del_sr > 0 else '') + str(total_del_sr) + ')'
            rtn_on = [OrderedNode((feat_list_db[i_], str(i_) in cf_dict['con_feat'][word]['features'], pred_r_vec[i_]), pred_r_vec[i_]) for i_ in range(len(pred_r_vec))]
            rtn_on.sort()
            rtn_on.reverse()
            rtn = [i_.id for i_ in rtn_on if i_.value > 0]
            analysis_dict[word].update({'ap': a_p, 'rho': s_r, 'rtn': rtn})

            print(word.upper() + ' (P, A): ' + str(list(zip(pred_r_vec, cf_dict['con_feat'][word]['ff_vector']))))
            print('AveP: ' + str(a_p) + ' (inst), ' + str(ap_fold_val) + ' (fold); SRCC: ' + str(s_r) + ' (inst), ' + str(sr_fold_val) + ' (fold)')
            print('AveP: ' + del_ap_str + '; SRCC: ' + del_sr_str)
            print(cf_dict['con_feat'][word]['cc_vector'].length)
            print(rtn)
            print()

    avg_prec += avg_prec_fold
    spearman_rho += spearman_rho_fold

    print()
    print('   FOLD:')
    print('      MAP: ' + str(sum(avg_prec_fold) / len(avg_prec_fold)))
    print('      Spearman Rho: ' + str(sum(spearman_rho_fold) / len(spearman_rho_fold)))
    print('   TOTAL:')
    print('      MAP: ' + str(sum(avg_prec) / len(avg_prec)))
    print('      Spearman Rho: ' + str(sum(spearman_rho) / len(spearman_rho)))
    print()

# with open('/home/mj/Desktop/McRae_v2/record.json', 'r') as f:
#     record_list = json.load(f)
#
# with open('/home/mj/Desktop/McRae_v2/record.json', 'w') as f:
#     json.dump([(str(datetime.now()), sum(avg_prec) / len(avg_prec), sum(spearman_rho) / len(spearman_rho))] + record_list, f)

if total_del_sr >= 0 and not RNDM:
    with open('/home/mj/Desktop/McRae_v2/analysis_all.json', 'w') as f:
        json.dump(analysis_dict, f)