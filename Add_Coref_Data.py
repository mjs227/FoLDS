
import json
from tqdm import tqdm


def pseudo_dist(a, b):
    (x1, y1), (x2, y2) = a, b

    return (((x1 - x2) ** 2) + abs(y1 - y2)) ** .5


for fi in tqdm(range(105)):
    with open('/home/mj/Desktop/oh_man_v3.2/' + str(fi) + '.json', 'w') as f_new:
        with open('/home/mj/Desktop/oh_man_v3.1/' + str(fi) + '.json', 'r') as f_old:
            readlines = f_old.readlines()

        for line in readlines:
            item = json.loads(line)
            coref_data, mrs_data = item['coref'], item['text']
            coref_dict = [{} for _ in range(len(mrs_data))]

            # reorganize coref data for better efficiency when searching for candidates
            for i in range(len(coref_data)):
                main_i, main_start, main_end = coref_data[i]['main']

                if mrs_data[main_i]:
                    if i not in coref_dict[main_i].keys():
                        coref_dict[main_i].update({i: {'main': None, 'inst': []}})

                    coref_dict[main_i][i].update({'main': {'lnk': (main_start, main_end), 'cand': []}})
                    no_inst = True

                    for inst_i, inst_start, inst_end in coref_data[i]['inst']:
                        if mrs_data[inst_i]:
                            if i not in coref_dict[inst_i].keys():
                                coref_dict[inst_i].update({i: {'main': None, 'inst': []}})

                            coref_dict[inst_i][i]['inst'].append({'lnk': (inst_start, inst_end), 'cand': []})
                            no_inst = False

                    if no_inst:
                        coref_dict[main_i].pop(i)

            quants, preds = [], [{} for _ in range(len(mrs_data))]

            # extract quantifiers & handle spans from MRS structure
            for i in range(len(mrs_data)):
                if mrs_data[i]:
                    for j in range(len(mrs_data[i]['relations'])):
                        p = mrs_data[i]['relations'][j]['predicate']

                        if (p[-2:] == '_q' or '_q_' in p) and 'ARG0' in mrs_data[i]['relations'][j]['arguments'].keys()\
                                and 'x' in mrs_data[i]['relations'][j]['arguments']['ARG0']:
                            quants.append([(i, j), tuple(mrs_data[i]['relations'][j]['lnk'])])
                        else:
                            if mrs_data[i]['relations'][j]['label'] in preds[i].keys():
                                from_new, to_new = tuple(mrs_data[i]['relations'][j]['lnk'])
                                from_old, to_old = preds[i][mrs_data[i]['relations'][j]['label']]
                                preds[i].update({
                                    mrs_data[i]['relations'][j]['label']: (min(from_old, from_new), max(to_new, to_old))
                                })
                            else:
                                preds[i].update({
                                    mrs_data[i]['relations'][j]['label']: tuple(mrs_data[i]['relations'][j]['lnk'])
                                })

            # calculate coref candidate scores -- for each quantifier q in MRS m_i, search thru all instances c_k in m_i
            # of each coref cluster c and calculate (pseudo) Euclidean distance between (q_start, q_end) &
            # (c_k_start, c_k_end) -- most likely candidate is the closest
            for i in range(len(quants)):
                (mrs_i, mrs_j), (from_old, to_old) = tuple(quants[i])
                qeq = mrs_data[mrs_i]['qeq']

                if 'RSTR' in mrs_data[mrs_i]['relations'][mrs_j]['arguments'].keys():
                    q_h = mrs_data[mrs_i]['relations'][mrs_j]['arguments']['RSTR']
                    from_new, to_new = from_old, to_old

                    if q_h in preds[mrs_i].keys():
                        from_new, to_new = preds[mrs_i][q_h]
                    elif q_h in qeq.keys() and qeq[q_h] in preds[mrs_i].keys():
                        from_new, to_new = preds[mrs_i][qeq[q_h]]

                    from_old = min(from_old, from_new)
                    to_old = max(to_old, to_new)

                for k in coref_dict[mrs_i].keys():
                    if coref_dict[mrs_i][k]['main']:
                        dist = pseudo_dist((from_old, to_old), coref_dict[mrs_i][k]['main']['lnk'])

                        if len(coref_dict[mrs_i][k]['main']['cand']) == 0:
                            coref_dict[mrs_i][k]['main']['cand'].append((dist, mrs_j))
                        else:
                            n, len_c = 0, len(coref_dict[mrs_i][k]['main']['cand'])

                            while n < len_c and coref_dict[mrs_i][k]['main']['cand'][n][0] < dist:
                                n += 1

                            coref_dict[mrs_i][k]['main']['cand'] = coref_dict[mrs_i][k]['main']['cand'][:n] + \
                                [(dist, mrs_j)] + coref_dict[mrs_i][k]['main']['cand'][n:]

                    for j in range(len(coref_dict[mrs_i][k]['inst'])):
                        dist = pseudo_dist((from_old, to_old), coref_dict[mrs_i][k]['inst'][j]['lnk'])

                        if len(coref_dict[mrs_i][k]['inst'][j]['cand']) == 0:
                            coref_dict[mrs_i][k]['inst'][j]['cand'].append((dist, mrs_j))
                        else:
                            n, len_c = 0, len(coref_dict[mrs_i][k]['inst'][j]['cand'])

                            while n < len_c and coref_dict[mrs_i][k]['inst'][j]['cand'][n][0] < dist:
                                n += 1

                            coref_dict[mrs_i][k]['inst'][j]['cand'] = coref_dict[mrs_i][k]['inst'][j]['cand'][:n] + \
                                [(dist, mrs_j)] + coref_dict[mrs_i][k]['inst'][j]['cand'][n:]

            coref_cand, null_main = {}, set()

            # choose corresp. quantifier for each instance c_k of each coref cluster c -- search thru possible
            # candidates for c_k & choose the closest (pseudo Euclidean distance) available (i.e. that wasn't already
            # chosen for another instance c'_j of some cluster c'; c' == c or c' != c, but k != j) quantifier q -- i.e.
            # the closest q that isn't in coref_candidates
            for i in range(len(coref_dict)):
                for k in coref_dict[i].keys():
                    if coref_dict[i][k]['main']:
                        n, len_c = 0, len(coref_dict[i][k]['main']['cand'])

                        while n < len_c and (i, coref_dict[i][k]['main']['cand'][n][1]) in coref_cand.keys():
                            n += 1

                        if n == len_c:
                            min_inst, mi_index = len_c, 0

                            for m in range(len(coref_dict[i][k]['main']['cand'])):
                                c_k = coref_cand[(i, coref_dict[i][k]['main']['cand'][m][1])]
                                cand_inst = len(coref_data[c_k]['inst'])

                                if cand_inst < min_inst:
                                    min_inst, mi_index = cand_inst, m

                            if min_inst < len_c:
                                _, mrs_j = coref_dict[i][k]['main']['cand'][mi_index]
                                null_main.add(coref_cand[(i, mrs_j)])
                                coref_cand.update({(i, mrs_j): k})
                                mrs_data[i]['relations'][mrs_j].update({'coref': (k, True)})
                            else:
                                null_main.add(k)
                        else:
                            _, mrs_j = coref_dict[i][k]['main']['cand'][n]
                            coref_cand.update({(i, mrs_j): k})
                            mrs_data[i]['relations'][mrs_j].update({'coref': (k, True)})

            for i in range(len(coref_dict)):
                for k in coref_dict[i].keys():
                    if k not in null_main:
                        for j in range(len(coref_dict[i][k]['inst'])):
                            for n in range(len(coref_dict[i][k]['inst'][j]['cand'])):
                                if (i, coref_dict[i][k]['inst'][j]['cand'][n][1]) not in coref_cand.keys():
                                    _, mrs_j = coref_dict[i][k]['inst'][j]['cand'][n]
                                    coref_cand.update({(i, mrs_j): None})
                                    mrs_data[i]['relations'][mrs_j].update({'coref': (k, False)})

                                    break

            f_new.write(json.dumps({'title': item['title'], 'text': [m for m in mrs_data if m]}) + '\n')

        f_old.close()

    f_new.close()
