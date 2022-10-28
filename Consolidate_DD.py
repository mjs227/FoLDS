
import json
from tqdm import tqdm


def get_paths(path, dd_obj):
    out = []

    if type(dd_obj) is dict:
        for k in dd_obj.keys():
            for lower_path in get_paths(path + [k], dd_obj[k]):
                out.append(lower_path)
    else:
        return [path + [dd_obj]]

    return out


with open('/home/mj/Desktop/Phase2_1/0_DD.json', 'r') as f:
    doc_dict = json.load(f)

for fi in tqdm(range(1, 104)):
    with open('/home/mj/Desktop/Phase2_1/' + str(fi) + '_DD.json', 'r') as f:
        file = json.load(f)

    paths = []

    for fk in file.keys():
        paths += get_paths([fk], file[fk])

    for p in paths:
        dd_, args = doc_dict, p[:-2]

        for a in args:
            if a not in dd_.keys():
                dd_.update({a: {}})

            dd_ = dd_[a]

        if p[-2] in dd_.keys():
            val = dd_[p[-2]]
            dd_.update({p[-2]: [val[0] + p[-1][0], val[1] + p[-1][1]]})
        else:
            dd_.update({p[-2]: p[-1]})

with open('/home/mj/Desktop/Phase2_1/DD_MASTER.json', 'w') as f:
    json.dump(doc_dict, f)
