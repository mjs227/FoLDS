
import subprocess
import json
import re
from tqdm import tqdm


# system = 'pycharm'
# start = (0, 0)  # (file, sub-file)
system = 'command line'
start = (52, 0)


def result_to_ep(result):
    result = result[1:-1].strip()
    predicate = result.split('<')[0].replace('\"', '').strip()
    from_to = re.search(r'<\d+:\d+>', result).group()[1:-1].split(':')
    remove, count, offset = [], 0, 0

    for i in range(len(result)):
        if result[i] == '[':
            if count == 0:
                remove.append([i])

            count += 1
        elif result[i] == ']':
            count -= 1

            if count == 0:
                remove[-1].append(i)

    for pair in remove:
        result = result[:pair[0] - offset] + result[(pair[1] + 1) - offset:]
        offset += pair[1] - pair[0]

    label, arg_dict = '', {}
    tag_match = list(re.finditer(r'\S+: \S+', result))

    for pair in tag_match:
        tag, item = tuple(map(lambda s: s.replace('\"', '').strip(), pair.group().split(':')))

        if tag == 'LBL':
            label = item
        else:
            arg_dict.update({tag: item})

    return {
        'label': label,
        'predicate': predicate,
        'lnk': (int(from_to[0]), int(from_to[1])),
        'arguments': arg_dict
    }


def results_to_json(results):
    if results[0][:5] == 'SKIP:':
        return None

    rels_list, i = [], 0

    while not results[i][:4] == 'RELS':
        i += 1

    rels_list.append(result_to_ep(results[i][8:]))

    while not results[i][-1] == '>':
        i += 1

        if results[i][-1] == '>':
            rels_list.append(result_to_ep(results[i][:-2]))
        else:
            rels_list.append(result_to_ep(results[i]))

    while not results[i][:5] == 'HCONS':
        i += 1

    qeq_match = list(re.finditer(r'h\d+ qeq h\d+', results[i]))
    qeq_dict = {}

    for match in qeq_match:
        match_strs = match.group().split(' qeq ')
        qeq_dict.update({match_strs[0]: match_strs[1]})

    return {'relations': rels_list, 'qeq': qeq_dict}


cmd_fp = '/home/mj/Desktop/ace-0.9.34'

if start[1] < 0 or start[1] > 4:
    raise Exception

if system == 'pycharm':
    if start[0] >= 52 or start[0] < 0:
        raise Exception

    fi_range = range(start[0], 52)
elif system == 'command line':
    if start[0] >= 105 or start[0] < 52:
        raise Exception

    cmd_fp += '_2'
    fi_range = range(start[0], 105)
else:
    raise Exception

sub_fi_range = lambda x: range(start[1], 4) if x == start[0] else range(4)

for fi in fi_range:
    for sub_fi in sub_fi_range(fi):
        with open('/home/mj/Desktop/oh_man_v2.1/' + str(fi) + '_' + str(sub_fi) + '.json', 'r') as f:
            file = json.load(f)

        print('\nFile: ' + str(fi + 1) + '(' + str(sub_fi + 1) + '/4)/105:')

        for n in tqdm(range(len(file))):
            sentences = file[n]['text']
            outputs = [[]]
            p = subprocess.Popen(
                ['./ace', '-g', 'erg-1214-x86-64-0.9.34.dat', '-1Tf'],
                stdout=subprocess.PIPE,
                stdin=subprocess.PIPE,
                stderr=subprocess.DEVNULL,
                cwd=cmd_fp
            )

            for sentence in sentences:
                p.stdin.write(bytes(sentence, encoding='utf-8'))
                p.stdin.write(b'\n')

            p.stdin.close()
            readlines = p.stdout.readlines()
            k = 0

            while k < len(readlines):
                line = readlines[k].decode('utf-8').strip()

                if len(line) == 0:
                    k += 2
                    outputs.append([])
                else:
                    k += 1
                    outputs[-1].append(line)

            out_list = []

            for j in range(len(sentences)):
                try:
                    mrs = results_to_json(outputs[j])
                except:
                    mrs = None

                out_list.append({'sent': sentences[j], 'MRS': mrs})

            file[n].update({'text': out_list})

        with open('/home/mj/Desktop/oh_man_v3/' + str(fi) + '_' + str(sub_fi) + '.json', 'w') as f:
            json.dump(file, f)
