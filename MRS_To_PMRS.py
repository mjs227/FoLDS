import json
import Parser
import nltk
import pickle
import gc
from nltk.stem import WordNetLemmatizer
from datetime import datetime
from tqdm import tqdm


mrs_ops = {
    'univ': {'_every_q', 'every_q', '_all_q', 'udef_q', '_udef_q', '_these_q_dem', '_most_q', '_both_q',
             '_half_q', '_each_q', '_each+and+every_q', '_many+a_q', '_those_q_dem', 'free_relative_ever_q'},
    'exist': {'_a_q', '_some_q', '_the_q', '_this_q_dem', 'pronoun_q', 'def_explicit_q', 'def_implicit_q',
              '_enough_q', 'free_relative_q', '_that_q_dem', '_another_q', '_any_q', 'which_q', '_which_q',
              '_such_q', '_a+bit_q', '_a+little_q', '_an+additional_q', '_either_q', '_some_q_indiv',
              '_such+a_q', '_the+most_q', '_twice_q', '_what+a_q', 'some_q'},
    'neg_exist': {'_no_q', '_neither_q', '_any+more_q', '_the+least_q', '_no+more_q'},
    'proper': {'proper_q', 'number_q'},
    'neg_e': {'_no+longer_a_1', '_by+no+means_a_1', '_no_x_deg'},  # negates the event
    'neg_xh': {'_not_x_deg', '_no+good_a_1', '_not+quite_x', 'few+if+any_a', 'little-few_a',
               'not_x_deg'},  # negates either the bvar of a quant or shares a handle with a quant
    'neg': {'neg', '_never+before_a_1', '_never_a_1', '_no_a_1', '_not+necessarily_a_1', '_not+quite_a',
            '_not+yet_a_1'},  # negates predicate handle(s)
    'conn': {'_and_c', '_or_c', 'implicit_conj', '_but_c', '_as+well+as_c', '_and+then_c', '_then_c',
             '_after_c', '_albeit_c', '_and+also_c', '_and+finally_c', '_and+so_c', '_and+thus_c',
             '_and+yet_c', '_and_c_btwn', '_but+also_c', '_but+then_c', '_else_c', '_even_c', '_except+that_c',
             '_if+not_c', '_let+alone_c', '_nor_c', '_not+to+mention_c', '_or+else_c', '_plus_c', '_though_c',
             '_together-with_c', '_yet_c', 'num_seq'},
    'neg_conn': {'_and+not_c', '_rather+than_c', '_but+not_c', '_instead+of_c', '_much+less_c', '_not+to+say_c',
                 '_not_c'},
    'named': {'named_n', 'named', 'yofc', 'mofy', 'dofm', 'card', 'ord', 'dofw', 'season', '_ad_x', '_am_x',
              '_bc_x', '_pm_x', 'greet', 'holiday', 'hour_prep', 'meas_np', 'minute', 'numbered_hour',
              'timezone_p'},
    'remove_q': {'idiom_q_i'},
    'ignore': {'parg_d', 'generic_entity', '_be_v_nv', '_be_v_there', 'nominalization', 'superl', 'pron',
               'unknown', 'year_range', 'INVALID', 'temp', 'temp_loc_x', 'subord', 'comp', 'ellipsis_ref',
               '_prior+to', 'comp_equal', 'addressee', '_colon_p_namely', 'focus_d', 'plus', '_a+great+many_q',
               '_certain_q', '_part_q', '_x_q', '_if+not_a_1', '_never+mind_a_1', '_no+doubt_a_1',
               '_not+always_a', '_not+even_x_deg', '_not+just_x_deg', '_not+only_x_deg', '_not+that_x',
               '_why+not_x', '_and_c_mod', '_but_c_mod', '_et+al_c', '_etc_c', '_except_c', '_minus_c',
               '_plus-minus_c', '_so+on_c', '_versus_c', '_vice+versa_c', 'abstr_deg', 'comp_enough', 'comp_less',
               'comp_not+so', 'comp_not+too', 'comp_so', 'comp_too', 'discourse', 'ellipsis', 'ellipsis_expl',
               'eventuality', 'excl', 'fraction', 'fw_seq', 'generic_verb', 'interval', 'interval_p_start',
               'interval_p_end', 'ne_x', 'parenthetical', 'polite', 'property', 'prpstn_to_prop', 'recip_pro',
               'refl_mod', 'relative_mod', 'times', 'v_event'},
    'subtype': {'_type_n_of-n', '_breed_n_of-n', '_species_n_of-n', '_variety_n_of-n', '_kind_n_of-n', 'part_of',
                '_piece_n_of'},
    'as': {'_as_p', '_as_p_nbar'}
}
mrs_ops.update({'conn': mrs_ops['conn'].union(mrs_ops['neg_conn'])})

mofy_dofw = {
    'mofy': {
        'Jan': 'january',
        'Feb': 'february',
        'Mar': 'march',
        'Apr': 'april',
        'May': 'may',
        'Jun': 'june',
        'Jul': 'july',
        'Aug': 'august',
        'Sep': 'september',
        'Oct': 'october',
        'Nov': 'november',
        'Dec': 'december'
    },
    'dofw': {
        'Mon': 'monday',
        'Tue': 'tuesday',
        'Wed': 'wednesday',
        'Thu': 'thursday',
        'Fri': 'friday',
        'Sat': 'saturday',
        'Sun': 'sunday'
    }
}

tb_to_wn = {
    'n': 'n',
    'nn': 'n',
    'a': 'a',
    'jj': 'a',
    'v': 'v',
    'vb': 'v'
}

nltk.download('omw-1.4')
nltk.download('wordnet')
lmtzr = WordNetLemmatizer()
and_or_err, pmrs_err, total_pmrs = 77, 727, 258194

for fi in range(105):
    with open('/home/mj/Desktop/oh_man_v3.2/' + str(fi) + '.json', 'r') as f:
        readlines = f.readlines()

    print('FILE ' + str(fi) + ': ')

    all_pmrs, all_coref = [], {'GOOD': set(), 'TYPE': {}, 'CLUSTERS': {}}
    and_or_err_fi, pmrs_err_fi = 0, 0

    for ai in tqdm(range(len(readlines))):  # line = article
        item, parser = json.loads(readlines[ai]), Parser.Parser(lmtzr, mrs_ops, mofy_dofw, tb_to_wn, fi, ai, datetime)
        pmrs_list, coref_data, and_or_err_ai, pmrs_err_ai = parser.parse(item['text'])
        and_or_err_fi += and_or_err_ai
        pmrs_err_fi += pmrs_err_ai
        all_pmrs += pmrs_list
        all_coref.update({
            'GOOD': all_coref['GOOD'].union(coref_data['GOOD']),
            'TYPE': {**all_coref['TYPE'], **coref_data['TYPE']},
            'CLUSTERS': {**all_coref['CLUSTERS'], **coref_data['CLUSTERS']}
        })

    with open('/home/mj/Desktop/oh_man_v4/' + str(fi) + '_coref.json', 'w') as f:
        json.dump({
            'GOOD': list(str(x) for x in all_coref['GOOD']),
            'TYPE': {str(k): str(t) for k, t in all_coref['TYPE'].items()},
            'CLUSTERS': {str(k): cl.to_json() for k, cl in all_coref['CLUSTERS'].items()}
        }, f)

    with open('/home/mj/Desktop/oh_man_v4/' + str(fi) + '_docdict.json', 'w') as f:
        json.dump({}, f)

    with open('/home/mj/Desktop/oh_man_v4/' + str(fi) + '_pmrs.pkl', 'wb') as f:
        pickle.dump(all_pmrs, f)

    and_or_err += and_or_err_fi
    pmrs_err += pmrs_err_fi
    total_pmrs += len(all_pmrs)

    print('   PMRS:')
    print('      FILE:  ' + str(len(all_pmrs)))
    print('      TOTAL: ' + str(total_pmrs))
    print('   COREF (FILE):')
    print('      GOOD:     ' + str(len(all_coref['GOOD'])))
    print('      TYPE:     ' + str(len(all_coref['TYPE'])))
    print('      CLUSTERS: ' + str(len(all_coref['CLUSTERS'])))
    print('   ERRORS:')
    print('      FILE:')
    print('         AND/OR: ' + str(and_or_err_fi))
    print('         PMRS:   ' + str(pmrs_err_fi))
    print('      TOTAL:')
    print('         AND/OR: ' + str(and_or_err))
    print('         PMRS:   ' + str(pmrs_err))
    print()

    for pmrs in all_pmrs:
        del pmrs

    del all_pmrs
    del all_coref
    gc.collect()
