import re

delimits = {'(': ')', '[': ']', '{': '}'}
imm_start_pat = re.compile('^0x[0-9a-fA-F]+|^[0-9]+|^-[0-9]+|^-0x[0-9a-fA-F]+')

def extract_from_quotes(val):
    res = val
    if "'" in val:
        res = val.split("'")[1].strip()
    return res

def extract_content(expr, left_delimit='('):
    right_delimit = delimits[left_delimit]
    return expr.split(left_delimit, 1)[1].rsplit(right_delimit, 1)[0].strip()

def replace_quote(val):
    res = val.replace("'", '"')
    return res
        

def construct_tuple_info(val):
    res = ''
    if val.startswith('('):
        val = extract_content(val)
        res = 'new Triplet('
        val_split = val.split(',')
        res += ', '.join([construct_tuple_info(v.strip()) for v in val_split])
        res += ')'
    elif imm_start_pat.match(val):
        res = val
    else:
        res = replace_quote(val)
    return res

def create_dictionary(p_version, name):
    p_split = p_version.split('\n')
    for p_i in p_split:
        p_info = name + '.put('
        p_i = p_i.strip()
        if p_i.endswith(','):
            p_i = p_i.rsplit(',', 1)[0]
        p_key, p_val = p_i.split(':', 1)
        p_key = replace_quote(p_key)
        p_val = p_val.strip()
        p_info += p_key + ', '
        p_info += construct_tuple_info(p_val) + ');'
        print(p_info)
        

if __name__ == '__main__':
    p_val = """'b': 'ae',
        'be': 'a',
        'l': 'ge',
        'le': 'g'"""
    name = 'aux_reg_info'
    res = replace_quote(p_val)
    print(res)
