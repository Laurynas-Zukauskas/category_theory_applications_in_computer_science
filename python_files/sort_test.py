from quicksort import Nil, Cons, O, S

def to_int(nat):
    if isinstance(nat, O):
        return 0
    elif isinstance(nat, S):
        nat_ = nat.field0
        return to_int(nat_) + 1
    
def to_nat(integ):
    if integ < 0:
        raise Exception("bad int")
    if integ == 0:
        return O()
    return S(to_nat(integ - 1))
    
def to_python_list(inlist):
    #print("???", inlist, "???")
    if isinstance(inlist, Nil):
        return []
    elif isinstance(inlist, Cons):
        head = inlist.field0
        tail = inlist.field1
        #print("returning", [head] + to_python_list(tail))
        return [head] + to_python_list(tail)

def to_inductive_list(inlist):
    if len(inlist) == 0:
        return Nil()
    else:
        return Cons(inlist[0], to_inductive_list(inlist[1:]))
    
def i2p(inlist):
    return [to_int(n) for n in to_python_list(inlist)]

def p2i(list):
    return to_inductive_list([to_nat(n) for n in list])