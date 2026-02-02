from dataclasses import dataclass

class Bool:
    pass

@dataclass
class True_(Bool):
    pass

@dataclass
class False_(Bool):
    pass

class Nat:
    pass

@dataclass
class O(Nat):
    pass

@dataclass
class S(Nat):
    field0: object

def isZero(n):
    if isinstance(n, O):
        return True_()
    if isinstance(n, S):
        _ = n.field0
        return False_()
    raise ValueError("Non-exhaustive patterns in function")

class List:
    pass

@dataclass
class Nil(List):
    pass

@dataclass
class Cons(List):
    field0: object
    field1: object

def concat(l, r):
    if isinstance(l, Nil):
        return r
    if isinstance(l, Cons):
        l0 = l.field0
        ls = l.field1
        return Cons(l0, concat(ls, r))
    raise ValueError("Non-exhaustive patterns in function")

def less(n, m):
    if isinstance(m, O):
        return False_()
    if isinstance(m, S):
        q = m.field0
        if isinstance(n, O):
            return True_()
        if isinstance(n, S):
            p = n.field0
            return less(p, q)
        raise ValueError("Non-exhaustive patterns in function")
    raise ValueError("Non-exhaustive patterns in function")

def lesseq(n, m):
    if isinstance(n, O):
        return True_()
    if isinstance(n, S):
        p = n.field0
        if isinstance(m, O):
            return False_()
        if isinstance(m, S):
            q = m.field0
            return lesseq(p, q)
        raise ValueError("Non-exhaustive patterns in function")
    raise ValueError("Non-exhaustive patterns in function")

def greatereq(n, m):
    if isinstance(m, O):
        return True_()
    if isinstance(m, S):
        q = m.field0
        if isinstance(n, O):
            return False_()
        if isinstance(n, S):
            p = n.field0
            return greatereq(p, q)
        raise ValueError("Non-exhaustive patterns in function")
    raise ValueError("Non-exhaustive patterns in function")

def allless(l, n):
    if isinstance(l, Nil):
        return Nil()
    if isinstance(l, Cons):
        m = l.field0
        ls = l.field1
        if isinstance(less(m, n), True_):
            return Cons(m, allless(ls, n))
        if isinstance(less(m, n), False_):
            return allless(ls, n)
        raise ValueError("Non-exhaustive patterns in function")
    raise ValueError("Non-exhaustive patterns in function")

def allgeq(l, n):
    if isinstance(l, Nil):
        return Nil()
    if isinstance(l, Cons):
        m = l.field0
        ls = l.field1
        if isinstance(greatereq(m, n), True_):
            return Cons(m, allgeq(ls, n))
        if isinstance(greatereq(m, n), False_):
            return allgeq(ls, n)
        raise ValueError("Non-exhaustive patterns in function")
    raise ValueError("Non-exhaustive patterns in function")

def qaux(n, l):
    if isinstance(n, O):
        return Nil()
    if isinstance(n, S):
        p = n.field0
        if isinstance(l, Nil):
            return Nil()
        if isinstance(l, Cons):
            m = l.field0
            ls = l.field1
            return concat(qaux(p, allless(ls, m)), Cons(m, qaux(p, allgeq(ls, m))))
        raise ValueError("Non-exhaustive patterns in function")
    raise ValueError("Non-exhaustive patterns in function")

def length(l):
    if isinstance(l, Nil):
        return O()
    if isinstance(l, Cons):
        _ = l.field0
        ls = l.field1
        return S(length(ls))
    raise ValueError("Non-exhaustive patterns in function")

def quicksort(l):
    return qaux(length(l), l)
