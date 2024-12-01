LOOKUP = {}
VAR = []
LOW = []
HIGH = []

class memoized(object):
    def __init__(self, func):
        self.func = func
        self.cache = {}

    def __call__(self, *args):
        try:
            return self.cache[args]
        except KeyError:
            value = self.func(*args)
            self.cache[args] = value
            return value


def zero():
    return -2

def one():
    return -1

@memoized
def bdd(v, low, high):
    if low == high:
        return low
    if (v, low, high) not in LOOKUP:
        i = len(VAR)
        VAR.append(v)
        LOW.append(low)
        HIGH.append(high)
        LOOKUP[(v, low, high)] = i
    return LOOKUP[(v, low, high)]

def bdd_equals(b1, b2):
    return b1 == b2

def bdd_atom(v):
    return bdd(v, zero(), one())

def bdd_state(s):
    b = one()
    for var, val in reversed(sorted(s.items())):
        if val:
            b = bdd(var, zero(), b)
        else:
            b = bdd(var, b, zero())
    return b

@memoized
def bdd_union(b1, b2):
    if b1 == zero() and b2 == zero():
        return zero()
    elif b1 == one() or b2 == one():
        return one()
    elif b1 == zero():
        return b2
    elif b2 == zero():
        return b1
    elif VAR[b1] < VAR[b2]:
        return bdd(VAR[b1], bdd_union(LOW[b1], b2), bdd_union(HIGH[b1], b2))
    elif VAR[b1] == VAR[b2]:
        return bdd(VAR[b1], bdd_union(LOW[b1], LOW[b2]), bdd_union(HIGH[b1], HIGH[b2]))
    elif VAR[b1] > VAR[b2]:
        return bdd(VAR[b2], bdd_union(b1, LOW[b2]), bdd_union(b1, HIGH[b2]))

@memoized
def bdd_complement(b):
    if b == zero():
        return one()
    elif b == one():
        return zero()
    else:
        return bdd(VAR[b], bdd_complement(LOW[b]), bdd_complement(HIGH[b]))

@memoized
def bdd_forget(b, v):
    if b == zero() or b == one() or VAR[b] > v:
        return b
    elif VAR[b] < v:
        return bdd(VAR[b], bdd_forget(LOW[b], v), bdd_forget(HIGH[b], v))
    else:
        return bdd_union(LOW[b], HIGH[b])

@memoized
def bdd_intersection(b1, b2):
    not_b1 = bdd_complement(b1)
    not_b2 = bdd_complement(b2)
    return bdd_complement(bdd_union(not_b1, not_b2))

@memoized
def bdd_setdifference(b1, b2):
    return bdd_intersection(b1, bdd_complement(b2))

def bdd_isempty(b):
    return bdd_equals(b, zero())

@memoized
def bdd_biimplication(b1, b2):
    b1_and_b2 = bdd_intersection(b1, b2)
    not_b1 = bdd_complement(b1)
    not_b2 = bdd_complement(b2)
    not_b1_and_not_b2 = bdd_intersection(not_b1, not_b2)
    return bdd_union(b1_and_b2, not_b1_and_not_b2)

@memoized
def bdd_rename(b, v1, v2):
    v1_eq_v2 = bdd_biimplication(bdd_atom(v1), bdd_atom(v2))
    return bdd_forget(bdd_intersection(b, v1_eq_v2), v1)

def bdd_get_ids_of_arbitrary_state(b):
    assert(not bdd_equals(b, zero()))
    s = {}
    node = b
    while not bdd_equals(node, zero()):
        if bdd_equals(node, one()):
            return s
        elif bdd_equals(HIGH[node], zero()):
            assert(not bdd_equals(LOW[node], zero()))
            s[VAR[node]] = False
            node = LOW[node]
        else:
            s[VAR[node]] = True
            node = HIGH[node]
