"""Deterministic consistency checks; not formal proof verification."""
from math import log2, ceil, isclose


def entropy(p):
    return 0.0 if p in (0, 1) else -p*log2(p)-(1-p)*log2(1-p)


def shortcut(n):
    return (3*n+1)//2 if n % 2 else n//2


def odd_step(n):
    z, a = 3*n+1, 0
    while z % 2 == 0:
        z //= 2
        a += 1
    return z, a


alpha = log2(3)
lo, hi = 0.5, 1/alpha
for _ in range(100):
    mid = (lo+hi)/2
    if entropy(mid) > alpha*mid:
        lo = mid
    else:
        hi = mid
beta = alpha*(lo+hi)/2
kappa = 1/entropy(1/alpha)
assert isclose(kappa, 1.052680858607972, abs_tol=1e-14)
assert isclose(1/beta, 1.035856760034048, abs_tol=1e-14)
print(f"Maximum-height exponent: {kappa:.14f}")
print(f"Cited spatial-bound consequence: {1/beta:.14f}")
print(f"Exponent increment: {kappa-1/beta:.14f}")

cases = 0
for start in range(1, 2000):
    orbit, seen, n = [], set(), start
    for _ in range(120):
        if n in seen:
            break
        seen.add(n)
        orbit.append(n)
        n = shortcut(n)
    for m in (2, 5, 10, 25, 50, 100):
        if len(orbit) < m:
            continue
        states = orbit[:m]
        r = ceil(log2(max(states)+1))
        p = sum(x % 2 for x in states)/m
        q = p-(r-1)/(2*m)
        words = []
        for x in states:
            word = []
            for _ in range(r):
                word.append(x % 2)
                x = shortcut(x)
            words.append(tuple(word))
        assert len(set(words)) == m
        if q >= 0.5:
            assert log2(m) <= r*entropy(q)+1e-11
            cases += 1
        end = shortcut(states[-1])
        error = sum(log2(1+1/(3*x)) for x in states if x % 2)
        assert isclose(log2(end)-log2(start), alpha*m*p-m+error, abs_tol=1e-10)
assert cases > 0
print(f"Finite entropy and growth identities checked; {cases} entropy cases.")
for h in range(1, 150):
    n = 2**(h+1)-1
    for t in range(h):
        assert n+1 == 3**t * 2**(h+1-t)
        n, a = odd_step(n)
        assert a == 1
print("Sharp shallow-step family checked through length 149.")
