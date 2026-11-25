"""Independent exact stability verifier: Cayley transform + Schur recursion.

Python standard library only. Does NOT import any discovery, interval, Routh,
Hurwitz-determinant or third-party code. Inputs are exact rational controllers.

For Q(z)=a[0]+...+a[n]z^n, Schur's reduction is
  R(z)=(a[n]*Q(z)-a[0]*z^n*Q(1/z))/z.
Q is strictly Schur-stable iff |a[0]|<|a[n]| and R is Schur-stable.
The report proves the recursion using Rouche's theorem.
"""
from pathlib import Path
from fractions import Fraction
from math import comb, gcd, lcm
from functools import reduce
import hashlib
import json
import sys

if hasattr(sys, 'set_int_max_str_digits'): sys.set_int_max_str_digits(0)


def require(condition, message):
    if not condition: raise ValueError(message)


def primitive(coefficients):
    den = reduce(lcm, (v.denominator for v in coefficients), 1)
    ints = [v.numerator*(den//v.denominator) for v in coefficients]
    g = reduce(gcd, ints, 0)
    require(g != 0, 'zero polynomial')
    return [v//g for v in ints]


def shifted_integer_coefficients(p, margin):
    n = len(p)-1
    return primitive([sum((p[j]*comb(j, i)*(-margin)**(j-i) for j in range(i, n+1)), Fraction(0))
                      for i in range(n+1)])


def cayley(p):
    """(z+1)^n p((z-1)/(z+1)); integer coefficients, ascending."""
    n = len(p)-1
    a = [0]*(n+1)
    for j, c in enumerate(p):
        for i in range(j+1):
            for k in range(n-j+1):
                a[i+k] += c*comb(j, i)*(-1)**(j-i)*comb(n-j, k)
    require(a[-1] != 0, 'Cayley leading coefficient zero (p(1)=0)')
    return a


def schur(a):
    records = []
    while len(a) > 1:
        n = len(a)-1
        require(abs(a[0]) < abs(a[-1]), f'Schur inequality failed at degree {n}')
        margin = a[-1]*a[-1]-a[0]*a[0]
        records.append({'degree': n, 'strict_inequality_verified': True,
                        'positive_difference_sha256': hashlib.sha256(str(margin).encode()).hexdigest()})
        b = [a[-1]*a[j]-a[0]*a[n-j] for j in range(n+1)]
        require(b[0] == 0, 'Schur reduction constant not zero')
        a = b[1:]
        g = reduce(gcd, a, 0)
        require(g > 0, 'zero reduced polynomial')
        a = [v//g for v in a]
    require(a[0] != 0, 'zero final constant')
    return records


def check_polynomial(p, margin):
    require(p[-1] != 0, 'polynomial degree is not as declared')
    return schur(cayley(shifted_integer_coefficients(p, margin)))


def negative_controls():
    check_polynomial(list(map(Fraction, [6, 11, 6, 1])), Fraction(1, 2))
    for p in [[1, 0, 1], [2, 1, 1, 1], [-1, 0, 1]]:
        try: check_polynomial(list(map(Fraction, p)), Fraction(0))
        except ValueError: pass
        else: raise RuntimeError('negative control accepted')


def certify(path):
    data = json.loads(path.read_text(encoding='utf-8'))
    require(data['coefficient_order'] == 'ascending', 'unsupported coefficient order')
    denominator = int(data['coefficient_denominator'])
    require(denominator > 0, 'denominator must be positive')
    x = [Fraction(int(a), denominator) for a in data['x_numerators']]
    y = [Fraction(int(a), denominator) for a in data['y_numerators']]
    delta = Fraction(data['target_delta'])
    margin = Fraction(data['claimed_margin_to_verify'])
    require(0 < delta < 1 and margin > 0, 'invalid parameter/margin')
    require(len(y) <= len(x) and x[-1] != 0 and y[-1] != 0, 'invalid degree condition')
    z = [Fraction(0)]*(len(x)+2)
    for j, a in enumerate(x): z[j] += a; z[j+1] -= 2*delta*a; z[j+2] += a
    for j, a in enumerate(y): z[j] -= a; z[j+2] += a
    out = {'input_sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
        'arithmetic': 'Python standard-library exact integers/Fraction',
        'method': 'independent Cayley transform and Schur recursion',
        'delta': str(delta), 'root_real_parts_strictly_below': str(-margin), 'polynomials': {}}
    for name, p in [('x', x), ('y', y), ('z', z)]:
        trace = check_polynomial(p, margin)
        out['polynomials'][name] = {'degree': len(p)-1, 'schur_trace': trace}
        print(path.name, name, len(trace), 'strict Schur inequalities PASS', flush=True)
    out['status'] = 'PASS'
    path.with_name(path.stem+'_schur_certificate.json').write_text(json.dumps(out, indent=2), encoding='utf-8')
    return out


if __name__ == '__main__':
    negative_controls()
    paths = sys.argv[1:]
    require(bool(paths), 'Usage: python verify_schur_standalone.py path/to/controller.json [...]')
    for name in paths: certify(Path(name).resolve())
