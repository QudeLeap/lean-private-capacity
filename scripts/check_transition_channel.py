#!/usr/bin/env python3
"""Exact independent checks of the transition-channel manuscript.

Requires SymPy. These checks are supplementary; their output is not a premise
of any Lean theorem. Input matrices follow private_superactivation.tex.
"""

if not __debug__:
    raise RuntimeError('Run without -O: exact checks use assertions')

import json
import sympy as s


def data():
    q = s.Rational
    unit = s.eye(4)
    d = s.diag(1, -4, 4, -1)
    a1, a2, a3 = (s.zeros(4) for _ in range(3))
    a1[0, 1], a1[1, 2], a1[2, 3] = 1, -2, 1
    a2[0, 2], a2[1, 3] = 1, -1
    a3[0, 3] = 1
    errors = [unit, d, a1, a1.T, a2, a2.T, a3, a3.T]
    weights = [q(x, 56) for x in [8, 1, 4, 4, 12, 12, 31, 31]]

    def vector(entries):
        z = s.zeros(32, 1)
        for (e, c), value in entries.items():
            z[4*e+c] = value
        return z

    v1 = vector({(0, 0): q(1, 2), (1, 0): -q(1, 8), (3, 1): 1})
    v2 = vector({(0, 0): q(1, 2), (1, 0): q(1, 8), (5, 2): 1})
    v3 = vector({(7, 3): 1})
    v = vector({(0, 2): 2, (1, 2): 1, (2, 1): -2, (3, 3): 1, (4, 0): 3})
    a = vector({(3, 0): 1, (5, 1): -2, (7, 2): 1})
    b = vector({(5, 0): -1, (7, 1): 1})
    z = vector({(7, 0): 1})
    vm = s.Matrix.hstack(v1, v2, v3)
    m = s.Matrix([[16, 8, 29], [8, 64, 77], [29, 77, 251]])
    ld, pivots = m.LDLdecomposition(hermitian=False)
    assert all(pivots[i, i] > 0 for i in range(3))
    assert m == ld*pivots*ld.T
    qmat = vm*m*vm.T + 4*(v*v.T+a*a.T+b*b.T) + 51*z*z.T
    perm, signs = [0, 1, 3, 2, 5, 4, 7, 6], [1, -1, 1, 1, -1, -1, 1, 1]
    reflect = s.zeros(32)
    for e in range(8):
        for c in range(4):
            reflect[4*perm[e]+3-c, 4*e+c] = signs[e]
    assert reflect.T*reflect == s.eye(32)
    h = (qmat + reflect*qmat*reflect.T)/560

    ket0, ket1, ketw = s.zeros(8, 1), s.zeros(8, 1), s.zeros(8, 1)
    ket0[0], ket0[5] = 2, 1
    ket1[2], ket1[7] = 1, 2
    ketw[1], ketw[6] = 1, 1
    rho0 = (ket0*ket0.T+ket1*ket1.T)/10
    rho1 = ketw*ketw.T/2
    t = s.zeros(16, 8)
    for c, entries in enumerate([{0: 1}, {1: 1, 10: q(1, 2)}, {8: 1},
                                {9: 1, 3: -q(1, 2)}, {2: 1, 12: 1},
                                {5: 1, 11: -1}, {4: 1, 14: 2}, {7: 2, 13: -1}]):
        for row, val in entries.items():
            t[row, c] = val
    aa = s.Matrix([[q(1, 2), q(4, 5)], [q(4, 5), 2]])
    bb = s.Matrix([[q(1, 2), -2], [-2, 8]])
    zz = s.diag(1, -1)
    d0 = s.diag(aa, zz*aa*zz, q(2, 5)*s.eye(2), s.eye(2)/10)
    d1 = s.diag(bb, zz*bb*zz, s.eye(2)/2, s.zeros(2))
    return dict(errors=errors, weights=weights, H=h, reflection=reflect, M=m, LDL=ld,
                pivots=pivots, vm=vm, qmat=qmat, vectors=[v, a, b, z],
                rho0=rho0, rho1=rho1, T=t, d0=d0, d1=d1, A=aa, B=bb)


def main():
    d = data()
    errors, weights, h = d['errors'], d['weights'], d['H']

    def channel(x):
        return sum((w*l*x*l.T for l, w in zip(errors, weights)), s.zeros(4))

    def raw_complement(x):
        return s.Matrix(8, 8, lambda e, f: s.trace(errors[e]*x*errors[f].T))

    def referenced(x, phi):
        return s.BlockMatrix([[phi(x[4*r:4*r+4, 4*t:4*t+4])
                               for t in range(2)] for r in range(2)]).as_explicit()

    assert sum((w*l.T*l for l, w in zip(errors, weights)), s.zeros(4)) == s.eye(4)
    assert s.Matrix(8, 8, lambda e, f: sum(h[4*e+c, 4*f+c] for c in range(4))) == s.diag(*weights)
    for i in range(4):
        for j in range(4):
            x = s.zeros(4); x[i, j] = 1
            lhs = sum(((errors[f].T*errors[e])[j, i]*h[4*e:4*e+4, 4*f:4*f+4]
                       for e in range(8) for f in range(8)), s.zeros(4))
            assert lhs == channel(x).T

    rho0, rho1 = d['rho0'], d['rho1']
    assert s.trace(rho0) == s.trace(rho1) == 1
    projector = 2*rho0+rho1
    assert projector*projector == projector
    for l in errors[1:]:
        assert projector*s.kronecker_product(s.eye(2), l)*projector == s.zeros(8)
    for rho in [rho0, rho1]:
        assert s.Matrix(2, 2, lambda i, j: s.trace(rho[4*i:4*i+4, 4*j:4*j+4])) == s.eye(2)/2
    assert s.trace(referenced(rho0, channel)*rho1) == 0
    assert s.trace(referenced(rho1, channel)*rho1) == s.Rational(1, 7)

    raw0, raw1 = [referenced(rho, raw_complement) for rho in [rho0, rho1]]
    assert raw0 == d['T']*d['d0']*d['T'].T
    assert raw1 == d['T']*d['d1']*d['T'].T
    vv = s.Matrix([7, 13])
    assert s.Rational(205, 9)*d['A']-d['B'] == s.Rational(2, 9)*vv*vv.T
    assert d['T'].rank() == 8 and raw0.rank() == 8 and raw1.rank() == 4
    eps0, eps1 = [raw[:8, :8]+raw[8:, 8:] for raw in [raw0, raw1]]
    assert eps0 == s.diag(1, 4, s.Rational(9, 10), s.Rational(9, 10), s.Rational(1, 2), s.Rational(1, 2), s.Rational(2, 5), s.Rational(2, 5))
    assert eps1 == s.diag(1, 16, s.Rational(5, 2), s.Rational(5, 2), s.Rational(1, 2), s.Rational(1, 2), 0, 0)
    assert all((4*eps0-eps1)[i, i] >= 0 for i in range(8))
    # Negative controls distinguish the full environmental constants from smaller,
    # unjustified replacements. Noncommuting blocks cannot share an eigenbasis.
    sharp = s.Matrix([13, -7])
    assert (s.Rational(205, 9)*d['A']-d['B'])*sharp == s.zeros(2, 1)
    assert (sharp.T*(22*d['A']-d['B'])*sharp)[0] == -s.Rational(287, 10)
    assert (3*eps0-eps1)[1, 1] == -4
    assert d['A']*d['B'] != d['B']*d['A']

    p, ln2 = s.symbols('p ln2', real=True)
    kappa, click = (27+169*p)/9, (1-p)/7
    t = 8*click*ln2/(3*kappa)
    rate = click*t/2-3*kappa*t**2/(32*ln2)
    assert s.factor(rate-6*ln2*(1-p)**2/(49*(27+169*p))) == 0
    assert s.factor(rate.subs(p, s.Rational(1, 2))-3*ln2/10927) == 0
    assert rate.subs(p, 1) == 0
    assert not any(m.has(s.Float) for m in [*errors, h, raw0, raw1, rate])
    print(json.dumps({'status':'passed','kraus_trace_preservation':True,
        'positive_simulator_LDL_pivots':[str(d['pivots'][i,i]) for i in range(3)],
        'simulator_partial_trace':True,'all_16_matrix_unit_simulations':True,
        'all_seven_error_detection_identities':True,'helper_marginals':True,
        'click_probabilities':['0','1/7'],'full_unweighted_environment_blocks':True,
        'environment_ranks':[8,4],'domination_constants':['205/9','4'],
        'negative_controls':{'constant_22_fails':True,'constant_3_fails_reduced':True,
            'environment_blocks_do_not_commute':True,'p_equals_one_rate_is_zero':True},
        'rate_parameter_substitution':True,'half_erasure_bound':'3*ln(2)/10927',
        'scope':'Independent exact algebra; not a Lean proof or operational coding theorem.'},indent=2))


if __name__ == '__main__':
    main()
