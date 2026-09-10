#!/usr/bin/env python3
"""Generate rational proof aids from the explicitly entered manuscript matrices.

Every generated identity is proved again in Lean; no Python result is trusted.
"""

from pathlib import Path
from check_transition_channel import data
import sympy as s


def scalar(x):
    x = s.Rational(x)
    return str(x.p) if x.q == 1 else f'({x.p} / {x.q})'


def vec(xs):
    return '![' + ', '.join(scalar(x) for x in xs) + ']'


def mat(m):
    return '![' + ',\n    '.join(vec(m.row(i)) for i in range(m.rows)) + ']'


def main():
    d = data()
    ff = s.Matrix.hstack(d['vm']*d['LDL'], *d['vectors'])
    ff = s.Matrix.hstack(ff, d['reflection']*ff)
    ww = [s.Rational(x, 560) for x in [16, 60, s.Rational(400, 3), 4, 4, 4, 51]]*2
    assert ff*s.diag(*ww)*ff.T == d['H']
    out = '''/-
Copyright (c) 2026 Chengkai Zhu.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chengkai Zhu
-/

module
public import QIT.Coding.Private.Basic

/-!
# Rational data for the transition-channel construction

Generated from the explicitly entered matrices in `private_superactivation.tex`.
These tables are proof aids. The equalities below are checked by Lean, and the
channel and simulator modules connect them to their complex physical operators.
-/

@[expose] public section
namespace QIT.TransitionData

'''
    out += 'def errors : Fin 8 → Matrix (Fin 4) (Fin 4) ℚ :=\n  !['
    out += ',\n   '.join(mat(m) for m in d['errors']) + ']\n\n'
    out += 'def weights : Fin 8 → ℚ :=\n  ' + vec(d['weights']) + '\n\n'
    out += 'def hTable : Matrix (Fin 32) (Fin 32) ℚ :=\n  ' + mat(d['H']) + '\n\n'
    out += 'def gramTable : Matrix (Fin 32) (Fin 14) ℚ :=\n  ' + mat(ff) + '\n\n'
    out += 'def gramWeights : Fin 14 → ℚ :=\n  ' + vec(ww) + '\n\n'
    out += '''def flat (x : Fin 8 × Fin 4) : Fin 32 := ⟨4 * x.1.val + x.2.val, by omega⟩

def h (x y : Fin 8 × Fin 4) : ℚ := hTable (flat x) (flat y)
def gram (k : Fin 14) (x : Fin 8 × Fin 4) : ℚ := gramTable (flat x) k

theorem weights_pos (e : Fin 8) : 0 < weights e := by
  fin_cases e <;> norm_num [weights]

theorem gramWeights_nonneg (k : Fin 14) : 0 ≤ gramWeights k := by
  fin_cases k <;> norm_num [gramWeights]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 10000000 in
theorem completeness (i j : Fin 4) :
    (∑ e : Fin 8, weights e * ∑ k : Fin 4, errors e k i * errors e k j) =
      if i = j then 1 else 0 := by
  revert i j
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 30000000 in
theorem h_gram (e f : Fin 8) (i j : Fin 4) :
    h (e, i) (f, j) = ∑ k : Fin 14, gramWeights k * gram k (e, i) * gram k (f, j) := by
  revert e f i j
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 10000000 in
theorem h_partialTrace (e f : Fin 8) :
    (∑ i : Fin 4, h (e, i) (f, i)) = if e = f then weights e else 0 := by
  revert e f
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 30000000 in
theorem simulation (i j r t : Fin 4) :
    (∑ e : Fin 8, ∑ f : Fin 8,
      (∑ k : Fin 4, errors f k j * errors e k i) * h (e, r) (f, t)) =
      ∑ e : Fin 8, weights e * errors e t i * errors e r j := by
  revert i j r t
  decide +kernel

end QIT.TransitionData
'''
    path = Path('QIT/Coding/Private/TransitionChannelData.lean')
    path.write_text(out)
    print(path)


if __name__ == '__main__':
    main()
