#!/usr/bin/env python3
"""Generate exact encoding proof aids; every certificate is kernel checked in Lean."""

from pathlib import Path
import sympy as s
from check_transition_channel import data
from generate_transition_data import mat, vec


def main():
    d = data()
    gg = s.zeros(8, 6)
    gg[0, 0], gg[1, 0], gg[2, 1], gg[3, 1] = 7, 13, 7, -13
    for i in range(4):
        gg[4+i, 2+i] = 1
    coeff = [s.Rational(2, 9)]*2 + [s.Rational(155, 18)]*2 + [s.Rational(41, 18)]*2
    assert s.Rational(205, 9)*d['d0']-d['d1'] == gg*s.diag(*coeff)*gg.T
    out = '''/-
Copyright (c) 2026 Chengkai Zhu.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chengkai Zhu
-/

module
public import QIT.Coding.Private.TransitionChannelData

/-! # Exact rational certificates for the new encoding and full environment

Vectors below are unnormalized: division by 10 and 2 reconstructs the density
operators in the paper without placing square roots in finite proof certificates.
-/

@[expose] public section
namespace QIT.TransitionEncodingData
open TransitionData

def inputFlat (x : Fin 2 × Fin 4) : Fin 8 := ⟨4 * x.1.val + x.2.val, by omega⟩
def envFlat (x : Fin 2 × Fin 8) : Fin 16 := ⟨8 * x.1.val + x.2.val, by omega⟩
def v0 (x : Fin 2 × Fin 4) : ℚ := ![2, 0, 0, 0, 0, 1, 0, 0] (inputFlat x)
def v1 (x : Fin 2 × Fin 4) : ℚ := ![0, 0, 1, 0, 0, 0, 0, 2] (inputFlat x)
def vw (x : Fin 2 × Fin 4) : ℚ := ![0, 1, 0, 0, 0, 0, 1, 0] (inputFlat x)
def rho (b : Bool) (x y : Fin 2 × Fin 4) : ℚ :=
  if b then vw x * vw y / 2 else (v0 x * v0 y + v1 x * v1 y) / 10

def bob (b : Bool) (x y : Fin 2 × Fin 4) : ℚ :=
  ∑ e : Fin 8, weights e * ∑ i : Fin 4, ∑ j : Fin 4,
    errors e x.2 i * rho b (x.1, i) (y.1, j) * errors e y.2 j

def env (b : Bool) (x y : Fin 2 × Fin 8) : ℚ :=
  ∑ i : Fin 4, ∑ j : Fin 4, rho b (x.1, i) (y.1, j) *
    ∑ k : Fin 4, errors y.2 k j * errors x.2 k i

'''
    out += 'def supportTable : Matrix (Fin 16) (Fin 8) ℚ :=\n  '+mat(d['T'])+'\n\n'
    out += 'def blockTable : Bool → Matrix (Fin 8) (Fin 8) ℚ :=\n  fun b ↦ if b then\n  '+mat(d['d1'])+'\n  else\n  '+mat(d['d0'])+'\n\n'
    out += 'def orderGramTable : Matrix (Fin 16) (Fin 6) ℚ :=\n  '+mat(d['T']*gg)+'\n\n'
    out += 'def orderWeights : Fin 6 → ℚ :=\n  '+vec(coeff)+'\n\n'
    out += 'def epsilonDiag : Bool → Fin 8 → ℚ :=\n  fun b ↦ if b then\n    '+vec([1,16,s.Rational(5,2),s.Rational(5,2),s.Rational(1,2),s.Rational(1,2),0,0])+'\n  else\n    '+vec([1,4,s.Rational(9,10),s.Rational(9,10),s.Rational(1,2),s.Rational(1,2),s.Rational(2,5),s.Rational(2,5)])+'\n\n'
    out += '''set_option maxRecDepth 10000
set_option maxHeartbeats 30000000

theorem rho_trace (b : Bool) : (∑ x : Fin 2 × Fin 4, rho b x x) = 1 := by
  revert b
  decide +kernel

theorem signal_projector (x y : Fin 2 × Fin 4) :
    (∑ z : Fin 2 × Fin 4, rho true x z * rho true z y) = rho true x y := by
  revert x y
  decide +kernel

theorem helper_marginal (b : Bool) (r s : Fin 2) :
    (∑ i : Fin 4, rho b (r, i) (s, i)) = if r = s then 1 / 2 else 0 := by
  revert b r s
  decide +kernel

theorem event (b : Bool) :
    (∑ x : Fin 2 × Fin 4, ∑ y : Fin 2 × Fin 4, bob b x y * rho true y x) =
      if b then 1 / 7 else 0 := by
  revert b
  decide +kernel

theorem environment_blocks (b : Bool) (x y : Fin 2 × Fin 8) :
    env b x y = ∑ i : Fin 8, ∑ j : Fin 8,
      supportTable (envFlat x) i * blockTable b i j * supportTable (envFlat y) j := by
  revert b x y
  decide +kernel

theorem order_gram (x y : Fin 2 × Fin 8) :
    (205 / 9) * env false x y - env true x y =
      ∑ k : Fin 6, orderWeights k * orderGramTable (envFlat x) k * orderGramTable (envFlat y) k := by
  revert x y
  decide +kernel

theorem orderWeights_nonneg (k : Fin 6) : 0 ≤ orderWeights k := by
  revert k
  decide +kernel

theorem epsilon_diagonal (b : Bool) (e f : Fin 8) :
    (∑ r : Fin 2, env b (r, e) (r, f)) = if e = f then epsilonDiag b e else 0 := by
  revert b e f
  decide +kernel

theorem epsilon_order (e : Fin 8) : 0 ≤ 4 * epsilonDiag false e - epsilonDiag true e := by
  revert e
  decide +kernel

end QIT.TransitionEncodingData
'''
    target = Path('QIT/Coding/Private/TransitionEncodingData.lean')
    target.write_text(out)
    print(target)


if __name__ == '__main__':
    main()
