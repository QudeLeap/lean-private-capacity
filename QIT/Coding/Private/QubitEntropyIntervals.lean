/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team, Chengkai Zhu
-/

module

public import QIT.Information.Entropy.EntropyTensorPower
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Analytic basis for finite entropy certificates

Rational interval arithmetic can bound the eigenvalue contributions without
assuming monotonicity of −x log x across its maximum. Logarithms use a proved
finite atanh series remainder; spectral roots use the intermediate value theorem.
These lemmas do not assume the new example's numerical entropy bounds.
-/

@[expose] public section
open scoped ComplexOrder MatrixOrder
namespace QIT.QubitActivation
noncomputable section
open Finset Polynomial

def logPartial (z : ℝ) (n : ℕ) : ℝ :=
  2 * ∑ i ∈ range n, z ^ (2 * i + 1) / (2 * i + 1)

def logError (z : ℝ) (n : ℕ) : ℝ := 2 * (z ^ (2 * n + 1) / (1 - z ^ 2))

/-- A conservative, finite rational remainder from mathlib's logarithm series. -/
theorem log_atanh_interval (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z < 1) (n : ℕ) :
    logPartial z n ≤ Real.log ((1 + z) / (1 - z)) ∧
      Real.log ((1 + z) / (1 - z)) ≤ logPartial z n + logError z n := by
  have hlo := Real.sum_range_le_log_div hz0 hz1 n
  have hhi := Real.log_div_le_sum_range_add hz0 hz1 n
  dsimp [logPartial, logError]
  constructor <;> linarith

/-- Range reduction x ↦ 2ⁿx, with an independently supplied interval for ln 2. -/
theorem log_scaled_interval (x : ℝ) (hx : 0 < x) (k n : ℕ) (z : ℝ)
    (hz0 : 0 ≤ z) (hz1 : z < 1)
    (hz : (1 + z) / (1 - z) = 2 ^ k * x)
    (l2 u2 : ℝ) (hl2 : l2 ≤ Real.log 2) (hu2 : Real.log 2 ≤ u2) :
    logPartial z n - k * u2 ≤ Real.log x ∧
      Real.log x ≤ logPartial z n + logError z n - k * l2 := by
  have h := log_atanh_interval z hz0 hz1 n
  rw [hz, Real.log_mul (pow_pos (by norm_num : (0 : ℝ) < 2) k).ne' hx.ne',
    Real.log_pow] at h
  have hlo := mul_le_mul_of_nonneg_left hl2 (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  have hhi := mul_le_mul_of_nonneg_left hu2 (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  constructor <;> linarith [h.1, h.2]

/-- Certified logarithm endpoint bounds bound a whole entropy summand interval. -/
theorem entropy_term_interval {x a b la ub l2 u2 : ℝ}
    (ha : 0 < a) (hax : a ≤ x) (hxb : x ≤ b) (hb : b ≤ 1)
    (hla : la ≤ Real.log a) (hub : Real.log b ≤ ub) (hu : ub ≤ 0)
    (hl2 : 0 < l2) (hl2log : l2 ≤ Real.log 2) (hu2log : Real.log 2 ≤ u2) :
    a * (-ub) / u2 ≤ -xlog2 x ∧ -xlog2 x ≤ b * (-la) / l2 := by
  have hx := ha.trans_le hax
  have hbpos := hx.trans_le hxb
  have hlogpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hu2 : 0 < u2 := hlogpos.trans_le hu2log
  have hlogax := Real.log_le_log ha hax
  have hlogxb := Real.log_le_log hx hxb
  have hlognonpos : Real.log x ≤ 0 := Real.log_nonpos hx.le (hxb.trans hb)
  have hlower : a * (-ub) ≤ x * (-Real.log x) :=
    mul_le_mul hax (by linarith) (by linarith) hx.le
  have hupper : x * (-Real.log x) ≤ b * (-la) :=
    mul_le_mul hxb (by linarith) (by linarith) hbpos.le
  have hid : -xlog2 x = x * (-Real.log x) / Real.log 2 := by
    simp [xlog2, hx.ne', log2]
    ring
  rw [hid]
  constructor
  · exact (div_le_div_iff₀ hu2 hlogpos).mpr (by
      nlinarith [mul_nonneg (sub_nonneg.mpr hu2log)
        (mul_nonneg ha.le (neg_nonneg.mpr hu))])
  · exact (div_le_div_iff₀ hlogpos hl2).mpr (by
      nlinarith [mul_nonneg (sub_nonneg.mpr hl2log)
        (mul_nonneg hx.le (neg_nonneg.mpr hlognonpos))])

/-- Exact zero eigenvalues contribute zero; no logarithm at a singular point is needed. -/
theorem entropy_zero_term : -xlog2 0 = 0 := by simp [xlog2]

/-- Opposite endpoint signs certify a real root in a closed interval. -/
theorem polynomial_root_in_interval (p : ℝ[X]) (a b : ℝ) (hab : a ≤ b)
    (hsign : (p.eval a ≤ 0 ∧ 0 ≤ p.eval b) ∨ (p.eval b ≤ 0 ∧ 0 ≤ p.eval a)) :
    ∃ x ∈ Set.Icc a b, p.eval x = 0 := by
  rcases hsign with h | h
  · exact intermediate_value_Icc hab p.continuous.continuousOn h
  · exact intermediate_value_Icc' hab p.continuous.continuousOn h

/-- A complete set of distinct certified roots exhausts a degree-n polynomial. -/
theorem polynomial_roots_complete {n : ℕ} (p : ℝ[X]) (hp : p ≠ 0)
    (hdegree : p.natDegree ≤ n) (roots : Fin n → ℝ)
    (hinj : Function.Injective roots) (hroot : ∀ i, p.eval (roots i) = 0) :
    p.roots = Multiset.map roots Finset.univ.val := by
  have hnd : (Multiset.map roots Finset.univ.val).Nodup :=
    Finset.univ.nodup.map hinj
  have hle : Multiset.map roots Finset.univ.val ≤ p.roots := by
    apply (Multiset.le_iff_subset hnd).mpr
    intro x hx
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hx
    exact (Polynomial.mem_roots hp).mpr (hroot i)
  apply (Multiset.eq_of_le_of_card_le hle ?_).symm
  simpa using (Polynomial.card_roots' p).trans hdegree

/-- Translate an exact real characteristic-polynomial root list into entropy. -/
theorem entropy_of_charpoly_roots {a : Type*} [Fintype a] [DecidableEq a]
    (rho : State a) (p : ℝ[X]) (roots : Multiset ℝ)
    (hchar : rho.matrix.charpoly = p.map Complex.ofRealHom)
    (hroots : p.roots = roots) (hcard : roots.card = p.natDegree) :
    rho.vonNeumann = -((roots.map xlog2).sum) := by
  have hmap := Polynomial.roots_map_of_injective_of_card_eq_natDegree
    (p := p) (f := Complex.ofRealHom) Complex.ofReal_injective (hroots ▸ hcard)
  have hspec : eigenvalueMultiset rho.pos.isHermitian = roots := by
    apply Multiset.map_injective (f := Complex.ofReal) Complex.ofReal_injective
    rw [hroots] at hmap
    change Multiset.map Complex.ofReal roots = (p.map Complex.ofRealHom).roots at hmap
    rw [hmap, ← hchar, rho.pos.isHermitian.roots_charpoly_eq_eigenvalues]
    simp [eigenvalueMultiset, Multiset.map_map]
  rw [State.vonNeumann_eq_neg_sum_eigenvalueMultiset, hspec]

theorem eigenvalueMultiset_fromBlocks {a b : Type*}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (A : CMatrix a) (B : CMatrix b) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hM : (Matrix.fromBlocks A 0 0 B).IsHermitian) :
    eigenvalueMultiset hM = eigenvalueMultiset hA + eigenvalueMultiset hB := by
  apply Multiset.map_injective (f := RCLike.ofReal (K := ℂ)) RCLike.ofReal_injective
  simp only [eigenvalueMultiset, Multiset.map_add, Multiset.map_map]
  rw [← hM.roots_charpoly_eq_eigenvalues, ← hA.roots_charpoly_eq_eigenvalues,
    ← hB.roots_charpoly_eq_eigenvalues, Matrix.charpoly_fromBlocks_zero₁₂,
    Polynomial.roots_mul (mul_ne_zero A.charpoly_monic.ne_zero B.charpoly_monic.ne_zero)]

/-- Exact entropy of the flagged half-erasure output, including both unequal-size blocks. -/
theorem vonNeumann_half_blocks {a b : Type*}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (rho : State (a ⊕ b)) (sigma : State a) (epsilon : State b)
    (hmat : rho.matrix = (1 / 2 : ℂ) • Matrix.fromBlocks sigma.matrix 0 0 epsilon.matrix) :
    rho.vonNeumann = 1 + sigma.vonNeumann / 2 + epsilon.vonNeumann / 2 := by
  have hM : (Matrix.fromBlocks sigma.matrix 0 0 epsilon.matrix).IsHermitian := by
    simp [Matrix.IsHermitian, Matrix.fromBlocks_conjTranspose,
      sigma.pos.isHermitian.eq, epsilon.pos.isHermitian.eq]
  have hscaled := eigenvalueMultiset_smul_ofReal (1 / 2 : ℝ)
    (Matrix.fromBlocks sigma.matrix 0 0 epsilon.matrix) hM
  have hmat' : rho.matrix = ((1 / 2 : ℝ) : ℂ) •
      Matrix.fromBlocks sigma.matrix 0 0 epsilon.matrix := by
    norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    exact hmat
  have heq := eigenvalueMultiset_eq_of_eq hmat' rho.pos.isHermitian
    (smul_isHermitian_ofReal (1 / 2 : ℝ) _ hM)
  rw [State.vonNeumann_eq_neg_sum_eigenvalueMultiset, heq, hscaled,
    eigenvalueMultiset_fromBlocks _ _ sigma.pos.isHermitian epsilon.pos.isHermitian hM,
    Multiset.map_add, Multiset.map_add, Multiset.sum_add, Multiset.map_map,
    Multiset.map_map]
  simp only [Function.comp_def]
  rw [State.xlog2_sum_scaled_state_spectrum (1 / 2) sigma (by norm_num),
    State.xlog2_sum_scaled_state_spectrum (1 / 2) epsilon (by norm_num)]
  have hhalf : xlog2 (1 / 2) = -(1 / 2 : ℝ) := by
    norm_num [xlog2, log2, Real.log_div, Real.log_pos one_lt_two |>.ne']
  rw [hhalf, State.vonNeumann_eq_neg_sum_eigenvalueMultiset,
    State.vonNeumann_eq_neg_sum_eigenvalueMultiset]
  ring

end
end QIT.QubitActivation
