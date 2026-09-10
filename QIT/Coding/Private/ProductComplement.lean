/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team, Chengkai Zhu
-/

module
public import QIT.Coding.Private.Basic

/-! # Tensor products of explicit Kraus complements -/

@[expose] public section
namespace QIT
noncomputable section
universe u v
variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

section ProdKraus

universe uK uL uC uD

variable {κ : Type uK} {ι : Type uL} [Fintype κ] [DecidableEq κ]
variable [Fintype ι] [DecidableEq ι]
variable {c : Type uC} {d : Type uD}
variable [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]

omit [DecidableEq κ] [DecidableEq ι] in
/-- The product of two Kraus channels is the Kraus channel of the
pairwise Kronecker family `K_k ⊗ L_l` (the pairwise-Kraus bookkeeping of
paper eq:complement applied to products). -/
theorem kron_ofKraus (K : κ → Matrix b a Complex) (L : ι → Matrix d c Complex) :
    MatrixMap.kron (MatrixMap.ofKraus K) (MatrixMap.ofKraus L)
      = MatrixMap.ofKraus (fun kl : κ × ι => Matrix.kronecker (K kl.1) (L kl.2)) := by
  apply LinearMap.ext
  intro X
  rw [MatrixMap.map_eq_sum_single _ X, MatrixMap.map_eq_sum_single (MatrixMap.ofKraus _) X]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  congr 1
  rcases p with ⟨i, j⟩
  rcases q with ⟨i', j'⟩
  rw [single_prod_eq_kronecker_single, MatrixMap.kron_apply_kronecker]
  change Matrix.kronecker (∑ k, K k * Matrix.single i i' (1 : ℂ) * (K k).conjTranspose)
      (∑ l, L l * Matrix.single j j' (1 : ℂ) * (L l).conjTranspose) =
    ∑ kl : κ × ι, Matrix.kronecker (K kl.1) (L kl.2) *
      Matrix.kronecker (Matrix.single i i' (1 : ℂ)) (Matrix.single j j' (1 : ℂ)) *
      (Matrix.kronecker (K kl.1) (L kl.2)).conjTranspose
  simp only [Matrix.kronecker, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul]
  ext r s
  simp only [Matrix.kroneckerMap_apply, Matrix.sum_apply, Finset.sum_mul,
    Finset.mul_sum, Fintype.sum_prod_type]
  rw [Finset.sum_comm]

omit [DecidableEq b] [DecidableEq d] in
/-- The complement of a product of Kraus channels is the complementary
channel of the pairwise Kronecker family — the complement-side half of
the pairwise-Kraus bookkeeping (paper eq:complement for products). -/
theorem kron_complementOfKraus (K : κ → Matrix b a Complex) (L : ι → Matrix d c Complex) :
    MatrixMap.kron (MatrixMap.complementOfKraus K) (MatrixMap.complementOfKraus L)
      = MatrixMap.complementOfKraus
          (fun kl : κ × ι => Matrix.kronecker (K kl.1) (L kl.2)) := by
  rw [MatrixMap.complementOfKraus_eq_ofKraus, MatrixMap.complementOfKraus_eq_ofKraus,
    MatrixMap.complementOfKraus_eq_ofKraus, kron_ofKraus]
  rfl

end ProdKraus

section ProductChannels

variable {c d e f : Type*}
variable [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
variable [Fintype e] [DecidableEq e] [Fintype f] [DecidableEq f]

/-- Taking full Kraus complements commutes with taking products of channels. -/
theorem Channel.IsComplementOf.prod
    {N : Channel a b} {Nc : Channel a e} {M : Channel c d} {Mc : Channel c f}
    (hN : Channel.IsComplementOf Nc N) (hM : Channel.IsComplementOf Mc M) :
    Channel.IsComplementOf (Nc.prod Mc) (N.prod M) := by
  obtain ⟨K, hK, hKc⟩ := hN
  obtain ⟨L, hL, hLc⟩ := hM
  refine ⟨fun ef : e × f => Matrix.kronecker (K ef.1) (L ef.2), ?_, ?_⟩
  · change MatrixMap.kron N.map M.map = _
    rw [hK, hL, kron_ofKraus]
  · change MatrixMap.kron Nc.map Mc.map = _
    rw [hKc, hLc, kron_complementOfKraus]

end ProductChannels

end
end QIT
