/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team, Chengkai Zhu
-/

module

public import QIT.Classical.CQState
public import QIT.Information.Entropy.Holevo
public import QIT.Information.Entropy.MutualInformationDPI
public import QIT.Core.Channel
public import QIT.Core.Map
public import QIT.Coding.Classical.HSW
public import QIT.Coding.Classical.HSWConverse

/-!
# Private capacity foundations

This module introduces the channel-theoretic prerequisites for the paper
"Private-capacity superactivation"
(Zhu--Wang, 2026), the operational setting and eq:capacities:

* `MatrixMap.transposeMap` — the entrywise transpose as a complex-linear map
  (positive but not completely positive in general; it is stored as a
  `MatrixMap`, while the simulator `𝓓` must be a channel).
* `MatrixMap.complementOfKraus` — the complementary channel of a Kraus
  family, `[𝓝ᶜ(X)]_{ℓm} = Tr(K_ℓ X K_m†)`
  (paper eq:complement).
* `Channel.IsComplementOf` — the associated complement predicate.
* Holevo monotonicity under channel postprocessing
  (`Ensemble.holevoInformation_outputEnsemble_le`), the paper's data-processing
  input for the transpose criterion.
* One-block private information `χ(X:B) - χ(X:E)` and the private capacity
  `P(𝓝) = sup_n (1/n) sup_ensemble [χ(X:B^n) - χ(X:E^n)]` (paper
  eq:capacities), regularized in the `sSup`-of-block-rates idiom of
  `Channel.regularizedHolevoInformation`.

Everything here is finite-dimensional; logarithms are base two, matching
`QIT.State.vonNeumann` and `QIT.log2`.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v w uEnsemble

noncomputable section

variable {a : Type u} {b : Type v} {e : Type w}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype e] [DecidableEq e]

namespace MatrixMap

/-! ## The transpose as a linear map

The entrywise transpose is complex-linear (`(c • X)ᵀ = c • Xᵀ` entrywise).
It is not completely positive in dimensions at least two; no complete
positivity is assumed by the `MatrixMap` definition below. -/

/-- The entrywise matrix transpose as a complex-linear matrix map. -/
def transposeMap : MatrixMap a a where
  toFun X := Matrix.transpose X
  map_add' X Y := by
    ext i j
    simp [Matrix.transpose_apply]
  map_smul' r X := by
    ext i j
    simp [Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]

@[simp]
theorem transposeMap_apply (X : CMatrix a) (i j : a) :
    transposeMap X i j = X j i := by
  rfl

/-- The transpose map is an involution. -/
theorem transposeMap_transposeMap (X : CMatrix a) :
    transposeMap (transposeMap X) = X := by
  ext i j
  simp [transposeMap_apply]

end MatrixMap

/-! ## Transposition preserves spectra, hence entropy -/

section TransposeEntropy

omit [Fintype a] [DecidableEq a] in
/-- Positive semidefiniteness is preserved under entrywise transposition.

Roadmap: for `M = B† B` (Cholesky-style characterization of `PosSemidef`),
`Mᵀ = C† C` with `C` the entrywise conjugate of `B`, since
`(B† B)ᵀ = Bᵀ B̄ = (B̄)† (B̄)`.  Alternatively search mathlib for
`Matrix.PosSemidef` transpose lemmas. -/
theorem posSemidef_transpose {M : CMatrix a} (hM : M.PosSemidef) :
    (Matrix.transpose M).PosSemidef := by
  exact hM.transpose

/-- The transposed density matrix, as a state. -/
def State.transpose (ρ : State a) : State a where
  matrix := Matrix.transpose ρ.matrix
  pos := posSemidef_transpose ρ.pos
  trace_eq_one := by
    rw [Matrix.trace_transpose]
    exact ρ.trace_eq_one

omit [Fintype a] [DecidableEq a] in
/-- The transpose of a Hermitian matrix is Hermitian: entrywise,
`(Mᵀ)† i j = conj ((Mᵀ) j i) = conj (M i j) = M j i = Mᵀ i j`
(the last step by Hermiticity `M i j = conj (M j i)`). -/
theorem hermitian_transpose {M : CMatrix a} (hM : M.IsHermitian) :
    (Matrix.transpose M).IsHermitian := by
  exact hM.transpose

/-- Transposition preserves the eigenvalue multiset of a Hermitian matrix.

Roadmap: `Matrix.charpoly_transpose` (already used in
`QIT/Information/Entropy/Entropy.lean`) gives
`(Mᵀ).charpoly = M.charpoly`; Hermitian eigenvalues are the real roots of the
characteristic polynomial with multiplicity, so the (sorted) eigenvalue
vectors coincide.  A mathlib bridge
`Matrix.IsHermitian.eigenvalues`-vs-`charpoly.roots` may need assembling. -/
theorem eigenvalues_hermitian_transpose {M : CMatrix a} (hM : M.IsHermitian) :
    (hermitian_transpose hM).eigenvalues = hM.eigenvalues := by
  exact ((hermitian_transpose hM).eigenvalues_eq_eigenvalues_iff hM).mpr
    (Matrix.charpoly_transpose M)

/-- Von Neumann entropy is invariant under transposition (paper, Section 1:
"Transposition preserves spectra"). -/
theorem State.vonNeumann_transpose (ρ : State a) :
    ρ.transpose.vonNeumann = ρ.vonNeumann := by
  unfold State.vonNeumann
  change -(∑ i, xlog2 ((hermitian_transpose ρ.pos.isHermitian).eigenvalues i)) = _
  rw [eigenvalues_hermitian_transpose]

end TransposeEntropy

/-! ## Complementary channels of a Kraus family -/

namespace MatrixMap

/-- The complementary channel of a Kraus family, in the environment basis:
`[𝓝ᶜ(X)]_{ℓm} = Tr(K_ℓ X K_m†)` (paper eq:complement).  The environment
system is the Kraus index type itself. -/
def complementOfKraus {κ : Type w} [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a Complex) :
    MatrixMap a κ where
  toFun X := fun ℓ m => (K ℓ * X * (K m).conjTranspose).trace
  map_add' X Y := by
    ext ℓ m
    simp [Matrix.mul_add, Matrix.add_mul, Matrix.trace_add, Matrix.add_apply]
  map_smul' r X := by
    ext ℓ m
    simp [Matrix.trace_smul, Matrix.smul_mul, smul_eq_mul]

omit [DecidableEq b] in
@[simp]
theorem complementOfKraus_apply {κ : Type w} [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a Complex) (X : CMatrix a) (ℓ m : κ) :
    complementOfKraus K X ℓ m = (K ℓ * X * (K m).conjTranspose).trace := by
  rfl

omit [DecidableEq b] in
/-- A complement is itself a Kraus map, obtained by exchanging the output
row and the Kraus index. This retains all environment coherences. -/
theorem complementOfKraus_eq_ofKraus {κ : Type w} [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a Complex) :
    complementOfKraus K = ofKraus (fun r : b ↦ fun ℓ i ↦ K ℓ r i) := by
  apply LinearMap.ext
  intro X
  ext ℓ m
  simp [complementOfKraus_apply, ofKraus, Matrix.trace, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.sum_apply]

omit [DecidableEq b] in
/-- The full Kraus-index complement is completely positive. -/
theorem complementOfKraus_completelyPositive {κ : Type w} [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a Complex) : IsCompletelyPositive (complementOfKraus K) := by
  rw [complementOfKraus_eq_ofKraus]
  exact ofKraus_completelyPositive _

end MatrixMap

/-! ## Holevo monotonicity under channel postprocessing

The paper's data-processing input: Holevo information cannot increase when
every ensemble member is postprocessed by a channel.  Route: the Holevo
information of an ensemble equals the mutual information of its cq state
(paper Section 1, `χ({p_x, ω_x})`); mutual information is monotone under local
channels (`QIT.mutualInformation_dataProcessing_local_channels_ge`), and
postprocessing the quantum register is `(idChannel ι).prod D`. -/

section HolevoDPI

variable {ι : Type uEnsemble} [Fintype ι] [DecidableEq ι]

/-- The Holevo information of an ensemble is the mutual information of its
classical-quantum state: `χ(E) = I(X;Q)_{E.cqState}`.  Discharged by the
library's `QIT.cqState_mutualInformation_eq_holevoInformation`
(`QIT/Coding/Classical/HSWConverse.lean:79`), which proves the symmetric
form `I(X;Q) = χ` via the marginal entropy identities
(`cqState_marginalA_vonNeumann`, `State.cqState_vonNeumann`). -/
theorem Ensemble.holevoInformation_eq_mutualInformation_cqState
    (E : Ensemble ι a) :
    E.holevoInformation = QIT.mutualInformation E.cqState :=
  (QIT.cqState_mutualInformation_eq_holevoInformation E).symm

/-- Sending every member of an ensemble through the quantum register of a
product channel `(id ⊗ D)` maps the cq state to the cq state of the output
ensemble. -/
theorem cqState_applyState_prod_id (D : Channel a b) (E : Ensemble ι a) :
    ((Channel.idChannel ι).prod D).applyState E.cqState
      = (D.outputEnsemble E).cqState := by
  apply State.ext
  change ((Channel.idChannel ι).prod D).map E.cqState.matrix = _
  simp only [Ensemble.cqState_matrix, map_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [LinearMap.map_smul_of_tower, Channel.prod_map_kronecker]
  simp [Channel.outputEnsemble, Channel.idChannel, MatrixMap.ofKraus,
    Channel.applyState]

/-- Holevo information is monotone under postprocessing by a channel
(the χ-side of data processing used throughout the paper). -/
theorem Ensemble.holevoInformation_outputEnsemble_le
    (D : Channel a b) (E : Ensemble ι a) :
    (D.outputEnsemble E).holevoInformation ≤ E.holevoInformation := by
  rw [Ensemble.holevoInformation_eq_mutualInformation_cqState,
    Ensemble.holevoInformation_eq_mutualInformation_cqState,
    ← cqState_applyState_prod_id]
  exact QIT.mutualInformation_dataProcessing_local_channels_ge
    E.cqState (Channel.idChannel ι) D

end HolevoDPI

/-! ## One-block private information and the private capacity -/

section PrivateCapacity

variable (N : Channel a b)

/-- `Nc` is (the channel of) a complement of `N`: both arise from one Kraus
family, `N` as the output channel and `Nc` as the complementary channel in
the Kraus-index (environment) basis.  The environment system is the Kraus
index type of the family. -/
def Channel.IsComplementOf (Nc : Channel a e) (N : Channel a b) : Prop :=
  ∃ K : e → Matrix b a Complex,
    N.map = MatrixMap.ofKraus K ∧ Nc.map = MatrixMap.complementOfKraus K

variable {N}

/-- One-block private information of the pair `(N, Nc)` at an ensemble:
`χ(X:B) - χ(X:E)` in paper eq:capacities (single letter). -/
def Channel.privateInformationWith (N : Channel a b) (Nc : Channel a e)
    {ι : Type uEnsemble} [Fintype ι] [DecidableEq ι] (E : Ensemble ι a) : ℝ :=
  (N.outputEnsemble E).holevoInformation
    - (Nc.outputEnsemble E).holevoInformation

/-- All one-block private-information values realized by finite input
ensembles, relative to the complement `Nc`.  Idiom follows
`Channel.holevoInformationValues` (HSW.lean:97). -/
def Channel.privateInformationValues (N : Channel a b) (Nc : Channel a e) :
    Set ℝ :=
  {r : ℝ | ∃ (ι : Type uEnsemble) (instF : Fintype ι) (instD : DecidableEq ι),
    letI : Fintype ι := instF
    letI : DecidableEq ι := instD
    ∃ E : Ensemble ι a, r = N.privateInformationWith Nc E}

/-- The one-block private information (supremum over finite input ensembles),
relative to the complement `Nc`. -/
def Channel.privateInformation (N : Channel a b) (Nc : Channel a e) : ℝ :=
  sSup (Channel.privateInformationValues.{u, v, w, uEnsemble} N Nc)

/-- The block-`n` private information of `n` uses, relative to the
complemented tensor powers. -/
def Channel.blockPrivateInformation (N : Channel a b) (Nc : Channel a e)
    (n : ℕ) : ℝ :=
  Channel.privateInformation.{u, v, w, uEnsemble}
    (N.tensorPower n) (Nc.tensorPower n)

/-- Regularized private-capacity block rates `P^(n)/n`, `n ≥ 1`
(paper eq:capacities, the `sup_{n≥1} (1/n) ...` form; sup-vs-lim is Fekete,
not needed for the zero statements proved here). -/
def Channel.privateCapacityRateValues (N : Channel a b) (Nc : Channel a e) :
    Set ℝ :=
  {R : ℝ | ∃ n : ℕ, 0 < n ∧
    R = Channel.blockPrivateInformation.{u, v, w, uEnsemble} N Nc n / (n : ℝ)}

/-- The private capacity `P(𝓝)` of paper eq:capacities, taken with respect to
the explicit complement `Nc`.

Meaningful use pairs `Nc` with a genuine complement: when
`Channel.IsComplementOf Nc N` holds, the value is the paper's `P(𝓝)` of
eq:capacities; with an arbitrary second channel the expression denotes only
the displayed optimization.  The zero-capacity theorems below fix one
explicit complement, and the superactivation lower bound exhibits one
explicit ensemble, so this caveat never bites there.

Complement independence (any two full complements are related by an
isometry, which leaves Holevo information invariant) is *not* needed for the
results formalized here: the zero statements use one fixed complement, and
the superactivation lower bound exhibits one explicit ensemble.  It is
deferred to the definitional-hygiene pass (no obligation number; not needed
below). -/
def Channel.privateCapacity (N : Channel a b) (Nc : Channel a e) : ℝ :=
  sSup (Channel.privateCapacityRateValues.{u, v, w, uEnsemble} N Nc)

/-- The one-point ensemble putting all weight on a single state.  (HSW's
`singletonEnsemble` is private, so we carry our own.) -/
def Ensemble.constantEnsemble (ρ : State a) : Ensemble PUnit.{uEnsemble + 1} a where
  probs := fun _ => 1
  weights_sum := by simp
  states := fun _ => ρ

/-- The Holevo information of a one-point ensemble is zero. -/
theorem Ensemble.holevoInformation_constantEnsemble (ρ : State a) :
    (Ensemble.constantEnsemble.{u, uEnsemble} ρ).holevoInformation = 0 := by
  rw [Ensemble.holevoInformation_def,
    Ensemble.averageState_of_constant _ ρ (fun _ ↦ rfl)]
  simp [Ensemble.constantEnsemble]

/-- The private information of a one-point (constant) ensemble is zero, so
the optimized value set is nonempty and contains `0`. -/
theorem Channel.privateInformationWith_constant_eq_zero
    (N : Channel a b) (Nc : Channel a e) (ρ : State a) :
    N.privateInformationWith Nc (Ensemble.constantEnsemble ρ) = 0 := by
  change (Ensemble.constantEnsemble (N.applyState ρ)).holevoInformation -
    (Ensemble.constantEnsemble (Nc.applyState ρ)).holevoInformation = 0
  rw [Ensemble.holevoInformation_constantEnsemble,
    Ensemble.holevoInformation_constantEnsemble, sub_self]

end PrivateCapacity

end

end QIT
