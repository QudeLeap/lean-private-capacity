/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team, Chengkai Zhu
-/

module

public import QIT.Coding.Private.Basic
public import QIT.Channels.Diamond
public import QIT.Util.Matrix

/-!
# The transpose-simulator criterion for zero private capacity

This module formalizes the elementary background criterion of the paper
"Private-capacity superactivation and complete information comparison"
(Zhu--Wang, 2026), Section 1, paragraph "An elementary background criterion",
together with its antidegradable sibling:

* if a channel `𝓝` admits a *transpose simulator* — a genuine channel `𝓓`
  with `𝓓 ∘ 𝓝ᶜ = 𝖳 ∘ 𝓝` — then `P(𝓝) = 0` at every block length
  (paper eq:transpose-criterion; the mechanism behind thm:private), and
* if `𝓝` is antidegradable — `𝓓 ∘ 𝓝ᶜ = 𝓝` for some channel `𝓓` — then
  `P(𝓝) = 0` (used for the half-erasure channel in Section 2).

The information-theoretic mechanism (paper Section 1): for every block
length `n` and every input ensemble `E`,

  χ(X : B^n) = χ(transpose of the B-side output ensemble)      (transposition
                                                               preserves spectra)
             = χ(X : 𝓓^{⊗n}(E^n-side output))                   (tensorized
                                                               simulator)
             ≤ χ(X : E^n-side output)                           (Holevo data
                                                               processing),

so every block private information is nonpositive, while the constant
ensemble realizes the value `0`; hence every block rate is exactly `0` and
the regularized supremum (paper eq:capacities) is `0`.

The entropy and constant-ensemble bridges in `QIT.Coding.Private.Basic`
are proved. The generic criteria below depend only on the standard Lean
axioms, including their tensorization and entropy dependencies. This
concerns the regularized information formula; the operational coding
theorem is outside this module.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v w uEnsemble

noncomputable section

variable {a : Type u} {b : Type v} {e : Type w}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype e] [DecidableEq e]

/-! ## Kronecker products and the transpose

Entrywise identities for the matrix Kronecker product under transposition.
The transpose of a Kronecker product is the Kronecker product of the
transposes — the matrix identity behind "the global transpose of `n` uses
factors is the factorwise transpose" (paper Section 1). -/

omit [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] in
/-- The entrywise transpose of a Kronecker product is the Kronecker product
of the transposes: `(X ⊗ Y)ᵀ = Xᵀ ⊗ Yᵀ`.

Entrywise, both sides at `((i,k),(j,l))` read `X j i * Y l k`. -/
theorem kronecker_transpose (X : CMatrix a) (Y : CMatrix b) :
    Matrix.transpose (Matrix.kronecker X Y) =
      Matrix.kronecker (Matrix.transpose X) (Matrix.transpose Y) := by
  ext p q
  rcases p with ⟨i, k⟩
  rcases q with ⟨j, l⟩
  simp only [Matrix.transpose_apply, Matrix.kronecker, Matrix.kroneckerMap_apply]

/-- `MatrixMap.transposeMap` (of `QIT.Coding.Private.Basic`) distributes over
Kronecker products of matrices. -/
theorem MatrixMap.transposeMap_kronecker (X : CMatrix a) (Y : CMatrix b) :
    MatrixMap.transposeMap (Matrix.kronecker X Y) =
      Matrix.kronecker (MatrixMap.transposeMap X) (MatrixMap.transposeMap Y) := by
  ext p q
  rcases p with ⟨i, k⟩
  rcases q with ⟨j, l⟩
  simp only [MatrixMap.transposeMap_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply]

/-- The Kronecker product of the transpose map with itself *is* the global
transpose on the product system: `𝖳 ⊗ 𝖳 = 𝖳`.

This is the bridge that turns the tensorized simulator recursion into the
*global* transpose of the block output (paper Section 1).  Proof: both maps
are linear and agree on product matrix units, where
`single_prod_eq_kronecker_single` identifies the unit with a Kronecker
product of units and `MatrixMap.transposeMap_kronecker` applies. -/
theorem MatrixMap.kron_transposeMap_apply (X : CMatrix (Prod a b)) :
    MatrixMap.kron (MatrixMap.transposeMap : MatrixMap a a)
        (MatrixMap.transposeMap : MatrixMap b b) X
      = MatrixMap.transposeMap X := by
  rw [MatrixMap.map_eq_sum_single
      (MatrixMap.kron MatrixMap.transposeMap MatrixMap.transposeMap) X,
    MatrixMap.map_eq_sum_single MatrixMap.transposeMap X]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun p' _ => ?_
  rcases p with ⟨i, j⟩
  rcases p' with ⟨i', j'⟩
  rw [single_prod_eq_kronecker_single i i' j j',
    MatrixMap.kron_apply_kronecker, MatrixMap.transposeMap_kronecker]

/-! ## Entrywise transposition of ensembles -/

section TransposeEnsemble

variable {ι : Type uEnsemble} [Fintype ι] [DecidableEq ι]

/-- The ensemble obtained by transposing every member state; the
probability weights are unchanged (paper Section 1: the transpose image of
an output ensemble). -/
def Ensemble.transposeEnsemble (E : Ensemble ι a) : Ensemble ι a where
  probs := E.probs
  weights_sum := E.weights_sum
  states := fun x => (E.states x).transpose

omit [DecidableEq ι] in
/-- Transposing every member state transposes the average state —
`transposeMap` is linear, so it commutes with the convex combination. -/
theorem Ensemble.averageState_transposeEnsemble (E : Ensemble ι a) :
    E.transposeEnsemble.averageState = E.averageState.transpose := by
  apply State.ext
  show (∑ i, (E.probs i) • Matrix.transpose (E.states i).matrix)
      = Matrix.transpose (∑ i, (E.probs i) • (E.states i).matrix)
  ext j k
  simp only [Matrix.transpose_apply, Matrix.sum_apply, Matrix.smul_apply]

omit [DecidableEq ι] in
/-- Transposition preserves spectra (paper Section 1), hence the Holevo
information of the entrywise-transposed ensemble equals that of the
original: `χ({p_x, ρ_xᵀ}) = χ({p_x, ρ_x})`.

Proof: unfold `holevoInformation` (`Ensemble.holevoInformation_def`),
rewrite the average state with
`Ensemble.averageState_transposeEnsemble`, and cancel the two entropy
invariances `State.vonNeumann_transpose` (of `Basic`, obligation M2-3)
term by term. -/
theorem Ensemble.holevoInformation_transpose (E : Ensemble ι a) :
    E.transposeEnsemble.holevoInformation = E.holevoInformation := by
  rw [Ensemble.holevoInformation_def, Ensemble.holevoInformation_def,
    Ensemble.averageState_transposeEnsemble, State.vonNeumann_transpose]
  congr 1
  show ∑ x, (E.probs x).toReal * ((E.states x).transpose).vonNeumann
      = ∑ x, (E.probs x).toReal * (E.states x).vonNeumann
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [State.vonNeumann_transpose]

end TransposeEnsemble

/-! ## Tensorized simulators

The simulator hypothesis `𝓓 ∘ 𝓝ᶜ = 𝖳 ∘ 𝓝` tensorizes: `𝓓^{⊗n} ∘
(𝓝ᶜ)^{⊗n} = 𝖳 ∘ 𝓝^{⊗n}` on the full `n`-fold tensor-power systems, by
induction on the repo's `Channel.tensorPower` recursion
`tensorPower 0 = unit`, `tensorPower (n+1) = Φ.prod (tensorPower n)`. -/

/-- The tensorized transpose simulator at the matrix-map level: if `𝓓 ∘ 𝓝ᶜ
= 𝖳 ∘ 𝓝` entrywise, then for every block length `n`,
`𝓓^{⊗n}((𝓝ᶜ)^{⊗n}(X)) = 𝖳(𝓝^{⊗n}(X))` for every matrix `X` on the `n`-fold
tensor-power input system.

The induction step composes `MatrixMap.kron_comp_apply_general` (of
`QIT.Channels.Diamond`, twice), the simulator hypothesis, and the
global-transpose bridge `MatrixMap.kron_transposeMap_apply`. -/
theorem Channel.tensorPower_simulator_transpose
    (N : Channel a b) (Nc : Channel a e) (D : Channel e b)
    (hsim : ∀ X : CMatrix a, D.map (Nc.map X) = MatrixMap.transposeMap (N.map X)) :
    ∀ (n : ℕ) (X : CMatrix (QIT.TensorPower a n)),
      (D.tensorPower n).map ((Nc.tensorPower n).map X)
        = MatrixMap.transposeMap ((N.tensorPower n).map X) := by
  intro n
  induction n with
  | zero =>
    intro X
    ext i j
    rfl
  | succ n ih =>
    intro X
    rw [Channel.tensorPower_succ D n, Channel.tensorPower_succ Nc n,
      Channel.tensorPower_succ N n]
    show MatrixMap.kron D.map (D.tensorPower n).map
        (MatrixMap.kron Nc.map (Nc.tensorPower n).map X)
      = MatrixMap.transposeMap
        (MatrixMap.kron N.map (N.tensorPower n).map X)
    rw [MatrixMap.kron_comp_apply_general]
    have h1 : D.map.comp Nc.map = MatrixMap.transposeMap.comp N.map := by
      apply LinearMap.ext
      intro Y
      rw [LinearMap.comp_apply, LinearMap.comp_apply]
      exact hsim Y
    have h2 : (D.tensorPower n).map.comp (Nc.tensorPower n).map
        = MatrixMap.transposeMap.comp (N.tensorPower n).map := by
      apply LinearMap.ext
      intro Y
      rw [LinearMap.comp_apply, LinearMap.comp_apply]
      exact ih Y
    rw [h1, h2, ← MatrixMap.kron_comp_apply_general,
      MatrixMap.kron_transposeMap_apply]

/-- The tensorized antidegradability hypothesis at the matrix-map level: if
`𝓓 ∘ 𝓝ᶜ = 𝓝`, then `𝓓^{⊗n} ∘ (𝓝ᶜ)^{⊗n} = 𝓝^{⊗n}` for every block length
`n` (paper Section 2, the half-erasure channel's route to `P = 0`).

The induction step composes `MatrixMap.kron_comp_apply_general` with the
antidegradability hypothesis. -/
theorem Channel.tensorPower_comp_antidegradable
    (N : Channel a b) (Nc : Channel a e) (D : Channel e b)
    (hdeg : ∀ X : CMatrix a, D.map (Nc.map X) = N.map X) :
    ∀ (n : ℕ) (X : CMatrix (QIT.TensorPower a n)),
      (D.tensorPower n).map ((Nc.tensorPower n).map X)
        = (N.tensorPower n).map X := by
  intro n
  induction n with
  | zero =>
    intro X
    ext i j
    rfl
  | succ n ih =>
    intro X
    rw [Channel.tensorPower_succ D n, Channel.tensorPower_succ Nc n,
      Channel.tensorPower_succ N n]
    show MatrixMap.kron D.map (D.tensorPower n).map
        (MatrixMap.kron Nc.map (Nc.tensorPower n).map X)
      = MatrixMap.kron N.map (N.tensorPower n).map X
    rw [MatrixMap.kron_comp_apply_general]
    have h1 : D.map.comp Nc.map = N.map := by
      apply LinearMap.ext
      intro Y
      exact hdeg Y
    have h2 : (D.tensorPower n).map.comp (Nc.tensorPower n).map
        = (N.tensorPower n).map := by
      apply LinearMap.ext
      intro Y
      exact ih Y
    rw [h1, h2]

/-! ## State- and ensemble-level bridges -/

/-- Private extensionality helper: two ensembles with equal weights and
equal member states are equal (the normalization proof field is irrelevant
by proof irrelevance). -/
private theorem ensembleExt {ι : Type uEnsemble} [Fintype ι] [DecidableEq ι]
    {E F : Ensemble ι a} (hp : E.probs = F.probs) (hs : E.states = F.states) :
    E = F := by
  cases E
  cases F
  cases hp
  cases hs
  rfl

/-- The state-level tensorized transpose simulator: postprocessing the
`n`-fold environment output by `𝓓^{⊗n}` produces the transpose of the
`n`-fold Bob output. -/
theorem Channel.applyState_comp_simulator_transpose
    (N : Channel a b) (Nc : Channel a e) (D : Channel e b)
    (hsim : ∀ X : CMatrix a, D.map (Nc.map X) = MatrixMap.transposeMap (N.map X))
    (n : ℕ) (ρ : State (QIT.TensorPower a n)) :
    (D.tensorPower n).applyState ((Nc.tensorPower n).applyState ρ)
      = State.transpose ((N.tensorPower n).applyState ρ) := by
  apply State.ext
  exact Channel.tensorPower_simulator_transpose N Nc D hsim n ρ.matrix

/-- The state-level tensorized antidegradability bridge. -/
theorem Channel.applyState_comp_antidegradable
    (N : Channel a b) (Nc : Channel a e) (D : Channel e b)
    (hdeg : ∀ X : CMatrix a, D.map (Nc.map X) = N.map X)
    (n : ℕ) (ρ : State (QIT.TensorPower a n)) :
    (D.tensorPower n).applyState ((Nc.tensorPower n).applyState ρ)
      = (N.tensorPower n).applyState ρ := by
  apply State.ext
  exact Channel.tensorPower_comp_antidegradable N Nc D hdeg n ρ.matrix

/-- Ensemble-level transpose simulator: the entrywise transpose of the
Bob-side output ensemble of `𝓝^{⊗n}` *is* the `𝓓^{⊗n}`-image of the
environment-side output ensemble. -/
theorem Channel.outputEnsemble_transpose_simulator
    (N : Channel a b) (Nc : Channel a e) (D : Channel e b)
    (hsim : ∀ X : CMatrix a, D.map (Nc.map X) = MatrixMap.transposeMap (N.map X))
    (n : ℕ) {ι : Type uEnsemble} [Fintype ι] [DecidableEq ι]
    (E : Ensemble ι (QIT.TensorPower a n)) :
    Ensemble.transposeEnsemble ((N.tensorPower n).outputEnsemble E)
      = (D.tensorPower n).outputEnsemble
          ((Nc.tensorPower n).outputEnsemble E) := by
  refine ensembleExt ?_ ?_
  · rfl
  · funext x
    exact (Channel.applyState_comp_simulator_transpose N Nc D hsim n
      (E.states x)).symm

/-- Ensemble-level antidegradability bridge. -/
theorem Channel.outputEnsemble_comp_antidegradable
    (N : Channel a b) (Nc : Channel a e) (D : Channel e b)
    (hdeg : ∀ X : CMatrix a, D.map (Nc.map X) = N.map X)
    (n : ℕ) {ι : Type uEnsemble} [Fintype ι] [DecidableEq ι]
    (E : Ensemble ι (QIT.TensorPower a n)) :
    (N.tensorPower n).outputEnsemble E
      = (D.tensorPower n).outputEnsemble
          ((Nc.tensorPower n).outputEnsemble E) := by
  refine ensembleExt ?_ ?_
  · rfl
  · funext x
    exact (Channel.applyState_comp_antidegradable N Nc D hdeg n (E.states x)).symm

/-! ## Block private information is nonpositive -/

section BlockPrivate

variable {ι : Type uEnsemble} [Fintype ι] [DecidableEq ι]

/-- Under the transpose-simulator hypothesis, every block private
information is nonpositive:
`χ(X : B^n) - χ(X : E^n) ≤ 0` for every `n` and every input ensemble `E`
(paper Section 1: the elementary criterion's mechanism, and thm:private's
route to `P(𝓝) = 0`).

The chain: `χ_B = χ_Bᵀ` (`Ensemble.holevoInformation_transpose`)
`= χ(𝓓^{⊗n} E-side)` (`Channel.outputEnsemble_transpose_simulator`)
`≤ χ_E` (`Ensemble.holevoInformation_outputEnsemble_le` applied to the
channel `D.tensorPower n`). -/
theorem Channel.privateInformationWith_le_zero_of_transpose_simulator
    (N : Channel a b) (Nc : Channel a e) (D : Channel e b)
    (hsim : ∀ X : CMatrix a, D.map (Nc.map X) = MatrixMap.transposeMap (N.map X))
    (n : ℕ) (E : Ensemble ι (QIT.TensorPower a n)) :
    (N.tensorPower n).privateInformationWith (Nc.tensorPower n) E ≤ 0 := by
  have hχ : ((N.tensorPower n).outputEnsemble E).holevoInformation
      ≤ ((Nc.tensorPower n).outputEnsemble E).holevoInformation :=
    calc ((N.tensorPower n).outputEnsemble E).holevoInformation
        = (Ensemble.transposeEnsemble
            ((N.tensorPower n).outputEnsemble E)).holevoInformation :=
          (Ensemble.holevoInformation_transpose _).symm
      _ = ((D.tensorPower n).outputEnsemble
            ((Nc.tensorPower n).outputEnsemble E)).holevoInformation :=
          congrArg Ensemble.holevoInformation
            (Channel.outputEnsemble_transpose_simulator N Nc D hsim n E)
      _ ≤ ((Nc.tensorPower n).outputEnsemble E).holevoInformation :=
          Ensemble.holevoInformation_outputEnsemble_le (D.tensorPower n)
            ((Nc.tensorPower n).outputEnsemble E)
  unfold Channel.privateInformationWith
  exact sub_nonpos.mpr hχ

/-- Under the antidegradability hypothesis `𝓓 ∘ 𝓝ᶜ = 𝓝`, every block
private information is nonpositive (paper Section 2: this is how the
half-erasure channel's zero private capacity is obtained; no transpose step
is needed). -/
theorem Channel.privateInformationWith_le_zero_of_antidegradable
    (N : Channel a b) (Nc : Channel a e) (D : Channel e b)
    (hdeg : ∀ X : CMatrix a, D.map (Nc.map X) = N.map X)
    (n : ℕ) (E : Ensemble ι (QIT.TensorPower a n)) :
    (N.tensorPower n).privateInformationWith (Nc.tensorPower n) E ≤ 0 := by
  have hχ : ((N.tensorPower n).outputEnsemble E).holevoInformation
      ≤ ((Nc.tensorPower n).outputEnsemble E).holevoInformation :=
    calc ((N.tensorPower n).outputEnsemble E).holevoInformation
        = ((D.tensorPower n).outputEnsemble
            ((Nc.tensorPower n).outputEnsemble E)).holevoInformation :=
          congrArg Ensemble.holevoInformation
            (Channel.outputEnsemble_comp_antidegradable N Nc D hdeg n E)
      _ ≤ ((Nc.tensorPower n).outputEnsemble E).holevoInformation :=
          Ensemble.holevoInformation_outputEnsemble_le (D.tensorPower n)
            ((Nc.tensorPower n).outputEnsemble E)
  unfold Channel.privateInformationWith
  exact sub_nonpos.mpr hχ

end BlockPrivate

/-! ## Zero private capacity -/

/-- Capacity-assembly step (paper eq:capacities, the sup-over-block-rates
form): if every block private information of the pair `(N, Nc)` is
nonpositive, then `P(N) = 0`.

Proof: each optimized block value is a supremum of a value set whose
members are all `≤ 0` (`Real.sSup_le`, side condition `0 ≤ 0` discharged
by `rfl`), while the
constant ensemble realizes `0` whenever the value set is nonempty
(`Channel.privateInformationWith_constant_eq_zero` of `Basic`; the average
state of any realized ensemble supplies a state on the block input system),
and `Real.sSup_empty` settles the degenerate empty case.  Hence every block
value is exactly `0`, every block rate is `0`, `0` is a rate (block length
`1`), and the rate set is bounded above by `0`. -/
theorem Channel.privateCapacity_eq_zero_of_block_le
    (N : Channel a b) (Nc : Channel a e)
    (h : ∀ (n : ℕ) (ι : Type uEnsemble) [Fintype ι] [DecidableEq ι]
      (E : Ensemble ι (QIT.TensorPower a n)),
      (N.tensorPower n).privateInformationWith (Nc.tensorPower n) E ≤ 0) :
    Channel.privateCapacity.{u, v, w, uEnsemble} N Nc = 0 := by
  have hvalues_le : ∀ (n : ℕ) (r : ℝ),
      r ∈ Channel.privateInformationValues.{u, v, w, uEnsemble}
          (N.tensorPower n) (Nc.tensorPower n) → r ≤ 0 := by
    intro n r hr
    rcases hr with ⟨ι, hιF, hιD, E, rfl⟩
    letI : Fintype ι := hιF
    letI : DecidableEq ι := hιD
    exact h n ι E
  have hblock : ∀ n : ℕ,
      Channel.blockPrivateInformation.{u, v, w, uEnsemble} N Nc n = 0 := by
    intro n
    unfold Channel.blockPrivateInformation
    have hle : Channel.privateInformation.{u, v, w, uEnsemble}
        (N.tensorPower n) (Nc.tensorPower n) ≤ 0 := by
      unfold Channel.privateInformation
      exact Real.sSup_le (fun r hr => hvalues_le n r hr) (le_of_eq rfl)
    have hge : 0 ≤ Channel.privateInformation.{u, v, w, uEnsemble}
        (N.tensorPower n) (Nc.tensorPower n) := by
      by_cases hne : (Channel.privateInformationValues.{u, v, w, uEnsemble}
          (N.tensorPower n) (Nc.tensorPower n)).Nonempty
      · unfold Channel.privateInformation
        rcases hne with ⟨r₀, ι, hιF, hιD, E, rfl⟩
        letI : Fintype ι := hιF
        letI : DecidableEq ι := hιD
        refine le_csSup ?_ ⟨PUnit.{uEnsemble + 1}, inferInstance, inferInstance,
          Ensemble.constantEnsemble E.averageState, ?_⟩
        · exact ⟨0, fun r hr => hvalues_le n r hr⟩
        · exact (Channel.privateInformationWith_constant_eq_zero
            (N.tensorPower n) (Nc.tensorPower n) E.averageState).symm
      · unfold Channel.privateInformation
        rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty]
    exact le_antisymm hle hge
  have hrate : ∀ R : ℝ,
      R ∈ Channel.privateCapacityRateValues.{u, v, w, uEnsemble} N Nc → R = 0 := by
    intro R hR
    rcases hR with ⟨n, hn, rfl⟩
    rw [hblock n]
    simp
  unfold Channel.privateCapacity
  refine le_antisymm ?_ ?_
  · exact Real.sSup_le (fun R hR => le_of_eq (hrate R hR)) (le_of_eq rfl)
  · refine le_csSup ⟨0, fun R hR => le_of_eq (hrate R hR)⟩
      ⟨1, by norm_num, by rw [hblock 1]; simp⟩

/-- **Transpose-simulator zero-capacity criterion** (paper Section 1,
paragraph "An elementary background criterion", eq:transpose-criterion; the
`P(𝓝) = 0` half of thm:private's mechanism): if the complement of `N` can
be postprocessed by a channel `D` into the transpose of `N`'s output, then
the private capacity of `N` (relative to the complement `Nc`) is zero. -/
theorem Channel.privateCapacity_eq_zero_of_transpose_simulator
    (N : Channel a b) (Nc : Channel a e) (D : Channel e b)
    (hsim : ∀ X : CMatrix a, D.map (Nc.map X)
      = MatrixMap.transposeMap (N.map X)) :
    Channel.privateCapacity.{u, v, w, uEnsemble} N Nc = 0 := by
  apply Channel.privateCapacity_eq_zero_of_block_le N Nc
  intro n ι hF hD E
  exact Channel.privateInformationWith_le_zero_of_transpose_simulator
    N Nc D hsim n E

/-- **Antidegradable channels have zero private capacity** (paper Section 2,
where this is applied to the half-erasure channel `ℰ₄`): if the complement
of `N` can be postprocessed by a channel `D` back into `N` itself, then the
private capacity of `N` (relative to the complement `Nc`) is zero. -/
theorem Channel.privateCapacity_eq_zero_of_antidegradable
    (N : Channel a b) (Nc : Channel a e) (D : Channel e b)
    (hdeg : ∀ X : CMatrix a, D.map (Nc.map X) = N.map X) :
    Channel.privateCapacity.{u, v, w, uEnsemble} N Nc = 0 := by
  apply Channel.privateCapacity_eq_zero_of_block_le N Nc
  intro n ι hF hD E
  exact Channel.privateInformationWith_le_zero_of_antidegradable
    N Nc D hdeg n E

end

end QIT
