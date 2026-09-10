/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team, Chengkai Zhu
-/

module

public import QIT.Coding.Private.Basic
public import QIT.Coding.Private.TransposeCriterion

/-!
# Half erasure in any finite dimension

`Channel.halfErasure` acts on `Fin n` as `X ↦ ½X ⊕ ½ Tr(X)`.
Its Kraus complement is `X ↦ ½ Tr(X) ⊕ ½X`; a summand swap proves
self-complementarity and zero regularized private information.

The qubit specialization is `Channel.erasure2`; `Channel.erasure4` gives
the four-dimensional specialization.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

noncomputable section

/-! ## The normalization scalar `1 / √2`

Local copy of the scalar `QIT.TwoQubit.invSqrtTwo` (which lives in the
unimported module `QIT.Nonlocality.TwoQubit`); the proofs are copied
verbatim from that file. -/

/-- The scalar `1 / sqrt 2`, embedded in `Complex`. -/
def erasureInvSqrtTwo : Complex :=
  ((Real.sqrt 2 : ℝ) : Complex)⁻¹

/-- The square of `1 / sqrt 2` is `1 / 2`. -/
theorem erasureInvSqrtTwo_mul_self :
    erasureInvSqrtTwo * erasureInvSqrtTwo = (1 / 2 : Complex) := by
  norm_num [erasureInvSqrtTwo, Complex.ext_iff]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

@[simp]
theorem star_erasureInvSqrtTwo : star erasureInvSqrtTwo = erasureInvSqrtTwo := by
  simp [erasureInvSqrtTwo]

/-- The product `z * star z = 1/2` in the order it arises from
`(z • M) * (z • M)† = (z * star z) • (M * M†)`. -/
theorem erasureInvSqrtTwo_mul_star_self :
    erasureInvSqrtTwo * star erasureInvSqrtTwo = (1 / 2 : Complex) := by
  rw [star_erasureInvSqrtTwo, erasureInvSqrtTwo_mul_self]

/-- The product `star z * z = 1/2` in the order it arises from
`conjTranspose (z • M) * (z • M) = (star z * z) • (M† * M)`. -/
theorem star_erasureInvSqrtTwo_mul_self :
    star erasureInvSqrtTwo * erasureInvSqrtTwo = (1 / 2 : Complex) := by
  rw [star_erasureInvSqrtTwo, erasureInvSqrtTwo_mul_self]

/-! ## Small `Fin 1` helpers

The flag system is `Fin 1`; mathlib carries `Fin.sum_univ_one` /
`Fin.eq_zero`, and we keep local copies (`fin1_eq_zero`, `sum_fin1`) to
avoid chasing their import boundaries. -/

/-- Every element of `Fin 1` equals `0` (`Fin.val < 1`, closed by `omega`). -/
private theorem fin1_eq_zero (u : Fin 1) : u = 0 := by
  omega

/-- A `Fin 1`-indexed sum of a constant is the constant. -/
private theorem sum_fin1 {M : Type*} [AddCommMonoid M] (N : M) :
    (∑ _u : Fin 1, N) = N := by
  have hc : ∀ u ∈ (Finset.univ : Finset (Fin 1)), N = if u = 0 then N else 0 :=
    fun u _ => by rw [if_pos (fin1_eq_zero u)]
  rw [Finset.sum_congr rfl hc]
  simp [Finset.sum_ite_eq']

variable {n : ℕ}

/-! ## The signal embedding and the erasure Kraus family (paper eq:erasure) -/

/-- The isometric embedding of the input `Fin n` into the signal summand of
`Sum (Fin n) (Fin 1)`; the flag row is zero.  `erasureEmbed† * erasureEmbed`
is the identity (`erasureEmbed_conjTranspose_mul_self`). -/
def erasureEmbed : Matrix (Sum (Fin n) (Fin 1)) (Fin n) Complex :=
  Matrix.of fun r c =>
    Sum.elim (fun i => if i = c then (1 : Complex) else 0) (fun _ => 0) r

@[simp]
theorem erasureEmbed_apply_inl (i c : Fin n) :
    (erasureEmbed (n := n)) (Sum.inl i) c = if i = c then (1 : Complex) else 0 :=
  rfl

@[simp]
theorem erasureEmbed_apply_inr (f : Fin 1) (c : Fin n) :
    (erasureEmbed (n := n)) (Sum.inr f) c = 0 :=
  rfl

/-- The embedding is an isometry: `erasureEmbed† * erasureEmbed = 1`. -/
theorem erasureEmbed_conjTranspose_mul_self :
    Matrix.conjTranspose (erasureEmbed (n := n)) * (erasureEmbed (n := n))
      = (1 : CMatrix (Fin n)) := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, (erasureEmbed_apply_inl (n := n)),
    (erasureEmbed_apply_inr (n := n)), Fintype.sum_sum_type]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

/-- The Kraus family of ℰₙ, indexed by the environment system
`Sum (Fin 1) (Fin n)` (flag ⊕ signal): the `inl` branch transmits through
the signal embedding, each `inr k` branch erases onto the flag carrying the
`k`-th input diagonal.  Both branches carry the `1/√2` of the 50% erasure
probability (paper eq:erasure). -/
def erasureKraus : Sum (Fin 1) (Fin n) → Matrix (Sum (Fin n) (Fin 1)) (Fin n) Complex
  | Sum.inl _ => erasureInvSqrtTwo • (erasureEmbed (n := n))
  | Sum.inr k =>
      erasureInvSqrtTwo • Matrix.single (Sum.inr (0 : Fin 1)) k (1 : Complex)

@[simp]
theorem erasureKraus_inl (u : Fin 1) :
    (erasureKraus (n := n)) (Sum.inl u) = erasureInvSqrtTwo • (erasureEmbed (n := n)) :=
  rfl

@[simp]
theorem erasureKraus_inr (k : Fin n) :
    (erasureKraus (n := n)) (Sum.inr k)
      = erasureInvSqrtTwo • Matrix.single (Sum.inr (0 : Fin 1)) k (1 : Complex) :=
  rfl

/-- Entrywise form of the flag-Kraus contraction `B_k† B_k = |k⟩⟨k|`. -/
private theorem erasureFlag_conjTranspose_mul_single (k i j : Fin n) :
    (Matrix.conjTranspose
        (Matrix.single (Sum.inr (0 : Fin 1) : Sum (Fin n) (Fin 1)) k (1 : Complex))
        * Matrix.single (Sum.inr (0 : Fin 1) : Sum (Fin n) (Fin 1)) k
            (1 : Complex)) i j
      = if i = k ∧ j = k then (1 : Complex) else 0 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, Matrix.single_apply, Fintype.sum_sum_type]
  simp
  by_cases h : i = k ∧ j = k
  · obtain ⟨hik, hjk⟩ := h
    rw [hik, hjk]
    simp
  · by_cases hik : i = k
    · have hjk : ¬j = k := fun hjk => h ⟨hik, hjk⟩
      simp [hik, hjk, Ne.symm hjk]
    · simp [hik, Ne.symm hik]

/-- The Kraus family of ℰₙ is complete: `∑_l K_l† K_l = 1`
(the `1/2 + 1/2` of the 50% erasure channel, paper eq:erasure). -/
theorem erasureKraus_sum :
    (∑ l : Sum (Fin 1) (Fin n),
      Matrix.conjTranspose ((erasureKraus (n := n)) l) * (erasureKraus (n := n)) l)
      = (1 : CMatrix (Fin n)) := by
  ext i j
  rw [Fintype.sum_sum_type, Matrix.add_apply, Matrix.sum_apply, Matrix.sum_apply,
    Matrix.one_apply]
  -- inl branch: (1/2) • (erasureEmbed† * erasureEmbed)
  have hterm : ∀ u : Fin 1,
      (Matrix.conjTranspose ((erasureKraus (n := n)) (Sum.inl u)) * (erasureKraus (n := n)) (Sum.inl
        u)) i j
        = (1 / 2 : Complex)
          * (Matrix.conjTranspose (erasureEmbed (n := n)) * (erasureEmbed (n := n))) i j := by
    intro u
    rw [(erasureKraus_inl (n := n)), Matrix.conjTranspose_smul, Matrix.mul_smul,
      Matrix.smul_mul, smul_smul, erasureInvSqrtTwo_mul_star_self,
      Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun u _ => hterm u), sum_fin1,
    (erasureEmbed_conjTranspose_mul_self (n := n)), Matrix.one_apply]
  -- inr branch: ∑_k (1/2) • [i = k][j = k]
  have hterm' : ∀ k : Fin n,
      (Matrix.conjTranspose ((erasureKraus (n := n)) (Sum.inr k)) * (erasureKraus (n := n)) (Sum.inr
        k)) i j
        = (1 / 2 : Complex) * (if i = k ∧ j = k then (1 : Complex) else 0) := by
    intro k
    rw [(erasureKraus_inr (n := n)), Matrix.conjTranspose_smul, Matrix.mul_smul,
      Matrix.smul_mul, smul_smul, erasureInvSqrtTwo_mul_star_self,
      Matrix.smul_apply, smul_eq_mul, (erasureFlag_conjTranspose_mul_single (n := n))]
  rw [Finset.sum_congr rfl (fun k _ => hterm' k), ← Finset.mul_sum]
  by_cases h : i = j
  · subst h
    rw [Finset.sum_eq_single i]
    · norm_num
    · intro k _ hk
      simp [Ne.symm hk]
    · intro hnot
      exact (hnot (Finset.mem_univ _)).elim
  · rw [Finset.sum_eq_zero]
    · simp [h]
    · intro k _
      by_cases hk : i = k
      · subst hk
        simp [h, eq_comm]
      · simp [hk]

/-- The Kraus adjoint of the erasure family is unital, giving trace
preservation via `MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one`. -/
theorem erasureKraus_krausAdjoint_one :
    MatrixMap.krausAdjoint (erasureKraus (n := n)) (1 : CMatrix (Sum (Fin n) (Fin 1)))
      = 1 := by
  show (∑ l : Sum (Fin 1) (Fin n),
      Matrix.conjTranspose ((erasureKraus (n := n)) l) * (1 : CMatrix (Sum (Fin n) (Fin 1)))
        * (erasureKraus (n := n)) l) = 1
  simp only [Matrix.mul_one]
  exact (erasureKraus_sum (n := n))

/-! ## The half-erasure channel ℰₙ -/

/-- The 50% erasure channel ℰₙ : n → n+1 on the output system
`Sum (Fin n) (Fin 1)` (signal ⊕ flag), paper eq:erasure. -/
def Channel.halfErasure : Channel (Fin n) (Sum (Fin n) (Fin 1)) where
  map := MatrixMap.ofKraus (erasureKraus (n := n))
  completelyPositive := MatrixMap.ofKraus_completelyPositive (erasureKraus (n := n))
  tracePreserving := MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one
    (erasureKraus (n := n)) (erasureKraus_krausAdjoint_one (n := n))
  mapsPositive := MatrixMap.ofKraus_mapsPositive (erasureKraus (n := n))

/-- The transmitted block of the Stinespring form: conjugating by the
embedding reproduces the upper-left block. -/
theorem erasureEmbed_conj_mul (X : CMatrix (Fin n)) :
    (erasureEmbed (n := n)) * X * Matrix.conjTranspose (erasureEmbed (n := n))
      = Matrix.fromBlocks X 0 0 (0 : Matrix (Fin 1) (Fin 1) Complex) := by
  ext r r'
  rcases r with i | f <;> rcases r' with i' | f'
  · simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
      (erasureEmbed_apply_inl (n := n)), Matrix.fromBlocks_apply₁₁, Finset.sum_mul]
    simp
  · simp [Matrix.mul_apply, Matrix.conjTranspose_apply, (erasureEmbed_apply_inr (n := n)),
      Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
  · simp [Matrix.mul_apply, Matrix.conjTranspose_apply, (erasureEmbed_apply_inr (n := n)),
      Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
  · simp [Matrix.mul_apply, Matrix.conjTranspose_apply, (erasureEmbed_apply_inr (n := n)),
      Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]

/-- The erased block of the Stinespring form: the flag Kraus `B_k` contributes
the single flag-flag entry `X k k`. -/
theorem erasureFlag_conj_mul (X : CMatrix (Fin n)) (k : Fin n) :
    Matrix.single (Sum.inr (0 : Fin 1)) k (1 : Complex) * X
      * Matrix.conjTranspose (Matrix.single (Sum.inr (0 : Fin 1)) k (1 : Complex))
      = Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) Complex) 0 0
          (Matrix.single (0 : Fin 1) (0 : Fin 1) (X k k)) := by
  ext r r'
  rcases r with i | f <;> rcases r' with i' | f'
  · simp [Matrix.mul_apply, Matrix.fromBlocks_apply₁₁, Matrix.zero_apply]
  · simp [Matrix.mul_apply, Matrix.single_apply, Matrix.fromBlocks_apply₁₂,
      Matrix.zero_apply]
  · simp [Matrix.mul_apply, Matrix.single_apply, Matrix.fromBlocks_apply₂₁,
      Matrix.zero_apply]
  · rw [fin1_eq_zero f, fin1_eq_zero f']
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.single_apply, Matrix.fromBlocks_apply₂₂, Finset.sum_mul]
    simp

/-- The action of ℰₙ: the signal block carries `½X`, the flag block carries
`½ Tr(X)` (paper eq:erasure). -/
theorem halfErasure_apply (X : CMatrix (Fin n)) :
    (Channel.halfErasure (n := n)).map X =
      Matrix.fromBlocks ((1 / 2 : Complex) • X) 0 0
        ((1 / 2 * X.trace) • (1 : Matrix (Fin 1) (Fin 1) Complex)) := by
  show (∑ l : Sum (Fin 1) (Fin n),
      (erasureKraus (n := n)) l * X * Matrix.conjTranspose ((erasureKraus (n := n)) l)) = _
  rw [Fintype.sum_sum_type]
  -- inl branch collapses to ½ • (embed X embed†)
  have hterm : ∀ u : Fin 1,
      (erasureKraus (n := n)) (Sum.inl u) * X * Matrix.conjTranspose ((erasureKraus (n := n))
        (Sum.inl u))
        = (1 / 2 : Complex)
          • ((erasureEmbed (n := n)) * X * Matrix.conjTranspose (erasureEmbed (n := n))) := by
    intro u
    rw [(erasureKraus_inl (n := n)), Matrix.conjTranspose_smul, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.smul_mul, smul_smul, star_erasureInvSqrtTwo_mul_self]
  rw [Finset.sum_congr rfl (fun u _ => hterm u), sum_fin1,
    (erasureEmbed_conj_mul (n := n))]
  -- inr branch collapses to ½ • ∑_k B_k X B_k†
  have hterm' : ∀ k : Fin n,
      (erasureKraus (n := n)) (Sum.inr k) * X * Matrix.conjTranspose ((erasureKraus (n := n))
        (Sum.inr k))
        = (1 / 2 : Complex)
          • Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) Complex) 0 0
              (Matrix.single (0 : Fin 1) (0 : Fin 1) (X k k)) := by
    intro k
    rw [(erasureKraus_inr (n := n)), Matrix.conjTranspose_smul, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.smul_mul, smul_smul, star_erasureInvSqrtTwo_mul_self,
      (erasureFlag_conj_mul (n := n))]
  rw [Finset.sum_congr rfl (fun k _ => hterm' k)]
  -- assemble the remaining identity entrywise
  ext r r'
  rcases r with i | f <;> rcases r' with i' | f'
  · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.sum_apply, Matrix.fromBlocks_apply₁₁, Matrix.zero_apply]
    simp
  · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.sum_apply, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
    simp
  · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.sum_apply, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
    simp
  · rw [fin1_eq_zero f, fin1_eq_zero f']
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.sum_apply, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply,
      Matrix.single_apply]
    simp only [Matrix.one_apply]
    simp only [Matrix.trace]
    simp
    rw [Finset.mul_sum]

/-! ## The summand-swap permutation -/

/-- The summand-swap function on the output system of ℰₙ. -/
def sumSwapMap : Sum (Fin n) (Fin 1) → Sum (Fin 1) (Fin n) :=
  Sum.elim Sum.inr Sum.inl

/-- The summand-swap function on the output system of ℰₙᶜ. -/
def sumSwapMap' : Sum (Fin 1) (Fin n) → Sum (Fin n) (Fin 1) :=
  Sum.elim Sum.inr Sum.inl

@[simp]
theorem sumSwapMap_involution (x : Sum (Fin n) (Fin 1)) :
    (sumSwapMap' (n := n)) ((sumSwapMap (n := n)) x) = x := by
  cases x <;> rfl

@[simp]
theorem sumSwapMap'_involution (x : Sum (Fin 1) (Fin n)) :
    (sumSwapMap (n := n)) ((sumSwapMap' (n := n)) x) = x := by
  cases x <;> rfl

theorem sumSwapMap_inj {r r' : Sum (Fin n) (Fin 1)}
    (h : (sumSwapMap (n := n)) r = (sumSwapMap (n := n)) r') : r = r' := by
  rw [← (sumSwapMap_involution (n := n)) r, ← (sumSwapMap_involution (n := n)) r', h]

theorem sumSwapMap'_inj {t t' : Sum (Fin 1) (Fin n)}
    (h : (sumSwapMap' (n := n)) t = (sumSwapMap' (n := n)) t') : t = t' := by
  rw [← (sumSwapMap'_involution (n := n)) t, ← (sumSwapMap'_involution (n := n)) t', h]

/-- The summand-swap permutation matrix `S : (flag ⊕ signal) → (signal ⊕ flag)`,
`S_{r,c} = [σ c = r]`.  It is unitary with `S⁻¹ = S†` the transposed swap. -/
def sumSwapM : Matrix (Sum (Fin 1) (Fin n)) (Sum (Fin n) (Fin 1)) Complex :=
  Matrix.of fun r c => if (sumSwapMap (n := n)) c = r then (1 : Complex) else 0

/-- The summand-swap permutation matrix in the other direction. -/
def sumSwapMinv : Matrix (Sum (Fin n) (Fin 1)) (Sum (Fin 1) (Fin n)) Complex :=
  Matrix.of fun s t => if (sumSwapMap (n := n)) s = t then (1 : Complex) else 0

theorem sumSwapMinv_eq_conjTranspose :
    (sumSwapMinv (n := n)) = Matrix.conjTranspose (sumSwapM (n := n)) := by
  ext s t
  by_cases h : (sumSwapMap (n := n)) s = t
  · simp [sumSwapM, sumSwapMinv, Matrix.conjTranspose_apply, h]
  · simp [sumSwapM, sumSwapMinv, Matrix.conjTranspose_apply, h]

theorem conjTranspose_sumSwapMinv :
    Matrix.conjTranspose (sumSwapMinv (n := n)) = (sumSwapM (n := n)) := by
  ext r c
  simp [sumSwapM, sumSwapMinv, Matrix.conjTranspose_apply, sumSwapMap]

/-- The swap and its reverse compose to the identity on `Sum (Fin 1) (Fin n)`. -/
theorem sumSwapM_mul_sumSwapMinv :
    (sumSwapM (n := n)) * (sumSwapMinv (n := n)) = (1 : CMatrix (Sum (Fin 1) (Fin n))) := by
  ext t t'
  rw [Matrix.mul_apply, Matrix.one_apply]
  by_cases htt' : t = t'
  · subst htt'
    rw [Finset.sum_eq_single ((sumSwapMap' (n := n)) t)]
    · simp [sumSwapM, sumSwapMinv]
    · intro s _ hs
      have hne : (sumSwapMap (n := n)) s ≠ t := by
        intro h
        refine hs ?_
        rw [← h, (sumSwapMap_involution (n := n))]
      simp [sumSwapM, sumSwapMinv, hne]
    · intro hnot
      exact (hnot (Finset.mem_univ _)).elim
  · rw [Finset.sum_eq_zero]
    · simp [htt']
    · intro s _
      by_cases h1 : (sumSwapMap (n := n)) s = t
      · simp [sumSwapM, sumSwapMinv, h1, htt']
      · simp [sumSwapM, sumSwapMinv, h1]

/-- The swap and its reverse compose to the identity on `Sum (Fin n) (Fin 1)`. -/
theorem sumSwapMinv_mul_sumSwapM :
    (sumSwapMinv (n := n)) * (sumSwapM (n := n)) = (1 : CMatrix (Sum (Fin n) (Fin 1))) := by
  ext r r'
  rw [Matrix.mul_apply, Matrix.one_apply]
  by_cases hrr' : r = r'
  · subst hrr'
    rw [Finset.sum_eq_single (sumSwapMap r)]
    · simp [sumSwapM, sumSwapMinv]
    · intro c _ hc
      simp [sumSwapM, sumSwapMinv, hc, eq_comm]
    · intro hnot
      exact (hnot (Finset.mem_univ _)).elim
  · rw [Finset.sum_eq_zero]
    · simp [hrr']
    · intro c _
      by_cases h1 : (sumSwapMap (n := n)) r = c
      · have h2 : ¬((sumSwapMap (n := n)) r' = c) := by
          intro h2
          exact hrr' ((sumSwapMap_inj (n := n)) (h1.trans h2.symm))
        simp [sumSwapM, sumSwapMinv, h1, h2]
      · simp [sumSwapM, sumSwapMinv, h1]

/-- The swap matrix is an isometry: `S† S = 1`. -/
theorem sumSwapM_conjTranspose_mul_self :
    Matrix.conjTranspose (sumSwapM (n := n)) * (sumSwapM (n := n))
      = (1 : CMatrix (Sum (Fin n) (Fin 1))) := by
  rw [← (sumSwapMinv_eq_conjTranspose (n := n)), (sumSwapMinv_mul_sumSwapM (n := n))]

/-- The reverse swap matrix is an isometry: `(S⁻¹)† S⁻¹ = 1`. -/
theorem sumSwapMinv_conjTranspose_mul_self :
    Matrix.conjTranspose (sumSwapMinv (n := n)) * (sumSwapMinv (n := n))
      = (1 : CMatrix (Sum (Fin 1) (Fin n))) := by
  rw [(conjTranspose_sumSwapMinv (n := n)), (sumSwapM_mul_sumSwapMinv (n := n))]

/-! ## The summand-swap channels -/

/-- The summand-swap unitary channel `S : X ↦ S X S†` from the output system
of ℰₙ to the output system of ℰₙᶜ, packaged as a single-Kraus channel (same
construction as the isometry decoder `typicalDecoder` in
`QIT.Coding.Source.SchumacherDirect`). -/
def Channel.sumSwap : Channel (Sum (Fin n) (Fin 1)) (Sum (Fin 1) (Fin n)) where
  map := MatrixMap.ofKraus (fun _ : Unit => (sumSwapM (n := n)))
  completelyPositive := MatrixMap.ofKraus_completelyPositive _
  tracePreserving := MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one _
    (by show (∑ _ : Unit, Matrix.conjTranspose (sumSwapM (n := n))
            * (1 : CMatrix (Sum (Fin 1) (Fin n))) * (sumSwapM (n := n))) = 1
        rw [Fintype.sum_unique]
        simp only [Matrix.mul_one]
        exact (sumSwapM_conjTranspose_mul_self (n := n)))
  mapsPositive := MatrixMap.ofKraus_mapsPositive _

/-- The reverse summand-swap unitary channel. -/
def Channel.sumSwapInv : Channel (Sum (Fin 1) (Fin n)) (Sum (Fin n) (Fin 1)) where
  map := MatrixMap.ofKraus (fun _ : Unit => (sumSwapMinv (n := n)))
  completelyPositive := MatrixMap.ofKraus_completelyPositive _
  tracePreserving := MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one _
    (by show (∑ _ : Unit, Matrix.conjTranspose (sumSwapMinv (n := n))
            * (1 : CMatrix (Sum (Fin n) (Fin 1))) * (sumSwapMinv (n := n))) = 1
        rw [Fintype.sum_unique]
        simp only [Matrix.mul_one]
        exact (sumSwapMinv_conjTranspose_mul_self (n := n)))
  mapsPositive := MatrixMap.ofKraus_mapsPositive _

/-- The reverse swap undoes the swap channel on every matrix
(`S⁻¹ ∘ S = id` on `CMatrix (Sum (Fin n) (Fin 1))`). -/
theorem sumSwapInv_map_sumSwap_map (Y : CMatrix (Sum (Fin n) (Fin 1))) :
    (Channel.sumSwapInv (n := n)).map ((Channel.sumSwap (n := n)).map Y) = Y := by
  have h1 : ((Channel.sumSwapInv (n := n)).map ((Channel.sumSwap (n := n)).map Y) : CMatrix (Sum
    (Fin n) (Fin 1)))
      = (MatrixMap.ofKraus (fun _ : Unit => (sumSwapMinv (n := n)))).comp
          (MatrixMap.ofKraus (fun _ : Unit => (sumSwapM (n := n)))) Y :=
    rfl
  rw [h1, MatrixMap.ofKraus_comp_ofKraus]
  show (∑ p : Unit × Unit,
      ((sumSwapMinv (n := n)) * (sumSwapM (n := n))) * Y * Matrix.conjTranspose ((sumSwapMinv (n :=
        n)) * (sumSwapM (n := n)))) = Y
  rw [(sumSwapMinv_mul_sumSwapM (n := n)), Matrix.conjTranspose_one, Matrix.mul_one,
    Matrix.one_mul, Fintype.sum_prod_type]
  simp

/-! ## The complementary channel ℰₙᶜ and self-complementarity -/

/-- The underlying matrix map of ℰₙᶜ:
`X ↦ ½ Tr(X) ⊕ ½X` on the environment system `Sum (Fin 1) (Fin n)`
(paper eq:erasure, complement). -/
def erasureComplementMap :
    MatrixMap (Fin n) (Sum (Fin 1) (Fin n)) where
  toFun X := Matrix.fromBlocks ((1 / 2 * X.trace) • (1 : Matrix (Fin 1) (Fin 1) Complex))
    0 0 ((1 / 2 : Complex) • X)
  map_add' X Y := by
    ext lm lm'
    rcases lm with u | k <;> rcases lm' with u' | k'
    all_goals
      simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
        Matrix.smul_apply, Matrix.one_apply, Matrix.add_apply,
        Matrix.trace_add, Matrix.zero_apply, smul_add]
    all_goals ring
  map_smul' r X := by
    ext lm lm'
    rcases lm with u | k <;> rcases lm' with u' | k'
    all_goals
      simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
        Matrix.smul_apply, Matrix.one_apply, Matrix.trace_smul,
        Matrix.zero_apply, RingHom.id_apply, smul_smul, smul_zero]
    all_goals ring

/-- One-entry trace of the `Fin 1` identity block. -/
private theorem trace_one_fin1 :
    (1 : Matrix (Fin 1) (Fin 1) Complex).trace = 1 := by
  rw [Matrix.trace_one, Fintype.card_fin]
  norm_num

/-- ℰₙᶜ is trace-preserving: the two half-traces reassemble `Tr X`
(`Matrix.trace_fromBlocks_diagonal`). -/
theorem erasureComplementMap_isTracePreserving :
    MatrixMap.IsTracePreserving (erasureComplementMap (n := n)) := by
  intro X
  show (Matrix.fromBlocks ((1 / 2 * X.trace)
        • (1 : Matrix (Fin 1) (Fin 1) Complex)) 0 0 ((1 / 2 : Complex) • X)).trace
      = X.trace
  rw [Matrix.trace_fromBlocks_diagonal, Matrix.trace_smul, Matrix.trace_smul,
    trace_one_fin1]
  ring

/-- The core conjugation identity behind self-complementarity: swapping the
summands of `½ A ⊕ t` (flag block `t • 1_{Fin 1}`) gives `t ⊕ ½ A` conjugated
by the swap, i.e. `S (½ A ⊕ t) S† = t ⊕ ½ A` (paper eq:erasure and
Section 2: "ℰₙ is self-complementary", i.e. `ℰₙᶜ = S ∘ ℰₙ`). -/
theorem sumSwapM_fromBlocks_conjTranspose (A : CMatrix (Fin n)) (t : Complex) :
    (sumSwapM (n := n)) * Matrix.fromBlocks A 0 0 (t • (1 : Matrix (Fin 1) (Fin 1) Complex))
      * Matrix.conjTranspose (sumSwapM (n := n))
    = Matrix.fromBlocks (t • (1 : Matrix (Fin 1) (Fin 1) Complex)) 0 0 A := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, sumSwapM, sumSwapMap,
      Fintype.sum_sum_type, fin1_eq_zero]

/-- Pointwise factorization of the underlying matrix map of ℰₙᶜ through the
swap: `erasureComplementMap X = S(ℰₙ(X))` — the self-complementarity matrix
identity of the half-erasure channel (paper eq:erasure; Section 2
"self-complementary").  Stated on the already-defined matrix map; the
channel-level version `halfErasureComplement_eq_swap` is derived after the
channel is defined. -/
private theorem erasureComplementMap_eq_swap (X : CMatrix (Fin n)) :
    (erasureComplementMap (n := n)) X
      = (Channel.sumSwap (n := n)).map ((Channel.halfErasure (n := n)).map X) := by
  rw [(halfErasure_apply (n := n)) X]
  show Matrix.fromBlocks ((1 / 2 * X.trace) • (1 : Matrix (Fin 1) (Fin 1) Complex))
      0 0 ((1 / 2 : Complex) • X)
      = (∑ u : Unit, (sumSwapM (n := n))
          * Matrix.fromBlocks ((1 / 2 : Complex) • X) 0 0
              ((1 / 2 * X.trace) • (1 : Matrix (Fin 1) (Fin 1) Complex))
          * Matrix.conjTranspose (sumSwapM (n := n)))
  rw [Fintype.sum_unique]
  exact ((sumSwapM_fromBlocks_conjTranspose (n := n)) ((1 / 2 : Complex) • X)
    (1 / 2 * X.trace)).symm

/-- Pointwise factorization at the map level. -/
private theorem erasureComplementMap_eq_comp :
    (erasureComplementMap (n := n))
      = ((Channel.sumSwap (n := n)).map).comp ((Channel.halfErasure (n := n)).map) := by
  apply LinearMap.ext
  intro X
  exact (erasureComplementMap_eq_swap (n := n)) X

/-- The complementary channel of ℰₙ on the environment system
`Sum (Fin 1) (Fin n)`, `ℰₙᶜ(X) = ½ Tr(X) ⊕ ½X` (paper eq:erasure).
Complete positivity and positivity transfer through the unitary
factorization `ℰₙᶜ = S ∘ ℰₙ` of `halfErasureComplement_eq_swap`. -/
def Channel.halfErasureComplement : Channel (Fin n) (Sum (Fin 1) (Fin n)) where
  map := (erasureComplementMap (n := n))
  completelyPositive := by
    show MatrixMap.IsCompletelyPositive (erasureComplementMap (n := n))
    rw [(erasureComplementMap_eq_comp (n := n))]
    exact MatrixMap.isCompletelyPositive_comp (Channel.sumSwap (n := n)).map
      (Channel.halfErasure (n := n)).map (Channel.sumSwap (n := n)).completelyPositive
      (Channel.halfErasure (n := n)).completelyPositive
  tracePreserving := (erasureComplementMap_isTracePreserving (n := n))
  mapsPositive := by
    intro X hX
    show ((erasureComplementMap (n := n)) X).PosSemidef
    rw [(erasureComplementMap_eq_swap (n := n)) X]
    exact (Channel.sumSwap (n := n)).mapsPositive _
      ((Channel.halfErasure (n := n)).mapsPositive X hX)

/-- Pointwise factorization of the complementary channel through the swap:
  `ℰₙᶜ(X) = S(ℰₙ(X))` — the self-complementarity identity of the half-erasure
channel (paper eq:erasure; Section 2 "self-complementary").  The channel's
underlying map *is* `erasureComplementMap`, so this is the matrix-map
factorization read through the definition. -/
theorem halfErasureComplement_eq_swap (X : CMatrix (Fin n)) :
    (Channel.halfErasureComplement (n := n)).map X
      = (Channel.sumSwap (n := n)).map ((Channel.halfErasure (n := n)).map X) :=
  (erasureComplementMap_eq_swap (n := n)) X

/-! ## ℰₙᶜ as the complement of the Kraus family (paper eq:complement) -/

/-- `halfErasureComplement` is a complement of `halfErasure` in the sense of
`Channel.IsComplementOf`: both arise from the single Kraus family
`erasureKraus`, the channel as `MatrixMap.ofKraus` and the complement as
`MatrixMap.complementOfKraus`, whose entries are
`[ℰₙᶜ(X)]_{ℓm} = Tr(K_ℓ X K_m†)` (paper eq:complement). -/
theorem halfErasure_isComplementOf :
    Channel.IsComplementOf (Channel.halfErasureComplement (n := n)) (Channel.halfErasure (n := n)) := by
  refine ⟨(erasureKraus (n := n)), rfl, ?_⟩
  apply LinearMap.ext
  intro X
  ext i j
  change (erasureComplementMap (n := n)) X i j =
    ((erasureKraus (n := n)) i * X * ((erasureKraus (n := n)) j).conjTranspose).trace
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [erasureKraus, Matrix.conjTranspose_smul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, star_erasureInvSqrtTwo,
      erasureInvSqrtTwo_mul_self, Matrix.trace_smul]
  · simp [erasureComplementMap, (erasureEmbed_conj_mul (n := n)), fin1_eq_zero,
      Matrix.trace_fromBlocks_diagonal]
  · simp [erasureComplementMap, Matrix.trace, Matrix.mul_apply,
      erasureEmbed, Fintype.sum_sum_type, Matrix.single_apply]
  · simp [erasureComplementMap, Matrix.trace, Matrix.mul_apply,
      Matrix.conjTranspose_apply, erasureEmbed, Fintype.sum_sum_type,
      Matrix.single_apply, Finset.sum_mul]
  · simp [erasureComplementMap, Matrix.trace, fin1_eq_zero]

/-! ## Antidegradability and the zero private capacity -/

/-- The degrading factorization: composing the reverse swap channel with the
complement recovers ℰₙ, `S⁻¹ ∘ ℰₙᶜ = ℰₙ` — ℰₙ is antidegradable
(paper Section 2: "self-complementary, hence antidegradable"). -/
theorem halfErasure_antidegradable_sumSwapInv (X : CMatrix (Fin n)) :
    (Channel.sumSwapInv (n := n)).map ((Channel.halfErasureComplement (n := n)).map X)
      = (Channel.halfErasure (n := n)).map X := by
  rw [(halfErasureComplement_eq_swap (n := n)) X]
  exact (sumSwapInv_map_sumSwap_map (n := n)) ((Channel.halfErasure (n := n)).map X)

/-- The degrading witness in `∀ X` form. -/
theorem halfErasure_antidegradable :
    ∀ X : CMatrix (Fin n),
      (Channel.sumSwapInv (n := n)).map ((Channel.halfErasureComplement (n := n)).map X)
        = (Channel.halfErasure (n := n)).map X :=
  (halfErasure_antidegradable_sumSwapInv (n := n))

/-- **The private capacity of the half-erasure channel is zero** (paper
eq:erasure and Section 2: "Self-complementarity gives P(ℰₙ) = 0 at every
blocklength").  Proof: the antidegradability criterion
`Channel.privateCapacity_eq_zero_of_antidegradable` applied with the
complement `halfErasureComplement` (which `halfErasure_isComplementOf`
legitimizes as a genuine complement, though the criterion itself does not
consume that hypothesis) and the degrading channel `Channel.sumSwapInv`
via `halfErasure_antidegradable`. The self-complementarity and complement
identities used here are proved. -/
theorem halfErasure_privateCapacity_eq_zero :
    Channel.privateCapacity (Channel.halfErasure (n := n)) (Channel.halfErasureComplement (n := n))
      = 0 :=
  Channel.privateCapacity_eq_zero_of_antidegradable (Channel.halfErasure (n := n))
    (Channel.halfErasureComplement (n := n)) (Channel.sumSwapInv (n := n))
      (halfErasure_antidegradable (n := n))


/-- Qubit half-erasure channel. -/
abbrev Channel.erasure2 := Channel.halfErasure (n := 2)

/-- The full three-dimensional complement of qubit half erasure. -/
abbrev Channel.erasure2Complement := Channel.halfErasureComplement (n := 2)

theorem erasure2_isComplementOf :
    Channel.IsComplementOf Channel.erasure2Complement Channel.erasure2 :=
  halfErasure_isComplementOf (n := 2)

theorem erasure2_privateCapacity_eq_zero :
    Channel.privateCapacity Channel.erasure2 Channel.erasure2Complement = 0 :=
  halfErasure_privateCapacity_eq_zero (n := 2)

/-- Four-dimensional half-erasure channel. -/
abbrev Channel.erasure4 := Channel.halfErasure (n := 4)

abbrev Channel.erasure4Complement := Channel.halfErasureComplement (n := 4)

theorem erasure4_apply (X : CMatrix (Fin 4)) :
    Channel.erasure4.map X =
      Matrix.fromBlocks ((1 / 2 : Complex) • X) 0 0
        ((1 / 2 * X.trace) • (1 : CMatrix (Fin 1))) :=
  halfErasure_apply X

theorem erasure4_isComplementOf :
    Channel.IsComplementOf Channel.erasure4Complement Channel.erasure4 :=
  halfErasure_isComplementOf (n := 4)

theorem erasure4_privateCapacity_eq_zero :
    Channel.privateCapacity Channel.erasure4 Channel.erasure4Complement = 0 :=
  halfErasure_privateCapacity_eq_zero (n := 4)

end

end QIT
