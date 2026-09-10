/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team, Chengkai Zhu
-/

module

public import QIT.Coding.Private.Basic
public import QIT.Coding.Private.TransposeCriterion

/-!
# The explicit four-dimensional channel and transpose simulator

This module constructs a four-dimensional channel, its full eight-dimensional
Kraus complement and a transpose simulator. Positivity and trace preservation
are proved here; the simulation identity is proved in `SimulatorCertificate`.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder
namespace QIT
open Channel
noncomputable section

/-! ## The channel data (paper eq:matrices, eq:channel)

`Y` is the real antidiagonal unitary `Y_{ba} = (-1)^b δ_{b,3-a}` and
`T_k` are the seven real symmetric matrices
`(T_k)_{bd} = δ_{k,b+d} √(C(3,b)C(3,d)/C(6,k))` of eq:matrices.  These are
`check_channel_integration.py` lines 35--38 verbatim (index conventions
included: rows and columns range over `0..3`, square roots are of
rationals built from binomial coefficients). -/

/-- The matrix `Y` of paper eq:matrices: the antidiagonal sign matrix,
`Y_{ba} = (-1)^b δ_{b,3-a}` (Python: `[(-1)**b if b == 3-a else 0]`). -/
def yM : Matrix (Fin 4) (Fin 4) Complex :=
  Matrix.of fun b a => if (b : ℕ) + (a : ℕ) = 3 then (-1 : Complex) ^ (b : ℕ) else 0

@[simp]
theorem yM_apply (b a : Fin 4) :
    yM b a = if (b : ℕ) + (a : ℕ) = 3 then (-1 : Complex) ^ (b : ℕ) else 0 := by
  rfl

/-- The matrices `T_k` of paper eq:matrices, `0 ≤ k ≤ 6`:
`(T_k)_{bd} = δ_{k,b+d} √(C(3,b)C(3,d)/C(6,k))`. -/
def tM (k : Fin 7) : Matrix (Fin 4) (Fin 4) Complex :=
  Matrix.of fun b d =>
    if (b : ℕ) + (d : ℕ) = (k : ℕ) then
      Complex.ofReal (Real.sqrt
        (((Nat.choose 3 b * Nat.choose 3 d : ℕ) : ℝ) / ((Nat.choose 6 k : ℕ) : ℝ)))
    else 0

@[simp]
theorem tM_apply (k : Fin 7) (b d : Fin 4) :
    tM k b d =
      (if (b : ℕ) + (d : ℕ) = (k : ℕ) then
        Complex.ofReal (Real.sqrt
          (((Nat.choose 3 b * Nat.choose 3 d : ℕ) : ℝ) / ((Nat.choose 6 k : ℕ) : ℝ)))
      else 0) := by
  rfl

/-- The Kraus family of paper eq:channel: `K₀ = I₄/√6` and
`K_{k+1} = √(10/21) · T_k Y` for `0 ≤ k ≤ 6` (Python:
`K = concat([I/√6], √(10/21) · T @ Y)`). -/
def krausN : Fin 8 → Matrix (Fin 4) (Fin 4) Complex :=
  fun ℓ =>
    match ℓ with
    | ⟨0, _⟩ => (Complex.ofReal (1 / Real.sqrt 6)) • (1 : CMatrix (Fin 4))
    | ⟨k + 1, h⟩ =>
      (Complex.ofReal (Real.sqrt ((10 : ℝ) / 21))) • (tM ⟨k, by omega⟩ * yM)

@[simp]
theorem krausN_zero :
    krausN 0 = (Complex.ofReal (1 / Real.sqrt 6)) • (1 : CMatrix (Fin 4)) := by
  rfl

theorem krausN_succ (k : Fin 7) :
    krausN ⟨(k : ℕ) + 1, by omega⟩ =
      (Complex.ofReal (Real.sqrt ((10 : ℝ) / 21))) • (tM k * yM) := by
  rfl

/-! ## Rational-normal-form identities

Paper Section 2: the finite identities `Y†Y = I`, `Yᵀ = −Y`, `T_kᵀ = T_k`,
`∑_k T_k†T_k = (7/4) I`, and `∑_ℓ K_ℓ†K_ℓ = I` (the last from
`1/6 + (10/21)(7/4) = 1`).  Each diagonal entry of `∑ T_k†T_k` is a sum of
rationals — every square root appears to an even power — so all five
identities live in the rational linear-combinants of the √-free normal
form; this is the design of `verify_simulator_exact.py` (exact arithmetic
over `Radical` values) and of plan §M5. -/

/-- `Y†Y = I₄`: the antidiagonal sign matrix is unitary (paper Section 2,
the identity used for `∑_ℓ K_ℓ†K_ℓ = I₄`).

Cross-reference: `verify_simulator_exact.py` (the Kraus completeness
assertion, 16 entries) and `check_channel_integration.py` line 39. -/
theorem yM_conjTranspose_mul_self :
    yM.conjTranspose * yM = (1 : CMatrix (Fin 4)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [yM, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ]

/-- `Yᵀ = −Y`: `Y` is antisymmetric (paper Section 2, "Since `Yᵀ = −Y`"). -/
theorem yM_transpose_neg : Matrix.transpose yM = -yM := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [yM, Matrix.transpose_apply]

/-- `T_kᵀ = T_k`: each `T_k` is symmetric (paper Section 2, "T_kᵀ = T_k"). -/
theorem tM_transpose (k : Fin 7) : Matrix.transpose (tM k) = tM k := by
  ext i j
  simp only [tM, Matrix.transpose_apply, Matrix.of_apply, Nat.add_comm, Nat.mul_comm]

/-- Every entry of a Clebsch--Gordan matrix is real. -/
theorem tM_star (k : Fin 7) (i j : Fin 4) : star (tM k i j) = tM k i j := by
  simp only [tM, Matrix.of_apply]
  split_ifs <;> simp only [Complex.star_def, Complex.conj_ofReal, map_zero]
/-- Entrywise symmetry of the matrices in eq:matrices. -/
theorem tM_symmetric_entry (k : Fin 7) (i j : Fin 4) : tM k i j = tM k j i := by
  exact congrFun (congrFun (tM_transpose k).symm i) j

/-- The finite identity `∑_{k=0}^6 T_k†T_k = (7/4) I₄` (paper Section 2,
used for the trace preservation of `𝓝`).

Each diagonal entry is the row sum
`∑_{j≤3} C(3,j)C(3,b)/C(6,j+b) = 7/4`, and the off-diagonal entries
vanish: a nonzero summand would need `j + b = j + d`. -/
theorem tM_sum :
    ∑ k : Fin 7, (tM k).conjTranspose * (tM k)
      = (7 / 4 : Complex) • (1 : CMatrix (Fin 4)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [tM, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ,
      Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Nat.choose, div_pow, ← pow_two,
      ← Complex.ofReal_pow, Real.sq_sqrt]
  all_goals norm_num [map_ofNat, ← pow_two, div_pow, ← Complex.ofReal_pow, Real.sq_sqrt]

private theorem real_smul_contraction {a b : Type*} [Fintype b]
    (r : ℝ) (M : Matrix b a ℂ) :
    ((r : ℂ) • M).conjTranspose * ((r : ℂ) • M) =
      ((r ^ 2 : ℝ) : ℂ) • (M.conjTranspose * M) := by
  rw [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  congr 1
  change (r : ℂ) * star (r : ℂ) = ↑(r ^ 2)
  rw [show star (r : ℂ) = (r : ℂ) from Complex.conj_ofReal r]
  norm_cast
  ring


/-- The Kraus completeness `∑_{ℓ=0}^7 K_ℓ†K_ℓ = I₄` (paper Section 2:
"1/6 + (10/21)(7/4) = 1"), the trace preservation of `𝓝`. -/
theorem krausN_sum :
    ∑ ℓ : Fin 8, (krausN ℓ).conjTranspose * (krausN ℓ) = (1 : CMatrix (Fin 4)) := by
  have hzero : (krausN 0).conjTranspose * krausN 0 =
      (1 / 6 : ℂ) • (1 : CMatrix (Fin 4)) := by
    rw [krausN_zero, real_smul_contraction]
    norm_num [div_pow, Real.sq_sqrt]
  have hsucc (k : Fin 7) : (krausN k.succ).conjTranspose * krausN k.succ =
      (10 / 21 : ℂ) • (yM.conjTranspose * ((tM k).conjTranspose * tM k) * yM) := by
    have hk : krausN k.succ =
        (Complex.ofReal (Real.sqrt ((10 : ℝ) / 21))) • (tM k * yM) := krausN_succ k
    rw [hk, real_smul_contraction, Real.sq_sqrt (by positivity)]
    norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat]
    rw [Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  rw [Fin.sum_univ_succ, hzero]
  simp_rw [hsucc]
  rw [← Finset.smul_sum, ← Matrix.sum_mul, ← Matrix.mul_sum, tM_sum,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, yM_conjTranspose_mul_self,
    smul_smul, ← add_smul]
  norm_num

/-- The Heisenberg adjoint of the Kraus family is unital; this is
`krausN_sum` unfolded through `MatrixMap.krausAdjoint`. -/
theorem krausN_krausAdjoint_one :
    MatrixMap.krausAdjoint krausN (1 : CMatrix (Fin 4)) = (1 : CMatrix (Fin 4)) := by
  show (∑ ℓ : Fin 8, (krausN ℓ).conjTranspose * (1 : CMatrix (Fin 4)) * krausN ℓ)
      = (1 : CMatrix (Fin 4))
  simp only [Matrix.mul_one]
  exact krausN_sum

/-! ## The channels `𝓝` and `𝓝ᶜ` (paper eq:channel, eq:complement) -/

/-- The channel `𝓝 : 4 → 4` of paper eq:channel, `𝓝(X) = ∑_ℓ K_ℓ X K_ℓ†`. -/
def Channel.privateN : Channel (Fin 4) (Fin 4) where
  map := MatrixMap.ofKraus krausN
  completelyPositive := MatrixMap.ofKraus_completelyPositive krausN
  tracePreserving :=
    MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one krausN krausN_krausAdjoint_one
  mapsPositive := MatrixMap.ofKraus_mapsPositive krausN

/-- Complete positivity of the complementary channel of a Kraus family
(the `MatrixMap.complementOfKraus` constructor of `QIT.Coding.Private.Basic`).

This instantiates the general complementary-channel theorem at `krausN`. -/
theorem complementN_completelyPositive :
    MatrixMap.IsCompletelyPositive (MatrixMap.complementOfKraus krausN) := by
  exact MatrixMap.complementOfKraus_completelyPositive krausN

/-- Trace preservation of the complement by trace cycling:
`Tr(𝓝ᶜ(X)) = ∑_ℓ Tr(K_ℓ X K_ℓ†) = Tr(𝓝(X)) = Tr(X)` (paper eq:complement;
the last step is `krausN_sum` through
`MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one`). -/
theorem complementN_isTracePreserving :
    MatrixMap.IsTracePreserving (MatrixMap.complementOfKraus krausN) := by
  intro X
  have hcomp_trace : (MatrixMap.complementOfKraus krausN X).trace
      = ∑ ℓ : Fin 8, (krausN ℓ * X * (krausN ℓ).conjTranspose).trace := by
    show (∑ ℓ : Fin 8, MatrixMap.complementOfKraus krausN X ℓ ℓ) = _
    exact Finset.sum_congr rfl fun ℓ _ => rfl
  have hN_trace : (MatrixMap.ofKraus krausN X).trace
      = ∑ ℓ : Fin 8, (krausN ℓ * X * (krausN ℓ).conjTranspose).trace := by
    simp [MatrixMap.ofKraus, Matrix.trace_sum]
  rw [hcomp_trace, ← hN_trace]
  exact MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one krausN
    krausN_krausAdjoint_one X

/-- The complementary channel `𝓝ᶜ : 4 → 8` of paper eq:complement, retained
in the Kraus-index basis `{|e_ℓ⟩}_{ℓ=0}^7`: `[𝓝ᶜ(X)]_{ℓm} = Tr(K_ℓ X K_m†)`. -/
def Channel.complementN : Channel (Fin 4) (Fin 8) where
  map := MatrixMap.complementOfKraus krausN
  completelyPositive := complementN_completelyPositive
  tracePreserving := complementN_isTracePreserving
  mapsPositive :=
    MatrixMap.isCompletelyPositive_mapsPositive _ complementN_completelyPositive

/-- `complementN` is a complement of `privateN` in the sense of
`Channel.IsComplementOf` (paper eq:complement): both arise from the one
Kraus family `krausN`.  Definitional. -/
theorem complementN_isComplementOf :
    Channel.IsComplementOf complementN privateN :=
  ⟨krausN, rfl, rfl⟩

private theorem real_smul_cov {a b : Type*} [Fintype a] (r : ℝ) (M : Matrix b a ℂ) :
    ((r : ℂ) • M) * ((r : ℂ) • M).conjTranspose =
      ((r ^ 2 : ℝ) : ℂ) • (M * M.conjTranspose) := by
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  change (r : ℂ) * star (r : ℂ) = ↑(r ^ 2)
  rw [show star (r : ℂ) = (r : ℂ) from Complex.conj_ofReal r]
  norm_cast
  ring

/-- The receiver branch constant `b = 𝓝(I₄)` of paper Section 3 (after
eq:half-gap): `𝓝` is unital, so `b = I₄` and `b/4 = I₄/4`. -/
theorem privateN_apply_one : privateN.map (1 : CMatrix (Fin 4)) = 1 := by
  have hy : yM * yM.conjTranspose = 1 := mul_eq_one_comm.mp yM_conjTranspose_mul_self
  have ht (k : Fin 7) : (tM k).conjTranspose = tM k := by
    ext i j
    change star (tM k j i) = tM k i j
    rw [tM_star, tM_symmetric_entry k j i]
  have hzero : krausN 0 * (krausN 0).conjTranspose =
      (1 / 6 : ℂ) • (1 : CMatrix (Fin 4)) := by
    rw [krausN_zero, real_smul_cov]
    norm_num [div_pow, Real.sq_sqrt]
  have hsucc (k : Fin 7) : krausN k.succ * (krausN k.succ).conjTranspose =
      (10 / 21 : ℂ) • ((tM k).conjTranspose * tM k) := by
    have hk : krausN k.succ =
        (Complex.ofReal (Real.sqrt ((10 : ℝ) / 21))) • (tM k * yM) := krausN_succ k
    rw [hk, real_smul_cov, Real.sq_sqrt (by positivity)]
    norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat]
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc yM,
      hy, Matrix.one_mul, ht]
  change (∑ ℓ, krausN ℓ * 1 * (krausN ℓ).conjTranspose) = 1
  simp only [Matrix.mul_one]
  rw [Fin.sum_univ_succ, hzero]
  simp_rw [hsucc]
  rw [← Finset.smul_sum, tM_sum, smul_smul, ← add_smul]
  norm_num

set_option maxHeartbeats 3000000 in
/-- The environment branch constant `e = 𝓝ᶜ(I₄)` of paper Section 3 and
`main.tex Appendix B` (the identity before cert:blocks):
`𝓝ᶜ(I₄) = (2/3)|e₀⟩⟨e₀| + (10/21) ∑_{k=0}^6 |e_{k+1}⟩⟨e_{k+1}|`. -/
theorem complementN_one_diagonal :
    complementN.map (1 : CMatrix (Fin 4))
      = Matrix.diagonal (fun ℓ : Fin 8 => if ℓ = 0 then 2 / 3 else 10 / 21) := by
  change (fun ℓ m => (krausN ℓ * 1 * (krausN m).conjTranspose).trace) = _
  simp only [Matrix.mul_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [krausN, tM, yM, Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.trace, Matrix.diagonal_apply,
      Fin.sum_univ_succ, Nat.choose, map_ofNat, ← pow_two, div_pow,
      ← Complex.ofReal_pow, Real.sq_sqrt] <;> ring_nf
  all_goals norm_num [smul_pow, Matrix.smul_apply, inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt]

/-! ## The transpose simulator `𝓓` (paper eq:transpose-criterion;
`main.tex Appendix A`)

The certificate realizes `𝓓(Z) = Tr_J(AZA†) + Tr_F(BZB†)` (cert:D) as the
Kraus map of the family `{K_j}_{j<4} ∪ {L_t}_{t<10}` obtained by reading
off the `J`- and `F`-marginals of `A` and `B`.  Entrywise (cert:Pi and the
displayed `A`, `B`):

* `(K_j)_{c,0} = δ_{c+j,3} (-1)^{3-c}/2`  (`A|e₀⟩ = |s⟩ = -vec(Y)/2`),
* `(K_j)_{c,k+1} = δ_{k,c+j} √(5 C(3,c)C(3,j)/(7 C(6,k)))`  (`A|e_{k+1}⟩ =
  √(5/7) ι|k⟩ = √(5/7) vec(T_k)`),
* `(L_t)_{c,0} = 0`  (`B|e₀⟩ = 0`),
* `(L_t)_{c,k+1} = δ_{t,k+3-c} (-1)^{3-c} √(C(3,c)C(6,k)/(5 C(9,t)))`
  (`B|e_{k+1}⟩ = (2/√5)(I⊗Π)(|s⟩⊗|k⟩)` with the cert:Pi coefficients).

These are `verify_simulator_exact.py` lines 85--96 verbatim (`amap`,
`bmap`). -/

/-- The `A`-part Kraus operators `K_j = (I_C ⊗ ⟨j|)A` of the simulator
certificate (cert:D), `j` ranging over the `J`-basis. -/
def simulatorKrausA (j : Fin 4) : Matrix (Fin 4) (Fin 8) Complex :=
  Matrix.of fun c ℓ =>
    match ℓ with
    | ⟨0, _⟩ => if (c : ℕ) + (j : ℕ) = 3 then (-1 : Complex) ^ (3 - (c : ℕ)) / 2 else 0
    | ⟨k + 1, _⟩ =>
      if (c : ℕ) + (j : ℕ) = k then
        Complex.ofReal (Real.sqrt
          (((5 : ℝ) * ((Nat.choose 3 c * Nat.choose 3 j : ℕ) : ℝ))
            / ((7 : ℝ) * ((Nat.choose 6 k : ℕ) : ℝ))))
      else 0

/-- The `B`-part Kraus operators `L_t = (I_C ⊗ ⟨t|)B` of the simulator
certificate (cert:D), `t` ranging over the `F`-basis (`dim F = 10`). -/
def simulatorKrausB (t : Fin 10) : Matrix (Fin 4) (Fin 8) Complex :=
  Matrix.of fun c ℓ =>
    match ℓ with
    | ⟨0, _⟩ => 0
    | ⟨k + 1, _⟩ =>
      if (t : ℕ) = (k : ℕ) + 3 - (c : ℕ) then
        (-1 : Complex) ^ (3 - (c : ℕ)) * Complex.ofReal (Real.sqrt
          (((Nat.choose 3 c * Nat.choose 6 k : ℕ) : ℝ)
            / ((5 : ℝ) * ((Nat.choose 9 t : ℕ) : ℝ))))
      else 0

/-- The full Kraus family of `𝓓`: the `Sum`-indexed union of the
`A`-part and the `B`-part (14 operators, `8 → 4`). -/
def simulatorKraus : Sum (Fin 4) (Fin 10) → Matrix (Fin 4) (Fin 8) Complex :=
  fun s =>
    match s with
    | Sum.inl j => simulatorKrausA j
    | Sum.inr t => simulatorKrausB t

set_option maxHeartbeats 3000000 in
/-- The trace-preservation certificate of `𝓓`: `∑ M†M = I₈`, i.e.
`A†A = 1 ⊕ (5/7)I₇` and `B†B = 0 ⊕ (2/7)I₇` (main.tex Appendix A,
the two displays before cert:binomial-TP).

The `(0,0)` entry is `4 · (1/2)² = 1`; the `(k+1,l+1)` entries are
`(5/7)δ_{kl}` (Vandermonde `∑_{c+j=k} C(3,c)C(3,j) = C(6,k)`) plus
`(2/7)δ_{kl}` (the binomial identity cert:binomial-TP,
`∑_j C(3,j)C(6,k)/C(9,j+k) = 10/7`); the mixed entries vanish because
`Y` is antisymmetric and `T_k` symmetric. -/
theorem simulatorKraus_krausAdjoint_one :
    MatrixMap.krausAdjoint simulatorKraus (1 : CMatrix (Fin 4)) = (1 : CMatrix (Fin 8)) := by
  change (∑ s, (simulatorKraus s).conjTranspose * 1 * simulatorKraus s) = 1
  simp only [Matrix.mul_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [simulatorKraus, simulatorKrausA, simulatorKrausB,
      Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_sum_type, Fin.sum_univ_succ, Nat.choose,
      map_ofNat, ← pow_two, div_pow, ← Complex.ofReal_pow, Real.sq_sqrt] <;> ring_nf
  all_goals norm_num [smul_pow, Matrix.smul_apply, inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt]

/-- The transpose simulator `𝓓 : 8 → 4` of paper eq:transpose-criterion /
main.tex Appendix A cert:D. -/
def Channel.simulatorD : Channel (Fin 8) (Fin 4) where
  map := MatrixMap.ofKraus simulatorKraus
  completelyPositive := MatrixMap.ofKraus_completelyPositive simulatorKraus
  tracePreserving :=
    MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one simulatorKraus
      simulatorKraus_krausAdjoint_one
  mapsPositive := MatrixMap.ofKraus_mapsPositive simulatorKraus

/-- The simulator is completely positive (its Kraus form;
main.tex Appendix A cert:D). -/
theorem simulatorD_completelyPositive :
    MatrixMap.IsCompletelyPositive simulatorD.map :=
  MatrixMap.ofKraus_completelyPositive simulatorKraus

/-- The simulator is trace preserving — the certificate's own
`A†A + B†B = I₈` identity (main.tex Appendix A, the paragraph
containing cert:binomial-TP). -/
theorem simulatorD_isTracePreserving :
    MatrixMap.IsTracePreserving simulatorD.map :=
  MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one simulatorKraus
    simulatorKraus_krausAdjoint_one

/-- The simulator maps states to states (positivity; consequence of the
Kraus form). -/
theorem simulatorD_mapsPositive :
    ∀ X : CMatrix (Fin 8), X.PosSemidef → (simulatorD.map X).PosSemidef :=
  MatrixMap.ofKraus_mapsPositive simulatorKraus

end
end QIT
