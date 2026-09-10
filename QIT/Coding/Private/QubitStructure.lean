/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team, Chengkai Zhu
-/

module

public import QIT.Coding.Private.QubitEvent

/-!
# The heralded three-vector receiver sector

The columns of `sectorEmbedding` are exactly the encoding vectors, and its
Gram matrix is the identity. The orthogonal projector onto their span obeys
`eq:sector-kraus`. Positivity and the full Kraus sum then prove `eq:heralded`
for every supported density state, including coherent superpositions.
These are direct finite-algebra proofs; the spin representation labels in
the manuscript are not asserted as formalized here.
-/

@[expose] public section
open scoped ComplexOrder MatrixOrder
namespace QIT.QubitActivation
open Channel SimulatorCanonical
noncomputable section

def sectorEmbedding : Matrix RA (Fin 3) ℂ := fun x j => phi j x

theorem sectorEmbedding_isometry : sectorEmbedding.conjTranspose * sectorEmbedding = 1 := by
  ext i j
  simpa [sectorEmbedding, Matrix.mul_apply, Matrix.conjTranspose_apply, mul_comm,
    Matrix.one_apply, eq_comm] using phi_inner j i

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 4000 in
private theorem sector_compressed_kraus_canonical (e : Fin 8) :
    sectorEmbedding.conjTranspose * receiverKraus e * sectorEmbedding =
      if e = 0 then (r2 * r3 / 6) • (1 : CMatrix (Fin 3)) else 0 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, sectorEmbedding,
    receiverKraus, Fintype.sum_prod_type, ← ks_eq,
    ← phiCanonical_eq]
  fin_cases e <;> fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.one_apply, ks, phiCanonical, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.cons_val, map_ofNat] <;> ring_nf
  all_goals (norm_num; ring)

private theorem sectorScale_eq : r2 * r3 / 6 = (Real.sqrt 6 : ℂ)⁻¹ := by
  simp only [r2, r3, ← Complex.ofReal_mul, ← Complex.ofReal_div,
    ← Complex.ofReal_inv, ← Complex.ofReal_ofNat, Complex.ofReal_inj]
  apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
  norm_num [mul_pow, div_pow, inv_pow, Real.sq_sqrt]

theorem sector_compressed_kraus (e : Fin 8) :
    sectorEmbedding.conjTranspose * receiverKraus e * sectorEmbedding =
      if e = 0 then (Real.sqrt 6 : ℂ)⁻¹ • (1 : CMatrix (Fin 3)) else 0 := by
  simpa only [sectorScale_eq] using sector_compressed_kraus_canonical e


def sectorProjector : CMatrix RA := sectorEmbedding * sectorEmbedding.conjTranspose

theorem sectorProjector_hermitian : sectorProjector.IsHermitian := by
  simp [sectorProjector, Matrix.IsHermitian, Matrix.conjTranspose_mul]

theorem sectorProjector_idempotent : sectorProjector * sectorProjector = sectorProjector := by
  calc
    _ = sectorEmbedding * (sectorEmbedding.conjTranspose * sectorEmbedding) *
        sectorEmbedding.conjTranspose := by simp [sectorProjector, Matrix.mul_assoc]
    _ = sectorProjector := by rw [sectorEmbedding_isometry]; simp [sectorProjector]

theorem sector_kraus (e : Fin 8) :
    sectorProjector * receiverKraus e * sectorProjector =
      if e = 0 then (Real.sqrt 6 : ℂ)⁻¹ • sectorProjector else 0 := by
  calc
    _ = sectorEmbedding * (sectorEmbedding.conjTranspose * receiverKraus e * sectorEmbedding) *
        sectorEmbedding.conjTranspose := by simp [sectorProjector, Matrix.mul_assoc]
    _ = _ := by
      rw [sector_compressed_kraus]
      split_ifs <;> simp [sectorProjector, Matrix.mul_smul, Matrix.smul_mul]


private theorem receiverKraus_zero : receiverKraus 0 = (r2 * r3 / 6) • (1 : CMatrix RA) := by
  ext ⟨r, a⟩ ⟨s, b⟩
  fin_cases r <;> fin_cases s <;> fin_cases a <;> fin_cases b <;>
    norm_num [receiverKraus, ← ks_eq, ks, Matrix.one_apply] <;> ring

def sectorNoise (rho : State RA) : CMatrix RA :=
  ∑ k : Fin 7, receiverKraus k.succ * rho.matrix * (receiverKraus k.succ).conjTranspose

theorem sectorNoise_pos (rho : State RA) : (sectorNoise rho).PosSemidef := by
  exact Matrix.posSemidef_sum _ (fun k _ => rho.pos.mul_mul_conjTranspose_same _)

theorem receiver_sector_decomposition (rho : State RA) :
    referencedReceiver.map rho.matrix = (1 / 6 : ℂ) • rho.matrix + sectorNoise rho := by
  rw [referencedReceiver_map]
  change (∑ e : Fin 8, receiverKraus e * rho.matrix * (receiverKraus e).conjTranspose) = _
  rw [Fin.sum_univ_succ, receiverKraus_zero]
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.smul_mul,
    Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul]
  have hc : star (r2 * r3 / 6) * (r2 * r3 / 6) = (1 / 6 : ℂ) := by
    simp only [star_div₀, star_mul, r2_star, r3_star]
    ring_nf
    norm_num
  rw [hc]
  rfl

theorem sectorNoise_orthogonal (rho : State RA)
    (h : sectorProjector * rho.matrix * sectorProjector = rho.matrix) :
    sectorProjector * sectorNoise rho = 0 := by
  unfold sectorNoise
  rw [Matrix.mul_sum]
  apply Finset.sum_eq_zero
  intro k _
  have hk : sectorProjector * receiverKraus k.succ * sectorProjector = 0 := by
    simpa using sector_kraus k.succ
  calc
    _ = sectorProjector * receiverKraus k.succ *
        (sectorProjector * rho.matrix * sectorProjector) *
          (receiverKraus k.succ).conjTranspose := by simp only [h, Matrix.mul_assoc]
    _ = 0 := by
      simp only [← Matrix.mul_assoc, hk, Matrix.zero_mul]

/-- The heralded identity sector, for every density state supported on the three-vector span. -/
theorem receiver_heralded (rho : State RA)
    (h : sectorProjector * rho.matrix * sectorProjector = rho.matrix) :
    ∃ noise : CMatrix RA, noise.PosSemidef ∧ sectorProjector * noise = 0 ∧
      noise * sectorProjector = 0 ∧
      referencedReceiver.map rho.matrix = (1 / 6 : ℂ) • rho.matrix + noise := by
  refine ⟨sectorNoise rho, sectorNoise_pos rho, sectorNoise_orthogonal rho h, ?_,
    receiver_sector_decomposition rho⟩
  have he := congrArg Matrix.conjTranspose (sectorNoise_orthogonal rho h)
  simpa only [Matrix.conjTranspose_mul, (sectorNoise_pos rho).isHermitian.eq,
    sectorProjector_hermitian.eq, Matrix.conjTranspose_zero] using he


theorem sectorProjector_phi (j : Fin 3) : sectorProjector.mulVec (phi j) = phi j := by
  have h : sectorProjector * sectorEmbedding = sectorEmbedding := by
    calc
      _ = sectorEmbedding * (sectorEmbedding.conjTranspose * sectorEmbedding) := by
        simp [sectorProjector, Matrix.mul_assoc]
      _ = sectorEmbedding := by rw [sectorEmbedding_isometry, Matrix.mul_one]
  funext x
  exact congrFun (congrFun h x) j

theorem sectorProjector_pure (j : Fin 3) :
    sectorProjector * rankOneMatrix (phi j) * sectorProjector = rankOneMatrix (phi j) := by
  have h := rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose sectorProjector (phi j)
  rw [sectorProjector_phi, sectorProjector_hermitian.eq] at h
  exact h.symm

theorem rho0_sector_support : sectorProjector * rho0.matrix * sectorProjector = rho0.matrix := by
  change sectorProjector * ((1 / 2 : ℂ) •
    (rankOneMatrix (phi 0) + rankOneMatrix (phi 1))) * sectorProjector = _
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
    sectorProjector_pure, sectorProjector_pure]
  rfl

theorem rho1_sector_support : sectorProjector * rho1.matrix * sectorProjector = rho1.matrix :=
  sectorProjector_pure 2

end
end QIT.QubitActivation
