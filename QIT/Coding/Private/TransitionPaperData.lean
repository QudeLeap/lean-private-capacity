/-
Copyright (c) 2026 Chengkai Zhu.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chengkai Zhu
-/

module
public import QIT.Coding.Private.TransitionEncodingData

/-! # Literal manuscript formulas underlying the finite proof certificates

These auxiliary equalities bind the simulator table to the paper's vectors,
M, Q and reflection. They also check every error-detection identity. All finite
decisions are reduced in Lean's kernel, not an external evaluator.
-/

@[expose] public section
namespace QIT.TransitionPaperData
open TransitionData TransitionEncodingData

def vectors : Fin 7 → Fin 32 → ℚ :=
  ![![(1 / 2), 0, 0, 0, (-1 / 8), 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![(1 / 2), 0, 0, 0, (1 / 8), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 2, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]]

def m : Matrix (Fin 3) (Fin 3) ℚ :=
  ![![16, 8, 29],
    ![8, 64, 77],
    ![29, 77, 251]]

def l : Matrix (Fin 3) (Fin 3) ℚ :=
  ![![1, 0, 0],
    ![(1 / 2), 1, 0],
    ![(29 / 16), (25 / 24), 1]]

def pivots : Fin 3 → ℚ :=
  ![16, 60, (400 / 3)]

def permutation : Fin 8 → Fin 8 := ![0, 1, 3, 2, 5, 4, 7, 6]
def signs : Fin 8 → ℚ := ![1, -1, 1, 1, -1, -1, 1, 1]
def reflect (x : Fin 8 × Fin 4) : Fin 8 × Fin 4 :=
  (permutation x.1, ⟨3 - x.2.val, by omega⟩)
def reflection : Matrix (Fin 8 × Fin 4) (Fin 8 × Fin 4) ℚ :=
  fun x y ↦ if x = reflect y then signs y.1 else 0
def q (x y : Fin 8 × Fin 4) : ℚ :=
  (∑ i : Fin 3, ∑ j : Fin 3,
    vectors i.castSucc.castSucc.castSucc.castSucc (flat x) * m i j *
      vectors j.castSucc.castSucc.castSucc.castSucc (flat y)) +
    4 * (vectors 3 (flat x) * vectors 3 (flat y) +
         vectors 4 (flat x) * vectors 4 (flat y) + vectors 5 (flat x) * vectors 5 (flat y)) +
    51 * vectors 6 (flat x) * vectors 6 (flat y)

set_option maxRecDepth 10000
set_option maxHeartbeats 30000000

theorem m_ldl : l * Matrix.diagonal pivots * l.transpose = m := by
  ext i j
  revert i j
  decide +kernel

theorem pivots_pos : ∀ i, 0 < pivots i := by decide +kernel

theorem reflection_orthogonal : reflection * reflection.transpose = 1 := by
  ext x y
  revert x y
  decide +kernel

/-- The H table used by the actual CPTP simulator is exactly the manuscript's Q/reflection formula. -/
theorem simulator_formula (x y : Fin 8 × Fin 4) :
    h x y = (q x y + signs x.1 * signs y.1 * q (reflect x) (reflect y)) / 560 := by
  revert x y
  decide +kernel

def codeProjector : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℚ :=
  fun x y ↦ 2 * rho false x y + rho true x y

theorem codeProjector_idempotent :
    codeProjector * codeProjector = codeProjector := by
  ext x y
  revert x y
  decide +kernel

/-- All seven nonidentity errors are detected on the entire three-dimensional code space. -/
theorem error_detection (e : Fin 7) (x y : Fin 2 × Fin 4) :
    (∑ i : Fin 2 × Fin 4, ∑ j : Fin 2 × Fin 4,
      codeProjector x i * (if i.1 = j.1 then errors e.succ i.2 j.2 else 0) * codeProjector j y) = 0 := by
  revert e x y
  decide +kernel

end QIT.TransitionPaperData
