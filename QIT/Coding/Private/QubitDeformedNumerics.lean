/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team, Chengkai Zhu
-/

module

public import QIT.Coding.Private.QubitEntropyIntervals

/-!
# Rational interval certificate for the deformed example's entropy expression

Every arithmetic inequality is checked by the Lean kernel. The root variables
are defined using the intermediate value theorem, with complete polynomial root
lists proved below. Physical matrix correspondence is supplied separately.
-/

@[expose] public section
namespace QIT.QubitActivation
noncomputable section
open Polynomial Finset

set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

theorem deformed_log_two_bounds :
    (69314718055994530941723 / 100000000000000000000000) ≤ Real.log 2 ∧ Real.log 2 ≤
      (2772588722239781237669 / 4000000000000000000000) := by
  have h := log_atanh_interval (1 / 3) (by norm_num) (by norm_num) 24
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_log_0 :
    (-38826663895539968901 / 15625000000000000000) ≤ Real.log (56084051 / 673008504) ∧ Real.log
      (56084051 / 673008504) ≤ (-2484906489314558009663 / 1000000000000000000000) := by
  have h := log_scaled_interval (56084051 / 673008504) (by norm_num) 4 24 (28042039 / 196294165)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_entropy_0_m_0 :
    (298746903708183233067 / 1000000000000000000000) ≤ -xlog2 ((56084051 / 673008504)) ∧ -xlog2
      ((56084051 / 673008504)) ≤ (74686725927045808267 / 250000000000000000000) := by
  have h := entropy_term_interval (x := (56084051 / 673008504)) (a := (56084051 / 673008504)) (b :=
    (56084051 / 673008504))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_0.1 deformed_log_0.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_entropy_0_m_1 :
    (298746903708183233067 / 1000000000000000000000) ≤ -xlog2 ((56084051 / 673008504)) ∧ -xlog2
      ((56084051 / 673008504)) ≤ (74686725927045808267 / 250000000000000000000) := by
  have h := entropy_term_interval (x := (56084051 / 673008504)) (a := (56084051 / 673008504)) (b :=
    (56084051 / 673008504))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_0.1 deformed_log_0.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_log_1 :
    (-466524523255783528057 / 250000000000000000000) ≤ Real.log (104132057 / 673008504) ∧ Real.log
      (104132057 / 673008504) ≤ (-1866098093023134112227 / 1000000000000000000000) := by
  have h := log_scaled_interval (104132057 / 673008504) (by norm_num) 3 24 (10002997 / 94129060)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_entropy_0_m_2 :
    (208277764613116926967 / 500000000000000000000) ≤ -xlog2 ((104132057 / 673008504)) ∧ -xlog2
      ((104132057 / 673008504)) ≤ (26034720576639615871 / 62500000000000000000) := by
  have h := entropy_term_interval (x := (104132057 / 673008504)) (a := (104132057 / 673008504)) (b
    := (104132057 / 673008504))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_1.1 deformed_log_1.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_entropy_0_m_3 :
    (208277764613116926967 / 500000000000000000000) ≤ -xlog2 ((104132057 / 673008504)) ∧ -xlog2
      ((104132057 / 673008504)) ≤ (26034720576639615871 / 62500000000000000000) := by
  have h := entropy_term_interval (x := (104132057 / 673008504)) (a := (104132057 / 673008504)) (b
    := (104132057 / 673008504))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_1.1 deformed_log_1.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_log_2 :
    (-486602505993037916417 / 250000000000000000000) ≤ Real.log (4004001 / 28042021) ∧ Real.log
      (4004001 / 28042021) ≤ (-1946410023972151665667 / 1000000000000000000000) := by
  have h := log_scaled_interval (4004001 / 28042021) (by norm_num) 3 24 (3989987 / 60074029)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_entropy_0_m_4 :
    (200476625221080539459 / 500000000000000000000) ≤ -xlog2 ((4004001 / 28042021)) ∧ -xlog2
      ((4004001 / 28042021)) ≤ (10023831261054026973 / 25000000000000000000) := by
  have h := entropy_term_interval (x := (4004001 / 28042021)) (a := (4004001 / 28042021)) (b :=
    (4004001 / 28042021))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_2.1 deformed_log_2.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_log_3 :
    (-17149214693139618484439 / 1000000000000000000000) ≤ Real.log (1 / 28042021) ∧ Real.log (1 /
      28042021) ≤ (-8574607346569809242219 / 500000000000000000000) := by
  have h := log_scaled_interval (1 / 28042021) (by norm_num) 25 24 (5512411 / 61596453)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_entropy_0_m_5 :
    (27571442462337 / 31250000000000000000) ≤ -xlog2 ((1 / 28042021)) ∧ -xlog2 ((1 / 28042021)) ≤
      (176457231758957 / 200000000000000000000) := by
  have h := entropy_term_interval (x := (1 / 28042021)) (a := (1 / 28042021)) (b := (1 / 28042021))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_3.1 deformed_log_3.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_log_4 :
    (-414463380369238266387 / 250000000000000000000) ≤ Real.log (16030015 / 84126063) ∧ Real.log
      (16030015 / 84126063) ≤ (-1657853521476953065547 / 1000000000000000000000) := by
  have h := log_scaled_interval (16030015 / 84126063) (by norm_num) 3 24 (44114057 / 212366183)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_entropy_0_m_6 :
    (113936813052680650547 / 250000000000000000000) ≤ -xlog2 ((16030015 / 84126063)) ∧ -xlog2
      ((16030015 / 84126063)) ≤ (455747252210722602189 / 1000000000000000000000) := by
  have h := entropy_term_interval (x := (16030015 / 84126063)) (a := (16030015 / 84126063)) (b :=
    (16030015 / 84126063))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_4.1 deformed_log_4.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_entropy_0_m_7 :
    (113936813052680650547 / 250000000000000000000) ≤ -xlog2 ((16030015 / 84126063)) ∧ -xlog2
      ((16030015 / 84126063)) ≤ (455747252210722602189 / 1000000000000000000000) := by
  have h := entropy_term_interval (x := (16030015 / 84126063)) (a := (16030015 / 84126063)) (b :=
    (16030015 / 84126063))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_4.1 deformed_log_4.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_log_5 :
    (-615964816306740036897 / 500000000000000000000) ≤ Real.log (3506003 / 12018009) ∧ Real.log
      (3506003 / 12018009) ≤ (-1231929632613480073793 / 1000000000000000000000) := by
  have h := log_scaled_interval (3506003 / 12018009) (by norm_num) 2 24 (2006003 / 26042021)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_entropy_0_b_0 :
    (1296224446466381189 / 2500000000000000000) ≤ -xlog2 ((3506003 / 12018009)) ∧ -xlog2 ((3506003 /
      12018009)) ≤ (518489778586552475601 / 1000000000000000000000) := by
  have h := entropy_term_interval (x := (3506003 / 12018009)) (a := (3506003 / 12018009)) (b :=
    (3506003 / 12018009))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_5.1 deformed_log_5.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_log_6 :
    (-392228915764455052133 / 250000000000000000000) ≤ Real.log (5006003 / 24036018) ∧ Real.log
      (5006003 / 24036018) ≤ (-1568915663057820208531 / 1000000000000000000000) := by
  have h := log_scaled_interval (5006003 / 24036018) (by norm_num) 3 24 (8006003 / 32042021)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_entropy_0_b_1 :
    (9428285354764857083 / 20000000000000000000) ≤ -xlog2 ((5006003 / 24036018)) ∧ -xlog2 ((5006003
      / 24036018)) ≤ (58926783467280356769 / 125000000000000000000) := by
  have h := entropy_term_interval (x := (5006003 / 24036018)) (a := (5006003 / 24036018)) (b :=
    (5006003 / 24036018))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_6.1 deformed_log_6.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_entropy_0_b_2 :
    (9428285354764857083 / 20000000000000000000) ≤ -xlog2 ((5006003 / 24036018)) ∧ -xlog2 ((5006003
      / 24036018)) ≤ (58926783467280356769 / 125000000000000000000) := by
  have h := entropy_term_interval (x := (5006003 / 24036018)) (a := (5006003 / 24036018)) (b :=
    (5006003 / 24036018))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_6.1 deformed_log_6.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_entropy_0_b_3 :
    (1296224446466381189 / 2500000000000000000) ≤ -xlog2 ((3506003 / 12018009)) ∧ -xlog2 ((3506003 /
      12018009)) ≤ (518489778586552475601 / 1000000000000000000000) := by
  have h := entropy_term_interval (x := (3506003 / 12018009)) (a := (3506003 / 12018009)) (b :=
    (3506003 / 12018009))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_5.1 deformed_log_5.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_log_7 :
    (-1791759469228055000813 / 1000000000000000000000) ≤ Real.log (1 / 6) ∧ Real.log (1 / 6) ≤
      (-447939867307013750203 / 250000000000000000000) := by
  have h := log_scaled_interval (1 / 6) (by norm_num) 3 24 (1 / 7)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_entropy_0_e_0 :
    (215413541726763015121 / 500000000000000000000) ≤ -xlog2 ((1 / 6)) ∧ -xlog2 ((1 / 6)) ≤
      (430827083453526030243 / 1000000000000000000000) := by
  have h := entropy_term_interval (x := (1 / 6)) (a := (1 / 6)) (b := (1 / 6))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_7.1 deformed_log_7.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_log_8 :
    (-1722267222075076939397 / 1000000000000000000000) ≤ Real.log (715715 / 4006003) ∧ Real.log
      (715715 / 4006003) ≤ (-344453444415015387879 / 200000000000000000000) := by
  have h := log_scaled_interval (715715 / 4006003) (by norm_num) 3 24 (1719717 / 9731723)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_entropy_0_e_1 :
    (110979798756322322873 / 250000000000000000000) ≤ -xlog2 ((715715 / 4006003)) ∧ -xlog2 ((715715
      / 4006003)) ≤ (443919195025289291493 / 1000000000000000000000) := by
  have h := entropy_term_interval (x := (715715 / 4006003)) (a := (715715 / 4006003)) (b := (715715
    / 4006003))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_8.1 deformed_log_8.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_log_9 :
    (-1064115852924633965659 / 500000000000000000000) ≤ Real.log (5 / 42) ∧ Real.log (5 / 42) ≤
      (-2128231705849267931317 / 1000000000000000000000) := by
  have h := log_scaled_interval (5 / 42) (by norm_num) 4 24 (19 / 61)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_entropy_0_e_2 :
    (182761269517345115537 / 500000000000000000000) ≤ -xlog2 ((5 / 42)) ∧ -xlog2 ((5 / 42)) ≤
      (14620901561387609243 / 40000000000000000000) := by
  have h := entropy_term_interval (x := (5 / 42)) (a := (5 / 42)) (b := (5 / 42))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_9.1 deformed_log_9.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_log_10 :
    (-2485549070863854447527 / 1000000000000000000000) ≤ Real.log (7006003 / 84126063) ∧ Real.log
      (7006003 / 84126063) ≤ (-1242774535431927223763 / 500000000000000000000) := by
  have h := log_scaled_interval (7006003 / 84126063) (by norm_num) 4 24 (27969985 / 196222111)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_entropy_0_e_3 :
    (298632200612177209229 / 1000000000000000000000) ≤ -xlog2 ((7006003 / 84126063)) ∧ -xlog2
      ((7006003 / 84126063)) ≤ (29863220061217720923 / 100000000000000000000) := by
  have h := entropy_term_interval (x := (7006003 / 84126063)) (a := (7006003 / 84126063)) (b :=
    (7006003 / 84126063))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_10.1 deformed_log_10.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_log_11 :
    (-1320028414849358386501 / 500000000000000000000) ≤ Real.log (4002001 / 56084042) ∧ Real.log
      (4002001 / 56084042) ≤ (-2640056829698716773001 / 1000000000000000000000) := by
  have h := log_scaled_interval (4002001 / 56084042) (by norm_num) 4 24 (3973987 / 60058029)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_entropy_0_e_4 :
    (135892568032758300631 / 500000000000000000000) ≤ -xlog2 ((4002001 / 56084042)) ∧ -xlog2
      ((4002001 / 56084042)) ≤ (271785136065516601263 / 1000000000000000000000) := by
  have h := entropy_term_interval (x := (4002001 / 56084042)) (a := (4002001 / 56084042)) (b :=
    (4002001 / 56084042))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_11.1 deformed_log_11.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_entropy_0_e_5 :
    (298632200612177209229 / 1000000000000000000000) ≤ -xlog2 ((7006003 / 84126063)) ∧ -xlog2
      ((7006003 / 84126063)) ≤ (29863220061217720923 / 100000000000000000000) := by
  have h := entropy_term_interval (x := (7006003 / 84126063)) (a := (7006003 / 84126063)) (b :=
    (7006003 / 84126063))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_10.1 deformed_log_10.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_entropy_0_e_6 :
    (182761269517345115537 / 500000000000000000000) ≤ -xlog2 ((5 / 42)) ∧ -xlog2 ((5 / 42)) ≤
      (14620901561387609243 / 40000000000000000000) := by
  have h := entropy_term_interval (x := (5 / 42)) (a := (5 / 42)) (b := (5 / 42))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_9.1 deformed_log_9.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_entropy_0_e_7 :
    (110979798756322322873 / 250000000000000000000) ≤ -xlog2 ((715715 / 4006003)) ∧ -xlog2 ((715715
      / 4006003)) ≤ (443919195025289291493 / 1000000000000000000000) := by
  have h := entropy_term_interval (x := (715715 / 4006003)) (a := (715715 / 4006003)) (b := (715715
    / 4006003))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_8.1 deformed_log_8.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

def deformed_numeric_poly_0_0 : ℝ[X] := C 1 * X ^ 3 + C (-14018009 / 84126063) * X ^ 2 + C
  (12302598322018 / 7077194475879969) * X ^ 1

def deformed_root_0_0_0 : ℝ := 0

theorem deformed_root_0_0_0_eval : deformed_numeric_poly_0_0.eval deformed_root_0_0_0 = 0 := by
  norm_num [deformed_root_0_0_0, deformed_numeric_poly_0_0]

theorem deformed_root_0_0_1_exists :
    ∃ x ∈ Set.Icc ((11182785926577943562721 / 1000000000000000000000000) : ℝ)
      (5591392963288971781361 / 500000000000000000000000), deformed_numeric_poly_0_0.eval x = 0 :=
      by
  apply polynomial_root_in_interval _ _ _ (by norm_num)
  apply Or.inr
  norm_num [deformed_numeric_poly_0_0]

def deformed_root_0_0_1 : ℝ := Classical.choose deformed_root_0_0_1_exists

theorem deformed_root_0_0_1_bounds : (11182785926577943562721 / 1000000000000000000000000) ≤
  deformed_root_0_0_1 ∧ deformed_root_0_0_1 ≤ (5591392963288971781361 / 500000000000000000000000) :=
  (Classical.choose_spec deformed_root_0_0_1_exists).1

theorem deformed_root_0_0_1_eval : deformed_numeric_poly_0_0.eval deformed_root_0_0_1 = 0 :=
  (Classical.choose_spec deformed_root_0_0_1_exists).2

theorem deformed_log_12 :
    (-44933796538736749769 / 10000000000000000000) ≤ Real.log (11182785926577943562721 /
      1000000000000000000000000) ∧ Real.log (11182785926577943562721 / 1000000000000000000000000) ≤
      (-4493379653873674976899 / 1000000000000000000000) := by
  have h := log_scaled_interval (11182785926577943562721 / 1000000000000000000000000) (by norm_num)
    7 24 (3370285926577943562721 / 18995285926577943562721)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_log_13 :
    (-44933796538736749769 / 10000000000000000000) ≤ Real.log (5591392963288971781361 /
      500000000000000000000000) ∧ Real.log (5591392963288971781361 / 500000000000000000000000) ≤
      (-4493379653873674976899 / 1000000000000000000000) := by
  have h := log_scaled_interval (5591392963288971781361 / 500000000000000000000000) (by norm_num) 7
    24 (1685142963288971781361 / 9497642963288971781361)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_root_0_0_1_entropy :
    (72493265738335600881 / 1000000000000000000000) ≤ -xlog2 (deformed_root_0_0_1) ∧ -xlog2
      (deformed_root_0_0_1) ≤ (36246632869167800441 / 500000000000000000000) := by
  have h := entropy_term_interval (x := deformed_root_0_0_1) (a := (11182785926577943562721 /
    1000000000000000000000000)) (b := (5591392963288971781361 / 500000000000000000000000))
    (by norm_num) deformed_root_0_0_1_bounds.1 deformed_root_0_0_1_bounds.2 (by norm_num)
    deformed_log_12.1 deformed_log_13.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_root_0_0_2_exists :
    ∃ x ∈ Set.Icc ((38862050535471957559193 / 250000000000000000000000) : ℝ)
      (155448202141887830236773 / 1000000000000000000000000), deformed_numeric_poly_0_0.eval x = 0
      := by
  apply polynomial_root_in_interval _ _ _ (by norm_num)
  apply Or.inl
  norm_num [deformed_numeric_poly_0_0]

def deformed_root_0_0_2 : ℝ := Classical.choose deformed_root_0_0_2_exists

theorem deformed_root_0_0_2_bounds : (38862050535471957559193 / 250000000000000000000000) ≤
  deformed_root_0_0_2 ∧ deformed_root_0_0_2 ≤ (155448202141887830236773 / 1000000000000000000000000)
  :=
  (Classical.choose_spec deformed_root_0_0_2_exists).1

theorem deformed_root_0_0_2_eval : deformed_numeric_poly_0_0.eval deformed_root_0_0_2 = 0 :=
  (Classical.choose_spec deformed_root_0_0_2_exists).2

theorem deformed_log_14 :
    (-1861442708051570570507 / 1000000000000000000000) ≤ Real.log (38862050535471957559193 /
      250000000000000000000000) ∧ Real.log (38862050535471957559193 / 250000000000000000000000) ≤
      (-930721354025785285253 / 500000000000000000000) := by
  have h := log_scaled_interval (38862050535471957559193 / 250000000000000000000000) (by norm_num) 3
    24 (7612050535471957559193 / 70112050535471957559193)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_log_15 :
    (-1861442708051570570507 / 1000000000000000000000) ≤ Real.log (155448202141887830236773 /
      1000000000000000000000000) ∧ Real.log (155448202141887830236773 / 1000000000000000000000000) ≤
      (-930721354025785285253 / 500000000000000000000) := by
  have h := log_scaled_interval (155448202141887830236773 / 1000000000000000000000000) (by norm_num)
    3 24 (30448202141887830236773 / 280448202141887830236773)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_root_0_0_2_entropy :
    (104363809906501939493 / 250000000000000000000) ≤ -xlog2 (deformed_root_0_0_2) ∧ -xlog2
      (deformed_root_0_0_2) ≤ (417455239626007757973 / 1000000000000000000000) := by
  have h := entropy_term_interval (x := deformed_root_0_0_2) (a := (38862050535471957559193 /
    250000000000000000000000)) (b := (155448202141887830236773 / 1000000000000000000000000))
    (by norm_num) deformed_root_0_0_2_bounds.1 deformed_root_0_0_2_bounds.2 (by norm_num)
    deformed_log_14.1 deformed_log_15.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

def deformed_roots_0_0 : Fin 3 → ℝ := ![deformed_root_0_0_0, deformed_root_0_0_1,
  deformed_root_0_0_2]

theorem deformed_roots_0_0_complete :
    deformed_numeric_poly_0_0.roots = Multiset.map deformed_roots_0_0 Finset.univ.val := by
  apply polynomial_roots_complete
  · intro h
    have h1 := congrArg (fun p : ℝ[X] ↦ p.eval 1) h
    norm_num [deformed_numeric_poly_0_0] at h1
  · unfold deformed_numeric_poly_0_0
    compute_degree
  · intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [deformed_roots_0_0] at hij ⊢
    all_goals
      have h0 := deformed_root_0_0_0_eval
      have h1 := deformed_root_0_0_1_bounds
      have h2 := deformed_root_0_0_2_bounds
      norm_num [deformed_root_0_0_0] at *
      linarith
  · intro i
    fin_cases i
    · exact deformed_root_0_0_0_eval
    · exact deformed_root_0_0_1_eval
    · exact deformed_root_0_0_2_eval

def deformed_numeric_poly_0_2 : ℝ[X] := C 1 * X ^ 2 + C (-17530015 / 84126063) * X ^ 1

def deformed_root_0_2_0 : ℝ := 0

theorem deformed_root_0_2_0_eval : deformed_numeric_poly_0_2.eval deformed_root_0_2_0 = 0 := by
  norm_num [deformed_root_0_2_0, deformed_numeric_poly_0_2]

def deformed_root_0_2_1 : ℝ := (17530015 / 84126063)

theorem deformed_root_0_2_1_eval : deformed_numeric_poly_0_2.eval deformed_root_0_2_1 = 0 := by
  norm_num [deformed_root_0_2_1, deformed_numeric_poly_0_2]

theorem deformed_log_16 :
    (-784200934617346502149 / 500000000000000000000) ≤ Real.log (17530015 / 84126063) ∧ Real.log
      (17530015 / 84126063) ≤ (-1568401869234693004297 / 1000000000000000000000) := by
  have h := log_scaled_interval (17530015 / 84126063) (by norm_num) 3 24 (56114057 / 224366183)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_root_0_2_1_entropy :
    (471502080027241025799 / 1000000000000000000000) ≤ -xlog2 (deformed_root_0_2_1) ∧ -xlog2
      (deformed_root_0_2_1) ≤ (2357510400136205129 / 5000000000000000000) := by
  have h := entropy_term_interval (x := deformed_root_0_2_1) (a := (17530015 / 84126063)) (b :=
    (17530015 / 84126063))
    (by norm_num) (by norm_num [deformed_root_0_2_1]) (by norm_num [deformed_root_0_2_1]) (by
      norm_num)
    deformed_log_16.1 deformed_log_16.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

def deformed_roots_0_2 : Fin 2 → ℝ := ![deformed_root_0_2_0, deformed_root_0_2_1]

theorem deformed_roots_0_2_complete :
    deformed_numeric_poly_0_2.roots = Multiset.map deformed_roots_0_2 Finset.univ.val := by
  apply polynomial_roots_complete
  · intro h
    have h1 := congrArg (fun p : ℝ[X] ↦ p.eval 1) h
    norm_num [deformed_numeric_poly_0_2] at h1
  · unfold deformed_numeric_poly_0_2
    compute_degree
  · intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [deformed_roots_0_2] at hij ⊢
    all_goals
      have h0 := deformed_root_0_2_0_eval
      norm_num [deformed_root_0_2_0, deformed_root_0_2_1] at *
  · intro i
    fin_cases i
    · exact deformed_root_0_2_0_eval
    · exact deformed_root_0_2_1_eval

def deformed_numeric_poly_0_3 : ℝ[X] := C 1 * X ^ 2 + C (-7010005 / 56084042) * X ^ 1

def deformed_root_0_3_0 : ℝ := 0

theorem deformed_root_0_3_0_eval : deformed_numeric_poly_0_3.eval deformed_root_0_3_0 = 0 := by
  norm_num [deformed_root_0_3_0, deformed_numeric_poly_0_3]

def deformed_root_0_3_1 : ℝ := (7010005 / 56084042)

theorem deformed_root_0_3_1_eval : deformed_numeric_poly_0_3.eval deformed_root_0_3_1 = 0 := by
  norm_num [deformed_root_0_3_1, deformed_numeric_poly_0_3]

theorem deformed_log_17 :
    (-1039756450711141786499 / 500000000000000000000) ≤ Real.log (7010005 / 56084042) ∧ Real.log
      (7010005 / 56084042) ≤ (-2079512901422283572997 / 1000000000000000000000) := by
  have h := log_scaled_interval (7010005 / 56084042) (by norm_num) 4 24 (28038019 / 84122061)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_root_0_3_1_entropy :
    (187493054463193429703 / 500000000000000000000) ≤ -xlog2 (deformed_root_0_3_1) ∧ -xlog2
      (deformed_root_0_3_1) ≤ (374986108926386859407 / 1000000000000000000000) := by
  have h := entropy_term_interval (x := deformed_root_0_3_1) (a := (7010005 / 56084042)) (b :=
    (7010005 / 56084042))
    (by norm_num) (by norm_num [deformed_root_0_3_1]) (by norm_num [deformed_root_0_3_1]) (by
      norm_num)
    deformed_log_17.1 deformed_log_17.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

def deformed_roots_0_3 : Fin 2 → ℝ := ![deformed_root_0_3_0, deformed_root_0_3_1]

theorem deformed_roots_0_3_complete :
    deformed_numeric_poly_0_3.roots = Multiset.map deformed_roots_0_3 Finset.univ.val := by
  apply polynomial_roots_complete
  · intro h
    have h1 := congrArg (fun p : ℝ[X] ↦ p.eval 1) h
    norm_num [deformed_numeric_poly_0_3] at h1
  · unfold deformed_numeric_poly_0_3
    compute_degree
  · intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [deformed_roots_0_3] at hij ⊢
    all_goals
      have h0 := deformed_root_0_3_0_eval
      norm_num [deformed_root_0_3_0, deformed_root_0_3_1] at *
  · intro i
    fin_cases i
    · exact deformed_root_0_3_0_eval
    · exact deformed_root_0_3_1_eval

theorem deformed_log_18 :
    (-2512277685628546858161 / 1000000000000000000000) ≤ Real.log (7772331089 / 95856072000) ∧
      Real.log (7772331089 / 95856072000) ≤ (-31403471070356835727 / 12500000000000000000) := by
  have h := log_scaled_interval (7772331089 / 95856072000) (by norm_num) 4 24 (1781326589 /
    13763335589)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_entropy_1_m_0 :
    (73470645019587115301 / 250000000000000000000) ≤ -xlog2 ((7772331089 / 95856072000)) ∧ -xlog2
      ((7772331089 / 95856072000)) ≤ (58776516015669692241 / 200000000000000000000) := by
  have h := entropy_term_interval (x := (7772331089 / 95856072000)) (a := (7772331089 /
    95856072000)) (b := (7772331089 / 95856072000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_18.1 deformed_log_18.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_entropy_1_m_1 :
    (73470645019587115301 / 250000000000000000000) ≤ -xlog2 ((7772331089 / 95856072000)) ∧ -xlog2
      ((7772331089 / 95856072000)) ≤ (58776516015669692241 / 200000000000000000000) := by
  have h := entropy_term_interval (x := (7772331089 / 95856072000)) (a := (7772331089 /
    95856072000)) (b := (7772331089 / 95856072000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_18.1 deformed_log_18.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_log_19 :
    (-1859432740475475793827 / 1000000000000000000000) ≤ Real.log (104514438053 / 670992504000) ∧
      Real.log (104514438053 / 670992504000) ≤ (-929716370237737896913 / 500000000000000000000) :=
      by
  have h := log_scaled_interval (104514438053 / 670992504000) (by norm_num) 3 24 (20640375053 /
    188388501053)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_entropy_1_m_2 :
    (417843483935646792673 / 1000000000000000000000) ≤ -xlog2 ((104514438053 / 670992504000)) ∧
      -xlog2 ((104514438053 / 670992504000)) ≤ (16713739357425871707 / 40000000000000000000) := by
  have h := entropy_term_interval (x := (104514438053 / 670992504000)) (a := (104514438053 /
    670992504000)) (b := (104514438053 / 670992504000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_19.1 deformed_log_19.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_entropy_1_m_3 :
    (417843483935646792673 / 1000000000000000000000) ≤ -xlog2 ((104514438053 / 670992504000)) ∧
      -xlog2 ((104514438053 / 670992504000)) ≤ (16713739357425871707 / 40000000000000000000) := by
  have h := entropy_term_interval (x := (104514438053 / 670992504000)) (a := (104514438053 /
    670992504000)) (b := (104514438053 / 670992504000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_19.1 deformed_log_19.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_log_20 :
    (-1932020317689912588703 / 1000000000000000000000) ≤ Real.log (8099732189 / 55916042000) ∧
      Real.log (8099732189 / 55916042000) ≤ (-966010158844956294351 / 500000000000000000000) := by
  have h := log_scaled_interval (8099732189 / 55916042000) (by norm_num) 3 24 (1110226939 /
    15089237439)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_entropy_1_m_4 :
    (403757372330216567847 / 1000000000000000000000) ≤ -xlog2 ((8099732189 / 55916042000)) ∧ -xlog2
      ((8099732189 / 55916042000)) ≤ (50469671541277070981 / 125000000000000000000) := by
  have h := entropy_term_interval (x := (8099732189 / 55916042000)) (a := (8099732189 /
    55916042000)) (b := (8099732189 / 55916042000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_20.1 deformed_log_20.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_log_21 :
    (-2701835074209310603797 / 500000000000000000000) ≤ Real.log (7189261 / 1597601200) ∧ Real.log
      (7189261 / 1597601200) ≤ (-5403670148418621207593 / 1000000000000000000000) := by
  have h := log_scaled_interval (7189261 / 1597601200) (by norm_num) 8 24 (15178101 / 214878251)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_entropy_1_m_5 :
    (17540793939121173767 / 500000000000000000000) ≤ -xlog2 ((7189261 / 1597601200)) ∧ -xlog2
      ((7189261 / 1597601200)) ≤ (7016317575648469507 / 200000000000000000000) := by
  have h := entropy_term_interval (x := (7189261 / 1597601200)) (a := (7189261 / 1597601200)) (b :=
    (7189261 / 1597601200))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_21.1 deformed_log_21.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_log_22 :
    (-1668773727174605862001 / 1000000000000000000000) ≤ Real.log (6323367919 / 33549625200) ∧
      Real.log (6323367919 / 33549625200) ≤ (-834386863587302931 / 500000000000000000) := by
  have h := log_scaled_interval (6323367919 / 33549625200) (by norm_num) 3 24 (2129664769 /
    10517071069)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_entropy_1_m_6 :
    (453766856402802257173 / 1000000000000000000000) ≤ -xlog2 ((6323367919 / 33549625200)) ∧ -xlog2
      ((6323367919 / 33549625200)) ≤ (226883428201401128587 / 500000000000000000000) := by
  have h := entropy_term_interval (x := (6323367919 / 33549625200)) (a := (6323367919 /
    33549625200)) (b := (6323367919 / 33549625200))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_22.1 deformed_log_22.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_entropy_1_m_7 :
    (453766856402802257173 / 1000000000000000000000) ≤ -xlog2 ((6323367919 / 33549625200)) ∧ -xlog2
      ((6323367919 / 33549625200)) ≤ (226883428201401128587 / 500000000000000000000) := by
  have h := entropy_term_interval (x := (6323367919 / 33549625200)) (a := (6323367919 /
    33549625200)) (b := (6323367919 / 33549625200))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_22.1 deformed_log_22.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_log_23 :
    (-248798750822714911287 / 200000000000000000000) ≤ Real.log (6907167919 / 23964018000) ∧
      Real.log (6907167919 / 23964018000) ≤ (-621996877056787278217 / 500000000000000000000) := by
  have h := log_scaled_interval (6907167919 / 23964018000) (by norm_num) 2 24 (916163419 /
    12898172419)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_entropy_1_b_0 :
    (517288848133760159121 / 1000000000000000000000) ≤ -xlog2 ((6907167919 / 23964018000)) ∧ -xlog2
      ((6907167919 / 23964018000)) ≤ (258644424066880079561 / 500000000000000000000) := by
  have h := entropy_term_interval (x := (6907167919 / 23964018000)) (a := (6907167919 /
    23964018000)) (b := (6907167919 / 23964018000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_23.1 deformed_log_23.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_log_24 :
    (-1552258244999201644937 / 1000000000000000000000) ≤ Real.log (5074841081 / 23964018000) ∧
      Real.log (5074841081 / 23964018000) ≤ (-194032280624900205617 / 125000000000000000000) := by
  have h := log_scaled_interval (5074841081 / 23964018000) (by norm_num) 3 24 (2079338831 /
    8070343331)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_entropy_1_b_1 :
    (474243431039014054623 / 1000000000000000000000) ≤ -xlog2 ((5074841081 / 23964018000)) ∧ -xlog2
      ((5074841081 / 23964018000)) ≤ (14820107219969189207 / 31250000000000000000) := by
  have h := entropy_term_interval (x := (5074841081 / 23964018000)) (a := (5074841081 /
    23964018000)) (b := (5074841081 / 23964018000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_24.1 deformed_log_24.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_entropy_1_b_2 :
    (474243431039014054623 / 1000000000000000000000) ≤ -xlog2 ((5074841081 / 23964018000)) ∧ -xlog2
      ((5074841081 / 23964018000)) ≤ (14820107219969189207 / 31250000000000000000) := by
  have h := entropy_term_interval (x := (5074841081 / 23964018000)) (a := (5074841081 /
    23964018000)) (b := (5074841081 / 23964018000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_24.1 deformed_log_24.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_entropy_1_b_3 :
    (517288848133760159121 / 1000000000000000000000) ≤ -xlog2 ((6907167919 / 23964018000)) ∧ -xlog2
      ((6907167919 / 23964018000)) ≤ (258644424066880079561 / 500000000000000000000) := by
  have h := entropy_term_interval (x := (6907167919 / 23964018000)) (a := (6907167919 /
    23964018000)) (b := (6907167919 / 23964018000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_23.1 deformed_log_23.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_entropy_1_e_0 :
    (215413541726763015121 / 500000000000000000000) ≤ -xlog2 ((1 / 6)) ∧ -xlog2 ((1 / 6)) ≤
      (430827083453526030243 / 1000000000000000000000) := by
  have h := entropy_term_interval (x := (1 / 6)) (a := (1 / 6)) (b := (1 / 6))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_7.1 deformed_log_7.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_log_25 :
    (-175063842020454339999 / 100000000000000000000) ≤ Real.log (138722139 / 798800600) ∧ Real.log
      (138722139 / 798800600) ≤ (-1750638420204543399989 / 1000000000000000000000) := by
  have h := log_scaled_interval (138722139 / 798800600) (by norm_num) 3 24 (19436032 / 119286107)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_entropy_1_e_1 :
    (219304929114298489211 / 500000000000000000000) ≤ -xlog2 ((138722139 / 798800600)) ∧ -xlog2
      ((138722139 / 798800600)) ≤ (54826232278574622303 / 125000000000000000000) := by
  have h := entropy_term_interval (x := (138722139 / 798800600)) (a := (138722139 / 798800600)) (b
    := (138722139 / 798800600))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_25.1 deformed_log_25.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_entropy_1_e_2 :
    (182761269517345115537 / 500000000000000000000) ≤ -xlog2 ((5 / 42)) ∧ -xlog2 ((5 / 42)) ≤
      (14620901561387609243 / 40000000000000000000) := by
  have h := entropy_term_interval (x := (5 / 42)) (a := (5 / 42)) (b := (5 / 42))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_9.1 deformed_log_9.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_log_26 :
    (-2450176376969039519281 / 1000000000000000000000) ≤ Real.log (7236517243 / 83874063000) ∧
      Real.log (7236517243 / 83874063000) ≤ (-30627204712112993991 / 12500000000000000000) := by
  have h := log_scaled_interval (7236517243 / 83874063000) (by norm_num) 4 24 (3988776611 /
    24957292361)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_entropy_1_e_3 :
    (152490859203199265281 / 500000000000000000000) ≤ -xlog2 ((7236517243 / 83874063000)) ∧ -xlog2
      ((7236517243 / 83874063000)) ≤ (304981718406398530563 / 1000000000000000000000) := by
  have h := entropy_term_interval (x := (7236517243 / 83874063000)) (a := (7236517243 /
    83874063000)) (b := (7236517243 / 83874063000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_26.1 deformed_log_26.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_log_27 :
    (-1292770616220826383213 / 500000000000000000000) ≤ Real.log (263348076 / 3494752625) ∧ Real.log
      (263348076 / 3494752625) ≤ (-103421649297666110657 / 40000000000000000000) := by
  have h := log_scaled_interval (263348076 / 3494752625) (by norm_num) 4 24 (718816591 / 7708321841)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_entropy_1_e_4 :
    (140543162339455785673 / 500000000000000000000) ≤ -xlog2 ((263348076 / 3494752625)) ∧ -xlog2
      ((263348076 / 3494752625)) ≤ (281086324678911571347 / 1000000000000000000000) := by
  have h := entropy_term_interval (x := (263348076 / 3494752625)) (a := (263348076 / 3494752625)) (b
    := (263348076 / 3494752625))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_27.1 deformed_log_27.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_entropy_1_e_5 :
    (152490859203199265281 / 500000000000000000000) ≤ -xlog2 ((7236517243 / 83874063000)) ∧ -xlog2
      ((7236517243 / 83874063000)) ≤ (304981718406398530563 / 1000000000000000000000) := by
  have h := entropy_term_interval (x := (7236517243 / 83874063000)) (a := (7236517243 /
    83874063000)) (b := (7236517243 / 83874063000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_26.1 deformed_log_26.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_entropy_1_e_6 :
    (182761269517345115537 / 500000000000000000000) ≤ -xlog2 ((5 / 42)) ∧ -xlog2 ((5 / 42)) ≤
      (14620901561387609243 / 40000000000000000000) := by
  have h := entropy_term_interval (x := (5 / 42)) (a := (5 / 42)) (b := (5 / 42))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_9.1 deformed_log_9.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_entropy_1_e_7 :
    (219304929114298489211 / 500000000000000000000) ≤ -xlog2 ((138722139 / 798800600)) ∧ -xlog2
      ((138722139 / 798800600)) ≤ (54826232278574622303 / 125000000000000000000) := by
  have h := entropy_term_interval (x := (138722139 / 798800600)) (a := (138722139 / 798800600)) (b
    := (138722139 / 798800600))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_25.1 deformed_log_25.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

def deformed_numeric_poly_1_0 : ℝ[X] := C 1 * X ^ 3 + C (-512834333 / 2995502250) * X ^ 2 + C
  (586692895082722331 / 200995955546513400000) * X ^ 1 + C (-390728756889 / 15952059964009000000000)

theorem deformed_root_1_0_0_exists :
    ∃ x ∈ Set.Icc ((4195708522406633 / 500000000000000000000000) : ℝ) (8391417044813267 /
      1000000000000000000000000), deformed_numeric_poly_1_0.eval x = 0 := by
  apply polynomial_root_in_interval _ _ _ (by norm_num)
  apply Or.inl
  norm_num [deformed_numeric_poly_1_0]

def deformed_root_1_0_0 : ℝ := Classical.choose deformed_root_1_0_0_exists

theorem deformed_root_1_0_0_bounds : (4195708522406633 / 500000000000000000000000) ≤
  deformed_root_1_0_0 ∧ deformed_root_1_0_0 ≤ (8391417044813267 / 1000000000000000000000000) :=
  (Classical.choose_spec deformed_root_1_0_0_exists).1

theorem deformed_root_1_0_0_eval : deformed_numeric_poly_1_0.eval deformed_root_1_0_0 = 0 :=
  (Classical.choose_spec deformed_root_1_0_0_exists).2

theorem deformed_log_28 :
    (-18596056433849952423009 / 1000000000000000000000) ≤ Real.log (4195708522406633 /
      500000000000000000000000) ∧ Real.log (4195708522406633 / 500000000000000000000000) ≤
      (-18596056433849952423007 / 1000000000000000000000) := by
  have h := log_scaled_interval (4195708522406633 / 500000000000000000000000) (by norm_num) 27 24
    (7526691583115503 / 126735981133896753)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_log_29 :
    (-116225352711562201899 / 6250000000000000000) ≤ Real.log (8391417044813267 /
      1000000000000000000000000) ∧ Real.log (8391417044813267 / 1000000000000000000000000) ≤
      (-9298028216924976151919 / 500000000000000000000) := by
  have h := log_scaled_interval (8391417044813267 / 1000000000000000000000000) (by norm_num) 27 24
    (7526691583115511 / 126735981133896761)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_root_1_0_0_entropy :
    (112564307626021 / 500000000000000000000) ≤ -xlog2 (deformed_root_1_0_0) ∧ -xlog2
      (deformed_root_1_0_0) ≤ (225128615252043 / 1000000000000000000000) := by
  have h := entropy_term_interval (x := deformed_root_1_0_0) (a := (4195708522406633 /
    500000000000000000000000)) (b := (8391417044813267 / 1000000000000000000000000))
    (by norm_num) deformed_root_1_0_0_bounds.1 deformed_root_1_0_0_bounds.2 (by norm_num)
    deformed_log_28.1 deformed_log_29.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_root_1_0_1_exists :
    ∃ x ∈ Set.Icc ((192037629819495976777 / 10000000000000000000000) : ℝ) (19203762981949597677701 /
      1000000000000000000000000), deformed_numeric_poly_1_0.eval x = 0 := by
  apply polynomial_root_in_interval _ _ _ (by norm_num)
  apply Or.inr
  norm_num [deformed_numeric_poly_1_0]

def deformed_root_1_0_1 : ℝ := Classical.choose deformed_root_1_0_1_exists

theorem deformed_root_1_0_1_bounds : (192037629819495976777 / 10000000000000000000000) ≤
  deformed_root_1_0_1 ∧ deformed_root_1_0_1 ≤ (19203762981949597677701 / 1000000000000000000000000)
  :=
  (Classical.choose_spec deformed_root_1_0_1_exists).1

theorem deformed_root_1_0_1_eval : deformed_numeric_poly_1_0.eval deformed_root_1_0_1 = 0 :=
  (Classical.choose_spec deformed_root_1_0_1_exists).2

theorem deformed_log_30 :
    (-197632451525422903441 / 50000000000000000000) ≤ Real.log (192037629819495976777 /
      10000000000000000000000) ∧ Real.log (192037629819495976777 / 10000000000000000000000) ≤
      (-1976324515254229034409 / 500000000000000000000) := by
  have h := log_scaled_interval (192037629819495976777 / 10000000000000000000000) (by norm_num) 6 24
    (35787629819495976777 / 348287629819495976777)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_log_31 :
    (-3952649030508458068819 / 1000000000000000000000) ≤ Real.log (19203762981949597677701 /
      1000000000000000000000000) ∧ Real.log (19203762981949597677701 / 1000000000000000000000000) ≤
      (-1976324515254229034409 / 500000000000000000000) := by
  have h := log_scaled_interval (19203762981949597677701 / 1000000000000000000000000) (by norm_num)
    6 24 (3578762981949597677701 / 34828762981949597677701)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_root_1_0_1_entropy :
    (13688603456375300161 / 125000000000000000000) ≤ -xlog2 (deformed_root_1_0_1) ∧ -xlog2
      (deformed_root_1_0_1) ≤ (109508827651002401289 / 1000000000000000000000) := by
  have h := entropy_term_interval (x := deformed_root_1_0_1) (a := (192037629819495976777 /
    10000000000000000000000)) (b := (19203762981949597677701 / 1000000000000000000000000))
    (by norm_num) deformed_root_1_0_1_bounds.1 deformed_root_1_0_1_bounds.2 (by norm_num)
    deformed_log_30.1 deformed_log_31.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_root_1_0_2_exists :
    ∃ x ∈ Set.Icc ((151997680069375555415911 / 1000000000000000000000000) : ℝ)
      (18999710008671944426989 / 125000000000000000000000), deformed_numeric_poly_1_0.eval x = 0 :=
      by
  apply polynomial_root_in_interval _ _ _ (by norm_num)
  apply Or.inl
  norm_num [deformed_numeric_poly_1_0]

def deformed_root_1_0_2 : ℝ := Classical.choose deformed_root_1_0_2_exists

theorem deformed_root_1_0_2_bounds : (151997680069375555415911 / 1000000000000000000000000) ≤
  deformed_root_1_0_2 ∧ deformed_root_1_0_2 ≤ (18999710008671944426989 / 125000000000000000000000)
  :=
  (Classical.choose_spec deformed_root_1_0_2_exists).1

theorem deformed_root_1_0_2_eval : deformed_numeric_poly_1_0.eval deformed_root_1_0_2 = 0 :=
  (Classical.choose_spec deformed_root_1_0_2_exists).2

theorem deformed_log_32 :
    (-470972505238453371561 / 250000000000000000000) ≤ Real.log (151997680069375555415911 /
      1000000000000000000000000) ∧ Real.log (151997680069375555415911 / 1000000000000000000000000) ≤
      (-1883890020953813486243 / 1000000000000000000000) := by
  have h := log_scaled_interval (151997680069375555415911 / 1000000000000000000000000) (by norm_num)
    3 24 (26997680069375555415911 / 276997680069375555415911)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_log_33 :
    (-470972505238453371561 / 250000000000000000000) ≤ Real.log (18999710008671944426989 /
      125000000000000000000000) ∧ Real.log (18999710008671944426989 / 125000000000000000000000) ≤
      (-1883890020953813486243 / 1000000000000000000000) := by
  have h := log_scaled_interval (18999710008671944426989 / 125000000000000000000000) (by norm_num) 3
    24 (3374710008671944426989 / 34624710008671944426989)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_root_1_0_2_entropy :
    (20655563545646051333 / 50000000000000000000) ≤ -xlog2 (deformed_root_1_0_2) ∧ -xlog2
      (deformed_root_1_0_2) ≤ (206555635456460513331 / 500000000000000000000) := by
  have h := entropy_term_interval (x := deformed_root_1_0_2) (a := (151997680069375555415911 /
    1000000000000000000000000)) (b := (18999710008671944426989 / 125000000000000000000000))
    (by norm_num) deformed_root_1_0_2_bounds.1 deformed_root_1_0_2_bounds.2 (by norm_num)
    deformed_log_32.1 deformed_log_33.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

def deformed_roots_1_0 : Fin 3 → ℝ := ![deformed_root_1_0_0, deformed_root_1_0_1,
  deformed_root_1_0_2]

theorem deformed_roots_1_0_complete :
    deformed_numeric_poly_1_0.roots = Multiset.map deformed_roots_1_0 Finset.univ.val := by
  apply polynomial_roots_complete
  · intro h
    have h1 := congrArg (fun p : ℝ[X] ↦ p.eval 1) h
    norm_num [deformed_numeric_poly_1_0] at h1
  · unfold deformed_numeric_poly_1_0
    compute_degree
  · intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [deformed_roots_1_0] at hij ⊢
    all_goals
      have h0 := deformed_root_1_0_0_bounds
      have h1 := deformed_root_1_0_1_bounds
      have h2 := deformed_root_1_0_2_bounds
      linarith
  · intro i
    fin_cases i
    · exact deformed_root_1_0_0_eval
    · exact deformed_root_1_0_1_eval
    · exact deformed_root_1_0_2_eval

def deformed_numeric_poly_1_2 : ℝ[X] := C 1 * X ^ 2 + C (-485666417 / 2396401800) * X ^ 1

def deformed_root_1_2_0 : ℝ := 0

theorem deformed_root_1_2_0_eval : deformed_numeric_poly_1_2.eval deformed_root_1_2_0 = 0 := by
  norm_num [deformed_root_1_2_0, deformed_numeric_poly_1_2]

def deformed_root_1_2_1 : ℝ := (485666417 / 2396401800)

theorem deformed_root_1_2_1_eval : deformed_numeric_poly_1_2.eval deformed_root_1_2_1 = 0 := by
  norm_num [deformed_root_1_2_1, deformed_numeric_poly_1_2]

theorem deformed_log_34 :
    (-1596201637879221637669 / 1000000000000000000000) ≤ Real.log (485666417 / 2396401800) ∧
      Real.log (485666417 / 2396401800) ≤ (-399050409469805409417 / 250000000000000000000) := by
  have h := log_scaled_interval (485666417 / 2396401800) (by norm_num) 3 24 (93058096 / 392608321)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_root_1_2_1_entropy :
    (466703145241713841937 / 1000000000000000000000) ≤ -xlog2 (deformed_root_1_2_1) ∧ -xlog2
      (deformed_root_1_2_1) ≤ (233351572620856920969 / 500000000000000000000) := by
  have h := entropy_term_interval (x := deformed_root_1_2_1) (a := (485666417 / 2396401800)) (b :=
    (485666417 / 2396401800))
    (by norm_num) (by norm_num [deformed_root_1_2_1]) (by norm_num [deformed_root_1_2_1]) (by
      norm_num)
    deformed_log_34.1 deformed_log_34.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

def deformed_roots_1_2 : Fin 2 → ℝ := ![deformed_root_1_2_0, deformed_root_1_2_1]

theorem deformed_roots_1_2_complete :
    deformed_numeric_poly_1_2.roots = Multiset.map deformed_roots_1_2 Finset.univ.val := by
  apply polynomial_roots_complete
  · intro h
    have h1 := congrArg (fun p : ℝ[X] ↦ p.eval 1) h
    norm_num [deformed_numeric_poly_1_2] at h1
  · unfold deformed_numeric_poly_1_2
    compute_degree
  · intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [deformed_roots_1_2] at hij ⊢
    all_goals
      have h0 := deformed_root_1_2_0_eval
      norm_num [deformed_root_1_2_0, deformed_root_1_2_1] at *
  · intro i
    fin_cases i
    · exact deformed_root_1_2_0_eval
    · exact deformed_root_1_2_1_eval

def deformed_numeric_poly_1_3 : ℝ[X] := C 1 * X ^ 2 + C (-503778361 / 3994003000) * X ^ 1 + C (1251
  / 11183208400000)

theorem deformed_root_1_3_0_exists :
    ∃ x ∈ Set.Icc ((221717401944517 / 250000000000000000000000) : ℝ) (886869607778069 /
      1000000000000000000000000), deformed_numeric_poly_1_3.eval x = 0 := by
  apply polynomial_root_in_interval _ _ _ (by norm_num)
  apply Or.inr
  norm_num [deformed_numeric_poly_1_3]

def deformed_root_1_3_0 : ℝ := Classical.choose deformed_root_1_3_0_exists

theorem deformed_root_1_3_0_bounds : (221717401944517 / 250000000000000000000000) ≤
  deformed_root_1_3_0 ∧ deformed_root_1_3_0 ≤ (886869607778069 / 1000000000000000000000000) :=
  (Classical.choose_spec deformed_root_1_3_0_exists).1

theorem deformed_root_1_3_0_eval : deformed_numeric_poly_1_3.eval deformed_root_1_3_0 = 0 :=
  (Classical.choose_spec deformed_root_1_3_0_exists).2

theorem deformed_log_35 :
    (-416866462961149081121 / 20000000000000000000) ≤ Real.log (221717401944517 /
      250000000000000000000000) ∧ Real.log (221717401944517 / 250000000000000000000000) ≤
      (-1302707696753590878503 / 62500000000000000000) := by
  have h := log_scaled_interval (221717401944517 / 250000000000000000000000) (by norm_num) 31 24
    (53914665020202079 / 173123954570983329)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_log_36 :
    (-20843323148057452928489 / 1000000000000000000000) ≤ Real.log (886869607778069 /
      1000000000000000000000000) ∧ Real.log (886869607778069 / 1000000000000000000000000) ≤
      (-20843323148057452928487 / 1000000000000000000000) := by
  have h := log_scaled_interval (886869607778069 / 1000000000000000000000000) (by norm_num) 31 24
    (53914665020202207 / 173123954570983457)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_root_1_3_0_entropy :
    (26668664813981 / 1000000000000000000000) ≤ -xlog2 (deformed_root_1_3_0) ∧ -xlog2
      (deformed_root_1_3_0) ≤ (13334332406991 / 500000000000000000000) := by
  have h := entropy_term_interval (x := deformed_root_1_3_0) (a := (221717401944517 /
    250000000000000000000000)) (b := (886869607778069 / 1000000000000000000000000))
    (by norm_num) deformed_root_1_3_0_bounds.1 deformed_root_1_3_0_bounds.2 (by norm_num)
    deformed_log_35.1 deformed_log_36.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_root_1_3_1_exists :
    ∃ x ∈ Set.Icc ((7883355956696829689499 / 62500000000000000000000) : ℝ) (25226739061429855006397
      / 200000000000000000000000), deformed_numeric_poly_1_3.eval x = 0 := by
  apply polynomial_root_in_interval _ _ _ (by norm_num)
  apply Or.inl
  norm_num [deformed_numeric_poly_1_3]

def deformed_root_1_3_1 : ℝ := Classical.choose deformed_root_1_3_1_exists

theorem deformed_root_1_3_1_bounds : (7883355956696829689499 / 62500000000000000000000) ≤
  deformed_root_1_3_1 ∧ deformed_root_1_3_1 ≤ (25226739061429855006397 / 200000000000000000000000)
  :=
  (Classical.choose_spec deformed_root_1_3_1_exists).1

theorem deformed_root_1_3_1_eval : deformed_numeric_poly_1_3.eval deformed_root_1_3_1 = 0 :=
  (Classical.choose_spec deformed_root_1_3_1_exists).2

theorem deformed_log_37 :
    (-1035206430352686640323 / 500000000000000000000) ≤ Real.log (7883355956696829689499 /
      62500000000000000000000) ∧ Real.log (7883355956696829689499 / 62500000000000000000000) ≤
      (-414082572141074656129 / 200000000000000000000) := by
  have h := log_scaled_interval (7883355956696829689499 / 62500000000000000000000) (by norm_num) 3
    24 (70855956696829689499 / 15695855956696829689499)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_log_38 :
    (-1035206430352686640323 / 500000000000000000000) ≤ Real.log (25226739061429855006397 /
      200000000000000000000000) ∧ Real.log (25226739061429855006397 / 200000000000000000000000) ≤
      (-414082572141074656129 / 200000000000000000000) := by
  have h := log_scaled_interval (25226739061429855006397 / 200000000000000000000000) (by norm_num) 3
    24 (226739061429855006397 / 50226739061429855006397)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_root_1_3_1_entropy :
    (376758114663686445833 / 1000000000000000000000) ≤ -xlog2 (deformed_root_1_3_1) ∧ -xlog2
      (deformed_root_1_3_1) ≤ (188379057331843222917 / 500000000000000000000) := by
  have h := entropy_term_interval (x := deformed_root_1_3_1) (a := (7883355956696829689499 /
    62500000000000000000000)) (b := (25226739061429855006397 / 200000000000000000000000))
    (by norm_num) deformed_root_1_3_1_bounds.1 deformed_root_1_3_1_bounds.2 (by norm_num)
    deformed_log_37.1 deformed_log_38.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

def deformed_roots_1_3 : Fin 2 → ℝ := ![deformed_root_1_3_0, deformed_root_1_3_1]

theorem deformed_roots_1_3_complete :
    deformed_numeric_poly_1_3.roots = Multiset.map deformed_roots_1_3 Finset.univ.val := by
  apply polynomial_roots_complete
  · intro h
    have h1 := congrArg (fun p : ℝ[X] ↦ p.eval 1) h
    norm_num [deformed_numeric_poly_1_3] at h1
  · unfold deformed_numeric_poly_1_3
    compute_degree
  · intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [deformed_roots_1_3] at hij ⊢
    all_goals
      have h0 := deformed_root_1_3_0_bounds
      have h1 := deformed_root_1_3_1_bounds
      linarith
  · intro i
    fin_cases i
    · exact deformed_root_1_3_0_eval
    · exact deformed_root_1_3_1_eval

theorem deformed_log_39 :
    (-1244990923546465913509 / 500000000000000000000) ≤ Real.log (3565853898150061607 /
      43007967744024192000) ∧ Real.log (3565853898150061607 / 43007967744024192000) ≤
      (-311247730886616478377 / 125000000000000000000) := by
  have h := log_scaled_interval (3565853898150061607 / 43007967744024192000) (by norm_num) 4 24
    (877855914148549607 / 6253851882151573607)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_entropy_2_m_0 :
    (297841591372999360157 / 1000000000000000000000) ≤ -xlog2 ((3565853898150061607 /
      43007967744024192000)) ∧ -xlog2 ((3565853898150061607 / 43007967744024192000)) ≤
      (148920795686499680079 / 500000000000000000000) := by
  have h := entropy_term_interval (x := (3565853898150061607 / 43007967744024192000)) (a :=
    (3565853898150061607 / 43007967744024192000)) (b := (3565853898150061607 /
    43007967744024192000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_39.1 deformed_log_39.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_entropy_2_m_1 :
    (297841591372999360157 / 1000000000000000000000) ≤ -xlog2 ((3565853898150061607 /
      43007967744024192000)) ∧ -xlog2 ((3565853898150061607 / 43007967744024192000)) ≤
      (148920795686499680079 / 500000000000000000000) := by
  have h := entropy_term_interval (x := (3565853898150061607 / 43007967744024192000)) (a :=
    (3565853898150061607 / 43007967744024192000)) (b := (3565853898150061607 /
    43007967744024192000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_39.1 deformed_log_39.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_log_40 :
    (-1864844950638046445517 / 1000000000000000000000) ≤ Real.log (6662804181855119477 /
      43007967744024192000) ∧ Real.log (6662804181855119477 / 43007967744024192000) ≤
      (-466211237659511611379 / 250000000000000000000) := by
  have h := log_scaled_interval (6662804181855119477 / 43007967744024192000) (by norm_num) 3 24
    (1286808213852095477 / 12038800149858143477)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_entropy_2_m_2 :
    (104199444796708901103 / 250000000000000000000) ≤ -xlog2 ((6662804181855119477 /
      43007967744024192000)) ∧ -xlog2 ((6662804181855119477 / 43007967744024192000)) ≤
      (416797779186835604413 / 1000000000000000000000) := by
  have h := entropy_term_interval (x := (6662804181855119477 / 43007967744024192000)) (a :=
    (6662804181855119477 / 43007967744024192000)) (b := (6662804181855119477 /
    43007967744024192000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_40.1 deformed_log_40.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_entropy_2_m_3 :
    (104199444796708901103 / 250000000000000000000) ≤ -xlog2 ((6662804181855119477 /
      43007967744024192000)) ∧ -xlog2 ((6662804181855119477 / 43007967744024192000)) ≤
      (416797779186835604413 / 1000000000000000000000) := by
  have h := entropy_term_interval (x := (6662804181855119477 / 43007967744024192000)) (a :=
    (6662804181855119477 / 43007967744024192000)) (b := (6662804181855119477 /
    43007967744024192000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_40.1 deformed_log_40.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_log_41 :
    (-971848067155783959957 / 500000000000000000000) ≤ Real.log (73304920928724243 /
      511999616000288000) ∧ Real.log (73304920928724243 / 511999616000288000) ≤
      (-1943696134311567919913 / 1000000000000000000000) := by
  have h := log_scaled_interval (73304920928724243 / 511999616000288000) (by norm_num) 3 24
    (9304968928688243 / 137304872928760243)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_entropy_2_m_4 :
    (80296460146922320351 / 200000000000000000000) ≤ -xlog2 ((73304920928724243 /
      511999616000288000)) ∧ -xlog2 ((73304920928724243 / 511999616000288000)) ≤
      (401482300734611601757 / 1000000000000000000000) := by
  have h := entropy_term_interval (x := (73304920928724243 / 511999616000288000)) (a :=
    (73304920928724243 / 511999616000288000)) (b := (73304920928724243 / 511999616000288000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_41.1 deformed_log_41.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_log_42 :
    (-7077612242846826528423 / 1000000000000000000000) ≤ Real.log (604824992625043 /
      716799462400403200) ∧ Real.log (604824992625043 / 716799462400403200) ≤
      (-3538806121423413264211 / 500000000000000000000) := by
  have h := log_scaled_interval (604824992625043 / 716799462400403200) (by norm_num) 11 24
    (2038602040998769 / 7638597841001919)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_entropy_2_m_5 :
    (8615755428406780843 / 1000000000000000000000) ≤ -xlog2 ((604824992625043 / 716799462400403200))
      ∧ -xlog2 ((604824992625043 / 716799462400403200)) ≤ (2153938857101695211 /
      250000000000000000000) := by
  have h := entropy_term_interval (x := (604824992625043 / 716799462400403200)) (a :=
    (604824992625043 / 716799462400403200)) (b := (604824992625043 / 716799462400403200))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_42.1 deformed_log_42.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_log_43 :
    (-829945998569412866127 / 500000000000000000000) ≤ Real.log (408918718161087271 /
      2150398387201209600) ∧ Real.log (408918718161087271 / 2150398387201209600) ≤
      (-1659891997138825732253 / 1000000000000000000000) := by
  have h := log_scaled_interval (408918718161087271 / 2150398387201209600) (by norm_num) 3 24
    (140118919760936071 / 677718516561238471)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_entropy_2_m_6 :
    (227689204334637955513 / 500000000000000000000) ≤ -xlog2 ((408918718161087271 /
      2150398387201209600)) ∧ -xlog2 ((408918718161087271 / 2150398387201209600)) ≤
      (113844602167318977757 / 250000000000000000000) := by
  have h := entropy_term_interval (x := (408918718161087271 / 2150398387201209600)) (a :=
    (408918718161087271 / 2150398387201209600)) (b := (408918718161087271 / 2150398387201209600))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_43.1 deformed_log_43.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_entropy_2_m_7 :
    (227689204334637955513 / 500000000000000000000) ≤ -xlog2 ((408918718161087271 /
      2150398387201209600)) ∧ -xlog2 ((408918718161087271 / 2150398387201209600)) ≤
      (113844602167318977757 / 250000000000000000000) := by
  have h := entropy_term_interval (x := (408918718161087271 / 2150398387201209600)) (a :=
    (408918718161087271 / 2150398387201209600)) (b := (408918718161087271 / 2150398387201209600))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_43.1 deformed_log_43.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_log_44 :
    (-61709029848076652551 / 50000000000000000000) ≤ Real.log (447088055215287271 /
      1535998848000864000) ∧ Real.log (447088055215287271 / 1535998848000864000) ≤
      (-1234180596961533051019 / 1000000000000000000000) := by
  have h := log_scaled_interval (447088055215287271 / 1535998848000864000) (by norm_num) 2 24
    (63088343215071271 / 831087767215503271)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_entropy_2_b_0 :
    (103653847240319201889 / 200000000000000000000) ≤ -xlog2 ((447088055215287271 /
      1535998848000864000)) ∧ -xlog2 ((447088055215287271 / 1535998848000864000)) ≤
      (518269236201596009447 / 1000000000000000000000) := by
  have h := entropy_term_interval (x := (447088055215287271 / 1535998848000864000)) (a :=
    (447088055215287271 / 1535998848000864000)) (b := (447088055215287271 / 1535998848000864000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_44.1 deformed_log_44.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_log_45 :
    (-313154237681356810599 / 200000000000000000000) ≤ Real.log (320911368785144729 /
      1535998848000864000) ∧ Real.log (320911368785144729 / 1535998848000864000) ≤
      (-782885594203392026497 / 500000000000000000000) := by
  have h := log_scaled_interval (320911368785144729 / 1535998848000864000) (by norm_num) 3 24
    (128911512785036729 / 512911224785252729)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_entropy_2_b_1 :
    (29496946917916106739 / 62500000000000000000) ≤ -xlog2 ((320911368785144729 /
      1535998848000864000)) ∧ -xlog2 ((320911368785144729 / 1535998848000864000)) ≤
      (18878046027466308313 / 40000000000000000000) := by
  have h := entropy_term_interval (x := (320911368785144729 / 1535998848000864000)) (a :=
    (320911368785144729 / 1535998848000864000)) (b := (320911368785144729 / 1535998848000864000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_45.1 deformed_log_45.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_entropy_2_b_2 :
    (29496946917916106739 / 62500000000000000000) ≤ -xlog2 ((320911368785144729 /
      1535998848000864000)) ∧ -xlog2 ((320911368785144729 / 1535998848000864000)) ≤
      (18878046027466308313 / 40000000000000000000) := by
  have h := entropy_term_interval (x := (320911368785144729 / 1535998848000864000)) (a :=
    (320911368785144729 / 1535998848000864000)) (b := (320911368785144729 / 1535998848000864000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_45.1 deformed_log_45.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_entropy_2_b_3 :
    (103653847240319201889 / 200000000000000000000) ≤ -xlog2 ((447088055215287271 /
      1535998848000864000)) ∧ -xlog2 ((447088055215287271 / 1535998848000864000)) ≤
      (518269236201596009447 / 1000000000000000000000) := by
  have h := entropy_term_interval (x := (447088055215287271 / 1535998848000864000)) (a :=
    (447088055215287271 / 1535998848000864000)) (b := (447088055215287271 / 1535998848000864000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_44.1 deformed_log_44.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_entropy_2_e_0 :
    (215413541726763015121 / 500000000000000000000) ≤ -xlog2 ((1 / 6)) ∧ -xlog2 ((1 / 6)) ≤
      (430827083453526030243 / 1000000000000000000000) := by
  have h := entropy_term_interval (x := (1 / 6)) (a := (1 / 6)) (b := (1 / 6))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_7.1 deformed_log_7.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_log_46 :
    (-1727525871119871639527 / 1000000000000000000000) ≤ Real.log (9099440343578251 /
      51199961600028800) ∧ Real.log (9099440343578251 / 51199961600028800) ≤ (-863762935559935819763
      / 500000000000000000000) := by
  have h := log_scaled_interval (9099440343578251 / 51199961600028800) (by norm_num) 3 24
    (2699445143574651 / 15499435543581851)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_entropy_2_e_1 :
    (88587845887666736331 / 200000000000000000000) ≤ -xlog2 ((9099440343578251 / 51199961600028800))
      ∧ -xlog2 ((9099440343578251 / 51199961600028800)) ≤ (442939229438333681657 /
      1000000000000000000000) := by
  have h := entropy_term_interval (x := (9099440343578251 / 51199961600028800)) (a :=
    (9099440343578251 / 51199961600028800)) (b := (9099440343578251 / 51199961600028800))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_46.1 deformed_log_46.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_entropy_2_e_2 :
    (182761269517345115537 / 500000000000000000000) ≤ -xlog2 ((5 / 42)) ∧ -xlog2 ((5 / 42)) ≤
      (14620901561387609243 / 40000000000000000000) := by
  have h := entropy_term_interval (x := (5 / 42)) (a := (5 / 42)) (b := (5 / 42))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_9.1 deformed_log_9.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_log_47 :
    (-1239410339620865097143 / 500000000000000000000) ≤ Real.log (450734490355146187 /
      5375995968003024000) ∧ Real.log (450734490355146187 / 5375995968003024000) ≤
      (-495764135848346038857 / 200000000000000000000) := by
  have h := log_scaled_interval (450734490355146187 / 5375995968003024000) (by norm_num) 4 24
    (114734742354957187 / 786734238355335187)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_entropy_2_e_3 :
    (149917216878513548109 / 500000000000000000000) ≤ -xlog2 ((450734490355146187 /
      5375995968003024000)) ∧ -xlog2 ((450734490355146187 / 5375995968003024000)) ≤
      (299834433757027096219 / 1000000000000000000000) := by
  have h := entropy_term_interval (x := (450734490355146187 / 5375995968003024000)) (a :=
    (450734490355146187 / 5375995968003024000)) (b := (450734490355146187 / 5375995968003024000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_47.1 deformed_log_47.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_log_48 :
    (-2629606200604652446071 / 1000000000000000000000) ≤ Real.log (32303845595006243 /
      447999664000252000) ∧ Real.log (32303845595006243 / 447999664000252000) ≤
      (-262960620060465244607 / 100000000000000000000) := by
  have h := log_scaled_interval (32303845595006243 / 447999664000252000) (by norm_num) 4 24
    (4303866594990493 / 60303824595021993)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_entropy_2_e_4 :
    (273553195032706434123 / 1000000000000000000000) ≤ -xlog2 ((32303845595006243 /
      447999664000252000)) ∧ -xlog2 ((32303845595006243 / 447999664000252000)) ≤
      (68388298758176608531 / 250000000000000000000) := by
  have h := entropy_term_interval (x := (32303845595006243 / 447999664000252000)) (a :=
    (32303845595006243 / 447999664000252000)) (b := (32303845595006243 / 447999664000252000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_48.1 deformed_log_48.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_entropy_2_e_5 :
    (149917216878513548109 / 500000000000000000000) ≤ -xlog2 ((450734490355146187 /
      5375995968003024000)) ∧ -xlog2 ((450734490355146187 / 5375995968003024000)) ≤
      (299834433757027096219 / 1000000000000000000000) := by
  have h := entropy_term_interval (x := (450734490355146187 / 5375995968003024000)) (a :=
    (450734490355146187 / 5375995968003024000)) (b := (450734490355146187 / 5375995968003024000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_47.1 deformed_log_47.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_entropy_2_e_6 :
    (182761269517345115537 / 500000000000000000000) ≤ -xlog2 ((5 / 42)) ∧ -xlog2 ((5 / 42)) ≤
      (14620901561387609243 / 40000000000000000000) := by
  have h := entropy_term_interval (x := (5 / 42)) (a := (5 / 42)) (b := (5 / 42))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_9.1 deformed_log_9.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_entropy_2_e_7 :
    (88587845887666736331 / 200000000000000000000) ≤ -xlog2 ((9099440343578251 / 51199961600028800))
      ∧ -xlog2 ((9099440343578251 / 51199961600028800)) ≤ (442939229438333681657 /
      1000000000000000000000) := by
  have h := entropy_term_interval (x := (9099440343578251 / 51199961600028800)) (a :=
    (9099440343578251 / 51199961600028800)) (b := (9099440343578251 / 51199961600028800))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    deformed_log_46.1 deformed_log_46.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

def deformed_numeric_poly_2_0 : ℝ[X] := C 1 * X ^ 3 + C (-225103635906608729 / 1343998992000756000)
  * X ^ 2 + C (11356973612592335318689661763431477 / 5780266529596954209522894628915200000) * X ^ 1
  + C (-3976318534891477683028740433969 / 154140440789252112253943856771072000000000)

theorem deformed_root_2_0_0_exists :
    ∃ x ∈ Set.Icc ((13129564004951869 / 1000000000000000000000000) : ℝ) (1312956400495187 /
      100000000000000000000000), deformed_numeric_poly_2_0.eval x = 0 := by
  apply polynomial_root_in_interval _ _ _ (by norm_num)
  apply Or.inl
  norm_num [deformed_numeric_poly_2_0]

def deformed_root_2_0_0 : ℝ := Classical.choose deformed_root_2_0_0_exists

theorem deformed_root_2_0_0_bounds : (13129564004951869 / 1000000000000000000000000) ≤
  deformed_root_2_0_0 ∧ deformed_root_2_0_0 ≤ (1312956400495187 / 100000000000000000000000) :=
  (Classical.choose_spec deformed_root_2_0_0_exists).1

theorem deformed_root_2_0_0_eval : deformed_numeric_poly_2_0.eval deformed_root_2_0_0 = 0 :=
  (Classical.choose_spec deformed_root_2_0_0_exists).2

theorem deformed_log_49 :
    (-18148399355203459687481 / 1000000000000000000000) ≤ Real.log (13129564004951869 /
      1000000000000000000000000) ∧ Real.log (13129564004951869 / 1000000000000000000000000) ≤
      (-453709983880086492187 / 25000000000000000000) := by
  have h := log_scaled_interval (13129564004951869 / 1000000000000000000000000) (by norm_num) 27 24
    (45431867264224327 / 164641156815005577)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_log_50 :
    (-18148399355203459611317 / 1000000000000000000000) ≤ Real.log (1312956400495187 /
      100000000000000000000000) ∧ Real.log (1312956400495187 / 100000000000000000000000) ≤
      (-4537099838800864902829 / 250000000000000000000) := by
  have h := log_scaled_interval (1312956400495187 / 100000000000000000000000) (by norm_num) 27 24
    (9086373452844867 / 32928231363001117)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_root_2_0_0_entropy :
    (343766198008741 / 1000000000000000000000) ≤ -xlog2 (deformed_root_2_0_0) ∧ -xlog2
      (deformed_root_2_0_0) ≤ (171883099004371 / 500000000000000000000) := by
  have h := entropy_term_interval (x := deformed_root_2_0_0) (a := (13129564004951869 /
    1000000000000000000000000)) (b := (1312956400495187 / 100000000000000000000000))
    (by norm_num) deformed_root_2_0_0_bounds.1 deformed_root_2_0_0_bounds.2 (by norm_num)
    deformed_log_49.1 deformed_log_50.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_root_2_0_1_exists :
    ∃ x ∈ Set.Icc ((3173196155725137147093 / 250000000000000000000000) : ℝ) (12692784622900548588373
      / 1000000000000000000000000), deformed_numeric_poly_2_0.eval x = 0 := by
  apply polynomial_root_in_interval _ _ _ (by norm_num)
  apply Or.inr
  norm_num [deformed_numeric_poly_2_0]

def deformed_root_2_0_1 : ℝ := Classical.choose deformed_root_2_0_1_exists

theorem deformed_root_2_0_1_bounds : (3173196155725137147093 / 250000000000000000000000) ≤
  deformed_root_2_0_1 ∧ deformed_root_2_0_1 ≤ (12692784622900548588373 / 1000000000000000000000000)
  :=
  (Classical.choose_spec deformed_root_2_0_1_exists).1

theorem deformed_root_2_0_1_eval : deformed_numeric_poly_2_0.eval deformed_root_2_0_1 = 0 :=
  (Classical.choose_spec deformed_root_2_0_1_exists).2

theorem deformed_log_51 :
    (-174668863475973053237 / 40000000000000000000) ≤ Real.log (3173196155725137147093 /
      250000000000000000000000) ∧ Real.log (3173196155725137147093 / 250000000000000000000000) ≤
      (-1091680396724831582731 / 250000000000000000000) := by
  have h := log_scaled_interval (3173196155725137147093 / 250000000000000000000000) (by norm_num) 7
    24 (1220071155725137147093 / 5126321155725137147093)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_log_52 :
    (-174668863475973053237 / 40000000000000000000) ≤ Real.log (12692784622900548588373 /
      1000000000000000000000000) ∧ Real.log (12692784622900548588373 / 1000000000000000000000000) ≤
      (-1091680396724831582731 / 250000000000000000000) := by
  have h := log_scaled_interval (12692784622900548588373 / 1000000000000000000000000) (by norm_num)
    7 24 (4880284622900548588373 / 20505284622900548588373)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_root_2_0_1_entropy :
    (19990652117314018119 / 250000000000000000000) ≤ -xlog2 (deformed_root_2_0_1) ∧ -xlog2
      (deformed_root_2_0_1) ≤ (79962608469256072477 / 1000000000000000000000) := by
  have h := entropy_term_interval (x := deformed_root_2_0_1) (a := (3173196155725137147093 /
    250000000000000000000000)) (b := (12692784622900548588373 / 1000000000000000000000000))
    (by norm_num) deformed_root_2_0_1_bounds.1 deformed_root_2_0_1_bounds.2 (by norm_num)
    deformed_log_51.1 deformed_log_52.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_root_2_0_2_exists :
    ∃ x ∈ Set.Icc ((77397576099339024889693 / 500000000000000000000000) : ℝ)
      (154795152198678049779387 / 1000000000000000000000000), deformed_numeric_poly_2_0.eval x = 0
      := by
  apply polynomial_root_in_interval _ _ _ (by norm_num)
  apply Or.inl
  norm_num [deformed_numeric_poly_2_0]

def deformed_root_2_0_2 : ℝ := Classical.choose deformed_root_2_0_2_exists

theorem deformed_root_2_0_2_bounds : (77397576099339024889693 / 500000000000000000000000) ≤
  deformed_root_2_0_2 ∧ deformed_root_2_0_2 ≤ (154795152198678049779387 / 1000000000000000000000000)
  :=
  (Classical.choose_spec deformed_root_2_0_2_exists).1

theorem deformed_root_2_0_2_eval : deformed_numeric_poly_2_0.eval deformed_root_2_0_2 = 0 :=
  (Classical.choose_spec deformed_root_2_0_2_exists).2

theorem deformed_log_53 :
    (-37313052697257820123 / 20000000000000000000) ≤ Real.log (77397576099339024889693 /
      500000000000000000000000) ∧ Real.log (77397576099339024889693 / 500000000000000000000000) ≤
      (-466413158715722751537 / 250000000000000000000) := by
  have h := log_scaled_interval (77397576099339024889693 / 500000000000000000000000) (by norm_num) 3
    24 (14897576099339024889693 / 139897576099339024889693)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_log_54 :
    (-37313052697257820123 / 20000000000000000000) ≤ Real.log (154795152198678049779387 /
      1000000000000000000000000) ∧ Real.log (154795152198678049779387 / 1000000000000000000000000) ≤
      (-466413158715722751537 / 250000000000000000000) := by
  have h := log_scaled_interval (154795152198678049779387 / 1000000000000000000000000) (by norm_num)
    3 24 (29795152198678049779387 / 279795152198678049779387)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_root_2_0_2_entropy :
    (208320823962790559901 / 500000000000000000000) ≤ -xlog2 (deformed_root_2_0_2) ∧ -xlog2
      (deformed_root_2_0_2) ≤ (104160411981395279951 / 250000000000000000000) := by
  have h := entropy_term_interval (x := deformed_root_2_0_2) (a := (77397576099339024889693 /
    500000000000000000000000)) (b := (154795152198678049779387 / 1000000000000000000000000))
    (by norm_num) deformed_root_2_0_2_bounds.1 deformed_root_2_0_2_bounds.2 (by norm_num)
    deformed_log_53.1 deformed_log_54.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

def deformed_roots_2_0 : Fin 3 → ℝ := ![deformed_root_2_0_0, deformed_root_2_0_1,
  deformed_root_2_0_2]

theorem deformed_roots_2_0_complete :
    deformed_numeric_poly_2_0.roots = Multiset.map deformed_roots_2_0 Finset.univ.val := by
  apply polynomial_roots_complete
  · intro h
    have h1 := congrArg (fun p : ℝ[X] ↦ p.eval 1) h
    norm_num [deformed_numeric_poly_2_0] at h1
  · unfold deformed_numeric_poly_2_0
    compute_degree
  · intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [deformed_roots_2_0] at hij ⊢
    all_goals
      have h0 := deformed_root_2_0_0_bounds
      have h1 := deformed_root_2_0_1_bounds
      have h2 := deformed_root_2_0_2_bounds
      linarith
  · intro i
    fin_cases i
    · exact deformed_root_2_0_0_eval
    · exact deformed_root_2_0_1_eval
    · exact deformed_root_2_0_2_eval

def deformed_numeric_poly_2_2 : ℝ[X] := C 1 * X ^ 2 + C (-222896028093643271 / 1075199193600604800)
  * X ^ 1 + C (434375 / 137846050461616)

theorem deformed_root_2_2_0_exists :
    ∃ x ∈ Set.Icc ((1520047385952561 / 100000000000000000000000) : ℝ) (15200473859525611 /
      1000000000000000000000000), deformed_numeric_poly_2_2.eval x = 0 := by
  apply polynomial_root_in_interval _ _ _ (by norm_num)
  apply Or.inr
  norm_num [deformed_numeric_poly_2_2]

def deformed_root_2_2_0 : ℝ := Classical.choose deformed_root_2_2_0_exists

theorem deformed_root_2_2_0_bounds : (1520047385952561 / 100000000000000000000000) ≤
  deformed_root_2_2_0 ∧ deformed_root_2_2_0 ≤ (15200473859525611 / 1000000000000000000000000) :=
  (Classical.choose_spec deformed_root_2_2_0_exists).1

theorem deformed_root_2_2_0_eval : deformed_numeric_poly_2_2.eval deformed_root_2_2_0 = 0 :=
  (Classical.choose_spec deformed_root_2_2_0_exists).2

theorem deformed_log_55 :
    (-18001939234611319560681 / 1000000000000000000000) ≤ Real.log (1520047385952561 /
      100000000000000000000000) ∧ Real.log (1520047385952561 / 100000000000000000000000) ≤
      (-18001939234611319560679 / 1000000000000000000000) := by
  have h := log_scaled_interval (1520047385952561 / 100000000000000000000000) (by norm_num) 26 24
    (239450132542363 / 24081308042698613)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_log_56 :
    (-9000969617305659747447 / 500000000000000000000) ≤ Real.log (15200473859525611 /
      1000000000000000000000000) ∧ Real.log (15200473859525611 / 1000000000000000000000000) ≤
      (-4500484808652829873723 / 250000000000000000000) := by
  have h := log_scaled_interval (15200473859525611 / 1000000000000000000000000) (by norm_num) 26 24
    (1197250662711819 / 120406540213493069)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_root_2_2_0_entropy :
    (394776195346311 / 1000000000000000000000) ≤ -xlog2 (deformed_root_2_2_0) ∧ -xlog2
      (deformed_root_2_2_0) ≤ (49347024418289 / 125000000000000000000) := by
  have h := entropy_term_interval (x := deformed_root_2_2_0) (a := (1520047385952561 /
    100000000000000000000000)) (b := (15200473859525611 / 1000000000000000000000000))
    (by norm_num) deformed_root_2_2_0_bounds.1 deformed_root_2_2_0_bounds.2 (by norm_num)
    deformed_log_55.1 deformed_log_56.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_root_2_2_1_exists :
    ∃ x ∈ Set.Icc ((1295666962670403456197 / 6250000000000000000000) : ℝ) (207306714027264552991521
      / 1000000000000000000000000), deformed_numeric_poly_2_2.eval x = 0 := by
  apply polynomial_root_in_interval _ _ _ (by norm_num)
  apply Or.inl
  norm_num [deformed_numeric_poly_2_2]

def deformed_root_2_2_1 : ℝ := Classical.choose deformed_root_2_2_1_exists

theorem deformed_root_2_2_1_bounds : (1295666962670403456197 / 6250000000000000000000) ≤
  deformed_root_2_2_1 ∧ deformed_root_2_2_1 ≤ (207306714027264552991521 / 1000000000000000000000000)
  :=
  (Classical.choose_spec deformed_root_2_2_1_exists).1

theorem deformed_root_2_2_1_eval : deformed_numeric_poly_2_2.eval deformed_root_2_2_1 = 0 :=
  (Classical.choose_spec deformed_root_2_2_1_exists).2

theorem deformed_log_57 :
    (-786777936044827656513 / 500000000000000000000) ≤ Real.log (1295666962670403456197 /
      6250000000000000000000) ∧ Real.log (1295666962670403456197 / 6250000000000000000000) ≤
      (-62942234883586212521 / 40000000000000000000) := by
  have h := log_scaled_interval (1295666962670403456197 / 6250000000000000000000) (by norm_num) 3 24
    (514416962670403456197 / 2076916962670403456197)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_log_58 :
    (-786777936044827656513 / 500000000000000000000) ≤ Real.log (207306714027264552991521 /
      1000000000000000000000000) ∧ Real.log (207306714027264552991521 / 1000000000000000000000000) ≤
      (-62942234883586212521 / 40000000000000000000) := by
  have h := log_scaled_interval (207306714027264552991521 / 1000000000000000000000000) (by norm_num)
    3 24 (82306714027264552991521 / 332306714027264552991521)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_root_2_2_1_entropy :
    (9412393394363712977 / 20000000000000000000) ≤ -xlog2 (deformed_root_2_2_1) ∧ -xlog2
      (deformed_root_2_2_1) ≤ (117654917429546412213 / 250000000000000000000) := by
  have h := entropy_term_interval (x := deformed_root_2_2_1) (a := (1295666962670403456197 /
    6250000000000000000000)) (b := (207306714027264552991521 / 1000000000000000000000000))
    (by norm_num) deformed_root_2_2_1_bounds.1 deformed_root_2_2_1_bounds.2 (by norm_num)
    deformed_log_57.1 deformed_log_58.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

def deformed_roots_2_2 : Fin 2 → ℝ := ![deformed_root_2_2_0, deformed_root_2_2_1]

theorem deformed_roots_2_2_complete :
    deformed_numeric_poly_2_2.roots = Multiset.map deformed_roots_2_2 Finset.univ.val := by
  apply polynomial_roots_complete
  · intro h
    have h1 := congrArg (fun p : ℝ[X] ↦ p.eval 1) h
    norm_num [deformed_numeric_poly_2_2] at h1
  · unfold deformed_numeric_poly_2_2
    compute_degree
  · intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [deformed_roots_2_2] at hij ⊢
    all_goals
      have h0 := deformed_root_2_2_0_bounds
      have h1 := deformed_root_2_2_1_bounds
      linarith
  · intro i
    fin_cases i
    · exact deformed_root_2_2_0_eval
    · exact deformed_root_2_2_1_eval

def deformed_numeric_poly_2_3 : ℝ[X] := C 1 * X ^ 2 + C (-224367766635620243 / 1791998656001008000)
  * X ^ 1 + C (153505620167439 / 80281539788845158400000)

theorem deformed_root_2_3_0_exists :
    ∃ x ∈ Set.Icc ((15271646213694479 / 1000000000000000000000000) : ℝ) (190895577671181 /
      12500000000000000000000), deformed_numeric_poly_2_3.eval x = 0 := by
  apply polynomial_root_in_interval _ _ _ (by norm_num)
  apply Or.inr
  norm_num [deformed_numeric_poly_2_3]

def deformed_root_2_3_0 : ℝ := Classical.choose deformed_root_2_3_0_exists

theorem deformed_root_2_3_0_bounds : (15271646213694479 / 1000000000000000000000000) ≤
  deformed_root_2_3_0 ∧ deformed_root_2_3_0 ≤ (190895577671181 / 12500000000000000000000) :=
  (Classical.choose_spec deformed_root_2_3_0_exists).1

theorem deformed_root_2_3_0_eval : deformed_numeric_poly_2_3.eval deformed_root_2_3_0 = 0 :=
  (Classical.choose_spec deformed_root_2_3_0_exists).2

theorem deformed_log_59 :
    (-17997267916473949142391 / 1000000000000000000000) ≤ Real.log (15271646213694479 /
      1000000000000000000000000) ∧ Real.log (15271646213694479 / 1000000000000000000000000) ≤
      (-1799726791647394914239 / 100000000000000000000) := by
  have h := log_scaled_interval (15271646213694479 / 1000000000000000000000000) (by norm_num) 26 24
    (1481940079387291 / 120691229630168541)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_log_60 :
    (-1799726791647394907691 / 100000000000000000000) ≤ Real.log (190895577671181 /
      12500000000000000000000) ∧ Real.log (190895577671181 / 12500000000000000000000) ≤
      (-17997267916473949076909 / 1000000000000000000000) := by
  have h := log_scaled_interval (190895577671181 / 12500000000000000000000) (by norm_num) 26 24
    (296388015877459 / 24138245926033709)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_root_2_3_0_entropy :
    (396521714495663 / 1000000000000000000000) ≤ -xlog2 (deformed_root_2_3_0) ∧ -xlog2
      (deformed_root_2_3_0) ≤ (24782607155979 / 62500000000000000000) := by
  have h := entropy_term_interval (x := deformed_root_2_3_0) (a := (15271646213694479 /
    1000000000000000000000000)) (b := (190895577671181 / 12500000000000000000000))
    (by norm_num) deformed_root_2_3_0_bounds.1 deformed_root_2_3_0_bounds.2 (by norm_num)
    deformed_log_59.1 deformed_log_60.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

theorem deformed_root_2_3_1_exists :
    ∃ x ∈ Set.Icc ((3130132638736819261719 / 25000000000000000000000) : ℝ) (125205305549472770468761
      / 1000000000000000000000000), deformed_numeric_poly_2_3.eval x = 0 := by
  apply polynomial_root_in_interval _ _ _ (by norm_num)
  apply Or.inl
  norm_num [deformed_numeric_poly_2_3]

def deformed_root_2_3_1 : ℝ := Classical.choose deformed_root_2_3_1_exists

theorem deformed_root_2_3_1_bounds : (3130132638736819261719 / 25000000000000000000000) ≤
  deformed_root_2_3_1 ∧ deformed_root_2_3_1 ≤ (125205305549472770468761 / 1000000000000000000000000)
  :=
  (Classical.choose_spec deformed_root_2_3_1_exists).1

theorem deformed_root_2_3_1_eval : deformed_numeric_poly_2_3.eval deformed_root_2_3_1 = 0 :=
  (Classical.choose_spec deformed_root_2_3_1_exists).2

theorem deformed_log_61 :
    (-2077800444620768371133 / 1000000000000000000000) ≤ Real.log (3130132638736819261719 /
      25000000000000000000000) ∧ Real.log (3130132638736819261719 / 25000000000000000000000) ≤
      (-519450111155192092783 / 250000000000000000000) := by
  have h := log_scaled_interval (3130132638736819261719 / 25000000000000000000000) (by norm_num) 3
    24 (5132638736819261719 / 6255132638736819261719)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_log_62 :
    (-2077800444620768371133 / 1000000000000000000000) ≤ Real.log (125205305549472770468761 /
      1000000000000000000000000) ∧ Real.log (125205305549472770468761 / 1000000000000000000000000) ≤
      (-519450111155192092783 / 250000000000000000000) := by
  have h := log_scaled_interval (125205305549472770468761 / 1000000000000000000000000) (by norm_num)
    3 24 (205305549472770468761 / 250205305549472770468761)
    (by norm_num) (by norm_num) (by norm_num)
    (69314718055994530941723 / 100000000000000000000000) (2772588722239781237669 /
      4000000000000000000000) deformed_log_two_bounds.1 deformed_log_two_bounds.2
  norm_num [logPartial, logError, Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem deformed_root_2_3_1_entropy :
    (375319480242876119807 / 1000000000000000000000) ≤ -xlog2 (deformed_root_2_3_1) ∧ -xlog2
      (deformed_root_2_3_1) ≤ (1466091719698734843 / 3906250000000000000) := by
  have h := entropy_term_interval (x := deformed_root_2_3_1) (a := (3130132638736819261719 /
    25000000000000000000000)) (b := (125205305549472770468761 / 1000000000000000000000000))
    (by norm_num) deformed_root_2_3_1_bounds.1 deformed_root_2_3_1_bounds.2 (by norm_num)
    deformed_log_61.1 deformed_log_62.2 (by norm_num) (by norm_num : (0 : ℝ) <
      (69314718055994530941723 / 100000000000000000000000))
    deformed_log_two_bounds.1 deformed_log_two_bounds.2
  constructor
  · exact le_trans (by norm_num) h.1
  · exact le_trans h.2 (by norm_num)

def deformed_roots_2_3 : Fin 2 → ℝ := ![deformed_root_2_3_0, deformed_root_2_3_1]

theorem deformed_roots_2_3_complete :
    deformed_numeric_poly_2_3.roots = Multiset.map deformed_roots_2_3 Finset.univ.val := by
  apply polynomial_roots_complete
  · intro h
    have h1 := congrArg (fun p : ℝ[X] ↦ p.eval 1) h
    norm_num [deformed_numeric_poly_2_3] at h1
  · unfold deformed_numeric_poly_2_3
    compute_degree
  · intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [deformed_roots_2_3] at hij ⊢
    all_goals
      have h0 := deformed_root_2_3_0_bounds
      have h1 := deformed_root_2_3_1_bounds
      linarith
  · intro i
    fin_cases i
    · exact deformed_root_2_3_0_eval
    · exact deformed_root_2_3_1_eval

def deformedNumericM : Fin 3 → Fin 8 → ℝ :=
  ![![(56084051 / 673008504), (56084051 / 673008504), (104132057 / 673008504), (104132057 /
    673008504), (4004001 / 28042021), (1 / 28042021), (16030015 / 84126063), (16030015 / 84126063)],
    ![(7772331089 / 95856072000), (7772331089 / 95856072000), (104514438053 / 670992504000),
      (104514438053 / 670992504000), (8099732189 / 55916042000), (7189261 / 1597601200), (6323367919
      / 33549625200), (6323367919 / 33549625200)],
    ![(3565853898150061607 / 43007967744024192000), (3565853898150061607 / 43007967744024192000),
      (6662804181855119477 / 43007967744024192000), (6662804181855119477 / 43007967744024192000),
      (73304920928724243 / 511999616000288000), (604824992625043 / 716799462400403200),
      (408918718161087271 / 2150398387201209600), (408918718161087271 / 2150398387201209600)]]

def deformedNumericB : Fin 3 → Fin 4 → ℝ :=
  ![![(3506003 / 12018009), (5006003 / 24036018), (5006003 / 24036018), (3506003 / 12018009)],
    ![(6907167919 / 23964018000), (5074841081 / 23964018000), (5074841081 / 23964018000),
      (6907167919 / 23964018000)],
    ![(447088055215287271 / 1535998848000864000), (320911368785144729 / 1535998848000864000),
      (320911368785144729 / 1535998848000864000), (447088055215287271 / 1535998848000864000)]]

def deformedNumericE : Fin 3 → Fin 8 → ℝ :=
  ![![(1 / 6), (715715 / 4006003), (5 / 42), (7006003 / 84126063), (4002001 / 56084042), (7006003 /
    84126063), (5 / 42), (715715 / 4006003)],
    ![(1 / 6), (138722139 / 798800600), (5 / 42), (7236517243 / 83874063000), (263348076 /
      3494752625), (7236517243 / 83874063000), (5 / 42), (138722139 / 798800600)],
    ![(1 / 6), (9099440343578251 / 51199961600028800), (5 / 42), (450734490355146187 /
      5375995968003024000), (32303845595006243 / 447999664000252000), (450734490355146187 /
      5375995968003024000), (5 / 42), (9099440343578251 / 51199961600028800)]]

def deformedNumericRoots : Fin 3 → Multiset ℝ :=
  ![({0, 0, deformed_root_0_0_0, deformed_root_0_0_1, deformed_root_0_0_2, deformed_root_0_2_0,
    deformed_root_0_2_1, deformed_root_0_3_0, deformed_root_0_3_1, deformed_root_0_0_0,
    deformed_root_0_0_1, deformed_root_0_0_2, deformed_root_0_2_0, deformed_root_0_2_1,
    deformed_root_0_3_0, deformed_root_0_3_1} : Multiset ℝ),
    ({0, 0, deformed_root_1_0_0, deformed_root_1_0_1, deformed_root_1_0_2, deformed_root_1_2_0,
      deformed_root_1_2_1, deformed_root_1_3_0, deformed_root_1_3_1, deformed_root_1_0_0,
      deformed_root_1_0_1, deformed_root_1_0_2, deformed_root_1_2_0, deformed_root_1_2_1,
      deformed_root_1_3_0, deformed_root_1_3_1} : Multiset ℝ),
    ({0, 0, deformed_root_2_0_0, deformed_root_2_0_1, deformed_root_2_0_2, deformed_root_2_2_0,
      deformed_root_2_2_1, deformed_root_2_3_0, deformed_root_2_3_1, deformed_root_2_0_0,
      deformed_root_2_0_1, deformed_root_2_0_2, deformed_root_2_2_0, deformed_root_2_2_1,
      deformed_root_2_3_0, deformed_root_2_3_1} : Multiset ℝ)]

def deformedShannon {n : ℕ} (p : Fin n → ℝ) : ℝ := -∑ i, xlog2 (p i)

def deformedNumericSigmaEntropy (k : Fin 3) : ℝ :=
  -(((deformedNumericRoots k).map xlog2).sum)

def deformedNumericHolevo (s : Fin 3 → ℝ) : ℝ :=
  s 2 - (13 / 16) * s 0 - (3 / 16) * s 1

def deformedNumericRate : ℝ := (1 / 2) * (
  deformedNumericHolevo (fun k ↦ deformedShannon (deformedNumericM k)) +
  deformedNumericHolevo (fun k ↦ deformedShannon (deformedNumericB k)) -
  deformedNumericHolevo deformedNumericSigmaEntropy -
  deformedNumericHolevo (fun k ↦ deformedShannon (deformedNumericE k)))

theorem deformedNumericM_table (k : Fin 3) :
    (![(2743053503 / 1000000000), (2769824801 / 1000000000), (1375066807 / 500000000)] k : ℝ) ≤
      deformedShannon (deformedNumericM k) ∧
      deformedShannon (deformedNumericM k) ≤ ![(2743053503 / 1000000000), (2769824801 / 1000000000),
        (1375066807 / 500000000)] k + 1 / 1000000000 := by
  have hz : xlog2 0 = 0 := by simp [xlog2]
  have h0 := deformed_entropy_0_m_0
  have h1 := deformed_entropy_0_m_1
  have h2 := deformed_entropy_0_m_2
  have h3 := deformed_entropy_0_m_3
  have h4 := deformed_entropy_0_m_4
  have h5 := deformed_entropy_0_m_5
  have h6 := deformed_entropy_0_m_6
  have h7 := deformed_entropy_0_m_7
  have h8 := deformed_entropy_0_b_0
  have h9 := deformed_entropy_0_b_1
  have h10 := deformed_entropy_0_b_2
  have h11 := deformed_entropy_0_b_3
  have h12 := deformed_entropy_0_e_0
  have h13 := deformed_entropy_0_e_1
  have h14 := deformed_entropy_0_e_2
  have h15 := deformed_entropy_0_e_3
  have h16 := deformed_entropy_0_e_4
  have h17 := deformed_entropy_0_e_5
  have h18 := deformed_entropy_0_e_6
  have h19 := deformed_entropy_0_e_7
  have h20 := deformed_root_0_0_1_entropy
  have h21 := deformed_root_0_0_2_entropy
  have h22 := deformed_root_0_2_1_entropy
  have h23 := deformed_root_0_3_1_entropy
  have h24 := deformed_entropy_1_m_0
  have h25 := deformed_entropy_1_m_1
  have h26 := deformed_entropy_1_m_2
  have h27 := deformed_entropy_1_m_3
  have h28 := deformed_entropy_1_m_4
  have h29 := deformed_entropy_1_m_5
  have h30 := deformed_entropy_1_m_6
  have h31 := deformed_entropy_1_m_7
  have h32 := deformed_entropy_1_b_0
  have h33 := deformed_entropy_1_b_1
  have h34 := deformed_entropy_1_b_2
  have h35 := deformed_entropy_1_b_3
  have h36 := deformed_entropy_1_e_0
  have h37 := deformed_entropy_1_e_1
  have h38 := deformed_entropy_1_e_2
  have h39 := deformed_entropy_1_e_3
  have h40 := deformed_entropy_1_e_4
  have h41 := deformed_entropy_1_e_5
  have h42 := deformed_entropy_1_e_6
  have h43 := deformed_entropy_1_e_7
  have h44 := deformed_root_1_0_0_entropy
  have h45 := deformed_root_1_0_1_entropy
  have h46 := deformed_root_1_0_2_entropy
  have h47 := deformed_root_1_2_1_entropy
  have h48 := deformed_root_1_3_0_entropy
  have h49 := deformed_root_1_3_1_entropy
  have h50 := deformed_entropy_2_m_0
  have h51 := deformed_entropy_2_m_1
  have h52 := deformed_entropy_2_m_2
  have h53 := deformed_entropy_2_m_3
  have h54 := deformed_entropy_2_m_4
  have h55 := deformed_entropy_2_m_5
  have h56 := deformed_entropy_2_m_6
  have h57 := deformed_entropy_2_m_7
  have h58 := deformed_entropy_2_b_0
  have h59 := deformed_entropy_2_b_1
  have h60 := deformed_entropy_2_b_2
  have h61 := deformed_entropy_2_b_3
  have h62 := deformed_entropy_2_e_0
  have h63 := deformed_entropy_2_e_1
  have h64 := deformed_entropy_2_e_2
  have h65 := deformed_entropy_2_e_3
  have h66 := deformed_entropy_2_e_4
  have h67 := deformed_entropy_2_e_5
  have h68 := deformed_entropy_2_e_6
  have h69 := deformed_entropy_2_e_7
  have h70 := deformed_root_2_0_0_entropy
  have h71 := deformed_root_2_0_1_entropy
  have h72 := deformed_root_2_0_2_entropy
  have h73 := deformed_root_2_2_0_entropy
  have h74 := deformed_root_2_2_1_entropy
  have h75 := deformed_root_2_3_0_entropy
  have h76 := deformed_root_2_3_1_entropy
  fin_cases k <;>
    norm_num [deformedShannon, deformedNumericSigmaEntropy,
      deformedNumericM, deformedNumericB, deformedNumericE, deformedNumericRoots,
      Fin.sum_univ_succ, Matrix.cons_val, Matrix.cons_val_two, hz,
      deformed_root_0_0_0, deformed_root_0_2_0, deformed_root_0_3_0,
      deformed_root_1_2_0] <;> constructor <;> linarith

theorem deformedNumericB_table (k : Fin 3) :
    (![(494952023 / 250000000), (991532279 / 500000000), (1980440773 / 1000000000)] k : ℝ) ≤
      deformedShannon (deformedNumericB k) ∧
      deformedShannon (deformedNumericB k) ≤ ![(494952023 / 250000000), (991532279 / 500000000),
        (1980440773 / 1000000000)] k + 1 / 1000000000 := by
  have hz : xlog2 0 = 0 := by simp [xlog2]
  have h0 := deformed_entropy_0_m_0
  have h1 := deformed_entropy_0_m_1
  have h2 := deformed_entropy_0_m_2
  have h3 := deformed_entropy_0_m_3
  have h4 := deformed_entropy_0_m_4
  have h5 := deformed_entropy_0_m_5
  have h6 := deformed_entropy_0_m_6
  have h7 := deformed_entropy_0_m_7
  have h8 := deformed_entropy_0_b_0
  have h9 := deformed_entropy_0_b_1
  have h10 := deformed_entropy_0_b_2
  have h11 := deformed_entropy_0_b_3
  have h12 := deformed_entropy_0_e_0
  have h13 := deformed_entropy_0_e_1
  have h14 := deformed_entropy_0_e_2
  have h15 := deformed_entropy_0_e_3
  have h16 := deformed_entropy_0_e_4
  have h17 := deformed_entropy_0_e_5
  have h18 := deformed_entropy_0_e_6
  have h19 := deformed_entropy_0_e_7
  have h20 := deformed_root_0_0_1_entropy
  have h21 := deformed_root_0_0_2_entropy
  have h22 := deformed_root_0_2_1_entropy
  have h23 := deformed_root_0_3_1_entropy
  have h24 := deformed_entropy_1_m_0
  have h25 := deformed_entropy_1_m_1
  have h26 := deformed_entropy_1_m_2
  have h27 := deformed_entropy_1_m_3
  have h28 := deformed_entropy_1_m_4
  have h29 := deformed_entropy_1_m_5
  have h30 := deformed_entropy_1_m_6
  have h31 := deformed_entropy_1_m_7
  have h32 := deformed_entropy_1_b_0
  have h33 := deformed_entropy_1_b_1
  have h34 := deformed_entropy_1_b_2
  have h35 := deformed_entropy_1_b_3
  have h36 := deformed_entropy_1_e_0
  have h37 := deformed_entropy_1_e_1
  have h38 := deformed_entropy_1_e_2
  have h39 := deformed_entropy_1_e_3
  have h40 := deformed_entropy_1_e_4
  have h41 := deformed_entropy_1_e_5
  have h42 := deformed_entropy_1_e_6
  have h43 := deformed_entropy_1_e_7
  have h44 := deformed_root_1_0_0_entropy
  have h45 := deformed_root_1_0_1_entropy
  have h46 := deformed_root_1_0_2_entropy
  have h47 := deformed_root_1_2_1_entropy
  have h48 := deformed_root_1_3_0_entropy
  have h49 := deformed_root_1_3_1_entropy
  have h50 := deformed_entropy_2_m_0
  have h51 := deformed_entropy_2_m_1
  have h52 := deformed_entropy_2_m_2
  have h53 := deformed_entropy_2_m_3
  have h54 := deformed_entropy_2_m_4
  have h55 := deformed_entropy_2_m_5
  have h56 := deformed_entropy_2_m_6
  have h57 := deformed_entropy_2_m_7
  have h58 := deformed_entropy_2_b_0
  have h59 := deformed_entropy_2_b_1
  have h60 := deformed_entropy_2_b_2
  have h61 := deformed_entropy_2_b_3
  have h62 := deformed_entropy_2_e_0
  have h63 := deformed_entropy_2_e_1
  have h64 := deformed_entropy_2_e_2
  have h65 := deformed_entropy_2_e_3
  have h66 := deformed_entropy_2_e_4
  have h67 := deformed_entropy_2_e_5
  have h68 := deformed_entropy_2_e_6
  have h69 := deformed_entropy_2_e_7
  have h70 := deformed_root_2_0_0_entropy
  have h71 := deformed_root_2_0_1_entropy
  have h72 := deformed_root_2_0_2_entropy
  have h73 := deformed_root_2_2_0_entropy
  have h74 := deformed_root_2_2_1_entropy
  have h75 := deformed_root_2_3_0_entropy
  have h76 := deformed_root_2_3_1_entropy
  fin_cases k <;>
    norm_num [deformedShannon, deformedNumericSigmaEntropy,
      deformedNumericM, deformedNumericB, deformedNumericE, deformedNumericRoots,
      Fin.sum_univ_succ, Matrix.cons_val, Matrix.cons_val_two, hz,
      deformed_root_0_0_0, deformed_root_0_2_0, deformed_root_0_3_0,
      deformed_root_1_2_0] <;> constructor <;> linarith

theorem deformedNumericSigma_table (k : Fin 3) :
    (![(668218347 / 250000000), (136608161 / 50000000), (1342544541 / 500000000)] k : ℝ) ≤
      deformedNumericSigmaEntropy k ∧
      deformedNumericSigmaEntropy k ≤ ![(668218347 / 250000000), (136608161 / 50000000), (1342544541
        / 500000000)] k + 1 / 1000000000 := by
  have hz : xlog2 0 = 0 := by simp [xlog2]
  have h0 := deformed_entropy_0_m_0
  have h1 := deformed_entropy_0_m_1
  have h2 := deformed_entropy_0_m_2
  have h3 := deformed_entropy_0_m_3
  have h4 := deformed_entropy_0_m_4
  have h5 := deformed_entropy_0_m_5
  have h6 := deformed_entropy_0_m_6
  have h7 := deformed_entropy_0_m_7
  have h8 := deformed_entropy_0_b_0
  have h9 := deformed_entropy_0_b_1
  have h10 := deformed_entropy_0_b_2
  have h11 := deformed_entropy_0_b_3
  have h12 := deformed_entropy_0_e_0
  have h13 := deformed_entropy_0_e_1
  have h14 := deformed_entropy_0_e_2
  have h15 := deformed_entropy_0_e_3
  have h16 := deformed_entropy_0_e_4
  have h17 := deformed_entropy_0_e_5
  have h18 := deformed_entropy_0_e_6
  have h19 := deformed_entropy_0_e_7
  have h20 := deformed_root_0_0_1_entropy
  have h21 := deformed_root_0_0_2_entropy
  have h22 := deformed_root_0_2_1_entropy
  have h23 := deformed_root_0_3_1_entropy
  have h24 := deformed_entropy_1_m_0
  have h25 := deformed_entropy_1_m_1
  have h26 := deformed_entropy_1_m_2
  have h27 := deformed_entropy_1_m_3
  have h28 := deformed_entropy_1_m_4
  have h29 := deformed_entropy_1_m_5
  have h30 := deformed_entropy_1_m_6
  have h31 := deformed_entropy_1_m_7
  have h32 := deformed_entropy_1_b_0
  have h33 := deformed_entropy_1_b_1
  have h34 := deformed_entropy_1_b_2
  have h35 := deformed_entropy_1_b_3
  have h36 := deformed_entropy_1_e_0
  have h37 := deformed_entropy_1_e_1
  have h38 := deformed_entropy_1_e_2
  have h39 := deformed_entropy_1_e_3
  have h40 := deformed_entropy_1_e_4
  have h41 := deformed_entropy_1_e_5
  have h42 := deformed_entropy_1_e_6
  have h43 := deformed_entropy_1_e_7
  have h44 := deformed_root_1_0_0_entropy
  have h45 := deformed_root_1_0_1_entropy
  have h46 := deformed_root_1_0_2_entropy
  have h47 := deformed_root_1_2_1_entropy
  have h48 := deformed_root_1_3_0_entropy
  have h49 := deformed_root_1_3_1_entropy
  have h50 := deformed_entropy_2_m_0
  have h51 := deformed_entropy_2_m_1
  have h52 := deformed_entropy_2_m_2
  have h53 := deformed_entropy_2_m_3
  have h54 := deformed_entropy_2_m_4
  have h55 := deformed_entropy_2_m_5
  have h56 := deformed_entropy_2_m_6
  have h57 := deformed_entropy_2_m_7
  have h58 := deformed_entropy_2_b_0
  have h59 := deformed_entropy_2_b_1
  have h60 := deformed_entropy_2_b_2
  have h61 := deformed_entropy_2_b_3
  have h62 := deformed_entropy_2_e_0
  have h63 := deformed_entropy_2_e_1
  have h64 := deformed_entropy_2_e_2
  have h65 := deformed_entropy_2_e_3
  have h66 := deformed_entropy_2_e_4
  have h67 := deformed_entropy_2_e_5
  have h68 := deformed_entropy_2_e_6
  have h69 := deformed_entropy_2_e_7
  have h70 := deformed_root_2_0_0_entropy
  have h71 := deformed_root_2_0_1_entropy
  have h72 := deformed_root_2_0_2_entropy
  have h73 := deformed_root_2_2_0_entropy
  have h74 := deformed_root_2_2_1_entropy
  have h75 := deformed_root_2_3_0_entropy
  have h76 := deformed_root_2_3_1_entropy
  fin_cases k <;>
    norm_num [deformedShannon, deformedNumericSigmaEntropy,
      deformedNumericM, deformedNumericB, deformedNumericE, deformedNumericRoots,
      Fin.sum_univ_succ, Matrix.cons_val, Matrix.cons_val_two, hz,
      deformed_root_0_0_0, deformed_root_0_2_0, deformed_root_0_3_0,
      deformed_root_1_2_0] <;> constructor <;> linarith

theorem deformedNumericE_table (k : Fin 3) :
    (![(364845011 / 125000000), (2930141639 / 1000000000), (1460486341 / 500000000)] k : ℝ) ≤
      deformedShannon (deformedNumericE k) ∧
      deformedShannon (deformedNumericE k) ≤ ![(364845011 / 125000000), (2930141639 / 1000000000),
        (1460486341 / 500000000)] k + 1 / 1000000000 := by
  have hz : xlog2 0 = 0 := by simp [xlog2]
  have h0 := deformed_entropy_0_m_0
  have h1 := deformed_entropy_0_m_1
  have h2 := deformed_entropy_0_m_2
  have h3 := deformed_entropy_0_m_3
  have h4 := deformed_entropy_0_m_4
  have h5 := deformed_entropy_0_m_5
  have h6 := deformed_entropy_0_m_6
  have h7 := deformed_entropy_0_m_7
  have h8 := deformed_entropy_0_b_0
  have h9 := deformed_entropy_0_b_1
  have h10 := deformed_entropy_0_b_2
  have h11 := deformed_entropy_0_b_3
  have h12 := deformed_entropy_0_e_0
  have h13 := deformed_entropy_0_e_1
  have h14 := deformed_entropy_0_e_2
  have h15 := deformed_entropy_0_e_3
  have h16 := deformed_entropy_0_e_4
  have h17 := deformed_entropy_0_e_5
  have h18 := deformed_entropy_0_e_6
  have h19 := deformed_entropy_0_e_7
  have h20 := deformed_root_0_0_1_entropy
  have h21 := deformed_root_0_0_2_entropy
  have h22 := deformed_root_0_2_1_entropy
  have h23 := deformed_root_0_3_1_entropy
  have h24 := deformed_entropy_1_m_0
  have h25 := deformed_entropy_1_m_1
  have h26 := deformed_entropy_1_m_2
  have h27 := deformed_entropy_1_m_3
  have h28 := deformed_entropy_1_m_4
  have h29 := deformed_entropy_1_m_5
  have h30 := deformed_entropy_1_m_6
  have h31 := deformed_entropy_1_m_7
  have h32 := deformed_entropy_1_b_0
  have h33 := deformed_entropy_1_b_1
  have h34 := deformed_entropy_1_b_2
  have h35 := deformed_entropy_1_b_3
  have h36 := deformed_entropy_1_e_0
  have h37 := deformed_entropy_1_e_1
  have h38 := deformed_entropy_1_e_2
  have h39 := deformed_entropy_1_e_3
  have h40 := deformed_entropy_1_e_4
  have h41 := deformed_entropy_1_e_5
  have h42 := deformed_entropy_1_e_6
  have h43 := deformed_entropy_1_e_7
  have h44 := deformed_root_1_0_0_entropy
  have h45 := deformed_root_1_0_1_entropy
  have h46 := deformed_root_1_0_2_entropy
  have h47 := deformed_root_1_2_1_entropy
  have h48 := deformed_root_1_3_0_entropy
  have h49 := deformed_root_1_3_1_entropy
  have h50 := deformed_entropy_2_m_0
  have h51 := deformed_entropy_2_m_1
  have h52 := deformed_entropy_2_m_2
  have h53 := deformed_entropy_2_m_3
  have h54 := deformed_entropy_2_m_4
  have h55 := deformed_entropy_2_m_5
  have h56 := deformed_entropy_2_m_6
  have h57 := deformed_entropy_2_m_7
  have h58 := deformed_entropy_2_b_0
  have h59 := deformed_entropy_2_b_1
  have h60 := deformed_entropy_2_b_2
  have h61 := deformed_entropy_2_b_3
  have h62 := deformed_entropy_2_e_0
  have h63 := deformed_entropy_2_e_1
  have h64 := deformed_entropy_2_e_2
  have h65 := deformed_entropy_2_e_3
  have h66 := deformed_entropy_2_e_4
  have h67 := deformed_entropy_2_e_5
  have h68 := deformed_entropy_2_e_6
  have h69 := deformed_entropy_2_e_7
  have h70 := deformed_root_2_0_0_entropy
  have h71 := deformed_root_2_0_1_entropy
  have h72 := deformed_root_2_0_2_entropy
  have h73 := deformed_root_2_2_0_entropy
  have h74 := deformed_root_2_2_1_entropy
  have h75 := deformed_root_2_3_0_entropy
  have h76 := deformed_root_2_3_1_entropy
  fin_cases k <;>
    norm_num [deformedShannon, deformedNumericSigmaEntropy,
      deformedNumericM, deformedNumericB, deformedNumericE, deformedNumericRoots,
      Fin.sum_univ_succ, Matrix.cons_val, Matrix.cons_val_two, hz,
      deformed_root_0_0_0, deformed_root_0_2_0, deformed_root_0_3_0,
      deformed_root_1_2_0] <;> constructor <;> linarith

theorem deformedNumericRate_interval :
    (45259148246 / 100000000000000 : ℝ) < deformedNumericRate ∧
      deformedNumericRate < (45259148249 / 100000000000000 : ℝ) := by
  unfold deformedNumericRate deformedNumericHolevo deformedShannon deformedNumericSigmaEntropy
  have hz : xlog2 0 = 0 := by simp [xlog2]
  norm_num [deformedNumericM, deformedNumericB, deformedNumericE, deformedNumericRoots,
    Fin.sum_univ_succ, Matrix.cons_val, Matrix.cons_val_two, hz, deformed_root_0_0_0,
      deformed_root_0_2_0, deformed_root_0_3_0, deformed_root_1_2_0]
  have h0 := deformed_entropy_0_m_0
  have h1 := deformed_entropy_0_m_1
  have h2 := deformed_entropy_0_m_2
  have h3 := deformed_entropy_0_m_3
  have h4 := deformed_entropy_0_m_4
  have h5 := deformed_entropy_0_m_5
  have h6 := deformed_entropy_0_m_6
  have h7 := deformed_entropy_0_m_7
  have h8 := deformed_entropy_0_b_0
  have h9 := deformed_entropy_0_b_1
  have h10 := deformed_entropy_0_b_2
  have h11 := deformed_entropy_0_b_3
  have h12 := deformed_entropy_0_e_0
  have h13 := deformed_entropy_0_e_1
  have h14 := deformed_entropy_0_e_2
  have h15 := deformed_entropy_0_e_3
  have h16 := deformed_entropy_0_e_4
  have h17 := deformed_entropy_0_e_5
  have h18 := deformed_entropy_0_e_6
  have h19 := deformed_entropy_0_e_7
  have h20 := deformed_root_0_0_1_entropy
  have h21 := deformed_root_0_0_2_entropy
  have h22 := deformed_root_0_2_1_entropy
  have h23 := deformed_root_0_3_1_entropy
  have h24 := deformed_entropy_1_m_0
  have h25 := deformed_entropy_1_m_1
  have h26 := deformed_entropy_1_m_2
  have h27 := deformed_entropy_1_m_3
  have h28 := deformed_entropy_1_m_4
  have h29 := deformed_entropy_1_m_5
  have h30 := deformed_entropy_1_m_6
  have h31 := deformed_entropy_1_m_7
  have h32 := deformed_entropy_1_b_0
  have h33 := deformed_entropy_1_b_1
  have h34 := deformed_entropy_1_b_2
  have h35 := deformed_entropy_1_b_3
  have h36 := deformed_entropy_1_e_0
  have h37 := deformed_entropy_1_e_1
  have h38 := deformed_entropy_1_e_2
  have h39 := deformed_entropy_1_e_3
  have h40 := deformed_entropy_1_e_4
  have h41 := deformed_entropy_1_e_5
  have h42 := deformed_entropy_1_e_6
  have h43 := deformed_entropy_1_e_7
  have h44 := deformed_root_1_0_0_entropy
  have h45 := deformed_root_1_0_1_entropy
  have h46 := deformed_root_1_0_2_entropy
  have h47 := deformed_root_1_2_1_entropy
  have h48 := deformed_root_1_3_0_entropy
  have h49 := deformed_root_1_3_1_entropy
  have h50 := deformed_entropy_2_m_0
  have h51 := deformed_entropy_2_m_1
  have h52 := deformed_entropy_2_m_2
  have h53 := deformed_entropy_2_m_3
  have h54 := deformed_entropy_2_m_4
  have h55 := deformed_entropy_2_m_5
  have h56 := deformed_entropy_2_m_6
  have h57 := deformed_entropy_2_m_7
  have h58 := deformed_entropy_2_b_0
  have h59 := deformed_entropy_2_b_1
  have h60 := deformed_entropy_2_b_2
  have h61 := deformed_entropy_2_b_3
  have h62 := deformed_entropy_2_e_0
  have h63 := deformed_entropy_2_e_1
  have h64 := deformed_entropy_2_e_2
  have h65 := deformed_entropy_2_e_3
  have h66 := deformed_entropy_2_e_4
  have h67 := deformed_entropy_2_e_5
  have h68 := deformed_entropy_2_e_6
  have h69 := deformed_entropy_2_e_7
  have h70 := deformed_root_2_0_0_entropy
  have h71 := deformed_root_2_0_1_entropy
  have h72 := deformed_root_2_0_2_entropy
  have h73 := deformed_root_2_2_0_entropy
  have h74 := deformed_root_2_2_1_entropy
  have h75 := deformed_root_2_3_0_entropy
  have h76 := deformed_root_2_3_1_entropy
  constructor <;> linarith

theorem deformedNumericRate_gt : (181 / 400000 : ℝ) < deformedNumericRate := by
  have h := deformedNumericRate_interval.1
  linarith

end
end QIT.QubitActivation
