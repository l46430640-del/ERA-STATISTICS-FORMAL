import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section

namespace BianchiIX

open MeasureTheory
open scoped Topology ENNReal

def dyadicScale (d : ℝ) (j : ℕ) : ℝ := d * (1 / 2 : ℝ) ^ (j + 1)

theorem hasSum_dyadic_weights : HasSum (fun j : ℕ => (1 / 2 : ℝ) ^ (j + 1)) 1 := by
  convert! hasSum_geometric_two.mul_left (1 / 2 : ℝ) using 1
  · ext j
    rw [pow_succ]
    ring
  · norm_num

theorem hasSum_dyadic_first_moment :
    HasSum (fun j : ℕ => ((j : ℝ) + 1) * (1 / 2 : ℝ) ^ (j + 1)) 2 := by
  have H : HasSum (fun j : ℕ => (j : ℝ) * (1 / 2 : ℝ) ^ j) 2 := by
    convert! hasSum_coe_mul_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1) using 1
    norm_num
  convert! (H.add hasSum_geometric_two).mul_left (1 / 2 : ℝ) using 1
  · ext j
    rw [pow_succ]
    ring
  · norm_num

theorem hasSum_dyadic_second_moment :
    HasSum (fun j : ℕ => ((j : ℝ) + 1) ^ 2 * (1 / 2 : ℝ) ^ (j + 1)) 6 := by
  have Hc : HasSum (fun j : ℕ => ((j + 2).choose 2 : ℝ) * (1 / 2 : ℝ) ^ j) 8 := by
    convert! hasSum_choose_mul_geometric_of_norm_lt_one 2
      (by norm_num : ‖(1 / 2 : ℝ)‖ < 1) using 1
    norm_num
  have Hn : HasSum (fun j : ℕ => (j : ℝ) * (1 / 2 : ℝ) ^ j) 2 := by
    convert! hasSum_coe_mul_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1) using 1
    norm_num
  convert! ((Hc.mul_left 2).sub (Hn.add hasSum_geometric_two)).mul_left (1 / 2 : ℝ) using 1
  · ext j
    rw [Nat.cast_choose_two]
    push_cast
    rw [pow_succ]
    ring
  · norm_num

theorem dyadicScale_pos {d : ℝ} (hd : 0 < d) (j : ℕ) : 0 < dyadicScale d j := by
  exact mul_pos hd (pow_pos (by norm_num) _)

theorem dyadicScale_le {d : ℝ} (hd : 0 ≤ d) (j : ℕ) : dyadicScale d j ≤ d :=
  mul_le_of_le_one_right hd (pow_le_one₀ (by norm_num) (by norm_num))

theorem log_dyadicScale {d : ℝ} (hd : 0 < d) (j : ℕ) :
    Real.log (dyadicScale d j) = Real.log d - ((j : ℝ) + 1) * Real.log 2 := by
  rw [dyadicScale, Real.log_mul (ne_of_gt hd) (ne_of_gt (pow_pos (by norm_num) _)), Real.log_pow]
  simp only [Nat.cast_add, Nat.cast_one, one_div, Real.log_inv]
  ring

theorem hasSum_dyadic_log_square {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) :
    HasSum (fun j => dyadicScale d j * (1 + |Real.log (dyadicScale d j)|) ^ 2)
      (d * ((1 - Real.log d) ^ 2 + 4 * (1 - Real.log d) * Real.log 2 + 6 * (Real.log 2) ^ 2)) := by
  have H := ((hasSum_dyadic_weights.mul_left ((1 - Real.log d) ^ 2)).add
    (hasSum_dyadic_first_moment.mul_left (2 * (1 - Real.log d) * Real.log 2))).add
    (hasSum_dyadic_second_moment.mul_left ((Real.log 2) ^ 2))
  convert! H.mul_left d using 1
  · ext j
    have hlog : Real.log (dyadicScale d j) ≤ 0 :=
      Real.log_nonpos (dyadicScale_pos hd j).le ((dyadicScale_le hd.le j).trans hd1)
    rw [abs_of_nonpos hlog, log_dyadicScale hd]
    dsimp [dyadicScale]
    ring
  · ring

theorem dyadic_log_square_sum_le {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) :
    (∑' j, dyadicScale d j * (1 + |Real.log (dyadicScale d j)|) ^ 2) ≤
      11 * d * (1 + |Real.log d|) ^ 2 := by
  rw [(hasSum_dyadic_log_square hd hd1).tsum_eq,
    abs_of_nonpos (Real.log_nonpos hd.le hd1)]
  have hA : 1 ≤ 1 - Real.log d := by linarith [Real.log_nonpos hd.le hd1]
  have hL : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hL1 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hLA : Real.log 2 ≤ 1 - Real.log d := hL1.trans hA
  have hcross := mul_le_mul_of_nonneg_left hLA (by linarith : 0 ≤ 1 - Real.log d)
  have hsquare : (Real.log 2) ^ 2 ≤ (1 - Real.log d) ^ 2 :=
    pow_le_pow_left₀ hL hLA 2
  have H : (1 - Real.log d) ^ 2 + 4 * (1 - Real.log d) * Real.log 2 + 6 * (Real.log 2) ^ 2 ≤
      11 * (1 - Real.log d) ^ 2 := by nlinarith
  calc
    _ ≤ d * (11 * (1 - Real.log d) ^ 2) := mul_le_mul_of_nonneg_left H hd.le
    _ = _ := by ring

theorem dyadic_flux_budget {d C : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) (hC : 0 ≤ C) :
    (∑' j, ENNReal.ofReal (C * (dyadicScale d j * (1 + |Real.log (dyadicScale d j)|) ^ 2))) ≤
      ENNReal.ofReal (11 * C * d * (1 + |Real.log d|) ^ 2) := by
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun j => mul_nonneg hC (mul_nonneg (dyadicScale_pos hd j).le (sq_nonneg _)))
    ((hasSum_dyadic_log_square hd hd1).summable.mul_left C), tsum_mul_left]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ C * (11 * d * (1 + |Real.log d|) ^ 2) :=
      mul_le_mul_of_nonneg_left (dyadic_log_square_sum_le hd hd1) hC
    _ = _ := by ring

/-- Null boundaries and countably many layer bounds give finite failure flux. -/
theorem finite_flux_of_dyadic_bounds {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {E boundary : Set X} {F : ℕ → Set X} {d C : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hC : 0 ≤ C)
    (hcover : E ⊆ boundary ∪ ⋃ j, F j) (hboundary : μ boundary = 0)
    (hF : ∀ j, μ (F j) ≤ ENNReal.ofReal (C * (dyadicScale d j * (1 + |Real.log (dyadicScale d j)|) ^ 2))) :
    μ E ≤ ENNReal.ofReal (11 * C * d * (1 + |Real.log d|) ^ 2) ∧ μ E ≠ ⊤ := by
  have H : μ E ≤ ENNReal.ofReal (11 * C * d * (1 + |Real.log d|) ^ 2) := by
    calc
      μ E ≤ μ (boundary ∪ ⋃ j, F j) := measure_mono hcover
      _ ≤ μ boundary + μ (⋃ j, F j) := measure_union_le _ _
      _ = μ (⋃ j, F j) := by rw [hboundary, zero_add]
      _ ≤ ∑' j, μ (F j) := measure_iUnion_le F
      _ ≤ ∑' j, ENNReal.ofReal (C * (dyadicScale d j * (1 + |Real.log (dyadicScale d j)|) ^ 2)) :=
        ENNReal.tsum_le_tsum hF
      _ ≤ _ := dyadic_flux_budget hd hd1 hC
  exact ⟨H, ne_top_of_le_ne_top ENNReal.ofReal_ne_top H⟩

end BianchiIX
