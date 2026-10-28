import BianchiIX.Measure.DyadicFlux
import Mathlib.Algebra.Order.Archimedean.Basic

noncomputable section

namespace BianchiIX

open Set

theorem two_mul_dyadicScale (d : ℝ) (j : ℕ) :
    2 * dyadicScale d j = d * (1 / 2 : ℝ) ^ j := by
  rw [dyadicScale, pow_succ]
  ring

/-- Half-open dyadic annuli cover every positive radius below the cutoff. -/
theorem exists_mem_dyadicScale_Ioc {d x : ℝ} (hd : 0 < d) (hx : x ∈ Ioc 0 d) :
    ∃ j : ℕ, x ∈ Ioc (dyadicScale d j) (2 * dyadicScale d j) := by
  obtain ⟨j, hj, hJ⟩ := exists_nat_pow_near_of_lt_one (div_pos hx.1 hd)
    ((div_le_one hd).mpr hx.2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨j, ?_, ?_⟩
  · change d * (1 / 2 : ℝ) ^ (j + 1) < x
    exact (mul_comm _ _).trans_lt ((lt_div_iff₀ hd).mp hj)
  · rw [two_mul_dyadicScale]
    exact ((div_le_iff₀ hd).mp hJ).trans_eq (mul_comm _ _)

theorem pairwise_disjoint_dyadicScale_Ioc {d : ℝ} (hd : 0 ≤ d) :
    Pairwise (fun j k : ℕ => Disjoint (Ioc (dyadicScale d j) (2 * dyadicScale d j))
      (Ioc (dyadicScale d k) (2 * dyadicScale d k))) := by
  have H {j k : ℕ} (hjk : j < k) : 2 * dyadicScale d k ≤ dyadicScale d j := by
    rw [two_mul_dyadicScale]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1) hjk) hd
  intro j k hjk
  apply Set.disjoint_left.mpr
  intro x hx hy
  rcases lt_or_gt_of_ne hjk with hj | hk
  · exact (not_lt_of_ge (hy.2.trans (H hj))) hx.1
  · exact (not_lt_of_ge (hx.2.trans (H hk))) hy.1

theorem iUnion_dyadicScale_Ioc {d : ℝ} (hd : 0 < d) :
    (⋃ j : ℕ, Ioc (dyadicScale d j) (2 * dyadicScale d j)) = Ioc 0 d := by
  ext x
  constructor
  · intro hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    refine ⟨(dyadicScale_pos hd j).trans hj.1, hj.2.trans ?_⟩
    rw [two_mul_dyadicScale]
    exact mul_le_of_le_one_right hd.le (pow_le_one₀ (by norm_num) (by norm_num))
  · intro hx
    obtain ⟨j, hj⟩ := exists_mem_dyadicScale_Ioc hd hx
    exact mem_iUnion_of_mem j hj

end BianchiIX
