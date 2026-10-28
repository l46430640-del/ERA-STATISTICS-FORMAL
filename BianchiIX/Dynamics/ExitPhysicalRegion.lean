import BianchiIX.Dynamics.ExitTailScale
import BianchiIX.Dynamics.ProjectiveRegularity
import BianchiIX.Dynamics.ConstrainedComplete

noncomputable section

namespace BianchiIX

open Set

def exitPhysicalRegion (h : ℝ) (y : ProjectiveState) : Prop :=
  y 0 ≤ 0 ∧ (7 / 4 ≤ coreRadius (y 0) (y 2) ∧ coreRadius (y 0) (y 2) ≤ 17 / 4) ∧
    |y 1| ≤ 1 / 100 ∧ (h ≤ y 2 ∧ y 2 ≤ 1) ∧ |y 3| ≤ 1 / 100

theorem isClosed_exitPhysicalRegion (h : ℝ) : IsClosed {y | exitPhysicalRegion h y} := by
  have hr : Continuous (fun y : ProjectiveState => coreRadius (y 0) (y 2)) := by
    unfold coreRadius coreEnergy
    fun_prop
  exact (isClosed_le (continuous_apply 0) continuous_const).inter
    (((isClosed_le continuous_const hr).inter (isClosed_le hr continuous_const)).inter
      ((isClosed_le (continuous_apply 1).abs continuous_const).inter
        (((isClosed_le continuous_const (continuous_apply 2)).inter
          (isClosed_le (continuous_apply 2) continuous_const)).inter
          (isClosed_le (continuous_apply 3).abs continuous_const))))

theorem exitPhysicalRegion_phase_bounds {h : ℝ} {y : ProjectiveState} (hh : 0 < h)
    (hy : exitPhysicalRegion h y) : -5 ≤ y 0 ∧ y 0 < 0 := by
  have hR0 : 0 ≤ coreRadius (y 0) (y 2) := Real.sqrt_nonneg _
  have he := coreRadius_sq (y 0) (y 2)
  dsimp only [coreEnergy] at he
  have hR2 := (sq_le_sq₀ hR0 (by norm_num : (0 : ℝ) ≤ 17 / 4)).mpr hy.2.1.2
  have hv0 : 0 ≤ y 2 := (hh.trans_le hy.2.2.2.1.1).le
  constructor
  · nlinarith only [he, hR2, sq_nonneg (y 2)]
  · by_contra hn
    have hm0 : y 0 = 0 := le_antisymm hy.1 (le_of_not_gt hn)
    nlinarith only [he, hm0, hv0, hy.2.2.2.1.2, hy.2.1.1]

theorem exitPhysicalRegion_clock {h : ℝ} {y : ProjectiveState} (hh : 0 < h)
    (hy : exitPhysicalRegion h y) : 1 / 2 ≤ exitClockRate y :=
  exitClockRate_compact (lt_of_le_of_lt hy.1 (by norm_num)) hy.2.1.1 hy.2.2.1
    ⟨(hh.trans_le hy.2.2.2.1.1).le, hy.2.2.2.1.2⟩ hy.2.2.2.2

/-- A fixed signed tail region bounds the projective denominator away from zero and infinity. -/
theorem exitPhysicalRegion_denom {h : ℝ} {y : ProjectiveState} (hh : 0 < h)
    (hy : exitPhysicalRegion h y) : 0 < projectiveStateDenom y ∧ projectiveStateDenom y ≤ 48 := by
  have hm := exitPhysicalRegion_phase_bounds hh hy
  have hm2 : (y 0) ^ 2 ≤ 25 := by nlinarith only [hm.1, hm.2]
  have hu := abs_le.mp hy.2.2.1
  have hw := abs_le.mp hy.2.2.2.2
  have hv : 0 ≤ y 2 ∧ y 2 ≤ 1 := ⟨(hh.trans_le hy.2.2.2.1.1).le, hy.2.2.2.1.2⟩
  have hu2 : (y 1) ^ 2 ≤ 1 := by nlinarith only [hu.1, hu.2]
  have hvw : |y 2 - y 3| ≤ 2 := by
    have H := abs_sub (y 2) (y 3)
    rw [abs_of_nonneg hv.1] at H
    linarith only [H, hv.2, hy.2.2.2.2]
  have hvw2 : (y 2 - y 3) ^ 2 ≤ 4 := by nlinarith only [hvw, abs_nonneg (y 2 - y 3), sq_abs (y 2 - y 3)]
  have hsum : |y 2 + y 3| ≤ 2 := by
    have H := abs_add_le (y 2) (y 3)
    rw [abs_of_nonneg hv.1] at H
    linarith only [H, hv.2, hy.2.2.2.2]
  have hc : |2 * y 1 * (y 2 + y 3)| ≤ 1 := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have H := mul_le_mul hy.2.2.1 hsum (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 100)
    nlinarith only [H]
  change 0 < projectiveDenom (y 0) (y 1) (y 2) (y 3) ∧ projectiveDenom (y 0) (y 1) (y 2) (y 3) ≤ 48
  rw [projectiveDenom_eq]
  constructor
  · nlinarith only [(abs_le.mp hc).2, sq_nonneg (y 0), sq_nonneg (y 1), sq_nonneg (y 2 - y 3)]
  · nlinarith only [(abs_le.mp hc).1, hm2, hu2, hvw2]

theorem normalized_exit_chart_lower {x : NormalizedState} {h : ℝ} (hh : 0 < h)
    (hA : 1 + x 0 ≠ 0) (hx : stateConstraint x = 1)
    (hy : exitPhysicalRegion h (toProjectiveState x)) : 1 / 8 ≤ 1 + x 0 := by
  have hD := exitPhysicalRegion_denom hh hy
  have H := projective_inverse_scale hA hx
  change 6 / projectiveStateDenom (toProjectiveState x) = 1 + x 0 at H
  rw [← H]
  exact (le_div_iff₀ hD.1).mpr (by linarith only [hD.2])

end BianchiIX
