import BianchiIX.Dynamics.CoreSectionPhysical
import Mathlib.Topology.Order.MonotoneConvergence

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def normalizedWallProduct (x : NormalizedState) : ℝ := x 2 * x 3 * x 4

theorem normalizedWallProduct_axisFrame (i : Fin 6) (x : NormalizedState) :
    normalizedWallProduct ((axisFrame i).map x) = normalizedWallProduct x := by
  fin_cases i <;> simp [axisFrame_apply, normalizedWallProduct, axisCycle_wall_product, axisSwap_wall_product]

/-- Small transverse amplitudes force the physical wall product to zero uniformly in the core radius. -/
theorem normalizedWallProduct_coreRadiusEntry_bound {Y : CoreAngleState} {B : ℝ}
    (hu : 0 ≤ Y 1) (hw : 0 ≤ Y 2) (hsum : Y 1 + Y 2 ≤ B) (hB : B ≤ 1 / 4) :
    0 ≤ normalizedWallProduct (fromProjectiveState (coreRadiusEntry Y)) ∧
      normalizedWallProduct (fromProjectiveState (coreRadiusEntry Y)) ≤ B ^ 2 := by
  let y := coreRadiusEntry Y
  have hdenom : projectiveStateDenom y = 4 + (y 0) ^ 2 + (Y 1 - Y 2) ^ 2 - 2 * (Y 1 + Y 2) := by
    dsimp [y, coreRadiusEntry, projectiveStateDenom, projectiveDenom, curvature]
    ring
  have hm : 1 ≤ y 0 := by
    change 1 ≤ 1 + Real.sqrt (Y 0 ^ 2 - 1)
    linarith only [Real.sqrt_nonneg (Y 0 ^ 2 - 1)]
  have hD : 4 ≤ projectiveStateDenom y := by
    rw [hdenom]
    nlinarith only [hsum, hB, hm, sq_nonneg (Y 1 - Y 2)]
  have hDpos : 0 < projectiveStateDenom y := lt_of_lt_of_le (by norm_num) hD
  have hr : (3 / 2 : ℝ) ≤ Real.sqrt 3 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
  have hrpos : 0 < Real.sqrt 3 := lt_of_lt_of_le (by norm_num) hr
  let a := (6 / projectiveStateDenom y) / Real.sqrt 3
  have ha : 0 ≤ a := (div_pos (div_pos (by norm_num) hDpos) hrpos).le
  have ha1 : a ≤ 1 := (div_le_iff₀ hrpos).mpr
    (((div_le_iff₀ hDpos).mpr (by linarith only [hD]) : 6 / projectiveStateDenom y ≤ 3 / 2).trans
      (by simpa only [one_mul] using hr))
  have heq : normalizedWallProduct (fromProjectiveState y) = a ^ 3 * Y 1 * Y 2 := by
    change (6 / projectiveStateDenom y * Y 1 / Real.sqrt 3) *
      (6 / projectiveStateDenom y * 1 / Real.sqrt 3) *
      (6 / projectiveStateDenom y * Y 2 / Real.sqrt 3) = _
    dsimp only [a]
    ring
  have hB0 : 0 ≤ B := (add_nonneg hu hw).trans hsum
  have hUB : Y 1 ≤ B := (le_add_of_nonneg_right hw).trans hsum
  have hWB : Y 2 ≤ B := (le_add_of_nonneg_left hu).trans hsum
  change 0 ≤ normalizedWallProduct (fromProjectiveState y) ∧ _
  rw [heq]
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ (1 : ℝ) ^ 3 * B * B := by gcongr
    _ = _ := by ring

/-- A positive physical orbit cannot have core arrivals with vanishing wall product accumulating at a finite time. -/
theorem coreArrivalTime_tendsto_atTop {x : NormalizedState} {t B : ℕ → ℝ}
    {Y : ℕ → CoreAngleState} {a : ℕ → Fin 6}
    (hp : positiveWalls x) (hc : stateConstraint x = 1)
    (ht : Monotone t) (ht0 : ∀ n, 0 ≤ t n)
    (hB : Tendsto B atTop (𝓝 0))
    (hsmall : ∀ n, 0 ≤ Y n 1 ∧ 0 ≤ Y n 2 ∧ Y n 1 + Y n 2 ≤ B n ∧ B n ≤ 1 / 4)
    (hactual : ∀ n, fromProjectiveState (coreRadiusEntry (Y n)) =
      (axisFrame (a n)).map (normalizedMaxCurve x 0 (t n))) : Tendsto t atTop atTop := by
  have hbounds (n : ℕ) : 0 ≤ normalizedWallProduct (normalizedMaxCurve x 0 (t n)) ∧
      normalizedWallProduct (normalizedMaxCurve x 0 (t n)) ≤ (B n) ^ 2 := by
    obtain ⟨hu, hw, hs, hcap⟩ := hsmall n
    have H := normalizedWallProduct_coreRadiusEntry_bound hu hw hs hcap
    rw [hactual n, normalizedWallProduct_axisFrame] at H
    exact H
  have hzero : Tendsto (fun n => normalizedWallProduct (normalizedMaxCurve x 0 (t n))) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => (hbounds n).1) (fun n => (hbounds n).2)
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hB.pow 2
  rcases tendsto_atTop_of_monotone ht with htop | ⟨T, hT⟩
  · exact htop
  · have hT0 : 0 ≤ T := ge_of_tendsto hT (Filter.Eventually.of_forall ht0)
    have hflow := (normalizedMaxCurve_forward hp hc hT0).1.continuousAt.tendsto.comp hT
    have hprod : Tendsto (fun n => normalizedWallProduct (normalizedMaxCurve x 0 (t n))) atTop
        (𝓝 (normalizedWallProduct (normalizedMaxCurve x 0 T))) := by
      have hcont : Continuous normalizedWallProduct := by unfold normalizedWallProduct; fun_prop
      exact hcont.continuousAt.tendsto.comp hflow
    have hpositive := (normalizedMaxCurve_forward hp hc hT0).2.1
    have hprodpos : 0 < normalizedWallProduct (normalizedMaxCurve x 0 T) :=
      mul_pos (mul_pos hpositive.1 hpositive.2.1) hpositive.2.2
    exact False.elim (ne_of_gt hprodpos (tendsto_nhds_unique hprod hzero))

end BianchiIX
