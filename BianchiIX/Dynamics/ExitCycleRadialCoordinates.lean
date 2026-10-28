import BianchiIX.Dynamics.ProjectiveCycleDerivativeBounds
import BianchiIX.Dynamics.ExitTailCoordinates
import BianchiIX.Algebra.ExitCycleEndpoint
import BianchiIX.Analysis.CompositionDerivativeBounds
import Mathlib.Topology.Order.Compact

noncomputable section

namespace BianchiIX

open Set

/-- Coordinates are ordered (R,V,U,W), with the descending choice of the shear. -/
def exitTailCoordinateMap (z : ProjectiveState) : ProjectiveState :=
  fromExitTailState (z 1) ![z 0, z 2, z 3]

theorem contDiffAt_exitTailCoordinateMap (n : WithTop ℕ∞) {z : ProjectiveState}
    (hz : (z 1) ^ 2 < (z 0) ^ 2) : ContDiffAt ℝ n exitTailCoordinateMap z := by
  have hgap : ContDiffAt ℝ n (fun p : ProjectiveState => exitTailGap (p 0) (p 1)) z := by
    unfold exitTailGap
    have H : ContDiffAt ℝ n (fun p : ProjectiveState => (p 0) ^ 2 - (p 1) ^ 2) z := by fun_prop
    exact H.sqrt (ne_of_gt (sub_pos.mpr hz))
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact contDiffAt_const.sub hgap
  all_goals dsimp [exitTailCoordinateMap, fromExitTailState]; fun_prop

theorem exists_exitTailCoordinateMap_derivative_bounds :
    ∃ K ≥ (1 : ℝ), ∀ z : ProjectiveState,
      (7 / 4 ≤ z 0 ∧ z 0 ≤ 17 / 4) → |z 1| ≤ 1 → |z 2| ≤ 1 → |z 3| ≤ 1 →
      ‖fderiv ℝ exitTailCoordinateMap z‖ ≤ K ∧
        ‖fderiv ℝ (fderiv ℝ exitTailCoordinateMap) z‖ ≤ K := by
  let S : Set ProjectiveState := Icc ![7 / 4, -1, -1, -1] ![17 / 4, 1, 1, 1]
  have hS : IsCompact S := isCompact_Icc
  let q := fun z : ProjectiveState => ‖fderiv ℝ exitTailCoordinateMap z‖ +
    ‖fderiv ℝ (fderiv ℝ exitTailCoordinateMap) z‖
  have hcont : ContinuousOn q S := by
    intro z hz
    have hR : 7 / 4 ≤ z 0 := hz.1 0
    have hv : |z 1| ≤ 1 := abs_le.mpr ⟨hz.1 1, hz.2 1⟩
    have hv2 : (z 1) ^ 2 ≤ 1 := by nlinarith only [sq_abs (z 1), sq_nonneg (|z 1| - 1), hv, abs_nonneg (z 1)]
    have hreg := contDiffAt_exitTailCoordinateMap 2 (by nlinarith only [hv2, hR])
    have hreg' := hreg.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    exact ((hreg.continuousAt_fderiv (by norm_num)).norm.add
      (hreg'.continuousAt_fderiv (by norm_num)).norm).continuousWithinAt
  obtain ⟨K, hK⟩ := hS.exists_bound_of_continuousOn hcont
  refine ⟨max K 1, le_max_right _ _, ?_⟩
  intro z hR hv hu hw
  have hz : z ∈ S := by
    constructor
    · intro i
      fin_cases i
      · exact hR.1
      · exact (abs_le.mp hv).1
      · exact (abs_le.mp hu).1
      · exact (abs_le.mp hw).1
    · intro i
      fin_cases i
      · exact hR.2
      · exact (abs_le.mp hv).2
      · exact (abs_le.mp hu).2
      · exact (abs_le.mp hw).2
  have H : q z ≤ max K 1 := (le_abs_self _).trans ((hK z hz).trans (le_max_left _ _))
  dsimp only [q] at H
  constructor <;> linarith only [H, norm_nonneg (fderiv ℝ exitTailCoordinateMap z),
    norm_nonneg (fderiv ℝ (fderiv ℝ exitTailCoordinateMap) z)]

/-- The same powers in D.20 hold in the ordinary radial coordinates (R,V,U,W). -/
theorem exists_exitCycle_radial_derivative_bounds :
    ∃ C > (0 : ℝ), ∀ α B R u v w : ℝ,
      (0 < α ∧ α ≤ 1) → B ≤ α / 10000 → |R - (2 + 2 * α)| ≤ B →
      |u| + |w| ≤ B → (0 ≤ v ∧ v ≤ α / 100) → ∀ i : Fin 4,
      let z : ProjectiveState := ![R, v, u, w]
      let f := fun p : ProjectiveState => projectiveCycle (exitTailCoordinateMap p) i
      ‖fderiv ℝ f z‖ ≤ C / α ^ 2 ∧ ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ C / α ^ 3 := by
  obtain ⟨K, hK, HK⟩ := exists_exitTailCoordinateMap_derivative_bounds
  have hK0 : 0 < K := lt_of_lt_of_le (by norm_num) hK
  refine ⟨24 * K + 320 * K ^ 2, by positivity, ?_⟩
  intro α B R u v w hα hB hR hw hv i z f
  have hα0 : 0 < α := hα.1
  have hRc := abs_le.mp hR
  have hRbounds : 7 / 4 ≤ R ∧ R ≤ 17 / 4 := by constructor <;> linarith only [hRc.1, hRc.2, hB, hα.1, hα.2]
  have hv1 : |v| ≤ 1 := by rw [abs_of_nonneg hv.1]; linarith only [hv.2, hα.2]
  have hu1 : |u| ≤ 1 := by linarith only [hw, hB, hα.2, abs_nonneg w]
  have hw1 : |w| ≤ 1 := by linarith only [hw, hB, hα.2, abs_nonneg u]
  have Hchart := HK z hRbounds hv1 hu1 hw1
  have hreg : ContDiffAt ℝ 2 exitTailCoordinateMap z := contDiffAt_exitTailCoordinateMap 2
    (by change v ^ 2 < R ^ 2; nlinarith only [hRbounds.1, hv.1, hv.2, hα.2])
  let y := exitTailCoordinateMap z
  have HD := exitTailGap_terminal_offset hα hB hR hv
  have hm : |y 0 + 1| ≤ 3 * α := by
    change |1 - exitTailGap R v + 1| ≤ _
    apply abs_le.mpr
    constructor <;> linarith only [HD.1, HD.2, hα.1]
  have hw' : |y 1| + |y 2| + |y 3| ≤ 3 * α := by
    change |u| + |v| + |w| ≤ _
    rw [abs_of_nonneg hv.1]
    linarith only [hw, hB, hv.2, hα.1]
  have hH : 39 / 10 * α ^ 2 ≤ projectiveCycleDenom y := by
    have HH := (exitCycleDenom_terminal_bounds hα hB hR hw hv).1
    change 39 / 10 * α ^ 2 ≤ axisCycleDenom (1 - exitTailGap R v) u v w
    nlinarith only [HH, sq_nonneg α]
  have hH0 : projectiveCycleDenom y ≠ 0 := (lt_of_lt_of_le (by positivity) hH).ne'
  have Hcycle := projectiveCycle_terminal_operator_bounds hα.1 hH hm hw' i
  have hg := contDiffAt_pi.mp (contDiffAt_projectiveCycle 2 hH0) i
  have H := composition_second_derivative_bounds hreg hg (by positivity) (by positivity) hK0.le
    Hchart.1 Hchart.2 Hcycle.1 Hcycle.2
  change ‖fderiv ℝ f z‖ ≤ (24 / α ^ 2) * K ∧
    ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ (24 / α ^ 2) * K + (320 / α ^ 3) * K ^ 2 at H
  have hpow : α ^ 3 ≤ α ^ 2 := by nlinarith only [mul_le_mul_of_nonneg_right hα.2 (sq_nonneg α)]
  have Hscale : (24 / α ^ 2) * K ≤ (24 / α ^ 3) * K :=
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (by norm_num) (pow_pos hα.1 3) hpow) hK0.le
  constructor
  · exact H.1.trans (by
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ (sq_nonneg α)
      nlinarith only [sq_nonneg K])
  · calc
      _ ≤ (24 / α ^ 3) * K + (320 / α ^ 3) * K ^ 2 := by linarith only [H.2, Hscale]
      _ = _ := by ring

end BianchiIX
