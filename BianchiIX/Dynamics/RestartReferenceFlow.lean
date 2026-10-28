import BianchiIX.Dynamics.RestartEquations
import BianchiIX.Dynamics.ConstrainedComplete
import BianchiIX.Dynamics.CoreContraction
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def restartReferenceInitial (h : ℝ) : NormalizedState := ![-restartReferenceRoot h, 0, h, 0, 0]

def restartReferenceCurve (h t : ℝ) : NormalizedState := normalizedMaxCurve (restartReferenceInitial h) 0 t

theorem restartReferenceInitial_constraint {h : ℝ} (hh : h ^ 2 ≤ 1) :
    stateConstraint (restartReferenceInitial h) = 1 := by
  change (-restartReferenceRoot h) ^ 2 + 0 ^ 2 + curvature h 0 0 = 1
  simp [curvature, restartReferenceRoot_sq hh]

theorem restartReferenceCurve_initial (h : ℝ) : restartReferenceCurve h 0 = restartReferenceInitial h :=
  normalizedMaxCurve_initial _ _

/-- Vanishing center coordinates are preserved on the whole maximal interval, not only forward in time. -/
theorem restartReferenceCurve_center_zero (h : ℝ) {t : ℝ}
    (ht : t ∈ normalizedMaxDomain (restartReferenceInitial h) 0) :
    restartReferenceCurve h t 1 = 0 ∧ restartReferenceCurve h t 3 = 0 ∧ restartReferenceCurve h t 4 = 0 := by
  let S := maximalNormalizedSolution (restartReferenceInitial h) 0
  have Hw (r : ℝ) (hr : r ∈ S.domain) : S.curve r 3 = 0 ∧ S.curve r 4 = 0 := by
    have H₁ := normalized_wall_formula S.convex_domain S.isOpen_domain S.hasDerivAt S.initial_mem hr 1
    have H₂ := normalized_wall_formula S.convex_domain S.isOpen_domain S.hasDerivAt S.initial_mem hr 2
    rw [S.initial_eq] at H₁ H₂
    simpa [wallValue, restartReferenceInitial] using And.intro H₁ H₂
  have Hs (r : ℝ) (hr : r ∈ S.domain) :
      HasDerivAt (fun q => S.curve q 1) (S.curve r 2 ^ 2 * S.curve r 1) r := by
    simpa [normalizedField, shearMinus, curvature, (Hw r hr).1, (Hw r hr).2] using
      hasDerivAt_pi.mp (S.hasDerivAt r hr) 1
  have H := homogeneous_solution_eq_exp_integral S.convex_domain S.isOpen_domain
    ((continuous_apply 2).comp_continuousOn (HasDerivAt.continuousOn S.hasDerivAt) |>.pow 2)
    Hs S.initial_mem ht
  rw [S.initial_eq] at H
  refine ⟨?_, (Hw t ht).1, (Hw t ht).2⟩
  change S.curve t 1 = 0
  simpa [restartReferenceInitial] using H

theorem restartReferenceCurve_forward {h t : ℝ} (hh : h ^ 2 ≤ 1) (ht : 0 ≤ t) :
    t ∈ normalizedMaxDomain (restartReferenceInitial h) 0 ∧
    HasDerivAt (restartReferenceCurve h) (normalizedField (restartReferenceCurve h t)) t ∧
    stateConstraint (restartReferenceCurve h t) = 1 := by
  have H := normalizedMaxCurve_forward_of_constraint (restartReferenceInitial_constraint hh) ht
  exact ⟨normalizedMaxDomain_contains_Ici_of_constraint (restartReferenceInitial_constraint hh) 0 ht, H.1, H.2.1⟩

theorem restartReferenceCurve_circle {h t : ℝ} (hh : h ^ 2 ≤ 1) (ht : 0 ≤ t) :
    restartReferenceCurve h t 0 ^ 2 + restartReferenceCurve h t 2 ^ 2 = 1 := by
  have HF := restartReferenceCurve_forward hh ht
  obtain ⟨hs, ha, hb⟩ := restartReferenceCurve_center_zero h HF.1
  simpa [stateConstraint, constraint, shearSq, curvature, hs, ha, hb] using HF.2.2

theorem hasDerivAt_restartReference_shear {h t : ℝ} (hh : h ^ 2 ≤ 1) (ht : 0 ≤ t) :
    HasDerivAt (fun r => restartReferenceCurve h r 0)
      (restartReferenceCurve h t 2 ^ 2 * (restartReferenceCurve h t 0 - 2)) t := by
  have HF := restartReferenceCurve_forward hh ht
  have Hw := restartReferenceCurve_center_zero h HF.1
  convert! hasDerivAt_pi.mp HF.2.1 0 using 1
  simp only [normalizedField, Matrix.cons_val_zero, shearPlus, curvature, Hw.2.1, Hw.2.2]
  ring

theorem restartReferenceCurve_shear_le {h t : ℝ} (hh : h ^ 2 ≤ 1) (ht : 0 ≤ t) :
    restartReferenceCurve h t 0 ≤ -restartReferenceRoot h := by
  have HD (r : ℝ) (hr : r ∈ Ici (0 : ℝ)) := hasDerivAt_restartReference_shear hh hr
  have HM : AntitoneOn (fun r => restartReferenceCurve h r 0) (Ici (0 : ℝ)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0) (HasDerivAt.continuousOn HD)
      (fun r hr => (HD r (interior_subset hr)).differentiableAt.differentiableWithinAt)
    intro r hr
    rw [(HD r (interior_subset hr)).deriv]
    apply mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _)
    have HC := restartReferenceCurve_circle hh (interior_subset hr)
    nlinarith only [HC, sq_nonneg (restartReferenceCurve h r 2), sq_nonneg (restartReferenceCurve h r 0 - 1)]
  have H := HM (by simp) ht ht
  simpa only [restartReferenceCurve_initial, restartReferenceInitial, Matrix.cons_val_zero] using H

theorem restartReferenceCurve_shape {h t : ℝ} (hh : h ^ 2 < 1) (ht : 0 ≤ t) :
    restartReferenceCurve h t 2 ^ 2 < 1 ∧
      restartReferenceCurve h t = restartReferenceInitial (restartReferenceCurve h t 2) := by
  have HF := restartReferenceCurve_forward hh.le ht
  have Hw := restartReferenceCurve_center_zero h HF.1
  have hp : restartReferenceCurve h t 0 < 0 :=
    (restartReferenceCurve_shear_le hh.le ht).trans_lt (neg_neg_of_pos (restartReferenceRoot_pos hh))
  have HC := restartReferenceCurve_circle hh.le ht
  refine ⟨by nlinarith only [HC, sq_pos_of_neg hp], ?_⟩
  have Hroot := restart_negative_branch_root HF.2.2 hp
  simp only [Hw.1, Hw.2.1, Hw.2.2, curvature, zero_pow (by norm_num : 2 ≠ 0),
    mul_zero, zero_mul, add_zero, sub_zero] at Hroot
  ext i
  fin_cases i
  · change restartReferenceCurve h t 0 = -restartReferenceRoot (restartReferenceCurve h t 2)
    dsimp only [restartReferenceRoot]
    linarith only [Hroot]
  · exact Hw.1
  · rfl
  · exact Hw.2.1
  · exact Hw.2.2

theorem restartReferenceCurve_strong_pos {h t : ℝ} (hh : 0 < h) (hsmall : h ^ 2 ≤ 1) (ht : 0 ≤ t) :
    0 < restartReferenceCurve h t 2 := by
  let S := maximalNormalizedSolution (restartReferenceInitial h) 0
  apply normalized_wall_pos S.convex_domain S.isOpen_domain S.hasDerivAt S.initial_mem
    (restartReferenceCurve_forward hsmall ht).1 0
  simpa [S.initial_eq, wallValue, restartReferenceInitial] using hh

/-- The actual zero-center strong wall has the uniform decay used in the restart reference comparison. -/
theorem restartReferenceCurve_strong_decay {h t : ℝ} (hh : 0 < h ∧ h ≤ 1 / 16) (ht : 0 ≤ t) :
    0 < restartReferenceCurve h t 2 ∧ restartReferenceCurve h t 2 ≤ h * Real.exp (-2 * t) := by
  have hh2 : h ^ 2 < 1 := by nlinarith only [hh.1, hh.2]
  have hz : 15 / 16 ≤ restartReferenceRoot h := by
    have H := restartReferenceRoot_sq hh2.le
    have Hpos := (restartReferenceRoot_pos hh2).le
    nlinarith only [H, Hpos, hh.1, hh.2]
  have HD (r : ℝ) (hr : r ∈ Ici (0 : ℝ)) :=
    (hasDerivAt_normalized_components (restartReferenceCurve_forward hh2.le hr).2.1).2.2.1
  have HB (r : ℝ) (hr : r ∈ Ici (0 : ℝ)) :
      rateOne (restartReferenceCurve h r 0) (restartReferenceCurve h r 1) * restartReferenceCurve h r 2 ≤
        -2 * restartReferenceCurve h r 2 := by
    have Hp := restartReferenceCurve_shear_le hh2.le hr
    have Hs := (restartReferenceCurve_center_zero h (restartReferenceCurve_forward hh2.le hr).1).1
    apply mul_le_mul_of_nonneg_right _ (restartReferenceCurve_strong_pos hh.1 hh2.le hr).le
    simp only [rateOne, shearSq, Hs, zero_pow (by norm_num : 2 ≠ 0), add_zero]
    nlinarith only [Hp, hz, sq_nonneg (restartReferenceCurve h r 0 + 15 / 16)]
  have HE := le_exp_of_linear_deriv_le (convex_Ici (0 : ℝ)) HD HB (s := 0) (t := t) (by simp) ht ht
  refine ⟨restartReferenceCurve_strong_pos hh.1 hh2.le ht, ?_⟩
  simpa [restartReferenceCurve_initial, restartReferenceInitial] using HE

theorem hasDerivAt_restartReference_strong {h t : ℝ} (hh : h ^ 2 < 1) (ht : 0 ≤ t) :
    HasDerivAt (fun r => restartReferenceCurve h r 2)
      (restartReferenceCurve h t 2 * restartReferenceStrongRate (restartReferenceCurve h t 2)) t := by
  have H := (hasDerivAt_restart_components (restartReferenceCurve_forward hh.le ht).2.1
    (restartReferenceCurve_forward hh.le ht).2.2).1
  have Hroot : restartReferenceCurve h t 0 = -restartReferenceRoot (restartReferenceCurve h t 2) :=
    congrFun (restartReferenceCurve_shape hh ht).2 0
  have Hw := restartReferenceCurve_center_zero h (restartReferenceCurve_forward hh.le ht).1
  have Hdelta : restartStrongRateDifference (restartReferenceCurve h t) = 0 := by
    simp [restartStrongRateDifference, restartCurvatureDifference, restartRootDifference, Hroot, Hw.2.1, Hw.2.2]
  simpa only [Hdelta, add_zero] using H

theorem tendsto_restartReference_strong {h : ℝ} (hh : 0 < h ∧ h ≤ 1 / 16) :
    Tendsto (fun t => restartReferenceCurve h t 2) atTop (𝓝 0) := by
  have HE : Tendsto (fun t : ℝ => h * Real.exp (-2 * t)) atTop (𝓝 0) := by
    convert! (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))).const_mul h using 1
    · ext t
      simp only [Function.comp_def, neg_mul, id_eq]
    · simp
  apply squeeze_zero' _ _ HE
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (restartReferenceCurve_strong_decay hh ht).1.le
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (restartReferenceCurve_strong_decay hh ht).2

end BianchiIX
