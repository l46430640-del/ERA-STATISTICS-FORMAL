import BianchiIX.Algebra.RestartTransferBounds
import BianchiIX.Dynamics.RestartReferenceVariation
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def restartCenterProjection : NormalizedState →L[ℝ] RestartCenterState :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 1, ContinuousLinearMap.proj 3,
    ContinuousLinearMap.proj 4]

def restartSectionRadicand (h : ℝ) (Z : RestartCenterState) : ℝ :=
  1 - Z 0 ^ 2 - curvature h (Z 1) (Z 2)

/-- Ordinary center coordinates on the fixed strong-wall section, including zero weak walls. -/
def restartSectionChart (h : ℝ) (Z : RestartCenterState) : NormalizedState :=
  ![-Real.sqrt (restartSectionRadicand h Z), Z 0, h, Z 1, Z 2]

theorem restartSectionChart_zero (h : ℝ) : restartSectionChart h 0 = restartReferenceInitial h := by
  ext i
  fin_cases i <;> simp [restartSectionChart, restartSectionRadicand, restartReferenceInitial,
    restartReferenceRoot, curvature]

theorem restartSectionChart_constraint {h : ℝ} {Z : RestartCenterState}
    (hZ : 0 ≤ restartSectionRadicand h Z) : stateConstraint (restartSectionChart h Z) = 1 := by
  have H := Real.sq_sqrt hZ
  dsimp [stateConstraint, constraint, shearSq, restartSectionChart]
  rw [neg_sq, H]
  unfold restartSectionRadicand
  ring

theorem restartCenterProjection_section (h : ℝ) (Z : RestartCenterState) :
    restartCenterProjection (restartSectionChart h Z) = Z := by
  ext i
  fin_cases i <;> rfl

theorem contDiffAt_restartSectionChart_zero {h : ℝ} (hh : h ^ 2 < 1) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k (restartSectionChart h) 0 := by
  have hr : ContDiff ℝ k (restartSectionRadicand h) := by
    unfold restartSectionRadicand curvature
    fun_prop
  have h0 : restartSectionRadicand h 0 ≠ 0 := by
    simpa [restartSectionRadicand, curvature] using (sub_pos.mpr hh).ne'
  rw [contDiffAt_pi]
  intro i
  fin_cases i
  · exact (hr.contDiffAt.sqrt h0).neg
  · exact contDiffAt_apply ℝ ℝ (0 : Fin 3) 0
  · exact contDiffAt_const
  · exact contDiffAt_apply ℝ ℝ (1 : Fin 3) 0
  · exact contDiffAt_apply ℝ ℝ (2 : Fin 3) 0

theorem restartCenterProjection_section_differential {h : ℝ} (hh : h ^ 2 < 1) :
    restartCenterProjection.comp (fderiv ℝ (restartSectionChart h) 0) =
      ContinuousLinearMap.id ℝ RestartCenterState := by
  have HD := (contDiffAt_restartSectionChart_zero hh 1).differentiableAt (by norm_num)
  have H := restartCenterProjection.hasFDerivAt.comp 0 HD.hasFDerivAt
  have H' : HasFDerivAt (fun Z : RestartCenterState => Z)
      (restartCenterProjection.comp (fderiv ℝ (restartSectionChart h) 0)) 0 := by
    simpa only [Function.comp_def, restartCenterProjection_section] using H
  exact H'.unique (hasFDerivAt_id 0)

def restartSectionCenterFlow (h t : ℝ) (Z : RestartCenterState) : RestartCenterState :=
  restartCenterProjection (normalizedMaxCurve (restartSectionChart h Z) 0 t)

def restartReferenceCenterDifferential (h t : ℝ) : RestartCenterState →L[ℝ] RestartCenterState :=
  restartCenterProjection.comp ((normalizedFlowDifferential (restartReferenceInitial h) 0 t).comp
    (fderiv ℝ (restartSectionChart h) 0))

/-- The reference matrix is the ordinary derivative of the exact flow on the physical section. -/
theorem hasFDerivAt_restartSectionCenterFlow_zero {h t : ℝ} (hh : h ^ 2 < 1) (ht : 0 ≤ t) :
    HasFDerivAt (restartSectionCenterFlow h t) (restartReferenceCenterDifferential h t) 0 := by
  have HD := (contDiffAt_restartSectionChart_zero hh 1).differentiableAt (by norm_num)
  have HF := hasFDerivAt_normalizedMaxCurve_initial (restartReferenceCurve_forward hh.le ht).1
  rw [← restartSectionChart_zero h] at HF
  have H := restartCenterProjection.hasFDerivAt.comp 0 (HF.comp 0 HD.hasFDerivAt)
  rw [restartSectionChart_zero] at H
  convert! H using 1

theorem restartReferenceCenterDifferential_initial {h : ℝ} (hh : h ^ 2 < 1) :
    restartReferenceCenterDifferential h 0 = ContinuousLinearMap.id ℝ RestartCenterState := by
  simpa only [restartReferenceCenterDifferential, normalizedFlowDifferential_initial,
    ContinuousLinearMap.id_comp] using restartCenterProjection_section_differential hh

theorem restartReferenceCenterDifferential_conservation {h t : ℝ} (hh : h ^ 2 < 1) (ht : 0 ≤ t) :
    (restartCenterTransfer (restartReferenceCurve h t 2)).comp (restartReferenceCenterDifferential h t) =
      restartCenterTransfer h := by
  ext Z i
  let d := fderiv ℝ (restartSectionChart h) 0 Z
  have Hd : restartCenterProjection d = Z :=
    congrArg (fun L : RestartCenterState →L[ℝ] RestartCenterState => L Z)
      (restartCenterProjection_section_differential hh)
  have hds : d 1 = Z 0 := congrFun Hd 0
  have hda : d 3 = Z 1 := congrFun Hd 1
  have hdb : d 4 = Z 2 := congrFun Hd 2
  obtain ⟨Hs, Ha, Hb⟩ := restartReferenceVariation_conservation hh ht d
  simp only [hds, hda, hdb] at Hs Ha Hb
  fin_cases i
  · exact Hs
  · exact Ha
  · exact Hb

/-- Uniform operator bounds follow from the finite conservation identity and strong-wall decay. -/
theorem restartReferenceCenterDifferential_bounds {h t : ℝ}
    (hh : 0 < h ∧ h ≤ 1 / 16) (ht : 0 ≤ t) :
    ‖restartReferenceCenterDifferential h t‖ ≤ 2 ∧
      ‖restartReferenceCenterDifferential h t - restartCenterTransfer h‖ ≤ 6 * h * Real.exp (-2 * t) := by
  have hh2 : h ^ 2 < 1 := by nlinarith only [hh.1, hh.2]
  obtain ⟨hn0, hnexp⟩ := restartReferenceCurve_strong_decay hh ht
  have hn : restartReferenceCurve h t 2 ≤ 1 / 16 := by
    have he : Real.exp (-2 * t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [ht])
    have H := mul_le_mul_of_nonneg_left he hh.1.le
    nlinarith only [hnexp, H, hh.2]
  obtain ⟨HY, Htail⟩ := restartCenterTransfer_conserved_bounds ⟨hh.1.le, hh.2⟩ ⟨hn0.le, hn⟩
    (restartReferenceCenterDifferential h t) (restartReferenceCenterDifferential_conservation hh2 ht)
  exact ⟨HY, Htail.trans (by nlinarith only [hnexp])⟩

/-- At the logarithmic cutoff the linear reference error has the full power required in (E.1). -/
theorem restartReferenceCenterDifferential_cutoff {h ρ q : ℝ}
    (hh : 0 < h ∧ h ≤ 1 / 16) (hρ : 0 < ρ ∧ ρ ≤ 1) (hq : 0 ≤ q) :
    let T := q / 2 * Real.log (1 / ρ)
    0 < restartReferenceCurve h T 2 ∧ restartReferenceCurve h T 2 ≤ h * ρ ^ q ∧
      ‖restartReferenceCenterDifferential h T - restartCenterTransfer h‖ ≤ 6 * h * ρ ^ q := by
  let T := q / 2 * Real.log (1 / ρ)
  have hlog : 0 ≤ Real.log (1 / ρ) :=
    Real.log_nonneg ((le_div_iff₀ hρ.1).mpr (by linarith only [hρ.2]))
  have hT : 0 ≤ T := mul_nonneg (div_nonneg hq (by norm_num)) hlog
  have he : Real.exp (-2 * T) = ρ ^ q := by
    rw [Real.rpow_def_of_pos hρ.1]
    congr 1
    dsimp only [T]
    rw [one_div, Real.log_inv]
    ring
  obtain ⟨hn0, hn⟩ := restartReferenceCurve_strong_decay hh hT
  have H := (restartReferenceCenterDifferential_bounds hh hT).2
  rw [he] at hn H
  exact ⟨hn0, hn, H⟩

end BianchiIX
