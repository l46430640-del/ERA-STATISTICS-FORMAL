import BianchiIX.Dynamics.ExitTailCoordinates
import BianchiIX.Dynamics.ExitTailRegularity
import BianchiIX.Analysis.CoordinateDerivativeNorm

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

/-- At fixed height, reconstruction of the descending shear costs at most a factor two. -/
theorem fromExitTailState_fderiv_bound {h : ℝ} {Y : ExitTailState}
    (hR : 7 / 4 ≤ Y 0) (hh : |h| ≤ 1) :
    ContDiffAt ℝ 2 (fromExitTailState h) Y ∧ ‖fderiv ℝ (fromExitTailState h) Y‖ ≤ 2 := by
  have hR0 : 0 < Y 0 := by linarith only [hR]
  have hR2 := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 7 / 4) hR0.le).mpr hR
  have hh2 : h ^ 2 ≤ 1 := by nlinarith only [sq_abs h, sq_nonneg (|h| - 1), hh, abs_nonneg h]
  have hgap : h ^ 2 < (Y 0) ^ 2 := by nlinarith only [hR2, hh2]
  have hg0 : 0 < exitTailGap (Y 0) h := Real.sqrt_pos.mpr (sub_pos.mpr hgap)
  have hratio : |Y 0 / exitTailGap (Y 0) h| ≤ 2 := by
    rw [abs_of_pos (div_pos hR0 hg0)]
    apply (div_le_iff₀ hg0).mpr
    nlinarith only [exitTailGap_sq hgap.le, hR2, hh2, hg0, hR0]
  have hgapreg : ContDiffAt ℝ 2 (fun Z : ExitTailState => exitTailGap (Z 0) h) Y := by
    unfold exitTailGap
    have H0 : ContDiffAt ℝ 2 (fun Z : ExitTailState => Z 0) Y := by fun_prop
    exact ((H0.pow 2).sub contDiffAt_const).sqrt
      (sub_pos.mpr hgap).ne'
  have Hreg : ContDiffAt ℝ 2 (fromExitTailState h) Y := by
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i
    · exact contDiffAt_const.sub hgapreg
    all_goals dsimp [fromExitTailState]; fun_prop
  have Hsqrt := (((hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) Y).pow 2).sub_const (h ^ 2)).sqrt
    (sub_pos.mpr hgap).ne'
  have HM := (hasFDerivAt_const (1 : ℝ) Y).sub Hsqrt
  change HasFDerivAt (fun Z : ExitTailState => 1 - exitTailGap (Z 0) h) _ Y at HM
  have Hformula (v : ExitTailState) :
      fderiv ℝ (fun Z : ExitTailState => 1 - exitTailGap (Z 0) h) Y v =
        -(Y 0 / exitTailGap (Y 0) h) * v 0 := by
    rw [HM.fderiv]
    simp only [sub_apply, zero_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
    unfold exitTailGap
    ring
  refine ⟨Hreg, fderiv_norm_le_of_coordinate_bounds (by norm_num)
    (Hreg.differentiableAt (by norm_num)) ?_⟩
  intro i
  fin_cases i
  · apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro v
    change |fderiv ℝ (fun Z : ExitTailState => 1 - exitTailGap (Z 0) h) Y v| ≤ _
    rw [Hformula, abs_mul, abs_neg]
    exact mul_le_mul hratio (norm_le_pi_norm v 0) (abs_nonneg _) (by norm_num)
  · change ‖fderiv ℝ (fun Z : ExitTailState => Z 1) Y‖ ≤ 2
    rw [(hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 3) Y).fderiv]
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro v
    exact (norm_le_pi_norm v 1).trans (by nlinarith only [norm_nonneg v])
  · change ‖fderiv ℝ (fun _ : ExitTailState => h) Y‖ ≤ 2
    simp
  · change ‖fderiv ℝ (fun Z : ExitTailState => Z 2) Y‖ ≤ 2
    rw [(hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 3) Y).fderiv]
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro v
    exact (norm_le_pi_norm v 2).trans (by nlinarith only [norm_nonneg v])

theorem coreTailState_eventuallyEq_reconstruction {h : ℝ} {Y : ExitTailState}
    (hR : 1 < Y 0) (HV : coreTailValid h Y) (hm : coreTailState h Y 0 < 1) :
    coreTailState h =ᶠ[𝓝 Y] (fun Z => fromExitTailState h (toExitTailState (coreTailState h Z))) := by
  have HR := coreTail_regular_of_valid hR HV
  have Hm := (continuousAt_pi.mp HR.2.1.continuousAt 0).eventually (isOpen_Iio.mem_nhds hm)
  filter_upwards [HR.2.2, Hm] with Z hZ hmZ
  have H := fromExitTailState_toExitTailState hmZ
  rw [coreTailState_active hZ] at H
  exact H.symm

theorem coreTailState_fderiv_bound_of_radial {h B : ℝ} {Y : ExitTailState}
    (hR : 1 < Y 0) (HV : coreTailValid h Y) (hm : coreTailState h Y 0 < 1)
    (hr : 7 / 4 ≤ coreRadius (coreTailState h Y 0) (coreTailState h Y 2)) (hh : |h| ≤ 1)
    (HF : ContDiffAt ℝ 2 (fun Z => toExitTailState (coreTailState h Z)) Y)
    (HB : ‖fderiv ℝ (fun Z => toExitTailState (coreTailState h Z)) Y‖ ≤ B) :
    ‖fderiv ℝ (coreTailState h) Y‖ ≤ 2 * B := by
  have HE := coreTailState_eventuallyEq_reconstruction hR HV hm
  have HG := fromExitTailState_fderiv_bound (Y := toExitTailState (coreTailState h Y)) (h := h) hr hh
  rw [HE.fderiv_eq]
  change ‖fderiv ℝ (fromExitTailState h ∘ fun Z => toExitTailState (coreTailState h Z)) Y‖ ≤ _
  rw [fderiv_comp Y (HG.1.differentiableAt (by norm_num)) (HF.differentiableAt (by norm_num))]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul HG.2 HB (norm_nonneg _) (by norm_num))

end BianchiIX
