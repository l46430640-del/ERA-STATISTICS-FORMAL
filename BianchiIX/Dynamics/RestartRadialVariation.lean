import BianchiIX.Dynamics.RestartRadialDifferential
import BianchiIX.Dynamics.RestartQuadraticControl

noncomputable section

namespace BianchiIX

def restartSectionRadialState (h t : ℝ) (Z : RestartCenterState) : RestartRadialState :=
  (restartSectionStrongWall h t Z, restartSectionCenterFlow h t Z)

theorem restartSectionRadialState_derivative {h t : ℝ} {Z : RestartCenterState}
    (hh : 0 < h) (hZ : 0 < restartSectionRadicand h Z) (ht : 0 ≤ t)
    (HD : DifferentiableAt ℝ (restartSectionMixedFlow h t) Z)
    (HB : ‖fderiv ℝ (restartSectionMixedFlow h t) Z‖ ≤ 2)
    (hn : restartSectionStrongWall h t Z ≤ 1) :
    DifferentiableAt ℝ (restartSectionRadialState h t) Z ∧
      ‖fderiv ℝ (restartSectionRadialState h t) Z‖ ≤ 2 ∧
      ∀ v : RestartCenterState,
        |(fderiv ℝ (restartSectionRadialState h t) Z v).1| ≤
          2 * restartSectionStrongWall h t Z * ‖v‖ := by
  have Hn := hasFDerivAt_restartSectionStrongWall hh hZ ht HD
  have HZ := hasFDerivAt_restartSectionCenterFlow_of_mixed hh HD
  have HP := Hn.prodMk HZ
  change HasFDerivAt (restartSectionRadialState h t) _ Z at HP
  have hnpos := restartSectionStrongWall_pos hh hZ.le ht
  have Hlog := (restartSectionStrongLog_fderiv_norm_le hh HD).trans HB
  have hnD : ‖fderiv ℝ (restartSectionStrongWall h t) Z‖ ≤ 2 * restartSectionStrongWall h t Z := by
    rw [restartSectionStrongWall_fderiv_norm hh hZ ht HD]
    nlinarith only [mul_le_mul_of_nonneg_left Hlog hnpos.le]
  have hZD : ‖fderiv ℝ (restartSectionCenterFlow h t) Z‖ ≤ 2 := by
    rw [HZ.fderiv]
    exact (restartCompactCenterProjection_comp_norm_le _).trans HB
  have hfst (v : RestartCenterState) :
      |(fderiv ℝ (restartSectionRadialState h t) Z v).1| ≤ 2 * restartSectionStrongWall h t Z * ‖v‖ := by
    rw [HP.fderiv]
    change |(restartSectionStrongWall h t Z • fderiv ℝ (restartSectionStrongLog h t) Z) v| ≤ _
    rw [← Hn.fderiv]
    exact ((fderiv ℝ (restartSectionStrongWall h t) Z).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right hnD (norm_nonneg _))
  refine ⟨HP.differentiableAt, ?_, hfst⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  rw [Prod.norm_def, max_le_iff]
  constructor
  · exact (hfst v).trans (by nlinarith only [mul_le_mul_of_nonneg_right hn (norm_nonneg v)])
  · rw [HP.fderiv]
    change ‖(restartCompactCenterProjection.comp (fderiv ℝ (restartSectionMixedFlow h t) Z)) v‖ ≤ _
    rw [← HZ.fderiv]
    exact ((fderiv ℝ (restartSectionCenterFlow h t) Z).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right hZD (norm_nonneg _))

theorem restartSectionQuadratic_derivative_bound {h t A b : ℝ} {Z : RestartCenterState}
    (hA : 0 ≤ A) (hb : 0 ≤ b)
    (HD : DifferentiableAt ℝ (restartSectionRadialState h t) Z)
    (HB : ‖fderiv ℝ (restartSectionRadialState h t) Z‖ ≤ 2)
    (hn : restartSectionStrongWall h t Z ^ 2 < 1)
    (HQ : ‖fderiv ℝ restartRadialQuadratic (restartSectionRadialState h t Z)‖ ≤ A * b) :
    DifferentiableAt ℝ (restartSectionQuadratic h t) Z ∧
      ‖fderiv ℝ (restartSectionQuadratic h t) Z‖ ≤ 2 * A * b := by
  have H := ((contDiffAt_restartRadialQuadratic hn 1).differentiableAt (by norm_num)).hasFDerivAt.comp Z HD.hasFDerivAt
  change HasFDerivAt (restartSectionQuadratic h t) _ Z at H
  refine ⟨H.differentiableAt, ?_⟩
  rw [H.fderiv]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul HQ HB (norm_nonneg _) (mul_nonneg hA hb)).trans_eq (by ring))

theorem restartSectionQuadraticRate_derivative_bound {h t A b : ℝ} {Z : RestartCenterState}
    (hA : 0 ≤ A) (hb : 0 ≤ b ∧ b ≤ 1)
    (HD : DifferentiableAt ℝ (restartSectionRadialState h t) Z)
    (HB : ‖fderiv ℝ (restartSectionRadialState h t) Z‖ ≤ 2)
    (Hn : ∀ v : RestartCenterState,
      |(fderiv ℝ (restartSectionRadialState h t) Z v).1| ≤ 2 * restartSectionStrongWall h t Z * ‖v‖)
    (hn : 0 ≤ restartSectionStrongWall h t Z ∧ restartSectionStrongWall h t Z ≤ 1 / 16)
    (hcenter : ‖restartSectionCenterFlow h t Z‖ ≤ b)
    (hrad : 0 < restartSectionRadicand (restartSectionStrongWall h t Z) (restartSectionCenterFlow h t Z))
    (HF : ∀ w : RestartRadialState,
      |fderiv ℝ restartRadialDrift (restartSectionRadialState h t Z) w| ≤
        A * ‖restartSectionCenterFlow h t Z‖ ^ 3 * |w.1| +
          A * (restartSectionStrongWall h t Z * ‖restartSectionCenterFlow h t Z‖ ^ 2 +
            ‖restartSectionCenterFlow h t Z‖ ^ 3) * ‖w.2‖) :
    DifferentiableAt ℝ (restartSectionQuadraticRate h t) Z ∧
      ‖fderiv ℝ (restartSectionQuadraticRate h t) Z‖ ≤
        4 * A * (restartSectionStrongWall h t Z * b ^ 2 + b ^ 3) := by
  have hn0 : 0 ≤ restartSectionStrongWall h t Z := hn.1
  have hb0 : 0 ≤ b := hb.1
  have hn2 : restartSectionStrongWall h t Z ^ 2 < 1 := by nlinarith only [hn.1, hn.2]
  have H := ((contDiffAt_restartRadialDrift (p := restartSectionRadialState h t Z) hn2 hrad).differentiableAt
    (by norm_num)).hasFDerivAt.comp Z HD.hasFDerivAt
  change HasFDerivAt (restartSectionQuadraticRate h t) _ Z at H
  refine ⟨H.differentiableAt, ?_⟩
  rw [H.fderiv]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have HW : ‖(fderiv ℝ (restartSectionRadialState h t) Z v).2‖ ≤ 2 * ‖v‖ :=
    (norm_snd_le _).trans (((fderiv ℝ (restartSectionRadialState h t) Z).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right HB (norm_nonneg _)))
  have Hcube : b ^ 3 ≤ b ^ 2 := by
    nlinarith only [mul_nonneg (sq_nonneg b) (sub_nonneg.mpr hb.2)]
  calc
    _ ≤ A * ‖restartSectionCenterFlow h t Z‖ ^ 3 * |(fderiv ℝ (restartSectionRadialState h t) Z v).1| +
        A * (restartSectionStrongWall h t Z * ‖restartSectionCenterFlow h t Z‖ ^ 2 +
          ‖restartSectionCenterFlow h t Z‖ ^ 3) * ‖(fderiv ℝ (restartSectionRadialState h t) Z v).2‖ := HF _
    _ ≤ A * b ^ 3 * (2 * restartSectionStrongWall h t Z * ‖v‖) +
        A * (restartSectionStrongWall h t Z * b ^ 2 + b ^ 3) * (2 * ‖v‖) := by
      gcongr
      exact Hn v
    _ ≤ _ := by
      nlinarith only [mul_le_mul_of_nonneg_left Hcube
        (by positivity : 0 ≤ A * restartSectionStrongWall h t Z * ‖v‖),
        mul_nonneg (mul_nonneg hA (pow_nonneg hb0 3)) (norm_nonneg v)]

end BianchiIX
