import BianchiIX.Dynamics.RestartMixedVariation

noncomputable section

namespace BianchiIX

open Set

def restartCenterInclusion : RestartCenterState →L[ℝ] RestartState :=
  ContinuousLinearMap.pi ![0, ContinuousLinearMap.proj 0, ContinuousLinearMap.proj 1, ContinuousLinearMap.proj 2]

def restartMixedSection (h : ℝ) (Z : RestartCenterState) : RestartState :=
  ![Real.log h, Z 0, Z 1, Z 2]

def restartSectionMixedFlow (h t : ℝ) (Z : RestartCenterState) : RestartState :=
  restartMixedFlow (restartMixedSection h Z, t)

theorem restartCenterInclusion_norm (v : RestartCenterState) : ‖restartCenterInclusion v‖ = ‖v‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
    intro i
    fin_cases i
    · change |(0 : ℝ)| ≤ ‖v‖
      simpa only [abs_zero] using norm_nonneg v
    · exact norm_le_pi_norm v 0
    · exact norm_le_pi_norm v 1
    · exact norm_le_pi_norm v 2
  · have heq : restartCompactCenterProjection (restartCenterInclusion v) = v := by
      ext i
      fin_cases i <;> rfl
    simpa only [heq] using restartCompactCenterProjection_norm_le (restartCenterInclusion v)

theorem hasFDerivAt_restartMixedSection (h : ℝ) (Z : RestartCenterState) :
    HasFDerivAt (restartMixedSection h) restartCenterInclusion Z := by
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasFDerivAt_const _ _
  · exact hasFDerivAt_apply (𝕜 := ℝ) 0 Z
  · exact hasFDerivAt_apply (𝕜 := ℝ) 1 Z
  · exact hasFDerivAt_apply (𝕜 := ℝ) 2 Z

theorem restartMixedSection_center (h : ℝ) (Z : RestartCenterState) :
    restartCompactCenterProjection (restartMixedSection h Z) = Z := by
  ext i
  fin_cases i <;> rfl

theorem restartMixedChart_section {h : ℝ} (hh : 0 < h) (Z : RestartCenterState) :
    restartMixedChart (restartMixedSection h Z) = restartSectionChart h Z := by
  ext i
  fin_cases i <;> simp [restartMixedChart, restartMixedSection, restartSectionChart,
    restartCompactRoot, restartRadicand, restartExpCoordinates, restartSectionRadicand, Real.exp_log hh]

theorem restartSectionMixedFlow_physical {h : ℝ} (hh : 0 < h) (t : ℝ) (Z : RestartCenterState) :
    restartSectionMixedFlow h t Z =
      restartMixedCoordinates (normalizedMaxCurve (restartSectionChart h Z) 0 t) := by
  rw [restartSectionMixedFlow, restartMixedFlow, restartMixedChart_section hh]

theorem restartSectionMixedFlow_center {h : ℝ} (hh : 0 < h) (t : ℝ) (Z : RestartCenterState) :
    restartCompactCenterProjection (restartSectionMixedFlow h t Z) = restartSectionCenterFlow h t Z := by
  rw [restartSectionMixedFlow_physical hh]
  ext i
  fin_cases i <;> rfl

theorem restartSectionMixedFlow_fderiv_apply {h t : ℝ} {Z : RestartCenterState}
    (H : restartMixedFlowRegular (restartMixedSection h Z, t)) (v : RestartCenterState) :
    fderiv ℝ (restartSectionMixedFlow h t) Z v =
      fderiv ℝ restartMixedFlow (restartMixedSection h Z, t) (restartCenterInclusion v, 0) := by
  have HD := ((contDiffAt_restartMixedFlow_two H).differentiableAt (by norm_num)).hasFDerivAt.comp Z
    ((hasFDerivAt_restartMixedSection h Z).prodMk (hasFDerivAt_const t Z))
  change HasFDerivAt (restartSectionMixedFlow h t) _ Z at HD
  rw [HD.fderiv]
  rfl

theorem restartSectionMixedFlow_derivative_bound {h t C : ℝ} {Z : RestartCenterState}
    (H : ContDiffAt ℝ 2 restartMixedFlow (restartMixedSection h Z, t))
    (hC : 0 ≤ C)
    (HD : ‖fderiv ℝ (fun y => restartMixedFlow (y, t)) (restartMixedSection h Z)‖ ≤ C) :
    DifferentiableAt ℝ (restartSectionMixedFlow h t) Z ∧
      ‖fderiv ℝ (restartSectionMixedFlow h t) Z‖ ≤ C := by
  have HF := (H.comp (restartMixedSection h Z) (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by norm_num)
  have HC := HF.hasFDerivAt.comp Z (hasFDerivAt_restartMixedSection h Z)
  change HasFDerivAt (restartSectionMixedFlow h t) _ Z at HC
  refine ⟨HC.differentiableAt, ?_⟩
  rw [HC.fderiv]
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro v
  exact ((fderiv ℝ (fun y => restartMixedFlow (y, t)) (restartMixedSection h Z)).le_opNorm _).trans
    (by
      change ‖fderiv ℝ (fun y => restartMixedFlow (y, t)) (restartMixedSection h Z)‖ *
        ‖restartCenterInclusion v‖ ≤ C * ‖v‖
      rw [restartCenterInclusion_norm]
      exact mul_le_mul_of_nonneg_right HD (norm_nonneg v))

/-- The actual fixed-section flow has uniformly bounded ordinary derivatives and finite differences. -/
theorem exists_restartSectionMixedFlow_derivative :
    ∃ C ≥ (32 : ℝ), ∀ (h b T : ℝ),
      0 < h → C * h ≤ 1 / 4 → (0 < b ∧ b ≤ 1 / 16) → 0 ≤ T → C * b * T ≤ 1 / 8 →
      ∀ t ∈ Icc (0 : ℝ) T,
        (∀ Z : RestartCenterState, ‖Z‖ ≤ b / 2 →
          DifferentiableAt ℝ (restartSectionMixedFlow h t) Z ∧
          ‖fderiv ℝ (restartSectionMixedFlow h t) Z‖ ≤ Real.exp (1 / 4)) ∧
        (∀ Z W : RestartCenterState, ‖Z‖ ≤ b / 2 → ‖W‖ ≤ b / 2 →
          ‖restartSectionMixedFlow h t Z - restartSectionMixedFlow h t W‖ ≤ Real.exp (1 / 4) * ‖Z - W‖) := by
  obtain ⟨C, hC, HC⟩ := exists_restartMixedFlow_fastLayer_derivative
  refine ⟨C, hC, ?_⟩
  intro h b T hh hCh hb hT hCb t ht
  have HD (Z : RestartCenterState) (hZ : ‖Z‖ ≤ b / 2) :
      DifferentiableAt ℝ (restartSectionMixedFlow h t) Z ∧
        ‖fderiv ℝ (restartSectionMixedFlow h t) Z‖ ≤ Real.exp (1 / 4) := by
    have H := HC h b T (restartMixedSection h Z) hh hCh hb hT hCb
      (by change Real.exp (Real.log h) ≤ h; rw [Real.exp_log hh])
      (by rwa [restartMixedSection_center]) t ht
    exact restartSectionMixedFlow_derivative_bound H.1 (Real.exp_pos _).le H.2.1
  refine ⟨HD, ?_⟩
  intro Z W hZ hW
  let S := Metric.closedBall (0 : RestartCenterState) (b / 2)
  exact Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun Y (hY : Y ∈ S) => (HD Y (by simpa [S] using hY)).1)
    (fun Y (hY : Y ∈ S) => (HD Y (by simpa [S] using hY)).2)
    (convex_closedBall (0 : RestartCenterState) (b / 2))
    (by simpa [S] using hW) (by simpa [S] using hZ)

end BianchiIX
