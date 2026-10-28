import BianchiIX.Dynamics.RestartRadiusTailDerivative
import BianchiIX.Dynamics.RestartRadiusDerivativeError
import BianchiIX.Dynamics.RestartRadialCutoff

noncomputable section

namespace BianchiIX

open Set

def restartSectionRadialError (h t : ℝ) (Z : RestartCenterState) : ℝ :=
  restartRadialPhase (restartSectionCenterFlow h t Z) - restartReferenceRadialPhase h Z

theorem restartSectionRadialError_eq (h t : ℝ) (Z : RestartCenterState) :
    restartSectionRadialError h t Z =
      (restartRadialNorm (restartSectionCenterFlow h t Z) - restartSectionRadius h 0 Z) / Real.sqrt 3 := by
  dsimp only [restartSectionRadialError, restartRadialPhase, restartReferenceRadialPhase, restartSectionRadius]
  rw [restartSectionQuadratic_initial]
  ring

theorem restartSectionRadialError_derivative_norm_le {h t : ℝ} {Z : RestartCenterState}
    (HD : DifferentiableAt ℝ
      (fun W => restartRadialNorm (restartSectionCenterFlow h t W) - restartSectionRadius h 0 W) Z) :
    DifferentiableAt ℝ (restartSectionRadialError h t) Z ∧
      ‖fderiv ℝ (restartSectionRadialError h t) Z‖ ≤
        ‖fderiv ℝ (fun W => restartRadialNorm (restartSectionCenterFlow h t W) - restartSectionRadius h 0 W) Z‖ := by
  have H : HasFDerivAt (restartSectionRadialError h t)
      ((1 / Real.sqrt 3) • fderiv ℝ
        (fun W => restartRadialNorm (restartSectionCenterFlow h t W) - restartSectionRadius h 0 W) Z) Z := by
    convert! HD.hasFDerivAt.const_mul (1 / Real.sqrt (3 : ℝ)) using 1
    ext W
    rw [restartSectionRadialError_eq]
    ring
  have hsqrt : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt1 : 1 ≤ Real.sqrt (3 : ℝ) := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), hsqrt]
  have hcoef : (1 : ℝ) / Real.sqrt 3 ≤ 1 := (div_le_iff₀ hsqrt).mpr (by simpa only [one_mul] using hsqrt1)
  refine ⟨H.differentiableAt, ?_⟩
  rw [H.fderiv, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / Real.sqrt (3 : ℝ))]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hcoef (norm_nonneg
    (fderiv ℝ (fun W => restartRadialNorm (restartSectionCenterFlow h t W) - restartSectionRadius h 0 W) Z))

/-- The integrated drift and endpoint reference error control the full ordinary radial error. -/
theorem exists_restartSectionRadialError_derivative :
    ∃ C ≥ (32 : ℝ), ∀ c : ℝ, 0 < c → ∃ K : ℝ, 0 < K ∧
      ∀ (h b T : ℝ) (Z : RestartCenterState),
        0 < h → C * h ≤ 1 / 4 → (0 < b ∧ b ≤ 1 / 16) → 0 ≤ T → C * b * T ≤ 1 / 8 →
        ‖Z‖ ≤ b / 2 → c * b ≤ restartRadialNorm Z → ∀ t ∈ Icc (0 : ℝ) T,
          DifferentiableAt ℝ (restartSectionRadialError h t) Z ∧
          ‖fderiv ℝ (restartSectionRadialError h t) Z‖ ≤
            K * (h * b + b ^ 2 * t + h * Real.exp (-2 * t)) := by
  obtain ⟨A, hA, HA⟩ := exists_restartSectionRadius_derivative_error
  obtain ⟨B, _, HB⟩ := exists_restartSectionRadiusTail_derivative_bound
  obtain ⟨D, _, HD⟩ := exists_restartSection_fastLayer_control
  let C := max A (max B D)
  have hAC : A ≤ C := le_max_left _ _
  have hBC : B ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hDC : D ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, hA.trans hAC, ?_⟩
  intro c hc
  obtain ⟨K₁, hK₁, HK₁⟩ := HA c hc
  obtain ⟨K₂, hK₂, HK₂⟩ := HB c hc
  let K := max K₁ K₂
  have hK : 0 < K := hK₁.trans_le (le_max_left _ _)
  refine ⟨K, hK, ?_⟩
  intro h b T Z hh hCh hb hT hCb hZ hradial t ht
  have hb0 := hb.1.le
  have Hheight (k : ℝ) (hk : k ≤ C) : k * h ≤ 1 / 4 :=
    (mul_le_mul_of_nonneg_right hk hh.le).trans hCh
  have Htime (k : ℝ) (hk : k ≤ C) : k * b * T ≤ 1 / 8 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hk hb0) hT).trans hCb
  have Hcore := HK₁ h b T Z hh (Hheight A hAC) hb hT (Htime A hAC) hZ hradial t ht
  have Htail := HK₂ h b T Z hh (Hheight B hBC) hb hT (Htime B hBC) hZ hradial t ht
  have Hwall := (HD h b T Z hh (Hheight D hDC) hb hT (Htime D hDC) hZ t ht).2.1
  have Hsub := Hcore.1.hasFDerivAt.sub Htail.1.hasFDerivAt
  have Heq : (fun W => restartRadialNorm (restartSectionCenterFlow h t W) - restartSectionRadius h 0 W) =
      (fun W => restartSectionRadius h t W - restartSectionRadius h 0 W) - restartSectionRadiusTail h t := by
    ext W
    dsimp only [Pi.sub_apply, restartSectionRadiusTail]
    ring
  have Hraw : DifferentiableAt ℝ
      (fun W => restartRadialNorm (restartSectionCenterFlow h t W) - restartSectionRadius h 0 W) Z := by
    rw [Heq]
    exact Hsub.differentiableAt
  have Hnorm := restartSectionRadialError_derivative_norm_le Hraw
  refine ⟨Hnorm.1, Hnorm.2.trans ?_⟩
  rw [Heq, Hsub.fderiv]
  calc
    _ ≤ ‖fderiv ℝ (fun W => restartSectionRadius h t W - restartSectionRadius h 0 W) Z‖ +
        ‖fderiv ℝ (restartSectionRadiusTail h t) Z‖ := norm_sub_le _ _
    _ ≤ K₁ * (h * b + b ^ 2 * t) + K₂ * restartSectionStrongWall h t Z := add_le_add Hcore.2 Htail.2
    _ ≤ K₁ * (h * b + b ^ 2 * t) + K₂ * (h * Real.exp (-2 * t)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left Hwall hK₂.le)
    _ ≤ K * (h * b + b ^ 2 * t) + K * (h * Real.exp (-2 * t)) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity [ht.1]))
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
    _ = _ := by ring

end BianchiIX
