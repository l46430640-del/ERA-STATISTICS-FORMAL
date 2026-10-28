import BianchiIX.Dynamics.ShearRestartScaledError

noncomputable section

namespace BianchiIX

open Set

/-- Quadratically small transverse walls and their first responses suffice for the shear phase comparison. -/
theorem exists_shearRestartProjectionError_quadratic :
    ∃ δ > (0 : ℝ), ∃ C ≥ (1 : ℝ), ∀ a ∈ Ioc (0 : ℝ) δ,
      ∀ (p : ℝ → RestartRadialState) (v : RestartRadialState) (t B : ℝ),
        HasDerivAt p v t → 0 ≤ B →
        a / 2 ≤ |(p t).2 0| → |(p t).2 0| ≤ 4 * a → |(p t).2 1| ≤ 4 * a →
        |(p t).1| ≤ a ^ 2 → |(p t).2 2| ≤ a ^ 2 →
        |v.2 0| ≤ B → |v.2 1| ≤ B → |v.1| ≤ B * a → |v.2 2| ≤ B * a →
          ContDiffAt ℝ 2 restartProjectionError (p t) ∧
          DifferentiableAt ℝ (fun r => restartProjectionError (p r)) t ∧
          |restartProjectionError (p t)| ≤ C * a ^ 2 ∧
          |deriv (fun r => restartProjectionError (p r)) t| ≤ 2 * C * B * a := by
  obtain ⟨δ, hδ, C, hC, HC⟩ := exists_shearRestartProjectionScaledError_bounds
    (c := 1 / 2) (M := 4) (by norm_num)
  refine ⟨δ, hδ, C, hC, ?_⟩
  intro a ha p v t B Hp hB hslo hshi hx hn hy hvs hvx hvn hvy
  have ha0 := ha.1.le
  let u := (restartProjectionParametersAt a (p t)).1
  let X := (restartProjectionParametersAt a (p t)).2
  let du := (restartProjectionParameterTangent a v).1
  let dX := (restartProjectionParameterTangent a v).2
  have hu : ‖u‖ ≤ a := by
    apply (pi_norm_le_iff_of_nonneg ha.1.le).mpr
    intro i
    fin_cases i
    · exact le_of_eq (abs_of_pos ha.1)
    · change |(p t).1 / a| ≤ a
      rw [abs_div, abs_of_pos ha.1]
      exact (div_le_iff₀ ha.1).mpr (by nlinarith only [hn])
    · change |(p t).2 2 / a| ≤ a
      rw [abs_div, abs_of_pos ha.1]
      exact (div_le_iff₀ ha.1).mpr (by nlinarith only [hy])
  have hXlo : 1 / 2 ≤ |X 0| := by
    change 1 / 2 ≤ |(p t).2 0 / a|
    rw [abs_div, abs_of_pos ha.1]
    exact (le_div_iff₀ ha.1).mpr (by linarith only [hslo])
  have hXhi : |X 0| ≤ 4 := by
    change |(p t).2 0 / a| ≤ 4
    rw [abs_div, abs_of_pos ha.1]
    exact (div_le_iff₀ ha.1).mpr hshi
  have hXwall : |X 1| ≤ 4 := by
    change |(p t).2 1 / a| ≤ 4
    rw [abs_div, abs_of_pos ha.1]
    exact (div_le_iff₀ ha.1).mpr hx
  have H := HC X hXlo hXhi hXwall u (hu.trans ha.2)
  have hdu : ‖du‖ ≤ B := by
    apply (pi_norm_le_iff_of_nonneg hB).mpr
    intro i
    fin_cases i
    · change |(0 : ℝ)| ≤ B
      simpa only [abs_zero] using hB
    · change |v.1 / a| ≤ B
      rw [abs_div, abs_of_pos ha.1]
      exact (div_le_iff₀ ha.1).mpr hvn
    · change |v.2 2 / a| ≤ B
      rw [abs_div, abs_of_pos ha.1]
      exact (div_le_iff₀ ha.1).mpr hvy
  have hdX : ‖dX‖ ≤ B / a := by
    apply (pi_norm_le_iff_of_nonneg (div_nonneg hB ha.1.le)).mpr
    intro i
    fin_cases i
    · change |v.2 0 / a| ≤ B / a
      rw [abs_div, abs_of_pos ha.1]
      exact div_le_div_of_nonneg_right hvs ha.1.le
    · change |v.2 1 / a| ≤ B / a
      rw [abs_div, abs_of_pos ha.1]
      exact div_le_div_of_nonneg_right hvx ha.1.le
  have HD := hasDerivAt_restartProjectionError ha.1 Hp (H.1.differentiableAt (by norm_num))
  have Hdir := restartProjectionScaledError_direction_bound (du := du) (dX := dX) H.2.2.1 H.2.2.2
  have hC0 : 0 ≤ C := by linarith only [hC]
  refine ⟨contDiffAt_restartProjectionError ha.1 H.1, HD.differentiableAt, ?_, ?_⟩
  · rw [restartProjectionError_rescaled ha.1, abs_mul, abs_of_pos ha.1]
    calc
      _ ≤ a * (C * ‖u‖) := mul_le_mul_of_nonneg_left H.2.1 ha.1.le
      _ ≤ a * (C * a) := by gcongr
      _ = C * a ^ 2 := by ring
  · rw [HD.deriv, abs_mul, abs_of_pos ha.1]
    calc
      _ ≤ a * (C * ‖du‖ + C * ‖u‖ * ‖dX‖) := mul_le_mul_of_nonneg_left Hdir ha.1.le
      _ ≤ a * (C * B + C * a * (B / a)) := by gcongr
      _ = 2 * C * B * a := by field_simp [ha.1.ne']; ring

end BianchiIX
