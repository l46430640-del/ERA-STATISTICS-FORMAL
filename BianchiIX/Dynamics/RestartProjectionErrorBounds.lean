import BianchiIX.Dynamics.RestartProjectionError

noncomputable section

namespace BianchiIX

open Set

/-- The value and ordinary directional bounds in (E.15), uniform in the two small wall amplitudes. -/
theorem exists_restartProjectionError_bounds {c M : ℝ} (hc : 0 < c) :
    ∃ δ > (0 : ℝ), ∃ C ≥ (1 : ℝ), ∀ r : ℝ, 0 < r → r ≤ δ →
      ∀ p : RestartRadialState, |p.2 0| ≤ M * r → c * r ≤ p.2 1 → p.2 1 ≤ M * r →
        |p.1| ≤ δ * r → |p.2 2| ≤ δ * r →
        ContDiffAt ℝ 2 restartProjectionError p ∧
        |restartProjectionError p| ≤ C * (r ^ 2 + |p.1| + |p.2 2|) ∧
        ∀ D : ℝ, 0 ≤ D → ∀ v : RestartRadialState,
          |v.2 0| ≤ D → |v.2 1| ≤ D →
          |v.1| ≤ D * |p.1| / r → |v.2 2| ≤ D * |p.2 2| / r →
            |fderiv ℝ restartProjectionError p v| ≤
              2 * C * D * (r + |p.1| / r + |p.2 2| / r) := by
  obtain ⟨δ, hδ, C, hC, HC⟩ := exists_restartProjectionScaledError_bounds (M := M) hc
  refine ⟨δ, hδ, C, hC, ?_⟩
  intro r hr hrδ p hs ha₀ ha₁ hn hb
  let u := (restartProjectionParametersAt r p).1
  let X := (restartProjectionParametersAt r p).2
  have hC₀ : 0 ≤ C := le_trans (by norm_num : (0 : ℝ) ≤ 1) hC
  have hu : ‖u‖ ≤ δ := by
    apply (pi_norm_le_iff_of_nonneg hδ.le).mpr
    intro i
    fin_cases i
    · change |r| ≤ δ
      rwa [abs_of_pos hr]
    · change |p.1 / r| ≤ δ
      rw [abs_div, abs_of_pos hr]
      exact (div_le_iff₀ hr).mpr hn
    · change |p.2 2 / r| ≤ δ
      rw [abs_div, abs_of_pos hr]
      exact (div_le_iff₀ hr).mpr hb
  have hX₀ : |X 0| ≤ M := by
    change |p.2 0 / r| ≤ M
    rw [abs_div, abs_of_pos hr]
    exact (div_le_iff₀ hr).mpr hs
  have hX₁ : X 1 ∈ Icc c M := ⟨(le_div_iff₀ hr).mpr ha₀, (div_le_iff₀ hr).mpr ha₁⟩
  have H := HC X hX₀ hX₁ u hu
  let a := r + |p.1| / r + |p.2 2| / r
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hua : ‖u‖ ≤ a := by
    apply (pi_norm_le_iff_of_nonneg ha).mpr
    intro i
    fin_cases i
    · change |r| ≤ a
      rw [abs_of_pos hr]
      dsimp only [a]
      linarith only [div_nonneg (abs_nonneg p.1) hr.le, div_nonneg (abs_nonneg (p.2 2)) hr.le]
    · change |p.1 / r| ≤ a
      rw [abs_div, abs_of_pos hr]
      dsimp only [a]
      linarith only [hr, div_nonneg (abs_nonneg (p.2 2)) hr.le]
    · change |p.2 2 / r| ≤ a
      rw [abs_div, abs_of_pos hr]
      dsimp only [a]
      linarith only [hr, div_nonneg (abs_nonneg p.1) hr.le]
  refine ⟨contDiffAt_restartProjectionError hr H.1, ?_, ?_⟩
  · rw [restartProjectionError_rescaled hr, abs_mul, abs_of_pos hr]
    calc
      _ ≤ r * (C * ‖u‖) := mul_le_mul_of_nonneg_left H.2.1 hr.le
      _ ≤ r * (C * a) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hua hC₀) hr.le
      _ = C * (r ^ 2 + |p.1| + |p.2 2|) := by dsimp only [a]; field_simp
  · intro D hD v hvs hva hvn hvb
    let du := (restartProjectionParameterTangent r v).1
    let dX := (restartProjectionParameterTangent r v).2
    have hdu : ‖du‖ ≤ (|v.1| + |v.2 2|) / r := by
      apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ (|v.1| + |v.2 2|) / r)).mpr
      intro i
      fin_cases i
      · change |(0 : ℝ)| ≤ _
        rw [abs_zero]
        positivity
      · change |v.1 / r| ≤ _
        rw [abs_div, abs_of_pos hr]
        exact div_le_div_of_nonneg_right (le_add_of_nonneg_right (abs_nonneg _)) hr.le
      · change |v.2 2 / r| ≤ _
        rw [abs_div, abs_of_pos hr]
        exact div_le_div_of_nonneg_right (le_add_of_nonneg_left (abs_nonneg _)) hr.le
    have hdX : ‖dX‖ ≤ D / r := by
      apply (pi_norm_le_iff_of_nonneg (div_nonneg hD hr.le)).mpr
      intro i
      fin_cases i
      · change |v.2 0 / r| ≤ _
        rw [abs_div, abs_of_pos hr]
        exact div_le_div_of_nonneg_right hvs hr.le
      · change |v.2 1 / r| ≤ _
        rw [abs_div, abs_of_pos hr]
        exact div_le_div_of_nonneg_right hva hr.le
    have Hv : |v.1| + |v.2 2| ≤ D * a := by
      dsimp only [a]
      have Hsmall := add_le_add hvn hvb
      simp only [mul_div_assoc] at Hsmall
      nlinarith only [Hsmall, mul_nonneg hD hr.le]
    have HB := restartProjectionScaledError_direction_bound (du := du) (dX := dX) H.2.2.1 H.2.2.2
    rw [fderiv_restartProjectionError hr H.1 v, abs_mul, abs_of_pos hr]
    calc
      _ ≤ r * (C * ‖du‖ + C * ‖u‖ * ‖dX‖) := mul_le_mul_of_nonneg_left HB hr.le
      _ ≤ r * (C * ((|v.1| + |v.2 2|) / r) + C * a * (D / r)) := by gcongr
      _ = C * (|v.1| + |v.2 2|) + C * a * D := by field_simp
      _ ≤ C * (D * a) + C * a * D := add_le_add (mul_le_mul_of_nonneg_left Hv hC₀) le_rfl
      _ = 2 * C * D * (r + |p.1| / r + |p.2 2| / r) := by dsimp only [a]; ring

/-- The combined value and derivative estimate holds along ordinary differentiable curves. -/
theorem exists_restartProjectionError_curve_bound {c M : ℝ} (hc : 0 < c) :
    ∃ δ > (0 : ℝ), ∃ C ≥ (1 : ℝ), ∀ r : ℝ, 0 < r → r ≤ δ →
      ∀ (p : ℝ → RestartRadialState) (v : RestartRadialState) (t D : ℝ),
        HasDerivAt p v t → 0 ≤ D →
        |(p t).2 0| ≤ M * r → c * r ≤ (p t).2 1 → (p t).2 1 ≤ M * r →
        |(p t).1| ≤ δ * r → |(p t).2 2| ≤ δ * r →
        |v.2 0| ≤ D → |v.2 1| ≤ D →
        |v.1| ≤ D * |(p t).1| / r → |v.2 2| ≤ D * |(p t).2 2| / r →
          DifferentiableAt ℝ (fun s => restartProjectionError (p s)) t ∧
          |restartProjectionError (p t)| + r * |deriv (fun s => restartProjectionError (p s)) t| ≤
            C * (1 + 2 * D) * (r ^ 2 + |(p t).1| + |(p t).2 2|) := by
  obtain ⟨δ, hδ, C, hC, HC⟩ := exists_restartProjectionError_bounds (M := M) hc
  refine ⟨δ, hδ, C, hC, ?_⟩
  intro r hr hrδ p v t D Hp hD hs ha₀ ha₁ hn hb hvs hva hvn hvb
  have H := HC r hr hrδ (p t) hs ha₀ ha₁ hn hb
  have HD := (H.1.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t Hp
  refine ⟨HD.differentiableAt, ?_⟩
  change |restartProjectionError (p t)| + r * |deriv (restartProjectionError ∘ p) t| ≤ _
  rw [HD.deriv]
  have HB := mul_le_mul_of_nonneg_left (H.2.2 D hD v hvs hva hvn hvb) hr.le
  have heq : r * (2 * C * D * (r + |(p t).1| / r + |(p t).2 2| / r)) =
      2 * C * D * (r ^ 2 + |(p t).1| + |(p t).2 2|) := by field_simp
  rw [heq] at HB
  calc
    _ ≤ C * (r ^ 2 + |(p t).1| + |(p t).2 2|) +
        2 * C * D * (r ^ 2 + |(p t).1| + |(p t).2 2|) := add_le_add H.2.1 HB
    _ = _ := by ring

end BianchiIX
