import BianchiIX.Dynamics.RestartRadialErrorDerivative

noncomputable section

namespace BianchiIX

open Set

/-- The three derivative errors in (E.11), at the actual fixed logarithmic cutoff. -/
theorem exists_restartSection_radial_cutoff_derivative :
    ∃ C ≥ (32 : ℝ), ∀ (c₀ C₀ : ℝ), 0 < c₀ → 0 < C₀ → ∃ K : ℝ, 0 < K ∧
      ∀ (h ρ q : ℝ), 0 < h → C * h ≤ 1 / 4 → (0 < ρ ∧ ρ ≤ 1) → 0 ≤ q →
        2 * C₀ * ρ ≤ 1 / 16 → C * (2 * C₀ * ρ) * (q / 2 * Real.log (1 / ρ)) ≤ 1 / 8 →
        ∀ Z : RestartCenterState, ‖Z‖ ≤ C₀ * ρ → c₀ * ρ ≤ restartRadialNorm Z →
          let T := q / 2 * Real.log (1 / ρ)
          DifferentiableAt ℝ (restartSectionRadialError h T) Z ∧
          ‖fderiv ℝ (restartSectionRadialError h T) Z‖ ≤ K * (h * ρ + ρ ^ 2 * T + h * ρ ^ q) := by
  obtain ⟨C, hC, HC⟩ := exists_restartSectionRadialError_derivative
  refine ⟨C, hC, ?_⟩
  intro c₀ C₀ hc₀ hC₀
  obtain ⟨L, hL, HL⟩ := HC (c₀ / (2 * C₀)) (by positivity)
  let M := 2 * C₀ + 4 * C₀ ^ 2 + 1
  let K := L * M
  have hK : 0 < K := by dsimp only [K, M]; positivity
  refine ⟨K, hK, ?_⟩
  intro h ρ q hh hCh hρ hq hb hCb Z hZ hlower
  have hρ0 := hρ.1
  let b := 2 * C₀ * ρ
  let T := q / 2 * Real.log (1 / ρ)
  have hb0 : 0 < b := by dsimp only [b]; positivity
  have hT : 0 ≤ T := mul_nonneg (div_nonneg hq (by norm_num))
    (Real.log_nonneg ((le_div_iff₀ hρ.1).mpr (by linarith only [hρ.2])))
  have hZb : ‖Z‖ ≤ b / 2 := by dsimp only [b]; linarith only [hZ]
  have Hlower : c₀ / (2 * C₀) * b ≤ restartRadialNorm Z := by
    have Heq : c₀ / (2 * C₀) * b = c₀ * ρ := by dsimp only [b]; field_simp
    rwa [Heq]
  have H := HL h b T Z hh hCh ⟨hb0, hb⟩ hT hCb hZb Hlower T ⟨hT, le_rfl⟩
  have he : Real.exp (-2 * T) = ρ ^ q := by
    rw [Real.rpow_def_of_pos hρ.1]
    congr 1
    dsimp only [T]
    rw [one_div, Real.log_inv]
    ring
  refine ⟨H.1, H.2.trans ?_⟩
  rw [he]
  have H1 : L * (2 * C₀) ≤ K := by dsimp only [K, M]; nlinarith only [mul_nonneg hL.le (sq_nonneg C₀), hL]
  have H2 : L * (4 * C₀ ^ 2) ≤ K := by dsimp only [K, M]; nlinarith only [mul_pos hL hC₀, hL]
  have H3 : L ≤ K := by dsimp only [K, M]; nlinarith only [mul_pos hL hC₀, mul_nonneg hL.le (sq_nonneg C₀)]
  calc
    _ = (L * (2 * C₀)) * (h * ρ) + (L * (4 * C₀ ^ 2)) * (ρ ^ 2 * T) + L * (h * ρ ^ q) := by
      dsimp only [b]
      ring
    _ ≤ K * (h * ρ) + K * (ρ ^ 2 * T) + K * (h * ρ ^ q) :=
      add_le_add (add_le_add
        (mul_le_mul_of_nonneg_right H1 (by positivity))
        (mul_le_mul_of_nonneg_right H2 (by positivity)))
        (mul_le_mul_of_nonneg_right H3 (by positivity))
    _ = _ := by ring

end BianchiIX
