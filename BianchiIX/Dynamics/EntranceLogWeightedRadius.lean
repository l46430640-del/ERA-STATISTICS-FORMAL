import BianchiIX.Dynamics.EntrancePhysicalRadialResponse

noncomputable section

namespace BianchiIX

/-- Small transverse walls absorb a logarithmic loss in the ordinary entrance response. -/
theorem exists_entrance_log_weighted_radius :
    ∃ C > (0 : ℝ), ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧
      ∀ (Y : ℝ → ProjectiveState) (ρ D L : ℝ),
      let y := Y ρ
      let k := coreRadius (y 0) (y 2)
      let κ := fun r => coreRadius (entranceReturnState (Y r) 0) (entranceReturnState (Y r) 2)
      let K := fun r => coreRadius (Y r 0) (Y r 2)
      DifferentiableAt ℝ Y ρ → 0 ≤ D → 1 ≤ L → 8 ≤ k → 1 ≤ y 0 →
      (0 < y 1 ∧ y 1 ≤ ε) → (0 < y 2 ∧ y 2 < 1) → (0 < y 3 ∧ y 3 ≤ ε) →
      L * (y 1 + y 3) ≤ 1 →
      |deriv (fun r => Y r 0) ρ| ≤ D * k ^ 2 →
      (∀ i : Fin 4, i ≠ 0 → |deriv (fun r => Y r i) ρ| ≤ D * L * k * y i) →
      DifferentiableAt ℝ κ ρ ∧ DifferentiableAt ℝ K ρ ∧
      |κ ρ - k| ≤ C / k ∧ |deriv κ ρ - deriv K ρ| ≤ C * D * k := by
  obtain ⟨A, hA, ε, hε, hεsmall, HA⟩ := exists_entrance_physical_curve_bounds
  refine ⟨3 * A, by positivity, ε, hε, hεsmall, ?_⟩
  intro Y ρ D L y k κ K HY hD hL hk hm hu hv hw hsmall hd0 hdwall
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hL0 : 0 ≤ L := by linarith only [hL]
  have Hd0 : |deriv (fun r => Y r 0) ρ| ≤ (D * L) * k ^ 2 := hd0.trans (by
    nlinarith only [mul_le_mul_of_nonneg_left hL (mul_nonneg hD (sq_nonneg k))])
  obtain ⟨Hκ, HK, Hval, Hder⟩ := HA Y ρ (D * L) HY (mul_nonneg hD hL0)
    (by linarith only [hk]) hm hu hv hw Hd0 hdwall
  let b := y 1 + y 3
  have hb0 : 0 ≤ b := add_nonneg hu.1.le hw.1.le
  have hb1 : b ≤ 1 := by
    have H := mul_le_mul_of_nonneg_right hL hb0
    change L * b ≤ 1 at hsmall
    linarith only [H, hsmall]
  have hb2 : b ^ 2 ≤ 1 := by nlinarith only [hb0, hb1]
  have hv2 : (y 2) ^ 2 ≤ 1 := by nlinarith only [hv.1, hv.2]
  have Henergy : y 1 * y 2 + (y 2) ^ 2 * b ^ 2 ≤ b + b ^ 2 := by
    have H0 := mul_le_mul_of_nonneg_left hv.2.le hu.1.le
    have H1 := mul_le_mul_of_nonneg_right hv2 (sq_nonneg b)
    dsimp only [b] at *
    nlinarith only [H0, H1, hw.1]
  have HLb2 : L * b ^ 2 ≤ 1 := by
    have H := mul_le_mul_of_nonneg_right hsmall hb0
    change L * (y 1 + y 3) * b ≤ 1 * b at H
    dsimp only [b] at *
    nlinarith only [H, hb1]
  have HE : L * (y 1 * y 2 + (y 2) ^ 2 * b ^ 2) ≤ 2 := by
    have H := mul_le_mul_of_nonneg_left Henergy hL0
    change L * b ≤ 1 at hsmall
    linarith only [H, hsmall, HLb2]
  refine ⟨Hκ, HK, ?_, ?_⟩
  · apply Hval.trans
    change A * (b ^ 2 + (y 1 * y 2 + (y 2) ^ 2 * b ^ 2)) / k ≤ _
    apply div_le_div_of_nonneg_right _ hk0
    nlinarith only [mul_le_mul_of_nonneg_left Henergy hA.le,
      mul_le_mul_of_nonneg_left hb1 hA.le, mul_le_mul_of_nonneg_left hb2 hA.le]
  · have HB : L * (b ^ 2 + k * (y 1 * y 2 + (y 2) ^ 2 * b ^ 2)) ≤ 3 * k := by
      have H := mul_le_mul_of_nonneg_left HE hk0
      nlinarith only [H, HLb2, hk]
    have H := mul_le_mul_of_nonneg_left HB (mul_nonneg hA.le hD)
    change |deriv κ ρ - deriv K ρ| ≤ A * (D * L) *
      (b ^ 2 + k * (y 1 * y 2 + (y 2) ^ 2 * b ^ 2)) at Hder
    nlinarith only [Hder, H]

end BianchiIX
