import BianchiIX.Dynamics.EntrancePhaseFeedbackBudget

noncomputable section

namespace BianchiIX

open Set MeasureTheory

/-- The initial strong and weak columns retain uv and uvw + theta v^2 w^2 separately. -/
theorem exists_scaled_entrance_phase_wall_budgets :
    ∃ C > (0 : ℝ), ∀ (Y : ℝ → ProjectiveState) (a : ℝ → ℝ) (s t k θ : ℝ),
      7 / 4 ≤ k → s ≤ t →
      (∀ r ∈ Icc s t, HasDerivAt Y (a r • projectiveField (Y r)) r) →
      ContinuousOn a (Icc s t) → (∀ r ∈ Icc s t, 0 ≤ a r) →
      (∀ r ∈ Icc s t, entranceRegion k (Y r)) → (∀ r ∈ Icc s t, 0 < Y r 2) →
      (θ = 1 ∨ (θ = 1 / k ^ 2 ∧ k * (Y s 1 + Y s 3) ^ 2 ≤ 1)) →
      (∫ r in s..t, |entranceRadialVariationCoefficients (Y r) 1| * (a r * entranceClockRate (Y r))) ≤
        C * (Y s 1 * Y s 2) / k ∧
      (∫ r in s..t, |entranceRadialVariationCoefficients (Y r) 2| * (a r * entranceClockRate (Y r))) ≤
        C * (Y s 1 * Y s 2 * Y s 3 + θ * (Y s 2 * Y s 3) ^ 2) / k := by
  obtain ⟨K, hK, HK⟩ := exists_entranceRadialVariationCoefficients_weighted_bounds
  refine ⟨3 * K, by positivity, ?_⟩
  intro Y a s t k θ hk hst hY hac ha hy hv hθ
  let q := fun r => a r * entranceClockRate (Y r)
  let P := fun r => Y r 1 * Y r 2 * q r
  let S := fun r => (Y r 2 * Y r 3) ^ 2 * q r
  have hs : s ∈ Icc s t := ⟨le_rfl, hst⟩
  have hk0 : 0 < k := by linarith
  have hθ0 : 0 ≤ θ := by rcases hθ with rfl | ⟨rfl, _⟩ <;> positivity
  have hw0 := (hy s hs).2.2.2.2.1
  have hcoord (i : Fin 4) := (continuous_apply i).comp_continuousOn (HasDerivAt.continuousOn hY)
  have hqc : ContinuousOn q (Icc s t) := hac.mul
    (continuous_entranceClockRate.comp_continuousOn (HasDerivAt.continuousOn hY))
  have hq (r : ℝ) (hr : r ∈ Icc s t) : 0 ≤ q r :=
    mul_nonneg (ha r hr) (entranceRegion_clock_pos hk (hy r hr)).le
  have hP : ContinuousOn P (Icc s t) := ((hcoord 1).mul (hcoord 2)).mul hqc
  have hS : ContinuousOn S (Icc s t) := (((hcoord 2).mul (hcoord 3)).pow 2).mul hqc
  have hcoeff : ContinuousOn (fun r => entranceRadialVariationCoefficients (Y r)) (Icc s t) := by
    intro r hr
    exact ((continuousAt_entranceRadialVariationCoefficients hk (hy r hr) (hv r hr)).comp
      (hY r hr).continuousAt).continuousWithinAt
  have hc (i : Fin 3) : ContinuousOn (fun r => |entranceRadialVariationCoefficients (Y r) i| * q r) (Icc s t) :=
    ((continuous_apply i).comp_continuousOn hcoeff).abs.mul hqc
  have hW := (scaled_entrance_wall_budgets hk hst hY hac ha hy hv).1
  have hbounds (r : ℝ) (hr : r ∈ Icc s t) :
      |entranceRadialVariationCoefficients (Y r) 1| * q r ≤ K * P r ∧
      |entranceRadialVariationCoefficients (Y r) 2| * q r ≤
        (K * Y s 3) * P r + (K * θ / k ^ 2) * S r := by
    have hθr : θ = 1 ∨ (θ = 1 / k ^ 2 ∧ k * (Y r 1 + Y r 3) ^ 2 ≤ 1) := by
      rcases hθ with h | ⟨h, hb⟩
      · exact Or.inl h
      · refine Or.inr ⟨h, ?_⟩
        have H := (sq_le_sq₀ (add_nonneg (hy r hr).2.2.1.1 (hy r hr).2.2.2.2.1)
          (add_nonneg (hy s hs).2.2.1.1 hw0)).mpr (add_le_add (hW r hr).1 (hW r hr).2)
        exact (mul_le_mul_of_nonneg_left H hk0.le).trans hb
    obtain ⟨_, hx, hw⟩ := HK k θ (Y r) hk (hy r hr) (hv r hr) hθr
    constructor
    · exact (mul_le_mul_of_nonneg_right hx (hq r hr)).trans_eq (by dsimp [P]; ring)
    · have HP := mul_le_mul_of_nonneg_left (hW r hr).2
        (mul_nonneg (hy r hr).2.2.1.1 (hy r hr).2.2.2.1.1)
      have H := mul_le_mul_of_nonneg_right
        (hw.trans (mul_le_mul_of_nonneg_left (add_le_add HP le_rfl) hK.le)) (hq r hr)
      exact H.trans_eq (by dsimp [P, S]; ring)
  obtain ⟨hP0, _, hS0, _⟩ := scaled_entrance_product_moments hk hst hY hac ha hy hv
  constructor
  · have H := intervalIntegral.integral_mono_on (μ := volume) hst ((hc 1).intervalIntegrable_of_Icc hst)
      ((hP.const_mul K).intervalIntegrable_of_Icc hst) (fun r hr => (hbounds r hr).1)
    rw [intervalIntegral.integral_const_mul] at H
    exact H.trans ((mul_le_mul_of_nonneg_left hP0 hK.le).trans_eq (by ring))
  · have H := intervalIntegral.integral_mono_on (μ := volume) hst ((hc 2).intervalIntegrable_of_Icc hst)
      (((hP.const_mul (K * Y s 3)).add (hS.const_mul (K * θ / k ^ 2))).intervalIntegrable_of_Icc hst)
      (fun r hr => (hbounds r hr).2)
    simp only [Pi.add_apply] at H
    rw [intervalIntegral.integral_add ((hP.const_mul (K * Y s 3)).intervalIntegrable_of_Icc hst)
      ((hS.const_mul (K * θ / k ^ 2)).intervalIntegrable_of_Icc hst),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at H
    have HI := add_le_add (mul_le_mul_of_nonneg_left hP0 (mul_nonneg hK.le hw0))
      (mul_le_mul_of_nonneg_left hS0 (show 0 ≤ K * θ / k ^ 2 by positivity))
    apply H.trans (HI.trans ?_)
    have HT : θ * (Y s 2 * Y s 3) ^ 2 / 2 ≤ 3 * (θ * (Y s 2 * Y s 3) ^ 2) := by
      nlinarith only [mul_nonneg hθ0 (sq_nonneg (Y s 2 * Y s 3))]
    have H' := mul_le_mul_of_nonneg_left HT (show 0 ≤ K / k by positivity)
    have heq : K * Y s 3 * (3 * (Y s 1 * Y s 2) / k) + K * θ / k ^ 2 * (k * (Y s 2 * Y s 3) ^ 2 / 2) =
        K / k * (3 * (Y s 1 * Y s 2 * Y s 3) + θ * (Y s 2 * Y s 3) ^ 2 / 2) := by field_simp
    rw [heq]
    calc
      _ = K / k * (3 * (Y s 1 * Y s 2 * Y s 3)) + K / k * (θ * (Y s 2 * Y s 3) ^ 2 / 2) := by ring
      _ ≤ K / k * (3 * (Y s 1 * Y s 2 * Y s 3)) + K / k * (3 * (θ * (Y s 2 * Y s 3) ^ 2)) :=
        add_le_add le_rfl H'
      _ = _ := by ring

end BianchiIX
