import BianchiIX.Dynamics.EntranceProductMoments
import BianchiIX.Dynamics.EntranceDriftRefinedEstimates
import BianchiIX.Dynamics.EntranceWallBudgets
import BianchiIX.Analysis.CoreIntegrals

noncomputable section

namespace BianchiIX

open Set MeasureTheory

theorem exists_entranceRadialDrift_weighted_bound :
    ∃ C > (0 : ℝ), ∀ (k θ : ℝ) (y : ProjectiveState),
      7 / 4 ≤ k → entranceRegion k y → 0 < y 2 →
      (θ = 1 ∨ (θ = 1 / k ^ 2 ∧ k * (y 1 + y 3) ^ 2 ≤ 1)) →
      |entranceRadialDrift y| ≤ C * (y 1 * y 2 + θ * (y 2 * y 3) ^ 2 / k ^ 2) := by
  obtain ⟨A, hA, HA⟩ := exists_entranceRadialDrift_basic_bounds
  obtain ⟨B, hB, HB⟩ := exists_entranceRadialDrift_refined_bounds
  refine ⟨A + B, add_pos hA hB, ?_⟩
  intro k θ y hk hy hv hθ
  obtain ⟨Ψ, HΨ⟩ := exists_entranceRegion_radial_inverse hk hy hv
  have hk0 : 0 < k := by linarith
  rcases hθ with rfl | ⟨rfl, hs⟩
  · simp only [one_mul, mul_pow]
    exact (HA k y hk hy hv Ψ HΨ).1.trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB.le) (by positivity [hy.2.2.1.1]))
  · have heq : (1 / k ^ 2) * (y 2 * y 3) ^ 2 / k ^ 2 = y 2 ^ 2 * y 3 ^ 2 / k ^ 4 := by
      field_simp
    rw [heq]
    exact (HB k y hk hy hs hv Ψ HΨ).1.trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA.le) (by positivity [hy.2.2.1.1]))

/-- Integrating the exact radial rate retains the strong and weak initial products. -/
theorem exists_scaled_entranceStableRadius_drift :
    ∃ C > (0 : ℝ), ∀ (Y : ℝ → ProjectiveState) (a : ℝ → ℝ) (s t k θ : ℝ),
      7 / 4 ≤ k → s ≤ t →
      (∀ r ∈ Icc s t, HasDerivAt Y (a r • projectiveField (Y r)) r) →
      ContinuousOn a (Icc s t) → (∀ r ∈ Icc s t, 0 ≤ a r) →
      (∀ r ∈ Icc s t, entranceRegion k (Y r)) → (∀ r ∈ Icc s t, 0 < Y r 2) →
      (θ = 1 ∨ (θ = 1 / k ^ 2 ∧ k * (Y s 1 + Y s 3) ^ 2 ≤ 1)) →
      |entranceStableRadius (Y t) - entranceStableRadius (Y s)| ≤
        C * (Y s 1 * Y s 2 + θ * (Y s 2 * Y s 3) ^ 2) / k := by
  obtain ⟨K, hK, HK⟩ := exists_entranceRadialDrift_weighted_bound
  refine ⟨3 * K, by positivity, ?_⟩
  intro Y a s t k θ hk hst hY hac ha hy hv hθ
  let q := fun r => a r * entranceClockRate (Y r)
  let P := fun r => Y r 1 * Y r 2 * q r
  let S := fun r => (Y r 2 * Y r 3) ^ 2 * q r
  let B := fun r => K * P r + (K * θ / k ^ 2) * S r
  have hk0 : 0 < k := by linarith
  have hs : s ∈ Icc s t := ⟨le_rfl, hst⟩
  have hθ0 : 0 ≤ θ := by rcases hθ with rfl | ⟨rfl, _⟩ <;> positivity
  have hcoord (i : Fin 4) := (continuous_apply i).comp_continuousOn (HasDerivAt.continuousOn hY)
  have hqc : ContinuousOn q (Icc s t) := hac.mul
    (continuous_entranceClockRate.comp_continuousOn (HasDerivAt.continuousOn hY))
  have hq (r : ℝ) (hr : r ∈ Icc s t) : 0 ≤ q r :=
    mul_nonneg (ha r hr) (entranceRegion_clock_pos hk (hy r hr)).le
  have hP : ContinuousOn P (Icc s t) := ((hcoord 1).mul (hcoord 2)).mul hqc
  have hS : ContinuousOn S (Icc s t) := (((hcoord 2).mul (hcoord 3)).pow 2).mul hqc
  have hB : ContinuousOn B (Icc s t) := (hP.const_mul K).add (hS.const_mul _)
  have hW := (scaled_entrance_wall_budgets hk hst hY hac ha hy hv).1
  have hd (r : ℝ) (hr : r ∈ Icc s t) :
      HasDerivAt (fun z => entranceStableRadius (Y z)) (q r * entranceRadialDrift (Y r)) r := by
    have hm : 2 ≤ Y r 0 := by linarith [(entranceRegion_phase hk (hy r hr)).1]
    have hu : |Y r 1| < 1 / 200 := by
      rw [abs_of_nonneg (hy r hr).2.2.1.1]
      linarith [(hy r hr).2.2.1.2]
    have hw : |Y r 3| < 1 / 200 := by
      rw [abs_of_nonneg (hy r hr).2.2.2.2.1]
      linarith [(hy r hr).2.2.2.2.2]
    exact hasDerivAt_entranceStableRadius_scaled (hY r hr) hm hu hw (hv r hr)
      (entranceRegion_clock_pos hk (hy r hr)).ne'
  have hbound (r : ℝ) (hr : r ∈ Icc s t) : |q r * entranceRadialDrift (Y r)| ≤ B r := by
    have hθr : θ = 1 ∨ (θ = 1 / k ^ 2 ∧ k * (Y r 1 + Y r 3) ^ 2 ≤ 1) := by
      rcases hθ with h | ⟨h, hb⟩
      · exact Or.inl h
      · refine Or.inr ⟨h, ?_⟩
        have H := (sq_le_sq₀ (add_nonneg (hy r hr).2.2.1.1 (hy r hr).2.2.2.2.1)
          (add_nonneg (hy s hs).2.2.1.1 (hy s hs).2.2.2.2.1)).mpr
          (add_le_add (hW r hr).1 (hW r hr).2)
        exact (mul_le_mul_of_nonneg_left H hk0.le).trans hb
    rw [abs_mul, abs_of_nonneg (hq r hr)]
    exact (mul_le_mul_of_nonneg_left (HK k θ (Y r) hk (hy r hr) (hv r hr) hθr) (hq r hr)).trans_eq
      (by dsimp [B, P, S]; ring)
  have HI := abs_sub_le_integral_bound hst hd hB hbound
  change |entranceStableRadius (Y t) - entranceStableRadius (Y s)| ≤
    ∫ r in s..t, K * P r + (K * θ / k ^ 2) * S r at HI
  rw [intervalIntegral.integral_add ((hP.const_mul K).intervalIntegrable_of_Icc hst)
    ((hS.const_mul _).intervalIntegrable_of_Icc hst),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at HI
  obtain ⟨HP, _, HS, _⟩ := scaled_entrance_product_moments hk hst hY hac ha hy hv
  apply HI.trans ((add_le_add (mul_le_mul_of_nonneg_left HP hK.le)
    (mul_le_mul_of_nonneg_left HS (show 0 ≤ K * θ / k ^ 2 by positivity))).trans ?_)
  have Hweak : θ * (Y s 2 * Y s 3) ^ 2 / 2 ≤ 3 * (θ * (Y s 2 * Y s 3) ^ 2) := by
    nlinarith only [mul_nonneg hθ0 (sq_nonneg (Y s 2 * Y s 3))]
  have H := mul_le_mul_of_nonneg_left (add_le_add_left Hweak (3 * (Y s 1 * Y s 2)))
    (show 0 ≤ K / k by positivity)
  convert! H using 1 <;> field_simp <;> ring

end BianchiIX
