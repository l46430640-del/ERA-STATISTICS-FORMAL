import BianchiIX.Dynamics.EntranceProductMoments
import BianchiIX.Dynamics.EntranceRadialVariationBounds
import BianchiIX.Dynamics.EntranceWallBudgets

noncomputable section

namespace BianchiIX

open Set MeasureTheory

def entrancePhaseFeedbackRate (k l : ℝ) (y : ProjectiveState) : ℝ :=
  |entranceRadialVariationCoefficients y 0| +
    l * (|entranceRadialVariationCoefficients y 1| + |entranceRadialVariationCoefficients y 2| / k ^ 2)

theorem entrancePhaseFeedbackRate_nonneg (k : ℝ) {l : ℝ} (hl : 0 ≤ l) (y : ProjectiveState) :
    0 ≤ entrancePhaseFeedbackRate k l y := by
  unfold entrancePhaseFeedbackRate
  positivity

/-- Both terms of (C.31) have a common integral budget, with the weak-column weight retained. -/
theorem exists_scaled_entrance_phase_feedback_budget :
    ∃ C > (0 : ℝ), ∀ (Y : ℝ → ProjectiveState) (a : ℝ → ℝ) (s t k θ : ℝ),
      7 / 4 ≤ k → s ≤ t →
      (∀ r ∈ Icc s t, HasDerivAt Y (a r • projectiveField (Y r)) r) →
      ContinuousOn a (Icc s t) → (∀ r ∈ Icc s t, 0 ≤ a r) →
      (∀ r ∈ Icc s t, entranceRegion k (Y r)) → (∀ r ∈ Icc s t, 0 < Y r 2) →
      (θ = 1 ∨ (θ = 1 / k ^ 2 ∧ k * (Y s 1 + Y s 3) ^ 2 ≤ 1)) →
      (∫ r in s..t, entrancePhaseFeedbackRate k (Real.log (Y r 2) - Real.log (Y s 2)) (Y r) *
        (a r * entranceClockRate (Y r))) ≤
          C * (Y s 1 * Y s 2 + θ * (Y s 2 * Y s 3) ^ 2) / k ^ 2 := by
  obtain ⟨K, hK, HK⟩ := exists_entranceRadialVariationCoefficients_weighted_bounds
  refine ⟨21 * K, by positivity, ?_⟩
  intro Y a s t k θ hk hst hY hac ha hy hv hθ
  let l := fun r => Real.log (Y r 2) - Real.log (Y s 2)
  let q := fun r => a r * entranceClockRate (Y r)
  let P := fun r => Y r 1 * Y r 2
  let S := fun r => (Y r 2 * Y r 3) ^ 2
  let w := Y s 3
  have hs : s ∈ Icc s t := ⟨le_rfl, hst⟩
  have hk0 : 0 < k := by linarith
  have hk1 : 1 ≤ k := by linarith
  have hk2 : 1 ≤ k ^ 2 := one_le_pow₀ hk1
  have hθ0 : 0 ≤ θ := by rcases hθ with rfl | ⟨rfl, _⟩ <;> positivity
  have hw0 : 0 ≤ w := (hy s hs).2.2.2.2.1
  have hw1 : w ≤ 1 := by dsimp [w]; linarith [(hy s hs).2.2.2.2.2]
  have hcoord (i : Fin 4) : ContinuousOn (fun r => Y r i) (Icc s t) :=
    (continuous_apply i).comp_continuousOn (HasDerivAt.continuousOn hY)
  have hz (r : ℝ) (hr : r ∈ Icc s t) := hasDerivAt_entranceLog_scaled (hY r hr) (hv r hr).ne'
  have hqc : ContinuousOn q (Icc s t) := hac.mul
    (continuous_entranceClockRate.comp_continuousOn (HasDerivAt.continuousOn hY))
  have hql (r : ℝ) (hr : r ∈ Icc s t) : 0 ≤ q r :=
    mul_nonneg (ha r hr) (entranceRegion_clock_pos hk (hy r hr)).le
  have hlogc := HasDerivAt.continuousOn hz
  have hlc : ContinuousOn l (Icc s t) := hlogc.sub continuousOn_const
  have hmono : MonotoneOn (fun r => Real.log (Y r 2)) (Icc s t) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc s t) hlogc
      (fun r hr => (hz r (interior_subset hr)).hasDerivWithinAt) (fun r hr => hql r (interior_subset hr))
  have hl (r : ℝ) (hr : r ∈ Icc s t) : 0 ≤ l r := sub_nonneg.mpr (hmono hs hr hr.1)
  have hPc : ContinuousOn P (Icc s t) := (hcoord 1).mul (hcoord 2)
  have hSc : ContinuousOn S (Icc s t) := ((hcoord 2).mul (hcoord 3)).pow 2
  have hCc : ContinuousOn (fun r => entranceRadialVariationCoefficients (Y r)) (Icc s t) := by
    intro r hr
    exact ((continuousAt_entranceRadialVariationCoefficients hk (hy r hr) (hv r hr)).comp
      (hY r hr).continuousAt).continuousWithinAt
  have hc (i : Fin 3) := (continuous_apply i).comp_continuousOn hCc
  have hFc : ContinuousOn (fun r => entrancePhaseFeedbackRate k (l r) (Y r) * q r) (Icc s t) :=
    (((hc 0).abs.add (hlc.mul ((hc 1).abs.add ((hc 2).abs.div_const _)))).mul hqc)
  have hW := (scaled_entrance_wall_budgets hk hst hY hac ha hy hv).1
  let A := K / k ^ 2
  let B := K * (1 + w / k ^ 2)
  let E := K * θ / k ^ 3
  let F := K * θ / k ^ 4
  let p0 := fun r => P r * q r
  let p1 := fun r => l r * P r * q r
  let s0 := fun r => S r * q r
  let s1 := fun r => l r * S r * q r
  have hp0 : ContinuousOn p0 (Icc s t) := hPc.mul hqc
  have hp1 : ContinuousOn p1 (Icc s t) := (hlc.mul hPc).mul hqc
  have hs0 : ContinuousOn s0 (Icc s t) := hSc.mul hqc
  have hs1 : ContinuousOn s1 (Icc s t) := (hlc.mul hSc).mul hqc
  have hpoint (r : ℝ) (hr : r ∈ Icc s t) :
      entrancePhaseFeedbackRate k (l r) (Y r) * q r ≤ A * p0 r + B * p1 r + E * s0 r + F * s1 r := by
    have hθr : θ = 1 ∨ (θ = 1 / k ^ 2 ∧ k * (Y r 1 + Y r 3) ^ 2 ≤ 1) := by
      rcases hθ with h | ⟨h, hb⟩
      · exact Or.inl h
      · refine Or.inr ⟨h, ?_⟩
        have hsum := add_le_add (hW r hr).1 (hW r hr).2
        have hsq := (sq_le_sq₀ (add_nonneg (hy r hr).2.2.1.1 (hy r hr).2.2.2.2.1)
          (add_nonneg (hy s hs).2.2.1.1 hw0)).mpr hsum
        exact (mul_le_mul_of_nonneg_left hsq hk0.le).trans hb
    obtain ⟨hrate, hx, hy'⟩ := HK k θ (Y r) hk (hy r hr) (hv r hr) hθr
    have hprod : Y r 1 * Y r 2 * Y r 3 ≤ P r * w :=
      mul_le_mul_of_nonneg_left (hW r hr).2 (mul_nonneg (hy r hr).2.2.1.1 (hy r hr).2.2.2.1.1)
    have hby : |entranceRadialVariationCoefficients (Y r) 2| ≤ K * (P r * w + θ * S r / k ^ 2) := by
      apply hy'.trans (mul_le_mul_of_nonneg_left (add_le_add hprod ?_) hK.le)
      exact le_of_eq (by dsimp [S]; ring)
    have hb := add_le_add hrate (mul_le_mul_of_nonneg_left
      (add_le_add hx (div_le_div_of_nonneg_right hby (sq_nonneg k))) (hl r hr))
    have H := mul_le_mul_of_nonneg_right hb (hql r hr)
    apply H.trans_eq
    dsimp [A, B, E, F, p0, p1, s0, s1, P, S]
    ring
  have hi := intervalIntegral.integral_mono_on (μ := volume) hst (hFc.intervalIntegrable_of_Icc hst)
    (((((hp0.const_mul A).add (hp1.const_mul B)).add (hs0.const_mul E)).add (hs1.const_mul F)).intervalIntegrable_of_Icc hst) hpoint
  simp only [Pi.add_apply] at hi
  have hAB : ContinuousOn (fun r => A * p0 r + B * p1 r) (Icc s t) :=
    (hp0.const_mul A).add (hp1.const_mul B)
  have hABE : ContinuousOn (fun r => A * p0 r + B * p1 r + E * s0 r) (Icc s t) :=
    hAB.add (hs0.const_mul E)
  rw [intervalIntegral.integral_add (hABE.intervalIntegrable_of_Icc hst)
      ((hs1.const_mul F).intervalIntegrable_of_Icc hst),
    intervalIntegral.integral_add (hAB.intervalIntegrable_of_Icc hst) ((hs0.const_mul E).intervalIntegrable_of_Icc hst),
    intervalIntegral.integral_add ((hp0.const_mul A).intervalIntegrable_of_Icc hst) ((hp1.const_mul B).intervalIntegrable_of_Icc hst),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hi
  obtain ⟨hP0, hP1, hS0, hS1⟩ := scaled_entrance_product_moments hk hst hY hac ha hy hv
  have hsum := add_le_add (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hP0 (show 0 ≤ A by dsimp [A]; positivity))
    (mul_le_mul_of_nonneg_left hP1 (show 0 ≤ B by dsimp [B]; positivity)))
    (mul_le_mul_of_nonneg_left hS0 (show 0 ≤ E by dsimp [E]; positivity)))
    (mul_le_mul_of_nonneg_left hS1 (show 0 ≤ F by dsimp [F]; positivity))
  apply hi.trans (hsum.trans ?_)
  have hp : 0 ≤ Y s 1 * Y s 2 := mul_nonneg (hy s hs).2.2.1.1 (hy s hs).2.2.2.1.1
  have hkw : w / k ^ 2 ≤ 1 := (div_le_self hw0 hk2).trans hw1
  have hpdiv : 3 * (Y s 1 * Y s 2) / k ≤ 3 * (Y s 1 * Y s 2) := div_le_self (by positivity) hk1
  have hmix : (1 + w / k ^ 2) * (9 * (Y s 1 * Y s 2)) ≤ 18 * (Y s 1 * Y s 2) := by
    nlinarith only [mul_le_mul_of_nonneg_right hkw (show 0 ≤ 9 * (Y s 1 * Y s 2) by positivity)]
  have hlast : 3 * (Y s 1 * Y s 2) / k + (1 + w / k ^ 2) * (9 * (Y s 1 * Y s 2)) +
      θ * (Y s 2 * Y s 3) ^ 2 / 2 + θ * (Y s 2 * Y s 3) ^ 2 / 4 ≤
        21 * (Y s 1 * Y s 2 + θ * (Y s 2 * Y s 3) ^ 2) := by
    nlinarith only [hpdiv, hmix, mul_nonneg hθ0 (sq_nonneg (Y s 2 * Y s 3))]
  have H := mul_le_mul_of_nonneg_left hlast (show 0 ≤ K / k ^ 2 by positivity)
  convert! H using 1
  · dsimp [A, B, E, F]
    field_simp
  · ring

end BianchiIX
