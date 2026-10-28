import BianchiIX.Analysis.ClockDissipativeMoments
import BianchiIX.Dynamics.EntranceWallLogRates

noncomputable section

namespace BianchiIX

open Set MeasureTheory

theorem scaled_entrance_product_dissipation {Y : ℝ → ProjectiveState} {a t k : ℝ}
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k (Y t)) (ha : 0 ≤ a)
    (hY : HasDerivAt Y (a • projectiveField (Y t)) t) :
    let q := a * entranceClockRate (Y t)
    let p := q * (entranceStrongLogRate (Y t) + 1) * (Y t 1 * Y t 2)
    let b := 2 * q * (entranceWeakLogRate (Y t) + 1) * (Y t 2 * Y t 3) ^ 2
    (HasDerivAt (fun r => Y r 1 * Y r 2) p t ∧ p ≤ -(k / 3) * ((Y t 1 * Y t 2) * q)) ∧
      (HasDerivAt (fun r => (Y r 2 * Y r 3) ^ 2) b t ∧ b ≤ -(2 / k) * ((Y t 2 * Y t 3) ^ 2 * q)) := by
  let q := a * entranceClockRate (Y t)
  have hD := entranceRegion_clock_pos hk hy
  have hq : 0 ≤ q := mul_nonneg ha hD.le
  obtain ⟨hs, hw⟩ := entranceWallLogRates_field hD.ne'
  have hU : HasDerivAt (fun r => Y r 1) (q * entranceStrongLogRate (Y t) * Y t 1) t := by
    apply (hasDerivAt_pi.mp hY 1).congr_deriv
    change a * projectiveField (Y t) 1 = _
    rw [hs]
    dsimp [q]
    ring
  have hV : HasDerivAt (fun r => Y r 2) (q * Y t 2) t := by
    apply (hasDerivAt_pi.mp hY 2).congr_deriv
    change a * (entranceClockRate (Y t) * Y t 2) = _
    dsimp [q]
    ring
  have hW : HasDerivAt (fun r => Y r 3) (q * entranceWeakLogRate (Y t) * Y t 3) t := by
    apply (hasDerivAt_pi.mp hY 3).congr_deriv
    change a * projectiveField (Y t) 3 = _
    rw [hw]
    dsimp [q]
    ring
  have hstrong : entranceStrongLogRate (Y t) + 1 ≤ -(k / 3) := by
    have H := (entranceRegion_wall_rates hk hy).1
    change entranceStrongLogRate (Y t) ≤ _ at H
    linarith only [H]
  have hweak : entranceWeakLogRate (Y t) + 1 ≤ -(1 / k) := by
    have heq : entranceWeakLogRate (Y t) =
        (-Y t 0 - 1 - coupling (Y t 1) (Y t 2) (Y t 3)) / entranceClockRate (Y t) := by
      unfold entranceWeakLogRate connectionWeakClockRate
      change -1 - 2 * (1 + coupling _ _ _) / entranceClockRate (Y t) = _
      field_simp
      unfold entranceClockRate connectionSpeed
      ring
    rw [heq]
    linarith only [(entranceRegion_wall_rates hk hy).2]
  dsimp only
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · apply (hU.mul hV).congr_deriv
    ring
  · have H := mul_le_mul_of_nonneg_right hstrong
      (mul_nonneg hq (mul_nonneg hy.2.2.1.1 hy.2.2.2.1.1))
    convert! H using 1 <;> ring
  · apply ((hV.mul hW).pow 2).congr_deriv
    dsimp [q]
    ring
  · have H := mul_le_mul_of_nonneg_right hweak (show 0 ≤ 2 * q * (Y t 2 * Y t 3) ^ 2 by positivity)
    convert! H using 1 <;> ring

/-- The four moments needed for entrance phase feedback, directly in the actual time variable. -/
theorem scaled_entrance_product_moments {Y : ℝ → ProjectiveState} {a : ℝ → ℝ} {s t k : ℝ}
    (hk : 7 / 4 ≤ k) (hst : s ≤ t)
    (hY : ∀ r ∈ Icc s t, HasDerivAt Y (a r • projectiveField (Y r)) r)
    (hac : ContinuousOn a (Icc s t)) (ha : ∀ r ∈ Icc s t, 0 ≤ a r)
    (hy : ∀ r ∈ Icc s t, entranceRegion k (Y r)) (hv : ∀ r ∈ Icc s t, 0 < Y r 2) :
    let q := fun r => a r * entranceClockRate (Y r)
    let l := fun r => Real.log (Y r 2) - Real.log (Y s 2)
    (∫ r in s..t, (Y r 1 * Y r 2) * q r) ≤ 3 * (Y s 1 * Y s 2) / k ∧
      (∫ r in s..t, l r * (Y r 1 * Y r 2) * q r) ≤ 9 * (Y s 1 * Y s 2) / k ^ 2 ∧
      (∫ r in s..t, (Y r 2 * Y r 3) ^ 2 * q r) ≤ k * (Y s 2 * Y s 3) ^ 2 / 2 ∧
      (∫ r in s..t, l r * (Y r 2 * Y r 3) ^ 2 * q r) ≤ k ^ 2 * (Y s 2 * Y s 3) ^ 2 / 4 := by
  let z := fun r => Real.log (Y r 2)
  let q := fun r => a r * entranceClockRate (Y r)
  have hk0 : 0 < k := by linarith
  have hz (r : ℝ) (hr : r ∈ Icc s t) : HasDerivAt z (q r) r :=
    hasDerivAt_entranceLog_scaled (hY r hr) (hv r hr).ne'
  have hq (r : ℝ) (hr : r ∈ Icc s t) : 0 ≤ q r :=
    mul_nonneg (ha r hr) (entranceRegion_clock_pos hk (hy r hr)).le
  have hqc : ContinuousOn q (Icc s t) := hac.mul
    (continuous_entranceClockRate.comp_continuousOn (HasDerivAt.continuousOn hY))
  have HD (r : ℝ) (hr : r ∈ Icc s t) := scaled_entrance_product_dissipation hk (hy r hr) (ha r hr) (hY r hr)
  have HP := integral_clock_moments_le_of_dissipation hst (show 0 < k / 3 by positivity)
    (fun r hr => (HD r hr).1.1) hz hqc hq (fun r hr => (HD r hr).1.2)
    (mul_nonneg (hy t ⟨hst, le_rfl⟩).2.2.1.1 (hy t ⟨hst, le_rfl⟩).2.2.2.1.1)
  have HS := integral_clock_moments_le_of_dissipation hst (show 0 < 2 / k by positivity)
    (fun r hr => (HD r hr).2.1) hz hqc hq (fun r hr => (HD r hr).2.2) (sq_nonneg _)
  refine ⟨HP.1.trans_eq ?_, HP.2.trans_eq ?_, HS.1.trans_eq ?_, HS.2.trans_eq ?_⟩
  all_goals field_simp <;> ring

end BianchiIX
