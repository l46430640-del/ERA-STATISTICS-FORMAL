import BianchiIX.Dynamics.EntranceProductMoments

noncomputable section

namespace BianchiIX

open Set MeasureTheory

theorem entranceWeakLogRate_shift_le {y : ProjectiveState} {k : ℝ}
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) : entranceWeakLogRate y + 1 ≤ -(1 / k) := by
  have hD := (entranceRegion_clock_pos hk hy).ne'
  have heq : entranceWeakLogRate y = (-y 0 - 1 - coupling (y 1) (y 2) (y 3)) / entranceClockRate y := by
    unfold entranceWeakLogRate connectionWeakClockRate
    change -1 - 2 * (1 + coupling _ _ _) / entranceClockRate y = _
    field_simp
    unfold entranceClockRate connectionSpeed
    ring
  rw [heq]
  linarith only [(entranceRegion_wall_rates hk hy).2]

/-- The two additional moments needed by the activity forcing, in the original time variable. -/
theorem scaled_entrance_active_source_moments {Y : ℝ → ProjectiveState} {a : ℝ → ℝ} {s t k : ℝ}
    (hk : 7 / 4 ≤ k) (hst : s ≤ t)
    (hY : ∀ r ∈ Icc s t, HasDerivAt Y (a r • projectiveField (Y r)) r)
    (hac : ContinuousOn a (Icc s t)) (ha : ∀ r ∈ Icc s t, 0 ≤ a r)
    (hy : ∀ r ∈ Icc s t, entranceRegion k (Y r)) (hv : ∀ r ∈ Icc s t, 0 < Y r 2) :
    let q := fun r => a r * entranceClockRate (Y r)
    (∫ r in s..t, (Y r 2) ^ 2 * q r) = ((Y t 2) ^ 2 - (Y s 2) ^ 2) / 2 ∧
      (∫ r in s..t, (Y r 2) ^ 2 * q r) ≤ 1 / 2 ∧
      (∫ r in s..t, (Y r 2 * Y r 3) * q r) ≤ k * (Y s 2 * Y s 3) := by
  intro q
  have hk0 : 0 < k := by linarith
  have hcoord (i : Fin 4) := (continuous_apply i).comp_continuousOn (HasDerivAt.continuousOn hY)
  have hqc : ContinuousOn q (Icc s t) := hac.mul
    (continuous_entranceClockRate.comp_continuousOn (HasDerivAt.continuousOn hY))
  have hq (r : ℝ) (hr : r ∈ Icc s t) : 0 ≤ q r :=
    mul_nonneg (ha r hr) (entranceRegion_clock_pos hk (hy r hr)).le
  have hV (r : ℝ) (hr : r ∈ Icc s t) : HasDerivAt (fun z => Y z 2) (q r * Y r 2) r := by
    apply (hasDerivAt_pi.mp (hY r hr) 2).congr_deriv
    change a r * (entranceClockRate (Y r) * Y r 2) = _
    dsimp [q]
    ring
  have hd (r : ℝ) (hr : r ∈ Icc s t) :
      HasDerivAt (fun z => (Y z 2) ^ 2 / 2) ((Y r 2) ^ 2 * q r) r := by
    convert! ((hV r hr).pow 2).div_const 2 using 1
    ring
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r hr => hd r (uIcc_of_le hst ▸ hr))
    ((((hcoord 2).pow 2).mul hqc).intervalIntegrable_of_Icc (μ := volume) hst)
  have hid : (∫ r in s..t, (Y r 2) ^ 2 * q r) = ((Y t 2) ^ 2 - (Y s 2) ^ 2) / 2 := H.trans (by ring)
  have hW (r : ℝ) (hr : r ∈ Icc s t) :
      HasDerivAt (fun z => Y z 3) (q r * entranceWeakLogRate (Y r) * Y r 3) r := by
    apply (hasDerivAt_pi.mp (hY r hr) 3).congr_deriv
    change a r * projectiveField (Y r) 3 = _
    rw [(entranceWallLogRates_field (entranceRegion_clock_pos hk (hy r hr)).ne').2]
    dsimp [q]
    ring
  have hp (r : ℝ) (hr : r ∈ Icc s t) : HasDerivAt (fun z => Y z 2 * Y z 3)
      (q r * (entranceWeakLogRate (Y r) + 1) * (Y r 2 * Y r 3)) r := by
    apply ((hV r hr).mul (hW r hr)).congr_deriv
    ring
  have hz (r : ℝ) (hr : r ∈ Icc s t) := hasDerivAt_entranceLog_scaled (hY r hr) (hv r hr).ne'
  have hdec (r : ℝ) (hr : r ∈ Icc s t) : q r * (entranceWeakLogRate (Y r) + 1) * (Y r 2 * Y r 3) ≤
      -(1 / k) * ((Y r 2 * Y r 3) * q r) := by
    have H := mul_le_mul_of_nonneg_right (entranceWeakLogRate_shift_le hk (hy r hr))
      (mul_nonneg (hq r hr) (mul_nonneg (hv r hr).le (hy r hr).2.2.2.2.1))
    convert! H using 1 <;> ring
  have HP := (integral_clock_moments_le_of_dissipation hst (show 0 < 1 / k by positivity)
    hp hz hqc hq hdec (mul_nonneg (hv t ⟨hst, le_rfl⟩).le (hy t ⟨hst, le_rfl⟩).2.2.2.2.1)).1
  refine ⟨hid, ?_, HP.trans_eq (by field_simp)⟩
  rw [hid]
  have ht := (hy t ⟨hst, le_rfl⟩).2.2.2.1
  have hsq := pow_le_one₀ ht.1 ht.2 (n := 2)
  nlinarith only [hsq, sq_nonneg (Y s 2)]

end BianchiIX
