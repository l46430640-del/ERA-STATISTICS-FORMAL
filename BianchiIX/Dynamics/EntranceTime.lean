import BianchiIX.Dynamics.EntranceArrival

noncomputable section

namespace BianchiIX

open Set MeasureTheory

theorem normalized_entrance_projective_time {x : NormalizedState} {t₀ s t k : ℝ}
    (hc : stateConstraint x = 1) (hk : 7 / 4 ≤ k) (hs : t₀ ≤ s) (hst : s ≤ t)
    (hA : ∀ r ∈ Icc s t, 0 < normalizedProjectiveRate x t₀ r) :
    let Y := fun r => toProjectiveState (normalizedMaxCurve x t₀ r)
    (∀ r ∈ Icc s t, entranceRegion k (Y r)) → 0 < Y s 2 → Y t 2 = 1 →
    Real.log (1 / Y s 2) / (2 * k) ≤ integralClock (normalizedProjectiveRate x t₀) s t ∧
      integralClock (normalizedProjectiveRate x t₀) s t ≤ 2 * Real.log (1 / Y s 2) / k := by
  intro Y hy hvs hvt
  have hk0 : 0 < k := by linarith
  have hsm : s ∈ Icc s t := ⟨le_rfl, hst⟩
  have hdom (r : ℝ) (hr : s ≤ r) := normalizedMaxDomain_contains_Ici_of_constraint hc t₀ (hs.trans hr)
  have hY (r : ℝ) (hr : r ∈ Icc s t) : HasDerivAt Y
      (normalizedProjectiveRate x t₀ r • projectiveField (Y r)) r := by
    have H := normalizedMaxCurve_forward_of_constraint hc (hs.trans hr.1)
    exact hasDerivAt_toProjectiveState_normalized H.1 (hA r hr).ne' H.2.1
  have hv (r : ℝ) (hr : r ∈ Icc s t) : 0 < Y r 2 :=
    normalized_projective_wall_pos (hdom s le_rfl) (hdom r hr.1) (hA s hsm) (hA r hr) 1 hvs
  let a := normalizedProjectiveRate x t₀
  let q := fun r => a r * entranceClockRate (Y r)
  have hac : ContinuousOn a (Icc s t) := (continuousOn_normalizedProjectiveRate x t₀).mono (fun r hr => hdom r hr.1)
  have hqc : ContinuousOn q (Icc s t) := hac.mul
    (continuous_entranceClockRate.comp_continuousOn (HasDerivAt.continuousOn hY))
  have hId : (∫ r in s..t, q r) = Real.log (1 / Y s 2) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r hr => hasDerivAt_entranceLog_scaled (hY r (uIcc_of_le hst ▸ hr)) (hv r (uIcc_of_le hst ▸ hr)).ne')
      (hqc.intervalIntegrable_of_Icc hst)]
    rw [hvt, Real.log_one, one_div, Real.log_inv, zero_sub]
  have hlow (r : ℝ) (hr : r ∈ Icc s t) : (3 / 4 * k) * a r ≤ q r := by
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (entranceRegion_speed hk (hy r hr)).1 (hA r hr).le
  have hhigh (r : ℝ) (hr : r ∈ Icc s t) : q r ≤ (21 / 20 * k) * a r := by
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (entranceRegion_speed hk (hy r hr)).2 (hA r hr).le
  have hIlow := intervalIntegral.integral_mono_on (μ := volume) hst
    ((hac.const_mul (3 / 4 * k)).intervalIntegrable_of_Icc hst) (hqc.intervalIntegrable_of_Icc hst) hlow
  have hIhigh := intervalIntegral.integral_mono_on (μ := volume) hst
    (hqc.intervalIntegrable_of_Icc hst) ((hac.const_mul (21 / 20 * k)).intervalIntegrable_of_Icc hst) hhigh
  rw [intervalIntegral.integral_const_mul, hId] at hIlow
  rw [intervalIntegral.integral_const_mul, hId] at hIhigh
  have hτ : 0 ≤ ∫ r in s..t, a r := intervalIntegral.integral_nonneg hst (fun r hr => (hA r hr).le)
  unfold integralClock
  change _ ≤ (∫ r in s..t, a r) ∧ (∫ r in s..t, a r) ≤ _
  constructor
  · apply (div_le_iff₀ (by positivity : 0 < 2 * k)).mpr
    nlinarith only [hIhigh, mul_nonneg hk0.le hτ]
  · apply (le_div_iff₀ hk0).mpr
    nlinarith only [hIlow, mul_nonneg hk0.le hτ]

theorem normalized_entrance_arrival_transverse {x : NormalizedState} {t₀ t k : ℝ}
    (hc : stateConstraint x = 1) (hk : 7 / 4 ≤ k) (ht : t₀ ≤ t)
    (hA : 0 < normalizedProjectiveRate x t₀ t) :
    let Y := fun r => toProjectiveState (normalizedMaxCurve x t₀ r)
    entranceRegion k (Y t) → Y t 2 = 1 →
    HasDerivAt (fun r => Y r 2) (normalizedProjectiveRate x t₀ t * entranceClockRate (Y t)) t ∧
      0 < normalizedProjectiveRate x t₀ t * entranceClockRate (Y t) := by
  intro Y hy hv
  have H := normalizedMaxCurve_forward_of_constraint hc ht
  have hd := hasDerivAt_pi.mp (hasDerivAt_toProjectiveState_normalized H.1 hA.ne' H.2.1) 2
  change HasDerivAt (fun r => Y r 2) (normalizedProjectiveRate x t₀ t * (entranceClockRate (Y t) * Y t 2)) t at hd
  rw [hv, mul_one] at hd
  exact ⟨hd, mul_pos hA (entranceRegion_clock_pos hk hy)⟩

theorem exists_entrance_first_arrival {k m u v w : ℝ} (hk : 7 / 4 ≤ k)
    (hm : 1 ≤ m) (hR : coreRadius m v = k) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 < v ∧ v < 1) (hw : 0 ≤ w ∧ w ≤ 1 / 10000) :
    let x := fromProjectiveState ![m, u, v, w]
    let Y := fun r => toProjectiveState (normalizedMaxCurve x 0 r)
    ∃ T > (0 : ℝ), Y T 2 = 1 ∧ (∀ r ∈ Ico 0 T, Y r 2 < 1) ∧
      (Real.log (1 / v) / (2 * k) ≤ integralClock (normalizedProjectiveRate x 0) 0 T ∧
        integralClock (normalizedProjectiveRate x 0) 0 T ≤ 2 * Real.log (1 / v) / k) ∧
      (∀ r ∈ Icc 0 T, 1 / (2 * (k + 1) ^ 2) ≤ normalizedProjectiveRate x 0 r ∧
        |coreRadius (Y r 0) (Y r 2) - k| < k / 200 ∧
        (3 / 4 * k ≤ entranceClockRate (Y r) ∧ entranceClockRate (Y r) ≤ 21 / 20 * k) ∧
        Y r 1 ≤ u * Real.exp (-(1 + k / 3) * (Real.log (Y r 2) - Real.log v)) ∧
        Y r 3 ≤ w * Real.exp (-(1 + 1 / k) * (Real.log (Y r 2) - Real.log v))) := by
  intro x Y
  have hrad : |coreRadius m v - k| ≤ k / 100 := by rw [hR, sub_self, abs_zero]; linarith
  have hD : 0 < projectiveStateDenom ![m, u, v, w] :=
    (entrance_denom_bounds hk (entrance_phase_bounds hk hm hrad ⟨hv.1.le, hv.2.le⟩) hu ⟨hv.1.le, hv.2.le⟩ hw).1
  have hc : stateConstraint x = 1 := fromProjectiveState_constraint hD.ne'
  have hinit : toProjectiveState (normalizedMaxCurve x 0 0) = ![m, u, v, w] := by
    rw [normalizedMaxCurve_initial]
    exact toProjectiveState_fromProjectiveState hD.ne'
  have hA : 0 < normalizedProjectiveRate x 0 0 := by
    unfold normalizedProjectiveRate
    rw [normalizedMaxCurve_initial]
    exact fromProjectiveState_clock_pos hD
  obtain ⟨T, hT, hhit, hbefore, hregion, hbounds⟩ := exists_normalized_entrance_first_arrival hc hk le_rfl hA
    (by simpa [hinit] using hm) (by simpa [hinit] using hR) (by simpa [hinit] using hu)
    (by simpa [hinit] using hv) (by simpa [hinit] using hw)
  have hK : 0 < k + 1 := by linarith
  have hpos : 0 < 1 / (2 * (k + 1) ^ 2) := by positivity
  have hAp (r : ℝ) (hr : r ∈ Icc 0 T) := hpos.trans_le (hregion r hr).1
  have htime := normalized_entrance_projective_time hc hk le_rfl hT.le hAp
    (fun r hr => (hregion r hr).2) (by simpa [hinit] using hv.1) hhit
  refine ⟨T, hT, hhit, hbefore, ?_, ?_⟩
  · simpa [hinit] using htime
  · intro r hr
    refine ⟨(hregion r hr).1, (hbounds r hr).1, entranceRegion_speed hk (hregion r hr).2, ?_⟩
    simpa [hinit] using (hbounds r hr).2

end BianchiIX
