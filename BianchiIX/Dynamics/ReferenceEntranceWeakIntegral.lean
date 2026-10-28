import BianchiIX.Dynamics.ReferenceEntranceWeakProfile
import BianchiIX.Dynamics.ReferenceEntranceWeakExpansion
import BianchiIX.Dynamics.ReferenceClockTransport

noncomputable section

namespace BianchiIX

open Set MeasureTheory

/-- The actual loss, including its moving endpoint, expressed in reference projective time. -/
theorem referenceEntrance_weak_loss_clock {k v : ℝ} (hk : 7 / 4 ≤ k) (hv : 0 < v ∧ v < 1) :
    entranceWeakQuadraticLoss (referenceEntranceState k v) =
      v ^ 2 * ((∫ r in (-referenceHeightTime k v)..(-referenceHalfTime k),
        Real.exp (-4 * (r + referenceHeightTime k v)) * entranceWeakDriftWeight (referencePulse k r)) +
        Real.exp (-4 * referenceEntranceDuration k v) *
          entranceWeakCorrectionWeight (referencePulse k (-referenceHalfTime k))) := by
  let y := referenceEntranceState k v
  let s := -referenceHeightTime k v
  let t := -referenceHalfTime k
  let T := entranceReturnTime y
  let Γ := referenceShiftClock k s
  let a := normalizedProjectiveRate (fromProjectiveState y) 0
  let Y := projectiveOriginalFlow y 0
  let E := fun u => Real.exp (-4 * ∫ z in 0..u, a z)
  let f := fun u => E u * entranceWeakDriftWeight (Y u)
  have hk0 : 0 < k := by linarith
  have hk1 : 1 < k := by linarith
  have hentry : referencePulse k s = y := referencePulse_height_entry hk0 ⟨hv.1, by linarith [hv.2]⟩
  have hR := referenceEntrance_radius hk0 ⟨hv.1, by linarith [hv.2]⟩
  have hm : 1 ≤ y 0 := le_add_of_nonneg_right (Real.sqrt_nonneg _)
  have hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000 := by dsimp [y, referenceEntranceState]; norm_num
  have hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000 := by dsimp [y, referenceEntranceState]; norm_num
  have H := (entranceReturn_regular (show 7 / 4 ≤ coreRadius (y 0) (y 2) by rw [hR]; exact hk)
    hm hu hv hw).1
  have hD : 0 < projectiveStateDenom y := by rw [← hentry]; exact referencePulse_denom_pos k s
  have hret := referenceEntrance_return hk hv
  have htime : T = Γ t := hret.1
  have hst : s ≤ t := (neg_lt_neg (referenceHalfTime_lt_heightTime hk1 hv)).le
  have hdiff : t - s = referenceEntranceDuration k v := by dsimp [s, t, referenceEntranceDuration]; ring
  have hmap : Γ '' uIcc s t ⊆ Icc 0 T := by
    rintro u ⟨r, hr, rfl⟩
    rw [uIcc_of_le hst] at hr
    constructor
    · have HH := (referenceShiftClock_strictMono k s).monotone hr.1
      simpa only [referenceShiftClock_initial] using HH
    · rw [htime]
      exact (referenceShiftClock_strictMono k s).monotone hr.2
  have horbit (r : ℝ) : Y (Γ r) = referencePulse k r := by
    change projectiveOriginalFlow y 0 (referenceShiftClock k s r) = _
    rw [← hentry]
    exact referenceShiftClock_projective_orbit k s r
  have hclock (r : ℝ) : (∫ u in 0..Γ r, a u) = r - s := by
    dsimp only [a, Γ]
    rw [← hentry]
    exact referenceShiftClock_elapsed k s r
  have hac : ContinuousOn a (Icc 0 T) := (continuousOn_normalizedProjectiveRate _ _).mono
    (fun u hu => (H.2.1 u hu).1)
  have hprim : ContinuousOn (fun u => ∫ z in 0..u, a z) (Icc 0 T) := by
    simpa only [uIcc_of_le H.1.1.1.le] using intervalIntegral.continuousOn_primitive_interval'
      (hac.intervalIntegrable_of_Icc H.1.1.1.le) left_mem_uIcc
  have hEc : ContinuousOn E (Icc 0 T) := Real.continuous_exp.comp_continuousOn (hprim.const_mul (-4))
  have hgc : ContinuousOn (fun u => entranceWeakDriftWeight (Y u)) (Γ '' uIcc s t) := by
    rintro u ⟨r, hr, rfl⟩
    have hur := hmap (mem_image_of_mem Γ hr)
    have hY : ContinuousAt Y (Γ r) := (hasDerivAt_projectiveOriginalFlow_time hD
      (H.2.1 _ hur).1 (H.2.1 _ hur).2).continuousAt
    have hmr : 2 ≤ referencePulse k r 0 := by
      have HH := antitone_referencePulse_phase k ((uIcc_of_le hst ▸ hr).2)
      change referencePulse k t 0 ≤ referencePulse k r 0 at HH
      rw [referencePulse_entry hk1] at HH
      have hs := (referenceEntrancePhase_lower (v := v) hk (le_refl (referenceEntranceDuration k v))).1
      change 1 + Real.sqrt (k ^ 2 - 1) ≤ referencePulse k r 0 at HH
      linarith
    have hg := (continuousAt_entranceWeak_weights hmr
      (by change |(0 : ℝ)| < 1 / 200; norm_num)
      (by change |(0 : ℝ)| < 1 / 200; norm_num) (referencePulse_active_pos hk0 r)).1
    rw [← horbit r] at hg
    exact (hg.comp hY).continuousWithinAt
  have hf : ContinuousOn f (Γ '' uIcc s t) := (hEc.mono hmap).mul hgc
  have HI := referenceShiftClock_weighted_integral k s t (f := f) hf
  rw [hentry] at HI
  change (∫ u in 0..Γ t, a u * f u) = ∫ r in s..t, f (Γ r) at HI
  rw [← htime] at HI
  have HI' : (∫ u in 0..T, a u * f u) =
      ∫ r in s..t, Real.exp (-4 * (r - s)) * entranceWeakDriftWeight (referencePulse k r) := by
    rw [HI]
    apply intervalIntegral.integral_congr
    intro r _
    change E (Γ r) * entranceWeakDriftWeight (Y (Γ r)) = _
    dsimp only [E]
    rw [horbit, hclock]
  have HQ : entranceWeakQuadraticLoss y = v ^ 2 * ((∫ u in 0..T, a u * f u) +
      E T * entranceWeakCorrectionWeight (entranceReturnState y)) := by
    unfold entranceWeakQuadraticLoss
    change (∫ u in 0..T, a u * v ^ 2 * E u * entranceWeakDriftWeight (Y u)) +
      v ^ 2 * E T * entranceWeakCorrectionWeight (entranceReturnState y) = _
    rw [mul_add]
    congr 1
    · rw [← intervalIntegral.integral_const_mul (v ^ 2) (fun u => a u * f u)]
      apply intervalIntegral.integral_congr
      intro u _
      dsimp [f]
      ring
    · ring
  have HE : E T = Real.exp (-4 * referenceEntranceDuration k v) := by
    dsimp only [E]
    rw [htime, hclock, hdiff]
  rw [HQ, HI', hret.2, HE]
  simp only [s, t, sub_neg_eq_add]

theorem referenceEntrance_weak_loss_eq {k v : ℝ} (hk : 7 / 4 ≤ k) (hv : 0 < v ∧ v < 1) :
    entranceWeakQuadraticLoss (referenceEntranceState k v) = -referenceEntranceWeakResponse k v := by
  let s := -referenceHeightTime k v
  let T := referenceEntranceDuration k v
  have hT : 0 ≤ T := (referenceEntranceDuration_pos (by linarith) hv).le
  have hend : T + s = -referenceHalfTime k := by dsimp [T, s, referenceEntranceDuration]; ring
  have Hshift := intervalIntegral.integral_comp_add_right
    (fun r => Real.exp (-4 * (r + referenceHeightTime k v)) * entranceWeakDriftWeight (referencePulse k r))
    (a := 0) (b := T) s
  rw [zero_add, hend] at Hshift
  have HI : (∫ r in s..(-referenceHalfTime k),
      Real.exp (-4 * (r + referenceHeightTime k v)) * entranceWeakDriftWeight (referencePulse k r)) =
      (1 / k) * ∫ u in 0..T, Real.exp (-4 * u) / (referenceEntrancePhase k v u + 2) ^ 2 := by
    rw [← Hshift, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hT] at hu
    have he : u + s + referenceHeightTime k v = u := by dsimp [s]; ring
    have hr : u + s = -referenceHeightTime k v + u := by dsimp [s]; ring
    dsimp only
    rw [he, hr, (referenceEntrance_weak_weights hk hu.2).1]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [referenceEntrance_weak_loss_clock hk hv, HI,
    (referenceEntrance_weak_weights (v := v) hk (le_refl (referenceEntranceDuration k v))).2]
  dsimp [referenceEntranceWeakResponse, T]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end BianchiIX
