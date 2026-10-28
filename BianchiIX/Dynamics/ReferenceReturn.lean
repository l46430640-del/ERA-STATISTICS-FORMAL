import BianchiIX.Dynamics.ReferencePulse
import BianchiIX.Dynamics.ProjectiveClock

noncomputable section

namespace BianchiIX

open Set MeasureTheory

def referenceHalfTime (k : ℝ) : ℝ := Real.arcosh k / k

def referenceNormalizedTime (k : ℝ) : ℝ :=
  (k ^ 2 + 4) * Real.arcosh k / (3 * k)

theorem referenceHalfTime_pos {k : ℝ} (hk : 1 < k) : 0 < referenceHalfTime k :=
  div_pos (Real.arcosh_pos hk) (lt_trans zero_lt_one hk)

theorem referencePulse_exit {k : ℝ} (hk : 1 < k) :
    referencePulse k (referenceHalfTime k) = ![1 - Real.sqrt (k ^ 2 - 1), 0, 1, 0] := by
  have hk0 : k ≠ 0 := ne_of_gt (lt_trans zero_lt_one hk)
  simp only [referencePulse, referenceHalfTime, mul_div_cancel₀ _ hk0,
    Real.tanh_arcosh hk.le, Real.cosh_arcosh hk.le, div_self hk0]

theorem referencePulse_entry {k : ℝ} (hk : 1 < k) :
    referencePulse k (-referenceHalfTime k) = ![1 + Real.sqrt (k ^ 2 - 1), 0, 1, 0] := by
  have hk0 : k ≠ 0 := ne_of_gt (lt_trans zero_lt_one hk)
  simp only [referencePulse, referenceHalfTime, mul_neg, mul_div_cancel₀ _ hk0,
    Real.tanh_neg, Real.cosh_neg, Real.tanh_arcosh hk.le, Real.cosh_arcosh hk.le,
    div_self hk0]
  congr 2
  ring

theorem referencePulse_above_section {k t : ℝ} (hk : 1 < k)
    (ht : t ∈ Ioo (-referenceHalfTime k) (referenceHalfTime k)) :
    1 < referencePulse k t 2 := by
  have hk0 : 0 < k := lt_trans zero_lt_one hk
  have hkt : |k * t| < Real.arcosh k := by
    apply abs_lt.mpr
    constructor
    · have h := mul_lt_mul_of_pos_left ht.1 hk0
      simpa [referenceHalfTime, mul_div_cancel₀ _ (ne_of_gt hk0)] using h
    · have h := mul_lt_mul_of_pos_left ht.2 hk0
      simpa [referenceHalfTime, mul_div_cancel₀ _ (ne_of_gt hk0)] using h
  have hc : Real.cosh (k * t) < k := by
    calc
      Real.cosh (k * t) < Real.cosh (Real.arcosh k) :=
        Real.cosh_lt_cosh.mpr (by simpa only [abs_of_pos (Real.arcosh_pos hk)] using hkt)
      _ = k := Real.cosh_arcosh hk.le
  exact (one_lt_div (Real.cosh_pos _)).mpr hc

theorem referencePulse_crossing_derivatives {k : ℝ} (hk : 1 < k) :
    HasDerivAt (fun t => referencePulse k t 2) (Real.sqrt (k ^ 2 - 1))
      (-referenceHalfTime k) ∧
    HasDerivAt (fun t => referencePulse k t 2) (-Real.sqrt (k ^ 2 - 1))
      (referenceHalfTime k) := by
  constructor
  · have h := hasDerivAt_pi.mp (hasDerivAt_referencePulse k (-referenceHalfTime k)) 2
    simpa [referencePulse_entry hk, projectiveField, activeVelocity, coupling] using h
  · have h := hasDerivAt_pi.mp (hasDerivAt_referencePulse k (referenceHalfTime k)) 2
    simpa [referencePulse_exit hk, projectiveField, activeVelocity, coupling] using h

def referenceClockPrimitive (k t : ℝ) : ℝ :=
  (k ^ 2 + 4) * t / 6 - Real.log (Real.cosh (k * t)) / 3

theorem hasDerivAt_referenceClockPrimitive (k t : ℝ) :
    HasDerivAt (referenceClockPrimitive k) (projectiveStateDenom (referencePulse k t) / 6) t := by
  have hz : HasDerivAt (fun s : ℝ => k * s) k t := by
    simpa using (hasDerivAt_id t).const_mul k
  have hlog := (hz.cosh.log (ne_of_gt (Real.cosh_pos (k * t)))).div_const 3
  convert! (((hasDerivAt_id t).const_mul (k ^ 2 + 4)).div_const 6).sub hlog using 1
  · rw [referencePulse_denom, Real.tanh_eq_sinh_div_cosh]
    ring

theorem referencePulse_clock_integral (k a b : ℝ) :
    integralClock (fun t => projectiveStateDenom (referencePulse k t) / 6) a b =
      referenceClockPrimitive k b - referenceClockPrimitive k a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_referenceClockPrimitive k t)
  have hc : Continuous (referencePulse k) :=
    continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_referencePulse k t).continuousAt)
  exact ((continuous_projectiveStateDenom.comp hc).div_const 6).intervalIntegrable _ _

theorem referencePulse_crossing_time (k : ℝ) :
    integralClock (fun t => projectiveStateDenom (referencePulse k t) / 6)
      (-referenceHalfTime k) (referenceHalfTime k) = referenceNormalizedTime k := by
  rw [referencePulse_clock_integral]
  simp only [referenceClockPrimitive, referenceNormalizedTime, mul_neg, Real.cosh_neg]
  unfold referenceHalfTime
  ring

theorem referenceNormalizedTime_pos {k : ℝ} (hk : 1 < k) :
    0 < referenceNormalizedTime k := by
  exact div_pos (mul_pos (by positivity) (Real.arcosh_pos hk))
    (mul_pos (by norm_num) (lt_trans zero_lt_one hk))

/-- The entire first crossing is realized by the original maximal flow. -/
theorem referencePulse_normalized_crossing {k : ℝ} (hk : 1 < k) :
    Icc 0 (referenceNormalizedTime k) ⊆ normalizedMaxDomain
      (fromProjectiveState ![1 + Real.sqrt (k ^ 2 - 1), 0, 1, 0]) 0 ∧
    normalizedMaxCurve (fromProjectiveState ![1 + Real.sqrt (k ^ 2 - 1), 0, 1, 0]) 0
      (referenceNormalizedTime k) =
      fromProjectiveState ![1 - Real.sqrt (k ^ 2 - 1), 0, 1, 0] ∧
    ∀ t ∈ Ioo 0 (referenceNormalizedTime k),
      1 < toProjectiveState (normalizedMaxCurve
        (fromProjectiveState ![1 + Real.sqrt (k ^ 2 - 1), 0, 1, 0]) 0 t) 2 := by
  obtain ⟨e, hsrc, he, _, hconv, hzero, _, hmono, hdom, hflow⟩ :=
    exists_projective_normalized_reparametrization (β := referencePulse k)
      (s := -referenceHalfTime k) convex_univ isOpen_univ (mem_univ _)
      (fun t _ => hasDerivAt_referencePulse k t) (fun t _ => referencePulse_denom_pos k t)
  have hmem : referenceHalfTime k ∈ e.source := by rw [hsrc]; trivial
  have ht : e (referenceHalfTime k) = referenceNormalizedTime k := by
    rw [he, referencePulse_crossing_time k]
  have htarget : referenceNormalizedTime k ∈ e.target := ht ▸ e.map_source hmem
  have hinter : Icc 0 (referenceNormalizedTime k) ⊆ e.target :=
    (Icc_subset_uIcc ..).trans (hconv.ordConnected.uIcc_subset hzero htarget)
  have hbase : e (-referenceHalfTime k) = 0 := by
    rw [he]
    exact integralClock_initial _ _
  have hinv : e.symm (referenceNormalizedTime k) = referenceHalfTime k := by
    rw [← ht, e.left_inv hmem]
  have h := (hflow _ htarget).1
  rw [hinv, referencePulse_entry hk, referencePulse_exit hk] at h
  refine ⟨by simpa only [referencePulse_entry hk] using hinter.trans hdom, h.symm, ?_⟩
  intro t htt
  have htg : t ∈ e.target := hinter ⟨htt.1.le, htt.2.le⟩
  have hleft : -referenceHalfTime k < e.symm t := by
    by_contra! hn
    have H := hmono.monotoneOn (mem_univ (e.symm t)) (mem_univ (-referenceHalfTime k)) hn
    rw [e.right_inv htg, hbase] at H
    exact (not_le_of_gt htt.1) H
  have hright : e.symm t < referenceHalfTime k := by
    by_contra! hn
    have H := hmono.monotoneOn (mem_univ (referenceHalfTime k)) (mem_univ (e.symm t)) hn
    rw [e.right_inv htg, ht] at H
    exact (not_le_of_gt htt.2) H
  have H := (hflow t htg).2
  rw [referencePulse_entry hk] at H
  rw [H]
  exact referencePulse_above_section hk ⟨hleft, hright⟩

end BianchiIX
