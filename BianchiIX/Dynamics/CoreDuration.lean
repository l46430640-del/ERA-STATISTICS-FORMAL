import BianchiIX.Dynamics.CoreTraversal
import Mathlib.Analysis.SpecialFunctions.Arcosh

noncomputable section

namespace BianchiIX

open Set

theorem coreAngle_exit_eq_arcosh {m : ℝ} (hm : m < 1) :
    coreAngle m 1 = Real.arcosh (coreRadius m 1) := by
  have H := Real.arcosh_cosh ((coreAngle_section_sign m).2.mpr hm).le
  rw [cosh_coreAngle (by norm_num : (0 : ℝ) < 1), div_one] at H
  exact H.symm

theorem coreAngle_entry_eq_neg_arcosh {m : ℝ} (hm : 1 < m) :
    coreAngle m 1 = -Real.arcosh (coreRadius m 1) := by
  have H := Real.arcosh_cosh (neg_nonneg.mpr ((coreAngle_section_sign m).1.mpr hm).le)
  rw [Real.cosh_neg, cosh_coreAngle (by norm_num : (0 : ℝ) < 1), div_one] at H
  linarith

theorem scaled_core_projective_duration {β : ℝ → ProjectiveState} {a τ : ℝ → ℝ} {I : Set ℝ}
    {k s t : ℝ} (hk : 6 ≤ k) (hI : Convex ℝ I)
    (ha : ∀ u ∈ I, 0 ≤ a u)
    (hβ : ∀ u ∈ I, HasDerivAt β (a u • projectiveField (β u)) u)
    (hτ : ∀ u ∈ I, HasDerivAt τ (a u) u)
    (hr : ∀ u ∈ I, 99 / 100 * k ≤ coreRadius (β u 0) (β u 2) ∧
      coreRadius (β u 0) (β u 2) ≤ 101 / 100 * k)
    (hv : ∀ u ∈ I, 1 ≤ β u 2)
    (hu : ∀ u ∈ I, 0 ≤ β u 1 ∧ β u 1 ≤ (1 / 10000) / k)
    (hw : ∀ u ∈ I, 0 ≤ β u 3 ∧ β u 3 ≤ (1 / 10000) / k)
    (hs : s ∈ I) (ht : t ∈ I) (hst : s ≤ t) :
    τ t - τ s ≤ 4 * Real.log (4 * k) / k := by
  have hk0 : 0 < k := by linarith
  let z := fun u => coreAngle (β u 0) (β u 2)
  let q := fun u => a u * coreRadius (β u 0) (β u 2) *
    coreClockFactor (coreRadius (β u 0) (β u 2)) (β u 1) (β u 3)
  have hz (u : ℝ) (hh : u ∈ I) : HasDerivAt z (q u) u :=
    hasDerivAt_coreAngle_scaled (hβ u hh) (lt_of_lt_of_le zero_lt_one (hv u hh))
  have hspeed (u : ℝ) (hh : u ∈ I) : a u ≤ (2 / k) * q u := by
    have hd := (coreBootstrap_clock_bounds hk (hr u hh).1 (hu u hh) (hw u hh)).1
    have H := mul_le_mul (hr u hh).1 hd (by norm_num : (0 : ℝ) ≤ 999 / 1000)
      (by linarith [(hr u hh).1] : 0 ≤ coreRadius (β u 0) (β u 2))
    have hrd : k / 2 ≤ coreRadius (β u 0) (β u 2) *
        coreClockFactor (coreRadius (β u 0) (β u 2)) (β u 1) (β u 3) := by nlinarith
    have hq : a u * (k / 2) ≤ q u := by
      have H' := mul_le_mul_of_nonneg_left hrd (ha u hh)
      dsimp [q]
      nlinarith
    calc
      a u = (2 / k) * (a u * (k / 2)) := by field_simp
      _ ≤ (2 / k) * q u := mul_le_mul_of_nonneg_left hq (by positivity)
  have H := image_sub_le_clock_sub_of_deriv_le hI hτ hz hspeed hs ht hst
  have hzs := abs_le.mp (coreBootstrap_angle_bound hk (hr s hs).2 (hv s hs))
  have hzt := abs_le.mp (coreBootstrap_angle_bound hk (hr t ht).2 (hv t ht))
  calc
    τ t - τ s ≤ (2 / k) * (z t - z s) := H
    _ ≤ (2 / k) * (2 * Real.log (4 * k)) :=
      mul_le_mul_of_nonneg_left (by dsimp [z]; linarith) (by positivity)
    _ = 4 * Real.log (4 * k) / k := by ring

theorem normalized_core_projective_duration {x : NormalizedState} {t₀ k s t : ℝ}
    (hc : stateConstraint x = 1) (hk : 6 ≤ k) (hs : t₀ ≤ s) (hst : s ≤ t)
    (hA : ∀ u ∈ Icc s t, 0 < normalizedProjectiveRate x t₀ u) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u)
    (∀ u ∈ Icc s t, 99 / 100 * k ≤ coreRadius (β u 0) (β u 2) ∧
      coreRadius (β u 0) (β u 2) ≤ 101 / 100 * k) →
    (∀ u ∈ Icc s t, 1 ≤ β u 2) →
    (∀ u ∈ Icc s t, 0 ≤ β u 1 ∧ β u 1 ≤ (1 / 10000) / k) →
    (∀ u ∈ Icc s t, 0 ≤ β u 3 ∧ β u 3 ≤ (1 / 10000) / k) →
    integralClock (normalizedProjectiveRate x t₀) s t ≤ 4 * Real.log (4 * k) / k := by
  intro β hr hv hu hw
  have hdom (u : ℝ) (hh : u ∈ Icc s t) : u ∈ normalizedMaxDomain x t₀ :=
    normalizedMaxDomain_contains_Ici_of_constraint hc t₀ (hs.trans hh.1)
  have hclock (u : ℝ) (hh : u ∈ Icc s t) :
      HasDerivAt (integralClock (normalizedProjectiveRate x t₀) s) (normalizedProjectiveRate x t₀ u) u :=
    (hasStrictDerivAt_integralClock (convex_normalizedMaxDomain x t₀) (isOpen_normalizedMaxDomain x t₀)
      (continuousOn_normalizedProjectiveRate x t₀) (hdom s ⟨le_rfl, hst⟩) (hdom u hh)).hasDerivAt
  have hsol (u : ℝ) (hh : u ∈ Icc s t) :
      HasDerivAt β (normalizedProjectiveRate x t₀ u • projectiveField (β u)) u := by
    have H := normalizedMaxCurve_forward_of_constraint hc (hs.trans hh.1)
    exact hasDerivAt_toProjectiveState_normalized H.1 (ne_of_gt (hA u hh)) H.2.1
  have H := scaled_core_projective_duration hk (convex_Icc s t) (fun u hh => (hA u hh).le)
    hsol hclock hr hv hu hw ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ hst
  simpa only [integralClock_initial, sub_zero] using H

end BianchiIX
