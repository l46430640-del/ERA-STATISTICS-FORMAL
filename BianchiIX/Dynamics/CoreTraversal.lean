import BianchiIX.Dynamics.CoreCrossings
import BianchiIX.Dynamics.CoreContraction
import BianchiIX.Dynamics.ProjectiveClock

noncomputable section

namespace BianchiIX

open Set

theorem image_sub_le_clock_sub_of_deriv_le {I : Set ℝ} (hI : Convex ℝ I)
    {f f' z z' : ℝ → ℝ} {C s t : ℝ}
    (hf : ∀ u ∈ I, HasDerivAt f (f' u) u) (hz : ∀ u ∈ I, HasDerivAt z (z' u) u)
    (hbound : ∀ u ∈ I, f' u ≤ C * z' u)
    (hs : s ∈ I) (ht : t ∈ I) (hst : s ≤ t) :
    f t - f s ≤ C * (z t - z s) := by
  have hd (u : ℝ) (hh : u ∈ I) := (hf u hh).sub ((hz u hh).const_mul C)
  have hanti := antitoneOn_of_deriv_nonpos hI (HasDerivAt.continuousOn hd)
    (fun u hh => (hd u (interior_subset hh)).differentiableAt.differentiableWithinAt)
    (fun u hh => by rw [(hd u (interior_subset hh)).deriv]; linarith [hbound u (interior_subset hh)])
  have H := hanti hs ht hst
  dsimp at H
  linarith

/-- Quantitative amplitude decay uses the actual accumulated projective clock. -/
theorem scaled_core_amplitude_decay {β : ℝ → ProjectiveState} {a τ : ℝ → ℝ} {I : Set ℝ}
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
    β t 1 ≤ β s 1 * Real.exp ((-k ^ 2 / 10) * (τ t - τ s)) ∧
      β t 2 * β t 3 ≤ (β s 2 * β s 3) * Real.exp (-2 * (τ t - τ s)) := by
  constructor
  · apply le_exp_of_clock_deriv_le hI (fun u hh => hasDerivAt_pi.mp (hβ u hh) 1) hτ ?_ hs ht hst
    intro u hh
    have H := mul_le_mul_of_nonneg_left (coreBootstrap_strong_velocity hk (hr u hh) (hu u hh) (hw u hh)) (ha u hh)
    change a u * strongVelocity (β u 0) (β u 1) (β u 2) (β u 3) ≤ _
    convert! H using 1
    ring
  · have hP (u : ℝ) (hh : u ∈ I) :
        HasDerivAt (fun v => β v 2 * β v 3)
          (a u * (-2 * (1 + coupling (β u 1) (β u 2) (β u 3)) * (β u 2 * β u 3))) u := by
      have H := (hasDerivAt_pi.mp (hβ u hh) 2).mul (hasDerivAt_pi.mp (hβ u hh) 3)
      convert! H using 1
      change _ = a u * activeVelocity (β u 0) (β u 1) (β u 2) (β u 3) * β u 3 +
        β u 2 * (a u * weakVelocity (β u 0) (β u 1) (β u 2) (β u 3))
      rw [show a u * activeVelocity (β u 0) (β u 1) (β u 2) (β u 3) * β u 3 +
          β u 2 * (a u * weakVelocity (β u 0) (β u 1) (β u 2) (β u 3)) =
          a u * (activeVelocity (β u 0) (β u 1) (β u 2) (β u 3) * β u 3 +
            β u 2 * weakVelocity (β u 0) (β u 1) (β u 2) (β u 3)) by ring,
        weak_product_directional]
    apply le_exp_of_clock_deriv_le hI hP hτ ?_ hs ht hst
    intro u hh
    have hC := coreBootstrap_coupling_nonneg hk (hv u hh) (hu u hh) (hw u hh).1
    have hprod : 0 ≤ a u * coupling (β u 1) (β u 2) (β u 3) * (β u 2 * β u 3) :=
      mul_nonneg (mul_nonneg (ha u hh) hC) (mul_nonneg (by linarith [hv u hh]) (hw u hh).1)
    nlinarith

/-- The phase displacement forces a positive projective duration and both exit contractions. -/
theorem scaled_core_exit_contraction {β : ℝ → ProjectiveState} {a τ : ℝ → ℝ}
    {k s t : ℝ} (hk : 6 ≤ k) (hst : s < t)
    (ha : ∀ u ∈ Icc s t, 0 < a u)
    (hβ : ∀ u ∈ Icc s t, HasDerivAt β (a u • projectiveField (β u)) u)
    (hτ : ∀ u ∈ Icc s t, HasDerivAt τ (a u) u)
    (hr : ∀ u ∈ Icc s t, 99 / 100 * k ≤ coreRadius (β u 0) (β u 2) ∧
      coreRadius (β u 0) (β u 2) ≤ 101 / 100 * k)
    (hv : ∀ u ∈ Icc s t, 1 ≤ β u 2)
    (hu : ∀ u ∈ Icc s t, 0 ≤ β u 1 ∧ β u 1 ≤ (1 / 10000) / k)
    (hw : ∀ u ∈ Icc s t, 0 ≤ β u 3 ∧ β u 3 ≤ (1 / 10000) / k)
    (hvs : β s 2 = 1) (hvt : β t 2 = 1) (hms : 1 ≤ β s 0) :
    1 / (4 * k) ≤ τ t - τ s ∧
      β t 1 ≤ Real.exp (-k / 40) * β s 1 ∧
      β t 3 ≤ Real.exp (-1 / (2 * k)) * β s 3 := by
  have hs : s ∈ Icc s t := ⟨le_rfl, hst.le⟩
  have ht : t ∈ Icc s t := ⟨hst.le, le_rfl⟩
  have hk0 : 0 < k := by linarith
  have hout := scaled_core_return_downward hk hst (ha t ht) (hβ t ht) hvt
    (fun u hh => hv u ⟨hh.1.le, hh.2.le⟩) (hr t ht).1 (hu t ht) (hw t ht)
  have hgs := core_section_phase_gap hk (by simpa only [hvs] using (hr s hs).1)
  have hgt := core_section_phase_gap hk (by simpa only [hvt] using (hr t ht).1)
  rw [abs_of_nonneg (sub_nonneg.mpr hms)] at hgs
  rw [abs_of_neg (by linarith [hout.1] : β t 0 - 1 < 0)] at hgt
  have hspeed (u : ℝ) (hh : u ∈ Icc s t) : -phaseVelocity (β u 0) (β u 1) (β u 2) (β u 3) ≤ 4 * k ^ 2 := by
    have H := (coreBootstrap_phase_velocity hk (coreBootstrap_phase_bound hk (hr u hh).2)
      (hv u hh) (hu u hh) (hw u hh)).2
    have hvhi : β u 2 ≤ 101 / 100 * k :=
      (le_abs_self _).trans ((coreRadius_component_bounds _ _).2.trans (hr u hh).2)
    have hv2 := (sq_le_sq₀ (by linarith [hv u hh]) (by positivity : 0 ≤ 101 / 100 * k)).mpr hvhi
    nlinarith [sq_nonneg k]
  have hdisp := image_sub_le_clock_sub_of_deriv_le (convex_Icc s t)
    (fun u hh => (hasDerivAt_pi.mp (hβ u hh) 0).neg) hτ
    (C := 4 * k ^ 2) (fun u hh => by
      have H := mul_le_mul_of_nonneg_left (hspeed u hh) (ha u hh).le
      change -(a u * phaseVelocity (β u 0) (β u 1) (β u 2) (β u 3)) ≤ _
      nlinarith) hs ht hst.le
  have htime : 1 / (4 * k) ≤ τ t - τ s := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * k)).mpr
    have H : k * 1 ≤ k * ((τ t - τ s) * (4 * k)) := by dsimp at hdisp; nlinarith
    exact le_of_mul_le_mul_left H hk0
  obtain ⟨hU, hP⟩ := scaled_core_amplitude_decay hk (convex_Icc s t) (fun u hh => (ha u hh).le)
    hβ hτ hr hv hu hw hs ht hst.le
  have hUexp : (-k ^ 2 / 10) * (τ t - τ s) ≤ -k / 40 := by
    calc
      _ ≤ (-k ^ 2 / 10) * (1 / (4 * k)) := mul_le_mul_of_nonpos_left htime (by nlinarith [sq_nonneg k])
      _ = _ := by field_simp; ring
  have hPexp : -2 * (τ t - τ s) ≤ -1 / (2 * k) := by
    calc
      _ ≤ -2 * (1 / (4 * k)) := mul_le_mul_of_nonpos_left htime (by norm_num)
      _ = _ := by field_simp; ring
  rw [hvs, hvt, one_mul, one_mul] at hP
  refine ⟨htime, ?_, ?_⟩
  · exact hU.trans ((mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hUexp) (hu s hs).1).trans_eq (mul_comm _ _))
  · exact hP.trans ((mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hPexp) (hw s hs).1).trans_eq (mul_comm _ _))

/-- The exit estimates for the actual normalized Einstein flow, with its clock constructed by integration. -/
theorem normalized_core_exit_contraction {x : NormalizedState} {t₀ k s t : ℝ}
    (hc : stateConstraint x = 1) (hk : 6 ≤ k) (hs : t₀ ≤ s) (hst : s < t)
    (hA : ∀ u ∈ Icc s t, 0 < normalizedProjectiveRate x t₀ u) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u)
    (∀ u ∈ Icc s t, 99 / 100 * k ≤ coreRadius (β u 0) (β u 2) ∧
      coreRadius (β u 0) (β u 2) ≤ 101 / 100 * k) →
    (∀ u ∈ Icc s t, 1 ≤ β u 2) →
    (∀ u ∈ Icc s t, 0 ≤ β u 1 ∧ β u 1 ≤ (1 / 10000) / k) →
    (∀ u ∈ Icc s t, 0 ≤ β u 3 ∧ β u 3 ≤ (1 / 10000) / k) →
    β s 2 = 1 → β t 2 = 1 → 1 ≤ β s 0 →
    1 / (4 * k) ≤ integralClock (normalizedProjectiveRate x t₀) s t ∧
      β t 1 ≤ Real.exp (-k / 40) * β s 1 ∧
      β t 3 ≤ Real.exp (-1 / (2 * k)) * β s 3 := by
  intro β hr hv hu hw hvs hvt hms
  have hdom (u : ℝ) (hh : u ∈ Icc s t) : u ∈ normalizedMaxDomain x t₀ :=
    normalizedMaxDomain_contains_Ici_of_constraint hc t₀ (hs.trans hh.1)
  have hclock (u : ℝ) (hh : u ∈ Icc s t) :
      HasDerivAt (integralClock (normalizedProjectiveRate x t₀) s) (normalizedProjectiveRate x t₀ u) u :=
    (hasStrictDerivAt_integralClock (convex_normalizedMaxDomain x t₀) (isOpen_normalizedMaxDomain x t₀)
      (continuousOn_normalizedProjectiveRate x t₀) (hdom s ⟨le_rfl, hst.le⟩) (hdom u hh)).hasDerivAt
  have hsol (u : ℝ) (hh : u ∈ Icc s t) :
      HasDerivAt β (normalizedProjectiveRate x t₀ u • projectiveField (β u)) u := by
    have H := normalizedMaxCurve_forward_of_constraint hc (hs.trans hh.1)
    exact hasDerivAt_toProjectiveState_normalized H.1 (ne_of_gt (hA u hh)) H.2.1
  have H := scaled_core_exit_contraction hk hst hA hsol hclock hr hv hu hw hvs hvt hms
  simpa only [integralClock_initial, sub_zero] using H

end BianchiIX
