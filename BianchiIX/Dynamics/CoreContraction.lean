import BianchiIX.Algebra.CoreBounds
import BianchiIX.Dynamics.CoreAngleClock

noncomputable section

namespace BianchiIX

open Set

theorem le_exp_of_clock_deriv_le {I : Set ℝ} (hI : Convex ℝ I)
    {f f' z z' : ℝ → ℝ} {c s t : ℝ}
    (hf : ∀ u ∈ I, HasDerivAt f (f' u) u) (hz : ∀ u ∈ I, HasDerivAt z (z' u) u)
    (hbound : ∀ u ∈ I, f' u ≤ c * z' u * f u)
    (hs : s ∈ I) (ht : t ∈ I) (hst : s ≤ t) :
    f t ≤ f s * Real.exp (c * (z t - z s)) := by
  let g : ℝ → ℝ := fun u => f u * Real.exp (-c * z u)
  have hg (u : ℝ) (hu : u ∈ I) :
      HasDerivAt g ((f' u - c * z' u * f u) * Real.exp (-c * z u)) u := by
    convert! (hf u hu).mul ((hz u hu).const_mul (-c)).exp using 1
    ring
  have hmono : AntitoneOn g I := antitoneOn_of_deriv_nonpos hI
    (fun u hu => (hg u hu).continuousAt.continuousWithinAt)
    (fun u hu => (hg u (interior_subset hu)).differentiableAt.differentiableWithinAt)
    (fun u hu => by
      rw [(hg u (interior_subset hu)).deriv]
      exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hbound u (interior_subset hu))) (Real.exp_pos _).le)
  calc
    f t = g t * Real.exp (c * z t) := by
      dsimp [g]
      rw [mul_assoc, ← Real.exp_add]
      simp
    _ ≤ g s * Real.exp (c * z t) := mul_le_mul_of_nonneg_right (hmono hs ht hst) (Real.exp_pos _).le
    _ = f s * Real.exp (c * (z t - z s)) := by
      dsimp [g]
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

theorem le_exp_of_linear_deriv_le {I : Set ℝ} (hI : Convex ℝ I)
    {f f' : ℝ → ℝ} {c s t : ℝ}
    (hf : ∀ u ∈ I, HasDerivAt f (f' u) u) (hbound : ∀ u ∈ I, f' u ≤ c * f u)
    (hs : s ∈ I) (ht : t ∈ I) (hst : s ≤ t) :
    f t ≤ f s * Real.exp (c * (t - s)) := by
  exact le_exp_of_clock_deriv_le hI hf (fun u _ => hasDerivAt_id u)
    (fun u hu => by simpa only [mul_one] using hbound u hu) hs ht hst

theorem coreAngleField_strong_le {k z : ℝ} {y : CoreAngleState} (hk : 6 ≤ k)
    (hr : 99 / 100 * k ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ (1 / 10000) / k)
    (hw : 0 ≤ y 2 / (y 0 / Real.cosh z) ∧ y 2 / (y 0 / Real.cosh z) ≤ (1 / 10000) / k) :
    coreAngleField z y 1 ≤ (-k / 4) * y 1 := by
  have hr0 : 0 < y 0 := by linarith
  have hv : y 0 / Real.cosh z ≤ y 0 :=
    (div_le_iff₀ (Real.cosh_pos z)).mpr (le_mul_of_one_le_right hr0.le (Real.one_le_cosh z))
  have ha := coreBootstrap_strong_rate hk hr hv
    (show -1 ≤ -Real.tanh z by linarith [Real.tanh_lt_one z]) hu hw
  have hd := ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 999 / 1000)
    (coreBootstrap_clock_bounds hk hr hu hw).1)
  have hrne := ne_of_gt hr0
  have H := mul_le_mul_of_nonneg_left ha hu.1
  convert! H using 1
  · dsimp [coreAngleField]
    field_simp
    ring
  · ring

theorem coreAngleField_product_nonpos {k z : ℝ} {y : CoreAngleState} (hk : 6 ≤ k)
    (hr : 99 / 100 * k ≤ y 0) (hv : 1 ≤ y 0 / Real.cosh z)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ (1 / 10000) / k)
    (hw : 0 ≤ y 2 / (y 0 / Real.cosh z) ∧ y 2 / (y 0 / Real.cosh z) ≤ (1 / 10000) / k) :
    coreAngleField z y 2 ≤ 0 := by
  have hr0 : 0 < y 0 := by linarith
  have hv0 : 0 < y 0 / Real.cosh z := lt_of_lt_of_le zero_lt_one hv
  have hp : 0 ≤ y 2 := by
    have H := mul_nonneg hw.1 hv0.le
    simpa only [div_mul_cancel₀ _ (ne_of_gt hv0)] using H
  have hC := coreBootstrap_coupling_nonneg hk hv hu hw.1
  have hd := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 999 / 1000)
    (coreBootstrap_clock_bounds hk hr hu hw).1
  dsimp [coreAngleField]
  apply div_nonpos_of_nonpos_of_nonneg
  · exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hp) (by linarith)
  · exact (mul_pos hr0 hd).le

/-- Every completed bootstrap prefix has exponential strong-wall decay and decreasing VW. -/
theorem coreAngle_prefix_contraction {I : Set ℝ} (hI : Convex ℝ I)
    {Y : ℝ → CoreAngleState} {k z₀ s t : ℝ} (hk : 6 ≤ k)
    (hY : ∀ z ∈ I, HasDerivAt Y (coreAngleField (z + z₀) (Y z)) z)
    (hr : ∀ z ∈ I, 99 / 100 * k ≤ Y z 0)
    (hv : ∀ z ∈ I, 1 ≤ Y z 0 / Real.cosh (z + z₀))
    (hu : ∀ z ∈ I, 0 ≤ Y z 1 ∧ Y z 1 ≤ (1 / 10000) / k)
    (hw : ∀ z ∈ I, 0 ≤ Y z 2 / (Y z 0 / Real.cosh (z + z₀)) ∧
      Y z 2 / (Y z 0 / Real.cosh (z + z₀)) ≤ (1 / 10000) / k)
    (hs : s ∈ I) (ht : t ∈ I) (hst : s ≤ t) :
    Y t 1 ≤ Y s 1 * Real.exp (-k * (t - s) / 4) ∧ Y t 2 ≤ Y s 2 := by
  constructor
  · have H := le_exp_of_linear_deriv_le hI (c := -k / 4)
      (fun z hz => hasDerivAt_pi.mp (hY z hz) 1)
      (fun z hz => coreAngleField_strong_le hk (hr z hz) (hu z hz) (hw z hz)) hs ht hst
    convert! H using 1
    congr 2
    ring
  · have hanti : AntitoneOn (fun z => Y z 2) I := antitoneOn_of_deriv_nonpos hI
      (fun z hz => (hasDerivAt_pi.mp (hY z hz) 2).continuousAt.continuousWithinAt)
      (fun z hz => (hasDerivAt_pi.mp (hY z (interior_subset hz)) 2).differentiableAt.differentiableWithinAt)
      (fun z hz => by
        rw [(hasDerivAt_pi.mp (hY z (interior_subset hz)) 2).deriv]
        exact coreAngleField_product_nonpos hk (hr z (interior_subset hz)) (hv z (interior_subset hz))
          (hu z (interior_subset hz)) (hw z (interior_subset hz)))
    exact hanti hs ht hst

/-- The prefix estimates expressed directly in the physical projective state. -/
theorem scaled_core_prefix_contraction {β : ℝ → ProjectiveState} {a : ℝ → ℝ}
    {I : Set ℝ} {k s t : ℝ} (hk : 6 ≤ k) (hI : Convex ℝ I)
    (ha_pos : ∀ u ∈ I, 0 < a u)
    (hβ : ∀ u ∈ I, HasDerivAt β (a u • projectiveField (β u)) u)
    (hr : ∀ u ∈ I, 99 / 100 * k ≤ coreRadius (β u 0) (β u 2))
    (hv : ∀ u ∈ I, 1 ≤ β u 2)
    (hu : ∀ z ∈ I, 0 ≤ β z 1 ∧ β z 1 ≤ (1 / 10000) / k)
    (hw : ∀ z ∈ I, 0 ≤ β z 3 ∧ β z 3 ≤ (1 / 10000) / k)
    (hs : s ∈ I) (ht : t ∈ I) (hst : s ≤ t) :
    β t 1 ≤ β s 1 * Real.exp (-k * (coreAngle (β t 0) (β t 2) - coreAngle (β s 0) (β s 2)) / 4) ∧
      β t 2 * β t 3 ≤ β s 2 * β s 3 := by
  have hvpos : ∀ u ∈ I, 0 < β u 2 := fun u hh => lt_of_lt_of_le zero_lt_one (hv u hh)
  have hd : ∀ u ∈ I, 0 < coreClockFactor (coreRadius (β u 0) (β u 2)) (β u 1) (β u 3) :=
    fun u hh => lt_of_lt_of_le (by norm_num : (0 : ℝ) < 999 / 1000)
      (coreBootstrap_clock_bounds hk (hr u hh) (hu u hh) (hw u hh)).1
  let q : ℝ → ℝ := fun u => a u * coreRadius (β u 0) (β u 2) *
    coreClockFactor (coreRadius (β u 0) (β u 2)) (β u 1) (β u 3)
  let F : ℝ → CoreAngleState := fun u => coreAngleField (coreAngle (β u 0) (β u 2)) (toCoreAngleState (β u))
  have hq : ∀ u ∈ I, 0 < q u := fun u hh =>
    mul_pos (mul_pos (ha_pos u hh) (coreRadius_pos (hvpos u hh))) (hd u hh)
  have hstate (u : ℝ) (hh : u ∈ I) :
      HasDerivAt (fun v => toCoreAngleState (β v)) (q u • F u) u :=
    hasDerivAt_toCoreAngleState_scaled (hβ u hh) (hvpos u hh) (ne_of_gt (hd u hh))
  have hF (u : ℝ) (hh : u ∈ I) : F u 1 ≤ (-k / 4) * β u 1 ∧ F u 2 ≤ 0 := by
    have hV : toCoreAngleState (β u) 0 / Real.cosh (coreAngle (β u 0) (β u 2)) = β u 2 :=
      (coreAngle_coordinates (hvpos u hh)).1
    have hW : toCoreAngleState (β u) 2 /
        (toCoreAngleState (β u) 0 / Real.cosh (coreAngle (β u 0) (β u 2))) = β u 3 := by
      rw [hV]
      change β u 2 * β u 3 / β u 2 = _
      field_simp [ne_of_gt (hvpos u hh)]
    have hw' : 0 ≤ toCoreAngleState (β u) 2 /
        (toCoreAngleState (β u) 0 / Real.cosh (coreAngle (β u 0) (β u 2))) ∧
        toCoreAngleState (β u) 2 /
        (toCoreAngleState (β u) 0 / Real.cosh (coreAngle (β u 0) (β u 2))) ≤ (1 / 10000) / k := by
      rw [hW]
      exact hw u hh
    exact ⟨coreAngleField_strong_le hk (hr u hh) (hu u hh) hw',
      coreAngleField_product_nonpos hk (hr u hh) (by rw [hV]; exact hv u hh) (hu u hh) hw'⟩
  constructor
  · have H := le_exp_of_clock_deriv_le hI (c := -k / 4)
      (fun u hh => hasDerivAt_pi.mp (hstate u hh) 1)
      (fun u hh => hasDerivAt_coreAngle_scaled (hβ u hh) (hvpos u hh))
      (fun u hh => (mul_le_mul_of_nonneg_left (hF u hh).1 (hq u hh).le).trans_eq
        (by dsimp [q, toCoreAngleState]; ring)) hs ht hst
    convert! H using 1
    congr 2
    ring
  · have hanti : AntitoneOn (fun u => toCoreAngleState (β u) 2) I := antitoneOn_of_deriv_nonpos hI
      (fun u hh => (hasDerivAt_pi.mp (hstate u hh) 2).continuousAt.continuousWithinAt)
      (fun u hh => (hasDerivAt_pi.mp (hstate u (interior_subset hh)) 2).differentiableAt.differentiableWithinAt)
      (fun u hh => by
        rw [(hasDerivAt_pi.mp (hstate u (interior_subset hh)) 2).deriv]
        exact mul_nonpos_of_nonneg_of_nonpos (hq u (interior_subset hh)).le (hF u (interior_subset hh)).2)
    exact hanti hs ht hst

theorem normalized_core_prefix_contraction {x : NormalizedState} {t₀ k s t : ℝ} {I : Set ℝ}
    (hk : 6 ≤ k) (hI : Convex ℝ I)
    (hdom : I ⊆ normalizedMaxDomain x t₀) (hc : stateConstraint x = 1)
    (hA : ∀ u ∈ I, 0 < 1 + normalizedMaxCurve x t₀ u 0)
    (hs : s ∈ I) (ht : t ∈ I) (hst : s ≤ t) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u)
    (∀ u ∈ I, 99 / 100 * k ≤ coreRadius (β u 0) (β u 2)) →
    (∀ u ∈ I, 1 ≤ β u 2) →
    (∀ u ∈ I, 0 ≤ β u 1 ∧ β u 1 ≤ (1 / 10000) / k) →
    (∀ u ∈ I, 0 ≤ β u 3 ∧ β u 3 ≤ (1 / 10000) / k) →
    β t 1 ≤ β s 1 * Real.exp (-k * (coreAngle (β t 0) (β t 2) - coreAngle (β s 0) (β s 2)) / 4) ∧
      β t 2 * β t 3 ≤ β s 2 * β s 3 := by
  intro β hr hv hu hw
  apply scaled_core_prefix_contraction (a := fun u => 1 + normalizedMaxCurve x t₀ u 0)
    hk hI hA ?_ hr hv hu hw hs ht hst
  intro u hu
  exact hasDerivAt_toProjectiveState_normalized (hasDerivAt_normalizedMaxCurve (hdom hu))
    (ne_of_gt (hA u hu)) ((normalizedMaxCurve_constraint (hdom hu)).trans hc)

end BianchiIX
