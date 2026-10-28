import BianchiIX.Algebra.StableBoundaryBounds
import BianchiIX.Analysis.ClockDecayIntegrals
import BianchiIX.Dynamics.ProjectiveState

noncomputable section

namespace BianchiIX

open Set MeasureTheory

/-- Signed walls on the actual boundary equations, in an arbitrary increasing clock. -/
theorem scaled_stable_boundary_decay {Y : ℝ → ProjectiveState} {a z : ℝ → ℝ}
    {s t c : ℝ} (hc : 2 ≤ c)
    (hY : ∀ r ∈ Icc s t, HasDerivAt Y (a r • projectiveField (Y r)) r)
    (hz : ∀ r ∈ Icc s t, HasDerivAt z ((c + 1) * a r) r)
    (ha : ∀ r ∈ Icc s t, 0 ≤ a r)
    (hv : ∀ r ∈ Icc s t, Y r 2 = 0)
    (hm : ∀ r ∈ Icc s t, |Y r 0 - c| ≤ 1 / 10)
    (hu : ∀ r ∈ Icc s t, |Y r 1| ≤ 1 / 100)
    (hw : ∀ r ∈ Icc s t, |Y r 3| ≤ 1 / 100) :
    ∀ r ∈ Icc s t,
      |Y r 1| ≤ |Y s 1| * Real.exp (-(c + 1) / 8 * (z r - z s)) ∧
      |Y r 3| ≤ |Y s 3| * Real.exp (-(1 / 4) * (z r - z s)) := by
  have hK : 0 < c + 1 := by linarith
  have hcoord (i : Fin 4) (r : ℝ) (hr : r ∈ Icc s t) := hasDerivAt_pi.mp (hY r hr) i
  have hU (r : ℝ) (hr : r ∈ Icc s t) :
      HasDerivAt (fun q => Y q 1)
        (((c + 1) * a r) * (stableStrongRate (Y r 0) (Y r 1) (Y r 3) / (c + 1) * Y r 1)) r := by
    convert! hcoord 1 r hr using 1
    change _ = a r * strongVelocity (Y r 0) (Y r 1) (Y r 2) (Y r 3)
    rw [hv r hr, (stable_boundary_field (Y r 0) (Y r 1) (Y r 3)).2.1]
    field_simp
  have hW (r : ℝ) (hr : r ∈ Icc s t) :
      HasDerivAt (fun q => Y q 3)
        (((c + 1) * a r) * (stableWeakRate (Y r 0) (Y r 1) (Y r 3) / (c + 1) * Y r 3)) r := by
    convert! hcoord 3 r hr using 1
    change _ = a r * weakVelocity (Y r 0) (Y r 1) (Y r 2) (Y r 3)
    rw [hv r hr, (stable_boundary_field (Y r 0) (Y r 1) (Y r 3)).2.2.2]
    field_simp
  have H := abs_le_exp_of_clock_damping hU hz (fun r hr => mul_nonneg hK.le (ha r hr))
    (fun r hr => by simpa only [neg_div] using (stable_boundary_rates hc (hm r hr) (hu r hr) (hw r hr)).1)
  have J := abs_le_exp_of_clock_damping hW hz (fun r hr => mul_nonneg hK.le (ha r hr))
    (fun r hr => (stable_boundary_rates hc (hm r hr) (hu r hr) (hw r hr)).2)
  intro r hr
  exact ⟨by simpa only [neg_div] using H r hr, J r hr⟩

theorem scaled_stable_boundary_drift {Y : ℝ → ProjectiveState} {a z : ℝ → ℝ}
    {s t c : ℝ} (hst : s ≤ t) (hc : 2 ≤ c)
    (hY : ∀ r ∈ Icc s t, HasDerivAt Y (a r • projectiveField (Y r)) r)
    (hz : ∀ r ∈ Icc s t, HasDerivAt z ((c + 1) * a r) r)
    (hac : ContinuousOn a (Icc s t)) (ha : ∀ r ∈ Icc s t, 0 ≤ a r)
    (hv : ∀ r ∈ Icc s t, Y r 2 = 0)
    (hm : ∀ r ∈ Icc s t, |Y r 0 - c| ≤ 1 / 10)
    (hu : ∀ r ∈ Icc s t, |Y r 1| ≤ 1 / 100)
    (hw : ∀ r ∈ Icc s t, |Y r 3| ≤ 1 / 100) :
    |Y t 0 - Y s 0| ≤ 8 * (|Y s 1| + |Y s 3|) ^ 2 / (c + 1) := by
  let K := c + 1
  let u := |Y s 1|
  let w := |Y s 3|
  let e := fun r => Real.exp (-K / 8 * (z r - z s))
  let f := fun r => Real.exp (-(1 / 2) * (z r - z s))
  have hK : 0 < K := by dsimp [K]; linarith
  have hu0 : 0 ≤ u := abs_nonneg _
  have hw0 : 0 ≤ w := abs_nonneg _
  have hdec := scaled_stable_boundary_decay hc hY hz ha hv hm hu hw
  have hzmono : MonotoneOn z (Icc s t) :=
    monotoneOn_of_deriv_nonneg (convex_Icc s t) (HasDerivAt.continuousOn hz)
      (fun r hr => (hz r (interior_subset hr)).differentiableAt.differentiableWithinAt)
      (fun r hr => by rw [(hz r (interior_subset hr)).deriv]; exact mul_nonneg hK.le (ha r (interior_subset hr)))
  have hz0 (r : ℝ) (hr : r ∈ Icc s t) : 0 ≤ z r - z s :=
    sub_nonneg.mpr (hzmono ⟨le_rfl, hst⟩ hr hr.1)
  have he1 (r : ℝ) (hr : r ∈ Icc s t) : e r ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by dsimp [K]; linarith) (hz0 r hr))
  have hbounds (r : ℝ) (hr : r ∈ Icc s t) :
      (Y r 1) ^ 2 + 2 * |Y r 1| * |Y r 3| + (Y r 3) ^ 2 / K ≤
        (u ^ 2 + 2 * u * w) * e r + (w ^ 2 / K) * f r := by
    have hU : |Y r 1| ≤ u * e r := (hdec r hr).1
    have hW : |Y r 3| ≤ w * Real.exp (-(1 / 4) * (z r - z s)) := (hdec r hr).2
    have hW0 : |Y r 3| ≤ w := hW.trans (mul_le_of_le_one_right hw0
      (Real.exp_le_one_iff.mpr (by nlinarith only [hz0 r hr])))
    have hU0 : |Y r 1| ≤ u := hU.trans (mul_le_of_le_one_right hu0 (he1 r hr))
    have hU2 := mul_le_mul hU0 hU (abs_nonneg _) hu0
    have hUW := mul_le_mul hU hW0 (abs_nonneg _) (by positivity : 0 ≤ u * e r)
    have hW2 := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ w * Real.exp (-(1 / 4) * (z r - z s)))).mpr hW
    have heq : (w * Real.exp (-(1 / 4) * (z r - z s))) ^ 2 = w ^ 2 * f r := by
      rw [mul_pow, pow_two (Real.exp _), ← Real.exp_add]
      congr 1
      dsimp [f]
      congr 1
      ring
    rw [sq_abs, heq] at hW2
    have hWdiv := div_le_div_of_nonneg_right hW2 hK.le
    rw [← pow_two, sq_abs] at hU2
    have H := add_le_add (add_le_add hU2 (mul_le_mul_of_nonneg_left hUW (by norm_num : (0 : ℝ) ≤ 2))) hWdiv
    convert! H using 1 <;> ring
  let B := fun r => (K * a r) * ((u ^ 2 + 2 * u * w) * e r + (w ^ 2 / K) * f r)
  have hzc := HasDerivAt.continuousOn hz
  have hec : ContinuousOn e (Icc s t) := Real.continuous_exp.comp_continuousOn
    ((hzc.sub continuousOn_const).const_mul (-K / 8))
  have hfc : ContinuousOn f (Icc s t) := Real.continuous_exp.comp_continuousOn
    ((hzc.sub continuousOn_const).const_mul (-(1 / 2)))
  have hBc : ContinuousOn B (Icc s t) := (hac.const_mul K).mul
    ((hec.const_mul (u ^ 2 + 2 * u * w)).add (hfc.const_mul (w ^ 2 / K)))
  have H := abs_sub_le_integral_bound hst (fun r hr => hasDerivAt_pi.mp (hY r hr) 0) hBc (fun r hr => ?_)
  · have hKe : ContinuousOn (fun r => (K * a r) * e r) (Icc s t) := (hac.const_mul K).mul hec
    have hKf : ContinuousOn (fun r => (K * a r) * f r) (Icc s t) := (hac.const_mul K).mul hfc
    have hBeq : B = fun r => (u ^ 2 + 2 * u * w) * ((K * a r) * e r) +
        (w ^ 2 / K) * ((K * a r) * f r) := by funext r; dsimp [B]; ring
    rw [hBeq, intervalIntegral.integral_add
      ((hKe.const_mul _).intervalIntegrable_of_Icc hst)
      ((hKf.const_mul _).intervalIntegrable_of_Icc hst),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at H
    have hIe : (∫ r in s..t, (K * a r) * e r) ≤ 1 / (K / 8) := by
      simpa only [e, neg_div] using integral_clock_exp_decay_le hst (by positivity : 0 < K / 8) hz (hac.const_mul K)
    have hIf : (∫ r in s..t, (K * a r) * f r) ≤ 1 / (1 / 2 : ℝ) :=
      integral_clock_exp_decay_le hst (by norm_num) hz (hac.const_mul K)
    have he := mul_le_mul_of_nonneg_left hIe (by positivity : 0 ≤ u ^ 2 + 2 * u * w)
    have hf := mul_le_mul_of_nonneg_left hIf (by positivity : 0 ≤ w ^ 2 / K)
    apply H.trans ((add_le_add he hf).trans ?_)
    change _ ≤ 8 * (u + w) ^ 2 / K
    have hid : (u ^ 2 + 2 * u * w) * (1 / (K / 8)) + (w ^ 2 / K) * (1 / (1 / 2 : ℝ)) =
        (8 * (u + w) ^ 2 - 6 * w ^ 2) / K := by
      field_simp
      ring
    rw [hid]
    exact (div_le_div_iff_of_pos_right hK).mpr (by nlinarith [sq_nonneg w])
  · change |a r * phaseVelocity (Y r 0) (Y r 1) (Y r 2) (Y r 3)| ≤ B r
    rw [hv r hr]
    have hid : a r * phaseVelocity (Y r 0) (Y r 1) 0 (Y r 3) =
        (K * a r) * (phaseVelocity (Y r 0) (Y r 1) 0 (Y r 3) / K) := by field_simp
    rw [hid, abs_mul, abs_of_nonneg (mul_nonneg hK.le (ha r hr))]
    exact mul_le_mul_of_nonneg_left
      ((stable_boundary_phase_bound hc (hm r hr)).trans (hbounds r hr)) (mul_nonneg hK.le (ha r hr))

end BianchiIX
