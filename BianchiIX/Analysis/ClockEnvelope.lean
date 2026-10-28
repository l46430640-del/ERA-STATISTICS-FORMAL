import BianchiIX.Analysis.ForcedDecayIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

noncomputable section

namespace BianchiIX

open Set MeasureTheory

theorem integral_clock_le_envelope {f z rate G : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hz : ∀ t ∈ Icc a b, HasDerivAt z (rate t) t)
    (hrate : ContinuousOn rate (Icc a b)) (hpos : ∀ t ∈ Icc a b, 0 ≤ rate t)
    (hf : ContinuousOn f (Icc a b)) (hG : Continuous G)
    (hbound : ∀ t ∈ Icc a b, f t ≤ G (z t)) :
    (∫ t in a..b, f t * rate t) ≤ ∫ s in z a..z b, G s := by
  have hzc : ContinuousOn z (Icc a b) := fun t ht => (hz t ht).continuousAt.continuousWithinAt
  have H := intervalIntegral.integral_mono_on (μ := volume) hab
    ((hf.mul hrate).intervalIntegrable_of_Icc hab)
    (((hG.comp_continuousOn hzc).mul hrate).intervalIntegrable_of_Icc hab)
    (fun t ht => mul_le_mul_of_nonneg_right (hbound t ht) (hpos t ht))
  have heq := intervalIntegral.integral_comp_mul_deriv
    (show ∀ t ∈ uIcc a b, HasDerivAt z (rate t) t by simpa only [uIcc_of_le hab] using hz)
    (show ContinuousOn rate (uIcc a b) by simpa only [uIcc_of_le hab] using hrate) hG
  simp only [Pi.mul_apply, Function.comp_apply] at H
  exact H.trans_eq (by simpa only [Function.comp_apply] using heq)

/-- Formula (B.36) as integrals in original time against the exact angular rate. -/
theorem core_clock_forced_variation_integrals {x z rate : ℝ → ℝ} {k a b U Q : ℝ}
    (hk : 6 ≤ k) (hab : a ≤ b) (hU : 0 ≤ U) (hQ : 0 ≤ Q)
    (hx : ContinuousOn x (Icc a b)) (hz : ∀ t ∈ Icc a b, HasDerivAt z (rate t) t)
    (hrate : ContinuousOn rate (Icc a b)) (hpos : ∀ t ∈ Icc a b, 0 ≤ rate t)
    (hentry : Real.cosh (z a) = k)
    (hbound : ∀ t ∈ Icc a b, |x t| ≤ Real.exp (-k * (z t - z a) / 4) *
      (|x a| + 3 * k * U * Q * (z t - z a))) :
    (∫ t in a..b, (|x t| / Real.cosh (z t)) * rate t) ≤ (12 * |x a| + 432 * U * Q) / k ^ 2 ∧
      (∫ t in a..b, |x t| * rate t) ≤ (4 * |x a| + 48 * U * Q) / k := by
  let e := fun t => z t - z a
  let E := fun s => Real.exp (-k * s / 4) * (|x a| + 3 * k * U * Q * s)
  have hE : Continuous E := by dsimp [E]; fun_prop
  have hE0 : E 0 = |x a| := by simp [E]
  have hzc : ContinuousOn z (Icc a b) := fun t ht => (hz t ht).continuousAt.continuousWithinAt
  have hmono : MonotoneOn z (Icc a b) := monotoneOn_of_deriv_nonneg (convex_Icc a b) hzc
    (fun t ht => (hz t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    (fun t ht => by rw [(hz t (interior_subset ht)).deriv]; exact hpos t (interior_subset ht))
  have hL : 0 ≤ e b := sub_nonneg.mpr (hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab)
  have hEpos (s : ℝ) (hs : 0 ≤ s) : 0 ≤ E s := by
    dsimp [E]
    have hk0 : 0 ≤ k := by linarith only [hk]
    positivity
  have H := core_forced_variation_integrals (x := E) hk hL hU hQ hE.continuousOn hentry
    (fun s hs => by rw [abs_of_nonneg (hEpos s hs.1), hE0, abs_of_nonneg (abs_nonneg _)])
  rw [hE0, abs_of_nonneg (abs_nonneg _)] at H
  have he : ∀ t ∈ Icc a b, HasDerivAt e (rate t) t := fun t ht => (hz t ht).sub_const (z a)
  have he0 : e a = 0 := sub_self _
  constructor
  · have hweight : ContinuousOn (fun t => |x t| / Real.cosh (z t)) (Icc a b) :=
      hx.abs.div (Real.continuous_cosh.comp_continuousOn hzc) (fun t _ => ne_of_gt (Real.cosh_pos _))
    have hEnv : Continuous (fun s => E s / Real.cosh (z a + s)) :=
      hE.div (by fun_prop) (fun _ => ne_of_gt (Real.cosh_pos _))
    have hle := integral_clock_le_envelope hab he hrate hpos hweight hEnv (fun t ht => by
      change |x t| / Real.cosh (z t) ≤ E (z t - z a) / Real.cosh (z a + (z t - z a))
      rw [show z a + (z t - z a) = z t by ring]
      exact div_le_div_of_nonneg_right (hbound t ht) (Real.cosh_pos _).le)
    rw [he0] at hle
    apply hle.trans
    have heq : (∫ s in 0..e b, E s / Real.cosh (z a + s)) =
        ∫ s in 0..e b, |E s| / Real.cosh (z a + s) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hL] at hs
      change E s / Real.cosh (z a + s) = |E s| / Real.cosh (z a + s)
      rw [abs_of_nonneg (hEpos s hs.1)]
    rw [heq]
    exact H.1
  · have hle := integral_clock_le_envelope hab he hrate hpos hx.abs hE hbound
    rw [he0] at hle
    apply hle.trans
    have heq : (∫ s in 0..e b, E s) = ∫ s in 0..e b, |E s| := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hL] at hs
      change E s = |E s|
      rw [abs_of_nonneg (hEpos s hs.1)]
    rw [heq]
    exact H.2

end BianchiIX
