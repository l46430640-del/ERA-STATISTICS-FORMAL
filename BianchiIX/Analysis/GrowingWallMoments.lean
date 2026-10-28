import BianchiIX.Analysis.DissipativeMoments
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section

namespace BianchiIX

open Set MeasureTheory

theorem integral_growing_square {W : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hW : ∀ t ∈ Icc a b, HasDerivAt W (W t) t) :
    (∫ t in a..b, W t ^ 2) = (W b ^ 2 - W a ^ 2) / 2 ∧
      (∫ t in a..b, W t ^ 2) ≤ W b ^ 2 / 2 := by
  have hd (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt (fun s => W s ^ 2 / 2) (W t ^ 2) t := by
    convert! ((hW t ht).pow 2).div_const 2 using 1
    ring
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hd t (uIcc_of_le hab ▸ ht))
    (((HasDerivAt.continuousOn hW).pow 2).intervalIntegrable_of_Icc (μ := volume) hab)
  have hid : (∫ t in a..b, W t ^ 2) = (W b ^ 2 - W a ^ 2) / 2 := H.trans (by ring)
  exact ⟨hid, by rw [hid]; nlinarith only [sq_nonneg (W a)]⟩

/-- The residence length is controlled without taking a logarithm or dividing by a wall. -/
theorem growing_wall_duration_bound {W : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hW : ∀ t ∈ Icc a b, HasDerivAt W (W t) t)
    (hW0 : ∀ t ∈ Icc a b, 0 ≤ W t) (hWb : W b ≤ 1) :
    W a * (b - a) ≤ 1 := by
  have hmono : MonotoneOn W (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b) (HasDerivAt.continuousOn hW)
      (fun t ht => (hW t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(hW t (interior_subset ht)).deriv]
    exact hW0 t (interior_subset ht)
  have HI := intervalIntegral.integral_mono_on (μ := volume) hab (intervalIntegrable_const (c := W a))
    ((HasDerivAt.continuousOn hW).intervalIntegrable_of_Icc hab)
    (fun t ht => hmono ⟨le_rfl, hab⟩ ht ht.1)
  rw [intervalIntegral.integral_const, smul_eq_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hW t (uIcc_of_le hab ▸ ht))
      ((HasDerivAt.continuousOn hW).intervalIntegrable_of_Icc hab)] at HI
  nlinarith only [HI, hWb, hW0 a ⟨le_rfl, hab⟩]

theorem integral_dissipative_growing_product {U U' W : ℝ → ℝ} {μ a b : ℝ}
    (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hU : ∀ t ∈ Icc a b, HasDerivAt U (U' t) t)
    (hdecay : ∀ t ∈ Icc a b, U' t ≤ -(μ / 2) * U t)
    (hU0 : ∀ t ∈ Icc a b, 0 ≤ U t)
    (hW : ∀ t ∈ Icc a b, HasDerivAt W (W t) t)
    (hW0 : ∀ t ∈ Icc a b, 0 ≤ W t) :
    (∫ t in a..b, U t * W t) ≤ 4 * U a * W a / μ := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have H := integral_moments_le_of_linear_dissipation hab (by positivity : 0 < μ / 4)
    (fun t ht => (hU t ht).mul (hW t ht)) (fun t ht => ?_)
    (mul_nonneg (hU0 b ⟨hab, le_rfl⟩) (hW0 b ⟨hab, le_rfl⟩))
  · exact H.1.trans_eq (by simp only [Pi.mul_apply]; ring)
  · have Hd := mul_le_mul_of_nonneg_right (hdecay t ht) (hW0 t ht)
    have Hμ := mul_le_mul_of_nonneg_right hμ (mul_nonneg (hU0 t ht) (hW0 t ht))
    simp only [Pi.mul_apply]
    nlinarith only [Hd, Hμ]

/-- At mu = 4 the mixed product is only nonincreasing; the wall duration pays for its integral. -/
theorem integral_dissipative_growing_square {U U' W : ℝ → ℝ} {μ a b : ℝ}
    (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hU : ∀ t ∈ Icc a b, HasDerivAt U (U' t) t)
    (hdecay : ∀ t ∈ Icc a b, U' t ≤ -(μ / 2) * U t)
    (hU0 : ∀ t ∈ Icc a b, 0 ≤ U t)
    (hW : ∀ t ∈ Icc a b, HasDerivAt W (W t) t)
    (hW0 : ∀ t ∈ Icc a b, 0 ≤ W t) (hWb : W b ≤ 1) :
    (∫ t in a..b, U t * W t ^ 2) ≤ U a * W a := by
  have hd (t : ℝ) (ht : t ∈ Icc a b) := (hU t ht).mul ((hW t ht).pow 2)
  have hanti : AntitoneOn (fun t => U t * W t ^ 2) (Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b) (HasDerivAt.continuousOn hd)
      (fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(hd t (interior_subset ht)).deriv]
    have Hd := mul_le_mul_of_nonneg_right (hdecay t (interior_subset ht)) (sq_nonneg (W t))
    have Hμ := mul_le_mul_of_nonneg_right hμ (mul_nonneg (hU0 t (interior_subset ht)) (sq_nonneg (W t)))
    norm_num only [Pi.pow_apply, Nat.reduceSub, pow_one, Nat.cast_ofNat]
    nlinarith only [Hd, Hμ]
  have HI := intervalIntegral.integral_mono_on (μ := volume) hab
    ((HasDerivAt.continuousOn hd).intervalIntegrable_of_Icc hab)
    (intervalIntegrable_const (c := U a * W a ^ 2)) (fun t ht => hanti ⟨le_rfl, hab⟩ ht ht.1)
  rw [intervalIntegral.integral_const, smul_eq_mul] at HI
  have Hlen := growing_wall_duration_bound hab hW hW0 hWb
  have Hprod := mul_le_mul_of_nonneg_left Hlen (mul_nonneg (hU0 a ⟨le_rfl, hab⟩) (hW0 a ⟨le_rfl, hab⟩))
  exact HI.trans (by nlinarith only [Hprod])

end BianchiIX
