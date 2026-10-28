import BianchiIX.Analysis.NormClockForcing
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.ProjIcc

noncomputable section

namespace BianchiIX

open Set MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A nondecreasing forcing budget gives a dimension-free variable-rate estimate. -/
theorem norm_le_exp_of_norm_deriv_budget {f f' : ℝ → E} {z z' B B' : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hz : ∀ t ∈ Icc a b, HasDerivAt z (z' t) t)
    (hB : ∀ t ∈ Icc a b, HasDerivAt B (B' t) t)
    (hB0 : ∀ t ∈ Icc a b, 0 ≤ B t) (hB' : ∀ t ∈ Icc a b, 0 ≤ B' t)
    (hinit : ‖f a‖ ≤ B a) (hclock : ∀ t ∈ Icc a b, z a ≤ z t)
    (hbound : ∀ t ∈ Icc a b, ‖f' t‖ ≤ z' t * ‖f t‖ + B' t) :
    ∀ t ∈ Icc a b, ‖f t‖ ≤ B t * Real.exp (z t - z a) := by
  intro t ht
  have H : ∀ δ ∈ Ioi (0 : ℝ),
      ‖f t‖ ≤ (B t + δ) * Real.exp (z t - z a + δ * (t - a)) := by
    intro δ hδ
    change 0 < δ at hδ
    let R := fun s => (B s + δ) * Real.exp (z s - z a + δ * (s - a))
    let R' := fun s => B' s * Real.exp (z s - z a + δ * (s - a)) + (z' s + δ) * R s
    have hR (s : ℝ) (hs : s ∈ Icc a b) : HasDerivAt R (R' s) s := by
      convert! ((hB s hs).add_const δ).mul
        ((((hz s hs).sub_const (z a)).add (((hasDerivAt_id' s).sub_const a).const_mul δ)).exp) using 1
      dsimp only [R, R', Pi.add_apply, Pi.sub_apply]
      ring
    apply image_norm_le_of_norm_deriv_right_lt_deriv_boundary' (HasDerivAt.continuousOn hf)
      (fun s hs => (hf s (Ico_subset_Icc_self hs)).hasDerivWithinAt) (B' := R')
      (by dsimp [R]; simp only [sub_self, mul_zero, add_zero, Real.exp_zero, mul_one]; linarith only [hinit, hδ])
      (HasDerivAt.continuousOn hR) (fun s hs => (hR s (Ico_subset_Icc_self hs)).hasDerivWithinAt) ?_ ht
    intro s hs heq
    have hb := hbound s (Ico_subset_Icc_self hs)
    rw [heq] at hb
    have hpos : 0 < R s := mul_pos (by linarith only [hB0 s (Ico_subset_Icc_self hs), hδ]) (Real.exp_pos _)
    have he : 1 ≤ Real.exp (z s - z a + δ * (s - a)) := Real.one_le_exp_iff.mpr
      (add_nonneg (sub_nonneg.mpr (hclock s (Ico_subset_Icc_self hs)))
        (mul_nonneg hδ.le (sub_nonneg.mpr hs.1)))
    have hforce := mul_le_mul_of_nonneg_left he (hB' s (Ico_subset_Icc_self hs))
    dsimp only [R']
    nlinarith only [hb, mul_pos hδ hpos, hforce]
  have hcont : ContinuousWithinAt
      (fun δ : ℝ => (B t + δ) * Real.exp (z t - z a + δ * (t - a))) (Ioi 0) 0 := by fun_prop
  have H0 := continuousWithinAt_const.closure_le
    (by simp only [closure_Ioi, self_mem_Ici] : (0 : ℝ) ∈ closure (Ioi 0)) hcont H
  simpa only [add_zero, zero_mul] using H0

/-- The exponential depends only on the integrated growth rate, with an integrated forcing cost. -/
theorem norm_le_exp_integral_of_norm_deriv {f f' : ℝ → E} {k e : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hk : ContinuousOn k (Icc a b)) (he : ContinuousOn e (Icc a b))
    (hk0 : ∀ t ∈ Icc a b, 0 ≤ k t) (he0 : ∀ t ∈ Icc a b, 0 ≤ e t)
    (hbound : ∀ t ∈ Icc a b, ‖f' t‖ ≤ k t * ‖f t‖ + e t) :
    ‖f b‖ ≤ (‖f a‖ + ∫ t in a..b, e t) * Real.exp (∫ t in a..b, k t) := by
  let K : ℝ → ℝ := fun t => k (projIcc a b hab t)
  let R : ℝ → ℝ := fun t => e (projIcc a b hab t)
  let z : ℝ → ℝ := fun t => ∫ u in a..t, K u
  let B : ℝ → ℝ := fun t => ‖f a‖ + ∫ u in a..t, R u
  have hK : Continuous K := hk.domRestrict.comp continuous_projIcc
  have hR : Continuous R := he.domRestrict.comp continuous_projIcc
  have hKe (t : ℝ) (ht : t ∈ Icc a b) : K t = k t := by simp only [K, projIcc_of_mem hab ht]
  have hRe (t : ℝ) (ht : t ∈ Icc a b) : R t = e t := by simp only [R, projIcc_of_mem hab ht]
  have hz (t : ℝ) : HasDerivAt z (K t) t := intervalIntegral.integral_hasDerivAt_right
    (hK.intervalIntegrable _ _) hK.stronglyMeasurable.stronglyMeasurableAtFilter hK.continuousAt
  have hB (t : ℝ) : HasDerivAt B (R t) t := (intervalIntegral.integral_hasDerivAt_right
    (hR.intervalIntegrable _ _) hR.stronglyMeasurable.stronglyMeasurableAtFilter hR.continuousAt).const_add _
  have hBn (t : ℝ) (ht : t ∈ Icc a b) : 0 ≤ B t := add_nonneg (norm_nonneg _)
    (intervalIntegral.integral_nonneg ht.1 (fun u hu => by rw [hRe u ⟨hu.1, hu.2.trans ht.2⟩]; exact he0 u ⟨hu.1, hu.2.trans ht.2⟩))
  have H := norm_le_exp_of_norm_deriv_budget hf (fun t _ => hz t) (fun t _ => hB t) hBn
    (fun t ht => by rw [hRe t ht]; exact he0 t ht) (by simp [B])
    (fun t ht => by
      simp only [z, intervalIntegral.integral_same]
      exact intervalIntegral.integral_nonneg ht.1 (fun u hu => by
        rw [hKe u ⟨hu.1, hu.2.trans ht.2⟩]; exact hk0 u ⟨hu.1, hu.2.trans ht.2⟩))
    (fun t ht => by rw [hKe t ht, hRe t ht]; exact hbound t ht) b ⟨hab, le_rfl⟩
  have HK : (∫ t in a..b, K t) = ∫ t in a..b, k t := intervalIntegral.integral_congr
    (fun t ht => hKe t (uIcc_of_le hab ▸ ht))
  have HR : (∫ t in a..b, R t) = ∫ t in a..b, e t := intervalIntegral.integral_congr
    (fun t ht => hRe t (uIcc_of_le hab ▸ ht))
  simpa only [B, z, intervalIntegral.integral_same, sub_zero, HK, HR] using H

end BianchiIX
