import BianchiIX.Measure.ClippedLogIntegral
import Mathlib.Topology.Order.LeftRight

noncomputable section

namespace BianchiIX

open Set MeasureTheory Filter
open scoped Topology

theorem tendsto_mul_log_sq_zero :
    Tendsto (fun x : ℝ => x * (Real.log x) ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have H : Tendsto (fun x : ℝ => (Real.log x * x ^ ((1 : ℝ) / 2)) ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_log_mul_rpow_nhdsGT_zero (by norm_num : (0 : ℝ) < 1 / 2)).pow 2
  apply H.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [mul_pow, ← Real.sqrt_eq_rpow, Real.sq_sqrt hx.le]
  ring

theorem continuousOn_mul_log_sq :
    ContinuousOn (fun x : ℝ => x * (Real.log x) ^ 2) (Ici 0) := by
  intro x hx
  by_cases h : x = 0
  · subst x
    apply continuousWithinAt_Ioi_iff_Ici.mp
    simpa only [ContinuousWithinAt, zero_mul] using tendsto_mul_log_sq_zero
  · exact (continuousAt_id.mul ((Real.continuousAt_log h).pow 2)).continuousWithinAt

def logSquarePrimitive (A x : ℝ) : ℝ :=
  x * ((A - Real.log x) ^ 2 + 2 * (A - Real.log x) + 2)

theorem continuousOn_logSquarePrimitive (A : ℝ) :
    ContinuousOn (logSquarePrimitive A) (Ici 0) := by
  convert! (continuousOn_mul_log_sq.add
    (Real.continuous_mul_log.continuousOn.const_mul (-2 * A - 2))).add
    (continuousOn_id.const_mul (A ^ 2 + 2 * A + 2)) using 1
  ext x
  dsimp [logSquarePrimitive]
  ring

theorem hasDerivAt_logSquarePrimitive (A : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (logSquarePrimitive A) ((A - Real.log x) ^ 2) x := by
  have H := (hasDerivAt_id x).mul
    ((((hasDerivAt_const x A).sub (Real.hasDerivAt_log hx)).pow 2).add
      (((hasDerivAt_const x A).sub (Real.hasDerivAt_log hx)).const_mul 2) |>.add_const 2)
  dsimp at H
  convert! H using 1
  field_simp
  ring

theorem integral_log_square_from_zero (A : ℝ) {c : ℝ} (hc : 0 < c) :
    IntervalIntegrable (fun x : ℝ => (A - Real.log x) ^ 2) volume 0 c ∧
      (∫ x in (0 : ℝ)..c, (A - Real.log x) ^ 2) = logSquarePrimitive A c := by
  have hcont : ContinuousOn (logSquarePrimitive A) (Icc 0 c) :=
    (continuousOn_logSquarePrimitive A).mono Icc_subset_Ici_self
  have hd (x : ℝ) (hx : x ∈ Ioo 0 c) := hasDerivAt_logSquarePrimitive A hx.1.ne'
  have hi : IntervalIntegrable (fun x : ℝ => (A - Real.log x) ^ 2) volume 0 c := by
    apply intervalIntegral.intervalIntegrable_deriv_of_nonneg (g := logSquarePrimitive A)
    · simpa only [uIcc_of_le hc.le] using hcont
    · simpa only [min_eq_left hc.le, max_eq_right hc.le] using hd
    · intro x hx
      exact sq_nonneg _
  refine ⟨hi, ?_⟩
  simpa [logSquarePrimitive] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hc.le hcont hd hi

theorem log_min_eq_positive_log {ell B : ℝ} (hl : 0 < ell) (hB : 0 < B) :
    Real.log B - Real.log (min ell B) = max (Real.log (B / ell)) 0 := by
  rcases le_total ell B with h | h
  · rw [min_eq_left h, max_eq_left (Real.log_nonneg ((one_le_div hl).mpr h)),
      Real.log_div hB.ne' hl.ne']
  · rw [min_eq_right h, max_eq_right (Real.log_nonpos (div_nonneg hB.le hl.le)
      ((div_le_one hl).mpr h)), sub_self]

/-- The positive logarithm is supported below the cutoff `min ell B`. -/
theorem positiveLogMoment_cutoff {ell B : ℝ} (hl : 0 < ell) (hB : 0 < B)
    (n : ℕ) (hn : n ≠ 0)
    (hi : IntervalIntegrable (fun x : ℝ => (Real.log B - Real.log x) ^ n) volume 0 (min ell B)) :
    IntervalIntegrable (fun x : ℝ => (max (Real.log (B / x)) 0) ^ n) volume 0 ell ∧
      (∫ x in (0 : ℝ)..ell, (max (Real.log (B / x)) 0) ^ n) =
        ∫ x in (0 : ℝ)..min ell B, (Real.log B - Real.log x) ^ n := by
  let c := min ell B
  have hc : 0 < c := lt_min hl hB
  have hcl : c ≤ ell := min_le_left _ _
  have hleft (x : ℝ) (hx : x ∈ Ioo 0 c) :
      (max (Real.log (B / x)) 0) ^ n = (Real.log B - Real.log x) ^ n := by
    rw [max_eq_left (Real.log_nonneg ((one_le_div hx.1).mpr (hx.2.le.trans (min_le_right _ _)))),
      Real.log_div hB.ne' hx.1.ne']
  have hright (x : ℝ) (hx : x ∈ Ioo c ell) : (max (Real.log (B / x)) 0) ^ n = 0 := by
    have hx0 := hc.trans hx.1
    have hBx : B < x := (min_lt_iff.mp hx.1).resolve_left (not_lt.mpr hx.2.le)
    rw [max_eq_right (Real.log_nonpos (div_nonneg hB.le hx0.le)
      ((div_le_one hx0).mpr hBx.le)), zero_pow hn]
  have hi0c : IntervalIntegrable (fun x : ℝ => (max (Real.log (B / x)) 0) ^ n) volume 0 c := by
    apply hi.congr_uIoo
    simpa only [EqOn, c, uIoo_of_le (le_min hl.le hB.le)] using (fun x hx => (hleft x hx).symm)
  have hicl : IntervalIntegrable (fun x : ℝ => (max (Real.log (B / x)) 0) ^ n) volume c ell := by
    apply (intervalIntegrable_const (c := (0 : ℝ))).congr_uIoo
    simpa only [EqOn, uIoo_of_le hcl] using (fun x hx => (hright x hx).symm)
  refine ⟨hi0c.trans hicl, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hi0c hicl,
    intervalIntegral.integral_congr_Ioo_of_le hc.le hleft,
    intervalIntegral.integral_congr_Ioo_of_le hcl hright, intervalIntegral.integral_zero, add_zero]

theorem integral_positive_log {ell B : ℝ} (hl : 0 < ell) (hB : 0 < B) :
    IntervalIntegrable (fun x : ℝ => max (Real.log (B / x)) 0) volume 0 ell ∧
      (∫ x in (0 : ℝ)..ell, max (Real.log (B / x)) 0) =
        min ell B * (1 + max (Real.log (B / ell)) 0) := by
  have hi : IntervalIntegrable (fun x : ℝ => Real.log B - Real.log x) volume 0 (min ell B) :=
    intervalIntegrable_const.sub intervalIntegral.intervalIntegrable_log'
  have H := positiveLogMoment_cutoff hl hB 1 (by norm_num) (by simpa only [pow_one] using hi)
  simp only [pow_one] at H
  refine ⟨H.1, ?_⟩
  rw [H.2, intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_log',
    intervalIntegral.integral_const, integral_log, ← log_min_eq_positive_log hl hB]
  simp only [sub_zero, Real.log_zero, zero_mul, smul_eq_mul]
  ring

theorem integral_positive_log_sq {ell B : ℝ} (hl : 0 < ell) (hB : 0 < B) :
    IntervalIntegrable (fun x : ℝ => (max (Real.log (B / x)) 0) ^ 2) volume 0 ell ∧
      (∫ x in (0 : ℝ)..ell, (max (Real.log (B / x)) 0) ^ 2) =
        min ell B * (2 + 2 * max (Real.log (B / ell)) 0 + (max (Real.log (B / ell)) 0) ^ 2) := by
  have hsq := integral_log_square_from_zero (Real.log B) (lt_min hl hB)
  have H := positiveLogMoment_cutoff hl hB 2 (by norm_num) hsq.1
  refine ⟨H.1, ?_⟩
  rw [H.2, hsq.2, logSquarePrimitive, log_min_eq_positive_log hl hB]
  ring

end BianchiIX
