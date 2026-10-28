import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The positive root-amplitude extension in Section 4.2. -/

open Set Filter MeasureTheory
open scoped Topology

namespace BianchiIX

noncomputable section

def rootCutoff (t : ℝ) : ℝ := max (1 - t) 0

def rootPrimitive (t : ℝ) : ℝ := ∫ u in (0 : ℝ)..t, rootCutoff u

theorem continuous_rootCutoff : Continuous rootCutoff :=
  (continuous_const.sub continuous_id).max continuous_const

theorem hasDerivAt_rootPrimitive (t : ℝ) : HasDerivAt rootPrimitive (rootCutoff t) t :=
  intervalIntegral.integral_hasDerivAt_right (continuous_rootCutoff.intervalIntegrable _ _)
    continuous_rootCutoff.aestronglyMeasurable.stronglyMeasurableAtFilter
    continuous_rootCutoff.continuousAt

theorem contDiff_rootPrimitive : ContDiff ℝ 1 rootPrimitive := by
  rw [contDiff_one_iff_deriv]
  exact ⟨fun t => (hasDerivAt_rootPrimitive t).differentiableAt,
    continuous_rootCutoff.congr (fun t => (hasDerivAt_rootPrimitive t).deriv.symm)⟩

theorem rootPrimitive_on_unit {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    rootPrimitive t = t - t ^ 2 / 2 := by
  have heq : rootPrimitive t = ∫ u in (0 : ℝ)..t, (1 - u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht.1] at hu
    exact max_eq_left (by linarith [hu.2, ht.2])
  rw [heq]
  have hd (u : ℝ) : HasDerivAt (fun v : ℝ => v - v ^ 2 / 2) (1 - u) u := by
    convert! (hasDerivAt_id u).sub (((hasDerivAt_id u).pow 2).div_const 2) using 1
    simp
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    ((continuous_const.sub continuous_id).intervalIntegrable 0 t)

theorem rootPrimitive_after_one {t : ℝ} (ht : 1 ≤ t) : rootPrimitive t = 1 / 2 := by
  have hzero : (∫ u in (1 : ℝ)..t, rootCutoff u) = 0 := by
    calc
      _ = ∫ _u in (1 : ℝ)..t, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le ht] at hu
        exact max_eq_right (by linarith [hu.1])
      _ = 0 := by simp
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (continuous_rootCutoff.intervalIntegrable (μ := volume) 0 1)
    (continuous_rootCutoff.intervalIntegrable (μ := volume) 1 t)
  change rootPrimitive 1 + _ = rootPrimitive t at hadd
  rw [hzero, rootPrimitive_on_unit ⟨by norm_num, le_rfl⟩] at hadd
  linarith

theorem rootPrimitive_bounds {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ rootPrimitive t ∧ rootPrimitive t ≤ 1 / 2 := by
  rcases le_total t 1 with h | h
  · rw [rootPrimitive_on_unit ⟨ht, h⟩]
    constructor <;> nlinarith [mul_nonneg ht (sub_nonneg.mpr h), sq_nonneg (t - 1)]
  · rw [rootPrimitive_after_one h]
    norm_num

theorem rootCutoff_bounds {t : ℝ} (ht : 0 ≤ t) : 0 ≤ rootCutoff t ∧ rootCutoff t ≤ 1 :=
  ⟨le_max_right _ _, max_le (by linarith) zero_le_one⟩

/-- The argument is the signed displacement from the endpoint; `e` is the outward orientation. -/
def rootExtension (s d e x : ℝ) : ℝ := s + e * d * s * rootPrimitive (e * x / s)

theorem rootExtension_zero (s d e : ℝ) : rootExtension s d e 0 = s := by
  simp [rootExtension, rootPrimitive]

theorem hasDerivAt_rootExtension {s e : ℝ} (hs : 0 < s) (he : |e| = 1) (d x : ℝ) :
    HasDerivAt (rootExtension s d e) (d * rootCutoff (e * x / s)) x := by
  have he2 : e ^ 2 = 1 := by nlinarith [sq_abs e]
  have h := (((hasDerivAt_rootPrimitive (e * x / s)).comp x
    (((hasDerivAt_id x).const_mul e).div_const s)).const_mul (e * d * s)).const_add s
  convert! h using 1
  field_simp
  ring_nf
  simp [he2]

theorem continuous_rootExtension_derivative (s d e : ℝ) :
    Continuous (fun x => d * rootCutoff (e * x / s)) :=
  (continuous_rootCutoff.comp ((continuous_const.mul continuous_id).div_const s)).const_mul d

theorem contDiff_rootExtension {s e : ℝ} (hs : 0 < s) (he : |e| = 1) (d : ℝ) :
    ContDiff ℝ 1 (rootExtension s d e) := by
  rw [contDiff_one_iff_deriv]
  exact ⟨fun x => (hasDerivAt_rootExtension hs he d x).differentiableAt,
    (continuous_rootExtension_derivative s d e).congr
      (fun x => (hasDerivAt_rootExtension hs he d x).deriv.symm)⟩

theorem rootExtension_error {s d e x θ : ℝ} (hs : 0 < s) (he : |e| = 1)
    (hx : 0 ≤ e * x) (hd : |d| ≤ θ / 2) :
    |rootExtension s d e x - s| ≤ θ * s / 4 := by
  have hp := rootPrimitive_bounds (div_nonneg hx hs.le)
  rw [rootExtension, add_sub_cancel_left, abs_mul, abs_mul, abs_mul,
    he, one_mul, abs_of_pos hs, abs_of_nonneg hp.1]
  calc
    _ ≤ |d| * s * (1 / 2) := mul_le_mul_of_nonneg_left hp.2 (mul_nonneg (abs_nonneg d) hs.le)
    _ ≤ (θ / 2) * s * (1 / 2) := by gcongr
    _ = _ := by ring

theorem rootExtension_bounds {s d e x θ : ℝ} (hs : 0 < s) (he : |e| = 1)
    (hx : 0 ≤ e * x) (hd : |d| ≤ θ / 2) :
    (1 - θ / 4) * s ≤ rootExtension s d e x ∧
      rootExtension s d e x ≤ (1 + θ / 4) * s := by
  have h := abs_le.mp (rootExtension_error hs he hx hd)
  constructor <;> nlinarith [h.1, h.2]

theorem rootExtension_pos {s d e x θ : ℝ} (hs : 0 < s) (he : |e| = 1)
    (hx : 0 ≤ e * x) (hd : |d| ≤ θ / 2) (hθ : θ ≤ 1) : 0 < rootExtension s d e x := by
  have hb := (rootExtension_bounds hs he hx hd).1
  have hfactor : 0 < 1 - θ / 4 := by linarith
  exact (mul_pos hfactor hs).trans_le hb

theorem rootExtension_derivative_bound {s d e x θ : ℝ} (hs : 0 < s)
    (hx : 0 ≤ e * x) (hd : |d| ≤ θ / 2) : |d * rootCutoff (e * x / s)| ≤ θ / 2 := by
  have hc := rootCutoff_bounds (div_nonneg hx hs.le)
  rw [abs_mul, abs_of_nonneg hc.1]
  exact (mul_le_of_le_one_right (abs_nonneg d) hc.2).trans hd

theorem rootExtension_derivative_zero {s e : ℝ} (hs : 0 < s) (he : |e| = 1) (d : ℝ) :
    deriv (rootExtension s d e) 0 = d := by
  rw [(hasDerivAt_rootExtension hs he d 0).deriv]
  simp [rootCutoff]

theorem rootExtension_constant_tail {s d e x : ℝ} (hs : 0 < s) (hx : s ≤ e * x) :
    rootExtension s d e x = s + e * d * s / 2 := by
  rw [rootExtension, rootPrimitive_after_one ((le_div_iff₀ hs).mpr (by simpa using hx))]
  ring

theorem square_derivative_cone {f : ℝ → ℝ} {d x θ : ℝ} (hf : HasDerivAt f d x)
    (hpos : 0 < f x) (hd : |d| ≤ θ / 2) :
    |deriv (fun z => f z ^ 2) x| ≤ θ * Real.sqrt (f x ^ 2) := by
  have hp' : HasDerivAt (fun z => f z ^ 2) (2 * f x * d) x := by
    convert! hf.pow 2 using 1
    simp
  rw [hp'.deriv, Real.sqrt_sq hpos.le]
  rw [abs_mul, abs_mul, abs_of_pos hpos]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ ≤ 2 * f x * (θ / 2) := mul_le_mul_of_nonneg_left hd (by positivity)
    _ = _ := by ring

theorem rootExtension_pair_bound {s t d c e x θ B : ℝ} (hs : 0 < s) (ht : 0 < t)
    (he : |e| = 1) (hx : 0 ≤ e * x) (hd : |d| ≤ θ / 2) (hc : |c| ≤ θ / 2)
    (hθ : θ ≤ 1) (hB : s ^ 2 + t ^ 2 ≤ B) :
    rootExtension s d e x ^ 2 + rootExtension t c e x ^ 2 ≤ (1 + θ / 4) ^ 2 * B := by
  have hs2 := pow_le_pow_left₀ (rootExtension_pos hs he hx hd hθ).le
    (rootExtension_bounds hs he hx hd).2 2
  have ht2 := pow_le_pow_left₀ (rootExtension_pos ht he hx hc hθ).le
    (rootExtension_bounds ht he hx hc).2 2
  calc
    _ ≤ ((1 + θ / 4) * s) ^ 2 + ((1 + θ / 4) * t) ^ 2 := add_le_add hs2 ht2
    _ = (1 + θ / 4) ^ 2 * (s ^ 2 + t ^ 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hB (sq_nonneg _)

theorem measurable_rootExtension {X : Type*} [MeasurableSpace X] {s d e x : X → ℝ}
    (hs : Measurable s) (hd : Measurable d) (he : Measurable e) (hx : Measurable x) :
    Measurable (fun q => rootExtension (s q) (d q) (e q) (x q)) :=
  hs.add (((he.mul hd).mul hs).mul (contDiff_rootPrimitive.continuous.measurable.comp ((he.mul hx).div hs)))

theorem measurable_rootExtension_derivative {X : Type*} [MeasurableSpace X] {s d e x : X → ℝ}
    (hs : Measurable s) (hd : Measurable d) (he : Measurable e) (hx : Measurable x) :
    Measurable (fun q => d q * rootCutoff (e q * x q / s q)) :=
  hd.mul (continuous_rootCutoff.measurable.comp ((he.mul hx).div hs))

end
end BianchiIX
