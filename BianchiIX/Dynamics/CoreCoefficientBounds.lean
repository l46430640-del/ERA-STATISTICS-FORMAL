import BianchiIX.Algebra.CoreCoefficientEstimates
import BianchiIX.Dynamics.CoreDiagonalBounds

noncomputable section

namespace BianchiIX

theorem coreAuxiliary_coefficient_bounds {k z : ℝ} {y : CoreAngleState}
    (hk : 6 ≤ k) (hr : 99 / 100 * k ≤ y 0 ∧ y 0 ≤ 101 / 100 * k)
    (hv : 1 ≤ y 0 / Real.cosh z)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ (1 / 10000) / k)
    (hw : 0 ≤ y 2 / (y 0 / Real.cosh z) ∧ y 2 / (y 0 / Real.cosh z) ≤ (1 / 10000) / k) :
    let r := y 0
    let v := r / Real.cosh z
    let m := (1 / 10000) / k
    let q := coreAuxiliary z y
    let h := coreAuxiliaryJacobian z y
    (0 ≤ q 0 ∧ q 0 ≤ 1 / 100) ∧ |q 2| ≤ r ∧ |q 3| ≤ 2 * r * m ∧
    999 / 1000 ≤ q 1 ∧
    |h 0 0| ≤ y 1 ∧ |h 0 1| ≤ 2 * r ∧
    |h 1 0| ≤ m / r ^ 2 ∧ |h 1 1| ≤ 2 * m / r ^ 2 ∧ |h 1 2| ≤ 2 * m / (v * r ^ 2) ∧
    |h 2 0| ≤ 3 / 4 ∧ |h 2 2| ≤ 1 / r ∧
    |h 3 0| ≤ 2 * m ∧ |h 3 1 + v| ≤ 3 * m ∧ |h 3 2| ≤ 2 * m / v := by
  let r := y 0
  let u := y 1
  let v := r / Real.cosh z
  let w := y 2 / v
  let m := (1 / 10000) / k
  let s := 1 / Real.cosh z
  let c := -Real.tanh z
  have hk0 : 0 < k := by linarith
  have hr5 : 5 ≤ r := by dsimp [r]; linarith [hr.1]
  have hr0 : 0 < r := by linarith
  have hm : 0 ≤ m ∧ m ≤ 1 / 100 := by
    dsimp [m]
    exact ⟨by positivity, (div_le_iff₀ hk0).mpr (by linarith)⟩
  have hrm : r * m ≤ 1 / 1000 := by
    dsimp [m]
    rw [← mul_div_assoc, div_le_iff₀ hk0]
    dsimp [r]
    linarith [hr.2]
  have hv' : 1 ≤ v ∧ v ≤ r := ⟨hv, div_le_self hr0.le (Real.one_le_cosh z)⟩
  have hs : 0 ≤ s ∧ s ≤ 1 :=
    ⟨by dsimp [s]; positivity, (div_le_one (Real.cosh_pos z)).mpr (Real.one_le_cosh z)⟩
  have hc : |c| ≤ 1 := by
    dsimp [c]
    rw [abs_neg]
    exact abs_le.mpr ⟨(Real.neg_one_lt_tanh z).le, (Real.tanh_lt_one z).le⟩
  obtain ⟨hC0, _, hC⟩ := core_small_coupling hm hrm hu hw hv'
  obtain ⟨ha, hg⟩ := core_small_numerators hr5 hm hrm hu hw hv' hs hc
  obtain ⟨hCR, hCU⟩ := core_small_coupling_derivatives hr5 hm hu hw hv' hs
  obtain ⟨hdR, hdU, hdP⟩ := core_small_clock_derivatives (v := v) hr5 hm hu hw (by linarith [hv'.1])
  obtain ⟨haR, haP⟩ := core_small_strong_derivatives hr5 hm hu hw hv'.1 hs
  obtain ⟨hgR, hgU, hgP⟩ := core_small_radius_derivatives hr5 hm hu hw hv' hs hc
  refine ⟨⟨hC0, hC⟩, ?_, ?_, (coreBootstrap_clock_bounds hk hr.1 hu hw).1,
    hCR, hCU, hdR, hdU, hdP, haR, haP, hgR, hgU, hgP⟩
  · convert! ha using 1
    dsimp [coreAuxiliary, r, v, w, s, c]
    congr 1
    ring
  · convert! hg using 1
    dsimp [coreAuxiliary, r, v, w, c]
    congr 1
    ring

theorem coreWeightedJacobian_radius_bounds {k z : ℝ} {y : CoreAngleState}
    (hk : 6 ≤ k) (hr : 99 / 100 * k ≤ y 0 ∧ y 0 ≤ 101 / 100 * k)
    (hv : 1 ≤ y 0 / Real.cosh z)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ (1 / 10000) / k)
    (hw : 0 ≤ y 2 / (y 0 / Real.cosh z) ∧ y 2 / (y 0 / Real.cosh z) ≤ (1 / 10000) / k) :
    let m := (1 / 10000) / k
    let v := y 0 / Real.cosh z
    let b := coreWeightedJacobian k z y
    |b 0 0| ≤ 8 * m ∧ |b 0 1 + v / k| ≤ 8 * m / k ∧ |b 0 2| ≤ 8 * m / v := by
  let r := y 0
  let v := r / Real.cosh z
  let m := (1 / 10000) / k
  let q := coreAuxiliary z y
  let h := coreAuxiliaryJacobian z y
  obtain ⟨hr5, hm0, hm, _, _, _, _, hsmall⟩ := coreBootstrap_coefficient_scales hk hr
  obtain ⟨_, _, hg, hd, _, _, hdR, hdU, hdP, _, _, hgR, hgU, hgP⟩ :=
    coreAuxiliary_coefficient_bounds hk hr hv hu hw
  change |q 3| ≤ 2 * r * m at hg
  change 999 / 1000 ≤ q 1 at hd
  change |h 1 0| ≤ m / r ^ 2 at hdR
  change |h 1 1| ≤ 2 * m / r ^ 2 at hdU
  change |h 1 2| ≤ 2 * m / (v * r ^ 2) at hdP
  have hr0 : 0 < r := by dsimp [r]; linarith
  have hv0 : 0 < v := by dsimp [v, r]; linarith
  have hk0 : 0 < k := by linarith
  have hd0 : 0 < q 1 := by linarith
  have hprodR : |q 3 * h 1 0| ≤ m / 10 := by
    calc
      _ = |q 3| * |h 1 0| := abs_mul _ _
      _ ≤ (2 * r * m) * (m / r ^ 2) := mul_le_mul hg hdR (abs_nonneg _) (by positivity)
      _ = 2 * m ^ 2 / r := by field_simp
      _ ≤ 4 * m ^ 2 / r := div_le_div_of_nonneg_right (by nlinarith [sq_nonneg m]) hr0.le
      _ ≤ m / 10 := hsmall
  have hprodU : |q 3 * h 1 1| ≤ m / 10 := by
    calc
      _ = |q 3| * |h 1 1| := abs_mul _ _
      _ ≤ (2 * r * m) * (2 * m / r ^ 2) := mul_le_mul hg hdU (abs_nonneg _) (by positivity)
      _ = 4 * m ^ 2 / r := by field_simp; ring
      _ ≤ m / 10 := hsmall
  have hprodP : |v * q 3 * h 1 2| ≤ m / 10 := by
    calc
      _ = v * |q 3| * |h 1 2| := by rw [abs_mul, abs_mul, abs_of_pos hv0]
      _ ≤ v * (2 * r * m) * (2 * m / (v * r ^ 2)) := by gcongr
      _ = 4 * m ^ 2 / r := by field_simp; ring
      _ ≤ m / 10 := hsmall
  have hvclock : |v * (1 - q 1)| ≤ m := by
    let w := y 2 / v
    have hδ := (core_wall_difference_bounds hu hw).1
    have hδ2 : (y 1 - w) ^ 2 ≤ m ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hm0).mpr hδ
    have hvle : v ≤ r := div_le_self hr0.le (Real.one_le_cosh z)
    have hid : 1 - q 1 = (y 1 - w) ^ 2 / r ^ 2 := by dsimp [q, coreAuxiliary, coreClockFactor, w, v, r]; ring
    rw [hid, abs_of_nonneg (mul_nonneg hv0.le (div_nonneg (sq_nonneg _) (sq_nonneg _)))]
    calc
      _ ≤ r * (m ^ 2 / r ^ 2) := mul_le_mul hvle
        (div_le_div_of_nonneg_right hδ2 (sq_nonneg _)) (by positivity) hr0.le
      _ = m ^ 2 / r := by field_simp
      _ ≤ m := (div_le_iff₀ hr0).mpr (by nlinarith [mul_nonneg hm0 (show 0 ≤ r - m by dsimp [r]; linarith)])
  have hx : |h 3 1 + v - v * (1 - q 1)| ≤ 4 * m := by
    have H := (abs_sub (h 3 1 + v) (v * (1 - q 1))).trans (add_le_add hgU hvclock)
    linarith
  constructor
  · change |h 3 0 / q 1 - q 3 * h 1 0 / q 1 ^ 2| ≤ 8 * m
    have H := core_clock_quotient_bound hd hgR hprodR
    linarith
  constructor
  · have hid : (coreWeightedJacobian k z y) 0 1 + v / k =
        ((h 3 1 + v - v * (1 - q 1)) / q 1 - q 3 * h 1 1 / q 1 ^ 2) / k := by
      change (h 3 1 / q 1 - q 3 * h 1 1 / q 1 ^ 2) / k + v / k = _
      field_simp
      ring
    change |(coreWeightedJacobian k z y) 0 1 + v / k| ≤ 8 * m / k
    rw [hid, abs_div, abs_of_pos hk0]
    apply div_le_div_of_nonneg_right _ hk0.le
    have H := core_clock_quotient_bound hd hx hprodU
    linarith
  · have hvh : |v * h 3 2| ≤ 2 * m := by
      rw [abs_mul, abs_of_pos hv0]
      have H := mul_le_mul_of_nonneg_left hgP hv0.le
      change v * |h 3 2| ≤ v * (2 * m / v) at H
      calc
        _ ≤ v * (2 * m / v) := H
        _ = 2 * m := by field_simp
    have hid : (coreWeightedJacobian k z y) 0 2 =
        ((v * h 3 2) / q 1 - (v * q 3 * h 1 2) / q 1 ^ 2) / v := by
      change h 3 2 / q 1 - q 3 * h 1 2 / q 1 ^ 2 = _
      field_simp
    change |(coreWeightedJacobian k z y) 0 2| ≤ 8 * m / v
    rw [hid, abs_div, abs_of_pos hv0]
    apply div_le_div_of_nonneg_right _ hv0.le
    have H := core_clock_quotient_bound hd hvh hprodP
    linarith

end BianchiIX
