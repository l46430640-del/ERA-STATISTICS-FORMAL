import BianchiIX.Algebra.CoreAmplitudeCoefficients
import BianchiIX.Dynamics.CoreCoefficientBounds
import BianchiIX.Dynamics.CoreEntry

noncomputable section

namespace BianchiIX

theorem coreAuxiliary_amplitude_bounds {k z : ℝ} {y : CoreAngleState}
    (hk : 6 ≤ k) (hr : 99 / 100 * k ≤ y 0 ∧ y 0 ≤ 101 / 100 * k)
    (hv : 1 ≤ y 0 / Real.cosh z)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ (1 / 10000) / k)
    (hw : 0 ≤ y 2 / (y 0 / Real.cosh z) ∧ y 2 / (y 0 / Real.cosh z) ≤ (1 / 10000) / k) :
    let r := y 0
    let v := r / Real.cosh z
    let w := y 2 / v
    let q := coreAuxiliary z y
    let h := coreAuxiliaryJacobian z y
    |h 3 0| ≤ 2 * y 1 + 3 * w ^ 2 / r ^ 2 ∧
    |h 3 1 + v - v * (1 - q 1)| ≤ 4 * (y 1 + w) ∧
    |v * h 3 2| ≤ 2 * (y 1 + w / r) ∧
    |q 3 * h 1 0| ≤ (y 1 + w ^ 2 / r ^ 2) / 10 ∧
    |q 3 * h 1 1| ≤ (y 1 + w / r) / 10 ∧
    |v * q 3 * h 1 2| ≤ (y 1 + w / r) / 10 := by
  intro r v w q h
  let m := (1 / 10000) / k
  obtain ⟨hr5, hm0, hm, _, _, _, _, _⟩ := coreBootstrap_coefficient_scales hk hr
  have hr0 : 0 < r := by dsimp [r]; linarith only [hr5]
  have hv0 : 0 < v := by dsimp [v, r]; linarith only [hv]
  have hv' : 1 ≤ v ∧ v ≤ r := ⟨hv, div_le_self hr0.le (Real.one_le_cosh z)⟩
  have hs : 0 ≤ 1 / Real.cosh z ∧ 1 / Real.cosh z ≤ 1 :=
    ⟨by positivity, (div_le_one (Real.cosh_pos z)).mpr (Real.one_le_cosh z)⟩
  have hc : |-Real.tanh z| ≤ 1 := by
    rw [abs_neg]
    exact abs_le.mpr ⟨(Real.neg_one_lt_tanh z).le, (Real.tanh_lt_one z).le⟩
  obtain ⟨hR, hU, hP⟩ := core_amplitude_radius_numerators hr5 ⟨hm0, hm⟩ hu hw hv' hs hc
  have hg : |q 3| ≤ 2 * r * m := (coreAuxiliary_coefficient_bounds hk hr hv hu hw).2.2.1
  obtain ⟨hpR, hpU⟩ := core_amplitude_clock_products hr5 ⟨hm0, hm⟩ hu hw hg
  refine ⟨hR, hU, hP, hpR, hpU, ?_⟩
  have hid : v * q 3 * h 1 2 = -(q 3 * h 1 1) := by
    change v * q 3 * (2 * (y 1 - w) / (v * r ^ 2)) = -(q 3 * (-2 * (y 1 - w) / r ^ 2))
    field_simp
  rw [hid, abs_neg]
  exact hpU

/-- The three amplitude-sensitive radius-row estimates in (B.35). -/
theorem coreWeightedJacobian_amplitude_bounds {k z : ℝ} {y : CoreAngleState}
    (hk : 6 ≤ k) (hr : 99 / 100 * k ≤ y 0 ∧ y 0 ≤ 101 / 100 * k)
    (hv : 1 ≤ y 0 / Real.cosh z)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ (1 / 10000) / k)
    (hw : 0 ≤ y 2 / (y 0 / Real.cosh z) ∧ y 2 / (y 0 / Real.cosh z) ≤ (1 / 10000) / k) :
    let v := y 0 / Real.cosh z
    let w := y 2 / v
    let b := coreWeightedJacobian k z y
    |b 0 0| ≤ 8 * (y 1 + w ^ 2 / k ^ 2) ∧
    |b 0 1 + v / k| ≤ 8 * (y 1 + w) / k ∧
    |b 0 2| ≤ 8 * (y 1 + w / k) / v := by
  intro v w b
  let r := y 0
  let q := coreAuxiliary z y
  let h := coreAuxiliaryJacobian z y
  have hk0 : 0 < k := by linarith only [hk]
  obtain ⟨hr5, _, _, _, _, hkr, hk2r2, _⟩ := coreBootstrap_coefficient_scales hk hr
  have hr0 : 0 < r := by dsimp [r]; linarith only [hr5]
  have hv0 : 0 < v := by dsimp [v]; linarith only [hv]
  have hu0 := hu.1
  have hw0 : 0 ≤ w := hw.1
  have hd : 999 / 1000 ≤ q 1 := (coreAuxiliary_coefficient_bounds hk hr hv hu hw).2.2.2.1
  have hd0 : 0 < q 1 := by linarith only [hd]
  obtain ⟨hR, hU, hP, hpR, hpU, hpP⟩ := coreAuxiliary_amplitude_bounds hk hr hv hu hw
  change |h 3 0| ≤ 2 * y 1 + 3 * w ^ 2 / r ^ 2 at hR
  change |h 3 1 + v - v * (1 - q 1)| ≤ 4 * (y 1 + w) at hU
  change |v * h 3 2| ≤ 2 * (y 1 + w / r) at hP
  change |q 3 * h 1 0| ≤ (y 1 + w ^ 2 / r ^ 2) / 10 at hpR
  change |q 3 * h 1 1| ≤ (y 1 + w / r) / 10 at hpU
  change |v * q 3 * h 1 2| ≤ (y 1 + w / r) / 10 at hpP
  have hwscale : w / r ≤ (3 / 2) * (w / k) := by
    calc
      _ = (k / r) * (w / k) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hkr (by positivity)
  have hw2scale : w ^ 2 / r ^ 2 ≤ (3 / 2) * (w ^ 2 / k ^ 2) := by
    calc
      _ = (k ^ 2 / r ^ 2) * (w ^ 2 / k ^ 2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hk2r2 (by positivity)
  have hwk : 0 ≤ w / k := div_nonneg hw0 hk0.le
  have hw2k : 0 ≤ w ^ 2 / k ^ 2 := by positivity
  constructor
  · change |h 3 0 / q 1 - q 3 * h 1 0 / q 1 ^ 2| ≤ 8 * (y 1 + w ^ 2 / k ^ 2)
    have H := core_clock_quotient_bound hd hR hpR
    rw [show 3 * w ^ 2 / r ^ 2 = 3 * (w ^ 2 / r ^ 2) by ring] at H
    linarith only [H, hw2scale, hu0, hw2k]
  constructor
  · have hid : b 0 1 + v / k =
        ((h 3 1 + v - v * (1 - q 1)) / q 1 - q 3 * h 1 1 / q 1 ^ 2) / k := by
      change (h 3 1 / q 1 - q 3 * h 1 1 / q 1 ^ 2) / k + v / k = _
      field_simp
      ring
    rw [hid, abs_div, abs_of_pos hk0]
    apply div_le_div_of_nonneg_right _ hk0.le
    have hwr : w / r ≤ w := div_le_self hw0 (by linarith only [hr5])
    have hpU' : |q 3 * h 1 1| ≤ (y 1 + w) / 10 := by linarith only [hpU, hwr]
    have H := core_clock_quotient_bound hd hU hpU'
    linarith only [H, hu0, hw0]
  · have hid : b 0 2 = ((v * h 3 2) / q 1 - (v * q 3 * h 1 2) / q 1 ^ 2) / v := by
      change h 3 2 / q 1 - q 3 * h 1 2 / q 1 ^ 2 = _
      field_simp
    rw [hid, abs_div, abs_of_pos hv0]
    apply div_le_div_of_nonneg_right _ hv0.le
    have H := core_clock_quotient_bound hd hP hpP
    linarith only [H, hwscale, hu0, hwk]

theorem coreRegion_amplitude_row_bounds {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) :
    let b := coreWeightedJacobian k (coreAngle (y 0) (y 2)) (toCoreAngleState y)
    |b 0 0| ≤ 8 * (y 1 + y 3 ^ 2 / k ^ 2) ∧
    |b 0 1 + y 2 / k| ≤ 8 * (y 1 + y 3) / k ∧
    |b 0 2| ≤ 8 * (y 1 + y 3 / k) / y 2 := by
  have hv0 : 0 < y 2 := lt_of_lt_of_le zero_lt_one hy.2.1
  have hcoord := (coreAngle_coordinates (m := y 0) hv0).1
  have hv : 1 ≤ (toCoreAngleState y) 0 / Real.cosh (coreAngle (y 0) (y 2)) := by
    change 1 ≤ coreRadius (y 0) (y 2) / Real.cosh (coreAngle (y 0) (y 2))
    rw [hcoord]
    exact hy.2.1
  have hw : 0 ≤ (toCoreAngleState y) 2 / ((toCoreAngleState y) 0 / Real.cosh (coreAngle (y 0) (y 2))) ∧
      (toCoreAngleState y) 2 / ((toCoreAngleState y) 0 / Real.cosh (coreAngle (y 0) (y 2))) ≤ (1 / 10000) / k := by
    change 0 ≤ y 2 * y 3 / (coreRadius (y 0) (y 2) / Real.cosh (coreAngle (y 0) (y 2))) ∧
      y 2 * y 3 / (coreRadius (y 0) (y 2) / Real.cosh (coreAngle (y 0) (y 2))) ≤ (1 / 10000) / k
    rw [hcoord, mul_div_cancel_left₀ _ (ne_of_gt hv0)]
    exact (coreRegion_wall_bounds hy).2
  have H := coreWeightedJacobian_amplitude_bounds hk (coreRegion_radius_bounds hk hy) hv hy.2.2.1 hw
  dsimp only at H ⊢
  simpa [toCoreAngleState, hcoord, ne_of_gt hv0] using H

end BianchiIX
