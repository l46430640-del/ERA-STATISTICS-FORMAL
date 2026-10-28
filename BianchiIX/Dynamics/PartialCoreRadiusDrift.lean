import BianchiIX.Analysis.PartialCoreRadialIntegral
import BianchiIX.Algebra.PartialCoreRadialBounds

noncomputable section

namespace BianchiIX

open Set MeasureTheory

/-- The partial-core estimate (E.17), with no restriction on the initial angle. -/
theorem partialCoreAngle_radius_drift {Y : ℝ → CoreAngleState} {a b k : ℝ}
    (hab : a ≤ b) (hk : 6 ≤ k)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (coreAngleField z (Y z)) z)
    (hinit : Y a 0 = k)
    (hr : ∀ z ∈ Icc a b, 99 / 100 * k ≤ Y z 0 ∧ Y z 0 ≤ 101 / 100 * k)
    (hv : ∀ z ∈ Icc a b, 1 ≤ Y z 0 / Real.cosh z)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ (1 / 10000) / k)
    (hp : ∀ z ∈ Icc a b, 0 ≤ Y z 2 ∧ Y z 2 ≤ (1 / 10000) / k) :
    |Y b 0 - k| ≤ 16 * (Y a 1 + (Y a 2) ^ 2 / k) := by
  let r : ℝ → ℝ := fun z => Y z 0
  let u : ℝ → ℝ := fun z => Y z 1
  let v : ℝ → ℝ := fun z => r z / Real.cosh z
  let w : ℝ → ℝ := fun z => Y z 2 / v z
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hk0 : 0 < k := by linarith only [hk]
  have hr0 (z : ℝ) (hz : z ∈ Icc a b) : 0 < r z := by
    have H := (hr z hz).1
    change 99 / 100 * k ≤ r z at H
    linarith only [H, hk]
  have hv0 (z : ℝ) (hz : z ∈ Icc a b) : 0 < v z := zero_lt_one.trans_le (hv z hz)
  have hw (z : ℝ) (hz : z ∈ Icc a b) : 0 ≤ w z ∧ w z ≤ (1 / 10000) / k :=
    ⟨div_nonneg (hp z hz).1 (hv0 z hz).le, (div_le_self (hp z hz).1 (hv z hz)).trans (hp z hz).2⟩
  have hcon (z : ℝ) (hz : z ∈ Icc a b) :
      u z ≤ u a * Real.exp (-k * (z - a) / 4) ∧ Y z 2 ≤ Y a 2 := by
    exact coreAngle_prefix_contraction (z₀ := 0) (convex_Icc a b) hk
      (fun t ht => by simpa only [add_zero] using hY t ht)
      (fun t ht => (hr t ht).1) (by simpa only [add_zero] using hv) hu
      (by simpa only [add_zero] using hw) ha hz hz.1
  have hcoord (i : Fin 3) : ContinuousOn (fun z => Y z i) (Icc a b) :=
    fun z hz => (hasDerivAt_pi.mp (hY z hz) i).continuousAt.continuousWithinAt
  have hrc : ContinuousOn r (Icc a b) := hcoord 0
  have huc : ContinuousOn u (Icc a b) := hcoord 1
  have hvc : ContinuousOn v (Icc a b) := hrc.div Real.continuous_cosh.continuousOn
    (fun z _ => ne_of_gt (Real.cosh_pos z))
  have hwc : ContinuousOn w (Icc a b) := (hcoord 2).div hvc (fun z hz => ne_of_gt (hv0 z hz))
  have hlo (z : ℝ) (hz : z ∈ Icc a b) : 9 / 10 * k ≤ r z := by
    have H := (hr z hz).1
    change 99 / 100 * k ≤ r z at H
    linarith only [H, hk]
  have hvbound (z : ℝ) (hz : z ∈ Icc a b) : 0 ≤ v z ∧ v z ≤ 11 / 10 * k := by
    refine ⟨(hv0 z hz).le, ?_⟩
    have H := div_le_self (hr0 z hz).le (Real.one_le_cosh z)
    have H' := (hr z hz).2
    change v z ≤ r z at H
    change r z ≤ 101 / 100 * k at H'
    linarith only [H, H', hk]
  have hwenv (z : ℝ) (hz : z ∈ Icc a b) :
      0 ≤ w z ∧ w z ≤ Y a 2 ∧ w z ≤ Y a 2 * Real.cosh z / r z := by
    refine ⟨(hw z hz).1, (div_le_self (hp z hz).1 (hv z hz)).trans (hcon z hz).2, ?_⟩
    calc
      w z = Y z 2 * Real.cosh z / r z := by
        dsimp [w, v]
        field_simp [ne_of_gt (hr0 z hz), ne_of_gt (Real.cosh_pos z)]
      _ ≤ Y a 2 * Real.cosh z / r z :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hcon z hz).2 (Real.cosh_pos z).le) (hr0 z hz).le
  have hend (z : ℝ) (hz : z ∈ Icc a b) : Real.cosh z ≤ 11 / 10 * k := by
    have H := (le_div_iff₀ (Real.cosh_pos z)).mp (hv z hz)
    have H' := (hr z hz).2
    nlinarith only [H, H', hk]
  obtain ⟨hUV, hUW, hU2, hW2⟩ := partial_core_four_integral_bounds hab hk (hu a ha).1 (hp a ha).1
    hrc huc hvc hwc hlo (fun z hz => ⟨(hu z hz).1, (hcon z hz).1⟩) hvbound hwenv (hend a ha) (hend b hb)
  have hc1 := huc.mul hvc
  have hc2 := huc.mul hwc
  have hc3 := (huc.pow 2).div hrc (fun z hz => ne_of_gt (hr0 z hz))
  have hc4 := (hwc.pow 2).div hrc (fun z hz => ne_of_gt (hr0 z hz))
  have hbound (z : ℝ) (hz : z ∈ Icc a b) :
      |coreAngleField z (Y z) 0| ≤ (u z * v z + u z * w z + u z ^ 2 / r z + w z ^ 2 / r z) / (999 / 1000) :=
    core_radial_velocity_bound hk (hr z hz).1 (hv z hz) (hu z hz) (hw z hz) (Real.abs_tanh_lt_one z).le
  have H := abs_sub_le_integral_bound hab (fun z hz => hasDerivAt_pi.mp (hY z hz) 0)
    (((hc1.add hc2).add hc3).add hc4 |>.div_const (999 / 1000)) hbound
  have hi1 := hc1.intervalIntegrable_of_Icc (μ := volume) hab
  have hi2 := hc2.intervalIntegrable_of_Icc (μ := volume) hab
  have hi3 := hc3.intervalIntegrable_of_Icc (μ := volume) hab
  have hi4 := hc4.intervalIntegrable_of_Icc (μ := volume) hab
  rw [hinit, intervalIntegral.integral_div] at H
  simp only [Pi.add_apply] at H
  rw [intervalIntegral.integral_add ((hi1.add hi2).add hi3) hi4,
    intervalIntegral.integral_add (hi1.add hi2) hi3, intervalIntegral.integral_add hi1 hi2] at H
  exact H.trans ((div_le_div_of_nonneg_right (add_le_add (add_le_add (add_le_add hUV hUW) hU2) hW2)
    (by norm_num : (0 : ℝ) ≤ 999 / 1000)).trans (partial_core_radius_budget hk (hu a ha) (hp a ha)))

theorem partialCoreAngle_energy_improvement {Y : ℝ → CoreAngleState} {a b k : ℝ}
    (hab : a ≤ b) (hk : 6 ≤ k)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (coreAngleField z (Y z)) z)
    (hinit : Y a 0 = k)
    (hr : ∀ z ∈ Icc a b, 99 / 100 * k ≤ Y z 0 ∧ Y z 0 ≤ 101 / 100 * k)
    (hv : ∀ z ∈ Icc a b, 1 ≤ Y z 0 / Real.cosh z)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ (1 / 10000) / k)
    (hp : ∀ z ∈ Icc a b, 0 ≤ Y z 2 ∧ Y z 2 ≤ (1 / 10000) / k) :
    |Y b 0 ^ 2 - k ^ 2| < 1 / 16 := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  exact partial_core_radius_energy_improvement hk (by have H := (hr b hb).1; linarith)
    (hr b hb).2 (hu a ha) (hp a ha) (partialCoreAngle_radius_drift hab hk hY hinit hr hv hu hp)

theorem partialCoreAngle_radius_drift_shifted {Y : ℝ → CoreAngleState} {a b k z₀ : ℝ}
    (hab : a ≤ b) (hk : 6 ≤ k)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (coreAngleField (z + z₀) (Y z)) z)
    (hinit : Y a 0 = k)
    (hr : ∀ z ∈ Icc a b, 99 / 100 * k ≤ Y z 0 ∧ Y z 0 ≤ 101 / 100 * k)
    (hv : ∀ z ∈ Icc a b, 1 ≤ Y z 0 / Real.cosh (z + z₀))
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ (1 / 10000) / k)
    (hp : ∀ z ∈ Icc a b, 0 ≤ Y z 2 ∧ Y z 2 ≤ (1 / 10000) / k) :
    |Y b 0 - k| ≤ 16 * (Y a 1 + (Y a 2) ^ 2 / k) := by
  have hmem (z : ℝ) (hz : z ∈ Icc (a + z₀) (b + z₀)) : z - z₀ ∈ Icc a b := by
    constructor <;> linarith only [hz.1, hz.2]
  have hsol (z : ℝ) (hz : z ∈ Icc (a + z₀) (b + z₀)) :
      HasDerivAt (fun u => Y (u - z₀)) (coreAngleField z (Y (z - z₀))) z := by
    have H := (hY (z - z₀) (hmem z hz)).scomp z ((hasDerivAt_id z).sub_const z₀)
    simp only [sub_add_cancel, one_smul] at H
    convert! H using 1
  have H := partialCoreAngle_radius_drift (Y := fun z => Y (z - z₀))
    (by linarith only [hab] : a + z₀ ≤ b + z₀) hk hsol
    (by simpa only [add_sub_cancel_right] using hinit)
    (fun z hz => hr _ (hmem z hz))
    (fun z hz => by simpa only [sub_add_cancel] using hv _ (hmem z hz))
    (fun z hz => hu _ (hmem z hz)) (fun z hz => hp _ (hmem z hz))
  simpa only [add_sub_cancel_right] using H

end BianchiIX
