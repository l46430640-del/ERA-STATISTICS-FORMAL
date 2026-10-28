import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped Topology ENNReal

def clippedPowerDensity (ell B δ x : ℝ) : ℝ := min ell (B * x ^ δ) / x

theorem clippedPowerDensity_nonneg {ell B δ x : ℝ} (hl : 0 ≤ ell) (hB : 0 ≤ B)
    (hx : 0 ≤ x) : 0 ≤ clippedPowerDensity ell B δ x :=
  div_nonneg (le_min hl (mul_nonneg hB (Real.rpow_nonneg hx δ))) hx

theorem measurable_clippedPowerDensity {δ : ℝ} (hδ : 0 ≤ δ) (ell B : ℝ) :
    Measurable (clippedPowerDensity ell B δ) :=
  (measurable_const.min (measurable_const.mul (Real.continuous_rpow_const hδ).measurable)).div
    measurable_id

theorem clippedPowerDensity_le {ell B δ x : ℝ} (hx : 0 < x) :
    clippedPowerDensity ell B δ x ≤ B * x ^ (δ - 1) := by
  calc
    clippedPowerDensity ell B δ x ≤ B * x ^ δ / x := div_le_div_of_nonneg_right (min_le_right _ _) hx.le
    _ = B * x ^ (δ - 1) := by rw [Real.rpow_sub hx, Real.rpow_one]; ring

theorem intervalIntegrable_clippedPowerDensity {ell B δ r : ℝ}
    (hl : 0 ≤ ell) (hB : 0 ≤ B) (hδ : 0 < δ) (hr : 0 ≤ r) :
    IntervalIntegrable (clippedPowerDensity ell B δ) volume 0 r := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hr]
  have H : IntegrableOn (fun x : ℝ => B * x ^ (δ - 1)) (Ioo 0 r) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hr).mp
      ((intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < δ - 1)).const_mul B)
  refine H.mono' (measurable_clippedPowerDensity hδ.le ell B).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (clippedPowerDensity_nonneg hl hB hx.1.le)]
  exact clippedPowerDensity_le hx.1

theorem integral_power_density {δ : ℝ} (hδ : 0 < δ) (B r : ℝ) :
    (∫ x in (0 : ℝ)..r, B * x ^ (δ - 1)) = B * r ^ δ / δ := by
  rw [intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by linarith : -1 < δ - 1))]
  simp only [sub_add_cancel, Real.zero_rpow (ne_of_gt hδ), sub_zero]
  ring

theorem clippedPowerDensity_below {ell B δ x c : ℝ} (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hx : 0 < x) (hxc : x ≤ c) (hc : B * c ^ δ = ell) :
    clippedPowerDensity ell B δ x = B * x ^ (δ - 1) := by
  have H : B * x ^ δ ≤ ell := by
    rw [← hc]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx.le hxc hδ) hB
  rw [clippedPowerDensity, min_eq_right H, Real.rpow_sub hx, Real.rpow_one]
  ring

theorem clippedPowerDensity_above {ell B δ x c : ℝ} (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hc0 : 0 ≤ c) (hcx : c ≤ x) (hc : B * c ^ δ = ell) :
    clippedPowerDensity ell B δ x = ell / x := by
  have H : ell ≤ B * x ^ δ := by
    rw [← hc]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hc0 hcx hδ) hB
  exact congrArg (fun z => z / x) (min_eq_left H)

theorem integral_clippedPowerDensity_of_cutoff {ell B δ c : ℝ}
    (hl : 0 ≤ ell) (hB : 0 ≤ B) (hδ : 0 < δ)
    (hc0 : 0 < c) (hc1 : c ≤ 1) (hc : B * c ^ δ = ell) :
    (∫ x in (0 : ℝ)..1, clippedPowerDensity ell B δ x) = ell / δ + ell * Real.log (1 / c) := by
  have hi0c := intervalIntegrable_clippedPowerDensity hl hB hδ hc0.le
  have hi01 := intervalIntegrable_clippedPowerDensity hl hB hδ (by norm_num : (0 : ℝ) ≤ 1)
  have hleft : (∫ x in (0 : ℝ)..c, clippedPowerDensity ell B δ x) = ell / δ := by
    rw [intervalIntegral.integral_congr_Ioo_of_le hc0.le
      (fun x hx => clippedPowerDensity_below hB hδ.le hx.1 hx.2.le hc),
      integral_power_density hδ, hc]
  have hright : (∫ x in c..(1 : ℝ), clippedPowerDensity ell B δ x) = ell * Real.log (1 / c) := by
    rw [intervalIntegral.integral_congr_Ioo_of_le hc1
      (fun x hx => clippedPowerDensity_above hB hδ.le hc0.le hx.1.le hc)]
    simp_rw [div_eq_mul_inv]
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hc0 (by norm_num)]
    simp only [one_div, one_mul]
  rw [← intervalIntegral.integral_add_adjacent_intervals hi0c (hi0c.symm.trans hi01), hleft, hright]

theorem integral_clippedPowerDensity_of_le {ell B δ : ℝ}
    (hB : 0 ≤ B) (hδ : 0 < δ) (hBl : B ≤ ell) :
    (∫ x in (0 : ℝ)..1, clippedPowerDensity ell B δ x) = B / δ := by
  calc
    _ = ∫ x in (0 : ℝ)..1, B * x ^ (δ - 1) := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro x hx
      have hp : B * x ^ δ ≤ ell :=
        (mul_le_of_le_one_right hB (Real.rpow_le_one hx.1.le hx.2.le hδ.le)).trans hBl
      dsimp only
      rw [clippedPowerDensity, min_eq_right hp, Real.rpow_sub hx.1, Real.rpow_one]
      ring
    _ = B / δ := by rw [integral_power_density hδ]; simp

theorem integral_clippedPowerDensity {ell B δ : ℝ} (hl : 0 < ell) (hB : 0 < B) (hδ : 0 < δ) :
    (∫ x in (0 : ℝ)..1, clippedPowerDensity ell B δ x) =
      min ell B / δ * (1 + max (Real.log (B / ell)) 0) := by
  by_cases hBl : B ≤ ell
  · have heq := integral_clippedPowerDensity_of_le hB.le hδ hBl
    have hlog : Real.log (B / ell) ≤ 0 :=
      Real.log_nonpos (div_nonneg hB.le hl.le) ((div_le_one hl).mpr hBl)
    rw [heq, min_eq_right hBl, max_eq_right hlog]
    ring
  · have hlB : ell ≤ B := (lt_of_not_ge hBl).le
    let c : ℝ := (ell / B) ^ δ⁻¹
    have hc0 : 0 < c := Real.rpow_pos_of_pos (div_pos hl hB) _
    have hc1 : c ≤ 1 := Real.rpow_le_one (div_nonneg hl.le hB.le)
      ((div_le_one hB).mpr hlB) (inv_nonneg.mpr hδ.le)
    have hc : B * c ^ δ = ell := by
      dsimp only [c]
      rw [Real.rpow_inv_rpow (div_nonneg hl.le hB.le) (ne_of_gt hδ)]
      field_simp
    have hlogc : Real.log (1 / c) = Real.log (B / ell) / δ := by
      rw [one_div, Real.log_inv]
      dsimp only [c]
      rw [Real.log_rpow (div_pos hl hB),
        Real.log_div (ne_of_gt hl) (ne_of_gt hB), Real.log_div (ne_of_gt hB) (ne_of_gt hl)]
      ring
    have hlog : 0 ≤ Real.log (B / ell) := Real.log_nonneg ((one_le_div hl).mpr hlB)
    rw [integral_clippedPowerDensity_of_cutoff hl.le hB.le hδ hc0 hc1 hc,
      hlogc, min_eq_left hlB, max_eq_left hlog]
    ring

def clippedPowerDensityTwo (ell B δ x : ℝ) : ℝ :=
  (∫ y in (0 : ℝ)..1, clippedPowerDensity ell (B * x ^ δ) δ y) / x

theorem clippedPowerDensityTwo_below {ell B δ x : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ)
    (hx : 0 < x) (hsmall : B * x ^ δ ≤ ell) :
    clippedPowerDensityTwo ell B δ x = (B / δ) * x ^ (δ - 1) := by
  rw [clippedPowerDensityTwo,
    integral_clippedPowerDensity_of_le (mul_nonneg hB (Real.rpow_nonneg hx.le _)) hδ hsmall,
    Real.rpow_sub hx, Real.rpow_one]
  ring

theorem clippedPowerDensityTwo_above {ell B δ x c : ℝ} (hl : 0 < ell) (hB : 0 < B) (hδ : 0 < δ)
    (hc0 : 0 < c) (hcx : c ≤ x) (hc : B * c ^ δ = ell) :
    clippedPowerDensityTwo ell B δ x =
      (ell / δ - ell * Real.log c + ell * Real.log x) / x := by
  have hx : 0 < x := hc0.trans_le hcx
  have hp : 0 < B * x ^ δ := mul_pos hB (Real.rpow_pos_of_pos hx _)
  have hlarge : ell ≤ B * x ^ δ := by
    rw [← hc]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hc0.le hcx hδ.le) hB.le
  have hlog : 0 ≤ Real.log (B * x ^ δ / ell) := Real.log_nonneg ((one_le_div hl).mpr hlarge)
  have hlogell : Real.log ell = Real.log B + δ * Real.log c := by
    rw [← hc, Real.log_mul (ne_of_gt hB) (ne_of_gt (Real.rpow_pos_of_pos hc0 δ)), Real.log_rpow hc0]
  rw [clippedPowerDensityTwo, integral_clippedPowerDensity hl hp hδ,
    min_eq_left hlarge, max_eq_left hlog, Real.log_div (ne_of_gt hp) (ne_of_gt hl),
    Real.log_mul (ne_of_gt hB) (ne_of_gt (Real.rpow_pos_of_pos hx δ)), Real.log_rpow hx, hlogell]
  field_simp
  ring

theorem intervalIntegrable_log_affine_density {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (A D : ℝ) :
    IntervalIntegrable (fun x : ℝ => (A + D * Real.log x) / x) volume c 1 := by
  apply ContinuousOn.intervalIntegrable_of_Icc hc1
  apply (continuousOn_const.add (continuousOn_const.mul (continuousOn_id.log ?_))).div continuousOn_id
  · intro x hx
    exact ne_of_gt (hc0.trans_le hx.1)
  · intro x hx
    exact ne_of_gt (hc0.trans_le hx.1)

theorem integral_log_affine_density {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (A D : ℝ) :
    (∫ x in c..(1 : ℝ), (A + D * Real.log x) / x) =
      -(A * Real.log c + D / 2 * (Real.log c) ^ 2) := by
  have hd (x : ℝ) (hx : x ∈ uIcc c 1) :
      HasDerivAt (fun y => A * Real.log y + D / 2 * (Real.log y) ^ 2)
        ((A + D * Real.log x) / x) x := by
    have hx0 : 0 < x := hc0.trans_le ((uIcc_of_le hc1 ▸ hx).1)
    have H := ((Real.hasDerivAt_log (ne_of_gt hx0)).const_mul A).add
      (((Real.hasDerivAt_log (ne_of_gt hx0)).pow 2).const_mul (D / 2))
    convert! H using 1
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (intervalIntegrable_log_affine_density hc0 hc1 A D)]
  simp

theorem integral_clippedPowerDensityTwo_of_cutoff {ell B δ c : ℝ}
    (hl : 0 < ell) (hB : 0 < B) (hδ : 0 < δ)
    (hc0 : 0 < c) (hc1 : c ≤ 1) (hc : B * c ^ δ = ell) :
    IntervalIntegrable (clippedPowerDensityTwo ell B δ) volume 0 1 ∧
      (∫ x in (0 : ℝ)..1, clippedPowerDensityTwo ell B δ x) =
        ell / δ ^ 2 - ell / δ * Real.log c + ell / 2 * (Real.log c) ^ 2 := by
  have hbelow : EqOn (clippedPowerDensityTwo ell B δ) (fun x => (B / δ) * x ^ (δ - 1)) (Ioo 0 c) := by
    intro x hx
    apply clippedPowerDensityTwo_below hB.le hδ hx.1
    rw [← hc]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx.1.le hx.2.le hδ.le) hB.le
  have habove : EqOn (clippedPowerDensityTwo ell B δ)
      (fun x => (ell / δ - ell * Real.log c + ell * Real.log x) / x) (Ioo c 1) :=
    fun _ hx => clippedPowerDensityTwo_above hl hB hδ hc0 hx.1.le hc
  have hi0c : IntervalIntegrable (clippedPowerDensityTwo ell B δ) volume 0 c := by
    apply ((intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < δ - 1)).const_mul (B / δ)).congr_uIoo
    simpa only [uIoo_of_le hc0.le] using hbelow.symm
  have hic1 : IntervalIntegrable (clippedPowerDensityTwo ell B δ) volume c 1 := by
    apply (intervalIntegrable_log_affine_density hc0 hc1 (ell / δ - ell * Real.log c) ell).congr_uIoo
    simpa only [uIoo_of_le hc1] using habove.symm
  refine ⟨hi0c.trans hic1, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hi0c hic1,
    intervalIntegral.integral_congr_Ioo_of_le hc0.le hbelow,
    intervalIntegral.integral_congr_Ioo_of_le hc1 habove,
    integral_power_density hδ,
    integral_log_affine_density hc0 hc1 (ell / δ - ell * Real.log c) ell]
  calc
    _ = (B * c ^ δ) / δ ^ 2 - ell / δ * Real.log c + ell / 2 * (Real.log c) ^ 2 := by ring
    _ = _ := by rw [hc]

theorem integral_clippedPowerDensityTwo {ell B δ : ℝ} (hl : 0 < ell) (hB : 0 < B) (hδ : 0 < δ) :
    IntervalIntegrable (clippedPowerDensityTwo ell B δ) volume 0 1 ∧
      (∫ x in (0 : ℝ)..1, clippedPowerDensityTwo ell B δ x) =
        min ell B / δ ^ 2 *
          (1 + max (Real.log (B / ell)) 0 + (max (Real.log (B / ell)) 0) ^ 2 / 2) := by
  by_cases hBl : B ≤ ell
  · have heq : EqOn (clippedPowerDensityTwo ell B δ) (fun x => (B / δ) * x ^ (δ - 1)) (Ioo 0 1) := by
      intro x hx
      apply clippedPowerDensityTwo_below hB.le hδ hx.1
      exact (mul_le_of_le_one_right hB.le (Real.rpow_le_one hx.1.le hx.2.le hδ.le)).trans hBl
    have hi : IntervalIntegrable (clippedPowerDensityTwo ell B δ) volume 0 1 := by
      apply ((intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < δ - 1)).const_mul (B / δ)).congr_uIoo
      simpa only [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)] using heq.symm
    have hlog : Real.log (B / ell) ≤ 0 := Real.log_nonpos (div_nonneg hB.le hl.le) ((div_le_one hl).mpr hBl)
    refine ⟨hi, ?_⟩
    rw [intervalIntegral.integral_congr_Ioo_of_le (by norm_num) heq, integral_power_density hδ,
      min_eq_right hBl, max_eq_right hlog]
    simp
    ring
  · have hlB : ell ≤ B := (lt_of_not_ge hBl).le
    let c : ℝ := (ell / B) ^ δ⁻¹
    have hc0 : 0 < c := Real.rpow_pos_of_pos (div_pos hl hB) _
    have hc1 : c ≤ 1 := Real.rpow_le_one (div_nonneg hl.le hB.le)
      ((div_le_one hB).mpr hlB) (inv_nonneg.mpr hδ.le)
    have hc : B * c ^ δ = ell := by
      dsimp only [c]
      rw [Real.rpow_inv_rpow (div_nonneg hl.le hB.le) (ne_of_gt hδ)]
      field_simp
    have hlogc : Real.log c = -Real.log (B / ell) / δ := by
      dsimp only [c]
      rw [Real.log_rpow (div_pos hl hB), Real.log_div (ne_of_gt hl) (ne_of_gt hB),
        Real.log_div (ne_of_gt hB) (ne_of_gt hl)]
      ring
    have hlog : 0 ≤ Real.log (B / ell) := Real.log_nonneg ((one_le_div hl).mpr hlB)
    have H := integral_clippedPowerDensityTwo_of_cutoff hl hB hδ hc0 hc1 hc
    refine ⟨H.1, ?_⟩
    rw [H.2, hlogc, min_eq_left hlB, max_eq_left hlog]
    ring

private theorem lintegral_unit_ofReal_eq {f : ℝ → ℝ}
    (hi : IntervalIntegrable f volume 0 1) (hn : ∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ f x) :
    (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (f x)) = ENNReal.ofReal (∫ x in (0 : ℝ)..1, f x) := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_Ioc_eq_integral_Ioo]
  symm
  apply ofReal_integral_eq_lintegral_ofReal
  · exact (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp hi
  · exact ae_restrict_of_forall_mem measurableSet_Ioo hn

theorem lintegral_clipped_log_one {ell B δ : ℝ} (hl : 0 < ell) (hB : 0 < B) (hδ : 0 < δ) :
    (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (min ell (B * x ^ δ) / x)) =
      ENNReal.ofReal (min ell B / δ * (1 + max (Real.log (B / ell)) 0)) := by
  exact (lintegral_unit_ofReal_eq (intervalIntegrable_clippedPowerDensity hl.le hB.le hδ (by norm_num))
    (fun _ hx => clippedPowerDensity_nonneg hl.le hB.le hx.1.le)).trans
      (congrArg ENNReal.ofReal (integral_clippedPowerDensity hl hB hδ))

theorem lintegral_clipped_log_two {ell B δ : ℝ} (hl : 0 < ell) (hB : 0 < B) (hδ : 0 < δ) :
    (∫⁻ x in Ioo (0 : ℝ) 1, ∫⁻ y in Ioo (0 : ℝ) 1,
      ENNReal.ofReal (min ell (B * (x * y) ^ δ) / (x * y))) =
      ENNReal.ofReal (min ell B / δ ^ 2 *
        (1 + max (Real.log (B / ell)) 0 + (max (Real.log (B / ell)) 0) ^ 2 / 2)) := by
  have hinner (x : ℝ) (hx : 0 < x) :
      (∫⁻ y in Ioo (0 : ℝ) 1, ENNReal.ofReal (min ell (B * (x * y) ^ δ) / (x * y))) =
        ENNReal.ofReal (clippedPowerDensityTwo ell B δ x) := by
    have hp : 0 ≤ B * x ^ δ := mul_nonneg hB.le (Real.rpow_nonneg hx.le δ)
    have heq (y : ℝ) (hy : 0 < y) : min ell (B * (x * y) ^ δ) / (x * y) =
        clippedPowerDensity ell (B * x ^ δ) δ y / x := by
      rw [Real.mul_rpow hx.le hy.le, clippedPowerDensity, ← mul_assoc]
      ring
    calc
      _ = ∫⁻ y in Ioo (0 : ℝ) 1, ENNReal.ofReal (clippedPowerDensity ell (B * x ^ δ) δ y / x) := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
        rw [heq y hy.1]
      _ = ENNReal.ofReal (∫ y in (0 : ℝ)..1, clippedPowerDensity ell (B * x ^ δ) δ y / x) :=
        lintegral_unit_ofReal_eq
          ((intervalIntegrable_clippedPowerDensity hl.le hp hδ (by norm_num)).div_const x)
          (fun _ hy => div_nonneg (clippedPowerDensity_nonneg hl.le hp hy.1.le) hx.le)
      _ = ENNReal.ofReal (clippedPowerDensityTwo ell B δ x) := by
        rw [intervalIntegral.integral_div]
        rfl
  have hnonneg (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : 0 ≤ clippedPowerDensityTwo ell B δ x := by
    apply div_nonneg _ hx.1.le
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro y hy
    exact clippedPowerDensity_nonneg hl.le
      (mul_nonneg hB.le (Real.rpow_nonneg hx.1.le δ)) hy.1
  calc
    _ = ∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (clippedPowerDensityTwo ell B δ x) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact hinner x hx.1
    _ = ENNReal.ofReal (∫ x in (0 : ℝ)..1, clippedPowerDensityTwo ell B δ x) :=
      lintegral_unit_ofReal_eq (integral_clippedPowerDensityTwo hl hB hδ).1 hnonneg
    _ = _ := by rw [(integral_clippedPowerDensityTwo hl hB hδ).2]

end BianchiIX
