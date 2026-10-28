import BianchiIX.Dynamics.StableCorrectedTail

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem stableCorrectedApproximation_uniform_tail {m c u w T : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 80)
    (hu : |u| ≤ 1 / 200) (hw : |w| ≤ 1 / 200) (hT : 0 ≤ T) :
    |stableBoundaryProjection m u w - stableCorrectedApproximation ![m, u, w] T| ≤
      8192 * Real.exp (-(3 / 8) * T) := by
  have hU : |u| ≤ 1 := by linarith
  have hb : |u| + |w| ≤ 2 := by linarith
  have hb3 := pow_le_pow_left₀ (by positivity : 0 ≤ |u| + |w|) hb 3
  have hprod := mul_le_mul hU hb3 (by positivity : 0 ≤ (|u| + |w|) ^ 3) (by norm_num : (0 : ℝ) ≤ 1)
  have hnum : 1024 * |u| * (|u| + |w|) ^ 3 ≤ 8192 := by nlinarith only [hprod]
  have hden : 1 ≤ (c + 1) ^ 3 := by
    have H := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) (by linarith : 1 ≤ c + 1) 3
    simpa only [one_pow] using H
  have hconst := (div_le_self (by positivity : 0 ≤ 1024 * |u| * (|u| + |w|) ^ 3) hden).trans hnum
  exact (stableCorrectedApproximation_tail hc hm hu hw hT).trans
    (mul_le_mul_of_nonneg_right hconst (Real.exp_pos _).le)

theorem continuousAt_stableBoundaryProjection {y : Fin 3 → ℝ}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) :
    ContinuousAt (fun z : Fin 3 → ℝ => stableBoundaryProjection (z 0) (z 1) (z 2)) y := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have heps : 0 < ε / 3 := by positivity
  have hexp : Tendsto (fun T : ℝ => 8192 * Real.exp (-(3 / 8) * T)) atTop (𝓝 0) := by
    have H := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 3 / 8) tendsto_id)).const_mul 8192
    simpa only [Function.comp_def, neg_mul, mul_zero, id_eq] using H
  obtain ⟨T, hT, hsmall⟩ := (eventually_ge_atTop (0 : ℝ) |>.and
    (hexp.eventually (gt_mem_nhds heps))).exists
  have hfinite : ContinuousAt (fun z : Fin 3 → ℝ => stableCorrectedApproximation z T) y := by
    have H := (contDiffAt_stableCorrectedApproximation_two hm (by simp : |y 0 - y 0| ≤ (1 : ℝ) / 40)
      hu.le hw.le hT).continuousAt
    exact H.comp (f := fun z : Fin 3 → ℝ => (z, T)) (continuousAt_id.prodMk continuousAt_const)
  have hnear := Metric.tendsto_nhds.mp hfinite (ε / 3) heps
  have hmc : ContinuousAt (fun z : Fin 3 → ℝ => |z 0 - y 0|) y :=
    ((continuous_apply 0).continuousAt.sub continuousAt_const).abs
  have huc : ContinuousAt (fun z : Fin 3 → ℝ => |z 1|) y := (continuous_apply 1).continuousAt.abs
  have hwc : ContinuousAt (fun z : Fin 3 → ℝ => |z 2|) y := (continuous_apply 2).continuousAt.abs
  have hbox : ∀ᶠ z in 𝓝 y, |z 0 - y 0| ≤ 1 / 80 ∧ |z 1| ≤ 1 / 200 ∧ |z 2| ≤ 1 / 200 := by
    filter_upwards [hmc.eventually (isOpen_Iio.mem_nhds (by simp : |y 0 - y 0| < (1 : ℝ) / 80)),
      huc.eventually (isOpen_Iio.mem_nhds hu), hwc.eventually (isOpen_Iio.mem_nhds hw)] with z hz hzu hzw
    exact ⟨hz.le, hzu.le, hzw.le⟩
  have hyvec : (![y 0, y 1, y 2] : Fin 3 → ℝ) = y := by ext i; fin_cases i <;> rfl
  have hytail := stableCorrectedApproximation_uniform_tail hm (by simp : |y 0 - y 0| ≤ (1 : ℝ) / 80)
    hu.le hw.le hT
  rw [hyvec] at hytail
  filter_upwards [hbox, hnear] with z hz hzn
  have hzvec : (![z 0, z 1, z 2] : Fin 3 → ℝ) = z := by ext i; fin_cases i <;> rfl
  have hztail := stableCorrectedApproximation_uniform_tail hm hz.1 hz.2.1 hz.2.2 hT
  rw [hzvec] at hztail
  rw [Real.dist_eq] at hzn ⊢
  have htri := abs_sub_le (stableBoundaryProjection (z 0) (z 1) (z 2))
    (stableCorrectedApproximation z T) (stableBoundaryProjection (y 0) (y 1) (y 2))
  have htri' := abs_sub_le (stableCorrectedApproximation z T)
    (stableCorrectedApproximation y T) (stableBoundaryProjection (y 0) (y 1) (y 2))
  rw [abs_sub_comm (stableCorrectedApproximation y T)] at htri'
  linarith

end BianchiIX
