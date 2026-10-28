import BianchiIX.Dynamics.CoreLogDerivativeBounds

noncomputable section

namespace BianchiIX

open Set MeasureTheory

theorem coreLogRates_strong_decay {k z : ℝ} {Y : CoreAngleState} (hk : 6 ≤ k)
    (hr : 99 / 100 * k ≤ Y 0)
    (hu : 0 ≤ Y 1 ∧ Y 1 ≤ (1 / 10000) / k)
    (hw : 0 ≤ Y 2 / (Y 0 / Real.cosh z) ∧ Y 2 / (Y 0 / Real.cosh z) ≤ (1 / 10000) / k) :
    coreLogRates z Y 0 ≤ -k / 4 := by
  have hr0 : 0 < Y 0 := by linarith only [hk, hr]
  have hv : Y 0 / Real.cosh z ≤ Y 0 :=
    (div_le_iff₀ (Real.cosh_pos z)).mpr (le_mul_of_one_le_right hr0.le (Real.one_le_cosh z))
  have H := coreBootstrap_strong_rate hk hr hv
    (show -1 ≤ -Real.tanh z by linarith [Real.tanh_lt_one z]) hu hw
  convert! H using 1
  dsimp [coreLogRates, coreAuxiliary]
  congr 1
  field_simp
  ring

/-- Original-time rates remain strictly negative even when either wall amplitude vanishes. -/
theorem coreRegion_original_log_rate_decay {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) :
    coreOriginalLogRates y 0 ≤ (-k ^ 2 / 10) * (6 / projectiveStateDenom y) ∧
      coreOriginalLogRates y 1 ≤ -2 * (6 / projectiveStateDenom y) := by
  let r := coreRadius (y 0) (y 2)
  let d := coreClockFactor r (y 1) (y 3)
  let a := 6 / projectiveStateDenom y
  have hk0 : 0 < k := by linarith only [hk]
  have hv : 0 < y 2 := lt_of_lt_of_le zero_lt_one hy.2.1
  have hr := (coreRegion_radius_bounds hk hy).1
  have hr0 : 0 < r := coreRadius_pos hv
  obtain ⟨hu, hw⟩ := coreRegion_wall_bounds hy
  have hd := coreBootstrap_clock_bounds hk hr hu hw
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 999 / 1000) hd.1
  have ha : 0 ≤ a := (div_pos (by norm_num) (coreRegion_clock_regular hk hy).1).le
  have hW : (toCoreAngleState y) 2 / ((toCoreAngleState y) 0 / Real.cosh (projectiveCoreAngle y)) = y 3 := by
    change y 2 * y 3 / (r / Real.cosh (coreAngle (y 0) (y 2))) = _
    rw [(coreAngle_coordinates hv).1, mul_div_cancel_left₀ _ (ne_of_gt hv)]
  have hstrong := coreLogRates_strong_decay (Y := toCoreAngleState y) (z := projectiveCoreAngle y)
    hk hr hu (by simpa only [hW] using hw)
  have hrd : k / 2 ≤ r * d := by
    have H := mul_le_mul hr hd.1 (by norm_num : (0 : ℝ) ≤ 999 / 1000) hr0.le
    nlinarith only [H, hk]
  have hrq : 0 ≤ r * d := mul_nonneg hr0.le hd0.le
  have hC := coreBootstrap_coupling_nonneg hk hy.2.1 hu hw.1
  constructor
  · have H := mul_le_mul_of_nonneg_left hstrong hrq
    have H' := mul_le_mul_of_nonpos_right hrd (show -k / 4 ≤ 0 by linarith only [hk])
    have hcoef : r * d * coreLogRates (projectiveCoreAngle y) (toCoreAngleState y) 0 ≤ -k ^ 2 / 10 := by
      nlinarith only [H, H', sq_nonneg k]
    have H'' := mul_le_mul_of_nonneg_left hcoef ha
    convert! H'' using 1 <;> dsimp [coreOriginalLogRates, coreOriginalClockRate, a, r, d] <;> ring
  · have hid : r * d * coreLogRates (projectiveCoreAngle y) (toCoreAngleState y) 1 =
        -2 * (1 + coupling (y 1) (y 2) (y 3)) := by
      change r * d * (-2 * (1 + coreAuxiliary (projectiveCoreAngle y) (toCoreAngleState y) 0) /
        (r * coreAuxiliary (projectiveCoreAngle y) (toCoreAngleState y) 1)) = _
      rw [coreAuxiliary_projective_clockFactor hv]
      have hq : coreAuxiliary (projectiveCoreAngle y) (toCoreAngleState y) 0 =
          coupling (y 1) (y 2) (y 3) := by
        change coupling (y 1) (r / Real.cosh (coreAngle (y 0) (y 2)))
          (y 2 * y 3 / (r / Real.cosh (coreAngle (y 0) (y 2)))) = _
        rw [(coreAngle_coordinates hv).1, mul_div_cancel_left₀ _ (ne_of_gt hv)]
      rw [hq]
      change r * d * (-2 * (1 + coupling (y 1) (y 2) (y 3)) / (r * d)) = _
      field_simp
    have H := mul_le_mul_of_nonneg_left (show r * d *
        coreLogRates (projectiveCoreAngle y) (toCoreAngleState y) 1 ≤ -2 by rw [hid]; linarith only [hC]) ha
    convert! H using 1 <;> dsimp [coreOriginalLogRates, coreOriginalClockRate, a, r, d] <;> ring

theorem coreFlowMultiplier_projective_decay {y : ProjectiveState} {t₀ k a b : ℝ}
    (hk : 6 ≤ k) (hab : a ≤ b) (hD : 0 < projectiveStateDenom y)
    (hdom : Icc a b ⊆ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : ∀ t ∈ Icc a b, 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hcore : ∀ t ∈ Icc a b, coreRegion k (projectiveOriginalFlow y t₀ t)) :
    let Δ := integralClock (normalizedProjectiveRate (fromProjectiveState y) t₀) a b
    coreFlowMultiplier y t₀ a b 0 ≤ Real.exp ((-k ^ 2 / 10) * Δ) ∧
      coreFlowMultiplier y t₀ a b 1 ≤ Real.exp (-2 * Δ) := by
  intro Δ
  have hrate := (continuousOn_normalizedProjectiveRate (fromProjectiveState y) t₀).mono hdom
  have hlog := continuousOn_coreFlow_log_rates hk hD hdom hA hcore
  have hscale (t : ℝ) (ht : t ∈ Icc a b) :
      6 / projectiveStateDenom (projectiveOriginalFlow y t₀ t) =
        normalizedProjectiveRate (fromProjectiveState y) t₀ t :=
    projective_inverse_scale (ne_of_gt (hA t ht))
      ((normalizedMaxCurve_constraint (hdom ht)).trans (fromProjectiveState_constraint (ne_of_gt hD)))
  have H (i : Fin 2) (c : ℝ)
      (hc : ∀ t ∈ Icc a b, coreOriginalLogRates (projectiveOriginalFlow y t₀ t) i ≤
        c * (6 / projectiveStateDenom (projectiveOriginalFlow y t₀ t))) :
      coreFlowMultiplier y t₀ a b i ≤ Real.exp (c * Δ) := by
    apply Real.exp_le_exp.mpr
    have HI := intervalIntegral.integral_mono_on (μ := volume) hab
      ((continuousOn_pi.mp hlog i).intervalIntegrable_of_Icc hab)
      ((continuousOn_const.mul hrate).intervalIntegrable_of_Icc hab)
      (fun t ht => by simpa only [Pi.mul_apply, hscale t ht] using hc t ht)
    simpa only [Pi.mul_apply, intervalIntegral.integral_const_mul, Δ, integralClock] using HI
  exact ⟨H 0 _ (fun t ht => (coreRegion_original_log_rate_decay hk (hcore t ht)).1),
    H 1 _ (fun t ht => (coreRegion_original_log_rate_decay hk (hcore t ht)).2)⟩

/-- The multiplier itself contracts at every admissible first return, including zero-wall entries. -/
theorem coreReturnMultiplier_contraction {Y : CoreAngleState} {T : ℝ} (hk : 6 ≤ Y 0)
    (hu : 0 ≤ Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0)
    (hw : 0 ≤ Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0)
    (hfirst : IsLeast {t | 0 < t ∧ projectiveOriginalFlow (coreRadiusEntry Y) 0 t 2 = 1} T) :
    coreFlowMultiplier (coreRadiusEntry Y) 0 0 T 0 ≤ Real.exp (-Y 0 / 40) ∧
      coreFlowMultiplier (coreRadiusEntry Y) 0 0 T 1 ≤ Real.exp (-1 / (2 * Y 0)) := by
  have hk0 : 0 < Y 0 := by linarith only [hk]
  have hD := (coreRegion_clock_regular hk (coreRadiusEntry_region hk hu hw)).1
  have hc := fromProjectiveState_constraint (ne_of_gt hD)
  obtain ⟨S, _, hfirstS, hcore, _, _, _, _, _, _, htime, _⟩ := exists_large_core_traversal hk hu hw
  have hST : S = T := hfirstS.unique hfirst
  subst S
  have H := coreFlowMultiplier_projective_decay hk hfirst.1.1.le hD
    (fun t ht => normalizedMaxDomain_contains_Ici_of_constraint hc 0 ht.1)
    (fun t ht => (hcore t ht).1) (fun t ht => (hcore t ht).2)
  constructor
  · apply H.1.trans (Real.exp_le_exp.mpr ?_)
    calc
      _ ≤ (-Y 0 ^ 2 / 10) * (1 / (4 * Y 0)) :=
        mul_le_mul_of_nonpos_left htime (by nlinarith only [sq_nonneg (Y 0)])
      _ = _ := by field_simp; ring
  · apply H.2.trans (Real.exp_le_exp.mpr ?_)
    calc
      _ ≤ -2 * (1 / (4 * Y 0)) := mul_le_mul_of_nonpos_left htime (by norm_num)
      _ = _ := by field_simp; ring

end BianchiIX
