import BianchiIX.Dynamics.CoreLogIntegralVariation
import BianchiIX.Dynamics.CoreStrongIntegrals

noncomputable section

namespace BianchiIX

open Set MeasureTheory

theorem core_log_lower_bound {k : ℝ} (hk : 6 ≤ k) : 1 ≤ Real.log (4 * k) := by
  have H := Real.le_log_one_add_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)
  norm_num at H
  exact H.trans (Real.log_le_log (by norm_num) (by linarith only [hk]))

/-- The strongly damped component supplies the extra inverse-radius power for the weak multiplier. -/
theorem coreFlow_log_integral_bounds {y : ProjectiveState} {t₀ k a b Q : ℝ}
    (hk : 6 ≤ k) (hab : a ≤ b) (hD : 0 < projectiveStateDenom y)
    (hdom : Icc a b ⊆ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : ∀ t ∈ Icc a b, 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hcore : ∀ t ∈ Icc a b, coreRegion k (projectiveOriginalFlow y t₀ t))
    (hentry : Real.cosh (projectiveCoreAngle (projectiveOriginalFlow y t₀ a)) = k)
    (w : ProjectiveState)
    (hQ : ∀ t ∈ Icc a b, ‖scaleCoreVariation k (coreProjectedFlowVariation y t₀ t w)‖ ≤ Q) :
    let β := projectiveOriginalFlow y t₀
    let I := fun i : Fin 2 => ∫ t in a..b, coreOriginalClockRate (β t) *
      (fderiv ℝ (coreLogRates (projectiveCoreAngle (β t))) (toCoreAngleState (β t))
        (coreProjectedFlowVariation y t₀ t w)) i
    |I 0| ≤ 6 * Real.log (4 * k) * Q ∧
      |I 1| ≤ 51 * Real.log (4 * k) * Q / k ^ 2 := by
  intro β I
  let θ := fun t => projectiveCoreAngle (β t)
  let rate := fun t => coreOriginalClockRate (β t)
  let x := fun t => k * coreProjectedFlowVariation y t₀ t w 1
  have hk0 : 0 < k := by linarith only [hk]
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hQ0 : 0 ≤ Q := (norm_nonneg _).trans (hQ a ha)
  have hV (t : ℝ) (ht : t ∈ Icc a b) : 0 < β t 2 :=
    lt_of_lt_of_le zero_lt_one (hcore t ht).2.1
  have hflow (t : ℝ) (ht : t ∈ Icc a b) := hasDerivAt_projectiveOriginalFlow_time hD (hdom ht) (hA t ht)
  have hθ (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt θ (rate t) t :=
    hasDerivAt_coreAngle_scaled (hflow t ht) (hV t ht)
  have hrate : ContinuousOn rate (Icc a b) := by
    intro t ht
    exact ((contDiffAt_coreOriginalClockRate 1 (hV t ht)
      (ne_of_gt (coreRegion_clock_regular hk (hcore t ht)).1)).continuousAt.comp
        (hflow t ht).continuousAt).continuousWithinAt
  have hpos (t : ℝ) (ht : t ∈ Icc a b) : 0 ≤ rate t :=
    (coreRegion_clock_regular hk (hcore t ht)).2.2.le
  have hx : ContinuousOn x (Icc a b) := by
    intro t ht
    have H := hasDerivAt_coreProjectedFlowVariation hD (hdom ht) (hA t ht) (hV t ht)
      (ne_of_gt (coreRegion_clock_regular hk (hcore t ht)).2.1) w
    exact ((hasDerivAt_pi.mp H 1).const_mul k).continuousAt.continuousWithinAt
  have hspan : (∫ t in a..b, rate t) ≤ 2 * Real.log (4 * k) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hθ t (uIcc_of_le hab ▸ ht)) (hrate.intervalIntegrable_of_Icc hab)]
    have hangle (t : ℝ) (ht : t ∈ Icc a b) : |θ t| ≤ Real.log (4 * k) :=
      coreBootstrap_angle_bound hk (coreRegion_radius_bounds hk (hcore t ht)).2 (hcore t ht).2.1
    linarith only [(abs_le.mp (hangle a ha)).1, (abs_le.mp (hangle b hb)).2]
  have hbound (t : ℝ) (ht : t ∈ Icc a b) := coreRegion_log_rate_variation_bound hk (hcore t ht) (hQ t ht)
  constructor
  · have H := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hab
      (f := fun t => rate t * (fderiv ℝ (coreLogRates (θ t)) (toCoreAngleState (β t))
        (coreProjectedFlowVariation y t₀ t w)) 0)
      (g := fun t => (3 * Q) * rate t) (Filter.Eventually.of_forall (fun t ht => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hpos t (Ioc_subset_Icc_self ht))]
        exact (mul_le_mul_of_nonneg_left (hbound t (Ioc_subset_Icc_self ht)).1
          (hpos t (Ioc_subset_Icc_self ht))).trans_eq (by ring)))
      ((continuousOn_const.mul hrate).intervalIntegrable_of_Icc hab)
    rw [intervalIntegral.integral_const_mul] at H
    exact H.trans ((mul_le_mul_of_nonneg_left hspan (by positivity)).trans_eq (by ring))
  · have h1 : IntervalIntegrable (fun t => (9 / k ^ 2 * Q) * rate t) volume a b :=
      (continuousOn_const.mul hrate).intervalIntegrable_of_Icc hab
    have h2 : IntervalIntegrable (fun t => (8 / k) * (|x t| * rate t)) volume a b :=
      (continuousOn_const.mul (hx.abs.mul hrate)).intervalIntegrable_of_Icc hab
    have H := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hab
      (f := fun t => rate t * (fderiv ℝ (coreLogRates (θ t)) (toCoreAngleState (β t))
        (coreProjectedFlowVariation y t₀ t w)) 1)
      (g := fun t => (9 / k ^ 2 * Q) * rate t + (8 / k) * (|x t| * rate t))
      (Filter.Eventually.of_forall (fun t ht => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hpos t (Ioc_subset_Icc_self ht))]
        exact (mul_le_mul_of_nonneg_left (hbound t (Ioc_subset_Icc_self ht)).2
          (hpos t (Ioc_subset_Icc_self ht))).trans_eq (by dsimp [x]; ring))) (h1.add h2)
    rw [intervalIntegral.integral_add h1 h2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul] at H
    have hstrong := (coreProjectedFlowVariation_strong_integrals hk hab hD hdom hA hcore hentry w hQ).2
    have hX : |x a| ≤ Q := (norm_le_pi_norm
      (scaleCoreVariation k (coreProjectedFlowVariation y t₀ a w)) 1).trans (hQ a ha)
    have hU : β a 1 ≤ 1 / 60000 := coreBootstrap_wall_bound hk (hcore a ha).2.2.1.2
    have hsmall : 32 * |x a| + 384 * β a 1 * Q ≤ 33 * Q := by
      nlinarith only [hX, mul_le_mul_of_nonneg_right hU hQ0, hQ0]
    have HI : (8 / k) * (∫ t in a..b, |x t| * rate t) ≤ 33 * Q / k ^ 2 := by
      calc
        _ ≤ (8 / k) * ((4 * |x a| + 48 * β a 1 * Q) / k) :=
          mul_le_mul_of_nonneg_left hstrong (by positivity)
        _ = (32 * |x a| + 384 * β a 1 * Q) / k ^ 2 := by ring
        _ ≤ _ := div_le_div_of_nonneg_right hsmall (sq_nonneg k)
    apply H.trans
    calc
      _ ≤ (9 / k ^ 2 * Q) * (2 * Real.log (4 * k)) + 33 * Q / k ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_left hspan (by positivity)) HI
      _ ≤ 51 * Real.log (4 * k) * Q / k ^ 2 := by
        have hlog := mul_le_mul_of_nonneg_right (core_log_lower_bound hk) hQ0
        apply (div_le_div_of_nonneg_right (show
          18 * Real.log (4 * k) * Q + 33 * Q ≤ 51 * Real.log (4 * k) * Q by
            nlinarith only [hlog]) (sq_nonneg k)).trans_eq' ?_
        ring

end BianchiIX
