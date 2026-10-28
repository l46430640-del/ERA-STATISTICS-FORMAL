import BianchiIX.Dynamics.CoreReturnAngleBounds
import BianchiIX.Dynamics.CoreLogIntegralBounds
import BianchiIX.Dynamics.CoreMultiplierRegularity

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology

/-- Formula (B.33) for the actual first-return multipliers, with both moving endpoints. -/
theorem exists_large_core_log_derivative_bounds {Y : CoreAngleState} (hk : 6 ≤ Y 0)
    (hu : 0 ≤ Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0)
    (hw : 0 ≤ Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0) :
    ∃ τ : CoreAngleState → ℝ, 0 < τ Y ∧ ContDiffAt ℝ 1 τ Y ∧
      (∀ᶠ Z in 𝓝 Y,
        IsLeast {t | 0 < t ∧ projectiveOriginalFlow (coreRadiusEntry Z) 0 t 2 = 1} (τ Z) ∧
        projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z) 1 = Z 1 * coreReturnMultiplier τ Z 0 ∧
        projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z) 3 = Z 2 * coreReturnMultiplier τ Z 1) ∧
      (∀ i : Fin 2, 0 < coreReturnMultiplier τ Y i ∧
        ContDiffAt ℝ 1 (fun Z => Real.log (coreReturnMultiplier τ Z i)) Y ∧
        ContDiffAt ℝ 1 (fun Z => coreReturnMultiplier τ Z i) Y) ∧
      ∀ v : CoreAngleState,
        let Q₀ := |v 0| + Y 0 * |v 1| + |v 2|
        |fderiv ℝ (fun Z => Real.log (coreReturnMultiplier τ Z 0)) Y v| ≤
          (20 * coreVariationBound + 4) * Real.log (4 * Y 0) * Q₀ ∧
        |fderiv ℝ (fun Z => Real.log (coreReturnMultiplier τ Z 1)) Y v| ≤
          (118 * coreVariationBound + 8) * Real.log (4 * Y 0) * Q₀ / Y 0 ^ 2 := by
  have hk0 : 0 < Y 0 := by linarith only [hk]
  have hD := (coreRegion_clock_regular hk (coreRadiusEntry_region hk hu hw)).1
  have hc := fromProjectiveState_constraint (ne_of_gt hD)
  obtain ⟨τ, hpos, hcτ, hnear, hmul⟩ := exists_large_core_multiplier_differential hk hu hw
  have hfirst := hnear.self_of_nhds.1
  obtain ⟨T, _, hfirstT, hcoreT, hM, _⟩ := exists_large_core_traversal hk hu hw
  have hT : T = τ Y := hfirstT.unique hfirst
  subst T
  obtain ⟨S, _, hfirstS, _, hnorm⟩ := exists_large_core_entry_variation hk hu hw
  have hS : S = τ Y := hfirstS.unique hfirst
  subst S
  have hdom : Icc 0 (τ Y) ⊆ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry Y)) 0 :=
    fun t ht => normalizedMaxDomain_contains_Ici_of_constraint hc 0 ht.1
  have hA : ∀ t ∈ Icc 0 (τ Y), 0 < 1 + normalizedMaxCurve (fromProjectiveState (coreRadiusEntry Y)) 0 t 0 :=
    fun t ht => (hcoreT t ht).1
  have hcore : ∀ t ∈ Icc 0 (τ Y), coreRegion (Y 0) (projectiveOriginalFlow (coreRadiusEntry Y) 0 t) :=
    fun t ht => (hcoreT t ht).2
  have hentry : Real.cosh (projectiveCoreAngle (projectiveOriginalFlow (coreRadiusEntry Y) 0 0)) = Y 0 := by
    rw [projectiveOriginalFlow_initial hD, projectiveCoreAngle,
      cosh_coreAngle (show 0 < coreRadiusEntry Y 2 by change (0 : ℝ) < 1; norm_num),
      coreRadius_coreRadiusEntry (by linarith only [hk] : 1 < Y 0)]
    exact div_one _
  refine ⟨τ, hpos, hcτ, hnear, fun i => ⟨(hmul i).1,
    contDiffAt_log_coreReturnMultiplier hk hD hcτ hpos.le hdom hA hcore i,
    contDiffAt_coreReturnMultiplier hk hD hcτ hpos.le hdom hA hcore i⟩, ?_⟩
  intro v Q₀
  let Q := (2 * coreVariationBound) * Q₀
  let β := projectiveOriginalFlow (coreRadiusEntry Y) 0
  let w := fderiv ℝ coreRadiusEntry Y v
  let ξ := fun t => coreProjectedFlowVariation (coreRadiusEntry Y) 0 t w
  let L := fun t => coreLogRates (projectiveCoreAngle (β t)) (toCoreAngleState (β t))
  let I := fun i : Fin 2 => ∫ t in 0..τ Y, coreOriginalClockRate (β t) *
    (fderiv ℝ (coreLogRates (projectiveCoreAngle (β t))) (toCoreAngleState (β t)) (ξ t)) i
  let a := fderiv ℝ (fun Z => projectiveCoreAngle (coreRadiusEntry Z)) Y v
  let b := fderiv ℝ (fun Z => projectiveCoreAngle (projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z))) Y v
  have hQ₀ : 0 ≤ Q₀ := by dsimp [Q₀]; positivity
  have hK : 0 ≤ coreVariationBound := (Real.exp_pos _).le
  have hQ : 0 ≤ Q := mul_nonneg (mul_nonneg (by norm_num) hK) hQ₀
  have hnorm' (t : ℝ) (ht : t ∈ Icc 0 (τ Y)) : ‖scaleCoreVariation (Y 0) (ξ t)‖ ≤ Q := hnorm t ht v
  have hend : τ Y ∈ Icc 0 (τ Y) := ⟨hpos.le, le_rfl⟩
  have hstart : (0 : ℝ) ∈ Icc 0 (τ Y) := ⟨le_rfl, hpos.le⟩
  have hI : |I 0| ≤ 6 * Real.log (4 * Y 0) * Q ∧
      |I 1| ≤ 51 * Real.log (4 * Y 0) * Q / Y 0 ^ 2 :=
    coreFlow_log_integral_bounds hk hpos.le hD hdom hA hcore hentry w hnorm'
  have hv0 : |v 0| ≤ Q₀ := by
    dsimp [Q₀]
    linarith only [mul_nonneg hk0.le (abs_nonneg (v 1)), abs_nonneg (v 2)]
  have ha : |a| ≤ 2 * Q₀ / Y 0 := (coreRadiusEntry_angle_bound hk v).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hv0 (by norm_num)) hk0.le)
  have hb : |b| ≤ 2 * Q / Y 0 := by
    have H := coreReturn_exit_angle_bound hk hD hcτ.continuousAt (hdom hend) (hA _ hend)
      (hcore _ hend) (hnear.mono fun _ h => h.1.1.2) hM v
    have hr : |ξ (τ Y) 0| ≤ Q :=
      (norm_le_pi_norm (scaleCoreVariation (Y 0) (ξ (τ Y))) 0).trans (hnorm' _ hend)
    exact H.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hr (by norm_num)) hk0.le)
  have hLa := coreRegion_log_rate_bounds hk (hcore 0 hstart)
  have hLb := coreRegion_log_rate_bounds hk (hcore (τ Y) hend)
  have ha0 : |L 0 0 * a| ≤ 4 * Q₀ := by
    rw [abs_mul]
    exact (mul_le_mul hLa.1 ha (abs_nonneg _) (by positivity)).trans_eq (by field_simp; ring)
  have hb0 : |L (τ Y) 0 * b| ≤ 4 * Q := by
    rw [abs_mul]
    exact (mul_le_mul hLb.1 hb (abs_nonneg _) (by positivity)).trans_eq (by field_simp; ring)
  have ha1 : |L 0 1 * a| ≤ 8 * Q₀ / Y 0 ^ 2 := by
    rw [abs_mul]
    exact (mul_le_mul hLa.2.1 ha (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have hb1 : |L (τ Y) 1 * b| ≤ 8 * Q / Y 0 ^ 2 := by
    rw [abs_mul]
    exact (mul_le_mul hLb.2.1 hb (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have hderiv (i : Fin 2) :
      fderiv ℝ (fun Z => Real.log (coreReturnMultiplier τ Z i)) Y v = I i + L (τ Y) i * b - L 0 i * a :=
    coreReturn_log_derivative hk hD hcτ hpos.le hdom hA hcore v i
  have htri (i : Fin 2) :
      |fderiv ℝ (fun Z => Real.log (coreReturnMultiplier τ Z i)) Y v| ≤
        |I i| + |L (τ Y) i * b| + |L 0 i * a| := by
    rw [hderiv]
    exact (abs_sub _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
  have hlogQ : Q ≤ Real.log (4 * Y 0) * Q := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (core_log_lower_bound hk) hQ
  have hlogQ₀ : Q₀ ≤ Real.log (4 * Y 0) * Q₀ := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (core_log_lower_bound hk) hQ₀
  constructor
  · apply (htri 0).trans ((add_le_add (add_le_add hI.1 hb0) ha0).trans ?_)
    calc
      _ ≤ 10 * Real.log (4 * Y 0) * Q + 4 * Real.log (4 * Y 0) * Q₀ := by
        nlinarith only [hlogQ, hlogQ₀]
      _ = _ := by dsimp [Q]; ring
  · apply (htri 1).trans ((add_le_add (add_le_add hI.2 hb1) ha1).trans ?_)
    calc
      _ = (51 * Real.log (4 * Y 0) * Q + 8 * Q + 8 * Q₀) / Y 0 ^ 2 := by ring
      _ ≤ (59 * Real.log (4 * Y 0) * Q + 8 * Real.log (4 * Y 0) * Q₀) / Y 0 ^ 2 :=
        div_le_div_of_nonneg_right (by nlinarith only [hlogQ, hlogQ₀]) (sq_nonneg _)
      _ = _ := by dsimp [Q]; ring

end BianchiIX
