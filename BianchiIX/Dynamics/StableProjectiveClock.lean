import BianchiIX.Analysis.CompactIntegralSecondRegularity
import BianchiIX.Dynamics.StableResidualClockBounds
import BianchiIX.Dynamics.StableProjectionFirstRegularity

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology

/-- The rate of the scaled projective time with respect to the original time. -/
def stableProjectiveRate (c : ℝ) (p : StableState × ℝ) : ℝ :=
  stableResidualClock (c + 1) (stableOriginalFlow p.1 p.2)

def stableProjectiveClock (c : ℝ) (p : StableState × ℝ) : ℝ :=
  ∫ t in 0..p.2, stableProjectiveRate c (p.1, t)

theorem stableProjectiveClock_zero (c : ℝ) (y : StableState) :
    stableProjectiveClock c (y, 0) = 0 := by simp [stableProjectiveClock]

theorem contDiffAt_stableProjectiveRate_two {c t : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (ht : 0 ≤ t) :
    ContDiffAt ℝ 2 (stableProjectiveRate c) (y, t) :=
  (contDiff_stableResidualClock 2 (c + 1)).contDiffAt.comp (y, t)
    (contDiffAt_stableOriginalFlow_two hc hy.1.le hy.2.1.le hy.2.2.le ht)

theorem stableProjectiveRate_pos {c : ℝ} (hc : 2 ≤ c) (p : StableState × ℝ) :
    0 < stableProjectiveRate c p := by
  unfold stableProjectiveRate stableResidualClock
  exact div_pos (by linarith) (stableBoundaryDenom_pos _)

theorem hasDerivAt_stableProjectiveClock {c t : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (ht : 0 ≤ t) :
    HasDerivAt (fun s => stableProjectiveClock c (y, s)) (stableProjectiveRate c (y, t)) t := by
  have hcont : ContinuousOn (fun s => stableProjectiveRate c (y, s)) (Icc 0 t) :=
    fun s hs => ((contDiffAt_stableProjectiveRate_two hc hy hs.1).continuousAt.comp
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  have hreg : ContDiffAt ℝ 2 (fun s => stableProjectiveRate c (y, s)) t :=
    (contDiffAt_stableProjectiveRate_two hc hy ht).comp t
      (g := stableProjectiveRate c) (f := fun s => (y, s)) (contDiffAt_const.prodMk contDiffAt_id)
  obtain ⟨S, hS, hCS⟩ := hreg.contDiffOn (m := 2) le_rfl (by simp)
  apply intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable_of_Icc ht)
  · exact ContinuousOn.stronglyMeasurableAtFilter isOpen_interior
      (hCS.continuousOn.mono interior_subset) t (mem_interior_iff_mem_nhds.mpr hS)
  · exact (contDiffAt_stableProjectiveRate_two hc hy ht).continuousAt.comp
      (continuousAt_const.prodMk continuousAt_id)

theorem contDiffAt_stableProjectiveClock_two {c t : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (ht : 0 ≤ t) :
    ContDiffAt ℝ 2 (stableProjectiveClock c) (y, t) := by
  apply contDiffAt_moving_intervalIntegral_two (τ := Prod.snd)
    (F := fun p : (StableState × ℝ) × ℝ => stableProjectiveRate c (p.1.1, p.2)) contDiffAt_snd ht
  intro r hr
  exact (contDiffAt_stableProjectiveRate_two hc hy hr.1).comp ((y, t), r)
    (g := stableProjectiveRate c) (f := fun p : (StableState × ℝ) × ℝ => (p.1.1, p.2))
    (by fun_prop : ContDiffAt ℝ 2 (fun p : (StableState × ℝ) × ℝ => (p.1.1, p.2)) ((y, t), r))

theorem stableProjectiveRate_eq_normalized {c t : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (ht : 0 ≤ t) :
    stableProjectiveRate c (y, t) = (c + 1) *
      normalizedProjectiveRate (fromProjectiveState (stableInclusion y)) 0 t := by
  let x := fromProjectiveState (stableInclusion y)
  have hD : 0 < projectiveStateDenom (stableInclusion y) := by
    rw [stableBoundaryDenom_eq]
    exact stableBoundaryDenom_pos y
  have hx := fromProjectiveState_constraint hD.ne'
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint hx 0 ht
  have hA := stableProjectiveFlow_rate_pos hc hy.1.le hy.2.1.le hy.2.2.le ht
  have hscale := projective_inverse_scale hA.ne' ((normalizedMaxCurve_constraint hdom).trans hx)
  have heq : stableBoundaryDenom (stableOriginalFlow y t) =
      projectiveStateDenom (toProjectiveState (normalizedMaxCurve x 0 t)) := by
    rw [← stableBoundaryDenom_eq, stableOriginalFlow, stableInclusion_restriction
      (stableProjectiveFlow_active_zero y ht)]
    rfl
  change 6 / projectiveStateDenom (toProjectiveState (normalizedMaxCurve x 0 t)) =
    normalizedProjectiveRate x 0 t at hscale
  dsimp only [stableProjectiveRate, stableResidualClock]
  rw [heq, ← hscale]
  ring

/-- This integral is precisely the projective time used in the stable-boundary estimates. -/
theorem stableProjectiveClock_eq_normalized {c t : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (ht : 0 ≤ t) :
    stableProjectiveClock c (y, t) =
      normalizedStableClock (fromProjectiveState (stableInclusion y)) 0 0 c t := by
  unfold stableProjectiveClock normalizedStableClock integralClock
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro r hr
  exact stableProjectiveRate_eq_normalized hc hy (uIcc_of_le ht ▸ hr).1

theorem stableProjectiveRate_bounds {c t : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (ht : 0 ≤ t) :
    3 / (c + 1) ≤ stableProjectiveRate c (y, t) ∧
      stableProjectiveRate c (y, t) ≤ 18 / (c + 1) := by
  have hK : 0 < c + 1 := by linarith
  have H := stableBoundaryOrbit_global hc hy.1.le hy.2.1.le hy.2.2.le t ht
  constructor
  · rw [stableProjectiveRate_eq_normalized hc hy ht, stableInclusion_entry]
    have h := mul_le_mul_of_nonneg_left H.1 hK.le
    convert! h using 1
    field_simp
  · apply (le_abs_self _).trans
    apply stableResidualClock_bound hc
    simpa only [stableOriginalFlow_eq, stableRestriction_apply, Matrix.cons_val_zero] using H.2.1.1

theorem stableProjectiveClock_bounds {c t : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (ht : 0 ≤ t) :
    3 / (c + 1) * t ≤ stableProjectiveClock c (y, t) ∧
      stableProjectiveClock c (y, t) ≤ 18 / (c + 1) * t := by
  have hcont : ContinuousOn (fun s => stableProjectiveRate c (y, s)) (Icc 0 t) :=
    fun s hs => ((contDiffAt_stableProjectiveRate_two hc hy hs.1).continuousAt.comp
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  have hi : IntervalIntegrable (fun s => stableProjectiveRate c (y, s)) volume 0 t :=
    hcont.intervalIntegrable_of_Icc ht
  have hlow := intervalIntegral.integral_mono_on ht
    (intervalIntegrable_const (c := 3 / (c + 1))) hi
    (fun r hr => (stableProjectiveRate_bounds hc hy hr.1).1)
  have hupp := intervalIntegral.integral_mono_on ht hi
    (intervalIntegrable_const (c := 18 / (c + 1)))
    (fun r hr => (stableProjectiveRate_bounds hc hy hr.1).2)
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm,
    stableProjectiveClock] using And.intro hlow hupp

theorem stableProjectiveClock_strictMonoOn {c : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) :
    StrictMonoOn (fun t => stableProjectiveClock c (y, t)) (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    (fun t ht => (hasDerivAt_stableProjectiveClock hc hy ht).continuousAt.continuousWithinAt)
  intro t ht
  rw [(hasDerivAt_stableProjectiveClock hc hy (interior_subset ht)).deriv]
  exact stableProjectiveRate_pos hc _

end BianchiIX
