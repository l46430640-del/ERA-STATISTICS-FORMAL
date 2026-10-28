import BianchiIX.Dynamics.StableProjectiveCutoff

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology

theorem measurable_normalizedMaxCurve_time (x : NormalizedState) (t₀ : ℝ) :
    Measurable (normalizedMaxCurve x t₀) := by
  classical
  have hc : ContinuousOn (normalizedMaxCurve x t₀) (normalizedMaxDomain x t₀) :=
    fun t ht => (hasDerivAt_normalizedMaxCurve ht).continuousAt.continuousWithinAt
  have hm := hc.measurable_piecewise (g := fun _ => x) continuousOn_const
    (isOpen_normalizedMaxDomain x t₀).measurableSet
  convert! hm using 1
  funext t
  by_cases ht : t ∈ normalizedMaxDomain x t₀
  · simp only [piecewise_eq_of_mem _ _ _ ht]
  · simp only [piecewise_eq_of_notMem _ _ _ ht, normalizedMaxCurve, dif_neg ht]

theorem measurable_stableOriginalFlow_time (y : StableState) :
    Measurable (stableOriginalFlow y) := by
  have hm := measurable_normalizedMaxCurve_time (fromProjectiveState (stableInclusion y)) 0
  have hp : Measurable toProjectiveState := by
    apply measurable_pi_lambda
    intro i
    fin_cases i <;> dsimp [toProjectiveState, projectiveCoord] <;> fun_prop
  exact stableRestriction.continuous.measurable.comp (hp.comp hm)

theorem measurable_stableProjectiveRate_time (c : ℝ) (y : StableState) :
    Measurable (fun t => stableProjectiveRate c (y, t)) :=
  (contDiff_stableResidualClock 0 (c + 1)).continuous.measurable.comp
    (measurable_stableOriginalFlow_time y)

theorem intervalIntegrable_stableProjectiveRate {c : ℝ} (hc : 2 ≤ c)
    (y : StableState) (a b : ℝ) :
    IntervalIntegrable (fun t => stableProjectiveRate c (y, t)) volume a b := by
  apply (intervalIntegrable_const (c := 2 * (c + 1))).mono_fun'
    (measurable_stableProjectiveRate_time c y).aestronglyMeasurable
  apply Eventually.of_forall
  intro t
  dsimp only
  rw [Real.norm_eq_abs, abs_of_pos (stableProjectiveRate_pos hc _)]
  unfold stableProjectiveRate stableResidualClock
  apply (div_le_iff₀ (stableBoundaryDenom_pos _)).mpr
  have hD : 3 ≤ stableBoundaryDenom (stableOriginalFlow y t) := by
    unfold stableBoundaryDenom
    nlinarith [sq_nonneg (stableOriginalFlow y t 0),
      sq_nonneg (stableOriginalFlow y t 1 - stableOriginalFlow y t 2)]
  nlinarith

/-- The positive measurable rate also defines a strictly increasing clock before time zero. -/
theorem stableProjectiveClock_strictMono {c : ℝ} (hc : 2 ≤ c) (y : StableState) :
    StrictMono (fun t => stableProjectiveClock c (y, t)) := by
  intro a b hab
  have hp := intervalIntegral.intervalIntegral_pos_of_pos
    (intervalIntegrable_stableProjectiveRate hc y a b) (fun t => stableProjectiveRate_pos hc (y, t)) hab
  have he := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_stableProjectiveRate hc y 0 a)
    (intervalIntegrable_stableProjectiveRate hc y a b)
  change stableProjectiveClock c (y, a) + _ = stableProjectiveClock c (y, b) at he
  linarith

/-- Using the whole clock gives a regular inverse across the initial time. -/
def stableProjectiveTime (c : ℝ) : StableState × ℝ → ℝ :=
  intervalScalarInverse (stableProjectiveClock c) univ

theorem stableProjectiveTime_eq_cutoff {c σ : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 ≤ σ) :
    stableProjectiveTime c (y, σ) = stableProjectiveCutoff c (y, σ) :=
  intervalScalarInverse_eq ((stableProjectiveClock_strictMono hc y).strictMonoOn univ)
    (mem_univ _) (stableProjectiveCutoff_spec hc hy hσ).2

theorem stableProjectiveTime_spec {c σ : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 ≤ σ) :
    0 ≤ stableProjectiveTime c (y, σ) ∧
      stableProjectiveClock c (y, stableProjectiveTime c (y, σ)) = σ := by
  rw [stableProjectiveTime_eq_cutoff hc hy hσ]
  exact stableProjectiveCutoff_spec hc hy hσ

theorem stableProjectiveTime_zero {c : ℝ} (hc : 2 ≤ c) (y : StableState) :
    stableProjectiveTime c (y, 0) = 0 :=
  intervalScalarInverse_eq ((stableProjectiveClock_strictMono hc y).strictMonoOn univ)
    (mem_univ _) (stableProjectiveClock_zero c y)

theorem stableProjectiveTime_regular {c σ : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 ≤ σ) :
    ContDiffAt ℝ 2 (stableProjectiveTime c) (y, σ) ∧
      (∀ᶠ p in 𝓝 (y, σ), stableProjectiveClock c (p.1, stableProjectiveTime c p) = p.2) := by
  obtain ⟨ht, he⟩ := stableProjectiveTime_spec hc hy hσ
  have H := intervalScalarInverse_regular isOpen_univ (mem_univ _)
    (contDiffAt_stableProjectiveClock_two hc hy ht)
    (hasDerivAt_stableProjectiveClock hc hy ht) (stableProjectiveRate_pos hc _).ne'
    (Eventually.of_forall fun z => (stableProjectiveClock_strictMono hc z).strictMonoOn univ)
  rw [he] at H
  exact ⟨H.1, H.2.mono fun _ h => h.2⟩

theorem hasDerivAt_stableProjectiveTime_clock {c σ : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 ≤ σ) :
    HasDerivAt (fun s => stableProjectiveTime c (y, s))
      (1 / stableProjectiveRate c (y, stableProjectiveTime c (y, σ))) σ := by
  obtain ⟨ht, he⟩ := stableProjectiveTime_spec hc hy hσ
  have H := hasDerivAt_intervalScalarInverse_clock isOpen_univ (mem_univ _)
    (contDiffAt_stableProjectiveClock_two hc hy ht)
    (hasDerivAt_stableProjectiveClock hc hy ht) (stableProjectiveRate_pos hc _).ne'
    (Eventually.of_forall fun z => (stableProjectiveClock_strictMono hc z).strictMonoOn univ)
  rwa [he] at H

end BianchiIX
