import BianchiIX.Dynamics.TaubDistance
import BianchiIX.Dynamics.ReferenceShiftedVariation
import BianchiIX.Dynamics.ReferenceTail

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem normalized_finiteVisit_neighborhood {x q : NormalizedState} {T ε : ℝ}
    (hdom : T ∈ normalizedMaxDomain x 0)
    (hclose : normalizedEuclideanDistance (normalizedMaxCurve x 0 T) q < ε) :
    ∀ᶠ y in 𝓝 x, T ∈ normalizedMaxDomain y 0 ∧
      normalizedEuclideanDistance (normalizedMaxCurve y 0 T) q < ε := by
  have hpair : ContinuousAt (fun y : NormalizedState => (y, T)) x := by fun_prop
  have hflow : ContinuousAt (fun y : NormalizedState => normalizedMaxCurve y 0 T) x :=
    ContinuousAt.comp (f := fun y : NormalizedState => (y, T))
      (normalizedMaxCurve_regular hdom).2.continuousAt hpair
  have hdist := continuous_normalizedEuclideanDistance.continuousAt.comp
    (hflow.prodMk (continuousAt_const (y := q)))
  exact (hpair.eventually ((isOpen_normalizedFlowDomain 0).mem_nhds hdom)).and
    (hdist.eventually (isOpen_Iio.mem_nhds hclose))

/-- A finite point on the radius-two boundary orbit lies in any prescribed Taub neighborhood. -/
theorem exists_reference_two_taub_visit {ε : ℝ} (hε : 0 < ε) :
    ∃ T > 0, T ∈ normalizedMaxDomain (referenceEntryState 2) 0 ∧
      normalizedEuclideanDistance (normalizedMaxCurve (referenceEntryState 2) 0 T) (taubPoint 1) < ε := by
  let y : ℝ → ProjectiveState := fun v => ![1 - Real.sqrt (4 - v ^ 2), 0, v, 0]
  have hs4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have hy : Continuous y := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp [y] <;> fun_prop
  have hD : projectiveStateDenom (y 0) ≠ 0 := by
    dsimp [y, projectiveStateDenom, projectiveDenom, curvature]
    norm_num [hs4]
  have hc := (contDiffAt_fromProjectiveState 0 hD).continuousAt.comp hy.continuousAt
  have hd := continuous_normalizedEuclideanDistance.continuousAt.comp
    (hc.prodMk (continuousAt_const (y := taubPoint 1)))
  have hz : normalizedEuclideanDistance (fromProjectiveState (y 0)) (taubPoint 1) = 0 := by
    have H := singleWall_taubDistance_sq (-1) 0
    have hy₀ : y 0 = ![-1, 0, 0, 0] := by norm_num [y, hs4]
    rw [hy₀]
    norm_num at H
    exact H
  have he : ∀ᶠ v in 𝓝 (0 : ℝ), normalizedEuclideanDistance (fromProjectiveState (y v)) (taubPoint 1) < ε :=
    hd.eventually (isOpen_Iio.mem_nhds (by simpa only [Function.comp_apply, hz, mem_Iio] using hε))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp he
  let v := min (r / 2) (1 / 2)
  have hv : 0 < v := lt_min (half_pos hr) (by norm_num)
  have hv1 : v < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hvr : v < r := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hr)
  have hnear := hball (show dist v 0 < r by simpa [Real.dist_eq, abs_of_pos hv] using hvr)
  let t := referenceHeightTime 2 v
  have ht : -referenceHalfTime 2 < t := by
    have H := referenceHalfTime_lt_heightTime (by norm_num : (1 : ℝ) < 2) ⟨hv, hv1⟩
    have Hp := referenceHalfTime_pos (by norm_num : (1 : ℝ) < 2)
    dsimp [t]
    linarith only [H, Hp]
  have hT : 0 < referenceClock 2 t := by
    have H := referenceShiftClock_strictMono 2 (-referenceHalfTime 2) ht
    simpa only [referenceShiftClock, referenceClock, sub_self] using H
  refine ⟨referenceClock 2 t, hT, (referenceClock_normalized_orbit 2 t).1, ?_⟩
  rw [(referenceClock_normalized_orbit 2 t).2]
  have hp := referencePulse_height_exit (by norm_num : (0 : ℝ) < 2) ⟨hv, by linarith only [hv1]⟩
  change normalizedEuclideanDistance (fromProjectiveState (referencePulse 2 (referenceHeightTime 2 v))) _ < ε
  rw [hp]
  simpa only [y, show (2 : ℝ) ^ 2 = 4 by norm_num] using hnear

/-- The same positive original time works on a whole neighborhood of the radius-two core. -/
theorem exists_core_two_taub_visit {ε : ℝ} (hε : 0 < ε) :
    ∃ T > 0, ∃ ρ > 0, ρ ≤ 1 / 16 ∧ ∀ Y : CoreAngleState,
      |Y 0 - 2| ≤ ρ → |Y 1| ≤ ρ → |Y 2| ≤ ρ →
      T ∈ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry Y)) 0 ∧
        normalizedEuclideanDistance
          (normalizedMaxCurve (fromProjectiveState (coreRadiusEntry Y)) 0 T) (taubPoint 1) < ε := by
  obtain ⟨T, hT, hdom, hclose⟩ := exists_reference_two_taub_visit hε
  let Y₀ : CoreAngleState := ![2, 0, 0]
  have hx : fromProjectiveState (coreRadiusEntry Y₀) = referenceEntryState 2 := by
    unfold referenceEntryState
    rw [referencePulse_entry (by norm_num : (1 : ℝ) < 2)]
    rfl
  have hD : projectiveStateDenom (coreRadiusEntry Y₀) ≠ 0 := by
    have H := referencePulse_denom_pos 2 (-referenceHalfTime 2)
    rw [referencePulse_entry (by norm_num : (1 : ℝ) < 2)] at H
    exact H.ne'
  have hc := ((contDiffAt_fromProjectiveState 1 hD).comp Y₀
    (contDiffAt_coreRadiusEntry 1 (by norm_num [Y₀]))).continuousAt
  have he := hc.eventually (hx.symm ▸ normalized_finiteVisit_neighborhood hdom hclose)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp he
  let ρ := min (r / 2) (1 / 16)
  have hρ : 0 < ρ := lt_min (half_pos hr) (by norm_num)
  refine ⟨T, hT, ρ, hρ, min_le_right _ _, ?_⟩
  intro Y hk hu hw
  have hdist : dist Y Y₀ ≤ ρ := by
    apply (dist_pi_le_iff hρ.le).mpr
    intro i
    fin_cases i
    · simpa [Y₀, Real.dist_eq] using hk
    · simpa [Y₀, Real.dist_eq] using hu
    · simpa [Y₀, Real.dist_eq] using hw
  exact hball (lt_of_le_of_lt hdist (lt_of_le_of_lt (min_le_left _ _) (half_lt_self hr)))

theorem exists_core_radius_separation_of_away {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ > 0, ρ ≤ 1 / 16 ∧ ∀ Y : CoreAngleState,
      |Y 1| ≤ ρ → |Y 2| ≤ ρ →
      (∀ T > 0, T ∈ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry Y)) 0 →
        ε ≤ normalizedEuclideanDistance
          (normalizedMaxCurve (fromProjectiveState (coreRadiusEntry Y)) 0 T) (taubPoint 1)) →
      ρ < |Y 0 - 2| := by
  obtain ⟨T, hT, ρ, hρ, hρle, H⟩ := exists_core_two_taub_visit hε
  refine ⟨ρ, hρ, hρle, fun Y hu hw haway => ?_⟩
  by_contra! hk
  obtain ⟨hdom, hnear⟩ := H Y hk hu hw
  exact (not_lt_of_ge (haway T hT hdom)) hnear

end BianchiIX
