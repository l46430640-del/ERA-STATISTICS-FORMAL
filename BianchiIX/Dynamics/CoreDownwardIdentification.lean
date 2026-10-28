import BianchiIX.Dynamics.CoreReturnCanonical
import BianchiIX.Dynamics.PartialCoreDownwardReturn

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- Radius coordinates reconstruct every point of the upward active-wall section. -/
theorem coreRadiusEntry_of_upward_section {y : ProjectiveState}
    (hm : 1 ≤ y 0) (hv : y 2 = 1) :
    coreRadiusEntry (toCoreAngleState y) = y := by
  have he : coreEnergy (y 0) (y 2) = (y 0 - 1) ^ 2 + 1 := by
    simp only [coreEnergy, hv, one_pow]
  have hs : coreRadius (y 0) (y 2) ^ 2 - 1 = (y 0 - 1) ^ 2 := by
    rw [coreRadius, Real.sq_sqrt (by rw [he]; positivity), he]
    ring
  ext i
  fin_cases i
  · change 1 + Real.sqrt (coreRadius (y 0) (y 2) ^ 2 - 1) = y 0
    rw [hs, Real.sqrt_sq (sub_nonneg.mpr hm)]
    ring
  · rfl
  · exact hv.symm
  · change y 2 * y 3 = y 3
    rw [hv, one_mul]

/-- The full-core return and the first downward event agree on an ordinary open germ,
including at zero transverse walls. -/
theorem coreRadiusReturn_downward_eventuallyEq {Y : CoreAngleState} (hk : 6 ≤ Y 0)
    (hu : 0 ≤ Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0)
    (hw : 0 ≤ Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0) :
    (coreRadiusReturnTime =ᶠ[𝓝 Y] fun Z => partialCoreDownwardReturnTime (coreRadiusEntry Z)) ∧
      (coreReturnState coreRadiusReturnTime =ᶠ[𝓝 Y]
        fun Z => partialCoreDownwardReturnState (coreRadiusEntry Z)) := by
  have hk1 : 1 < Y 0 := by linarith only [hk]
  have he := contDiffAt_coreRadiusEntry 2 hk1
  have hr := coreRadiusReturn_large_regular hk hu hw
  have hd := partialCoreDownwardReturn_regular hk (coreRadiusEntry_region hk hu hw)
    (coreRadius_coreRadiusEntry hk1) (Or.inr ⟨rfl, by
      change (1 : ℝ) ≤ 1 + Real.sqrt (Y 0 ^ 2 - 1)
      linarith only [Real.sqrt_nonneg (Y 0 ^ 2 - 1)]⟩)
  obtain ⟨T, _, hfirst, _, _, _, σ, _, _, _, huniq, _⟩ :=
    exists_large_core_exit_derivative hk hu hw
  have ht : coreRadiusReturnTime Y = T := hr.2.2.2.self_of_nhds.unique hfirst
  have hdt : partialCoreDownwardReturnTime (coreRadiusEntry Y) = T := hd.1.unique hfirst
  have hpair : ContinuousAt (fun Z => (coreRadiusEntry Z, coreRadiusReturnTime Z)) Y :=
    he.continuousAt.prodMk hr.2.1.continuousAt
  have hpaird : ContinuousAt (fun Z =>
      (coreRadiusEntry Z, partialCoreDownwardReturnTime (coreRadiusEntry Z))) Y :=
    he.continuousAt.prodMk (hd.2.1.continuousAt.comp he.continuousAt)
  have hn : ∀ᶠ Z in 𝓝 Y,
      projectiveOriginalFlow (coreRadiusEntry Z) 0 (coreRadiusReturnTime Z) 2 = 1 ↔
        σ (coreRadiusEntry Z) = coreRadiusReturnTime Z := by
    have hlocal : ∀ᶠ z : ProjectiveState × ℝ in
        𝓝 (coreRadiusEntry Y, coreRadiusReturnTime Y),
        projectiveOriginalFlow z.1 0 z.2 2 = 1 ↔ σ z.1 = z.2 := by
      simpa only [ht, coreRadiusEntry] using huniq
    exact hpair.eventually hlocal
  have hnd : ∀ᶠ Z in 𝓝 Y,
      projectiveOriginalFlow (coreRadiusEntry Z) 0
        (partialCoreDownwardReturnTime (coreRadiusEntry Z)) 2 = 1 ↔
        σ (coreRadiusEntry Z) = partialCoreDownwardReturnTime (coreRadiusEntry Z) := by
    have hlocal : ∀ᶠ z : ProjectiveState × ℝ in
        𝓝 (coreRadiusEntry Y, partialCoreDownwardReturnTime (coreRadiusEntry Y)),
        projectiveOriginalFlow z.1 0 z.2 2 = 1 ↔ σ z.1 = z.2 := by
      rw [hdt]
      simpa only [coreRadiusEntry] using huniq
    exact hpaird.eventually hlocal
  have hdown := he.continuousAt.tendsto.eventually hd.2.2.2.1
  have htime : coreRadiusReturnTime =ᶠ[𝓝 Y]
      fun Z => partialCoreDownwardReturnTime (coreRadiusEntry Z) := by
    filter_upwards [hn, hnd, hr.2.2.2, hdown] with Z hZ hZd hfull hdown
    exact (hZ.mp hfull.1.2).symm.trans (hZd.mp hdown.1.1.2.2.1)
  refine ⟨htime, ?_⟩
  filter_upwards [htime] with Z hZ
  simp only [coreReturnState, partialCoreDownwardReturnState, hZ]

/-- The canonical large-core time and state inherit the joint C2 downward-event regularity. -/
theorem coreRadiusReturn_large_contDiff_two {Y : CoreAngleState} (hk : 6 ≤ Y 0)
    (hu : 0 ≤ Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0)
    (hw : 0 ≤ Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0) :
    ContDiffAt ℝ 2 coreRadiusReturnTime Y ∧
      ContDiffAt ℝ 2 (coreReturnState coreRadiusReturnTime) Y := by
  have hk1 : 1 < Y 0 := by linarith only [hk]
  have he := contDiffAt_coreRadiusEntry 2 hk1
  have hd := partialCoreDownwardReturn_regular hk (coreRadiusEntry_region hk hu hw)
    (coreRadius_coreRadiusEntry hk1) (Or.inr ⟨rfl, by
      change (1 : ℝ) ≤ 1 + Real.sqrt (Y 0 ^ 2 - 1)
      linarith only [Real.sqrt_nonneg (Y 0 ^ 2 - 1)]⟩)
  have hg := coreRadiusReturn_downward_eventuallyEq hk hu hw
  exact ⟨(hd.2.1.comp Y he).congr_of_eventuallyEq hg.1,
    (hd.2.2.1.comp Y he).congr_of_eventuallyEq hg.2⟩

end BianchiIX
