import BianchiIX.Dynamics.PartialCoreRadiusResponse

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def partialCoreReturnTime (y : ProjectiveState) : ℝ :=
  sInf {t : ℝ | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧
    projectiveOriginalFlow y 0 t 2 = 1}

def partialCoreReturnState (y : ProjectiveState) : CoreAngleState :=
  toCoreAngleState (projectiveOriginalFlow y 0 (partialCoreReturnTime y))

theorem partialCoreReturnTime_eq {y : ProjectiveState} {T : ℝ}
    (hT : IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧
      projectiveOriginalFlow y 0 t 2 = 1} T) : partialCoreReturnTime y = T := hT.csInf_eq

/-- First-event uniqueness identifies every local branch with one fixed return time. -/
theorem partialCoreReturnTime_eventuallyEq {y : ProjectiveState} {τ : ProjectiveState → ℝ}
    (hτ : ∀ᶠ z in 𝓝 y, IsLeast {t | 0 < t ∧
      t ∈ normalizedMaxDomain (fromProjectiveState z) 0 ∧ projectiveOriginalFlow z 0 t 2 = 1} (τ z)) :
    partialCoreReturnTime =ᶠ[𝓝 y] τ := hτ.mono fun _ h => partialCoreReturnTime_eq h

theorem partialCoreReturnState_eventuallyEq {y : ProjectiveState} {τ : ProjectiveState → ℝ}
    (hτ : ∀ᶠ z in 𝓝 y, IsLeast {t | 0 < t ∧
      t ∈ normalizedMaxDomain (fromProjectiveState z) 0 ∧ projectiveOriginalFlow z 0 t 2 = 1} (τ z)) :
    partialCoreReturnState =ᶠ[𝓝 y] fun z =>
      let out := projectiveOriginalFlow z 0 (τ z)
      ![coreRadius (out 0) (out 2), out 1, out 3] := by
  filter_upwards [hτ, partialCoreReturnTime_eventuallyEq hτ] with z hz ht
  simp only [partialCoreReturnState, ht, toCoreAngleState, hz.1.2.2, one_mul]

/-- The canonical partial-core return has the same C2 regularity as its local event branches. -/
theorem partialCoreReturn_regular {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hR : coreRadius (y 0) (y 2) = k)
    (hV : 1 < y 2) :
    IsLeast {t | 0 < t ∧ projectiveOriginalFlow y 0 t 2 = 1} (partialCoreReturnTime y) ∧
      ContDiffAt ℝ 2 partialCoreReturnTime y ∧ ContDiffAt ℝ 2 partialCoreReturnState y ∧
      (∀ᶠ z in 𝓝 y, IsLeast {t | 0 < t ∧
        t ∈ normalizedMaxDomain (fromProjectiveState z) 0 ∧ projectiveOriginalFlow z 0 t 2 = 1}
          (partialCoreReturnTime z) ∧
        ∀ t ∈ Icc 0 (partialCoreReturnTime z), t ∈ normalizedMaxDomain (fromProjectiveState z) 0 ∧
          0 < 1 + normalizedMaxCurve (fromProjectiveState z) 0 t 0) := by
  obtain ⟨T, _, hfirst, τ, hτ, hcτ, hnear, hcF, _⟩ :=
    exists_partialCore_radius_response hk hy hR hV
  have heq := partialCoreReturnTime_eventuallyEq (hnear.mono fun _ h => h.1)
  have hstate : partialCoreReturnState =ᶠ[𝓝 y] fun z =>
      toCoreAngleState (projectiveOriginalFlow z 0 (τ z)) := by
    filter_upwards [heq] with z hz
    simp only [partialCoreReturnState, hz]
  refine ⟨?_, hcτ.congr_of_eventuallyEq heq, hcF.congr_of_eventuallyEq hstate, ?_⟩
  · rw [heq.self_of_nhds, hτ]
    exact hfirst
  · filter_upwards [hnear, heq] with z hz ht
    simpa only [ht] using hz

end BianchiIX
