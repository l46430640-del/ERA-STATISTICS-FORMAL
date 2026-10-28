import BianchiIX.Dynamics.CompactCoreReturn
import BianchiIX.Dynamics.CoreRadiusArrival

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem coreRadiusReturnTime_eq_of_first {Y : CoreAngleState} {T : ℝ}
    (hT : IsLeast {t | 0 < t ∧ projectiveOriginalFlow (coreRadiusEntry Y) 0 t 2 = 1} T)
    (hdom : T ∈ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry Y)) 0) :
    coreRadiusReturnTime Y = T := by
  apply IsLeast.csInf_eq
  exact ⟨⟨hT.1.1, hdom, hT.1.2⟩, fun t ht => hT.2 ⟨ht.1, ht.2.2⟩⟩

/-- Local first-return times coincide with the fixed return defined on the actual flow domain. -/
theorem coreRadiusReturnTime_eventuallyEq {Y : CoreAngleState} {τ : CoreAngleState → ℝ}
    (hτ : ∀ᶠ Z in 𝓝 Y,
      IsLeast {t | 0 < t ∧ projectiveOriginalFlow (coreRadiusEntry Z) 0 t 2 = 1} (τ Z) ∧
        τ Z ∈ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry Z)) 0) :
    coreRadiusReturnTime =ᶠ[𝓝 Y] τ :=
  hτ.mono fun _ h => coreRadiusReturnTime_eq_of_first h.1 h.2

/-- The compact-core and large-core constructions use the same actual first return. -/
theorem coreRadiusReturn_large_regular {Y : CoreAngleState} (hk : 6 ≤ Y 0)
    (hu : 0 ≤ Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0)
    (hw : 0 ≤ Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0) :
    coreRadiusReturnValid Y ∧ ContDiffAt ℝ 1 coreRadiusReturnTime Y ∧
      ContDiffAt ℝ 1 (coreReturnState coreRadiusReturnTime) Y ∧
      (∀ᶠ Z in 𝓝 Y,
        IsLeast {t | 0 < t ∧ projectiveOriginalFlow (coreRadiusEntry Z) 0 t 2 = 1}
          (coreRadiusReturnTime Z)) := by
  obtain ⟨T, hT, hfirst, τ, hτ, hcτ, hnear, hcF, _⟩ := exists_large_core_radius_arrival hk hu hw
  have heq := coreRadiusReturnTime_eventuallyEq (hnear.mono fun Z h =>
    ⟨h.1, (h.2 (τ Z) ⟨h.1.1.1.le, le_rfl⟩).1⟩)
  have hstate : coreReturnState coreRadiusReturnTime =ᶠ[𝓝 Y] coreReturnState τ := by
    filter_upwards [heq] with Z hZ
    simp only [coreReturnState, hZ]
  have htime : coreRadiusReturnTime Y = T := heq.self_of_nhds.trans hτ
  refine ⟨?_, hcτ.congr_of_eventuallyEq heq, hcF.congr_of_eventuallyEq hstate, ?_⟩
  · obtain ⟨S, _, hS, hcore, _, _, hneg, _⟩ := exists_large_core_traversal hk hu hw
    have hST : S = T := hS.unique hfirst
    subst S
    have hD := (coreRegion_clock_regular hk (coreRadiusEntry_region hk hu hw)).1
    have hc := fromProjectiveState_constraint hD.ne'
    have hdom (t : ℝ) (ht : 0 ≤ t) :
        t ∈ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry Y)) 0 :=
      normalizedMaxDomain_contains_Ici_of_constraint hc 0 ht
    change coreRadiusReturnValid Y
    dsimp only [coreRadiusReturnValid]
    rw [htime]
    refine ⟨⟨⟨hT, hdom T hT.le, hfirst.1.2⟩,
      fun t ht => hfirst.2 ⟨ht.1, ht.2.2⟩⟩,
      fun t ht => ⟨hdom t ht.1, (hcore t ht).1⟩, ?_, ?_⟩
    · intro t ht
      have hv : 1 ≤ projectiveOriginalFlow (coreRadiusEntry Y) 0 t 2 :=
        (hcore t ⟨ht.1.le, ht.2.le⟩).2.2.1
      exact lt_of_le_of_ne hv (fun he => (not_le_of_gt ht.2) (hfirst.2 ⟨ht.1, he.symm⟩))
    · have hA := (hcore T ⟨hT.le, le_rfl⟩).1
      have hd := ((contDiffAt_projectiveActiveWall 1 hA.ne').differentiableAt
        (by norm_num)).hasFDerivAt.comp_hasDerivAt T (hasDerivAt_normalizedMaxCurve (hdom T hT.le))
      change HasDerivAt (fun t => projectiveOriginalFlow (coreRadiusEntry Y) 0 t 2)
        (normalizedEventRate projectiveActiveWall (fromProjectiveState (coreRadiusEntry Y)) 0 T) T at hd
      rwa [← hd.deriv]
  · filter_upwards [hnear, heq] with Z hZ ht
    rw [ht]
    exact hZ.1

end BianchiIX
