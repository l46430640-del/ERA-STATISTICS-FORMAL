import BianchiIX.Dynamics.CoreConnectionChart
import BianchiIX.Dynamics.CompactConnectionBounds
import BianchiIX.Dynamics.CompactConnectionError

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def reflectionReturnTime (Y : CoreAngleState) : ℝ :=
  connectionReturnTime (coreExitConnectionParameters Y)

def reflectionReturnState (Y : CoreAngleState) : CoreAngleState :=
  connectionReturnPhysicalState (coreExitConnectionParameters Y)

def compactConnectionPhysicalState (η : ℝ) (Y : CoreAngleState) : CoreAngleState :=
  ![compactConnectionPhase η Y, compactConnectionState η Y 1, compactConnectionState η Y 3]

theorem connectionEntry_coreExitParameters (Y : CoreAngleState) :
    connectionEntry (coreExitConnectionParameters Y 0) (coreExitConnectionParameters Y 1)
      (coreExitConnectionParameters Y 2) = coreTailEntry Y := by
  ext i
  fin_cases i <;> simp [connectionEntry, coreExitConnectionParameters, coreTailEntry, neg_sub]

theorem connectionReturnState_coreExitParameters (Y : CoreAngleState) :
    connectionReturnState (coreExitConnectionParameters Y) =
      projectiveOriginalFlow (coreTailEntry Y) 0 (reflectionReturnTime Y) := by
  unfold connectionReturnState connectionInitialState
  rw [connectionEntry_coreExitParameters]
  rfl

theorem reflectionReturn_state_reconstruction {Y : CoreAngleState}
    (hm : 1 < -projectiveOriginalFlow (coreTailEntry Y) 0 (reflectionReturnTime Y) 0)
    (hw : projectiveOriginalFlow (coreTailEntry Y) 0 (reflectionReturnTime Y) 3 = 1) :
    coreRadiusEntry (reflectionReturnState Y) =
      projectiveReflection (projectiveOriginalFlow (coreTailEntry Y) 0 (reflectionReturnTime Y)) := by
  unfold reflectionReturnState connectionReturnPhysicalState
  rw [connectionReturnState_coreExitParameters]
  exact coreRadiusEntry_reflected_exit hm hw

/-- The compact two-stage passage is the canonical next-wall return, including its physical output. -/
theorem reflectionReturn_compact_eq {η : ℝ} {Y : CoreAngleState}
    (htail : coreTailValid η Y) (hD : 0 < projectiveStateDenom (compactConnectionEntry η Y))
    (hreturn : entranceReturnValid (compactConnectionEntry η Y)) :
    reflectionReturnTime Y = compactConnectionTime η Y ∧
      reflectionReturnState Y = compactConnectionPhysicalState η Y := by
  obtain ⟨hstate, hfirst⟩ := compactConnection_actual_passage htail hD hreturn
  let p := coreExitConnectionParameters Y
  have hx : connectionInitialState p = fromProjectiveState (coreTailEntry Y) := by
    dsimp only [connectionInitialState, p]
    rw [connectionEntry_coreExitParameters]
  have hdom (t : ℝ) (ht : 0 ≤ t) : t ∈ normalizedMaxDomain (connectionInitialState p) 0 := by
    rw [hx]
    exact normalizedMaxDomain_contains_Ici_of_constraint
      (fromProjectiveState_constraint (coreTailValid_denom_pos htail).ne') 0 ht
  have hfirst' : IsLeast {t : ℝ | 0 < t ∧ t ∈ normalizedMaxDomain (connectionInitialState p) 0 ∧
      projectiveGrowingWall (normalizedMaxCurve (connectionInitialState p) 0 t) = 1}
      (compactConnectionTime η Y) := by
    refine ⟨⟨hfirst.1.1, hdom _ hfirst.1.1.le, ?_⟩, ?_⟩
    · rw [hx]
      exact hfirst.1.2
    · intro t ht
      apply hfirst.2
      refine ⟨ht.1, ?_⟩
      rw [hx] at ht
      exact ht.2.2
  have htime : reflectionReturnTime Y = compactConnectionTime η Y := hfirst'.csInf_eq
  have hs : compactConnectionState η Y = projectiveReflection (connectionReturnState p) := by
    rw [connectionReturnState, hx, show connectionReturnTime p = compactConnectionTime η Y from htime]
    exact hstate
  have hactive : compactConnectionState η Y 2 = 1 := hreturn.1.1.2.2
  refine ⟨htime, ?_⟩
  ext i
  fin_cases i
  · change phaseNorm (-connectionReturnState p 0 - 1) 1 =
      coreRadius (compactConnectionState η Y 0) (compactConnectionState η Y 2)
    rw [hactive, hs]
    rfl
  · exact (congrFun hs 1).symm
  · exact (congrFun hs 3).symm

/-- Pointwise first-return uniqueness on a neighborhood also identifies ordinary derivatives. -/
theorem reflectionReturn_compact_eventuallyEq {η : ℝ} {Y : CoreAngleState}
    (hnear : ∀ᶠ Z in 𝓝 Y, coreTailValid η Z ∧
      0 < projectiveStateDenom (compactConnectionEntry η Z) ∧
      entranceReturnValid (compactConnectionEntry η Z)) :
    reflectionReturnTime =ᶠ[𝓝 Y] compactConnectionTime η ∧
      reflectionReturnState =ᶠ[𝓝 Y] compactConnectionPhysicalState η := by
  exact ⟨hnear.mono fun _ h => (reflectionReturn_compact_eq h.1 h.2.1 h.2.2).1,
    hnear.mono fun _ h => (reflectionReturn_compact_eq h.1 h.2.1 h.2.2).2⟩

end BianchiIX
