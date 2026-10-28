import BianchiIX.Dynamics.CoreTaubVisit
import BianchiIX.Dynamics.CoreReflectionOrbit

noncomputable section

namespace BianchiIX

/-- The entire forward exact orbit stays at least `ε` from all three Taub points. -/
def normalizedTaubAvoidance (ε : ℝ) (x : NormalizedState) : Prop :=
  ∀ t, 0 ≤ t → t ∈ normalizedMaxDomain x 0 →
    ∀ i, ε ≤ normalizedEuclideanDistance (normalizedMaxCurve x 0 t) (taubPoint i)

theorem normalizedTaubAvoidance.initial {ε : ℝ} {x : NormalizedState}
    (H : normalizedTaubAvoidance ε x) : ∀ i, ε ≤ normalizedEuclideanDistance x (taubPoint i) := by
  simpa only [normalizedMaxCurve_initial] using H 0 le_rfl (initial_mem_normalizedMaxDomain x 0)

theorem normalizedTaubAvoidance.forward {ε s : ℝ} {x : NormalizedState}
    (H : normalizedTaubAvoidance ε x) (hs : 0 ≤ s) (hdom : s ∈ normalizedMaxDomain x 0) :
    normalizedTaubAvoidance ε (normalizedMaxCurve x 0 s) := by
  intro t ht htime i
  obtain ⟨hfull, heq⟩ := normalizedMaxCurve_restart (t := t + s) hdom (by simpa only [add_sub_cancel_right] using htime)
  simp only [add_sub_cancel_right] at heq
  rw [← heq]
  exact H _ (add_nonneg ht hs) hfull i

theorem normalizedTaubAvoidance.frame {ε : ℝ} {x : NormalizedState}
    (H : normalizedTaubAvoidance ε x) (i : Fin 6) :
    normalizedTaubAvoidance ε ((axisFrame i).map x) := by
  intro t ht hdom j
  rw [(axisFrame i).maxDomain] at hdom
  rw [(axisFrame i).maxCurve hdom]
  exact axisFrame_away_taub (H t ht hdom) i j

/-- The projective endpoint identity reconstructs the physical endpoint, even below radius two. -/
theorem coreReflection_normalized_endpoint {Y : CoreAngleState}
    (hcore : coreRadiusReturnValid Y) (hT : 0 < coreReflectionTime Y)
    (hentry : coreRadiusEntry (coreReflectionState coreRadiusReturnTime Y) =
      projectiveReflection (projectiveOriginalFlow (coreRadiusEntry Y) 0 (coreReflectionTime Y))) :
    fromProjectiveState (coreRadiusEntry (coreReflectionState coreRadiusReturnTime Y)) =
      axisSwap (normalizedMaxCurve (fromProjectiveState (coreRadiusEntry Y)) 0 (coreReflectionTime Y)) := by
  let x := fromProjectiveState (coreRadiusEntry Y)
  let T := coreReflectionTime Y
  have hc : stateConstraint x = 1 := fromProjectiveState_constraint (coreRadiusReturnValid_denom_pos hcore).ne'
  have hd : T ∈ normalizedMaxDomain x 0 := normalizedMaxDomain_contains_Ici_of_constraint hc 0 hT.le
  have hA : 1 + normalizedMaxCurve x 0 T 0 ≠ 0 := by
    intro hz
    have H := congrArg (fun y : ProjectiveState => y 2) hentry
    change 1 = projectiveCoord (normalizedMaxCurve x 0 T 0) (normalizedMaxCurve x 0 T 4) at H
    simp only [projectiveCoord, hz, div_zero] at H
    norm_num at H
  rw [hentry, fromProjectiveState_reflection]
  exact congrArg axisSwap (fromProjectiveState_toProjectiveState hA ((normalizedMaxCurve_constraint hd).trans hc))

theorem normalizedTaubAvoidance.coreReflection {ε : ℝ} {Y : CoreAngleState}
    (H : normalizedTaubAvoidance ε (fromProjectiveState (coreRadiusEntry Y)))
    (hcore : coreRadiusReturnValid Y) (hT : 0 < coreReflectionTime Y)
    (hentry : coreRadiusEntry (coreReflectionState coreRadiusReturnTime Y) =
      projectiveReflection (projectiveOriginalFlow (coreRadiusEntry Y) 0 (coreReflectionTime Y))) :
    normalizedTaubAvoidance ε
      (fromProjectiveState (coreRadiusEntry (coreReflectionState coreRadiusReturnTime Y))) := by
  rw [coreReflection_normalized_endpoint hcore hT hentry]
  have hc := fromProjectiveState_constraint (coreRadiusReturnValid_denom_pos hcore).ne'
  exact (H.forward hT.le (normalizedMaxDomain_contains_Ici_of_constraint hc 0 hT.le)).frame 3

end BianchiIX
