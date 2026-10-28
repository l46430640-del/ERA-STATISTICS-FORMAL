import BianchiIX.Dynamics.CoreSectionPhysical
import BianchiIX.Dynamics.ReflectionReturnEstimates

noncomputable section

namespace BianchiIX

open Set

/-- Small positive-wall radius inputs lie on the strictly upward active-wall section. -/
theorem coreRadiusEntry_upward {Y : CoreAngleState} (hk : 2 ≤ Y 0)
    (hu : 0 ≤ Y 1 ∧ Y 1 ≤ 1 / 4) (hw : 0 ≤ Y 2 ∧ Y 2 ≤ 1 / 4) :
    projectiveActiveWall (fromProjectiveState (coreRadiusEntry Y)) = 1 ∧
      0 < normalizedEventRate projectiveActiveWall (fromProjectiveState (coreRadiusEntry Y)) 0 0 := by
  have hD := unit_active_wall_denom_pos (y := coreRadiusEntry Y) rfl hu hw
  have hc := fromProjectiveState_constraint hD.ne'
  have hA := fromProjectiveState_clock_pos hD
  have hcoords := toProjectiveState_fromProjectiveState hD.ne'
  have hroot : 1 ≤ Real.sqrt (Y 0 ^ 2 - 1) := by
    exact (Real.le_sqrt (by norm_num) (by nlinarith only [hk])).mpr (by nlinarith only [hk])
  have hprod : Y 1 * (1 + Y 2) ≤ 5 / 16 := by
    have H := mul_le_mul hu.2 (by linarith only [hw.2] : 1 + Y 2 ≤ 5 / 4)
      (by linarith only [hw.1] : 0 ≤ 1 + Y 2) (by norm_num : (0 : ℝ) ≤ 1 / 4)
    norm_num at H
    exact H
  constructor
  · exact congrFun hcoords 2
  · rw [normalizedEventRate, normalizedMaxCurve_initial, projectiveActiveWall_fderiv_field hA.ne' hc,
      hcoords]
    apply mul_pos hA
    change 0 < activeVelocity (1 + Real.sqrt (Y 0 ^ 2 - 1)) (Y 1) 1 (Y 2)
    dsimp only [activeVelocity, coupling]
    nlinarith only [hroot, hprod, sq_nonneg (Y 1)]

/-- The old growing-wall first return is exactly the new active-wall first return after the physical axis swap. -/
theorem reflectionReturn_first_active {Z : CoreAngleState}
    (hD : 0 < projectiveStateDenom (coreTailEntry Z))
    (hfirst : IsLeast {t : ℝ | 0 < t ∧ projectiveOriginalFlow (coreTailEntry Z) 0 t 3 = 1}
      (reflectionReturnTime Z))
    (hactual : coreRadiusEntry (reflectionReturnState Z) =
      projectiveReflection (projectiveOriginalFlow (coreTailEntry Z) 0 (reflectionReturnTime Z))) :
    let x := axisSwap (fromProjectiveState (coreTailEntry Z))
    IsLeast {t : ℝ | 0 < t ∧ t ∈ normalizedMaxDomain x 0 ∧
      projectiveActiveWall (normalizedMaxCurve x 0 t) = 1} (reflectionReturnTime Z) ∧
      toProjectiveState (normalizedMaxCurve x 0 (reflectionReturnTime Z)) =
        coreRadiusEntry (reflectionReturnState Z) := by
  intro x
  have hc := fromProjectiveState_constraint hD.ne'
  have hcx : stateConstraint x = 1 := (axisSwap_constraint _).trans hc
  have hdom (t : ℝ) (ht : 0 ≤ t) := normalizedMaxDomain_contains_Ici_of_constraint hc 0 ht
  have hflow (t : ℝ) (ht : 0 ≤ t) :
      toProjectiveState (normalizedMaxCurve x 0 t) =
        projectiveReflection (projectiveOriginalFlow (coreTailEntry Z) 0 t) := by
    have hs := NormalizedSymmetry.swap.maxCurve (hdom t ht)
    change normalizedMaxCurve x 0 t =
      axisSwap (normalizedMaxCurve (fromProjectiveState (coreTailEntry Z)) 0 t) at hs
    rw [hs, toProjectiveState_axisSwap]
    rfl
  refine ⟨⟨⟨hfirst.1.1, normalizedMaxDomain_contains_Ici_of_constraint hcx 0 hfirst.1.1.le, ?_⟩,
    ?_⟩, (hflow _ hfirst.1.1.le).trans hactual.symm⟩
  · exact (congrFun (hflow _ hfirst.1.1.le) 2).trans hfirst.1.2
  · intro t ht
    apply hfirst.2
    exact ⟨ht.1, (congrFun (hflow t ht.1.le) 2).symm.trans ht.2.2⟩

end BianchiIX
