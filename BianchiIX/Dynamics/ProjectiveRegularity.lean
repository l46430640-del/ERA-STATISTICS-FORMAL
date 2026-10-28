import BianchiIX.Dynamics.ProjectiveInverse

noncomputable section

namespace BianchiIX

theorem contDiff_projectiveStateDenom (n : WithTop ℕ∞) :
    ContDiff ℝ n projectiveStateDenom := by
  unfold projectiveStateDenom projectiveDenom curvature
  fun_prop

theorem contDiffAt_toProjectiveState (n : WithTop ℕ∞) {x : NormalizedState}
    (hA : 1 + x 0 ≠ 0) : ContDiffAt ℝ n toProjectiveState x := by
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [toProjectiveState, projectiveCoord] <;> fun_prop

theorem contDiffAt_fromProjectiveState (n : WithTop ℕ∞) {y : ProjectiveState}
    (hD : projectiveStateDenom y ≠ 0) : ContDiffAt ℝ n fromProjectiveState y := by
  have hden := (contDiff_projectiveStateDenom n).contDiffAt (x := y)
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [fromProjectiveState] <;> fun_prop

theorem hasDerivAt_toProjectiveState_normalized {alpha : ℝ → NormalizedState} {t : ℝ}
    (hα : HasDerivAt alpha (normalizedField (alpha t)) t)
    (hA : 1 + alpha t 0 ≠ 0) (hc : stateConstraint (alpha t) = 1) :
    HasDerivAt (fun s => toProjectiveState (alpha s))
      ((1 + alpha t 0) • projectiveField (toProjectiveState (alpha t))) t := by
  obtain ⟨hp, hs, ha, hb, hw⟩ := hasDerivAt_normalized_components hα
  obtain ⟨hm, hu, hv, hw⟩ := hasDerivAt_projective_flow
    (p := fun s => alpha s 0) (s := fun s => alpha s 1)
    (a := fun s => alpha s 2) (b := fun s => alpha s 3) (c := fun s => alpha s 4)
    hp hs ha hb hw hA hc
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hm
  · exact hu
  · exact hv
  · exact hw

theorem toProjectiveState_fderiv_field {x : NormalizedState}
    (hA : 1 + x 0 ≠ 0) (hc : stateConstraint x = 1) :
    fderiv ℝ toProjectiveState x (normalizedField x) =
      (1 + x 0) • projectiveField (toProjectiveState x) := by
  let alpha : ℝ → NormalizedState := fun t => x + t • normalizedField x
  have hbase : alpha 0 = x := by simp [alpha]
  have hα : HasDerivAt alpha (normalizedField x) 0 := by
    convert! (hasDerivAt_const (0 : ℝ) x).add
      ((hasDerivAt_id (0 : ℝ)).smul_const (normalizedField x)) using 1
    simp
  have hd := ((contDiffAt_toProjectiveState 1 hA).differentiableAt (by norm_num)).hasFDerivAt
  have H := (hbase.symm ▸ hd).comp_hasDerivAt 0 hα
  have H' := hasDerivAt_toProjectiveState_normalized
    (show HasDerivAt alpha (normalizedField (alpha 0)) 0 by simpa [hbase] using hα)
    (by simpa [hbase] using hA) (by simpa [hbase] using hc)
  simpa only [hbase] using H.unique H'

def projectiveActiveWall (x : NormalizedState) : ℝ := toProjectiveState x 2

theorem contDiffAt_projectiveActiveWall (n : WithTop ℕ∞) {x : NormalizedState}
    (hA : 1 + x 0 ≠ 0) : ContDiffAt ℝ n projectiveActiveWall x :=
  contDiffAt_pi.mp (contDiffAt_toProjectiveState n hA) 2

theorem projectiveActiveWall_fderiv {x : NormalizedState}
    (hA : 1 + x 0 ≠ 0) (v : NormalizedState) :
    fderiv ℝ projectiveActiveWall x v = (fderiv ℝ toProjectiveState x v) 2 := by
  have hd := (hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 4) (toProjectiveState x)).comp x
    ((contDiffAt_toProjectiveState 1 hA).differentiableAt (by norm_num)).hasFDerivAt
  rw [show fderiv ℝ projectiveActiveWall x = _ from hd.fderiv]
  rfl

theorem projectiveActiveWall_fderiv_field {x : NormalizedState}
    (hA : 1 + x 0 ≠ 0) (hc : stateConstraint x = 1) :
    fderiv ℝ projectiveActiveWall x (normalizedField x) =
      (1 + x 0) * projectiveField (toProjectiveState x) 2 := by
  rw [projectiveActiveWall_fderiv hA]
  rw [toProjectiveState_fderiv_field hA hc]
  rfl

end BianchiIX
