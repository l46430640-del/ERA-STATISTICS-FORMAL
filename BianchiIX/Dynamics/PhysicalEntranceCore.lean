import BianchiIX.Dynamics.PhysicalEntranceData

noncomputable section

namespace BianchiIX

open Set

def referenceCoreWallFloor (K : ℝ) : ℝ := Real.sqrt 3 / (4 + (1 + K) ^ 2)

theorem referenceCoreWallFloor_pos (K : ℝ) : 0 < referenceCoreWallFloor K := by
  unfold referenceCoreWallFloor
  positivity

theorem referenceCore_endpoint_bounds {k K : ℝ} (hk : 2 ≤ k ∧ k ≤ K) :
    2 ≤ referencePulse k (-referenceHalfTime k) 0 ∧
      2 * referenceCoreWallFloor K ≤ fromProjectiveState (referencePulse k (-referenceHalfTime k)) 3 := by
  have hk1 : 1 < k := by linarith only [hk.1]
  have hroot : Real.sqrt (k ^ 2 - 1) ^ 2 = k ^ 2 - 1 := Real.sq_sqrt (by nlinarith only [hk.1])
  have hr0 := Real.sqrt_nonneg (k ^ 2 - 1)
  have hrlo : 1 ≤ Real.sqrt (k ^ 2 - 1) := Real.le_sqrt_of_sq_le (by nlinarith only [hk.1])
  have hrhi : Real.sqrt (k ^ 2 - 1) ≤ k := by nlinarith only [hroot, hr0, hk.1]
  have hm : 0 ≤ 1 + Real.sqrt (k ^ 2 - 1) := by positivity
  have hmK : 1 + Real.sqrt (k ^ 2 - 1) ≤ 1 + K := by linarith only [hrhi, hk.2]
  have hden : 4 + (1 + Real.sqrt (k ^ 2 - 1)) ^ 2 ≤ 4 + (1 + K) ^ 2 := by
    nlinarith only [(sq_le_sq₀ hm (hm.trans hmK)).mpr hmK]
  have hrt : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hrt0 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  rw [referencePulse_entry hk1]
  refine ⟨by change 2 ≤ 1 + Real.sqrt (k ^ 2 - 1); linarith only [hrlo], ?_⟩
  have he : fromProjectiveState (![1 + Real.sqrt (k ^ 2 - 1), 0, 1, 0] : ProjectiveState) 3 =
      2 * Real.sqrt 3 / (4 + (1 + Real.sqrt (k ^ 2 - 1)) ^ 2) := by
    simp [fromProjectiveState, projectiveStateDenom, projectiveDenom, curvature]
    field_simp
    nlinarith only [hrt]
  rw [he]
  have H := div_le_div_of_nonneg_left (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hrt0.le)
    (by positivity : 0 < 4 + (1 + Real.sqrt (k ^ 2 - 1)) ^ 2) hden
  simpa only [referenceCoreWallFloor, mul_div_assoc] using H

/-- The ordinary physical-coordinate event data agree with the original constrained orbit. -/
theorem physicalEntranceData_actual {x : NormalizedState}
    (hc : stateConstraint x = 1) (hA : 0 < 1 + x 0)
    (hv : entranceReturnValid (toProjectiveState x)) :
    let T := (physicalEntranceData x).1
    let X := normalizedMaxCurve x 0 T
    IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain x 0 ∧ projectiveActiveWall (normalizedMaxCurve x 0 t) = 1} T ∧
      (physicalEntranceData x).2.1 = toProjectiveState X ∧
      (physicalEntranceData x).2.2.1 = X ∧
      (physicalEntranceData x).2.1 2 = 1 ∧ 0 < 1 + X 0 ∧
      HasDerivAt (fun t => projectiveActiveWall (normalizedMaxCurve x 0 t))
        (normalizedEventRate projectiveActiveWall x 0 T) T ∧
      0 < normalizedEventRate projectiveActiveWall x 0 T := by
  intro T X
  have hback := fromProjectiveState_toProjectiveState hA.ne' hc
  have H := hv
  dsimp only [entranceReturnValid] at H
  rw [hback] at H
  change IsLeast _ T ∧ _ at H
  have htime : T ∈ Icc 0 T := ⟨H.1.1.1.le, le_rfl⟩
  have hAX : 0 < 1 + X 0 := (H.2.1 T htime).2
  have hcX : stateConstraint X = 1 := (normalizedMaxCurve_constraint H.1.1.2.1).trans hc
  have hP : (physicalEntranceData x).2.1 = toProjectiveState X := by
    change toProjectiveState (normalizedMaxCurve (fromProjectiveState (toProjectiveState x)) 0 T) = _
    rw [hback]
  have hphys : (physicalEntranceData x).2.2.1 = X := by
    change fromProjectiveState ((physicalEntranceData x).2.1) = X
    rw [hP, fromProjectiveState_toProjectiveState hAX.ne' hcX]
  refine ⟨H.1, hP, hphys, ?_, hAX, ?_, H.2.2.2 T htime⟩
  · rw [hP]
    exact H.1.1.2.2
  · exact ((contDiffAt_projectiveActiveWall 1 hAX.ne').differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt T
      (hasDerivAt_normalizedMaxCurve H.1.1.2.1)

/-- At a positive core the physical wall products give the required quadratic weak amplitude. -/
theorem physical_core_weak_sum {x : NormalizedState} {Δ n : ℝ}
    (hp : positiveWalls x) (hA : 0 < 1 + x 0) (hv : toProjectiveState x 2 = 1)
    (hprod : normalizedWallProductsBound Δ x) (hn : 0 < n) (hwall : n ≤ x 3) :
    0 < toProjectiveState x 1 ∧ 0 < toProjectiveState x 3 ∧
      toProjectiveState x 1 + toProjectiveState x 3 ≤ Δ ^ 2 / (2 * n ^ 2) := by
  have hrt : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  have hscale : 1 + x 0 = Real.sqrt 3 * x 3 := by
    change Real.sqrt 3 * x 3 / (1 + x 0) = 1 at hv
    have H := (div_eq_iff hA.ne').mp hv
    linarith only [H]
  have hU : toProjectiveState x 1 = x 2 / x 3 := by
    change Real.sqrt 3 * x 2 / (1 + x 0) = _
    rw [hscale]
    field_simp
  have hW : toProjectiveState x 3 = x 4 / x 3 := by
    change Real.sqrt 3 * x 4 / (1 + x 0) = _
    rw [hscale]
    field_simp
  obtain ⟨hup, _, hwp⟩ := toProjectiveState_positive hA hp
  refine ⟨hup, hwp, ?_⟩
  have hsum : (toProjectiveState x 1 + toProjectiveState x 3) * x 3 = x 2 + x 4 := by
    rw [hU, hW]
    field_simp [hp.2.1.ne']
  have hprod' : 2 * x 3 * (x 2 + x 4) ≤ Δ ^ 2 := by nlinarith only [hprod.1, hprod.2.1]
  have hnsq : n ^ 2 ≤ x 3 ^ 2 := (sq_le_sq₀ hn.le hp.2.1.le).mpr hwall
  apply (le_div_iff₀ (by positivity : 0 < 2 * n ^ 2)).mpr
  have H := mul_le_mul_of_nonneg_left hnsq (add_pos hup hwp).le
  have hsum2 := congrArg (fun r : ℝ => r * x 3) hsum
  nlinarith only [H, hsum2, hprod']

end BianchiIX
