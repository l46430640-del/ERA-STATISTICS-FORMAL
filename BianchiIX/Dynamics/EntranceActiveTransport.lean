import BianchiIX.Dynamics.EntranceReturnTransport

noncomputable section

namespace BianchiIX

/-- The active input is recovered by applying the mixed response once in the remaining flow direction. -/
theorem EntranceRadialInverseAt.return_active_direction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {y : ProjectiveState} {Ψ : ProjectiveState → ProjectiveState} (HΨ : EntranceRadialInverseAt y Ψ)
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000)
    {p : ProjectiveState → E} (hp : DifferentiableAt ℝ p (entranceReturnState y)) :
    let D := fderiv ℝ (fun z => p (entranceReturnState (Ψ z))) (entranceRadialCoordinates y)
    y 2 • D (Pi.single 2 1) =
      -D ![entranceRadialDrift y, y 1 * entranceStrongLogRate y, 0, y 3 * entranceWeakLogRate y] := by
  intro D
  have hy : entranceRegion (coreRadius (y 0) (y 2)) y :=
    ⟨hm, by rw [sub_self, abs_zero]; linarith, hu, ⟨hv.1.le, hv.2.le⟩, hw⟩
  have hp' : HasFDerivAt p (fderiv ℝ p (entranceReturnState y))
      (entranceReturnState (Ψ (entranceRadialCoordinates y))) := by
    rw [HΨ.apply_base]
    exact hp.hasFDerivAt
  have HD := hp'.comp (entranceRadialCoordinates y) (HΨ.hasFDerivAt_return hk hm hu hv hw)
  simp only [Function.comp_def] at HD
  have Hzero : D (entranceRadialDifferential y (entranceLogField y)) = 0 := by
    dsimp [D]
    rw [HD.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      (entranceRegion_radialDifferential_inverse hk hy hv.1).1,
      (entranceReturnState_fderiv_field hk hm hu hv hw).2, map_zero]
  have heq : entranceRadialDifferential y (entranceLogField y) =
      ![entranceRadialDrift y, y 1 * entranceStrongLogRate y, 0, y 3 * entranceWeakLogRate y] +
        y 2 • Pi.single 2 1 := by
    rw [entranceRadialDifferential_logField hk hy hv.1]
    ext i
    fin_cases i <;> simp
  rw [heq, map_add, map_smul] at Hzero
  exact eq_neg_of_add_eq_zero_right Hzero

theorem entranceLogWalls_comp_fderiv_scale {g : ProjectiveState → ProjectiveState} {z : ProjectiveState}
    (hg : DifferentiableAt ℝ g z) (hu : g z 1 ≠ 0) (hw : g z 3 ≠ 0) (k : ℝ) (d : ProjectiveState) :
    fderiv ℝ (fun q => entranceLogWalls k (g q)) z d =
      ![fderiv ℝ (fun q => entranceLogWalls 1 (g q)) z d 0,
        k ^ 2 * fderiv ℝ (fun q => entranceLogWalls 1 (g q)) z d 1] := by
  have HE (a : ℝ) : fderiv ℝ (fun q => entranceLogWalls a (g q)) z d =
      entranceWallTangent a (g z) (fderiv ℝ g z d) := by
    have H := (hasFDerivAt_entranceLogWalls a hu hw).differentiableAt.hasFDerivAt.comp z hg.hasFDerivAt
    simp only [Function.comp_def] at H
    rw [H.fderiv, ContinuousLinearMap.comp_apply, entranceLogWalls_fderiv_apply a hu hw]
  rw [HE k, HE 1]
  ext i
  fin_cases i <;> simp [entranceWallTangent]

end BianchiIX
