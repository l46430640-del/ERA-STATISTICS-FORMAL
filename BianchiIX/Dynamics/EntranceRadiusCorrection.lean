import BianchiIX.Dynamics.EntranceRadialQuotient

noncomputable section

namespace BianchiIX

def entranceRadiusCorrection (y : ProjectiveState) : ℝ :=
  entranceStableRadius y - coreRadius (y 0) (y 2)

theorem contDiffAt_entranceRadiusCorrection_two {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) (hv : 0 < y 2) :
    ContDiffAt ℝ 2 entranceRadiusCorrection y := by
  have hR : ContDiffAt ℝ 2 (fun z : ProjectiveState => coreRadius (z 0) (z 2)) y := by
    change ContDiffAt ℝ 2 (fun z : ProjectiveState => Real.sqrt ((z 0 - 1) ^ 2 + (z 2) ^ 2)) y
    apply ContDiffAt.sqrt (by fun_prop)
    positivity
  exact (contDiffAt_entranceStableRadius_two hm hu hw hv).sub hR

theorem hasFDerivAt_coreRadius_state {y : ProjectiveState} (hv : 0 < y 2) :
    HasFDerivAt (fun z : ProjectiveState => coreRadius (z 0) (z 2))
      ((1 / coreRadius (y 0) (y 2)) •
        ((y 0 - 1) • (ContinuousLinearMap.proj (0 : Fin 4) : ProjectiveState →L[ℝ] ℝ) +
          y 2 • (ContinuousLinearMap.proj (2 : Fin 4) : ProjectiveState →L[ℝ] ℝ))) y := by
  have H := ((((hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 4) y).sub_const 1).pow 2).add
    ((hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 4) y).pow 2)).sqrt
      (by change (y 0 - 1) ^ 2 + y 2 ^ 2 ≠ 0; positivity)
  convert! H using 1
  ext v
  simp only [add_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  simp only [Pi.add_apply, Nat.reduceSub, pow_one, nsmul_eq_mul, Nat.cast_ofNat, coreRadius, coreEnergy]
  ring

theorem EntranceRadialInverseAt.correction_differential {y : ProjectiveState}
    {Ψ : ProjectiveState → ProjectiveState} (H : EntranceRadialInverseAt y Ψ)
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) (hv : 0 < y 2)
    (d : ProjectiveState) :
    fderiv ℝ (fun z => entranceRadiusCorrection (Ψ z)) (entranceRadialCoordinates y) d =
      d 0 - ((y 0 - 1) * (entranceRadialInverseDifferential y d) 0 + y 2 * d 2) / coreRadius (y 0) (y 2) := by
  have hΨ := H.contDiffAt.differentiableAt (by norm_num)
  have hr : DifferentiableAt ℝ entranceStableRadius (Ψ (entranceRadialCoordinates y)) := by
    rw [H.apply_base]
    exact (contDiffAt_entranceStableRadius_two hm hu hw hv).differentiableAt (by norm_num)
  have hR := (hasFDerivAt_coreRadius_state hv).differentiableAt
  have hR' : DifferentiableAt ℝ (fun z : ProjectiveState => coreRadius (z 0) (z 2))
      (Ψ (entranceRadialCoordinates y)) := by rw [H.apply_base]; exact hR
  change fderiv ℝ (fun z => entranceStableRadius (Ψ z) - coreRadius (Ψ z 0) (Ψ z 2)) _ d = _
  have hsub := (hr.comp _ hΨ).hasFDerivAt.sub (hR'.comp _ hΨ).hasFDerivAt
  simp only [Function.comp_def] at hsub
  change HasFDerivAt (fun z => entranceStableRadius (Ψ z) - coreRadius (Ψ z 0) (Ψ z 2)) _ _ at hsub
  rw [hsub.fderiv, sub_apply,
    H.radius_differential, H.scalar_differential hR, (hasFDerivAt_coreRadius_state hv).fderiv]
  simp only [smul_apply, add_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  have hvcol : (entranceRadialInverseDifferential y d) 2 = d 2 := by
    simp [entranceRadialInverseDifferential_apply]
  rw [hvcol]
  ring

theorem EntranceRadialInverseAt.correction_partials {y : ProjectiveState}
    {Ψ : ProjectiveState → ProjectiveState} (H : EntranceRadialInverseAt y Ψ)
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) (hv : 0 < y 2) :
    let D := fderiv ℝ (fun z => entranceRadiusCorrection (Ψ z)) (entranceRadialCoordinates y)
    let R := coreRadius (y 0) (y 2)
    D (Pi.single 0 1) = 1 - (y 0 - 1) * entranceStableRadius y /
      (R * (entranceStablePhase y - 1) * entranceStablePartial y 0) ∧
    D (Pi.single 1 1) = (y 0 - 1) * entranceStablePartial y 1 / (R * entranceStablePartial y 0) ∧
    D (Pi.single 3 1) = (y 0 - 1) * entranceStablePartial y 3 / (R * entranceStablePartial y 0) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  all_goals
    simp [H.correction_differential hm hu hw hv, entranceRadialInverseDifferential_apply,
      div_eq_mul_inv, mul_inv_rev]
    ring

end BianchiIX
