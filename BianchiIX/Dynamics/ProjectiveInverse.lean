import BianchiIX.Dynamics.ProjectiveState

noncomputable section

namespace BianchiIX

theorem hasDerivAt_projectiveStateDenom {β : ℝ → ProjectiveState} {τ : ℝ}
    (hβ : HasDerivAt β (projectiveField (β τ)) τ) :
    HasDerivAt (fun t => projectiveStateDenom (β t))
      (-coupling (β τ 1) (β τ 2) (β τ 3) * projectiveStateDenom (β τ) -
        2 * curvature (β τ 1) (β τ 2) (β τ 3)) τ := by
  have hm := hasDerivAt_pi.mp hβ 0
  have hu := hasDerivAt_pi.mp hβ 1
  have hv := hasDerivAt_pi.mp hβ 2
  have hw := hasDerivAt_pi.mp hβ 3
  convert! (hm.pow 2).const_add 3 |>.add
    (((hu.pow 2).add (hv.pow 2) |>.add (hw.pow 2)).sub
      (((hu.mul hv).add (hv.mul hw) |>.add (hw.mul hu)).const_mul 2)) using 1
  dsimp [projectiveStateDenom, projectiveDenom, projectiveField, curvature,
    phaseVelocity, strongVelocity, activeVelocity, weakVelocity, coupling]
  ring

theorem hasDerivAt_inverseProjectiveScale {β : ℝ → ProjectiveState} {τ : ℝ}
    (hβ : HasDerivAt β (projectiveField (β τ)) τ)
    (hD : projectiveStateDenom (β τ) ≠ 0) :
    HasDerivAt (fun t => 6 / projectiveStateDenom (β t))
      ((6 / projectiveStateDenom (β τ)) * coupling (β τ 1) (β τ 2) (β τ 3) +
        (6 / projectiveStateDenom (β τ)) ^ 2 * curvature (β τ 1) (β τ 2) (β τ 3) / 3) τ := by
  convert! (hasDerivAt_const τ (6 : ℝ)).div (hasDerivAt_projectiveStateDenom hβ) hD using 1
  field_simp
  ring

theorem inverse_projective_field_identity (A m u v w : ℝ)
    (hD : A * projectiveDenom m u v w = 6) :
    let B := A * coupling u v w + A ^ 2 * curvature u v w / 3
    A • ![B, (B * m + A * phaseVelocity m u v w) / Real.sqrt 3,
      (B * u + A * strongVelocity m u v w) / Real.sqrt 3,
      (B * v + A * activeVelocity m u v w) / Real.sqrt 3,
      (B * w + A * weakVelocity m u v w) / Real.sqrt 3] =
      normalizedField ![A - 1, A * m / Real.sqrt 3, A * u / Real.sqrt 3,
        A * v / Real.sqrt 3, A * w / Real.sqrt 3] := by
  have hr : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hr2 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hd : A * (3 + m ^ 2 + curvature u v w) = 6 := hD
  dsimp [curvature] at hd
  ext i
  fin_cases i <;>
    dsimp [normalizedField, shearPlus, shearMinus, rateOne, rateTwo, rateThree,
      shearSq, phaseVelocity, strongVelocity, activeVelocity, weakVelocity, coupling,
      curvature] <;>
    field_simp <;> ring_nf <;> rw [hr2] <;> ring_nf
  · linear_combination (6 * A - 9) * A * u * hd
  · linear_combination 3 * A ^ 2 * v * hd
  · linear_combination 3 * A ^ 2 * w * hd

theorem hasDerivAt_fromProjectiveState {β : ℝ → ProjectiveState} {τ : ℝ}
    (hβ : HasDerivAt β (projectiveField (β τ)) τ)
    (hD : projectiveStateDenom (β τ) ≠ 0) :
    HasDerivAt (fun t => fromProjectiveState (β t))
      ((projectiveStateDenom (β τ) / 6) • normalizedField (fromProjectiveState (β τ))) τ := by
  let y := β τ
  let A := 6 / projectiveStateDenom y
  let B := A * coupling (y 1) (y 2) (y 3) + A ^ 2 * curvature (y 1) (y 2) (y 3) / 3
  let W : NormalizedState := ![B,
    (B * y 0 + A * projectiveField y 0) / Real.sqrt 3,
    (B * y 1 + A * projectiveField y 1) / Real.sqrt 3,
    (B * y 2 + A * projectiveField y 2) / Real.sqrt 3,
    (B * y 3 + A * projectiveField y 3) / Real.sqrt 3]
  have hA := hasDerivAt_inverseProjectiveScale hβ hD
  have hW : HasDerivAt (fun t => fromProjectiveState (β t)) W τ := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact hA.sub_const 1
    · exact (hA.mul (hasDerivAt_pi.mp hβ 0)).div_const (Real.sqrt 3)
    · exact (hA.mul (hasDerivAt_pi.mp hβ 1)).div_const (Real.sqrt 3)
    · exact (hA.mul (hasDerivAt_pi.mp hβ 2)).div_const (Real.sqrt 3)
    · exact (hA.mul (hasDerivAt_pi.mp hβ 3)).div_const (Real.sqrt 3)
  have hAD : A * projectiveDenom (y 0) (y 1) (y 2) (y 3) = 6 := by
    change 6 / projectiveStateDenom y * projectiveStateDenom y = 6
    exact div_mul_cancel₀ _ hD
  have hfield : A • W = normalizedField (fromProjectiveState y) :=
    inverse_projective_field_identity A (y 0) (y 1) (y 2) (y 3) hAD
  have hinv : projectiveStateDenom y / 6 * A = 1 := by
    dsimp [A]
    field_simp [show projectiveStateDenom y ≠ 0 from hD]
  change HasDerivAt _ ((projectiveStateDenom y / 6) • normalizedField (fromProjectiveState y)) τ
  rw [← hfield, smul_smul, hinv, one_smul]
  exact hW

theorem hasDerivAt_reparametrized_fromProjectiveState {β : ℝ → ProjectiveState}
    {clock : ℝ → ℝ} {t : ℝ}
    (hβ : HasDerivAt β (projectiveField (β (clock t))) (clock t))
    (hD : projectiveStateDenom (β (clock t)) ≠ 0)
    (hclock : HasDerivAt clock (6 / projectiveStateDenom (β (clock t))) t) :
    HasDerivAt (fun u => fromProjectiveState (β (clock u)))
      (normalizedField (fromProjectiveState (β (clock t)))) t := by
  have h := (hasDerivAt_fromProjectiveState hβ hD).scomp t hclock
  have hscale : (6 / projectiveStateDenom (β (clock t))) *
      (projectiveStateDenom (β (clock t)) / 6) = 1 := by field_simp
  simp only [smul_smul, hscale, one_smul] at h
  convert! h using 1

end BianchiIX
