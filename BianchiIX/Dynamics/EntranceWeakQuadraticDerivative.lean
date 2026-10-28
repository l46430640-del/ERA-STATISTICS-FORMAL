import BianchiIX.Dynamics.EntranceWeakRemainderBounds

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

theorem entranceWeakQuadratic_differential {y : ProjectiveState} (hm : y 0 + 1 ≠ 0) :
    DifferentiableAt ℝ entranceWeakQuadratic y ∧ ∀ v : ProjectiveState,
      fderiv ℝ entranceWeakQuadratic y v =
        (2 * y 1 ^ 2 - 8 * y 1 * y 3 + 2 * y 3 ^ 2) / (y 0 + 1) ^ 3 * v 0 +
        (2 * (1 - 1 / (y 0 + 1) ^ 2) * y 1 + (-1 + 4 / (y 0 + 1) ^ 2) * y 3) * v 1 +
        ((-1 + 4 / (y 0 + 1) ^ 2) * y 1 - 2 * y 3 / (y 0 + 1) ^ 2) * v 3 := by
  have hi : HasDerivAt (fun t : ℝ => 1 / (t + 1) ^ 2) (-2 / (y 0 + 1) ^ 3) (y 0) := by
    apply ((hasDerivAt_const (y 0) (1 : ℝ)).div (((hasDerivAt_id (y 0)).add_const 1).pow 2)
      (pow_ne_zero 2 hm)).congr_deriv
    dsimp
    field_simp
    ring
  have hd (i : Fin 4) := hasFDerivAt_apply (𝕜 := ℝ) i y
  have hI := hi.comp_hasFDerivAt y (hd 0)
  have hA := (hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) y).sub hI
  have hC := (hasFDerivAt_const (𝕜 := ℝ) (-1 : ℝ) y).add (hI.const_mul 4)
  have H := ((hA.mul ((hd 1).pow 2)).add ((hC.mul (hd 1)).mul (hd 3))).sub (((hd 3).pow 2).mul hI)
  have heq : entranceWeakQuadratic = fun z => (1 - 1 / (z 0 + 1) ^ 2) * z 1 ^ 2 +
      (-1 + 4 * (1 / (z 0 + 1) ^ 2)) * z 1 * z 3 - z 3 ^ 2 * (1 / (z 0 + 1) ^ 2) := by
    funext z
    unfold entranceWeakQuadratic
    ring
  change HasFDerivAt (fun z => (1 - 1 / (z 0 + 1) ^ 2) * z 1 ^ 2 +
    (-1 + 4 * (1 / (z 0 + 1) ^ 2)) * z 1 * z 3 - z 3 ^ 2 * (1 / (z 0 + 1) ^ 2)) _ y at H
  rw [← heq] at H
  refine ⟨H.differentiableAt, fun v => ?_⟩
  rw [H.fderiv]
  simp [sub_apply, add_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply, Function.comp_def]
  ring

/-- The expansion may be differentiated on the open phase domain containing every entrance point. -/
theorem entranceWeakNumerator_expansion_fderiv {y : ProjectiveState}
    (hm : 2 < y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) (v : ProjectiveState) :
    fderiv ℝ entranceWeakNumerator y v =
      fderiv ℝ entranceWeakQuadratic y v + fderiv ℝ entranceWeakRemainder y v := by
  have hm' : ∀ᶠ z : ProjectiveState in 𝓝 y, 2 < z 0 :=
    (continuousAt_apply 0 y).eventually (lt_mem_nhds hm)
  have hu' : ∀ᶠ z : ProjectiveState in 𝓝 y, |z 1| < 1 / 200 :=
    (continuousAt_apply 1 y).abs.eventually (gt_mem_nhds hu)
  have hw' : ∀ᶠ z : ProjectiveState in 𝓝 y, |z 3| < 1 / 200 :=
    (continuousAt_apply 3 y).abs.eventually (gt_mem_nhds hw)
  have heq : entranceWeakNumerator =ᶠ[𝓝 y] (fun z => entranceWeakQuadratic z + entranceWeakRemainder z) := by
    filter_upwards [hm', hu', hw'] with z hmz huz hwz
    exact entranceWeakNumerator_quadratic_expansion hmz.le huz hwz
  rw [heq.fderiv_eq, fderiv_fun_add (entranceWeakQuadratic_differential (by linarith)).1
    (entranceWeakRemainder_differential hm.le hu hw).1]
  rfl

end BianchiIX
