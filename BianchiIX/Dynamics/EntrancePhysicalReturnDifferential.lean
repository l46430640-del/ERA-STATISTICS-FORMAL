import BianchiIX.Dynamics.EntranceReturnCorrection

noncomputable section

namespace BianchiIX

open Set

theorem EntranceRadialInverseAt.return_correction_difference {y : ProjectiveState}
    {Ψ : ProjectiveState → ProjectiveState} (HΨ : EntranceRadialInverseAt y Ψ)
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) (d : ProjectiveState) :
    let z := entranceRadialCoordinates y
    let Q := fun z => entranceStableRadius (entranceReturnState (Ψ z))
    let F := fun z => coreRadius (entranceReturnState (Ψ z) 0) (entranceReturnState (Ψ z) 2)
    let E := fun z => entranceRadiusCorrection (entranceReturnState (Ψ z))
    fderiv ℝ E z d = fderiv ℝ Q z d - fderiv ℝ F z d := by
  intro z Q F E
  have HR := (entranceReturn_regular hk hm hu hv hw).1
  have hp : entranceRegion (coreRadius (y 0) (y 2)) (entranceReturnState y) :=
    entranceReturn_region hk hm hu hv hw _ ⟨HR.1.1.1.le, le_rfl⟩
  have hV : 0 < entranceReturnState y 2 := by
    rw [(entranceReturn_active_component hk hm hu hv hw).1]
    norm_num
  have hM : 2 ≤ entranceReturnState y 0 := by linarith [(entranceRegion_phase hk hp).1]
  have hU : |entranceReturnState y 1| < 1 / 200 := by rw [abs_of_nonneg hp.2.2.1.1]; linarith [hp.2.2.1.2]
  have hW : |entranceReturnState y 3| < 1 / 200 := by rw [abs_of_nonneg hp.2.2.2.2.1]; linarith [hp.2.2.2.2.2]
  have hg := (HΨ.hasFDerivAt_return hk hm hu hv hw).differentiableAt
  have hQ : DifferentiableAt ℝ Q z := by
    have hf : DifferentiableAt ℝ entranceStableRadius (entranceReturnState (Ψ z)) := by
      dsimp only [z]
      rw [HΨ.apply_base]
      exact (contDiffAt_entranceStableRadius_two hM hU hW hV).differentiableAt (by norm_num)
    have Hcomp := hf.comp z hg
    exact Hcomp
  have hF : DifferentiableAt ℝ F z := by
    have hf : DifferentiableAt ℝ (fun p : ProjectiveState => coreRadius (p 0) (p 2))
        (entranceReturnState (Ψ z)) := by
      dsimp only [z]
      rw [HΨ.apply_base]
      exact (hasFDerivAt_coreRadius_state hV).differentiableAt
    have Hcomp := hf.comp z hg
    exact Hcomp
  have H := hQ.hasFDerivAt.sub hF.hasFDerivAt
  change HasFDerivAt E (fderiv ℝ Q z - fderiv ℝ F z) z at H
  rw [H.fderiv, sub_apply]

end BianchiIX
