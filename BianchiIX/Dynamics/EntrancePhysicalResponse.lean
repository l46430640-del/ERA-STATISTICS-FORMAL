import BianchiIX.Dynamics.EntrancePhysicalBounds
import BianchiIX.Dynamics.EntranceRadialVariationBounds

noncomputable section

namespace BianchiIX

def entrancePhysicalResponse (y : ProjectiveState) : ProjectiveState →L[ℝ] ℝ :=
  (fderiv ℝ (fun z => coreRadius (entranceReturnState z 0) (entranceReturnState z 2)) y).comp
    (entranceRadialInverseDifferential y)

theorem contDiffAt_entrancePhysicalReturn {y : ProjectiveState}
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) :
    ContDiffAt ℝ 2 (fun z => coreRadius (entranceReturnState z 0) (entranceReturnState z 2)) y := by
  have hE := (entranceReturn_regular hk hm hu hv hw).2.2.1
  have hV : 0 < entranceReturnState y 2 := by
    rw [(entranceReturn_active_component hk hm hu hv hw).1]
    norm_num
  have hR : ContDiffAt ℝ 2 (fun p : ProjectiveState => coreRadius (p 0) (p 2))
      (entranceReturnState y) := by
    change ContDiffAt ℝ 2 (fun p : ProjectiveState => Real.sqrt ((p 0 - 1) ^ 2 + (p 2) ^ 2)) _
    apply ContDiffAt.sqrt (by fun_prop)
    positivity
  exact hR.comp y hE

theorem continuousAt_entrancePhysicalResponse {y : ProjectiveState}
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) (d : ProjectiveState) :
    ContinuousAt (fun z => entrancePhysicalResponse z d) y := by
  have hy : entranceRegion (coreRadius (y 0) (y 2)) y :=
    ⟨hm, by simp; positivity, hu, ⟨hv.1.le, hv.2.le⟩, hw⟩
  exact ((contDiffAt_entrancePhysicalReturn hk hm hu hv hw).continuousAt_fderiv (by norm_num)).clm_apply
    (continuousAt_entranceRadialInverseDifferential_apply hk hy hv.1 d)

theorem EntranceRadialInverseAt.physical_differential {y : ProjectiveState}
    {Ψ : ProjectiveState → ProjectiveState} (HΨ : EntranceRadialInverseAt y Ψ)
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) (d : ProjectiveState) :
    fderiv ℝ (fun z => coreRadius (entranceReturnState (Ψ z) 0) (entranceReturnState (Ψ z) 2))
      (entranceRadialCoordinates y) d = entrancePhysicalResponse y d :=
  HΨ.scalar_differential ((contDiffAt_entrancePhysicalReturn hk hm hu hv hw).differentiableAt
    (by norm_num)) d

end BianchiIX
