import BianchiIX.Dynamics.EntranceDownwardReturn
import BianchiIX.Dynamics.CoreDownwardIdentification

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The downward event below the core is the upward entrance followed by the fixed full-core return. -/
theorem entrancePartialCore_fullCore_eventuallyEq {y : ProjectiveState} {η : ℝ}
    (hk : 8 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) (hη : 0 < η ∧ η ≤ 1 / 10000)
    (hsmall : y 1 + y 2 * y 3 ≤ η / (2 * coreRadius (y 0) (y 2))) :
    (partialCoreDownwardReturnTime =ᶠ[𝓝 y] fun w => entranceReturnTime w +
      coreRadiusReturnTime (toCoreAngleState (entranceReturnState w))) ∧
      (partialCoreDownwardReturnState =ᶠ[𝓝 y] fun w =>
        coreReturnState coreRadiusReturnTime (toCoreAngleState (entranceReturnState w))) := by
  let z := entranceReturnState y
  let X := toCoreAngleState z
  have hk' : 7 / 4 ≤ coreRadius (y 0) (y 2) := by linarith only [hk]
  have HE := entranceReturn_regular hk' hm hu hv hw
  obtain ⟨hκ, _, hhit, hmz, _, hU, hW, hsum, _⟩ :=
    entranceReturn_partialCore_entry hk hm hu hv hw hη hsmall
  change 6 ≤ X 0 at hκ
  change z 2 = 1 at hhit
  change 1 < z 0 at hmz
  have hXU : 0 ≤ X 1 := hU.1
  have hXW : 0 ≤ X 2 := by change 0 ≤ z 2 * z 3; rw [hhit, one_mul]; exact hW.1
  have hκ0 : 0 ≤ X 0 := by linarith only [hκ]
  change X 1 + X 2 ≤ η / X 0 at hsum
  have hsum' : X 1 + X 2 ≤ (1 / 10000) / X 0 := hsum.trans
    (div_le_div_of_nonneg_right hη.2 hκ0)
  have HG := coreRadiusReturn_downward_eventuallyEq hκ
    ⟨hXU, (le_add_of_nonneg_right hXW).trans hsum'⟩
    ⟨hXW, (le_add_of_nonneg_left hXU).trans hsum'⟩
  have hcoord : ContinuousAt (fun w => toCoreAngleState (entranceReturnState w)) y :=
    (contDiffAt_toCoreAngleState 2 (by change 0 < z 2; rw [hhit]; norm_num)).continuousAt.comp HE.2.2.1.continuousAt
  have hrecover : ∀ᶠ w in 𝓝 y,
      coreRadiusEntry (toCoreAngleState (entranceReturnState w)) = entranceReturnState w := by
    have hM : ContinuousAt (fun w => entranceReturnState w 0) y :=
      (continuous_apply 0).continuousAt.comp HE.2.2.1.continuousAt
    filter_upwards [HE.2.2.2.2.2, hM.eventually (lt_mem_nhds hmz)] with w he hm'
    apply coreRadiusEntry_of_upward_section hm'.le
    exact he.1.1.2.2
  have HD := entrancePartialCore_downward_regular hk hm hu hv hw hη hsmall
  constructor
  · filter_upwards [HD.2.2.2.2.2.1, hcoord.eventually HG.1, hrecover] with w hd hg hr
    rw [hr] at hg
    exact hd.trans (congrArg (entranceReturnTime w + ·) hg.symm)
  · filter_upwards [HD.2.2.2.2.2.2, hcoord.eventually HG.2, hrecover] with w hd hg hr
    rw [hr] at hg
    exact hd.trans hg.symm

/-- On the upward entrance, the active component is identically one on an ordinary germ. -/
theorem entranceReturn_coreCoordinates_eventuallyEq {y : ProjectiveState}
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) :
    (fun w => toCoreAngleState (entranceReturnState w)) =ᶠ[𝓝 y] fun w =>
      ![coreRadius (entranceReturnState w 0) (entranceReturnState w 2),
        entranceReturnState w 1, entranceReturnState w 3] := by
  filter_upwards [(entranceReturn_regular hk hm hu hv hw).2.2.2.2.2] with w hw'
  have hv' : entranceReturnState w 2 = 1 := hw'.1.1.2.2
  simp only [toCoreAngleState, hv', one_mul]

end BianchiIX
