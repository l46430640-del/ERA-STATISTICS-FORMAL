import BianchiIX.Dynamics.EntranceDownwardReturn

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- First downward-event selection near an ascending entrance persists in all ordinary coordinates. -/
theorem eventually_entrancePartialCore_downward_first {y : ProjectiveState} {η : ℝ}
    (hk : 8 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) (hη : 0 < η ∧ η ≤ 1 / 10000)
    (hsmall : y 1 + y 2 * y 3 ≤ η / (2 * coreRadius (y 0) (y 2))) :
    ∀ᶠ z in 𝓝 y,
      IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState z) 0 ∧
        projectiveOriginalFlow z 0 t 2 = 1 ∧
        normalizedEventRate projectiveActiveWall (fromProjectiveState z) 0 t < 0}
        (partialCoreDownwardReturnTime z) := by
  have hk' : 7 / 4 ≤ coreRadius (y 0) (y 2) := by linarith only [hk]
  have HE := entranceReturn_regular hk' hm hu hv hw
  obtain ⟨hκ, _, hhit, hmz, hregion, _⟩ := entranceReturn_partialCore_entry hk hm hu hv hw hη hsmall
  have HC := partialCoreDownwardReturn_regular hκ hregion rfl (Or.inr ⟨hhit, hmz.le⟩)
  have hD := entrance_initial_denom_pos hk' hm hu hv hw
  filter_upwards [continuous_projectiveStateDenom.continuousAt.eventually (lt_mem_nhds hD),
    HE.2.2.2.2.2, HE.2.2.1.continuousAt.tendsto.eventually HC.2.2.2.1] with z hd he hc
  have H := entranceReturn_downward_restart hd he hc.1
  rw [H.2.1]
  exact H.1

end BianchiIX
