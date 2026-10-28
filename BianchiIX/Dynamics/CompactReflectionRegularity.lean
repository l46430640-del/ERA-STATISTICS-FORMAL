import BianchiIX.Dynamics.ReflectionReturn
import BianchiIX.Dynamics.CoreTailHeightRegularity

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem contDiffAt_compactConnectionPhysicalState {η : ℝ} {Y : CoreAngleState}
    (hs : ContDiffAt ℝ 2 (compactConnectionState η) Y)
    (ha : 0 < compactConnectionState η Y 2) :
    ContDiffAt ℝ 2 (compactConnectionPhysicalState η) Y := by
  have hp := (contDiffAt_toCoreAngleState 2 ha).comp Y hs
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact contDiffAt_pi.mp hp 0
  · exact contDiffAt_pi.mp hs 1
  · exact contDiffAt_pi.mp hs 3

/-- The compact construction identifies the canonical reflection in a full neighborhood, including at phase endpoints. -/
theorem exists_compact_reflection_regular {η : ℝ} (hη : 0 < η ∧ η ≤ 1 / 10000) :
    ∃ ε > (0 : ℝ), ∀ Y : CoreAngleState,
      (31 / 8 ≤ Y 0 ∧ Y 0 ≤ 6) → (0 < Y 1 ∧ Y 1 ≤ ε) → (0 < Y 2 ∧ Y 2 ≤ ε) →
      (reflectionReturnTime =ᶠ[𝓝 Y] compactConnectionTime η) ∧
        (reflectionReturnState =ᶠ[𝓝 Y] compactConnectionPhysicalState η) ∧
        ContDiffAt ℝ 2 reflectionReturnTime Y ∧ ContDiffAt ℝ 2 reflectionReturnState Y := by
  obtain ⟨ε, hε, C, hC, H⟩ := exists_compact_connection_entrance_data
    (δ := 1 / 10000) (by norm_num) hη
  refine ⟨ε, hε, ?_⟩
  intro Y hk hu hw
  obtain ⟨htail, ht, he, hr, hm, hU, hV, hW, _, _⟩ := H Y hk hu hw
  have hR : 1 < Y 0 := by linarith only [hk.1]
  have hv : 0 < compactConnectionEntry η Y 2 ∧ compactConnectionEntry η Y 2 < 1 :=
    ⟨hV.1, by linarith only [hV.2]⟩
  have hw' : 0 ≤ compactConnectionEntry η Y 3 ∧ compactConnectionEntry η Y 3 ≤ 1 / 10000 := by
    rw [hW]
    exact ⟨hη.1.le, hη.2⟩
  have HR := entranceReturn_regular hr.1 hm ⟨hU.1.le, hU.2⟩ hv hw'
  have hD := entrance_initial_denom_pos hr.1 hm ⟨hU.1.le, hU.2⟩ hv hw'
  have htailNear : ∀ᶠ Z in 𝓝 Y, coreTailValid η Z :=
    (continuousAt_const.prodMk continuousAt_id).eventually
      (coreTail_joint_regular_of_valid hR htail).2.2
  have hreturnNear : ∀ᶠ Z in 𝓝 Y, entranceReturnValid (compactConnectionEntry η Z) :=
    he.continuousAt.eventually HR.2.2.2.2.2
  have hdenNear : ∀ᶠ Z in 𝓝 Y, 0 < projectiveStateDenom (compactConnectionEntry η Z) :=
    (continuous_projectiveStateDenom.continuousAt.comp he.continuousAt).eventually
      (isOpen_Ioi.mem_nhds hD)
  have hnear : ∀ᶠ Z in 𝓝 Y, coreTailValid η Z ∧
      0 < projectiveStateDenom (compactConnectionEntry η Z) ∧
      entranceReturnValid (compactConnectionEntry η Z) := by
    filter_upwards [htailNear, hdenNear, hreturnNear] with Z htZ hdZ hrZ
    exact ⟨htZ, hdZ, hrZ⟩
  obtain ⟨heqT, heqF⟩ := reflectionReturn_compact_eventuallyEq hnear
  have htime : ContDiffAt ℝ 2 (compactConnectionTime η) Y := (HR.2.1.comp Y he).add ht
  have hstate : ContDiffAt ℝ 2 (compactConnectionState η) Y := HR.2.2.1.comp Y he
  have hactive : compactConnectionState η Y 2 = 1 := HR.1.1.1.2.2
  have hphysical := contDiffAt_compactConnectionPhysicalState hstate (by rw [hactive]; norm_num)
  exact ⟨heqT, heqF, htime.congr_of_eventuallyEq heqT, hphysical.congr_of_eventuallyEq heqF⟩

end BianchiIX
