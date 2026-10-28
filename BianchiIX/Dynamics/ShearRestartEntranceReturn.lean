import BianchiIX.Dynamics.ShearRestartEntranceInputs
import BianchiIX.Dynamics.EntranceDownwardReturn
import BianchiIX.Dynamics.ShearRestartPartialCoreResponse

noncomputable section

namespace BianchiIX

open Set

/-- Restarting at the exact shear cutoff also preserves the normalized state and hence event rates. -/
theorem restartFastShearProjectiveEntry_normalized_flow {h s σ n₂ n₃ ρ t : ℝ}
    (hrad : 0 ≤ restartSectionRadicand h (restartShearCurve σ n₂ n₃ ρ))
    (hs : 0 ≤ s) (hA : 0 < restartFastShearHeight h s σ n₂ n₃ ρ) (ht : 0 ≤ t) :
    normalizedMaxCurve (fromProjectiveState (restartFastShearProjectiveEntry h s σ n₂ n₃ ρ)) 0 t =
      normalizedMaxCurve (restartSectionChart h (restartShearCurve σ n₂ n₃ ρ)) 0 (s + t) := by
  have hc := restartSectionChart_constraint hrad
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint hc 0 hs
  have hbase := fromProjectiveState_toProjectiveState hA.ne'
    ((normalizedMaxCurve_constraint hdom).trans hc)
  have H := normalizedMaxCurve_shift (by simpa only [zero_add] using hdom)
    (normalizedMaxDomain_contains_Ici_of_constraint hc 0 (add_nonneg ht hs))
  simp only [zero_add] at H
  change normalizedMaxCurve (fromProjectiveState (toProjectiveState
    (normalizedMaxCurve (restartSectionChart h (restartShearCurve σ n₂ n₃ ρ)) 0 s))) 0 t = _
  rw [hbase, H, add_comm t s]

/-- Oriented first-event minimality transfers from the cutoff state to the original normalized orbit. -/
theorem restartFastShearProjectiveEntry_downward_event {h s σ n₂ n₃ ρ T : ℝ}
    (hrad : 0 ≤ restartSectionRadicand h (restartShearCurve σ n₂ n₃ ρ))
    (hs : 0 ≤ s) (hA : 0 < restartFastShearHeight h s σ n₂ n₃ ρ)
    (hD : 0 < projectiveStateDenom (restartFastShearProjectiveEntry h s σ n₂ n₃ ρ))
    (HT : IsLeast {t | 0 < t ∧
      t ∈ normalizedMaxDomain (fromProjectiveState (restartFastShearProjectiveEntry h s σ n₂ n₃ ρ)) 0 ∧
      projectiveOriginalFlow (restartFastShearProjectiveEntry h s σ n₂ n₃ ρ) 0 t 2 = 1 ∧
      normalizedEventRate projectiveActiveWall (fromProjectiveState (restartFastShearProjectiveEntry h s σ n₂ n₃ ρ)) 0 t < 0} T) :
    let x := restartSectionChart h (restartShearCurve σ n₂ n₃ ρ)
    IsLeast {t | s < t ∧ toProjectiveState (normalizedMaxCurve x 0 t) 2 = 1 ∧
      normalizedEventRate projectiveActiveWall x 0 t < 0} (s + T) := by
  intro x
  have hT : 0 < T := HT.1.1
  have hc := fromProjectiveState_constraint hD.ne'
  have Hflow (t : ℝ) (ht : 0 ≤ t) := restartFastShearProjectiveEntry_flow hrad hs hA ht
  have Hrate (t : ℝ) (ht : 0 ≤ t) : normalizedEventRate projectiveActiveWall
      (fromProjectiveState (restartFastShearProjectiveEntry h s σ n₂ n₃ ρ)) 0 t =
      normalizedEventRate projectiveActiveWall x 0 (s + t) := by
    unfold normalizedEventRate
    rw [restartFastShearProjectiveEntry_normalized_flow hrad hs hA ht]
  refine ⟨⟨by linarith only [hT], ?_, ?_⟩, ?_⟩
  · rw [← Hflow T hT.le]
    exact HT.1.2.2.1
  · rw [← Hrate T hT.le]
    exact HT.1.2.2.2
  · intro t ht
    have hsub : 0 < t - s := sub_pos.mpr ht.1
    have HF := Hflow (t - s) hsub.le
    have HR := Hrate (t - s) hsub.le
    rw [add_sub_cancel] at HF HR
    have H := HT.2 ⟨hsub, normalizedMaxDomain_contains_Ici_of_constraint hc 0 hsub.le,
      by rw [HF]; exact ht.2.1, by rw [HR]; exact ht.2.2⟩
    linarith only [H]

/-- Actual V < 1 shear entries reach the ascending core and then the same regular first downward event. -/
theorem exists_restartShearEntrance_downward_return :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∀ η ∈ Ioc (0 : ℝ) (1 / 10000),
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
          ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
            (0 < n₂ ∧ n₂ ≤ 2 * ε * a) → (0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) →
            n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
              let s := q / 2 * Real.log (1 / a)
              let y := restartFastShearProjectiveEntry h s 1 n₂ n₃ ρ
              let x := restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)
              let z := entranceReturnState y
              let κ := coreRadius (z 0) (z 2)
              let T := partialCoreDownwardReturnTime y
              y 2 < 1 →
              entranceReturnValid y ∧ ContDiffAt ℝ 2 entranceReturnTime y ∧ ContDiffAt ℝ 2 entranceReturnState y ∧
              (6 ≤ κ ∧ 1 / (32 * a) ≤ κ ∧ κ ≤ 64 / a) ∧
              z 2 = 1 ∧ 1 < z 0 ∧ coreRegion κ z ∧
              (0 ≤ z 1 ∧ z 1 ≤ y 1) ∧ (0 ≤ z 3 ∧ z 3 ≤ y 2 * y 3) ∧
              z 1 + z 2 * z 3 ≤ η / κ ∧ projectiveCoreAngle z = -Real.arcosh κ ∧
              0 < T ∧ T = entranceReturnTime y + partialCoreDownwardReturnTime z ∧
              partialCoreDownwardReturnState y = partialCoreDownwardReturnState z ∧
              ContDiffAt ℝ 2 partialCoreDownwardReturnTime y ∧ ContDiffAt ℝ 2 partialCoreDownwardReturnState y ∧
              IsLeast {t | s < t ∧ toProjectiveState (normalizedMaxCurve x 0 t) 2 = 1 ∧
                normalizedEventRate projectiveActiveWall x 0 t < 0} (s + T) ∧
              projectiveOriginalFlow y 0 T = toProjectiveState (normalizedMaxCurve x 0 (s + T)) := by
  obtain ⟨hstar, hhstar, HH⟩ := exists_restartShearEntrance_inputs
  refine ⟨hstar, hhstar, ?_⟩
  intro h hh q P hq hP η hη
  obtain ⟨astar, hastar, Ha⟩ := HH h hh q P hq hP η hη
  refine ⟨astar, hastar, ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s y x z κ T hv
  obtain ⟨hs, hrad, _, hA, hk, hklo, hkhi, hm, hu, hv', hw, hsmall⟩ :=
    Ha a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ hv
  change 8 ≤ coreRadius (y 0) (y 2) at hk
  change 1 / (16 * a) ≤ coreRadius (y 0) (y 2) at hklo
  have hk' : 7 / 4 ≤ coreRadius (y 0) (y 2) := by linarith only [hk]
  have HE := entranceReturn_regular hk' hm.le ⟨hu.1.le, hu.2⟩ hv' hw
  obtain ⟨hκ, hκrange, hhit, hmz, hregion, hU, hW, hsum, hangle⟩ :=
    entranceReturn_partialCore_entry hk hm.le ⟨hu.1.le, hu.2⟩ hv' hw hη hsmall
  change 99 / 100 * coreRadius (y 0) (y 2) ≤ κ ∧ κ ≤ 101 / 100 * coreRadius (y 0) (y 2) at hκrange
  obtain ⟨hdown, htime, hstate, hct, hcs, _⟩ :=
    entrancePartialCore_downward_regular hk hm.le ⟨hu.1.le, hu.2⟩ hv' hw hη hsmall
  have hT : 0 < T := hdown.1.1
  have hD := entrance_initial_denom_pos hk' hm.le ⟨hu.1.le, hu.2⟩ hv' hw
  have hκlo : 1 / (32 * a) ≤ κ := by
    have Heq : 1 / (16 * a) = 2 * (1 / (32 * a)) := by ring
    rw [Heq] at hklo
    have H : 0 ≤ 1 / (32 * a) := by positivity [ha.1]
    linarith only [hklo, hκrange.1, H]
  have hκhi : κ ≤ 64 / a := calc
    _ ≤ 101 / 100 * restartFastShearCoreRadius h s 1 n₂ n₃ ρ := hκrange.2
    _ ≤ 101 / 100 * (32 / a) := mul_le_mul_of_nonneg_left hkhi (by norm_num)
    _ = (808 / 25) / a := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (by norm_num) ha.1.le
  exact ⟨HE.1, HE.2.1, HE.2.2.1, ⟨hκ, hκlo, hκhi⟩, hhit, hmz, hregion, hU, hW, hsum, hangle,
    hT, htime, hstate, hct, hcs, restartFastShearProjectiveEntry_downward_event hrad.le hs hA hD hdown,
    restartFastShearProjectiveEntry_flow hrad.le hs hA hT.le⟩

end BianchiIX
