import BianchiIX.Dynamics.ShearRestartEntranceConnection
import BianchiIX.Dynamics.EntranceReflectionValues
import BianchiIX.Dynamics.ConnectionRestartBounds

noncomputable section

namespace BianchiIX

open Set

/-- Below V = 1, the complete reflected return retains the initial two-wall product budget. -/
theorem exists_restartShearEntrance_output_bounds :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
        ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
          (0 < n₂ ∧ n₂ ≤ 2 * ε * a) → (0 < n₃ ∧ n₃ ≤ 2 * ε * a) →
          n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
            let s := q / 2 * Real.log (1 / a)
            let y := restartFastShearProjectiveEntry h s 1 n₂ n₃ ρ
            let x := restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)
            let p := restartShearReturnParameters h s n₂ n₃ ρ
            let G := restartShearReturnState h s n₂ n₃ ρ
            y 2 < 1 → connectionReturnValid p ∧ s < restartShearReturnTime h s n₂ n₃ ρ ∧
              1 / (64 * a) ≤ G 0 ∧ G 0 ≤ 64 / a ∧
              0 < G 1 ∧ 0 < G 2 ∧ G 1 + G 2 ≤ 512 * n₂ * n₃ / a ^ 4 ∧
              coreRadiusEntry G = projectiveReflection (toProjectiveState
                (normalizedMaxCurve x 0 (restartShearReturnTime h s n₂ n₃ ρ))) := by
  obtain ⟨hI, hhI, HI⟩ := exists_restartShearEntrance_inputs
  obtain ⟨hC, hhC, HC⟩ := exists_restartShearEntrance_connection
  obtain ⟨hV, hhV, HV⟩ := exists_restartFastShearProjectiveEntry_bounds
  refine ⟨min hI (min hC hV), lt_min hhI (lt_min hhC hhV), ?_⟩
  intro h hh q P hq hP
  have hh' := hh.2.trans (min_le_right _ _)
  obtain ⟨aI, haI, HaI⟩ := HI h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q P hq hP
    (1 / 10000) ⟨by norm_num, le_rfl⟩
  obtain ⟨aC, haC, HaC⟩ := HC h ⟨hh.1, hh'.trans (min_le_left _ _)⟩ q P hq hP
    (1 / 10000) ⟨by norm_num, le_rfl⟩
  obtain ⟨aV, haV, HaV⟩ := HV h ⟨hh.1, hh'.trans (min_le_right _ _)⟩ q (by linarith only [hq])
  refine ⟨min aI (min aC aV), lt_min haI (lt_min haC haV), ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s y x p G hv
  have ha' := ha.2.trans (min_le_right _ _)
  obtain ⟨_, _, _, _, hk, hklo, hkhi, hm, hu, hv', hw, hsmall⟩ :=
    HaI a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ ⟨h₃.1.le, h₃.2⟩ h₃P ρ hρ hv
  obtain ⟨hT, _, _, hμ, hU, hW, _, hweak, _, hvalid, horbit, _⟩ :=
    HaC a ⟨ha.1, ha'.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ hv
  obtain ⟨_, _, _, _, _, _, _, _, _, hWfast, _, hprod⟩ :=
    HaV a ⟨ha.1, ha'.trans (min_le_right _ _)⟩ ε 1 n₂ n₃ hε (by norm_num)
      ⟨h₂.1.le, h₂.2⟩ ⟨h₃.1.le, h₃.2⟩ ρ hρ
  have hwpos : 0 < y 3 := (div_pos h₃.1 (by positivity [ha.1])).trans_le hWfast.1
  let z := entranceReturnState y
  let κ := coreRadius (z 0) (z 2)
  let k := restartFastShearCoreRadius h s 1 n₂ n₃ ρ
  obtain ⟨_, hκrange, _, _, _, _, hWe, _, _⟩ :=
    entranceReturn_partialCore_entry hk hm.le ⟨hu.1.le, hu.2⟩ hv' hw
      ⟨by norm_num, le_rfl⟩ hsmall
  change 99 / 100 * k ≤ κ ∧ κ ≤ 101 / 100 * k at hκrange
  change 1 / (16 * a) ≤ k at hklo
  change k ≤ 32 / a at hkhi
  have Hvalues := entrancePartialCore_reflection_values hk hm.le hu hv' ⟨hwpos, hw.2⟩
    ⟨by norm_num, le_rfl⟩ hsmall
  change κ / 2 ≤ p 0 ∧ (1 ≤ κ - G 0 ∧ κ - G 0 ≤ 3) ∧ κ / 2 ≤ G 0 ∧ G 0 ≤ κ ∧ _ at Hvalues
  obtain ⟨_, _, Hstrong, Hweak, Hsum, Hentry⟩ := connectionReturn_restart_bounds hμ.1 hU hW
  have hκlo : 1 / (32 * a) ≤ κ := by
    have Heq : 1 / (16 * a) = 2 * (1 / (32 * a)) := by ring
    rw [Heq] at hklo
    have H : 0 ≤ 1 / (32 * a) := by positivity [ha.1]
    linarith only [hklo, hκrange.1, H]
  have hκhi : κ ≤ 64 / a := calc
    _ ≤ 101 / 100 * k := hκrange.2
    _ ≤ 101 / 100 * (32 / a) := mul_le_mul_of_nonneg_left hkhi (by norm_num)
    _ = (808 / 25) / a := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (by norm_num) ha.1.le
  refine ⟨hvalid, ?_, ?_, Hvalues.2.2.2.1.trans hκhi, Hstrong.1, Hweak.1, ?_, ?_⟩
  · have htc : 0 < connectionReturnTime p := hvalid.1.1.1
    change s < s + partialCoreDownwardReturnTime y + connectionReturnTime p
    linarith only [hT, htc]
  · calc
      _ = (1 / (32 * a)) / 2 := by ring
      _ ≤ κ / 2 := div_le_div_of_nonneg_right hκlo (by norm_num)
      _ ≤ _ := Hvalues.2.2.1
  · exact Hsum.trans ((mul_le_mul_of_nonneg_left
      (hweak.trans (hWe.2.trans hprod.2)) (by norm_num)).trans_eq (by ring))
  · rw [horbit] at Hentry
    exact Hentry

end BianchiIX
