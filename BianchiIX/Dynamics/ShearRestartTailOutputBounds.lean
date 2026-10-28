import BianchiIX.Dynamics.ShearRestartTailConnection
import BianchiIX.Dynamics.ShearRestartTailEntrancePhase
import BianchiIX.Dynamics.ShearRestartTailProduct
import BianchiIX.Dynamics.EntranceReflectionValues
import BianchiIX.Dynamics.ConnectionRestartBounds

noncomputable section

namespace BianchiIX

open Set

/-- The complete long-tail return retains the original weak-wall product and reaches the reflected ascending section. -/
theorem exists_restartShearTail_output_bounds :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε ζ ν : ℝ,
          (0 ≤ ε ∧ ε ≤ 1 / 128) →
          (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
          (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
          let s := shearTailTime a D + q / 2 * Real.log (1 / a)
          let x := restartSectionChart h (restartShearCurve 1 ζ ν ρ)
          let p := restartShearReturnParameters h s ζ ν ρ
          let G := restartShearReturnState h s ζ ν ρ
          connectionReturnValid p ∧ s < restartShearReturnTime h s ζ ν ρ ∧
          1 / (96 * a) ≤ G 0 ∧ G 0 ≤ 128 / a ∧
          0 < G 1 ∧ 0 < G 2 ∧ G 1 + G 2 ≤ 512 * ζ * ν / a ^ 4 ∧
          coreRadiusEntry G = projectiveReflection (toProjectiveState
            (normalizedMaxCurve x 0 (restartShearReturnTime h s ζ ν ρ))) := by
  obtain ⟨hI, hhI, HI⟩ := exists_restartShearTail_core_inputs
  obtain ⟨hC, hhC, HC⟩ := exists_restartShearTail_connection
  obtain ⟨hP, hhP, HP⟩ := exists_restartShearTail_product
  obtain ⟨hR, hhR, HR⟩ := exists_restartShearTail_entrance_phase
  refine ⟨min hI (min hC (min hP hR)), lt_min hhI (lt_min hhC (lt_min hhP hhR)), ?_⟩
  intro h hh q D P hq hD hPexp
  have hh' := hh.2.trans (min_le_right _ _)
  have hh'' := hh'.trans (min_le_right _ _)
  have hq' : 2 < q := by linarith only [hq]
  have hD' : 2 < D := by linarith only [hD]
  obtain ⟨aI, haI, HAI⟩ := HI h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq hD hPexp
    (1 / 10000) ⟨by norm_num, le_rfl⟩
  obtain ⟨aC, haC, HAC⟩ := HC h ⟨hh.1, hh'.trans (min_le_left _ _)⟩ q D P hq hD hPexp
    (1 / 10000) ⟨by norm_num, le_rfl⟩
  obtain ⟨aP, haP, HAP⟩ := HP h ⟨hh.1, hh''.trans (min_le_left _ _)⟩ q D P hq' hD' hPexp
  obtain ⟨_, _, HBR⟩ := HR h ⟨hh.1, hh''.trans (min_le_right _ _)⟩ q D hq' hD'
  obtain ⟨aR, haR, HAR⟩ := HBR P hPexp
  refine ⟨min aI (min aC (min aP aR)), lt_min haI (lt_min haC (lt_min haP haR)), ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ s x p G
  have ha' := ha.2.trans (min_le_right _ _)
  have ha'' := ha'.trans (min_le_right _ _)
  obtain ⟨_, _, hk, _, _, hm, hu, hv, hw, hsmall, _⟩ :=
    HAI a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  obtain ⟨hT, _, hμ, hU, hW, _, hweak, _, hvalid, horbit, _⟩ :=
    HAC a ⟨ha.1, ha'.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  obtain ⟨_, _, Hprod⟩ := HAP a ⟨ha.1, ha''.trans (min_le_left _ _)⟩ ε ζ ν hε
    ⟨hζ.1.le, hζ.2⟩ ⟨hν.1.le, hν.2⟩ ρ hρ
  obtain ⟨_, _, _, _, _, _, _, Hκlo, Hκhi, _⟩ :=
    HAR a ⟨ha.1, ha''.trans (min_le_right _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  let y := restartShearTailProjectiveEntry h a q ζ ν (shearTailTime a D) ρ
  let z := entranceReturnState y
  let κ := coreRadius (z 0) (z 2)
  obtain ⟨_, _, _, _, _, _, hWe, _, _⟩ :=
    entranceReturn_partialCore_entry hk hm.le ⟨hu.1.le, hu.2⟩ hv ⟨hw.1.le, hw.2⟩
      ⟨by norm_num, le_rfl⟩ hsmall
  have Hvalues := entrancePartialCore_reflection_values hk hm.le hu hv hw ⟨by norm_num, le_rfl⟩ hsmall
  change κ / 2 ≤ p 0 ∧ (1 ≤ κ - G 0 ∧ κ - G 0 ≤ 3) ∧ κ / 2 ≤ G 0 ∧ G 0 ≤ κ ∧ _ at Hvalues
  change 1 / (48 * a) ≤ κ at Hκlo
  change κ ≤ 128 / a at Hκhi
  obtain ⟨_, _, Hstrong, Hweak, Hsum, Hentry⟩ := connectionReturn_restart_bounds hμ.1 hU hW
  refine ⟨hvalid, ?_, ?_, Hvalues.2.2.2.1.trans Hκhi, Hstrong.1, Hweak.1, ?_, ?_⟩
  · have htc : 0 < connectionReturnTime p := hvalid.1.1.1
    change s < s + partialCoreDownwardReturnTime y + connectionReturnTime p
    linarith only [hT, htc]
  · calc
      _ = (1 / (48 * a)) / 2 := by ring
      _ ≤ κ / 2 := div_le_div_of_nonneg_right Hκlo (by norm_num)
      _ ≤ _ := Hvalues.2.2.1
  · exact Hsum.trans ((mul_le_mul_of_nonneg_left
      (hweak.trans (hWe.2.trans Hprod)) (by norm_num)).trans_eq (by ring))
  · rw [horbit] at Hentry
    exact Hentry

end BianchiIX
