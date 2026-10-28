import BianchiIX.Dynamics.EntranceDownwardConnection
import BianchiIX.Dynamics.ShearRestartEntranceReturn
import BianchiIX.Dynamics.ShearRestartReturnRegularity

noncomputable section

namespace BianchiIX

open Set

/-- Below V = 1 the exact shear family reaches the long connection, with joint ordinary C2 return data. -/
theorem exists_restartShearEntrance_connection :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∀ η ∈ Ioc (0 : ℝ) (1 / 10000),
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
          ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
            (0 < n₂ ∧ n₂ ≤ 2 * ε * a) → (0 < n₃ ∧ n₃ ≤ 2 * ε * a) →
            n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
              let s := q / 2 * Real.log (1 / a)
              let x := restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)
              let y := restartFastShearProjectiveEntry h s 1 n₂ n₃ ρ
              let z := entranceReturnState y
              let κ := coreRadius (z 0) (z 2)
              let T := partialCoreDownwardReturnTime y
              let p := restartShearReturnParameters h s n₂ n₃ ρ
              y 2 < 1 → 0 < T ∧
              IsLeast {t | s < t ∧ toProjectiveState (normalizedMaxCurve x 0 t) 2 = 1 ∧
                normalizedEventRate projectiveActiveWall x 0 t < 0} (s + T) ∧
              projectiveOriginalFlow y 0 T = connectionEntry (p 0) (p 1) (p 2) ∧
              (4 ≤ p 0 ∧ κ / 2 ≤ p 0 ∧ p 0 < κ) ∧
              (0 < p 1 ∧ p 1 ≤ η / p 0) ∧ (0 < p 2 ∧ p 2 ≤ η) ∧
              p 1 ≤ z 1 * Real.exp (-κ / 12) ∧ p 2 ≤ z 3 ∧
              1 < partialCoreDownwardReturnState y 0 ∧ connectionReturnValid p ∧
              connectionReturnState p = toProjectiveState (normalizedMaxCurve x 0
                (restartShearReturnTime h s n₂ n₃ ρ)) ∧
              ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartShearReturnParameters h s v.1.1 v.1.2 v.2) ((n₂, n₃), ρ) ∧
              ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartShearReturnState h s v.1.1 v.1.2 v.2) ((n₂, n₃), ρ) ∧
              ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartShearReturnPhase h s v.1.1 v.1.2 v.2) ((n₂, n₃), ρ) ∧
              ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartShearReturnTime h s v.1.1 v.1.2 v.2) ((n₂, n₃), ρ) := by
  obtain ⟨hstar, hhstar, HI⟩ := exists_restartShearEntrance_inputs
  refine ⟨hstar, hhstar, ?_⟩
  intro h hh q P hq hP η hη
  obtain ⟨astar, hastar, Ha⟩ := HI h hh q P hq hP η hη
  refine ⟨astar, hastar, ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s x y z κ T p hv
  obtain ⟨hs, hrad, hdom, hA, hk, _, _, hm, hu, hv', hw, hsmall⟩ :=
    Ha a ha ε n₂ n₃ hε h₂ ⟨h₃.1.le, h₃.2⟩ h₃P ρ hρ hv
  have hc : stateConstraint x = 1 := restartSectionChart_constraint hrad.le
  have Hsign := normalizedMaxCurve_wall_sign hc hs (2 : Fin 3)
  have hnpos : 0 < normalizedMaxCurve x 0 s 4 := by
    have Hnonneg : 0 ≤ wallValue 2 (normalizedMaxCurve x 0 s) := Hsign.2.mpr h₃.1.le
    have Hne : wallValue 2 (normalizedMaxCurve x 0 s) ≠ 0 := fun hzero => h₃.1.ne' (Hsign.1.mp hzero)
    exact lt_of_le_of_ne Hnonneg (Ne.symm Hne)
  have hwpos : 0 < y 3 := div_pos (mul_pos (Real.sqrt_pos.mpr (by norm_num)) hnpos) hA
  have hk' : 7 / 4 ≤ coreRadius (y 0) (y 2) := (by norm_num : (7 : ℝ) / 4 ≤ 8).trans hk
  obtain ⟨hT, hentry, hμ, hU, hW, hdecU, hdecW, _, hK, hvalid, hcT, _, horbit, hcQ, _, _⟩ :=
    entrancePartialCore_connection_domain hk hm.le hu hv' ⟨hwpos, hw.2⟩ hη hsmall
  have HD := entrancePartialCore_downward_regular hk hm.le ⟨hu.1.le, hu.2⟩ hv' hw hη hsmall
  have hD := entrance_initial_denom_pos hk' hm.le ⟨hu.1.le, hu.2⟩ hv' hw
  have hfirst := restartFastShearProjectiveEntry_downward_event hrad.le hs hA hD HD.1
  let base : (ℝ × ℝ) × ℝ := ((n₂, n₃), ρ)
  let Y := fun v : (ℝ × ℝ) × ℝ => restartFastShearProjectiveEntry h s 1 v.1.1 v.1.2 v.2
  have hcY : ContDiffAt ℝ 2 Y base := contDiffAt_restartFastShearProjectiveEntry_joint hrad hdom hA.ne'
  have hcP : ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartShearReturnParameters h s v.1.1 v.1.2 v.2) base :=
    ContDiffAt.comp (g := fun w => coreExitConnectionParameters (partialCoreDownwardReturnState w)) base hcQ hcY
  have hμ0 : 0 ≤ p 0 := by change 4 ≤ p 0 ∧ _ at hμ; linarith only [hμ.1]
  have hcG : ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartShearReturnState h s v.1.1 v.1.2 v.2) base :=
    ContDiffAt.comp (g := connectionReturnPhysicalState) base
      (contDiffAt_connectionReturnPhysicalState hμ.1
        ⟨hU.1.le, hU.2.trans (div_le_div_of_nonneg_right hη.2 hμ0)⟩ ⟨hW.1, hW.2.trans hη.2⟩) hcP
  have hg0 : restartShearReturnState h s n₂ n₃ ρ 0 ≠ 0 := by
    change phaseNorm (-connectionReturnState p 0 - 1) 1 ≠ 0
    exact ne_of_gt (by unfold phaseNorm; positivity)
  have hcphase : ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartShearReturnPhase h s v.1.1 v.1.2 v.2) base :=
    contDiffAt_const.div (contDiffAt_pi.mp hcG 0) hg0
  have hctime : ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartShearReturnTime h s v.1.1 v.1.2 v.2) base :=
    (contDiffAt_const.add (HD.2.2.2.1.comp base hcY)).add
      (ContDiffAt.comp (g := connectionReturnTime) base hcT hcP)
  refine ⟨hT, hfirst, hentry, hμ, hU, hW, hdecU, hdecW, hK, hvalid, ?_, hcP, hcG, hcphase, hctime⟩
  have htc : 0 < connectionReturnTime p := hvalid.1.1.1
  have Hfast := restartFastShearProjectiveEntry_flow hrad.le hs hA (add_nonneg hT.le htc.le)
  exact (horbit.trans Hfast).trans (by change _ = toProjectiveState (normalizedMaxCurve x 0 (s + T + _)); rw [add_assoc])

end BianchiIX
