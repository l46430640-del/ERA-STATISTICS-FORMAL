import BianchiIX.Dynamics.ShearRestartTailCoreEntry
import BianchiIX.Dynamics.ShearRestartTailDownwardReturn
import BianchiIX.Dynamics.EntranceDownwardConnection
import BianchiIX.Dynamics.ShearRestartReturnRegularity

noncomputable section

namespace BianchiIX

open Set

/-- The long-tail family reaches a finite long connection, with joint ordinary C2 return data on the original orbit. -/
theorem exists_restartShearTail_connection :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
        ∀ η ∈ Ioc (0 : ℝ) (1 / 10000), ∃ astar > (0 : ℝ),
          ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε ζ ν : ℝ,
            (0 ≤ ε ∧ ε ≤ 1 / 128) →
            (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
            (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
            let s := shearTailTime a D + q / 2 * Real.log (1 / a)
            let x := restartSectionChart h (restartShearCurve 1 ζ ν ρ)
            let y := restartShearTailProjectiveEntry h a q ζ ν (shearTailTime a D) ρ
            let z := entranceReturnState y
            let κ := coreRadius (z 0) (z 2)
            let T := partialCoreDownwardReturnTime y
            let p := restartShearReturnParameters h s ζ ν ρ
            0 < T ∧ projectiveOriginalFlow y 0 T = connectionEntry (p 0) (p 1) (p 2) ∧
            (4 ≤ p 0 ∧ κ / 2 ≤ p 0 ∧ p 0 < κ) ∧
            (0 < p 1 ∧ p 1 ≤ η / p 0) ∧ (0 < p 2 ∧ p 2 ≤ η) ∧
            p 1 ≤ z 1 * Real.exp (-κ / 12) ∧ p 2 ≤ z 3 ∧
            1 < partialCoreDownwardReturnState y 0 ∧ connectionReturnValid p ∧
            connectionReturnState p = toProjectiveState (normalizedMaxCurve x 0 (restartShearReturnTime h s ζ ν ρ)) ∧
            ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartShearReturnParameters h s v.1.1 v.1.2 v.2) ((ζ, ν), ρ) ∧
            ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartShearReturnState h s v.1.1 v.1.2 v.2) ((ζ, ν), ρ) ∧
            ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartShearReturnPhase h s v.1.1 v.1.2 v.2) ((ζ, ν), ρ) ∧
            ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartShearReturnTime h s v.1.1 v.1.2 v.2) ((ζ, ν), ρ) := by
  obtain ⟨hI, hhI, HI⟩ := exists_restartShearTail_core_inputs
  obtain ⟨hV, hhV, HV⟩ := exists_restartShearTail_control
  refine ⟨min hI hV, lt_min hhI hhV, ?_⟩
  intro h hh q D P hq hD hP η hη
  obtain ⟨aI, haI, HAI⟩ := HI h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq hD hP η hη
  obtain ⟨aV, haV, HAV⟩ := HV h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q D P
    (by linarith only [hq]) (by linarith only [hD]) hP
  refine ⟨min aI aV, lt_min haI haV, ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ s x y z κ T p
  obtain ⟨_, _, hk, _, _, hm, hu, hv, hw, hsmall, _⟩ :=
    HAI a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  obtain ⟨_, hs₀, hT₀, hrad, _, HT, _⟩ :=
    HAV a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε ζ ν hε ⟨hζ.1.le, hζ.2⟩ ⟨hν.1.le, hν.2⟩ ρ hρ
  have hs : 0 ≤ s := add_nonneg hT₀ hs₀
  have hdom : s ∈ normalizedMaxDomain x 0 := (HT _ ⟨hT₀, le_rfl⟩).1
  have hA : 0 < restartFastShearHeight h s 1 ζ ν ρ := by
    have H := (HT _ ⟨hT₀, le_rfl⟩).2.2.2.2.2.2.2.2.2.1
    change a ^ 2 / 10 ≤ restartFastShearHeight h s 1 ζ ν ρ at H
    exact (by positivity [ha.1] : 0 < a ^ 2 / 10).trans_le H
  obtain ⟨hT, hentry, hμ, hU, hW, hdecU, hdecW, _, hK, hvalid, hcT, _, horbit, hcQ, _, _⟩ :=
    entrancePartialCore_connection_domain hk hm.le hu hv hw hη hsmall
  have HD := entrancePartialCore_downward_regular hk hm.le ⟨hu.1.le, hu.2⟩ hv ⟨hw.1.le, hw.2⟩ hη hsmall
  let base : (ℝ × ℝ) × ℝ := ((ζ, ν), ρ)
  let Y := fun v : (ℝ × ℝ) × ℝ => restartFastShearProjectiveEntry h s 1 v.1.1 v.1.2 v.2
  have hcY : ContDiffAt ℝ 2 Y base := contDiffAt_restartFastShearProjectiveEntry_joint hrad hdom hA.ne'
  have hcP : ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartShearReturnParameters h s v.1.1 v.1.2 v.2) base :=
    ContDiffAt.comp (g := fun w => coreExitConnectionParameters (partialCoreDownwardReturnState w)) base hcQ hcY
  have hμ0 : 0 ≤ p 0 := by change 4 ≤ p 0 ∧ _ at hμ; linarith only [hμ.1]
  have hcG : ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartShearReturnState h s v.1.1 v.1.2 v.2) base :=
    ContDiffAt.comp (g := connectionReturnPhysicalState) base
      (contDiffAt_connectionReturnPhysicalState hμ.1
        ⟨hU.1.le, hU.2.trans (div_le_div_of_nonneg_right hη.2 hμ0)⟩ ⟨hW.1, hW.2.trans hη.2⟩) hcP
  have hg0 : restartShearReturnState h s ζ ν ρ 0 ≠ 0 := by
    change phaseNorm (-connectionReturnState p 0 - 1) 1 ≠ 0
    exact ne_of_gt (by unfold phaseNorm; positivity)
  have hcphase : ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartShearReturnPhase h s v.1.1 v.1.2 v.2) base :=
    contDiffAt_const.div (contDiffAt_pi.mp hcG 0) hg0
  have hctime : ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartShearReturnTime h s v.1.1 v.1.2 v.2) base :=
    (contDiffAt_const.add (HD.2.2.2.1.comp base hcY)).add
      (ContDiffAt.comp (g := connectionReturnTime) base hcT hcP)
  refine ⟨hT, hentry, hμ, hU, hW, hdecU, hdecW, hK, hvalid, ?_, hcP, hcG, hcphase, hctime⟩
  have htc : 0 < connectionReturnTime p := hvalid.1.1.1
  have Hflow := restartFastShearProjectiveEntry_flow hrad.le hs hA (add_nonneg hT.le htc.le)
  exact (horbit.trans Hflow).trans (by
    change _ = toProjectiveState (normalizedMaxCurve x 0 (s + T + _))
    simp only [s, T, x, p, y, add_assoc])

end BianchiIX
