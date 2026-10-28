import BianchiIX.Dynamics.ShearRestartReturnMap
import BianchiIX.Dynamics.ShearRestartDownwardConnection

noncomputable section

namespace BianchiIX

open Set

theorem contDiffAt_restartFastShearProjectiveEntry_joint {h s σ n₂ n₃ ρ : ℝ}
    (hZ : 0 < restartSectionRadicand h (restartShearCurve σ n₂ n₃ ρ))
    (hs : s ∈ normalizedMaxDomain (restartSectionChart h (restartShearCurve σ n₂ n₃ ρ)) 0)
    (hA : restartFastShearHeight h s σ n₂ n₃ ρ ≠ 0) :
    ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartFastShearProjectiveEntry h s σ p.1.1 p.1.2 p.2)
      ((n₂, n₃), ρ) := by
  have hc : ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartShearCurve σ p.1.1 p.1.2 p.2) ((n₂, n₃), ρ) := by
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i <;> dsimp [restartShearCurve] <;> fun_prop
  have hchart := (contDiffAt_restartSectionChart hZ 2).comp ((n₂, n₃), ρ) hc
  have hflow := (contDiffAt_normalizedMaxCurve_two hs).comp ((n₂, n₃), ρ)
    (g := fun p : NormalizedState × ℝ => normalizedMaxCurve p.1 0 p.2)
    (hchart.prodMk (contDiffAt_const (c := s)))
  exact (contDiffAt_toProjectiveState 2 hA).comp ((n₂, n₃), ρ) hflow

/-- The fixed positive-shear restart is jointly C2 in both wall labels and the radial coordinate, including V = 1. -/
theorem exists_restartShearReturn_joint_regular :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
        ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
          (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) → (0 < n₃ ∧ n₃ ≤ 2 * ε * a) →
          n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
            let s := q / 2 * Real.log (1 / a)
            1 ≤ restartFastShearProjectiveEntry h s 1 n₂ n₃ ρ 2 →
            ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartFastShearProjectiveEntry h s 1 p.1.1 p.1.2 p.2) ((n₂, n₃), ρ) ∧
            ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartShearReturnParameters h s p.1.1 p.1.2 p.2) ((n₂, n₃), ρ) ∧
            ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartShearReturnState h s p.1.1 p.1.2 p.2) ((n₂, n₃), ρ) ∧
            ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartShearReturnPhase h s p.1.1 p.1.2 p.2) ((n₂, n₃), ρ) ∧
            ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartShearReturnTime h s p.1.1 p.1.2 p.2) ((n₂, n₃), ρ) := by
  obtain ⟨hE, hhE, HE⟩ := exists_restartShearPartialCore_entry
  obtain ⟨hC, hhC, HC⟩ := exists_restartShearPartialCore_downward_connection
  refine ⟨min hE hC, lt_min hhE hhC, ?_⟩
  intro h hh q P hq hP
  obtain ⟨aE, haE, HaE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q P hq hP
    (1 / 10000) ⟨by norm_num, le_rfl⟩
  obtain ⟨aC, haC, HaC⟩ := HC h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q P hq hP
    (1 / 10000) ⟨by norm_num, le_rfl⟩
  refine ⟨min aE aC, lt_min haE haC, ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s hv
  obtain ⟨_, hrad, hdom, hA, _, hk, _, _, hR, _, _, _, Hentry⟩ :=
    HaE a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ ⟨h₃.1.le, h₃.2⟩ h₃P ρ hρ
  obtain ⟨_, _, hy, hvcase⟩ := Hentry hv
  obtain ⟨_, _, _, hμ, hu, hw, _, _, _, _, hct, _, _, hcp, _⟩ :=
    HaC a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ hv
  let base : (ℝ × ℝ) × ℝ := ((n₂, n₃), ρ)
  let Y := fun p : (ℝ × ℝ) × ℝ => restartFastShearProjectiveEntry h s 1 p.1.1 p.1.2 p.2
  have hcY : ContDiffAt ℝ 2 Y base := contDiffAt_restartFastShearProjectiveEntry_joint hrad hdom hA.ne'
  have Hcore := partialCoreDownwardReturn_regular hk hy hR hvcase
  have hcP : ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartShearReturnParameters h s p.1.1 p.1.2 p.2) base :=
    ContDiffAt.comp (g := fun z => coreExitConnectionParameters (partialCoreDownwardReturnState z))
      (f := Y) base hcp hcY
  have hcG : ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartShearReturnState h s p.1.1 p.1.2 p.2) base :=
    ContDiffAt.comp (g := connectionReturnPhysicalState) base
      (contDiffAt_connectionReturnPhysicalState hμ.1 ⟨hu.1.le, hu.2⟩ hw) hcP
  have hg0 : restartShearReturnState h s n₂ n₃ ρ 0 ≠ 0 := by
    change phaseNorm (-connectionReturnState (restartShearReturnParameters h s n₂ n₃ ρ) 0 - 1) 1 ≠ 0
    exact ne_of_gt (by unfold phaseNorm; positivity)
  have hcphase : ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartShearReturnPhase h s p.1.1 p.1.2 p.2) base :=
    contDiffAt_const.div (contDiffAt_pi.mp hcG 0) hg0
  have hctime : ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartShearReturnTime h s p.1.1 p.1.2 p.2) base :=
    (contDiffAt_const.add (Hcore.2.1.comp base hcY)).add
      (ContDiffAt.comp (g := connectionReturnTime) base hct hcP)
  exact ⟨hcY, hcP, hcG, hcphase, hctime⟩

/-- Restriction of the joint ordinary regularity to a fixed shear ray. -/
theorem exists_restartShearReturn_regular :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
        ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
          (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) → (0 < n₃ ∧ n₃ ≤ 2 * ε * a) →
          n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
            let s := q / 2 * Real.log (1 / a)
            1 ≤ restartFastShearProjectiveEntry h s 1 n₂ n₃ ρ 2 →
            ContDiffAt ℝ 2 (restartFastShearProjectiveEntry h s 1 n₂ n₃) ρ ∧
            ContDiffAt ℝ 2 (restartShearReturnParameters h s n₂ n₃) ρ ∧
            ContDiffAt ℝ 2 (restartShearReturnState h s n₂ n₃) ρ ∧
            ContDiffAt ℝ 2 (restartShearReturnPhase h s n₂ n₃) ρ ∧
            ContDiffAt ℝ 2 (restartShearReturnTime h s n₂ n₃) ρ := by
  obtain ⟨hstar, hhstar, HH⟩ := exists_restartShearReturn_joint_regular
  refine ⟨hstar, hhstar, ?_⟩
  intro h hh q P hq hP
  obtain ⟨astar, hastar, Ha⟩ := HH h hh q P hq hP
  refine ⟨astar, hastar, ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s hv
  obtain ⟨hY, hp, hG, hf, ht⟩ := Ha a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ hv
  have hc : ContDiffAt ℝ 2 (fun r : ℝ => ((n₂, n₃), r)) ρ := by fun_prop
  exact ⟨hY.comp ρ hc, hp.comp ρ hc, hG.comp ρ hc, hf.comp ρ hc, ht.comp ρ hc⟩

end BianchiIX
