import BianchiIX.Dynamics.ShearRestartTailCutoff
import BianchiIX.Dynamics.ShearRestartTailOutputPhase
import BianchiIX.Dynamics.ShearRestartTailOutputBounds

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The common fast-cutoff map inherits the long-tail phase estimate and its ordinary radial derivative. -/
theorem exists_restartShearTail_fast_output_phase :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D : ℝ, 3 < q → 4 < D → ∃ C > (0 : ℝ),
        ∀ P : ℝ, 6 * D + 2 < P → ∃ astar > (0 : ℝ),
          ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε ζ ν : ℝ,
            (0 ≤ ε ∧ ε ≤ 1 / 128) →
            (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
            (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
            let s := q / 2 * Real.log (1 / a)
            let X := restartShearReturnPhase h s ζ ν
            let F := fun r => restartReferenceRadialPhase h (restartShearCurve 1 ζ ν r)
            DifferentiableAt ℝ X ρ ∧ |X ρ - F ρ| ≤ C * a ^ 2 ∧
            |deriv X ρ - deriv F ρ| ≤ C * a ∧
            1 / (8 * Real.sqrt 3) ≤ deriv X ρ ∧ deriv X ρ ≤ C := by
  obtain ⟨hG, hhG, HG⟩ := exists_restartShearTail_cutoff_germs
  obtain ⟨hX, hhX, HX⟩ := exists_restartShearTail_output_phase
  refine ⟨min hG hX, lt_min hhG hhX, ?_⟩
  intro h hh q D hq hD
  obtain ⟨C, hC, HC⟩ := HX h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q D hq hD
  refine ⟨C, hC, ?_⟩
  intro P hP
  obtain ⟨aG, haG, HAG⟩ := HG h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq hD hP
  obtain ⟨aX, haX, HAX⟩ := HC P hP
  refine ⟨min aG aX, lt_min haG haX, ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ s X F
  have H := (HAG a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ).2.2.1
  have hi : ContinuousAt (fun r : ℝ => ((ζ, ν), r)) ρ := continuousAt_const.prodMk continuousAt_id
  have Heq : X =ᶠ[𝓝 ρ] restartShearReturnPhase h (shearTailTime a D + s) ζ ν := hi.tendsto.eventually H
  obtain ⟨hd, hv, hder, hlo, hhi⟩ :=
    HAX a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  refine ⟨hd.congr_of_eventuallyEq Heq, ?_, ?_, ?_, ?_⟩
  · rw [Heq.self_of_nhds]
    exact hv
  · rw [Heq.deriv_eq]
    exact hder
  · rw [Heq.deriv_eq]
    exact hlo
  · rw [Heq.deriv_eq]
    exact hhi

/-- The common fast-cutoff map reaches the same physical reflected section with the original product amplitude. -/
theorem exists_restartShearTail_fast_output_bounds :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε ζ ν : ℝ,
          (0 ≤ ε ∧ ε ≤ 1 / 128) →
          (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
          (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
          let s := q / 2 * Real.log (1 / a)
          let x := restartSectionChart h (restartShearCurve 1 ζ ν ρ)
          let p := restartShearReturnParameters h s ζ ν ρ
          let G := restartShearReturnState h s ζ ν ρ
          connectionReturnValid p ∧ s < restartShearReturnTime h s ζ ν ρ ∧
          1 / (96 * a) ≤ G 0 ∧ G 0 ≤ 128 / a ∧
          0 < G 1 ∧ 0 < G 2 ∧ G 1 + G 2 ≤ 512 * ζ * ν / a ^ 4 ∧
          coreRadiusEntry G = projectiveReflection (toProjectiveState
            (normalizedMaxCurve x 0 (restartShearReturnTime h s ζ ν ρ))) := by
  obtain ⟨hG, hhG, HG⟩ := exists_restartShearTail_cutoff_germs
  obtain ⟨hB, hhB, HB⟩ := exists_restartShearTail_output_bounds
  refine ⟨min hG hB, lt_min hhG hhB, ?_⟩
  intro h hh q D P hq hD hP
  obtain ⟨aG, haG, HAG⟩ := HG h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq hD hP
  obtain ⟨aB, haB, HAB⟩ := HB h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q D P hq hD hP
  refine ⟨min aG (min aB 1), lt_min haG (lt_min haB zero_lt_one), ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ s x p G
  have ha1 := ha.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨HP, HG, _, HT⟩ := HAG a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  have hp := HP.self_of_nhds
  have hg := HG.self_of_nhds
  have ht := HT.self_of_nhds
  change p = restartShearReturnParameters h (shearTailTime a D + s) ζ ν ρ at hp
  change G = restartShearReturnState h (shearTailTime a D + s) ζ ν ρ at hg
  change restartShearReturnTime h s ζ ν ρ = restartShearReturnTime h (shearTailTime a D + s) ζ ν ρ at ht
  obtain ⟨hvalid, htime, hlo, hhi, h₁, h₂, hsum, horbit⟩ :=
    HAB a ⟨ha.1, ha.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩ ε ζ ν hε hζ hν ρ hρ
  have hS : 0 ≤ shearTailTime a D := mul_nonneg (div_nonneg (by linarith only [hD]) ha.1.le)
    (Real.log_nonneg ((le_div_iff₀ ha.1).mpr (by simpa using ha1)))
  rw [hp, hg, ht]
  exact ⟨hvalid, lt_of_le_of_lt (le_add_of_nonneg_left hS) htime, hlo, hhi, h₁, h₂, hsum, horbit⟩

end BianchiIX
