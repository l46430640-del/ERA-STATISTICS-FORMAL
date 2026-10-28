import BianchiIX.Dynamics.ShearRestartCutoffGerm
import BianchiIX.Dynamics.EntranceDownwardPersistence
import BianchiIX.Dynamics.ShearRestartTailCoreEntry
import BianchiIX.Dynamics.ShearRestartTailConnection

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The long tail is an auxiliary cutoff: all return data agree with the fast-cutoff map on an ordinary open germ. -/
theorem exists_restartShearTail_cutoff_germs :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε ζ ν : ℝ,
          (0 ≤ ε ∧ ε ≤ 1 / 128) →
          (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
          (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
          let s := q / 2 * Real.log (1 / a)
          let S := shearTailTime a D
          (fun v : (ℝ × ℝ) × ℝ => restartShearReturnParameters h s v.1.1 v.1.2 v.2) =ᶠ[𝓝 ((ζ, ν), ρ)]
            (fun v => restartShearReturnParameters h (S + s) v.1.1 v.1.2 v.2) ∧
          (fun v : (ℝ × ℝ) × ℝ => restartShearReturnState h s v.1.1 v.1.2 v.2) =ᶠ[𝓝 ((ζ, ν), ρ)]
            (fun v => restartShearReturnState h (S + s) v.1.1 v.1.2 v.2) ∧
          (fun v : (ℝ × ℝ) × ℝ => restartShearReturnPhase h s v.1.1 v.1.2 v.2) =ᶠ[𝓝 ((ζ, ν), ρ)]
            (fun v => restartShearReturnPhase h (S + s) v.1.1 v.1.2 v.2) ∧
          (fun v : (ℝ × ℝ) × ℝ => restartShearReturnTime h s v.1.1 v.1.2 v.2) =ᶠ[𝓝 ((ζ, ν), ρ)]
            (fun v => restartShearReturnTime h (S + s) v.1.1 v.1.2 v.2) := by
  obtain ⟨hI, hhI, HI⟩ := exists_restartShearTail_core_inputs
  obtain ⟨hV, hhV, HV⟩ := exists_restartShearTail_control
  refine ⟨min hI hV, lt_min hhI hhV, ?_⟩
  intro h hh q D P hq hD hP
  obtain ⟨aI, haI, HAI⟩ := HI h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq hD hP
    (1 / 10000) ⟨by norm_num, le_rfl⟩
  obtain ⟨aV, haV, HAV⟩ := HV h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q D P
    (by linarith only [hq]) (by linarith only [hD]) hP
  refine ⟨min aI aV, lt_min haI haV, ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ s S
  obtain ⟨_, _, hk, _, _, hm, hu, hv, hw, hsmall, _⟩ :=
    HAI a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  obtain ⟨_, hs, hS, hrad, _, HT, _⟩ :=
    HAV a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε ζ ν hε ⟨hζ.1.le, hζ.2⟩ ⟨hν.1.le, hν.2⟩ ρ hρ
  have Hnear := eventually_entrancePartialCore_downward_first hk hm.le
    ⟨hu.1.le, hu.2⟩ hv ⟨hw.1.le, hw.2⟩ ⟨by norm_num, le_rfl⟩ hsmall
  apply restartShearReturn_cutoff_eventuallyEq hrad hs hS ?_ Hnear
  intro t ht
  have H := HT t ht
  have HA := H.2.2.2.2.2.2.2.2.2.1
  change a ^ 2 / 10 ≤ restartFastShearHeight h (t + s) 1 ζ ν ρ at HA
  exact ⟨(by positivity [ha.1] : 0 < a ^ 2 / 10).trans_le HA,
    H.2.2.2.2.2.2.2.2.2.2.2⟩

/-- Removing the auxiliary long tail preserves joint C2 regularity at every admissible positive-wall input. -/
theorem exists_restartShearTail_fast_return_regular :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε ζ ν : ℝ,
          (0 ≤ ε ∧ ε ≤ 1 / 128) →
          (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
          (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
          let s := q / 2 * Real.log (1 / a)
          ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartShearReturnParameters h s v.1.1 v.1.2 v.2) ((ζ, ν), ρ) ∧
          ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartShearReturnState h s v.1.1 v.1.2 v.2) ((ζ, ν), ρ) ∧
          ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartShearReturnPhase h s v.1.1 v.1.2 v.2) ((ζ, ν), ρ) ∧
          ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartShearReturnTime h s v.1.1 v.1.2 v.2) ((ζ, ν), ρ) := by
  obtain ⟨hG, hhG, HG⟩ := exists_restartShearTail_cutoff_germs
  obtain ⟨hC, hhC, HC⟩ := exists_restartShearTail_connection
  refine ⟨min hG hC, lt_min hhG hhC, ?_⟩
  intro h hh q D P hq hD hP
  obtain ⟨aG, haG, HAG⟩ := HG h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq hD hP
  obtain ⟨aC, haC, HAC⟩ := HC h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q D P hq hD hP
    (1 / 10000) ⟨by norm_num, le_rfl⟩
  refine ⟨min aG aC, lt_min haG haC, ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ s
  obtain ⟨HP, HG, HX, HT⟩ := HAG a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hcp, hcg, hcx, hct⟩ :=
    HAC a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  exact ⟨hcp.congr_of_eventuallyEq HP, hcg.congr_of_eventuallyEq HG,
    hcx.congr_of_eventuallyEq HX, hct.congr_of_eventuallyEq HT⟩

end BianchiIX
