import BianchiIX.Dynamics.ShearRestartCommonReturn
import BianchiIX.Dynamics.ShearRestartTailConnectionCurve

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The ordinary cutoff germ carries the long-tail square-root cone back to the original fast-cutoff return. -/
theorem exists_restartShearTail_fast_cone :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε ζ ν : ℝ,
          (0 ≤ ε ∧ ε ≤ 1 / 128) → (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
          (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
          let s := q / 2 * Real.log (1 / a)
          let G := restartShearReturnState h s ζ ν
          let g := fun r => G r 0
          ContDiffAt ℝ 2 G ρ ∧ deriv g ρ < 0 ∧
          ∀ i : Fin 2, |deriv (fun r => G r i.succ) ρ| ≤ Real.sqrt (G ρ i.succ) * |deriv g ρ| := by
  obtain ⟨hG, hhG, HG⟩ := exists_restartShearTail_cutoff_germs
  obtain ⟨hC, hhC, HC⟩ := exists_restartShearTail_connection_curve
  refine ⟨min hG hC, lt_min hhG hhC, ?_⟩
  intro h hh q D P hq hD hP
  obtain ⟨aG, haG, HAG⟩ := HG h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq hD hP
  obtain ⟨aC, haC, HAC⟩ := HC h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q D P hq hD hP
  refine ⟨min aG aC, lt_min haG haC, ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ s G g
  have H := (HAG a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ).2.1
  have hi : ContinuousAt (fun r : ℝ => ((ζ, ν), r)) ρ := continuousAt_const.prodMk continuousAt_id
  have Heq : G =ᶠ[𝓝 ρ] restartShearReturnState h (shearTailTime a D + s) ζ ν := hi.tendsto.eventually H
  have Heqi (i : Fin 3) : (fun r => G r i) =ᶠ[𝓝 ρ]
      (fun r => restartShearReturnState h (shearTailTime a D + s) ζ ν r i) :=
    Heq.mono fun _ hv => congrFun hv i
  obtain ⟨hc, _, _, _, _, hneg, _, _, hcone, _⟩ :=
    HAC a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  refine ⟨hc.congr_of_eventuallyEq Heq, ?_, ?_⟩
  · change deriv (fun r => G r 0) ρ < 0
    rw [(Heqi 0).deriv_eq]
    exact hneg
  · intro i
    change |deriv (fun r => G r i.succ) ρ| ≤ Real.sqrt (G ρ i.succ) * |deriv (fun r => G r 0) ρ|
    rw [(Heqi i.succ).deriv_eq, (Heqi 0).deriv_eq, Heq.self_of_nhds]
    exact hcone i

/-- The single positive-shear return preserves the square-root cone for either choice of the small wall. -/
theorem exists_restartShearReturn_common_cone :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε n₂ n₃ : ℝ,
          (0 ≤ ε ∧ ε ≤ 1 / 128) → (0 < n₂ ∧ n₂ ≤ 2 * ε * a) →
          (0 < n₃ ∧ n₃ ≤ 2 * ε * a) → min n₂ n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
          let s := q / 2 * Real.log (1 / a)
          let G := restartShearReturnState h s n₂ n₃
          let g := fun r => G r 0
          ContDiffAt ℝ 2 G ρ ∧ deriv g ρ < 0 ∧
          ∀ i : Fin 2, |deriv (fun r => G r i.succ) ρ| ≤ Real.sqrt (G ρ i.succ) * |deriv g ρ| := by
  obtain ⟨hA, hhA, HA⟩ := exists_restartShearReturn_all_active_cone
  obtain ⟨hT, hhT, HT⟩ := exists_restartShearTail_fast_cone
  refine ⟨min hA hT, lt_min hhA hhT, ?_⟩
  intro h hh q D P hq hD hP
  obtain ⟨aA, haA, HAA⟩ := HA h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q P hq (by linarith only [hD, hP])
  obtain ⟨aT, haT, HAT⟩ := HT h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q D P hq hD hP
  refine ⟨min aA aT, lt_min haA haT, ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ hmin ρ hρ s G g
  by_cases hn₃ : n₃ ≤ a ^ P
  · obtain ⟨hc, hneg, hcone, _⟩ := HAA a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃
      ⟨hε.1, hε.2.trans (by norm_num)⟩ h₂ h₃ hn₃ ρ hρ
    exact ⟨hc, hneg, hcone⟩
  · exact HAT a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε n₂ n₃ hε
      ⟨h₂.1, (min_le_iff.mp hmin).resolve_right hn₃, h₂.2⟩ h₃ ρ hρ

/-- The negative-shear return has the same cone along the original positive radial parameter. -/
theorem exists_restartShear_negative_cone :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε n₂ n₃ : ℝ,
          (0 ≤ ε ∧ ε ≤ 1 / 128) → (0 < n₂ ∧ n₂ ≤ 2 * ε * a) →
          (0 < n₃ ∧ n₃ ≤ 2 * ε * a) → min n₂ n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
          let s := q / 2 * Real.log (1 / a)
          let G := restartShearReturnState h s n₃ n₂
          let g := fun r => G r 0
          ContDiffAt ℝ 2 G ρ ∧ deriv g ρ < 0 ∧
          ∀ i : Fin 2, |deriv (fun r => G r i.succ) ρ| ≤ Real.sqrt (G ρ i.succ) * |deriv g ρ| := by
  obtain ⟨hstar, hhstar, HH⟩ := exists_restartShearReturn_common_cone
  refine ⟨hstar, hhstar, ?_⟩
  intro h hh q D P hq hD hP
  obtain ⟨astar, hastar, HA⟩ := HH h hh q D P hq hD hP
  refine ⟨astar, hastar, ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ hmin ρ hρ
  exact HA a ha ε n₃ n₂ hε h₃ h₂ (by simpa only [min_comm] using hmin) ρ hρ

end BianchiIX
