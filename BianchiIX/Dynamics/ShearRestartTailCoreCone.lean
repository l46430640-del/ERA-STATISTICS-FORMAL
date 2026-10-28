import BianchiIX.Dynamics.ShearRestartTailCoreEntry
import BianchiIX.Dynamics.ShearRestartTailEntranceCone
import BianchiIX.Dynamics.EntranceFullCoreIdentification
import BianchiIX.Dynamics.CoreReturnCurveCone

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The long-tail family retains its negative radial slope and square-root cone through the actual full core. -/
theorem exists_restartShearTail_core_cone :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε ζ ν : ℝ,
          (0 ≤ ε ∧ ε ≤ 1 / 128) →
          (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
          (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
          let Y := restartShearTailProjectiveEntry h a q ζ ν (shearTailTime a D)
          let κ := restartShearTailEntranceRadius h a q D ζ ν
          let G := fun r => partialCoreDownwardReturnState (Y r)
          6 ≤ κ ρ ∧ DifferentiableAt ℝ κ ρ ∧ DifferentiableAt ℝ G ρ ∧
          deriv κ ρ < 0 ∧ deriv (fun r => G r 0) ρ < 0 ∧
          |deriv (fun r => G r 0) ρ / deriv κ ρ - 1| ≤ 1 / (32 * κ ρ) ∧
          (3 / 4 ≤ deriv (fun r => G r 0) ρ / deriv κ ρ ∧
            deriv (fun r => G r 0) ρ / deriv κ ρ ≤ 5 / 4) ∧
          ∀ i : Fin 2, |deriv (fun r => G r i.succ) ρ| ≤
            (1 - 1 / (16 * κ ρ)) * Real.sqrt (G ρ i.succ) * |deriv (fun r => G r 0) ρ| := by
  obtain ⟨δ, hδ, hδsmall, HC⟩ := exists_coreRadiusReturn_curve_cone
  obtain ⟨hI, hhI, HI⟩ := exists_restartShearTail_core_inputs
  obtain ⟨hE, hhE, HE⟩ := exists_restartShearTail_entrance_cone
  refine ⟨min hI hE, lt_min hhI hhE, ?_⟩
  intro h hh q D P hq hD hP
  obtain ⟨aI, haI, HAI⟩ := HI h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq hD hP δ ⟨hδ, hδsmall⟩
  obtain ⟨aE, haE, HAE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q D P
    (by linarith only [hq]) (by linarith only [hD]) hP 1 zero_lt_one
  refine ⟨min aI aE, lt_min haI haE, ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ Y κ G
  obtain ⟨_, HY, hk8, _, _, hm, hu, hv, hw, hsmall, _⟩ :=
    HAI a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  obtain ⟨HZ, HK, Hneg, _, _, HU, HW⟩ :=
    HAE a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  let Z := fun r => entranceReturnState (Y r)
  change DifferentiableAt ℝ Y ρ at HY
  change DifferentiableAt ℝ Z ρ at HZ
  change DifferentiableAt ℝ κ ρ at HK
  change 0 < -deriv κ ρ at Hneg
  change |deriv (fun r => Z r 1) ρ| ≤ 1 * Real.sqrt (Z ρ 1) * |deriv κ ρ| at HU
  change |deriv (fun r => Z r 3) ρ| ≤ 1 * Real.sqrt (Z ρ 3) * |deriv κ ρ| at HW
  have hu' : 0 ≤ Y ρ 1 ∧ Y ρ 1 ≤ 1 / 10000 := ⟨hu.1.le, hu.2⟩
  have hw' : 0 ≤ Y ρ 3 ∧ Y ρ 3 ≤ 1 / 10000 := ⟨hw.1.le, hw.2⟩
  obtain ⟨hκ, _, hhit, _, _, hU, hW, hsum, _⟩ :=
    entranceReturn_partialCore_entry hk8 hm.le hu' hv hw' ⟨hδ, hδsmall⟩ hsmall
  change 6 ≤ κ ρ at hκ
  change Z ρ 2 = 1 at hhit
  change Z ρ 1 + Z ρ 2 * Z ρ 3 ≤ δ / κ ρ at hsum
  rw [hhit, one_mul] at hsum
  let X : ℝ → CoreAngleState := fun r => ![κ r, Z r 1, Z r 3]
  have HX : DifferentiableAt ℝ X ρ := by
    apply differentiableAt_pi.mpr
    intro i
    fin_cases i
    · exact HK
    · exact (differentiableAt_pi.mp HZ) 1
    · exact (differentiableAt_pi.mp HZ) 3
  have Hwall : ∀ i : Fin 2, |deriv (fun r => X r i.succ) ρ| ≤
      Real.sqrt (X ρ i.succ) * |deriv (fun r => X r 0) ρ| := by
    intro i
    fin_cases i
    · simpa [X] using HU
    · simpa [X] using HW
  have Hcore := HC X ρ HX hκ
    ⟨hU.1, (le_add_of_nonneg_right hW.1).trans hsum⟩
    ⟨hW.1, (le_add_of_nonneg_left hU.1).trans hsum⟩ (neg_pos.mp Hneg) Hwall
  let F := fun r => coreReturnState coreRadiusReturnTime (X r)
  have hg := (entrancePartialCore_fullCore_eventuallyEq hk8 hm.le hu' hv hw'
    ⟨hδ, hδsmall⟩ hsmall).2
  have hk' : 7 / 4 ≤ coreRadius (Y ρ 0) (Y ρ 2) := by
    change 8 ≤ coreRadius (Y ρ 0) (Y ρ 2) at hk8
    linarith only [hk8]
  have hx := entranceReturn_coreCoordinates_eventuallyEq hk' hm.le hu' hv hw'
  have heq : G =ᶠ[𝓝 ρ] F := by
    filter_upwards [HY.continuousAt.eventually hg, HY.continuousAt.eventually hx] with r hr hx'
    exact hr.trans (congrArg (coreReturnState coreRadiusReturnTime) hx')
  have heqi (i : Fin 3) : (fun r => G r i) =ᶠ[𝓝 ρ] fun r => F r i :=
    heq.mono fun _ h => congrFun h i
  refine ⟨hκ, HK, Hcore.1.congr_of_eventuallyEq heq, neg_pos.mp Hneg, ?_, ?_, ?_, ?_⟩
  · rw [(heqi 0).deriv_eq]
    exact Hcore.2.1
  · rw [(heqi 0).deriv_eq]
    exact Hcore.2.2.1
  · rw [(heqi 0).deriv_eq]
    exact Hcore.2.2.2.1
  · intro i
    rw [(heqi i.succ).deriv_eq, heq.self_of_nhds, (heqi 0).deriv_eq]
    exact Hcore.2.2.2.2 i

end BianchiIX
