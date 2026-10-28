import BianchiIX.Dynamics.ShearRestartEntranceCone
import BianchiIX.Dynamics.EntranceFullCoreIdentification
import BianchiIX.Dynamics.CoreReturnCurveCone

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The exact shear family below the active-wall section reaches its fixed downward event
with negative radial slope and the full-core square-root cone margin. -/
theorem exists_restartShearEntrance_core_cone :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
        ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
          (0 < n₂ ∧ n₂ ≤ 2 * ε * a) → (0 < n₃ ∧ n₃ ≤ 2 * ε * a) →
          n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
            let s := q / 2 * Real.log (1 / a)
            let Y := restartFastShearProjectiveEntry h s 1 n₂ n₃
            let Z := fun t => entranceReturnState (Y t)
            let κ := fun t => coreRadius (Z t 0) (Z t 2)
            let G := fun t => partialCoreDownwardReturnState (Y t)
            Y ρ 2 < 1 → 6 ≤ κ ρ ∧ DifferentiableAt ℝ κ ρ ∧ DifferentiableAt ℝ G ρ ∧
              deriv κ ρ < 0 ∧ deriv (fun t => G t 0) ρ < 0 ∧
              |deriv (fun t => G t 0) ρ / deriv κ ρ - 1| ≤ 1 / (32 * κ ρ) ∧
              (3 / 4 ≤ deriv (fun t => G t 0) ρ / deriv κ ρ ∧
                deriv (fun t => G t 0) ρ / deriv κ ρ ≤ 5 / 4) ∧
              ∀ i : Fin 2, |deriv (fun t => G t i.succ) ρ| ≤
                (1 - 1 / (16 * κ ρ)) * Real.sqrt (G ρ i.succ) * |deriv (fun t => G t 0) ρ| := by
  obtain ⟨δ, hδ, hδsmall, HC⟩ := exists_coreRadiusReturn_curve_cone
  obtain ⟨hI, hhI, _, _, HI⟩ := exists_restartShearEntrance_differential_inputs
  obtain ⟨hE, hhE, HE⟩ := exists_restartShearEntrance_cone
  refine ⟨min hI hE, lt_min hhI hhE, ?_⟩
  intro h hh q P hq hP
  obtain ⟨aI, haI, HaI⟩ := HI h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q P hq hP δ ⟨hδ, hδsmall⟩
  obtain ⟨aE, haE, HaE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q P hq hP 1 zero_lt_one
  refine ⟨min aI aE, lt_min haI haE, ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s Y Z κ G hv
  obtain ⟨HY, hk8, _, _, hm, hu, hv', hw, hsmall, _⟩ :=
    HaI a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ hv
  obtain ⟨HZ, HK, Hneg, _, _, HU, HW⟩ :=
    HaE a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ hv
  change DifferentiableAt ℝ Y ρ at HY
  change DifferentiableAt ℝ Z ρ at HZ
  change DifferentiableAt ℝ κ ρ at HK
  change 0 < -deriv κ ρ at Hneg
  change |deriv (fun t => Z t 1) ρ| ≤ 1 * Real.sqrt (Z ρ 1) * |deriv κ ρ| at HU
  change |deriv (fun t => Z t 3) ρ| ≤ 1 * Real.sqrt (Z ρ 3) * |deriv κ ρ| at HW
  have hu' : 0 ≤ Y ρ 1 ∧ Y ρ 1 ≤ 1 / 10000 := ⟨hu.1.le, hu.2.trans hδsmall⟩
  have hw' : 0 ≤ Y ρ 3 ∧ Y ρ 3 ≤ 1 / 10000 := ⟨hw.1.le, hw.2.trans hδsmall⟩
  obtain ⟨hκ, _, hhit, _, _, hU, hW, hsum, _⟩ :=
    entranceReturn_partialCore_entry hk8 hm.le hu' hv' hw' ⟨hδ, hδsmall⟩ hsmall
  change 6 ≤ κ ρ at hκ
  change Z ρ 2 = 1 at hhit
  change Z ρ 1 + Z ρ 2 * Z ρ 3 ≤ δ / κ ρ at hsum
  rw [hhit, one_mul] at hsum
  let X : ℝ → CoreAngleState := fun t => ![κ t, Z t 1, Z t 3]
  have HX : DifferentiableAt ℝ X ρ := by
    apply differentiableAt_pi.mpr
    intro i
    fin_cases i
    · exact HK
    · exact (differentiableAt_pi.mp HZ) 1
    · exact (differentiableAt_pi.mp HZ) 3
  have Hwall : ∀ i : Fin 2, |deriv (fun t => X t i.succ) ρ| ≤
      Real.sqrt (X ρ i.succ) * |deriv (fun t => X t 0) ρ| := by
    intro i
    fin_cases i
    · simpa [X] using HU
    · simpa [X] using HW
  have Hcore := HC X ρ HX hκ
    ⟨hU.1, (le_add_of_nonneg_right hW.1).trans hsum⟩
    ⟨hW.1, (le_add_of_nonneg_left hU.1).trans hsum⟩ (neg_pos.mp Hneg) Hwall
  let F := fun t => coreReturnState coreRadiusReturnTime (X t)
  have hg := (entrancePartialCore_fullCore_eventuallyEq hk8 hm.le hu' hv' hw'
    ⟨hδ, hδsmall⟩ hsmall).2
  have hk' : 7 / 4 ≤ coreRadius (Y ρ 0) (Y ρ 2) := by
    change 8 ≤ coreRadius (Y ρ 0) (Y ρ 2) at hk8
    linarith only [hk8]
  have hx := entranceReturn_coreCoordinates_eventuallyEq hk' hm.le hu' hv' hw'
  have heq : G =ᶠ[𝓝 ρ] F := by
    filter_upwards [HY.continuousAt.eventually hg, HY.continuousAt.eventually hx] with t ht hx'
    exact ht.trans (congrArg (coreReturnState coreRadiusReturnTime) hx')
  have heqi (i : Fin 3) : (fun t => G t i) =ᶠ[𝓝 ρ] fun t => F t i :=
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
