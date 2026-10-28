import BianchiIX.Dynamics.ShearRestartEntranceReturn
import BianchiIX.Dynamics.ShearRestartReturnRegularity

noncomputable section

namespace BianchiIX

open Set

/-- One ordinary C2 downward event covers every positive active wall in the small-decaying-wall shear family. -/
theorem exists_restartShearDownward_return :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
        ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
          (0 < n₂ ∧ n₂ ≤ 2 * ε * a) → (0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) →
          n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
            let s := q / 2 * Real.log (1 / a)
            let x := restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)
            let y := restartFastShearProjectiveEntry h s 1 n₂ n₃ ρ
            let T := partialCoreDownwardReturnTime y
            0 < T ∧ ContDiffAt ℝ 2 partialCoreDownwardReturnTime y ∧
              ContDiffAt ℝ 2 partialCoreDownwardReturnState y ∧
              IsLeast {t | s < t ∧ toProjectiveState (normalizedMaxCurve x 0 t) 2 = 1 ∧
                normalizedEventRate projectiveActiveWall x 0 t < 0} (s + T) ∧
              partialCoreDownwardReturnState y = toCoreAngleState
                (toProjectiveState (normalizedMaxCurve x 0 (s + T))) ∧
              ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => s + partialCoreDownwardReturnTime
                (restartFastShearProjectiveEntry h s 1 p.1.1 p.1.2 p.2)) ((n₂, n₃), ρ) ∧
              ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => partialCoreDownwardReturnState
                (restartFastShearProjectiveEntry h s 1 p.1.1 p.1.2 p.2)) ((n₂, n₃), ρ) := by
  obtain ⟨hE, hhE, HE⟩ := exists_restartShearPartialCore_entry
  obtain ⟨hL, hhL, HL⟩ := exists_restartShearEntrance_inputs
  refine ⟨min hE hL, lt_min hhE hhL, ?_⟩
  intro h hh q P hq hP
  obtain ⟨aE, haE, HaE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q P hq hP
    (1 / 10000) ⟨by norm_num, le_rfl⟩
  obtain ⟨aL, haL, HaL⟩ := HL h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q P hq hP
    (1 / 10000) ⟨by norm_num, le_rfl⟩
  refine ⟨min aE aL, lt_min haE haL, ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s x y T
  obtain ⟨hs, hrad, hdom, hA, _, hk, _, _, hR, _, _, _, Hentry⟩ :=
    HaE a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε ⟨h₂.1.le, h₂.2⟩ h₃ h₃P ρ hρ
  have H : 0 < projectiveStateDenom y ∧
      IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧
        projectiveOriginalFlow y 0 t 2 = 1 ∧ normalizedEventRate projectiveActiveWall (fromProjectiveState y) 0 t < 0} T ∧
      ContDiffAt ℝ 2 partialCoreDownwardReturnTime y ∧ ContDiffAt ℝ 2 partialCoreDownwardReturnState y := by
    by_cases hv : 1 ≤ y 2
    · obtain ⟨_, _, hy, hvcase⟩ := Hentry hv
      have HC := partialCoreDownwardReturn_regular hk hy hR hvcase
      exact ⟨(coreRegion_clock_regular hk hy).1, HC.2.2.2.1.self_of_nhds.1, HC.2.1, HC.2.2.1⟩
    · obtain ⟨_, _, _, _, hk8, _, _, hm, hu, hv', hw, hsmall⟩ :=
        HaL a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ (lt_of_not_ge hv)
      have hk' : 7 / 4 ≤ coreRadius (y 0) (y 2) := (by norm_num : (7 : ℝ) / 4 ≤ 8).trans hk8
      obtain ⟨hfirst, _, _, hct, hcs, _⟩ := entrancePartialCore_downward_regular hk8 hm.le
        ⟨hu.1.le, hu.2⟩ hv' hw ⟨by norm_num, le_rfl⟩ hsmall
      exact ⟨entrance_initial_denom_pos hk' hm.le ⟨hu.1.le, hu.2⟩ hv' hw, hfirst, hct, hcs⟩
  have hT : 0 < T := H.2.1.1.1
  let base : (ℝ × ℝ) × ℝ := ((n₂, n₃), ρ)
  let Y := fun p : (ℝ × ℝ) × ℝ => restartFastShearProjectiveEntry h s 1 p.1.1 p.1.2 p.2
  have hcY : ContDiffAt ℝ 2 Y base := contDiffAt_restartFastShearProjectiveEntry_joint hrad hdom hA.ne'
  have htime := ContDiffAt.comp (g := partialCoreDownwardReturnTime) (f := Y) base H.2.2.1 hcY
  have hstate := ContDiffAt.comp (g := partialCoreDownwardReturnState) (f := Y) base H.2.2.2 hcY
  refine ⟨hT, H.2.2.1, H.2.2.2, restartFastShearProjectiveEntry_downward_event hrad.le hs hA H.1 H.2.1,
    ?_, contDiffAt_const.add htime, hstate⟩
  exact congrArg toCoreAngleState (restartFastShearProjectiveEntry_flow hrad.le hs hA hT.le)

end BianchiIX
