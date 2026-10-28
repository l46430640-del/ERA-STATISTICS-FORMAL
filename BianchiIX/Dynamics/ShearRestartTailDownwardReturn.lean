import BianchiIX.Dynamics.ShearRestartTailCoreEntry
import BianchiIX.Dynamics.ShearRestartEntranceReturn

noncomputable section

namespace BianchiIX

open Set

/-- The regular entrance and full core end at the original orbit's first downward event after its fast cutoff. -/
theorem exists_restartShearTail_downward_return :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε ζ ν : ℝ,
          (0 ≤ ε ∧ ε ≤ 1 / 128) →
          (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
          (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
          let x := restartSectionChart h (restartShearCurve 1 ζ ν ρ)
          let s := q / 2 * Real.log (1 / a)
          let T := shearTailTime a D
          let y := restartShearTailProjectiveEntry h a q ζ ν T ρ
          let z := entranceReturnState y
          let τ := partialCoreDownwardReturnTime y
          0 < τ ∧ τ = entranceReturnTime y + partialCoreDownwardReturnTime z ∧
          partialCoreDownwardReturnState y = partialCoreDownwardReturnState z ∧
          ContDiffAt ℝ 2 partialCoreDownwardReturnTime y ∧ ContDiffAt ℝ 2 partialCoreDownwardReturnState y ∧
          IsLeast {t | s < t ∧ toProjectiveState (normalizedMaxCurve x 0 t) 2 = 1 ∧
            normalizedEventRate projectiveActiveWall x 0 t < 0} ((T + s) + τ) ∧
          (T + s) + τ ∈ normalizedMaxDomain x 0 ∧
          projectiveOriginalFlow y 0 τ = toProjectiveState (normalizedMaxCurve x 0 ((T + s) + τ)) := by
  obtain ⟨hI, hhI, HI⟩ := exists_restartShearTail_core_inputs
  obtain ⟨hV, hhV, HV⟩ := exists_restartShearTail_control
  refine ⟨min hI hV, lt_min hhI hhV, ?_⟩
  intro h hh q D P hq hD hP
  obtain ⟨aI, haI, HAI⟩ := HI h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq hD hP
    (1 / 10000) ⟨by norm_num, le_rfl⟩
  obtain ⟨aV, haV, HAV⟩ := HV h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q D P
    (by linarith only [hq]) (by linarith only [hD]) hP
  refine ⟨min aI aV, lt_min haI haV, ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ x s T y z τ
  obtain ⟨_, _, hk, _, _, hm, hu, hv, hw, hsmall, _⟩ :=
    HAI a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  obtain ⟨_, hs, hT, hrad, hcx, HT, _⟩ :=
    HAV a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε ζ ν hε ⟨hζ.1.le, hζ.2⟩ ⟨hν.1.le, hν.2⟩ ρ hρ
  have hk' : 7 / 4 ≤ coreRadius (y 0) (y 2) := by
    change 8 ≤ coreRadius (y 0) (y 2) at hk
    linarith only [hk]
  obtain ⟨Hdown, Htime, Hstate, Hct, Hcs, _⟩ :=
    entrancePartialCore_downward_regular hk hm.le ⟨hu.1.le, hu.2⟩ hv ⟨hw.1.le, hw.2⟩
      ⟨by norm_num, le_rfl⟩ hsmall
  have hτ : 0 < τ := Hdown.1.1
  have hDenom := entrance_initial_denom_pos hk' hm.le ⟨hu.1.le, hu.2⟩ hv ⟨hw.1.le, hw.2⟩
  have hA : 0 < restartFastShearHeight h (T + s) 1 ζ ν ρ := by
    have H := (HT T ⟨hT, le_rfl⟩).2.2.2.2.2.2.2.2.2.1
    change a ^ 2 / 10 ≤ restartFastShearHeight h (T + s) 1 ζ ν ρ at H
    exact (by positivity [ha.1] : 0 < a ^ 2 / 10).trans_le H
  have HE := restartFastShearProjectiveEntry_downward_event hrad.le (add_nonneg hT hs) hA hDenom Hdown
  change IsLeast {t | T + s < t ∧ toProjectiveState (normalizedMaxCurve x 0 t) 2 = 1 ∧
    normalizedEventRate projectiveActiveWall x 0 t < 0} ((T + s) + τ) at HE
  have Hleast : IsLeast {t | s < t ∧ toProjectiveState (normalizedMaxCurve x 0 t) 2 = 1 ∧
      normalizedEventRate projectiveActiveWall x 0 t < 0} ((T + s) + τ) := by
    refine ⟨⟨by linarith only [HE.1.1, hT], HE.1.2⟩, ?_⟩
    intro t ht
    by_cases hbefore : t ≤ T + s
    · have H := (HT (t - s) ⟨by linarith only [ht.1], by linarith only [hbefore]⟩).2.2.2.2.2.2.2.2.2.2.2
      change toProjectiveState (normalizedMaxCurve x 0 ((t - s) + s)) 2 < 1 at H
      rw [sub_add_cancel, ht.2.1] at H
      exact (lt_irrefl _ H).elim
    · exact HE.2 ⟨lt_of_not_ge hbefore, ht.2⟩
  exact ⟨hτ, Htime, Hstate, Hct, Hcs, Hleast,
    normalizedMaxDomain_contains_Ici_of_constraint hcx 0 (add_nonneg (add_nonneg hT hs) hτ.le),
    restartFastShearProjectiveEntry_flow hrad.le (add_nonneg hT hs) hA hτ.le⟩

end BianchiIX
