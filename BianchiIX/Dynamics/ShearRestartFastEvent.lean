import BianchiIX.Dynamics.ShearRestartFastInterval
import BianchiIX.Dynamics.ShearRestartUnifiedDownwardReturn

noncomputable section

namespace BianchiIX

open Set

/-- Any two admissible fast exponents select the same physical downward event in the small-decaying-wall family. -/
theorem exists_restartShear_fast_event_independent :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q₀ q₁ P : ℝ, 3 < q₀ → q₀ ≤ q₁ → 4 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
          ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
          (0 < n₂ ∧ n₂ ≤ 2 * ε * a) → (0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) →
          n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
          let s₀ := q₀ / 2 * Real.log (1 / a)
          let s₁ := q₁ / 2 * Real.log (1 / a)
          let y₀ := restartFastShearProjectiveEntry h s₀ 1 n₂ n₃ ρ
          let y₁ := restartFastShearProjectiveEntry h s₁ 1 n₂ n₃ ρ
          s₀ + partialCoreDownwardReturnTime y₀ = s₁ + partialCoreDownwardReturnTime y₁ ∧
          partialCoreDownwardReturnState y₀ = partialCoreDownwardReturnState y₁ := by
  obtain ⟨hI, hhI, HI⟩ := exists_restartShear_fast_interval
  obtain ⟨hR, hhR, HR⟩ := exists_restartShearDownward_return
  refine ⟨min hI hR, lt_min hhI hhR, ?_⟩
  intro h hh q₀ q₁ P hq₀ hq hP
  obtain ⟨aI, haI, HAI⟩ := HI h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩
    q₀ q₁ (by linarith only [hq₀]) hq
  obtain ⟨a₀, ha₀, HA₀⟩ := HR h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q₀ P hq₀ hP
  obtain ⟨a₁, ha₁, HA₁⟩ := HR h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q₁ P (hq₀.trans_le hq) hP
  refine ⟨min aI (min a₀ a₁), lt_min haI (lt_min ha₀ ha₁), ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s₀ s₁ y₀ y₁
  obtain ⟨_, hss, _, Hprefix⟩ := HAI a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩
    ε n₂ n₃ hε ⟨h₂.1.le, h₂.2⟩ h₃ ρ hρ
  obtain ⟨_, _, _, Hfirst₀, Hstate₀, _⟩ :=
    HA₀ a ⟨ha.1, ha.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
      ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ
  obtain ⟨_, _, _, Hfirst₁, Hstate₁, _⟩ :=
    HA₁ a ⟨ha.1, ha.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
      ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ
  let τ₀ := s₀ + partialCoreDownwardReturnTime y₀
  let τ₁ := s₁ + partialCoreDownwardReturnTime y₁
  let x := restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)
  change IsLeast {t | s₀ < t ∧ toProjectiveState (normalizedMaxCurve x 0 t) 2 = 1 ∧
    normalizedEventRate projectiveActiveWall x 0 t < 0} τ₀ at Hfirst₀
  change IsLeast {t | s₁ < t ∧ toProjectiveState (normalizedMaxCurve x 0 t) 2 = 1 ∧
    normalizedEventRate projectiveActiveWall x 0 t < 0} τ₁ at Hfirst₁
  have hafter : s₁ < τ₀ := by
    by_contra H
    have ht : τ₀ ∈ Icc s₀ s₁ := ⟨Hfirst₀.1.1.le, le_of_not_gt H⟩
    rcases (Hprefix τ₀ ht).2.2.2.2.2.2 with hv | hr
    · exact hv Hfirst₀.1.2.1
    · exact not_lt_of_ge hr.le Hfirst₀.1.2.2
  have Heq : τ₀ = τ₁ := le_antisymm
    (Hfirst₀.2 ⟨hss.trans_lt Hfirst₁.1.1, Hfirst₁.1.2⟩)
    (Hfirst₁.2 ⟨hafter, Hfirst₀.1.2⟩)
  refine ⟨Heq, ?_⟩
  change partialCoreDownwardReturnState y₀ =
    toCoreAngleState (toProjectiveState (normalizedMaxCurve x 0 τ₀)) at Hstate₀
  change partialCoreDownwardReturnState y₁ =
    toCoreAngleState (toProjectiveState (normalizedMaxCurve x 0 τ₁)) at Hstate₁
  rw [Hstate₀, Hstate₁, Heq]

end BianchiIX
