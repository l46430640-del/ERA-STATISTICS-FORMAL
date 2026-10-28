import BianchiIX.Dynamics.ShearRestartSymmetry
import BianchiIX.Dynamics.ShearRestartCommonReturn

noncomputable section

namespace BianchiIX

open Set

/-- For negative shear the exchanged-label return reaches the canonical core on the original orbit, without another reflection. -/
theorem exists_restartShear_negative_output_bounds :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε n₂ n₃ : ℝ,
          (0 ≤ ε ∧ ε ≤ 1 / 128) → (0 < n₂ ∧ n₂ ≤ 2 * ε * a) →
          (0 < n₃ ∧ n₃ ≤ 2 * ε * a) → min n₂ n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
          let s := q / 2 * Real.log (1 / a)
          let x := restartSectionChart h (restartShearCurve (-1) n₂ n₃ ρ)
          let p := restartShearReturnParameters h s n₃ n₂ ρ
          let G := restartShearReturnState h s n₃ n₂ ρ
          let T := restartShearReturnTime h s n₃ n₂ ρ
          0 < restartSectionRadicand h (restartShearCurve (-1) n₂ n₃ ρ) ∧
          0 ≤ s ∧ s < T ∧ T ∈ normalizedMaxDomain x 0 ∧ connectionReturnValid p ∧
          1 / (96 * a) ≤ G 0 ∧ G 0 ≤ 128 / a ∧
          0 < G 1 ∧ 0 < G 2 ∧ G 1 + G 2 ≤ 512 * n₂ * n₃ / a ^ 4 ∧
          coreRadiusEntry G = toProjectiveState (normalizedMaxCurve x 0 T) := by
  obtain ⟨hstar, hhstar, HH⟩ := exists_restartShearReturn_common_bounds
  refine ⟨hstar, hhstar, ?_⟩
  intro h hh q D P hq hD hP
  obtain ⟨astar, hastar, HA⟩ := HH h hh q D P hq hD hP
  refine ⟨astar, hastar, ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ hmin ρ hρ s x p G T
  obtain ⟨hrad, hs, ht, hdom, hp, hlo, hhi, hu, hw, hsum, horbit⟩ :=
    HA a ha ε n₃ n₂ hε h₃ h₂ (by simpa only [min_comm] using hmin) ρ hρ
  refine ⟨?_, hs, ht, ?_, hp, hlo, hhi, hu, hw, ?_, ?_⟩
  · rw [restartSectionRadicand_shear_reflection]
    exact hrad
  · change T ∈ normalizedMaxDomain (restartSectionChart h (restartShearCurve (-1) n₂ n₃ ρ)) 0
    rw [normalizedMaxDomain_shear_reflection]
    exact hdom
  · simpa only [mul_assoc, mul_left_comm, mul_comm] using hsum
  · change coreRadiusEntry G = toProjectiveState
      (normalizedMaxCurve (restartSectionChart h (restartShearCurve (-1) n₂ n₃ ρ)) 0 T)
    rw [normalizedMaxCurve_shear_reflection hdom, toProjectiveState_axisSwap]
    exact horbit

/-- Negative shear inherits the full phase estimate with the original negative-shear reference function. -/
theorem exists_restartShear_negative_output_phase :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D : ℝ, 3 < q → 4 < D → ∃ C > (0 : ℝ),
        ∀ P : ℝ, 6 * D + 2 < P → ∃ astar > (0 : ℝ),
          ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε n₂ n₃ : ℝ,
            (0 ≤ ε ∧ ε ≤ 1 / 128) → (0 < n₂ ∧ n₂ ≤ 2 * ε * a) →
            (0 < n₃ ∧ n₃ ≤ 2 * ε * a) → min n₂ n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
            let s := q / 2 * Real.log (1 / a)
            let X := restartShearReturnPhase h s n₃ n₂
            let F := fun r => restartReferenceRadialPhase h (restartShearCurve (-1) n₂ n₃ r)
            DifferentiableAt ℝ X ρ ∧ |X ρ - F ρ| ≤ C * a ^ 2 ∧
            |deriv X ρ - deriv F ρ| ≤ C * a ∧
            1 / (4 * Real.sqrt 3) ≤ deriv X ρ ∧ deriv X ρ ≤ C := by
  obtain ⟨hstar, hhstar, HH⟩ := exists_restartShearReturn_common_phase
  refine ⟨hstar, hhstar, ?_⟩
  intro h hh q D hq hD
  obtain ⟨C, hC, HC⟩ := HH h hh q D hq hD
  refine ⟨C, hC, ?_⟩
  intro P hP
  obtain ⟨astar, hastar, HA⟩ := HC P hP
  refine ⟨astar, hastar, ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ hmin ρ hρ s X F
  have HF : F = fun r => restartReferenceRadialPhase h (restartShearCurve 1 n₃ n₂ r) := by
    funext r
    exact restartReferenceRadialPhase_shear_reflection h 1 n₃ n₂ r
  rw [HF]
  exact HA a ha ε n₃ n₂ hε h₃ h₂ (by simpa only [min_comm] using hmin) ρ hρ

/-- Exchanging the two weak-wall labels transfers joint ordinary C2 regularity to the negative-shear return. -/
theorem exists_restartShear_negative_return_regular :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε n₂ n₃ : ℝ,
          (0 ≤ ε ∧ ε ≤ 1 / 128) → (0 < n₂ ∧ n₂ ≤ 2 * ε * a) →
          (0 < n₃ ∧ n₃ ≤ 2 * ε * a) → min n₂ n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
          let s := q / 2 * Real.log (1 / a)
          ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartShearReturnParameters h s v.1.2 v.1.1 v.2) ((n₂, n₃), ρ) ∧
          ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartShearReturnState h s v.1.2 v.1.1 v.2) ((n₂, n₃), ρ) ∧
          ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartShearReturnPhase h s v.1.2 v.1.1 v.2) ((n₂, n₃), ρ) ∧
          ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartShearReturnTime h s v.1.2 v.1.1 v.2) ((n₂, n₃), ρ) := by
  obtain ⟨hstar, hhstar, HH⟩ := exists_restartShearReturn_common_regular
  refine ⟨hstar, hhstar, ?_⟩
  intro h hh q D P hq hD hP
  obtain ⟨astar, hastar, HA⟩ := HH h hh q D P hq hD hP
  refine ⟨astar, hastar, ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ hmin ρ hρ s
  obtain ⟨hp, hg, hx, ht⟩ := HA a ha ε n₃ n₂ hε h₃ h₂ (by simpa only [min_comm] using hmin) ρ hρ
  have hswap : ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => ((v.1.2, v.1.1), v.2)) ((n₂, n₃), ρ) := by fun_prop
  exact ⟨ContDiffAt.comp (g := fun v : (ℝ × ℝ) × ℝ => restartShearReturnParameters h s v.1.1 v.1.2 v.2)
      (f := fun v : (ℝ × ℝ) × ℝ => ((v.1.2, v.1.1), v.2)) ((n₂, n₃), ρ) hp hswap,
    ContDiffAt.comp (g := fun v : (ℝ × ℝ) × ℝ => restartShearReturnState h s v.1.1 v.1.2 v.2)
      (f := fun v : (ℝ × ℝ) × ℝ => ((v.1.2, v.1.1), v.2)) ((n₂, n₃), ρ) hg hswap,
    ContDiffAt.comp (g := fun v : (ℝ × ℝ) × ℝ => restartShearReturnPhase h s v.1.1 v.1.2 v.2)
      (f := fun v : (ℝ × ℝ) × ℝ => ((v.1.2, v.1.1), v.2)) ((n₂, n₃), ρ) hx hswap,
    ContDiffAt.comp (g := fun v : (ℝ × ℝ) × ℝ => restartShearReturnTime h s v.1.1 v.1.2 v.2)
      (f := fun v : (ℝ × ℝ) × ℝ => ((v.1.2, v.1.1), v.2)) ((n₂, n₃), ρ) ht hswap⟩

end BianchiIX
