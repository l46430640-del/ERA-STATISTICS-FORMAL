import BianchiIX.Dynamics.ShearRestartAllActiveOutputAmplitude
import BianchiIX.Dynamics.ShearRestartAllActiveReturn
import BianchiIX.Analysis.RadiusAmplitudeExtension

noncomputable section

namespace BianchiIX

open Set

def restartShearAmplitudeExtension (h s n₂ n₃ a : ℝ) (i : Fin 3) : ℝ → ℝ :=
  radiusAmplitudeExtension (fun r => restartShearReturnState h s n₂ n₃ r 0)
    (fun r => restartShearReturnState h s n₂ n₃ r i) a (2 * a)

/-- The whole positive-wall shear return has a global C1 radius-parametrized extension with the same product amplitude scale. -/
theorem exists_restartShearReturn_extension :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
        ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
          (0 < n₂ ∧ n₂ ≤ 2 * ε * a) → (0 < n₃ ∧ n₃ ≤ 2 * ε * a) → n₃ ≤ a ^ P →
            let s := q / 2 * Real.log (1 / a)
            let G := restartShearReturnState h s n₂ n₃
            let u := restartShearAmplitudeExtension h s n₂ n₃ a 1
            let w := restartShearAmplitudeExtension h s n₂ n₃ a 2
            ContDiff ℝ 1 u ∧ ContDiff ℝ 1 w ∧
              (∀ ρ ∈ Icc a (2 * a), u (G ρ 0) = G ρ 1 ∧ w (G ρ 0) = G ρ 2 ∧
                deriv u (G ρ 0) = deriv (fun r => G r 1) ρ / deriv (fun r => G r 0) ρ ∧
                deriv w (G ρ 0) = deriv (fun r => G r 2) ρ / deriv (fun r => G r 0) ρ) ∧
              ∀ k : ℝ, 0 < u k ∧ 0 < w k ∧ u k + w k ≤ 800 * n₂ * n₃ / a ^ 4 ∧
                |deriv u k| ≤ Real.sqrt (u k) ∧ |deriv w k| ≤ Real.sqrt (w k) := by
  obtain ⟨hA, hhA, HA⟩ := exists_restartShearReturn_all_active_output_bounds
  obtain ⟨hC, hhC, HC⟩ := exists_restartShearReturn_all_active_cone
  refine ⟨min hA hC, lt_min hhA hhC, ?_⟩
  intro h hh q P hq hP
  obtain ⟨aA, haA, HaA⟩ := HA h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q P hq hP
  obtain ⟨aC, haC, HaC⟩ := HC h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q P hq hP
  refine ⟨min aA aC, lt_min haA haC, ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P s G u w
  have HA' (ρ : ℝ) (hρ : ρ ∈ Icc a (2 * a)) :=
    HaA a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ
  have HC' (ρ : ℝ) (hρ : ρ ∈ Icc a (2 * a)) :=
    HaC a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ
  have hG (ρ : ℝ) (hρ : ρ ∈ Icc a (2 * a)) (i : Fin 3) :
      ContDiffAt ℝ 1 (fun r => G r i) ρ := (contDiffAt_pi.mp (HC' ρ hρ).1 i).of_le (by norm_num)
  have hab : a < 2 * a := by linarith only [ha.1]
  obtain ⟨hcu, hcw, hmatch, hbound⟩ := radiusAmplitudeExtension_pair hab
    (fun ρ hρ => hG ρ hρ 0) (fun ρ hρ => (HC' ρ hρ).2.1)
    (fun ρ hρ => hG ρ hρ 1) (fun ρ hρ => hG ρ hρ 2)
    (fun ρ hρ => (HA' ρ hρ).2.2.2.2.1) (fun ρ hρ => (HA' ρ hρ).2.2.2.2.2.1)
    (fun ρ hρ => (HC' ρ hρ).2.2.1 0) (fun ρ hρ => (HC' ρ hρ).2.2.1 1)
    (fun ρ hρ => (HA' ρ hρ).2.2.2.2.2.2.1)
  refine ⟨hcu, hcw, hmatch, ?_⟩
  intro k
  obtain ⟨hu, hw, hsum, hdu, hdw⟩ := hbound k
  exact ⟨hu, hw, hsum.trans_eq (by ring), hdu, hdw⟩

end BianchiIX
