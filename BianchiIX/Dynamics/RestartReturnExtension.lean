import BianchiIX.Dynamics.RestartReturnCone
import BianchiIX.Analysis.RadiusAmplitudeExtension

noncomputable section

namespace BianchiIX

open Set

def restartAmplitudeExtension (h s θ ζ r : ℝ) (i : Fin 3) : ℝ → ℝ :=
  radiusAmplitudeExtension (fun a => restartReturnState h s θ ζ a 0)
    (fun a => restartReturnState h s θ ζ a i) r (2 * r)

/-- The actual restart admits a global C1 root-amplitude extension with one uniform amplitude bound. -/
theorem exists_restartReturn_extension :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∀ q P : ℝ, 3 < q → 4 < P →
        ∃ rstar : ℝ, 0 < rstar ∧ ∀ r ∈ Ioc (0 : ℝ) rstar,
          ∀ θ ζ : ℝ, |θ| ≤ L → (0 < ζ ∧ ζ ≤ r ^ P) →
            let s := q / 2 * Real.log (1 / r)
            let G := restartReturnState h s θ ζ
            let u := restartAmplitudeExtension h s θ ζ r 1
            let w := restartAmplitudeExtension h s θ ζ r 2
            ContDiff ℝ 1 u ∧ ContDiff ℝ 1 w ∧
              (∀ ρ ∈ Icc r (2 * r), u (G ρ 0) = G ρ 1 ∧ w (G ρ 0) = G ρ 2 ∧
                deriv u (G ρ 0) = deriv (fun a => G a 1) ρ / deriv (fun a => G a 0) ρ ∧
                deriv w (G ρ 0) = deriv (fun a => G a 2) ρ / deriv (fun a => G a 0) ρ) ∧
              ∀ k : ℝ, 0 < u k ∧ 0 < w k ∧
                u k + w k ≤ 6400 * (8 * (L + 1)) * ζ / r ^ 3 ∧
                |deriv u k| ≤ Real.sqrt (u k) ∧ |deriv w k| ≤ Real.sqrt (w k) := by
  obtain ⟨hstar, hhstar, HH⟩ := exists_restartReturn_cone
  refine ⟨hstar, hhstar, ?_⟩
  intro h hh L hL q P hq hP
  obtain ⟨rstar, hrstar, HR⟩ := HH h hh L hL q P hq hP
  refine ⟨rstar, hrstar, ?_⟩
  intro r hr θ ζ hθ hζ
  let s := q / 2 * Real.log (1 / r)
  let G := restartReturnState h s θ ζ
  have H (ρ : ℝ) (hρ : ρ ∈ Icc r (2 * r)) := HR r hr θ ζ hθ hζ ρ hρ
  have hG (ρ : ℝ) (hρ : ρ ∈ Icc r (2 * r)) (i : Fin 3) :
      ContDiffAt ℝ 1 (fun a => G a i) ρ := (contDiffAt_pi.mp (H ρ hρ).1 i).of_le (by norm_num)
  have hab : r < 2 * r := by linarith only [hr.1]
  obtain ⟨hcu, hcw, hmatch, hbound⟩ := radiusAmplitudeExtension_pair hab
    (fun ρ hρ => hG ρ hρ 0) (fun ρ hρ => (H ρ hρ).2.2.2.2.1)
    (fun ρ hρ => hG ρ hρ 1) (fun ρ hρ => hG ρ hρ 2)
    (fun ρ hρ => (H ρ hρ).2.1) (fun ρ hρ => (H ρ hρ).2.2.1)
    (fun ρ hρ => (H ρ hρ).2.2.2.2.2.1) (fun ρ hρ => (H ρ hρ).2.2.2.2.2.2)
    (fun ρ hρ => (H ρ hρ).2.2.2.1)
  refine ⟨hcu, hcw, hmatch, ?_⟩
  intro k
  obtain ⟨hu, hw, hsum, hdu, hdw⟩ := hbound k
  exact ⟨hu, hw, hsum.trans_eq (by ring), hdu, hdw⟩

end BianchiIX
