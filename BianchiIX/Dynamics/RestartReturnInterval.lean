import BianchiIX.Dynamics.RestartReturnControl
import BianchiIX.Analysis.RadialPhaseInterval
import BianchiIX.Measure.RadialPhasePullback

noncomputable section

namespace BianchiIX

open Set MeasureTheory

/-- The actual restart phase parametrizes an interval of comparable length and controls deletion. -/
theorem exists_restartReturn_interval :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∃ C : ℝ, 0 < C ∧ ∀ q P : ℝ, 3 < q → 4 < P →
        ∃ rstar : ℝ, 0 < rstar ∧ ∀ r ∈ Ioc (0 : ℝ) rstar,
          ∀ θ ζ : ℝ, |θ| ≤ L → (0 < ζ ∧ ζ ≤ r ^ P) →
            let s := q / 2 * Real.log (1 / r)
            let f := restartReturnPhase h s θ ζ
            StrictMonoOn f (Icc r (2 * r)) ∧ f '' Icc r (2 * r) = Icc (f r) (f (2 * r)) ∧
              r / (8 * Real.sqrt 3) ≤ f (2 * r) - f r ∧ f (2 * r) - f r ≤ C * r ∧
              ∀ A E : Set ℝ, MeasurableSet A → A ⊆ Icc r (2 * r) → f '' A ⊆ E →
                volume A ≤ min (ENNReal.ofReal r) (ENNReal.ofReal (8 * Real.sqrt 3) * volume E) := by
  obtain ⟨hstar, hhstar, HH⟩ := exists_restartReturn_control
  refine ⟨hstar, hhstar, ?_⟩
  intro h hh L hL
  obtain ⟨C, hC, HC⟩ := HH h hh L hL
  refine ⟨C, hC, ?_⟩
  intro q P hq hP
  obtain ⟨rstar, hrstar, HR⟩ := HC q P hq hP
  refine ⟨rstar, hrstar, ?_⟩
  intro r hr θ ζ hθ hζ
  let s := q / 2 * Real.log (1 / r)
  let f := restartReturnPhase h s θ ζ
  have hf (ρ : ℝ) (hρ : ρ ∈ Icc r (2 * r)) :
      DifferentiableAt ℝ f ρ ∧ 1 / (8 * Real.sqrt 3) ≤ deriv f ρ ∧ deriv f ρ ≤ C := by
    obtain ⟨_, _, _, _, _, _, _, _, _, hd, _, _, hlo, hhi⟩ := HR r hr θ ζ hθ hζ ρ hρ
    exact ⟨hd, hlo, hhi⟩
  have hc : 0 < 1 / (8 * Real.sqrt (3 : ℝ)) := by positivity
  have hab : r ≤ 2 * r := by linarith only [hr.1]
  have hlen : 2 * r - r = r := by ring
  obtain ⟨hmono, himage, H⟩ := radial_phase_interval hab hc (fun ρ hρ => (hf ρ hρ).1)
    (fun ρ hρ => (hf ρ hρ).2)
  have Hend := H r ⟨le_rfl, hab⟩ (2 * r) ⟨hab, le_rfl⟩ hab
  rw [hlen] at Hend
  refine ⟨hmono, himage, ?_, Hend.2, ?_⟩
  · exact (by ring : r / (8 * Real.sqrt 3) = (1 / (8 * Real.sqrt 3)) * r).trans_le Hend.1
  · intro A E hA hAI hE
    simpa only [hlen, one_div_one_div] using radial_phase_deleted_length hc
      (fun ρ hρ => (hf ρ hρ).1) (fun ρ hρ => (hf ρ hρ).2.1) hA hAI hE

end BianchiIX
