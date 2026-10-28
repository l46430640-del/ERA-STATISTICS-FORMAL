import BianchiIX.Dynamics.ShearRestartAllActivePhase
import BianchiIX.Analysis.RadialPhaseInterval
import BianchiIX.Measure.RadialPhasePullback

noncomputable section

namespace BianchiIX

open Set MeasureTheory

/-- Image length and deleted length are controlled on every radial subinterval,
including intervals crossing the active-wall boundary. -/
theorem exists_restartShearReturn_all_active_interval :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∃ C > (0 : ℝ), ∀ q P : ℝ, 3 < q → 4 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
          ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
            (0 < n₂ ∧ n₂ ≤ 2 * ε * a) → (0 < n₃ ∧ n₃ ≤ 2 * ε * a) → n₃ ≤ a ^ P →
            let s := q / 2 * Real.log (1 / a)
            let f := restartShearReturnPhase h s n₂ n₃
            ∀ b c : ℝ, a ≤ b → b ≤ c → c ≤ 2 * a →
              StrictMonoOn f (Icc b c) ∧ f '' Icc b c = Icc (f b) (f c) ∧
              (c - b) / (8 * Real.sqrt 3) ≤ f c - f b ∧ f c - f b ≤ C * (c - b) ∧
              ∀ A E : Set ℝ, MeasurableSet A → A ⊆ Icc b c → f '' A ⊆ E →
                volume A ≤ min (ENNReal.ofReal (c - b)) (ENNReal.ofReal (8 * Real.sqrt 3) * volume E) := by
  obtain ⟨hstar, hhstar, HH⟩ := exists_restartShearReturn_all_active_phase
  refine ⟨hstar, hhstar, ?_⟩
  intro h hh
  obtain ⟨C, hC, HC⟩ := HH h hh
  refine ⟨C, hC, ?_⟩
  intro q P hq hP
  obtain ⟨astar, hastar, Ha⟩ := HC q P hq hP
  refine ⟨astar, hastar, ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P s f b c hab hbc hca
  have hf (ρ : ℝ) (hρ : ρ ∈ Icc b c) :
      DifferentiableAt ℝ f ρ ∧ 1 / (8 * Real.sqrt 3) ≤ deriv f ρ ∧ deriv f ρ ≤ C := by
    obtain ⟨hd, _, _, hlo, hhi⟩ :=
      Ha a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ ⟨hab.trans hρ.1, hρ.2.trans hca⟩
    exact ⟨hd, hlo, hhi⟩
  have hc : 0 < 1 / (8 * Real.sqrt (3 : ℝ)) := by positivity
  obtain ⟨hmono, himage, H⟩ := radial_phase_interval hbc hc (fun ρ hρ => (hf ρ hρ).1)
    (fun ρ hρ => (hf ρ hρ).2)
  have Hend := H b ⟨le_rfl, hbc⟩ c ⟨hbc, le_rfl⟩ hbc
  refine ⟨hmono, himage, ?_, Hend.2, ?_⟩
  · exact (by ring : (c - b) / (8 * Real.sqrt 3) = (1 / (8 * Real.sqrt 3)) * (c - b)).trans_le Hend.1
  · intro A E hA hAI hE
    simpa only [one_div_one_div] using radial_phase_deleted_length hc
      (fun ρ hρ => (hf ρ hρ).1) (fun ρ hρ => (hf ρ hρ).2.1) hA hAI hE

end BianchiIX
