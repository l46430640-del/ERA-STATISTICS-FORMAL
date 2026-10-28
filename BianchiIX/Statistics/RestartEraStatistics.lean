import BianchiIX.Statistics.EraRadialStatistics
import BianchiIX.Dynamics.RestartStatisticalPreparation

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

/-- The fixed actual restart has a jointly Borel failure set and the weighted radial statistical bound. -/
theorem exists_restart_era_statistics (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∃ hstar > (0 : ℝ),
          ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ L : ℝ, 0 ≤ L →
            ∀ q P : ℝ, 3 < q → 4 < P → ∃ rstar > (0 : ℝ),
              ∀ r ∈ Ioc (0 : ℝ) rstar,
                let s := q / 2 * Real.log (1 / r)
                MeasurableSet {p : restartLabelSet L r P × Icc r (2 * r) |
                  (p.2 : ℝ) ∈ eraRadialFailure η J σ (restartAmplitudeBudget L r p.1.val.2) Bcap r (2 * r)
                    (restartReturnState h s p.1.val.1 p.1.val.2)} ∧
                ∀ θ ζ : ℝ, |θ| ≤ L → (0 < ζ ∧ ζ ≤ r ^ P) →
                  let B := restartAmplitudeBudget L r ζ
                  let Y := restartReturnState h s θ ζ
                  let F := eraRadialFailure η J σ B Bcap r (2 * r) Y
                  B ∈ Ioc 0 Bcap ∧ MeasurableSet F ∧
                    (∀ A : Set ℝ, MeasurableSet A → A ⊆ Icc r (2 * r) →
                      ∀ (ω : ℝ → ℝ≥0∞) (M : ℝ), 0 ≤ M → (∀ ρ ∈ A, ω ρ ≤ ENNReal.ofReal M) →
                        (∫⁻ ρ in A ∩ F, ω ρ) ≤ min (∫⁻ ρ in A, ω ρ)
                          (ENNReal.ofReal (640 * Real.sqrt 3 * M * B ^ σ))) ∧
                    ∀ ρ ∈ Icc r (2 * r), ρ ∉ F →
                      ∃ p : eraSurvivorDomain η J σ Bcap, p.val = (B, Y ρ) ∧
                        EraStatistics (EraSurvivor.digits p) (EraSurvivor.phase p) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_era_joint_statistics hBirkhoff
  obtain ⟨hstar, hhstar, HP⟩ := exists_restart_statistical_preparation
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bcap, hcap, hcapone, htyp, Bs, hBs, hBscap, Hstats⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  refine ⟨Bcap, hcap, hcapone, hstar, hhstar, ?_⟩
  intro h hh L hL q P hq hP
  obtain ⟨rstar, hrstar, HR⟩ := HP h hh L hL q P hq hP Bs hBs
  refine ⟨rstar, hrstar, ?_⟩
  intro r hr s
  obtain ⟨hY, Hcurve⟩ := HR r hr
  refine ⟨?_, ?_⟩
  · have hbad := htyp.compl.preimage hY
    convert! hbad using 1
    ext p
    change ((p.2 : ℝ) ∈ Icc r (2 * r) ∧
      (restartAmplitudeBudget L r p.1.val.2, restartReturnState h s p.1.val.1 p.1.val.2 p.2) ∉
        EraSurvivor.typicalDomain η J σ Bcap) ↔ _
    exact and_iff_right p.2.property
  · intro θ ζ hθ hζ B Y F
    obtain ⟨hB, hΓ, Hradial⟩ := Hcurve θ ζ hθ hζ
    let Γ := restartEraCurve h s θ ζ r
    let f := restartReturnPhase h s θ ζ
    obtain ⟨hG, _, Hloss, Hgood⟩ := Hstats B hB Γ hΓ
    have hloss : volume (Ioo 0 1 \ EraSurvivor.curveTypicalSet Γ η J σ B Bcap) ≤ ENNReal.ofReal (80 * B ^ σ) := by
      simpa only [univ_inter] using (Hloss univ).trans (min_le_right _ _)
    have Hfail := era_radial_failure_weighted (Γ := Γ) (Y := Y) (f := f)
      (by positivity : 0 < 1 / (8 * Real.sqrt (3 : ℝ)))
      (fun ρ hρ => (Hradial ρ hρ).2.1) (fun ρ hρ => (Hradial ρ hρ).2.2.1)
      (fun ρ hρ => (Hradial ρ hρ).1) (fun ρ hρ => (Hradial ρ hρ).2.2.2) hG hloss
    refine ⟨⟨hB.1, hB.2.trans hBscap⟩, Hfail.1, ?_, ?_⟩
    · intro A hA hAI ω M hM hω
      have H := Hfail.2 A hA hAI ω M hM hω
      have hcoef : ENNReal.ofReal (M / (1 / (8 * Real.sqrt 3))) * ENNReal.ofReal (80 * B ^ σ) =
          ENNReal.ofReal (640 * Real.sqrt 3 * M * B ^ σ) := by
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ M / (1 / (8 * Real.sqrt 3)))]
        congr 1
        simp only [one_div, div_inv_eq_mul]
        ring
      simpa only [hcoef] using H
    · intro ρ hρ hnot
      have hgood : (B, Y ρ) ∈ EraSurvivor.typicalDomain η J σ Bcap := by
        by_contra hn
        exact hnot ⟨hρ, hn⟩
      have hfgood : f ρ ∈ EraSurvivor.curveTypicalSet Γ η J σ B Bcap :=
        (era_radial_good_iff (Hradial ρ hρ).1 (Hradial ρ hρ).2.2.2).mpr hgood
      obtain ⟨p, hp, hstat⟩ := Hgood (f ρ) hfgood
      exact ⟨p, hp.trans (congrArg (fun Z => (B, Z)) (Hradial ρ hρ).2.2.2), hstat⟩

end BianchiIX
