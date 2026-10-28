import BianchiIX.Measure.ShearCommonFailurePhysical
import BianchiIX.Measure.MainWallReflection

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

theorem mem_restartShearCommonLabelSet_swap {ε a P n₂ n₃ : ℝ}
    (hl : (n₂, n₃) ∈ restartShearCommonLabelSet ε a P) :
    (n₃, n₂) ∈ restartShearCommonLabelSet ε a P :=
  ⟨hl.2.1, hl.1, by simpa only [min_comm] using hl.2.2⟩

theorem restartShearAmplitudeBudget_swap (a n₂ n₃ : ℝ) :
    restartShearAmplitudeBudget a n₃ n₂ = restartShearAmplitudeBudget a n₂ n₃ := by
  unfold restartShearAmplitudeBudget
  ring

/-- Axis exchange combines both shear signs without changing the statistical cap or product budget. -/
theorem exists_restartShear_signed_physical_failure (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∃ hstar > (0 : ℝ),
          ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
            ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
              ∀ ε : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 128) →
              let s := q / 2 * Real.log (1 / a)
              let E := mainWallSymmetrization (restartShearCommonFailureSection h s a ε P η J σ Bcap)
              let K := 6 * logarithmicFluxConstant (shearFailureFluxConstant σ) σ
              MeasurableSet E ∧ mainWallMeasure h E ≤ ENNReal.ofReal (K * a * (1 + |Real.log a|) ^ 2) ∧
                mainWallMeasure h E ≠ ⊤ ∧
                ∀ τ : ℝ, (τ = 1 ∨ τ = -1) →
                  ∀ n₂ n₃ : ℝ, (n₂, n₃) ∈ restartShearCommonLabelSet ε a P →
                    ∀ ρ ∈ Icc a (2 * a), ![τ * ρ, -Real.log n₂, -Real.log n₃] ∉ E →
                      let z := if τ = 1 then (n₂, n₃) else (n₃, n₂)
                      ∃ p : eraSurvivorDomain η J σ Bcap,
                        p.val = (restartShearAmplitudeBudget a n₂ n₃, restartShearReturnState h s z.1 z.2 ρ) ∧
                        EraStatistics (EraSurvivor.digits p) (EraSurvivor.phase p) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_restartShear_common_physical_failure hBirkhoff
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bcap, hcap, hcapone, hstar, hhstar, HH⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  refine ⟨Bcap, hcap, hcapone, hstar, hhstar, ?_⟩
  intro h hh q D P hq hD hP
  obtain ⟨astar, hastar, Ha⟩ := HH h hh q D P hq hD hP
  refine ⟨astar, hastar, ?_⟩
  intro a ha ε hε s E K
  obtain ⟨hE, _, Hbound, _, Hgood⟩ := Ha a ha ε hε
  have Hsigned : mainWallMeasure h E ≤ ENNReal.ofReal (K * a * (1 + |Real.log a|) ^ 2) := calc
    _ ≤ _ := mainWallMeasure_symmetrization_le hE
    _ ≤ 2 * ENNReal.ofReal
        (3 * logarithmicFluxConstant (shearFailureFluxConstant σ) σ * a * (1 + |Real.log a|) ^ 2) :=
      mul_le_mul' le_rfl Hbound
    _ = _ := by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      dsimp only [K]
      ring
  refine ⟨measurableSet_mainWallSymmetrization hE, Hsigned,
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top Hsigned, ?_⟩
  intro τ hτ n₂ n₃ hl ρ hρ hn
  rcases hτ with rfl | rfl
  · have hn' : ![ρ, -Real.log n₂, -Real.log n₃] ∉
        restartShearCommonFailureSection h s a ε P η J σ Bcap := by
      intro hbad
      apply hn
      rw [one_mul]
      exact Or.inl hbad
    simpa only [if_pos rfl, ite_true] using Hgood n₂ n₃ hl ρ hρ hn'
  · have hn' : ![ρ, -Real.log n₃, -Real.log n₂] ∉
        restartShearCommonFailureSection h s a ε P η J σ Bcap := by
      intro hbad
      apply hn
      have H : mainWallReflection ![ρ, -Real.log n₃, -Real.log n₂] ∈ E := Or.inr ⟨_, hbad, rfl⟩
      change ![-ρ, -Real.log n₂, -Real.log n₃] ∈ E at H
      simpa only [neg_one_mul] using H
    obtain ⟨p, hp, hstat⟩ := Hgood n₃ n₂ (mem_restartShearCommonLabelSet_swap hl) ρ hρ hn'
    refine ⟨p, ?_, hstat⟩
    simpa only [if_neg (by norm_num : (-1 : ℝ) ≠ 1), restartShearAmplitudeBudget_swap a n₂ n₃] using hp

end BianchiIX
