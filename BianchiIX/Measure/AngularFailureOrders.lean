import BianchiIX.Measure.AngularFailurePhysical
import BianchiIX.Measure.MainWallReflection
import BianchiIX.Dynamics.RestartReturnReflection

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

/-- The two weak-wall orderings share one exceptional set and one set of statistical parameters. -/
theorem exists_restartAngular_two_orders (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∃ hstar > (0 : ℝ),
          ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ L : ℝ, 0 ≤ L →
            ∀ q P : ℝ, 3 < q → 4 < P → ∃ astar > (0 : ℝ),
              ∀ a ∈ Ioc (0 : ℝ) astar,
                let s := q / 2 * Real.log (1 / a)
                let E := mainWallSymmetrization (restartAngularFailureSection h s a L P η J σ Bcap)
                let K := 12 * L * logarithmicFluxConstantOne (angularFailureFluxConstant L σ) σ
                MeasurableSet E ∧ mainWallMeasure h E ≤ ENNReal.ofReal (K * a * (1 + |Real.log a|)) ∧
                  mainWallMeasure h E ≠ ⊤ ∧
                  ∀ θ ζ : ℝ, |θ| ≤ L → (0 < ζ ∧ ζ ≤ a ^ P) → ∀ ρ ∈ Icc a (2 * a),
                    let y : SectionCoordinates := ![θ * ρ, -Real.log ρ, -Real.log ζ]
                    let T := restartReturnTime h s θ ζ ρ
                    y ∈ mainWallChartDomain h ∧ 0 < T ∧ T ∈ normalizedMaxDomain (mainWallChart h y) 0 ∧
                      ((y ∉ E ∨ mainWallReflection y ∉ E) →
                      ∃ p : eraSurvivorDomain η J σ Bcap,
                        p.val = (restartAmplitudeBudget L a ζ, restartReturnState h s θ ζ ρ) ∧
                        EraStatistics (EraSurvivor.digits p) (EraSurvivor.phase p) ∧
                        coreRadiusEntry p.val.2 = projectiveReflection (toProjectiveState
                          (normalizedMaxCurve (mainWallChart h y) 0 T)) ∧
                        coreRadiusEntry p.val.2 = toProjectiveState
                          (normalizedMaxCurve (mainWallChart h (mainWallReflection y)) 0 T)) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_restartAngular_physical_failure hBirkhoff
  obtain ⟨hO, hhO, HO⟩ := exists_restartReturn_reflected_orbit
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bcap, hcap, hcapone, hS, hhS, HS⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  refine ⟨Bcap, hcap, hcapone, min hS hO, lt_min hhS hhO, ?_⟩
  intro h hh L hL q P hq hP
  obtain ⟨aS, haS, HaS⟩ := HS h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ L hL q P hq hP
  obtain ⟨aO, haO, HaO⟩ := HO h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ L hL q P hq hP
  refine ⟨min aS aO, lt_min haS haO, ?_⟩
  intro a ha s E K
  obtain ⟨hF, hbound, _, Hgood⟩ := HaS a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩
  have HE : mainWallMeasure h E ≤ ENNReal.ofReal (K * a * (1 + |Real.log a|)) := calc
    _ ≤ _ := mainWallMeasure_symmetrization_le hF
    _ ≤ 2 * ENNReal.ofReal ((6 * L * logarithmicFluxConstantOne (angularFailureFluxConstant L σ) σ) * a * (1 + |Real.log a|)) :=
      mul_le_mul' le_rfl hbound
    _ = _ := by
      rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      dsimp only [K]
      ring
  refine ⟨measurableSet_mainWallSymmetrization hF, HE, ne_top_of_le_ne_top ENNReal.ofReal_ne_top HE, ?_⟩
  intro θ ζ hθ hζ ρ hρ y T
  obtain ⟨hy, ht, hdom, ho, hos⟩ := HaO a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ θ ζ hθ hζ ρ hρ
  refine ⟨hy, ht, hdom, ?_⟩
  intro H
  have hn : y ∉ E := H.elim id (fun hs hy => hs (mainWallReflection_mem_symmetrization_iff.mpr hy))
  obtain ⟨p, hp, hstat⟩ := Hgood θ ζ hθ hζ ρ hρ (fun hbad => hn (Or.inl hbad))
  exact ⟨p, hp, hstat, by simpa only [hp] using ho, by simpa only [hp] using hos⟩

end BianchiIX
