import BianchiIX.Measure.AngularFailureVolume

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

/-- The actual bounded-angle restart has a Borel physical failure set with linear-logarithmic flux and statistics outside it. -/
theorem exists_restartAngular_physical_failure (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∃ hstar > (0 : ℝ),
          ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ L : ℝ, 0 ≤ L →
            ∀ q P : ℝ, 3 < q → 4 < P → ∃ astar > (0 : ℝ),
              ∀ a ∈ Ioc (0 : ℝ) astar,
                let s := q / 2 * Real.log (1 / a)
                let E := restartAngularFailureSection h s a L P η J σ Bcap
                let K := 6 * L * logarithmicFluxConstantOne (angularFailureFluxConstant L σ) σ
                MeasurableSet E ∧ mainWallMeasure h E ≤ ENNReal.ofReal (K * a * (1 + |Real.log a|)) ∧
                  mainWallMeasure h E ≠ ⊤ ∧
                  ∀ θ ζ : ℝ, |θ| ≤ L → (0 < ζ ∧ ζ ≤ a ^ P) →
                    ∀ ρ ∈ Icc a (2 * a), ![θ * ρ, -Real.log ρ, -Real.log ζ] ∉ E →
                      ∃ p : eraSurvivorDomain η J σ Bcap,
                        p.val = (restartAmplitudeBudget L a ζ, restartReturnState h s θ ζ ρ) ∧
                        EraStatistics (EraSurvivor.digits p) (EraSurvivor.phase p) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_restart_era_statistics hBirkhoff
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bcap, hcap, hcapone, hS, hhS, HS⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  refine ⟨Bcap, hcap, hcapone, min hS (1 / 8), lt_min hhS (by norm_num), ?_⟩
  intro h hh L hL q P hq hP
  have hh1 : h ≤ 1 / 8 := hh.2.trans (min_le_right _ _)
  obtain ⟨aS, haS, HaS⟩ := HS h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ L hL q P hq hP
  refine ⟨min aS (min (h / 16) (1 / (16 * (L + 1)))),
    lt_min haS (lt_min (div_pos hh.1 (by norm_num)) (by positivity)), ?_⟩
  intro a ha s E K
  have hah : a ≤ h / 16 := ha.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have ha1 : a ≤ 1 := by linarith only [hah, hh1]
  have hLa : 2 * L * a ≤ 1 / 8 := by
    have H := (le_div_iff₀ (by positivity : 0 < 16 * (L + 1))).mp
      (ha.2.trans ((min_le_right _ _).trans (min_le_right _ _)))
    nlinarith only [H, ha.1]
  obtain ⟨hjoint, Hstats⟩ := HaS a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩
  have hA := measurableSet_restartAngularFailureCoordinates hjoint
  have Hslice (θ ζ : ℝ) (hl : (θ, ζ) ∈ restartLabelSet L a P) :
      volume (eraRadialFailure η J σ (restartAmplitudeBudget L a ζ) Bcap a (2 * a)
        (restartReturnState h s θ ζ)) ≤ ENNReal.ofReal (min a (640 * Real.sqrt 3 * (restartAmplitudeBudget L a ζ) ^ σ)) := by
    let F := eraRadialFailure η J σ (restartAmplitudeBudget L a ζ) Bcap a (2 * a) (restartReturnState h s θ ζ)
    have hFI : F ⊆ Icc a (2 * a) := fun _ hρ => hρ.1
    have H := (Hstats θ ζ hl.1 hl.2).2.2.1 (Icc a (2 * a)) measurableSet_Icc (Subset.refl _)
      (fun _ => (1 : ℝ≥0∞)) 1 (by norm_num) (by intros; norm_num)
    change (∫⁻ _ in Icc a (2 * a) ∩ F, (1 : ℝ≥0∞)) ≤ _ at H
    rw [inter_eq_right.mpr hFI] at H
    simpa only [lintegral_one, Measure.restrict_apply_univ, Real.volume_Icc,
      show 2 * a - a = a by ring, mul_one, ← ENNReal.ofReal_min] using H
  have Hbound : mainWallMeasure h E ≤ ENNReal.ofReal (K * a * (1 + |Real.log a|)) := calc
    _ ≤ _ := mainWallMeasure_restartAngularFailureSection_le_volume hh.1 hh1 ha.1 hah hL hLa hA
    _ ≤ ENNReal.ofReal (3 : ℝ) *
        (ENNReal.ofReal (2 * L) * logarithmicLayerCostOne a (angularFailureFluxConstant L σ) σ) :=
      mul_le_mul' le_rfl (volume_restartAngularFailureSection_le ha.1 hL hA Hslice)
    _ ≤ ENNReal.ofReal (3 : ℝ) * (ENNReal.ofReal (2 * L) * ENNReal.ofReal
        (logarithmicFluxConstantOne (angularFailureFluxConstant L σ) σ * a * (1 + |Real.log a|))) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl (logarithmicLayerCostOne_le ha.1 ha1
        (angularFailureFluxConstant_ge_one hL hσ.le) hσ))
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * L), ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      dsimp only [K]
      ring
  refine ⟨measurableSet_restartAngularFailureSection ha.1 hA, Hbound,
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top Hbound, ?_⟩
  intro θ ζ hθ hζ ρ hρ hn
  have hζa : ζ < 2 * a := (hζ.2.trans (Real.rpow_le_self_of_le_one ha.1.le ha1 (by linarith))).trans_lt (by linarith only [ha.1])
  exact (Hstats θ ζ hθ hζ).2.2.2 ρ hρ (fun hbad => hn
    ((mem_restartAngularFailureSection_iff ha.1 hθ ⟨hζ.1, hζa⟩ hζ.2 (ha.1.trans_le hρ.1)).mpr hbad))

end BianchiIX
