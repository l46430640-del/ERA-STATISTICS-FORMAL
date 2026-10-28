import BianchiIX.Measure.ShearFailureFamily
import BianchiIX.Measure.ShearFailureLayer
import BianchiIX.Statistics.ShearRestartCommonStatistics

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

def restartShearFailureFibers (h s a η : ℝ) (J : ℕ) (σ Bcap : ℝ) : ℝ × ℝ → Set ℝ :=
  fun z => eraRadialFailure η J σ (restartShearAmplitudeBudget a z.1 z.2) Bcap a (2 * a)
    (restartShearReturnState h s z.1 z.2)

def restartShearCommonFailureSection (h s a ε P η : ℝ) (J : ℕ) (σ Bcap : ℝ) : Set SectionCoordinates :=
  shearLabelFailureSection a (restartShearCommonLabelSet ε a P) (restartShearFailureFibers h s a η J σ Bcap)

def restartShearCommonFailureLayer (h s a ε P η : ℝ) (J : ℕ) (σ Bcap : ℝ) : ℝ≥0∞ :=
  shearLabelFailureLayer h a (restartShearCommonLabelSet ε a P) (restartShearFailureFibers h s a η J σ Bcap)

theorem mem_restartShearCommonFailureSection_iff {h s a ε P η σ Bcap n₂ n₃ ρ : ℝ} {J : ℕ}
    (ha : 0 < a) (hε : ε ≤ 1 / 128) (hl : (n₂, n₃) ∈ restartShearCommonLabelSet ε a P) :
    ![ρ, -Real.log n₂, -Real.log n₃] ∈ restartShearCommonFailureSection h s a ε P η J σ Bcap ↔
      ρ ∈ restartShearFailureFibers h s a η J σ Bcap (n₂, n₃) := by
  have hs : 2 * ε < 1 := by linarith only [hε]
  exact mem_shearLabelFailureSection_iff ha
    ⟨hl.1.1, hl.1.2.trans_lt (mul_lt_of_lt_one_left ha hs)⟩
    ⟨hl.2.1.1, hl.2.1.2.trans_lt (mul_lt_of_lt_one_left ha hs)⟩ hl

/-- One Borel physical failure set covers both positive-wall orderings, with finite corrected flux and actual return statistics. -/
theorem exists_restartShear_common_physical_failure (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∃ hstar > (0 : ℝ),
          ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
            ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
              ∀ ε : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 128) →
              let s := q / 2 * Real.log (1 / a)
              let E := restartShearCommonFailureSection h s a ε P η J σ Bcap
              let K := 3 * logarithmicFluxConstant (shearFailureFluxConstant σ) σ
              MeasurableSet E ∧ mainWallMeasure h E = restartShearCommonFailureLayer h s a ε P η J σ Bcap ∧
                mainWallMeasure h E ≤ ENNReal.ofReal (K * a * (1 + |Real.log a|) ^ 2) ∧
                mainWallMeasure h E ≠ ⊤ ∧
                ∀ n₂ n₃ : ℝ, (n₂, n₃) ∈ restartShearCommonLabelSet ε a P →
                  ∀ ρ ∈ Icc a (2 * a), ![ρ, -Real.log n₂, -Real.log n₃] ∉ E →
                    ∃ p : eraSurvivorDomain η J σ Bcap,
                      p.val = (restartShearAmplitudeBudget a n₂ n₃, restartShearReturnState h s n₂ n₃ ρ) ∧
                      EraStatistics (EraSurvivor.digits p) (EraSurvivor.phase p) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_restartShear_common_era_statistics hBirkhoff
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bcap, hcap, hcapone, hS, hhS, HS⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  refine ⟨Bcap, hcap, hcapone, min hS (1 / 8), lt_min hhS (by norm_num), ?_⟩
  intro h hh q D P hq hD hP
  have hh1 : h ≤ 1 / 8 := hh.2.trans (min_le_right _ _)
  obtain ⟨aS, haS, HaS⟩ := HS h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq hD hP
  refine ⟨min aS (min (h / 8) 1), lt_min haS (lt_min (div_pos hh.1 (by norm_num)) zero_lt_one), ?_⟩
  intro a ha ε hε s E K
  have hah : a ≤ h / 8 := ha.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have ha1 : a ≤ 1 := ha.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hε64 : 0 ≤ ε ∧ ε ≤ 1 / 64 := ⟨hε.1, hε.2.trans (by norm_num)⟩
  obtain ⟨hjoint, Hstats⟩ := HaS a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε hε
  let L := restartShearCommonLabelSet ε a P
  let F := restartShearFailureFibers h s a η J σ Bcap
  have hFI : ∀ z ∈ L, F z ⊆ Icc a (2 * a) := fun _ _ _ hρ => hρ.1
  have hA := measurableSet_shearLabelFailureCoordinates
    (measurableSet_restartShearCommonLabelSet ε a P) hFI hjoint
  have heq : mainWallMeasure h E = restartShearCommonFailureLayer h s a ε P η J σ Bcap := by
    apply mainWallMeasure_shearLabelFailureSection ha.1 hA
    intro z hz
    have hl := hz.2.2.1
    exact (restartShear_small_section hh.1 hh1 ha.1 hah hε64
      ⟨hl.1.1.le, hl.1.2⟩ ⟨hl.2.1.1.le, hl.2.1.2⟩ (hFI _ hl hz.2.2.2)).1
  have Hslice (n₂ n₃ : ℝ) (hl : (n₂, n₃) ∈ L) :
      restartShearRadialFlux h n₂ n₃ (F (n₂, n₃)) ≤
        ENNReal.ofReal (3 * min a (640 * Real.sqrt 3 * (restartShearAmplitudeBudget a n₂ n₃) ^ σ)) := by
    obtain ⟨hB, hF, Hloss, _⟩ := Hstats n₂ n₃ hl.1 hl.2.1 hl.2.2
    have H := (Hloss (F (n₂, n₃)) hF (hFI _ hl)
      (fun ρ => ENNReal.ofReal (restartShearFluxDensity h n₂ n₃ ρ)) 3 (by norm_num)
      (fun ρ hρ => ENNReal.ofReal_le_ofReal
        (restartShearFluxDensity_bounds hh.1 hh1 ha.1 hah hε64
          ⟨hl.1.1.le, hl.1.2⟩ ⟨hl.2.1.1.le, hl.2.1.2⟩ (hFI _ hl hρ)).2)).trans (min_le_right _ _)
    change (∫⁻ ρ in F (n₂, n₃) ∩ F (n₂, n₃), _) ≤ _ at H
    rw [inter_self] at H
    by_cases hm : a ≤ 640 * Real.sqrt 3 * (restartShearAmplitudeBudget a n₂ n₃) ^ σ
    · rw [min_eq_left hm]
      exact restartShearRadialFlux_le hh.1 hh1 ha.1 hah hε64
        ⟨hl.1.1.le, hl.1.2⟩ ⟨hl.2.1.1.le, hl.2.1.2⟩ (hFI _ hl)
    · rw [min_eq_right (le_of_not_ge hm)]
      refine H.trans (ENNReal.ofReal_le_ofReal ?_)
      nlinarith only [mul_nonneg (Real.sqrt_nonneg (3 : ℝ)) (Real.rpow_nonneg hB.1.le σ)]
  have Hlayer : restartShearCommonFailureLayer h s a ε P η J σ Bcap ≤
      3 * logarithmicLayerCost a (shearFailureFluxConstant σ) σ := by
    apply shearLabelFailureLayer_le
    intro x hx y hy hl
    simpa only [restartShearAmplitudeBudget_normalized ha.1 hx.1.le hy.1.le] using Hslice (a * x) (a * y) hl
  have Hbound : mainWallMeasure h E ≤ ENNReal.ofReal (K * a * (1 + |Real.log a|) ^ 2) := calc
    _ = _ := heq
    _ ≤ _ := Hlayer
    _ ≤ 3 * ENNReal.ofReal (logarithmicFluxConstant (shearFailureFluxConstant σ) σ * a * (1 + |Real.log a|) ^ 2) :=
      mul_le_mul' le_rfl (logarithmicLayerCost_le ha.1 ha1 (shearFailureFluxConstant_ge_one hσ.le) hσ)
    _ = _ := by
      rw [show (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      dsimp only [K]
      ring
  refine ⟨measurableSet_shearLabelFailureSection ha.1 hA, heq, Hbound,
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top Hbound, ?_⟩
  intro n₂ n₃ hl ρ hρ hn
  exact (Hstats n₂ n₃ hl.1 hl.2.1 hl.2.2).2.2.2 ρ hρ
    (fun hbad => hn ((mem_restartShearCommonFailureSection_iff ha.1 hε.2 hl).mpr hbad))

end BianchiIX
