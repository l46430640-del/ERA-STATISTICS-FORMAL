import BianchiIX.Measure.CommonSuccessException
import BianchiIX.Measure.MainWallAxisCapture
import BianchiIX.Measure.AxisFamilyCoordinates

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

/-- The success target, null exception, and Borel first arrival are fixed before choosing any initial chart. -/
theorem exists_common_borel_first_success
    (hBirkhoff : Literature.BirkhoffErgodicInput ℝ)
    (hBrehm : Literature.BrehmIXAttractorInput) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∃ h > (0 : ℝ), h ≤ 1 / 16 ∧
          ∃ d > (0 : ℝ), d < h / 8 ∧
            let E := fun _ : Fin 3 => mainWallSmallSection d ∩ mainWallChartDomain h
            ∃ F : Set (Fin 3 × SectionCoordinates), MeasurableSet F ∧
              axisFamilyMeasure (fun _ : Fin 3 => h) F ≠ ⊤ ∧
              (∀ z ∈ axisFamilySection E \ F,
                StatisticalCoreFuture η J σ Bcap (axisFamilyChart primaryAxisFrame (fun _ => h) z)) ∧
              ∃ N : Set NormalizedState, MeasurableSet N ∧ N ⊆ physicalPhaseSpace ∧
                geometricException ⊆ N ∧
                (∀ x : NormalizedState, ∀ t ∈ normalizedMaxDomain x 0,
                  normalizedMaxCurve x 0 t ∈ N ↔ x ∈ N) ∧
                (∀ (C : SectionCoordinates → NormalizedState) (U : Set SectionCoordinates),
                  IsOpen U → (∀ y ∈ U, ContDiffAt ℝ 1 C y) →
                  (∀ y ∈ U, positiveWalls (C y)) → (∀ y ∈ U, stateConstraint (C y) = 1) →
                  (∀ y ∈ U, normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0) →
                  volume (U ∩ C ⁻¹' N) = 0) ∧ NullInFourCoordinates N ∧
                ∃ τ : NormalizedState → ℝ, ∃ Y : NormalizedState → NormalizedState,
                  ∃ Z : NormalizedState → Fin 3 × SectionCoordinates,
                  Measurable τ ∧ Measurable Y ∧ Measurable Z ∧
                  (∀ x, Y x = normalizedMaxCurve x 0 (τ x)) ∧
                  ∀ x ∈ physicalPhaseSpace, x ∉ N →
                    IsLeast (globalAxisWallHittingTimes primaryAxisFrame (fun _ => h)
                      (axisFamilySuccessTargets E F) (Ici 0) x) (τ x) ∧
                    Z x ∈ axisFamilySection E \ F ∧
                    axisFamilyChart primaryAxisFrame (fun _ => h) (Z x) = Y x ∧
                    StatisticalCoreFuture η J σ Bcap (Y x) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_mainWall_primaryAxis_capture hBirkhoff
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bcap, hcap, hcapone, hS, hhS, HS⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  let h := min hS (1 / 16) / 2
  have hh : 0 < h := div_pos (lt_min hhS (by norm_num)) (by norm_num)
  have hhle : h ≤ min hS (1 / 16) := (half_lt_self (lt_min hhS (by norm_num))).le
  have hhmax : h ≤ 1 / 16 := hhle.trans (min_le_right _ _)
  have hh1 : h ≤ 1 / 8 := hhmax.trans (by norm_num)
  obtain ⟨dS, hdS, C, hC, HdS⟩ := HS h ⟨hh, hhle.trans (min_le_left _ _)⟩
  let d := min dS (h / 8) / 2
  have hd : 0 < d := div_pos (lt_min hdS (div_pos hh (by norm_num))) (by norm_num)
  have hdlt : d < min dS (h / 8) := half_lt_self (lt_min hdS (div_pos hh (by norm_num)))
  have hdh : d < h / 8 := hdlt.trans_le (min_le_right _ _)
  have hd1 : d ≤ 1 / 8 := hdh.le.trans (by linarith only [hh1])
  obtain ⟨F, hBm, hFm, hinj, _, hfinite, hgood, _⟩ := HdS d ⟨hd, hdlt.le.trans (min_le_left _ _)⟩
  let E := fun _ : Fin 3 => mainWallSmallSection d ∩ mainWallChartDomain h
  have hsmall (i : Fin 3) (y : SectionCoordinates) (hy : y ∈ E i) :
      y ∈ mainWallChartDomain h ∧ |y 0| ≤ 1 / 8 ∧
        Real.exp (-y 1) ≤ h / 8 ∧ Real.exp (-y 2) ≤ h / 8 :=
    ⟨hy.2, hy.1.1.trans hd1, (le_max_left _ _).trans (hy.1.2.trans hdh.le),
      (le_max_right _ _).trans (hy.1.2.trans hdh.le)⟩
  obtain ⟨N, hNm, hNp, hNg, hNi, hNn, hNfour, hhit⟩ :=
    exists_common_borel_success_exception hBirkhoff hBrehm hh hhmax hd hdh hFm hfinite
  obtain ⟨τ, Y, hτ, hY, hflow, hfirst, _⟩ :=
    exists_smallAxis_borel_first_success hh hh1 (fun _ => hBm) hsmall hFm hfinite
  obtain ⟨c, hcm, hcinv⟩ := exists_measurable_primaryAxis_coordinates (fun _ => hBm) hinj
  let Z := c ∘ Y
  refine ⟨Bcap, hcap, hcapone, h, hh, hhmax, d, hd, hdh, F, hFm, hfinite, hgood,
    N, hNm, hNp, hNg, hNi, hNn, hNfour, τ, Y, Z, hτ, hY, hcm.comp hY, hflow, ?_⟩
  intro x hx hn
  obtain ⟨ht, w, hw, heq⟩ := hfirst x hx.1 hx.2 (hhit x hx hn)
  have hZ : Z x = w := by
    change c (Y x) = w
    rw [← heq]
    exact hcinv w hw.1
  refine ⟨ht, hZ.symm ▸ hw, hZ.symm ▸ heq, ?_⟩
  rw [← heq]
  exact hgood w hw

end BianchiIX
