import BianchiIX.Measure.TransverseWallNull
import BianchiIX.Measure.PrimaryAxisStatistics
import BianchiIX.Dynamics.WallProductDecay

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology ENNReal

theorem volume_axisFamily_exceptional_slice {h : ℝ} (hh : 0 < h)
    {E : Fin 3 → Set SectionCoordinates} {P : Fin 3 × SectionCoordinates → Prop}
    (hE : ∀ i, E i ⊆ mainWallChartDomain h)
    (H : ∀ᵐ z ∂axisFamilyMeasure (fun _ : Fin 3 => h), z ∈ axisFamilySection E → P z)
    (i : Fin 3) : volume {y | y ∈ E i ∧ ¬P (i, y)} = 0 := by
  have Hi := (ae_axisFamilyMeasure_iff _ _).mp H i
  have hae : ∀ᵐ y ∂mainWallMeasure h, ¬(y ∈ E i ∧ ¬P (i, y)) := by
    filter_upwards [Hi] with y hy hbad
    exact hbad.2 (hy hbad.1)
  have hnull : mainWallMeasure h {y | y ∈ E i ∧ ¬P (i, y)} = 0 := by
    simpa only [ae_iff, not_not] using hae
  have Hvol := (mainWallMeasure_null_iff hh _).mp hnull
  rwa [Measure.restrict_apply' (isOpen_mainWallChartDomain h).measurableSet,
    inter_eq_left.mpr (fun _ hy => hE i hy.1)] at Hvol

/-- Statistical capture on the complete small section propagates to every transverse initial chart. -/
theorem ae_transverse_statistical_future_of_smallSection
    (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) {h d η σ Bcap : ℝ} {J : ℕ}
    (hh : 0 < h) (hhmax : h ≤ 1 / 16) (hd : 0 < d) (hdh : d < h / 8)
    (hstat : ∀ᵐ z ∂axisFamilyMeasure (fun _ : Fin 3 => h),
      z ∈ axisFamilySection (fun _ => mainWallSmallSection d ∩ mainWallChartDomain h) →
        WallProductDecay (axisFamilyChart primaryAxisFrame (fun _ => h) z) →
          StatisticalCoreFuture η J σ Bcap (axisFamilyChart primaryAxisFrame (fun _ => h) z))
    {C : SectionCoordinates → NormalizedState} {U : Set SectionCoordinates}
    (hU : IsOpen U) (hC : ∀ y ∈ U, ContDiffAt ℝ 1 C y)
    (hp : ∀ y ∈ U, positiveWalls (C y)) (hc : ∀ y ∈ U, stateConstraint (C y) = 1)
    (hflux : ∀ y ∈ U,
      normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0)
    (ρ : SectionCoordinates → ℝ≥0∞) :
    ∀ᵐ y ∂(volume.withDensity ρ), y ∈ U → WallProductDecay (C y) → StatisticalCoreFuture η J σ Bcap (C y) := by
  let E := mainWallSmallSection d ∩ mainWallChartDomain h
  let P : Fin 3 × SectionCoordinates → Prop := fun z =>
    WallProductDecay (axisFamilyChart primaryAxisFrame (fun _ => h) z) →
      StatisticalCoreFuture η J σ Bcap (axisFamilyChart primaryAxisFrame (fun _ => h) z)
  let Z : Fin 3 → Set SectionCoordinates := fun i => {z | z ∈ E ∧ ¬P (i, z)}
  have hZ (i : Fin 3) : volume (Z i) = 0 :=
    volume_axisFamily_exceptional_slice hh (fun _ _ hz => hz.2) hstat i
  have havoid := ae_transverse_orbit_avoids_axis_null_targets primaryAxisFrame (t₀ := 0)
    (fun _ => hh) hU hC hp hc hflux (Z := Z) (fun _ _ hz => hz.1.2) hZ ρ
  filter_upwards [havoid, ae_transverse_late_primaryAxis_crossing hBirkhoff hh hhmax hd hdh
    hU hC hp hc hflux ρ] with y hy hhit hyU hprod
  obtain ⟨i, hi⟩ := hhit hyU hprod
  obtain ⟨t, ht, hdom, z, hz, heq, hs, hb, hw, _⟩ := hi 0 1 (by norm_num)
  have hzE : z ∈ E := ⟨⟨hs.le, max_le hb.le hw.le⟩, hz⟩
  have hgood : P (i, z) := by
    by_contra hn
    exact hy hyU t hdom i z ⟨hzE, hn⟩ heq
  have hdecay : WallProductDecay (axisFamilyChart primaryAxisFrame (fun _ => h) (i, z)) := by
    change WallProductDecay (axisWallChart (primaryAxisFrame i) h z)
    rw [heq, wallProductDecay_maxCurve_iff (hc y hyU) hdom]
    exact hprod
  have H : StatisticalCoreFuture η J σ Bcap (normalizedMaxCurve (C y) 0 t) := by
    simpa only [axisFamilyChart, heq] using hgood hdecay
  exact H.of_forward (hc y hyU) (by simpa using ht.le)

/-- A common choice of statistical parameters works almost everywhere on every smooth transverse chart. -/
theorem exists_transverse_statistics_of_decay (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧
          ∀ (C : SectionCoordinates → NormalizedState) (U : Set SectionCoordinates),
            IsOpen U → (∀ y ∈ U, ContDiffAt ℝ 1 C y) →
            (∀ y ∈ U, positiveWalls (C y)) → (∀ y ∈ U, stateConstraint (C y) = 1) →
            (∀ y ∈ U, normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0) →
            ∀ ρ : SectionCoordinates → ℝ≥0∞,
              ∀ᵐ y ∂(volume.withDensity ρ), y ∈ U → WallProductDecay (C y) →
                StatisticalCoreFuture η J σ Bcap (C y) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_primaryAxis_statistics_of_decay hBirkhoff
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bcap, hcap, hcapone, hS, hhS, HS⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  let h := min hS (1 / 16) / 2
  have hh : 0 < h := div_pos (lt_min hhS (by norm_num)) (by norm_num)
  have hhle : h ≤ min hS (1 / 16) := (half_lt_self (lt_min hhS (by norm_num))).le
  obtain ⟨dS, hdS, HdS⟩ := HS h ⟨hh, hhle.trans (min_le_left _ _)⟩
  let d := min dS (h / 8) / 2
  have hd : 0 < d := div_pos (lt_min hdS (div_pos hh (by norm_num))) (by norm_num)
  have hdlt : d < min dS (h / 8) := half_lt_self (lt_min hdS (div_pos hh (by norm_num)))
  refine ⟨Bcap, hcap, hcapone, ?_⟩
  intro C U hU hC hp hc hflux ρ
  exact ae_transverse_statistical_future_of_smallSection hBirkhoff hh
    (hhle.trans (min_le_right _ _)) hd (hdlt.trans_le (min_le_right _ _))
    (HdS d ⟨hd, hdlt.le.trans (min_le_left _ _)⟩) hU hC hp hc hflux ρ

end BianchiIX
