import BianchiIX.Measure.RestartClosedSection
import BianchiIX.Measure.CommonSuccessException
import BianchiIX.Measure.AxisFamilyCoordinates
import BianchiIX.Statistics.CoreRestartTransport

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

/-- A single global Borel map selects an exact statistical core outside one invariant exception null on every transverse section and in four-dimensional constraint coordinates. -/
theorem exists_common_borel_core_restart
    (hBirkhoff : Literature.BirkhoffErgodicInput ℝ)
    (hBrehm : Literature.BrehmIXAttractorInput) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∀ Bbound : ℝ, 0 < Bbound →
          ∃ N : Set NormalizedState, MeasurableSet N ∧ N ⊆ physicalPhaseSpace ∧
            geometricException ⊆ N ∧
            (∀ x : NormalizedState, ∀ t ∈ normalizedMaxDomain x 0,
              normalizedMaxCurve x 0 t ∈ N ↔ x ∈ N) ∧
            (∀ (C : SectionCoordinates → NormalizedState) (U : Set SectionCoordinates),
              IsOpen U → (∀ y ∈ U, ContDiffAt ℝ 1 C y) →
              (∀ y ∈ U, positiveWalls (C y)) → (∀ y ∈ U, stateConstraint (C y) = 1) →
              (∀ y ∈ U, normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0) →
              volume (U ∩ C ⁻¹' N) = 0) ∧ NullInFourCoordinates N ∧
            ∃ W : NormalizedState → CoreRestartData, Measurable W ∧
              ∀ x ∈ physicalPhaseSpace, x ∉ N →
                (W x).2.1 ≤ Bbound ∧ CoreRestartWitness η J σ Bcap x (W x) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_restartClosedSection_borel_restart hBirkhoff
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bcap, hcap, hcapone, hS, hhS, _, HS⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  refine ⟨Bcap, hcap, hcapone, ?_⟩
  intro Bbound hBbound
  let h := min hS (1 / 16) / 2
  have hh : 0 < h := div_pos (lt_min hhS (by norm_num)) (by norm_num)
  have hhle : h ≤ min hS (1 / 16) := (half_lt_self (lt_min hhS (by norm_num))).le
  have hhmax : h ≤ 1 / 16 := hhle.trans (min_le_right _ _)
  have hh1 : h ≤ 1 / 8 := hhmax.trans (by norm_num)
  obtain ⟨_, _, HB⟩ := HS h ⟨hh, hhle.trans (min_le_left _ _)⟩
    50 90 550 (by norm_num) (by norm_num) (by norm_num) (1 / 128) (by norm_num)
  obtain ⟨dS, hdS, _, HdS⟩ := HB Bbound hBbound
  let d := min dS (h / 8) / 2
  have hd : 0 < d := div_pos (lt_min hdS (div_pos hh (by norm_num))) (by norm_num)
  have hdlt : d < min dS (h / 8) := half_lt_self (lt_min hdS (div_pos hh (by norm_num)))
  have hdh : d < h / 8 := hdlt.trans_le (min_le_right _ _)
  have hd1 : d ≤ 1 / 8 := hdh.le.trans (by linarith only [hh1])
  let F₀ := mainWallClosedFailure d
    (radialFailureSet d (1 / 128) (restartRadialFailureFamily h 50 d (1 / 128) 550 η J σ Bcap))
  obtain ⟨hF₀, _, _, hcompare, _, hfiniteOriginal, W₀, hW₀, Hgood⟩ :=
    HdS d ⟨hd, hdlt.le.trans (min_le_left _ _)⟩
  have hF₀finite : mainWallMeasure h F₀ ≠ ⊤ := ne_top_of_le_ne_top hfiniteOriginal hcompare
  let E := fun _ : Fin 3 => mainWallSmallSection d ∩ mainWallChartDomain h
  let F := axisFamilySection (fun _ : Fin 3 => F₀)
  have hE : ∀ i, MeasurableSet (E i) := fun _ =>
    (measurableSet_mainWallSmallSection d).inter (isOpen_mainWallChartDomain h).measurableSet
  have hF : MeasurableSet F := measurableSet_axisFamilySection (fun _ => hF₀)
  have hfinite : axisFamilyMeasure (fun _ : Fin 3 => h) F ≠ ⊤ := by
    rw [axisFamilyMeasure_constant_section h hF₀]
    exact ENNReal.mul_ne_top (by norm_num) hF₀finite
  have hsmall (i : Fin 3) (y : SectionCoordinates) (hy : y ∈ E i) :
      y ∈ mainWallChartDomain h ∧ |y 0| ≤ 1 / 8 ∧
        Real.exp (-y 1) ≤ h / 8 ∧ Real.exp (-y 2) ≤ h / 8 :=
    ⟨hy.2, hy.1.1.trans hd1, (le_max_left _ _).trans (hy.1.2.trans hdh.le),
      (le_max_right _ _).trans (hy.1.2.trans hdh.le)⟩
  have hinj : InjOn (axisFamilyChart primaryAxisFrame (fun _ => h)) (axisFamilySection E) :=
    primaryAxisChart_injOn (fun i y hy => mem_dominantWallChartDomain_of_small hh
      (hsmall i y hy).1 (hsmall i y hy).2.2.1 (hsmall i y hy).2.2.2)
  obtain ⟨N, hNm, hNp, hNg, hNi, hNn, hNfour, hhit⟩ :=
    exists_common_borel_success_exception hBirkhoff hBrehm hh hhmax hd hdh hF hfinite
  obtain ⟨τ, Y, hτ, hY, hflow, hfirst, _⟩ :=
    exists_smallAxis_borel_first_success hh hh1 hE hsmall hF hfinite
  obtain ⟨c, hcm, hcinv⟩ := exists_measurable_primaryAxis_coordinates hE hinj
  let Z := c ∘ Y
  have hZ : Measurable Z := hcm.comp hY
  let I : Fin 3 → Fin 6 := fun i => (axisOrder_covers (Equiv.swap 0 i)).choose
  have hI : Measurable I := measurable_of_countable _
  let V := fun x => coreRestartFrame (I (Z x).1) (W₀ (Z x).2)
  have hV : Measurable V := measurable_coreRestartFrame.comp ((hI.comp hZ.fst).prodMk (hW₀.comp hZ.snd))
  let W := fun x => coreRestartDelay (τ x) (V x)
  have hW : Measurable W := measurable_coreRestartDelay.comp (hτ.prodMk hV)
  refine ⟨N, hNm, hNp, hNg, hNi, hNn, hNfour, W, hW, ?_⟩
  intro x hx hn
  obtain ⟨ht, z, hz, heq⟩ := hfirst x hx.1 hx.2 (hhit x hx hn)
  have hZeq : Z x = z := by
    change c (Y x) = z
    rw [← heq]
    exact hcinv z hz.1
  have Hcanonical := (Hgood z.2 ⟨hz.1.1, hz.2⟩).2.2.1
  have Hframe : CoreRestartWitness η J σ Bcap
      ((axisFrame (I z.1)).map (axisFamilyChart primaryAxisFrame (fun _ => h) z)) (W₀ z.2) := by
    change CoreRestartWitness η J σ Bcap
      ((primaryAxisFrame z.1).map ((primaryAxisFrame z.1).map.symm (mainWallChart h z.2))) (W₀ z.2)
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using Hcanonical
  have Hsuccess : CoreRestartWitness η J σ Bcap (Y x) (V x) := by
    dsimp only [V]
    rw [hZeq, ← heq]
    exact Hframe.of_axisFrame (I z.1)
  rw [hflow x] at Hsuccess
  refine ⟨?_, Hsuccess.of_forward hx.2 ht.1.1⟩
  change (W₀ (Z x).2).2.1 ≤ Bbound
  rw [hZeq]
  exact (Hgood z.2 ⟨hz.1.1, hz.2⟩).2.1

end BianchiIX
