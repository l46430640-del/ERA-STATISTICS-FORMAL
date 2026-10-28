import BianchiIX.Measure.LateCoreTarget
import BianchiIX.Measure.TransverseCoreNull
import BianchiIX.Dynamics.MainWallDensity

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology ENNReal

def corePhaseSectionCoordinates (q : SectionCoordinates) : SectionCoordinates :=
  coreSectionCoordinates (coreRadiusEntry ![2 / q 0, q 1, q 2])

theorem contDiffAt_corePhaseSectionCoordinates (n : WithTop ℕ∞) {q : SectionCoordinates}
    (hq : q 0 ∈ Ioo (0 : ℝ) 1) : ContDiffAt ℝ n corePhaseSectionCoordinates q := by
  have hk : 1 < 2 / q 0 := (lt_div_iff₀ hq.1).mpr (by linarith only [hq.2])
  have hcoord : ContDiffAt ℝ n (fun z : SectionCoordinates => (![2 / z 0, z 1, z 2] : CoreAngleState)) q := by
    have hne := hq.1.ne'
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i <;> dsimp <;> fun_prop
  exact (contDiff_coreSectionCoordinates n).contDiffAt.comp q
    ((contDiffAt_coreRadiusEntry n hk).comp q hcoord)

/-- Uniform eventual Taub avoidance and decaying wall products occur on a null set of every transverse chart. -/
theorem volume_eventually_taub_avoiding_section
    (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) {ε : ℝ} (hε : 0 < ε)
    {C : SectionCoordinates → NormalizedState} {U : Set SectionCoordinates}
    (hU : IsOpen U) (hC : ∀ y ∈ U, ContDiffAt ℝ 1 C y)
    (hp : ∀ y ∈ U, positiveWalls (C y)) (hc : ∀ y ∈ U, stateConstraint (C y) = 1)
    (hflux : ∀ y ∈ U,
      normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0) :
    volume {y | y ∈ U ∧
      (∀ᶠ t in atTop, ∀ i, ε ≤ normalizedEuclideanDistance (normalizedMaxCurve (C y) 0 t) (taubPoint i)) ∧
      (∀ i j : Fin 3, i ≠ j → Tendsto
        (fun t => wallValue i (normalizedMaxCurve (C y) 0 t) * wallValue j (normalizedMaxCurve (C y) 0 t))
          atTop (𝓝 0))} = 0 := by
  obtain ⟨B, _, hnull, Hhit⟩ := exists_late_null_core_target hBirkhoff hε
  let Z := corePhaseSectionCoordinates '' coreTaubAvoidance ε B
  have hZ : volume Z = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (fun q hq => ((contDiffAt_corePhaseSectionCoordinates 1 hq.1).differentiableAt
        (by norm_num)).differentiableWithinAt) hnull
  have haxis (a : Fin 6) : volume
      (U ∩ transverseCoreHittingDomain (fun y => (axisFrame a).map (C y)) 0 Z) = 0 :=
    volume_axis_transverseCoreHittingDomain (axisFrame a) hU hC hp hc hflux hZ
  apply measure_mono_null (t := ⋃ a : Fin 6,
    U ∩ transverseCoreHittingDomain (fun y => (axisFrame a).map (C y)) 0 Z) _
      (measure_iUnion_null haxis)
  intro y hy
  obtain ⟨T, hT, a, q, hq, hdom, heq, htrans⟩ := Hhit (C y) (hc y hy.1) (hp y hy.1) hy.2.1 hy.2.2 0
  let z := coreRadiusEntry ![2 / q 0, q 1, q 2]
  have hposit : positiveWalls (fromProjectiveState z) := by
    rw [heq]
    exact ((axisFrame a).positive _).mpr
      (normalizedMaxCurve_forward (hp y hy.1) (hc y hy.1) (by simpa using hT.le)).2.1
  have hD : projectiveStateDenom z ≠ 0 := by
    intro hz
    simpa [fromProjectiveState, hz] using hposit.1
  have hflow : normalizedMaxCurve ((axisFrame a).map (C y)) 0 T = fromProjectiveState z :=
    ((axisFrame a).maxCurve hdom).trans heq.symm
  have hproj : toProjectiveState (normalizedMaxCurve ((axisFrame a).map (C y)) 0 T) = z := by
    rw [hflow, toProjectiveState_fromProjectiveState hD]
  refine mem_iUnion.mpr ⟨a, hy.1, T, ?_, ?_, ?_, ?_⟩
  · rwa [(axisFrame a).maxDomain]
  · change toProjectiveState _ 2 = 1
    rw [hproj]
    rfl
  · unfold normalizedEventRate
    rw [hflow]
    exact htrans.ne'
  · change coreSectionCoordinates (toProjectiveState _) ∈ Z
    rw [hproj]
    exact mem_image_of_mem corePhaseSectionCoordinates hq

/-- Countably many distance thresholds remove every eventually Taub-separated orbit with decaying wall products. -/
theorem volume_eventually_taub_separated_section
    (hBirkhoff : Literature.BirkhoffErgodicInput ℝ)
    {C : SectionCoordinates → NormalizedState} {U : Set SectionCoordinates}
    (hU : IsOpen U) (hC : ∀ y ∈ U, ContDiffAt ℝ 1 C y)
    (hp : ∀ y ∈ U, positiveWalls (C y)) (hc : ∀ y ∈ U, stateConstraint (C y) = 1)
    (hflux : ∀ y ∈ U,
      normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0) :
    volume {y | y ∈ U ∧
      (∃ ε > (0 : ℝ), ∀ᶠ t in atTop, ∀ i,
        ε ≤ normalizedEuclideanDistance (normalizedMaxCurve (C y) 0 t) (taubPoint i)) ∧
      (∀ i j : Fin 3, i ≠ j → Tendsto
        (fun t => wallValue i (normalizedMaxCurve (C y) 0 t) * wallValue j (normalizedMaxCurve (C y) 0 t))
          atTop (𝓝 0))} = 0 := by
  let E (n : ℕ) := {y | y ∈ U ∧
    (∀ᶠ t in atTop, ∀ i, 1 / (n + 1 : ℝ) ≤
      normalizedEuclideanDistance (normalizedMaxCurve (C y) 0 t) (taubPoint i)) ∧
    (∀ i j : Fin 3, i ≠ j → Tendsto
      (fun t => wallValue i (normalizedMaxCurve (C y) 0 t) * wallValue j (normalizedMaxCurve (C y) 0 t))
        atTop (𝓝 0))}
  have hE (n : ℕ) : volume (E n) = 0 :=
    volume_eventually_taub_avoiding_section hBirkhoff (by positivity) hU hC hp hc hflux
  apply measure_mono_null (t := ⋃ n, E n) _ (measure_iUnion_null hE)
  rintro y ⟨hy, ⟨ε, hε, ha⟩, hd⟩
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  refine mem_iUnion.mpr ⟨n, hy, ?_, hd⟩
  exact ha.mono fun t ht i => hn.le.trans (ht i)

theorem ae_arbitrarily_late_taub_approach
    (hBirkhoff : Literature.BirkhoffErgodicInput ℝ)
    {C : SectionCoordinates → NormalizedState} {U : Set SectionCoordinates}
    (hU : IsOpen U) (hC : ∀ y ∈ U, ContDiffAt ℝ 1 C y)
    (hp : ∀ y ∈ U, positiveWalls (C y)) (hc : ∀ y ∈ U, stateConstraint (C y) = 1)
    (hflux : ∀ y ∈ U,
      normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0)
    (ρ : SectionCoordinates → ℝ≥0∞) :
    ∀ᵐ y ∂(volume.withDensity ρ), y ∈ U →
      (∀ i j : Fin 3, i ≠ j → Tendsto
        (fun t => wallValue i (normalizedMaxCurve (C y) 0 t) * wallValue j (normalizedMaxCurve (C y) 0 t))
          atTop (𝓝 0)) →
      ∀ ε > (0 : ℝ), ∀ r : ℝ, ∃ t ≥ r, ∃ i : Fin 3,
        normalizedEuclideanDistance (normalizedMaxCurve (C y) 0 t) (taubPoint i) < ε := by
  classical
  have hnull := withDensity_absolutelyContinuous volume ρ
    (volume_eventually_taub_separated_section hBirkhoff hU hC hp hc hflux)
  have hae : ∀ᵐ y ∂(volume.withDensity ρ), ¬(y ∈ U ∧
      (∃ ε > (0 : ℝ), ∀ᶠ t in atTop, ∀ i,
        ε ≤ normalizedEuclideanDistance (normalizedMaxCurve (C y) 0 t) (taubPoint i)) ∧
      (∀ i j : Fin 3, i ≠ j → Tendsto
        (fun t => wallValue i (normalizedMaxCurve (C y) 0 t) * wallValue j (normalizedMaxCurve (C y) 0 t))
          atTop (𝓝 0))) := by
    rw [ae_iff]
    simpa only [not_not] using hnull
  filter_upwards [hae] with y hy hyU hd ε hε r
  by_contra! hn
  apply hy
  exact ⟨hyU, ⟨ε, hε, (eventually_ge_atTop r).mono fun t ht i => hn t ht i⟩, hd⟩

theorem ae_mainWall_arbitrarily_late_taub_approach
    (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) {h : ℝ} (hh : 0 < h)
    (ρ : SectionCoordinates → ℝ≥0∞) :
    ∀ᵐ y ∂(volume.withDensity ρ), y ∈ mainWallChartDomain h →
      (∀ i j : Fin 3, i ≠ j → Tendsto
        (fun t => wallValue i (normalizedMaxCurve (mainWallChart h y) 0 t) *
          wallValue j (normalizedMaxCurve (mainWallChart h y) 0 t)) atTop (𝓝 0)) →
      ∀ ε > (0 : ℝ), ∀ r : ℝ, ∃ t ≥ r, ∃ i : Fin 3,
        normalizedEuclideanDistance (normalizedMaxCurve (mainWallChart h y) 0 t) (taubPoint i) < ε := by
  apply ae_arbitrarily_late_taub_approach hBirkhoff (isOpen_mainWallChartDomain h)
    (fun _ hy => contDiffAt_mainWallChart hy 1) (fun y _ => mainWallChart_positive hh y)
    (fun _ hy => mainWallChart_constraint hy) _ ρ
  intro y hy
  rw [(hasFDerivAt_mainWallChart hy).fderiv]
  apply abs_pos.mp
  rw [show (fun i => mainWallChartDifferential h y (Pi.single i 1)) = mainWallChartFrame h y from rfl,
    mainWallChart_flux hh hy]
  exact mainWallChartDensity_pos hh hy

end BianchiIX
