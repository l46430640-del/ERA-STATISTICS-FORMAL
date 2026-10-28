import BianchiIX.Dynamics.AxisJacobian
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- An injective local arrival of the exact flow between two independently chosen axis charts. -/
structure AxisWallArrival (A B : NormalizedSymmetry) (h k t₀ : ℝ) where
  source : Set SectionCoordinates
  time : NormalizedState → ℝ
  map : SectionCoordinates → SectionCoordinates
  isOpen_source : IsOpen source
  source_chart : source ⊆ mainWallChartDomain h
  target_chart : MapsTo map source (mainWallChartDomain k)
  time_mem : ∀ y ∈ source, time (axisWallChart A h y) ∈ normalizedMaxDomain (axisWallChart A h y) t₀
  time_regular : ∀ y ∈ source, ContDiffAt ℝ 1 time (axisWallChart A h y)
  map_regular : ∀ y ∈ source, ContDiffAt ℝ 1 map y
  arrival : ∀ y ∈ source,
    axisWallChart B k (map y) = normalizedMaxCurve (axisWallChart A h y) t₀ (time (axisWallChart A h y))
  injOn : InjOn map source

theorem exists_axisWallArrival (A B : NormalizedSymmetry) {h k t₀ t : ℝ} {y : SectionCoordinates}
    (hh : 0 < h) (hk : 0 < k) (hy : y ∈ mainWallChartDomain h)
    (ht : t ∈ normalizedMaxDomain (axisWallChart A h y) t₀)
    (hlevel : B.map (normalizedMaxCurve (axisWallChart A h y) t₀ t) 2 = k)
    (hp : B.map (normalizedMaxCurve (axisWallChart A h y) t₀ t) 0 < 0) :
    ∃ P : AxisWallArrival A B h k t₀, y ∈ P.source ∧ P.time (axisWallChart A h y) = t ∧
      P.map y = axisWallCoordinates B (normalizedMaxCurve (axisWallChart A h y) t₀ t) ∧
      (∀ᶠ z : SectionCoordinates × ℝ in 𝓝 (y, t), z.1 ∈ P.source ∧
        z.2 ∈ normalizedMaxDomain (axisWallChart A h z.1) t₀ ∧
        (B.map (normalizedMaxCurve (axisWallChart A h z.1) t₀ z.2) 2 = k ↔
          P.time (axisWallChart A h z.1) = z.2)) := by
  obtain ⟨τ, R, hτ, hcτ, hcR, hRy, hlocal, hdet, _, huniq⟩ :=
    exists_axisWall_coordinate_event A B hh hk hy ht hlevel hp
  let L := (fderiv ℝ R y).toContinuousLinearEquivOfDetNeZero hdet
  have hdR : HasFDerivAt R (L : SectionCoordinates →L[ℝ] SectionCoordinates) y := by
    rw [show (L : SectionCoordinates →L[ℝ] SectionCoordinates) = fderiv ℝ R y from
      ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _]
    exact (hcR.differentiableAt (by norm_num)).hasFDerivAt
  let e := hcR.toOpenPartialHomeomorph R hdR (by norm_num)
  have hye : y ∈ e.source := hcR.mem_toOpenPartialHomeomorph_source hdR (by norm_num)
  have hgood := hlocal.and
    (((contDiffAt_axisWallChart A hy 1).continuousAt.eventually
      (hcτ.eventually (by simp))).and (hcR.eventually (by simp)))
  obtain ⟨U, hU, hUopen, hyU⟩ := mem_nhds_iff.mp hgood
  let P : AxisWallArrival A B h k t₀ := {
    source := U ∩ e.source
    time := τ
    map := R
    isOpen_source := hUopen.inter e.open_source
    source_chart := fun _ hv => (hU hv.1).1.1
    target_chart := fun _ hv => (hU hv.1).1.2.2.1
    time_mem := fun _ hv => (hU hv.1).1.2.1
    time_regular := fun _ hv => (hU hv.1).2.1
    map_regular := fun _ hv => (hU hv.1).2.2
    arrival := fun _ hv => (hU hv.1).1.2.2.2
    injOn := e.injOn.mono inter_subset_right }
  refine ⟨P, ⟨hyU, hye⟩, hτ, hRy, ?_⟩
  exact (continuousAt_fst.eventually (P.isOpen_source.mem_nhds ⟨hyU, hye⟩)).and huniq

namespace AxisWallArrival

variable {A B : NormalizedSymmetry} {h k t₀ : ℝ} (P : AxisWallArrival A B h k t₀)

def restrict (U : Set SectionCoordinates) (hU : IsOpen U) : AxisWallArrival A B h k t₀ where
  source := P.source ∩ U
  time := P.time
  map := P.map
  isOpen_source := P.isOpen_source.inter hU
  source_chart := fun _ hy => P.source_chart hy.1
  target_chart := fun _ hy => P.target_chart hy.1
  time_mem := fun y hy => P.time_mem y hy.1
  time_regular := fun y hy => P.time_regular y hy.1
  map_regular := fun y hy => P.map_regular y hy.1
  arrival := fun y hy => P.arrival y hy.1
  injOn := P.injOn.mono inter_subset_left

def jacobian (y : SectionCoordinates) : ℝ :=
  mainWallChartDensity k (P.map y) * |(fderiv ℝ P.map y).det| / mainWallChartDensity h y

theorem eventually_arrival {y : SectionCoordinates} (hy : y ∈ P.source) :
    (fun v => axisWallChart B k (P.map v)) =ᶠ[𝓝 y]
      (fun v => normalizedMaxCurve (axisWallChart A h v) t₀ (P.time (axisWallChart A h v))) := by
  filter_upwards [P.isOpen_source.mem_nhds hy] with v hv
  exact P.arrival v hv

theorem density_jacobian (hh : 0 < h) (hk : 0 < k) {y : SectionCoordinates} (hy : y ∈ P.source) :
    mainWallChartDensity k (P.map y) * |(fderiv ℝ P.map y).det| =
      Real.exp (∫ u in t₀..P.time (axisWallChart A h y),
        normalizedCorrectedDivergence (normalizedMaxCurve (axisWallChart A h y) t₀ u)) *
          mainWallChartDensity h y :=
  axisWall_coordinate_jacobian A B hh hk (P.source_chart hy) (P.target_chart hy) (P.time_mem y hy)
    ((P.time_regular y hy).differentiableAt (by norm_num))
    ((P.map_regular y hy).differentiableAt (by norm_num)) (P.eventually_arrival hy)

theorem jacobian_eq_exp (hh : 0 < h) (hk : 0 < k) {y : SectionCoordinates} (hy : y ∈ P.source) :
    P.jacobian y = Real.exp (∫ u in t₀..P.time (axisWallChart A h y),
      normalizedCorrectedDivergence (normalizedMaxCurve (axisWallChart A h y) t₀ u)) := by
  rw [jacobian, P.density_jacobian hh hk hy,
    mul_div_cancel_right₀ _ (ne_of_gt (mainWallChartDensity_pos hh (P.source_chart hy)))]

theorem jacobian_pos (hh : 0 < h) (hk : 0 < k) {y : SectionCoordinates} (hy : y ∈ P.source) :
    0 < P.jacobian y := by
  rw [P.jacobian_eq_exp hh hk hy]
  exact Real.exp_pos _

theorem jacobian_gt_one (hh : 0 < h) (hk : 0 < k) {y : SectionCoordinates}
    (hy : y ∈ P.source) (ht : t₀ < P.time (axisWallChart A h y)) : 1 < P.jacobian y := by
  rw [P.jacobian_eq_exp hh hk hy,
    ← normalizedVolumeJacobian_eq_exp_integral (axisWallChart_positive A hh y)
      (axisWallChart_constraint A (P.source_chart hy)) (P.time_mem y hy)]
  exact normalizedVolumeJacobian_gt_one (axisWallChart_positive A hh y)
    (axisWallChart_constraint A (P.source_chart hy)) ht

end AxisWallArrival

theorem exists_forward_axisWallArrival (A B : NormalizedSymmetry) {h k t₀ t : ℝ} {y : SectionCoordinates}
    (hh : 0 < h) (hk : 0 < k) (hy : y ∈ mainWallChartDomain h) (htt : t₀ < t)
    (hlevel : B.map (normalizedMaxCurve (axisWallChart A h y) t₀ t) 2 = k)
    (hp : B.map (normalizedMaxCurve (axisWallChart A h y) t₀ t) 0 < 0) :
    ∃ P : AxisWallArrival A B h k t₀, y ∈ P.source ∧ P.time (axisWallChart A h y) = t ∧
      P.map y = axisWallCoordinates B (normalizedMaxCurve (axisWallChart A h y) t₀ t) ∧
      ∀ v ∈ P.source, t₀ < P.time (axisWallChart A h v) := by
  have ht := normalizedMaxDomain_contains_Ici (axisWallChart_positive A hh y)
    (axisWallChart_constraint A hy) t₀ htt.le
  obtain ⟨P, hyP, htime, hmap, _⟩ := exists_axisWallArrival A B hh hk hy ht hlevel hp
  have hc : ContinuousAt (fun v => P.time (axisWallChart A h v)) y :=
    (P.time_regular y hyP).continuousAt.comp (contDiffAt_axisWallChart A hy 1).continuousAt
  have hpositive : ∀ᶠ v in 𝓝 y, t₀ < P.time (axisWallChart A h v) :=
    continuousAt_const.eventually_lt hc (by rwa [htime])
  obtain ⟨U, hU, hUopen, hyU⟩ := mem_nhds_iff.mp hpositive
  exact ⟨P.restrict U hUopen, ⟨hyP, hyU⟩, htime, hmap, fun _ hv => hU hv.2⟩

end BianchiIX
