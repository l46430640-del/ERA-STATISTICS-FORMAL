import BianchiIX.Dynamics.AxisAtlas
import BianchiIX.Dynamics.SmoothEventBranch

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology ContDiff

namespace AxisWallArrival

variable {A B : NormalizedSymmetry} {h k t₀ : ℝ} (P : AxisWallArrival A B h k t₀)

/-- Smoothness is a property of every existing arrival branch, not of a new branch choice. -/
theorem contDiffAt_smooth (hk : 0 < k) {y : SectionCoordinates} (hy : y ∈ P.source) :
    ContDiffAt ℝ ∞ P.coordinateTime y ∧ ContDiffAt ℝ ∞ P.map y := by
  let C := axisWallChart A h
  let g : NormalizedState → ℝ := fun x => B.map x 2
  have H := P.mem_relation hy
  have htime : ContinuousAt P.coordinateTime y :=
    (P.continuousOn_coordinateTime y hy).continuousAt (P.isOpen_source.mem_nhds hy)
  have hg : ContDiffAt ℝ ∞ g (normalizedMaxCurve (C y) t₀ (P.coordinateTime y)) := by
    dsimp only [g]
    fun_prop
  have htrans : normalizedEventRate g (C y) t₀ (P.coordinateTime y) ≠ 0 := by
    rw [normalizedEventRate_axisWall, H.2.2.1]
    have hrate : rateOne (B.map (normalizedMaxCurve (C y) t₀ (P.coordinateTime y)) 0)
        (B.map (normalizedMaxCurve (C y) t₀ (P.coordinateTime y)) 1) < 0 := by
      unfold rateOne shearSq
      nlinarith [sq_nonneg (B.map (normalizedMaxCurve (C y) t₀ (P.coordinateTime y)) 0),
        sq_nonneg (B.map (normalizedMaxCurve (C y) t₀ (P.coordinateTime y)) 1), H.2.2.2]
    exact ne_of_lt (mul_neg_of_neg_of_pos hrate hk)
  have hhit : ∀ᶠ v in 𝓝 y, g (normalizedMaxCurve (C v) t₀ (P.coordinateTime v)) =
      g (normalizedMaxCurve (C y) t₀ (P.coordinateTime y)) := by
    filter_upwards [P.isOpen_source.mem_nhds hy] with v hv
    exact (P.mem_relation hv).2.2.1.trans H.2.2.1.symm
  obtain ⟨hτ, hF⟩ := contDiffAt_normalized_event_branch
    (contDiffAt_axisWallChart A (P.source_chart hy) ∞) (P.time_mem y hy) hg htrans htime hhit
  have hpos : positiveWalls (normalizedMaxCurve (C y) t₀ (P.coordinateTime y)) := by
    rw [show normalizedMaxCurve (C y) t₀ (P.coordinateTime y) =
      axisWallChart B k (P.map y) from (P.arrival y hy).symm]
    exact axisWallChart_positive B hk _
  have heq : P.map =ᶠ[𝓝 y] (fun v => axisWallCoordinates B
      (normalizedMaxCurve (C v) t₀ (P.coordinateTime v))) := by
    filter_upwards [P.isOpen_source.mem_nhds hy] with v hv
    exact P.map_eq_coordinates hv
  exact ⟨hτ, ((contDiffAt_axisWallCoordinates B hpos ∞).comp y
    (g := axisWallCoordinates B) (f := fun v => normalizedMaxCurve (C v) t₀ (P.coordinateTime v))
    hF).congr_of_eventuallyEq heq⟩

theorem contDiffOn_coordinateTime_smooth (hk : 0 < k) :
    ContDiffOn ℝ ∞ P.coordinateTime P.source :=
  fun _ hy => (P.contDiffAt_smooth hk hy).1.contDiffWithinAt

theorem contDiffOn_map_smooth (hk : 0 < k) : ContDiffOn ℝ ∞ P.map P.source :=
  fun _ hy => (P.contDiffAt_smooth hk hy).2.contDiffWithinAt

theorem map_det_ne_zero (hh : 0 < h) (hk : 0 < k) {y : SectionCoordinates} (hy : y ∈ P.source) :
    (fderiv ℝ P.map y).det ≠ 0 :=
  axisWall_coordinate_det_ne_zero A B hh hk (P.source_chart hy) (P.target_chart hy) (P.time_mem y hy)
    ((P.time_regular y hy).differentiableAt (by norm_num))
    ((P.map_regular y hy).differentiableAt (by norm_num)) (P.eventually_arrival hy)

/-- The unchanged injective branch is a smooth diffeomorphism on its entire open source. -/
theorem exists_smooth_diffeomorph (hh : 0 < h) (hk : 0 < k) :
    ∃ e : OpenPartialHomeomorph SectionCoordinates SectionCoordinates,
      e.source = P.source ∧ e.target = P.map '' P.source ∧ (e : SectionCoordinates → SectionCoordinates) = P.map ∧
        ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  have hd (y : SectionCoordinates) (hy : y ∈ P.source) :
      ∃ L : SectionCoordinates ≃L[ℝ] SectionCoordinates,
        HasFDerivAt P.map (L : SectionCoordinates →L[ℝ] SectionCoordinates) y := by
    let L := (fderiv ℝ P.map y).toContinuousLinearEquivOfDetNeZero (P.map_det_ne_zero hh hk hy)
    refine ⟨L, ?_⟩
    rw [show (L : SectionCoordinates →L[ℝ] SectionCoordinates) = fderiv ℝ P.map y from
      ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _]
    exact ((P.contDiffAt_smooth hk hy).2.differentiableAt (by simp)).hasFDerivAt
  have ho : IsOpenMap (fun y : P.source => P.map y.val) := by
    apply IsOpenMap.of_nhds_le
    intro y
    obtain ⟨L, hL⟩ := hd y.val y.property
    have H := ((P.contDiffAt_smooth hk y.property).2.hasStrictFDerivAt' hL (by simp)).map_nhds_eq_of_equiv
    have hsub := P.isOpen_source.isOpenEmbedding_subtypeVal.map_nhds_eq y
    rw [← H, ← hsub, Filter.map_map]
    exact le_rfl
  let e₀ := P.injOn.toPartialEquiv P.map P.source
  let e := OpenPartialHomeomorph.ofContinuousOpenRestrict e₀
    (P.contDiffOn_map_smooth hk).continuousOn ho P.isOpen_source
  refine ⟨e, rfl, rfl, rfl, P.contDiffOn_map_smooth hk, ?_⟩
  intro z hz
  have hy : e.symm z ∈ P.source := e.map_target hz
  obtain ⟨L, hL⟩ := hd (e.symm z) hy
  exact (e.contDiffAt_symm hz hL (P.contDiffAt_smooth hk hy).2).contDiffWithinAt

end AxisWallArrival

/-- Every branch in the existing countable cover has smooth time and a smooth inverse on its open image. -/
theorem AxisWallArrivalAtlas.smooth_branches {A B : NormalizedSymmetry} {h k t₀ : ℝ}
    (C : AxisWallArrivalAtlas A B h k t₀) (hh : 0 < h) (hk : 0 < k) (n : ℕ) :
    ContDiffOn ℝ ∞ (C.branch n).coordinateTime (C.branch n).source ∧
      ∃ e : OpenPartialHomeomorph SectionCoordinates SectionCoordinates,
        e.source = (C.branch n).source ∧ e.target = (C.branch n).map '' (C.branch n).source ∧
          (e : SectionCoordinates → SectionCoordinates) = (C.branch n).map ∧
          ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target :=
  ⟨(C.branch n).contDiffOn_coordinateTime_smooth hk, (C.branch n).exists_smooth_diffeomorph hh hk⟩

end BianchiIX
