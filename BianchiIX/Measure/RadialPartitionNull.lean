import BianchiIX.Measure.RadialPartitionGeometry

noncomputable section

namespace BianchiIX

open Set MeasureTheory

def mainWallRadialBoundary (d ε : ℝ) : Set SectionCoordinates :=
  mainWallOpenSection d ∩ ⋃ j : ℕ, {z | mainWallRadialRadius ε z = 2 * dyadicScale d j}

theorem measurableSet_mainWallRadialBoundary (d ε : ℝ) : MeasurableSet (mainWallRadialBoundary d ε) :=
  (measurableSet_mainWallOpenSection d).inter (MeasurableSet.iUnion fun _ =>
    measurableSet_eq_fun (measurable_mainWallRadialRadius ε) measurable_const)

theorem volume_sectionCoordinate_level (i : Fin 3) (t : ℝ) :
    volume {z : SectionCoordinates | z i = t} = 0 := by
  exact Measure.pi_eval_preimage_null (fun _ : Fin 3 => (volume : Measure ℝ)) (measure_singleton t)

theorem volume_sectionWall_level (i : Fin 3) (t : ℝ) :
    volume {z : SectionCoordinates | Real.exp (-z i) = t} = 0 := by
  apply measure_mono_null (t := {z : SectionCoordinates | z i = -Real.log t})
    _ (volume_sectionCoordinate_level i _)
  intro z hz
  have H := congrArg Real.log hz
  rw [Real.log_exp] at H
  change z i = -Real.log t
  linarith

theorem volume_mainWallRadialRadius_level (ε t : ℝ) :
    volume {z : SectionCoordinates | mainWallRadialRadius ε z = t} = 0 := by
  have hnull : volume (({z : SectionCoordinates | z 0 = t} ∪ {z | z 0 = -t}) ∪
      ({z | Real.exp (-z 1) = t} ∪ {z | Real.exp (-z 2) = t})) = 0 :=
    measure_union_null (measure_union_null (volume_sectionCoordinate_level 0 t)
      (volume_sectionCoordinate_level 0 (-t)))
      (measure_union_null (volume_sectionWall_level 1 t) (volume_sectionWall_level 2 t))
  apply measure_mono_null _ hnull
  intro z hz
  change mainWallRadialRadius ε z = t at hz
  unfold mainWallRadialRadius at hz
  split_ifs at hz
  · apply Or.inl
    rcases le_total 0 (z 0) with hs | hs
    · exact Or.inl (by simpa only [mem_ofPred_eq, abs_of_nonneg hs] using hz)
    · exact Or.inr (by rw [abs_of_nonpos hs] at hz; change z 0 = -t; linarith)
  · apply Or.inr
    rcases le_total (Real.exp (-z 1)) (Real.exp (-z 2)) with hw | hw
    · exact Or.inr (by simpa only [mem_ofPred_eq, max_eq_right hw] using hz)
    · exact Or.inl (by simpa only [mem_ofPred_eq, max_eq_left hw] using hz)

theorem volume_mainWallRadialBoundary (d ε : ℝ) : volume (mainWallRadialBoundary d ε) = 0 :=
  measure_mono_null inter_subset_right (measure_iUnion_null fun _ => volume_mainWallRadialRadius_level _ _)

theorem mainWallOriginalMeasure_radialBoundary (h d ε : ℝ) :
    mainWallOriginalMeasure h (mainWallRadialBoundary d ε) = 0 := by
  apply withDensity_absolutelyContinuous _ _
  exact Measure.absolutelyContinuous_restrict (volume_mainWallRadialBoundary d ε)

theorem dyadicScale_upper_not_mem_Ioo {d : ℝ} (hd : 0 < d) (j k : ℕ) :
    2 * dyadicScale d k ∉ Ioo (dyadicScale d j) (2 * dyadicScale d j) := by
  intro hx
  by_cases hjk : j = k
  · subst k
    exact lt_irrefl _ hx.2
  · exact Set.disjoint_left.mp (pairwise_disjoint_dyadicScale_Ioc hd.le hjk)
      ⟨hx.1, hx.2.le⟩ ⟨by linarith [dyadicScale_pos hd k], le_rfl⟩

theorem physicalRadialPiece_disjoint_boundary {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε)
    (i : RadialPieceIndex) : Disjoint (physicalRadialPiece d ε i) (mainWallRadialBoundary d ε) := by
  apply Set.disjoint_left.mpr
  intro z hz hb
  obtain ⟨j, hj⟩ := mem_iUnion.mp hb.2
  have hr := physicalRadialPiece_radius hd hε hz
  rw [show mainWallRadialRadius ε z = 2 * dyadicScale d j from hj] at hr
  exact dyadicScale_upper_not_mem_Ioo hd i.2 j hr

/-- The boundary uses the radius of the assigned region, so the cover has no enlarged exceptional set. -/
theorem mainWallOpenSection_radial_partition {d ε : ℝ}
    (hd : 0 < d) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    mainWallOpenSection d = mainWallRadialBoundary d ε ∪ ⋃ i : RadialPieceIndex, physicalRadialPiece d ε i := by
  ext z
  constructor
  · intro hz
    by_cases hb : z ∈ mainWallRadialBoundary d ε
    · exact Or.inl hb
    · obtain ⟨j, hj⟩ := exists_mem_dyadicScale_Ioc hd
        ⟨mainWallRadialRadius_pos hε z, (mainWallRadialRadius_lt hz).le⟩
      have hne : mainWallRadialRadius ε z ≠ 2 * dyadicScale d j := by
        intro heq
        exact hb ⟨hz, mem_iUnion_of_mem j heq⟩
      obtain ⟨k, hk⟩ := exists_mem_physicalRadialPiece hε hz ⟨hj.1, lt_of_le_of_ne hj.2 hne⟩
      exact Or.inr (mem_iUnion_of_mem (k, j) hk)
  · rintro (hb | hp)
    · exact hb.1
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hp
      exact physicalRadialPiece_subset_openSection hd hε1 i hi

end BianchiIX
