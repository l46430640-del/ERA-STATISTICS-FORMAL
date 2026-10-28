import BianchiIX.Measure.RadialPartitionNull

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

def radialFailurePiece (d ε : ℝ) (F : RadialPieceIndex → Set SectionCoordinates)
    (i : RadialPieceIndex) : Set SectionCoordinates :=
  radialPieceMap i.1 '' (radialPieceDomain d ε i ∩ F i)

def radialFailureSet (d ε : ℝ) (F : RadialPieceIndex → Set SectionCoordinates) : Set SectionCoordinates :=
  mainWallRadialBoundary d ε ∪ ⋃ i : RadialPieceIndex, radialFailurePiece d ε F i

def radialFailureIntegral (h d ε : ℝ) (F : RadialPieceIndex → Set SectionCoordinates)
    (i : RadialPieceIndex) : ℝ≥0∞ :=
  match i.1 with
  | Sum.inl neg =>
      ∫⁻ n₂ : ℝ, ∫⁻ n₃ : ℝ, ENNReal.ofReal (1 / (n₂ * n₃)) *
        ∫⁻ r in {r : ℝ | 0 < n₂ ∧ 0 < n₃ ∧
          r ∈ shearRadialInterval (dyadicScale d i.2) d ε n₂ n₃ ∧ ![r, n₂, n₃] ∈ F i},
          ENNReal.ofReal (mainWallOriginalDensity h
            (signedShearLogCoordinates (if neg then -1 else 1) ![r, n₂, n₃]))
  | Sum.inr other =>
      ∫⁻ θ : ℝ, ∫⁻ ζ : ℝ, ENNReal.ofReal (1 / ζ) *
        ∫⁻ r in {r : ℝ | |θ| < 1 / ε ∧ 0 < ζ ∧
          r ∈ angularRadialInterval other (dyadicScale d i.2) d θ ζ ∧ ![r, θ, ζ] ∈ F i},
          ENNReal.ofReal (mainWallOriginalDensity h (orderedAngularLogCoordinates other ![r, θ, ζ]))

theorem radialFailurePiece_subset (d ε : ℝ) (F : RadialPieceIndex → Set SectionCoordinates)
    (i : RadialPieceIndex) : radialFailurePiece d ε F i ⊆ physicalRadialPiece d ε i :=
  image_mono inter_subset_left

theorem measurableSet_radialFailurePiece {d ε : ℝ} (hd : 0 < d)
    {F : RadialPieceIndex → Set SectionCoordinates} (hF : ∀ i, MeasurableSet (F i))
    (i : RadialPieceIndex) : MeasurableSet (radialFailurePiece d ε F i) := by
  rcases i with ⟨neg | other, j⟩
  · exact measurableSet_shearRadialPiece (by cases neg <;> norm_num) (hF _)
  · exact measurableSet_angularRadialPiece other (dyadicScale_pos hd j) (hF _)

theorem measurableSet_radialFailureSet {d ε : ℝ} (hd : 0 < d)
    {F : RadialPieceIndex → Set SectionCoordinates} (hF : ∀ i, MeasurableSet (F i)) :
    MeasurableSet (radialFailureSet d ε F) :=
  (measurableSet_mainWallRadialBoundary d ε).union
    (MeasurableSet.iUnion fun i => measurableSet_radialFailurePiece hd hF i)

theorem radialFailurePieces_pairwiseDisjoint {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε)
    (F : RadialPieceIndex → Set SectionCoordinates) :
    Pairwise (fun i j : RadialPieceIndex => Disjoint (radialFailurePiece d ε F i) (radialFailurePiece d ε F j)) := by
  intro i j hij
  exact (physicalRadialPieces_pairwiseDisjoint hd hε hij).mono
    (radialFailurePiece_subset d ε F i) (radialFailurePiece_subset d ε F j)

theorem mainWallOriginalMeasure_radialFailurePiece {h d ε : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1 / 8) (hd : 0 < d) (hdh : d ≤ h / 8) (hε : ε ≤ 1)
    {F : RadialPieceIndex → Set SectionCoordinates} (hF : ∀ i, MeasurableSet (F i))
    (i : RadialPieceIndex) :
    mainWallOriginalMeasure h (radialFailurePiece d ε F i) = radialFailureIntegral h d ε F i := by
  rcases i with ⟨neg | other, j⟩
  · exact mainWallOriginalMeasure_shearRadialPiece hh hh1 (dyadicScale_pos hd j) hdh hε
      (by cases neg <;> norm_num) (hF _)
  · exact mainWallOriginalMeasure_angularRadialPiece other hh hh1 (dyadicScale_pos hd j) hdh (hF _)

/-- The exact global flux identity includes the region-dependent dyadic boundary at zero cost. -/
theorem mainWallOriginalMeasure_radialFailureSet {h d ε : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1 / 8) (hd : 0 < d) (hdh : d ≤ h / 8)
    (hε : 0 < ε) (hε1 : ε ≤ 1) {F : RadialPieceIndex → Set SectionCoordinates}
    (hF : ∀ i, MeasurableSet (F i)) :
    mainWallOriginalMeasure h (radialFailureSet d ε F) = ∑' i, radialFailureIntegral h d ε F i := by
  have H : mainWallOriginalMeasure h (radialFailureSet d ε F) =
      mainWallOriginalMeasure h (⋃ i, radialFailurePiece d ε F i) := by
    apply le_antisymm
    · exact (measure_union_le _ _).trans_eq (by rw [mainWallOriginalMeasure_radialBoundary, zero_add])
    · exact measure_mono subset_union_right
  rw [H, measure_iUnion (radialFailurePieces_pairwiseDisjoint hd hε F)
    (fun i => measurableSet_radialFailurePiece hd hF i)]
  apply tsum_congr
  exact fun i => mainWallOriginalMeasure_radialFailurePiece hh hh1 hd hdh hε1 hF i

/-- Every point outside the fixed failure set has exactly one assigned nonfailure coordinate. -/
theorem radialFailureSet_complement {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (F : RadialPieceIndex → Set SectionCoordinates) {z : SectionCoordinates}
    (hz : z ∈ mainWallOpenSection d \ radialFailureSet d ε F) :
    ∃! i : RadialPieceIndex, z ∈ physicalRadialPiece d ε i ∧ radialPieceInverse i.1 z ∉ F i := by
  have hb : z ∉ mainWallRadialBoundary d ε := fun hb => hz.2 (Or.inl hb)
  have hcover := hz.1
  rw [mainWallOpenSection_radial_partition hd hε hε1] at hcover
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover.resolve_left hb)
  refine ⟨i, ⟨hi, ?_⟩, ?_⟩
  · rintro hf
    rcases hi with ⟨x, hx, rfl⟩
    rw [radialPieceInverse_map hd hx] at hf
    exact hz.2 (Or.inr (mem_iUnion_of_mem i ⟨x, ⟨hx, hf⟩, rfl⟩))
  · intro j hj
    by_contra hji
    exact Set.disjoint_left.mp (physicalRadialPieces_pairwiseDisjoint hd hε hji) hj.1 hi

end BianchiIX
