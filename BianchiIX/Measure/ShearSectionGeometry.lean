import BianchiIX.Measure.ShearUnselectedGeometry
import BianchiIX.Measure.DyadicCover
import BianchiIX.Dynamics.ShearRestartCommonMeasurability

noncomputable section

namespace BianchiIX

open Set MeasureTheory

def shearSection (d ε : ℝ) : Set SectionCoordinates :=
  {z | |z 0| ∈ Ioc 0 d ∧ Real.exp (-z 1) ≤ ε * |z 0| ∧ Real.exp (-z 2) ≤ ε * |z 0|}

def shearSectionAnnulus (a ε : ℝ) : Set SectionCoordinates :=
  {z | |z 0| ∈ Ioc a (2 * a) ∧ Real.exp (-z 1) ≤ ε * |z 0| ∧ Real.exp (-z 2) ≤ ε * |z 0|}

theorem measurableSet_shearSection (d ε : ℝ) : MeasurableSet (shearSection d ε) := by
  have hs : Measurable (fun z : SectionCoordinates => |z 0|) := by fun_prop
  exact (measurableSet_Ioc.preimage hs).inter
    ((measurableSet_le (by fun_prop) (measurable_const.mul hs)).inter
      (measurableSet_le (by fun_prop) (measurable_const.mul hs)))

theorem measurableSet_shearSectionAnnulus (a ε : ℝ) : MeasurableSet (shearSectionAnnulus a ε) := by
  have hs : Measurable (fun z : SectionCoordinates => |z 0|) := by fun_prop
  exact (measurableSet_Ioc.preimage hs).inter
    ((measurableSet_le (by fun_prop) (measurable_const.mul hs)).inter
      (measurableSet_le (by fun_prop) (measurable_const.mul hs)))

theorem shearSection_dyadic_cover {d ε : ℝ} (hd : 0 < d) :
    shearSection d ε = ⋃ j : ℕ, shearSectionAnnulus (dyadicScale d j) ε := by
  ext z
  constructor
  · intro hz
    obtain ⟨j, hj⟩ := exists_mem_dyadicScale_Ioc hd hz.1
    exact mem_iUnion_of_mem j ⟨hj, hz.2⟩
  · intro hz
    obtain ⟨j, hj⟩ := mem_iUnion.mp hz
    have hs : |z 0| ∈ Ioc 0 d := iUnion_dyadicScale_Ioc hd ▸ mem_iUnion_of_mem j hj.1
    exact ⟨hs, hj.2⟩

theorem shearSection_dyadic_disjoint {d ε : ℝ} (hd : 0 ≤ d) :
    Pairwise (fun j k : ℕ => Disjoint (shearSectionAnnulus (dyadicScale d j) ε)
      (shearSectionAnnulus (dyadicScale d k) ε)) := by
  intro j k hjk
  apply Set.disjoint_left.mpr
  intro z hz hw
  exact Set.disjoint_left.mp (pairwise_disjoint_dyadicScale_Ioc hd hjk) hz.1 hw.1

theorem shearSectionAnnulus_subset_layer {a ε : ℝ} (hε : 0 ≤ ε) :
    shearSectionAnnulus a ε ⊆ shearSectionLayer a ε := by
  intro z hz
  have H : ε * |z 0| ≤ 2 * ε * a :=
    (mul_le_mul_of_nonneg_left hz.1.2 hε).trans_eq (by ring)
  exact ⟨⟨hz.1.1.le, hz.1.2⟩, hz.2.1.trans H, hz.2.2.trans H⟩

/-- Outside the unselected label set, every physical point has a signed radial representation in the common return family. -/
theorem shearSection_selected_representation {a ε P : ℝ} {z : SectionCoordinates}
    (hε : 0 ≤ ε) (hz : z ∈ shearSectionAnnulus a ε) (hn : z ∉ shearUnselectedSection a ε P) :
    ∃ τ n₂ n₃ ρ : ℝ, (τ = 1 ∨ τ = -1) ∧ (n₂, n₃) ∈ restartShearCommonLabelSet ε a P ∧
      ρ ∈ Icc a (2 * a) ∧ z = ![τ * ρ, -Real.log n₂, -Real.log n₃] := by
  have hzL := shearSectionAnnulus_subset_layer hε hz
  have hmin : min (Real.exp (-z 1)) (Real.exp (-z 2)) ≤ a ^ P := by
    by_contra H
    exact hn ⟨hzL, lt_min_iff.mp (lt_of_not_ge H)⟩
  have hl : (Real.exp (-z 1), Real.exp (-z 2)) ∈ restartShearCommonLabelSet ε a P :=
    ⟨⟨Real.exp_pos _, hzL.2.1⟩, ⟨Real.exp_pos _, hzL.2.2⟩, hmin⟩
  by_cases hs : 0 ≤ z 0
  · refine ⟨1, Real.exp (-z 1), Real.exp (-z 2), |z 0|, Or.inl rfl, hl,
      ⟨hz.1.1.le, hz.1.2⟩, ?_⟩
    ext i
    fin_cases i <;> simp [abs_of_nonneg hs]
  · refine ⟨-1, Real.exp (-z 1), Real.exp (-z 2), |z 0|, Or.inr rfl, hl,
      ⟨hz.1.1.le, hz.1.2⟩, ?_⟩
    ext i
    fin_cases i <;> simp [abs_of_neg (lt_of_not_ge hs)]

end BianchiIX
