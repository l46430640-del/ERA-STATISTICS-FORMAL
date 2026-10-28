import BianchiIX.Measure.AngularUnselectedGeometry
import BianchiIX.Measure.DyadicCover
import BianchiIX.Dynamics.MainWallReflection

noncomputable section

namespace BianchiIX

open Set MeasureTheory

def angularSection (d L : ℝ) : Set SectionCoordinates :=
  {z | max (Real.exp (-z 1)) (Real.exp (-z 2)) ≤ d ∧
    |z 0| ≤ L * max (Real.exp (-z 1)) (Real.exp (-z 2))}

def angularSectionAnnulus (a L : ℝ) : Set SectionCoordinates :=
  {z | max (Real.exp (-z 1)) (Real.exp (-z 2)) ∈ Ioc a (2 * a) ∧
    |z 0| ≤ L * max (Real.exp (-z 1)) (Real.exp (-z 2))}

theorem measurableSet_angularSection (d L : ℝ) : MeasurableSet (angularSection d L) := by
  have hm : Measurable (fun z : SectionCoordinates => max (Real.exp (-z 1)) (Real.exp (-z 2))) := by fun_prop
  exact (measurableSet_le hm measurable_const).inter (measurableSet_le (by fun_prop) (measurable_const.mul hm))

theorem measurableSet_angularSectionAnnulus (a L : ℝ) : MeasurableSet (angularSectionAnnulus a L) := by
  have hm : Measurable (fun z : SectionCoordinates => max (Real.exp (-z 1)) (Real.exp (-z 2))) := by fun_prop
  exact (measurableSet_Ioc.preimage hm).inter (measurableSet_le (by fun_prop) (measurable_const.mul hm))

theorem angularSection_dyadic_cover {d L : ℝ} (hd : 0 < d) :
    angularSection d L = ⋃ j : ℕ, angularSectionAnnulus (dyadicScale d j) L := by
  ext z
  constructor
  · intro hz
    have hm : 0 < max (Real.exp (-z 1)) (Real.exp (-z 2)) := lt_max_of_lt_left (Real.exp_pos _)
    obtain ⟨j, hj⟩ := exists_mem_dyadicScale_Ioc hd ⟨hm, hz.1⟩
    exact mem_iUnion_of_mem j ⟨hj, hz.2⟩
  · intro hz
    obtain ⟨j, hj⟩ := mem_iUnion.mp hz
    have hm : max (Real.exp (-z 1)) (Real.exp (-z 2)) ∈ Ioc 0 d :=
      iUnion_dyadicScale_Ioc hd ▸ mem_iUnion_of_mem j hj.1
    exact ⟨hm.2, hj.2⟩

theorem angularSection_dyadic_disjoint {d L : ℝ} (hd : 0 ≤ d) :
    Pairwise (fun j k : ℕ => Disjoint (angularSectionAnnulus (dyadicScale d j) L)
      (angularSectionAnnulus (dyadicScale d k) L)) := by
  intro j k hjk
  apply Set.disjoint_left.mpr
  intro z hz hw
  exact Set.disjoint_left.mp (pairwise_disjoint_dyadicScale_Ioc hd hjk) hz.1 hw.1

/-- Every selected physical point has a radial representation in one of the two actual axis orders. -/
theorem angularSection_selected_representation {a L P : ℝ} {z : SectionCoordinates}
    (hz : z ∈ angularSectionAnnulus a L) (hn : z ∉ angularUnselectedSection a L P) :
    ∃ θ ζ ρ : ℝ, |θ| ≤ L ∧ (0 < ζ ∧ ζ ≤ a ^ P) ∧ ρ ∈ Icc a (2 * a) ∧
      (z = ![θ * ρ, -Real.log ρ, -Real.log ζ] ∨
        z = mainWallReflection ![θ * ρ, -Real.log ρ, -Real.log ζ]) := by
  have hmin : min (Real.exp (-z 1)) (Real.exp (-z 2)) ≤ a ^ P := by
    by_contra h
    exact hn ⟨⟨hz.1.1.le, hz.1.2⟩, hz.2, lt_of_not_ge h⟩
  by_cases horder : Real.exp (-z 2) ≤ Real.exp (-z 1)
  · have hρ : 0 < Real.exp (-z 1) := Real.exp_pos _
    refine ⟨z 0 / Real.exp (-z 1), Real.exp (-z 2), Real.exp (-z 1), ?_,
      ⟨Real.exp_pos _, by simpa only [min_eq_right horder] using hmin⟩,
      ⟨by simpa only [max_eq_left horder] using hz.1.1.le,
        by simpa only [max_eq_left horder] using hz.1.2⟩, Or.inl ?_⟩
    · rw [abs_div, abs_of_pos hρ]
      exact (div_le_iff₀ hρ).mpr (by simpa only [max_eq_left horder] using hz.2)
    · ext i
      fin_cases i <;> simp [hρ.ne']
  · have horder' := (lt_of_not_ge horder).le
    have hρ : 0 < Real.exp (-z 2) := Real.exp_pos _
    refine ⟨-z 0 / Real.exp (-z 2), Real.exp (-z 1), Real.exp (-z 2), ?_,
      ⟨Real.exp_pos _, by simpa only [min_eq_left horder'] using hmin⟩,
      ⟨by simpa only [max_eq_right horder'] using hz.1.1.le,
        by simpa only [max_eq_right horder'] using hz.1.2⟩, Or.inr ?_⟩
    · rw [abs_div, abs_neg, abs_of_pos hρ]
      exact (div_le_iff₀ hρ).mpr (by simpa only [max_eq_right horder'] using hz.2)
    · ext i
      fin_cases i <;> simp [mainWallReflection, hρ.ne']

end BianchiIX
