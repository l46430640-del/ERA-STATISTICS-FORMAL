import BianchiIX.Dynamics.ShearSectionAbsolute
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

def shearSectionLayer (a ε : ℝ) : Set SectionCoordinates :=
  {z | |z 0| ∈ Icc a (2 * a) ∧ Real.exp (-z 1) ≤ 2 * ε * a ∧ Real.exp (-z 2) ≤ 2 * ε * a}

def shearUnselectedSection (a ε P : ℝ) : Set SectionCoordinates :=
  {z ∈ shearSectionLayer a ε | a ^ P < Real.exp (-z 1) ∧ a ^ P < Real.exp (-z 2)}

theorem measurableSet_shearSectionLayer (a ε : ℝ) : MeasurableSet (shearSectionLayer a ε) := by
  have hρ : Measurable (fun z : SectionCoordinates => |z 0|) := by fun_prop
  have h₂ : Measurable (fun z : SectionCoordinates => Real.exp (-z 1)) := by fun_prop
  have h₃ : Measurable (fun z : SectionCoordinates => Real.exp (-z 2)) := by fun_prop
  exact (measurableSet_Icc.preimage hρ).inter
    ((measurableSet_le h₂ measurable_const).inter (measurableSet_le h₃ measurable_const))

theorem measurableSet_shearUnselectedSection (a ε P : ℝ) : MeasurableSet (shearUnselectedSection a ε P) := by
  have h₂ : Measurable (fun z : SectionCoordinates => Real.exp (-z 1)) := by fun_prop
  have h₃ : Measurable (fun z : SectionCoordinates => Real.exp (-z 2)) := by fun_prop
  exact (measurableSet_shearSectionLayer a ε).inter
    ((measurableSet_lt measurable_const h₂).inter (measurableSet_lt measurable_const h₃))

theorem shearSectionLayer_selected_union_unselected (a ε P : ℝ) :
    shearSectionLayer a ε =
      {z ∈ shearSectionLayer a ε | min (Real.exp (-z 1)) (Real.exp (-z 2)) ≤ a ^ P} ∪
        shearUnselectedSection a ε P := by
  ext z
  change z ∈ shearSectionLayer a ε ↔
    (z ∈ shearSectionLayer a ε ∧ min _ _ ≤ a ^ P) ∨
      (z ∈ shearSectionLayer a ε ∧ a ^ P < Real.exp (-z 1) ∧ a ^ P < Real.exp (-z 2))
  rw [← lt_min_iff]
  exact ⟨fun hz => (le_or_gt (min _ _) (a ^ P)).elim (fun hb => Or.inl ⟨hz, hb⟩)
    (fun hb => Or.inr ⟨hz, hb⟩), fun hz => hz.elim And.left And.left⟩

/-- A lower bound on each weak wall makes its logarithmic coordinate bounded. -/
theorem logarithmic_wall_window {a P y : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hup : Real.exp (-y) ≤ 1) (hlow : a ^ P < Real.exp (-y)) :
    y ∈ Icc 0 (P * |Real.log a|) := by
  have hy0 : 0 ≤ y := by linarith only [Real.exp_le_one_iff.mp hup]
  rw [Real.rpow_def_of_pos ha, Real.exp_lt_exp] at hlow
  refine ⟨hy0, ?_⟩
  rw [abs_of_nonpos (Real.log_nonpos ha.le ha1)]
  nlinarith only [hlow]

theorem shearUnselectedSection_subset_box {a ε P : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hε : ε ≤ 1 / 64) :
    shearUnselectedSection a ε P ⊆
      Icc ![-2 * a, 0, 0] ![2 * a, P * |Real.log a|, P * |Real.log a|] := by
  intro z hz
  have hρ := abs_le.mp hz.1.1.2
  have hε2 : 2 * ε ≤ 1 := by linarith only [hε]
  have hupper : 2 * ε * a ≤ 1 := (mul_le_of_le_one_left ha.le hε2).trans ha1
  have h₂ := logarithmic_wall_window ha ha1 (hz.1.2.1.trans hupper) hz.2.1
  have h₃ := logarithmic_wall_window ha ha1 (hz.1.2.2.trans hupper) hz.2.2
  constructor <;> intro i <;> fin_cases i
  · change -2 * a ≤ z 0
    linarith only [hρ.1]
  · exact h₂.1
  · exact h₃.1
  · exact hρ.2
  · exact h₂.2
  · exact h₃.2

theorem volume_shear_log_box {a P : ℝ} (ha : 0 ≤ a) (hP : 0 ≤ P) :
    volume (Icc ![-2 * a, 0, 0] ![2 * a, P * |Real.log a|, P * |Real.log a|]) =
      ENNReal.ofReal (4 * P ^ 2 * a * |Real.log a| ^ 2) := by
  rw [Real.volume_Icc_pi]
  simp [Fin.prod_univ_succ]
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ P * |Real.log a|),
    ← ENNReal.ofReal_mul (by linarith : 0 ≤ 2 * a + 2 * a)]
  congr 1
  ring_nf
  simp only [sq_abs]

end BianchiIX
