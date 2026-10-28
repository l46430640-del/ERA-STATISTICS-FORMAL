import BianchiIX.Measure.ShearUnselectedGeometry
import BianchiIX.Measure.SmallSectionVolume

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

def angularUnselectedSection (a L P : ℝ) : Set SectionCoordinates :=
  {z | max (Real.exp (-z 1)) (Real.exp (-z 2)) ∈ Icc a (2 * a) ∧
    |z 0| ≤ L * max (Real.exp (-z 1)) (Real.exp (-z 2)) ∧
    a ^ P < min (Real.exp (-z 1)) (Real.exp (-z 2))}

def angularLogBox (a L P : ℝ) : Set SectionCoordinates :=
  Icc ![-2 * L * a, -Real.log (2 * a), 0] ![2 * L * a, -Real.log a, P * |Real.log a|]

def angularLogBoxSwapped (a L P : ℝ) : Set SectionCoordinates :=
  Icc ![-2 * L * a, 0, -Real.log (2 * a)] ![2 * L * a, P * |Real.log a|, -Real.log a]

theorem measurableSet_angularUnselectedSection (a L P : ℝ) : MeasurableSet (angularUnselectedSection a L P) := by
  have hρ : Measurable (fun z : SectionCoordinates => |z 0|) := by fun_prop
  have hmax : Measurable (fun z : SectionCoordinates => max (Real.exp (-z 1)) (Real.exp (-z 2))) := by fun_prop
  have hmin : Measurable (fun z : SectionCoordinates => min (Real.exp (-z 1)) (Real.exp (-z 2))) := by fun_prop
  exact (measurableSet_Icc.preimage hmax).inter
    ((measurableSet_le hρ (measurable_const.mul hmax)).inter (measurableSet_lt measurable_const hmin))

theorem logarithmic_wall_annulus {a y : ℝ} (ha : 0 < a) (hy : Real.exp (-y) ∈ Icc a (2 * a)) :
    y ∈ Icc (-Real.log (2 * a)) (-Real.log a) := by
  have hlow := Real.log_le_log ha hy.1
  have hup := Real.log_le_log (Real.exp_pos (-y)) hy.2
  rw [Real.log_exp] at hlow hup
  constructor <;> linarith only [hlow, hup]

/-- One logarithmic wall coordinate has the fixed width log 2 in each ordering. -/
theorem angularUnselectedSection_subset_boxes {a L P : ℝ}
    (ha : 0 < a) (ha2 : 2 * a ≤ 1) (hL : 0 ≤ L) :
    angularUnselectedSection a L P ⊆ angularLogBox a L P ∪ angularLogBoxSwapped a L P := by
  intro z hz
  have hn₂ : Real.exp (-z 1) ≤ 2 * a := (le_max_left _ _).trans hz.1.2
  have hn₃ : Real.exp (-z 2) ≤ 2 * a := (le_max_right _ _).trans hz.1.2
  have hlow := lt_min_iff.mp hz.2.2
  have ha1 : a ≤ 1 := by linarith only [ha, ha2]
  have hw₂ := logarithmic_wall_window ha ha1 (hn₂.trans ha2) hlow.1
  have hw₃ := logarithmic_wall_window ha ha1 (hn₃.trans ha2) hlow.2
  have hs : |z 0| ≤ 2 * L * a := calc
    _ ≤ _ := hz.2.1
    _ ≤ L * (2 * a) := mul_le_mul_of_nonneg_left hz.1.2 hL
    _ = _ := by ring
  have hs' := abs_le.mp hs
  by_cases ho : Real.exp (-z 2) ≤ Real.exp (-z 1)
  · have hm : Real.exp (-z 1) ∈ Icc a (2 * a) := by simpa only [max_eq_left ho] using hz.1
    have hw := logarithmic_wall_annulus ha hm
    left
    constructor <;> intro i <;> fin_cases i
    · change -2 * L * a ≤ z 0
      linarith only [hs'.1]
    · exact hw.1
    · exact hw₃.1
    · exact hs'.2
    · exact hw.2
    · exact hw₃.2
  · have hm : Real.exp (-z 2) ∈ Icc a (2 * a) := by
      simpa only [max_eq_right (le_of_not_ge ho)] using hz.1
    have hw := logarithmic_wall_annulus ha hm
    right
    constructor <;> intro i <;> fin_cases i
    · change -2 * L * a ≤ z 0
      linarith only [hs'.1]
    · exact hw₂.1
    · exact hw.1
    · exact hs'.2
    · exact hw₂.2
    · exact hw.2

theorem volume_angular_log_boxes {a L P : ℝ} (ha : 0 < a) (hL : 0 ≤ L) (hP : 0 ≤ P) :
    volume (angularLogBox a L P) = ENNReal.ofReal (4 * L * P * Real.log 2 * a * |Real.log a|) ∧
    volume (angularLogBoxSwapped a L P) = ENNReal.ofReal (4 * L * P * Real.log 2 * a * |Real.log a|) := by
  have hwidth : -Real.log a - -Real.log (2 * a) = Real.log 2 := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) ha.ne']
    ring
  have hlog : -Real.log (2 * a) ≤ -Real.log a := by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  have hLa : 0 ≤ L * a := mul_nonneg hL ha.le
  have hPa : 0 ≤ P * |Real.log a| := mul_nonneg hP (abs_nonneg _)
  constructor
  · have hb : (![-2 * L * a, -Real.log (2 * a), 0] : SectionCoordinates) ≤
        ![2 * L * a, -Real.log a, P * |Real.log a|] := by
      intro i
      fin_cases i
      · change -2 * L * a ≤ 2 * L * a
        nlinarith only [hLa]
      · exact hlog
      · exact hPa
    rw [angularLogBox, volume_three_box hb]
    change ENNReal.ofReal ((2 * L * a - -2 * L * a) * (-Real.log a - -Real.log (2 * a)) *
      (P * |Real.log a| - 0)) = _
    rw [hwidth]
    congr 1
    ring
  · have hb : (![-2 * L * a, 0, -Real.log (2 * a)] : SectionCoordinates) ≤
        ![2 * L * a, P * |Real.log a|, -Real.log a] := by
      intro i
      fin_cases i
      · change -2 * L * a ≤ 2 * L * a
        nlinarith only [hLa]
      · exact hPa
      · exact hlog
    rw [angularLogBoxSwapped, volume_three_box hb]
    change ENNReal.ofReal ((2 * L * a - -2 * L * a) * (P * |Real.log a| - 0) *
      (-Real.log a - -Real.log (2 * a))) = _
    rw [hwidth]
    congr 1
    ring

end BianchiIX
