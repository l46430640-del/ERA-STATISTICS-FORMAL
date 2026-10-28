import BianchiIX.Measure.AngularUnselectedGeometry
import BianchiIX.Measure.DyadicLogFlux

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

/-- Both weak-wall orderings and both shear signs have a linear-logarithmic unselected flux bound. -/
theorem mainWallMeasure_angularUnselectedSection_le {h a L P : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1 / 8) (ha : 0 < a) (hah : a ≤ h / 16)
    (hL : 0 ≤ L) (hLa : 2 * L * a ≤ 1 / 8) (hP : 0 ≤ P) :
    mainWallMeasure h (angularUnselectedSection a L P) ≤
      ENNReal.ofReal (24 * L * P * Real.log 2 * a * |Real.log a|) := by
  have ha2 : 2 * a ≤ 1 := by linarith only [hah, hh1]
  have hsmall (z : SectionCoordinates) (hz : z ∈ angularUnselectedSection a L P) :
      |z 0| ≤ 1 / 8 ∧ Real.exp (-z 1) ≤ h / 8 ∧ Real.exp (-z 2) ≤ h / 8 := by
    have hs : |z 0| ≤ 2 * L * a := calc
      _ ≤ _ := hz.2.1
      _ ≤ L * (2 * a) := mul_le_mul_of_nonneg_left hz.1.2 hL
      _ = _ := by ring
    have hm : max (Real.exp (-z 1)) (Real.exp (-z 2)) ≤ h / 8 := by linarith only [hz.1.2, hah]
    exact ⟨hs.trans hLa, (le_max_left _ _).trans hm, (le_max_right _ _).trans hm⟩
  have hbox := volume_angular_log_boxes ha hL hP
  have hW : 0 ≤ 4 * L * P * Real.log 2 * a * |Real.log a| :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hL) hP)
      (Real.log_nonneg (by norm_num))) ha.le) (abs_nonneg _)
  calc
    _ ≤ ENNReal.ofReal (3 : ℝ) * volume (angularUnselectedSection a L P) :=
      mainWallMeasure_le_three_volume hh hh1 (measurableSet_angularUnselectedSection a L P) hsmall
    _ ≤ ENNReal.ofReal (3 : ℝ) *
        (volume (angularLogBox a L P) + volume (angularLogBoxSwapped a L P)) :=
      mul_le_mul' le_rfl ((measure_mono (angularUnselectedSection_subset_boxes ha ha2 hL)).trans (measure_union_le _ _))
    _ = _ := by
      rw [hbox.1, hbox.2, ← ENNReal.ofReal_add hW hW, ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      ring

theorem mainWallMeasure_angularUnselectedSection_dyadic {h d L P : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1 / 8) (hd : 0 < d) (hdh : d ≤ h / 16)
    (hL : 0 ≤ L) (hLd : 2 * L * d ≤ 1 / 8) (hP : 0 ≤ P) :
    let E := fun j => angularUnselectedSection (dyadicScale d j) L P
    let C := 24 * L * P * Real.log 2
    MeasurableSet (⋃ j : ℕ, E j) ∧
      (∑' j : ℕ, mainWallMeasure h (E j)) ≤ ENNReal.ofReal (C * d * (|Real.log d| + 2 * Real.log 2)) ∧
      mainWallMeasure h (⋃ j : ℕ, E j) ≤ ENNReal.ofReal (C * d * (|Real.log d| + 2 * Real.log 2)) ∧
      mainWallMeasure h (⋃ j : ℕ, E j) ≠ ⊤ := by
  intro E C
  have hd1 : d ≤ 1 := by linarith only [hdh, hh1]
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hL) hP) (Real.log_nonneg (by norm_num))
  have Hlayer (j : ℕ) : mainWallMeasure h (E j) ≤
      ENNReal.ofReal (C * (dyadicScale d j * |Real.log (dyadicScale d j)|)) := by
    have ha := dyadicScale_pos hd j
    have hLa : 2 * L * dyadicScale d j ≤ 1 / 8 :=
      (mul_le_mul_of_nonneg_left (dyadicScale_le hd.le j) (mul_nonneg (by norm_num) hL)).trans hLd
    simpa only [E, C, mul_assoc] using mainWallMeasure_angularUnselectedSection_le hh hh1 ha
      ((dyadicScale_le hd.le j).trans hdh) hL hLa hP
  have Hsum : (∑' j : ℕ, mainWallMeasure h (E j)) ≤
      ENNReal.ofReal (C * d * (|Real.log d| + 2 * Real.log 2)) :=
    (ENNReal.tsum_le_tsum Hlayer).trans_eq (dyadic_log_flux_sum hd hd1 hC)
  have Hunion := (measure_iUnion_le E).trans Hsum
  exact ⟨MeasurableSet.iUnion (fun j => measurableSet_angularUnselectedSection (dyadicScale d j) L P),
    Hsum, Hunion, ne_top_of_le_ne_top ENNReal.ofReal_ne_top Hunion⟩

end BianchiIX
