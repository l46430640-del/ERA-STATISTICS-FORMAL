import BianchiIX.Measure.ShearUnselectedGeometry
import BianchiIX.Measure.MainWallMeasure
import BianchiIX.Measure.DyadicFlux

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

/-- All unselected labels, with either shear sign, have finite physical flux without a restart assumption. -/
theorem mainWallMeasure_shearUnselectedSection_le {h a ε P : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1 / 8) (ha : 0 < a) (hah : a ≤ h / 8)
    (hε : 0 ≤ ε ∧ ε ≤ 1 / 64) (hP : 0 ≤ P) :
    mainWallMeasure h (shearUnselectedSection a ε P) ≤
      ENNReal.ofReal (12 * P ^ 2 * a * |Real.log a| ^ 2) := by
  have ha1 : a ≤ 1 := by linarith only [hah, hh1]
  have hA := measurableSet_shearUnselectedSection a ε P
  have H (z : SectionCoordinates) (hz : z ∈ shearUnselectedSection a ε P) :=
    mainWall_small_shear_abs hh hh1 ha hah hε hz.1.1 hz.1.2.1 hz.1.2.2
  calc
    _ = ∫⁻ z in shearUnselectedSection a ε P, ENNReal.ofReal (mainWallChartDensity h z) :=
      mainWallMeasure_apply hA (fun z hz => (H z hz).1)
    _ ≤ ∫⁻ _ in shearUnselectedSection a ε P, ENNReal.ofReal (3 : ℝ) :=
      setLIntegral_mono' hA (fun z hz => ENNReal.ofReal_le_ofReal (H z hz).2.2)
    _ = ENNReal.ofReal (3 : ℝ) * volume (shearUnselectedSection a ε P) := by simp
    _ ≤ ENNReal.ofReal (3 : ℝ) * volume
        (Icc ![-2 * a, 0, 0] ![2 * a, P * |Real.log a|, P * |Real.log a|]) :=
      mul_le_mul' le_rfl (measure_mono (shearUnselectedSection_subset_box ha ha1 hε.2))
    _ = _ := by
      rw [volume_shear_log_box ha.le hP, ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      ring

theorem mainWallMeasure_shearUnselectedSection_dyadic {h d ε P : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1 / 8) (hd : 0 < d) (hdh : d ≤ h / 8)
    (hε : 0 ≤ ε ∧ ε ≤ 1 / 64) (hP : 0 ≤ P) :
    let E := fun j => shearUnselectedSection (dyadicScale d j) ε P
    MeasurableSet (⋃ j : ℕ, E j) ∧
      (∑' j : ℕ, mainWallMeasure h (E j)) ≤ ENNReal.ofReal (132 * P ^ 2 * d * (1 + |Real.log d|) ^ 2) ∧
      mainWallMeasure h (⋃ j : ℕ, E j) ≤ ENNReal.ofReal (132 * P ^ 2 * d * (1 + |Real.log d|) ^ 2) ∧
      mainWallMeasure h (⋃ j : ℕ, E j) ≠ ⊤ := by
  intro E
  have hd1 : d ≤ 1 := by linarith only [hdh, hh1]
  have Hlayer (j : ℕ) : mainWallMeasure h (E j) ≤ ENNReal.ofReal
      ((12 * P ^ 2) * (dyadicScale d j * (1 + |Real.log (dyadicScale d j)|) ^ 2)) := by
    have ha := dyadicScale_pos hd j
    refine (mainWallMeasure_shearUnselectedSection_le hh hh1 ha
      ((dyadicScale_le hd.le j).trans hdh) hε hP).trans ?_
    apply ENNReal.ofReal_le_ofReal
    have H := pow_le_pow_left₀ (abs_nonneg (Real.log (dyadicScale d j)))
      (show |Real.log (dyadicScale d j)| ≤ 1 + |Real.log (dyadicScale d j)| by linarith) 2
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left H
      (show 0 ≤ 12 * P ^ 2 * dyadicScale d j by positivity)
  have Hsum : (∑' j : ℕ, mainWallMeasure h (E j)) ≤
      ENNReal.ofReal (132 * P ^ 2 * d * (1 + |Real.log d|) ^ 2) := calc
    _ ≤ _ := ENNReal.tsum_le_tsum Hlayer
    _ ≤ _ := dyadic_flux_budget hd hd1 (show 0 ≤ 12 * P ^ 2 by positivity)
    _ = _ := by congr 1; ring
  have Hunion := (measure_iUnion_le E).trans Hsum
  exact ⟨MeasurableSet.iUnion (fun j => measurableSet_shearUnselectedSection (dyadicScale d j) ε P),
    Hsum, Hunion, ne_top_of_le_ne_top ENNReal.ofReal_ne_top Hunion⟩

end BianchiIX
