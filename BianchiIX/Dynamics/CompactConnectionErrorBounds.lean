import BianchiIX.Analysis.CompactPhaseComposition
import BianchiIX.Dynamics.CompactConnectionError
import BianchiIX.Dynamics.CompactConnectionReturn
import BianchiIX.Dynamics.CompactEntrancePhaseBounds

noncomputable section

namespace BianchiIX

/-- All four estimates in B.50 hold for the exact composed Einstein return. -/
theorem exists_compact_connection_error_bounds :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 10000 ∧ ∀ η : ℝ, (0 < η ∧ η ≤ δ) →
      ∃ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ Y : CoreAngleState,
      (31 / 8 ≤ Y 0 ∧ Y 0 ≤ 6) → (0 < Y 1 ∧ Y 1 ≤ ε) → (0 < Y 2 ∧ Y 2 ≤ ε) →
      coreTailValid η Y ∧ entranceReturnValid (compactConnectionEntry η Y) ∧
        ContDiffAt ℝ 2 (compactConnectionError η) Y ∧
        |compactConnectionError η Y| + |fderiv ℝ (compactConnectionError η) Y (Pi.single 0 1)| ≤
          C * Y 2 * (Y 1 + Y 2) ∧
        |fderiv ℝ (compactConnectionError η) Y (Pi.single 1 1)| ≤ C * Y 2 ∧
        |fderiv ℝ (compactConnectionError η) Y (Pi.single 2 1)| ≤ C * (Y 1 + Y 2) := by
  obtain ⟨B, hB, δ, hδ, hδsmall, HB⟩ := exists_entrance_compact_phase_bounds
  refine ⟨δ, hδ, hδsmall, ?_⟩
  intro η hη
  obtain ⟨εc, hεc, A, hA, HC⟩ := exists_compact_connection_coordinate_bounds ⟨hη.1, hη.2.trans hδsmall⟩
  obtain ⟨εe, hεe, _, _, HE⟩ := exists_compact_connection_entrance_data ⟨hδ, hδsmall⟩ hη
  let ε := min εc (min εe (1 / 2))
  have hεc' : ε ≤ εc := min_le_left _ _
  have hεe' : ε ≤ εe := (min_le_right _ _).trans (min_le_left _ _)
  have hεhalf : ε ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hApos : 0 < A := by linarith only [hA]
  have hBpos : 0 < B := by linarith only [hB]
  refine ⟨ε, lt_min hεc (lt_min hεe (by norm_num)), B * A ^ 2 * (A + 3), by positivity, ?_⟩
  intro Y hk hu hw
  obtain ⟨htail, _, hentry, hrange, hm, hU, hV, hW, _, _⟩ := HE Y hk
    ⟨hu.1, hu.2.trans hεe'⟩ ⟨hw.1, hw.2.trans hεe'⟩
  obtain ⟨hvalid, hR, hDR, hBi⟩ := HC Y hk
    (by rw [abs_of_pos hu.1]; exact hu.2.trans hεc')
    (by rw [abs_of_pos hw.1]; exact hw.2.trans hεc')
  let y := compactConnectionEntry η Y
  have hv : 0 < y 2 ∧ y 2 < 1 := ⟨hV.1, by linarith only [hV.2]⟩
  have hww : 0 < y 3 ∧ y 3 ≤ δ := by
    change 0 < compactConnectionEntry η Y 3 ∧ compactConnectionEntry η Y 3 ≤ δ
    rw [hW]
    exact hη
  obtain ⟨Ψ, HΨ, hF, H0, Hr, Hu, Hv⟩ := HB y hrange.1 hm hU hv hww
  let F := fun z => coreRadius (entranceReturnState (Ψ z) 0) (entranceReturnState (Ψ z) 2)
  let z := compactConnectionCoordinates η Y
  have hbase : z = entranceRadialCoordinates y := compactConnectionCoordinates_eq htail
  have hdiff := compactConnectionError_differential HΨ hentry.continuousAt hvalid hR
    (fun i => (hBi i).1) hF
  have hreturn : entranceReturnValid y := (entranceReturn_regular hrange.1 hm
    ⟨hU.1.le, hU.2.trans hδsmall⟩ hv ⟨hww.1.le, hww.2.trans hδsmall⟩).1
  refine ⟨htail, hreturn, hdiff.1, ?_⟩
  have hform := coreTail_reflected_multiplier_state htail
  have hUb : y 1 ≤ A * Y 1 := by
    change compactConnectionEntry η Y 1 ≤ _
    rw [show compactConnectionEntry η Y 1 = Y 1 * coreTailMultiplier η Y 0 from congrFun hform 1, mul_comm A]
    exact mul_le_mul_of_nonneg_left (hBi 0).2.2.1 hu.1.le
  have hVb : y 2 ≤ A * Y 2 := by
    change compactConnectionEntry η Y 2 ≤ _
    rw [show compactConnectionEntry η Y 2 = Y 2 * coreTailMultiplier η Y 1 from congrFun hform 2, mul_comm A]
    exact mul_le_mul_of_nonneg_left (hBi 1).2.2.1 hw.1.le
  have hsum : y 1 + y 2 ≤ A * (Y 1 + Y 2) := by nlinarith only [hUb, hVb]
  have hbudget : B * y 2 * (y 1 + y 2) ≤ B * A ^ 2 * Y 2 * (Y 1 + Y 2) := by
    calc
      _ = B * (y 2 * (y 1 + y 2)) := by ring
      _ ≤ B * ((A * Y 2) * (A * (Y 1 + Y 2))) := mul_le_mul_of_nonneg_left
        (mul_le_mul hVb hsum (add_nonneg hU.1.le hv.1.le) (by positivity [hw.1])) hBpos.le
      _ = _ := by ring
  have heq := (compactConnectionError_chart_germ HΨ hentry.continuousAt hvalid).self_of_nhds
  have hErr : |compactConnectionError η Y| ≤ B * A ^ 2 * Y 2 * (Y 1 + Y 2) := by
    rw [heq]
    change |F z - z 0| ≤ _
    rw [hbase]
    exact H0.trans hbudget
  have hLr : |fderiv ℝ F z (Pi.single 0 1) - 1| ≤ B * A ^ 2 * Y 2 * (Y 1 + Y 2) := by
    rw [hbase]
    exact Hr.trans hbudget
  have hLu : |fderiv ℝ F z (Pi.single 1 1)| ≤ B * A * Y 2 := by
    rw [hbase]
    exact Hu.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hVb hBpos.le)
  have hLv : |fderiv ℝ F z (Pi.single 2 1)| ≤ B * A * (Y 1 + Y 2) := by
    rw [hbase]
    exact Hv.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hsum hBpos.le)
  let p := fun j : Fin 3 => fderiv ℝ (compactConnectionFinitePhase η) Y (Pi.single j 1)
  let q := fun j : Fin 3 => fderiv ℝ (fun Z => coreTailMultiplier η Z 0) Y (Pi.single j 1)
  let r := fun j : Fin 3 => fderiv ℝ (fun Z => coreTailMultiplier η Z 1) Y (Pi.single j 1)
  have hcol (L : CoreAngleState →L[ℝ] ℝ) (hL : ‖L‖ ≤ A) (j : Fin 3) : |L (Pi.single j 1)| ≤ A := by
    have H := L.le_opNorm (Pi.single j 1)
    simp only [Real.norm_eq_abs, Pi.norm_single, norm_one, mul_one] at H
    exact H.trans hL
  have hb : Y 1 + Y 2 ≤ 1 := by linarith only [hu.2.trans hεhalf, hw.2.trans hεhalf]
  have hBa (i : Fin 2) : |coreTailMultiplier η Y i| ≤ A := by
    rw [abs_of_pos (hBi i).2.1]
    exact (hBi i).2.2.1
  have H := compact_phase_composition_bounds p q r hApos.le hBpos.le hu.1.le hw.1.le hb
    (hcol _ hDR) (hcol _ (hBi 0).2.2.2) (hcol _ (hBi 1).2.2.2)
    (hBa 0) (hBa 1) hErr hLr hLu hLv
  let D := fun j : Fin 3 => (fderiv ℝ F z (Pi.single 0 1) - 1) * p j +
    fderiv ℝ F z (Pi.single 1 1) * (Y 1 * q j) + fderiv ℝ F z (Pi.single 2 1) * (Y 2 * r j)
  have H0' : fderiv ℝ (compactConnectionError η) Y (Pi.single 0 1) = D 0 := by
    rw [hdiff.2 (Pi.single 0 1)]
    change (fderiv ℝ F z (Pi.single 0 1) - 1) * p 0 +
      fderiv ℝ F z (Pi.single 1 1) * (0 * coreTailMultiplier η Y 0 + Y 1 * q 0) +
      fderiv ℝ F z (Pi.single 2 1) * (0 * coreTailMultiplier η Y 1 + Y 2 * r 0) = D 0
    dsimp only [D]; ring
  have H1' : fderiv ℝ (compactConnectionError η) Y (Pi.single 1 1) =
      D 1 + fderiv ℝ F z (Pi.single 1 1) * coreTailMultiplier η Y 0 := by
    rw [hdiff.2 (Pi.single 1 1)]
    change (fderiv ℝ F z (Pi.single 0 1) - 1) * p 1 +
      fderiv ℝ F z (Pi.single 1 1) * (1 * coreTailMultiplier η Y 0 + Y 1 * q 1) +
      fderiv ℝ F z (Pi.single 2 1) * (0 * coreTailMultiplier η Y 1 + Y 2 * r 1) = _
    dsimp only [D]; ring
  have H2' : fderiv ℝ (compactConnectionError η) Y (Pi.single 2 1) =
      D 2 + fderiv ℝ F z (Pi.single 2 1) * coreTailMultiplier η Y 1 := by
    rw [hdiff.2 (Pi.single 2 1)]
    change (fderiv ℝ F z (Pi.single 0 1) - 1) * p 2 +
      fderiv ℝ F z (Pi.single 1 1) * (0 * coreTailMultiplier η Y 0 + Y 1 * q 2) +
      fderiv ℝ F z (Pi.single 2 1) * (1 * coreTailMultiplier η Y 1 + Y 2 * r 2) = _
    dsimp only [D]; ring
  rw [H0', H1', H2']
  exact H

end BianchiIX
