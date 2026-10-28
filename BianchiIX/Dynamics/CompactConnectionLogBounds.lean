import BianchiIX.Dynamics.CompactConnectionLogDifferential
import BianchiIX.Dynamics.CompactConnectionTangent
import BianchiIX.Dynamics.CompactConnectionReturn
import BianchiIX.Dynamics.EntranceFullReturnColumns

noncomputable section

namespace BianchiIX

/-- The actual compact connection has the logarithmic cone bounds used before B.52. -/
theorem exists_compact_connection_log_bounds :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 10000 ∧ ∀ η : ℝ, (0 < η ∧ η ≤ δ) →
      ∃ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ Y : CoreAngleState,
      (31 / 8 ≤ Y 0 ∧ Y 0 ≤ 6) → (0 < Y 1 ∧ Y 1 ≤ ε) → (0 < Y 2 ∧ Y 2 ≤ ε) →
      coreTailValid η Y ∧ entranceReturnValid (compactConnectionEntry η Y) ∧
        DifferentiableAt ℝ (compactConnectionLogWalls η) Y ∧
        ∀ v : CoreAngleState, v 0 = 1 → |v 1| ≤ Real.sqrt (Y 1) → |v 2| ≤ Real.sqrt (Y 2) →
        |fderiv ℝ (compactConnectionLogWalls η) Y v 0| ≤
          C * (1 + |Real.log (Y 2)| + 1 / Real.sqrt (Y 1) + 1 / Real.sqrt (Y 2)) ∧
        |fderiv ℝ (compactConnectionLogWalls η) Y v 1| ≤
          C * (1 + |Real.log (Y 2)| + 1 / Real.sqrt (Y 2)) := by
  obtain ⟨B, hB, δ, hδ, hδsmall, HB⟩ := exists_entrance_return_full_columns
  refine ⟨δ, hδ, hδsmall, ?_⟩
  intro η hη
  obtain ⟨εt, hεt, A, hA, HT⟩ := exists_compact_connection_tangent_bounds ⟨hη.1, hη.2.trans hδsmall⟩
  obtain ⟨εe, hεe, _, _, HE⟩ := exists_compact_connection_entrance_data ⟨hδ, hδsmall⟩ hη
  let ε := min εt εe
  have hεt' : ε ≤ εt := min_le_left _ _
  have hεe' : ε ≤ εe := min_le_right _ _
  have hA0 : 0 ≤ A := by linarith only [hA]
  refine ⟨ε, lt_min hεt hεe, B * A ^ 2 + 6 * (B * A) + A + 4 * B + 1, by positivity, ?_⟩
  intro Y hk hu hw
  obtain ⟨htail, _, hentry, hrange, hm, hU, hV, hW, _, _⟩ := HE Y hk
    ⟨hu.1, hu.2.trans hεe'⟩ ⟨hw.1, hw.2.trans hεe'⟩
  obtain ⟨hvalid, hc, hlog, HD⟩ := HT Y hk ⟨hu.1, hu.2.trans hεt'⟩ ⟨hw.1, hw.2.trans hεt'⟩
  let y := compactConnectionEntry η Y
  have hv : 0 < y 2 ∧ y 2 < 1 := ⟨hV.1, by linarith only [hV.2]⟩
  have hww : 0 < y 3 ∧ y 3 ≤ δ := by
    change 0 < compactConnectionEntry η Y 3 ∧ compactConnectionEntry η Y 3 ≤ δ
    rw [hW]
    exact hη
  have hu' : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000 := ⟨hU.1.le, hU.2.trans hδsmall⟩
  have hw' : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000 := ⟨hww.1.le, hww.2.trans hδsmall⟩
  obtain ⟨Ψ, HΨ, _, HU, HW⟩ := HB y 1 hrange.1 hm hU hv hww (Or.inl rfl)
  let F := fun z => entranceLogWalls 1 (entranceReturnState (Ψ z))
  let z := compactConnectionCoordinates η Y
  have hbase : z = entranceRadialCoordinates y := compactConnectionCoordinates_eq htail
  have hzu : z 1 = y 1 := congrFun hbase 1
  have hzv : z 2 = y 2 := congrFun hbase 2
  have HR := entranceReturn_regular hrange.1 hm hu' hv hw'
  have hpos := entranceReturn_walls_pos hrange.1 hm ⟨hU.1, hu'.2⟩ hv ⟨hww.1, hw'.2⟩
    (entranceReturnTime y) ⟨HR.1.1.1.1.le, le_rfl⟩
  have hLp : DifferentiableAt ℝ (entranceLogWalls 1) (entranceReturnState (Ψ (entranceRadialCoordinates y))) := by
    rw [HΨ.apply_base]
    exact (hasFDerivAt_entranceLogWalls 1 hpos.1.ne' hpos.2.2.ne').differentiableAt
  have hLf : DifferentiableAt ℝ F (entranceRadialCoordinates y) :=
    hLp.comp (entranceRadialCoordinates y) (g := entranceLogWalls 1)
      (f := fun z => entranceReturnState (Ψ z)) (HΨ.hasFDerivAt_return hrange.1 hm hu' hv hw').differentiableAt
  have Hdiff := compactConnectionLogWalls_differential HΨ hentry.continuousAt hvalid
    (hc.differentiableAt (by norm_num)) hLf
  refine ⟨htail, HR.1, Hdiff.1, ?_⟩
  intro v hv0 hv1 hv2
  obtain ⟨hd0, hd1, hdu, hdv, hd3⟩ := HD v hv0 hv1 hv2
  let J := fderiv ℝ F z
  let d := fderiv ℝ (compactConnectionCoordinates η) Y v
  have hk2 : 1 ≤ coreRadius (y 0) (y 2) ^ 2 := by nlinarith only [hrange.1]
  have hL0 : 0 ≤ -Real.log (y 2) := neg_nonneg.mpr (Real.log_nonpos hv.1.le hv.2.le)
  have HUr : |J (Pi.single 0 1) 0| ≤ B * (-Real.log (y 2)) := by
    change |fderiv ℝ F z (Pi.single 0 1) 0| ≤ _
    rw [hbase]
    exact HU.1
  have HUu : |J (Pi.single 1 1) 0 - 1 / y 1| ≤ B := by
    change |fderiv ℝ F z (Pi.single 1 1) 0 - 1 / y 1| ≤ _
    rw [hbase]
    exact HU.2.1
  have HUv : |J (Pi.single 2 1) 0| ≤ 4 * B / y 2 := by
    change |fderiv ℝ F z (Pi.single 2 1) 0| ≤ _
    rw [hbase]
    exact HU.2.2.1.trans (div_le_div_of_nonneg_right (by nlinarith only [mul_le_mul_of_nonneg_left hrange.2.le hB.le]) hv.1.le)
  have HWr : |J (Pi.single 0 1) 1| ≤ B * (-Real.log (y 2)) := by
    change |fderiv ℝ F z (Pi.single 0 1) 1| ≤ _
    rw [hbase]
    exact HW.1.trans (div_le_self (mul_nonneg hB.le hL0) hk2)
  have HWu : |J (Pi.single 1 1) 1| ≤ B := by
    change |fderiv ℝ F z (Pi.single 1 1) 1| ≤ _
    rw [hbase]
    exact HW.2.1.trans (div_le_self hB.le hk2)
  have HWv : |J (Pi.single 2 1) 1| ≤ B / y 2 := by
    change |fderiv ℝ F z (Pi.single 2 1) 1| ≤ _
    rw [hbase]
    exact HW.2.2.1
  change -Real.log (z 2) ≤ _ at hlog
  change |d 1| ≤ z 1 * _ at hdu
  change |d 2| ≤ z 2 * _ at hdv
  rw [hzv] at hlog hdv
  rw [hzu] at hdu
  have H := compact_log_composition_bounds J d hA0 hB.le hU.1 hv.1 (abs_nonneg _)
    (by positivity [hu.1] : 0 ≤ 1 / Real.sqrt (Y 1)) (by positivity [hw.1] : 0 ≤ 1 / Real.sqrt (Y 2))
    hlog hd0 hd1 hdu hdv hd3 HUr HUu HUv HWr HWu HWv
  rw [Hdiff.2 v]
  exact H

end BianchiIX
