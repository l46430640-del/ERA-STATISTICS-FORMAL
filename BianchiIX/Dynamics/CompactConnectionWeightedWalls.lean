import BianchiIX.Dynamics.CompactConnectionLogBounds
import BianchiIX.Dynamics.CompactConnectionBounds
import BianchiIX.Analysis.CompactConePowers

noncomputable section

namespace BianchiIX

/-- B.52 and the stronger strong-wall exponent, before division by the outgoing phase derivative. -/
theorem exists_compact_connection_weighted_wall_bounds :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 10000 ∧ ∀ η : ℝ, (0 < η ∧ η ≤ δ) →
      ∃ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ Y : CoreAngleState,
      (31 / 8 ≤ Y 0 ∧ Y 0 ≤ 6) → (0 < Y 1 ∧ Y 1 ≤ ε) → (0 < Y 2 ∧ Y 2 ≤ ε) →
      coreTailValid η Y ∧ entranceReturnValid (compactConnectionEntry η Y) ∧
        ContDiffAt ℝ 2 (compactConnectionState η) Y ∧
        0 < compactConnectionState η Y 1 ∧ 0 < compactConnectionState η Y 3 ∧
        ∀ v : CoreAngleState, v 0 = 1 → |v 1| ≤ Real.sqrt (Y 1) → |v 2| ≤ Real.sqrt (Y 2) →
        |fderiv ℝ (compactConnectionState η) Y v 1| ≤
          C * (Y 1 + Y 2) ^ (19 / 24 : ℝ) * Real.sqrt (compactConnectionState η Y 1) ∧
        |fderiv ℝ (compactConnectionState η) Y v 3| ≤
          C * (Y 1 + Y 2) ^ (2 / 9 : ℝ) * Real.sqrt (compactConnectionState η Y 3) := by
  obtain ⟨δ, hδ, hδsmall, HL⟩ := exists_compact_connection_log_bounds
  refine ⟨δ, hδ, hδsmall, ?_⟩
  intro η hη
  obtain ⟨εl, hεl, B, hB, HL'⟩ := HL η hη
  obtain ⟨εa, hεa, A, hA, HA⟩ := exists_compact_connection_return ⟨hη.1, hη.2.trans hδsmall⟩
  let ε := min εl (min εa 1)
  have hεl' : ε ≤ εl := min_le_left _ _
  have hεa' : ε ≤ εa := (min_le_right _ _).trans (min_le_left _ _)
  have hε1 : ε ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ε, lt_min hεl (lt_min hεa zero_lt_one), 4 * Real.sqrt A * B, by positivity, ?_⟩
  intro Y hk hu hw
  obtain ⟨htail, hreturn, _, hstate, _, _, _, _, hU, hW⟩ := HA Y hk
    ⟨hu.1, hu.2.trans hεa'⟩ ⟨hw.1, hw.2.trans hεa'⟩
  obtain ⟨_, _, _, HLogs⟩ := HL' Y hk ⟨hu.1, hu.2.trans hεl'⟩ ⟨hw.1, hw.2.trans hεl'⟩
  have hsu : Real.sqrt (compactConnectionState η Y 1) ≤
      Real.sqrt A * Real.sqrt (Y 1) * (Y 2) ^ (19 / 24 : ℝ) := by
    have H := Real.sqrt_le_sqrt hU.2.1
    rw [Real.sqrt_mul (mul_nonneg hA.le hu.1.le), Real.sqrt_mul hA.le,
      Real.sqrt_eq_rpow ((Y 2) ^ (19 / 12 : ℝ)), ← Real.rpow_mul hw.1.le] at H
    norm_num at H
    exact H
  have hsw : Real.sqrt (compactConnectionState η Y 3) ≤ Real.sqrt A * (Y 2) ^ (13 / 18 : ℝ) := by
    have H := Real.sqrt_le_sqrt hW.2.1
    rw [Real.sqrt_mul hA.le, Real.sqrt_eq_rpow ((Y 2) ^ (13 / 9 : ℝ)), ← Real.rpow_mul hw.1.le] at H
    norm_num at H
    exact H
  refine ⟨htail, hreturn, hstate, hU.1, hW.1, ?_⟩
  intro v hv0 hv1 hv2
  obtain ⟨Hlu, Hlw⟩ := HLogs v hv0 hv1 hv2
  let L := fderiv ℝ (compactConnectionLogWalls η) Y v
  have HcoefU : Real.sqrt (compactConnectionState η Y 1) * |L 0| ≤
      (4 * Real.sqrt A * B) * (Y 1 + Y 2) ^ (19 / 24 : ℝ) := by
    calc
      _ ≤ (Real.sqrt A * Real.sqrt (Y 1) * (Y 2) ^ (19 / 24 : ℝ)) *
          (B * (1 + |Real.log (Y 2)| + 1 / Real.sqrt (Y 1) + 1 / Real.sqrt (Y 2))) :=
        mul_le_mul hsu Hlu (abs_nonneg _) (by positivity [hu.1, hw.1])
      _ = (Real.sqrt A * B) * (Real.sqrt (Y 1) * (Y 2) ^ (19 / 24 : ℝ) *
          (1 + |Real.log (Y 2)| + 1 / Real.sqrt (Y 1) + 1 / Real.sqrt (Y 2))) := by ring
      _ ≤ (Real.sqrt A * B) * (4 * (Y 1 + Y 2) ^ (19 / 24 : ℝ)) :=
        mul_le_mul_of_nonneg_left (compact_strong_cone_power hu.1 hw.1 (hw.2.trans hε1)) (by positivity)
      _ = _ := by ring
  have HcoefW : Real.sqrt (compactConnectionState η Y 3) * |L 1| ≤
      (4 * Real.sqrt A * B) * (Y 1 + Y 2) ^ (2 / 9 : ℝ) := by
    calc
      _ ≤ (Real.sqrt A * (Y 2) ^ (13 / 18 : ℝ)) *
          (B * (1 + |Real.log (Y 2)| + 1 / Real.sqrt (Y 2))) :=
        mul_le_mul hsw Hlw (abs_nonneg _) (by positivity [hw.1])
      _ = (Real.sqrt A * B) * ((Y 2) ^ (13 / 18 : ℝ) * (1 + |Real.log (Y 2)| + 1 / Real.sqrt (Y 2))) := by ring
      _ ≤ (Real.sqrt A * B) * (3 * (Y 1 + Y 2) ^ (2 / 9 : ℝ)) :=
        mul_le_mul_of_nonneg_left (compact_weak_cone_power hu.1.le hw.1 (hw.2.trans hε1)) (by positivity)
      _ ≤ _ := by
        have H := mul_nonneg (mul_nonneg (Real.sqrt_nonneg A) hB.le)
          (Real.rpow_nonneg (add_nonneg hu.1.le hw.1.le) (2 / 9))
        nlinarith only [H]
  have HD := compactConnectionLogWalls_fderiv (hstate.differentiableAt (by norm_num)) hU.1.ne' hW.1.ne' v
  have huD : fderiv ℝ (compactConnectionState η) Y v 1 = compactConnectionState η Y 1 * L 0 := by
    have H := congrFun HD 0
    change L 0 = _ / _ at H
    rw [H]
    field_simp [hU.1.ne']
  have hwD : fderiv ℝ (compactConnectionState η) Y v 3 = compactConnectionState η Y 3 * L 1 := by
    have H := congrFun HD 1
    change L 1 = _ / _ at H
    rw [H]
    field_simp [hW.1.ne']
  constructor
  · rw [huD, abs_mul, abs_of_pos hU.1]
    have H := mul_le_mul_of_nonneg_left HcoefU (Real.sqrt_nonneg (compactConnectionState η Y 1))
    rw [← mul_assoc, Real.mul_self_sqrt hU.1.le] at H
    simpa only [mul_comm] using H
  · rw [hwD, abs_mul, abs_of_pos hW.1]
    have H := mul_le_mul_of_nonneg_left HcoefW (Real.sqrt_nonneg (compactConnectionState η Y 3))
    rw [← mul_assoc, Real.mul_self_sqrt hW.1.le] at H
    simpa only [mul_comm] using H

end BianchiIX
