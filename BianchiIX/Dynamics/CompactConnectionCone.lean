import BianchiIX.Dynamics.CompactConnectionWeightedWalls
import BianchiIX.Dynamics.CompactConnectionPhaseBounds
import BianchiIX.Analysis.CompactPhaseCone

noncomputable section

namespace BianchiIX

theorem exists_compact_connection_phase_cone_bounds :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 10000 ∧ ∀ η : ℝ, (0 < η ∧ η ≤ δ) →
      ∃ ε > (0 : ℝ), ε ≤ 1 / 2 ∧ ∃ C > (0 : ℝ), ∀ Y : CoreAngleState,
      (31 / 8 ≤ Y 0 ∧ Y 0 ≤ 6) → (0 < Y 1 ∧ Y 1 ≤ ε) → (0 < Y 2 ∧ Y 2 ≤ ε) →
      ContDiffAt ℝ 2 (compactConnectionPhase η) Y ∧
        ∀ v : CoreAngleState, v 0 = 1 → |v 1| ≤ Real.sqrt (Y 1) → |v 2| ≤ Real.sqrt (Y 2) →
        1 / 2 ≤ fderiv ℝ (compactConnectionPhase η) Y v ∧
        |fderiv ℝ (compactConnectionPhase η) Y v - 1| ≤ C * (Real.sqrt (Y 1) + Y 2 * Real.sqrt (Y 2)) := by
  obtain ⟨δ, hδ, hδsmall, HP⟩ := exists_compact_connection_phase_bounds
  refine ⟨δ, hδ, hδsmall, ?_⟩
  intro η hη
  obtain ⟨εp, hεp, P, hP, HP'⟩ := HP η hη
  let C := 4 * P + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  let a := 1 / (4 * C)
  have ha : 0 < a := by dsimp only [a]; positivity
  have habudget : 2 * C * a = 1 / 2 := by dsimp only [a]; field_simp; norm_num
  let ε := min εp (min (1 / 2) (a ^ 2))
  have hεp' : ε ≤ εp := min_le_left _ _
  have hεhalf : ε ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hεroot : Real.sqrt ε ≤ a := Real.sqrt_le_iff.mpr
    ⟨ha.le, (min_le_right _ _).trans (min_le_right _ _)⟩
  refine ⟨ε, lt_min hεp (lt_min (by norm_num) (sq_pos_of_pos ha)), hεhalf, C, hC, ?_⟩
  intro Y hk hu hw
  obtain ⟨_, _, hphase, _, Hr, Ht⟩ := HP' Y hk ⟨hu.1, hu.2.trans hεp'⟩ ⟨hw.1, hw.2.trans hεp'⟩
  have hu1 : Y 1 ≤ 1 := by linarith only [hu.2, hεhalf]
  have hw1 : Y 2 ≤ 1 := by linarith only [hw.2, hεhalf]
  refine ⟨hphase, ?_⟩
  intro v hv0 hv1 hv2
  have H := compact_phase_cone_direction (fderiv ℝ (compactConnectionPhase η) Y) v hP.le
    (by linarith only [hk.1]) ⟨hu.1.le, hu1⟩ ⟨hw.1.le, hw1⟩ hv0 hv1 hv2 Hr Ht
  change |fderiv ℝ (compactConnectionPhase η) Y v - 1| ≤ C * (Real.sqrt (Y 1) + Y 2 * Real.sqrt (Y 2)) at H
  have hsize : Real.sqrt (Y 1) + Y 2 * Real.sqrt (Y 2) ≤ 2 * a := by
    have hsu := (Real.sqrt_le_sqrt hu.2).trans hεroot
    have hsw := (Real.sqrt_le_sqrt hw.2).trans hεroot
    have H' := mul_le_mul_of_nonneg_right hw1 (Real.sqrt_nonneg (Y 2))
    linarith only [hsu, hsw, H']
  have Hsmall := H.trans (mul_le_mul_of_nonneg_left hsize hC.le)
  have Hsmall' : |fderiv ℝ (compactConnectionPhase η) Y v - 1| ≤ 1 / 2 := by
    nlinarith only [Hsmall, habudget]
  exact ⟨by linarith only [(abs_le.mp Hsmall').1], H⟩

/-- The actual compact connection strictly preserves the square-root cone, uniformly over wall ratios. -/
theorem exists_compact_connection_cone :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 10000 ∧ ∀ η : ℝ, (0 < η ∧ η ≤ δ) →
      ∃ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ Y : CoreAngleState,
      (31 / 8 ≤ Y 0 ∧ Y 0 ≤ 6) → (0 < Y 1 ∧ Y 1 ≤ ε) → (0 < Y 2 ∧ Y 2 ≤ ε) →
      coreTailValid η Y ∧ entranceReturnValid (compactConnectionEntry η Y) ∧
        ContDiffAt ℝ 2 (compactConnectionState η) Y ∧ ContDiffAt ℝ 2 (compactConnectionPhase η) Y ∧
        0 < compactConnectionState η Y 1 ∧ 0 < compactConnectionState η Y 3 ∧
        C * (Y 1 + Y 2) ^ (2 / 9 : ℝ) < 1 / 2 ∧
        ∀ v : CoreAngleState, v 0 = 1 → |v 1| ≤ Real.sqrt (Y 1) → |v 2| ≤ Real.sqrt (Y 2) →
        let r := fderiv ℝ (compactConnectionPhase η) Y v
        1 / 2 ≤ r ∧ |r - 1| ≤ C * (Real.sqrt (Y 1) + Y 2 * Real.sqrt (Y 2)) ∧
        |fderiv ℝ (compactConnectionState η) Y v 1| ≤
          C * (Y 1 + Y 2) ^ (2 / 9 : ℝ) * Real.sqrt (compactConnectionState η Y 1) * r ∧
        |fderiv ℝ (compactConnectionState η) Y v 3| ≤
          C * (Y 1 + Y 2) ^ (2 / 9 : ℝ) * Real.sqrt (compactConnectionState η Y 3) * r := by
  obtain ⟨δp, hδp, hδpsmall, HP⟩ := exists_compact_connection_phase_cone_bounds
  obtain ⟨δw, hδw, _, HW⟩ := exists_compact_connection_weighted_wall_bounds
  refine ⟨min δp δw, lt_min hδp hδw, (min_le_left _ _).trans hδpsmall, ?_⟩
  intro η hη
  obtain ⟨εp, hεp, hεphalf, P, hP, HP'⟩ := HP η ⟨hη.1, hη.2.trans (min_le_left _ _)⟩
  obtain ⟨εw, hεw, W, hW, HW'⟩ := HW η ⟨hη.1, hη.2.trans (min_le_right _ _)⟩
  let C := 2 * W + P
  have hC : 0 < C := by dsimp only [C]; positivity
  have hPC : P ≤ C := by dsimp only [C]; linarith only [hW]
  have hWC : 2 * W ≤ C := by dsimp only [C]; linarith only [hP]
  obtain ⟨b, hb, hbmax, Hbudget⟩ := exists_common_rpow_budget (ι := Fin 1) Finset.univ
    (C := fun _ => C) (p := fun _ => 2 / 9) (ε := fun _ => 1 / 2)
    (fun _ _ => hC.le) (by intros; norm_num) (by intros; norm_num) (lt_min hεp hεw)
  let ε := b / 2
  have hεb : ε ≤ b := by dsimp only [ε]; linarith only [hb]
  have hεp' : ε ≤ εp := hεb.trans (hbmax.le.trans (min_le_left _ _))
  have hεw' : ε ≤ εw := hεb.trans (hbmax.le.trans (min_le_right _ _))
  refine ⟨ε, half_pos hb, C, hC, ?_⟩
  intro Y hk hu hw
  obtain ⟨hphase, Hphase⟩ := HP' Y hk ⟨hu.1, hu.2.trans hεp'⟩ ⟨hw.1, hw.2.trans hεp'⟩
  obtain ⟨htail, hreturn, hstate, hU, hV, Hwall⟩ := HW' Y hk ⟨hu.1, hu.2.trans hεw'⟩ ⟨hw.1, hw.2.trans hεw'⟩
  have hsum : 0 < Y 1 + Y 2 := add_pos hu.1 hw.1
  have hsumb : Y 1 + Y 2 ≤ b := by dsimp only [ε] at hu hw; linarith only [hu.2, hw.2]
  have hsum1 : Y 1 + Y 2 ≤ 1 := by linarith only [hu.2.trans hεp', hw.2.trans hεp', hεphalf]
  have hpow : (Y 1 + Y 2) ^ (19 / 24 : ℝ) ≤ (Y 1 + Y 2) ^ (2 / 9 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hsum hsum1 (by norm_num)
  refine ⟨htail, hreturn, hstate, hphase, hU, hV, Hbudget _ ⟨hsum, hsumb⟩ 0 (Finset.mem_univ _), ?_⟩
  intro v hv0 hv1 hv2
  obtain ⟨hr, herror⟩ := Hphase v hv0 hv1 hv2
  obtain ⟨hwu, hwv⟩ := Hwall v hv0 hv1 hv2
  have hfactor : W ≤ C * fderiv ℝ (compactConnectionPhase η) Y v := by
    have H := mul_le_mul_of_nonneg_left hr hC.le
    linarith only [H, hWC]
  refine ⟨hr, herror.trans (mul_le_mul_of_nonneg_right hPC (by positivity [hw.1])), ?_, ?_⟩
  · calc
      _ ≤ W * (Y 1 + Y 2) ^ (2 / 9 : ℝ) * Real.sqrt (compactConnectionState η Y 1) :=
        hwu.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hW.le) (Real.sqrt_nonneg _))
      _ ≤ (C * fderiv ℝ (compactConnectionPhase η) Y v) * (Y 1 + Y 2) ^ (2 / 9 : ℝ) *
          Real.sqrt (compactConnectionState η Y 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg hsum.le _)) (Real.sqrt_nonneg _)
      _ = _ := by ring
  · calc
      _ ≤ W * (Y 1 + Y 2) ^ (2 / 9 : ℝ) * Real.sqrt (compactConnectionState η Y 3) := hwv
      _ ≤ (C * fderiv ℝ (compactConnectionPhase η) Y v) * (Y 1 + Y 2) ^ (2 / 9 : ℝ) *
          Real.sqrt (compactConnectionState η Y 3) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg hsum.le _)) (Real.sqrt_nonneg _)
      _ = _ := by ring

end BianchiIX
