import BianchiIX.Dynamics.CompactConnectionCoordinates
import BianchiIX.Dynamics.CompactTailMultiplierBounds
import BianchiIX.Analysis.CompactLogComposition

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

theorem coreTailMultiplier_fderiv_log {η : ℝ} {Y : CoreAngleState} (i : Fin 2)
    (hB : DifferentiableAt ℝ (fun Z => coreTailMultiplier η Z i) Y) (v : CoreAngleState) :
    fderiv ℝ (fun Z => coreTailMultiplier η Z i) Y v = coreTailMultiplier η Y i *
      fderiv ℝ (fun Z => Real.log (coreTailMultiplier η Z i)) Y v := by
  rw [(hB.hasFDerivAt.log (coreTailMultiplier_pos η Y i).ne').fderiv]
  simp only [smul_apply, smul_eq_mul]
  field_simp [(coreTailMultiplier_pos η Y i).ne']

/-- Finite-tail coordinates preserve the factors needed by the long-entrance logarithmic columns. -/
theorem exists_compact_connection_tangent_bounds {η : ℝ} (hη : 0 < η ∧ η ≤ 1 / 10000) :
    ∃ ε > (0 : ℝ), ∃ A : ℝ, 1 ≤ A ∧ ∀ Y : CoreAngleState,
      (31 / 8 ≤ Y 0 ∧ Y 0 ≤ 6) → (0 < Y 1 ∧ Y 1 ≤ ε) → (0 < Y 2 ∧ Y 2 ≤ ε) →
      (∀ᶠ Z in 𝓝 Y, coreTailValid η Z) ∧ ContDiffAt ℝ 2 (compactConnectionCoordinates η) Y ∧
        -Real.log (compactConnectionCoordinates η Y 2) ≤ A + |Real.log (Y 2)| ∧
        ∀ v : CoreAngleState, v 0 = 1 → |v 1| ≤ Real.sqrt (Y 1) → |v 2| ≤ Real.sqrt (Y 2) →
        let d := fderiv ℝ (compactConnectionCoordinates η) Y v
        |d 0| ≤ A ∧ |d 1| ≤ A ∧
          |d 1| ≤ compactConnectionCoordinates η Y 1 * (A + 1 / Real.sqrt (Y 1)) ∧
          |d 2| ≤ compactConnectionCoordinates η Y 2 * (A + 1 / Real.sqrt (Y 2)) ∧ d 3 = 0 := by
  obtain ⟨εc, hεc, R, hR, HC⟩ := exists_compact_connection_coordinate_bounds hη
  obtain ⟨εm, hεm, M, hM, HM⟩ := exists_compact_tail_multiplier_bounds ⟨hη.1, by linarith [hη.2]⟩
  let ε := min εc (min εm 1)
  let A := 2 * R + M + 1
  have hR0 : 0 ≤ R := by linarith only [hR]
  have hRA : R ≤ A := by dsimp only [A]; linarith only [hR, hM]
  have h2RA : 2 * R ≤ A := by dsimp only [A]; linarith only [hM]
  have hMA : M ≤ A := by dsimp only [A]; linarith only [hR]
  have hεc' : ε ≤ εc := min_le_left _ _
  have hεm' : ε ≤ εm := (min_le_right _ _).trans (min_le_left _ _)
  have hε1 : ε ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ε, lt_min hεc (lt_min hεm zero_lt_one), A, by dsimp only [A]; linarith only [hR, hM], ?_⟩
  intro Y hk hu hw
  obtain ⟨hvalid, hF, hDF, hBi⟩ := HC Y hk
    (by rw [abs_of_pos hu.1]; exact hu.2.trans hεc')
    (by rw [abs_of_pos hw.1]; exact hw.2.trans hεc')
  obtain ⟨_, _, _, _, hBm⟩ := HM Y hk
    (by rw [abs_of_pos hu.1]; exact hu.2.trans hεm')
    (by rw [abs_of_pos hw.1]; exact hw.2.trans hεm')
  have hmb (i : Fin 2) : (coreTailMultiplier η Y i)⁻¹ ≤ M ∧
      ‖fderiv ℝ (fun Z => Real.log (coreTailMultiplier η Z i)) Y‖ ≤ M := by
    have H := (hBm i).2.2.2
    constructor <;> linarith only [H, (hBm i).1,
      inv_nonneg.mpr (hBm i).1.le,
      norm_nonneg (fderiv ℝ (fun Z => Real.log (coreTailMultiplier η Z i)) Y),
      norm_nonneg (fderiv ℝ (fderiv ℝ (fun Z => Real.log (coreTailMultiplier η Z i))) Y)]
  refine ⟨hvalid, contDiffAt_compactConnectionCoordinates_two hF (fun i => (hBi i).1), ?_, ?_⟩
  · change -Real.log (Y 2 * coreTailMultiplier η Y 1) ≤ _
    rw [Real.log_mul hw.1.ne' (hBi 1).2.1.ne']
    have H := Real.neg_inv_le_log (hBi 1).2.1.le
    linarith only [H, (hmb 1).1, hMA, neg_le_abs (Real.log (Y 2))]
  · intro v hv0 hv1 hv2
    have hvnorm : ‖v‖ ≤ 1 := by
      apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
      intro i
      fin_cases i
      · simp [hv0]
      · exact hv1.trans (Real.sqrt_le_one.mpr (hu.2.trans hε1))
      · exact hv2.trans (Real.sqrt_le_one.mpr (hw.2.trans hε1))
    have hnorm (L : CoreAngleState →L[ℝ] ℝ) : |L v| ≤ ‖L‖ := by
      exact (L.le_opNorm v).trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hvnorm (norm_nonneg L))
    have hl (i : Fin 2) : |fderiv ℝ (fun Z => Real.log (coreTailMultiplier η Z i)) Y v| ≤ A :=
      (hnorm _).trans ((hmb i).2.trans hMA)
    dsimp only
    rw [compactConnectionCoordinates_fderiv hF (fun i => (hBi i).1)]
    change |fderiv ℝ (compactConnectionFinitePhase η) Y v| ≤ A ∧
      |v 1 * coreTailMultiplier η Y 0 + Y 1 * fderiv ℝ (fun Z => coreTailMultiplier η Z 0) Y v| ≤ A ∧ _
    refine ⟨(hnorm _).trans (hDF.trans hRA), ?_, ?_, ?_, rfl⟩
    · have H1 : |v 1| ≤ 1 := hv1.trans (Real.sqrt_le_one.mpr (hu.2.trans hε1))
      have H2 : |fderiv ℝ (fun Z => coreTailMultiplier η Z 0) Y v| ≤ R := (hnorm _).trans (hBi 0).2.2.2
      calc
        _ ≤ |v 1 * coreTailMultiplier η Y 0| + |Y 1 * fderiv ℝ (fun Z => coreTailMultiplier η Z 0) Y v| := abs_add_le _ _
        _ = |v 1| * coreTailMultiplier η Y 0 + Y 1 * |fderiv ℝ (fun Z => coreTailMultiplier η Z 0) Y v| := by
          rw [abs_mul, abs_mul, abs_of_pos (hBi 0).2.1, abs_of_pos hu.1]
        _ ≤ 1 * R + 1 * R := add_le_add
          (mul_le_mul H1 (hBi 0).2.2.1 (hBi 0).2.1.le zero_le_one)
          (mul_le_mul (hu.2.trans hε1) H2 (abs_nonneg _) zero_le_one)
        _ ≤ A := by linarith only [h2RA]
    · change |v 1 * coreTailMultiplier η Y 0 + Y 1 * fderiv ℝ (fun Z => coreTailMultiplier η Z 0) Y v| ≤
        (Y 1 * coreTailMultiplier η Y 0) * (A + 1 / Real.sqrt (Y 1))
      rw [coreTailMultiplier_fderiv_log 0 ((hBi 0).1.differentiableAt (by norm_num))]
      convert sqrt_wall_product_direction_bound hu.1 (hBi 0).2.1 hv1 (hl 0) using 1
      congr 1
      ring
    · change |v 2 * coreTailMultiplier η Y 1 + Y 2 * fderiv ℝ (fun Z => coreTailMultiplier η Z 1) Y v| ≤
        (Y 2 * coreTailMultiplier η Y 1) * (A + 1 / Real.sqrt (Y 2))
      rw [coreTailMultiplier_fderiv_log 1 ((hBi 1).1.differentiableAt (by norm_num))]
      convert sqrt_wall_product_direction_bound hw.1 (hBi 1).2.1 hv2 (hl 1) using 1
      congr 1
      ring

end BianchiIX
