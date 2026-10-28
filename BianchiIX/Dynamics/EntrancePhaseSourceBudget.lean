import BianchiIX.Dynamics.EntrancePhaseWallBudgets
import BianchiIX.Algebra.EntranceVariationMixing
import BianchiIX.Analysis.CoupledClockVariation

noncomputable section

namespace BianchiIX

open Set MeasureTheory

def entranceWeightedPhaseCoefficients (k : ℝ) (y : ProjectiveState) : Fin 3 → ℝ :=
  ![entranceRadialVariationCoefficients y 0, entranceRadialVariationCoefficients y 1,
    entranceRadialVariationCoefficients y 2 / k ^ 2]

theorem continuousAt_entranceWeightedPhaseCoefficients {k : ℝ} {y : ProjectiveState}
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (hv : 0 < y 2) :
    ContinuousAt (entranceWeightedPhaseCoefficients k) y := by
  apply continuousAt_pi.mpr
  intro i
  have H (j : Fin 3) := (continuous_apply j).continuousAt.comp
    (continuousAt_entranceRadialVariationCoefficients hk hy hv)
  fin_cases i
  · exact H 0
  · exact H 1
  · exact (H 2).div_const _

theorem entranceWeightedPhaseCoefficients_feedback (k C l : ℝ) (y : ProjectiveState) :
    coupledVariationFeedback C l (entranceWeightedPhaseCoefficients k y) =
      (C + 1) * entrancePhaseFeedbackRate k l y := by
  simp [coupledVariationFeedback, entranceWeightedPhaseCoefficients, entrancePhaseFeedbackRate,
    abs_div, abs_of_nonneg (sq_nonneg k)]

/-- The transverse initial data force the phase by I/k, with both wall amplitudes retained. -/
theorem exists_scaled_entrance_phase_source_budget :
    ∃ K > (0 : ℝ), ∀ (Y : ℝ → ProjectiveState) (a : ℝ → ℝ) (s t k θ C X W : ℝ),
      7 / 4 ≤ k → s ≤ t → 0 ≤ C →
      (∀ r ∈ Icc s t, HasDerivAt Y (a r • projectiveField (Y r)) r) →
      ContinuousOn a (Icc s t) → (∀ r ∈ Icc s t, 0 ≤ a r) →
      (∀ r ∈ Icc s t, entranceRegion k (Y r)) → (∀ r ∈ Icc s t, 0 < Y r 2) →
      (θ = 1 ∨ (θ = 1 / k ^ 2 ∧ k * (Y s 1 + Y s 3) ^ 2 ≤ 1)) →
      (∫ r in s..t, coupledVariationSource C (Y s 1 * |X| + Y s 3 * |W|) X (k ^ 2 * W)
        (entranceWeightedPhaseCoefficients k (Y r)) * (a r * entranceClockRate (Y r))) ≤
      K * (1 + 3 * C) * (Y s 1 * Y s 2 * |X| +
        (Y s 1 * Y s 2 * Y s 3 + θ * (Y s 2 * Y s 3) ^ 2) * |W|) / k := by
  obtain ⟨K, hK, HK⟩ := exists_scaled_entrance_phase_wall_budgets
  refine ⟨K, hK, ?_⟩
  intro Y a s t k θ C X W hk hst hC hY hac ha hy hv hθ
  let u := Y s 1
  let v := Y s 2
  let w := Y s 3
  let A := u * |X| + w * |W|
  let P := u * v
  let S := u * v * w + θ * (v * w) ^ 2
  let q := fun r => a r * entranceClockRate (Y r)
  have hk0 : 0 < k := by linarith
  have hk1 : 1 ≤ k := by linarith
  have hs : s ∈ Icc s t := ⟨le_rfl, hst⟩
  have hu0 : 0 ≤ u := (hy s hs).2.2.1.1
  have hw0 : 0 ≤ w := (hy s hs).2.2.2.2.1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hθ01 : 0 ≤ θ ∧ θ ≤ 1 := by
    rcases hθ with rfl | ⟨rfl, _⟩
    · norm_num
    · exact ⟨by positivity, (div_le_one (sq_pos_of_pos hk0)).mpr (one_le_pow₀ hk1)⟩
  have hmix : A * (P + S / k ^ 2) ≤ 3 * (P * |X| + S * |W|) :=
    entrance_initial_wall_mixing hk1 hθ01
      ⟨hu0, by dsimp [u]; linarith [(hy s hs).2.2.1.2]⟩ (hy s hs).2.2.2.1
      ⟨hw0, by dsimp [w]; linarith [(hy s hs).2.2.2.2.2]⟩
  have hcoeff : ContinuousOn (fun r => entranceRadialVariationCoefficients (Y r)) (Icc s t) := by
    intro r hr
    exact ((continuousAt_entranceRadialVariationCoefficients hk (hy r hr) (hv r hr)).comp
      (hY r hr).continuousAt).continuousWithinAt
  have hqc : ContinuousOn q (Icc s t) := hac.mul
    (continuous_entranceClockRate.comp_continuousOn (HasDerivAt.continuousOn hY))
  have hc (i : Fin 3) : ContinuousOn (fun r => |entranceRadialVariationCoefficients (Y r) i| * q r) (Icc s t) :=
    ((continuous_apply i).comp_continuousOn hcoeff).abs.mul hqc
  have heq (r : ℝ) : coupledVariationSource C A X (k ^ 2 * W)
      (entranceWeightedPhaseCoefficients k (Y r)) * q r =
      (|X| + C * A) * (|entranceRadialVariationCoefficients (Y r) 1| * q r) +
      (|W| + C * A / k ^ 2) * (|entranceRadialVariationCoefficients (Y r) 2| * q r) := by
    simp [coupledVariationSource, entranceWeightedPhaseCoefficients,
      abs_mul, abs_div, abs_of_nonneg (sq_nonneg k)]
    field_simp
    ring
  change (∫ r in s..t, coupledVariationSource C A X (k ^ 2 * W)
    (entranceWeightedPhaseCoefficients k (Y r)) * q r) ≤ _
  simp_rw [heq]
  rw [intervalIntegral.integral_add (((hc 1).const_mul (|X| + C * A)).intervalIntegrable_of_Icc hst)
    (((hc 2).const_mul (|W| + C * A / k ^ 2)).intervalIntegrable_of_Icc hst),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  obtain ⟨HX, HW⟩ := HK Y a s t k θ hk hst hY hac ha hy hv hθ
  have H := add_le_add (mul_le_mul_of_nonneg_left HX (show 0 ≤ |X| + C * A by positivity))
    (mul_le_mul_of_nonneg_left HW (show 0 ≤ |W| + C * A / k ^ 2 by positivity))
  apply H.trans
  calc
    _ = K / k * (P * |X| + S * |W| + C * (A * (P + S / k ^ 2))) := by dsimp [P, S, u, v, w]; ring
    _ ≤ K / k * (P * |X| + S * |W| + C * (3 * (P * |X| + S * |W|))) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left hmix hC)) (by positivity)
    _ = _ := by dsimp [P, S, u, v, w]; ring

end BianchiIX
