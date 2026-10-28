import BianchiIX.Dynamics.EntrancePhaseSourceBudget
import BianchiIX.Dynamics.EntranceActualWallResponse

noncomputable section

namespace BianchiIX

open Set MeasureTheory

/-- Uniform fixed-clock phase and wall response of the actual Einstein flow, including phase increments. -/
theorem exists_actual_entrance_phase_response :
    ∃ T > (0 : ℝ), ∃ K > (0 : ℝ), ∃ F > (0 : ℝ), ∃ ε > (0 : ℝ),
      ∀ (y : ProjectiveState) (t₀ s t k θ : ℝ),
      0 < projectiveStateDenom y → 7 / 4 ≤ k → s ≤ t →
      (∀ r ∈ Icc s t, r ∈ normalizedMaxDomain (fromProjectiveState y) t₀) →
      (∀ r ∈ Icc s t, 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ r 0) →
      let Y := projectiveOriginalFlow y t₀
      (∀ r ∈ Icc s t, entranceRegion k (Y r)) → (∀ r ∈ Icc s t, 0 < Y r 2) →
      (∀ r ∈ Icc s t, Y r 1 ≠ 0 ∧ Y r 3 ≠ 0) →
      Y s 1 ≤ ε → Y s 3 ≤ ε →
      (θ = 1 ∨ (θ = 1 / k ^ 2 ∧ k * (Y s 1 + Y s 3) ^ 2 ≤ 1)) →
      ∀ (w : ProjectiveState), w 2 = 0 →
      let v := fun r => entranceProjectedFlowVariation y t₀ r w
      let X := fun r => v r 1 / Y r 1
      let W := fun r => v r 3 / Y r 3
      let Z := fun r => fderiv ℝ entranceStableRadius (Y r) (v r)
      let A := Y s 1 * |X s| + Y s 3 * |W s|
      let I := Y s 1 * Y s 2 * |X s| +
        (Y s 1 * Y s 2 * Y s 3 + θ * (Y s 2 * Y s 3) ^ 2) * |W s|
      let B := K * I / k
      let Λ := F * (Y s 1 * Y s 2 + θ * (Y s 2 * Y s 3) ^ 2) / k ^ 2
      0 ≤ Λ ∧ Λ ≤ 1 / 2 ∧ ∀ r ∈ Icc s t,
        |Z r - Z s| ≤ 2 * B + 2 * Λ * |Z s| ∧
        |Z r| ≤ (1 + 2 * Λ) * |Z s| + 2 * B ∧
        |X r - X s| + k ^ 2 * |W r - W s| ≤
          T * (A + 2 * (Real.log (Y r 2) - Real.log (Y s 2)) * (|Z s| + B)) := by
  obtain ⟨T, hT, HT⟩ := exists_actual_entrance_wall_response
  obtain ⟨K₀, hK₀, HK⟩ := exists_scaled_entrance_phase_source_budget
  obtain ⟨F₀, hF₀, HF⟩ := exists_scaled_entrance_phase_feedback_budget
  let K := K₀ * (1 + 3 * T)
  let F := (T + 1) * F₀
  let ε := min (1 / 10000) (1 / (4 * F))
  have hK : 0 < K := by dsimp [K]; positivity
  have hF : 0 < F := by dsimp [F]; positivity
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  refine ⟨T, hT, K, hK, F, hF, ε, hε, ?_⟩
  intro y t₀ s t k θ hD hk hst hdom hchart Y hreg hv hwall huε hwε hθ w hw0 v X W Z A I B Λ
  let a := fun r => 6 / projectiveStateDenom (Y r)
  let q := fun r => entranceOriginalClockRate (Y r)
  let l := fun r => Real.log (Y r 2) - Real.log (Y s 2)
  let f := fun r => entranceWallTangent k (Y r) (v r)
  let c := fun r => entranceWeightedPhaseCoefficients k (Y r)
  have hs : s ∈ Icc s t := ⟨le_rfl, hst⟩
  have hk0 : 0 < k := by linarith
  have hk1 : 1 ≤ k := by linarith
  have hθ01 : 0 ≤ θ ∧ θ ≤ 1 := by
    rcases hθ with rfl | ⟨rfl, _⟩
    · norm_num
    · exact ⟨by positivity, (div_le_one (sq_pos_of_pos hk0)).mpr (one_le_pow₀ hk1)⟩
  have hsmall : 0 ≤ Λ ∧ Λ ≤ 1 / 2 := entrance_phase_feedback_small hF
    ((min_le_left _ _).trans (by norm_num : (1 : ℝ) / 10000 ≤ 1)) (min_le_right _ _) hk1 hθ01
    ⟨(hreg s hs).2.2.1.1, huε⟩ (hreg s hs).2.2.2.1 ⟨(hreg s hs).2.2.2.2.1, hwε⟩
  have hA : 0 ≤ A := by dsimp [A]; positivity [(hreg s hs).2.2.1.1, (hreg s hs).2.2.2.2.1]
  have hB : 0 ≤ B := by
    dsimp [B, I]
    positivity [(hreg s hs).2.2.1.1, (hreg s hs).2.2.2.1.1, (hreg s hs).2.2.2.2.1, hθ01.1]
  have hden (r : ℝ) (hr : r ∈ Icc s t) : 0 < projectiveStateDenom (Y r) := by
    have hc : stateConstraint (normalizedMaxCurve (fromProjectiveState y) t₀ r) = 1 :=
      (normalizedMaxCurve_constraint (hdom r hr)).trans (fromProjectiveState_constraint hD.ne')
    exact toProjectiveState_denom_pos (hchart r hr) hc
  have hY (r : ℝ) (hr : r ∈ Icc s t) : HasDerivAt Y (a r • projectiveField (Y r)) r :=
    hasDerivAt_projectiveOriginalFlow_time hD (hdom r hr) (hchart r hr)
  have hac : ContinuousOn a (Icc s t) := by
    intro r hr
    exact (continuousAt_const.div ((contDiff_projectiveStateDenom 1).continuous.continuousAt.comp
      (hY r hr).continuousAt) (hden r hr).ne').continuousWithinAt
  have ha (r : ℝ) (hr : r ∈ Icc s t) : 0 ≤ a r := (div_pos (by norm_num) (hden r hr)).le
  have hqc : ContinuousOn q (Icc s t) := hac.mul
    (continuous_entranceClockRate.comp_continuousOn (HasDerivAt.continuousOn hY))
  have hq (r : ℝ) (hr : r ∈ Icc s t) : 0 ≤ q r :=
    mul_nonneg (ha r hr) (entranceRegion_clock_pos hk (hreg r hr)).le
  have hl (r : ℝ) (hr : r ∈ Icc s t) : HasDerivAt l (q r) r :=
    (hasDerivAt_entranceLog_scaled (hY r hr) (hv r hr).ne').sub_const _
  have hmono : MonotoneOn l (Icc s t) := monotoneOn_of_hasDerivWithinAt_nonneg
    (convex_Icc s t) (HasDerivAt.continuousOn hl)
    (fun r hr => (hl r (interior_subset hr)).hasDerivWithinAt) (fun r hr => hq r (interior_subset hr))
  have hl0 (r : ℝ) (hr : r ∈ Icc s t) : 0 ≤ l r := by
    have H := hmono hs hr hr.1
    simpa only [l, sub_self] using H
  have hcc : ContinuousOn c (Icc s t) := by
    intro r hr
    exact ((continuousAt_entranceWeightedPhaseCoefficients hk (hreg r hr) (hv r hr)).comp
      (hY r hr).continuousAt).continuousWithinAt
  have hf0 (r : ℝ) : f r 0 = X r := rfl
  have hf1 (r : ℝ) : f r 1 = k ^ 2 * W r := rfl
  have hdiff (r : ℝ) : |f r 0 - f s 0| + |f r 1 - f s 1| =
      |X r - X s| + k ^ 2 * |W r - W s| := by
    rw [hf0, hf0, hf1, hf1, ← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg k)]
  have htrans (r : ℝ) (hr : r ∈ Icc s t) :
      |f r 0 - f s 0| + |f r 1 - f s 1| ≤ T * (A + ∫ z in s..r, |Z z| * q z) := by
    have H := HT y t₀ s t k hD hk hst hdom hchart hreg hv hwall w hw0 s r le_rfl hr.1 hr.2
    change _ ≤ T * (Y s 1 * |f s 0| + Y s 3 / k ^ 2 * |f s 1| + _) at H
    have hinit : Y s 1 * |f s 0| + Y s 3 / k ^ 2 * |f s 1| = A := by
      rw [hf0, hf1, abs_mul, abs_of_nonneg (sq_nonneg k)]
      dsimp [A]
      field_simp
    rwa [hinit] at H
  have hsource : (∫ r in s..t, coupledVariationSource T A (f s 0) (f s 1) (c r) * q r) ≤ B := by
    exact HK Y a s t k θ T (X s) (W s) hk hst hT.le hY hac ha hreg hv hθ
  have hbudget : (∫ r in s..t, coupledVariationFeedback T (l r) (c r) * q r) ≤ Λ := by
    simp only [c, entranceWeightedPhaseCoefficients_feedback, mul_assoc]
    rw [intervalIntegral.integral_const_mul]
    exact (mul_le_mul_of_nonneg_left (HF Y a s t k θ hk hst hY hac ha hreg hv hθ)
      (by positivity : 0 ≤ T + 1)).trans_eq (by dsimp [Λ, F]; ring)
  have hZ (r : ℝ) (hr : r ∈ Icc s t) :
      HasDerivAt Z (q r * (c r 0 * Z r + c r 1 * f r 0 + c r 2 * f r 1)) r := by
    have H := hasDerivAt_entranceProjectedRadialTangent hD (hdom r hr) (hchart r hr) hk
      (hreg r hr) (hv r hr) (hwall r hr).1 (hwall r hr).2 w hw0
    convert! H using 1
    dsimp [c, f, entranceWeightedPhaseCoefficients, entranceWallTangent]
    field_simp
    rfl
  have H := coupled_clock_variation_bounds hst hT.le hA hZ hl (by dsimp [l]; ring)
    hqc hq hcc (fun _ _ => rfl) htrans hsource hbudget (by linarith [hsmall.2])
  have hM : (|Z s| + B) / (1 - Λ) ≤ 2 * (|Z s| + B) := by
    apply (div_le_iff₀ (by linarith [hsmall.2] : 0 < 1 - Λ)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hsmall.2 (add_nonneg (abs_nonneg (Z s)) hB)]
  refine ⟨hsmall.1, hsmall.2, ?_⟩
  intro r hr
  have hinc : |Z r - Z s| ≤ 2 * B + 2 * Λ * |Z s| := by
    have HI := (H r hr).2.1.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hM hsmall.1))
    nlinarith only [HI, mul_le_mul_of_nonneg_right hsmall.2 hB]
  refine ⟨hinc, ?_, ?_⟩
  · have HT : |Z r| ≤ |Z r - Z s| + |Z s| := by simpa using abs_add_le (Z r - Z s) (Z s)
    nlinarith only [HT, hinc]
  · rw [← hdiff]
    exact (H r hr).2.2.trans ((mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hM (hl0 r hr))) hT.le).trans_eq (by dsimp [l]; ring))

end BianchiIX
