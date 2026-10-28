import BianchiIX.Analysis.ForcedClockFeedback
import BianchiIX.Dynamics.EntranceForcedWallResponse
import BianchiIX.Dynamics.EntranceForcedSourceBudget
import BianchiIX.Dynamics.EntranceActiveReturnSystem

noncomputable section

namespace BianchiIX

open Set MeasureTheory

/-- The full fixed-clock active response (C.44) for the exact first-arrival trajectory. -/
theorem exists_entrance_return_active_response :
    ∃ C > (0 : ℝ), ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧ ∀ (y : ProjectiveState),
      7 / 4 ≤ coreRadius (y 0) (y 2) → 1 ≤ y 0 →
      (0 < y 1 ∧ y 1 ≤ ε) → (0 < y 2 ∧ y 2 < 1) → (0 < y 3 ∧ y 3 ≤ ε) →
      coreRadius (y 0) (y 2) ^ 2 * (y 1 + y 3) ≤ 1 →
      let k := coreRadius (y 0) (y 2)
      let Y := projectiveOriginalFlow y 0
      let v := fun t => entranceProjectedFlowVariation y 0 t (entranceActiveInitialVector y)
      let Z := fun t => fderiv ℝ entranceStableRadius (Y t) (v t)
      let f := fun t => entranceWallTangent k (Y t) (v t)
      let H := y 1 * y 2 + (y 2 * y 3) ^ 2 / k ^ 2
      ∀ r ∈ Icc 0 (entranceReturnTime y), |Z r| ≤ C * H / k ∧
        |f r 0| + |f r 1| ≤ C * (1 + (Real.log (Y r 2) - Real.log (y 2)) * H) / k := by
  obtain ⟨T, hT, HT⟩ := exists_scaled_entrance_forced_wall_response
  obtain ⟨K₀, hK₀, HK⟩ := exists_scaled_entrance_forced_source_budget
  obtain ⟨F₀, hF₀, HF⟩ := exists_scaled_entrance_phase_feedback_budget
  let K := K₀ * (1 + T)
  let F := (T + 1) * F₀
  let C := 2 * K + T * (1 + 2 * K)
  let ε := min (1 / 10000) (1 / (4 * F))
  have hK : 0 < K := by dsimp [K]; positivity
  have hF : 0 < F := by dsimp [F]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  have hεcap : ε ≤ 1 / 10000 := min_le_left _ _
  refine ⟨C, hC, ε, hε, hεcap, ?_⟩
  intro y hk hm hu hv hw hsmall k Y v Z f H
  let t := entranceReturnTime y
  let a := fun r => 6 / projectiveStateDenom (Y r)
  let q := fun r => entranceOriginalClockRate (Y r)
  let l := fun r => Real.log (Y r 2) - Real.log (y 2)
  let c := fun r => entranceWeightedPhaseCoefficients k (Y r)
  let g := fun r => entrancePhaseActiveSource (Y r)
  let B := K * H / k
  let Λ := F * H / k ^ 2
  have hu' : 0 < y 1 ∧ y 1 ≤ 1 / 10000 := ⟨hu.1, hu.2.trans hεcap⟩
  have hw' : 0 < y 3 ∧ y 3 ≤ 1 / 10000 := ⟨hw.1, hw.2.trans hεcap⟩
  have hD := entrance_initial_denom_pos hk hm ⟨hu'.1.le, hu'.2⟩ hv ⟨hw'.1.le, hw'.2⟩
  have HR := (entranceReturn_regular hk hm ⟨hu'.1.le, hu'.2⟩ hv ⟨hw'.1.le, hw'.2⟩).1
  have ht : 0 ≤ t := HR.1.1.1.le
  have hinit : Y 0 = y := projectiveOriginalFlow_initial hD 0
  have hreg := entranceReturn_region hk hm ⟨hu'.1.le, hu'.2⟩ hv ⟨hw'.1.le, hw'.2⟩
  have hpos := entranceReturn_walls_pos hk hm hu' hv hw'
  have hV (r : ℝ) (hr : r ∈ Icc 0 t) : 0 < Y r 2 := (hpos r hr).2.1
  have hk0 : 0 < k := by linarith
  have hk1 : 1 ≤ k := by linarith
  have hb0 : 0 ≤ y 1 + y 3 := add_nonneg hu.1.le hw.1.le
  have hb1 : y 1 + y 3 ≤ 1 := by linarith [hu'.2, hw'.2]
  have hrefined : k * (y 1 + y 3) ^ 2 ≤ 1 := by
    have H1 : (y 1 + y 3) ^ 2 ≤ y 1 + y 3 := by nlinarith only [hb0, hb1]
    have H2 : k ≤ k ^ 2 := by nlinarith only [hk1]
    exact (mul_le_mul_of_nonneg_left H1 hk0.le).trans
      ((mul_le_mul_of_nonneg_right H2 hb0).trans hsmall)
  have hθ : 0 ≤ 1 / k ^ 2 ∧ 1 / k ^ 2 ≤ 1 :=
    ⟨by positivity, (div_le_one (sq_pos_of_pos hk0)).mpr (one_le_pow₀ hk1)⟩
  have hΛ : 0 ≤ Λ ∧ Λ ≤ 1 / 2 := by
    have Hsmall := entrance_phase_feedback_small hF
      (hεcap.trans (by norm_num : (1 : ℝ) / 10000 ≤ 1)) (min_le_right _ _) hk1 hθ
      ⟨hu.1.le, hu.2⟩ ⟨hv.1.le, hv.2.le⟩ ⟨hw.1.le, hw.2⟩
    simpa only [Λ, H, one_div_mul_eq_div] using Hsmall
  have hH : 0 ≤ H := by dsimp [H]; positivity [hu.1, hv.1]
  have hden (r : ℝ) (hr : r ∈ Icc 0 t) : 0 < projectiveStateDenom (Y r) := by
    have hc := (normalizedMaxCurve_constraint (HR.2.1 r hr).1).trans (fromProjectiveState_constraint hD.ne')
    exact toProjectiveState_denom_pos (HR.2.1 r hr).2 hc
  have hY (r : ℝ) (hr : r ∈ Icc 0 t) : HasDerivAt Y (a r • projectiveField (Y r)) r :=
    hasDerivAt_projectiveOriginalFlow_time hD (HR.2.1 r hr).1 (HR.2.1 r hr).2
  have hac : ContinuousOn a (Icc 0 t) := by
    intro r hr
    exact (continuousAt_const.div ((contDiff_projectiveStateDenom 1).continuous.continuousAt.comp
      (hY r hr).continuousAt) (hden r hr).ne').continuousWithinAt
  have ha (r : ℝ) (hr : r ∈ Icc 0 t) : 0 ≤ a r := (div_pos (by norm_num) (hden r hr)).le
  have hqc : ContinuousOn q (Icc 0 t) := hac.mul
    (continuous_entranceClockRate.comp_continuousOn (HasDerivAt.continuousOn hY))
  have hq (r : ℝ) (hr : r ∈ Icc 0 t) : 0 ≤ q r := mul_nonneg (ha r hr) (entranceRegion_clock_pos hk (hreg r hr)).le
  have hl (r : ℝ) (hr : r ∈ Icc 0 t) : HasDerivAt l (q r) r :=
    (hasDerivAt_entranceLog_scaled (hY r hr) (hV r hr).ne').sub_const _
  have hls : l 0 = 0 := by simp only [l, hinit, sub_self]
  have hmono : MonotoneOn l (Icc 0 t) := monotoneOn_of_hasDerivWithinAt_nonneg
    (convex_Icc 0 t) (HasDerivAt.continuousOn hl)
    (fun r hr => (hl r (interior_subset hr)).hasDerivWithinAt) (fun r hr => hq r (interior_subset hr))
  have hl0 (r : ℝ) (hr : r ∈ Icc 0 t) : 0 ≤ l r := by
    simpa only [hls] using hmono ⟨le_rfl, ht⟩ hr hr.1
  have hcc : ContinuousOn c (Icc 0 t) := by
    intro r hr
    exact ((continuousAt_entranceWeightedPhaseCoefficients hk (hreg r hr) (hV r hr)).comp
      (hY r hr).continuousAt).continuousWithinAt
  have hgc : ContinuousOn g (Icc 0 t) := by
    intro r hr
    exact ((continuousAt_entrancePhaseActiveSource hk (hreg r hr) (hV r hr)).comp
      (hY r hr).continuousAt).continuousWithinAt
  obtain ⟨hZs, hfs, hvar⟩ := entrance_return_active_variation_system hk hm hu' hv hw'
  have hZ (r : ℝ) (hr : r ∈ Icc 0 t) :
      HasDerivAt Z (q r * (c r 0 * Z r + c r 1 * f r 0 + c r 2 * f r 1 + g r)) r := by
    have HZ := (hvar r hr).1
    convert! HZ using 1
    dsimp [c, f, entranceWeightedPhaseCoefficients, entranceWallTangent]
    field_simp
    rfl
  have htrans := HT Y a 0 t k hk ht hY hac ha hreg hV (by simpa only [hinit] using hsmall)
    f Z (HasDerivAt.continuousOn hZ) hfs (fun r hr => (hvar r hr).2)
  have hsource : (∫ r in (0 : ℝ)..t, (|g r| + T * (1 / k) * (|c r 1| + |c r 2|)) * q r) ≤ B := by
    have HS := HK Y a 0 t k T hk ht hT.le hY hac ha hreg hV (by simpa only [hinit] using hrefined)
    simpa only [hinit, B, K, H, c, g, q, a, entranceOriginalClockRate] using HS
  have hbudget : (∫ r in (0 : ℝ)..t, coupledVariationFeedback T (l r) (c r) * q r) ≤ Λ := by
    simp only [c, entranceWeightedPhaseCoefficients_feedback, mul_assoc]
    rw [intervalIntegral.integral_const_mul]
    have HS := HF Y a 0 t k (1 / k ^ 2) hk ht hY hac ha hreg hV
      (Or.inr ⟨rfl, by simpa only [hinit] using hrefined⟩)
    simp only [hinit] at HS
    convert! mul_le_mul_of_nonneg_left HS (show 0 ≤ T + 1 by positivity) using 1
    dsimp [l, q, Λ, F, H]
    ring
  have HA := forced_clock_feedback_bounds ht hT.le (show 0 ≤ 1 / k by positivity)
    hZ hZs hl hls hqc hq hcc hgc htrans hsource hbudget hΛ.2
  have hCK : 2 * K ≤ C := le_add_of_nonneg_right (by positivity)
  have hCT : T * (1 + 2 * K) ≤ C := le_add_of_nonneg_left (by positivity)
  intro r hr
  obtain ⟨HZ, HX⟩ := HA r hr
  constructor
  · calc
      _ ≤ 2 * B := HZ
      _ = (2 * K) * H / k := by dsimp [B]; ring
      _ ≤ C * H / k := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCK hH) hk0.le
  · have hlH : 0 ≤ l r * H := mul_nonneg (hl0 r hr) hH
    have Hscale : 1 + 2 * K * (l r * H) ≤ (1 + 2 * K) * (1 + l r * H) := by nlinarith only [hK, hlH]
    calc
      _ ≤ T * (1 / k + 2 * l r * B) := HX
      _ = T * (1 + 2 * K * (l r * H)) / k := by dsimp [B]; ring
      _ ≤ (T * (1 + 2 * K)) * (1 + l r * H) / k :=
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left Hscale hT.le) hk0.le).trans_eq (by ring)
      _ ≤ C * (1 + l r * H) / k := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCT (by positivity)) hk0.le

end BianchiIX
