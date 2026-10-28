import BianchiIX.Dynamics.EntrancePhaseActiveBudget
import BianchiIX.Dynamics.EntrancePhaseSourceBudget

noncomputable section

namespace BianchiIX

open Set MeasureTheory

/-- The direct phase forcing and the k inverse transverse response share the same phase budget. -/
theorem exists_scaled_entrance_forced_source_budget :
    ∃ K > (0 : ℝ), ∀ (Y : ℝ → ProjectiveState) (a : ℝ → ℝ) (s t k C : ℝ),
      7 / 4 ≤ k → s ≤ t → 0 ≤ C →
      (∀ r ∈ Icc s t, HasDerivAt Y (a r • projectiveField (Y r)) r) →
      ContinuousOn a (Icc s t) → (∀ r ∈ Icc s t, 0 ≤ a r) →
      (∀ r ∈ Icc s t, entranceRegion k (Y r)) → (∀ r ∈ Icc s t, 0 < Y r 2) →
      k * (Y s 1 + Y s 3) ^ 2 ≤ 1 →
      let c := fun r => entranceWeightedPhaseCoefficients k (Y r)
      (∫ r in s..t, (|entrancePhaseActiveSource (Y r)| + C * (1 / k) * (|c r 1| + |c r 2|)) *
        (a r * entranceClockRate (Y r))) ≤
          K * (1 + C) * (Y s 1 * Y s 2 + (Y s 2 * Y s 3) ^ 2 / k ^ 2) / k := by
  obtain ⟨G, hG, HG⟩ := exists_scaled_entrance_phase_active_budget
  obtain ⟨W, hW, HW⟩ := exists_scaled_entrance_phase_wall_budgets
  refine ⟨G + 2 * W, by positivity, ?_⟩
  intro Y a s t k C hk hst hC hY hac ha hy hv hsmall c
  let q := fun r => a r * entranceClockRate (Y r)
  let H := Y s 1 * Y s 2 + (Y s 2 * Y s 3) ^ 2 / k ^ 2
  have hs : s ∈ Icc s t := ⟨le_rfl, hst⟩
  have hk0 : 0 < k := by linarith
  have hk1 : 1 ≤ k := by linarith
  have hu := (hy s hs).2.2.1.1
  have hw := (hy s hs).2.2.2.2.1
  have hw1 : Y s 3 ≤ 1 := by linarith [(hy s hs).2.2.2.2.2]
  have hH : 0 ≤ H := by dsimp [H]; positivity [hv s hs]
  have hqc : ContinuousOn q (Icc s t) := hac.mul
    (continuous_entranceClockRate.comp_continuousOn (HasDerivAt.continuousOn hY))
  have hcc : ContinuousOn c (Icc s t) := by
    intro r hr
    exact ((continuousAt_entranceWeightedPhaseCoefficients hk (hy r hr) (hv r hr)).comp
      (hY r hr).continuousAt).continuousWithinAt
  have hc (i : Fin 3) : ContinuousOn (fun r => |c r i| * q r) (Icc s t) :=
    ((continuous_apply i).comp_continuousOn hcc).abs.mul hqc
  have hgc : ContinuousOn (fun r => |entrancePhaseActiveSource (Y r)| * q r) (Icc s t) := by
    apply ContinuousOn.mul ?_ hqc
    intro r hr
    exact (((continuousAt_entrancePhaseActiveSource hk (hy r hr) (hv r hr)).comp
      (hY r hr).continuousAt).abs).continuousWithinAt
  obtain ⟨HX, HY⟩ := HW Y a s t k (1 / k ^ 2) hk hst hY hac ha hy hv (Or.inr ⟨rfl, hsmall⟩)
  have HX' : (∫ r in s..t, |c r 1| * q r) ≤ W * H / k :=
    HX.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (by positivity)) hW.le) hk0.le)
  have HY' : (∫ r in s..t, |c r 2| * q r) ≤ W * H / k := by
    have he (r : ℝ) : |c r 2| * q r = (1 / k ^ 2) * (|entranceRadialVariationCoefficients (Y r) 2| * q r) := by
      dsimp [c, entranceWeightedPhaseCoefficients]
      rw [abs_div, abs_of_nonneg (sq_nonneg k)]
      ring
    simp_rw [he]
    rw [intervalIntegral.integral_const_mul]
    calc
      _ ≤ (1 / k ^ 2) * (W * (Y s 1 * Y s 2 * Y s 3 + (1 / k ^ 2) * (Y s 2 * Y s 3) ^ 2) / k) :=
        mul_le_mul_of_nonneg_left HY (by positivity)
      _ = (W * (Y s 1 * Y s 2 * Y s 3 + (1 / k ^ 2) * (Y s 2 * Y s 3) ^ 2) / k) / k ^ 2 := by ring
      _ ≤ W * (Y s 1 * Y s 2 * Y s 3 + (1 / k ^ 2) * (Y s 2 * Y s 3) ^ 2) / k :=
        div_le_self (by positivity [hv s hs]) (one_le_pow₀ hk1)
      _ ≤ W * H / k := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (by dsimp [H]; rw [one_div_mul_eq_div]; exact add_le_add (mul_le_of_le_one_right (mul_nonneg hu (hv s hs).le) hw1) le_rfl) hW.le) hk0.le
  have hsum : (∫ r in s..t, (|c r 1| + |c r 2|) * q r) ≤ 2 * W * H / k := by
    simp_rw [add_mul]
    rw [intervalIntegral.integral_add ((hc 1).intervalIntegrable_of_Icc hst) ((hc 2).intervalIntegrable_of_Icc hst)]
    exact (add_le_add HX' HY').trans_eq (by ring)
  have hsumc : ContinuousOn (fun r => (|c r 1| + |c r 2|) * q r) (Icc s t) := by
    exact (((continuous_apply 1).comp_continuousOn hcc).abs.add
      ((continuous_apply 2).comp_continuousOn hcc).abs).mul hqc
  have hGI := HG Y a s t k hk hst hY hac ha hy hv hsmall
  have heq : (fun r => (|entrancePhaseActiveSource (Y r)| + C * (1 / k) * (|c r 1| + |c r 2|)) * q r) =
      (fun r => |entrancePhaseActiveSource (Y r)| * q r + (C / k) * ((|c r 1| + |c r 2|) * q r)) := by
    funext r
    ring
  change (∫ r in s..t, (|entrancePhaseActiveSource (Y r)| + C * (1 / k) * (|c r 1| + |c r 2|)) * q r) ≤ _
  rw [heq, intervalIntegral.integral_add (hgc.intervalIntegrable_of_Icc hst)
    ((hsumc.const_mul (C / k)).intervalIntegrable_of_Icc hst), intervalIntegral.integral_const_mul]
  have hCk : C / k ≤ C := div_le_self hC hk1
  calc
    _ ≤ G * H / k + (C / k) * (2 * W * H / k) := add_le_add hGI (mul_le_mul_of_nonneg_left hsum (by positivity))
    _ ≤ G * H / k + C * (2 * W * H / k) := add_le_add le_rfl (mul_le_mul_of_nonneg_right hCk (by positivity))
    _ ≤ (G + 2 * W) * (1 + C) * H / k := by
      have h0 : 0 ≤ G * C * (H / k) := by positivity
      have h1 : 0 ≤ W * (H / k) := by positivity
      simp only [div_eq_mul_inv] at h0 h1 ⊢
      nlinarith only [h0, h1]

end BianchiIX
