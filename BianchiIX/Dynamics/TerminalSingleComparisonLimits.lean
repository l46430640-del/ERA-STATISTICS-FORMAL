import BianchiIX.Dynamics.TerminalSingleValueComparison
import BianchiIX.Dynamics.CoreTailReferenceDifferential
import BianchiIX.Dynamics.ReferenceTailDecayLimits

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

def terminalSingleComparisonEnvelope (h : ℝ) (Y : ExitTailState) : ℝ :=
  (h + Y 1 * coreTailMultiplier h Y 0 + Y 2 * coreTailMultiplier h Y 1) *
    (coreTailMultiplier h Y 0 + coreTailMultiplier h Y 1)

/-- Divide by the original wall amplitude while retaining the actual finite-tail multipliers. -/
theorem exists_terminal_single_normalized_comparison_uniform :
    ∃ C ≥ (1 : ℝ), ∀ η₀ : ℝ, (0 < η₀ ∧ η₀ ≤ 1 / 40000) →
      ∀ J : ℕ, 2 ≤ J → ∃ ε > (0 : ℝ), ∀ η α b u w : ℝ,
      η₀ ≤ η → η ≤ 1 / 40000 → (0 < α ∧ α ≤ 1) →
      0 < b → b ≤ ε * α ^ (2 * J) → |u| + |w| ≤ b → 0 < u → 0 < w →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      coreTailValid h Y ∧
        |2 / terminalConnectionPhase h Y - terminalSinglePhase h Y| / (u + w) ≤
          C / α ^ 4 * terminalSingleComparisonEnvelope h Y := by
  obtain ⟨C, hC, HC⟩ := exists_terminal_single_value_comparison_uniform
  refine ⟨C, hC, ?_⟩
  intro η₀ hη₀ J hJ
  obtain ⟨ε, hε, HE⟩ := HC η₀ hη₀ J hJ
  refine ⟨ε, hε, ?_⟩
  intro η α b u w hηlo hηhi hα hb hsmall hsum hu hw Y h
  obtain ⟨HV, H⟩ := HE η α b u w hηlo hηhi hα hb hsmall hsum hu hw
  have H0 := coreTailMultiplier_formula HV 0
  have H1 := coreTailMultiplier_formula HV 1
  change coreTailState h Y 1 = u * coreTailMultiplier h Y 0 at H0
  change coreTailState h Y 3 = w * coreTailMultiplier h Y 1 at H1
  change |2 / terminalConnectionPhase h Y - terminalSinglePhase h Y| ≤ _ at H
  rw [H0, H1] at H
  let U := coreTailMultiplier h Y 0
  let W := coreTailMultiplier h Y 1
  have hU : 0 ≤ U := (coreTailMultiplier_pos h Y 0).le
  have hW : 0 ≤ W := (coreTailMultiplier_pos h Y 1).le
  have hC0 : 0 ≤ C := by linarith only [hC]
  have hh : 0 ≤ h := mul_nonneg (hη₀.1.le.trans hηlo) (pow_nonneg hα.1.le _)
  have hS : u * U + w * W ≤ (u + w) * (U + W) := by
    nlinarith only [mul_nonneg hu.le hW, mul_nonneg hw.le hU]
  refine ⟨HV, (div_le_iff₀ (add_pos hu hw)).mpr (H.trans ?_)⟩
  calc
    C / α ^ 4 * (h * (u * U + w * W) + (u * U + w * W) ^ 2) =
        (C / α ^ 4 * (h + u * U + w * W)) * (u * U + w * W) := by ring
    _ ≤ (C / α ^ 4 * (h + u * U + w * W)) * ((u + w) * (U + W)) :=
      mul_le_mul_of_nonneg_left hS (by positivity)
    _ = C / α ^ 4 * terminalSingleComparisonEnvelope h Y * (u + w) := by
      change _ = C / α ^ 4 * ((h + u * U + w * W) * (U + W)) * (u + w)
      ring

theorem contDiffAt_terminalSingleComparisonEnvelope_two {h : ℝ} {Y : ExitTailState}
    (hR : 1 < Y 0) (HV : coreTailValid h Y) :
    ContDiffAt ℝ 2 (terminalSingleComparisonEnvelope h) Y := by
  have HR := coreTail_regular_of_valid hR HV
  have HU := (contDiffAt_coreTailMultiplier_two hR HV HR.1 0).1
  have HW := (contDiffAt_coreTailMultiplier_two hR HV HR.1 1).1
  exact ((contDiffAt_const.add ((contDiff_apply ℝ ℝ 1).contDiffAt.mul HU)).add
    ((contDiff_apply ℝ ℝ 2).contDiffAt.mul HW)).mul (HU.add HW)

theorem terminalSingleComparisonEnvelope_boundary {R h : ℝ}
    (hR : 1 < R) (hh : 0 < h ∧ h < 1) :
    terminalSingleComparisonEnvelope h ![R, 0, 0] =
      Real.exp (-(R ^ 2 / 2) * referenceTailDuration R h) + Real.exp (-2 * referenceTailDuration R h) := by
  change (h + 0 * coreTailMultiplier h ![R, 0, 0] 0 + 0 * coreTailMultiplier h ![R, 0, 0] 1) *
    (coreTailMultiplier h ![R, 0, 0] 0 + coreTailMultiplier h ![R, 0, 0] 1) = _
  simp only [zero_mul, add_zero, mul_add]
  rw [coreTail_reference_weighted_multiplier hR hh 0, coreTail_reference_weighted_multiplier hR hh 1]
  norm_num

/-- The normalized comparison has a continuous envelope at every fixed positive height. -/
theorem tendsto_terminalSingleComparisonEnvelope_at_boundary {R h : ℝ}
    (hR : 1 < R) (hh : 0 < h ∧ h < 1) :
    Tendsto (terminalSingleComparisonEnvelope h) (𝓝 (![R, 0, 0] : ExitTailState))
      (𝓝 (Real.exp (-(R ^ 2 / 2) * referenceTailDuration R h) + Real.exp (-2 * referenceTailDuration R h))) := by
  have HV := (coreTail_reference_regular hR hh).2.2.2.2.self_of_nhds
  have H := (contDiffAt_terminalSingleComparisonEnvelope_two hR HV).continuousAt.tendsto
  rwa [terminalSingleComparisonEnvelope_boundary hR hh] at H

/-- Every positive wall path approaching zero obeys the same fixed-height boundary control. -/
theorem exists_terminal_single_comparison_boundary_control :
    ∃ C ≥ (1 : ℝ), ∀ α η : ℝ, (0 < α ∧ α ≤ 1) → (0 < η ∧ η ≤ 1 / 40000) →
      ∀ {ι : Type*} {l : Filter ι} {u w : ι → ℝ},
      Tendsto u l (𝓝 0) → Tendsto w l (𝓝 0) → (∀ᶠ x in l, 0 < u x ∧ 0 < w x) →
      ∀ δ : ℝ, 0 < δ →
      let R := 2 + 2 * α
      let h := η * α ^ 2
      ∀ᶠ x in l, coreTailValid h ![R, u x, w x] ∧
        |2 / terminalConnectionPhase h ![R, u x, w x] - terminalSinglePhase h ![R, u x, w x]| /
          (u x + w x) ≤ C / α ^ 4 *
            (Real.exp (-(R ^ 2 / 2) * referenceTailDuration R h) +
              Real.exp (-2 * referenceTailDuration R h) + δ) := by
  obtain ⟨C, hC, HC⟩ := exists_terminal_single_normalized_comparison_uniform
  refine ⟨C, hC, ?_⟩
  intro α η hα hη ι l u w hu hw hpos δ hδ R h
  obtain ⟨ε, hε, HE⟩ := HC η hη 2 (by norm_num)
  have hR : 1 < R := by dsimp only [R]; linarith only [hα.1]
  have hh : 0 < h ∧ h < 1 := by
    refine ⟨mul_pos hη.1 (pow_pos hα.1 2), ?_⟩
    exact (mul_le_of_le_one_right hη.1.le (pow_le_one₀ hα.1.le hα.2)).trans_lt
      (by linarith only [hη.2])
  have HY : Tendsto (fun x => (![R, u x, w x] : ExitTailState)) l (𝓝 ![R, 0, 0]) := by
    apply tendsto_pi_nhds.mpr
    intro i
    fin_cases i
    · exact tendsto_const_nhds
    · exact hu
    · exact hw
  have Henv := (tendsto_terminalSingleComparisonEnvelope_at_boundary hR hh).comp HY
  have Hsmall := (hu.add hw).eventually (gt_mem_nhds
    (show (0 : ℝ) + 0 < ε * α ^ (2 * 2) by simpa using mul_pos hε (pow_pos hα.1 (2 * 2))))
  have Hnear := Henv.eventually (gt_mem_nhds (lt_add_of_pos_right _ hδ))
  filter_upwards [hpos, Hsmall, Hnear] with x hp hs he
  have H := HE η α (u x + w x) (u x) (w x) le_rfl hη.2 hα
    (add_pos hp.1 hp.2) hs.le (by rw [abs_of_pos hp.1, abs_of_pos hp.2]) hp.1 hp.2
  refine ⟨H.1, H.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_left he.le (div_nonneg (by linarith only [hC]) (pow_nonneg hα.1.le 4))

/-- The boundary envelope vanishes jointly in radius and late height. -/
theorem tendsto_terminalSingleComparisonEnvelope_boundary {ι : Type*} {l : Filter ι}
    {R h : ι → ℝ} {R₀ : ℝ} (hR₀ : 1 < R₀) (hR : Tendsto R l (𝓝 R₀))
    (hh : Tendsto h l (𝓝 0)) (hhpos : ∀ᶠ x in l, 0 < h x) :
    Tendsto (fun x => terminalSingleComparisonEnvelope (h x) ![R x, 0, 0]) l (𝓝 0) := by
  have hRpos : 0 < R₀ := lt_trans zero_lt_one hR₀
  have HU := tendsto_referenceTail_decay hR₀
    (div_pos (sq_pos_of_pos hRpos) (by norm_num)) hR hh ((hR.pow 2).div_const 2) hhpos
  have HW := tendsto_referenceTail_decay hR₀ (by norm_num : (0 : ℝ) < 2) hR hh
    (show Tendsto (fun _ : ι => (2 : ℝ)) l (𝓝 2) from tendsto_const_nhds) hhpos
  have H := HU.add HW
  simp only [zero_add] at H
  apply H.congr'
  filter_upwards [hR.eventually (lt_mem_nhds hR₀), hhpos,
    hh.eventually (gt_mem_nhds (zero_lt_one : (0 : ℝ) < 1))] with x hx hp hx1
  exact (terminalSingleComparisonEnvelope_boundary hx ⟨hp, hx1⟩).symm

theorem tendsto_terminalSingleComparisonEnvelope_scaled_boundary {ι : Type*} {l : Filter ι}
    {R h : ι → ℝ} {R₀ C : ℝ} (hR₀ : 2 < R₀) (hR : Tendsto R l (𝓝 R₀))
    (hh : Tendsto h l (𝓝 0)) (hhpos : ∀ᶠ x in l, 0 < h x) :
    Tendsto (fun x => C / ((R x - 2) / 2) ^ 4 *
      terminalSingleComparisonEnvelope (h x) ![R x, 0, 0]) l (𝓝 0) := by
  have H := tendsto_terminalSingleComparisonEnvelope_boundary
    (by linarith only [hR₀] : 1 < R₀) hR hh hhpos
  have HD := ((hR.sub_const 2).div_const 2).pow 4
  have HN : ((R₀ - 2) / 2) ^ 4 ≠ 0 := pow_ne_zero 4 (div_pos (sub_pos.mpr hR₀) (by norm_num)).ne'
  have HC : Tendsto (fun x => C / ((R x - 2) / 2) ^ 4) l (𝓝 (C / ((R₀ - 2) / 2) ^ 4)) :=
    tendsto_const_nhds.div HD HN
  simpa only [mul_zero] using HC.mul H

end BianchiIX
