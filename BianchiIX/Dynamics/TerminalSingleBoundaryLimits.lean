import BianchiIX.Dynamics.TerminalSingleBoundaryDifferential
import BianchiIX.Dynamics.ReferenceTailDecayLimits

noncomputable section

namespace BianchiIX

open Filter Asymptotics
open scoped Topology

theorem tendsto_exitSingleBoundarySlope {ι : Type*} {l : Filter ι} {R h : ι → ℝ} {R₀ : ℝ}
    (hR₀ : 2 < R₀) (hR : Tendsto R l (𝓝 R₀)) (hh : Tendsto h l (𝓝 0)) :
    Tendsto (fun x => exitSingleBoundarySlope (R x) (h x)) l (𝓝 (-1 / (R₀ - 2))) := by
  have hRpos : 0 < R₀ := by linarith only [hR₀]
  have hbase : exitSingleBase R₀ 0 ≠ 0 :=
    ((sq_pos_of_pos (sub_pos.mpr hR₀)).trans_le
      (exitSingleBase_boundary_lower hR₀ (by simpa only [zero_pow (by norm_num : 2 ≠ 0)] using sq_nonneg R₀))).ne'
  have HR : ContinuousAt (fun p : ℝ × ℝ => p.1) (R₀, 0) := continuous_fst.continuousAt
  have HB : Continuous (fun p : ℝ × ℝ => exitSingleBase p.1 p.2) := by
    unfold exitSingleBase exitTailGap
    fun_prop
  have HS := (((((HR.pow 2).sub_const 4).div HB.continuousAt hbase).const_add 1).neg).div
    (HR.const_mul 2) (mul_pos (by norm_num) hRpos).ne'
  have H := HS.comp (hR.prodMk_nhds hh)
  change Tendsto (fun x => exitSingleBoundarySlope (R x) (h x)) l (𝓝 (exitSingleBoundarySlope R₀ 0)) at H
  rwa [exitSingleBoundarySlope_zero hR₀] at H

/-- The entire ordinary finite-tail differential has a joint late-height limit in operator norm. -/
theorem tendsto_terminalSinglePhase_boundary_fderiv {ι : Type*} {l : Filter ι} {R h : ι → ℝ} {R₀ : ℝ}
    (hR₀ : 2 < R₀) (hR : Tendsto R l (𝓝 R₀)) (hh : Tendsto h l (𝓝 0))
    (hhpos : ∀ᶠ x in l, 0 < h x) :
    Tendsto (fun x => fderiv ℝ (terminalSinglePhase (h x)) ![R x, 0, 0]) l
      (𝓝 ((1 / 2 : ℝ) • (ContinuousLinearMap.proj 0 : ExitTailState →L[ℝ] ℝ) +
        (-1 / R₀) • ContinuousLinearMap.proj 1)) := by
  have hR1 : 1 < R₀ := by linarith only [hR₀]
  have hRpos : 0 < R₀ := by linarith only [hR₀]
  have HS := tendsto_exitSingleBoundarySlope hR₀ hR hh
  have HEU := tendsto_referenceTail_decay hR1
    (div_pos (sq_pos_of_pos hRpos) (by norm_num)) hR hh ((hR.pow 2).div_const 2) hhpos
  have HEW := tendsto_referenceTail_decay hR1 (by norm_num : (0 : ℝ) < 2) hR hh
    (show Tendsto (fun _ : ι => (2 : ℝ)) l (𝓝 2) from tendsto_const_nhds) hhpos
  have HI : Tendsto (fun x => 1 / R x) l (𝓝 (1 / R₀)) := tendsto_const_nhds.div hR hRpos.ne'
  have HU := HI.neg.add ((HI.add HS).mul HEU)
  have HW := HS.mul HEW
  simp only [mul_zero, add_zero, neg_div] at HU HW
  let e0 : ExitTailState →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  let e1 : ExitTailState →L[ℝ] ℝ := ContinuousLinearMap.proj 1
  let e2 : ExitTailState →L[ℝ] ℝ := ContinuousLinearMap.proj 2
  have HT := ((tendsto_const_nhds (x := (1 / 2 : ℝ) • e0)).add
    (HU.smul (tendsto_const_nhds (x := e1)))).add (HW.smul (tendsto_const_nhds (x := e2)))
  simp only [zero_smul, add_zero] at HT
  simp only [neg_div]
  apply HT.congr'
  filter_upwards [hR.eventually (lt_mem_nhds hR₀), hhpos,
    hh.eventually (gt_mem_nhds (zero_lt_one : (0 : ℝ) < 1))] with x hx hp hx1
  apply ContinuousLinearMap.ext
  intro d
  rw [(terminalSinglePhase_boundary_differential hx ⟨hp, hx1⟩).2.2 d]
  simp [e0, e1, e2, add_apply, smul_apply, smul_eq_mul]
  ring

/-- At each fixed finite height the ordinary Taylor remainder is little-o in all three inputs. -/
theorem terminalSinglePhase_boundary_taylor {R h : ℝ} (hR : 2 < R) (hh : 0 < h ∧ h < 1) :
    (fun Z : ExitTailState => terminalSinglePhase h Z - (R - 2) / 2 -
      ((Z 0 - R) / 2 + (-1 / R + (1 / R + exitSingleBoundarySlope R h) *
        Real.exp (-(R ^ 2 / 2) * referenceTailDuration R h)) * Z 1 +
        (exitSingleBoundarySlope R h * Real.exp (-2 * referenceTailDuration R h)) * Z 2))
      =o[𝓝 (![R, 0, 0] : ExitTailState)] (fun Z => Z - ![R, 0, 0]) := by
  have H := terminalSinglePhase_boundary_differential hR hh
  have HT := (H.2.1.differentiableAt (by norm_num)).hasFDerivAt.isLittleO
  apply HT.congr_left
  intro Z
  rw [H.1, H.2.2]
  simp

end BianchiIX
