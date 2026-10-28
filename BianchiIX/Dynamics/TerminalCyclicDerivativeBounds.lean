import BianchiIX.Dynamics.ExitTailHeightGeometry
import BianchiIX.Dynamics.ExitTailHeightDerivativeBounds
import BianchiIX.Dynamics.ExitTailReconstruction
import BianchiIX.Dynamics.ProjectiveCycleDerivativeBounds
import BianchiIX.Algebra.ExitCycleEndpoint

noncomputable section

namespace BianchiIX

def terminalCyclicInput (h : ℝ) (Y : ExitTailState) : ProjectiveState :=
  projectiveCycle (coreTailState h Y)

/-- The actual fixed-height tail followed by the cyclic chart has the alpha^-2 derivative bound. -/
theorem exists_terminalCyclicInput_derivative_uniform {η₀ : ℝ} (hη₀ : 0 < η₀ ∧ η₀ ≤ 1 / 100)
    {J : ℕ} (hJ : 1 ≤ J) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ η α b u w : ℝ,
      η₀ ≤ η → η ≤ 1 / 100 → (0 < α ∧ α ≤ 1) →
      0 < b → b ≤ ε * α ^ (2 * J) → |u| + |w| ≤ b →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      coreTailValid h Y ∧ ContDiffAt ℝ 2 (terminalCyclicInput h) Y ∧
        ‖fderiv ℝ (terminalCyclicInput h) Y‖ ≤ C / α ^ 2 ∧
        ‖fderiv ℝ (fun Z => Real.log (projectiveCycleDenom (coreTailState h Z))) Y‖ ≤ C / α := by
  obtain ⟨A, _, εg, hεg, HG⟩ := exists_terminal_tail_geometry_uniform hη₀ hJ
  obtain ⟨B, hB, εd, hεd, HD⟩ := exists_terminal_exitReturn_two_bounds_uniform
    ⟨hη₀.1, by linarith only [hη₀.2]⟩ hJ
  have hB0 : 0 < B := lt_of_lt_of_le (by norm_num) hB
  refine ⟨48 * B, by linarith only [hB], min εg εd, lt_min hεg hεd, ?_⟩
  intro η α b u w hηlo hηhi hα hb hsmall hsum Y h
  have hα0 : 0 < α := hα.1
  have hsmallg := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_left εg εd) (pow_nonneg hα.1.le (2 * J)))
  have hsmalld : b ≤ εd * α ^ J := hsmall.trans
    ((mul_le_mul_of_nonneg_right (min_le_right εg εd) (pow_nonneg hα.1.le (2 * J))).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hα.1.le hα.2 (by omega)) hεd.le))
  obtain ⟨HV, HM, HR, HW, HB, HVbounds, HH⟩ := HG η α b u w hηlo hηhi hα hb hsmallg hsum
  change coreTailValid h Y at HV
  have Hder := HD η α b u w hηlo (by linarith only [hηhi]) hα hb hsmalld hsum
  let y := coreTailState h Y
  have hr : 7 / 4 ≤ coreRadius (y 0) (y 2) := by linarith only [(abs_le.mp HR).1, HB, hα.1]
  have hh : |h| ≤ 1 := by
    rw [← coreTailState_active HV, abs_of_nonneg HVbounds.1]
    linarith only [HVbounds.2, hα.2]
  have hR : 1 < Y 0 := by change 1 < 2 + 2 * α; linarith only [hα.1]
  have Htail := coreTailState_fderiv_bound_of_radial hR HV HM hr hh Hder.2.1 Hder.2.2.1
  have Hreg := (coreTail_regular_of_valid hR HV).2.1
  have hH : 0 < projectiveCycleDenom y := lt_of_lt_of_le (by positivity) HH
  have HGc := contDiffAt_projectiveCycle 2 hH.ne'
  have Hgap := exitTailGap_terminal_offset hα HB HR HVbounds
  rw [exitTailGap_of_coreRadius HM] at Hgap
  have hm : |y 0 + 1| ≤ 3 * α := abs_le.mpr (by constructor <;> linarith only [Hgap.1, Hgap.2, hα.1])
  have hw : |y 1| + |y 2| + |y 3| ≤ 3 * α := by
    rw [abs_of_nonneg HVbounds.1]
    linarith only [HW, HB, HVbounds.2, hα.1]
  have Hcycle : ‖fderiv ℝ projectiveCycle y‖ ≤ 24 / α ^ 2 :=
    fderiv_norm_le_of_coordinate_bounds (by positivity) (HGc.differentiableAt (by norm_num))
      (fun i => (projectiveCycle_terminal_operator_bounds hα.1 HH hm hw i).1)
  have Hlog := projectiveCycle_log_denom_derivative_bound hα.1 HH hm hw
  have Hlogreg : ContDiffAt ℝ 2 (fun z => Real.log (projectiveCycleDenom z)) y :=
    (contDiff_projectiveCycleDenom 2).contDiffAt.log hH.ne'
  refine ⟨HV, ContDiffAt.comp (g := projectiveCycle) (f := coreTailState h) Y HGc Hreg, ?_, ?_⟩
  · change ‖fderiv ℝ (projectiveCycle ∘ coreTailState h) Y‖ ≤ _
    rw [fderiv_comp Y (HGc.differentiableAt (by norm_num)) (Hreg.differentiableAt (by norm_num))]
    exact ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul Hcycle Htail (norm_nonneg _) (by positivity))).trans_eq (by ring)
  · change ‖fderiv ℝ ((fun z => Real.log (projectiveCycleDenom z)) ∘ coreTailState h) Y‖ ≤ _
    rw [fderiv_comp Y (Hlogreg.differentiableAt (by norm_num)) (Hreg.differentiableAt (by norm_num))]
    apply ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul Hlog Htail (norm_nonneg _) (by positivity))).trans
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hα.1.le
    nlinarith only [hB]

end BianchiIX
