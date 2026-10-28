import BianchiIX.Dynamics.ExitActualVariation
import BianchiIX.Dynamics.ExitTailRegularity
import BianchiIX.Dynamics.ProjectiveFlowSecondRegularity

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem exitClockProjection_add_field {y : ProjectiveState} (hv : 0 < y 2)
    (hm : y 0 < 1) (hd : exitClockRate y ≠ 0) (v : ProjectiveState) (a : ℝ) :
    exitClockProjection y (v + a • projectiveOriginalField y) = exitClockProjection y v := by
  simp only [exitClockProjection, map_add, map_smul, toExitTailState_fderiv_field hv hm hd,
    exitLogClock_fderiv_field hv, add_smul, smul_smul]
  module

/-- At fixed target height the arrival-time correction is exactly the removed clock displacement. -/
theorem coreTailState_exit_differential {Y : ExitTailState} {η : ℝ}
    (hR : 1 < Y 0) (H : coreTailValid η Y)
    (hv : 0 < coreTailState η Y 2) (hm : coreTailState η Y 0 < 1)
    (hd : exitClockRate (coreTailState η Y) ≠ 0) (v : ExitTailState) :
    fderiv ℝ (fun Z => toExitTailState (coreTailState η Z)) Y v =
      exitProjectedFlowVariation (coreTailEntry Y) 0 (coreTailTime η Y)
        (fderiv ℝ coreTailEntry Y v) := by
  obtain ⟨hτ, hP, hnear⟩ := coreTail_regular_of_valid hR H
  have hD := coreTailValid_denom_pos H
  have hA := (H.2.1 (coreTailTime η Y) ⟨H.1.1.1.le, le_rfl⟩).2
  have hentry := ((contDiffAt_coreTailEntry 1 hR).differentiableAt (by norm_num)).hasFDerivAt
  have htime := (hτ.differentiableAt (by norm_num)).hasFDerivAt
  have hflow := (hasFDerivAt_projectiveOriginalFlow hD H.1.1.2.1 hA).comp Y (hentry.prodMk htime)
  change HasFDerivAt (coreTailState η) _ Y at hflow
  have hendpoint : fderiv ℝ (coreTailState η) Y v =
      projectiveFlowDifferential (coreTailEntry Y) 0 (coreTailTime η Y) (fderiv ℝ coreTailEntry Y v) +
        fderiv ℝ (coreTailTime η) Y v • projectiveOriginalField (coreTailState η Y) := by
    rw [hflow.fderiv]
    rfl
  have hclock := ((contDiffAt_exitLogClock 1 hv).differentiableAt (by norm_num)).hasFDerivAt
  have hstate := (hP.differentiableAt (by norm_num)).hasFDerivAt
  have heq : (fun Z => exitLogClock (coreTailState η Z)) =ᶠ[𝓝 Y] (fun _ => -Real.log η) := by
    filter_upwards [hnear] with Z hZ
    simp only [exitLogClock, coreTailState_active hZ]
  have hzero := ((hclock.comp Y hstate).congr_of_eventuallyEq heq.symm).unique
    (hasFDerivAt_const (-Real.log η) Y)
  have hz := congrArg (fun L : ExitTailState →L[ℝ] ℝ => L v) hzero
  change fderiv ℝ exitLogClock (coreTailState η Y) (fderiv ℝ (coreTailState η) Y v) = 0 at hz
  have hp := ((contDiffAt_toExitTailState 1 hv).differentiableAt (by norm_num)).hasFDerivAt
  have hout := hp.comp Y hstate
  change HasFDerivAt (fun Z => toExitTailState (coreTailState η Z)) _ Y at hout
  rw [hout.fderiv]
  change fderiv ℝ toExitTailState (coreTailState η Y) (fderiv ℝ (coreTailState η) Y v) = _
  calc
    _ = exitClockProjection (coreTailState η Y) (fderiv ℝ (coreTailState η) Y v) := by
      simp only [exitClockProjection, hz, zero_smul, sub_zero]
    _ = _ := by
      rw [hendpoint, exitClockProjection_add_field hv hm hd]
      rfl

theorem exists_terminal_exitReturn_first_bound {η : ℝ} (hη : 0 < η ∧ η < 1) {J : ℕ} (hJ : 1 ≤ J) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ α b u w : ℝ,
      (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ J → |u| + |w| ≤ b →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      coreTailValid h Y ∧ ContDiffAt ℝ 2 (fun Z => toExitTailState (coreTailState h Z)) Y ∧
        ‖fderiv ℝ (fun Z => toExitTailState (coreTailState h Z)) Y‖ ≤ C := by
  obtain ⟨C, hC, ε₁, hε₁, HB⟩ := exists_terminal_exitProjected_entry_bound hη hJ
  obtain ⟨A, hA, ε₂, hε₂, HE⟩ := exists_terminal_coreTail_valid hη hJ
  refine ⟨C, hC, min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  intro α b u w hα hb hsmall hw Y h
  have hb₁ := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_left ε₁ ε₂) (pow_nonneg hα.1.le J))
  have hb₂ := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_right ε₁ ε₂) (pow_nonneg hα.1.le J))
  have H := HB α b u w hα hb hb₁ hw
  obtain ⟨hvalid, hT, _, HP⟩ := HE α b u w hα hb hb₂ hw
  have ht : coreTailTime h Y ∈ Icc 0 (coreTailTime h Y) := ⟨hT.le, le_rfl⟩
  have hphys : exitPhysicalRegion h (coreTailState h Y) := (HP _ ht).2.1
  have hh : 0 < h := mul_pos hη.1 (pow_pos hα.1 J)
  have hv : 0 < coreTailState h Y 2 := hh.trans_le hphys.2.2.2.1.1
  have hm : coreTailState h Y 0 < 1 := lt_of_le_of_lt hphys.1 (by norm_num)
  have hd : exitClockRate (coreTailState h Y) ≠ 0 :=
    (lt_of_lt_of_le (by norm_num) (exitPhysicalRegion_clock hh hphys)).ne'
  have hR : 1 < Y 0 := by change 1 < 2 + 2 * α; linarith only [hα.1]
  refine ⟨hvalid, (contDiffAt_toExitTailState 2 hv).comp Y (coreTail_regular_of_valid hR hvalid).2.1, ?_⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (by linarith only [hC])
  intro v
  rw [coreTailState_exit_differential hR hvalid hv hm hd v]
  exact H.2 _ ht v

end BianchiIX
