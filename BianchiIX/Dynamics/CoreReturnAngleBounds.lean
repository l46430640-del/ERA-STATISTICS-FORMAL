import BianchiIX.Dynamics.CoreLogDerivative

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem coreRadiusEntry_angle_bound {Y : CoreAngleState} (hk : 6 ≤ Y 0)
    (v : CoreAngleState) :
    |fderiv ℝ (fun Z => projectiveCoreAngle (coreRadiusEntry Z)) Y v| ≤
      2 * |v 0| / Y 0 := by
  have hgap := coreRadiusEntry_gap hk
  have hk0 : 0 < Y 0 := by linarith only [hk]
  have hs : 0 < Real.sqrt (Y 0 ^ 2 - 1) := lt_of_lt_of_le (by positivity) hgap
  rw [coreRadiusEntry_angle_fderiv (by linarith only [hk]), abs_div, abs_neg, abs_of_pos hs]
  exact (div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hgap).trans_eq (by ring)

/-- Local event uniqueness identifies derivatives of any continuous hitting-time branch. -/
theorem coreReturn_exit_angle_bound {Y : CoreAngleState} {τ : CoreAngleState → ℝ}
    (hk : 6 ≤ Y 0) (hD : 0 < projectiveStateDenom (coreRadiusEntry Y))
    (hτ : ContinuousAt τ Y)
    (ht : τ Y ∈ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry Y)) 0)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState (coreRadiusEntry Y)) 0 (τ Y) 0)
    (hcore : coreRegion (Y 0) (projectiveOriginalFlow (coreRadiusEntry Y) 0 (τ Y)))
    (hhit : ∀ᶠ Z in 𝓝 Y, projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z) 2 = 1)
    (hM : projectiveOriginalFlow (coreRadiusEntry Y) 0 (τ Y) 0 < 1)
    (v : CoreAngleState) :
    |fderiv ℝ (fun Z => projectiveCoreAngle (projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z))) Y v| ≤
      2 * |coreProjectedFlowVariation (coreRadiusEntry Y) 0 (τ Y)
        (fderiv ℝ coreRadiusEntry Y v) 0| / Y 0 := by
  have hV := hhit.self_of_nhds
  obtain ⟨σ, _, _, _, huniq, _, hcZ, hderiv⟩ :=
    exists_coreExit_event hk hD ht hA hcore hV hM
  have hentry := contDiffAt_coreRadiusEntry 1 (by linarith only [hk] : 1 < Y 0)
  have hpair : ContinuousAt (fun Z => (coreRadiusEntry Z, τ Z)) Y :=
    hentry.continuousAt.prodMk hτ
  have heq : (fun Z => projectiveCoreAngle (projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z))) =ᶠ[𝓝 Y]
      (fun Z => projectiveCoreAngle (projectiveOriginalFlow (coreRadiusEntry Z) 0 (σ (coreRadiusEntry Z)))) := by
    filter_upwards [hpair.eventually huniq, hhit] with Z hZ hh
    rw [(hZ.2.mp hh).symm]
  have hchain := ((hcZ.differentiableAt (by norm_num)).hasFDerivAt).comp Y
    ((hentry.differentiableAt (by norm_num)).hasFDerivAt)
  change HasFDerivAt
    (fun Z => projectiveCoreAngle (projectiveOriginalFlow (coreRadiusEntry Z) 0 (σ (coreRadiusEntry Z)))) _ Y at hchain
  rw [heq.fderiv_eq, hchain.fderiv, ContinuousLinearMap.comp_apply, (hderiv (fderiv ℝ coreRadiusEntry Y v)).1]
  exact coreRegion_exit_angle_bound hk hcore hV hM _

end BianchiIX
