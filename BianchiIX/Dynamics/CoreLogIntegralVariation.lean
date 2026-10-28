import BianchiIX.Analysis.ClockIntegralVariation
import BianchiIX.Dynamics.CoreMultipliers

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology

def coreLogBoundary (y : ProjectiveState) (t₀ t : ℝ) (w : ProjectiveState) (i : Fin 2) : ℝ :=
  let z := projectiveOriginalFlow y t₀ t
  coreLogRates (projectiveCoreAngle z) (toCoreAngleState z) i *
    fderiv ℝ projectiveCoreAngle z (projectiveFlowDifferential y t₀ t w)

theorem continuousAt_coreLogRates_stateDifferential {z : ℝ} {Y : CoreAngleState}
    (hr : Y 0 ≠ 0) (hd : coreAuxiliary z Y 1 ≠ 0) :
    ContinuousAt (fun p : ℝ × CoreAngleState => fderiv ℝ (coreLogRates p.1) p.2) (z, Y) := by
  have hp : ContDiffAt ℝ 1
      (fun q : (ℝ × CoreAngleState) × CoreAngleState => (q.1.1, q.2)) ((z, Y), Y) :=
    (contDiffAt_fst.comp _ contDiffAt_fst).prodMk contDiffAt_snd
  have hL := (contDiffAt_coreLogRates_joint 1 z hr hd).comp ((z, Y), Y)
    (f := fun q : (ℝ × CoreAngleState) × CoreAngleState => (q.1.1, q.2)) hp
  exact (hL.fderiv (m := 0) contDiffAt_snd (by norm_num)).continuousAt

/-- The physical clock variation is exactly a total derivative, without wall division. -/
theorem hasDerivAt_coreLogBoundary {y : ProjectiveState} {t₀ t : ℝ}
    (hD : 0 < projectiveStateDenom y)
    (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hV : 0 < projectiveOriginalFlow y t₀ t 2)
    (hd : coreClockFactor (coreRadius (projectiveOriginalFlow y t₀ t 0)
      (projectiveOriginalFlow y t₀ t 2)) (projectiveOriginalFlow y t₀ t 1)
        (projectiveOriginalFlow y t₀ t 3) ≠ 0) (w : ProjectiveState) (i : Fin 2) :
    let z := projectiveOriginalFlow y t₀ t
    let v := projectiveFlowDifferential y t₀ t w
    HasDerivAt (fun s => coreLogBoundary y t₀ s w i)
      ((fderiv ℝ coreOriginalLogRates z v) i - coreOriginalClockRate z *
        (fderiv ℝ (coreLogRates (projectiveCoreAngle z)) (toCoreAngleState z)
          (coreProjectedFlowVariation y t₀ t w)) i) t := by
  intro z v
  have hc := (normalizedMaxCurve_constraint ht).trans (fromProjectiveState_constraint (ne_of_gt hD))
  have hDz : projectiveStateDenom z ≠ 0 := ne_of_gt (toProjectiveState_denom_pos hA hc)
  have hr : toCoreAngleState z 0 ≠ 0 := ne_of_gt (coreRadius_pos hV)
  have hd' : coreAuxiliary (projectiveCoreAngle z) (toCoreAngleState z) 1 ≠ 0 := by
    rwa [coreAuxiliary_projective_clockFactor hV]
  have hclock : (fun x => fderiv ℝ projectiveCoreAngle x (projectiveOriginalField x)) =ᶠ[𝓝 z]
      coreOriginalClockRate := by
    filter_upwards [(continuous_apply 2).continuousAt.eventually (isOpen_Ioi.mem_nhds hV)] with x hx
    exact projectiveCoreAngle_fderiv_field hx
  have hLc := contDiffAt_pi.mp (contDiffAt_coreLogRates_joint 1 (projectiveCoreAngle z) hr hd') i
  have hL := hLc.differentiableAt (by norm_num)
  have H := hasDerivAt_clock_integral_boundary
    ((contDiffAt_toCoreAngleState 1 hV).differentiableAt (by norm_num))
    (contDiffAt_projectiveCoreAngle 2 hV)
    ((contDiffAt_projectiveOriginalField 1 hDz).differentiableAt (by norm_num))
    ((contDiffAt_coreOriginalClockRate 1 hV hDz).differentiableAt (by norm_num)) hL
    (hasDerivAt_projectiveOriginalFlow_time hD ht hA)
    (hasDerivAt_projectiveFlowDifferential_apply hD ht hA w) hclock
    (toCoreAngleState_fderiv_field hV hd)
  have hrate := (contDiffAt_coreOriginalLogRates 1 hV hDz hd).differentiableAt (by norm_num)
  have hslice := (contDiffAt_coreLogRates 1 (projectiveCoreAngle z) hr hd').differentiableAt (by norm_num)
  apply H.congr_deriv
  change fderiv ℝ (fun q => coreOriginalLogRates q i) z v - coreOriginalClockRate z *
    fderiv ℝ (fun X => coreLogRates (projectiveCoreAngle z) X i) (toCoreAngleState z)
      (coreProjectedFlowVariation y t₀ t w) = _
  rw [fderiv_apply hrate i, fderiv_apply hslice i]
  rfl

theorem coreFlow_log_rate_integral_variation {y : ProjectiveState} {t₀ k a b : ℝ}
    (hk : 6 ≤ k) (hab : a ≤ b) (hD : 0 < projectiveStateDenom y)
    (hdom : Icc a b ⊆ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : ∀ t ∈ Icc a b, 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hcore : ∀ t ∈ Icc a b, coreRegion k (projectiveOriginalFlow y t₀ t))
    (w : ProjectiveState) (i : Fin 2) :
    let β := projectiveOriginalFlow y t₀
    let ξ := fun t => coreProjectedFlowVariation y t₀ t w
    (∫ t in a..b, (fderiv ℝ coreOriginalLogRates (β t) (projectiveFlowDifferential y t₀ t w)) i) =
      (∫ t in a..b, coreOriginalClockRate (β t) *
        (fderiv ℝ (coreLogRates (projectiveCoreAngle (β t))) (toCoreAngleState (β t)) (ξ t)) i) +
      coreLogBoundary y t₀ b w i - coreLogBoundary y t₀ a w i := by
  intro β ξ
  have hflow (t : ℝ) (ht : t ∈ Icc a b) := hasDerivAt_projectiveOriginalFlow_time hD (hdom ht) (hA t ht)
  have hv (t : ℝ) (ht : t ∈ Icc a b) : 0 < β t 2 := lt_of_lt_of_le zero_lt_one (hcore t ht).2.1
  have hreg (t : ℝ) (ht : t ∈ Icc a b) := coreRegion_clock_regular hk (hcore t ht)
  apply integral_eq_projected_add_boundary hab
  · intro t ht
    have hdiff := (contDiffAt_coreOriginalLogRates 1 (hv t ht) (ne_of_gt (hreg t ht).1)
      (ne_of_gt (hreg t ht).2.1)).continuousAt_fderiv (by norm_num)
    have hvar := (hasDerivAt_projectiveFlowDifferential_apply hD (hdom ht) (hA t ht) w).continuousAt
    exact (continuousAt_pi.mp ((hdiff.comp (hflow t ht).continuousAt).clm_apply hvar) i).continuousWithinAt
  · intro t ht
    have hd : coreAuxiliary (projectiveCoreAngle (β t)) (toCoreAngleState (β t)) 1 ≠ 0 := by
      rw [coreAuxiliary_projective_clockFactor (hv t ht)]
      exact ne_of_gt (hreg t ht).2.1
    have hdiff := continuousAt_coreLogRates_stateDifferential (ne_of_gt (coreRadius_pos (hv t ht))) hd
    have hp := ((contDiffAt_projectiveCoreAngle 1 (hv t ht)).continuousAt.comp (hflow t ht).continuousAt).prodMk
      ((contDiffAt_toCoreAngleState 1 (hv t ht)).continuousAt.comp (hflow t ht).continuousAt)
    have hvar := (hasDerivAt_coreProjectedFlowVariation hD (hdom ht) (hA t ht) (hv t ht)
      (ne_of_gt (hreg t ht).2.1) w).continuousAt
    have hcomp := hdiff.comp
      (g := fun p : ℝ × CoreAngleState => fderiv ℝ (coreLogRates p.1) p.2)
      (f := fun s : ℝ => (projectiveCoreAngle (β s), toCoreAngleState (β s))) hp
    have hvalue := continuousAt_pi.mp (hcomp.clm_apply hvar) i
    have hrate := (contDiffAt_coreOriginalClockRate 1 (hv t ht) (ne_of_gt (hreg t ht).1)).continuousAt.comp
      (hflow t ht).continuousAt
    exact (hrate.mul hvalue).continuousWithinAt
  · intro t ht
    exact hasDerivAt_coreLogBoundary hD (hdom ht) (hA t ht) (hv t ht) (ne_of_gt (hreg t ht).2.1) w i

end BianchiIX
