import BianchiIX.Dynamics.CoreAngle
import BianchiIX.Dynamics.IntegralClock
import BianchiIX.Dynamics.FlowTransport

noncomputable section

namespace BianchiIX

open Set

/-- Integrating the positive angle rate constructs its inverse on the entire chosen interval. -/
theorem exists_scaled_coreAngle_reparametrization {β : ℝ → ProjectiveState} {a : ℝ → ℝ}
    {I : Set ℝ} {s : ℝ} (hI : Convex ℝ I) (ho : IsOpen I) (hs : s ∈ I)
    (ha : ContinuousOn a I) (ha_pos : ∀ t ∈ I, 0 < a t)
    (hβ : ∀ t ∈ I, HasDerivAt β (a t • projectiveField (β t)) t)
    (hv : ∀ t ∈ I, 0 < β t 2)
    (hd : ∀ t ∈ I, 0 < coreClockFactor (coreRadius (β t 0) (β t 2)) (β t 1) (β t 3)) :
    ∃ e : OpenPartialHomeomorph ℝ ℝ,
      e.source = I ∧
      (∀ t ∈ I, e t = coreAngle (β t 0) (β t 2) - coreAngle (β s 0) (β s 2)) ∧
      Convex ℝ e.target ∧ 0 ∈ e.target ∧ e.symm 0 = s ∧ StrictMonoOn e I ∧
      (∀ z ∈ e.target,
        coreAngle (β (e.symm z) 0) (β (e.symm z) 2) = z + coreAngle (β s 0) (β s 2) ∧
        HasDerivAt (fun u => toCoreAngleState (β (e.symm u)))
          (coreAngleField (z + coreAngle (β s 0) (β s 2)) (toCoreAngleState (β (e.symm z)))) z ∧
        fromCoreAngleState (z + coreAngle (β s 0) (β s 2)) (toCoreAngleState (β (e.symm z))) = β (e.symm z)) := by
  let q : ℝ → ℝ := fun t => a t * coreRadius (β t 0) (β t 2) *
    coreClockFactor (coreRadius (β t 0) (β t 2)) (β t 1) (β t 3)
  have hcoord (i : Fin 4) : ContinuousOn (fun t => β t i) I :=
    fun t ht => (hasDerivAt_pi.mp (hβ t ht) i).continuousAt.continuousWithinAt
  have hR : ContinuousOn (fun t => coreRadius (β t 0) (β t 2)) I := by
    unfold coreRadius coreEnergy
    exact (((hcoord 0).sub continuousOn_const).pow 2 |>.add ((hcoord 2).pow 2)).sqrt
  have hq : ContinuousOn q I := by
    apply (ha.mul hR).mul
    exact continuousOn_const.sub (((hcoord 1).sub (hcoord 3)).pow 2 |>.div (hR.pow 2)
      (fun t ht => pow_ne_zero 2 (ne_of_gt (coreRadius_pos (hv t ht)))))
  have hqpos : ∀ t ∈ I, 0 < q t := fun t ht =>
    mul_pos (mul_pos (ha_pos t ht) (coreRadius_pos (hv t ht))) (hd t ht)
  have hz (t : ℝ) (ht : t ∈ I) :
      HasDerivAt (fun u => coreAngle (β u 0) (β u 2)) (q t) t :=
    hasDerivAt_coreAngle_scaled (hβ t ht) (hv t ht)
  have hg (t : ℝ) (ht : t ∈ I) :
      HasDerivAt (fun u => integralClock q s u + coreAngle (β s 0) (β s 2)) (q t) t :=
    (hasStrictDerivAt_integralClock hI ho hq hs ht).hasDerivAt.add_const _
  have heq : I.EqOn (fun t => coreAngle (β t 0) (β t 2))
      (fun t => integralClock q s t + coreAngle (β s 0) (β s 2)) :=
    ho.eqOn_of_deriv_eq hI.isPreconnected
      (fun t ht => (hz t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => (hg t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => (hz t ht).deriv.trans (hg t ht).deriv.symm) hs (by rw [integralClock_initial, zero_add])
  let e := positiveIntegralClock hI ho hq hs hqpos
  have he0 : e s = 0 := integralClock_initial q s
  refine ⟨e, rfl, ?_, convex_positiveIntegralClock_target hI ho hq hs hqpos,
    he0 ▸ e.map_source hs, positiveIntegralClock_symm_zero hI ho hq hs hqpos,
    strictMonoOn_integralClock hI ho hq hs hqpos, ?_⟩
  · intro t ht
    change integralClock q s t = _
    linarith [heq ht]
  · intro z hzmem
    have ht : e.symm z ∈ I := e.map_target hzmem
    have htime : coreAngle (β (e.symm z) 0) (β (e.symm z) 2) = z + coreAngle (β s 0) (β s 2) := by
      have H := heq ht
      change _ = e (e.symm z) + _ at H
      rw [e.right_inv hzmem] at H
      exact H
    have hinv := hasDerivAt_positiveIntegralClock_symm hI ho hq hs hqpos hzmem
    have hstate := (hasDerivAt_toCoreAngleState_scaled (hβ _ ht) (hv _ ht) (ne_of_gt (hd _ ht))).scomp z hinv
    have hstate' : HasDerivAt (fun u => toCoreAngleState (β (e.symm u)))
        (coreAngleField (z + coreAngle (β s 0) (β s 2)) (toCoreAngleState (β (e.symm z)))) z := by
      change HasDerivAt _ ((1 / q (e.symm z)) • (q (e.symm z) • _)) z at hstate
      simp only [smul_smul, one_div, inv_mul_cancel₀ (ne_of_gt (hqpos _ ht)), one_smul, htime] at hstate
      convert! hstate using 1
    refine ⟨htime, hstate', ?_⟩
    rw [← htime]
    exact fromCoreAngleState_toCoreAngleState (hv _ ht)

/-- The exact normalized Einstein flow satisfies the angle system on every positive-clock interval. -/
theorem exists_normalized_coreAngle_reparametrization {x : NormalizedState} {t₀ s : ℝ}
    {I : Set ℝ} (hI : Convex ℝ I) (ho : IsOpen I) (hs : s ∈ I)
    (hdom : I ⊆ normalizedMaxDomain x t₀) (hc : stateConstraint x = 1)
    (hA : ∀ t ∈ I, 0 < 1 + normalizedMaxCurve x t₀ t 0)
    (hv : ∀ t ∈ I, 0 < toProjectiveState (normalizedMaxCurve x t₀ t) 2)
    (hd : ∀ t ∈ I, let y := toProjectiveState (normalizedMaxCurve x t₀ t)
      0 < coreClockFactor (coreRadius (y 0) (y 2)) (y 1) (y 3)) :
    let β := fun t => toProjectiveState (normalizedMaxCurve x t₀ t)
    ∃ e : OpenPartialHomeomorph ℝ ℝ,
      e.source = I ∧
      (∀ t ∈ I, e t = coreAngle (β t 0) (β t 2) - coreAngle (β s 0) (β s 2)) ∧
      Convex ℝ e.target ∧ 0 ∈ e.target ∧ e.symm 0 = s ∧ StrictMonoOn e I ∧
      (∀ z ∈ e.target,
        coreAngle (β (e.symm z) 0) (β (e.symm z) 2) = z + coreAngle (β s 0) (β s 2) ∧
        HasDerivAt (fun u => toCoreAngleState (β (e.symm u)))
          (coreAngleField (z + coreAngle (β s 0) (β s 2)) (toCoreAngleState (β (e.symm z)))) z ∧
        fromCoreAngleState (z + coreAngle (β s 0) (β s 2)) (toCoreAngleState (β (e.symm z))) = β (e.symm z)) := by
  apply exists_scaled_coreAngle_reparametrization (a := fun t => 1 + normalizedMaxCurve x t₀ t 0)
    hI ho hs ?_ hA ?_ hv hd
  · intro t ht
    exact (continuousAt_const.add (hasDerivAt_pi.mp
      (hasDerivAt_normalizedMaxCurve (hdom ht)) 0).continuousAt).continuousWithinAt
  · intro t ht
    exact hasDerivAt_toProjectiveState_normalized (hasDerivAt_normalizedMaxCurve (hdom ht))
      (ne_of_gt (hA t ht)) ((normalizedMaxCurve_constraint (hdom ht)).trans hc)

end BianchiIX
