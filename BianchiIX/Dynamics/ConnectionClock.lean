import BianchiIX.Algebra.ConnectionBounds
import BianchiIX.Dynamics.CoreAngleClock

noncomputable section

namespace BianchiIX

open Set

def connectionClockRate (y : ProjectiveState) : ℝ :=
  connectionSpeed (-y 0) (y 1) (y 2) (y 3)

def connectionLogField (y : ProjectiveState) : ProjectiveState :=
  (connectionClockRate y)⁻¹ • projectiveField y

theorem contDiff_connectionClockRate (n : WithTop ℕ∞) : ContDiff ℝ n connectionClockRate := by
  unfold connectionClockRate connectionSpeed coupling
  fun_prop

theorem contDiffAt_connectionLogField (n : WithTop ℕ∞) {y : ProjectiveState}
    (hD : connectionClockRate y ≠ 0) : ContDiffAt ℝ n connectionLogField y := by
  exact ((contDiff_connectionClockRate n).contDiffAt.inv hD).smul
    (contDiff_projectiveField n).contDiffAt

theorem connectionLogField_components {y : ProjectiveState} (hD : connectionClockRate y ≠ 0) :
    connectionLogField y 0 = phaseVelocity (y 0) (y 1) (y 2) (y 3) / connectionClockRate y ∧
    connectionLogField y 1 = connectionStrongRate (-y 0) (y 1) (y 2) (y 3) /
      connectionClockRate y * y 1 ∧
    connectionLogField y 2 = (y 0 - 1 - coupling (y 1) (y 2) (y 3)) /
      connectionClockRate y * y 2 ∧
    connectionLogField y 3 = y 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (connectionClockRate y)⁻¹ * phaseVelocity _ _ _ _ = _
    ring
  · change (connectionClockRate y)⁻¹ * strongVelocity _ _ _ _ = _
    dsimp [strongVelocity, connectionStrongRate]
    ring
  · change (connectionClockRate y)⁻¹ * activeVelocity _ _ _ _ = _
    dsimp [activeVelocity]
    ring
  · change (connectionClockRate y)⁻¹ * (connectionClockRate y * y 3) = y 3
    rw [← mul_assoc, inv_mul_cancel₀ hD, one_mul]

theorem hasDerivAt_connectionLog_scaled {β : ℝ → ProjectiveState} {a t : ℝ}
    (hβ : HasDerivAt β (a • projectiveField (β t)) t) (hw : β t 3 ≠ 0) :
    HasDerivAt (fun s => Real.log (β s 3)) (a * connectionClockRate (β t)) t := by
  have H := (hasDerivAt_pi.mp hβ 3).log hw
  convert! H using 1
  change a * connectionClockRate (β t) = a * weakVelocity (β t 0) (β t 1) (β t 2) (β t 3) / β t 3
  dsimp [connectionClockRate, connectionSpeed, weakVelocity]
  field_simp

/-- The growing wall is an exact clock on the whole chosen positive-rate interval. -/
theorem exists_scaled_connectionLog_reparametrization {β : ℝ → ProjectiveState} {a : ℝ → ℝ}
    {I : Set ℝ} {s : ℝ} (hI : Convex ℝ I) (ho : IsOpen I) (hs : s ∈ I)
    (ha : ContinuousOn a I) (hapos : ∀ t ∈ I, 0 < a t)
    (hβ : ∀ t ∈ I, HasDerivAt β (a t • projectiveField (β t)) t)
    (hw : ∀ t ∈ I, 0 < β t 3) (hD : ∀ t ∈ I, 0 < connectionClockRate (β t)) :
    ∃ e : OpenPartialHomeomorph ℝ ℝ,
      e.source = I ∧
      (∀ t ∈ I, e t = Real.log (β t 3) - Real.log (β s 3)) ∧
      Convex ℝ e.target ∧ 0 ∈ e.target ∧ e.symm 0 = s ∧ StrictMonoOn e I ∧
      (∀ z ∈ e.target,
        HasDerivAt e.symm (1 / (a (e.symm z) * connectionClockRate (β (e.symm z)))) z ∧
        β (e.symm z) 3 = β s 3 * Real.exp z ∧
        HasDerivAt (fun u => β (e.symm u)) (connectionLogField (β (e.symm z))) z) := by
  let q : ℝ → ℝ := fun t => a t * connectionClockRate (β t)
  have hq : ContinuousOn q I := ha.mul ((contDiff_connectionClockRate 1).continuous.comp_continuousOn
    (HasDerivAt.continuousOn hβ))
  have hqpos : ∀ t ∈ I, 0 < q t := fun t ht => mul_pos (hapos t ht) (hD t ht)
  have hz (t : ℝ) (ht : t ∈ I) : HasDerivAt (fun u => Real.log (β u 3)) (q t) t :=
    hasDerivAt_connectionLog_scaled (hβ t ht) (ne_of_gt (hw t ht))
  have hg (t : ℝ) (ht : t ∈ I) :
      HasDerivAt (fun u => integralClock q s u + Real.log (β s 3)) (q t) t :=
    (hasStrictDerivAt_integralClock hI ho hq hs ht).hasDerivAt.add_const _
  have heq : I.EqOn (fun t => Real.log (β t 3))
      (fun t => integralClock q s t + Real.log (β s 3)) :=
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
    linarith only [heq ht]
  · intro z hzmem
    have ht : e.symm z ∈ I := e.map_target hzmem
    have hinv := hasDerivAt_positiveIntegralClock_symm hI ho hq hs hqpos hzmem
    have htime : Real.log (β (e.symm z) 3) = z + Real.log (β s 3) := by
      have H := heq ht
      change _ = e (e.symm z) + _ at H
      rwa [e.right_inv hzmem] at H
    refine ⟨hinv, ?_, ?_⟩
    · have H := congrArg Real.exp htime
      rw [Real.exp_log (hw _ ht), Real.exp_add, Real.exp_log (hw s hs)] at H
      exact H.trans (mul_comm _ _)
    · have H := (hβ _ ht).scomp z hinv
      convert! H using 1
      ext i
      change (connectionClockRate (β (e.symm z)))⁻¹ * projectiveField (β (e.symm z)) i =
        (1 / (a (e.symm z) * connectionClockRate (β (e.symm z)))) *
          (a (e.symm z) * projectiveField (β (e.symm z)) i)
      field_simp [ne_of_gt (hapos _ ht), ne_of_gt (hD _ ht)]

theorem exists_normalized_connectionLog_reparametrization {x : NormalizedState} {t₀ s : ℝ}
    {I : Set ℝ} (hI : Convex ℝ I) (ho : IsOpen I) (hs : s ∈ I)
    (hdom : I ⊆ normalizedMaxDomain x t₀) (hc : stateConstraint x = 1)
    (hA : ∀ t ∈ I, 0 < 1 + normalizedMaxCurve x t₀ t 0)
    (hw : ∀ t ∈ I, 0 < toProjectiveState (normalizedMaxCurve x t₀ t) 3)
    (hD : ∀ t ∈ I, 0 < connectionClockRate (toProjectiveState (normalizedMaxCurve x t₀ t))) :
    let β := fun t => toProjectiveState (normalizedMaxCurve x t₀ t)
    ∃ e : OpenPartialHomeomorph ℝ ℝ,
      e.source = I ∧
      (∀ t ∈ I, e t = Real.log (β t 3) - Real.log (β s 3)) ∧
      Convex ℝ e.target ∧ 0 ∈ e.target ∧ e.symm 0 = s ∧ StrictMonoOn e I ∧
      (∀ z ∈ e.target,
        HasDerivAt e.symm (1 / ((1 + normalizedMaxCurve x t₀ (e.symm z) 0) *
          connectionClockRate (β (e.symm z)))) z ∧
        β (e.symm z) 3 = β s 3 * Real.exp z ∧
        HasDerivAt (fun u => β (e.symm u)) (connectionLogField (β (e.symm z))) z) := by
  apply exists_scaled_connectionLog_reparametrization
    (a := fun t => 1 + normalizedMaxCurve x t₀ t 0) hI ho hs ?_ hA ?_ hw hD
  · intro t ht
    exact (continuousAt_const.add (hasDerivAt_pi.mp
      (hasDerivAt_normalizedMaxCurve (hdom ht)) 0).continuousAt).continuousWithinAt
  · intro t ht
    exact hasDerivAt_toProjectiveState_normalized (hasDerivAt_normalizedMaxCurve (hdom ht))
      (ne_of_gt (hA t ht)) ((normalizedMaxCurve_constraint (hdom ht)).trans hc)

end BianchiIX
