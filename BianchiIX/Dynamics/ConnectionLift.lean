import BianchiIX.Dynamics.ConnectionClock
import BianchiIX.Dynamics.ProjectiveClock

noncomputable section

namespace BianchiIX

open Set

theorem fromProjectiveState_fderiv_field {y : ProjectiveState} (hD : projectiveStateDenom y ≠ 0) :
    fderiv ℝ fromProjectiveState y (projectiveField y) =
      (projectiveStateDenom y / 6) • normalizedField (fromProjectiveState y) := by
  let β : ℝ → ProjectiveState := fun t => y + t • projectiveField y
  have hbase : β 0 = y := by simp [β]
  have hβ : HasDerivAt β (projectiveField y) 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add
      ((hasDerivAt_id (0 : ℝ)).smul_const (projectiveField y)) using 1
    simp
  have hd := ((contDiffAt_fromProjectiveState 1 hD).differentiableAt (by norm_num)).hasFDerivAt
  have H := (hbase.symm ▸ hd).comp_hasDerivAt 0 hβ
  have H' := hasDerivAt_fromProjectiveState
    (show HasDerivAt β (projectiveField (β 0)) 0 by simpa only [hbase] using hβ)
    (by simpa only [hbase] using hD)
  simpa only [hbase] using H.unique H'

theorem hasDerivAt_fromConnectionLog {Y : ℝ → ProjectiveState} {z : ℝ}
    (hY : HasDerivAt Y (connectionLogField (Y z)) z) (hD : projectiveStateDenom (Y z) ≠ 0) :
    HasDerivAt (fun t => fromProjectiveState (Y t))
      ((projectiveStateDenom (Y z) / (6 * connectionClockRate (Y z))) •
        normalizedField (fromProjectiveState (Y z))) z := by
  have hd := ((contDiffAt_fromProjectiveState 1 hD).differentiableAt (by norm_num)).hasFDerivAt
  have H := hd.comp_hasDerivAt z hY
  rw [connectionLogField, map_smul, fromProjectiveState_fderiv_field hD, smul_smul] at H
  convert! H using 1
  congr 1
  ring

/-- Every regular solution in the connection clock is part of the exact maximal Einstein flow. -/
theorem exists_connectionLog_normalized_reparametrization {Y : ℝ → ProjectiveState}
    {I : Set ℝ} {s : ℝ} (hI : Convex ℝ I) (ho : IsOpen I) (hs : s ∈ I)
    (hY : ∀ z ∈ I, HasDerivAt Y (connectionLogField (Y z)) z)
    (hD : ∀ z ∈ I, 0 < connectionClockRate (Y z))
    (hchart : ∀ z ∈ I, 0 < projectiveStateDenom (Y z)) :
    ∃ e : OpenPartialHomeomorph ℝ ℝ,
      e.source = I ∧
      (∀ z, e z = integralClock (fun u => projectiveStateDenom (Y u) / (6 * connectionClockRate (Y u))) s z) ∧
      Convex ℝ e.target ∧ 0 ∈ e.target ∧ e.symm 0 = s ∧ StrictMonoOn e I ∧
      e.target ⊆ normalizedMaxDomain (fromProjectiveState (Y s)) 0 ∧
      (∀ t ∈ e.target,
        fromProjectiveState (Y (e.symm t)) = normalizedMaxCurve (fromProjectiveState (Y s)) 0 t ∧
        toProjectiveState (normalizedMaxCurve (fromProjectiveState (Y s)) 0 t) = Y (e.symm t)) := by
  let q : ℝ → ℝ := fun z => projectiveStateDenom (Y z) / (6 * connectionClockRate (Y z))
  have hcontY := HasDerivAt.continuousOn hY
  have hq : ContinuousOn q I :=
    (continuous_projectiveStateDenom.comp_continuousOn hcontY).div
      (((contDiff_connectionClockRate 1).continuous.comp_continuousOn hcontY).const_mul 6)
      (fun z hz => mul_ne_zero (by norm_num) (ne_of_gt (hD z hz)))
  have hqpos : ∀ z ∈ I, 0 < q z := fun z hz => div_pos (hchart z hz) (mul_pos (by norm_num) (hD z hz))
  let e := positiveIntegralClock hI ho hq hs hqpos
  have he0 : e s = 0 := integralClock_initial q s
  have hzero : 0 ∈ e.target := he0 ▸ e.map_source hs
  have hinitial : e.symm 0 = s := positiveIntegralClock_symm_zero hI ho hq hs hqpos
  have hconvex : Convex ℝ e.target := convex_positiveIntegralClock_target hI ho hq hs hqpos
  have hsol (t : ℝ) (ht : t ∈ e.target) :
      HasDerivAt (fun u => fromProjectiveState (Y (e.symm u)))
        (normalizedField (fromProjectiveState (Y (e.symm t)))) t := by
    have hz : e.symm t ∈ I := e.map_target ht
    have hinv := hasDerivAt_positiveIntegralClock_symm hI ho hq hs hqpos ht
    have H := (hasDerivAt_fromConnectionLog (hY _ hz) (ne_of_gt (hchart _ hz))).scomp t hinv
    change HasDerivAt _ ((1 / q (e.symm t)) • (q (e.symm t) • _)) t at H
    simp only [smul_smul, one_div, inv_mul_cancel₀ (ne_of_gt (hqpos _ hz)), one_smul] at H
    convert! H using 1
  let S : NormalizedSolution (fromProjectiveState (Y s)) 0 :=
    { domain := e.target
      isOpen_domain := e.open_target
      convex_domain := hconvex
      initial_mem := hzero
      curve := fun t => fromProjectiveState (Y (e.symm t))
      initial_eq := by rw [hinitial]
      hasDerivAt := hsol }
  refine ⟨e, rfl, fun _ => rfl, hconvex, hzero, hinitial,
    strictMonoOn_integralClock hI ho hq hs hqpos, S.domain_subset_maximal, ?_⟩
  intro t ht
  have heq : fromProjectiveState (Y (e.symm t)) = normalizedMaxCurve (fromProjectiveState (Y s)) 0 t :=
    (normalizedMaxCurve_eqOn S ht).symm
  refine ⟨heq, ?_⟩
  rw [← heq]
  exact toProjectiveState_fromProjectiveState (ne_of_gt (hchart _ (e.map_target ht)))

end BianchiIX
