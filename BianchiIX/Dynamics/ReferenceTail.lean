import BianchiIX.Dynamics.ReferenceEvents

noncomputable section

namespace BianchiIX

open Set

def referenceHeightTime (k η : ℝ) : ℝ := Real.arcosh (k / η) / k

def referenceTailTime (k η : ℝ) : ℝ :=
  integralClock (fun t => projectiveStateDenom (referencePulse k t) / 6)
    (referenceHalfTime k) (referenceHeightTime k η)

theorem referenceHalfTime_lt_heightTime {k η : ℝ} (hk : 1 < k) (hη : 0 < η ∧ η < 1) :
    referenceHalfTime k < referenceHeightTime k η := by
  have hk0 : 0 < k := lt_trans zero_lt_one hk
  apply (div_lt_div_iff_of_pos_right hk0).mpr
  apply (Real.arcosh_lt_arcosh hk0 (div_pos hk0 hη.1)).mpr
  exact (lt_div_iff₀ hη.1).mpr (by nlinarith only [hk0, hη.2])

theorem referencePulse_height_exit {k η : ℝ} (hk : 0 < k) (hη : 0 < η ∧ η < k) :
    referencePulse k (referenceHeightTime k η) =
      ![1 - Real.sqrt (k ^ 2 - η ^ 2), 0, η, 0] := by
  let s := referenceHeightTime k η
  have hr : 1 < k / η := (one_lt_div hη.1).mpr hη.2
  have hks : k * s = Real.arcosh (k / η) := by
    dsimp [s, referenceHeightTime]
    field_simp
  have hv : referencePulse k s 2 = η := by
    change k / Real.cosh (k * s) = η
    rw [hks, Real.cosh_arcosh hr.le]
    field_simp
  have htanh : 0 < Real.tanh (k * s) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (by rw [hks]; exact Real.arcosh_pos hr)) (Real.cosh_pos _)
  have hm : referencePulse k s 0 < 1 := by
    change 1 - k * Real.tanh (k * s) < 1
    linarith only [mul_pos hk htanh]
  have he := referencePulse_energy k s
  rw [hv] at he
  have hsqrt : Real.sqrt (k ^ 2 - η ^ 2) = 1 - referencePulse k s 0 :=
    (Real.sqrt_eq_iff_eq_sq (by nlinarith only [hη.1, hη.2]) (by linarith only [hm])).mpr (by
      dsimp [coreEnergy] at he
      nlinarith only [he])
  ext i
  fin_cases i
  · change referencePulse k s 0 = 1 - Real.sqrt (k ^ 2 - η ^ 2)
    linarith only [hsqrt]
  · rfl
  · exact hv
  · rfl

theorem referencePulse_active_rate_neg {k t : ℝ} (hk : 0 < k) (ht : 0 < t) :
    projectiveField (referencePulse k t) 2 < 0 := by
  have htan : 0 < Real.tanh (k * t) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (mul_pos hk ht)) (Real.cosh_pos _)
  have hv := referencePulse_active_pos hk t
  change 0 < k / Real.cosh (k * t) at hv
  dsimp [projectiveField, referencePulse, activeVelocity, coupling]
  nlinarith only [mul_pos (mul_pos hk htan) hv]

/-- The finite downward tail is a segment of the original maximal Einstein flow. -/
theorem referenceTail_normalized_segment {k η : ℝ} (hk : 1 < k) (hη : 0 < η ∧ η < 1) :
    0 < referenceTailTime k η ∧
      normalizedMaxCurve (referenceExitState k) 0 (referenceTailTime k η) =
        fromProjectiveState ![1 - Real.sqrt (k ^ 2 - η ^ 2), 0, η, 0] ∧
      ∀ t ∈ Icc 0 (referenceTailTime k η),
        t ∈ normalizedMaxDomain (referenceExitState k) 0 ∧
        0 < 1 + normalizedMaxCurve (referenceExitState k) 0 t 0 ∧
        normalizedEventRate projectiveActiveWall (referenceExitState k) 0 t < 0 ∧
        toProjectiveState (normalizedMaxCurve (referenceExitState k) 0 t) 3 = 0 := by
  obtain ⟨e, hsrc, he, _, hconv, hzero, _, hmono, hdom, hflow⟩ :=
    exists_projective_normalized_reparametrization (β := referencePulse k)
      (s := referenceHalfTime k) convex_univ isOpen_univ (mem_univ _)
      (fun t _ => hasDerivAt_referencePulse k t) (fun t _ => referencePulse_denom_pos k t)
  have hin : e (referenceHalfTime k) = 0 := by rw [he]; exact integralClock_initial _ _
  have hout : e (referenceHeightTime k η) = referenceTailTime k η := he _
  have hT : 0 < referenceTailTime k η := by
    have H := hmono (mem_univ _) (mem_univ _) (referenceHalfTime_lt_heightTime hk hη)
    simpa only [hin, hout] using H
  have hsrcout : referenceHeightTime k η ∈ e.source := by rw [hsrc]; trivial
  have htarg : referenceTailTime k η ∈ e.target := hout ▸ e.map_source hsrcout
  have hinter : Icc 0 (referenceTailTime k η) ⊆ e.target :=
    (Icc_subset_uIcc ..).trans (hconv.ordConnected.uIcc_subset hzero htarg)
  have heout : e.symm (referenceTailTime k η) = referenceHeightTime k η := by
    rw [← hout, e.left_inv hsrcout]
  refine ⟨hT, ?_, ?_⟩
  · have H := (hflow _ htarg).1
    rw [heout, referencePulse_height_exit (lt_trans zero_lt_one hk) ⟨hη.1, hη.2.trans hk⟩] at H
    exact H.symm
  · intro t ht
    have htg := hinter ht
    have hs : referenceHalfTime k ≤ e.symm t := by
      by_contra! hn
      have H := hmono (mem_univ _) (mem_univ _) hn
      rw [e.right_inv htg, hin] at H
      linarith only [ht.1, H]
    have Hflow := hflow t htg
    change fromProjectiveState (referencePulse k (e.symm t)) =
      normalizedMaxCurve (referenceExitState k) 0 t ∧
      toProjectiveState (normalizedMaxCurve (referenceExitState k) 0 t) = referencePulse k (e.symm t) at Hflow
    have hA : 0 < 1 + normalizedMaxCurve (referenceExitState k) 0 t 0 := by
      rw [← Hflow.1]
      exact fromProjectiveState_clock_pos (referencePulse_denom_pos k _)
    have hc : stateConstraint (normalizedMaxCurve (referenceExitState k) 0 t) = 1 := by
      rw [← Hflow.1]
      exact fromProjectiveState_constraint (ne_of_gt (referencePulse_denom_pos k _))
    refine ⟨hdom htg, hA, ?_, ?_⟩
    · rw [normalizedEventRate, projectiveActiveWall_fderiv_field (ne_of_gt hA) hc, Hflow.2]
      exact mul_neg_of_pos_of_neg hA (referencePulse_active_rate_neg (lt_trans zero_lt_one hk)
        ((referenceHalfTime_pos hk).trans_le hs))
    · rw [Hflow.2]
      rfl

theorem referenceTail_active_hit {k η : ℝ} (hk : 1 < k) (hη : 0 < η ∧ η < 1) :
    projectiveActiveWall (normalizedMaxCurve (referenceExitState k) 0 (referenceTailTime k η)) = η := by
  have H := referenceTail_normalized_segment hk hη
  have hD : 0 < projectiveStateDenom (![1 - Real.sqrt (k ^ 2 - η ^ 2), 0, η, 0] : ProjectiveState) := by
    rw [← referencePulse_height_exit (lt_trans zero_lt_one hk) ⟨hη.1, hη.2.trans hk⟩]
    exact referencePulse_denom_pos k _
  rw [H.2.1]
  unfold projectiveActiveWall
  rw [toProjectiveState_fromProjectiveState (ne_of_gt hD)]
  rfl

end BianchiIX
