import BianchiIX.Dynamics.CompactCoreReturn

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem coreRadiusReturn_wall_zero {Y : CoreAngleState} (hvalid : coreRadiusReturnValid Y)
    (i : Fin 2) (hi : Y i.succ = 0) : (coreReturnState coreRadiusReturnTime Y) i.succ = 0 := by
  let x := fromProjectiveState (coreRadiusEntry Y)
  let T := coreRadiusReturnTime Y
  have hT : 0 < T := hvalid.1.1.1
  have hdom : T ∈ normalizedMaxDomain x 0 := hvalid.1.1.2.1
  have hA : 0 < 1 + normalizedMaxCurve x 0 T 0 := (hvalid.2.1 T ⟨hT.le, le_rfl⟩).2
  have hzero (j : Fin 3) (hj : wallValue j x = 0) :
      toProjectiveState (normalizedMaxCurve x 0 T) j.succ = 0 := by
    have H := normalized_wall_sign (convex_normalizedMaxDomain x 0) (isOpen_normalizedMaxDomain x 0)
      (fun _ ht => hasDerivAt_normalizedMaxCurve ht) (initial_mem_normalizedMaxDomain x 0) hdom j
    rw [normalizedMaxCurve_initial] at H
    exact (toProjectiveState_wall_sign hA j).1.mpr (H.1.mpr hj)
  fin_cases i
  · change Y 1 = 0 at hi
    exact hzero 0 (by simp [x, fromProjectiveState, coreRadiusEntry, wallValue, hi])
  · change Y 2 = 0 at hi
    have H := hzero 2 (by simp [x, fromProjectiveState, coreRadiusEntry, wallValue, hi])
    change toProjectiveState (normalizedMaxCurve x 0 T) 3 = 0 at H
    change toProjectiveState (normalizedMaxCurve x 0 T) 2 *
      toProjectiveState (normalizedMaxCurve x 0 T) 3 = 0
    rw [H, mul_zero]

theorem coreRadiusReturn_reference_value {k : ℝ} (hk : 1 < k) :
    coreReturnState coreRadiusReturnTime ![k, 0, 0] = ![k, 0, 0] := by
  have hT := (coreRadiusReturn_reference_regular hk).1
  have hx : fromProjectiveState (coreRadiusEntry ![k, 0, 0]) = referenceEntryState k := by
    unfold referenceEntryState
    rw [referencePulse_entry hk]
    rfl
  unfold coreReturnState projectiveOriginalFlow
  rw [hT, hx, (referenceEntryState_crossing hk).2, referenceExitState_projective]
  ext i
  fin_cases i
  · change Real.sqrt (coreEnergy (referencePulse k (referenceHalfTime k) 0)
      (referencePulse k (referenceHalfTime k) 2)) = k
    rw [referencePulse_energy, Real.sqrt_sq (by linarith only [hk])]
  · rfl
  · simp [toCoreAngleState, referencePulse]

/-- The transverse rows in radius coordinates retain the two exact reference multipliers. -/
theorem coreRadiusReturn_reference_wall_derivative {k : ℝ} (hk : 1 < k) (v : CoreAngleState) :
    (fderiv ℝ (coreReturnState coreRadiusReturnTime) ![k, 0, 0] v) 1 =
        Real.exp (-k * Real.arcosh k) * v 1 ∧
      (fderiv ℝ (coreReturnState coreRadiusReturnTime) ![k, 0, 0] v) 2 =
        Real.exp (-4 * Real.arcosh k / k) * v 2 := by
  let Y₀ : CoreAngleState := ![k, 0, 0]
  let e : CoreAngleState → CoreCoordinates := fun Y => coreSectionCoordinates (coreRadiusEntry Y)
  have hemb (Y : CoreAngleState) : coreSectionEmbedding (e Y) = coreRadiusEntry Y := by
    ext i
    fin_cases i <;> rfl
  have hchart (Y : CoreAngleState) : coreSectionChart (e Y) = fromProjectiveState (coreRadiusEntry Y) := by
    rw [coreSectionChart, hemb]
  have he₀ : e Y₀ = referenceCoreInput k := rfl
  have hce : ContDiffAt ℝ 1 e Y₀ :=
    (contDiff_coreSectionCoordinates 1).contDiffAt.comp Y₀ (contDiffAt_coreRadiusEntry 1 hk)
  have hde : fderiv ℝ e Y₀ v = ![k / Real.sqrt (k ^ 2 - 1) * v 0, v 1, v 2] := by
    have H := fderiv_comp Y₀ ((contDiff_coreSectionCoordinates 1).differentiable (by norm_num) _)
      ((contDiffAt_coreRadiusEntry 1 hk).differentiableAt (by norm_num))
    change fderiv ℝ e Y₀ = _ at H
    rw [H, ContinuousLinearMap.comp_apply, coreSectionCoordinates_fderiv, coreRadiusEntry_fderiv hk]
    rfl
  obtain ⟨τ, P, _, _, _, hcP, hnear, hdP⟩ := exists_referenceCore_firstReturn_two hk
  have hnear' := hce.continuousAt.eventually (he₀.symm ▸ hnear)
  have heq (i : Fin 2) : (fun Y => coreReturnState coreRadiusReturnTime Y i.succ) =ᶠ[𝓝 Y₀]
      (fun Y => P (e Y) i.succ) := by
    filter_upwards [hnear'] with Y hY
    have hT : coreRadiusReturnTime Y = τ (e Y) := by
      simpa only [coreRadiusReturnTime, hchart] using hY.1.csInf_eq
    dsimp only [coreReturnState, projectiveOriginalFlow]
    rw [hT, ← hchart, hY.2.2.2.2]
    fin_cases i
    · rfl
    · exact one_mul (P (e Y) 2)
  have hcF := (coreRadiusReturn_reference_regular hk).2.2.1
  have hdF := (hcF.differentiableAt (by norm_num)).hasFDerivAt
  have hdPe := ((he₀.symm ▸ hcP).differentiableAt (by norm_num)).hasFDerivAt.comp Y₀
    (hce.differentiableAt (by norm_num)).hasFDerivAt
  have H (i : Fin 2) :
      (fderiv ℝ (coreReturnState coreRadiusReturnTime) Y₀ v) i.succ =
        (fderiv ℝ P (referenceCoreInput k) (fderiv ℝ e Y₀ v)) i.succ := by
    have hleft := (hasFDerivAt_apply (𝕜 := ℝ) i.succ (coreReturnState coreRadiusReturnTime Y₀)).comp Y₀ hdF
    have hright := (hasFDerivAt_apply (𝕜 := ℝ) i.succ (P (e Y₀))).comp Y₀ hdPe
    exact congrArg (fun L => L v) ((hleft.congr_of_eventuallyEq (heq i).symm).unique hright)
  have H₀ := H 0
  have H₁ := H 1
  rw [hdP, hde] at H₀ H₁
  exact ⟨H₀, H₁⟩

end BianchiIX
