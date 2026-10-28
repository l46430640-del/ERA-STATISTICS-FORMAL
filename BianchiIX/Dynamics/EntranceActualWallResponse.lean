import BianchiIX.Dynamics.EntranceWallVariation

noncomputable section

namespace BianchiIX

open Set MeasureTheory

def entranceLogWalls (k : ℝ) (y : ProjectiveState) : Fin 2 → ℝ :=
  ![Real.log (y 1), k ^ 2 * Real.log (y 3)]

theorem hasFDerivAt_entranceLogWalls {y : ProjectiveState} (k : ℝ)
    (hu : y 1 ≠ 0) (hw : y 3 ≠ 0) :
    HasFDerivAt (entranceLogWalls k)
      (ContinuousLinearMap.pi (![(y 1)⁻¹ • ContinuousLinearMap.proj 1,
        k ^ 2 • ((y 3)⁻¹ • ContinuousLinearMap.proj 3)] : Fin 2 → (ProjectiveState →L[ℝ] ℝ))) y := by
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 4) y).log hu
  · exact ((hasFDerivAt_apply (𝕜 := ℝ) (3 : Fin 4) y).log hw).const_mul (k ^ 2)

theorem entranceLogWalls_fderiv_apply {y : ProjectiveState} (k : ℝ)
    (hu : y 1 ≠ 0) (hw : y 3 ≠ 0) (v : ProjectiveState) :
    fderiv ℝ (entranceLogWalls k) y v = entranceWallTangent k y v := by
  rw [(hasFDerivAt_entranceLogWalls k hu hw).fderiv]
  ext i
  fin_cases i <;> simp [entranceWallTangent, div_eq_mul_inv, mul_comm]

/-- The actual branch constructed at fixed relative clock has this logarithmic amplitude derivative. -/
theorem entranceClock_branch_logWalls {y : ProjectiveState} {t₀ t k : ℝ} {τ : ProjectiveState → ℝ}
    (hτ : τ y = t)
    (hmap : HasFDerivAt (fun z => projectiveOriginalFlow z t₀ (τ z)) (entranceClockFlowDifferential y t₀ t) y)
    (hy : y 2 ≠ 0) (hv : projectiveOriginalFlow y t₀ t 2 ≠ 0)
    (hu : projectiveOriginalFlow y t₀ t 1 ≠ 0) (hw : projectiveOriginalFlow y t₀ t 3 ≠ 0)
    (w : ProjectiveState) :
    fderiv ℝ (fun z => entranceLogWalls k (projectiveOriginalFlow z t₀ (τ z))) y w =
      entranceWallTangent k (projectiveOriginalFlow y t₀ t) (entranceProjectedFlowVariation y t₀ t w) := by
  have hd : HasFDerivAt (entranceLogWalls k)
      (fderiv ℝ (entranceLogWalls k) (projectiveOriginalFlow y t₀ t)) (projectiveOriginalFlow y t₀ (τ y)) := by
    rw [hτ]
    exact (hasFDerivAt_entranceLogWalls k hu hw).differentiableAt.hasFDerivAt
  have H := congrArg (fun L : ProjectiveState →L[ℝ] (Fin 2 → ℝ) => L w) (hd.comp y hmap).fderiv
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    entranceClockFlowDifferential_apply hy hv, entranceLogWalls_fderiv_apply k hu hw] using H

/-- (C.30) for the true fixed-clock parameter derivatives on an actual entrance segment. -/
theorem exists_actual_entrance_wall_response :
    ∃ C > (0 : ℝ), ∀ (y : ProjectiveState) (t₀ s t k : ℝ),
      0 < projectiveStateDenom y → 7 / 4 ≤ k → s ≤ t →
      (∀ r ∈ Icc s t, r ∈ normalizedMaxDomain (fromProjectiveState y) t₀) →
      (∀ r ∈ Icc s t, 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ r 0) →
      let Y := projectiveOriginalFlow y t₀
      (∀ r ∈ Icc s t, entranceRegion k (Y r)) → (∀ r ∈ Icc s t, 0 < Y r 2) →
      (∀ r ∈ Icc s t, Y r 1 ≠ 0 ∧ Y r 3 ≠ 0) →
      ∀ (w : ProjectiveState), w 2 = 0 →
      let v := fun r => entranceProjectedFlowVariation y t₀ r w
      let f := fun r => entranceWallTangent k (Y r) (v r)
      let Z := fun r => fderiv ℝ entranceStableRadius (Y r) (v r)
      ∀ b c : ℝ, s ≤ b → b ≤ c → c ≤ t →
      |f c 0 - f b 0| + |f c 1 - f b 1| ≤ C * (Y s 1 * |f b 0| + Y s 3 / k ^ 2 * |f b 1| +
        ∫ r in b..c, |Z r| * entranceOriginalClockRate (Y r)) := by
  obtain ⟨C, hC, HC⟩ := exists_scaled_entrance_wall_radial_response
  refine ⟨C, hC, ?_⟩
  intro y t₀ s t k hD hk hst hdom hA Y hreg hv hwall w hw0 v f Z b c hsb hbc hct
  let a := fun r => 6 / projectiveStateDenom (Y r)
  have hden (r : ℝ) (hr : r ∈ Icc s t) : 0 < projectiveStateDenom (Y r) := by
    have hc : stateConstraint (normalizedMaxCurve (fromProjectiveState y) t₀ r) = 1 :=
      (normalizedMaxCurve_constraint (hdom r hr)).trans (fromProjectiveState_constraint hD.ne')
    exact toProjectiveState_denom_pos (hA r hr) hc
  have hY (r : ℝ) (hr : r ∈ Icc s t) : HasDerivAt Y (a r • projectiveField (Y r)) r :=
    hasDerivAt_projectiveOriginalFlow_time hD (hdom r hr) (hA r hr)
  have hac : ContinuousOn a (Icc s t) := by
    intro r hr
    exact (continuousAt_const.div ((contDiff_projectiveStateDenom 1).continuous.continuousAt.comp
      (hY r hr).continuousAt) (hden r hr).ne').continuousWithinAt
  have ha (r : ℝ) (hr : r ∈ Icc s t) : 0 ≤ a r := (div_pos (by norm_num) (hden r hr)).le
  have hsub : Icc b c ⊆ Icc s t := fun r hr => ⟨hsb.trans hr.1, hr.2.trans hct⟩
  have hZ : ContinuousOn Z (Icc b c) := by
    intro r hr
    have hy := hreg r (hsub hr)
    have hm : 2 ≤ Y r 0 := by linarith [(entranceRegion_phase hk hy).1]
    have hu : |Y r 1| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.1.1]; linarith [hy.2.2.1.2]
    have hw : |Y r 3| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.2.2.1]; linarith [hy.2.2.2.2.2]
    have hR := (contDiffAt_entranceStableRadius_two hm hu hw (hv r (hsub hr))).continuousAt_fderiv (by norm_num)
    have hvc := (hasDerivAt_entranceProjectedFlowVariation hD (hdom r (hsub hr)) (hA r (hsub hr))
      (hv r (hsub hr)).ne' (entranceRegion_clock_pos hk hy).ne' w).continuousAt
    exact ((hR.comp (hY r (hsub hr)).continuousAt).clm_apply hvc).continuousWithinAt
  have hf (r : ℝ) (hr : r ∈ Icc b c) : HasDerivAt f
      (((a r * entranceClockRate (Y r)) • entranceWallWeightedMatrix k (Y r)).mulVec (f r) +
        ((a r * entranceClockRate (Y r)) * Z r) • entranceWallRadialSource k (Y r)) r :=
    hasDerivAt_entranceProjectedWallTangent hD (hdom r (hsub hr)) (hA r (hsub hr)) hk
      (hreg r (hsub hr)) (hv r (hsub hr)) (hwall r (hsub hr)).1 (hwall r (hsub hr)).2 w hw0
  exact HC Y a s t k hk hst hY hac ha hreg hv b c hsb hbc hct f Z hZ hf

end BianchiIX
