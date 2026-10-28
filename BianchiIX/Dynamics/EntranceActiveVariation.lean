import BianchiIX.Dynamics.EntrancePhaseActiveSource
import BianchiIX.Dynamics.EntranceActiveLogRates
import BianchiIX.Dynamics.EntranceWallVariation

noncomputable section

namespace BianchiIX

theorem entrance_radial_linearForm_decomposition {y v : ProjectiveState} {k : ℝ}
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (hv : 0 < y 2)
    (L : ProjectiveState →L[ℝ] ℝ) :
    let B := L.comp (entranceRadialInverseDifferential y)
    L v = B (Pi.single 0 1) * fderiv ℝ entranceStableRadius y v +
      B (Pi.single 1 1) * v 1 + B (Pi.single 2 1) * v 2 + B (Pi.single 3 1) * v 3 := by
  have hm : 2 ≤ y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hu : |y 1| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.1.1]; linarith [hy.2.2.1.2]
  have hw : |y 3| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.2.2.1]; linarith [hy.2.2.2.2.2]
  obtain ⟨hchi, _, hPM⟩ := entranceRegion_stable_radial_bounds hk hy
  have hinv := (entranceRadialDifferential_inverse hm hu hw hv
    (by linarith [hchi.1]) (by linarith [hPM.1])).1 v
  have he : entranceRadialDifferential y v =
      (fderiv ℝ entranceStableRadius y v) • Pi.single 0 1 + v 1 • Pi.single 1 1 +
        v 2 • Pi.single 2 1 + v 3 • Pi.single 3 1 := by
    rw [entranceRadialDifferential_apply]
    ext i
    fin_cases i <;> simp
  dsimp only
  conv_lhs => rw [← hinv, he]
  simp only [map_add, map_smul, smul_eq_mul, ContinuousLinearMap.comp_apply]
  ring

theorem entranceRadialDrift_forced_decomposition {y v : ProjectiveState} {k : ℝ}
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (hv : 0 < y 2)
    (hu : y 1 ≠ 0) (hw : y 3 ≠ 0) :
    fderiv ℝ entranceRadialDrift y v =
      entranceRadialVariationCoefficients y 0 * fderiv ℝ entranceStableRadius y v +
      entranceRadialVariationCoefficients y 1 * (v 1 / y 1) +
      entranceRadialVariationCoefficients y 2 * (v 3 / y 3) +
      (v 2 / y 2) * entrancePhaseActiveSource y := by
  rw [entrance_radial_linearForm_decomposition hk hy hv (fderiv ℝ entranceRadialDrift y)]
  dsimp [entranceRadialVariationCoefficients, entrancePhaseActiveSource, entranceRadialDriftDifferential]
  field_simp
  ring

theorem entranceWallTangent_forced_decomposition {y v : ProjectiveState} {k : ℝ}
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (hv : 0 < y 2)
    (hu : y 1 ≠ 0) (hw : y 3 ≠ 0) :
    ![fderiv ℝ entranceStrongLogRate y v, k ^ 2 * fderiv ℝ entranceWeakLogRate y v] =
      (entranceWallWeightedMatrix k y).mulVec (entranceWallTangent k y v) +
      (fderiv ℝ entranceStableRadius y v) • entranceWallRadialSource k y +
      (v 2 / y 2) • entranceWallActiveSource k y := by
  rw [entrance_radial_linearForm_decomposition hk hy hv (fderiv ℝ entranceStrongLogRate y),
    entrance_radial_linearForm_decomposition hk hy hv (fderiv ℝ entranceWeakLogRate y)]
  have hk0 : k ≠ 0 := by linarith
  ext i
  fin_cases i <;>
    simp [Matrix.vecHead, Matrix.vecTail, Function.comp_def,
      entranceWallWeightedMatrix, entranceWallTangent, entranceWallRadialSource,
      entranceWallActiveSource, entranceStrongLogDifferential, entranceWeakLogDifferential] <;>
      field_simp <;> ring

/-- The actual projected Einstein variation obeys both forced equations with its initial activity. -/
theorem hasDerivAt_entranceProjectedForcedTangents {y : ProjectiveState} {t₀ t k : ℝ}
    (hD : 0 < projectiveStateDenom y) (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hk : 7 / 4 ≤ k) (hreg : entranceRegion k (projectiveOriginalFlow y t₀ t))
    (hv : 0 < projectiveOriginalFlow y t₀ t 2)
    (hu : projectiveOriginalFlow y t₀ t 1 ≠ 0) (hw : projectiveOriginalFlow y t₀ t 3 ≠ 0)
    (w : ProjectiveState) :
    let Y := projectiveOriginalFlow y t₀
    let v := fun s => entranceProjectedFlowVariation y t₀ s w
    let Z := fun s => fderiv ℝ entranceStableRadius (Y s) (v s)
    let f := fun s => entranceWallTangent k (Y s) (v s)
    let c := entranceRadialVariationCoefficients (Y t)
    let q := entranceOriginalClockRate (Y t)
    let ζ := w 2 / y 2
    HasDerivAt Z (q * (c 0 * Z t + c 1 * (v t 1 / Y t 1) + c 2 * (v t 3 / Y t 3) +
      ζ * entrancePhaseActiveSource (Y t))) t ∧
    HasDerivAt f (q • ((entranceWallWeightedMatrix k (Y t)).mulVec (f t) +
      Z t • entranceWallRadialSource k (Y t) + ζ • entranceWallActiveSource k (Y t))) t := by
  dsimp only
  have hclock := (entranceRegion_clock_pos hk hreg).ne'
  have hY := hasDerivAt_projectiveOriginalFlow_time hD ht hA
  rw [projectiveOriginalField_entranceLog hclock] at hY
  have hvar := hasDerivAt_entranceProjectedFlowVariation hD ht hA hv.ne' hclock w
  have hz := hasDerivAt_entranceRadialTangent hY hvar hk hreg hv
  have hf := hasDerivAt_entranceWallTangent (k := k) hY hvar hu hw hclock
  have hactive : entranceProjectedFlowVariation y t₀ t w 2 / projectiveOriginalFlow y t₀ t 2 = w 2 / y 2 := by
    rw [entranceProjectedFlowVariation_active hv.ne' hclock w]
    exact mul_div_cancel_right₀ _ hv.ne'
  rw [entranceRadialDrift_forced_decomposition hk hreg hv hu hw, hactive] at hz
  rw [entranceWallTangent_forced_decomposition hk hreg hv hu hw, hactive] at hf
  exact ⟨hz, hf⟩

def entranceActiveInitialVector (y : ProjectiveState) : ProjectiveState :=
  entranceRadialInverseDifferential y (y 2 • Pi.single 2 1)

theorem entranceActiveInitialVector_coordinates {y : ProjectiveState} {k : ℝ}
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (hv : 0 < y 2) :
    fderiv ℝ entranceStableRadius y (entranceActiveInitialVector y) = 0 ∧
      entranceActiveInitialVector y 1 = 0 ∧ entranceActiveInitialVector y 2 = y 2 ∧
      entranceActiveInitialVector y 3 = 0 := by
  have hm : 2 ≤ y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hu : |y 1| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.1.1]; linarith [hy.2.2.1.2]
  have hw : |y 3| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.2.2.1]; linarith [hy.2.2.2.2.2]
  obtain ⟨hchi, _, hPM⟩ := entranceRegion_stable_radial_bounds hk hy
  have H := (entranceRadialDifferential_inverse hm hu hw hv
    (by linarith [hchi.1]) (by linarith [hPM.1])).2 (y 2 • Pi.single 2 1)
  rw [entranceRadialDifferential_apply] at H
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [entranceActiveInitialVector] using congrArg (fun z : ProjectiveState => z 0) H
  · simpa [entranceActiveInitialVector] using congrArg (fun z : ProjectiveState => z 1) H
  · simpa [entranceActiveInitialVector] using congrArg (fun z : ProjectiveState => z 2) H
  · simpa [entranceActiveInitialVector] using congrArg (fun z : ProjectiveState => z 3) H

theorem entranceActiveVariation_initial {y : ProjectiveState} {k : ℝ}
    (hD : 0 < projectiveStateDenom y) (hk : 7 / 4 ≤ k) (hy : entranceRegion k y)
    (hv : 0 < y 2) (t₀ : ℝ) :
    let Y := projectiveOriginalFlow y t₀ t₀
    let w := entranceActiveInitialVector y
    let v := entranceProjectedFlowVariation y t₀ t₀ w
    fderiv ℝ entranceStableRadius Y v = 0 ∧ entranceWallTangent k Y v = 0 ∧ w 2 / y 2 = 1 := by
  dsimp only
  rw [projectiveOriginalFlow_initial hD, entranceProjectedFlowVariation_initial hD]
  obtain ⟨h0, h1, h2, h3⟩ := entranceActiveInitialVector_coordinates hk hy hv
  refine ⟨h0, ?_, ?_⟩
  · ext i
    fin_cases i <;> simp [entranceWallTangent, h1, h3]
  · rw [h2, div_self hv.ne']

end BianchiIX
