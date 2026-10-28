import BianchiIX.Dynamics.EntranceClockBranch
import BianchiIX.Dynamics.EntranceWallRadialResponse

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

def entranceWallTangent (k : ℝ) (y v : ProjectiveState) : Fin 2 → ℝ :=
  ![v 1 / y 1, k ^ 2 * (v 3 / y 3)]

theorem entranceLogField_wall_rates {y : ProjectiveState} (hD : entranceClockRate y ≠ 0) :
    entranceLogField y 1 = entranceStrongLogRate y * y 1 ∧
      entranceLogField y 3 = entranceWeakLogRate y * y 3 := by
  obtain ⟨hs, hw⟩ := entranceWallLogRates_field hD
  constructor
  · change (entranceClockRate y)⁻¹ * projectiveField y 1 = _
    rw [hs]
    field_simp
  · change (entranceClockRate y)⁻¹ * projectiveField y 3 = _
    rw [hw]
    field_simp

theorem entranceLogField_wall_fderiv {y : ProjectiveState}
    (hD : entranceClockRate y ≠ 0) (v : ProjectiveState) :
    fderiv ℝ entranceLogField y v 1 =
        fderiv ℝ entranceStrongLogRate y v * y 1 + entranceStrongLogRate y * v 1 ∧
      fderiv ℝ entranceLogField y v 3 =
        fderiv ℝ entranceWeakLogRate y v * y 3 + entranceWeakLogRate y * v 3 := by
  have hF := ((contDiffAt_entranceLogField 1 hD).differentiableAt (by norm_num)).hasFDerivAt
  have hnear := continuous_entranceClockRate.continuousAt.eventually_ne hD
  have H (i : Fin 4) (b : ProjectiveState → ℝ) (hb : DifferentiableAt ℝ b y)
      (he : (fun z => entranceLogField z i) =ᶠ[𝓝 y] (fun z => b z * z i)) :
      fderiv ℝ entranceLogField y v i = fderiv ℝ b y v * y i + b y * v i := by
    have hf := (hasFDerivAt_apply (𝕜 := ℝ) i (entranceLogField y)).comp y hF
    have hg := (hb.hasFDerivAt.mul (hasFDerivAt_apply (𝕜 := ℝ) i y)).congr_of_eventuallyEq he
    have hd := congrArg (fun L : ProjectiveState →L[ℝ] ℝ => L v) (hf.unique hg)
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      add_apply, smul_apply, smul_eq_mul, mul_comm, add_comm] using hd
  obtain ⟨hs, hw⟩ := contDiffAt_entranceWallLogRates 1 hD
  constructor
  · apply H 1 entranceStrongLogRate (hs.differentiableAt (by norm_num))
    filter_upwards [hnear] with z hz
    exact (entranceLogField_wall_rates hz).1
  · apply H 3 entranceWeakLogRate (hw.differentiableAt (by norm_num))
    filter_upwards [hnear] with z hz
    exact (entranceLogField_wall_rates hz).2

private theorem hasDerivAt_relative_variation {u v : ℝ → ℝ} {a b c t : ℝ}
    (hu : HasDerivAt u (a * b * u t) t)
    (hv : HasDerivAt v (a * (c * u t + b * v t)) t) (hne : u t ≠ 0) :
    HasDerivAt (fun s => v s / u s) (a * c) t := by
  apply (hv.div hu hne).congr_deriv
  field_simp
  ring

/-- The logarithmic tangent differentiates the actual amplitudes; the weight k is held fixed. -/
theorem hasDerivAt_entranceWallTangent {Y v : ℝ → ProjectiveState} {a t k : ℝ}
    (hY : HasDerivAt Y (a • entranceLogField (Y t)) t)
    (hv : HasDerivAt v (a • fderiv ℝ entranceLogField (Y t) (v t)) t)
    (hu : Y t 1 ≠ 0) (hw : Y t 3 ≠ 0) (hD : entranceClockRate (Y t) ≠ 0) :
    HasDerivAt (fun s => entranceWallTangent k (Y s) (v s))
      (a • ![fderiv ℝ entranceStrongLogRate (Y t) (v t),
        k ^ 2 * fderiv ℝ entranceWeakLogRate (Y t) (v t)]) t := by
  obtain ⟨hs, hw'⟩ := entranceLogField_wall_rates hD
  obtain ⟨hds, hdw⟩ := entranceLogField_wall_fderiv hD (v t)
  have hY1 := hasDerivAt_pi.mp hY 1
  have hY3 := hasDerivAt_pi.mp hY 3
  have hv1 := hasDerivAt_pi.mp hv 1
  have hv3 := hasDerivAt_pi.mp hv 3
  simp only [Pi.smul_apply, smul_eq_mul, hs] at hY1
  simp only [Pi.smul_apply, smul_eq_mul, hw'] at hY3
  simp only [Pi.smul_apply, smul_eq_mul, hds] at hv1
  simp only [Pi.smul_apply, smul_eq_mul, hdw] at hv3
  have H1 := hasDerivAt_relative_variation (u := fun s => Y s 1) (v := fun s => v s 1)
    (a := a) (b := entranceStrongLogRate (Y t))
    (by simpa only [mul_assoc] using hY1) hv1 hu
  have H3 := (hasDerivAt_relative_variation (u := fun s => Y s 3) (v := fun s => v s 3)
    (a := a) (b := entranceWeakLogRate (Y t))
    (by simpa only [mul_assoc] using hY3) hv3 hw).const_mul (k ^ 2)
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact H1
  · convert! H3 using 1
    change a * (k ^ 2 * _) = k ^ 2 * (a * _)
    ring

theorem entranceWallTangent_radial_decomposition {y v : ProjectiveState} {k : ℝ}
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (hv : 0 < y 2)
    (hu : y 1 ≠ 0) (hw : y 3 ≠ 0) (hactive : v 2 = 0) :
    ![fderiv ℝ entranceStrongLogRate y v, k ^ 2 * fderiv ℝ entranceWeakLogRate y v] =
      (entranceWallWeightedMatrix k y).mulVec (entranceWallTangent k y v) +
        (fderiv ℝ entranceStableRadius y v) • entranceWallRadialSource k y := by
  have hm : 2 ≤ y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hu' : |y 1| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.1.1]; linarith [hy.2.2.1.2]
  have hw' : |y 3| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.2.2.1]; linarith [hy.2.2.2.2.2]
  obtain ⟨hchi, _, hPM⟩ := entranceRegion_stable_radial_bounds hk hy
  have hinv := (entranceRadialDifferential_inverse hm hu' hw' hv
    (by linarith [hchi.1]) (by linarith [hPM.1])).1 v
  rw [entranceRadialDifferential_apply, hactive] at hinv
  let Z := fderiv ℝ entranceStableRadius y v
  have he : (![Z, v 1, 0, v 3] : ProjectiveState) =
      Z • Pi.single 0 1 + v 1 • Pi.single 1 1 + v 3 • Pi.single 3 1 := by
    ext i
    fin_cases i <;> simp
  have hs : fderiv ℝ entranceStrongLogRate y v =
      entranceStrongLogDifferential y ![Z, v 1, 0, v 3] := by
    change _ = fderiv ℝ entranceStrongLogRate y (entranceRadialInverseDifferential y _)
    rw [hinv]
  have hw'' : fderiv ℝ entranceWeakLogRate y v =
      entranceWeakLogDifferential y ![Z, v 1, 0, v 3] := by
    change _ = fderiv ℝ entranceWeakLogRate y (entranceRadialInverseDifferential y _)
    rw [hinv]
  rw [hs, hw'', he]
  simp only [map_add, map_smul, smul_eq_mul]
  have hk0 : k ≠ 0 := by linarith
  ext i
  fin_cases i <;>
    simp [entranceWallWeightedMatrix, entranceWallTangent, entranceWallRadialSource, Z] <;>
      field_simp <;> ring

theorem hasDerivAt_entranceProjectedWallTangent {y : ProjectiveState} {t₀ t k : ℝ}
    (hD : 0 < projectiveStateDenom y) (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hk : 7 / 4 ≤ k) (hreg : entranceRegion k (projectiveOriginalFlow y t₀ t))
    (hv : 0 < projectiveOriginalFlow y t₀ t 2)
    (hu : projectiveOriginalFlow y t₀ t 1 ≠ 0) (hw : projectiveOriginalFlow y t₀ t 3 ≠ 0)
    (w : ProjectiveState) (hw0 : w 2 = 0) :
    let Y := projectiveOriginalFlow y t₀
    let v := fun s => entranceProjectedFlowVariation y t₀ s w
    let f := fun s => entranceWallTangent k (Y s) (v s)
    let q := entranceOriginalClockRate (Y t)
    HasDerivAt f (((q • entranceWallWeightedMatrix k (Y t)).mulVec (f t)) +
      (q * fderiv ℝ entranceStableRadius (Y t) (v t)) • entranceWallRadialSource k (Y t)) t := by
  dsimp only
  have hclock := (entranceRegion_clock_pos hk hreg).ne'
  have hY := hasDerivAt_projectiveOriginalFlow_time hD ht hA
  rw [projectiveOriginalField_entranceLog hclock] at hY
  have H := hasDerivAt_entranceWallTangent (k := k) hY
    (hasDerivAt_entranceProjectedFlowVariation hD ht hA hv.ne' hclock w) hu hw hclock
  have hactive : entranceProjectedFlowVariation y t₀ t w 2 = 0 := by
    rw [entranceProjectedFlowVariation_active hv.ne' hclock w, hw0, zero_div, zero_mul]
  rw [entranceWallTangent_radial_decomposition hk hreg hv hu hw hactive] at H
  simpa only [smul_add, smul_smul, Matrix.smul_mulVec] using H

end BianchiIX
