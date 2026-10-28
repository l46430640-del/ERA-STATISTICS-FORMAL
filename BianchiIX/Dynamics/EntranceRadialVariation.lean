import BianchiIX.Analysis.ScaledObservableVariation
import BianchiIX.Dynamics.EntranceFlowVariation
import BianchiIX.Dynamics.EntranceDriftDifferential

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

def entranceRadialDriftDifferential (y : ProjectiveState) : ProjectiveState →L[ℝ] ℝ :=
  (fderiv ℝ entranceRadialDrift y).comp (entranceRadialInverseDifferential y)

def entranceRadialVariationCoefficients (y : ProjectiveState) : Fin 3 → ℝ :=
  ![entranceRadialDriftDifferential y (Pi.single 0 1),
    y 1 * entranceRadialDriftDifferential y (Pi.single 1 1),
    y 3 * entranceRadialDriftDifferential y (Pi.single 3 1)]

theorem entranceRadialDrift_lie_eventuallyEq {y : ProjectiveState} {k : ℝ}
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (hv : 0 < y 2) :
    (fun z => fderiv ℝ entranceStableRadius z (entranceLogField z)) =ᶠ[𝓝 y] entranceRadialDrift := by
  have hm : 2 < y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hu : |y 1| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.1.1]; linarith [hy.2.2.1.2]
  have hw : |y 3| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.2.2.1]; linarith [hy.2.2.2.2.2]
  filter_upwards [(continuous_apply 0).continuousAt.eventually (isOpen_Ioi.mem_nhds hm),
    (continuous_apply 1).abs.continuousAt.eventually (isOpen_Iio.mem_nhds hu),
    (continuous_apply 3).abs.continuousAt.eventually (isOpen_Iio.mem_nhds hw),
    (continuous_apply 2).continuousAt.eventually (isOpen_Ioi.mem_nhds hv)] with z hmz huz hwz hvz
  rw [entranceRadialDrift_eq_log_rate hmz.le huz hwz hvz, entranceLogField, map_smul]
  simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem contDiffAt_entranceRadialDrift_one {y : ProjectiveState} {k : ℝ}
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (hv : 0 < y 2) :
    ContDiffAt ℝ 1 entranceRadialDrift y := by
  have hm : 2 ≤ y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hu : |y 1| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.1.1]; linarith [hy.2.2.1.2]
  have hw : |y 3| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.2.2.1]; linarith [hy.2.2.2.2.2]
  have hR := (contDiffAt_entranceStableRadius_two hm hu hw hv).fderiv_right (m := 1) (by norm_num)
  exact (hR.clm_apply (contDiffAt_entranceLogField 1 (entranceRegion_clock_pos hk hy).ne')).congr_of_eventuallyEq
    (entranceRadialDrift_lie_eventuallyEq hk hy hv).symm

theorem EntranceRadialInverseAt.radialDriftDifferential_eq {y : ProjectiveState} {k : ℝ}
    {Ψ : ProjectiveState → ProjectiveState} (H : EntranceRadialInverseAt y Ψ)
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (hv : 0 < y 2) :
    fderiv ℝ (fun z => entranceRadialDrift (Ψ z)) (entranceRadialCoordinates y) =
      entranceRadialDriftDifferential y := by
  ext v
  exact H.scalar_differential ((contDiffAt_entranceRadialDrift_one hk hy hv).differentiableAt (by norm_num)) v

theorem hasDerivAt_entranceRadialTangent {Y v : ℝ → ProjectiveState} {a t k : ℝ}
    (hY : HasDerivAt Y (a • entranceLogField (Y t)) t)
    (hv : HasDerivAt v (a • fderiv ℝ entranceLogField (Y t) (v t)) t)
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k (Y t)) (hV : 0 < Y t 2) :
    HasDerivAt (fun s => fderiv ℝ entranceStableRadius (Y s) (v s))
      (a * fderiv ℝ entranceRadialDrift (Y t) (v t)) t := by
  have hm : 2 ≤ Y t 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hu : |Y t 1| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.1.1]; linarith [hy.2.2.1.2]
  have hw : |Y t 3| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.2.2.1]; linarith [hy.2.2.2.2.2]
  have H := hasDerivAt_scaled_observable_variation (contDiffAt_entranceStableRadius_two hm hu hw hV)
    ((contDiffAt_entranceLogField 1 (entranceRegion_clock_pos hk hy).ne').differentiableAt (by norm_num)) hY hv
  rwa [(entranceRadialDrift_lie_eventuallyEq hk hy hV).fderiv_eq] at H

theorem entranceRadialDrift_tangent_decomposition {y v : ProjectiveState} {k : ℝ}
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (hv : 0 < y 2)
    (hu : y 1 ≠ 0) (hw : y 3 ≠ 0) (hactive : v 2 = 0) :
    fderiv ℝ entranceRadialDrift y v =
      entranceRadialVariationCoefficients y 0 * fderiv ℝ entranceStableRadius y v +
      entranceRadialVariationCoefficients y 1 * (v 1 / y 1) +
      entranceRadialVariationCoefficients y 2 * (v 3 / y 3) := by
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
  have hd : fderiv ℝ entranceRadialDrift y v = entranceRadialDriftDifferential y ![Z, v 1, 0, v 3] := by
    change _ = fderiv ℝ entranceRadialDrift y (entranceRadialInverseDifferential y _)
    rw [hinv]
  rw [hd, he]
  simp only [map_add, map_smul, smul_eq_mul]
  dsimp [entranceRadialVariationCoefficients]
  field_simp
  ring

theorem hasDerivAt_entranceProjectedRadialTangent {y : ProjectiveState} {t₀ t k : ℝ}
    (hD : 0 < projectiveStateDenom y) (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hk : 7 / 4 ≤ k) (hreg : entranceRegion k (projectiveOriginalFlow y t₀ t))
    (hv : 0 < projectiveOriginalFlow y t₀ t 2)
    (hu : projectiveOriginalFlow y t₀ t 1 ≠ 0) (hw : projectiveOriginalFlow y t₀ t 3 ≠ 0)
    (w : ProjectiveState) (hw0 : w 2 = 0) :
    let Y := projectiveOriginalFlow y t₀
    let v := fun s => entranceProjectedFlowVariation y t₀ s w
    let Z := fun s => fderiv ℝ entranceStableRadius (Y s) (v s)
    let c := entranceRadialVariationCoefficients (Y t)
    HasDerivAt Z (entranceOriginalClockRate (Y t) *
      (c 0 * Z t + c 1 * (v t 1 / Y t 1) + c 2 * (v t 3 / Y t 3))) t := by
  dsimp only
  have hclock := (entranceRegion_clock_pos hk hreg).ne'
  have hY := hasDerivAt_projectiveOriginalFlow_time hD ht hA
  rw [projectiveOriginalField_entranceLog hclock] at hY
  have H := hasDerivAt_entranceRadialTangent hY
    (hasDerivAt_entranceProjectedFlowVariation hD ht hA hv.ne' hclock w) hk hreg hv
  have hactive : entranceProjectedFlowVariation y t₀ t w 2 = 0 := by
    rw [entranceProjectedFlowVariation_active hv.ne' hclock w, hw0, zero_div, zero_mul]
  rwa [entranceRadialDrift_tangent_decomposition hk hreg hv hu hw hactive] at H

end BianchiIX
