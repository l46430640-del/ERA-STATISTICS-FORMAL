import BianchiIX.Analysis.MovingIntegralDerivative
import BianchiIX.Dynamics.CoreLogIntegralVariation
import BianchiIX.Dynamics.PartialCoreMultiplierRegularity

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology

theorem projectiveCoreLogRate_parameter_derivative {y : ProjectiveState} {t : ℝ}
    (hD : 0 < projectiveStateDenom y)
    (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) 0)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 t 0)
    (hV : 0 < projectiveOriginalFlow y 0 t 2)
    (hDz : projectiveStateDenom (projectiveOriginalFlow y 0 t) ≠ 0)
    (hd : let z := projectiveOriginalFlow y 0 t
      coreClockFactor (coreRadius (z 0) (z 2)) (z 1) (z 3) ≠ 0)
    (w : ProjectiveState) (i : Fin 2) :
    fderiv ℝ (fun p : ProjectiveState × ℝ =>
      coreOriginalLogRates (projectiveOriginalFlow p.1 0 p.2) i) (y, t) (w, 0) =
      (fderiv ℝ coreOriginalLogRates (projectiveOriginalFlow y 0 t)
        (projectiveFlowDifferential y 0 t w)) i := by
  have hFc := contDiffAt_pi.mp (contDiffAt_projectiveCoreLogRates hD ht hA hV hDz hd) i
  have hleft := (hFc.differentiableAt (by norm_num)).hasFDerivAt.comp y
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) y t)
  have hrate := hasFDerivAt_pi'.mp
    ((contDiffAt_coreOriginalLogRates 1 hV hDz hd).differentiableAt (by norm_num)).hasFDerivAt i
  have hright := hrate.comp y (hasFDerivAt_projectiveOriginalFlow_initial hD ht hA)
  exact congrArg (fun A : ProjectiveState →L[ℝ] ℝ => A w) (hleft.unique hright)

theorem partialCoreReturn_angle_derivative {y : ProjectiveState} {τ : ProjectiveState → ℝ}
    (hD : 0 < projectiveStateDenom y) (hτ : DifferentiableAt ℝ τ y)
    (ht : τ y ∈ normalizedMaxDomain (fromProjectiveState y) 0)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 (τ y) 0)
    (hV : 0 < projectiveOriginalFlow y 0 (τ y) 2) (w : ProjectiveState) :
    let z := projectiveOriginalFlow y 0 (τ y)
    fderiv ℝ (fun x => projectiveCoreAngle (projectiveOriginalFlow x 0 (τ x))) y w =
      fderiv ℝ projectiveCoreAngle z (projectiveFlowDifferential y 0 (τ y) w) +
      coreOriginalClockRate z * fderiv ℝ τ y w := by
  intro z
  have hangle := (contDiffAt_projectiveCoreAngle 1 hV).differentiableAt (by norm_num)
  have hF := hangle.comp (y, τ y)
    ((contDiffAt_projectiveOriginalFlow_two hD ht hA).differentiableAt (by norm_num))
  have hleft := hangle.hasFDerivAt.comp y (hasFDerivAt_projectiveOriginalFlow_initial hD ht hA)
  have hright := hasDerivAt_coreAngle_scaled (hasDerivAt_projectiveOriginalFlow_time hD ht hA) hV
  exact fderiv_variable_endpoint hF hτ hleft hright w

/-- Fixed-angle variation accounts for the interior; both ordinary endpoint motions remain. -/
theorem partialCoreReturn_log_derivative {k : ℝ} {y : ProjectiveState}
    {τ : ProjectiveState → ℝ} (hk : 6 ≤ k) (hD : 0 < projectiveStateDenom y)
    (hτ : ContDiffAt ℝ 1 τ y) (hpos : 0 ≤ τ y)
    (hdom : Icc 0 (τ y) ⊆ normalizedMaxDomain (fromProjectiveState y) 0)
    (hA : ∀ t ∈ Icc 0 (τ y), 0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 t 0)
    (hcore : ∀ t ∈ Icc 0 (τ y), coreRegion k (projectiveOriginalFlow y 0 t))
    (w : ProjectiveState) (i : Fin 2) :
    let β := projectiveOriginalFlow y 0
    let L := fun t => coreLogRates (projectiveCoreAngle (β t)) (toCoreAngleState (β t)) i
    fderiv ℝ (fun x => Real.log (partialCoreReturnMultiplier τ x i)) y w =
      (∫ t in 0..τ y, coreOriginalClockRate (β t) *
        (fderiv ℝ (coreLogRates (projectiveCoreAngle (β t))) (toCoreAngleState (β t))
          (coreProjectedFlowVariation y 0 t w)) i) +
      L (τ y) * fderiv ℝ (fun x => projectiveCoreAngle (projectiveOriginalFlow x 0 (τ x))) y w -
      L 0 * fderiv ℝ projectiveCoreAngle y w := by
  intro β L
  have hV (t : ℝ) (ht : t ∈ Icc 0 (τ y)) : 0 < β t 2 :=
    zero_lt_one.trans_le (hcore t ht).2.1
  have hreg (t : ℝ) (ht : t ∈ Icc 0 (τ y)) := coreRegion_clock_regular hk (hcore t ht)
  have hF (t : ℝ) (ht : t ∈ Icc 0 (τ y)) := contDiffAt_pi.mp
    (contDiffAt_projectiveCoreLogRates hD (hdom ht) (hA t ht)
      (hV t ht) (ne_of_gt (hreg t ht).1) (ne_of_gt (hreg t ht).2.1)) i
  have H := fderiv_moving_intervalIntegral hτ hpos hF w
  have hlog : (fun x => Real.log (partialCoreReturnMultiplier τ x i)) =
      (fun x => ∫ t in 0..τ x, coreOriginalLogRates (projectiveOriginalFlow x 0 t) i) := by
    ext x
    exact log_coreFlowMultiplier _ _ _ _ _
  rw [hlog, H]
  have hparam : (∫ t in 0..τ y, fderiv ℝ (fun p : ProjectiveState × ℝ =>
      coreOriginalLogRates (projectiveOriginalFlow p.1 0 p.2) i) (y, t) (w, 0)) =
      ∫ t in 0..τ y, (fderiv ℝ coreOriginalLogRates (β t) (projectiveFlowDifferential y 0 t w)) i := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc 0 (τ y) := uIcc_of_le hpos ▸ ht
    exact projectiveCoreLogRate_parameter_derivative hD (hdom ht') (hA t ht')
      (hV t ht') (ne_of_gt (hreg t ht').1) (ne_of_gt (hreg t ht').2.1) w i
  rw [hparam, coreFlow_log_rate_integral_variation hk hpos hD hdom hA hcore w i]
  have hend : τ y ∈ Icc 0 (τ y) := ⟨hpos, le_rfl⟩
  rw [partialCoreReturn_angle_derivative hD (hτ.differentiableAt (by norm_num))
    (hdom hend) (hA _ hend) (hV _ hend) w]
  dsimp only [coreLogBoundary, coreOriginalLogRates]
  simp only [projectiveOriginalFlow_initial hD, projectiveFlowDifferential_initial hD,
    ContinuousLinearMap.id_apply]
  dsimp only [L, β]
  simp only [Pi.smul_apply, smul_eq_mul, projectiveOriginalFlow_initial hD]
  ring

end BianchiIX
