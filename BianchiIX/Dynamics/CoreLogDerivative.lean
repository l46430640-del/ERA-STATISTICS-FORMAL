import BianchiIX.Analysis.MovingIntegralDerivative
import BianchiIX.Dynamics.CoreLogIntegralVariation
import BianchiIX.Dynamics.CoreMultiplierDifferential

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology

theorem contDiffAt_coreEntryLogRates {Y : CoreAngleState} {t : ℝ}
    (hk : 1 < Y 0) (hD : 0 < projectiveStateDenom (coreRadiusEntry Y))
    (ht : t ∈ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry Y)) 0)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState (coreRadiusEntry Y)) 0 t 0)
    (hV : 0 < projectiveOriginalFlow (coreRadiusEntry Y) 0 t 2)
    (hDz : projectiveStateDenom (projectiveOriginalFlow (coreRadiusEntry Y) 0 t) ≠ 0)
    (hd : let z := projectiveOriginalFlow (coreRadiusEntry Y) 0 t
      coreClockFactor (coreRadius (z 0) (z 2)) (z 1) (z 3) ≠ 0) :
    ContDiffAt ℝ 1 (fun p : CoreAngleState × ℝ =>
      coreOriginalLogRates (projectiveOriginalFlow (coreRadiusEntry p.1) 0 p.2)) (Y, t) :=
  (contDiffAt_coreOriginalLogRates 1 hV hDz hd).comp (Y, t) (g := coreOriginalLogRates)
    (f := fun p : CoreAngleState × ℝ => projectiveOriginalFlow (coreRadiusEntry p.1) 0 p.2)
    (contDiffAt_coreRadius_flow hk hD ht hA)

theorem coreEntryLogRate_parameter_derivative {Y : CoreAngleState} {t : ℝ}
    (hk : 1 < Y 0) (hD : 0 < projectiveStateDenom (coreRadiusEntry Y))
    (ht : t ∈ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry Y)) 0)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState (coreRadiusEntry Y)) 0 t 0)
    (hV : 0 < projectiveOriginalFlow (coreRadiusEntry Y) 0 t 2)
    (hDz : projectiveStateDenom (projectiveOriginalFlow (coreRadiusEntry Y) 0 t) ≠ 0)
    (hd : let z := projectiveOriginalFlow (coreRadiusEntry Y) 0 t
      coreClockFactor (coreRadius (z 0) (z 2)) (z 1) (z 3) ≠ 0) (v : CoreAngleState) (i : Fin 2) :
    fderiv ℝ (fun p : CoreAngleState × ℝ =>
      coreOriginalLogRates (projectiveOriginalFlow (coreRadiusEntry p.1) 0 p.2) i) (Y, t) (v, 0) =
      (fderiv ℝ coreOriginalLogRates (projectiveOriginalFlow (coreRadiusEntry Y) 0 t)
        (projectiveFlowDifferential (coreRadiusEntry Y) 0 t (fderiv ℝ coreRadiusEntry Y v))) i := by
  have hFc := contDiffAt_pi.mp (contDiffAt_coreEntryLogRates hk hD ht hA hV hDz hd) i
  have hF := hFc.differentiableAt (by norm_num)
  have hleft := hF.hasFDerivAt.comp Y (hasFDerivAt_prodMk_left (𝕜 := ℝ) Y t)
  have hrate := hasFDerivAt_pi'.mp
    ((contDiffAt_coreOriginalLogRates 1 hV hDz hd).differentiableAt (by norm_num)).hasFDerivAt i
  have hentry := ((contDiffAt_coreRadiusEntry 1 hk).differentiableAt (by norm_num)).hasFDerivAt
  have hright := hrate.comp Y ((hasFDerivAt_projectiveOriginalFlow_initial hD ht hA).comp Y hentry)
  exact congrArg (fun A : CoreAngleState →L[ℝ] ℝ => A v) (hleft.unique hright)

theorem coreReturn_angle_derivative {Y : CoreAngleState} {τ : CoreAngleState → ℝ}
    (hk : 1 < Y 0) (hD : 0 < projectiveStateDenom (coreRadiusEntry Y))
    (hτ : DifferentiableAt ℝ τ Y)
    (ht : τ Y ∈ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry Y)) 0)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState (coreRadiusEntry Y)) 0 (τ Y) 0)
    (hV : 0 < projectiveOriginalFlow (coreRadiusEntry Y) 0 (τ Y) 2) (v : CoreAngleState) :
    let z := projectiveOriginalFlow (coreRadiusEntry Y) 0 (τ Y)
    fderiv ℝ (fun Z => projectiveCoreAngle (projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z))) Y v =
      fderiv ℝ projectiveCoreAngle z
        (projectiveFlowDifferential (coreRadiusEntry Y) 0 (τ Y) (fderiv ℝ coreRadiusEntry Y v)) +
      coreOriginalClockRate z * fderiv ℝ τ Y v := by
  intro z
  have hangle := (contDiffAt_projectiveCoreAngle 1 hV).differentiableAt (by norm_num)
  have hF := hangle.comp (Y, τ Y)
    ((contDiffAt_coreRadius_flow hk hD ht hA).differentiableAt (by norm_num))
  have hentry := ((contDiffAt_coreRadiusEntry 1 hk).differentiableAt (by norm_num)).hasFDerivAt
  have hleft := hangle.hasFDerivAt.comp Y ((hasFDerivAt_projectiveOriginalFlow_initial hD ht hA).comp Y hentry)
  have hright := hasDerivAt_coreAngle_scaled (hasDerivAt_projectiveOriginalFlow_time hD ht hA) hV
  exact fderiv_variable_endpoint hF hτ hleft hright v

/-- The interior integrand uses fixed-angle variations; all clock motion is at the endpoints. -/
theorem coreReturn_log_derivative {Y : CoreAngleState} {τ : CoreAngleState → ℝ}
    (hk : 6 ≤ Y 0) (hD : 0 < projectiveStateDenom (coreRadiusEntry Y))
    (hτ : ContDiffAt ℝ 1 τ Y) (hpos : 0 ≤ τ Y)
    (hdom : Icc 0 (τ Y) ⊆ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry Y)) 0)
    (hA : ∀ t ∈ Icc 0 (τ Y), 0 < 1 + normalizedMaxCurve (fromProjectiveState (coreRadiusEntry Y)) 0 t 0)
    (hcore : ∀ t ∈ Icc 0 (τ Y), coreRegion (Y 0) (projectiveOriginalFlow (coreRadiusEntry Y) 0 t))
    (v : CoreAngleState) (i : Fin 2) :
    let y := coreRadiusEntry Y
    let β := projectiveOriginalFlow y 0
    let w := fderiv ℝ coreRadiusEntry Y v
    let L := fun t => coreLogRates (projectiveCoreAngle (β t)) (toCoreAngleState (β t)) i
    fderiv ℝ (fun Z => Real.log (coreReturnMultiplier τ Z i)) Y v =
      (∫ t in 0..τ Y, coreOriginalClockRate (β t) *
        (fderiv ℝ (coreLogRates (projectiveCoreAngle (β t))) (toCoreAngleState (β t))
          (coreProjectedFlowVariation y 0 t w)) i) +
      L (τ Y) * fderiv ℝ (fun Z => projectiveCoreAngle (projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z))) Y v -
      L 0 * fderiv ℝ (fun Z => projectiveCoreAngle (coreRadiusEntry Z)) Y v := by
  intro y β w L
  have hV (t : ℝ) (ht : t ∈ Icc 0 (τ Y)) : 0 < β t 2 :=
    lt_of_lt_of_le zero_lt_one (hcore t ht).2.1
  have hreg (t : ℝ) (ht : t ∈ Icc 0 (τ Y)) := coreRegion_clock_regular hk (hcore t ht)
  have hF (t : ℝ) (ht : t ∈ Icc 0 (τ Y)) := contDiffAt_pi.mp
    (contDiffAt_coreEntryLogRates (by linarith only [hk]) hD (hdom ht) (hA t ht)
      (hV t ht) (ne_of_gt (hreg t ht).1) (ne_of_gt (hreg t ht).2.1)) i
  have H := fderiv_moving_intervalIntegral hτ hpos hF v
  have hlog : (fun Z => Real.log (coreReturnMultiplier τ Z i)) =
      (fun Z => ∫ t in 0..τ Z, coreOriginalLogRates (projectiveOriginalFlow (coreRadiusEntry Z) 0 t) i) := by
    ext Z
    exact log_coreFlowMultiplier _ _ _ _ _
  rw [hlog, H]
  have hparam : (∫ t in 0..τ Y, fderiv ℝ (fun p : CoreAngleState × ℝ =>
      coreOriginalLogRates (projectiveOriginalFlow (coreRadiusEntry p.1) 0 p.2) i) (Y, t) (v, 0)) =
      ∫ t in 0..τ Y, (fderiv ℝ coreOriginalLogRates (β t) (projectiveFlowDifferential y 0 t w)) i := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc 0 (τ Y) := uIcc_of_le hpos ▸ ht
    exact coreEntryLogRate_parameter_derivative (by linarith only [hk]) hD (hdom ht') (hA t ht')
      (hV t ht') (ne_of_gt (hreg t ht').1) (ne_of_gt (hreg t ht').2.1) v i
  rw [hparam, coreFlow_log_rate_integral_variation hk hpos hD hdom hA hcore w i]
  have hend : τ Y ∈ Icc 0 (τ Y) := ⟨hpos, le_rfl⟩
  rw [coreReturn_angle_derivative (by linarith only [hk]) hD (hτ.differentiableAt (by norm_num))
    (hdom hend) (hA _ hend) (hV _ hend) v]
  have hentryAngle := ((contDiffAt_projectiveCoreAngle 1
    (show 0 < coreRadiusEntry Y 2 by change (0 : ℝ) < 1; norm_num)).differentiableAt (by norm_num)).hasFDerivAt.comp Y
      (((contDiffAt_coreRadiusEntry 1 (by linarith only [hk])).differentiableAt (by norm_num)).hasFDerivAt)
  change HasFDerivAt (fun Z => projectiveCoreAngle (coreRadiusEntry Z)) _ _ at hentryAngle
  rw [hentryAngle.fderiv]
  dsimp only [coreLogBoundary, coreOriginalLogRates, ContinuousLinearMap.comp_apply]
  simp only [projectiveOriginalFlow_initial hD, projectiveFlowDifferential_initial hD,
    ContinuousLinearMap.id_apply]
  dsimp only [L, β, y, w]
  simp only [Pi.smul_apply, smul_eq_mul, projectiveOriginalFlow_initial hD]
  ring

/-- The projected integral formula holds for a genuine first return, including zero walls. -/
theorem exists_large_core_log_derivative {Y : CoreAngleState} (hk : 6 ≤ Y 0)
    (hu : 0 ≤ Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0)
    (hw : 0 ≤ Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0) :
    ∃ τ : CoreAngleState → ℝ, 0 < τ Y ∧ ContDiffAt ℝ 1 τ Y ∧
      (∀ᶠ Z in 𝓝 Y, IsLeast {t | 0 < t ∧ projectiveOriginalFlow (coreRadiusEntry Z) 0 t 2 = 1} (τ Z)) ∧
      (∀ i : Fin 2, DifferentiableAt ℝ (fun Z => Real.log (coreReturnMultiplier τ Z i)) Y) ∧
      ∀ (v : CoreAngleState) (i : Fin 2),
        let y := coreRadiusEntry Y
        let β := projectiveOriginalFlow y 0
        let w := fderiv ℝ coreRadiusEntry Y v
        let L := fun t => coreLogRates (projectiveCoreAngle (β t)) (toCoreAngleState (β t)) i
        fderiv ℝ (fun Z => Real.log (coreReturnMultiplier τ Z i)) Y v =
          (∫ t in 0..τ Y, coreOriginalClockRate (β t) *
            (fderiv ℝ (coreLogRates (projectiveCoreAngle (β t))) (toCoreAngleState (β t))
              (coreProjectedFlowVariation y 0 t w)) i) +
          L (τ Y) * fderiv ℝ (fun Z => projectiveCoreAngle (projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z))) Y v -
          L 0 * fderiv ℝ (fun Z => projectiveCoreAngle (coreRadiusEntry Z)) Y v := by
  have hD := (coreRegion_clock_regular hk (coreRadiusEntry_region hk hu hw)).1
  have hc := fromProjectiveState_constraint (ne_of_gt hD)
  obtain ⟨T, hT, hfirst, τ, hτ, hcτ, hnear, _⟩ := exists_large_core_radius_arrival hk hu hw
  obtain ⟨S, _, hfirstS, hcore, _⟩ := exists_large_core_traversal hk hu hw
  have hST : S = T := hfirstS.unique hfirst
  subst S
  have hdom : Icc 0 (τ Y) ⊆ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry Y)) 0 :=
    fun t ht => normalizedMaxDomain_contains_Ici_of_constraint hc 0 ht.1
  have hA : ∀ t ∈ Icc 0 (τ Y), 0 < 1 + normalizedMaxCurve (fromProjectiveState (coreRadiusEntry Y)) 0 t 0 :=
    fun t ht => (hcore t (hτ ▸ ht)).1
  have hregion : ∀ t ∈ Icc 0 (τ Y), coreRegion (Y 0) (projectiveOriginalFlow (coreRadiusEntry Y) 0 t) :=
    fun t ht => (hcore t (hτ ▸ ht)).2
  refine ⟨τ, hτ ▸ hT, hcτ, hnear.mono (fun _ h => h.1), ?_, ?_⟩
  · intro i
    exact (hasFDerivAt_log_coreReturnMultiplier hk hD hcτ (hτ ▸ hT.le) hdom hA hregion i).differentiableAt
  · intro v i
    exact coreReturn_log_derivative hk hD hcτ (hτ ▸ hT.le) hdom hA hregion v i

end BianchiIX
