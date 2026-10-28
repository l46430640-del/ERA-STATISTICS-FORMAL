import BianchiIX.Dynamics.EntranceReturnMultipliers
import BianchiIX.Dynamics.ProjectiveFlowVariation
import BianchiIX.Analysis.ScalarMultiplier

noncomputable section

namespace BianchiIX

open Set MeasureTheory

theorem scaled_zero_strong_weak_product {Y : ℝ → ProjectiveState} {a : ℝ → ℝ} {s t : ℝ}
    (hst : s ≤ t) (ha : ContinuousOn a (Icc s t))
    (hY : ∀ r ∈ Icc s t, HasDerivAt Y (a r • projectiveField (Y r)) r)
    (hu : ∀ r ∈ Icc s t, Y r 1 = 0) :
    Y t 2 * Y t 3 = Y s 2 * Y s 3 * Real.exp (-2 * ∫ r in s..t, a r) := by
  have hcoord (i : Fin 4) := (continuous_apply i).comp_continuousOn (HasDerivAt.continuousOn hY)
  have hp (r : ℝ) (hr : r ∈ Ioo s t) :
      HasDerivAt (fun b => Y b 2 * Y b 3) ((-2 * a r) * (Y r 2 * Y r 3)) r := by
    have H := (hasDerivAt_pi.mp (hY r (Ioo_subset_Icc_self hr)) 2).mul
      (hasDerivAt_pi.mp (hY r (Ioo_subset_Icc_self hr)) 3)
    convert! H using 1
    dsimp [projectiveField, activeVelocity, weakVelocity, coupling]
    rw [hu r (Ioo_subset_Icc_self hr)]
    ring
  have H := homogeneous_solution_eq_exp_integral_Icc hst (ha.const_mul (-2)) ((hcoord 2).mul (hcoord 3)) hp
  rwa [intervalIntegral.integral_const_mul] at H

/-- The exact product identity along every prefix of the actual Einstein entrance. -/
theorem entranceReturn_weak_product {y : ProjectiveState} {t : ℝ}
    (hD : 0 < projectiveStateDenom y) (H : entranceReturnValid y) (hu : y 1 = 0)
    (ht : t ∈ Icc 0 (entranceReturnTime y)) :
    projectiveOriginalFlow y 0 t 2 * projectiveOriginalFlow y 0 t 3 =
      y 2 * y 3 * Real.exp (-2 * ∫ r in 0..t, normalizedProjectiveRate (fromProjectiveState y) 0 r) := by
  let x := fromProjectiveState y
  let Y := projectiveOriginalFlow y 0
  let a := normalizedProjectiveRate x 0
  have hprefix (r : ℝ) (hr : r ∈ Icc 0 t) : r ∈ Icc 0 (entranceReturnTime y) :=
    ⟨hr.1, hr.2.trans ht.2⟩
  have hA (r : ℝ) (hr : r ∈ Icc 0 t) : 0 < a r := (H.2.1 r (hprefix r hr)).2
  have hY (r : ℝ) (hr : r ∈ Icc 0 t) : HasDerivAt Y (a r • projectiveField (Y r)) r :=
    hasDerivAt_toProjectiveState_normalized (hasDerivAt_normalizedMaxCurve (H.2.1 r (hprefix r hr)).1)
      (hA r hr).ne' ((normalizedMaxCurve_constraint (H.2.1 r (hprefix r hr)).1).trans
        (fromProjectiveState_constraint hD.ne'))
  have hU (r : ℝ) (hr : r ∈ Icc 0 t) : Y r 1 = 0 := by
    have HF := normalizedProjectiveWallMultiplier_formula (H.2.1 r (hprefix r hr)).1
      (fromProjectiveState_clock_pos hD) (hA r hr) 0
    rw [toProjectiveState_fromProjectiveState hD.ne'] at HF
    change Y r 1 = y 1 * normalizedProjectiveWallMultiplier x r 0 at HF
    simpa only [hu, zero_mul] using HF
  have hac : ContinuousOn a (Icc 0 t) := (continuousOn_normalizedProjectiveRate x 0).mono
    (fun r hr => (H.2.1 r (hprefix r hr)).1)
  have HP := scaled_zero_strong_weak_product ht.1 hac hY hU
  change Y t 2 * Y t 3 = Y 0 2 * Y 0 3 * Real.exp (-2 * ∫ r in 0..t, a r) at HP
  rwa [show Y 0 = y from projectiveOriginalFlow_initial hD 0] at HP

end BianchiIX
