import BianchiIX.Dynamics.ReferenceTail
import BianchiIX.Dynamics.ActiveWallFirstHit
import BianchiIX.Dynamics.CoreEntryDifferential

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def coreTailEntry (Y : CoreAngleState) : ProjectiveState :=
  ![1 - Real.sqrt (Y 0 ^ 2 - 1), Y 1, 1, Y 2]

def coreTailTime (η : ℝ) (Y : CoreAngleState) : ℝ :=
  sInf {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState (coreTailEntry Y)) 0 ∧
    projectiveActiveWall (normalizedMaxCurve (fromProjectiveState (coreTailEntry Y)) 0 t) = η}

def coreTailState (η : ℝ) (Y : CoreAngleState) : ProjectiveState :=
  projectiveOriginalFlow (coreTailEntry Y) 0 (coreTailTime η Y)

def coreTailValid (η : ℝ) (Y : CoreAngleState) : Prop :=
  let x := fromProjectiveState (coreTailEntry Y)
  let T := coreTailTime η Y
  IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain x 0 ∧
    projectiveActiveWall (normalizedMaxCurve x 0 t) = η} T ∧
    (∀ t ∈ Icc 0 T, t ∈ normalizedMaxDomain x 0 ∧ 0 < 1 + normalizedMaxCurve x 0 t 0) ∧
    (∀ t ∈ Ico 0 T, η < projectiveActiveWall (normalizedMaxCurve x 0 t)) ∧
    (∀ t ∈ Icc 0 T, normalizedEventRate projectiveActiveWall x 0 t < 0) ∧
    (∀ t ∈ Icc 0 T, |toProjectiveState (normalizedMaxCurve x 0 t) 3| < 1 / 2)

theorem contDiffAt_coreTailEntry (n : WithTop ℕ∞) {Y : CoreAngleState} (hk : 1 < Y 0) :
    ContDiffAt ℝ n coreTailEntry Y := by
  have hs : Y 0 ^ 2 - 1 ≠ 0 := ne_of_gt (by nlinarith only [hk] : 0 < Y 0 ^ 2 - 1)
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [coreTailEntry] <;> fun_prop

theorem coreTailEntry_reference {k : ℝ} (hk : 1 < k) :
    coreTailEntry ![k, 0, 0] = referencePulse k (referenceHalfTime k) := by
  rw [referencePulse_exit hk]
  rfl

/-- This chart recovers the actual state on every downward core exit. -/
theorem coreTailEntry_of_exit {y : ProjectiveState} (hM : y 0 < 1) (hV : y 2 = 1) :
    coreTailEntry (toCoreAngleState y) = y := by
  have hs : (toCoreAngleState y 0) ^ 2 - 1 = (y 0 - 1) ^ 2 := by
    change coreRadius (y 0) (y 2) ^ 2 - 1 = _
    rw [coreRadius_sq, hV]
    dsimp [coreEnergy]
    ring
  ext i
  fin_cases i
  · change 1 - Real.sqrt ((toCoreAngleState y 0) ^ 2 - 1) = y 0
    rw [hs, Real.sqrt_sq_eq_abs, abs_of_neg (by linarith only [hM] : y 0 - 1 < 0)]
    ring
  · rfl
  · exact hV.symm
  · change y 2 * y 3 = y 3
    rw [hV, one_mul]

/-- The finite tail has a canonical first-hit map with two derivatives near each boundary orbit. -/
theorem coreTail_reference_regular {k η : ℝ} (hk : 1 < k) (hη : 0 < η ∧ η < 1) :
    coreTailTime η ![k, 0, 0] = referenceTailTime k η ∧
      coreTailState η ![k, 0, 0] = ![1 - Real.sqrt (k ^ 2 - η ^ 2), 0, η, 0] ∧
      ContDiffAt ℝ 2 (coreTailTime η) ![k, 0, 0] ∧
      ContDiffAt ℝ 2 (coreTailState η) ![k, 0, 0] ∧
      (∀ᶠ Y in 𝓝 (![k, 0, 0] : CoreAngleState), coreTailValid η Y) := by
  let Y₀ : CoreAngleState := ![k, 0, 0]
  let c : CoreAngleState → NormalizedState := fun Y => fromProjectiveState (coreTailEntry Y)
  have hc₀ : c Y₀ = referenceExitState k := by
    dsimp only [c, Y₀]
    rw [coreTailEntry_reference hk]
    rfl
  have hD : 0 < projectiveStateDenom (coreTailEntry Y₀) := by
    rw [coreTailEntry_reference hk]
    exact referencePulse_denom_pos k _
  have hcc : ContDiffAt ℝ 2 c Y₀ :=
    (contDiffAt_fromProjectiveState 2 (ne_of_gt hD)).comp Y₀ (contDiffAt_coreTailEntry 2 hk)
  have H := referenceTail_normalized_segment hk hη
  obtain ⟨τ, hτ, hcτ, hcP, _, hnear⟩ := exists_activeWall_first_downward_hit_two H.1
    (fun t ht => ⟨(H.2.2 t ht).1, (H.2.2 t ht).2.1⟩)
    (fun t ht => (H.2.2 t ht).2.2.1) (referenceTail_active_hit hk hη)
  have hsmall : ∀ᶠ x in 𝓝 (referenceExitState k), ∀ t ∈ Icc 0 (τ x),
      |toProjectiveState (normalizedMaxCurve x 0 t) 3| < 1 / 2 := by
    apply eventually_forall_movingInterval hcτ.continuousAt (by rw [hτ]; exact H.1)
    intro t ht
    rw [hτ] at ht
    have hreg := H.2.2 t ht
    have hf := (normalizedMaxCurve_regular hreg.1).2.continuousAt
    have hp : ContinuousAt (fun q : NormalizedState × ℝ =>
        toProjectiveState (normalizedMaxCurve q.1 0 q.2)) (referenceExitState k, t) :=
      ContinuousAt.comp (g := toProjectiveState) (f := fun q : NormalizedState × ℝ => normalizedMaxCurve q.1 0 q.2)
        (contDiffAt_toProjectiveState 1 (ne_of_gt hreg.2.1)).continuousAt hf
    apply (continuousAt_pi.mp hp 3).abs.eventually (isOpen_Iio.mem_nhds _)
    change |toProjectiveState (normalizedMaxCurve (referenceExitState k) 0 t) 3| < 1 / 2
    rw [hreg.2.2.2, abs_zero]
    norm_num
  have hnear' := hcc.continuousAt.eventually (hc₀.symm ▸ hnear)
  have hsmall' := hcc.continuousAt.eventually (hc₀.symm ▸ hsmall)
  have heq : coreTailTime η =ᶠ[𝓝 Y₀] (fun Y => τ (c Y)) := by
    filter_upwards [hnear'] with Y hY
    exact hY.1.csInf_eq
  have hcTime : ContDiffAt ℝ 2 (coreTailTime η) Y₀ :=
    ((hc₀.symm ▸ hcτ).comp Y₀ hcc).congr_of_eventuallyEq heq
  have hcOut : ContDiffAt ℝ 2 (coreTailState η) Y₀ := by
    have hcomp : ContDiffAt ℝ 2 (fun Y => toProjectiveState (normalizedMaxCurve (c Y) 0 (τ (c Y)))) Y₀ :=
      (hc₀.symm ▸ hcP).comp Y₀ hcc
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [heq] with Y hY
    dsimp only [coreTailState, projectiveOriginalFlow]
    rw [hY]
  have htime : coreTailTime η Y₀ = referenceTailTime k η :=
    heq.self_of_nhds.trans ((congrArg τ hc₀).trans hτ)
  refine ⟨htime, ?_, hcTime, hcOut, ?_⟩
  · change toProjectiveState (normalizedMaxCurve (c Y₀) 0 (coreTailTime η Y₀)) = _
    rw [hc₀, htime, H.2.1]
    have hDout : 0 < projectiveStateDenom (![1 - Real.sqrt (k ^ 2 - η ^ 2), 0, η, 0] : ProjectiveState) := by
      rw [← referencePulse_height_exit (lt_trans zero_lt_one hk) ⟨hη.1, hη.2.trans hk⟩]
      exact referencePulse_denom_pos k _
    exact toProjectiveState_fromProjectiveState (ne_of_gt hDout)
  · filter_upwards [heq, hnear', hsmall'] with Y hY hfirst hsmallY
    dsimp only [coreTailValid]
    rw [hY]
    exact ⟨hfirst.1, hfirst.2.1, hfirst.2.2.1, hfirst.2.2.2, hsmallY⟩

end BianchiIX
