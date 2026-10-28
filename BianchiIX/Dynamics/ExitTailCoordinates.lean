import BianchiIX.Algebra.ExitTailBounds
import BianchiIX.Dynamics.ExitClock

noncomputable section

namespace BianchiIX

open Set

abbrev ExitTailState := Fin 3 → ℝ

def toExitTailState (y : ProjectiveState) : ExitTailState := ![coreRadius (y 0) (y 2), y 1, y 3]

def fromExitTailState (v : ℝ) (Y : ExitTailState) : ProjectiveState :=
  ![1 - exitTailGap (Y 0) v, Y 1, v, Y 2]

def exitTailField (v : ℝ) (Y : ExitTailState) : ExitTailState :=
  ![exitTailRadial (Y 0) (Y 1) v (Y 2),
    exitTailStrongRate (Y 0) (Y 1) v (Y 2) * Y 1,
    exitTailWeakRate (Y 0) (Y 1) v (Y 2) * Y 2]

theorem fromExitTailState_toExitTailState {y : ProjectiveState} (hm : y 0 < 1) :
    fromExitTailState (y 2) (toExitTailState y) = y := by
  ext i
  fin_cases i
  · change 1 - exitTailGap (coreRadius (y 0) (y 2)) (y 2) = y 0
    rw [exitTailGap_of_coreRadius hm]
    ring
  · rfl
  · rfl
  · rfl

theorem toExitTailState_fromExitTailState {v : ℝ} {Y : ExitTailState}
    (hR : 0 < Y 0) (hv : v ^ 2 ≤ (Y 0) ^ 2) :
    toExitTailState (fromExitTailState v Y) = Y := by
  have hs := exitTailGap_sq hv
  have he : coreEnergy (1 - exitTailGap (Y 0) v) v = (Y 0) ^ 2 := by
    dsimp only [coreEnergy]
    nlinarith only [hs]
  ext i
  fin_cases i
  · change Real.sqrt (coreEnergy (1 - exitTailGap (Y 0) v) v) = Y 0
    rw [he, Real.sqrt_sq hR.le]
  · rfl
  · rfl

theorem exitClockRate_tail {y : ProjectiveState} (hm : y 0 < 1) :
    exitClockRate y = exitTailSpeed (coreRadius (y 0) (y 2)) (y 1) (y 2) (y 3) := by
  dsimp only [exitClockRate, exitTailSpeed]
  rw [exitTailGap_of_coreRadius hm]

theorem exitClockRate_compact {y : ProjectiveState} (hm : y 0 < 1)
    (hR : 7 / 4 ≤ coreRadius (y 0) (y 2))
    (hu : |y 1| ≤ 1 / 100) (hv : 0 ≤ y 2 ∧ y 2 ≤ 1) (hw : |y 3| ≤ 1 / 100) :
    1 / 2 ≤ exitClockRate y := by
  rw [exitClockRate_tail hm]
  exact exitTailSpeed_compact hR hu hv hw

theorem contDiffAt_exitTailField (n : WithTop ℕ∞) {v : ℝ} {Y : ExitTailState}
    (hv : v ^ 2 < (Y 0) ^ 2) (hR : Y 0 ≠ 0)
    (hd : exitTailSpeed (Y 0) (Y 1) v (Y 2) ≠ 0) :
    ContDiffAt ℝ n (fun q : ℝ × ExitTailState => exitTailField q.1 q.2) (v, Y) := by
  have hcoord (i : Fin 3) : ContDiffAt ℝ n (fun q : ℝ × ExitTailState => q.2 i) (v, Y) := by fun_prop
  have hgap : ContDiffAt ℝ n (fun q : ℝ × ExitTailState => exitTailGap (q.2 0) q.1) (v, Y) := by
    unfold exitTailGap
    exact (((hcoord 0).pow 2).sub (contDiffAt_fst.pow 2)).sqrt
      (ne_of_gt (sub_pos.mpr hv))
  have hc : ContDiffAt ℝ n (fun q : ℝ × ExitTailState => coupling (q.2 1) q.1 (q.2 2)) (v, Y) := by
    unfold coupling
    fun_prop
  have hs : ContDiffAt ℝ n (fun q : ℝ × ExitTailState => exitTailSpeed (q.2 0) (q.2 1) q.1 (q.2 2)) (v, Y) := hgap.add hc
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · change ContDiffAt ℝ n (fun q : ℝ × ExitTailState => exitTailRadial (q.2 0) (q.2 1) q.1 (q.2 2)) (v, Y)
    unfold exitTailRadial
    exact (((hc.neg.mul (hcoord 0)).sub
      ((hgap.mul (by fun_prop)).div (by fun_prop) hR)).div hs hd)
  · change ContDiffAt ℝ n (fun q : ℝ × ExitTailState => exitTailStrongRate (q.2 0) (q.2 1) q.1 (q.2 2) * q.2 1) (v, Y)
    unfold exitTailStrongRate
    apply ContDiffAt.mul _ (hcoord 1)
    have hn : ContDiffAt ℝ n (fun q : ℝ × ExitTailState =>
        2 * exitTailGap (q.2 0) q.1 - (q.2 0) ^ 2 + 2 * q.1 * q.2 2 - (q.2 2) ^ 2 + (q.2 1) ^ 2) (v, Y) := by fun_prop
    exact hn.div (contDiffAt_const.mul hs) (mul_ne_zero (by norm_num) hd)
  · change ContDiffAt ℝ n (fun q : ℝ × ExitTailState => exitTailWeakRate (q.2 0) (q.2 1) q.1 (q.2 2) * q.2 2) (v, Y)
    unfold exitTailWeakRate
    apply ContDiffAt.mul _ (hcoord 2)
    exact ((hgap.sub contDiffAt_const).sub hc).div hs hd

/-- The logarithmic tail equations are the exact pullback of the projective Einstein vector field. -/
theorem hasDerivAt_toExitTailState {β : ℝ → ProjectiveState} {t : ℝ}
    (hβ : HasDerivAt β (exitLogField (β t)) t) (hv : 0 < β t 2)
    (hm : β t 0 < 1) :
    HasDerivAt (fun s => toExitTailState (β s)) (exitTailField (β t 2) (toExitTailState (β t))) t := by
  have hg := exitTailGap_of_coreRadius (v := β t 2) hm
  have he := coreRadius_sq (β t 0) (β t 2)
  have hc := exitClockRate_tail hm
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · have H := hasDerivAt_coreRadius (hasDerivAt_pi.mp hβ 0) (hasDerivAt_pi.mp hβ 2) hv
    convert! H using 1
    change exitTailRadial (coreRadius (β t 0) (β t 2)) (β t 1) (β t 2) (β t 3) = _
    calc
      _ = (exitClockRate (β t))⁻¹ * (-coupling (β t 1) (β t 2) (β t 3) * coreRadius (β t 0) (β t 2) +
          (β t 0 - 1) / coreRadius (β t 0) (β t 2) * (β t 1 - β t 3) ^ 2) := by
        dsimp only [exitTailRadial]
        rw [hg, ← hc]
        ring
      _ = _ := by
        rw [← coreRadius_directional hv]
        change _ = ((β t 0 - 1) * ((exitClockRate (β t))⁻¹ * phaseVelocity _ _ _ _) +
          β t 2 * ((exitClockRate (β t))⁻¹ * activeVelocity _ _ _ _)) / _
        ring
  · have H := hasDerivAt_pi.mp hβ 1
    convert! H using 1
    change exitTailStrongRate (coreRadius (β t 0) (β t 2)) (β t 1) (β t 2) (β t 3) * β t 1 =
      (exitClockRate (β t))⁻¹ * strongVelocity (β t 0) (β t 1) (β t 2) (β t 3)
    dsimp only [exitTailStrongRate, strongVelocity]
    rw [hg, ← hc, he]
    dsimp only [coreEnergy]
    ring
  · have H := hasDerivAt_pi.mp hβ 3
    convert! H using 1
    change exitTailWeakRate (coreRadius (β t 0) (β t 2)) (β t 1) (β t 2) (β t 3) * β t 3 =
      (exitClockRate (β t))⁻¹ * weakVelocity (β t 0) (β t 1) (β t 2) (β t 3)
    dsimp only [exitTailWeakRate, weakVelocity]
    rw [hg, ← hc]
    ring

/-- The signed compact tail chart is realized by the normalized Einstein flow with V = V0 exp(-s). -/
theorem exists_normalized_exitTail_coordinates {x : NormalizedState} {t₀ s : ℝ}
    {I : Set ℝ} (hI : Convex ℝ I) (ho : IsOpen I) (hs : s ∈ I)
    (hdom : I ⊆ normalizedMaxDomain x t₀) (hc : stateConstraint x = 1)
    (hA : ∀ t ∈ I, 0 < 1 + normalizedMaxCurve x t₀ t 0)
    (hregion : ∀ t ∈ I, let y := toProjectiveState (normalizedMaxCurve x t₀ t)
      y 0 < 1 ∧ 7 / 4 ≤ coreRadius (y 0) (y 2) ∧ |y 1| ≤ 1 / 100 ∧
        (0 < y 2 ∧ y 2 ≤ 1) ∧ |y 3| ≤ 1 / 100) :
    let β := fun t => toProjectiveState (normalizedMaxCurve x t₀ t)
    ∃ e : OpenPartialHomeomorph ℝ ℝ,
      e.source = I ∧ (∀ t ∈ I, e t = Real.log (β s 2) - Real.log (β t 2)) ∧
      Convex ℝ e.target ∧ 0 ∈ e.target ∧ e.symm 0 = s ∧ StrictMonoOn e I ∧
      (∀ z ∈ e.target,
        β (e.symm z) 2 = β s 2 * Real.exp (-z) ∧
        HasDerivAt (fun u => toExitTailState (β (e.symm u)))
          (exitTailField (β s 2 * Real.exp (-z)) (toExitTailState (β (e.symm z)))) z ∧
        fromExitTailState (β s 2 * Real.exp (-z)) (toExitTailState (β (e.symm z))) = β (e.symm z)) := by
  have hv (t : ℝ) (ht : t ∈ I) := (hregion t ht).2.2.2.1.1
  have hd (t : ℝ) (ht : t ∈ I) :
      0 < exitClockRate (toProjectiveState (normalizedMaxCurve x t₀ t)) := by
    obtain ⟨hm, hR, hu, hV, hw⟩ := hregion t ht
    have H := exitClockRate_compact hm hR hu ⟨hV.1.le, hV.2⟩ hw
    linarith only [H]
  obtain ⟨e, hsource, he, hconv, hzero, hinit, hmono, H⟩ :=
    exists_normalized_exitLog_reparametrization hI ho hs hdom hc hA hv hd
  refine ⟨e, hsource, he, hconv, hzero, hinit, hmono, ?_⟩
  intro z hz
  have ht : e.symm z ∈ I := hsource ▸ e.map_target hz
  obtain ⟨_, hval, hflow⟩ := H z hz
  have hM := (hregion (e.symm z) ht).1
  refine ⟨hval, ?_, ?_⟩
  · simpa only [hval] using hasDerivAt_toExitTailState hflow (hv _ ht) hM
  · rw [← hval]
    exact fromExitTailState_toExitTailState hM

end BianchiIX
