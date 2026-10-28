import BianchiIX.Algebra.StablePhaseResidual
import BianchiIX.Dynamics.StableBoundaryRegularity

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology

def stableCorrectedApproximation (y : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  let Y := stableBoundaryOrbit (y 0) (y 1) (y 2) t
  stableCorrectedPhase (Y 0) (Y 1) (Y 3)

def stableResidualIntegral (m u w T : ℝ) : ℝ :=
  ∫ t in 0..T, normalizedProjectiveRate (fromProjectiveState (stableBoundaryEntry m u w)) 0 t *
    stableCorrectedResidual (stableBoundaryOrbit m u w t 0)
      (stableBoundaryOrbit m u w t 1) (stableBoundaryOrbit m u w t 3)

theorem hasDerivAt_stableCorrectedPhase_scaled {Y : ℝ → ProjectiveState} {a t : ℝ}
    (hY : HasDerivAt Y (a • projectiveField (Y t)) t) (hm : 1 < Y t 0) (hv : Y t 2 = 0) :
    HasDerivAt (fun s => stableCorrectedPhase (Y s 0) (Y s 1) (Y s 3))
      (a * stableCorrectedResidual (Y t 0) (Y t 1) (Y t 3)) t := by
  have H := hasDerivAt_stableCorrectedPhase (hasDerivAt_pi.mp hY 0)
    (hasDerivAt_pi.mp hY 1) (hasDerivAt_pi.mp hY 3) hm
  convert! H using 1
  simp only [Pi.smul_apply, smul_eq_mul]
  change _ = _ * (a * phaseVelocity _ _ _ _) + _ * (a * strongVelocity _ _ _ _) + _ * (a * weakVelocity _ _ _ _)
  rw [hv, ← stableCorrectedPhase_directional hm]
  ring

theorem contDiffAt_stableCorrectedResidual (n : WithTop ℕ∞) {y : Fin 3 → ℝ}
    (hm : 1 < y 0) :
    ContDiffAt ℝ n (fun z : Fin 3 → ℝ => stableCorrectedResidual (z 0) (z 1) (z 2)) y := by
  have hL : y 0 + 1 ≠ 0 := by linarith
  have hD : y 0 ^ 2 - 1 ≠ 0 := by nlinarith
  have hD2 := pow_ne_zero 2 hD
  have hL2 := pow_ne_zero 2 hL
  have hR : Real.sqrt ((y 0 + 1) ^ 2 + y 2 ^ 2) ≠ 0 :=
    ne_of_gt (stableWeakRadius_pos (w := y 2) (by linarith : -1 < y 0))
  have hsum : Real.sqrt ((y 0 + 1) ^ 2 + y 2 ^ 2) + (y 0 + 1) ≠ 0 := by
    have H := Real.sqrt_nonneg ((y 0 + 1) ^ 2 + y 2 ^ 2)
    linarith
  have hS : (y 0 + 1) ^ 2 + y 2 ^ 2 ≠ 0 := by
    have h : 0 < y 0 + 1 := by linarith
    positivity
  have hprod := mul_ne_zero hR hsum
  unfold stableCorrectedResidual stableResidual4 stableResidual3 stableResidual2 stableResidual1
    stableWeakRadius phaseNorm
  fun_prop

theorem contDiffAt_stableCorrectedApproximation_two {y : Fin 3 → ℝ} {c t : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (ht : 0 ≤ t) :
    ContDiffAt ℝ 2 (fun z : (Fin 3 → ℝ) × ℝ => stableCorrectedApproximation z.1 z.2) (y, t) := by
  have H := contDiffAt_stableBoundaryOrbit_two hc hm hu hw ht
  let Y := stableBoundaryOrbit (y 0) (y 1) (y 2) t
  have hM : 1 < Y 0 := by
    have hband := (stableBoundaryOrbit_global hc hm hu hw t ht).2.1.1
    have hl := (abs_le.mp hband).1
    dsimp [Y]
    linarith
  have hcoords : ContDiffAt ℝ 2 (fun z : (Fin 3 → ℝ) × ℝ =>
      ![stableBoundaryOrbit (z.1 0) (z.1 1) (z.1 2) z.2 0,
        stableBoundaryOrbit (z.1 0) (z.1 1) (z.1 2) z.2 1,
        stableBoundaryOrbit (z.1 0) (z.1 1) (z.1 2) z.2 3]) (y, t) := by
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i
    · exact contDiffAt_pi.mp H 0
    · exact contDiffAt_pi.mp H 1
    · exact contDiffAt_pi.mp H 3
  have HC := (contDiffAt_stableCorrectedPhase 2 (y := ![Y 0, Y 1, Y 3]) hM).comp (y, t) hcoords
  exact HC

theorem stableCorrectedApproximation_tendsto {m c u w : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 40)
    (hu : |u| ≤ 1 / 200) (hw : |w| ≤ 1 / 200) :
    Tendsto (fun t => stableCorrectedApproximation ![m, u, w] t) atTop (𝓝 (stableBoundaryProjection m u w)) := by
  have H := stableBoundaryProjection_exists hc hm hu hw
  have hP : 1 < stableBoundaryProjection m u w := by
    have hband := (abs_le.mp (stableBoundaryProjection_band hc hm hu hw)).1
    linarith
  have hvec : Tendsto (fun t => ![stableBoundaryOrbit m u w t 0, stableBoundaryOrbit m u w t 1,
      stableBoundaryOrbit m u w t 3]) atTop (𝓝 (![stableBoundaryProjection m u w, 0, 0] : Fin 3 → ℝ)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    fin_cases i
    · exact H.1
    · exact H.2.1
    · exact H.2.2.1
  have hlim := (contDiffAt_stableCorrectedPhase 2 (y := ![stableBoundaryProjection m u w, 0, 0]) hP).continuousAt.tendsto.comp hvec
  change Tendsto (fun t => stableCorrectedApproximation ![m, u, w] t) atTop
    (𝓝 (stableCorrectedPhase (stableBoundaryProjection m u w) 0 0)) at hlim
  rw [stableCorrectedPhase_zero (by linarith : -1 ≤ stableBoundaryProjection m u w)] at hlim
  exact hlim

theorem stableResidualIntegral_eq {m c u w T : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 40)
    (hu : |u| ≤ 1 / 200) (hw : |w| ≤ 1 / 200) (hT : 0 ≤ T) :
    stableResidualIntegral m u w T = stableCorrectedApproximation ![m, u, w] T - stableCorrectedPhase m u w := by
  let Y := stableBoundaryOrbit m u w
  let a := normalizedProjectiveRate (fromProjectiveState (stableBoundaryEntry m u w)) 0
  have hM (t : ℝ) (ht : 0 ≤ t) : 1 < Y t 0 := by
    have hl := (abs_le.mp (stableBoundaryOrbit_global hc hm hu hw t ht).2.1.1).1
    linarith
  have hY (t : ℝ) (ht : 0 ≤ t) := hasDerivAt_stableBoundaryOrbit hc hm hu hw ht
  have hd (t : ℝ) (ht : 0 ≤ t) := hasDerivAt_stableCorrectedPhase_scaled
    (hY t ht) (hM t ht) (stableBoundaryOrbit_global hc hm hu hw t ht).2.1.2.2.1
  have hR : ContinuousOn (fun t => stableCorrectedResidual (Y t 0) (Y t 1) (Y t 3)) (Icc 0 T) := by
    intro t ht
    have hcoords : ContinuousAt (fun s => ![Y s 0, Y s 1, Y s 3]) t := by
      have H : ContinuousAt Y t := (hY t ht.1).continuousAt
      apply continuousAt_pi.mpr
      intro i
      fin_cases i
      · change ContinuousAt (fun s => Y s 0) t
        exact (continuous_apply 0).continuousAt.comp H
      · change ContinuousAt (fun s => Y s 1) t
        exact (continuous_apply 1).continuousAt.comp H
      · change ContinuousAt (fun s => Y s 3) t
        exact (continuous_apply 3).continuousAt.comp H
    have HC := (contDiffAt_stableCorrectedResidual 1 (y := ![Y t 0, Y t 1, Y t 3]) (hM t ht.1)).continuousAt.comp
      (f := fun s => ![Y s 0, Y s 1, Y s 3]) hcoords
    exact HC.continuousWithinAt
  have hx := fromProjectiveState_constraint (ne_of_gt (stableBoundaryEntry_denom_pos m u w))
  have ha : ContinuousOn a (Icc 0 T) := (continuousOn_normalizedProjectiveRate _ _).mono
    (fun t ht => normalizedMaxDomain_contains_Ici_of_constraint hx 0 ht.1)
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (show 0 ≤ t from (uIcc_of_le hT ▸ ht).1))
    ((ha.mul hR).intervalIntegrable_of_Icc hT)
  change stableResidualIntegral m u w T =
    stableCorrectedApproximation ![m, u, w] T - stableCorrectedPhase (Y 0 0) (Y 0 1) (Y 0 3) at H
  simpa [Y, stableBoundaryOrbit_initial, stableBoundaryEntry] using H

theorem stableResidualIntegral_tendsto {m c u w : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 40)
    (hu : |u| ≤ 1 / 200) (hw : |w| ≤ 1 / 200) :
    Tendsto (stableResidualIntegral m u w) atTop (𝓝 (stableBoundaryProjection m u w - stableCorrectedPhase m u w)) := by
  apply ((stableCorrectedApproximation_tendsto hc hm hu hw).sub_const (stableCorrectedPhase m u w)).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  exact (stableResidualIntegral_eq hc hm hu hw hT).symm

end BianchiIX
