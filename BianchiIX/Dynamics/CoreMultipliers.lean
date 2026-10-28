import BianchiIX.Analysis.ScalarMultiplier
import BianchiIX.Dynamics.CoreLogRateVariation

noncomputable section

namespace BianchiIX

open Set MeasureTheory

/-- The two logarithmic rates in the original normalized Einstein time. -/
def coreOriginalLogRates (y : ProjectiveState) : Fin 2 → ℝ :=
  coreOriginalClockRate y • coreLogRates (projectiveCoreAngle y) (toCoreAngleState y)

/-- Positive transverse factors defined without dividing by an entrance wall. -/
def coreFlowMultiplier (y : ProjectiveState) (t₀ a b : ℝ) (i : Fin 2) : ℝ :=
  Real.exp (∫ t in a..b, coreOriginalLogRates (projectiveOriginalFlow y t₀ t) i)

theorem contDiffAt_coreOriginalLogRates (n : WithTop ℕ∞) {y : ProjectiveState}
    (hv : 0 < y 2) (hD : projectiveStateDenom y ≠ 0)
    (hd : coreClockFactor (coreRadius (y 0) (y 2)) (y 1) (y 3) ≠ 0) :
    ContDiffAt ℝ n coreOriginalLogRates y := by
  have hq : coreAuxiliary (projectiveCoreAngle y) (toCoreAngleState y) 1 ≠ 0 := by
    rwa [coreAuxiliary_projective_clockFactor hv]
  have hpair := (contDiffAt_projectiveCoreAngle n hv).prodMk
    (contDiffAt_toCoreAngleState n hv)
  have hlog : ContDiffAt ℝ n (fun p : ℝ × CoreAngleState => coreLogRates p.1 p.2)
      (projectiveCoreAngle y, toCoreAngleState y) :=
    contDiffAt_coreLogRates_joint n _ (ne_of_gt (coreRadius_pos hv)) hq
  have hcomp := hlog.comp y (g := fun p : ℝ × CoreAngleState => coreLogRates p.1 p.2)
    (f := fun z : ProjectiveState => (projectiveCoreAngle z, toCoreAngleState z)) hpair
  exact (contDiffAt_coreOriginalClockRate n hv hD).smul hcomp

theorem coreFlowMultiplier_pos (y : ProjectiveState) (t₀ a b : ℝ) (i : Fin 2) :
    0 < coreFlowMultiplier y t₀ a b i := Real.exp_pos _

theorem log_coreFlowMultiplier (y : ProjectiveState) (t₀ a b : ℝ) (i : Fin 2) :
    Real.log (coreFlowMultiplier y t₀ a b i) =
      ∫ t in a..b, coreOriginalLogRates (projectiveOriginalFlow y t₀ t) i :=
  Real.log_exp _

theorem projectiveOriginalFlow_core_multipliers_of_regular {y : ProjectiveState} {t₀ a b : ℝ}
    (hab : a ≤ b) (hD : 0 < projectiveStateDenom y)
    (hdom : Icc a b ⊆ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : ∀ t ∈ Icc a b, 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hreg : ∀ t ∈ Icc a b, let z := projectiveOriginalFlow y t₀ t
      0 < z 2 ∧ projectiveStateDenom z ≠ 0 ∧
        coreClockFactor (coreRadius (z 0) (z 2)) (z 1) (z 3) ≠ 0) :
    let β := projectiveOriginalFlow y t₀
    β b 1 = β a 1 * coreFlowMultiplier y t₀ a b 0 ∧
      β b 2 * β b 3 = (β a 2 * β a 3) * coreFlowMultiplier y t₀ a b 1 := by
  intro β
  have hflow (t : ℝ) (ht : t ∈ Icc a b) :=
    hasDerivAt_projectiveOriginalFlow_time hD (hdom ht) (hA t ht)
  have hc (i : Fin 4) : ContinuousOn (fun t => β t i) (Icc a b) :=
    fun t ht => (hasDerivAt_pi.mp (hflow t ht) i).continuousAt.continuousWithinAt
  have hr : ContinuousOn (fun t => coreOriginalLogRates (β t)) (Icc a b) := by
    intro t ht
    have hrate := contDiffAt_coreOriginalLogRates 1 (hreg t ht).1 (hreg t ht).2.1 (hreg t ht).2.2
    exact (hrate.continuousAt.comp (hflow t ht).continuousAt).continuousWithinAt
  have hderiv (t : ℝ) (ht : t ∈ Ioo a b) :=
    hasDerivAt_toCoreAngleState_scaled (hflow t (Ioo_subset_Icc_self ht))
      (hreg t (Ioo_subset_Icc_self ht)).1 (hreg t (Ioo_subset_Icc_self ht)).2.2
  have hcoef (t : ℝ) := coreAngleField_log_rates (projectiveCoreAngle (β t)) (toCoreAngleState (β t))
  constructor
  · apply homogeneous_solution_eq_exp_integral_Icc hab (continuousOn_pi.mp hr 0) (hc 1)
    intro t ht
    apply (hasDerivAt_pi.mp (hderiv t ht) 1).congr_deriv
    change coreOriginalClockRate (β t) * coreAngleField (projectiveCoreAngle (β t)) (toCoreAngleState (β t)) 1 = _
    rw [(hcoef t).1]
    dsimp [coreOriginalLogRates, toCoreAngleState]
    ring
  · apply homogeneous_solution_eq_exp_integral_Icc hab (continuousOn_pi.mp hr 1) ((hc 2).mul (hc 3))
    intro t ht
    apply (hasDerivAt_pi.mp (hderiv t ht) 2).congr_deriv
    change coreOriginalClockRate (β t) * coreAngleField (projectiveCoreAngle (β t)) (toCoreAngleState (β t)) 2 = _
    rw [(hcoef t).2]
    dsimp [coreOriginalLogRates, toCoreAngleState]
    ring

theorem continuousOn_coreFlow_log_rates {y : ProjectiveState} {t₀ k a b : ℝ}
    (hk : 6 ≤ k) (hD : 0 < projectiveStateDenom y)
    (hdom : Icc a b ⊆ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : ∀ t ∈ Icc a b, 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hcore : ∀ t ∈ Icc a b, coreRegion k (projectiveOriginalFlow y t₀ t)) :
    ContinuousOn (fun t => coreOriginalLogRates (projectiveOriginalFlow y t₀ t)) (Icc a b) := by
  intro t ht
  have hv := lt_of_lt_of_le zero_lt_one (hcore t ht).2.1
  have hreg := coreRegion_clock_regular hk (hcore t ht)
  exact ((contDiffAt_coreOriginalLogRates 1 hv (ne_of_gt hreg.1) (ne_of_gt hreg.2.1)).continuousAt.comp
    (hasDerivAt_projectiveOriginalFlow_time hD (hdom ht) (hA t ht)).continuousAt).continuousWithinAt

theorem projectiveOriginalFlow_core_multipliers {y : ProjectiveState} {t₀ k a b : ℝ}
    (hk : 6 ≤ k) (hab : a ≤ b) (hD : 0 < projectiveStateDenom y)
    (hdom : Icc a b ⊆ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : ∀ t ∈ Icc a b, 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hcore : ∀ t ∈ Icc a b, coreRegion k (projectiveOriginalFlow y t₀ t)) :
    let β := projectiveOriginalFlow y t₀
    β b 1 = β a 1 * coreFlowMultiplier y t₀ a b 0 ∧
      β b 2 * β b 3 = (β a 2 * β a 3) * coreFlowMultiplier y t₀ a b 1 := by
  apply projectiveOriginalFlow_core_multipliers_of_regular hab hD hdom hA
  intro t ht
  have hreg := coreRegion_clock_regular hk (hcore t ht)
  exact ⟨lt_of_lt_of_le zero_lt_one (hcore t ht).2.1, ne_of_gt hreg.1, ne_of_gt hreg.2.1⟩

/-- The factors represent the actual first return even when either entrance wall vanishes. -/
theorem exists_large_core_multipliers {Y : CoreAngleState} (hk : 6 ≤ Y 0)
    (hu : 0 ≤ Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0)
    (hw : 0 ≤ Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0) :
    ∃ T > 0, IsLeast {t | 0 < t ∧ projectiveOriginalFlow (coreRadiusEntry Y) 0 t 2 = 1} T ∧
      let A := coreFlowMultiplier (coreRadiusEntry Y) 0 0 T
      let β := projectiveOriginalFlow (coreRadiusEntry Y) 0
      (∀ i, 0 < A i) ∧ β T 1 = Y 1 * A 0 ∧ β T 3 = Y 2 * A 1 := by
  have hD : 0 < projectiveStateDenom (coreRadiusEntry Y) :=
    (coreRegion_clock_regular hk (coreRadiusEntry_region hk hu hw)).1
  have hc := fromProjectiveState_constraint (ne_of_gt hD)
  obtain ⟨T, hT, hfirst, hcore, _⟩ := exists_large_core_traversal hk hu hw
  refine ⟨T, hT, hfirst, fun i => coreFlowMultiplier_pos _ _ _ _ i, ?_⟩
  have H := projectiveOriginalFlow_core_multipliers hk hT.le hD
    (fun s hs => normalizedMaxDomain_contains_Ici_of_constraint hc 0 hs.1)
    (fun s hs => (hcore s hs).1) (fun s hs => (hcore s hs).2)
  dsimp only at H
  have hreturn : projectiveOriginalFlow (coreRadiusEntry Y) 0 T 2 = 1 := hfirst.1.2
  rw [projectiveOriginalFlow_initial hD, hreturn] at H
  simpa [coreRadiusEntry] using H

end BianchiIX
