import BianchiIX.Analysis.CompactIntegralRegularity
import BianchiIX.Dynamics.CoreMultipliers
import BianchiIX.Dynamics.ProjectiveFlowSecondRegularity

noncomputable section

namespace BianchiIX

open Set MeasureTheory

/-- Positive multipliers from an arbitrary projective initial point to its moving exit. -/
def partialCoreReturnMultiplier (τ : ProjectiveState → ℝ) (y : ProjectiveState) (i : Fin 2) : ℝ :=
  coreFlowMultiplier y 0 0 (τ y) i

theorem contDiffAt_projectiveCoreLogRates {y : ProjectiveState} {t₀ t : ℝ}
    (hD : 0 < projectiveStateDenom y)
    (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hV : 0 < projectiveOriginalFlow y t₀ t 2)
    (hDz : projectiveStateDenom (projectiveOriginalFlow y t₀ t) ≠ 0)
    (hd : let z := projectiveOriginalFlow y t₀ t
      coreClockFactor (coreRadius (z 0) (z 2)) (z 1) (z 3) ≠ 0) :
    ContDiffAt ℝ 1 (fun p : ProjectiveState × ℝ =>
      coreOriginalLogRates (projectiveOriginalFlow p.1 t₀ p.2)) (y, t) :=
  (contDiffAt_coreOriginalLogRates 1 hV hDz hd).comp (y, t) (g := coreOriginalLogRates)
    (f := fun p : ProjectiveState × ℝ => projectiveOriginalFlow p.1 t₀ p.2)
    ((contDiffAt_projectiveOriginalFlow_two hD ht hA).of_le (by norm_num))

/-- Compact joint regularity gives ordinary C1 logarithmic multipliers through either zero wall. -/
theorem contDiffAt_log_partialCoreReturnMultiplier {k : ℝ} {y : ProjectiveState}
    {τ : ProjectiveState → ℝ} (hk : 6 ≤ k) (hD : 0 < projectiveStateDenom y)
    (hτ : ContDiffAt ℝ 1 τ y) (hpos : 0 ≤ τ y)
    (hdom : Icc 0 (τ y) ⊆ normalizedMaxDomain (fromProjectiveState y) 0)
    (hA : ∀ t ∈ Icc 0 (τ y), 0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 t 0)
    (hcore : ∀ t ∈ Icc 0 (τ y), coreRegion k (projectiveOriginalFlow y 0 t))
    (i : Fin 2) : ContDiffAt ℝ 1 (fun z => Real.log (partialCoreReturnMultiplier τ z i)) y := by
  have hF (t : ℝ) (ht : t ∈ Icc 0 (τ y)) := contDiffAt_pi.mp
    (contDiffAt_projectiveCoreLogRates hD (hdom ht) (hA t ht)
      (zero_lt_one.trans_le (hcore t ht).2.1)
      (ne_of_gt (coreRegion_clock_regular hk (hcore t ht)).1)
      (ne_of_gt (coreRegion_clock_regular hk (hcore t ht)).2.1)) i
  convert! contDiffAt_moving_intervalIntegral_of_contDiffAt hτ hpos hF using 1
  ext z
  exact log_coreFlowMultiplier _ _ _ _ _

theorem contDiffAt_partialCoreReturnMultiplier {k : ℝ} {y : ProjectiveState}
    {τ : ProjectiveState → ℝ} (hk : 6 ≤ k) (hD : 0 < projectiveStateDenom y)
    (hτ : ContDiffAt ℝ 1 τ y) (hpos : 0 ≤ τ y)
    (hdom : Icc 0 (τ y) ⊆ normalizedMaxDomain (fromProjectiveState y) 0)
    (hA : ∀ t ∈ Icc 0 (τ y), 0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 t 0)
    (hcore : ∀ t ∈ Icc 0 (τ y), coreRegion k (projectiveOriginalFlow y 0 t))
    (i : Fin 2) : ContDiffAt ℝ 1 (fun z => partialCoreReturnMultiplier τ z i) y := by
  convert! (contDiffAt_log_partialCoreReturnMultiplier hk hD hτ hpos hdom hA hcore i).exp using 1
  ext z
  exact (Real.exp_log (coreFlowMultiplier_pos _ _ _ _ i)).symm

end BianchiIX
