import BianchiIX.Analysis.FirstReturnPersistence
import BianchiIX.Dynamics.PartialCoreMultiplierRegularity

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The integral factors describe the return map on an ordinary open germ, even at zero walls. -/
theorem eventually_partialCore_multiplier_formula {k : ℝ} {y : ProjectiveState}
    {τ : ProjectiveState → ℝ} (hk : 6 ≤ k) (hD : 0 < projectiveStateDenom y)
    (hτ : ContinuousAt τ y) (hpos : 0 < τ y)
    (hnear : ∀ᶠ x in 𝓝 y, ∀ t ∈ Icc 0 (τ x),
      t ∈ normalizedMaxDomain (fromProjectiveState x) 0 ∧
        0 < 1 + normalizedMaxCurve (fromProjectiveState x) 0 t 0)
    (hcore : ∀ t ∈ Icc 0 (τ y), coreRegion k (projectiveOriginalFlow y 0 t))
    (hhit : ∀ᶠ x in 𝓝 y, projectiveOriginalFlow x 0 (τ x) 2 = 1) :
    ∀ᶠ x in 𝓝 y,
      projectiveOriginalFlow x 0 (τ x) 1 = x 1 * partialCoreReturnMultiplier τ x 0 ∧
      projectiveOriginalFlow x 0 (τ x) 3 = (x 2 * x 3) * partialCoreReturnMultiplier τ x 1 := by
  have hbase := hnear.self_of_nhds
  have htube : ∀ᶠ x in 𝓝 y, ∀ t ∈ Icc 0 (τ x),
      let z := projectiveOriginalFlow x 0 t
      0 < z 2 ∧ projectiveStateDenom z ≠ 0 ∧
        coreClockFactor (coreRadius (z 0) (z 2)) (z 1) (z 3) ≠ 0 := by
    apply eventually_forall_movingInterval hτ hpos
    intro t ht
    have hreg := coreRegion_clock_regular hk (hcore t ht)
    have hv := zero_lt_one.trans_le (hcore t ht).2.1
    have hf := (contDiffAt_projectiveOriginalFlow_two hD (hbase t ht).1 (hbase t ht).2).continuousAt
    have hV := (continuousAt_pi.mp hf 2).eventually (isOpen_Ioi.mem_nhds hv)
    have hden : ∀ᶠ p : ProjectiveState × ℝ in 𝓝 (y, t),
        0 < projectiveStateDenom (projectiveOriginalFlow p.1 0 p.2) :=
      (continuous_projectiveStateDenom.continuousAt.comp hf).eventually (isOpen_Ioi.mem_nhds hreg.1)
    have hfactor : ContinuousAt (fun z : ProjectiveState =>
        coreClockFactor (coreRadius (z 0) (z 2)) (z 1) (z 3)) (projectiveOriginalFlow y 0 t) :=
      (contDiffAt_projectiveCoreClockFactor 1 hv).continuousAt
    have hclockCont : ContinuousAt (fun p : ProjectiveState × ℝ =>
        let z := projectiveOriginalFlow p.1 0 p.2
        coreClockFactor (coreRadius (z 0) (z 2)) (z 1) (z 3)) (y, t) :=
      ContinuousAt.comp (f := fun p : ProjectiveState × ℝ => projectiveOriginalFlow p.1 0 p.2)
        (g := fun z : ProjectiveState => coreClockFactor (coreRadius (z 0) (z 2)) (z 1) (z 3)) hfactor hf
    have hclock : ∀ᶠ p : ProjectiveState × ℝ in 𝓝 (y, t),
        let z := projectiveOriginalFlow p.1 0 p.2
        0 < coreClockFactor (coreRadius (z 0) (z 2)) (z 1) (z 3) :=
      hclockCont.eventually (isOpen_Ioi.mem_nhds hreg.2.1)
    filter_upwards [hV, hden, hclock] with p hpV hpD hpclock
    exact ⟨hpV, ne_of_gt hpD, ne_of_gt hpclock⟩
  have hden := continuous_projectiveStateDenom.continuousAt.eventually (isOpen_Ioi.mem_nhds hD)
  have hpositive := hτ.eventually (isOpen_Ioi.mem_nhds hpos)
  filter_upwards [hnear, htube, hden, hpositive, hhit] with x hx hreg hDx hτx hhitx
  have H := projectiveOriginalFlow_core_multipliers_of_regular hτx.le hDx
    (fun t ht => (hx t ht).1) (fun t ht => (hx t ht).2) hreg
  dsimp only at H
  rw [projectiveOriginalFlow_initial hDx, hhitx] at H
  simpa only [one_mul, partialCoreReturnMultiplier] using H

end BianchiIX
