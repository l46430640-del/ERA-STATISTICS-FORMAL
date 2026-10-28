import BianchiIX.Analysis.CompactParametricIntegral
import BianchiIX.Dynamics.CoreMultipliers
import BianchiIX.Dynamics.CoreRadiusArrival

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology

def coreReturnMultiplier (τ : CoreAngleState → ℝ) (Y : CoreAngleState) (i : Fin 2) : ℝ :=
  coreFlowMultiplier (coreRadiusEntry Y) 0 0 (τ Y) i

def coreRescaledLogRate (τ : CoreAngleState → ℝ) (i : Fin 2) (p : CoreAngleState × ℝ) : ℝ :=
  τ p.1 * coreOriginalLogRates (projectiveOriginalFlow (coreRadiusEntry p.1) 0 (p.2 * τ p.1)) i

theorem contDiffAt_coreRadius_flow {Y : CoreAngleState} {t : ℝ}
    (hk : 1 < Y 0) (hD : 0 < projectiveStateDenom (coreRadiusEntry Y))
    (ht : t ∈ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry Y)) 0)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState (coreRadiusEntry Y)) 0 t 0) :
    ContDiffAt ℝ 1 (fun p : CoreAngleState × ℝ => projectiveOriginalFlow (coreRadiusEntry p.1) 0 p.2)
      (Y, t) := by
  have he := (contDiffAt_fromProjectiveState 1 (ne_of_gt hD)).comp Y (contDiffAt_coreRadiusEntry 1 hk)
  have hp : ContDiffAt ℝ 1 (fun p : CoreAngleState × ℝ =>
      (fromProjectiveState (coreRadiusEntry p.1), p.2)) (Y, t) :=
    (he.comp (Y, t) contDiffAt_fst).prodMk contDiffAt_snd
  have hf := (normalizedMaxCurve_regular ht).2.comp (Y, t)
    (g := fun p : NormalizedState × ℝ => normalizedMaxCurve p.1 0 p.2)
    (f := fun p : CoreAngleState × ℝ => (fromProjectiveState (coreRadiusEntry p.1), p.2)) hp
  exact (contDiffAt_toProjectiveState 1 (ne_of_gt hA)).comp (Y, t) hf

/-- The endpoint motion is included in the derivative of the rescaled integrand. -/
theorem hasFDerivAt_log_coreReturnMultiplier {Y : CoreAngleState} {τ : CoreAngleState → ℝ}
    (hk : 6 ≤ Y 0) (hD : 0 < projectiveStateDenom (coreRadiusEntry Y))
    (hτ : ContDiffAt ℝ 1 τ Y) (hpos : 0 ≤ τ Y)
    (hdom : Icc 0 (τ Y) ⊆ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry Y)) 0)
    (hA : ∀ t ∈ Icc 0 (τ Y), 0 < 1 + normalizedMaxCurve (fromProjectiveState (coreRadiusEntry Y)) 0 t 0)
    (hcore : ∀ t ∈ Icc 0 (τ Y), coreRegion (Y 0) (projectiveOriginalFlow (coreRadiusEntry Y) 0 t))
    (i : Fin 2) :
    HasFDerivAt (fun Z => Real.log (coreReturnMultiplier τ Z i))
      (∫ s in (0 : ℝ)..1, (fderiv ℝ (coreRescaledLogRate τ i) (Y, s)).comp
        (ContinuousLinearMap.inl ℝ CoreAngleState ℝ)) Y := by
  have hF (t : ℝ) (ht : t ∈ Icc 0 (τ Y)) :
      ContDiffAt ℝ 1 (fun p : CoreAngleState × ℝ =>
        coreOriginalLogRates (projectiveOriginalFlow (coreRadiusEntry p.1) 0 p.2) i) (Y, t) := by
    have hreg := coreRegion_clock_regular hk (hcore t ht)
    have hc := contDiffAt_coreOriginalLogRates 1 (lt_of_lt_of_le zero_lt_one (hcore t ht).2.1)
      (ne_of_gt hreg.1) (ne_of_gt hreg.2.1)
    have hf := contDiffAt_coreRadius_flow (by linarith only [hk]) hD (hdom ht) (hA t ht)
    exact contDiffAt_pi.mp (hc.comp (Y, t) hf) i
  convert! hasFDerivAt_moving_intervalIntegral_of_contDiffAt hτ hpos hF using 1
  ext Z
  exact log_coreFlowMultiplier _ _ _ _ _

theorem eventually_coreRadius_multiplier_formula {Y : CoreAngleState} {τ : CoreAngleState → ℝ}
    (hk : 6 ≤ Y 0) (hD : 0 < projectiveStateDenom (coreRadiusEntry Y))
    (hτ : ContinuousAt τ Y) (hpos : 0 < τ Y)
    (hdom : Icc 0 (τ Y) ⊆ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry Y)) 0)
    (hA : ∀ t ∈ Icc 0 (τ Y), 0 < 1 + normalizedMaxCurve (fromProjectiveState (coreRadiusEntry Y)) 0 t 0)
    (hcore : ∀ t ∈ Icc 0 (τ Y), coreRegion (Y 0) (projectiveOriginalFlow (coreRadiusEntry Y) 0 t))
    (hhit : ∀ᶠ Z in 𝓝 Y, projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z) 2 = 1) :
    ∀ᶠ Z in 𝓝 Y,
      projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z) 1 = Z 1 * coreReturnMultiplier τ Z 0 ∧
      projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z) 3 = Z 2 * coreReturnMultiplier τ Z 1 := by
  have htube : ∀ᶠ Z in 𝓝 Y, ∀ t ∈ Icc 0 (τ Z),
      t ∈ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry Z)) 0 ∧
      0 < 1 + normalizedMaxCurve (fromProjectiveState (coreRadiusEntry Z)) 0 t 0 ∧
      let z := projectiveOriginalFlow (coreRadiusEntry Z) 0 t
      0 < z 2 ∧ projectiveStateDenom z ≠ 0 ∧
        coreClockFactor (coreRadius (z 0) (z 2)) (z 1) (z 3) ≠ 0 := by
    apply eventually_forall_movingInterval hτ hpos
    intro t ht
    have hreg := coreRegion_clock_regular hk (hcore t ht)
    have hv := lt_of_lt_of_le zero_lt_one (hcore t ht).2.1
    obtain ⟨hnear, hf⟩ := coreRadius_flow_regular (by linarith only [hk]) hD (hdom ht) (hA t ht)
    have hV := (continuousAt_pi.mp hf 2).eventually (isOpen_Ioi.mem_nhds hv)
    have hden : ∀ᶠ p : CoreAngleState × ℝ in 𝓝 (Y, t),
        0 < projectiveStateDenom (projectiveOriginalFlow (coreRadiusEntry p.1) 0 p.2) :=
      (continuous_projectiveStateDenom.continuousAt.comp hf).eventually (isOpen_Ioi.mem_nhds hreg.1)
    have hfactor : ContinuousAt (fun z : ProjectiveState =>
        coreClockFactor (coreRadius (z 0) (z 2)) (z 1) (z 3))
        (projectiveOriginalFlow (coreRadiusEntry Y) 0 t) :=
      (contDiffAt_projectiveCoreClockFactor 1 hv).continuousAt
    have hclockCont : ContinuousAt (fun p : CoreAngleState × ℝ =>
        let z := projectiveOriginalFlow (coreRadiusEntry p.1) 0 p.2
        coreClockFactor (coreRadius (z 0) (z 2)) (z 1) (z 3)) (Y, t) :=
      ContinuousAt.comp (f := fun p : CoreAngleState × ℝ =>
        projectiveOriginalFlow (coreRadiusEntry p.1) 0 p.2)
        (g := fun z : ProjectiveState => coreClockFactor (coreRadius (z 0) (z 2)) (z 1) (z 3)) hfactor hf
    have hclock : ∀ᶠ p : CoreAngleState × ℝ in 𝓝 (Y, t),
        let z := projectiveOriginalFlow (coreRadiusEntry p.1) 0 p.2
        0 < coreClockFactor (coreRadius (z 0) (z 2)) (z 1) (z 3) :=
      hclockCont.eventually (isOpen_Ioi.mem_nhds hreg.2.1)
    filter_upwards [hnear, hV, hden, hclock] with p hp hpV hpD hpclock
    exact ⟨hp.1, hp.2, hpV, ne_of_gt hpD, ne_of_gt hpclock⟩
  have hentry := (contDiffAt_coreRadiusEntry 1 (by linarith only [hk])).continuousAt
  have hden := (continuous_projectiveStateDenom.continuousAt.comp hentry).eventually
    (isOpen_Ioi.mem_nhds hD)
  have hpositive := hτ.eventually (isOpen_Ioi.mem_nhds hpos)
  filter_upwards [htube, hden, hpositive, hhit] with Z hZ hDZ hτZ hhitZ
  have H := projectiveOriginalFlow_core_multipliers_of_regular hτZ.le hDZ
    (fun t ht => (hZ t ht).1) (fun t ht => (hZ t ht).2.1) (fun t ht => (hZ t ht).2.2)
  dsimp only at H
  rw [projectiveOriginalFlow_initial hDZ, hhitZ] at H
  simpa [coreRadiusEntry, coreReturnMultiplier] using H

/-- Differentiable positive factors for the genuine first-return map on an open neighborhood. -/
theorem exists_large_core_multiplier_differential {Y : CoreAngleState} (hk : 6 ≤ Y 0)
    (hu : 0 ≤ Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0)
    (hw : 0 ≤ Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0) :
    ∃ τ : CoreAngleState → ℝ, 0 < τ Y ∧ ContDiffAt ℝ 1 τ Y ∧
      (∀ᶠ Z in 𝓝 Y,
        IsLeast {t | 0 < t ∧ projectiveOriginalFlow (coreRadiusEntry Z) 0 t 2 = 1} (τ Z) ∧
        projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z) 1 = Z 1 * coreReturnMultiplier τ Z 0 ∧
        projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z) 3 = Z 2 * coreReturnMultiplier τ Z 1) ∧
      ∀ i : Fin 2,
        0 < coreReturnMultiplier τ Y i ∧
        HasFDerivAt (fun Z => Real.log (coreReturnMultiplier τ Z i))
          (∫ s in (0 : ℝ)..1, (fderiv ℝ (coreRescaledLogRate τ i) (Y, s)).comp
            (ContinuousLinearMap.inl ℝ CoreAngleState ℝ)) Y ∧
        HasFDerivAt (fun Z => coreReturnMultiplier τ Z i)
          (coreReturnMultiplier τ Y i •
            ∫ s in (0 : ℝ)..1, (fderiv ℝ (coreRescaledLogRate τ i) (Y, s)).comp
              (ContinuousLinearMap.inl ℝ CoreAngleState ℝ)) Y := by
  have hD := (coreRegion_clock_regular hk (coreRadiusEntry_region hk hu hw)).1
  have hc := fromProjectiveState_constraint (ne_of_gt hD)
  obtain ⟨T, hT, hfirst, τ, hτ, hcτ, hnear, _⟩ := exists_large_core_radius_arrival hk hu hw
  obtain ⟨S, _, hfirstS, hcore, _⟩ := exists_large_core_traversal hk hu hw
  have hST : S = T := hfirstS.unique hfirst
  subst S
  have hpos : 0 < τ Y := hτ ▸ hT
  have hdom : Icc 0 (τ Y) ⊆ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry Y)) 0 :=
    fun t ht => normalizedMaxDomain_contains_Ici_of_constraint hc 0 ht.1
  have hA : ∀ t ∈ Icc 0 (τ Y), 0 < 1 + normalizedMaxCurve (fromProjectiveState (coreRadiusEntry Y)) 0 t 0 :=
    fun t ht => (hcore t (hτ ▸ ht)).1
  have hregion : ∀ t ∈ Icc 0 (τ Y), coreRegion (Y 0) (projectiveOriginalFlow (coreRadiusEntry Y) 0 t) :=
    fun t ht => (hcore t (hτ ▸ ht)).2
  have hformula := eventually_coreRadius_multiplier_formula hk hD hcτ.continuousAt hpos hdom hA hregion
    (hnear.mono fun _ h => h.1.1.2)
  refine ⟨τ, hpos, hcτ, ?_, ?_⟩
  · filter_upwards [hnear, hformula] with Z hZ hf
    exact ⟨hZ.1, hf⟩
  · intro i
    have H := hasFDerivAt_log_coreReturnMultiplier hk hD hcτ hpos.le hdom hA hregion i
    refine ⟨coreFlowMultiplier_pos _ _ _ _ i, H, ?_⟩
    convert! H.exp using 1
    · ext Z
      exact (Real.exp_log (coreFlowMultiplier_pos _ _ _ _ i)).symm
    · rw [Real.exp_log (show 0 < coreReturnMultiplier τ Y i from coreFlowMultiplier_pos _ _ _ _ i)]

end BianchiIX
