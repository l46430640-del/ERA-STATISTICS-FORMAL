import BianchiIX.Algebra.RadialError
import BianchiIX.Dynamics.CoreRadialVariation
import BianchiIX.Dynamics.CoreRadiusPersistence

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- Formula (B.34) for the actual moving-exit map in incoming radius coordinates. -/
theorem exists_large_core_radius_arrival {Y : CoreAngleState} (hk : 6 ≤ Y 0)
    (hu : 0 ≤ Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0)
    (hw : 0 ≤ Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0) :
    ∃ T > 0, IsLeast {t | 0 < t ∧ projectiveOriginalFlow (coreRadiusEntry Y) 0 t 2 = 1} T ∧
      ∃ τ : CoreAngleState → ℝ, τ Y = T ∧ ContDiffAt ℝ 1 τ Y ∧
        (∀ᶠ Z in 𝓝 Y,
          IsLeast {t | 0 < t ∧ projectiveOriginalFlow (coreRadiusEntry Z) 0 t 2 = 1} (τ Z) ∧
            ∀ t ∈ Icc 0 (τ Z), t ∈ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry Z)) 0 ∧
              0 < 1 + normalizedMaxCurve (fromProjectiveState (coreRadiusEntry Z)) 0 t 0) ∧
        let F := fun Z => toCoreAngleState (projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z))
        ContDiffAt ℝ 1 F Y ∧ ∀ v : CoreAngleState,
          |(fderiv ℝ F Y v) 0 - v 0| ≤ (1040 + 512 * coreVariationBound) *
            (|v 1| / Y 0 + (Y 1 + Y 2) * (|v 0| + Y 0 * |v 1| + |v 2|) / Y 0) := by
  have hk0 : 0 < Y 0 := by linarith only [hk]
  have hD : 0 < projectiveStateDenom (coreRadiusEntry Y) :=
    (coreRegion_clock_regular hk (coreRadiusEntry_region hk hu hw)).1
  have hentry : ContDiffAt ℝ 1 coreRadiusEntry Y :=
    contDiffAt_coreRadiusEntry 1 (by linarith only [hk])
  obtain ⟨T, hT, hfirst, hpos, hle, herr, σ, hσ, hcσ, hhit, huniq, hcP, _, hderiv⟩ :=
    exists_large_core_exit_derivative hk hu hw
  obtain ⟨S, _, hfirstS, hrad⟩ := exists_large_core_radius_variation hk hu hw
  have hST : S = T := hfirstS.unique hfirst
  subst S
  obtain ⟨R, _, hfirstR, hcore, _⟩ := exists_large_core_traversal hk hu hw
  have hRT : R = T := hfirstR.unique hfirst
  subst R
  let τ := fun Z => σ (coreRadiusEntry Z)
  let F := fun Z => toCoreAngleState (projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z))
  have hcτ : ContDiffAt ℝ 1 τ Y := hcσ.comp Y hentry
  have hcF : ContDiffAt ℝ 1 F Y := by convert! hcP.comp Y hentry using 1
  have hhit' : ∀ᶠ Z in 𝓝 Y, τ Z ∈ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry Z)) 0 ∧
      0 < 1 + normalizedMaxCurve (fromProjectiveState (coreRadiusEntry Z)) 0 (τ Z) 0 ∧
      projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z) 2 = 1 :=
    hentry.continuousAt.tendsto.eventually hhit
  have hpair : ContinuousAt (fun q : CoreAngleState × ℝ => (coreRadiusEntry q.1, q.2)) (Y, T) := by
    convert! (hentry.continuousAt.comp
      (continuousAt_fst : ContinuousAt (Prod.fst : CoreAngleState × ℝ → CoreAngleState) (Y, T))).prodMk
        continuousAt_snd using 1
  have huniq' : ∀ᶠ q : CoreAngleState × ℝ in 𝓝 (Y, T),
      projectiveOriginalFlow (coreRadiusEntry q.1) 0 q.2 2 = 1 → τ q.1 = q.2 :=
    (hpair.eventually huniq).mono fun _ h => h.mp
  have hfirstNear := eventually_coreRadius_firstReturn hk hu hw hT hσ hcτ.continuousAt hfirst hcore
    (hhit'.mono fun _ h => h.2.2) huniq'
  refine ⟨T, hT, hfirst, τ, hσ, hcτ, hfirstNear, hcF, ?_⟩
  intro v
  let w := fderiv ℝ coreRadiusEntry Y v
  let ξ := fun t => coreProjectedFlowVariation (coreRadiusEntry Y) 0 t w
  let s := coreExitRadialFactor (projectiveOriginalFlow (coreRadiusEntry Y) 0 T)
  let Q₀ := |v 0| + Y 0 * |v 1| + |v 2|
  have hchain : HasFDerivAt F
      ((fderiv ℝ (fun z => toCoreAngleState (projectiveOriginalFlow z 0 (σ z))) (coreRadiusEntry Y)).comp
        (fderiv ℝ coreRadiusEntry Y)) Y := by
    convert! ((hcP.differentiableAt (by norm_num)).hasFDerivAt).comp Y
      ((hentry.differentiableAt (by norm_num)).hasFDerivAt) using 1
  have hout : (fderiv ℝ F Y v) 0 = s * ξ T 0 := by
    rw [hchain.fderiv, ContinuousLinearMap.comp_apply]
    exact (hderiv w).2.1
  have hinit : ξ 0 = coreClockProjection (coreRadiusEntry Y) w :=
    coreProjectedFlowVariation_initial hD 0 w
  obtain ⟨hR, hX, _⟩ := coreRadiusEntry_variation_bounds hk hu hw v
  have hR' : |ξ 0 0 - v 0| ≤ 4 * (Y 1 / Y 0 + Y 2 ^ 2 / Y 0 ^ 2) * |v 0| := by
    rw [hinit]
    exact hR
  have hX' : |Y 0 * ξ 0 1| ≤ Y 0 * |v 1| + 4 * Y 0 * Y 1 * |v 0| := by
    rw [hinit]
    exact hX
  have hQ : |v 0| ≤ Q₀ := by
    dsimp [Q₀]
    have H := mul_nonneg hk0.le (abs_nonneg (v 1))
    linarith only [H, abs_nonneg (v 2)]
  have hWk : Y 2 ≤ Y 0 := by
    have H := coreBootstrap_wall_bound hk hw.2
    linarith only [H, hk]
  have H := core_radius_arrival_error hk hu.1 hw.1 hWk hQ hpos.le hle herr hR' hX'
    (hrad v T ⟨hT.le, le_rfl⟩)
  rw [hout]
  apply H.trans
  have hK : 0 ≤ coreVariationBound := (Real.exp_pos _).le
  have hC : (256 : ℝ) ≤ 1040 + 512 * coreVariationBound := by linarith only [hK]
  calc
    _ = 256 * (|v 1| / Y 0) + (1040 + 512 * coreVariationBound) * ((Y 1 + Y 2) * Q₀ / Y 0) := by ring
    _ ≤ (1040 + 512 * coreVariationBound) * (|v 1| / Y 0) +
        (1040 + 512 * coreVariationBound) * ((Y 1 + Y 2) * Q₀ / Y 0) :=
      add_le_add (mul_le_mul_of_nonneg_right hC (div_nonneg (abs_nonneg _) hk0.le)) (le_refl _)
    _ = _ := by dsimp [Q₀]; ring

end BianchiIX
