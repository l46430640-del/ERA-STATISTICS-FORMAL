import BianchiIX.Dynamics.CoreSectionDifferential

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def projectiveWallArrivalDifferential (y : ProjectiveState) (t₀ t : ℝ) :
    ProjectiveState →L[ℝ] ProjectiveState :=
  (fderiv ℝ toProjectiveState (normalizedMaxCurve (fromProjectiveState y) t₀ t)).comp
    ((normalizedEventDifferential projectiveActiveWall (fromProjectiveState y) t₀ t).comp
      (fderiv ℝ fromProjectiveState y))

/-- The constant active-wall event, in projective initial coordinates, uses the actual flow. -/
theorem exists_projectiveWall_event {y : ProjectiveState} {t₀ t : ℝ}
    (hD : 0 < projectiveStateDenom y) (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hv : projectiveField (projectiveOriginalFlow y t₀ t) 2 ≠ 0) :
    ∃ τ : ProjectiveState → ℝ, τ y = t ∧ ContDiffAt ℝ 1 τ y ∧
      (∀ᶠ z in 𝓝 y, τ z ∈ normalizedMaxDomain (fromProjectiveState z) t₀ ∧
        0 < 1 + normalizedMaxCurve (fromProjectiveState z) t₀ (τ z) 0 ∧
        projectiveOriginalFlow z t₀ (τ z) 2 = projectiveOriginalFlow y t₀ t 2) ∧
      (∀ᶠ z : ProjectiveState × ℝ in 𝓝 (y, t),
        z.2 ∈ normalizedMaxDomain (fromProjectiveState z.1) t₀ ∧
        (projectiveOriginalFlow z.1 t₀ z.2 2 = projectiveOriginalFlow y t₀ t 2 ↔ τ z.1 = z.2)) ∧
      ContDiffAt ℝ 1 (fun z => projectiveOriginalFlow z t₀ (τ z)) y ∧
      HasFDerivAt (fun z => projectiveOriginalFlow z t₀ (τ z))
        (projectiveWallArrivalDifferential y t₀ t) y := by
  let x := fromProjectiveState y
  let X := normalizedMaxCurve x t₀ t
  have hc : stateConstraint X = 1 :=
    (normalizedMaxCurve_constraint ht).trans (fromProjectiveState_constraint (ne_of_gt hD))
  have htrans : normalizedEventRate projectiveActiveWall x t₀ t ≠ 0 := by
    change fderiv ℝ projectiveActiveWall X (normalizedField X) ≠ 0
    rw [projectiveActiveWall_fderiv_field (ne_of_gt hA) hc]
    exact mul_ne_zero (ne_of_gt hA) hv
  obtain ⟨tau, hinit, hctau, _, hhit, huniq, hcmap, hdmap⟩ :=
    exists_normalized_event ht (contDiffAt_projectiveActiveWall 1 (ne_of_gt hA)) htrans
  let τ : ProjectiveState → ℝ := fun z => tau (fromProjectiveState z)
  have hfrom := contDiffAt_fromProjectiveState 1 (ne_of_gt hD)
  have hfrom' := (hfrom.differentiableAt (by norm_num)).hasFDerivAt
  have hτ : τ y = t := hinit
  let eta : ProjectiveState → NormalizedState := fun z => normalizedMaxCurve (fromProjectiveState z) t₀ (τ z)
  have hceta : ContDiffAt ℝ 1 eta y := hcmap.comp y hfrom
  have heta : eta y = X := by change normalizedMaxCurve x t₀ (τ y) = X; rw [hτ]
  have hto : ContDiffAt ℝ 1 toProjectiveState (eta y) := by
    rw [heta]
    exact contDiffAt_toProjectiveState 1 (ne_of_gt hA)
  have hAnear : ∀ᶠ z in 𝓝 y, 0 < 1 + eta z 0 := by
    have H : ContinuousAt (fun z => 1 + eta z 0) y :=
      continuousAt_const.add ((continuous_apply 0).continuousAt.comp hceta.continuousAt)
    apply H.eventually (isOpen_Ioi.mem_nhds ?_)
    change 0 < 1 + eta y 0
    rw [heta]
    exact hA
  refine ⟨τ, hτ, hctau.comp y hfrom, ?_, ?_, hto.comp y hceta, ?_⟩
  · filter_upwards [hfrom.continuousAt.eventually hhit, hAnear] with z hz hAz
    exact ⟨hz.1, hAz, hz.2⟩
  · have hfamily : ContinuousAt (fun z : ProjectiveState × ℝ => (fromProjectiveState z.1, z.2))
        (y, t) := by
      convert! (hfrom.continuousAt.comp
        (continuousAt_fst : ContinuousAt (Prod.fst : ProjectiveState × ℝ → ProjectiveState) (y, t))).prodMk
          continuousAt_snd using 1
    exact hfamily.eventually huniq
  · have H := ((hto.differentiableAt (by norm_num)).hasFDerivAt).comp y (hdmap.comp y hfrom')
    rw [heta] at H
    convert! H using 1

theorem coreRegion_exit_transverse {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hV : y 2 = 1) (hM : y 0 < 1) :
    projectiveField y 2 < 0 ∧
      -Real.tanh (projectiveCoreAngle y) +
        coreAngleField (projectiveCoreAngle y) (toCoreAngleState y) 0 / coreRadius (y 0) (y 2) < 0 := by
  have hv : 0 < y 2 := by rw [hV]; norm_num
  obtain ⟨hu, hw⟩ := coreRegion_wall_bounds hy
  have hC := coreBootstrap_coupling_nonneg hk hy.2.1 hu hw.1
  have hf := (coreRegion_exit_radius_velocity hk hy hV hM).1
  have hr := coreRadius_pos (m := y 0) hv
  constructor
  · change (y 0 - 1 - coupling (y 1) (y 2) (y 3)) * y 2 < 0
    exact mul_neg_of_neg_of_pos (by linarith only [hM, hC]) hv
  · have hz : 0 < Real.tanh (projectiveCoreAngle y) := by
      rw [projectiveCoreAngle, tanh_coreAngle hv]
      exact div_pos (sub_pos.mpr hM) hr
    exact add_neg_of_neg_of_nonpos (neg_neg_of_pos hz) (div_nonpos_of_nonpos_of_nonneg hf hr.le)

/-- The event derivative and the fixed-angle variation give exactly the exit factor in (B.38). -/
theorem coreWallArrivalDifferential_correction {k : ℝ} {y : ProjectiveState} {t₀ t : ℝ}
    (hk : 6 ≤ k) (hD : 0 < projectiveStateDenom y)
    (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hy : coreRegion k (projectiveOriginalFlow y t₀ t))
    (hV : projectiveOriginalFlow y t₀ t 2 = 1) (hM : projectiveOriginalFlow y t₀ t 0 < 1)
    (w : ProjectiveState) :
    let b := projectiveOriginalFlow y t₀ t
    let q := coreProjectedFlowVariation y t₀ t w 0
    fderiv ℝ projectiveCoreAngle b (projectiveWallArrivalDifferential y t₀ t w) =
        -q / (coreRadius (b 0) (b 2) * (-Real.tanh (projectiveCoreAngle b) +
          coreAngleField (projectiveCoreAngle b) (toCoreAngleState b) 0 / coreRadius (b 0) (b 2))) ∧
      (fderiv ℝ toCoreAngleState b (projectiveWallArrivalDifferential y t₀ t w)) 0 =
        coreExitRadialFactor b * q := by
  intro b q
  have hc : stateConstraint (normalizedMaxCurve (fromProjectiveState y) t₀ t) = 1 :=
    (normalizedMaxCurve_constraint ht).trans (fromProjectiveState_constraint (ne_of_gt hD))
  have hv : 0 < b 2 := by change 0 < projectiveOriginalFlow y t₀ t 2; rw [hV]; norm_num
  have hreg := coreRegion_exit_transverse hk hy hV hM
  have hd := (coreRegion_clock_regular hk hy).2.1
  have H := coreWall_event_projection (ne_of_gt hA) hc hv (ne_of_gt hd) (ne_of_lt hreg.1)
    (fderiv ℝ fromProjectiveState y w)
  change (projectiveWallArrivalDifferential y t₀ t w) 2 = 0 ∧
    coreClockProjection b (projectiveWallArrivalDifferential y t₀ t w) =
      coreProjectedFlowVariation y t₀ t w at H
  have H' := core_section_tangent_correction hv (ne_of_lt hreg.2)
    (projectiveWallArrivalDifferential y t₀ t w) H.1
  simpa only [H.2] using H'

theorem exists_coreExit_event {k : ℝ} {y : ProjectiveState} {t₀ t : ℝ}
    (hk : 6 ≤ k) (hD : 0 < projectiveStateDenom y)
    (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hy : coreRegion k (projectiveOriginalFlow y t₀ t))
    (hV : projectiveOriginalFlow y t₀ t 2 = 1) (hM : projectiveOriginalFlow y t₀ t 0 < 1) :
    ∃ τ : ProjectiveState → ℝ, τ y = t ∧ ContDiffAt ℝ 1 τ y ∧
      (∀ᶠ z in 𝓝 y, τ z ∈ normalizedMaxDomain (fromProjectiveState z) t₀ ∧
        0 < 1 + normalizedMaxCurve (fromProjectiveState z) t₀ (τ z) 0 ∧
        projectiveOriginalFlow z t₀ (τ z) 2 = 1) ∧
      (∀ᶠ z : ProjectiveState × ℝ in 𝓝 (y, t),
        z.2 ∈ normalizedMaxDomain (fromProjectiveState z.1) t₀ ∧
        (projectiveOriginalFlow z.1 t₀ z.2 2 = 1 ↔ τ z.1 = z.2)) ∧
      ContDiffAt ℝ 1 (fun z => toCoreAngleState (projectiveOriginalFlow z t₀ (τ z))) y ∧
      ContDiffAt ℝ 1 (fun z => projectiveCoreAngle (projectiveOriginalFlow z t₀ (τ z))) y ∧
      ∀ w : ProjectiveState,
        let b := projectiveOriginalFlow y t₀ t
        let q := coreProjectedFlowVariation y t₀ t w 0
        fderiv ℝ (fun z => projectiveCoreAngle (projectiveOriginalFlow z t₀ (τ z))) y w =
          -q / (coreRadius (b 0) (b 2) * (-Real.tanh (projectiveCoreAngle b) +
            coreAngleField (projectiveCoreAngle b) (toCoreAngleState b) 0 / coreRadius (b 0) (b 2))) ∧
        (fderiv ℝ (fun z => toCoreAngleState (projectiveOriginalFlow z t₀ (τ z))) y w) 0 =
          coreExitRadialFactor b * q ∧
        |(fderiv ℝ (fun z => toCoreAngleState (projectiveOriginalFlow z t₀ (τ z))) y w) 0| ≤ |q| := by
  obtain ⟨τ, hτ, hcτ, hhit, huniq, hcmap, hdmap⟩ :=
    exists_projectiveWall_event hD ht hA (ne_of_lt (coreRegion_exit_transverse hk hy hV hM).1)
  have hv : 0 < projectiveOriginalFlow y t₀ (τ y) 2 := by rw [hτ, hV]; norm_num
  have hcP := contDiffAt_toCoreAngleState 1 hv
  have hcZ := contDiffAt_projectiveCoreAngle 1 hv
  refine ⟨τ, hτ, hcτ, by simpa only [hV] using hhit, by simpa only [hV] using huniq,
    ?_, ?_, ?_⟩
  · convert! hcP.comp y hcmap using 1
  · convert! hcZ.comp y hcmap using 1
  intro w b q
  have hdP : HasFDerivAt (fun z => toCoreAngleState (projectiveOriginalFlow z t₀ (τ z)))
      ((fderiv ℝ toCoreAngleState b).comp (projectiveWallArrivalDifferential y t₀ t)) y := by
    have H := (hcP.differentiableAt (by norm_num)).hasFDerivAt.comp y hdmap
    rw [hτ] at H
    convert! H using 1
  have hdZ : HasFDerivAt (fun z => projectiveCoreAngle (projectiveOriginalFlow z t₀ (τ z)))
      ((fderiv ℝ projectiveCoreAngle b).comp (projectiveWallArrivalDifferential y t₀ t)) y := by
    have H := (hcZ.differentiableAt (by norm_num)).hasFDerivAt.comp y hdmap
    rw [hτ] at H
    convert! H using 1
  rw [hdP.fderiv, hdZ.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  have H := coreWallArrivalDifferential_correction hk hD ht hA hy hV hM w
  refine ⟨H.1, H.2, ?_⟩
  rw [H.2, abs_mul, abs_of_pos (coreRegion_exit_factor_bounds hk hy hV hM).1]
  exact mul_le_of_le_one_left (abs_nonneg _) (coreRegion_exit_factor_bounds hk hy hV hM).2.1

theorem coreRegion_exit_angle_bound {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hV : y 2 = 1) (hM : y 0 < 1) (q : ℝ) :
    |(-q) / (coreRadius (y 0) (y 2) * (-Real.tanh (projectiveCoreAngle y) +
      coreAngleField (projectiveCoreAngle y) (toCoreAngleState y) 0 / coreRadius (y 0) (y 2)))| ≤
      2 * |q| / k := by
  let r := coreRadius (y 0) (y 2)
  let f := coreAngleField (projectiveCoreAngle y) (toCoreAngleState y) 0
  have hv : 0 < y 2 := by rw [hV]; norm_num
  have hr : 0 < r := coreRadius_pos hv
  have hrange := coreRegion_radius_bounds hk hy
  have hgap := core_section_phase_gap hk
    (show 99 / 100 * k ≤ coreRadius (y 0) 1 by simpa only [hV] using hrange.1)
  rw [abs_of_neg (sub_neg.mpr hM)] at hgap
  have hf : f ≤ 0 := (coreRegion_exit_radius_velocity hk hy hV hM).1
  have hden : r * (-Real.tanh (projectiveCoreAngle y) + f / r) = y 0 - 1 + f := by
    rw [projectiveCoreAngle, tanh_coreAngle hv]
    change r * (-((1 - y 0) / r) + f / r) = _
    field_simp
    ring
  have hk0 : 0 < k := by linarith only [hk]
  have hnegative : y 0 - 1 + f < 0 := by linarith only [hM, hf]
  have hlower : k / 2 ≤ -(y 0 - 1 + f) := by linarith only [hgap, hf, hk]
  change |(-q) / (r * (-Real.tanh (projectiveCoreAngle y) + f / r))| ≤ _
  rw [hden, abs_div, abs_neg, abs_of_neg hnegative]
  calc
    |q| / -(y 0 - 1 + f) ≤ |q| / (k / 2) :=
      div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hlower
    _ = 2 * |q| / k := by ring

/-- Every admissible large-core entrance has an actual moving-exit derivative satisfying (B.38). -/
theorem exists_large_core_exit_derivative {k u w : ℝ} (hk : 6 ≤ k)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k) (hw : 0 ≤ w ∧ w ≤ (1 / 10000) / k) :
    let y : ProjectiveState := ![1 + Real.sqrt (k ^ 2 - 1), u, 1, w]
    ∃ T > 0, IsLeast {t | 0 < t ∧ projectiveOriginalFlow y 0 t 2 = 1} T ∧
      0 < coreExitRadialFactor (projectiveOriginalFlow y 0 T) ∧
      coreExitRadialFactor (projectiveOriginalFlow y 0 T) ≤ 1 ∧
      |coreExitRadialFactor (projectiveOriginalFlow y 0 T) - 1| ≤ 8 * (u / k + w ^ 2 / k ^ 2) ∧
      ∃ τ : ProjectiveState → ℝ, τ y = T ∧ ContDiffAt ℝ 1 τ y ∧
        (∀ᶠ z in 𝓝 y, τ z ∈ normalizedMaxDomain (fromProjectiveState z) 0 ∧
          0 < 1 + normalizedMaxCurve (fromProjectiveState z) 0 (τ z) 0 ∧
          projectiveOriginalFlow z 0 (τ z) 2 = 1) ∧
        (∀ᶠ z : ProjectiveState × ℝ in 𝓝 (y, T),
          projectiveOriginalFlow z.1 0 z.2 2 = 1 ↔ τ z.1 = z.2) ∧
        ContDiffAt ℝ 1 (fun z => toCoreAngleState (projectiveOriginalFlow z 0 (τ z))) y ∧
        ContDiffAt ℝ 1 (fun z => projectiveCoreAngle (projectiveOriginalFlow z 0 (τ z))) y ∧
        ∀ v : ProjectiveState,
          let b := projectiveOriginalFlow y 0 T
          let q := coreProjectedFlowVariation y 0 T v 0
          fderiv ℝ (fun z => projectiveCoreAngle (projectiveOriginalFlow z 0 (τ z))) y v =
            -q / (coreRadius (b 0) (b 2) * (-Real.tanh (projectiveCoreAngle b) +
              coreAngleField (projectiveCoreAngle b) (toCoreAngleState b) 0 / coreRadius (b 0) (b 2))) ∧
          (fderiv ℝ (fun z => toCoreAngleState (projectiveOriginalFlow z 0 (τ z))) y v) 0 =
            coreExitRadialFactor b * q ∧
          |(fderiv ℝ (fun z => toCoreAngleState (projectiveOriginalFlow z 0 (τ z))) y v) 0| ≤ |q| ∧
          |fderiv ℝ (fun z => projectiveCoreAngle (projectiveOriginalFlow z 0 (τ z))) y v| ≤
            2 * |q| / k := by
  intro y
  have hD : 0 < projectiveStateDenom y :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (coreBootstrap_denom_lower hk hu hw)
  have hc : stateConstraint (fromProjectiveState y) = 1 := fromProjectiveState_constraint (ne_of_gt hD)
  obtain ⟨T, hT, hfirst, hcore, hM, _⟩ := exists_large_core_traversal hk hu hw
  obtain ⟨S, _, hfirstS, _, hpos, hle, herr⟩ := exists_large_core_exit_factor hk hu hw
  have hST : S = T := hfirstS.unique hfirst
  subst S
  have ht : T ∈ normalizedMaxDomain (fromProjectiveState y) 0 :=
    normalizedMaxDomain_contains_Ici_of_constraint hc 0 hT.le
  have hexit := hcore T ⟨hT.le, le_rfl⟩
  obtain ⟨τ, hτ, hcτ, hhit, huniq, hcP, hcZ, hderiv⟩ :=
    exists_coreExit_event hk hD ht hexit.1 hexit.2 hfirst.1.2 hM
  refine ⟨T, hT, hfirst, hpos, hle, herr, τ, hτ, hcτ, hhit, huniq.mono (fun _ h => h.2), hcP, hcZ, ?_⟩
  intro v b q
  have H := hderiv v
  refine ⟨H.1, H.2.1, H.2.2, ?_⟩
  rw [H.1]
  exact coreRegion_exit_angle_bound hk hexit.2 hfirst.1.2 hM q

end BianchiIX
