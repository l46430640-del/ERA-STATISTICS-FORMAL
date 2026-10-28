import BianchiIX.Dynamics.CompactConnectionWeakPhase

noncomputable section

namespace BianchiIX

open Set Filter Metric
open scoped Topology

theorem compactConnectionFinitePhase_weak_radial_germ {k η : ℝ}
    (hk : 7 / 2 ≤ k) (hη : 0 < η ∧ η ≤ 1 / 10000) :
    ∀ᶠ p : ℝ × ℝ in 𝓝 (k, 0),
      fderiv ℝ (compactConnectionFinitePhase η) ![p.1, 0, p.2] (Pi.single 0 1) =
        1 + p.2 ^ 2 * fderiv ℝ (compactConnectionWeakCoefficient η) ![p.1, 0, p.2] (Pi.single 0 1) := by
  let c := fun p : ℝ × ℝ => (![p.1, 0, p.2] : CoreAngleState)
  have hc : Tendsto c (𝓝 (k, 0)) (𝓝 (![k, 0, 0] : CoreAngleState)) :=
    (by fun_prop : Continuous c).continuousAt.tendsto
  have hF := (contDiffAt_compactConnectionFinitePhase_reference hk hη).eventually (by norm_num)
  have hQ := (contDiffAt_compactConnectionWeakCoefficient_reference hk hη).eventually (by norm_num)
  filter_upwards [hc.eventually hF, hc.eventually hQ,
    (compactConnectionFinitePhase_weak_germ hk hη).eventually_nhds] with p hpF hpQ heq
  have hline : HasDerivAt (fun a : ℝ => (![a, 0, p.2] : CoreAngleState)) (Pi.single 0 1) p.1 := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · change HasDerivAt (fun a : ℝ => a) 1 p.1
      exact hasDerivAt_id' p.1
    · simpa using hasDerivAt_const p.1 (0 : ℝ)
    · simpa using hasDerivAt_const p.1 p.2
  have hFd := (hpF.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt p.1 hline
  have hQd := (hpQ.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt p.1 hline
  have hformula := ((hasDerivAt_id' p.1).sub_const 2).add (hQd.const_mul (p.2 ^ 2))
  have heq' : (fun a : ℝ => compactConnectionFinitePhase η ![a, 0, p.2]) =ᶠ[𝓝 p.1]
      (fun a => a - 2 + p.2 ^ 2 * compactConnectionWeakCoefficient η ![a, 0, p.2]) :=
    (by fun_prop : Continuous (fun a : ℝ => (a, p.2))).continuousAt.tendsto.eventually heq
  exact (hFd.congr_of_eventuallyEq heq'.symm).unique hformula

/-- The weak-wall square persists in the radial column uniformly on the compact phase interval. -/
theorem exists_compact_connection_weak_radial_bound {η : ℝ} (hη : 0 < η ∧ η ≤ 1 / 10000) :
    ∃ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ k : ℝ, (31 / 8 ≤ k ∧ k ≤ 6) →
      ∀ w : ℝ, |w| ≤ ε →
        |fderiv ℝ (compactConnectionFinitePhase η) ![k, 0, w] (Pi.single 0 1) - 1| ≤ C * w ^ 2 := by
  let F := compactConnectionFinitePhase η
  let Q := compactConnectionWeakCoefficient η
  let c := fun p : ℝ × ℝ => (![p.1, 0, p.2] : CoreAngleState)
  let G : Set (ℝ × ℝ) := {p | ContDiffAt ℝ 2 Q (c p) ∧
    fderiv ℝ F (c p) (Pi.single 0 1) = 1 + p.2 ^ 2 * fderiv ℝ Q (c p) (Pi.single 0 1)}
  let S : Set (ℝ × ℝ) := (fun k : ℝ => (k, (0 : ℝ))) '' Icc (31 / 8) 6
  have hcS : IsCompact S := isCompact_Icc.image (by fun_prop)
  have hSG : S ⊆ interior G := by
    rintro p ⟨k, hk, rfl⟩
    have hk' : 7 / 2 ≤ k := by linarith only [hk.1]
    have hc : Tendsto c (𝓝 (k, 0)) (𝓝 (![k, 0, 0] : CoreAngleState)) :=
      (by fun_prop : Continuous c).continuousAt.tendsto
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [hc.eventually ((contDiffAt_compactConnectionWeakCoefficient_reference hk' hη).eventually
      (by norm_num)), compactConnectionFinitePhase_weak_radial_germ hk' hη] with p hp hrad
    exact ⟨hp, hrad⟩
  obtain ⟨ε, hε, hεG⟩ := hcS.exists_cthickening_subset_open isOpen_interior hSG
  let W := cthickening ε S
  have hWG : W ⊆ G := hεG.trans interior_subset
  have hnorm : ContinuousOn (fun p => ‖fderiv ℝ Q (c p)‖) W := by
    intro p hp
    have hQ : ContDiffAt ℝ 2 Q (c p) := (hWG hp).1
    exact (((hQ.continuousAt_fderiv (by norm_num)).comp
      (by fun_prop : ContinuousAt c p)).norm).continuousWithinAt
  obtain ⟨B, hB⟩ := hcS.cthickening.exists_bound_of_continuousOn hnorm
  refine ⟨ε, hε, max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro k hk w hw
  have hs : (k, (0 : ℝ)) ∈ S := ⟨k, hk, rfl⟩
  have hd : dist (k, w) (k, (0 : ℝ)) ≤ ε := by
    simpa only [Prod.dist_eq, dist_self, Real.dist_eq, sub_zero, max_eq_right (abs_nonneg w)] using hw
  have hp : (k, w) ∈ W := mem_cthickening_of_dist_le _ _ ε S hs hd
  have hb : ‖fderiv ℝ Q (c (k, w))‖ ≤ max B 1 := by
    have H := hB (k, w) hp
    simpa only [Real.norm_eq_abs, abs_norm] using H.trans (le_max_left B 1)
  have hcol : |fderiv ℝ Q (c (k, w)) (Pi.single 0 1)| ≤ max B 1 := by
    have H := (fderiv ℝ Q (c (k, w))).le_opNorm (Pi.single 0 1)
    have HL : |fderiv ℝ Q (c (k, w)) (Pi.single 0 1)| ≤ ‖fderiv ℝ Q (c (k, w))‖ := by
      simpa only [Real.norm_eq_abs, Pi.norm_single, norm_one, mul_one] using H
    exact HL.trans hb
  have heq := (hWG hp).2
  change fderiv ℝ F ![k, 0, w] (Pi.single 0 1) =
    1 + w ^ 2 * fderiv ℝ Q ![k, 0, w] (Pi.single 0 1) at heq
  change |fderiv ℝ F ![k, 0, w] (Pi.single 0 1) - 1| ≤ _
  rw [heq, add_sub_cancel_left, abs_mul, abs_of_nonneg (sq_nonneg w)]
  exact (mul_le_mul_of_nonneg_left hcol (sq_nonneg w)).trans_eq (mul_comm _ _)

end BianchiIX
