import BianchiIX.Dynamics.CompactCoreFactorBounds

noncomputable section

namespace BianchiIX

open Set Filter Metric
open scoped Topology

theorem coreRadiusReturn_reference_radial_derivative {k : ℝ} (hk : 1 < k) :
    fderiv ℝ (coreReturnState coreRadiusReturnTime) ![k, 0, 0] (Pi.single 0 1) = Pi.single 0 1 := by
  have hp : HasDerivAt (fun s : ℝ => (![s, 0, 0] : CoreAngleState)) (Pi.single 0 1) k := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · convert! hasDerivAt_id k using 1
    · simpa using hasDerivAt_const k (0 : ℝ)
    · simpa using hasDerivAt_const k (0 : ℝ)
  have hF := (coreRadiusReturn_reference_regular hk).2.2.1
  have H := (hF.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt k hp
  have heq : (fun s : ℝ => coreReturnState coreRadiusReturnTime ![s, 0, 0]) =ᶠ[𝓝 k]
      (fun s => ![s, 0, 0]) := by
    filter_upwards [isOpen_Ioi.mem_nhds (show k ∈ Ioi (1 : ℝ) from hk)] with s hs
    exact coreRadiusReturn_reference_value hs
  exact (H.congr_of_eventuallyEq heq.symm).unique hp

theorem exists_compact_core_radial_margin {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ Y : CoreAngleState,
      (2 ≤ Y 0 ∧ Y 0 ≤ 6) → |Y 1| ≤ ε → |Y 2| ≤ ε →
      |(fderiv ℝ (coreReturnState coreRadiusReturnTime) Y (Pi.single 0 1)) 0 - 1| ≤ δ ∧
        ‖fderiv ℝ (coreReturnState coreRadiusReturnTime) Y‖ ≤ C := by
  let F := coreReturnState coreRadiusReturnTime
  let S : Set CoreAngleState := (fun k : ℝ => (![k, 0, 0] : CoreAngleState)) '' Icc 2 6
  let G : Set CoreAngleState := {Y | |(fderiv ℝ F Y (Pi.single 0 1)) 0 - 1| < δ}
  have hS : IsCompact S := isCompact_Icc.image (by fun_prop)
  have hSG : S ⊆ interior G := by
    rintro Y ⟨k, hk, rfl⟩
    have hk1 : 1 < k := by linarith only [hk.1]
    have hc := ((coreRadiusReturn_reference_regular hk1).2.2.1.continuousAt_fderiv (by norm_num)).clm_apply
      (continuousAt_const (y := (Pi.single 0 1 : CoreAngleState)))
    have hcr := ((continuousAt_pi.mp hc 0).sub (continuousAt_const (y := (1 : ℝ)))).abs
    apply mem_interior_iff_mem_nhds.mpr
    apply hcr.eventually (isOpen_Iio.mem_nhds _)
    change |(fderiv ℝ F ![k, 0, 0] (Pi.single 0 1)) 0 - 1| < δ
    simpa only [F, coreRadiusReturn_reference_radial_derivative hk1, Pi.single_eq_same,
      sub_self, abs_zero] using hδ
  obtain ⟨ρ, hρ, hρG⟩ := hS.exists_cthickening_subset_open isOpen_interior hSG
  obtain ⟨ε₀, hε₀, C, hC, hbox⟩ := exists_compact_core_return_two
  refine ⟨min ε₀ ρ, lt_min hε₀ hρ, C, hC, ?_⟩
  intro Y hk hu hw
  have hdist : dist Y (![Y 0, 0, 0] : CoreAngleState) ≤ ρ := by
    apply (dist_pi_le_iff hρ.le).mpr
    intro i
    fin_cases i
    · simpa using hρ.le
    · simpa [Real.dist_eq] using hu.trans (min_le_right ε₀ ρ)
    · simpa [Real.dist_eq] using hw.trans (min_le_right ε₀ ρ)
  have hnear : Y ∈ G := interior_subset (hρG
    (mem_cthickening_of_dist_le Y _ ρ S ⟨Y 0, hk, rfl⟩ hdist))
  refine ⟨hnear.le, ?_⟩
  have H := (hbox Y hk (hu.trans (min_le_left _ _)) (hw.trans (min_le_left _ _))).2.2.2
  linarith only [H, norm_nonneg (fderiv ℝ coreRadiusReturnTime Y),
    norm_nonneg (fderiv ℝ (fderiv ℝ coreRadiusReturnTime) Y), norm_nonneg (fderiv ℝ (fderiv ℝ F) Y)]

end BianchiIX
