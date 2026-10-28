import BianchiIX.Dynamics.CompactConnectionReturn
import BianchiIX.Dynamics.EntranceWeakCoefficient

noncomputable section

namespace BianchiIX

open Set Filter Metric
open scoped Topology

/-- The finite phase in (B.47), before the long entrance. -/
def compactConnectionFinitePhase (η : ℝ) (Y : CoreAngleState) : ℝ :=
  entranceStableRadius (compactConnectionEntry η Y)

theorem contDiffAt_compactConnectionEntry_two {η : ℝ} {Y : CoreAngleState}
    (h : ContDiffAt ℝ 2 (coreTailState η) Y) :
    ContDiffAt ℝ 2 (compactConnectionEntry η) Y := by
  have hr : ContDiff ℝ 2 projectiveReflection := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp [projectiveReflection] <;> fun_prop
  exact hr.contDiffAt.comp Y h

/-- Stable projection cancels the fixed-height tail error exactly on the reference axis. -/
theorem compactConnection_reference_stable_phase {k η : ℝ}
    (hk : 7 / 2 ≤ k) (hη : 0 < η ∧ η ≤ 1 / 10000) :
    2 < compactConnectionEntry η ![k, 0, 0] 0 ∧
      entranceStablePhase (compactConnectionEntry η ![k, 0, 0]) = k - 1 := by
  have hk0 : 0 ≤ k := by linarith
  have hk2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 2) hk 2
  have hη2 := pow_le_pow_left₀ hη.1.le hη.2 2
  have hsq : 0 ≤ k ^ 2 - η ^ 2 := by nlinarith only [hk2, hη2]
  have hs := Real.sq_sqrt hsq
  have hm : 2 < Real.sqrt (k ^ 2 - η ^ 2) - 1 := by
    nlinarith only [hs, Real.sqrt_nonneg (k ^ 2 - η ^ 2), hk2, hη2]
  have heq : compactConnectionEntry η ![k, 0, 0] = ![Real.sqrt (k ^ 2 - η ^ 2) - 1, 0, 0, η] :=
    coreTail_reflected_reference (by linarith) ⟨hη.1, by linarith [hη.2]⟩
  rw [heq]
  refine ⟨hm, ?_⟩
  change stableBoundaryProjection (Real.sqrt (k ^ 2 - η ^ 2) - 1) 0 η = k - 1
  rw [stableBoundaryProjection_weak hm.le (by simp) (by rw [abs_of_pos hη.1]; linarith [hη.2])]
  unfold stableWeakRadius phaseNorm
  rw [show (Real.sqrt (k ^ 2 - η ^ 2) - 1 + 1) ^ 2 + η ^ 2 = k ^ 2 by nlinarith only [hs],
    Real.sqrt_sq hk0]

theorem compactConnectionFinitePhase_reference {k η : ℝ}
    (hk : 7 / 2 ≤ k) (hη : 0 < η ∧ η ≤ 1 / 10000) :
    compactConnectionFinitePhase η ![k, 0, 0] = k - 2 := by
  have hP := (compactConnection_reference_stable_phase hk hη).2
  have hv : compactConnectionEntry η ![k, 0, 0] 2 = 0 := by
    change projectiveReflection (coreTailState η ![k, 0, 0]) 2 = 0
    rw [coreTail_reflected_reference (by linarith) ⟨hη.1, by linarith [hη.2]⟩]
    rfl
  unfold compactConnectionFinitePhase entranceStableRadius
  rw [hP, hv]
  change Real.sqrt ((k - 1 - 1) ^ 2 + 0 ^ 2) = k - 2
  rw [show (k - 1 - 1) ^ 2 + 0 ^ 2 = (k - 2) ^ 2 by ring,
    Real.sqrt_sq (by linarith)]

theorem contDiffAt_compactConnectionFinitePhase_reference {k η : ℝ}
    (hk : 7 / 2 ≤ k) (hη : 0 < η ∧ η ≤ 1 / 10000) :
    ContDiffAt ℝ 2 (compactConnectionFinitePhase η) ![k, 0, 0] := by
  let Y : CoreAngleState := ![k, 0, 0]
  let y := compactConnectionEntry η Y
  have H := coreTail_reference_regular (by linarith : 1 < k) ⟨hη.1, by linarith [hη.2]⟩
  have hentry : ContDiffAt ℝ 2 (compactConnectionEntry η) Y := contDiffAt_compactConnectionEntry_two H.2.2.2.1
  have hdata := compactConnection_reference_stable_phase hk hη
  have heq : y = ![Real.sqrt (k ^ 2 - η ^ 2) - 1, 0, 0, η] :=
    coreTail_reflected_reference (by linarith) ⟨hη.1, by linarith [hη.2]⟩
  have hP : ContDiffAt ℝ 2 entranceStablePhase y := contDiffAt_entranceStablePhase_two hdata.1.le
    (by rw [heq]; norm_num) (by rw [heq]; change |η| < 1 / 200; rw [abs_of_pos hη.1]; linarith [hη.2])
  have hn : (entranceStablePhase y - 1) ^ 2 + y 2 ^ 2 ≠ 0 := by
    have hp : 0 < entranceStablePhase y - 1 := by change 0 < entranceStablePhase (compactConnectionEntry η Y) - 1; rw [hdata.2]; linarith
    positivity
  have hR : ContDiffAt ℝ 2 entranceStableRadius y :=
    (((hP.sub contDiffAt_const).pow 2).add ((by fun_prop : ContDiffAt ℝ 2 (fun z : ProjectiveState => z 2) y).pow 2)).sqrt hn
  exact hR.comp Y hentry

/-- Uniform C2 bounds include a signed neighborhood of the closed entrance quadrant. -/
theorem exists_compact_connection_finite_phase_bounds {η : ℝ} (hη : 0 < η ∧ η ≤ 1 / 10000) :
    ∃ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ Y : CoreAngleState,
      (31 / 8 ≤ Y 0 ∧ Y 0 ≤ 6) → |Y 1| ≤ ε → |Y 2| ≤ ε →
      coreTailValid η Y ∧ ContDiffAt ℝ 2 (compactConnectionFinitePhase η) Y ∧
        |compactConnectionFinitePhase η Y| + ‖fderiv ℝ (compactConnectionFinitePhase η) Y‖ +
          ‖fderiv ℝ (fderiv ℝ (compactConnectionFinitePhase η)) Y‖ ≤ C := by
  let F := compactConnectionFinitePhase η
  let G : Set CoreAngleState := {Y | coreTailValid η Y ∧ ContDiffAt ℝ 2 F Y}
  let S : Set CoreAngleState := (fun k : ℝ => (![k, 0, 0] : CoreAngleState)) '' Icc (31 / 8) 6
  have hcS : IsCompact S := isCompact_Icc.image (by fun_prop)
  have hSG : S ⊆ interior G := by
    rintro Y ⟨k, hk, rfl⟩
    have H := coreTail_reference_regular (by linarith only [hk.1] : 1 < k)
      ⟨hη.1, by linarith [hη.2]⟩
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [H.2.2.2.2,
      (contDiffAt_compactConnectionFinitePhase_reference (k := k) (by linarith only [hk.1]) hη).eventually
        (by norm_num)] with Z hZ hF
    exact ⟨hZ, hF⟩
  obtain ⟨ε, hε, hεG⟩ := hcS.exists_cthickening_subset_open isOpen_interior hSG
  let W := cthickening ε S
  have hWG : W ⊆ G := hεG.trans interior_subset
  let q := fun Y => |F Y| + ‖fderiv ℝ F Y‖ + ‖fderiv ℝ (fderiv ℝ F) Y‖
  have hcq : ContinuousOn q W := by
    intro Y hY
    have hF : ContDiffAt ℝ 2 F Y := (hWG hY).2
    have hF' := hF.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    exact ((hF.continuousAt.abs.add (hF.continuousAt_fderiv (by norm_num)).norm).add
      (hF'.continuousAt_fderiv (by norm_num)).norm).continuousWithinAt
  obtain ⟨B, hB⟩ := hcS.cthickening.exists_bound_of_continuousOn hcq
  refine ⟨ε, hε, max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro Y hk hu hw
  have hd : dist Y (![Y 0, 0, 0] : CoreAngleState) ≤ ε := by
    apply (dist_pi_le_iff hε.le).mpr
    intro i
    fin_cases i
    · simpa using hε.le
    · simpa [Real.dist_eq] using hu
    · simpa [Real.dist_eq] using hw
  have hYS : (![Y 0, 0, 0] : CoreAngleState) ∈ S := ⟨Y 0, hk, rfl⟩
  have hYW : Y ∈ W := mem_cthickening_of_dist_le Y _ ε S hYS hd
  exact ⟨(hWG hYW).1, (hWG hYW).2, (le_abs_self (q Y)).trans ((hB Y hYW).trans (le_max_left _ _))⟩

/-- On the zero strong-wall plane the finite phase uses only the finite smooth tail. -/
theorem compactConnectionFinitePhase_weak {η : ℝ} {Y : CoreAngleState}
    (hη : |η| ≤ 1 / 200) (htail : coreTailValid η Y)
    (hm : 2 ≤ -coreTailState η Y 0) (hu : Y 1 = 0) :
    compactConnectionFinitePhase η Y =
      phaseNorm (coreRadius (coreTailState η Y 0) η - 2) (coreTailState η Y 3) := by
  have hU : compactConnectionEntry η Y 1 = 0 := coreTailState_wall_zero htail 0 hu
  have hW : compactConnectionEntry η Y 3 = η := coreTailState_active htail
  have hP := entranceStablePhase_weak hm hU (by rw [hW]; exact hη)
  unfold compactConnectionFinitePhase entranceStableRadius
  rw [hP, hW]
  have hs : stableWeakRadius (compactConnectionEntry η Y 0) η = coreRadius (coreTailState η Y 0) η := by
    change Real.sqrt ((-coreTailState η Y 0 + 1) ^ 2 + η ^ 2) =
      Real.sqrt ((coreTailState η Y 0 - 1) ^ 2 + η ^ 2)
    congr 1
    ring
  rw [hs]
  change Real.sqrt ((coreRadius (coreTailState η Y 0) η - 1 - 1) ^ 2 + (coreTailState η Y 3) ^ 2) = _
  unfold phaseNorm
  congr 1
  ring

theorem compactConnectionFinitePhase_radial_reference {k η : ℝ}
    (hk : 31 / 8 ≤ k) (hη : 0 < η ∧ η ≤ 1 / 10000) :
    fderiv ℝ (compactConnectionFinitePhase η) ![k, 0, 0] (Pi.single 0 1) = 1 := by
  have hline : HasDerivAt (fun a : ℝ => (![a, 0, 0] : CoreAngleState)) (Pi.single 0 1) k := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · change HasDerivAt (fun a : ℝ => a) 1 k
      exact hasDerivAt_id' k
    · simpa using hasDerivAt_const k (0 : ℝ)
    · simpa using hasDerivAt_const k (0 : ℝ)
  have hF := (contDiffAt_compactConnectionFinitePhase_reference (k := k) (by linarith only [hk]) hη).differentiableAt (by norm_num)
  have H := hF.hasFDerivAt.comp_hasDerivAt k hline
  have heq : (fun a : ℝ => compactConnectionFinitePhase η ![a, 0, 0]) =ᶠ[𝓝 k] (fun a => a - 2) := by
    filter_upwards [eventually_gt_nhds (show 7 / 2 < k by linarith)] with a ha
    exact compactConnectionFinitePhase_reference ha.le hη
  exact (H.congr_of_eventuallyEq heq.symm).unique ((hasDerivAt_id' k).sub_const 2)

end BianchiIX
