import BianchiIX.Dynamics.ReferenceSecondReturn
import BianchiIX.Dynamics.CoreReturnDifferential
import Mathlib.Topology.MetricSpace.Thickening

noncomputable section

namespace BianchiIX

open Set Filter Metric
open scoped Topology

def coreRadiusReturnTime (Y : CoreAngleState) : ℝ :=
  sInf {t : ℝ | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry Y)) 0 ∧
    projectiveActiveWall (normalizedMaxCurve (fromProjectiveState (coreRadiusEntry Y)) 0 t) = 1}

def coreRadiusReturnValid (Y : CoreAngleState) : Prop :=
  let x := fromProjectiveState (coreRadiusEntry Y)
  let T := coreRadiusReturnTime Y
  IsLeast {t : ℝ | 0 < t ∧ t ∈ normalizedMaxDomain x 0 ∧
    projectiveActiveWall (normalizedMaxCurve x 0 t) = 1} T ∧
    (∀ t ∈ Icc 0 T, t ∈ normalizedMaxDomain x 0 ∧ 0 < 1 + normalizedMaxCurve x 0 t 0) ∧
    (∀ t ∈ Ioo 0 T, 1 < projectiveActiveWall (normalizedMaxCurve x 0 t)) ∧
    normalizedEventRate projectiveActiveWall x 0 T < 0

/-- The canonical first return agrees locally with the smooth branch near every boundary pulse. -/
theorem coreRadiusReturn_reference_regular {k : ℝ} (hk : 1 < k) :
    coreRadiusReturnTime ![k, 0, 0] = referenceNormalizedTime k ∧
      ContDiffAt ℝ 2 coreRadiusReturnTime ![k, 0, 0] ∧
      ContDiffAt ℝ 2 (coreReturnState coreRadiusReturnTime) ![k, 0, 0] ∧
      (∀ᶠ Y in 𝓝 (![k, 0, 0] : CoreAngleState), coreRadiusReturnValid Y) := by
  let Y₀ : CoreAngleState := ![k, 0, 0]
  let e : CoreAngleState → CoreCoordinates := fun Y => coreSectionCoordinates (coreRadiusEntry Y)
  have hemb (Y : CoreAngleState) : coreSectionEmbedding (e Y) = coreRadiusEntry Y := by
    ext i
    fin_cases i <;> rfl
  have hchart (Y : CoreAngleState) : coreSectionChart (e Y) = fromProjectiveState (coreRadiusEntry Y) := by
    rw [coreSectionChart, hemb]
  have he₀ : e Y₀ = referenceCoreInput k := rfl
  have hce : ContDiffAt ℝ 2 e Y₀ :=
    (contDiff_coreSectionCoordinates 2).contDiffAt.comp Y₀ (contDiffAt_coreRadiusEntry 2 hk)
  obtain ⟨τ, P, hτ, hP, hcτ, hcP, hnear, _⟩ := exists_referenceCore_firstReturn_two hk
  have hnear' := hce.continuousAt.eventually (he₀.symm ▸ hnear)
  have heq : coreRadiusReturnTime =ᶠ[𝓝 Y₀] (fun Y => τ (e Y)) := by
    filter_upwards [hnear'] with Y hY
    have H := hY.1.csInf_eq
    simpa only [coreRadiusReturnTime, hchart] using H
  have hcTime : ContDiffAt ℝ 2 coreRadiusReturnTime Y₀ :=
    ((he₀.symm ▸ hcτ).comp Y₀ hce).congr_of_eventuallyEq heq
  have hfirst : ∀ᶠ Y in 𝓝 Y₀, coreRadiusReturnValid Y := by
    filter_upwards [hnear', heq] with Y hY hT
    dsimp only [coreRadiusReturnValid]
    rw [hT, ← hchart]
    exact ⟨hY.1, hY.2.1, hY.2.2.1, hY.2.2.2.1⟩
  have hcP' : ContDiffAt ℝ 2 (fun Y => P (e Y)) Y₀ := (he₀.symm ▸ hcP).comp Y₀ hce
  have hcEmb : ContDiffAt ℝ 2 (fun Y => coreSectionEmbedding (P (e Y))) Y₀ :=
    (contDiff_coreSectionEmbedding 2).contDiffAt.comp Y₀ hcP'
  have hcOut : ContDiffAt ℝ 2 (fun Y => toCoreAngleState (coreSectionEmbedding (P (e Y)))) Y₀ := by
    have hv : (0 : ℝ) < coreSectionEmbedding (P (e Y₀)) 2 := by change (0 : ℝ) < 1; norm_num
    convert! (contDiffAt_toCoreAngleState 2 hv).comp Y₀ hcEmb using 1
  have heqOut : coreReturnState coreRadiusReturnTime =ᶠ[𝓝 Y₀]
      (fun Y => toCoreAngleState (coreSectionEmbedding (P (e Y)))) := by
    filter_upwards [hnear', heq] with Y hY hT
    dsimp only [coreReturnState, projectiveOriginalFlow]
    rw [hT, ← hchart, hY.2.2.2.2]
  refine ⟨?_, hcTime, hcOut.congr_of_eventuallyEq heqOut, hfirst⟩
  exact heq.self_of_nhds.trans ((congrArg τ he₀).trans hτ)

/-- One common wall neighborhood and one bound for the first two derivatives on the compact core. -/
theorem exists_compact_core_return_two_germ :
    ∃ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ Y : CoreAngleState,
      (2 ≤ Y 0 ∧ Y 0 ≤ 6) → |Y 1| ≤ ε → |Y 2| ≤ ε →
      coreRadiusReturnValid Y ∧ ContDiffAt ℝ 2 coreRadiusReturnTime Y ∧
        ContDiffAt ℝ 2 (coreReturnState coreRadiusReturnTime) Y ∧
        ‖fderiv ℝ coreRadiusReturnTime Y‖ +
          ‖fderiv ℝ (coreReturnState coreRadiusReturnTime) Y‖ +
          ‖fderiv ℝ (fderiv ℝ coreRadiusReturnTime) Y‖ +
          ‖fderiv ℝ (fderiv ℝ (coreReturnState coreRadiusReturnTime)) Y‖ ≤ C ∧
        (∀ᶠ Z in 𝓝 Y, coreRadiusReturnValid Z ∧ ContDiffAt ℝ 2 coreRadiusReturnTime Z ∧
          ContDiffAt ℝ 2 (coreReturnState coreRadiusReturnTime) Z) := by
  let P := coreReturnState coreRadiusReturnTime
  let G : Set CoreAngleState := {Y | coreRadiusReturnValid Y ∧
    ContDiffAt ℝ 2 coreRadiusReturnTime Y ∧ ContDiffAt ℝ 2 P Y}
  let S : Set CoreAngleState := (fun k : ℝ => (![k, 0, 0] : CoreAngleState)) '' Icc 2 6
  have hcS : IsCompact S := isCompact_Icc.image (by fun_prop)
  have hSG : S ⊆ interior G := by
    rintro Y ⟨k, hk, rfl⟩
    obtain ⟨_, ht, hP, hvalid⟩ := coreRadiusReturn_reference_regular (by linarith only [hk.1])
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [hvalid, ht.eventually (by norm_num), hP.eventually (by norm_num)] with Z hz htZ hPZ
    exact ⟨hz, htZ, hPZ⟩
  obtain ⟨ε, hε, hεG⟩ := hcS.exists_cthickening_subset_open isOpen_interior hSG
  let W := cthickening ε S
  have hWG : W ⊆ G := hεG.trans interior_subset
  let b : CoreAngleState → ℝ := fun Y => ‖fderiv ℝ coreRadiusReturnTime Y‖ +
    ‖fderiv ℝ P Y‖ + ‖fderiv ℝ (fderiv ℝ coreRadiusReturnTime) Y‖ + ‖fderiv ℝ (fderiv ℝ P) Y‖
  have hcb : ContinuousOn b W := by
    intro Y hY
    obtain ⟨_, ht, hP⟩ := hWG hY
    have ht' := ht.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    have hP' := hP.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    exact ((((ht.continuousAt_fderiv (by norm_num)).norm.add
      (hP.continuousAt_fderiv (by norm_num)).norm).add
      (ht'.continuousAt_fderiv (by norm_num)).norm).add
      (hP'.continuousAt_fderiv (by norm_num)).norm).continuousWithinAt
  obtain ⟨B, hB⟩ := hcS.cthickening.exists_bound_of_continuousOn hcb
  refine ⟨ε, hε, max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro Y hk hu hw
  have hdist : dist Y (![Y 0, 0, 0] : CoreAngleState) ≤ ε := by
    apply (dist_pi_le_iff hε.le).mpr
    intro i
    fin_cases i
    · simpa using hε.le
    · simpa [Real.dist_eq] using hu
    · simpa [Real.dist_eq] using hw
  have hYS : (![Y 0, 0, 0] : CoreAngleState) ∈ S := ⟨Y 0, hk, rfl⟩
  have hYW : Y ∈ W := mem_cthickening_of_dist_le Y _ ε S hYS hdist
  obtain ⟨hvalid, ht, hP⟩ := hWG hYW
  exact ⟨hvalid, ht, hP, (le_abs_self (b Y)).trans ((hB Y hYW).trans (le_max_left _ _)),
    mem_interior_iff_mem_nhds.mp (hεG hYW)⟩

theorem exists_compact_core_return_two :
    ∃ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ Y : CoreAngleState,
      (2 ≤ Y 0 ∧ Y 0 ≤ 6) → |Y 1| ≤ ε → |Y 2| ≤ ε →
      coreRadiusReturnValid Y ∧ ContDiffAt ℝ 2 coreRadiusReturnTime Y ∧
        ContDiffAt ℝ 2 (coreReturnState coreRadiusReturnTime) Y ∧
        ‖fderiv ℝ coreRadiusReturnTime Y‖ +
          ‖fderiv ℝ (coreReturnState coreRadiusReturnTime) Y‖ +
          ‖fderiv ℝ (fderiv ℝ coreRadiusReturnTime) Y‖ +
          ‖fderiv ℝ (fderiv ℝ (coreReturnState coreRadiusReturnTime)) Y‖ ≤ C := by
  obtain ⟨ε, hε, C, hC, h⟩ := exists_compact_core_return_two_germ
  refine ⟨ε, hε, C, hC, ?_⟩
  intro Y hk hu hw
  have H := h Y hk hu hw
  exact ⟨H.1, H.2.1, H.2.2.1, H.2.2.2.1⟩

end BianchiIX
