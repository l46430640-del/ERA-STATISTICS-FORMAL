import BianchiIX.Dynamics.CompactConnectionFinitePhase
import BianchiIX.Dynamics.EntranceRadialCoordinates

noncomputable section

namespace BianchiIX

open Set Filter Metric
open scoped Topology

def compactConnectionCoordinates (η : ℝ) (Y : CoreAngleState) : ProjectiveState :=
  ![compactConnectionFinitePhase η Y, Y 1 * coreTailMultiplier η Y 0,
    Y 2 * coreTailMultiplier η Y 1, η]

theorem compactConnectionCoordinates_eq {η : ℝ} {Y : CoreAngleState} (H : coreTailValid η Y) :
    compactConnectionCoordinates η Y = entranceRadialCoordinates (compactConnectionEntry η Y) := by
  have heq := coreTail_reflected_multiplier_state H
  ext i
  fin_cases i
  · rfl
  · exact (congrFun heq 1).symm
  · exact (congrFun heq 2).symm
  · exact (congrFun heq 3).symm

theorem contDiffAt_compactConnectionCoordinates_two {η : ℝ} {Y : CoreAngleState}
    (hF : ContDiffAt ℝ 2 (compactConnectionFinitePhase η) Y)
    (hB : ∀ i : Fin 2, ContDiffAt ℝ 2 (fun Z => coreTailMultiplier η Z i) Y) :
    ContDiffAt ℝ 2 (compactConnectionCoordinates η) Y := by
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact hF
  · exact (by fun_prop : ContDiffAt ℝ 2 (fun Z : CoreAngleState => Z 1) Y).mul (hB 0)
  · exact (by fun_prop : ContDiffAt ℝ 2 (fun Z : CoreAngleState => Z 2) Y).mul (hB 1)
  · exact contDiffAt_const

theorem compactConnectionCoordinates_fderiv {η : ℝ} {Y : CoreAngleState}
    (hF : ContDiffAt ℝ 2 (compactConnectionFinitePhase η) Y)
    (hB : ∀ i : Fin 2, ContDiffAt ℝ 2 (fun Z => coreTailMultiplier η Z i) Y) (v : CoreAngleState) :
    fderiv ℝ (compactConnectionCoordinates η) Y v =
      ![fderiv ℝ (compactConnectionFinitePhase η) Y v,
        v 1 * coreTailMultiplier η Y 0 + Y 1 * fderiv ℝ (fun Z => coreTailMultiplier η Z 0) Y v,
        v 2 * coreTailMultiplier η Y 1 + Y 2 * fderiv ℝ (fun Z => coreTailMultiplier η Z 1) Y v, 0] := by
  have h := ((contDiffAt_compactConnectionCoordinates_two hF hB).differentiableAt (by norm_num)).hasFDerivAt
  have hc (i : Fin 4) := (hasFDerivAt_apply (𝕜 := ℝ) i (compactConnectionCoordinates η Y)).comp Y h
  ext i
  fin_cases i
  · exact congrArg (fun L : CoreAngleState →L[ℝ] ℝ => L v)
      ((hc 0).unique ((hF.differentiableAt (by norm_num)).hasFDerivAt))
  · have H := (hc 1).unique ((hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 3) Y).mul
      (((hB 0).differentiableAt (by norm_num)).hasFDerivAt))
    have H' := congrArg (fun L : CoreAngleState →L[ℝ] ℝ => L v) H
    change fderiv ℝ (compactConnectionCoordinates η) Y v 1 =
      v 1 * coreTailMultiplier η Y 0 + Y 1 * fderiv ℝ (fun Z => coreTailMultiplier η Z 0) Y v
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, add_apply,
      smul_apply, smul_eq_mul, mul_comm, add_comm] using H'
  · have H := (hc 2).unique ((hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 3) Y).mul
      (((hB 1).differentiableAt (by norm_num)).hasFDerivAt))
    have H' := congrArg (fun L : CoreAngleState →L[ℝ] ℝ => L v) H
    change fderiv ℝ (compactConnectionCoordinates η) Y v 2 =
      v 2 * coreTailMultiplier η Y 1 + Y 2 * fderiv ℝ (fun Z => coreTailMultiplier η Z 1) Y v
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, add_apply,
      smul_apply, smul_eq_mul, mul_comm, add_comm] using H'
  · exact congrArg (fun L : CoreAngleState →L[ℝ] ℝ => L v)
      ((hc 3).unique (hasFDerivAt_const η Y))

/-- Actual coordinate identities hold on neighborhoods, including the ends of the compact interval. -/
theorem exists_compact_connection_coordinate_bounds {η : ℝ} (hη : 0 < η ∧ η ≤ 1 / 10000) :
    ∃ ε > (0 : ℝ), ∃ A : ℝ, 1 ≤ A ∧ ∀ Y : CoreAngleState,
      (31 / 8 ≤ Y 0 ∧ Y 0 ≤ 6) → |Y 1| ≤ ε → |Y 2| ≤ ε →
      (∀ᶠ Z in 𝓝 Y, coreTailValid η Z) ∧ ContDiffAt ℝ 2 (compactConnectionFinitePhase η) Y ∧
        ‖fderiv ℝ (compactConnectionFinitePhase η) Y‖ ≤ A ∧
        ∀ i : Fin 2, ContDiffAt ℝ 2 (fun Z => coreTailMultiplier η Z i) Y ∧
          0 < coreTailMultiplier η Y i ∧ coreTailMultiplier η Y i ≤ A ∧
          ‖fderiv ℝ (fun Z => coreTailMultiplier η Z i) Y‖ ≤ A := by
  let F := compactConnectionFinitePhase η
  let B := coreTailMultiplier η
  let G : Set CoreAngleState := {Y | 1 < Y 0 ∧ coreTailValid η Y ∧
    ContDiffAt ℝ 2 (coreTailTime η) Y ∧ ContDiffAt ℝ 2 F Y}
  let S : Set CoreAngleState := (fun k : ℝ => (![k, 0, 0] : CoreAngleState)) '' Icc (31 / 8) 6
  have hS : IsCompact S := isCompact_Icc.image (by fun_prop)
  have hSG : S ⊆ interior G := by
    rintro Y ⟨k, hk, rfl⟩
    have hk1 : 1 < k := by linarith only [hk.1]
    have H := coreTail_reference_regular hk1 ⟨hη.1, by linarith [hη.2]⟩
    have hcoord : ∀ᶠ Y : CoreAngleState in 𝓝 ![k, 0, 0], 1 < Y 0 :=
      ((continuous_apply 0).continuousAt : ContinuousAt (fun Y : CoreAngleState => Y 0) ![k, 0, 0]).eventually (lt_mem_nhds hk1)
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [hcoord, H.2.2.2.2, H.2.2.1.eventually (by norm_num),
      (contDiffAt_compactConnectionFinitePhase_reference (by linarith only [hk.1]) hη).eventually (by norm_num)]
      with Z hkZ hv ht hf
    exact ⟨hkZ, hv, ht, hf⟩
  obtain ⟨ε, hε, hεG⟩ := hS.exists_cthickening_subset_open isOpen_interior hSG
  let W := cthickening ε S
  have hWG : W ⊆ G := hεG.trans interior_subset
  have hreg (Y : CoreAngleState) (hY : Y ∈ W) (i : Fin 2) :
      ContDiffAt ℝ 2 (fun Z => B Z i) Y :=
    (contDiffAt_coreTailMultiplier_two (hWG hY).1 (hWG hY).2.1 (hWG hY).2.2.1 i).1
  let q := fun Y => ‖fderiv ℝ F Y‖ +
    (B Y 0 + ‖fderiv ℝ (fun Z => B Z 0) Y‖) + (B Y 1 + ‖fderiv ℝ (fun Z => B Z 1) Y‖)
  have hq : ContinuousOn q W := by
    intro Y hY
    have hF := (hWG hY).2.2.2
    have hb (i : Fin 2) := (hreg Y hY i).continuousAt.add
      ((hreg Y hY i).continuousAt_fderiv (by norm_num)).norm
    exact (((hF.continuousAt_fderiv (by norm_num)).norm.add (hb 0)).add (hb 1)).continuousWithinAt
  obtain ⟨C, hC⟩ := hS.cthickening.exists_bound_of_continuousOn hq
  refine ⟨ε, hε, max C 1, le_max_right _ _, ?_⟩
  intro Y hk hu hw
  have hd : dist Y (![Y 0, 0, 0] : CoreAngleState) ≤ ε := by
    apply (dist_pi_le_iff hε.le).mpr
    intro i
    fin_cases i
    · simpa using hε.le
    · simpa [Real.dist_eq] using hu
    · simpa [Real.dist_eq] using hw
  have hY : Y ∈ W := mem_cthickening_of_dist_le Y _ ε S ⟨Y 0, hk, rfl⟩ hd
  have hloc : ∀ᶠ Z in 𝓝 Y, coreTailValid η Z := by
    have H : ∀ᶠ Z in 𝓝 Y, Z ∈ G := mem_interior_iff_mem_nhds.mp (hεG hY)
    exact H.mono (fun _ hz => hz.2.1)
  have Hb : q Y ≤ max C 1 := (le_abs_self _).trans ((hC Y hY).trans (le_max_left _ _))
  have hp0 : 0 ≤ B Y 0 := (coreTailMultiplier_pos η Y 0).le
  have hp1 : 0 ≤ B Y 1 := (coreTailMultiplier_pos η Y 1).le
  dsimp only [q] at Hb
  refine ⟨hloc, (hWG hY).2.2.2, ?_, ?_⟩
  · linarith only [Hb, hp0, hp1, norm_nonneg (fderiv ℝ (fun Z => B Z 0) Y), norm_nonneg (fderiv ℝ (fun Z => B Z 1) Y)]
  · intro i
    have H0 : B Y 0 ≤ max C 1 ∧ ‖fderiv ℝ (fun Z => B Z 0) Y‖ ≤ max C 1 := by
      constructor <;> linarith only [Hb, hp0, hp1, norm_nonneg (fderiv ℝ F Y),
        norm_nonneg (fderiv ℝ (fun Z => B Z 0) Y), norm_nonneg (fderiv ℝ (fun Z => B Z 1) Y)]
    have H1 : B Y 1 ≤ max C 1 ∧ ‖fderiv ℝ (fun Z => B Z 1) Y‖ ≤ max C 1 := by
      constructor <;> linarith only [Hb, hp0, hp1, norm_nonneg (fderiv ℝ F Y),
        norm_nonneg (fderiv ℝ (fun Z => B Z 0) Y), norm_nonneg (fderiv ℝ (fun Z => B Z 1) Y)]
    refine ⟨hreg Y hY i, coreTailMultiplier_pos η Y i, ?_⟩
    fin_cases i
    · exact H0
    · exact H1

end BianchiIX
