import BianchiIX.Dynamics.EntrancePhysicalBounds

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

theorem clm_four_coordinate_bound (L : ProjectiveState →L[ℝ] ℝ) (d : ProjectiveState) :
    |L d| ≤ |d 0| * |L (Pi.single 0 1)| + |d 1| * |L (Pi.single 1 1)| +
      |d 2| * |L (Pi.single 2 1)| + |d 3| * |L (Pi.single 3 1)| := by
  have hd : d = d 0 • Pi.single 0 1 + d 1 • Pi.single 1 1 +
      d 2 • Pi.single 2 1 + d 3 • Pi.single 3 1 := by
    ext i
    fin_cases i <;> simp
  conv_lhs => rw [hd, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul]
  simpa only [smul_eq_mul, abs_mul] using
    (abs_add_le (d 0 * L (Pi.single 0 1) + d 1 * L (Pi.single 1 1) + d 2 * L (Pi.single 2 1))
      (d 3 * L (Pi.single 3 1))).trans (add_le_add
        ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)

/-- Relative wall directions cancel the apparent singularity at a small active wall. -/
theorem entrance_physical_columns_direction {C D k U V W : ℝ}
    {L : ProjectiveState →L[ℝ] ℝ} {d : ProjectiveState}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hk : 1 ≤ k)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W ∧ W ≤ 1)
    (hr : |L (Pi.single 0 1) - 1| ≤ C * (U * V + V ^ 2 * (U + W) ^ 2) / k ^ 2)
    (hu : |L (Pi.single 1 1)| ≤ C * (V + V ^ 2 * (U + W)) / k)
    (hv : |L (Pi.single 2 1)| ≤ C * (U + V * (U + W) ^ 2))
    (hw : |L (Pi.single 3 1)| ≤ C * (U * V + V ^ 2 * (U + W)) / k)
    (hd0 : |d 0| ≤ D * k ^ 2) (hd1 : |d 1| ≤ D * k * U)
    (hd2 : |d 2| ≤ D * k * V) (hd3 : |d 3| ≤ D * k * W) :
    |L d - d 0| ≤ 4 * C * D * k * (U * V + V ^ 2 * (U + W) ^ 2) := by
  let H := U * V + V ^ 2 * (U + W) ^ 2
  have hk0 : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have h1 : U * (V + V ^ 2 * (U + W)) ≤ H := by
    dsimp only [H]
    nlinarith only [mul_nonneg (mul_nonneg (sq_nonneg V) (add_nonneg hU hW.1)) hW.1]
  have h3 : W * (U * V + V ^ 2 * (U + W)) ≤ H := by
    dsimp only [H]
    nlinarith only [mul_nonneg (mul_nonneg hU hV) (sub_nonneg.mpr hW.2),
      mul_nonneg (mul_nonneg (sq_nonneg V) (add_nonneg hU hW.1)) hU]
  have hbase := clm_four_coordinate_bound
    (L - (ContinuousLinearMap.proj 0 : ProjectiveState →L[ℝ] ℝ)) d
  simp only [sub_apply, ContinuousLinearMap.proj_apply, Pi.single_eq_same,
    Pi.single_eq_of_ne (by decide : (0 : Fin 4) ≠ 1),
    Pi.single_eq_of_ne (by decide : (0 : Fin 4) ≠ 2),
    Pi.single_eq_of_ne (by decide : (0 : Fin 4) ≠ 3), sub_zero] at hbase
  have hscale : C * D * H ≤ C * D * k * H := by
    nlinarith only [mul_le_mul_of_nonneg_left hk (by positivity : 0 ≤ C * D * H)]
  calc
    _ ≤ _ := hbase
    _ ≤ (D * k ^ 2) * (C * H / k ^ 2) +
        (D * k * U) * (C * (V + V ^ 2 * (U + W)) / k) +
        (D * k * V) * (C * (U + V * (U + W) ^ 2)) +
        (D * k * W) * (C * (U * V + V ^ 2 * (U + W)) / k) := by
      exact add_le_add (add_le_add (add_le_add
        (mul_le_mul hd0 hr (abs_nonneg _) (by positivity))
        (mul_le_mul hd1 hu (abs_nonneg _) (by positivity)))
        (mul_le_mul hd2 hv (abs_nonneg _) (by positivity)))
        (mul_le_mul hd3 hw (abs_nonneg _) (by positivity [hW.1]))
    _ = C * D * H + C * D * (U * (V + V ^ 2 * (U + W))) +
        C * D * k * H + C * D * (W * (U * V + V ^ 2 * (U + W))) := by
      dsimp only [H]
      field_simp
    _ ≤ C * D * H + C * D * H + C * D * k * H + C * D * H := by
      gcongr
    _ ≤ _ := by nlinarith only [hscale]

/-- The bounds concern the physical arrival as a function of the original projective data. -/
theorem exists_entrance_physical_direction_bounds :
    ∃ C > (0 : ℝ), ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧
      ∀ y : ProjectiveState,
      let k := coreRadius (y 0) (y 2)
      let R := fun p : ProjectiveState => coreRadius (entranceReturnState p 0) (entranceReturnState p 2)
      let H := y 1 * y 2 + (y 2) ^ 2 * (y 1 + y 3) ^ 2
      7 / 4 ≤ k → 2 ≤ y 0 → (0 < y 1 ∧ y 1 ≤ ε) → (0 < y 2 ∧ y 2 < 1) →
      (0 < y 3 ∧ y 3 ≤ ε) →
      ContDiffAt ℝ 2 R y ∧ |R y - entranceStableRadius y| ≤ C * H / k ∧
      ∀ (D : ℝ) (d : ProjectiveState), 0 ≤ D →
        |fderiv ℝ entranceStableRadius y d| ≤ D * k ^ 2 →
        (∀ i : Fin 4, i ≠ 0 → |d i| ≤ D * k * y i) →
        |fderiv ℝ R y d - fderiv ℝ entranceStableRadius y d| ≤ C * D * k * H := by
  obtain ⟨A, hA, ε, hε, hεsmall, HA⟩ := exists_entrance_physical_basic_bounds
  refine ⟨4 * A, by positivity, ε, hε, hεsmall, ?_⟩
  intro y k R H hk hm hu hv hw
  obtain ⟨Ψ, HΨ, HF, Hval, Hr, Hu, Hv, Hw⟩ := HA y hk (by linarith only [hm]) hu hv hw
  let z := entranceRadialCoordinates y
  let F := fun z => R (Ψ z)
  have hu' : |y 1| < 1 / 200 := by rw [abs_of_pos hu.1]; linarith only [hu.2, hεsmall]
  have hw' : |y 3| < 1 / 200 := by rw [abs_of_pos hw.1]; linarith only [hw.2, hεsmall]
  have hcoord := contDiffAt_entranceRadialCoordinates_two hm hu' hw' hv.1
  have heq : R =ᶠ[𝓝 y] (F ∘ entranceRadialCoordinates) := by
    filter_upwards [HΨ.left_inverse] with p hp
    change R p = R (Ψ (entranceRadialCoordinates p))
    rw [hp]
  have Hreg : ContDiffAt ℝ 2 R y := (HF.comp y hcoord).congr_of_eventuallyEq heq
  have Hd : HasFDerivAt R ((fderiv ℝ F z).comp (entranceRadialDifferential y)) y :=
    (((HF.differentiableAt (by norm_num)).hasFDerivAt).comp y
      (hasFDerivAt_entranceRadialCoordinates hm hu' hw' hv.1)).congr_of_eventuallyEq heq
  have Hval' : |R y - entranceStableRadius y| ≤ A * H / k := by
    change |R (Ψ (entranceRadialCoordinates y)) - entranceStableRadius y| ≤ A * H / k at Hval
    rwa [HΨ.apply_base] at Hval
  refine ⟨Hreg, Hval'.trans ?_, ?_⟩
  · have hH : 0 ≤ H := by dsimp only [H]; positivity [hu.1, hv.1]
    have hk0 : 0 ≤ k := by linarith only [hk]
    gcongr
    linarith only [hA]
  · intro D d hD hd0 hdwall
    let v := entranceRadialDifferential y d
    have hv0 : v 0 = fderiv ℝ entranceStableRadius y d := by simp [v, entranceRadialDifferential_apply]
    have hvwall (i : Fin 4) (hi : i ≠ 0) : v i = d i := by
      fin_cases i <;> simp_all [v, entranceRadialDifferential_apply]
    have HB := entrance_physical_columns_direction (d := v) hA.le hD (by linarith only [hk]) hu.1.le hv.1.le
      ⟨hw.1.le, by linarith only [hw.2, hεsmall]⟩ Hr Hu Hv Hw
      (by simpa only [hv0] using hd0)
      (by simpa only [hvwall 1 (by decide)] using hdwall 1 (by decide))
      (by simpa only [hvwall 2 (by decide)] using hdwall 2 (by decide))
      (by simpa only [hvwall 3 (by decide)] using hdwall 3 (by decide))
    rw [Hd.fderiv]
    change |fderiv ℝ F z v - fderiv ℝ entranceStableRadius y d| ≤ _
    rw [← hv0]
    exact HB

end BianchiIX
