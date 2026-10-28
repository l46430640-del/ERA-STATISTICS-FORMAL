import BianchiIX.Dynamics.SingleWallReference
import Mathlib.Topology.MetricSpace.Thickening

noncomputable section

namespace BianchiIX

open Set Filter Metric
open scoped Topology

theorem continuous_referenceEntranceState :
    Continuous (fun p : ℝ × ℝ => referenceEntranceState p.1 p.2) := by
  unfold referenceEntranceState
  fun_prop

/-- A compact rectangle of reference entrances has one smooth first-event neighborhood. -/
theorem exists_compact_referenceEntrance_return {K a : ℝ} (ha : 0 < a) :
    ∃ δ > (0 : ℝ), ∃ C ≥ (1 : ℝ), ∀ k ∈ Icc 2 K, ∀ v ∈ Icc a (1 / 2),
      ∀ y : ProjectiveState, ‖y - referenceEntranceState k v‖ ≤ δ →
        entranceReturnValid y ∧ ContDiffAt ℝ 2 entranceReturnTime y ∧
        ContDiffAt ℝ 2 entranceReturnState y ∧
        (0 < entranceReturnTime y ∧ entranceReturnTime y ≤ C) ∧
        ‖entranceReturnState y - entranceReturnState (referenceEntranceState k v)‖ ≤
          C * ‖y - referenceEntranceState k v‖ ∧
        |entranceReturnTime y - entranceReturnTime (referenceEntranceState k v)| ≤
          C * ‖y - referenceEntranceState k v‖ := by
  let S : Set ProjectiveState := (fun p : ℝ × ℝ => referenceEntranceState p.1 p.2) ''
    (Icc 2 K ×ˢ Icc a (1 / 2))
  have hS : IsCompact S := (isCompact_Icc.prod isCompact_Icc).image continuous_referenceEntranceState
  let G : Set ProjectiveState := {y | entranceReturnValid y ∧ ContDiffAt ℝ 2 entranceReturnTime y ∧
    ContDiffAt ℝ 2 entranceReturnState y}
  have hSG : S ⊆ interior G := by
    rintro y ⟨⟨k, v⟩, ⟨hk, hv⟩, rfl⟩
    have hk0 : 0 < k := by linarith only [hk.1]
    have hv0 : 0 < v := ha.trans_le hv.1
    have hvk : v < k := by linarith only [hk.1, hv.2]
    apply mem_interior_iff_mem_nhds.mpr
    exact entranceReturn_regular_germ (y := referenceEntranceState k v)
      (by rw [referenceEntrance_radius hk0 ⟨hv0, hvk⟩]; linarith only [hk.1])
      (show 1 ≤ referenceEntranceState k v 0 from le_add_of_nonneg_right (Real.sqrt_nonneg _))
      (by dsimp [referenceEntranceState]; norm_num)
      (by change 0 < v ∧ v < 1; exact ⟨hv0, by linarith only [hv.2]⟩)
      (by dsimp [referenceEntranceState]; norm_num)
  obtain ⟨δ, hδ, hδG⟩ := hS.exists_cthickening_subset_open isOpen_interior hSG
  let W := cthickening δ S
  have hWG : W ⊆ G := hδG.trans interior_subset
  let b : ProjectiveState → ℝ := fun y => |entranceReturnTime y| +
    ‖fderiv ℝ entranceReturnTime y‖ + ‖fderiv ℝ entranceReturnState y‖
  have hb : ContinuousOn b W := by
    intro y hy
    obtain ⟨_, ht, hP⟩ := hWG hy
    exact ((ht.continuousAt.abs.add (ht.continuousAt_fderiv (by norm_num)).norm).add
      (hP.continuousAt_fderiv (by norm_num)).norm).continuousWithinAt
  obtain ⟨B, hB⟩ := hS.cthickening.exists_bound_of_continuousOn hb
  let C := max B 1
  have HB (y : ProjectiveState) (hy : y ∈ W) :
      |entranceReturnTime y| ≤ C ∧ ‖fderiv ℝ entranceReturnTime y‖ ≤ C ∧
        ‖fderiv ℝ entranceReturnState y‖ ≤ C := by
    have H : b y ≤ C := (le_abs_self _).trans ((hB y hy).trans (le_max_left _ _))
    dsimp [b] at H
    have h0 := abs_nonneg (entranceReturnTime y)
    have h1 := norm_nonneg (fderiv ℝ entranceReturnTime y)
    have h2 := norm_nonneg (fderiv ℝ entranceReturnState y)
    exact ⟨by linarith only [H, h1, h2], by linarith only [H, h0, h2], by linarith only [H, h0, h1]⟩
  refine ⟨δ, hδ, C, le_max_right _ _, ?_⟩
  intro k hk v hv y hy
  let q := referenceEntranceState k v
  have hqS : q ∈ S := ⟨(k, v), ⟨hk, hv⟩, rfl⟩
  have hball (p : ProjectiveState) (hp : p ∈ closedBall q δ) : p ∈ W :=
    mem_cthickening_of_dist_le p q δ S hqS hp
  have hbase : q ∈ closedBall q δ := mem_closedBall_self hδ.le
  have hnear : y ∈ closedBall q δ := by simpa only [mem_closedBall, dist_eq_norm] using hy
  obtain ⟨hvalid, ht, hP⟩ := hWG (hball y hnear)
  have htime := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun p hp => (hWG (hball p hp)).2.1.differentiableAt (by norm_num))
    (fun p hp => (HB p (hball p hp)).2.1) (convex_closedBall q δ) hbase hnear
  have hstate := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun p hp => (hWG (hball p hp)).2.2.differentiableAt (by norm_num))
    (fun p hp => (HB p (hball p hp)).2.2) (convex_closedBall q δ) hbase hnear
  exact ⟨hvalid, ht, hP, ⟨hvalid.1.1.1, (le_abs_self _).trans (HB y (hball y hnear)).1⟩,
    hstate, by simpa only [Real.norm_eq_abs] using htime⟩

end BianchiIX
