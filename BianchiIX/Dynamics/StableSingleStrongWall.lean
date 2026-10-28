import BianchiIX.Algebra.SingleStrongWall
import BianchiIX.Dynamics.StableBoundaryRescaling

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem stableOriginalFlow_single_strong_region {m c u t : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 40) (hu : |u| ≤ 1 / 200) (ht : 0 ≤ t) :
    1 < stableOriginalFlow ![m, u, 0] t 0 ∧ stableOriginalFlow ![m, u, 0] t 2 = 0 := by
  have H := stableBoundaryOrbit_global hc hm hu (by norm_num : |(0 : ℝ)| ≤ 1 / 200) t ht
  have hM : |stableOriginalFlow ![m, u, 0] t 0 - c| ≤ 1 / 10 := by
    simpa [stableOriginalFlow_eq, stableRestriction_apply] using H.2.1.1
  have hW : |stableOriginalFlow ![m, u, 0] t 2| ≤ 0 := by
    simpa [stableOriginalFlow_eq, stableRestriction_apply] using H.2.2.2.2
  exact ⟨by linarith [(abs_le.mp hM).1], abs_eq_zero.mp (le_antisymm hW (abs_nonneg _))⟩

theorem hasDerivAt_stableSingleStrongInvariant {m c u t : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 40) (hu : |u| ≤ 1 / 200) (ht : 0 ≤ t) :
    HasDerivAt (fun s => singleStrongInvariant (stableOriginalFlow ![m, u, 0] s 0)
      (stableOriginalFlow ![m, u, 0] s 1)) 0 t := by
  have H := hasDerivAt_stableOriginalFlow (y := ![m, u, 0]) hc hm hu
    (by change |(0 : ℝ)| ≤ 1 / 200; norm_num) ht
  obtain ⟨hM, hW⟩ := stableOriginalFlow_single_strong_region hc hm hu ht
  apply hasDerivAt_singleStrongInvariant (a := 6 / stableBoundaryDenom (stableOriginalFlow ![m, u, 0] t))
  · simpa [stableOriginalField, stableBoundaryField, hW] using hasDerivAt_pi.mp H 0
  · simpa [stableOriginalField, stableBoundaryField, stableStrongRate, hW] using hasDerivAt_pi.mp H 1
  · linarith

theorem stableSingleStrongInvariant_constant {m c u t : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 40) (hu : |u| ≤ 1 / 200) (ht : 0 ≤ t) :
    singleStrongInvariant (stableOriginalFlow ![m, u, 0] t 0) (stableOriginalFlow ![m, u, 0] t 1) =
      singleStrongInvariant m u := by
  have H := (convex_Ici (0 : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs => (hasDerivAt_stableSingleStrongInvariant hc hm hu hs).hasDerivWithinAt)
    (C := 0) (fun _ _ => by simp) (by simp : (0 : ℝ) ∈ Ici 0) ht
  simpa [sub_eq_zero, stableOriginalFlow_initial] using H

theorem stableSingleStrongPhase_constant {m c u t : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 40) (hu : |u| ≤ 1 / 200) (ht : 0 ≤ t) :
    singleStrongPhase (stableOriginalFlow ![m, u, 0] t 0) (stableOriginalFlow ![m, u, 0] t 1) =
      singleStrongPhase m u := by
  unfold singleStrongPhase
  rw [stableSingleStrongInvariant_constant hc hm hu ht]

theorem stableBoundaryProjection_single_strong_invariant {m c u : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 40) (hu : |u| ≤ 1 / 200) :
    singleStrongInvariant (stableBoundaryProjection m u 0) 0 = singleStrongInvariant m u := by
  have hP : 1 < stableBoundaryProjection m u 0 := by
    have H := (abs_le.mp (stableBoundaryProjection_band (w := 0) hc hm hu (by norm_num))).1
    linarith
  have hlim := stableOriginalFlow_limit (y := ![m, u, 0]) hc hm hu
    (by change |(0 : ℝ)| ≤ 1 / 200; norm_num)
  have hreg := contDiffAt_singleStrongInvariant 0 (y := ![stableBoundaryProjection m u 0, 0, 0]) (by simpa using (ne_of_gt (show 0 < stableBoundaryProjection m u 0 by linarith)))
  have H := hreg.continuousAt.tendsto.comp hlim
  have heq : (fun t => singleStrongInvariant (stableOriginalFlow ![m, u, 0] t 0)
      (stableOriginalFlow ![m, u, 0] t 1)) =ᶠ[atTop] (fun _ => singleStrongInvariant m u) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact stableSingleStrongInvariant_constant hc hm hu ht
  exact tendsto_nhds_unique H ((tendsto_congr' heq).mpr tendsto_const_nhds)

theorem stableBoundaryProjection_strong {m c u : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 40) (hu : |u| ≤ 1 / 200) :
    stableBoundaryProjection m u 0 = singleStrongUpperRoot (singleStrongInvariant m u) := by
  have hm1 : 1 < m := by linarith [(abs_le.mp hm).1]
  have hI := singleStrongInvariant_gt_two (u := u) (by linarith : 0 < m) (Or.inl (ne_of_gt hm1))
  have hP : 1 < stableBoundaryProjection m u 0 := by
    have H := (abs_le.mp (stableBoundaryProjection_band (w := 0) hc hm hu (by norm_num))).1
    linarith
  apply singleStrongUpperRoot_unique hI hP
  have H := stableBoundaryProjection_single_strong_invariant hc hm hu
  have hP0 : stableBoundaryProjection m u 0 ≠ 0 := by linarith
  unfold singleStrongInvariant at H
  simp only [zero_pow (by norm_num : 2 ≠ 0), add_zero] at H
  have H' := (div_eq_iff hP0).mp H
  dsimp [singleStrongInvariant]
  nlinarith only [H']

theorem stableBoundaryProjection_strong_ge {m u : ℝ} (hm : 2 ≤ m) (hu : |u| ≤ 1 / 200) :
    m ≤ stableBoundaryProjection m u 0 := by
  rw [stableBoundaryProjection_strong hm (by simp) hu]
  exact singleStrongUpperRoot_ge (by linarith)

end BianchiIX
