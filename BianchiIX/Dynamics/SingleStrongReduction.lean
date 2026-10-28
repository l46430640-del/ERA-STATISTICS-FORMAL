import BianchiIX.Dynamics.SingleStrongChart

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem hasDerivAt_singleStrongFlow_invariant {m u t : ℝ}
    (hm : 0 < m) (hu : 0 < u) (ht : 0 ≤ t) :
    HasDerivAt (fun s => singleStrongInvariant (stableOriginalFlow ![m, u, 0] s 0)
      (stableOriginalFlow ![m, u, 0] s 1)) 0 t := by
  have H := hasDerivAt_singleStrongFlow hm hu ht
  obtain ⟨hM, _, hW, _⟩ := singleStrongFlow_global_region hm hu ht
  apply hasDerivAt_singleStrongInvariant (a := 6 / stableBoundaryDenom (stableOriginalFlow ![m, u, 0] t))
  · simpa [stableOriginalField, stableBoundaryField, hW] using hasDerivAt_pi.mp H 0
  · simpa [stableOriginalField, stableBoundaryField, stableStrongRate, hW] using hasDerivAt_pi.mp H 1
  · exact hM.ne'

theorem singleStrongFlow_invariant {m u t : ℝ} (hm : 0 < m) (hu : 0 < u) (ht : 0 ≤ t) :
    singleStrongInvariant (stableOriginalFlow ![m, u, 0] t 0) (stableOriginalFlow ![m, u, 0] t 1) =
      singleStrongInvariant m u := by
  have H := (convex_Ici (0 : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs => (hasDerivAt_singleStrongFlow_invariant hm hu hs).hasDerivWithinAt)
    (C := 0) (fun _ _ => by simp) (by simp : (0 : ℝ) ∈ Ici 0) ht
  simpa [sub_eq_zero, stableOriginalFlow_initial] using H

theorem singleStrongFlow_phase {m u t : ℝ} (hm : 0 < m) (hu : 0 < u) (ht : 0 ≤ t) :
    singleStrongPhase (stableOriginalFlow ![m, u, 0] t 0) (stableOriginalFlow ![m, u, 0] t 1) =
      singleStrongPhase m u := by
  unfold singleStrongPhase
  rw [singleStrongFlow_invariant hm hu ht]

theorem singleStrongFlow_bracket {m u t : ℝ} (hm : 0 < m) (hu : 0 < u) (ht : 0 ≤ t) :
    singleStrongLowerRoot (singleStrongInvariant m u) < stableOriginalFlow ![m, u, 0] t 0 ∧
      stableOriginalFlow ![m, u, 0] t 0 < singleStrongUpperRoot (singleStrongInvariant m u) := by
  obtain ⟨hM, hU, _, _⟩ := singleStrongFlow_global_region hm hu ht
  simpa only [singleStrongFlow_invariant hm hu ht] using singleStrongRoot_bracket hM hU.ne'

theorem singleStrongFlow_factorization {m u t : ℝ} (hm : 0 < m) (hu : 0 < u) (ht : 0 ≤ t) :
    stableOriginalFlow ![m, u, 0] t 1 ^ 2 =
      (stableOriginalFlow ![m, u, 0] t 0 - singleStrongLowerRoot (singleStrongInvariant m u)) *
      (singleStrongUpperRoot (singleStrongInvariant m u) - stableOriginalFlow ![m, u, 0] t 0) := by
  obtain ⟨hM, hU, _, _⟩ := singleStrongFlow_global_region hm hu ht
  have hI := singleStrongInvariant_gt_two hM (Or.inr hU.ne')
  simpa only [singleStrongFlow_invariant hm hu ht] using singleStrongInvariant_factorization hM hI

theorem singleStrongFlow_denom {m u t : ℝ} (hm : 0 < m) (hu : 0 < u) (ht : 0 ≤ t) :
    stableBoundaryDenom (stableOriginalFlow ![m, u, 0] t) =
      2 + singleStrongInvariant m u * stableOriginalFlow ![m, u, 0] t 0 := by
  obtain ⟨hM, _, hW, _⟩ := singleStrongFlow_global_region hm hu ht
  have H := singleStrongFlow_invariant hm hu ht
  unfold singleStrongInvariant at H
  have H' := (div_eq_iff hM.ne').mp H
  simp only [stableBoundaryDenom, hW, sub_zero]
  dsimp [singleStrongInvariant]
  linarith only [H']

theorem hasDerivAt_singleStrongFlow_mass {m u t : ℝ} (hm : 0 < m) (hu : 0 < u) (ht : 0 ≤ t) :
    HasDerivAt (fun s => stableOriginalFlow ![m, u, 0] s 0)
      (6 / stableBoundaryDenom (stableOriginalFlow ![m, u, 0] t) *
        (stableOriginalFlow ![m, u, 0] t 0 * stableOriginalFlow ![m, u, 0] t 1 ^ 2)) t := by
  have hW := (singleStrongFlow_global_region hm hu ht).2.2.1
  simpa [stableOriginalField, stableBoundaryField, hW] using
    hasDerivAt_pi.mp (hasDerivAt_singleStrongFlow hm hu ht) 0

theorem singleStrongFlow_strictMono {m u : ℝ} (hm : 0 < m) (hu : 0 < u) :
    StrictMonoOn (fun t => stableOriginalFlow ![m, u, 0] t 0) (Ici 0) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici (0 : ℝ))
    (HasDerivAt.continuousOn (fun t ht => hasDerivAt_singleStrongFlow_mass hm hu ht))
    (fun t ht => (hasDerivAt_singleStrongFlow_mass hm hu (interior_subset ht)).hasDerivWithinAt)
  intro t ht
  obtain ⟨hM, hU, _, _⟩ := singleStrongFlow_global_region hm hu (interior_subset ht)
  have hD := stableBoundaryDenom_pos (stableOriginalFlow ![m, u, 0] t)
  positivity

theorem singleStrongFlow_mass_ge {m u t : ℝ} (hm : 0 < m) (hu : 0 < u) (ht : 0 ≤ t) :
    m ≤ stableOriginalFlow ![m, u, 0] t 0 := by
  simpa [stableOriginalFlow_initial] using
    (singleStrongFlow_strictMono hm hu).monotoneOn (by simp : (0 : ℝ) ∈ Ici 0) ht ht

theorem hasDerivAt_singleStrongFlow_reduced {m u t : ℝ} (hm : 0 < m) (hu : 0 < u) (ht : 0 ≤ t) :
    HasDerivAt (fun s => stableOriginalFlow ![m, u, 0] s 0)
      (6 * stableOriginalFlow ![m, u, 0] t 0 *
        (stableOriginalFlow ![m, u, 0] t 0 - singleStrongLowerRoot (singleStrongInvariant m u)) /
        (2 + singleStrongInvariant m u * stableOriginalFlow ![m, u, 0] t 0) *
        (singleStrongUpperRoot (singleStrongInvariant m u) - stableOriginalFlow ![m, u, 0] t 0)) t := by
  convert hasDerivAt_singleStrongFlow_mass hm hu ht using 1
  rw [singleStrongFlow_factorization hm hu ht, singleStrongFlow_denom hm hu ht]
  ring

end BianchiIX
