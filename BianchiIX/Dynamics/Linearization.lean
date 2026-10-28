import BianchiIX.Dynamics.LocalDependence

noncomputable section

namespace BianchiIX

open Set Filter Metric
open scoped Topology NNReal

abbrev NormalizedVariation := NormalizedState →L[ℝ] NormalizedState

def normalizedDifferential (x : NormalizedState) : NormalizedVariation :=
  fderiv ℝ normalizedField x

theorem hasFDerivAt_normalizedField (x : NormalizedState) :
    HasFDerivAt normalizedField (normalizedDifferential x) x :=
  ((contDiff_normalizedField 1).differentiable (by norm_num) x).hasFDerivAt

theorem contDiff_normalizedDifferential (n : WithTop ℕ∞) :
    ContDiff ℝ n normalizedDifferential :=
  (contDiff_normalizedField (n + 1)).fderiv_right le_rfl

theorem normalizedDifferential_lipschitz_closedBall (x : NormalizedState) (r : ℝ) :
    ∃ K : ℝ≥0, LipschitzOnWith K normalizedDifferential (closedBall x r) :=
  (contDiff_normalizedDifferential 1).contDiffOn.exists_lipschitzOnWith (by norm_num)
    (convex_closedBall x r) (isCompact_closedBall x r)

/-- A uniform quadratic Taylor bound, without selecting second derivative coordinates. -/
theorem normalizedField_quadratic_remainder {S : Set NormalizedState} (hS : Convex ℝ S)
    {K : ℝ≥0} (hK : LipschitzOnWith K normalizedDifferential S)
    {x y : NormalizedState} (hx : x ∈ S) (hy : y ∈ S) :
    ‖normalizedField y - normalizedField x - normalizedDifferential x (y - x)‖ ≤
      K * ‖y - x‖ ^ 2 := by
  let g : NormalizedState → NormalizedState := fun z => normalizedField z - normalizedDifferential x z
  have hg (z : NormalizedState) :
      HasFDerivAt g (normalizedDifferential z - normalizedDifferential x) z :=
    (hasFDerivAt_normalizedField z).sub (normalizedDifferential x).hasFDerivAt
  have hbound (z : NormalizedState) (hz : z ∈ segment ℝ x y) :
      ‖normalizedDifferential z - normalizedDifferential x‖ ≤ K * ‖y - x‖ :=
    (hK.norm_sub_le (hS.segment_subset hx hy hz) hx).trans
      (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hz) K.coe_nonneg)
  have H := (convex_segment x y).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (hg z).hasFDerivWithinAt) hbound (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  simpa only [g, map_sub, sub_sub_sub_comm, pow_two, mul_assoc] using H

def normalizedTangentField (z : NormalizedState × NormalizedVariation) :
    NormalizedState × NormalizedVariation :=
  (normalizedField z.1, (normalizedDifferential z.1).comp z.2)

theorem contDiff_normalizedTangentField (n : WithTop ℕ∞) :
    ContDiff ℝ n normalizedTangentField :=
  ((contDiff_normalizedField n).comp contDiff_fst).prodMk
    (((contDiff_normalizedDifferential n).comp contDiff_fst).clm_comp contDiff_snd)

end BianchiIX
