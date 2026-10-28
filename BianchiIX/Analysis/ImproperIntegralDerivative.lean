import BianchiIX.Analysis.ParametricDerivatives
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem hasFDerivAt_integral_Ioi_of_contDiffAt {f : ℝ × E → F} {U : Set E} {x : E}
    {T : ℝ} {B : ℝ → ℝ} (hU : IsOpen U) (hx : x ∈ U)
    (hreg : ∀ z ∈ U, ∀ t ∈ Ioi T, ContDiffAt ℝ 1 f (t, z))
    (hint : IntegrableOn (fun t => f (t, x)) (Ioi T))
    (hB : IntegrableOn B (Ioi T))
    (hbound : ∀ z ∈ U, ∀ t ∈ Ioi T, ‖fderiv ℝ (fun y => f (t, y)) z‖ ≤ B t) :
    IntegrableOn (fun t => fderiv ℝ (fun y => f (t, y)) x) (Ioi T) ∧
      HasFDerivAt (fun y => ∫ t in Ioi T, f (t, y))
        (∫ t in Ioi T, fderiv ℝ (fun y => f (t, y)) x) x := by
  have hc (z : E) (hz : z ∈ U) : ContinuousOn (fun t => f (t, z)) (Ioi T) := by
    intro t ht
    exact ((hreg z hz t ht).continuousAt.comp (f := fun r : ℝ => (r, z))
      (continuousAt_id.prodMk continuousAt_const)).continuousWithinAt
  have hdc : ContinuousOn (fun t => fderiv ℝ (fun y => f (t, y)) x) (Ioi T) := by
    intro t ht
    have H := contDiffAt_partial_fderiv (hreg x hx t ht) (by norm_num : (0 : WithTop ℕ∞) + 1 ≤ 1)
    exact (H.continuousAt.comp (f := fun r : ℝ => (r, x))
      (continuousAt_id.prodMk continuousAt_const)).continuousWithinAt
  have hmeas := hdc.aestronglyMeasurable (μ := volume) measurableSet_Ioi
  have hpoint : ∀ᵐ t ∂volume.restrict (Ioi T), ‖fderiv ℝ (fun y => f (t, y)) x‖ ≤ B t :=
    (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall (fun t ht => hbound x hx t ht))
  have hnear : ∀ᶠ z in 𝓝 x, AEStronglyMeasurable (fun t => f (t, z)) (volume.restrict (Ioi T)) := by
    filter_upwards [hU.mem_nhds hx] with z hz
    exact (hc z hz).aestronglyMeasurable measurableSet_Ioi
  have hbnd : ∀ᵐ t ∂volume.restrict (Ioi T), ∀ z ∈ U, ‖fderiv ℝ (fun y => f (t, y)) z‖ ≤ B t :=
    (ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall (fun t ht z hz => hbound z hz t ht))
  have hdiff : ∀ᵐ t ∂volume.restrict (Ioi T), ∀ z ∈ U,
      HasFDerivAt (fun y => f (t, y)) (fderiv ℝ (fun y => f (t, y)) z) z := by
    apply (ae_restrict_iff' measurableSet_Ioi).mpr
    exact Eventually.of_forall (fun t ht z hz =>
      (((hreg z hz t ht).comp (f := fun y : E => (t, y)) z
        (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by norm_num)).hasFDerivAt)
  exact ⟨hB.mono' hmeas hpoint, hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun y t => f (t, y)) (F' := fun y t => fderiv ℝ (fun z => f (t, z)) y)
    (s := U) (bound := B) (hU.mem_nhds hx) hnear hint hmeas hbnd hB hdiff⟩

-- Fix the operator norm structure before forming the second operator space.
local instance : NormedAddCommGroup (E →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] F) := inferInstance

theorem fderiv2_integral_Ioi_of_contDiffAt {f : ℝ × E → F} {U : Set E} {x : E}
    {T : ℝ} {B : ℝ → ℝ} (hU : IsOpen U) (hx : x ∈ U)
    (hreg : ∀ z ∈ U, ∀ t ∈ Ioi T, ContDiffAt ℝ 2 f (t, z))
    (hint : ∀ z ∈ U, IntegrableOn (fun t => f (t, z)) (Ioi T))
    (hB : IntegrableOn B (Ioi T))
    (hbound1 : ∀ z ∈ U, ∀ t ∈ Ioi T, ‖fderiv ℝ (fun y => f (t, y)) z‖ ≤ B t)
    (hbound2 : ∀ z ∈ U, ∀ t ∈ Ioi T, ‖fderiv ℝ (fderiv ℝ (fun y => f (t, y))) z‖ ≤ B t) :
    IntegrableOn (fun t => fderiv ℝ (fun y => f (t, y)) x) (Ioi T) ∧
      IntegrableOn (fun t => fderiv ℝ (fderiv ℝ (fun y => f (t, y))) x) (Ioi T) ∧
      fderiv ℝ (fun y => ∫ t in Ioi T, f (t, y)) x =
        (∫ t in Ioi T, fderiv ℝ (fun y => f (t, y)) x) ∧
      fderiv ℝ (fderiv ℝ (fun y => ∫ t in Ioi T, f (t, y))) x =
        ∫ t in Ioi T, fderiv ℝ (fderiv ℝ (fun y => f (t, y))) x := by
  have hfirst (z : E) (hz : z ∈ U) := hasFDerivAt_integral_Ioi_of_contDiffAt hU hz
    (fun y hy t ht => (hreg y hy t ht).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2))
    (hint z hz) hB hbound1
  have hsecond := hasFDerivAt_integral_Ioi_of_contDiffAt (f := fun p : ℝ × E =>
      fderiv ℝ (fun y => f (p.1, y)) p.2) hU hx
    (fun y hy t ht => contDiffAt_partial_fderiv (hreg y hy t ht) (by norm_num))
    (hfirst x hx).1 hB hbound2
  have heq : fderiv ℝ (fun y => ∫ t in Ioi T, f (t, y)) =ᶠ[𝓝 x]
      (fun y => ∫ t in Ioi T, fderiv ℝ (fun z => f (t, z)) y) := by
    filter_upwards [hU.mem_nhds hx] with z hz
    exact (hfirst z hz).2.fderiv
  exact ⟨(hfirst x hx).1, hsecond.1, (hfirst x hx).2.fderiv,
    heq.fderiv_eq.trans hsecond.2.fderiv⟩

end BianchiIX
