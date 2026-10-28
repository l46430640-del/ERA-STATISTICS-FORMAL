import BianchiIX.Analysis.CompactParametricIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Compactness supplies a common neighborhood on which the parameter derivative is continuous. -/
theorem contDiffAt_intervalIntegral_of_contDiffAt {F : E × ℝ → ℝ} {x : E} {a b : ℝ}
    (hab : a ≤ b) (hF : ∀ t ∈ Icc a b, ContDiffAt ℝ 1 F (x, t)) :
    ContDiffAt ℝ 1 (fun y => ∫ t in a..b, F (y, t)) x := by
  let D : E × ℝ → E →L[ℝ] ℝ := fun p =>
    (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ E ℝ)
  have hDc {y : E} {t : ℝ} (h : ContDiffAt ℝ 1 F (y, t)) : ContinuousAt D (y, t) :=
    (h.continuousAt_fderiv (by norm_num)).clm_comp continuousAt_const
  have hDt : ContinuousOn (fun t => D (x, t)) (Icc a b) := fun t ht =>
    ((hDc (hF t ht)).comp (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hDt.norm
  let s : Set E := {y | ∀ t ∈ Icc a b, ContDiffAt ℝ 1 F (y, t) ∧ ‖D (y, t)‖ ≤ B + 1}
  have hs : s ∈ 𝓝 x := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro t ht
    have hlt : ‖D (x, t)‖ < B + 1 := (hB (mem_image_of_mem _ ht)).trans_lt (lt_add_one B)
    exact ((hF t ht).eventually (by norm_num)).and
      (((hDc (hF t ht)).norm.eventually (isOpen_Iio.mem_nhds hlt)).mono fun _ h => h.le)
  apply contDiffAt_one_iff.mpr
  refine ⟨fun y => ∫ t in a..b, D (y, t), s, hs, ?_, ?_⟩
  · intro y hy
    apply intervalIntegral.continuousWithinAt_of_dominated_interval (bound := fun _ => B + 1)
    · filter_upwards [self_mem_nhdsWithin] with z hz
      have hcont : ContinuousOn (fun t => D (z, t)) (Icc a b) := fun t ht =>
        ((hDc (hz t ht).1).comp (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
      rw [uIoc_of_le hab]
      exact (hcont.intervalIntegrable_of_Icc hab).1.aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact Eventually.of_forall fun t ht => (hz t (uIcc_of_le hab ▸ uIoc_subset_uIcc ht)).2
    · exact intervalIntegrable_const
    · exact Eventually.of_forall fun t ht =>
        ((hDc (hy t (uIcc_of_le hab ▸ uIoc_subset_uIcc ht)).1).comp
          (f := fun z : E => (z, t)) (g := D)
          (continuousAt_id.prodMk continuousAt_const)).continuousWithinAt
  · intro y hy
    exact hasFDerivAt_intervalIntegral_of_contDiffAt hab (fun t ht => (hy t ht).1)

theorem contDiffAt_moving_intervalIntegral_of_contDiffAt
    {F : E × ℝ → ℝ} {τ : E → ℝ} {x : E} (hτ : ContDiffAt ℝ 1 τ x) (hpos : 0 ≤ τ x)
    (hF : ∀ t ∈ Icc 0 (τ x), ContDiffAt ℝ 1 F (x, t)) :
    ContDiffAt ℝ 1 (fun y => ∫ t in 0..τ y, F (y, t)) x := by
  have hG (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ContDiffAt ℝ 1 (fun p : E × ℝ => τ p.1 * F (p.1, p.2 * τ p.1)) (x, t) := by
    have htime : t * τ x ∈ Icc 0 (τ x) :=
      ⟨mul_nonneg ht.1 hpos, by simpa using mul_le_mul_of_nonneg_right ht.2 hpos⟩
    have hcτ : ContDiffAt ℝ 1 (fun p : E × ℝ => τ p.1) (x, t) :=
      hτ.comp (x, t) contDiffAt_fst
    have hp : ContDiffAt ℝ 1 (fun p : E × ℝ => (p.1, p.2 * τ p.1)) (x, t) :=
      contDiffAt_fst.prodMk (contDiffAt_snd.mul hcτ)
    exact hcτ.mul ((hF _ htime).comp (x, t) (g := F)
      (f := fun p : E × ℝ => (p.1, p.2 * τ p.1)) hp)
  convert! contDiffAt_intervalIntegral_of_contDiffAt (by norm_num : (0 : ℝ) ≤ 1) hG using 1
  ext y
  exact integral_rescale_zero_one (fun t => F (y, t)) (τ y)

end BianchiIX
