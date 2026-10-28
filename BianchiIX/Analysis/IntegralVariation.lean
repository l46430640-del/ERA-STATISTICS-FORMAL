import BianchiIX.Analysis.CompactVectorIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- Differentiating a finite-time integral equation needs one derivative of its rate. -/
theorem hasFDerivAt_of_parametric_ode
    {J G : E × ℝ → V} {x : E} {a b : ℝ} {v : V}
    (hab : a ≤ b) (hG : ∀ t ∈ Icc a b, ContDiffAt ℝ 1 G (x, t))
    (hJ : ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc a b,
      HasDerivAt (fun r => J (y, r)) (G (y, t)) t)
    (hinit : ∀ᶠ y in 𝓝 x, J (y, a) = v) :
    HasFDerivAt (fun y => J (y, b))
      (∫ t in a..b, (fderiv ℝ G (x, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)) x := by
  have hnear : ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc a b, ContDiffAt ℝ 1 G (y, t) := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro t ht
    exact (hG t ht).eventually (by norm_num)
  have heq : (fun y => J (y, b)) =ᶠ[𝓝 x] (fun y => v + ∫ t in a..b, G (y, t)) := by
    filter_upwards [hJ, hinit, hnear] with y hy hi hc
    have hcont : ContinuousOn (fun t => G (y, t)) (Icc a b) := fun t ht =>
      ((hc t ht).continuousAt.comp (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
    have H := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hy t (uIcc_of_le hab ▸ ht)) (hcont.intervalIntegrable_of_Icc hab)
    rw [hi] at H
    rw [H, add_sub_cancel]
  have H := (hasFDerivAt_const v x).add (hasFDerivAt_compact_vector_integral hab hG)
  simpa only [zero_add] using H.congr_of_eventuallyEq heq

theorem hasDerivAt_integral_partial_fderiv {G : E × ℝ → V} {x : E} {a b : ℝ}
    (hab : a ≤ b) (hG : ∀ t ∈ Icc a b, ContDiffAt ℝ 1 G (x, t)) :
    HasDerivAt
      (fun s => ∫ t in a..s, (fderiv ℝ G (x, t)).comp (ContinuousLinearMap.inl ℝ E ℝ))
      ((fderiv ℝ G (x, b)).comp (ContinuousLinearMap.inl ℝ E ℝ)) b := by
  let S : Set ℝ := {t | ContDiffAt ℝ 1 G (x, t)}
  let D := fun t => (fderiv ℝ G (x, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)
  have hS : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    change ContDiffAt ℝ 1 G (x, t) at ht
    exact (continuousAt_const.prodMk (continuousAt_id (x := t))).eventually
      (ht.eventually (by norm_num))
  have hD : ContinuousOn D S := by
    intro t ht
    change ContDiffAt ℝ 1 G (x, t) at ht
    exact (((ht.continuousAt_fderiv (by norm_num)).clm_comp continuousAt_const).comp
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  have hb : b ∈ S := hG b ⟨hab, le_rfl⟩
  exact intervalIntegral.integral_hasDerivAt_right
    ((hD.mono (fun t ht => hG t ht)).intervalIntegrable_of_Icc hab)
    (hD.stronglyMeasurableAtFilter hS b hb) (hD.continuousAt (hS.mem_nhds hb))

end BianchiIX
