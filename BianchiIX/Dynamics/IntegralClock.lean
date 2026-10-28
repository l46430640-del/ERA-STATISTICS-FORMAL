import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology

def integralClock (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ := ∫ u in t₀..t, a u

theorem integralClock_initial (a : ℝ → ℝ) (t₀ : ℝ) : integralClock a t₀ t₀ = 0 := by
  simp [integralClock]

theorem hasStrictDerivAt_integralClock {J : Set ℝ} {a : ℝ → ℝ} {t₀ t : ℝ}
    (hJ : Convex ℝ J) (ho : IsOpen J) (ha : ContinuousOn a J)
    (ht₀ : t₀ ∈ J) (ht : t ∈ J) :
    HasStrictDerivAt (integralClock a t₀) (a t) t :=
  intervalIntegral.integral_hasStrictDerivAt_right
    (ha.mono (hJ.ordConnected.uIcc_subset ht₀ ht)).intervalIntegrable
    (ha.stronglyMeasurableAtFilter ho t ht) (ha.continuousAt (ho.mem_nhds ht))

theorem strictMonoOn_integralClock {J : Set ℝ} {a : ℝ → ℝ} {t₀ : ℝ}
    (hJ : Convex ℝ J) (ho : IsOpen J) (ha : ContinuousOn a J)
    (ht₀ : t₀ ∈ J) (hpos : ∀ t ∈ J, 0 < a t) :
    StrictMonoOn (integralClock a t₀) J := by
  have hd := fun t ht => (hasStrictDerivAt_integralClock hJ ho ha ht₀ (t := t) ht).hasDerivAt
  exact strictMonoOn_of_deriv_pos hJ (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).deriv ▸ hpos t (interior_subset ht))

theorem isOpenMap_integralClock_restrict {J : Set ℝ} {a : ℝ → ℝ} {t₀ : ℝ}
    (hJ : Convex ℝ J) (ho : IsOpen J) (ha : ContinuousOn a J)
    (ht₀ : t₀ ∈ J) (hpos : ∀ t ∈ J, 0 < a t) :
    IsOpenMap (J.domRestrict (integralClock a t₀)) := by
  apply IsOpenMap.of_nhds_le
  intro t
  change 𝓝 (integralClock a t₀ t) ≤ map (integralClock a t₀ ∘ Subtype.val) (𝓝 t)
  rw [← map_map, map_nhds_subtype_val, ho.nhdsWithin_eq t.2]
  exact ((hasStrictDerivAt_integralClock hJ ho ha ht₀ t.2).map_nhds_eq
    (ne_of_gt (hpos t t.2))).ge

/-- The entire positive-clock interval, with its exact image as target. -/
def positiveIntegralClock {J : Set ℝ} {a : ℝ → ℝ} {t₀ : ℝ}
    (hJ : Convex ℝ J) (ho : IsOpen J) (ha : ContinuousOn a J)
    (ht₀ : t₀ ∈ J) (hpos : ∀ t ∈ J, 0 < a t) : OpenPartialHomeomorph ℝ ℝ :=
  OpenPartialHomeomorph.ofContinuousOpenRestrict
    ((strictMonoOn_integralClock hJ ho ha ht₀ hpos).injOn.toPartialEquiv _ _)
    (fun _ ht => (hasStrictDerivAt_integralClock hJ ho ha ht₀ ht).hasDerivAt.continuousAt.continuousWithinAt)
    (isOpenMap_integralClock_restrict hJ ho ha ht₀ hpos) ho

theorem positiveIntegralClock_source {J : Set ℝ} {a : ℝ → ℝ} {t₀ : ℝ}
    (hJ : Convex ℝ J) (ho : IsOpen J) (ha : ContinuousOn a J)
    (ht₀ : t₀ ∈ J) (hpos : ∀ t ∈ J, 0 < a t) :
    (positiveIntegralClock hJ ho ha ht₀ hpos).source = J := rfl

theorem positiveIntegralClock_target {J : Set ℝ} {a : ℝ → ℝ} {t₀ : ℝ}
    (hJ : Convex ℝ J) (ho : IsOpen J) (ha : ContinuousOn a J)
    (ht₀ : t₀ ∈ J) (hpos : ∀ t ∈ J, 0 < a t) :
    (positiveIntegralClock hJ ho ha ht₀ hpos).target = integralClock a t₀ '' J := rfl

theorem positiveIntegralClock_apply {J : Set ℝ} {a : ℝ → ℝ} {t₀ t : ℝ}
    (hJ : Convex ℝ J) (ho : IsOpen J) (ha : ContinuousOn a J)
    (ht₀ : t₀ ∈ J) (hpos : ∀ t ∈ J, 0 < a t) :
    positiveIntegralClock hJ ho ha ht₀ hpos t = integralClock a t₀ t := rfl

theorem hasDerivAt_positiveIntegralClock_symm {J : Set ℝ} {a : ℝ → ℝ} {t₀ τ : ℝ}
    (hJ : Convex ℝ J) (ho : IsOpen J) (ha : ContinuousOn a J)
    (ht₀ : t₀ ∈ J) (hpos : ∀ t ∈ J, 0 < a t)
    (hτ : τ ∈ (positiveIntegralClock hJ ho ha ht₀ hpos).target) :
    HasDerivAt (positiveIntegralClock hJ ho ha ht₀ hpos).symm
      (1 / a ((positiveIntegralClock hJ ho ha ht₀ hpos).symm τ)) τ := by
  let e := positiveIntegralClock hJ ho ha ht₀ hpos
  have ht : e.symm τ ∈ J := e.map_target hτ
  simpa only [one_div] using e.hasDerivAt_symm hτ (ne_of_gt (hpos _ ht))
    (hasStrictDerivAt_integralClock hJ ho ha ht₀ ht).hasDerivAt

theorem convex_positiveIntegralClock_target {J : Set ℝ} {a : ℝ → ℝ} {t₀ : ℝ}
    (hJ : Convex ℝ J) (ho : IsOpen J) (ha : ContinuousOn a J)
    (ht₀ : t₀ ∈ J) (hpos : ∀ t ∈ J, 0 < a t) :
    Convex ℝ (positiveIntegralClock hJ ho ha ht₀ hpos).target := by
  let e := positiveIntegralClock hJ ho ha ht₀ hpos
  rw [← e.image_source_eq_target]
  exact (hJ.isPreconnected.image e e.continuousOn).convex

theorem positiveIntegralClock_symm_zero {J : Set ℝ} {a : ℝ → ℝ} {t₀ : ℝ}
    (hJ : Convex ℝ J) (ho : IsOpen J) (ha : ContinuousOn a J)
    (ht₀ : t₀ ∈ J) (hpos : ∀ t ∈ J, 0 < a t) :
    (positiveIntegralClock hJ ho ha ht₀ hpos).symm 0 = t₀ := by
  let e := positiveIntegralClock hJ ho ha ht₀ hpos
  have he : e t₀ = 0 := integralClock_initial a t₀
  rw [← he]
  exact e.left_inv ht₀

end BianchiIX
