import BianchiIX.Dynamics.AxisCharts
import BianchiIX.Dynamics.Events

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem normalizedEventRate_axisWall (A : NormalizedSymmetry) (x : NormalizedState) (t₀ t : ℝ) :
    normalizedEventRate (fun z => A.map z 2) x t₀ t =
      rateOne (A.map (normalizedMaxCurve x t₀ t) 0) (A.map (normalizedMaxCurve x t₀ t) 1) *
        A.map (normalizedMaxCurve x t₀ t) 2 := by
  unfold normalizedEventRate
  have hd : HasFDerivAt (fun z => A.map z 2)
      ((ContinuousLinearMap.proj (2 : Fin 5)).comp A.map.toContinuousLinearMap)
      (normalizedMaxCurve x t₀ t) := by
    convert! (hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 5) (A.map (normalizedMaxCurve x t₀ t))).comp
      (normalizedMaxCurve x t₀ t) A.map.hasFDerivAt using 1
  rw [hd.fderiv]
  change A.map (normalizedField (normalizedMaxCurve x t₀ t)) 2 = _
  rw [← A.field]
  rfl

/-- A transverse target-axis crossing determines an actual event of the original flow. -/
theorem exists_normalized_axisWall_event (A : NormalizedSymmetry) {x : NormalizedState} {t₀ t h : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) (hh : 0 < h)
    (hlevel : A.map (normalizedMaxCurve x t₀ t) 2 = h)
    (hp : A.map (normalizedMaxCurve x t₀ t) 0 < 0) :
    ∃ τ : NormalizedState → ℝ, τ x = t ∧ ContDiffAt ℝ 1 τ x ∧
      (∀ᶠ y in 𝓝 x, τ y ∈ normalizedMaxDomain y t₀ ∧ A.map (normalizedMaxCurve y t₀ (τ y)) 2 = h) ∧
      (∀ᶠ z : NormalizedState × ℝ in 𝓝 (x, t), z.2 ∈ normalizedMaxDomain z.1 t₀ ∧
        (A.map (normalizedMaxCurve z.1 t₀ z.2) 2 = h ↔ τ z.1 = z.2)) ∧
      ContDiffAt ℝ 1 (fun y => normalizedMaxCurve y t₀ (τ y)) x := by
  have hrate : rateOne (A.map (normalizedMaxCurve x t₀ t) 0)
      (A.map (normalizedMaxCurve x t₀ t) 1) < 0 := by
    unfold rateOne shearSq
    nlinarith [sq_nonneg (A.map (normalizedMaxCurve x t₀ t) 0),
      sq_nonneg (A.map (normalizedMaxCurve x t₀ t) 1)]
  have htrans : normalizedEventRate (fun z => A.map z 2) x t₀ t ≠ 0 := by
    rw [normalizedEventRate_axisWall, hlevel]
    exact ne_of_lt (mul_neg_of_neg_of_pos hrate hh)
  have hg : ContDiffAt ℝ 1 (fun z => A.map z 2) (normalizedMaxCurve x t₀ t) := by fun_prop
  obtain ⟨τ, hτ, hcτ, _, hhit, huniq, hcMap, _⟩ := exists_normalized_event ht hg htrans
  refine ⟨τ, hτ, hcτ, ?_, ?_, hcMap⟩
  · filter_upwards [hhit] with y hy
    exact ⟨hy.1, hy.2.trans hlevel⟩
  · filter_upwards [huniq] with z hz
    simpa only [hlevel] using hz

end BianchiIX
