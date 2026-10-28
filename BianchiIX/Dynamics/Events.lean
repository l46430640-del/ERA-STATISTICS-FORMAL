import BianchiIX.Dynamics.FlowDifferential
import Mathlib.Analysis.Calculus.ImplicitContDiff

noncomputable section

namespace BianchiIX

open Set Filter Metric
open scoped Topology

def normalizedEventRate (g : NormalizedState → ℝ) (x : NormalizedState) (t₀ t : ℝ) : ℝ :=
  fderiv ℝ g (normalizedMaxCurve x t₀ t) (normalizedField (normalizedMaxCurve x t₀ t))

def normalizedEventTimeDifferential (g : NormalizedState → ℝ) (x : NormalizedState) (t₀ t : ℝ) :
    NormalizedState →L[ℝ] ℝ :=
  -(normalizedEventRate g x t₀ t)⁻¹ •
    (fderiv ℝ g (normalizedMaxCurve x t₀ t)).comp (normalizedFlowDifferential x t₀ t)

def normalizedEventDifferential (g : NormalizedState → ℝ) (x : NormalizedState) (t₀ t : ℝ) :
    NormalizedVariation :=
  normalizedFlowDifferential x t₀ t +
    (normalizedEventTimeDifferential g x t₀ t).smulRight (normalizedField (normalizedMaxCurve x t₀ t))

private theorem scalar_map_inverse {a : ℝ} (ha : a ≠ 0) :
    (a • ContinuousLinearMap.id ℝ ℝ).IsInvertible ∧
      (a • ContinuousLinearMap.id ℝ ℝ).inverse = a⁻¹ • ContinuousLinearMap.id ℝ ℝ := by
  have hright : (a • ContinuousLinearMap.id ℝ ℝ).comp (a⁻¹ • ContinuousLinearMap.id ℝ ℝ) =
      ContinuousLinearMap.id ℝ ℝ := by ext; simp [ha]
  have hleft : (a⁻¹ • ContinuousLinearMap.id ℝ ℝ).comp (a • ContinuousLinearMap.id ℝ ℝ) =
      ContinuousLinearMap.id ℝ ℝ := by ext; simp [ha]
  exact ⟨ContinuousLinearMap.IsInvertible.of_inverse hright hleft,
    ContinuousLinearMap.inverse_eq hright hleft⟩

/-- A transverse crossing defines a locally unique smooth event time and endpoint map. -/
theorem exists_normalized_event {x : NormalizedState} {t₀ t : ℝ} {g : NormalizedState → ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀)
    (hg : ContDiffAt ℝ 1 g (normalizedMaxCurve x t₀ t))
    (htrans : normalizedEventRate g x t₀ t ≠ 0) :
    ∃ τ : NormalizedState → ℝ, τ x = t ∧ ContDiffAt ℝ 1 τ x ∧
      HasFDerivAt τ (normalizedEventTimeDifferential g x t₀ t) x ∧
      (∀ᶠ y in 𝓝 x, τ y ∈ normalizedMaxDomain y t₀ ∧
        g (normalizedMaxCurve y t₀ (τ y)) = g (normalizedMaxCurve x t₀ t)) ∧
      (∀ᶠ z : NormalizedState × ℝ in 𝓝 (x, t), z.2 ∈ normalizedMaxDomain z.1 t₀ ∧
        (g (normalizedMaxCurve z.1 t₀ z.2) = g (normalizedMaxCurve x t₀ t) ↔ τ z.1 = z.2)) ∧
      ContDiffAt ℝ 1 (fun y => normalizedMaxCurve y t₀ (τ y)) x ∧
      HasFDerivAt (fun y => normalizedMaxCurve y t₀ (τ y)) (normalizedEventDifferential g x t₀ t) x := by
  let Q : NormalizedState × ℝ → ℝ := fun z => g (normalizedMaxCurve z.1 t₀ z.2)
  have hcQ : ContDiffAt ℝ 1 Q (x, t) := hg.comp (x, t) (normalizedMaxCurve_regular ht).2
  have hdQ := (hg.differentiableAt (by norm_num)).hasFDerivAt.comp (x, t)
    (hasFDerivAt_normalizedMaxCurve ht)
  have htime : (fderiv ℝ Q (x, t)).comp (ContinuousLinearMap.inr ℝ NormalizedState ℝ) =
      normalizedEventRate g x t₀ t • ContinuousLinearMap.id ℝ ℝ := by
    rw [show fderiv ℝ Q (x, t) = _ from hdQ.fderiv]
    ext
    simp [normalizedEventRate, ContinuousLinearMap.comp_apply, mul_comm]
  have hinitial : (fderiv ℝ Q (x, t)).comp (ContinuousLinearMap.inl ℝ NormalizedState ℝ) =
      (fderiv ℝ g (normalizedMaxCurve x t₀ t)).comp (normalizedFlowDifferential x t₀ t) := by
    rw [show fderiv ℝ Q (x, t) = _ from hdQ.fderiv]
    simp [ContinuousLinearMap.comp_assoc]
  have hinv : ((fderiv ℝ Q (x, t)).comp (ContinuousLinearMap.inr ℝ NormalizedState ℝ)).IsInvertible := by
    rw [htime]
    exact (scalar_map_inverse htrans).1
  let τ := hcQ.implicitFunction (by norm_num) hinv
  have hτinit : τ x = t := hcQ.implicitFunction_apply_self (by norm_num) hinv
  have hcτ : ContDiffAt ℝ 1 τ x := hcQ.contDiffAt_implicitFunction (by norm_num) hinv
  have hdτ : HasFDerivAt τ (normalizedEventTimeDifferential g x t₀ t) x := by
    have H := (hcQ.hasStrictFDerivAt_implicitFunction (by norm_num) hinv).hasFDerivAt
    rw [htime, hinitial, (scalar_map_inverse htrans).2] at H
    convert! H using 1
    ext v
    simp [normalizedEventTimeDifferential]
  have hgraph : Tendsto (fun y => (y, τ y)) (𝓝 x) (𝓝 (x, t)) := by
    have H : ContinuousAt (fun y : NormalizedState => (y, τ y)) x := by fun_prop
    simpa only [hτinit] using H.tendsto
  have hdomain : normalizedFlowDomain t₀ ∈ 𝓝 (x, t) :=
    (isOpen_normalizedFlowDomain t₀).mem_nhds ht
  have hhit : ∀ᶠ y in 𝓝 x, τ y ∈ normalizedMaxDomain y t₀ ∧
      g (normalizedMaxCurve y t₀ (τ y)) = g (normalizedMaxCurve x t₀ t) :=
    (hgraph.eventually hdomain).and (hcQ.eventually_apply_implicitFunction (by norm_num) hinv)
  have huniq : ∀ᶠ z : NormalizedState × ℝ in 𝓝 (x, t), z.2 ∈ normalizedMaxDomain z.1 t₀ ∧
      (g (normalizedMaxCurve z.1 t₀ z.2) = g (normalizedMaxCurve x t₀ t) ↔ τ z.1 = z.2) := by
    filter_upwards [hdomain, hcQ.eventually_apply_eq_iff_implicitFunction (by norm_num) hinv] with z hz hq
    exact ⟨hz, hq⟩
  have hcFlow : ContDiffAt ℝ 1
      (fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 t₀ z.2) (x, τ x) := by
    rw [hτinit]
    exact (normalizedMaxCurve_regular ht).2
  have hdFlow : HasFDerivAt (fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 t₀ z.2)
      ((normalizedFlowDifferential x t₀ t).coprod
        ((ContinuousLinearMap.id ℝ ℝ).smulRight (normalizedField (normalizedMaxCurve x t₀ t))))
      (x, τ x) := by
    rw [hτinit]
    exact hasFDerivAt_normalizedMaxCurve ht
  have hcMap : ContDiffAt ℝ 1 (fun y => normalizedMaxCurve y t₀ (τ y)) x := by
    convert! hcFlow.comp x (contDiffAt_id.prodMk hcτ) using 1
  refine ⟨τ, hτinit, hcτ, hdτ, hhit, huniq, hcMap, ?_⟩
  convert! hdFlow.comp x ((hasFDerivAt_id x).prodMk hdτ) using 1

theorem normalizedEventRate_mainWall (x : NormalizedState) (t₀ t : ℝ) :
    normalizedEventRate (fun z => z 2) x t₀ t =
      rateOne (normalizedMaxCurve x t₀ t 0) (normalizedMaxCurve x t₀ t 1) *
        normalizedMaxCurve x t₀ t 2 := by
  unfold normalizedEventRate
  rw [(hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 5) (normalizedMaxCurve x t₀ t)).fderiv]
  rfl

/-- Every positive main-wall crossing on the negative shear branch gives an actual local event. -/
theorem exists_normalized_mainWall_event {x : NormalizedState} {t₀ t h : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) (hh : 0 < h)
    (hlevel : normalizedMaxCurve x t₀ t 2 = h) (hp : normalizedMaxCurve x t₀ t 0 < 0) :
    ∃ τ : NormalizedState → ℝ, τ x = t ∧ ContDiffAt ℝ 1 τ x ∧
      (∀ᶠ y in 𝓝 x, τ y ∈ normalizedMaxDomain y t₀ ∧ normalizedMaxCurve y t₀ (τ y) 2 = h) ∧
      (∀ᶠ z : NormalizedState × ℝ in 𝓝 (x, t), z.2 ∈ normalizedMaxDomain z.1 t₀ ∧
        (normalizedMaxCurve z.1 t₀ z.2 2 = h ↔ τ z.1 = z.2)) ∧
      ContDiffAt ℝ 1 (fun y => normalizedMaxCurve y t₀ (τ y)) x := by
  have hrate : rateOne (normalizedMaxCurve x t₀ t 0) (normalizedMaxCurve x t₀ t 1) < 0 := by
    unfold rateOne shearSq
    nlinarith [sq_nonneg (normalizedMaxCurve x t₀ t 0), sq_nonneg (normalizedMaxCurve x t₀ t 1)]
  have htrans : normalizedEventRate (fun z => z 2) x t₀ t ≠ 0 := by
    rw [normalizedEventRate_mainWall, hlevel]
    exact ne_of_lt (mul_neg_of_neg_of_pos hrate hh)
  obtain ⟨τ, hτ, hcτ, _, hhit, huniq, hcMap, _⟩ :=
    exists_normalized_event ht (g := fun z => z 2) (by fun_prop) htrans
  refine ⟨τ, hτ, hcτ, ?_, ?_, hcMap⟩
  · filter_upwards [hhit] with y hy
    exact ⟨hy.1, hy.2.trans hlevel⟩
  · filter_upwards [huniq] with z hz
    simpa only [hlevel] using hz

end BianchiIX
