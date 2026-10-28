import BianchiIX.Analysis.ODEVariation
import Mathlib.Analysis.Calculus.FDeriv.Partial

noncomputable section

namespace BianchiIX

open Set Filter Metric Asymptotics
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A continuous variational family supplies the derivative of the solution family. -/
theorem contDiffOn_ode_family_with_derivative {f : E → E} (hf : ContDiff ℝ 2 f)
    {x₀ : E} {t₀ r ε : ℝ} (hε : 0 < ε)
    {α : E × ℝ → E} {J : E × ℝ → E →L[ℝ] E} {L : ℝ≥0}
    (hcα : ContinuousOn α (closedBall x₀ r ×ˢ Icc (t₀ - ε) (t₀ + ε)))
    (hcJ : ContinuousOn J (ball x₀ r ×ˢ Ioo (t₀ - ε) (t₀ + ε)))
    (hα0 : ∀ x ∈ ball x₀ r, α (x, t₀) = x)
    (hJ0 : ∀ x ∈ ball x₀ r, J (x, t₀) = ContinuousLinearMap.id ℝ E)
    (hα : ∀ x ∈ ball x₀ r, ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
      HasDerivAt (fun u => α (x, u)) (f (α (x, t))) t)
    (hJ : ∀ x ∈ ball x₀ r, ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
      HasDerivAt (fun u => J (x, u)) ((fderiv ℝ f (α (x, t))).comp (J (x, t))) t)
    (hLip : ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
      LipschitzOnWith L (fun x => α (x, t)) (ball x₀ r)) :
    ContDiffOn ℝ 1 α (ball x₀ r ×ˢ Ioo (t₀ - ε) (t₀ + ε)) ∧
      ∀ z ∈ ball x₀ r ×ˢ Ioo (t₀ - ε) (t₀ + ε), HasStrictFDerivAt α
        ((J z).coprod ((ContinuousLinearMap.id ℝ ℝ).smulRight (f (α z)))) z := by
  let U := ball x₀ r ×ˢ Ioo (t₀ - ε) (t₀ + ε)
  have ho : IsOpen U := isOpen_ball.prod isOpen_Ioo
  have hDU : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  obtain ⟨B, hB⟩ := ((isCompact_closedBall x₀ r).prod
    (isCompact_Icc (a := t₀ - ε) (b := t₀ + ε))).exists_bound_of_continuousOn hcα
  obtain ⟨C, hC⟩ := hDU.contDiffOn.exists_lipschitzOnWith (by norm_num)
    (convex_closedBall (0 : E) B) (isCompact_closedBall (0 : E) B)
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : E) B).exists_bound_of_continuousOn
    hDU.continuous.continuousOn
  have hstate {x : E} (hx : x ∈ ball x₀ r) {u : ℝ} (hu : u ∈ Ioo (t₀ - ε) (t₀ + ε)) :
      α (x, u) ∈ closedBall (0 : E) B := by
    rw [mem_closedBall, dist_zero_right]
    exact hB (x, u) ⟨ball_subset_closedBall hx, Ioo_subset_Icc_self hu⟩
  have hdx (x : E) (hx : x ∈ ball x₀ r) (t : ℝ) (ht : t ∈ Ioo (t₀ - ε) (t₀ + ε)) :
      HasFDerivAt (fun y => α (y, t)) (J (x, t)) x := by
    have ht₀ : t₀ ∈ Ioo (t₀ - ε) (t₀ + ε) := by constructor <;> linarith
    have hseg : uIcc t₀ t ⊆ Ioo (t₀ - ε) (t₀ + ε) :=
      (convex_Ioo _ _).ordConnected.uIcc_subset ht₀ ht
    have hO : (fun y => α (y, t) - α (x, t) - J (x, t) (y - x))
        =O[𝓝 x] (fun y => ‖y - x‖ ^ 2) := by
      apply IsBigO.of_bound (gronwallBound 0 K (C * (L : ℝ) ^ 2) |t - t₀|)
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      have H := ode_variation_remainder (fun z => (hf.differentiable (by norm_num) z).hasFDerivAt)
        (convex_closedBall (0 : E) B) hC
        (fun u hu => hα x hx u (hseg hu)) (fun u hu => hα y hy u (hseg hu))
        (fun _ hu => hstate hx (hseg hu)) (fun _ hu => hstate hy (hseg hu))
        (fun u hu => hJ x hx u (hseg hu)) (hJ0 x hx)
        (fun u hu => hK _ (hstate hx (hseg hu)))
        (fun u hu => by
          rw [hα0 y hy, hα0 x hx]
          exact (hLip u (hseg hu)).norm_sub_le hy hx)
      simpa only [hα0 y hy, hα0 x hx, norm_pow, norm_norm] using H
    exact hasFDerivAt_iff_isLittleO.mpr (hO.trans_isLittleO (isLittleO_pow_sub_sub x (by norm_num)))
  let V : E × ℝ → ℝ →L[ℝ] E := fun z =>
    (ContinuousLinearMap.id ℝ ℝ).smulRight (f (α z))
  have hcαU : ContinuousOn α U := hcα.mono (fun _ hz => ⟨ball_subset_closedBall hz.1, Ioo_subset_Icc_self hz.2⟩)
  have hcV : ContinuousOn V U :=
    (ContinuousLinearMap.smulRightL ℝ ℝ E (ContinuousLinearMap.id ℝ ℝ)).continuous.comp_continuousOn
      (hf.continuous.comp_continuousOn hcαU)
  have hd (z : E × ℝ) (hz : z ∈ U) : HasStrictFDerivAt α ((J z).coprod (V z)) z := by
    apply hasStrictFDerivAt_uncurry_coprod (f := fun x t => α (x, t))
      (f₁ := fun x t => J (x, t)) (f₂ := fun x t => V (x, t))
    · filter_upwards [ho.mem_nhds hz] with w hw
      exact hdx w.1 hw.1 w.2 hw.2
    · filter_upwards [ho.mem_nhds hz] with w hw
      exact (hα w.1 hw.1 w.2 hw.2).hasFDerivAt
    · exact hcJ.continuousAt (ho.mem_nhds hz)
    · exact hcV.continuousAt (ho.mem_nhds hz)
  refine ⟨?_, hd⟩
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by rfl,
    contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn ho.uniqueDiffOn]
  exact ⟨by simp, fun z => (J z).coprod (V z),
    contDiffOn_zero.mpr (hcJ.continuousLinearMapCoprod hcV),
    fun z hz => (hd z hz).hasFDerivAt.hasFDerivWithinAt⟩

theorem contDiffOn_ode_family {f : E → E} (hf : ContDiff ℝ 2 f)
    {x₀ : E} {t₀ r ε : ℝ} (hε : 0 < ε)
    {α : E × ℝ → E} {J : E × ℝ → E →L[ℝ] E} {L : ℝ≥0}
    (hcα : ContinuousOn α (closedBall x₀ r ×ˢ Icc (t₀ - ε) (t₀ + ε)))
    (hcJ : ContinuousOn J (ball x₀ r ×ˢ Ioo (t₀ - ε) (t₀ + ε)))
    (hα0 : ∀ x ∈ ball x₀ r, α (x, t₀) = x)
    (hJ0 : ∀ x ∈ ball x₀ r, J (x, t₀) = ContinuousLinearMap.id ℝ E)
    (hα : ∀ x ∈ ball x₀ r, ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
      HasDerivAt (fun u => α (x, u)) (f (α (x, t))) t)
    (hJ : ∀ x ∈ ball x₀ r, ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
      HasDerivAt (fun u => J (x, u)) ((fderiv ℝ f (α (x, t))).comp (J (x, t))) t)
    (hLip : ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
      LipschitzOnWith L (fun x => α (x, t)) (ball x₀ r)) :
    ContDiffOn ℝ 1 α (ball x₀ r ×ˢ Ioo (t₀ - ε) (t₀ + ε)) :=
  (contDiffOn_ode_family_with_derivative hf hε hcα hcJ hα0 hJ0 hα hJ hLip).1

/-- Apply Picard-Lindelof once to the state and its linear variation together. -/
theorem exists_ode_local_contDiff_one {f : E → E} (hf : ContDiff ℝ 2 f) (x₀ : E) (t₀ : ℝ) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ α : E × ℝ → E,
      ContDiffOn ℝ 1 α (ball x₀ r ×ˢ Ioo (t₀ - ε) (t₀ + ε)) ∧
      ∀ x ∈ ball x₀ r, α (x, t₀) = x ∧
        ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt (fun u => α (x, u)) (f (α (x, t))) t := by
  let idE := ContinuousLinearMap.id ℝ E
  let T : E × (E →L[ℝ] E) → E × (E →L[ℝ] E) :=
    fun z => (f z.1, (fderiv ℝ f z.1).comp z.2)
  have hT : ContDiff ℝ 1 T :=
    ((hf.of_le (by norm_num)).comp contDiff_fst).prodMk
      (((hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).comp contDiff_fst).clm_comp contDiff_snd)
  obtain ⟨ε, hε, a, r, L, K, hr, hPL⟩ := IsPicardLindelof.of_contDiffAt_one
    (hT.contDiffAt (x := (x₀, idE)))
  obtain ⟨Φ, hΦ, L', hLip⟩ :=
    (hPL t₀).exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
  have hcΦ : ContinuousOn (fun z => Φ z.1 z.2)
      (closedBall (x₀, idE) r ×ˢ Icc (t₀ - ε) (t₀ + ε)) :=
    continuousOn_prod_of_continuousOn_lipschitzOnWith _ L'
      (fun x hx => HasDerivWithinAt.continuousOn (hΦ x hx).2) hLip
  have hxpair (x : E) (hx : x ∈ closedBall x₀ r) : (x, idE) ∈ closedBall (x₀, idE) r := by
    simpa only [mem_closedBall, dist_prod_same_right] using hx
  let α : E × ℝ → E := fun z => (Φ (z.1, idE) z.2).1
  let J : E × ℝ → E →L[ℝ] E := fun z => (Φ (z.1, idE) z.2).2
  have hc : ContinuousOn (fun z : E × ℝ => Φ (z.1, idE) z.2)
      (closedBall x₀ r ×ˢ Icc (t₀ - ε) (t₀ + ε)) :=
    hcΦ.comp (by fun_prop : ContinuousOn (fun z : E × ℝ => ((z.1, idE), z.2))
      (closedBall x₀ r ×ˢ Icc (t₀ - ε) (t₀ + ε))) (fun z hz => ⟨hxpair z.1 hz.1, hz.2⟩)
  have hode (x : E) (hx : x ∈ ball x₀ r) (t : ℝ) (ht : t ∈ Ioo (t₀ - ε) (t₀ + ε)) :
      HasDerivAt (fun u => α (x, u)) (f (α (x, t))) t ∧
      HasDerivAt (fun u => J (x, u)) ((fderiv ℝ f (α (x, t))).comp (J (x, t))) t := by
    have H := ((hΦ (x, idE) (hxpair x (ball_subset_closedBall hx))).2 t
      (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    exact ⟨(ContinuousLinearMap.fst ℝ E (E →L[ℝ] E)).hasFDerivAt.comp_hasDerivAt t H,
      (ContinuousLinearMap.snd ℝ E (E →L[ℝ] E)).hasFDerivAt.comp_hasDerivAt t H⟩
  have hα0 (x : E) (hx : x ∈ ball x₀ r) : α (x, t₀) = x :=
    congrArg Prod.fst (hΦ (x, idE) (hxpair x (ball_subset_closedBall hx))).1
  have hJ0 (x : E) (hx : x ∈ ball x₀ r) : J (x, t₀) = idE :=
    congrArg Prod.snd (hΦ (x, idE) (hxpair x (ball_subset_closedBall hx))).1
  refine ⟨r, hr, ε, hε, α, ?_, fun x hx => ⟨hα0 x hx, fun t ht => (hode x hx t ht).1⟩⟩
  apply contDiffOn_ode_family hf hε (continuous_fst.comp_continuousOn hc)
    ((continuous_snd.comp_continuousOn hc).mono
      (fun _ hz => ⟨ball_subset_closedBall hz.1, Ioo_subset_Icc_self hz.2⟩)) hα0 hJ0
    (fun x hx t ht => (hode x hx t ht).1) (fun x hx t ht => (hode x hx t ht).2)
    (L := L')
  intro t ht
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  calc
    _ ≤ dist (Φ (x, idE) t) (Φ (y, idE) t) := le_max_left _ _
    _ ≤ L' * dist (x, idE) (y, idE) :=
      (hLip t (Ioo_subset_Icc_self ht)).dist_le_mul _ (hxpair x (ball_subset_closedBall hx))
        _ (hxpair y (ball_subset_closedBall hy))
    _ = _ := by rw [dist_prod_same_right]

end BianchiIX
