import BianchiIX.Dynamics.IntegralClock
import BianchiIX.Dynamics.ProjectiveInverse
import BianchiIX.Dynamics.ForwardComplete

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def normalizedProjectiveRate (x : NormalizedState) (t₀ t : ℝ) : ℝ :=
  1 + normalizedMaxCurve x t₀ t 0

theorem continuousOn_normalizedProjectiveRate (x : NormalizedState) (t₀ : ℝ) :
    ContinuousOn (normalizedProjectiveRate x t₀) (normalizedMaxDomain x t₀) := by
  intro t ht
  exact (continuousAt_const.add
    ((continuous_apply 0).continuousAt.comp
      (hasDerivAt_normalizedMaxCurve ht).continuousAt)).continuousWithinAt

theorem exists_positive_projective_interval {x : NormalizedState} {t₀ s : ℝ}
    (hs : s ∈ normalizedMaxDomain x t₀) (hA : 0 < normalizedProjectiveRate x t₀ s) :
    ∃ l r : ℝ, s ∈ Ioo l r ∧ Ioo l r ⊆ normalizedMaxDomain x t₀ ∧
      ∀ t ∈ Ioo l r, 0 < normalizedProjectiveRate x t₀ t := by
  have hc := (continuousOn_normalizedProjectiveRate x t₀).continuousAt
    ((isOpen_normalizedMaxDomain x t₀).mem_nhds hs)
  have hp : ∀ᶠ t in 𝓝 s, 0 < normalizedProjectiveRate x t₀ t :=
    (isOpen_lt continuous_const continuous_id).mem_nhds hA |> hc.eventually
  obtain ⟨l, r, hsr, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (inter_mem ((isOpen_normalizedMaxDomain x t₀).mem_nhds hs) hp)
  exact ⟨l, r, hsr, fun t ht => (hsub ht).1, fun t ht => (hsub ht).2⟩

/-- The positive chart is used on its whole chosen interval, not just near the base point. -/
theorem exists_normalized_projective_reparametrization
    {x : NormalizedState} {t₀ s : ℝ} {J : Set ℝ}
    (hcon : stateConstraint x = 1) (hJ : Convex ℝ J) (ho : IsOpen J)
    (hs : s ∈ J) (hdom : J ⊆ normalizedMaxDomain x t₀)
    (hpos : ∀ t ∈ J, 0 < normalizedProjectiveRate x t₀ t) :
    ∃ e : OpenPartialHomeomorph ℝ ℝ,
      e.source = J ∧
      (∀ t, e t = integralClock (normalizedProjectiveRate x t₀) s t) ∧
      e.target = integralClock (normalizedProjectiveRate x t₀) s '' J ∧
      Convex ℝ e.target ∧ 0 ∈ e.target ∧ e.symm 0 = s ∧
      StrictMonoOn e J ∧
      (∀ τ ∈ e.target,
        HasDerivAt e.symm (1 / normalizedProjectiveRate x t₀ (e.symm τ)) τ ∧
        HasDerivAt (fun u => toProjectiveState (normalizedMaxCurve x t₀ (e.symm u)))
          (projectiveField (toProjectiveState (normalizedMaxCurve x t₀ (e.symm τ)))) τ ∧
        0 < projectiveStateDenom (toProjectiveState (normalizedMaxCurve x t₀ (e.symm τ))) ∧
        fromProjectiveState (toProjectiveState (normalizedMaxCurve x t₀ (e.symm τ))) =
          normalizedMaxCurve x t₀ (e.symm τ)) := by
  have ha := (continuousOn_normalizedProjectiveRate x t₀).mono hdom
  let e := positiveIntegralClock hJ ho ha hs hpos
  have he0 : e s = 0 := integralClock_initial _ _
  refine ⟨e, rfl, fun _ => rfl, rfl, convex_positiveIntegralClock_target hJ ho ha hs hpos,
    he0 ▸ e.map_source hs, positiveIntegralClock_symm_zero hJ ho ha hs hpos,
    strictMonoOn_integralClock hJ ho ha hs hpos, ?_⟩
  intro τ hτ
  have ht : e.symm τ ∈ J := e.map_target hτ
  have hc : stateConstraint (normalizedMaxCurve x t₀ (e.symm τ)) = 1 := by
    have H := normalized_constraint_constant (convex_normalizedMaxDomain x t₀)
      (fun _ hu => hasDerivAt_normalizedMaxCurve hu)
      (initial_mem_normalizedMaxDomain x t₀) (hdom ht)
    rw [normalizedMaxCurve_initial] at H
    exact H.trans hcon
  have hinv := hasDerivAt_positiveIntegralClock_symm hJ ho ha hs hpos hτ
  exact ⟨hinv, hasDerivAt_reparametrized_projectiveState
    (hasDerivAt_normalizedMaxCurve (hdom ht)) (hpos _ ht) hc hinv,
    toProjectiveState_denom_pos (hpos _ ht) hc,
    fromProjectiveState_toProjectiveState (ne_of_gt (hpos _ ht)) hc⟩

/-- Every solution of the exact projective system lifts to the maximal original flow. -/
theorem exists_projective_normalized_reparametrization
    {β : ℝ → ProjectiveState} {I : Set ℝ} {s : ℝ}
    (hI : Convex ℝ I) (ho : IsOpen I) (hs : s ∈ I)
    (hβ : ∀ τ ∈ I, HasDerivAt β (projectiveField (β τ)) τ)
    (hD : ∀ τ ∈ I, 0 < projectiveStateDenom (β τ)) :
    ∃ e : OpenPartialHomeomorph ℝ ℝ,
      e.source = I ∧
      (∀ τ, e τ = integralClock (fun u => projectiveStateDenom (β u) / 6) s τ) ∧
      e.target = integralClock (fun u => projectiveStateDenom (β u) / 6) s '' I ∧
      Convex ℝ e.target ∧ 0 ∈ e.target ∧ e.symm 0 = s ∧
      StrictMonoOn e I ∧
      e.target ⊆ normalizedMaxDomain (fromProjectiveState (β s)) 0 ∧
      (∀ t ∈ e.target,
        fromProjectiveState (β (e.symm t)) =
          normalizedMaxCurve (fromProjectiveState (β s)) 0 t ∧
        toProjectiveState (normalizedMaxCurve (fromProjectiveState (β s)) 0 t) = β (e.symm t)) := by
  let a : ℝ → ℝ := fun τ => projectiveStateDenom (β τ) / 6
  have ha : ContinuousOn a I := fun τ hτ =>
    ((continuous_projectiveStateDenom.continuousAt.comp (hβ τ hτ).continuousAt).div_const 6).continuousWithinAt
  have hpos : ∀ τ ∈ I, 0 < a τ := fun τ hτ => div_pos (hD τ hτ) (by norm_num)
  let e := positiveIntegralClock hI ho ha hs hpos
  have he0 : e s = 0 := integralClock_initial _ _
  have hzero : 0 ∈ e.target := he0 ▸ e.map_source hs
  have hinitial : e.symm 0 = s := positiveIntegralClock_symm_zero hI ho ha hs hpos
  have hconvex : Convex ℝ e.target := convex_positiveIntegralClock_target hI ho ha hs hpos
  have hsol (t : ℝ) (ht : t ∈ e.target) :
      HasDerivAt (fun u => fromProjectiveState (β (e.symm u)))
        (normalizedField (fromProjectiveState (β (e.symm t)))) t := by
    have hmem : e.symm t ∈ I := e.map_target ht
    have hc := hasDerivAt_positiveIntegralClock_symm hI ho ha hs hpos ht
    have hc' : HasDerivAt e.symm (6 / projectiveStateDenom (β (e.symm t))) t := by
      convert! hc using 1
      dsimp [a]
      field_simp
      rfl
    exact hasDerivAt_reparametrized_fromProjectiveState (hβ _ hmem)
      (ne_of_gt (hD _ hmem)) hc'
  let S : NormalizedSolution (fromProjectiveState (β s)) 0 :=
    { domain := e.target
      isOpen_domain := e.open_target
      convex_domain := hconvex
      initial_mem := hzero
      curve := fun t => fromProjectiveState (β (e.symm t))
      initial_eq := by rw [hinitial]
      hasDerivAt := hsol }
  refine ⟨e, rfl, fun _ => rfl, rfl, hconvex, hzero, hinitial,
    strictMonoOn_integralClock hI ho ha hs hpos, S.domain_subset_maximal, ?_⟩
  intro t ht
  have heq : fromProjectiveState (β (e.symm t)) =
      normalizedMaxCurve (fromProjectiveState (β s)) 0 t :=
    (normalizedMaxCurve_eqOn S ht).symm
  refine ⟨heq, ?_⟩
  rw [← heq]
  exact toProjectiveState_fromProjectiveState (ne_of_gt (hD _ (e.map_target ht)))

end BianchiIX
