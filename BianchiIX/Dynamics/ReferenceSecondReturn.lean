import BianchiIX.Analysis.ImplicitBranch
import BianchiIX.Dynamics.FlowSecondRegularity
import BianchiIX.Dynamics.ReferenceFirstReturn

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The previously identified first-return branch is twice continuously differentiable. -/
theorem exists_referenceCore_firstReturn_two {k : ℝ} (hk : 1 < k) :
    ∃ (τ : CoreCoordinates → ℝ) (P : CoreCoordinates → CoreCoordinates),
      τ (referenceCoreInput k) = referenceNormalizedTime k ∧
      P (referenceCoreInput k) = referenceCoreOutput k ∧
      ContDiffAt ℝ 2 τ (referenceCoreInput k) ∧ ContDiffAt ℝ 2 P (referenceCoreInput k) ∧
      (∀ᶠ z in 𝓝 (referenceCoreInput k),
        IsLeast {t : ℝ | 0 < t ∧ t ∈ normalizedMaxDomain (coreSectionChart z) 0 ∧
          projectiveActiveWall (normalizedMaxCurve (coreSectionChart z) 0 t) = 1} (τ z) ∧
        (∀ t ∈ Icc 0 (τ z), t ∈ normalizedMaxDomain (coreSectionChart z) 0 ∧
          0 < 1 + normalizedMaxCurve (coreSectionChart z) 0 t 0) ∧
        (∀ t ∈ Ioo 0 (τ z), 1 < projectiveActiveWall (normalizedMaxCurve (coreSectionChart z) 0 t)) ∧
        normalizedEventRate projectiveActiveWall (coreSectionChart z) 0 (τ z) < 0 ∧
        toProjectiveState (normalizedMaxCurve (coreSectionChart z) 0 (τ z)) = coreSectionEmbedding (P z)) ∧
      (∀ v : CoreCoordinates, fderiv ℝ P (referenceCoreInput k) v =
        ![-v 0 + (2 / Real.sqrt (k ^ 2 - 1)) * (1 - Real.exp (-k * Real.arcosh k)) * v 1,
          Real.exp (-k * Real.arcosh k) * v 1, Real.exp (-4 * Real.arcosh k / k) * v 2]) := by
  obtain ⟨τ, P, hτ, hP, hcτ, _, hfirst, hdP⟩ := exists_referenceCore_firstReturn hk
  let z₀ := referenceCoreInput k
  let T := referenceNormalizedTime k
  let F : CoreCoordinates × ℝ → NormalizedState := fun z => normalizedMaxCurve (coreSectionChart z.1) 0 z.2
  let Q : CoreCoordinates × ℝ → ℝ := fun z => projectiveActiveWall (F z)
  have hcross : T ∈ normalizedMaxDomain (coreSectionChart z₀) 0 := by
    rw [referenceCoreInput_chart hk]
    exact (referenceEntryState_crossing hk).1
  have hFvalue : F (z₀, T) = referenceExitState k := by
    dsimp [F, z₀, T]
    rw [referenceCoreInput_chart hk, (referenceEntryState_crossing hk).2]
  have hcC : ContDiffAt ℝ 2 coreSectionChart z₀ := contDiffAt_referenceCoreChart hk 2
  have hcF : ContDiffAt ℝ 2 F (z₀, T) :=
    (contDiffAt_normalizedMaxCurve_two hcross).comp (z₀, T)
      ((hcC.comp (z₀, T) contDiffAt_fst).prodMk contDiffAt_snd)
  have hwall : ContDiffAt ℝ 2 projectiveActiveWall (F (z₀, T)) := by
    rw [hFvalue]
    exact contDiffAt_projectiveActiveWall 2 (ne_of_gt (referenceExitState_clock_pos k))
  have hcQ : ContDiffAt ℝ 2 Q (z₀, T) := hwall.comp (z₀, T) hcF
  have htime : HasDerivAt (fun u => Q (z₀, u))
      (normalizedEventRate projectiveActiveWall (coreSectionChart z₀) 0 T) T := by
    convert! (hwall.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt T
      (hasDerivAt_normalizedMaxCurve hcross) using 1
  have htrans : normalizedEventRate projectiveActiveWall (coreSectionChart z₀) 0 T ≠ 0 := by
    unfold normalizedEventRate
    change fderiv ℝ projectiveActiveWall (F (z₀, T)) (normalizedField (F (z₀, T))) ≠ 0
    rw [hFvalue]
    exact ne_of_lt (referenceExitState_rate_neg hk)
  have hQvalue : Q (z₀, T) = 1 := by
    have H := hfirst.self_of_nhds.1.1.2.2
    rw [hτ] at H
    exact H
  have hτ2 : ContDiffAt ℝ 2 τ z₀ := contDiffAt_scalar_event_branch_two hcQ htime htrans hτ
    hcτ.continuousAt (hfirst.mono fun _ hz => hz.1.1.2.2.trans hQvalue.symm)
  have hcEnd : ContDiffAt ℝ 2 (fun z => F (z, τ z)) z₀ := by
    have H : ContDiffAt ℝ 2 F (z₀, τ z₀) := by rw [hτ]; exact hcF
    exact H.comp z₀ (contDiffAt_id.prodMk hτ2)
  have hto : ContDiffAt ℝ 2 toProjectiveState (F (z₀, τ z₀)) := by
    rw [hτ, hFvalue]
    exact contDiffAt_toProjectiveState 2 (ne_of_gt (referenceExitState_clock_pos k))
  have hcProjective : ContDiffAt ℝ 2 (fun z => toProjectiveState (F (z, τ z))) z₀ := by
    convert! hto.comp z₀ hcEnd using 1
  have hcOut : ContDiffAt ℝ 2 (fun z => coreSectionCoordinates (toProjectiveState (F (z, τ z)))) z₀ := by
    convert! (contDiff_coreSectionCoordinates 2).contDiffAt.comp z₀ hcProjective using 1
  have heq : P =ᶠ[𝓝 z₀] (fun z => coreSectionCoordinates (toProjectiveState (F (z, τ z)))) := by
    filter_upwards [hfirst] with z hz
    change P z = coreSectionCoordinates (toProjectiveState (normalizedMaxCurve (coreSectionChart z) 0 (τ z)))
    rw [hz.2.2.2.2]
    ext i
    fin_cases i <;> rfl
  exact ⟨τ, P, hτ, hP, hτ2, hcOut.congr_of_eventuallyEq heq, hfirst, hdP⟩

end BianchiIX
