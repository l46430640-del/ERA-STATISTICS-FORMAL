import BianchiIX.Dynamics.FlowRegularity

noncomputable section

namespace BianchiIX

open Set

def normalizedFlowDifferential (x : NormalizedState) (t₀ t : ℝ) : NormalizedVariation :=
  fderiv ℝ (fun y => normalizedMaxCurve y t₀ t) x

theorem hasFDerivAt_normalizedMaxCurve_initial {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    HasFDerivAt (fun y => normalizedMaxCurve y t₀ t) (normalizedFlowDifferential x t₀ t) x := by
  have H := (normalizedMaxCurve_regular ht).2.comp x (contDiffAt_id.prodMk contDiffAt_const)
  exact (H.differentiableAt (by norm_num)).hasFDerivAt

theorem normalizedMaxCurve_fderiv_initial {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    (fderiv ℝ (fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 t₀ z.2) (x, t)).comp
      (ContinuousLinearMap.inl ℝ NormalizedState ℝ) = normalizedFlowDifferential x t₀ t := by
  have H := ((normalizedMaxCurve_regular ht).2.differentiableAt (by norm_num)).hasFDerivAt
  have hleft : HasFDerivAt (fun y => normalizedMaxCurve y t₀ t)
      ((fderiv ℝ (fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 t₀ z.2) (x, t)).comp
        (ContinuousLinearMap.inl ℝ NormalizedState ℝ)) x := by
    convert! H.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x t) using 1
  exact hleft.unique (hasFDerivAt_normalizedMaxCurve_initial ht)

theorem hasFDerivAt_normalizedMaxCurve {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    HasFDerivAt (fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 t₀ z.2)
      ((normalizedFlowDifferential x t₀ t).coprod
        ((ContinuousLinearMap.id ℝ ℝ).smulRight (normalizedField (normalizedMaxCurve x t₀ t))))
      (x, t) := by
  have H := ((normalizedMaxCurve_regular ht).2.differentiableAt (by norm_num)).hasFDerivAt
  have hright := (H.comp t (hasFDerivAt_prodMk_right x t)).unique
    (hasDerivAt_normalizedMaxCurve ht).hasFDerivAt
  have heq : ContinuousLinearMap.toSpanSingleton ℝ (normalizedField (normalizedMaxCurve x t₀ t)) =
      (ContinuousLinearMap.id ℝ ℝ).smulRight (normalizedField (normalizedMaxCurve x t₀ t)) := by
    ext u
    rfl
  rw [heq] at hright
  rw [← normalizedMaxCurve_fderiv_initial ht, ← hright, ContinuousLinearMap.coprod_comp_inl_inr]
  exact H

theorem continuousOn_normalizedFlowDifferential (t₀ : ℝ) :
    ContinuousOn (fun z : NormalizedState × ℝ => normalizedFlowDifferential z.1 t₀ z.2)
      (normalizedFlowDomain t₀) := by
  have hc := (contDiffOn_normalizedMaxCurve t₀).continuousOn_fderiv_of_isOpen
    (isOpen_normalizedFlowDomain t₀) (by norm_num)
  exact (hc.clm_comp (continuousOn_const (c := ContinuousLinearMap.inl ℝ NormalizedState ℝ))).congr
    (fun z hz => (normalizedMaxCurve_fderiv_initial hz).symm)

end BianchiIX
