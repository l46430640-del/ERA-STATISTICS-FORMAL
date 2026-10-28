import BianchiIX.Dynamics.CoreTailMultipliers
import BianchiIX.Analysis.MonotoneCrossing

noncomputable section

namespace BianchiIX

open Set

/-- Every intermediate height is reached on the same strictly decreasing finite tail. -/
theorem coreTailValid_of_height_le {h₀ h : ℝ} {Y : CoreAngleState}
    (HV : coreTailValid h₀ Y) (hlo : h₀ ≤ h) (hhi : h < 1) :
    coreTailValid h Y ∧ coreTailTime h Y ≤ coreTailTime h₀ Y := by
  let x := fromProjectiveState (coreTailEntry Y)
  let T := coreTailTime h₀ Y
  let V := fun t => projectiveActiveWall (normalizedMaxCurve x 0 t)
  have hT : 0 < T := HV.1.1.1
  have hderiv (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivAt V (normalizedEventRate projectiveActiveWall x 0 t) t :=
    ((contDiffAt_projectiveActiveWall 1 (HV.2.1 t ht).2.ne').differentiableAt
      (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_normalizedMaxCurve (HV.2.1 t ht).1)
  have hmono : StrictAntiOn V (Icc 0 T) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (HasDerivAt.continuousOn hderiv)
    intro t ht
    rw [(hderiv t (interior_subset ht)).deriv]
    exact HV.2.2.2.1 t (interior_subset ht)
  have hV0 : V 0 = 1 := by
    dsimp only [V, x, projectiveActiveWall]
    rw [normalizedMaxCurve_initial, toProjectiveState_fromProjectiveState (coreTailValid_denom_pos HV).ne']
    rfl
  have hVT : V T = h₀ := HV.1.1.2.2
  obtain ⟨t, ht, hhit⟩ := intermediate_value_Icc' hT.le (HasDerivAt.continuousOn hderiv)
    (show h ∈ Icc (V T) (V 0) by rw [hVT, hV0]; exact ⟨hlo, hhi.le⟩)
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (by
    intro heq
    rw [← heq, hV0] at hhit
    linarith only [hhit, hhi])
  have hsub : Icc 0 t ⊆ Icc 0 T := fun _ hr => ⟨hr.1, hr.2.trans ht.2⟩
  have hbefore (r : ℝ) (hr : r ∈ Ico 0 t) : h < V r := by
    rw [← hhit]
    exact hmono (hsub ⟨hr.1, hr.2.le⟩) ht hr.2
  have hfirst : IsLeast {r | 0 < r ∧ r ∈ normalizedMaxDomain x 0 ∧ V r = h} t := by
    refine ⟨⟨htpos, (HV.2.1 t ht).1, hhit⟩, ?_⟩
    intro r hr
    by_contra hn
    have H := hbefore r ⟨hr.1.le, lt_of_not_ge hn⟩
    rw [hr.2.2] at H
    exact lt_irrefl _ H
  have htime : coreTailTime h Y = t := hfirst.csInf_eq
  refine ⟨?_, by rw [htime]; exact ht.2⟩
  dsimp only [coreTailValid]
  rw [htime]
  exact ⟨hfirst, (fun r hr => HV.2.1 r (hsub hr)), hbefore,
    (fun r hr => HV.2.2.2.1 r (hsub hr)), fun r hr => HV.2.2.2.2 r (hsub hr)⟩

end BianchiIX
