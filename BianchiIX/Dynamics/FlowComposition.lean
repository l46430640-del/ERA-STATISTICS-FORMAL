import BianchiIX.Dynamics.SmoothLocalFlow

noncomputable section

namespace BianchiIX

open Set Filter Metric
open scoped Topology

/-- Translate the initial time of a solution of the autonomous equation. -/
def NormalizedSolution.retime {x : NormalizedState} {t₀ : ℝ}
    (S : NormalizedSolution x t₀) (t₁ : ℝ) : NormalizedSolution x t₁ where
  domain := (fun t => t + t₀ - t₁) ⁻¹' S.domain
  isOpen_domain := S.isOpen_domain.preimage (by fun_prop)
  convex_domain := convex_iff_ordConnected.mpr
    (S.convex_domain.ordConnected.preimage_mono (fun a b hab => by linarith))
  initial_mem := by simpa using S.initial_mem
  curve := fun t => S.curve (t + t₀ - t₁)
  initial_eq := by simpa using S.initial_eq
  hasDerivAt := by
    intro t ht
    convert! (S.hasDerivAt (t + t₀ - t₁) ht).scomp t
      (((hasDerivAt_id t).add_const t₀).sub_const t₁) using 1
    simp

theorem mem_normalizedMaxDomain_retime {x : NormalizedState} {t₀ t₁ t : ℝ} :
    t ∈ normalizedMaxDomain x t₁ ↔ t + t₀ - t₁ ∈ normalizedMaxDomain x t₀ := by
  constructor
  · intro ht
    apply ((maximalNormalizedSolution x t₁).retime t₀).domain_subset_maximal
    change (t + t₀ - t₁) + t₁ - t₀ ∈ normalizedMaxDomain x t₁
    convert! ht using 1
    ring
  · intro ht
    exact ((maximalNormalizedSolution x t₀).retime t₁).domain_subset_maximal ht

theorem normalizedMaxCurve_retime {x : NormalizedState} {t₀ t₁ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₁) :
    normalizedMaxCurve x t₁ t = normalizedMaxCurve x t₀ (t + t₀ - t₁) :=
  normalizedMaxCurve_eqOn ((maximalNormalizedSolution x t₀).retime t₁)
    (mem_normalizedMaxDomain_retime.mp ht)

def NormalizedSolution.rebase {x : NormalizedState} {t₀ s : ℝ}
    (S : NormalizedSolution x t₀) (hs : s ∈ S.domain) : NormalizedSolution (S.curve s) s :=
  ⟨S.domain, S.isOpen_domain, S.convex_domain, hs, S.curve, rfl, S.hasDerivAt⟩

theorem normalizedMaxDomain_rebase {x : NormalizedState} {t₀ s : ℝ}
    (hs : s ∈ normalizedMaxDomain x t₀) :
    normalizedMaxDomain (normalizedMaxCurve x t₀ s) s = normalizedMaxDomain x t₀ := by
  let S := maximalNormalizedSolution x t₀
  have hsub := (S.rebase hs).domain_subset_maximal
  let T := maximalNormalizedSolution (S.curve s) s
  have ht₀ : t₀ ∈ T.domain := hsub S.initial_mem
  have hinit : T.curve t₀ = x :=
    (normalizedMaxCurve_eqOn (S.rebase hs) S.initial_mem).trans S.initial_eq
  let U : NormalizedSolution x t₀ :=
    ⟨T.domain, T.isOpen_domain, T.convex_domain, ht₀, T.curve, hinit, T.hasDerivAt⟩
  exact Subset.antisymm U.domain_subset_maximal hsub

theorem normalizedMaxCurve_rebase {x : NormalizedState} {t₀ s t : ℝ}
    (hs : s ∈ normalizedMaxDomain x t₀) (ht : t ∈ normalizedMaxDomain x t₀) :
    normalizedMaxCurve (normalizedMaxCurve x t₀ s) s t = normalizedMaxCurve x t₀ t :=
  normalizedMaxCurve_eqOn ((maximalNormalizedSolution x t₀).rebase hs) ht

/-- A local restart proves membership in the original maximal domain as well as the flow identity. -/
theorem normalizedMaxCurve_restart {x : NormalizedState} {t₀ s t : ℝ}
    (hs : s ∈ normalizedMaxDomain x t₀)
    (ht : t - s ∈ normalizedMaxDomain (normalizedMaxCurve x t₀ s) 0) :
    t ∈ normalizedMaxDomain x t₀ ∧
      normalizedMaxCurve x t₀ t = normalizedMaxCurve (normalizedMaxCurve x t₀ s) 0 (t - s) := by
  have ht' : t ∈ normalizedMaxDomain (normalizedMaxCurve x t₀ s) s :=
    (mem_normalizedMaxDomain_retime (t₀ := (0 : ℝ))).mpr (by simpa using ht)
  have hmem : t ∈ normalizedMaxDomain x t₀ := by rwa [normalizedMaxDomain_rebase hs] at ht'
  refine ⟨hmem, (normalizedMaxCurve_rebase hs hmem).symm.trans ?_⟩
  simpa using (normalizedMaxCurve_retime (t₀ := (0 : ℝ)) ht')

end BianchiIX
