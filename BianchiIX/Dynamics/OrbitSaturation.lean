import BianchiIX.Dynamics.FlowTransport

noncomputable section

namespace BianchiIX

open Set

def normalizedOrbitSaturation (S : Set NormalizedState) : Set NormalizedState :=
  {x | ∃ z ∈ S, ∃ t ∈ normalizedMaxDomain z 0, normalizedMaxCurve z 0 t = x}

theorem normalizedMaxCurve_inverse {x : NormalizedState} {t : ℝ}
    (ht : t ∈ normalizedMaxDomain x 0) :
    -t ∈ normalizedMaxDomain (normalizedMaxCurve x 0 t) 0 ∧
      normalizedMaxCurve (normalizedMaxCurve x 0 t) 0 (-t) = x := by
  have hzero : 0 ∈ normalizedMaxDomain (normalizedMaxCurve x 0 t) t := by
    rw [normalizedMaxDomain_rebase ht]
    exact initial_mem_normalizedMaxDomain x 0
  refine ⟨(mem_normalizedMaxDomain_retime (t₀ := t)).mpr (by simpa using hzero), ?_⟩
  have H := normalizedMaxCurve_shift (by simpa only [zero_add] using ht)
    (show -t + t ∈ normalizedMaxDomain x 0 by simpa using initial_mem_normalizedMaxDomain x 0)
  simpa only [zero_add, neg_add_cancel, normalizedMaxCurve_initial] using H

theorem subset_normalizedOrbitSaturation (S : Set NormalizedState) : S ⊆ normalizedOrbitSaturation S :=
  fun x hx => ⟨x, hx, 0, initial_mem_normalizedMaxDomain x 0, normalizedMaxCurve_initial x 0⟩

theorem mem_normalizedOrbitSaturation_flow {S : Set NormalizedState} {x : NormalizedState} {s : ℝ}
    (hx : x ∈ normalizedOrbitSaturation S) (hs : s ∈ normalizedMaxDomain x 0) :
    normalizedMaxCurve x 0 s ∈ normalizedOrbitSaturation S := by
  obtain ⟨z, hz, t, ht, rfl⟩ := hx
  have H := normalizedMaxCurve_restart (t := t + s) ht (by simpa using hs)
  exact ⟨z, hz, t + s, H.1, by simpa using H.2⟩

theorem mem_normalizedOrbitSaturation_flow_iff {S : Set NormalizedState}
    {x : NormalizedState} {s : ℝ} (hs : s ∈ normalizedMaxDomain x 0) :
    normalizedMaxCurve x 0 s ∈ normalizedOrbitSaturation S ↔ x ∈ normalizedOrbitSaturation S := by
  constructor
  · intro hx
    have H := mem_normalizedOrbitSaturation_flow hx (normalizedMaxCurve_inverse hs).1
    rwa [(normalizedMaxCurve_inverse hs).2] at H
  · exact fun hx => mem_normalizedOrbitSaturation_flow hx hs

end BianchiIX
