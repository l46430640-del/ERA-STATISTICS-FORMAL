import BianchiIX.Dynamics.CompactConnectionThresholdControl
import BianchiIX.Analysis.ThreeCoordinateLevel
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue

noncomputable section

namespace BianchiIX

open Set

def compactConnectionCritical (η : ℝ) (p : Fin 2 → ℝ) : ℝ :=
  sInf {k : ℝ | k ∈ Icc (31 / 8) (33 / 8) ∧ compactConnectionPhase η ![k, p 0, p 1] = 2}

/-- The critical phase is the unique actual level crossing in the entire compact parameter interval. -/
theorem compactConnectionCritical_spec_of_control {η : ℝ} {p : Fin 2 → ℝ}
    (hreg : ∀ k ∈ Icc (31 / 8 : ℝ) 6, ContDiffAt ℝ 2 (compactConnectionPhase η) ![k, p 0, p 1])
    (hr : ∀ k ∈ Icc (31 / 8 : ℝ) 6,
      1 / 2 ≤ fderiv ℝ (compactConnectionPhase η) ![k, p 0, p 1] (Pi.single 0 1))
    (hval : ∀ k ∈ Icc (31 / 8 : ℝ) 6, |compactConnectionPhase η ![k, p 0, p 1] - (k - 2)| ≤ 1 / 16) :
    compactConnectionCritical η p ∈ Ioo (31 / 8) (33 / 8) ∧
      compactConnectionPhase η ![compactConnectionCritical η p, p 0, p 1] = 2 ∧
      StrictMonoOn (fun k => compactConnectionPhase η ![k, p 0, p 1]) (Icc (31 / 8 : ℝ) 6) := by
  let f := fun k => compactConnectionPhase η ![k, p 0, p 1]
  have hd (k : ℝ) (hk : k ∈ Icc (31 / 8 : ℝ) 6) : HasDerivAt f
      (fderiv ℝ (compactConnectionPhase η) ![k, p 0, p 1] (Pi.single 0 1)) k := by
    have H := ((hreg k hk).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt k
      (hasDerivAt_three_coordinate_line p k)
    exact H
  have hcont : ContinuousOn f (Icc (31 / 8 : ℝ) 6) := fun k hk => (hd k hk).continuousAt.continuousWithinAt
  have hmono : StrictMonoOn f (Icc (31 / 8 : ℝ) 6) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hcont
    intro k hk
    rw [(hd k (interior_subset hk)).deriv]
    linarith only [hr k (interior_subset hk)]
  have hleft : f (31 / 8) < 2 := by
    have H := hval (31 / 8) (by norm_num)
    change |f (31 / 8) - (31 / 8 - 2)| ≤ 1 / 16 at H
    linarith only [(abs_le.mp H).2]
  have hright : 2 < f (33 / 8) := by
    have H := hval (33 / 8) (by norm_num)
    change |f (33 / 8) - (33 / 8 - 2)| ≤ 1 / 16 at H
    linarith only [(abs_le.mp H).1]
  have hsub : Icc (31 / 8 : ℝ) (33 / 8) ⊆ Icc (31 / 8) 6 :=
    fun _ hk => ⟨hk.1, hk.2.trans (by norm_num)⟩
  obtain ⟨k, hk, heq⟩ := intermediate_value_Icc (by norm_num : (31 / 8 : ℝ) ≤ 33 / 8)
    (hcont.mono hsub) ⟨hleft.le, hright.le⟩
  have hkopen : k ∈ Ioo (31 / 8 : ℝ) (33 / 8) := by
    constructor
    · apply lt_of_le_of_ne hk.1
      intro H
      subst k
      linarith only [heq, hleft]
    · apply lt_of_le_of_ne hk.2
      intro H
      subst k
      linarith only [heq, hright]
  have hleast : IsLeast {a : ℝ | a ∈ Icc (31 / 8) (33 / 8) ∧ f a = 2} k := by
    refine ⟨⟨hk, heq⟩, ?_⟩
    intro a ha
    exact le_of_eq (hmono.injOn (hsub ha.1) (hsub hk) (ha.2.trans heq.symm)).symm
  have hcritical : compactConnectionCritical η p = k := hleast.csInf_eq
  rw [hcritical]
  exact ⟨hkopen, heq, hmono⟩

end BianchiIX
