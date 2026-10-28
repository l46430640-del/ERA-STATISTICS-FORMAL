import BianchiIX.Dynamics.StableBoundaryDissipation
import BianchiIX.Analysis.ForcedRowGrowth

noncomputable section

namespace BianchiIX

open Set

def stableLinearBlock (K : ℝ) (y : StableState) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![K * stableOriginalJacobian y 1 1, K * stableOriginalJacobian y 1 2],
    ![K * stableOriginalJacobian y 2 1, K * stableOriginalJacobian y 2 2]]

def stableCenterColumn (K : ℝ) (y : StableState) : Fin 2 → ℝ :=
  ![K * stableOriginalJacobian y 1 0, K * stableOriginalJacobian y 2 0]

theorem stableLinearBlock_signedRowSum {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) (i : Fin 2) :
    signedRowSum (stableLinearBlock (c + 1) y) i ≤ -(1 / 4) := by
  have H := stableRescaledJacobian_stable_rows hc hm hu hw
  have hK : 0 < c + 1 := by linarith
  have hfin : Finset.univ = ({0, 1} : Finset (Fin 2)) := by decide
  fin_cases i
  · simp [signedRowSum, stableLinearBlock, hfin, abs_mul, abs_of_pos hK]
    nlinarith only [H.1, hc]
  · simp [signedRowSum, stableLinearBlock, hfin, abs_mul, abs_of_pos hK]
    nlinarith only [H.2]

theorem stableRescaledFlow_band {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) :
    |stableRescaledFlow (c + 1) y s 0 - c| ≤ 1 / 10 ∧
    |stableRescaledFlow (c + 1) y s 1| ≤ 1 / 100 ∧
    |stableRescaledFlow (c + 1) y s 2| ≤ 1 / 100 := by
  have ht : 0 ≤ (c + 1) * s := mul_nonneg (by linarith) hs
  have H := (stableBoundaryOrbit_global hc hm hu hw ((c + 1) * s) ht).2.1
  simp only [stableRescaledFlow, stableOriginalFlow_eq, stableRestriction_apply]
  exact ⟨H.1, H.2.1, H.2.2.2⟩

theorem stableFlow_stableBlock_decay {y : StableState} {c a b : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (ha : 0 ≤ a)
    {v : ℝ → (Fin 2 → ℝ)}
    (hv : ∀ s ∈ Icc a b, HasDerivAt v
      ((stableLinearBlock (c + 1) (stableRescaledFlow (c + 1) y s)).mulVec (v s)) s) :
    ∀ s ∈ Icc a b, ‖v s‖ ≤ ‖v a‖ * Real.exp (-(s - a) / 4) := by
  have hrow (s : ℝ) (hs : s ∈ Ico a b) (i : Fin 2) :
      signedRowSum (stableLinearBlock (c + 1) (stableRescaledFlow (c + 1) y s)) i ≤ -(1 / 4) := by
    obtain ⟨hm', hu', hw'⟩ := stableRescaledFlow_band hc hm hu hw (ha.trans hs.1)
    exact stableLinearBlock_signedRowSum hc hm' hu' hw' i
  have hz (s : ℝ) : HasDerivAt (fun r : ℝ => -r / 4) (-(1 / 4)) s := by
    convert! (hasDerivAt_id s).neg.div_const 4 using 1
    norm_num
  have H := norm_le_exp_of_signedRowSum (HasDerivAt.continuousOn hv)
    (fun s hs => hv s (Ico_subset_Icc_self hs))
    (HasDerivAt.continuousOn (fun s _ => hz s)) (fun s _ => hz s) hrow
  intro s hs
  convert! H s hs using 1
  congr 2
  ring

theorem stableRescaledVariation_stable_equation {K : ℝ} {y : StableState} {c s : ℝ}
    (hK : 0 < K) (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) (v : StableState) :
    HasDerivAt (fun r => ![stableRescaledDifferential K y r v 1, stableRescaledDifferential K y r v 2])
      ((stableLinearBlock K (stableRescaledFlow K y s)).mulVec
        ![stableRescaledDifferential K y s v 1, stableRescaledDifferential K y s v 2] +
       stableRescaledDifferential K y s v 0 • stableCenterColumn K (stableRescaledFlow K y s)) s := by
  have H := hasDerivAt_pi.mp (stableRescaledFlow_variational_equation hK hc hm hu hw hs v)
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · apply (H 1).congr_deriv
    simp [stableLinearBlock, stableCenterColumn, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  · apply (H 2).congr_deriv
    simp [stableLinearBlock, stableCenterColumn, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring

end BianchiIX
