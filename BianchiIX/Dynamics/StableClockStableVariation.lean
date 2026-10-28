import BianchiIX.Dynamics.StableClockVariationGrowth
import BianchiIX.Analysis.ContractiveForcing

noncomputable section

namespace BianchiIX

open Set

def stableClockStableBlock (c : ℝ) (y : StableState) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![stableClockJacobian c y 1 1, stableClockJacobian c y 1 2],
    ![stableClockJacobian c y 2 1, stableClockJacobian c y 2 2]]

def stableClockCenterColumn (c : ℝ) (y : StableState) : Fin 2 → ℝ :=
  ![stableClockJacobian c y 1 0, stableClockJacobian c y 2 0]

theorem stableClockStableBlock_signedRowSum {c : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) (i : Fin 2) :
    signedRowSum (stableClockStableBlock c y) i ≤ -(3 / 8) := by
  have H := stableClockJacobian_stable_rows hc hm hu hw
  have hfin : Finset.univ = ({0, 1} : Finset (Fin 2)) := by decide
  fin_cases i <;> simp [signedRowSum, stableClockStableBlock, hfin]
  · linarith [H.1]
  · linarith [H.2]

theorem stableClockCenterColumn_norm {c : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10) :
    ‖stableClockCenterColumn c y‖ ≤ |y 1| + |y 2| := by
  have H := stableClockJacobian_center_column hc hm
  apply (pi_norm_le_iff_of_nonempty _).mpr
  intro i
  fin_cases i
  · change ‖stableClockJacobian c y 1 0‖ ≤ _
    rw [Real.norm_eq_abs]
    linarith [H.1, abs_nonneg (y 2)]
  · change ‖stableClockJacobian c y 2 0‖ ≤ _
    rw [Real.norm_eq_abs]
    linarith [H.2, abs_nonneg (y 1)]

theorem stableClockFlow_stable_variational_equation {c σ : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 ≤ σ) (v : StableState) :
    HasDerivAt (fun s => ![fderiv ℝ (stableClockFlow c) (y, s) (v, 0) 1,
        fderiv ℝ (stableClockFlow c) (y, s) (v, 0) 2])
      ((stableClockStableBlock c (stableClockFlow c (y, σ))).mulVec
        ![fderiv ℝ (stableClockFlow c) (y, σ) (v, 0) 1,
          fderiv ℝ (stableClockFlow c) (y, σ) (v, 0) 2] +
        fderiv ℝ (stableClockFlow c) (y, σ) (v, 0) 0 •
          stableClockCenterColumn c (stableClockFlow c (y, σ))) σ := by
  have H := hasDerivAt_pi.mp (stableClockFlow_variational_equation hc hy hσ v)
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · apply (H 1).congr_deriv
    simp [stableClockStableBlock, stableClockCenterColumn, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]
    ring
  · apply (H 2).congr_deriv
    simp [stableClockStableBlock, stableClockCenterColumn, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]
    ring

theorem stableClockFlow_stable_variation_decay {c σ : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 ≤ σ) (v : StableState) :
    ‖![fderiv ℝ (stableClockFlow c) (y, σ) (v, 0) 1,
        fderiv ℝ (stableClockFlow c) (y, σ) (v, 0) 2]‖ ≤
      (‖![v 1, v 2]‖ + 8 * (|y 1| + |y 2|) *
        Real.exp (32 * (|y 1| + |y 2|)) * ‖v‖) * Real.exp (-σ / 8) := by
  let b := |y 1| + |y 2|
  let M := Real.exp (32 * b) * ‖v‖
  let J := fun s => fderiv ℝ (stableClockFlow c) (y, s) (v, 0)
  let Y := fun s => stableClockFlow c (y, s)
  let Z := fun s => ![J s 1, J s 2]
  let A := fun s => stableClockStableBlock c (Y s)
  let q := fun s => J s 0 • stableClockCenterColumn c (Y s)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hZ (s : ℝ) (hs : s ∈ Icc 0 σ) : HasDerivAt Z ((A s).mulVec (Z s) + q s) s :=
    stableClockFlow_stable_variational_equation hc hy hs.1 v
  have hA (s : ℝ) (hs : s ∈ Icc 0 σ) (i : Fin 2) : signedRowSum (A s) i ≤ -(1 / 8) := by
    obtain ⟨hm, hu, hw⟩ := stableClockFlow_band hc hy hs.1
    exact (stableClockStableBlock_signedRowSum hc hm
      (hu.trans (by linarith [hy.2.1])) (hw.trans (by linarith [hy.2.2])) i).trans (by norm_num)
  have hq (s : ℝ) (hs : s ∈ Icc 0 σ) : ‖q s‖ ≤ b * M * Real.exp (-2 * (1 / 8 : ℝ) * s) := by
    have hJ : |J s 0| ≤ M :=
      (show |J s 0| ≤ ‖J s‖ by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (J s) 0).trans
        (stableClockFlow_variation_bound hc hy hs.1 v)
    have hcol := (stableClockCenterColumn_norm hc (stableClockFlow_band hc hy hs.1).1).trans
      (stableClockFlow_amplitude_decay hc hy hs.1)
    dsimp only [q]
    rw [norm_smul, Real.norm_eq_abs]
    have H := mul_le_mul hJ hcol (norm_nonneg _) hM
    have he : -2 * (1 / 8 : ℝ) * s = -s / 4 := by ring
    rw [he]
    dsimp only [b]
    nlinarith only [H]
  have H := norm_le_exp_of_faster_forcing (ρ := (1 / 8 : ℝ)) (Q := b * M)
    (by norm_num) (by positivity) hZ hA hq σ ⟨hσ, le_rfl⟩
  have hzero : Z 0 = ![v 1, v 2] := by simp only [Z, J, stableClockFlow_variation_initial hc hy]
  rw [hzero] at H
  convert! H using 1
  dsimp [M, b]
  congr 1
  · ring
  · congr 1
    ring

end BianchiIX
