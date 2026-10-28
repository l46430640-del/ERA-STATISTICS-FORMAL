import BianchiIX.Dynamics.StableBoundaryVariationGrowth
import BianchiIX.Analysis.ContractiveForcing

noncomputable section

namespace BianchiIX

open Set

theorem stableCenterColumn_norm_bound {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) :
    ‖stableCenterColumn (c + 1) y‖ ≤ 64 * (|y 1| + |y 2|) := by
  have H := stableRescaledJacobian_center_column hc hm hu hw
  apply (pi_norm_le_iff_of_nonempty _).mpr
  intro i
  fin_cases i
  · change ‖(c + 1) * stableOriginalJacobian y 1 0‖ ≤ _
    rw [Real.norm_eq_abs]
    nlinarith [H.1, abs_nonneg (y 2)]
  · change ‖(c + 1) * stableOriginalJacobian y 2 0‖ ≤ _
    rw [Real.norm_eq_abs]
    nlinarith [H.2, abs_nonneg (y 1)]

theorem stableRescaledDifferential_stable_decay {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) (v : StableState) :
    ‖![stableRescaledDifferential (c + 1) y s v 1, stableRescaledDifferential (c + 1) y s v 2]‖ ≤
      (‖![v 1, v 2]‖ + 256 * (|y 1| + |y 2|) *
        Real.exp (512 * (|y 1| + |y 2|)) * ‖v‖) * Real.exp (-s / 4) := by
  let b := |y 1| + |y 2|
  let M := Real.exp (512 * b) * ‖v‖
  let J := fun r => stableRescaledDifferential (c + 1) y r v
  let Z := fun r => ![J r 1, J r 2]
  let A := fun r => stableLinearBlock (c + 1) (stableRescaledFlow (c + 1) y r)
  let q := fun r => J r 0 • stableCenterColumn (c + 1) (stableRescaledFlow (c + 1) y r)
  have hK : 0 < c + 1 := by linarith
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hZ (r : ℝ) (hr : r ∈ Icc 0 s) : HasDerivAt Z ((A r).mulVec (Z r) + q r) r :=
    stableRescaledVariation_stable_equation hK hc hm hu hw hr.1 v
  have hA (r : ℝ) (hr : r ∈ Icc 0 s) (i : Fin 2) : signedRowSum (A r) i ≤ -(1 / 4) := by
    obtain ⟨hm', hu', hw'⟩ := stableRescaledFlow_band hc hm hu hw hr.1
    exact stableLinearBlock_signedRowSum hc hm' hu' hw' i
  have hq (r : ℝ) (hr : r ∈ Icc 0 s) : ‖q r‖ ≤ 64 * b * M * Real.exp (-r / 2) := by
    obtain ⟨hm', hu', hw'⟩ := stableRescaledFlow_band hc hm hu hw hr.1
    have hc0 : |J r 0| ≤ ‖J r‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (J r) 0
    have hmM : |J r 0| ≤ M := hc0.trans (stableRescaledDifferential_bound hc hm hu hw hr.1 v)
    have hcol := (stableCenterColumn_norm_bound hc hm' hu' hw').trans
      (mul_le_mul_of_nonneg_left (stableRescaledFlow_amplitude_decay hc hm hu hw hr.1)
        (by norm_num : (0 : ℝ) ≤ 64))
    dsimp only [q]
    rw [norm_smul, Real.norm_eq_abs]
    have H := mul_le_mul hmM hcol (norm_nonneg _) hM
    nlinarith only [H]
  have H := norm_le_exp_of_faster_forcing (ρ := (1 / 4 : ℝ)) (Q := 64 * b * M)
    (by norm_num) (by positivity) hZ hA (fun r hr => by
      convert! hq r hr using 1
      congr 2
      ring) s ⟨hs, le_rfl⟩
  have hzero : Z 0 = ![v 1, v 2] := by
    simp only [Z, J, stableRescaledDifferential_initial, ContinuousLinearMap.id_apply]
  rw [hzero] at H
  convert! H using 1
  dsimp [M, b]
  congr 1
  · ring
  · congr 1
    ring

end BianchiIX
