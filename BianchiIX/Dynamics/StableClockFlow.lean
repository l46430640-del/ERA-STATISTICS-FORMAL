import BianchiIX.Dynamics.StableClockInverse

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def stableClockField (c : ℝ) (y : StableState) : StableState :=
  (c + 1)⁻¹ • stableBoundaryField y

def stableClockFlow (c : ℝ) (p : StableState × ℝ) : StableState :=
  stableOriginalFlow p.1 (stableProjectiveTime c p)

theorem contDiff_stableClockField (c : ℝ) (n : WithTop ℕ∞) :
    ContDiff ℝ n (stableClockField c) := by
  unfold stableClockField
  exact (contDiff_stableBoundaryField n).const_smul _

theorem stableClockField_fderiv (c : ℝ) (y v : StableState) :
    fderiv ℝ (stableClockField c) y v =
      (c + 1)⁻¹ • (stableBoundaryJacobian y).mulVec v := by
  unfold stableClockField
  rw [fderiv_fun_const_smul ((contDiff_stableBoundaryField 1).differentiable (by norm_num) y)]
  simp only [smul_apply, stableBoundaryField_fderiv]

theorem stableClockFlow_initial {c : ℝ} (hc : 2 ≤ c) (y : StableState) :
    stableClockFlow c (y, 0) = y := by
  simp only [stableClockFlow, stableProjectiveTime_zero hc, stableOriginalFlow_initial]

theorem stableClockFlow_eq_original {c σ : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 ≤ σ) :
    stableClockFlow c (y, σ) = stableOriginalFlow y (stableProjectiveCutoff c (y, σ)) := by
  rw [stableClockFlow, stableProjectiveTime_eq_cutoff hc hy hσ]

theorem contDiffAt_stableClockFlow_two {c σ : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 ≤ σ) :
    ContDiffAt ℝ 2 (stableClockFlow c) (y, σ) :=
  (contDiffAt_stableOriginalFlow_two hc hy.1.le hy.2.1.le hy.2.2.le
    (stableProjectiveTime_spec hc hy hσ).1).comp (y, σ)
      (g := fun p : StableState × ℝ => stableOriginalFlow p.1 p.2)
      (f := fun p : StableState × ℝ => (p.1, stableProjectiveTime c p))
      (contDiffAt_fst.prodMk (stableProjectiveTime_regular hc hy hσ).1)

theorem hasDerivAt_stableClockFlow_time {c σ : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 ≤ σ) :
    HasDerivAt (fun s => stableClockFlow c (y, s))
      (stableClockField c (stableClockFlow c (y, σ))) σ := by
  have hK : c + 1 ≠ 0 := by linarith
  have hD := (stableBoundaryDenom_pos (stableOriginalFlow y (stableProjectiveTime c (y, σ)))).ne'
  have H := (hasDerivAt_stableOriginalFlow hc hy.1.le hy.2.1.le hy.2.2.le
    (stableProjectiveTime_spec hc hy hσ).1).scomp σ (hasDerivAt_stableProjectiveTime_clock hc hy hσ)
  apply H.congr_deriv
  dsimp only [stableProjectiveRate, stableResidualClock, stableOriginalField, stableClockField,
    stableClockFlow]
  rw [smul_smul]
  congr 1
  field_simp [hD]

theorem stableClockFlow_band {c σ : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 ≤ σ) :
    |stableClockFlow c (y, σ) 0 - c| ≤ 1 / 10 ∧
      |stableClockFlow c (y, σ) 1| ≤ |y 1| ∧ |stableClockFlow c (y, σ) 2| ≤ |y 2| := by
  have H := stableBoundaryOrbit_global hc hy.1.le hy.2.1.le hy.2.2.le _
    (stableProjectiveTime_spec hc hy hσ).1
  simpa [stableClockFlow, stableOriginalFlow_eq, stableRestriction_apply] using
    And.intro H.2.1.1 (And.intro H.2.2.2.1 H.2.2.2.2)

theorem stableClockFlow_wall_decay {c σ : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 ≤ σ) :
    |stableClockFlow c (y, σ) 1| ≤ |y 1| * Real.exp (-(c + 1) / 8 * σ) ∧
      |stableClockFlow c (y, σ) 2| ≤ |y 2| * Real.exp (-(1 / 4) * σ) := by
  let T := stableProjectiveTime c (y, σ)
  let x := fromProjectiveState (stableBoundaryEntry (y 0) (y 1) (y 2))
  let Y := stableBoundaryOrbit (y 0) (y 1) (y 2)
  obtain ⟨ht, he⟩ := stableProjectiveTime_spec hc hy hσ
  have hg := stableBoundaryOrbit_global hc hy.1.le hy.2.1.le hy.2.2.le
  have hx : stateConstraint x = 1 :=
    fromProjectiveState_constraint (stableBoundaryEntry_denom_pos _ _ _).ne'
  have hapos (t : ℝ) (ht : 0 ≤ t) : 0 < normalizedProjectiveRate x 0 t :=
    lt_of_lt_of_le (by positivity : 0 < 3 / (c + 1) ^ 2) (hg t ht).1
  have hdec := (normalized_stable_prefix_estimates hx hc (le_refl 0) ht
    (fun t ht => hapos t ht.1) (fun t ht => (hg t ht.1).2.1)).2.1 T ⟨ht, le_rfl⟩
  have hclock : normalizedStableClock x 0 0 c T = σ :=
    (stableProjectiveClock_eq_normalized hc hy ht).symm.trans he
  rw [hclock] at hdec
  change |Y T 1| ≤ |Y 0 1| * Real.exp (-(c + 1) / 8 * σ) ∧
    |Y T 3| ≤ |Y 0 3| * Real.exp (-(1 / 4) * σ) at hdec
  simpa [stableClockFlow, stableOriginalFlow_eq, stableRestriction_apply, T, Y,
    stableBoundaryOrbit_initial, stableBoundaryEntry] using hdec

end BianchiIX
