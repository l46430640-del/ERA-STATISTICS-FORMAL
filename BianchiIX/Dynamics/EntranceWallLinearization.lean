import BianchiIX.Dynamics.EntranceWallWeightedBounds

noncomputable section

namespace BianchiIX

def entranceStrongLogDifferential (y : ProjectiveState) : ProjectiveState →L[ℝ] ℝ :=
  (fderiv ℝ entranceStrongLogRate y).comp (entranceRadialInverseDifferential y)

def entranceWeakLogDifferential (y : ProjectiveState) : ProjectiveState →L[ℝ] ℝ :=
  (fderiv ℝ entranceWeakLogRate y).comp (entranceRadialInverseDifferential y)

def entranceWallWeightedMatrix (k : ℝ) (y : ProjectiveState) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![y 1 * entranceStrongLogDifferential y (Pi.single 1 1),
      y 3 / k ^ 2 * entranceStrongLogDifferential y (Pi.single 3 1);
    k ^ 2 * y 1 * entranceWeakLogDifferential y (Pi.single 1 1),
      y 3 * entranceWeakLogDifferential y (Pi.single 3 1)]

def entranceWallWeightedColumn (k : ℝ) (y : ProjectiveState) (j : Fin 2) : ℝ :=
  |entranceWallWeightedMatrix k y 0 j| + |entranceWallWeightedMatrix k y 1 j|

/-- Canonical coefficients agree with the derivatives in every actual local radial inverse. -/
theorem EntranceRadialInverseAt.wallLogDifferential_eq {y : ProjectiveState} {k : ℝ}
    {Ψ : ProjectiveState → ProjectiveState} (H : EntranceRadialInverseAt y Ψ)
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) :
    fderiv ℝ (fun z => entranceStrongLogRate (Ψ z)) (entranceRadialCoordinates y) = entranceStrongLogDifferential y ∧
      fderiv ℝ (fun z => entranceWeakLogRate (Ψ z)) (entranceRadialCoordinates y) = entranceWeakLogDifferential y := by
  obtain ⟨hs, hw⟩ := contDiffAt_entranceWallLogRates 1 (entranceRegion_clock_pos hk hy).ne'
  constructor
  · ext v
    exact H.scalar_differential (hs.differentiableAt (by norm_num)) v
  · ext v
    exact H.scalar_differential (hw.differentiableAt (by norm_num)) v

theorem EntranceRadialInverseAt.wallWeightedMatrix_action {y : ProjectiveState} {k : ℝ}
    {Ψ : ProjectiveState → ProjectiveState} (H : EntranceRadialInverseAt y Ψ)
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (X Y : ℝ) :
    let z := entranceRadialCoordinates y
    let v : ProjectiveState := ![0, y 1 * X, 0, y 3 * Y / k ^ 2]
    ![fderiv ℝ (fun z => entranceStrongLogRate (Ψ z)) z v,
      k ^ 2 * fderiv ℝ (fun z => entranceWeakLogRate (Ψ z)) z v] =
        (entranceWallWeightedMatrix k y).mulVec ![X, Y] := by
  obtain ⟨hs, hw⟩ := entranceWallLogRates_weighted_differential (y := y) Ψ (by linarith : k ≠ 0) 0 X Y
  obtain ⟨hA, hB⟩ := H.wallLogDifferential_eq hk hy
  dsimp only at hs hw ⊢
  ext i
  fin_cases i
  · simpa [entranceWallWeightedMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hA] using hs
  · simpa [entranceWallWeightedMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hB] using hw

theorem continuousAt_entranceWallLogDifferential_apply {y : ProjectiveState} {k : ℝ}
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (hv : 0 < y 2) (v : ProjectiveState) :
    ContinuousAt (fun y => entranceStrongLogDifferential y v) y ∧
      ContinuousAt (fun y => entranceWeakLogDifferential y v) y := by
  have hm : 2 ≤ y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hu : |y 1| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.1.1]; linarith [hy.2.2.1.2]
  have hw : |y 3| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.2.2.1]; linarith [hy.2.2.2.2.2]
  have hP := (contDiffAt_entranceStablePhase_two hm hu hw).continuousAt
  have hR := (contDiffAt_entranceStableRadius_two hm hu hw hv).continuousAt
  have hpartial (i : Fin 4) := (contDiffAt_entranceStablePartial_one hm hu hw i).continuousAt
  have hbounds := entranceRegion_stable_radial_bounds hk hy
  have hchi : entranceStablePhase y - 1 ≠ 0 := by linarith [hbounds.1.1]
  have hPM : entranceStablePartial y 0 ≠ 0 := by linarith [hbounds.2.2.1]
  have hden := mul_ne_zero hchi hPM
  have hInv : ContinuousAt (fun z => entranceRadialInverseDifferential z v) y := by
    simp only [entranceRadialInverseDifferential_apply]
    apply continuousAt_pi.mpr
    intro i
    fin_cases i
    · exact ((((hR.div ((hP.sub_const 1).mul (hpartial 0)) hden).mul_const (v 0)).sub
        (((hpartial 1).div (hpartial 0) hPM).mul_const (v 1))).sub
        (((continuousAt_apply 2 y).div ((hP.sub_const 1).mul (hpartial 0)) hden).mul_const (v 2))).sub
        (((hpartial 3).div (hpartial 0) hPM).mul_const (v 3))
    all_goals exact continuousAt_const
  obtain ⟨hs, hw'⟩ := contDiffAt_entranceWallLogRates 1 (entranceRegion_clock_pos hk hy).ne'
  exact ⟨(hs.continuousAt_fderiv (by norm_num)).clm_apply hInv,
    (hw'.continuousAt_fderiv (by norm_num)).clm_apply hInv⟩

theorem continuousAt_entranceWallWeightedMatrix {y : ProjectiveState} {k : ℝ}
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (hv : 0 < y 2) :
    ContinuousAt (entranceWallWeightedMatrix k) y := by
  have h1 := continuousAt_entranceWallLogDifferential_apply hk hy hv (Pi.single 1 1)
  have h3 := continuousAt_entranceWallLogDifferential_apply hk hy hv (Pi.single 3 1)
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · exact (continuousAt_apply 1 y).mul h1.1
  · exact ((continuousAt_apply 3 y).div_const _).mul h3.1
  · exact ((continuousAt_apply 1 y).const_mul _).mul h1.2
  · exact (continuousAt_apply 3 y).mul h3.2

theorem continuousAt_entranceWallWeightedColumn {y : ProjectiveState} {k : ℝ}
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (hv : 0 < y 2) (j : Fin 2) :
    ContinuousAt (fun y => entranceWallWeightedColumn k y j) y := by
  have hc := continuousAt_entranceWallWeightedMatrix hk hy hv
  exact (continuousAt_pi.mp (continuousAt_pi.mp hc 0) j).abs.add
    (continuousAt_pi.mp (continuousAt_pi.mp hc 1) j).abs

theorem entranceWallWeightedColumn_nonneg (k : ℝ) (y : ProjectiveState) (j : Fin 2) :
    0 ≤ entranceWallWeightedColumn k y j := add_nonneg (abs_nonneg _) (abs_nonneg _)

theorem exists_entranceWallWeightedColumn_bounds :
    ∃ C > (0 : ℝ), ∀ (k : ℝ) (y : ProjectiveState), 7 / 4 ≤ k → entranceRegion k y → 0 < y 2 →
      entranceWallWeightedColumn k y 0 ≤ C * (y 1 + k * y 1 * (y 2 + y 1 + y 3)) ∧
        entranceWallWeightedColumn k y 1 ≤ C * (y 3 / k ^ 2 + y 1 * y 3 / k + y 3 * (y 1 + y 3) / k ^ 3) := by
  obtain ⟨C, hC, HC⟩ := exists_entranceWallLogRates_weighted_bounds
  refine ⟨C, hC, ?_⟩
  intro k y hk hy hv
  obtain ⟨Ψ, H⟩ := exists_entranceRegion_radial_inverse hk hy hv
  obtain ⟨_, h11, h12, h21, h22⟩ := HC k y hk hy hv Ψ H
  obtain ⟨hA, hB⟩ := H.wallLogDifferential_eq hk hy
  rw [hA] at h11 h12
  rw [hB] at h21 h22
  constructor
  · exact (add_le_add h11 h21).trans_eq (by ring)
  · exact (add_le_add h12 h22).trans_eq (by ring)

end BianchiIX
