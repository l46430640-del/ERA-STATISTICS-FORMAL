import BianchiIX.Dynamics.EntranceWallSolutionGrowth

noncomputable section

namespace BianchiIX

open Set MeasureTheory

def entranceWallRadialSource (k : ℝ) (y : ProjectiveState) : Fin 2 → ℝ :=
  ![entranceStrongLogDifferential y (Pi.single 0 1), k ^ 2 * entranceWeakLogDifferential y (Pi.single 0 1)]

theorem exists_entranceWallRadialSource_bounds :
    ∃ C > (0 : ℝ), ∀ (k : ℝ) (y : ProjectiveState), 7 / 4 ≤ k → entranceRegion k y → 0 < y 2 →
      ContinuousAt (entranceWallRadialSource k) y ∧ ‖entranceWallRadialSource k y‖ ≤ C := by
  obtain ⟨C, hC, HC⟩ := exists_entranceWallLogRates_weighted_bounds
  refine ⟨C, hC, ?_⟩
  intro k y hk hy hv
  obtain ⟨hs, hw⟩ := continuousAt_entranceWallLogDifferential_apply hk hy hv (Pi.single 0 1)
  obtain ⟨Ψ, H⟩ := exists_entranceRegion_radial_inverse hk hy hv
  have hb := (HC k y hk hy hv Ψ H).1
  obtain ⟨hA, hB⟩ := H.wallLogDifferential_eq hk hy
  rw [hA, hB] at hb
  constructor
  · apply continuousAt_pi.mpr
    intro i
    fin_cases i
    · exact hs
    · exact hw.const_mul _
  · apply (pi_norm_le_iff_of_nonneg hC.le).mpr
    intro i
    fin_cases i
    · change |entranceStrongLogDifferential y (Pi.single 0 1)| ≤ C
      exact (le_add_of_nonneg_right (mul_nonneg (sq_nonneg k) (abs_nonneg _))).trans hb
    · change |k ^ 2 * entranceWeakLogDifferential y (Pi.single 0 1)| ≤ C
      rw [abs_mul, abs_of_nonneg (sq_nonneg k)]
      exact (le_add_of_nonneg_left (abs_nonneg _)).trans hb

/-- The transverse response estimate in (C.30), for solutions of the actual coefficient system. -/
theorem exists_scaled_entrance_wall_radial_response :
    ∃ C > (0 : ℝ), ∀ (Y : ℝ → ProjectiveState) (a : ℝ → ℝ) (s t k : ℝ),
      7 / 4 ≤ k → s ≤ t →
      (∀ r ∈ Icc s t, HasDerivAt Y (a r • projectiveField (Y r)) r) →
      ContinuousOn a (Icc s t) → (∀ r ∈ Icc s t, 0 ≤ a r) →
      (∀ r ∈ Icc s t, entranceRegion k (Y r)) → (∀ r ∈ Icc s t, 0 < Y r 2) →
      ∀ b c : ℝ, s ≤ b → b ≤ c → c ≤ t →
      ∀ (f : ℝ → (Fin 2 → ℝ)) (Z : ℝ → ℝ), ContinuousOn Z (Icc b c) →
      (∀ r ∈ Icc b c, HasDerivAt f
        (((a r * entranceClockRate (Y r)) • entranceWallWeightedMatrix k (Y r)).mulVec (f r) +
          ((a r * entranceClockRate (Y r)) * Z r) • entranceWallRadialSource k (Y r)) r) →
      |f c 0 - f b 0| + |f c 1 - f b 1| ≤ C * (Y s 1 * |f b 0| + Y s 3 / k ^ 2 * |f b 1| +
        ∫ r in b..c, |Z r| * (a r * entranceClockRate (Y r))) := by
  obtain ⟨K, hK, HK⟩ := exists_scaled_entrance_wall_solution_growth
  obtain ⟨J, hJ, HJ⟩ := exists_entranceWallRadialSource_bounds
  refine ⟨2 * K * (J + 1), by positivity, ?_⟩
  intro Y a s t k hk hst hY hac ha hy hv b c hsb hbc hct f Z hZ hf
  have hsub : Icc b c ⊆ Icc s t := fun r hr => ⟨hsb.trans hr.1, hr.2.trans hct⟩
  let q := fun r => a r * entranceClockRate (Y r)
  let p := fun r => (q r * Z r) • entranceWallRadialSource k (Y r)
  have hq (r : ℝ) (hr : r ∈ Icc b c) : 0 ≤ q r :=
    mul_nonneg (ha r (hsub hr)) (entranceRegion_clock_pos hk (hy r (hsub hr))).le
  have hqc : ContinuousOn q (Icc b c) := (hac.mul
    (continuous_entranceClockRate.comp_continuousOn (HasDerivAt.continuousOn hY))).mono hsub
  have hsource : ContinuousOn (fun r => entranceWallRadialSource k (Y r)) (Icc b c) := by
    intro r hr
    exact (((HJ k (Y r) hk (hy r (hsub hr)) (hv r (hsub hr))).1).comp
      (hY r (hsub hr)).continuousAt).continuousWithinAt
  have hp : ContinuousOn p (Icc b c) := (hqc.mul hZ).smul hsource
  have hpoint (r : ℝ) (hr : r ∈ Icc b c) : ‖p r‖ ≤ J * (|Z r| * q r) := by
    simp only [p, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hq r hr)]
    exact (mul_le_mul_of_nonneg_left (HJ k (Y r) hk (hy r (hsub hr)) (hv r (hsub hr))).2
      (mul_nonneg (hq r hr) (abs_nonneg _))).trans_eq (by ring)
  have hP : (∫ r in b..c, ‖p r‖) ≤ J * ∫ r in b..c, |Z r| * q r := by
    have H := intervalIntegral.integral_mono_on (μ := volume) hbc (hp.norm.intervalIntegrable_of_Icc hbc)
      (((hZ.abs.mul hqc).const_mul J).intervalIntegrable_of_Icc hbc) hpoint
    simpa only [intervalIntegral.integral_const_mul, Pi.mul_apply] using H
  have hI0 : 0 ≤ ∫ r in b..c, |Z r| * q r :=
    intervalIntegral.integral_nonneg hbc (fun r hr => mul_nonneg (abs_nonneg _) (hq r hr))
  let B := Y s 1 * |f b 0| + Y s 3 / k ^ 2 * |f b 1|
  have hB : 0 ≤ B := by
    have hs : s ∈ Icc s t := ⟨le_rfl, hst⟩
    exact add_nonneg (mul_nonneg (hy s hs).2.2.1.1 (abs_nonneg _))
      (mul_nonneg (div_nonneg (hy s hs).2.2.2.2.1 (sq_nonneg k)) (abs_nonneg _))
  have HG := HK Y a s t k hk hst hY hac ha hy hv b c hsb hbc hct f p hp hf
  have HD : ‖f c - f b‖ ≤ K * (J + 1) * (B + ∫ r in b..c, |Z r| * q r) := by
    apply HG.trans ((mul_le_mul_of_nonneg_left (add_le_add (le_refl B) hP) hK.le).trans ?_)
    have HB : B + J * (∫ r in b..c, |Z r| * q r) ≤ (J + 1) * (B + ∫ r in b..c, |Z r| * q r) := by
      nlinarith only [mul_nonneg hJ.le hB, hI0]
    exact (mul_le_mul_of_nonneg_left HB hK.le).trans_eq (by ring)
  have hv' (i : Fin 2) : |f c i - f b i| ≤ ‖f c - f b‖ := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (f c - f b) i
  exact (add_le_add (hv' 0) (hv' 1)).trans (by nlinarith only [HD])

end BianchiIX
