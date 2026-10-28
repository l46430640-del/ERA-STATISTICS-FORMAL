import BianchiIX.Dynamics.EntranceWallActiveSourceBudget
import BianchiIX.Dynamics.EntranceWallRadialResponse

noncomputable section

namespace BianchiIX

open Set MeasureTheory

/-- The active forcing contributes only k inverse to the zero-initial-data wall response. -/
theorem exists_scaled_entrance_forced_wall_response :
    ∃ C > (0 : ℝ), ∀ (Y : ℝ → ProjectiveState) (a : ℝ → ℝ) (s t k : ℝ),
      7 / 4 ≤ k → s ≤ t →
      (∀ r ∈ Icc s t, HasDerivAt Y (a r • projectiveField (Y r)) r) →
      ContinuousOn a (Icc s t) → (∀ r ∈ Icc s t, 0 ≤ a r) →
      (∀ r ∈ Icc s t, entranceRegion k (Y r)) → (∀ r ∈ Icc s t, 0 < Y r 2) →
      k ^ 2 * (Y s 1 + Y s 3) ≤ 1 →
      ∀ (f : ℝ → Fin 2 → ℝ) (Z : ℝ → ℝ), ContinuousOn Z (Icc s t) → f s = 0 →
      (∀ r ∈ Icc s t, HasDerivAt f ((a r * entranceClockRate (Y r)) •
        ((entranceWallWeightedMatrix k (Y r)).mulVec (f r) +
          Z r • entranceWallRadialSource k (Y r) + entranceWallActiveSource k (Y r))) r) →
      ∀ r ∈ Icc s t, |f r 0| + |f r 1| ≤
        C * (1 / k + ∫ z in s..r, |Z z| * (a z * entranceClockRate (Y z))) := by
  obtain ⟨K, hK, HK⟩ := exists_scaled_entrance_wall_solution_growth
  obtain ⟨J, hJ, HJ⟩ := exists_entranceWallRadialSource_bounds
  refine ⟨2 * K * (J + 1536), by positivity, ?_⟩
  intro Y a s t k hk hst hY hac ha hy hv hsmall f Z hZ hfs hf
  let q := fun r => a r * entranceClockRate (Y r)
  let p := fun r => (q r * Z r) • entranceWallRadialSource k (Y r) + q r • entranceWallActiveSource k (Y r)
  let S := fun r => ‖entranceWallActiveSource k (Y r)‖ * q r
  let E := fun r => |Z r| * q r
  have hk0 : 0 < k := by linarith
  have hqc : ContinuousOn q (Icc s t) := hac.mul
    (continuous_entranceClockRate.comp_continuousOn (HasDerivAt.continuousOn hY))
  have hq (r : ℝ) (hr : r ∈ Icc s t) : 0 ≤ q r :=
    mul_nonneg (ha r hr) (entranceRegion_clock_pos hk (hy r hr)).le
  have hRc : ContinuousOn (fun r => entranceWallRadialSource k (Y r)) (Icc s t) := by
    intro r hr
    exact (((HJ k (Y r) hk (hy r hr) (hv r hr)).1).comp (hY r hr).continuousAt).continuousWithinAt
  have hAc : ContinuousOn (fun r => entranceWallActiveSource k (Y r)) (Icc s t) := by
    intro r hr
    exact ((continuousAt_entranceWallActiveSource hk (hy r hr) (hv r hr)).comp (hY r hr).continuousAt).continuousWithinAt
  have hpc : ContinuousOn p (Icc s t) := ((hqc.mul hZ).smul hRc).add (hqc.smul hAc)
  have hEc : ContinuousOn E (Icc s t) := hZ.abs.mul hqc
  have hSc : ContinuousOn S (Icc s t) := hAc.norm.mul hqc
  have hpbound (r : ℝ) (hr : r ∈ Icc s t) : ‖p r‖ ≤ J * E r + S r := by
    apply (norm_add_le _ _).trans
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hq r hr)]
    exact (add_le_add (mul_le_mul_of_nonneg_left (HJ k (Y r) hk (hy r hr) (hv r hr)).2
      (mul_nonneg (hq r hr) (abs_nonneg _))) le_rfl).trans_eq (by dsimp [E, S]; ring)
  intro r hr
  have hsub : Icc s r ⊆ Icc s t := Icc_subset_Icc_right hr.2
  have hfeq (z : ℝ) (hz : z ∈ Icc s r) : HasDerivAt f
      (((a z * entranceClockRate (Y z)) • entranceWallWeightedMatrix k (Y z)).mulVec (f z) + p z) z := by
    simpa only [p, q, smul_add, smul_smul, Matrix.smul_mulVec, add_assoc] using hf z (hsub hz)
  have H := HK Y a s t k hk hst hY hac ha hy hv s r le_rfl hr.1 hr.2 f p (hpc.mono hsub) hfeq
  simp only [hfs, Pi.zero_apply, abs_zero, mul_zero, zero_add, sub_zero] at H
  have HI := intervalIntegral.integral_mono_on (μ := volume) hr.1
    ((hpc.norm.mono hsub).intervalIntegrable_of_Icc hr.1)
    ((((hEc.const_mul J).add hSc).mono hsub).intervalIntegrable_of_Icc hr.1)
    (fun z hz => hpbound z (hsub hz))
  simp only [Pi.add_apply] at HI
  rw [intervalIntegral.integral_add (((hEc.const_mul J).mono hsub).intervalIntegrable_of_Icc hr.1)
    ((hSc.mono hsub).intervalIntegrable_of_Icc hr.1), intervalIntegral.integral_const_mul] at HI
  have HS := scaled_entrance_wall_active_source_budget hk hr.1 (fun z hz => hY z (hsub hz))
    (hac.mono hsub) (fun z hz => ha z (hsub hz)) (fun z hz => hy z (hsub hz))
    (fun z hz => hv z (hsub hz)) hsmall
  have HI' : (∫ z in s..r, ‖p z‖) ≤ J * (∫ z in s..r, E z) + 1536 / k :=
    HI.trans (add_le_add le_rfl HS)
  have hI0 : 0 ≤ ∫ z in s..r, E z :=
    intervalIntegral.integral_nonneg hr.1 (fun z hz => mul_nonneg (abs_nonneg _) (hq z (hsub hz)))
  have hsum : |f r 0| + |f r 1| ≤ 2 * ‖f r‖ := by
    have h0 := norm_le_pi_norm (f r) 0
    have h1 := norm_le_pi_norm (f r) 1
    simpa only [Real.norm_eq_abs, two_mul] using add_le_add h0 h1
  have hscale : J * (∫ z in s..r, E z) + 1536 / k ≤ (J + 1536) * (1 / k + ∫ z in s..r, E z) := by
    have HJ0 : 0 ≤ J / k := by positivity
    simp only [div_eq_mul_inv] at HJ0 ⊢
    nlinarith only [HJ0, hI0]
  calc
    _ ≤ 2 * ‖f r‖ := hsum
    _ ≤ 2 * (K * (J * (∫ z in s..r, E z) + 1536 / k)) := mul_le_mul_of_nonneg_left
      (H.trans (mul_le_mul_of_nonneg_left HI' hK.le)) (by norm_num)
    _ = (2 * K) * (J * (∫ z in s..r, E z) + 1536 / k) := by ring
    _ ≤ (2 * K) * ((J + 1536) * (1 / k + ∫ z in s..r, E z)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = _ := by dsimp [E, q]; ring

end BianchiIX
