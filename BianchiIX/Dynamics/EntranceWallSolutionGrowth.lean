import BianchiIX.Dynamics.EntranceWallMatrixBounds
import BianchiIX.Dynamics.EntranceWallColumnIntegrals

noncomputable section

namespace BianchiIX

open Set MeasureTheory

/-- The change of any forced transverse solution retains the two distinct initial wall scales. -/
theorem exists_scaled_entrance_wall_solution_growth :
    ∃ C > (0 : ℝ), ∀ (Y : ℝ → ProjectiveState) (a : ℝ → ℝ) (s t k : ℝ),
      7 / 4 ≤ k → s ≤ t →
      (∀ r ∈ Icc s t, HasDerivAt Y (a r • projectiveField (Y r)) r) →
      ContinuousOn a (Icc s t) → (∀ r ∈ Icc s t, 0 ≤ a r) →
      (∀ r ∈ Icc s t, entranceRegion k (Y r)) → (∀ r ∈ Icc s t, 0 < Y r 2) →
      ∀ b c : ℝ, s ≤ b → b ≤ c → c ≤ t →
      ∀ f p : ℝ → (Fin 2 → ℝ), ContinuousOn p (Icc b c) →
      (∀ r ∈ Icc b c, HasDerivAt f
        (((a r * entranceClockRate (Y r)) • entranceWallWeightedMatrix k (Y r)).mulVec (f r) + p r) r) →
      ‖f c - f b‖ ≤ C * (Y s 1 * |f b 0| + Y s 3 / k ^ 2 * |f b 1| + ∫ r in b..c, ‖p r‖) := by
  obtain ⟨J, hJ, HJ⟩ := exists_scaled_entrance_wall_column_integrals
  refine ⟨Real.exp (2 * J) * (J + 1), by positivity, ?_⟩
  intro Y a s t k hk hst hY hac ha hy hv b c hsb hbc hct f p hp hf
  have hsub : Icc b c ⊆ Icc s t := fun r hr => ⟨hsb.trans hr.1, hr.2.trans hct⟩
  have hs : s ∈ Icc s t := ⟨le_rfl, hst⟩
  have hk0 : 0 < k := by linarith
  have hk1 : 1 ≤ k := by linarith
  have hu := (hy s hs).2.2.1.1
  have hw := (hy s hs).2.2.2.2.1
  have hu1 : Y s 1 ≤ 1 := by linarith [(hy s hs).2.2.1.2]
  have hw1 : Y s 3 ≤ 1 := by linarith [(hy s hs).2.2.2.2.2]
  have hwk : Y s 3 / k ^ 2 ≤ 1 :=
    (div_le_self hw (one_le_pow₀ hk1)).trans hw1
  let q := fun r => a r * entranceClockRate (Y r)
  let L := fun (j : Fin 2) r => entranceWallWeightedColumn k (Y r) j * q r
  let σ := fun r => L 0 r + L 1 r
  let R := fun r => L 0 r * |f b 0| + L 1 r * |f b 1| + ‖p r‖
  have hq (r : ℝ) (hr : r ∈ Icc b c) : 0 ≤ q r :=
    mul_nonneg (ha r (hsub hr)) (entranceRegion_clock_pos hk (hy r (hsub hr))).le
  have hqc : ContinuousOn q (Icc b c) := (hac.mul
    (continuous_entranceClockRate.comp_continuousOn (HasDerivAt.continuousOn hY))).mono hsub
  have hLc (j : Fin 2) : ContinuousOn (L j) (Icc b c) := by
    apply ContinuousOn.mul ?_ hqc
    intro r hr
    exact ((continuousAt_entranceWallWeightedColumn hk (hy r (hsub hr)) (hv r (hsub hr)) j).comp
      (hY r (hsub hr)).continuousAt).continuousWithinAt
  have hL0 (j : Fin 2) (r : ℝ) (hr : r ∈ Icc b c) : 0 ≤ L j r :=
    mul_nonneg (entranceWallWeightedColumn_nonneg _ _ _) (hq r hr)
  have hσc : ContinuousOn σ (Icc b c) := (hLc 0).add (hLc 1)
  have hRc : ContinuousOn R (Icc b c) := (((hLc 0).mul_const _).add ((hLc 1).mul_const _)).add hp.norm
  have hR0 (r : ℝ) (hr : r ∈ Icc b c) : 0 ≤ R r := add_nonneg
    (add_nonneg (mul_nonneg (hL0 0 r hr) (abs_nonneg _)) (mul_nonneg (hL0 1 r hr) (abs_nonneg _))) (norm_nonneg _)
  have H := norm_sub_initial_le_exp_integral_of_forced_rows hbc hf hσc
    (fun r hr => add_nonneg (hL0 0 r hr) (hL0 1 r hr))
    (fun r hr i => show signedRowSum (q r • entranceWallWeightedMatrix k (Y r)) i ≤ σ r from by
      convert! entranceWallWeightedMatrix_row_bound k (Y r) (hq r hr) i using 1
      dsimp [σ, L]
      ring) hRc
    (fun r hr => show ‖(q r • entranceWallWeightedMatrix k (Y r)).mulVec (f b) + p r‖ ≤ R r from by
      apply (norm_add_le _ _).trans
      have HB := add_le_add (entranceWallWeightedMatrix_forcing_bound k (Y r) (hq r hr) (f b)) (le_refl ‖p r‖)
      convert! HB using 1
      dsimp [R, L]
      ring)
  obtain ⟨hI0, hI1⟩ := HJ Y a s t k hk hst hY hac ha hy hv b c hsb hbc hct
  change (∫ r in b..c, L 0 r) ≤ J * Y s 1 at hI0
  change (∫ r in b..c, L 1 r) ≤ J * Y s 3 / k ^ 2 at hI1
  have hσI : (∫ r in b..c, σ r) ≤ 2 * J := by
    change (∫ r in b..c, L 0 r + L 1 r) ≤ _
    rw [intervalIntegral.integral_add ((hLc 0).intervalIntegrable_of_Icc hbc) ((hLc 1).intervalIntegrable_of_Icc hbc)]
    apply (add_le_add hI0 hI1).trans
    rw [mul_div_assoc]
    nlinarith only [mul_le_mul_of_nonneg_left hu1 hJ.le, mul_le_mul_of_nonneg_left hwk hJ.le]
  let B := Y s 1 * |f b 0| + Y s 3 / k ^ 2 * |f b 1|
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hP : 0 ≤ ∫ r in b..c, ‖p r‖ := intervalIntegral.integral_nonneg hbc (fun _ _ => norm_nonneg _)
  have hRI : (∫ r in b..c, R r) ≤ (J + 1) * (B + ∫ r in b..c, ‖p r‖) := by
    have hIu : IntervalIntegrable (fun r => L 0 r * |f b 0|) volume b c :=
      ((hLc 0).mul_const |f b 0|).intervalIntegrable_of_Icc hbc
    have hIw : IntervalIntegrable (fun r => L 1 r * |f b 1|) volume b c :=
      ((hLc 1).mul_const |f b 1|).intervalIntegrable_of_Icc hbc
    change (∫ r in b..c, L 0 r * |f b 0| + L 1 r * |f b 1| + ‖p r‖) ≤ _
    rw [intervalIntegral.integral_add (hIu.add hIw) (hp.norm.intervalIntegrable_of_Icc hbc),
      intervalIntegral.integral_add hIu hIw,
      intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]
    apply (add_le_add (add_le_add (mul_le_mul_of_nonneg_right hI0 (abs_nonneg _))
      (mul_le_mul_of_nonneg_right hI1 (abs_nonneg _))) le_rfl).trans
    have he : J * Y s 1 * |f b 0| + (J * Y s 3 / k ^ 2) * |f b 1| = J * B := by dsimp [B]; ring
    rw [he]
    nlinarith only [mul_nonneg hJ.le hP, hB]
  exact H.trans ((mul_le_mul (Real.exp_le_exp.mpr hσI) hRI
    (intervalIntegral.integral_nonneg hbc hR0) (Real.exp_pos _).le).trans_eq (by dsimp [B]; ring))

theorem exists_scaled_entrance_wall_basis_growth :
    ∃ C > (0 : ℝ), ∀ (Y : ℝ → ProjectiveState) (a : ℝ → ℝ) (s t k : ℝ),
      7 / 4 ≤ k → s ≤ t →
      (∀ r ∈ Icc s t, HasDerivAt Y (a r • projectiveField (Y r)) r) →
      ContinuousOn a (Icc s t) → (∀ r ∈ Icc s t, 0 ≤ a r) →
      (∀ r ∈ Icc s t, entranceRegion k (Y r)) → (∀ r ∈ Icc s t, 0 < Y r 2) →
      ∀ b c : ℝ, s ≤ b → b ≤ c → c ≤ t →
      ∀ (j : Fin 2) (f : ℝ → (Fin 2 → ℝ)), f b = Pi.single j 1 →
      (∀ r ∈ Icc b c, HasDerivAt f
        (((a r * entranceClockRate (Y r)) • entranceWallWeightedMatrix k (Y r)).mulVec (f r)) r) →
      ‖f c - Pi.single j 1‖ ≤ C * (![Y s 1, Y s 3 / k ^ 2] : Fin 2 → ℝ) j := by
  obtain ⟨C, hC, HC⟩ := exists_scaled_entrance_wall_solution_growth
  refine ⟨C, hC, ?_⟩
  intro Y a s t k hk hst hY hac ha hy hv b c hsb hbc hct j f hinit hf
  have H := HC Y a s t k hk hst hY hac ha hy hv b c hsb hbc hct f (fun _ => 0) continuousOn_const
    (fun r hr => by simpa only [add_zero] using hf r hr)
  rw [hinit] at H
  fin_cases j <;> simpa using H

end BianchiIX
