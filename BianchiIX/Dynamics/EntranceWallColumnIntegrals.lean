import BianchiIX.Dynamics.EntranceWallLinearization
import BianchiIX.Dynamics.EntranceWeightedEnvelopeIntegrals
import BianchiIX.Dynamics.EntranceArrival

noncomputable section

namespace BianchiIX

open Set MeasureTheory

/-- Every subinterval retains the original strong and weak wall factors separately. -/
theorem exists_scaled_entrance_wall_column_integrals :
    ∃ C > (0 : ℝ), ∀ (Y : ℝ → ProjectiveState) (a : ℝ → ℝ) (s t k : ℝ),
      7 / 4 ≤ k → s ≤ t →
      (∀ r ∈ Icc s t, HasDerivAt Y (a r • projectiveField (Y r)) r) →
      ContinuousOn a (Icc s t) → (∀ r ∈ Icc s t, 0 ≤ a r) →
      (∀ r ∈ Icc s t, entranceRegion k (Y r)) → (∀ r ∈ Icc s t, 0 < Y r 2) →
      ∀ b c : ℝ, s ≤ b → b ≤ c → c ≤ t →
        (∫ r in b..c, entranceWallWeightedColumn k (Y r) 0 * (a r * entranceClockRate (Y r))) ≤ C * Y s 1 ∧
        (∫ r in b..c, entranceWallWeightedColumn k (Y r) 1 * (a r * entranceClockRate (Y r))) ≤ C * Y s 3 / k ^ 2 := by
  obtain ⟨C, hC, HC⟩ := exists_entranceWallWeightedColumn_bounds
  refine ⟨12 * C, by positivity, ?_⟩
  intro Y a s t k hk hst hY hac ha hy hv b c hsb hbc hct
  have hsub : Icc b c ⊆ Icc s t := fun r hr => ⟨hsb.trans hr.1, hr.2.trans hct⟩
  have hb : b ∈ Icc s t := ⟨hsb, hbc.trans hct⟩
  have hk0 : 0 < k := by linarith
  have hu := (hy s ⟨le_rfl, hst⟩).2.2.1.1
  have hw := (hy s ⟨le_rfl, hst⟩).2.2.2.2.1
  have hwall := (scaled_entrance_wall_budgets hk hst hY hac ha hy hv).1 b hb
  obtain ⟨hI0, hI1⟩ := scaled_entrance_weighted_envelope_integrals hk hbc
    (fun r hr => hY r (hsub hr)) (hac.mono hsub) (fun r hr => ha r (hsub hr))
    (fun r hr => hy r (hsub hr)) (fun r hr => hv r (hsub hr))
  let q := fun r => a r * entranceClockRate (Y r)
  have hq (r : ℝ) (hr : r ∈ Icc b c) : 0 ≤ q r :=
    mul_nonneg (ha r (hsub hr)) (entranceRegion_clock_pos hk (hy r (hsub hr))).le
  have hqc : ContinuousOn q (Icc b c) := (hac.mul
    (continuous_entranceClockRate.comp_continuousOn (HasDerivAt.continuousOn hY))).mono hsub
  have hcoord (i : Fin 4) : ContinuousOn (fun r => Y r i) (Icc b c) :=
    ((continuous_apply i).comp_continuousOn (HasDerivAt.continuousOn hY)).mono hsub
  have hcol (j : Fin 2) : ContinuousOn (fun r => entranceWallWeightedColumn k (Y r) j) (Icc b c) := by
    intro r hr
    exact ((continuousAt_entranceWallWeightedColumn hk (hy r (hsub hr)) (hv r (hsub hr)) j).comp
      (hY r (hsub hr)).continuousAt).continuousWithinAt
  have htransfer {f g : ℝ → ℝ} (hf : ContinuousOn f (Icc b c)) (hg : ContinuousOn g (Icc b c))
      (hfg : ∀ r ∈ Icc b c, f r ≤ C * g r) :
      (∫ r in b..c, f r * q r) ≤ C * ∫ r in b..c, g r * q r := by
    have HI := intervalIntegral.integral_mono_on (μ := volume) hbc
      ((hf.mul hqc).intervalIntegrable_of_Icc hbc)
      (((hg.mul hqc).const_mul C).intervalIntegrable_of_Icc hbc) (fun r hr => show
        f r * q r ≤ C * (g r * q r) from by
          convert! mul_le_mul_of_nonneg_right (hfg r hr) (hq r hr) using 1
          ring)
    simpa only [intervalIntegral.integral_const_mul, Pi.mul_apply] using HI
  constructor
  · have hg : ContinuousOn (fun r => Y r 1 + k * Y r 1 * (Y r 2 + Y r 1 + Y r 3)) (Icc b c) :=
      (hcoord 1).add (((hcoord 1).const_mul k).mul (((hcoord 2).add (hcoord 1)).add (hcoord 3)))
    have H := htransfer (hcol 0) hg (fun r hr => (HC k (Y r) hk (hy r (hsub hr)) (hv r (hsub hr))).1)
    apply H.trans ((mul_le_mul_of_nonneg_left hI0 hC.le).trans ?_)
    nlinarith only [mul_le_mul_of_nonneg_left hwall.1 hC.le]
  · have hg : ContinuousOn (fun r => Y r 3 / k ^ 2 + Y r 1 * Y r 3 / k +
        Y r 3 * (Y r 1 + Y r 3) / k ^ 3) (Icc b c) :=
      (((hcoord 3).div_const (k ^ 2)).add (((hcoord 1).mul (hcoord 3)).div_const k)).add
        (((hcoord 3).mul ((hcoord 1).add (hcoord 3))).div_const (k ^ 3))
    have H := htransfer (hcol 1) hg (fun r hr => (HC k (Y r) hk (hy r (hsub hr)) (hv r (hsub hr))).2)
    apply H.trans ((mul_le_mul_of_nonneg_left hI1 hC.le).trans ?_)
    rw [← mul_div_assoc]
    apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hk0)).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hwall.2 hC.le, mul_nonneg hC.le hw]

theorem exists_normalized_entrance_wall_column_integrals :
    ∃ C > (0 : ℝ), ∀ (x : NormalizedState) (t₀ s t k : ℝ),
      stateConstraint x = 1 → 7 / 4 ≤ k → t₀ ≤ s → s ≤ t →
      (∀ r ∈ Icc s t, 0 < normalizedProjectiveRate x t₀ r) →
      let Y := fun r => toProjectiveState (normalizedMaxCurve x t₀ r)
      (∀ r ∈ Icc s t, entranceRegion k (Y r)) → 0 < Y s 2 →
      ∀ b c : ℝ, s ≤ b → b ≤ c → c ≤ t →
        (∫ r in b..c, entranceWallWeightedColumn k (Y r) 0 *
          (normalizedProjectiveRate x t₀ r * entranceClockRate (Y r))) ≤ C * Y s 1 ∧
        (∫ r in b..c, entranceWallWeightedColumn k (Y r) 1 *
          (normalizedProjectiveRate x t₀ r * entranceClockRate (Y r))) ≤ C * Y s 3 / k ^ 2 := by
  obtain ⟨C, hC, HC⟩ := exists_scaled_entrance_wall_column_integrals
  refine ⟨C, hC, ?_⟩
  intro x t₀ s t k hc hk hs hst hA Y hy hvs
  have hdom (r : ℝ) (hr : s ≤ r) := normalizedMaxDomain_contains_Ici_of_constraint hc t₀ (hs.trans hr)
  have hY (r : ℝ) (hr : r ∈ Icc s t) : HasDerivAt Y
      (normalizedProjectiveRate x t₀ r • projectiveField (Y r)) r := by
    have H := normalizedMaxCurve_forward_of_constraint hc (hs.trans hr.1)
    exact hasDerivAt_toProjectiveState_normalized H.1 (hA r hr).ne' H.2.1
  have hv (r : ℝ) (hr : r ∈ Icc s t) : 0 < Y r 2 :=
    normalized_projective_wall_pos (hdom s le_rfl) (hdom r hr.1)
      (hA s ⟨le_rfl, hst⟩) (hA r hr) 1 hvs
  have hac : ContinuousOn (normalizedProjectiveRate x t₀) (Icc s t) :=
    (continuousOn_normalizedProjectiveRate x t₀).mono (fun r hr => hdom r hr.1)
  exact HC Y (normalizedProjectiveRate x t₀) s t k hk hst hY hac (fun r hr => (hA r hr).le) hy hv

theorem exists_entrance_first_arrival_wall_column_integrals :
    ∃ C > (0 : ℝ), ∀ (x : NormalizedState) (t₀ s k : ℝ),
      stateConstraint x = 1 → 7 / 4 ≤ k → t₀ ≤ s → 0 < normalizedProjectiveRate x t₀ s →
      let Y := fun r => toProjectiveState (normalizedMaxCurve x t₀ r)
      1 ≤ Y s 0 → coreRadius (Y s 0) (Y s 2) = k →
      (0 ≤ Y s 1 ∧ Y s 1 ≤ 1 / 10000) → (0 < Y s 2 ∧ Y s 2 < 1) →
      (0 ≤ Y s 3 ∧ Y s 3 ≤ 1 / 10000) →
      ∃ t > s, Y t 2 = 1 ∧ (∀ r ∈ Ico s t, Y r 2 < 1) ∧
        (∀ r ∈ Icc s t, 1 / (2 * (k + 1) ^ 2) ≤ normalizedProjectiveRate x t₀ r ∧ entranceRegion k (Y r)) ∧
        ∀ b c : ℝ, s ≤ b → b ≤ c → c ≤ t →
          (∫ r in b..c, entranceWallWeightedColumn k (Y r) 0 *
            (normalizedProjectiveRate x t₀ r * entranceClockRate (Y r))) ≤ C * Y s 1 ∧
          (∫ r in b..c, entranceWallWeightedColumn k (Y r) 1 *
            (normalizedProjectiveRate x t₀ r * entranceClockRate (Y r))) ≤ C * Y s 3 / k ^ 2 := by
  obtain ⟨C, hC, HC⟩ := exists_normalized_entrance_wall_column_integrals
  refine ⟨C, hC, ?_⟩
  intro x t₀ s k hc hk hs hA Y hm hR hu hv hw
  obtain ⟨t, hst, hhit, hbefore, hregion, _⟩ :=
    exists_normalized_entrance_first_arrival hc hk hs hA hm hR hu hv hw
  have hK : 0 < k + 1 := by linarith
  have hpos : 0 < 1 / (2 * (k + 1) ^ 2) := by positivity
  refine ⟨t, hst, hhit, hbefore, hregion, ?_⟩
  exact HC x t₀ s t k hc hk hs hst.le (fun r hr => hpos.trans_le (hregion r hr).1)
    (fun r hr => (hregion r hr).2) hv.1

end BianchiIX
