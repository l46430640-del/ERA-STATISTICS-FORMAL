import BianchiIX.Dynamics.StableClockResidualState
import BianchiIX.Dynamics.StableClockResidualWeights
import BianchiIX.Dynamics.StableResidualJetDecay

noncomputable section

namespace BianchiIX

def stableClockResidualRate (c s : ℝ) (y : StableState) : ℝ :=
  stableClockResidual c (y, s)

theorem stableClockResidualRate_fderiv {c s : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hs : 0 ≤ s)
    (hg : ContDiffAt ℝ 2 (stableClockResidualState c) (stableClockFlow c (y, s))) (v : StableState) :
    fderiv ℝ (stableClockResidualRate c s) y v =
      fderiv ℝ (stableClockResidualState c) (stableClockFlow c (y, s))
        (fderiv ℝ (fun z => stableClockFlow c (z, s)) y v) := by
  exact congrArg (fun L : StableState →L[ℝ] ℝ => L v)
    (((hg.differentiableAt (by norm_num)).hasFDerivAt.comp y
      ((contDiffAt_stableClockFlow_slice hc hy hs).differentiableAt (by norm_num)).hasFDerivAt).fderiv)

theorem stableClockResidualRate_fderiv2 {c s : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hs : 0 ≤ s)
    (hg : ContDiffAt ℝ 2 (stableClockResidualState c) (stableClockFlow c (y, s))) (v w : StableState) :
    fderiv ℝ (fderiv ℝ (stableClockResidualRate c s)) y v w =
      fderiv ℝ (stableClockResidualState c) (stableClockFlow c (y, s))
        (fderiv ℝ (fderiv ℝ (fun z => stableClockFlow c (z, s))) y v w) +
      fderiv ℝ (fderiv ℝ (stableClockResidualState c)) (stableClockFlow c (y, s))
        (fderiv ℝ (fun z => stableClockFlow c (z, s)) y v)
        (fderiv ℝ (fun z => stableClockFlow c (z, s)) y w) :=
  fderiv2_comp_apply (contDiffAt_stableClockFlow_slice hc hy hs) hg v w

theorem exists_stableClockResidualRate_weighted_decay :
    ∃ C > (0 : ℝ), ∀ (c s : ℝ) (y : StableState), 2 ≤ c → y ∈ stableParameterDomain c → 0 ≤ s →
      let b := |y 1| + |y 2|
      let q := Real.exp (-(c + 1) / 16 * s)
      ContDiffAt ℝ 2 (stableClockResidualRate c s) y ∧
        |stableClockResidualRate c s y| ≤ C / (c + 1) ^ 2 * |y 1| * b ^ 3 * q ∧
        (∀ v, |fderiv ℝ (stableClockResidualRate c s) y v| ≤
          C / (c + 1) ^ 2 * b ^ 3 * stableFirstInputWeight b v * q) ∧
        (∀ v w, |fderiv ℝ (fderiv ℝ (stableClockResidualRate c s)) y v w| ≤
          C / (c + 1) ^ 2 * b ^ 2 * stableFirstInputWeight b v * stableFirstInputWeight b w * q) := by
  obtain ⟨C, hC, HC⟩ := exists_stableClockResidualState_bounds
  let E := Real.exp 1
  let F := 400000000 * E ^ 3
  have hE : 1 ≤ E := Real.one_le_exp (by norm_num)
  have hE0 : 0 ≤ E := le_trans (by norm_num) hE
  have hF : 0 < F := by dsimp [F, E]; positivity
  have hF1 : 1 ≤ F := by
    have H := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hE 3
    dsimp [F]
    norm_num only [one_pow] at H
    linarith
  have hF969 : 969 * E ≤ F := by
    have H := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hE 2) hE0
    norm_num only [one_pow, mul_one] at H
    dsimp [F]
    nlinarith only [H, hE0]
  refine ⟨F * C, mul_pos hF hC, ?_⟩
  intro c s y hc hy hs
  dsimp only
  let b := |y 1| + |y 2|
  let q := Real.exp (-(c + 1) / 16 * s)
  let Q := C / (c + 1) ^ 2
  let Y := stableClockFlow c (y, s)
  let J := fderiv ℝ (fun z => stableClockFlow c (z, s)) y
  let H := fderiv ℝ (fderiv ℝ (fun z => stableClockFlow c (z, s))) y
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hb1 : b ≤ 1 := by dsimp [b]; linarith [hy.2.1, hy.2.2]
  have hq : 0 ≤ q := (Real.exp_pos _).le
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hscale : F * C / (c + 1) ^ 2 = F * Q := by dsimp [Q]; ring
  rw [hscale]
  obtain ⟨hm, hu, hw⟩ := stableClockFlow_band hc hy hs
  obtain ⟨hg, h0, h1, h2⟩ := HC c Y hc hm
    (hu.trans (by linarith [hy.2.1])) (hw.trans (by linarith [hy.2.2]))
  have hY := stableClockFlow_residual_weights hc hy hs
  have hU : |Y 1| ≤ b * q :=
    hY.2.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (abs_nonneg (y 2))) hq)
  have hJ (v : StableState) := stableClockFlow_first_residual_weights hc hy hs v
  have hH (v w : StableState) := stableClockFlow_second_residual_weights hc hy hs v w
  refine ⟨hg.comp y (g := stableClockResidualState c)
    (f := fun z => stableClockFlow c (z, s)) (contDiffAt_stableClockFlow_slice hc hy hs), ?_, ?_, ?_⟩
  · have h3 := pow_le_pow_left₀ (by positivity : 0 ≤ |Y 1| + |Y 2|) hY.1 3
    have H0 := mul_le_mul_of_nonneg_left (mul_le_mul hY.2 h3 (by positivity) (by positivity)) hQ
    have H1 := mul_le_mul_of_nonneg_right hF1 (show 0 ≤ Q * |y 1| * b ^ 3 * q by positivity)
    change |stableClockResidualState c Y| ≤ _
    nlinarith only [h0, H0, H1]
  · intro v
    rw [stableClockResidualRate_fderiv hc hy hs hg]
    have HB := stableResidualFirstDecay_bound hb hE0 hq hY.1 hU (hJ v).1 (hJ v).2.1 (hJ v).2.2
    have H0 := mul_le_mul_of_nonneg_left HB hQ
    have H1 := mul_le_mul_of_nonneg_right hF969
      (show 0 ≤ Q * b ^ 3 * stableFirstInputWeight b v * q by
        have := stableFirstInputWeight_nonneg hb v
        positivity)
    have R := h1 (J v)
    nlinarith only [R, H0, H1]
  · intro v w
    rw [stableClockResidualRate_fderiv2 hc hy hs hg]
    have HB := stableResidualSecondDecay_bound hb hb1 hE hq hY.1 hU
      (hJ v).1 (hJ w).1 (hJ v).2.1 (hJ w).2.1 (hJ v).2.2 (hJ w).2.2 (hH v w).1 (hH v w).2
    have H0 := mul_le_mul_of_nonneg_left HB hQ
    have R1 := h1 (H v w)
    have R2 := h2 (J v) (J w)
    have R := abs_add_le (fderiv ℝ (stableClockResidualState c) Y (H v w))
      (fderiv ℝ (fderiv ℝ (stableClockResidualState c)) Y (J v) (J w))
    dsimp only [F, E] at H0 ⊢
    nlinarith only [R, R1, R2, H0]

end BianchiIX
