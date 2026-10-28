import BianchiIX.Dynamics.StableScaledResidualDerivatives
import BianchiIX.Dynamics.StableSecondIntegral
import BianchiIX.Dynamics.StableBoundaryStableBlock
import BianchiIX.Dynamics.StableCorrectedFlow

noncomputable section

namespace BianchiIX

def stableRescaledResidualRate (K s : ℝ) (y : StableState) : ℝ :=
  stableScaledResidual K (stableRescaledFlow K y s)

theorem hasDerivAt_stableCorrectedPhase_rescaled {c s : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) :
    HasDerivAt (fun r => stableCorrectedPhase (stableRescaledFlow (c + 1) y r 0)
      (stableRescaledFlow (c + 1) y r 1) (stableRescaledFlow (c + 1) y r 2))
      (stableRescaledResidualRate (c + 1) s y) s := by
  have hK : 0 < c + 1 := by linarith
  have hY := stableInclusion.hasFDerivAt.comp_hasDerivAt s
    (hasDerivAt_stableRescaledFlow hK hc hm hu hw hs)
  have heq (z : StableState) : stableInclusion ((c + 1) • stableOriginalField z) =
      stableResidualClock (c + 1) z • projectiveField (stableInclusion z) := by
    rw [map_smul, stableOriginalField, map_smul, ← stableBoundaryField_inclusion, smul_smul]
    congr 1
    unfold stableResidualClock
    ring
  rw [heq] at hY
  have hM : 1 < stableInclusion (stableRescaledFlow (c + 1) y s) 0 := by
    change 1 < stableRescaledFlow (c + 1) y s 0
    have H := (abs_le.mp (stableRescaledFlow_band hc hm hu hw hs).1).1
    linarith
  have H := hasDerivAt_stableCorrectedPhase_scaled hY hM (by rfl)
  simpa [stableInclusion_apply, stableRescaledResidualRate, stableScaledResidual] using H

theorem stableRescaledResidualRate_fderiv {K c s : ℝ} {y : StableState}
    (hK : 0 < K) (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s)
    (hg : ContDiffAt ℝ 2 (stableScaledResidual K) (stableRescaledFlow K y s)) (v : StableState) :
    fderiv ℝ (stableRescaledResidualRate K s) y v =
      fderiv ℝ (stableScaledResidual K) (stableRescaledFlow K y s) (stableRescaledDifferential K y s v) := by
  exact congrArg (fun L : StableState →L[ℝ] ℝ => L v)
    (((hg.differentiableAt (by norm_num)).hasFDerivAt.comp y
      (hasFDerivAt_stableRescaledFlow hK hc hm hu hw hs)).fderiv)

theorem stableRescaledResidualRate_fderiv2 {K c s : ℝ} {y : StableState}
    (hK : 0 < K) (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) (hs : 0 ≤ s)
    (hg : ContDiffAt ℝ 2 (stableScaledResidual K) (stableRescaledFlow K y s)) (v w : StableState) :
    fderiv ℝ (fderiv ℝ (stableRescaledResidualRate K s)) y v w =
      fderiv ℝ (stableScaledResidual K) (stableRescaledFlow K y s)
        (stableRescaledSecondDifferential K y s v w) +
      fderiv ℝ (fderiv ℝ (stableScaledResidual K)) (stableRescaledFlow K y s)
        (stableRescaledDifferential K y s v) (stableRescaledDifferential K y s w) := by
  have hp : ContDiffAt ℝ 2 (fun z : StableState => (z, s)) y :=
    contDiffAt_id.prodMk contDiffAt_const
  have hf : ContDiffAt ℝ 2 (fun z => stableRescaledFlow K z s) y :=
    (contDiffAt_stableRescaledFlow_two hK hc hm.le hu.le hw.le hs).comp
      (f := fun z : StableState => (z, s)) y hp
  have H := fderiv2_comp_apply hf hg v w
  rw [stableRescaledFlow_fderiv2 hK hc hm hu hw hs,
    (hasFDerivAt_stableRescaledFlow hK hc hm.le hu.le hw.le hs).fderiv] at H
  exact H

theorem exists_stableRescaledResidualRate_bounds :
    ∃ C > (0 : ℝ), ∀ (c s : ℝ) (y : StableState), 2 ≤ c → |y 0 - c| < 1 / 40 →
      |y 1| < 1 / 200 → |y 2| < 1 / 200 → 0 ≤ s →
      let Y := stableRescaledFlow (c + 1) y s
      let J := stableRescaledDifferential (c + 1) y s
      let H := stableRescaledSecondDifferential (c + 1) y s
      ContDiffAt ℝ 2 (stableRescaledResidualRate (c + 1) s) y ∧
        |stableRescaledResidualRate (c + 1) s y| ≤ C / (c + 1) ^ 2 * |Y 1| * (|Y 1| + |Y 2|) ^ 3 ∧
        (∀ v, |fderiv ℝ (stableRescaledResidualRate (c + 1) s) y v| ≤
          C / (c + 1) ^ 2 * (|J v 1| * (|Y 1| + |Y 2|) ^ 3 + |Y 1| * stableCubicFirstBudget Y (J v))) ∧
        (∀ v w, |fderiv ℝ (fderiv ℝ (stableRescaledResidualRate (c + 1) s)) y v w| ≤
          C / (c + 1) ^ 2 * (|H v w 1| * (|Y 1| + |Y 2|) ^ 3 +
            |Y 1| * stableCubicFirstBudget Y (H v w) +
            |J v 1| * stableCubicFirstBudget Y (J w) +
            |J w 1| * stableCubicFirstBudget Y (J v) +
            |Y 1| * stableCubicSecondBudget Y (J v) (J w))) := by
  obtain ⟨C, hC, HC⟩ := exists_stableScaledResidual_derivative_bounds
  refine ⟨C, hC, ?_⟩
  intro c s y hc hm hu hw hs
  dsimp only
  have hK : 0 < c + 1 := by linarith
  obtain ⟨hym, hyu, hyw⟩ := stableRescaledFlow_band hc hm.le hu.le hw.le hs
  obtain ⟨hg, h0, h1, h2⟩ := HC c (stableRescaledFlow (c + 1) y s) hc hym hyu hyw
  have hp : ContDiffAt ℝ 2 (fun z : StableState => (z, s)) y :=
    contDiffAt_id.prodMk contDiffAt_const
  have hf : ContDiffAt ℝ 2 (fun z => stableRescaledFlow (c + 1) z s) y :=
    (contDiffAt_stableRescaledFlow_two hK hc hm.le hu.le hw.le hs).comp
      (f := fun z : StableState => (z, s)) y hp
  refine ⟨hg.comp y hf, h0, ?_, ?_⟩
  · intro v
    rw [stableRescaledResidualRate_fderiv hK hc hm.le hu.le hw.le hs hg]
    exact h1 _
  · intro v w
    rw [stableRescaledResidualRate_fderiv2 hK hc hm hu hw hs hg]
    have H1 := h1 (stableRescaledSecondDifferential (c + 1) y s v w)
    have H2 := h2 (stableRescaledDifferential (c + 1) y s v) (stableRescaledDifferential (c + 1) y s w)
    have H := abs_add_le
      (fderiv ℝ (stableScaledResidual (c + 1)) (stableRescaledFlow (c + 1) y s)
        (stableRescaledSecondDifferential (c + 1) y s v w))
      (fderiv ℝ (fderiv ℝ (stableScaledResidual (c + 1))) (stableRescaledFlow (c + 1) y s)
        (stableRescaledDifferential (c + 1) y s v) (stableRescaledDifferential (c + 1) y s w))
    nlinarith only [H, H1, H2]

end BianchiIX
