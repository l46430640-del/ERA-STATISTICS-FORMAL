import BianchiIX.Algebra.ExitSinglePhaseBounds
import BianchiIX.Dynamics.ExitTailCoordinates

noncomputable section

namespace BianchiIX

def exitSingleBaseRadial (R v : ℝ) : ℝ := 2 * (exitTailGap R v - 2) * R / exitTailGap R v

def exitSingleErrorRadial (R u v w : ℝ) : ℝ :=
  exitSingleDefect u v w * (2 * R / exitSingleBase R v -
    (R ^ 2 - 4 + exitSingleDefect u v w) * exitSingleBaseRadial R v / (exitSingleBase R v) ^ 2)

def exitSingleErrorWallFactor (R u v w : ℝ) : ℝ :=
  1 + (R ^ 2 - 4 + 2 * exitSingleDefect u v w) / exitSingleBase R v

theorem exitSinglePhase_differential {v : ℝ} {Y : ExitTailState}
    (hg : v ^ 2 < (Y 0) ^ 2) (hH : exitSingleBase (Y 0) v ≠ 0)
    (hS : 0 < (Y 0) ^ 2 + exitSingleError (Y 0) (Y 1) v (Y 2)) :
    ContDiffAt ℝ 2 (fun Z : ExitTailState => exitSinglePhase (Z 0) (Z 1) v (Z 2)) Y ∧
      ∀ d : ExitTailState,
      fderiv ℝ (fun Z : ExitTailState => exitSinglePhase (Z 0) (Z 1) v (Z 2)) Y d =
        ((2 * Y 0 + exitSingleErrorRadial (Y 0) (Y 1) v (Y 2)) * d 0 +
          exitSingleErrorWallFactor (Y 0) (Y 1) v (Y 2) *
            ((2 * (Y 1 - Y 2) - 2 * v) * d 1 + (-2 * (Y 1 - Y 2) - 2 * v) * d 2)) /
          (4 * Real.sqrt ((Y 0) ^ 2 + exitSingleError (Y 0) (Y 1) v (Y 2))) := by
  have H0 : ContDiffAt ℝ 2 (fun Z : ExitTailState => Z 0) Y := by fun_prop
  have H1 : ContDiffAt ℝ 2 (fun Z : ExitTailState => Z 1) Y := by fun_prop
  have H2 : ContDiffAt ℝ 2 (fun Z : ExitTailState => Z 2) Y := by fun_prop
  have HG := ((H0.pow 2).sub contDiffAt_const).sqrt (sub_pos.mpr hg).ne'
  have HH : ContDiffAt ℝ 2 (fun Z : ExitTailState => exitSingleBase (Z 0) v) Y :=
    ((contDiffAt_const.sub HG).pow 2).add contDiffAt_const
  have HT : ContDiffAt ℝ 2 (fun Z : ExitTailState => exitSingleDefect (Z 1) v (Z 2)) Y := by
    unfold exitSingleDefect
    fun_prop
  have HE : ContDiffAt ℝ 2 (fun Z : ExitTailState => exitSingleError (Z 0) (Z 1) v (Z 2)) Y :=
    HT.mul (contDiffAt_const.add ((((H0.pow 2).sub contDiffAt_const).add HT).div HH hH))
  refine ⟨((((H0.pow 2).add HE).sqrt hS.ne').sub contDiffAt_const).div_const 2, ?_⟩
  have D0 := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) Y
  have D1 := hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 3) Y
  have D2 := hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 3) Y
  have DG := (((D0.pow 2).sub_const (v ^ 2)).sqrt (sub_pos.mpr hg).ne')
  have DH := (((hasFDerivAt_const (2 : ℝ) Y).sub DG).pow 2).add_const (v ^ 2)
  have DT := ((D1.sub D2).pow 2).sub ((D1.add D2).const_mul (2 * v))
  have DN := ((D0.pow 2).sub_const 4).add DT
  have DI := (hasDerivAt_inv hH).comp_hasFDerivAt Y DH
  have DE := DT.mul ((DN.mul DI).const_add 1)
  have DS := ((D0.pow 2).add DE).sqrt hS.ne'
  have DX := (DS.sub_const 2).mul_const ((2 : ℝ)⁻¹)
  change HasFDerivAt (fun Z : ExitTailState => exitSinglePhase (Z 0) (Z 1) v (Z 2)) _ Y at DX
  intro d
  rw [DX.fderiv]
  simp only [smul_apply, sub_apply, add_apply, zero_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  dsimp [exitSingleErrorRadial, exitSingleErrorWallFactor, exitSingleBaseRadial,
    exitSingleBase, exitSingleDefect, exitSingleError, exitTailGap]
  ring_nf

end BianchiIX
