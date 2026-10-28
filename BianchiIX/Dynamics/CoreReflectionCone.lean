import BianchiIX.Dynamics.CoreConnectionDifferential
import BianchiIX.Dynamics.ConnectionReturnCone

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The coordinate change and actual connection transport a positive core cone direction. -/
theorem coreReflection_cone_transport {Y v : CoreAngleState} {τ : CoreAngleState → ℝ} {ε : ℝ}
    (hK : 1 < coreReturnState τ Y 0)
    (hcore : DifferentiableAt ℝ (coreReturnState τ) Y)
    (hε : 0 < ε ∧ ε ≤ 1 / 10000) (hsε : Real.sqrt ε ≤ 1 / 1000000)
    (hεL : ε ≤ Real.exp (-256))
    (hμ : 4 ≤ coreConnectionParameters τ Y 0)
    (hu : 0 < coreConnectionParameters τ Y 1 ∧
      coreConnectionParameters τ Y 1 ≤ ε / coreConnectionParameters τ Y 0)
    (hw : 0 < coreConnectionParameters τ Y 2 ∧ coreConnectionParameters τ Y 2 ≤ ε)
    (hr : 0 < fderiv ℝ (coreReturnState τ) Y v 0)
    (hvu : |fderiv ℝ (coreReturnState τ) Y v 1| ≤
      Real.sqrt (coreReturnState τ Y 1) * fderiv ℝ (coreReturnState τ) Y v 0)
    (hvw : |fderiv ℝ (coreReturnState τ) Y v 2| ≤
      Real.sqrt (coreReturnState τ Y 2) * fderiv ℝ (coreReturnState τ) Y v 0) :
    let d := fderiv ℝ (coreReflectionState τ) Y v
    (3 / 4) * fderiv ℝ (coreReturnState τ) Y v 0 ≤ d 0 ∧
      |d 1| ≤ Real.sqrt (coreReflectionState τ Y 1) * d 0 ∧
      |d 2| ≤ Real.sqrt (coreReflectionState τ Y 2) * d 0 := by
  intro d
  let p := coreConnectionParameters τ Y
  let ξ := fderiv ℝ (coreReturnState τ) Y v
  let w := fderiv ℝ (coreConnectionParameters τ) Y v
  let z := (ξ 0)⁻¹ • w
  have hμ0 : 0 < p 0 := by linarith only [hμ]
  have hp : DifferentiableAt ℝ (coreConnectionParameters τ) Y :=
    ((contDiffAt_coreExitConnectionParameters 1 hK).differentiableAt (by norm_num)).comp Y hcore
  have hconn := (contDiffAt_connectionReturnPhysicalState hμ
    ⟨hu.1.le, hu.2.trans (div_le_div_of_nonneg_right hε.2 hμ0.le)⟩
    ⟨hw.1, hw.2.trans hε.2⟩).differentiableAt (by norm_num)
  have Hcoord := coreConnectionParameters_differential hK hcore v
  change ((p 0 + 1) / phaseNorm (p 0 + 1) 1) * w 0 = ξ 0 ∧
    w 1 = ξ 1 ∧ w 2 = ξ 2 at Hcoord
  have hξ : 0 < ξ 0 := hr
  have hz : ((p 0 + 1) / phaseNorm (p 0 + 1) 1) * z 0 = 1 := by
    change _ * ((ξ 0)⁻¹ * w 0) = 1
    calc
      _ = (ξ 0)⁻¹ * (((p 0 + 1) / phaseNorm (p 0 + 1) 1) * w 0) := by ring
      _ = 1 := by rw [Hcoord.1, inv_mul_cancel₀ hξ.ne']
  have hzu : |z 1| ≤ Real.sqrt (p 1) := by
    change |(ξ 0)⁻¹ * w 1| ≤ _
    rw [abs_mul, abs_of_pos (inv_pos.mpr hξ), Hcoord.2.1]
    calc
      _ ≤ (ξ 0)⁻¹ * (Real.sqrt (p 1) * ξ 0) :=
        mul_le_mul_of_nonneg_left hvu (inv_nonneg.mpr hξ.le)
      _ = _ := by field_simp
  have hzw : |z 2| ≤ Real.sqrt (p 2) := by
    change |(ξ 0)⁻¹ * w 2| ≤ _
    rw [abs_mul, abs_of_pos (inv_pos.mpr hξ), Hcoord.2.2]
    calc
      _ ≤ (ξ 0)⁻¹ * (Real.sqrt (p 2) * ξ 0) :=
        mul_le_mul_of_nonneg_left hvw (inv_nonneg.mpr hξ.le)
      _ = _ := by field_simp
  have H := connectionReturn_unit_cone hμ hε hsε hεL hu hw hz hzu hzw
  let e := fderiv ℝ connectionReturnPhysicalState p z
  have he0 : 0 ≤ e 0 := by linarith only [H.1]
  have hucone : |e 1| ≤ Real.sqrt (coreReflectionState τ Y 1) * e 0 := by
    change |e 1| ≤ Real.sqrt (connectionReturnState p 1) * e 0
    exact H.2.2.1.trans (by
      change (1 / 3) * Real.sqrt (connectionReturnState p 1) * e 0 ≤ _
      nlinarith only [mul_nonneg (Real.sqrt_nonneg (connectionReturnState p 1)) he0])
  have hL : 4 ≤ -Real.log (p 2) := by
    have Hl := Real.log_le_log hw.1 (hw.2.trans hεL)
    rw [Real.log_exp] at Hl
    linarith only [Hl]
  have hg : 0 ≤ 1 - Real.exp (-(-Real.log (p 2)) / (2 * p 0)) :=
    (by positivity : (0 : ℝ) ≤ 1 / p 0).trans (connection_cone_gap hμ hL).1
  have hwcone : |e 2| ≤ Real.sqrt (coreReflectionState τ Y 2) * e 0 := by
    change |e 2| ≤ Real.sqrt (connectionReturnState p 2) * e 0
    have Hb := mul_le_mul_of_nonneg_right
      (show 1 - (1 - Real.exp (-(-Real.log (p 2)) / (2 * p 0))) / 2 ≤ 1 by linarith only [hg])
      (mul_nonneg (Real.sqrt_nonneg (connectionReturnState p 2)) he0)
    exact H.2.2.2.trans (by
      change (1 - (1 - Real.exp (-(-Real.log (p 2)) / (2 * p 0))) / 2) *
        Real.sqrt (connectionReturnState p 2) * e 0 ≤ _
      nlinarith only [Hb])
  have hwz : w = ξ 0 • z := by simp [z, smul_smul, hξ.ne']
  have hd : d = ξ 0 • e := by
    change fderiv ℝ (connectionReturnPhysicalState ∘ coreConnectionParameters τ) Y v = _
    rw [fderiv_comp Y hconn hp, ContinuousLinearMap.comp_apply]
    change fderiv ℝ connectionReturnPhysicalState p w = _
    rw [hwz, map_smul]
  rw [hd]
  change (3 / 4) * ξ 0 ≤ ξ 0 * e 0 ∧
    |ξ 0 * e 1| ≤ Real.sqrt (coreReflectionState τ Y 1) * (ξ 0 * e 0) ∧
    |ξ 0 * e 2| ≤ Real.sqrt (coreReflectionState τ Y 2) * (ξ 0 * e 0)
  rw [abs_mul, abs_mul, abs_of_pos hξ]
  exact ⟨by nlinarith only [mul_le_mul_of_nonneg_left H.1 hξ.le],
    by nlinarith only [mul_le_mul_of_nonneg_left hucone hξ.le],
    by nlinarith only [mul_le_mul_of_nonneg_left hwcone hξ.le]⟩

end BianchiIX
