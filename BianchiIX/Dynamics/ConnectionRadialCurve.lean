import BianchiIX.Dynamics.CoreConnectionDifferential
import BianchiIX.Dynamics.ConnectionReturnCone
import BianchiIX.Analysis.HomogeneousPhase
import BianchiIX.Analysis.ReciprocalCurve

noncomputable section

namespace BianchiIX

/-- The connection preserves the actual curve cone and the sign of its radial slope. -/
theorem connectionReturn_coreExit_curve {f u w : ℝ → ℝ} {x ε : ℝ}
    (hf : DifferentiableAt ℝ f x) (hu : DifferentiableAt ℝ u x)
    (hw : DifferentiableAt ℝ w x) (hf1 : 1 < f x) (hdf : deriv f x < 0)
    (hε : 0 < ε ∧ ε ≤ 1 / 10000) (hsε : Real.sqrt ε ≤ 1 / 1000000)
    (hεL : ε ≤ Real.exp (-256))
    (hμ : 4 ≤ coreExitConnectionParameters ![f x, u x, w x] 0)
    (hu0 : 0 < u x ∧ u x ≤ ε / coreExitConnectionParameters ![f x, u x, w x] 0)
    (hw0 : 0 < w x ∧ w x ≤ ε)
    (hdu : |deriv u x| ≤ Real.sqrt (u x) * |deriv f x|)
    (hdw : |deriv w x| ≤ Real.sqrt (w x) * |deriv f x|) :
    let p := fun a => coreExitConnectionParameters ![f a, u a, w a]
    let G := fun a => connectionReturnPhysicalState (p a)
    DifferentiableAt ℝ G x ∧
      deriv (fun a => G a 0) x < 0 ∧
      |deriv (fun a => G a 0) x / deriv f x - 1| ≤ 1 / (4 * p x 0) ∧
      (3 / 4 ≤ deriv (fun a => G a 0) x / deriv f x ∧
        deriv (fun a => G a 0) x / deriv f x ≤ 5 / 4) ∧
      |deriv (fun a => G a 1) x| ≤ Real.sqrt (G x 1) * |deriv (fun a => G a 0) x| ∧
      |deriv (fun a => G a 2) x| ≤ Real.sqrt (G x 2) * |deriv (fun a => G a 0) x| := by
  intro p G
  let Z := fun a => ![f a, u a, w a]
  let v : CoreAngleState := ![deriv f x, deriv u x, deriv w x]
  have hZ : HasDerivAt Z v x := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact hf.hasDerivAt
    · exact hu.hasDerivAt
    · exact hw.hasDerivAt
  have hc := (contDiffAt_coreExitConnectionParameters (Z := Z x) 1 hf1).differentiableAt (by norm_num)
  let ξ := fderiv ℝ coreExitConnectionParameters (Z x) v
  have hp : HasDerivAt p ξ x := hc.hasFDerivAt.comp_hasDerivAt x hZ
  have Hc := coreExitConnectionParameters_differential (Z := Z x) hf1 v
  change ((p x 0 + 1) / phaseNorm (p x 0 + 1) 1) * ξ 0 = deriv f x ∧
    ξ 1 = deriv u x ∧ ξ 2 = deriv w x at Hc
  have hμ0 : 0 < p x 0 := by linarith only [hμ]
  have hu' : 0 ≤ p x 1 ∧ p x 1 ≤ (1 / 10000) / p x 0 :=
    ⟨hu0.1.le, hu0.2.trans (div_le_div_of_nonneg_right hε.2 hμ0.le)⟩
  have hw' : 0 < p x 2 ∧ p x 2 ≤ 1 / 10000 := ⟨hw0.1, hw0.2.trans hε.2⟩
  have hG := (contDiffAt_connectionReturnPhysicalState hμ hu' hw').differentiableAt (by norm_num)
  let D := fderiv ℝ connectionReturnPhysicalState (p x)
  have HD : HasDerivAt G (D ξ) x := hG.hasFDerivAt.comp_hasDerivAt (f := p) x hp
  have hd (i : Fin 3) : deriv (fun a => G a i) x = D ξ i := (hasDerivAt_pi.mp HD i).deriv
  have hξu : |ξ 1| ≤ Real.sqrt (p x 1) * |((p x 0 + 1) / phaseNorm (p x 0 + 1) 1) * ξ 0| := by
    rw [Hc.1, Hc.2.1]
    exact hdu
  have hξw : |ξ 2| ≤ Real.sqrt (p x 2) * |((p x 0 + 1) / phaseNorm (p x 0 + 1) 1) * ξ 0| := by
    rw [Hc.1, Hc.2.2]
    exact hdw
  have Hunit (z : ConnectionParameters)
      (hz : ((p x 0 + 1) / phaseNorm (p x 0 + 1) 1) * z 0 = 1)
      (hzu : |z 1| ≤ Real.sqrt (p x 1)) (hzw : |z 2| ≤ Real.sqrt (p x 2)) :=
    connectionReturn_unit_cone hμ hε hsε hεL hu0 hw0 hz hzu hzw
  have Hphase := homogeneous_phase_ratio_of_unit D (fun z hz hzu hzw =>
    (Hunit z hz hzu hzw).2.1) ξ (by rw [Hc.1]; exact ne_of_lt hdf) hξu hξw
  rw [Hc.1] at Hphase
  have hR := (phaseNorm_ratio_bounds (b := 1) (by linarith only [hμ] : 2 ≤ p x 0 + 1) (by norm_num)).1
  have Hcone := homogeneous_cone_of_unit D
    (show 0 < (p x 0 + 1) / phaseNorm (p x 0 + 1) 1 by linarith only [hR])
    (a := Real.sqrt (p x 1)) (b := Real.sqrt (p x 2))
    (A := Real.sqrt (G x 1)) (B := Real.sqrt (G x 2)) (by
      intro z hz hzu hzw
      have Hz := Hunit z hz hzu hzw
      have hd0 : 0 ≤ D z 0 := by linarith only [Hz.1]
      refine ⟨hd0, Hz.2.2.1.trans ?_, Hz.2.2.2.trans ?_⟩
      · change (1 / 3) * Real.sqrt (G x 1) * D z 0 ≤ Real.sqrt (G x 1) * D z 0
        nlinarith only [mul_nonneg (Real.sqrt_nonneg (G x 1)) hd0]
      · have hL : 4 ≤ -Real.log (p x 2) := by
          change 4 ≤ -Real.log (w x)
          have Hl := Real.log_le_log hw0.1 (hw0.2.trans hεL)
          rw [Real.log_exp] at Hl
          linarith only [Hl]
        have hgap := (connection_cone_gap hμ hL).1
        have hgap0 : 0 ≤ 1 - Real.exp (-(-Real.log (p x 2)) / (2 * p x 0)) :=
          (by positivity : (0 : ℝ) ≤ 1 / p x 0).trans hgap
        have Hb := mul_le_mul_of_nonneg_right (show
          1 - (1 - Real.exp (-(-Real.log (p x 2)) / (2 * p x 0))) / 2 ≤ 1 by linarith)
          (mul_nonneg (Real.sqrt_nonneg (G x 2)) hd0)
        change (1 - (1 - Real.exp (-(-Real.log (p x 2)) / (2 * p x 0))) / 2) *
          Real.sqrt (G x 2) * D z 0 ≤ Real.sqrt (G x 2) * D z 0
        nlinarith only [Hb]) ξ hξu hξw
  have hsmall : 1 / (4 * p x 0) ≤ 1 / 4 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    linarith only [hμ]
  have Hbounds : 3 / 4 ≤ D ξ 0 / deriv f x ∧ D ξ 0 / deriv f x ≤ 5 / 4 := by
    have Hb := abs_le.mp (Hphase.trans hsmall)
    constructor <;> linarith only [Hb.1, Hb.2]
  have Hneg : D ξ 0 < 0 := by
    have Hpos : 0 < D ξ 0 / deriv f x := lt_of_lt_of_le (by norm_num) Hbounds.1
    exact (div_pos_iff.mp Hpos).resolve_left (fun h => (not_lt_of_ge hdf.le) h.2) |>.1
  refine ⟨HD.differentiableAt, ?_, ?_, ?_, ?_, ?_⟩
  · rwa [hd]
  · rwa [hd]
  · simpa only [hd] using Hbounds
  · simpa only [hd] using Hcone.1
  · simpa only [hd] using Hcone.2

end BianchiIX
