import BianchiIX.Dynamics.ConnectionConeDirections
import BianchiIX.Dynamics.ConnectionReturnContraction
import BianchiIX.Algebra.ConnectionConeMargin
import BianchiIX.Analysis.HomogeneousCone

noncomputable section

namespace BianchiIX

/-- The actual positive-wall connection preserves unit physical-phase cone directions,
with a uniform strong margin and the nonuniform weak margin of B.31. -/
theorem connectionReturn_unit_cone {p v : ConnectionParameters} {ε : ℝ}
    (hμ : 4 ≤ p 0) (hε : 0 < ε ∧ ε ≤ 1 / 10000)
    (hsε : Real.sqrt ε ≤ 1 / 1000000) (hεL : ε ≤ Real.exp (-256))
    (hu : 0 < p 1 ∧ p 1 ≤ ε / p 0) (hw : 0 < p 2 ∧ p 2 ≤ ε)
    (hv : ((p 0 + 1) / phaseNorm (p 0 + 1) 1) * v 0 = 1)
    (hvu : |v 1| ≤ Real.sqrt (p 1)) (hvw : |v 2| ≤ Real.sqrt (p 2)) :
    let L := -Real.log (p 2)
    let d := fderiv ℝ connectionReturnPhysicalState p v
    3 / 4 ≤ d 0 ∧ |d 0 - 1| ≤ 1 / (4 * p 0) ∧
      |d 1| ≤ (1 / 3) * Real.sqrt (connectionReturnState p 1) * d 0 ∧
      |d 2| ≤ (1 - (1 - Real.exp (-L / (2 * p 0))) / 2) *
        Real.sqrt (connectionReturnState p 2) * d 0 := by
  intro L d
  have hμ0 : 0 < p 0 := by linarith only [hμ]
  have hu' : 0 < p 1 ∧ p 1 ≤ (1 / 10000) / p 0 :=
    ⟨hu.1, hu.2.trans (div_le_div_of_nonneg_right hε.2 hμ0.le)⟩
  have hw' : 0 < p 2 ∧ p 2 ≤ 1 / 10000 := ⟨hw.1, hw.2.trans hε.2⟩
  have hL : 256 ≤ L := by
    have H := Real.log_le_log hw.1 (hw.2.trans hεL)
    rw [Real.log_exp] at H
    linarith only [H]
  have hwexp : p 2 = Real.exp (-L) := by simp only [L, neg_neg, Real.exp_log hw.1]
  have H := connectionReturn_cone_direction_bounds hμ ⟨hε.1.le, hε.2⟩ hu hw hv hvu hvw
  have Hd := connectionReturnPhysicalState_differential hμ hu' hw' v
  have Hdec := connectionReturn_exponential_decay hμ hu' hw'
  have Hpos := connectionReturn_wall_pos hμ ⟨hu'.1.le, hu'.2⟩ hw'
  have hphase : |d 0 - 1| ≤ 1 / (4 * p 0) := by
    have heq : d 0 - 1 = fderiv ℝ connectionReturnPhaseError p v := by
      dsimp only [d]
      rw [Hd.1, hv]
      ring
    rw [heq]
    calc
      _ ≤ 200000 * Real.sqrt ε / p 0 := H.1
      _ ≤ (1 / 4) / p 0 := div_le_div_of_nonneg_right (by linarith only [hsε]) hμ0.le
      _ = _ := by ring
  have Hmargin := connection_cone_phase_margin hμ (by linarith only [hL] : 4 ≤ L) hphase
  have hU : Real.sqrt (connectionReturnState p 1) ≤ Real.sqrt (p 1) * Real.exp (-p 0 * L / 4) := by
    have Hb := sqrt_le_sqrt_mul_exp_half hu.1.le Hdec.1
    have heq : (-p 0 * (-Real.log (p 2)) / 2) / 2 = -p 0 * L / 4 := by dsimp only [L]; ring
    rwa [heq] at Hb
  have hV : Real.sqrt (connectionReturnState p 2) ≤ Real.sqrt (p 2) * Real.exp (-L / p 0) := by
    have Hb := sqrt_le_sqrt_mul_exp_half hw.1.le Hdec.2
    have heq : (-2 * (-Real.log (p 2)) / p 0) / 2 = -L / p 0 := by dsimp only [L]; ring
    rwa [heq] at Hb
  let J := fderiv ℝ (connectionLogCoordinates ∘ connectionReturnState) p
  have hstrong : Real.sqrt (connectionReturnState p 1) * |J v 1| ≤ 1 / 4 := by
    have Hs := connection_strong_cone_size hμ ⟨hε.1.le, by linarith only [hε.2]⟩ hu hw (by linarith only [hL]) hwexp
    have Hb := mul_le_mul hU H.2.1 (abs_nonneg _) (by positivity)
    exact (Hb.trans Hs).trans (by linarith only [hsε])
  have hweak : Real.sqrt (connectionReturnState p 2) * |J v 2| ≤ Real.exp (-L / (2 * p 0)) := by
    have hue : p 1 ≤ ε := hu.2.trans (div_le_self hε.1.le (by linarith only [hμ]))
    have hs : 40000 * Real.sqrt (p 2) ≤ 1 := by
      have Hw := (Real.sqrt_le_sqrt hw.2).trans hsε
      linarith only [Hw]
    have Hs := connection_weak_cone_size hμ ⟨hu.1.le, by linarith only [hue, hε.2]⟩ hw.1 hL hs
    exact (mul_le_mul hV H.2.2 (abs_nonneg _) (by positivity)).trans Hs
  refine ⟨Hmargin.1, hphase, ?_, ?_⟩
  · calc
      |d 1| = Real.sqrt (connectionReturnState p 1) *
          (Real.sqrt (connectionReturnState p 1) * |J v 1|) := by
        dsimp only [d]
        rw [Hd.2.1, abs_mul, abs_of_pos (Hpos.2 hu'.1), ← mul_assoc,
          Real.mul_self_sqrt (Hpos.2 hu'.1).le]
      _ ≤ Real.sqrt (connectionReturnState p 1) * ((1 / 3) * d 0) :=
        mul_le_mul_of_nonneg_left (hstrong.trans Hmargin.2.1) (Real.sqrt_nonneg _)
      _ = _ := by ring
  · calc
      |d 2| = Real.sqrt (connectionReturnState p 2) *
          (Real.sqrt (connectionReturnState p 2) * |J v 2|) := by
        dsimp only [d]
        rw [Hd.2.2, abs_mul, abs_of_pos Hpos.1, ← mul_assoc, Real.mul_self_sqrt Hpos.1.le]
      _ ≤ Real.sqrt (connectionReturnState p 2) *
          ((1 - (1 - Real.exp (-L / (2 * p 0))) / 2) * d 0) :=
        mul_le_mul_of_nonneg_left (hweak.trans Hmargin.2.2) (Real.sqrt_nonneg _)
      _ = _ := by ring

/-- The B.28 cone and both B.31 margins for every tangent vector of the actual connection.
No upper bound on the radial parameter, waiting length, or wall ratio is imposed. -/
theorem exists_connectionReturn_cone :
    ∃ ε > 0, ε ≤ 1 / 10000 ∧ ∀ (p : ConnectionParameters),
      4 ≤ p 0 → (0 < p 1 ∧ p 1 ≤ ε / p 0) → (0 < p 2 ∧ p 2 ≤ ε) →
      ContDiffAt ℝ 2 connectionReturnPhysicalState p ∧
      ∀ (v : ConnectionParameters),
        |v 1| ≤ Real.sqrt (p 1) * |((p 0 + 1) / phaseNorm (p 0 + 1) 1) * v 0| →
        |v 2| ≤ Real.sqrt (p 2) * |((p 0 + 1) / phaseNorm (p 0 + 1) 1) * v 0| →
        let d := fderiv ℝ connectionReturnPhysicalState p v
        let γ := 1 - Real.exp (-(-Real.log (p 2)) / (2 * p 0))
        (|d 1| ≤ (1 / 3) * Real.sqrt (connectionReturnState p 1) * |d 0| ∧
          |d 2| ≤ (1 - γ / 2) * Real.sqrt (connectionReturnState p 2) * |d 0|) ∧
        (|d 1| ≤ Real.sqrt (connectionReturnState p 1) * |d 0| ∧
          |d 2| ≤ Real.sqrt (connectionReturnState p 2) * |d 0|) := by
  obtain ⟨ε, hε0, hε, hsε, hεL⟩ := exists_connection_cone_threshold
  refine ⟨ε, hε0, hε, ?_⟩
  intro p hμ hu hw
  have hμ0 : 0 < p 0 := by linarith only [hμ]
  have hu' : 0 ≤ p 1 ∧ p 1 ≤ (1 / 10000) / p 0 :=
    ⟨hu.1.le, hu.2.trans (div_le_div_of_nonneg_right hε hμ0.le)⟩
  have hw' : 0 < p 2 ∧ p 2 ≤ 1 / 10000 := ⟨hw.1, hw.2.trans hε⟩
  refine ⟨contDiffAt_connectionReturnPhysicalState hμ hu' hw', ?_⟩
  intro v hvu hvw d γ
  have hR := (phaseNorm_ratio_bounds (b := 1) (by linarith only [hμ] : 2 ≤ p 0 + 1) (by norm_num)).1
  have H := homogeneous_cone_of_unit (fderiv ℝ connectionReturnPhysicalState p)
    (show 0 < (p 0 + 1) / phaseNorm (p 0 + 1) 1 by linarith only [hR])
    (a := Real.sqrt (p 1)) (b := Real.sqrt (p 2))
    (A := (1 / 3) * Real.sqrt (connectionReturnState p 1))
    (B := (1 - γ / 2) * Real.sqrt (connectionReturnState p 2)) (by
      intro z hz hzu hzw
      have Hz := connectionReturn_unit_cone hμ ⟨hε0, hε⟩ hsε hεL hu hw hz hzu hzw
      exact ⟨by linarith only [Hz.1], Hz.2.2.1, Hz.2.2.2⟩) v hvu hvw
  refine ⟨H, ?_, ?_⟩
  · exact H.1.trans (by nlinarith only [mul_nonneg (Real.sqrt_nonneg (connectionReturnState p 1)) (abs_nonneg (d 0))])
  · have hL : 4 ≤ -Real.log (p 2) := by
      have Hl := Real.log_le_log hw.1 (hw.2.trans hεL)
      rw [Real.log_exp] at Hl
      linarith only [Hl]
    have hg := (connection_cone_gap hμ hL).1
    have hg0 : 0 ≤ γ := (by positivity : (0 : ℝ) ≤ 1 / p 0).trans hg
    have Hb := mul_le_mul_of_nonneg_right (show 1 - γ / 2 ≤ 1 by linarith only [hg0])
      (mul_nonneg (Real.sqrt_nonneg (connectionReturnState p 2)) (abs_nonneg (d 0)))
    exact H.2.trans (by nlinarith only [Hb])

end BianchiIX
