import BianchiIX.Dynamics.ConnectionRadialResponse
import BianchiIX.Analysis.NarrowCone

noncomputable section

namespace BianchiIX

theorem connectionReturn_unit_wall_bounds {p v : ConnectionParameters} {ε : ℝ}
    (hμ : 4 ≤ p 0) (hε : 0 < ε ∧ ε ≤ 1 / 10000)
    (hsε : Real.sqrt ε ≤ 1 / 1000000) (hεL : ε ≤ Real.exp (-256))
    (hu : 0 < p 1 ∧ p 1 ≤ ε / p 0) (hw : 0 < p 2 ∧ p 2 ≤ ε)
    (hv : ((p 0 + 1) / phaseNorm (p 0 + 1) 1) * v 0 = 1)
    (hvu : |v 1| ≤ Real.sqrt (p 1)) (hvw : |v 2| ≤ Real.sqrt (p 2)) :
    let d := fderiv ℝ connectionReturnPhysicalState p v
    |d 1| ≤ 2 * Real.sqrt (connectionReturnState p 1) ∧
      |d 2| ≤ 2 * Real.sqrt (connectionReturnState p 2) := by
  intro d
  have H := connectionReturn_unit_cone hμ hε hsε hεL hu hw hv hvu hvw
  have hμ0 : 0 < p 0 := by linarith only [hμ]
  have he : 1 / (4 * p 0) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith only [hμ])
  have hdlo : 0 ≤ d 0 := by linarith only [H.1]
  have hdhi : d 0 ≤ 2 := by linarith only [(abs_le.mp H.2.1).2, he]
  have hL : 0 ≤ -Real.log (p 2) :=
    neg_nonneg.mpr (Real.log_nonpos hw.1.le (by linarith only [hw.2, hε.2]))
  have hγ : 0 ≤ 1 - Real.exp (-(-Real.log (p 2)) / (2 * p 0)) := by
    apply sub_nonneg.mpr
    exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hL) (by positivity))
  constructor
  · calc
      |d 1| ≤ (1 / 3) * Real.sqrt (connectionReturnState p 1) * d 0 := H.2.2.1
      _ ≤ (1 / 3) * Real.sqrt (connectionReturnState p 1) * 2 := mul_le_mul_of_nonneg_left hdhi (by positivity)
      _ ≤ _ := by nlinarith only [Real.sqrt_nonneg (connectionReturnState p 1)]
  · have Hfac := mul_le_mul_of_nonneg_right
      (show 1 - (1 - Real.exp (-(-Real.log (p 2)) / (2 * p 0))) / 2 ≤ 1 by linarith only [hγ])
      (mul_nonneg (Real.sqrt_nonneg (connectionReturnState p 2)) hdlo)
    calc
      |d 2| ≤ (1 - (1 - Real.exp (-(-Real.log (p 2)) / (2 * p 0))) / 2) *
          Real.sqrt (connectionReturnState p 2) * d 0 := H.2.2.2
      _ ≤ Real.sqrt (connectionReturnState p 2) * d 0 := by nlinarith only [Hfac]
      _ ≤ Real.sqrt (connectionReturnState p 2) * 2 := mul_le_mul_of_nonneg_left hdhi (Real.sqrt_nonneg _)
      _ = _ := by ring

/-- B.32 for the actual first-return derivative, including zero input slope. -/
theorem connectionReturn_refined_cone {p v : ConnectionParameters} {ε θ : ℝ}
    (hμ : 4 ≤ p 0) (hε : 0 < ε ∧ ε ≤ 1 / 10000)
    (hsε : Real.sqrt ε ≤ 1 / 1000000) (hεL : ε ≤ Real.exp (-256))
    (hu : 0 < p 1 ∧ p 1 ≤ ε / p 0) (hw : 0 < p 2 ∧ p 2 ≤ ε)
    (hθ : 0 ≤ θ ∧ θ ≤ 1)
    (hv : ((p 0 + 1) / phaseNorm (p 0 + 1) 1) * v 0 = 1)
    (hvu : |v 1| ≤ θ * Real.sqrt (p 1)) (hvw : |v 2| ≤ θ * Real.sqrt (p 2)) :
    let L := -Real.log (p 2)
    let d := fderiv ℝ connectionReturnPhysicalState p v
    3 / 4 ≤ d 0 ∧
      max (|d 1| / (Real.sqrt (connectionReturnState p 1) * d 0))
        (|d 2| / (Real.sqrt (connectionReturnState p 2) * d 0)) ≤
          30000 * (θ + (Real.sqrt (p 1) + (1 + L) * Real.sqrt (p 2)) / p 0 ^ 2) := by
  intro L d
  have hμ0 : 0 < p 0 := by linarith only [hμ]
  have hu' : 0 < p 1 ∧ p 1 ≤ (1 / 10000) / p 0 :=
    ⟨hu.1, hu.2.trans (div_le_div_of_nonneg_right hε.2 hμ0.le)⟩
  have hw' : 0 < p 2 ∧ p 2 ≤ 1 / 10000 := ⟨hw.1, hw.2.trans hε.2⟩
  have hL : 1 ≤ L := by
    have Hl := Real.log_le_log hw.1 (hw.2.trans hεL)
    rw [Real.log_exp] at Hl
    linarith only [Hl]
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hvu' : |v 1| ≤ Real.sqrt (p 1) := hvu.trans (mul_le_of_le_one_left (Real.sqrt_nonneg _) hθ.2)
  have hvw' : |v 2| ≤ Real.sqrt (p 2) := hvw.trans (mul_le_of_le_one_left (Real.sqrt_nonneg _) hθ.2)
  have Hd := (connectionReturn_unit_cone hμ hε hsε hεL hu hw hv hvu' hvw').1
  have hd0 : 0 < d 0 := by linarith only [Hd]
  let S := (Real.sqrt (p 1) + (1 + L) * Real.sqrt (p 2)) / p 0 ^ 2
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  let r : ConnectionParameters := ![v 0, 0, 0]
  have hr : ((p 0 + 1) / phaseNorm (p 0 + 1) 1) * r 0 = 1 := hv
  have Hr := connectionReturn_radial_wall_bounds hμ hu' hw' hL hr (by rfl) (by rfl)
  have Hrad (i : Fin 2) : |fderiv ℝ connectionReturnPhysicalState p r i.succ| ≤
      (20000 * S) * Real.sqrt (connectionReturnState p i.succ.castSucc) := by
    fin_cases i
    · have Hc : 17536 * Real.sqrt (p 1) / p 0 ^ 2 ≤ 20000 * S := by
        have Hn : 17536 * Real.sqrt (p 1) ≤ 20000 * (Real.sqrt (p 1) + (1 + L) * Real.sqrt (p 2)) := by
          nlinarith only [Real.sqrt_nonneg (p 1), Real.sqrt_nonneg (p 2), mul_nonneg hL0 (Real.sqrt_nonneg (p 2))]
        exact (div_le_div_of_nonneg_right Hn (sq_nonneg (p 0))).trans_eq (by dsimp only [S]; ring)
      exact Hr.1.trans (mul_le_mul_of_nonneg_right Hc (Real.sqrt_nonneg _))
    · have Hc : 274 * L * Real.sqrt (p 2) / p 0 ^ 2 ≤ 20000 * S := by
        have Hn : 274 * L * Real.sqrt (p 2) ≤ 20000 * (Real.sqrt (p 1) + (1 + L) * Real.sqrt (p 2)) := by
          nlinarith only [Real.sqrt_nonneg (p 1), Real.sqrt_nonneg (p 2), mul_nonneg hL0 (Real.sqrt_nonneg (p 2))]
        exact (div_le_div_of_nonneg_right Hn (sq_nonneg (p 0))).trans_eq (by dsimp only [S]; ring)
      exact Hr.2.trans (mul_le_mul_of_nonneg_right Hc (Real.sqrt_nonneg _))
  have Hraw (i : Fin 2) : |d i.succ| ≤ (2 * θ + 20000 * S) *
      Real.sqrt (connectionReturnState p i.succ.castSucc) := by
    let A := (ContinuousLinearMap.proj i.succ : ConnectionParameters →L[ℝ] ℝ).comp
      (fderiv ℝ connectionReturnPhysicalState p)
    have H := linear_narrow_cone_bound A r v (by rfl) (by rfl) (by rfl) hθ hvu hvw
      (C := 2 * Real.sqrt (connectionReturnState p i.succ.castSucc)) (E := (20000 * S) * Real.sqrt (connectionReturnState p i.succ.castSucc)) (by
        intro z hz hzu hzw
        have hzphase : ((p 0 + 1) / phaseNorm (p 0 + 1) 1) * z 0 = 1 := by rw [hz]; exact hr
        have Hz := connectionReturn_unit_wall_bounds hμ hε hsε hεL hu hw hzphase hzu hzw
        fin_cases i
        · exact Hz.1
        · exact Hz.2) (Hrad i)
    exact H.trans_eq (by ring)
  have HC : 2 * θ + 20000 * S ≤ (30000 * (θ + S)) * d 0 := by
    have H := mul_le_mul_of_nonneg_left Hd (mul_nonneg (by norm_num : (0 : ℝ) ≤ 30000) (add_nonneg hθ.1 hS))
    nlinarith only [H, hθ.1, hS]
  have Hpos := connectionReturn_wall_pos hμ ⟨hu'.1.le, hu'.2⟩ hw'
  change 3 / 4 ≤ d 0 ∧ max (|d 1| / (Real.sqrt (connectionReturnState p 1) * d 0))
    (|d 2| / (Real.sqrt (connectionReturnState p 2) * d 0)) ≤ 30000 * (θ + S)
  refine ⟨Hd, max_le ?_ ?_⟩
  · apply (div_le_iff₀ (mul_pos (Real.sqrt_pos.mpr (Hpos.2 hu.1)) hd0)).mpr
    have H1 : |d 1| ≤ (2 * θ + 20000 * S) * Real.sqrt (connectionReturnState p 1) := Hraw 0
    exact (H1.trans (mul_le_mul_of_nonneg_right HC (Real.sqrt_nonneg _))).trans_eq (by ring)
  · apply (div_le_iff₀ (mul_pos (Real.sqrt_pos.mpr Hpos.1) hd0)).mpr
    have H2 : |d 2| ≤ (2 * θ + 20000 * S) * Real.sqrt (connectionReturnState p 2) := Hraw 1
    exact (H2.trans (mul_le_mul_of_nonneg_right HC (Real.sqrt_nonneg _))).trans_eq (by ring)

theorem exists_connectionReturn_refined_cone :
    ∃ ε > 0, ε ≤ 1 / 10000 ∧ ∀ (p : ConnectionParameters),
      4 ≤ p 0 → (0 < p 1 ∧ p 1 ≤ ε / p 0) → (0 < p 2 ∧ p 2 ≤ ε) →
      ∀ (θ : ℝ), (0 ≤ θ ∧ θ ≤ 1) → ∀ (v : ConnectionParameters),
        ((p 0 + 1) / phaseNorm (p 0 + 1) 1) * v 0 = 1 →
        |v 1| ≤ θ * Real.sqrt (p 1) → |v 2| ≤ θ * Real.sqrt (p 2) →
        let L := -Real.log (p 2)
        let d := fderiv ℝ connectionReturnPhysicalState p v
        3 / 4 ≤ d 0 ∧
          max (|d 1| / (Real.sqrt (connectionReturnState p 1) * d 0))
            (|d 2| / (Real.sqrt (connectionReturnState p 2) * d 0)) ≤
              30000 * (θ + (Real.sqrt (p 1) + (1 + L) * Real.sqrt (p 2)) / p 0 ^ 2) := by
  obtain ⟨ε, hε0, hε, hsε, hεL⟩ := exists_connection_cone_threshold
  exact ⟨ε, hε0, hε, fun p hμ hu hw θ hθ v hv hvu hvw =>
    connectionReturn_refined_cone hμ ⟨hε0, hε⟩ hsε hεL hu hw hθ hv hvu hvw⟩

end BianchiIX
