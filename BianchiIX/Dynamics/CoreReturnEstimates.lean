import BianchiIX.Dynamics.CoreReturnPhaseBounds
import BianchiIX.Dynamics.CoreReturnUniformCone
import BianchiIX.Dynamics.CoreReturnUniform
import BianchiIX.Analysis.InverseLogDistortion

noncomputable section

namespace BianchiIX

/-- Phase drift, logarithmic distortion, wall contraction and cone preservation share one actual core domain. -/
theorem exists_coreRadiusReturn_estimates :
    ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧ ∃ C > (0 : ℝ), ∃ c > (0 : ℝ), c ≤ 1 / 2 ∧
      ∀ Y : CoreAngleState, 2 ≤ Y 0 →
        (0 ≤ Y 1 ∧ Y 1 ≤ ε / Y 0) → (0 ≤ Y 2 ∧ Y 2 ≤ ε / Y 0) →
        let F := coreReturnState coreRadiusReturnTime
        coreRadiusReturnValid Y ∧ ContDiffAt ℝ 1 coreRadiusReturnTime Y ∧ ContDiffAt ℝ 1 F Y ∧
          |F Y 0 - Y 0| ≤ C * (Y 1 + Y 2) / Y 0 ∧
          (∀ i : Fin 2, 0 ≤ F Y i.succ ∧ (0 < F Y i.succ ↔ 0 < Y i.succ) ∧
            F Y i.succ ≤ Real.exp (-c / Y 0) * Y i.succ) ∧
          ∀ v : CoreAngleState, v 0 = 1 → |v 1| ≤ Real.sqrt (Y 1) → |v 2| ≤ Real.sqrt (Y 2) →
            let d := fderiv ℝ F Y v
            (3 / 4 ≤ d 0 ∧ d 0 ≤ 5 / 4) ∧
              |Real.log (d 0)| ≤ C * Real.sqrt (Y 1 + Y 2) / Y 0 ∧
              ∀ i : Fin 2, |d i.succ| ≤ Real.sqrt (F Y i.succ) * d 0 := by
  obtain ⟨εp, hεp, _, C, hC, Hp⟩ := exists_coreRadiusReturn_phase_bounds
  obtain ⟨εc, hεc, _, Hc⟩ := exists_coreRadiusReturn_invariant_cone
  obtain ⟨εd, hεd, hεη, c, hc, hcmax, Hd⟩ := exists_coreRadiusReturn_uniform_contraction
  let δ := 1 / (4 * C)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hCδ : C * δ = 1 / 4 := by dsimp [δ]; field_simp
  let ε := min εd (min εp (min εc (δ ^ 2)))
  have hε : 0 < ε := lt_min hεd (lt_min hεp (lt_min hεc (sq_pos_of_pos hδ)))
  have hεd' : ε ≤ εd := min_le_left _ _
  have hεp' : ε ≤ εp := (min_le_right _ _).trans (min_le_left _ _)
  have hεc' : ε ≤ εc := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεδ : ε ≤ δ ^ 2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨ε, hε, hεd'.trans hεη, 2 * C, by positivity, c, hc, hcmax, ?_⟩
  intro Y hk hu hw F
  have hk0 : 0 < Y 0 := by linarith only [hk]
  have hscale {r : ℝ} (hr : ε ≤ r) : ε / Y 0 ≤ r / Y 0 :=
    div_le_div_of_nonneg_right hr hk0.le
  obtain ⟨hvalid, ht, hF, hwalls⟩ := Hd Y hk
    ⟨hu.1, hu.2.trans (hscale hεd')⟩ ⟨hw.1, hw.2.trans (hscale hεd')⟩
  obtain ⟨_, _, hval, hderiv⟩ := Hp Y hk
    ⟨hu.1, hu.2.trans (hscale hεp')⟩ ⟨hw.1, hw.2.trans (hscale hεp')⟩
  have hcone := Hc Y hk
    ⟨hu.1, hu.2.trans (hscale hεc')⟩ ⟨hw.1, hw.2.trans (hscale hεc')⟩
  have hb : 0 ≤ Y 1 + Y 2 := add_nonneg hu.1 hw.1
  have hbε : Y 1 + Y 2 ≤ ε := by
    nlinarith only [(le_div_iff₀ hk0).mp hu.2, (le_div_iff₀ hk0).mp hw.2,
      mul_le_mul_of_nonneg_right hk hu.1, mul_le_mul_of_nonneg_right hk hw.1]
  have hs : Real.sqrt (Y 1 + Y 2) ≤ δ := Real.sqrt_le_iff.mpr ⟨hδ.le, hbε.trans hεδ⟩
  have he : C * Real.sqrt (Y 1 + Y 2) / Y 0 ≤ 1 / 4 := by
    calc
      _ ≤ C * Real.sqrt (Y 1 + Y 2) := div_le_self (by positivity) (by linarith only [hk])
      _ ≤ C * δ := mul_le_mul_of_nonneg_left hs hC.le
      _ = _ := hCδ
  refine ⟨hvalid, ht, hF, hval.trans ?_, hwalls, ?_⟩
  · apply div_le_div_of_nonneg_right _ hk0.le
    exact mul_le_mul_of_nonneg_right (by linarith only [hC] : C ≤ 2 * C) hb
  · intro v hv0 hv1 hv2 d
    have herr := hderiv v hv0 hv1 hv2
    have hmargin := herr.trans he
    refine ⟨⟨by linarith only [(abs_le.mp hmargin).1],
      by linarith only [(abs_le.mp hmargin).2]⟩, ?_, (hcone v hv0 hv1 hv2).2⟩
    exact (abs_log_le_twice_error he herr).trans_eq (by ring)

end BianchiIX
