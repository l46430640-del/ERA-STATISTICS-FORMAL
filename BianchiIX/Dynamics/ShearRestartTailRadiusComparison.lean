import BianchiIX.Algebra.TwoStageRadiusResponse
import BianchiIX.Dynamics.EntranceReflectionValues
import BianchiIX.Dynamics.ShearRestartTailConnectionCurve

noncomputable section

namespace BianchiIX

open Set

/-- The core and long connection have bounded radius displacement and an inverse-scale ordinary derivative error. -/
theorem exists_restartShearTail_radius_comparison :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε ζ ν : ℝ,
          (0 ≤ ε ∧ ε ≤ 1 / 128) →
          (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
          (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
          let s := shearTailTime a D + q / 2 * Real.log (1 / a)
          let κ := restartShearTailEntranceRadius h a q D ζ ν
          let g := fun r => restartShearReturnState h s ζ ν r 0
          DifferentiableAt ℝ κ ρ ∧ DifferentiableAt ℝ g ρ ∧
          1 / (96 * a) ≤ κ ρ ∧ 1 / (96 * a) ≤ g ρ ∧
          |g ρ - κ ρ| ≤ 3 ∧ |deriv κ ρ| ≤ 24576 / a ^ 2 ∧
          |deriv g ρ - deriv κ ρ| ≤ 1179648 / a := by
  obtain ⟨hI, hhI, HI⟩ := exists_restartShearTail_core_inputs
  obtain ⟨hR, hhR, HR⟩ := exists_restartShearTail_entrance_phase
  obtain ⟨hC, hhC, HC⟩ := exists_restartShearTail_core_cone
  obtain ⟨hG, hhG, HG⟩ := exists_restartShearTail_connection_curve
  refine ⟨min hI (min hR (min hC hG)), lt_min hhI (lt_min hhR (lt_min hhC hhG)), ?_⟩
  intro h hh q D P hq hD hP
  have hh' := hh.2.trans (min_le_right _ _)
  have hh'' := hh'.trans (min_le_right _ _)
  obtain ⟨aI, haI, HAI⟩ := HI h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq hD hP
    (1 / 10000) ⟨by norm_num, le_rfl⟩
  obtain ⟨_, _, HBR⟩ := HR h ⟨hh.1, hh'.trans (min_le_left _ _)⟩ q D
    (by linarith only [hq]) (by linarith only [hD])
  obtain ⟨aR, haR, HAR⟩ := HBR P hP
  obtain ⟨aC, haC, HAC⟩ := HC h ⟨hh.1, hh''.trans (min_le_left _ _)⟩ q D P hq hD hP
  obtain ⟨aG, haG, HAG⟩ := HG h ⟨hh.1, hh''.trans (min_le_right _ _)⟩ q D P hq hD hP
  refine ⟨min aI (min aR (min aC aG)), lt_min haI (lt_min haR (lt_min haC haG)), ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ s κ g
  have ha' := ha.2.trans (min_le_right _ _)
  have ha'' := ha'.trans (min_le_right _ _)
  obtain ⟨_, _, hk8, _, _, hm, hu, hv, hw, hsmall, _⟩ :=
    HAI a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  obtain ⟨_, _, _, _, _, _, HK, hκlo, _, _, Hκder⟩ :=
    HAR a ⟨ha.1, ha'.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  obtain ⟨hκ6, _, _, hκneg, hfneg, Hcore, Hbounds, _⟩ :=
    HAC a ⟨ha.1, ha''.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  obtain ⟨HGdiff, _, _, _, _, _, Hconn, _⟩ :=
    HAG a ⟨ha.1, ha''.trans (min_le_right _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  let Y := restartShearTailProjectiveEntry h a q ζ ν (shearTailTime a D)
  let f := fun r => partialCoreDownwardReturnState (Y r) 0
  have HV := entrancePartialCore_reflection_values hk8 hm.le hu hv hw ⟨by norm_num, le_rfl⟩ hsmall
  change κ ρ / 2 ≤ restartShearReturnParameters h s ζ ν ρ 0 ∧
    (1 ≤ κ ρ - g ρ ∧ κ ρ - g ρ ≤ 3) ∧ κ ρ / 2 ≤ g ρ ∧ g ρ ≤ κ ρ ∧ _ at HV
  change 6 ≤ κ ρ at hκ6
  change 1 / (48 * a) ≤ κ ρ at hκlo
  change -deriv κ ρ ≤ 24576 / a ^ 2 at Hκder
  change deriv κ ρ < 0 at hκneg
  change deriv f ρ < 0 at hfneg
  have hκpos : 0 < κ ρ := by linarith only [hκ6]
  have hratio : |deriv f ρ / deriv κ ρ| ≤ 5 / 4 := by
    rw [abs_of_nonneg (div_pos_of_neg_of_neg hfneg hκneg).le]
    exact Hbounds.2
  have Hd := two_stage_radius_response hκpos HV.1 hκneg.ne hfneg.ne hratio Hcore Hconn
  have hκabs : |deriv κ ρ| ≤ 24576 / a ^ 2 := by rwa [abs_of_neg hκneg]
  have Hgκ : |deriv g ρ - deriv κ ρ| ≤ 1179648 / a := Hd.trans (by
    calc
      _ ≤ (24576 / a ^ 2) / (1 / (48 * a)) :=
        div_le_div₀ (by positivity) hκabs (by positivity [ha.1]) hκlo
      _ = _ := by field_simp; ring)
  have Hg : DifferentiableAt ℝ g ρ := differentiableAt_pi.mp (HGdiff.differentiableAt (by norm_num)) 0
  refine ⟨HK, Hg, ?_, ?_, ?_, hκabs, Hgκ⟩
  · exact (div_le_div_of_nonneg_left (by norm_num) (by positivity [ha.1]) (by linarith only [ha.1])).trans hκlo
  · calc
      _ = (1 / (48 * a)) / 2 := by ring
      _ ≤ κ ρ / 2 := div_le_div_of_nonneg_right hκlo (by norm_num)
      _ ≤ _ := HV.2.2.1
  · rw [abs_of_nonpos (sub_nonpos.mpr HV.2.2.2.1)]
    linarith only [HV.2.1.2]

end BianchiIX
