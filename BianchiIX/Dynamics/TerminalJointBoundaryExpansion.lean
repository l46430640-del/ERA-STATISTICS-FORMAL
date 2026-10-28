import BianchiIX.Dynamics.TerminalMovingRadius

noncomputable section

namespace BianchiIX

open Filter Asymptotics
open scoped Topology

/-- The true boundary remainder is little-o in wall amplitude along jointly moving radius and height-coefficient paths. -/
theorem terminalConnectionPhase_joint_boundary_expansion {ι : Type*} {l : Filter ι}
    {α ξ u w : ι → ℝ} {α₀ ξ₀ : ℝ} (hα₀ : 0 < α₀ ∧ α₀ < 1)
    (hξ₀ : 0 < ξ₀ ∧ ξ₀ ≤ 1 / 40000)
    (hα : Tendsto α l (𝓝 α₀)) (hξ : Tendsto ξ l (𝓝 ξ₀))
    (hu : Tendsto u l (𝓝 0)) (hw : Tendsto w l (𝓝 0))
    (hpos : ∀ᶠ x in l, ξ x ≤ 1 / 40000 ∧ 0 < u x ∧ 0 < w x) :
    (fun x => 2 / terminalConnectionPhase (ξ x * α x ^ 2) ![2 + 2 * α x, u x, w x] - α x +
      u x / (2 + 2 * α x)) =o[l] (fun x => u x + w x) := by
  obtain ⟨C, hC, HC⟩ := exists_terminal_moving_radius_comparison
  let R := fun x => 2 + 2 * α x
  let R₀ := 2 + 2 * α₀
  let L : ExitTailState →L[ℝ] ℝ := (1 / 2 : ℝ) • ContinuousLinearMap.proj 0 +
    (-1 / R₀) • ContinuousLinearMap.proj 1
  have hR₀ : 2 < R₀ := by dsimp only [R₀]; linarith only [hα₀.1]
  have hR : Tendsto R l (𝓝 R₀) := (hα.const_mul 2).const_add 2
  have HY : Tendsto (fun x => (![R x, u x, w x] : ExitTailState)) l (𝓝 ![R₀, 0, 0]) := by
    apply tendsto_pi_nhds.mpr
    intro i
    fin_cases i
    · exact hR
    · exact hu
    · exact hw
  have Hmain : (fun x => 2 / terminalConnectionPhase (ξ x * α x ^ 2) ![R x, u x, w x] - α x +
      u x / R₀) =o[l] (fun x => u x + w x) := by
    apply IsLittleO.of_bound
    intro c hc
    obtain ⟨η, hη, Hsmall⟩ := exists_terminal_boundary_approximation_height (C := C) hα₀.1
      (div_pos hξ₀.1 (by norm_num : (0 : ℝ) < 4)) (div_pos hc (by norm_num : (0 : ℝ) < 4))
    let h := η * α₀ ^ 2
    let D := fderiv ℝ (terminalSinglePhase h) ![R₀, 0, 0]
    have hh : 0 < h ∧ h < 1 := by
      refine ⟨mul_pos hη.1 (pow_pos hα₀.1 2), ?_⟩
      exact (mul_le_of_le_one_right hη.1.le (pow_le_one₀ hα₀.1.le hα₀.2.le)).trans_lt
        (by linarith only [hη.2, hξ₀.2])
    have HE := HC α₀ ξ₀ η hα₀ hξ₀ hη hα hξ hu hw hpos
    have HT := (terminalSinglePhase_moving_radius_taylor hR₀ hh hR hu hw
      (hpos.mono fun _ hx => ⟨hx.2.1.le, hx.2.2.le⟩)).bound (div_pos hc (by norm_num : (0 : ℝ) < 4))
    have HV := (coreTail_reference_regular (by linarith only [hR₀] : 1 < R₀) hh).2.2.2.2.self_of_nhds
    have Henv := (contDiffAt_terminalSingleComparisonEnvelope_two
      (by change 1 < R₀; linarith only [hR₀]) HV).continuousAt.tendsto.comp HY
    have Hcoef : Tendsto (fun x => C / α x ^ 4) l (𝓝 (C / α₀ ^ 4)) :=
      tendsto_const_nhds.div (hα.pow 4) (pow_ne_zero 4 hα₀.1.ne')
    have Hnear := ((Hcoef.mul Henv).add_const ‖D - L‖).eventually (gt_mem_nhds
      (show C / α₀ ^ 4 * terminalSingleComparisonEnvelope h ![R₀, 0, 0] + ‖D - L‖ < c / 2 by
        change C / α₀ ^ 4 * terminalSingleComparisonEnvelope h ![R₀, 0, 0] + ‖D - L‖ < c / 4 at Hsmall
        linarith only [Hsmall, hc]))
    filter_upwards [hpos, HE, HT, Hnear] with x hp he ht hn
    let d : ExitTailState := ![0, u x, w x]
    have hb : 0 < u x + w x := add_pos hp.2.1 hp.2.2
    have hd : ‖d‖ ≤ u x + w x := by
      simpa [d] using exitTail_wall_offset_norm_le (R := 0) hp.2.1.le hp.2.2.le
    have HL : L d = -u x / R₀ := by dsimp [L, d]; simp; ring
    have Hlin : |(D - L) d| ≤ ‖D - L‖ * (u x + w x) :=
      ((D - L).le_opNorm d).trans (mul_le_mul_of_nonneg_left hd (norm_nonneg _))
    have He := (div_le_iff₀ hb).mp he
    change ‖terminalSinglePhase h ![R x, u x, w x] - (R x - 2) / 2 - D d‖ ≤ c / 4 * ‖u x + w x‖ at ht
    have HR : (R x - 2) / 2 = α x := by dsimp only [R]; ring
    rw [HR, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hb] at ht
    let e₁ := 2 / terminalConnectionPhase (ξ x * α x ^ 2) ![R x, u x, w x] - terminalSinglePhase h ![R x, u x, w x]
    let e₂ := terminalSinglePhase h ![R x, u x, w x] - α x - D d
    have Hid : 2 / terminalConnectionPhase (ξ x * α x ^ 2) ![R x, u x, w x] - α x + u x / R₀ =
        e₁ + e₂ + (D - L) d := by rw [sub_apply, HL]; dsimp only [e₁, e₂]; ring
    have Htri := (abs_add_le (e₁ + e₂) ((D - L) d)).trans (add_le_add (abs_add_le e₁ e₂) le_rfl)
    change |e₁| ≤ (C / α x ^ 4 * terminalSingleComparisonEnvelope h ![R x, u x, w x]) * (u x + w x) at He
    change |e₂| ≤ c / 4 * (u x + w x) at ht
    change C / α x ^ 4 * terminalSingleComparisonEnvelope h ![R x, u x, w x] + ‖D - L‖ < c / 2 at hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hb, Hid]
    nlinarith only [Htri, He, ht, Hlin, mul_le_mul_of_nonneg_right hn.le hb.le, mul_nonneg hc.le hb.le]
  have HU : u =O[l] (fun x => u x + w x) := by
    apply IsBigO.of_bound'
    filter_upwards [hpos] with x hx
    simp only [Real.norm_eq_abs, abs_of_pos hx.2.1, abs_of_pos (add_pos hx.2.1 hx.2.2)]
    exact le_add_of_nonneg_right hx.2.2.le
  have Hinv : Tendsto (fun x => 1 / R x - 1 / R₀) l (𝓝 0) := by
    have H := ((tendsto_const_nhds (x := (1 : ℝ))).div hR
      (by linarith only [hR₀] : R₀ ≠ 0)).sub_const (1 / R₀)
    simpa only [sub_self, Pi.div_apply] using H
  have Hdiff : (fun x => 1 / R x - 1 / R₀) =o[l] (fun _ => (1 : ℝ)) := (isLittleO_one_iff ℝ).mpr Hinv
  have Hcorr := Hdiff.mul_isBigO HU
  simp only [one_mul] at Hcorr
  apply (Hmain.add Hcorr).congr_left
  intro x
  dsimp only [R]
  ring

end BianchiIX
