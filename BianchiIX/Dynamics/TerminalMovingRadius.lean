import BianchiIX.Dynamics.TerminalBoundaryExpansion
import Mathlib.Analysis.Calculus.ContDiff.RCLike

noncomputable section

namespace BianchiIX

open Filter Asymptotics Set
open scoped Topology

/-- Strict differentiability measures the wall remainder by wall amplitude even when the radius moves. -/
theorem terminalSinglePhase_moving_radius_taylor {ι : Type*} {l : Filter ι}
    {R u w : ι → ℝ} {R₀ h : ℝ} (hR₀ : 2 < R₀) (hh : 0 < h ∧ h < 1)
    (hR : Tendsto R l (𝓝 R₀)) (hu : Tendsto u l (𝓝 0)) (hw : Tendsto w l (𝓝 0))
    (hpos : ∀ᶠ x in l, 0 ≤ u x ∧ 0 ≤ w x) :
    (fun x => terminalSinglePhase h ![R x, u x, w x] - (R x - 2) / 2 -
      fderiv ℝ (terminalSinglePhase h) ![R₀, 0, 0] ![0, u x, w x]) =o[l] (fun x => u x + w x) := by
  have HY : Tendsto (fun x => (![R x, u x, w x] : ExitTailState)) l (𝓝 ![R₀, 0, 0]) := by
    apply tendsto_pi_nhds.mpr
    intro i
    fin_cases i
    · exact hR
    · exact hu
    · exact hw
  have HZ : Tendsto (fun x => (![R x, 0, 0] : ExitTailState)) l (𝓝 ![R₀, 0, 0]) := by
    apply tendsto_pi_nhds.mpr
    intro i
    fin_cases i
    · exact hR
    · exact tendsto_const_nhds
    · exact tendsto_const_nhds
  have HD := (terminalSinglePhase_boundary_differential hR₀ hh).2.1.hasStrictFDerivAt (by norm_num)
  have HT := HD.isLittleO.comp_tendsto (HY.prodMk_nhds HZ)
  have HO : (fun x => (![R x, u x, w x] : ExitTailState) - ![R x, 0, 0]) =O[l] (fun x => u x + w x) := by
    apply IsBigO.of_bound'
    filter_upwards [hpos] with x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg (add_nonneg hx.1 hx.2)] using
      exitTail_wall_offset_norm_le (R := R x) hx.1 hx.2
  apply (HT.trans_isBigO HO).congr' _ EventuallyEq.rfl
  filter_upwards [hR.eventually (lt_mem_nhds hR₀)] with x hx
  dsimp only [Function.comp_def]
  rw [(terminalSinglePhase_boundary_differential hx hh).1]
  have Hdiff : (![R x, u x, w x] : ExitTailState) - ![R x, 0, 0] = ![0, u x, w x] := by
    ext i
    fin_cases i <;> simp
  rw [Hdiff]

/-- Freeze a late physical height on a moving-radius path without changing the actual terminal state. -/
theorem exists_terminal_moving_radius_comparison :
    ∃ C ≥ (1 : ℝ), ∀ α₀ ξ₀ η : ℝ,
      (0 < α₀ ∧ α₀ < 1) → (0 < ξ₀ ∧ ξ₀ ≤ 1 / 40000) → (0 < η ∧ η ≤ ξ₀ / 4) →
      ∀ {ι : Type*} {l : Filter ι} {α ξ u w : ι → ℝ},
      Tendsto α l (𝓝 α₀) → Tendsto ξ l (𝓝 ξ₀) →
      Tendsto u l (𝓝 0) → Tendsto w l (𝓝 0) →
      (∀ᶠ x in l, ξ x ≤ 1 / 40000 ∧ 0 < u x ∧ 0 < w x) →
      let h := η * α₀ ^ 2
      ∀ᶠ x in l,
        |2 / terminalConnectionPhase (ξ x * α x ^ 2) ![2 + 2 * α x, u x, w x] -
          terminalSinglePhase h ![2 + 2 * α x, u x, w x]| / (u x + w x) ≤
          C / α x ^ 4 * terminalSingleComparisonEnvelope h ![2 + 2 * α x, u x, w x] := by
  obtain ⟨C, hC, HC⟩ := exists_terminal_single_normalized_comparison_uniform
  refine ⟨C, hC, ?_⟩
  intro α₀ ξ₀ η hα₀ hξ₀ hη ι l α ξ u w hα hξ hu hw hpos h
  have hηhalf : 0 < η / 2 ∧ η / 2 ≤ 1 / 40000 :=
    ⟨div_pos hη.1 (by norm_num), by linarith only [hη.2, hξ₀.2, hη.1]⟩
  obtain ⟨εc, hεc, HE⟩ := HC (η / 2) hηhalf 2 (by norm_num)
  obtain ⟨εh, hεh, HH⟩ := exists_terminal_connection_uniform_height_independent
    (by norm_num : 0 < (1 / 10000 : ℝ) ∧ (1 / 10000 : ℝ) ≤ 1 / 10000)
    hηhalf.1 hηhalf.2 (by norm_num : (1 / 40000 : ℝ) ≤ 1 / 100)
    (q := 0) (J := 2) (by norm_num) (by norm_num)
  let ε := min εc εh
  have hε : 0 < ε := lt_min hεc hεh
  let ζ := fun x => h / α x ^ 2
  have Hζ : Tendsto ζ l (𝓝 η) := by
    have H : Tendsto ζ l (𝓝 (h / α₀ ^ 2)) := tendsto_const_nhds.div (hα.pow 2) (pow_ne_zero 2 hα₀.1.ne')
    have Heq : h / α₀ ^ 2 = η := by dsimp only [h]; field_simp [hα₀.1.ne']
    rwa [Heq] at H
  have Hsmall := (hu.add hw).eventually_lt (tendsto_const_nhds.mul (hα.pow (2 * 2)))
    (show (0 : ℝ) + 0 < ε * α₀ ^ (2 * 2) by simpa using mul_pos hε (pow_pos hα₀.1 _))
  have Hζlo := Hζ.eventually (lt_mem_nhds (show η / 2 < η by linarith only [hη.1]))
  have Hζhi := Hζ.eventually (gt_mem_nhds
    (show η < (1 / 40000 : ℝ) by linarith only [hη.1, hη.2, hξ₀.2]))
  have Hξlo := hξ.eventually (lt_mem_nhds (show η / 2 < ξ₀ by linarith only [hη.1, hη.2]))
  filter_upwards [hpos, Hsmall, Hζlo, Hζhi, Hξlo,
    hα.eventually (lt_mem_nhds hα₀.1), hα.eventually (gt_mem_nhds hα₀.2)] with x hp hs hzlo hzhi hxlo hapos hahi
  have ha : 0 < α x ∧ α x ≤ 1 := ⟨hapos, hahi.le⟩
  have hb : 0 < u x + w x := add_pos hp.2.1 hp.2.2
  have hsum : |u x| + |w x| ≤ u x + w x := by rw [abs_of_pos hp.2.1, abs_of_pos hp.2.2]
  have hsc := hs.le.trans (mul_le_mul_of_nonneg_right (min_le_left εc εh) (pow_nonneg hapos.le _))
  have hsh := hs.le.trans (mul_le_mul_of_nonneg_right (min_le_right εc εh) (pow_nonneg hapos.le _))
  have Hc := HE (ζ x) (α x) (u x + w x) (u x) (w x) hzlo.le hzhi.le ha hb hsc hsum hp.2.1 hp.2.2
  have H₁ := (HH (α x) (u x + w x) (u x) (w x) ha hb hsh hsum hp.2.1 hp.2.2 (ξ x) ⟨hxlo.le, hp.1⟩).2
  have H₂ := (HH (α x) (u x + w x) (u x) (w x) ha hb hsh hsum hp.2.1 hp.2.2 (ζ x) ⟨hzlo.le, hzhi.le⟩).2
  have Hheight : ζ x * α x ^ 2 = h := div_mul_cancel₀ _ (pow_ne_zero 2 hapos.ne')
  have Heq := H₁.trans H₂.symm
  rw [Hheight] at Heq Hc
  have Hp : terminalConnectionPhase (ξ x * α x ^ 2) ![2 + 2 * α x, u x, w x] =
      terminalConnectionPhase h ![2 + 2 * α x, u x, w x] := by
    unfold terminalConnectionPhase
    rw [Heq]
  rw [Hp]
  exact Hc.2

end BianchiIX
