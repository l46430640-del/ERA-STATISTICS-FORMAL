import BianchiIX.Dynamics.TerminalPhaseBoundarySlope
import BianchiIX.Dynamics.TerminalPhaseStatistics
import BianchiIX.Dynamics.TerminalHeightInterval

noncomputable section

namespace BianchiIX

open Filter Set
open scoped Topology

theorem eventually_lt_terminal_phase_coefficient {p C : ℝ} (hp : p < 2) :
    ∀ᶠ α : ℝ in 𝓝[>] 0, 0 < α ∧ α < 1 ∧
      C / α ^ p < 1 / ((2 + 2 * α) * α ^ 2) := by
  have HT : Tendsto (fun α : ℝ => α) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have HR : Tendsto (fun α : ℝ => C * α ^ (2 - p) * (2 + 2 * α))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using ((HT.rpow_const_nhds_zero (sub_pos.mpr hp)).const_mul C).mul
      ((HT.const_mul 2).const_add 2)
  filter_upwards [self_mem_nhdsWithin, HT.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    HR.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with α hα hαhi hbound
  change 0 < α at hα
  refine ⟨hα, hαhi, ?_⟩
  have hR : 0 < (2 + 2 * α) * α ^ 2 := mul_pos (by linarith only [hα]) (sq_pos_of_pos hα)
  apply (lt_div_iff₀ hR).mpr
  rw [Real.rpow_sub hα, Real.rpow_two] at hbound
  convert hbound using 1
  ring

/-- Every fixed positive radius has a positive-wall interval on which the exact phase is smooth. -/
theorem exists_terminal_phase_equal_wall_regular :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, (0 < η ∧ η ≤ δ) →
      ∀ J : ℕ, 4 ≤ J → ∀ α : ℝ, (0 < α ∧ α ≤ 1) → ∃ r > (0 : ℝ),
      ∀ t ∈ Ioo 0 r,
        coreTailValid (η * α ^ J) ![2 + 2 * α, t, t] ∧
        entranceReturnValid (terminalCyclicInput (η * α ^ J) ![2 + 2 * α, t, t]) ∧
        ContDiffAt ℝ 2 (terminalConnectionPhase (η * α ^ J)) ![2 + 2 * α, t, t] := by
  obtain ⟨δ, hδ, hδhi, HE⟩ := exists_terminal_phase_statistics
  refine ⟨δ, hδ, hδhi, ?_⟩
  intro η hη J hJ α hα
  obtain ⟨C, _, ε, hε, HC⟩ := HE η hη J hJ
  have hηhi : η ≤ 1 / 40000 := hη.2.trans hδhi
  obtain ⟨b₀, hb₀, HV⟩ := exists_terminal_connection_height_interval
    (by norm_num : 0 < (1 / 10000 : ℝ) ∧ (1 / 10000 : ℝ) ≤ 1 / 10000)
    ⟨hη.1, by linarith only [hηhi]⟩ (q := 0) (by omega : 0 + 2 ≤ J)
  refine ⟨min ε b₀ * α ^ (2 * J) / 2,
    div_pos (mul_pos (lt_min hε hb₀) (pow_pos hα.1 _)) (by norm_num), ?_⟩
  intro t ht
  have hbudget : 2 * t ≤ min ε b₀ * α ^ (2 * J) := by linarith only [ht.2]
  have hsum : |t| + |t| ≤ 2 * t := by rw [abs_of_pos ht.1]; linarith
  have H := HC η α (2 * t) t t le_rfl hη.2 hα (by linarith only [ht.1])
    (hbudget.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (pow_nonneg hα.1.le _)))
    hsum ht.1 ht.1
  have V := HV η α (2 * t) t t le_rfl (by linarith only [hηhi])
    (by norm_num; exact hηhi) hα (by linarith only [ht.1])
    (hbudget.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (pow_nonneg hα.1.le _)))
    hsum ht.1 ht.1
  exact ⟨H.1, V.2.1, H.2.1⟩

/-- Neither value errors nor ordinary amplitude columns admit any smaller uniform phase power,
even after imposing an arbitrarily small positive amplitude budget at each radius. -/
theorem exists_terminal_phase_exponent_obstruction :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, (0 < η ∧ η ≤ δ) →
      ∀ J : ℕ, 4 ≤ J → ∀ p C : ℝ, p < 2 →
      ∀ᶠ α : ℝ in 𝓝[>] 0, 0 < α ∧ α < 1 ∧ ∀ ρ : ℝ, 0 < ρ →
      (∃ t : ℝ, 0 < t ∧ 2 * t < ρ ∧
        coreTailValid (η * α ^ J) ![2 + 2 * α, t, t] ∧
        entranceReturnValid (terminalCyclicInput (η * α ^ J) ![2 + 2 * α, t, t]) ∧
        ContDiffAt ℝ 2 (terminalConnectionPhase (η * α ^ J)) ![2 + 2 * α, t, t] ∧
        C * (2 * t) / α ^ p <
          |terminalConnectionPhase (η * α ^ J) ![2 + 2 * α, t, t] - 2 / α|) ∧
      (∃ s : ℝ, 0 < s ∧ 2 * s < ρ ∧
        coreTailValid (η * α ^ J) ![2 + 2 * α, s, s] ∧
        entranceReturnValid (terminalCyclicInput (η * α ^ J) ![2 + 2 * α, s, s]) ∧
        ContDiffAt ℝ 2 (terminalConnectionPhase (η * α ^ J)) ![2 + 2 * α, s, s] ∧
        C / α ^ p <
          |fderiv ℝ (terminalConnectionPhase (η * α ^ J)) ![2 + 2 * α, s, s] (Pi.single 1 1)| +
          |fderiv ℝ (terminalConnectionPhase (η * α ^ J)) ![2 + 2 * α, s, s] (Pi.single 2 1)|) := by
  obtain ⟨δ, hδ, hδhi, Hreg⟩ := exists_terminal_phase_equal_wall_regular
  refine ⟨δ, hδ, hδhi, ?_⟩
  intro η hη J hJ p C hp
  filter_upwards [eventually_lt_terminal_phase_coefficient (C := C) hp] with α hα
  refine ⟨hα.1, hα.2.1, ?_⟩
  intro ρ hρ
  obtain ⟨r, hr, Hr⟩ := Hreg η hη J hJ α ⟨hα.1, hα.2.1.le⟩
  let r₀ := min r (ρ / 2)
  have hr₀ : 0 < r₀ := lt_min hr (by positivity)
  have HI {t : ℝ} (ht : t ∈ Ioo 0 r₀) : t ∈ Ioo 0 r ∧ 2 * t < ρ := by
    have htr := ht.2.trans_le (min_le_left r (ρ / 2))
    have htρ := ht.2.trans_le (min_le_right r (ρ / 2))
    exact ⟨⟨ht.1, htr⟩, by linarith only [htρ]⟩
  have HT := tendsto_terminal_phase_equal_wall_slope ⟨hα.1, hα.2.1.le⟩
    ⟨hη.1, hη.2.trans hδhi⟩ (by omega : 2 ≤ J)
  let L := 2 / ((2 + 2 * α) * α ^ 2)
  have hL : 0 < L := div_pos (by norm_num)
    (mul_pos (by linarith only [hα.1]) (sq_pos_of_pos hα.1))
  have hB : 2 * (C / α ^ p) < L := by
    calc
      2 * (C / α ^ p) < 2 * (1 / ((2 + 2 * α) * α ^ 2)) :=
        mul_lt_mul_of_pos_left hα.2.2 (by norm_num)
      _ = L := by dsimp only [L]; ring
  constructor
  · have HE := HT.eventually (lt_mem_nhds hB)
    have Hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ Ioo 0 r₀ := by
      filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds hr₀).filter_mono nhdsWithin_le_nhds] with t ht htr
      exact ⟨ht, htr⟩
    obtain ⟨t, ht, he⟩ := (Hsmall.and HE).exists
    have HD := Hr t (HI ht).1
    refine ⟨t, ht.1, (HI ht).2, HD.1, HD.2.1, HD.2.2, ?_⟩
    have Hmul := (lt_div_iff₀ ht.1).mp he
    have Hval : C * (2 * t) / α ^ p <
        terminalConnectionPhase (η * α ^ J) ![2 + 2 * α, t, t] - 2 / α := by
      calc
        C * (2 * t) / α ^ p = (2 * (C / α ^ p)) * t := by ring
        _ < _ := Hmul
    exact Hval.trans_le (le_abs_self _)
  · have Hder {t : ℝ} (ht : t ∈ Ioo 0 r₀) :=
      hasDerivAt_terminal_phase_equal_wall ((Hr t (HI ht).1).2.2.differentiableAt (by norm_num))
    obtain ⟨s, hs, Hs⟩ := exists_derivative_gt_of_boundary_slope HT hr₀
      (by linarith only [hB, hL] : C / α ^ p < L) (fun t ht => Hder ht)
    have HD := Hr s (HI hs).1
    refine ⟨s, hs.1, (HI hs).2, HD.1, HD.2.1, HD.2.2, ?_⟩
    exact Hs.trans_le (add_le_add (le_abs_self _) (le_abs_self _))

end BianchiIX
