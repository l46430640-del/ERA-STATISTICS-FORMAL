import BianchiIX.Dynamics.TerminalWeakDirectionalLimits
import BianchiIX.Dynamics.TerminalPhaseCone

noncomputable section

namespace BianchiIX

open Filter Set
open scoped Topology

theorem tendsto_terminal_equal_wall_sqrt_output {η c : ℝ} (hη : 0 < η ∧ η ≤ 1 / 40000)
    (hc : 0 < c) {J : ℕ} (hJ : 2 ≤ J) :
    Tendsto (fun α : ℝ => α ^ 2 * Real.sqrt (terminalConnectionState (η * α ^ J)
      (terminalEqualWallInitial J c α) 3) / (c * α ^ (2 * J + 1))) (𝓝[>] 0) (𝓝 taubMultiplierConstant) := by
  have H := Real.continuous_sqrt.continuousAt.tendsto.comp (tendsto_terminal_equal_wall_weak_output hη hc hJ)
  rw [Real.sqrt_sq taubMultiplierConstant_pos.le] at H
  apply H.congr'
  filter_upwards [show ∀ᶠ α : ℝ in 𝓝[>] 0, 0 < α from self_mem_nhdsWithin] with α hα
  dsimp only [Function.comp_def]
  rw [Real.sqrt_div' _ (sq_nonneg _), show α ^ 4 = (α ^ 2) ^ 2 by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (sq_nonneg α), Real.sqrt_sq (mul_pos hc (pow_pos hα _)).le]

theorem exists_terminal_equal_wall_phase_limits :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η c : ℝ, (0 < η ∧ η ≤ δ) → 0 < c →
      ∀ J : ℕ, 4 ≤ J →
      (∀ᶠ α : ℝ in 𝓝[>] 0,
        fderiv ℝ (terminalConnectionPhase (η * α ^ J)) (terminalEqualWallInitial J c α)
          (terminalSharpWeakDirection (c * α ^ (2 * J + 1))) < 0) ∧
      Tendsto (fun α : ℝ => α ^ 2 *
        fderiv ℝ (terminalConnectionPhase (η * α ^ J)) (terminalEqualWallInitial J c α)
          (terminalSharpWeakDirection (c * α ^ (2 * J + 1)))) (𝓝[>] 0) (𝓝 (-1)) := by
  obtain ⟨δ, hδ, hδhi, HP⟩ := exists_terminal_phase_cone_bounds
  refine ⟨δ, hδ, hδhi, ?_⟩
  intro η c hη hc J hJ
  obtain ⟨C, _, ε, hε, HC⟩ := HP η hη J hJ
  let p := fun α : ℝ => fderiv ℝ (terminalConnectionPhase (η * α ^ J)) (terminalEqualWallInitial J c α)
    (terminalSharpWeakDirection (c * α ^ (2 * J + 1)))
  have HE : ∀ᶠ α : ℝ in 𝓝[>] 0,
      |α ^ 2 * p α + 1| ≤ C * Real.sqrt (2 * c * α ^ (2 * J + 1)) ∧ p α < 0 := by
    filter_upwards [eventually_equal_wall_budget hc hε J] with α ha
    have H := HC η α (2 * c * α ^ (2 * J + 1)) (c * α ^ (2 * J + 1)) (c * α ^ (2 * J + 1))
      le_rfl hη.2 ha.1 ha.2.2.1 ha.2.2.2.1 ha.2.2.2.2 ha.2.1 ha.2.1
    have Hd := H.2.2.2 (terminalSharpWeakDirection (c * α ^ (2 * J + 1))) rfl
      (by simp [terminalSharpWeakDirection, abs_of_nonneg (Real.sqrt_nonneg _)])
      (by simp [terminalSharpWeakDirection])
    exact ⟨Hd.1, Hd.2.1⟩
  refine ⟨HE.mono (fun _ ha => ha.2), ?_⟩
  have HT : Tendsto (fun α : ℝ => α) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have HB : Tendsto (fun α : ℝ => 2 * c * α ^ (2 * J + 1)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (HT.pow (2 * J + 1)).const_mul (2 * c)
  have HG : Tendsto (fun α : ℝ => C * Real.sqrt (2 * c * α ^ (2 * J + 1))) (𝓝[>] 0) (𝓝 0) := by
    simpa using (Real.continuous_sqrt.continuousAt.tendsto.comp HB).const_mul C
  have HD : Tendsto (fun α : ℝ => α ^ 2 * p α + 1) (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero_norm' _ HG
    exact HE.mono (fun _ ha => by simpa only [Real.norm_eq_abs] using ha.1)
  simpa only [add_sub_cancel_right, zero_sub] using HD.sub_const 1

theorem normalized_sqrt_wall_ratio_identity {α u w p d : ℝ}
    (hα : α ≠ 0) (hu : 0 < u) (hw : 0 < w) (hp : p ≠ 0) :
    |d| / (Real.sqrt w * |p|) / Real.sqrt u =
      (α ^ 2 * Real.sqrt w / u) * |Real.sqrt u * (d / w)| / |α ^ 2 * p| := by
  have hs : Real.sqrt u ≠ 0 := (Real.sqrt_pos.2 hu).ne'
  have ht : Real.sqrt w ≠ 0 := (Real.sqrt_pos.2 hw).ne'
  have hp' : |p| ≠ 0 := abs_ne_zero.mpr hp
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg u), abs_div, abs_of_pos hw,
    abs_mul, abs_of_nonneg (sq_nonneg α)]
  field_simp
  rw [Real.sq_sqrt hw.le, Real.sq_sqrt hu.le]
  ring

def terminalEqualWallWeakConeRatio (η c : ℝ) (J : ℕ) (α : ℝ) : ℝ :=
  let Y := terminalEqualWallInitial J c α
  let h := η * α ^ J
  let d := terminalSharpWeakDirection (c * α ^ (2 * J + 1))
  |fderiv ℝ (terminalConnectionState h) Y d 3| /
    (Real.sqrt (terminalConnectionState h Y 3) * |fderiv ℝ (terminalConnectionPhase h) Y d|) /
      Real.sqrt (c * α ^ (2 * J + 1))

/-- Formula (D.39) for the actual finite Einstein connection and the specified ordinary direction. -/
theorem exists_terminal_sharp_weak_cone_limit :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η c : ℝ, (0 < η ∧ η ≤ δ) → 0 < c →
      ∀ J : ℕ, 4 ≤ J →
      Tendsto (terminalEqualWallWeakConeRatio η c J) (𝓝[>] 0) (𝓝 taubMultiplierConstant) := by
  obtain ⟨δw, hδw, hδwhi, HW⟩ := exists_terminal_equal_wall_weak_response_limits
  obtain ⟨δp, hδp, _, HP⟩ := exists_terminal_equal_wall_phase_limits
  refine ⟨min δw δp, lt_min hδw hδp, (min_le_left _ _).trans hδwhi, ?_⟩
  intro η c hη hc J hJ
  have hJ2 : 2 ≤ J := by omega
  have hηw : 0 < η ∧ η ≤ δw := ⟨hη.1, hη.2.trans (min_le_left _ _)⟩
  have hηp : 0 < η ∧ η ≤ δp := ⟨hη.1, hη.2.trans (min_le_right _ _)⟩
  obtain ⟨Hreg, Hlog⟩ := HW η c hηw hc J hJ2
  obtain ⟨Hneg, Hphase⟩ := HP η c hηp hc J hJ
  have Hval := tendsto_terminal_equal_wall_sqrt_output ⟨hη.1, hηw.2.trans hδwhi⟩ hc hJ2
  have HL := Hlog.abs
  have HPabs := Hphase.abs
  simp only [abs_one] at HL
  simp only [abs_neg, abs_one] at HPabs
  have HT := (Hval.mul HL).div HPabs (by norm_num : (1 : ℝ) ≠ 0)
  simp only [mul_one, div_one] at HT
  apply HT.congr'
  filter_upwards [Hreg, Hneg, show ∀ᶠ α : ℝ in 𝓝[>] 0, 0 < α from self_mem_nhdsWithin] with α hreg hneg hα
  let Y := terminalEqualWallInitial J c α
  let h := η * α ^ J
  let d := terminalSharpWeakDirection (c * α ^ (2 * J + 1))
  have HD := congrFun (terminalConnectionLogWalls_fderiv
    (hreg.1.differentiableAt (by norm_num)) hreg.2.1.ne' hreg.2.2.ne' d) 1
  change fderiv ℝ (terminalConnectionLogWalls h) Y d 1 =
    fderiv ℝ (terminalConnectionState h) Y d 3 / terminalConnectionState h Y 3 at HD
  change (α ^ 2 * Real.sqrt (terminalConnectionState h Y 3) / (c * α ^ (2 * J + 1))) *
    |Real.sqrt (c * α ^ (2 * J + 1)) * fderiv ℝ (terminalConnectionLogWalls h) Y d 1| /
    |α ^ 2 * fderiv ℝ (terminalConnectionPhase h) Y d| = _
  rw [HD]
  exact (normalized_sqrt_wall_ratio_identity hα.ne' (mul_pos hc (pow_pos hα _)) hreg.2.2 hneg.ne).symm

/-- Every exponent strictly larger than one half fails even on the positive equal-wall path. -/
theorem exists_terminal_weak_exponent_obstruction :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η c : ℝ, (0 < η ∧ η ≤ δ) → 0 < c →
      ∀ J : ℕ, 4 ≤ J → ∀ γ K : ℝ, 1 / 2 < γ →
      ∀ᶠ α : ℝ in 𝓝[>] 0,
        let u := c * α ^ (2 * J + 1)
        let Y := terminalEqualWallInitial J c α
        let h := η * α ^ J
        let d := terminalSharpWeakDirection u
        K * (2 * u) ^ γ < |fderiv ℝ (terminalConnectionState h) Y d 3| /
          (Real.sqrt (terminalConnectionState h Y 3) * |fderiv ℝ (terminalConnectionPhase h) Y d|) := by
  obtain ⟨δ, hδ, hδhi, HT⟩ := exists_terminal_sharp_weak_cone_limit
  refine ⟨δ, hδ, hδhi, ?_⟩
  intro η c hη hc J hJ γ K hγ
  have HR := HT η c hη hc J hJ
  let u := fun α : ℝ => c * α ^ (2 * J + 1)
  have Hα : Tendsto (fun α : ℝ => α) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have HU : Tendsto u (𝓝[>] 0) (𝓝 0) := by
    simpa [u] using (Hα.pow (2 * J + 1)).const_mul c
  have HP : Tendsto (fun α : ℝ => K * (2 * u α) ^ γ / Real.sqrt (u α)) (𝓝[>] 0) (𝓝 0) := by
    have H := (HU.rpow_const_nhds_zero (sub_pos.mpr hγ)).const_mul (K * (2 : ℝ) ^ γ)
    simp only [mul_zero] at H
    apply H.congr'
    filter_upwards [show ∀ᶠ α : ℝ in 𝓝[>] 0, 0 < α from self_mem_nhdsWithin] with α hα
    have hu : 0 < u α := mul_pos hc (pow_pos hα _)
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hu.le, Real.sqrt_eq_rpow,
      Real.rpow_sub hu]
    ring
  have hhalf : 0 < taubMultiplierConstant / 2 := by positivity [taubMultiplierConstant_pos]
  have hhalf' : taubMultiplierConstant / 2 < taubMultiplierConstant := by linarith only [taubMultiplierConstant_pos]
  filter_upwards [HP.eventually (gt_mem_nhds hhalf), HR.eventually (lt_mem_nhds hhalf'),
    show ∀ᶠ α : ℝ in 𝓝[>] 0, 0 < α from self_mem_nhdsWithin] with α ha hb hα
  have hsp : 0 < Real.sqrt (u α) := Real.sqrt_pos.2 (mul_pos hc (pow_pos hα _))
  have hs : Real.sqrt (u α) ≠ 0 := hsp.ne'
  have H := mul_lt_mul_of_pos_right (ha.trans hb) hsp
  change K * (2 * u α) ^ γ / Real.sqrt (u α) * Real.sqrt (u α) <
    terminalEqualWallWeakConeRatio η c J α * Real.sqrt (u α) at H
  dsimp only [u] at hs H
  simpa only [terminalEqualWallWeakConeRatio, div_mul_cancel₀ _ hs] using H

end BianchiIX
