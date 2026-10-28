import BianchiIX.Dynamics.TerminalBoundaryApproximation

noncomputable section

namespace BianchiIX

open Filter Asymptotics Set
open scoped Topology

/-- Choose one finite height at which both the boundary comparison and the differential error are small. -/
theorem exists_terminal_boundary_approximation_height {α η₁ ε C : ℝ}
    (hα : 0 < α) (hη₁ : 0 < η₁) (hε : 0 < ε) :
    let R := 2 + 2 * α
    let L : ExitTailState →L[ℝ] ℝ := (1 / 2 : ℝ) • ContinuousLinearMap.proj 0 +
      (-1 / R) • ContinuousLinearMap.proj 1
    ∃ η : ℝ, (0 < η ∧ η ≤ η₁) ∧
      C / α ^ 4 * terminalSingleComparisonEnvelope (η * α ^ 2) ![R, 0, 0] +
        ‖fderiv ℝ (terminalSinglePhase (η * α ^ 2)) ![R, 0, 0] - L‖ < ε := by
  intro R L
  have hR : 2 < R := by dsimp only [R]; linarith only [hα]
  have Hη : Tendsto (id : ℝ → ℝ) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have Hh : Tendsto (fun η : ℝ => η * α ^ 2) (𝓝[>] 0) (𝓝 0) := by
    simpa only [zero_mul, id_eq] using Hη.mul_const (α ^ 2)
  have Hpos : ∀ᶠ η : ℝ in 𝓝[>] 0, 0 < η * α ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    exact mul_pos hη (pow_pos hα 2)
  have HE := tendsto_terminalSingleComparisonEnvelope_scaled_boundary (C := C) hR
    (show Tendsto (fun _ : ℝ => R) (𝓝[>] 0) (𝓝 R) from tendsto_const_nhds) Hh Hpos
  have HR : (R - 2) / 2 = α := by dsimp only [R]; ring
  rw [HR] at HE
  have HL := tendsto_terminalSinglePhase_boundary_fderiv hR
    (show Tendsto (fun _ : ℝ => R) (𝓝[>] 0) (𝓝 R) from tendsto_const_nhds) Hh Hpos
  change Tendsto _ _ (𝓝 L) at HL
  have HN := (HL.sub (tendsto_const_nhds (x := L))).norm
  simp only [sub_self, norm_zero] at HN
  have H := HE.add HN
  simp only [zero_add] at H
  obtain ⟨η, hsmall, hη⟩ := ((H.eventually (gt_mem_nhds hε)).and (Ioo_mem_nhdsGT hη₁)).exists
  exact ⟨η, ⟨hη.1, hη.2.le⟩, hsmall⟩

/-- The first expansion in (D.40), for the actual arrival and arbitrary positive wall paths. -/
theorem terminalConnectionPhase_boundary_expansion {ι : Type*} {l : Filter ι}
    {u w : ι → ℝ} {α η₁ : ℝ} (hα : 0 < α ∧ α ≤ 1)
    (hη₁ : 0 < η₁ ∧ η₁ ≤ 1 / 40000)
    (hu : Tendsto u l (𝓝 0)) (hw : Tendsto w l (𝓝 0))
    (hpos : ∀ᶠ x in l, 0 < u x ∧ 0 < w x) :
    (fun x => 2 / terminalConnectionPhase (η₁ * α ^ 2) ![2 + 2 * α, u x, w x] - α +
      u x / (2 + 2 * α)) =o[l] (fun x => u x + w x) := by
  obtain ⟨C, hC, HC⟩ := exists_terminal_single_comparison_boundary_control
  let R := 2 + 2 * α
  let L : ExitTailState →L[ℝ] ℝ := (1 / 2 : ℝ) • ContinuousLinearMap.proj 0 +
    (-1 / R) • ContinuousLinearMap.proj 1
  let A := C / α ^ 4
  have hA : 0 < A := div_pos (by linarith only [hC]) (pow_pos hα.1 4)
  have hR : 2 < R := by dsimp only [R]; linarith only [hα.1]
  have HR : (R - 2) / 2 = α := by dsimp only [R]; ring
  apply IsLittleO.of_bound
  intro c hc
  obtain ⟨η, hη, Hsmall⟩ := exists_terminal_boundary_approximation_height (C := C) hα.1 hη₁.1
    (div_pos hc (by norm_num : (0 : ℝ) < 4))
  let h := η * α ^ 2
  let D := fderiv ℝ (terminalSinglePhase h) ![R, 0, 0]
  let δ := c / (4 * A)
  have hδ : 0 < δ := div_pos hc (by positivity)
  have Hδ : A * δ = c / 4 := by dsimp only [δ]; field_simp
  have hh : 0 < h ∧ h < 1 := by
    refine ⟨mul_pos hη.1 (pow_pos hα.1 2), ?_⟩
    exact (mul_le_of_le_one_right hη.1.le (pow_le_one₀ hα.1.le hα.2)).trans_lt
      (by linarith only [hη.2, hη₁.2])
  have HE := HC α η hα ⟨hη.1, hη.2.trans hη₁.2⟩ hu hw hpos δ hδ
  have HT := (terminalSinglePhase_boundary_path_taylor hR hh hu hw
    (hpos.mono fun _ hx => ⟨hx.1.le, hx.2.le⟩)).bound (div_pos hc (by norm_num : (0 : ℝ) < 4))
  have HH := eventually_terminalConnectionState_boundary_height_eq hα hη.1 hη.2 hη₁.2 hu hw hpos
  filter_upwards [hpos, HE, HT, HH] with x hp he ht heq
  let d : ExitTailState := ![R, u x, w x] - ![R, 0, 0]
  have hb : 0 < u x + w x := add_pos hp.1 hp.2
  have hd := exitTail_wall_offset_norm_le (R := R) hp.1.le hp.2.le
  have HL : L d = -u x / R := by
    dsimp [L, d]
    simp
    ring
  have Hphase : terminalConnectionPhase (η₁ * α ^ 2) ![R, u x, w x] =
      terminalConnectionPhase h ![R, u x, w x] := by
    unfold terminalConnectionPhase
    rw [heq]
  have He := (div_le_iff₀ hb).mp he.2
  change |2 / terminalConnectionPhase h ![R, u x, w x] - terminalSinglePhase h ![R, u x, w x]| ≤
    A * (_ + _ + δ) * (u x + w x) at He
  rw [← terminalSingleComparisonEnvelope_boundary (by linarith only [hR]) hh] at He
  change |2 / terminalConnectionPhase h ![R, u x, w x] - terminalSinglePhase h ![R, u x, w x]| ≤
    A * (terminalSingleComparisonEnvelope h ![R, 0, 0] + δ) * (u x + w x) at He
  change ‖terminalSinglePhase h ![R, u x, w x] - (R - 2) / 2 - D d‖ ≤
    c / 4 * ‖u x + w x‖ at ht
  rw [HR, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hb] at ht
  have Hlin : |(D - L) d| ≤ ‖D - L‖ * (u x + w x) := by
    exact ((D - L).le_opNorm d).trans (mul_le_mul_of_nonneg_left hd (norm_nonneg _))
  have Hid : 2 / terminalConnectionPhase (η₁ * α ^ 2) ![R, u x, w x] - α + u x / R =
      (2 / terminalConnectionPhase h ![R, u x, w x] - terminalSinglePhase h ![R, u x, w x]) +
      (terminalSinglePhase h ![R, u x, w x] - α - D d) + (D - L) d := by
    rw [Hphase, sub_apply, HL]
    ring
  have Htri := (abs_add_le
    ((2 / terminalConnectionPhase h ![R, u x, w x] - terminalSinglePhase h ![R, u x, w x]) +
      (terminalSinglePhase h ![R, u x, w x] - α - D d)) ((D - L) d)).trans
      (add_le_add (abs_add_le
        (2 / terminalConnectionPhase h ![R, u x, w x] - terminalSinglePhase h ![R, u x, w x])
        (terminalSinglePhase h ![R, u x, w x] - α - D d)) le_rfl)
  change A * terminalSingleComparisonEnvelope h ![R, 0, 0] + ‖D - L‖ < c / 4 at Hsmall
  have Hcoeff : A * (terminalSingleComparisonEnvelope h ![R, 0, 0] + δ) + c / 4 + ‖D - L‖ ≤ c := by
    nlinarith only [Hsmall, Hδ, hc]
  change ‖2 / terminalConnectionPhase (η₁ * α ^ 2) ![R, u x, w x] - α + u x / R‖ ≤ c * ‖u x + w x‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hb, Hid]
  nlinarith only [Htri, He, ht, Hlin, mul_le_mul_of_nonneg_right Hcoeff hb.le]

end BianchiIX
