import BianchiIX.Dynamics.TerminalHeightInterval
import BianchiIX.Dynamics.TerminalSingleBoundaryLimits
import BianchiIX.Dynamics.TerminalSingleComparisonLimits

noncomputable section

namespace BianchiIX

open Filter Asymptotics
open scoped Topology

theorem exitTail_wall_offset_norm_le {R u w : ℝ} (hu : 0 ≤ u) (hw : 0 ≤ w) :
    ‖(![R, u, w] : ExitTailState) - ![R, 0, 0]‖ ≤ u + w := by
  apply (pi_norm_le_iff_of_nonneg (add_nonneg hu hw)).mpr
  intro i
  fin_cases i
  · change ‖R - R‖ ≤ u + w
    simpa using add_nonneg hu hw
  · change ‖u - 0‖ ≤ u + w
    simpa only [sub_zero, Real.norm_eq_abs, abs_of_nonneg hu] using le_add_of_nonneg_right hw
  · change ‖w - 0‖ ≤ u + w
    simpa only [sub_zero, Real.norm_eq_abs, abs_of_nonneg hw] using le_add_of_nonneg_left hu

theorem terminalSinglePhase_boundary_path_taylor {ι : Type*} {l : Filter ι} {u w : ι → ℝ}
    {R h : ℝ} (hR : 2 < R) (hh : 0 < h ∧ h < 1)
    (hu : Tendsto u l (𝓝 0)) (hw : Tendsto w l (𝓝 0))
    (hpos : ∀ᶠ x in l, 0 ≤ u x ∧ 0 ≤ w x) :
    (fun x => terminalSinglePhase h ![R, u x, w x] - (R - 2) / 2 -
      fderiv ℝ (terminalSinglePhase h) ![R, 0, 0] (![R, u x, w x] - ![R, 0, 0]))
      =o[l] (fun x => u x + w x) := by
  have HY : Tendsto (fun x => (![R, u x, w x] : ExitTailState)) l (𝓝 ![R, 0, 0]) := by
    apply tendsto_pi_nhds.mpr
    intro i
    fin_cases i
    · exact tendsto_const_nhds
    · exact hu
    · exact hw
  have H := terminalSinglePhase_boundary_differential hR hh
  have HT := ((H.2.1.differentiableAt (by norm_num)).hasFDerivAt.isLittleO).comp_tendsto HY
  have HO : (fun x => (![R, u x, w x] : ExitTailState) - ![R, 0, 0]) =O[l] (fun x => u x + w x) := by
    apply IsBigO.of_bound'
    filter_upwards [hpos] with x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg (add_nonneg hx.1 hx.2)] using
      exitTail_wall_offset_norm_le (R := R) hx.1 hx.2
  simpa only [Function.comp_def, H.1] using HT.trans_isBigO HO

/-- Fixed auxiliary heights describe the same actual arrival along every sufficiently small positive wall path. -/
theorem eventually_terminalConnectionState_boundary_height_eq {ι : Type*} {l : Filter ι}
    {u w : ι → ℝ} {α η₀ η₁ : ℝ} (hα : 0 < α ∧ α ≤ 1)
    (hη₀ : 0 < η₀) (hη₀₁ : η₀ ≤ η₁) (hη₁ : η₁ ≤ 1 / 40000)
    (hu : Tendsto u l (𝓝 0)) (hw : Tendsto w l (𝓝 0))
    (hpos : ∀ᶠ x in l, 0 < u x ∧ 0 < w x) :
    ∀ᶠ x in l,
      terminalConnectionState (η₁ * α ^ 2) ![2 + 2 * α, u x, w x] =
        terminalConnectionState (η₀ * α ^ 2) ![2 + 2 * α, u x, w x] := by
  obtain ⟨ε, hε, HE⟩ := exists_terminal_connection_uniform_height_independent
    (by norm_num : 0 < (1 / 10000 : ℝ) ∧ (1 / 10000 : ℝ) ≤ 1 / 10000)
    hη₀ hη₀₁ (by linarith only [hη₁] : η₁ ≤ 1 / 100) (q := 0) (J := 2)
    (by norm_num) (by norm_num; exact hη₁)
  have Hsmall := (hu.add hw).eventually (gt_mem_nhds
    (show (0 : ℝ) + 0 < ε * α ^ (2 * 2) by simpa using mul_pos hε (pow_pos hα.1 (2 * 2))))
  filter_upwards [hpos, Hsmall] with x hp hs
  exact (HE α (u x + w x) (u x) (w x) hα (add_pos hp.1 hp.2) hs.le
    (by rw [abs_of_pos hp.1, abs_of_pos hp.2]) hp.1 hp.2 η₁ ⟨hη₀₁, le_rfl⟩).2

end BianchiIX
