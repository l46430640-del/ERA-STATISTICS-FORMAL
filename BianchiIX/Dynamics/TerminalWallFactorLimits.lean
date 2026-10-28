import BianchiIX.Dynamics.TerminalWallFactorComparison
import BianchiIX.Dynamics.TerminalReferenceFactors

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The reference asymptotics persist along every wall path in the terminal amplitude budget. -/
theorem exists_terminalWallFactor_limits {η : ℝ} (hη : 0 < η ∧ η ≤ 1 / 100)
    {J : ℕ} (hJ : 2 ≤ J) :
    ∃ ε > (0 : ℝ), ∀ u w : ℝ → ℝ,
      (∀ᶠ α : ℝ in 𝓝[>] 0, |u α| + |w α| ≤ ε * α ^ (2 * J)) →
      ∀ i : Fin 2,
        Tendsto (fun α : ℝ => terminalWallFactor (η * α ^ J) ![2 + 2 * α, u α, w α] i /
          terminalWallFactor (η * α ^ J) ![2 + 2 * α, 0, 0] i) (𝓝[>] 0) (𝓝 1) ∧
        Tendsto (fun α : ℝ => α ^ 2 * terminalWallFactor (η * α ^ J) ![2 + 2 * α, u α, w α] i)
          (𝓝[>] 0) (𝓝 taubMultiplierConstant) := by
  obtain ⟨C, hC, ε, hε, HB⟩ := exists_terminalWallFactor_log_comparison hη hJ
  refine ⟨ε, hε, ?_⟩
  intro u w hsum i
  let B := fun α => terminalWallFactor (η * α ^ J) ![2 + 2 * α, u α, w α] i
  let B₀ := fun α => terminalWallFactor (η * α ^ J) ![2 + 2 * α, 0, 0] i
  have hgood : ∀ᶠ α : ℝ in 𝓝[>] 0,
      0 < B α ∧ 0 < B₀ α ∧ |Real.log (B α) - Real.log (B₀ α)| ≤ C * (ε * α ^ (2 * J)) / α := by
    filter_upwards [hsum, show ∀ᶠ α : ℝ in 𝓝[>] 0, 0 < α from self_mem_nhdsWithin,
      show ∀ᶠ α : ℝ in 𝓝[>] 0, α < 1 from
        mem_nhdsWithin_of_mem_nhds (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with α hsumα hα hα1
    exact (HB η α (ε * α ^ (2 * J)) (u α) (w α) le_rfl hη.2 ⟨hα, hα1.le⟩
      (mul_pos hε (pow_pos hα _)) le_rfl hsumα).2 i
  have HG : Tendsto (fun α : ℝ => C * (ε * α ^ (2 * J)) / α) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_div_assoc, mul_zero] using
      (tendsto_terminal_height_div_phase ε (show 2 ≤ 2 * J by omega)).const_mul C
  have HD : Tendsto (fun α : ℝ => Real.log (B α) - Real.log (B₀ α)) (𝓝[>] 0) (𝓝 0) :=
    squeeze_zero_norm' (hgood.mono fun α ha => by simpa only [Real.norm_eq_abs] using ha.2.2) HG
  have HR : Tendsto (fun α : ℝ => B α / B₀ α) (𝓝[>] 0) (𝓝 1) := by
    have HE := Real.continuous_exp.continuousAt.tendsto.comp HD
    simp only [Real.exp_zero] at HE
    apply HE.congr'
    filter_upwards [hgood] with α ha
    exact (Real.exp_sub _ _).trans (by rw [Real.exp_log ha.1, Real.exp_log ha.2.1])
  refine ⟨HR, ?_⟩
  have HT := HR.mul (tendsto_terminal_reference_wallFactor hη.1 hJ i)
  simp only [one_mul] at HT
  apply HT.congr'
  filter_upwards [hgood] with α ha
  change B α / B₀ α * (α ^ 2 * B₀ α) = α ^ 2 * B α
  field_simp [ha.2.1.ne']

end BianchiIX
