import BianchiIX.Dynamics.TerminalWallFactorBounds

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- Integrating the ordinary logarithmic derivative along a fixed-radius amplitude segment. -/
theorem exists_terminalWallFactor_log_comparison {η₀ : ℝ} (hη₀ : 0 < η₀ ∧ η₀ ≤ 1 / 100)
    {J : ℕ} (hJ : 2 ≤ J) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ η α b u w : ℝ,
      η₀ ≤ η → η ≤ 1 / 100 → (0 < α ∧ α ≤ 1) →
      0 < b → b ≤ ε * α ^ (2 * J) → |u| + |w| ≤ b →
      let h := η * α ^ J
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let Y₀ : ExitTailState := ![2 + 2 * α, 0, 0]
      coreTailValid h Y ∧ ∀ i : Fin 2,
        0 < terminalWallFactor h Y i ∧ 0 < terminalWallFactor h Y₀ i ∧
          |Real.log (terminalWallFactor h Y i) - Real.log (terminalWallFactor h Y₀ i)| ≤ C * b / α := by
  obtain ⟨C, hC, ε, hε, HB⟩ := exists_terminalWallFactor_bounds_uniform hη₀ hJ
  refine ⟨C, hC, ε, hε, ?_⟩
  intro η α b u w hηlo hηhi hα hb hsmall hsum h Y Y₀
  let γ : ℝ → ExitTailState := fun t => ![2 + 2 * α, t * u, t * w]
  let v : ExitTailState := ![0, u, w]
  have hγ (t : ℝ) : HasDerivAt γ v t := by
    apply hasDerivAt_pi.mpr
    intro j
    fin_cases j
    · exact hasDerivAt_const t _
    · simpa [γ, v] using (hasDerivAt_id t).mul_const u
    · simpa [γ, v] using (hasDerivAt_id t).mul_const w
  have hsumt {t : ℝ} (ht : t ∈ Icc 0 1) : |t * u| + |t * w| ≤ b := by
    rw [abs_mul, abs_mul, abs_of_nonneg ht.1]
    calc
      _ = t * (|u| + |w|) := by ring
      _ ≤ 1 * (|u| + |w|) := mul_le_mul_of_nonneg_right ht.2 (by positivity)
      _ ≤ b := by simpa using hsum
  have hv : ‖v‖ ≤ b := by
    apply (pi_norm_le_iff_of_nonneg hb.le).mpr
    intro j
    fin_cases j
    · simpa [v] using hb.le
    · change |u| ≤ b
      linarith only [hsum, abs_nonneg w]
    · change |w| ≤ b
      linarith only [hsum, abs_nonneg u]
  have HT (t : ℝ) (ht : t ∈ Icc 0 1) :=
    HB η α b (t * u) (t * w) hηlo hηhi hα hb hsmall (hsumt ht)
  have H1 := HB η α b u w hηlo hηhi hα hb hsmall hsum
  have H0 := HB η α b 0 0 hηlo hηhi hα hb hsmall (by simpa using hb.le)
  refine ⟨H1.1, fun i => ⟨(H1.2.2.2.2.2 i).1, (H0.2.2.2.2.2 i).1, ?_⟩⟩
  let F := fun Z => Real.log (terminalWallFactor h Z i)
  have hd (t : ℝ) (ht : t ∈ Icc 0 1) :
      HasDerivAt (fun s => F (γ s)) (fderiv ℝ F (γ t) v) t := by
    have HF := (((HT t ht).2.2.2.2.2 i).2.2.1.differentiableAt (by norm_num)).hasFDerivAt
    exact HF.comp_hasDerivAt t (hγ t)
  have hbound (t : ℝ) (ht : t ∈ Icc 0 1) : ‖fderiv ℝ F (γ t) v‖ ≤ (C / α) * b := by
    have HF : ‖fderiv ℝ F (γ t)‖ ≤ C / α := ((HT t ht).2.2.2.2.2 i).2.2.2.2.2
    exact (ContinuousLinearMap.le_opNorm _ v).trans
      (mul_le_mul HF hv (norm_nonneg v) (div_nonneg (by linarith only [hC]) hα.1.le))
  have HE := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hd t ht).hasDerivWithinAt) hbound
    (by norm_num : (0 : ℝ) ∈ Icc 0 1) (by norm_num : (1 : ℝ) ∈ Icc 0 1)
  simpa [F, γ, Y, Y₀, Real.norm_eq_abs, div_mul_eq_mul_div] using HE

end BianchiIX
