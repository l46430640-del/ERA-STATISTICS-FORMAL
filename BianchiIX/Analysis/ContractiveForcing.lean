import BianchiIX.Analysis.ForcedRowGrowth

noncomputable section

namespace BianchiIX

open Set

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem norm_le_exp_of_faster_forcing {f q : ℝ → (ι → ℝ)}
    {A : ℝ → Matrix ι ι ℝ} {ρ Q T : ℝ} (hρ : 0 < ρ) (hQ : 0 ≤ Q)
    (hf : ∀ t ∈ Icc 0 T, HasDerivAt f ((A t).mulVec (f t) + q t) t)
    (hA : ∀ t ∈ Icc 0 T, ∀ i, signedRowSum (A t) i ≤ -ρ)
    (hq : ∀ t ∈ Icc 0 T, ‖q t‖ ≤ Q * Real.exp (-2 * ρ * t)) :
    ∀ t ∈ Icc 0 T, ‖f t‖ ≤ (‖f 0‖ + Q / ρ) * Real.exp (-ρ * t) := by
  let g := fun t => Real.exp (ρ * t) • f t
  let M := fun t => A t - (-ρ) • (1 : Matrix ι ι ℝ)
  let c := fun t => Real.exp (ρ * t) • q t
  let B := fun t => ‖f 0‖ + Q / ρ * (1 - Real.exp (-ρ * t))
  have hg (t : ℝ) (ht : t ∈ Icc 0 T) : HasDerivAt g ((M t).mulVec (g t) + c t) t := by
    convert! (((hasDerivAt_id t).const_mul ρ).exp).smul (hf t ht) using 1
    dsimp [M, g, c]
    rw [Matrix.mulVec_smul, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    ext i
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hM (t : ℝ) (ht : t ∈ Ico 0 T) (i : ι) : signedRowSum (M t) i ≤ 0 := by
    dsimp [M]
    rw [signedRowSum_sub_scalar]
    linarith only [hA t (Ico_subset_Icc_self ht) i]
  have hB (t : ℝ) : HasDerivAt B (Q * Real.exp (-ρ * t)) t := by
    convert! (((hasDerivAt_const t (1 : ℝ)).sub
      (((hasDerivAt_id t).const_mul (-ρ)).exp)).const_mul (Q / ρ)).const_add ‖f 0‖ using 1
    dsimp
    field_simp
    ring
  have hc (t : ℝ) (ht : t ∈ Icc 0 T) : ‖c t‖ ≤ Q * Real.exp (-ρ * t) := by
    simp only [c, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (ρ * t) * (Q * Real.exp (-2 * ρ * t)) :=
        mul_le_mul_of_nonneg_left (hq t ht) (Real.exp_pos _).le
      _ = Q * (Real.exp (ρ * t) * Real.exp (-2 * ρ * t)) := by ring
      _ = Q * Real.exp (-ρ * t) := by rw [← Real.exp_add]; congr 2; ring
  have H := norm_le_of_forced_signedRowSum_nonpos (HasDerivAt.continuousOn hg)
    (fun t ht => hg t (Ico_subset_Icc_self ht)) hM
    (HasDerivAt.continuousOn (fun t _ => hB t)) (fun t _ => hB t)
    (by simp [g, B]) (fun t ht => hc t (Ico_subset_Icc_self ht))
  intro t ht
  have H' := H t ht
  simp only [g, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at H'
  have hBt : B t ≤ ‖f 0‖ + Q / ρ := by
    dsimp [B]
    have hn : 0 ≤ Q / ρ := div_nonneg hQ hρ.le
    nlinarith [Real.exp_pos (-ρ * t)]
  calc
    ‖f t‖ = Real.exp (-ρ * t) * (Real.exp (ρ * t) * ‖f t‖) := by
      rw [← mul_assoc, ← Real.exp_add]
      have he : -ρ * t + ρ * t = 0 := by ring
      rw [he, Real.exp_zero, one_mul]
    _ ≤ Real.exp (-ρ * t) * (‖f 0‖ + Q / ρ) :=
      mul_le_mul_of_nonneg_left (H'.trans hBt) (Real.exp_pos _).le
    _ = _ := by ring

end BianchiIX
