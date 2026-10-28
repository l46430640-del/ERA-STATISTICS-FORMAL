import BianchiIX.Analysis.PositiveConeTransport

noncomputable section

namespace BianchiIX

/-- Positive input normalization preserves a negative output phase and its transverse cone. -/
theorem negative_phase_cone_transport (L : (Fin 3 → ℝ) →L[ℝ] ℝ)
    (D : (Fin 3 → ℝ) →L[ℝ] (Fin 2 → ℝ)) {w : Fin 3 → ℝ} {a b : Fin 2 → ℝ}
    (hw0 : 0 < w 0) (hw : ∀ i : Fin 2, |w i.succ| ≤ a i * w 0)
    (H : ∀ z : Fin 3 → ℝ, z 0 = 1 → (∀ i : Fin 2, |z i.succ| ≤ a i) →
      L z < 0 ∧ ∀ i : Fin 2, |D z i| ≤ b i * |L z|) :
    L w < 0 ∧ ∀ i : Fin 2, |D w i| ≤ b i * |L w| := by
  let z := (w 0)⁻¹ • w
  have hz0 : z 0 = 1 := inv_mul_cancel₀ hw0.ne'
  have hz (i : Fin 2) : |z i.succ| ≤ a i := by
    change |(w 0)⁻¹ * w i.succ| ≤ a i
    rw [abs_mul, abs_of_pos (inv_pos.mpr hw0)]
    exact (mul_le_mul_of_nonneg_left (hw i) (inv_nonneg.mpr hw0.le)).trans_eq (by field_simp)
  obtain ⟨hp, hc⟩ := H z hz0 hz
  have hwz : w = w 0 • z := by
    dsimp only [z]
    rw [smul_smul, mul_inv_cancel₀ hw0.ne', one_smul]
  have hL : L w = w 0 * L z := by
    calc
      _ = L (w 0 • z) := congrArg L hwz
      _ = _ := by rw [map_smul]; rfl
  have hD (i : Fin 2) : D w i = w 0 * D z i := by
    calc
      _ = D (w 0 • z) i := congrArg (fun q => D q i) hwz
      _ = _ := by rw [map_smul]; rfl
  refine ⟨by rw [hL]; exact mul_neg_of_pos_of_neg hw0 hp, ?_⟩
  intro i
  rw [hL, hD, abs_mul, abs_mul, abs_of_pos hw0]
  exact (mul_le_mul_of_nonneg_left (hc i) hw0.le).trans_eq (by ring)

end BianchiIX
