import BianchiIX.Analysis.PositiveConeTransport

noncomputable section

namespace BianchiIX

/-- Scalar phase distortion adds to the incoming radial distortion after positive normalization. -/
theorem positive_scalar_cone_transport (L : (Fin 3 → ℝ) →L[ℝ] ℝ)
    {w : Fin 3 → ℝ} {a : Fin 2 → ℝ} {B : ℝ} (hw0 : 0 < w 0)
    (hw : ∀ i : Fin 2, |w i.succ| ≤ a i * w 0)
    (H : ∀ z : Fin 3 → ℝ, z 0 = 1 → (∀ i : Fin 2, |z i.succ| ≤ a i) →
      0 < L z ∧ |Real.log (L z)| ≤ B) :
    0 < L w ∧ |Real.log (L w)| ≤ |Real.log (w 0)| + B := by
  let D : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) := ContinuousLinearMap.pi (fun _ => L)
  have HD : ∀ z : Fin 3 → ℝ, z 0 = 1 → (∀ i : Fin 2, |z i.succ| ≤ a i) →
      0 < D z 0 ∧ |Real.log (D z 0)| ≤ B ∧
        ∀ i : Fin 2, |D z i.succ| ≤ 1 * D z 0 := by
    intro z hz0 hz
    obtain ⟨hp, hl⟩ := H z hz0 hz
    exact ⟨hp, hl, fun _ => by change |L z| ≤ 1 * L z; rw [abs_of_pos hp, one_mul]⟩
  have HT := positive_cone_transport D hw0 hw HD
  exact ⟨HT.1, HT.2.1⟩

end BianchiIX
