import BianchiIX.Algebra.EntranceWallCone

noncomputable section

namespace BianchiIX

/-- Dividing the entrance response by the actual radius slope retains the active-wall factor. -/
theorem entrance_wall_radius_cone {C B k K J a R u v w U W dU dW : ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hk : 1 ≤ k) (hJ : 0 < J) (ha : 0 < a)
    (hkhi : k ≤ K / a) (hR : 1 / (J * a ^ 2) ≤ R)
    (HU : |dU| ≤ C * B * k ^ 2 * Real.sqrt (u * v) * Real.sqrt U)
    (HW : |dW| ≤ C * B * k * Real.sqrt (w * v) * Real.sqrt W) :
    |dU| ≤ (J * K ^ 2 * C * B) * Real.sqrt (u * v) * Real.sqrt U * R ∧
    |dW| ≤ (J * K ^ 2 * C * B) * Real.sqrt (w * v) * Real.sqrt W * R := by
  have hk0 : 0 ≤ k := by linarith only [hk]
  have Hratio : k ^ 2 ≤ J * K ^ 2 * R := by
    calc
      _ ≤ (K / a) ^ 2 := pow_le_pow_left₀ hk0 hkhi 2
      _ = J * K ^ 2 * (1 / (J * a ^ 2)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hR (by positivity)
  have Hwall {b z dz : ℝ} (H : |dz| ≤ C * B * k ^ 2 * Real.sqrt b * Real.sqrt z) :
      |dz| ≤ (J * K ^ 2 * C * B) * Real.sqrt b * Real.sqrt z * R := by
    calc
      _ ≤ C * B * k ^ 2 * Real.sqrt b * Real.sqrt z := H
      _ ≤ C * B * (J * K ^ 2 * R) * Real.sqrt b * Real.sqrt z := by gcongr
      _ = _ := by ring
  refine ⟨Hwall HU, Hwall (HW.trans ?_)⟩
  gcongr
  nlinarith only [mul_le_mul_of_nonneg_left hk hk0]

end BianchiIX
