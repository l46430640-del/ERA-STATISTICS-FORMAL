import BianchiIX.Analysis.ShearTailEntranceScale

noncomputable section

namespace BianchiIX

open Set

/-- The square-root wall budget absorbs the tail's logarithmic loss. -/
theorem exists_shearTail_sqrt_wall_scale {h q D δ : ℝ}
    (hh : 0 ≤ h) (hq : 2 < q) (hD : 2 < D) (hδ : 0 < δ) :
    ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
      a ≤ 1 ∧ (1 + |Real.log a|) *
        Real.sqrt (20 * h * a ^ (q - 2) + 80 * a ^ (D / 2 - 1)) ≤ δ := by
  obtain ⟨astar, hastar, HA⟩ := exists_shearTail_entrance_wall_scale
    (h := (20 * h + 1) / 20) (q := q / 2 + 1) (D := D / 2 + 1)
    (by linarith only [hq]) (by linarith only [hD]) hδ
  refine ⟨astar, hastar, ?_⟩
  intro a ha
  obtain ⟨ha1, H⟩ := HA a ha
  let x := a ^ (q / 2 - 1)
  let y := a ^ (D / 4 - 1 / 2)
  have hx : 0 ≤ x := Real.rpow_nonneg ha.1.le _
  have hy : 0 ≤ y := Real.rpow_nonneg ha.1.le _
  have hx2 : x ^ 2 = a ^ (q - 2) := by
    dsimp only [x]
    rw [sq, ← Real.rpow_add ha.1]
    congr 1
    ring
  have hy2 : y ^ 2 = a ^ (D / 2 - 1) := by
    dsimp only [y]
    rw [sq, ← Real.rpow_add ha.1]
    congr 1
    ring
  have Hroot : Real.sqrt (20 * h * a ^ (q - 2) + 80 * a ^ (D / 2 - 1)) ≤
      (20 * h + 1) * x + 80 * y := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [← hx2, ← hy2]
    have Hc : 20 * h ≤ (20 * h + 1) ^ 2 := by nlinarith only [hh, sq_nonneg (20 * h)]
    nlinarith only [mul_le_mul_of_nonneg_right Hc (sq_nonneg x), sq_nonneg y,
      mul_nonneg (mul_nonneg (by positivity : 0 ≤ 20 * h + 1) hx) hy]
  have Heq₁ : q / 2 + 1 - 2 = q / 2 - 1 := by ring
  have Heq₂ : (D / 2 + 1) / 2 - 1 = D / 4 - 1 / 2 := by ring
  rw [Heq₁, Heq₂] at H
  have Hcoef : 20 * ((20 * h + 1) / 20) = 20 * h + 1 := by ring
  rw [Hcoef] at H
  exact ⟨ha1, (mul_le_mul_of_nonneg_left Hroot (by positivity)).trans (by simpa only [mul_comm] using H)⟩

/-- A wall budget of order smaller than a is sufficient for the subsequent core. -/
theorem exists_shearTail_core_wall_scale {h q D η : ℝ}
    (hh : 0 ≤ h) (hq : 3 < q) (hD : 4 < D) (hη : 0 < η) :
    ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
      a ≤ 1 ∧ 20 * h * a ^ (q - 2) + 80 * a ^ (D / 2 - 1) ≤ η * a / 128 := by
  obtain ⟨astar, hastar, HA⟩ := exists_shearTail_entrance_wall_scale
    (h := h) (q := q - 1) (D := D - 2)
    (by linarith only [hq]) (by linarith only [hD]) (by positivity : 0 < η / 128)
  refine ⟨astar, hastar, ?_⟩
  intro a ha
  obtain ⟨ha1, H⟩ := HA a ha
  let b := 20 * h * a ^ (q - 1 - 2) + 80 * a ^ ((D - 2) / 2 - 1)
  have hb : 0 ≤ b := by dsimp only [b]; positivity [ha.1]
  have Hb : b ≤ η / 128 := by
    have Hmul := mul_le_mul_of_nonneg_left
      (show 1 ≤ 1 + |Real.log a| by linarith only [abs_nonneg (Real.log a)]) hb
    change b * (1 + |Real.log a|) ≤ η / 128 at H
    linarith only [H, Hmul]
  have Heq : b * a = 20 * h * a ^ (q - 2) + 80 * a ^ (D / 2 - 1) := by
    dsimp only [b]
    calc
      _ = 20 * h * (a ^ (q - 1 - 2) * a) + 80 * (a ^ ((D - 2) / 2 - 1) * a) := by ring
      _ = _ := by
        rw [← Real.rpow_add_one ha.1.ne', ← Real.rpow_add_one ha.1.ne']
        rw [show q - 1 - 2 + 1 = q - 2 by ring,
          show (D - 2) / 2 - 1 + 1 = D / 2 - 1 by ring]
  exact ⟨ha1, Heq ▸ (mul_le_mul_of_nonneg_right Hb ha.1.le).trans_eq (by ring)⟩

end BianchiIX
