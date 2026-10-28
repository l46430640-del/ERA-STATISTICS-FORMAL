import BianchiIX.Dynamics.CoreReflectionPaidStep
import BianchiIX.Dynamics.TaubAvoidance

noncomputable section

namespace BianchiIX

/-- Finite actual prefixes exclude every positive even integer, with a length-independent error budget. -/
theorem exists_core_even_separation :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 10000 ∧ ∃ C ≥ (1 : ℝ),
      ∀ ε > (0 : ℝ), ∃ ρ > (0 : ℝ), ρ ≤ 1 / 16 ∧ ∀ Y : CoreAngleState,
        0 < Y 1 → 0 < Y 2 → Y 1 + Y 2 ≤ δ / (1 + Y 0) → C * (Y 1 + Y 2) ≤ ρ / 4 →
        normalizedTaubAvoidance ε (fromProjectiveState (coreRadiusEntry Y)) →
        ∀ n : ℕ, 1 ≤ n → ρ / 2 < |Y 0 - 2 * n| := by
  obtain ⟨δ, hδ, hδmax, C, hC, Hstep⟩ := exists_coreReflection_paid_step
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  refine ⟨δ, hδ, hδmax, C, hC, ?_⟩
  intro ε hε
  obtain ⟨ρ, hρ, hρmax, Hsep⟩ := exists_core_radius_separation_of_away hε
  refine ⟨ρ, hρ, hρmax, ?_⟩
  intro Y hu hw hbudget hsmall haway n hn
  by_contra! hnear
  let G := coreReflectionState coreRadiusReturnTime
  let Z : ℕ → CoreAngleState := fun j => G^[j] Y
  let b : ℕ → ℝ := fun j => Z j 1 + Z j 2
  have hZ0 : Z 0 = Y := rfl
  have hZnext (j : ℕ) : Z (j + 1) = G (Z j) := Function.iterate_succ_apply' G j Y
  have hb0 : 0 < b 0 := add_pos hu hw
  have hsmall' : C * b 0 ≤ ρ / 4 := hsmall
  have hprefix : ∀ j, j ≤ n - 1 →
      (0 < Z j 1 ∧ 0 < Z j 2) ∧ b j ≤ b 0 ∧ Z j 0 ≤ Y 0 ∧
      |Z j 0 - (Y 0 - 2 * j)| ≤ C * (b 0 - b j) ∧
      normalizedTaubAvoidance ε (fromProjectiveState (coreRadiusEntry (Z j))) := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨⟨hu, hw⟩, le_rfl, le_rfl, ?_, haway⟩
      simp only [hZ0, Nat.cast_zero, mul_zero, sub_zero, sub_self, abs_zero, le_refl]
    | succ j ih =>
      intro hj
      obtain ⟨hpos, hb, hk, herr, ha⟩ := ih (by omega)
      have hbj : 0 ≤ b j := add_nonneg hpos.1.le hpos.2.le
      have hpaid : C * (b 0 - b j) ≤ ρ / 4 :=
        (mul_le_mul_of_nonneg_left (sub_le_self _ hbj) hC0).trans hsmall'
      have hnj : (j : ℝ) + 2 ≤ n := by exact_mod_cast (show j + 2 ≤ n by omega)
      have hguard : 63 / 16 ≤ Z j 0 := by
        have H1 := (abs_le.mp hnear).1
        have H2 := (abs_le.mp (herr.trans hpaid)).1
        linarith only [H1, H2, hnj, hρmax]
      have hentry : b j ≤ δ / (1 + Z j 0) :=
        (hb.trans hbudget).trans (div_le_div_of_nonneg_left hδ.le
          (by linarith only [hguard] : 0 < 1 + Z j 0) (by linarith only [hk]))
      obtain ⟨hcore, hT, horbit, hdrop, hwall, hphase⟩ := Hstep (Z j) hguard hpos.1 hpos.2 hentry
      have hbn : b (j + 1) ≤ b j := by
        change Z (j + 1) 1 + Z (j + 1) 2 ≤ _
        rw [hZnext]
        exact add_le_add (hwall 0).2 (hwall 1).2
      have hphase' : |Z (j + 1) 0 - (Z j 0 - 2)| ≤ C * (b j - b (j + 1)) := by
        simpa only [b, hZnext, G] using hphase
      have herror : |Z (j + 1) 0 - (Y 0 - 2 * (j + 1 : ℕ))| ≤ C * (b 0 - b (j + 1)) := by
        have heq : Z (j + 1) 0 - (Y 0 - 2 * (j + 1 : ℕ)) =
            (Z (j + 1) 0 - (Z j 0 - 2)) + (Z j 0 - (Y 0 - 2 * j)) := by
          push_cast
          ring
        rw [heq]
        exact ((abs_add_le _ _).trans (add_le_add hphase' herr)).trans_eq (by ring)
      refine ⟨?_, hbn.trans hb, ?_, herror, ?_⟩
      · rw [hZnext]
        exact ⟨(hwall 0).1, (hwall 1).1⟩
      · rw [hZnext]
        linarith only [hdrop.1, hk]
      · rw [hZnext]
        exact ha.coreReflection hcore hT horbit
  let m := n - 1
  obtain ⟨hpos, hb, _, herr, ha⟩ := hprefix m le_rfl
  have hm : (m : ℝ) + 1 = n := by exact_mod_cast (show m + 1 = n by dsimp [m]; omega)
  have hbm : 0 ≤ b m := add_nonneg hpos.1.le hpos.2.le
  have hpaid : C * (b 0 - b m) ≤ ρ / 4 :=
    (mul_le_mul_of_nonneg_left (sub_le_self _ hbm) hC0).trans hsmall'
  have hterminal : |Z m 0 - 2| ≤ ρ := by
    have H1 := abs_le.mp hnear
    have H2 := abs_le.mp (herr.trans hpaid)
    apply abs_le.mpr
    constructor <;> linarith only [H1.1, H1.2, H2.1, H2.2, hm, hρ]
  have hbr : b m ≤ ρ := by
    have H := mul_le_mul_of_nonneg_right hC hb0.le
    nlinarith only [H, hsmall', hb, hρ]
  have hu' : |Z m 1| ≤ ρ := by
    rw [abs_of_pos hpos.1]
    change Z m 1 + Z m 2 ≤ ρ at hbr
    linarith only [hbr, hpos.2]
  have hw' : |Z m 2| ≤ ρ := by
    rw [abs_of_pos hpos.2]
    change Z m 1 + Z m 2 ≤ ρ at hbr
    linarith only [hbr, hpos.1]
  have H := Hsep (Z m) hu' hw' (fun T hT hdom => ha T hT.le hdom 1)
  exact (not_lt_of_ge hterminal) H

end BianchiIX
