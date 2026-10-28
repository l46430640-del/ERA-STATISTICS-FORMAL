import BianchiIX.Dynamics.ShearRestartPartialCoreEntry

noncomputable section

namespace BianchiIX

open Set

/-- Every positive active wall below one in the shear fast layer satisfies the ordinary entrance budget. -/
theorem exists_restartShearEntrance_inputs :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∀ η ∈ Ioc (0 : ℝ) (1 / 10000),
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
          ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
            (0 < n₂ ∧ n₂ ≤ 2 * ε * a) → (0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) →
            n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
              let s := q / 2 * Real.log (1 / a)
              let y := restartFastShearProjectiveEntry h s 1 n₂ n₃ ρ
              let k := restartFastShearCoreRadius h s 1 n₂ n₃ ρ
              y 2 < 1 →
              0 ≤ s ∧ 0 < restartSectionRadicand h (restartShearCurve 1 n₂ n₃ ρ) ∧
              s ∈ normalizedMaxDomain (restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)) 0 ∧
              0 < restartFastShearHeight h s 1 n₂ n₃ ρ ∧
              8 ≤ k ∧ 1 / (16 * a) ≤ k ∧ k ≤ 32 / a ∧ 1 < y 0 ∧
              (0 < y 1 ∧ y 1 ≤ 1 / 10000) ∧ (0 < y 2 ∧ y 2 < 1) ∧
              (0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) ∧ y 1 + y 2 * y 3 ≤ η / (2 * k) := by
  obtain ⟨hE, hhE, HE⟩ := exists_restartShearPartialCore_entry
  obtain ⟨hV, hhV, HV⟩ := exists_restartFastShearProjectiveEntry_bounds
  refine ⟨min hE hV, lt_min hhE hhV, ?_⟩
  intro h hh q P hq hP η hη
  have hηhalf : η / 2 ∈ Ioc (0 : ℝ) (1 / 10000) := ⟨by positivity [hη.1], by linarith only [hη.2]⟩
  obtain ⟨aE, haE, HaE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q P hq hP (η / 2) hηhalf
  obtain ⟨aV, haV, HaV⟩ := HV h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q (by linarith only [hq])
  refine ⟨min aE (min aV (1 / 512)), lt_min haE (lt_min haV (by norm_num)), ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s y k hv
  have haV' := ha.2.trans (min_le_right _ _)
  have ha512 : a ≤ 1 / 512 := haV'.trans (min_le_right _ _)
  have ha1 : a ≤ 1 := ha512.trans (by norm_num)
  obtain ⟨hs, hrad, hdom, hA, hm, _, hklo, hkhi, _, hu0, hp0, hsum, _⟩ :=
    HaE a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε ⟨h₂.1.le, h₂.2⟩ h₃ h₃P ρ hρ
  obtain ⟨_, _, _, _, _, _, _, _, hV, hW, _⟩ :=
    HaV a ⟨ha.1, haV'.trans (min_le_left _ _)⟩ ε 1 n₂ n₃ hε (by norm_num) ⟨h₂.1.le, h₂.2⟩ h₃ ρ hρ
  have hk8 : 8 ≤ k := (show 8 ≤ 1 / (16 * a) by
    apply (le_div_iff₀ (by positivity [ha.1])).mpr
    linarith only [ha512]).trans hklo
  have hsmall : y 1 + y 2 * y 3 ≤ η / (2 * k) := hsum.trans_eq (by ring)
  have hu : y 1 ≤ 1 / 10000 := ((le_add_of_nonneg_right hp0).trans hsmall).trans
    ((div_le_self hη.1.le (by linarith only [hk8])).trans hη.2)
  have hv0 : 0 < y 2 := (div_pos h₂.1 (by positivity [ha.1])).trans_le hV.1
  have hw0 : 0 ≤ y 3 := (div_nonneg h₃.1 (by positivity)).trans hW.1
  have hn₃ : n₃ ≤ a ^ (4 : ℕ) := h₃P.trans (by
    have H := Real.rpow_le_rpow_of_exponent_ge ha.1 ha1 hP.le
    rw [show a ^ (4 : ℝ) = a ^ (4 : ℕ) from Real.rpow_natCast a 4] at H
    exact H)
  have hw : y 3 ≤ 1 / 10000 := by
    calc
      _ ≤ 16 * n₃ / a ^ 2 := hW.2
      _ ≤ 16 * a ^ 4 / a ^ 2 := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hn₃ (by norm_num)) (sq_nonneg a)
      _ = 16 * a ^ 2 := by field_simp
      _ ≤ _ := by
        have H := pow_le_pow_left₀ ha.1.le ha512 2
        norm_num at H
        linarith only [H]
  exact ⟨hs, hrad, hdom, hA, hk8, hklo, hkhi, hm, ⟨hu0, hu⟩, ⟨hv0, hv⟩, ⟨hw0, hw⟩, hsmall⟩

end BianchiIX
