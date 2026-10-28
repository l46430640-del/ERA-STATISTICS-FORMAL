import BianchiIX.Dynamics.ShearRestartEntranceInputs
import BianchiIX.Dynamics.ShearRestartProjectiveResponse

noncomputable section

namespace BianchiIX

open Set

/-- One common shear threshold supplies arbitrarily small entrance walls and all relative radial derivatives. -/
theorem exists_restartShearEntrance_differential_inputs :
    ∃ hstar > (0 : ℝ), ∃ D > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∀ δ ∈ Ioc (0 : ℝ) (1 / 10000),
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
          ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
            (0 < n₂ ∧ n₂ ≤ 2 * ε * a) → (0 < n₃ ∧ n₃ ≤ 2 * ε * a) →
            n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
              let s := q / 2 * Real.log (1 / a)
              let Y := restartFastShearProjectiveEntry h s 1 n₂ n₃
              let k := coreRadius (Y ρ 0) (Y ρ 2)
              Y ρ 2 < 1 → DifferentiableAt ℝ Y ρ ∧
              8 ≤ k ∧ 1 / (16 * a) ≤ k ∧ k ≤ 32 / a ∧ 1 < Y ρ 0 ∧
              (0 < Y ρ 1 ∧ Y ρ 1 ≤ δ) ∧ (0 < Y ρ 2 ∧ Y ρ 2 < 1) ∧ (0 < Y ρ 3 ∧ Y ρ 3 ≤ δ) ∧
              Y ρ 1 + Y ρ 2 * Y ρ 3 ≤ δ / (2 * k) ∧
              |deriv (fun t => Y t 0) ρ| ≤ D * k ^ 2 ∧
              ∀ i : Fin 4, i ≠ 0 → |deriv (fun t => Y t i) ρ| ≤ D * k * Y ρ i := by
  obtain ⟨hE, hhE, HE⟩ := exists_restartShearEntrance_inputs
  obtain ⟨hR, hhR, K, hK, HR⟩ := exists_restartFastShearProjectiveEntry_response
  obtain ⟨hV, hhV, HV⟩ := exists_restartFastShearProjectiveEntry_bounds
  let D := 256 * K
  refine ⟨min hE (min hR hV), lt_min hhE (lt_min hhR hhV), D, by dsimp only [D]; positivity, ?_⟩
  intro h hh q P hq hP δ hδ
  have hh' := hh.2.trans (min_le_right _ _)
  obtain ⟨aE, haE, HaE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q P hq hP δ hδ
  obtain ⟨aR, haR, HaR⟩ := HR h ⟨hh.1, hh'.trans (min_le_left _ _)⟩ q (by linarith only [hq])
  obtain ⟨aV, haV, HaV⟩ := HV h ⟨hh.1, hh'.trans (min_le_right _ _)⟩ q (by linarith only [hq])
  refine ⟨min aE (min aR (min aV (min 1 (δ / 16)))),
    lt_min haE (lt_min haR (lt_min haV (lt_min zero_lt_one (by positivity [hδ.1])))), ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s Y k hv
  have ha' := ha.2.trans (min_le_right _ _)
  have ha'' := ha'.trans (min_le_right _ _)
  have hasmall := ha''.trans (min_le_right _ _)
  have ha1 : a ≤ 1 := hasmall.trans (min_le_left _ _)
  have haδ : a ≤ δ / 16 := hasmall.trans (min_le_right _ _)
  obtain ⟨_, _, _, _, hk8, hklo, hkhi, hm, hu, hv', hw, hsum⟩ :=
    HaE a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ ⟨h₃.1.le, h₃.2⟩ h₃P ρ hρ hv
  obtain ⟨_, HY, HM, Hwall, _⟩ := HaR a ⟨ha.1, ha'.trans (min_le_left _ _)⟩ ε 1 n₂ n₃ hε
    (by norm_num) ⟨h₂.1.le, h₂.2⟩ ⟨h₃.1.le, h₃.2⟩ ρ hρ
  obtain ⟨_, _, _, _, _, _, _, _, _, HW, _⟩ := HaV a ⟨ha.1, ha''.trans (min_le_left _ _)⟩
    ε 1 n₂ n₃ hε (by norm_num) ⟨h₂.1.le, h₂.2⟩ ⟨h₃.1.le, h₃.2⟩ ρ hρ
  change 8 ≤ k at hk8
  change 1 / (16 * a) ≤ k at hklo
  change k ≤ 32 / a at hkhi
  change 0 < Y ρ 2 ∧ Y ρ 2 < 1 at hv'
  change 0 ≤ Y ρ 3 ∧ Y ρ 3 ≤ 1 / 10000 at hw
  change Y ρ 1 + Y ρ 2 * Y ρ 3 ≤ δ / (2 * k) at hsum
  have hkpos : 0 < k := by linarith only [hk8]
  have hUδ : Y ρ 1 ≤ δ := ((le_add_of_nonneg_right (mul_nonneg hv'.1.le hw.1)).trans hsum).trans
    (div_le_self hδ.1.le (by linarith only [hk8]))
  have hWpos : 0 < Y ρ 3 := (div_pos h₃.1 (by positivity [ha.1])).trans_le HW.1
  have hn₃ : n₃ ≤ a ^ (4 : ℕ) := h₃P.trans (by
    have H := Real.rpow_le_rpow_of_exponent_ge ha.1 ha1 hP.le
    rw [show a ^ (4 : ℝ) = a ^ (4 : ℕ) from Real.rpow_natCast a 4] at H
    exact H)
  have hWδ : Y ρ 3 ≤ δ := by
    calc
      _ ≤ 16 * n₃ / a ^ 2 := HW.2
      _ ≤ 16 * a ^ 4 / a ^ 2 := by gcongr
      _ = 16 * a ^ 2 := by field_simp
      _ ≤ 16 * a := by nlinarith only [mul_le_mul_of_nonneg_left ha1 ha.1.le]
      _ ≤ δ := by linarith only [(le_div_iff₀ (by norm_num : (0 : ℝ) < 16)).mp haδ]
  have hki : 1 / a ≤ 16 * k := by
    calc
      _ = 16 * (1 / (16 * a)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hklo (by norm_num)
  have Hd0 : |deriv (fun t => Y t 0) ρ| ≤ D * k ^ 2 := HM.trans (by
    calc
      _ = K * (1 / a) ^ 2 := by ring
      _ ≤ K * (16 * k) ^ 2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity [ha.1]) hki 2) hK.le
      _ = _ := by dsimp only [D]; ring)
  have HDwall (i : Fin 3) : |deriv (fun t => Y t i.succ) ρ| ≤ D * k * Y ρ i.succ := by
    calc
      _ ≤ K * Y ρ i.succ / a := (Hwall i).2.1
      _ = (K * Y ρ i.succ) * (1 / a) := by ring
      _ ≤ (K * Y ρ i.succ) * (16 * k) :=
        mul_le_mul_of_nonneg_left hki (mul_nonneg hK.le (Hwall i).1)
      _ ≤ _ := by dsimp only [D]; nlinarith only [mul_nonneg (mul_nonneg hK.le hkpos.le) (Hwall i).1]
  refine ⟨HY, hk8, hklo, hkhi, hm, ⟨hu.1, hUδ⟩, hv', ⟨hWpos, hWδ⟩, hsum, Hd0, ?_⟩
  intro i hi
  fin_cases i
  · exact (hi rfl).elim
  · exact HDwall 0
  · exact HDwall 1
  · exact HDwall 2

end BianchiIX
