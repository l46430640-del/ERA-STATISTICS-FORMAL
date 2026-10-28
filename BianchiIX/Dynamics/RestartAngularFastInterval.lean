import BianchiIX.Dynamics.RestartFastInterval
import BianchiIX.Dynamics.RestartProjectiveEntryBounds

noncomputable section

namespace BianchiIX

open Set

/-- The whole interval between fast cutoffs stays above the active section in every bounded angular region. -/
theorem exists_restartAngular_fast_interval :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∀ q₀ q₁ : ℝ, 2 < q₀ → q₀ ≤ q₁ →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ θ ζ : ℝ,
          |θ| ≤ L → (0 ≤ ζ ∧ ζ ≤ a ^ 2) → ∀ ρ ∈ Icc a (2 * a),
          let T₀ := q₀ / 2 * Real.log (1 / a)
          let T₁ := q₁ / 2 * Real.log (1 / a)
          let z := restartSectionChart h (restartRadialCurve θ ζ ρ)
          0 ≤ T₀ ∧ T₀ ≤ T₁ ∧ 0 < restartSectionRadicand h (restartRadialCurve θ ζ ρ) ∧
          ∀ t ∈ Icc T₀ T₁, t ∈ normalizedMaxDomain z 0 ∧
            0 < 1 + normalizedMaxCurve z 0 t 0 ∧
            2 ≤ toProjectiveState (normalizedMaxCurve z 0 t) 2 := by
  obtain ⟨C, hC, HC⟩ := exists_restartSection_fast_interval
  have hCp : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 32) hC
  refine ⟨min (1 / (4 * C)) 1, lt_min (by positivity) zero_lt_one, ?_⟩
  intro h hh L hL q₀ q₁ hq₀ hq
  let M := 4 * (L + 1)
  have hM : 0 < M := by dsimp only [M]; positivity
  have hM1 : 1 ≤ M := by dsimp only [M]; linarith only [hL]
  obtain ⟨aI, haI, HI⟩ := HC h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩
    (2 * (L + 1)) (by positivity) q₀ q₁ hq₀ hq
  refine ⟨min aI (min (1 / (16 * M)) (1 / (40 * M ^ 2))),
    lt_min haI (lt_min (by positivity) (by positivity)), ?_⟩
  intro a ha θ ζ hθ hζ ρ hρ T₀ T₁ z
  obtain ⟨hasmall, hT₀, hTT, HZ⟩ := HI a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩
  have hMa : M * a ≤ 1 / 16 := by
    have H := (le_div_iff₀ (by positivity : 0 < 16 * M)).mp
      (ha.2.trans ((min_le_right _ _).trans (min_le_left _ _)))
    nlinarith only [H]
  have hMsa : 40 * M ^ 2 * a ≤ 1 := by
    have H := (le_div_iff₀ (by positivity : 0 < 40 * M ^ 2)).mp
      (ha.2.trans ((min_le_right _ _).trans (min_le_right _ _)))
    nlinarith only [H]
  let Z := restartRadialCurve θ ζ ρ
  have hζ' : 0 ≤ ζ ∧ ζ ≤ a / 9 := ⟨hζ.1, hζ.2.trans (by nlinarith only [hasmall, ha.1])⟩
  have hZ : ‖Z‖ ≤ (2 * (L + 1)) * a := (restartRadialCurve_annulus ha.1 hρ hL hθ hζ').1
  obtain ⟨hrad, HT⟩ := HZ Z hZ
  have ha1 : a ≤ 1 := by linarith only [hasmall]
  have Hpower : a ^ q₀ ≤ a ^ (2 : ℕ) := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_ge ha.1 ha1 hq₀.le
  refine ⟨hT₀, hTT, hrad, ?_⟩
  intro t ht
  let x := normalizedMaxCurve z 0 t
  let p := restartSectionRadialState h t Z
  obtain ⟨hdom, hc, hneg, hn, hcenter, _, _, HW⟩ := HT t ht
  change stateConstraint x = 1 at hc
  change x 0 ≤ -(15 / 16) at hneg
  have hnsmall : x 2 ≤ a ^ 2 := hn.2.trans
    ((mul_le_mul_of_nonneg_left Hpower hh.1.le).trans
      (mul_le_of_le_one_left (sq_nonneg a) (hh.2.trans (min_le_right _ _))))
  have Hactive : a / 2 ≤ x 3 := (div_le_div_of_nonneg_right hρ.1 (by norm_num)).trans (HW 0 (ha.1.le.trans hρ.1)).1
  have Hweak : 0 ≤ x 4 ∧ x 4 ≤ 2 * a ^ 2 := by
    have H := HW 1 hζ.1
    exact ⟨(div_nonneg hζ.1 (by norm_num)).trans H.1,
      H.2.trans (mul_le_mul_of_nonneg_left hζ.2 (by norm_num))⟩
  have Hp : ‖p‖ ≤ M * a := by
    rw [Prod.norm_def, max_le_iff, Real.norm_eq_abs, abs_of_pos (show 0 < p.1 from hn.1)]
    refine ⟨hnsmall.trans ?_, ?_⟩
    · nlinarith only [hasmall, ha.1, mul_le_mul_of_nonneg_right hM1 ha.1.le]
    · exact hcenter.le.trans_eq (by dsimp only [M]; ring)
  have Hn : 0 ≤ p.1 ∧ p.1 ≤ p.2 1 / 16 := ⟨hn.1.le, by
    change x 2 ≤ x 3 / 16
    nlinarith only [hnsmall, Hactive, mul_le_mul_of_nonneg_right hasmall ha.1.le]⟩
  have Hw : 0 ≤ p.2 2 ∧ p.2 2 ≤ p.2 1 / 16 := ⟨Hweak.1, by
    change x 4 ≤ x 3 / 16
    nlinarith only [Hweak.2, Hactive, mul_le_mul_of_nonneg_right hasmall ha.1.le]⟩
  obtain ⟨_, Hlo, Hhi⟩ := restartProjectionHeight_bounds ha.1 Hp hMa Hactive Hn Hw
  have Heq : restartProjectionHeight p = 1 + x 0 :=
    restartProjectionHeight_of_constraint (x := x) hc (by linarith only [hneg])
  rw [Heq] at Hlo Hhi
  have hA : 0 < 1 + x 0 := (by positivity [ha.1] : 0 < a ^ 2 / 16).trans_le Hlo
  have hcoords (i : Fin 3) : |p.2 i| ≤ M * a :=
    (norm_le_pi_norm p.2 i).trans ((norm_snd_le p).trans Hp)
  have Hproj := restartProjectiveEntry_bounds ha.1 hM.le hMa Hlo Hhi
    (hcoords 0) ⟨Hactive, (le_abs_self _).trans (hcoords 1)⟩ hn.1.le Hweak.1
  have Htwo : 2 ≤ 1 / (20 * M ^ 2 * a) := (le_div_iff₀ (by positivity [ha.1])).mpr
    (by nlinarith only [hMsa])
  exact ⟨hdom, hA, Htwo.trans Hproj.1⟩

end BianchiIX
