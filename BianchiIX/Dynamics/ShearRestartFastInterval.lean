import BianchiIX.Dynamics.RestartFastInterval
import BianchiIX.Dynamics.ShearRestartProjectiveEntry
import BianchiIX.Dynamics.ProjectiveRegularity
import BianchiIX.Dynamics.Events

noncomputable section

namespace BianchiIX

open Set

/-- Between any two fixed fast exponents the positive-shear orbit can only cross the active section upward. -/
theorem exists_restartShear_fast_interval :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q₀ q₁ : ℝ, 2 < q₀ → q₀ ≤ q₁ → ∃ astar > (0 : ℝ),
        ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε n₂ n₃ : ℝ,
          (0 ≤ ε ∧ ε ≤ 1 / 64) →
          (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) → (0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) →
          ∀ ρ ∈ Icc a (2 * a),
          let T₀ := q₀ / 2 * Real.log (1 / a)
          let T₁ := q₁ / 2 * Real.log (1 / a)
          let z := restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)
          0 ≤ T₀ ∧ T₀ ≤ T₁ ∧ 0 < restartSectionRadicand h (restartShearCurve 1 n₂ n₃ ρ) ∧
          ∀ t ∈ Icc T₀ T₁,
            let x := normalizedMaxCurve z 0 t
            let y := toProjectiveState x
            t ∈ normalizedMaxDomain z 0 ∧ 0 < 1 + x 0 ∧
            1 / (8 * a) ≤ y 0 ∧ (0 < y 1 ∧ y 1 ≤ 1 / 512) ∧
            (0 ≤ y 2 + y 3 ∧ y 2 + y 3 ≤ 1 / a) ∧
            1 / (16 * a) ≤ y 0 - 1 - coupling (y 1) (y 2) (y 3) ∧
            (y 2 ≠ 1 ∨ 0 < normalizedEventRate projectiveActiveWall z 0 t) := by
  obtain ⟨C, hC, HC⟩ := exists_restartSection_fast_interval
  have hCp : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 32) hC
  refine ⟨min (1 / (4 * C)) (1 / 4096), lt_min (by positivity) (by norm_num), ?_⟩
  intro h hh q₀ q₁ hq₀ hq
  have hhsmall : h ≤ 1 / 4096 := hh.2.trans (min_le_right _ _)
  obtain ⟨astar, hastar, HA⟩ := HC h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩
    2 (by norm_num) q₀ q₁ hq₀ hq
  refine ⟨astar, hastar, ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ ρ hρ T₀ T₁ z
  obtain ⟨hasmall, hT₀, hTT, HZ⟩ := HA a ha
  let Z := restartShearCurve 1 n₂ n₃ ρ
  have hZ : ‖Z‖ ≤ 2 * a := (restartShearCurve_annulus ha.1 hρ (by norm_num) hε h₂ h₃).1
  obtain ⟨hrad, HT⟩ := HZ Z hZ
  have ha1 : a ≤ 1 := by linarith only [hasmall]
  have Hpower : a ^ q₀ ≤ a ^ (2 : ℕ) := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_ge ha.1 ha1 hq₀.le
  refine ⟨hT₀, hTT, hrad, ?_⟩
  intro t ht x y
  obtain ⟨hdom, hc, hneg, hn, _, _, herr, HW⟩ := HT t ht
  change stateConstraint x = 1 at hc
  change x 0 ≤ -(15 / 16) at hneg
  change 0 < x 2 ∧ x 2 ≤ h * a ^ q₀ at hn
  have htransfer : ‖restartCenterTransfer h Z - Z‖ ≤ a / 8 := by
    have H := (restartCenterTransfer h - ContinuousLinearMap.id ℝ RestartCenterState).le_opNorm Z
    change ‖restartCenterTransfer h Z - Z‖ ≤ _ at H
    have HB := restartCenterTransfer_sub_id_bound ⟨hh.1.le, by linarith only [hhsmall]⟩
    have H' := H.trans (mul_le_mul HB hZ (norm_nonneg Z) (by positivity [hh.1]))
    exact H'.trans (by nlinarith only [mul_le_mul_of_nonneg_right hhsmall ha.1.le, ha.1])
  have hclose : ‖restartSectionCenterFlow h t Z - Z‖ ≤ a / 4 := by
    have H := norm_add_le (restartSectionRemainder h t Z) (restartCenterTransfer h Z - Z)
    have heq : restartSectionRemainder h t Z + (restartCenterTransfer h Z - Z) =
        restartSectionCenterFlow h t Z - Z := by unfold restartSectionRemainder; abel
    rw [heq] at H
    exact H.trans (by linarith only [herr, htransfer])
  have hs : 3 * a / 4 ≤ x 1 ∧ x 1 ≤ 9 * a / 4 := by
    have H := restartShearCurve_shear_of_close hρ (by norm_num : |(1 : ℝ)| = 1) hclose
    change 3 * a / 4 ≤ 1 * x 1 ∧ 1 * x 1 ≤ 9 * a / 4 at H
    simpa only [one_mul] using H
  have hnsmall : x 2 ≤ h * a ^ 2 :=
    hn.2.trans (mul_le_mul_of_nonneg_left Hpower hh.1.le)
  have hnsq : x 2 ≤ a ^ 2 := hnsmall.trans
    (mul_le_of_le_one_left (sq_nonneg a) (by linarith only [hhsmall]))
  have Hw₂ : n₂ / 2 ≤ x 3 ∧ x 3 ≤ 2 * n₂ := HW 0 h₂.1
  have Hw₃ : n₃ / 2 ≤ x 4 ∧ x 4 ≤ 2 * n₃ := HW 1 h₃.1
  have H₂ : 0 ≤ x 3 ∧ x 3 ≤ a / 16 := by
    constructor
    · linarith only [Hw₂.1, h₂.1]
    · nlinarith only [Hw₂.2, h₂.2, mul_le_mul_of_nonneg_right hε.2 ha.1.le]
  have H₃ : 0 ≤ x 4 ∧ x 4 ≤ a / 16 := by
    constructor
    · linarith only [Hw₃.1, h₃.1]
    · nlinarith only [Hw₃.2, h₃.2, mul_le_mul_of_nonneg_right hε.2 ha.1.le]
  have Hp := restartProjectionHeight_shear_bounds
    (p := (x 2, ![x 1, x 3, x 4])) ⟨ha.1, hasmall⟩ (by norm_num : |(1 : ℝ)| = 1)
    (by simpa only [one_mul, Matrix.cons_val_zero] using hs) ⟨hn.1.le, hnsq⟩ H₂ H₃
  have Heq : restartProjectionHeight (x 2, ![x 1, x 3, x 4]) = 1 + x 0 :=
    restartProjectionHeight_of_constraint hc (by linarith only [hneg])
  rw [Heq] at Hp
  have hA : 0 < 1 + x 0 := (by positivity [ha.1] : 0 < a ^ 2 / 4).trans_le Hp.2.1
  have hsqrt1 : 1 ≤ Real.sqrt (3 : ℝ) := by
    nlinarith only [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have hsqrt2 : Real.sqrt (3 : ℝ) ≤ 2 := by
    nlinarith only [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have hspos : 0 ≤ x 1 := (by positivity [ha.1] : 0 ≤ 3 * a / 4).trans hs.1
  have hm : 1 / (8 * a) ≤ y 0 := by
    calc
      _ = (3 * a / 4) / (6 * a ^ 2) := by field_simp; ring
      _ ≤ Real.sqrt 3 * x 1 / (1 + x 0) := div_le_div₀ (by positivity [ha.1])
        (hs.1.trans (by nlinarith only [mul_le_mul_of_nonneg_right hsqrt1 hspos])) hA Hp.2.2
  have hu : 0 < y 1 ∧ y 1 ≤ 1 / 512 := by
    refine ⟨div_pos (mul_pos (by positivity) hn.1) hA, ?_⟩
    calc
      y 1 ≤ (2 * (h * a ^ 2)) / (a ^ 2 / 4) := div_le_div₀ (by positivity [hh.1])
        (by nlinarith only [mul_le_mul_of_nonneg_right hsqrt2 hn.1.le, hnsmall])
        (by positivity [ha.1]) Hp.2.1
      _ = 8 * h := by field_simp [ha.1.ne']; ring
      _ ≤ _ := by linarith only [hhsmall]
  have hsum : 0 ≤ y 2 + y 3 ∧ y 2 + y 3 ≤ 1 / a := by
    have Hnon₂ : 0 ≤ y 2 := div_nonneg (mul_nonneg (Real.sqrt_nonneg _) H₂.1) hA.le
    have Hnon₃ : 0 ≤ y 3 := div_nonneg (mul_nonneg (Real.sqrt_nonneg _) H₃.1) hA.le
    refine ⟨add_nonneg Hnon₂ Hnon₃, ?_⟩
    calc
      _ = (Real.sqrt 3 * (x 3 + x 4)) / (1 + x 0) := by
        change Real.sqrt 3 * x 3 / (1 + x 0) + Real.sqrt 3 * x 4 / (1 + x 0) = _
        ring
      _ ≤ (a / 4) / (a ^ 2 / 4) := div_le_div₀ (by positivity [ha.1])
        (by nlinarith only [mul_le_mul_of_nonneg_right hsqrt2 (add_nonneg H₂.1 H₃.1), H₂.2, H₃.2])
        (by positivity [ha.1]) Hp.2.1
      _ = _ := by field_simp
  have hcoup : coupling (y 1) (y 2) (y 3) ≤ 1 / (512 * a) := by
    have H := mul_le_mul hu.2 hsum.2 hsum.1 (by norm_num : (0 : ℝ) ≤ 1 / 512)
    dsimp only [coupling]
    calc
      _ ≤ y 1 * (y 2 + y 3) := by nlinarith only [sq_nonneg (y 1)]
      _ ≤ _ := H.trans_eq (by ring)
  have hr : 1 / (16 * a) ≤ y 0 - 1 - coupling (y 1) (y 2) (y 3) := by
    have Hscale : 1 / (16 * a) ≤ 1 / (8 * a) - 1 - 1 / (512 * a) := by
      have H : (1 : ℝ) / 16 ≤ 1 / 8 - a - 1 / 512 := by linarith only [hasmall]
      calc
        _ = ((1 : ℝ) / 16) / a := by ring
        _ ≤ (1 / 8 - a - 1 / 512) / a := div_le_div_of_nonneg_right H ha.1.le
        _ = _ := by field_simp [ha.1.ne']
    linarith only [Hscale, hm, hcoup]
  refine ⟨hdom, hA, hm, hu, hsum, hr, ?_⟩
  by_cases hv : y 2 = 1
  · right
    change 0 < fderiv ℝ projectiveActiveWall x (normalizedField x)
    rw [projectiveActiveWall_fderiv_field hA.ne' hc]
    apply mul_pos hA
    change 0 < (y 0 - 1 - coupling (y 1) (y 2) (y 3)) * y 2
    rw [hv, mul_one]
    simpa only [hv] using (by positivity [ha.1] : 0 < 1 / (16 * a)).trans_le hr
  · exact Or.inl hv

end BianchiIX
