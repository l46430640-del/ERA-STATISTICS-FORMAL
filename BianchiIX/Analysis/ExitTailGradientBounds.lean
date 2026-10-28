import BianchiIX.Analysis.ExitTailDifferential

noncomputable section

namespace BianchiIX

private theorem abs_div_le_twice {x d B : ℝ} (hd : 1 / 2 ≤ d) (hx : |x| ≤ B) :
    |x / d| ≤ 2 * B := by
  have hd0 : 0 < d := by linarith only [hd]
  have hB : 0 ≤ B := (abs_nonneg x).trans hx
  rw [abs_div, abs_of_pos hd0]
  apply (div_le_iff₀ hd0).mpr
  nlinarith only [hx, mul_le_mul_of_nonneg_left hd hB]

theorem exitTail_compact_scalar_bounds {R u v w : ℝ}
    (hR : 7 / 4 ≤ R ∧ R ≤ 17 / 4) (hu : |u| ≤ 1 / 100)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : |w| ≤ 1 / 100) :
    |exitTailRadial R u v w| ≤ 1 ∧ |exitTailStrongRate R u v w| ≤ 32 ∧
      |exitTailWeakRate R u v w| ≤ 32 := by
  let b := |u| + |w|
  have hb : 0 ≤ b := add_nonneg (abs_nonneg u) (abs_nonneg w)
  have hbsmall : b ≤ 1 / 50 := by dsimp [b]; linarith only [hu, hw]
  have hb2 : b ^ 2 ≤ b := by nlinarith only [hb, hbsmall]
  have hbv : b * v ≤ b := by nlinarith only [mul_le_mul_of_nonneg_left hv.2 hb]
  have huv : |u| * v ≤ b := by
    have H := mul_le_mul_of_nonneg_left hv.2 (abs_nonneg u)
    dsimp only [b]
    linarith only [H, abs_nonneg w]
  have H := exitTail_perturbation_bounds hR hu hv hw
  have H0 := exitTail_boundary_rate_bounds hR hv
  have H1 := (abs_sub_le (exitTailStrongRate R u v w) (exitTailStrongRate R 0 v 0) 0)
  have H2 := (abs_sub_le (exitTailWeakRate R u v w) (exitTailWeakRate R 0 v 0) 0)
  simp only [sub_zero] at H1 H2
  change |exitTailRadial R u v w| ≤ 20 * (|u| * v + b ^ 2) ∧
    |exitTailStrongRate R u v w - exitTailStrongRate R 0 v 0| ≤ 100 * (b * v + b ^ 2) ∧
    |exitTailWeakRate R u v w - exitTailWeakRate R 0 v 0| ≤ 100 * (b * v + b ^ 2) at H
  exact ⟨by nlinarith only [H.1, huv, hb2, hbsmall],
    by nlinarith only [H1, H.2.1, H0.1, hbv, hb2, hbsmall],
    by nlinarith only [H2, H.2.2, H0.2, hbv, hb2, hbsmall]⟩

theorem exitTail_radial_gradient_bounds {R u v w : ℝ}
    (hR : 7 / 4 ≤ R ∧ R ≤ 17 / 4) (hu : |u| ≤ 1 / 100)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : |w| ≤ 1 / 100) :
    |exitTailRadialGradient R u v w 0| ≤ 256 * (|u| * v + (|u| + |w|) ^ 2) ∧
      |exitTailRadialGradient R u v w 1| ≤ 32 * (v + |u| + |w|) ∧
      |exitTailRadialGradient R u v w 2| ≤ 16 * (|u| + |w|) := by
  let b := |u| + |w|
  let H := |u| * v + b ^ 2
  let t := exitTailGap R v
  let g := exitTailRadial R u v w
  have hR0 : 0 < R := by linarith only [hR.1]
  have hR1 : 1 ≤ R := by linarith only [hR.1]
  have hR5 : R ≤ 5 := by linarith only [hR.2]
  have ht := exitTailGap_compact hR.1 hv
  have ht0 : 0 < t := by dsimp only [t]; linarith only [ht.1]
  have hd := exitTailSpeed_compact hR.1 hu hv hw
  have hb : 0 ≤ b := add_nonneg (abs_nonneg u) (abs_nonneg w)
  have hH : 0 ≤ H := add_nonneg (mul_nonneg (abs_nonneg u) hv.1) (sq_nonneg b)
  have hub : |u| ≤ b := by dsimp only [b]; linarith only [abs_nonneg w]
  have hdiff : |u - w| ≤ b := abs_sub u w
  have hdiff2 : (u - w) ^ 2 ≤ b ^ 2 := by
    nlinarith only [hdiff, sq_abs (u - w), abs_nonneg (u - w), hb]
  have hC : |coupling u v w| ≤ H := exitTail_coupling_bound hv.1
  have hg : |g| ≤ 20 * H := (exitTail_perturbation_bounds hR hu hv hw).1
  have hg1 : |g| ≤ 1 := (exitTail_compact_scalar_bounds hR hu hv hw).1
  have hratio : 0 ≤ t / R ∧ t / R ≤ 1 :=
    ⟨div_nonneg ht0.le hR0.le, (div_le_one hR0).mpr ht.2⟩
  have hRt : |R / t| ≤ 5 := by
    rw [abs_of_pos (div_pos hR0 ht0)]
    apply (div_le_iff₀ ht0).mpr
    nlinarith only [hR5, ht.1]
  have hsmall : |1 / t - t / R ^ 2| ≤ 2 := by
    have hfirst : 1 / t ≤ 1 := (div_le_one ht0).mpr ht.1
    have hsecond : t / R ^ 2 ≤ 1 := (div_le_one (sq_pos_of_pos hR0)).mpr (by nlinarith only [ht.2, hR1])
    have HA := abs_sub (1 / t) (t / R ^ 2)
    rw [abs_of_nonneg (by positivity : 0 ≤ 1 / t), abs_of_nonneg (by positivity : 0 ≤ t / R ^ 2)] at HA
    linarith only [HA, hfirst, hsecond]
  have hcU : |v + w - 2 * u| ≤ v + 2 * b := by
    have Hc := (abs_sub (v + w) (2 * u)).trans (add_le_add (abs_add_le v w) le_rfl)
    rw [abs_of_nonneg hv.1, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at Hc
    dsimp only [b]
    linarith only [Hc, abs_nonneg w]
  have htw : |2 * t * (u - w) / R| ≤ 2 * b := by
    have he : 2 * t * (u - w) / R = 2 * (t / R) * (u - w) := by ring
    rw [he, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonneg hratio.1]
    nlinarith only [mul_le_mul hratio.2 hdiff (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
  refine ⟨?_, ?_, ?_⟩
  · change |(-coupling u v w - (1 / t - t / R ^ 2) * (u - w) ^ 2 - g * R / t) /
        exitTailSpeed R u v w| ≤ 256 * H
    have hprod : |(1 / t - t / R ^ 2) * (u - w) ^ 2| ≤ 2 * b ^ 2 := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg (u - w))]
      exact mul_le_mul hsmall hdiff2 (sq_nonneg _) (by norm_num)
    have hgR : |g * R / t| ≤ 100 * H := by
      rw [mul_div_assoc, abs_mul]
      have HB := mul_le_mul hg hRt (abs_nonneg _) (by positivity : 0 ≤ 20 * H)
      nlinarith only [HB]
    have Hn := (abs_sub (-coupling u v w - (1 / t - t / R ^ 2) * (u - w) ^ 2) (g * R / t)).trans
      (add_le_add (abs_sub _ _) le_rfl)
    rw [abs_neg] at Hn
    have Hbound : |-coupling u v w - (1 / t - t / R ^ 2) * (u - w) ^ 2 - g * R / t| ≤ 128 * H := by
      have HbH : b ^ 2 ≤ H := le_add_of_nonneg_left (mul_nonneg (abs_nonneg u) hv.1)
      linarith only [Hn, hC, hprod, hgR, HbH, hH]
    simpa only [← mul_assoc, show (2 : ℝ) * 128 = 256 by norm_num] using abs_div_le_twice hd Hbound
  · change |(-(v + w - 2 * u) * R - 2 * t * (u - w) / R - g * (v + w - 2 * u)) /
        exitTailSpeed R u v w| ≤ 32 * (v + |u| + |w|)
    have HA : |-(v + w - 2 * u) * R| ≤ 5 * (v + 2 * b) := by
      rw [abs_mul, abs_neg, abs_of_pos hR0]
      nlinarith only [mul_le_mul hcU hR5 hR0.le (add_nonneg hv.1 (mul_nonneg (by norm_num) hb))]
    have HB : |g * (v + w - 2 * u)| ≤ v + 2 * b := by
      rw [abs_mul]
      simpa only [one_mul] using mul_le_mul hg1 hcU (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    have Hn := (abs_sub (-(v + w - 2 * u) * R - 2 * t * (u - w) / R) (g * (v + w - 2 * u))).trans
      (add_le_add (abs_sub _ _) le_rfl)
    have Hbound : |-(v + w - 2 * u) * R - 2 * t * (u - w) / R - g * (v + w - 2 * u)| ≤ 16 * (v + b) := by
      linarith only [Hn, HA, HB, htw, hv.1, hb]
    have HQ := abs_div_le_twice hd Hbound
    dsimp only [b] at HQ
    nlinarith only [HQ]
  · change |(-u * R + 2 * t * (u - w) / R - g * u) / exitTailSpeed R u v w| ≤ 16 * b
    have HA : |-u * R| ≤ 5 * b := by
      rw [abs_mul, abs_neg, abs_of_pos hR0]
      nlinarith only [mul_le_mul hub hR5 hR0.le hb]
    have HB : |g * u| ≤ b := by
      rw [abs_mul]
      simpa only [one_mul] using mul_le_mul hg1 hub (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    have Hn := (abs_sub (-u * R + 2 * t * (u - w) / R) (g * u)).trans
      (add_le_add (abs_add_le _ _) le_rfl)
    have Hbound : |-u * R + 2 * t * (u - w) / R - g * u| ≤ 8 * b := by
      linarith only [Hn, HA, HB, htw]
    simpa only [← mul_assoc, show (2 : ℝ) * 8 = 16 by norm_num] using abs_div_le_twice hd Hbound

theorem exitTail_rate_gradient_bounds {R u v w : ℝ}
    (hR : 7 / 4 ≤ R ∧ R ≤ 17 / 4) (hu : |u| ≤ 1 / 100)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : |w| ≤ 1 / 100) :
    |exitTailStrongRateGradient R u v w 0| ≤ 512 ∧
      |exitTailWeakRateGradient R u v w 0| ≤ 512 ∧
      ∀ i : Fin 2,
        |exitTailStrongRateGradient R u v w i.succ| ≤ 256 * (v + |u| + |w|) ∧
        |exitTailWeakRateGradient R u v w i.succ| ≤ 256 * (v + |u| + |w|) := by
  let b := |u| + |w|
  let t := exitTailGap R v
  let a := exitTailStrongRate R u v w
  let c := exitTailWeakRate R u v w
  have hR0 : 0 < R := by linarith only [hR.1]
  have hR5 : R ≤ 5 := by linarith only [hR.2]
  have ht := (exitTailGap_compact hR.1 hv).1
  have ht0 : 0 < t := by dsimp only [t]; linarith only [ht]
  have hd := exitTailSpeed_compact hR.1 hu hv hw
  have hb : 0 ≤ b := add_nonneg (abs_nonneg u) (abs_nonneg w)
  have hub : |u| ≤ b := by dsimp only [b]; linarith only [abs_nonneg w]
  have hwb : |w| ≤ b := by dsimp only [b]; linarith only [abs_nonneg u]
  have ha : |a| ≤ 32 := (exitTail_compact_scalar_bounds hR hu hv hw).2.1
  have hc : |c| ≤ 32 := (exitTail_compact_scalar_bounds hR hu hv hw).2.2
  have hcplus : |1 + c| ≤ 33 := by
    have H := abs_add_le 1 c
    norm_num only [abs_one] at H
    linarith only [H, hc]
  have hcminus : |1 - c| ≤ 33 := by
    have H := abs_sub 1 c
    norm_num only [abs_one] at H
    linarith only [H, hc]
  have hRt : |R / t| ≤ 5 := by
    rw [abs_of_pos (div_pos hR0 ht0)]
    exact (div_le_iff₀ ht0).mpr (by nlinarith only [hR5, ht])
  have hcu : |v + w - 2 * u| ≤ v + 2 * b := by
    have H := (abs_sub (v + w) (2 * u)).trans (add_le_add (abs_add_le v w) le_rfl)
    rw [abs_of_nonneg hv.1, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at H
    dsimp only [b]
    linarith only [H, abs_nonneg w]
  have hauc : |a * (v + w - 2 * u)| ≤ 32 * (v + 2 * b) := by
    rw [abs_mul]
    exact mul_le_mul ha hcu (abs_nonneg _) (by norm_num)
  have hau : |a * u| ≤ 32 * b := by
    rw [abs_mul]
    exact mul_le_mul ha hub (abs_nonneg _) (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · change |(R / t - R - a * R / t) / exitTailSpeed R u v w| ≤ 512
    have HA : |a * R / t| ≤ 160 := by
      rw [mul_div_assoc, abs_mul]
      exact (mul_le_mul ha hRt (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
    have Hn := (abs_sub (R / t - R) (a * R / t)).trans (add_le_add (abs_sub _ _) le_rfl)
    rw [abs_of_pos hR0] at Hn
    have HQ := abs_div_le_twice hd (show |R / t - R - a * R / t| ≤ 256 by linarith only [Hn, hRt, hR5, HA])
    norm_num only [show (2 : ℝ) * 256 = 512 by norm_num] at HQ
    exact HQ
  · change |((1 - c) * R / t) / exitTailSpeed R u v w| ≤ 512
    have HA : |(1 - c) * R / t| ≤ 256 := by
      rw [mul_div_assoc, abs_mul]
      have H := mul_le_mul hcminus hRt (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 33)
      linarith only [H]
    simpa only [show (2 : ℝ) * 256 = 512 by norm_num] using abs_div_le_twice hd HA
  · intro i
    fin_cases i
    · constructor
      · change |(u - a * (v + w - 2 * u)) / exitTailSpeed R u v w| ≤ 256 * (v + |u| + |w|)
        have Hn := abs_sub u (a * (v + w - 2 * u))
        have H := abs_div_le_twice hd (show |u - a * (v + w - 2 * u)| ≤ 128 * (v + b) by
          linarith only [Hn, hub, hauc, hv.1, hb])
        dsimp only [b] at H
        nlinarith only [H]
      · change |(-(1 + c) * (v + w - 2 * u)) / exitTailSpeed R u v w| ≤ 256 * (v + |u| + |w|)
        have Hn : |-(1 + c) * (v + w - 2 * u)| ≤ 128 * (v + b) := by
          rw [abs_mul, abs_neg]
          have H := mul_le_mul hcplus hcu (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 33)
          linarith only [H, hv.1, hb]
        have H := abs_div_le_twice hd Hn
        dsimp only [b] at H
        nlinarith only [H]
    · constructor
      · change |(v - w - a * u) / exitTailSpeed R u v w| ≤ 256 * (v + |u| + |w|)
        have Hn := (abs_sub (v - w) (a * u)).trans (add_le_add (abs_sub _ _) le_rfl)
        rw [abs_of_nonneg hv.1] at Hn
        have H := abs_div_le_twice hd (show |v - w - a * u| ≤ 128 * (v + b) by
          linarith only [Hn, hwb, hau, hv.1, hb])
        dsimp only [b] at H
        nlinarith only [H]
      · change |(-(1 + c) * u) / exitTailSpeed R u v w| ≤ 256 * (v + |u| + |w|)
        have Hn : |-(1 + c) * u| ≤ 128 * (v + b) := by
          rw [abs_mul, abs_neg]
          have H := mul_le_mul hcplus hub (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 33)
          linarith only [H, hv.1, hb]
        have H := abs_div_le_twice hd Hn
        dsimp only [b] at H
        nlinarith only [H]

end BianchiIX
