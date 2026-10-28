import BianchiIX.Analysis.EntranceTerminalWeights

noncomputable section

namespace BianchiIX

/-- Keeping the strong exponential in every terminal product avoids a waiting loss. -/
theorem entrance_active_terminal_products {u v w U W a c : ℝ}
    (hu : 0 ≤ u ∧ u ≤ 1) (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1)
    (hU0 : 0 ≤ U) (hW0 : 0 ≤ W) (ha : 0 ≤ a ∧ a ≤ 1) (hc : 0 ≤ c ∧ c ≤ 1)
    (hU : U ≤ u * v * a) (hW : W ≤ w * v * c) :
    let A := u * v * a
    let B := v ^ 2 * w ^ 2 * c ^ 2
    U + W ≤ u + w ∧ W ^ 2 ≤ B ∧
      (U + W) ^ 2 ≤ 2 * (A + B) ∧ (U + W) * U ≤ 2 * A ∧ (U + W) * W ≤ A + B := by
  intro A B
  have hUb : U ≤ u := hU.trans ((mul_le_of_le_one_right (mul_nonneg hu.1 hv.1) ha.2).trans
    (mul_le_of_le_one_right hu.1 hv.2))
  have hWb : W ≤ w := hW.trans ((mul_le_of_le_one_right (mul_nonneg hw.1 hv.1) hc.2).trans
    (mul_le_of_le_one_right hw.1 hv.2))
  have hU1 : U ≤ 1 := hUb.trans hu.2
  have hW1 : W ≤ 1 := hWb.trans hw.2
  have hUsq : U ^ 2 ≤ A := (by nlinarith only [mul_le_of_le_one_right hU0 hU1] : U ^ 2 ≤ U).trans hU
  have hWsq : W ^ 2 ≤ B := by
    convert! pow_le_pow_left₀ hW0 hW 2 using 1
    ring
  have hcross : U * W ≤ A := (mul_le_of_le_one_right hU0 hW1).trans hU
  refine ⟨add_le_add hUb hWb, hWsq, ?_, ?_, ?_⟩
  · nlinarith only [hUsq, hWsq, sq_nonneg (U - W)]
  · nlinarith only [hUsq, hcross]
  · nlinarith only [hcross, hWsq]

theorem entrance_active_terminal_correction {k T K A B b U W q x y e : ℝ}
    (hk : 1 ≤ k) (hT : 0 ≤ T) (hK : 0 ≤ K) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hb : 0 ≤ b) (hU : 0 ≤ U) (hW : 0 ≤ W)
    (hsq : b ^ 2 ≤ 2 * (A + B)) (hfast : b * U ≤ 2 * A) (hslow : b * W ≤ A + B)
    (hq : |q| ≤ K) (hx : |x| ≤ K * k) (hy : |y| ≤ K)
    (he : |e| ≤ T * (b ^ 2 / k ^ 2 * |q| + b / k * (U * |x| + W * |y|))) :
    |e| ≤ 5 * T * K * (A + B / k) := by
  have hk0 : 0 < k := by linarith
  have hAk : A / k ≤ A := div_le_self hA hk
  have hAk2 : A / k ^ 2 ≤ A := div_le_self hA (one_le_pow₀ hk)
  have hBk2 : B / k ^ 2 ≤ B / k :=
    div_le_div_of_nonneg_left hB hk0 (by nlinarith only [hk])
  have hsq' : b ^ 2 / k ^ 2 ≤ 2 * (A + B / k) := by
    have H := div_le_div_of_nonneg_right hsq (sq_nonneg k)
    calc
      _ ≤ 2 * (A + B) / k ^ 2 := H
      _ = 2 * (A / k ^ 2 + B / k ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hAk2 hBk2) (by norm_num)
  have hwall : b / k * (U * |x| + W * |y|) ≤ 3 * K * (A + B / k) := by
    calc
      _ ≤ b / k * (U * (K * k) + W * K) :=
        mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hx hU)
          (mul_le_mul_of_nonneg_left hy hW)) (div_nonneg hb hk0.le)
      _ = K * (b * U + b * W / k) := by field_simp
      _ ≤ K * (2 * A + (A + B) / k) := mul_le_mul_of_nonneg_left
        (add_le_add hfast (div_le_div_of_nonneg_right hslow hk0.le)) hK
      _ ≤ 3 * K * (A + B / k) := by
        rw [add_div]
        have H := mul_le_mul_of_nonneg_left hAk hK
        nlinarith only [H, mul_nonneg hK (div_nonneg hB hk0.le)]
  have hrad := (mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ b ^ 2 / k ^ 2)).trans
    (mul_le_mul_of_nonneg_right hsq' hK)
  exact he.trans ((mul_le_mul_of_nonneg_left (add_le_add hrad hwall) hT).trans_eq (by ring))

theorem entrance_active_half_decay {v k : ℝ} (hv : 0 < v) (hhalf : v ≤ 1 / 2) (hk : 1 ≤ k) :
    Real.exp (-k * (-Real.log v) / 3) ≤ 6 / k := by
  have hlog := Real.log_le_log hv hhalf
  have htwo := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num [Real.log_div] at hlog
  have hL : 1 / 2 ≤ -Real.log v := by norm_num at htwo; linarith
  have H := (entrance_terminal_clock_weights hk (by linarith : 0 ≤ -Real.log v)).2.2.1
  have H' := mul_le_mul_of_nonneg_right hL (Real.exp_pos (-k * (-Real.log v) / 3)).le
  simp only [div_eq_mul_inv] at H H' ⊢
  nlinarith only [H, H']

theorem entrance_strong_weight_eq_rpow {v : ℝ} (hv : 0 < v) (k : ℝ) :
    Real.exp (-k * (-Real.log v) / 3) = v ^ (k / 3) := by
  rw [Real.rpow_def_of_pos hv]
  congr 1
  ring

theorem entrance_active_endpoint_unshift {k C D H q G x y βU βW : ℝ}
    (hk : 1 ≤ k) (hC : 0 ≤ C) (hD : 0 ≤ D) (hH : 0 ≤ H ∧ H ≤ 2)
    (hG : |G| ≤ 2 * D) (hq : |q + G| ≤ C * H / k)
    (hlogs : |x + βU| + k ^ 2 * |y + βW| ≤ C / k)
    (hU : |βU| ≤ 12 * k) (hW : |βW| ≤ 9) :
    let K := 2 * C + 2 * D + 12
    |q| ≤ K ∧ |x| ≤ K * k ∧ |y| ≤ K := by
  intro K
  have hk0 : 0 < k := by linarith
  have hCk : C / k ≤ C := div_le_self hC hk
  have hphase : C * H / k ≤ 2 * C :=
    (div_le_self (mul_nonneg hC hH.1) hk).trans
      ((mul_le_mul_of_nonneg_left hH.2 hC).trans_eq (by ring))
  have hstrong : |x + βU| ≤ C := (le_add_of_nonneg_right (by positivity)).trans (hlogs.trans hCk)
  have hweak : |y + βW| ≤ C := by
    calc
      _ ≤ k ^ 2 * |y + βW| := le_mul_of_one_le_left (abs_nonneg _) (one_le_pow₀ hk)
      _ ≤ |x + βU| + k ^ 2 * |y + βW| := le_add_of_nonneg_left (abs_nonneg _)
      _ ≤ C := hlogs.trans hCk
  have htriangle (a b : ℝ) : |a| ≤ |a + b| + |b| := by
    simpa only [add_sub_cancel_right] using abs_sub (a + b) b
  have hq' := (htriangle q G).trans (add_le_add (hq.trans hphase) hG)
  have hx' := (htriangle x βU).trans (add_le_add hstrong hU)
  have hy' := (htriangle y βW).trans (add_le_add hweak hW)
  refine ⟨hq'.trans (by dsimp [K]; linarith), ?_, hy'.trans (by dsimp [K]; linarith)⟩
  have H1 := mul_le_mul_of_nonneg_left hk hC
  have H2 := mul_nonneg hD hk0.le
  dsimp [K]
  nlinarith only [hx', H1, H2, hC]

end BianchiIX
