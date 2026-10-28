import BianchiIX.Analysis.ConnectionCoefficientMatrix
import BianchiIX.Analysis.SignedRowGrowth

noncomputable section

namespace BianchiIX

/-- The homogeneous equation for (X, mu^2 Y). -/
def connectionTransverseMatrix (μ m u v w : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![connectionStrongClockPartials m u v w 1, connectionStrongClockPartials m u v w 2 / μ ^ 2;
     μ ^ 2 * connectionWeakClockPartials m u v w 1, connectionWeakClockPartials m u v w 2]

def connectionTransverseRate (μ u v w : ℝ) : ℝ :=
  64 * (2 * μ * u + v ^ 2 / μ ^ 3 + v * w / μ ^ 3)

/-- A decreasing state function pays for the entire transverse growth. -/
def connectionTransverseBudget (μ u v w : ℝ) : ℝ :=
  64 * (4 * u + v ^ 2 / (2 * μ ^ 3) + v * w / (2 * μ ^ 2))

theorem connectionTransverseMatrix_rows {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) (i : Fin 2) :
    (∑ j : Fin 2, |connectionTransverseMatrix μ m u v w i j|) ≤
      connectionTransverseRate μ u v w := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hμ2 : 1 ≤ μ ^ 2 := by nlinarith only [hμ, sq_nonneg (μ - 4)]
  have hu0 := hu.1
  have hv0 := hv.1
  have hw0 := hw.1
  have huv : u * v ≤ u := by nlinarith only [mul_le_mul_of_nonneg_left hv.2 hu0]
  have hinv : 1 / μ ≤ 1 := (div_le_one hμ0).mpr (by linarith only [hμ])
  have hinv2 : 1 / μ ^ 2 ≤ 1 := (div_le_one (sq_pos_of_pos hμ0)).mpr hμ2
  have ha := connectionStrongClockPartials_bounds hμ hm hu hv hw
  have hb := connectionWeakClockPartials_bounds hμ hm hu hv hw
  have hdiv (r : ℝ) : |r / μ ^ 2| = |r| / μ ^ 2 := by rw [abs_div, abs_of_pos (sq_pos_of_pos hμ0)]
  rw [Fin.sum_univ_two]
  fin_cases i
  · change |connectionStrongClockPartials m u v w 1| +
      |connectionStrongClockPartials m u v w 2 / μ ^ 2| ≤ connectionTransverseRate μ u v w
    rw [hdiv]
    have H := add_le_add ha.2.1 (div_le_div_of_nonneg_right ha.2.2.1 (sq_nonneg μ))
    have huv' : u * v / μ ^ 2 ≤ u :=
      (div_le_div_of_nonneg_right huv (sq_nonneg μ)).trans
        (by simpa only [one_div, div_eq_mul_inv, mul_one, one_mul] using mul_le_mul_of_nonneg_left hinv2 hu0)
    have hmain : 32 * u + 32 * ((v ^ 2 + v * w) / μ + u * v) / μ ^ 2 =
        32 * (u + v ^ 2 / μ ^ 3 + v * w / μ ^ 3 + u * v / μ ^ 2) := by ring
    rw [hmain] at H
    dsimp [connectionTransverseRate]
    have hv2 : 0 ≤ v ^ 2 / μ ^ 3 := by positivity
    have hp : 0 ≤ v * w / μ ^ 3 := by positivity
    nlinarith only [H, huv', hv2, hp, hu0, mul_nonneg (sub_nonneg.mpr hμ) hu0]
  · change |μ ^ 2 * connectionWeakClockPartials m u v w 1| +
      |connectionWeakClockPartials m u v w 2| ≤ connectionTransverseRate μ u v w
    rw [abs_mul, abs_of_nonneg (sq_nonneg μ)]
    have H := add_le_add (mul_le_mul_of_nonneg_left hb.2.1 (sq_nonneg μ)) hb.2.2.1
    have hid : μ ^ 2 * (64 * u / μ) = 64 * μ * u := by field_simp
    rw [hid] at H
    have huv' : u * v / μ ≤ u :=
      (div_le_div_of_nonneg_right huv hμ0.le).trans
        (by simpa only [one_div, div_eq_mul_inv, mul_one, one_mul] using mul_le_mul_of_nonneg_left hinv hu0)
    dsimp [connectionTransverseRate]
    have hp : 0 ≤ v * w / μ ^ 3 := by positivity
    nlinarith only [H, huv', hp, mul_nonneg (show 0 ≤ μ - 1 by linarith only [hμ]) hu0]

theorem connectionTransverseMatrix_signedRows {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) (i : Fin 2) :
    signedRowSum (connectionTransverseMatrix μ m u v w) i ≤ connectionTransverseRate μ u v w := by
  apply le_trans _ (connectionTransverseMatrix_rows hμ hm hu hv hw i)
  have hfin : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
  fin_cases i
  · simpa [signedRowSum, hfin] using le_abs_self (connectionTransverseMatrix μ m u v w 0 0)
  · simpa [signedRowSum, hfin, add_comm] using
      add_le_add_right (le_abs_self (connectionTransverseMatrix μ m u v w 1 1))
        |connectionTransverseMatrix μ m u v w 1 0|

theorem connectionTransverseBudget_nonneg {μ u v w : ℝ} (hμ : 0 ≤ μ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) : 0 ≤ connectionTransverseBudget μ u v w := by
  unfold connectionTransverseBudget
  positivity

theorem connectionTransverseBudget_entry {μ u v w : ℝ} (hμ : 4 ≤ μ)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / μ) (hv : 0 ≤ v ∧ v ≤ 1)
    (hw : 0 ≤ w ∧ w ≤ 1 / 10000) : connectionTransverseBudget μ u v w ≤ 2533 / 5000 := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hu' : u ≤ 1 / 40000 := by
    calc
      u ≤ (1 / 10000) / μ := hu.2
      _ ≤ (1 / 10000) / 4 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hμ
      _ = _ := by norm_num
  have hμ2 : 16 ≤ μ ^ 2 := by nlinarith only [hμ, sq_nonneg (μ - 4)]
  have hμ3 : 64 ≤ μ ^ 3 := by nlinarith only [mul_le_mul_of_nonneg_right hμ2 hμ0.le, hμ]
  have hv2 : v ^ 2 ≤ 1 := by nlinarith only [hv.1, hv.2, mul_nonneg hv.1 (sub_nonneg.mpr hv.2)]
  have hp : v * w ≤ 1 / 10000 := (mul_le_mul_of_nonneg_right hv.2 hw.1).trans (by simpa using hw.2)
  have H1 : v ^ 2 / (2 * μ ^ 3) ≤ 1 / 128 := by
    calc
      _ ≤ 1 / (2 * μ ^ 3) := div_le_div_of_nonneg_right hv2 (by positivity)
      _ ≤ 1 / 128 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith only [hμ3])
  have H2 : v * w / (2 * μ ^ 2) ≤ 1 / 320000 := by
    calc
      _ ≤ (1 / 10000) / (2 * μ ^ 2) := div_le_div_of_nonneg_right hp (by positivity)
      _ ≤ (1 / 10000) / 32 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith only [hμ2])
      _ = _ := by norm_num
  unfold connectionTransverseBudget
  linarith only [hu', H1, H2]

theorem exp_connectionTransverseBudget_lt_two {μ u v w : ℝ} (hμ : 4 ≤ μ)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / μ) (hv : 0 ≤ v ∧ v ≤ 1)
    (hw : 0 ≤ w ∧ w ≤ 1 / 10000) : Real.exp (connectionTransverseBudget μ u v w) < 2 := by
  have H := connectionTransverseBudget_entry hμ hu hv hw
  have H' := Real.exp_lt_two_add_div_two_sub (x := (2 : ℝ) / 3) (by norm_num) (by norm_num)
  have hE : connectionTransverseBudget μ u v w ≤ 2 / 3 := H.trans (by norm_num)
  exact (Real.exp_le_exp.mpr hE).trans_lt (by norm_num at H'; exact H')

end BianchiIX
