import BianchiIX.Algebra.CoreConeSize

noncomputable section

namespace BianchiIX

theorem sqrt_le_exp_half {m c : ℝ} (hm : m ≤ Real.exp c) :
    Real.sqrt m ≤ Real.exp (c / 2) := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨(Real.exp_pos _).le, hm.trans_eq ?_⟩
  rw [sq, ← Real.exp_add]
  congr 1
  ring

theorem exists_core_cone_threshold {R A B : ℝ} (hR : 0 ≤ R) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ ε > 0, ε ≤ 1 / 10000 ∧ 7 * R * Real.sqrt ε ≤ 1 / 32 ∧
      38400 * A * Real.sqrt ε ≤ 1 / 32 ∧ 3 * B * Real.sqrt ε ≤ 1 / 32 := by
  let C := 1 + 7 * R + 38400 * A + 3 * B
  have hC : 0 < C := by dsimp [C]; positivity
  let d := min (1 / 100 : ℝ) (1 / (32 * C))
  have hd : 0 < d := lt_min (by norm_num) (by positivity)
  have hdsq : Real.sqrt (d ^ 2) = d := Real.sqrt_sq hd.le
  have hdC : C * d ≤ 1 / 32 := by
    have H := (le_div_iff₀ (show 0 < 32 * C by positivity)).mp (min_le_right (1 / 100) (1 / (32 * C)))
    change d * (32 * C) ≤ 1 at H
    linarith only [H]
  have hbound (X : ℝ) (hX : X ≤ C) : X * Real.sqrt (d ^ 2) ≤ 1 / 32 := by
    rw [hdsq]
    exact (mul_le_mul_of_nonneg_right hX hd.le).trans hdC
  refine ⟨d ^ 2, sq_pos_of_pos hd, ?_, hbound _ ?_, hbound _ ?_, hbound _ ?_⟩
  · have H : d ≤ 1 / 100 := min_le_left _ _
    nlinarith only [H, hd, mul_nonneg hd.le (sub_nonneg.mpr H)]
  all_goals dsimp [C]; linarith only [hR, hA, hB]

/-- A single entrance threshold gives the quantitative cone margin, without amplitude division. -/
theorem core_cone_margin {k ε u w a b R A B mU mW lU lW dK dU dW : ℝ}
    (hk : 6 ≤ k) (hε : 0 ≤ ε ∧ ε ≤ 1)
    (hu : 0 ≤ u ∧ u ≤ ε / k) (hw : 0 ≤ w ∧ w ≤ ε / k)
    (ha : |a| ≤ Real.sqrt u) (hb : |b| ≤ Real.sqrt w)
    (hR : 0 ≤ R) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hsmallR : 7 * R * Real.sqrt ε ≤ 1 / 32)
    (hsmallU : 38400 * A * Real.sqrt ε ≤ 1 / 32)
    (hsmallW : 3 * B * Real.sqrt ε ≤ 1 / 32)
    (hmU : 0 < mU ∧ mU ≤ Real.exp (-k / 40))
    (hmW : 0 < mW ∧ mW ≤ Real.exp (-1 / (2 * k)))
    (hrad : |dK - 1| ≤ R * (|a| / k + (u + w) * (1 + k * |a| + |b|) / k))
    (hlogU : |lU| ≤ A * Real.log (4 * k) * (1 + k * |a| + |b|))
    (hlogW : |lW| ≤ B * Real.log (4 * k) * (1 + k * |a| + |b|) / k ^ 2)
    (hdU : dU = mU * (a + u * lU)) (hdW : dW = mW * (b + w * lW)) :
    0 < dK ∧ |dK - 1| ≤ 1 / (32 * k) ∧
      |dU| ≤ (1 - 1 / (16 * k)) * Real.sqrt (u * mU) * dK ∧
      |dW| ≤ (1 - 1 / (16 * k)) * Real.sqrt (w * mW) * dK := by
  let Q := 1 + k * |a| + |b|
  let L := Real.log (4 * k)
  let e := 1 / (32 * k)
  have hk0 : 0 < k := by linarith only [hk]
  have hL : 0 ≤ L := Real.log_nonneg (by linarith only [hk])
  have hLk : L ≤ k := core_log_bound hk
  have he : 0 < e := by dsimp [e]; positivity
  have he1 : e ≤ 1 / 192 := (div_le_iff₀ (by positivity : 0 < 32 * k)).mpr (by linarith only [hk])
  obtain ⟨huQ, hwQ, hbQ⟩ := core_cone_weighted_size hk hε hu hw ha hb
  have hr : |dK - 1| ≤ e := by
    apply hrad.trans
    calc
      _ = R * (|a| + (u + w) * Q) / k := by dsimp [Q]; ring
      _ ≤ R * (7 * Real.sqrt ε) / k :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith only [ha, hbQ]) hR) hk0.le
      _ = (7 * R * Real.sqrt ε) / k := by ring
      _ ≤ (1 / 32) / k := div_le_div_of_nonneg_right hsmallR hk0.le
      _ = e := by dsimp [e]; ring
  have hdK : 1 - e ≤ dK := by linarith only [(abs_le.mp hr).1]
  have hrootU : Real.sqrt mU ≤ Real.exp (-k / 80) := by
    convert! sqrt_le_exp_half hmU.2 using 1
    congr 1
    ring
  have hrootW : Real.sqrt mW ≤ Real.exp (-1 / (4 * k)) := by
    convert! sqrt_le_exp_half hmW.2 using 1
    congr 1
    ring
  have hbase : Real.exp (-1 / (4 * k)) ≤ 1 - 4 * e := by
    have hx : 0 ≤ 1 / (4 * k) := by positivity
    have hx1 : 1 / (4 * k) ≤ 1 := (div_le_iff₀ (by positivity)).mpr (by linarith only [hk])
    calc
      _ = Real.exp (-(1 / (4 * k))) := by congr 1; ring
      _ ≤ 1 - (1 / (4 * k)) / 2 := exp_neg_le_one_sub_half hx hx1
      _ = _ := by dsimp [e]; ring
  have hstrongBase : Real.exp (-k / 80) ≤ Real.exp (-1 / (4 * k)) := by
    apply Real.exp_le_exp.mpr
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 80) (by positivity : 0 < 4 * k)).mpr
    nlinarith only [hk, sq_nonneg (k - 6)]
  have hrootW1 : Real.sqrt mW ≤ 1 := hrootW.trans (hbase.trans (by linarith only [he]))
  have hstrongBudget : Real.exp (-k / 80) * L ≤ 12800 / k := by
    apply (le_div_iff₀ hk0).mpr
    have H := mul_le_mul_of_nonneg_left hLk (mul_nonneg hk0.le (Real.exp_pos (-k / 80)).le)
    have H' := core_strong_exp_budget hk0.le
    nlinarith only [H, H']
  have huLog : Real.sqrt u * |lU| ≤ 3 * A * L * Real.sqrt ε := by
    calc
      _ ≤ Real.sqrt u * (A * L * Q) := mul_le_mul_of_nonneg_left hlogU (Real.sqrt_nonneg _)
      _ = (A * L) * (Real.sqrt u * Q) := by ring
      _ ≤ (A * L) * (3 * Real.sqrt ε) := mul_le_mul_of_nonneg_left huQ (mul_nonneg hA hL)
      _ = _ := by ring
  have hwLog : Real.sqrt w * |lW| ≤ 3 * B * L * Real.sqrt ε / k ^ 2 := by
    calc
      _ ≤ Real.sqrt w * (B * L * Q / k ^ 2) := mul_le_mul_of_nonneg_left hlogW (Real.sqrt_nonneg _)
      _ = (B * L / k ^ 2) * (Real.sqrt w * Q) := by ring
      _ ≤ (B * L / k ^ 2) * (3 * Real.sqrt ε) := mul_le_mul_of_nonneg_left hwQ (by positivity)
      _ = _ := by ring
  have hU : Real.sqrt mU * Real.sqrt u * |lU| ≤ e := by
    calc
      _ ≤ Real.exp (-k / 80) * (3 * A * L * Real.sqrt ε) := by
        rw [mul_assoc]
        exact mul_le_mul hrootU huLog (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)) (Real.exp_pos _).le
      _ = (3 * A * Real.sqrt ε) * (Real.exp (-k / 80) * L) := by ring
      _ ≤ (3 * A * Real.sqrt ε) * (12800 / k) := mul_le_mul_of_nonneg_left hstrongBudget (by positivity)
      _ = (38400 * A * Real.sqrt ε) / k := by ring
      _ ≤ (1 / 32) / k := div_le_div_of_nonneg_right hsmallU hk0.le
      _ = e := by dsimp [e]; ring
  have hW : Real.sqrt mW * Real.sqrt w * |lW| ≤ e := by
    calc
      _ ≤ 3 * B * L * Real.sqrt ε / k ^ 2 := by
        rw [mul_assoc]
        exact (mul_le_of_le_one_left (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)) hrootW1).trans hwLog
      _ ≤ 3 * B * k * Real.sqrt ε / k ^ 2 := by gcongr
      _ = (3 * B * Real.sqrt ε) / k := by field_simp
      _ ≤ (1 / 32) / k := div_le_div_of_nonneg_right hsmallW hk0.le
      _ = e := by dsimp [e]; ring
  have hratio : 1 - 3 * e ≤ (1 - 1 / (16 * k)) * dK := by
    calc
      _ ≤ (1 - 2 * e) * (1 - e) := by nlinarith only [sq_nonneg e]
      _ ≤ (1 - 2 * e) * dK := mul_le_mul_of_nonneg_left hdK (by linarith only [he1])
      _ = _ := by dsimp [e]; ring
  have hfinish {j m dj dlj dJ : ℝ} (hj : 0 ≤ j) (hm : 0 < m)
      (hdj : |dj| ≤ Real.sqrt j) (hd : dJ = m * (dj + j * dlj))
      (hsize : Real.sqrt m + Real.sqrt m * Real.sqrt j * |dlj| ≤ 1 - 3 * e) :
      |dJ| ≤ (1 - 1 / (16 * k)) * Real.sqrt (j * m) * dK := by
    have H := wall_multiplier_cone_bound hj hm (θ := 1) (by simpa only [one_mul] using hdj) hd
    simp only [mul_one] at H
    calc
      _ ≤ Real.sqrt (j * m) * (1 - 3 * e) :=
        H.trans (mul_le_mul_of_nonneg_left hsize (Real.sqrt_nonneg _))
      _ ≤ Real.sqrt (j * m) * ((1 - 1 / (16 * k)) * dK) :=
        mul_le_mul_of_nonneg_left hratio (Real.sqrt_nonneg _)
      _ = _ := by ring
  refine ⟨by linarith only [hdK, he1], hr, hfinish hu.1 hmU.1 ha hdU ?_, hfinish hw.1 hmW.1 hb hdW ?_⟩
  · linarith only [hrootU.trans (hstrongBase.trans hbase), hU]
  · linarith only [hrootW.trans hbase, hW]

end BianchiIX
