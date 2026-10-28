import BianchiIX.Algebra.CoreCone

noncomputable section

namespace BianchiIX

theorem core_cone_slope_size {k ε u w a b θ : ℝ} (hk : 6 ≤ k) (hε : 0 ≤ ε)
    (hu : 0 ≤ u ∧ u ≤ ε / k) (hw : 0 ≤ w ∧ w ≤ ε / k) (hθ : 0 ≤ θ)
    (ha : |a| ≤ θ * Real.sqrt u) (hb : |b| ≤ θ * Real.sqrt w) :
    let Q := 1 + k * |a| + |b|
    Real.sqrt u * Q ≤ Real.sqrt u + 2 * ε * θ ∧
      Real.sqrt w * Q ≤ Real.sqrt w + 2 * ε * θ := by
  intro Q
  have hk0 : 0 < k := by linarith only [hk]
  have hku : k * u ≤ ε := by simpa only [mul_comm] using (le_div_iff₀ hk0).mp hu.2
  have hwe : w ≤ ε := hw.2.trans (div_le_self hε (by linarith only [hk]))
  have hsu2 := Real.sq_sqrt hu.1
  have hsw2 := Real.sq_sqrt hw.1
  have hcross : Real.sqrt u * Real.sqrt w ≤ ε / k := by
    nlinarith only [hsu2, hsw2, hu.2, hw.2, sq_nonneg (Real.sqrt u - Real.sqrt w)]
  have hkcross : k * (Real.sqrt u * Real.sqrt w) ≤ ε := by
    simpa only [mul_comm] using (le_div_iff₀ hk0).mp hcross
  have hcross' : Real.sqrt u * Real.sqrt w ≤ ε :=
    hcross.trans (div_le_self hε (by linarith only [hk]))
  have hQ : Q ≤ 1 + θ * (k * Real.sqrt u + Real.sqrt w) := by
    have H := mul_le_mul_of_nonneg_left ha hk0.le
    dsimp [Q]
    nlinarith only [H, hb]
  constructor
  · calc
      _ ≤ Real.sqrt u * (1 + θ * (k * Real.sqrt u + Real.sqrt w)) :=
        mul_le_mul_of_nonneg_left hQ (Real.sqrt_nonneg _)
      _ = Real.sqrt u + θ * (k * u + Real.sqrt u * Real.sqrt w) := by
        have H : Real.sqrt u * (1 + θ * (k * Real.sqrt u + Real.sqrt w)) =
            Real.sqrt u + θ * (k * (Real.sqrt u) ^ 2 + Real.sqrt u * Real.sqrt w) := by ring
        rw [H, hsu2]
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hku hθ,
        mul_le_mul_of_nonneg_left hcross' hθ]
  · calc
      _ ≤ Real.sqrt w * (1 + θ * (k * Real.sqrt u + Real.sqrt w)) :=
        mul_le_mul_of_nonneg_left hQ (Real.sqrt_nonneg _)
      _ = Real.sqrt w + θ * (k * (Real.sqrt u * Real.sqrt w) + w) := by
        have H : Real.sqrt w * (1 + θ * (k * Real.sqrt u + Real.sqrt w)) =
            Real.sqrt w + θ * (k * (Real.sqrt u * Real.sqrt w) + (Real.sqrt w) ^ 2) := by ring
        rw [H, hsw2]
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hkcross hθ,
        mul_le_mul_of_nonneg_left hwe hθ]

/-- The radial error vanishes with the actual wall sum, rather than just its fixed upper bound. -/
theorem core_cone_radius_size {k ε u w a b : ℝ} (hk : 6 ≤ k)
    (hε : 0 ≤ ε ∧ ε ≤ 1) (hu : 0 ≤ u ∧ u ≤ ε / k) (hw : 0 ≤ w ∧ w ≤ ε / k)
    (ha : |a| ≤ Real.sqrt u) (hb : |b| ≤ Real.sqrt w) :
    Real.sqrt u + (u + w) * (1 + k * |a| + |b|) ≤ 5 * Real.sqrt (u + w) := by
  let B := u + w
  have hε0 := hε.1
  have hk0 : 0 < k := by linarith only [hk]
  have hB0 : 0 ≤ B := add_nonneg hu.1 hw.1
  have hkB : k * B ≤ 2 * ε := by
    have H := (le_div_iff₀ hk0).mp hu.2
    have H' := (le_div_iff₀ hk0).mp hw.2
    dsimp [B]
    nlinarith only [H, H']
  have hB1 : B ≤ 1 := by nlinarith only [hkB, hε.2, hk, hB0]
  have hsB : B ≤ Real.sqrt B := by
    have H := Real.sq_sqrt hB0
    have H' : Real.sqrt B ≤ 1 := by simpa using Real.sqrt_le_sqrt hB1
    nlinarith only [H, H', Real.sqrt_nonneg B]
  have hsu : Real.sqrt u ≤ Real.sqrt B := Real.sqrt_le_sqrt (by dsimp [B]; linarith only [hw.1])
  have hsw : Real.sqrt w ≤ Real.sqrt B := Real.sqrt_le_sqrt (by dsimp [B]; linarith only [hu.1])
  have hQ : 1 + k * |a| + |b| ≤ 1 + k * Real.sqrt u + Real.sqrt w := by
    nlinarith only [mul_le_mul_of_nonneg_left ha hk0.le, hb]
  calc
    _ ≤ Real.sqrt B + B * (1 + k * Real.sqrt u + Real.sqrt w) :=
      add_le_add hsu (mul_le_mul_of_nonneg_left hQ hB0)
    _ = Real.sqrt B + B + (k * B) * Real.sqrt u + B * Real.sqrt w := by ring
    _ ≤ Real.sqrt B + Real.sqrt B + (2 * ε) * Real.sqrt B + 1 * Real.sqrt B := by
      gcongr
    _ ≤ 5 * Real.sqrt B := by
      nlinarith only [mul_le_mul_of_nonneg_right hε.2 (Real.sqrt_nonneg B)]

theorem core_cone_slope_bound {k ε u w a b θ A B mU mW lU lW dK dU dW : ℝ}
    (hk : 6 ≤ k) (hε : 0 ≤ ε ∧ ε ≤ 1)
    (hu : 0 ≤ u ∧ u ≤ ε / k) (hw : 0 ≤ w ∧ w ≤ ε / k)
    (hθ : 0 ≤ θ) (ha : |a| ≤ θ * Real.sqrt u) (hb : |b| ≤ θ * Real.sqrt w)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hK : 3 / 4 ≤ dK)
    (hmU : 0 < mU ∧ mU ≤ Real.exp (-k / 40))
    (hmW : 0 < mW ∧ mW ≤ Real.exp (-1 / (2 * k)))
    (hlogU : |lU| ≤ A * Real.log (4 * k) * (1 + k * |a| + |b|))
    (hlogW : |lW| ≤ B * Real.log (4 * k) * (1 + k * |a| + |b|) / k ^ 2)
    (hdU : dU = mU * (a + u * lU)) (hdW : dW = mW * (b + w * lW)) :
    let C := 2 * (1 + 12800 * A + 2 * B)
    let S := Real.sqrt (u + w) * Real.log (4 * k) / k ^ 2
    |dU| ≤ C * (θ + S) * Real.sqrt (u * mU) * dK ∧
      |dW| ≤ C * (θ + S) * Real.sqrt (w * mW) * dK := by
  intro C S
  let Q := 1 + k * |a| + |b|
  let L := Real.log (4 * k)
  let E := Real.exp (-k / 80)
  let C₀ := 1 + 12800 * A + 2 * B
  have hε0 := hε.1
  have hε1 := hε.2
  have hk0 : 0 < k := by linarith only [hk]
  have hL : 0 ≤ L := Real.log_nonneg (by linarith only [hk])
  have hLk : L ≤ k := core_log_bound hk
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hE1 : E ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hk])
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  have hsu := Real.sqrt_le_sqrt (show u ≤ u + w by linarith only [hw.1])
  have hsw := Real.sqrt_le_sqrt (show w ≤ u + w by linarith only [hu.1])
  obtain ⟨huQ, hwQ⟩ := core_cone_slope_size hk hε.1 hu hw hθ ha hb
  have hrootU : Real.sqrt mU ≤ E := by
    convert! sqrt_le_exp_half hmU.2 using 1
    dsimp [E]
    congr 1
    ring
  have hrootW : Real.sqrt mW ≤ 1 := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by norm_num, ?_⟩
    have H : Real.exp (-1 / (2 * k)) ≤ 1 := Real.exp_le_one_iff.mpr
      (div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity))
    simpa only [one_pow] using hmW.2.trans H
  have hphaseU : E * L * Real.sqrt u ≤ 12800 * S := by
    have H := core_strong_exp_budget hk0.le
    have HE : E ≤ 12800 / k ^ 2 := (le_div_iff₀ (sq_pos_of_pos hk0)).mpr (by nlinarith only [H])
    calc
      _ ≤ (12800 / k ^ 2) * L * Real.sqrt (u + w) := by gcongr
      _ = _ := by dsimp [S, L]; ring
  have hslopeU : 2 * ε * E * L ≤ 12800 := by
    calc
      _ ≤ 2 * 1 * E * k := by gcongr
      _ ≤ k ^ 2 * E := by nlinarith only [mul_nonneg hE (show 0 ≤ k ^ 2 - 2 * k by nlinarith only [hk])]
      _ ≤ 12800 := core_strong_exp_budget hk0.le
  have hphaseW : L * Real.sqrt w / k ^ 2 ≤ S := by
    calc
      _ ≤ L * Real.sqrt (u + w) / k ^ 2 := by gcongr
      _ = _ := by dsimp [S, L]; ring
  have hslopeW : 2 * ε * L / k ^ 2 ≤ 2 := by
    calc
      _ ≤ 2 * 1 * k / k ^ 2 := by gcongr
      _ = 2 / k := by field_simp
      _ ≤ 2 := (div_le_iff₀ hk0).mpr (by linarith only [hk])
  have huLog : Real.sqrt u * |lU| ≤ A * L * (Real.sqrt u + 2 * ε * θ) := by
    calc
      _ ≤ Real.sqrt u * (A * L * Q) := mul_le_mul_of_nonneg_left hlogU (Real.sqrt_nonneg _)
      _ = A * L * (Real.sqrt u * Q) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left huQ (mul_nonneg hA hL)
  have hwLog : Real.sqrt w * |lW| ≤ (B * L / k ^ 2) * (Real.sqrt w + 2 * ε * θ) := by
    calc
      _ ≤ Real.sqrt w * (B * L * Q / k ^ 2) := mul_le_mul_of_nonneg_left hlogW (Real.sqrt_nonneg _)
      _ = (B * L / k ^ 2) * (Real.sqrt w * Q) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hwQ (by positivity)
  have hU : Real.sqrt mU * θ + Real.sqrt mU * Real.sqrt u * |lU| ≤ C₀ * (θ + S) := by
    calc
      _ ≤ θ + E * (A * L * (Real.sqrt u + 2 * ε * θ)) := by
        apply add_le_add (mul_le_of_le_one_left hθ (hrootU.trans hE1))
        rw [mul_assoc]
        exact mul_le_mul hrootU huLog (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)) hE
      _ = θ + A * (E * L * Real.sqrt u) + A * θ * (2 * ε * E * L) := by ring
      _ ≤ θ + A * (12800 * S) + A * θ * 12800 := by gcongr
      _ = (1 + 12800 * A) * θ + (12800 * A) * S := by ring
      _ ≤ C₀ * θ + C₀ * S := by
        apply add_le_add <;> apply mul_le_mul_of_nonneg_right _ (by assumption)
        all_goals dsimp [C₀]; linarith only [hA, hB]
      _ = _ := by ring
  have hW : Real.sqrt mW * θ + Real.sqrt mW * Real.sqrt w * |lW| ≤ C₀ * (θ + S) := by
    calc
      _ ≤ θ + (B * L / k ^ 2) * (Real.sqrt w + 2 * ε * θ) := by
        apply add_le_add (mul_le_of_le_one_left hθ hrootW)
        rw [mul_assoc]
        exact (mul_le_of_le_one_left (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)) hrootW).trans hwLog
      _ = θ + B * (L * Real.sqrt w / k ^ 2) + B * θ * (2 * ε * L / k ^ 2) := by ring
      _ ≤ θ + B * S + B * θ * 2 := by gcongr
      _ = (1 + 2 * B) * θ + B * S := by ring
      _ ≤ C₀ * θ + C₀ * S := by
        apply add_le_add <;> apply mul_le_mul_of_nonneg_right _ (by assumption)
        all_goals dsimp [C₀]; linarith only [hA, hB]
      _ = _ := by ring
  have hfinish {j m dj dlj dJ : ℝ} (hj : 0 ≤ j) (hm : 0 < m)
      (hdj : |dj| ≤ θ * Real.sqrt j) (hd : dJ = m * (dj + j * dlj))
      (hsize : Real.sqrt m * θ + Real.sqrt m * Real.sqrt j * |dlj| ≤ C₀ * (θ + S)) :
      |dJ| ≤ C * (θ + S) * Real.sqrt (j * m) * dK := by
    have H := wall_multiplier_cone_bound hj hm hdj hd
    calc
      _ ≤ Real.sqrt (j * m) * (C₀ * (θ + S)) :=
        H.trans (mul_le_mul_of_nonneg_left hsize (Real.sqrt_nonneg _))
      _ ≤ (Real.sqrt (j * m) * (C₀ * (θ + S))) * (2 * dK) :=
        le_mul_of_one_le_right (by positivity) (by linarith only [hK])
      _ = _ := by dsimp [C, C₀]; ring
  exact ⟨hfinish hu.1 hmU.1 ha hdU hU, hfinish hw.1 hmW.1 hb hdW hW⟩

end BianchiIX
