import BianchiIX.Dynamics.EntranceReturnDecay

noncomputable section

namespace BianchiIX

open Set

theorem entranceReturn_walls_nonincreasing {y : ProjectiveState}
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) :
    entranceReturnState y 1 ≤ y 1 ∧ entranceReturnState y 3 ≤ y 3 := by
  have H := entranceReturn_decay hk hm hu hv hw
  have hk0 : 0 < coreRadius (y 0) (y 2) := by linarith only [hk]
  have hL : 0 ≤ -Real.log (y 2) := neg_nonneg.mpr (Real.log_nonpos hv.1.le hv.2.le)
  have hEs : Real.exp (-coreRadius (y 0) (y 2) * -Real.log (y 2) / 3) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hk0.le) hL) (by norm_num))
  have hEw : Real.exp (-(-Real.log (y 2)) / coreRadius (y 0) (y 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hL) hk0.le)
  constructor
  · exact H.1.trans ((mul_le_mul_of_nonneg_left hEs (mul_nonneg hu.1 hv.1.le)).trans
      (by nlinarith only [mul_le_mul_of_nonneg_left hv.2.le hu.1]))
  · exact H.2.trans ((mul_le_mul_of_nonneg_left hEw (mul_nonneg hw.1 hv.1.le)).trans
      (by nlinarith only [mul_le_mul_of_nonneg_left hv.2.le hw.1]))

/-- The entrance power budget already implies the sixteenth-power core wall bounds. -/
theorem entranceReturn_core_wall_budget {y : ProjectiveState} {ε : ℝ} {q : ℕ} (hq : 16 ≤ q)
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 < y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 < y 3 ∧ y 3 ≤ 1 / 10000)
    (hup : y 1 * coreRadius (y 0) (y 2) ^ q ≤ ε / 2)
    (hwp : y 3 * coreRadius (y 0) (y 2) ^ q ≤ ε / 2) :
    let k := coreRadius (y 0) (y 2)
    let κ := coreRadius (entranceReturnState y 0) (entranceReturnState y 2)
    99 / 100 * k ≤ κ ∧ κ ≤ 101 / 100 * k ∧
      (0 < entranceReturnState y 1 ∧ entranceReturnState y 1 ≤ ε / κ ^ 16) ∧
      (0 < entranceReturnState y 3 ∧ entranceReturnState y 3 ≤ ε / κ ^ 16) := by
  intro k κ
  have HV := (entranceReturn_regular hk hm ⟨hu.1.le, hu.2⟩ hv ⟨hw.1.le, hw.2⟩).1
  have ht : entranceReturnTime y ∈ Icc 0 (entranceReturnTime y) := ⟨HV.1.1.1.le, le_rfl⟩
  have HR := (entranceReturn_region hk hm ⟨hu.1.le, hu.2⟩ hv ⟨hw.1.le, hw.2⟩ _ ht).2.1
  change |κ - k| ≤ k / 100 at HR
  have hκ : 99 / 100 * k ≤ κ ∧ κ ≤ 101 / 100 * k := by constructor <;> linarith only [(abs_le.mp HR).1, (abs_le.mp HR).2]
  have hk1 : 1 ≤ k := by linarith only [hk]
  have hk0 : 0 < k := by linarith only [hk1]
  have hκ0 : 0 < κ := lt_of_lt_of_le (mul_pos (by norm_num) hk0) hκ.1
  have HP := entranceReturn_walls_pos hk hm hu hv hw _ ht
  have HN := entranceReturn_walls_nonincreasing hk hm ⟨hu.1.le, hu.2⟩ hv ⟨hw.1.le, hw.2⟩
  have hkp : k ^ 16 ≤ k ^ q := pow_le_pow_right₀ hk1 hq
  have hκp : κ ^ 16 ≤ 2 * k ^ q := by
    calc
      _ ≤ (101 / 100 * k) ^ 16 := pow_le_pow_left₀ hκ0.le hκ.2 16
      _ = (101 / 100 : ℝ) ^ 16 * k ^ 16 := mul_pow _ _ _
      _ ≤ 2 * k ^ 16 := mul_le_mul_of_nonneg_right (by norm_num : (101 / 100 : ℝ) ^ 16 ≤ 2) (pow_nonneg hk0.le 16)
      _ ≤ _ := mul_le_mul_of_nonneg_left hkp (by norm_num)
  have hwall {a a₀ : ℝ} (ha : 0 < a) (ha₀ : 0 < a₀) (hN : a ≤ a₀) (hP : a₀ * k ^ q ≤ ε / 2) :
      a ≤ ε / κ ^ 16 := by
    apply (le_div_iff₀ (pow_pos hκ0 16)).mpr
    have H1 := mul_le_mul_of_nonneg_right hN (pow_nonneg hκ0.le 16)
    have H2 := mul_le_mul_of_nonneg_left hκp ha₀.le
    nlinarith only [H1, H2, hP]
  exact ⟨hκ.1, hκ.2, ⟨HP.1, hwall HP.1 hu.1 HN.1 hup⟩, ⟨HP.2.2, hwall HP.2.2 hw.1 HN.2 hwp⟩⟩

end BianchiIX
