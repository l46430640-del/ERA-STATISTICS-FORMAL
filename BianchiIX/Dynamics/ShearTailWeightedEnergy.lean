import BianchiIX.Dynamics.ShearTailMomentScale

noncomputable section

namespace BianchiIX

open Set

/-- Regional wall scales absorb one power of the waiting time in the energy. -/
theorem shearTail_energy_time_bound {a D t : ℝ} {z : NormalizedState}
    (ha : 0 < a ∧ a ≤ 1) (hD : 0 ≤ D) (ht : t ∈ Icc (0 : ℝ) (shearTailTime a D))
    (hn : 0 ≤ z 2 ∧ z 2 ≤ a ^ 2 * Real.exp (-2 * t))
    (hx : 0 ≤ z 3 ∧ z 3 ≤ a ^ 2)
    (hy : 0 ≤ z 4 ∧ z 4 ≤ a * Real.exp (-(a / 2) * t)) :
    shearTailEnergy z ≤ 5 * a ^ 2 ∧ t * shearTailEnergy z ≤ (3 + D) * a := by
  have ha2 : a ^ 2 ≤ a := by nlinarith only [ha.1, ha.2]
  have ha3 : a ^ 3 ≤ a ^ 2 := by
    nlinarith only [mul_le_mul_of_nonneg_left ha.2 (sq_nonneg a)]
  have ha4 : a ^ 4 ≤ a ^ 2 := by
    nlinarith only [pow_le_pow_left₀ (sq_nonneg a) ha2 2]
  have hEn : Real.exp (-2 * t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [ht.1])
  have hEy : Real.exp (-a * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith only [ha.1, ht.1])
  have hEyhalf : Real.exp (-(a / 2) * t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith only [ha.1, ht.1])
  have hn2 : z 2 ≤ a ^ 2 := hn.2.trans (mul_le_of_le_one_right (sq_nonneg a) hEn)
  have hy1 : z 4 ≤ a := hy.2.trans (mul_le_of_le_one_right ha.1.le hEyhalf)
  have HF : z 2 ^ 2 + z 2 * (z 3 + z 4) ≤ 3 * a ^ 3 * Real.exp (-2 * t) := by
    have H := mul_le_mul hn.2
      (show z 2 + z 3 + z 4 ≤ 3 * a by linarith only [hn2, hx.2, hy1, ha2])
      (by positivity [hn.1, hx.1, hy.1] : 0 ≤ z 2 + z 3 + z 4)
      (by positivity : 0 ≤ a ^ 2 * Real.exp (-2 * t))
    nlinarith only [H]
  have HX : z 3 ^ 2 ≤ a ^ 4 := by simpa only [← pow_mul] using pow_le_pow_left₀ hx.1 hx.2 2
  have HY : z 4 ^ 2 ≤ a ^ 2 * Real.exp (-a * t) := by
    have H := pow_le_pow_left₀ hy.1 hy.2 2
    have he : (a * Real.exp (-(a / 2) * t)) ^ 2 = a ^ 2 * Real.exp (-a * t) := by
      rw [mul_pow, pow_two (Real.exp _), ← Real.exp_add]
      congr 2
      ring
    rwa [he] at H
  have HB : shearTailEnergy z ≤
      3 * a ^ 3 * Real.exp (-2 * t) + a ^ 4 + a ^ 2 * Real.exp (-a * t) := by
    dsimp only [shearTailEnergy]
    linarith only [HF, HX, HY]
  constructor
  · have HF1 := mul_le_of_le_one_right (by positivity [ha.1] : 0 ≤ 3 * a ^ 3) hEn
    have HY1 := mul_le_of_le_one_right (sq_nonneg a) hEy
    nlinarith only [HB, HF1, HY1, ha3, ha4]
  · have Hexp (u : ℝ) : u * Real.exp (-u) ≤ 1 :=
      (Real.mul_exp_neg_le_exp_neg_one u).trans (Real.exp_le_one_iff.mpr (by norm_num))
    have HTF : t * (3 * a ^ 3 * Real.exp (-2 * t)) ≤ (3 / 2 : ℝ) * a ^ 3 := by
      have H := mul_le_mul_of_nonneg_left (Hexp (2 * t)) (by positivity [ha.1] : 0 ≤ 3 * a ^ 3 / 2)
      rw [← neg_mul] at H
      nlinarith only [H]
    have HTY : t * (a ^ 2 * Real.exp (-a * t)) ≤ a := by
      have H := mul_le_mul_of_nonneg_left (Hexp (a * t)) ha.1.le
      rw [← neg_mul] at H
      nlinarith only [H]
    have halog : a * Real.log (1 / a) ≤ 1 := by
      have H := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (one_div_pos.mpr ha.1)) ha.1.le
      have he : a * (1 / a - 1) = 1 - a := by field_simp [ha.1.ne']
      rw [he] at H
      linarith only [H, ha.1]
    have HTX : t * a ^ 4 ≤ D * a := by
      apply (mul_le_mul_of_nonneg_right ht.2 (pow_nonneg ha.1.le 4)).trans
      have he : shearTailTime a D * a ^ 4 = (D * a ^ 2) * (a * Real.log (1 / a)) := by
        dsimp only [shearTailTime]
        field_simp [ha.1.ne']
      rw [he]
      exact (mul_le_of_le_one_right (mul_nonneg hD (sq_nonneg a)) halog).trans
        (mul_le_mul_of_nonneg_left ha2 hD)
    nlinarith only [mul_le_mul_of_nonneg_left HB ht.1, HTF, HTY, HTX, ha3, ha2]

/-- The actual controlled prefix has uniformly bounded energy weighted by its logarithmic entrance size. -/
theorem shearTail_prefix_weighted_energy {a D C q L₀ : ℝ} {α : ℝ → NormalizedState}
    (ha : 0 < a ∧ a ≤ 1 / 256) (hD : 0 ≤ D) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hL₀ : 0 ≤ L₀ ∧ L₀ ≤ 2 + 4 * C * q * |Real.log a|)
    (hα : ∀ t ∈ Icc (0 : ℝ) (shearTailTime a D), HasDerivAt α (normalizedField (α t)) t)
    (hc : ∀ t ∈ Icc (0 : ℝ) (shearTailTime a D), stateConstraint (α t) = 1)
    (hn : ∀ t ∈ Icc (0 : ℝ) (shearTailTime a D), 0 ≤ α t 2 ∧ 0 ≤ α t 3 ∧ 0 ≤ α t 4)
    (hr : ∀ t ∈ Icc (0 : ℝ) (shearTailTime a D), shearTailRegion a (α t)) :
    ∀ t ∈ Icc (0 : ℝ) (shearTailTime a D),
      (L₀ + t) * shearTailEnergy (α t) ≤ (13 + 20 * C * q + D) * a := by
  have ha1 : a ≤ 1 := by linarith only [ha.2]
  have hT : 0 ≤ shearTailTime a D := mul_nonneg (div_nonneg hD ha.1.le)
    (Real.log_nonneg ((le_div_iff₀ ha.1).mpr (by simpa using ha1)))
  obtain ⟨_, _, _, hN, hX, hY⟩ := hr 0 ⟨le_rfl, hT⟩
  have HW := shearTail_prefix ha hα hc hn hr ⟨hN, hX, hY⟩
  have hlog : a * |Real.log a| ≤ 1 := by
    have H := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos ha.1) ha.1.le
    rw [mul_sub, mul_one, mul_inv_cancel₀ ha.1.ne'] at H
    rw [abs_of_nonpos (Real.log_nonpos ha.1.le ha1)]
    nlinarith only [H, ha.1]
  have HL : a * L₀ ≤ 2 + 4 * C * q := by
    have H := mul_le_mul_of_nonneg_left hL₀.2 ha.1.le
    have Hlog := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 4 * C * q)
    nlinarith only [H, Hlog, ha1]
  intro t ht
  have H := HW t ht
  have HB := shearTail_energy_time_bound ⟨ha.1, ha1⟩ hD ht
    ⟨(hn t ht).1, H.1⟩ ⟨(hn t ht).2.1, (hr t ht).2.2.2.2.1⟩
    ⟨(hn t ht).2.2, H.2.2.1.trans
      (mul_le_mul_of_nonneg_right (by linarith only [ha.1] : a / 16 ≤ a) (Real.exp_pos _).le)⟩
  have HBL := mul_le_mul_of_nonneg_left HB.1 hL₀.1
  have HLa := mul_le_mul_of_nonneg_left HL (by positivity [ha.1] : 0 ≤ 5 * a)
  nlinarith only [HB.2, HBL, HLa]

end BianchiIX
