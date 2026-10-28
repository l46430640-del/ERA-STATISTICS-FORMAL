import BianchiIX.Dynamics.EntranceReturnDecay

noncomputable section

namespace BianchiIX

open Set

/-- The compact entrance has the stronger weak-wall rate used in (B.51). -/
theorem entranceRegion_compact_weak_rate {k : ℝ} {y : ProjectiveState}
    (hk : 7 / 4 ≤ k) (hk4 : k ≤ 4) (hy : entranceRegion k y) :
    (-y 0 - 1 - coupling (y 1) (y 2) (y 3)) / entranceClockRate y ≤ -(13 / 9) := by
  have hD := entranceRegion_clock_pos hk hy
  have hDhi : entranceClockRate y ≤ 21 / 5 := by
    linarith only [(entranceRegion_speed hk hy).2, hk4]
  have hC := (connection_coupling_bounds hy.2.2.1.1 hy.2.2.2.1
    ⟨hy.2.2.2.2.1, by linarith [hy.2.2.2.2.2]⟩).1
  have hU : (y 1) ^ 2 ≤ (1 / 10000 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hy.2.2.1.1 hy.2.2.1.2 2
  have hfrac : 4 / 9 ≤ 2 * (1 + coupling (y 1) (y 2) (y 3)) / entranceClockRate y := by
    apply (le_div_iff₀ hD).mpr
    nlinarith only [hC, hU, hDhi]
  have hid := (connection_clock_identities hD.ne').1
  change (-y 0 - 1 - coupling (y 1) (y 2) (y 3)) / entranceClockRate y =
    -1 - 2 * (1 + coupling (y 1) (y 2) (y 3)) / entranceClockRate y at hid
  linarith only [hid, hfrac]

theorem scaled_compact_entrance_weak_decay {Y : ℝ → ProjectiveState} {a : ℝ → ℝ} {s t k : ℝ}
    (hk : 7 / 4 ≤ k) (hk4 : k ≤ 4)
    (hY : ∀ r ∈ Icc s t, HasDerivAt Y (a r • projectiveField (Y r)) r)
    (ha : ∀ r ∈ Icc s t, 0 ≤ a r) (hy : ∀ r ∈ Icc s t, entranceRegion k (Y r))
    (hv : ∀ r ∈ Icc s t, 0 < Y r 2) :
    ∀ r ∈ Icc s t, |Y r 3| ≤ |Y s 3| *
      Real.exp (-(13 / 9) * (Real.log (Y r 2) - Real.log (Y s 2))) := by
  let q := fun r => a r * entranceClockRate (Y r)
  have hz (r : ℝ) (hr : r ∈ Icc s t) :
      HasDerivAt (fun r => Real.log (Y r 2)) (q r) r :=
    hasDerivAt_entranceLog_scaled (hY r hr) (hv r hr).ne'
  have hW (r : ℝ) (hr : r ∈ Icc s t) :
      HasDerivAt (fun b => Y b 3)
        (q r * ((-Y r 0 - 1 - coupling (Y r 1) (Y r 2) (Y r 3)) /
          entranceClockRate (Y r) * Y r 3)) r := by
    have hD := (entranceRegion_clock_pos hk (hy r hr)).ne'
    convert! hasDerivAt_pi.mp (hY r hr) 3 using 1
    change _ = a r * weakVelocity (Y r 0) (Y r 1) (Y r 2) (Y r 3)
    dsimp [q, weakVelocity]
    field_simp
  exact abs_le_exp_of_clock_damping hW hz
    (fun r hr => mul_nonneg (ha r hr) (entranceRegion_clock_pos hk (hy r hr)).le)
    (fun r hr => entranceRegion_compact_weak_rate hk hk4 (hy r hr))

/-- Both compact-connection powers are estimates on the actual first return. -/
theorem entranceReturn_compact_decay {y : ProjectiveState}
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hk4 : coreRadius (y 0) (y 2) ≤ 4) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) :
    entranceReturnState y 1 ≤ y 1 * (y 2) ^ (19 / 12 : ℝ) ∧
      entranceReturnState y 3 ≤ y 3 * (y 2) ^ (13 / 9 : ℝ) := by
  let x := fromProjectiveState y
  let T := entranceReturnTime y
  let Y := projectiveOriginalFlow y 0
  have hD := entrance_initial_denom_pos hk hm hu hv hw
  have hc := fromProjectiveState_constraint hD.ne'
  have HR := (entranceReturn_regular hk hm hu hv hw).1
  have hT : 0 ≤ T := HR.1.1.1.le
  have hinit : Y 0 = y := projectiveOriginalFlow_initial hD 0
  have hreg := entranceReturn_region hk hm hu hv hw
  have hY (r : ℝ) (hr : r ∈ Icc 0 T) :
      HasDerivAt Y (normalizedProjectiveRate x 0 r • projectiveField (Y r)) r := by
    have H := normalizedMaxCurve_forward_of_constraint hc hr.1
    exact hasDerivAt_toProjectiveState_normalized H.1 (HR.2.1 r hr).2.ne' H.2.1
  have hV (r : ℝ) (hr : r ∈ Icc 0 T) : 0 < Y r 2 := by
    apply normalized_projective_wall_pos (HR.2.1 0 ⟨le_rfl, hT⟩).1 (HR.2.1 r hr).1
      (HR.2.1 0 ⟨le_rfl, hT⟩).2 (HR.2.1 r hr).2 1
    change 0 < Y 0 2
    rw [hinit]
    exact hv.1
  have H := scaled_compact_entrance_weak_decay hk hk4 hY
    (fun r hr => (HR.2.1 r hr).2.le) hreg hV T ⟨hT, le_rfl⟩
  change |entranceReturnState y 3| ≤ |Y 0 3| *
    Real.exp (-(13 / 9) * (Real.log (entranceReturnState y 2) - Real.log (Y 0 2))) at H
  rw [hinit, (entranceReturn_active_component hk hm hu hv hw).1, Real.log_one,
    zero_sub, abs_of_nonneg hw.1] at H
  have hpow (p : ℝ) : Real.exp (-p * -Real.log (y 2)) = (y 2) ^ p := by
    rw [Real.rpow_def_of_pos hv.1]
    congr 1
    ring
  rw [hpow] at H
  have hstrong := (entranceReturn_decay hk hm hu hv hw).1
  have hlog : Real.log (y 2) ≤ 0 := Real.log_nonpos hv.1.le hv.2.le
  have hexp : y 2 * Real.exp (-coreRadius (y 0) (y 2) * -Real.log (y 2) / 3) ≤
      (y 2) ^ (19 / 12 : ℝ) := by
    conv_lhs => lhs; rw [← Real.exp_log hv.1]
    rw [← Real.exp_add, Real.rpow_def_of_pos hv.1]
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hk) hlog]
  exact ⟨hstrong.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hexp hu.1),
    (le_abs_self _).trans H⟩

end BianchiIX
