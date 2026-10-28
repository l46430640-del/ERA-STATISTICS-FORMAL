import BianchiIX.Algebra.EntranceArcRate
import BianchiIX.Dynamics.EntranceErrorIntegrals
import BianchiIX.Analysis.ScalarMultiplier

noncomputable section

namespace BianchiIX

open Set MeasureTheory

theorem scaled_entrance_strong_rate_integral {Y : ℝ → ProjectiveState} {a : ℝ → ℝ} {s t k : ℝ}
    (hk : 7 / 4 ≤ k) (hst : s ≤ t)
    (hY : ∀ r ∈ Icc s t, HasDerivAt Y (a r • projectiveField (Y r)) r)
    (hac : ContinuousOn a (Icc s t)) (ha : ∀ r ∈ Icc s t, 0 ≤ a r)
    (hy : ∀ r ∈ Icc s t, entranceRegion k (Y r)) (hv : ∀ r ∈ Icc s t, 0 < Y r 2) :
    (∫ r in s..t, a r * connectionStrongRate (Y r 0) (Y r 1) (Y r 2) (Y r 3)) ≤
      -(1 + 99 * k / 200) * (Real.log (Y t 2) - Real.log (Y s 2)) +
        (2 * Y s 3 + 3 * (Y s 1) ^ 2) / k := by
  let z := fun r => Real.log (Y r 2)
  let q := fun r => a r * entranceClockRate (Y r)
  let c := 1 + 99 * k / 200
  let b := fun r => a r * connectionStrongRate (Y r 0) (Y r 1) (Y r 2) (Y r 3)
  have hk0 : 0 < k := by linarith
  have hcoord (i : Fin 4) : ContinuousOn (fun r => Y r i) (Icc s t) :=
    (continuous_apply i).comp_continuousOn (HasDerivAt.continuousOn hY)
  have hbc : ContinuousOn b (Icc s t) := by
    apply hac.mul
    unfold connectionStrongRate
    fun_prop
  have hqc : ContinuousOn q (Icc s t) := hac.mul
    (continuous_entranceClockRate.comp_continuousOn (HasDerivAt.continuousOn hY))
  have hwc : ContinuousOn (fun r => Y r 3 * q r) (Icc s t) := (hcoord 3).mul hqc
  have huc : ContinuousOn (fun r => (Y r 1) ^ 2 * q r) (Icc s t) := ((hcoord 1).pow 2).mul hqc
  have hz (r : ℝ) (hr : r ∈ Icc s t) : HasDerivAt z (q r) r :=
    hasDerivAt_entranceLog_scaled (hY r hr) (hv r hr).ne'
  have hqeq : (∫ r in s..t, q r) = z t - z s :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r hr => hz r (uIcc_of_le hst ▸ hr)) (hqc.intervalIntegrable_of_Icc hst)
  have hbd (r : ℝ) (hr : r ∈ Icc s t) :
      b r ≤ -c * q r + (2 / k) * (Y r 3 * q r) + 2 * ((Y r 1) ^ 2 * q r) := by
    have hD := entranceRegion_clock_pos hk (hy r hr)
    have H := entrance_strong_arc_rate hk (hy r hr).1 (hy r hr).2.1
      (hy r hr).2.2.1 (hy r hr).2.2.2.1 (hy r hr).2.2.2.2
    have hq : 0 ≤ q r := mul_nonneg (ha r hr) hD.le
    have J := mul_le_mul_of_nonneg_left H hq
    have heq : b r = q r * (connectionStrongRate (Y r 0) (Y r 1) (Y r 2) (Y r 3) / entranceClockRate (Y r)) := by
      dsimp [b, q]
      field_simp
    rw [heq]
    convert! J using 1
    dsimp [c]
    ring
  have H := intervalIntegral.integral_mono_on (μ := volume) hst (hbc.intervalIntegrable_of_Icc hst)
    (((hqc.const_mul (-c)).add (hwc.const_mul (2 / k)) |>.add (huc.const_mul 2)).intervalIntegrable_of_Icc hst) hbd
  simp only [Pi.add_apply] at H
  have hsum : ContinuousOn (fun r => -c * q r + (2 / k) * (Y r 3 * q r)) (Icc s t) :=
    (hqc.const_mul (-c)).add (hwc.const_mul (2 / k))
  rw [intervalIntegral.integral_add
      (hsum.intervalIntegrable_of_Icc hst)
      ((huc.const_mul 2).intervalIntegrable_of_Icc hst),
    intervalIntegral.integral_add ((hqc.const_mul (-c)).intervalIntegrable_of_Icc hst)
      ((hwc.const_mul (2 / k)).intervalIntegrable_of_Icc hst),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, hqeq] at H
  have hi := scaled_entrance_error_integrals hk hst hY hac ha hy hv
  have J := add_le_add
    (add_le_add (le_refl (-c * (z t - z s)))
      (mul_le_mul_of_nonneg_left hi.1 (show 0 ≤ 2 / k by positivity)))
    (mul_le_mul_of_nonneg_left hi.2 (by norm_num : (0 : ℝ) ≤ 2))
  apply H.trans (J.trans_eq ?_)
  dsimp [c, z]
  ring

theorem scaled_entrance_arc_decay {Y : ℝ → ProjectiveState} {a : ℝ → ℝ} {s t k : ℝ}
    (hk : 7 / 4 ≤ k) (hst : s ≤ t)
    (hY : ∀ r ∈ Icc s t, HasDerivAt Y (a r • projectiveField (Y r)) r)
    (hac : ContinuousOn a (Icc s t)) (ha : ∀ r ∈ Icc s t, 0 ≤ a r)
    (hy : ∀ r ∈ Icc s t, entranceRegion k (Y r)) (hv : ∀ r ∈ Icc s t, 0 < Y r 2) :
    Y t 1 ≤ Y s 1 * Real.exp ((2 * Y s 3 + 3 * (Y s 1) ^ 2) / k) *
      Real.exp (-(1 + 99 * k / 200) * (Real.log (Y t 2) - Real.log (Y s 2))) := by
  let b := fun r => a r * connectionStrongRate (Y r 0) (Y r 1) (Y r 2) (Y r 3)
  have hcoord (i : Fin 4) : ContinuousOn (fun r => Y r i) (Icc s t) :=
    (continuous_apply i).comp_continuousOn (HasDerivAt.continuousOn hY)
  have hbc : ContinuousOn b (Icc s t) := by
    apply hac.mul
    unfold connectionStrongRate
    fun_prop
  have heq : Y t 1 = Y s 1 * Real.exp (∫ r in s..t, b r) := by
    apply homogeneous_solution_eq_exp_integral_Icc hst hbc (hcoord 1)
    intro r hr
    convert! hasDerivAt_pi.mp (hY r (Ioo_subset_Icc_self hr)) 1 using 1
    change _ = a r * strongVelocity _ _ _ _
    dsimp [b, connectionStrongRate, strongVelocity]
    ring
  rw [heq]
  have H := mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (scaled_entrance_strong_rate_integral hk hst hY hac ha hy hv)) (hy s ⟨le_rfl, hst⟩).2.2.1.1
  apply H.trans_eq
  rw [Real.exp_add]
  ring

theorem normalized_entrance_arc_decay {x : NormalizedState} {t₀ s t k : ℝ}
    (hc : stateConstraint x = 1) (hk : 7 / 4 ≤ k) (hs : t₀ ≤ s) (hst : s ≤ t)
    (hA : ∀ r ∈ Icc s t, 0 < normalizedProjectiveRate x t₀ r) :
    let Y := fun r => toProjectiveState (normalizedMaxCurve x t₀ r)
    (∀ r ∈ Icc s t, entranceRegion k (Y r)) → 0 < Y s 2 →
    Y t 1 ≤ Y s 1 * Real.exp ((2 * Y s 3 + 3 * (Y s 1) ^ 2) / k) *
      Real.exp (-(1 + 99 * k / 200) * (Real.log (Y t 2) - Real.log (Y s 2))) := by
  intro Y hy hvs
  have hsm : s ∈ Icc s t := ⟨le_rfl, hst⟩
  have hdom (r : ℝ) (hr : s ≤ r) := normalizedMaxDomain_contains_Ici_of_constraint hc t₀ (hs.trans hr)
  have hY (r : ℝ) (hr : r ∈ Icc s t) : HasDerivAt Y
      (normalizedProjectiveRate x t₀ r • projectiveField (Y r)) r := by
    have H := normalizedMaxCurve_forward_of_constraint hc (hs.trans hr.1)
    exact hasDerivAt_toProjectiveState_normalized H.1 (hA r hr).ne' H.2.1
  have hv (r : ℝ) (hr : r ∈ Icc s t) : 0 < Y r 2 :=
    normalized_projective_wall_pos (hdom s le_rfl) (hdom r hr.1) (hA s hsm) (hA r hr) 1 hvs
  have hac : ContinuousOn (normalizedProjectiveRate x t₀) (Icc s t) :=
    (continuousOn_normalizedProjectiveRate x t₀).mono (fun r hr => hdom r hr.1)
  exact scaled_entrance_arc_decay hk hst hY hac (fun r hr => (hA r hr).le) hy hv

end BianchiIX
