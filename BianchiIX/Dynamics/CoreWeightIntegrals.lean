import BianchiIX.Analysis.ClockWeightIntegrals
import BianchiIX.Dynamics.CoreEntryBounds

noncomputable section

namespace BianchiIX

open Set MeasureTheory

theorem coreRegion_cosh_bound {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) :
    Real.cosh (projectiveCoreAngle y) ≤ 101 / 100 * k := by
  have hv : 0 < y 2 := lt_of_lt_of_le zero_lt_one hy.2.1
  rw [projectiveCoreAngle, cosh_coreAngle hv]
  apply (div_le_iff₀ hv).mpr
  exact (coreRegion_radius_bounds hk hy).2.trans
    (le_mul_of_one_le_right (by linarith only [hk]) hy.2.1)

theorem coreRegion_inverse_wall_sq {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) :
    1 / y 2 ^ 2 ≤ (1 / (99 / 100 * k) ^ 2) * Real.cosh (projectiveCoreAngle y) ^ 2 := by
  have hv : 0 < y 2 := lt_of_lt_of_le zero_lt_one hy.2.1
  have hlo : 0 < 99 / 100 * k := by linarith only [hk]
  have hr := (coreRegion_radius_bounds hk hy).1
  have hR : 0 < coreRadius (y 0) (y 2) := hlo.trans_le hr
  have H := div_le_div_of_nonneg_left (sq_nonneg (Real.cosh (projectiveCoreAngle y)))
    (sq_pos_of_pos hlo) (sq_le_sq₀ hlo.le hR.le |>.mpr hr)
  have heq : Real.cosh (projectiveCoreAngle y) ^ 2 / coreRadius (y 0) (y 2) ^ 2 = 1 / y 2 ^ 2 := by
    rw [projectiveCoreAngle, cosh_coreAngle hv]
    field_simp
  rw [heq] at H
  convert! H using 1
  ring

/-- Strong-wall decay and the slow-wall weights (B.37), integrated against the actual angular rate. -/
theorem projectiveOriginalFlow_core_weight_integrals {y : ProjectiveState} {t₀ k a b : ℝ}
    (hk : 6 ≤ k) (hab : a ≤ b) (hD : 0 < projectiveStateDenom y)
    (hdom : Icc a b ⊆ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : ∀ t ∈ Icc a b, 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hcore : ∀ t ∈ Icc a b, coreRegion k (projectiveOriginalFlow y t₀ t)) :
    let β := projectiveOriginalFlow y t₀
    let rate := fun t => coreOriginalClockRate (β t)
    let P₀ := β a 2 * β a 3
    (∫ t in a..b, β t 1 * rate t) ≤ 4 * β a 1 / k ∧
      (∫ t in a..b, (1 / β t 2 ^ 2) * rate t) ≤ 2 * (101 / 99 : ℝ) ^ 2 ∧
      (∫ t in a..b, (β t 3 / (k * β t 2)) * rate t) ≤ 2 * (101 / 99 : ℝ) ^ 2 * P₀ / k ∧
      (∫ t in a..b, β t 3 ^ 2 * rate t) ≤ 2 * (101 / 99 : ℝ) ^ 2 * P₀ ^ 2 := by
  intro β rate P₀
  let θ := fun t => projectiveCoreAngle (β t)
  have hk0 : 0 < k := by linarith only [hk]
  have hlo : 0 < 99 / 100 * k := by positivity
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hP₀ : 0 ≤ P₀ := (hcore a ha).2.2.2.1
  have hV (t : ℝ) (ht : t ∈ Icc a b) : 0 < β t 2 :=
    lt_of_lt_of_le zero_lt_one (hcore t ht).2.1
  have hflow (t : ℝ) (ht : t ∈ Icc a b) := hasDerivAt_projectiveOriginalFlow_time hD (hdom ht) (hA t ht)
  have hθ (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt θ (rate t) t :=
    hasDerivAt_coreAngle_scaled (hflow t ht) (hV t ht)
  have hrate : ContinuousOn rate (Icc a b) := by
    intro t ht
    exact ((contDiffAt_coreOriginalClockRate 1 (hV t ht)
      (ne_of_gt (coreRegion_clock_regular hk (hcore t ht)).1)).continuousAt.comp
        (hflow t ht).continuousAt).continuousWithinAt
  have hpos (t : ℝ) (ht : t ∈ Icc a b) : 0 ≤ rate t :=
    (coreRegion_clock_regular hk (hcore t ht)).2.2.le
  have hc (i : Fin 4) : ContinuousOn (fun t => β t i) (Icc a b) :=
    fun t ht => (hasDerivAt_pi.mp (hflow t ht) i).continuousAt.continuousWithinAt
  have hInv : ContinuousOn (fun t => 1 / β t 2 ^ 2) (Icc a b) :=
    continuousOn_const.div ((hc 2).pow 2) (fun t ht => ne_of_gt (sq_pos_of_pos (hV t ht)))
  have hcon (t : ℝ) (ht : t ∈ Icc a b) :
      β t 1 ≤ β a 1 * Real.exp (-k * (θ t - θ a) / 4) ∧ β t 2 * β t 3 ≤ P₀ :=
    normalized_core_prefix_contraction hk (convex_Icc a b) hdom
      (fromProjectiveState_constraint (ne_of_gt hD)) hA ha ht ht.1
      (fun s hs => (coreRegion_radius_bounds hk (hcore s hs)).1)
      (fun s hs => (hcore s hs).2.1) (fun s hs => (coreRegion_wall_bounds (hcore s hs)).1)
      (fun s hs => (coreRegion_wall_bounds (hcore s hs)).2)
  have hweights := integral_clock_le_of_cosh_sq hab hθ hrate hpos
    (show 0 ≤ 1 / (99 / 100 * k) ^ 2 by positivity) hInv
    (fun t ht => coreRegion_inverse_wall_sq hk (hcore t ht))
    (coreRegion_cosh_bound hk (hcore a ha)) (coreRegion_cosh_bound hk (hcore b hb))
  have hweights' : (∫ t in a..b, (1 / β t 2 ^ 2) * rate t) ≤ 2 * (101 / 99 : ℝ) ^ 2 := by
    convert! hweights using 1
    field_simp
  refine ⟨?_, hweights', ?_, ?_⟩
  · have H := integral_clock_le_of_exp_decay hab hθ hrate hpos
      (show 0 < k / 4 by positivity) (hcore a ha).2.2.1.1 (hc 1)
      (fun t ht => by convert! (hcon t ht).1 using 1; congr 2; ring)
    convert! H using 1
    ring
  · have hcont := (hc 3).div (continuousOn_const.mul (hc 2))
      (fun t ht => ne_of_gt (mul_pos hk0 (hV t ht)))
    have H := intervalIntegral.integral_mono_on (μ := volume) hab
      ((hcont.mul hrate).intervalIntegrable_of_Icc hab)
      (((continuousOn_const (c := P₀ / k)).mul (hInv.mul hrate)).intervalIntegrable_of_Icc hab)
      (fun t ht => ?_)
    · simp only [Pi.mul_apply, Pi.div_apply] at H
      rw [intervalIntegral.integral_const_mul] at H
      exact H.trans ((mul_le_mul_of_nonneg_left hweights' (div_nonneg hP₀ hk0.le)).trans_eq (by ring))
    · have heq : β t 3 / (k * β t 2) = (β t 2 * β t 3 / k) * (1 / β t 2 ^ 2) := by
        field_simp
      change (β t 3 / (k * β t 2)) * rate t ≤ P₀ / k * ((1 / β t 2 ^ 2) * rate t)
      rw [heq]
      calc
        _ ≤ (P₀ / k * (1 / β t 2 ^ 2)) * rate t :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_right (hcon t ht).2 hk0.le) (by positivity)) (hpos t ht)
        _ = _ := by ring
  · have H := intervalIntegral.integral_mono_on (μ := volume) hab
      (((hc 3).pow 2 |>.mul hrate).intervalIntegrable_of_Icc hab)
      (((continuousOn_const (c := P₀ ^ 2)).mul (hInv.mul hrate)).intervalIntegrable_of_Icc hab)
      (fun t ht => ?_)
    · simp only [Pi.mul_apply, Pi.pow_apply] at H
      rw [intervalIntegral.integral_const_mul] at H
      exact H.trans ((mul_le_mul_of_nonneg_left hweights' (sq_nonneg P₀)).trans_eq (by ring))
    · have hw : β t 3 ≤ P₀ / β t 2 := (le_div_iff₀ (hV t ht)).mpr (by simpa only [mul_comm] using (hcon t ht).2)
      have hsq := (sq_le_sq₀ (coreRegion_wall_bounds (hcore t ht)).2.1 (div_nonneg hP₀ (hV t ht).le)).mpr hw
      calc
        β t 3 ^ 2 * rate t ≤ (P₀ / β t 2) ^ 2 * rate t := mul_le_mul_of_nonneg_right hsq (hpos t ht)
        _ = P₀ ^ 2 * ((1 / β t 2 ^ 2) * rate t) := by ring

/-- The slow-wall integral estimates hold for every admissible large-core first return. -/
theorem exists_large_core_weight_integrals {Y : CoreAngleState} (hk : 6 ≤ Y 0)
    (hu : 0 ≤ Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0)
    (hw : 0 ≤ Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0) :
    ∃ T > 0, IsLeast {t | 0 < t ∧ projectiveOriginalFlow (coreRadiusEntry Y) 0 t 2 = 1} T ∧
      let β := projectiveOriginalFlow (coreRadiusEntry Y) 0
      let rate := fun t => coreOriginalClockRate (β t)
      (∫ t in 0..T, β t 1 * rate t) ≤ 4 * Y 1 / Y 0 ∧
        (∫ t in 0..T, (1 / β t 2 ^ 2) * rate t) ≤ 2 * (101 / 99 : ℝ) ^ 2 ∧
        (∫ t in 0..T, (β t 3 / (Y 0 * β t 2)) * rate t) ≤ 2 * (101 / 99 : ℝ) ^ 2 * Y 2 / Y 0 ∧
        (∫ t in 0..T, β t 3 ^ 2 * rate t) ≤ 2 * (101 / 99 : ℝ) ^ 2 * Y 2 ^ 2 := by
  have hD : 0 < projectiveStateDenom (coreRadiusEntry Y) :=
    (coreRegion_clock_regular hk (coreRadiusEntry_region hk hu hw)).1
  have hc := fromProjectiveState_constraint (ne_of_gt hD)
  obtain ⟨T, hT, hfirst, hcore, _⟩ := exists_large_core_traversal hk hu hw
  refine ⟨T, hT, hfirst, ?_⟩
  have H := projectiveOriginalFlow_core_weight_integrals hk hT.le hD
    (fun s hs => normalizedMaxDomain_contains_Ici_of_constraint hc 0 hs.1)
    (fun s hs => (hcore s hs).1) (fun s hs => (hcore s hs).2)
  dsimp only at H
  rw [projectiveOriginalFlow_initial hD] at H
  simpa [coreRadiusEntry] using H

end BianchiIX
