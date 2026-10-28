import BianchiIX.Analysis.DampedForcing
import BianchiIX.Dynamics.CoreEntryBounds

noncomputable section

namespace BianchiIX

open Set

theorem coreRegion_strong_forcing {k Q : ℝ} {y : ProjectiveState} {v : CoreAngleState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hQ : ‖v‖ ≤ Q) :
    let B := coreWeightedJacobian k (projectiveCoreAngle y) (toCoreAngleState y)
    B 1 1 ≤ -k / 4 ∧ |B 1 0 * v 0 + B 1 2 * v 2| ≤ 3 * k * y 1 * Q := by
  intro B
  have hv : 0 < y 2 := lt_of_lt_of_le zero_lt_one hy.2.1
  have hcoord := (coreAngle_coordinates (m := y 0) hv).1
  have hV : 1 ≤ toCoreAngleState y 0 / Real.cosh (projectiveCoreAngle y) := by
    change 1 ≤ coreRadius (y 0) (y 2) / Real.cosh (coreAngle (y 0) (y 2))
    rw [hcoord]
    exact hy.2.1
  have hW : 0 ≤ toCoreAngleState y 2 / (toCoreAngleState y 0 / Real.cosh (projectiveCoreAngle y)) ∧
      toCoreAngleState y 2 / (toCoreAngleState y 0 / Real.cosh (projectiveCoreAngle y)) ≤ (1 / 10000) / k := by
    change 0 ≤ y 2 * y 3 / (coreRadius (y 0) (y 2) / Real.cosh (coreAngle (y 0) (y 2))) ∧
      y 2 * y 3 / (coreRadius (y 0) (y 2) / Real.cosh (coreAngle (y 0) (y 2))) ≤ _
    rw [hcoord, mul_div_cancel_left₀ _ (ne_of_gt hv)]
    exact (coreRegion_wall_bounds hy).2
  have hr := coreRegion_radius_bounds hk hy
  obtain ⟨h10, h12⟩ := coreWeightedJacobian_strong_off_diagonal hk hr hV hy.2.2.1 hW
  refine ⟨coreWeightedJacobian_strong_bound hk hr.1 hy.2.2.1 hW, ?_⟩
  have hQ0 : 0 ≤ Q := (norm_nonneg v).trans hQ
  have hc (i : Fin 3) : |v i| ≤ Q := (show |v i| ≤ ‖v‖ by exact norm_le_pi_norm v i).trans hQ
  calc
    _ ≤ |B 1 0| * |v 0| + |B 1 2| * |v 2| := by simpa only [abs_mul] using abs_add_le (B 1 0 * v 0) (B 1 2 * v 2)
    _ ≤ (2 * k * y 1) * Q + (4 * y 1) * Q := add_le_add
      (mul_le_mul h10 (hc 0) (abs_nonneg _) (by have := hy.2.2.1.1; positivity))
      (mul_le_mul h12 (hc 2) (abs_nonneg _) (by have := hy.2.2.1.1; positivity))
    _ ≤ _ := by nlinarith only [mul_nonneg (show 0 ≤ k - 4 by linarith only [hk]) (mul_nonneg hy.2.2.1.1 hQ0)]

/-- The strong component of the genuine flow derivative, estimated without inverting the angular clock. -/
theorem coreProjectedFlowVariation_strong_bound {y : ProjectiveState} {t₀ k a b Q : ℝ}
    (hk : 6 ≤ k) (hab : a ≤ b) (hD : 0 < projectiveStateDenom y)
    (hdom : Icc a b ⊆ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : ∀ t ∈ Icc a b, 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hcore : ∀ t ∈ Icc a b, coreRegion k (projectiveOriginalFlow y t₀ t))
    (w : ProjectiveState)
    (hQ : ∀ t ∈ Icc a b, ‖scaleCoreVariation k (coreProjectedFlowVariation y t₀ t w)‖ ≤ Q) :
    ∀ t ∈ Icc a b,
      let θ := fun s => projectiveCoreAngle (projectiveOriginalFlow y t₀ s)
      let x := fun s => k * coreProjectedFlowVariation y t₀ s w 1
      |x t| ≤ Real.exp (-k * (θ t - θ a) / 4) *
        (|x a| + 3 * k * projectiveOriginalFlow y t₀ a 1 * Q * (θ t - θ a)) := by
  let beta := projectiveOriginalFlow y t₀
  let θ := fun s => projectiveCoreAngle (beta s)
  let rate := fun s => coreOriginalClockRate (beta s)
  let xi := fun s => coreProjectedFlowVariation y t₀ s w
  let v := fun s => scaleCoreVariation k (xi s)
  let B := fun s => coreWeightedJacobian k (θ s) (toCoreAngleState (beta s))
  let d := fun s => B s 1 1
  let g := fun s => B s 1 0 * v s 0 + B s 1 2 * v s 2
  let x := fun s => k * xi s 1
  have hk0 : 0 < k := by linarith only [hk]
  have hQ0 : 0 ≤ Q := (norm_nonneg _).trans (hQ a ⟨le_rfl, hab⟩)
  have hrate (s : ℝ) (hs : s ∈ Icc a b) : 0 < rate s := (coreRegion_clock_regular hk (hcore s hs)).2.2
  have hV (s : ℝ) (hs : s ∈ Icc a b) : 0 < beta s 2 := lt_of_lt_of_le zero_lt_one (hcore s hs).2.1
  have hθ (s : ℝ) (hs : s ∈ Icc a b) : HasDerivAt θ (rate s) s :=
    hasDerivAt_coreAngle_scaled (hasDerivAt_projectiveOriginalFlow_time hD (hdom hs) (hA s hs)) (hV s hs)
  have hcoef (s : ℝ) (hs : s ∈ Icc a b) : d s ≤ -k / 4 ∧ |g s| ≤ 3 * k * beta s 1 * Q :=
    coreRegion_strong_forcing hk (hcore s hs) (hQ s hs)
  have hx (s : ℝ) (hs : s ∈ Icc a b) : HasDerivAt x (rate s * (d s * x s + g s)) s := by
    have hxi := hasDerivAt_coreProjectedFlowVariation hD (hdom hs) (hA s hs) (hV s hs)
      (ne_of_gt (coreRegion_clock_regular hk (hcore s hs)).2.1) w
    have H := (hasDerivAt_pi.mp hxi 1).const_mul k
    have he := congrArg (fun V : CoreAngleState => V 1)
      (coreWeightedJacobian_mulVec (ne_of_gt hk0) (θ s) (toCoreAngleState (beta s)) (xi s))
    change (B s).mulVec (v s) 1 = k * (coreAngleJacobian (θ s) (toCoreAngleState (beta s))).mulVec (xi s) 1 at he
    have hrow : (B s).mulVec (v s) 1 = d s * x s + g s := by
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
      dsimp [d, g, v, x, scaleCoreVariation]
      ring
    convert! H using 1
    rw [← hrow, he]
    change rate s * (k * _) = k * (rate s * _)
    ring
  have hc : stateConstraint (fromProjectiveState y) = 1 := fromProjectiveState_constraint (ne_of_gt hD)
  have hu (s : ℝ) (hs : s ∈ Icc a b) :
      beta s 1 ≤ beta a 1 * Real.exp (-k * (θ s - θ a) / 4) := by
    exact (normalized_core_prefix_contraction hk (convex_Icc a b) hdom hc hA
      (show a ∈ Icc a b from ⟨le_rfl, hab⟩) hs hs.1
      (fun t ht => (coreRegion_radius_bounds hk (hcore t ht)).1)
      (fun t ht => (hcore t ht).2.1) (fun t ht => (coreRegion_wall_bounds (hcore t ht)).1)
      (fun t ht => (coreRegion_wall_bounds (hcore t ht)).2)).1
  have hg (s : ℝ) (hs : s ∈ Icc a b) :
      |g s| ≤ (3 * k * beta a 1 * Q) * Real.exp (-(k / 4) * (θ s - θ a)) := by
    calc
      _ ≤ 3 * k * beta s 1 * Q := (hcoef s hs).2
      _ ≤ 3 * k * (beta a 1 * Real.exp (-k * (θ s - θ a) / 4)) * Q := by gcongr; exact hu s hs
      _ = _ := by
        rw [show -k * (θ s - θ a) / 4 = -(k / 4) * (θ s - θ a) by ring]
        ring
  have H := abs_le_affine_exp_of_clock_damping hx hθ (fun s hs => (hrate s hs).le)
    (fun s hs => by convert! (hcoef s hs).1 using 1; ring) hg
  intro t ht
  convert! H t ht using 1
  congr 2
  ring

theorem exists_large_core_strong_variation {Y : CoreAngleState} (hk : 6 ≤ Y 0)
    (hu : 0 ≤ Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0)
    (hw : 0 ≤ Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0) :
    ∃ T > 0, IsLeast {t | 0 < t ∧ projectiveOriginalFlow (coreRadiusEntry Y) 0 t 2 = 1} T ∧
      ∀ v : CoreAngleState, ∀ t ∈ Icc 0 T,
        let y := coreRadiusEntry Y
        let w := fderiv ℝ coreRadiusEntry Y v
        let θ := fun s => projectiveCoreAngle (projectiveOriginalFlow y 0 s)
        let x := fun s => Y 0 * coreProjectedFlowVariation y 0 s w 1
        let Q := (2 * coreVariationBound) * (|v 0| + Y 0 * |v 1| + |v 2|)
        |x t| ≤ Real.exp (-Y 0 * (θ t - θ 0) / 4) * (|x 0| + 3 * Y 0 * Y 1 * Q * (θ t - θ 0)) := by
  have hD : 0 < projectiveStateDenom (coreRadiusEntry Y) :=
    (coreRegion_clock_regular hk (coreRadiusEntry_region hk hu hw)).1
  have hc : stateConstraint (fromProjectiveState (coreRadiusEntry Y)) = 1 := fromProjectiveState_constraint (ne_of_gt hD)
  obtain ⟨T, hT, hfirst, hcore, _⟩ := exists_large_core_traversal hk hu hw
  obtain ⟨S, _, hfirstS, _, hnorm⟩ := exists_large_core_entry_variation hk hu hw
  have hST : S = T := hfirstS.unique hfirst
  subst S
  refine ⟨T, hT, hfirst, ?_⟩
  intro v t ht y w θ x Q
  have H := coreProjectedFlowVariation_strong_bound hk hT.le hD
    (fun s hs => normalizedMaxDomain_contains_Ici_of_constraint hc 0 hs.1)
    (fun s hs => (hcore s hs).1) (fun s hs => (hcore s hs).2) w
    (fun s hs => hnorm s hs v) t ht
  rw [projectiveOriginalFlow_initial hD] at H
  exact H

end BianchiIX
