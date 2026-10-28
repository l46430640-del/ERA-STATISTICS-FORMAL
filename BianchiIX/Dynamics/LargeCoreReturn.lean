import BianchiIX.Dynamics.CoreExistence
import BianchiIX.Dynamics.CoreDuration

noncomputable section

namespace BianchiIX

open Set

/-- The large-parameter nonlinear core crossing for every entrance in (A.6), including its boundary. -/
theorem exists_large_core_traversal {k u w : ℝ} (hk : 6 ≤ k)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k) (hw : 0 ≤ w ∧ w ≤ (1 / 10000) / k) :
    let y : ProjectiveState := ![1 + Real.sqrt (k ^ 2 - 1), u, 1, w]
    let x := fromProjectiveState y
    let β := fun t => toProjectiveState (normalizedMaxCurve x 0 t)
    ∃ T > 0,
      IsLeast {t | 0 < t ∧ β t 2 = 1} T ∧
      (∀ t ∈ Icc 0 T, 0 < 1 + normalizedMaxCurve x 0 t 0 ∧ coreRegion k (β t)) ∧
      β T 0 < 1 ∧ 0 < coreAngle (β T 0) (β T 2) ∧ deriv (fun t => β t 2) T < 0 ∧
      |coreRadius (β T 0) (β T 2) - k| ≤ 16 / k * (u + w ^ 2) ∧
      β T 1 ≤ Real.exp (-k / 40) * u ∧ β T 3 ≤ Real.exp (-1 / (2 * k)) * w ∧
      1 / (4 * k) ≤ integralClock (normalizedProjectiveRate x 0) 0 T ∧
      integralClock (normalizedProjectiveRate x 0) 0 T ≤ 4 * Real.log (4 * k) / k ∧
      T ≤ 2 * k * Real.log (4 * k) := by
  intro y x β
  have hk0 : 0 < k := by linarith
  have hD : 0 < projectiveStateDenom y :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (coreBootstrap_denom_lower hk hu hw)
  have hc : stateConstraint x = 1 := fromProjectiveState_constraint (ne_of_gt hD)
  have hβ0 : β 0 = y := by
    dsimp [β]
    rw [normalizedMaxCurve_initial]
    exact toProjectiveState_fromProjectiveState (ne_of_gt hD)
  have hA : 0 < 1 + normalizedMaxCurve x 0 0 0 := by
    rw [normalizedMaxCurve_initial]
    exact fromProjectiveState_clock_pos hD
  have henergy : coreEnergy (1 + Real.sqrt (k ^ 2 - 1)) 1 = k ^ 2 := by
    have H := Real.sq_sqrt (by nlinarith [sq_nonneg (k - 6)] : 0 ≤ k ^ 2 - 1)
    unfold coreEnergy
    nlinarith
  have hR : coreRadius (β 0 0) (β 0 2) = k := by
    rw [hβ0]
    change Real.sqrt (coreEnergy (1 + Real.sqrt (k ^ 2 - 1)) 1) = k
    rw [henergy, Real.sqrt_sq hk0.le]
  have hV : β 0 2 = 1 := by rw [hβ0]; rfl
  have hM : 1 ≤ β 0 0 := by
    rw [hβ0]
    change 1 ≤ 1 + Real.sqrt (k ^ 2 - 1)
    linarith [Real.sqrt_nonneg (k ^ 2 - 1)]
  have hU : 0 ≤ β 0 1 ∧ β 0 1 ≤ (1 / 10000) / k := by rw [hβ0]; exact hu
  have hW : 0 ≤ β 0 3 ∧ β 0 3 ≤ (1 / 10000) / k := by rw [hβ0]; exact hw
  obtain ⟨T, hT, hVT, hcore⟩ := exists_normalized_core_return hc hk le_rfl hA hR hV hM hU hW
  have hTmem : T ∈ Icc 0 T := ⟨hT.le, le_rfl⟩
  have hAall (t : ℝ) (ht : t ∈ Icc 0 T) : 0 < 1 + normalizedMaxCurve x 0 t 0 :=
    lt_of_lt_of_le (by positivity : 0 < 3 / (2 * k ^ 2)) (hcore t ht).1
  have hr (t : ℝ) (ht : t ∈ Icc 0 T) := coreRegion_radius_bounds hk (hcore t ht).2
  have hv (t : ℝ) (ht : t ∈ Icc 0 T) : 1 ≤ β t 2 := (hcore t ht).2.2.1
  have hu' (t : ℝ) (ht : t ∈ Icc 0 T) := (coreRegion_wall_bounds (hcore t ht).2).1
  have hw' (t : ℝ) (ht : t ∈ Icc 0 T) := (coreRegion_wall_bounds (hcore t ht).2).2
  have hfirst := normalized_core_return_isLeast hc hk le_rfl hT hAall
    (fun t ht => (hr t ht).1) hv hu' hw' hVT
  have hdown := normalized_core_return_downward hc hk le_rfl hT (hAall T hTmem) hVT
    (fun t ht => hv t ⟨ht.1.le, ht.2.le⟩) (hr T hTmem).1 (hu' T hTmem) (hw' T hTmem)
  have hneg : deriv (fun t => β t 2) T < 0 := by
    have H : 0 < (1 + normalizedMaxCurve x 0 T 0) * k / 2 := by
      have HA := hAall T hTmem
      positivity
    linarith [hdown.2.2.1]
  have hdrift := (normalized_core_energy_band_improves hc hk le_rfl hT.le hAall hR hV
    (fun t ht => by rw [coreRadius_sq]; exact (hcore t ht).2.1)
    hv hu' (fun t ht => (hcore t ht).2.2.2.2)).1
  change |coreRadius (β T 0) (β T 2) - k| ≤ 16 / k * (β 0 1 + (β 0 3) ^ 2) at hdrift
  rw [hβ0] at hdrift
  obtain ⟨htime, hUout, hWout⟩ := normalized_core_exit_contraction hc hk le_rfl hT hAall hr hv hu' hw' hV hVT hM
  change β T 1 ≤ Real.exp (-k / 40) * β 0 1 at hUout
  change β T 3 ≤ Real.exp (-1 / (2 * k)) * β 0 3 at hWout
  rw [hβ0] at hUout hWout
  have htimeup := (normalized_core_residence hc hk le_rfl hT.le hAall hr hv hu' hw').2
  simp only [sub_zero] at htimeup
  have hτup := normalized_core_projective_duration hc hk le_rfl hT.le hAall hr hv hu' hw'
  exact ⟨T, hT, hfirst, fun t ht => ⟨hAall t ht, (hcore t ht).2⟩,
    hdown.1, hdown.2.1, hneg, hdrift, hUout, hWout, htime, hτup, htimeup⟩

end BianchiIX
