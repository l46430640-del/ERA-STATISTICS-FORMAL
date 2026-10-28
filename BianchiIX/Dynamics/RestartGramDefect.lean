import BianchiIX.Dynamics.RestartRadialDifferential

noncomputable section

namespace BianchiIX

open Set

def restartGramDefect (n : ℝ) : Fin 3 → ℝ := restartGramCoefficients n - ![1, 0, 1]

theorem restartGramDefect_zero : restartGramDefect 0 = 0 := by
  ext i
  fin_cases i <;> simp [restartGramDefect, restartGramCoefficients, restart_coefficients_zero.1,
    restart_coefficients_zero.2.1, restart_coefficients_zero.2.2]

theorem contDiffAt_restartGramDefect {n : ℝ} (hn : n ^ 2 < 1) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k restartGramDefect n := (contDiffAt_restartGramCoefficients hn k).1.sub contDiffAt_const

theorem exists_restartGramDefect_bounds :
    ∃ A ≥ (1 : ℝ), ∀ n : ℝ, |n| ≤ 1 / 16 →
      ‖restartGramDefect n‖ ≤ A * |n| ∧ ‖fderiv ℝ restartGramDefect n‖ ≤ A := by
  let S := Metric.closedBall (0 : ℝ) (1 / 16)
  have Hreg (n : ℝ) (hn : n ∈ S) : ContDiffAt ℝ 2 restartGramDefect n := by
    have H : |n| ≤ 1 / 16 := by simpa [S] using hn
    obtain ⟨hl, hu⟩ := abs_le.mp H
    exact contDiffAt_restartGramDefect (by nlinarith only [hl, hu]) 2
  have HC : ContinuousOn (fun n => ‖fderiv ℝ restartGramDefect n‖) S := by
    intro n hn
    exact ((Hreg n hn).fderiv_right (m := 1) (by norm_num)).continuousAt.norm.continuousWithinAt
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℝ) (1 / 16)).exists_bound_of_continuousOn HC
  let A := max B 1
  have Hbound (n : ℝ) (hn : n ∈ S) : ‖fderiv ℝ restartGramDefect n‖ ≤ A :=
    (le_abs_self _).trans ((hB n hn).trans (le_max_left _ _))
  refine ⟨A, le_max_right _ _, ?_⟩
  intro n hn
  have hnS : n ∈ S := by simpa [S] using hn
  have H := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun x hx => (Hreg x hx).differentiableAt (by norm_num)) Hbound
    (convex_closedBall (0 : ℝ) (1 / 16)) (by simp [S] : (0 : ℝ) ∈ S) hnS
  exact ⟨by simpa [restartGramDefect_zero] using H, Hbound n hnS⟩

def restartRadialQuadraticDefect (p : RestartRadialState) : ℝ :=
  restartRadialQuadratic p - (p.2 0 ^ 2 + (p.2 1 - p.2 2) ^ 2)

theorem restartRadialQuadraticDefect_formula (p : RestartRadialState) :
    restartRadialQuadraticDefect p =
      quadraticFromCoefficients (restartGramDefect p.1) (p.2 0) (p.2 1 - p.2 2) := by
  dsimp [restartRadialQuadraticDefect, restartRadialQuadratic, restartQuadratic,
    quadraticFromCoefficients, restartGramDefect, restartGramCoefficients]
  ring

theorem contDiffAt_restartRadialQuadraticDefect {p : RestartRadialState}
    (hn : p.1 ^ 2 < 1) (k : WithTop ℕ∞) : ContDiffAt ℝ k restartRadialQuadraticDefect p := by
  have HQ := contDiffAt_restartRadialQuadratic hn k
  unfold restartRadialQuadraticDefect
  fun_prop

theorem fderiv_restartRadialQuadraticDefect_apply {p : RestartRadialState}
    (hn : p.1 ^ 2 < 1) (w : RestartRadialState) :
    fderiv ℝ restartRadialQuadraticDefect p w =
      quadraticFromCoefficients (fderiv ℝ restartGramDefect p.1 w.1) (p.2 0) (p.2 1 - p.2 2) +
      (2 * restartGramDefect p.1 0 * p.2 0 + restartGramDefect p.1 1 * (p.2 1 - p.2 2)) * w.2 0 +
      (restartGramDefect p.1 1 * p.2 0 + 2 * restartGramDefect p.1 2 * (p.2 1 - p.2 2)) * (w.2 1 - w.2 2) := by
  have HM := ((contDiffAt_restartGramDefect hn 1).differentiableAt (by norm_num)).hasFDerivAt.comp p hasFDerivAt_fst
  have hm (i : Fin 3) := hasFDerivAt_pi'.mp HM i
  have hs := (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) p.2).comp p (hasFDerivAt_snd (𝕜 := ℝ))
  have hv := ((hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 3) p.2).sub
    (hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 3) p.2)).comp p (hasFDerivAt_snd (𝕜 := ℝ))
  have H := (((hm 0).mul (hs.pow 2)).add (((hm 1).mul hs).mul hv)).add ((hm 2).mul (hv.pow 2))
  change HasFDerivAt (fun q : RestartRadialState =>
    quadraticFromCoefficients (restartGramDefect q.1) (q.2 0) (q.2 1 - q.2 2)) _ p at H
  have heq : restartRadialQuadraticDefect = fun q =>
      quadraticFromCoefficients (restartGramDefect q.1) (q.2 0) (q.2 1 - q.2 2) :=
    funext restartRadialQuadraticDefect_formula
  rw [heq, H.fderiv]
  simp [quadraticFromCoefficients]
  ring

theorem exists_restartRadialQuadraticDefect_tangent_bound :
    ∃ A ≥ (1 : ℝ), ∀ (n : ℝ) (Z : RestartCenterState), |n| ≤ 1 / 16 → ∀ w : RestartRadialState,
      |fderiv ℝ restartRadialQuadraticDefect (n, Z) w| ≤
        12 * A * |w.1| * ‖Z‖ ^ 2 + 24 * A * |n| * ‖Z‖ * ‖w.2‖ := by
  obtain ⟨A, hA, HA⟩ := exists_restartGramDefect_bounds
  refine ⟨A, hA, ?_⟩
  intro n Z hn w
  have hn2 : n ^ 2 < 1 := by obtain ⟨hl, hu⟩ := abs_le.mp hn; nlinarith only [hl, hu]
  have hdiff (V : RestartCenterState) : |V 1 - V 2| ≤ 2 * ‖V‖ := by
    have H1 : |V 1| ≤ ‖V‖ := norm_le_pi_norm V 1
    have H2 : |V 2| ≤ ‖V‖ := norm_le_pi_norm V 2
    linarith only [abs_sub (V 1) (V 2), H1, H2]
  rw [fderiv_restartRadialQuadraticDefect_apply (p := (n, Z)) hn2]
  apply (abs_quadratic_tangent_le _ _ (norm_nonneg Z) (norm_nonneg w.2)
    (norm_le_pi_norm Z 0) (hdiff Z) (norm_le_pi_norm w.2 0) (hdiff w.2)).trans
  have HD : ‖fderiv ℝ restartGramDefect n w.1‖ ≤ A * |w.1| :=
    ((fderiv ℝ restartGramDefect n).le_opNorm w.1).trans
      (mul_le_mul_of_nonneg_right (HA n hn).2 (abs_nonneg _))
  calc
    _ ≤ 12 * (A * |w.1|) * ‖Z‖ ^ 2 + 24 * (A * |n|) * ‖Z‖ * ‖w.2‖ := by
      gcongr
      exact (HA n hn).1
    _ = _ := by ring

end BianchiIX
