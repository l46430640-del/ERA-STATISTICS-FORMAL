import BianchiIX.Dynamics.RestartRadialDriftBounds
import BianchiIX.Analysis.StationaryAxis

noncomputable section

namespace BianchiIX

def restartRadialQuadratic (p : RestartRadialState) : ℝ :=
  restartQuadratic p.1 (p.2 0) (p.2 1 - p.2 2)

theorem contDiffAt_restartRadialQuadratic {p : RestartRadialState}
    (hn : p.1 ^ 2 < 1) (k : WithTop ℕ∞) : ContDiffAt ℝ k restartRadialQuadratic p := by
  obtain ⟨ha, hc, hk⟩ := contDiffAt_restart_coefficients hn k
  have hA := ha.comp p contDiffAt_fst
  have hC := hc.comp p contDiffAt_fst
  have hK := hk.comp p contDiffAt_fst
  unfold restartRadialQuadratic restartQuadratic
  fun_prop

theorem fderiv_restartRadialQuadratic_axis {n : ℝ} (hn : n ^ 2 < 1) :
    fderiv ℝ restartRadialQuadratic (n, 0) = 0 := by
  obtain ⟨ha, hc, hk⟩ := contDiffAt_restart_coefficients hn 1
  have hA := (ha.comp (n, (0 : RestartCenterState)) contDiffAt_fst).differentiableAt (by norm_num)
  have hC := (hc.comp (n, (0 : RestartCenterState)) contDiffAt_fst).differentiableAt (by norm_num)
  have hK := (hk.comp (n, (0 : RestartCenterState)) contDiffAt_fst).differentiableAt (by norm_num)
  have hs : DifferentiableAt ℝ (fun p : RestartRadialState => p.2 0) (n, 0) := by fun_prop
  have hv : DifferentiableAt ℝ (fun p : RestartRadialState => p.2 1 - p.2 2) (n, 0) := by fun_prop
  have H := (((hA.hasFDerivAt.mul hs.hasFDerivAt).add (hK.hasFDerivAt.mul hv.hasFDerivAt)).pow 2).add
    ((hC.hasFDerivAt.mul hv.hasFDerivAt).pow 2)
  change HasFDerivAt restartRadialQuadratic _ (n, 0) at H
  rw [H.fderiv]
  simp

theorem exists_restartRadialQuadratic_fderiv_bound :
    ∃ A ≥ (1 : ℝ), ∀ (n : ℝ) (Z : RestartCenterState), |n| ≤ 1 / 16 → ‖Z‖ ≤ 1 / 16 →
      ‖fderiv ℝ restartRadialQuadratic (n, Z)‖ ≤ A * ‖Z‖ := by
  have hreg (p : RestartRadialState) (hp : ‖p‖ ≤ 1 / 16) :
      ContDiffAt ℝ 3 restartRadialQuadratic p := by
    have hn : |p.1| ≤ 1 / 16 := (norm_fst_le p).trans hp
    obtain ⟨hl, hu⟩ := abs_le.mp hn
    exact contDiffAt_restartRadialQuadratic (by nlinarith only [hl, hu]) 3
  obtain ⟨A, hA, HA⟩ := exists_fderiv_bound_of_stationary_axis hreg
    (fun n hn => fderiv_restartRadialQuadratic_axis (by
      obtain ⟨hl, hu⟩ := abs_le.mp hn
      nlinarith only [hl, hu]))
  refine ⟨A, hA, ?_⟩
  intro n Z hn hZ
  exact HA (n, Z) (by simpa only [Prod.norm_def, Real.norm_eq_abs, max_le_iff] using And.intro hn hZ)

/-- Keep the ordinary strong-wall direction separate before applying the actual flow derivative. -/
theorem fderiv_restartRadialDrift_split {p : RestartRadialState}
    (hn : p.1 ^ 2 < 1) (hr : 0 < restartSectionRadicand p.1 p.2) (w : RestartRadialState) :
    fderiv ℝ restartRadialDrift p w =
      w.1 * deriv (fun m => restartRadialDrift (m, p.2)) p.1 +
        fderiv ℝ (fun W => restartRadialDrift (p.1, W)) p.2 w.2 := by
  have HD := (contDiffAt_restartRadialDrift hn hr).differentiableAt (by norm_num)
  have Hn := HD.hasFDerivAt.comp_hasDerivAt p.1
    ((hasDerivAt_id' p.1).prodMk (hasDerivAt_const p.1 p.2))
  have HZ := HD.hasFDerivAt.comp p.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) p.1 p.2)
  change HasDerivAt (fun m => restartRadialDrift (m, p.2)) _ p.1 at Hn
  change HasFDerivAt (fun W => restartRadialDrift (p.1, W)) _ p.2 at HZ
  rw [Hn.deriv, HZ.fderiv]
  have heq : w = w.1 • (1, (0 : RestartCenterState)) + (0, w.2) := by ext <;> simp
  conv_lhs => rw [heq, map_add, map_smul]
  rfl

theorem exists_restartRadialDrift_tangent_bound :
    ∃ A ≥ (1 : ℝ), ∀ (n : ℝ) (Z : RestartCenterState),
      (0 ≤ n ∧ n ≤ 1 / 16) → ‖Z‖ ≤ 1 / 16 → ∀ w : RestartRadialState,
        |fderiv ℝ restartRadialDrift (n, Z) w| ≤
          A * ‖Z‖ ^ 3 * |w.1| + A * (n * ‖Z‖ ^ 2 + ‖Z‖ ^ 3) * ‖w.2‖ := by
  obtain ⟨A, hA, HA⟩ := exists_restartRadialDrift_bounds
  refine ⟨A, hA, ?_⟩
  intro n Z hn hZ w
  have hn2 : n ^ 2 < 1 := by nlinarith only [hn.1, hn.2]
  have hrad := restartSectionRadicand_pos_of_small
    (by rw [abs_of_nonneg hn.1]; exact hn.2) hZ
  have H := HA n Z hn hZ
  rw [fderiv_restartRadialDrift_split (p := (n, Z)) hn2 hrad]
  apply (abs_add_le _ _).trans
  apply add_le_add
  · rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right H.2.2.2 (abs_nonneg _)
  · exact ((fderiv ℝ (fun W => restartRadialDrift (n, W)) Z).le_opNorm w.2).trans
      (mul_le_mul_of_nonneg_right H.2.2.1 (norm_nonneg _))

end BianchiIX
