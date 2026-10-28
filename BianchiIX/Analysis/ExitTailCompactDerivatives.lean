import BianchiIX.Analysis.ExitTailDifferential
import Mathlib.Topology.Order.Compact

noncomputable section

namespace BianchiIX

open Set

theorem contDiffAt_exitTail_stateDerivative (n : WithTop ℕ∞) {v : ℝ} {Y : ExitTailState}
    (hv : v ^ 2 < (Y 0) ^ 2) (hR : Y 0 ≠ 0)
    (hd : exitTailSpeed (Y 0) (Y 1) v (Y 2) ≠ 0) :
    ContDiffAt ℝ n (fun q : ℝ × ExitTailState => fderiv ℝ (exitTailField q.1) q.2) (v, Y) := by
  have hmap : ContDiffAt ℝ (n + 1)
      (fun q : (ℝ × ExitTailState) × ExitTailState => (q.1.1, q.2)) ((v, Y), Y) := by fun_prop
  have H := contDiffAt_exitTailField (n + 1) hv hR hd
  have HF := H.comp ((v, Y), Y) hmap
  exact HF.fderiv (f := fun q : ℝ × ExitTailState => exitTailField q.1) contDiffAt_snd le_rfl

theorem contDiffAt_exitTail_stateHessian (n : WithTop ℕ∞) {v : ℝ} {Y : ExitTailState}
    (hv : v ^ 2 < (Y 0) ^ 2) (hR : Y 0 ≠ 0)
    (hd : exitTailSpeed (Y 0) (Y 1) v (Y 2) ≠ 0) :
    ContDiffAt ℝ n (fun q : ℝ × ExitTailState => fderiv ℝ (fderiv ℝ (exitTailField q.1)) q.2) (v, Y) := by
  have hmap : ContDiffAt ℝ (n + 1)
      (fun q : (ℝ × ExitTailState) × ExitTailState => (q.1.1, q.2)) ((v, Y), Y) := by fun_prop
  have H := contDiffAt_exitTail_stateDerivative (n + 1) hv hR hd
  have HF := H.comp ((v, Y), Y) hmap
  exact HF.fderiv (f := fun q : ℝ × ExitTailState => fderiv ℝ (exitTailField q.1)) contDiffAt_snd le_rfl

/-- The full state Hessian is uniformly bounded on the signed tail box, including V = 0. -/
theorem exists_exitTail_field_two_bounds :
    ∃ C ≥ (1 : ℝ), ∀ (v : ℝ) (Y : ExitTailState),
      (7 / 4 ≤ Y 0 ∧ Y 0 ≤ 17 / 4) → |Y 1| ≤ 1 / 100 →
      (0 ≤ v ∧ v ≤ 1) → |Y 2| ≤ 1 / 100 →
      ‖exitTailField v Y‖ ≤ C ∧ ‖fderiv ℝ (exitTailField v) Y‖ ≤ C ∧
        ‖fderiv ℝ (fderiv ℝ (exitTailField v)) Y‖ ≤ C := by
  let S : Set (ℝ × ExitTailState) := Icc (0, ![7 / 4, -(1 / 100), -(1 / 100)])
    (1, ![17 / 4, 1 / 100, 1 / 100])
  have hcompact : IsCompact S := isCompact_Icc
  let q := fun p : ℝ × ExitTailState => ‖exitTailField p.1 p.2‖ +
    ‖fderiv ℝ (exitTailField p.1) p.2‖ + ‖fderiv ℝ (fderiv ℝ (exitTailField p.1)) p.2‖
  have hq : ContinuousOn q S := by
    intro p hp
    have hR : 7 / 4 ≤ p.2 0 ∧ p.2 0 ≤ 17 / 4 := ⟨hp.1.2 0, hp.2.2 0⟩
    have hu : |p.2 1| ≤ 1 / 100 := abs_le.mpr ⟨hp.1.2 1, hp.2.2 1⟩
    have hv : 0 ≤ p.1 ∧ p.1 ≤ 1 := ⟨hp.1.1, hp.2.1⟩
    have hw : |p.2 2| ≤ 1 / 100 := abs_le.mpr ⟨hp.1.2 2, hp.2.2 2⟩
    have hvR : p.1 ^ 2 < (p.2 0) ^ 2 := by nlinarith only [hR.1, hv.1, hv.2]
    have hR0 : p.2 0 ≠ 0 := by linarith only [hR.1]
    have hd : exitTailSpeed (p.2 0) (p.2 1) p.1 (p.2 2) ≠ 0 := by
      have H := exitTailSpeed_compact hR.1 hu hv hw
      linarith only [H]
    have h0 : ContinuousAt (fun q : ℝ × ExitTailState => ‖exitTailField q.1 q.2‖) p :=
      (contDiffAt_exitTailField 0 hvR hR0 hd).continuousAt.norm
    have h1 : ContinuousAt (fun q : ℝ × ExitTailState => ‖fderiv ℝ (exitTailField q.1) q.2‖) p :=
      (contDiffAt_exitTail_stateDerivative 0 hvR hR0 hd).continuousAt.norm
    have HH := (contDiffAt_exitTail_stateHessian 0 hvR hR0 hd).continuousAt
    have h2 := ContinuousAt.norm (E := ExitTailState →L[ℝ] ExitTailState →L[ℝ] ExitTailState) HH
    exact ((h0.add h1).add h2).continuousWithinAt
  obtain ⟨B, hB⟩ := hcompact.exists_bound_of_continuousOn hq
  refine ⟨max B 1, le_max_right _ _, ?_⟩
  intro v Y hR hu hv hw
  have hYS : (v, Y) ∈ S := by
    constructor
    · refine ⟨hv.1, ?_⟩
      intro i
      fin_cases i
      · exact hR.1
      · exact (abs_le.mp hu).1
      · exact (abs_le.mp hw).1
    · refine ⟨hv.2, ?_⟩
      intro i
      fin_cases i
      · exact hR.2
      · exact (abs_le.mp hu).2
      · exact (abs_le.mp hw).2
  have H : q (v, Y) ≤ max B 1 := (le_abs_self _).trans ((hB (v, Y) hYS).trans (le_max_left _ _))
  dsimp only [q] at H
  exact ⟨by linarith [norm_nonneg (fderiv ℝ (exitTailField v) Y),
      norm_nonneg (fderiv ℝ (fderiv ℝ (exitTailField v)) Y)],
    by linarith [norm_nonneg (exitTailField v Y), norm_nonneg (fderiv ℝ (fderiv ℝ (exitTailField v)) Y)],
    by linarith [norm_nonneg (exitTailField v Y), norm_nonneg (fderiv ℝ (exitTailField v) Y)]⟩

theorem exists_exitTail_hessian_forcing_bound :
    ∃ C ≥ (1 : ℝ), ∀ (v : ℝ) (Y ξ ζ : ExitTailState),
      (7 / 4 ≤ Y 0 ∧ Y 0 ≤ 17 / 4) → |Y 1| ≤ 1 / 100 →
      (0 ≤ v ∧ v ≤ 1) → |Y 2| ≤ 1 / 100 →
      ‖fderiv ℝ (fderiv ℝ (exitTailField v)) Y ξ ζ‖ ≤ C * ‖ξ‖ * ‖ζ‖ := by
  obtain ⟨C, hC, H⟩ := exists_exitTail_field_two_bounds
  refine ⟨C, hC, ?_⟩
  intro v Y ξ ζ hR hu hv hw
  have HB := (H v Y hR hu hv hw).2.2
  exact ((fderiv ℝ (fderiv ℝ (exitTailField v)) Y ξ).le_opNorm ζ).trans
    (mul_le_mul_of_nonneg_right
      (((fderiv ℝ (fderiv ℝ (exitTailField v)) Y).le_opNorm ξ).trans
        (mul_le_mul_of_nonneg_right HB (norm_nonneg ξ))) (norm_nonneg ζ))

end BianchiIX
