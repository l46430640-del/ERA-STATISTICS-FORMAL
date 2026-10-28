import BianchiIX.Analysis.PositiveConeTransport
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.ContDiff.Comp

noncomputable section

namespace BianchiIX

/-- Ambient differentiability along a finite orbit gives ambient regularity of its iterate. -/
theorem contDiffAt_iterate_along_orbit (f : (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (Y : ℕ → Fin 3 → ℝ) (n : ℕ)
    (horbit : ∀ j < n, Y (j + 1) = f (Y j))
    (hreg : ∀ j < n, ContDiffAt ℝ 1 f (Y j)) :
    f^[n] (Y 0) = Y n ∧ ContDiffAt ℝ 1 (f^[n]) (Y 0) := by
  revert horbit hreg
  induction n with
  | zero => intro _ _; exact ⟨rfl, contDiffAt_id⟩
  | succ n ih =>
    intro horbit hreg
    obtain ⟨hy, hd⟩ := ih (fun j hj => horbit j (by omega)) (fun j hj => hreg j (by omega))
    have hfn : ContDiffAt ℝ 1 f (f^[n] (Y 0)) := by rw [hy]; exact hreg n (by omega)
    have hn : f^[n + 1] = f ∘ f^[n] := funext (Function.iterate_succ_apply' f n)
    rw [hn, Function.comp_apply, hy, ← horbit n (by omega)]
    exact ⟨rfl, hfn.comp _ hd⟩

/-- Unit-radial estimates control the derivative of a genuine finite iterate along its orbit. -/
theorem positive_cone_iterate (f : (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (Y : ℕ → Fin 3 → ℝ) (a : ℕ → Fin 2 → ℝ) (L : ℕ → ℝ) (n : ℕ)
    (horbit : ∀ j < n, Y (j + 1) = f (Y j))
    (hreg : ∀ j < n, DifferentiableAt ℝ f (Y j))
    (H : ∀ j < n, ∀ z : Fin 3 → ℝ, z 0 = 1 → (∀ i : Fin 2, |z i.succ| ≤ a j i) →
      0 < fderiv ℝ f (Y j) z 0 ∧ |Real.log (fderiv ℝ f (Y j) z 0)| ≤ L j ∧
        ∀ i : Fin 2, |fderiv ℝ f (Y j) z i.succ| ≤ a (j + 1) i * fderiv ℝ f (Y j) z 0)
    {v : Fin 3 → ℝ} (hv0 : v 0 = 1) (hv : ∀ i : Fin 2, |v i.succ| ≤ a 0 i) :
    f^[n] (Y 0) = Y n ∧ DifferentiableAt ℝ (f^[n]) (Y 0) ∧
      let w := fderiv ℝ (f^[n]) (Y 0) v
      0 < w 0 ∧ |Real.log (w 0)| ≤ ∑ j ∈ Finset.range n, L j ∧
        ∀ i : Fin 2, |w i.succ| ≤ a n i * w 0 := by
  revert horbit hreg H
  induction n with
  | zero =>
    intro _ _ _
    simp only [Function.iterate_zero, fderiv_id, ContinuousLinearMap.id_apply,
      hv0, Real.log_one, abs_zero, Finset.range_zero, Finset.sum_empty, mul_one]
    exact ⟨rfl, differentiableAt_id, zero_lt_one, le_rfl, hv⟩
  | succ n ih =>
    intro horbit hreg H
    obtain ⟨hy, hd, hp, hl, hcone⟩ := ih
      (fun j hj => horbit j (by omega)) (fun j hj => hreg j (by omega))
      (fun j hj => H j (by omega))
    have hfn : DifferentiableAt ℝ f (f^[n] (Y 0)) := by rw [hy]; exact hreg n (by omega)
    have hn : f^[n + 1] = f ∘ f^[n] := funext (Function.iterate_succ_apply' f n)
    have hder : fderiv ℝ (f^[n + 1]) (Y 0) v =
        fderiv ℝ f (Y n) (fderiv ℝ (f^[n]) (Y 0) v) := by
      rw [hn, fderiv_comp _ hfn hd, ContinuousLinearMap.comp_apply, hy]
    have HT := positive_cone_transport (fderiv ℝ f (Y n)) hp hcone (H n (by omega))
    refine ⟨?_, ?_, ?_⟩
    · rw [hn, Function.comp_apply, hy, ← horbit n (by omega)]
    · rw [hn]
      exact hfn.comp _ hd
    · dsimp only
      rw [hder]
      refine ⟨HT.1, ?_, HT.2.2⟩
      rw [Finset.sum_range_succ]
      exact HT.2.1.trans (add_le_add hl le_rfl)

end BianchiIX
