import BianchiIX.Dynamics.ExitTailCoordinates
import BianchiIX.Analysis.ScalarMultiplier

noncomputable section

namespace BianchiIX

open Set MeasureTheory

def exitTailWallRate (v : ℝ) (Y : ExitTailState) : Fin 2 → ℝ :=
  ![exitTailStrongRate (Y 0) (Y 1) v (Y 2), exitTailWeakRate (Y 0) (Y 1) v (Y 2)]

def exitTailMultiplier (Y : ℝ → ExitTailState) (i : Fin 2) (T : ℝ) : ℝ :=
  Real.exp (∫ s in (0 : ℝ)..T, exitTailWallRate (Real.exp (-s)) (Y s) i)

theorem exitTailField_wall (v : ℝ) (Y : ExitTailState) (i : Fin 2) :
    exitTailField v Y i.succ = exitTailWallRate v Y i * Y i.succ := by
  fin_cases i <;> rfl

theorem continuousOn_exitTailWallRate {Y : ℝ → ExitTailState} {I : Set ℝ}
    (hY : ContinuousOn Y I)
    (hd : ∀ s ∈ I, exitTailSpeed (Y s 0) (Y s 1) (Real.exp (-s)) (Y s 2) ≠ 0)
    (i : Fin 2) : ContinuousOn (fun s => exitTailWallRate (Real.exp (-s)) (Y s) i) I := by
  have hy (j : Fin 3) : ContinuousOn (fun s => Y s j) I :=
    (continuous_apply j).comp_continuousOn hY
  have hv : ContinuousOn (fun s : ℝ => Real.exp (-s)) I := by fun_prop
  have ht : ContinuousOn (fun s => exitTailGap (Y s 0) (Real.exp (-s))) I :=
    (((hy 0).pow 2).sub (hv.pow 2)).sqrt
  have hc : ContinuousOn (fun s => coupling (Y s 1) (Real.exp (-s)) (Y s 2)) I :=
    (hy 1).mul ((hv.add (hy 2)).sub (hy 1))
  have hs : ContinuousOn (fun s => exitTailSpeed (Y s 0) (Y s 1) (Real.exp (-s)) (Y s 2)) I := ht.add hc
  fin_cases i
  · change ContinuousOn (fun s => exitTailStrongRate (Y s 0) (Y s 1) (Real.exp (-s)) (Y s 2)) I
    have hbase := (ht.const_mul 2).sub ((hy 0).pow 2)
    have hcross := (hv.const_mul 2).mul (hy 2)
    have hn := ((hbase.add hcross).sub ((hy 2).pow 2)).add ((hy 1).pow 2)
    exact hn.div (hs.const_mul 2)
      (fun s hs => mul_ne_zero (by norm_num) (hd s hs))
  · change ContinuousOn (fun s => exitTailWeakRate (Y s 0) (Y s 1) (Real.exp (-s)) (Y s 2)) I
    exact ((ht.sub continuousOn_const).sub hc).div hs hd

/-- Both signed walls keep their initial amplitude as a factor, including zero initial walls. -/
theorem exitTail_wall_multiplier {Y : ℝ → ExitTailState} {T : ℝ} (hT : 0 ≤ T)
    (hY : ∀ s ∈ Icc 0 T, HasDerivAt Y (exitTailField (Real.exp (-s)) (Y s)) s)
    (hd : ∀ s ∈ Icc 0 T, exitTailSpeed (Y s 0) (Y s 1) (Real.exp (-s)) (Y s 2) ≠ 0)
    (i : Fin 2) :
    Y T i.succ = Y 0 i.succ * exitTailMultiplier Y i T ∧ 0 < exitTailMultiplier Y i T := by
  have hy := HasDerivAt.continuousOn hY
  refine ⟨?_, Real.exp_pos _⟩
  apply homogeneous_solution_eq_exp_integral_Icc hT (continuousOn_exitTailWallRate hy hd i)
    ((continuous_apply i.succ).comp_continuousOn hy)
  intro s hs
  have H := hasDerivAt_pi.mp (hY s (Ioo_subset_Icc_self hs)) i.succ
  rw [exitTailField_wall] at H
  exact H

end BianchiIX
