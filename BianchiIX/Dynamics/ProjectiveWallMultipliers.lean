import BianchiIX.Analysis.CompactIntegralSecondRegularity
import BianchiIX.Dynamics.FlowSecondRegularity
import BianchiIX.Dynamics.CoreEntry

noncomputable section

namespace BianchiIX

open Set MeasureTheory

/-- The clock ratio converts the exact normalized wall factor to projective amplitudes. -/
def normalizedProjectiveWallMultiplier (x : NormalizedState) (T : ℝ) (i : Fin 3) : ℝ :=
  Real.exp (Real.log (1 + x 0) - Real.log (1 + normalizedMaxCurve x 0 T 0) +
    ∫ t in 0..T, wallRate i (normalizedMaxCurve x 0 t))

theorem normalizedProjectiveWallMultiplier_pos (x : NormalizedState) (T : ℝ) (i : Fin 3) :
    0 < normalizedProjectiveWallMultiplier x T i := Real.exp_pos _

theorem normalizedProjectiveWallMultiplier_formula {x : NormalizedState} {T : ℝ}
    (hT : T ∈ normalizedMaxDomain x 0) (hA0 : 0 < 1 + x 0)
    (hAT : 0 < 1 + normalizedMaxCurve x 0 T 0) (i : Fin 3) :
    toProjectiveState (normalizedMaxCurve x 0 T) i.succ =
      toProjectiveState x i.succ * normalizedProjectiveWallMultiplier x T i := by
  have H := normalized_wall_formula (convex_normalizedMaxDomain x 0) (isOpen_normalizedMaxDomain x 0)
    (fun _ ht => hasDerivAt_normalizedMaxCurve ht) (initial_mem_normalizedMaxDomain x 0) hT i
  rw [normalizedMaxCurve_initial] at H
  have hcoord (z : NormalizedState) : toProjectiveState z i.succ = Real.sqrt 3 * wallValue i z / (1 + z 0) := by
    fin_cases i <;> rfl
  rw [hcoord, hcoord, H, normalizedProjectiveWallMultiplier, Real.exp_add, Real.exp_sub,
    Real.exp_log hA0, Real.exp_log hAT]
  field_simp

theorem contDiff_wallRate (n : WithTop ℕ∞) (i : Fin 3) : ContDiff ℝ n (wallRate i) := by
  change ContDiff ℝ n (fun x => wallRate i x)
  fin_cases i <;> dsimp [wallRate, rateOne, rateTwo, rateThree, shearSq] <;> fun_prop

/-- Parameter-dependent finite flights have positive C2 wall factors, including zero entrance walls. -/
theorem contDiffAt_normalizedProjectiveWallMultiplier_two
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c : E → NormalizedState} {τ : E → ℝ} {Y : E}
    (hc : ContDiffAt ℝ 2 c Y) (hτ : ContDiffAt ℝ 2 τ Y) (hpos : 0 ≤ τ Y)
    (hdom : Icc 0 (τ Y) ⊆ normalizedMaxDomain (c Y) 0)
    (hA0 : 0 < 1 + c Y 0) (hAT : 0 < 1 + normalizedMaxCurve (c Y) 0 (τ Y) 0) (i : Fin 3) :
    ContDiffAt ℝ 2 (fun Z => normalizedProjectiveWallMultiplier (c Z) (τ Z) i) Y ∧
      ContDiffAt ℝ 2 (fun Z => Real.log (normalizedProjectiveWallMultiplier (c Z) (τ Z) i)) Y := by
  have hF (t : ℝ) (ht : t ∈ Icc 0 (τ Y)) :
      ContDiffAt ℝ 2 (fun p : E × ℝ => wallRate i (normalizedMaxCurve (c p.1) 0 p.2)) (Y, t) := by
    have hp : ContDiffAt ℝ 2 (fun p : E × ℝ => (c p.1, p.2)) (Y, t) :=
      (hc.comp (Y, t) contDiffAt_fst).prodMk contDiffAt_snd
    have hflow := (contDiffAt_normalizedMaxCurve_two (hdom ht)).comp (Y, t) hp
    exact (contDiff_wallRate 2 i).contDiffAt.comp (Y, t) hflow
  have hInt := contDiffAt_moving_intervalIntegral_two hτ hpos hF
  have hEnd : ContDiffAt ℝ 2 (fun Z => normalizedMaxCurve (c Z) 0 (τ Z)) Y :=
    (contDiffAt_normalizedMaxCurve_two (hdom ⟨hpos, le_rfl⟩)).comp Y
      (g := fun p : NormalizedState × ℝ => normalizedMaxCurve p.1 0 p.2)
      (f := fun Z => (c Z, τ Z)) (hc.prodMk hτ)
  have hStart : ContDiffAt ℝ 2 (fun Z => 1 + c Z 0) Y :=
    contDiffAt_const.add (contDiffAt_pi.mp hc 0)
  have hFinish : ContDiffAt ℝ 2 (fun Z => 1 + normalizedMaxCurve (c Z) 0 (τ Z) 0) Y :=
    contDiffAt_const.add (contDiffAt_pi.mp hEnd 0)
  have hLog := ((hStart.log hA0.ne').sub (hFinish.log hAT.ne')).add hInt
  refine ⟨hLog.exp, ?_⟩
  simpa only [normalizedProjectiveWallMultiplier, Real.log_exp] using hLog

end BianchiIX
