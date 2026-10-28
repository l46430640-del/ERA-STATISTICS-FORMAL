import BianchiIX.Algebra.MatchingPhaseBounds
import Mathlib.Analysis.Calculus.ImplicitContDiff

noncomputable section

namespace BianchiIX

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contDiffAt_matchingPhase_comp {m v w : E → ℝ} {p : E} (n : WithTop ℕ∞)
    (hm : ContDiffAt ℝ n m p) (hv : ContDiffAt ℝ n v p) (hw : ContDiffAt ℝ n w p)
    (hmt : 1 < m p) : ContDiffAt ℝ n (fun q => matchingPhase (m q) (v q) (w q)) p := by
  have hp : (m p + 1) ^ 2 + v p ^ 2 ≠ 0 := by
    have H : 0 < m p + 1 := by linarith only [hmt]
    positivity
  have hn : (m p - 1) ^ 2 + w p ^ 2 ≠ 0 := by
    have H : 0 < m p - 1 := by linarith only [hmt]
    positivity
  exact (((((hm.add contDiffAt_const).pow 2).add (hv.pow 2)).sqrt hp).add
    ((((hm.sub contDiffAt_const).pow 2).add (hw.pow 2)).sqrt hn)).sub hm

theorem hasFDerivAt_matchingPhase_comp {m v w : E → ℝ} {m' v' w' : E →L[ℝ] ℝ} {p : E}
    (hm : HasFDerivAt m m' p) (hv : HasFDerivAt v v' p) (hw : HasFDerivAt w w' p)
    (hmt : 1 < m p) :
    HasFDerivAt (fun q => matchingPhase (m q) (v q) (w q))
      (matchingPhaseSlope (m p) (v p) (w p) • m' +
        (v p / phaseNorm (m p + 1) (v p)) • v' + (w p / phaseNorm (m p - 1) (w p)) • w') p := by
  have hp : (m p + 1) ^ 2 + v p ^ 2 ≠ 0 := by
    have H : 0 < m p + 1 := by linarith only [hmt]
    positivity
  have hn : (m p - 1) ^ 2 + w p ^ 2 ≠ 0 := by
    have H : 0 < m p - 1 := by linarith only [hmt]
    positivity
  have H := (((((hm.add_const 1).pow 2).add (hv.pow 2)).sqrt hp).add
    ((((hm.sub_const 1).pow 2).add (hw.pow 2)).sqrt hn)).sub hm
  convert! H using 1
  ext z
  simp only [add_apply, sub_apply, smul_apply, smul_eq_mul]
  dsimp [matchingPhaseSlope, phaseNorm]
  ring

end BianchiIX
