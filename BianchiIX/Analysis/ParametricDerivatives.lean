import Mathlib.Analysis.Calculus.ContDiff.Operations

noncomputable section

namespace BianchiIX

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem contDiffAt_partial_fderiv {f : E × F → G} {x : E} {y : F} {m n : WithTop ℕ∞}
    (hf : ContDiffAt ℝ n f (x, y)) (hmn : m + 1 ≤ n) :
    ContDiffAt ℝ m (fun p : E × F => fderiv ℝ (fun z => f (p.1, z)) p.2) (x, y) := by
  have hp : ContDiffAt ℝ n (fun p : (E × F) × F => (p.1.1, p.2)) ((x, y), y) :=
    contDiffAt_fst.fst.prodMk contDiffAt_snd
  have H : ContDiffAt ℝ n
      (Function.uncurry (fun p : E × F => fun z : F => f (p.1, z))) ((x, y), y) :=
    hf.comp ((x, y), y) hp
  exact H.fderiv contDiffAt_snd hmn

end BianchiIX
