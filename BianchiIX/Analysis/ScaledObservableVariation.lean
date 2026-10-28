import BianchiIX.Analysis.ClockVariation

noncomputable section

namespace BianchiIX

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A common time multiplier acts on the observable variation without a spatial rate derivative. -/
theorem hasDerivAt_scaled_observable_variation
    {p : E → F} {f : E → E} {Y v : ℝ → E} {t a : ℝ}
    (hp : ContDiffAt ℝ 2 p (Y t)) (hf : DifferentiableAt ℝ f (Y t))
    (hY : HasDerivAt Y (a • f (Y t)) t)
    (hv : HasDerivAt v (a • fderiv ℝ f (Y t) (v t)) t) :
    HasDerivAt (fun s => fderiv ℝ p (Y s) (v s))
      (a • fderiv ℝ (fun x => fderiv ℝ p x (f x)) (Y t) (v t)) t := by
  have hdp : DifferentiableAt ℝ (fderiv ℝ p) (Y t) :=
    (hp.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hLie := hdp.hasFDerivAt.clm_apply hf.hasFDerivAt
  have hsym := (hp.isSymmSndFDerivAt (by norm_num)).eq (f (Y t)) (v t)
  have hd := (hdp.hasFDerivAt.comp_hasDerivAt t hY).clm_apply hv
  convert! hd using 1
  rw [hLie.fderiv]
  change a • (fderiv ℝ p (Y t) (fderiv ℝ f (Y t) (v t)) +
      fderiv ℝ (fderiv ℝ p) (Y t) (v t) (f (Y t))) = _
  simp only [map_smul, smul_apply, smul_add, Function.comp_apply]
  rw [hsym]
  module

end BianchiIX
