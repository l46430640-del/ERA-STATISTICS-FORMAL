import BianchiIX.Dynamics.RestartQuadratic

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- Three conserved quantities give the complete finite reference linear transfer. -/
theorem restart_reference_linear_conservation {I : Set ℝ} (hI : Convex ℝ I)
    {n s a b : ℝ → ℝ} (hn₀ : ∀ t ∈ I, n t ^ 2 < 1)
    (hn : ∀ t ∈ I, HasDerivAt n (n t * restartReferenceStrongRate (n t)) t)
    (hs : ∀ t ∈ I, HasDerivAt s (n t ^ 2 * s t + Real.sqrt 3 * n t * (a t - b t)) t)
    (ha : ∀ t ∈ I, HasDerivAt a (restartReferenceWallRate (n t) * a t) t)
    (hb : ∀ t ∈ I, HasDerivAt b (restartReferenceWallRate (n t) * b t) t)
    {t₀ t : ℝ} (ht₀ : t₀ ∈ I) (ht : t ∈ I) :
    restartShearFactor (n t) * s t + restartShearCoupling (n t) * (a t - b t) =
        restartShearFactor (n t₀) * s t₀ + restartShearCoupling (n t₀) * (a t₀ - b t₀) ∧
      restartWallFactor (n t) * a t = restartWallFactor (n t₀) * a t₀ ∧
      restartWallFactor (n t) * b t = restartWallFactor (n t₀) * b t₀ := by
  have Hconst {f : ℝ → ℝ} (hf : ∀ r ∈ I, HasDerivAt f 0 r) : f t = f t₀ := by
    have H := hI.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun r hr => (hf r hr).hasDerivWithinAt) (C := 0) (fun _ _ => by simp) ht₀ ht
    simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using H
  have Hwall {w : ℝ → ℝ}
      (hw : ∀ r ∈ I, HasDerivAt w (restartReferenceWallRate (n r) * w r) r) :
      restartWallFactor (n t) * w t = restartWallFactor (n t₀) * w t₀ := by
    apply Hconst
    intro r hr
    have HC := (hasDerivAt_restartWallFactor (hn₀ r hr)).differentiableAt.hasDerivAt.comp r (hn r hr)
    have HC0 := (restart_transport_cancellation (hn₀ r hr)).2.1
    convert! HC.mul (hw r hr) using 1
    simp only [Function.comp_def]
    linear_combination -(w r) * HC0
  refine ⟨?_, Hwall ha, Hwall hb⟩
  apply Hconst
  intro r hr
  have HV : HasDerivAt (fun q => a q - b q)
      (restartReferenceWallRate (n r) * (a r - b r) + 0) r := by
    convert! (ha r hr).sub (hb r hr) using 1
    ring
  have H := (hasDerivAt_restart_transported_components (dF := 0) (es := 0) (ev := 0)
    (hn₀ r hr) (by simpa only [add_zero] using hn r hr)
    (by simpa only [add_zero] using hs r hr) HV).1
  simpa only [mul_zero, zero_mul, zero_add, add_zero] using H

/-- The coefficients in (E.2)--(E.3) follow from conservation and `n -> 0`, without an improper forcing integral. -/
theorem tendsto_restart_reference_linear_transfer
    {n s a b : ℝ → ℝ} (hn₀ : ∀ t ∈ Ici (0 : ℝ), n t ^ 2 < 1)
    (hn : ∀ t ∈ Ici (0 : ℝ), HasDerivAt n (n t * restartReferenceStrongRate (n t)) t)
    (hs : ∀ t ∈ Ici (0 : ℝ), HasDerivAt s (n t ^ 2 * s t + Real.sqrt 3 * n t * (a t - b t)) t)
    (ha : ∀ t ∈ Ici (0 : ℝ), HasDerivAt a (restartReferenceWallRate (n t) * a t) t)
    (hb : ∀ t ∈ Ici (0 : ℝ), HasDerivAt b (restartReferenceWallRate (n t) * b t) t)
    (hlim : Tendsto n atTop (𝓝 0)) :
    Tendsto s atTop (𝓝 (restartShearFactor (n 0) * s 0 + restartShearCoupling (n 0) * (a 0 - b 0))) ∧
      Tendsto a atTop (𝓝 (restartWallFactor (n 0) * a 0)) ∧
      Tendsto b atTop (𝓝 (restartWallFactor (n 0) * b 0)) := by
  have HE {t : ℝ} (ht : 0 ≤ t) := restart_reference_linear_conservation (I := Ici (0 : ℝ)) (convex_Ici 0)
    hn₀ hn hs ha hb (t₀ := 0) (by simp) ht
  obtain ⟨HAr, HCr, HKr⟩ := contDiffAt_restart_coefficients (n := 0) (by norm_num) 1
  have HA : Tendsto (fun t => restartShearFactor (n t)) atTop (𝓝 1) := by
    simpa only [restart_coefficients_zero.1, Function.comp_def] using HAr.continuousAt.tendsto.comp hlim
  have HC : Tendsto (fun t => restartWallFactor (n t)) atTop (𝓝 1) := by
    simpa only [restart_coefficients_zero.2.1, Function.comp_def] using HCr.continuousAt.tendsto.comp hlim
  have HK : Tendsto (fun t => restartShearCoupling (n t)) atTop (𝓝 0) := by
    simpa only [restart_coefficients_zero.2.2, Function.comp_def] using HKr.continuousAt.tendsto.comp hlim
  have Halim : Tendsto a atTop (𝓝 (restartWallFactor (n 0) * a 0)) := by
    have H := (tendsto_const_nhds (x := restartWallFactor (n 0) * a 0)).div HC (by norm_num : (1 : ℝ) ≠ 0)
    simp only [div_one] at H
    apply H.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (div_eq_iff (restart_coefficients_pos (hn₀ t ht)).2.ne').mpr
      ((HE ht).2.1.symm.trans (mul_comm _ _))
  have Hblim : Tendsto b atTop (𝓝 (restartWallFactor (n 0) * b 0)) := by
    have H := (tendsto_const_nhds (x := restartWallFactor (n 0) * b 0)).div HC (by norm_num : (1 : ℝ) ≠ 0)
    simp only [div_one] at H
    apply H.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (div_eq_iff (restart_coefficients_pos (hn₀ t ht)).2.ne').mpr
      ((HE ht).2.2.symm.trans (mul_comm _ _))
  refine ⟨?_, Halim, Hblim⟩
  have H := ((HK.mul (Halim.sub Hblim)).const_sub
    (restartShearFactor (n 0) * s 0 + restartShearCoupling (n 0) * (a 0 - b 0))).div HA
      (by norm_num : (1 : ℝ) ≠ 0)
  simp only [zero_mul, sub_zero, div_one] at H
  apply H.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  apply (div_eq_iff (restart_coefficients_pos (hn₀ t ht)).1.ne').mpr
  have HS := (HE ht).1
  linarith only [HS]

end BianchiIX
