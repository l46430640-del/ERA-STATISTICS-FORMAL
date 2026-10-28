import BianchiIX.Analysis.NormIntegralForcing
import BianchiIX.Analysis.CoreIntegrals
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section

namespace BianchiIX

open Set MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Two time moments control the shear-wall feedback without a smallness or absorption hypothesis. -/
theorem two_moment_variation_bound {s s' b : ℝ → ℝ} {l l' : ℝ → E} {T : ℝ}
    (hT : 0 ≤ T) (hs : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt s (s' t) t)
    (hl : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt l (l' t) t)
    (hb : ContinuousOn b (Icc (0 : ℝ) T)) (hb0 : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ b t)
    (hds : ∀ t ∈ Icc (0 : ℝ) T, |s' t| ≤ 2 * b t * |s t| + 4 * b t * ‖l t‖)
    (hdl : ∀ t ∈ Icc (0 : ℝ) T, ‖l' t‖ ≤ 2 * |s t| + 9 * b t * ‖l t‖) :
    let J₀ := ∫ t in 0..T, b t
    let J₁ := ∫ t in 0..T, t * b t
    let c := Real.exp (9 * J₀)
    let B := (|s 0| + 4 * c * ‖l 0‖ * J₀) * Real.exp (2 * J₀ + 8 * c * J₁)
    ∀ t ∈ Icc (0 : ℝ) T, |s t| ≤ B ∧ ‖l t‖ ≤ c * (‖l 0‖ + 2 * t * B) := by
  intro J₀ J₁ c B
  have hc : 0 ≤ c := (Real.exp_pos _).le
  have hsc := (HasDerivAt.continuousOn hs).abs
  have hlc := (HasDerivAt.continuousOn hl).norm
  let F : ℝ → ℝ := fun t => 2 * b t * |s t| + 4 * b t * ‖l t‖
  have hF : ContinuousOn F (Icc (0 : ℝ) T) :=
    ((hb.const_mul 2).mul hsc).add ((hb.const_mul 4).mul hlc)
  have hF0 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : 0 ≤ F t := by
    dsimp only [F]; positivity [hb0 t ht]
  let G : ℝ → ℝ := fun t => F (projIcc 0 T hT t)
  let S : ℝ → ℝ := fun t => |s 0| + ∫ u in 0..t, G u
  have hG : Continuous G := hF.domRestrict.comp continuous_projIcc
  have hGe (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : G t = F t := by simp only [G, projIcc_of_mem hT ht]
  have hS (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : HasDerivAt S (F t) t := by
    rw [← hGe t ht]
    exact (intervalIntegral.integral_hasDerivAt_right (hG.intervalIntegrable _ _)
      hG.stronglyMeasurable.stronglyMeasurableAtFilter hG.continuousAt).const_add _
  have hSi : S 0 = |s 0| := by simp [S]
  have hSm : MonotoneOn S (Icc (0 : ℝ) T) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 T) (HasDerivAt.continuousOn hS)
      (fun t ht => (hS t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => hF0 t (interior_subset ht))
  have hS0 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : 0 ≤ S t :=
    (abs_nonneg (s 0)).trans (hSi ▸ hSm ⟨le_rfl, hT⟩ ht ht.1)
  have hsS (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : |s t| ≤ S t := by
    have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T := Icc_subset_Icc_right ht.2
    have H := abs_sub_le_integral_bound ht.1 (fun u hu => hs u (hsub hu)) (hF.mono hsub)
      (fun u hu => hds u (hsub hu))
    have HI : (∫ u in 0..t, G u) = ∫ u in 0..t, F u := intervalIntegral.integral_congr
      (fun u hu => hGe u (hsub (uIcc_of_le ht.1 ▸ hu)))
    dsimp only [S]
    rw [HI]
    have HA := abs_add_le (s t - s 0) (s 0)
    rw [sub_add_cancel] at HA
    linarith only [HA, H]
  have Hprefix {g : ℝ → ℝ} (hg : ContinuousOn g (Icc (0 : ℝ) T))
      (hg0 : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ g t) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      (∫ u in 0..t, g u) ≤ ∫ u in 0..T, g u :=
    intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
      (ae_restrict_of_forall_mem measurableSet_Ioc (fun u hu => hg0 u ⟨hu.1.le, hu.2⟩))
      (hg.intervalIntegrable_of_Icc hT)
  have hlS (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : ‖l t‖ ≤ c * (‖l 0‖ + 2 * t * S t) := by
    have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T := Icc_subset_Icc_right ht.2
    have H := norm_le_exp_integral_of_norm_deriv ht.1 (fun u hu => hl u (hsub hu))
      ((hb.const_mul 9).mono hsub) ((hsc.const_mul 2).mono hsub)
      (fun u hu => by positivity [hb0 u (hsub hu)]) (fun u _ => by positivity)
      (fun u hu => by linarith only [hdl u (hsub hu)])
    have HB : (∫ u in 0..t, 2 * |s u|) ≤ 2 * t * S t := by
      have HI : (∫ u in 0..t, 2 * |s u|) ≤ ∫ _u in 0..t, 2 * S t := intervalIntegral.integral_mono_on ht.1
        (((hsc.const_mul 2).mono hsub).intervalIntegrable_of_Icc ht.1)
        (continuous_const.intervalIntegrable 0 t)
        (fun u hu => mul_le_mul_of_nonneg_left ((hsS u (hsub hu)).trans (hSm (hsub hu) ht hu.2)) (by norm_num : (0 : ℝ) ≤ 2))
      simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_left_comm, mul_assoc] using HI
    have HE : Real.exp (∫ u in 0..t, 9 * b u) ≤ c := by
      rw [intervalIntegral.integral_const_mul]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Hprefix hb hb0 t ht) (by norm_num))
    have HP := mul_le_mul (add_le_add le_rfl HB) HE (Real.exp_pos _).le
      (by positivity [hS0 t ht, ht.1] : 0 ≤ ‖l 0‖ + 2 * t * S t)
    exact H.trans (HP.trans_eq (mul_comm _ _))
  let k : ℝ → ℝ := fun t => (2 + 8 * c * t) * b t
  let e : ℝ → ℝ := fun t => 4 * c * ‖l 0‖ * b t
  have hk : ContinuousOn k (Icc (0 : ℝ) T) := (continuousOn_const.add (continuousOn_const.mul continuousOn_id)).mul hb
  have he : ContinuousOn e (Icc (0 : ℝ) T) := hb.const_mul _
  have hk0 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : 0 ≤ k t := by dsimp only [k]; positivity [hb0 t ht, ht.1]
  have he0 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : 0 ≤ e t := by dsimp only [e]; positivity [hb0 t ht]
  have HdS (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : ‖F t‖ ≤ k t * ‖S t‖ + e t := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hF0 t ht), Real.norm_eq_abs, abs_of_nonneg (hS0 t ht)]
    dsimp only [F, k, e]
    have H1 := mul_le_mul_of_nonneg_left (hsS t ht) (by positivity [hb0 t ht] : 0 ≤ 2 * b t)
    have H2 := mul_le_mul_of_nonneg_left (hlS t ht) (by positivity [hb0 t ht] : 0 ≤ 4 * b t)
    nlinarith only [H1, H2]
  have Hk : (∫ t in 0..T, k t) = 2 * J₀ + 8 * c * J₁ := by
    have H : k = fun t => 2 * b t + (8 * c) * (t * b t) := by ext t; dsimp only [k]; ring
    have HI₁ : IntervalIntegrable (fun t => 2 * b t) volume 0 T := (hb.const_mul 2).intervalIntegrable_of_Icc hT
    have HI₂ : IntervalIntegrable (fun t => 8 * c * (t * b t)) volume 0 T :=
      ((continuousOn_id.mul hb).const_mul (8 * c)).intervalIntegrable_of_Icc hT
    rw [H, intervalIntegral.integral_add HI₁ HI₂,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have He : (∫ t in 0..T, e t) = 4 * c * ‖l 0‖ * J₀ := intervalIntegral.integral_const_mul _ _
  have HSB (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : S t ≤ B := by
    have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T := Icc_subset_Icc_right ht.2
    have H := norm_le_exp_integral_of_norm_deriv ht.1 (fun u hu => hS u (hsub hu))
      (hk.mono hsub) (he.mono hsub) (fun u hu => hk0 u (hsub hu)) (fun u hu => he0 u (hsub hu))
      (fun u hu => HdS u (hsub hu))
    rw [Real.norm_eq_abs, abs_of_nonneg (hS0 t ht), hSi, Real.norm_eq_abs, abs_abs] at H
    have HE := Hprefix he he0 t ht
    have HK := Hprefix hk hk0 t ht
    rw [He] at HE
    rw [Hk] at HK
    have hJ₀ : 0 ≤ J₀ := intervalIntegral.integral_nonneg hT hb0
    exact H.trans (mul_le_mul (add_le_add le_rfl HE) (Real.exp_le_exp.mpr HK) (Real.exp_pos _).le
      (by positivity : 0 ≤ |s 0| + 4 * c * ‖l 0‖ * J₀))
  intro t ht
  refine ⟨(hsS t ht).trans (HSB t ht), (hlS t ht).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (HSB t ht) (by positivity [ht.1] : 0 ≤ 2 * t))) hc

/-- The numerical budgets in (E.44) give the uniform shear bound and linear logarithmic growth. -/
theorem two_moment_variation_small {s s' b : ℝ → ℝ} {l l' : ℝ → E} {T : ℝ}
    (hT : 0 ≤ T) (hs : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt s (s' t) t)
    (hl : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt l (l' t) t)
    (hb : ContinuousOn b (Icc (0 : ℝ) T)) (hb0 : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ b t)
    (hds : ∀ t ∈ Icc (0 : ℝ) T, |s' t| ≤ 2 * b t * |s t| + 4 * b t * ‖l t‖)
    (hdl : ∀ t ∈ Icc (0 : ℝ) T, ‖l' t‖ ≤ 2 * |s t| + 9 * b t * ‖l t‖)
    (hinit : |s 0| ≤ 2)
    (hsmall : 9 * (∫ t in 0..T, b t) ≤ Real.log 2 ∧
      2 * (∫ t in 0..T, b t) + 16 * (∫ t in 0..T, t * b t) ≤ 1 / 2 ∧
      ‖l 0‖ * (∫ t in 0..T, b t) ≤ 1 / 16) :
    ∀ t ∈ Icc (0 : ℝ) T, |s t| ≤ 5 ∧ ‖l t‖ ≤ 2 * ‖l 0‖ + 20 * t := by
  let J₀ := ∫ t in 0..T, b t
  let J₁ := ∫ t in 0..T, t * b t
  let c := Real.exp (9 * J₀)
  have hc0 : 0 ≤ c := (Real.exp_pos _).le
  have hc : c ≤ 2 := (Real.exp_le_exp.mpr hsmall.1).trans_eq (Real.exp_log (by norm_num))
  have hJ₀ : 0 ≤ J₀ := intervalIntegral.integral_nonneg hT hb0
  have hJ₁ : 0 ≤ J₁ := intervalIntegral.integral_nonneg hT (fun t ht => mul_nonneg ht.1 (hb0 t ht))
  have Hexp : Real.exp (2 * J₀ + 8 * c * J₁) ≤ 2 := by
    have He := Real.exp_lt_two_add_div_two_sub (x := (1 : ℝ) / 2) (by norm_num) (by norm_num)
    norm_num at He
    apply (Real.exp_le_exp.mpr (show 2 * J₀ + 8 * c * J₁ ≤ 1 / 2 by
      nlinarith only [hsmall.2.1, mul_le_mul_of_nonneg_right hc hJ₁])).trans
    linarith only [He]
  have Hfac : |s 0| + 4 * c * ‖l 0‖ * J₀ ≤ 5 / 2 := by
    have H := mul_le_mul hc hsmall.2.2 (mul_nonneg (norm_nonneg _) hJ₀) (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith only [H, hinit]
  have HB : (|s 0| + 4 * c * ‖l 0‖ * J₀) * Real.exp (2 * J₀ + 8 * c * J₁) ≤ 5 := by
    have H := mul_le_mul Hfac Hexp (Real.exp_pos _).le (by norm_num : (0 : ℝ) ≤ 5 / 2)
    norm_num at H
    exact H
  have H := two_moment_variation_bound hT hs hl hb hb0 hds hdl
  intro t ht
  refine ⟨(H t ht).1.trans HB, (H t ht).2.trans ?_⟩
  have Hinner := mul_le_mul_of_nonneg_left HB (by positivity [ht.1] : 0 ≤ 2 * t)
  have Houter := mul_le_mul hc (add_le_add le_rfl Hinner)
    (by positivity [hJ₀, ht.1] : 0 ≤ ‖l 0‖ + 2 * t * ((|s 0| + 4 * c * ‖l 0‖ * J₀) * Real.exp (2 * J₀ + 8 * c * J₁)))
    (by norm_num : (0 : ℝ) ≤ 2)
  exact Houter.trans_eq (by ring)

end BianchiIX
