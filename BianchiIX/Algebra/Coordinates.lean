import BianchiIX.Algebra.Projective
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! The exact projective coordinate change in Section 1.2. -/

namespace BianchiIX

noncomputable section

def projectiveCoord (p z : ℝ) : ℝ := Real.sqrt 3 * z / (1 + p)

def projectiveDenom (m u v w : ℝ) : ℝ := 3 + m ^ 2 + curvature u v w

theorem projectiveDenom_eq (m u v w : ℝ) :
    projectiveDenom m u v w = 3 + m ^ 2 + u ^ 2 + (v - w) ^ 2 - 2 * u * (v + w) := by
  unfold projectiveDenom curvature
  ring

theorem projectiveDenom_of_constraint
    {p s a b c : ℝ} (hA : 1 + p ≠ 0) (hG : constraint p s a b c = 1) :
    projectiveDenom (projectiveCoord p s) (projectiveCoord p a)
      (projectiveCoord p b) (projectiveCoord p c) = 6 / (1 + p) := by
  have hr : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  unfold projectiveDenom projectiveCoord curvature
  field_simp
  ring_nf
  rw [hr]
  unfold constraint shearSq curvature at hG
  nlinarith only [hG]

theorem projective_inverse_scale
    {p s a b c : ℝ} (hA : 1 + p ≠ 0) (hG : constraint p s a b c = 1) :
    6 / projectiveDenom (projectiveCoord p s) (projectiveCoord p a)
      (projectiveCoord p b) (projectiveCoord p c) = 1 + p := by
  rw [projectiveDenom_of_constraint hA hG]
  field_simp

theorem projectiveDenom_positive
    {p s a b c : ℝ} (hA : 0 < 1 + p) (hG : constraint p s a b c = 1) :
    0 < projectiveDenom (projectiveCoord p s) (projectiveCoord p a)
      (projectiveCoord p b) (projectiveCoord p c) := by
  rw [projectiveDenom_of_constraint (ne_of_gt hA) hG]
  exact div_pos (by norm_num) hA

theorem projective_inverse_coord {p z : ℝ} (hA : 1 + p ≠ 0) :
    (1 + p) * projectiveCoord p z / Real.sqrt 3 = z := by
  have hr : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  unfold projectiveCoord
  field_simp

theorem projective_forward_coord {A z : ℝ} (hA : A ≠ 0) :
    projectiveCoord (A - 1) (A * z / Real.sqrt 3) = z := by
  have hr : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  unfold projectiveCoord
  rw [show 1 + (A - 1) = A by ring]
  field_simp

theorem constraint_of_projective
    {A m u v w : ℝ} (hD : A * projectiveDenom m u v w = 6) :
    constraint (A - 1) (A * m / Real.sqrt 3) (A * u / Real.sqrt 3)
      (A * v / Real.sqrt 3) (A * w / Real.sqrt 3) = 1 := by
  have hr : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hr2 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  unfold constraint shearSq curvature
  field_simp
  ring_nf
  rw [hr2]
  unfold projectiveDenom curvature at hD
  nlinarith only [congrArg (fun x => A * x) hD]

theorem constraint_of_inverse_projective
    {m u v w : ℝ} (hD : projectiveDenom m u v w ≠ 0) :
    let A := 6 / projectiveDenom m u v w
    constraint (A - 1) (A * m / Real.sqrt 3) (A * u / Real.sqrt 3)
      (A * v / Real.sqrt 3) (A * w / Real.sqrt 3) = 1 := by
  apply constraint_of_projective
  field_simp

/-- Quotient differentiation with the original time variable. -/
theorem hasDerivAt_projectiveCoord
    {p z : ℝ → ℝ} {p' z' t : ℝ}
    (hp : HasDerivAt p p' t) (hz : HasDerivAt z z' t) (hA : 1 + p t ≠ 0) :
    HasDerivAt (fun x => projectiveCoord (p x) (z x))
      (Real.sqrt 3 * (z' * (1 + p t) - z t * p') / (1 + p t) ^ 2) t := by
  convert (hz.const_mul (Real.sqrt 3)).div (hp.const_add 1) hA using 1 <;>
    first | rfl | ring

theorem phase_velocity_in_original_time
    {p s a b c : ℝ} (hA : 1 + p ≠ 0) :
    Real.sqrt 3 * (shearMinus s a b c * (1 + p) - s * shearPlus p a b c) /
      (1 + p) ^ 2 = (1 + p) * phaseVelocity
        (projectiveCoord p s) (projectiveCoord p a) (projectiveCoord p b)
        (projectiveCoord p c) := by
  have hr : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  unfold projectiveCoord phaseVelocity coupling shearMinus shearPlus curvature
  field_simp
  ring_nf
  rw [hr]

theorem strong_velocity_in_original_time
    {p s a b c : ℝ} (hA : 1 + p ≠ 0) (hG : constraint p s a b c = 1) :
    Real.sqrt 3 * ((rateOne p s * a) * (1 + p) - a * shearPlus p a b c) /
      (1 + p) ^ 2 = (1 + p) * strongVelocity
        (projectiveCoord p s) (projectiveCoord p a) (projectiveCoord p b)
        (projectiveCoord p c) := by
  have hr : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  unfold projectiveCoord strongVelocity rateOne shearSq shearPlus curvature
  field_simp
  ring_nf
  rw [hr]
  unfold constraint shearSq curvature at hG
  linear_combination a * (1 - 2 * p) * hG

theorem active_velocity_in_original_time
    {p s a b c : ℝ} (hA : 1 + p ≠ 0) (hG : constraint p s a b c = 1) :
    Real.sqrt 3 * ((rateTwo p s * b) * (1 + p) - b * shearPlus p a b c) /
      (1 + p) ^ 2 = (1 + p) * activeVelocity
        (projectiveCoord p s) (projectiveCoord p a) (projectiveCoord p b)
        (projectiveCoord p c) := by
  have hr : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  unfold projectiveCoord activeVelocity coupling rateTwo shearSq shearPlus curvature
  field_simp
  ring_nf
  rw [hr]
  unfold constraint shearSq curvature at hG
  linear_combination -b * (1 + p) * hG

theorem weak_velocity_in_original_time
    {p s a b c : ℝ} (hA : 1 + p ≠ 0) (hG : constraint p s a b c = 1) :
    Real.sqrt 3 * ((rateThree p s * c) * (1 + p) - c * shearPlus p a b c) /
      (1 + p) ^ 2 = (1 + p) * weakVelocity
        (projectiveCoord p s) (projectiveCoord p a) (projectiveCoord p b)
        (projectiveCoord p c) := by
  have hr : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  unfold projectiveCoord weakVelocity coupling rateThree shearSq shearPlus curvature
  field_simp
  ring_nf
  rw [hr]
  unfold constraint shearSq curvature at hG
  linear_combination -c * (1 + p) * hG

theorem hasDerivAt_projective_flow
    {p s a b c : ℝ → ℝ} {t : ℝ}
    (hp : HasDerivAt p (shearPlus (p t) (a t) (b t) (c t)) t)
    (hs : HasDerivAt s (shearMinus (s t) (a t) (b t) (c t)) t)
    (ha : HasDerivAt a (rateOne (p t) (s t) * a t) t)
    (hb : HasDerivAt b (rateTwo (p t) (s t) * b t) t)
    (hc : HasDerivAt c (rateThree (p t) (s t) * c t) t)
    (hA : 1 + p t ≠ 0) (hG : constraint (p t) (s t) (a t) (b t) (c t) = 1) :
    let m := projectiveCoord (p t) (s t)
    let u := projectiveCoord (p t) (a t)
    let v := projectiveCoord (p t) (b t)
    let w := projectiveCoord (p t) (c t)
    HasDerivAt (fun x => projectiveCoord (p x) (s x)) ((1 + p t) * phaseVelocity m u v w) t ∧
    HasDerivAt (fun x => projectiveCoord (p x) (a x)) ((1 + p t) * strongVelocity m u v w) t ∧
    HasDerivAt (fun x => projectiveCoord (p x) (b x)) ((1 + p t) * activeVelocity m u v w) t ∧
    HasDerivAt (fun x => projectiveCoord (p x) (c x)) ((1 + p t) * weakVelocity m u v w) t := by
  have hm := hasDerivAt_projectiveCoord hp hs hA
  have hu := hasDerivAt_projectiveCoord hp ha hA
  have hv := hasDerivAt_projectiveCoord hp hb hA
  have hw := hasDerivAt_projectiveCoord hp hc hA
  rw [phase_velocity_in_original_time hA] at hm
  rw [strong_velocity_in_original_time hA hG] at hu
  rw [active_velocity_in_original_time hA hG] at hv
  rw [weak_velocity_in_original_time hA hG] at hw
  exact ⟨hm, hu, hv, hw⟩

/-- A specified reciprocal clock removes the positive time factor. -/
theorem hasDerivAt_reciprocal_clock
    {f clock : ℝ → ℝ} {tau A v : ℝ} (hA : A ≠ 0)
    (hf : HasDerivAt f (A * v) (clock tau))
    (hclock : HasDerivAt clock (1 / A) tau) :
    HasDerivAt (fun x => f (clock x)) v tau := by
  convert hf.comp tau hclock using 1 <;> first | rfl | field_simp

theorem projective_clock_positive {p : ℝ} (hA : 0 < 1 + p) :
    0 < 1 / (1 + p) := one_div_pos.mpr hA

theorem hasDerivAt_reparametrized_projective_flow
    {p s a b c clock : ℝ → ℝ} {tau : ℝ}
    (hp : HasDerivAt p (shearPlus (p (clock tau)) (a (clock tau)) (b (clock tau)) (c (clock tau))) (clock tau))
    (hs : HasDerivAt s (shearMinus (s (clock tau)) (a (clock tau)) (b (clock tau)) (c (clock tau))) (clock tau))
    (ha : HasDerivAt a (rateOne (p (clock tau)) (s (clock tau)) * a (clock tau)) (clock tau))
    (hb : HasDerivAt b (rateTwo (p (clock tau)) (s (clock tau)) * b (clock tau)) (clock tau))
    (hc : HasDerivAt c (rateThree (p (clock tau)) (s (clock tau)) * c (clock tau)) (clock tau))
    (hA : 0 < 1 + p (clock tau))
    (hG : constraint (p (clock tau)) (s (clock tau)) (a (clock tau)) (b (clock tau)) (c (clock tau)) = 1)
    (hclock : HasDerivAt clock (1 / (1 + p (clock tau))) tau) :
    let m := projectiveCoord (p (clock tau)) (s (clock tau))
    let u := projectiveCoord (p (clock tau)) (a (clock tau))
    let v := projectiveCoord (p (clock tau)) (b (clock tau))
    let w := projectiveCoord (p (clock tau)) (c (clock tau))
    HasDerivAt (fun x => projectiveCoord (p (clock x)) (s (clock x))) (phaseVelocity m u v w) tau ∧
    HasDerivAt (fun x => projectiveCoord (p (clock x)) (a (clock x))) (strongVelocity m u v w) tau ∧
    HasDerivAt (fun x => projectiveCoord (p (clock x)) (b (clock x))) (activeVelocity m u v w) tau ∧
    HasDerivAt (fun x => projectiveCoord (p (clock x)) (c (clock x))) (weakVelocity m u v w) tau := by
  have h := hasDerivAt_projective_flow hp hs ha hb hc (ne_of_gt hA) hG
  exact ⟨hasDerivAt_reciprocal_clock (ne_of_gt hA) h.1 hclock,
    hasDerivAt_reciprocal_clock (ne_of_gt hA) h.2.1 hclock,
    hasDerivAt_reciprocal_clock (ne_of_gt hA) h.2.2.1 hclock,
    hasDerivAt_reciprocal_clock (ne_of_gt hA) h.2.2.2 hclock⟩

end

end BianchiIX
