import BianchiIX.Statistics.GaussCoding
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Finite-prefix distortion along the actual branch inputs, Section 3.3. -/

namespace BianchiIX

noncomputable section

open Set Finset

/-- The pair `(q_n, q_{n-1})`, with initial pair `(1, 0)`. -/
def gaussDenoms (a : ℕ → ℕ+) : ℕ → ℝ × ℝ
  | 0 => (1, 0)
  | n + 1 => ((a n : ℝ) * (gaussDenoms a n).1 + (gaussDenoms a n).2,
      (gaussDenoms a n).1)

theorem gaussDenoms_bounds (a : ℕ → ℕ+) (n : ℕ) :
    1 ≤ (gaussDenoms a n).1 ∧ 0 ≤ (gaussDenoms a n).2 ∧
      (gaussDenoms a n).2 ≤ (gaussDenoms a n).1 := by
  induction n with
  | zero => norm_num [gaussDenoms]
  | succ n ih =>
    have ha : (1 : ℝ) ≤ a n := by exact_mod_cast Nat.succ_le_of_lt (a n).pos
    have hmul : (gaussDenoms a n).1 ≤ (a n : ℝ) * (gaussDenoms a n).1 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr ha) (show 0 ≤ (gaussDenoms a n).1 by linarith [ih.1])]
    simp only [gaussDenoms]
    exact ⟨by linarith [ih.1, ih.2.1], by linarith [ih.1], by linarith [ih.2.1]⟩

def gaussDenom (a : ℕ → ℕ+) (n : ℕ) (x : ℝ) : ℝ :=
  (gaussDenoms a n).1 + (gaussDenoms a n).2 * x

theorem gaussDenom_pos (a : ℕ → ℕ+) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 < gaussDenom a n x := by
  have h := gaussDenoms_bounds a n
  dsimp [gaussDenom]
  nlinarith [mul_nonneg h.2.1 hx]

theorem gaussDenom_succ (a : ℕ → ℕ+) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    gaussDenom a (n + 1) x = gaussDenom a n (gaussInv (a n) x) * ((a n : ℝ) + x) := by
  have ha : (1 : ℝ) ≤ a n := by exact_mod_cast Nat.succ_le_of_lt (a n).pos
  have hax : (a n : ℝ) + x ≠ 0 := ne_of_gt (by linarith)
  dsimp [gaussDenom, gaussDenoms, gaussInv]
  field_simp
  ring

theorem gaussWord_prefix_succ (a : ℕ → ℕ+) (n : ℕ) (x : ℝ) :
    gaussWord (digitPrefix a (n + 1)) x =
      gaussWord (digitPrefix a n) (gaussInv (a n) x) := by
  rw [digitPrefix_add, gaussWord_append]
  simp [digitPrefix, shiftDigits, gaussWord]

theorem hasDerivAt_gaussWord_prefix (a : ℕ → ℕ+) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (gaussWord (digitPrefix a n))
      ((-1 : ℝ) ^ n / (gaussDenom a n x) ^ 2) x := by
  induction n generalizing x with
  | zero =>
    convert! (hasDerivAt_id x) using 1
    norm_num [gaussDenom, gaussDenoms]
  | succ n ih =>
    have ha : (1 : ℝ) ≤ a n := by exact_mod_cast Nat.succ_le_of_lt (a n).pos
    have hg := hasDerivAt_gaussInv ha hx
    have hp := ih (gaussInv_pos ha hx).le
    have h := hp.comp x hg
    have hf : gaussWord (digitPrefix a (n + 1)) =
        fun t => gaussWord (digitPrefix a n) (gaussInv (a n) t) := by
      funext t
      exact gaussWord_prefix_succ a n t
    rw [hf]
    convert! h using 1
    rw [gaussDenom_succ a n hx, pow_succ, mul_pow, div_mul_div_comm]

theorem abs_deriv_gaussWord_prefix (a : ℕ → ℕ+) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    |deriv (gaussWord (digitPrefix a n)) x| = 1 / (gaussDenom a n x) ^ 2 := by
  rw [(hasDerivAt_gaussWord_prefix a n hx).deriv, abs_div, abs_pow, abs_neg,
    abs_one, one_pow, abs_pow, abs_of_pos (gaussDenom_pos a n hx)]

theorem deriv_gaussWord_prefix_ne_zero (a : ℕ → ℕ+) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    deriv (gaussWord (digitPrefix a n)) x ≠ 0 := by
  have h : 0 < |deriv (gaussWord (digitPrefix a n)) x| := by
    rw [abs_deriv_gaussWord_prefix a n hx]
    have hpos := gaussDenom_pos a n hx
    positivity
  exact (abs_pos.mp h)

def gaussPrefixLog (a : ℕ → ℕ+) (n : ℕ) (x : ℝ) : ℝ :=
  -2 * Real.log (gaussDenom a n x)

theorem log_abs_deriv_gaussWord_prefix (a : ℕ → ℕ+) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    Real.log |deriv (gaussWord (digitPrefix a n)) x| = gaussPrefixLog a n x := by
  rw [abs_deriv_gaussWord_prefix a n hx, one_div, Real.log_inv, Real.log_pow]
  simp [gaussPrefixLog]

theorem gaussPrefixLog_zero (a : ℕ → ℕ+) (x : ℝ) : gaussPrefixLog a 0 x = 0 := by
  simp [gaussPrefixLog, gaussDenom, gaussDenoms]

theorem gaussPrefixLog_succ (a : ℕ → ℕ+) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    gaussPrefixLog a (n + 1) x = gaussPrefixLog a n (gaussInv (a n) x) +
      Real.log |deriv (gaussInv (a n)) x| := by
  have ha : (1 : ℝ) ≤ a n := by exact_mod_cast Nat.succ_le_of_lt (a n).pos
  have hax : 0 < (a n : ℝ) + x := by linarith
  rw [(hasDerivAt_gaussInv ha hx).deriv]
  simp only [abs_div, abs_neg, abs_one, abs_pow, abs_of_pos hax]
  rw [one_div, Real.log_inv, Real.log_pow]
  unfold gaussPrefixLog
  rw [gaussDenom_succ a n hx,
    Real.log_mul (gaussDenom_pos a n (gaussInv_pos ha hx).le).ne' hax.ne']
  push_cast
  ring

theorem gaussPrefixLog_lipschitz (a : ℕ → ℕ+) (n : ℕ)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |gaussPrefixLog a n x - gaussPrefixLog a n y| ≤ 2 * |x - y| := by
  have hd (t : ℝ) (ht : t ∈ Ici (0 : ℝ)) :
      HasDerivWithinAt (gaussPrefixLog a n)
        (-2 * ((gaussDenoms a n).2 / gaussDenom a n t)) (Ici 0) t := by
    have h := (((hasDerivAt_id t).const_mul (gaussDenoms a n).2).const_add
      (gaussDenoms a n).1).log (gaussDenom_pos a n ht).ne'
    convert! (h.const_mul (-2)).hasDerivWithinAt (s := Ici 0) using 1
    simp [gaussDenom]
  have hb (t : ℝ) (ht : t ∈ Ici (0 : ℝ)) :
      ‖-2 * ((gaussDenoms a n).2 / gaussDenom a n t)‖ ≤ (2 : ℝ) := by
    have h := gaussDenoms_bounds a n
    have hpos := gaussDenom_pos a n ht
    have hrat : (gaussDenoms a n).2 / gaussDenom a n t ≤ 1 := by
      apply (div_le_one hpos).mpr
      dsimp [gaussDenom]
      nlinarith [mul_nonneg h.2.1 ht]
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_nonneg h.2.1, abs_of_pos hpos]
    norm_num
    linarith
  simpa only [Real.norm_eq_abs] using
    (convex_Ici (0 : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le hd hb hy hx

theorem gauss_log_sum_distortion (a : ℕ → ℕ+) (D Y d e : ℕ → ℝ) (n : ℕ)
    (hy : ∀ j ≤ n, 0 ≤ Y j) (hD : ∀ j < n, D j ≠ 0)
    (hvalue : ∀ j < n, |Y j - gaussInv (a j) (Y (j + 1))| ≤ d j)
    (hlog : ∀ j < n,
      |Real.log (|D j| / |deriv (gaussInv (a j)) (Y (j + 1))|)| ≤ e j) :
    |(∑ j ∈ range n, Real.log |D j|) - gaussPrefixLog a n (Y n)| ≤
      ∑ j ∈ range n, (e j + if j = 0 then 0 else 2 * d j) := by
  induction n with
  | zero => simp [gaussPrefixLog_zero]
  | succ n ih =>
    have hprev := ih (fun j hj => hy j (by omega)) (fun j hj => hD j (by omega))
      (fun j hj => hvalue j (by omega)) (fun j hj => hlog j (by omega))
    have ha : (1 : ℝ) ≤ a n := by exact_mod_cast Nat.succ_le_of_lt (a n).pos
    have hyn := hy (n + 1) le_rfl
    have hg : deriv (gaussInv (a n)) (Y (n + 1)) ≠ 0 := by
      rw [(hasDerivAt_gaussInv ha hyn).deriv]
      exact div_ne_zero (by norm_num) (pow_ne_zero _ (ne_of_gt (by linarith)))
    have hstep := hlog n (by omega)
    rw [Real.log_div (abs_ne_zero.mpr (hD n (by omega))) (abs_ne_zero.mpr hg)] at hstep
    have hphase :
        |gaussPrefixLog a n (Y n) - gaussPrefixLog a n (gaussInv (a n) (Y (n + 1)))| ≤
          if n = 0 then 0 else 2 * d n := by
      by_cases hn : n = 0
      · simp [hn, gaussPrefixLog_zero]
      · rw [if_neg hn]
        exact (gaussPrefixLog_lipschitz a n (hy n (by omega)) (gaussInv_pos ha hyn).le).trans
          (mul_le_mul_of_nonneg_left (hvalue n (by omega)) (by norm_num))
    let R := (∑ j ∈ range n, Real.log |D j|) - gaussPrefixLog a n (Y n)
    let P := gaussPrefixLog a n (Y n) - gaussPrefixLog a n (gaussInv (a n) (Y (n + 1)))
    let E := Real.log |D n| - Real.log |deriv (gaussInv (a n)) (Y (n + 1))|
    have heq : (∑ j ∈ range (n + 1), Real.log |D j|) -
        gaussPrefixLog a (n + 1) (Y (n + 1)) = R + P + E := by
      rw [sum_range_succ, gaussPrefixLog_succ a n hyn]
      dsimp [R, P, E]
      ring
    rw [heq, sum_range_succ]
    calc
      |R + P + E| ≤ |R| + |P| + |E| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le R P) le_rfl)
      _ ≤ _ := by dsimp [R, P, E]; linarith

theorem gauss_log_product_distortion (a : ℕ → ℕ+) (D Y d e : ℕ → ℝ) (n : ℕ)
    (hy : ∀ j ≤ n, 0 ≤ Y j) (hD : ∀ j < n, D j ≠ 0)
    (hvalue : ∀ j < n, |Y j - gaussInv (a j) (Y (j + 1))| ≤ d j)
    (hlog : ∀ j < n,
      |Real.log (|D j| / |deriv (gaussInv (a j)) (Y (j + 1))|)| ≤ e j) :
    |Real.log (|∏ j ∈ range n, D j| / |deriv (gaussWord (digitPrefix a n)) (Y n)|)| ≤
      ∑ j ∈ range n, (e j + if j = 0 then 0 else 2 * d j) := by
  have hp : (∏ j ∈ range n, D j) ≠ 0 := prod_ne_zero_iff.mpr (fun j hj => hD j (mem_range.mp hj))
  rw [Real.log_div (abs_ne_zero.mpr hp)
    (abs_ne_zero.mpr (deriv_gaussWord_prefix_ne_zero a n (hy n le_rfl))),
    log_abs_deriv_gaussWord_prefix a n (hy n le_rfl), abs_prod,
    Real.log_prod (fun j hj => abs_ne_zero.mpr (hD j (mem_range.mp hj)))]
  exact gauss_log_sum_distortion a D Y d e n hy hD hvalue hlog

def branchPrefix (h : ℕ → ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0, x => x
  | n + 1, x => branchPrefix h n (h n x)

theorem hasDerivAt_branchPrefix (h : ℕ → ℝ → ℝ) (D Y : ℕ → ℝ) (n : ℕ)
    (hrec : ∀ j < n, h j (Y (j + 1)) = Y j)
    (hder : ∀ j < n, HasDerivAt (h j) (D j) (Y (j + 1))) :
    HasDerivAt (branchPrefix h n) (∏ j ∈ range n, D j) (Y n) := by
  induction n with
  | zero =>
    convert! (hasDerivAt_id (Y 0)) using 1
  | succ n ih =>
    have hp := ih (fun j hj => hrec j (by omega)) (fun j hj => hder j (by omega))
    rw [← hrec n (by omega)] at hp
    simpa only [branchPrefix, prod_range_succ, Function.comp_def] using
      hp.comp (Y (n + 1)) (hder n (by omega))

/-- All branch data are checked only at the actual intermediate points. -/
theorem gauss_actual_prefix_distortion (a : ℕ → ℕ+) (h : ℕ → ℝ → ℝ)
    (D Y d e : ℕ → ℝ) (n : ℕ)
    (hrec : ∀ j < n, h j (Y (j + 1)) = Y j)
    (hder : ∀ j < n, HasDerivAt (h j) (D j) (Y (j + 1)))
    (hy : ∀ j ≤ n, 0 ≤ Y j) (hD : ∀ j < n, D j ≠ 0)
    (hvalue : ∀ j < n, |h j (Y (j + 1)) - gaussInv (a j) (Y (j + 1))| ≤ d j)
    (hlog : ∀ j < n,
      |Real.log (|D j| / |deriv (gaussInv (a j)) (Y (j + 1))|)| ≤ e j) :
    |Real.log (|deriv (branchPrefix h n) (Y n)| /
      |deriv (gaussWord (digitPrefix a n)) (Y n)|)| ≤
        ∑ j ∈ range n, (e j + if j = 0 then 0 else 2 * d j) := by
  rw [(hasDerivAt_branchPrefix h D Y n hrec hder).deriv]
  apply gauss_log_product_distortion a D Y d e n hy hD
  · intro j hj
    simpa only [hrec j hj] using hvalue j hj
  · exact hlog

theorem gauss_actual_prefix_deriv_bound (a : ℕ → ℕ+) (h : ℕ → ℝ → ℝ)
    (D Y d e : ℕ → ℝ) (n : ℕ)
    (hrec : ∀ j < n, h j (Y (j + 1)) = Y j)
    (hder : ∀ j < n, HasDerivAt (h j) (D j) (Y (j + 1)))
    (hy : ∀ j ≤ n, 0 ≤ Y j) (hD : ∀ j < n, D j ≠ 0)
    (hvalue : ∀ j < n, |h j (Y (j + 1)) - gaussInv (a j) (Y (j + 1))| ≤ d j)
    (hlog : ∀ j < n,
      |Real.log (|D j| / |deriv (gaussInv (a j)) (Y (j + 1))|)| ≤ e j) :
    |deriv (branchPrefix h n) (Y n)| ≤
      Real.exp (∑ j ∈ range n, (e j + if j = 0 then 0 else 2 * d j)) *
        |deriv (gaussWord (digitPrefix a n)) (Y n)| := by
  have hb := gauss_actual_prefix_distortion a h D Y d e n hrec hder hy hD hvalue hlog
  have hh : deriv (branchPrefix h n) (Y n) ≠ 0 := by
    rw [(hasDerivAt_branchPrefix h D Y n hrec hder).deriv]
    exact prod_ne_zero_iff.mpr (fun j hj => hD j (mem_range.mp hj))
  have hg := deriv_gaussWord_prefix_ne_zero a n (hy n le_rfl)
  have hratio : 0 < |deriv (branchPrefix h n) (Y n)| /
      |deriv (gaussWord (digitPrefix a n)) (Y n)| :=
    div_pos (abs_pos.mpr hh) (abs_pos.mpr hg)
  have he := Real.exp_le_exp.mpr ((le_abs_self _).trans hb)
  rw [Real.exp_log hratio] at he
  exact (div_le_iff₀ (abs_pos.mpr hg)).mp he

end

end BianchiIX
