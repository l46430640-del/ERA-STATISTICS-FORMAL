import BianchiIX.Statistics.TreeMeasure

/-! Local inverse-branch errors imply distortion and measure bounds for the whole tree. -/

open Set MeasureTheory
open scoped NNReal ENNReal

namespace BianchiIX

theorem gaussWord_positive_regular (w : List ℕ+) {x : ℝ} (hx : 0 ≤ x) :
    DifferentiableAt ℝ (gaussWord (w.map (fun a : ℕ+ => (a : ℕ)))) x ∧
      deriv (gaussWord (w.map (fun a : ℕ+ => (a : ℕ)))) x ≠ 0 := by
  have hd := hasDerivAt_gaussWord_prefix (extendPositiveWord w) w.length hx
  have hn := deriv_gaussWord_prefix_ne_zero (extendPositiveWord w) w.length hx
  simp only [digitPrefix_extendPositiveWord] at hd hn
  exact ⟨hd.differentiableAt, hn⟩

theorem log_deriv_gaussWord_lipschitz (w : List ℕ+) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.log (|deriv (gaussWord (w.map (fun a : ℕ+ => (a : ℕ)))) x|) -
      Real.log (|deriv (gaussWord (w.map (fun a : ℕ+ => (a : ℕ)))) y|)| ≤ 2 * |x - y| := by
  rw [← digitPrefix_extendPositiveWord w,
    log_abs_deriv_gaussWord_prefix _ _ hx, log_abs_deriv_gaussWord_prefix _ _ hy]
  exact gaussPrefixLog_lipschitz _ _ hx hy

theorem log_deriv_gaussWord_append (w : List ℕ+) (a : ℕ+) {x : ℝ} (hx : 0 ≤ x) :
    Real.log |deriv (gaussWord ((w ++ [a]).map (fun b : ℕ+ => (b : ℕ)))) x| =
      Real.log |deriv (gaussWord (w.map (fun b : ℕ+ => (b : ℕ)))) (gaussInv a x)| +
        Real.log |deriv (gaussInv a) x| := by
  have ha : (1 : ℝ) ≤ a := by exact_mod_cast a.pos
  have hg := hasDerivAt_gaussInv ha hx
  have hp := gaussWord_positive_regular w (gaussInv_pos ha hx).le
  have hf : gaussWord ((w ++ [a]).map (fun b : ℕ+ => (b : ℕ))) =
      gaussWord (w.map (fun b : ℕ+ => (b : ℕ))) ∘ gaussInv a := by
    funext t
    simp only [List.map_append, List.map_singleton, gaussWord_append, gaussWord,
      Function.comp_apply]
  have hgn : deriv (gaussInv a) x ≠ 0 := by
    rw [hg.deriv]
    exact div_ne_zero (by norm_num) (pow_ne_zero _ (ne_of_gt (by linarith)))
  rw [hf, deriv_comp x hp.1 hg.differentiableAt, abs_mul,
    Real.log_mul (abs_ne_zero.mpr hp.2) (abs_ne_zero.mpr hgn)]

namespace InverseBranchTree

/-- These are local analytic inputs on the branch domains, not conclusions about prefixes. -/
structure BranchEstimates (T : InverseBranchTree) (d e : ℕ → ℝ) : Prop where
  root_subset : T.root ⊆ Ioo (0 : ℝ) 1
  domain_subset : ∀ w a, T.domain w a ⊆ Ioo (0 : ℝ) 1
  differentiable : ∀ w a, ∀ x ∈ T.domain w a, DifferentiableAt ℝ (T.branch w a) x
  nonzero : ∀ w a, ∀ x ∈ T.domain w a, deriv (T.branch w a) x ≠ 0
  value_error : ∀ w a, ∀ x ∈ T.domain w a,
    |T.branch w a x - gaussInv a x| ≤ d w.length
  log_error : ∀ w a, ∀ x ∈ T.domain w a,
    |Real.log (|deriv (T.branch w a) x| / |deriv (gaussInv a) x|)| ≤ e w.length

namespace BranchEstimates

variable {T : InverseBranchTree} {d e : ℕ → ℝ} (E : T.BranchEstimates d e)

include E

theorem terminal_subset (w : List ℕ+) : T.terminal w ⊆ Ioo (0 : ℝ) 1 :=
  T.terminal_subset E.root_subset E.domain_subset w

theorem toRoot_regular (w : List ℕ+) {x : ℝ} (hx : x ∈ T.terminal w) :
    DifferentiableAt ℝ (T.toRoot w) x ∧ deriv (T.toRoot w) x ≠ 0 := by
  induction w using List.reverseRecOn generalizing x with
  | nil => simp
  | append_singleton w a ih =>
    rw [T.terminal_append] at hx
    have hp := ih hx.2
    have ha := E.differentiable w a x hx.1
    rw [T.toRoot_append]
    refine ⟨hp.1.comp x ha, ?_⟩
    rw [deriv_comp x hp.1 ha]
    exact mul_ne_zero hp.2 (E.nonzero w a x hx.1)

theorem log_distortion (w : List ℕ+) {x : ℝ} (hx : x ∈ T.terminal w) :
    |Real.log (|deriv (T.toRoot w) x| /
      |deriv (gaussWord (w.map (fun a : ℕ+ => (a : ℕ)))) x|)| ≤
      ∑ j ∈ Finset.range w.length, (e j + if j = 0 then 0 else 2 * d j) := by
  induction w using List.reverseRecOn generalizing x with
  | nil => simp [gaussWord]
  | append_singleton w a ih =>
    have hterminal := hx
    rw [T.terminal_append] at hx
    have hx0 := (E.domain_subset w a hx.1).1.le
    have hy0 := (E.terminal_subset w hx.2).1.le
    have ha : (1 : ℝ) ≤ a := by exact_mod_cast a.pos
    have hg0 := (gaussInv_pos ha hx0).le
    have hp := E.toRoot_regular w hx.2
    have hg := gaussWord_positive_regular w hy0
    have hprev := ih hx.2
    rw [Real.log_div (abs_ne_zero.mpr hp.2) (abs_ne_zero.mpr hg.2)] at hprev
    have hgn : deriv (gaussInv a) x ≠ 0 := by
      rw [(hasDerivAt_gaussInv ha hx0).deriv]
      exact div_ne_zero (by norm_num) (pow_ne_zero _ (ne_of_gt (by linarith)))
    have hstep := E.log_error w a x hx.1
    rw [Real.log_div (abs_ne_zero.mpr (E.nonzero w a x hx.1)) (abs_ne_zero.mpr hgn)] at hstep
    have hphase :
        |Real.log (|deriv (gaussWord (w.map (fun b : ℕ+ => (b : ℕ)))) (T.branch w a x)|) -
          Real.log (|deriv (gaussWord (w.map (fun b : ℕ+ => (b : ℕ)))) (gaussInv a x)|)| ≤
          if w.length = 0 then 0 else 2 * d w.length := by
      by_cases hw : w.length = 0
      · have hz := List.length_eq_zero_iff.mp hw
        simp [hz, gaussWord]
      · rw [if_neg hw]
        exact (log_deriv_gaussWord_lipschitz w hy0 hg0).trans
          (mul_le_mul_of_nonneg_left (E.value_error w a x hx.1) (by norm_num))
    rw [Real.log_div (abs_ne_zero.mpr (E.toRoot_regular (w ++ [a]) hterminal).2)
      (abs_ne_zero.mpr (gaussWord_positive_regular (w ++ [a]) hx0).2),
      T.toRoot_append, deriv_comp x hp.1 (E.differentiable w a x hx.1), abs_mul,
      Real.log_mul (abs_ne_zero.mpr hp.2) (abs_ne_zero.mpr (E.nonzero w a x hx.1)),
      log_deriv_gaussWord_append w a hx0]
    simp only [List.length_append, List.length_singleton, Finset.sum_range_succ]
    let r := Real.log |deriv (T.toRoot w) (T.branch w a x)| -
      Real.log |deriv (gaussWord (w.map (fun b : ℕ+ => (b : ℕ)))) (T.branch w a x)|
    let p := Real.log |deriv (gaussWord (w.map (fun b : ℕ+ => (b : ℕ)))) (T.branch w a x)| -
      Real.log |deriv (gaussWord (w.map (fun b : ℕ+ => (b : ℕ)))) (gaussInv a x)|
    let s := Real.log |deriv (T.branch w a) x| - Real.log |deriv (gaussInv a) x|
    have hsum : Real.log |deriv (T.toRoot w) (T.branch w a x)| +
        Real.log |deriv (T.branch w a) x| -
        (Real.log |deriv (gaussWord (w.map (fun b : ℕ+ => (b : ℕ)))) (gaussInv a x)| +
        Real.log |deriv (gaussInv a) x|) = r + p + s := by
      dsimp [r, p, s]
      ring
    rw [hsum]
    have htri : |r + p + s| ≤ |r| + |p| + |s| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le r p) le_rfl)
    dsimp [r, p, s] at htri
    linarith

theorem deriv_bound (w : List ℕ+) {x : ℝ} (hx : x ∈ T.terminal w) :
    |deriv (T.toRoot w) x| ≤
      Real.exp (∑ j ∈ Finset.range w.length, (e j + if j = 0 then 0 else 2 * d j)) *
        |deriv (gaussWord (w.map (fun a : ℕ+ => (a : ℕ)))) x| := by
  have hb := E.log_distortion w hx
  have hp := E.toRoot_regular w hx
  have hg := gaussWord_positive_regular w (E.terminal_subset w hx).1.le
  have hratio : 0 < |deriv (T.toRoot w) x| /
      |deriv (gaussWord (w.map (fun a : ℕ+ => (a : ℕ)))) x| :=
    div_pos (abs_pos.mpr hp.2) (abs_pos.mpr hg.2)
  have he := Real.exp_le_exp.mpr ((le_abs_self _).trans hb)
  rw [Real.exp_log hratio] at he
  exact (div_le_iff₀ (abs_pos.mpr hg.2)).mp he

theorem uniform_deriv_bound {L : ℝ}
    (hbudget : ∀ n, (∑ j ∈ Finset.range n, (e j + if j = 0 then 0 else 2 * d j)) ≤ L)
    (w : List ℕ+) {x : ℝ} (hx : x ∈ T.terminal w) :
    |deriv (T.toRoot w) x| ≤ Real.exp L *
      |deriv (gaussWord (w.map (fun a : ℕ+ => (a : ℕ)))) x| :=
  (E.deriv_bound w hx).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hbudget w.length)) (abs_nonneg _))

theorem code_map_le {L : ℝ}
    (hbudget : ∀ n, (∑ j ∈ Finset.range n, (e j + if j = 0 then 0 else 2 * d j)) ≤ L) :
    Measure.map T.code (volume.comap (Subtype.val : T.survivors → ℝ)) ≤
      Real.toNNReal (Real.exp L) • volume :=
  T.code_volume_map_le L E.terminal_subset (fun w _ hx => (E.toRoot_regular w hx).1)
    (fun w _ hx => E.uniform_deriv_bound hbudget w hx)

theorem root_loss_le (ell : ℕ → ℝ≥0∞) {L : ℝ}
    (hbudget : ∀ n, (∑ j ∈ Finset.range n, (e j + if j = 0 then 0 else 2 * d j)) ≤ L)
    (hsize : ∀ w, volume (T.stoppedDomain w) ≤ ell w.length) :
    volume (T.root \ T.survivors) ≤ 2 * ENNReal.ofReal (Real.exp L) * ∑' m, ell m :=
  T.root_loss_le ell L E.terminal_subset (fun w _ hx => (E.toRoot_regular w hx).1) hsize
    (fun w _ hx => E.uniform_deriv_bound hbudget w hx)

theorem restricted_root_loss_le (I : Set ℝ) (ell : ℕ → ℝ≥0∞) {L : ℝ}
    (hbudget : ∀ n, (∑ j ∈ Finset.range n, (e j + if j = 0 then 0 else 2 * d j)) ≤ L)
    (hsize : ∀ w, volume (T.stoppedDomain w) ≤ ell w.length) :
    volume ((I ∩ T.root) \ (I ∩ T.survivors)) ≤
      min (volume I) (2 * ENNReal.ofReal (Real.exp L) * ∑' m, ell m) :=
  T.restricted_root_loss_le I ell L E.terminal_subset
    (fun w _ hx => (E.toRoot_regular w hx).1) hsize
    (fun w _ hx => E.uniform_deriv_bound hbudget w hx)

theorem measure_bounds_of_summable (ell : ℕ → ℝ≥0∞)
    (hd0 : ∀ n, 0 ≤ d n) (he0 : ∀ n, 0 ≤ e n) (hd : Summable d) (he : Summable e)
    (hsize : ∀ w, volume (T.stoppedDomain w) ≤ ell w.length) :
    let L := (∑' n, e n) + 2 * ∑' n, d (n + 1)
    Measure.map T.code (volume.comap (Subtype.val : T.survivors → ℝ)) ≤
        Real.toNNReal (Real.exp L) • volume ∧
      ∀ I : Set ℝ, volume ((I ∩ T.root) \ (I ∩ T.survivors)) ≤
        min (volume I) (2 * ENNReal.ofReal (Real.exp L) * ∑' n, ell n) := by
  have hb := finite_distortion_budget_le d e hd0 he0 hd he
  exact ⟨E.code_map_le hb, fun I => E.restricted_root_loss_le I ell hb hsize⟩

theorem ae_code_property {L : ℝ}
    (hbudget : ∀ n, (∑ j ∈ Finset.range n, (e j + if j = 0 then 0 else 2 * d j)) ≤ L)
    {P : ℝ → Prop} (hP : ∀ᵐ y ∂volume, P y) :
    ∀ᵐ x ∂(volume.comap (Subtype.val : T.survivors → ℝ)), P (T.code x) := by
  have hac : Measure.map T.code (volume.comap (Subtype.val : T.survivors → ℝ)) ≪ volume := by
    intro s hs
    have h := Measure.le_iff'.mp (E.code_map_le hbudget) s
    simpa only [Measure.smul_apply, hs, smul_zero, nonpos_iff_eq_zero] using h
  exact ae_of_ae_map T.code_measurable.aemeasurable (hac.ae_le hP)

end BranchEstimates
end InverseBranchTree
end BianchiIX
