import BianchiIX.Statistics.GaussDistortion

/-! Exact telescoping of ideal-prefix denominators along actual branch inputs. -/

namespace BianchiIX

noncomputable section

open Finset

theorem gauss_product_distortion_identity (a : ℕ → ℕ+) (D Y : ℕ → ℝ) (n : ℕ)
    (hy : ∀ j ≤ n, 0 ≤ Y j) :
    |∏ j ∈ range n, D j| / |deriv (gaussWord (digitPrefix a n)) (Y n)| =
      ∏ j ∈ range n, (|D j| / |deriv (gaussInv (a j)) (Y (j + 1))| *
        (gaussDenom a j (gaussInv (a j) (Y (j + 1))) / gaussDenom a j (Y j)) ^ 2) := by
  induction n with
  | zero => simp [digitPrefix, gaussWord]
  | succ n ih =>
    have hn := hy n (by omega)
    have hnext := hy (n + 1) le_rfl
    have ha : (1 : ℝ) ≤ a n := by exact_mod_cast (a n).pos
    have hp : 0 < (a n : ℝ) + Y (n + 1) := by linarith
    have hden := gaussDenom_pos a n hn
    have hden' := gaussDenom_pos a n (gaussInv_pos ha hnext).le
    have hprev := ih (fun j hj => hy j (by omega))
    rw [abs_deriv_gaussWord_prefix a n hn] at hprev
    rw [prod_range_succ, prod_range_succ, abs_mul,
      abs_deriv_gaussWord_prefix a (n + 1) hnext, gaussDenom_succ a n hnext,
      (hasDerivAt_gaussInv ha hnext).deriv, ← hprev]
    simp only [abs_div, abs_neg, abs_one, abs_pow, abs_of_pos hp]
    field_simp

theorem gauss_actual_prefix_product_identity (a : ℕ → ℕ+) (h : ℕ → ℝ → ℝ)
    (D Y : ℕ → ℝ) (n : ℕ)
    (hrec : ∀ j < n, h j (Y (j + 1)) = Y j)
    (hder : ∀ j < n, HasDerivAt (h j) (D j) (Y (j + 1)))
    (hy : ∀ j ≤ n, 0 ≤ Y j) :
    |deriv (branchPrefix h n) (Y n)| / |deriv (gaussWord (digitPrefix a n)) (Y n)| =
      ∏ j ∈ range n, (|D j| / |deriv (gaussInv (a j)) (Y (j + 1))| *
        (gaussDenom a j (gaussInv (a j) (Y (j + 1))) / gaussDenom a j (Y j)) ^ 2) := by
  rw [(hasDerivAt_branchPrefix h D Y n hrec hder).deriv]
  exact gauss_product_distortion_identity a D Y n hy

end
end BianchiIX
