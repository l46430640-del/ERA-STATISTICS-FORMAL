import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Pointwise convergence of discrete probability masses implies convergence in total variation. -/

open Filter
open scoped Topology

namespace BianchiIX

private theorem abs_sub_eq_add_sub_min (a b : ℝ) : |a - b| = a + b - 2 * min a b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

theorem probability_mass_l1_identity {ι : Type*} {p q : ι → ℝ}
    (hp0 : ∀ i, 0 ≤ p i) (hq0 : ∀ i, 0 ≤ q i) (hp : HasSum p 1) (hq : HasSum q 1) :
    (∑' i, |p i - q i|) = 2 - 2 * ∑' i, min (p i) (q i) := by
  have hm : Summable (fun i => min (p i) (q i)) :=
    Summable.of_nonneg_of_le (fun i => le_min (hp0 i) (hq0 i)) (fun i => min_le_right _ _) hq.summable
  simp_rw [abs_sub_eq_add_sub_min]
  rw [(hp.summable.add hq.summable).tsum_sub (hm.mul_left 2),
    hp.summable.tsum_add hq.summable, tsum_mul_left, hp.tsum_eq, hq.tsum_eq]
  ring

theorem probability_mass_l1_tendsto {ι : Type*} {p : ℕ → ι → ℝ} {q : ι → ℝ}
    (hp0 : ∀ n i, 0 ≤ p n i) (hq0 : ∀ i, 0 ≤ q i)
    (hp : ∀ n, HasSum (p n) 1) (hq : HasSum q 1)
    (hpoint : ∀ i, Tendsto (fun n => p n i) atTop (𝓝 (q i))) :
    Tendsto (fun n => ∑' i, |p n i - q i|) atTop (𝓝 0) := by
  have hm : Tendsto (fun n => ∑' i, min (p n i) (q i)) atTop (𝓝 (∑' i, q i)) := by
    apply tendsto_tsum_of_dominated_convergence hq.summable
    · intro i
      simpa only [min_self] using (hpoint i).min
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => q i) atTop (𝓝 (q i)))
    · exact Eventually.of_forall (fun n i => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hp0 n i) (hq0 i))]
        exact min_le_right _ _)
  rw [hq.tsum_eq] at hm
  simp_rw [probability_mass_l1_identity (hp0 _) hq0 (hp _) hq]
  simpa using (tendsto_const_nhds.sub (hm.const_mul 2) :
    Tendsto (fun n => (2 : ℝ) - 2 * ∑' i, min (p n i) (q i)) atTop (𝓝 (2 - 2 * 1)))

theorem summable_probability_weighted {ι : Type*} {p f : ι → ℝ} {M : ℝ}
    (hp0 : ∀ i, 0 ≤ p i) (hp : HasSum p 1) (hf : ∀ i, |f i| ≤ M) :
    Summable (fun i => p i * f i) := by
  apply (hp.summable.mul_right M).of_norm_bounded
  intro i
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hp0 i)]
  exact mul_le_mul_of_nonneg_left (hf i) (hp0 i)

theorem probability_weighted_difference_le {ι : Type*} {p q f : ι → ℝ} {M : ℝ}
    (hp0 : ∀ i, 0 ≤ p i) (hq0 : ∀ i, 0 ≤ q i) (hp : HasSum p 1) (hq : HasSum q 1)
    (hf : ∀ i, |f i| ≤ M) :
    |(∑' i, p i * f i) - ∑' i, q i * f i| ≤ M * ∑' i, |p i - q i| := by
  have hpf := summable_probability_weighted hp0 hp hf
  have hqf := summable_probability_weighted hq0 hq hf
  have hdiff := (hp.summable.sub hq.summable).abs
  have hdom : Summable (fun i => M * |p i - q i|) := hdiff.mul_left M
  have habs : Summable (fun i => |p i * f i - q i * f i|) := (hpf.sub hqf).abs
  rw [← hpf.tsum_sub hqf]
  calc
    |∑' i, (p i * f i - q i * f i)| ≤ ∑' i, |p i * f i - q i * f i| := by
      simpa only [Real.norm_eq_abs] using
        (norm_tsum_le_tsum_norm (f := fun i => p i * f i - q i * f i)
          (by simpa only [Real.norm_eq_abs] using habs))
    _ ≤ ∑' i, M * |p i - q i| := by
      apply habs.tsum_le_tsum _ hdom
      intro i
      rw [← sub_mul, abs_mul, mul_comm M]
      exact mul_le_mul_of_nonneg_left (hf i) (abs_nonneg _)
    _ = _ := tsum_mul_left

theorem probability_weighted_tendsto {ι : Type*} {p : ℕ → ι → ℝ} {q f : ι → ℝ} {M : ℝ}
    (hp0 : ∀ n i, 0 ≤ p n i) (hq0 : ∀ i, 0 ≤ q i)
    (hp : ∀ n, HasSum (p n) 1) (hq : HasSum q 1)
    (hpoint : ∀ i, Tendsto (fun n => p n i) atTop (𝓝 (q i)))
    (hf : ∀ i, |f i| ≤ M) :
    Tendsto (fun n => ∑' i, p n i * f i) atTop (𝓝 (∑' i, q i * f i)) := by
  apply tendsto_sub_nhds_zero_iff.mp
  apply squeeze_zero_norm
  · intro n
    exact probability_weighted_difference_le (hp0 n) hq0 (hp n) hq hf
  · simpa only [mul_zero] using (probability_mass_l1_tendsto hp0 hq0 hp hq hpoint).const_mul M

end BianchiIX
