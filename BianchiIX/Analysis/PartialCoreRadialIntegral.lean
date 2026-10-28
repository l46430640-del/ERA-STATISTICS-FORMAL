import BianchiIX.Analysis.CoreRadialIntegral

noncomputable section

namespace BianchiIX

open Set MeasureTheory

/-- Rescaling the active wall reuses the full-core integral bounds without fixing the entry angle. -/
theorem partial_core_four_integral_bounds {r u v w : ℝ → ℝ} {a b k u₀ p₀ : ℝ}
    (hab : a ≤ b) (hk : 6 ≤ k) (hu₀ : 0 ≤ u₀) (hp₀ : 0 ≤ p₀)
    (hrc : ContinuousOn r (Icc a b)) (huc : ContinuousOn u (Icc a b))
    (hvc : ContinuousOn v (Icc a b)) (hwc : ContinuousOn w (Icc a b))
    (hr : ∀ z ∈ Icc a b, 9 / 10 * k ≤ r z)
    (hu : ∀ z ∈ Icc a b, 0 ≤ u z ∧ u z ≤ u₀ * Real.exp (-k * (z - a) / 4))
    (hv : ∀ z ∈ Icc a b, 0 ≤ v z ∧ v z ≤ 11 / 10 * k)
    (hw : ∀ z ∈ Icc a b, 0 ≤ w z ∧ w z ≤ p₀ ∧ w z ≤ p₀ * Real.cosh z / r z)
    (ha : Real.cosh a ≤ 11 / 10 * k) (hb : Real.cosh b ≤ 11 / 10 * k) :
    (∫ z in a..b, u z * v z) ≤ 14 * u₀ ∧
    (∫ z in a..b, u z * w z) ≤ 4 * u₀ * p₀ / k ∧
    (∫ z in a..b, u z ^ 2 / r z) ≤ 3 * u₀ ^ 2 / k ^ 2 ∧
    (∫ z in a..b, w z ^ 2 / r z) ≤ 4 * p₀ ^ 2 / k := by
  have hk0 : 0 < k := by linarith only [hk]
  have hvscaled (z : ℝ) (hz : z ∈ Icc a b) :
      0 ≤ v z / k ∧ v z / k ≤ 11 / 10 * Real.exp (z - a) := by
    refine ⟨div_nonneg (hv z hz).1 hk0.le, ?_⟩
    have H : v z / k ≤ 11 / 10 := (div_le_iff₀ hk0).mpr (hv z hz).2
    have He : 1 ≤ Real.exp (z - a) := Real.one_le_exp_iff.mpr (sub_nonneg.mpr hz.1)
    linarith only [H, He]
  obtain ⟨hUV, hUW, hU2, hW2⟩ := core_four_integral_bounds hab hk hu₀ hp₀
    hrc huc (hvc.div_const k) hwc hr hu hvscaled hw ha hb
  refine ⟨?_, hUW, hU2, hW2⟩
  have Heq : (fun z => u z * (v z / k)) = fun z => (u z * v z) / k := by
    funext z
    ring
  rw [Heq, intervalIntegral.integral_div] at hUV
  exact (div_le_div_iff_of_pos_right hk0).mp hUV

end BianchiIX
