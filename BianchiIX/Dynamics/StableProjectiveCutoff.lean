import BianchiIX.Analysis.MonotoneClockInverse
import BianchiIX.Dynamics.StableProjectiveClock

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def stableProjectiveCutoff (c : ℝ) : StableState × ℝ → ℝ :=
  intervalScalarInverse (stableProjectiveClock c) (Ioi 0)

theorem stableProjectiveClock_surjective {c σ : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 ≤ σ) :
    ∃ t ∈ Ici 0, stableProjectiveClock c (y, t) = σ := by
  have hK : 0 < c + 1 := by linarith
  let T := (c + 1) * σ / 3
  have hT : 0 ≤ T := div_nonneg (mul_nonneg hK.le hσ) (by norm_num)
  have hlow := (stableProjectiveClock_bounds hc hy hT).1
  have he : 3 / (c + 1) * T = σ := by dsimp [T]; field_simp
  rw [he] at hlow
  have hcont : ContinuousOn (fun t => stableProjectiveClock c (y, t)) (Icc 0 T) :=
    HasDerivAt.continuousOn (fun t ht => hasDerivAt_stableProjectiveClock hc hy ht.1)
  obtain ⟨t, ht, heq⟩ := intermediate_value_Icc hT hcont
    (show σ ∈ Icc (stableProjectiveClock c (y, 0)) (stableProjectiveClock c (y, T)) by
      rw [stableProjectiveClock_zero]; exact ⟨hσ, hlow⟩)
  exact ⟨t, ht.1, heq⟩

theorem stableProjectiveCutoff_zero {c : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) :
    stableProjectiveCutoff c (y, 0) = 0 := by
  have hn : ¬ ∃ t ∈ Ioi (0 : ℝ), stableProjectiveClock c (y, t) = 0 := by
    rintro ⟨t, ht, he⟩
    have H := stableProjectiveClock_strictMonoOn hc hy (show 0 ∈ Ici (0 : ℝ) by simp)
      (mem_Ici.mpr (le_of_lt (mem_Ioi.mp ht))) (mem_Ioi.mp ht)
    dsimp only at H
    rw [stableProjectiveClock_zero, he] at H
    exact lt_irrefl _ H
  simp only [stableProjectiveCutoff, intervalScalarInverse, hn, ↓reduceDIte]

theorem stableProjectiveCutoff_spec_pos {c σ : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 < σ) :
    0 < stableProjectiveCutoff c (y, σ) ∧
      stableProjectiveClock c (y, stableProjectiveCutoff c (y, σ)) = σ := by
  obtain ⟨t, ht, he⟩ := stableProjectiveClock_surjective hc hy hσ.le
  have htpos : 0 < t := lt_of_le_of_ne ht (by
    intro h; subst t; rw [stableProjectiveClock_zero] at he; linarith)
  have hi := intervalScalarInverse_eq
    ((stableProjectiveClock_strictMonoOn hc hy).mono Ioi_subset_Ici_self) htpos he
  change stableProjectiveCutoff c (y, σ) = t at hi
  rw [hi]
  exact ⟨htpos, he⟩

theorem stableProjectiveCutoff_spec {c σ : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 ≤ σ) :
    0 ≤ stableProjectiveCutoff c (y, σ) ∧
      stableProjectiveClock c (y, stableProjectiveCutoff c (y, σ)) = σ := by
  rcases hσ.eq_or_lt with rfl | hσ
  · simp [stableProjectiveCutoff_zero hc hy, stableProjectiveClock_zero]
  · exact ⟨(stableProjectiveCutoff_spec_pos hc hy hσ).1.le,
      (stableProjectiveCutoff_spec_pos hc hy hσ).2⟩

theorem stableProjectiveCutoff_clock {c t : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (ht : 0 ≤ t) :
    stableProjectiveCutoff c (y, stableProjectiveClock c (y, t)) = t := by
  rcases ht.eq_or_lt with rfl | ht
  · rw [stableProjectiveClock_zero, stableProjectiveCutoff_zero hc hy]
  · exact intervalScalarInverse_eq
      ((stableProjectiveClock_strictMonoOn hc hy).mono Ioi_subset_Ici_self) ht rfl

theorem stableProjectiveCutoff_bounds {c σ : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 ≤ σ) :
    (c + 1) * σ / 18 ≤ stableProjectiveCutoff c (y, σ) ∧
      stableProjectiveCutoff c (y, σ) ≤ (c + 1) * σ / 3 := by
  have hK : 0 < c + 1 := by linarith
  obtain ⟨ht, he⟩ := stableProjectiveCutoff_spec hc hy hσ
  obtain ⟨hl, hu⟩ := stableProjectiveClock_bounds hc hy ht
  rw [he] at hl hu
  have hl' := mul_le_mul_of_nonneg_left hl hK.le
  have hu' := mul_le_mul_of_nonneg_left hu hK.le
  field_simp at hl' hu'
  constructor <;> nlinarith

theorem stableProjectiveCutoff_regular {c σ : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 < σ) :
    ContDiffAt ℝ 2 (stableProjectiveCutoff c) (y, σ) ∧
      (∀ᶠ p in 𝓝 (y, σ), 0 < stableProjectiveCutoff c p ∧
        stableProjectiveClock c (p.1, stableProjectiveCutoff c p) = p.2) := by
  obtain ⟨ht, he⟩ := stableProjectiveCutoff_spec_pos hc hy hσ
  have hm : ∀ᶠ z in 𝓝 y, StrictMonoOn (fun t => stableProjectiveClock c (z, t)) (Ioi 0) := by
    filter_upwards [(isOpen_stableParameterDomain c).mem_nhds hy] with z hz
    exact (stableProjectiveClock_strictMonoOn hc hz).mono Ioi_subset_Ici_self
  have H := intervalScalarInverse_regular isOpen_Ioi ht
    (contDiffAt_stableProjectiveClock_two hc hy ht.le)
    (hasDerivAt_stableProjectiveClock hc hy ht.le) (stableProjectiveRate_pos hc _).ne' hm
  rw [he] at H
  exact H

/-- At zero cutoff the initial-state function is locally constant, including on either wall. -/
theorem contDiffAt_stableProjectiveCutoff_initial_two {c σ : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 ≤ σ) :
    ContDiffAt ℝ 2 (fun z => stableProjectiveCutoff c (z, σ)) y := by
  rcases hσ.eq_or_lt with rfl | hσ
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [(isOpen_stableParameterDomain c).mem_nhds hy] with z hz
    exact stableProjectiveCutoff_zero hc hz
  · exact (stableProjectiveCutoff_regular hc hy hσ).1.comp y
      (contDiffAt_id.prodMk contDiffAt_const)

theorem hasDerivAt_stableProjectiveCutoff_clock {c σ : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 < σ) :
    HasDerivAt (fun s => stableProjectiveCutoff c (y, s))
      (1 / stableProjectiveRate c (y, stableProjectiveCutoff c (y, σ))) σ := by
  obtain ⟨ht, he⟩ := stableProjectiveCutoff_spec_pos hc hy hσ
  have hm : ∀ᶠ z in 𝓝 y, StrictMonoOn (fun t => stableProjectiveClock c (z, t)) (Ioi 0) := by
    filter_upwards [(isOpen_stableParameterDomain c).mem_nhds hy] with z hz
    exact (stableProjectiveClock_strictMonoOn hc hz).mono Ioi_subset_Ici_self
  have H := hasDerivAt_intervalScalarInverse_clock isOpen_Ioi ht
    (contDiffAt_stableProjectiveClock_two hc hy ht.le)
    (hasDerivAt_stableProjectiveClock hc hy ht.le) (stableProjectiveRate_pos hc _).ne' hm
  rwa [he] at H

end BianchiIX
