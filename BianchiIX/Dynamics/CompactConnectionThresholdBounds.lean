import BianchiIX.Dynamics.CompactConnectionThreshold
import BianchiIX.Analysis.CriticalPhaseAlgebra

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The unique actual threshold has the B.53 displacement and both B.54 derivatives. -/
theorem exists_compact_connection_critical_bounds :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 10000 ∧ ∀ η : ℝ, (0 < η ∧ η ≤ δ) →
      ∃ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ p : Fin 2 → ℝ,
      (0 < p 0 ∧ p 0 ≤ ε) → (0 < p 1 ∧ p 1 ≤ ε) →
      let k := compactConnectionCritical η p
      k ∈ Ioo (31 / 8) (33 / 8) ∧ compactConnectionPhase η ![k, p 0, p 1] = 2 ∧
        coreTailValid η ![k, p 0, p 1] ∧ entranceReturnValid (compactConnectionEntry η ![k, p 0, p 1]) ∧
        ContDiffAt ℝ 2 (compactConnectionCritical η) p ∧
        |k - 4 - p 0 / 2| ≤ C * (p 0 + p 1) ^ 2 ∧
        |fderiv ℝ (compactConnectionCritical η) p (Pi.single 0 1) - 1 / 2| +
          |fderiv ℝ (compactConnectionCritical η) p (Pi.single 1 1)| ≤ C * (p 0 + p 1) ∧
        ∀ a ∈ Icc (31 / 8 : ℝ) 6,
          (compactConnectionPhase η ![a, p 0, p 1] = 2 ↔ a = k) ∧
          (compactConnectionPhase η ![a, p 0, p 1] < 2 ↔ a < k) ∧
          (2 < compactConnectionPhase η ![a, p 0, p 1] ↔ k < a) := by
  obtain ⟨δ, hδ, hδsmall, HC⟩ := exists_compact_connection_threshold_control
  refine ⟨δ, hδ, hδsmall, ?_⟩
  intro η hη
  obtain ⟨ε₀, hε₀, hεhalf, A, hA, HC'⟩ := HC η hη
  have Hgeom (p : Fin 2 → ℝ) (hu : 0 < p 0 ∧ p 0 ≤ ε₀) (hw : 0 < p 1 ∧ p 1 ≤ ε₀) :=
    compactConnectionCritical_spec_of_control
      (fun k hk => (HC' ![k, p 0, p 1] hk hu hw).2.2.1)
      (fun k hk => (HC' ![k, p 0, p 1] hk hu hw).2.2.2.1)
      (fun k hk => (HC' ![k, p 0, p 1] hk hu hw).2.2.2.2.1)
  let ε := ε₀ / 2
  have hεle : ε ≤ ε₀ := by dsimp only [ε]; linarith only [hε₀]
  refine ⟨ε, half_pos hε₀, 5 * A + 2, by positivity, ?_⟩
  intro p hu hw
  let k := compactConnectionCritical η p
  obtain ⟨hk, hroot, hmono⟩ := Hgeom p ⟨hu.1, hu.2.trans hεle⟩ ⟨hw.1, hw.2.trans hεle⟩
  change compactConnectionPhase η ![k, p 0, p 1] = 2 at hroot
  have hkclosed : k ∈ Icc (31 / 8 : ℝ) 6 := ⟨hk.1.le, hk.2.le.trans (by norm_num)⟩
  obtain ⟨htail, hreturn, hphase, hr, _, hval, hrr, hst⟩ := HC' ![k, p 0, p 1] hkclosed
    ⟨hu.1, hu.2.trans hεle⟩ ⟨hw.1, hw.2.trans hεle⟩
  have hr0 : fderiv ℝ (compactConnectionPhase η) ![k, p 0, p 1] (Pi.single 0 1) ≠ 0 := by linarith only [hr]
  obtain ⟨τ, hτ, hcτ, hhit, hτd⟩ := exists_three_coordinate_level_branch hphase hr0
  have hp0 : p 0 < ε₀ := by dsimp only [ε] at hu; linarith only [hu.2, hε₀]
  have hp1 : p 1 < ε₀ := by dsimp only [ε] at hw; linarith only [hw.2, hε₀]
  have hnear0 : ∀ᶠ q : Fin 2 → ℝ in 𝓝 p, q 0 ∈ Ioo 0 ε₀ :=
    ((continuous_apply 0).continuousAt : ContinuousAt (fun q : Fin 2 → ℝ => q 0) p).eventually (Ioo_mem_nhds hu.1 hp0)
  have hnear1 : ∀ᶠ q : Fin 2 → ℝ in 𝓝 p, q 1 ∈ Ioo 0 ε₀ :=
    ((continuous_apply 1).continuousAt : ContinuousAt (fun q : Fin 2 → ℝ => q 1) p).eventually (Ioo_mem_nhds hw.1 hp1)
  have hτrange : ∀ᶠ q in 𝓝 p, τ q ∈ Ioo (31 / 8 : ℝ) (33 / 8) :=
    hcτ.continuousAt.eventually (by rw [hτ]; exact Ioo_mem_nhds hk.1 hk.2)
  have heq : compactConnectionCritical η =ᶠ[𝓝 p] τ := by
    filter_upwards [hnear0, hnear1, hτrange, hhit] with q hq0 hq1 hqr hqe
    obtain ⟨hqk, hqroot, hqm⟩ := Hgeom q ⟨hq0.1, hq0.2.le⟩ ⟨hq1.1, hq1.2.le⟩
    apply hqm.injOn ⟨hqk.1.le, hqk.2.le.trans (by norm_num)⟩ ⟨hqr.1.le, hqr.2.le.trans (by norm_num)⟩
    exact hqroot.trans (hqe.trans hroot).symm
  have hcritical := hcτ.congr_of_eventuallyEq heq
  have HD (i : Fin 2) : fderiv ℝ (compactConnectionCritical η) p (Pi.single i 1) =
      -fderiv ℝ (compactConnectionPhase η) ![k, p 0, p 1] (Pi.single i.succ 1) /
        fderiv ℝ (compactConnectionPhase η) ![k, p 0, p 1] (Pi.single 0 1) := by
    rw [heq.fderiv_eq]
    exact hτd i
  have hb : p 0 + p 1 ≤ 1 := by linarith only [hu.2.trans hεle, hw.2.trans hεle, hεhalf]
  have hk2 : 2 ≤ k := by linarith only [hk.1]
  have he : |4 - k + 2 * p 0 / k| ≤ A * (p 0 + p 1) ^ 2 := by
    change |compactConnectionPhase η ![k, p 0, p 1] - (k - 2) + 2 * p 0 / k| ≤ _ at hval
    rw [hroot, show (2 : ℝ) - (k - 2) = 4 - k by ring] at hval
    exact hval
  obtain ⟨hk4, hshift⟩ := critical_phase_root_bounds hA.le hk2 hu.1.le hw.1.le hb he
  have Hderiv := critical_phase_derivative_bounds hA.le hk2 (add_nonneg hu.1.le hw.1.le) hr hk4 hrr hst
  refine ⟨hk, hroot, htail, hreturn, hcritical, ?_, ?_, ?_⟩
  · exact hshift.trans (mul_le_mul_of_nonneg_right (by linarith only [hA]) (sq_nonneg _))
  · rw [HD 0, HD 1]
    exact Hderiv
  · intro a ha
    refine ⟨?_, ?_, ?_⟩
    · constructor
      · intro H
        exact hmono.injOn ha hkclosed (H.trans hroot.symm)
      · intro H
        rw [H]
        exact hroot
    · simpa only [hroot] using hmono.lt_iff_lt ha hkclosed
    · simpa only [hroot] using hmono.lt_iff_lt hkclosed ha

end BianchiIX
