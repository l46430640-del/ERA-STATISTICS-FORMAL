import BianchiIX.Analysis.AmplitudeSequence
import BianchiIX.Analysis.SmallParameters
import BianchiIX.Statistics.EraStatistics
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology ENNReal

theorem exists_era_budget_threshold {η Cv Ci C : ℝ} (hη : 0 < η)
    (hCv : 0 ≤ Cv) (hCi : 0 ≤ Ci) (hC : 0 ≤ C) :
    ∃ Bmax : ℝ, 0 < Bmax ∧ Bmax < 1 ∧ ∀ B ∈ Ioc 0 Bmax,
      B ^ η < 1 / 160 ∧
        2 * Ci * Real.sqrt B + 4 * Cv * B ^ (4 / 3 : ℝ) ≤ Real.log 2 ∧
        (25 / 16 : ℝ) * C * B ^ (17 / 30 : ℝ) ≤ 1 := by
  let c : Fin 4 → ℝ := ![1, 2 * Ci, 4 * Cv, (25 / 16) * C]
  let p : Fin 4 → ℝ := ![η, 1 / 2, 4 / 3, 17 / 30]
  let ε : Fin 4 → ℝ := ![1 / 160, Real.log 2 / 2, Real.log 2 / 2, 1]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨Bmax, hpos, hupper, hbudget⟩ :=
    exists_common_rpow_budget (Finset.univ : Finset (Fin 4)) (C := c) (p := p) (ε := ε)
      (by intro i _; fin_cases i <;> dsimp [c] <;> positivity)
      (by intro i _; fin_cases i <;> dsimp [p] <;> positivity)
      (by intro i _; fin_cases i <;> dsimp [ε] <;> positivity)
      (by norm_num : (0 : ℝ) < 1)
  refine ⟨Bmax, hpos, hupper, fun B hB => ?_⟩
  have h₀ := hbudget B hB 0 (Finset.mem_univ _)
  have h₁ := hbudget B hB 1 (Finset.mem_univ _)
  have h₂ := hbudget B hB 2 (Finset.mem_univ _)
  have h₃ := hbudget B hB 3 (Finset.mem_univ _)
  change 1 * B ^ η < 1 / 160 at h₀
  change 2 * Ci * B ^ (1 / 2 : ℝ) < Real.log 2 / 2 at h₁
  change 4 * Cv * B ^ (4 / 3 : ℝ) < Real.log 2 / 2 at h₂
  change (25 / 16 : ℝ) * C * B ^ (17 / 30 : ℝ) < 1 at h₃
  rw [← Real.sqrt_eq_rpow] at h₁
  exact ⟨by simpa only [one_mul] using h₀, by linarith, h₃.le⟩

/-- The root value error drops out of the distortion budget, leaving a tail
of order `B^(4/3)` rather than `B`. -/
theorem era_distortion_budget {B η Cv Ci : ℝ} (hB : 0 < B) (hB1 : B ≤ 1)
    (hη : 0 ≤ η) (hηhalf : η ≤ 1 / 2) (hsmall : B ^ η < 1 / 160)
    (hCv : 0 ≤ Cv) (hCi : 0 ≤ Ci) :
    (Summable fun m => Cv * eraAmplitude B m) ∧
      (Summable fun m => Ci * Real.sqrt (eraAmplitude B m)) ∧
      ∀ n, (∑ j ∈ Finset.range n,
        (Ci * Real.sqrt (eraAmplitude B j) + if j = 0 then 0 else 2 * (Cv * eraAmplitude B j))) ≤
          2 * Ci * Real.sqrt B + 4 * Cv * B ^ (4 / 3 : ℝ) := by
  have hηone : η ≤ 1 := by linarith
  have hd : Summable (eraAmplitude B) := by
    simpa only [Nat.add_zero, Real.rpow_one] using
      (eraAmplitude_series_of_small_beta hB hB1 hη hηone hsmall 0).1
  have hds : (∑' m, eraAmplitude B (m + 1)) ≤ 2 * B ^ (4 / 3 : ℝ) := by
    simpa only [Real.rpow_one, eraAmplitude_succ hB.le, eraAmplitude_zero] using
      (eraAmplitude_series_of_small_beta hB hB1 hη hηone hsmall 1).2
  have he : (Summable fun m => Real.sqrt (eraAmplitude B m)) ∧
      (∑' m, Real.sqrt (eraAmplitude B m)) ≤ 2 * Real.sqrt B := by
    simpa only [Nat.add_zero, eraAmplitude_zero, Real.sqrt_eq_rpow] using
      eraAmplitude_series_of_small_beta hB hB1 hη hηhalf hsmall 0
  refine ⟨hd.mul_left Cv, he.1.mul_left Ci, fun n => ?_⟩
  have H := finite_distortion_budget_le (fun m => Cv * eraAmplitude B m)
    (fun m => Ci * Real.sqrt (eraAmplitude B m))
    (fun m => mul_nonneg hCv (eraAmplitude_pos hB m).le)
    (fun _ => mul_nonneg hCi (Real.sqrt_nonneg _)) (hd.mul_left Cv) (he.1.mul_left Ci) n
  rw [tsum_mul_left, tsum_mul_left] at H
  nlinarith [mul_le_mul_of_nonneg_left hds hCv, mul_le_mul_of_nonneg_left he.2 hCi]

theorem era_stopping_budget {B η : ℝ} (hB : 0 < B) (hB1 : B ≤ 1)
    (hη : 0 ≤ η) (hsmall : B ^ η < 1 / 160) :
    (∑' m, ENNReal.ofReal (10 * eraAmplitude B m ^ η)) ≤ ENNReal.ofReal (20 * B ^ η) := by
  have H : (Summable fun m => eraAmplitude B m ^ η) ∧
      (∑' m, eraAmplitude B m ^ η) ≤ 2 * B ^ η := by
    simpa only [Nat.add_zero, eraAmplitude_zero] using
      eraAmplitude_series_of_small_beta hB hB1 hη le_rfl hsmall 0
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun m => mul_nonneg (by norm_num) (Real.rpow_nonneg (eraAmplitude_pos hB m).le η))
    (H.1.mul_left 10)]
  apply ENNReal.ofReal_le_ofReal
  rw [tsum_mul_left]
  linarith [H.2]

namespace InverseBranchTree

def typicalSurvivors (T : InverseBranchTree) : Set ℝ :=
  (Subtype.val : T.survivors → ℝ) '' (T.code ⁻¹' gaussCylinderTypicalSet)

theorem typicalSurvivors_measurable (T : InverseBranchTree) : MeasurableSet T.typicalSurvivors :=
  (MeasurableEmbedding.subtype_coe T.survivors_measurable).measurableSet_image.mpr
    (gaussCylinderTypicalSet_measurable.preimage T.code_measurable)

theorem typicalSurvivors_subset (T : InverseBranchTree) : T.typicalSurvivors ⊆ T.survivors := by
  rintro _ ⟨x, _, rfl⟩
  exact x.property

theorem survivors_subset_root (T : InverseBranchTree) : T.survivors ⊆ T.root := by
  intro x hx
  have H := mem_iInter.mp hx 0
  simpa only [T.level_zero] using H

theorem mem_typicalSurvivors (T : InverseBranchTree) (x : T.survivors) :
    x.val ∈ T.typicalSurvivors ↔ T.code x ∈ gaussCylinderTypicalSet := by
  constructor
  · rintro ⟨y, hy, heq⟩
    have he : y = x := Subtype.ext heq
    simpa only [mem_preimage, he] using hy
  · exact fun hx => ⟨x, hx, rfl⟩

namespace BranchEstimates

theorem typicalSurvivors_ae_eq {T : InverseBranchTree} {d e : ℕ → ℝ}
    (E : T.BranchEstimates d e) (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) {L : ℝ}
    (hbudget : ∀ n, (∑ j ∈ Finset.range n, (e j + if j = 0 then 0 else 2 * d j)) ≤ L) :
    T.typicalSurvivors =ᵐ[volume] T.survivors := by
  have H : ∀ᵐ x ∂volume.restrict T.survivors, x ∈ T.typicalSurvivors := by
    apply (ae_restrict_iff_subtype T.survivors_measurable).mpr
    filter_upwards [E.ae_code_gaussCylinderTypical hBirkhoff hbudget] with x hx
    exact (T.mem_typicalSurvivors x).mpr hx
  have H' := (ae_restrict_iff' T.survivors_measurable).mp H
  filter_upwards [H'] with x hx
  exact propext ⟨fun h => T.typicalSurvivors_subset h, hx⟩

theorem eraStatistics_on_typicalSurvivors {T : InverseBranchTree} {d e : ℕ → ℝ}
    (E : T.BranchEstimates d e) (hd : Tendsto d atTop (𝓝 0))
    (x : T.survivors) (hx : x.val ∈ T.typicalSurvivors) : EraStatistics (T.digits x) (T.phase x) :=
  eraStatistics_of_typical_code (T.digits x) ((T.mem_typicalSurvivors x).mp hx) (E.phase_mem_unit x)
    (squeeze_zero (fun _ => abs_nonneg _) (E.phase_error_le x) hd)

theorem restricted_loss_of_amplitude_bounds {T : InverseBranchTree} {B η Cv Ci : ℝ}
    (E : T.BranchEstimates (fun m => Cv * eraAmplitude B m)
      (fun m => Ci * Real.sqrt (eraAmplitude B m)))
    (hB : 0 < B) (hB1 : B ≤ 1) (hη : 0 ≤ η) (hηhalf : η ≤ 1 / 2)
    (hsmall : B ^ η < 1 / 160) (hCv : 0 ≤ Cv) (hCi : 0 ≤ Ci)
    (hL : 2 * Ci * Real.sqrt B + 4 * Cv * B ^ (4 / 3 : ℝ) ≤ Real.log 2)
    (hsize : ∀ w, volume (T.stoppedDomain w) ≤ ENNReal.ofReal (10 * eraAmplitude B w.length ^ η))
    (I : Set ℝ) :
    volume ((I ∩ T.root) \ (I ∩ T.survivors)) ≤ min (volume I) (ENNReal.ofReal (80 * B ^ η)) := by
  have hb := (era_distortion_budget hB hB1 hη hηhalf hsmall hCv hCi).2.2
  have H := E.restricted_root_loss_le I (fun m => ENNReal.ofReal (10 * eraAmplitude B m ^ η))
    (fun n => (hb n).trans hL) hsize
  refine H.trans (min_le_min_left _ ?_)
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  calc
    2 * ENNReal.ofReal 2 * (∑' m, ENNReal.ofReal (10 * eraAmplitude B m ^ η)) ≤
        2 * ENNReal.ofReal 2 * ENNReal.ofReal (20 * B ^ η) :=
      mul_le_mul le_rfl (era_stopping_budget hB hB1 hη hsmall) (by positivity) (by positivity)
    _ = ENNReal.ofReal (80 * B ^ η) := by
      rw [show (80 : ℝ) * B ^ η = 4 * (20 * B ^ η) by ring,
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num

theorem ae_eraStatistics_of_amplitude_bounds {T : InverseBranchTree} {B η Cv Ci : ℝ}
    (E : T.BranchEstimates (fun m => Cv * eraAmplitude B m)
      (fun m => Ci * Real.sqrt (eraAmplitude B m)))
    (hBirkhoff : Literature.BirkhoffErgodicInput ℝ)
    (hB : 0 < B) (hB1 : B ≤ 1) (hη : 0 ≤ η) (hηhalf : η ≤ 1 / 2)
    (hsmall : B ^ η < 1 / 160) (hCv : 0 ≤ Cv) (hCi : 0 ≤ Ci) :
    ∀ᵐ x ∂(volume.comap (Subtype.val : T.survivors → ℝ)), EraStatistics (T.digits x) (T.phase x) := by
  have H := era_distortion_budget hB hB1 hη hηhalf hsmall hCv hCi
  exact E.ae_eraStatistics hBirkhoff H.2.2 H.1.tendsto_atTop_zero

/-- The canonical typical survivor set satisfies every statistical conclusion and the restricted loss bound. -/
theorem typicalSurvivors_era_bounds {T : InverseBranchTree} {B η Cv Ci : ℝ}
    (E : T.BranchEstimates (fun m => Cv * eraAmplitude B m)
      (fun m => Ci * Real.sqrt (eraAmplitude B m)))
    (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) (hroot : T.root = Ioo (0 : ℝ) 1)
    (hB : 0 < B) (hB1 : B ≤ 1) (hη : 0 ≤ η) (hηhalf : η ≤ 1 / 2)
    (hsmall : B ^ η < 1 / 160) (hCv : 0 ≤ Cv) (hCi : 0 ≤ Ci)
    (hL : 2 * Ci * Real.sqrt B + 4 * Cv * B ^ (4 / 3 : ℝ) ≤ Real.log 2)
    (hsize : ∀ w, volume (T.stoppedDomain w) ≤ ENNReal.ofReal (10 * eraAmplitude B w.length ^ η)) :
    (1 / 2 : ℝ≥0∞) < volume T.typicalSurvivors ∧
      (∀ I : Set ℝ, volume ((I ∩ T.root) \ (I ∩ T.typicalSurvivors)) ≤
        min (volume I) (ENNReal.ofReal (80 * B ^ η))) ∧
      ∀ x : T.survivors, x.val ∈ T.typicalSurvivors → EraStatistics (T.digits x) (T.phase x) := by
  have hb := era_distortion_budget hB hB1 hη hηhalf hsmall hCv hCi
  have heq := E.typicalSurvivors_ae_eq hBirkhoff hb.2.2
  have hloss (I : Set ℝ) : volume ((I ∩ T.root) \ (I ∩ T.typicalSurvivors)) ≤
      min (volume I) (ENNReal.ofReal (80 * B ^ η)) := by
    have hm : volume ((I ∩ T.root) \ (I ∩ T.typicalSurvivors)) =
        volume ((I ∩ T.root) \ (I ∩ T.survivors)) :=
      measure_congr (ae_eq_set_sdiff (ae_eq_refl (I ∩ T.root : Set ℝ))
        (ae_eq_set_inter (ae_eq_refl I) heq))
    exact hm.trans_le
      (E.restricted_loss_of_amplitude_bounds hB hB1 hη hηhalf hsmall hCv hCi hL hsize I)
  have hloss0 : volume (T.root \ T.typicalSurvivors) ≤ ENNReal.ofReal (80 * B ^ η) := by
    simpa only [univ_inter] using (hloss univ).trans (min_le_right _ _)
  have hhalf : ENNReal.ofReal (80 * B ^ η) < (1 / 2 : ℝ≥0∞) := by
    have H : 80 * B ^ η < (1 / 2 : ℝ) := by linarith
    convert! (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1 / 2)).mpr H using 1
    norm_num [ENNReal.ofReal_div_of_pos]
  have hmass : (1 / 2 : ℝ≥0∞) < volume T.typicalSurvivors := by
    have hsplit := measure_sdiff_add_inter (μ := volume) T.root T.typicalSurvivors_measurable
    rw [inter_eq_right.mpr (T.typicalSurvivors_subset.trans T.survivors_subset_root),
      hroot, Real.volume_Ioo] at hsplit
    norm_num at hsplit
    by_contra h
    have hle := le_of_not_gt h
    have hfinite : volume T.typicalSurvivors ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) hle
    have H := ENNReal.add_lt_add_of_lt_of_le hfinite (hloss0.trans_lt hhalf) hle
    rw [hroot, hsplit] at H
    have htwo : (1 / 2 : ℝ≥0∞) + 1 / 2 = 1 := by
      rw [← ENNReal.add_div, show (1 : ℝ≥0∞) + 1 = 2 by norm_num]
      exact ENNReal.div_self (by norm_num) (by norm_num)
    exact (not_lt_of_ge htwo.le) H
  exact ⟨hmass, hloss, E.eraStatistics_on_typicalSurvivors hb.1.tendsto_atTop_zero⟩

/-- One measurable set supports every statistical conclusion, with the same
loss bound after restriction to any initial set. -/
theorem exists_measurable_era_set {T : InverseBranchTree} {B η Cv Ci : ℝ}
    (E : T.BranchEstimates (fun m => Cv * eraAmplitude B m)
      (fun m => Ci * Real.sqrt (eraAmplitude B m)))
    (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) (hroot : T.root = Ioo (0 : ℝ) 1)
    (hB : 0 < B) (hB1 : B ≤ 1) (hη : 0 ≤ η) (hηhalf : η ≤ 1 / 2)
    (hsmall : B ^ η < 1 / 160) (hCv : 0 ≤ Cv) (hCi : 0 ≤ Ci)
    (hL : 2 * Ci * Real.sqrt B + 4 * Cv * B ^ (4 / 3 : ℝ) ≤ Real.log 2)
    (hsize : ∀ w, volume (T.stoppedDomain w) ≤ ENNReal.ofReal (10 * eraAmplitude B w.length ^ η)) :
    ∃ G : Set ℝ, MeasurableSet G ∧ G ⊆ T.survivors ∧ (1 / 2 : ℝ≥0∞) < volume G ∧
      (∀ I : Set ℝ, volume ((I ∩ T.root) \ (I ∩ G)) ≤ min (volume I) (ENNReal.ofReal (80 * B ^ η))) ∧
      ∀ x : T.survivors, x.val ∈ G → EraStatistics (T.digits x) (T.phase x) :=
  ⟨T.typicalSurvivors, T.typicalSurvivors_measurable, T.typicalSurvivors_subset,
    E.typicalSurvivors_era_bounds hBirkhoff hroot hB hB1 hη hηhalf hsmall hCv hCi hL hsize⟩

end BranchEstimates
end InverseBranchTree
end BianchiIX
