import BianchiIX.Dynamics.ReferenceEntranceWeakIntegral
import BianchiIX.Analysis.CoreIntegrals

noncomputable section

namespace BianchiIX

open Set MeasureTheory Asymptotics
open scoped Topology

theorem referenceEntranceWeakResponse_eq {k v : ℝ} (hk : 0 < k) :
    referenceEntranceWeakResponse k v = -(v ^ 2 / k) *
      ((∫ t in 0..referenceEntranceDuration k v,
        Real.exp (-4 * t) / (k * Real.tanh (Real.arcosh (k / v) - k * t) + 2) ^ 2) +
        Real.sqrt (k ^ 2 - 1) / (2 * (Real.sqrt (k ^ 2 - 1) + 2)) *
          Real.exp (-4 * referenceEntranceDuration k v)) := by
  unfold referenceEntranceWeakResponse
  simp_rw [referenceEntrancePhase_eq hk]

theorem referenceEntranceWeakResponse_bounds {k v : ℝ} (hk : 7 / 4 ≤ k) (hv : 0 < v ∧ v < 1) :
    -(v ^ 2 / (2 * k)) ≤ referenceEntranceWeakResponse k v ∧ referenceEntranceWeakResponse k v < 0 := by
  have hk0 : 0 < k := by linarith
  let T := referenceEntranceDuration k v
  let s := Real.sqrt (k ^ 2 - 1)
  let E := Real.exp (-4 * T)
  let f := fun t => Real.exp (-4 * t) / (referenceEntrancePhase k v t + 2) ^ 2
  have hT : 0 ≤ T := (referenceEntranceDuration_pos (by linarith) hv).le
  have hden (t : ℝ) (ht : t ∈ Icc 0 T) : 1 ≤ (referenceEntrancePhase k v t + 2) ^ 2 := by
    have H := referenceEntrancePhase_lower hk ht.2
    nlinarith [H.1, H.2]
  have hfc : ContinuousOn f (Icc 0 T) :=
    (by fun_prop : Continuous (fun t : ℝ => Real.exp (-4 * t))).continuousOn.div
      (((continuous_referenceEntrancePhase k v).add_const 2).pow 2).continuousOn
      (fun t ht => ne_of_gt (lt_of_lt_of_le zero_lt_one (hden t ht)))
  have hg : Continuous (fun t : ℝ => Real.exp (-4 * t)) := by fun_prop
  have HI := intervalIntegral.integral_mono_on (μ := volume) hT
    (hfc.intervalIntegrable_of_Icc hT) (hg.intervalIntegrable 0 T) (by
      intro t ht
      exact (div_le_iff₀ (lt_of_lt_of_le zero_lt_one (hden t ht))).mpr
        (le_mul_of_one_le_right (Real.exp_pos _).le (hden t ht)))
  have HEint : (∫ t in 0..T, Real.exp (-4 * t)) = (1 - E) / 4 := by
    simpa only [sub_zero] using (integral_exp_decay (a := 0) (b := T) (c := 4) (by norm_num))
  rw [HEint] at HI
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hterm : s / (2 * (s + 2)) ≤ 1 / 2 := by
    apply (div_le_iff₀ (show 0 < 2 * (s + 2) by positivity)).mpr
    linarith
  have hE : E ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hT])
  have hbracket : (∫ t in 0..T, f t) + s / (2 * (s + 2)) * E ≤ 1 / 2 := by
    have HH := mul_le_mul_of_nonneg_right hterm (Real.exp_pos (-4 * T)).le
    linarith only [HI, HH, hE]
  constructor
  · have HH := mul_le_mul_of_nonneg_left hbracket (div_nonneg (sq_nonneg v) hk0.le)
    change -(v ^ 2 / (2 * k)) ≤ -(v ^ 2 / k) * ((∫ t in 0..T, f t) + s / (2 * (s + 2)) * E)
    have he : v ^ 2 / (2 * k) = (v ^ 2 / k) * (1 / 2) := by ring
    rw [he]
    nlinarith only [HH]
  · have HQ := (referenceEntrance_weak_regular hk hv).2.2
    rw [referenceEntrance_weak_loss_eq hk hv] at HQ
    linarith

/-- The explicit coefficient in (C.49) belongs to the actual return in any valid radial chart. -/
theorem EntranceRadialInverseAt.referenceEntrance_weak_response {k v : ℝ}
    (hk : 7 / 4 ≤ k) (hv : 0 < v ∧ v < 1)
    {Ψ : ProjectiveState → ProjectiveState} (HΨ : EntranceRadialInverseAt (referenceEntranceState k v) Ψ) :
    (fun w : ℝ =>
      coreRadius (entranceReturnState (Ψ ![k, 0, v, w]) 0) (entranceReturnState (Ψ ![k, 0, v, w]) 2) - k -
        referenceEntranceWeakResponse k v * w ^ 2) =o[𝓝 0] (fun w => w ^ 2) := by
  have H := HΨ.referenceEntrance_weak_expansion hk hv
  rw [referenceEntrance_weak_loss_eq hk hv] at H
  simpa only [neg_mul, sub_eq_add_neg] using H

theorem exists_referenceEntrance_weak_response {k v : ℝ} (hk : 7 / 4 ≤ k) (hv : 0 < v ∧ v < 1) :
    ∃ Ψ : ProjectiveState → ProjectiveState,
      EntranceRadialInverseAt (referenceEntranceState k v) Ψ ∧
      (-(v ^ 2 / (2 * k)) ≤ referenceEntranceWeakResponse k v ∧ referenceEntranceWeakResponse k v < 0) ∧
      (fun w : ℝ =>
        coreRadius (entranceReturnState (Ψ ![k, 0, v, w]) 0) (entranceReturnState (Ψ ![k, 0, v, w]) 2) - k -
          referenceEntranceWeakResponse k v * w ^ 2) =o[𝓝 0] (fun w => w ^ 2) := by
  obtain ⟨Ψ, HΨ⟩ := exists_entranceRegion_radial_inverse hk (referenceEntrance_region hk hv) hv.1
  exact ⟨Ψ, HΨ, referenceEntranceWeakResponse_bounds hk hv, HΨ.referenceEntrance_weak_response hk hv⟩

end BianchiIX
