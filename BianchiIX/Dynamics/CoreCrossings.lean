import BianchiIX.Algebra.CoreCrossing
import BianchiIX.Analysis.OneSidedCrossing
import BianchiIX.Dynamics.CoreResidence

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- Any later return approached from above is on the outgoing branch and is transverse. -/
theorem scaled_core_return_downward {β : ℝ → ProjectiveState} {s t a k : ℝ}
    (hk : 6 ≤ k) (hst : s < t) (ha : 0 < a)
    (hβ : HasDerivAt β (a • projectiveField (β t)) t)
    (hv : β t 2 = 1) (habove : ∀ u ∈ Ioo s t, 1 ≤ β u 2)
    (hr : 99 / 100 * k ≤ coreRadius (β t 0) (β t 2))
    (hu : 0 ≤ β t 1 ∧ β t 1 ≤ (1 / 10000) / k)
    (hw : 0 ≤ β t 3 ∧ β t 3 ≤ (1 / 10000) / k) :
    β t 0 < 1 ∧ 0 < coreAngle (β t 0) (β t 2) ∧
      deriv (fun u => β u 2) t ≤ -a * k / 2 ∧
      ∀ᶠ u in 𝓝[>] t, β u 2 < 1 := by
  have hd : HasDerivAt (fun u => β u 2) (a * activeVelocity (β t 0) (β t 1) 1 (β t 3)) t := by
    have H := hasDerivAt_pi.mp hβ 2
    change HasDerivAt (fun u => β u 2) (a * activeVelocity (β t 0) (β t 1) (β t 2) (β t 3)) t at H
    rwa [hv] at H
  have hnonpos := deriv_nonpos_of_left_lower hst hd (fun u hh => by rw [hv]; exact habove u hh)
  rw [hv] at hr
  obtain h | h := core_section_velocity hk hr hu hw
  · have H : 0 < a * activeVelocity (β t 0) (β t 1) 1 (β t 3) :=
      mul_pos ha (lt_of_lt_of_le (by linarith : 0 < k / 2) h.2)
    linarith
  · have hvel := mul_le_mul_of_nonneg_left h.2 ha.le
    have hneg : a * activeVelocity (β t 0) (β t 1) 1 (β t 3) < 0 := by
      have H : a * (-k / 2) < 0 := mul_neg_of_pos_of_neg ha (by linarith)
      exact hvel.trans_lt H
    refine ⟨h.1, ?_, ?_, ?_⟩
    · rw [hv]
      exact (coreAngle_section_sign _).2.mpr h.1
    · rw [hd.deriv]
      nlinarith
    · simpa only [hv] using eventually_lt_right_of_deriv_neg hd hneg

theorem scaled_core_entry_upward {β : ℝ → ProjectiveState} {s a k : ℝ}
    (hk : 6 ≤ k) (ha : 0 < a)
    (hβ : HasDerivAt β (a • projectiveField (β s)) s)
    (hv : β s 2 = 1) (hm : 1 ≤ β s 0)
    (hr : 99 / 100 * k ≤ coreRadius (β s 0) (β s 2))
    (hu : 0 ≤ β s 1 ∧ β s 1 ≤ (1 / 10000) / k)
    (hw : 0 ≤ β s 3 ∧ β s 3 ≤ (1 / 10000) / k) :
    coreAngle (β s 0) (β s 2) < 0 ∧
      a * k / 2 ≤ deriv (fun u => β u 2) s ∧ ∀ᶠ u in 𝓝[>] s, 1 < β u 2 := by
  have hd := hasDerivAt_pi.mp hβ 2
  change HasDerivAt (fun u => β u 2) (a * activeVelocity (β s 0) (β s 1) (β s 2) (β s 3)) s at hd
  rw [hv] at hd hr
  obtain h | h := core_section_velocity hk hr hu hw
  · have hvel := mul_le_mul_of_nonneg_left h.2 ha.le
    have hpos : 0 < a * activeVelocity (β s 0) (β s 1) 1 (β s 3) :=
      mul_pos ha (lt_of_lt_of_le (by linarith : 0 < k / 2) h.2)
    refine ⟨?_, ?_, ?_⟩
    · rw [hv]
      exact (coreAngle_section_sign _).1.mpr h.1
    · rw [hd.deriv]
      nlinarith
    · simpa only [hv] using eventually_gt_right_of_deriv_pos hd hpos
  · linarith [h.1]

theorem normalized_core_return_downward {x : NormalizedState} {t₀ s t k : ℝ}
    (hc : stateConstraint x = 1) (hk : 6 ≤ k) (hs : t₀ ≤ s) (hst : s < t)
    (hA : 0 < 1 + normalizedMaxCurve x t₀ t 0) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u)
    β t 2 = 1 → (∀ u ∈ Ioo s t, 1 ≤ β u 2) →
    99 / 100 * k ≤ coreRadius (β t 0) (β t 2) →
    (0 ≤ β t 1 ∧ β t 1 ≤ (1 / 10000) / k) →
    (0 ≤ β t 3 ∧ β t 3 ≤ (1 / 10000) / k) →
    β t 0 < 1 ∧ 0 < coreAngle (β t 0) (β t 2) ∧
      deriv (fun u => β u 2) t ≤ -(1 + normalizedMaxCurve x t₀ t 0) * k / 2 ∧
      ∀ᶠ u in 𝓝[>] t, β u 2 < 1 := by
  intro β hv habove hr hu hw
  have H := normalizedMaxCurve_forward_of_constraint hc (hs.trans hst.le)
  exact scaled_core_return_downward hk hst hA
    (hasDerivAt_toProjectiveState_normalized H.1 (ne_of_gt hA) H.2.1) hv habove hr hu hw

/-- An interior touch would immediately move below the section, contradicting the core bounds. -/
theorem scaled_core_interior_above {β : ℝ → ProjectiveState} {a : ℝ → ℝ} {k s t : ℝ}
    (hk : 6 ≤ k)
    (ha : ∀ u ∈ Icc s t, 0 < a u)
    (hβ : ∀ u ∈ Icc s t, HasDerivAt β (a u • projectiveField (β u)) u)
    (hr : ∀ u ∈ Icc s t, 99 / 100 * k ≤ coreRadius (β u 0) (β u 2))
    (hv : ∀ u ∈ Icc s t, 1 ≤ β u 2)
    (hu : ∀ u ∈ Icc s t, 0 ≤ β u 1 ∧ β u 1 ≤ (1 / 10000) / k)
    (hw : ∀ u ∈ Icc s t, 0 ≤ β u 3 ∧ β u 3 ≤ (1 / 10000) / k) :
    ∀ u ∈ Ioo s t, 1 < β u 2 := by
  intro u hst
  have hh : u ∈ Icc s t := ⟨hst.1.le, hst.2.le⟩
  apply lt_of_le_of_ne (hv u hh)
  intro heq
  have H := scaled_core_return_downward hk hst.1 (ha u hh) (hβ u hh) heq.symm
    (fun v hvs => hv v ⟨hvs.1.le, (hvs.2.trans hst.2).le⟩) (hr u hh) (hu u hh) (hw u hh)
  obtain ⟨v, hbelow, hvt⟩ := (H.2.2.2.and (Ioo_mem_nhdsGT hst.2)).exists
  have H' := hv v ⟨(hst.1.trans hvt.1).le, hvt.2.le⟩
  linarith

theorem scaled_core_return_isLeast {β : ℝ → ProjectiveState} {a : ℝ → ℝ} {k s t : ℝ}
    (hk : 6 ≤ k) (hst : s < t)
    (ha : ∀ u ∈ Icc s t, 0 < a u)
    (hβ : ∀ u ∈ Icc s t, HasDerivAt β (a u • projectiveField (β u)) u)
    (hr : ∀ u ∈ Icc s t, 99 / 100 * k ≤ coreRadius (β u 0) (β u 2))
    (hv : ∀ u ∈ Icc s t, 1 ≤ β u 2)
    (hu : ∀ u ∈ Icc s t, 0 ≤ β u 1 ∧ β u 1 ≤ (1 / 10000) / k)
    (hw : ∀ u ∈ Icc s t, 0 ≤ β u 3 ∧ β u 3 ≤ (1 / 10000) / k)
    (hvt : β t 2 = 1) : IsLeast {u | s < u ∧ β u 2 = 1} t := by
  refine ⟨⟨hst, hvt⟩, ?_⟩
  intro u hu'
  by_contra! hut
  have H := scaled_core_interior_above hk ha hβ hr hv hu hw u ⟨hu'.1, hut⟩
  rw [hu'.2] at H
  exact (lt_irrefl (1 : ℝ)) H

theorem normalized_core_return_isLeast {x : NormalizedState} {t₀ s t k : ℝ}
    (hc : stateConstraint x = 1) (hk : 6 ≤ k) (hs : t₀ ≤ s) (hst : s < t)
    (hA : ∀ u ∈ Icc s t, 0 < 1 + normalizedMaxCurve x t₀ u 0) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u)
    (∀ u ∈ Icc s t, 99 / 100 * k ≤ coreRadius (β u 0) (β u 2)) →
    (∀ u ∈ Icc s t, 1 ≤ β u 2) →
    (∀ u ∈ Icc s t, 0 ≤ β u 1 ∧ β u 1 ≤ (1 / 10000) / k) →
    (∀ u ∈ Icc s t, 0 ≤ β u 3 ∧ β u 3 ≤ (1 / 10000) / k) →
    β t 2 = 1 → IsLeast {u | s < u ∧ β u 2 = 1} t := by
  intro β hr hv hu hw hvt
  apply scaled_core_return_isLeast hk hst hA ?_ hr hv hu hw hvt
  intro u hh
  have H := normalizedMaxCurve_forward_of_constraint hc (hs.trans hh.1)
  exact hasDerivAt_toProjectiveState_normalized H.1 (ne_of_gt (hA u hh)) H.2.1

end BianchiIX
