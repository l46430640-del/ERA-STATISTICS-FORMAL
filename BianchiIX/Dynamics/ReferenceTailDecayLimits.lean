import BianchiIX.Analysis.TerminalReferenceLimits
import BianchiIX.Dynamics.ReferenceTailResponse

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem referenceTail_decay_rpow {R h : ℝ} (hR : 1 < R) (hh : 0 < h ∧ h < 1) (r : ℝ) :
    Real.exp (-r * referenceTailDuration R h) =
      h ^ (r / R) * Real.exp ((r / R) *
        (Real.arcosh R - Real.log (R + Real.sqrt (R ^ 2 - h ^ 2)))) := by
  rw [Real.rpow_def_of_pos hh.1, ← Real.exp_add, referenceTailDuration_eq]
  congr 1
  change -r * (arcoshGap R h / R) = _
  rw [arcoshGap_log_split hR hh]
  ring

theorem tendsto_referenceTail_log_offset_at {ι : Type*} {l : Filter ι} {R h : ι → ℝ} {R₀ : ℝ}
    (hR₀ : 1 < R₀) (hR : Tendsto R l (𝓝 R₀)) (hh : Tendsto h l (𝓝 0)) :
    Tendsto (fun x => Real.arcosh (R x) - Real.log (R x + Real.sqrt (R x ^ 2 - h x ^ 2)))
      l (𝓝 (Real.arcosh R₀ - Real.log (2 * R₀))) := by
  have hRpos : 0 < R₀ := lt_trans zero_lt_one hR₀
  have HS : Tendsto (fun x => Real.sqrt (R x ^ 2 - h x ^ 2)) l (𝓝 R₀) := by
    simpa only [zero_pow (by norm_num : 2 ≠ 0), sub_zero, Real.sqrt_sq hRpos.le, Function.comp_def] using
      Real.continuous_sqrt.continuousAt.tendsto.comp ((hR.pow 2).sub (hh.pow 2))
  have HA : Tendsto (fun x => R x + Real.sqrt (R x ^ 2 - h x ^ 2)) l (𝓝 (2 * R₀)) := by
    simpa only [two_mul] using hR.add HS
  exact ((Real.hasDerivAt_arcosh hR₀).continuousAt.tendsto.comp hR).sub
    ((Real.continuousAt_log (mul_pos (by norm_num) hRpos).ne').tendsto.comp HA)

/-- The weighted transverse modes decay jointly in the reference radius and the terminal height. -/
theorem tendsto_referenceTail_decay {ι : Type*} {l : Filter ι} {R h r : ι → ℝ} {R₀ r₀ : ℝ}
    (hR₀ : 1 < R₀) (hr₀ : 0 < r₀) (hR : Tendsto R l (𝓝 R₀)) (hh : Tendsto h l (𝓝 0))
    (hr : Tendsto r l (𝓝 r₀)) (hhpos : ∀ᶠ x in l, 0 < h x) :
    Tendsto (fun x => Real.exp (-r x * referenceTailDuration (R x) (h x))) l (𝓝 0) := by
  have hRpos : 0 < R₀ := lt_trans zero_lt_one hR₀
  have HQ := hr.div hR hRpos.ne'
  have HD := tendsto_referenceTail_log_offset_at hR₀ hR hh
  have HP := hh.rpow HQ (Or.inr (div_pos hr₀ hRpos))
  rw [Real.zero_rpow (div_pos hr₀ hRpos).ne'] at HP
  have HE := Real.continuous_exp.continuousAt.tendsto.comp (HQ.mul HD)
  have H := HP.mul HE
  simp only [zero_mul] at H
  apply H.congr'
  filter_upwards [hR.eventually (lt_mem_nhds hR₀), hhpos,
    hh.eventually (gt_mem_nhds (zero_lt_one : (0 : ℝ) < 1))] with x hx hp hx1
  exact (referenceTail_decay_rpow hx ⟨hp, hx1⟩ (r x)).symm

end BianchiIX
