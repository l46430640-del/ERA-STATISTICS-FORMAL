import BianchiIX.Analysis.TerminalReferenceLimits
import BianchiIX.Dynamics.CoreTailReferenceDifferential

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem coreTail_reference_log_split {k h : ℝ} (hk : 1 < k)
    (hh : 0 < h ∧ h < 1) (i : Fin 2) :
    let r := if i = 0 then k ^ 2 / 2 else 2
    Real.log (coreTailMultiplier h ![k, 0, 0] i) =
      (r / k - 1) * Real.log h + r / k *
        (Real.arcosh k - Real.log (k + Real.sqrt (k ^ 2 - h ^ 2))) := by
  intro r
  rw [coreTail_reference_multiplier hk hh,
    Real.log_div (Real.exp_pos _).ne' hh.1.ne', Real.log_exp, referenceTailDuration_eq]
  change -r * (arcoshGap k h / k) - Real.log h = _
  rw [arcoshGap_log_split hk hh]
  ring

/-- Both actual boundary multipliers have the same Taub limit when the logarithmic drift vanishes. -/
theorem tendsto_coreTail_reference_multiplier {ι : Type*} {l : Filter ι} {k h : ι → ℝ}
    (hk : Tendsto k l (𝓝 2)) (hh : Tendsto h l (𝓝 0))
    (hhpos : ∀ᶠ x in l, 0 < h x)
    (hlog : Tendsto (fun x => (k x - 2) * Real.log (h x)) l (𝓝 0)) (i : Fin 2) :
    Tendsto (fun x => coreTailMultiplier (h x) ![k x, 0, 0] i) l (𝓝 taubMultiplierConstant) := by
  let d := fun x => Real.arcosh (k x) - Real.log (k x + Real.sqrt (k x ^ 2 - h x ^ 2))
  let d₀ := Real.arcosh 2 - Real.log 4
  have hd : Tendsto d l (𝓝 d₀) := tendsto_referenceTail_log_offset hk hh
  have hk₂ : Tendsto (fun x => k x / 2) l (𝓝 1) := by simpa using hk.div_const 2
  have h₂k : Tendsto (fun x => 2 / k x) l (𝓝 1) := by
    have HC : Tendsto (fun _ : ι => (2 : ℝ)) l (𝓝 2) := tendsto_const_nhds
    have HQ := HC.div hk (by norm_num : (2 : ℝ) ≠ 0)
    change Tendsto (fun x => (2 : ℝ) / k x) l (𝓝 ((2 : ℝ) / 2)) at HQ
    norm_num at HQ
    exact HQ
  let e := fun x => if i = 0 then
    (k x - 2) * Real.log (h x) / 2 + (k x / 2) * d x
    else -((k x - 2) * Real.log (h x)) / k x + (2 / k x) * d x
  have he : Tendsto e l (𝓝 d₀) := by
    fin_cases i
    · simpa [e, Pi.div_apply] using
        (hlog.div_const 2).add (hk₂.mul hd)
    · simpa [e, Pi.div_apply] using
        (hlog.neg.div hk (by norm_num : (2 : ℝ) ≠ 0)).add (h₂k.mul hd)
  have HE := Real.continuous_exp.continuousAt.tendsto.comp he
  change Tendsto (fun x => Real.exp (e x)) l (𝓝 (Real.exp d₀)) at HE
  rw [show Real.exp d₀ = taubMultiplierConstant from exp_arcosh_two_sub_log_four] at HE
  apply HE.congr'
  filter_upwards [hhpos, hk.eventually (lt_mem_nhds (by norm_num : (1 : ℝ) < 2)),
    hh.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with x hx hkx hhx
  have hk0 : k x ≠ 0 := (lt_trans zero_lt_one hkx).ne'
  symm
  rw [← Real.exp_log (coreTailMultiplier_pos (h x) ![k x, 0, 0] i)]
  congr 1
  rw [coreTail_reference_log_split hkx ⟨hx, hhx⟩]
  fin_cases i <;> (dsimp [e, d]; field_simp)
  all_goals ring

theorem tendsto_terminal_reference_multiplier {η : ℝ} (hη : 0 < η) {J : ℕ} (hJ : 1 ≤ J)
    (i : Fin 2) :
    Tendsto (fun α : ℝ => coreTailMultiplier (η * α ^ J) ![2 + 2 * α, 0, 0] i)
      (𝓝[>] 0) (𝓝 taubMultiplierConstant) := by
  have H : Tendsto (fun α : ℝ => α) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hk : Tendsto (fun α : ℝ => 2 + 2 * α) (𝓝[>] 0) (𝓝 2) := by
    simpa using (H.const_mul 2).const_add 2
  have hhpos : ∀ᶠ α : ℝ in 𝓝[>] 0, 0 < η * α ^ J :=
    (eventually_terminal_reference_parameters hη hJ).mono fun _ ha => ha.2.2.1
  have hlog : Tendsto (fun α : ℝ => (2 + 2 * α - 2) * Real.log (η * α ^ J))
      (𝓝[>] 0) (𝓝 0) := by
    have HL := (tendsto_terminal_scaled_log_height hη.ne' J).const_mul 2
    simp only [mul_zero] at HL
    apply HL.congr'
    exact Eventually.of_forall fun α => by ring
  exact tendsto_coreTail_reference_multiplier hk (tendsto_terminal_height η hJ) hhpos hlog i

end BianchiIX
