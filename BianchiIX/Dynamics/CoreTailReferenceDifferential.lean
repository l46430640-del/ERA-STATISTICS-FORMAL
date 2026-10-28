import BianchiIX.Dynamics.ReferenceTailResponse
import BianchiIX.Dynamics.ExitTailReturnDifferential

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem coreTailEntry_fderiv {Y : ExitTailState} (hR : 1 < Y 0) (v : ExitTailState) :
    fderiv ℝ coreTailEntry Y v =
      ![-Y 0 / Real.sqrt (Y 0 ^ 2 - 1) * v 0, v 1, 0, v 2] := by
  have hs : Y 0 ^ 2 - 1 ≠ 0 := ne_of_gt (by nlinarith only [hR] : 0 < Y 0 ^ 2 - 1)
  have hd : HasDerivAt (fun s : ℝ => coreTailEntry (Y + s • v))
      ![-Y 0 / Real.sqrt (Y 0 ^ 2 - 1) * v 0, v 1, 0, v 2] 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · have H := (((((hasDerivAt_id (0 : ℝ)).mul_const (v 0)).const_add (Y 0)).pow 2).sub_const 1).sqrt
        (by simpa using hs)
      convert! H.const_sub 1 using 1
      dsimp
      ring_nf
    · simpa [coreTailEntry] using ((hasDerivAt_id (0 : ℝ)).mul_const (v 1)).const_add (Y 1)
    · exact hasDerivAt_const 0 1
    · simpa [coreTailEntry] using ((hasDerivAt_id (0 : ℝ)).mul_const (v 2)).const_add (Y 2)
  have hl : HasDerivAt (fun s : ℝ => Y + s • v) v 0 := by
    convert! (hasDerivAt_const (0 : ℝ) Y).add ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1
    simp
  have hf : HasFDerivAt coreTailEntry (fderiv ℝ coreTailEntry Y) (Y + (0 : ℝ) • v) := by
    simpa only [zero_smul, add_zero] using
      ((contDiffAt_coreTailEntry 1 hR).differentiableAt (by norm_num)).hasFDerivAt
  have H : HasDerivAt (fun s : ℝ => coreTailEntry (Y + s • v))
      (fderiv ℝ coreTailEntry Y v) 0 := by
    convert! hf.comp_hasDerivAt 0 hl using 1
  exact H.unique hd

/-- The ordinary derivative of the actual first-arrival map, including its varying arrival time. -/
theorem coreTail_reference_differential {k h : ℝ} (hk : 1 < k)
    (hh : 0 < h ∧ h < 1) (v : ExitTailState) :
    fderiv ℝ (fun Y => toExitTailState (coreTailState h Y)) ![k, 0, 0] v =
      ![v 0 - (2 / k) * (1 - Real.exp (-(k ^ 2 / 2) * referenceTailDuration k h)) * v 1,
        Real.exp (-(k ^ 2 / 2) * referenceTailDuration k h) / h * v 1,
        Real.exp (-2 * referenceTailDuration k h) / h * v 2] := by
  have hk0 : 0 < k := lt_trans zero_lt_one hk
  have HR := coreTail_reference_regular hk hh
  have HV := HR.2.2.2.2.self_of_nhds
  have hsqrt : 0 < Real.sqrt (k ^ 2 - h ^ 2) := Real.sqrt_pos.mpr (by
    nlinarith only [hk, hh.1, hh.2])
  have hv : 0 < coreTailState h ![k, 0, 0] 2 := by rw [HR.2.1]; exact hh.1
  have hm : coreTailState h ![k, 0, 0] 0 < 1 := by
    rw [HR.2.1]; change 1 - Real.sqrt (k ^ 2 - h ^ 2) < 1; linarith only [hsqrt]
  have hd : exitClockRate (coreTailState h ![k, 0, 0]) ≠ 0 := by
    rw [HR.2.1]
    simpa [exitClockRate, coupling] using hsqrt.ne'
  rw [coreTailState_exit_differential hk HV hv hm hd, HR.1, coreTailEntry_reference hk,
    referenceTail_projected_variation hk hh]
  have hrad : fderiv ℝ (fun z : ProjectiveState => coreRadius (z 0) (z 2))
      (referencePulse k (referenceHalfTime k)) (fderiv ℝ coreTailEntry ![k, 0, 0] v) = v 0 := by
    rw [referencePulse_radius_fderiv hk0, referencePulse_exit hk, coreTailEntry_fderiv hk]
    dsimp
    have hs := (referenceCoreGap_pos hk).ne'
    field_simp
    ring
  rw [hrad, coreTailEntry_fderiv hk]
  ext i
  fin_cases i
  · dsimp
    ring
  · rfl
  · rfl

theorem coreTail_reference_coordinates {k h : ℝ} (hk : 1 < k) (hh : 0 < h ∧ h < 1) :
    toExitTailState (coreTailState h ![k, 0, 0]) = ![k, 0, 0] := by
  rw [(coreTail_reference_regular hk hh).2.1,
    ← referencePulse_height_exit (lt_trans zero_lt_one hk) ⟨hh.1, hh.2.trans hk⟩]
  exact toExitTailState_reference (lt_trans zero_lt_one hk).le _

/-- Recover the actual multiplier at a zero input wall by differentiating its smooth product. -/
theorem coreTail_reference_multiplier {k h : ℝ} (hk : 1 < k)
    (hh : 0 < h ∧ h < 1) (i : Fin 2) :
    coreTailMultiplier h ![k, 0, 0] i =
      Real.exp (-(if i = 0 then k ^ 2 / 2 else 2) * referenceTailDuration k h) / h := by
  let Y : ExitTailState := ![k, 0, 0]
  let F := fun Z => toExitTailState (coreTailState h Z)
  let v : ExitTailState := Pi.single i.succ 1
  have HR := coreTail_reference_regular hk hh
  have HV := HR.2.2.2.2.self_of_nhds
  have hm := ((contDiffAt_coreTailMultiplier_two hk HV HR.2.2.1 i).1.differentiableAt
    (by norm_num)).hasFDerivAt
  have hp := (hasFDerivAt_apply (𝕜 := ℝ) i.succ Y).mul hm
  have heq : (fun Z => F Z i.succ) =ᶠ[𝓝 Y] (fun Z => Z i.succ * coreTailMultiplier h Z i) := by
    filter_upwards [HR.2.2.2.2] with Z hZ
    fin_cases i
    · exact coreTailMultiplier_formula hZ 0
    · exact coreTailMultiplier_formula hZ 1
  have hv : 0 < coreTailState h Y 2 := by rw [HR.2.1]; exact hh.1
  have hF : DifferentiableAt ℝ F Y :=
    ((contDiffAt_toExitTailState 2 hv).comp Y HR.2.2.2.1).differentiableAt (by norm_num)
  have H := congrArg (fun L : ExitTailState →L[ℝ] ℝ => L v) (heq.fderiv_eq.trans hp.fderiv)
  rw [fderiv_apply hF i.succ] at H
  have HF := congrArg (fun Z : ExitTailState => Z i.succ) (coreTail_reference_differential hk hh v)
  change (fderiv ℝ F Y v) i.succ = _ at HF
  change (fderiv ℝ F Y v) i.succ = _ at H
  rw [HF] at H
  fin_cases i <;> simpa [Y, v, add_apply, smul_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul] using H.symm

theorem coreTail_reference_weighted_multiplier {k h : ℝ} (hk : 1 < k)
    (hh : 0 < h ∧ h < 1) (i : Fin 2) :
    h * coreTailMultiplier h ![k, 0, 0] i =
      Real.exp (-(if i = 0 then k ^ 2 / 2 else 2) * referenceTailDuration k h) := by
  rw [coreTail_reference_multiplier hk hh]
  field_simp [hh.1.ne']

/-- The finite logarithmic-clock formulas (D.41) are identities for the actual flow. -/
theorem coreTail_reference_logClock {k s : ℝ} (hk : 1 < k) (hs : 0 < s) :
    let h := Real.exp (-s)
    let τ := (Real.arcosh (k * Real.exp s) - Real.arcosh k) / k
    coreTailMultiplier h ![k, 0, 0] 0 = Real.exp (s - k ^ 2 * τ / 2) ∧
      coreTailMultiplier h ![k, 0, 0] 1 = Real.exp (s - 2 * τ) ∧
      ∀ v : ExitTailState,
        fderiv ℝ (fun Y => toExitTailState (coreTailState h Y)) ![k, 0, 0] v =
          ![v 0 - (2 / k) * (1 - Real.exp (-k ^ 2 * τ / 2)) * v 1,
            Real.exp (s - k ^ 2 * τ / 2) * v 1, Real.exp (s - 2 * τ) * v 2] := by
  intro h τ
  have hh : 0 < h ∧ h < 1 := ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (neg_neg_of_pos hs)⟩
  have ht : referenceTailDuration k h = τ := by
    rw [referenceTailDuration_eq]
    dsimp [h, τ]
    rw [Real.exp_neg, div_inv_eq_mul]
  have he (r : ℝ) : Real.exp (-r * referenceTailDuration k h) / h = Real.exp (s - r * τ) := by
    rw [ht]
    change Real.exp (-r * τ) / Real.exp (-s) = _
    rw [← Real.exp_sub]
    congr 1
    ring
  constructor
  · rw [coreTail_reference_multiplier hk hh]
    simp only [ite_true]
    rw [he]
    congr 1
    ring
  constructor
  · rw [coreTail_reference_multiplier hk hh]
    norm_num only [Fin.isValue, one_ne_zero, ite_false]
    exact he 2
  · intro v
    rw [coreTail_reference_differential hk hh, he, he, ht]
    rw [show -(k ^ 2 / 2) * τ = -k ^ 2 * τ / 2 by ring,
      show s - (k ^ 2 / 2) * τ = s - k ^ 2 * τ / 2 by ring]

end BianchiIX
