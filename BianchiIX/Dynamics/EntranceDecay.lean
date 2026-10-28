import BianchiIX.Dynamics.EntranceRegion
import BianchiIX.Analysis.ClockDecayIntegrals

noncomputable section

namespace BianchiIX

open Set

theorem scaled_entrance_decay {Y : ℝ → ProjectiveState} {a : ℝ → ℝ} {s t k : ℝ}
    (hk : 7 / 4 ≤ k)
    (hY : ∀ r ∈ Icc s t, HasDerivAt Y (a r • projectiveField (Y r)) r)
    (ha : ∀ r ∈ Icc s t, 0 ≤ a r) (hy : ∀ r ∈ Icc s t, entranceRegion k (Y r))
    (hv : ∀ r ∈ Icc s t, 0 < Y r 2) :
    ∀ r ∈ Icc s t,
      |Y r 1| ≤ |Y s 1| * Real.exp (-(1 + k / 3) * (Real.log (Y r 2) - Real.log (Y s 2))) ∧
      |Y r 3| ≤ |Y s 3| * Real.exp (-(1 + 1 / k) * (Real.log (Y r 2) - Real.log (Y s 2))) := by
  let z := fun r => Real.log (Y r 2)
  let q := fun r => a r * entranceClockRate (Y r)
  have hz (r : ℝ) (hr : r ∈ Icc s t) : HasDerivAt z (q r) r :=
    hasDerivAt_entranceLog_scaled (hY r hr) (hv r hr).ne'
  have hq (r : ℝ) (hr : r ∈ Icc s t) : 0 ≤ q r :=
    mul_nonneg (ha r hr) (entranceRegion_clock_pos hk (hy r hr)).le
  have hU (r : ℝ) (hr : r ∈ Icc s t) :
      HasDerivAt (fun b => Y b 1)
        (q r * (connectionStrongRate (Y r 0) (Y r 1) (Y r 2) (Y r 3) / entranceClockRate (Y r) * Y r 1)) r := by
    have hD := (entranceRegion_clock_pos hk (hy r hr)).ne'
    convert! hasDerivAt_pi.mp (hY r hr) 1 using 1
    change _ = a r * strongVelocity (Y r 0) (Y r 1) (Y r 2) (Y r 3)
    dsimp [q, strongVelocity, connectionStrongRate]
    field_simp
  have hW (r : ℝ) (hr : r ∈ Icc s t) :
      HasDerivAt (fun b => Y b 3)
        (q r * ((-Y r 0 - 1 - coupling (Y r 1) (Y r 2) (Y r 3)) / entranceClockRate (Y r) * Y r 3)) r := by
    have hD := (entranceRegion_clock_pos hk (hy r hr)).ne'
    convert! hasDerivAt_pi.mp (hY r hr) 3 using 1
    change _ = a r * weakVelocity (Y r 0) (Y r 1) (Y r 2) (Y r 3)
    dsimp [q, weakVelocity]
    field_simp
  have H := abs_le_exp_of_clock_damping hU hz hq
    (fun r hr => (entranceRegion_wall_rates hk (hy r hr)).1)
  have J := abs_le_exp_of_clock_damping hW hz hq
    (fun r hr => (entranceRegion_wall_rates hk (hy r hr)).2)
  exact fun r hr => ⟨H r hr, J r hr⟩

theorem normalized_entrance_decay {x : NormalizedState} {t₀ s t k : ℝ}
    (hc : stateConstraint x = 1) (hk : 7 / 4 ≤ k) (hs : t₀ ≤ s) (hst : s ≤ t)
    (hA : ∀ r ∈ Icc s t, 0 < normalizedProjectiveRate x t₀ r) :
    let Y := fun r => toProjectiveState (normalizedMaxCurve x t₀ r)
    (∀ r ∈ Icc s t, entranceRegion k (Y r)) → 0 < Y s 2 →
    ∀ r ∈ Icc s t,
      Y r 1 ≤ Y s 1 * Real.exp (-(1 + k / 3) * (Real.log (Y r 2) - Real.log (Y s 2))) ∧
      Y r 3 ≤ Y s 3 * Real.exp (-(1 + 1 / k) * (Real.log (Y r 2) - Real.log (Y s 2))) := by
  intro Y hy hvs
  have hdom (r : ℝ) (hr : s ≤ r) := normalizedMaxDomain_contains_Ici_of_constraint hc t₀ (hs.trans hr)
  have hY (r : ℝ) (hr : r ∈ Icc s t) : HasDerivAt Y
      (normalizedProjectiveRate x t₀ r • projectiveField (Y r)) r := by
    have H := normalizedMaxCurve_forward_of_constraint hc (hs.trans hr.1)
    exact hasDerivAt_toProjectiveState_normalized H.1 (hA r hr).ne' H.2.1
  have hv (r : ℝ) (hr : r ∈ Icc s t) : 0 < Y r 2 :=
    normalized_projective_wall_pos (hdom s le_rfl) (hdom r hr.1)
      (hA s ⟨le_rfl, hst⟩) (hA r hr) 1 hvs
  have H := scaled_entrance_decay hk hY (fun r hr => (hA r hr).le) hy hv
  intro r hr
  simpa only [abs_of_nonneg (hy r hr).2.2.1.1, abs_of_nonneg (hy s ⟨le_rfl, hst⟩).2.2.1.1,
    abs_of_nonneg (hy r hr).2.2.2.2.1, abs_of_nonneg (hy s ⟨le_rfl, hst⟩).2.2.2.2.1] using H r hr

end BianchiIX
