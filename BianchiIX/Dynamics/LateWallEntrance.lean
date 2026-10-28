import BianchiIX.Dynamics.SmallWallEntry
import BianchiIX.Dynamics.SmallWallArrival

noncomputable section

namespace BianchiIX

open Set

/-- Any uniformly Taub-avoiding orbit with sufficiently small future wall products reaches a transverse fixed-height entrance. -/
theorem exists_late_fixedWall_entrance {ε : ℝ} (hε : 0 < ε) :
    ∃ ν₀ > (0 : ℝ), ν₀ ≤ 1 / 4 ∧ ∃ c > (0 : ℝ), c ≤ 1 ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ Δ : ℝ, 0 ≤ Δ → Δ ≤ ν / 8 →
        ∀ x : NormalizedState, stateConstraint x = 1 → positiveWalls x →
          normalizedTaubAvoidance ε x →
          (∀ u ≥ (0 : ℝ), normalizedWallProductsBound Δ (normalizedMaxCurve x 0 u)) →
          ∃ s ∈ Icc 0 (5 / ν ^ 2), ∃ T > s, ∃ i : Fin 3,
            (∀ j : Fin 3, wallValue j (normalizedMaxCurve x 0 s) < ν) ∧
            IsLeast {t | s < t ∧ t ∈ normalizedMaxDomain x 0 ∧
              ∃ j : Fin 3, wallValue j (normalizedMaxCurve x 0 t) = ν} T ∧
            (∀ u ∈ Ico s T, ∀ j : Fin 3, wallValue j (normalizedMaxCurve x 0 u) < ν) ∧
            wallValue i (normalizedMaxCurve x 0 T) = ν ∧
            (∀ j : Fin 3, j ≠ i → wallValue j (normalizedMaxCurve x 0 T) < ν) ∧
            c ≤ wallRate i (normalizedMaxCurve x 0 T) ∧
            HasDerivAt (fun u => wallValue i (normalizedMaxCurve x 0 u))
              (wallRate i (normalizedMaxCurve x 0 T) * ν) T ∧
            0 < c * ν ∧ c * ν ≤ wallRate i (normalizedMaxCurve x 0 T) * ν := by
  obtain ⟨ν₀, hν₀, hν₀max, c, hc, hcmax, H⟩ := exists_smallWall_first_upcrossing hε
  refine ⟨ν₀, hν₀, hν₀max, c, hc, hcmax, ?_⟩
  intro ν hν hνcap Δ hΔ hΔmax x hx hp ha hprod
  obtain ⟨s, hs, hsmall⟩ := exists_normalized_smallWall_entry hx hp hν (hνcap.trans hν₀max)
    ⟨hΔ, hΔmax⟩ (fun u hu => hprod u hu.1)
  let y := normalizedMaxCurve x 0 s
  have hdoms := normalizedMaxDomain_contains_Ici_of_constraint hx 0 hs.1
  have hy : stateConstraint y = 1 := (normalizedMaxCurve_forward_of_constraint hx hs.1).2.1
  have hpos : positiveWalls y := normalized_positive_walls_invariant
    (convex_normalizedMaxDomain x 0) (isOpen_normalizedMaxDomain x 0)
    (fun v hv => hasDerivAt_normalizedMaxCurve hv) (initial_mem_normalizedMaxDomain x 0) hdoms
    (by simpa only [normalizedMaxCurve_initial] using hp)
  obtain ⟨τ, hτ, i, hfirst, hpre, hgap, hhit, hother, _, _, _⟩ :=
    H ν hν hνcap y hy hpos hsmall (ha.forward hs.1 hdoms)
  have hrestart (u : ℝ) (hu : s ≤ u) :
      normalizedMaxCurve x 0 u = normalizedMaxCurve y 0 (u - s) :=
    (normalizedMaxCurve_restart hdoms
      (normalizedMaxDomain_contains_Ici_of_constraint hy 0 (sub_nonneg.mpr hu))).2
  have hend : normalizedMaxCurve x 0 (s + τ) = normalizedMaxCurve y 0 τ := by
    simpa only [add_sub_cancel_left] using hrestart (s + τ) (by linarith only [hτ])
  have hT : s < s + τ := by linarith only [hτ]
  have hTdom := normalizedMaxDomain_contains_Ici_of_constraint hx 0 (hs.1.trans hT.le)
  have hactive : wallValue i (normalizedMaxCurve x 0 (s + τ)) = ν := by rw [hend]; exact hhit
  have hleast : IsLeast {t | s < t ∧ t ∈ normalizedMaxDomain x 0 ∧
      ∃ j : Fin 3, wallValue j (normalizedMaxCurve x 0 t) = ν} (s + τ) := by
    refine ⟨⟨hT, hTdom, i, hactive⟩, ?_⟩
    intro u hu
    have hud : u - s ∈ normalizedMaxDomain y 0 :=
      normalizedMaxDomain_contains_Ici_of_constraint hy 0 (sub_pos.mpr hu.1).le
    have hh : ∃ j : Fin 3, wallValue j (normalizedMaxCurve y 0 (u - s)) = ν := by
      rw [← hrestart u hu.1.le]
      exact hu.2.2
    have hle := hfirst.2 ⟨sub_pos.mpr hu.1, hud, hh⟩
    linarith only [hle]
  have hprefix (u : ℝ) (hu : u ∈ Ico s (s + τ)) (j : Fin 3) :
      wallValue j (normalizedMaxCurve x 0 u) < ν := by
    rw [hrestart u hu.1]
    exact hpre (u - s) ⟨sub_nonneg.mpr hu.1, by linarith only [hu.2]⟩ j
  have hother' (j : Fin 3) (hj : j ≠ i) : wallValue j (normalizedMaxCurve x 0 (s + τ)) < ν := by
    rw [hend]
    exact hother j hj
  have hrate : c ≤ wallRate i (normalizedMaxCurve x 0 (s + τ)) := by
    rw [hend]
    exact (hgap τ ⟨hτ.le, le_rfl⟩).1
  have hd := hasDerivAt_wallValue
    (normalizedMaxCurve_forward_of_constraint hx (hs.1.trans hT.le)).1 i
  rw [hactive] at hd
  exact ⟨s, hs, s + τ, hT, i, hsmall, hleast, hprefix, hactive, hother', hrate, hd,
    mul_pos hc hν, mul_le_mul_of_nonneg_right hrate hν.le⟩

end BianchiIX
