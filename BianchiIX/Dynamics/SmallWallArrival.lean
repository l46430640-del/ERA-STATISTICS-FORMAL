import BianchiIX.Dynamics.SmallWallMotion
import BianchiIX.Dynamics.TaubAvoidance
import BianchiIX.Analysis.FirstLevelHit

noncomputable section

namespace BianchiIX

open Set

def normalizedWallMaximum (x : NormalizedState) : ℝ := max (x 2) (max (x 3) (x 4))

theorem wallValue_le_wallMaximum (x : NormalizedState) (i : Fin 3) :
    wallValue i x ≤ normalizedWallMaximum x := by
  fin_cases i
  · exact le_max_left _ _
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

/-- Every Taub-avoiding positive orbit starting below a small wall height has a first upward wall hit. -/
theorem exists_smallWall_first_upcrossing {ε : ℝ} (hε : 0 < ε) :
    ∃ ν₀ > (0 : ℝ), ν₀ ≤ 1 / 4 ∧ ∃ c > (0 : ℝ), c ≤ 1 ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ x : NormalizedState,
        stateConstraint x = 1 → positiveWalls x → (∀ i : Fin 3, wallValue i x < ν) →
        normalizedTaubAvoidance ε x → ∃ T > (0 : ℝ), ∃ i : Fin 3,
          IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain x 0 ∧
            ∃ j : Fin 3, wallValue j (normalizedMaxCurve x 0 t) = ν} T ∧
          (∀ u ∈ Ico 0 T, ∀ j : Fin 3, wallValue j (normalizedMaxCurve x 0 u) < ν) ∧
          (∀ u ∈ Icc 0 T, c ≤ wallRate i (normalizedMaxCurve x 0 u) ∧
            ∀ j : Fin 3, j ≠ i → wallRate j (normalizedMaxCurve x 0 u) ≤ -c) ∧
          wallValue i (normalizedMaxCurve x 0 T) = ν ∧
          (∀ j : Fin 3, j ≠ i → wallValue j (normalizedMaxCurve x 0 T) < ν) ∧
          HasDerivAt (fun u => wallValue i (normalizedMaxCurve x 0 u))
            (wallRate i (normalizedMaxCurve x 0 T) * ν) T ∧
          0 < c * ν ∧ c * ν ≤ wallRate i (normalizedMaxCurve x 0 T) * ν := by
  obtain ⟨ν₀, hν₀, hν₀max, c, hc, hcmax, HG⟩ := exists_smallWall_growth_gap hε
  refine ⟨ν₀, hν₀, hν₀max, c, hc, hcmax, ?_⟩
  intro ν hν hνcap x hx hp hsmall ha
  let α := normalizedMaxCurve x 0
  let f := fun t => normalizedWallMaximum (α t)
  have hdom (u : ℝ) (hu : 0 ≤ u) : u ∈ normalizedMaxDomain x 0 :=
    normalizedMaxDomain_contains_Ici_of_constraint hx 0 hu
  have hflow (u : ℝ) (hu : 0 ≤ u) : HasDerivAt α (normalizedField (α u)) u :=
    (normalizedMaxCurve_forward_of_constraint hx hu).1
  have hpos (u : ℝ) (hu : 0 ≤ u) (i : Fin 3) : 0 < wallValue i (α u) := by
    have hstart : 0 < wallValue i x := by fin_cases i <;> first | exact hp.1 | exact hp.2.1 | exact hp.2.2
    exact normalized_wall_pos (convex_normalizedMaxDomain x 0) (isOpen_normalizedMaxDomain x 0)
      (fun v hv => hasDerivAt_normalizedMaxCurve hv) (initial_mem_normalizedMaxDomain x 0)
      (hdom u hu) i (by simpa only [normalizedMaxCurve_initial] using hstart)
  have hgap (u : ℝ) (hu : 0 ≤ u) (hfu : f u ≤ ν) :
      ∃ i : Fin 3, c ≤ wallRate i (α u) ∧ ∀ j : Fin 3, j ≠ i → wallRate j (α u) ≤ -c :=
    HG (α u) (normalizedMaxCurve_forward_of_constraint hx hu).2.1
      (fun i => ⟨(hpos u hu i).le, ((wallValue_le_wallMaximum (α u) i).trans hfu).trans hνcap⟩)
      (ha u hu (hdom u hu))
  have hf (H : ℝ) : ContinuousOn f (Icc 0 H) := by
    have hα : ContinuousOn α (Icc 0 H) := fun u hu => (hflow u hu.1).continuousAt.continuousWithinAt
    exact (show Continuous normalizedWallMaximum by unfold normalizedWallMaximum; fun_prop).comp_continuousOn hα
  have hf0 : f 0 < ν := by
    change max (α 0 2) (max (α 0 3) (α 0 4)) < ν
    simp only [α, normalizedMaxCurve_initial]
    exact max_lt (hsmall 0) (max_lt (hsmall 1) (hsmall 2))
  have hexit : ∃ H ≥ (0 : ℝ), ν ≤ f H := by
    by_contra! hnone
    let m := min (x 2) (min (x 3) (x 4))
    have hm : 0 < m := lt_min hp.1 (lt_min hp.2.1 hp.2.2)
    have hmi (i : Fin 3) : m ≤ wallValue i x := by
      fin_cases i
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (min_le_left _ _)
      · exact (min_le_right _ _).trans (min_le_right _ _)
    let H := ν / (c * m)
    have hH : 0 < H := div_pos hν (mul_pos hc hm)
    obtain ⟨i, _, _, _, hgrow⟩ := normalized_growth_gap_motion hx hp hH.le hc
      (fun u hu => hgap u hu.1 (hnone u hu.1).le)
    have hl := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (c * H)) hm.le
    have heq : m * (c * H + 1) = ν + m := by
      dsimp [H]
      field_simp [hc.ne', hm.ne']
    rw [heq] at hl
    have hh := (hl.trans (mul_le_mul_of_nonneg_right (hmi i) (Real.exp_pos _).le)).trans hgrow
    have hu : wallValue i (α H) < ν := (wallValue_le_wallMaximum (α H) i).trans_lt (hnone H hH.le)
    linarith only [hh, hu, hm]
  obtain ⟨H, hH, hreach⟩ := hexit
  obtain ⟨T, hT, hhit, hprefix⟩ := exists_first_level_hit hH (hf H) hf0 hreach
  have hwhole (u : ℝ) (hu : u ∈ Icc 0 T) : f u ≤ ν := by
    rcases lt_or_eq_of_le hu.2 with hh | rfl
    · exact (hprefix u ⟨hu.1, hh⟩).le
    · exact hhit.le
  obtain ⟨i, Hi, _, Hanti, _⟩ := normalized_growth_gap_motion hx hp hT.1.le hc
    (fun u hu => hgap u hu.1 (hwhole u hu))
  have hother (j : Fin 3) (hj : j ≠ i) : wallValue j (α T) < ν := by
    have hh := Hanti j hj ⟨le_rfl, hT.1.le⟩ ⟨hT.1.le, le_rfl⟩ hT.1
    exact hh.trans (by simpa only [normalizedMaxCurve_initial] using hsmall j)
  have hactive : wallValue i (α T) = ν := by
    have hle := (wallValue_le_wallMaximum (α T) i).trans_eq hhit
    apply le_antisymm hle
    by_contra! hh
    have hall (j : Fin 3) : wallValue j (α T) < ν := by
      by_cases hj : j = i
      · simpa only [hj] using hh
      · exact hother j hj
    have hfT : f T < ν := max_lt (hall 0) (max_lt (hall 1) (hall 2))
    exact (ne_of_lt hfT) hhit
  have hpre (u : ℝ) (hu : u ∈ Ico 0 T) (j : Fin 3) : wallValue j (α u) < ν :=
    (wallValue_le_wallMaximum (α u) j).trans_lt (hprefix u hu)
  have hleast : IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain x 0 ∧
      ∃ j : Fin 3, wallValue j (α t) = ν} T := by
    refine ⟨⟨hT.1, hdom T hT.1.le, i, hactive⟩, ?_⟩
    intro u hu
    by_contra! hh
    obtain ⟨j, hj⟩ := hu.2.2
    exact (hpre u ⟨hu.1.le, hh⟩ j).ne hj
  have hd := hasDerivAt_wallValue (hflow T hT.1.le) i
  rw [hactive] at hd
  exact ⟨T, hT.1, i, hleast, hpre, Hi, hactive, hother, hd,
    mul_pos hc hν, mul_le_mul_of_nonneg_right (Hi T ⟨hT.1.le, le_rfl⟩).1 hν.le⟩

end BianchiIX
