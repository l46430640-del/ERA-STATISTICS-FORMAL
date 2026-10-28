import BianchiIX.Dynamics.ProjectiveProductMonotonicity
import BianchiIX.Dynamics.ShearRestartTailEntranceInputs
import BianchiIX.Dynamics.ShearRestartProjectiveEntry

noncomputable section

namespace BianchiIX

open Set

/-- The exact tail preserves the original two-wall product budget, including zero weak walls. -/
theorem exists_restartShearTail_product :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 2 < q → 2 < D → 6 * D + 2 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε ζ ν : ℝ,
          (0 ≤ ε ∧ ε ≤ 1 / 128) →
          (0 ≤ ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
          (0 ≤ ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
          let T := shearTailTime a D
          let Y := fun t => restartShearTailProjectiveEntry h a q ζ ν t ρ
          AntitoneOn (fun t => Y t 2 * Y t 3) (Icc 0 T) ∧
          0 ≤ Y T 2 * Y T 3 ∧ Y T 2 * Y T 3 ≤ 256 * ζ * ν / a ^ 4 := by
  obtain ⟨hT, hhT, HT⟩ := exists_restartShearTail_control
  obtain ⟨hF, hhF, HF⟩ := exists_restartFastShearProjectiveEntry_bounds
  refine ⟨min hT hF, lt_min hhT hhF, ?_⟩
  intro h hh q D P hq hD hP
  obtain ⟨aT, haT, HAT⟩ := HT h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq (by linarith only [hD]) hP
  obtain ⟨aF, haF, HAF⟩ := HF h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q hq
  obtain ⟨aS, haS, HAS⟩ := exists_shearTail_entrance_wall_scale (h := h) hq hD zero_lt_one
  refine ⟨min aT (min aF aS), lt_min haT (lt_min haF haS), ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ T Y
  obtain ⟨_, _, hT0, _, _, Hall, _⟩ :=
    HAT a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, Hfast⟩ :=
    HAF a ⟨ha.1, ha.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩ ε 1 ζ ν
      ⟨hε.1, by linarith only [hε.2]⟩ (by norm_num) ⟨hζ.1, hζ.2.2⟩ hν ρ hρ
  obtain ⟨_, Hscale⟩ := HAS a
    ⟨ha.1, ha.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  have Hu1 : 20 * h * a ^ (q - 2) ≤ 1 := by
    have hp : 0 ≤ 20 * h * a ^ (q - 2) + 80 * a ^ (D / 2 - 1) := by positivity [hh.1, ha.1]
    have HL := mul_le_mul_of_nonneg_left (show 1 ≤ 1 + |Real.log a| by linarith only [abs_nonneg (Real.log a)]) hp
    have hw0 : 0 ≤ 80 * a ^ (D / 2 - 1) := by positivity [ha.1]
    linarith only [Hscale, HL, hw0]
  let Z := fun t => restartShearTailFlow h a q ζ ν t ρ
  let A := fun t => 1 + Z t 0
  have Hlocal (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivAt Y (A t • projectiveField (Y t)) t ∧ 0 ≤ A t ∧
      (0 ≤ Y t 1 ∧ Y t 1 ≤ 1) ∧ 0 ≤ Y t 2 ∧ 0 ≤ Y t 3 := by
    obtain ⟨hdom, _, hcon, hn, _, Hn, _, _, _, HAl, _, _⟩ := Hall t ht
    have hA : 0 < A t := (by positivity [ha.1] : 0 < a ^ 2 / 10).trans_le HAl
    have HD : HasDerivAt Z (normalizedField (Z t)) t := by
      have H := (hasDerivAt_normalizedMaxCurve hdom).scomp t
        ((hasDerivAt_id t).add_const (q / 2 * Real.log (1 / a)))
      convert! H using 1
      simp only [Z, restartShearTailFlow, one_smul]
    have HY := hasDerivAt_toProjectiveState_normalized HD hA.ne' hcon
    have Hn' : Z t 2 ≤ h * a ^ q := Hn.trans
      (mul_le_of_le_one_right (by positivity [hh.1, ha.1])
        (Real.exp_le_one_iff.mpr (by linarith only [ht.1])))
    obtain ⟨Hu0, Hu⟩ := shearTail_projectiveCoordinate_le ha.1 HAl ⟨hn.1, Hn'⟩
    have Hu' : Y t 1 ≤ 20 * h * a ^ (q - 2) := Hu.trans_eq (by
      rw [Real.rpow_sub ha.1, Real.rpow_two]
      ring)
    have Hv : 0 ≤ Y t 2 := div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hn.2.1) hA.le
    have Hw : 0 ≤ Y t 3 := div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hn.2.2) hA.le
    exact ⟨HY, hA.le, ⟨Hu0, Hu'.trans Hu1⟩, Hv, Hw⟩
  have Hmono := scaled_projective_product_antitone (convex_Icc 0 T)
    (fun t ht => (Hlocal t ht).1) (fun t ht => (Hlocal t ht).2.1)
    (fun t ht => (Hlocal t ht).2.2.1) (fun t ht => (Hlocal t ht).2.2.2.1)
    (fun t ht => (Hlocal t ht).2.2.2.2)
  have Hend := Hlocal T ⟨hT0, le_rfl⟩
  refine ⟨Hmono, mul_nonneg Hend.2.2.2.1 Hend.2.2.2.2, ?_⟩
  have H := Hmono ⟨le_rfl, hT0⟩ ⟨hT0, le_rfl⟩ hT0
  exact H.trans (by simpa only [Y, restartShearTailProjectiveEntry, restartShearTailFlow, zero_add,
    restartFastShearProjectiveEntry] using Hfast.2)

end BianchiIX
