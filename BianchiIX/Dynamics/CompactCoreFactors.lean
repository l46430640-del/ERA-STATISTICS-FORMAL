import BianchiIX.Analysis.CoordinateFactor
import BianchiIX.Dynamics.CompactCoreBoundary

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The transverse factor obtained by division along the invariant wall hyperplane. -/
def compactCoreFactor (Y : CoreAngleState) (i : Fin 2) : ℝ :=
  coordinateFactor (fun Z => coreReturnState coreRadiusReturnTime Z i.succ) i.succ Y

theorem coordinateSegment_core_box {Y : CoreAngleState} {ε s : ℝ} (i : Fin 2)
    (hs : 0 ≤ s ∧ s ≤ 1) (hu : |Y 1| ≤ ε) (hw : |Y 2| ≤ ε) :
    coordinateSegment i.succ Y s 0 = Y 0 ∧
      |coordinateSegment i.succ Y s 1| ≤ ε ∧ |coordinateSegment i.succ Y s 2| ≤ ε := by
  have H (a : ℝ) : |s * a| ≤ |a| := by
    rw [abs_mul, abs_of_nonneg hs.1]
    exact mul_le_of_le_one_left (abs_nonneg _) hs.2
  fin_cases i
  · exact ⟨rfl, (H _).trans hu, hw⟩
  · exact ⟨rfl, hu, (H _).trans hw⟩

theorem compactCoreFactor_reference_value {k : ℝ} (hk : 1 < k) (i : Fin 2) :
    compactCoreFactor ![k, 0, 0] i =
      if i = 0 then Real.exp (-k * Real.arcosh k) else Real.exp (-4 * Real.arcosh k / k) := by
  have hc := (coreRadiusReturn_reference_regular hk).2.2.1
  have hzero : (![k, 0, 0] : CoreAngleState) i.succ = 0 := by fin_cases i <;> rfl
  rw [compactCoreFactor, coordinateFactor_of_zero _ _ hzero]
  have hd := (hasFDerivAt_apply (𝕜 := ℝ) i.succ (coreReturnState coreRadiusReturnTime ![k, 0, 0])).comp
    (![k, 0, 0] : CoreAngleState) (hc.differentiableAt (by norm_num)).hasFDerivAt
  simp only [Function.comp_def] at hd
  rw [hd.fderiv]
  fin_cases i
  · simpa using (coreRadiusReturn_reference_wall_derivative hk (Pi.single 1 1)).1
  · simpa using (coreRadiusReturn_reference_wall_derivative hk (Pi.single 2 1)).2

theorem compactCoreFactor_reference_bounds {k : ℝ} (hk : 1 < k) (i : Fin 2) :
    0 < compactCoreFactor ![k, 0, 0] i ∧ compactCoreFactor ![k, 0, 0] i < 1 := by
  rw [compactCoreFactor_reference_value hk i]
  have hL := Real.arcosh_pos hk
  have hk0 : 0 < k := by linarith only [hk]
  split_ifs
  · exact ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_neg_of_pos hk0) hL)⟩
  · exact ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (by norm_num) hL) hk0)⟩

theorem contDiffAt_compactCoreFactor_reference {k : ℝ} (hk : 1 < k) (i : Fin 2) :
    ContDiffAt ℝ 1 (fun Y => compactCoreFactor Y i) ![k, 0, 0] := by
  apply contDiffAt_coordinateFactor
  intro s _
  have hzero : (![k, 0, 0] : CoreAngleState) i.succ = 0 := by fin_cases i <;> rfl
  have hseg : coordinateSegment i.succ (![k, 0, 0] : CoreAngleState) s = ![k, 0, 0] := by
    simp only [coordinateSegment, hzero, mul_zero]
    exact Function.update_eq_self_iff.mpr hzero.symm
  rw [hseg]
  exact contDiffAt_pi.mp (coreRadiusReturn_reference_regular hk).2.2.1 i.succ

theorem eventually_compactCoreFactor_formula {Y : CoreAngleState} (i : Fin 2)
    (hseg : ∀ s ∈ Icc (0 : ℝ) 1, ∀ᶠ Z in 𝓝 (coordinateSegment i.succ Y s),
      coreRadiusReturnValid Z ∧ ContDiffAt ℝ 2 (coreReturnState coreRadiusReturnTime) Z) :
    ∀ᶠ Z in 𝓝 Y, coreReturnState coreRadiusReturnTime Z i.succ = Z i.succ * compactCoreFactor Z i := by
  have H : ∀ᶠ Z in 𝓝 Y, ∀ s ∈ Icc (0 : ℝ) 1,
      coreRadiusReturnValid (coordinateSegment i.succ Z s) ∧
        ContDiffAt ℝ 2 (coreReturnState coreRadiusReturnTime) (coordinateSegment i.succ Z s) := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro s hs
    have Hc : ContinuousAt (fun p : CoreAngleState × ℝ => coordinateSegment i.succ p.1 p.2) (Y, s) :=
      (contDiff_coordinateSegment i.succ 1).continuous.continuousAt
    exact Hc.eventually (hseg s hs)
  filter_upwards [H] with Z hZ
  have hc (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) := contDiffAt_pi.mp (hZ s hs).2 i.succ
  have hvalid : coreRadiusReturnValid (Function.update Z i.succ 0) := by
    simpa only [coordinateSegment, zero_mul] using (hZ 0 (by norm_num)).1
  have hzero := coreRadiusReturn_wall_zero hvalid i (Function.update_self _ _ _)
  have H' := coordinateFactor_identity hc
  rw [hzero, sub_zero] at H'
  exact H'

/-- Actual factorization and C1 factors on one fixed neighborhood, including both sides of zero walls. -/
theorem exists_compact_core_factorization :
    ∃ ε > (0 : ℝ), ∀ Y : CoreAngleState, (2 ≤ Y 0 ∧ Y 0 ≤ 6) → |Y 1| ≤ ε → |Y 2| ≤ ε →
      coreRadiusReturnValid Y ∧ ContDiffAt ℝ 2 (coreReturnState coreRadiusReturnTime) Y ∧
        ∀ i : Fin 2, ContDiffAt ℝ 1 (fun Z => compactCoreFactor Z i) Y ∧
          coreReturnState coreRadiusReturnTime Y i.succ = Y i.succ * compactCoreFactor Y i ∧
          (∀ᶠ Z in 𝓝 Y, coreReturnState coreRadiusReturnTime Z i.succ = Z i.succ * compactCoreFactor Z i) := by
  obtain ⟨ε, hε, _, _, hbox⟩ := exists_compact_core_return_two_germ
  refine ⟨ε, hε, ?_⟩
  intro Y hk hu hw
  have hY := hbox Y hk hu hw
  refine ⟨hY.1, hY.2.2.1, ?_⟩
  intro i
  have hseg (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) := coordinateSegment_core_box i hs hu hw
  have hf (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) := hbox (coordinateSegment i.succ Y s)
    (by rw [(hseg s hs).1]; exact hk) (hseg s hs).2.1 (hseg s hs).2.2
  have hc (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      ContDiffAt ℝ 2 (fun Z => coreReturnState coreRadiusReturnTime Z i.succ) (coordinateSegment i.succ Y s) :=
    contDiffAt_pi.mp (hf s hs).2.2.1 i.succ
  have hformula := eventually_compactCoreFactor_formula i (fun s hs =>
    ((hf s hs).2.2.2.2).mono fun _ h => ⟨h.1, h.2.2⟩)
  exact ⟨contDiffAt_coordinateFactor hc, hformula.self_of_nhds, hformula⟩

end BianchiIX
