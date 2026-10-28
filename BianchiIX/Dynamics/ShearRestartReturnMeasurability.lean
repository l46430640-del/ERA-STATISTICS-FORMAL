import BianchiIX.Dynamics.ShearRestartReturnExtension
import BianchiIX.Analysis.RadiusAmplitudeMeasurability

noncomputable section

namespace BianchiIX

open Set

def restartShearLabelSet (ε a P : ℝ) : Set (ℝ × ℝ) :=
  {z | (0 < z.1 ∧ z.1 ≤ 2 * ε * a) ∧ (0 < z.2 ∧ z.2 ≤ 2 * ε * a) ∧ z.2 ≤ a ^ P}

theorem measurableSet_restartShearLabelSet (ε a P : ℝ) :
    MeasurableSet (restartShearLabelSet ε a P) :=
  ((measurableSet_lt measurable_const measurable_fst).inter
    (measurableSet_le measurable_fst measurable_const)).inter
    (((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)).inter
      (measurableSet_le measurable_snd measurable_const))

/-- The exact shear return and its extended amplitudes and slopes are jointly Borel across the active-wall boundary. -/
theorem exists_restartShearReturn_extension_measurable :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
        ∀ ε : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
          let s := q / 2 * Real.log (1 / a)
          Measurable (fun p : restartShearLabelSet ε a P × Icc a (2 * a) =>
            restartShearReturnState h s p.1.val.1 p.1.val.2 p.2) ∧
            ∀ i : Fin 3, (i = 1 ∨ i = 2) →
              Measurable (fun p : restartShearLabelSet ε a P × ℝ =>
                restartShearAmplitudeExtension h s p.1.val.1 p.1.val.2 a i p.2) ∧
              Measurable (fun p : restartShearLabelSet ε a P × ℝ =>
                deriv (restartShearAmplitudeExtension h s p.1.val.1 p.1.val.2 a i) p.2) := by
  obtain ⟨hR, hhR, HR⟩ := exists_restartShearReturn_all_active_joint_regular
  obtain ⟨hC, hhC, HC⟩ := exists_restartShearReturn_all_active_cone
  obtain ⟨hA, hhA, HA⟩ := exists_restartShearReturn_all_active_output_bounds
  refine ⟨min hR (min hC hA), lt_min hhR (lt_min hhC hhA), ?_⟩
  intro h hh q P hq hP
  have hh' := hh.2.trans (min_le_right _ _)
  obtain ⟨aR, haR, HaR⟩ := HR h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q P hq hP
  obtain ⟨aC, haC, HaC⟩ := HC h ⟨hh.1, hh'.trans (min_le_left _ _)⟩ q P hq hP
  obtain ⟨aA, haA, HaA⟩ := HA h ⟨hh.1, hh'.trans (min_le_right _ _)⟩ q P hq hP
  refine ⟨min aR (min aC aA), lt_min haR (lt_min haC haA), ?_⟩
  intro a ha ε hε s
  have ha' := ha.2.trans (min_le_right _ _)
  let X := ↥(restartShearLabelSet ε a P)
  let : StandardBorelSpace X := (measurableSet_restartShearLabelSet ε a P).standardBorel
  let G : X → ℝ → CoreAngleState := fun z r => restartShearReturnState h s z.val.1 z.val.2 r
  have hmap : Continuous (fun p : X × Icc a (2 * a) => (p.1.val, (p.2 : ℝ))) := by
    dsimp only [X]
    fun_prop
  have hGc : Continuous (fun p : X × Icc a (2 * a) => G p.1 p.2) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    have hstate := (HaR a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε p.1.val.1 p.1.val.2
      hε p.1.property.1 p.1.property.2.1 p.1.property.2.2 p.2 p.2.property).2.1
    exact hstate.continuousAt.comp
      (f := fun p : X × Icc a (2 * a) => (p.1.val, (p.2 : ℝ))) (x := p) hmap.continuousAt
  have hGm (i : Fin 3) : Measurable (fun p : X × Icc a (2 * a) => G p.1 p.2 i) :=
    ((continuous_apply i).comp hGc).measurable
  have H (z : X) (r : ℝ) (hr : r ∈ Icc a (2 * a)) :=
    HaC a ⟨ha.1, ha'.trans (min_le_left _ _)⟩ ε z.val.1 z.val.2 hε
      z.property.1 z.property.2.1 z.property.2.2 r hr
  have Hpos (z : X) (r : ℝ) (hr : r ∈ Icc a (2 * a)) :=
    HaA a ⟨ha.1, ha'.trans (min_le_right _ _)⟩ ε z.val.1 z.val.2 hε
      z.property.1 z.property.2.1 z.property.2.2 r hr
  have hGtwo (z : X) (r : ℝ) (hr : r ∈ Icc a (2 * a)) (i : Fin 3) :
      ContDiffAt ℝ 2 (fun t => G z t i) r := contDiffAt_pi.mp (H z r hr).1 i
  refine ⟨hGc.measurable, ?_⟩
  intro i hi
  have hpos (z : X) (r : ℝ) (hr : r ∈ Icc a (2 * a)) : 0 < G z r i := by
    rcases hi with rfl | rfl
    · exact (Hpos z r hr).2.2.2.2.1
    · exact (Hpos z r hr).2.2.2.2.2.1
  exact jointly_measurable_radiusAmplitudeExtension (by linarith only [ha.1] : a < 2 * a)
    (hGm 0) (hGm i) (fun z r hr => (hGtwo z r hr 0).of_le (by norm_num))
    (fun z r hr => (H z r hr).2.1)
    (fun z r hr => (hGtwo z r hr i).of_le (by norm_num)) hpos

open scoped Classical in
/-- Zero extension gives Borel amplitude families on the ambient weak-wall label space. -/
theorem exists_restartShearReturn_extension_ambient_measurable :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
        ∀ ε : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
          let s := q / 2 * Real.log (1 / a)
          ∀ i : Fin 3, (i = 1 ∨ i = 2) →
            Measurable (fun p : (ℝ × ℝ) × ℝ => if p.1 ∈ restartShearLabelSet ε a P then
              restartShearAmplitudeExtension h s p.1.1 p.1.2 a i p.2 else 0) ∧
            Measurable (fun p : (ℝ × ℝ) × ℝ => if p.1 ∈ restartShearLabelSet ε a P then
              deriv (restartShearAmplitudeExtension h s p.1.1 p.1.2 a i) p.2 else 0) := by
  obtain ⟨hstar, hhstar, HH⟩ := exists_restartShearReturn_extension_measurable
  refine ⟨hstar, hhstar, ?_⟩
  intro h hh q P hq hP
  obtain ⟨astar, hastar, Ha⟩ := HH h hh q P hq hP
  refine ⟨astar, hastar, ?_⟩
  intro a ha ε hε s i hi
  obtain ⟨hU, hdU⟩ := (Ha a ha ε hε).2 i hi
  exact ⟨jointly_measurable_zero_extension
      (F := fun z k => restartShearAmplitudeExtension h s z.1 z.2 a i k)
      (measurableSet_restartShearLabelSet ε a P) hU,
    jointly_measurable_zero_extension
      (F := fun z k => deriv (restartShearAmplitudeExtension h s z.1 z.2 a i) k)
      (measurableSet_restartShearLabelSet ε a P) hdU⟩

end BianchiIX
