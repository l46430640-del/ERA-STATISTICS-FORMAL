import BianchiIX.Dynamics.RestartReturnExtension
import BianchiIX.Analysis.RadiusAmplitudeMeasurability

noncomputable section

namespace BianchiIX

open Set

def restartLabelSet (L r P : ℝ) : Set (ℝ × ℝ) :=
  {z | |z.1| ≤ L ∧ 0 < z.2 ∧ z.2 ≤ r ^ P}

theorem measurableSet_restartLabelSet (L r P : ℝ) : MeasurableSet (restartLabelSet L r P) :=
  (measurableSet_le (continuous_abs.comp continuous_fst).measurable measurable_const).inter
    ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const))

/-- The actual restart state and its extended amplitudes and slopes are jointly Borel in the labels. -/
theorem exists_restartReturn_extension_measurable :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∀ q P : ℝ, 3 < q → 4 < P →
        ∃ rstar : ℝ, 0 < rstar ∧ ∀ r ∈ Ioc (0 : ℝ) rstar,
          let s := q / 2 * Real.log (1 / r)
          Measurable (fun p : restartLabelSet L r P × Icc r (2 * r) =>
            restartReturnState h s p.1.val.1 p.1.val.2 p.2) ∧
            ∀ i : Fin 3, (i = 1 ∨ i = 2) →
              Measurable (fun p : restartLabelSet L r P × ℝ =>
                restartAmplitudeExtension h s p.1.val.1 p.1.val.2 r i p.2) ∧
              Measurable (fun p : restartLabelSet L r P × ℝ =>
                deriv (restartAmplitudeExtension h s p.1.val.1 p.1.val.2 r i) p.2) := by
  obtain ⟨hR, hhR, HR⟩ := exists_restartReturn_joint_regular
  obtain ⟨hC, hhC, HC⟩ := exists_restartReturn_cone
  refine ⟨min hR hC, lt_min hhR hhC, ?_⟩
  intro h hh L hL q P hq hP
  obtain ⟨rR, hrR, HRR⟩ := HR h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ L hL q P hq hP
  obtain ⟨rC, hrC, HRC⟩ := HC h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ L hL q P hq hP
  refine ⟨min rR rC, lt_min hrR hrC, ?_⟩
  intro r hr
  let s := q / 2 * Real.log (1 / r)
  let X := ↥(restartLabelSet L r P)
  let : StandardBorelSpace X := (measurableSet_restartLabelSet L r P).standardBorel
  let G : X → ℝ → CoreAngleState := fun z a => restartReturnState h s z.val.1 z.val.2 a
  have hmap : Continuous (fun p : X × Icc r (2 * r) => (p.1.val, (p.2 : ℝ))) := by
    dsimp only [X]
    fun_prop
  have hGc : Continuous (fun p : X × Icc r (2 * r) => G p.1 p.2) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    obtain ⟨_, _, hstate, _⟩ := HRR r ⟨hr.1, hr.2.trans (min_le_left _ _)⟩
      p.1.val.1 p.1.val.2 p.1.property.1 p.1.property.2 p.2 p.2.property
    exact hstate.continuousAt.comp
      (f := fun p : X × Icc r (2 * r) => (p.1.val, (p.2 : ℝ))) (x := p) hmap.continuousAt
  have hGm (i : Fin 3) : Measurable (fun p : X × Icc r (2 * r) => G p.1 p.2 i) :=
    ((continuous_apply i).comp hGc).measurable
  have H (z : X) (a : ℝ) (ha : a ∈ Icc r (2 * r)) := HRC r ⟨hr.1, hr.2.trans (min_le_right _ _)⟩
    z.val.1 z.val.2 z.property.1 z.property.2 a ha
  have hGtwo (z : X) (a : ℝ) (ha : a ∈ Icc r (2 * r)) (i : Fin 3) :
      ContDiffAt ℝ 2 (fun b => G z b i) a := contDiffAt_pi.mp (H z a ha).1 i
  refine ⟨hGc.measurable, ?_⟩
  intro i hi
  have hpos (z : X) (a : ℝ) (ha : a ∈ Icc r (2 * r)) : 0 < G z a i := by
    rcases hi with rfl | rfl
    · exact (H z a ha).2.1
    · exact (H z a ha).2.2.1
  exact jointly_measurable_radiusAmplitudeExtension (by linarith only [hr.1] : r < 2 * r)
    (hGm 0) (hGm i) (fun z a ha => (hGtwo z a ha 0).of_le (by norm_num))
    (fun z a ha => (H z a ha).2.2.2.2.1)
    (fun z a ha => (hGtwo z a ha i).of_le (by norm_num)) hpos

open scoped Classical in
/-- Zero extension off the valid labels gives measurable families on the ambient product space. -/
theorem exists_restartReturn_extension_ambient_measurable :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∀ q P : ℝ, 3 < q → 4 < P →
        ∃ rstar : ℝ, 0 < rstar ∧ ∀ r ∈ Ioc (0 : ℝ) rstar,
          let s := q / 2 * Real.log (1 / r)
          ∀ i : Fin 3, (i = 1 ∨ i = 2) →
            Measurable (fun p : (ℝ × ℝ) × ℝ => if p.1 ∈ restartLabelSet L r P then
              restartAmplitudeExtension h s p.1.1 p.1.2 r i p.2 else 0) ∧
            Measurable (fun p : (ℝ × ℝ) × ℝ => if p.1 ∈ restartLabelSet L r P then
              deriv (restartAmplitudeExtension h s p.1.1 p.1.2 r i) p.2 else 0) := by
  obtain ⟨hstar, hhstar, HH⟩ := exists_restartReturn_extension_measurable
  refine ⟨hstar, hhstar, ?_⟩
  intro h hh L hL q P hq hP
  obtain ⟨rstar, hrstar, HR⟩ := HH h hh L hL q P hq hP
  refine ⟨rstar, hrstar, ?_⟩
  intro r hr s i hi
  obtain ⟨hU, hdU⟩ := (HR r hr).2 i hi
  exact ⟨jointly_measurable_zero_extension
      (F := fun z k => restartAmplitudeExtension h s z.1 z.2 r i k)
      (measurableSet_restartLabelSet L r P) hU,
    jointly_measurable_zero_extension
      (F := fun z k => deriv (restartAmplitudeExtension h s z.1 z.2 r i) k)
      (measurableSet_restartLabelSet L r P) hdU⟩

end BianchiIX
