import BianchiIX.Dynamics.ShearRestartCommonExtension
import BianchiIX.Analysis.RadiusAmplitudeMeasurability

noncomputable section

namespace BianchiIX

open Set

def restartShearCommonLabelSet (ε a P : ℝ) : Set (ℝ × ℝ) :=
  {z | (0 < z.1 ∧ z.1 ≤ 2 * ε * a) ∧ (0 < z.2 ∧ z.2 ≤ 2 * ε * a) ∧ min z.1 z.2 ≤ a ^ P}

theorem measurableSet_restartShearCommonLabelSet (ε a P : ℝ) :
    MeasurableSet (restartShearCommonLabelSet ε a P) :=
  ((measurableSet_lt measurable_const measurable_fst).inter
    (measurableSet_le measurable_fst measurable_const)).inter
    (((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)).inter
      (measurableSet_le (measurable_fst.min measurable_snd) measurable_const))

/-- Both small-wall orderings form one jointly Borel family of actual returns and globally extended amplitudes. -/
theorem exists_restartShearReturn_common_extension_measurable :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
          ∀ ε : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 128) →
          let s := q / 2 * Real.log (1 / a)
          Measurable (fun p : restartShearCommonLabelSet ε a P × Icc a (2 * a) =>
            restartShearReturnState h s p.1.val.1 p.1.val.2 p.2) ∧
          ∀ i : Fin 3, (i = 1 ∨ i = 2) →
            Measurable (fun p : restartShearCommonLabelSet ε a P × ℝ =>
              restartShearAmplitudeExtension h s p.1.val.1 p.1.val.2 a i p.2) ∧
            Measurable (fun p : restartShearCommonLabelSet ε a P × ℝ =>
              deriv (restartShearAmplitudeExtension h s p.1.val.1 p.1.val.2 a i) p.2) := by
  obtain ⟨hR, hhR, HR⟩ := exists_restartShearReturn_common_regular
  obtain ⟨hC, hhC, HC⟩ := exists_restartShearReturn_common_cone
  obtain ⟨hA, hhA, HA⟩ := exists_restartShearReturn_common_bounds
  refine ⟨min hR (min hC hA), lt_min hhR (lt_min hhC hhA), ?_⟩
  intro h hh q D P hq hD hP
  have hh' := hh.2.trans (min_le_right _ _)
  obtain ⟨aR, haR, HAR⟩ := HR h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq hD hP
  obtain ⟨aC, haC, HAC⟩ := HC h ⟨hh.1, hh'.trans (min_le_left _ _)⟩ q D P hq hD hP
  obtain ⟨aA, haA, HAA⟩ := HA h ⟨hh.1, hh'.trans (min_le_right _ _)⟩ q D P hq hD hP
  refine ⟨min aR (min aC aA), lt_min haR (lt_min haC haA), ?_⟩
  intro a ha ε hε s
  have ha' := ha.2.trans (min_le_right _ _)
  let X := ↥(restartShearCommonLabelSet ε a P)
  let : StandardBorelSpace X := (measurableSet_restartShearCommonLabelSet ε a P).standardBorel
  let G : X → ℝ → CoreAngleState := fun z r => restartShearReturnState h s z.val.1 z.val.2 r
  have hmap : Continuous (fun p : X × Icc a (2 * a) => (p.1.val, (p.2 : ℝ))) := by
    dsimp only [X]
    fun_prop
  have hGc : Continuous (fun p : X × Icc a (2 * a) => G p.1 p.2) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    have hstate := (HAR a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε p.1.val.1 p.1.val.2
      hε p.1.property.1 p.1.property.2.1 p.1.property.2.2 p.2 p.2.property).2.1
    exact hstate.continuousAt.comp
      (f := fun p : X × Icc a (2 * a) => (p.1.val, (p.2 : ℝ))) (x := p) hmap.continuousAt
  have hGm (i : Fin 3) : Measurable (fun p : X × Icc a (2 * a) => G p.1 p.2 i) :=
    ((continuous_apply i).comp hGc).measurable
  have H (z : X) (r : ℝ) (hr : r ∈ Icc a (2 * a)) :=
    HAC a ⟨ha.1, ha'.trans (min_le_left _ _)⟩ ε z.val.1 z.val.2 hε
      z.property.1 z.property.2.1 z.property.2.2 r hr
  have Hpos (z : X) (r : ℝ) (hr : r ∈ Icc a (2 * a)) : 0 < G z r 1 ∧ 0 < G z r 2 := by
    obtain ⟨_, _, _, _, _, _, _, hu, hw, _⟩ := HAA a ⟨ha.1, ha'.trans (min_le_right _ _)⟩
      ε z.val.1 z.val.2 hε z.property.1 z.property.2.1 z.property.2.2 r hr
    exact ⟨hu, hw⟩
  have hGtwo (z : X) (r : ℝ) (hr : r ∈ Icc a (2 * a)) (i : Fin 3) :
      ContDiffAt ℝ 2 (fun t => G z t i) r := contDiffAt_pi.mp (H z r hr).1 i
  refine ⟨hGc.measurable, ?_⟩
  intro i hi
  have hpos (z : X) (r : ℝ) (hr : r ∈ Icc a (2 * a)) : 0 < G z r i := by
    rcases hi with rfl | rfl
    · exact (Hpos z r hr).1
    · exact (Hpos z r hr).2
  exact jointly_measurable_radiusAmplitudeExtension (by linarith only [ha.1] : a < 2 * a)
    (hGm 0) (hGm i) (fun z r hr => (hGtwo z r hr 0).of_le (by norm_num))
    (fun z r hr => (H z r hr).2.1)
    (fun z r hr => (hGtwo z r hr i).of_le (by norm_num)) hpos

end BianchiIX
