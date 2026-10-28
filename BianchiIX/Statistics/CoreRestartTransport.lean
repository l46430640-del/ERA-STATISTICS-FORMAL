import BianchiIX.Statistics.CoreRestartWitness
import BianchiIX.Statistics.PhysicalFutureAxes

noncomputable section

namespace BianchiIX

def coreRestartFrame (i : Fin 6) (w : CoreRestartData) : CoreRestartData :=
  (((axisFrame_comp w.1.1 i).choose, w.1.2), w.2)

theorem measurable_coreRestartFrame :
    Measurable (fun p : Fin 6 × CoreRestartData => coreRestartFrame p.1 p.2) := by
  have H : Measurable (fun p : Fin 6 × Fin 6 => (axisFrame_comp p.1 p.2).choose) :=
    measurable_of_countable _
  exact ((H.comp (measurable_snd.fst.fst.prodMk measurable_fst)).prodMk measurable_snd.fst.snd).prodMk
    measurable_snd.snd

theorem CoreRestartWitness.of_axisFrame {η σ Bcap : ℝ} {J : ℕ}
    {x : NormalizedState} {w : CoreRestartData} (i : Fin 6)
    (H : CoreRestartWitness η J σ Bcap ((axisFrame i).map x) w) :
    CoreRestartWitness η J σ Bcap x (coreRestartFrame i w) := by
  obtain ⟨ht, hdom, p, hp, hstat, ho⟩ := H
  have hdom' : w.1.2 ∈ normalizedMaxDomain x 0 := by rwa [(axisFrame i).maxDomain] at hdom
  refine ⟨ht, hdom', p, hp, hstat, ?_⟩
  rwa [(axisFrame i).maxCurve hdom', (axisFrame_comp w.1.1 i).choose_spec] at ho

def coreRestartDelay (s : ℝ) (w : CoreRestartData) : CoreRestartData :=
  ((w.1.1, w.1.2 + s), w.2)

theorem measurable_coreRestartDelay :
    Measurable (fun p : ℝ × CoreRestartData => coreRestartDelay p.1 p.2) := by
  exact (measurable_snd.fst.fst.prodMk (measurable_snd.fst.snd.add measurable_fst)).prodMk
    measurable_snd.snd

theorem CoreRestartWitness.of_forward {η σ Bcap s : ℝ} {J : ℕ}
    {x : NormalizedState} {w : CoreRestartData} (hc : stateConstraint x = 1) (hs : 0 ≤ s)
    (H : CoreRestartWitness η J σ Bcap (normalizedMaxCurve x 0 s) w) :
    CoreRestartWitness η J σ Bcap x (coreRestartDelay s w) := by
  obtain ⟨ht, _, p, hp, hstat, ho⟩ := H
  have hTs : 0 < w.1.2 + s := add_pos_of_pos_of_nonneg ht hs
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint hc 0 hTs.le
  have hshift := normalizedMaxCurve_shift (t := w.1.2)
    (by simpa only [zero_add] using normalizedMaxDomain_contains_Ici_of_constraint hc 0 hs) hdom
  simp only [zero_add] at hshift
  exact ⟨hTs, hdom, p, hp, hstat, by simpa only [coreRestartDelay, hshift] using ho⟩

end BianchiIX
