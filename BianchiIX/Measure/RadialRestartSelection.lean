import BianchiIX.Measure.RestartRadialPartition
import BianchiIX.Measure.AngularRestartChoice
import BianchiIX.Measure.ShearRestartChoice

noncomputable section

namespace BianchiIX

open Set MeasureTheory

def radialRestartParameter (k : Bool ⊕ Bool) (z : SectionCoordinates) : (ℝ × ℝ) × ℝ :=
  match k with
  | Sum.inl neg => ((if neg then (z 2, z 1) else (z 1, z 2)), z 0)
  | Sum.inr _ => ((z 1, z 2), z 0)

def radialRestartParameterDomain (a ε P : ℝ) : Bool ⊕ Bool → Set ((ℝ × ℝ) × ℝ)
  | Sum.inl _ => shearRestartParameterDomain ε a P
  | Sum.inr _ => angularRestartParameterDomain a (1 / ε) P

def radialRestartChart : Bool ⊕ Bool → ((ℝ × ℝ) × ℝ) → SectionCoordinates
  | Sum.inl neg => shearRestartChart neg
  | Sum.inr other => angularRestartChart other

def radialRestartData (h s a ε : ℝ) : Bool ⊕ Bool → ((ℝ × ℝ) × ℝ) → CoreRestartData
  | Sum.inl neg => shearRestartData h s a neg
  | Sum.inr other => angularRestartData h s a (1 / ε) other

theorem coreRestartWitness_reflected_entry {h T B η σ Bcap : ℝ} {J : ℕ}
    {y : SectionCoordinates} {Z : CoreAngleState} (ht : 0 < T)
    (hdom : T ∈ normalizedMaxDomain (mainWallChart h y) 0)
    (ho : coreRadiusEntry Z = projectiveReflection
      (toProjectiveState (normalizedMaxCurve (mainWallChart h y) 0 T)))
    (p : eraSurvivorDomain η J σ Bcap) (hp : p.val = (B, Z))
    (hs : EraStatistics (EraSurvivor.digits p) (EraSurvivor.phase p)) (o : Bool) :
    CoreRestartWitness η J σ Bcap (mainWallChart h (if o then mainWallReflection y else y))
      ((if o then 0 else 3, T), (B, Z)) := by
  cases o
  · refine ⟨ht, hdom, p, hp, hs, ?_⟩
    change coreRadiusEntry p.val.2 = toProjectiveState (axisSwap _)
    rw [toProjectiveState_axisSwap, hp]
    exact ho
  · refine ⟨ht, ?_, p, hp, hs, ?_⟩
    · change T ∈ normalizedMaxDomain (mainWallChart h (mainWallReflection y)) 0
      rwa [normalizedMaxDomain_mainWallReflection]
    · change coreRadiusEntry p.val.2 = toProjectiveState
        (normalizedMaxCurve (mainWallChart h (mainWallReflection y)) 0 T)
      rw [normalizedMaxCurve_mainWallReflection hdom, toProjectiveState_axisSwap, hp]
      exact ho

theorem radialRestartChart_parameter (k : Bool ⊕ Bool) (z : SectionCoordinates) :
    radialRestartChart k (radialRestartParameter k z) = radialPieceMap k z := by
  rcases k with neg | other
  · cases neg <;> ext i <;> fin_cases i <;>
      simp [radialRestartChart, radialRestartParameter, shearRestartChart, radialPieceMap,
        signedShearLogCoordinates, mainWallReflection]
  · cases other <;> ext i <;> fin_cases i <;>
      simp [radialRestartChart, radialRestartParameter, angularRestartChart, radialPieceMap,
        orderedAngularLogCoordinates, scaledAngularLogCoordinates, mainWallReflection]

theorem radialRestartData_output (h q d ε : ℝ) (i : RadialPieceIndex) (z : SectionCoordinates) :
    (radialRestartData h (q / 2 * Real.log (1 / dyadicScale d i.2)) (dyadicScale d i.2) ε i.1
      (radialRestartParameter i.1 z)).2 = restartRadialOutput h q d ε i z := by
  rcases i with ⟨neg | other, j⟩ <;> rfl

theorem radialRestartParameter_selected {h q d ε P η σ Bcap : ℝ} {J : ℕ}
    {i : RadialPieceIndex} {z : SectionCoordinates} (hz : z ∈ radialPieceDomain d ε i)
    (hn : z ∉ restartRadialFailureFamily h q d ε P η J σ Bcap i) :
    radialRestartParameter i.1 z ∈ radialRestartParameterDomain (dyadicScale d i.2) ε P i.1 := by
  have hr : z 0 ∈ Icc (dyadicScale d i.2) (2 * dyadicScale d i.2) := by
    rcases i with ⟨neg | other, j⟩ <;> exact ⟨hz.2.2.1.1.le, hz.2.2.1.2.le⟩
  rcases i with ⟨neg | other, j⟩
  · cases neg <;> exact ⟨by by_contra hl; exact hn ⟨hr, Or.inl hl⟩, hr⟩
  · exact ⟨by by_contra hl; exact hn ⟨hr, Or.inl hl⟩, hr⟩

/-- Selection only uses the successful parts of the prescribed disjoint radial pieces. -/
theorem exists_measurable_radial_restart {h q d ε P η σ Bcap : ℝ} {J : ℕ}
    (hd : 0 < d) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hF : ∀ i, MeasurableSet (restartRadialFailureFamily h q d ε P η J σ Bcap i))
    (hG : ∀ i : RadialPieceIndex, Measurable
      ((radialRestartParameterDomain (dyadicScale d i.2) ε P i.1).domRestrict
        (radialRestartData h (q / 2 * Real.log (1 / dyadicScale d i.2)) (dyadicScale d i.2) ε i.1))) :
    ∃ W : SectionCoordinates → CoreRestartData, Measurable W ∧
      ∀ y ∈ mainWallOpenSection d \ radialFailureSet d ε (restartRadialFailureFamily h q d ε P η J σ Bcap),
        ∃ i : RadialPieceIndex, ∃ z ∈ radialPieceDomain d ε i,
          z ∉ restartRadialFailureFamily h q d ε P η J σ Bcap i ∧ radialPieceMap i.1 z = y ∧
          W y = radialRestartData h (q / 2 * Real.log (1 / dyadicScale d i.2)) (dyadicScale d i.2) ε i.1
            (radialRestartParameter i.1 z) := by
  have Hext (i : RadialPieceIndex) : ∃ f : SectionCoordinates → CoreRestartData, Measurable f ∧
      ∀ p ∈ radialRestartParameterDomain (dyadicScale d i.2) ε P i.1,
        f (radialRestartChart i.1 p) =
          radialRestartData h (q / 2 * Real.log (1 / dyadicScale d i.2)) (dyadicScale d i.2) ε i.1 p := by
    apply exists_measurable_chart_extension (hG := hG i)
    · rcases i with ⟨neg | other, j⟩
      · exact measurableSet_shearRestartParameterDomain _ _ _
      · exact measurableSet_angularRestartParameterDomain _ _ _
    · rcases i with ⟨neg | other, j⟩
      · exact continuousOn_shearRestartChart _ _ _ _
      · exact continuousOn_angularRestartChart (dyadicScale_pos hd j) _
    · rcases i with ⟨neg | other, j⟩
      · exact injOn_shearRestartChart _ _ _ _
      · exact injOn_angularRestartChart (dyadicScale_pos hd j) _
  choose f hfm hfeq using Hext
  let F := restartRadialFailureFamily h q d ε P η J σ Bcap
  let S := fun i => radialFailurePiece d ε (fun j => (F j)ᶜ) i
  obtain ⟨W, hW, HW⟩ := exists_measurable_countable_selection S f
    (fun i => measurableSet_radialFailurePiece hd (fun j => (hF j).compl) i) hfm
  refine ⟨W, hW, ?_⟩
  intro y hy
  have hcover : y ∈ ⋃ i, S i := by
    obtain ⟨i, ⟨⟨z, hz, heq⟩, hn⟩, _⟩ := radialFailureSet_complement hd hε hε1 F hy
    rw [← heq, radialPieceInverse_map hd hz] at hn
    exact mem_iUnion.mpr ⟨i, z, ⟨hz, hn⟩, heq⟩
  obtain ⟨i, ⟨z, ⟨hz, hn⟩, rfl⟩, hval⟩ := HW y hcover
  refine ⟨i, z, hz, hn, rfl, hval.trans ?_⟩
  rw [← radialRestartChart_parameter]
  exact hfeq i _ (radialRestartParameter_selected hz hn)

end BianchiIX
