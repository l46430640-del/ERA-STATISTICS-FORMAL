import BianchiIX.Dynamics.ExitClockWallFactor
import BianchiIX.Dynamics.ExitTailRefinedRadius

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The refined signed radius error and positive weak-wall growth of D.12 hold on the actual full tail. -/
theorem exists_terminal_exitClock_refined_radius {η : ℝ} (hη : 0 < η ∧ η < 1) {J : ℕ} (hJ : 1 ≤ J) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ α b u w : ℝ,
      (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ J → |u| + |w| ≤ b →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      let S := exitTailLength η α J
      coreTailValid h Y ∧ ∃ I : Set ℝ, IsOpen I ∧ Convex ℝ I ∧ Icc 0 (coreTailTime h Y) ⊆ I ∧
        (∀ t ∈ I, exitEntryRegular Y t) ∧ exitClockFlow I (Y, 0) = Y ∧
        ((fun Z => toExitTailState (coreTailState h Z)) =ᶠ[𝓝 Y] (fun Z => exitClockFlow I (Z, S))) ∧
        ∀ s ∈ Icc 0 S,
          HasDerivAt (fun r => exitClockFlow I (Y, r))
            (exitTailField (Real.exp (-s)) (exitClockFlow I (Y, s))) s ∧
          |exitClockFlow I (Y, s) 0 - Y 0| ≤ C * (|u| + b ^ 2 * s) ∧
          ((0 ≤ u ∧ 0 < w) → 0 < exitClockFlow I (Y, s) 2 ∧
            exitClockFlow I (Y, s) 2 ≤ w * Real.exp (α / (1 + α) * s)) ∧
          (u = 0 → HasDerivAt (fun r => exitClockFlow I (Y, r) 0)
            (-(exitClockFlow I (Y, s) 2) ^ 2 / exitClockFlow I (Y, s) 0) s) := by
  obtain ⟨εe, hεe, HE⟩ := exists_terminal_exitClock_family hη hJ
  obtain ⟨C, hC, εr, hεr, HD⟩ := exists_exitTail_refined_scale_bounds ⟨hη.1, hη.2.le⟩ hJ
  refine ⟨C, hC, min εe εr, lt_min hεe hεr, ?_⟩
  intro α b u w hα hb hsmall hw Y h S
  have he := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_left εe εr) (pow_nonneg hα.1.le J))
  have hr := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_right εe εr) (pow_nonneg hα.1.le J))
  obtain ⟨hvalid, I, hIo, hI, hcover, U, hUo, hYU, HR, hinit, hend, HF⟩ := HE α b u w hα hb he hw
  change coreTailValid h Y at hvalid
  have hT : 0 ≤ coreTailTime h Y := hvalid.1.1.1.le
  have hS : 0 ≤ S := exitTailLength_nonneg ⟨hη.1, hη.2.le⟩ hα J
  have hclock : exitEntryClock (Y, coreTailTime h Y) = S := by
    change -Real.log (coreTailState h Y 2) = S
    rw [coreTailState_active hvalid]
    change -Real.log (η * α ^ J) = exitTailLength η α J
    rw [← exp_neg_exitTailLength hη.1 hα.1 J, Real.log_exp, neg_neg]
  let β : ℝ → ExitTailState := fun s => exitClockFlow I (Y, s)
  have hβ0 : β 0 = Y := hinit
  have hR : β 0 0 = 2 + 2 * α := by rw [hβ0]; rfl
  have hwall : |β 0 1| + |β 0 2| ≤ b := by rw [hβ0]; exact hw
  have hβ (s : ℝ) (hs : s ∈ Icc 0 S) : HasDerivAt β (exitTailField (Real.exp (-s)) (β s)) s :=
    (HF s hs).2.1
  have HB := HD α b S β hα hb hr ⟨hS, le_rfl⟩ hR hwall hβ
  refine ⟨hvalid, I, hIo, hI, hcover, HR Y hYU, hinit, hend, ?_⟩
  intro s hs
  have hfactor (i : Fin 2) : β s i.succ = Y i.succ * Real.exp (exitClockLogMultiplier I i Y s) :=
    (exitClockFlow_eventually_wall_factor hIo hI hUo hYU HR hT hcover (hclock ▸ hs) i).self_of_nhds
  have Hstrong : β s 1 = u * Real.exp (exitClockLogMultiplier I 0 Y s) := hfactor 0
  have Hweak : β s 2 = w * Real.exp (exitClockLogMultiplier I 1 Y s) := hfactor 1
  refine ⟨hβ s hs, ?_, ?_, ?_⟩
  · simpa only [hβ0, show Y 1 = u from rfl] using (HB s hs).1
  · intro hpos
    have hpos0 : 0 ≤ β 0 1 ∧ 0 ≤ β 0 2 := by rw [hβ0]; exact ⟨hpos.1, hpos.2.le⟩
    refine ⟨?_, ?_⟩
    · change 0 < β s 2
      rw [Hweak]
      exact mul_pos hpos.2 (Real.exp_pos _)
    · simpa only [hβ0, show Y 2 = w from rfl] using (HB s hs).2 hpos0
  · intro hu
    have hz : β s 1 = 0 := by
      rw [Hstrong, hu, zero_mul]
    obtain ⟨t, ht, heq⟩ := exitEntryClock_interval_surjective hT
      (fun t ht => HR Y hYU t (hcover ht)) (hclock ▸ hs)
    have Hreg := HR Y hYU t (hcover ht)
    have hval := exitClockFlow_eq hI (HR Y hYU) (hcover ht)
    rw [heq] at hval
    have hgap : exitTailGap (β s 0) (Real.exp (-s)) ≠ 0 := by
      change exitTailGap (exitClockFlow I (Y, s) 0) (Real.exp (-s)) ≠ 0
      rw [hval, ← heq]
      change exitTailGap (coreRadius (exitEntryFlow (Y, t) 0) (exitEntryFlow (Y, t) 2))
        (Real.exp (-exitLogClock (exitEntryFlow (Y, t)))) ≠ 0
      rw [exp_neg_exitLogClock Hreg.2.2.2.2.1, exitTailGap_of_coreRadius Hreg.2.2.2.2.2.1]
      exact (sub_pos.mpr Hreg.2.2.2.2.2.1).ne'
    have HV := hasDerivAt_pi.mp (hβ s hs) 0
    change HasDerivAt (fun r => β r 0) (exitTailRadial (β s 0) (β s 1) (Real.exp (-s)) (β s 2)) s at HV
    rwa [hz, exitTailRadial_zero_strong _ hgap] at HV

end BianchiIX
