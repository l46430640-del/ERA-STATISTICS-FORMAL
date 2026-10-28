import BianchiIX.Dynamics.PartialCoreDownwardCone
import BianchiIX.Dynamics.CoreConnectionBounds

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- Core coordinates and the physical exit coordinates define the same connection parameters on an open germ. -/
theorem partialCoreDownwardReturn_connectionParameters_eventuallyEq {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hR : coreRadius (y 0) (y 2) = k)
    (hV : 1 < y 2 ∨ (y 2 = 1 ∧ 1 ≤ y 0)) :
    let out := fun z => projectiveOriginalFlow z 0 (partialCoreDownwardReturnTime z)
    (fun z => coreExitConnectionParameters ![coreRadius (out z 0) (out z 2), out z 1, out z 3]) =ᶠ[𝓝 y]
      (fun z => coreExitConnectionParameters (partialCoreDownwardReturnState z)) := by
  intro out
  filter_upwards [(partialCoreDownwardReturn_regular hk hy hR hV).2.2.2.1] with z hz
  have hhit : out z 2 = 1 := hz.1.1.2.2.1
  apply congrArg coreExitConnectionParameters
  ext i
  fin_cases i
  · rfl
  · rfl
  · change out z 3 = out z 2 * out z 3
    rw [hhit, one_mul]

/-- The fixed downward return enters a finite regular connection on the same exact orbit. -/
theorem partialCoreDownwardReturn_connection_domain {k Z ε : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hR : coreRadius (y 0) (y 2) = k)
    (hV : 1 < y 2 ∨ (y 2 = 1 ∧ 1 ≤ y 0)) (hZ : 0 ≤ Z) (hkZ : 2 * Real.cosh Z ≤ k)
    (hz : projectiveCoreAngle y ≤ Z) (hε : 0 < ε ∧ ε ≤ 1 / 10000)
    (hu : 0 < y 1 ∧ y 1 ≤ ε / k) (hp : 0 < y 2 * y 3 ∧ y 2 * y 3 ≤ ε / k) :
    let T := partialCoreDownwardReturnTime y
    let out := projectiveOriginalFlow y 0 T
    let p := coreExitConnectionParameters (partialCoreDownwardReturnState y)
    out = connectionEntry (p 0) (p 1) (p 2) ∧
      (4 ≤ p 0 ∧ k / 2 ≤ p 0 ∧ p 0 < k) ∧
      (0 < p 1 ∧ p 1 ≤ ε / p 0) ∧ (0 < p 2 ∧ p 2 ≤ ε) ∧
      p 1 ≤ y 1 * Real.exp (-k / 12) ∧ p 2 ≤ y 2 * y 3 ∧
      phaseNorm (p 0 + 1) 1 = coreRadius (out 0) (out 2) ∧
      0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 T 0 ∧
      connectionReturnValid p ∧ ContDiffAt ℝ 2 connectionReturnTime p ∧
      ContDiffAt ℝ 2 connectionReturnState p ∧
      connectionReturnState p = projectiveOriginalFlow y 0 (T + connectionReturnTime p) := by
  intro T out p
  have hfirst := (partialCoreDownwardReturn_regular hk hy hR hV).1
  have HB := partialCoreDownwardReturn_bounds hk hy hR hV
  have hreg := HB.2.2
  have htm : T ∈ Icc 0 T := ⟨hfirst.1.1.le, le_rfl⟩
  have hr : coreRegion k out := (hreg T htm).2.1
  have hD := (coreRegion_clock_regular hk hy).1
  have hc := fromProjectiveState_constraint hD.ne'
  have hhit : out 2 = 1 := hfirst.1.2
  have hM : out 0 < 1 := HB.1
  have heq : p = ![-out 0, out 1, out 3] := coreExitConnectionParameters_of_exit hM hhit
  have hμ := core_exit_connection_radial_range hk hM (by simpa only [hhit] using hr.1)
  have hentry : out = connectionEntry (p 0) (p 1) (p 2) := by
    rw [heq]
    ext i
    fin_cases i <;> simp [connectionEntry, hhit]
  have hpos (i : Fin 3) (hi : 0 < y i.succ) : 0 < out i.succ := by
    apply normalized_projective_wall_pos (initial_mem_normalizedMaxDomain _ 0)
      (normalizedMaxDomain_contains_Ici_of_constraint hc 0 hfirst.1.1.le)
      (hreg 0 ⟨le_rfl, hfirst.1.1.le⟩).1 (hreg T htm).1 i
    change 0 < projectiveOriginalFlow y 0 0 i.succ
    rw [projectiveOriginalFlow_initial hD]
    exact hi
  have huout : 0 < out 1 := hpos 0 hu.1
  have hpout : 0 < out 3 := hpos 2 ((mul_pos_iff_of_pos_left (zero_lt_one.trans_le hy.2.1)).mp hp.1)
  have HC := partialCoreDownwardReturn_contraction hk hy hR hV hZ hkZ hz
  have huexp : y 1 * Real.exp (-k / 12) ≤ y 1 :=
    mul_le_of_le_one_right hu.1.le (Real.exp_le_one_iff.mpr (by linarith only [hk]))
  have hdomainU : 0 < p 1 ∧ p 1 ≤ ε / p 0 := by
    change 0 < out 1 ∧ out 1 ≤ ε / (p 0)
    refine ⟨huout, (HC.1.trans huexp).trans (hu.2.trans ?_)⟩
    rw [heq]
    exact div_le_div_of_nonneg_left hε.1.le
      (by simpa using lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4) hμ.1) hμ.2.2.le
  have hdomainP : 0 < p 2 ∧ p 2 ≤ ε := by
    change 0 < out 2 * out 3 ∧ out 2 * out 3 ≤ ε
    rw [hhit, one_mul]
    exact ⟨hpout, HC.2.trans (hp.2.trans (div_le_self hε.1.le (by linarith only [hk])))⟩
  have hμp : 4 ≤ p 0 ∧ k / 2 ≤ p 0 ∧ p 0 < k := by simpa only [heq, Matrix.cons_val_zero] using hμ
  have HR := connectionReturn_regular hμp.1
    ⟨hdomainU.1.le, hdomainU.2.trans (div_le_div_of_nonneg_right hε.2 (by linarith only [hμp.1]))⟩
    ⟨hdomainP.1, hdomainP.2.trans hε.2⟩
  refine ⟨hentry, hμp, hdomainU, hdomainP, HC.1, ?_, ?_, (hreg T htm).1,
    HR.1, HR.2.1, HR.2.2.1, ?_⟩
  · change out 2 * out 3 ≤ y 2 * y 3
    rw [hhit, one_mul]
    exact HC.2
  · apply coreExitConnectionParameters_phase
    exact lt_of_lt_of_le (by linarith only [hk] : 1 < 99 / 100 * k) (coreRegion_radius_bounds hk hr).1
  · have htc : 0 < connectionReturnTime p := HR.1.1.1.1
    have Hrestart := projectiveOriginalFlow_restart hD hfirst.1.1.le htc.le (hreg T htm).1
    change projectiveOriginalFlow (connectionEntry (p 0) (p 1) (p 2)) 0 (connectionReturnTime p) = _
    rw [← hentry]
    change projectiveOriginalFlow out 0 (connectionReturnTime p) =
      projectiveOriginalFlow y 0 (connectionReturnTime p + T) at Hrestart
    rwa [add_comm (connectionReturnTime p) T] at Hrestart

/-- Ordinary C2 regularity survives the composition with the long connection at the incoming boundary. -/
theorem partialCoreDownwardConnection_regular {k Z ε : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hR : coreRadius (y 0) (y 2) = k)
    (hV : 1 < y 2 ∨ (y 2 = 1 ∧ 1 ≤ y 0)) (hZ : 0 ≤ Z) (hkZ : 2 * Real.cosh Z ≤ k)
    (hz : projectiveCoreAngle y ≤ Z) (hε : 0 < ε ∧ ε ≤ 1 / 10000)
    (hu : 0 < y 1 ∧ y 1 ≤ ε / k) (hp : 0 < y 2 * y 3 ∧ y 2 * y 3 ≤ ε / k) :
    let p := fun x => coreExitConnectionParameters (partialCoreDownwardReturnState x)
    ContDiffAt ℝ 2 p y ∧
      ContDiffAt ℝ 2 (fun x => partialCoreDownwardReturnTime x + connectionReturnTime (p x)) y ∧
      ContDiffAt ℝ 2 (fun x => connectionReturnState (p x)) y := by
  intro p
  have HR := partialCoreDownwardReturn_regular hk hy hR hV
  obtain ⟨_, _, _, _, _, _, _, _, _, hct, hcs, _⟩ :=
    partialCoreDownwardReturn_connection_domain hk hy hR hV hZ hkZ hz hε hu hp
  have HB := (partialCoreDownwardReturn_bounds hk hy hR hV).2.2 _ ⟨HR.1.1.1.le, le_rfl⟩
  have hr := (coreRegion_radius_bounds hk HB.2.1).1
  have hf : 1 < partialCoreDownwardReturnState y 0 :=
    lt_of_lt_of_le (by linarith only [hk] : 1 < 99 / 100 * k) hr
  have hcP : ContDiffAt ℝ 2 p y := (contDiffAt_coreExitConnectionParameters 2 hf).comp y HR.2.2.1
  exact ⟨hcP, HR.2.1.add (ContDiffAt.comp (g := connectionReturnTime) (f := p) y hct hcP),
    ContDiffAt.comp (g := connectionReturnState) (f := p) y hcs hcP⟩

end BianchiIX
