import BianchiIX.Dynamics.CoreTailMultipliers

noncomputable section

namespace BianchiIX

open Set MeasureTheory

def coreTailWeakEnergyIntegrand (p : CoreAngleState × ℝ) : ℝ :=
  2 * normalizedProjectiveRate (fromProjectiveState (coreTailEntry p.1)) 0 p.2 *
    (projectiveOriginalFlow (coreTailEntry p.1) 0 p.2 0 - 1) *
    (normalizedProjectiveWallMultiplier (fromProjectiveState (coreTailEntry p.1)) p.2 2) ^ 2

def coreTailWeakEnergyCoefficient (η : ℝ) (Y : CoreAngleState) : ℝ :=
  ∫ t in 0..coreTailTime η Y, coreTailWeakEnergyIntegrand (Y, t)

theorem contDiffAt_coreTailWeakEnergyIntegrand_two {η t : ℝ} {Y : CoreAngleState}
    (hk : 1 < Y 0) (H : coreTailValid η Y) (ht : t ∈ Icc 0 (coreTailTime η Y)) :
    ContDiffAt ℝ 2 coreTailWeakEnergyIntegrand (Y, t) := by
  let c := fun Z => fromProjectiveState (coreTailEntry Z)
  have hD := coreTailValid_denom_pos H
  have hc : ContDiffAt ℝ 2 c Y :=
    (contDiffAt_fromProjectiveState 2 hD.ne').comp Y (contDiffAt_coreTailEntry 2 hk)
  have hp : ContDiffAt ℝ 2 (fun p : CoreAngleState × ℝ => (c p.1, p.2)) (Y, t) :=
    (hc.comp (Y, t) contDiffAt_fst).prodMk contDiffAt_snd
  have hn := (contDiffAt_normalizedMaxCurve_two (H.2.1 t ht).1).comp (Y, t)
    (g := fun p : NormalizedState × ℝ => normalizedMaxCurve p.1 0 p.2)
    (f := fun p : CoreAngleState × ℝ => (c p.1, p.2)) hp
  have ha : ContDiffAt ℝ 2 (fun p : CoreAngleState × ℝ => normalizedProjectiveRate (c p.1) 0 p.2) (Y, t) :=
    contDiffAt_const.add (contDiffAt_pi.mp hn 0)
  have hy : ContDiffAt ℝ 2 (fun p : CoreAngleState × ℝ => projectiveOriginalFlow (coreTailEntry p.1) 0 p.2) (Y, t) :=
    (contDiffAt_toProjectiveState 2 (H.2.1 t ht).2.ne').comp (Y, t)
      (g := toProjectiveState) (f := fun p : CoreAngleState × ℝ => normalizedMaxCurve (c p.1) 0 p.2) hn
  have hb : ContDiffAt ℝ 2 (fun p : CoreAngleState × ℝ => normalizedProjectiveWallMultiplier (c p.1) p.2 2) (Y, t) :=
    (contDiffAt_normalizedProjectiveWallMultiplier_two
    (c := fun p : CoreAngleState × ℝ => c p.1) (τ := fun p => p.2) (Y := (Y, t))
    (hc.comp (Y, t) contDiffAt_fst) contDiffAt_snd ht.1
    (fun s hs => (H.2.1 s ⟨hs.1, hs.2.trans ht.2⟩).1)
    (fromProjectiveState_clock_pos hD) (H.2.1 t ht).2 2).1
  exact ((contDiffAt_const.mul ha).mul ((contDiffAt_pi.mp hy 0).sub contDiffAt_const)).mul (hb.pow 2)

theorem contDiffAt_coreTailWeakEnergyCoefficient_two {η : ℝ} {Y : CoreAngleState}
    (hk : 1 < Y 0) (H : coreTailValid η Y) (hT : ContDiffAt ℝ 2 (coreTailTime η) Y) :
    ContDiffAt ℝ 2 (coreTailWeakEnergyCoefficient η) Y :=
  contDiffAt_moving_intervalIntegral_two hT H.1.1.1.le
    (fun _ ht => contDiffAt_coreTailWeakEnergyIntegrand_two hk H ht)

/-- On the zero strong-wall plane, the exact finite-tail energy retains the initial weak-wall square. -/
theorem coreTail_weak_energy_factorization {η : ℝ} {Y : CoreAngleState}
    (hk : 1 < Y 0) (H : coreTailValid η Y) (hu : Y 1 = 0) :
    coreRadius (coreTailState η Y 0) η ^ 2 =
      (Y 0) ^ 2 + (Y 2) ^ 2 * coreTailWeakEnergyCoefficient η Y := by
  let x := fromProjectiveState (coreTailEntry Y)
  let T := coreTailTime η Y
  let Z := projectiveOriginalFlow (coreTailEntry Y) 0
  let a := normalizedProjectiveRate x 0
  let B := fun t => normalizedProjectiveWallMultiplier x t 2
  have hD := coreTailValid_denom_pos H
  have hT : 0 ≤ T := H.1.1.1.le
  have hinit : Z 0 = coreTailEntry Y := projectiveOriginalFlow_initial hD 0
  have hZ (t : ℝ) (ht : t ∈ Icc 0 T) : HasDerivAt Z (a t • projectiveField (Z t)) t :=
    hasDerivAt_toProjectiveState_normalized (hasDerivAt_normalizedMaxCurve (H.2.1 t ht).1)
      (H.2.1 t ht).2.ne' ((normalizedMaxCurve_constraint (H.2.1 t ht).1).trans
        (fromProjectiveState_constraint hD.ne'))
  have hfactor (t : ℝ) (ht : t ∈ Icc 0 T) (i : Fin 3) :
      Z t i.succ = coreTailEntry Y i.succ * normalizedProjectiveWallMultiplier x t i := by
    have HF := normalizedProjectiveWallMultiplier_formula (H.2.1 t ht).1
      (fromProjectiveState_clock_pos hD) (H.2.1 t ht).2 i
    rw [toProjectiveState_fromProjectiveState hD.ne'] at HF
    exact HF
  have hU (t : ℝ) (ht : t ∈ Icc 0 T) : Z t 1 = 0 := by
    have HF := hfactor t ht 0
    change Z t 1 = Y 1 * _ at HF
    simpa only [hu, zero_mul] using HF
  have hW (t : ℝ) (ht : t ∈ Icc 0 T) : Z t 3 = Y 2 * B t := hfactor t ht 2
  have hd (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivAt (fun s => coreEnergy (Z s 0) (Z s 2))
        ((Y 2) ^ 2 * coreTailWeakEnergyIntegrand (Y, t)) t := by
    convert! (((hasDerivAt_pi.mp (hZ t ht) 0).sub_const 1).pow 2).add
      ((hasDerivAt_pi.mp (hZ t ht) 2).pow 2) using 1
    change (Y 2) ^ 2 * (2 * a t * (Z t 0 - 1) * B t ^ 2) =
      2 * (Z t 0 - 1) ^ (2 - 1) * (a t * phaseVelocity (Z t 0) (Z t 1) (Z t 2) (Z t 3)) +
        2 * (Z t 2) ^ (2 - 1) * (a t * activeVelocity (Z t 0) (Z t 1) (Z t 2) (Z t 3))
    rw [hU t ht, hW t ht]
    unfold phaseVelocity activeVelocity coupling
    ring
  have hic : ContinuousOn (fun t => coreTailWeakEnergyIntegrand (Y, t)) (Icc 0 T) := by
    intro t ht
    exact ((contDiffAt_coreTailWeakEnergyIntegrand_two hk H ht).continuousAt.comp
      (by fun_prop : ContinuousAt (fun s : ℝ => (Y, s)) t)).continuousWithinAt
  have hi : IntervalIntegrable (fun t => coreTailWeakEnergyIntegrand (Y, t)) volume 0 T :=
    hic.intervalIntegrable_of_Icc hT
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (uIcc_of_le hT ▸ ht)) (hi.const_mul ((Y 2) ^ 2))
  rw [intervalIntegral.integral_const_mul, hinit] at he
  have he0 : coreEnergy (coreTailEntry Y 0) (coreTailEntry Y 2) = (Y 0) ^ 2 := by
    have hs := Real.sq_sqrt (show 0 ≤ (Y 0) ^ 2 - 1 by nlinarith only [hk])
    dsimp [coreEnergy, coreTailEntry]
    nlinarith only [hs]
  rw [he0] at he
  change (Y 2) ^ 2 * coreTailWeakEnergyCoefficient η Y =
    coreEnergy (coreTailState η Y 0) (coreTailState η Y 2) - (Y 0) ^ 2 at he
  rw [coreTailState_active H] at he
  rw [coreRadius_sq]
  linarith only [he]

end BianchiIX
