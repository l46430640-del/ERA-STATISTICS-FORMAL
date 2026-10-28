import BianchiIX.Analysis.CompactIntegralRegularity
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section

namespace BianchiIX

open Set MeasureTheory

def coordinateSegment {n : ℕ} (i : Fin n) (Y : Fin n → ℝ) (s : ℝ) : Fin n → ℝ :=
  Function.update Y i (s * Y i)

def coordinateFactor {n : ℕ} (f : (Fin n → ℝ) → ℝ) (i : Fin n) (Y : Fin n → ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, fderiv ℝ f (coordinateSegment i Y s) (Pi.single i 1)

theorem contDiff_coordinateSegment {n : ℕ} (i : Fin n) (m : WithTop ℕ∞) :
    ContDiff ℝ m (fun p : (Fin n → ℝ) × ℝ => coordinateSegment i p.1 p.2) := by
  apply contDiff_pi.mpr
  intro j
  by_cases h : j = i
  · subst j
    simp only [coordinateSegment, Function.update_self]
    fun_prop
  · simp only [coordinateSegment, Function.update_of_ne h]
    fun_prop

theorem hasDerivAt_coordinateSegment {n : ℕ} (i : Fin n) (Y : Fin n → ℝ) (s : ℝ) :
    HasDerivAt (coordinateSegment i Y) (Y i • Pi.single i 1) s := by
  convert! (hasDerivAt_update Y i (s * Y i)).scomp s ((hasDerivAt_id s).mul_const (Y i)) using 1
  simp only [one_mul]

/-- Integrating in one coordinate removes its zero without dividing by that coordinate. -/
theorem contDiffAt_coordinateFactor {n : ℕ} {f : (Fin n → ℝ) → ℝ} {i : Fin n} {Y : Fin n → ℝ}
    (hf : ∀ s ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 2 f (coordinateSegment i Y s)) :
    ContDiffAt ℝ 1 (coordinateFactor f i) Y := by
  apply contDiffAt_intervalIntegral_of_contDiffAt
    (F := fun p => fderiv ℝ f (coordinateSegment i p.1 p.2) (Pi.single i 1))
    (by norm_num : (0 : ℝ) ≤ 1)
  intro s hs
  have hD := ((hf s hs).fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).comp (Y, s)
    (contDiff_coordinateSegment i 1).contDiffAt
  exact hD.clm_apply contDiffAt_const

theorem coordinateFactor_identity {n : ℕ} {f : (Fin n → ℝ) → ℝ} {i : Fin n} {Y : Fin n → ℝ}
    (hf : ∀ s ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 2 f (coordinateSegment i Y s)) :
    f Y - f (Function.update Y i 0) = Y i * coordinateFactor f i Y := by
  have hd (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun t => f (coordinateSegment i Y t))
        (Y i * fderiv ℝ f (coordinateSegment i Y s) (Pi.single i 1)) s := by
    convert! ((hf s hs).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt s
      (hasDerivAt_coordinateSegment i Y s) using 1
    simp only [map_smul, smul_eq_mul]
  have hc : ContinuousOn (fun s => Y i * fderiv ℝ f (coordinateSegment i Y s) (Pi.single i 1))
      (Icc (0 : ℝ) 1) := by
    intro s hs
    have H := (hf s hs).continuousAt_fderiv (by norm_num)
    exact (continuousAt_const.mul
      ((H.comp (hasDerivAt_coordinateSegment i Y s).continuousAt).clm_apply continuousAt_const)).continuousWithinAt
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hd s (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs))
    (hc.intervalIntegrable_of_Icc (by norm_num))
  rw [intervalIntegral.integral_const_mul] at H
  simpa only [coordinateSegment, one_mul, Function.update_eq_self, zero_mul, coordinateFactor] using H.symm

theorem coordinateFactor_of_zero {n : ℕ} (f : (Fin n → ℝ) → ℝ) (i : Fin n) {Y : Fin n → ℝ}
    (hY : Y i = 0) : coordinateFactor f i Y = fderiv ℝ f Y (Pi.single i 1) := by
  have hseg (s : ℝ) : coordinateSegment i Y s = Y := by
    simp only [coordinateSegment, hY, mul_zero]
    exact Function.update_eq_self_iff.mpr hY.symm
  simp [coordinateFactor, hseg]

end BianchiIX
