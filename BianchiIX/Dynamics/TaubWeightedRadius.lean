import BianchiIX.Algebra.TaubApproach
import BianchiIX.Dynamics.Normalized
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section

namespace BianchiIX

open Set

def normalizedTaubRadiusSq (x : NormalizedState) : ℝ := taubRadiusSq (x 1) (x 3) (x 4)

def weightedTaubRadiusSq (x : NormalizedState) : ℝ :=
  normalizedTaubRadiusSq x * Real.exp (-8 * x 2)

theorem hasDerivAt_normalizedTaubRadiusSq {α : ℝ → NormalizedState} {t : ℝ}
    (hα : HasDerivAt α (normalizedField (α t)) t) :
    HasDerivAt (fun u => normalizedTaubRadiusSq (α u))
      (2 * taubRadiusHalfRate (α t 0) (α t 1) (α t 2) (α t 3) (α t 4)) t := by
  obtain ⟨_, hs, _, hb, hc⟩ := hasDerivAt_normalized_components hα
  convert! (hs.pow 2).add ((hb.sub hc).pow 2) using 1
  unfold taubRadiusHalfRate
  simp only [Pi.sub_apply]
  ring

theorem hasDerivAt_weightedTaubRadiusSq {α : ℝ → NormalizedState} {t : ℝ}
    (hα : HasDerivAt α (normalizedField (α t)) t) :
    HasDerivAt (fun u => weightedTaubRadiusSq (α u))
      ((2 * taubRadiusHalfRate (α t 0) (α t 1) (α t 2) (α t 3) (α t 4) -
        8 * normalizedTaubRadiusSq (α t) * rateOne (α t 0) (α t 1) * α t 2) * Real.exp (-8 * α t 2)) t := by
  have hn := (hasDerivAt_normalized_components hα).2.2.1
  convert! (hasDerivAt_normalizedTaubRadiusSq hα).mul ((hn.const_mul (-8)).exp) using 1
  ring

theorem weightedTaubRadiusSq_monotone {α : ℝ → NormalizedState} {a b : ℝ}
    (hα : ∀ t ∈ Icc a b, HasDerivAt α (normalizedField (α t)) t)
    (hc : ∀ t ∈ Icc a b, stateConstraint (α t) = 1)
    (hp : ∀ t ∈ Icc a b, α t 0 ≤ -1 / 2)
    (hn : ∀ t ∈ Icc a b, 0 ≤ α t 2)
    (hw : ∀ t ∈ Icc a b, (α t 2) ^ 2 + (α t 3) ^ 2 + (α t 4) ^ 2 ≤ 2) :
    MonotoneOn (fun t => weightedTaubRadiusSq (α t)) (Icc a b) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
    (HasDerivAt.continuousOn fun t ht => hasDerivAt_weightedTaubRadiusSq (hα t ht))
    (fun t ht => (hasDerivAt_weightedTaubRadiusSq (hα t (interior_subset ht))).hasDerivWithinAt)
  intro t ht
  have ht' := interior_subset ht
  have hr := taubRadiusHalfRate_lower (hc t ht') (hp t ht') (hn t ht') (hw t ht')
  have hnR := mul_nonneg (hn t ht') (taubRadiusSq_nonneg (α t 1) (α t 3) (α t 4))
  have hrate := mul_le_mul_of_nonneg_right (taub_negative_wall_rate (s := α t 1) (hp t ht')) hnR
  apply mul_nonneg _ (Real.exp_pos _).le
  change 0 ≤ 2 * taubRadiusHalfRate _ _ _ _ _ - 8 * taubRadiusSq _ _ _ * rateOne _ _ * α t 2
  nlinarith only [hr, hrate]

theorem taubRadiusSq_backward_bound {α : ℝ → NormalizedState} {a b h : ℝ}
    (hab : a ≤ b) (hh : h ≤ 1 / 16)
    (hmono : MonotoneOn (fun t => weightedTaubRadiusSq (α t)) (Icc a b))
    (hna : α a 2 ≤ h) (hnb : 0 ≤ α b 2) :
    normalizedTaubRadiusSq (α a) ≤ 2 * normalizedTaubRadiusSq (α b) := by
  have H := hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  have hn : -8 * α b 2 - (-8 * α a 2) ≤ 1 / 2 := by linarith only [hna, hnb, hh]
  have hexp : Real.exp (-8 * α b 2 - (-8 * α a 2)) ≤ 2 := by
    calc
      _ ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr hn
      _ ≤ 2 := by
        convert Real.exp_bound_div_one_sub_of_interval (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num) using 1
        norm_num
  have H' := (le_div_iff₀ (Real.exp_pos (-8 * α a 2))).mpr H
  change normalizedTaubRadiusSq (α a) ≤ normalizedTaubRadiusSq (α b) * Real.exp (-8 * α b 2) /
    Real.exp (-8 * α a 2) at H'
  rw [mul_div_assoc, ← Real.exp_sub] at H'
  exact H'.trans (by
    have := mul_le_mul_of_nonneg_left hexp (taubRadiusSq_nonneg (α b 1) (α b 3) (α b 4))
    simpa only [normalizedTaubRadiusSq, mul_comm] using this)

end BianchiIX
