import BianchiIX.Dynamics.TaubWeightedRadius
import BianchiIX.Dynamics.AxisSymmetry

noncomputable section

namespace BianchiIX

theorem NormalizedSymmetry.fixed_maxCurve_iff (A : NormalizedSymmetry)
    {x : NormalizedState} {t₀ t : ℝ} (ht : t ∈ normalizedMaxDomain x t₀) :
    A.map (normalizedMaxCurve x t₀ t) = normalizedMaxCurve x t₀ t ↔ A.map x = x := by
  constructor
  · intro heq
    have hAt : t ∈ normalizedMaxDomain (A.map x) t₀ := by rwa [A.maxDomain]
    calc
      A.map x = normalizedMaxCurve (normalizedMaxCurve (A.map x) t₀ t) t t₀ := by
        rw [normalizedMaxCurve_rebase hAt (initial_mem_normalizedMaxDomain _ _), normalizedMaxCurve_initial]
      _ = normalizedMaxCurve (normalizedMaxCurve x t₀ t) t t₀ := by rw [A.maxCurve ht, heq]
      _ = x := by rw [normalizedMaxCurve_rebase ht (initial_mem_normalizedMaxDomain _ _), normalizedMaxCurve_initial]
  · intro heq
    rw [← A.maxCurve ht, heq]

theorem normalizedTaubRadiusSq_eq_zero_iff (x : NormalizedState) :
    normalizedTaubRadiusSq x = 0 ↔ axisSwap x = x := by
  constructor
  · intro hr
    dsimp [normalizedTaubRadiusSq, taubRadiusSq] at hr
    have hs : x 1 = 0 := by nlinarith [sq_nonneg (x 3 - x 4)]
    have hw : x 3 = x 4 := by nlinarith [sq_nonneg (x 1)]
    ext i
    fin_cases i <;> simp [axisSwap, hs, hw]
  · intro heq
    have hs := congrFun heq 1
    have hw := congrFun heq 3
    change -x 1 = x 1 at hs
    change x 4 = x 3 at hw
    dsimp [normalizedTaubRadiusSq, taubRadiusSq]
    rw [hw]
    nlinarith only [hs]

theorem normalizedTaubRadiusSq_maxCurve_pos {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) (hr : 0 < normalizedTaubRadiusSq x) :
    0 < normalizedTaubRadiusSq (normalizedMaxCurve x t₀ t) := by
  apply lt_of_le_of_ne (taubRadiusSq_nonneg _ _ _)
  intro heq
  have hf := (normalizedTaubRadiusSq_eq_zero_iff _).mp heq.symm
  have hi := (NormalizedSymmetry.swap.fixed_maxCurve_iff ht).mp hf
  exact (ne_of_gt hr) ((normalizedTaubRadiusSq_eq_zero_iff _).mpr hi)

end BianchiIX
