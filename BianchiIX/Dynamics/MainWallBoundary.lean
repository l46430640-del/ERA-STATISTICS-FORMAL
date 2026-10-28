import BianchiIX.Dynamics.MainWallChart
import BianchiIX.Dynamics.TaubWeightedRadius

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

def mainWallBoundary (h : ℝ) : NormalizedState := ![-Real.sqrt (1 - h ^ 2), 0, h, 0, 0]

/-- On a fixed wall section, vanishing transverse radius and weak walls determine the boundary point. -/
theorem tendsto_mainWall_boundary {α : Type*} {l : Filter α} {h : ℝ} {z : α → NormalizedState}
    (hchart : ∀ a, ∃ y, mainWallChart h y = z a)
    (hr : Tendsto (fun a => normalizedTaubRadiusSq (z a)) l (𝓝 0))
    (hb : Tendsto (fun a => z a 3) l (𝓝 0))
    (hw : Tendsto (fun a => z a 4) l (𝓝 0)) :
    Tendsto z l (𝓝 (mainWallBoundary h)) := by
  have hs : Tendsto (fun a => z a 1) l (𝓝 0) := by
    apply squeeze_zero_norm (a := fun a => Real.sqrt (normalizedTaubRadiusSq (z a)))
    · intro a
      rw [Real.norm_eq_abs]
      apply (Real.le_sqrt (abs_nonneg _) (taubRadiusSq_nonneg _ _ _)).mpr
      dsimp [normalizedTaubRadiusSq, taubRadiusSq]
      nlinarith only [sq_abs (z a 1), sq_nonneg (z a 3 - z a 4)]
    · simpa only [Function.comp_def, Real.sqrt_zero] using Real.continuous_sqrt.continuousAt.tendsto.comp hr
  have hcurv : Tendsto (fun a => curvature h (z a 3) (z a 4)) l (𝓝 (h ^ 2)) := by
    have Hconst : Tendsto (fun _ : α => h ^ 2) l (𝓝 (h ^ 2)) := tendsto_const_nhds
    have H := ((Hconst.add (hb.pow 2)).add (hw.pow 2)).sub
      (((hb.const_mul h).add (hb.mul hw) |>.add (hw.mul_const h)).const_mul 2)
    simpa only [curvature, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, add_zero, sub_zero] using H
  have hp : Tendsto (fun a => z a 0) l (𝓝 (-Real.sqrt (1 - h ^ 2))) := by
    have H := Real.continuous_sqrt.continuousAt.tendsto.comp ((hs.pow 2).const_sub 1 |>.sub hcurv)
    have heq (a : α) : z a 0 = -Real.sqrt (1 - z a 1 ^ 2 - curvature h (z a 3) (z a 4)) := by
      obtain ⟨y, hy⟩ := hchart a
      rw [← hy]
      rfl
    simpa only [heq, Function.comp_def, zero_pow (by decide : 2 ≠ 0), sub_zero] using H.neg
  apply tendsto_pi_nhds.mpr
  intro i
  fin_cases i
  · exact hp
  · exact hs
  · have heq (a : α) : z a 2 = h := by
      obtain ⟨y, hy⟩ := hchart a
      rw [← hy]
      rfl
    change Tendsto (fun a => z a 2) l (𝓝 h)
    simpa only [heq] using (tendsto_const_nhds : Tendsto (fun _ : α => h) l (𝓝 h))
  · exact hb
  · exact hw

end BianchiIX
