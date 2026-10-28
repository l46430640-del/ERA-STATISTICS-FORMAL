import BianchiIX.Dynamics.StableProjectionDifferential

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The linearized corrected energy is conserved on the single weak-wall orbit. -/
theorem stable_weak_linear_energy {y v : StableState} (hu : y 1 = 0) :
    stableOriginalField y 0 * v 0 +
      (y 0 + 1) * (stableOriginalJacobian y).mulVec v 0 +
      stableOriginalField y 2 * (v 2 - 2 * v 1) +
      y 2 * ((stableOriginalJacobian y).mulVec v 2 -
        2 * (stableOriginalJacobian y).mulVec v 1) = 0 := by
  simp [stableOriginalField, stableOriginalJacobian, stableBoundaryField,
    stableBoundaryJacobian, stableDenomGradient, stableStrongRate, stableWeakRate,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hu]
  ring

theorem stableRescaledFlow_strong_zero {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40) (hu : y 1 = 0)
    (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) :
    stableRescaledFlow (c + 1) y s 1 = 0 := by
  have H := (stableBoundaryOrbit_global (u := y 1) hc hm (by rw [hu]; norm_num) hw
    ((c + 1) * s) (mul_nonneg (by linarith) hs)).2.2.2.1
  rw [hu, abs_zero] at H
  have heq := abs_eq_zero.mp (le_antisymm H (abs_nonneg _))
  simpa [stableRescaledFlow, stableOriginalFlow_eq, stableRestriction_apply, hu] using heq

theorem stableRescaledDifferential_weak_energy {y v : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40) (hu : y 1 = 0)
    (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) :
    let z := stableRescaledFlow (c + 1) y s
    let q := stableRescaledDifferential (c + 1) y s v
    (z 0 + 1) * q 0 + z 2 * (q 2 - 2 * q 1) =
      (y 0 + 1) * v 0 + y 2 * (v 2 - 2 * v 1) := by
  let z := stableRescaledFlow (c + 1) y
  let q := fun t => stableRescaledDifferential (c + 1) y t v
  let E := fun t => (z t 0 + 1) * q t 0 + z t 2 * (q t 2 - 2 * q t 1)
  have hK : 0 < c + 1 := by linarith
  have hu' : |y 1| ≤ 1 / 200 := by rw [hu]; norm_num
  have hE (t : ℝ) (ht : t ∈ Icc 0 s) : HasDerivAt E 0 t := by
    have hz := hasDerivAt_pi.mp (hasDerivAt_stableRescaledFlow hK hc hm hu' hw ht.1)
    have hq := hasDerivAt_pi.mp (stableRescaledFlow_variational_equation hK hc hm hu' hw ht.1 v)
    have H := (((hz 0).add_const 1).mul (hq 0)).add
      ((hz 2).mul ((hq 2).sub ((hq 1).const_mul 2)))
    have Hz : z t 1 = 0 := stableRescaledFlow_strong_zero hc hm hu hw ht.1
    have HE := stable_weak_linear_energy (v := q t) Hz
    convert! H using 1
    change 0 = (c + 1) * stableOriginalField (z t) 0 * q t 0 +
      (z t 0 + 1) * ((c + 1) * (stableOriginalJacobian (z t)).mulVec (q t) 0) +
      ((c + 1) * stableOriginalField (z t) 2 * (q t 2 - 2 * q t 1) +
      z t 2 * ((c + 1) * (stableOriginalJacobian (z t)).mulVec (q t) 2 -
        2 * ((c + 1) * (stableOriginalJacobian (z t)).mulVec (q t) 1)))
    linear_combination -(c + 1) * HE
  have H := (convex_Icc (0 : ℝ) s).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hE t ht).hasDerivWithinAt) (C := 0) (fun _ _ => by simp)
    (show 0 ∈ Icc 0 s from ⟨le_rfl, hs⟩) (show s ∈ Icc 0 s from ⟨hs, le_rfl⟩)
  have heq : E s = E 0 := by simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using H
  simpa only [E, z, q, stableRescaledFlow_initial, stableRescaledDifferential_initial,
    ContinuousLinearMap.id_apply] using heq

/-- Exact differential of the stable projection, including transverse strong inputs. -/
theorem stableBoundaryProjection_fderiv_weak {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40) (hu : y 1 = 0)
    (hw : |y 2| < 1 / 200) (v : StableState) :
    (stableBoundaryProjection (y 0) (y 1) (y 2) + 1) *
      fderiv ℝ (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2)) y v =
        (y 0 + 1) * v 0 + y 2 * (v 2 - 2 * v 1) := by
  let z := stableRescaledFlow (c + 1) y
  let q := fun t => stableRescaledDifferential (c + 1) y t v
  let P := stableBoundaryProjection (y 0) (y 1) (y 2)
  have hu' : |y 1| < 1 / 200 := by rw [hu]; norm_num
  have hz := tendsto_pi_nhds.mp (stableRescaledFlow_limit (by linarith : 0 < c + 1) hc hm.le hu'.le hw.le)
  have hq : Tendsto (fun t => q t 0) atTop
      (𝓝 (fderiv ℝ (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2)) y v)) := by
    rw [stableBoundaryProjection_fderiv_eq hc hm hu' hw]
    exact (continuousAt_id.clm_apply continuousAt_const).tendsto.comp
      (stableCenterDifferential_tendsto hc hm.le hu'.le hw.le)
  have hbounded (i : Fin 3) : IsBoundedUnder (· ≤ ·) atTop (fun t => ‖q t i‖) := by
    refine ⟨Real.exp (512 * (|y 1| + |y 2|)) * ‖v‖, ?_⟩
    change ∀ᶠ t in atTop, ‖q t i‖ ≤ _
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (norm_le_pi_norm (q t) i).trans (stableRescaledDifferential_bound hc hm.le hu'.le hw.le ht v)
  have hW : Tendsto (fun t => z t 2) atTop (𝓝 0) := hz 2
  have hWq (i : Fin 3) : Tendsto (fun t => z t 2 * q t i) atTop (𝓝 0) :=
    hW.zero_mul_isBoundedUnder_le (hbounded i)
  have hlim := (((hz 0).add_const 1).mul hq).add ((hWq 2).sub ((hWq 1).const_mul 2))
  have heq : (fun t => (z t 0 + 1) * q t 0 + (z t 2 * q t 2 - 2 * (z t 2 * q t 1))) =ᶠ[atTop]
      (fun _ => (y 0 + 1) * v 0 + y 2 * (v 2 - 2 * v 1)) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have H := stableRescaledDifferential_weak_energy (v := v) hc hm.le hu hw.le ht
    dsimp only at H
    change (z t 0 + 1) * q t 0 + z t 2 * (q t 2 - 2 * q t 1) = _ at H
    nlinarith only [H]
  have H := tendsto_nhds_unique (hlim.congr' heq) tendsto_const_nhds
  simpa only [Matrix.cons_val_zero, sub_self, mul_zero, zero_sub, add_zero] using H

end BianchiIX
