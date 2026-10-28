import BianchiIX.Dynamics.StableSecondCenterInputRates
import BianchiIX.Dynamics.StableProjectionSecondRegularity

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem stableRescaledSecondDifferential_center_bound_of_rate {y v w : StableState} {c s Q : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) (hs : 0 ≤ s) (hQ : 0 ≤ Q)
    (hq : ∀ r ∈ Icc 0 s,
      |stableRescaledSecondSource (c + 1) v w (y, r) 0| ≤ Q * Real.exp (-r / 4)) :
    |stableRescaledSecondDifferential (c + 1) y s v w 0| ≤ 4 * Q := by
  have hK : 0 < c + 1 := by linarith
  have hf (r : ℝ) (hr : r ∈ Icc 0 s) := hasDerivAt_pi.mp
    (hasDerivAt_stableSecondIntegral_apply hK hc hm.le hu.le hw.le hr.1 v w) 0
  have hcont : Continuous (fun r : ℝ => Q * Real.exp (-r / 4)) := by fun_prop
  have H := abs_sub_le_integral_bound hs hf hcont.continuousOn hq
  have HI := integral_le_of_exp_decay (f := fun r : ℝ => Q * Real.exp (-r / 4))
    (B := Q) (c := (1 / 4 : ℝ)) hs (by norm_num) hQ hcont.continuousOn
    (fun r _ => by apply le_of_eq; congr 1; congr 1; ring)
  rw [stableRescaledSecondDifferential_eq_integral hK hc hm hu hw hs v w]
  simpa only [stableSecondIntegral_initial, zero_apply, Pi.zero_apply,
    sub_zero, div_one, div_div, mul_one] using H.trans (by convert! HI using 1; ring)

theorem stableRescaledSecondDifferential_centerInputs_center_bound {y v w : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) (hs : 0 ≤ s)
    (hv1 : v 1 = 0) (hv2 : v 2 = 0) (hw1 : w 1 = 0) (hw2 : w 2 = 0) :
    |stableRescaledSecondDifferential (c + 1) y s v w 0| ≤
      2400000000 * (|y 1| + |y 2|) ^ 2 * Real.exp (512 * (|y 1| + |y 2|)) ^ 3 * ‖v‖ * ‖w‖ := by
  have H := stableRescaledSecondDifferential_center_bound_of_rate hc hm hu hw hs
    (show 0 ≤ 600000000 * (|y 1| + |y 2|) ^ 2 * Real.exp (512 * (|y 1| + |y 2|)) ^ 3 * ‖v‖ * ‖w‖ by positivity)
    (fun r hr => stableRescaledSecondSource_centerInputs_rate hc hm hu hw hr.1 hv1 hv2 hw1 hw2)
  convert! H using 1
  ring

theorem stableRescaledSecondDifferential_centerInput_center_bound {y v w : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) (hs : 0 ≤ s)
    (hv1 : v 1 = 0) (hv2 : v 2 = 0) :
    |stableRescaledSecondDifferential (c + 1) y s v w 0| ≤
      40000000 * (|y 1| + |y 2|) * Real.exp (512 * (|y 1| + |y 2|)) ^ 3 * ‖v‖ * ‖w‖ := by
  have H := stableRescaledSecondDifferential_center_bound_of_rate hc hm hu hw hs
    (show 0 ≤ 10000000 * (|y 1| + |y 2|) * Real.exp (512 * (|y 1| + |y 2|)) ^ 3 * ‖v‖ * ‖w‖ by positivity)
    (fun r hr => stableRescaledSecondSource_centerInput_rate hc hm hu hw hr.1 hv1 hv2)
  convert! H using 1
  ring

theorem stableBoundaryProjection_fderiv2_bound_of_center_bound {y v w : StableState} {c Q : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200)
    (hH : ∀ s, 0 ≤ s → |stableRescaledSecondDifferential (c + 1) y s v w 0| ≤ Q) :
    |fderiv ℝ (fderiv ℝ (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2))) y v w| ≤ Q := by
  rw [stableBoundaryProjection_fderiv2_eq hc hm hu hw]
  have heval : ContinuousAt (fun L : StableState →L[ℝ] (StableState →L[ℝ] ℝ) => L v w)
      (stableCenterSecondDifferentialLimit c y) :=
    (continuousAt_id.clm_apply continuousAt_const).clm_apply continuousAt_const
  have H := heval.tendsto.comp (stableCenterSecondDifferential_tendsto hc hm hu hw)
  apply le_of_tendsto H.abs
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
  exact hH s hs

theorem stableBoundaryProjection_fderiv2_centerInputs {y v w : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200)
    (hv1 : v 1 = 0) (hv2 : v 2 = 0) (hw1 : w 1 = 0) (hw2 : w 2 = 0) :
    |fderiv ℝ (fderiv ℝ (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2))) y v w| ≤
      2400000000 * (|y 1| + |y 2|) ^ 2 * Real.exp (512 * (|y 1| + |y 2|)) ^ 3 * ‖v‖ * ‖w‖ :=
  stableBoundaryProjection_fderiv2_bound_of_center_bound hc hm hu hw
    (fun _s hs => stableRescaledSecondDifferential_centerInputs_center_bound hc hm hu hw hs hv1 hv2 hw1 hw2)

theorem stableBoundaryProjection_fderiv2_centerInput {y v w : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200)
    (hv1 : v 1 = 0) (hv2 : v 2 = 0) :
    |fderiv ℝ (fderiv ℝ (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2))) y v w| ≤
      40000000 * (|y 1| + |y 2|) * Real.exp (512 * (|y 1| + |y 2|)) ^ 3 * ‖v‖ * ‖w‖ :=
  stableBoundaryProjection_fderiv2_bound_of_center_bound hc hm hu hw
    (fun _s hs => stableRescaledSecondDifferential_centerInput_center_bound hc hm hu hw hs hv1 hv2)

end BianchiIX
