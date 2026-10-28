import BianchiIX.Statistics.PhysicalFuture
import BianchiIX.Dynamics.AxisFrameComposition
import BianchiIX.Dynamics.AxisCharts

noncomputable section

namespace BianchiIX

theorem StatisticalCoreFuture.of_axisFrame {η σ Bcap : ℝ} {J : ℕ} {x : NormalizedState}
    (i : Fin 6) (H : StatisticalCoreFuture η J σ Bcap ((axisFrame i).map x)) :
    StatisticalCoreFuture η J σ Bcap x := by
  obtain ⟨T, ht, hdom, j, p, hstat, ho⟩ := H
  have hdom' : T ∈ normalizedMaxDomain x 0 := by rwa [(axisFrame i).maxDomain] at hdom
  obtain ⟨k, hk⟩ := axisFrame_comp j i
  refine ⟨T, ht, hdom', k, p, hstat, ?_⟩
  rwa [(axisFrame i).maxCurve hdom', hk] at ho

theorem statisticalCoreFuture_axisFrame_iff {η σ Bcap : ℝ} {J : ℕ} (i : Fin 6) (x : NormalizedState) :
    StatisticalCoreFuture η J σ Bcap ((axisFrame i).map x) ↔ StatisticalCoreFuture η J σ Bcap x := by
  refine ⟨fun H => H.of_axisFrame i, ?_⟩
  intro H
  obtain ⟨k, hk⟩ := axisFrame_inverse i
  exact (show StatisticalCoreFuture η J σ Bcap ((axisFrame k).map ((axisFrame i).map x)) from
    by simpa only [hk] using H).of_axisFrame k

theorem statisticalCoreFuture_axisPermutation_iff {η σ Bcap : ℝ} {J : ℕ}
    (π : Equiv.Perm (Fin 3)) (x : NormalizedState) :
    StatisticalCoreFuture η J σ Bcap ((axisPermutation π).map x) ↔ StatisticalCoreFuture η J σ Bcap x :=
  statisticalCoreFuture_axisFrame_iff _ x

theorem statisticalCoreFuture_axisWallChart_iff {η σ Bcap h : ℝ} {J : ℕ}
    (π : Equiv.Perm (Fin 3)) (y : SectionCoordinates) :
    StatisticalCoreFuture η J σ Bcap (axisWallChart (axisPermutation π) h y) ↔
      StatisticalCoreFuture η J σ Bcap (mainWallChart h y) := by
  have H := statisticalCoreFuture_axisPermutation_iff (η := η) (J := J) (σ := σ) (Bcap := Bcap)
    π ((axisPermutation π).map.symm (mainWallChart h y))
  simpa only [axisWallChart, ContinuousLinearEquiv.apply_symm_apply] using H.symm

end BianchiIX
