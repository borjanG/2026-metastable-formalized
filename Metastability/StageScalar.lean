import Metastability.ActiveSourceLaw
import Metastability.ActiveTiming

/-! Integration of the actual active logarithmic law on closed stage intervals.
The later uniform angle limit uses this estimate, with the entry coordinate
bounded by the prescribed caps. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace
namespace Metastability.StageScalar
open Source ActiveSourceLaw ActiveScales ActiveLogCoordinate CapEnlargement
variable {n N d : ℕ}

/-- Regularity of the literal logarithmic coordinate follows from source
trajectory regularity and a compact correlation range inside (-1,1). -/
theorem absolutelyContinuous_log (model : Model) (β : ℝ) (hβ : 1 < β)
    (X : ℝ → Configuration n d) (hX : Solves model β X)
    (shift : ℝ) (hshift : 0 ≤ shift) (clock : ℝ → ℝ)
    (hc : ClockRelation β X shift clock) (i j : Fin n)
    (a b lo hi : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hlo : -1 < lo) (hhi : hi < 1)
    (hrange : ∀ t ∈ Icc a b, ⟪(accelerated X shift clock t i).val,
      (accelerated X shift clock t j).val⟫ ∈ Icc lo hi) :
    AbsolutelyContinuousOnInterval (fun t => logHalfAngle
      ⟪(accelerated X shift clock t i).val, (accelerated X shift clock t j).val⟫) a b := by
  obtain ⟨K, hK⟩ := exists_lipschitzOnWith_logHalfAngle hlo hhi
  have hp := (ActiveTrajectory.accelerated_correlation_lipschitz model β hβ X hX
    shift hshift clock hc i j).mono (show Icc a b ⊆ Ici 0 from fun _ ht => ha.trans ht.1)
  have hcomp := hK.comp hp hrange
  apply LipschitzOnWith.absolutelyContinuousOnInterval
  simpa only [uIcc_of_le hab] using hcomp

/-- The integrated source scalar law, with an explicit uniform error at both
closed endpoints. No differential law or absolute continuity is an input. -/
theorem integrated_log_law (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) (κ : ℝ) (hκ : 4 < κ) :
    ∃ K : ℝ, 0 < K ∧ ∃ β₀ : ℝ, 1 < β₀ ∧ ∀ β ≥ β₀,
      ∀ M ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 5),
      ∀ (model : Model) (l : Fin N) (X : ℝ → Configuration n d),
      Solves model β X → ∀ shift : ℝ, 0 ≤ shift → ∀ clock : ℝ → ℝ,
      ClockRelation β X shift clock → ∀ i j : Fin n, i ∈ T.left l → j ∈ T.right l →
      ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      (∀ t ∈ Icc a b, StageHyp T C β κ M l (accelerated X shift clock t)) →
      (∀ t ∈ Icc a b, 1 - ⟪(accelerated X shift clock t i).val,
        (accelerated X shift clock t j).val⟫ ≤ upperBarrier C l + 2 * treeMargin hN C) →
      (∀ t ∈ Icc a b, mesoscopicScale β ≤
        angularDist (accelerated X shift clock t i) (accelerated X shift clock t j)) →
      |logHalfAngle ⟪(accelerated X shift clock b i).val, (accelerated X shift clock b j).val⟫ -
        logHalfAngle ⟪(accelerated X shift clock a i).val, (accelerated X shift clock a j).val⟫ +
        stageRate model T l * Real.log β * (b - a)| ≤
        K * β ^ (-(1 / 3 : ℝ)) * Real.log β * (b - a) := by
  obtain ⟨K, hK, B, hB, hlaw⟩ := active_scalar_law T hN C hC κ hκ
  obtain ⟨E, hE⟩ := eventually_atTop.mp
    (tendsto_mesoscopicScale.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  refine ⟨K, hK, max B E, hB.trans_le (le_max_left _ _), ?_⟩
  intro β hβ M hM model l X hX shift hshift clock hc i j hi hj a b ha hab hstage hupper hangle
  have hβB := (le_max_left B E).trans hβ
  have hβ1 := hB.trans_le hβB
  have hmeso := hE β ((le_max_right B E).trans hβ)
  have hU := (source_barrier_parameters T hN C hC κ hκ l).2.2.2.2
  have hlo : -1 < 1 - (upperBarrier C l + 2 * treeMargin hN C) := by linarith only [hU]
  have hhi : Real.cos (mesoscopicScale β) < 1 := by
    have hh := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl (0 : ℝ))
      (hmeso.le.trans (by linarith only [Real.two_le_pi] : (1 : ℝ) ≤ Real.pi))
      (mesoscopicScale_pos hβ1)
    simpa only [Real.cos_zero] using hh
  have hrange : ∀ t ∈ Icc a b, ⟪(accelerated X shift clock t i).val,
      (accelerated X shift clock t j).val⟫ ∈
      Icc (1 - (upperBarrier C l + 2 * treeMargin hN C)) (Real.cos (mesoscopicScale β)) := by
    intro t ht
    refine ⟨by linarith only [hupper t ht], ?_⟩
    rw [← AngularGeometry.cos_angularDist]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (mesoscopicScale_pos hβ1).le
      (AngularGeometry.angularDist_le_pi _ _) (hangle t ht)
  have hac := absolutelyContinuous_log model β hβ1 X hX shift hshift clock hc i j a b
    _ _ ha hab hlo hhi hrange
  apply ActiveTiming.integrated_slope_error hab hac
  have hd := (ae_restrict_iff' measurableSet_Ici).mp
    (hlaw β hβB M hM model l X hX shift hshift clock hc i j hi hj)
  filter_upwards [hd] with t ht hmem
  obtain ⟨_, v, _, _, hv, herr⟩ := ht (ha.trans hmem.1.le)
    (hstage t ⟨hmem.1.le, hmem.2.le⟩) (hupper t ⟨hmem.1.le, hmem.2.le⟩)
    (hangle t ⟨hmem.1.le, hmem.2.le⟩)
  rwa [hv.deriv]

end Metastability.StageScalar
