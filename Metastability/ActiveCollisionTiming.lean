import Metastability.ActiveSourceLaw
import Metastability.ActiveStoppedTiming
import Metastability.ActiveEntry

/-!
# The source first mesoscopic collision time

The theorem consumes the actual ODE, literal cutoff clock, prepared entry caps,
and the manuscript's stopped stage hypotheses. Its scalar law and regularity
are proved inputs from other modules, not premises. An actual least hitting
time is produced, avoiding any convention for the infimum of an empty set.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace
namespace Metastability.ActiveCollisionTiming
open Source ActiveScales ActiveLogCoordinate ActiveSourceLaw CapEnlargement
variable {n N d : ℕ}

/-- First part of the source timing corollary. Constants are chosen before the
real temperature, entry time, solution, clock, and representatives. The stopped
stage conditions are required only on a fixed finite horizon before a first
mesoscopic hit. Initial exponential tightness is not additionally needed once
those stopped conditions are supplied. -/
theorem first_mesoscopic_collision (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) (κ : ℝ) (hκ : 4 < κ)
    (model : Model) (l : Fin N) :
    ∃ K : ℝ, 0 < K ∧ ∃ β₀ : ℝ, 1 < β₀ ∧
      ∀ β ≥ β₀, ∀ M ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 5),
      ∀ X : ℝ → Configuration n d, Solves model β X →
      ∀ shift : ℝ, 0 ≤ shift → ∀ clock : ℝ → ℝ, ClockRelation β X shift clock →
      ∀ s : ℝ, 0 ≤ s → ∀ i j : Fin n, i ∈ T.left l → j ∈ T.right l →
      (∀ (D : Block n) (hD : D ∈ T.partition l.castSucc), ∀ k ∈ D,
        angularDist (accelerated X shift clock s k) (C (T.currentNode l D hD)).center ≤
          (C (T.currentNode l D hD)).radius + M * enlargementScale β) →
      (∀ t ∈ Icc s (s + 2 / stageRate model T l),
        (∀ u ∈ Icc s t, mesoscopicScale β <
          angularDist (accelerated X shift clock u i) (accelerated X shift clock u j)) →
        StageHyp T C β κ M l (accelerated X shift clock t) ∧
          1 - ⟪(accelerated X shift clock t i).val, (accelerated X shift clock t j).val⟫ ≤
            upperBarrier C l + 2 * treeMargin hN C) →
      ∃ t₁ ∈ Ioc s (s + 2 / stageRate model T l),
        angularDist (accelerated X shift clock t₁ i) (accelerated X shift clock t₁ j) =
          mesoscopicScale β ∧
        (∀ u ∈ Ico s t₁, mesoscopicScale β <
          angularDist (accelerated X shift clock u i) (accelerated X shift clock u j)) ∧
        IsLeast {t : ℝ | s ≤ t ∧
          angularDist (accelerated X shift clock t i) (accelerated X shift clock t j) =
            mesoscopicScale β} t₁ ∧
        |t₁ - s - 1 / (2 * stageRate model T l)| ≤ K * (Real.log (Real.log β) / Real.log β) := by
  obtain ⟨D, hD, βlaw, hβlaw, hlaw⟩ := active_scalar_law T hN C hC κ hκ
  obtain ⟨B, hB, βentry, hβentry, hentry⟩ := ActiveEntry.entry_log_bound T C hC l
  have hc := TreeDynamics.stageRate_pos T model l
  have hu0 : 0 < upperBarrier C l + 2 * treeMargin hN C := by
    have hu := (TreeSeparation.lowerBarrier_pos T C hC l).trans_le (hC.2 l).2.2.2.2.1
    have hδ := treeMargin_pos hN C hC
    linarith only [hu, hδ]
  have hu2 := (source_barrier_parameters T hN C hC κ hκ l).2.2.2.2
  obtain ⟨K, hK, htiming⟩ := ActiveStoppedTiming.eventual_actual_first_hit n d
    (stageRate model T l) B D (upperBarrier C l + 2 * treeMargin hN C) hc hB hD.le hu0 hu2
  obtain ⟨βtime, hβtime⟩ := eventually_atTop.mp htiming
  refine ⟨K, hK, max βlaw (max βentry βtime), hβlaw.trans_le (le_max_left _ _), ?_⟩
  intro β hβ M hM X hX shift hshift clock hclock s hs i j hi hj hcaps hstop
  have hlawβ : βlaw ≤ β := (le_max_left _ _).trans hβ
  have hentryβ : βentry ≤ β := (le_max_left _ _).trans ((le_max_right _ _).trans hβ)
  have htimeβ : βtime ≤ β := (le_max_right _ _).trans ((le_max_right _ _).trans hβ)
  obtain ⟨hρstart, hBstart⟩ := hentry β hentryβ M hM
    (accelerated X shift clock s i) (accelerated X shift clock s j)
    (hcaps _ (T.left_mem l) i hi) (hcaps _ (T.right_mem l) j hj)
  have haelaw := (ae_restrict_iff' measurableSet_Ici).mp
    (hlaw β hlawβ M hM model l X hX shift hshift clock hclock i j hi hj)
  obtain ⟨t₁, ht₁, hhit, hbefore, herr⟩ := (hβtime β htimeβ).2 model X hX shift hshift clock hclock
    s hs i j hρstart hBstart (by
      filter_upwards [haelaw] with t ht hmem hprefix
      obtain ⟨hstage, hupper⟩ := hstop t ⟨hmem.1.le, hmem.2.le⟩ hprefix
      obtain ⟨_, v, _, _, hd, hv⟩ := ht (hs.trans hmem.1.le) hstage hupper
        (hprefix t ⟨hmem.1.le, le_rfl⟩).le
      exact ⟨hupper, v, hd, by simpa only [neg_div] using hv⟩)
  refine ⟨t₁, ht₁, hhit, hbefore, ⟨⟨ht₁.1.le, hhit⟩, ?_⟩, herr⟩
  intro t ht
  by_contra h
  have hlt := hbefore t ⟨ht.1, lt_of_not_ge h⟩
  rw [ht.2] at hlt
  exact (lt_irrefl _) hlt

end Metastability.ActiveCollisionTiming
