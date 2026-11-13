import Metastability.PlateauStability
import Metastability.PlateauFuture
import Metastability.ActiveCollisionTiming

/-!
# Plateau stability through the actual first mesoscopic collision

This source-facing export assumes only prepared entry caps, exponentially
tight entry blocks, the actual ODE, and the actual cutoff clock. The stopped
stage hypotheses are conclusions, including at the produced collision time.
-/

noncomputable section
open Set Filter
open scoped Topology RealInnerProductSpace

namespace Metastability.PlateauCollision
open Source CapEnlargement ActiveScales ActiveSourceLaw
variable {n N d : ℕ}

theorem horizon_bound (T : CollisionTree n N) (model : Model) (l : Fin N) :
    2 / stageRate model T l ≤ 2 * ((n : ℝ) + 1) := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (TreeDynamics.particle_pos T)
  have hc := TreeDynamics.stageRate_pos T model l
  have hb := (div_le_iff₀ hn).mp (stageRate_bounds model T l).1
  apply (div_le_iff₀ hc).mpr
  nlinarith only [hb, hc]

/-- The plateau milestone: the first mesoscopic hit exists strictly before
the manuscript horizon, has the source timing error, and all stage geometry
persists on its closed entry-to-hit interval. Every later prescribed parent
contains a pair separated by a fixed positive angle, so no later merge has
occurred. Constants precede temperature, entry multiplier, solution, clock,
entry time, and representative labels. -/
theorem plateau_stability (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) (κ : ℝ)
    (hκ : PlateauStability.kappaThreshold n < κ) (model : Model) (l : Fin N) :
    ∃ K : ℝ, 0 < K ∧ ∃ β₀ : ℝ, 1 < β₀ ∧
      ∀ β ≥ β₀, ∀ M ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 4),
      ∀ X : ℝ → Configuration n d, Solves model β X →
      ∀ shift : ℝ, 0 ≤ shift → ∀ clock : ℝ → ℝ, ClockRelation β X shift clock →
      ∀ s : ℝ, 0 ≤ s → ∀ i j : Fin n, i ∈ T.left l → j ∈ T.right l →
      (∀ D ∈ T.partition l.castSucc, ∀ p ∈ D, ∀ q ∈ D,
        angularDist (accelerated X shift clock s p) (accelerated X shift clock s q) ≤
          Real.exp (-2 * κ * β)) →
      (∀ (D : Block n) (hD : D ∈ T.partition l.castSucc), ∀ p ∈ D,
        angularDist (accelerated X shift clock s p) (C (T.currentNode l D hD)).center ≤
          (C (T.currentNode l D hD)).radius + M * enlargementScale β) →
      ∃ t₁ ∈ Ioo s (s + (1 + 1 / (2 * stageRate model T l))),
        angularDist (accelerated X shift clock t₁ i) (accelerated X shift clock t₁ j) =
          mesoscopicScale β ∧
        (∀ u ∈ Ico s t₁, mesoscopicScale β <
          angularDist (accelerated X shift clock u i) (accelerated X shift clock u j)) ∧
        IsLeast {t : ℝ | s ≤ t ∧
          angularDist (accelerated X shift clock t i) (accelerated X shift clock t j) =
            mesoscopicScale β} t₁ ∧
        |t₁ - s - 1 / (2 * stageRate model T l)| ≤ K * (Real.log (Real.log β) / Real.log β) ∧
        (∀ t ∈ Icc s t₁,
          StageHyp T C β κ (M + 1) l (accelerated X shift clock t) ∧
          1 - ⟪(accelerated X shift clock t i).val, (accelerated X shift clock t j).val⟫ ≤
            upperBarrier C l + treeMargin hN C) ∧
        (∀ t ∈ Icc s t₁, ∀ m : Fin N, l < m →
          ∃ p ∈ T.parent m, ∃ q ∈ T.parent m,
            7 * treeMargin hN C ≤
              angularDist (accelerated X shift clock t p) (accelerated X shift clock t q) ∧
            visibleScale β <
              angularDist (accelerated X shift clock t p) (accelerated X shift clock t q)) := by
  have hκ4 := (PlateauStability.kappaThreshold_gt_four n).trans hκ
  obtain ⟨P, hP, hplateau⟩ := PlateauStability.stopped_interval T hN C hC κ hκ
  obtain ⟨K, hK, H, hH, hhit⟩ := ActiveCollisionTiming.first_mesoscopic_collision
    T hN C hC κ hκ4 model l
  obtain ⟨F, hF, hfuture⟩ := PlateauFuture.future_parent_has_large_pair T hN C hC
  have herrSmall : ∀ᶠ β : ℝ in atTop, K * (Real.log (Real.log β) / Real.log β) < 1 := by
    have ht : Tendsto (fun β : ℝ => K * (Real.log (Real.log β) / Real.log β)) atTop (𝓝 0) := by
      simpa only [mul_zero] using ActiveTimingScales.tendsto_loglog_div_log.const_mul K
    exact ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨E, hE⟩ := eventually_atTop.mp herrSmall
  refine ⟨K, hK, max (max P H) (max F E), hP.trans_le ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro β hβ M hM X hX shift hshift clock hc s hs i j hi hj hd0 hc0
  have hβP := (le_max_left P H).trans ((le_max_left _ _).trans hβ)
  have hβH := (le_max_right P H).trans ((le_max_left _ _).trans hβ)
  have hβF := (le_max_left F E).trans ((le_max_right _ _).trans hβ)
  have hβE := (le_max_right F E).trans ((le_max_right _ _).trans hβ)
  have hβ1 := hP.trans_le hβP
  have hM1 : M + 1 ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 5) :=
    ⟨by linarith only [hM.1], by linarith only [hM.2]⟩
  have hγ := (enlargementScale_pos (zero_lt_one.trans hβ1)).le
  have hc1 : ∀ (D : Block n) (hD : D ∈ T.partition l.castSucc), ∀ p ∈ D,
      angularDist (accelerated X shift clock s p) (C (T.currentNode l D hD)).center ≤
        (C (T.currentNode l D hD)).radius + (M + 1) * enlargementScale β := by
    intro D hD p hp
    have hh := hc0 D hD p hp
    nlinarith only [hh, hγ]
  have hδ := (treeMargin_pos hN C hC).le
  have htime := horizon_bound T model l
  obtain ⟨t₁, ht₁, hhit₁, hbefore, hleast, herror⟩ := hhit β hβH (M + 1) hM1
    X hX shift hshift clock hc s hs i j hi hj hc1 (by
      intro t ht hprefix
      have hlen : t - s ≤ 2 * ((n : ℝ) + 1) := by linarith only [ht.2, htime]
      obtain ⟨hst, hup⟩ := hplateau β hβP M hM model l X hX shift hshift clock hc
        i j hi hj s t hs ht.1 hlen hd0 hc0 (fun u hu => (hprefix u hu).le) t ⟨ht.1, le_rfl⟩
      exact ⟨hst, by linarith only [hup, hδ]⟩)
  have hlen : t₁ - s ≤ 2 * ((n : ℝ) + 1) := by linarith only [ht₁.2, htime]
  have hangle : ∀ t ∈ Icc s t₁, mesoscopicScale β ≤
      angularDist (accelerated X shift clock t i) (accelerated X shift clock t j) := by
    intro t ht
    rcases lt_or_eq_of_le ht.2 with hlt | rfl
    · exact (hbefore t ⟨ht.1, hlt⟩).le
    · exact hhit₁.symm.le
  have hstable := hplateau β hβP M hM model l X hX shift hshift clock hc
    i j hi hj s t₁ hs ht₁.1.le hlen hd0 hc0 hangle
  have htimeStrict : t₁ < s + (1 + 1 / (2 * stageRate model T l)) := by
    have he := (abs_le.mp herror).2
    have hh := hE β hβE
    linarith only [he, hh]
  refine ⟨t₁, ⟨ht₁.1, htimeStrict⟩, hhit₁, hbefore, hleast, herror, hstable, ?_⟩
  intro t ht m hm
  exact hfuture β hβF (M + 1) hM1 κ l (accelerated X shift clock t) (hstable t ht).1 m hm

end Metastability.PlateauCollision
