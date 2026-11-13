import Metastability.CompletionStability
import Metastability.PlateauCollision
import Metastability.SourceTerminalTiming

/-! Actual parent completion from prepared stage entry. Both collision times
are produced, and all stage geometry is preserved through the closed terminal
endpoint. No stopped geometry is a premise of the final theorem. -/
noncomputable section
open Set Filter
open scoped Topology RealInnerProductSpace
namespace Metastability.CompletionCollision
open Source CapEnlargement ActiveScales ActiveSourceLaw
variable {n N d : ℕ}

theorem stage_duration_le_particle_count (T : CollisionTree n N) (model : Model) (l : Fin N) :
    1 / (2 * stageRate model T l) ≤ n := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (TreeDynamics.particle_pos T)
  have hc := TreeDynamics.stageRate_pos T model l
  have hb := (div_le_iff₀ hn).mp (stageRate_bounds model T l).1
  apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hc)).mpr
  nlinarith only [hb]

theorem stage_completion (T : CollisionTree n N) (hN : 0 < N)
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
      ∃ t₂ ∈ Ioc t₁ (t₁ + 20 * n * (Real.log (Real.log β) / Real.log β)),
        angularDist (accelerated X shift clock t₁ i) (accelerated X shift clock t₁ j) = mesoscopicScale β ∧
        IsLeast {t : ℝ | s ≤ t ∧
          angularDist (accelerated X shift clock t i) (accelerated X shift clock t j) = mesoscopicScale β} t₁ ∧
        |t₁ - s - 1 / (2 * stageRate model T l)| ≤ K * (Real.log (Real.log β) / Real.log β) ∧
        IsLeast {t : ℝ | s ≤ t ∧ ∀ p ∈ T.parent l, ∀ q ∈ T.parent l,
          angularDist (accelerated X shift clock t p) (accelerated X shift clock t q) ≤ clockCutoff β} t₂ ∧
        (∀ t ∈ Ico s t₂, ¬ ∀ p ∈ T.parent l, ∀ q ∈ T.parent l,
          angularDist (accelerated X shift clock t p) (accelerated X shift clock t q) ≤ clockCutoff β) ∧
        (∀ t ∈ Icc s t₂,
          StageHyp T C β κ (M + 1) l (accelerated X shift clock t) ∧
          1 - ⟪(accelerated X shift clock t i).val, (accelerated X shift clock t j).val⟫ ≤
            upperBarrier C l + treeMargin hN C) ∧
        (∀ t ∈ Icc t₁ t₂,
          angularDist (accelerated X shift clock t i) (accelerated X shift clock t j) ≤ mesoscopicScale β) ∧
        (∀ t ∈ Icc s t₂, ∀ m : Fin N, l < m →
          ∃ p ∈ T.parent m, ∃ q ∈ T.parent m,
            7 * treeMargin hN C ≤
              angularDist (accelerated X shift clock t p) (accelerated X shift clock t q) ∧
            visibleScale β < angularDist (accelerated X shift clock t p) (accelerated X shift clock t q)) := by
  have hκ0 : 0 < κ := (by norm_num : (0 : ℝ) < 4).trans
    ((PlateauStability.kappaThreshold_gt_four n).trans hκ)
  obtain ⟨K, hK, P, hP, hplateau⟩ := PlateauCollision.plateau_stability T hN C hC κ hκ model l
  obtain ⟨S, hS, hstable⟩ := CompletionStability.stopped_interval T hN C hC κ hκ
  obtain ⟨D, hD, hterminal⟩ := SourceTerminalTiming.terminal_completion T hN C hC κ hκ0
  obtain ⟨F, hF, hfuture⟩ := PlateauFuture.future_parent_has_large_pair T hN C hC
  have hbudget : Tendsto (fun β : ℝ => 20 * n * (Real.log (Real.log β) / Real.log β)) atTop (𝓝 0) := by
    simpa only [mul_zero] using ActiveTimingScales.tendsto_loglog_div_log.const_mul (20 * (n : ℝ))
  obtain ⟨E, hE⟩ := eventually_atTop.mp
    ((hbudget.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).and
      (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))))
  refine ⟨K, hK, max (max P S) (max D (max F E)),
    hP.trans_le ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro β hβ M hM X hX shift hshift clock hc s hs i j hi hj hd0 hc0
  have hβP := (le_max_left P S).trans ((le_max_left _ _).trans hβ)
  have hβS := (le_max_right P S).trans ((le_max_left _ _).trans hβ)
  have hβD := (le_max_left D (max F E)).trans ((le_max_right _ _).trans hβ)
  have hβFE := (le_max_right D (max F E)).trans ((le_max_right _ _).trans hβ)
  have hβF := (le_max_left F E).trans hβFE
  have hβE := (le_max_right F E).trans hβFE
  have hβ1 := hP.trans_le hβP
  obtain ⟨hbudget1, hlog1⟩ := hE β hβE
  have hM1 : M + 1 ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 5) :=
    ⟨by linarith only [hM.1], by linarith only [hM.2]⟩
  have hcut : clockCutoff β < mesoscopicScale β := by
    rw [mesoscopicScale_eq_log_mul_visible hβ1]
    have hv := ContractionScale.visibleScale_pos hβ1
    have hh := mul_le_mul_of_nonneg_right hlog1 hv.le
    change visibleScale β / 4 < _
    linarith only [hv, hh]
  obtain ⟨t₁, ht₁, hhit, hbefore, hleast, herror, _, _⟩ :=
    hplateau β hβP M hM X hX shift hshift clock hc s hs i j hi hj hd0 hc0
  have ht₁0 := hs.trans ht₁.1.le
  have htime := stage_duration_le_particle_count T model l
  have hlen : ∀ t ≤ t₁ + 20 * n * (Real.log (Real.log β) / Real.log β),
      t - s ≤ 2 * ((n : ℝ) + 1) := by
    intro t ht
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith only [ht, ht₁.2, htime, hbudget1, hn]
  have hpre : ∀ t ∈ Ico s t₁, ¬ ∀ p ∈ T.parent l, ∀ q ∈ T.parent l,
      angularDist (accelerated X shift clock t p) (accelerated X shift clock t q) ≤ clockCutoff β := by
    intro t ht hcomplete
    exact (not_le.mpr (hcut.trans (hbefore t ht)))
      (hcomplete i (Finset.mem_union_left _ hi) j (Finset.mem_union_right _ hj))
  obtain ⟨t₂, ht₂, hcomplete, hnoncomplete, hterminalAngle⟩ :=
    hterminal β hβD (M + 1) hM1 l model X hX shift hshift clock hc t₁ ht₁0 i j hi hj hhit (by
      intro t ht hprefix
      have hnc : ∀ u ∈ Ico s t, ¬ ∀ p ∈ T.parent l, ∀ q ∈ T.parent l,
          angularDist (accelerated X shift clock u p) (accelerated X shift clock u q) ≤ clockCutoff β := by
        intro u hu
        by_cases hu₁ : u < t₁
        · exact hpre u ⟨hu.1, hu₁⟩
        · exact hprefix u ⟨le_of_not_gt hu₁, hu.2.le⟩
      exact (hstable β hβS M hM model l X hX shift hshift clock hc i j hi hj
        s t hs (ht₁.1.le.trans ht.1) (hlen t ht.2) hd0 hc0 hnc t
        ⟨ht₁.1.le.trans ht.1, le_rfl⟩).1)
  have hnc : ∀ t ∈ Ico s t₂, ¬ ∀ p ∈ T.parent l, ∀ q ∈ T.parent l,
      angularDist (accelerated X shift clock t p) (accelerated X shift clock t q) ≤ clockCutoff β := by
    intro t ht
    by_cases ht₁' : t < t₁
    · exact hpre t ⟨ht.1, ht₁'⟩
    · exact hnoncomplete t ⟨le_of_not_gt ht₁', ht.2⟩
  have hgeometry := hstable β hβS M hM model l X hX shift hshift clock hc i j hi hj
    s t₂ hs (ht₁.1.le.trans ht₂.1.le) (hlen t₂ ht₂.2) hd0 hc0 hnc
  have hleast₂ : IsLeast {t : ℝ | s ≤ t ∧ ∀ p ∈ T.parent l, ∀ q ∈ T.parent l,
      angularDist (accelerated X shift clock t p) (accelerated X shift clock t q) ≤ clockCutoff β} t₂ := by
    refine ⟨⟨ht₁.1.le.trans ht₂.1.le, hcomplete⟩, ?_⟩
    intro t ht
    by_contra h
    exact hnc t ⟨ht.1, lt_of_not_ge h⟩ ht.2
  refine ⟨t₁, ht₁, t₂, ht₂, hhit, hleast, herror, hleast₂, hnc, hgeometry, ?_, ?_⟩
  · intro t ht
    rcases lt_or_eq_of_le ht.2 with hlt | rfl
    · exact hterminalAngle t ⟨ht.1, hlt⟩
    · exact (hcomplete i (Finset.mem_union_left _ hi) j (Finset.mem_union_right _ hj)).trans hcut.le
  · intro t ht m hm
    exact hfuture β hβF (M + 1) hM1 κ l (accelerated X shift clock t) (hgeometry t ht).1 m hm

end Metastability.CompletionCollision
