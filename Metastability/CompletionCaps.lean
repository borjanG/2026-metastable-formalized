import Metastability.PlateauCaps
import Metastability.CompletionScalar

/-! Strict cap margins from original stage entry, valid through the closed
parent-completion endpoint. Only pre-completion times require a clock bound. -/
noncomputable section
open Set Filter
open scoped Topology RealInnerProductSpace
namespace Metastability.CompletionCaps
open Source CapEnlargement ActiveSourceLaw PlateauCaps
variable {n N d : ℕ}

theorem cap_margin (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) (κ : ℝ) (hκ : 4 < κ) :
    ∃ β₀ : ℝ, 1 < β₀ ∧ ∀ β ≥ β₀,
      ∀ M ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 4),
        (∀ A, (C A).radius + (M + 1) * enlargementScale β < Real.pi / 2) ∧
      ∀ (model : Model) (l : Fin N) (X : ℝ → Configuration n d), Solves model β X →
      ∀ shift : ℝ, 0 ≤ shift → ∀ clock : ℝ → ℝ, ClockRelation β X shift clock →
      ∀ i j : Fin n, i ∈ T.left l → j ∈ T.right l →
      ∀ a b : ℝ, 0 ≤ a → a ≤ b → b - a ≤ 2 * ((n : ℝ) + 1) →
      (∀ (D : Block n) (hD : D ∈ T.partition l.castSucc), ∀ k ∈ D,
        angularDist (accelerated X shift clock a k) (C (T.currentNode l D hD)).center ≤
          (C (T.currentNode l D hD)).radius + M * enlargementScale β) →
      (∀ t ∈ Icc a b, StageHyp T C β κ (M + 1) l (accelerated X shift clock t)) →
      (∀ t ∈ Icc a b,
        1 - ⟪(accelerated X shift clock t i).val, (accelerated X shift clock t j).val⟫ ≤
          upperBarrier C l + 2 * treeMargin hN C) →
      (∀ t ∈ Ico a b, ¬ ∀ p ∈ T.parent l, ∀ q ∈ T.parent l,
        angularDist (accelerated X shift clock t p) (accelerated X shift clock t q) ≤ clockCutoff β) →
      ∀ t ∈ Icc a b,
        (∀ (D : Block n) (hD : D ∈ T.partition l.castSucc), D ≠ T.left l → D ≠ T.right l →
          ∀ k ∈ D,
            angularDist (accelerated X shift clock t k) (C (T.currentNode l D hD)).center <
              (C (T.currentNode l D hD)).radius + (M + 1) * enlargementScale β) ∧
        (∀ hp : T.parent l ≠ Finset.univ, ∀ k ∈ T.parent l,
          angularDist (accelerated X shift clock t k) (C (T.parentNode l hp)).center <
            (C (T.parentNode l hp)).radius + (M + 1) * enlargementScale β) := by
  obtain ⟨E, hE, hentryGeometry⟩ := PlateauCapGeometry.entry_cap_geometry T hN C hC
  obtain ⟨G, hG, hgeometry⟩ := ActiveGeometry.stage_barriers T hN C hC
  obtain ⟨S, hS, hscalar⟩ := CompletionScalar.interval_bounds T hN C hC κ hκ
  obtain ⟨P, hP⟩ := eventually_atTop.mp
    (PlateauCapScale.eventually_cap_error n (treeMargin hN C) (treeMargin_pos hN C hC))
  refine ⟨max (max E G) (max S P), hE.trans_le ((le_max_left E G).trans (le_max_left _ _)), ?_⟩
  intro β hβ M hM
  have hβE := (le_max_left E G).trans ((le_max_left _ _).trans hβ)
  have hβG := (le_max_right E G).trans ((le_max_left _ _).trans hβ)
  have hβS := (le_max_left S P).trans ((le_max_right _ _).trans hβ)
  have hβP := (le_max_right S P).trans ((le_max_right _ _).trans hβ)
  obtain ⟨hβ1, hscale, herror⟩ := hP β hβP
  have hM0 : M ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 5) := ⟨hM.1, by linarith only [hM.2]⟩
  have hM1 : M + 1 ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 5) :=
    ⟨by linarith only [hM.1], by linarith only [hM.2]⟩
  have hsmall := (hentryGeometry β hβE (M + 1) hM1).1
  refine ⟨hsmall, ?_⟩
  intro model l X hX shift hshift clock hc i j hi hj a b ha hab htime hentry hstage hupper hnoncomplete
  have hclock := (hscalar β hβS (M + 1) hM1 model l X hX shift hshift clock hc
    i j hi hj a b ha hab hstage hupper hnoncomplete).2.1
  have hlength : clock b - clock a ≤ 4 * ((n : ℝ) + 1) * Real.log β *
      Real.exp (β * (upperBarrier C l + 2 * treeMargin hN C)) := by
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htime (by norm_num : (0 : ℝ) ≤ 2))
        (Real.log_pos hβ1).le)
      (Real.exp_pos (β * (upperBarrier C l + 2 * treeMargin hN C))).le
    nlinarith only [hclock, hh]
  have hext : ∀ t ∈ Icc a b,
      (∀ p ∈ T.parent l, ∀ q ∉ T.parent l,
        upperBarrier C l + 7 * treeMargin hN C ≤
          1 - ⟪(accelerated X shift clock t p).val, (accelerated X shift clock t q).val⟫) ∧
      (∀ p q, T.blockOf l.castSucc p ≠ T.blockOf l.castSucc q →
        ¬ ActiveGeometry.IsActiveCross T l p q →
        upperBarrier C l + 7 * treeMargin hN C ≤
          1 - ⟪(accelerated X shift clock t p).val, (accelerated X shift clock t q).val⟫) := by
    intro t ht
    exact hgeometry β hβG (M + 1) hM1 l (accelerated X shift clock t)
      (hstage t ht).2.1 (hstage t ht).2.2
  have hparentEntry := ((hentryGeometry β hβE M hM0).2 l
    (accelerated X shift clock a) hentry).1
  have hγ := enlargementScale_pos (zero_lt_one.trans hβ1)
  have hpositiveR : ∀ A, 0 ≤ (C A).radius + (M + 1) * enlargementScale β :=
    fun A => add_nonneg (C A).radius_nonneg (mul_nonneg hM1.1 hγ.le)
  intro t ht
  constructor
  · intro D hD hDl hDr k hk
    have hmargin := cap_margin_of_clock_length model β hβ1 X hX shift hshift clock hc
      D (T.block_nonempty _ _ hD) (C (T.currentNode l D hD)) a b M
      (upperBarrier C l + 2 * treeMargin hN C) (treeMargin hN C)
      ha hab hM.1 (hsmall _) hscale herror hlength (hentry D hD)
      (fun u hu => (hstage u ⟨hu.1, hu.2.le⟩).2.1 D hD hDl hDr) (by
        intro u hu p hp q hq
        have hh := PlateauCapGeometry.inactive_barrier_of_nonactive_pairs T l
          (accelerated X shift clock u) _ (hext u ⟨hu.1, hu.2.le⟩).2 D hD hDl hDr p hp q hq
        linarith only [hh]) t ht k hk
    exact angularDist_lt_of_cos_lt _ _ _ (hpositiveR _) hmargin.2
  · intro hp k hk
    have hA : (T.parent l).Nonempty :=
      (T.block_nonempty _ _ (T.left_mem l)).mono (Finset.subset_union_left)
    have hmargin := cap_margin_of_clock_length model β hβ1 X hX shift hshift clock hc
      (T.parent l) hA (C (T.parentNode l hp)) a b M
      (upperBarrier C l + 2 * treeMargin hN C) (treeMargin hN C)
      ha hab hM.1 (hsmall _) hscale herror hlength (hparentEntry hp)
      (fun u hu => (hstage u ⟨hu.1, hu.2.le⟩).2.2 hp) (by
        intro u hu p hp' q hq
        have hh := (hext u ⟨hu.1, hu.2.le⟩).1 p hp' q hq
        linarith only [hh]) t ht k hk
    exact angularDist_lt_of_cos_lt _ _ _ (hpositiveR _) hmargin.2


end Metastability.CompletionCaps
