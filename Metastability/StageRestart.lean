import Metastability.CompletionCollision
import Metastability.NextStageGeometry
import Metastability.PostMergeStep

/-! One geometric stage, from prepared entry through collision and post-merge
tightening. The same actual clock serves all times. The next entry geometry
and timing are produced; active deterministic-center propagation is separate. -/
noncomputable section
open Set Filter
open scoped Topology RealInnerProductSpace
namespace Metastability.StageRestart
open Source CapEnlargement ActiveScales ActiveSourceLaw
variable {n N d : ℕ}

theorem stage_to_next_entry (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) (κ : ℝ)
    (hκ : PlateauStability.kappaThreshold n < κ) (model : Model)
    (l k : Fin N) (hk : k.castSucc = l.succ) (CStar : ℝ)
    (hCStar : 8 * κ / (1 / (4 * (n : ℝ))) < CStar) :
    ∃ K : ℝ, 0 < K ∧ ∃ β₀ : ℝ, 1 < β₀ ∧
      ∀ β ≥ β₀, ∀ M ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 3),
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
      ∃ snext : ℝ, t₂ ≤ snext ∧
        IsLeast {t : ℝ | s ≤ t ∧
          angularDist (accelerated X shift clock t i) (accelerated X shift clock t j) = mesoscopicScale β} t₁ ∧
        IsLeast {t : ℝ | s ≤ t ∧ ∀ p ∈ T.parent l, ∀ q ∈ T.parent l,
          angularDist (accelerated X shift clock t p) (accelerated X shift clock t q) ≤ clockCutoff β} t₂ ∧
        |t₁ - s - 1 / (2 * stageRate model T l)| ≤ K * (Real.log (Real.log β) / Real.log β) ∧
        snext = originalClockTime β X shift (clock t₂ + CStar * β) ∧
        clock snext = clock t₂ + CStar * β ∧
        snext - t₂ ≤ CStar * β / Real.log β * Real.exp (-β * (lowerBarrier C k - treeMargin hN C)) ∧
        |snext - s - 1 / (2 * stageRate model T l)| ≤
          (K + 20 * n + 1) * (Real.log (Real.log β) / Real.log β) ∧
        (∀ t ∈ Icc s t₂, StageHyp T C β κ (M + 1) l (accelerated X shift clock t)) ∧
        (∀ D ∈ T.partition k.castSucc, ∀ p ∈ D, ∀ q ∈ D,
          angularDist (accelerated X shift clock snext p) (accelerated X shift clock snext q) ≤
            Real.exp (-2 * κ * β)) ∧
        (∀ t ∈ Icc t₂ snext,
          (∀ (D : Block n) (hD : D ∈ T.partition k.castSucc), ∀ p ∈ D,
            angularDist (accelerated X shift clock t p) (C (T.currentNode k D hD)).center <
              (C (T.currentNode k D hD)).radius + (M + 2) * enlargementScale β) ∧
          (∀ D ∈ T.partition k.castSucc, ∀ p ∈ D, ∀ q ∈ D,
            angularDist (accelerated X shift clock t p) (accelerated X shift clock t q) ≤ clockCutoff β)) ∧
        (∀ (D : Block n) (hD : D ∈ T.partition k.castSucc),
          let hne := T.block_nonempty _ _ hD
          BlockGeometry.blockMean D hne (accelerated X shift clock t₂) ≠ 0 ∧ ∃ z₀ : Sphere d,
            z₀.val = ‖BlockGeometry.blockMean D hne (accelerated X shift clock t₂)‖⁻¹ •
              BlockGeometry.blockMean D hne (accelerated X shift clock t₂) ∧
            ∀ t ∈ Icc t₂ snext,
              BlockGeometry.blockMean D hne (accelerated X shift clock t) ≠ 0 ∧ ∃ z : Sphere d,
                z.val = ‖BlockGeometry.blockMean D hne (accelerated X shift clock t)‖⁻¹ •
                  BlockGeometry.blockMean D hne (accelerated X shift clock t) ∧
                angularDist z z₀ ≤ 4 * clockCutoff β) := by
  have hκ0 : 0 < κ := (by norm_num : (0 : ℝ) < 4).trans
    ((PlateauStability.kappaThreshold_gt_four n).trans hκ)
  obtain ⟨K, hK, A, hA, hcompletion⟩ := CompletionCollision.stage_completion T hN C hC κ hκ model l
  obtain ⟨B, hB, hrestart⟩ := PostMergeStep.tightening_from_caps T hN C hC k κ CStar hκ0 hCStar
  obtain ⟨E, hE⟩ := eventually_atTop.mp (eventually_clock_parameters κ 1 hκ0 (by norm_num))
  refine ⟨K, hK, max A (max B E), hA.trans_le (le_max_left _ _), ?_⟩
  intro β hβ M hM X hX shift hshift clock hc s hs i j hi hj hd0 hc0
  have hβA := (le_max_left A (max B E)).trans hβ
  have hβB := (le_max_left B E).trans ((le_max_right A (max B E)).trans hβ)
  have hβE := (le_max_right B E).trans ((le_max_right A (max B E)).trans hβ)
  have hM0 : M ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 4) := ⟨hM.1, by linarith only [hM.2]⟩
  have hM1 : M + 1 ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 4) :=
    ⟨by linarith only [hM.1], by linarith only [hM.2]⟩
  obtain ⟨t₁, ht₁, t₂, ht₂, _, hleast₁, herr, hleast₂, _, hgeometry, _, _⟩ :=
    hcompletion β hβA M hM0 X hX shift hshift clock hc s hs i j hi hj hd0 hc0
  have hst₂ : s ≤ t₂ := ht₁.1.le.trans ht₂.1.le
  have ht₂0 := hs.trans hst₂
  have hsmall := (hE β hβE).2.2.1
  obtain ⟨hdiam₂, hcaps₂⟩ := NextStageGeometry.completed_partition T C l k hk β κ (M + 1)
    (accelerated X shift clock t₂) (hgeometry t₂ ⟨hst₂, le_rfl⟩).1 hsmall hleast₂.1.2
  obtain ⟨snext, hnext, hdef, hclocknext, hduration, hratio, hpost, hfinal, hcenters⟩ :=
    hrestart β hβB (M + 1) hM1 model X hX shift hshift clock hc t₂ ht₂0 hdiam₂ hcaps₂
  have htime : |snext - s - 1 / (2 * stageRate model T l)| ≤
      (K + 20 * n + 1) * (Real.log (Real.log β) / Real.log β) := by
    have ht₂len : t₂ - t₁ ≤ 20 * n * (Real.log (Real.log β) / Real.log β) := by
      linarith only [ht₂.2]
    have hsum : snext - s - 1 / (2 * stageRate model T l) =
        ((t₁ - s - 1 / (2 * stageRate model T l)) + (t₂ - t₁)) + (snext - t₂) := by ring
    rw [hsum]
    have htri := abs_add_le ((t₁ - s - 1 / (2 * stageRate model T l)) + (t₂ - t₁)) (snext - t₂)
    have htri' := abs_add_le (t₁ - s - 1 / (2 * stageRate model T l)) (t₂ - t₁)
    rw [abs_of_nonneg (sub_nonneg.mpr ht₂.1.le)] at htri'
    rw [abs_of_nonneg (sub_nonneg.mpr hnext)] at htri
    nlinarith only [htri, htri', herr, ht₂len, hratio]
  refine ⟨t₁, ht₁, t₂, ht₂, snext, hnext, hleast₁, hleast₂, herr, hdef, hclocknext,
    hduration, htime, fun t ht => (hgeometry t ht).1, hfinal, ?_, hcenters⟩
  simpa only [show M + 1 + 1 = M + 2 by ring] using hpost

end Metastability.StageRestart
