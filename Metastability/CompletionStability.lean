import Metastability.PlateauStability
import Metastability.CompletionCaps
import Metastability.CompletionTightness

/-! Closed stage stability from prepared entry data until parent completion.
The half-open noncompletion condition permits completion at the right endpoint;
all cap, diameter and active-upper stopping hypotheses are derived. -/
noncomputable section
open Set
open scoped RealInnerProductSpace
namespace Metastability.CompletionStability
open Source CapEnlargement ActiveScales ActiveSourceLaw PlateauStability
variable {n N d : ℕ}

theorem stopped_interval (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) (κ : ℝ) (hκ : kappaThreshold n < κ) :
    ∃ β₀ : ℝ, 1 < β₀ ∧ ∀ β ≥ β₀,
      ∀ M ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 4),
      ∀ (model : Model) (l : Fin N) (X : ℝ → Configuration n d), Solves model β X →
      ∀ shift : ℝ, 0 ≤ shift → ∀ clock : ℝ → ℝ, ClockRelation β X shift clock →
      ∀ i j : Fin n, i ∈ T.left l → j ∈ T.right l →
      ∀ a b : ℝ, 0 ≤ a → a ≤ b → b - a ≤ 2 * ((n : ℝ) + 1) →
      (∀ D ∈ T.partition l.castSucc, ∀ p ∈ D, ∀ q ∈ D,
        angularDist (accelerated X shift clock a p) (accelerated X shift clock a q) ≤
          Real.exp (-2 * κ * β)) →
      (∀ (D : Block n) (hD : D ∈ T.partition l.castSucc), ∀ p ∈ D,
        angularDist (accelerated X shift clock a p) (C (T.currentNode l D hD)).center ≤
          (C (T.currentNode l D hD)).radius + M * enlargementScale β) →
      (∀ t ∈ Ico a b, ¬ ∀ p ∈ T.parent l, ∀ q ∈ T.parent l,
        angularDist (accelerated X shift clock t p) (accelerated X shift clock t q) ≤ clockCutoff β) →
      ∀ t ∈ Icc a b,
        StageHyp T C β κ (M + 1) l (accelerated X shift clock t) ∧
        1 - ⟪(accelerated X shift clock t i).val, (accelerated X shift clock t j).val⟫ ≤
          upperBarrier C l + treeMargin hN C := by
  have hκ4 := (kappaThreshold_gt_four n).trans hκ
  have hκd : 10 * PlateauIntegral.diameterConstant n + 3 < κ := by
    unfold kappaThreshold at hκ
    linarith only [hκ]
  obtain ⟨E, hE, hentry⟩ := PlateauEntry.conditions T hN C hC
  obtain ⟨P, hP, hcaps⟩ := CompletionCaps.cap_margin T hN C hC κ hκ4
  obtain ⟨D, hD, hdiam⟩ := CompletionTightness.strict_diameter T hN C hC κ hκ4 hκd
  obtain ⟨S, hS, hscalar⟩ := CompletionScalar.interval_bounds T hN C hC κ hκ4
  refine ⟨max (max E P) (max D S), hE.trans_le ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro β hβ M hM model l X hX shift hshift clock hc i j hi hj a b ha hab hlen hd0 hc0 hnoncomplete
  have hβE := (le_max_left E P).trans ((le_max_left _ _).trans hβ)
  have hβP := (le_max_right E P).trans ((le_max_left _ _).trans hβ)
  have hβD := (le_max_left D S).trans ((le_max_right _ _).trans hβ)
  have hβS := (le_max_right D S).trans ((le_max_right _ _).trans hβ)
  have hβ1 := hE.trans_le hβE
  have hM1 : M + 1 ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 5) :=
    ⟨by linarith only [hM.1], by linarith only [hM.2]⟩
  obtain ⟨hstart, hupper0⟩ := hentry β hβE M hM κ (by linarith only [hκ4]) l
    (accelerated X shift clock a) hd0 hc0
  have hu0 := hupper0 i j hi hj
  have hδ := (treeMargin_pos hN C hC).le
  have hclosed := PlateauRegion.persist_of_strict_improvement T hN C β κ (M + 1) l i j
    (accelerated X shift clock) a b hab
    (fun p => (PlateauRegion.accelerated_continuous model β hβ1 X hX shift hshift clock hc p).mono
      (fun t ht => ha.trans ht.1))
    ⟨hstart, by linarith only [hu0, hδ]⟩ (by
      intro e he hstop
      have heNoncomplete : ∀ t ∈ Ico a e, ¬ ∀ p ∈ T.parent l, ∀ q ∈ T.parent l,
          angularDist (accelerated X shift clock t p) (accelerated X shift clock t q) ≤ clockCutoff β :=
        fun t ht => hnoncomplete t ⟨ht.1, ht.2.trans_le he.2⟩
      have heLen : e - a ≤ 2 * ((n : ℝ) + 1) := by linarith only [he.2, hlen]
      have hst := fun t ht => (hstop t ht).1
      have hup := fun t ht => (hstop t ht).2
      have hdm := hdiam β hβD (M + 1) hM1 model l X hX shift hshift clock hc
        i j hi hj a e ha he.1 heLen hd0 hst hup heNoncomplete e ⟨he.1, le_rfl⟩
      obtain ⟨hcp, hpp⟩ := (hcaps β hβP M hM).2 model l X hX shift hshift clock hc
        i j hi hj a e ha he.1 heLen hc0 hst hup heNoncomplete e ⟨he.1, le_rfl⟩
      have hmono := (hscalar β hβS (M + 1) hM1 model l X hX shift hshift clock hc
        i j hi hj a e ha he.1 hst hup heNoncomplete).1
      have hu := (PlateauScalar.retains_entry_upper T hN C hC l X shift clock i j
        a e he.1 hmono hu0 e ⟨he.1, le_rfl⟩).2
      exact PlateauRegion.positive T hN C β κ (M + 1) l i j
        (accelerated X shift clock e) hdm hcp hpp hu)
  have hmono := (hscalar β hβS (M + 1) hM1 model l X hX shift hshift clock hc
    i j hi hj a b ha hab (fun t ht => (hclosed t ht).1)
    (fun t ht => (hclosed t ht).2) hnoncomplete).1
  intro t ht
  exact ⟨(hclosed t ht).1, (PlateauScalar.retains_entry_upper T hN C hC l X shift clock i j
    a b hab hmono hu0 t ht).1⟩


end Metastability.CompletionStability
