import Metastability.CompletionIntegral
import Metastability.PlateauTightness

/-! Strict block tightness from original stage entry through parent completion.
The initial reserve and the integrated exterior estimate are used over the
whole stage, without restarting at a weaker mesoscopic entry diameter. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace
namespace Metastability.CompletionTightness
open Source ActiveScales ActiveSourceLaw CapEnlargement PlateauScalar PlateauIntegral PlateauTightness
variable {n N d : ℕ}

theorem strict_diameter (T : CollisionTree n N) (hN : 0 < N) (C : TreeCaps T d)
    (hC : StrictlyPrepared C) (κ : ℝ) (hκ : 4 < κ)
    (hκdiam : 10 * diameterConstant n + 3 < κ) :
    ∃ β₀ : ℝ, 1 < β₀ ∧ ∀ β ≥ β₀,
      ∀ M ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 5), ∀ (model : Model) (l : Fin N)
      (X : ℝ → Configuration n d), Solves model β X →
      ∀ shift : ℝ, 0 ≤ shift → ∀ clock : ℝ → ℝ, ClockRelation β X shift clock →
      ∀ i j : Fin n, i ∈ T.left l → j ∈ T.right l →
      ∀ a b : ℝ, 0 ≤ a → a ≤ b → b - a ≤ 2 * ((n : ℝ) + 1) →
      (∀ D ∈ T.partition l.castSucc, ∀ p ∈ D, ∀ q ∈ D,
        angularDist (accelerated X shift clock a p) (accelerated X shift clock a q) ≤
          Real.exp (-2 * κ * β)) →
      (∀ t ∈ Icc a b, StageHyp T C β κ M l (accelerated X shift clock t)) →
      (∀ t ∈ Icc a b, 1 - correlation X shift clock i j t ≤
        upperBarrier C l + 2 * treeMargin hN C) →
      (∀ t ∈ Ico a b, ¬ ∀ p ∈ T.parent l, ∀ q ∈ T.parent l,
        angularDist (accelerated X shift clock t p) (accelerated X shift clock t q) ≤ clockCutoff β) →
      ∀ t ∈ Icc a b, ∀ D ∈ T.partition l.castSucc, ∀ p ∈ D, ∀ q ∈ D,
        angularDist (accelerated X shift clock t p) (accelerated X shift clock t q) <
          Real.exp (-κ * β) := by
  obtain ⟨B, hB, hint⟩ := CompletionIntegral.exterior_integral_bound T hN C hC κ hκ
  have hn := TreeDynamics.particle_pos T
  have hκ0 : 0 < κ := by linarith only [hκ]
  have he : Tendsto (fun β : ℝ => 4 * Real.exp (-κ * β)) atTop (𝓝 0) := by
    have ht : Tendsto (fun β : ℝ => Real.exp (-κ * β)) atTop (𝓝 0) := by
      simpa only [Real.rpow_zero, one_mul] using
        tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 κ hκ0
    simpa only [mul_zero] using ht.const_mul 4
  obtain ⟨S, hS⟩ := eventually_atTop.mp
    ((ContractionScale.eventually_visibleScale_small n hn).and
      ((eventually_exp_le_visible κ hκ0).and (he.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)))))
  refine ⟨max B S, hB.trans_le (le_max_left _ _), ?_⟩
  intro β hβ M hM model l X hX shift hshift clock hc i j hi hj a b ha hab hlen hentry hstage hupper hnoncomplete t ht D hD p hp q hq
  have hβB : B ≤ β := (le_max_left _ _).trans hβ
  obtain ⟨⟨hβ1, hε0, hε1, hβε⟩, hδ, hsmall⟩ := hS β ((le_max_right _ _).trans hβ)
  have hβ0 : 0 ≤ β := by linarith only [hβ1]
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
  have hlen' : t - a ≤ 2 * ((n : ℝ) + 1) := by linarith only [ht.2, hlen]
  have hint' := hint β hβB M hM model l X hX shift hshift clock hc i j hi hj a t ha ht.1 hlen'
    (fun s hs => hstage s (hsub hs)) (fun s hs => hupper s (hsub hs))
    (fun s hs => hnoncomplete s ⟨hs.1, hs.2.trans_le ht.2⟩) D hD
  have hτa : 0 ≤ shift + clock a := add_nonneg hshift (hc.1.2.1 a ha)
  have hτat : shift + clock a ≤ shift + clock t :=
    add_le_add le_rfl (hc.2.1.monotoneOn ha (ha.trans ht.1) ht.1)
  have hdiam : ∀ u ∈ Icc (shift + clock a) (shift + clock t), ∀ p ∈ D, ∀ q ∈ D,
      angularDist (X u p) (X u q) ≤ visibleScale β := by
    intro u hu p hp q hq
    obtain ⟨s, hs, rfl⟩ := PlateauClockTransfer.exists_time_Icc hc ha ht.1 hu
    exact ((hstage s (hsub hs)).1 D hD p hp q hq).trans hδ
  have hg := ContractionDynamics.interval_gronwall hn model β hβ0 (visibleScale β) hε0.le hε1 hβε
    X hX D (T.block_nonempty _ _ hD) hτa hdiam p q hp hq ⟨hτat, le_rfl⟩
  have heinit : PairDeficit.deficit (X (shift + clock a)) p q ≤ Real.exp (-4 * κ * β) := by
    have hq0 := ContractionScale.deficit_le_half_sq_of_angularDist_le
      (X (shift + clock a)) p q (Real.exp (-2 * κ * β)) (hentry D hD p hp q hq)
    have hex : Real.exp (-2 * κ * β) ^ 2 = Real.exp (-4 * κ * β) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [hex] at hq0
    exact hq0.trans (by linarith only [Real.exp_pos (-4 * κ * β)])
  have hgr : PairDeficit.deficit (accelerated X shift clock t) p q ≤
      Real.exp (-4 * κ * β) * Real.exp (10 * diameterConstant n * β) := by
    apply hg.trans
    have hcpos : 0 ≤ 1 / (4 * (n : ℝ)) := by positivity
    have hexp := Real.exp_le_exp.mpr (show
        -(1 / (4 * (n : ℝ))) * ((shift + clock t) - (shift + clock a)) +
          10 * (∫ u in (shift + clock a)..(shift + clock t),
            ContractionInteraction.exterior β (X u) D (T.block_nonempty _ _ hD)) ≤
          10 * diameterConstant n * β from by
      nlinarith only [hint', mul_nonneg hcpos (sub_nonneg.mpr hτat)])
    exact mul_le_mul heinit hexp (Real.exp_pos _).le (Real.exp_pos _).le
  apply strict_angle_of_deficit_bound β κ (diameterConstant n) hβ0
    (by linarith only [hκdiam]) hsmall (accelerated X shift clock t) p q
    (((hstage t ht).1 D hD p hp q hq).trans (hδ.trans hε1)) hgr


end Metastability.CompletionTightness
