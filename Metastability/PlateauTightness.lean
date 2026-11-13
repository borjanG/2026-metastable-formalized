import Metastability.PlateauIntegral
import Metastability.PlateauClockTransfer
import Metastability.ContractionDynamics

/-!
# Strict block tightness on a stopped active plateau

Entry diameter is exp(-2 kappa beta). The source exterior integral and the
original-time contraction theorem improve the stopped exp(-kappa beta) bound
strictly. All low-temperature conditions are produced by a uniform threshold.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace

namespace Metastability.PlateauTightness
open Source ActiveScales ActiveSourceLaw CapEnlargement PlateauScalar PlateauIntegral
variable {n N d : ℕ}

/-- The exponential block scale lies within the source visible scale. -/
theorem eventually_exp_le_visible (κ : ℝ) (hκ : 0 < κ) :
    ∀ᶠ β : ℝ in atTop, Real.exp (-κ * β) ≤ visibleScale β := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    eventually_mul_exp_le_rpow 1 κ 1 0 hκ] with β hβ hs
  simp only [one_mul, Real.rpow_one, Real.rpow_zero] at hs
  have he : Real.exp (-κ * β) ≤ 1 / β := by
    apply (le_div_iff₀ (zero_lt_one.trans hβ)).mpr
    nlinarith only [hs]
  have hcut := inv_four_beta_le_clockCutoff hβ
  rw [clockCutoff] at hcut
  have hid : 1 / (4 * β) = (1 / β) / 4 := by ring
  rw [hid] at hcut
  linarith only [he, hcut]

/-- A numerical comparison used after the actual original-time Gronwall bound. -/
theorem strict_angle_of_deficit_bound (β κ C : ℝ) (hβ : 0 ≤ β)
    (hκC : 10 * C ≤ κ) (hsmall : 4 * Real.exp (-κ * β) < 1)
    (x : Configuration n d) (p q : Fin n)
    (hangle : angularDist (x p) (x q) ≤ 1)
    (hq : PairDeficit.deficit x p q ≤ Real.exp (-4 * κ * β) * Real.exp (10 * C * β)) :
    angularDist (x p) (x q) < Real.exp (-κ * β) := by
  have hq' : PairDeficit.deficit x p q ≤ Real.exp (-3 * κ * β) := by
    apply hq.trans
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_right hκC hβ]
  have hs := ContractionScale.angularDist_sq_le_four_mul_deficit x p q hangle
  have hexp : Real.exp (-3 * κ * β) = Real.exp (-κ * β) * Real.exp (-2 * κ * β) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hstrict : 4 * Real.exp (-3 * κ * β) < Real.exp (-2 * κ * β) := by
    rw [hexp]
    nlinarith only [mul_lt_mul_of_pos_right hsmall (Real.exp_pos (-2 * κ * β))]
  have heq : Real.exp (-2 * κ * β) = Real.exp (-κ * β) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [heq] at hstrict
  have hnonneg := AngularGeometry.angularDist_nonneg (x p) (x q)
  nlinarith only [hs, hq', hstrict, hnonneg, Real.exp_pos (-κ * β)]

/-- Source-facing strict diameter preservation. The constant in the standing
kappa condition depends only on the particle count, before the stage, model,
dimension, trajectory, and representatives are chosen. -/
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
      (∀ t ∈ Icc a b, mesoscopicScale β ≤
        angularDist (accelerated X shift clock t i) (accelerated X shift clock t j)) →
      ∀ t ∈ Icc a b, ∀ D ∈ T.partition l.castSucc, ∀ p ∈ D, ∀ q ∈ D,
        angularDist (accelerated X shift clock t p) (accelerated X shift clock t q) <
          Real.exp (-κ * β) := by
  obtain ⟨B, hB, hint⟩ := exterior_integral_bound T hN C hC κ hκ
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
  intro β hβ M hM model l X hX shift hshift clock hc i j hi hj a b ha hab hlen hentry hstage hupper hangle t ht D hD p hp q hq
  have hβB : B ≤ β := (le_max_left _ _).trans hβ
  obtain ⟨⟨hβ1, hε0, hε1, hβε⟩, hδ, hsmall⟩ := hS β ((le_max_right _ _).trans hβ)
  have hβ0 : 0 ≤ β := by linarith only [hβ1]
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
  have hlen' : t - a ≤ 2 * ((n : ℝ) + 1) := by linarith only [ht.2, hlen]
  have hint' := hint β hβB M hM model l X hX shift hshift clock hc i j hi hj a t ha ht.1 hlen'
    (fun s hs => hstage s (hsub hs)) (fun s hs => hupper s (hsub hs))
    (fun s hs => hangle s (hsub hs)) D hD
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

end Metastability.PlateauTightness
