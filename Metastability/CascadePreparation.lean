import Metastability.InitialPreparation
import Metastability.PostMergeContraction

/-! Initial preparation with the same admissible multiplier used at every restart. -/
noncomputable section
open Filter Set
open scoped Topology RealInnerProductSpace
namespace Metastability.CascadePreparation
open Source
variable {n N d : ℕ}

/-- The concrete contraction constants permit any admissible common multiplier. -/
theorem visible_tightening (n : ℕ) (hn : 0 < n) (b κ CStar : ℝ)
    (hb : 0 < b) (hκ : 0 < κ) (hC : 8 * κ / (1 / (4 * (n : ℝ))) < CStar) :
    ∀ᶠ β : ℝ in atTop, 1 < β ∧ ∀ (d : ℕ) (model : Model)
      (X : ℝ → Configuration n d), Solves model β X →
      ∀ (A : Block n) (_hA : A.Nonempty),
      (∀ i ∈ A, ∀ j ∈ A, angularDist (X 0 i) (X 0 j) ≤ visibleScale β) →
      (∀ t ∈ Icc 0 (CStar * β), ∀ i ∈ A, ∀ j ∉ A,
        b ≤ 1 - ⟪(X t i).val, (X t j).val⟫) →
      ∀ i ∈ A, ∀ j ∈ A,
        angularDist (X (CStar * β) i) (X (CStar * β) j) ≤ Real.exp (-2 * κ * β) := by
  filter_upwards [ContractionScale.eventually_visibleScale_small n hn,
    BlockContraction.eventually_tightening_parameters n hn b κ CStar hb hC]
    with β hscale htight
  obtain ⟨hβ, hε, hε1, hβε⟩ := hscale
  obtain ⟨hext, hfinal⟩ := htight
  refine ⟨hβ, ?_⟩
  intro d model X hX A hA hstart hsep i hi j hj
  have hβ0 := (zero_lt_one.trans hβ).le
  have hC0 : 0 < CStar := (div_pos (mul_pos (by norm_num) hκ)
    (BlockContraction.contraction_constant_pos n hn)).trans hC
  have htime : CStar * β ∈ Icc 0 (CStar * β) := ⟨mul_nonneg hC0.le hβ0, le_rfl⟩
  have hdecay := ContractionDynamics.confinement_and_decay hn model β hβ0
    (visibleScale β) hε hε1 hβε b hext X hX A hA (le_refl 0) hstart
    (fun t ht _ => hsep t ht)
  have hangle := (hdecay _ htime).1 i hi j hj
  have hq := (hdecay _ htime).2 i hi j hj
  have hinit := ContractionScale.deficit_le_half_sq_of_angularDist_le
    (X 0) i j (visibleScale β) (hstart i hi j hj)
  have hanglesq := ContractionScale.angularDist_sq_le_four_mul_deficit
    (X (CStar * β)) i j (hangle.trans hε1)
  rw [show -(1 / (4 * (n : ℝ)) / 2) * (CStar * β - 0) =
    -(1 / (4 * (n : ℝ))) * CStar * β / 2 by ring] at hq
  have hmul := mul_le_mul_of_nonneg_right hinit
    (Real.exp_pos (-(1 / (4 * (n : ℝ))) * CStar * β / 2)).le
  have hsq : angularDist (X (CStar * β) i) (X (CStar * β) j) ^ 2 ≤
      Real.exp (-4 * κ * β) := by nlinarith only [hanglesq, hq, hmul, hfinal]
  have hexp : Real.exp (-2 * κ * β) ^ 2 = Real.exp (-4 * κ * β) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  nlinarith only [hsq, hexp, Real.exp_pos (-2 * κ * β),
    AngularGeometry.angularDist_nonneg (X (CStar * β) i) (X (CStar * β) j)]

/-- Visible source data yield prepared entry geometry and an actual clock at
any fixed multiplier satisfying the source contraction margin. -/
theorem initial_at_multiplier (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) (κ CStar : ℝ) (hκ : 0 < κ)
    (hCStar : 8 * κ / (1 / (4 * (n : ℝ))) < CStar) :
    ∀ᶠ β : ℝ in atTop, 1 < β ∧
      ∀ (model : Model) (X : ℝ → Configuration n d), Solves model β X →
      VisiblePrepared hN C β (X 0) →
      (∀ (D : Block n) (hD : D ∈ T.partition 0),
        (∀ t ∈ Icc 0 (CStar * β), ∀ i ∈ D,
          angularDist (X t i) (C (T.currentNode ⟨0, hN⟩ D hD)).center ≤
            (C (T.currentNode ⟨0, hN⟩ D hD)).radius + β ^ (-(1 : ℝ) / 4)) ∧
        (∀ i ∈ D, ∀ j ∈ D,
          angularDist (X (CStar * β) i) (X (CStar * β) j) ≤ Real.exp (-2 * κ * β)) ∧
        BlockGeometry.blockMean D (T.block_nonempty 0 D hD) (X (CStar * β)) ≠ 0 ∧
        ∃ z : Sphere d,
          z.val = ‖BlockGeometry.blockMean D (T.block_nonempty 0 D hD)
            (X (CStar * β))‖⁻¹ • BlockGeometry.blockMean D (T.block_nonempty 0 D hD) (X (CStar * β)) ∧
          angularDist z (C (T.currentNode ⟨0, hN⟩ D hD)).center ≤ 2 * visibleScale β) ∧
      ∃ clock : ℝ → ℝ, ClockRelation β X (CStar * β) clock := by
  classical
  have hn := TreeDynamics.particle_pos T
  have hC0 : 0 < CStar := (div_pos (mul_pos (by norm_num) hκ)
    (BlockContraction.contraction_constant_pos n hn)).trans hCStar
  let I := {D : Block n // D ∈ T.partition 0}
  letI : Fintype I := Fintype.ofFinite I
  let A : I → Block n := fun D => D.val
  let w : I → Sphere d := fun D => (C (T.currentNode ⟨0, hN⟩ D.val D.property)).center
  have hA : ∀ D, (A D).Nonempty := fun D => T.block_nonempty 0 D.val D.property
  have hcover : ∀ i : Fin n, ∃ D, i ∈ A D := by
    intro i
    obtain ⟨D, ⟨hD, hi⟩, _⟩ := T.existsUnique_block 0 i
    exact ⟨⟨D, hD⟩, hi⟩
  obtain ⟨g, hg, hgap⟩ := TreeSeparation.exists_initial_center_barrier T hN C hC
  have hgap' : ∀ D E : I, D ≠ E → g ≤ 1 - ⟪(w D).val, (w E).val⟫ := by
    intro D E hne
    exact hgap D.val D.property E.val E.property (fun h => hne (Subtype.ext h))
  filter_upwards [visible_tightening n hn (g / 2) κ CStar (by positivity) hκ hCStar,
    PreparationScale.eventually_preparation_parameters n g CStar hg hC0,
    PreparationScale.eventually_doubled_visible_le_quarter_power] with β hcontract hparam hquarter
  obtain ⟨hβ, hε, _, hεπ, hεg, _, herr⟩ := hparam
  refine ⟨hβ, ?_⟩
  intro model X hX hvisible
  have hβ0 := (zero_lt_one.trans hβ).le
  have htime : 0 ≤ CStar * β := mul_nonneg hC0.le hβ0
  have hsep : ∀ x : Configuration n d,
      (∀ α, ∀ i ∈ A α, angularDist (x i) (w α) ≤ 2 * visibleScale β) →
      ∀ α, ∀ i ∈ A α, ∀ j ∉ A α, g / 2 ≤ 1 - ⟪(x i).val, (x j).val⟫ := by
    intro x hx
    exact PreparationGeometry.exterior_barrier_of_center_separation A w hcover
      g (2 * visibleScale β) hgap' (by linarith only [hεg]) x hx
  have hconf : ∀ t ∈ Icc 0 (CStar * β), ∀ α, ∀ i ∈ A α,
      angularDist (X t i) (w α) ≤ 2 * visibleScale β := by
    have hh := CapNoExit.simultaneous_cap_no_exit model β hβ0 X hX A hA w
      0 (CStar * β) (visibleScale β) (2 * visibleScale β) (g / 2)
      (le_refl 0) htime hε.le (by linarith only [hε]) hεπ
      (fun D => (hvisible D.val D.property).2)
      (fun u _ hu => hsep (X u) hu) (by simpa only [sub_zero] using herr)
    exact fun t ht α i hi => (hh t ht α i hi).1
  refine ⟨?_, GeneralClock.exists_clockRelation β hβ X hX (CStar * β) htime⟩
  intro D hD
  let α : I := ⟨D, hD⟩
  refine ⟨?_, hcontract.2 d model X hX D (T.block_nonempty 0 D hD)
    (hvisible D hD).1 (fun t ht => hsep (X t) (hconf t ht) α), ?_⟩
  · intro t ht i hi
    exact (hconf t ht α i hi).trans (hquarter.trans
      (le_add_of_nonneg_left (C (T.currentNode ⟨0, hN⟩ D hD)).radius_nonneg))
  · exact PreparationGeometry.exists_mean_near_center D (T.block_nonempty 0 D hD)
      (X (CStar * β)) (w α) (2 * visibleScale β) (by positivity) hεπ
      (hconf (CStar * β) ⟨htime, le_rfl⟩ α)

end Metastability.CascadePreparation
