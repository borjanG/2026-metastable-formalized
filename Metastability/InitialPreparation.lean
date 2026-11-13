import Metastability.PreparedBlocks
import Metastability.TreeSeparation

/-!
# Initial preparation from the manuscript's tree and visible hypotheses

One common time multiplier is chosen from particle count and kappa, before
dimension, tree, caps, model, or trajectory. Static separation is derived
from the tree. The theorem produces cap confinement, exponential tightness,
literal normalized centers, and the exact source clock after the shift.
-/

noncomputable section
open Filter Set
open scoped Topology RealInnerProductSpace

namespace Metastability.InitialPreparation
open Source

/-- The prepared original-time shift obeys the same source equation on the
nonnegative halfline, including its initial endpoint. -/
theorem solves_shift {n d : ℕ} (model : Model) (β : ℝ)
    (X : ℝ → Configuration n d) (hX : Solves model β X)
    (shift : ℝ) (hshift : 0 ≤ shift) :
    Solves model β (fun t => X (shift + t)) := by
  intro t ht i
  have hd := hX (shift + t) (add_nonneg hshift ht) i
  have ha : HasDerivWithinAt (fun u : ℝ => shift + u) 1 (Ici 0) t :=
    ((hasDerivAt_id t).const_add shift).hasDerivWithinAt
  have hcomp := hd.scomp t ha (fun u hu => add_nonneg hshift hu)
  simpa only [one_smul, Function.comp_def] using hcomp

/-- Quantitative initial preparation for both source models. All block centers
have error at most twice the visible scale, uniformly over the blocks and
all visibly prepared solutions. The cap-radius and containment conclusions
refer only to proper initial nodes. -/
theorem initial_preparation_bounds (n : ℕ) (hn : 0 < n) (κ : ℝ) (hκ : 0 < κ) :
    ∃ CStar : ℝ, 0 < CStar ∧ ∀ (N d : ℕ) (T : CollisionTree n N)
      (hN : 0 < N) (C : TreeCaps T d), StrictlyPrepared C →
      ∀ᶠ β : ℝ in atTop, 1 < β ∧
        ∀ (model : Model) (X : ℝ → Configuration n d), Solves model β X →
        VisiblePrepared hN C β (X 0) →
        (∀ (D : Block n) (hD : D ∈ T.partition 0),
          (C (T.currentNode ⟨0, hN⟩ D hD)).radius + β ^ (-(1 : ℝ) / 4) < Real.pi / 2 ∧
          (∀ t ∈ Icc 0 (CStar * β), ∀ i ∈ D,
            angularDist (X t i) (C (T.currentNode ⟨0, hN⟩ D hD)).center ≤
              2 * visibleScale β ∧
            angularDist (X t i) (C (T.currentNode ⟨0, hN⟩ D hD)).center ≤
              (C (T.currentNode ⟨0, hN⟩ D hD)).radius + β ^ (-(1 : ℝ) / 4)) ∧
          (∀ i ∈ D, ∀ j ∈ D,
            angularDist (X (CStar * β) i) (X (CStar * β) j) ≤ Real.exp (-2 * κ * β)) ∧
          BlockGeometry.blockMean D (T.block_nonempty 0 D hD) (X (CStar * β)) ≠ 0 ∧
          ∃ z : Sphere d,
            z.val = ‖BlockGeometry.blockMean D (T.block_nonempty 0 D hD)
              (X (CStar * β))‖⁻¹ •
              BlockGeometry.blockMean D (T.block_nonempty 0 D hD) (X (CStar * β)) ∧
            angularDist z (C (T.currentNode ⟨0, hN⟩ D hD)).center ≤ 2 * visibleScale β) ∧
        ∃ clock : ℝ → ℝ, ClockRelation β X (CStar * β) clock := by
  obtain ⟨CStar, hCStar, hprepare⟩ := PreparedBlocks.prepare_separated_blocks n hn κ hκ
  refine ⟨CStar, hCStar, ?_⟩
  intro N d T hN C hC
  classical
  let I := {D : Block n // D ∈ T.partition 0}
  letI : Fintype I := Fintype.ofFinite I
  let A : I → Block n := fun D => D.val
  have hA : ∀ D, (A D).Nonempty := fun D => T.block_nonempty 0 D.val D.property
  let w : I → Sphere d := fun D => (C (T.currentNode ⟨0, hN⟩ D.val D.property)).center
  have hcover : ∀ i : Fin n, ∃ D, i ∈ A D := by
    intro i
    obtain ⟨D, ⟨hD, hi⟩, _⟩ := T.existsUnique_block 0 i
    exact ⟨⟨D, hD⟩, hi⟩
  obtain ⟨g, hg, hgap⟩ := TreeSeparation.exists_initial_center_barrier T hN C hC
  have hgap' : ∀ D E : I, D ≠ E → g ≤ 1 - ⟪(w D).val, (w E).val⟫ := by
    intro D E hne
    exact hgap D.val D.property E.val E.property (fun heq => hne (Subtype.ext heq))
  have hmain := hprepare d I A hA w hcover g hg hgap'
  have hradius : ∀ᶠ β : ℝ in atTop, ∀ D : I,
      (C (T.currentNode ⟨0, hN⟩ D.val D.property)).radius + β ^ (-(1 : ℝ) / 4) <
        Real.pi / 2 := by
    apply Filter.eventually_all.mpr
    intro D
    have hlim : Tendsto (fun β : ℝ =>
        (C (T.currentNode ⟨0, hN⟩ D.val D.property)).radius + β ^ (-(1 : ℝ) / 4))
        atTop (𝓝 (C (T.currentNode ⟨0, hN⟩ D.val D.property)).radius) := by
      convert (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).const_add
        (C (T.currentNode ⟨0, hN⟩ D.val D.property)).radius using 1 <;> norm_num
    exact hlim.eventually (gt_mem_nhds (C (T.currentNode ⟨0, hN⟩ D.val D.property)).radius_lt_half_pi)
  filter_upwards [hmain, hradius,
    PreparationScale.eventually_doubled_visible_le_quarter_power] with β hmain hradius hquarter
  refine ⟨hmain.1, ?_⟩
  intro model X hX hvisible
  obtain ⟨hcap, hdiam, hmean, hclock⟩ := hmain.2 model X hX
    (fun D => (hvisible D.val D.property).2)
    (fun D => (hvisible D.val D.property).1)
  refine ⟨?_, hclock⟩
  intro D hD
  let α : I := ⟨D, hD⟩
  refine ⟨hradius α, ?_, hdiam α, (hmean α).1, (hmean α).2⟩
  intro t ht i hi
  have hc := hcap t ht α i hi
  refine ⟨hc, hc.trans (hquarter.trans ?_)⟩
  exact le_add_of_nonneg_left (C (T.currentNode ⟨0, hN⟩ D hD)).radius_nonneg

/-- The same common shift yields center convergence uniformly over all initial
blocks and visibly prepared source solutions. Accuracy is chosen before the
temperature threshold and before the model or trajectory. -/
theorem initial_preparation (n : ℕ) (hn : 0 < n) (κ : ℝ) (hκ : 0 < κ) :
    ∃ CStar : ℝ, 0 < CStar ∧ ∀ (N d : ℕ) (T : CollisionTree n N)
      (hN : 0 < N) (C : TreeCaps T d), StrictlyPrepared C →
      ∀ accuracy : ℝ, 0 < accuracy → ∀ᶠ β : ℝ in atTop, 1 < β ∧
        ∀ (model : Model) (X : ℝ → Configuration n d), Solves model β X →
        VisiblePrepared hN C β (X 0) →
        (∀ (D : Block n) (hD : D ∈ T.partition 0),
          (C (T.currentNode ⟨0, hN⟩ D hD)).radius + β ^ (-(1 : ℝ) / 4) < Real.pi / 2 ∧
          (∀ t ∈ Icc 0 (CStar * β), ∀ i ∈ D,
            angularDist (X t i) (C (T.currentNode ⟨0, hN⟩ D hD)).center ≤
              (C (T.currentNode ⟨0, hN⟩ D hD)).radius + β ^ (-(1 : ℝ) / 4)) ∧
          (∀ i ∈ D, ∀ j ∈ D,
            angularDist (X (CStar * β) i) (X (CStar * β) j) ≤ Real.exp (-2 * κ * β)) ∧
          BlockGeometry.blockMean D (T.block_nonempty 0 D hD) (X (CStar * β)) ≠ 0 ∧
          ∃ z : Sphere d,
            z.val = ‖BlockGeometry.blockMean D (T.block_nonempty 0 D hD)
              (X (CStar * β))‖⁻¹ •
              BlockGeometry.blockMean D (T.block_nonempty 0 D hD) (X (CStar * β)) ∧
            angularDist z (C (T.currentNode ⟨0, hN⟩ D hD)).center < accuracy) ∧
        ∃ clock : ℝ → ℝ, ClockRelation β X (CStar * β) clock := by
  obtain ⟨CStar, hCStar, hprepare⟩ := initial_preparation_bounds n hn κ hκ
  refine ⟨CStar, hCStar, ?_⟩
  intro N d T hN C hC accuracy hacc
  have hlim : Tendsto (fun β => 2 * visibleScale β) atTop (𝓝 0) := by
    simpa only [mul_zero] using ContractionScale.tendsto_visibleScale.const_mul 2
  filter_upwards [hprepare N d T hN C hC, hlim.eventually (gt_mem_nhds hacc)] with β hprep hsmall
  refine ⟨hprep.1, ?_⟩
  intro model X hX hvisible
  obtain ⟨hblocks, hclock⟩ := hprep.2 model X hX hvisible
  refine ⟨?_, hclock⟩
  intro D hD
  obtain ⟨hradius, hcap, hdiam, hne, z, hz, hclose⟩ := hblocks D hD
  exact ⟨hradius, fun t ht i hi => (hcap t ht i hi).2, hdiam, hne,
    z, hz, hclose.trans_lt hsmall⟩

end Metastability.InitialPreparation
