import Metastability.TreeCapEnlargement

/-!
# Source stage geometry and nonactive-pair barriers

The hypotheses are the manuscript's literal cap containment inequalities.
All exterior and nonactive pair barriers are derived from the prepared tree,
including the case in which the active parent is the full particle set.
-/

noncomputable section
open Set
open scoped RealInnerProductSpace

namespace Metastability.ActiveGeometry

open Source CapEnlargement
variable {n N d : ℕ}

/-- The two orientations of an active cross pair at a prescribed stage. -/
def IsActiveCross (T : CollisionTree n N) (l : Fin N) (i j : Fin n) : Prop :=
  (i ∈ T.left l ∧ j ∈ T.right l) ∨ (i ∈ T.right l ∧ j ∈ T.left l)

theorem isActiveCross_symm (T : CollisionTree n N) (l : Fin N) (i j : Fin n) :
    IsActiveCross T l i j ↔ IsActiveCross T l j i := by
  unfold IsActiveCross
  tauto

theorem activeCross_of_mem_parent_of_blocks_ne (T : CollisionTree n N) (l : Fin N)
    (i j : Fin n) (hi : i ∈ T.parent l) (hj : j ∈ T.parent l)
    (hne : T.blockOf l.castSucc i ≠ T.blockOf l.castSucc j) : IsActiveCross T l i j := by
  rcases Finset.mem_union.mp hi with hi | hi <;>
    rcases Finset.mem_union.mp hj with hj | hj
  · exact False.elim (hne ((T.blockOf_unique l.castSucc i (T.left l) (T.left_mem l) hi).symm.trans
      (T.blockOf_unique l.castSucc j (T.left l) (T.left_mem l) hj)))
  · exact Or.inl ⟨hi, hj⟩
  · exact Or.inr ⟨hi, hj⟩
  · exact False.elim (hne ((T.blockOf_unique l.castSucc i (T.right l) (T.right_mem l) hi).symm.trans
      (T.blockOf_unique l.castSucc j (T.right l) (T.right_mem l) hj)))

/-- The cap assumptions H2 and H3 imply every needed exterior and nonactive
pair barrier, with one temperature threshold uniform in stage and M. -/
theorem stage_barriers (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) :
    ∃ β₀ : ℝ, 1 < β₀ ∧ ∀ β ≥ β₀, ∀ M ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 5),
      ∀ (l : Fin N) (x : Configuration n d),
        (∀ (D : Block n) (hD : D ∈ T.partition l.castSucc),
          D ≠ T.left l → D ≠ T.right l → ∀ i ∈ D,
          angularDist (x i) (C (T.currentNode l D hD)).center ≤
            (C (T.currentNode l D hD)).radius + M * enlargementScale β) →
        (∀ hp : T.parent l ≠ Finset.univ, ∀ i ∈ T.parent l,
          angularDist (x i) (C (T.parentNode l hp)).center ≤
            (C (T.parentNode l hp)).radius + M * enlargementScale β) →
        (∀ i ∈ T.parent l, ∀ j ∉ T.parent l,
          upperBarrier C l + 7 * treeMargin hN C ≤ 1 - ⟪(x i).val, (x j).val⟫) ∧
        (∀ i j, T.blockOf l.castSucc i ≠ T.blockOf l.castSucc j →
          ¬ IsActiveCross T l i j →
          upperBarrier C l + 7 * treeMargin hN C ≤ 1 - ⟪(x i).val, (x j).val⟫) := by
  obtain ⟨_, _, _, β₀, hβ₀, hfamily⟩ :=
    TreeCapEnlargement.enlarged_tree_barriers T hN C hC
  refine ⟨β₀, hβ₀, ?_⟩
  intro β hβ M hM l x hother hparent
  obtain ⟨E, hE, _, houtside, hfuture⟩ := hfamily β hβ M hM
  have hotherE : ∀ (D : Block n) (hD : D ∈ T.partition l.castSucc),
      D ≠ T.left l → D ≠ T.right l → ∀ i ∈ D,
        x i ∈ (E (T.currentNode l D hD)).carrier := by
    intro D hD hDl hDr i hi
    change angularDist (x i) (E (T.currentNode l D hD)).center ≤
      (E (T.currentNode l D hD)).radius
    rw [(hE _).1, (hE _).2]
    exact hother D hD hDl hDr i hi
  have hparentE : ∀ hp : T.parent l ≠ Finset.univ, ∀ i ∈ T.parent l,
      x i ∈ (E (T.parentNode l hp)).carrier := by
    intro hp i hi
    change angularDist (x i) (E (T.parentNode l hp)).center ≤ (E (T.parentNode l hp)).radius
    rw [(hE _).1, (hE _).2]
    exact hparent hp i hi
  have hnonactive : ∀ j ∉ T.parent l,
      T.blockOf l.castSucc j ≠ T.left l ∧ T.blockOf l.castSucc j ≠ T.right l := by
    intro j hj
    have hjD := (T.blockOf_spec l.castSucc j).2
    constructor
    · intro heq
      exact hj (Finset.mem_union_left _ (heq ▸ hjD))
    · intro heq
      exact hj (Finset.mem_union_right _ (heq ▸ hjD))
  have hext : ∀ i ∈ T.parent l, ∀ j ∉ T.parent l,
      upperBarrier C l + 7 * treeMargin hN C ≤ 1 - ⟪(x i).val, (x j).val⟫ := by
    intro i hi j hj
    have hp : T.parent l ≠ Finset.univ := by
      intro hp
      exact hj (hp ▸ Finset.mem_univ j)
    let D := T.currentNode l (T.blockOf l.castSucc j) (T.blockOf_spec l.castSucc j).1
    obtain ⟨hDl, hDr⟩ := hnonactive j hj
    have hcap := (houtside l hp D (T.blockOf_spec l.castSucc j).1 hDl hDr).2.2
    have hpoint := min_barrier_le_deficit (E (T.parentNode l hp)) (E D) (x i) (x j)
      (hparentE hp i hi)
      (hotherE _ (T.blockOf_spec l.castSucc j).1 hDl hDr j (T.blockOf_spec l.castSucc j).2)
    simpa only [AngularGeometry.cos_angularDist] using hcap.trans hpoint
  refine ⟨hext, ?_⟩
  intro i j hne hcross
  by_cases hi : i ∈ T.parent l
  · have hj : j ∉ T.parent l := fun hj =>
      hcross (activeCross_of_mem_parent_of_blocks_ne T l i j hi hj hne)
    exact hext i hi j hj
  by_cases hj : j ∈ T.parent l
  · simpa only [real_inner_comm (x j).val (x i).val] using hext j hj i hi
  let D := T.currentNode l (T.blockOf l.castSucc i) (T.blockOf_spec l.castSucc i).1
  let F := T.currentNode l (T.blockOf l.castSucc j) (T.blockOf_spec l.castSucc j).1
  obtain ⟨hDl, hDr⟩ := hnonactive i hi
  obtain ⟨hFl, hFr⟩ := hnonactive j hj
  obtain ⟨_, _, _, _, _, _, hcap⟩ := hfuture l D F
    (T.blockOf_spec l.castSucc i).1 (T.blockOf_spec l.castSucc j).1 hne hDl hDr hFl hFr
  have hpoint := min_barrier_le_deficit (E D) (E F) (x i) (x j)
    (hotherE _ (T.blockOf_spec l.castSucc i).1 hDl hDr i (T.blockOf_spec l.castSucc i).2)
    (hotherE _ (T.blockOf_spec l.castSucc j).1 hFl hFr j (T.blockOf_spec l.castSucc j).2)
  simpa only [AngularGeometry.cos_angularDist] using hcap.trans hpoint

end Metastability.ActiveGeometry
