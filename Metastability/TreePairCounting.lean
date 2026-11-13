import Metastability.TreeDynamics

/-!
# Counting pairs in a collision-tree partition

The source energy sums over ordered particle pairs, including diagonal pairs.
The indicator of belonging to the same current block therefore sums to the
sum of squared block cardinalities. All partition properties used below come
from `Source.CollisionTree`; no additional counting identity is assumed.
-/

noncomputable section
open scoped BigOperators
open Set

namespace Metastability.TreePairCounting

open Source

variable {n N : ℕ} (T : CollisionTree n N)

theorem blockOf_eq_iff_mem (l : Fin (N + 1)) (i j : Fin n) :
    T.blockOf l i = T.blockOf l j ↔ j ∈ T.blockOf l i := by
  constructor
  · intro h
    rw [h]
    exact (T.blockOf_spec l j).2
  · intro h
    exact T.blockOf_unique l j (T.blockOf l i) (T.blockOf_spec l i).1 h

/-- For a fixed first label, every label in its block contributes exactly one. -/
theorem sum_same_block_row (l : Fin (N + 1)) (i : Fin n) :
    (∑ j : Fin n, if T.blockOf l i = T.blockOf l j then (1 : ℝ) else 0) =
      ((T.blockOf l i).card : ℝ) := by
  simp_rw [blockOf_eq_iff_mem T l i]
  rw [Finset.sum_ite_mem_eq]
  simp

/-- Exact count of ordered same-block pairs; diagonal pairs are included. -/
theorem sum_same_block_pairs (l : Fin (N + 1)) :
    (∑ i : Fin n, ∑ j : Fin n,
      if T.blockOf l i = T.blockOf l j then (1 : ℝ) else 0) =
        ∑ D ∈ T.partition l, (D.card : ℝ) ^ 2 := by
  have hd : (T.partition l : Set (Block n)).PairwiseDisjoint id := by
    intro D hD E hE hne
    exact T.block_disjoint l D E hD hE hne
  have hs := Finset.sum_biUnion (f := fun i : Fin n => ((T.blockOf l i).card : ℝ)) hd
  rw [T.partition_cover l] at hs
  calc
    _ = ∑ i : Fin n, ((T.blockOf l i).card : ℝ) := by
      exact Finset.sum_congr rfl (fun i _ => sum_same_block_row T l i)
    _ = ∑ D ∈ T.partition l, ∑ i ∈ D, ((T.blockOf l i).card : ℝ) := hs
    _ = ∑ D ∈ T.partition l, (D.card : ℝ) ^ 2 := by
      apply Finset.sum_congr rfl
      intro D hD
      calc
        _ = ∑ _i ∈ D, (D.card : ℝ) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [← T.blockOf_unique l i D hD hi]
        _ = (D.card : ℝ) ^ 2 := by simp [nsmul_eq_mul, pow_two]

/-- The normalized same-block pair indicator is precisely the source plateau. -/
theorem normalized_same_block_pairs (l : Fin (N + 1)) :
    (∑ i : Fin n, ∑ j : Fin n,
      if T.blockOf l i = T.blockOf l j then (1 : ℝ) else 0) / (n : ℝ) ^ 2 =
        plateauEnergy T l := by
  rw [sum_same_block_pairs T l]
  rfl

end Metastability.TreePairCounting
