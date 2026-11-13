import Metastability.SourceDefinitions
import Mathlib.Order.Fin.Basic

/-!
# Arithmetic of the prescribed collision tree

The source partitions alone determine positive stage rates, strictly increasing
jump times, and the energy increments. Partition cardinality identities and
rate positivity are proved here rather than supplied as extra assumptions.
This is infrastructure for the general collision tree, not a cascade proof.
-/

noncomputable section
open scoped BigOperators
open Set

namespace Metastability.TreeDynamics

open Source

variable {n N : ℕ} (T : CollisionTree n N)

include T in
/-- A nonempty final block forces a positive particle number, even if `N=0`. -/
theorem particle_pos : 0 < n := by
  have hm : (Finset.univ : Block n) ∈ T.partition (Fin.last N) := by
    rw [T.final_partition]
    exact Finset.mem_singleton_self _
  have hc := Finset.card_pos.mpr (T.block_nonempty _ _ hm)
  simpa only [Finset.card_univ, Fintype.card_fin] using hc

theorem children_disjoint (l : Fin N) : Disjoint (T.left l) (T.right l) :=
  T.block_disjoint _ _ _ (T.left_mem l) (T.right_mem l) (T.children_ne l)

theorem left_card_pos (l : Fin N) : 0 < (T.left l).card :=
  Finset.card_pos.mpr (T.block_nonempty _ _ (T.left_mem l))

theorem right_card_pos (l : Fin N) : 0 < (T.right l).card :=
  Finset.card_pos.mpr (T.block_nonempty _ _ (T.right_mem l))

theorem parent_card (l : Fin N) : (T.parent l).card = (T.left l).card + (T.right l).card :=
  Finset.card_union_of_disjoint (children_disjoint T l)

/-- The cardinalities of the blocks sum to the number of particle labels. -/
theorem sum_card_partition (l : Fin (N + 1)) :
    ∑ D ∈ T.partition l, D.card = n := by
  have hd : (T.partition l : Set (Block n)).PairwiseDisjoint id := by
    intro D hD E hE hne
    exact T.block_disjoint l D E hD hE hne
  have hc := Finset.card_biUnion hd
  rw [T.partition_cover l] at hc
  simpa only [Finset.card_univ, Fintype.card_fin, id_eq] using hc.symm

theorem sum_card_partition_real (l : Fin (N + 1)) :
    ∑ D ∈ T.partition l, (D.card : ℝ) = n := by
  exact_mod_cast sum_card_partition T l

theorem block_card_le (D : Block n) : D.card ≤ n := by
  simpa only [Finset.card_univ, Fintype.card_fin] using
    Finset.card_le_card (Finset.subset_univ D)

/-- Both normalizations in the source give positive stage rates. -/
theorem stageRate_pos (model : Model) (l : Fin N) : 0 < stageRate model T l := by
  have hn : (0 : ℝ) < n := by exact_mod_cast particle_pos T
  have hB : (0 : ℝ) < (T.left l).card := by exact_mod_cast left_card_pos T l
  have hC : (0 : ℝ) < (T.right l).card := by exact_mod_cast right_card_pos T l
  cases model <;> simp only [stageRate] <;> positivity

theorem stageDuration_pos (model : Model) (l : Fin N) :
    0 < 1 / (2 * stageRate model T l) :=
  div_pos zero_lt_one (mul_pos (by norm_num) (stageRate_pos T model l))

theorem jumpTime_zero (model : Model) : jumpTime model T 0 = 0 := by
  simp only [jumpTime, Fin.val_zero, Nat.not_lt_zero, ↓reduceIte, Finset.sum_const_zero]

/-- The finite-sum definition satisfies the source recursion exactly. -/
theorem jumpTime_succ (model : Model) (l : Fin N) :
    jumpTime model T l.succ =
      jumpTime model T l.castSucc + 1 / (2 * stageRate model T l) := by
  have hterm : ∀ k : Fin N,
      (if k.val < l.succ.val then 1 / (2 * stageRate model T k) else 0) =
        (if k.val < l.castSucc.val then 1 / (2 * stageRate model T k) else 0) +
        (if k = l then 1 / (2 * stageRate model T l) else 0) := by
    intro k
    by_cases hkl : k = l
    · subst k
      simp only [Fin.val_succ, Fin.val_castSucc, Nat.lt_succ_self, lt_self_iff_false,
        ↓reduceIte, zero_add]
    · have hv : k.val ≠ l.val := fun h => hkl (Fin.ext h)
      have hh : k.val < l.val + 1 ↔ k.val < l.val := by omega
      simp only [Fin.val_succ, Fin.val_castSucc, hh, hkl, ↓reduceIte, add_zero]
      rfl
  simp only [jumpTime, hterm, Finset.sum_add_distrib]
  simp

theorem jumpTime_strictMono (model : Model) : StrictMono (jumpTime model T) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro l
  rw [jumpTime_succ T model l]
  exact lt_add_of_pos_right _ (stageDuration_pos T model l)

theorem jumpTime_nonneg (model : Model) (l : Fin (N + 1)) :
    0 ≤ jumpTime model T l := by
  have h := (jumpTime_strictMono T model).monotone (Fin.zero_le l)
  rwa [jumpTime_zero T model] at h

theorem plateauEnergy_nonneg (l : Fin (N + 1)) : 0 ≤ plateauEnergy T l := by
  unfold plateauEnergy
  positivity

theorem plateauEnergy_le_one (l : Fin (N + 1)) : plateauEnergy T l ≤ 1 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast particle_pos T
  have hs : (∑ D ∈ T.partition l, (D.card : ℝ) ^ 2) ≤ (n : ℝ) ^ 2 := by
    calc
      (∑ D ∈ T.partition l, (D.card : ℝ) ^ 2) ≤
          ∑ D ∈ T.partition l, (n : ℝ) * D.card := by
        apply Finset.sum_le_sum
        intro D _
        have hD : (D.card : ℝ) ≤ n := by exact_mod_cast block_card_le (n := n) D
        simpa only [pow_two] using mul_le_mul_of_nonneg_right hD (Nat.cast_nonneg D.card)
      _ = (n : ℝ) ^ 2 := by
        rw [← Finset.mul_sum, sum_card_partition_real T l]
        ring
  exact (div_le_one (sq_pos_of_pos hn)).mpr hs

theorem plateauEnergy_final : plateauEnergy T (Fin.last N) = 1 := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (particle_pos T).ne'
  simp only [plateauEnergy, T.final_partition, Finset.sum_singleton,
    Finset.card_univ, Fintype.card_fin]
  exact div_self (pow_ne_zero 2 hn)

/-- The newly merged block is not already an element of the old partition. -/
theorem parent_not_mem_current (l : Fin N) : T.parent l ∉ T.partition l.castSucc := by
  intro hp
  by_cases hB : T.parent l = T.left l
  · obtain ⟨i, hi⟩ := T.block_nonempty _ _ (T.right_mem l)
    have hip : i ∈ T.parent l := Finset.mem_union_right _ hi
    rw [hB] at hip
    exact Finset.disjoint_left.mp (children_disjoint T l) hip hi
  · obtain ⟨i, hi⟩ := T.block_nonempty _ _ (T.left_mem l)
    have hd := T.block_disjoint _ _ _ hp (T.left_mem l) hB
    exact Finset.disjoint_left.mp hd (Finset.mem_union_left _ hi) hi

/-- Exact update of any real-valued block sum under a prescribed binary merge. -/
theorem sum_partition_succ (f : Block n → ℝ) (l : Fin N) :
    ∑ D ∈ T.partition l.succ, f D =
      (∑ D ∈ T.partition l.castSucc, f D) - f (T.left l) - f (T.right l) +
        f (T.parent l) := by
  have hC : T.right l ∈ (T.partition l.castSucc).erase (T.left l) :=
    Finset.mem_erase.mpr ⟨(T.children_ne l).symm, T.right_mem l⟩
  have hp : T.parent l ∉ ((T.partition l.castSucc).erase (T.left l)).erase (T.right l) := by
    intro h
    exact parent_not_mem_current T l (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))
  have hBsum := Finset.sum_erase_add (T.partition l.castSucc) f (T.left_mem l)
  have hCsum := Finset.sum_erase_add ((T.partition l.castSucc).erase (T.left l)) f hC
  rw [T.merge l]
  change (∑ D ∈ insert (T.parent l)
    (((T.partition l.castSucc).erase (T.left l)).erase (T.right l)), f D) = _
  rw [Finset.sum_insert hp]
  change f (T.parent l) + _ = _
  linarith only [hBsum, hCsum]

/-- Each merge raises the source energy plateau by precisely the cross mass. -/
theorem plateauEnergy_succ (l : Fin N) :
    plateauEnergy T l.succ = plateauEnergy T l.castSucc +
      (2 * (T.left l).card * (T.right l).card : ℝ) / (n : ℝ) ^ 2 := by
  have hc : ((T.parent l).card : ℝ) = (T.left l).card + (T.right l).card := by
    exact_mod_cast parent_card T l
  unfold plateauEnergy
  rw [sum_partition_succ T (fun D => (D.card : ℝ) ^ 2) l, hc]
  ring

theorem plateauEnergy_lt_succ (l : Fin N) :
    plateauEnergy T l.castSucc < plateauEnergy T l.succ := by
  have hn : (0 : ℝ) < n := by exact_mod_cast particle_pos T
  have hB : (0 : ℝ) < (T.left l).card := by exact_mod_cast left_card_pos T l
  have hC : (0 : ℝ) < (T.right l).card := by exact_mod_cast right_card_pos T l
  rw [plateauEnergy_succ T l]
  apply lt_add_of_pos_right
  positivity

theorem plateauEnergy_strictMono : StrictMono (plateauEnergy T) :=
  Fin.strictMono_iff_lt_succ.mpr (plateauEnergy_lt_succ T)

/-- The finitely many strict source gaps admit a common positive margin with
the paper's factor eight. No quantitative separation is added as a premise. -/
theorem exists_uniform_gap_margin (hN : 0 < N) {d : ℕ}
    (C : TreeCaps T d) (hC : StrictlyPrepared C) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ l : Fin N,
      previousUpperBarrier C l + 8 * δ ≤ lowerBarrier C l ∧
      upperBarrier C l + 8 * δ ≤ outsideBarrier C l := by
  classical
  let g : Fin N → ℝ := fun l =>
    min (lowerBarrier C l - previousUpperBarrier C l)
      (outsideBarrier C l - upperBarrier C l)
  let S : Finset ℝ := Finset.univ.image g
  have hS : S.Nonempty := Finset.Nonempty.image
    ⟨(⟨0, hN⟩ : Fin N), Finset.mem_univ _⟩ g
  have hpos : 0 < S.min' hS := by
    obtain ⟨l, _, heq⟩ := Finset.mem_image.mp (Finset.min'_mem S hS)
    rw [← heq]
    obtain ⟨_, _, _, hprevious, _, houtside⟩ := hC.2 l
    exact lt_min (sub_pos.mpr hprevious) (sub_pos.mpr houtside)
  refine ⟨S.min' hS / 8, div_pos hpos (by norm_num), ?_⟩
  intro l
  have hb : S.min' hS ≤ g l :=
    Finset.min'_le S (g l) (Finset.mem_image.mpr ⟨l, Finset.mem_univ _, rfl⟩)
  have hl := hb.trans (min_le_left _ _)
  have hr := hb.trans (min_le_right _ _)
  constructor
  · linarith only [hl]
  · linarith only [hr]

end Metastability.TreeDynamics
