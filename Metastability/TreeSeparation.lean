import Metastability.TreeDynamics
import Metastability.CapDistances

/-!
# Ancestry and geometric separation in the prescribed collision tree

The coarsening and separating-child facts are derived from the literal merge
rule. Cap containment is then inherited using only the source's proper-node
nesting hypothesis; no cap is attached to the root.
-/

noncomputable section
open Set
open scoped RealInnerProductSpace

namespace Metastability.TreeSeparation

open Source
variable {n N d : ℕ} (T : CollisionTree n N)

theorem successor_block (l : Fin N) (D : Block n) (hD : D ∈ T.partition l.castSucc) :
    ∃ E ∈ T.partition l.succ, D ⊆ E ∧
      (D = E ∨ ((D = T.left l ∨ D = T.right l) ∧ E = T.parent l)) := by
  classical
  by_cases hleft : D = T.left l
  · refine ⟨T.parent l, ?_, ?_, Or.inr ⟨Or.inl hleft, rfl⟩⟩
    · rw [T.merge l]
      exact Finset.mem_insert_self _ _
    · simpa only [hleft, CollisionTree.parent] using Finset.subset_union_left
  by_cases hright : D = T.right l
  · refine ⟨T.parent l, ?_, ?_, Or.inr ⟨Or.inr hright, rfl⟩⟩
    · rw [T.merge l]
      exact Finset.mem_insert_self _ _
    · simpa only [hright, CollisionTree.parent] using Finset.subset_union_right
  refine ⟨D, ?_, Finset.Subset.refl D, Or.inl rfl⟩
  rw [T.merge l]
  exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr
    ⟨hright, Finset.mem_erase.mpr ⟨hleft, hD⟩⟩)

theorem blockOf_subset_succ (l : Fin N) (i : Fin n) :
    T.blockOf l.castSucc i ⊆ T.blockOf l.succ i := by
  obtain ⟨E, hE, hsub, _⟩ := successor_block T l _ (T.blockOf_spec l.castSucc i).1
  have heq := T.blockOf_unique l.succ i E hE (hsub (T.blockOf_spec l.castSucc i).2)
  simpa only [heq] using hsub

theorem blockOf_mono (i : Fin n) : Monotone (fun l => T.blockOf l i) :=
  Fin.monotone_iff_le_succ.mpr (fun l => blockOf_subset_succ T l i)

theorem blockOf_final (i : Fin n) : T.blockOf (Fin.last N) i = Finset.univ := by
  have h := (T.blockOf_spec (Fin.last N) i).1
  simpa only [T.final_partition, Finset.mem_singleton] using h

theorem subset_blockOf_of_mem {l : Fin (N + 1)} {D : Block n}
    (hD : D ∈ T.partition l) {i : Fin n} (hi : i ∈ D) : D = T.blockOf l i :=
  T.blockOf_unique l i D hD hi

theorem exists_coarsening (l m : Fin (N + 1)) (hlm : l ≤ m)
    (D : Block n) (hD : D ∈ T.partition l) :
    ∃ E ∈ T.partition m, D ⊆ E := by
  obtain ⟨i, hi⟩ := T.block_nonempty l D hD
  refine ⟨T.blockOf m i, (T.blockOf_spec m i).1, ?_⟩
  rw [T.blockOf_unique l i D hD hi]
  exact blockOf_mono T i hlm

theorem proper_of_subset {D E : Block n} (hDE : D ⊆ E) (hE : E ≠ Finset.univ) :
    D ≠ Finset.univ := by
  intro hD
  apply hE
  exact Finset.Subset.antisymm (Finset.subset_univ E) (hD ▸ hDE)

theorem cap_subset_succ (C : TreeCaps T d) (hC : StrictlyPrepared C)
    (l : Fin N) (i : Fin n) (hproper : T.blockOf l.succ i ≠ Finset.univ) :
    (C ⟨T.blockOf l.castSucc i, ⟨l.castSucc, (T.blockOf_spec _ i).1⟩,
      proper_of_subset (blockOf_subset_succ T l i) hproper⟩).carrier ⊆
    (C ⟨T.blockOf l.succ i, ⟨l.succ, (T.blockOf_spec _ i).1⟩, hproper⟩).carrier := by
  obtain ⟨E, hE, hsub, hcases⟩ := successor_block T l _ (T.blockOf_spec l.castSucc i).1
  have heq := T.blockOf_unique l.succ i E hE (hsub (T.blockOf_spec l.castSucc i).2)
  rcases hcases with hsame | ⟨hchild, hparent⟩
  · have hb : T.blockOf l.castSucc i = T.blockOf l.succ i := hsame.trans heq
    simpa only [hb] using (Set.Subset.refl
      (C ⟨T.blockOf l.succ i, ⟨l.succ, (T.blockOf_spec _ i).1⟩, hproper⟩).carrier)
  · have hp : T.parent l = T.blockOf l.succ i := hparent.symm.trans heq
    have hpp : T.parent l ≠ Finset.univ := hp ▸ hproper
    have hn := hC.1 l hpp
    rcases hchild with hleft | hright
    · simpa only [← hp, hleft] using Set.Subset.trans Set.subset_union_left hn
    · simpa only [← hp, hright] using Set.Subset.trans Set.subset_union_right hn

theorem cap_subset_of_blockOf_le (C : TreeCaps T d) (hC : StrictlyPrepared C)
    (i : Fin n) (l m : Fin (N + 1)) (hlm : l ≤ m)
    (hproper : T.blockOf m i ≠ Finset.univ) :
    (C ⟨T.blockOf l i, ⟨l, (T.blockOf_spec _ i).1⟩,
      proper_of_subset (blockOf_mono T i hlm) hproper⟩).carrier ⊆
    (C ⟨T.blockOf m i, ⟨m, (T.blockOf_spec _ i).1⟩, hproper⟩).carrier := by
  induction m using Fin.induction generalizing l with
  | zero =>
    have hl : l = 0 := le_antisymm hlm (Fin.zero_le l)
    subst l
    exact Set.Subset.refl _
  | succ m ih =>
    by_cases heq : l = m.succ
    · subst l
      exact Set.Subset.refl _
    have hlm' : l ≤ m.castSucc := by
      have hval := Fin.le_iff_val_le_val.mp hlm
      simp only [Fin.val_succ] at hval
      have hne : l.val ≠ m.val + 1 := by
        intro h
        apply heq
        exact Fin.ext h
      exact Fin.le_iff_val_le_val.mpr (by simpa only [Fin.val_castSucc] using (by omega : l.val ≤ m.val))
    have hp := proper_of_subset (blockOf_subset_succ T m i) hproper
    exact (ih l hlm' hp).trans (cap_subset_succ T C hC m i hproper)

theorem cap_subset_of_stages (C : TreeCaps T d) (hC : StrictlyPrepared C)
    (l m : Fin (N + 1)) (hlm : l ≤ m) (D E : T.ProperNode)
    (hD : D.val ∈ T.partition l) (hE : E.val ∈ T.partition m)
    (hDE : D.val ⊆ E.val) : (C D).carrier ⊆ (C E).carrier := by
  obtain ⟨i, hi⟩ := T.block_nonempty l D.val hD
  have hDi := T.blockOf_unique l i D.val hD hi
  have hEi := T.blockOf_unique m i E.val hE (hDE hi)
  have hp : T.blockOf m i ≠ Finset.univ := hEi ▸ E.property.2
  simpa only [← hDi, ← hEi] using cap_subset_of_blockOf_le T C hC i l m hlm hp

/-- When two distinct current blocks merge at the next step, they are exactly
the prescribed children, in one of the two possible orders. -/
theorem children_of_first_join (l : Fin N) (i j : Fin n)
    (hbefore : T.blockOf l.castSucc i ≠ T.blockOf l.castSucc j)
    (hafter : T.blockOf l.succ i = T.blockOf l.succ j) :
    (T.blockOf l.castSucc i = T.left l ∧ T.blockOf l.castSucc j = T.right l) ∨
    (T.blockOf l.castSucc i = T.right l ∧ T.blockOf l.castSucc j = T.left l) := by
  obtain ⟨E, hE, hsubE, hcE⟩ := successor_block T l _ (T.blockOf_spec l.castSucc i).1
  obtain ⟨F, hF, hsubF, hcF⟩ := successor_block T l _ (T.blockOf_spec l.castSucc j).1
  have he := T.blockOf_unique l.succ i E hE (hsubE (T.blockOf_spec l.castSucc i).2)
  have hf := T.blockOf_unique l.succ j F hF (hsubF (T.blockOf_spec l.castSucc j).2)
  have hef : E = F := he.trans (hafter.trans hf.symm)
  have hiChild : T.blockOf l.castSucc i = T.left l ∨ T.blockOf l.castSucc i = T.right l := by
    rcases hcE with hi | ⟨hi, _⟩
    · rcases hcF with hj | ⟨_, hj⟩
      · exact False.elim (hbefore (hi.trans (hef.trans hj.symm)))
      · have hb : T.parent l ∈ T.partition l.castSucc := by
          rw [← hj, ← hef, ← hi]
          exact (T.blockOf_spec l.castSucc i).1
        exact False.elim (TreeDynamics.parent_not_mem_current T l hb)
    · exact hi
  have hjChild : T.blockOf l.castSucc j = T.left l ∨ T.blockOf l.castSucc j = T.right l := by
    rcases hcF with hj | ⟨hj, _⟩
    · rcases hcE with hi | ⟨_, hi⟩
      · exact False.elim (hbefore (hi.trans (hef.trans hj.symm)))
      · have hb : T.parent l ∈ T.partition l.castSucc := by
          rw [← hi, hef, ← hj]
          exact (T.blockOf_spec l.castSucc j).1
        exact False.elim (TreeDynamics.parent_not_mem_current T l hb)
    · exact hj
  rcases hiChild with hi | hi <;> rcases hjChild with hj | hj
  · exact False.elim (hbefore (hi.trans hj.symm))
  · exact Or.inl ⟨hi, hj⟩
  · exact Or.inr ⟨hi, hj⟩
  · exact False.elim (hbefore (hi.trans hj.symm))

/-- Every two distinct blocks in a partition are separated by the children of
a later merge. The witness is obtained from the first joining time. -/
theorem exists_separating_stage (l : Fin (N + 1)) (D E : Block n)
    (hD : D ∈ T.partition l) (hE : E ∈ T.partition l) (hne : D ≠ E) :
    ∃ r : Fin N, l ≤ r.castSucc ∧
      ((D ⊆ T.left r ∧ E ⊆ T.right r) ∨ (D ⊆ T.right r ∧ E ⊆ T.left r)) := by
  classical
  obtain ⟨i, hi⟩ := T.block_nonempty l D hD
  obtain ⟨j, hj⟩ := T.block_nonempty l E hE
  have hDi := T.blockOf_unique l i D hD hi
  have hEj := T.blockOf_unique l j E hE hj
  let p : ℕ → Prop := fun q => ∃ hq : q < N + 1,
    l.val ≤ q ∧ T.blockOf ⟨q, hq⟩ i = T.blockOf ⟨q, hq⟩ j
  have hex : ∃ q, p q := by
    refine ⟨N, Nat.lt_succ_self N, Nat.le_of_lt_succ l.isLt, ?_⟩
    exact (blockOf_final T i).trans (blockOf_final T j).symm
  obtain ⟨hqN, hlq, hjoin⟩ := Nat.find_spec hex
  have hlt : l.val < Nat.find hex := by
    by_contra h
    have heq : Nat.find hex = l.val := by omega
    have hfin : (⟨Nat.find hex, hqN⟩ : Fin (N + 1)) = l := Fin.ext heq
    rw [hfin] at hjoin
    exact hne (hDi.trans (hjoin.trans hEj.symm))
  let r : Fin N := ⟨Nat.find hex - 1, by omega⟩
  have hr : l ≤ r.castSucc := Fin.le_iff_val_le_val.mpr (by dsimp [r]; omega)
  have hs : r.succ = (⟨Nat.find hex, hqN⟩ : Fin (N + 1)) := Fin.ext (by dsimp [r]; omega)
  have hbefore : T.blockOf r.castSucc i ≠ T.blockOf r.castSucc j := by
    intro h
    have hp : p r.val := ⟨r.castSucc.isLt, Fin.le_iff_val_le_val.mp hr, h⟩
    have hmin := Nat.find_min' hex hp
    dsimp [r] at hmin
    omega
  have hchildren := children_of_first_join T r i j hbefore (hs ▸ hjoin)
  have hDi' : D ⊆ T.blockOf r.castSucc i := hDi ▸ blockOf_mono T i hr
  have hEj' : E ⊆ T.blockOf r.castSucc j := hEj ▸ blockOf_mono T j hr
  refine ⟨r, hr, ?_⟩
  rcases hchildren with ⟨hleft, hright⟩ | ⟨hright, hleft⟩
  · exact Or.inl ⟨hleft ▸ hDi', hright ▸ hEj'⟩
  · exact Or.inr ⟨hright ▸ hDi', hleft ▸ hEj'⟩

theorem eq_of_subset_same_partition (l : Fin (N + 1)) (D E : Block n)
    (hD : D ∈ T.partition l) (hE : E ∈ T.partition l) (hDE : D ⊆ E) : D = E := by
  obtain ⟨i, hi⟩ := T.block_nonempty l D hD
  exact (T.blockOf_unique l i D hD hi).trans
    (T.blockOf_unique l i E hE (hDE hi)).symm

theorem exists_future_separating_stage (l : Fin N) (D E : Block n)
    (hD : D ∈ T.partition l.castSucc) (hE : E ∈ T.partition l.castSucc)
    (hne : D ≠ E) (hDl : D ≠ T.left l) (hDr : D ≠ T.right l) :
    ∃ r : Fin N, l < r ∧
      ((D ⊆ T.left r ∧ E ⊆ T.right r) ∨ (D ⊆ T.right r ∧ E ⊆ T.left r)) := by
  obtain ⟨r, hlr, hcases⟩ := exists_separating_stage T l.castSucc D E hD hE hne
  have hle : l ≤ r := Fin.le_iff_val_le_val.mpr (Fin.le_iff_val_le_val.mp hlr)
  refine ⟨r, lt_of_le_of_ne hle ?_, hcases⟩
  intro heq
  subst r
  rcases hcases with ⟨hsub, _⟩ | ⟨hsub, _⟩
  · exact hDl (eq_of_subset_same_partition T l.castSucc D (T.left l) hD (T.left_mem l) hsub)
  · exact hDr (eq_of_subset_same_partition T l.castSucc D (T.right l) hD (T.right_mem l) hsub)

theorem capMinDistance_mono {C D E F : SphericalCap d}
    (hCE : C.carrier ⊆ E.carrier) (hDF : D.carrier ⊆ F.carrier) :
    capMinDistance E F ≤ capMinDistance C D := by
  apply le_csInf (CapDistances.values_nonempty C D)
  rintro a ⟨x, hx, y, hy, rfl⟩
  exact CapDistances.capMinDistance_le_angle E F x y (hCE hx) (hDF hy)

theorem capMinDistance_comm (C D : SphericalCap d) : capMinDistance C D = capMinDistance D C := by
  unfold capMinDistance
  congr 1
  ext a
  constructor <;> rintro ⟨x, hx, y, hy, rfl⟩
  · exact ⟨y, hy, x, hx, AngularGeometry.angularDist_comm x y⟩
  · exact ⟨y, hy, x, hx, AngularGeometry.angularDist_comm x y⟩

theorem lowerBarrier_pos (C : TreeCaps T d) (hC : StrictlyPrepared C) (r : Fin N) :
    0 < lowerBarrier C r := by
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num : (0 : ℝ) ≤ 0)
    ((hC.2 r).2.1.trans (hC.2 r).2.2.1.le) (hC.2 r).1
  rw [Real.cos_zero] at h
  exact sub_pos.mpr h

theorem barrier_of_separating_children (C : TreeCaps T d) (hC : StrictlyPrepared C)
    (l : Fin (N + 1)) (r : Fin N) (hlr : l ≤ r.castSucc) (D E : T.ProperNode)
    (hD : D.val ∈ T.partition l) (hE : E.val ∈ T.partition l)
    (hsep : (D.val ⊆ T.left r ∧ E.val ⊆ T.right r) ∨
      (D.val ⊆ T.right r ∧ E.val ⊆ T.left r)) :
    lowerBarrier C r ≤ 1 - Real.cos (capMinDistance (C D) (C E)) := by
  have hangle : lowerAngle C r ≤ capMinDistance (C D) (C E) := by
    rcases hsep with ⟨hleft, hright⟩ | ⟨hright, hleft⟩
    · exact capMinDistance_mono
        (cap_subset_of_stages T C hC l r.castSucc hlr D (T.leftNode r) hD (T.left_mem r) hleft)
        (cap_subset_of_stages T C hC l r.castSucc hlr E (T.rightNode r) hE (T.right_mem r) hright)
    · have h := capMinDistance_mono
        (cap_subset_of_stages T C hC l r.castSucc hlr E (T.leftNode r) hE (T.left_mem r) hleft)
        (cap_subset_of_stages T C hC l r.castSucc hlr D (T.rightNode r) hD (T.right_mem r) hright)
      rwa [capMinDistance_comm (C E) (C D)] at h
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi (hC.2 r).1.le
    (CapDistances.capMinDistance_le_pi (C D) (C E)) hangle
  exact sub_le_sub_left hcos 1

theorem current_pair_barrier (C : TreeCaps T d) (hC : StrictlyPrepared C)
    (l : Fin (N + 1)) (D E : T.ProperNode)
    (hD : D.val ∈ T.partition l) (hE : E.val ∈ T.partition l) (hne : D.val ≠ E.val) :
    ∃ r : Fin N, l ≤ r.castSucc ∧
      lowerBarrier C r ≤ 1 - Real.cos (capMinDistance (C D) (C E)) := by
  obtain ⟨r, hlr, hsep⟩ := exists_separating_stage T l D.val E.val hD hE hne
  exact ⟨r, hlr, barrier_of_separating_children T C hC l r hlr D E hD hE hsep⟩

theorem future_pair_barrier (C : TreeCaps T d) (hC : StrictlyPrepared C)
    (l : Fin N) (D E : T.ProperNode)
    (hD : D.val ∈ T.partition l.castSucc) (hE : E.val ∈ T.partition l.castSucc)
    (hne : D.val ≠ E.val) (hDl : D.val ≠ T.left l) (hDr : D.val ≠ T.right l) :
    ∃ r : Fin N, l < r ∧
      lowerBarrier C r ≤ 1 - Real.cos (capMinDistance (C D) (C E)) := by
  obtain ⟨r, hlr, hsep⟩ := exists_future_separating_stage T l D.val E.val hD hE hne hDl hDr
  exact ⟨r, hlr, barrier_of_separating_children T C hC l.castSucc r
    (Fin.le_iff_val_le_val.mpr (Fin.le_iff_val_le_val.mp hlr.le)) D E hD hE hsep⟩

theorem upperBarrier_strictMono (C : TreeCaps T d) (hC : StrictlyPrepared C) :
    StrictMono (upperBarrier C) := by
  cases N with
  | zero => exact fun i => Fin.elim0 i
  | succ k =>
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    have heq : previousUpperBarrier C i.succ = upperBarrier C i.castSucc := by
      unfold previousUpperBarrier
      rw [dif_neg (by simp only [Fin.val_succ, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true])]
      congr 1
    have h := (hC.2 i.succ).2.2.2.1
    rw [heq] at h
    exact h.trans_le (hC.2 i.succ).2.2.2.2.1

theorem upperBarrier_add_le_lowerBarrier_of_lt (C : TreeCaps T d) (hC : StrictlyPrepared C)
    (δ : ℝ) (hgap : ∀ r : Fin N, previousUpperBarrier C r + 8 * δ ≤ lowerBarrier C r)
    (l r : Fin N) (hlr : l < r) : upperBarrier C l + 8 * δ ≤ lowerBarrier C r := by
  have hr0 : r.val ≠ 0 := by have h := Fin.lt_def.mp hlr; omega
  let p : Fin N := ⟨r.val - 1, by omega⟩
  have hlp : l ≤ p := Fin.le_iff_val_le_val.mpr (by
    have h := Fin.lt_def.mp hlr
    dsimp [p]
    omega)
  have heq : previousUpperBarrier C r = upperBarrier C p := by
    simp only [previousUpperBarrier, hr0, ↓reduceDIte, p]
  have h := (upperBarrier_strictMono T C hC).monotone hlp
  have hg := hgap r
  rw [heq] at hg
  linarith only [h, hg]

theorem future_pair_gap (C : TreeCaps T d) (hC : StrictlyPrepared C)
    (δ : ℝ) (hgap : ∀ r : Fin N, previousUpperBarrier C r + 8 * δ ≤ lowerBarrier C r)
    (l : Fin N) (D E : T.ProperNode)
    (hD : D.val ∈ T.partition l.castSucc) (hE : E.val ∈ T.partition l.castSucc)
    (hne : D.val ≠ E.val) (hDl : D.val ≠ T.left l) (hDr : D.val ≠ T.right l) :
    upperBarrier C l + 8 * δ ≤ 1 - Real.cos (capMinDistance (C D) (C E)) := by
  obtain ⟨r, hlr, hbarrier⟩ := future_pair_barrier T C hC l D E hD hE hne hDl hDr
  exact (upperBarrier_add_le_lowerBarrier_of_lt T C hC δ hgap l r hlr).trans hbarrier

theorem outsideBarrier_le_current (C : TreeCaps T d) (l : Fin N)
    (hp : T.parent l ≠ Finset.univ) (D : T.ProperNode)
    (hD : D.val ∈ T.partition l.castSucc) (hDl : D.val ≠ T.left l) (hDr : D.val ≠ T.right l) :
    outsideBarrier C l ≤ 1 - Real.cos (capMinDistance (C (T.parentNode l hp)) (C D)) := by
  let S : Set ℝ := {r | ∃ E : T.ProperNode,
    E.val ∈ T.partition l.castSucc ∧ E.val ≠ T.left l ∧ E.val ≠ T.right l ∧
    r = capMinDistance (C (T.parentNode l hp)) (C E)}
  have hmem : capMinDistance (C (T.parentNode l hp)) (C D) ∈ S := ⟨D, hD, hDl, hDr, rfl⟩
  have hnonneg : ∀ r ∈ S, 0 ≤ r := by
    rintro r ⟨E, _, _, _, rfl⟩
    exact CapDistances.capMinDistance_nonneg _ _
  have hzero : 0 ≤ sInf S := le_csInf ⟨_, hmem⟩ hnonneg
  have hle : sInf S ≤ capMinDistance (C (T.parentNode l hp)) (C D) :=
    csInf_le ⟨0, hnonneg⟩ hmem
  unfold outsideBarrier
  rw [dif_neg hp]
  exact sub_le_sub_left (Real.cos_le_cos_of_nonneg_of_le_pi hzero
    (CapDistances.capMinDistance_le_pi _ _) hle) 1

/-- A common positive barrier holds between every two distinct current caps.
The factor two leaves a positive margin for later cap perturbations. -/
theorem exists_uniform_current_barrier (hN : 0 < N) (C : TreeCaps T d)
    (hC : StrictlyPrepared C) :
    ∃ b : ℝ, 0 < b ∧ ∀ (l : Fin (N + 1)) (D E : T.ProperNode),
      D.val ∈ T.partition l → E.val ∈ T.partition l → D.val ≠ E.val →
      2 * b ≤ 1 - Real.cos (capMinDistance (C D) (C E)) := by
  classical
  let S : Finset ℝ := Finset.univ.image (lowerBarrier C)
  have hS : S.Nonempty := Finset.Nonempty.image
    ⟨(⟨0, hN⟩ : Fin N), Finset.mem_univ _⟩ (lowerBarrier C)
  have hpos : 0 < S.min' hS := by
    obtain ⟨r, _, heq⟩ := Finset.mem_image.mp (Finset.min'_mem S hS)
    rw [← heq]
    exact lowerBarrier_pos T C hC r
  refine ⟨S.min' hS / 2, half_pos hpos, ?_⟩
  intro l D E hD hE hne
  obtain ⟨r, _, hr⟩ := current_pair_barrier T C hC l D E hD hE hne
  have hmin := Finset.min'_le S (lowerBarrier C r)
    (Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩)
  linarith only [hmin, hr]

theorem cap_barrier_le_pointwise (C D : SphericalCap d) (x y : Sphere d)
    (hx : x ∈ C.carrier) (hy : y ∈ D.carrier) :
    1 - Real.cos (capMinDistance C D) ≤ 1 - Real.cos (angularDist x y) :=
  sub_le_sub_left (Real.cos_le_cos_of_nonneg_of_le_pi
    (CapDistances.capMinDistance_nonneg C D) (AngularGeometry.angularDist_le_pi x y)
    (CapDistances.capMinDistance_le_angle C D x y hx hy)) 1

theorem exists_initial_uniform_barrier (hN : 0 < N) (C : TreeCaps T d)
    (hC : StrictlyPrepared C) :
    ∃ b : ℝ, 0 < b ∧ ∀ (D E : T.ProperNode),
      D.val ∈ T.partition 0 → E.val ∈ T.partition 0 → D.val ≠ E.val →
      ∀ (x y : Sphere d), x ∈ (C D).carrier → y ∈ (C E).carrier →
      2 * b ≤ 1 - Real.cos (angularDist x y) := by
  obtain ⟨b, hb, hbarrier⟩ := exists_uniform_current_barrier T hN C hC
  refine ⟨b, hb, ?_⟩
  intro D E hD hE hne x y hx hy
  exact (hbarrier 0 D E hD hE hne).trans (cap_barrier_le_pointwise (C D) (C E) x y hx hy)

theorem exists_uniform_center_barrier (hN : 0 < N) (C : TreeCaps T d)
    (hC : StrictlyPrepared C) :
    ∃ g : ℝ, 0 < g ∧ ∀ (l : Fin (N + 1)) (D E : T.ProperNode),
      D.val ∈ T.partition l → E.val ∈ T.partition l → D.val ≠ E.val →
      g ≤ 1 - ⟪(C D).center.val, (C E).center.val⟫ := by
  obtain ⟨b, hb, hbarrier⟩ := exists_uniform_current_barrier T hN C hC
  refine ⟨2 * b, mul_pos (by norm_num) hb, ?_⟩
  intro l D E hD hE hne
  have h := (hbarrier l D E hD hE hne).trans
    (cap_barrier_le_pointwise (C D) (C E) (C D).center (C E).center
      (AngularGeometry.cap_center_mem (C D)) (AngularGeometry.cap_center_mem (C E)))
  simpa only [AngularGeometry.cos_angularDist] using h

theorem exists_initial_center_barrier (hN : 0 < N) (C : TreeCaps T d)
    (hC : StrictlyPrepared C) :
    ∃ g : ℝ, 0 < g ∧ ∀ (D : Block n) (hD : D ∈ T.partition 0)
      (E : Block n) (hE : E ∈ T.partition 0), D ≠ E →
      g ≤ 1 - ⟪(C (T.currentNode ⟨0, hN⟩ D hD)).center.val,
        (C (T.currentNode ⟨0, hN⟩ E hE)).center.val⟫ := by
  obtain ⟨g, hg, hbarrier⟩ := exists_uniform_center_barrier T hN C hC
  refine ⟨g, hg, ?_⟩
  intro D hD E hE hne
  exact hbarrier 0 (T.currentNode ⟨0, hN⟩ D hD) (T.currentNode ⟨0, hN⟩ E hE) hD hE hne

/-- Once two labels have joined, the merge rule never separates them again. -/
theorem blockOf_eq_of_le (l m : Fin (N + 1)) (hlm : l ≤ m) (i j : Fin n)
    (hij : T.blockOf l i = T.blockOf l j) : T.blockOf m i = T.blockOf m j := by
  have hi' : i ∈ T.blockOf l j := by
    rw [← hij]
    exact (T.blockOf_spec l i).2
  have hi : i ∈ T.blockOf m j := blockOf_mono T j hlm hi'
  exact (T.blockOf_unique m i (T.blockOf m j) (T.blockOf_spec m j).1 hi).symm

theorem blockOf_ne_of_separating_children (D E : Block n) (r : Fin N)
    (hsep : (D ⊆ T.left r ∧ E ⊆ T.right r) ∨ (D ⊆ T.right r ∧ E ⊆ T.left r))
    (i j : Fin n) (hi : i ∈ D) (hj : j ∈ E) :
    T.blockOf r.castSucc i ≠ T.blockOf r.castSucc j := by
  rcases hsep with ⟨hD, hE⟩ | ⟨hD, hE⟩
  · have hDi := (T.blockOf_unique r.castSucc i (T.left r) (T.left_mem r) (hD hi)).symm
    have hEj := (T.blockOf_unique r.castSucc j (T.right r) (T.right_mem r) (hE hj)).symm
    rw [hDi, hEj]
    exact T.children_ne r
  · have hDi := (T.blockOf_unique r.castSucc i (T.right r) (T.right_mem r) (hD hi)).symm
    have hEj := (T.blockOf_unique r.castSucc j (T.left r) (T.left_mem r) (hE hj)).symm
    rw [hDi, hEj]
    exact (T.children_ne r).symm

theorem blockOf_eq_succ_of_separating_children (D E : Block n) (r : Fin N)
    (hsep : (D ⊆ T.left r ∧ E ⊆ T.right r) ∨ (D ⊆ T.right r ∧ E ⊆ T.left r))
    (i j : Fin n) (hi : i ∈ D) (hj : j ∈ E) :
    T.blockOf r.succ i = T.blockOf r.succ j := by
  have hp : T.parent r ∈ T.partition r.succ := by
    rw [T.merge r]
    exact Finset.mem_insert_self _ _
  have hij : i ∈ T.parent r ∧ j ∈ T.parent r := by
    rcases hsep with ⟨hD, hE⟩ | ⟨hD, hE⟩
    · exact ⟨Finset.mem_union_left _ (hD hi), Finset.mem_union_right _ (hE hj)⟩
    · exact ⟨Finset.mem_union_right _ (hD hi), Finset.mem_union_left _ (hE hj)⟩
  exact (T.blockOf_unique r.succ i (T.parent r) hp hij.1).symm.trans
    (T.blockOf_unique r.succ j (T.parent r) hp hij.2)

/-- Two nonempty blocks can lie in opposite prescribed children at only one
stage. After that merge, coarsening keeps their labels together forever. -/
theorem separating_stage_unique (D E : Block n) (hD : D.Nonempty) (hE : E.Nonempty)
    (r s : Fin N)
    (hr : (D ⊆ T.left r ∧ E ⊆ T.right r) ∨ (D ⊆ T.right r ∧ E ⊆ T.left r))
    (hs : (D ⊆ T.left s ∧ E ⊆ T.right s) ∨ (D ⊆ T.right s ∧ E ⊆ T.left s)) :
    r = s := by
  obtain ⟨i, hi⟩ := hD
  obtain ⟨j, hj⟩ := hE
  rcases lt_trichotomy r s with hrs | heq | hsr
  · have hle : r.succ ≤ s.castSucc := by
      have h := Fin.lt_def.mp hrs
      exact Fin.le_iff_val_le_val.mpr (by simpa only [Fin.val_succ, Fin.val_castSucc] using h)
    exact False.elim ((blockOf_ne_of_separating_children T D E s hs i j hi hj)
      (blockOf_eq_of_le T r.succ s.castSucc hle i j
        (blockOf_eq_succ_of_separating_children T D E r hr i j hi hj)))
  · exact heq
  · have hle : s.succ ≤ r.castSucc := by
      have h := Fin.lt_def.mp hsr
      exact Fin.le_iff_val_le_val.mpr (by simpa only [Fin.val_succ, Fin.val_castSucc] using h)
    exact False.elim ((blockOf_ne_of_separating_children T D E r hr i j hi hj)
      (blockOf_eq_of_le T s.succ r.castSucc hle i j
        (blockOf_eq_succ_of_separating_children T D E s hs i j hi hj)))

theorem separating_stage_le (D E : Block n) (hD : D.Nonempty) (hE : E.Nonempty)
    (r s : Fin N)
    (hr : (D ⊆ T.left r ∧ E ⊆ T.right r) ∨ (D ⊆ T.right r ∧ E ⊆ T.left r))
    (hs : (D ⊆ T.left s ∧ E ⊆ T.right s) ∨ (D ⊆ T.right s ∧ E ⊆ T.left s)) :
    r ≤ s := (separating_stage_unique T D E hD hE r s hr hs).le

end Metastability.TreeSeparation
