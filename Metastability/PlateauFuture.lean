import Metastability.ActiveSourceLaw

/-! A future parent cannot become small during the current plateau. The
needed separation of its labels is derived from the literal merge rules. -/

noncomputable section
open Filter Set
open scoped Topology RealInnerProductSpace

namespace Metastability.PlateauFuture
open Source CapEnlargement ActiveSourceLaw
variable {n N d : ℕ}

theorem future_pair_nonactive (T : CollisionTree n N) (l m : Fin N) (hlm : l < m)
    (i j : Fin n) (hi : i ∈ T.left m) (hj : j ∈ T.right m) :
    T.blockOf l.castSucc i ≠ T.blockOf l.castSucc j ∧
      ¬ ActiveGeometry.IsActiveCross T l i j := by
  have hm := TreeSeparation.blockOf_ne_of_separating_children T (T.left m) (T.right m) m
    (Or.inl ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩) i j hi hj
  have hlm' : l.castSucc ≤ m.castSucc := by simpa only [Fin.le_iff_val_le_val] using hlm.le
  have hsucc : l.succ ≤ m.castSucc := by
    simp only [Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_castSucc]
    exact Nat.succ_le_of_lt hlm
  constructor
  · intro heq
    exact hm (TreeSeparation.blockOf_eq_of_le T _ _ hlm' i j heq)
  · rintro (⟨hil, hjr⟩ | ⟨hir, hjl⟩)
    · have heq := TreeSeparation.blockOf_eq_succ_of_separating_children T (T.left l) (T.right l) l
        (Or.inl ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩) i j hil hjr
      exact hm (TreeSeparation.blockOf_eq_of_le T _ _ hsucc i j heq)
    · have heq := TreeSeparation.blockOf_eq_succ_of_separating_children T (T.right l) (T.left l) l
        (Or.inr ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩) i j hir hjl
      exact hm (TreeSeparation.blockOf_eq_of_le T _ _ hsucc i j heq)

theorem deficit_le_angle (x y : Sphere d) :
    1 - ⟪x.val, y.val⟫ ≤ angularDist x y := by
  have hh := Real.abs_cos_sub_cos_le (angularDist x y) 0
  rw [Real.cos_zero, sub_zero, abs_of_nonneg (AngularGeometry.angularDist_nonneg x y),
    AngularGeometry.cos_angularDist] at hh
  linarith only [(abs_le.mp hh).1]

/-- A single positive source-tree barrier, independent of beta, controls a
pair in every later parent. In particular, no future parent has reached even
the larger visible scale. -/
theorem future_parent_has_large_pair (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) :
    ∃ β₀ : ℝ, 1 < β₀ ∧ ∀ β ≥ β₀,
      ∀ M ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 5), ∀ (κ : ℝ) (l : Fin N) (x : Configuration n d),
      StageHyp T C β κ M l x → ∀ m : Fin N, l < m →
        ∃ i ∈ T.parent m, ∃ j ∈ T.parent m,
          7 * treeMargin hN C ≤ angularDist (x i) (x j) ∧
            visibleScale β < angularDist (x i) (x j) := by
  obtain ⟨G, hG, hgeometry⟩ := ActiveGeometry.stage_barriers T hN C hC
  have hδ := treeMargin_pos hN C hC
  obtain ⟨V, hV⟩ := eventually_atTop.mp
    (ContractionScale.tendsto_visibleScale.eventually
      (gt_mem_nhds (by positivity : (0 : ℝ) < 7 * treeMargin hN C)))
  refine ⟨max G V, hG.trans_le (le_max_left _ _), ?_⟩
  intro β hβ M hM κ l x hstage m hlm
  have hpair := (hgeometry β ((le_max_left _ _).trans hβ) M hM l x hstage.2.1 hstage.2.2).2
  obtain ⟨i, hi⟩ := T.block_nonempty _ _ (T.left_mem m)
  obtain ⟨j, hj⟩ := T.block_nonempty _ _ (T.right_mem m)
  have hne := future_pair_nonactive T l m hlm i j hi hj
  have hbound := (hpair i j hne.1 hne.2).trans (deficit_le_angle (x i) (x j))
  have hu : 0 ≤ upperBarrier C l :=
    ((TreeSeparation.lowerBarrier_pos T C hC l).trans_le (hC.2 l).2.2.2.2.1).le
  have hlo : 7 * treeMargin hN C ≤ angularDist (x i) (x j) := by linarith only [hu, hbound]
  exact ⟨i, Finset.mem_union_left _ hi, j, Finset.mem_union_right _ hj, hlo,
    (hV β ((le_max_right _ _).trans hβ)).trans_le hlo⟩

end Metastability.PlateauFuture
