import Metastability.ActiveGeometry

/-! Entry-cap nesting and exterior barriers for the plateau cap estimates. -/

noncomputable section
open Set
open scoped RealInnerProductSpace

namespace Metastability.PlateauCapGeometry
open Source CapEnlargement
variable {n N d : ℕ}

theorem enlarged_mem_of_subset (C D : SphericalCap d) (η : ℝ) (hη : 0 ≤ η)
    (hsmall : C.radius + η < Real.pi / 2) (hCD : C.carrier ⊆ D.carrier)
    (x : Sphere d) (hx : angularDist x C.center ≤ C.radius + η) :
    angularDist x D.center ≤ D.radius + η := by
  obtain ⟨z, hz, hnear⟩ := exists_near_original C η hη hsmall x hx
  have hzD : angularDist z D.center ≤ D.radius := hCD hz
  have htri := AngularGeometry.angularDist_triangle x z D.center
  linarith only [hnear, hzD, htri]

theorem entry_cap_geometry (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) :
    ∃ β₀ : ℝ, 1 < β₀ ∧ ∀ β ≥ β₀, ∀ M ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 5),
      (∀ A, (C A).radius + M * enlargementScale β < Real.pi / 2) ∧
      ∀ (l : Fin N) (x : Configuration n d),
        (∀ (D : Block n) (hD : D ∈ T.partition l.castSucc), ∀ i ∈ D,
          angularDist (x i) (C (T.currentNode l D hD)).center ≤
            (C (T.currentNode l D hD)).radius + M * enlargementScale β) →
        (∀ hp : T.parent l ≠ Finset.univ, ∀ i ∈ T.parent l,
          angularDist (x i) (C (T.parentNode l hp)).center ≤
            (C (T.parentNode l hp)).radius + M * enlargementScale β) ∧
        ∀ (i j : Fin n), i ∈ T.left l → j ∈ T.right l →
          1 - ⟪(x i).val, (x j).val⟫ ≤ upperBarrier C l + treeMargin hN C := by
  obtain ⟨_, _, _, β₀, hβ₀, hfamily⟩ := TreeCapEnlargement.enlarged_tree_barriers T hN C hC
  refine ⟨β₀, hβ₀, ?_⟩
  intro β hβ M hM
  obtain ⟨E, hE, hactive, _, _⟩ := hfamily β hβ M hM
  have hsmall : ∀ A, (C A).radius + M * enlargementScale β < Real.pi / 2 := by
    intro A
    rw [← (hE A).2]
    exact (E A).radius_lt_half_pi
  have hη : 0 ≤ M * enlargementScale β :=
    mul_nonneg hM.1 (enlargementScale_pos (zero_lt_one.trans (hβ₀.trans_le hβ))).le
  refine ⟨hsmall, ?_⟩
  intro l x hentry
  have hleft : ∀ i ∈ T.left l, angularDist (x i) (C (T.leftNode l)).center ≤
      (C (T.leftNode l)).radius + M * enlargementScale β := hentry _ (T.left_mem l)
  have hright : ∀ i ∈ T.right l, angularDist (x i) (C (T.rightNode l)).center ≤
      (C (T.rightNode l)).radius + M * enlargementScale β := hentry _ (T.right_mem l)
  constructor
  · intro hp i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact enlarged_mem_of_subset _ _ _ hη (hsmall _)
        (fun _ hx => hC.1 l hp (Or.inl hx)) _ (hleft i hi)
    · exact enlarged_mem_of_subset _ _ _ hη (hsmall _)
        (fun _ hx => hC.1 l hp (Or.inr hx)) _ (hright i hi)
  · intro i j hi hj
    have hiE : x i ∈ (E (T.leftNode l)).carrier := by
      change angularDist (x i) (E (T.leftNode l)).center ≤ (E (T.leftNode l)).radius
      rw [(hE _).1, (hE _).2]
      exact hleft i hi
    have hjE : x j ∈ (E (T.rightNode l)).carrier := by
      change angularDist (x j) (E (T.rightNode l)).center ≤ (E (T.rightNode l)).radius
      rw [(hE _).1, (hE _).2]
      exact hright j hj
    have hbound := deficit_le_max_barrier _ _ _ _ hiE hjE
    rw [AngularGeometry.cos_angularDist] at hbound
    exact hbound.trans (hactive l).2.1

theorem inactive_barrier_of_nonactive_pairs (T : CollisionTree n N) (l : Fin N)
    (x : Configuration n d) (L : ℝ)
    (hpair : ∀ i j, T.blockOf l.castSucc i ≠ T.blockOf l.castSucc j →
      ¬ ActiveGeometry.IsActiveCross T l i j → L ≤ 1 - ⟪(x i).val, (x j).val⟫)
    (D : Block n) (hD : D ∈ T.partition l.castSucc)
    (hDl : D ≠ T.left l) (hDr : D ≠ T.right l) :
    ∀ i ∈ D, ∀ j ∉ D, L ≤ 1 - ⟪(x i).val, (x j).val⟫ := by
  intro i hi j hj
  have hiD := T.blockOf_unique l.castSucc i D hD hi
  apply hpair i j
  · intro heq
    have hjD := (T.blockOf_spec l.castSucc j).2
    rw [← heq, ← hiD] at hjD
    exact hj hjD
  · rintro (⟨hil, _⟩ | ⟨hir, _⟩)
    · exact hDl (hiD.trans (T.blockOf_unique l.castSucc i _ (T.left_mem l) hil).symm)
    · exact hDr (hiD.trans (T.blockOf_unique l.castSucc i _ (T.right_mem l) hir).symm)

end Metastability.PlateauCapGeometry
