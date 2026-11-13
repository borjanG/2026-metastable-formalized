import Metastability.TreeCapEnlargement

/-! The literal next-partition barrier, derived from ordered tree gaps. -/

noncomputable section
open Set
open scoped RealInnerProductSpace

namespace Metastability.PostMergeGeometry
open Source CapEnlargement
variable {n N d : ℕ}

theorem lowerBarrier_mono (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) : Monotone (lowerBarrier C) := by
  intro k r hkr
  rcases lt_or_eq_of_le hkr with hlt | rfl
  · have hh := TreeSeparation.upperBarrier_add_le_lowerBarrier_of_lt T C hC
      (treeMargin hN C) (fun s => (treeMargin_gaps hN C s).1) k r hlt
    have hk := (hC.2 k).2.2.2.2.1
    have hδ := treeMargin_pos hN C hC
    linarith only [hh, hk, hδ]
  · exact le_rfl

theorem post_barrier_lower (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) (k : Fin N) :
    7 * treeMargin hN C ≤ lowerBarrier C k - treeMargin hN C := by
  have hp : 0 ≤ previousUpperBarrier C k := by
    unfold previousUpperBarrier
    split_ifs with hk
    · exact le_rfl
    · exact ((TreeSeparation.lowerBarrier_pos T C hC _).trans_le (hC.2 _).2.2.2.2.1).le
  have hg := (treeMargin_gaps hN C k).1
  linarith only [hp, hg]

theorem post_barrier_pos (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) (k : Fin N) :
    0 < lowerBarrier C k - treeMargin hN C :=
  (mul_pos (by norm_num) (treeMargin_pos hN C hC)).trans_le
    (post_barrier_lower T hN C hC k)

theorem current_cap_barrier (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) (k : Fin N)
    (D E : T.ProperNode) (hD : D.val ∈ T.partition k.castSucc)
    (hE : E.val ∈ T.partition k.castSucc) (hne : D.val ≠ E.val) :
    lowerBarrier C k ≤ 1 - Real.cos (capMinDistance (C D) (C E)) := by
  obtain ⟨r, hkr, hh⟩ := TreeSeparation.current_pair_barrier T C hC _ D E hD hE hne
  exact ((lowerBarrier_mono T hN C hC)
    (by simpa only [Fin.le_iff_val_le_val, Fin.val_castSucc] using hkr)).trans hh

/-- The same threshold gives all enlarged radii and the exact source
post-completion barrier for every current stage and block. -/
theorem enlarged_current_barriers (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) :
    ∃ β₀ : ℝ, 1 < β₀ ∧ ∀ β ≥ β₀,
      ∀ M ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 5),
      (∀ A, (C A).radius + M * enlargementScale β < Real.pi / 2) ∧
      ∀ (k : Fin N) (x : Configuration n d),
        (∀ (D : Block n) (hD : D ∈ T.partition k.castSucc), ∀ i ∈ D,
          angularDist (x i) (C (T.currentNode k D hD)).center ≤
            (C (T.currentNode k D hD)).radius + M * enlargementScale β) →
        ∀ (D : Block n) (_hD : D ∈ T.partition k.castSucc), ∀ i ∈ D, ∀ j ∉ D,
          lowerBarrier C k - treeMargin hN C ≤ 1 - ⟪(x i).val, (x j).val⟫ := by
  obtain ⟨β₀, hβ₀, hfamily⟩ := exists_uniform_enlarged_family C (treeMargin hN C)
    (treeMargin_pos hN C hC)
  refine ⟨β₀, hβ₀, ?_⟩
  intro β hβ M hM
  obtain ⟨E, hE, herr, hperturb⟩ := hfamily β hβ M hM
  refine ⟨fun A => by rw [← (hE A).2]; exact (E A).radius_lt_half_pi, ?_⟩
  intro k x hcap D hD i hi j hj
  let D' := T.currentNode k D hD
  let F := T.currentNode k (T.blockOf k.castSucc j) (T.blockOf_spec k.castSucc j).1
  have hne : D'.val ≠ F.val := by
    intro hh
    have hm := (T.blockOf_spec k.castSucc j).2
    change D = T.blockOf k.castSucc j at hh
    rw [← hh] at hm
    exact hj hm
  have hbase := current_cap_barrier T hN C hC k D' F hD (T.blockOf_spec k.castSucc j).1 hne
  have hp := (hperturb D' F).1
  have hiE : x i ∈ (E D').carrier := by
    change angularDist (x i) (E D').center ≤ (E D').radius
    rw [(hE _).1, (hE _).2]
    exact hcap D hD i hi
  have hjE : x j ∈ (E F).carrier := by
    change angularDist (x j) (E F).center ≤ (E F).radius
    rw [(hE _).1, (hE _).2]
    exact hcap _ (T.blockOf_spec k.castSucc j).1 j (T.blockOf_spec k.castSucc j).2
  have hpoint := min_barrier_le_deficit (E D') (E F) (x i) (x j) hiE hjE
  rw [AngularGeometry.cos_angularDist] at hpoint
  linarith only [hbase, hp, hpoint, herr]

end Metastability.PostMergeGeometry
