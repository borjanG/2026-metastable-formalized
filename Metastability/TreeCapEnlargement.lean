import Metastability.CapEnlargement
import Metastability.TreeSeparation

/-!
# The source enlarged-cap separation estimates

The literal source tree margin and a uniform geometric constant control every
proper-node enlargement with 0 <= M <= 2N+5. The parent-versus-outside and
future-pair barriers are derived from the collision tree and strict preparation.
No root cap, ancestry hypothesis, or additional separation premise is supplied.
-/

noncomputable section
open Set

namespace Metastability.TreeCapEnlargement

open Source CapEnlargement
variable {n N d : ℕ}

/-- Source enlarged-cap barriers, uniform in the real enlargement parameter.
The witness family is completely specified by its exact centers and radii;
each of its caps has radius strictly below a hemisphere by its source type.

The future-stage conclusion supplies the first separating stage after the
present one and both its barrier and the seven-margin gap. The active conclusion
includes the literal supremum of pair deficits from the manuscript. -/
theorem enlarged_tree_barriers (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) :
    0 < treeMargin hN C ∧ ∃ Cgeo : ℝ, 0 < Cgeo ∧ ∃ β₀ : ℝ, 1 < β₀ ∧
      ∀ β ≥ β₀, ∀ M ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 5),
        ∃ E : TreeCaps T d,
          (∀ A, (E A).center = (C A).center ∧
            (E A).radius = (C A).radius + M * enlargementScale β) ∧
          (∀ l : Fin N,
            upperBarrier E l ≤ upperBarrier C l + Cgeo * enlargementScale β ∧
            upperBarrier E l ≤ upperBarrier C l + treeMargin hN C ∧
            sSup {z : ℝ | ∃ x ∈ (E (T.leftNode l)).carrier,
              ∃ y ∈ (E (T.rightNode l)).carrier,
                z = 1 - Real.cos (angularDist x y)} ≤ upperBarrier C l + treeMargin hN C) ∧
          (∀ (l : Fin N) (hp : T.parent l ≠ Finset.univ) (D : T.ProperNode),
            D.val ∈ T.partition l.castSucc → D.val ≠ T.left l → D.val ≠ T.right l →
            outsideBarrier C l - Cgeo * enlargementScale β ≤
              1 - Real.cos (capMinDistance (E (T.parentNode l hp)) (E D)) ∧
            outsideBarrier C l - treeMargin hN C ≤
              1 - Real.cos (capMinDistance (E (T.parentNode l hp)) (E D)) ∧
            upperBarrier C l + 7 * treeMargin hN C ≤
              1 - Real.cos (capMinDistance (E (T.parentNode l hp)) (E D))) ∧
          (∀ (l : Fin N) (D F : T.ProperNode),
            D.val ∈ T.partition l.castSucc → F.val ∈ T.partition l.castSucc → D.val ≠ F.val →
            D.val ≠ T.left l → D.val ≠ T.right l → F.val ≠ T.left l → F.val ≠ T.right l →
            ∃ r : Fin N, l < r ∧
              ((D.val ⊆ T.left r ∧ F.val ⊆ T.right r) ∨
                (D.val ⊆ T.right r ∧ F.val ⊆ T.left r)) ∧
              (∀ s : Fin N, l ≤ s →
                ((D.val ⊆ T.left s ∧ F.val ⊆ T.right s) ∨
                  (D.val ⊆ T.right s ∧ F.val ⊆ T.left s)) → r ≤ s) ∧
              lowerBarrier C r - Cgeo * enlargementScale β ≤
                1 - Real.cos (capMinDistance (E D) (E F)) ∧
              lowerBarrier C r - treeMargin hN C ≤
                1 - Real.cos (capMinDistance (E D) (E F)) ∧
              upperBarrier C l + 7 * treeMargin hN C ≤
                1 - Real.cos (capMinDistance (E D) (E F))) := by
  have hδ := treeMargin_pos hN C hC
  obtain ⟨β₀, hβ₀, hfamily⟩ := exists_uniform_enlarged_family C (treeMargin hN C) hδ
  refine ⟨hδ, geometryConstant N, geometryConstant_pos N, β₀, hβ₀, ?_⟩
  intro β hβ M hM
  obtain ⟨E, hE, herr, hperturb⟩ := hfamily β hβ M hM
  have hβ0 : 0 < β := lt_trans zero_lt_one (hβ₀.trans_le hβ)
  have hgeo := enlargement_error_le N hβ0 hM.2
  refine ⟨E, hE, ?_, ?_, ?_⟩
  · intro l
    have hmax := (hperturb (T.leftNode l) (T.rightNode l)).2
    change upperBarrier E l ≤ upperBarrier C l + 2 * (M * enlargementScale β) at hmax
    have hfinal : upperBarrier E l ≤ upperBarrier C l + treeMargin hN C := by
      linarith only [hmax, herr]
    refine ⟨by linarith only [hmax, hgeo], hfinal, ?_⟩
    exact (sup_deficits_le_max_barrier (E (T.leftNode l)) (E (T.rightNode l))).trans hfinal
  · intro l hp D hD hDl hDr
    have hbase := TreeSeparation.outsideBarrier_le_current T C l hp D hD hDl hDr
    have hmin := (hperturb (T.parentNode l hp) D).1
    have hgap := (treeMargin_gaps hN C l).2
    refine ⟨by linarith only [hbase, hmin, hgeo],
      by linarith only [hbase, hmin, herr], ?_⟩
    linarith only [hbase, hmin, herr, hgap]
  · intro l D F hD hF hne hDl hDr _hFl _hFr
    obtain ⟨r, hlr, hsep⟩ := TreeSeparation.exists_future_separating_stage T l D.val F.val
      hD hF hne hDl hDr
    have hbase := TreeSeparation.barrier_of_separating_children T C hC l.castSucc r
      (Fin.le_iff_val_le_val.mpr (Fin.le_iff_val_le_val.mp hlr.le)) D F hD hF hsep
    have hmin := (hperturb D F).1
    have hgap := TreeSeparation.upperBarrier_add_le_lowerBarrier_of_lt T C hC
      (treeMargin hN C) (fun r => (treeMargin_gaps hN C r).1) l r hlr
    have hfirst : ∀ s : Fin N, l ≤ s →
        ((D.val ⊆ T.left s ∧ F.val ⊆ T.right s) ∨
          (D.val ⊆ T.right s ∧ F.val ⊆ T.left s)) → r ≤ s := by
      intro s _hls hs
      exact TreeSeparation.separating_stage_le T D.val F.val
        (T.block_nonempty _ _ hD) (T.block_nonempty _ _ hF) r s hsep hs
    refine ⟨r, hlr, hsep, hfirst, by linarith only [hbase, hmin, hgeo],
      by linarith only [hbase, hmin, herr], ?_⟩
    linarith only [hbase, hmin, herr, hgap]

end Metastability.TreeCapEnlargement
