import Metastability.GeodesicBarycenter
import Metastability.TreeSeparation

/-! The deterministic node centers are constructed from the literal ordered
merge tree. Their equations and proper-node cap membership depend only on the
fixed prepared tree and the model, before any trajectory is chosen. -/
noncomputable section
open Set
namespace Metastability.DeterministicCenters
open Source AngularGeometry GeodesicBarycenter
variable {n N d : ℕ}

/-- A newly created parent has not appeared in any earlier partition. -/
theorem parent_not_mem_previous (T : CollisionTree n N) (l : Fin N)
    (m : Fin (N + 1)) (hm : m ≤ l.castSucc) : T.parent l ∉ T.partition m := by
  intro hp
  obtain ⟨E, hE, hsub⟩ := TreeSeparation.exists_coarsening T m l.castSucc hm _ hp
  obtain ⟨i, hi⟩ := T.block_nonempty _ _ (T.left_mem l)
  have hiE := hsub (Finset.mem_union_left (T.right l) hi)
  have heq : E = T.left l :=
    (T.blockOf_unique l.castSucc i E hE hiE).trans
      (T.blockOf_unique l.castSucc i (T.left l) (T.left_mem l) hi).symm
  have hleft : T.parent l ⊆ T.left l := heq ▸ hsub
  obtain ⟨j, hj⟩ := T.block_nonempty _ _ (T.right_mem l)
  exact Finset.disjoint_left.mp (TreeDynamics.children_disjoint T l)
    (hleft (Finset.mem_union_right (T.left l) hj)) hj

/-- Successive finite construction, retaining all earlier node equations. -/
theorem exists_prefix (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) (model : Model)
    (m : Fin (N + 1)) :
    ∃ z : NodeCenters T d,
      (∀ D (hD : D ∈ T.partition (0 : Fin (N + 1))),
        z D ⟨_, hD⟩ = (C (T.currentNode ⟨0, hN⟩ D hD)).center) ∧
      (∀ l : Fin N, l.val < m.val →
        ∃ h : angularDist (z (T.left l) (T.left_node l))
            (z (T.right l) (T.right_node l)) < Real.pi,
          (z (T.parent l) (T.parent_node l)).val =
            geodesicBarycenter (centerWeight model (T.left l))
              (centerWeight model (T.right l))
              (centerWeight_pos model _ (T.block_nonempty _ _ (T.left_mem l)))
              (centerWeight_pos model _ (T.block_nonempty _ _ (T.right_mem l)))
              (z (T.left l) (T.left_node l)) (z (T.right l) (T.right_node l)) h) ∧
      (∀ q : Fin (N + 1), q ≤ m → ∀ D (hD : D ∈ T.partition q)
        (hp : D ≠ Finset.univ), z D ⟨q, hD⟩ ∈ (C ⟨D, ⟨q, hD⟩, hp⟩).carrier) := by
  classical
  induction m using Fin.induction with
  | zero =>
    let z : NodeCenters T d := fun D _ =>
      if hD : D ∈ T.partition (0 : Fin (N + 1)) then
        (C (T.currentNode ⟨0, hN⟩ D hD)).center
      else (C (T.leftNode ⟨0, hN⟩)).center
    refine ⟨z, ?_, ?_, ?_⟩
    · intro D hD
      exact dif_pos hD
    · intro l hl
      exact (Nat.not_lt_zero _ hl).elim
    · intro q hq D hD hp
      have hq0 : q = 0 := le_antisymm hq (Fin.zero_le q)
      subst q
      dsimp [z]
      rw [dif_pos hD]
      exact cap_center_mem _
  | succ l ih =>
    obtain ⟨z, hz0, hzrec, hzcap⟩ := ih
    let u := z (T.left l) (T.left_node l)
    let v := z (T.right l) (T.right_node l)
    have hu : u ∈ (C (T.leftNode l)).carrier :=
      hzcap l.castSucc le_rfl _ (T.left_mem l) (T.left_proper l)
    have hv : v ∈ (C (T.rightNode l)).carrier :=
      hzcap l.castSucc le_rfl _ (T.right_mem l) (T.right_proper l)
    have hθ : angularDist u v < Real.pi :=
      (CapDistances.angle_le_capMaxDistance _ _ u v hu hv).trans_lt (hC.2 l).2.2.1
    let p := point (centerWeight model (T.left l)) (centerWeight model (T.right l))
      (centerWeight_pos model _ (T.block_nonempty _ _ (T.left_mem l)))
      (centerWeight_pos model _ (T.block_nonempty _ _ (T.right_mem l))) u v hθ
    let z' : NodeCenters T d := fun D hD => if D = T.parent l then p else z D hD
    have hold (q : Fin (N + 1)) (hq : q ≤ l.castSucc) (D : Block n)
        (hD : D ∈ T.partition q) : z' D ⟨q, hD⟩ = z D ⟨q, hD⟩ := by
      apply if_neg
      intro he
      exact parent_not_mem_previous T l q hq (he ▸ hD)
    have hup : z' (T.left l) (T.left_node l) = u :=
      hold l.castSucc le_rfl _ (T.left_mem l)
    have hvp : z' (T.right l) (T.right_node l) = v :=
      hold l.castSucc le_rfl _ (T.right_mem l)
    have hpp : z' (T.parent l) (T.parent_node l) = p := if_pos rfl
    refine ⟨z', ?_, ?_, ?_⟩
    · intro D hD
      rw [hold 0 (Fin.zero_le _) D hD]
      exact hz0 D hD
    · intro r hr
      by_cases he : r = l
      · subst r
        refine ⟨by simpa only [hup, hvp] using hθ, ?_⟩
        simpa only [hpp, hup, hvp] using
          (point_val (centerWeight model (T.left l)) (centerWeight model (T.right l))
            (centerWeight_pos model _ (T.block_nonempty _ _ (T.left_mem l)))
            (centerWeight_pos model _ (T.block_nonempty _ _ (T.right_mem l))) u v hθ)
      · have hrl : r.val < l.val := by
          have hne : r.val ≠ l.val := fun h => he (Fin.ext h)
          simp only [Fin.val_succ] at hr
          omega
        obtain ⟨hθr, hpr⟩ := hzrec r hrl
        have hrl' : r.castSucc ≤ l.castSucc := Fin.le_iff_val_le_val.mpr hrl.le
        have hrp : r.succ ≤ l.castSucc := Fin.le_iff_val_le_val.mpr hrl
        have hub := hold r.castSucc hrl' _ (T.left_mem r)
        have hvb := hold r.castSucc hrl' _ (T.right_mem r)
        have hpb := hold r.succ hrp (T.parent r)
          (by rw [T.merge r]; exact Finset.mem_insert_self _ _)
        refine ⟨by simpa only [hub, hvb] using hθr, ?_⟩
        simpa only [hub, hvb, hpb] using hpr
    · intro q hq D hD hp
      by_cases hqold : q ≤ l.castSucc
      · rw [hold q hqold D hD]
        exact hzcap q hqold D hD hp
      · have hql : q = l.succ := by
          apply Fin.ext
          have ha := Fin.le_iff_val_le_val.mp hq
          have hb : ¬ q.val ≤ l.castSucc.val := by
            intro h
            exact hqold (Fin.le_iff_val_le_val.mpr h)
          simp only [Fin.val_succ, Fin.val_castSucc] at *
          omega
        subst q
        rw [T.merge l] at hD
        rcases Finset.mem_insert.mp hD with he | hD
        · subst D
          change z' (T.parent l) _ ∈ (C (T.parentNode l hp)).carrier
          rw [hpp]
          have hparent := hC.1 l hp
          exact point_mem_cap _ _ _ _ u v hθ (C (T.parentNode l hp))
            (hparent (Or.inl hu)) (hparent (Or.inr hv))
        · have hDold := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hD)
          rw [hold l.castSucc le_rfl D hDold]
          exact hzcap l.castSucc le_rfl D hDold hp

/-- The source recursive centers exist, with proper-node cap containment. -/
theorem exists_deterministic_centers (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) (model : Model) :
    ∃ z : NodeCenters T d, IsDeterministicCenters model hN C z ∧
      ∀ D : T.ProperNode, z D.val D.property.1 ∈ (C D).carrier := by
  obtain ⟨z, hz0, hzrec, hzcap⟩ := exists_prefix T hN C hC model (Fin.last N)
  refine ⟨z, ⟨hz0, fun l => hzrec l l.isLt⟩, ?_⟩
  intro D
  obtain ⟨q, hq⟩ := D.property.1
  exact hzcap q (Fin.le_last q) D.val hq D.property.2

end Metastability.DeterministicCenters
