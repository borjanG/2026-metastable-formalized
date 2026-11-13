import Metastability.DeterministicCenters
import Metastability.BarycenterContinuity
import Metastability.ActiveBarycenter
import Metastability.AngularChord
import Metastability.CascadePreparation
import Metastability.LiteralCenters

/-! Continuity and initial-data bridges for the finite deterministic-center
induction. These helpers use literal spherical centers and normalized means. -/
noncomputable section
open Set Filter
open scoped Topology RealInnerProductSpace
namespace Metastability.CenterLimits
open Source AngularGeometry
variable {n N d : ℕ}

/-- Angular convergence implies convergence in the sphere's inherited topology. -/
theorem tendsto_of_angle (p : ℝ → Sphere d) (z : Sphere d)
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ β : ℝ in atTop, angularDist (p β) z < ε) :
    Tendsto p atTop (𝓝 z) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [h ε hε] with β hb
  exact (norm_sub_le_angularDist (p β) z).trans_lt hb

/-- Continuity of the source ambient barycenter on converging unit pairs. -/
theorem vector_tendsto (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (p q : ℝ → Sphere d) (u v : Sphere d) (hπ : angularDist u v < Real.pi)
    (hp : Tendsto p atTop (𝓝 u)) (hq : Tendsto q atTop (𝓝 v)) :
    Tendsto (fun β => BarycenterFormula.vector (b / (a + b)) (p β).val (q β).val)
      atTop (𝓝 (BarycenterFormula.vector (b / (a + b)) u.val v.val)) := by
  have hcont := BarycenterContinuity.continuousOn_vector (d := d) a b ha hb
  have hopen : IsOpen {w : Sphere d × Sphere d | angularDist w.1 w.2 < Real.pi} :=
    isOpen_lt continuous_angularDist continuous_const
  have hnb : {w : Sphere d × Sphere d | angularDist w.1 w.2 < Real.pi} ∈ 𝓝 (u, v) :=
    hopen.mem_nhds hπ
  have hc : ContinuousAt (fun w : Sphere d × Sphere d =>
      BarycenterFormula.vector (b / (a + b)) w.1.val w.2.val) (u, v) :=
    hcont.continuousAt hnb
  have hpair : Tendsto (fun β => (p β, q β)) atTop (𝓝 (u, v)) := hp.prodMk_nhds hq
  have hout := hc.tendsto.comp hpair
  exact hout

/-- Entry representative barycenters converge to the recursive parent. -/
theorem representative_center_tendsto (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (model : Model) (z : NodeCenters T d)
    (hz : IsDeterministicCenters model hN C z) (l : Fin N)
    (x : ℝ → Configuration n d) (i j : Fin n)
    (hi : ∀ ε : ℝ, 0 < ε → ∀ᶠ β : ℝ in atTop,
      angularDist (x β i) (z (T.left l) (T.left_node l)) < ε)
    (hj : ∀ ε : ℝ, 0 < ε → ∀ᶠ β : ℝ in atTop,
      angularDist (x β j) (z (T.right l) (T.right_node l)) < ε) :
    Tendsto (fun β => ActiveBarycenter.representativeCenter model T l (x β) i j)
      atTop (𝓝 (z (T.parent l) (T.parent_node l)).val) := by
  obtain ⟨hπ, hp⟩ := hz.2 l
  have ht := vector_tendsto (centerWeight model (T.left l)) (centerWeight model (T.right l))
    (centerWeight_pos model _ (T.block_nonempty _ _ (T.left_mem l)))
    (centerWeight_pos model _ (T.block_nonempty _ _ (T.right_mem l)))
    (fun β => x β i) (fun β => x β j)
    (z (T.left l) (T.left_node l)) (z (T.right l) (T.right_node l)) hπ
    (tendsto_of_angle _ _ hi) (tendsto_of_angle _ _ hj)
  have heq : BarycenterFormula.vector
      (centerWeight model (T.right l) / (centerWeight model (T.left l) + centerWeight model (T.right l)))
      (z (T.left l) (T.left_node l)).val (z (T.right l) (T.right_node l)).val =
      (z (T.parent l) (T.parent_node l)).val :=
    (BarycenterFormula.vector_eq_source _ _ _ _ _ _ hπ).trans hp.symm
  rw [heq] at ht
  exact ht

/-- A sphere-valued representative of the literal entry formula is uniformly
close to the deterministic parent. The formula, rather than a choice of cap,
identifies the center. -/
theorem entry_barycenter_close (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (model : Model) (z : NodeCenters T d)
    (hz : IsDeterministicCenters model hN C z) (l : Fin N)
    (x : ℝ → Configuration n d) (i j : Fin n)
    (hi : ∀ ε : ℝ, 0 < ε → ∀ᶠ β : ℝ in atTop,
      angularDist (x β i) (z (T.left l) (T.left_node l)) < ε)
    (hj : ∀ ε : ℝ, 0 < ε → ∀ᶠ β : ℝ in atTop,
      angularDist (x β j) (z (T.right l) (T.right_node l)) < ε)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ β : ℝ in atTop, ∀ G : Sphere d,
      (∃ hπ : angularDist (x β i) (x β j) < Real.pi,
        G.val = geodesicBarycenter (centerWeight model (T.left l)) (centerWeight model (T.right l))
          (centerWeight_pos model _ (T.block_nonempty _ _ (T.left_mem l)))
          (centerWeight_pos model _ (T.block_nonempty _ _ (T.right_mem l))) (x β i) (x β j) hπ) →
      angularDist G (z (T.parent l) (T.parent_node l)) < ε := by
  have ht := representative_center_tendsto T hN C model z hz l x i j hi hj
  have he := (Metric.tendsto_nhds.mp ht) (2 * ε / Real.pi) (by positivity)
  filter_upwards [he] with β hb
  intro G hG
  obtain ⟨hπ, hG⟩ := hG
  have heq : ActiveBarycenter.representativeCenter model T l (x β) i j = G.val := by
    rw [ActiveBarycenter.representativeCenter_eq_source model T l _ i j hπ, ← hG]
  rw [heq, dist_eq_norm] at hb
  have hh := (AngularChord.angularDist_le_pi_half_norm G (z (T.parent l) (T.parent_node l))).trans_lt
    (mul_lt_mul_of_pos_left hb (half_pos Real.pi_pos))
  convert hh using 1
  field_simp

/-- Initial actual shifted particles converge to their prescribed leaf centers. -/
theorem initial_particles (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) (κ CStar : ℝ) (hκ : 0 < κ)
    (hCStar : 8 * κ / (1 / (4 * (n : ℝ))) < CStar)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ β : ℝ in atTop, 1 < β ∧
      ∀ (model : Model) (X : ℝ → Configuration n d), Solves model β X →
      VisiblePrepared hN C β (X 0) → ∀ clock : ℝ → ℝ,
      ClockRelation β X (CStar * β) clock →
      ∀ (D : Block n) (hD : D ∈ T.partition 0), ∀ p ∈ D,
        angularDist (accelerated X (CStar * β) clock 0 p)
          (C (T.currentNode ⟨0, hN⟩ D hD)).center < ε := by
  have hexp : Tendsto (fun β : ℝ => Real.exp (-2 * κ * β)) atTop (𝓝 0) := by
    simpa only [Real.rpow_zero, one_mul, neg_mul] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (2 * κ) (by positivity)
  have hsum : Tendsto (fun β : ℝ => Real.exp (-2 * κ * β) + 2 * visibleScale β) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using hexp.add (ContractionScale.tendsto_visibleScale.const_mul 2)
  filter_upwards [CascadePreparation.initial_at_multiplier T hN C hC κ CStar hκ hCStar,
    hexp.eventually (gt_mem_nhds (half_pos Real.pi_pos)), hsum.eventually (gt_mem_nhds hε)]
      with β hprep hsmall herr
  refine ⟨hprep.1, ?_⟩
  intro model X hX hv clock hc D hD p hp
  obtain ⟨_, hdiam, _, z, hz, hnear⟩ := (hprep.2 model X hX hv).1 D hD
  have hpart := LiteralCenters.particle_to_mean D (T.block_nonempty 0 D hD)
    (X (CStar * β)) z hz _ hsmall hdiam p hp
  have hh := (angularDist_triangle (X (CStar * β) p) z _).trans (add_le_add hpart hnear)
  simpa only [accelerated, hc.1.1, add_zero] using hh.trans_lt herr

end Metastability.CenterLimits
