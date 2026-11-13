import Metastability.ActiveBarycenter
import Metastability.InactiveCenterMotion
import Metastability.AngularChord

/-! Source particle-center propagation through one entire active collision.
The literal entry barycenter, actual ODE, and original inverse clock are used
throughout; reduced vector dynamics and regularity are proved dependencies. -/
noncomputable section
open Set Filter
open scoped Topology RealInnerProductSpace
namespace Metastability.StageCenterPropagation
open Source ActiveScales ActiveSourceLaw CapEnlargement ActiveBarycenter AngularGeometry
variable {n N d : ℕ}

theorem point_endpoint_bounds (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (u v : Sphere d) (hπ : angularDist u v < Real.pi) :
    angularDist u (GeodesicBarycenter.point a b ha hb u v hπ) ≤ angularDist u v ∧
    angularDist v (GeodesicBarycenter.point a b ha hb u v hπ) ≤ angularDist u v := by
  have hh := GeodesicBarycenter.angularDist_add a b ha hb u v hπ
  have hl := angularDist_nonneg u (GeodesicBarycenter.point a b ha hb u v hπ)
  have hr := angularDist_nonneg (GeodesicBarycenter.point a b ha hb u v hπ) v
  constructor
  · linarith only [hh, hr]
  · rw [angularDist_comm]
    linarith only [hh, hl]

/-- The entry representative barycenter controls every active particle before
and after the mesoscopic hit. All inactive particles retain their entry
positions uniformly through the closed completion endpoint. -/
theorem source_propagation (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) (κ : ℝ) (hκ : 4 < κ)
    (H : ℝ) (hH : 0 < H) (ε : ℝ) (hε : 0 < ε) :
    ∃ β₀ : ℝ, 1 < β₀ ∧ ∀ β ≥ β₀,
      ∀ M ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 5), ∀ (model : Model) (l : Fin N)
      (X : ℝ → Configuration n d), Solves model β X →
      ∀ shift : ℝ, 0 ≤ shift → ∀ clock : ℝ → ℝ, ClockRelation β X shift clock →
      ∀ i j : Fin n, i ∈ T.left l → j ∈ T.right l →
      ∀ a h b : ℝ, 0 ≤ a → a ≤ h → h ≤ b → b - a ≤ H →
      (∀ t ∈ Icc a b, StageHyp T C β κ M l (accelerated X shift clock t)) →
      (∀ t ∈ Icc a b, 1 - ⟪(accelerated X shift clock t i).val, (accelerated X shift clock t j).val⟫ ≤
        upperBarrier C l + 2 * treeMargin hN C) →
      (∀ t ∈ Ico a b, ¬ ∀ p ∈ T.parent l, ∀ q ∈ T.parent l,
        angularDist (accelerated X shift clock t p) (accelerated X shift clock t q) ≤ clockCutoff β) →
      (∀ t ∈ Icc a h, mesoscopicScale β ≤
        angularDist (accelerated X shift clock t i) (accelerated X shift clock t j)) →
      (∀ t ∈ Icc h b, angularDist (accelerated X shift clock t i)
        (accelerated X shift clock t j) ≤ mesoscopicScale β) →
      ∃ G : Sphere d,
        (∃ hπ : angularDist (accelerated X shift clock a i) (accelerated X shift clock a j) < Real.pi,
          G.val = geodesicBarycenter (centerWeight model (T.left l)) (centerWeight model (T.right l))
            (centerWeight_pos model _ (T.block_nonempty _ _ (T.left_mem l)))
            (centerWeight_pos model _ (T.block_nonempty _ _ (T.right_mem l)))
            (accelerated X shift clock a i) (accelerated X shift clock a j) hπ) ∧
        (∀ t ∈ Icc a h, ∀ p ∈ T.parent l,
          angularDist (accelerated X shift clock t p) G ≤
            angularDist (accelerated X shift clock t i) (accelerated X shift clock t j) + ε) ∧
        (∀ t ∈ Icc h b, ∀ p ∈ T.parent l, angularDist (accelerated X shift clock t p) G < ε) ∧
        (∀ t ∈ Icc a b, ∀ D ∈ T.partition l.castSucc,
          D ≠ T.left l → D ≠ T.right l → ∀ p ∈ D,
          angularDist (accelerated X shift clock t p) (accelerated X shift clock a p) < ε) := by
  have hκ0 : 0 < κ := by linarith only [hκ]
  obtain ⟨A, hA, hactive⟩ := uniformly_small_variation T hN C hC κ hκ H hH
    (ε / (2 * Real.pi)) (by positivity)
  obtain ⟨Q, hQ, hterminal⟩ := TerminalCenterMotion.terminal_confinement T hN C hC κ hκ H hH
  obtain ⟨I, hI, hinactive⟩ := InactiveCenterMotion.inactive_centers T hN C hC κ hκ H hH
  have hexp : Tendsto (fun β : ℝ => Real.exp (-κ * β)) atTop (𝓝 0) := by
    simpa only [Real.rpow_zero, one_mul] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 κ hκ0
  obtain ⟨E, hE⟩ := eventually_atTop.mp
    ((hexp.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 4 by positivity))).and
      ((tendsto_mesoscopicScale.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 20 by positivity))).and
        (tendsto_enlargementScale.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 4 by positivity)))))
  refine ⟨max (max A Q) (max I E), hA.trans_le ((le_max_left A Q).trans (le_max_left _ _)), ?_⟩
  intro β hβ M hM model l X hX shift hshift clock hc i j hi hj a h b ha hah hhb hlen hs hu hnc hpre hpost
  have hβA := (le_max_left A Q).trans ((le_max_left _ _).trans hβ)
  have hβQ := (le_max_right A Q).trans ((le_max_left _ _).trans hβ)
  have hβI := (le_max_left I E).trans ((le_max_right _ _).trans hβ)
  have hβE := (le_max_right I E).trans ((le_max_right _ _).trans hβ)
  obtain ⟨hδ, hm, hγ⟩ := hE β hβE
  have hab := hah.trans hhb
  have hU := (source_barrier_parameters T hN C hC κ hκ l).2.2.2.2
  have hπ : ∀ t ∈ Icc a b,
      angularDist (accelerated X shift clock t i) (accelerated X shift clock t j) < Real.pi := by
    intro t ht
    apply Real.arccos_lt_pi.mpr
    linarith only [hu t ht, hU]
  let aB := centerWeight model (T.left l)
  let aC := centerWeight model (T.right l)
  have haB : 0 < aB := centerWeight_pos model _ (T.block_nonempty _ _ (T.left_mem l))
  have haC : 0 < aC := centerWeight_pos model _ (T.block_nonempty _ _ (T.right_mem l))
  let G := GeodesicBarycenter.point aB aC haB haC
    (accelerated X shift clock a i) (accelerated X shift clock a j) (hπ a ⟨le_rfl, hab⟩)
  have hhvar := hactive β hβA M hM model l X hX shift hshift clock hc i j hi hj a h ha hah
    (by linarith only [hlen, hhb]) (fun t ht => hs t ⟨ht.1, ht.2.trans hhb⟩)
    (fun t ht => hu t ⟨ht.1, ht.2.trans hhb⟩) hpre
  have hnear : ∀ t ∈ Icc a h,
      angularDist (accelerated X shift clock t i) G ≤
        angularDist (accelerated X shift clock t i) (accelerated X shift clock t j) + ε / 4 ∧
      angularDist (accelerated X shift clock t j) G ≤
        angularDist (accelerated X shift clock t i) (accelerated X shift clock t j) + ε / 4 := by
    intro t ht
    let Gt := GeodesicBarycenter.point aB aC haB haC
      (accelerated X shift clock t i) (accelerated X shift clock t j) (hπ t ⟨ht.1, ht.2.trans hhb⟩)
    have hvec : ‖Gt.val - G.val‖ < ε / (2 * Real.pi) := by
      have hh := hhvar t ht
      rw [representativeCenter_eq_source model T l _ i j (hπ t ⟨ht.1, ht.2.trans hhb⟩),
        representativeCenter_eq_source model T l _ i j (hπ a ⟨le_rfl, hab⟩)] at hh
      exact hh
    have hdist : angularDist Gt G < ε / 4 := by
      have hh := (AngularChord.angularDist_le_pi_half_norm Gt G).trans_lt
        (mul_lt_mul_of_pos_left hvec (half_pos Real.pi_pos))
      convert hh using 1
      field_simp
      norm_num
    have hep := point_endpoint_bounds aB aC haB haC
      (accelerated X shift clock t i) (accelerated X shift clock t j) (hπ t ⟨ht.1, ht.2.trans hhb⟩)
    constructor
    · exact (angularDist_triangle _ Gt G).trans (add_le_add hep.1 hdist.le)
    · exact (angularDist_triangle _ Gt G).trans (add_le_add hep.2 hdist.le)
  refine ⟨G, ⟨hπ a ⟨le_rfl, hab⟩, rfl⟩, ?_, ?_, ?_⟩
  · intro t ht p hp
    have hn := hnear t ht
    rcases Finset.mem_union.mp hp with hp | hp
    · have hd := (hs t ⟨ht.1, ht.2.trans hhb⟩).1 _ (T.left_mem l) p hp i hi
      have hh := angularDist_triangle (accelerated X shift clock t p) (accelerated X shift clock t i) G
      linarith only [hh, hd, hn.1, hδ, hε]
    · have hd := (hs t ⟨ht.1, ht.2.trans hhb⟩).1 _ (T.right_mem l) p hp j hj
      have hh := angularDist_triangle (accelerated X shift clock t p) (accelerated X shift clock t j) G
      linarith only [hh, hd, hn.2, hδ, hε]
  · have hterm := hterminal β hβQ M hM model l X hX shift hshift clock hc i j hi hj h b
      (ha.trans hah) hhb (by linarith only [hlen, hah])
      (fun t ht => hs t ⟨hah.trans ht.1, ht.2⟩)
      (fun t ht => hu t ⟨hah.trans ht.1, ht.2⟩)
      (fun t ht => hnc t ⟨hah.trans ht.1, ht.2⟩) (hpost h ⟨le_rfl, hhb⟩)
    have hhnear := (hnear h ⟨hah, le_rfl⟩).1
    have hhangle := hpost h ⟨le_rfl, hhb⟩
    intro t ht p hp
    have hd := (hterm t ht).1 p hp
    have hh := angularDist_triangle (accelerated X shift clock t p) (accelerated X shift clock h i) G
    linarith only [hh, hd, hhnear, hhangle, hm, hε]
  · intro t ht D hD hDl hDr p hp
    obtain ⟨_, z₀, _, hconf⟩ := hinactive β hβI M hM model l X hX shift hshift clock hc
      i j hi hj a b ha hab hlen hs hu hnc D hD hDl hDr
    have hh := (hconf t ht).2.1 p hp
    linarith only [hh, hγ]

end Metastability.StageCenterPropagation
