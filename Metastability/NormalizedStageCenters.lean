import Metastability.StageCenterPropagation
import Metastability.BarycenterContinuity
import Metastability.LiteralCenters

/-! Literal normalized-mean centers during a completed active stage. This
bridge retains the explicit closed stage/angle hypotheses of the particle
propagation helper. It constructs all means and their nonvanishing, and uses
uniform continuity of the genuine geodesic barycenter, including coincidence. -/
noncomputable section
open Set Filter
open scoped Topology RealInnerProductSpace
namespace Metastability.NormalizedStageCenters
open Source AngularGeometry BarycenterFormula BarycenterContinuity
open ActiveScales ActiveSourceLaw CapEnlargement
variable {n N d : ℕ}

/-- Uniform replacement of both inputs to the literal barycenter on a fixed
non-antipodal region. No positive lower angle is required. -/
theorem point_replacement (a b R ε : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hR : R < Real.pi) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p q u v : Sphere d), angularDist p q ≤ R →
      angularDist p u ≤ δ → angularDist q v ≤ δ →
      ∃ hpq : angularDist p q < Real.pi, ∃ huv : angularDist u v < Real.pi,
        angularDist (GeodesicBarycenter.point a b ha hb u v huv)
          (GeodesicBarycenter.point a b ha hb p q hpq) < ε := by
  let R' := (R + Real.pi) / 2
  have hR' : R' < Real.pi := by dsimp only [R']; linarith only [hR]
  obtain ⟨η, hη, hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (uniformContinuousOn_vector (d := d) a b R' ha hb hR') (ε / Real.pi) (div_pos hε Real.pi_pos)
  let δ := min (η / 2) ((Real.pi - R) / 8)
  have hδ : 0 < δ := lt_min (half_pos hη) (div_pos (sub_pos.mpr hR) (by norm_num))
  refine ⟨δ, hδ, ?_⟩
  intro p q u v hpq hpu hqv
  have hdη : δ < η := (min_le_left _ _).trans_lt (half_lt_self hη)
  have hdR : δ ≤ (Real.pi - R) / 8 := min_le_right _ _
  have huv : angularDist u v ≤ R' := by
    have htri := angularDist_triangle u p v
    have htri' := angularDist_triangle p q v
    rw [angularDist_comm u p] at htri
    dsimp only [R']
    linarith only [htri, htri', hpq, hpu, hqv, hdR, hR]
  have hpq' : angularDist p q ≤ R' := by dsimp only [R']; linarith only [hpq, hR]
  have hdist : dist (p, q) (u, v) < η := by
    rw [Prod.dist_eq]
    apply max_lt
    · exact (norm_sub_le_angularDist p u).trans_lt (hpu.trans_lt hdη)
    · exact (norm_sub_le_angularDist q v).trans_lt (hqv.trans_lt hdη)
  have hvectors := hclose (p, q) hpq' (u, v) huv hdist
  have hpqπ := hpq.trans_lt hR
  have huvπ := huv.trans_lt hR'
  refine ⟨hpqπ, huvπ, ?_⟩
  rw [vector_eq_point a b ha hb p q hpqπ, vector_eq_point a b ha hb u v huvπ] at hvectors
  have hn : ‖(GeodesicBarycenter.point a b ha hb u v huvπ).val -
      (GeodesicBarycenter.point a b ha hb p q hpqπ).val‖ < ε / Real.pi := by
    simpa only [dist_eq_norm, norm_sub_rev] using hvectors
  have hangle := (AngularChord.angularDist_le_pi_half_norm
    (GeodesicBarycenter.point a b ha hb u v huvπ)
    (GeodesicBarycenter.point a b ha hb p q hpqπ)).trans_lt
      (mul_lt_mul_of_pos_left hn (half_pos Real.pi_pos))
  have heq : (Real.pi / 2) * (ε / Real.pi) = ε / 2 := by field_simp
  rw [heq] at hangle
  exact hangle.trans (half_lt_self hε)

/-- The literal normalized means of the two tight children exist and are
within the child diameter of any fixed representatives. -/
theorem exists_child_means (T : CollisionTree n N) (l : Fin N)
    (x : Configuration n d) (δ : ℝ) (hδ : δ < Real.pi / 2)
    (htight : ∀ D ∈ T.partition l.castSucc, ∀ p ∈ D, ∀ q ∈ D,
      angularDist (x p) (x q) ≤ δ)
    (i j : Fin n) (hi : i ∈ T.left l) (hj : j ∈ T.right l) :
    let hB := T.block_nonempty _ _ (T.left_mem l)
    let hC := T.block_nonempty _ _ (T.right_mem l)
    BlockGeometry.blockMean (T.left l) hB x ≠ 0 ∧
      BlockGeometry.blockMean (T.right l) hC x ≠ 0 ∧
      ∃ u v : Sphere d,
        u.val = ‖BlockGeometry.blockMean (T.left l) hB x‖⁻¹ • BlockGeometry.blockMean (T.left l) hB x ∧
        v.val = ‖BlockGeometry.blockMean (T.right l) hC x‖⁻¹ • BlockGeometry.blockMean (T.right l) hC x ∧
        angularDist (x i) u ≤ δ ∧ angularDist (x j) v ≤ δ := by
  let hB := T.block_nonempty _ _ (T.left_mem l)
  let hC := T.block_nonempty _ _ (T.right_mem l)
  obtain ⟨CB, _, hCB⟩ := BlockGeometry.exists_cap_of_diameter (T.left l) hB x hδ (htight _ (T.left_mem l))
  obtain ⟨CC, _, hCC⟩ := BlockGeometry.exists_cap_of_diameter (T.right l) hC x hδ (htight _ (T.right_mem l))
  let u := BlockGeometry.normalizedMean (T.left l) hB x CB hCB
  let v := BlockGeometry.normalizedMean (T.right l) hC x CC hCC
  exact ⟨BlockGeometry.blockMean_ne_zero_of_diameter _ hB x hδ (htight _ (T.left_mem l)),
    BlockGeometry.blockMean_ne_zero_of_diameter _ hC x hδ (htight _ (T.right_mem l)),
    u, v, rfl, rfl,
    BlockGeometry.angularDist_normalizedMean_le_of_diameter _ hB x CB hCB hδ (htight _ (T.left_mem l)) hi,
    BlockGeometry.angularDist_normalizedMean_le_of_diameter _ hC x CC hCC hδ (htight _ (T.right_mem l)) hj⟩


/-- Literal mean-center propagation on an actual stage interval. The displayed
stage/angle assumptions are the same explicit conditional inputs as in the
particle producer; neither existence of means nor barycenter continuity is
assumed. The terminal conclusion includes the completed-parent endpoint. -/
theorem normalized_propagation (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) (κ : ℝ) (hκ : 4 < κ)
    (model : Model) (l : Fin N) (H : ℝ) (hH : 0 < H) (ε : ℝ) (hε : 0 < ε) :
    ∃ β₀ : ℝ, 1 < β₀ ∧ ∀ β ≥ β₀,
      ∀ M ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 5),
      ∀ (X : ℝ → Configuration n d), Solves model β X →
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
      let Y := accelerated X shift clock
      let hB := T.block_nonempty _ _ (T.left_mem l)
      let hD := T.block_nonempty _ _ (T.right_mem l)
      let hA := hB.mono Finset.subset_union_left
      let wB := centerWeight model (T.left l)
      let wD := centerWeight model (T.right l)
      let hwB := centerWeight_pos model _ hB
      let hwD := centerWeight_pos model _ hD
      ∃ u₀ v₀ G : Sphere d,
        u₀.val = ‖BlockGeometry.blockMean (T.left l) hB (Y a)‖⁻¹ • BlockGeometry.blockMean (T.left l) hB (Y a) ∧
        v₀.val = ‖BlockGeometry.blockMean (T.right l) hD (Y a)‖⁻¹ • BlockGeometry.blockMean (T.right l) hD (Y a) ∧
        BlockGeometry.blockMean (T.left l) hB (Y a) ≠ 0 ∧
        BlockGeometry.blockMean (T.right l) hD (Y a) ≠ 0 ∧
        (∃ hπ : angularDist u₀ v₀ < Real.pi,
          G.val = geodesicBarycenter wB wD hwB hwD u₀ v₀ hπ) ∧
        (∀ t ∈ Icc a b,
          BlockGeometry.blockMean (T.left l) hB (Y t) ≠ 0 ∧
          BlockGeometry.blockMean (T.right l) hD (Y t) ≠ 0 ∧
          ∃ u v : Sphere d,
            u.val = ‖BlockGeometry.blockMean (T.left l) hB (Y t)‖⁻¹ • BlockGeometry.blockMean (T.left l) hB (Y t) ∧
            v.val = ‖BlockGeometry.blockMean (T.right l) hD (Y t)‖⁻¹ • BlockGeometry.blockMean (T.right l) hD (Y t) ∧
            (∃ hπ : angularDist u v < Real.pi,
              angularDist (GeodesicBarycenter.point wB wD hwB hwD u v hπ) G < ε) ∧
            angularDist u G ≤ angularDist (Y t i) (Y t j) + ε ∧
            angularDist v G ≤ angularDist (Y t i) (Y t j) + ε) ∧
        (∀ t ∈ Icc h b,
          BlockGeometry.blockMean (T.parent l) hA (Y t) ≠ 0 ∧ ∃ z : Sphere d,
            z.val = ‖BlockGeometry.blockMean (T.parent l) hA (Y t)‖⁻¹ • BlockGeometry.blockMean (T.parent l) hA (Y t) ∧
            angularDist z G < ε) := by
  let η := min (ε / 10) (Real.pi / 10)
  have hη : 0 < η := lt_min (div_pos hε (by norm_num)) (div_pos Real.pi_pos (by norm_num))
  have hηε : 10 * η ≤ ε := by have hh := min_le_left (ε / 10) (Real.pi / 10); dsimp only [η]; linarith only [hh]
  have hηπ : η < Real.pi / 2 := by
    have hh := min_le_right (ε / 10) (Real.pi / 10)
    dsimp only [η]
    linarith only [hh, Real.pi_pos]
  let wB := centerWeight model (T.left l)
  let wD := centerWeight model (T.right l)
  have hwB : 0 < wB := centerWeight_pos model _ (T.block_nonempty _ _ (T.left_mem l))
  have hwD : 0 < wD := centerWeight_pos model _ (T.block_nonempty _ _ (T.right_mem l))
  let U := upperBarrier C l + 2 * treeMargin hN C
  let R := Real.arccos (1 - U)
  have hU := (source_barrier_parameters T hN C hC κ hκ l).2.2.2.2
  have hR : R < Real.pi := Real.arccos_lt_pi.mpr (by dsimp only [U]; linarith only [hU])
  obtain ⟨δ, hδ, hreplace⟩ := point_replacement (d := d) wB wD R η hwB hwD hR hη
  obtain ⟨P, hP, hparticle⟩ := StageCenterPropagation.source_propagation T hN C hC κ hκ H hH η hη
  obtain ⟨V, hV, hvariation⟩ := ActiveBarycenter.uniformly_small_variation T hN C hC κ hκ H hH
    (η / Real.pi) (div_pos hη Real.pi_pos)
  have hexp : Tendsto (fun β : ℝ => Real.exp (-κ * β)) atTop (𝓝 0) := by
    simpa only [Real.rpow_zero, one_mul] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 κ (by linarith only [hκ])
  obtain ⟨E, hE⟩ := eventually_atTop.mp
    ((hexp.eventually (gt_mem_nhds hδ)).and
      ((hexp.eventually (gt_mem_nhds hη)).and
        (hexp.eventually (gt_mem_nhds (half_pos Real.pi_pos)))))
  refine ⟨max P (max V E), hP.trans_le (le_max_left _ _), ?_⟩
  intro β hβ M hM X hX shift hshift clock hc i j hi hj a h b ha hah hhb hlen hstage hupper hnc hpre hpost
  have hβP := (le_max_left P (max V E)).trans hβ
  have hβV := (le_max_left V E).trans ((le_max_right P (max V E)).trans hβ)
  have hβE := (le_max_right V E).trans ((le_max_right P (max V E)).trans hβ)
  obtain ⟨heδ, heη, heπ⟩ := hE β hβE
  let Y := accelerated X shift clock
  have hab := hah.trans hhb
  have haab : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hrepR : ∀ t ∈ Icc a b, angularDist (Y t i) (Y t j) ≤ R := by
    intro t ht
    exact Real.arccos_le_arccos (by have hh := hupper t ht; dsimp only [U]; linarith only [hh])
  obtain ⟨Gp, ⟨hpa, hGp⟩, hparentPre, hparentPost, _⟩ :=
    hparticle β hβP M hM model l X hX shift hshift clock hc i j hi hj a h b ha hah hhb hlen
      hstage hupper hnc hpre hpost
  have hGpPoint : GeodesicBarycenter.point wB wD hwB hwD (Y a i) (Y a j) hpa = Gp :=
    Subtype.ext hGp.symm
  obtain ⟨hB0, hD0, u₀, v₀, hu₀, hv₀, hpu₀, hqv₀⟩ :=
    exists_child_means T l (Y a) (Real.exp (-κ * β)) heπ (hstage a haab).1 i j hi hj
  obtain ⟨hpq₀, huv₀, hGclose⟩ := hreplace (Y a i) (Y a j) u₀ v₀ (hrepR a haab)
    (hpu₀.trans heδ.le) (hqv₀.trans heδ.le)
  let G := GeodesicBarycenter.point wB wD hwB hwD u₀ v₀ huv₀
  have hGGp : angularDist G Gp < η := by
    simpa only [hGpPoint] using hGclose
  have hπ : ∀ t ∈ Icc a b, angularDist (Y t i) (Y t j) < Real.pi :=
    fun t ht => (hrepR t ht).trans_lt hR
  have hvar := hvariation β hβV M hM model l X hX shift hshift clock hc i j hi hj a h ha hah
    (by linarith only [hlen, hhb]) (fun t ht => hstage t ⟨ht.1, ht.2.trans hhb⟩)
    (fun t ht => hupper t ⟨ht.1, ht.2.trans hhb⟩) hpre
  have hrepbar : ∀ (t : ℝ) (ht : t ∈ Icc a b),
      angularDist (GeodesicBarycenter.point wB wD hwB hwD (Y t i) (Y t j) (hπ t ht)) Gp ≤ η := by
    intro t ht
    by_cases hth : t ≤ h
    · have hv := hvar t ⟨ht.1, hth⟩
      rw [ActiveBarycenter.representativeCenter_eq_source model T l _ i j (hπ t ht),
        ActiveBarycenter.representativeCenter_eq_source model T l _ i j hpa] at hv
      have hn : ‖(GeodesicBarycenter.point wB wD hwB hwD (Y t i) (Y t j) (hπ t ht)).val - Gp.val‖ < η / Real.pi := by
        simpa only [hGp] using hv
      have hh := (AngularChord.angularDist_le_pi_half_norm _ Gp).trans_lt
        (mul_lt_mul_of_pos_left hn (half_pos Real.pi_pos))
      have heq : (Real.pi / 2) * (η / Real.pi) = η / 2 := by field_simp
      rw [heq] at hh
      exact hh.le.trans (half_le_self hη.le)
    · let cap : SphericalCap d := ⟨Gp, η, hη.le, hηπ⟩
      exact GeodesicBarycenter.point_mem_cap wB wD hwB hwD (Y t i) (Y t j) (hπ t ht) cap
        ((hparentPost t ⟨(lt_of_not_ge hth).le, ht.2⟩ i (Finset.mem_union_left _ hi)).le)
        ((hparentPost t ⟨(lt_of_not_ge hth).le, ht.2⟩ j (Finset.mem_union_right _ hj)).le)
  have hrepNear : ∀ t ∈ Icc a b,
      angularDist (Y t i) Gp ≤ angularDist (Y t i) (Y t j) + η ∧
      angularDist (Y t j) Gp ≤ angularDist (Y t i) (Y t j) + η := by
    intro t ht
    by_cases hth : t ≤ h
    · exact ⟨hparentPre t ⟨ht.1, hth⟩ i (Finset.mem_union_left _ hi),
        hparentPre t ⟨ht.1, hth⟩ j (Finset.mem_union_right _ hj)⟩
    · have htpost : t ∈ Icc h b := ⟨(lt_of_not_ge hth).le, ht.2⟩
      have hangle0 := angularDist_nonneg (Y t i) (Y t j)
      exact ⟨(hparentPost t htpost i (Finset.mem_union_left _ hi)).le.trans (by linarith only [hangle0]),
        (hparentPost t htpost j (Finset.mem_union_right _ hj)).le.trans (by linarith only [hangle0])⟩
  refine ⟨u₀, v₀, G, hu₀, hv₀, hB0, hD0, ⟨huv₀, rfl⟩, ?_, ?_⟩
  · intro t ht
    obtain ⟨hBt, hDt, u, v, hu, hv, hpu, hqv⟩ :=
      exists_child_means T l (Y t) (Real.exp (-κ * β)) heπ (hstage t ht).1 i j hi hj
    obtain ⟨hpq, huv, hbar⟩ := hreplace (Y t i) (Y t j) u v (hrepR t ht)
      (hpu.trans heδ.le) (hqv.trans heδ.le)
    refine ⟨hBt, hDt, u, v, hu, hv, ⟨huv, ?_⟩, ?_, ?_⟩
    · have htri := angularDist_triangle (GeodesicBarycenter.point wB wD hwB hwD u v huv)
        (GeodesicBarycenter.point wB wD hwB hwD (Y t i) (Y t j) hpq) G
      have htri' := angularDist_triangle
        (GeodesicBarycenter.point wB wD hwB hwD (Y t i) (Y t j) hpq) Gp G
      have hr := hrepbar t ht
      rw [angularDist_comm Gp G] at htri'
      linarith only [htri, htri', hbar, hr, hGGp, hηε, hη]
    · have ht1 := angularDist_triangle u (Y t i) G
      have ht2 := angularDist_triangle (Y t i) Gp G
      rw [angularDist_comm u (Y t i)] at ht1
      rw [angularDist_comm Gp G] at ht2
      have hr := (hrepNear t ht).1
      linarith only [ht1, ht2, hpu, hr, hGGp, heη, hηε, hη]
    · have ht1 := angularDist_triangle v (Y t j) G
      have ht2 := angularDist_triangle (Y t j) Gp G
      rw [angularDist_comm v (Y t j)] at ht1
      rw [angularDist_comm Gp G] at ht2
      have hr := (hrepNear t ht).2
      linarith only [ht1, ht2, hqv, hr, hGGp, heη, hηε, hη]
  · intro t ht
    obtain ⟨hnz, z, hz, hzg⟩ := PreparationGeometry.exists_mean_near_center
      (T.parent l) ((T.block_nonempty _ _ (T.left_mem l)).mono Finset.subset_union_left)
      (Y t) Gp η hη.le hηπ (fun p hp => (hparentPost t ht p hp).le)
    refine ⟨hnz, z, hz, ?_⟩
    have htri := angularDist_triangle z Gp G
    rw [angularDist_comm Gp G] at htri
    linarith only [htri, hzg, hGGp, hηε, hη]

end Metastability.NormalizedStageCenters
