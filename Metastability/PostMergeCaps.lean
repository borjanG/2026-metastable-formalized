import Metastability.PostMergeGeometry
import Metastability.PlateauCaps
import Metastability.PlateauBootstrap

/-! Simultaneous post-merge confinement in the next enlarged current caps. -/

noncomputable section
open Filter Set
open scoped Topology RealInnerProductSpace

namespace Metastability.PostMergeCaps
open Source CapEnlargement
variable {n N d : ℕ}

theorem variable_caps_no_exit {ι : Type*} [Fintype ι] [Nonempty ι]
    (model : Model) (β : ℝ) (hβ : 0 ≤ β)
    (X : ℝ → Configuration n d) (hX : Solves model β X)
    (A : ι → Block n) (hA : ∀ k, (A k).Nonempty) (w : ι → Sphere d)
    (r R : ι → ℝ) (a b L : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hr : ∀ k, 0 ≤ r k) (hrR : ∀ k, r k < R k) (hRπ : ∀ k, R k < Real.pi / 2)
    (hentry : ∀ k, ∀ i ∈ A k, angularDist (X a i) (w k) ≤ r k)
    (hsep : ∀ u ∈ Ico a b,
      (∀ k, ∀ i ∈ A k, angularDist (X u i) (w k) ≤ R k) →
      ∀ k, ∀ i ∈ A k, ∀ j ∉ A k, L ≤ 1 - ⟪(X u i).val, (X u j).val⟫)
    (herror : ∀ k, (2 * n) * (b - a) * Real.exp (-β * L) < Real.cos (r k) - Real.cos (R k)) :
    ∀ t ∈ Icc a b, ∀ k, ∀ i ∈ A k, angularDist (X t i) (w k) < R k := by
  classical
  let s : Finset (Σ _ : ι, Fin n) := Finset.univ.sigma A
  obtain ⟨k₀⟩ := ‹Nonempty ι›
  obtain ⟨i₀, hi₀⟩ := hA k₀
  have hs : s.Nonempty := ⟨⟨k₀, i₀⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ _, hi₀⟩⟩
  let f : (Σ _ : ι, Fin n) → ℝ → ℝ := fun p u => ⟪(X u p.2).val, (w p.1).val⟫
  let v : (Σ _ : ι, Fin n) → ℝ := fun p => Real.cos (R p.1)
  have hR0 : ∀ k, 0 ≤ R k := fun k => (hr k).trans (hrR k).le
  have hRpi : ∀ k, R k ≤ Real.pi := fun k => by linarith only [hRπ k, Real.pi_pos]
  have hrpi : ∀ k, r k ≤ Real.pi := fun k => (hrR k).le.trans (hRpi k)
  have hcos : ∀ k, 0 < Real.cos (R k) := fun k =>
    Real.cos_pos_of_mem_Ioo ⟨by linarith only [hR0 k, Real.pi_pos], hRπ k⟩
  have hstart : ∀ p ∈ s, v p ≤ f p a := by
    intro p hp
    have hi := (Finset.mem_sigma.mp hp).2
    have hinner := (AngularGeometry.angularDist_le_iff_inner _ _ (hr p.1) (hrpi p.1)).mp
      (hentry p.1 p.2 hi)
    exact (Real.cos_le_cos_of_nonneg_of_le_pi (hr p.1) (hRpi p.1) (hrR p.1).le).trans hinner
  have himprove : ∀ e ∈ Icc a b,
      (∀ t ∈ Icc a e, ∀ p ∈ s, v p ≤ f p t) → ∀ p ∈ s, v p < f p e := by
    intro e he hstop p hp
    have hcap : ∀ u ∈ Icc a e, ∀ k, ∀ i ∈ A k, angularDist (X u i) (w k) ≤ R k := by
      intro u hu k i hi
      exact (AngularGeometry.angularDist_le_iff_inner _ _ (hR0 k) (hRpi k)).mpr
        (hstop u hu ⟨k, i⟩ (Finset.mem_sigma.mpr ⟨Finset.mem_univ _, hi⟩))
    have hdrift := CapDrift.cap_drift_on_interval X hX hβ (A p.1) (hA p.1) (w p.1)
      a e (r p.1) L ha (hr p.1) (hrpi p.1) (hentry p.1)
      (by
        intro u hu i hi
        exact (hcos p.1).le.trans ((AngularGeometry.angularDist_le_iff_inner _ _ (hR0 p.1) (hRpi p.1)).mp
          (hcap u ⟨hu.1, hu.2.le⟩ p.1 i hi)))
      (by
        intro u hu i hi j hj
        have hh := hsep u ⟨hu.1, hu.2.trans_le he.2⟩ (hcap u ⟨hu.1, hu.2.le⟩) p.1 i hi j hj
        linarith only [hh]) ⟨he.1, le_rfl⟩ p.2 (Finset.mem_sigma.mp hp).2
    have hle := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (sub_le_sub_right he.2 a) (show (0 : ℝ) ≤ 2 * n by positivity))
      (Real.exp_pos (-β * L)).le
    have herr := herror p.1
    change Real.cos (R p.1) < ⟪(X e p.2).val, (w p.1).val⟫
    linarith only [hdrift, hle, herr]
  have hclosed := PlateauBootstrap.persist s hs f v hab
    (fun p _ => CapDrift.coordinate_continuousOn X hX (w p.1) p.2 a b ha) hstart himprove
  intro t ht k i hi
  have hh := himprove t ht (fun u hu => hclosed u ⟨hu.1, hu.2.trans ht.2⟩)
    ⟨k, i⟩ (Finset.mem_sigma.mpr ⟨Finset.mem_univ _, hi⟩)
  exact PlateauCaps.angularDist_lt_of_cos_lt _ _ _ (hR0 k) hh

theorem eventually_drift_error (n : ℕ) (CStar δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ β : ℝ in atTop, 1 < β ∧ enlargementScale β ≤ 1 ∧
      2 * n * CStar * β * Real.exp (-7 * δ * β) ≤ (1 / 5 : ℝ) * enlargementScale β ^ 2 := by
  have he := ActiveScales.eventually_mul_exp_le_rpow (5 * (2 * n * CStar))
    (7 * δ) 1 (-(1 / 2 : ℝ)) (by positivity)
  filter_upwards [eventually_gt_atTop (1 : ℝ), he,
    tendsto_enlargementScale.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with β hβ heβ hγ
  have heq : enlargementScale β ^ 2 = β ^ (-(1 / 2 : ℝ)) := by
    rw [enlargementScale, ← Real.rpow_mul_natCast (zero_lt_one.trans hβ).le]
    congr 1
    norm_num
  simp only [Real.rpow_one] at heβ
  have hexp : -(7 * δ) * β = -7 * δ * β := by ring
  rw [hexp] at heβ
  refine ⟨hβ, hγ.le, ?_⟩
  rw [heq]
  nlinarith only [heβ]

/-- Source post-merge cap confinement and interblock separation on the entire
original-time tightening interval. The interval's separation is a conclusion,
not a premise. No initial diameter bound is needed for this cap estimate. -/
theorem post_merge_caps (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) (CStar : ℝ) (hCStar : 0 < CStar) :
    ∃ β₀ : ℝ, 1 < β₀ ∧ ∀ β ≥ β₀,
      ∀ M ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 4),
      ∀ (model : Model) (k : Fin N) (X : ℝ → Configuration n d), Solves model β X →
      ∀ a : ℝ, 0 ≤ a →
      (∀ (D : Block n) (hD : D ∈ T.partition k.castSucc), ∀ i ∈ D,
        angularDist (X a i) (C (T.currentNode k D hD)).center ≤
          (C (T.currentNode k D hD)).radius + M * enlargementScale β) →
      0 < lowerBarrier C k - treeMargin hN C ∧
      ∀ t ∈ Icc a (a + CStar * β),
        (∀ (D : Block n) (hD : D ∈ T.partition k.castSucc), ∀ i ∈ D,
          angularDist (X t i) (C (T.currentNode k D hD)).center <
            (C (T.currentNode k D hD)).radius + (M + 1) * enlargementScale β) ∧
        (∀ D ∈ T.partition k.castSucc, ∀ i ∈ D, ∀ j ∉ D,
          lowerBarrier C k - treeMargin hN C ≤ 1 - ⟪(X t i).val, (X t j).val⟫) := by
  classical
  obtain ⟨G, hG, hgeometry⟩ := PostMergeGeometry.enlarged_current_barriers T hN C hC
  obtain ⟨S, hS⟩ := eventually_atTop.mp
    (eventually_drift_error n CStar (treeMargin hN C) (treeMargin_pos hN C hC))
  refine ⟨max G S, hG.trans_le (le_max_left _ _), ?_⟩
  intro β hβ M hM model k X hX a ha hentry
  have hβG := (le_max_left _ _).trans hβ
  obtain ⟨hβ1, hscale, herror⟩ := hS β ((le_max_right _ _).trans hβ)
  have hβ0 := zero_lt_one.trans hβ1
  have hγ := enlargementScale_pos hβ0
  have hM1 : M + 1 ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 5) :=
    ⟨by linarith only [hM.1], by linarith only [hM.2]⟩
  obtain ⟨hsmall, hpair⟩ := hgeometry β hβG (M + 1) hM1
  let ι := {D : Block n // D ∈ T.partition k.castSucc}
  letI : Fintype ι := Fintype.ofFinite ι
  letI : Nonempty ι := ⟨⟨T.left k, T.left_mem k⟩⟩
  let A : ι → Block n := fun D => D.val
  let w : ι → Sphere d := fun D => (C (T.currentNode k D.val D.property)).center
  let r : ι → ℝ := fun D => (C (T.currentNode k D.val D.property)).radius + M * enlargementScale β
  let R : ι → ℝ := fun D => (C (T.currentNode k D.val D.property)).radius + (M + 1) * enlargementScale β
  let L := lowerBarrier C k - treeMargin hN C
  have hL := PostMergeGeometry.post_barrier_lower T hN C hC k
  have hab : a ≤ a + CStar * β := le_add_of_nonneg_right (mul_pos hCStar hβ0).le
  have hr : ∀ D : ι, 0 ≤ r D := fun D =>
    add_nonneg (C (T.currentNode k D.val D.property)).radius_nonneg (mul_nonneg hM.1 hγ.le)
  have hrR : ∀ D : ι, r D < R D := by
    intro D
    dsimp only [r, R]
    nlinarith only [hγ]
  have hconf := variable_caps_no_exit model β hβ0.le X hX A
    (fun D => T.block_nonempty _ _ D.property) w r R a (a + CStar * β) L ha hab hr hrR
    (fun D => hsmall _) (fun D => hentry D.val D.property) (by
      intro u _htime hc D i hi j hj
      have hall : ∀ (E : Block n) (hE : E ∈ T.partition k.castSucc), ∀ p ∈ E,
          angularDist (X u p) (C (T.currentNode k E hE)).center ≤
            (C (T.currentNode k E hE)).radius + (M + 1) * enlargementScale β :=
        fun E hE => hc ⟨E, hE⟩
      exact hpair k (X u) hall D.val D.property i hi j hj) (by
      intro D
      have hgap := PlateauCapScale.cosine_gap_lower (r D) (enlargementScale β)
        (hr D) hγ.le hscale (by
          have hh := hsmall (T.currentNode k D.val D.property)
          dsimp only [r]
          nlinarith only [hh.le])
      have hgap' : (2 / 5 : ℝ) * enlargementScale β ^ 2 ≤ Real.cos (r D) - Real.cos (R D) := by
        convert hgap using 1
        dsimp only [r, R]
        congr 1
        congr 1
        ring
      have hExp : Real.exp (-β * L) ≤ Real.exp (-7 * treeMargin hN C * β) := by
        apply Real.exp_le_exp.mpr
        dsimp only [L]
        nlinarith only [mul_le_mul_of_nonneg_left hL hβ0.le]
      have hh := mul_le_mul_of_nonneg_left hExp
        (show (0 : ℝ) ≤ 2 * n * CStar * β by positivity)
      have heq : (2 * n) * (a + CStar * β - a) * Real.exp (-β * L) =
          (2 * n * CStar * β) * Real.exp (-β * L) := by ring
      rw [heq]
      have hsquare : 0 < enlargementScale β ^ 2 := sq_pos_of_pos hγ
      nlinarith only [hh, herror, hgap', hsquare])
  refine ⟨PostMergeGeometry.post_barrier_pos T hN C hC k, ?_⟩
  intro t ht
  have hall : ∀ (D : Block n) (hD : D ∈ T.partition k.castSucc), ∀ i ∈ D,
      angularDist (X t i) (C (T.currentNode k D hD)).center <
        (C (T.currentNode k D hD)).radius + (M + 1) * enlargementScale β :=
    fun D hD => hconf t ht ⟨D, hD⟩
  exact ⟨hall, hpair k (X t) (fun D hD i hi => (hall D hD i hi).le)⟩

end Metastability.PostMergeCaps
