import Metastability.TerminalCenterMotion

/-! Literal normalized centers of inactive blocks remain uniformly close to
their entry values throughout the collision, including parent completion. -/
noncomputable section
open Set Filter
open scoped Topology RealInnerProductSpace
namespace Metastability.InactiveCenterMotion
open Source CapEnlargement ActiveScales ActiveSourceLaw
variable {n N d : ℕ}

theorem eventually_parameters (H κ δ : ℝ) (hH : 0 ≤ H) (hκ : 0 < κ) (hδ : 0 < δ) :
    ∀ᶠ β : ℝ in atTop, 1 < β ∧ enlargementScale β ≤ 1 ∧
      2 * enlargementScale β < Real.pi / 2 ∧ Real.exp (-κ * β) ≤ enlargementScale β ∧
      4 * n * H * Real.log β * Real.exp (-(5 * δ) * β) < enlargementScale β ^ 2 / 2 := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    tendsto_enlargementScale.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    tendsto_enlargementScale.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < Real.pi / 4)),
    eventually_mul_exp_le_rpow 1 κ 0 (-(1 / 4 : ℝ)) hκ,
    eventually_mul_exp_le_rpow (16 * n * H) (5 * δ) 1 (-(1 / 2 : ℝ)) (by positivity)]
      with β hβ hγ hπ hδβ he
  have hβ0 := zero_lt_one.trans hβ
  have hsq : enlargementScale β ^ 2 = β ^ (-(1 / 2 : ℝ)) := by
    rw [enlargementScale, ← Real.rpow_mul_natCast hβ0.le]
    congr 1
    norm_num
  have hδ' : Real.exp (-κ * β) ≤ enlargementScale β := by
    simpa only [enlargementScale, Real.rpow_zero, one_mul] using hδβ
  refine ⟨hβ, hγ.le, by linarith only [hπ], hδ', ?_⟩
  rw [Real.rpow_one, ← hsq] at he
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.log_le_self hβ0.le) (show (0 : ℝ) ≤ 4 * n * H by positivity))
    (Real.exp_pos (-(5 * δ) * β)).le
  have hp := sq_pos_of_pos (enlargementScale_pos hβ0)
  nlinarith only [he, hh, hp]

/-- Source inactive-center propagation with an explicit vanishing angular
bound. Nonvanishing and the normalized arithmetic means are conclusions. -/
theorem inactive_centers (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) (κ : ℝ) (hκ : 4 < κ)
    (H : ℝ) (hH : 0 < H) :
    ∃ β₀ : ℝ, 1 < β₀ ∧ ∀ β ≥ β₀,
      ∀ M ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 5), ∀ (model : Model) (l : Fin N)
      (X : ℝ → Configuration n d), Solves model β X →
      ∀ shift : ℝ, 0 ≤ shift → ∀ clock : ℝ → ℝ, ClockRelation β X shift clock →
      ∀ i j : Fin n, i ∈ T.left l → j ∈ T.right l →
      ∀ a b : ℝ, 0 ≤ a → a ≤ b → b - a ≤ H →
      (∀ t ∈ Icc a b, StageHyp T C β κ M l (accelerated X shift clock t)) →
      (∀ t ∈ Icc a b, 1 - ⟪(accelerated X shift clock t i).val, (accelerated X shift clock t j).val⟫ ≤
        upperBarrier C l + 2 * treeMargin hN C) →
      (∀ t ∈ Ico a b, ¬ ∀ p ∈ T.parent l, ∀ q ∈ T.parent l,
        angularDist (accelerated X shift clock t p) (accelerated X shift clock t q) ≤ clockCutoff β) →
      ∀ (D : Block n) (hD : D ∈ T.partition l.castSucc), D ≠ T.left l → D ≠ T.right l →
      let hne := T.block_nonempty _ _ hD
      BlockGeometry.blockMean D hne (accelerated X shift clock a) ≠ 0 ∧ ∃ z₀ : Sphere d,
        z₀.val = ‖BlockGeometry.blockMean D hne (accelerated X shift clock a)‖⁻¹ •
          BlockGeometry.blockMean D hne (accelerated X shift clock a) ∧
        ∀ t ∈ Icc a b,
          (∀ p ∈ D, angularDist (accelerated X shift clock t p) z₀ < 2 * enlargementScale β) ∧
          (∀ p ∈ D, angularDist (accelerated X shift clock t p)
            (accelerated X shift clock a p) < 4 * enlargementScale β) ∧
          BlockGeometry.blockMean D hne (accelerated X shift clock t) ≠ 0 ∧ ∃ z : Sphere d,
            z.val = ‖BlockGeometry.blockMean D hne (accelerated X shift clock t)‖⁻¹ •
              BlockGeometry.blockMean D hne (accelerated X shift clock t) ∧
            angularDist z z₀ ≤ 2 * enlargementScale β := by
  obtain ⟨S, hS, hscalar⟩ := CompletionScalar.interval_bounds T hN C hC κ hκ
  obtain ⟨G, hG, hgeo⟩ := ActiveGeometry.stage_barriers T hN C hC
  obtain ⟨E, hE⟩ := eventually_atTop.mp (eventually_parameters (n := n) H κ
    (treeMargin hN C) hH.le (by linarith only [hκ]) (treeMargin_pos hN C hC))
  refine ⟨max S (max G E), hS.trans_le (le_max_left _ _), ?_⟩
  intro β hβ M hM model l X hX shift hshift clock hc i j hi hj a b ha hab hlen hs hu hnc D hD hDl hDr
  have hβS := (le_max_left S (max G E)).trans hβ
  have hβG := (le_max_left G E).trans ((le_max_right S (max G E)).trans hβ)
  have hβE := (le_max_right G E).trans ((le_max_right S (max G E)).trans hβ)
  obtain ⟨hβ1, hγ1, hπ, hδ, herr⟩ := hE β hβE
  have hγ := enlargementScale_pos (zero_lt_one.trans hβ1)
  have hδπ : Real.exp (-κ * β) < Real.pi / 2 := by linarith only [hδ, hπ, hγ]
  have hd := (hs a ⟨le_rfl, hab⟩).1 D hD
  let hne := T.block_nonempty _ _ hD
  obtain ⟨F, _, hF⟩ := BlockGeometry.exists_cap_of_diameter D hne
    (accelerated X shift clock a) hδπ hd
  let z₀ := BlockGeometry.normalizedMean D hne (accelerated X shift clock a) F hF
  have hz₀ : ∀ p ∈ D, angularDist (accelerated X shift clock a p) z₀ ≤ enlargementScale β := by
    intro p hp
    exact (BlockGeometry.angularDist_normalizedMean_le_of_diameter D hne
      (accelerated X shift clock a) F hF hδπ hd hp).trans hδ
  have hext : ∀ t ∈ Ico a b, ∀ p ∈ D, ∀ q ∉ D,
      upperBarrier C l + 7 * treeMargin hN C ≤
        1 - ⟪(accelerated X shift clock t p).val, (accelerated X shift clock t q).val⟫ := by
    intro t ht
    exact PlateauCapGeometry.inactive_barrier_of_nonactive_pairs T l
      (accelerated X shift clock t) _
      (hgeo β hβG M hM l (accelerated X shift clock t)
        (hs t ⟨ht.1, ht.2.le⟩).2.1 (hs t ⟨ht.1, ht.2.le⟩).2.2).2 D hD hDl hDr
  have hclock := (hscalar β hβS M hM model l X hX shift hshift clock hc
    i j hi hj a b ha hab hs hu hnc).2.1
  have hclock' : clock b - clock a ≤ 2 * H * Real.log β *
      Real.exp (β * (upperBarrier C l + 2 * treeMargin hN C)) := by
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlen (by norm_num : (0 : ℝ) ≤ 2))
        (Real.log_pos hβ1).le) (Real.exp_pos (β * (upperBarrier C l + 2 * treeMargin hN C))).le
    exact hclock.trans hh
  have herror : (2 * n) * (clock b - clock a) *
      Real.exp (-β * (upperBarrier C l + 7 * treeMargin hN C)) <
      Real.cos (enlargementScale β) - Real.cos (2 * enlargementScale β) := by
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hclock' (show (0 : ℝ) ≤ 2 * n by positivity))
      (Real.exp_pos (-β * (upperBarrier C l + 7 * treeMargin hN C))).le
    have heq : (2 * n) * (2 * H * Real.log β * Real.exp (β * (upperBarrier C l + 2 * treeMargin hN C))) *
        Real.exp (-β * (upperBarrier C l + 7 * treeMargin hN C)) =
        4 * n * H * Real.log β * Real.exp (-(5 * treeMargin hN C) * β) := by
      rw [show (2 * n) * (2 * H * Real.log β * Real.exp (β * (upperBarrier C l + 2 * treeMargin hN C))) *
        Real.exp (-β * (upperBarrier C l + 7 * treeMargin hN C)) =
        (4 * n * H * Real.log β) * (Real.exp (β * (upperBarrier C l + 2 * treeMargin hN C)) *
        Real.exp (-β * (upperBarrier C l + 7 * treeMargin hN C))) by ring, ← Real.exp_add]
      congr 2
      ring
    rw [heq] at hh
    exact hh.trans_lt (herr.trans_le (PreparationScale.cosine_margin hγ.le hγ1))
  have hconf := TerminalCenterMotion.cap_no_exit model β (zero_lt_one.trans hβ1).le X hX
    shift hshift clock hc D hne z₀ a b (enlargementScale β) (2 * enlargementScale β)
    (upperBarrier C l + 7 * treeMargin hN C) ha hab hγ.le (by linarith only [hγ]) hπ hz₀ hext herror
  refine ⟨BlockGeometry.blockMean_ne_zero_of_diameter D hne (accelerated X shift clock a) hδπ hd,
    z₀, rfl, ?_⟩
  intro t ht
  refine ⟨hconf t ht, ?_, PreparationGeometry.exists_mean_near_center D hne
    (accelerated X shift clock t) z₀ (2 * enlargementScale β) (by positivity) hπ
      (fun p hp => (hconf t ht p hp).le)⟩
  intro p hp
  have hh := AngularGeometry.angularDist_triangle (accelerated X shift clock t p) z₀
    (accelerated X shift clock a p)
  rw [AngularGeometry.angularDist_comm z₀ (accelerated X shift clock a p)] at hh
  linarith only [hh, hconf t ht p hp, hconf a ⟨le_rfl, hab⟩ p hp]

end Metastability.InactiveCenterMotion
