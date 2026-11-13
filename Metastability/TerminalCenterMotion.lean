import Metastability.ActiveCenterMotion

/-! Terminal motion from a single fixed small cap about the entry
representative. The source ODE and clock supply every drift estimate. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace
namespace Metastability.TerminalCenterMotion
open Source ActiveScales CapEnlargement ActiveSourceLaw
variable {n N d : ℕ}

/-- Transfer a genuine original-time no-exit argument through the actual clock. -/
theorem cap_no_exit (model : Model) (β : ℝ) (hβ : 0 ≤ β)
    (X : ℝ → Configuration n d) (hX : Solves model β X)
    (shift : ℝ) (hshift : 0 ≤ shift) (clock : ℝ → ℝ) (hc : ClockRelation β X shift clock)
    (D : Block n) (hD : D.Nonempty) (w : Sphere d) (a b r R L : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hr : 0 ≤ r) (hrR : r < R) (hR : R < Real.pi / 2)
    (hstart : ∀ p ∈ D, angularDist (accelerated X shift clock a p) w ≤ r)
    (hsep : ∀ t ∈ Ico a b, ∀ p ∈ D, ∀ q ∉ D,
      L ≤ 1 - ⟪(accelerated X shift clock t p).val, (accelerated X shift clock t q).val⟫)
    (herror : (2 * n) * (clock b - clock a) * Real.exp (-β * L) < Real.cos r - Real.cos R) :
    ∀ t ∈ Icc a b, ∀ p ∈ D, angularDist (accelerated X shift clock t p) w < R := by
  have hτa : 0 ≤ shift + clock a := add_nonneg hshift (hc.1.2.1 a ha)
  have hτab : shift + clock a ≤ shift + clock b :=
    add_le_add le_rfl (hc.2.1.monotoneOn ha (ha.trans hab) hab)
  have hh := PostMergeCaps.variable_caps_no_exit model β hβ X hX (fun _ : Unit => D)
    (fun _ => hD) (fun _ => w) (fun _ => r) (fun _ => R)
    (shift + clock a) (shift + clock b) L hτa hτab (fun _ => hr) (fun _ => hrR)
    (fun _ => hR) (fun _ => hstart) (by
      intro u hu _ _ p hp q hq
      obtain ⟨t, ht, rfl⟩ := PlateauClockTransfer.exists_time_Ico hc ha hab hu
      exact hsep t ht p hp q hq) (by
      intro _
      simpa only [show shift + clock b - (shift + clock a) = clock b - clock a by ring] using herror)
  intro t ht p hp
  exact hh _ (PlateauClockTransfer.shifted_clock_mem_Icc hc ha ht) () p hp

/-- Exponential exterior drift is smaller than the squared mesoscopic radius. -/
theorem eventually_terminal_error (H δ : ℝ) (hH : 0 ≤ H) (hδ : 0 < δ) :
    ∀ᶠ β : ℝ in atTop, 1 < β ∧ 1 ≤ Real.log β ∧
      4 * mesoscopicScale β < Real.pi / 2 ∧ 2 * mesoscopicScale β ≤ 1 ∧
      4 * n * H * Real.log β * Real.exp (-(5 * δ) * β) < 2 * mesoscopicScale β ^ 2 := by
  have hsmall : 0 < min (Real.pi / 8) (1 / 2 : ℝ) := lt_min (by positivity) (by norm_num)
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    tendsto_mesoscopicScale.eventually (gt_mem_nhds hsmall),
    eventually_mul_exp_le_rpow (4 * n * H) (5 * δ) 2 (-1) (by positivity)] with β hβ hlog hm he
  have hβ0 := zero_lt_one.trans hβ
  have hml := lt_of_lt_of_le hm (min_le_left _ _)
  have hmr := lt_of_lt_of_le hm (min_le_right _ _)
  refine ⟨hβ, hlog, by linarith only [hml], by linarith only [hmr], ?_⟩
  rw [Real.rpow_two, Real.rpow_neg_one] at he
  have hlogβ : Real.log β ≤ β ^ 2 := (Real.log_le_self hβ0.le).trans (by nlinarith only [hβ.le])
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hlogβ (show 0 ≤ 4 * (n : ℝ) * H by positivity))
    (Real.exp_pos (-(5 * δ) * β)).le
  have hsq : β⁻¹ ≤ mesoscopicScale β ^ 2 := by
    rw [mesoscopicScale_sq hβ]
    have hh' := div_le_div_of_nonneg_right hlog hβ0.le
    simpa only [one_div] using hh'
  have hp := sq_pos_of_pos (mesoscopicScale_pos hβ)
  linarith only [hh, he, hsq, hp]

/-- Terminal particles and all nonempty subset means stay in a radius-four
mesoscopic cap about the initial active representative. The right endpoint may
be the first completed parent, and no post-completion clock estimate is used. -/
theorem terminal_confinement (T : CollisionTree n N) (hN : 0 < N)
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
      angularDist (accelerated X shift clock a i) (accelerated X shift clock a j) ≤ mesoscopicScale β →
      ∀ t ∈ Icc a b,
        (∀ p ∈ T.parent l, angularDist (accelerated X shift clock t p)
          (accelerated X shift clock a i) < 4 * mesoscopicScale β) ∧
        (∀ (D : Block n) (hD : D.Nonempty), D ⊆ T.parent l →
          BlockGeometry.blockMean D hD (accelerated X shift clock t) ≠ 0 ∧ ∃ z : Sphere d,
            z.val = ‖BlockGeometry.blockMean D hD (accelerated X shift clock t)‖⁻¹ •
              BlockGeometry.blockMean D hD (accelerated X shift clock t) ∧
            angularDist z (accelerated X shift clock a i) ≤ 4 * mesoscopicScale β) := by
  obtain ⟨S, hS, hscalar⟩ := CompletionScalar.interval_bounds T hN C hC κ hκ
  obtain ⟨G, hG, hgeo⟩ := ActiveGeometry.stage_barriers T hN C hC
  obtain ⟨E, hE⟩ := eventually_atTop.mp (eventually_terminal_error (n := n) H
    (treeMargin hN C) hH.le (treeMargin_pos hN C hC))
  obtain ⟨Q, hQ⟩ := eventually_atTop.mp (eventually_clock_parameters κ
    (treeMargin hN C) (by linarith only [hκ]) (treeMargin_pos hN C hC))
  refine ⟨max (max S G) (max E Q), hS.trans_le ((le_max_left S G).trans (le_max_left _ _)), ?_⟩
  intro β hβ M hM model l X hX shift hshift clock hc i j hi hj a b ha hab hlen hs hu hnc hstart
  have hβS := (le_max_left S G).trans ((le_max_left _ _).trans hβ)
  have hβG := (le_max_right S G).trans ((le_max_left _ _).trans hβ)
  have hβE := (le_max_left E Q).trans ((le_max_right _ _).trans hβ)
  have hβQ := (le_max_right E Q).trans ((le_max_right _ _).trans hβ)
  obtain ⟨hβ1, _, hπ, hm1, herr⟩ := hE β hβE
  have hm := mesoscopicScale_pos hβ1
  have hδmeso : Real.exp (-κ * β) ≤ mesoscopicScale β := by
    obtain ⟨_, _, hδ, _, _, _, hcut⟩ := hQ β hβQ
    linarith only [hδ, hcut, Real.exp_pos (-κ * β)]
  have hentry : ∀ p ∈ T.parent l,
      angularDist (accelerated X shift clock a p) (accelerated X shift clock a i) ≤ 2 * mesoscopicScale β := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact ((hs a ⟨le_rfl, hab⟩).1 _ (T.left_mem l) p hp i hi).trans
        (by linarith only [hδmeso, hm.le])
    · have hd := (hs a ⟨le_rfl, hab⟩).1 _ (T.right_mem l) p hp j hj
      have ht := AngularGeometry.angularDist_triangle (accelerated X shift clock a p)
        (accelerated X shift clock a j) (accelerated X shift clock a i)
      rw [AngularGeometry.angularDist_comm (accelerated X shift clock a j) (accelerated X shift clock a i)] at ht
      linarith only [hd, ht, hδmeso, hstart]
  have hext : ∀ t ∈ Ico a b, ∀ p ∈ T.parent l, ∀ q ∉ T.parent l,
      upperBarrier C l + 7 * treeMargin hN C ≤
        1 - ⟪(accelerated X shift clock t p).val, (accelerated X shift clock t q).val⟫ := by
    intro t ht
    exact (hgeo β hβG M hM l (accelerated X shift clock t)
      (hs t ⟨ht.1, ht.2.le⟩).2.1 (hs t ⟨ht.1, ht.2.le⟩).2.2).1
  have hclock := (hscalar β hβS M hM model l X hX shift hshift clock hc
    i j hi hj a b ha hab hs hu hnc).2.1
  have hclock' : clock b - clock a ≤ 2 * H * Real.log β *
      Real.exp (β * (upperBarrier C l + 2 * treeMargin hN C)) := by
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlen (by norm_num : (0 : ℝ) ≤ 2))
        (Real.log_pos hβ1).le) (Real.exp_pos (β * (upperBarrier C l + 2 * treeMargin hN C))).le
    exact hclock.trans hh
  have hgap := PreparationScale.cosine_margin (show 0 ≤ 2 * mesoscopicScale β by positivity) hm1
  have herror : (2 * n) * (clock b - clock a) *
      Real.exp (-β * (upperBarrier C l + 7 * treeMargin hN C)) <
      Real.cos (2 * mesoscopicScale β) - Real.cos (4 * mesoscopicScale β) := by
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
    rw [show 2 * (2 * mesoscopicScale β) = 4 * mesoscopicScale β by ring] at hgap
    nlinarith only [hh, herr, hgap]
  have hparent : (T.parent l).Nonempty :=
    (T.block_nonempty _ _ (T.left_mem l)).mono Finset.subset_union_left
  have hconf := cap_no_exit model β (zero_lt_one.trans hβ1).le X hX shift hshift clock hc
    (T.parent l) hparent (accelerated X shift clock a i) a b (2 * mesoscopicScale β)
    (4 * mesoscopicScale β) (upperBarrier C l + 7 * treeMargin hN C)
    ha hab (by positivity) (by linarith only [hm]) hπ hentry hext herror
  intro t ht
  refine ⟨hconf t ht, ?_⟩
  intro D hD hsub
  exact PreparationGeometry.exists_mean_near_center D hD (accelerated X shift clock t)
    (accelerated X shift clock a i) (4 * mesoscopicScale β) (by positivity) hπ
    (fun p hp => (hconf t ht p (hsub hp)).le)

end Metastability.TerminalCenterMotion
