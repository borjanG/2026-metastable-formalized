import Metastability.ActiveGeometry
import Metastability.ActiveScales

/-!
# Active cross pairs in the literal cutoff clock

This module works with the exact eligible-pair finite minimum. In the terminal
regime it requires only one eligible active pair, obtained from noncompletion
of the parent, and does not assert that all active pairs remain eligible.
-/

noncomputable section
open Filter Set
open scoped Topology RealInnerProductSpace

namespace Metastability.ActiveClock

open Source ActiveGeometry CapEnlargement ActiveScales
variable {n N d : ℕ}

theorem mem_eligiblePairs (β : ℝ) (x : Configuration n d) (i j : Fin n) :
    (i, j) ∈ eligiblePairs β x ↔ i ≠ j ∧ clockCutoff β < angularDist (x i) (x j) := by
  simp only [eligiblePairs, Finset.mem_filter, Finset.mem_univ, true_and]

theorem activeCross_ne (T : CollisionTree n N) (l : Fin N) (i j : Fin n)
    (hcross : IsActiveCross T l i j) : i ≠ j := by
  intro heq
  subst j
  rcases hcross with ⟨hi, hj⟩ | ⟨hj, hi⟩
  · exact Finset.disjoint_left.mp (TreeDynamics.children_disjoint T l) hi hj
  · exact Finset.disjoint_left.mp (TreeDynamics.children_disjoint T l) hi hj

theorem blockOf_ne_of_eligible (T : CollisionTree n N) (l : Fin N)
    (β ε : ℝ) (x : Configuration n d)
    (htight : ∀ D ∈ T.partition l.castSucc, ∀ i ∈ D, ∀ j ∈ D,
      angularDist (x i) (x j) ≤ ε) (hε : ε ≤ clockCutoff β)
    (i j : Fin n) (hp : (i, j) ∈ eligiblePairs β x) :
    T.blockOf l.castSucc i ≠ T.blockOf l.castSucc j := by
  intro heq
  have hj : j ∈ T.blockOf l.castSucc i := by rw [heq]; exact (T.blockOf_spec l.castSucc j).2
  have h := htight _ (T.blockOf_spec l.castSucc i).1 i (T.blockOf_spec l.castSucc i).2 j hj
  exact (not_le.mpr ((mem_eligiblePairs β x i j).mp hp).2) (h.trans hε)

theorem activeCross_angle_error (T : CollisionTree n N) (l : Fin N)
    (ε : ℝ) (x : Configuration n d)
    (htight : ∀ D ∈ T.partition l.castSucc, ∀ p ∈ D, ∀ q ∈ D,
      angularDist (x p) (x q) ≤ ε)
    (i j : Fin n) (hi : i ∈ T.left l) (hj : j ∈ T.right l)
    (p q : Fin n) (hpq : IsActiveCross T l p q) :
    |angularDist (x p) (x q) - angularDist (x i) (x j)| ≤ 2 * ε := by
  rcases hpq with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · exact (abs_angularDist_sub_le (x p) (x q) (x i) (x j)).trans
      (add_le_add (htight _ (T.left_mem l) p hp i hi) (htight _ (T.right_mem l) q hq j hj) |>.trans_eq (by ring))
  · rw [AngularGeometry.angularDist_comm (x p) (x q)]
    exact (abs_angularDist_sub_le (x q) (x p) (x i) (x j)).trans
      (add_le_add (htight _ (T.left_mem l) q hq i hi) (htight _ (T.right_mem l) p hp j hj) |>.trans_eq (by ring))

theorem activeCross_deficit_error (T : CollisionTree n N) (l : Fin N)
    (ε : ℝ) (x : Configuration n d)
    (htight : ∀ D ∈ T.partition l.castSucc, ∀ p ∈ D, ∀ q ∈ D,
      angularDist (x p) (x q) ≤ ε)
    (i j : Fin n) (hi : i ∈ T.left l) (hj : j ∈ T.right l)
    (p q : Fin n) (hpq : IsActiveCross T l p q) :
    |(1 - ⟪(x p).val, (x q).val⟫) - (1 - ⟪(x i).val, (x j).val⟫)| ≤ 2 * ε := by
  rcases hpq with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · exact (abs_inner_deficit_sub_le (x p) (x q) (x i) (x j)).trans
      (add_le_add (htight _ (T.left_mem l) p hp i hi) (htight _ (T.right_mem l) q hq j hj) |>.trans_eq (by ring))
  · rw [real_inner_comm (x q).val (x p).val]
    exact (abs_inner_deficit_sub_le (x q) (x p) (x i) (x j)).trans
      (add_le_add (htight _ (T.left_mem l) q hq i hi) (htight _ (T.right_mem l) p hp j hj) |>.trans_eq (by ring))

theorem eligible_active_of_parent_not_complete (T : CollisionTree n N) (l : Fin N)
    (β ε : ℝ) (x : Configuration n d)
    (htight : ∀ D ∈ T.partition l.castSucc, ∀ p ∈ D, ∀ q ∈ D,
      angularDist (x p) (x q) ≤ ε) (hε : ε ≤ clockCutoff β)
    (hparent : ¬ ∀ p ∈ T.parent l, ∀ q ∈ T.parent l,
      angularDist (x p) (x q) ≤ clockCutoff β) :
    ∃ p q, IsActiveCross T l p q ∧ (p, q) ∈ eligiblePairs β x := by
  classical
  push Not at hparent
  obtain ⟨p, hp, q, hq, hangle⟩ := hparent
  have hne : T.blockOf l.castSucc p ≠ T.blockOf l.castSucc q := by
    intro heq
    have hq' : q ∈ T.blockOf l.castSucc p := by rw [heq]; exact (T.blockOf_spec l.castSucc q).2
    exact (not_le.mpr hangle) ((htight _ (T.blockOf_spec l.castSucc p).1
      p (T.blockOf_spec l.castSucc p).2 q hq').trans hε)
  have hcross := activeCross_of_mem_parent_of_blocks_ne T l p q hp hq hne
  exact ⟨p, q, hcross, (mem_eligiblePairs β x p q).mpr ⟨activeCross_ne T l p q hcross, hangle⟩⟩

/-- Static minimum selection. The active/nonactive barrier premises are
discharged from the source cap hypotheses in the final source-facing exports. -/
theorem exists_active_minimizer (T : CollisionTree n N) (l : Fin N)
    (β ε U L : ℝ) (hβ : 0 < β) (x : Configuration n d)
    (htight : ∀ D ∈ T.partition l.castSucc, ∀ p ∈ D, ∀ q ∈ D,
      angularDist (x p) (x q) ≤ ε) (hε : ε ≤ clockCutoff β)
    (i j : Fin n) (hi : i ∈ T.left l) (hj : j ∈ T.right l)
    (hupper : 1 - ⟪(x i).val, (x j).val⟫ ≤ U) (hgap : U + 2 * ε < L)
    (hbarrier : ∀ p q, T.blockOf l.castSucc p ≠ T.blockOf l.castSucc q →
      ¬ IsActiveCross T l p q → L ≤ 1 - ⟪(x p).val, (x q).val⟫)
    (hex : ∃ p q, IsActiveCross T l p q ∧ (p, q) ∈ eligiblePairs β x) :
    ∃ p q, IsActiveCross T l p q ∧ (p, q) ∈ eligiblePairs β x ∧
      clockFactor β x = Real.log β * Real.exp (β * (1 - ⟪(x p).val, (x q).val⟫)) := by
  classical
  obtain ⟨a, b, habcross, hab⟩ := hex
  have hne : (eligiblePairs β x).Nonempty := ⟨(a, b), hab⟩
  let S := (eligiblePairs β x).image fun p => Real.exp (β * (1 - ⟪(x p.1).val, (x p.2).val⟫))
  have hS : S.Nonempty := Finset.Nonempty.image hne _
  obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp (Finset.min'_mem S hS)
  have hmin : Real.exp (β * (1 - ⟪(x p.1).val, (x p.2).val⟫)) ≤
      Real.exp (β * (1 - ⟪(x a).val, (x b).val⟫)) := by
    rw [heq]
    exact Finset.min'_le S _ (Finset.mem_image.mpr ⟨(a, b), hab, rfl⟩)
  have hcross : IsActiveCross T l p.1 p.2 := by
    by_contra hnot
    have hlow := hbarrier p.1 p.2
      (blockOf_ne_of_eligible T l β ε x htight hε p.1 p.2 hp) hnot
    have hnear := (abs_le.mp (activeCross_deficit_error T l ε x htight i j hi hj a b habcross)).2
    have hexp := (Real.exp_le_exp.mp hmin)
    have hdef := (mul_le_mul_iff_right₀ hβ).mp hexp
    linarith only [hlow, hnear, hupper, hgap, hdef]
  refine ⟨p.1, p.2, hcross, hp, ?_⟩
  unfold clockFactor
  rw [dif_pos hne]
  change Real.log β * S.min' hS = _
  rw [← heq]

theorem clock_ratio_error (T : CollisionTree n N) (l : Fin N)
    (β ε U L : ℝ) (hβ : 1 < β) (x : Configuration n d)
    (htight : ∀ D ∈ T.partition l.castSucc, ∀ p ∈ D, ∀ q ∈ D,
      angularDist (x p) (x q) ≤ ε) (hε : ε ≤ clockCutoff β)
    (i j : Fin n) (hi : i ∈ T.left l) (hj : j ∈ T.right l)
    (hupper : 1 - ⟪(x i).val, (x j).val⟫ ≤ U) (hgap : U + 2 * ε < L)
    (hbarrier : ∀ p q, T.blockOf l.castSucc p ≠ T.blockOf l.castSucc q →
      ¬ IsActiveCross T l p q → L ≤ 1 - ⟪(x p).val, (x q).val⟫)
    (hex : ∃ p q, IsActiveCross T l p q ∧ (p, q) ∈ eligiblePairs β x)
    (hsmall : 2 * β * ε ≤ 1) :
    |clockFactor β x / (Real.log β * Real.exp (β * (1 - ⟪(x i).val, (x j).val⟫))) - 1| ≤
      4 * β * ε := by
  have hβ0 : 0 < β := zero_lt_one.trans hβ
  obtain ⟨p, q, hpq, _, hclock⟩ :=
    exists_active_minimizer T l β ε U L hβ0 x htight hε i j hi hj hupper hgap hbarrier hex
  have hnear := activeCross_deficit_error T l ε x htight i j hi hj p q hpq
  have hscaled : |β * ((1 - ⟪(x p).val, (x q).val⟫) -
      (1 - ⟪(x i).val, (x j).val⟫))| ≤ 2 * β * ε := by
    rw [abs_mul, abs_of_pos hβ0]
    nlinarith only [mul_le_mul_of_nonneg_left hnear hβ0.le]
  rw [hclock, mul_div_mul_left _ _ (Real.log_pos hβ).ne', ← Real.exp_sub]
  have he := Real.abs_exp_sub_one_le (hscaled.trans hsmall)
  rw [mul_sub] at he hscaled
  exact he.trans (by nlinarith only [hscaled])

/-- Source cap geometry and exponential block tightness identify the actual
clock whenever the active parent has not yet completed. All thresholds are
chosen before the configuration, stage, or representatives. -/
theorem source_clock_of_noncomplete (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) (κ : ℝ) (hκ : 0 < κ) :
    ∃ β₀ : ℝ, 1 < β₀ ∧ ∀ β ≥ β₀, ∀ M ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 5),
      ∀ (l : Fin N) (x : Configuration n d),
        (∀ D ∈ T.partition l.castSucc, ∀ p ∈ D, ∀ q ∈ D,
          angularDist (x p) (x q) ≤ Real.exp (-κ * β)) →
        (∀ (D : Block n) (hD : D ∈ T.partition l.castSucc),
          D ≠ T.left l → D ≠ T.right l → ∀ p ∈ D,
          angularDist (x p) (C (T.currentNode l D hD)).center ≤
            (C (T.currentNode l D hD)).radius + M * enlargementScale β) →
        (∀ hp : T.parent l ≠ Finset.univ, ∀ p ∈ T.parent l,
          angularDist (x p) (C (T.parentNode l hp)).center ≤
            (C (T.parentNode l hp)).radius + M * enlargementScale β) →
        ∀ (i j : Fin n), i ∈ T.left l → j ∈ T.right l →
          1 - ⟪(x i).val, (x j).val⟫ ≤ upperBarrier C l + 2 * treeMargin hN C →
          (¬ ∀ p ∈ T.parent l, ∀ q ∈ T.parent l,
            angularDist (x p) (x q) ≤ clockCutoff β) →
          (∃ p q, IsActiveCross T l p q ∧ (p, q) ∈ eligiblePairs β x ∧
            clockFactor β x = Real.log β * Real.exp (β * (1 - ⟪(x p).val, (x q).val⟫))) ∧
          |clockFactor β x / (Real.log β * Real.exp (β * (1 - ⟪(x i).val, (x j).val⟫))) - 1| ≤
            β ^ (-(1 / 3 : ℝ)) := by
  obtain ⟨B, hB, hgeometry⟩ := stage_barriers T hN C hC
  obtain ⟨S, hS⟩ := eventually_atTop.mp
    (eventually_clock_parameters κ (treeMargin hN C) hκ (treeMargin_pos hN C hC))
  refine ⟨max B S, hB.trans_le (le_max_left _ _), ?_⟩
  intro β hβ M hM l x htight hother hparent i j hi hj hupper hnoncomplete
  obtain ⟨hβ1, _, hε, hgap, hsmall, herr, _⟩ := hS β ((le_max_right _ _).trans hβ)
  have hbarrier := (hgeometry β ((le_max_left _ _).trans hβ) M hM l x hother hparent).2
  have hgap' : (upperBarrier C l + 2 * treeMargin hN C) + 2 * Real.exp (-κ * β) <
      upperBarrier C l + 7 * treeMargin hN C := by linarith only [hgap]
  have hex := eligible_active_of_parent_not_complete T l β (Real.exp (-κ * β)) x htight hε hnoncomplete
  refine ⟨exists_active_minimizer T l β (Real.exp (-κ * β))
    (upperBarrier C l + 2 * treeMargin hN C) (upperBarrier C l + 7 * treeMargin hN C)
    (zero_lt_one.trans hβ1) x htight hε i j hi hj hupper hgap' hbarrier hex, ?_⟩
  exact (clock_ratio_error T l β (Real.exp (-κ * β))
    (upperBarrier C l + 2 * treeMargin hN C) (upperBarrier C l + 7 * treeMargin hN C)
    hβ1 x htight hε i j hi hj hupper hgap' hbarrier hex hsmall).trans herr

/-- Above the mesoscopic angle every active cross pair is eligible, and the
literal source clock has the quantitative relative error beta^(-1/3). -/
theorem active_clock (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) (κ : ℝ) (hκ : 0 < κ) :
    ∃ β₀ : ℝ, 1 < β₀ ∧ ∀ β ≥ β₀, ∀ M ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 5),
      ∀ (l : Fin N) (x : Configuration n d),
        (∀ D ∈ T.partition l.castSucc, ∀ p ∈ D, ∀ q ∈ D,
          angularDist (x p) (x q) ≤ Real.exp (-κ * β)) →
        (∀ (D : Block n) (hD : D ∈ T.partition l.castSucc),
          D ≠ T.left l → D ≠ T.right l → ∀ p ∈ D,
          angularDist (x p) (C (T.currentNode l D hD)).center ≤
            (C (T.currentNode l D hD)).radius + M * enlargementScale β) →
        (∀ hp : T.parent l ≠ Finset.univ, ∀ p ∈ T.parent l,
          angularDist (x p) (C (T.parentNode l hp)).center ≤
            (C (T.parentNode l hp)).radius + M * enlargementScale β) →
        ∀ (i j : Fin n), i ∈ T.left l → j ∈ T.right l →
          1 - ⟪(x i).val, (x j).val⟫ ≤ upperBarrier C l + 2 * treeMargin hN C →
          mesoscopicScale β ≤ angularDist (x i) (x j) →
          (∀ p q, IsActiveCross T l p q → (p, q) ∈ eligiblePairs β x) ∧
          (∃ p q, IsActiveCross T l p q ∧ (p, q) ∈ eligiblePairs β x ∧
            clockFactor β x = Real.log β * Real.exp (β * (1 - ⟪(x p).val, (x q).val⟫))) ∧
          |clockFactor β x / (Real.log β * Real.exp (β * (1 - ⟪(x i).val, (x j).val⟫))) - 1| ≤
            β ^ (-(1 / 3 : ℝ)) := by
  obtain ⟨B, hB, hclock⟩ := source_clock_of_noncomplete T hN C hC κ hκ
  obtain ⟨S, hS⟩ := eventually_atTop.mp
    (eventually_clock_parameters κ (treeMargin hN C) hκ (treeMargin_pos hN C hC))
  refine ⟨max B S, hB.trans_le (le_max_left _ _), ?_⟩
  intro β hβ M hM l x htight hother hparent i j hi hj hupper hmeso
  obtain ⟨_, _, _, _, _, _, hangle⟩ := hS β ((le_max_right _ _).trans hβ)
  have hall : ∀ p q, IsActiveCross T l p q → (p, q) ∈ eligiblePairs β x := by
    intro p q hpq
    apply (mem_eligiblePairs β x p q).mpr
    refine ⟨activeCross_ne T l p q hpq, ?_⟩
    have hnear := (abs_le.mp (activeCross_angle_error T l (Real.exp (-κ * β))
      x htight i j hi hj p q hpq)).1
    linarith only [hnear, hangle, hmeso]
  have hnoncomplete : ¬ ∀ p ∈ T.parent l, ∀ q ∈ T.parent l,
      angularDist (x p) (x q) ≤ clockCutoff β := by
    intro hc
    exact (not_le.mpr ((mem_eligiblePairs β x i j).mp (hall i j (Or.inl ⟨hi, hj⟩))).2)
      (hc i (Finset.mem_union_left _ hi) j (Finset.mem_union_right _ hj))
  exact ⟨hall, hclock β ((le_max_left _ _).trans hβ) M hM l x
    htight hother hparent i j hi hj hupper hnoncomplete⟩

/-- In the terminal range the representative need not itself be eligible.
Noncompletion of the parent supplies an eligible active cross pair; the
mesoscopic upper bound supplies the active barrier upper bound automatically. -/
theorem terminal_clock (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) (κ : ℝ) (hκ : 0 < κ) :
    ∃ β₀ : ℝ, 1 < β₀ ∧ ∀ β ≥ β₀, ∀ M ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 5),
      ∀ (l : Fin N) (x : Configuration n d),
        (∀ D ∈ T.partition l.castSucc, ∀ p ∈ D, ∀ q ∈ D,
          angularDist (x p) (x q) ≤ Real.exp (-κ * β)) →
        (∀ (D : Block n) (hD : D ∈ T.partition l.castSucc),
          D ≠ T.left l → D ≠ T.right l → ∀ p ∈ D,
          angularDist (x p) (C (T.currentNode l D hD)).center ≤
            (C (T.currentNode l D hD)).radius + M * enlargementScale β) →
        (∀ hp : T.parent l ≠ Finset.univ, ∀ p ∈ T.parent l,
          angularDist (x p) (C (T.parentNode l hp)).center ≤
            (C (T.parentNode l hp)).radius + M * enlargementScale β) →
        ∀ (i j : Fin n), i ∈ T.left l → j ∈ T.right l →
          angularDist (x i) (x j) ≤ mesoscopicScale β →
          (¬ ∀ p ∈ T.parent l, ∀ q ∈ T.parent l,
            angularDist (x p) (x q) ≤ clockCutoff β) →
          (∃ p q, IsActiveCross T l p q ∧ (p, q) ∈ eligiblePairs β x ∧
            clockFactor β x = Real.log β * Real.exp (β * (1 - ⟪(x p).val, (x q).val⟫))) ∧
          |clockFactor β x / (Real.log β * Real.exp (β * (1 - ⟪(x i).val, (x j).val⟫))) - 1| ≤
            β ^ (-(1 / 3 : ℝ)) := by
  obtain ⟨B, hB, hclock⟩ := source_clock_of_noncomplete T hN C hC κ hκ
  have hδ := treeMargin_pos hN C hC
  have hlim : Tendsto (fun β => mesoscopicScale β ^ 2 / 2) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : 2 ≠ 0), zero_div] using
      (tendsto_mesoscopicScale.pow 2).div_const (2 : ℝ)
  obtain ⟨S, hS⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hδ))
  refine ⟨max B S, hB.trans_le (le_max_left _ _), ?_⟩
  intro β hβ M hM l x htight hother hparent i j hi hj hmeso hnoncomplete
  have hsmall := hS β ((le_max_right _ _).trans hβ)
  have hq := ContractionScale.deficit_le_half_sq_of_angularDist_le x i j (mesoscopicScale β) hmeso
  have hu : 0 < upperBarrier C l :=
    (TreeSeparation.lowerBarrier_pos T C hC l).trans_le (hC.2 l).2.2.2.2.1
  have hupper : 1 - ⟪(x i).val, (x j).val⟫ ≤ upperBarrier C l + 2 * treeMargin hN C := by
    change 1 - ⟪(x i).val, (x j).val⟫ ≤ mesoscopicScale β ^ 2 / 2 at hq
    linarith only [hq, hsmall, hu, hδ]
  exact hclock β ((le_max_left _ _).trans hβ) M hM l x
    htight hother hparent i j hi hj hupper hnoncomplete

end Metastability.ActiveClock
