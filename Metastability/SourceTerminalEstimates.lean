import Metastability.ActiveTerminalBand
import Metastability.ActiveClock
import Metastability.ActiveTrajectory

/-! Pointwise terminal estimates from literal source stage geometry. -/
noncomputable section
open Filter Set
open scoped Topology RealInnerProductSpace
namespace Metastability.SourceTerminalEstimates
open Source ActiveCoefficients ActiveVelocity ActiveScales CapEnlargement
variable {n N d : ℕ}

theorem clock_cancellation_lower (β : ℝ) (hβ : 1 < β)
    (x : Configuration n d) (i j : Fin n) (v : ℝ)
    (hv : sineSquare x i j * kernel β x i j / (2 * n) ≤ v)
    (hc : |clockFactor β x / (Real.log β * Real.exp (β * (1 - ⟪(x i).val, (x j).val⟫))) - 1| ≤ 1 / 2) :
    Real.log β / (4 * n) * sineSquare x i j ≤ v * clockFactor β x := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt i.isLt
  have hs := sineSquare_nonneg x i j
  have hK : 0 ≤ kernel β x i j := (Real.exp_pos _).le
  have hden : 0 < Real.log β * Real.exp (β * (1 - ⟪(x i).val, (x j).val⟫)) :=
    mul_pos (Real.log_pos hβ) (Real.exp_pos _)
  have hlo : (1 / 2 : ℝ) ≤ clockFactor β x /
      (Real.log β * Real.exp (β * (1 - ⟪(x i).val, (x j).val⟫))) := by
    linarith only [(abs_le.mp hc).1]
  have hcl := (le_div_iff₀ hden).mp hlo
  have hmul := mul_le_mul hv hcl (by positivity : (0 : ℝ) ≤
      (1 / 2) * (Real.log β * Real.exp (β * (1 - ⟪(x i).val, (x j).val⟫))))
    (le_trans (by positivity : (0 : ℝ) ≤ sineSquare x i j * kernel β x i j / (2 * n)) hv)
  have hexp : kernel β x i j * Real.exp (β * (1 - ⟪(x i).val, (x j).val⟫)) = 1 := by
    rw [kernel, ← Real.exp_add]
    rw [show β * (⟪(x i).val, (x j).val⟫ - 1) + β * (1 - ⟪(x i).val, (x j).val⟫) = 0 by ring, Real.exp_zero]
  have heq : (sineSquare x i j * kernel β x i j / (2 * n)) *
      ((1 / 2) * (Real.log β * Real.exp (β * (1 - ⟪(x i).val, (x j).val⟫)))) =
      Real.log β / (4 * n) * sineSquare x i j := by
    calc
      _ = (Real.log β / (4 * n) * sineSquare x i j) *
        (kernel β x i j * Real.exp (β * (1 - ⟪(x i).val, (x j).val⟫))) := by ring
      _ = _ := by rw [hexp, mul_one]
  rwa [heq] at hmul

/-- The enlarged terminal band has strictly positive original correlation
velocity. Inside the terminal window the actual clock gives the uniform
logarithmic lower slope. -/
theorem source_terminal_estimates (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) (κ : ℝ) (hκ : 0 < κ) :
    ∃ β₀ : ℝ, 1 < β₀ ∧ ∀ β ≥ β₀,
      2 * mesoscopicScale β ≤ 1 ∧ Real.exp (-κ * β) ≤ clockCutoff β / 4 ∧
      ∀ M ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 5), ∀ (l : Fin N) (model : Model)
      (x : Configuration n d),
      (∀ D ∈ T.partition l.castSucc, ∀ p ∈ D, ∀ q ∈ D,
        angularDist (x p) (x q) ≤ Real.exp (-κ * β)) →
      (∀ (D : Block n) (hD : D ∈ T.partition l.castSucc), D ≠ T.left l → D ≠ T.right l →
        ∀ p ∈ D, angularDist (x p) (C (T.currentNode l D hD)).center ≤
          (C (T.currentNode l D hD)).radius + M * enlargementScale β) →
      (∀ hp : T.parent l ≠ Finset.univ, ∀ p ∈ T.parent l,
        angularDist (x p) (C (T.parentNode l hp)).center ≤
          (C (T.parentNode l hp)).radius + M * enlargementScale β) →
      ∀ (i j : Fin n), i ∈ T.left l → j ∈ T.right l →
      (¬ ∀ p ∈ T.parent l, ∀ q ∈ T.parent l, angularDist (x p) (x q) ≤ clockCutoff β) →
      2 * mesoscopicScale β ≥ angularDist (x i) (x j) →
      clockCutoff β / 2 < angularDist (x i) (x j) ∧
      0 < -PairDeficit.velocity model β x i j ∧
      (angularDist (x i) (x j) ≤ mesoscopicScale β →
        Real.log β / (4 * n) * sineSquare x i j ≤
          (-PairDeficit.velocity model β x i j) * clockFactor β x) := by
  have hn := TreeDynamics.particle_pos T
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hδ := treeMargin_pos hN C hC
  obtain ⟨V, hV⟩ := eventually_atTop.mp
    (ActiveTerminalBand.eventually_terminal_comparable_doubled n hn κ (7 * treeMargin hN C)
      hκ (by positivity))
  obtain ⟨G, hG, hgeometry⟩ := ActiveGeometry.stage_barriers T hN C hC
  obtain ⟨R, hR, hclock⟩ := ActiveClock.terminal_clock T hN C hC κ hκ
  have hpow : Tendsto (fun β : ℝ => β ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)
  obtain ⟨S, hS⟩ := eventually_atTop.mp (show ∀ᶠ β : ℝ in atTop,
      2 * mesoscopicScale β ≤ 1 ∧ 16 * β * Real.exp (-κ * β) ≤ 1 ∧
        β ^ (-(1 / 3 : ℝ)) ≤ 1 / 2 by
    filter_upwards [tendsto_mesoscopicScale.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
      eventually_mul_exp_le_rpow 16 κ 1 0 hκ,
      hpow.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with β hm he hp
    simp only [Real.rpow_one, Real.rpow_zero] at he
    exact ⟨by linarith only [hm], he, hp.le⟩)
  refine ⟨max (max V G) (max R S), hG.trans_le ((le_max_right V G).trans (le_max_left _ _)), ?_⟩
  intro β hβ
  have hVβ := hV β ((le_max_left V G).trans ((le_max_left _ _).trans hβ))
  have hβ1 := hVβ.1
  have hβ0 := zero_lt_one.trans hβ1
  have hSβ := hS β ((le_max_right R S).trans ((le_max_right _ _).trans hβ))
  have hε : Real.exp (-κ * β) ≤ clockCutoff β / 4 := by
    have he : Real.exp (-κ * β) ≤ 1 / (16 * β) := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 16 * β)).mpr
      nlinarith only [hSβ.2.1]
    have hi := div_le_div_of_nonneg_right (inv_four_beta_le_clockCutoff hβ1) (by norm_num : (0 : ℝ) ≤ 4)
    have hh : (1 / (4 * β)) / 4 = 1 / (16 * β) := by ring
    rw [hh] at hi
    exact he.trans hi
  refine ⟨hSβ.1, hε, ?_⟩
  intro M hM l model x htight hother hparent i j hi hj hnoncomplete hupper
  have hε' : Real.exp (-κ * β) ≤ clockCutoff β := by
    have hc := clockCutoff_pos hβ1
    linarith only [hε, hc]
  obtain ⟨p, q, hpq, heligible⟩ := ActiveClock.eligible_active_of_parent_not_complete
    T l β (Real.exp (-κ * β)) x htight hε' hnoncomplete
  have herr := (abs_le.mp (ActiveClock.activeCross_angle_error T l (Real.exp (-κ * β))
    x htight i j hi hj p q hpq)).2
  have hlow : clockCutoff β / 2 < angularDist (x i) (x j) := by
    have hh := (ActiveClock.mem_eligiblePairs β x p q).mp heligible
    linarith only [hh.2, herr, hε]
  have hext := (hgeometry β ((le_max_right V G).trans ((le_max_left _ _).trans hβ))
    M hM l x hother hparent).1
  have hu : 0 ≤ upperBarrier C l :=
    ((TreeSeparation.lowerBarrier_pos T C hC l).trans_le (hC.2 l).2.2.2.2.1).le
  have hbi : ∀ k ∈ T.left l, angularDist (x k) (x i) ≤ Real.exp (-κ * β) :=
    fun k hk => htight _ (T.left_mem l) k hk i hi
  have hcj : ∀ k ∈ T.right l, angularDist (x k) (x j) ≤ Real.exp (-κ * β) :=
    fun k hk => htight _ (T.right_mem l) k hk j hj
  have hsepB : ∀ k ∉ T.left l, k ∉ T.right l → 7 * treeMargin hN C ≤ PairDeficit.deficit x i k := by
    intro k hkB hkC
    have hh := hext i (Finset.mem_union_left _ hi) k (by simpa only [CollisionTree.parent, Finset.mem_union, not_or] using And.intro hkB hkC)
    dsimp only [PairDeficit.deficit]
    linarith only [hh, hu]
  have hsepC : ∀ k ∉ T.right l, k ∉ T.left l → 7 * treeMargin hN C ≤ PairDeficit.deficit x j k := by
    intro k hkC hkB
    have hh := hext j (Finset.mem_union_right _ hj) k (by simpa only [CollisionTree.parent, Finset.mem_union, not_or] using And.intro hkB hkC)
    dsimp only [PairDeficit.deficit]
    linarith only [hh, hu]
  have hv := hVβ.2 d model x (T.left l) (T.right l)
    (T.block_nonempty _ _ (T.left_mem l)) (T.block_nonempty _ _ (T.right_mem l)) i j
    hbi hcj hsepB hsepC hlow.le hupper
  have hs := ActiveTerminalBand.terminal_signal_lower_doubled β hβ1 hSβ.1 x i j hlow.le hupper
  have hspos : 0 < sineSquare x i j * kernel β x i j := lt_of_lt_of_le (by positivity) hs
  refine ⟨hlow, (div_pos hspos (by positivity)).trans_le hv.1, ?_⟩
  intro hmeso
  have hcl := (hclock β ((le_max_left R S).trans ((le_max_right _ _).trans hβ)) M hM l x
    htight hother hparent i j hi hj hmeso hnoncomplete).2
  exact clock_cancellation_lower β hβ1 x i j _ hv.1 (hcl.trans hSβ.2.2)

end Metastability.SourceTerminalEstimates
