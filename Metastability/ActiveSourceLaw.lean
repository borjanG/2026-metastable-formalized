import Metastability.ActiveClock
import Metastability.ActiveVelocityScale
import Metastability.ActiveTrajectory
import Metastability.ActiveLogCoordinate

/-!
# The active scalar law from the manuscript's source hypotheses

All geometric and coefficient estimates are derived from the literal prepared
tree and source dynamics. The clock enters through its actual inverse-integral
relation and the chain rule is asserted almost everywhere.
-/

noncomputable section
open Filter Set MeasureTheory
open scoped Topology RealInnerProductSpace

namespace Metastability.ActiveSourceLaw

open Source CapEnlargement ActiveScales ActiveVelocity ActiveCoefficients
variable {n N d : ℕ}

/-- The manuscript's literal stage hypotheses H1, H2, and H3. The active-angle
range is kept separate, exactly as in the source proposition. -/
def StageHyp (T : CollisionTree n N) (C : TreeCaps T d) (β κ M : ℝ)
    (l : Fin N) (x : Configuration n d) : Prop :=
  (∀ D ∈ T.partition l.castSucc, ∀ p ∈ D, ∀ q ∈ D,
    angularDist (x p) (x q) ≤ Real.exp (-κ * β)) ∧
  (∀ (D : Block n) (hD : D ∈ T.partition l.castSucc),
    D ≠ T.left l → D ≠ T.right l → ∀ p ∈ D,
    angularDist (x p) (C (T.currentNode l D hD)).center ≤
      (C (T.currentNode l D hD)).radius + M * enlargementScale β) ∧
  (∀ hp : T.parent l ≠ Finset.univ, ∀ p ∈ T.parent l,
    angularDist (x p) (C (T.parentNode l hp)).center ≤
      (C (T.parentNode l hp)).radius + M * enlargementScale β)

theorem outsideBarrier_le_two (T : CollisionTree n N) (C : TreeCaps T d) (l : Fin N) :
    outsideBarrier C l ≤ 2 := by
  unfold outsideBarrier
  split_ifs
  · exact le_rfl
  · linarith only [Real.neg_one_le_cos
      (sInf {r | ∃ D : T.ProperNode, D.val ∈ T.partition l.castSucc ∧
        D.val ≠ T.left l ∧ D.val ≠ T.right l ∧
        r = capMinDistance (C (T.parentNode l ‹_›)) (C D)})]

theorem source_barrier_parameters (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) (κ : ℝ) (hκ : 4 < κ) (l : Fin N) :
    0 < κ ∧ upperBarrier C l + 2 * treeMargin hN C < κ ∧
      upperBarrier C l + 2 * treeMargin hN C < upperBarrier C l + 7 * treeMargin hN C ∧
      0 < upperBarrier C l + 7 * treeMargin hN C ∧
      upperBarrier C l + 2 * treeMargin hN C < 2 := by
  have hδ := treeMargin_pos hN C hC
  have hg := (treeMargin_gaps hN C l).2
  have ho := outsideBarrier_le_two T C l
  have hu := (TreeSeparation.lowerBarrier_pos T C hC l).trans_le (hC.2 l).2.2.2.2.1
  constructor
  · linarith only [hκ]
  constructor
  · linarith only [hg, ho, hδ, hκ]
  constructor
  · linarith only [hδ]
  constructor
  · linarith only [hu, hδ]
  · linarith only [hg, ho, hδ]

theorem rate_eq_stageRate (model : Model) (T : CollisionTree n N) (l : Fin N) :
    rate model (T.left l) (T.right l) = stageRate model T l := by
  cases model
  · rw [rate_usa]
    rfl
  · rw [rate_sa]
    dsimp only [stageRate]
    ring

theorem stageRate_bounds (model : Model) (T : CollisionTree n N) (l : Fin N) :
    1 / (n : ℝ) ≤ stageRate model T l ∧ stageRate model T l ≤ 2 * n := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (TreeDynamics.particle_pos T)
  have hB := T.block_nonempty _ _ (T.left_mem l)
  have hC := T.block_nonempty _ _ (T.right_mem l)
  have hdB := blockDenominator_ge_one model (T.left l) hB
  have hdC := blockDenominator_ge_one model (T.right l) hC
  have hcB : (0 : ℝ) ≤ (T.left l).card := Nat.cast_nonneg _
  have hcC : (0 : ℝ) ≤ (T.right l).card := Nat.cast_nonneg _
  have hCB : (1 : ℝ) ≤ (T.left l).card := by exact_mod_cast Finset.one_le_card.mpr hB
  have hCC : (1 : ℝ) ≤ (T.right l).card := by exact_mod_cast Finset.one_le_card.mpr hC
  have hBn : ((T.left l).card : ℝ) ≤ n := by exact_mod_cast TreeDynamics.block_card_le (T.left l)
  have hCn : ((T.right l).card : ℝ) ≤ n := by exact_mod_cast TreeDynamics.block_card_le (T.right l)
  have hdBn : blockDenominator model (T.left l) ≤ n := by
    cases model
    · exact le_rfl
    · exact hBn
  rw [← rate_eq_stageRate model T l]
  unfold rate
  constructor
  · have hfirst : 1 / (n : ℝ) ≤ (T.right l).card / blockDenominator model (T.left l) := by
      apply (div_le_div_iff₀ hn (lt_of_lt_of_le zero_lt_one hdB)).mpr
      have hm := mul_le_mul_of_nonneg_right hCC hn.le
      linarith only [hdBn, hm]
    exact hfirst.trans (le_add_of_nonneg_right (div_nonneg hcB (le_trans zero_le_one hdC)))
  · have hb := div_le_self hcC hdB
    have hc := div_le_self hcB hdC
    linarith only [hb, hc, hBn, hCn]

theorem correlation_mem_Ioo (β U : ℝ) (hβ : 1 < β) (hU : U < 2)
    (x : Configuration n d) (i j : Fin n)
    (hupper : 1 - ⟪(x i).val, (x j).val⟫ ≤ U)
    (hangle : mesoscopicScale β ≤ angularDist (x i) (x j)) :
    ⟪(x i).val, (x j).val⟫ ∈ Ioo (-1 : ℝ) 1 := by
  constructor
  · linarith only [hupper, hU]
  · have hle := (ModelBounds.inner_bounds (x i) (x j)).2
    by_contra h
    have heq : ⟪(x i).val, (x j).val⟫ = 1 := le_antisymm hle (le_of_not_gt h)
    have hz : angularDist (x i) (x j) = 0 := by
      rw [angularDist, heq, Real.arccos_one]
    rw [hz] at hangle
    exact (not_le.mpr (mesoscopicScale_pos hβ)) hangle

/-- Elementary multiplication of the original velocity error and clock error. -/
theorem accelerated_error_algebra (v r s k f L p A : ℝ)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hf : 0 ≤ f) (hL : 0 ≤ L)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hA : 0 ≤ A)
    (hv : |v - r * (s * k)| ≤ A * (s * k) * p)
    (hc : |k * f - L| ≤ L * p) :
    |v * f - r * s * L| ≤ (2 * A + r) * s * L * p := by
  have hfbound : k * f ≤ 2 * L := by
    have hh := (abs_le.mp hc).2
    have hm := mul_le_mul_of_nonneg_left hp1 hL
    linarith only [hh, hm]
  have hfirst := mul_le_mul_of_nonneg_right hv hf
  have hsecond := mul_le_mul_of_nonneg_left hc (mul_nonneg hr hs)
  have hfirst' := mul_le_mul_of_nonneg_left hfbound (mul_nonneg (mul_nonneg hA hs) hp)
  have hid : v * f - r * s * L = (v - r * (s * k)) * f + (r * s) * (k * f - L) := by ring
  rw [hid]
  have hadd := abs_add_le ((v - r * (s * k)) * f) ((r * s) * (k * f - L))
  rw [abs_mul, abs_of_nonneg hf, abs_mul, abs_of_nonneg (mul_nonneg hr hs)] at hadd
  nlinarith only [hadd, hfirst, hsecond, hfirst']

/-- The source active scalar estimates at one configuration, uniformly over
all stages and both models. The original law is stated as a relative error;
the accelerated and logarithmic errors have their explicit source scales. -/
theorem static_active_law (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) (κ : ℝ) (hκ : 4 < κ) :
    ∃ K : ℝ, 0 < K ∧ ∃ β₀ : ℝ, 1 < β₀ ∧
      ∀ β ≥ β₀, ∀ M ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 5),
        ∀ (model : Model) (l : Fin N) (x : Configuration n d),
          StageHyp T C β κ M l x → ∀ (i j : Fin n), i ∈ T.left l → j ∈ T.right l →
          1 - ⟪(x i).val, (x j).val⟫ ≤ upperBarrier C l + 2 * treeMargin hN C →
          mesoscopicScale β ≤ angularDist (x i) (x j) →
          ⟪(x i).val, (x j).val⟫ ∈ Ioo (-1 : ℝ) 1 ∧
          |(-PairDeficit.velocity model β x i j) /
            (stageRate model T l * (sineSquare x i j * kernel β x i j)) - 1| ≤
              K * β ^ (-(1 / 3 : ℝ)) ∧
          |clockFactor β x / (Real.log β * Real.exp (β * (1 - ⟪(x i).val, (x j).val⟫))) - 1| ≤
            β ^ (-(1 / 3 : ℝ)) ∧
          |(-PairDeficit.velocity model β x i j) * clockFactor β x -
            stageRate model T l * sineSquare x i j * Real.log β| ≤
              K * sineSquare x i j * β ^ (-(1 / 3 : ℝ)) * Real.log β ∧
          |(-((-PairDeficit.velocity model β x i j) * clockFactor β x) / sineSquare x i j) +
            stageRate model T l * Real.log β| ≤ K * β ^ (-(1 / 3 : ℝ)) * Real.log β := by
  classical
  let A : ℝ := 4 + 8 * (n : ℝ) + 10 * (n : ℝ) ^ 2
  let K : ℝ := ((n : ℝ) + 2) * A + 2 * n
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (TreeDynamics.particle_pos T)
  have hA : 0 < A := by dsimp [A]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hKn : (n : ℝ) * A ≤ K := by dsimp [K]; nlinarith only [hA, hn]
  have hK2 : 2 * A + 2 * n ≤ K := by dsimp [K]; nlinarith only [mul_nonneg hn.le hA.le]
  have hκ0 : 0 < κ := by linarith only [hκ]
  have hvel : ∀ᶠ β : ℝ in atTop, ∀ l : Fin N,
      1 < β ∧ ∀ (model : Model) (x : Configuration n d) (B D : Block n),
      B.Nonempty → D.Nonempty → ∀ i j,
      (∀ k ∈ B, angularDist (x k) (x i) ≤ Real.exp (-κ * β)) →
      (∀ k ∈ D, angularDist (x k) (x j) ≤ Real.exp (-κ * β)) →
      (∀ k ∉ B, k ∉ D → upperBarrier C l + 7 * treeMargin hN C ≤ PairDeficit.deficit x i k) →
      (∀ k ∉ D, k ∉ B → upperBarrier C l + 7 * treeMargin hN C ≤ PairDeficit.deficit x j k) →
      PairDeficit.deficit x i j ≤ upperBarrier C l + 2 * treeMargin hN C →
      mesoscopicScale β ≤ angularDist (x i) (x j) →
      |-PairDeficit.velocity model β x i j - rate model B D * (sineSquare x i j * kernel β x i j)| ≤
        A * (sineSquare x i j * kernel β x i j) * β ^ (-(1 / 3 : ℝ)) := by
    apply eventually_all.mpr
    intro l
    obtain ⟨_, hκU, hUL, hL, hU⟩ := source_barrier_parameters T hN C hC κ hκ l
    simpa only [A, neg_div] using ActiveVelocityScale.eventually_correlation_error n d κ
      (upperBarrier C l + 2 * treeMargin hN C) (upperBarrier C l + 7 * treeMargin hN C)
      hκ0 hκU hUL hL hU
  obtain ⟨V, hV⟩ := eventually_atTop.mp hvel
  obtain ⟨G, hG, hgeo⟩ := ActiveGeometry.stage_barriers T hN C hC
  obtain ⟨B, hB, hclock⟩ := ActiveClock.active_clock T hN C hC κ hκ0
  refine ⟨K, hK, max B (max G V), hB.trans_le (le_max_left _ _), ?_⟩
  intro β hβ M hM model l x hstage i j hi hj hupper hangle
  have hβB : B ≤ β := (le_max_left _ _).trans hβ
  have hβG : G ≤ β := (le_max_left _ _).trans ((le_max_right _ _).trans hβ)
  have hβV : V ≤ β := (le_max_right _ _).trans ((le_max_right _ _).trans hβ)
  have hβ1 : 1 < β := hB.trans_le hβB
  have hlog : 0 < Real.log β := Real.log_pos hβ1
  have hp : 0 ≤ β ^ (-(1 / 3 : ℝ)) := (Real.rpow_pos_of_pos (zero_lt_one.trans hβ1) _).le
  have hp1 : β ^ (-(1 / 3 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hβ1.le (by norm_num)
  have hu := (source_barrier_parameters T hN C hC κ hκ l).2.2.2.2
  have hρ := correlation_mem_Ioo β _ hβ1 hu x i j hupper hangle
  have hs : 0 < sineSquare x i j := by
    dsimp only [sineSquare]
    nlinarith only [hρ.1, hρ.2]
  have hk : 0 < kernel β x i j := Real.exp_pos _
  have hr := TreeDynamics.stageRate_pos T model l
  have hb := stageRate_bounds model T l
  have hext := (hgeo β hβG M hM l x hstage.2.1 hstage.2.2).1
  have hraw := (hV β hβV l).2 model x (T.left l) (T.right l)
    (T.block_nonempty _ _ (T.left_mem l)) (T.block_nonempty _ _ (T.right_mem l)) i j
    (fun k hk => hstage.1 _ (T.left_mem l) k hk i hi)
    (fun k hk => hstage.1 _ (T.right_mem l) k hk j hj)
    (fun k hkB hkC => hext i (Finset.mem_union_left _ hi) k (by
      simpa only [CollisionTree.parent, Finset.mem_union, not_or] using And.intro hkB hkC))
    (fun k hkC hkB => hext j (Finset.mem_union_right _ hj) k (by
      simpa only [CollisionTree.parent, Finset.mem_union, not_or] using And.intro hkB hkC))
    hupper hangle
  rw [rate_eq_stageRate model T l] at hraw
  have hc := (hclock β hβB M hM l x hstage.1 hstage.2.1 hstage.2.2 i j hi hj hupper hangle).2.2
  have hz : kernel β x i j * Real.exp (β * (1 - ⟪(x i).val, (x j).val⟫)) = 1 := by
    rw [kernel, ← Real.exp_add]
    convert Real.exp_zero using 1
    congr 1
    ring
  have hratio : clockFactor β x / (Real.log β * Real.exp (β * (1 - ⟪(x i).val, (x j).val⟫))) - 1 =
      (kernel β x i j * clockFactor β x - Real.log β) / Real.log β := by
    field_simp
    have hzf := congrArg (fun z => clockFactor β x * z) hz
    nlinarith only [hzf]
  rw [hratio, abs_div, abs_of_pos hlog] at hc
  have hcf : |kernel β x i j * clockFactor β x - Real.log β| ≤
      Real.log β * β ^ (-(1 / 3 : ℝ)) := by
    have h := (div_le_iff₀ hlog).mp hc
    simpa only [mul_comm] using h
  have hf : 0 ≤ clockFactor β x := by
    have h := (GeneralClock.clockFactor_bounds β hβ1 x).1
    exact (le_min zero_le_one hlog.le).trans h
  have hac := accelerated_error_algebra (-PairDeficit.velocity model β x i j)
    (stageRate model T l) (sineSquare x i j) (kernel β x i j) (clockFactor β x)
    (Real.log β) (β ^ (-(1 / 3 : ℝ))) A hr.le hs.le hf hlog.le hp hp1 hA.le hraw hcf
  have hacc : |(-PairDeficit.velocity model β x i j) * clockFactor β x -
      stageRate model T l * sineSquare x i j * Real.log β| ≤
      K * sineSquare x i j * β ^ (-(1 / 3 : ℝ)) * Real.log β := by
    have hcoeff : 2 * A + stageRate model T l ≤ K := by linarith only [hb.2, hK2]
    have hh := mul_le_mul_of_nonneg_right hcoeff (mul_nonneg (mul_nonneg hs.le hlog.le) hp)
    nlinarith only [hac, hh]
  refine ⟨hρ, ?_, ?_, hacc, ?_⟩
  · have hnr : 1 ≤ (n : ℝ) * stageRate model T l := by
      exact (div_le_iff₀ hn).mp hb.1 |>.trans_eq (mul_comm _ _)
    have hden : 0 < stageRate model T l * (sineSquare x i j * kernel β x i j) := by positivity
    rw [show (-PairDeficit.velocity model β x i j) /
        (stageRate model T l * (sineSquare x i j * kernel β x i j)) - 1 =
        (-PairDeficit.velocity model β x i j - stageRate model T l *
          (sineSquare x i j * kernel β x i j)) /
        (stageRate model T l * (sineSquare x i j * kernel β x i j)) by field_simp,
      abs_div, abs_of_pos hden]
    apply (div_le_iff₀ hden).mpr
    have hmul := mul_le_mul_of_nonneg_left hnr (mul_nonneg (mul_nonneg hA.le (mul_nonneg hs.le hk.le)) hp)
    have hKmul := mul_le_mul_of_nonneg_right hKn
      (mul_nonneg (mul_nonneg hr.le (mul_nonneg hs.le hk.le)) hp)
    nlinarith only [hraw, hmul, hKmul]
  · exact (hclock β hβB M hM l x hstage.1 hstage.2.1 hstage.2.2 i j hi hj hupper hangle).2.2
  · rw [show (-((-PairDeficit.velocity model β x i j) * clockFactor β x) / sineSquare x i j) +
        stageRate model T l * Real.log β =
        -((-PairDeficit.velocity model β x i j) * clockFactor β x -
          stageRate model T l * sineSquare x i j * Real.log β) / sineSquare x i j by field_simp; ring,
      abs_div, abs_neg, abs_of_pos hs]
    apply (div_le_iff₀ hs).mpr
    convert hacc using 1
    ring

/-- The active scalar and logarithmic half-angle laws for an actual source
trajectory and any clock satisfying the literal source clock relation.
The derivative statements hold almost everywhere on the nonnegative halfline;
the geometric hypotheses are tested at the current accelerated configuration. -/
theorem active_scalar_law (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) (κ : ℝ) (hκ : 4 < κ) :
    ∃ K : ℝ, 0 < K ∧ ∃ β₀ : ℝ, 1 < β₀ ∧
      ∀ β ≥ β₀, ∀ M ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 5),
        ∀ (model : Model) (l : Fin N) (X : ℝ → Configuration n d),
          Solves model β X → ∀ (shift : ℝ), 0 ≤ shift → ∀ (clock : ℝ → ℝ),
          ClockRelation β X shift clock → ∀ (i j : Fin n), i ∈ T.left l → j ∈ T.right l →
          ∀ᵐ t ∂volume.restrict (Ici (0 : ℝ)),
            StageHyp T C β κ M l (accelerated X shift clock t) →
            1 - ⟪(accelerated X shift clock t i).val, (accelerated X shift clock t j).val⟫ ≤
              upperBarrier C l + 2 * treeMargin hN C →
            mesoscopicScale β ≤ angularDist (accelerated X shift clock t i) (accelerated X shift clock t j) →
            ∃ vρ vlog : ℝ,
              HasDerivAt (fun u => ⟪(accelerated X shift clock u i).val,
                (accelerated X shift clock u j).val⟫) vρ t ∧
              |vρ - stageRate model T l *
                (1 - ⟪(accelerated X shift clock t i).val, (accelerated X shift clock t j).val⟫ ^ 2) *
                Real.log β| ≤ K *
                (1 - ⟪(accelerated X shift clock t i).val, (accelerated X shift clock t j).val⟫ ^ 2) *
                β ^ (-(1 / 3 : ℝ)) * Real.log β ∧
              HasDerivAt (fun u => ActiveLogCoordinate.logHalfAngle
                ⟪(accelerated X shift clock u i).val, (accelerated X shift clock u j).val⟫) vlog t ∧
              |vlog + stageRate model T l * Real.log β| ≤ K * β ^ (-(1 / 3 : ℝ)) * Real.log β := by
  obtain ⟨K, hK, β₀, hβ₀, hstatic⟩ := static_active_law T hN C hC κ hκ
  refine ⟨K, hK, β₀, hβ₀, ?_⟩
  intro β hβ M hM model l X hX shift hshift clock hc i j hi hj
  filter_upwards [ActiveTrajectory.ae_accelerated_correlation_hasDerivAt
    model β X hX shift hshift clock hc i j] with t hd
  intro hstage hupper hangle
  obtain ⟨hρ, _, _, hacc, hlog⟩ :=
    hstatic β hβ M hM model l (accelerated X shift clock t) hstage i j hi hj hupper hangle
  have hld := ActiveLogCoordinate.hasDerivAt_logHalfAngle_comp hρ hd
  exact ⟨_, _, hd, hacc, hld, hlog⟩

/-- The first equation of the source active proposition for the actual clock.
Only the literal clock relation is needed: its almost-everywhere derivative
and the proved geometric clock estimate give the conclusion directly. -/
theorem active_clock_law (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) (κ : ℝ) (hκ : 0 < κ) :
    ∃ β₀ : ℝ, 1 < β₀ ∧
      ∀ β ≥ β₀, ∀ M ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 5),
        ∀ (l : Fin N) (X : ℝ → Configuration n d) (shift : ℝ) (clock : ℝ → ℝ),
          ClockRelation β X shift clock → ∀ (i j : Fin n), i ∈ T.left l → j ∈ T.right l →
          ∀ᵐ t ∂volume.restrict (Ici (0 : ℝ)),
            StageHyp T C β κ M l (accelerated X shift clock t) →
            1 - ⟪(accelerated X shift clock t i).val, (accelerated X shift clock t j).val⟫ ≤
              upperBarrier C l + 2 * treeMargin hN C →
            mesoscopicScale β ≤ angularDist (accelerated X shift clock t i) (accelerated X shift clock t j) →
            HasDerivAt clock (clockFactor β (accelerated X shift clock t)) t ∧
              |clockFactor β (accelerated X shift clock t) /
                (Real.log β * Real.exp (β *
                  (1 - ⟪(accelerated X shift clock t i).val, (accelerated X shift clock t j).val⟫))) - 1| ≤
                β ^ (-(1 / 3 : ℝ)) := by
  obtain ⟨β₀, hβ₀, hclock⟩ := ActiveClock.active_clock T hN C hC κ hκ
  refine ⟨β₀, hβ₀, ?_⟩
  intro β hβ M hM l X shift clock hc i j hi hj
  filter_upwards [hc.1.2.2.2] with t hd
  intro hstage hupper hangle
  exact ⟨hd, (hclock β hβ M hM l (accelerated X shift clock t)
    hstage.1 hstage.2.1 hstage.2.2 i j hi hj hupper hangle).2.2⟩

/-- The original-time part of the source proposition for actual solutions,
with a uniform relative error and no reduced scalar equation as a premise. -/
theorem original_scalar_law (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) (κ : ℝ) (hκ : 4 < κ) :
    ∃ K : ℝ, 0 < K ∧ ∃ β₀ : ℝ, 1 < β₀ ∧
      ∀ β ≥ β₀, ∀ M ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 5),
        ∀ (model : Model) (l : Fin N) (X : ℝ → Configuration n d),
          Solves model β X → ∀ τ : ℝ, 0 < τ →
          StageHyp T C β κ M l (X τ) → ∀ (i j : Fin n), i ∈ T.left l → j ∈ T.right l →
          1 - ⟪(X τ i).val, (X τ j).val⟫ ≤ upperBarrier C l + 2 * treeMargin hN C →
          mesoscopicScale β ≤ angularDist (X τ i) (X τ j) →
          ∃ v : ℝ, HasDerivAt (fun u => ⟪(X u i).val, (X u j).val⟫) v τ ∧
            |v / (stageRate model T l * ((1 - ⟪(X τ i).val, (X τ j).val⟫ ^ 2) *
              Real.exp (β * (⟪(X τ i).val, (X τ j).val⟫ - 1)))) - 1| ≤
              K * β ^ (-(1 / 3 : ℝ)) := by
  obtain ⟨K, hK, β₀, hβ₀, hstatic⟩ := static_active_law T hN C hC κ hκ
  refine ⟨K, hK, β₀, hβ₀, ?_⟩
  intro β hβ M hM model l X hX τ hτ hstage i j hi hj hupper hangle
  exact ⟨_, ActiveTrajectory.correlation_hasDerivAt model β X hX i j τ hτ,
    (hstatic β hβ M hM model l (X τ) hstage i j hi hj hupper hangle).2.1⟩

end Metastability.ActiveSourceLaw
