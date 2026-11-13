import Metastability.PlateauScalar
import Metastability.SourceTerminalEstimates

/-!
# Unified scalar control until parent completion

The active and terminal source estimates cover both sides of the mesoscopic
scale. Noncompletion is needed only before the right endpoint. In particular,
an actual completion at that endpoint is permitted by all interval exports.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace

namespace Metastability.CompletionScalar
open Source ActiveScales ActiveVelocity ActiveSourceLaw CapEnlargement PlateauScalar ActiveCoefficients
variable {n N d : ℕ}

/-- Static bounds for the literal clock up to parent completion. The active
representative need not itself be clock-eligible below the mesoscopic scale. -/
theorem clock_bounds (T : CollisionTree n N) (hN : 0 < N) (C : TreeCaps T d)
    (hC : StrictlyPrepared C) (κ : ℝ) (hκ : 0 < κ) :
    ∃ β₀ : ℝ, 1 < β₀ ∧ ∀ β ≥ β₀,
      ∀ M ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 5), ∀ (l : Fin N) (x : Configuration n d),
      StageHyp T C β κ M l x → ∀ i j : Fin n, i ∈ T.left l → j ∈ T.right l →
      1 - ⟪(x i).val, (x j).val⟫ ≤ upperBarrier C l + 2 * treeMargin hN C →
      (¬ ∀ p ∈ T.parent l, ∀ q ∈ T.parent l, angularDist (x p) (x q) ≤ clockCutoff β) →
      clockFactor β x ≤ 2 * (Real.log β * Real.exp (β * (1 - ⟪(x i).val, (x j).val⟫))) ∧
      kernel β x i j * clockFactor β x ≤ 2 * Real.log β ∧
      clockFactor β x ≤ 2 * Real.log β * Real.exp (β * (upperBarrier C l + 2 * treeMargin hN C)) := by
  obtain ⟨B, hB, hclock⟩ := ActiveClock.source_clock_of_noncomplete T hN C hC κ hκ
  refine ⟨B, hB, ?_⟩
  intro β hβ M hM l x hstage i j hi hj hupper hnc
  have hβ1 := hB.trans_le hβ
  have hlog := Real.log_pos hβ1
  have hcf := (hclock β hβ M hM l x hstage.1 hstage.2.1 hstage.2.2 i j hi hj hupper hnc).2
  have hp1 : β ^ (-(1 / 3 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hβ1.le (by norm_num)
  have hden : 0 < Real.log β * Real.exp (β * (1 - ⟪(x i).val, (x j).val⟫)) := by positivity
  have hratio : clockFactor β x / (Real.log β * Real.exp (β * (1 - ⟪(x i).val, (x j).val⟫))) ≤ 2 := by
    linarith only [(abs_le.mp hcf).2, hp1]
  have hf := (div_le_iff₀ hden).mp hratio
  have hK := Real.exp_pos (β * (⟪(x i).val, (x j).val⟫ - 1))
  have hcancel : kernel β x i j * Real.exp (β * (1 - ⟪(x i).val, (x j).val⟫)) = 1 := by
    rw [kernel, ← Real.exp_add, show β * (⟪(x i).val, (x j).val⟫ - 1) +
      β * (1 - ⟪(x i).val, (x j).val⟫) = 0 by ring, Real.exp_zero]
  refine ⟨hf, ?_, ?_⟩
  · calc
      _ ≤ kernel β x i j * (2 * (Real.log β * Real.exp (β * (1 - ⟪(x i).val, (x j).val⟫)))) :=
        mul_le_mul_of_nonneg_left hf hK.le
      _ = (2 * Real.log β) * (kernel β x i j * Real.exp (β * (1 - ⟪(x i).val, (x j).val⟫))) := by ring
      _ = _ := by rw [hcancel, mul_one]
  · have hexp := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hupper (zero_lt_one.trans hβ1).le)
    have hlast := mul_le_mul_of_nonneg_left hexp (show 0 ≤ 2 * Real.log β by positivity)
    nlinarith only [hf, hlast]

/-- The actual correlation has a common positive lower slope in the active
and terminal windows, without a mesoscopic lower-angle assumption. -/
theorem ae_bounds (T : CollisionTree n N) (hN : 0 < N) (C : TreeCaps T d)
    (hC : StrictlyPrepared C) (κ : ℝ) (hκ : 4 < κ) :
    ∃ β₀ : ℝ, 1 < β₀ ∧ ∀ β ≥ β₀,
      ∀ M ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 5), ∀ (model : Model) (l : Fin N)
      (X : ℝ → Configuration n d), Solves model β X →
      ∀ shift : ℝ, 0 ≤ shift → ∀ clock : ℝ → ℝ, ClockRelation β X shift clock →
      ∀ i j : Fin n, i ∈ T.left l → j ∈ T.right l →
      ∀ᵐ t ∂volume.restrict (Ici (0 : ℝ)),
        StageHyp T C β κ M l (accelerated X shift clock t) →
        1 - correlation X shift clock i j t ≤ upperBarrier C l + 2 * treeMargin hN C →
        (¬ ∀ p ∈ T.parent l, ∀ q ∈ T.parent l,
          angularDist (accelerated X shift clock t p) (accelerated X shift clock t q) ≤ clockCutoff β) →
        (1 / (4 * (n : ℝ))) * activeWeight β X shift clock i j t ≤
          deriv (correlation X shift clock i j) t ∧
        HasDerivAt clock (clockFactor β (accelerated X shift clock t)) t ∧
        clockFactor β (accelerated X shift clock t) ≤
          2 * Real.log β * Real.exp (β * (upperBarrier C l + 2 * treeMargin hN C)) := by
  have hκ0 : 0 < κ := by linarith only [hκ]
  obtain ⟨B, hB, hactive⟩ := PlateauScalar.ae_bounds T hN C hC κ hκ
  obtain ⟨S, hS, hterminal⟩ := SourceTerminalEstimates.source_terminal_estimates T hN C hC κ hκ0
  obtain ⟨Q, hQ, hclock⟩ := ActiveClock.source_clock_of_noncomplete T hN C hC κ hκ0
  refine ⟨max B (max S Q), hB.trans_le (le_max_left _ _), ?_⟩
  intro β hβ M hM model l X hX shift hshift clock hc i j hi hj
  have hβB := (le_max_left B (max S Q)).trans hβ
  have hβS := (le_max_left S Q).trans ((le_max_right B (max S Q)).trans hβ)
  have hβQ := (le_max_right S Q).trans ((le_max_right B (max S Q)).trans hβ)
  have hβ1 : 1 < β := hB.trans_le hβB
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (TreeDynamics.particle_pos T)
  have hlog := Real.log_pos hβ1
  have hp1 : β ^ (-(1 / 3 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hβ1.le (by norm_num)
  filter_upwards [hactive β hβB M hM model l X hX shift hshift clock hc i j hi hj,
    ActiveTrajectory.ae_accelerated_correlation_hasDerivAt model β X hX shift hshift clock hc i j,
    hc.1.2.2.2] with t hact hd hdc
  intro hstage hupper hnc
  have hlow : (1 / (4 * (n : ℝ))) * activeWeight β X shift clock i j t ≤
      deriv (correlation X shift clock i j) t := by
    by_cases hmeso : mesoscopicScale β ≤
        angularDist (accelerated X shift clock t i) (accelerated X shift clock t j)
    · have hs := (hact hstage hupper hmeso).1
      have hr : (1 / (4 * (n : ℝ))) ≤ stageRate model T l / 2 := by
        have hh := (div_le_iff₀ hn).mp (stageRate_bounds model T l).1
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * n)).mpr
        nlinarith only [hh]
      exact (mul_le_mul_of_nonneg_right hr (activeWeight_nonneg β hβ1 X shift clock i j t)).trans hs
    · have hm : angularDist (accelerated X shift clock t i) (accelerated X shift clock t j) ≤
          mesoscopicScale β := (lt_of_not_ge hmeso).le
      have htwice : angularDist (accelerated X shift clock t i) (accelerated X shift clock t j) ≤
          2 * mesoscopicScale β := by linarith only [hm, mesoscopicScale_pos hβ1]
      have ht := ((hterminal β hβS).2.2 M hM l model (accelerated X shift clock t)
        hstage.1 hstage.2.1 hstage.2.2 i j hi hj hnc htwice).2.2 hm
      have hderiv : deriv (correlation X shift clock i j) t =
          (-PairDeficit.velocity model β (accelerated X shift clock t) i j) *
            clockFactor β (accelerated X shift clock t) := hd.deriv
      rw [hderiv]
      dsimp only [activeWeight]
      convert ht using 1
      ring
  have hcf := (hclock β hβQ M hM l (accelerated X shift clock t)
    hstage.1 hstage.2.1 hstage.2.2 i j hi hj hupper hnc).2
  have hden : 0 < Real.log β * Real.exp (β * (1 - correlation X shift clock i j t)) := by positivity
  have hratio : clockFactor β (accelerated X shift clock t) /
      (Real.log β * Real.exp (β * (1 - correlation X shift clock i j t))) ≤ 2 := by
    dsimp only [correlation]
    linarith only [(abs_le.mp hcf).2, hp1]
  have hmul := (div_le_iff₀ hden).mp hratio
  have hexp := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hupper (zero_lt_one.trans hβ1).le)
  have hlast := mul_le_mul_of_nonneg_left hexp (show 0 ≤ 2 * Real.log β by positivity)
  exact ⟨hlow, hdc, by nlinarith only [hmul, hlast]⟩

/-- Unified closed-interval monotonicity, clock duration, and source weighted
integrals. The parent may complete at b; no mesoscopic angle bound is assumed. -/
theorem interval_bounds (T : CollisionTree n N) (hN : 0 < N) (C : TreeCaps T d)
    (hC : StrictlyPrepared C) (κ : ℝ) (hκ : 4 < κ) :
    ∃ β₀ : ℝ, 1 < β₀ ∧ ∀ β ≥ β₀,
      ∀ M ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 5), ∀ (model : Model) (l : Fin N)
      (X : ℝ → Configuration n d), Solves model β X →
      ∀ shift : ℝ, 0 ≤ shift → ∀ clock : ℝ → ℝ, ClockRelation β X shift clock →
      ∀ i j : Fin n, i ∈ T.left l → j ∈ T.right l →
      ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      (∀ t ∈ Icc a b, StageHyp T C β κ M l (accelerated X shift clock t)) →
      (∀ t ∈ Icc a b, 1 - correlation X shift clock i j t ≤
        upperBarrier C l + 2 * treeMargin hN C) →
      (∀ t ∈ Ico a b, ¬ ∀ p ∈ T.parent l, ∀ q ∈ T.parent l,
        angularDist (accelerated X shift clock t p) (accelerated X shift clock t q) ≤ clockCutoff β) →
      MonotoneOn (correlation X shift clock i j) (Icc a b) ∧
      clock b - clock a ≤ 2 * (b - a) * Real.log β *
        Real.exp (β * (upperBarrier C l + 2 * treeMargin hN C)) ∧
      IntervalIntegrable (activeWeight β X shift clock i j) volume a b ∧
      IntervalIntegrable (fun t => β * activeWeight β X shift clock i j t) volume a b ∧
      (∫ t in a..b, activeWeight β X shift clock i j t) ≤
        (4 * n) * (correlation X shift clock i j b - correlation X shift clock i j a) ∧
      (∫ t in a..b, activeWeight β X shift clock i j t) ≤ 8 * n ∧
      (∫ t in a..b, β * activeWeight β X shift clock i j t) ≤ (8 * n) * β := by
  obtain ⟨B, hB, hbounds⟩ := ae_bounds T hN C hC κ hκ
  refine ⟨B, hB, ?_⟩
  intro β hβ M hM model l X hX shift hshift clock hc i j hi hj a b ha hab hstage hupper hnc
  have hβ1 := hB.trans_le hβ
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (TreeDynamics.particle_pos T)
  have hAE := (ae_restrict_iff' measurableSet_Ici).mp
    (hbounds β hβ M hM model l X hX shift hshift clock hc i j hi hj)
  have hρac : AbsolutelyContinuousOnInterval (correlation X shift clock i j) a b :=
    ActiveTrajectory.accelerated_correlation_absolutelyContinuous model β hβ1
      X hX shift hshift clock hc i j a b ha hab
  have hw := activeWeight_intervalIntegrable model β hβ1 X hX shift hshift clock hc i j a b ha hab
  have hd : ∀ᵐ t ∂volume, t ∈ Ioo a b →
      (1 / (4 * (n : ℝ))) * activeWeight β X shift clock i j t ≤
        deriv (correlation X shift clock i j) t := by
    filter_upwards [hAE] with t ht hmem
    have hm : t ∈ Icc a b := ⟨hmem.1.le, hmem.2.le⟩
    exact (ht (ha.trans hm.1) (hstage t hm) (hupper t hm) (hnc t ⟨hmem.1.le, hmem.2⟩)).1
  have hmono : MonotoneOn (correlation X shift clock i j) (Icc a b) := by
    intro s hs t ht hst
    have hac : AbsolutelyContinuousOnInterval (correlation X shift clock i j) s t :=
      hρac.mono (by rw [uIcc_of_le hst, uIcc_of_le hab]; exact Icc_subset_Icc hs.1 ht.2)
    have hh := ActiveBarrier.sub_nonneg_of_ae_deriv_nonneg hst hac (by
      filter_upwards [hd] with u hu humem
      exact (mul_nonneg (by positivity : (0 : ℝ) ≤ 1 / (4 * n))
        (activeWeight_nonneg β hβ1 X shift clock i j u)).trans
        (hu ⟨hs.1.trans_lt humem.1, humem.2.trans_le ht.2⟩))
    linarith only [hh]
  have hclockac : AbsolutelyContinuousOnInterval clock a b := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval
    rw [uIcc_of_le hab]
    exact (ActiveTrajectory.clock_lipschitz model β hβ1 X hX shift hshift clock hc).mono
      (fun _ ht => ha.trans ht.1)
  have hlength := ActiveTiming.sub_le_of_ae_deriv_le hab hclockac (by
    filter_upwards [hAE] with t ht hmem
    have hm : t ∈ Icc a b := ⟨hmem.1.le, hmem.2.le⟩
    obtain ⟨_, hdc, hcf⟩ := ht (ha.trans hm.1) (hstage t hm) (hupper t hm) (hnc t ⟨hmem.1.le, hmem.2⟩)
    rwa [hdc.deriv])
  have hint0 := integral_le_of_ae_lower_deriv hab
    (by positivity : (0 : ℝ) < 1 / (2 * n)) hρac hw (by
      have he : (1 / (2 * (n : ℝ))) / 2 = 1 / (4 * n) := by ring
      simpa only [he] using hd)
  have hint : (∫ t in a..b, activeWeight β X shift clock i j t) ≤
      (4 * n) * (correlation X shift clock i j b - correlation X shift clock i j a) := by
    have he : (2 : ℝ) / (1 / (2 * n)) = 4 * n := by field_simp; norm_num
    simpa only [he] using hint0
  have hdiff : correlation X shift clock i j b - correlation X shift clock i j a ≤ 2 := by
    have hba := (ModelBounds.inner_bounds (accelerated X shift clock b i) (accelerated X shift clock b j)).2
    have haa := (ModelBounds.inner_bounds (accelerated X shift clock a i) (accelerated X shift clock a j)).1
    dsimp only [correlation]
    linarith only [hba, haa]
  have hint8 : (∫ t in a..b, activeWeight β X shift clock i j t) ≤ 8 * n := by
    have hh := hint.trans (mul_le_mul_of_nonneg_left hdiff (by positivity))
    nlinarith only [hh]
  refine ⟨hmono, ?_, hw, hw.const_mul β, hint, hint8, ?_⟩
  · nlinarith only [hlength]
  · rw [intervalIntegral.integral_const_mul]
    have hh := mul_le_mul_of_nonneg_left hint8 (zero_lt_one.trans hβ1).le
    simpa only [mul_comm] using hh

end Metastability.CompletionScalar
