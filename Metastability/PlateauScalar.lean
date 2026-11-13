import Metastability.ActiveSourceLaw
import Metastability.ActiveBarrier

/-!
# Scalar control on a stopped active plateau

All differential estimates in the source-facing exports are derived from the
actual source dynamics and cutoff clock. The closed interval hypotheses are
the stopped stage geometry; no scalar differential inequality is assumed.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace

namespace Metastability.PlateauScalar
open Source ActiveScales ActiveVelocity ActiveSourceLaw CapEnlargement
variable {n N d : ℕ}

def correlation (X : ℝ → Configuration n d) (shift : ℝ) (clock : ℝ → ℝ)
    (i j : Fin n) (t : ℝ) : ℝ :=
  ⟪(accelerated X shift clock t i).val, (accelerated X shift clock t j).val⟫

def activeWeight (β : ℝ) (X : ℝ → Configuration n d) (shift : ℝ)
    (clock : ℝ → ℝ) (i j : Fin n) (t : ℝ) : ℝ :=
  sineSquare (accelerated X shift clock t) i j * Real.log β

theorem activeWeight_nonneg (β : ℝ) (hβ : 1 < β)
    (X : ℝ → Configuration n d) (shift : ℝ) (clock : ℝ → ℝ) (i j : Fin n) (t : ℝ) :
    0 ≤ activeWeight β X shift clock i j t :=
  mul_nonneg (sineSquare_nonneg _ _ _) (Real.log_pos hβ).le

theorem activeWeight_intervalIntegrable (model : Model) (β : ℝ) (hβ : 1 < β)
    (X : ℝ → Configuration n d) (hX : Solves model β X)
    (shift : ℝ) (hshift : 0 ≤ shift) (clock : ℝ → ℝ) (hc : ClockRelation β X shift clock)
    (i j : Fin n) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (activeWeight β X shift clock i j) volume a b := by
  have hρ := ((ActiveTrajectory.accelerated_correlation_lipschitz model β hβ X hX
    shift hshift clock hc i j).mono (show Icc a b ⊆ Ici (0 : ℝ) from fun _ ht => ha.trans ht.1)).continuousOn
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  exact (continuousOn_const.sub (hρ.pow 2)).mul_const (Real.log β)

/-- The eventual derivative lower bound and clock upper bound, uniformly in
the stage and both models. The assumptions are exactly the stopped source
stage hypotheses and active angular range. -/
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
        mesoscopicScale β ≤ angularDist (accelerated X shift clock t i) (accelerated X shift clock t j) →
        (stageRate model T l / 2) * activeWeight β X shift clock i j t ≤
          deriv (correlation X shift clock i j) t ∧
        HasDerivAt clock (clockFactor β (accelerated X shift clock t)) t ∧
        clockFactor β (accelerated X shift clock t) ≤
          2 * Real.log β * Real.exp (β * (upperBarrier C l + 2 * treeMargin hN C)) := by
  obtain ⟨K, hK, B, hB, hstatic⟩ := static_active_law T hN C hC κ hκ
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (TreeDynamics.particle_pos T)
  have hp : Tendsto (fun β : ℝ => K * β ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).const_mul K
  obtain ⟨S, hS⟩ := eventually_atTop.mp
    (hp.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / (2 * n))))
  refine ⟨max B S, hB.trans_le (le_max_left _ _), ?_⟩
  intro β hβ M hM model l X hX shift hshift clock hc i j hi hj
  have hβB : B ≤ β := (le_max_left _ _).trans hβ
  have hβ1 : 1 < β := hB.trans_le hβB
  have hlog : 0 < Real.log β := Real.log_pos hβ1
  have hsmall : K * β ^ (-(1 / 3 : ℝ)) ≤ stageRate model T l / 2 := by
    have hs := (hS β ((le_max_right _ _).trans hβ)).le
    have hr := (stageRate_bounds model T l).1
    have he : (1 / (n : ℝ)) / 2 = 1 / (2 * n) := by ring
    rw [← he] at hs
    exact hs.trans (div_le_div_of_nonneg_right hr (by norm_num))
  have hp1 : β ^ (-(1 / 3 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hβ1.le (by norm_num)
  filter_upwards [ActiveTrajectory.ae_accelerated_correlation_hasDerivAt model β X hX
    shift hshift clock hc i j, hc.1.2.2.2] with t hd hdc
  intro hstage hupper hangle
  obtain ⟨_, _, hcf, hacc, _⟩ := hstatic β hβB M hM model l
    (accelerated X shift clock t) hstage i j hi hj hupper hangle
  have hw := activeWeight_nonneg β hβ1 X shift clock i j t
  have hmul := mul_le_mul_of_nonneg_right hsmall hw
  have hlow := (abs_le.mp hacc).1
  have hdρ : deriv (correlation X shift clock i j) t =
      (-PairDeficit.velocity model β (accelerated X shift clock t) i j) *
        clockFactor β (accelerated X shift clock t) := hd.deriv
  refine ⟨?_, hdc, ?_⟩
  · rw [hdρ]
    dsimp only [activeWeight] at hmul ⊢
    nlinarith only [hlow, hmul]
  · have hden : 0 < Real.log β * Real.exp (β * (1 - correlation X shift clock i j t)) := by positivity
    have hratio : clockFactor β (accelerated X shift clock t) /
        (Real.log β * Real.exp (β * (1 - correlation X shift clock i j t))) ≤ 2 := by
      dsimp only [correlation]
      linarith only [(abs_le.mp hcf).2, hp1]
    have hmul := (div_le_iff₀ hden).mp hratio
    have hexp := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hupper (zero_lt_one.trans hβ1).le)
    have hlast := mul_le_mul_of_nonneg_left hexp (show 0 ≤ 2 * Real.log β by positivity)
    nlinarith only [hmul, hlast]

theorem integral_le_of_ae_lower_deriv {f w : ℝ → ℝ} {a b c : ℝ}
    (hab : a ≤ b) (hc : 0 < c) (hf : AbsolutelyContinuousOnInterval f a b)
    (hw : IntervalIntegrable w volume a b)
    (hd : ∀ᵐ t ∂volume, t ∈ Ioo a b → (c / 2) * w t ≤ deriv f t) :
    (∫ t in a..b, w t) ≤ (2 / c) * (f b - f a) := by
  have hd' : ∀ᵐ t ∂volume.restrict (Icc a b), (c / 2) * w t ≤ deriv f t := by
    apply (ae_restrict_iff' measurableSet_Icc).mpr
    filter_upwards [hd, volume.ae_ne a, volume.ae_ne b] with t ht hta htb hmem
    exact ht ⟨lt_of_le_of_ne hmem.1 (Ne.symm hta), lt_of_le_of_ne hmem.2 htb⟩
  have hi := intervalIntegral.integral_mono_ae_restrict hab (hw.const_mul (c / 2))
    hf.intervalIntegrable_deriv hd'
  rw [intervalIntegral.integral_const_mul, hf.integral_deriv_eq_sub] at hi
  apply (mul_le_mul_iff_left₀ hc).mp
  have he : ((2 / c) * (f b - f a)) * c = 2 * (f b - f a) := by field_simp
  rw [he]
  nlinarith only [hi]

/-- Closed-interval plateau estimates from the actual source scalar law.
No bound on the interval length is needed for these estimates. -/
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
      (∀ t ∈ Icc a b, mesoscopicScale β ≤
        angularDist (accelerated X shift clock t i) (accelerated X shift clock t j)) →
      MonotoneOn (correlation X shift clock i j) (Icc a b) ∧
      clock b - clock a ≤ 2 * (b - a) * Real.log β *
        Real.exp (β * (upperBarrier C l + 2 * treeMargin hN C)) ∧
      IntervalIntegrable (activeWeight β X shift clock i j) volume a b ∧
      IntervalIntegrable (fun t => β * activeWeight β X shift clock i j t) volume a b ∧
      (∫ t in a..b, activeWeight β X shift clock i j t) ≤
        (2 / stageRate model T l) * (correlation X shift clock i j b - correlation X shift clock i j a) ∧
      (∫ t in a..b, activeWeight β X shift clock i j t) ≤ 4 / stageRate model T l ∧
      (∫ t in a..b, β * activeWeight β X shift clock i j t) ≤ (4 / stageRate model T l) * β := by
  obtain ⟨B, hB, hbounds⟩ := ae_bounds T hN C hC κ hκ
  refine ⟨B, hB, ?_⟩
  intro β hβ M hM model l X hX shift hshift clock hc i j hi hj a b ha hab hstage hupper hangle
  have hβ1 := hB.trans_le hβ
  have hrate := TreeDynamics.stageRate_pos T model l
  have hAE := (ae_restrict_iff' measurableSet_Ici).mp
    (hbounds β hβ M hM model l X hX shift hshift clock hc i j hi hj)
  have hρac := ActiveTrajectory.accelerated_correlation_absolutelyContinuous model β hβ1
    X hX shift hshift clock hc i j a b ha hab
  have hw := activeWeight_intervalIntegrable model β hβ1 X hX shift hshift clock hc i j a b ha hab
  have hd : ∀ᵐ t ∂volume, t ∈ Ioo a b →
      (stageRate model T l / 2) * activeWeight β X shift clock i j t ≤
        deriv (correlation X shift clock i j) t := by
    filter_upwards [hAE] with t ht hmem
    have hm : t ∈ Icc a b := ⟨hmem.1.le, hmem.2.le⟩
    exact (ht (ha.trans hm.1) (hstage t hm) (hupper t hm) (hangle t hm)).1
  have hmono : MonotoneOn (correlation X shift clock i j) (Icc a b) := by
    intro s hs t ht hst
    have hac : AbsolutelyContinuousOnInterval (correlation X shift clock i j) s t :=
      hρac.mono (by rw [uIcc_of_le hst, uIcc_of_le hab]; exact Icc_subset_Icc hs.1 ht.2)
    have hn := ActiveBarrier.sub_nonneg_of_ae_deriv_nonneg hst hac (by
      filter_upwards [hd] with u hu humem
      exact (mul_nonneg (div_pos hrate (by norm_num)).le
        (activeWeight_nonneg β hβ1 X shift clock i j u)).trans
        (hu ⟨hs.1.trans_lt humem.1, humem.2.trans_le ht.2⟩))
    linarith only [hn]
  have hclockac : AbsolutelyContinuousOnInterval clock a b := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval
    rw [uIcc_of_le hab]
    exact (ActiveTrajectory.clock_lipschitz model β hβ1 X hX shift hshift clock hc).mono
      (fun _ ht => ha.trans ht.1)
  have hlength := ActiveTiming.sub_le_of_ae_deriv_le hab hclockac (by
    filter_upwards [hAE] with t ht hmem
    have hm : t ∈ Icc a b := ⟨hmem.1.le, hmem.2.le⟩
    obtain ⟨_, hdc, hcf⟩ := ht (ha.trans hm.1) (hstage t hm) (hupper t hm) (hangle t hm)
    rwa [hdc.deriv])
  have hint := integral_le_of_ae_lower_deriv hab hrate hρac hw hd
  have hdiff : correlation X shift clock i j b - correlation X shift clock i j a ≤ 2 := by
    have hba := (ModelBounds.inner_bounds (accelerated X shift clock b i) (accelerated X shift clock b j)).2
    have haa := (ModelBounds.inner_bounds (accelerated X shift clock a i) (accelerated X shift clock a j)).1
    dsimp only [correlation]
    linarith only [hba, haa]
  have hint4 : (∫ t in a..b, activeWeight β X shift clock i j t) ≤ 4 / stageRate model T l := by
    have hh := hint.trans (mul_le_mul_of_nonneg_left hdiff (by positivity))
    convert hh using 1
    ring
  refine ⟨hmono, ?_, hw, hw.const_mul β, hint, hint4, ?_⟩
  · nlinarith only [hlength]
  · rw [intervalIntegral.integral_const_mul]
    have hh := mul_le_mul_of_nonneg_left hint4 (zero_lt_one.trans hβ1).le
    simpa only [mul_comm] using hh

/-- Monotonicity retains the tighter entry deficit and therefore excludes
an exit through the active upper barrier, including at the closed endpoint. -/
theorem retains_entry_upper (T : CollisionTree n N) (hN : 0 < N) (C : TreeCaps T d)
    (hC : StrictlyPrepared C) (l : Fin N)
    (X : ℝ → Configuration n d) (shift : ℝ) (clock : ℝ → ℝ) (i j : Fin n)
    (a b : ℝ) (hab : a ≤ b)
    (hmono : MonotoneOn (correlation X shift clock i j) (Icc a b))
    (hentry : 1 - correlation X shift clock i j a ≤ upperBarrier C l + treeMargin hN C) :
    ∀ t ∈ Icc a b,
      1 - correlation X shift clock i j t ≤ upperBarrier C l + treeMargin hN C ∧
      1 - correlation X shift clock i j t < upperBarrier C l + 2 * treeMargin hN C := by
  intro t ht
  have hh := hmono ⟨le_rfl, hab⟩ ht ht.1
  have hδ := treeMargin_pos hN C hC
  constructor <;> linarith only [hh, hentry, hδ]

end Metastability.PlateauScalar
