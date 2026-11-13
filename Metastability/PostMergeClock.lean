import Metastability.ActiveClock
import Metastability.PlateauFuture

/-!
# The source clock after a merge

When every current block is below the literal cutoff, all eligible pairs
cross current blocks. A fixed positive interblock barrier then bounds the
actual finite-minimum clock from below. The inverse integral supplies the
accelerated duration without differentiability at switching times.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace

namespace Metastability.PostMergeClock
open Source
variable {n N d : ℕ}

/-- At a nonterminal tree partition, cutoff confinement and interblock
separation force the exact source clock to be exponentially large. -/
theorem clockFactor_lower (T : CollisionTree n N) (k : Fin N)
    (β b : ℝ) (hβ : 1 < β) (hcut : clockCutoff β < b) (x : Configuration n d)
    (hdiam : ∀ D ∈ T.partition k.castSucc, ∀ i ∈ D, ∀ j ∈ D,
      angularDist (x i) (x j) ≤ clockCutoff β)
    (hsep : ∀ D ∈ T.partition k.castSucc, ∀ i ∈ D, ∀ j ∉ D,
      b ≤ 1 - ⟪(x i).val, (x j).val⟫) :
    Real.log β * Real.exp (β * b) ≤ clockFactor β x := by
  classical
  obtain ⟨i, hi⟩ := T.block_nonempty _ _ (T.left_mem k)
  obtain ⟨j, hj⟩ := T.block_nonempty _ _ (T.right_mem k)
  have hjout : j ∉ T.left k := fun hh =>
    Finset.disjoint_left.mp (TreeDynamics.children_disjoint T k) hh hj
  have hij : i ≠ j := fun heq => hjout (heq ▸ hi)
  have hangle : clockCutoff β < angularDist (x i) (x j) :=
    hcut.trans_le ((hsep _ (T.left_mem k) i hi j hjout).trans
      (PlateauFuture.deficit_le_angle (x i) (x j)))
  have he : (eligiblePairs β x).Nonempty :=
    ⟨(i, j), (ActiveClock.mem_eligiblePairs β x i j).mpr ⟨hij, hangle⟩⟩
  unfold clockFactor
  rw [dif_pos he]
  apply mul_le_mul_of_nonneg_left _ (Real.log_pos hβ).le
  apply Finset.le_min'
  intro v hv
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
  have hne := ActiveClock.blockOf_ne_of_eligible T k β (clockCutoff β) x hdiam le_rfl p.1 p.2 hp
  have hout : p.2 ∉ T.blockOf k.castSucc p.1 := by
    intro hh
    exact hne (T.blockOf_unique k.castSucc p.2 _ (T.blockOf_spec k.castSucc p.1).1 hh)
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
    (hsep _ (T.blockOf_spec k.castSucc p.1).1 p.1 (T.blockOf_spec k.castSucc p.1).2 p.2 hout)
    (zero_lt_one.trans hβ).le)

/-- A lower rate bound on an original-time interval bounds the increment of
the literal inverse-clock integral. Integrability follows from the source ODE. -/
theorem originalClockTime_sub_le (model : Model) (β : ℝ) (hβ : 1 < β)
    (X : ℝ → Configuration n d) (hX : Solves model β X)
    (shift : ℝ) (hshift : 0 ≤ shift) (u v L : ℝ) (hu : 0 ≤ u)
    (huv : u ≤ v) (hL : 0 < L)
    (hlower : ∀ s ∈ Icc u v, L ≤ clockFactor β (X (shift + s))) :
    originalClockTime β X shift v - originalClockTime β X shift u ≤ (v - u) / L := by
  let r := GeneralClock.boundedRate β hβ X hX shift
  rw [← GeneralClock.elapsed_eq_originalClockTime β hβ X hX hshift (hu.trans huv),
    ← GeneralClock.elapsed_eq_originalClockTime β hβ X hX hshift hu]
  change r.elapsed v - r.elapsed u ≤ _
  rw [r.elapsed_sub]
  have hi := intervalIntegral.integral_mono_on huv (r.intervalIntegrable_inv_rate u v)
    (intervalIntegrable_const (c := L⁻¹)) (fun s hs => by
      have he := GeneralClock.boundedRate_rate_of_nonneg β hβ X hX hshift (hu.trans hs.1)
      change ((GeneralClock.boundedRate β hβ X hX shift).rate s)⁻¹ ≤ L⁻¹
      rw [he]
      simpa only [one_div] using one_div_le_one_div_of_le hL (hlower s hs))
  simpa only [intervalIntegral.integral_const, smul_eq_mul, div_eq_mul_inv] using hi

/-- The source inverse clock produces the next accelerated time and its exact
image. No existence of a future hitting time is assumed. -/
theorem exists_next_time (model : Model) (β : ℝ) (hβ : 1 < β)
    (X : ℝ → Configuration n d) (hX : Solves model β X)
    (shift : ℝ) (hshift : 0 ≤ shift) (clock : ℝ → ℝ) (hc : ClockRelation β X shift clock)
    (t₀ h b : ℝ) (ht₀ : 0 ≤ t₀) (hh : 0 ≤ h)
    (hlower : ∀ u ∈ Icc (shift + clock t₀) (shift + clock t₀ + h),
      Real.log β * Real.exp (β * b) ≤ clockFactor β (X u)) :
    ∃ t₁ : ℝ, t₀ ≤ t₁ ∧
      t₁ = originalClockTime β X shift (clock t₀ + h) ∧
      clock t₁ = clock t₀ + h ∧
      t₁ - t₀ ≤ h / Real.log β * Real.exp (-β * b) := by
  let t₁ := originalClockTime β X shift (clock t₀ + h)
  have hc₀ : 0 ≤ clock t₀ := hc.1.2.1 t₀ ht₀
  have hu : 0 ≤ clock t₀ + h := add_nonneg hc₀ hh
  have ht₁ : 0 ≤ t₁ := hc.2.2.1 _ hu
  have heq : clock t₁ = clock t₀ + h := hc.2.2.2.2 _ hu
  have hle : t₀ ≤ t₁ := by
    by_contra h
    have hlt := hc.2.1 ht₁ ht₀ (lt_of_not_ge h)
    rw [heq] at hlt
    linarith only [hlt, hh]
  refine ⟨t₁, hle, rfl, heq, ?_⟩
  have hbound := originalClockTime_sub_le model β hβ X hX shift hshift
    (clock t₀) (clock t₀ + h) (Real.log β * Real.exp (β * b)) hc₀
    (le_add_of_nonneg_right hh) (mul_pos (Real.log_pos hβ) (Real.exp_pos _)) (by
      intro u hu
      exact hlower (shift + u) ⟨by linarith only [hu.1], by linarith only [hu.2]⟩)
  rw [hc.2.2.2.1 t₀ ht₀] at hbound
  change t₁ - t₀ ≤ _ at hbound
  have hid : h / (Real.log β * Real.exp (β * b)) =
      h / Real.log β * Real.exp (-β * b) := by
    rw [show -β * b = -(β * b) by ring, Real.exp_neg, div_mul_eq_div_mul_one_div, one_div]
  calc
    t₁ - t₀ ≤ ((clock t₀ + h) - clock t₀) / (Real.log β * Real.exp (β * b)) := hbound
    _ = h / (Real.log β * Real.exp (β * b)) := by congr 1; ring
    _ = _ := hid

/-- The quantitative post-merge duration tends to zero for a fixed positive barrier. -/
theorem tendsto_duration_bound (C b : ℝ) (hb : 0 < b) :
    Tendsto (fun β : ℝ => C * β / Real.log β * Real.exp (-β * b)) atTop (𝓝 0) := by
  have he : Tendsto (fun β : ℝ => β * Real.exp (-b * β)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 b hb
  have hi : Tendsto (fun β : ℝ => (Real.log β)⁻¹) atTop (𝓝 0) :=
    Real.tendsto_log_atTop.inv_tendsto_atTop
  have heq : (fun β : ℝ => C * β / Real.log β * Real.exp (-β * b)) =
      (fun β : ℝ => C * ((β * Real.exp (-b * β)) * (Real.log β)⁻¹)) := by
    funext β
    rw [show -β * b = -b * β by ring]
    ring
  rw [heq]
  simpa only [mul_zero] using (he.mul hi).const_mul C

/-- The post-merge duration is smaller than the source log-logarithmic timing
scale for every sufficiently large real inverse temperature. -/
theorem eventually_duration_le_logRatio (C b : ℝ) (hb : 0 < b) :
    ∀ᶠ β : ℝ in atTop,
      C * β / Real.log β * Real.exp (-β * b) ≤ Real.log (Real.log β) / Real.log β := by
  have he : Tendsto (fun β : ℝ => C * β * Real.exp (-β * b)) atTop (𝓝 0) := by
    have hbase : Tendsto (fun β : ℝ => β * Real.exp (-b * β)) atTop (𝓝 0) := by
      simpa only [Real.rpow_one] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 b hb
    have heq : (fun β : ℝ => C * β * Real.exp (-β * b)) =
        (fun β : ℝ => C * (β * Real.exp (-b * β))) := by
      funext β
      rw [show -β * b = -b * β by ring]
      ring
    rw [heq]
    simpa only [mul_zero] using hbase.const_mul C
  filter_upwards [eventually_gt_atTop (1 : ℝ), he.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually (eventually_ge_atTop (1 : ℝ))]
    with β hβ heβ hloglog
  have hlog := Real.log_pos hβ
  have hh := div_le_div_of_nonneg_right (heβ.le.trans hloglog) hlog.le
  convert hh using 1
  ring

end Metastability.PostMergeClock
