import Metastability.StageScalar
import Metastability.ActiveEntry

/-! Uniform collapse of the active angle a fixed accelerated distance after
entry. Every scalar estimate is supplied by the actual source dynamics. -/
noncomputable section
open Set Filter
open scoped Topology RealInnerProductSpace
namespace Metastability.StageAngleLimit
open Source ActiveSourceLaw ActiveScales ActiveLogCoordinate CapEnlargement
variable {n N d : ℕ}

/-- A fixed positive time after entry, the representative angle is uniformly
small as beta grows, provided this remains in the pre-mesoscopic stage. -/
theorem eventual_angle_small (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) (κ : ℝ) (hκ : 4 < κ)
    (model : Model) (l : Fin N) (η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∀ᶠ β : ℝ in atTop, 1 < β ∧
      ∀ M ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 5),
      ∀ X : ℝ → Configuration n d, Solves model β X →
      ∀ shift : ℝ, 0 ≤ shift → ∀ clock : ℝ → ℝ, ClockRelation β X shift clock →
      ∀ i j : Fin n, i ∈ T.left l → j ∈ T.right l →
      ∀ a b : ℝ, 0 ≤ a → a + η ≤ b →
      angularDist (accelerated X shift clock a i) (C (T.leftNode l)).center ≤
        (C (T.leftNode l)).radius + M * enlargementScale β →
      angularDist (accelerated X shift clock a j) (C (T.rightNode l)).center ≤
        (C (T.rightNode l)).radius + M * enlargementScale β →
      (∀ t ∈ Icc a b, StageHyp T C β κ M l (accelerated X shift clock t)) →
      (∀ t ∈ Icc a b, 1 - ⟪(accelerated X shift clock t i).val,
        (accelerated X shift clock t j).val⟫ ≤ upperBarrier C l + 2 * treeMargin hN C) →
      (∀ t ∈ Icc a b, mesoscopicScale β ≤
        angularDist (accelerated X shift clock t i) (accelerated X shift clock t j)) →
      angularDist (accelerated X shift clock b i) (accelerated X shift clock b j) < ε := by
  obtain ⟨K, hK, A, hA, hintegrated⟩ := StageScalar.integrated_log_law T hN C hC κ hκ
  obtain ⟨B, _, E, _, hentry⟩ := ActiveEntry.entry_log_bound T C hC l
  let c := stageRate model T l
  have hc : 0 < c := TreeDynamics.stageRate_pos T model l
  let θ := min ε 1
  have hθ : 0 < θ := lt_min hε (by norm_num)
  have hθπ : θ < Real.pi := (min_le_right ε 1).trans_lt (by linarith only [Real.two_le_pi])
  have hcos : Real.cos θ ∈ Ioo (-1 : ℝ) 1 := by
    constructor
    · have hh := Real.cos_lt_cos_of_nonneg_of_le_pi hθ.le (le_refl Real.pi) hθπ
      simpa only [Real.cos_pi] using hh
    · have hh := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl (0 : ℝ)) hθπ.le hθ
      simpa only [Real.cos_zero] using hh
  have herr : ∀ᶠ β : ℝ in atTop, K * β ^ (-(1 / 3 : ℝ)) ≤ c / 2 := by
    have hl : Tendsto (fun β : ℝ => K * β ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) := by
      simpa only [mul_zero] using
        (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).const_mul K
    exact (hl.eventually (gt_mem_nhds (half_pos hc))).mono (fun _ h => h.le)
  have hlarge : ∀ᶠ β : ℝ in atTop,
      (B - logHalfAngle (Real.cos θ)) / (c * η / 2) < Real.log β :=
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop _)
  filter_upwards [eventually_ge_atTop A, eventually_ge_atTop E, herr, hlarge]
    with β hβA hβE herr hlarge
  have hβ : 1 < β := hA.trans_le hβA
  have hlog := Real.log_pos hβ
  refine ⟨hβ, ?_⟩
  intro M hM X hX shift hshift clock hclock i j hi hj a b ha hab hleft hright hstage hupper hangle
  have hab' : a ≤ b := (le_add_of_nonneg_right hη.le).trans hab
  have hent := hentry β hβE M hM _ _ hleft hright
  have hint := hintegrated β hβA M hM model l X hX shift hshift clock hclock i j hi hj
    a b ha hab' hstage hupper hangle
  let ρ := ⟪(accelerated X shift clock b i).val, (accelerated X shift clock b j).val⟫
  have hρ : ρ ∈ Ioo (-1 : ℝ) 1 := correlation_mem_Ioo β _ hβ
    (source_barrier_parameters T hN C hC κ hκ l).2.2.2.2 _ i j
    (hupper b ⟨hab', le_rfl⟩) (hangle b ⟨hab', le_rfl⟩)
  have htime : η ≤ b - a := by linarith only [hab]
  have hbound : logHalfAngle ρ ≤ B - (c * η / 2) * Real.log β := by
    have he := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right herr hlog.le) (sub_nonneg.mpr hab')
    have ht := mul_le_mul_of_nonneg_left htime (mul_nonneg (half_pos hc).le hlog.le)
    have hi' := (abs_le.mp hint).2
    have hs := (abs_le.mp hent.2).2
    dsimp only [c] at he ht ⊢
    linarith only [hi', hs, he, ht]
  have hbelow : logHalfAngle ρ < logHalfAngle (Real.cos θ) := by
    have hp : 0 < c * η / 2 := div_pos (mul_pos hc hη) (by norm_num)
    have hm := (div_lt_iff₀ hp).mp hlarge
    linarith only [hbound, hm]
  have hcor : Real.cos θ < ρ := by
    by_contra h
    exact (not_lt_of_ge
      (strictAntiOn_logHalfAngle.antitoneOn hρ hcos (le_of_not_gt h))) hbelow
  have hang : angularDist (accelerated X shift clock b i) (accelerated X shift clock b j) < θ := by
    change Real.arccos ρ < θ
    rw [← Real.arccos_cos hθ.le hθπ.le]
    exact Real.arccos_lt_arccos hcos.1.le hcor hρ.2.le
  exact hang.trans_le (min_le_left ε 1)

end Metastability.StageAngleLimit
