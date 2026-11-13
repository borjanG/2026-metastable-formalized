import Metastability.CompletionScalar

/-! Actual vector equations near two tight blocks. The finite remainder bounds
retain the tangent projection norm and the literal SA row normalization. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators RealInnerProductSpace
namespace Metastability.ActiveVectorLaw
open Source ActiveCoefficients ActiveVelocity ActiveScales ActiveSourceLaw CapEnlargement
variable {n N d : ℕ}

theorem projection_self (u : Sphere d) : projectTangent u u.val = 0 := by
  simp only [projectTangent, real_inner_self_eq_norm_sq, u.property, one_pow, one_smul, sub_self]

theorem projection_variation (u v w : Sphere d) :
    ‖projectTangent u v.val - projectTangent u w.val‖ ≤ 2 * angularDist v w := by
  have he : projectTangent u v.val - projectTangent u w.val =
      (v.val - w.val) - ⟪u.val, v.val - w.val⟫ • u.val := by
    simp only [projectTangent, inner_sub_right, sub_smul]
    abel
  have hi : |⟪u.val, v.val - w.val⟫| ≤ ‖v.val - w.val‖ := by
    simpa only [u.property, one_mul] using abs_real_inner_le_norm u.val (v.val - w.val)
  rw [he]
  calc
    _ ≤ ‖v.val - w.val‖ + ‖⟪u.val, v.val - w.val⟫ • u.val‖ := norm_sub_le _ _
    _ ≤ 2 * ‖v.val - w.val‖ := by
      rw [norm_smul, Real.norm_eq_abs, u.property, mul_one]
      linarith only [hi]
    _ ≤ _ := mul_le_mul_of_nonneg_left (AngularGeometry.norm_sub_le_angularDist v w) (by norm_num)

theorem projection_norm_le_two (u v : Sphere d) : ‖projectTangent u v.val‖ ≤ 2 := by
  have hi := abs_le.mpr (ModelBounds.inner_bounds u v)
  calc
    _ ≤ ‖v.val‖ + ‖⟪u.val, v.val⟫ • u.val‖ := norm_sub_le _ _
    _ ≤ 2 := by
      rw [norm_smul, Real.norm_eq_abs, u.property, v.property, mul_one]
      linarith only [hi]

theorem vectorField_eq_sum (model : Model) (β : ℝ) (x : Configuration n d) (i : Fin n) :
    vectorField model β x i = ∑ k, coefficient model β x i k • projectTangent (x i) (x k).val := by
  simp only [vectorField, projectTangent, inner_sum, inner_smul_right,
    Finset.sum_smul, smul_sub, smul_smul, ← Finset.sum_sub_distrib]

theorem geometric_error (model : Model) (β δ L : ℝ) (hβ : 0 ≤ β) (hδ : 0 ≤ δ)
    (x : Configuration n d) (B C : Block n) (i j : Fin n)
    (hBclose : ∀ k ∈ B, angularDist (x k) (x i) ≤ δ)
    (hCclose : ∀ k ∈ C, angularDist (x k) (x j) ≤ δ)
    (hsep : ∀ k ∉ B, k ∉ C → L ≤ PairDeficit.deficit x i k) :
    ‖vectorField model β x i - (∑ k ∈ C, coefficient model β x i k) • projectTangent (x i) (x j).val‖ ≤
      2 * δ + 2 * n * Real.exp (-β * L) := by
  classical
  have hterm : ∀ k : Fin n,
      ‖coefficient model β x i k • (projectTangent (x i) (x k).val -
        (if k ∈ C then projectTangent (x i) (x j).val else 0))‖ ≤
      2 * δ * coefficient model β x i k + 2 * Real.exp (-β * L) := by
    intro k
    have hc := ModelBounds.coefficient_nonneg model β x i k
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
    by_cases hkC : k ∈ C
    · rw [if_pos hkC]
      have hh := mul_le_mul_of_nonneg_left ((projection_variation (x i) (x k) (x j)).trans
        (mul_le_mul_of_nonneg_left (hCclose k hkC) (by norm_num))) hc
      nlinarith only [hh, Real.exp_pos (-β * L)]
    · rw [if_neg hkC, sub_zero]
      by_cases hkB : k ∈ B
      · have hp : ‖projectTangent (x i) (x k).val‖ ≤ 2 * δ := by
          simpa only [projection_self, sub_zero] using
            (projection_variation (x i) (x k) (x i)).trans
              (mul_le_mul_of_nonneg_left (hBclose k hkB) (by norm_num))
        have hh := mul_le_mul_of_nonneg_left hp hc
        nlinarith only [hh, Real.exp_pos (-β * L)]
      · have hcO := ModelBounds.coefficient_le_exp_barrier model β L hβ x i k (by
          have hh := hsep k hkB hkC
          dsimp only [PairDeficit.deficit] at hh
          linarith only [hh])
        have hh := mul_le_mul hcO (projection_norm_le_two (x i) (x k)) (norm_nonneg _) (Real.exp_pos _).le
        nlinarith only [hh, mul_nonneg hδ hc]
  have heq : vectorField model β x i - (∑ k ∈ C, coefficient model β x i k) • projectTangent (x i) (x j).val =
      ∑ k : Fin n, coefficient model β x i k • (projectTangent (x i) (x k).val -
        (if k ∈ C then projectTangent (x i) (x j).val else 0)) := by
    rw [vectorField_eq_sum]
    simp only [smul_sub, Finset.sum_sub_distrib, Finset.sum_smul, smul_ite, smul_zero,
      Finset.sum_ite_mem, Finset.univ_inter]
  rw [heq]
  calc
    _ ≤ ∑ k : Fin n, ‖coefficient model β x i k • (projectTangent (x i) (x k).val -
        (if k ∈ C then projectTangent (x i) (x j).val else 0))‖ := norm_sum_le _ _
    _ ≤ ∑ k : Fin n, (2 * δ * coefficient model β x i k + 2 * Real.exp (-β * L)) :=
      Finset.sum_le_sum (fun k _ => hterm k)
    _ = 2 * δ * (∑ k : Fin n, coefficient model β x i k) + 2 * n * Real.exp (-β * L) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (ModelBounds.row_sum_le_one model β hβ x i)
        (show 0 ≤ 2 * δ by positivity)
      linarith only [hh]

theorem row_error (model : Model) (β δ L : ℝ) (hβ : 0 ≤ β) (hδ : 0 ≤ δ)
    (x : Configuration n d) (B C : Block n) (hB : B.Nonempty) (i j : Fin n)
    (hBclose : ∀ k ∈ B, angularDist (x k) (x i) ≤ δ)
    (hCclose : ∀ k ∈ C, angularDist (x k) (x j) ≤ δ)
    (hsep : ∀ k ∉ B, k ∉ C → L ≤ PairDeficit.deficit x i k) :
    ‖vectorField model β x i - ((C.card : ℝ) / blockDenominator model B * kernel β x i j) •
      projectTangent (x i) (x j).val‖ ≤
      2 * δ + 2 * n * Real.exp (-β * L) +
        n * kernel β x i j * (kernelError β δ +
          denominatorError n β δ (kernel β x i j) (Real.exp (-β * L))) *
            ‖projectTangent (x i) (x j).val‖ := by
  have hg := geometric_error model β δ L hβ hδ x B C i j hBclose hCclose hsep
  have hm := ActiveVelocity.cross_mass_error model β δ L hβ hδ x B C hB i j
    (fun k hk => by simpa only [AngularGeometry.angularDist_comm] using hBclose k hk) hCclose hsep
  have heq : vectorField model β x i - ((C.card : ℝ) / blockDenominator model B * kernel β x i j) •
      projectTangent (x i) (x j).val =
      (vectorField model β x i - (∑ k ∈ C, coefficient model β x i k) • projectTangent (x i) (x j).val) +
      ((∑ k ∈ C, coefficient model β x i k) - (C.card : ℝ) / blockDenominator model B * kernel β x i j) •
        projectTangent (x i) (x j).val := by rw [sub_smul]; abel
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add hg (by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hm (norm_nonneg _)))


/-- The explicit SA denominator remainder is uniformly of order beta^(-1/3)
in the mesoscopic range. -/
theorem coefficient_error_bound (β δ K O : ℝ) (hβ : 1 < β) (hδ : 0 ≤ δ)
    (hK : K ≤ β ^ (-(1 / 3 : ℝ)))
    (hsmall : β * δ ≤ β ^ (-(1 / 3 : ℝ)))
    (hH : kernelError β δ ≤ 2 * β ^ (-(1 / 3 : ℝ)))
    (hO : O ≤ β ^ (-(1 / 3 : ℝ))) :
    kernelError β δ + denominatorError n β δ K O ≤ (2 + 5 * n) * β ^ (-(1 / 3 : ℝ)) := by
  have hp : 0 ≤ β ^ (-(1 / 3 : ℝ)) := (Real.rpow_pos_of_pos (zero_lt_one.trans hβ) _).le
  have hp1 : β ^ (-(1 / 3 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hβ.le (by norm_num)
  have hH0 := kernelError_nonneg β δ (zero_lt_one.trans hβ).le hδ
  have hKterm : K * (1 + kernelError β δ) ≤ 3 * β ^ (-(1 / 3 : ℝ)) := by
    have hfactor : 1 + kernelError β δ ≤ 3 := by linarith only [hH, hp1]
    have hh := mul_le_mul hK hfactor (by linarith only [hH0] : 0 ≤ 1 + kernelError β δ) hp
    nlinarith only [hh]
  have hsum := add_le_add (add_le_add hsmall hKterm) hO
  have hh := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  dsimp only [denominatorError]
  nlinarith only [hh, hH]

/-- Acceleration of the actual vector row. The first error retains the tangent
projection norm; the remaining terms have positive exponential gaps. -/
theorem accelerated_row_error (model : Model) (β κ U L F : ℝ) (hβ : 1 < β)
    (x : Configuration n d) (B C : Block n) (hB : B.Nonempty) (i j : Fin n)
    (hBclose : ∀ k ∈ B, angularDist (x k) (x i) ≤ Real.exp (-κ * β))
    (hCclose : ∀ k ∈ C, angularDist (x k) (x j) ≤ Real.exp (-κ * β))
    (hsep : ∀ k ∉ B, k ∉ C → L ≤ PairDeficit.deficit x i k)
    (hF0 : 0 ≤ F) (hFU : F ≤ 2 * Real.log β * Real.exp (β * U))
    (hCF : |kernel β x i j * F - Real.log β| ≤ Real.log β * β ^ (-(1 / 3 : ℝ)))
    (hcoef : kernelError β (Real.exp (-κ * β)) +
      denominatorError n β (Real.exp (-κ * β)) (kernel β x i j) (Real.exp (-β * L)) ≤
        (2 + 5 * n) * β ^ (-(1 / 3 : ℝ))) :
    ‖F • vectorField model β x i -
      (((C.card : ℝ) / blockDenominator model B) * Real.log β) • projectTangent (x i) (x j).val‖ ≤
      (5 * n + 10 * (n : ℝ) ^ 2) * β ^ (-(1 / 3 : ℝ)) * Real.log β *
        ‖projectTangent (x i) (x j).val‖ +
      4 * Real.log β * (Real.exp (-(κ - U) * β) + n * Real.exp (-(L - U) * β)) := by
  let α : ℝ := (C.card : ℝ) / blockDenominator model B
  let P := projectTangent (x i) (x j).val
  let p := β ^ (-(1 / 3 : ℝ))
  have hp : 0 ≤ p := (Real.rpow_pos_of_pos (zero_lt_one.trans hβ) _).le
  have hp1 : p ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hβ.le (by norm_num)
  have hlog := (Real.log_pos hβ).le
  have hk := (Real.exp_pos (β * (⟪(x i).val, (x j).val⟫ - 1))).le
  have hα0 : 0 ≤ α := div_nonneg (Nat.cast_nonneg _) ((blockDenominator_ge_one model B hB).trans' zero_le_one)
  have hαn : α ≤ n := (div_le_self (Nat.cast_nonneg C.card) (blockDenominator_ge_one model B hB)).trans
    (by exact_mod_cast TreeDynamics.block_card_le C)
  have hKF : kernel β x i j * F ≤ 2 * Real.log β := by
    have hh := (abs_le.mp hCF).2
    have hh' := mul_le_mul_of_nonneg_left hp1 hlog
    dsimp only [p] at hh'
    linarith only [hh, hh']
  have hraw := row_error model β (Real.exp (-κ * β)) L (zero_lt_one.trans hβ).le
    (Real.exp_pos _).le x B C hB i j hBclose hCclose hsep
  have heq : F • vectorField model β x i - (α * Real.log β) • P =
      F • (vectorField model β x i - (α * kernel β x i j) • P) +
        (α * (kernel β x i j * F - Real.log β)) • P := by
    simp only [smul_sub, sub_smul, mul_smul]
    module
  rw [heq]
  have hN := norm_nonneg P
  have herr := mul_le_mul_of_nonneg_left hraw hF0
  have hprod := mul_le_mul_of_nonneg_left hcoef
    (show 0 ≤ n * (kernel β x i j * F) by positivity)
  have hprod' := mul_le_mul_of_nonneg_right hKF
    (show 0 ≤ (n : ℝ) * (2 + 5 * n) * p by positivity)
  have hterm : F * (n * kernel β x i j * (kernelError β (Real.exp (-κ * β)) +
      denominatorError n β (Real.exp (-κ * β)) (kernel β x i j) (Real.exp (-β * L)))) ≤
      2 * n * (2 + 5 * n) * p * Real.log β := by
    dsimp only [p] at *
    nlinarith only [hprod, hprod']
  have hterm' := mul_le_mul_of_nonneg_right hterm hN
  have hclockerr := mul_le_mul_of_nonneg_left hCF hα0
  have hclockerr' := mul_le_mul_of_nonneg_right hαn (mul_nonneg hlog hp)
  have hclockP : |α * (kernel β x i j * F - Real.log β)| * ‖P‖ ≤ n * p * Real.log β * ‖P‖ := by
    rw [abs_mul, abs_of_nonneg hα0]
    have hh : α * |kernel β x i j * F - Real.log β| ≤ n * p * Real.log β := by
      dsimp only [p] at *
      nlinarith only [hclockerr, hclockerr']
    exact mul_le_mul_of_nonneg_right hh hN
  have hrem := mul_le_mul_of_nonneg_right hFU
    (show 0 ≤ 2 * Real.exp (-κ * β) + 2 * n * Real.exp (-β * L) by positivity)
  have hexpκ : Real.exp (β * U) * Real.exp (-κ * β) = Real.exp (-(κ - U) * β) := by
    rw [← Real.exp_add]; congr 1; ring
  have hexpL : Real.exp (β * U) * Real.exp (-β * L) = Real.exp (-(L - U) * β) := by
    rw [← Real.exp_add]; congr 1; ring
  have hrem' : F * (2 * Real.exp (-κ * β) + 2 * n * Real.exp (-β * L)) ≤
      4 * Real.log β * (Real.exp (-(κ - U) * β) + n * Real.exp (-(L - U) * β)) := by
    calc
      _ ≤ (2 * Real.log β * Real.exp (β * U)) *
          (2 * Real.exp (-κ * β) + 2 * n * Real.exp (-β * L)) := hrem
      _ = 4 * Real.log β * (Real.exp (β * U) * Real.exp (-κ * β) +
          n * (Real.exp (β * U) * Real.exp (-β * L))) := by ring
      _ = _ := by rw [hexpκ, hexpL]
  calc
    _ ≤ ‖F • (vectorField model β x i - (α * kernel β x i j) • P)‖ +
        ‖(α * (kernel β x i j * F - Real.log β)) • P‖ := norm_add_le _ _
    _ ≤ _ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hF0]
      dsimp only [α, P, p] at *
      nlinarith only [herr, hterm', hclockP, hrem']


/-- Cancellation of the literal exponential kernel against the active clock. -/
theorem kernel_clock_error (β F : ℝ) (hβ : 1 < β) (x : Configuration n d) (i j : Fin n)
    (hclock : |F / (Real.log β * Real.exp (β * (1 - ⟪(x i).val, (x j).val⟫))) - 1| ≤
      β ^ (-(1 / 3 : ℝ))) :
    |kernel β x i j * F - Real.log β| ≤ Real.log β * β ^ (-(1 / 3 : ℝ)) := by
  have hlog := Real.log_pos hβ
  have hz : kernel β x i j * Real.exp (β * (1 - ⟪(x i).val, (x j).val⟫)) = 1 := by
    rw [kernel, ← Real.exp_add]
    convert Real.exp_zero using 1
    congr 1
    ring
  have hratio : F / (Real.log β * Real.exp (β * (1 - ⟪(x i).val, (x j).val⟫))) - 1 =
      (kernel β x i j * F - Real.log β) / Real.log β := by
    field_simp
    have hzf := congrArg (fun z => F * z) hz
    nlinarith only [hzf]
  rw [hratio, abs_div, abs_of_pos hlog] at hclock
  have hh := (div_le_iff₀ hlog).mp hclock
  simpa only [mul_comm] using hh

/-- Source vector estimates for both active representatives. The beta threshold
precedes the stage, multiplier, configuration, model, and representatives. -/
theorem static_reduced_pair (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) (κ : ℝ) (hκ : 4 < κ) :
    ∃ β₀ : ℝ, 1 < β₀ ∧ ∀ β ≥ β₀,
      ∀ M ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 5), ∀ (model : Model) (l : Fin N)
      (x : Configuration n d), StageHyp T C β κ M l x →
      ∀ i j : Fin n, i ∈ T.left l → j ∈ T.right l →
      1 - ⟪(x i).val, (x j).val⟫ ≤ upperBarrier C l + 2 * treeMargin hN C →
      mesoscopicScale β ≤ angularDist (x i) (x j) →
      let U := upperBarrier C l + 2 * treeMargin hN C
      let L := upperBarrier C l + 7 * treeMargin hN C
      let R := 4 * Real.log β * (Real.exp (-(κ - U) * β) + n * Real.exp (-(L - U) * β))
      let E := (5 * n + 10 * (n : ℝ) ^ 2) * β ^ (-(1 / 3 : ℝ)) * Real.log β
      (‖clockFactor β x • vectorField model β x i -
        (((T.right l).card : ℝ) / blockDenominator model (T.left l) * Real.log β) •
          projectTangent (x i) (x j).val‖ ≤ E * ‖projectTangent (x i) (x j).val‖ + R) ∧
      (‖clockFactor β x • vectorField model β x j -
        (((T.left l).card : ℝ) / blockDenominator model (T.right l) * Real.log β) •
          projectTangent (x j) (x i).val‖ ≤ E * ‖projectTangent (x j) (x i).val‖ + R) := by
  have hκ0 : 0 < κ := by linarith only [hκ]
  have hparameters : ∀ᶠ β : ℝ in atTop, ∀ l : Fin N,
      1 < β ∧ 1 ≤ Real.log β ∧ mesoscopicScale β ≤ 1 ∧
      β * Real.exp (-κ * β) ≤ β ^ (-(1 / 3 : ℝ)) ∧
      kernelError β (Real.exp (-κ * β)) ≤ 2 * β ^ (-(1 / 3 : ℝ)) ∧
      Real.exp (-β * (upperBarrier C l + 7 * treeMargin hN C)) ≤ β ^ (-(1 / 3 : ℝ)) := by
    apply eventually_all.mpr
    intro l
    obtain ⟨_, hκU, hUL, hL, _⟩ := source_barrier_parameters T hN C hC κ hκ l
    filter_upwards [ActiveVelocityScale.eventually_parameters κ
      (upperBarrier C l + 2 * treeMargin hN C) (upperBarrier C l + 7 * treeMargin hN C)
      1 hκ0 hκU hUL hL (by norm_num)] with β h
    refine ⟨h.1, h.2.1, h.2.2.1, ?_, ?_, ?_⟩
    · simpa only [neg_div] using h.2.2.2.1
    · simpa only [neg_div] using h.2.2.2.2.1
    · simpa only [neg_div] using h.2.2.2.2.2.1
  obtain ⟨V, hV⟩ := eventually_atTop.mp hparameters
  obtain ⟨G, hG, hgeometry⟩ := ActiveGeometry.stage_barriers T hN C hC
  obtain ⟨B, hB, hclock⟩ := ActiveClock.active_clock T hN C hC κ hκ0
  refine ⟨max B (max G V), hB.trans_le (le_max_left _ _), ?_⟩
  intro β hβ M hM model l x hstage i j hi hj hupper hangle
  have hβB := (le_max_left B (max G V)).trans hβ
  have hβG := (le_max_left G V).trans ((le_max_right B (max G V)).trans hβ)
  have hβV := (le_max_right G V).trans ((le_max_right B (max G V)).trans hβ)
  obtain ⟨hβ1, _, hmeso, hδ, hH, hO⟩ := hV β hβV l
  have hc := (hclock β hβB M hM l x hstage.1 hstage.2.1 hstage.2.2 i j hi hj hupper hangle).2.2
  have hCF := kernel_clock_error β (clockFactor β x) hβ1 x i j hc
  have hlog := Real.log_pos hβ1
  have hF0 : 0 ≤ clockFactor β x :=
    (le_min zero_le_one hlog.le).trans (GeneralClock.clockFactor_bounds β hβ1 x).1
  have hp1 : β ^ (-(1 / 3 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hβ1.le (by norm_num)
  have hden : 0 < Real.log β * Real.exp (β * (1 - ⟪(x i).val, (x j).val⟫)) := by positivity
  have hratio : clockFactor β x / (Real.log β * Real.exp (β * (1 - ⟪(x i).val, (x j).val⟫))) ≤ 2 := by
    linarith only [(abs_le.mp hc).2, hp1]
  have hF := (div_le_iff₀ hden).mp hratio
  have hExp := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hupper (zero_lt_one.trans hβ1).le)
  have hF' := mul_le_mul_of_nonneg_left hExp (show 0 ≤ 2 * Real.log β by positivity)
  have hFU : clockFactor β x ≤ 2 * Real.log β *
      Real.exp (β * (upperBarrier C l + 2 * treeMargin hN C)) := by nlinarith only [hF, hF']
  have hK : kernel β x i j ≤ β ^ (-(1 / 3 : ℝ)) := by
    simpa only [kernel, neg_div] using
      ActiveAngleScale.kernel_le_third_power β hβ1 hmeso (x i) (x j) hangle
  have hcoef := coefficient_error_bound (n := n) β (Real.exp (-κ * β)) (kernel β x i j)
    (Real.exp (-β * (upperBarrier C l + 7 * treeMargin hN C))) hβ1 (Real.exp_pos _).le
    hK hδ hH hO
  have hext := (hgeometry β hβG M hM l x hstage.2.1 hstage.2.2).1
  constructor
  · exact accelerated_row_error model β κ _ _ _ hβ1 x (T.left l) (T.right l)
      (T.block_nonempty _ _ (T.left_mem l)) i j
      (fun k hk => hstage.1 _ (T.left_mem l) k hk i hi)
      (fun k hk => hstage.1 _ (T.right_mem l) k hk j hj)
      (fun k hkB hkC => hext i (Finset.mem_union_left _ hi) k (by
        simpa only [CollisionTree.parent, Finset.mem_union, not_or] using And.intro hkB hkC))
      hF0 hFU hCF hcoef
  · apply accelerated_row_error model β κ _ _ _ hβ1 x (T.right l) (T.left l)
      (T.block_nonempty _ _ (T.right_mem l)) j i
      (fun k hk => hstage.1 _ (T.right_mem l) k hk j hj)
      (fun k hk => hstage.1 _ (T.left_mem l) k hk i hi)
      (fun k hkC hkB => hext j (Finset.mem_union_right _ hj) k (by
        simpa only [CollisionTree.parent, Finset.mem_union, not_or] using And.intro hkB hkC)) hF0 hFU
    · simpa only [kernel_comm β x j i] using hCF
    · simpa only [kernel_comm β x j i] using hcoef

end Metastability.ActiveVectorLaw
