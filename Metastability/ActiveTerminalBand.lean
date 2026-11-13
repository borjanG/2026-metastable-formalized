import Metastability.ActiveTerminalAsymptotics

/-! The slightly enlarged terminal band used to rule out an upward exit. -/
noncomputable section
open Filter Set
open scoped Topology BigOperators RealInnerProductSpace
namespace Metastability.ActiveTerminalBand
open Source ActiveCoefficients ActiveVelocity ActiveScales ActiveTerminalAsymptotics
variable {n d : ℕ}

theorem terminal_signal_lower_doubled (β : ℝ) (hβ : 1 < β)
    (hsmall : 2 * mesoscopicScale β ≤ 1)
    (x : Configuration n d) (i j : Fin n)
    (hlower : clockCutoff β / 2 ≤ angularDist (x i) (x j))
    (hupper : angularDist (x i) (x j) ≤ 2 * mesoscopicScale β) :
    1 / (256 * β ^ 4) ≤ sineSquare x i j * kernel β x i j := by
  have hβ0 : 0 < β := zero_lt_one.trans hβ
  have hlog : 0 ≤ Real.log β := (Real.log_pos hβ).le
  have hθ0 := AngularGeometry.angularDist_nonneg (x i) (x j)
  have hθ1 : angularDist (x i) (x j) ≤ 1 := hupper.trans hsmall
  have hθlo : 1 / (8 * β) ≤ angularDist (x i) (x j) := by
    have hh := div_le_div_of_nonneg_right (inv_four_beta_le_clockCutoff hβ) (by norm_num : (0 : ℝ) ≤ 2)
    have he : (1 / (4 * β)) / 2 = 1 / (8 * β) := by ring
    rw [he] at hh
    exact hh.trans hlower
  have hqlo := ContractionScale.angularDist_sq_le_four_mul_deficit x i j hθ1
  have hqhi := KernelComparison.one_sub_inner_le_sq_half_of_angle_le (x i) (x j) 1 hθ1
  have hr0 : 0 ≤ ⟪(x i).val, (x j).val⟫ := by norm_num at hqhi; linarith only [hqhi]
  have hrs := ModelBounds.inner_bounds (x i) (x j)
  have hsin : PairDeficit.deficit x i j ≤ sineSquare x i j := by
    dsimp only [PairDeficit.deficit, sineSquare]
    nlinarith only [hr0, hrs.2]
  have hsquare := pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 / (8 * β) by positivity) hθlo 2
  have hlo : 1 / (256 * β ^ 2) ≤ sineSquare x i j := by
    have he : (1 / (8 * β)) ^ 2 = 4 * (1 / (256 * β ^ 2)) := by field_simp; ring
    rw [he] at hsquare
    linarith only [hsquare, hqlo, hsin]
  have hqmeso := KernelComparison.one_sub_inner_le_sq_half_of_angle_le (x i) (x j)
    (2 * mesoscopicScale β) hupper
  rw [mul_pow, mesoscopicScale_sq hβ] at hqmeso
  have hβq := mul_le_mul_of_nonneg_left hqmeso hβ0.le
  have hcancel : β * ((2 : ℝ) ^ 2 * (Real.log β / β) / 2) = 2 * Real.log β := by field_simp
  rw [hcancel] at hβq
  have hexponent : -(2 * Real.log β) ≤ β * (⟪(x i).val, (x j).val⟫ - 1) := by
    nlinarith only [hβq, hlog]
  have hkernel : 1 / β ^ 2 ≤ kernel β x i j := by
    calc
      1 / β ^ 2 = Real.exp (-(2 * Real.log β)) := by
        rw [Real.exp_neg, two_mul, Real.exp_add, Real.exp_log hβ0]
        simp only [one_div, pow_two]
      _ ≤ _ := Real.exp_le_exp.mpr hexponent
  have hmul := mul_le_mul hlo hkernel (by positivity : (0 : ℝ) ≤ 1 / β ^ 2)
    (sineSquare_nonneg x i j)
  have he : (1 / (256 * β ^ 2)) * (1 / β ^ 2) = 1 / (256 * β ^ 4) := by field_simp
  rw [he] at hmul
  exact hmul

theorem tendsto_terminal_error_doubled (n : ℕ) (κ L : ℝ) (hκ : 0 < κ) (hL : 0 < L) :
    Tendsto (fun β : ℝ => β ^ 4 * (4 * Real.exp (-κ * β) + 4 * n * Real.exp (-β * L)))
      atTop (𝓝 0) := by
  have hκ' : Tendsto (fun β : ℝ => β ^ 4 * Real.exp (-κ * β)) atTop (𝓝 0) := by
    simpa only [Real.rpow_ofNat] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 4 κ hκ
  have hL' : Tendsto (fun β : ℝ => β ^ 4 * Real.exp (-L * β)) atTop (𝓝 0) := by
    simpa only [Real.rpow_ofNat] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 4 L hL
  convert (hκ'.const_mul 4).add (hL'.const_mul (4 * (n : ℝ))) using 1
  · ext β
    rw [show -β * L = -L * β by ring]
    ring
  · norm_num

/-- The complete static terminal-window estimate, with its numerical error
conditions derived rather than assumed. The threshold precedes all geometry. -/
theorem eventually_terminal_comparable_doubled (n : ℕ) (hn : 0 < n) (κ L : ℝ)
    (hκ : 0 < κ) (hL : 0 < L) :
    ∀ᶠ β : ℝ in atTop, 1 < β ∧
      ∀ (d : ℕ) (model : Model) (x : Configuration n d) (B C : Block n),
      B.Nonempty → C.Nonempty → ∀ (i j : Fin n),
      (∀ k ∈ B, angularDist (x k) (x i) ≤ Real.exp (-κ * β)) →
      (∀ k ∈ C, angularDist (x k) (x j) ≤ Real.exp (-κ * β)) →
      (∀ k ∉ B, k ∉ C → L ≤ PairDeficit.deficit x i k) →
      (∀ k ∉ C, k ∉ B → L ≤ PairDeficit.deficit x j k) →
      clockCutoff β / 2 ≤ angularDist (x i) (x j) →
      angularDist (x i) (x j) ≤ 2 * mesoscopicScale β →
      (sineSquare x i j * kernel β x i j) / (2 * n) ≤
          -PairDeficit.velocity model β x i j ∧
        -PairDeficit.velocity model β x i j ≤
          (4 * n + 1) * (sineSquare x i j * kernel β x i j) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hH := (tendsto_kernelError_exp κ hκ).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hE := (tendsto_terminal_error_doubled n κ L hκ hL).eventually
    (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / (512 * n)))
  have hm := tendsto_mesoscopicScale.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [eventually_gt_atTop (1 : ℝ), hH, hE, hm] with β hβ hHβ hEβ hmβ
  refine ⟨hβ, ?_⟩
  intro d model x B C hB hC i j hBclose hCclose hsepB hsepC hlower hupper
  have hβ0 : 0 < β := zero_lt_one.trans hβ
  have hlo := terminal_signal_lower_doubled β hβ (by linarith only [hmβ]) x i j hlower hupper
  have hE' : 4 * Real.exp (-κ * β) + 4 * n * Real.exp (-β * L) ≤
      (1 / (256 * β ^ 4)) / (2 * n) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) hn0)).mpr
    have h := (le_div_iff₀ (pow_pos hβ0 4)).mpr (by
      simpa only [mul_comm (β ^ 4)] using hEβ.le)
    have he : (1 / (512 * (n : ℝ))) / β ^ 4 = (1 / (256 * β ^ 4)) / (2 * n) := by field_simp; ring
    rw [he] at h
    exact (le_div_iff₀ (mul_pos (by norm_num) hn0)).mp h
  exact ActiveTerminalVelocity.correlation_comparable model β (Real.exp (-κ * β)) L
    hβ0.le (Real.exp_pos _).le hHβ.le x B C hB hC i j hBclose hCclose hsepB hsepC
    (hE'.trans (div_le_div_of_nonneg_right hlo (by positivity)))

end Metastability.ActiveTerminalBand
