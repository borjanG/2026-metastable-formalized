import Metastability.ActiveAngleScale
import Metastability.ActiveScales
import Metastability.CapEnlargement

/-! A uniform strict cosine margin for plateau caps, including zero-radius caps. -/

noncomputable section
open Filter Set
open scoped Topology

namespace Metastability.PlateauCapScale
open Source CapEnlargement
variable {n N d : ℕ}

theorem cosine_gap_lower (r γ : ℝ) (hr : 0 ≤ r) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hR : r + γ ≤ Real.pi / 2) :
    (2 / 5 : ℝ) * γ ^ 2 ≤ Real.cos r - Real.cos (r + γ) := by
  have hsin := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi / 2) ≤ γ / 2 by linarith only [hγ, Real.pi_pos])
    (show (r + (r + γ)) / 2 ≤ Real.pi / 2 by linarith only [hR, hγ])
    (show γ / 2 ≤ (r + (r + γ)) / 2 by linarith only [hr])
  have hsin0 : 0 ≤ Real.sin (γ / 2) := Real.sin_nonneg_of_nonneg_of_le_pi
    (by positivity) (by linarith only [hR, hr, Real.pi_pos])
  have hmul := mul_le_mul_of_nonneg_right hsin hsin0
  have hhalf := Real.sin_sq_eq_half_sub (γ / 2)
  rw [show 2 * (γ / 2) = γ by ring] at hhalf
  have hsmall := ActiveAngleScale.two_fifths_sq_le_deficit hγ hγ1
  rw [Real.cos_sub_cos, show (r - (r + γ)) / 2 = -(γ / 2) by ring, Real.sin_neg]
  nlinarith only [hmul, hhalf, hsmall]

theorem eventually_cap_error (n : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ β : ℝ in atTop, 1 < β ∧ enlargementScale β ≤ 1 ∧
      8 * n * (n + 1) * Real.log β * Real.exp (-5 * δ * β) ≤
        (1 / 5 : ℝ) * enlargementScale β ^ 2 := by
  have he := ActiveScales.eventually_mul_exp_le_rpow
    (5 * (8 * n * (n + 1))) (5 * δ) 1 (-(1 / 2 : ℝ)) (by positivity)
  have hm := tendsto_enlargementScale.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [eventually_gt_atTop (1 : ℝ), he, hm] with β hβ heβ hmβ
  have hβ0 := zero_lt_one.trans hβ
  have hlogle : Real.log β ≤ β := (Real.log_le_sub_one_of_pos hβ0).trans (by linarith)
  have heq : enlargementScale β ^ 2 = β ^ (-(1 / 2 : ℝ)) := by
    rw [enlargementScale, ← Real.rpow_mul_natCast hβ0.le]
    congr 1
    norm_num
  simp only [Real.rpow_one] at heβ
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hlogle (show 0 ≤ 5 * (8 * (n : ℝ) * (n + 1)) by positivity))
    (Real.exp_pos (-5 * δ * β)).le
  rw [heq]
  refine ⟨hβ, hmβ.le, ?_⟩
  have heexp : -(5 * δ) * β = -5 * δ * β := by ring
  rw [heexp] at heβ
  nlinarith only [heβ, hmul]

end Metastability.PlateauCapScale
