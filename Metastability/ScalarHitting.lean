import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite threshold crossing for the two-particle original-time scalar equation

This is an internal scalar lemma. Its differential equation is an input here;
`TwoParticle.hasDerivAt_inner_of_fullUSA` derives that equation from the vector
system. No threshold-hitting assumption is made.
-/

noncomputable section

open Set

namespace Metastability.ScalarHitting

theorem scalar_rhs_nonneg (β q : ℝ) (hq : q ∈ Icc (-1 : ℝ) 1) :
    0 ≤ (1 - q ^ 2) * Real.exp (β * (q - 1)) := by
  have hsq : q ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one q).mpr (abs_le.mpr hq)
  exact mul_nonneg (sub_nonneg.mpr hsq) (Real.exp_pos _).le

/-- A uniform positive lower bound while the scalar product stays between its
initial value and a fixed target strictly below one. -/
theorem scalar_rhs_lower_bound (β q₀ r q : ℝ) (hβ : 0 < β)
    (hq₀ : -1 < q₀) (hr : r < 1) (hlo : q₀ ≤ q) (hhi : q ≤ r) :
    (1 - r) * (1 + q₀) * Real.exp (-2 * β) ≤
      (1 - q ^ 2) * Real.exp (β * (q - 1)) := by
  have hleft : 0 ≤ 1 - q := by linarith only [hhi, hr]
  have hright : 0 ≤ 1 + q := by linarith only [hlo, hq₀]
  have hprod : (1 - r) * (1 + q₀) ≤ (1 - q) * (1 + q) := by
    apply mul_le_mul
    · linarith only [hhi]
    · linarith only [hlo]
    · linarith only [hq₀]
    · exact hleft
  have hexp : Real.exp (-2 * β) ≤ Real.exp (β * (q - 1)) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [hβ, hq₀, hlo]
  calc
    _ ≤ ((1 - q) * (1 + q)) * Real.exp (β * (q - 1)) :=
      mul_le_mul hprod hexp (Real.exp_pos _).le (mul_nonneg hleft hright)
    _ = (1 - q ^ 2) * Real.exp (β * (q - 1)) := by ring

/-- The scalar equation makes the scalar product nondecreasing on nonnegative
original times, including the initial endpoint. -/
theorem monotoneOn_of_scalarODE (β : ℝ) (ρ : ℝ → ℝ)
    (hc : ContinuousOn ρ (Ici 0))
    (hd : ∀ u, 0 < u →
      HasDerivAt ρ ((1 - (ρ u) ^ 2) * Real.exp (β * (ρ u - 1))) u)
    (hb : ∀ u, 0 ≤ u → ρ u ∈ Icc (-1 : ℝ) 1) :
    MonotoneOn ρ (Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hc
  · intro u hu
    have hu' : 0 < u := by simpa only [interior_Ici, mem_Ioi] using hu
    exact (hd u hu').differentiableAt.differentiableWithinAt
  · intro u hu
    have hu' : 0 < u := by simpa only [interior_Ici, mem_Ioi] using hu
    rw [(hd u hu').deriv]
    exact scalar_rhs_nonneg β (ρ u) (hb u hu'.le)

/-- Every target strictly between the initial scalar product and one is reached
at a finite positive first time. The scalar product is strictly below the target
before that time and is at least the target afterwards. -/
theorem exists_first_hit (β r : ℝ) (ρ : ℝ → ℝ) (hβ : 0 < β)
    (hc : ContinuousOn ρ (Ici 0))
    (hd : ∀ u, 0 < u →
      HasDerivAt ρ ((1 - (ρ u) ^ 2) * Real.exp (β * (ρ u - 1))) u)
    (hb : ∀ u, 0 ≤ u → ρ u ∈ Icc (-1 : ℝ) 1)
    (hρ₀ : -1 < ρ 0) (hinitial : ρ 0 < r) (hr : r < 1) :
    ∃ U : ℝ, 0 < U ∧ ρ U = r ∧
      (∀ u : ℝ, 0 ≤ u → u < U → ρ u < r) ∧
      (∀ u : ℝ, U ≤ u → r ≤ ρ u) := by
  have hmono := monotoneOn_of_scalarODE β ρ hc hd hb
  let c := (1 - r) * (1 + ρ 0) * Real.exp (-2 * β)
  have hcpos : 0 < c := by
    dsimp [c]
    exact mul_pos (mul_pos (sub_pos.mpr hr) (by linarith only [hρ₀])) (Real.exp_pos _)
  let T := (2 - ρ 0) / c
  have hT : 0 < T := by
    exact div_pos (by linarith only [hinitial, hr]) hcpos
  have hcross : r ≤ ρ T := by
    by_contra hcross
    have hbelow : ρ T < r := lt_of_not_ge hcross
    have hcI : ContinuousOn ρ (Icc 0 T) := hc.mono (fun _ hu => hu.1)
    have hdI : DifferentiableOn ℝ ρ (interior (Icc 0 T)) := by
      intro u hu
      have hu' : u ∈ Ioo 0 T := by simpa only [interior_Icc] using hu
      exact (hd u hu'.1).differentiableAt.differentiableWithinAt
    have hlower : ∀ u ∈ interior (Icc 0 T), c ≤ deriv ρ u := by
      intro u hu
      have hu' : u ∈ Ioo 0 T := by simpa only [interior_Icc] using hu
      rw [(hd u hu'.1).deriv]
      exact scalar_rhs_lower_bound β (ρ 0) r (ρ u) hβ hρ₀ hr
        (hmono (show 0 ∈ Ici (0 : ℝ) from le_refl (0 : ℝ)) hu'.1.le hu'.1.le)
        ((hmono hu'.1.le hT.le hu'.2.le).trans hbelow.le)
    have hgrowth := (convex_Icc (0 : ℝ) T).mul_sub_le_image_sub_of_le_deriv hcI hdI hlower
      0 ⟨le_rfl, hT.le⟩ T ⟨hT.le, le_rfl⟩ hT.le
    have hcT : c * T = 2 - ρ 0 := by
      dsimp [T]
      rw [mul_div_cancel₀ _ hcpos.ne']
    rw [sub_zero, hcT] at hgrowth
    have hub := (hb T hT.le).2
    linarith only [hgrowth, hub]
  obtain ⟨U, hU, hρU⟩ :=
    intermediate_value_Icc hT.le (hc.mono (fun _ hu => hu.1))
      (show r ∈ Icc (ρ 0) (ρ T) from ⟨hinitial.le, hcross⟩)
  have hUpos : 0 < U := by
    apply lt_of_le_of_ne hU.1
    intro heq
    have : ρ 0 = r := by simpa only [← heq] using hρU
    exact hinitial.ne this
  have hstrict : StrictMonoOn ρ (Icc 0 U) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) U)
      (hc.mono (fun _ hu => hu.1))
    intro u hu
    have hu' : u ∈ Ioo 0 U := by simpa only [interior_Icc] using hu
    rw [(hd u hu'.1).deriv]
    apply hcpos.trans_le
    apply scalar_rhs_lower_bound β (ρ 0) r (ρ u) hβ hρ₀ hr
    · exact hmono (show 0 ∈ Ici (0 : ℝ) from le_refl (0 : ℝ)) hu'.1.le hu'.1.le
    · rw [← hρU]
      exact hmono hu'.1.le hUpos.le hu'.2.le
  refine ⟨U, hUpos, hρU, ?_, ?_⟩
  · intro u hu huU
    rw [← hρU]
    exact hstrict ⟨hu, huU.le⟩ ⟨hUpos.le, le_rfl⟩ huU
  · intro u hUu
    rw [← hρU]
    exact hmono hUpos.le (hUpos.le.trans hUu) hUu

end Metastability.ScalarHitting
