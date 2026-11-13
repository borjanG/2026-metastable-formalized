import Metastability.ModelBounds
import Metastability.AngularGeometry
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Quantitative energy estimates from particle geometry

These static estimates are the final energy assembly tools. Within-block
closeness and cross-block separation remain geometric inputs to these helpers;
the cascade must establish them from the ODE before using these results.
-/

noncomputable section
open Set Filter
open scoped BigOperators RealInnerProductSpace Topology
namespace Metastability.EnergyEstimates
variable {n d : ℕ}

theorem interaction_bounds (β : ℝ) (hβ : 0 ≤ β) (x y : Source.Sphere d) :
    0 ≤ Real.exp (β * (⟪x.val, y.val⟫ - 1)) ∧
      Real.exp (β * (⟪x.val, y.val⟫ - 1)) ≤ 1 := by
  refine ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr ?_⟩
  exact mul_nonpos_of_nonneg_of_nonpos hβ (sub_nonpos.mpr (ModelBounds.inner_bounds x y).2)

theorem interaction_deficit_le (β : ℝ) (hβ : 0 ≤ β) (x y : Source.Sphere d)
    (ε : ℝ) (hclose : 1 - ⟪x.val, y.val⟫ ≤ ε) :
    |Real.exp (β * (⟪x.val, y.val⟫ - 1)) - 1| ≤ β * ε := by
  rw [abs_of_nonpos (sub_nonpos.mpr (interaction_bounds β hβ x y).2)]
  have he := Real.add_one_le_exp (β * (⟪x.val, y.val⟫ - 1))
  nlinarith

theorem interaction_cross_le (β : ℝ) (hβ : 0 ≤ β) (x y : Source.Sphere d)
    (L : ℝ) (hsep : L ≤ 1 - ⟪x.val, y.val⟫) :
    Real.exp (β * (⟪x.val, y.val⟫ - 1)) ≤ Real.exp (-β * L) := by
  apply Real.exp_le_exp.mpr
  nlinarith

/-- The normalized count of ordered pairs carrying the same block label. -/
def pairPlateau {α : Type*} [DecidableEq α] (p : Fin n → α) : ℝ :=
  (∑ i, ∑ j, if p i = p j then (1 : ℝ) else 0) / (n : ℝ) ^ 2

/-- If each within-block correlation deficit is at most epsilon and every
cross-block barrier is at least L, the entire normalized energy has this error. -/
theorem energy_sub_pairPlateau_le {α : Type*} [DecidableEq α]
    (hn : 0 < n) (β ε L : ℝ) (hβ : 0 ≤ β) (hε : 0 ≤ ε)
    (x : Source.Configuration n d) (p : Fin n → α)
    (hwithin : ∀ i j, p i = p j → 1 - ⟪(x i).val, (x j).val⟫ ≤ ε)
    (hcross : ∀ i j, p i ≠ p j → L ≤ 1 - ⟪(x i).val, (x j).val⟫) :
    |Source.energy β x - pairPlateau p| ≤ β * ε + Real.exp (-β * L) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := sq_pos_of_pos hn'
  have hterm : ∀ i j : Fin n,
      |Real.exp (β * (⟪(x i).val, (x j).val⟫ - 1)) - (if p i = p j then 1 else 0)|
        ≤ β * ε + Real.exp (-β * L) := by
    intro i j
    by_cases hij : p i = p j
    · rw [if_pos hij]
      exact (interaction_deficit_le β hβ (x i) (x j) ε (hwithin i j hij)).trans
        (le_add_of_nonneg_right (Real.exp_pos _).le)
    · rw [if_neg hij, sub_zero, abs_of_nonneg (Real.exp_pos _).le]
      exact (interaction_cross_le β hβ (x i) (x j) L (hcross i j hij)).trans
        (le_add_of_nonneg_left (mul_nonneg hβ hε))
  unfold Source.energy pairPlateau
  rw [← sub_div, abs_div, abs_of_pos hn2]
  apply (div_le_iff₀ hn2).mpr
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  calc
    |∑ i, ∑ j, (Real.exp (β * (⟪(x i).val, (x j).val⟫ - 1)) -
        (if p i = p j then 1 else 0))| ≤
      ∑ i, ∑ j, |Real.exp (β * (⟪(x i).val, (x j).val⟫ - 1)) -
        (if p i = p j then 1 else 0)| := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ _ : Fin n, ∑ _ : Fin n, (β * ε + Real.exp (-β * L)) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
    _ = (β * ε + Real.exp (-β * L)) * (n : ℝ) ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

theorem energy_nonneg (hn : 0 < n) (β : ℝ) (x : Source.Configuration n d) :
    0 ≤ Source.energy β x := by
  unfold Source.energy
  positivity

theorem energy_le_one (hn : 0 < n) (β : ℝ) (hβ : 0 ≤ β)
    (x : Source.Configuration n d) : Source.energy β x ≤ 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold Source.energy
  apply (div_le_iff₀ (sq_pos_of_pos hn')).mpr
  calc
    ∑ i, ∑ j, Real.exp (β * (⟪(x i).val, (x j).val⟫ - 1)) ≤
        ∑ _ : Fin n, ∑ _ : Fin n, (1 : ℝ) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => (interaction_bounds β hβ _ _).2))
    _ = 1 * (n : ℝ) ^ 2 := by simp; ring

/-- Uniform diameter control is sufficient for the final plateau, with an
explicit error valid for any number of particles. -/
theorem one_sub_energy_le_diameter (hn : 0 < n) (β R : ℝ) (hβ : 0 ≤ β) (hR : 0 ≤ R)
    (x : Source.Configuration n d)
    (hdiam : ∀ i j, Source.angularDist (x i) (x j) ≤ R) :
    0 ≤ 1 - Source.energy β x ∧ 1 - Source.energy β x ≤ β * R ^ 2 / 2 := by
  refine ⟨sub_nonneg.mpr (energy_le_one hn β hβ x), ?_⟩
  have hterm : ∀ i j : Fin n, 1 - Real.exp (β * (⟪(x i).val, (x j).val⟫ - 1)) ≤ β * R ^ 2 / 2 := by
    intro i j
    have hcos : 1 - Source.angularDist (x i) (x j) ^ 2 / 2 ≤
        ⟪(x i).val, (x j).val⟫ := by
      rw [← AngularGeometry.cos_angularDist]
      exact Real.one_sub_sq_div_two_le_cos
    have hd := hdiam i j
    have ha := AngularGeometry.angularDist_nonneg (x i) (x j)
    have hh : 1 - ⟪(x i).val, (x j).val⟫ ≤ R ^ 2 / 2 := by nlinarith
    have he := interaction_deficit_le β hβ (x i) (x j) (R ^ 2 / 2) hh
    rw [abs_of_nonpos (sub_nonpos.mpr (interaction_bounds β hβ _ _).2)] at he
    linarith
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hn2 : (n : ℝ) ^ 2 ≠ 0 := (sq_pos_of_pos hn').ne'
  have heq : 1 - Source.energy β x =
      (∑ i, ∑ j, (1 - Real.exp (β * (⟪(x i).val, (x j).val⟫ - 1)))) / (n : ℝ) ^ 2 := by
    simp only [Source.energy, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    field_simp
  rw [heq]
  apply (div_le_iff₀ (sq_pos_of_pos hn')).mpr
  calc
    _ ≤ ∑ _ : Fin n, ∑ _ : Fin n, (β * R ^ 2 / 2) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end Metastability.EnergyEstimates
