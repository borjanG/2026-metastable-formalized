import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.Lattice
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Conditional scalar comparison and finite-maximum invariance

These are analytic helpers. The differential inequalities are explicit inputs;
the source dynamics must establish them separately. Neither a Grönwall estimate
nor confinement is assumed as an input.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace Metastability.ContractionComparison

/-- Integrating-factor comparison for a continuous varying coefficient and
actual right derivatives. It is valid for either sign of the scalar function. -/
theorem le_initial_mul_exp_integral (q q' K : ℝ → ℝ) {a b : ℝ}
    (hq : ContinuousOn q (Icc a b)) (hK : ContinuousOn K (Icc a b))
    (hd : ∀ x ∈ Ico a b, HasDerivWithinAt q (q' x) (Ici x) x)
    (hbound : ∀ x ∈ Ico a b, q' x ≤ K x * q x)
    {t : ℝ} (ht : t ∈ Icc a b) :
    q t ≤ q a * Real.exp (∫ u in a..t, K u) := by
  have hab : a ≤ b := ht.1.trans ht.2
  let Kext : ℝ → ℝ := fun u => K (max a (min u b))
  have hKext : Continuous Kext := hK.comp_continuous
    (continuous_const.max (continuous_id.min continuous_const))
    (fun u => ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩)
  have hext : ∀ u ∈ Icc a b, Kext u = K u := by
    intro u hu
    simp only [Kext, min_eq_left hu.2, max_eq_right hu.1]
  let H : ℝ → ℝ := fun u => ∫ v in a..u, Kext v
  have hHd (u : ℝ) : HasDerivAt H (Kext u) u :=
    (hKext.integral_hasStrictDerivAt a u).hasDerivAt
  have hHc : Continuous H := continuous_iff_continuousAt.mpr (fun u => (hHd u).continuousAt)
  let g : ℝ → ℝ := fun u => q u * Real.exp (-H u)
  let g' : ℝ → ℝ := fun u => (q' u - K u * q u) * Real.exp (-H u)
  have hgc : ContinuousOn g (Icc a b) :=
    hq.mul (Real.continuous_exp.comp hHc.neg).continuousOn
  have hgd : ∀ u ∈ Ico a b, HasDerivWithinAt g (g' u) (Ici u) u := by
    intro u hu
    have h := (hd u hu).mul (hHd u).neg.exp.hasDerivWithinAt
    rw [hext u (Ico_subset_Icc_self hu)] at h
    convert h using 1
    dsimp [g, g']
    ring
  have hg0 : g a = q a := by
    simp only [g, H, intervalIntegral.integral_same, neg_zero, Real.exp_zero, mul_one]
  have hg' : ∀ u ∈ Ico a b, g' u ≤ 0 := by
    intro u hu
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hbound u hu)) (Real.exp_pos _).le
  have hg : g t ≤ q a :=
    image_le_of_deriv_right_le_deriv_boundary hgc hgd (B := fun _ => q a)
      (B' := fun _ => 0) hg0.le continuousOn_const
      (fun u _ => hasDerivWithinAt_const u (Ici u) (q a)) hg' ht
  have hmul := mul_le_mul_of_nonneg_right hg (Real.exp_pos (H t)).le
  have hexp : Real.exp (-H t) * Real.exp (H t) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hfinal : q t ≤ q a * Real.exp (H t) := by
    simpa only [g, mul_assoc, hexp, mul_one] using hmul
  have hHint : H t = ∫ u in a..t, K u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht.1] at hu
    exact hext u ⟨hu.1, hu.2.trans ht.2⟩
  rwa [hHint] at hfinal

/-- The contraction form of the varying-coefficient estimate. No sign
assumption on `q`, `c`, `C`, or `L` is needed for this implication. -/
theorem contraction_bound (q q' L : ℝ → ℝ) {a b c C : ℝ}
    (hq : ContinuousOn q (Icc a b)) (hL : ContinuousOn L (Icc a b))
    (hd : ∀ x ∈ Ico a b, HasDerivWithinAt q (q' x) (Ici x) x)
    (hbound : ∀ x ∈ Ico a b, q' x ≤ (-c + C * L x) * q x)
    {t : ℝ} (ht : t ∈ Icc a b) :
    q t ≤ q a * Real.exp (-c * (t - a) + C * ∫ u in a..t, L u) := by
  have h := le_initial_mul_exp_integral q q' (fun u => -c + C * L u) hq
    (continuousOn_const.add (continuousOn_const.mul hL)) hd hbound ht
  have hLi : IntervalIntegrable L volume a t :=
    (hL.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
  rw [intervalIntegral.integral_add intervalIntegrable_const (hLi.const_mul C),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, smul_eq_mul] at h
  simpa only [mul_comm (t - a) (-c)] using h

/-- A finite maximum cannot cross a constant barrier if every branch at the
barrier has strictly negative right derivative whenever all branches are below
or at it. Initial equality is allowed; no prior confinement is assumed. -/
theorem finite_maximum_le_of_strict_boundary {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f f' : ι → ℝ → ℝ) {a b R : ℝ}
    (hc : ∀ i ∈ s, ContinuousOn (f i) (Icc a b))
    (hd : ∀ x ∈ Ico a b, ∀ i ∈ s, HasDerivWithinAt (f i) (f' i x) (Ici x) x)
    (ha : ∀ i ∈ s, f i a ≤ R)
    (hboundary : ∀ x ∈ Ico a b, (∀ j ∈ s, f j x ≤ R) →
      ∀ i ∈ s, f i x = R → f' i x < 0)
    {t : ℝ} (ht : t ∈ Icc a b) : ∀ i ∈ s, f i t ≤ R := by
  let M : ℝ → ℝ := fun u => s.sup' hs (fun i => f i u)
  let S : Set ℝ := {u | M u ≤ R}
  have hMc : ContinuousOn M (Icc a b) := ContinuousOn.finset_sup'_apply hs hc
  have hclosed : IsClosed (S ∩ Icc a b) := by
    simpa only [inter_comm] using
      hMc.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_Iic (a := R))
  have hstart : a ∈ S := Finset.sup'_le hs _ ha
  have hinvariant : Icc a b ⊆ S := by
    apply hclosed.Icc_subset_of_forall_exists_gt hstart
    intro x hx y hy
    have hxall : ∀ i ∈ s, f i x ≤ R := fun i hi =>
      (Finset.le_sup' (fun j => f j x) hi).trans hx.1
    have hbranches : ∀ i ∈ s, ∀ᶠ z in 𝓝[>] x, f i z < R := by
      intro i hi
      by_cases heq : f i x = R
      · have he := (hd x hx.2 i hi).Ioi_of_Ici.limsup_slope_le'
          (lt_irrefl x) (hboundary x hx.2 hxall i hi heq)
        filter_upwards [he, self_mem_nhdsWithin] with z hz hxz
        rw [slope_def_field] at hz
        have hz' := (div_lt_iff₀ (sub_pos.mpr hxz)).mp hz
        rw [zero_mul, heq] at hz'
        exact sub_neg.mp hz'
      · have hlt : f i x < R := lt_of_le_of_ne (hxall i hi) heq
        exact (hd x hx.2 i hi).Ioi_of_Ici.continuousWithinAt (Iio_mem_nhds hlt)
    have hall : ∀ᶠ z in 𝓝[>] x, ∀ i ∈ s, f i z < R :=
      (eventually_all_finset s).mpr hbranches
    obtain ⟨z, hz, hzy⟩ := (hall.and (Ioc_mem_nhdsGT hy)).exists
    exact ⟨z, Finset.sup'_le hs _ (fun i hi => (hz i hi).le), hzy⟩
  intro i hi
  exact (Finset.le_sup' (fun j => f j t) hi).trans (hinvariant ht)

end Metastability.ContractionComparison
