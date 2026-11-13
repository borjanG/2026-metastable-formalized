import Metastability.BarycenterBounds
import Metastability.BarycenterContinuity
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! Local ambient smoothness away from both exceptional correlations, and
Lipschitz regularity along every compact active trajectory interval. -/
noncomputable section
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
namespace Metastability.BarycenterRegularity
open Source AngularGeometry BarycenterFormula
variable {d : ℕ}

/-- Smoothness is only used off the diagonal. Continuity at the diagonal is
proved separately using the genuine source interpolation. -/
theorem contDiffAt_vector (s : ℝ) (z : Vector d × Vector d)
    (hlo : -1 < ⟪z.1, z.2⟫) (hhi : ⟪z.1, z.2⟫ < 1) :
    ContDiffAt ℝ 1 (fun w : Vector d × Vector d => vector s w.1 w.2) z := by
  have hρ : ContDiffAt ℝ 1 (fun w : Vector d × Vector d => ⟪w.1, w.2⟫) z :=
    contDiffAt_fst.inner ℝ contDiffAt_snd
  have hθ : ContDiffAt ℝ 1 (fun w : Vector d × Vector d => Real.arccos ⟪w.1, w.2⟫) z :=
    (Real.contDiffAt_arccos hlo.ne' hhi.ne).comp (f := fun w : Vector d × Vector d => ⟪w.1, w.2⟫) (g := Real.arccos) z hρ
  have hsin : Real.sin (Real.arccos ⟪z.1, z.2⟫) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (Real.arccos_pos.mpr hhi) (Real.arccos_lt_pi.mpr hlo)).ne'
  have hcos : ContDiffAt ℝ 1 (fun w : Vector d × Vector d => Real.cos (s * Real.arccos ⟪w.1, w.2⟫)) z :=
    Real.contDiff_cos.contDiffAt.comp z (contDiffAt_const.mul hθ)
  have hrat : ContDiffAt ℝ 1 (fun w : Vector d × Vector d =>
      Real.sin (s * Real.arccos ⟪w.1, w.2⟫) / Real.sin (Real.arccos ⟪w.1, w.2⟫)) z :=
    (Real.contDiff_sin.contDiffAt.comp z (contDiffAt_const.mul hθ)).div
      (Real.contDiff_sin.contDiffAt.comp z hθ) hsin
  exact (hcos.smul contDiffAt_fst).add
    (hrat.smul (contDiffAt_snd.sub (hρ.smul contDiffAt_fst)))

/-- No regularity of the clock or the composed barycenter is assumed here:
particle Lipschitz bounds and the genuine nondegenerate angular window suffice. -/
theorem exists_lipschitzOnWith_vector (s : ℝ) (p q : ℝ → Sphere d)
    (a b : ℝ) {Kp Kq : ℝ≥0}
    (hp : LipschitzOnWith Kp (fun t => (p t).val) (Icc a b))
    (hq : LipschitzOnWith Kq (fun t => (q t).val) (Icc a b))
    (hneq : ∀ t ∈ Icc a b, p t ≠ q t)
    (hθ : ∀ t ∈ Icc a b, angularDist (p t) (q t) < Real.pi) :
    ∃ K : ℝ≥0, LipschitzOnWith K
      (fun t => vector s (p t).val (q t).val) (Icc a b) := by
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact isCompact_Icc
  intro t ht
  have hpos : 0 < angularDist (p t) (q t) :=
    lt_of_le_of_ne (angularDist_nonneg _ _) (fun hz => hneq t ht ((angularDist_eq_zero_iff _ _).mp hz.symm))
  have hρlo : -1 < ⟪(p t).val, (q t).val⟫ := Real.arccos_lt_pi.mp (hθ t ht)
  have hρhi : ⟪(p t).val, (q t).val⟫ < 1 := Real.arccos_pos.mp hpos
  obtain ⟨K, V, hV, hloc⟩ := (contDiffAt_vector s ((p t).val, (q t).val) hρlo hρhi).exists_lipschitzOnWith
  let f : ℝ → Vector d × Vector d := fun u => ((p u).val, (q u).val)
  have hpair : LipschitzOnWith (max Kp Kq) f (Icc a b) := hp.prodMk hq
  refine ⟨K * max Kp Kq, Icc a b ∩ f ⁻¹' V, ?_, ?_⟩
  · exact inter_mem self_mem_nhdsWithin ((hpair.continuousOn t ht).preimage_mem_nhdsWithin hV)
  · have hrestricted : LipschitzOnWith (max Kp Kq) f (Icc a b ∩ f ⁻¹' V) :=
      hpair.mono inter_subset_left
    have hm : MapsTo f (Icc a b ∩ f ⁻¹' V) V := fun _ hu => hu.2
    have hh := LipschitzOnWith.comp (f := f)
      (g := fun z : Vector d × Vector d => vector s z.1 z.2) hloc hrestricted hm
    exact hh

end Metastability.BarycenterRegularity
