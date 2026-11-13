import Metastability.ActiveSourceLaw
import Metastability.EnergyAssembly

/-! Uniform energy control on an entire pre-mesoscopic stage. The mesoscopic
lower angle already makes every active cross kernel vanish; no sharper
interior angle asymptotic is needed for the energy limit. -/
noncomputable section
open Set Filter
open scoped Topology RealInnerProductSpace
namespace Metastability.StageEnergy
open Source ActiveScales ActiveSourceLaw CapEnlargement
variable {n N d : ℕ}

def error (κ β : ℝ) : ℝ := β * Real.exp (-κ * β) + β ^ (-(1 / 3 : ℝ))

theorem tendsto_error (κ : ℝ) (hκ : 0 < κ) :
    Tendsto (error κ) atTop (𝓝 0) := by
  have hfirst : Tendsto (fun β : ℝ => β * Real.exp (-κ * β)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 κ hκ
  simpa only [error, add_zero] using
    hfirst.add (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3))

/-- The source stage hypotheses and the mesoscopic lower angle give a single
vanishing energy error, uniform in stage, model, representatives and configuration. -/
theorem eventual_energy_bound (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) (κ : ℝ) (hκ : 0 < κ) :
    ∀ᶠ β : ℝ in atTop, 1 < β ∧
      ∀ M ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 5), ∀ l : Fin N,
      ∀ x : Configuration n d, StageHyp T C β κ M l x →
      ∀ i j : Fin n, i ∈ T.left l → j ∈ T.right l →
      mesoscopicScale β ≤ angularDist (x i) (x j) →
      |energy β x - plateauEnergy T l.castSucc| ≤ error κ β := by
  obtain ⟨B, hB, hbarriers⟩ := ActiveGeometry.stage_barriers T hN C hC
  have hgap : ∀ᶠ β : ℝ in atTop,
      (1 / 3 : ℝ) * (Real.log β / β) ≤ 7 * treeMargin hN C := by
    have ht : Tendsto (fun β : ℝ => (1 / 3 : ℝ) * (Real.log β / β)) atTop (𝓝 0) := by
      simpa only [mul_zero] using
        Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.const_mul (1 / 3 : ℝ)
    have hp : (0 : ℝ) < 7 * treeMargin hN C := mul_pos (by norm_num) (treeMargin_pos hN C hC)
    exact (ht.eventually (gt_mem_nhds hp)).mono (fun _ h => h.le)
  filter_upwards [eventually_ge_atTop B,
    ActiveScales.eventually_mul_exp_le_rpow 30 κ 1 0 hκ,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    tendsto_mesoscopicScale.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)), hgap]
      with β hβ hex hlog hmeso hgap
  have hβ1 : 1 < β := hB.trans_le hβ
  have hβ0 : 0 < β := zero_lt_one.trans hβ1
  have he0 : 0 ≤ Real.exp (-κ * β) := (Real.exp_pos _).le
  simp only [Real.rpow_one, Real.rpow_zero] at hex
  refine ⟨hβ1, ?_⟩
  intro M hM l x hstage i j hi hj hangle
  have hgeo := (hbarriers β hβ M hM l x hstage.2.1 hstage.2.2).2
  have hactive := ActiveAngleScale.mesoscopic_deficit_lower β hβ1 hmeso.le (x i) (x j) hangle
  have hsmall : 2 * Real.exp (-κ * β) ≤ (1 / 15 : ℝ) * (Real.log β / β) := by
    have hm : (2 * Real.exp (-κ * β)) * β ≤ (1 / 15 : ℝ) * Real.log β := by
      nlinarith only [hex, hlog]
    have hd := (le_div_iff₀ hβ0).mpr hm
    convert hd using 1
    ring
  have hwithin : ∀ D ∈ T.partition l.castSucc, ∀ p ∈ D, ∀ q ∈ D,
      1 - ⟪(x p).val, (x q).val⟫ ≤ Real.exp (-κ * β) := by
    intro D hD p hp q hq
    have hv := ActiveCoefficients.inner_variation (x p) (x p) (x q)
    rw [real_inner_self_eq_norm_sq, (x p).property, one_pow] at hv
    exact (le_abs_self _).trans (hv.trans (hstage.1 D hD p hp q hq))
  have hcross : ∀ D ∈ T.partition l.castSucc, ∀ E ∈ T.partition l.castSucc,
      D ≠ E → ∀ p ∈ D, ∀ q ∈ E,
      (1 / 3 : ℝ) * (Real.log β / β) ≤ 1 - ⟪(x p).val, (x q).val⟫ := by
    intro D hD E hE hne p hp q hq
    by_cases ha : ActiveGeometry.IsActiveCross T l p q
    · have hdiff := ActiveClock.activeCross_deficit_error T l _ x hstage.1 i j hi hj p q ha
      linarith only [hactive, hsmall, (abs_le.mp hdiff).1]
    · have hne' : T.blockOf l.castSucc p ≠ T.blockOf l.castSucc q := by
        intro he
        exact hne ((T.blockOf_unique l.castSucc p D hD hp).trans
          (he.trans (T.blockOf_unique l.castSucc q E hE hq).symm))
      have hu : 0 ≤ upperBarrier C l :=
        (TreeSeparation.lowerBarrier_pos T C hC l).le.trans (hC.2 l).2.2.2.2.1
      have hb := hgeo p q hne' ha
      linarith only [hb, hgap, hu]
  have he := EnergyAssembly.energy_sub_plateau_le T l.castSucc β
    (Real.exp (-κ * β)) ((1 / 3 : ℝ) * (Real.log β / β)) hβ0.le he0 x hwithin hcross
  have hpow : Real.exp (-β * ((1 / 3 : ℝ) * (Real.log β / β))) = β ^ (-(1 / 3 : ℝ)) := by
    rw [Real.rpow_def_of_pos hβ0]
    congr 1
    field_simp
  simpa only [hpow, error] using he

end Metastability.StageEnergy
