import Metastability.ActualPilot
import Metastability.PilotLimit

/-!
# The two-particle USA energy staircase

The input is a family of actual sphere-valued vector ODE solutions with a fixed
initial correlation strictly between -1 and 1. The cutoff clocks are constructed,
not assumed. The conclusion is uniform on every compact set of nonnegative
accelerated times avoiding the single jump at one half, for real beta → infinity.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace Metastability.PilotTheorem

variable {d : ℕ}

abbrev Family (d : ℕ) := (β : ℝ) → 1 < β → ActualPilot.Trajectory β d

/-- Auxiliary limit function: the actual energy for beta > 1, extended by zero
outside that parameter domain only to express a real atTop limit. -/
def energy (P : Family d) (β t : ℝ) : ℝ :=
  if hβ : 1 < β then (P β hβ).energy hβ t else 0

/-- Family of constructed clocks for beta > 1, with an arbitrary zero extension
outside that domain. Source clock claims are restricted to beta > 1. -/
def clock (P : Family d) (β t : ℝ) : ℝ :=
  if hβ : 1 < β then (P β hβ).clock hβ t else 0

/-- Every clock in the family satisfies the literal source clock relation with
zero preparation shift. -/
theorem clockRelation (P : Family d) (β : ℝ) (hβ : 1 < β) :
    Source.ClockRelation β (P β hβ).configuration 0 (clock P β) := by
  have heq : clock P β = (P β hβ).clock hβ := by
    funext t
    simp only [clock, dif_pos hβ]
  rw [heq]
  exact (P β hβ).clockRelation hβ

/-- Uniform energy staircase for actual two-particle USA solutions.
All intermediate profile and hitting-time estimates are proved from the ODE. -/
theorem energy_staircase (P : Family d) (ρ₀ : ℝ)
    (hρl : -1 < ρ₀) (hρu : ρ₀ < 1)
    (hinitial : ∀ (β : ℝ) (hβ : 1 < β), (P β hβ).correlation 0 = ρ₀)
    {K : Set ℝ} (hK : IsCompact K) (hKsub : K ⊆ Ici 0) (hjump : (1 / 2 : ℝ) ∉ K) :
    TendstoUniformlyOn (energy P) (fun t => if t < 1 / 2 then 1 / 2 else 1) atTop K := by
  let a := Real.tan (Real.arccos ρ₀ / 2)
  have ha : 0 < a := PilotGeometry.tan_arccos_half_pos hρl hρu
  have hodds : ScalarClock.odds ρ₀ = a ^ 2 :=
    PilotGeometry.odds_eq_tan_arccos_half_sq hρl hρu.le
  have heq : Source.clockCutoff = PilotCutoff.angularCutoff :=
    funext PilotGeometry.clockCutoff_eq_angularCutoff
  have hcut : Tendsto Source.clockCutoff atTop (𝓝 0) := by
    rw [heq]
    exact PilotCutoff.tendsto_angularCutoff
  have hcos : Tendsto (fun β : ℝ => Real.cos (Source.clockCutoff β)) atTop (𝓝 1) := by
    simpa only [Real.cos_zero] using Real.continuous_cos.continuousAt.tendsto.comp hcut
  have hevent : ∀ᶠ β : ℝ in atTop,
      1 < β ∧ Source.clockCutoff β < Real.pi ∧ ρ₀ < Real.cos (Source.clockCutoff β) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ),
      hcut.eventually (gt_mem_nhds Real.pi_pos), hcos.eventually (lt_mem_nhds hρu)]
      with β hb hc hr
    exact ⟨hb, hc, hr⟩
  have hprofile : ∀ᶠ β : ℝ in atTop, ∀ t ∈ Icc 0 (PilotCutoff.cutoffTime a β),
      energy P β t = PilotAsymptotics.analyticEnergy a β t := by
    filter_upwards [hevent] with β hb
    have hp := (P β hb.1).profile_until_cutoff hb.1 ha
      (by rw [hinitial]; exact hρl) (by rw [hinitial]; exact hodds)
      (by rw [hinitial]; exact hb.2.2) hb.2.1
    intro t ht
    simpa only [energy, dif_pos hb.1] using hp.2.2 t ht
  have hmono : ∀ᶠ β : ℝ in atTop, MonotoneOn (energy P β) (Ici 0) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with β hb
    intro s hs t ht hst
    simpa only [energy, dif_pos hb] using (P β hb).monotone_energy hb hs ht hst
  have hupper : ∀ᶠ β : ℝ in atTop, ∀ t ∈ Ici 0, energy P β t ≤ 1 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with β hb
    intro t _
    simpa only [energy, dif_pos hb] using (P β hb).energy_le_one hb t
  exact PilotLimit.tendstoUniformlyOn_staircase a ha (energy P) hprofile hmono hupper
    hK hKsub hjump

end Metastability.PilotTheorem
