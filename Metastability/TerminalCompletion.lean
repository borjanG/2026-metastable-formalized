import Metastability.TerminalEnergy
import Metastability.FiniteTransport
import Metastability.ActiveScales

/-! Forward control after actual root completion, in the same accelerated
clock. The completion configuration supplies the terminal cap. -/
noncomputable section
open Set Filter
open scoped Topology
namespace Metastability.TerminalCompletion
open Source AngularGeometry
variable {n d : ℕ}

theorem after_completion (hn : 0 < n) (model : Model) (β : ℝ) (hβ : 1 < β)
    (hcut : clockCutoff β < Real.pi / 2)
    (X : ℝ → Configuration n d) (hX : Solves model β X)
    (shift : ℝ) (hshift : 0 ≤ shift) (clock : ℝ → ℝ)
    (hc : ClockRelation β X shift clock) (a : ℝ) (ha : 0 ≤ a)
    (hcomplete : ∀ i j, angularDist (accelerated X shift clock a i)
      (accelerated X shift clock a j) ≤ clockCutoff β) :
    ∀ t ≥ a,
      (∀ i j, angularDist (accelerated X shift clock t i)
        (accelerated X shift clock a j) ≤ clockCutoff β) ∧
      |energy β (accelerated X shift clock t) - 1| ≤ 2 * β * clockCutoff β ^ 2 ∧
      ∀ z : Sphere d, ∀ j : Fin n,
        empiricalWasserstein hn (accelerated X shift clock t) (fun _ => z) ≤
          clockCutoff β + angularDist (accelerated X shift clock a j) z := by
  intro t ht
  have haorig : 0 ≤ shift + clock a := add_nonneg hshift (hc.1.2.1 a ha)
  have htime : shift + clock a ≤ shift + clock t :=
    add_le_add_right (hc.2.1.monotoneOn ha (ha.trans ht) ht) shift
  have hcaps : ∀ i j, angularDist (accelerated X shift clock t i)
      (accelerated X shift clock a j) ≤ clockCutoff β := by
    intro i j
    let C : SphericalCap d := ⟨accelerated X shift clock a j, clockCutoff β,
      (ActiveScales.clockCutoff_pos hβ).le, hcut⟩
    exact CapInvariance.full_cap_forward_invariant hn X hX C
      (shift + clock a) haorig (fun k => hcomplete k j) (shift + clock t) htime i
  refine ⟨hcaps, ?_, ?_⟩
  · let C : SphericalCap d := ⟨accelerated X shift clock a ⟨0, hn⟩, clockCutoff β,
      (ActiveScales.clockCutoff_pos hβ).le, hcut⟩
    have he := CapInvariance.full_cap_energy_bound hn (zero_lt_one.trans hβ).le X hX C
      (shift + clock a) haorig (fun k => hcomplete k ⟨0, hn⟩) (shift + clock t) htime
    change |energy β (X (shift + clock t)) - 1| ≤ 2 * β * clockCutoff β ^ 2
    rw [abs_sub_comm, abs_of_nonneg he.1]
    exact he.2
  · intro z j
    apply FiniteTransport.empiricalWasserstein_le_of_pointwise
    intro i
    exact (angularDist_triangle (accelerated X shift clock t i)
      (accelerated X shift clock a j) z).trans (add_le_add (hcaps i j) le_rfl)

end Metastability.TerminalCompletion
