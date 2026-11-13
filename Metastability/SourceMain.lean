import Metastability.CenterCascade
import Metastability.GlobalEnergy
import Metastability.GlobalMeasure

/-! The joint source theorem: one preparation shift and one actual clock
serve the energy staircase, deterministic empirical transport limits, and
quantitative collision windows. Every stage estimate and entry-center limit
is produced from visible initial data and the literal source ODE.

The transport quantity is Source.empiricalWasserstein, the explicit finite
angular coupling infimum. No identification with a separate measure-library
Wasserstein implementation is asserted by this file. These are proved ordinary
declarations, not an author-approved frozen statement packet. -/
noncomputable section
open Set Filter
open scoped Topology
namespace Metastability.SourceMain
open Source

/-- Joint global limits and finite collision cascade for USA and SA. The
recursive deterministic centers are chosen before the arbitrary real-beta
family. All conclusions share the same O(beta) shift and actual inverse clock. -/
theorem main_and_cascade
    (n d N : ℕ) (hN : 0 < N)
    (model : Model) (T : CollisionTree n N) (C : TreeCaps T d)
    (hC : StrictlyPrepared C) :
    ∃ z : NodeCenters T d,
      IsDeterministicCenters model hN C z ∧
      ∀ X : ℝ → ℝ → Configuration n d,
        (∀ β > 1, Solves model β (X β)) →
        (∀ β > 1, VisiblePrepared hN C β (X β 0)) →
        ∃ (shift : ℝ → ℝ) (clock : ℝ → ℝ → ℝ),
          (∀ β > 1, 0 ≤ shift β) ∧
          Asymptotics.IsBigO atTop shift (fun β : ℝ => β) ∧
          (∀ β > 1, ClockRelation β (X β) (shift β) (clock β)) ∧
          (∀ K : Set ℝ, IsCompact K → K ⊆ Ici 0 →
            (∀ t ∈ K, ∀ l : Fin N, t ≠ jumpTime model T l.succ) →
            ∀ ε > 0, ∀ᶠ β : ℝ in atTop, ∀ t ∈ K,
              |energy β (accelerated (X β) (shift β) (clock β) t) -
                staircase model T t| < ε) ∧
          (∀ l : Fin N, ∀ K : Set ℝ, IsCompact K →
            K ⊆ Ioo (jumpTime model T l.castSucc) (jumpTime model T l.succ) →
            ∀ ε > 0, ∀ᶠ β : ℝ in atTop, ∀ t ∈ K,
              empiricalWasserstein (T.particle_pos hN)
                (accelerated (X β) (shift β) (clock β) t)
                (partitionConfiguration T z l.succ) < ε) ∧
          (∀ K : Set ℝ, IsCompact K →
            K ⊆ Ioi (jumpTime model T (Fin.last N)) →
            ∀ ε > 0, ∀ᶠ β : ℝ in atTop, ∀ t ∈ K,
              empiricalWasserstein (T.particle_pos hN)
                (accelerated (X β) (shift β) (clock β) t)
                (partitionConfiguration T z (Fin.last N)) < ε) ∧
          ∃ (tminus tplus : ℝ → Fin N → ℝ),
            (∀ᶠ β : ℝ in atTop, ∀ l : Fin N,
              0 ≤ tminus β l ∧ tminus β l < tplus β l ∧
              (∀ i ∈ T.parent l, ∀ j ∈ T.parent l,
                angularDist
                  (accelerated (X β) (shift β) (clock β) (tplus β l) i)
                  (accelerated (X β) (shift β) (clock β) (tplus β l) j)
                    ≤ clockCutoff β) ∧
              (∀ m : Fin N, l.val < m.val →
                ∀ t ∈ Icc (tminus β l) (tplus β l),
                  ∃ i ∈ T.parent m, ∃ j ∈ T.parent m,
                    visibleScale β < angularDist
                      (accelerated (X β) (shift β) (clock β) t i)
                      (accelerated (X β) (shift β) (clock β) t j))) ∧
            (∀ l : Fin N, Asymptotics.IsBigO atTop
              (fun β : ℝ => tminus β l - jumpTime model T l.succ)
              (fun β : ℝ => Real.log (Real.log β) / Real.log β)) ∧
            (∀ l : Fin N, Asymptotics.IsBigO atTop
              (fun β : ℝ => tplus β l - tminus β l)
              (fun β : ℝ => Real.log (Real.log β) / Real.log β)) := by
  obtain ⟨κ, CStar, hκ, hCs, hmargin⟩ :=
    GeometricCascade.admissible_parameters n (TreeDynamics.particle_pos T)
  have hκ4 : 4 < κ := (PlateauStability.kappaThreshold_gt_four n).trans hκ
  have hκ0 : 0 < κ := by linarith only [hκ4]
  obtain ⟨z, hz, _⟩ := DeterministicCenters.exists_deterministic_centers T hN C hC model
  refine ⟨z, hz, ?_⟩
  intro X hX hvisible
  obtain ⟨data⟩ := CascadeFamilyData.exists_data T hN C hC κ hκ model CStar hmargin X hX hvisible
  have hentry := CenterCascade.entry_centers T hN C hC κ hκ4 model CStar hmargin X hX hvisible data z hz
  have hmeasure := GlobalMeasure.measure_limit_of_cascade T hN C hC κ hκ4 model CStar hCs.le X hX data z hz hentry
  refine ⟨fun β => CStar * β, data.clock, ?_, ?_, data.clock_relation, ?_, hmeasure.1, hmeasure.2,
    data.hit, data.complete, ?_, ?_, ?_⟩
  · intro β hβ
    exact mul_nonneg hCs.le (zero_lt_one.trans hβ).le
  · exact (Asymptotics.isBigO_refl (fun β : ℝ => β) atTop).const_mul_left CStar
  · intro K hK hK0 havoid ε hε
    have hh := GlobalEnergy.energy_limit_of_cascade T hN C hC κ hκ0 model CStar hCs.le X hX data K hK hK0 havoid
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hh ε hε] with β hb t ht
    simpa only [Real.dist_eq, abs_sub_comm] using hb t ht
  · filter_upwards [data.entry_nonneg, data.stage_times, data.stage_windows,
      data.complete_least, data.future_separation] with β hn ht hw hc hf
    intro l
    refine ⟨(hn l.castSucc).trans (ht l).1, (hw l).2.1, (hc l).1.2, ?_⟩
    intro m hl t htt
    obtain ⟨p, hp, q, hq, _, hgap⟩ := hf l t ⟨(ht l).1.trans htt.1, htt.2⟩ m hl
    exact ⟨p, hp, q, hq, hgap⟩
  · intro l
    obtain ⟨K, hK, hbound⟩ := data.timing_error
    apply Asymptotics.IsBigO.of_bound K
    filter_upwards [hbound] with β hb
    simpa only [Real.norm_eq_abs] using ((hb.2 l).1.trans
      (mul_le_mul_of_nonneg_left (le_abs_self _) hK.le))
  · intro l
    obtain ⟨K, hK, hbound⟩ := data.timing_error
    apply Asymptotics.IsBigO.of_bound (2 * K)
    filter_upwards [hbound] with β hb
    have hdiff : |data.complete β l - data.hit β l| ≤
        |data.complete β l - jumpTime model T l.succ| +
          |data.hit β l - jumpTime model T l.succ| := by
      have hh := abs_sub (data.complete β l - jumpTime model T l.succ)
        (data.hit β l - jumpTime model T l.succ)
      simpa only [sub_sub_sub_cancel_right] using hh
    have hsum := add_le_add (hb.2 l).2 (hb.2 l).1
    have habs := mul_le_mul_of_nonneg_left
      (le_abs_self (Real.log (Real.log β) / Real.log β)) (show 0 ≤ 2 * K by positivity)
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    linarith only [hdiff, hsum, habs]


/-- Both source global limits, with quantitative windows omitted. -/
theorem main
    (n d N : ℕ) (hN : 0 < N)
    (model : Model) (T : CollisionTree n N) (C : TreeCaps T d)
    (hC : StrictlyPrepared C) :
    ∃ z : NodeCenters T d,
      IsDeterministicCenters model hN C z ∧
      ∀ X : ℝ → ℝ → Configuration n d,
        (∀ β > 1, Solves model β (X β)) →
        (∀ β > 1, VisiblePrepared hN C β (X β 0)) →
        ∃ (shift : ℝ → ℝ) (clock : ℝ → ℝ → ℝ),
          (∀ β > 1, 0 ≤ shift β) ∧
          Asymptotics.IsBigO atTop shift (fun β : ℝ => β) ∧
          (∀ β > 1, ClockRelation β (X β) (shift β) (clock β)) ∧
          (∀ K : Set ℝ, IsCompact K → K ⊆ Ici 0 →
            (∀ t ∈ K, ∀ l : Fin N, t ≠ jumpTime model T l.succ) →
            ∀ ε > 0, ∀ᶠ β : ℝ in atTop, ∀ t ∈ K,
              |energy β (accelerated (X β) (shift β) (clock β) t) -
                staircase model T t| < ε) ∧
          (∀ l : Fin N, ∀ K : Set ℝ, IsCompact K →
            K ⊆ Ioo (jumpTime model T l.castSucc) (jumpTime model T l.succ) →
            ∀ ε > 0, ∀ᶠ β : ℝ in atTop, ∀ t ∈ K,
              empiricalWasserstein (T.particle_pos hN)
                (accelerated (X β) (shift β) (clock β) t)
                (partitionConfiguration T z l.succ) < ε) ∧
          (∀ K : Set ℝ, IsCompact K →
            K ⊆ Ioi (jumpTime model T (Fin.last N)) →
            ∀ ε > 0, ∀ᶠ β : ℝ in atTop, ∀ t ∈ K,
              empiricalWasserstein (T.particle_pos hN)
                (accelerated (X β) (shift β) (clock β) t)
                (partitionConfiguration T z (Fin.last N)) < ε) := by
  obtain ⟨z, hz, hall⟩ := main_and_cascade n d N hN model T C hC
  refine ⟨z, hz, ?_⟩
  intro X hX hv
  obtain ⟨shift, clock, hs, hO, hc, he, hm, hf, _⟩ := hall X hX hv
  exact ⟨shift, clock, hs, hO, hc, he, hm, hf⟩


end Metastability.SourceMain
