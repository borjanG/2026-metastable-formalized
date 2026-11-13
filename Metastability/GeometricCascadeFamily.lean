import Metastability.GeometricCascade

/-! Families of actual clocks and stage times, with convergence of every finite time. -/
noncomputable section
open Filter Set
open scoped Topology RealInnerProductSpace
namespace Metastability.GeometricCascadeFamily
open Source CapEnlargement ActiveScales ActiveSourceLaw CascadeStep
variable {n N d : ℕ}

theorem time_limit_of_error (f : ℝ → ℝ) (a K : ℝ)
    (hbound : ∀ᶠ β : ℝ in atTop,
      |f β - a| ≤ K * (Real.log (Real.log β) / Real.log β)) :
    Tendsto f atTop (𝓝 a) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hlim : Tendsto (fun β : ℝ => K * (Real.log (Real.log β) / Real.log β)) atTop (𝓝 0) := by
    simpa only [mul_zero] using ActiveTimingScales.tendsto_loglog_div_log.const_mul K
  exact squeeze_zero' (Eventually.of_forall (fun _ => dist_nonneg))
    (hbound.mono (fun _ h => by simpa only [Real.dist_eq] using h)) hlim

/-- Visible source families admit actual clocks at every real beta above one,
and simultaneous stage-time families with every geometric conclusion and
the literal deterministic jump-time limits. Constants precede the trajectory
family and representatives. Values below the common large-beta threshold
carry no geometric assertion. -/
theorem geometric_cascade_family (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) (κ : ℝ)
    (hκ : PlateauStability.kappaThreshold n < κ) (model : Model) (CStar : ℝ)
    (hCStar : 8 * κ / (1 / (4 * (n : ℝ))) < CStar) :
    ∃ K : ℝ, 0 < K ∧ ∃ β₀ : ℝ, 1 < β₀ ∧
      ∀ X : ℝ → ℝ → Configuration n d,
      (∀ β : ℝ, 1 < β → Solves model β (X β)) →
      (∀ β : ℝ, 1 < β → VisiblePrepared hN C β (X β 0)) →
      ∀ (i j : Fin N → Fin n), (∀ l, i l ∈ T.left l) → (∀ l, j l ∈ T.right l) →
      ∃ clock : ℝ → ℝ → ℝ, (∀ β : ℝ, 1 < β → ClockRelation β (X β) (CStar * β) (clock β)) ∧
      ∃ s : ℝ → Fin (N + 1) → ℝ, ∃ hit complete : ℝ → Fin N → ℝ,
        (∀ β ≥ β₀,
          (s β) 0 = 0 ∧ (∀ r, 0 ≤ (s β) r) ∧
        (∀ l, EntryGeometry T C β κ l (accelerated (X β) (CStar * β) (clock β) ((s β) l.castSucc))) ∧
        (∀ r, |(s β) r - jumpTime model T r| ≤ K * (Real.log (Real.log β) / Real.log β)) ∧
        (∀ l : Fin N,
          (hit β) l ∈ Ioo ((s β) l.castSucc) ((s β) l.castSucc + (1 + 1 / (2 * stageRate model T l))) ∧
          (complete β) l ∈ Ioc ((hit β) l) ((hit β) l + 20 * n * (Real.log (Real.log β) / Real.log β)) ∧
          (complete β) l ≤ (s β) l.succ ∧
          IsLeast {t : ℝ | (s β) l.castSucc ≤ t ∧
            angularDist (accelerated (X β) (CStar * β) (clock β) t (i l))
              (accelerated (X β) (CStar * β) (clock β) t (j l)) = mesoscopicScale β} ((hit β) l) ∧
          IsLeast {t : ℝ | (s β) l.castSucc ≤ t ∧ ∀ p ∈ T.parent l, ∀ q ∈ T.parent l,
            angularDist (accelerated (X β) (CStar * β) (clock β) t p)
              (accelerated (X β) (CStar * β) (clock β) t q) ≤ clockCutoff β} ((complete β) l) ∧
          |(hit β) l - jumpTime model T l.succ| ≤ K * (Real.log (Real.log β) / Real.log β) ∧
          |(complete β) l - jumpTime model T l.succ| ≤ K * (Real.log (Real.log β) / Real.log β) ∧
          (∀ t ∈ Icc ((s β) l.castSucc) ((complete β) l),
            StageHyp T C β κ (entryMultiplier l + 1) l (accelerated (X β) (CStar * β) (clock β) t) ∧
            1 - ⟪(accelerated (X β) (CStar * β) (clock β) t (i l)).val,
              (accelerated (X β) (CStar * β) (clock β) t (j l)).val⟫ ≤ upperBarrier C l + treeMargin hN C) ∧
          (∀ t ∈ Icc ((s β) l.castSucc) ((hit β) l), mesoscopicScale β ≤
            angularDist (accelerated (X β) (CStar * β) (clock β) t (i l))
              (accelerated (X β) (CStar * β) (clock β) t (j l))) ∧
          (∀ t ∈ Icc ((hit β) l) ((complete β) l),
            angularDist (accelerated (X β) (CStar * β) (clock β) t (i l))
              (accelerated (X β) (CStar * β) (clock β) t (j l)) ≤ mesoscopicScale β) ∧
          (∀ t ∈ Icc ((s β) l.castSucc) ((complete β) l), ∀ m : Fin N, l < m →
            ∃ p ∈ T.parent m, ∃ q ∈ T.parent m,
              7 * treeMargin hN C ≤ angularDist (accelerated (X β) (CStar * β) (clock β) t p)
                (accelerated (X β) (CStar * β) (clock β) t q) ∧
              visibleScale β < angularDist (accelerated (X β) (CStar * β) (clock β) t p)
                (accelerated (X β) (CStar * β) (clock β) t q)) ∧
          (l.val + 1 = N → (s β) l.succ = (complete β) l) ∧
          (∀ k : Fin N, k.castSucc = l.succ →
            (s β) l.succ = originalClockTime β (X β) (CStar * β) ((clock β) ((complete β) l) + CStar * β) ∧
            (clock β) ((s β) l.succ) = (clock β) ((complete β) l) + CStar * β ∧
            (s β) l.succ - (complete β) l ≤ CStar * β / Real.log β *
              Real.exp (-β * (lowerBarrier C k - treeMargin hN C)) ∧
            (∀ t ∈ Icc ((complete β) l) ((s β) l.succ),
              (∀ (D : Block n) (hD : D ∈ T.partition k.castSucc), ∀ p ∈ D,
                angularDist (accelerated (X β) (CStar * β) (clock β) t p) (C (T.currentNode k D hD)).center <
                  (C (T.currentNode k D hD)).radius + entryMultiplier k * enlargementScale β) ∧
              (∀ D ∈ T.partition k.castSucc, ∀ p ∈ D, ∀ q ∈ D,
                angularDist (accelerated (X β) (CStar * β) (clock β) t p)
                  (accelerated (X β) (CStar * β) (clock β) t q) ≤ clockCutoff β)) ∧
            (∀ t ∈ Icc ((complete β) l) ((s β) l.succ), ∀ D ∈ T.partition k.castSucc,
              ∀ p ∈ D, ∀ q ∈ D,
                angularDist (accelerated (X β) (CStar * β) (clock β) t p)
                  (accelerated (X β) (CStar * β) (clock β) ((complete β) l) q) ≤ 6 * clockCutoff β))) ∧
        (∀ p q : Fin n,
          angularDist (accelerated (X β) (CStar * β) (clock β) ((s β) (Fin.last N)) p)
            (accelerated (X β) (CStar * β) (clock β) ((s β) (Fin.last N)) q) ≤ clockCutoff β) ) ∧
        (∀ r : Fin (N + 1), Tendsto (fun β => s β r) atTop (𝓝 (jumpTime model T r))) ∧
        (∀ l : Fin N, Tendsto (fun β => hit β l) atTop (𝓝 (jumpTime model T l.succ))) ∧
        (∀ l : Fin N, Tendsto (fun β => complete β l) atTop (𝓝 (jumpTime model T l.succ))) := by
  classical
  obtain ⟨K, hK, B, hB, hcascade⟩ :=
    GeometricCascade.geometric_cascade T hN C hC κ hκ model CStar hCStar
  refine ⟨K, hK, B, hB, ?_⟩
  intro X hX hvisible i j hi hj
  have hκ0 : 0 < κ := (by norm_num : (0 : ℝ) < 4).trans
    ((PlateauStability.kappaThreshold_gt_four n).trans hκ)
  have hC0 : 0 < CStar := (div_pos (mul_pos (by norm_num) hκ0)
    (BlockContraction.contraction_constant_pos n (TreeDynamics.particle_pos T))).trans hCStar
  have hclock : ∀ β : ℝ, ∃ clock : ℝ → ℝ,
      ∀ hb : 1 < β, ClockRelation β (X β) (CStar * β) clock := by
    intro β
    by_cases hb : 1 < β
    · obtain ⟨clock, hc⟩ := GeneralClock.exists_clockRelation β hb (X β) (hX β hb)
        (CStar * β) (mul_nonneg hC0.le (zero_lt_one.trans hb).le)
      exact ⟨clock, fun _ => hc⟩
    · exact ⟨fun _ => 0, fun h => (hb h).elim⟩
  choose clock hc using hclock
  have htimes := fun β : {β : ℝ // B ≤ β} =>
    (hcascade β.val β.property (X β.val) (hX β.val (hB.trans_le β.property))
      (hvisible β.val (hB.trans_le β.property))).2
      (clock β.val) (hc β.val (hB.trans_le β.property)) i j hi hj
  choose s hit complete hprops using htimes
  let S : ℝ → Fin (N + 1) → ℝ := fun β => if hb : B ≤ β then s ⟨β, hb⟩ else fun _ => 0
  let H : ℝ → Fin N → ℝ := fun β => if hb : B ≤ β then hit ⟨β, hb⟩ else fun _ => 0
  let F : ℝ → Fin N → ℝ := fun β => if hb : B ≤ β then complete ⟨β, hb⟩ else fun _ => 0
  refine ⟨clock, hc, S, H, F, ?_, ?_, ?_, ?_⟩
  · intro β hb
    simpa only [S, H, F, dif_pos hb] using hprops ⟨β, hb⟩
  · intro r
    apply time_limit_of_error _ _ K
    filter_upwards [eventually_ge_atTop B] with β hb
    have hh := (hprops ⟨β, hb⟩).2.2.2.1 r
    simpa only [S, dif_pos hb] using hh
  · intro l
    apply time_limit_of_error _ _ K
    filter_upwards [eventually_ge_atTop B] with β hb
    obtain ⟨_, _, _, _, _, hh, _, _⟩ := (hprops ⟨β, hb⟩).2.2.2.2.1 l
    simpa only [H, dif_pos hb] using hh
  · intro l
    apply time_limit_of_error _ _ K
    filter_upwards [eventually_ge_atTop B] with β hb
    obtain ⟨_, _, _, _, _, _, hh, _⟩ := (hprops ⟨β, hb⟩).2.2.2.2.1 l
    simpa only [F, dif_pos hb] using hh

end Metastability.GeometricCascadeFamily
