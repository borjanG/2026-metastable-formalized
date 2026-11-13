import Metastability.CapDrift
import Mathlib.Topology.Order.Monotone

/-!
# Stopped cap drift and simultaneous no-exit

The stopped exterior-separation hypothesis is imposed only before the first
exit. The endpoint is inserted into the exit set, encoding the usual truncated
first-exit convention even when the set of exits is empty.
-/

noncomputable section
open Set
open scoped RealInnerProductSpace

namespace Metastability.CapNoExit

variable {n d : ℕ}

/-- Truncated first exit from finitely many closed scalar lower barriers. -/
def finiteExit {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ) (R : ι → ℝ)
    (a b : ℝ) : ℝ :=
  sInf (insert b {u | u ∈ Icc a b ∧ ∃ i ∈ s, f i u < R i})

theorem finiteExit_bounds {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ) (R : ι → ℝ)
    {a b : ℝ} (hab : a ≤ b) : finiteExit s f R a b ∈ Icc a b := by
  have hbelow : BddBelow (insert b {u | u ∈ Icc a b ∧ ∃ i ∈ s, f i u < R i}) := by
    refine ⟨a, ?_⟩
    rintro u (rfl | hu)
    · exact hab
    · exact hu.1.1
  refine ⟨le_csInf ⟨b, mem_insert _ _⟩ ?_, csInf_le hbelow (mem_insert _ _)⟩
  rintro u (rfl | hu)
  · exact hab
  · exact hu.1.1

theorem le_of_before_finiteExit {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (R : ι → ℝ) {a b u : ℝ} (hab : a ≤ b)
    (hu : u ∈ Ico a (finiteExit s f R a b)) : ∀ i ∈ s, R i ≤ f i u := by
  have hex := finiteExit_bounds s f R hab
  have hbelow : BddBelow (insert b {v | v ∈ Icc a b ∧ ∃ i ∈ s, f i v < R i}) := by
    refine ⟨a, ?_⟩
    rintro v (rfl | hv)
    · exact hab
    · exact hv.1.1
  intro i hi
  by_contra h
  have hle : finiteExit s f R a b ≤ u := csInf_le hbelow
    (mem_insert_of_mem _ ⟨⟨hu.1, hu.2.le.trans hex.2⟩, i, hi, lt_of_not_ge h⟩)
  exact (not_le.mpr hu.2) hle

/-- If every branch is strictly inside at the truncated first exit, that exit
is the right endpoint. Continuity is needed only on the stated interval. -/
theorem finiteExit_eq_end_of_strict {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f : ι → ℝ → ℝ) (R : ι → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hc : ∀ i ∈ s, ContinuousOn (f i) (Icc a b))
    (hstrict : ∀ i ∈ s, R i < f i (finiteExit s f R a b)) :
    finiteExit s f R a b = b := by
  let μ : ℝ → ℝ := fun u => s.inf' hs (fun i => f i u - R i)
  let Z : Set ℝ := Icc a b ∩ μ ⁻¹' Iic 0
  have hμ : ContinuousOn μ (Icc a b) :=
    ContinuousOn.finset_inf'_apply hs (fun i hi => (hc i hi).sub continuousOn_const)
  have hZ : IsClosed Z := hμ.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hbelow : BddBelow (insert b {u | u ∈ Icc a b ∧ ∃ i ∈ s, f i u < R i}) := by
    refine ⟨a, ?_⟩
    rintro u (rfl | hu)
    · exact hab
    · exact hu.1.1
  have hclosure : finiteExit s f R a b ∈
      closure (insert b {u | u ∈ Icc a b ∧ ∃ i ∈ s, f i u < R i}) :=
    csInf_mem_closure ⟨b, mem_insert _ _⟩ hbelow
  have hsub : insert b {u | u ∈ Icc a b ∧ ∃ i ∈ s, f i u < R i} ⊆ insert b Z := by
    rintro u (rfl | ⟨hu, i, hi, hfi⟩)
    · exact mem_insert _ _
    · apply mem_insert_of_mem
      exact ⟨hu, (Finset.inf'_le (fun j => f j u - R j) hi).trans (sub_nonpos.mpr hfi.le)⟩
  have hclosed : IsClosed (insert b Z) := by
    rw [insert_eq]
    exact isClosed_singleton.union hZ
  have hmem : finiteExit s f R a b ∈ insert b Z :=
    hclosed.closure_subset_iff.mpr hsub hclosure
  rcases hmem with heq | hz
  · exact heq
  · have hpos : 0 < μ (finiteExit s f R a b) :=
      (Finset.lt_inf'_iff hs).mpr (fun i hi => sub_pos.mpr (hstrict i hi))
    exact False.elim ((not_lt_of_ge hz.2) hpos)

/-- Literal angular distance from a point to a nonempty spherical cap. -/
def pointCapDistance (x : Source.Sphere d) (C : Source.SphericalCap d) : ℝ :=
  sInf {r | ∃ y ∈ C.carrier, r = Source.angularDist x y}

theorem le_pointCapDistance_iff (x : Source.Sphere d) (C : Source.SphericalCap d) (σ : ℝ) :
    σ ≤ pointCapDistance x C ↔ ∀ y ∈ C.carrier, σ ≤ Source.angularDist x y := by
  have hne : ({r | ∃ y ∈ C.carrier, r = Source.angularDist x y} : Set ℝ).Nonempty :=
    ⟨Source.angularDist x C.center, C.center, AngularGeometry.cap_center_mem C, rfl⟩
  have hbelow : BddBelow ({r | ∃ y ∈ C.carrier, r = Source.angularDist x y} : Set ℝ) := by
    refine ⟨0, ?_⟩
    rintro r ⟨y, _, rfl⟩
    exact AngularGeometry.angularDist_nonneg x y
  constructor
  · intro h y hy
    exact h.trans (csInf_le hbelow ⟨y, hy, rfl⟩)
  · intro h
    apply le_csInf hne
    rintro r ⟨y, hy, rfl⟩
    exact h y hy

/-- First exit of a block from a closed cap, truncated at `b`. -/
def capExit (X : ℝ → Source.Configuration n d) (A : Source.Block n)
    (C : Source.SphericalCap d) (a b : ℝ) : ℝ :=
  finiteExit A (fun i u => ⟪(X u i).val, C.center.val⟫) (fun _ => Real.cos C.radius) a b

theorem capExit_eq_angular (X : ℝ → Source.Configuration n d) (A : Source.Block n)
    (C : Source.SphericalCap d) (a b : ℝ) :
    capExit X A C a b = sInf (insert b {u | u ∈ Icc a b ∧ ∃ i ∈ A, X u i ∉ C.carrier}) := by
  unfold capExit finiteExit
  congr 2
  ext u
  simp only [mem_setOf_eq, AngularGeometry.cap_mem_iff_inner, not_le]

theorem mem_cap_before_exit (X : ℝ → Source.Configuration n d) (A : Source.Block n)
    (C : Source.SphericalCap d) {a b u : ℝ} (hab : a ≤ b)
    (hu : u ∈ Ico a (capExit X A C a b)) : ∀ i ∈ A, X u i ∈ C.carrier := by
  intro i hi
  apply (AngularGeometry.cap_mem_iff_inner C _).mpr
  exact le_of_before_finiteExit A _ _ hab hu i hi

/-- The manuscript's stopped drift estimate, with the explicit common constant
`2n`. The enlarged cap has radius `C.radius`; thus its enlargement is
`C.radius - r > 0`. No cap confinement or coordinate positivity is assumed. -/
theorem cap_drift_stopped (model : Source.Model) (β : ℝ) (hβ : 0 ≤ β)
    (X : ℝ → Source.Configuration n d) (hX : Source.Solves model β X)
    (A : Source.Block n) (hA : A.Nonempty) (C : Source.SphericalCap d)
    (a b r σ : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hr0 : 0 ≤ r)
    (hrC : r < C.radius) (hσ : 0 < σ)
    (hinitial : ∀ i ∈ A, Source.angularDist (X a i) C.center ≤ r)
    (hsep : ∀ u ∈ Ico a (capExit X A C a b), ∀ k ∉ A,
      σ ≤ pointCapDistance (X u k) C)
    {t : ℝ} (ht : t ∈ Icc a (capExit X A C a b)) :
    ∀ i ∈ A, Real.cos r - (2 * n) * (t - a) * Real.exp (-β * (1 - Real.cos σ)) ≤
      ⟪(X t i).val, C.center.val⟫ := by
  have hrπ : r ≤ Real.pi := hrC.le.trans
    (C.radius_lt_half_pi.le.trans (by linarith only [Real.pi_pos]))
  apply CapDrift.cap_drift_on_interval X hX hβ A hA C.center a
    (capExit X A C a b) r (1 - Real.cos σ) ha hr0 hrπ hinitial
  · intro u hu i hi
    exact (AngularGeometry.cap_cos_radius_pos C).le.trans
      ((AngularGeometry.cap_mem_iff_inner C _).mp (mem_cap_before_exit X A C hab hu i hi))
  · intro u hu i hi k hk
    have hdist := (le_pointCapDistance_iff (X u k) C σ).mp (hsep u hu k hk)
      (X u i) (mem_cap_before_exit X A C hab hu i hi)
    rw [AngularGeometry.angularDist_comm (X u k)] at hdist
    have hcos := Real.cos_le_cos_of_nonneg_of_le_pi hσ.le
      (AngularGeometry.angularDist_le_pi (X u i) (X u k)) hdist
    rw [AngularGeometry.cos_angularDist] at hcos
    linarith only [hcos]
  · exact ht

/-- The finite-minimum formulation appearing in the manuscript. -/
theorem minimum_cap_drift_stopped (model : Source.Model) (β : ℝ) (hβ : 0 ≤ β)
    (X : ℝ → Source.Configuration n d) (hX : Source.Solves model β X)
    (A : Source.Block n) (hA : A.Nonempty) (C : Source.SphericalCap d)
    (a b r σ : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hr0 : 0 ≤ r)
    (hrC : r < C.radius) (hσ : 0 < σ)
    (hinitial : ∀ i ∈ A, Source.angularDist (X a i) C.center ≤ r)
    (hsep : ∀ u ∈ Ico a (capExit X A C a b), ∀ k ∉ A,
      σ ≤ pointCapDistance (X u k) C)
    {t : ℝ} (ht : t ∈ Icc a (capExit X A C a b)) :
    Real.cos r - (2 * n) * (t - a) * Real.exp (-β * (1 - Real.cos σ)) ≤
      A.inf' hA (fun i => ⟪(X t i).val, C.center.val⟫) :=
  Finset.le_inf' hA _ (cap_drift_stopped model β hβ X hX A hA C a b r σ
    ha hab hr0 hrC hσ hinitial hsep ht)

/-- Strictly insufficient accumulated exterior drift prevents cap exit,
including at the interval endpoint. This uses separation only before exit. -/
theorem cap_no_exit (model : Source.Model) (β : ℝ) (hβ : 0 ≤ β)
    (X : ℝ → Source.Configuration n d) (hX : Source.Solves model β X)
    (A : Source.Block n) (hA : A.Nonempty) (C : Source.SphericalCap d)
    (a b r σ : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hr0 : 0 ≤ r)
    (hrC : r < C.radius) (hσ : 0 < σ)
    (hinitial : ∀ i ∈ A, Source.angularDist (X a i) C.center ≤ r)
    (hsep : ∀ u ∈ Ico a (capExit X A C a b), ∀ k ∉ A,
      σ ≤ pointCapDistance (X u k) C)
    (herror : (2 * n) * (b - a) * Real.exp (-β * (1 - Real.cos σ)) <
      Real.cos r - Real.cos C.radius) :
    capExit X A C a b = b ∧ ∀ t ∈ Icc a b, ∀ i ∈ A, X t i ∈ C.carrier := by
  have hex := finiteExit_bounds A
    (fun i u => ⟪(X u i).val, C.center.val⟫) (fun _ => Real.cos C.radius) hab
  change capExit X A C a b ∈ Icc a b at hex
  have hstrict : ∀ t ∈ Icc a (capExit X A C a b), ∀ i ∈ A,
      Real.cos C.radius < ⟪(X t i).val, C.center.val⟫ := by
    intro t ht i hi
    have hbound := cap_drift_stopped model β hβ X hX A hA C a b r σ
      ha hab hr0 hrC hσ hinitial hsep ht i hi
    have herr : (2 * n) * (t - a) * Real.exp (-β * (1 - Real.cos σ)) ≤
        (2 * n) * (b - a) * Real.exp (-β * (1 - Real.cos σ)) := by
      gcongr
      exact ht.2.trans hex.2
    linarith only [hbound, herr, herror]
  have heq : capExit X A C a b = b :=
    finiteExit_eq_end_of_strict A hA _ _ hab
      (fun i _ => CapDrift.coordinate_continuousOn X hX C.center i a b ha)
      (hstrict _ ⟨hex.1, le_rfl⟩)
  refine ⟨heq, ?_⟩
  intro t ht i hi
  apply (AngularGeometry.cap_mem_iff_inner C _).mpr
  exact (hstrict t (heq.symm ▸ ht) i hi).le

/-- Simultaneous no-exit for a finite family of blocks. The exterior barrier is
required only when all blocks currently lie in their enlarged caps. In
particular it can be deduced from pairwise separation of those fixed caps. -/
theorem simultaneous_cap_no_exit {ι : Type*} [Fintype ι]
    (model : Source.Model) (β : ℝ) (hβ : 0 ≤ β)
    (X : ℝ → Source.Configuration n d) (hX : Source.Solves model β X)
    (A : ι → Source.Block n) (hA : ∀ k, (A k).Nonempty) (w : ι → Source.Sphere d)
    (a b r R L : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hr0 : 0 ≤ r)
    (hrR : r < R) (hRπ : R < Real.pi / 2)
    (hinitial : ∀ k, ∀ i ∈ A k, Source.angularDist (X a i) (w k) ≤ r)
    (hsep : ∀ u ∈ Ico a b,
      (∀ k, ∀ i ∈ A k, Source.angularDist (X u i) (w k) ≤ R) →
      ∀ k, ∀ i ∈ A k, ∀ j ∉ A k, L ≤ 1 - ⟪(X u i).val, (X u j).val⟫)
    (herror : (2 * n) * (b - a) * Real.exp (-β * L) < Real.cos r - Real.cos R) :
    ∀ t ∈ Icc a b, ∀ k, ∀ i ∈ A k,
      Source.angularDist (X t i) (w k) ≤ R ∧
      Real.cos r - (2 * n) * (t - a) * Real.exp (-β * L) ≤ ⟪(X t i).val, (w k).val⟫ := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl he => exact fun _ _ k => isEmptyElim k
  | inr hne =>
    let s : Finset (Σ _ : ι, Fin n) := Finset.univ.sigma A
    have hs : s.Nonempty := by
      obtain ⟨k⟩ := hne
      obtain ⟨i, hi⟩ := hA k
      exact ⟨⟨k, i⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ _, hi⟩⟩
    let f : (Σ _ : ι, Fin n) → ℝ → ℝ := fun p u => ⟪(X u p.2).val, (w p.1).val⟫
    let e : ℝ := finiteExit s f (fun _ => Real.cos R) a b
    have he : e ∈ Icc a b := finiteExit_bounds s f (fun _ => Real.cos R) hab
    have hR0 : 0 ≤ R := hr0.trans hrR.le
    have hRpi : R ≤ Real.pi := hRπ.le.trans (by linarith only [Real.pi_pos])
    have hrpi : r ≤ Real.pi := hrR.le.trans hRpi
    have hcosR : 0 < Real.cos R := Real.cos_pos_of_mem_Ioo
      ⟨by linarith only [hR0, Real.pi_pos], hRπ⟩
    have hbefore : ∀ u ∈ Ico a e, ∀ k, ∀ i ∈ A k,
        Source.angularDist (X u i) (w k) ≤ R := by
      intro u hu k i hi
      apply (AngularGeometry.angularDist_le_iff_inner _ _ hR0 hRpi).mpr
      exact le_of_before_finiteExit s f (fun _ => Real.cos R) hab hu ⟨k, i⟩
        (Finset.mem_sigma.mpr ⟨Finset.mem_univ _, hi⟩)
    have hdrift : ∀ t ∈ Icc a e, ∀ k, ∀ i ∈ A k,
        Real.cos r - (2 * n) * (t - a) * Real.exp (-β * L) ≤
          ⟪(X t i).val, (w k).val⟫ := by
      intro t ht k
      apply CapDrift.cap_drift_on_interval X hX hβ (A k) (hA k) (w k) a e r L
        ha hr0 hrpi (hinitial k)
      · intro u hu i hi
        exact hcosR.le.trans ((AngularGeometry.angularDist_le_iff_inner _ _ hR0 hRpi).mp
          (hbefore u hu k i hi))
      · intro u hu i hi j hj
        have hb := hsep u ⟨hu.1, hu.2.trans_le he.2⟩ (hbefore u hu) k i hi j hj
        linarith only [hb]
      · exact ht
    have hstrict : ∀ t ∈ Icc a e, ∀ k, ∀ i ∈ A k,
        Real.cos R < ⟪(X t i).val, (w k).val⟫ := by
      intro t ht k i hi
      have hbound := hdrift t ht k i hi
      have herr : (2 * n) * (t - a) * Real.exp (-β * L) ≤
          (2 * n) * (b - a) * Real.exp (-β * L) := by
        gcongr
        exact ht.2.trans he.2
      linarith only [hbound, herr, herror]
    have heq : e = b := finiteExit_eq_end_of_strict s hs f (fun _ => Real.cos R) hab
      (fun p _ => CapDrift.coordinate_continuousOn X hX (w p.1) p.2 a b ha)
      (fun p hp => hstrict e ⟨he.1, le_rfl⟩ p.1 p.2 (Finset.mem_sigma.mp hp).2)
    intro t ht k i hi
    have hte : t ∈ Icc a e := heq.symm ▸ ht
    exact ⟨(AngularGeometry.angularDist_le_iff_inner _ _ hR0 hRpi).mpr
      (hstrict t hte k i hi).le, hdrift t hte k i hi⟩

end Metastability.CapNoExit
