module

public import TP3.Conditioning
public import Mathlib.Order.Interval.Finset.Fin

@[expose] public section

namespace TP3

open scoped BigOperators

variable {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

/-- One class uses fresh set marks, independent q-coins for the vertices,
and independent auxiliary trials for each vertex. -/
abbrev ClassNoise (V U : Type*) (m : ℕ) :=
  (U → Bool) × ((V → Bool) × (V → Fin (m+1) → Bool))

/-- A vertex with a list of size l requires m-l auxiliary successes.
The extra index in Fin (m+1) makes the endpoint uniform, including l=0. -/
def auxiliaryIndices (m l : ℕ) : Finset (Fin (m+1)) :=
  Finset.Iio ⟨m-l,Nat.lt_succ_of_le (Nat.sub_le m l)⟩

@[simp] theorem auxiliaryIndices_card (m l : ℕ) :
    (auxiliaryIndices m l).card = m-l := by
  simp [auxiliaryIndices]

noncomputable def finiteClassLaw (m : ℕ) (q τ : ℝ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    FiniteLaw (ClassNoise V U m) :=
  (FiniteLaw.product fun _ : U => FiniteLaw.bernoulli τ hτ hτ1).staged
    (fun _ =>
      (FiniteLaw.product fun _ : V => FiniteLaw.bernoulli q hq hq1).staged
        (fun _ => FiniteLaw.product fun _ : V =>
          FiniteLaw.product fun _ : Fin (m+1) => FiniteLaw.bernoulli τ hτ hτ1))

/-- The fresh trials used by one eligible vertex after its list is fixed. -/
def finiteClassPass (m : ℕ) (L : V → Finset U) (x : V)
    (ω : ClassNoise V U m) : Prop :=
  (∀ u ∈ L x, ω.1 u = true) ∧ ω.2.1 x = true ∧
    ∀ j ∈ auxiliaryIndices m (L x).card, ω.2.2 x j = true

theorem auxiliary_success_probability (m : ℕ) (L : V → Finset U)
    (W : Finset V) (τ : ℝ) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    (FiniteLaw.product fun _ : V =>
      FiniteLaw.product fun _ : Fin (m+1) => FiniteLaw.bernoulli τ hτ hτ1).event
        (fun ω => ∀ x ∈ W, ∀ j ∈ auxiliaryIndices m (L x).card, ω x j = true) =
      ∏ x ∈ W, τ ^ (m-(L x).card) := by
  classical
  rw [FiniteLaw.product_event _
    (fun (x : V) (ω : Fin (m+1) → Bool) =>
      x ∈ W → ∀ j ∈ auxiliaryIndices m (L x).card, ω j = true)]
  have hi (x : V) :
      (FiniteLaw.product fun _ : Fin (m+1) => FiniteLaw.bernoulli τ hτ hτ1).event
        (fun ω => x ∈ W → ∀ j ∈ auxiliaryIndices m (L x).card, ω j = true) =
      if x ∈ W then τ ^ (m-(L x).card) else 1 := by
    by_cases hx : x ∈ W
    · simp only [hx, true_implies, ite_true]
      rw [FiniteLaw.bernoulli_required]
      simp
    · simp only [hx, false_implies, ite_false]
      rw [← FiniteLaw.mean_indicator]
      simp only [ite_true]
      exact FiniteLaw.mean_const _ 1
  simp_rw [hi]
  exact Finset.prod_ite_mem_eq W _

/-- Exact joint probability for fixed lists, before any conflict deletion. -/
theorem finiteClassPass_probability (m : ℕ) (L : V → Finset U) (W : Finset V)
    (q τ : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    (finiteClassLaw m q τ hq hq1 hτ hτ1).event
      (fun ω => ∀ x ∈ W, finiteClassPass m L x ω) =
      τ ^ (W.biUnion L).card *
        (q ^ W.card * ∏ x ∈ W, τ ^ (m-(L x).card)) := by
  classical
  have heq : (fun ω : ClassNoise V U m => ∀ x ∈ W, finiteClassPass m L x ω) =
      (fun ω => (∀ u ∈ W.biUnion L, ω.1 u = true) ∧
        ((∀ x ∈ W, ω.2.1 x = true) ∧
          ∀ x ∈ W, ∀ j ∈ auxiliaryIndices m (L x).card, ω.2.2 x j = true)) := by
    funext ω
    apply propext
    constructor
    · intro h
      refine ⟨?_,⟨fun x hx => (h x hx).2.1,fun x hx => (h x hx).2.2⟩⟩
      intro u hu
      obtain ⟨x,hx,hu⟩ := Finset.mem_biUnion.mp hu
      exact (h x hx).1 u hu
    · rintro ⟨hm,hq,ha⟩ x hx
      refine ⟨?_,hq x hx,ha x hx⟩
      intro u hu
      exact hm u (Finset.mem_biUnion.mpr ⟨x,hx,hu⟩)
  rw [heq]
  unfold finiteClassLaw
  rw [FiniteLaw.independent_events _ _
    (fun ω : U → Bool => ∀ u ∈ W.biUnion L, ω u = true)
    (fun ω : (V → Bool) × (V → Fin (m+1) → Bool) => (∀ x ∈ W, ω.1 x = true) ∧
      ∀ x ∈ W, ∀ j ∈ auxiliaryIndices m (L x).card, ω.2 x j = true)]
  rw [FiniteLaw.independent_events _ _
    (fun ω : V → Bool => ∀ x ∈ W, ω x = true)
    (fun ω : V → Fin (m+1) → Bool =>
      ∀ x ∈ W, ∀ j ∈ auxiliaryIndices m (L x).card, ω x j = true)]
  rw [FiniteLaw.bernoulli_required, FiniteLaw.bernoulli_required,
    auxiliary_success_probability]
  simp

/-- Disjoint lists give independent-sampling probabilities with
φ = q τ^m, even though the experiment also handles overlapping lists. -/
theorem finiteClassPass_disjoint (m : ℕ) (L : V → Finset U) (W : Finset V)
    (q τ : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hsize : ∀ x ∈ W, (L x).card ≤ m)
    (hdis : (W : Set V).PairwiseDisjoint L) :
    (finiteClassLaw m q τ hq hq1 hτ hτ1).event
      (fun ω => ∀ x ∈ W, finiteClassPass m L x ω) =
      (q*τ^m)^W.card := by
  rw [finiteClassPass_probability, Finset.card_biUnion hdis]
  rw [← Finset.prod_pow_eq_pow_sum]
  calc
    _ = q^W.card * (∏ x ∈ W, (τ^(L x).card * τ^(m-(L x).card))) := by
      rw [Finset.prod_mul_distrib]
      ring
    _ = q^W.card * (∏ _x ∈ W, τ^m) := by
      congr 1
      apply Finset.prod_congr rfl
      intro x hx
      rw [← pow_add, Nat.add_sub_of_le (hsize x hx)]
    _ = _ := by simp [mul_pow]

/-- The independent q-coins do not depend on lists, eligibility, or
deletions. They dominate every tentative choice in the same class. -/
theorem finiteClass_envelope_probability (m : ℕ) (W : Finset V)
    (q τ : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    (finiteClassLaw (V := V) (U := U) m q τ hq hq1 hτ hτ1).event
      (fun ω => ∀ x ∈ W, ω.2.1 x = true) = q^W.card := by
  unfold finiteClassLaw
  rw [FiniteLaw.staged_event_second _ _
    (fun ω : (V → Bool) × (V → Fin (m+1) → Bool) => ∀ x ∈ W, ω.1 x = true)]
  rw [FiniteLaw.staged_event_first _ _ (fun ω : V → Bool => ∀ x ∈ W, ω x = true)]
  rw [FiniteLaw.bernoulli_required]
  simp

end TP3
