module

public import TP3.Conditioning

@[expose] public section

namespace TP3

open scoped BigOperators

variable {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

/-- The experiment within one class after fixing all previous choices.
Each required set has one shared mark. Each vertex also has its own
independent acceptance coin, whose probability compensates for its marks.
Only eligible vertices are to be tested using this experiment. -/
noncomputable def classSelectionLaw (L : V → Finset U) (φ τ : ℝ)
    (hφ : 0 ≤ φ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (haccept : ∀ x, φ / τ^(L x).card ≤ 1) :
    FiniteLaw ((U → Bool) × (V → Bool)) :=
  (FiniteLaw.product fun _ : U => FiniteLaw.bernoulli τ hτ.le hτ1).staged
    (fun _ => FiniteLaw.product fun x : V =>
      FiniteLaw.bernoulli (φ / τ^(L x).card)
        (div_nonneg hφ (pow_nonneg hτ.le _)) (haccept x))

/-- Passing all vertex tests in W: every listed mark must be present,
and every independent vertex coin must succeed. -/
def classTests (L : V → Finset U) (W : Finset V)
    (ω : (U → Bool) × (V → Bool)) : Prop :=
  (∀ x ∈ W, ∀ u ∈ L x, ω.1 u = true) ∧ (∀ x ∈ W, ω.2 x = true)

/-- Exact probability of all class tests, allowing shared marks. -/
theorem classTests_probability (L : V → Finset U) (φ τ : ℝ)
    (hφ : 0 ≤ φ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (haccept : ∀ x, φ / τ^(L x).card ≤ 1)
    (W : Finset V) :
    (classSelectionLaw L φ τ hφ hτ hτ1 haccept).event (classTests L W) =
      τ ^ (W.biUnion L).card * ∏ x ∈ W, (φ / τ^(L x).card) := by
  classical
  unfold classSelectionLaw classTests
  rw [FiniteLaw.independent_events _ _
    (fun ω : U → Bool => ∀ x ∈ W, ∀ u ∈ L x, ω u = true)
    (fun ω : V → Bool => ∀ x ∈ W, ω x = true)]
  have hmarks :
      (fun ω : U → Bool => ∀ x ∈ W, ∀ u ∈ L x, ω u = true) =
        (fun ω => ∀ u ∈ W.biUnion L, ω u = true) := by
    funext ω
    apply propext
    constructor
    · intro h u hu
      obtain ⟨x,hx,hu⟩ := Finset.mem_biUnion.mp hu
      exact h x hx u hu
    · intro h x hx u hu
      exact h u (Finset.mem_biUnion.mpr ⟨x,hx,hu⟩)
  rw [hmarks, FiniteLaw.bernoulli_required, FiniteLaw.bernoulli_required]
  simp only [Finset.prod_const]

/-- With disjoint lists, the compensation gives exactly φ per vertex.
This theorem does not assume that vertices with overlapping lists are
independent. Those cases require the manuscript's separate deletion and
collision estimates. -/
theorem classTests_disjoint_probability (L : V → Finset U) (φ τ : ℝ)
    (hφ : 0 ≤ φ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (haccept : ∀ x, φ / τ^(L x).card ≤ 1)
    (W : Finset V) (hdis : (W : Set V).PairwiseDisjoint L) :
    (classSelectionLaw L φ τ hφ hτ hτ1 haccept).event (classTests L W) =
      φ ^ W.card := by
  rw [classTests_probability]
  rw [Finset.card_biUnion hdis, Finset.prod_div_distrib]
  have hprod : (∏ x ∈ W, τ ^ (L x).card) = τ ^ (∑ x ∈ W, (L x).card) := by
    rw [Finset.prod_pow_eq_pow_sum]
  rw [hprod, Finset.prod_const]
  have hnonzero : τ ^ (∑ x ∈ W, (L x).card) ≠ 0 := pow_ne_zero _ hτ.ne'
  field_simp

end TP3
