module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.List.Pairwise
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

/-!
# The Ramsey number of the three-edge tight path

This states the main Ramsey theorem in the manuscript by Abhishek Dhawan
and Abhishek Methuku. All logarithms are natural. The family H represents
the red triples; every other triple is blue. The alternatives are a red tight
path on five distinct vertices and a blue clique of order t. The positive
constant and the lower threshold for t are independent of the colouring.

The deliberate placeholder below specifies the target for Comparator.
The proof development must supply this exact declaration before submission.
-/

namespace TP3

variable {V : Type*} [DecidableEq V]

/-- A family containing only three-element edges. -/
def IsTripleSystem (H : Finset (Finset V)) : Prop :=
  ∀ e ∈ H, e.card = 3

/-- Three consecutive triples on five distinct vertices, as a subhypergraph. -/
def HasTightPath (H : Finset (Finset V)) : Prop :=
  ∃ a b c d e : V, [a, b, c, d, e].Pairwise (· ≠ ·) ∧
    {a, b, c} ∈ H ∧ {b, c, d} ∈ H ∧ {c, d, e} ∈ H

/-- Containing no red triple is equivalent to being a blue clique. -/
def Independent (H : Finset (Finset V)) (S : Finset V) : Prop :=
  ∀ e ∈ H, ¬ e ⊆ S

/-- For all sufficiently large t, some integer N at most C t² / log(log t)
has the Ramsey property for the three-edge tight path versus a t-clique. -/
theorem ramsey_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ t₀ : ℕ, 3 ≤ t₀ ∧
      ∀ t : ℕ, t₀ ≤ t →
        ∃ N : ℕ, (N : ℝ) ≤ C * (t : ℝ) ^ 2 / Real.log (Real.log (t : ℝ)) ∧
          ∀ H : Finset (Finset (Fin N)), IsTripleSystem H →
            HasTightPath H ∨
              ∃ S : Finset (Fin N), S.card = t ∧ Independent H S := by
  sorry

end TP3
