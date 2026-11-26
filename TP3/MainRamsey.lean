module

public import TP3.MainIndependence

@[expose] public section

namespace TP3

/-- The unconditional Ramsey bound for the three-edge tight path.
This has exactly the statement specified in Challenge.lean. -/
theorem ramsey_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ t₀ : ℕ, 3 ≤ t₀ ∧
      ∀ t : ℕ, t₀ ≤ t →
        ∃ N : ℕ, (N : ℝ) ≤ C * (t : ℝ) ^ 2 / Real.log (Real.log (t : ℝ)) ∧
          ∀ H : Finset (Finset (Fin N)), IsTripleSystem H →
            HasTightPath H ∨
              ∃ S : Finset (Fin N), S.card = t ∧ Independent H S :=
  ramsey_bound_of_independence_bound independence_bound

end TP3
