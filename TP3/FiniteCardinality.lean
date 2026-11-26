module

public import TP3.FiniteCounting

@[expose] public section

namespace TP3.FiniteLaw

attribute [local instance] Classical.propDecidable

open scoped BigOperators

variable {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]

/-- Expected cardinality is the sum of the individual inclusion probabilities.
No independence assumption is used. -/
theorem mean_card (μ : FiniteLaw Ω) (C : Ω → Finset V) :
    μ.mean (fun ω => ((C ω).card : ℝ)) = ∑ x, μ.event (fun ω => x ∈ C ω) := by
  classical
  have hc (ω : Ω) : ((C ω).card : ℝ) =
      ∑ x : V, if x ∈ C ω then (1 : ℝ) else 0 := by simp
  simp_rw [hc]
  rw [μ.mean_sum]
  simp_rw [μ.mean_indicator]

theorem mean_filter_card (μ : FiniteLaw Ω) (A : Finset V) (P : V → Ω → Prop) :
    μ.mean (fun ω => ((A.filter (fun x => P x ω)).card : ℝ)) =
      ∑ x ∈ A, μ.event (P x) := by
  classical
  have hc (ω : Ω) : ((A.filter (fun x => P x ω)).card : ℝ) =
      ∑ x ∈ A, if P x ω then (1 : ℝ) else 0 := by simp [Finset.sum_filter]
  simp_rw [hc]
  rw [μ.mean_sum]
  simp_rw [μ.mean_indicator]

end TP3.FiniteLaw
