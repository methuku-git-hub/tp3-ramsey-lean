module

public import TP3.WitnessCounts

@[expose] public section

namespace TP3.DependentSample.Data

attribute [local instance] Classical.propDecidable

variable {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
variable (d : Data V U)

/-- The principal pointwise sampling estimate. Its error terms count
respectively one and two additional supporting vertices. All probabilities
refer to the actual adaptive process, including the conflict deletions. -/
theorem chosen_probability (W : Finset V)
    (hW : FourVertexProperty d.triples W)
    (h : ℕ) (g : ℝ)
    (hinc : ∀ y M, (d.listing y M).card ≤ h)
    (hdeg : ∀ x, ((d.neighbors x).card : ℝ) ≤ g)
    (q τ : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    (historyLaw (finiteClassLaw d.maxListSize q τ hq hq1 hτ hτ1) d.classes).event
      (fun ξ => W ⊆ (d.run d.classes ξ).chosen) ≤
      (q*τ^d.maxListSize)^W.card + (W.card : ℝ)^2 *
        ((W.card : ℝ)*d.listBound*h*q^(W.card+1) +
          g*d.listBound*h*q^(W.card+2)) := by
  let μ := historyLaw (finiteClassLaw (V := V) (U := U) d.maxListSize q τ hq hq1 hτ hτ1) d.classes
  let C := fun ξ => (d.run d.classes ξ).chosen
  let P := fun ξ => ∃ j ∈ d.smallIndices W, smallSupport W j ⊆ C ξ
  let Q := fun ξ => ∃ j ∈ d.largeIndices W, largeSupport W j ⊆ C ξ
  have hcoarse : ∀ A, μ.event (fun ξ => A ⊆ C ξ) ≤ q^A.card :=
    fun A => d.chosen_coarse_probability A q τ hq hq1 hτ hτ1
  have hP : μ.event P ≤ (W.card : ℝ)^3*d.listBound*h*q^(W.card+1) := by
    apply le_trans (μ.exists_support_probability C (d.smallIndices W) (smallSupport W)
      q (W.card+1) hcoarse (d.small_support_card W))
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hq _)
    exact_mod_cast d.small_indices_card W h hinc
  have hQ : μ.event Q ≤ (W.card : ℝ)^2*g*d.listBound*h*q^(W.card+2) := by
    apply le_trans (μ.exists_support_probability C (d.largeIndices W) (largeSupport W)
      q (W.card+2) hcoarse (d.large_support_card W))
    exact mul_le_mul_of_nonneg_right (d.large_indices_card W h g hinc hdeg) (pow_nonneg hq _)
  calc
    _ ≤ μ.event (fun ξ => d.Good W d.classes ξ ∨ (P ξ ∨ Q ξ)) := by
      apply FiniteLaw.event_mono
      intro ξ hchosen
      by_cases hg : d.Good W d.classes ξ
      · exact Or.inl hg
      · exact Or.inr (d.witness_has_support W (C ξ) hchosen
          (d.final_not_good_witness W hW ξ hchosen hg))
    _ ≤ μ.event (d.Good W d.classes) + μ.event (fun ξ => P ξ ∨ Q ξ) :=
      μ.event_or_le _ _
    _ ≤ (q*τ^d.maxListSize)^W.card +
        ((W.card : ℝ)^3*d.listBound*h*q^(W.card+1) +
          (W.card : ℝ)^2*g*d.listBound*h*q^(W.card+2)) :=
      add_le_add (d.good_probability W q τ hq hq1 hτ hτ1)
        ((μ.event_or_le P Q).trans (add_le_add hP hQ))
    _ = _ := by ring

end TP3.DependentSample.Data
