module

public import TP3.FinalSample

@[expose] public section

namespace TP3.DependentSample.Data

attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
variable (d : Data V U)

theorem mean_within_class_loss (h : ℕ) (g : ℝ)
    (hinc : ∀ y M, (d.listing y M).card ≤ h)
    (hdeg : ∀ x, ((d.neighbors x).card : ℝ) ≤ g)
    (q τ : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    (historyLaw (finiteClassLaw d.maxListSize q τ hq hq1 hτ hτ1) d.classes).mean
      (fun ξ => ((d.remainingWithinPairs d.classes ξ).card : ℝ)) ≤
        (d.withinClassPairs.card : ℝ) * ((q*τ^d.maxListSize)^2 +
          4*(2*d.listBound*h*q^3 + g*d.listBound*h*q^4)) := by
  let μ := historyLaw (finiteClassLaw (V := V) (U := U) d.maxListSize q τ hq hq1 hτ hτ1) d.classes
  change μ.mean (fun ξ => ((d.withinClassPairs.filter
    (fun e => e ⊆ d.unmarked d.classes ξ)).card : ℝ)) ≤ _
  have hmean := μ.mean_filter_card d.withinClassPairs
    (fun (e : Finset V) (ξ : History (ClassNoise V U d.maxListSize) d.classes) =>
      e ⊆ d.unmarked d.classes ξ)
  calc
    _ = ∑ e ∈ d.withinClassPairs, μ.event (fun ξ => e ⊆ d.unmarked d.classes ξ) := by
      convert hmean using 1
      congr 1
      funext ξ
      congr 1
      congr 1
      ext e
      simp
    _ ≤ _ := ?_
  calc
    _ ≤ ∑ _e ∈ d.withinClassPairs, ((q*τ^d.maxListSize)^2 +
        4*(2*d.listBound*h*q^3 + g*d.listBound*h*q^4)) := by
      apply Finset.sum_le_sum
      intro e he
      have hcard := d.withinClassPairs_card he
      have hp := d.chosen_probability e (fourVertexProperty_small d.triples e (by omega))
        h g hinc hdeg q τ hq hq1 hτ hτ1
      apply le_trans (μ.event_mono (fun ξ heξ => heξ.trans (d.unmarked_subset d.classes ξ)))
      norm_num only [hcard,Nat.cast_ofNat] at hp
      exact hp
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- The complete expected-size estimate for the constructed random set.
The four losses are eligibility, conflicts, marked sets, and graph edges
inside classes. Every term is proved for the actual dependent law. -/
theorem mean_finalSet_size (hH : IsTripleSystem d.triples)
    (hsym : ∀ a b, d.lists a b = d.lists b a) (hR : 0 < d.classes)
    (h r : ℕ) (g : ℝ)
    (hinc : ∀ y M, (d.listing y M).card ≤ h)
    (hr : ∀ x, (d.setIncidences x).card ≤ r)
    (hdeg : ∀ x, ((d.neighbors x).card : ℝ) ≤ g)
    (q τ : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    let φ := q*τ^d.maxListSize
    (Fintype.card V : ℝ)*φ*(1-g*φ/d.classes) -
      (3*(Fintype.card V : ℝ)*g*d.listBound*h*q^3 +
        162*(d.triples.card : ℝ)*d.listBound*h*q^4) -
      (Fintype.card V : ℝ)*r*(d.classes*τ*φ + h*φ^2) -
      (d.withinClassPairs.card : ℝ)*(φ^2 + 4*(2*d.listBound*h*q^3 + g*d.listBound*h*q^4)) ≤
    (historyLaw (finiteClassLaw d.maxListSize q τ hq hq1 hτ hτ1) d.classes).mean
      (fun ξ => ((d.finalSet d.classes ξ).card : ℝ)) := by
  dsimp only
  let μ := historyLaw (finiteClassLaw (V := V) (U := U) d.maxListSize q τ hq hq1 hτ hτ1) d.classes
  have hchosen := d.mean_chosen_size hH hsym hR h g hinc hdeg q τ hq hq1 hτ hτ1
  have hmarked := d.mean_marked_vertices d.classes h r hinc hr q τ hq hq1 hτ hτ1
  have hwithin := d.mean_within_class_loss h g hinc hdeg q τ hq hq1 hτ hτ1
  have hdelete : μ.mean (fun ξ => ((d.run d.classes ξ).chosen.card : ℝ)) ≤
      μ.mean (fun ξ => ((d.finalSet d.classes ξ).card : ℝ)) +
        μ.mean (fun ξ => ((d.remainingWithinPairs d.classes ξ).card : ℝ)) +
          μ.mean (fun ξ => ((d.markedVertices d.classes ξ).card : ℝ)) := by
    rw [← μ.mean_add,← μ.mean_add]
    apply μ.mean_mono
    intro ξ
    exact_mod_cast d.finalSet_size_loss d.classes ξ
  linarith

end TP3.DependentSample.Data
