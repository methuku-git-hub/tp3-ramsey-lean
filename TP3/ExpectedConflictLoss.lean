module

public import TP3.ConflictCoverage

@[expose] public section

namespace TP3.DependentSample.Data

attribute [local instance] Classical.propDecidable

variable {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
variable (d : Data V U)

/-- The expected number of conflict pairs is controlled by configurations
on three or four distinct selected vertices. The constants 3 and 162 allow
all pairs in each supporting set and all ordered choices in a triple. -/
theorem mean_conflict_loss (hH : IsTripleSystem d.triples)
    (hsym : ∀ a b, d.lists a b = d.lists b a)
    (h : ℕ) (g : ℝ)
    (hinc : ∀ y M, (d.listing y M).card ≤ h)
    (hdeg : ∀ x, ((d.neighbors x).card : ℝ) ≤ g)
    (q τ : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    (historyLaw (finiteClassLaw d.maxListSize q τ hq hq1 hτ hτ1) d.classes).mean
      (fun ξ => ((d.allConflicts d.classes ξ).card : ℝ)) ≤
        3*(Fintype.card V : ℝ)*g*d.listBound*h*q^3 +
        162*(d.triples.card : ℝ)*d.listBound*h*q^4 := by
  let μ := historyLaw (finiteClassLaw (V := V) (U := U) d.maxListSize q τ hq hq1 hτ hτ1) d.classes
  let A := fun ξ => (d.run d.classes ξ).tentative
  have hcoarse : ∀ S, μ.event (fun ξ => S ⊆ A ξ) ≤ q^S.card :=
    fun S => d.tentative_probability S q τ hq hq1 hτ hτ1
  have h₃ : μ.mean (fun ξ => ((coveredPairs d.threeIndices threeSupport (A ξ)).card : ℝ)) ≤
      3*(d.threeIndices.card : ℝ)*q^3 := by
    apply μ.mean_activated_union A d.threeIndices threeSupport
      (fun j => (threeSupport j).powersetCard 2) q 3 3 hcoarse (d.three_support_card)
    intro j hj
    rw [Finset.card_powersetCard,d.three_support_card j hj]
    decide
  have h₄ : μ.mean (fun ξ => ((coveredPairs d.fourIndices fourSupport (A ξ)).card : ℝ)) ≤
      6*(d.fourIndices.card : ℝ)*q^4 := by
    apply μ.mean_activated_union A d.fourIndices fourSupport
      (fun j => (fourSupport j).powersetCard 2) q 6 4 hcoarse (d.four_support_card hH)
    intro j hj
    rw [Finset.card_powersetCard,d.four_support_card hH j hj]
    decide
  have hc : μ.mean (fun ξ => ((d.allConflicts d.classes ξ).card : ℝ)) ≤
      μ.mean (fun ξ => ((coveredPairs d.threeIndices threeSupport (A ξ)).card : ℝ)) +
        μ.mean (fun ξ => ((coveredPairs d.fourIndices fourSupport (A ξ)).card : ℝ)) := by
    rw [← μ.mean_add]
    apply μ.mean_mono
    intro ξ
    exact_mod_cast (Finset.card_le_card (d.allConflicts_covered hH hsym d.classes ξ)).trans
      (Finset.card_union_le _ _)
  have h₃' : 3*(d.threeIndices.card : ℝ)*q^3 ≤
      3*(Fintype.card V : ℝ)*g*d.listBound*h*q^3 := by
    have hh := mul_le_mul_of_nonneg_left (d.three_indices_card h g hinc hdeg) (by norm_num : (0:ℝ) ≤ 3)
    convert mul_le_mul_of_nonneg_right hh (pow_nonneg hq 3) using 1 <;> ring
  have h₄' : 6*(d.fourIndices.card : ℝ)*q^4 ≤
      162*(d.triples.card : ℝ)*d.listBound*h*q^4 := by
    have hh : (d.fourIndices.card : ℝ) ≤ 27*(d.triples.card : ℝ)*d.listBound*h := by
      exact_mod_cast d.four_indices_card hH h hinc
    have hh' := mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ) ≤ 6)
    convert mul_le_mul_of_nonneg_right hh' (pow_nonneg hq 4) using 1 <;> ring
  exact hc.trans (add_le_add (h₃.trans h₃') (h₄.trans h₄'))

/-- A proved expected-size estimate for the adaptive selection after the
conflict deletions. The remaining marked-set and within-class deletions
are separate later steps. -/
theorem mean_chosen_size (hH : IsTripleSystem d.triples)
    (hsym : ∀ a b, d.lists a b = d.lists b a) (hR : 0 < d.classes)
    (h : ℕ) (g : ℝ)
    (hinc : ∀ y M, (d.listing y M).card ≤ h)
    (hdeg : ∀ x, ((d.neighbors x).card : ℝ) ≤ g)
    (q τ : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    (Fintype.card V : ℝ) *
      ((q*τ^d.maxListSize) * (1-g*(q*τ^d.maxListSize)/d.classes)) -
        (3*(Fintype.card V : ℝ)*g*d.listBound*h*q^3 +
          162*(d.triples.card : ℝ)*d.listBound*h*q^4) ≤
    (historyLaw (finiteClassLaw d.maxListSize q τ hq hq1 hτ hτ1) d.classes).mean
      (fun ξ => ((d.run d.classes ξ).chosen.card : ℝ)) := by
  have hsize := d.mean_chosen_lower_bound hR g hdeg q τ hq hq1 hτ hτ1
  have hloss := d.mean_conflict_loss hH hsym h g hinc hdeg q τ hq hq1 hτ hτ1
  linarith

end TP3.DependentSample.Data
