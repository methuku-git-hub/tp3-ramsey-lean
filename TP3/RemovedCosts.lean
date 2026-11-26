module

public import TP3.AwayRemoval

@[expose] public section

namespace TP3

attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem linkCount_erase (H : Finset (Finset V)) (v : V) (S : Finset V) :
    linkCount H v (S.erase v)=linkCount H v S := by
  unfold linkCount
  congr 1
  congr 1
  ext e
  simp only [induced,Finset.mem_filter,Finset.subset_erase]
  constructor
  · rintro ⟨he,heS,_⟩
    exact ⟨he,heS⟩
  · rintro ⟨he,heS⟩
    exact ⟨he,heS,(Finset.mem_filter.mp he).2.1⟩

theorem incidentCost_erase (H : Finset (Finset V)) (v : V) (S : Finset V) :
    incidentCost H v (S.erase v)=incidentCost H v S := by
  by_cases hv : v ∈ S
  · have hh := Finset.sum_erase_add S (orderedCost H v) hv
    simpa [orderedCost,incidentCost] using hh
  · rw [Finset.erase_eq_of_notMem hv]

theorem away_linkCount_le (H : Finset (Finset V)) (hH : IsTripleSystem H)
    (p δ : ℝ) (hp : 0 ≤ p) (hp1 : p < 1) (hδ : 0 ≤ δ) (v : V) :
    (awayLaw H hH (codegreeCost H) (codegreeCost_nonneg H) p δ hp hp1.le hδ v).mean (linkCount H v) ≤
      (restrictedLaw H hH (codegreeCost H) (codegreeCost_nonneg H) p δ hp hp1.le hδ).mean
        (linkCount H v)/(1-p) := by
  have hh := away_remove_bound H hH (codegreeCost H) (codegreeCost_nonneg H)
    p δ hp hp1 hδ v (linkCount H v) (fun I => Nat.cast_nonneg _)
  simpa only [linkCount_erase] using hh

theorem away_incidentCost_le (H : Finset (Finset V)) (hH : IsTripleSystem H)
    (p δ : ℝ) (hp : 0 ≤ p) (hp1 : p < 1) (hδ : 0 ≤ δ) (v : V) :
    (awayLaw H hH (codegreeCost H) (codegreeCost_nonneg H) p δ hp hp1.le hδ v).mean (incidentCost H v) ≤
      (restrictedLaw H hH (codegreeCost H) (codegreeCost_nonneg H) p δ hp hp1.le hδ).mean
        (incidentCost H v)/(1-p) := by
  have hh := away_remove_bound H hH (codegreeCost H) (codegreeCost_nonneg H)
    p δ hp hp1 hδ v (incidentCost H v) (incidentCost_nonneg H v)
  simpa only [incidentCost_erase] using hh

end TP3
