module

public import TP3.SharedMarks
public import TP3.ChosenVertices

@[expose] public section

namespace TP3.DependentSample.Data

attribute [local instance] Classical.propDecidable

variable {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
variable (d : Data V U)

/-- Every failure of the disjoint-list event among vertices that actually
survive produces the outside witness counted in the error term. The proof
follows the actual history, including all earlier deletions. -/
theorem chosen_not_good_witness (W : Finset V)
    (hW : FourVertexProperty d.triples W)
    (n : ℕ) (h : History (ClassNoise V U d.maxListSize) n)
    (hchosen : d.processed W n ⊆ (d.run n h).chosen)
    (hnot : ¬ d.Good W n h) :
    d.ExternalWitness W (d.run n h).chosen := by
  classical
  induction n with
  | zero => exact False.elim (hnot trivial)
  | succ n ih =>
    have hh := (d.processed_chosen_step_iff W n h.1 h.2).mp hchosen
    by_cases hp : d.Good W n h.1
    · have hn : ¬ (d.slice W n : Set V).PairwiseDisjoint
          (d.required (d.run n h.1).chosen) := by
        intro hd
        exact hnot ⟨hp,hd,hh.2⟩
      simp only [Set.PairwiseDisjoint,Set.Pairwise] at hn
      push Not at hn
      obtain ⟨x,hx,y,hy,hxy,hdis⟩ := hn
      have hwitness := d.retained_overlap_witness W (d.run n h.1).chosen
        (d.tentative n (d.run n h.1).chosen h.2) n hW
        (d.run_chosen_class_lt n h.1)
        (fun z hz => (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2)
        (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 hxy
        (hh.2 hx) (hh.2 hy) hdis
      exact d.externalWitness_mono Finset.subset_union_left hwitness
    · exact d.externalWitness_mono Finset.subset_union_left (ih h.1 hh.1 hp)

theorem final_not_good_witness (W : Finset V)
    (hW : FourVertexProperty d.triples W)
    (h : History (ClassNoise V U d.maxListSize) d.classes)
    (hchosen : W ⊆ (d.run d.classes h).chosen)
    (hnot : ¬ d.Good W d.classes h) :
    d.ExternalWitness W (d.run d.classes h).chosen := by
  apply d.chosen_not_good_witness W hW d.classes h _ hnot
  rwa [d.processed_all]

end TP3.DependentSample.Data
