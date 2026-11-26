module

public import TP3.MarkedDeletion

@[expose] public section

namespace TP3.DependentSample.Data

attribute [local instance] Classical.propDecidable

variable {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
variable (d : Data V U)

/-- A retained vertex in the new class requires every mark listed by its
edge to an earlier chosen neighbour. -/
theorem new_vertex_requires_list (n : ℕ)
    (ξ : History (ClassNoise V U d.maxListSize) n)
    (ω : ClassNoise V U d.maxListSize) {x y : V}
    (hx : x ∈ d.retained (d.run n ξ).chosen (d.tentative n (d.run n ξ).chosen ω))
    (hy : y ∈ (d.run n ξ).chosen) (hxy : d.graph.Adj x y) :
    ∀ M ∈ d.lists x y, ω.1 M=true := by
  intro M hM
  have hp := (Finset.mem_filter.mp (d.retained_subset _ _ hx)).2.2
  apply hp.1 M
  exact Finset.mem_biUnion.mpr ⟨y,Finset.mem_filter.mpr ⟨hy,hxy⟩,hM⟩

/-- Across two distinct classes, a chosen graph edge forces every set in
its list to have been marked. This invariant survives every deletion. -/
theorem chosen_lists_marked (hsym : ∀ a b, d.lists a b = d.lists b a)
    (n : ℕ) (ξ : History (ClassNoise V U d.maxListSize) n)
    {x y : V} (hx : x ∈ (d.run n ξ).chosen) (hy : y ∈ (d.run n ξ).chosen)
    (hxy : d.graph.Adj x y) (hclasses : d.classOf x ≠ d.classOf y) :
    d.lists x y ⊆ (d.run n ξ).marked := by
  induction n with
  | zero => simp [run,processState,initial] at hx
  | succ n ih =>
    change x ∈ (d.run n ξ.1).chosen ∪ _ at hx
    change y ∈ (d.run n ξ.1).chosen ∪ _ at hy
    rcases Finset.mem_union.mp hx with hxp | hxn <;>
      rcases Finset.mem_union.mp hy with hyp | hyn
    · intro M hM
      exact (d.run_marked_succ n ξ.1 ξ.2 M).mpr (Or.inl (ih ξ.1 hxp hyp hM))
    · intro M hM
      have hm := d.new_vertex_requires_list n ξ.1 ξ.2 hyn hxp hxy.symm M
        (by simpa only [hsym y x] using hM)
      exact (d.run_marked_succ n ξ.1 ξ.2 M).mpr (Or.inr hm)
    · intro M hM
      exact (d.run_marked_succ n ξ.1 ξ.2 M).mpr
        (Or.inr (d.new_vertex_requires_list n ξ.1 ξ.2 hxn hyp hxy M hM))
    · have hxt := d.retained_subset _ _ hxn
      have hyt := d.retained_subset _ _ hyn
      have hxc := (Finset.mem_filter.mp (Finset.mem_filter.mp hxt).1).2
      have hyc := (Finset.mem_filter.mp (Finset.mem_filter.mp hyt).1).2
      exact False.elim (hclasses (Fin.ext (hxc.trans hyc.symm)))

end TP3.DependentSample.Data
