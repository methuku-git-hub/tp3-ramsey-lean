module

public import TP3.ListedMarks

@[expose] public section

namespace TP3.DependentSample.Data

attribute [local instance] Classical.propDecidable

variable {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
variable (d : Data V U)

noncomputable def withinClassPairs : Finset (Finset V) :=
  (Finset.univ.powersetCard 2).filter
    (fun e => ∃ x ∈ e, ∃ y ∈ e, d.graph.Adj x y ∧ d.classOf x=d.classOf y)

theorem withinClassPairs_card {e : Finset V} (he : e ∈ d.withinClassPairs) : e.card=2 :=
  (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2

noncomputable def remainingWithinPairs (n : ℕ)
    (ξ : History (ClassNoise V U d.maxListSize) n) : Finset (Finset V) :=
  d.withinClassPairs.filter (fun e => e ⊆ d.unmarked n ξ)

theorem remainingWithinPairs_nonempty (n : ℕ)
    (ξ : History (ClassNoise V U d.maxListSize) n) :
    ∀ e ∈ d.remainingWithinPairs n ξ, e.Nonempty := by
  intro e he
  have hc := d.withinClassPairs_card (Finset.mem_filter.mp he).1
  exact Finset.card_pos.mp (by omega)

/-- The output of the sampling argument, after deleting vertices in
marked sets and one vertex from every surviving edge inside a class. -/
noncomputable def finalSet (n : ℕ)
    (ξ : History (ClassNoise V U d.maxListSize) n) : Finset V :=
  deleteForbidden (d.remainingWithinPairs n ξ) (d.remainingWithinPairs_nonempty n ξ)
    (d.unmarked n ξ)

theorem finalSet_subset_unmarked (n : ℕ)
    (ξ : History (ClassNoise V U d.maxListSize) n) :
    d.finalSet n ξ ⊆ d.unmarked n ξ := deleteForbidden_subset _ _ _

theorem finalSet_subset_chosen (n : ℕ)
    (ξ : History (ClassNoise V U d.maxListSize) n) :
    d.finalSet n ξ ⊆ (d.run n ξ).chosen :=
  (d.finalSet_subset_unmarked n ξ).trans (d.unmarked_subset n ξ)

theorem finalSet_edge_classes (n : ℕ)
    (ξ : History (ClassNoise V U d.maxListSize) n)
    {x y : V} (hx : x ∈ d.finalSet n ξ) (hy : y ∈ d.finalSet n ξ)
    (hxy : d.graph.Adj x y) : d.classOf x ≠ d.classOf y := by
  intro hclasses
  have hp : ({x,y} : Finset V) ∈ d.remainingWithinPairs n ξ := by
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,by simp [hxy.ne]⟩,
        x,by simp,y,by simp,hxy,hclasses⟩
    · simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]
      exact ⟨d.finalSet_subset_unmarked n ξ hx,d.finalSet_subset_unmarked n ξ hy⟩
  apply deleteForbidden_independent (d.remainingWithinPairs n ξ)
    (d.remainingWithinPairs_nonempty n ξ) (d.unmarked n ξ) {x,y} hp
  simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]
  exact ⟨hx,hy⟩

/-- The exclusion property required to remove dense completions of F:
each selected graph edge forces every listed set to avoid the final output. -/
theorem finalSet_exclusion (hsym : ∀ a b, d.lists a b = d.lists b a)
    (n : ℕ) (ξ : History (ClassNoise V U d.maxListSize) n)
    {x y : V} (hx : x ∈ d.finalSet n ξ) (hy : y ∈ d.finalSet n ξ)
    (hxy : d.graph.Adj x y) {M : U} (hM : M ∈ d.lists x y) :
    Disjoint (d.finalSet n ξ) (d.sets M) := by
  have hm := d.chosen_lists_marked hsym n ξ (d.finalSet_subset_chosen n ξ hx)
    (d.finalSet_subset_chosen n ξ hy) hxy (d.finalSet_edge_classes n ξ hx hy hxy) hM
  exact Finset.disjoint_left.mpr (fun z hz =>
    d.unmarked_avoids n ξ (d.finalSet_subset_unmarked n ξ hz) hm)

theorem finalSet_size_loss (n : ℕ)
    (ξ : History (ClassNoise V U d.maxListSize) n) :
    (d.run n ξ).chosen.card ≤ (d.finalSet n ξ).card +
      (d.remainingWithinPairs n ξ).card + (d.markedVertices n ξ).card := by
  have hh := deleteForbidden_size (d.remainingWithinPairs n ξ)
    (d.remainingWithinPairs_nonempty n ξ) (d.unmarked n ξ)
  have hc := d.unmarked_size n ξ
  change (d.unmarked n ξ).card ≤ (d.finalSet n ξ).card + (d.remainingWithinPairs n ξ).card at hh
  omega

theorem finalSet_probability (W : Finset V) (hW : FourVertexProperty d.triples W)
    (h : ℕ) (g : ℝ)
    (hinc : ∀ y M, (d.listing y M).card ≤ h)
    (hdeg : ∀ x, ((d.neighbors x).card : ℝ) ≤ g)
    (q τ : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    (historyLaw (finiteClassLaw d.maxListSize q τ hq hq1 hτ hτ1) d.classes).event
      (fun ξ => W ⊆ d.finalSet d.classes ξ) ≤
      (q*τ^d.maxListSize)^W.card + (W.card : ℝ)^2 *
        ((W.card : ℝ)*d.listBound*h*q^(W.card+1) +
          g*d.listBound*h*q^(W.card+2)) := by
  apply le_trans (FiniteLaw.event_mono _ ?_)
    (d.chosen_probability W hW h g hinc hdeg q τ hq hq1 hτ hτ1)
  intro ξ hchosen
  exact hchosen.trans (d.finalSet_subset_chosen d.classes ξ)

end TP3.DependentSample.Data
