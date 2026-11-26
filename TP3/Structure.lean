module

public import TP3.Definitions

@[expose] public section

namespace TP3

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
theorem independent_mono {H : Finset (Finset V)} {S T : Finset V}
    (h : Independent H T) (hST : S ⊆ T) : Independent H S := by
  intro e he hes
  exact h e he (hes.trans hST)

theorem independent_induced {H : Finset (Finset V)} {S T : Finset V}
    (hST : S ⊆ T) (h : Independent (induced H T) S) : Independent H S := by
  intro e he hes
  apply h e
  · exact Finset.mem_filter.mpr ⟨he, hes.trans hST⟩
  · exact hes

theorem induced_isTripleSystem {H : Finset (Finset V)} (h : IsTripleSystem H)
    (S : Finset V) : IsTripleSystem (induced H S) := by
  intro e he
  exact h e (Finset.mem_filter.mp he).1

theorem hasTightPath_mono {H K : Finset (Finset V)} (hHK : H ⊆ K)
    (h : HasTightPath H) : HasTightPath K := by
  obtain ⟨a,b,c,d,e,hd,h₁,h₂,h₃⟩ := h
  exact ⟨a,b,c,d,e,hd,hHK h₁,hHK h₂,hHK h₃⟩

theorem induced_pathFree {H : Finset (Finset V)} (h : ¬ HasTightPath H)
    (S : Finset V) : ¬ HasTightPath (induced H S) := by
  intro hp
  exact h (hasTightPath_mono (Finset.filter_subset _ _) hp)

theorem edge_distinct {H : Finset (Finset V)} (hH : IsTripleSystem H)
    {a b c : V} (he : {a,b,c} ∈ H) : a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  have hc := hH _ he
  constructor
  · intro hab
    subst b
    by_cases hac : a = c <;> simp_all
  constructor
  · intro hac
    subst c
    by_cases hab : a = b
    · subst b
      simp at hc
    · simp [hab, Ne.symm hab] at hc
  · intro hbc
    subst c
    by_cases hab : a = b <;> simp_all

theorem triple_swap_last (a b c : V) : ({a,b,c} : Finset V) = {a,c,b} := by
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

theorem triple_rotate (a b c : V) : ({a,b,c} : Finset V) = {c,a,b} := by
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

variable [Fintype V]

@[simp] theorem mem_pairNeighbors {H : Finset (Finset V)} {a b x : V} :
    x ∈ pairNeighbors H a b ↔ x ≠ a ∧ x ≠ b ∧ {a,b,x} ∈ H := by
  simp [pairNeighbors]

theorem pairNeighbors_comm (H : Finset (Finset V)) (a b : V) :
    pairNeighbors H a b = pairNeighbors H b a := by
  ext x
  simp [Finset.insert_comm, and_left_comm]

theorem codegree_comm (H : Finset (Finset V)) (a b : V) :
    codegree H a b = codegree H b a := by
  simp only [codegree, pairNeighbors_comm H a b]

/-- A pair in at least three triples has private pairs to each of its
completion vertices, by the absence of a three-edge tight path. -/
theorem high_pair_private {H : Finset (Finset V)} (hH : IsTripleSystem H)
    (hfree : ¬ HasTightPath H) {a b x : V}
    (hab : 3 ≤ codegree H a b) (he : {a,b,x} ∈ H) :
    pairNeighbors H a x = {b} := by
  obtain ⟨habne,hax,hbx⟩ := edge_distinct hH he
  have hba : b ∈ pairNeighbors H a x := by
    simp only [mem_pairNeighbors]
    exact ⟨habne.symm, hbx, by rwa [← triple_swap_last a b x]⟩
  apply Finset.Subset.antisymm
  · intro z hz
    simp only [Finset.mem_singleton]
    by_contra hzb
    obtain ⟨hza,hzx,hez⟩ := mem_pairNeighbors.mp hz
    have hsmall : ({x,z} : Finset V).card < (pairNeighbors H a b).card := by
      have hcard : ({x,z} : Finset V).card ≤ 2 := by
        by_cases h : x = z <;> simp [h]
      unfold codegree at hab
      omega
    obtain ⟨y,hy,hynot⟩ := Finset.exists_mem_notMem_of_card_lt_card hsmall
    obtain ⟨hya,hyb,hey⟩ := mem_pairNeighbors.mp hy
    have hyx : y ≠ x := by simpa using fun h : y = x => hynot (by simp [h])
    have hyz : y ≠ z := by simpa using fun h : y = z => hynot (by simp [h])
    apply hfree
    refine ⟨z,x,a,b,y,?_,?_,?_,?_⟩
    · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, forall_eq_or_imp]
      aesop
    · rwa [triple_swap_last z x a, ← triple_rotate a x z]
    · rwa [← triple_rotate a b x]
    · exact hey
  · exact Finset.singleton_subset_iff.mpr hba

theorem high_pair_codegrees {H : Finset (Finset V)} (hH : IsTripleSystem H)
    (hfree : ¬ HasTightPath H) {a b x : V}
    (hab : 3 ≤ codegree H a b) (he : {a,b,x} ∈ H) :
    codegree H a x = 1 ∧ codegree H b x = 1 := by
  constructor
  · simp [codegree, high_pair_private hH hfree hab he]
  · have hba : 3 ≤ codegree H b a := by simpa [codegree_comm H b a] using hab
    have hbe : {b,a,x} ∈ H := by simpa [Finset.insert_comm] using he
    simp [codegree, high_pair_private hH hfree hba hbe]

/-- Neighbourhoods of distinct pairs through a fixed vertex are disjoint
as soon as one of the two pairs has codegree at least three. -/
theorem pairNeighbors_disjoint {H : Finset (Finset V)}
    (hH : IsTripleSystem H) (hfree : ¬ HasTightPath H) {a b c : V}
    (hab : 3 ≤ codegree H a b) (hbc : b ≠ c) :
    Disjoint (pairNeighbors H a b) (pairNeighbors H a c) := by
  apply Finset.disjoint_left.mpr
  intro x hxb hxc
  obtain ⟨hxa,hxc',hacx⟩ := mem_pairNeighbors.mp hxc
  have he := (mem_pairNeighbors.mp hxb).2.2
  have hac := (edge_distinct hH hacx).1
  have hc : c ∈ pairNeighbors H a x := by
    exact mem_pairNeighbors.mpr
      ⟨hac.symm, hxc'.symm, by rwa [← triple_swap_last a c x]⟩
  rw [high_pair_private hH hfree hab he, Finset.mem_singleton] at hc
  exact hbc hc.symm

end TP3
