module

public import TP3.LinkTriangles

@[expose] public section

namespace TP3

attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem pairSystem_low_degree {G : Finset (Finset V)} (hG : IsPairSystem G)
    (hpath : ∀ a b c d : V, [a,b,c,d].Pairwise (· ≠ ·) →
      {a,b} ∈ G → {b,c} ∈ G → {c,d} ∈ G → False)
    (X : Finset V) (hX : X.Nonempty) :
    ∃ x ∈ X, degree (induced G X) x ≤ 2 := by
  by_contra hn
  push Not at hn
  let N := fun x => Finset.univ.filter (fun y => (pairGraph (induced G X)).Adj x y)
  have hNX (x : V) : N x ⊆ X := by
    intro y hy
    have hh := (Finset.mem_filter.mp hy).2.2
    exact (Finset.mem_filter.mp hh).2 (by simp)
  have hNc (x : V) (hx : x ∈ X) : 2 < (N x).card := by
    dsimp only [N]
    rw [pairGraph_neighbors_card (G := induced G X) (fun e he => hG e (Finset.mem_filter.mp he).1)]
    exact hn x hx
  obtain ⟨x,hx⟩ := hX
  obtain ⟨y,hy⟩ := Finset.card_pos.mp (show 0 < (N x).card by have := hNc x hx; omega)
  have hxy := (Finset.mem_filter.mp hy).2
  obtain ⟨z,hz,hzy⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show ({y} : Finset V).card < (N x).card by have := hNc x hx; simp; omega)
  have hxz := (Finset.mem_filter.mp hz).2
  have hpaircard : ({x,z} : Finset V).card ≤ 2 := by
    by_cases hh : x=z <;> simp [hh]
  obtain ⟨w,hw,hwxz⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show ({x,z} : Finset V).card < (N y).card by have := hNc y (hNX x hy); omega)
  have hyw := (Finset.mem_filter.mp hw).2
  apply hpath z x y w
  · have hzy' : z ≠ y := by simpa using hzy
    have hwx : w ≠ x := by intro hh; exact hwxz (by simp [hh])
    have hwz : w ≠ z := by intro hh; exact hwxz (by simp [hh])
    have hxy' : x ≠ y := hxy.1
    have hxz' : x ≠ z := hxz.1
    have hyw' : y ≠ w := hyw.1
    simp only [List.pairwise_cons,List.mem_cons,List.not_mem_nil,forall_eq_or_imp]
    aesop
  · simpa only [Finset.pair_comm] using (Finset.mem_filter.mp hxz.2).1
  · exact (Finset.mem_filter.mp hxy.2).1
  · exact (Finset.mem_filter.mp hyw.2).1

theorem pairSystem_no_path_edge_bound {G : Finset (Finset V)} (hG : IsPairSystem G)
    (hpath : ∀ a b c d : V, [a,b,c,d].Pairwise (· ≠ ·) →
      {a,b} ∈ G → {b,c} ∈ G → {c,d} ∈ G → False) :
    (G.card : ℝ) ≤ 3*(Fintype.card V : ℝ) := by
  have hh := induced_edges_le_of_low_degree G
    (fun e he => Finset.card_pos.mp (by rw [hG e he]; norm_num)) 3 (by norm_num)
    Finset.univ (fun X _ hX => by
      obtain ⟨x,hx,hd⟩ := pairSystem_low_degree hG hpath X hX
      refine ⟨x,hx,?_⟩
      have hd' : (degree (induced G X) x : ℝ) ≤ 2 := by exact_mod_cast hd
      linarith)
  simpa [induced] using hh

/-- A deliberately loose degree bound sufficient for the Ramsey reduction.
Every link has no path of three edges, hence is 2-degenerate. -/
theorem pathFree_degree_bound {H : Finset (Finset V)} (hH : IsTripleSystem H)
    (hfree : ¬ HasTightPath H) (v : V) :
    (degree H v : ℝ) ≤ 3*(Fintype.card V : ℝ) := by
  rw [← linkPairs_card hH]
  apply pairSystem_no_path_edge_bound
    (fun e he => mem_allPairs.mp (Finset.mem_filter.mp he).1)
  intro a b c d hd hab hbc hcd
  have hm {x y : V} (hxy : x ≠ y) (he : {x,y} ∈ linkPairs H v) : (link H v).Adj x y := by
    obtain ⟨_,hnot,heH⟩ := Finset.mem_filter.mp he
    have hvx : v ≠ x := by intro hh; exact hnot (by simp [hh])
    have hvy : v ≠ y := by intro hh; exact hnot (by simp [hh])
    exact ⟨hxy,hvx,hvy,heH⟩
  have hd' := hd
  simp only [List.pairwise_cons,List.mem_cons,List.not_mem_nil,forall_eq_or_imp] at hd'
  apply link_no_three_edge_path hfree v a b c d hd
  · exact hm (by aesop) hab
  · exact hm (by aesop) hbc
  · exact hm (by aesop) hcd

end TP3
