module

public import TP3.LinkTriangles

@[expose] public section

namespace TP3

attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem triangleInstance_of_three {H : Finset (Finset V)} {v a b c : V}
    (hd : [v,a,b,c].Pairwise (· ≠ ·))
    (h1 : ({v,a,b} : Finset V) ∈ H) (h2 : ({v,a,c} : Finset V) ∈ H)
    (h3 : ({v,b,c} : Finset V) ∈ H) :
    (v,{a,b,c}) ∈ triangleInstances H := by
  simp only [List.pairwise_cons,List.mem_cons,List.not_mem_nil,forall_eq_or_imp] at hd
  rw [mem_triangleInstances]
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_powersetCard.mpr
    exact ⟨Finset.subset_univ _,by simp [hd.2.1.1,hd.2.1.2.1,hd.2.2.1.1]⟩
  · intro x hx y hy hxy
    have hab : (link H v).Adj a b := ⟨hd.2.1.1,hd.1.1,hd.1.2.1,h1⟩
    have hac : (link H v).Adj a c := ⟨hd.2.1.2.1,hd.1.1,hd.1.2.2.1,h2⟩
    have hbc : (link H v).Adj b c := ⟨hd.2.2.1.1,hd.1.2.1,hd.1.2.2.1,h3⟩
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first | exact hab | exact hab.symm | exact hac | exact hac.symm |
        exact hbc | exact hbc.symm | exact False.elim (hxy rfl)

theorem hasThreeOnFour_induced_support {H : Finset (Finset V)} {S : Finset V}
    (h4 : HasThreeOnFour (induced H S)) :
    ∃ j ∈ triangleInstances H, triangleSupport j ⊆ S := by
  obtain ⟨v,a,b,c,hd,h1,h2,h3⟩ := h4
  obtain ⟨h1,h1S⟩ := Finset.mem_filter.mp h1
  obtain ⟨h2,h2S⟩ := Finset.mem_filter.mp h2
  obtain ⟨h3,h3S⟩ := Finset.mem_filter.mp h3
  refine ⟨(v,{a,b,c}),triangleInstance_of_three hd h1 h2 h3,?_⟩
  intro x hx
  simp only [triangleSupport,Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact h1S (by simp)
  · exact h1S (by simp)
  · exact h1S (by simp)
  · exact h2S (by simp)

theorem delete_present_triangles (H : Finset (Finset V)) (S : Finset V) :
    ∃ T ⊆ S, ¬ HasThreeOnFour (induced H T) ∧
      S.card ≤ T.card + ((triangleInstances H).filter (fun j => triangleSupport j ⊆ S)).card := by
  let J := (triangleInstances H).filter (fun j => triangleSupport j ⊆ S)
  let E := J.image triangleSupport
  have hE : ∀ e ∈ E, e.Nonempty := by
    intro e he
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp he
    exact Finset.card_pos.mp (by rw [triangleSupport_card (Finset.mem_filter.mp hj).1]; omega)
  refine ⟨deleteForbidden E hE S,deleteForbidden_subset E hE S,?_,?_⟩
  · intro h4
    obtain ⟨j,hj,hjT⟩ := hasThreeOnFour_induced_support h4
    have hjS := hjT.trans (deleteForbidden_subset E hE S)
    have hjE : triangleSupport j ∈ E := Finset.mem_image.mpr
      ⟨j,Finset.mem_filter.mpr ⟨hj,hjS⟩,rfl⟩
    exact deleteForbidden_independent E hE S _ hjE hjT
  · exact (deleteForbidden_size E hE S).trans
      (Nat.add_le_add_left Finset.card_image_le _)

namespace DependentSample.Data

variable {U : Type*} [Fintype U] [DecidableEq U] (d : Data V U)

theorem mean_triangle_instances
    (q τ : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    (historyLaw (finiteClassLaw d.maxListSize q τ hq hq1 hτ hτ1) d.classes).mean
      (fun ξ => (((triangleInstances d.triples).filter
        (fun j => triangleSupport j ⊆ d.finalSet d.classes ξ)).card : ℝ)) ≤
    (triangleInstances d.triples).card * q^4 := by
  let μ := historyLaw (finiteClassLaw (V := V) (U := U) d.maxListSize q τ hq hq1 hτ hτ1) d.classes
  have hm := μ.mean_filter_card (triangleInstances d.triples)
    (fun (j : V × Finset V) (ξ : History (ClassNoise V U d.maxListSize) d.classes) =>
      triangleSupport j ⊆ d.finalSet d.classes ξ)
  calc
    _ = ∑ j ∈ triangleInstances d.triples, μ.event (fun ξ => triangleSupport j ⊆ d.finalSet d.classes ξ) := by
      convert hm using 1
      congr 1
      funext ξ
      congr 1
      congr 1
      ext j
      simp
    _ ≤ ∑ _j ∈ triangleInstances d.triples, q^4 := by
      apply Finset.sum_le_sum
      intro j hj
      have hp := d.chosen_coarse_probability (triangleSupport j) q τ hq hq1 hτ hτ1
      apply le_trans (μ.event_mono (fun ξ hξ => hξ.trans (d.finalSet_subset_chosen d.classes ξ)))
      rwa [triangleSupport_card hj] at hp
    _ = _ := by rw [Finset.sum_const,nsmul_eq_mul]

end DependentSample.Data
end TP3
