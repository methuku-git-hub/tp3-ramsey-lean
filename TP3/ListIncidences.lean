module

public import TP3.GraphPeeling

@[expose] public section

namespace TP3

attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {V ι : Type*} [DecidableEq V] [DecidableEq ι]

/-- Double count incidences of a vertex set with a finite indexed family.
Repeated vertex sets are allowed, with each occurrence counted separately. -/
theorem intersection_sum (I : Finset ι) (U : ι → Finset V) (N : Finset V) :
    ∑ i ∈ I, (N ∩ U i).card = ∑ x ∈ N, (I.filter (fun i => x ∈ U i)).card := by
  have hi (i : ι) : (N ∩ U i).card = ∑ x ∈ N, if x ∈ U i then 1 else 0 := by
    simp [← Finset.sum_filter]
  simp_rw [hi]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  simp [← Finset.sum_filter]

noncomputable def intersectionList (I : Finset ι) (U : ι → Finset V)
    (N : Finset V) (c : ℝ) : Finset ι :=
  I.filter (fun i => c ≤ ((N ∩ U i).card : ℝ))

/-- Bounded incidence of vertices bounds the length of every list. -/
theorem intersectionList_bound (I : Finset ι) (U : ι → Finset V)
    (N : Finset V) (c r : ℝ)
    (hr : ∀ x ∈ N, ((I.filter (fun i => x ∈ U i)).card : ℝ) ≤ r) :
    c*((intersectionList I U N c).card : ℝ) ≤ r*N.card := by
  let L := intersectionList I U N c
  calc
    _ = ∑ _i ∈ L, c := by simp [L,mul_comm]
    _ ≤ ∑ i ∈ L, ((N ∩ U i).card : ℝ) :=
      Finset.sum_le_sum (fun i hi => (Finset.mem_filter.mp hi).2)
    _ ≤ ∑ i ∈ I, ((N ∩ U i).card : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => Nat.cast_nonneg _)
    _ = ∑ x ∈ N, ((I.filter (fun i => x ∈ U i)).card : ℝ) := by
      exact_mod_cast intersection_sum I U N
    _ ≤ ∑ _x ∈ N, r := Finset.sum_le_sum hr
    _ = _ := by simp [mul_comm]

/-- Disjoint neighbourhoods through a fixed vertex bound the number of
its incident pairs that can list one specified set. -/
theorem disjoint_neighborhood_list_bound (I : Finset ι) (N : ι → Finset V)
    (U : Finset V) (c : ℝ) (hdis : (I : Set ι).PairwiseDisjoint N) :
    c*((I.filter (fun i => c ≤ ((N i ∩ U).card : ℝ))).card : ℝ) ≤ U.card := by
  let L := I.filter (fun i => c ≤ ((N i ∩ U).card : ℝ))
  have hd : (L : Set ι).PairwiseDisjoint (fun i => N i ∩ U) := by
    intro i hi j hj hij
    exact (hdis (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1 hij).mono
      Finset.inter_subset_left Finset.inter_subset_left
  have hs : L.biUnion (fun i => N i ∩ U) ⊆ U := by
    intro x hx
    obtain ⟨i,hi,hx⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_inter.mp hx).2
  calc
    _ = ∑ _i ∈ L, c := by simp [L,mul_comm]
    _ ≤ ∑ i ∈ L, ((N i ∩ U).card : ℝ) :=
      Finset.sum_le_sum (fun i hi => (Finset.mem_filter.mp hi).2)
    _ = ((L.biUnion (fun i => N i ∩ U)).card : ℝ) := by
      rw [Finset.card_biUnion hd,Nat.cast_sum]
    _ ≤ _ := by exact_mod_cast Finset.card_le_card hs

/-- The edges removed by peeling have a small intersection with a
neighbourhood unless their block is on its list. -/
theorem unlisted_intersection_square_sum (I : Finset ι) (U : ι → Finset V)
    (Y : Finset V) (c r : ℝ) (hc : 0 ≤ c)
    (hsmall : ∀ i ∈ I, ((Y ∩ U i).card : ℝ) ≤ c)
    (hr : ∀ x ∈ Y, ((I.filter (fun i => x ∈ U i)).card : ℝ) ≤ r) :
    ∑ i ∈ I, ((Y ∩ U i).card : ℝ)^2 ≤ c*r*Y.card := by
  have hinc : (∑ i ∈ I, ((Y ∩ U i).card : ℝ)) ≤ r*Y.card := by
    calc
      _ = ∑ x ∈ Y, ((I.filter (fun i => x ∈ U i)).card : ℝ) := by
        exact_mod_cast intersection_sum I U Y
      _ ≤ ∑ _x ∈ Y, r := Finset.sum_le_sum hr
      _ = _ := by simp [mul_comm]
  calc
    _ ≤ ∑ i ∈ I, c*((Y ∩ U i).card : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      nlinarith [hsmall i hi,Nat.cast_nonneg (α := ℝ) (Y ∩ U i).card]
    _ = c*∑ i ∈ I, ((Y ∩ U i).card : ℝ) := by rw [Finset.mul_sum]
    _ ≤ c*(r*Y.card) := mul_le_mul_of_nonneg_left hinc hc
    _ = _ := by ring

end TP3
