module

public import TP3.ConflictSupports

@[expose] public section

namespace TP3

attribute [local instance] Classical.propDecidable

variable {V ι : Type*} [DecidableEq V]

/-- Pairs covered by selected supports. A support may cover extra pairs;
this harmless overcount keeps the deletion estimate elementary. -/
noncomputable def coveredPairs (I : Finset ι) (S : ι → Finset V) (A : Finset V) :
    Finset (Finset V) :=
  (I.filter (fun j => S j ⊆ A)).biUnion (fun j => (S j).powersetCard 2)

theorem mem_coveredPairs {I : Finset ι} {S : ι → Finset V} {A e : Finset V}
    {j : ι} (hj : j ∈ I) (hSA : S j ⊆ A) (heS : e ⊆ S j) (he : e.card=2) :
    e ∈ coveredPairs I S A :=
  Finset.mem_biUnion.mpr ⟨j,Finset.mem_filter.mpr ⟨hj,hSA⟩,
    Finset.mem_powersetCard.mpr ⟨heS,he⟩⟩

theorem coveredPairs_mono (I : Finset ι) (S : ι → Finset V)
    {A B : Finset V} (hAB : A ⊆ B) : coveredPairs I S A ⊆ coveredPairs I S B := by
  intro e he
  obtain ⟨j,hj,he⟩ := Finset.mem_biUnion.mp he
  exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp hj).1,((Finset.mem_filter.mp hj).2).trans hAB⟩,he⟩

namespace DependentSample.Data

variable {U : Type*} [Fintype V] [Fintype U] [DecidableEq U]
variable (d : Data V U)

theorem conflicts_covered (hH : IsTripleSystem d.triples)
    (hsym : ∀ a b, d.lists a b = d.lists b a)
    (C A : Finset V) (i : ℕ)
    (hC : ∀ u ∈ C, (d.classOf u).val < i)
    (hA : ∀ x ∈ A, (d.classOf x).val = i) :
    d.conflicts C A ⊆
      coveredPairs d.threeIndices threeSupport (C ∪ A) ∪
        coveredPairs d.fourIndices fourSupport (C ∪ A) := by
  intro e he
  obtain ⟨hep,hex⟩ := Finset.mem_filter.mp he
  obtain ⟨heA,hecard⟩ := Finset.mem_powersetCard.mp hep
  obtain ⟨x,hxe,y,hye,hxy,u,hu,v,hv,hM,hcase⟩ := hex
  obtain ⟨M,hM⟩ := hM
  obtain ⟨hMx,hMy⟩ := Finset.mem_inter.mp hM
  have hpair : ({x,y} : Finset V) = e := by
    apply Finset.eq_of_subset_of_card_le
    · simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]
      exact ⟨hxe,hye⟩
    · simp [hecard,hxy]
  have hxA := heA hxe
  have hyA := heA hye
  obtain ⟨huC,hxu⟩ := Finset.mem_filter.mp hu
  obtain ⟨hvC,hyv⟩ := Finset.mem_filter.mp hv
  have hxU : x ∈ C ∪ A := Finset.mem_union_right _ hxA
  have hyU : y ∈ C ∪ A := Finset.mem_union_right _ hyA
  have huU : u ∈ C ∪ A := Finset.mem_union_left _ huC
  have hvU : v ∈ C ∪ A := Finset.mem_union_left _ hvC
  have hxu' : x ≠ u := by intro hh; subst u; have := hC x huC; have := hA x hxA; omega
  have hxv' : x ≠ v := by intro hh; subst v; have := hC x hvC; have := hA x hxA; omega
  have hyu' : y ≠ u := by intro hh; subst u; have := hC y huC; have := hA y hyA; omega
  have hyv' : y ≠ v := by intro hh; subst v; have := hC y hvC; have := hA y hyA; omega
  by_cases huv : u=v
  · subst v
    apply Finset.mem_union_left
    apply mem_coveredPairs (j := (x,u,M,y))
      (d.mem_threeIndices hxu hyv.symm hxy.symm hMx (by simpa only [hsym u y] using hMy))
    · simp only [threeSupport,Finset.insert_subset_iff,Finset.singleton_subset_iff]
      exact ⟨hxU,huU,hyU⟩
    · rw [← hpair]
      simp [threeSupport]
    · exact hecard
  · obtain ⟨f,hf,hfs⟩ := hcase.resolve_left huv
    have hd : [x,u,y,v].Pairwise (· ≠ ·) := by
      simp only [List.pairwise_cons,List.mem_cons,List.not_mem_nil,forall_eq_or_imp]
      aesop
    obtain ⟨j,hj,hjS⟩ := d.four_witness_of_triple hH hsym hd hxu hyv hMx hMy hf hfs
    apply Finset.mem_union_right
    apply mem_coveredPairs hj
    · rw [hjS]
      simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]
      exact ⟨hxU,huU,hyU,hvU⟩
    · rw [hjS,← hpair]
      simp
    · exact hecard

theorem allConflicts_covered (hH : IsTripleSystem d.triples)
    (hsym : ∀ a b, d.lists a b = d.lists b a)
    (n : ℕ) (ξ : History (ClassNoise V U d.maxListSize) n) :
    d.allConflicts n ξ ⊆
      coveredPairs d.threeIndices threeSupport (d.run n ξ).tentative ∪
        coveredPairs d.fourIndices fourSupport (d.run n ξ).tentative := by
  induction n with
  | zero => simp [allConflicts]
  | succ n ih =>
    have hnew := d.conflicts_covered hH hsym (d.run n ξ.1).chosen
      (d.tentative n (d.run n ξ.1).chosen ξ.2) n (d.run_chosen_class_lt n ξ.1)
      (fun x hx => (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2)
    have hp : (d.run n ξ.1).tentative ⊆ (d.run (n+1) ξ).tentative :=
      Finset.subset_union_left
    have hn : (d.run n ξ.1).chosen ∪ d.tentative n (d.run n ξ.1).chosen ξ.2 ⊆
        (d.run (n+1) ξ).tentative :=
      Finset.union_subset_union (d.run_chosen_subset_tentative n ξ.1) (Finset.Subset.refl _)
    exact Finset.union_subset
      ((ih ξ.1).trans (Finset.union_subset_union (coveredPairs_mono _ _ hp) (coveredPairs_mono _ _ hp)))
      (hnew.trans (Finset.union_subset_union (coveredPairs_mono _ _ hn) (coveredPairs_mono _ _ hn)))

end DependentSample.Data
end TP3
