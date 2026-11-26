module

public import TP3.ResidualDensity

@[expose] public section

namespace TP3

attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Completion vertices of an unordered pair. -/
noncomputable def completions (H : Finset (Finset V)) (e : Finset V) : Finset V :=
  Finset.univ.filter (fun x => x ∉ e ∧ insert x e ∈ H)

@[simp] theorem mem_completions {H : Finset (Finset V)} {e : Finset V} {x : V} :
    x ∈ completions H e ↔ x ∉ e ∧ insert x e ∈ H := by simp [completions]

theorem completions_pair (H : Finset (Finset V)) (a b : V) :
    completions H {a,b} = pairNeighbors H a b := by
  ext x
  simp only [mem_completions,Finset.mem_insert,Finset.mem_singleton,not_or,mem_pairNeighbors]
  have heq : (insert x {a,b} : Finset V)={a,b,x} := by ext y; simp; tauto
  rw [heq]
  tauto

theorem completions_mono {H K : Finset (Finset V)} (hHK : H ⊆ K) (e : Finset V) :
    completions H e ⊆ completions K e := by
  intro x hx
  obtain ⟨hx,he⟩ := mem_completions.mp hx
  exact mem_completions.mpr ⟨hx,hHK he⟩

theorem triple_eq_insert_completion {H : Finset (Finset V)} (hH : IsTripleSystem H)
    {e f : Finset V} (he : e.card=2) (hf : f ∈ H) (hef : e ⊆ f) :
    ∃ x ∉ e, insert x e=f := by
  have hdiff : (f \ e).card=1 := by rw [Finset.card_sdiff_of_subset hef,hH f hf,he]
  obtain ⟨x,hx⟩ := Finset.card_eq_one.mp hdiff
  have hxm : x ∈ f \ e := by rw [hx]; simp
  refine ⟨x,(Finset.mem_sdiff.mp hxm).2,?_⟩
  have hh := Finset.sdiff_union_of_subset hef
  rw [hx] at hh
  simpa only [Finset.singleton_union] using hh

theorem completions_image {H : Finset (Finset V)} (hH : IsTripleSystem H)
    (e : Finset V) (he : e.card=2) :
    (completions H e).image (fun x => insert x e) = H.filter (fun f => e ⊆ f) := by
  ext f
  constructor
  · intro hf
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hf
    exact Finset.mem_filter.mpr ⟨(mem_completions.mp hx).2,Finset.subset_insert _ _⟩
  · intro hf
    obtain ⟨hfH,hef⟩ := Finset.mem_filter.mp hf
    obtain ⟨x,hx,heq⟩ := triple_eq_insert_completion hH he hfH hef
    exact Finset.mem_image.mpr ⟨x,mem_completions.mpr ⟨hx,by rwa [heq]⟩,heq⟩

theorem completions_card {H : Finset (Finset V)} (hH : IsTripleSystem H)
    (e : Finset V) (he : e.card=2) :
    (completions H e).card = (H.filter (fun f => e ⊆ f)).card := by
  have hinj : Set.InjOn (fun x => insert x e) (completions H e : Set V) := by
    intro x hx y hy heq
    have hxm := (Finset.ext_iff.mp heq x).mp (Finset.mem_insert_self _ _)
    exact (Finset.mem_insert.mp hxm).resolve_right (mem_completions.mp hx).1
  rw [← completions_image hH e he,Finset.card_image_of_injOn hinj]

noncomputable def allPairs (V : Type*) [Fintype V] [DecidableEq V] : Finset (Finset V) :=
  Finset.univ.powersetCard 2

@[simp] theorem mem_allPairs {e : Finset V} : e ∈ allPairs V ↔ e.card=2 := by
  simp [allPairs,Finset.mem_powersetCard]

/-- The sum of pair codegrees is three times the number of triples. -/
theorem sum_completions {H : Finset (Finset V)} (hH : IsTripleSystem H) :
    ∑ e ∈ allPairs V, (completions H e).card = 3*H.card := by
  calc
    _ = ∑ e ∈ allPairs V, (H.filter (fun f => e ⊆ f)).card :=
      Finset.sum_congr rfl (fun e he => completions_card hH e (mem_allPairs.mp he))
    _ = ∑ e ∈ allPairs V, ∑ f ∈ H, if e ⊆ f then 1 else 0 := by simp
    _ = ∑ f ∈ H, ∑ e ∈ allPairs V, if e ⊆ f then 1 else 0 := Finset.sum_comm
    _ = ∑ f ∈ H, (f.powersetCard 2).card := by
      apply Finset.sum_congr rfl
      intro f hf
      have heq : (allPairs V).filter (fun e => e ⊆ f)=f.powersetCard 2 := by
        ext e
        simp only [Finset.mem_filter,mem_allPairs,Finset.mem_powersetCard]
        tauto
      rw [← Finset.sum_filter,← Finset.card_eq_sum_ones,heq]
    _ = ∑ _f ∈ H, 3 := by
      apply Finset.sum_congr rfl
      intro f hf
      rw [Finset.card_powersetCard,hH f hf]
      decide
    _ = _ := by simp [Nat.mul_comm]

theorem completions_degree_bound {H : Finset (Finset V)} (hH : IsTripleSystem H)
    {e : Finset V} (he : e.card=2) {v : V} (hv : v ∈ e) :
    (completions H e).card ≤ degree H v := by
  rw [completions_card hH e he]
  apply Finset.card_le_card
  intro f hf
  obtain ⟨hfH,hef⟩ := Finset.mem_filter.mp hf
  exact Finset.mem_filter.mpr ⟨hfH,hef hv⟩

end TP3
