module

public import TP3.Configurations

@[expose] public section

namespace TP3

variable {V : Type*} [DecidableEq V]

/-- Each four-element subset contains a triple. This is vacuous for a
pair or triple, and holds for the five vertices of the configuration F. -/
def FourVertexProperty (H : Finset (Finset V)) (W : Finset V) : Prop :=
  ∀ T ⊆ W, T.card=4 → ∃ e ∈ H, e ⊆ T

theorem fourVertexProperty_small (H : Finset (Finset V)) (W : Finset V)
    (hW : W.card ≤ 3) : FourVertexProperty H W := by
  intro T hTW hT
  have := Finset.card_le_card hTW
  omega

theorem fourVertexProperty_F {H : Finset (Finset V)} {a b x y z : V}
    (hd : [a,b,x,y,z].Pairwise (· ≠ ·))
    (habx : ({a,b,x} : Finset V) ∈ H)
    (haby : ({a,b,y} : Finset V) ∈ H)
    (hxyz : ({x,y,z} : Finset V) ∈ H) :
    FourVertexProperty H {a,b,x,y,z} := by
  intro T hTW hT
  have hcard : ({a,b,x,y,z} : Finset V).card=5 := by
    simpa using List.toFinset_card_of_nodup hd
  have hdiff : (({a,b,x,y,z} : Finset V) \ T).card=1 := by
    rw [Finset.card_sdiff_of_subset hTW,hcard,hT]
  obtain ⟨w,hw⟩ := Finset.card_eq_one.mp hdiff
  have hwmem : w ∈ ({a,b,x,y,z} : Finset V) := by
    have hh : w ∈ ({a,b,x,y,z} : Finset V) \ T := by rw [hw]; simp
    exact (Finset.mem_sdiff.mp hh).1
  have hkeep {v : V} (hv : v ∈ ({a,b,x,y,z} : Finset V)) (hvw : v ≠ w) : v ∈ T := by
    by_contra hnot
    have hh : v ∈ ({a,b,x,y,z} : Finset V) \ T := Finset.mem_sdiff.mpr ⟨hv,hnot⟩
    rw [hw,Finset.mem_singleton] at hh
    exact hvw hh
  simp only [List.pairwise_cons,List.mem_cons,List.not_mem_nil,forall_eq_or_imp] at hd
  simp only [Finset.mem_insert,Finset.mem_singleton] at hwmem
  rcases hwmem with rfl | rfl | rfl | rfl | rfl
  · refine ⟨{x,y,z},hxyz,?_⟩
    simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]
    exact ⟨hkeep (by simp) (by aesop),hkeep (by simp) (by aesop),hkeep (by simp) (by aesop)⟩
  · refine ⟨{x,y,z},hxyz,?_⟩
    simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]
    exact ⟨hkeep (by simp) (by aesop),hkeep (by simp) (by aesop),hkeep (by simp) (by aesop)⟩
  · refine ⟨{a,b,y},haby,?_⟩
    simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]
    exact ⟨hkeep (by simp) (by aesop),hkeep (by simp) (by aesop),hkeep (by simp) (by aesop)⟩
  · refine ⟨{a,b,x},habx,?_⟩
    simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]
    exact ⟨hkeep (by simp) (by aesop),hkeep (by simp) (by aesop),hkeep (by simp) (by aesop)⟩
  · refine ⟨{a,b,x},habx,?_⟩
    simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]
    exact ⟨hkeep (by simp) (by aesop),hkeep (by simp) (by aesop),hkeep (by simp) (by aesop)⟩

end TP3
