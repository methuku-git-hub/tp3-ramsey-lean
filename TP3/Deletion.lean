module

public import TP3.Structure

@[expose] public section

namespace TP3

variable {V : Type*} [DecidableEq V]

/-- Choose one vertex from each nonempty forbidden set. The choice is a
fixed function of the set, so this introduces no additional randomness. -/
noncomputable def deletionVertices (F : Finset (Finset V))
    (hF : ∀ e ∈ F, e.Nonempty) : Finset V :=
  F.attach.image (fun e => (hF e.val e.property).choose)

/-- Delete at most one vertex per forbidden set. -/
noncomputable def deleteForbidden (F : Finset (Finset V))
    (hF : ∀ e ∈ F, e.Nonempty) (A : Finset V) : Finset V :=
  A \ deletionVertices F hF

theorem deletionVertices_card_le (F : Finset (Finset V))
    (hF : ∀ e ∈ F, e.Nonempty) : (deletionVertices F hF).card ≤ F.card := by
  exact (Finset.card_image_le).trans_eq Finset.card_attach

theorem deleteForbidden_subset (F : Finset (Finset V))
    (hF : ∀ e ∈ F, e.Nonempty) (A : Finset V) : deleteForbidden F hF A ⊆ A :=
  Finset.sdiff_subset

theorem deleteForbidden_independent (F : Finset (Finset V))
    (hF : ∀ e ∈ F, e.Nonempty) (A : Finset V) :
    Independent F (deleteForbidden F hF A) := by
  intro e he hsub
  let x := (hF e he).choose
  have hxe : x ∈ e := (hF e he).choose_spec
  have hdel : x ∈ deletionVertices F hF := by
    apply Finset.mem_image.mpr
    exact ⟨⟨e,he⟩,Finset.mem_attach _ _,rfl⟩
  exact (Finset.mem_sdiff.mp (hsub hxe)).2 hdel

theorem deleteForbidden_size (F : Finset (Finset V))
    (hF : ∀ e ∈ F, e.Nonempty) (A : Finset V) :
    A.card ≤ (deleteForbidden F hF A).card + F.card := by
  have hcover : A ⊆ deleteForbidden F hF A ∪ deletionVertices F hF := by
    intro x hx
    by_cases hd : x ∈ deletionVertices F hF
    · exact Finset.mem_union_right _ hd
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx,hd⟩)
  calc
    A.card ≤ (deleteForbidden F hF A ∪ deletionVertices F hF).card :=
      Finset.card_le_card hcover
    _ ≤ (deleteForbidden F hF A).card + (deletionVertices F hF).card :=
      Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add_left (deletionVertices_card_le F hF) _

/-- It suffices to delete for forbidden sets that are entirely present.
This is the version used for the conflict graph and for final deletions. -/
theorem delete_present_forbidden {F : Finset (Finset V)}
    (hF : ∀ e ∈ F, e.Nonempty) (A : Finset V) :
    ∃ B : Finset V, B ⊆ A ∧ Independent F B ∧
      A.card ≤ B.card + (F.filter (fun e => e ⊆ A)).card := by
  classical
  let E := F.filter (fun e => e ⊆ A)
  have hE : ∀ e ∈ E, e.Nonempty := fun e he => hF e (Finset.mem_filter.mp he).1
  refine ⟨deleteForbidden E hE A,deleteForbidden_subset E hE A,?_,
    deleteForbidden_size E hE A⟩
  intro e he hsub
  have hea : e ⊆ A := hsub.trans (deleteForbidden_subset E hE A)
  exact deleteForbidden_independent E hE A e (Finset.mem_filter.mpr ⟨he,hea⟩) hsub

end TP3
