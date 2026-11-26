module

public import TP3.Conditioning
public import TP3.Definitions

@[expose] public section

namespace TP3

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- F is the family omitting v; E consists of the members of F that
can be extended by v. These are exactly the two parts of the full family. -/
def insertedFamily (F E : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  F ∪ E.image (insert v)

omit [Fintype V] in
theorem insert_injective_on_omitting (F : Finset (Finset V)) (v : V)
    (hv : ∀ S ∈ F, v ∉ S) :
    Set.InjOn (fun S : Finset V => insert v S) (F : Set (Finset V)) := by
  intro S hS T hT heq
  ext x
  have hx := Finset.ext_iff.mp heq x
  simp only [Finset.mem_insert] at hx
  by_cases hxv : x = v
  · subst x
    simp [hv S hS, hv T hT]
  · simpa [hxv] using hx

/-- The exact finite counting identity underlying the insertion inequality. -/
theorem uniform_insert_probability
    (F E : Finset (Finset V)) (v : V) (hF : F.Nonempty)
    (hEF : E ⊆ F) (hv : ∀ S ∈ F, v ∉ S) :
    (FiniteLaw.uniform (insertedFamily F E v)
      (hF.mono Finset.subset_union_left)).event (fun S => v ∈ S) =
      (E.card : ℝ) / ((F.card : ℝ) + E.card) := by
  classical
  have hvinj := insert_injective_on_omitting E v (fun S hS => hv S (hEF hS))
  have hdis : Disjoint F (E.image (insert v)) := by
    apply Finset.disjoint_left.mpr
    intro S hSF hSE
    obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hSE
    exact hv (insert v T) hSF (Finset.mem_insert_self _ _)
  have hfilter : (insertedFamily F E v).filter (fun S => v ∈ S) =
      E.image (insert v) := by
    ext S
    simp only [insertedFamily, Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hF' | hE',hvS⟩
      · exact False.elim ((hv S hF') hvS)
      · exact hE'
    · intro hE'
      refine ⟨Or.inr hE',?_⟩
      obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hE'
      exact Finset.mem_insert_self _ _
  rw [FiniteLaw.uniform_event, hfilter]
  simp only [insertedFamily, Finset.card_union_of_disjoint hdis,
    Finset.card_image_of_injOn hvinj, Nat.cast_add]

/-- The extension fraction loses at most a factor of two when the
extendible sets and the original sets are counted together. -/
theorem uniform_insert_lower_bound
    (F E : Finset (Finset V)) (v : V) (hF : F.Nonempty)
    (hEF : E ⊆ F) (hv : ∀ S ∈ F, v ∉ S) :
    ((E.card : ℝ) / F.card) / 2 ≤
      (FiniteLaw.uniform (insertedFamily F E v)
        (hF.mono Finset.subset_union_left)).event (fun S => v ∈ S) := by
  rw [uniform_insert_probability F E v hF hEF hv]
  have hFc : 0 < (F.card : ℝ) := by exact_mod_cast hF.card_pos
  have hEc : (E.card : ℝ) ≤ F.card := by exact_mod_cast Finset.card_le_card hEF
  have hden : 0 < (F.card : ℝ) + E.card := by positivity
  have heq : ((E.card : ℝ) / F.card) / 2 = E.card / (2*(F.card : ℝ)) := by ring
  rw [heq]
  apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) hden
  linarith

end TP3
