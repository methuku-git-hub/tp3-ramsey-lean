module

public import TP3.UniformLeaves
public import TP3.Conditioning

@[expose] public section

namespace TP3

attribute [local instance] Classical.propDecidable

variable {V : Type*} [DecidableEq V]

/-- A finite family of forbidden sets encodes both forbidden pairs and
triples. The feasible choices lie in the fixed sampled vertex set X. -/
noncomputable def allowedSubsets (F : Finset (Finset V)) (X : Finset V) : Finset (Finset V) :=
  X.powerset.filter (Independent F)

/-- After U is fixed, revealing the chosen vertices outside U leaves
precisely this finite family. -/
noncomputable def outsideFiber (F : Finset (Finset V)) (X U O : Finset V) : Finset (Finset V) :=
  (allowedSubsets F X).filter (fun I => I \ U = O)

/-- The fibre of the outside observation consists exactly of the unions
of O with arbitrary subsets of the individually available vertices. -/
theorem outsideFiber_eq_image
    {F : Finset (Finset V)} {X U O : Finset V}
    (hOX : O ⊆ X) (hUX : U ⊆ X) (hOU : Disjoint O U)
    (hO : Independent F O)
    (hone : ∀ e ∈ F, e ⊆ O ∪ U →
      ∀ x ∈ e, x ∈ U → ∀ y ∈ e, y ∈ U → x = y) :
    outsideFiber F X U O =
      (U.filter (fun x => Independent F (O ∪ {x}))).powerset.image
        (fun S => O ∪ S) := by
  classical
  ext I
  simp only [outsideFiber, allowedSubsets, Finset.mem_filter, Finset.mem_powerset,
    Finset.mem_image]
  constructor
  · rintro ⟨⟨hIX,hI⟩,hIO⟩
    have heq : O ∪ (I ∩ U) = I := by
      rw [← hIO]
      ext x
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
      tauto
    refine ⟨I ∩ U, ?_, heq⟩
    apply (independent_union_iff_subset_available hO Finset.inter_subset_right hone).mp
    rwa [heq]
  · rintro ⟨S,hSM,rfl⟩
    have hSU : S ⊆ U := hSM.trans (Finset.filter_subset _ _)
    refine ⟨⟨Finset.union_subset hOX (hSU.trans hUX),
      (independent_union_iff_subset_available hO hSU hone).mpr hSM⟩,?_⟩
    ext x
    have hdis : x ∈ O → x ∉ U := fun hx => Finset.disjoint_left.mp hOU hx
    have hsin : x ∈ S → x ∈ U := fun hx => hSU hx
    simp only [Finset.mem_sdiff, Finset.mem_union]
    tauto

theorem union_injective_on_subsets {O U : Finset V} (hOU : Disjoint O U) :
    Set.InjOn (fun S : Finset V => O ∪ S) U.powerset := by
  intro S hS T hT heq
  have hSU := Finset.mem_powerset.mp hS
  have hTU := Finset.mem_powerset.mp hT
  ext x
  have hdis : x ∈ U → x ∉ O := fun hx ho => Finset.disjoint_left.mp hOU ho hx
  have hx := Finset.ext_iff.mp heq x
  simp only [Finset.mem_union] at hx
  constructor
  · intro hs
    exact (hx.mp (Or.inr hs)).resolve_left (hdis (hSU hs))
  · intro ht
    exact (hx.mpr (Or.inr ht)).resolve_left (hdis (hTU ht))

variable [Fintype V]

/-- The conditional probability of each remaining choice is exactly
2^(-|M|). This includes the normalization after revealing the outside set.
The forbidden family can contain both pairs and triples. -/
theorem leaf_conditional_probability
    {F : Finset (Finset V)} {X U O : Finset V}
    (hOX : O ⊆ X) (hUX : U ⊆ X) (hOU : Disjoint O U)
    (hO : Independent F O)
    (hone : ∀ e ∈ F, e ⊆ O ∪ U →
      ∀ x ∈ e, x ∈ U → ∀ y ∈ e, y ∈ U → x = y)
    (S : Finset V)
    (hS : S ⊆ U.filter (fun x => Independent F (O ∪ {x}))) :
    let A := allowedSubsets F X
    let P := fun I => I \ U = O
    ∃ hA : A.Nonempty, ∃ hP : 0 < (FiniteLaw.uniform A hA).event P,
      ((FiniteLaw.uniform A hA).condition P hP).prob (O ∪ S) =
        1 / (2 : ℝ) ^ (U.filter (fun x => Independent F (O ∪ {x}))).card := by
  classical
  dsimp only
  let M := U.filter (fun x => Independent F (O ∪ {x}))
  have hM : M ⊆ U := Finset.filter_subset _ _
  have hOM : Disjoint O M := hOU.mono_right hM
  have hOmem : O ∈ allowedSubsets F X := by
    simp only [allowedSubsets, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hOX,hO⟩
  have hA : (allowedSubsets F X).Nonempty := ⟨O,hOmem⟩
  have hfiber := outsideFiber_eq_image hOX hUX hOU hO hone
  have hFP : ((allowedSubsets F X).filter (fun I => I \ U = O)).Nonempty := by
    change (outsideFiber F X U O).Nonempty
    rw [hfiber]
    exact (show M.powerset.Nonempty from ⟨∅,by simp⟩).image _
  refine ⟨hA, FiniteLaw.uniform_event_pos _ hA _ hFP, ?_⟩
  rw [FiniteLaw.uniform_condition_prob _ hA _ hFP]
  have hmem : O ∪ S ∈ (allowedSubsets F X).filter (fun I => I \ U = O) := by
    change O ∪ S ∈ outsideFiber F X U O
    rw [hfiber]
    exact Finset.mem_image.mpr ⟨S,Finset.mem_powerset.mpr hS,rfl⟩
  have hcard : ((allowedSubsets F X).filter (fun I => I \ U = O)).card =
      2 ^ M.card := by
    change (outsideFiber F X U O).card = _
    rw [hfiber, Finset.card_image_of_injOn (union_injective_on_subsets hOM),
      Finset.card_powerset]
  simp only [FiniteLaw.uniform, ite_eq_left hmem, hcard, Nat.cast_pow, Nat.cast_ofNat]
  rfl

end TP3
