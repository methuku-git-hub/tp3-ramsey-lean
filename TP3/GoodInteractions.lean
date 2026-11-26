module

public import TP3.InteractionVertices
public import TP3.LinkCosts
public import TP3.RestrictionEvents

@[expose] public section

namespace TP3.StarOrientation

attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {H : Finset (Finset V)} {v : V} (O : StarOrientation (link H v))

noncomputable def interactionSupport (e : Finset V) : Finset V := e ∪ e.image O.centre

theorem interactionSupport_pair (x y : V) :
    O.interactionSupport {x,y}={x,y,O.centre x,O.centre y} := by
  ext z
  simp [interactionSupport]
  tauto

theorem interactionSupport_card (hind : IndependentPairNeighborhoods H)
    {e : Finset V} (he : e ∈ O.leaves.powersetCard 2)
    (hne : (completions H e).Nonempty) : (O.interactionSupport e).card=4 := by
  obtain ⟨heA,hecard⟩ := Finset.mem_powersetCard.mp he
  obtain ⟨x,y,hxy,rfl⟩ := Finset.card_eq_two.mp hecard
  obtain ⟨z,hz⟩ := hne
  have hxyz : ({x,y,z} : Finset V) ∈ H := by
    rw [triple_rotate x y z]
    exact (mem_completions.mp hz).2
  have hd := O.interaction_four_distinct hind (heA (by simp)) (heA (by simp)) hxy hxyz (by simp)
  rw [O.interactionSupport_pair]
  simpa using List.toFinset_card_of_nodup hd

theorem tripleInteractionSupport_card (hH : IsTripleSystem H) (hind : IndependentPairNeighborhoods H)
    {e : Finset V} (he : e ∈ O.leaves.powersetCard 2) {z : V} (hz : z ∈ completions H e) :
    (insert z (O.interactionSupport e)).card=5 := by
  obtain ⟨heA,hecard⟩ := Finset.mem_powersetCard.mp he
  obtain ⟨x,y,hxy,rfl⟩ := Finset.card_eq_two.mp hecard
  have hxyz : ({x,y,z} : Finset V) ∈ H := by
    rw [triple_rotate x y z]
    exact (mem_completions.mp hz).2
  have hd := O.interaction_five_distinct hH hind (heA (by simp)) (heA (by simp)) hxyz
  have hc : ({x,y,O.centre x,O.centre y,z} : Finset V).card=5 := by
    simpa using List.toFinset_card_of_nodup hd
  rw [O.interactionSupport_pair]
  convert hc using 1
  congr 1
  ext w
  simp
  tauto

def BadPair (ω : RestrictionData V) : Prop :=
  ∃ e ∈ O.leaves.powersetCard 2, (∀ x ∈ O.interactionSupport e, ω.1 x=true) ∧ ω.2 e=false

def BadTriple (ω : RestrictionData V) : Prop :=
  ∃ e ∈ O.leaves.powersetCard 2, ∃ z ∈ completions H e,
    z ≠ v ∧ ∀ x ∈ insert z (O.interactionSupport e), ω.1 x=true

def GoodInteractions (ω : RestrictionData V) : Prop := ¬ O.BadPair ω ∧ ¬ O.BadTriple ω

theorem badPair_probability (hind : IndependentPairNeighborhoods H)
    (p δ : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hδ : 0 ≤ δ) :
    (restrictionDataLaw (codegreeCost H) (codegreeCost_nonneg H) p δ hp hp1 hδ).event O.BadPair ≤
      δ*p^4*pairCost (codegreeCost H) O.leaves := by
  let μ := restrictionDataLaw (codegreeCost H) (codegreeCost_nonneg H) p δ hp hp1 hδ
  calc
    _ ≤ ∑ e ∈ O.leaves.powersetCard 2, μ.event
        (fun ω => (∀ x ∈ O.interactionSupport e, ω.1 x=true) ∧ ω.2 e=false) :=
      μ.event_exists_finset_le_sum _ _
    _ ≤ ∑ e ∈ O.leaves.powersetCard 2, δ*p^4*codegreeCost H e := by
      apply Finset.sum_le_sum
      intro e he
      rw [restriction_forbidden_pair]
      by_cases hn : (completions H e).Nonempty
      · rw [O.interactionSupport_card hind he hn]
        have hh := mul_le_mul_of_nonneg_left (one_sub_exp_neg_le (δ*codegreeCost H e)) (pow_nonneg hp 4)
        rw [neg_mul]
        nlinarith only [hh]
      · have hz : codegreeCost H e=0 := by
          simp only [codegreeCost,Finset.not_nonempty_iff_eq_empty.mp hn,Finset.card_empty,Nat.cast_zero]
        simp [hz]
    _ = _ := by rw [pairCost,Finset.mul_sum]

theorem badTriple_probability (hH : IsTripleSystem H) (hind : IndependentPairNeighborhoods H)
    (p δ : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hδ : 0 ≤ δ) :
    (restrictionDataLaw (codegreeCost H) (codegreeCost_nonneg H) p δ hp hp1 hδ).event O.BadTriple ≤
      p^5*pairCost (codegreeCost H) O.leaves := by
  let μ := restrictionDataLaw (codegreeCost H) (codegreeCost_nonneg H) p δ hp hp1 hδ
  calc
    _ ≤ ∑ e ∈ O.leaves.powersetCard 2, μ.event
        (fun ω => ∃ z ∈ completions H e, z ≠ v ∧
          ∀ x ∈ insert z (O.interactionSupport e), ω.1 x=true) := μ.event_exists_finset_le_sum _ _
    _ ≤ ∑ e ∈ O.leaves.powersetCard 2, p^5*codegreeCost H e := by
      apply Finset.sum_le_sum
      intro e he
      calc
        _ ≤ ∑ z ∈ completions H e, μ.event (fun ω => z ≠ v ∧
            ∀ x ∈ insert z (O.interactionSupport e), ω.1 x=true) := μ.event_exists_finset_le_sum _ _
        _ ≤ ∑ _z ∈ completions H e, p^5 := by
          apply Finset.sum_le_sum
          intro z hz
          calc
            _ ≤ μ.event (fun ω => ∀ x ∈ insert z (O.interactionSupport e), ω.1 x=true) :=
              μ.event_mono (fun _ hh => hh.2)
            _ = p^5 := by rw [restriction_vertices_required,O.tripleInteractionSupport_card hH hind he hz]
        _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,codegreeCost,mul_comm]
    _ = _ := by rw [pairCost,Finset.mul_sum]

theorem goodInteractions_probability (hH : IsTripleSystem H) (hind : IndependentPairNeighborhoods H)
    (D : ℝ) (hD0 : 0 ≤ D) (hD : ∀ x, (degree H x : ℝ) ≤ D)
    (p δ : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hδ : 0 ≤ δ) :
    1-D^2*(δ*p^4+p^5) ≤
      (restrictionDataLaw (codegreeCost H) (codegreeCost_nonneg H) p δ hp hp1 hδ).event O.GoodInteractions := by
  let μ := restrictionDataLaw (codegreeCost H) (codegreeCost_nonneg H) p δ hp hp1 hδ
  have hpairs := O.badPair_probability hind p δ hp hp1 hδ
  have htriples := O.badTriple_probability hH hind p δ hp hp1 hδ
  have hcost := leaf_pairCost_bound hH O D hD0 hD
  have hunion := μ.event_or_le O.BadPair O.BadTriple
  have hnot : O.GoodInteractions = (fun ω => ¬ (O.BadPair ω ∨ O.BadTriple ω)) := by
    funext ω
    simp only [GoodInteractions,not_or]
  rw [hnot,μ.event_not]
  have hweighted := mul_le_mul_of_nonneg_left hcost
    (show 0 ≤ δ*p^4+p^5 by positivity)
  linarith

end TP3.StarOrientation
