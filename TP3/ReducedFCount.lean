module

public import TP3.ReducedSystem

@[expose] public section

namespace TP3

attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev FIndex (V : Type*) := Finset V × Finset V × V

/-- An unordered outer pair, unordered inner pair, and final vertex
specify a copy of F. Ordering either pair is unnecessary for deletion. -/
noncomputable def fInstances (H : Finset (Finset V)) : Finset (FIndex V) :=
  (allPairs V).biUnion (fun e => (completions H e).powersetCard 2 |>.biUnion
    (fun f => ((completions H f).filter (fun z => z ∉ e)).image (fun z => (e,f,z))))

def fSupport (j : FIndex V) : Finset V := j.1 ∪ insert j.2.2 j.2.1

theorem fInstances_card_le (H : Finset (Finset V)) :
    (fInstances H).card ≤
      ∑ e ∈ allPairs V, ∑ f ∈ (completions H e).powersetCard 2, (completions H f).card := by
  calc
    _ ≤ ∑ e ∈ allPairs V,
      (((completions H e).powersetCard 2).biUnion
        (fun f => ((completions H f).filter (fun z => z ∉ e)).image (fun z => (e,f,z)))).card :=
      Finset.card_biUnion_le
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro e he
      apply le_trans Finset.card_biUnion_le
      apply Finset.sum_le_sum
      intro f hf
      exact Finset.card_image_le.trans (Finset.card_filter_le _ _)

namespace DenseDecomposition

variable {H : Finset (Finset V)} {a s : ℝ}
variable (P : DenseDecomposition (mediumPairs H a s) s a)

theorem reduced_inner_sum (ha : 0 ≤ a) (hs : 0 ≤ s) (c r : ℝ) (hc : 0 ≤ c) (hr0 : 0 ≤ r)
    (hr : ∀ x, ((P.blocks.filter (fun b => x ∈ b.1)).card : ℝ) ≤ r)
    {e : Finset V} (he : e.card=2) :
    (∑ f ∈ (completions (P.reducedSystem c) e).powersetCard 2,
      ((completions (P.reducedSystem c) f).card : ℝ)) ≤
        s*(2*a+c*r)*(completions (P.reducedSystem c) e).card := by
  let K := P.reducedSystem c
  let Y := completions K e
  have hY : (Y.card : ℝ) ≤ s := P.reduced_pair_bound c hs he
  have hpairs : ((Y.powersetCard 2).card : ℝ) ≤ (Y.card : ℝ)^2 := by
    rw [Finset.card_powersetCard]
    exact_mod_cast Nat.choose_le_pow Y.card 2
  by_cases heG : e ∈ mediumPairs H a s
  · have hmedium := P.reduced_medium_density ha hs c r hc hr heG
    have hsum : (∑ f ∈ Y.powersetCard 2, ((completions K f).card : ℝ)) ≤
        a*(Y.powersetCard 2).card + s*(induced (mediumPairs H a s) Y).card := by
      calc
        _ ≤ ∑ f ∈ Y.powersetCard 2, (a + if f ∈ mediumPairs H a s then s else 0) := by
          apply Finset.sum_le_sum
          intro f hf
          have hfcard := (Finset.mem_powersetCard.mp hf).2
          by_cases hfG : f ∈ mediumPairs H a s
          · rw [ite_eq_left hfG]
            have hb := P.reduced_pair_bound c hs hfcard
            linarith
          · rw [ite_eq_right hfG,add_zero]
            exact P.reduced_nonmedium_bound c ha hfcard hfG
        _ = a*(Y.powersetCard 2).card +
            ∑ f ∈ (Y.powersetCard 2).filter (fun f => f ∈ mediumPairs H a s), s := by
          rw [Finset.sum_add_distrib,← Finset.sum_filter]
          simp [mul_comm]
        _ = _ := by
          have heq : (Y.powersetCard 2).filter (fun f => f ∈ mediumPairs H a s) =
              induced (mediumPairs H a s) Y := by
            ext f
            simp only [Finset.mem_filter,Finset.mem_powersetCard,induced]
            exact ⟨fun hh => ⟨hh.2,hh.1.1⟩,fun hh =>
              ⟨⟨hh.2,mediumPairs_isPairSystem H a s f hh.1⟩,hh.1⟩⟩
          rw [heq]
          simp [mul_comm]
    have hp : a*(Y.powersetCard 2).card ≤ a*s*Y.card := by
      have hy0 : (0:ℝ) ≤ Y.card := Nat.cast_nonneg _
      nlinarith [mul_le_mul_of_nonneg_left hpairs ha,
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hY hy0) ha]
    have hm := mul_le_mul_of_nonneg_left hmedium hs
    change (∑ f ∈ Y.powersetCard 2, ((completions K f).card : ℝ)) ≤ _
    change s*(induced (mediumPairs H a s) Y).card ≤ s*((a+c*r)*Y.card) at hm
    nlinarith
  · have hlow : (Y.card : ℝ) ≤ a := P.reduced_nonmedium_bound c ha he heG
    have hsum : (∑ f ∈ Y.powersetCard 2, ((completions K f).card : ℝ)) ≤
        s*(Y.powersetCard 2).card := by
      calc
        _ ≤ ∑ _f ∈ Y.powersetCard 2, s :=
          Finset.sum_le_sum (fun f hf => P.reduced_pair_bound c hs (Finset.mem_powersetCard.mp hf).2)
        _ = _ := by simp [mul_comm]
    have hsq : (Y.card : ℝ)^2 ≤ a*Y.card := by
      nlinarith [Nat.cast_nonneg (α := ℝ) Y.card]
    have hh := hsum.trans (mul_le_mul_of_nonneg_left (hpairs.trans hsq) hs)
    change (∑ f ∈ Y.powersetCard 2, ((completions K f).card : ℝ)) ≤ _
    have hnonneg : 0 ≤ s*(a+c*r)*(Y.card : ℝ) := by positivity
    nlinarith

/-- Count F using unordered outer and inner pairs. This is four times
smaller than the ordered-copy convention, and suffices for deletion. -/
theorem reduced_f_count (hH : IsTripleSystem H) (ha : 0 ≤ a) (hs : 0 ≤ s)
    (c r : ℝ) (hc : 0 ≤ c) (hr0 : 0 ≤ r)
    (hr : ∀ x, ((P.blocks.filter (fun b => x ∈ b.1)).card : ℝ) ≤ r) :
    ((fInstances (P.reducedSystem c)).card : ℝ) ≤
      s*(2*a+c*r)*(3*(H.card : ℝ)) := by
  have hcount : ((fInstances (P.reducedSystem c)).card : ℝ) ≤
      ∑ e ∈ allPairs V, ∑ f ∈ (completions (P.reducedSystem c) e).powersetCard 2,
        ((completions (P.reducedSystem c) f).card : ℝ) := by
    exact_mod_cast fInstances_card_le (P.reducedSystem c)
  have hsum : (∑ e ∈ allPairs V, ((completions (P.reducedSystem c) e).card : ℝ)) ≤ 3*(H.card : ℝ) := by
    have heq := sum_completions (P.reducedSystem_triples hH c)
    calc
      _ = 3*((P.reducedSystem c).card : ℝ) := by exact_mod_cast heq
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (by exact_mod_cast Finset.card_le_card (P.reducedSystem_subset c)) (by norm_num : (0:ℝ) ≤ 3)
  calc
    _ ≤ _ := hcount
    _ ≤ ∑ e ∈ allPairs V, s*(2*a+c*r)*(completions (P.reducedSystem c) e).card :=
      Finset.sum_le_sum (fun e he => P.reduced_inner_sum ha hs c r hc hr0 hr (mem_allPairs.mp he))
    _ = s*(2*a+c*r)*(∑ e ∈ allPairs V, ((completions (P.reducedSystem c) e).card : ℝ)) := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)

end DenseDecomposition
end TP3
