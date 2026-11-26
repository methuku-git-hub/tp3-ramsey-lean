module

public import TP3.CentreConditioning
public import TP3.RestrictionLaw

@[expose] public section

namespace TP3

attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def codegreeCost (H : Finset (Finset V)) (e : Finset V) : ℝ :=
  (completions H e).card

theorem codegreeCost_nonneg (H : Finset (Finset V)) (e : Finset V) : 0 ≤ codegreeCost H e :=
  Nat.cast_nonneg _

noncomputable def linkCount (H : Finset (Finset V)) (v : V) (S : Finset V) : ℝ :=
  (induced (linkPairs H v) S).card

theorem linkCount_sum (H : Finset (Finset V)) (S : Finset V) :
    ∑ v : V, linkCount H v S = pairCost (codegreeCost H) S := by
  have heq (v : V) : induced (linkPairs H v) S =
      (S.powersetCard 2).filter (fun e => v ∈ completions H e) := by
    ext e
    simp only [induced,linkPairs,Finset.mem_filter,mem_allPairs,Finset.mem_powersetCard,mem_completions]
    tauto
  calc
    _ = ∑ v : V, ∑ e ∈ S.powersetCard 2, if v ∈ completions H e then (1:ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [linkCount,heq v]
      simp
    _ = ∑ e ∈ S.powersetCard 2, ∑ v : V, if v ∈ completions H e then (1:ℝ) else 0 := Finset.sum_comm
    _ = _ := by
      unfold pairCost codegreeCost
      apply Finset.sum_congr rfl
      intro e he
      simp only [← Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.univ_inter,
        Finset.sum_const,nsmul_eq_mul,mul_one]

noncomputable def orderedCost (H : Finset (Finset V)) (x y : V) : ℝ :=
  if x=y then 0 else codegreeCost H {x,y}

theorem orderedCost_nonneg (H : Finset (Finset V)) (x y : V) : 0 ≤ orderedCost H x y := by
  unfold orderedCost
  split
  · exact le_rfl
  · exact codegreeCost_nonneg _ _

theorem orderedCost_symm (H : Finset (Finset V)) (x y : V) : orderedCost H x y=orderedCost H y x := by
  simp only [orderedCost,eq_comm,Finset.pair_comm]

theorem orderedCost_sum {H : Finset (Finset V)} (hH : IsTripleSystem H) (x : V) :
    ∑ y : V, orderedCost H x y = 2*(degree H x : ℝ) := by
  calc
    _ = ∑ y ∈ Finset.univ.erase x, codegreeCost H {x,y} := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ x)]
      have hself : orderedCost H x x=0 := by simp [orderedCost]
      rw [hself,add_zero]
      apply Finset.sum_congr rfl
      intro y hy
      simp only [orderedCost,ite_eq_right (Finset.mem_erase.mp hy).1.symm]
    _ = ∑ e ∈ (allPairs V).filter (fun e => x ∈ e), codegreeCost H e := by
      apply Finset.sum_bij (fun y _ => ({x,y} : Finset V))
      · intro y hy
        exact Finset.mem_filter.mpr ⟨mem_allPairs.mpr
          (by simp [(Finset.mem_erase.mp hy).1.symm]),by simp⟩
      · intro y hy z hz heq
        exact pair_image_injective x heq
      · intro e he
        obtain ⟨heP,hxe⟩ := Finset.mem_filter.mp he
        obtain ⟨y,hy,rfl⟩ := pair_eq_pair_of_mem (mem_allPairs.mp heP) hxe
        exact ⟨y,by simp [hy],rfl⟩
      · intro y hy
        rfl
    _ = _ := by unfold codegreeCost; exact_mod_cast sum_completions_at_vertex hH x

noncomputable def incidentCost (H : Finset (Finset V)) (v : V) (S : Finset V) : ℝ :=
  ∑ x ∈ S, orderedCost H v x

theorem incidentCost_nonneg (H : Finset (Finset V)) (v : V) (S : Finset V) :
    0 ≤ incidentCost H v S := Finset.sum_nonneg (fun x _ => orderedCost_nonneg H v x)

theorem incidentCost_mono (H : Finset (Finset V)) (v : V) {S T : Finset V} (hST : S ⊆ T) :
    incidentCost H v S ≤ incidentCost H v T :=
  Finset.sum_le_sum_of_subset_of_nonneg hST (fun x _ _ => orderedCost_nonneg H v x)

theorem incidentCost_sum {H : Finset (Finset V)} (hH : IsTripleSystem H) (S : Finset V) :
    ∑ v : V, incidentCost H v S = 2*∑ x ∈ S, (degree H x : ℝ) := by
  unfold incidentCost
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  simp_rw [orderedCost_symm H _ x]
  exact orderedCost_sum hH x

theorem incidentCost_sum_le {H : Finset (Finset V)} (hH : IsTripleSystem H)
    (D : ℝ) (hD : ∀ x, (degree H x : ℝ) ≤ D) (S : Finset V) :
    ∑ v : V, incidentCost H v S ≤ 2*D*S.card := by
  rw [incidentCost_sum hH]
  calc
    _ ≤ 2*∑ _x ∈ S, D := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun x _ => hD x)) (by norm_num)
    _ = _ := by simp; ring

/-- Charge each pair to its two endpoints, then use the full incident
codegree sum at each endpoint. -/
theorem pairCost_le_degree_sum {H : Finset (Finset V)} (hH : IsTripleSystem H) (S : Finset V) :
    pairCost (codegreeCost H) S ≤ ∑ x ∈ S, (degree H x : ℝ) := by
  have hdouble : (∑ x ∈ S, ∑ e ∈ (S.powersetCard 2).filter (fun e => x ∈ e), codegreeCost H e) =
      2*pairCost (codegreeCost H) S := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm, pairCost,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    have heS := (Finset.mem_powersetCard.mp he).1
    have hecard := (Finset.mem_powersetCard.mp he).2
    have heq : S.filter (fun x => x ∈ e)=e := by ext x; simp; exact fun hx => heS hx
    rw [← Finset.sum_filter,heq,Finset.sum_const,hecard]
    simp
  have hbound : (∑ x ∈ S, ∑ e ∈ (S.powersetCard 2).filter (fun e => x ∈ e), codegreeCost H e) ≤
      2*∑ x ∈ S, (degree H x : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x hx
    calc
      _ ≤ ∑ e ∈ (allPairs V).filter (fun e => x ∈ e), codegreeCost H e := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro e he
          obtain ⟨heS,hxe⟩ := Finset.mem_filter.mp he
          exact Finset.mem_filter.mpr ⟨mem_allPairs.mpr (Finset.mem_powersetCard.mp heS).2,hxe⟩
        · exact fun e _ _ => codegreeCost_nonneg H e
      _ = _ := by unfold codegreeCost; exact_mod_cast sum_completions_at_vertex hH x
  linarith

theorem leaf_pairCost_bound {H : Finset (Finset V)} (hH : IsTripleSystem H)
    {v : V} (O : StarOrientation (link H v)) (D : ℝ) (hD0 : 0 ≤ D)
    (hD : ∀ x, (degree H x : ℝ) ≤ D) : pairCost (codegreeCost H) O.leaves ≤ D^2 := by
  have hcard : (O.leaves.card : ℝ) ≤ D :=
    (show (O.leaves.card : ℝ) ≤ degree H v by exact_mod_cast O.leaves_card_le hH).trans (hD v)
  calc
    _ ≤ ∑ x ∈ O.leaves, (degree H x : ℝ) := pairCost_le_degree_sum hH _
    _ ≤ ∑ _x ∈ O.leaves, D := Finset.sum_le_sum (fun x _ => hD x)
    _ = D*O.leaves.card := by simp [mul_comm]
    _ ≤ D^2 := by nlinarith [mul_le_mul_of_nonneg_left hcard hD0]

end TP3
