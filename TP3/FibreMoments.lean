module

public import TP3.CentreConditioning
public import TP3.LinkCosts

@[expose] public section

namespace TP3

attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem union_inter_eq_of_subsets {A U M S : Finset V}
    (hAU : Disjoint A U) (hMU : M ⊆ U) (hSM : S ⊆ M) : (A∪S)∩U=S := by
  ext x
  have hd := Finset.disjoint_left.mp hAU
  simp only [Finset.mem_inter,Finset.mem_union]
  exact ⟨fun hx => hx.1.elim (fun ha => False.elim (hd ha hx.2)) id,
    fun hx => ⟨Or.inr hx,hMU (hSM hx)⟩⟩

/-- Conditional on a valid outside fibre, each available leaf has
conditional inclusion probability one half. -/
theorem union_powerset_mean_inter (A U M : Finset V) (hAU : Disjoint A U) (hMU : M ⊆ U) :
    (FiniteLaw.uniform (M.powerset.image (fun S => A∪S))
      ((show M.powerset.Nonempty from ⟨∅,by simp⟩).image _)).mean
      (fun I => ((I∩U).card : ℝ)) = (M.card : ℝ)/2 := by
  rw [FiniteLaw.uniform_image_mean M.powerset ⟨∅,by simp⟩ _
    (union_injective_on_subsets (hAU.mono_right hMU))]
  calc
    _ = (FiniteLaw.uniform M.powerset ⟨∅,by simp⟩).mean (fun S => (S.card : ℝ)) := by
      erw [FiniteLaw.uniform_mean,FiniteLaw.uniform_mean]
      congr 1
      apply Finset.sum_congr rfl
      intro S hS
      rw [union_inter_eq_of_subsets hAU hMU (Finset.mem_powerset.mp hS)]
    _ = _ := uniform_powerset_mean_card M

/-- The only member of the fibre with no chosen active leaf is the
revealed outside set itself. The weight may be any function of I. -/
theorem union_powerset_mean_empty (A U M : Finset V) (hAU : Disjoint A U) (hMU : M ⊆ U)
    (f : Finset V → ℝ) :
    (FiniteLaw.uniform (M.powerset.image (fun S => A∪S))
      ((show M.powerset.Nonempty from ⟨∅,by simp⟩).image _)).mean
      (fun I => if I∩U=∅ then f I else 0) = f A/(2:ℝ)^M.card := by
  rw [FiniteLaw.uniform_image_mean M.powerset ⟨∅,by simp⟩ _
    (union_injective_on_subsets (hAU.mono_right hMU))]
  erw [FiniteLaw.uniform_mean]
  have hsum : (∑ S ∈ M.powerset, if (A∪S)∩U=∅ then f (A∪S) else 0)=f A := by
    calc
      _ = ∑ S ∈ M.powerset, if S=∅ then f A else 0 := by
        apply Finset.sum_congr rfl
        intro S hS
        rw [union_inter_eq_of_subsets hAU hMU (Finset.mem_powerset.mp hS)]
        by_cases h : S=∅ <;> simp [h]
      _ = _ := by simp
  rw [hsum,Finset.card_powerset,Nat.cast_pow,Nat.cast_ofNat]

namespace StarOrientation

variable {H : Finset (Finset V)} {v : V} (O : StarOrientation (link H v))

/-- Every set in the observation fibre uses the same active leaf set.
This is the point at which the centres-first order is needed. -/
theorem linkCount_in_fiber {X I I₀ : Finset V} (hIX : I ⊆ X)
    (hobs : O.observation X I=O.observation X I₀) :
    linkCount H v I = ((I∩O.activeLeaves X (I₀∩O.centres)).card : ℝ) := by
  have hc := congrArg Prod.fst hobs
  change I∩O.centres=I₀∩O.centres at hc
  rw [linkCount,← O.chosenLeaves_count I,O.chosenLeaves_eq_inter hIX,hc]

end StarOrientation
end TP3
