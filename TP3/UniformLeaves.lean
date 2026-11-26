module

public import TP3.LeafChoices
public import TP3.FiniteSampling
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

@[expose] public section

namespace TP3

open scoped BigOperators

variable {V : Type*} [DecidableEq V]

/-- Each vertex belongs to exactly half the subsets of a finite set,
expressed as the sum of their cardinalities. -/
theorem twice_sum_card_powerset (M : Finset V) :
    2 * (∑ S ∈ M.powerset, (S.card : ℝ)) = (M.card : ℝ) * 2 ^ M.card := by
  induction M using Finset.induction_on with
  | empty => simp
  | @insert a M ha ih =>
    rw [Finset.sum_powerset_insert ha]
    have hs : (∑ S ∈ M.powerset, ((insert a S).card : ℝ)) =
        (∑ S ∈ M.powerset, (S.card : ℝ)) + (2 : ℝ) ^ M.card := by
      calc
        _ = ∑ S ∈ M.powerset, ((S.card : ℝ) + 1) := by
          apply Finset.sum_congr rfl
          intro S hS
          have has : a ∉ S := fun h => ha ((Finset.mem_powerset.mp hS) h)
          simp [Finset.card_insert_of_notMem has]
        _ = _ := by simp [Finset.sum_add_distrib]
    rw [hs, Finset.card_insert_of_notMem ha, Nat.cast_add, Nat.cast_one, pow_succ]
    nlinarith

variable [Fintype V]

/-- A uniform subset of M has expected cardinality |M|/2. -/
theorem uniform_powerset_mean_card (M : Finset V) :
    (FiniteLaw.uniform M.powerset ⟨∅, by simp⟩).mean
      (fun S => (S.card : ℝ)) = (M.card : ℝ) / 2 := by
  classical
  have htwo : (2 : ℝ) ^ M.card ≠ 0 := by positivity
  have hsum := twice_sum_card_powerset M
  have heq :
      (FiniteLaw.uniform M.powerset ⟨∅, by simp⟩).mean
        (fun S => (S.card : ℝ)) =
        (∑ S ∈ M.powerset, (S.card : ℝ)) / (2 : ℝ)^M.card := by
    simp only [FiniteLaw.mean, FiniteLaw.uniform]
    simp only [ite_mul, zero_mul, Finset.sum_ite_mem, one_div]
    simp only [← Finset.mul_sum, Finset.card_powerset, Nat.cast_pow,
      Nat.cast_ofNat, Finset.univ_inter]
    ring
  rw [heq]
  apply (div_eq_iff htwo).mpr
  nlinarith

/-- The only subset with no selected leaves is the empty set. -/
theorem uniform_powerset_prob_empty (M : Finset V) :
    (FiniteLaw.uniform M.powerset ⟨∅, by simp⟩).prob ∅ =
      1 / (2 : ℝ) ^ M.card := by
  simp [FiniteLaw.uniform]

end TP3
