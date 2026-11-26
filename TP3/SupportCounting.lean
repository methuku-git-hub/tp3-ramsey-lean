module

public import TP3.FiniteCardinality

@[expose] public section

namespace TP3.FiniteLaw

attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {Ω V ι α : Type*} [Fintype Ω] [DecidableEq V] [DecidableEq α]

/-- A union of small sets, indexed by configurations whose supports must
be selected. This is the expectation form of the usual deletion count. -/
theorem mean_activated_union (μ : FiniteLaw Ω) (C : Ω → Finset V)
    (I : Finset ι) (S : ι → Finset V) (F : ι → Finset α)
    (q : ℝ) (k r : ℕ)
    (hcoarse : ∀ A, μ.event (fun ω => A ⊆ C ω) ≤ q^A.card)
    (hcard : ∀ i ∈ I, (S i).card=r)
    (hsize : ∀ i ∈ I, (F i).card ≤ k) :
    μ.mean (fun ω => (((I.filter (fun i => S i ⊆ C ω)).biUnion F).card : ℝ)) ≤
      k * (I.card : ℝ) * q^r := by
  classical
  have hpoint (ω : Ω) :
      (((I.filter (fun i => S i ⊆ C ω)).biUnion F).card : ℝ) ≤
        ∑ i ∈ I, (k : ℝ) * (if S i ⊆ C ω then 1 else 0) := by
    calc
      _ ≤ ((I.filter (fun i => S i ⊆ C ω)).card : ℝ)*k := by
        exact_mod_cast card_biUnion_le_mul _ F k
          (fun i hi => hsize i (Finset.mem_filter.mp hi).1)
      _ = _ := by
        simp only [mul_ite,mul_one,mul_zero,← Finset.sum_filter]
        simp
  calc
    _ ≤ μ.mean (fun ω => ∑ i ∈ I, (k : ℝ) * (if S i ⊆ C ω then 1 else 0)) :=
      μ.mean_mono hpoint
    _ = ∑ i ∈ I, (k : ℝ) * μ.event (fun ω => S i ⊆ C ω) := by
      rw [μ.mean_sum]
      simp_rw [μ.mean_mul_const,μ.mean_indicator]
    _ ≤ ∑ _i ∈ I, (k : ℝ)*q^r := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      simpa only [hcard i hi] using hcoarse (S i)
    _ = _ := by simp; ring

end TP3.FiniteLaw
