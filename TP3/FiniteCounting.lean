module

public import TP3.FiniteProcess

@[expose] public section

namespace TP3

open scoped BigOperators

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω]

theorem event_or_le (μ : FiniteLaw Ω) (P Q : Ω → Prop) :
    μ.event (fun ω => P ω ∨ Q ω) ≤ μ.event P + μ.event Q := by
  classical
  simp_rw [← μ.mean_indicator]
  rw [← μ.mean_add]
  apply μ.mean_mono
  intro ω
  by_cases hp : P ω <;> by_cases hq : Q ω <;> simp [hp,hq]

theorem event_exists_finset_le_sum {ι : Type*} (μ : FiniteLaw Ω)
    (I : Finset ι) (P : ι → Ω → Prop) :
    μ.event (fun ω => ∃ i ∈ I, P i ω) ≤ ∑ i ∈ I, μ.event (P i) := by
  classical
  simp_rw [← μ.mean_indicator]
  rw [← μ.mean_sum]
  apply μ.mean_mono
  intro ω
  by_cases hex : ∃ i ∈ I, P i ω
  · obtain ⟨i,hi,hp⟩ := hex
    rw [ite_eq_left ⟨i,hi,hp⟩]
    have hh := Finset.single_le_sum (s := I)
      (f := fun j => if P j ω then (1:ℝ) else 0)
      (fun j _ => by split <;> positivity) hi
    simpa [hp] using hh
  · rw [ite_eq_right hex]
    exact Finset.sum_nonneg (fun _ _ => by split <;> positivity)

/-- The union bound for configurations requiring a fixed number of
distinct selected vertices. All correlations in C are allowed; the only
probability input is its previously proved coarse inclusion bound. -/
theorem exists_support_probability {V ι : Type*} [DecidableEq V]
    (μ : FiniteLaw Ω) (C : Ω → Finset V) (I : Finset ι) (S : ι → Finset V)
    (q : ℝ) (r : ℕ)
    (hcoarse : ∀ A, μ.event (fun ω => A ⊆ C ω) ≤ q^A.card)
    (hcard : ∀ i ∈ I, (S i).card=r) :
    μ.event (fun ω => ∃ i ∈ I, S i ⊆ C ω) ≤ (I.card : ℝ)*q^r := by
  calc
    _ ≤ ∑ i ∈ I, μ.event (fun ω => S i ⊆ C ω) := μ.event_exists_finset_le_sum I _
    _ ≤ ∑ _i ∈ I, q^r := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [hcard i hi] using hcoarse (S i)
    _ = _ := by simp

end FiniteLaw

theorem card_biUnion_le_mul {ι α : Type*} [DecidableEq α]
    (I : Finset ι) (F : ι → Finset α) (r : ℕ)
    (hr : ∀ i ∈ I, (F i).card ≤ r) : (I.biUnion F).card ≤ I.card*r := by
  calc
    _ ≤ ∑ i ∈ I, (F i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ I, r := Finset.sum_le_sum hr
    _ = _ := by simp

theorem card_biUnion_le_mul_real {ι α : Type*} [DecidableEq α]
    (I : Finset ι) (F : ι → Finset α) (r : ℝ)
    (hr : ∀ i ∈ I, ((F i).card : ℝ) ≤ r) :
    ((I.biUnion F).card : ℝ) ≤ (I.card : ℝ)*r := by
  calc
    _ ≤ ∑ i ∈ I, ((F i).card : ℝ) := by exact_mod_cast (Finset.card_biUnion_le (s:=I) (t:=F))
    _ ≤ ∑ _i ∈ I, r := Finset.sum_le_sum hr
    _ = _ := by simp

end TP3
