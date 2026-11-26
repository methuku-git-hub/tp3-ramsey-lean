module

public import TP3.FiniteSampling

@[expose] public section

namespace TP3.FiniteLaw

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

@[simp] theorem event_true (μ : FiniteLaw Ω) : μ.event (fun _ => True) = 1 := by
  rw [← μ.mean_indicator]
  simpa using μ.mean_const 1

@[simp] theorem event_false (μ : FiniteLaw Ω) : μ.event (fun _ => False) = 0 := by
  simp [event]

theorem event_const (μ : FiniteLaw Ω) (P : Prop) [Decidable P] :
    μ.event (fun _ => P) = if P then 1 else 0 := by
  by_cases h : P <;> simp [h]

theorem staged_event_first {Ω' : Type*} [Fintype Ω']
    (μ : FiniteLaw Ω) (ν : Ω → FiniteLaw Ω') (P : Ω → Prop) :
    (μ.staged ν).event (fun ω => P ω.1) = μ.event P := by
  classical
  rw [staged_event]
  simp_rw [event_const]
  exact μ.mean_indicator P

theorem staged_event_second {Ω' : Type*} [Fintype Ω']
    (μ : FiniteLaw Ω) (ν : FiniteLaw Ω') (P : Ω' → Prop) :
    (μ.staged (fun _ => ν)).event (fun ω => P ω.2) = ν.event P := by
  rw [staged_event]
  convert μ.mean_const (ν.event P) using 1

/-- Restrict a finite probability law to an event of positive probability,
and divide by the probability of that event. -/
noncomputable def condition (μ : FiniteLaw Ω) (P : Ω → Prop)
    (hP : 0 < μ.event P) : FiniteLaw Ω := by
  classical
  exact {
    prob := fun ω => if P ω then μ.prob ω / μ.event P else 0
    nonneg := fun ω => by
      split
      · exact div_nonneg (μ.nonneg ω) hP.le
      · exact le_rfl
    total := by
      rw [← Finset.sum_filter, ← Finset.sum_div]
      change μ.event P / μ.event P = 1
      exact div_self (ne_of_gt hP) }

/-- The probability of an event under a uniform choice is the fraction of
the original family satisfying it. -/
theorem uniform_event [DecidableEq Ω] (F : Finset Ω) (hF : F.Nonempty)
    (P : Ω → Prop) [DecidablePred P] :
    (uniform F hF).event P = ((F.filter P).card : ℝ) / F.card := by
  classical
  simp [event, uniform, div_eq_mul_inv]
  left
  congr 1
  ext ω
  simp [and_comm]

/-- Every nonempty fibre of an observation has positive probability under
a uniform choice from the original family. -/
theorem uniform_event_pos [DecidableEq Ω] (F : Finset Ω) (hF : F.Nonempty)
    (P : Ω → Prop) [DecidablePred P] (hFP : (F.filter P).Nonempty) :
    0 < (uniform F hF).event P := by
  rw [uniform_event]
  exact div_pos (by exact_mod_cast hFP.card_pos) (by exact_mod_cast hF.card_pos)

/-- Conditioning a uniform choice on any observation leaves a uniform
choice on the sets consistent with that observation. This is equality of
the probability of each outcome, with the normalizing factors explicit. -/
theorem uniform_condition_prob [DecidableEq Ω] (F : Finset Ω) (hF : F.Nonempty)
    (P : Ω → Prop) [DecidablePred P] (hFP : (F.filter P).Nonempty) (ω : Ω) :
    ((uniform F hF).condition P (uniform_event_pos F hF P hFP)).prob ω =
      (uniform (F.filter P) hFP).prob ω := by
  classical
  have hcard : (F.card : ℝ) ≠ 0 := by exact_mod_cast hF.card_ne_zero
  have hfcard : ((F.filter P).card : ℝ) ≠ 0 := by exact_mod_cast hFP.card_ne_zero
  simp only [condition]
  rw [uniform_event]
  simp only [uniform, Finset.mem_filter]
  by_cases hP : P ω <;> by_cases hω : ω ∈ F <;> simp [hP,hω]
  field_simp

/-- Expected values under a uniform law are ordinary finite averages. -/
theorem uniform_mean [DecidableEq Ω] (F : Finset Ω) (hF : F.Nonempty)
    (X : Ω → ℝ) :
    (uniform F hF).mean X = (∑ ω ∈ F, X ω) / F.card := by
  classical
  simp only [mean, uniform, ite_mul, zero_mul, Finset.sum_ite_mem,
    Finset.univ_inter, one_div, ← Finset.mul_sum]
  ring

/-- An injective relabelling preserves the uniform distribution on a
finite family. The conclusion is stated for arbitrary expected values. -/
theorem uniform_image_mean [DecidableEq Ω] {Ω' : Type*} [Fintype Ω']
    [DecidableEq Ω'] (F : Finset Ω) (hF : F.Nonempty) (f : Ω → Ω')
    (hf : Set.InjOn f F) (X : Ω' → ℝ) :
    (uniform (F.image f) (hF.image f)).mean X =
      (uniform F hF).mean (fun ω => X (f ω)) := by
  rw [uniform_mean, uniform_mean, Finset.card_image_of_injOn hf]
  congr 1
  exact Finset.sum_image hf

/-- The elementary conditional-mean formula used for all exposures. -/
theorem condition_mean (μ : FiniteLaw Ω) (P : Ω → Prop)
    [DecidablePred P] (hP : 0 < μ.event P) (X : Ω → ℝ) :
    (μ.condition P hP).mean X =
      μ.mean (fun ω => if P ω then X ω else 0) / μ.event P := by
  classical
  simp only [mean, condition, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : P ω <;> simp [h, div_mul_eq_mul_div]

/-- Nonnegative conditional expectations are bounded by the full
expectation divided by the probability of the conditioning event. -/
theorem condition_mean_le (μ : FiniteLaw Ω) (P : Ω → Prop)
    [DecidablePred P] (hP : 0 < μ.event P) (X : Ω → ℝ) (hX : ∀ ω, 0 ≤ X ω) :
    (μ.condition P hP).mean X ≤ μ.mean X / μ.event P := by
  rw [condition_mean]
  apply div_le_div_of_nonneg_right _ hP.le
  apply μ.mean_mono
  intro ω
  split <;> simp_all

/-- For independent stages, the probability of an event in each stage
is the product of their probabilities. -/
theorem independent_events {Ω' : Type*} [Fintype Ω']
    (μ : FiniteLaw Ω) (ν : FiniteLaw Ω') (P : Ω → Prop) (Q : Ω' → Prop) :
    (μ.staged (fun _ => ν)).event (fun ω => P ω.1 ∧ Q ω.2) =
      μ.event P * ν.event Q := by
  classical
  rw [← mean_indicator, staged_mean]
  have hi (ω : Ω) :
      ν.mean (fun y => if P ω ∧ Q y then (1 : ℝ) else 0) =
        (if P ω then (1 : ℝ) else 0) * ν.event Q := by
    by_cases h : P ω
    · simp only [h, true_and, ite_true, one_mul]
      exact ν.mean_indicator Q
    · simp only [h, false_and, ite_false, zero_mul]
      exact ν.mean_const 0
  simp_rw [hi]
  have heq : (fun ω => (if P ω then (1 : ℝ) else 0) * ν.event Q) =
      fun ω => ν.event Q * (if P ω then 1 else 0) := by
    funext ω
    ring
  rw [heq, mean_mul_const, mean_indicator, mul_comm]

end TP3.FiniteLaw
