module

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic
public import Mathlib.Analysis.Convex.Jensen

@[expose] public section

namespace TP3

open scoped BigOperators

/-- A probability distribution on a finite type, with real-valued masses. -/
structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  prob : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ prob ω
  total : ∑ ω, prob ω = 1

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω]

def mean (μ : FiniteLaw Ω) (X : Ω → ℝ) : ℝ := ∑ ω, μ.prob ω * X ω

theorem mean_mono (μ : FiniteLaw Ω) {X Y : Ω → ℝ} (h : ∀ ω, X ω ≤ Y ω) :
    μ.mean X ≤ μ.mean Y := by
  exact Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (μ.nonneg ω)

theorem mean_nonneg (μ : FiniteLaw Ω) {X : Ω → ℝ} (h : ∀ ω, 0 ≤ X ω) :
    0 ≤ μ.mean X := Finset.sum_nonneg fun ω _ => mul_nonneg (μ.nonneg ω) (h ω)

theorem mean_add (μ : FiniteLaw Ω) (X Y : Ω → ℝ) :
    μ.mean (fun ω => X ω + Y ω) = μ.mean X + μ.mean Y := by
  simp [mean, mul_add, Finset.sum_add_distrib]

theorem mean_mul_const (μ : FiniteLaw Ω) (a : ℝ) (X : Ω → ℝ) :
    μ.mean (fun ω => a * X ω) = a * μ.mean X := by
  simp [mean, Finset.mul_sum, mul_left_comm]

theorem mean_sum {κ : Type*} (μ : FiniteLaw Ω) (A : Finset κ) (X : κ → Ω → ℝ) :
    μ.mean (fun ω => ∑ x ∈ A, X x ω) = ∑ x ∈ A, μ.mean (X x) := by
  simp only [mean, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Probability of any event in a finite law. -/
noncomputable def event (μ : FiniteLaw Ω) (P : Ω → Prop) : ℝ := by
  classical
  exact ∑ ω ∈ Finset.univ.filter P, μ.prob ω

theorem event_mono (μ : FiniteLaw Ω) {P Q : Ω → Prop} (h : ∀ ω, P ω → Q ω) :
    μ.event P ≤ μ.event Q := by
  classical
  apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun ω _ _ => μ.nonneg ω)
  intro ω hω
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ ω, h ω (Finset.mem_filter.mp hω).2⟩

theorem mean_indicator (μ : FiniteLaw Ω) (P : Ω → Prop) [DecidablePred P] :
    μ.mean (fun ω => if P ω then 1 else 0) = μ.event P := by
  classical
  simp only [mean, event, Finset.sum_filter, mul_ite, mul_one, mul_zero]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : P ω <;> simp [h]

theorem mean_const (μ : FiniteLaw Ω) (a : ℝ) : μ.mean (fun _ => a) = a := by
  rw [mean, ← Finset.sum_mul, μ.total, one_mul]

theorem sq_mean_le_mean_sq (μ : FiniteLaw Ω) (X : Ω → ℝ) :
    μ.mean X ^ 2 ≤ μ.mean (fun ω => X ω ^ 2) := by
  let m := μ.mean X
  have h := μ.mean_nonneg (X := fun ω => (X ω - m) ^ 2) (fun ω => sq_nonneg _)
  have hid : (fun ω => (X ω - m) ^ 2) =
      fun ω => (X ω ^ 2 + (-2 * m) * X ω) + m ^ 2 := by
    funext ω
    ring
  rw [hid, μ.mean_add, μ.mean_add, μ.mean_mul_const, μ.mean_const] at h
  change m ^ 2 ≤ _
  nlinarith only [h]

/-- Markov's inequality for the mass of a threshold event. -/
theorem prob_ge_le (μ : FiniteLaw Ω) {X : Ω → ℝ} (hX : ∀ ω, 0 ≤ X ω)
    {a : ℝ} (ha : 0 < a) :
    (∑ ω ∈ Finset.univ.filter (fun ω => a ≤ X ω), μ.prob ω) ≤ μ.mean X / a := by
  classical
  rw [le_div_iff₀ ha, Finset.sum_mul]
  calc
    _ ≤ ∑ ω ∈ Finset.univ.filter (fun ω => a ≤ X ω), μ.prob ω * X ω :=
      Finset.sum_le_sum fun ω hω =>
        mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hω).2 (μ.nonneg ω)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun ω _ _ => mul_nonneg (μ.nonneg ω) (hX ω)

/-- Taking an exponential moment of a variable valued in `[0,1]`. -/
theorem mean_exp_le (μ : FiniteLaw Ω) (X : Ω → ℝ)
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) (t : ℝ) :
    μ.mean (fun ω => Real.exp (t * X ω)) ≤
      Real.exp ((Real.exp t - 1) * μ.mean X) := by
  have hchord (ω : Ω) : Real.exp (t * X ω) ≤
      1 + (Real.exp t - 1) * X ω := by
    have hx : 0 ≤ X ω ∧ X ω ≤ 1 := hX ω
    have hweights : 1 - X ω + X ω = 1 := sub_add_cancel _ _
    have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ t)
      (sub_nonneg.mpr hx.2) hx.1 hweights
    simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
    rw [mul_comm t]
    linarith
  calc
    _ ≤ μ.mean (fun ω => 1 + (Real.exp t - 1) * X ω) := μ.mean_mono hchord
    _ = ((Real.exp t - 1) * μ.mean X) + 1 := by
      rw [μ.mean_add, μ.mean_const, μ.mean_mul_const, add_comm]
    _ ≤ _ := Real.add_one_le_exp _

theorem event_ge_le (μ : FiniteLaw Ω) {X : Ω → ℝ} (hX : ∀ ω, 0 ≤ X ω)
    {a : ℝ} (ha : 0 < a) : μ.event (fun ω => a ≤ X ω) ≤ μ.mean X / a := by
  classical
  exact μ.prob_ge_le hX ha

/-- The union bound, with no independence restriction on the events. -/
theorem event_exists_le_sum {κ : Type*} [Fintype κ]
    (μ : FiniteLaw Ω) (P : κ → Ω → Prop) :
    μ.event (fun ω => ∃ k, P k ω) ≤ ∑ k, μ.event (P k) := by
  classical
  simp_rw [← μ.mean_indicator]
  rw [← μ.mean_sum]
  apply μ.mean_mono
  intro ω
  by_cases hex : ∃ k, P k ω
  · obtain ⟨k, hk⟩ := hex
    rw [ite_eq_left ⟨k, hk⟩]
    have h := Finset.single_le_sum (s := Finset.univ)
      (f := fun j => if P j ω then (1 : ℝ) else 0)
      (fun j _ => by split <;> positivity) (Finset.mem_univ k)
    simpa [hk] using h
  · rw [ite_eq_right hex]
    exact Finset.sum_nonneg fun k _ => by split <;> positivity

/-- The joint experiment of drawing a first observation and then choosing a
law for the remaining observation using the first. -/
def staged {Ω' : Type*} [Fintype Ω'] (μ : FiniteLaw Ω) (ν : Ω → FiniteLaw Ω') :
    FiniteLaw (Ω × Ω') where
  prob s := μ.prob s.1 * (ν s.1).prob s.2
  nonneg s := mul_nonneg (μ.nonneg s.1) ((ν s.1).nonneg s.2)
  total := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, fun ω => (ν ω).total, mul_one, μ.total]

theorem staged_mean {Ω' : Type*} [Fintype Ω'] (μ : FiniteLaw Ω)
    (ν : Ω → FiniteLaw Ω') (X : Ω × Ω' → ℝ) :
    (μ.staged ν).mean X = μ.mean (fun ω => (ν ω).mean (fun ω' => X (ω, ω'))) := by
  simp only [mean, staged, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

/-- Conditioning on an exposed value of positive probability gives exactly
the indicated remaining law. In particular, drawing the remaining groups
from a product law independent of this observation preserves that law. -/
theorem staged_conditional_mass {Ω' : Type*} [Fintype Ω']
    (μ : FiniteLaw Ω) (ν : Ω → FiniteLaw Ω') (ω : Ω) (hω : 0 < μ.prob ω)
    (ω' : Ω') :
    (μ.staged ν).prob (ω, ω') / (μ.staged ν).event (fun s => s.1 = ω) =
      (ν ω).prob ω' := by
  classical
  have hfirst : (μ.staged ν).event (fun s => s.1 = ω) = μ.prob ω := by
    rw [← mean_indicator, staged_mean]
    have hmean (a : Ω) :
        (ν a).mean (fun _ => if a = ω then (1 : ℝ) else 0) = if a = ω then 1 else 0 :=
      (ν a).mean_const _
    simp_rw [hmean]
    simp [mean, mul_ite, Finset.sum_ite_eq']
  rw [hfirst]
  change (μ.prob ω * (ν ω).prob ω') / μ.prob ω = _
  field_simp

theorem event_nonneg (μ : FiniteLaw Ω) (P : Ω → Prop) : 0 ≤ μ.event P := by
  classical
  exact Finset.sum_nonneg fun ω _ => μ.nonneg ω

theorem event_not (μ : FiniteLaw Ω) (P : Ω → Prop) :
    μ.event (fun ω => ¬ P ω) = 1 - μ.event P := by
  classical
  rw [← mean_indicator, ← mean_indicator, eq_sub_iff_add_eq, ← mean_add]
  have hone : (fun ω => (if ¬ P ω then (1 : ℝ) else 0) + (if P ω then 1 else 0)) =
      fun _ => 1 := by
    funext ω
    by_cases h : P ω <;> simp [h]
  rw [hone, mean_const]

/-- Express the probability in a two-stage experiment as the first-stage
average of the conditional probabilities. -/
theorem staged_event {Ω' : Type*} [Fintype Ω']
    (μ : FiniteLaw Ω) (ν : Ω → FiniteLaw Ω') (P : Ω × Ω' → Prop) :
    (μ.staged ν).event P = μ.mean (fun ω => (ν ω).event (fun ω' => P (ω, ω'))) := by
  classical
  rw [← mean_indicator, staged_mean]
  simp_rw [mean_indicator]

theorem event_lt_one_exists_not (μ : FiniteLaw Ω) {P : Ω → Prop}
    (h : μ.event P < 1) : ∃ ω, ¬ P ω := by
  classical
  by_contra! he
  unfold event at h
  simp [he, μ.total] at h


end FiniteLaw

end TP3
