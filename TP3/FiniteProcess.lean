module

public import TP3.Conditioning

@[expose] public section

namespace TP3

open scoped BigOperators

attribute [local instance] Classical.propDecidable

universe u

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω]

/-- A deterministic finite probability law. -/
noncomputable def point (x : Ω) : FiniteLaw Ω := by
  classical
  exact {
    prob := fun y => if y=x then 1 else 0
    nonneg := fun y => by split <;> norm_num
    total := by simp }

theorem event_le_one (μ : FiniteLaw Ω) (P : Ω → Prop) : μ.event P ≤ 1 := by
  classical
  rw [← μ.mean_indicator]
  calc
    _ ≤ μ.mean (fun _ => 1) := μ.mean_mono (fun _ => by split <;> norm_num)
    _ = 1 := μ.mean_const 1

end FiniteLaw

/-- A finite history retains every earlier trial. Using nested pairs
makes each next step an explicit independent extension of that history. -/
@[reducible] def History (Ω : Type u) : ℕ → Type u
  | 0 => PUnit
  | n+1 => History Ω n × Ω

@[reducible] instance historyFintype (Ω : Type*) [Fintype Ω] (n : ℕ) : Fintype (History Ω n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Fintype (History Ω n × Ω))

/-- Each new class receives fresh noise, independent of the full past. -/
noncomputable def historyLaw {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) :
    (n : ℕ) → FiniteLaw (History Ω n)
  | 0 => FiniteLaw.point PUnit.unit
  | n+1 => (historyLaw μ n).staged (fun _ => μ)

/-- Evaluate a deterministic algorithm along a complete finite history.
The update may depend on every previous choice through its state. -/
def processState {Ω S : Type*} (initial : S) (step : ℕ → S → Ω → S) :
    (n : ℕ) → History Ω n → S
  | 0, _ => initial
  | n+1, h => step n (processState initial step n h.1) h.2

/-- The induction for the no-shared-mark event. The hypotheses give an
upper bound for every fixed earlier history, not conditioning on future
choices. Thus multiplying the bounds is justified despite adaptivity. -/
theorem history_event_bound {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)
    (E : (n : ℕ) → History Ω n → Prop) (a : ℕ → ℝ)
    (ha : ∀ i, 0 ≤ a i)
    (hstep : ∀ i h, μ.event (fun ω => E (i+1) (h,ω)) ≤
      if E i h then a i else 0) (n : ℕ) :
    (historyLaw μ n).event (E n) ≤ ∏ i ∈ Finset.range n, a i := by
  classical
  induction n with
  | zero =>
    simpa using (historyLaw μ 0).event_le_one (E 0)
  | succ n ih =>
    change ((historyLaw μ n).staged (fun _ => μ)).event _ ≤ _
    rw [FiniteLaw.staged_event]
    calc
      _ ≤ (historyLaw μ n).mean (fun h => if E n h then a n else 0) :=
        FiniteLaw.mean_mono _ (hstep n)
      _ = a n * (historyLaw μ n).event (E n) := by
        rw [← FiniteLaw.mean_indicator]
        have heq : (fun h : History Ω n => if E n h then a n else 0) =
            fun h => a n * (if E n h then 1 else 0) := by
          funext h
          split <;> simp
        rw [heq, FiniteLaw.mean_mul_const]
      _ ≤ a n * ∏ i ∈ Finset.range n, a i := mul_le_mul_of_nonneg_left ih (ha n)
      _ = _ := by rw [Finset.prod_range_succ, mul_comm]

end TP3
