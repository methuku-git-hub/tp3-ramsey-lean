module

public import TP3.ClassMarks

@[expose] public section

namespace TP3

attribute [local instance] Classical.propDecidable

namespace FiniteLaw

/-- Multiply a uniform conditional upper bound by the probability of an
event determined by the past. Future information is never conditioned on. -/
theorem staged_event_bound_past {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω']
    (μ : FiniteLaw Ω) (ν : Ω → FiniteLaw Ω') (P : Ω → Prop)
    (Q : Ω → Ω' → Prop) (a : ℝ)
    (hQ : ∀ ξ, (ν ξ).event (Q ξ) ≤ a) :
    (μ.staged ν).event (fun ξ => P ξ.1 ∧ Q ξ.1 ξ.2) ≤ a*μ.event P := by
  rw [staged_event]
  calc
    _ ≤ μ.mean (fun ξ => a*(if P ξ then 1 else 0)) := by
      apply μ.mean_mono
      intro ξ
      by_cases hp : P ξ
      · simpa only [hp,true_and,ite_true,mul_one] using hQ ξ
      · simp only [hp,false_and,ite_false,mul_zero,event_false]
        rfl
    _ = _ := by rw [μ.mean_mul_const,μ.mean_indicator]

end FiniteLaw

namespace DependentSample.Data

variable {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
variable (d : Data V U)

theorem run_marked_succ (n : ℕ)
    (ξ : History (ClassNoise V U d.maxListSize) n)
    (ω : ClassNoise V U d.maxListSize) (M : U) :
    M ∈ (d.run (n+1) (ξ,ω)).marked ↔ M ∈ (d.run n ξ).marked ∨ ω.1 M=true := by
  change M ∈ (d.run n ξ).marked ∪ Finset.univ.filter _ ↔ _
  simp

theorem marked_probability (M : U) (n : ℕ)
    (q τ : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    (historyLaw (finiteClassLaw d.maxListSize q τ hq hq1 hτ hτ1) n).event
      (fun ξ => M ∈ (d.run n ξ).marked) ≤ n*τ := by
  induction n with
  | zero => simp [run,processState,initial]
  | succ n ih =>
    let μ := historyLaw (finiteClassLaw (V := V) (U := U) d.maxListSize q τ hq hq1 hτ hτ1) n
    let ν := finiteClassLaw (V := V) (U := U) d.maxListSize q τ hq hq1 hτ hτ1
    have heq : (fun ξ : History (ClassNoise V U d.maxListSize) (n+1) =>
        M ∈ (d.run (n+1) ξ).marked) =
        fun ξ => M ∈ (d.run n ξ.1).marked ∨ ξ.2.1 M=true := by
      funext ξ
      exact propext (d.run_marked_succ n ξ.1 ξ.2 M)
    rw [heq]
    change (μ.staged (fun _ => ν)).event _ ≤ _
    calc
      _ ≤ (μ.staged (fun _ => ν)).event (fun ξ => M ∈ (d.run n ξ.1).marked) +
        (μ.staged (fun _ => ν)).event (fun ξ => ξ.2.1 M=true) :=
          FiniteLaw.event_or_le _ _ _
      _ = μ.event (fun ξ => M ∈ (d.run n ξ).marked) + τ := by
        rw [FiniteLaw.staged_event_first _ _
          (fun ξ : History (ClassNoise V U d.maxListSize) n => M ∈ (d.run n ξ).marked),
          FiniteLaw.staged_event_second _ _ (fun ω : ClassNoise V U d.maxListSize => ω.1 M=true),
          finiteClass_mark_probability]
      _ ≤ n*τ + τ := add_le_add ih le_rfl
      _ = _ := by push_cast; ring

theorem tentative_past_event (i : ℕ) (x : V) (hx : x ∈ d.classVertices i)
    (P : History (ClassNoise V U d.maxListSize) i → Prop)
    (q τ : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    (historyLaw (finiteClassLaw d.maxListSize q τ hq hq1 hτ hτ1) (i+1)).event
      (fun ξ => P ξ.1 ∧ x ∈ d.tentative i (d.run i ξ.1).chosen ξ.2) ≤
      (q*τ^d.maxListSize) *
        (historyLaw (finiteClassLaw d.maxListSize q τ hq hq1 hτ hτ1) i).event P := by
  change ((historyLaw _ i).staged (fun _ => _)).event _ ≤ _
  apply FiniteLaw.staged_event_bound_past _ _ P
    (fun (ξ : History (ClassNoise V U d.maxListSize) i) (ω : ClassNoise V U d.maxListSize) =>
      x ∈ d.tentative i (d.run i ξ).chosen ω)
  intro ξ
  rw [d.tentative_vertex_conditional i _ x hx q τ hq hq1 hτ hτ1]
  split <;> (first | rfl | positivity)

end DependentSample.Data
end TP3
