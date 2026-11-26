module

public import TP3.AwayCongruence
public import TP3.FeasibleInsertion
public import TP3.RestrictionWeights

@[expose] public section

namespace TP3

attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem away_uniform_mean_congr (H : Finset (Finset V)) (hH : IsTripleSystem H) (v : V)
    (ω ω' : RestrictionData V) (f : Finset V → ℝ)
    (hvertices : ∀ x, x ≠ v → ω.1 x=ω'.1 x)
    (hpairs : ∀ e, v ∉ e → ω.2 e=ω'.2 e) :
    (FiniteLaw.uniform (awayFamily H ω v) (awayFamily_nonempty hH ω v)).mean f =
      (FiniteLaw.uniform (awayFamily H ω' v) (awayFamily_nonempty hH ω' v)).mean f := by
  rw [FiniteLaw.uniform_mean,FiniteLaw.uniform_mean,awayFamily_congr H v ω ω' hvertices hpairs]

theorem uniform_removed_eq_of_absent (H : Finset (Finset V)) (hH : IsTripleSystem H)
    (ω : RestrictionData V) (v : V) (hv : ω.1 v=false) (f : Finset V → ℝ) :
    (FiniteLaw.uniform (feasibleFamily H ω) (feasibleFamily_nonempty hH ω)).mean (fun S => f (S.erase v)) =
      (FiniteLaw.uniform (awayFamily H ω v) (awayFamily_nonempty hH ω v)).mean f := by
  rw [FiniteLaw.uniform_mean,FiniteLaw.uniform_mean,awayFamily_eq_of_absent H ω v hv]
  congr 1
  apply Finset.sum_congr rfl
  intro S hS
  have hvS : v ∉ S := by
    intro hvS
    have ht := (Finset.mem_filter.mp hS).2.2.1 v hvS
    rw [hv] at ht
    contradiction
  rw [Finset.erase_eq_of_notMem hvS]

/-- Removing v is realised by conditioning the original vertex mask
on the independent event that v was not sampled. The original pair
probabilities are retained throughout. -/
theorem away_remove_bound (H : Finset (Finset V)) (hH : IsTripleSystem H)
    (c : Finset V → ℝ) (hc : ∀ e, 0 ≤ c e)
    (p δ : ℝ) (hp : 0 ≤ p) (hp1 : p < 1) (hδ : 0 ≤ δ)
    (v : V) (f : Finset V → ℝ) (hf : ∀ S, 0 ≤ f S) :
    (awayLaw H hH c hc p δ hp hp1.le hδ v).mean f ≤
      (restrictedLaw H hH c hc p δ hp hp1.le hδ).mean (fun S => f (S.erase v))/(1-p) := by
  let μ := restrictionDataLaw c hc p δ hp hp1.le hδ
  let F := fun ω : RestrictionData V =>
    (FiniteLaw.uniform (awayFamily H ω v) (awayFamily_nonempty hH ω v)).mean f
  have hfactor : μ.mean (fun ω => F ω*(if ω.1 v=false then 1 else 0))=(1-p)*μ.mean F := by
    apply restriction_vertex_factor
    intro σ σ' π hh
    exact away_uniform_mean_congr H hH v (σ,π) (σ',π) f hh (fun _ _ => rfl)
  have hpoint (ω : RestrictionData V) : F ω*(if ω.1 v=false then 1 else 0) ≤
      (FiniteLaw.uniform (feasibleFamily H ω) (feasibleFamily_nonempty hH ω)).mean
        (fun S => f (S.erase v)) := by
    by_cases hv : ω.1 v=false
    · rw [if_pos hv,mul_one,uniform_removed_eq_of_absent H hH ω v hv f]
    · rw [if_neg hv,mul_zero]
      exact FiniteLaw.mean_nonneg _ (fun S => hf (S.erase v))
  apply (le_div_iff₀ (sub_pos.mpr hp1)).mpr
  change (μ.bind _).mean f*(1-p) ≤ (μ.bind _).mean _
  rw [FiniteLaw.bind_mean,FiniteLaw.bind_mean]
  calc
    _ = μ.mean (fun ω => F ω*(if ω.1 v=false then 1 else 0)) := by rw [hfactor]; ring
    _ ≤ _ := μ.mean_mono hpoint

end TP3
