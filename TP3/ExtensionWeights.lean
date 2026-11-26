module

public import TP3.AwayRemoval
public import TP3.FiniteMeanAlgebra

@[expose] public section

namespace TP3

attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem away_uniform_prob_congr (H : Finset (Finset V)) (hH : IsTripleSystem H) (v : V)
    (ω ω' : RestrictionData V) (S : Finset V)
    (hvertices : ∀ x, x ≠ v → ω.1 x=ω'.1 x)
    (hpairs : ∀ e, v ∉ e → ω.2 e=ω'.2 e) :
    (FiniteLaw.uniform (awayFamily H ω v) (awayFamily_nonempty hH ω v)).prob S =
      (FiniteLaw.uniform (awayFamily H ω' v) (awayFamily_nonempty hH ω' v)).prob S := by
  simp only [FiniteLaw.uniform,awayFamily_congr H v ω ω' hvertices hpairs]
  congr 1

/-- The still-unrevealed vertex and incident-pair decisions contribute
exactly p exp(-δ w_v(S)), even after weighting S by its uniform
probability in the random family omitting v. -/
theorem extension_weight (H : Finset (Finset V)) (hH : IsTripleSystem H)
    (p δ : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hδ : 0 ≤ δ) (v : V) (S : Finset V) :
    (restrictionDataLaw (codegreeCost H) (codegreeCost_nonneg H) p δ hp hp1 hδ).mean
      (fun ω => (FiniteLaw.uniform (awayFamily H ω v) (awayFamily_nonempty hH ω v)).prob S *
        (if ω.1 v=true then 1 else 0) * (if ∀ x ∈ S, ω.2 {v,x}=true then 1 else 0)) =
      p*Real.exp (-δ*incidentCost H v S)*
        (awayLaw H hH (codegreeCost H) (codegreeCost_nonneg H) p δ hp hp1 hδ v).prob S := by
  let μ := restrictionDataLaw (codegreeCost H) (codegreeCost_nonneg H) p δ hp hp1 hδ
  let F := fun ω : RestrictionData V =>
    (FiniteLaw.uniform (awayFamily H ω v) (awayFamily_nonempty hH ω v)).prob S
  have hpairs := restriction_incident_pair_factor (codegreeCost H) (codegreeCost_nonneg H)
    p δ hp hp1 hδ v S (fun ω => F ω*(if ω.1 v=true then 1 else 0))
    (by
      intro σ π π' hh
      congr 1
      exact away_uniform_prob_congr H hH v (σ,π) (σ,π') S (fun _ _ => rfl) hh)
  have hvertex := restriction_vertex_factor (codegreeCost H) (codegreeCost_nonneg H)
    p δ hp hp1 hδ v true F
    (fun σ σ' π hh => away_uniform_prob_congr H hH v (σ,π) (σ',π) S hh (fun _ _ => rfl))
  change μ.mean (fun ω => F ω*(if ω.1 v=true then 1 else 0)*
    (if ∀ x ∈ S, ω.2 {v,x}=true then 1 else 0)) = _
  rw [hpairs,hvertex]
  have hprob : (awayLaw H hH (codegreeCost H) (codegreeCost_nonneg H) p δ hp hp1 hδ v).prob S = μ.mean F := rfl
  rw [hprob]
  by_cases hvS : v ∈ S
  · have hz (ω : RestrictionData V) : F ω=0 := by
      have hn : S ∉ awayFamily H ω v := fun hh => (mem_awayFamily.mp hh).2 hvS
      simp [F,FiniteLaw.uniform,hn]
    have hm : μ.mean F=0 := by
      calc
        _ = μ.mean (fun _ => 0) := congrArg μ.mean (funext hz)
        _ = 0 := μ.mean_const 0
    rw [hm]
    ring
  · rw [incidentCost_eq_pair_sum H v S hvS]
    simp only [Bool.true_eq,ite_true]
    ring

theorem extension_fraction_mean (H : Finset (Finset V)) (hH : IsTripleSystem H)
    (p δ : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hδ : 0 ≤ δ) (v : V) :
    (restrictionDataLaw (codegreeCost H) (codegreeCost_nonneg H) p δ hp hp1 hδ).mean
      (fun ω => (FiniteLaw.uniform (awayFamily H ω v) (awayFamily_nonempty hH ω v)).mean
        (fun S => (if ω.1 v=true then 1 else 0)*
          (if linkCount H v S=0 then 1 else 0)*(if ∀ x ∈ S, ω.2 {v,x}=true then 1 else 0))) =
      p*(awayLaw H hH (codegreeCost H) (codegreeCost_nonneg H) p δ hp hp1 hδ v).mean
        (fun S => if linkCount H v S=0 then Real.exp (-δ*incidentCost H v S) else 0) := by
  let μ := restrictionDataLaw (codegreeCost H) (codegreeCost_nonneg H) p δ hp hp1 hδ
  let ν := awayLaw H hH (codegreeCost H) (codegreeCost_nonneg H) p δ hp hp1 hδ v
  change μ.mean (fun ω => ∑ S : Finset V,
    (FiniteLaw.uniform (awayFamily H ω v) (awayFamily_nonempty hH ω v)).prob S *
      ((if ω.1 v=true then 1 else 0)*(if linkCount H v S=0 then 1 else 0)*
        (if ∀ x ∈ S, ω.2 {v,x}=true then 1 else 0))) =
    p*(∑ S : Finset V, ν.prob S*(if linkCount H v S=0 then Real.exp (-δ*incidentCost H v S) else 0))
  rw [μ.mean_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  by_cases hzero : linkCount H v S=0
  · simp only [if_pos hzero,mul_one]
    have hh := extension_weight H hH p δ hp hp1 hδ v S
    convert hh using 1
    · congr 1
      funext ω
      ring
    · ring
  · simp only [if_neg hzero,mul_zero,zero_mul,μ.mean_const]

theorem extendible_fraction_identity (H : Finset (Finset V)) (hH : IsTripleSystem H)
    (ω : RestrictionData V) (v : V) :
    ((extendibleFamily H ω v).card : ℝ)/(awayFamily H ω v).card =
      (FiniteLaw.uniform (awayFamily H ω v) (awayFamily_nonempty hH ω v)).mean
        (fun S => (if ω.1 v=true then 1 else 0)*(if linkCount H v S=0 then 1 else 0)*
          (if ∀ x ∈ S, ω.2 {v,x}=true then 1 else 0)) := by
  rw [FiniteLaw.uniform_mean]
  congr 1
  rw [Finset.card_eq_sum_ones,Nat.cast_sum]
  simp only [Nat.cast_one,extendibleFamily,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro S hS
  simp only [feasible_insert_iff hH ω v hS]
  by_cases hv : ω.1 v=true <;> by_cases hlink : linkCount H v S=0 <;>
    by_cases hpairs : ∀ x ∈ S, ω.2 {v,x}=true <;> simp [hv,hlink,hpairs]

theorem away_insert_bound (H : Finset (Finset V)) (hH : IsTripleSystem H)
    (p δ : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hδ : 0 ≤ δ) (v : V) :
    (p/2)*(awayLaw H hH (codegreeCost H) (codegreeCost_nonneg H) p δ hp hp1 hδ v).mean
      (fun S => if linkCount H v S=0 then Real.exp (-δ*incidentCost H v S) else 0) ≤
      (restrictedLaw H hH (codegreeCost H) (codegreeCost_nonneg H) p δ hp hp1 hδ).event
        (fun I => v ∈ I) := by
  let μ := restrictionDataLaw (codegreeCost H) (codegreeCost_nonneg H) p δ hp hp1 hδ
  have hpoint := μ.mean_mono (fun ω => feasible_uniform_insertion H hH ω v)
  have hfrac := extension_fraction_mean H hH p δ hp hp1 hδ v
  simp_rw [extendible_fraction_identity H hH] at hpoint
  have hevent : (restrictedLaw H hH (codegreeCost H) (codegreeCost_nonneg H) p δ hp hp1 hδ).event
      (fun I => v ∈ I) = μ.mean (fun ω =>
        (FiniteLaw.uniform (feasibleFamily H ω) (feasibleFamily_nonempty hH ω)).event (fun I => v ∈ I)) := by
    rw [← FiniteLaw.mean_indicator,restrictedLaw,FiniteLaw.bind_mean]
    simp_rw [FiniteLaw.mean_indicator]
    congr 1
  rw [hevent]
  have hleft : μ.mean (fun ω =>
      ((FiniteLaw.uniform (awayFamily H ω v) (awayFamily_nonempty hH ω v)).mean
        (fun S => (if ω.1 v=true then 1 else 0)*(if linkCount H v S=0 then 1 else 0)*
          (if ∀ x ∈ S, ω.2 {v,x}=true then 1 else 0)))/2) =
      (p/2)*(awayLaw H hH (codegreeCost H) (codegreeCost_nonneg H) p δ hp hp1 hδ v).mean
        (fun S => if linkCount H v S=0 then Real.exp (-δ*incidentCost H v S) else 0) := by
    rw [FiniteLaw.mean_div,hfrac]
    ring
  rwa [hleft] at hpoint

end TP3
