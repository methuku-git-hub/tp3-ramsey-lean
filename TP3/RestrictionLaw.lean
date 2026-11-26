module

public import TP3.Definitions
public import TP3.FiniteSampling
public import TP3.PairRestrictions

@[expose] public section

namespace TP3

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Vertex decisions and pair decisions in the preliminary experiment.
The pair mask is indexed by all subsets; only two-element subsets are used. -/
abbrev RestrictionData (V : Type*) := (V → Bool) × (Finset V → Bool)

/-- Sum the given pair costs over the pairs contained in S. -/
def pairCost (c : Finset V → ℝ) (S : Finset V) : ℝ :=
  ∑ e ∈ S.powersetCard 2, c e

/-- Feasible sets are independent and meet both types of random restriction. -/
noncomputable def feasibleFamily (H : Finset (Finset V)) (ω : RestrictionData V) :
    Finset (Finset V) := by
  classical
  exact Finset.univ.filter fun S => Independent H S ∧
    (∀ x ∈ S, ω.1 x = true) ∧ (∀ e ∈ S.powersetCard 2, ω.2 e = true)

theorem feasibleFamily_nonempty {H : Finset (Finset V)} (hH : IsTripleSystem H)
    (ω : RestrictionData V) : (feasibleFamily H ω).Nonempty := by
  refine ⟨∅, ?_⟩
  simp only [feasibleFamily, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨?_, by simp, by simp⟩
  intro e he hes
  have hempty := Finset.subset_empty.mp hes
  have hc := hH e he
  simp [hempty] at hc

/-- Sample vertices with probability p and independently allow each pair e
with probability exp(-δ c(e)). -/
noncomputable def restrictionDataLaw (c : Finset V → ℝ) (hc : ∀ e, 0 ≤ c e)
    (p δ : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hδ : 0 ≤ δ) :
    FiniteLaw (RestrictionData V) :=
  (FiniteLaw.product fun _ : V => FiniteLaw.bernoulli p hp hp1).staged
    (fun _ => FiniteLaw.product fun e : Finset V =>
      FiniteLaw.bernoulli (Real.exp (-δ * c e)) (Real.exp_pos _).le
        (Real.exp_le_one_iff.mpr (by nlinarith [hc e])))

/-- The actual distribution used in the last step of the manuscript. -/
noncomputable def restrictedLaw (H : Finset (Finset V)) (hH : IsTripleSystem H)
    (c : Finset V → ℝ) (hc : ∀ e, 0 ≤ c e)
    (p δ : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hδ : 0 ≤ δ) :
    FiniteLaw (Finset V) :=
  (restrictionDataLaw c hc p δ hp hp1 hδ).bind
    (fun ω => FiniteLaw.uniform (feasibleFamily H ω) (feasibleFamily_nonempty hH ω))

theorem restriction_data_required (c : Finset V → ℝ) (hc : ∀ e, 0 ≤ c e)
    (p δ : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hδ : 0 ≤ δ) (S : Finset V) :
    (restrictionDataLaw c hc p δ hp hp1 hδ).event
      (fun ω => (∀ x ∈ S, ω.1 x = true) ∧
        (∀ e ∈ S.powersetCard 2, ω.2 e = true)) =
      p ^ S.card * Real.exp (-δ * pairCost c S) := by
  classical
  let μ := FiniteLaw.product fun _ : V => FiniteLaw.bernoulli p hp hp1
  let ν := FiniteLaw.product fun e : Finset V =>
      FiniteLaw.bernoulli (Real.exp (-δ * c e)) (Real.exp_pos _).le
        (Real.exp_le_one_iff.mpr (by nlinarith [hc e]))
  have hν : ν.event (fun ω => ∀ e ∈ S.powersetCard 2, ω e = true) =
      Real.exp (-δ * pairCost c S) := by
    rw [FiniteLaw.bernoulli_required]
    rw [← Real.exp_sum]
    congr 1
    simp [pairCost, Finset.mul_sum]
  have hμ : μ.event (fun ω => ∀ x ∈ S, ω x = true) = p ^ S.card := by
    rw [FiniteLaw.bernoulli_required]
    simp
  change (μ.staged (fun _ => ν)).event _ = _
  rw [FiniteLaw.staged_event]
  have hinner (x : V → Bool) :
      ν.event (fun y => (∀ a ∈ S, x a = true) ∧
        (∀ e ∈ S.powersetCard 2, y e = true)) =
      (if ∀ a ∈ S, x a = true then (1 : ℝ) else 0) *
        Real.exp (-δ * pairCost c S) := by
    by_cases hx : ∀ a ∈ S, x a = true
    · have hfun :
          (fun y : Finset V → Bool => (∀ a ∈ S, x a = true) ∧
            (∀ e ∈ S.powersetCard 2, y e = true)) =
          (fun y => ∀ e ∈ S.powersetCard 2, y e = true) := by
        funext y
        exact propext ⟨fun h => h.2, fun h => ⟨hx,h⟩⟩
      rw [hfun, ite_eq_left hx, one_mul]
      exact hν
    · simp [hx, FiniteLaw.event]
  simp_rw [hinner]
  have hmean : μ.mean (fun x =>
      (if ∀ a ∈ S, x a = true then (1 : ℝ) else 0) *
        Real.exp (-δ * pairCost c S)) =
      Real.exp (-δ * pairCost c S) * μ.event (fun x => ∀ a ∈ S, x a = true) := by
    rw [← μ.mean_indicator]
    convert μ.mean_mul_const (Real.exp (-δ * pairCost c S))
      (fun x => if ∀ a ∈ S, x a = true then (1 : ℝ) else 0) using 1
    congr 1
    funext x
    ring
  rw [hmean, hμ, mul_comm]

/-- The pointwise inclusion estimate is proved for the constructed law,
including the normalization of the uniform choice from the feasible family. -/
theorem restrictedLaw_prob_le (H : Finset (Finset V)) (hH : IsTripleSystem H)
    (c : Finset V → ℝ) (hc : ∀ e, 0 ≤ c e)
    (p δ : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hδ : 0 ≤ δ) (S : Finset V) :
    (restrictedLaw H hH c hc p δ hp hp1 hδ).prob S ≤
      p ^ S.card * Real.exp (-δ * pairCost c S) := by
  calc
    _ ≤ (restrictionDataLaw c hc p δ hp hp1 hδ).event
        (fun ω => S ∈ feasibleFamily H ω) :=
      FiniteLaw.uniform_bind_prob_le_event _ _ _ _
    _ ≤ (restrictionDataLaw c hc p δ hp hp1 hδ).event
        (fun ω => (∀ x ∈ S, ω.1 x = true) ∧
          (∀ e ∈ S.powersetCard 2, ω.2 e = true)) := by
      apply FiniteLaw.event_mono
      intro ω hω
      classical
      unfold feasibleFamily at hω
      exact (Finset.mem_filter.mp hω).2.2
    _ = _ := restriction_data_required c hc p δ hp hp1 hδ S

/-- Every outcome with positive mass is an independent set of H. -/
theorem restrictedLaw_independent (H : Finset (Finset V)) (hH : IsTripleSystem H)
    (c : Finset V → ℝ) (hc : ∀ e, 0 ≤ c e)
    (p δ : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hδ : 0 ≤ δ) (S : Finset V)
    (hS : 0 < (restrictedLaw H hH c hc p δ hp hp1 hδ).prob S) :
    Independent H S := by
  classical
  by_contra hind
  have h := FiniteLaw.uniform_bind_prob_le_event
    (restrictionDataLaw c hc p δ hp hp1 hδ)
    (feasibleFamily H) (feasibleFamily_nonempty hH) S
  have hzero : (restrictionDataLaw c hc p δ hp hp1 hδ).event
      (fun ω => S ∈ feasibleFamily H ω) = 0 := by
    simp [FiniteLaw.event, feasibleFamily, hind]
  rw [hzero] at h
  exact (not_lt_of_ge h) hS

/-- The pair-cost estimate for the specified random experiment. -/
theorem restrictedLaw_charge (H : Finset (Finset V)) (hH : IsTripleSystem H)
    (c : Finset V → ℝ) (hc : ∀ e, 0 ≤ c e)
    (p δ : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hδ : 0 ≤ δ)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hdensity :
      (restrictedLaw H hH c hc p δ hp.le hp1 hδ).mean
        (fun S => (S.card : ℝ)) = (Fintype.card V : ℝ)*ρ) :
    δ * (restrictedLaw H hH c hc p δ hp.le hp1 hδ).mean (pairCost c) ≤
      (Fintype.card V : ℝ)*ρ*Real.log (Real.exp 1*p/ρ) :=
  restriction_charge _ _ hp hρ hdensity
    (restrictedLaw_prob_le H hH c hc p δ hp.le hp1 hδ)

end TP3
