module

public import TP3.ProductWeights
public import TP3.LinkCosts

@[expose] public section

namespace TP3

attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem restriction_vertex_factor (c : Finset V → ℝ) (hc : ∀ e, 0 ≤ c e)
    (p δ : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hδ : 0 ≤ δ)
    (v : V) (b : Bool) (F : RestrictionData V → ℝ)
    (hF : ∀ σ σ' π, (∀ x, x ≠ v → σ x=σ' x) → F (σ,π)=F (σ',π)) :
    (restrictionDataLaw c hc p δ hp hp1 hδ).mean
      (fun ω => F ω*(if ω.1 v=b then 1 else 0)) =
      (if b then p else 1-p)*(restrictionDataLaw c hc p δ hp hp1 hδ).mean F := by
  let μ := FiniteLaw.product fun _ : V => FiniteLaw.bernoulli p hp hp1
  let ν := FiniteLaw.product fun e : Finset V =>
    FiniteLaw.bernoulli (Real.exp (-δ*c e)) (Real.exp_pos _).le
      (Real.exp_le_one_iff.mpr (by nlinarith [hc e]))
  change (μ.staged (fun _ => ν)).mean _ = _*(μ.staged (fun _ => ν)).mean F
  rw [FiniteLaw.staged_mean,FiniteLaw.staged_mean]
  have hf (σ : V → Bool) : ν.mean (fun π => F (σ,π)*(if σ v=b then 1 else 0)) =
      ν.mean (fun π => F (σ,π))*(if σ v=b then 1 else 0) := by
    simpa only [mul_comm] using ν.mean_mul_const (if σ v=b then 1 else 0) (fun π => F (σ,π))
  simp_rw [hf]
  apply FiniteLaw.product_coordinate_factor
  intro σ σ' hh
  congr 1
  funext π
  exact hF σ σ' π hh

theorem restriction_incident_pair_factor (c : Finset V → ℝ) (hc : ∀ e, 0 ≤ c e)
    (p δ : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hδ : 0 ≤ δ)
    (v : V) (S : Finset V) (F : RestrictionData V → ℝ)
    (hF : ∀ σ π π', (∀ e, v ∉ e → π e=π' e) → F (σ,π)=F (σ,π')) :
    (restrictionDataLaw c hc p δ hp hp1 hδ).mean
      (fun ω => F ω*(if ∀ x ∈ S, ω.2 {v,x}=true then 1 else 0)) =
      Real.exp (-δ*(∑ x ∈ S, c {v,x})) *
        (restrictionDataLaw c hc p δ hp hp1 hδ).mean F := by
  let μ := FiniteLaw.product fun _ : V => FiniteLaw.bernoulli p hp hp1
  let ν := FiniteLaw.product fun e : Finset V =>
    FiniteLaw.bernoulli (Real.exp (-δ*c e)) (Real.exp_pos _).le
      (Real.exp_le_one_iff.mpr (by nlinarith [hc e]))
  let A := S.image (fun x => ({v,x} : Finset V))
  have hA : ∀ e ∈ A, v ∈ e := by
    intro e he
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp he
    simp
  have hprod : (∏ e ∈ A, Real.exp (-δ*c e))=Real.exp (-δ*(∑ x ∈ S, c {v,x})) := by
    rw [← Real.exp_sum,Finset.sum_image (pair_image_injective v).injOn]
    congr 1
    rw [Finset.mul_sum]
  have hf (σ : V → Bool) : ν.mean (fun π => F (σ,π)*(if ∀ x ∈ S, π {v,x}=true then 1 else 0)) =
      Real.exp (-δ*(∑ x ∈ S, c {v,x}))*ν.mean (fun π => F (σ,π)) := by
    have hh := FiniteLaw.product_required_factor
      (fun e => Real.exp (-δ*c e)) (fun _ => (Real.exp_pos _).le)
      (fun e => Real.exp_le_one_iff.mpr (by nlinarith [hc e]))
      (fun e : Finset V => v ∈ e) A hA (fun π => F (σ,π)) (hF σ)
    rw [hprod] at hh
    simpa only [A,Finset.forall_mem_image] using hh
  change (μ.staged (fun _ => ν)).mean _ = _*(μ.staged (fun _ => ν)).mean F
  rw [FiniteLaw.staged_mean,FiniteLaw.staged_mean]
  simp_rw [hf]
  exact μ.mean_mul_const _ _

theorem incidentCost_eq_pair_sum (H : Finset (Finset V)) (v : V) (S : Finset V) (hv : v ∉ S) :
    incidentCost H v S=∑ x ∈ S, codegreeCost H {v,x} := by
  apply Finset.sum_congr rfl
  intro x hx
  exact if_neg (fun hh : v=x => hv (hh.symm ▸ hx))

end TP3
