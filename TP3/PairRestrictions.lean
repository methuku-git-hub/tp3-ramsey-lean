module

public import TP3.FiniteProbability
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Powerset

@[expose] public section

namespace TP3

open scoped BigOperators

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω]

theorem exp_mean_le (μ : FiniteLaw Ω) (X : Ω → ℝ) :
    Real.exp (μ.mean X) ≤ μ.mean (fun ω => Real.exp (X ω)) := by
  simpa only [mean, smul_eq_mul] using
    convexOn_exp.map_sum_le (t := Finset.univ) (w := μ.prob) (p := X)
      (fun ω _ => μ.nonneg ω) μ.total (fun _ _ => Set.mem_univ _)

end FiniteLaw

variable {V : Type*} [Fintype V]

/-- The generating function of all subsets, with each vertex weighted by a. -/
theorem sum_pow_card (a : ℝ) :
    (∑ S : Finset V, a ^ S.card) = (1 + a) ^ Fintype.card V := by
  simpa using (Finset.prod_one_add (f := fun _ : V => a) Finset.univ).symm

/-- The exponential moment estimate in the random-restriction lemma.
The hypothesis is the probability bound obtained by requiring all vertices
and all pairs of a given set to be allowed. -/
theorem restriction_moment (μ : FiniteLaw (Finset V)) (W : Finset V → ℝ)
    {p δ u : ℝ} (hu : 0 < u)
    (hpoint : ∀ S, μ.prob S ≤ p ^ S.card * Real.exp (-δ * W S)) :
    μ.mean (fun S => u ^ S.card * Real.exp (δ * W S)) ≤
      (1 + p * u) ^ Fintype.card V := by
  calc
    _ ≤ ∑ S : Finset V,
        (p ^ S.card * Real.exp (-δ * W S)) *
          (u ^ S.card * Real.exp (δ * W S)) := by
      apply Finset.sum_le_sum
      intro S _
      exact mul_le_mul_of_nonneg_right (hpoint S) (by positivity)
    _ = ∑ S : Finset V, (p*u)^S.card := by
      apply Finset.sum_congr rfl
      intro S _
      have hexp : Real.exp (-δ * W S) * Real.exp (δ * W S) = 1 := by
        rw [← Real.exp_add]
        have hz : -δ * W S + δ * W S = 0 := by ring
        rw [hz, Real.exp_zero]
      calc
        _ = (p ^ S.card * u ^ S.card) *
            (Real.exp (-δ * W S) * Real.exp (δ * W S)) := by ring
        _ = _ := by rw [hexp, mul_one, mul_pow]
    _ = _ := sum_pow_card (p*u)

/-- Taking logarithms after Jensen's inequality bounds the mean pair cost. -/
theorem restriction_log_moment (μ : FiniteLaw (Finset V))
    (W : Finset V → ℝ) {p δ u : ℝ} (_hp : 0 < p) (hu : 0 < u)
    (hpoint : ∀ S, μ.prob S ≤ p ^ S.card * Real.exp (-δ * W S)) :
    μ.mean (fun S => (S.card : ℝ)) * Real.log u + δ * μ.mean W ≤
      (Fintype.card V : ℝ) * Real.log (1 + p*u) := by
  have h := μ.exp_mean_le (fun S => (S.card : ℝ) * Real.log u + δ * W S)
  have hexp (S : Finset V) :
      Real.exp ((S.card : ℝ) * Real.log u + δ * W S) =
        u ^ S.card * Real.exp (δ * W S) := by
    rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hu]
  simp_rw [hexp] at h
  have hupper := h.trans (restriction_moment μ W hu hpoint)
  have hlog := Real.log_le_log
    (Real.exp_pos (μ.mean (fun S => (S.card : ℝ) * Real.log u + δ * W S))) hupper
  rw [Real.log_exp, Real.log_pow] at hlog
  have hm :
      μ.mean (fun S => (S.card : ℝ) * Real.log u + δ * W S) =
        μ.mean (fun S => (S.card : ℝ)) * Real.log u + δ * μ.mean W := by
    calc
      _ = μ.mean (fun S => Real.log u * (S.card : ℝ) + δ * W S) := by
        congr 1
        funext S
        ring
      _ = _ := by
        rw [μ.mean_add, μ.mean_mul_const, μ.mean_mul_const]
        ring
  rwa [hm] at hlog

/-- The mean total pair cost is at most density times log(ep/density)/δ. -/
theorem restriction_charge (μ : FiniteLaw (Finset V))
    (W : Finset V → ℝ) {p δ ρ : ℝ} (hp : 0 < p) (hρ : 0 < ρ)
    (hdensity : μ.mean (fun S => (S.card : ℝ)) = (Fintype.card V : ℝ) * ρ)
    (hpoint : ∀ S, μ.prob S ≤ p ^ S.card * Real.exp (-δ * W S)) :
    δ * μ.mean W ≤
      (Fintype.card V : ℝ) * ρ * Real.log (Real.exp 1 * p / ρ) := by
  have hu : 0 < ρ/p := div_pos hρ hp
  have h := restriction_log_moment μ W hp hu hpoint
  rw [hdensity] at h
  have hcancel : p*(ρ/p) = ρ := by field_simp
  rw [hcancel] at h
  have hlog : Real.log (1+ρ) ≤ ρ := by
    have := Real.log_le_sub_one_of_pos (by linarith : 0 < 1+ρ)
    linarith
  have hN : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hcombine : Real.log (Real.exp 1 * p / ρ) = 1 - Real.log (ρ/p) := by
    rw [Real.log_div (ne_of_gt (mul_pos (Real.exp_pos 1) hp)) hρ.ne',
      Real.log_mul (Real.exp_ne_zero 1) hp.ne', Real.log_exp,
      Real.log_div hρ.ne' hp.ne']
    ring
  rw [hcombine]
  nlinarith [mul_le_mul_of_nonneg_left hlog hN]

end TP3
