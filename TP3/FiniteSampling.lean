module

public import TP3.FiniteProbability
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

@[expose] public section

namespace TP3.FiniteLaw

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

theorem prob_le_one (μ : FiniteLaw Ω) (ω : Ω) : μ.prob ω ≤ 1 := by
  rw [← μ.total]
  exact Finset.single_le_sum (fun x _ => μ.nonneg x) (Finset.mem_univ ω)

/-- Some outcome has positive probability, since the masses sum to one. -/
theorem exists_positive_mass (μ : FiniteLaw Ω) : ∃ ω, 0 < μ.prob ω := by
  by_contra! h
  have hz : ∀ ω, μ.prob ω = 0 := fun ω => le_antisymm (h ω) (μ.nonneg ω)
  have ht := μ.total
  simp [hz] at ht

/-- A finite expectation is attained or exceeded by an outcome in the
support. Zero-probability outcomes cannot supply the witness. -/
theorem exists_support_ge_mean (μ : FiniteLaw Ω) (X : Ω → ℝ) :
    ∃ ω, 0 < μ.prob ω ∧ μ.mean X ≤ X ω := by
  classical
  by_contra h
  have hsmall (ω : Ω) (hω : 0 < μ.prob ω) : X ω < μ.mean X := by
    apply lt_of_not_ge
    intro hx
    exact h ⟨ω,hω,hx⟩
  obtain ⟨ω,hω⟩ := μ.exists_positive_mass
  have hpoint (x : Ω) : μ.prob x * X x ≤ μ.prob x * μ.mean X := by
    by_cases hx : 0 < μ.prob x
    · exact (mul_lt_mul_of_pos_left (hsmall x hx) hx).le
    · have hz : μ.prob x = 0 := le_antisymm (le_of_not_gt hx) (μ.nonneg x)
      simp [hz]
  have hs := Finset.sum_lt_sum (s := Finset.univ)
    (fun x _ => hpoint x)
    ⟨ω,Finset.mem_univ ω,mul_lt_mul_of_pos_left (hsmall ω hω) hω⟩
  change μ.mean X < μ.mean (fun _ => μ.mean X) at hs
  rw [μ.mean_const] at hs
  exact lt_irrefl _ hs

/-- Choose uniformly from a specified nonempty finite family. -/
noncomputable def uniform (F : Finset Ω) (hF : F.Nonempty) : FiniteLaw Ω := by
  classical
  exact {
    prob := fun ω => if ω ∈ F then 1 / (F.card : ℝ) else 0
    nonneg := fun ω => by split <;> positivity
    total := by
      have hcard : (F.card : ℝ) ≠ 0 := by exact_mod_cast hF.card_ne_zero
      simp [hcard] }

theorem uniform_prob_le [DecidableEq Ω] (F : Finset Ω) (hF : F.Nonempty) (ω : Ω) :
    (uniform F hF).prob ω ≤ if ω ∈ F then 1 else 0 := by
  classical
  by_cases h : ω ∈ F
  · simpa [h] using (uniform F hF).prob_le_one ω
  · simp [uniform, h]

/-- Draw an initial observation, then draw from a law depending on it. -/
def bind {Ω' : Type*} [Fintype Ω'] (μ : FiniteLaw Ω)
    (ν : Ω → FiniteLaw Ω') : FiniteLaw Ω' where
  prob y := ∑ x, μ.prob x * (ν x).prob y
  nonneg y := Finset.sum_nonneg fun x _ => mul_nonneg (μ.nonneg x) ((ν x).nonneg y)
  total := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, fun x => (ν x).total, mul_one, μ.total]

theorem bind_prob (μ : FiniteLaw Ω) {Ω' : Type*} [Fintype Ω']
    (ν : Ω → FiniteLaw Ω') (y : Ω') :
    (μ.bind ν).prob y = μ.mean (fun x => (ν x).prob y) := rfl

theorem bind_mean (μ : FiniteLaw Ω) {Ω' : Type*} [Fintype Ω']
    (ν : Ω → FiniteLaw Ω') (f : Ω' → ℝ) :
    (μ.bind ν).mean f = μ.mean (fun x => (ν x).mean f) := by
  simp only [mean, bind, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

theorem uniform_bind_prob_le_event {Ω' : Type*} [Fintype Ω']
    (μ : FiniteLaw Ω) (F : Ω → Finset Ω') (hF : ∀ x, (F x).Nonempty) (y : Ω') :
    (μ.bind (fun x => uniform (F x) (hF x))).prob y ≤
      μ.event (fun x => y ∈ F x) := by
  classical
  rw [bind_prob, ← μ.mean_indicator]
  exact μ.mean_mono fun x => uniform_prob_le _ _ _

/-- One independent trial with success probability p. -/
def bernoulli (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) : FiniteLaw Bool where
  prob x := if x then p else 1-p
  nonneg x := by cases x <;> simp [hp, sub_nonneg.mpr hp1]
  total := by simp

@[simp] theorem bernoulli_mean_indicator {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (bernoulli p hp hp1).mean (fun b => if b = true then 1 else 0) = p := by
  simp [mean, bernoulli]

section Product

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : ι → Type*} [∀ i, Fintype (S i)]

/-- Independent draws at each of finitely many positions. -/
def product (μ : ∀ i, FiniteLaw (S i)) : FiniteLaw ((i : ι) → S i) where
  prob ω := ∏ i, (μ i).prob (ω i)
  nonneg ω := Finset.prod_nonneg fun i _ => (μ i).nonneg (ω i)
  total := by
    classical
    rw [← Fintype.prod_sum]
    simp [(μ _).total]

theorem mean_product (μ : ∀ i, FiniteLaw (S i)) (X : ∀ i, S i → ℝ) :
    (product μ).mean (fun ω => ∏ i, X i (ω i)) = ∏ i, (μ i).mean (X i) := by
  classical
  simp only [mean, product, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i ω => (μ i).prob ω * X i ω)).symm

theorem product_event (μ : ∀ i, FiniteLaw (S i)) (P : ∀ i, S i → Prop) :
    (product μ).event (fun ω => ∀ i, P i (ω i)) = ∏ i, (μ i).event (P i) := by
  classical
  rw [← mean_indicator]
  have hi (ω : (i : ι) → S i) :
      (if ∀ i, P i (ω i) then (1 : ℝ) else 0) =
        ∏ i, if P i (ω i) then (1 : ℝ) else 0 := by
    simp [Finset.prod_boole]
  simp_rw [hi]
  rw [mean_product μ (fun i x => if P i x then (1 : ℝ) else 0)]
  simp_rw [mean_indicator]

end Product

section Successes

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem bernoulli_required (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (A : Finset ι) :
    (product fun i => bernoulli (p i) (hp i) (hp1 i)).event
      (fun ω => ∀ i ∈ A, ω i = true) = ∏ i ∈ A, p i := by
  classical
  rw [product_event _ (fun i b => i ∈ A → b = true)]
  have hprob (i : ι) :
      (bernoulli (p i) (hp i) (hp1 i)).event (fun b => i ∈ A → b = true) =
        if i ∈ A then p i else 1 := by
    by_cases hi : i ∈ A
    · simp only [hi, true_implies, ite_true]
      rw [← mean_indicator]
      exact bernoulli_mean_indicator _ _
    · simp [event, bernoulli, hi]
  simp_rw [hprob]
  exact Finset.prod_ite_mem_eq A p

end Successes

end TP3.FiniteLaw
