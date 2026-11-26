module

public import TP3.ProductSplit
public import TP3.RestrictionEvents

@[expose] public section

namespace TP3.FiniteLaw

attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem bernoulli_coordinate_event (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (i : ι) (b : Bool) :
    (product fun j => bernoulli (p j) (hp j) (hp1 j)).event (fun ω => ω i=b) =
      if b then p i else 1-p i := by
  have hh := bernoulli_required p hp hp1 {i}
  simp only [Finset.mem_singleton,forall_eq,Finset.prod_singleton] at hh
  cases b
  · have heq : (fun ω : ι → Bool => ω i=false)=(fun ω => ¬ω i=true) := by funext ω; simp
    rw [heq,event_not,hh]
    rfl
  · exact hh

theorem product_coordinate_factor (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (i : ι) (b : Bool) (F : (ι → Bool) → ℝ)
    (hF : ∀ ω ω', (∀ j, j ≠ i → ω j=ω' j) → F ω=F ω') :
    (product fun j => bernoulli (p j) (hp j) (hp1 j)).mean
      (fun ω => F ω*(if ω i=b then 1 else 0)) =
      (if b then p i else 1-p i) * (product fun j => bernoulli (p j) (hp j) (hp1 j)).mean F := by
  rw [product_disjoint_mean _ (fun j => j=i) F (fun ω => if ω i=b then 1 else 0) hF]
  · rw [mean_indicator,bernoulli_coordinate_event,mul_comm]
  · intro ω ω' hh
    rw [hh i rfl]

theorem product_required_factor (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (P : ι → Prop) [DecidablePred P] (A : Finset ι) (hA : ∀ i ∈ A, P i)
    (F : (ι → Bool) → ℝ)
    (hF : ∀ ω ω', (∀ j, ¬P j → ω j=ω' j) → F ω=F ω') :
    (product fun j => bernoulli (p j) (hp j) (hp1 j)).mean
      (fun ω => F ω*(if ∀ i ∈ A, ω i=true then 1 else 0)) =
      (∏ i ∈ A, p i) * (product fun j => bernoulli (p j) (hp j) (hp1 j)).mean F := by
  rw [product_disjoint_mean _ P F (fun ω => if ∀ i ∈ A, ω i=true then 1 else 0) hF]
  · rw [mean_indicator,bernoulli_required,mul_comm]
  · intro ω ω' hh
    have heq : (∀ i ∈ A, ω i=true) ↔ (∀ i ∈ A, ω' i=true) := by
      constructor <;> intro h i hi
      · rw [← hh i (hA i hi)]; exact h i hi
      · rw [hh i (hA i hi)]; exact h i hi
    simp only [heq]

end TP3.FiniteLaw
