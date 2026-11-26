module

public import TP3.Conditioning

@[expose] public section

namespace TP3.FiniteLaw

attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {Ω K : Type*} [Fintype Ω] [DecidableEq Ω] [DecidableEq K]

theorem uniform_mean_congr_on (F : Finset Ω) (hF : F.Nonempty) (f g : Ω → ℝ)
    (h : ∀ (x : Ω) (hx : x ∈ F), f x=g x) : (uniform F hF).mean f=(uniform F hF).mean g := by
  rw [uniform_mean,uniform_mean]
  congr 1
  exact Finset.sum_congr rfl h

/-- Averaging equal conditional means on every nonempty observation
fibre gives equality under the original uniform law. -/
theorem uniform_mean_eq_of_fiber_means (F : Finset Ω) (hF : F.Nonempty)
    (obs : Ω → K) (f g : Ω → ℝ)
    (h : ∀ (x : Ω) (hx : x ∈ F),
      (uniform (F.filter (fun y => obs y=obs x)) ⟨x,Finset.mem_filter.mpr ⟨hx,rfl⟩⟩).mean f =
      (uniform (F.filter (fun y => obs y=obs x)) ⟨x,Finset.mem_filter.mpr ⟨hx,rfl⟩⟩).mean g) :
    (uniform F hF).mean f=(uniform F hF).mean g := by
  rw [uniform_mean,uniform_mean]
  congr 1
  have hsum (x : Ω) (hx : x ∈ F) :
      (∑ y ∈ F.filter (fun y => obs y=obs x), f y)=
        ∑ y ∈ F.filter (fun y => obs y=obs x), g y := by
    have hh := h x hx
    erw [uniform_mean,uniform_mean] at hh
    have hne : ((F.filter (fun y => obs y=obs x)).card : ℝ) ≠ 0 := by
      exact_mod_cast (show (F.filter (fun y => obs y=obs x)).Nonempty from ⟨x,by simp [hx]⟩).card_ne_zero
    exact (div_left_inj' hne).mp hh
  have hmap : ∀ x ∈ F, obs x ∈ F.image obs := fun x hx => Finset.mem_image.mpr ⟨x,hx,rfl⟩
  calc
    _ = ∑ k ∈ F.image obs, ∑ y ∈ F.filter (fun y => obs y=k), f y :=
      (Finset.sum_fiberwise_of_maps_to hmap f).symm
    _ = ∑ k ∈ F.image obs, ∑ y ∈ F.filter (fun y => obs y=k), g y := by
      apply Finset.sum_congr rfl
      intro k hk
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hk
      exact hsum x hx
    _ = _ := Finset.sum_fiberwise_of_maps_to hmap g

end TP3.FiniteLaw
