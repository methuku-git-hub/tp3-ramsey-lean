module

public import TP3.FiniteSampling

@[expose] public section

namespace TP3

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω]

theorem mean_sub (μ : FiniteLaw Ω) (X Y : Ω → ℝ) :
    μ.mean (fun ω => X ω - Y ω) = μ.mean X - μ.mean Y := by
  simp only [mean,mul_sub,Finset.sum_sub_distrib]

theorem mean_div (μ : FiniteLaw Ω) (X : Ω → ℝ) (a : ℝ) :
    μ.mean (fun ω => X ω/a) = μ.mean X/a := by
  simp only [mean,mul_div_assoc,Finset.sum_div]

end FiniteLaw

end TP3
