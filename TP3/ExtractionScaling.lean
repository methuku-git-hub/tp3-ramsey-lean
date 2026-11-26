module

public import TP3.ExtractionFormula

@[expose] public section

namespace TP3

/-- The coefficient of the additional factor 1/x in a joint inclusion
estimate when the original maximum degree is x squared. -/
def collisionCoefficient (b h : ℕ) (g₀ t : ℝ) (j : ℕ) : ℝ :=
  (j:ℝ)^2*b*h*((j:ℝ)*t^(j+1)+g₀*t^(j+2))

noncomputable def leadingCoefficient (k a₀ s₀ c₀ g₀ : ℝ)
    (R r : ℕ) (τ D : ℝ) : ℝ :=
  k*(1-g₀*k/R)-r*R*τ*k-g₀/(2*R)*k^2-k^2/s₀-
    s₀*(2*a₀+c₀*r)*k^5-k^3/D

noncomputable def errorCoefficient (k a₀ s₀ c₀ g₀ : ℝ)
    (b R h r : ℕ) (t D : ℝ) : ℝ :=
  3*g₀*b*h*t^3+54*b*h*t^4+r*h*k^2+
    g₀/(2*R)*collisionCoefficient b h g₀ t 2+
    collisionCoefficient b h g₀ t 2/s₀+
    s₀*(2*a₀+c₀*r)*collisionCoefficient b h g₀ t 5+t^4+
    collisionCoefficient b h g₀ t 3/D

theorem inclusionFormula_scaled (b R h : ℕ) (k g₀ t τ x : ℝ)
    (hx : x ≠ 0) (hφ : t*τ^(b*R)=k) (j : ℕ) :
    inclusionFormula b R h (g₀*x) (t/x) τ j =
      k^j/x^j + collisionCoefficient b h g₀ t j/x^(j+1) := by
  have hφ' : t/x*τ^(b*R)=k/x := by rw [div_mul_eq_mul_div,hφ]
  unfold inclusionFormula collisionCoefficient
  rw [hφ']
  simp only [div_pow,pow_succ]
  field_simp

/-- All terms with shared marks have an extra inverse power of x.
This identity records that fact without dropping any collision term. -/
theorem extractionFraction_scaled (b R h r : ℕ) (k a₀ s₀ c₀ g₀ t τ D x : ℝ)
    (hx : x ≠ 0) (hφ : t*τ^(b*R)=k) :
    extractionFraction (x^2) (a₀*x) (s₀*x) (c₀*x) (g₀*x) b R h r (t/x) τ D =
      leadingCoefficient k a₀ s₀ c₀ g₀ R r τ D/x-
      errorCoefficient k a₀ s₀ c₀ g₀ b R h r t D/x^2 := by
  have hφ' : t/x*τ^(b*R)=k/x := by rw [div_mul_eq_mul_div,hφ]
  unfold extractionFraction
  rw [hφ']
  simp only [inclusionFormula_scaled b R h k g₀ t τ x hx hφ]
  unfold leadingCoefficient errorCoefficient
  simp only [div_mul_eq_mul_div,mul_div_assoc,div_div]
  field_simp
  ring

end TP3
