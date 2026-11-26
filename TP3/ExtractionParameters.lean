module

public import TP3.ExtractionScaling

@[expose] public section

namespace TP3.ExtractionParameters

def b (k : ℕ) : ℕ := 2*k^44
def R (k : ℕ) : ℕ := 200*k^9
def h (k : ℕ) : ℕ := k^28
def r (k : ℕ) : ℕ := 2*k^16
noncomputable def a₀ (k : ℕ) : ℝ := 1/(k:ℝ)^8
noncomputable def s₀ (k : ℕ) : ℝ := (k:ℝ)^2
noncomputable def c₀ (k : ℕ) : ℝ := 1/(k:ℝ)^26
noncomputable def g₀ (k : ℕ) : ℝ := 2*(k:ℝ)^8
noncomputable def τ (k : ℕ) : ℝ := 1/(100*(r k:ℝ)*R k)
noncomputable def t (k : ℕ) : ℝ := k/(τ k)^(b k*R k)
noncomputable def D (k : ℕ) : ℝ := 100*(k:ℝ)^2
noncomputable def A (k : ℕ) : ℝ := leadingCoefficient k (a₀ k) (s₀ k) (c₀ k) (g₀ k) (R k) (r k) (τ k) (D k)
noncomputable def E (k : ℕ) : ℝ := errorCoefficient k (a₀ k) (s₀ k) (c₀ k) (g₀ k)
  (b k) (R k) (h k) (r k) (t k) (D k)

theorem R_pos {k : ℕ} (hk : 0 < k) : 0 < R k := by unfold R; positivity
theorem τ_pos {k : ℕ} (hk : 0 < k) : 0 < τ k := by unfold τ r R; positivity
theorem τ_le_one {k : ℕ} (hk : 0 < k) : τ k ≤ 1 := by
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hr : (1:ℝ) ≤ r k := by
    unfold r
    push_cast
    have := one_le_pow₀ hk1 (n := 16)
    linarith
  have hR : (1:ℝ) ≤ R k := by exact_mod_cast R_pos hk
  unfold τ
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith [mul_le_mul hr hR (by norm_num : (0:ℝ) ≤ 1) (by positivity : (0:ℝ) ≤ r k)]

theorem t_cancel {k : ℕ} (hk : 0 < k) : t k*(τ k)^(b k*R k)=k := by
  unfold t
  exact div_mul_cancel₀ _ (pow_ne_zero _ (τ_pos hk).ne')

theorem A_formula {k : ℕ} (hk : 0 < k) :
    A k=193*(k:ℝ)/200-1-2/(k:ℝ)-2/(k:ℝ)^3 := by
  have hk0 : (k:ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  dsimp [A,leadingCoefficient,a₀,s₀,c₀,g₀,R,r,τ,D]
  push_cast
  field_simp
  ring

theorem A_lower {k : ℕ} (hk : 10 ≤ k) : 3*(k:ℝ)/4 ≤ A k := by
  have hk0 : 0 < k := by omega
  have hk10 : (10:ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0:ℝ) < k := by positivity
  have hc : (1:ℝ) ≤ (k:ℝ)^3 := one_le_pow₀ (by linarith) (n := 3)
  have h₁ : 2/(k:ℝ) ≤ 1/5 := (div_le_iff₀ hkpos).mpr (by linarith)
  have hc10 : (10:ℝ) ≤ (k:ℝ)^3 := by nlinarith [sq_nonneg ((k:ℝ)-1)]
  have h₂ : 2/(k:ℝ)^3 ≤ 1/5 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  rw [A_formula hk0]
  linarith

theorem parameter_ratios {k : ℕ} (hk : 0 < k) (x : ℝ) (hx : 0 < x) :
    2*x^2/(a₀ k*x)=g₀ k*x ∧
    ((g₀ k*x)/(a₀ k*x))*(s₀ k*x)/(c₀ k*x)=(b k:ℝ) ∧
    (g₀ k*x)/(a₀ k*x)=(r k:ℝ) ∧
    (s₀ k*x)/(c₀ k*x)=(h k:ℝ) := by
  have hk0 : (k:ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold a₀ s₀ c₀ g₀ b r h
  push_cast
  constructor
  · field_simp <;> ring
  constructor
  · field_simp <;> ring
  constructor <;> field_simp <;> ring

end TP3.ExtractionParameters
