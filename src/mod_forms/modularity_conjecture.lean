import for_mathlib.mod_forms2
import for_mathlib.congruence_subgroups
import algebraic_geometry.EllipticCurve
import for_mathlib.unform_limits_of_holomorphic

open modular_forms complex
open_locale interval real modular_forms

local notation `ℍ`:=upper_half_plane

noncomputable theory

def map_to_upper (x : ℝ) : ℍ := ⟨(x + I),
  by {simp only [complex.add_im, complex.of_real_im, complex.I_im, zero_add, zero_lt_one],} ⟩

def modular_form_an (n : ℕ) {N : ℕ} {k : ℤ} (f : S k (Gamma0 N))
: ℂ := ∫ (x : ℝ) in 0..1, ( exp (-2 * π * I * n *(x + I))) * f.1 (map_to_upper x)

local notation `a_[`:73 n:0`]` f  :72 := modular_form_an n f

def rat_red (q : ℚ) ( p : ℕ) : (zmod p) := (q.num : zmod p) * (q.denom : zmod p)⁻¹

def set_of_points_mod_n (E : EllipticCurve ℚ) (n : ℕ) := {P : (zmod n) × (zmod n) |
  let ⟨x, y⟩ := P in  y^2 + (rat_red E.a1 n)* x * y+ (rat_red E.a3 n) * y   =
  x^3 +(rat_red E.a2 n)* x^2 + (rat_red E.a4 n) * x + (rat_red E.a6 n)}

def EllipticCurve.ap (E : EllipticCurve ℚ) (p : ℕ) : ℕ :=
  p-(cardinal.mk (set_of_points_mod_n E p)).to_nat

def is_normalised_eigenform {N : ℕ} {k : ℤ}
(f : S k (Gamma0 N)) : Prop :=
(a_[1] f) = 1 ∧
∀ (m n : ℕ) (hmn : m.coprime n), ((a_[n * m] f) = (a_[n] f) * (a_[m] f)) ∧
∀ (p r : ℕ) (hp : p.prime ) (hr : 2 ≤ r),
(a_[p^r] f) = (a_[p] f) * (a_[p^(r-1)] f) - (p^(k-1)) * (a_[p^(r-2)] f)


theorem modularity_conjecture (E : EllipticCurve ℚ) : ∃ (N : ℕ)
  (f : S 2 (Gamma0 N))
  (hf : is_normalised_eigenform f),
  ∀ (p : ℕ) (hp : p.prime ) (hN : (N : zmod p ) ≠ 0 ), a_[p] f = E.ap p :=
begin
sorry,
end
