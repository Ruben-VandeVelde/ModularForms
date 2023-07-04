/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler
-/
import Mathlib.Algebra.DirectSum.Ring
import Mathlib.NumberTheory.Modular
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathlib.NumberTheory.ModularForms.Basic

open scoped ComplexConjugate UpperHalfPlane

local prefix:1024 "↑ₘ" => @coe _ (Matrix (Fin 2) (Fin 2) _) _

local notation "GL(" n ", " R ")" "⁺" => Matrix.GLPos (Fin n) R

local notation "SL(" n ", " R ")" => Matrix.SpecialLinearGroup (Fin n) R

open ModularForm

open CuspForm

open SlashInvariantForm

open Complex

noncomputable section

/-- The upper half space as a subset of `ℂ` which is convenient sometimes.-/
def UpperHalfPlane.upperHalfSpace :=
  {z : ℂ | 0 < z.im}
#align upper_half_plane.upper_half_space UpperHalfPlane.upperHalfSpace

theorem upper_half_plane_isOpen : IsOpen UpperHalfPlane.upperHalfSpace :=
  IsOpen.preimage Complex.continuous_im isOpen_Ioi
#align upper_half_plane_is_open upper_half_plane_isOpen

local notation "ℍ'" =>
  (⟨UpperHalfPlane.upperHalfSpace, upper_half_plane_isOpen⟩ : TopologicalSpace.Opens ℂ)

section GradedRing

namespace ModularForm

open ModularForm

open scoped Topology Manifold UpperHalfPlane

variable (F : Type _) (Γ : Subgroup SL(2, ℤ)) (k : ℤ)

--cast for modular forms, which is useful for removing `heq`'s.
def mcast {a b : ℤ} {Γ : Subgroup SL(2, ℤ)} (h : a = b) (f : ModularForm Γ a) : ModularForm Γ b
    where
  toFun := (f : ℍ → ℂ)
  slash_action_eq' := by intro A; have := f.slash_action_eq' A; convert this; exact h.symm
  holo' := f.holo'
  bdd_at_infty' := by intro A; convert f.bdd_at_infty' A; exact h.symm
#align modular_form.mcast ModularForm.mcast

theorem type_eq {a b : ℤ} (Γ : Subgroup SL(2, ℤ)) (h : a = b) : ModularForm Γ a = ModularForm Γ b :=
  by
  induction h
  rfl
#align modular_form.type_eq ModularForm.type_eq

theorem cast_eq_mcast {a b : ℤ} {Γ : Subgroup SL(2, ℤ)} (h : a = b) (f : ModularForm Γ a) :
    cast (type_eq Γ h) f = mcast h f := by
  induction h
  ext1
  rfl
#align modular_form.cast_eq_mcast ModularForm.cast_eq_mcast

theorem hEq_one_mul (k : ℤ) {Γ : Subgroup SL(2, ℤ)} (f : ModularForm Γ k) :
    HEq ((1 : ModularForm Γ 0).mul f) f :=
  by
  apply heq_of_cast_eq (type_eq Γ (zero_add k).symm).symm
  funext
  rw [cast_eq_mcast, mcast, mul]
  simp only [one_coe_eq_one, one_mul]
  ext1
  rfl
  simp only [zero_add]
#align modular_form.heq_one_mul ModularForm.hEq_one_mul

theorem hEq_mul_one (k : ℤ) {Γ : Subgroup SL(2, ℤ)} (f : ModularForm Γ k) :
    HEq (f.mul (1 : ModularForm Γ 0)) f :=
  by
  apply heq_of_cast_eq (type_eq Γ (add_zero k).symm).symm
  funext
  rw [cast_eq_mcast, mcast, mul]
  simp only [one_coe_eq_one, mul_one]
  ext1
  rfl
  simp only [add_zero]
#align modular_form.heq_mul_one ModularForm.hEq_mul_one

theorem hEq_mul_assoc {a b c : ℤ} (f : ModularForm Γ a) (g : ModularForm Γ b)
    (h : ModularForm Γ c) : HEq ((f.mul g).mul h) (f.mul (g.mul h)) :=
  by
  apply heq_of_cast_eq (type_eq Γ (add_assoc a b c))
  rw [cast_eq_mcast, mcast]
  ext1
  simp only [mul_coe, Pi.mul_apply, ← mul_assoc]
  rfl
#align modular_form.heq_mul_assoc ModularForm.hEq_mul_assoc

theorem hEq_mul_comm (a b : ℤ) (f : ModularForm Γ a) (g : ModularForm Γ b) :
    HEq (f.mul g) (g.mul f) :=
  by
  apply heq_of_cast_eq (type_eq Γ (add_comm a b))
  rw [cast_eq_mcast, mcast]
  ext1
  simp only [mul_coe, Pi.mul_apply, mul_comm]
  rfl
#align modular_form.heq_mul_comm ModularForm.hEq_mul_comm

instance gradedModRing (Γ : Subgroup SL(2, ℤ)) : DirectSum.GCommRing fun k => ModularForm Γ k
    where
  mul k_1 k_2 f g := f.mul g
  one := 1
  one_mul := by
    intro f
    rw [GradedMonoid.GOne.toOne, GradedMonoid.GMul.toMul]
    apply Sigma.ext
    · simp only [zero_add]
    · simp only [Submodule.coe_mk, one_mul, heq_one_mul]
  mul_one := by
    intro f
    rw [GradedMonoid.GOne.toOne, GradedMonoid.GMul.toMul]
    apply Sigma.ext
    · simp only [add_zero]
    · simp only [Submodule.coe_mk, mul_one, heq_mul_one]
  mul_assoc := by
    intro f g h
    rw [GradedMonoid.GMul.toMul]
    apply Sigma.ext
    · apply add_assoc
    · simp only [Submodule.coe_mk, heq_mul_assoc]
  mul_zero := by intro i j f; ext1; simp
  zero_mul := by intro i j f; ext1; simp
  mul_add := by
    intro i j f g h
    ext1
    simp only [Pi.mul_apply, mul_add, mul_coe, add_apply]
  add_mul := by
    intro i j f g h
    ext1
    simp only [add_mul, mul_coe, Pi.mul_apply, add_apply]
  mul_comm := by
    intro f g
    rw [GradedMonoid.GMul.toMul]
    apply Sigma.ext
    · apply add_comm
    · apply heq_mul_comm
  gnpow_zero' := by
    intro f
    apply Sigma.ext
    repeat' rfl
  gnpow_succ' := by
    intro n f
    rw [GradedMonoid.GMul.toMul]
    apply Sigma.ext
    repeat' rfl
  natCast n := n • (1 : ModularForm Γ 0)
  natCast_zero := by simp
  natCast_succ := by intro n; simp only [add_smul, one_nsmul, add_right_inj]; rfl
  intCast n := n • (1 : ModularForm Γ 0)
  intCast_ofNat := by simp
  intCast_negSucc := by intro; apply _root_.neg_smul
#align modular_form.graded_mod_ring ModularForm.gradedModRing

end ModularForm

end GradedRing

section PeterssonProduct

def pet (f g : ℍ → ℂ) (k : ℤ) : ℍ → ℂ := fun z => conj (f z) * g z * UpperHalfPlane.im z ^ k
#align pet pet

def petSelf (f : ℍ → ℂ) (k : ℤ) : ℍ → ℝ := fun z => Complex.abs (f z) ^ 2 * UpperHalfPlane.im z ^ k
#align pet_self petSelf

theorem pet_is_invariant {k : ℤ} {Γ : Subgroup SL(2, ℤ)} (f : SlashInvariantForm Γ k)
    (g : SlashInvariantForm Γ k) {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) (z : ℍ) :
    pet f g k (γ • z) = pet f g k z := by
  dsimp only [pet]
  let D := UpperHalfPlane.denom γ z; have hD : D ≠ 0 := by apply UpperHalfPlane.denom_ne_zero
  have mod_g : g (γ • z) = D ^ k * g z :=
    by
    have tt := (slash_action_eqn' k Γ g) ⟨γ, hγ⟩ z
    dsimp only [UpperHalfPlane.denom] at *; exact tt
  have mod_f : conj (f (γ • z)) = conj D ^ k * conj (f z) :=
    by
    have tt : f (γ • z) = D ^ k * f z := by apply (slash_action_eqn' k Γ f) ⟨γ, hγ⟩ z
    rw [tt, starRingEnd_apply, starRingEnd_apply, star_mul', ← star_zpow₀]; rfl
  rw [mod_f, mod_g]; ring_nf
  suffices ↑(γ • z).im = ↑(UpperHalfPlane.im z) / D / conj D
    by
    rw [this]; simp only [UpperHalfPlane.coe_im, div_zpow]
    have :
      ↑z.im ^ k / D ^ k / conj D ^ k * g z * D ^ k * conj (f z) * conj D ^ k =
        ↑z.im ^ k / D ^ k / conj D ^ k * D ^ k * conj D ^ k * g z * conj (f z) :=
      by ring
    rw [this]; congr 2
    have h1 : D ^ k ≠ 0 := zpow_ne_zero _ hD
    have h2 : conj D ^ k ≠ 0 := by apply zpow_ne_zero; rw [starRingEnd_apply, star_ne_zero];
      exact hD
    field_simp [h1, h2]; ring
  have : ((γ • z : ℍ) : ℂ).im = UpperHalfPlane.im z / Complex.normSq D :=
    by
    rw [UpperHalfPlane.coe_im]
    convert UpperHalfPlane.im_smul_eq_div_normSq γ z
    simp only [UpperHalfPlane.coe_im, coe_coe,
      Matrix.SpecialLinearGroup.coe_GLPos_coe_GL_coe_matrix,
      Matrix.SpecialLinearGroup.coe_matrix_coe, Int.coe_castRingHom]
    suffices ((↑ₘγ).map coe).det = (1 : ℝ) by rw [this]; simp only [one_mul]
    have : (↑ₘγ).map (coe : ℤ → ℝ) = ↑ₘ(γ : SL(2, ℝ)) := by
      simp only [Matrix.SpecialLinearGroup.coe_matrix_coe, Int.coe_castRingHom]
    rw [this]; apply Matrix.SpecialLinearGroup.det_coe
  apply_fun (coe : ℝ → ℂ) at this 
  convert this
  simp only [UpperHalfPlane.coe_im, Complex.ofReal_div]
  rw [div_div, mul_conj]
#align pet_is_invariant pet_is_invariant

theorem petSelf_eq (f : ℍ → ℂ) (k : ℤ) (z : ℍ) : petSelf f k z = re (pet f f k z) :=
  by
  dsimp only [pet, petSelf]
  simp_rw [starRingEnd_apply]
  have : (star (f z) * f z * ↑z.im ^ k).re = (star (f z) * f z).re * ↑z.im ^ k :=
    by
    conv =>
      lhs
      congr
      rw [mul_comm]
    rw [← of_real_zpow, of_real_mul_re, mul_comm]
    simp only [UpperHalfPlane.coe_im, IsROrC.ofReal_real_eq_id, id.def]
  rw [this]; congr
  rw [mul_comm, ← norm_sq_eq_abs, norm_sq]
  simp only [MonoidWithZeroHom.coe_mk, IsROrC.star_def, mul_re, conj_re, conj_im, mul_neg,
    sub_neg_eq_add]
#align pet_self_eq petSelf_eq

theorem petSelf_is_invariant {k : ℤ} {Γ : Subgroup SL(2, ℤ)} (f : SlashInvariantForm Γ k)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) (z : ℍ) : petSelf f k (γ • z) = petSelf f k z := by
  rw [petSelf_eq, petSelf_eq]; congr 1; exact pet_is_invariant f f hγ z
#align pet_self_is_invariant petSelf_is_invariant

end PeterssonProduct

