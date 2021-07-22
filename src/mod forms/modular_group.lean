import tactic.ring
import tactic.tidy
import group_theory.group_action
import linear_algebra.special_linear_group
import linear_algebra.determinant
import data.matrix.notation
import group_theory.group_action.basic
import algebra.group_action_hom
import linear_algebra.matrix
import .GLnR

--import .matrix_groups

/-  This is an attempt to update the kbb birthday repo, so most is not orginal to me-/

universe u 

run_cmd mk_simp_attr `SL2Z
 open finset 
 open matrix 
@[tidy] meta def tidy_ring := `[ring]

def MAT2:= matrix (fin 2) (fin 2) ℤ

section 


open_locale matrix
@[reducible]
def SL2Z := special_linear_group (fin 2) ℤ

instance: group SL2Z:= infer_instance



@[derive decidable_eq]
def  integral_matrices_with_determinant (m : ℤ ) :={ A : matrix (fin 2) (fin 2) ℤ  // A.det = m }




variable (m: ℤ)



instance coe_matrix : has_coe (integral_matrices_with_determinant m) (matrix (fin 2) (fin 2) ℤ) :=
⟨λ A, A.val⟩



instance coe_fun : has_coe_to_fun (integral_matrices_with_determinant m) :=
{ F   := λ _, fin 2 → fin 2 → ℤ,
  coe := λ A, A.val }


def to_lin' (A : integral_matrices_with_determinant m) := matrix.to_lin' A

namespace integral_matrices_with_determinant


lemma ext_iff (A B :  integral_matrices_with_determinant m) : A = B ↔ (∀ i j, A i j = B i j) :=
iff.trans subtype.ext_iff_val ⟨(λ h i j, congr_fun (congr_fun h i) j), matrix.ext⟩

@[ext] lemma ext (A B : integral_matrices_with_determinant m) : (∀ i j, A i j = B i j) → A = B :=

begin 
rw ext_iff,
simp,
end

end  integral_matrices_with_determinant








def N': matrix  (fin 2) (fin 2 ) ℤ:= ![![-1, 0], ![0, -1]]

lemma ND: N'.det =1 :=

begin
rw N',
refl,
end   

def N : SL2Z := ⟨ N', ND ⟩




def Sr: matrix  (fin 2) (fin 2 ) ℤ:= ![![1, 0], ![0, 1]]

lemma SD2: Sr.det =1 :=

begin
rw Sr,
refl,
end   

def Ni : special_linear_group (fin 2) ℤ  := ⟨ Sr, SD2 ⟩



def S2: matrix  (fin 2) (fin 2 ) ℤ:= ![![-2, 0], ![0, -1]]







lemma valorsl (A : SL2Z):  A 0 0 = A.1 0 0 ∧ A 0 1 = A.1 0 1 ∧ A 1 0 = A.1 1 0 ∧ A 1 1 = A.1 1 1  :=

begin
split, refl, split, refl,split, refl, refl,
end  


lemma valor_mat_m (A : integral_matrices_with_determinant m):  A 0 0 = A.1 0 0 ∧ A 0 1 = A.1 0 1 ∧ A 1 0 = A.1 1 0 ∧ A 1 1 = A.1 1 1  :=

begin
split, refl, split, refl,split, refl, refl,
end  

lemma MND (M: matrix (fin 2) (fin 2) ℤ): M.det= (M 0 0) * (M 1 1) - (M 0 1) * (M 1 0):=

begin 
exact GLn.det_of_22 M,  
end   

lemma det_onee (A: SL2Z):  det A= A 0 0 * A 1 1 - A 1 0 * A 0 1 :=

begin
have:= MND A.1, have ad:=A.2,simp [valorsl] at *, rw ad at this, have cg : A.1 1 0* A.1 0 1 =  A.1 0 1* A.1 1 0, by {ring,},
simp at cg, rw cg,exact this,

end  



lemma str (A: SL2Z): det A = 1:= A.2

lemma det_onne (A: SL2Z):  A 0 0 * A 1 1 - A 1 0 * A 0 1=1 :=

begin
rw ← str A,
rw det_onee,
end 

lemma det_m (M: integral_matrices_with_determinant m): (M 0 0 * M 1 1 - M 1 0 * M 0 1)=m:=

begin 
 have H:= MND M.1, simp [valor_mat_m] at *, have m2:=M.2, simp at m2, rw m2 at H,
 have cg : M.1 1 0* M.1 0 1 =  M.1 0 1* M.1 1 0, by {ring,}, simp at cg, rw cg, exact H.symm,
end  


lemma det_m''' (M: integral_matrices_with_determinant m) (h: M 1 0 = 0): M 0 0 * M 1 1=m:=

begin 
have:=det_m _ M,  rw h at this, simp at this,exact this,
end  

lemma det_m' (M: integral_matrices_with_determinant m): M 0 0 * M 1 1 - M 1 0 * M 0 1= M.val.det:=

begin
have:=MND M.1, simp [valor_mat_m],simp  at this, 
 have cg : M.1 1 0* M.1 0 1 =  M.1 0 1* M.1 1 0, by {ring,}, simp at cg, rw cg, exact this.symm,
end 


lemma det_m2 (M: integral_matrices_with_determinant m): M.1 0 0 * M.1 1 1 - M.1 1 0 * M.1 0 1= M.val.det:=

begin
have:= det_m' _ M, simp [valor_mat_m] at *, exact this,
end 


@[simp, SL2Z] lemma SL2Z_mul_a (A B : SL2Z) : (A * B) 0 0 = A 0 0 * B 0 0 + A 0 1 * B 1 0 := 

begin
simp,
rw  matrix.mul_apply,
rw finset.sum_fin_eq_sum_range,
rw sum_range_succ,
simp only [nat.succ_pos', fin.mk_zero, dif_pos, nat.one_lt_bit0_iff, sum_singleton, fin.mk_one, range_one],
end



 


@[simp, SL2Z] lemma SL2Z_mul_b (A B : SL2Z) : (A * B) 0 1 = A 0 0 * B 0 1 + A 0 1 * B 1 1 :=

begin
simp,
rw  matrix.mul_apply,
rw finset.sum_fin_eq_sum_range,
rw sum_range_succ,
simp only [nat.succ_pos', fin.mk_zero, dif_pos, nat.one_lt_bit0_iff, sum_singleton, fin.mk_one, range_one],
end






@[simp, SL2Z] lemma SL2Z_mul_c (A B : SL2Z) : (A * B) 1 0 = A 1 0 * B 0 0 + A 1 1 * B 1 0 := 

begin
simp,
rw  matrix.mul_apply,
rw finset.sum_fin_eq_sum_range,
rw sum_range_succ,
simp only [nat.succ_pos', fin.mk_zero, dif_pos, nat.one_lt_bit0_iff, sum_singleton, fin.mk_one, range_one],
end






@[simp, SL2Z] lemma SL2Z_mul_d (A B : SL2Z) : (A * B) 1 1  = A 1 0 * B 0 1 + A 1 1  * B 1 1 :=

begin
simp,
rw  matrix.mul_apply,
rw finset.sum_fin_eq_sum_range,
rw sum_range_succ,
simp only [nat.succ_pos', fin.mk_zero, dif_pos, nat.one_lt_bit0_iff, sum_singleton, fin.mk_one, range_one],
end

lemma mre: N * N = (1: SL2Z):=

begin
ext i j,
fin_cases i; fin_cases j,
rw SL2Z_mul_a N N, simp, refl,rw SL2Z_mul_b N N, simp, refl, rw SL2Z_mul_c N N, simp, refl, rw SL2Z_mul_d N N, simp, refl,
end   

 lemma ng : Ni = (1: special_linear_group (fin 2) ℤ ):=

 begin
  rw Ni, simp_rw Sr,  ext i j,fin_cases i; fin_cases j, simp [valorsl], simp [valorsl], simp [valorsl], simp [valorsl],
  
 end   

lemma vale (A : integral_matrices_with_determinant m): A 0 0 = A.1 0 0 ∧ A 0 1 = A.1 0 1 ∧ A 1 0 = A.1 1 0 ∧ A 1 1 = A.1 1 1  :=

begin
split, refl, split, refl,split, refl, refl,
end  


@[simp, SL2Z] lemma SL2Z_one_a : (1 : SL2Z) 0 0 = 1 := rfl
@[simp, SL2Z] lemma SL2Z_one_b : (1 : SL2Z) 0 1 = 0 := rfl
@[simp, SL2Z] lemma SL2Z_one_c : (1 : SL2Z) 1 0 = 0 := rfl
@[simp, SL2Z] lemma SL2Z_one_d : (1 : SL2Z) 1 1 = 1 := rfl


lemma sl2_inv (A: SL2Z) (B: SL2Z)  (h1: B.1 0 0 = A.1 1 1)  (h2: B.1 0 1= - A.1 0 1) (h3: B.1 1 0 = - A.1 1 0) (h4: B.1 1 1 = A.1 0 0): A.1 * B.1= (1: SL2Z).1 :=

begin
have:= GLn.mat_mul_expl A.1 B.1,   
ext i j, 
fin_cases i; fin_cases j,
have e1:= this.1,rw e1, rw h1, rw h3, simp,
have Adet:= det_onne A, simp [valorsl] at Adet, ring_nf,
have cg : A.1 1 0* A.1 0 1 =  A.1 0 1* A.1 1 0, by {ring,},
simp at cg, rw ← cg, exact Adet, have e2:= this.2.1, rw e2, rw [h2,h4], ring,
have e3:= this.2.2.1, rw e3, rw [h1,h3], ring, rw this.2.2.2, rw [h2,h4], simp,
have Adet:= det_onne A, simp [valorsl] at Adet, rw add_comm, 
have cg : A.1 1 1* A.1 0 0 =  A.1 0 0* A.1 1 1, by {ring,}, simp at cg, rw cg, convert Adet,
 
end 



lemma sl2_inv' (A: SL2Z) (B: SL2Z)  (h1: B 0 0 = A 1 1)  (h2: B 0 1= - A 0 1) (h3: B 1 0 = - A 1 0) (h4: B 1 1 = A 0 0): A * B= 1 :=

begin
have H :=sl2_inv A B h1 h2 h3 h4, simp at H, rw ← matrix.mul_eq_mul at H, norm_cast at H,
simp only [valorsl] at *, cases B, cases A, dsimp at *, ext1, cases j, 
cases i, dsimp at *, simp at *, dsimp at *, solve_by_elim,

end


lemma sl2_inv'' (A: SL2Z) (B: SL2Z)  (h1: B 0 0 = A 1 1)  (h2: B 0 1= - A 0 1) (h3: B 1 0 = - A 1 0) (h4: B 1 1 = A 0 0): A⁻¹= B :=

begin
have H :=sl2_inv' A B h1 h2 h3 h4, have:=eq_inv_of_mul_eq_one H, simp_rw this, simp,
end  

def ainv' (A: SL2Z): matrix (fin 2) (fin 2) ℤ:=![![A 1 1, -A 0 1], ![-A 1 0 , A  0 0]]

lemma ainvdet (A : SL2Z): (ainv' A).det=1:=
begin
rw ainv', rw MND, simp, have :=det_onne A, simp only [valorsl] at *, rw mul_comm at this,
have cg: A.val 0 1 * A.val 1 0= A.val 1 0 * A.val 0 1, by {ring,},
rw cg, exact this,
end 


def Ainv (A: SL2Z): SL2Z:=
⟨ ainv' A, ainvdet A⟩

lemma Ainv_is_inv (A: SL2Z): A⁻¹ = Ainv A:=
begin
rw sl2_inv'' A (Ainv A), simp [valorsl] at *, rw Ainv, simp_rw ainv', ring,
 simp [valorsl] at *, rw Ainv, simp_rw ainv', simp only [cons_val_one, neg_inj, cons_val_zero, subtype.coe_mk, head_cons],
   simp only [valorsl], simp,
   simp [valorsl] at *, rw Ainv, simp_rw ainv', simp,simp only [valorsl], simp,simp only [valorsl], rw Ainv, simp_rw ainv', simp [valorsl],
end



@[simp, SL2Z] lemma SL2Z_inv_a (A : SL2Z) : (A⁻¹) 0 0 = A 1 1 :=

begin
simp only [valorsl], rw Ainv_is_inv, rw Ainv,simp_rw ainv',simp only [valorsl, cons_val_zero],

end 




@[simp, SL2Z] lemma SL2Z_inv_b (A : SL2Z) : (A⁻¹) 0 1 = -A 0 1 := 

begin
simp only [valorsl], rw Ainv_is_inv, rw Ainv,simp_rw ainv',simp only [valorsl, cons_val_one, cons_val_zero, head_cons],
end  

@[simp, SL2Z] lemma SL2Z_inv_c (A : SL2Z) : (A⁻¹) 1 0  = -A 1 0 := 

begin
simp only [valorsl], rw Ainv_is_inv, rw Ainv,simp_rw ainv',simp only [valorsl, cons_val_one, cons_val_zero, head_cons],
end



@[simp, SL2Z] lemma SL2Z_inv_d (A : SL2Z) : (A⁻¹) 1 1 = A 0 0 := 

begin
simp only [valorsl], rw Ainv_is_inv, rw Ainv,simp_rw ainv',simp only [valorsl, cons_val_one, head_cons],
end 




def SL2Z_M (m : ℤ) : SL2Z → integral_matrices_with_determinant m → integral_matrices_with_determinant m :=
λ A B, ⟨A.1 ⬝ B.1, by erw [det_mul, A.2, B.2, one_mul]⟩




lemma one_smull  : ∀ (M: integral_matrices_with_determinant m ),  SL2Z_M m (1: SL2Z) M= M :=

begin
rw SL2Z_M,
simp,
end

lemma mul_smull : ∀ (A B : SL2Z ), ∀ (M: integral_matrices_with_determinant m ), SL2Z_M m (A * B ) M= SL2Z_M m A (SL2Z_M m B M):=

begin  
simp [SL2Z_M],
intros A B M, 
simp [matrix.mul_assoc],
refl,
end   




instance (m: ℤ )  :  mul_action  (SL2Z) (integral_matrices_with_determinant m):=

{ smul := SL2Z_M (m : ℤ),
  one_smul := one_smull (m: ℤ ),
  mul_smul := mul_smull (m:ℤ ) }

section


variables  (A : SL2Z) (M : integral_matrices_with_determinant m)

@[simp, SL2Z] lemma smul_is_mul (A : SL2Z) (M : integral_matrices_with_determinant m): (A • M).1 =A * M :=
begin
simp [SL2Z_M],
refl,
end  

lemma m_a_b (m : ℤ) (hm : m ≠ 0) (A : SL2Z) (M N : integral_matrices_with_determinant m):   (A • M) = N ↔  N 0 0= A 0 0 * M 0 0 + A 0 1 * M 1 0 ∧ N 0 1= A 0 0 * M 0 1 + A 0 1 * M 1 1 ∧ N 1 0= A 1 0 * M 0 0 + A 1 1 * M 1 0 ∧ N 1 1= A 1 0 * M 0 1 + A 1 1 * M 1 1:=

begin
split,
intro h,
have:= GLn.mat_mul_expl A M,  rw ← h, simp [valor_mat_m],intro h, ext i j, fin_cases i; fin_cases j, simp [valor_mat_m] at *, rw h.1,
simp [valor_mat_m] at *, rw h.2.1,simp [valor_mat_m] at *, rw h.2.2.1,simp [valor_mat_m] at *, rw h.2.2.2,

end  

@[simp, SL2Z] lemma SL2Z_M_a : (SL2Z_M m A M).1 0 0 = A.1 0 0 * M.1 0 0 + A.1 0 1 * M.1 1 0 :=

begin
simp [SL2Z_M, add_mul, mul_add, mul_assoc],
rw mul_apply,
rw finset.sum_fin_eq_sum_range,
rw sum_range_succ,
rw sum_range_succ,
simp,
end   


@[simp, SL2Z] lemma SL2Z_M_aa: (A • M) 0 0= A 0 0 * M 0 0 + A 0 1 * M 1 0 :=

begin
apply SL2Z_M_a,
end 



@[simp, SL2Z] lemma SL2Z_M_b : (SL2Z_M m A M).1 0 1 = A.1 0 0 * M.1 0 1 + A.1 0 1 * M.1 1 1 := 

begin
simp [SL2Z_M, add_mul, mul_add, mul_assoc],
rw mul_apply,
rw finset.sum_fin_eq_sum_range,
rw sum_range_succ,
rw sum_range_succ,
simp,
end


@[simp, SL2Z] lemma SL2Z_M_ba: (A • M) 0 1= A 0 0 * M 0 1 + A 0 1 * M 1 1 :=

begin
apply SL2Z_M_b,
end 






@[simp, SL2Z] lemma SL2Z_M_c : (SL2Z_M m A M).1 1 0 = A.1 1 0 * M.1 0 0 + A.1 1 1  * M.1 1 0 :=

begin
simp [SL2Z_M, add_mul, mul_add, mul_assoc],
rw mul_apply,
rw finset.sum_fin_eq_sum_range,
rw sum_range_succ,
rw sum_range_succ,
simp,
end  

@[simp, SL2Z] lemma SL2Z_M_ca: (A • M) 1 0= A 1 0 * M 0 0 + A 1 1 * M 1 0 :=

begin
apply SL2Z_M_c,
end 


@[simp, SL2Z] lemma SL2Z_M_d : (SL2Z_M m A M).1 1 1 = A.1 1 0 * M.1 0 1 + A.1 1 1 * M.1 1 1 := 

begin
simp [SL2Z_M, add_mul, mul_add, mul_assoc],
rw mul_apply,
rw finset.sum_fin_eq_sum_range,
rw sum_range_succ,
rw sum_range_succ,
simp,
end


@[simp, SL2Z] lemma SL2Z_M_da: (A • M) 1 1= A 1 0 * M 0 1 + A 1 1 * M 1 1 :=

begin
apply SL2Z_M_d,
end   




namespace integral_matrices_with_determinant 
 
variables  ( B : integral_matrices_with_determinant m)

def mi (m: ℤ) (M: integral_matrices_with_determinant m) : (matrix (fin 2) (fin 2) ℤ) := ![![-M 0 0,  - M 0 1], ![-M 1 0 , -M 1 1]] 
 


lemma fff (m: ℤ) (M: integral_matrices_with_determinant m): (mi m M).det = m:=

begin
rw mi, rw MND, simp, have:=det_m m M, simp [valor_mat_m] at *,
have cg : M.1 1 0* M.1 0 1 =  M.1 0 1* M.1 1 0, by {ring,}, simp at cg, rw ← cg,exact this,
end   


def MATINV (m : ℤ) : integral_matrices_with_determinant m → integral_matrices_with_determinant m :=
λ A , ⟨mi m  A, by apply fff⟩

instance (m : ℤ) : has_neg (integral_matrices_with_determinant m) :=
⟨λ A, MATINV m A ⟩



@[simp, SL2Z] lemma neg_a : (-B) 0 0 = -B 0 0 := rfl
@[simp, SL2Z] lemma neg_b : (-B) 0 1 = -B 0 1 := rfl
@[simp, SL2Z] lemma neg_c : (-B) 1 0 = -B 1 0  := rfl
@[simp, SL2Z] lemma neg_d : (-B) 1 1 = -B 1 1 := rfl
@[simp, SL2Z]  lemma neg_neg : -(-B) = B :=
begin
ext i j, fin_cases i; fin_cases j,simp,simp, simp,simp,  
end


end integral_matrices_with_determinant



namespace SL2Z

variables (C D B : SL2Z)





def mis (M: SL2Z) : (matrix (fin 2) (fin 2) ℤ) := ![![-M 0 0,  - M 0 1], ![-M 1 0 , -M 1 1]] 
 


lemma fffs (M: SL2Z): (mis M).det = 1:=

begin 
rw mis, have:= det_onne M, rw MND, simp, simp [valorsl] at *,
have cg : M.1 1 0* M.1 0 1 =  M.1 0 1* M.1 1 0, by {ring,}, simp at cg, rw  ← cg,exact this,
end   

def MATINVs  : SL2Z → SL2Z :=
λ A , ⟨mis  A, by apply fffs⟩

instance  : has_neg (SL2Z) :=
⟨λ A, MATINVs  A ⟩


@[simp, SL2Z] lemma neg_a : (-B) 0 0 = -B 0 0 := rfl
@[simp, SL2Z] lemma neg_b : (-B) 0 1 = -B 0 1 := rfl
@[simp, SL2Z] lemma neg_c : (-B) 1 0 = -B 1 0  := rfl
@[simp, SL2Z] lemma neg_d : (-B) 1 1 = -B 1 1 := rfl
@[simp, SL2Z]  lemma neg_neg : -(-B) = B :=
begin
ext i j, fin_cases i; fin_cases j,simp,simp, simp,simp,  
end

@[simp, SL2Z] protected lemma neg_one_mul : -1 * C = -C := 
begin
ext i j, fin_cases i; fin_cases j, simp, simp,simp,simp,
end


@[simp, SL2Z] protected lemma neg_mul_neg : -C * -D = C * D :=
begin
ext i j, fin_cases i; fin_cases j; simp,
end

@[simp, SL2Z] protected lemma neg_mul : -(C * D) = -C * D :=
begin
ext i j, fin_cases i; fin_cases j, simp, ring, simp,ring, simp,ring,simp,ring,
end


end SL2Z
end 
end 