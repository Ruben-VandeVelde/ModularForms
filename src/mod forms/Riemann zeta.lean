import tactic.ring
import tactic.pi_instances
import .holomorphic_functions
import ring_theory.coprime
import ring_theory.int.basic
import data.complex.basic

universes u v

open complex

open_locale big_operators

noncomputable theory


/-! ### Riemann zeta function at integer values -/


def rie (k : ℕ): ℕ → ℝ :=
λ x, 1/(x+1)^k

/-I could define this for non-integer values, but I dont know how to make it summable, so ill leave it here for now  -/

def Riemann_zeta (k : ℕ): ℝ :=
 ∑' (x : ℕ), (rie k x)


/-Im shifting the index like this since the sum with range in them are easier to work with than trying to split the range into 0 and everything else  -/
def consec : ℕ → ℝ:=
λ x, 1/((x+1)*(x+2))

def consec_sum: ℝ:=
∑' (x: ℕ), consec x


lemma sum_range_sub'' {G : Type*} [add_comm_group G] (f : ℕ → G) (n : ℕ) :
  ∑ i in finset.range n, (f (i) - f (i+1)) = f 0 - f n :=
by { apply finset.sum_range_induction; abel, simp }


lemma au (x : ℝ) (h : x+1 ≠ 0) (h1: x+2 ≠ 0) : 1/((x+1)*(x+2))=1/(x+1)-1/(x+2):=
begin

have:= one_div_mul_sub_mul_one_div_eq_one_div_add_one_div h h1, simp at *, simp at *, rw ← this, simp_rw [mul_inv'], ring,

end

lemma nat_plus_one_not_zero (n: ℕ): (n+1) ≠ 0:=
begin
simp,
end



lemma aux0 (n : ℕ) : consec n = 1/(n+1)-1/(n+2):=
begin
rw consec, simp only, 
have h2: (n+1 : ℝ) ≠ 0, have:=nat_plus_one_not_zero (n), simp, norm_cast, exact this,
have h3: ((n+2) : ℝ) ≠ 0, have:=nat_plus_one_not_zero (n+1), simp, norm_cast, exact this,
have:=au n h2 h3, exact this,
end   

def auxfun: ℕ → ℝ:=
λ x , 1/(x+1)



lemma aux (n :ℕ):∑ i in (finset.range n), consec i=1-1/(n+1):=
begin
simp_rw aux0,
 have:=sum_range_sub'' auxfun, rw auxfun at this,
 simp only [one_div, finset.sum_sub_distrib, nat.cast_zero, nat.cast_add, zero_add, nat.cast_one, div_one] at this, 
simp only [one_div, finset.sum_sub_distrib],  rw ← this, ring_nf,
end



lemma gh (n : ℕ) :  (finset.range n).sum consec  ≤ (1: ℝ):=
begin
 have h: n+1 > 0, simp only [nat.succ_pos', gt_iff_lt], 
 rw aux n, simp only [one_div, sub_le_self_iff, inv_nonneg], norm_cast, simp only [zero_le'],
end 

lemma gh2 (n : ℕ): 0 ≤ consec n:=
begin
rw consec, dsimp only at *, simp only [one_div, inv_nonneg] at *, norm_cast, exact dec_trivial, 
end  

lemma consec_is_sum: summable consec:=

begin
have:=summable_of_sum_range_le  (gh2) (gh), exact this,

/-
rw metric.cauchy_seq_iff', intros ε hε,
 let N1:= int.nat_abs( floor (1/ε)),

let Ne:=finset.range (N1 : ℕ), use Ne, intros n hn, simp_rw dist, 
have h3: n = finset.range (n.card), by {sorry,}, 
have hn2: finset.card (Ne) ≤ finset.card(n), by {sorry,},
have H:= finset.sum_Ico_eq_sub consec hn2, simp at H, rw consec at H, simp_rw Ne, rw h3, 
rw ← H, 
-/


end  

def BUMP : ℕ → ℝ:=
λ x, if x =0 then (1:ℝ)  else 0


lemma BUMP_ZERO_OUTSIDE_SUPP: ∀ x ∉ finset.range 1, BUMP x =0 :=

begin
rw BUMP, simp, intros x H ᾰ, solve_by_elim,
end

lemma BUMP_SUMMABLE: summable BUMP:=
begin
apply summable_of_ne_finset_zero (BUMP_ZERO_OUTSIDE_SUPP),
end  

def consec': ℕ → ℝ:=
λ x, consec x + BUMP x

lemma consec'_is_sum: summable consec':=

begin
rw consec',
apply summable.add   consec_is_sum BUMP_SUMMABLE,
end  

lemma ineq1 (n: ℕ) (h: n > 1): n+1 ≤ n*n:=

begin 
nlinarith, 
end


lemma halp (k n : ℕ) (h : 3 ≤  k) (h1 : n ≠ 0):(n + 1) * (n + 2) ≤ (n + 1) ^ k:=

begin
have h0: 0 ≤ n+1, simp only [zero_le'],  
have hh: 1 ≤ n+1 , simp only [zero_le', le_add_iff_nonneg_left],
have H0: (n+1)^3 ≤ (n+1)^k, apply pow_le_pow hh h,
have H1: (n + 1) * (n + 2) ≤ (n + 1) ^ 3, 
have H2: (n+1)*(n+1)*(n+1)=(n+1)^3, ring, rw ← H2, 
have H3: (n+2) ≤ (n+1)*(n+1), by {apply ineq1, have g: n > 0, apply nat.pos_of_ne_zero h1, simp only [lt_add_iff_pos_left, gt_iff_lt], exact g,},
have:= mul_le_mul_of_nonneg_left H3 h0, rw←  mul_assoc at this, exact this,
apply le_trans H1 H0,
end  

lemma woot (k : ℕ) (h: k ≥ 3) (n : ℕ): rie k n ≤ consec' (n):=
begin
rw rie, rw consec', simp, rw consec, rw BUMP, simp, 
by_cases H: n=0,
rw H, simp, linarith,

simp [H],
apply inv_le_inv_of_le,
have h3: (n+1)*(n+2) ≠ 0, simp only [nat.mul_eq_zero, nat.succ_ne_zero, ne.def, not_false_iff, or_self], 
work_on_goal 0 { dsimp at *, simp at *, norm_cast, exact dec_trivial }, simp at *, norm_cast, 
apply halp, exact h, exact H,

end  

lemma woot2 (k n: ℕ): 0 ≤ rie k n:=
begin
rw rie, simp, norm_cast, exact dec_trivial,
end  

lemma Rie_is_summmable (k: ℕ) (h: k ≥ 3): summable (rie k):=
begin
have:=summable_of_nonneg_of_le (woot2 k) (woot k h) (consec'_is_sum), exact this,
--rw summable_iff_cauchy_seq_finset, rw metric.cauchy_seq_iff',simp, intros ε hε,
--have h0: 1 ≤ k, sorry, 
--have h1:=tendsto_pow_neg_at_top h0,
-- 
-- sum_range_sub_of_monotone
end  

#lint
