Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_ADD_RID_term_abbrevs.
Require Import REAL_ADD_RID_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2301201 (x : int) : term0 x.
Proof. exact (@lem1361590 (real_of_int x)). Qed.
Lemma lem2301202 (x : int) : (term0 x) = ((term1 x) = (real_of_int x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2301203 (x : int) : (term1 x) = (real_of_int x).
Proof. exact (EQ_MP (@lem2301202 x) (@lem2301201 x)). Qed.
Lemma lem2301205 (n : nat) : (real_of_num n) = (term2 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2301206 : term3 = term4.
Proof. exact (@lem2301205 (NUMERAL 0)). Qed.
Lemma lem2301207 (x : int) : (term5 x) = (term5 x).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem2301208 (x : int) : (term1 x) = (term6 x).
Proof. exact (MK_COMB (@lem2301207 x) (@lem2301206)). Qed.
Lemma lem2301210 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2301211 (x : int) : (term6 x) = (term9 x).
Proof. exact (@lem2301210 x term10). Qed.
Lemma lem2301212 (x : int) : (term1 x) = (term9 x).
Proof. exact (TRANS (@lem2301208 x) (@lem2301211 x)). Qed.
Lemma lem2301213 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2301214 (x : int) : (term11 x) = (term12 x).
Proof. exact (MK_COMB (@lem2301213) (@lem2301212 x)). Qed.
Lemma lem2301215 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2301216 (x : int) : ((term1 x) = (real_of_int x)) = ((term9 x) = (real_of_int x)).
Proof. exact (MK_COMB (@lem2301214 x) (@lem2301215 x)). Qed.
Lemma lem2301218 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2301219 (x : int) : ((term9 x) = (real_of_int x)) = ((term13 x) = x).
Proof. exact (@lem2301218 (term13 x) x). Qed.
Lemma lem2301220 (x : int) : ((term1 x) = (real_of_int x)) = ((term13 x) = x).
Proof. exact (TRANS (@lem2301216 x) (@lem2301219 x)). Qed.
Lemma lem2301221 (x : int) : (term13 x) = x.
Proof. exact (EQ_MP (@lem2301220 x) (@lem2301203 x)). Qed.
Lemma lem2301222 : term14.
Proof. exact (fun x : int => @lem2301221 x). Qed.
