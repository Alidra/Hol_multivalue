Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_MUL_RID_term_abbrevs.
Require Import REAL_MUL_RID_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2306212 (x : int) : term0 x.
Proof. exact (@lem1383409 (real_of_int x)). Qed.
Lemma lem2306213 (x : int) : (term0 x) = ((term1 x) = (real_of_int x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2306214 (x : int) : (term1 x) = (real_of_int x).
Proof. exact (EQ_MP (@lem2306213 x) (@lem2306212 x)). Qed.
Lemma lem2306216 (n : nat) : (real_of_num n) = (term2 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2306217 : term3 = term4.
Proof. exact (@lem2306216 term5). Qed.
Lemma lem2306218 (x : int) : (term6 x) = (term6 x).
Proof. exact (eq_refl (term6 x)). Qed.
Lemma lem2306219 (x : int) : (term1 x) = (term7 x).
Proof. exact (MK_COMB (@lem2306218 x) (@lem2306217)). Qed.
Lemma lem2306221 (x : int) (y : int) : (term8 x y) = (term9 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2306222 (x : int) : (term7 x) = (term10 x).
Proof. exact (@lem2306221 x term11). Qed.
Lemma lem2306223 (x : int) : (term1 x) = (term10 x).
Proof. exact (TRANS (@lem2306219 x) (@lem2306222 x)). Qed.
Lemma lem2306224 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2306225 (x : int) : (term12 x) = (term13 x).
Proof. exact (MK_COMB (@lem2306224) (@lem2306223 x)). Qed.
Lemma lem2306226 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2306227 (x : int) : ((term1 x) = (real_of_int x)) = ((term10 x) = (real_of_int x)).
Proof. exact (MK_COMB (@lem2306225 x) (@lem2306226 x)). Qed.
Lemma lem2306229 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2306230 (x : int) : ((term10 x) = (real_of_int x)) = ((term14 x) = x).
Proof. exact (@lem2306229 (term14 x) x). Qed.
Lemma lem2306231 (x : int) : ((term1 x) = (real_of_int x)) = ((term14 x) = x).
Proof. exact (TRANS (@lem2306227 x) (@lem2306230 x)). Qed.
Lemma lem2306232 (x : int) : (term14 x) = x.
Proof. exact (EQ_MP (@lem2306231 x) (@lem2306214 x)). Qed.
Lemma lem2306233 : term15.
Proof. exact (fun x : int => @lem2306232 x). Qed.
