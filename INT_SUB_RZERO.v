Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_SUB_RZERO_term_abbrevs.
Require Import REAL_SUB_RZERO_spec.
Require Import thm2299897_spec.
Require Import thm2299898_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2310425 (x : int) : term0 x.
Proof. exact (@lem1518006 (real_of_int x)). Qed.
Lemma lem2310426 (x : int) : (term0 x) = ((term1 x) = (real_of_int x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2310427 (x : int) : (term1 x) = (real_of_int x).
Proof. exact (EQ_MP (@lem2310426 x) (@lem2310425 x)). Qed.
Lemma lem2310429 (n : nat) : (real_of_num n) = (term2 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2310430 : term3 = term4.
Proof. exact (@lem2310429 (NUMERAL 0)). Qed.
Lemma lem2310431 (x : int) : (term5 x) = (term5 x).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem2310432 (x : int) : (term1 x) = (term6 x).
Proof. exact (MK_COMB (@lem2310431 x) (@lem2310430)). Qed.
Lemma lem2310434 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2310435 (x : int) : (term6 x) = (term9 x).
Proof. exact (@lem2310434 x term10). Qed.
Lemma lem2310436 (x : int) : (term1 x) = (term9 x).
Proof. exact (TRANS (@lem2310432 x) (@lem2310435 x)). Qed.
Lemma lem2310437 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2310438 (x : int) : (term11 x) = (term12 x).
Proof. exact (MK_COMB (@lem2310437) (@lem2310436 x)). Qed.
Lemma lem2310439 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2310440 (x : int) : ((term1 x) = (real_of_int x)) = ((term9 x) = (real_of_int x)).
Proof. exact (MK_COMB (@lem2310438 x) (@lem2310439 x)). Qed.
Lemma lem2310442 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2310443 (x : int) : ((term9 x) = (real_of_int x)) = ((term13 x) = x).
Proof. exact (@lem2310442 (term13 x) x). Qed.
Lemma lem2310444 (x : int) : ((term1 x) = (real_of_int x)) = ((term13 x) = x).
Proof. exact (TRANS (@lem2310440 x) (@lem2310443 x)). Qed.
Lemma lem2310445 (x : int) : (term13 x) = x.
Proof. exact (EQ_MP (@lem2310444 x) (@lem2310427 x)). Qed.
Lemma lem2310446 : term14.
Proof. exact (fun x : int => @lem2310445 x). Qed.
