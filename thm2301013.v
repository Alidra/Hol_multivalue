Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2301013_term_abbrevs.
Require Import REAL_ADD_AC_spec.
Lemma lem2301005 (n : real) (m : real) : (real_add m n) = (real_add n m).
Proof. exact (proj1 (@lem1352530 n m (@el real))). Qed.
Lemma lem2301006 (n : real) : term0 n.
Proof. exact (fun m : real => @lem2301005 n m). Qed.
Lemma lem2301007 : term1.
Proof. exact (fun n : real => @lem2301006 n). Qed.
Lemma lem2301008 (n : int) : term2 n.
Proof. exact (@lem2301007 (real_of_int n)). Qed.
Lemma lem2301009 (n : int) : (term2 n) = (term3 n).
Proof. exact (eq_refl (term2 n)). Qed.
Lemma lem2301010 (n : int) : term3 n.
Proof. exact (EQ_MP (@lem2301009 n) (@lem2301008 n)). Qed.
Lemma lem2301011 (n : int) (m : int) : term4 n m.
Proof. exact (@lem2301010 n (real_of_int m)). Qed.
Lemma lem2301012 (n : int) (m : int) : (term4 n m) = ((term5 m n) = (term5 n m)).
Proof. exact (eq_refl (term4 n m)). Qed.
Lemma lem2301013 (n : int) (m : int) : (term5 m n) = (term5 n m).
Proof. exact (EQ_MP (@lem2301012 n m) (@lem2301011 n m)). Qed.
