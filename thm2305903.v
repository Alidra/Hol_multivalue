Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2305903_term_abbrevs.
Require Import REAL_MUL_AC_spec.
Lemma lem2305895 (n : real) (m : real) : (real_mul m n) = (real_mul n m).
Proof. exact (proj1 (@lem1486340 n m (@el real))). Qed.
Lemma lem2305896 (n : real) : term0 n.
Proof. exact (fun m : real => @lem2305895 n m). Qed.
Lemma lem2305897 : term1.
Proof. exact (fun n : real => @lem2305896 n). Qed.
Lemma lem2305898 (n : int) : term2 n.
Proof. exact (@lem2305897 (real_of_int n)). Qed.
Lemma lem2305899 (n : int) : (term2 n) = (term3 n).
Proof. exact (eq_refl (term2 n)). Qed.
Lemma lem2305900 (n : int) : term3 n.
Proof. exact (EQ_MP (@lem2305899 n) (@lem2305898 n)). Qed.
Lemma lem2305901 (n : int) (m : int) : term4 n m.
Proof. exact (@lem2305900 n (real_of_int m)). Qed.
Lemma lem2305902 (n : int) (m : int) : (term4 n m) = ((term5 m n) = (term5 n m)).
Proof. exact (eq_refl (term4 n m)). Qed.
Lemma lem2305903 (n : int) (m : int) : (term5 m n) = (term5 n m).
Proof. exact (EQ_MP (@lem2305902 n m) (@lem2305901 n m)). Qed.
