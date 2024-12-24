Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm75559_term_abbrevs.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75543_spec.
Lemma lem75544 (n : nat) : term0 n.
Proof. exact (@lem75543 n). Qed.
Lemma lem75545 (n : nat) : (term0 n) = ((NUMERAL n) = n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem75550 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem75545 n) (@lem75544 n)). Qed.
Lemma lem75551 : (NUMERAL 0) = 0.
Proof. exact (@lem75550 0). Qed.
Lemma lem75552 : (@eq nat 0) = (@eq nat 0).
Proof. exact (eq_refl (@eq nat 0)). Qed.
Lemma lem75553 : (0 = (NUMERAL 0)) = (0 = 0).
Proof. exact (MK_COMB (@lem75552) (@lem75551)). Qed.
Lemma lem75555 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem75556 (x : nat) : (x = x) = True.
Proof. exact (@lem75555 nat x). Qed.
Lemma lem75557 : (0 = 0) = True.
Proof. exact (@lem75556 0). Qed.
Lemma lem75558 : (0 = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem75553) (@lem75557)). Qed.
Lemma lem75559 : True = (0 = (NUMERAL 0)).
Proof. exact (SYM (@lem75558)). Qed.
