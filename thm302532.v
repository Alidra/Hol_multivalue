Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm302532_term_abbrevs.
Require Import thm75543_spec.
Lemma lem302521 (n : nat) : term0 n.
Proof. exact (@lem75543 n). Qed.
Lemma lem302522 (n : nat) : (term0 n) = ((NUMERAL n) = n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem302525 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem302522 n) (@lem302521 n)). Qed.
Lemma lem302526 : (NUMERAL 0) = 0.
Proof. exact (@lem302525 0). Qed.
Lemma lem302527 (h1 : (NUMERAL 0) = 0) : (NUMERAL 0) = 0.
Proof. exact (h1). Qed.
Lemma lem302528 (h1 : (NUMERAL 0) = 0) : 0 = (NUMERAL 0).
Proof. exact (SYM (@lem302527 h1)). Qed.
Lemma lem302529 (h1 : 0 = (NUMERAL 0)) : 0 = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem302530 (h1 : 0 = (NUMERAL 0)) : (NUMERAL 0) = 0.
Proof. exact (SYM (@lem302529 h1)). Qed.
Lemma lem302531 : ((NUMERAL 0) = 0) = (0 = (NUMERAL 0)).
Proof. exact (prop_ext (fun h1 : (NUMERAL 0) = 0 => @lem302528 h1) (fun h1 : 0 = (NUMERAL 0) => @lem302530 h1)). Qed.
Lemma lem302532 : 0 = (NUMERAL 0).
Proof. exact (EQ_MP (@lem302531) (@lem302526)). Qed.
