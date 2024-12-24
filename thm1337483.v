Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1337483_term_abbrevs.
Lemma lem1337479 (x : prod hreal hreal) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1337480 (x : prod hreal hreal) : (treal_eq x) = (treal_eq x).
Proof. exact (eq_refl (treal_eq x)). Qed.
Lemma lem1337481 (x : prod hreal hreal) : term1 x.
Proof. exact (ex_intro (term2 x) x (@lem1337480 x)). Qed.
Lemma lem1337482 (x : prod hreal hreal) : (term1 x) = (term0 x).
Proof. exact (SYM (@lem1337479 x)). Qed.
Lemma lem1337483 (x : prod hreal hreal) : term0 x.
Proof. exact (EQ_MP (@lem1337482 x) (@lem1337481 x)). Qed.
