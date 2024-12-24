Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1317734_term_abbrevs.
Lemma lem1317730 (x : nadd) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1317731 (x : nadd) : (nadd_eq x) = (nadd_eq x).
Proof. exact (eq_refl (nadd_eq x)). Qed.
Lemma lem1317732 (x : nadd) : term1 x.
Proof. exact (ex_intro (term2 x) x (@lem1317731 x)). Qed.
Lemma lem1317733 (x : nadd) : (term1 x) = (term0 x).
Proof. exact (SYM (@lem1317730 x)). Qed.
Lemma lem1317734 (x : nadd) : term0 x.
Proof. exact (EQ_MP (@lem1317733 x) (@lem1317732 x)). Qed.
