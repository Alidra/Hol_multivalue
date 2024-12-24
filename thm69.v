Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm69_term_abbrevs.
Require Import NOT_DEF_spec.
Lemma lem63 (P : Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem64 (P : Prop) : (~ P) = (term0 P).
Proof. exact (MK_COMB (@lem56) (@lem63 P)). Qed.
Lemma lem65 (P : Prop) : (term0 P) = (P -> False).
Proof. exact (eq_refl (term0 P)). Qed.
Lemma lem66 (P : Prop) : (term1 P) = (term1 P).
Proof. exact (eq_refl (term1 P)). Qed.
Lemma lem67 (P : Prop) : ((~ P) = (term0 P)) = ((~ P) = (P -> False)).
Proof. exact (MK_COMB (@lem66 P) (@lem65 P)). Qed.
Lemma lem68 (P : Prop) : (~ P) = (P -> False).
Proof. exact (EQ_MP (@lem67 P) (@lem64 P)). Qed.
Lemma lem69 (P : Prop) : (P -> False) = (~ P).
Proof. exact (SYM (@lem68 P)). Qed.
