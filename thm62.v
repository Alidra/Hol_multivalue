Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm62_term_abbrevs.
Require Import NOT_DEF_spec.
Lemma lem57 (P : Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem58 (P : Prop) : (~ P) = (term0 P).
Proof. exact (MK_COMB (@lem56) (@lem57 P)). Qed.
Lemma lem59 (P : Prop) : (term0 P) = (P -> False).
Proof. exact (eq_refl (term0 P)). Qed.
Lemma lem60 (P : Prop) : (term1 P) = (term1 P).
Proof. exact (eq_refl (term1 P)). Qed.
Lemma lem61 (P : Prop) : ((~ P) = (term0 P)) = ((~ P) = (P -> False)).
Proof. exact (MK_COMB (@lem60 P) (@lem59 P)). Qed.
Lemma lem62 (P : Prop) : (~ P) = (P -> False).
Proof. exact (EQ_MP (@lem61 P) (@lem58 P)). Qed.
