Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm10578_term_abbrevs.
Require Import thm1823_spec.
Lemma lem10572 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem10573 (p : Prop) : (term0 p) = (term1 p).
Proof. exact (@lem10572 (~ p)). Qed.
Lemma lem10574 (p : Prop) : (@eq Prop p) = (@eq Prop p).
Proof. exact (eq_refl (@eq Prop p)). Qed.
Lemma lem10575 (p : Prop) : (p = (term0 p)) = (p = (term1 p)).
Proof. exact (MK_COMB (@lem10574 p) (@lem10573 p)). Qed.
Lemma lem10578 (p : Prop) : (p = (term1 p)) = (p = (term0 p)).
Proof. exact (SYM (@lem10575 p)). Qed.
