Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1246844_term_abbrevs.
Require Import DIST_ELIM_THM_spec.
Lemma lem1246844 (_22840 : nat) (_22841 : nat) (_22842 : nat -> Prop) : (term0 _22842 _22841 _22840) = (term1 _22840 _22841 _22842).
Proof. exact (@lem1246841 _22840 _22841 _22842). Qed.
