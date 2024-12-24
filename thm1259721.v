Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259721_term_abbrevs.
Require Import thm1259695_spec.
Lemma lem1259721 : term0.
Proof. exact (fun m : nat => @lem1259695 m). Qed.
