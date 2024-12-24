Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2267744_term_abbrevs.
Require Import thm2267726_spec.
Lemma lem2267743 : term0.
Proof. exact (fun a : int => @lem2267726 a). Qed.
Lemma lem2267744 (a : int) : term1 a.
Proof. exact (@lem2267743 a). Qed.
