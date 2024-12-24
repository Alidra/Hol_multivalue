Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm21107_term_abbrevs.
Require Import thm21031_spec.
Require Import thm21104_spec.
Require Import thm21105_spec.
Lemma lem21107 (p : Prop) : (term0 p) = (~ p).
Proof. exact (or_elim (@lem21031 p) (fun h0 : p = True => @lem21105 p h0) (fun h0 : p = False => @lem21104 p h0)). Qed.
