Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm9120_term_abbrevs.
Lemma lem9114 (p : Prop) (h1 : p) : p.
Proof. exact (h1). Qed.
Lemma lem9115 (p : Prop) : p -> p.
Proof. exact (fun h0 : p => @lem9114 p h0). Qed.
Lemma lem9120 : term0.
Proof. exact (fun p : Prop => @lem9115 p). Qed.
