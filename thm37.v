Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm37_term_abbrevs.
Lemma lem33 (p : Prop) (h1 : p) : p.
Proof. exact (h1). Qed.
Lemma lem34 (p : Prop) (q : Prop) (h1 : p = q) : p = q.
Proof. exact (h1). Qed.
Lemma lem35 (p : Prop) (q : Prop) (h1 : p) (h2 : p = q) : q.
Proof. exact (EQ_MP (@lem34 p q h2) (@lem33 p h1)). Qed.
Lemma lem36 (p : Prop) (q : Prop) (h1 : p = q) : p -> q.
Proof. exact (fun h0 : p => @lem35 p q h0 h1). Qed.
Lemma lem37 (p : Prop) (q : Prop) : term0 p q.
Proof. exact (fun h0 : p = q => @lem36 p q h0). Qed.
