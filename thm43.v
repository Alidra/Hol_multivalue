Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm43_term_abbrevs.
Lemma lem38 (q : Prop) (h1 : q) : q.
Proof. exact (h1). Qed.
Lemma lem39 (p : Prop) (q : Prop) (h1 : p = q) : p = q.
Proof. exact (h1). Qed.
Lemma lem40 (p : Prop) (q : Prop) (h1 : p = q) : q = p.
Proof. exact (SYM (@lem39 p q h1)). Qed.
Lemma lem41 (p : Prop) (q : Prop) (h1 : q) (h2 : p = q) : p.
Proof. exact (EQ_MP (@lem40 p q h2) (@lem38 q h1)). Qed.
Lemma lem42 (p : Prop) (q : Prop) (h1 : p = q) : q -> p.
Proof. exact (fun h0 : q => @lem41 p q h0 h1). Qed.
Lemma lem43 (q : Prop) (p : Prop) : term0 q p.
Proof. exact (fun h0 : p = q => @lem42 p q h0). Qed.
