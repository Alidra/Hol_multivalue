Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm51_term_abbrevs.
Lemma lem44 (p : Prop) (h1 : p) : p.
Proof. exact (h1). Qed.
Lemma lem45 (p : Prop) (q : Prop) (h1 : p -> q) : p -> q.
Proof. exact (h1). Qed.
Lemma lem46 (p : Prop) (q : Prop) (h1 : p) (h2 : p -> q) : q.
Proof. exact (@lem45 p q h2 (@lem44 p h1)). Qed.
Lemma lem47 (q : Prop) (r : Prop) (h1 : q -> r) : q -> r.
Proof. exact (h1). Qed.
Lemma lem48 (p : Prop) (q : Prop) (r : Prop) (h1 : p) (h2 : p -> q) (h3 : q -> r) : r.
Proof. exact (@lem47 q r h3 (@lem46 p q h1 h2)). Qed.
Lemma lem49 (p : Prop) (q : Prop) (r : Prop) (h1 : p -> q) (h2 : q -> r) : p -> r.
Proof. exact (fun h0 : p => @lem48 p q r h0 h1 h2). Qed.
Lemma lem50 (r : Prop) (p : Prop) (q : Prop) (h1 : p -> q) : term0 q p r.
Proof. exact (fun h0 : q -> r => @lem49 p q r h1 h0). Qed.
Lemma lem51 (q : Prop) (p : Prop) (r : Prop) : term1 q p r.
Proof. exact (fun h0 : p -> q => @lem50 r p q h0). Qed.
