Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm129_term_abbrevs.
Lemma lem122 (p : Prop) (q : Prop) (r : Prop) (h1 : term0 p q r) : term0 p q r.
Proof. exact (h1). Qed.
Lemma lem123 (p : Prop) (q : Prop) (r : Prop) (h1 : term0 p q r) : q -> r.
Proof. exact (proj2 (@lem122 p q r h1)). Qed.
Lemma lem124 (p : Prop) (q : Prop) (r : Prop) (h1 : term0 p q r) : p.
Proof. exact (proj1 (@lem122 p q r h1)). Qed.
Lemma lem125 (p : Prop) (q : Prop) (h1 : p -> q) : p -> q.
Proof. exact (h1). Qed.
Lemma lem126 (r : Prop) (p : Prop) (q : Prop) (h1 : term0 p q r) (h2 : p -> q) : q.
Proof. exact (@lem125 p q h2 (@lem124 p q r h1)). Qed.
Lemma lem127 (r : Prop) (p : Prop) (q : Prop) (h1 : term0 p q r) (h2 : p -> q) : r.
Proof. exact (@lem123 p q r h1 (@lem126 r p q h1 h2)). Qed.
Lemma lem128 (p : Prop) (q : Prop) (r : Prop) (h1 : term0 p q r) : term1 p q r.
Proof. exact (fun h0 : p -> q => @lem127 r p q h1 h0). Qed.
Lemma lem129 (p : Prop) (q : Prop) (r : Prop) : term2 p q r.
Proof. exact (fun h0 : term0 p q r => @lem128 p q r h0). Qed.
