Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm554_term_abbrevs.
Lemma lem540 (p : Prop) (q : Prop) (h1 : p /\ q) : p /\ q.
Proof. exact (h1). Qed.
Lemma lem541 (p : Prop) (q : Prop) (h1 : p /\ q) : q.
Proof. exact (proj2 (@lem540 p q h1)). Qed.
Lemma lem544 (p : Prop) (q : Prop) (h1 : p /\ q) : p.
Proof. exact (proj1 (@lem540 p q h1)). Qed.
Lemma lem545 (p : Prop) (q : Prop) (h1 : p /\ q) : q /\ p.
Proof. exact (conj (@lem541 p q h1) (@lem544 p q h1)). Qed.
Lemma lem546 (q : Prop) (p : Prop) : term0 q p.
Proof. exact (fun h0 : p /\ q => @lem545 p q h0). Qed.
Lemma lem547 (q : Prop) (p : Prop) (h1 : q /\ p) : q /\ p.
Proof. exact (h1). Qed.
Lemma lem548 (q : Prop) (p : Prop) (h1 : q /\ p) : p.
Proof. exact (proj2 (@lem547 q p h1)). Qed.
Lemma lem551 (q : Prop) (p : Prop) (h1 : q /\ p) : q.
Proof. exact (proj1 (@lem547 q p h1)). Qed.
Lemma lem552 (q : Prop) (p : Prop) (h1 : q /\ p) : p /\ q.
Proof. exact (conj (@lem548 q p h1) (@lem551 q p h1)). Qed.
Lemma lem553 (p : Prop) (q : Prop) : term0 p q.
Proof. exact (fun h0 : q /\ p => @lem552 q p h0). Qed.
Lemma lem554 (p : Prop) (q : Prop) : term1 p q.
Proof. exact (conj (@lem546 q p) (@lem553 p q)). Qed.
