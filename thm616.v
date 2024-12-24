Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm616_term_abbrevs.
Lemma lem588 (p : Prop) (q : Prop) (r : Prop) (h1 : term0 p q r) : term0 p q r.
Proof. exact (h1). Qed.
Lemma lem589 (p : Prop) (q : Prop) (r : Prop) (h1 : term0 p q r) : q /\ r.
Proof. exact (proj2 (@lem588 p q r h1)). Qed.
Lemma lem592 (p : Prop) (q : Prop) (r : Prop) (h1 : term0 p q r) : q.
Proof. exact (proj1 (@lem589 p q r h1)). Qed.
Lemma lem594 (p : Prop) (q : Prop) (r : Prop) (h1 : term0 p q r) : p.
Proof. exact (proj1 (@lem588 p q r h1)). Qed.
Lemma lem595 (p : Prop) (q : Prop) (r : Prop) (h1 : term0 p q r) : q /\ r.
Proof. exact (proj2 (@lem588 p q r h1)). Qed.
Lemma lem597 (p : Prop) (q : Prop) (r : Prop) (h1 : term0 p q r) : r.
Proof. exact (proj2 (@lem595 p q r h1)). Qed.
Lemma lem599 (p : Prop) (q : Prop) (r : Prop) (h1 : term0 p q r) : p /\ r.
Proof. exact (conj (@lem594 p q r h1) (@lem597 p q r h1)). Qed.
Lemma lem600 (p : Prop) (q : Prop) (r : Prop) (h1 : term0 p q r) : term0 q p r.
Proof. exact (conj (@lem592 p q r h1) (@lem599 p q r h1)). Qed.
Lemma lem601 (q : Prop) (p : Prop) (r : Prop) : term1 q p r.
Proof. exact (fun h0 : term0 p q r => @lem600 p q r h0). Qed.
Lemma lem602 (q : Prop) (p : Prop) (r : Prop) (h1 : term0 q p r) : term0 q p r.
Proof. exact (h1). Qed.
Lemma lem603 (q : Prop) (p : Prop) (r : Prop) (h1 : term0 q p r) : p /\ r.
Proof. exact (proj2 (@lem602 q p r h1)). Qed.
Lemma lem606 (q : Prop) (p : Prop) (r : Prop) (h1 : term0 q p r) : p.
Proof. exact (proj1 (@lem603 q p r h1)). Qed.
Lemma lem608 (q : Prop) (p : Prop) (r : Prop) (h1 : term0 q p r) : q.
Proof. exact (proj1 (@lem602 q p r h1)). Qed.
Lemma lem609 (q : Prop) (p : Prop) (r : Prop) (h1 : term0 q p r) : p /\ r.
Proof. exact (proj2 (@lem602 q p r h1)). Qed.
Lemma lem611 (q : Prop) (p : Prop) (r : Prop) (h1 : term0 q p r) : r.
Proof. exact (proj2 (@lem609 q p r h1)). Qed.
Lemma lem613 (q : Prop) (p : Prop) (r : Prop) (h1 : term0 q p r) : q /\ r.
Proof. exact (conj (@lem608 q p r h1) (@lem611 q p r h1)). Qed.
Lemma lem614 (q : Prop) (p : Prop) (r : Prop) (h1 : term0 q p r) : term0 p q r.
Proof. exact (conj (@lem606 q p r h1) (@lem613 q p r h1)). Qed.
Lemma lem615 (p : Prop) (q : Prop) (r : Prop) : term1 p q r.
Proof. exact (fun h0 : term0 q p r => @lem614 q p r h0). Qed.
Lemma lem616 (p : Prop) (q : Prop) (r : Prop) : term2 p q r.
Proof. exact (conj (@lem601 q p r) (@lem615 p q r)). Qed.
