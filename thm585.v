Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm585_term_abbrevs.
Lemma lem557 (p : Prop) (q : Prop) (r : Prop) (h1 : term0 p q r) : term0 p q r.
Proof. exact (h1). Qed.
Lemma lem559 (p : Prop) (q : Prop) (r : Prop) (h1 : term0 p q r) : p /\ q.
Proof. exact (proj1 (@lem557 p q r h1)). Qed.
Lemma lem561 (p : Prop) (q : Prop) (r : Prop) (h1 : term0 p q r) : p.
Proof. exact (proj1 (@lem559 p q r h1)). Qed.
Lemma lem563 (p : Prop) (q : Prop) (r : Prop) (h1 : term0 p q r) : p /\ q.
Proof. exact (proj1 (@lem557 p q r h1)). Qed.
Lemma lem564 (p : Prop) (q : Prop) (r : Prop) (h1 : term0 p q r) : q.
Proof. exact (proj2 (@lem563 p q r h1)). Qed.
Lemma lem566 (p : Prop) (q : Prop) (r : Prop) (h1 : term0 p q r) : r.
Proof. exact (proj2 (@lem557 p q r h1)). Qed.
Lemma lem568 (p : Prop) (q : Prop) (r : Prop) (h1 : term0 p q r) : q /\ r.
Proof. exact (conj (@lem564 p q r h1) (@lem566 p q r h1)). Qed.
Lemma lem569 (p : Prop) (q : Prop) (r : Prop) (h1 : term0 p q r) : term1 p q r.
Proof. exact (conj (@lem561 p q r h1) (@lem568 p q r h1)). Qed.
Lemma lem570 (p : Prop) (q : Prop) (r : Prop) : term2 p q r.
Proof. exact (fun h0 : term0 p q r => @lem569 p q r h0). Qed.
Lemma lem571 (p : Prop) (q : Prop) (r : Prop) (h1 : term1 p q r) : term1 p q r.
Proof. exact (h1). Qed.
Lemma lem573 (p : Prop) (q : Prop) (r : Prop) (h1 : term1 p q r) : p.
Proof. exact (proj1 (@lem571 p q r h1)). Qed.
Lemma lem574 (p : Prop) (q : Prop) (r : Prop) (h1 : term1 p q r) : q /\ r.
Proof. exact (proj2 (@lem571 p q r h1)). Qed.
Lemma lem577 (p : Prop) (q : Prop) (r : Prop) (h1 : term1 p q r) : q.
Proof. exact (proj1 (@lem574 p q r h1)). Qed.
Lemma lem578 (p : Prop) (q : Prop) (r : Prop) (h1 : term1 p q r) : p /\ q.
Proof. exact (conj (@lem573 p q r h1) (@lem577 p q r h1)). Qed.
Lemma lem579 (p : Prop) (q : Prop) (r : Prop) (h1 : term1 p q r) : q /\ r.
Proof. exact (proj2 (@lem571 p q r h1)). Qed.
Lemma lem581 (p : Prop) (q : Prop) (r : Prop) (h1 : term1 p q r) : r.
Proof. exact (proj2 (@lem579 p q r h1)). Qed.
Lemma lem583 (p : Prop) (q : Prop) (r : Prop) (h1 : term1 p q r) : term0 p q r.
Proof. exact (conj (@lem578 p q r h1) (@lem581 p q r h1)). Qed.
Lemma lem584 (p : Prop) (q : Prop) (r : Prop) : term3 p q r.
Proof. exact (fun h0 : term1 p q r => @lem583 p q r h0). Qed.
Lemma lem585 (p : Prop) (q : Prop) (r : Prop) : term4 p q r.
Proof. exact (conj (@lem570 p q r) (@lem584 p q r)). Qed.
