Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm643_term_abbrevs.
Lemma lem629 (p : Prop) (q : Prop) (h1 : term0 p q) : term0 p q.
Proof. exact (h1). Qed.
Lemma lem631 (p : Prop) (q : Prop) (h1 : term0 p q) : p.
Proof. exact (proj1 (@lem629 p q h1)). Qed.
Lemma lem632 (p : Prop) (q : Prop) (h1 : term0 p q) : p /\ q.
Proof. exact (proj2 (@lem629 p q h1)). Qed.
Lemma lem634 (p : Prop) (q : Prop) (h1 : term0 p q) : q.
Proof. exact (proj2 (@lem632 p q h1)). Qed.
Lemma lem636 (p : Prop) (q : Prop) (h1 : term0 p q) : p /\ q.
Proof. exact (conj (@lem631 p q h1) (@lem634 p q h1)). Qed.
Lemma lem637 (p : Prop) (q : Prop) : term1 p q.
Proof. exact (fun h0 : term0 p q => @lem636 p q h0). Qed.
Lemma lem638 (p : Prop) (q : Prop) (h1 : p /\ q) : p /\ q.
Proof. exact (h1). Qed.
Lemma lem640 (p : Prop) (q : Prop) (h1 : p /\ q) : p.
Proof. exact (proj1 (@lem638 p q h1)). Qed.
Lemma lem641 (p : Prop) (q : Prop) (h1 : p /\ q) : term0 p q.
Proof. exact (conj (@lem640 p q h1) (@lem638 p q h1)). Qed.
Lemma lem642 (p : Prop) (q : Prop) : term2 p q.
Proof. exact (fun h0 : p /\ q => @lem641 p q h0). Qed.
Lemma lem643 (p : Prop) (q : Prop) : term3 p q.
Proof. exact (conj (@lem637 p q) (@lem642 p q)). Qed.
