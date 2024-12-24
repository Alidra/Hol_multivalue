Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm735_term_abbrevs.
Lemma lem721 (p : Prop) (q : Prop) (h1 : p \/ q) : p \/ q.
Proof. exact (h1). Qed.
Lemma lem722 (p : Prop) (h1 : p) : p.
Proof. exact (h1). Qed.
Lemma lem723 (q : Prop) (h1 : q) : q.
Proof. exact (h1). Qed.
Lemma lem724 (q : Prop) (p : Prop) (h1 : p) : q \/ p.
Proof. exact (or_intro2 q (@lem722 p h1)). Qed.
Lemma lem725 (p : Prop) (q : Prop) (h1 : q) : q \/ p.
Proof. exact (or_intro1 (@lem723 q h1) p). Qed.
Lemma lem726 (p : Prop) (q : Prop) (h1 : p \/ q) : q \/ p.
Proof. exact (or_elim (@lem721 p q h1) (fun h0 : p => @lem724 q p h0) (fun h0 : q => @lem725 p q h0)). Qed.
Lemma lem727 (q : Prop) (p : Prop) : term0 q p.
Proof. exact (fun h0 : p \/ q => @lem726 p q h0). Qed.
Lemma lem728 (q : Prop) (p : Prop) (h1 : q \/ p) : q \/ p.
Proof. exact (h1). Qed.
Lemma lem729 (q : Prop) (h1 : q) : q.
Proof. exact (h1). Qed.
Lemma lem730 (p : Prop) (h1 : p) : p.
Proof. exact (h1). Qed.
Lemma lem731 (p : Prop) (q : Prop) (h1 : q) : p \/ q.
Proof. exact (or_intro2 p (@lem729 q h1)). Qed.
Lemma lem732 (q : Prop) (p : Prop) (h1 : p) : p \/ q.
Proof. exact (or_intro1 (@lem730 p h1) q). Qed.
Lemma lem733 (q : Prop) (p : Prop) (h1 : q \/ p) : p \/ q.
Proof. exact (or_elim (@lem728 q p h1) (fun h0 : q => @lem731 p q h0) (fun h0 : p => @lem732 q p h0)). Qed.
Lemma lem734 (p : Prop) (q : Prop) : term0 p q.
Proof. exact (fun h0 : q \/ p => @lem733 q p h0). Qed.
Lemma lem735 (p : Prop) (q : Prop) : term1 p q.
Proof. exact (conj (@lem727 q p) (@lem734 p q)). Qed.
