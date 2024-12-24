Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm821_term_abbrevs.
Lemma lem807 (p : Prop) (q : Prop) (h1 : term0 p q) : term0 p q.
Proof. exact (h1). Qed.
Lemma lem808 (p : Prop) (h1 : p) : p.
Proof. exact (h1). Qed.
Lemma lem809 (p : Prop) (q : Prop) (h1 : p \/ q) : p \/ q.
Proof. exact (h1). Qed.
Lemma lem810 (q : Prop) (p : Prop) (h1 : p) : p \/ q.
Proof. exact (or_intro1 (@lem808 p h1) q). Qed.
Lemma lem811 (p : Prop) (q : Prop) (h1 : term0 p q) : p \/ q.
Proof. exact (or_elim (@lem807 p q h1) (fun h0 : p => @lem810 q p h0) (fun h0 : p \/ q => @lem809 p q h0)). Qed.
Lemma lem812 (p : Prop) (q : Prop) : term1 p q.
Proof. exact (fun h0 : term0 p q => @lem811 p q h0). Qed.
Lemma lem813 (p : Prop) (q : Prop) (h1 : p \/ q) : p \/ q.
Proof. exact (h1). Qed.
Lemma lem814 (p : Prop) (h1 : p) : p.
Proof. exact (h1). Qed.
Lemma lem815 (q : Prop) (h1 : q) : q.
Proof. exact (h1). Qed.
Lemma lem816 (q : Prop) (p : Prop) (h1 : p) : term0 p q.
Proof. exact (or_intro1 (@lem814 p h1) (p \/ q)). Qed.
Lemma lem817 (p : Prop) (q : Prop) (h1 : q) : p \/ q.
Proof. exact (or_intro2 p (@lem815 q h1)). Qed.
Lemma lem818 (p : Prop) (q : Prop) (h1 : q) : term0 p q.
Proof. exact (or_intro2 p (@lem817 p q h1)). Qed.
Lemma lem819 (p : Prop) (q : Prop) (h1 : p \/ q) : term0 p q.
Proof. exact (or_elim (@lem813 p q h1) (fun h0 : p => @lem816 q p h0) (fun h0 : q => @lem818 p q h0)). Qed.
Lemma lem820 (p : Prop) (q : Prop) : term2 p q.
Proof. exact (fun h0 : p \/ q => @lem819 p q h0). Qed.
Lemma lem821 (p : Prop) (q : Prop) : term3 p q.
Proof. exact (conj (@lem812 p q) (@lem820 p q)). Qed.
