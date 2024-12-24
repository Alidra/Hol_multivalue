Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm626_term_abbrevs.
Lemma lem619 (p : Prop) (h1 : p /\ p) : p /\ p.
Proof. exact (h1). Qed.
Lemma lem620 (p : Prop) (h1 : p /\ p) : p.
Proof. exact (proj2 (@lem619 p h1)). Qed.
Lemma lem622 (p : Prop) : term0 p.
Proof. exact (fun h0 : p /\ p => @lem620 p h0). Qed.
Lemma lem623 (p : Prop) (h1 : p) : p.
Proof. exact (h1). Qed.
Lemma lem624 (p : Prop) (h1 : p) : p /\ p.
Proof. exact (conj (@lem623 p h1) (@lem623 p h1)). Qed.
Lemma lem625 (p : Prop) : term1 p.
Proof. exact (fun h0 : p => @lem624 p h0). Qed.
Lemma lem626 (p : Prop) : term2 p.
Proof. exact (conj (@lem622 p) (@lem625 p)). Qed.
