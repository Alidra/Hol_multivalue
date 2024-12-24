Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SND_DEF_term_abbrevs.
Lemma lem45473 {A B : Type'} : (@snd A B) = (term0 A B).
Proof. exact (@SND_def A B). Qed.
Lemma lem45474 {A B : Type'} (p : prod A B) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem45475 {A B : Type'} (p : prod A B) : (@snd A B p) = (term1 A B p).
Proof. exact (MK_COMB (@lem45473 A B) (@lem45474 A B p)). Qed.
Lemma lem45476 {A B : Type'} (p : prod A B) : (term1 A B p) = (term2 A B p).
Proof. exact (eq_refl (term1 A B p)). Qed.
Lemma lem45477 {A B : Type'} (p : prod A B) : (@snd A B p) = (term2 A B p).
Proof. exact (TRANS (@lem45475 A B p) (@lem45476 A B p)). Qed.
Lemma lem45478 {A B : Type'} : term3 A B.
Proof. exact (fun p : prod A B => @lem45477 A B p). Qed.
