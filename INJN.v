Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INJN_term_abbrevs.
Lemma lem1055363 {A : Type'} : (@INJN A) = (term0 A).
Proof. exact (@INJN_def A). Qed.
Lemma lem1055364 (_17374 : nat) : _17374 = _17374.
Proof. exact (eq_refl _17374). Qed.
Lemma lem1055365 {A : Type'} (_17374 : nat) : (@INJN A _17374) = (term1 A _17374).
Proof. exact (MK_COMB (@lem1055363 A) (@lem1055364 _17374)). Qed.
Lemma lem1055366 {A : Type'} (_17374 : nat) : (term1 A _17374) = (term2 A _17374).
Proof. exact (eq_refl (term1 A _17374)). Qed.
Lemma lem1055367 {A : Type'} (_17374 : nat) : (@INJN A _17374) = (term2 A _17374).
Proof. exact (TRANS (@lem1055365 A _17374) (@lem1055366 A _17374)). Qed.
Lemma lem1055368 {A : Type'} : term3 A.
Proof. exact (fun _17374 : nat => @lem1055367 A _17374). Qed.
Lemma lem1055369 {A : Type'} (_17374 : nat) : term4 A _17374.
Proof. exact (@lem1055368 A _17374). Qed.
Lemma lem1055370 {A : Type'} (_17374 : nat) : (term4 A _17374) = ((@INJN A _17374) = (term2 A _17374)).
Proof. exact (eq_refl (term4 A _17374)). Qed.
Lemma lem1055371 {A : Type'} (_17374 : nat) : (@INJN A _17374) = (term2 A _17374).
Proof. exact (EQ_MP (@lem1055370 A _17374) (@lem1055369 A _17374)). Qed.
Lemma lem1055401 {A : Type'} (m : nat) : (@INJN A m) = (term2 A m).
Proof. exact (@lem1055371 A m). Qed.
Lemma lem1055402 {A : Type'} : term3 A.
Proof. exact (fun m : nat => @lem1055401 A m). Qed.
