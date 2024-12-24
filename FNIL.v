Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FNIL_term_abbrevs.
Lemma lem1066514 {A : Type'} : (@FNIL A) = (term0 A).
Proof. exact (@FNIL_def A). Qed.
Lemma lem1066515 (_17461 : nat) : _17461 = _17461.
Proof. exact (eq_refl _17461). Qed.
Lemma lem1066516 {A : Type'} (_17461 : nat) : (@FNIL A _17461) = (term1 A _17461).
Proof. exact (MK_COMB (@lem1066514 A) (@lem1066515 _17461)). Qed.
Lemma lem1066517 {A : Type'} (_17461 : nat) : (term1 A _17461) = (term2 A).
Proof. exact (eq_refl (term1 A _17461)). Qed.
Lemma lem1066518 {A : Type'} (_17461 : nat) : (@FNIL A _17461) = (term2 A).
Proof. exact (TRANS (@lem1066516 A _17461) (@lem1066517 A _17461)). Qed.
Lemma lem1066519 {A : Type'} : term3 A.
Proof. exact (fun _17461 : nat => @lem1066518 A _17461). Qed.
Lemma lem1066520 {A : Type'} (_17461 : nat) : term4 A _17461.
Proof. exact (@lem1066519 A _17461). Qed.
Lemma lem1066521 {A : Type'} (_17461 : nat) : (term4 A _17461) = ((@FNIL A _17461) = (term2 A)).
Proof. exact (eq_refl (term4 A _17461)). Qed.
Lemma lem1066522 {A : Type'} (_17461 : nat) : (@FNIL A _17461) = (term2 A).
Proof. exact (EQ_MP (@lem1066521 A _17461) (@lem1066520 A _17461)). Qed.
Lemma lem1066552 {A : Type'} (n : nat) : (@FNIL A n) = (term2 A).
Proof. exact (@lem1066522 A n). Qed.
Lemma lem1066553 {A : Type'} : term3 A.
Proof. exact (fun n : nat => @lem1066552 A n). Qed.
