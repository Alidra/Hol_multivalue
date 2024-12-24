Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1317787_term_abbrevs.
Lemma lem1317783 (m : nat) (h1 : (hreal_of_num m) = (term0 m)) : (hreal_of_num m) = (term0 m).
Proof. exact (h1). Qed.
Lemma lem1317784 (m : nat) (h1 : (hreal_of_num m) = (term0 m)) : (term0 m) = (hreal_of_num m).
Proof. exact (SYM (@lem1317783 m h1)). Qed.
Lemma lem1317785 (m : nat) (h1 : (term0 m) = (hreal_of_num m)) : (term0 m) = (hreal_of_num m).
Proof. exact (h1). Qed.
Lemma lem1317786 (m : nat) (h1 : (term0 m) = (hreal_of_num m)) : (hreal_of_num m) = (term0 m).
Proof. exact (SYM (@lem1317785 m h1)). Qed.
Lemma lem1317787 (m : nat) : ((hreal_of_num m) = (term0 m)) = ((term0 m) = (hreal_of_num m)).
Proof. exact (prop_ext (fun h1 : (hreal_of_num m) = (term0 m) => @lem1317784 m h1) (fun h1 : (term0 m) = (hreal_of_num m) => @lem1317786 m h1)). Qed.
