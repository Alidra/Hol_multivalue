Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1337536_term_abbrevs.
Lemma lem1337532 (m : nat) (h1 : (real_of_num m) = (term0 m)) : (real_of_num m) = (term0 m).
Proof. exact (h1). Qed.
Lemma lem1337533 (m : nat) (h1 : (real_of_num m) = (term0 m)) : (term0 m) = (real_of_num m).
Proof. exact (SYM (@lem1337532 m h1)). Qed.
Lemma lem1337534 (m : nat) (h1 : (term0 m) = (real_of_num m)) : (term0 m) = (real_of_num m).
Proof. exact (h1). Qed.
Lemma lem1337535 (m : nat) (h1 : (term0 m) = (real_of_num m)) : (real_of_num m) = (term0 m).
Proof. exact (SYM (@lem1337534 m h1)). Qed.
Lemma lem1337536 (m : nat) : ((real_of_num m) = (term0 m)) = ((term0 m) = (real_of_num m)).
Proof. exact (prop_ext (fun h1 : (real_of_num m) = (term0 m) => @lem1337533 m h1) (fun h1 : (term0 m) = (real_of_num m) => @lem1337535 m h1)). Qed.
