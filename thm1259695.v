Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259695_term_abbrevs.
Require Import thm1259569_spec.
Lemma lem1259685 (m : nat) (p : nat) (n : nat) : term0 m p n.
Proof. exact (fun q : nat => @lem1259569 m p n q). Qed.
Lemma lem1259690 (m : nat) (n : nat) : term1 m n.
Proof. exact (fun p : nat => @lem1259685 m p n). Qed.
Lemma lem1259695 (m : nat) : term2 m.
Proof. exact (fun n : nat => @lem1259690 m n). Qed.
