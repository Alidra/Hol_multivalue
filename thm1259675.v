Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259675_term_abbrevs.
Require Import thm1259488_spec.
Lemma lem1259665 (m : nat) (p : nat) (n : nat) : term0 m p n.
Proof. exact (fun q : nat => @lem1259488 m p n q). Qed.
Lemma lem1259670 (m : nat) (n : nat) : term1 m n.
Proof. exact (fun p : nat => @lem1259665 m p n). Qed.
Lemma lem1259675 (m : nat) : term2 m.
Proof. exact (fun n : nat => @lem1259670 m n). Qed.
