Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259719_term_abbrevs.
Require Import thm1259660_spec.
Lemma lem1259706 (m : nat) (n : nat) : term0 m n.
Proof. exact (fun p : nat => @lem1259660 m n p). Qed.
Lemma lem1259711 (m : nat) : term1 m.
Proof. exact (fun n : nat => @lem1259706 m n). Qed.
Lemma lem1259719 : term2.
Proof. exact (fun m : nat => @lem1259711 m). Qed.
