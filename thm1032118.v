Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1032118_term_abbrevs.
Require Import thm1032097_spec.
Lemma lem1032099 (p : nat) (y : nat) (z : nat) (x : nat) (q : nat) : term0 p y z x q.
Proof. exact (proj2 (@lem1032097 (@el nat) (@el nat) (@el nat) p y z x q)). Qed.
Lemma lem1032101 (p : nat) (y : nat) (z : nat) (x : nat) (q : nat) : term1 p y z x q.
Proof. exact (proj2 (@lem1032099 p y z x q)). Qed.
Lemma lem1032103 (p : nat) (y : nat) (z : nat) (x : nat) (q : nat) : term2 p y z x q.
Proof. exact (proj2 (@lem1032101 p y z x q)). Qed.
Lemma lem1032105 (p : nat) (y : nat) (z : nat) (x : nat) (q : nat) : term3 p y z x q.
Proof. exact (proj2 (@lem1032103 p y z x q)). Qed.
Lemma lem1032107 (p : nat) (y : nat) (z : nat) (x : nat) (q : nat) : term4 p y z x q.
Proof. exact (proj2 (@lem1032105 p y z x q)). Qed.
Lemma lem1032109 (p : nat) (y : nat) (z : nat) (x : nat) (q : nat) : term5 p y z x q.
Proof. exact (proj2 (@lem1032107 p y z x q)). Qed.
Lemma lem1032111 (y : nat) (z : nat) (x : nat) (q : nat) : term6 y z x q.
Proof. exact (proj2 (@lem1032109 (@el nat) y z x q)). Qed.
Lemma lem1032113 (y : nat) (z : nat) (x : nat) (q : nat) : term7 y z x q.
Proof. exact (proj2 (@lem1032111 y z x q)). Qed.
Lemma lem1032115 (y : nat) (z : nat) (x : nat) (q : nat) : term8 y z x q.
Proof. exact (proj2 (@lem1032113 y z x q)). Qed.
Lemma lem1032118 (y : nat) (x : nat) (z : nat) : (term9 x y z) = (term10 y x z).
Proof. exact (proj1 (@lem1032115 y z x (@el nat))). Qed.
