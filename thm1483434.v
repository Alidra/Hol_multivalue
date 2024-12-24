Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1483434_term_abbrevs.
Require Import REAL_POLY_CLAUSES_spec.
Require Import thm1031360_spec.
Lemma lem1483431 {A : Type'} (m : A) (r0 : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (r1 : A) (add : type1400 A) (y : A) (z : A) (mul : type1400 A) (pwr : type1423 A) (x : A) (q : nat) : term0 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (fun h0 : term1 A r0 add r1 mul pwr => @lem1031360 A m ly rx lx ry b a c d p y z x q r0 add r1 mul pwr h0). Qed.
Lemma lem1483432 (m : real) (r0 : real) (ly : real) (rx : real) (lx : real) (ry : real) (b : real) (a : real) (c : real) (d : real) (p : nat) (r1 : real) (add : type1627) (y : real) (z : real) (mul : type1627) (pwr : type1623) (x : real) (q : nat) : term2 m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (@lem1483431 real m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q). Qed.
Lemma lem1483433 (m : real) (ly : real) (rx : real) (lx : real) (ry : real) (b : real) (a : real) (c : real) (d : real) (p : nat) (y : real) (z : real) (x : real) (q : nat) : term3 m ly rx lx ry b a c d p y z x q.
Proof. exact (@lem1483432 m term4 ly rx lx ry b a c d p term5 real_add y z real_mul real_pow x q). Qed.
Lemma lem1483434 (m : real) (ly : real) (rx : real) (lx : real) (ry : real) (b : real) (a : real) (c : real) (d : real) (p : nat) (y : real) (z : real) (x : real) (q : nat) : term6 m ly rx lx ry b a c d p y z x q.
Proof. exact (@lem1483433 m ly rx lx ry b a c d p y z x q (@lem1384210)). Qed.
