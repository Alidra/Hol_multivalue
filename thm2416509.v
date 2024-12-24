Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2416509_term_abbrevs.
Require Import thm1031360_spec.
Require Import thm2414414_spec.
Lemma lem2416506 {A : Type'} (m : A) (r0 : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (r1 : A) (add : type1400 A) (y : A) (z : A) (mul : type1400 A) (pwr : type1423 A) (x : A) (q : nat) : term0 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (fun h0 : term1 A r0 add r1 mul pwr => @lem1031360 A m ly rx lx ry b a c d p y z x q r0 add r1 mul pwr h0). Qed.
Lemma lem2416507 (m : int) (r0 : int) (ly : int) (rx : int) (lx : int) (ry : int) (b : int) (a : int) (c : int) (d : int) (p : nat) (r1 : int) (add : type1551) (y : int) (z : int) (mul : type1551) (pwr : type1553) (x : int) (q : nat) : term2 m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (@lem2416506 int m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q). Qed.
Lemma lem2416508 (m : int) (ly : int) (rx : int) (lx : int) (ry : int) (b : int) (a : int) (c : int) (d : int) (p : nat) (y : int) (z : int) (x : int) (q : nat) : term3 m ly rx lx ry b a c d p y z x q.
Proof. exact (@lem2416507 m term4 ly rx lx ry b a c d p term5 int_add y z int_mul int_pow x q). Qed.
Lemma lem2416509 (m : int) (ly : int) (rx : int) (lx : int) (ry : int) (b : int) (a : int) (c : int) (d : int) (p : nat) (y : int) (z : int) (x : int) (q : nat) : term6 m ly rx lx ry b a c d p y z x q.
Proof. exact (@lem2416508 m ly rx lx ry b a c d p y z x q (@lem2414414)). Qed.
