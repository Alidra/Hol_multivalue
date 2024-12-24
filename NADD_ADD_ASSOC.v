Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_ADD_ASSOC_term_abbrevs.
Require Import ADD_ASSOC_spec.
Require Import NADD_ADD_spec.
Require Import NADD_EQ_REFL_spec.
Require Import nadd_add_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm7_spec.
Lemma lem1274477 (x : nadd) : term0 x.
Proof. exact (@lem1267990 x). Qed.
Lemma lem1274478 (x : nadd) : (term0 x) = (nadd_eq x x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1274479 (x : nadd) : nadd_eq x x.
Proof. exact (EQ_MP (@lem1274478 x) (@lem1274477 x)). Qed.
Lemma lem1274480 (x : nadd) : (nadd_eq x x) = ((nadd_eq x x) = True).
Proof. exact (@lem7 (nadd_eq x x)). Qed.
Lemma lem1274482 (m : nat) : term1 m.
Proof. exact (@lem77960 m). Qed.
Lemma lem1274483 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem1274484 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem1274483 m) (@lem1274482 m)). Qed.
Lemma lem1274485 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem1274484 m n). Qed.
Lemma lem1274486 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem1274487 (m : nat) (n : nat) : term4 m n.
Proof. exact (EQ_MP (@lem1274486 m n) (@lem1274485 m n)). Qed.
Lemma lem1274488 (m : nat) (n : nat) (p : nat) : term5 m n p.
Proof. exact (@lem1274487 m n p). Qed.
Lemma lem1274489 (m : nat) (n : nat) (p : nat) : (term5 m n p) = ((term6 m n p) = (term7 m n p)).
Proof. exact (eq_refl (term5 m n p)). Qed.
Lemma lem1274491 (x : nadd) : term8 x.
Proof. exact (@lem1274104 x). Qed.
Lemma lem1274492 (x : nadd) : (term8 x) = (term9 x).
Proof. exact (eq_refl (term8 x)). Qed.
Lemma lem1274493 (x : nadd) : term9 x.
Proof. exact (EQ_MP (@lem1274492 x) (@lem1274491 x)). Qed.
Lemma lem1274494 (x : nadd) (y : nadd) : term10 x y.
Proof. exact (@lem1274493 x y). Qed.
Lemma lem1274495 (x : nadd) (y : nadd) : (term10 x y) = ((term11 x y) = (term12 x y)).
Proof. exact (eq_refl (term10 x y)). Qed.
Lemma lem1274497 (x : nadd) : term13 x.
Proof. exact (@lem1273759 x). Qed.
Lemma lem1274498 (x : nadd) : (term13 x) = (term14 x).
Proof. exact (eq_refl (term13 x)). Qed.
Lemma lem1274499 (x : nadd) : term14 x.
Proof. exact (EQ_MP (@lem1274498 x) (@lem1274497 x)). Qed.
Lemma lem1274500 (x : nadd) (y : nadd) : term15 x y.
Proof. exact (@lem1274499 x y). Qed.
Lemma lem1274501 (x : nadd) (y : nadd) : (term15 x y) = ((nadd_add x y) = (term16 x y)).
Proof. exact (eq_refl (term15 x y)). Qed.
Lemma lem1274504 (x : nadd) (y : nadd) : (nadd_add x y) = (term16 x y).
Proof. exact (EQ_MP (@lem1274501 x y) (@lem1274500 x y)). Qed.
Lemma lem1274505 (x : nadd) (y : nadd) (z : nadd) : (term17 x y z) = (term18 x y z).
Proof. exact (@lem1274504 x (nadd_add y z)). Qed.
Lemma lem1274506 : nadd_eq = nadd_eq.
Proof. exact (eq_refl nadd_eq). Qed.
Lemma lem1274507 (x : nadd) (y : nadd) (z : nadd) : (term19 x y z) = (term20 x y z).
Proof. exact (MK_COMB (@lem1274506) (@lem1274505 x y z)). Qed.
Lemma lem1274509 (x : nadd) (y : nadd) : (nadd_add x y) = (term16 x y).
Proof. exact (EQ_MP (@lem1274501 x y) (@lem1274500 x y)). Qed.
Lemma lem1274510 (x : nadd) (y : nadd) (z : nadd) : (term21 x y z) = (term22 x y z).
Proof. exact (@lem1274509 (nadd_add x y) z). Qed.
Lemma lem1274511 (x : nadd) (y : nadd) (z : nadd) : (term23 x y z) = (term24 x y z).
Proof. exact (MK_COMB (@lem1274507 x y z) (@lem1274510 x y z)). Qed.
Lemma lem1274512 (x : nadd) (y : nadd) (z : nadd) : (term24 x y z) = (term23 x y z).
Proof. exact (SYM (@lem1274511 x y z)). Qed.
Lemma lem1274516 (x : nadd) (y : nadd) : (term11 x y) = (term12 x y).
Proof. exact (EQ_MP (@lem1274495 x y) (@lem1274494 x y)). Qed.
Lemma lem1274517 (y : nadd) (z : nadd) : (term11 y z) = (term12 y z).
Proof. exact (@lem1274516 y z). Qed.
Lemma lem1274518 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1274519 (y : nadd) (z : nadd) (n : nat) : (term25 y z n) = (term26 y z n).
Proof. exact (MK_COMB (@lem1274517 y z) (@lem1274518 n)). Qed.
Lemma lem1274521 {A B : Type'} (f : A -> B) (y : A) : (term27 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1274522 (f : nat -> nat) (y : nat) : (term28 f y) = (f y).
Proof. exact (@lem1274521 nat nat f y). Qed.
Lemma lem1274523 (y : nadd) (z : nadd) (n : nat) : (term29 y z n) = (term26 y z n).
Proof. exact (@lem1274522 (term12 y z) n). Qed.
Lemma lem1274524 (y : nadd) (z : nadd) (n : nat) : (term26 y z n) = (term30 y z n).
Proof. exact (eq_refl (term26 y z n)). Qed.
Lemma lem1274525 (y : nadd) (z : nadd) : (term31 y z) = (term12 y z).
Proof. exact (fun_ext (fun n : nat => @lem1274524 y z n)). Qed.
Lemma lem1274526 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1274527 (y : nadd) (z : nadd) (n : nat) : (term29 y z n) = (term26 y z n).
Proof. exact (MK_COMB (@lem1274525 y z) (@lem1274526 n)). Qed.
Lemma lem1274528 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1274529 (y : nadd) (z : nadd) (n : nat) : (term32 y z n) = (term33 y z n).
Proof. exact (MK_COMB (@lem1274528) (@lem1274527 y z n)). Qed.
Lemma lem1274530 (y : nadd) (z : nadd) (n : nat) : (term26 y z n) = (term30 y z n).
Proof. exact (eq_refl (term26 y z n)). Qed.
Lemma lem1274531 (y : nadd) (z : nadd) (n : nat) : ((term29 y z n) = (term26 y z n)) = ((term26 y z n) = (term30 y z n)).
Proof. exact (MK_COMB (@lem1274529 y z n) (@lem1274530 y z n)). Qed.
Lemma lem1274532 (y : nadd) (z : nadd) (n : nat) : (term26 y z n) = (term30 y z n).
Proof. exact (EQ_MP (@lem1274531 y z n) (@lem1274523 y z n)). Qed.
Lemma lem1274533 (y : nadd) (z : nadd) (n : nat) : (term25 y z n) = (term30 y z n).
Proof. exact (TRANS (@lem1274519 y z n) (@lem1274532 y z n)). Qed.
Lemma lem1274534 (x : nadd) (n : nat) : (term34 x n) = (term34 x n).
Proof. exact (eq_refl (term34 x n)). Qed.
Lemma lem1274535 (x : nadd) (y : nadd) (z : nadd) (n : nat) : (term35 x y z n) = (term36 x y z n).
Proof. exact (MK_COMB (@lem1274534 x n) (@lem1274533 y z n)). Qed.
Lemma lem1274537 (m : nat) (n : nat) (p : nat) : (term6 m n p) = (term7 m n p).
Proof. exact (EQ_MP (@lem1274489 m n p) (@lem1274488 m n p)). Qed.
Lemma lem1274538 (x : nadd) (y : nadd) (z : nadd) (n : nat) : (term36 x y z n) = (term37 x y z n).
Proof. exact (@lem1274537 (dest_nadd x n) (dest_nadd y n) (dest_nadd z n)). Qed.
Lemma lem1274539 (x : nadd) (y : nadd) (z : nadd) (n : nat) : (term35 x y z n) = (term37 x y z n).
Proof. exact (TRANS (@lem1274535 x y z n) (@lem1274538 x y z n)). Qed.
Lemma lem1274540 (x : nadd) (y : nadd) (z : nadd) : (term38 x y z) = (term39 x y z).
Proof. exact (fun_ext (fun n : nat => @lem1274539 x y z n)). Qed.
Lemma lem1274541 : mk_nadd = mk_nadd.
Proof. exact (eq_refl mk_nadd). Qed.
Lemma lem1274542 (x : nadd) (y : nadd) (z : nadd) : (term18 x y z) = (term40 x y z).
Proof. exact (MK_COMB (@lem1274541) (@lem1274540 x y z)). Qed.
Lemma lem1274543 : nadd_eq = nadd_eq.
Proof. exact (eq_refl nadd_eq). Qed.
Lemma lem1274544 (x : nadd) (y : nadd) (z : nadd) : (term20 x y z) = (term41 x y z).
Proof. exact (MK_COMB (@lem1274543) (@lem1274542 x y z)). Qed.
Lemma lem1274546 (x : nadd) (y : nadd) : (term11 x y) = (term12 x y).
Proof. exact (EQ_MP (@lem1274495 x y) (@lem1274494 x y)). Qed.
Lemma lem1274547 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1274548 (x : nadd) (y : nadd) (n : nat) : (term25 x y n) = (term26 x y n).
Proof. exact (MK_COMB (@lem1274546 x y) (@lem1274547 n)). Qed.
Lemma lem1274550 {A B : Type'} (f : A -> B) (y : A) : (term27 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1274551 (f : nat -> nat) (y : nat) : (term28 f y) = (f y).
Proof. exact (@lem1274550 nat nat f y). Qed.
Lemma lem1274552 (x : nadd) (y : nadd) (n : nat) : (term29 x y n) = (term26 x y n).
Proof. exact (@lem1274551 (term12 x y) n). Qed.
Lemma lem1274553 (x : nadd) (y : nadd) (n : nat) : (term26 x y n) = (term30 x y n).
Proof. exact (eq_refl (term26 x y n)). Qed.
Lemma lem1274554 (x : nadd) (y : nadd) : (term31 x y) = (term12 x y).
Proof. exact (fun_ext (fun n : nat => @lem1274553 x y n)). Qed.
Lemma lem1274555 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1274556 (x : nadd) (y : nadd) (n : nat) : (term29 x y n) = (term26 x y n).
Proof. exact (MK_COMB (@lem1274554 x y) (@lem1274555 n)). Qed.
Lemma lem1274557 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1274558 (x : nadd) (y : nadd) (n : nat) : (term32 x y n) = (term33 x y n).
Proof. exact (MK_COMB (@lem1274557) (@lem1274556 x y n)). Qed.
Lemma lem1274559 (x : nadd) (y : nadd) (n : nat) : (term26 x y n) = (term30 x y n).
Proof. exact (eq_refl (term26 x y n)). Qed.
Lemma lem1274560 (x : nadd) (y : nadd) (n : nat) : ((term29 x y n) = (term26 x y n)) = ((term26 x y n) = (term30 x y n)).
Proof. exact (MK_COMB (@lem1274558 x y n) (@lem1274559 x y n)). Qed.
Lemma lem1274561 (x : nadd) (y : nadd) (n : nat) : (term26 x y n) = (term30 x y n).
Proof. exact (EQ_MP (@lem1274560 x y n) (@lem1274552 x y n)). Qed.
Lemma lem1274562 (x : nadd) (y : nadd) (n : nat) : (term25 x y n) = (term30 x y n).
Proof. exact (TRANS (@lem1274548 x y n) (@lem1274561 x y n)). Qed.
Lemma lem1274563 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1274564 (x : nadd) (y : nadd) (n : nat) : (term42 x y n) = (term43 x y n).
Proof. exact (MK_COMB (@lem1274563) (@lem1274562 x y n)). Qed.
Lemma lem1274565 (z : nadd) (n : nat) : (dest_nadd z n) = (dest_nadd z n).
Proof. exact (eq_refl (dest_nadd z n)). Qed.
Lemma lem1274566 (x : nadd) (y : nadd) (z : nadd) (n : nat) : (term44 x y z n) = (term37 x y z n).
Proof. exact (MK_COMB (@lem1274564 x y n) (@lem1274565 z n)). Qed.
Lemma lem1274567 (x : nadd) (y : nadd) (z : nadd) : (term45 x y z) = (term39 x y z).
Proof. exact (fun_ext (fun n : nat => @lem1274566 x y z n)). Qed.
Lemma lem1274568 : mk_nadd = mk_nadd.
Proof. exact (eq_refl mk_nadd). Qed.
Lemma lem1274569 (x : nadd) (y : nadd) (z : nadd) : (term22 x y z) = (term40 x y z).
Proof. exact (MK_COMB (@lem1274568) (@lem1274567 x y z)). Qed.
Lemma lem1274570 (x : nadd) (y : nadd) (z : nadd) : (term24 x y z) = (term46 x y z).
Proof. exact (MK_COMB (@lem1274544 x y z) (@lem1274569 x y z)). Qed.
Lemma lem1274572 (x : nadd) : (nadd_eq x x) = True.
Proof. exact (EQ_MP (@lem1274480 x) (@lem1274479 x)). Qed.
Lemma lem1274573 (x : nadd) (y : nadd) (z : nadd) : (term46 x y z) = True.
Proof. exact (@lem1274572 (term40 x y z)). Qed.
Lemma lem1274574 (x : nadd) (y : nadd) (z : nadd) : (term24 x y z) = True.
Proof. exact (TRANS (@lem1274570 x y z) (@lem1274573 x y z)). Qed.
Lemma lem1274575 (x : nadd) (y : nadd) (z : nadd) : True = (term24 x y z).
Proof. exact (SYM (@lem1274574 x y z)). Qed.
Lemma lem1274576 (x : nadd) (y : nadd) (z : nadd) : term24 x y z.
Proof. exact (EQ_MP (@lem1274575 x y z) (@lem0)). Qed.
Lemma lem1274577 (x : nadd) (y : nadd) (z : nadd) : term23 x y z.
Proof. exact (EQ_MP (@lem1274512 x y z) (@lem1274576 x y z)). Qed.
Lemma lem1274582 (x : nadd) (y : nadd) : term47 x y.
Proof. exact (fun z : nadd => @lem1274577 x y z). Qed.
Lemma lem1274587 (x : nadd) : term48 x.
Proof. exact (fun y : nadd => @lem1274582 x y). Qed.
Lemma lem1274592 : term49.
Proof. exact (fun x : nadd => @lem1274587 x). Qed.
