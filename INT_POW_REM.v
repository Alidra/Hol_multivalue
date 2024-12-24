Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_POW_REM_term_abbrevs.
Require Import INT_MUL_REM_spec.
Require Import INT_POW_spec.
Require Import INT_REM_REM_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Lemma lem2537473 (m : int) : term0 m.
Proof. exact (@lem2537472 m). Qed.
Lemma lem2537474 (m : int) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem2537475 (m : int) : term1 m.
Proof. exact (EQ_MP (@lem2537474 m) (@lem2537473 m)). Qed.
Lemma lem2537476 (m : int) (n : int) : term2 m n.
Proof. exact (@lem2537475 m n). Qed.
Lemma lem2537477 (m : int) (n : int) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem2537478 (m : int) (n : int) : term3 m n.
Proof. exact (EQ_MP (@lem2537477 m n) (@lem2537476 m n)). Qed.
Lemma lem2537479 (m : int) (n : int) (p : int) : term4 m n p.
Proof. exact (@lem2537478 m n p). Qed.
Lemma lem2537480 (m : int) (n : int) (p : int) : (term4 m n p) = ((term5 m n p) = (term6 m n p)).
Proof. exact (eq_refl (term4 m n p)). Qed.
Lemma lem2537482 (m : int) : term7 m.
Proof. exact (@lem2521244 m). Qed.
Lemma lem2537483 (m : int) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem2537484 (m : int) : term8 m.
Proof. exact (EQ_MP (@lem2537483 m) (@lem2537482 m)). Qed.
Lemma lem2537485 (m : int) (n : int) : term9 m n.
Proof. exact (@lem2537484 m n). Qed.
Lemma lem2537486 (m : int) (n : int) : (term9 m n) = ((term10 m n) = (rem m n)).
Proof. exact (eq_refl (term9 m n)). Qed.
Lemma lem2537491 (m : int) (n : int) (p : int) (h1 : (term5 m n p) = (term6 m n p)) : (term5 m n p) = (term6 m n p).
Proof. exact (h1). Qed.
Lemma lem2537492 (m : int) (n : int) (p : int) (h1 : (term5 m n p) = (term6 m n p)) : (term6 m n p) = (term5 m n p).
Proof. exact (SYM (@lem2537491 m n p h1)). Qed.
Lemma lem2537493 (m : int) (n : int) (p : int) (h1 : (term6 m n p) = (term5 m n p)) : (term6 m n p) = (term5 m n p).
Proof. exact (h1). Qed.
Lemma lem2537494 (m : int) (n : int) (p : int) (h1 : (term6 m n p) = (term5 m n p)) : (term5 m n p) = (term6 m n p).
Proof. exact (SYM (@lem2537493 m n p h1)). Qed.
Lemma lem2537495 (m : int) (n : int) (p : int) : ((term5 m n p) = (term6 m n p)) = ((term6 m n p) = (term5 m n p)).
Proof. exact (prop_ext (fun h1 : (term5 m n p) = (term6 m n p) => @lem2537492 m n p h1) (fun h1 : (term6 m n p) = (term5 m n p) => @lem2537494 m n p h1)). Qed.
Lemma lem2537496 (m : int) (n : int) : (term11 m n) = (term12 m n).
Proof. exact (fun_ext (fun p : int => @lem2537495 m n p)). Qed.
Lemma lem2537497 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2537498 (m : int) (n : int) : (term3 m n) = (term13 m n).
Proof. exact (MK_COMB (@lem2537497) (@lem2537496 m n)). Qed.
Lemma lem2537499 (m : int) : (term14 m) = (term15 m).
Proof. exact (fun_ext (fun n : int => @lem2537498 m n)). Qed.
Lemma lem2537500 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2537501 (m : int) : (term1 m) = (term16 m).
Proof. exact (MK_COMB (@lem2537500) (@lem2537499 m)). Qed.
Lemma lem2537502 : term17 = term18.
Proof. exact (fun_ext (fun m : int => @lem2537501 m)). Qed.
Lemma lem2537503 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2537504 : term19 = term20.
Proof. exact (MK_COMB (@lem2537503) (@lem2537502)). Qed.
Lemma lem2537505 : term20.
Proof. exact (EQ_MP (@lem2537504) (@lem2537472)). Qed.
Lemma lem2537506 (m : int) : term21 m.
Proof. exact (@lem2537505 m). Qed.
Lemma lem2537507 (m : int) : (term21 m) = (term16 m).
Proof. exact (eq_refl (term21 m)). Qed.
Lemma lem2537508 (m : int) : term16 m.
Proof. exact (EQ_MP (@lem2537507 m) (@lem2537506 m)). Qed.
Lemma lem2537509 (m : int) (n : int) : term22 m n.
Proof. exact (@lem2537508 m n). Qed.
Lemma lem2537510 (m : int) (n : int) : (term22 m n) = (term13 m n).
Proof. exact (eq_refl (term22 m n)). Qed.
Lemma lem2537511 (m : int) (n : int) : term13 m n.
Proof. exact (EQ_MP (@lem2537510 m n) (@lem2537509 m n)). Qed.
Lemma lem2537512 (m : int) (n : int) (p : int) : term23 m n p.
Proof. exact (@lem2537511 m n p). Qed.
Lemma lem2537513 (m : int) (n : int) (p : int) : (term23 m n p) = ((term6 m n p) = (term5 m n p)).
Proof. exact (eq_refl (term23 m n p)). Qed.
Lemma lem2537515 (x : int) : term24 x.
Proof. exact (proj2 (@lem2318057 x)). Qed.
Lemma lem2537516 (x : int) (n : nat) : term25 x n.
Proof. exact (@lem2537515 x n). Qed.
Lemma lem2537517 (x : int) (n : nat) : (term25 x n) = ((term26 x n) = (term27 x n)).
Proof. exact (eq_refl (term25 x n)). Qed.
Lemma lem2537521 (P : nat -> Prop) : term28 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem2537522 (m : int) : term29 m.
Proof. exact (@lem2537521 (term30 m)). Qed.
Lemma lem2537523 (m : int) : (term31 m) = (term32 m).
Proof. exact (eq_refl (term31 m)). Qed.
Lemma lem2537524 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2537525 (m : int) : (term33 m) = (term34 m).
Proof. exact (MK_COMB (@lem2537524) (@lem2537523 m)). Qed.
Lemma lem2537526 (m : int) (n : nat) : (term35 m n) = (term36 m n).
Proof. exact (eq_refl (term35 m n)). Qed.
Lemma lem2537527 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2537528 (m : int) (n : nat) : (term37 m n) = (term38 m n).
Proof. exact (MK_COMB (@lem2537527) (@lem2537526 m n)). Qed.
Lemma lem2537529 (m : int) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (eq_refl (term39 m n)). Qed.
Lemma lem2537530 (m : int) (n : nat) : (term41 m n) = (term42 m n).
Proof. exact (MK_COMB (@lem2537528 m n) (@lem2537529 m n)). Qed.
Lemma lem2537531 (m : int) : (term43 m) = (term44 m).
Proof. exact (fun_ext (fun n : nat => @lem2537530 m n)). Qed.
Lemma lem2537532 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2537533 (m : int) : (term45 m) = (term46 m).
Proof. exact (MK_COMB (@lem2537532) (@lem2537531 m)). Qed.
Lemma lem2537534 (m : int) : (term47 m) = (term48 m).
Proof. exact (MK_COMB (@lem2537525 m) (@lem2537533 m)). Qed.
Lemma lem2537535 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2537536 (m : int) : (term49 m) = (term50 m).
Proof. exact (MK_COMB (@lem2537535) (@lem2537534 m)). Qed.
Lemma lem2537537 (m : int) (n : nat) : (term35 m n) = (term36 m n).
Proof. exact (eq_refl (term35 m n)). Qed.
Lemma lem2537538 (m : int) : (term51 m) = (term30 m).
Proof. exact (fun_ext (fun n : nat => @lem2537537 m n)). Qed.
Lemma lem2537539 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2537540 (m : int) : (term52 m) = (term53 m).
Proof. exact (MK_COMB (@lem2537539) (@lem2537538 m)). Qed.
Lemma lem2537541 (m : int) : (term29 m) = (term54 m).
Proof. exact (MK_COMB (@lem2537536 m) (@lem2537540 m)). Qed.
Lemma lem2537542 (m : int) : term54 m.
Proof. exact (EQ_MP (@lem2537541 m) (@lem2537522 m)). Qed.
Lemma lem2537543 (m : int) (n : nat) (h1 : term36 m n) : term36 m n.
Proof. exact (h1). Qed.
Lemma lem2537551 (x : int) : (term55 x) = term56.
Proof. exact (proj1 (@lem2318057 x)). Qed.
Lemma lem2537552 (m : int) (p : int) : (term57 m p) = term56.
Proof. exact (@lem2537551 (rem m p)). Qed.
Lemma lem2537553 : rem = rem.
Proof. exact (eq_refl rem). Qed.
Lemma lem2537554 (m : int) (p : int) : (term58 m p) = term59.
Proof. exact (MK_COMB (@lem2537553) (@lem2537552 m p)). Qed.
Lemma lem2537555 (p : int) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem2537556 (m : int) (p : int) : (term60 m p) = (term61 p).
Proof. exact (MK_COMB (@lem2537554 m p) (@lem2537555 p)). Qed.
Lemma lem2537557 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2537558 (m : int) (p : int) : (term62 m p) = (term63 p).
Proof. exact (MK_COMB (@lem2537557) (@lem2537556 m p)). Qed.
Lemma lem2537560 (x : int) : (term55 x) = term56.
Proof. exact (proj1 (@lem2318057 x)). Qed.
Lemma lem2537561 (m : int) : (term55 m) = term56.
Proof. exact (@lem2537560 m). Qed.
Lemma lem2537562 : rem = rem.
Proof. exact (eq_refl rem). Qed.
Lemma lem2537563 (m : int) : (term64 m) = term59.
Proof. exact (MK_COMB (@lem2537562) (@lem2537561 m)). Qed.
Lemma lem2537564 (p : int) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem2537565 (m : int) (p : int) : (term65 m p) = (term61 p).
Proof. exact (MK_COMB (@lem2537563 m) (@lem2537564 p)). Qed.
Lemma lem2537566 (m : int) (p : int) : ((term60 m p) = (term65 m p)) = ((term61 p) = (term61 p)).
Proof. exact (MK_COMB (@lem2537558 m p) (@lem2537565 m p)). Qed.
Lemma lem2537568 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2537569 (x : int) : (x = x) = True.
Proof. exact (@lem2537568 int x). Qed.
Lemma lem2537570 (p : int) : ((term61 p) = (term61 p)) = True.
Proof. exact (@lem2537569 (term61 p)). Qed.
Lemma lem2537571 (m : int) (p : int) : ((term60 m p) = (term65 m p)) = True.
Proof. exact (TRANS (@lem2537566 m p) (@lem2537570 p)). Qed.
Lemma lem2537572 (m : int) : (term66 m) = term67.
Proof. exact (fun_ext (fun p : int => @lem2537571 m p)). Qed.
Lemma lem2537573 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2537574 (m : int) : (term32 m) = term68.
Proof. exact (MK_COMB (@lem2537573) (@lem2537572 m)). Qed.
Lemma lem2537576 {A : Type'} (t : Prop) : (term69 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2537577 (t : Prop) : (term70 t) = t.
Proof. exact (@lem2537576 int t). Qed.
Lemma lem2537578 : term68 = True.
Proof. exact (@lem2537577 True). Qed.
Lemma lem2537579 (m : int) : (term32 m) = True.
Proof. exact (TRANS (@lem2537574 m) (@lem2537578)). Qed.
Lemma lem2537580 (m : int) : True = (term32 m).
Proof. exact (SYM (@lem2537579 m)). Qed.
Lemma lem2537581 (m : int) : term32 m.
Proof. exact (EQ_MP (@lem2537580 m) (@lem0)). Qed.
Lemma lem2537589 (x : int) (n : nat) : (term26 x n) = (term27 x n).
Proof. exact (EQ_MP (@lem2537517 x n) (@lem2537516 x n)). Qed.
Lemma lem2537590 (m : int) (p : int) (n : nat) : (term71 m p n) = (term72 m p n).
Proof. exact (@lem2537589 (rem m p) n). Qed.
Lemma lem2537591 : rem = rem.
Proof. exact (eq_refl rem). Qed.
Lemma lem2537592 (m : int) (p : int) (n : nat) : (term73 m p n) = (term74 m p n).
Proof. exact (MK_COMB (@lem2537591) (@lem2537590 m p n)). Qed.
Lemma lem2537593 (p : int) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem2537594 (m : int) (n : nat) (p : int) : (term75 m n p) = (term76 m n p).
Proof. exact (MK_COMB (@lem2537592 m p n) (@lem2537593 p)). Qed.
Lemma lem2537595 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2537596 (m : int) (n : nat) (p : int) : (term77 m n p) = (term78 m n p).
Proof. exact (MK_COMB (@lem2537595) (@lem2537594 m n p)). Qed.
Lemma lem2537598 (x : int) (n : nat) : (term26 x n) = (term27 x n).
Proof. exact (EQ_MP (@lem2537517 x n) (@lem2537516 x n)). Qed.
Lemma lem2537599 (m : int) (n : nat) : (term26 m n) = (term27 m n).
Proof. exact (@lem2537598 m n). Qed.
Lemma lem2537600 : rem = rem.
Proof. exact (eq_refl rem). Qed.
Lemma lem2537601 (m : int) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (MK_COMB (@lem2537600) (@lem2537599 m n)). Qed.
Lemma lem2537602 (p : int) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem2537603 (m : int) (n : nat) (p : int) : (term81 m n p) = (term82 m n p).
Proof. exact (MK_COMB (@lem2537601 m n) (@lem2537602 p)). Qed.
Lemma lem2537604 (m : int) (n : nat) (p : int) : ((term75 m n p) = (term81 m n p)) = ((term76 m n p) = (term82 m n p)).
Proof. exact (MK_COMB (@lem2537596 m n p) (@lem2537603 m n p)). Qed.
Lemma lem2537607 (m : int) (n : nat) : (term83 m n) = (term84 m n).
Proof. exact (fun_ext (fun p : int => @lem2537604 m n p)). Qed.
Lemma lem2537608 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2537609 (m : int) (n : nat) : (term40 m n) = (term85 m n).
Proof. exact (MK_COMB (@lem2537608) (@lem2537607 m n)). Qed.
Lemma lem2537614 (m : int) (n : nat) : (term85 m n) = (term40 m n).
Proof. exact (SYM (@lem2537609 m n)). Qed.
Lemma lem2537616 (m : int) (n : int) (p : int) : (term6 m n p) = (term5 m n p).
Proof. exact (EQ_MP (@lem2537513 m n p) (@lem2537512 m n p)). Qed.
Lemma lem2537617 (m : int) (n : nat) (p : int) : (term76 m n p) = (term86 m n p).
Proof. exact (@lem2537616 (rem m p) (term87 m p n) p). Qed.
Lemma lem2537618 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2537619 (m : int) (n : nat) (p : int) : (term78 m n p) = (term88 m n p).
Proof. exact (MK_COMB (@lem2537618) (@lem2537617 m n p)). Qed.
Lemma lem2537620 (m : int) (n : nat) (p : int) : (term82 m n p) = (term82 m n p).
Proof. exact (eq_refl (term82 m n p)). Qed.
Lemma lem2537621 (m : int) (n : nat) (p : int) : ((term76 m n p) = (term82 m n p)) = ((term86 m n p) = (term82 m n p)).
Proof. exact (MK_COMB (@lem2537619 m n p) (@lem2537620 m n p)). Qed.
Lemma lem2537622 (m : int) (n : nat) (p : int) : ((term86 m n p) = (term82 m n p)) = ((term76 m n p) = (term82 m n p)).
Proof. exact (SYM (@lem2537621 m n p)). Qed.
Lemma lem2537623 (p : int) (m : int) (n : nat) (h1 : term36 m n) : term89 m n p.
Proof. exact (@lem2537543 m n h1 p). Qed.
Lemma lem2537624 (m : int) (n : nat) (p : int) : (term89 m n p) = ((term90 m n p) = (term91 m n p)).
Proof. exact (eq_refl (term89 m n p)). Qed.
Lemma lem2537629 (p : int) (m : int) (n : nat) (h1 : term36 m n) : (term90 m n p) = (term91 m n p).
Proof. exact (EQ_MP (@lem2537624 m n p) (@lem2537623 p m n h1)). Qed.
Lemma lem2537630 (m : int) (p : int) : (term92 m p) = (term92 m p).
Proof. exact (eq_refl (term92 m p)). Qed.
Lemma lem2537631 (p : int) (m : int) (n : nat) (h1 : term36 m n) : (term93 m n p) = (term94 m n p).
Proof. exact (MK_COMB (@lem2537630 m p) (@lem2537629 p m n h1)). Qed.
Lemma lem2537632 : rem = rem.
Proof. exact (eq_refl rem). Qed.
Lemma lem2537633 (p : int) (m : int) (n : nat) (h1 : term36 m n) : (term95 m n p) = (term96 m n p).
Proof. exact (MK_COMB (@lem2537632) (@lem2537631 p m n h1)). Qed.
Lemma lem2537634 (p : int) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem2537635 (p : int) (m : int) (n : nat) (h1 : term36 m n) : (term86 m n p) = (term97 m n p).
Proof. exact (MK_COMB (@lem2537633 p m n h1) (@lem2537634 p)). Qed.
Lemma lem2537636 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2537637 (p : int) (m : int) (n : nat) (h1 : term36 m n) : (term88 m n p) = (term98 m n p).
Proof. exact (MK_COMB (@lem2537636) (@lem2537635 p m n h1)). Qed.
Lemma lem2537638 (m : int) (n : nat) (p : int) : (term82 m n p) = (term82 m n p).
Proof. exact (eq_refl (term82 m n p)). Qed.
Lemma lem2537639 (p : int) (m : int) (n : nat) (h1 : term36 m n) : ((term86 m n p) = (term82 m n p)) = ((term97 m n p) = (term82 m n p)).
Proof. exact (MK_COMB (@lem2537637 p m n h1) (@lem2537638 m n p)). Qed.
Lemma lem2537642 (p : int) (m : int) (n : nat) (h1 : term36 m n) : ((term97 m n p) = (term82 m n p)) = ((term86 m n p) = (term82 m n p)).
Proof. exact (SYM (@lem2537639 p m n h1)). Qed.
Lemma lem2537646 (m : int) (n : int) : (term10 m n) = (rem m n).
Proof. exact (EQ_MP (@lem2537486 m n) (@lem2537485 m n)). Qed.
Lemma lem2537647 (m : int) (p : int) : (term10 m p) = (rem m p).
Proof. exact (@lem2537646 m p). Qed.
Lemma lem2537648 : int_mul = int_mul.
Proof. exact (eq_refl int_mul). Qed.
Lemma lem2537649 (m : int) (p : int) : (term92 m p) = (term99 m p).
Proof. exact (MK_COMB (@lem2537648) (@lem2537647 m p)). Qed.
Lemma lem2537650 (m : int) (n : nat) (p : int) : (term91 m n p) = (term91 m n p).
Proof. exact (eq_refl (term91 m n p)). Qed.
Lemma lem2537651 (m : int) (n : nat) (p : int) : (term94 m n p) = (term100 m n p).
Proof. exact (MK_COMB (@lem2537649 m p) (@lem2537650 m n p)). Qed.
Lemma lem2537652 : rem = rem.
Proof. exact (eq_refl rem). Qed.
Lemma lem2537653 (m : int) (n : nat) (p : int) : (term96 m n p) = (term101 m n p).
Proof. exact (MK_COMB (@lem2537652) (@lem2537651 m n p)). Qed.
Lemma lem2537654 (p : int) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem2537655 (m : int) (n : nat) (p : int) : (term97 m n p) = (term102 m n p).
Proof. exact (MK_COMB (@lem2537653 m n p) (@lem2537654 p)). Qed.
Lemma lem2537656 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2537657 (m : int) (n : nat) (p : int) : (term98 m n p) = (term103 m n p).
Proof. exact (MK_COMB (@lem2537656) (@lem2537655 m n p)). Qed.
Lemma lem2537658 (m : int) (n : nat) (p : int) : (term82 m n p) = (term82 m n p).
Proof. exact (eq_refl (term82 m n p)). Qed.
Lemma lem2537659 (m : int) (n : nat) (p : int) : ((term97 m n p) = (term82 m n p)) = ((term102 m n p) = (term82 m n p)).
Proof. exact (MK_COMB (@lem2537657 m n p) (@lem2537658 m n p)). Qed.
Lemma lem2537662 (m : int) (n : nat) (p : int) : ((term102 m n p) = (term82 m n p)) = ((term97 m n p) = (term82 m n p)).
Proof. exact (SYM (@lem2537659 m n p)). Qed.
Lemma lem2537666 (m : int) (n : int) (p : int) : (term5 m n p) = (term6 m n p).
Proof. exact (EQ_MP (@lem2537480 m n p) (@lem2537479 m n p)). Qed.
Lemma lem2537667 (m : int) (n : nat) (p : int) : (term102 m n p) = (term82 m n p).
Proof. exact (@lem2537666 m (int_pow m n) p). Qed.
Lemma lem2537668 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2537669 (m : int) (n : nat) (p : int) : (term103 m n p) = (term104 m n p).
Proof. exact (MK_COMB (@lem2537668) (@lem2537667 m n p)). Qed.
Lemma lem2537670 (m : int) (n : nat) (p : int) : (term82 m n p) = (term82 m n p).
Proof. exact (eq_refl (term82 m n p)). Qed.
Lemma lem2537671 (m : int) (n : nat) (p : int) : ((term102 m n p) = (term82 m n p)) = ((term82 m n p) = (term82 m n p)).
Proof. exact (MK_COMB (@lem2537669 m n p) (@lem2537670 m n p)). Qed.
Lemma lem2537673 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2537674 (x : int) : (x = x) = True.
Proof. exact (@lem2537673 int x). Qed.
Lemma lem2537675 (m : int) (n : nat) (p : int) : ((term82 m n p) = (term82 m n p)) = True.
Proof. exact (@lem2537674 (term82 m n p)). Qed.
Lemma lem2537676 (m : int) (n : nat) (p : int) : ((term102 m n p) = (term82 m n p)) = True.
Proof. exact (TRANS (@lem2537671 m n p) (@lem2537675 m n p)). Qed.
Lemma lem2537677 (m : int) (n : nat) (p : int) : True = ((term102 m n p) = (term82 m n p)).
Proof. exact (SYM (@lem2537676 m n p)). Qed.
Lemma lem2537678 (m : int) (n : nat) (p : int) : (term102 m n p) = (term82 m n p).
Proof. exact (EQ_MP (@lem2537677 m n p) (@lem0)). Qed.
Lemma lem2537679 (m : int) (n : nat) (p : int) : (term97 m n p) = (term82 m n p).
Proof. exact (EQ_MP (@lem2537662 m n p) (@lem2537678 m n p)). Qed.
Lemma lem2537680 (p : int) (m : int) (n : nat) (h1 : term36 m n) : (term86 m n p) = (term82 m n p).
Proof. exact (EQ_MP (@lem2537642 p m n h1) (@lem2537679 m n p)). Qed.
Lemma lem2537681 (p : int) (m : int) (n : nat) (h1 : term36 m n) : (term76 m n p) = (term82 m n p).
Proof. exact (EQ_MP (@lem2537622 m n p) (@lem2537680 p m n h1)). Qed.
Lemma lem2537686 (m : int) (n : nat) (h1 : term36 m n) : term85 m n.
Proof. exact (fun p : int => @lem2537681 p m n h1). Qed.
Lemma lem2537687 (m : int) (n : nat) (h1 : term36 m n) : term40 m n.
Proof. exact (EQ_MP (@lem2537614 m n) (@lem2537686 m n h1)). Qed.
Lemma lem2537688 (m : int) (n : nat) : term42 m n.
Proof. exact (fun h0 : term36 m n => @lem2537687 m n h0). Qed.
Lemma lem2537693 (m : int) : term46 m.
Proof. exact (fun n : nat => @lem2537688 m n). Qed.
Lemma lem2537694 (m : int) : term48 m.
Proof. exact (conj (@lem2537581 m) (@lem2537693 m)). Qed.
Lemma lem2537695 (m : int) : term53 m.
Proof. exact (@lem2537542 m (@lem2537694 m)). Qed.
Lemma lem2537700 : term105.
Proof. exact (fun m : int => @lem2537695 m). Qed.
