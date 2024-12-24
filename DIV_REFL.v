Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIV_REFL_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import DIV_UNIQ_spec.
Require Import LT_0_spec.
Require Import MULT_CLAUSES_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Lemma lem210483 (n : nat) : term0 n.
Proof. exact (@lem91530 n). Qed.
Lemma lem210484 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem210485 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem210484 n) (@lem210483 n)). Qed.
Lemma lem210486 (n : nat) : (term1 n) = ((term1 n) = True).
Proof. exact (@lem7 (term1 n)). Qed.
Lemma lem210488 : term2.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem210489 : term3.
Proof. exact (proj2 (@lem210488)). Qed.
Lemma lem210510 : term4.
Proof. exact (proj1 (@lem210489)). Qed.
Lemma lem210511 (n : nat) : term5 n.
Proof. exact (@lem210510 n). Qed.
Lemma lem210512 (n : nat) : (term5 n) = ((term6 n) = n).
Proof. exact (eq_refl (term5 n)). Qed.
Lemma lem210522 : term7.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem210538 : term8.
Proof. exact (proj1 (@lem210522)). Qed.
Lemma lem210539 (m : nat) : term9 m.
Proof. exact (@lem210538 m). Qed.
Lemma lem210540 (m : nat) : (term9 m) = ((term10 m) = m).
Proof. exact (eq_refl (term9 m)). Qed.
Lemma lem210546 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem210547 (m : nat) (h1 : term11) : term12 m.
Proof. exact (@lem210546 h1 m). Qed.
Lemma lem210548 (m : nat) : (term12 m) = (term13 m).
Proof. exact (eq_refl (term12 m)). Qed.
Lemma lem210549 (m : nat) (h1 : term11) : term13 m.
Proof. exact (EQ_MP (@lem210548 m) (@lem210547 m h1)). Qed.
Lemma lem210550 (m : nat) (n : nat) (h1 : term11) : term14 m n.
Proof. exact (@lem210549 m h1 n). Qed.
Lemma lem210551 (m : nat) (n : nat) : (term14 m n) = (term15 m n).
Proof. exact (eq_refl (term14 m n)). Qed.
Lemma lem210552 (m : nat) (n : nat) (h1 : term11) : term15 m n.
Proof. exact (EQ_MP (@lem210551 m n) (@lem210550 m n h1)). Qed.
Lemma lem210553 (m : nat) (n : nat) (q : nat) (h1 : term11) : term16 m n q.
Proof. exact (@lem210552 m n h1 q). Qed.
Lemma lem210554 (m : nat) (n : nat) (q : nat) : (term16 m n q) = (term17 m n q).
Proof. exact (eq_refl (term16 m n q)). Qed.
Lemma lem210555 (m : nat) (n : nat) (q : nat) (h1 : term11) : term17 m n q.
Proof. exact (EQ_MP (@lem210554 m n q) (@lem210553 m n q h1)). Qed.
Lemma lem210556 (m : nat) (n : nat) (q : nat) (r : nat) (h1 : term11) : term18 m n q r.
Proof. exact (@lem210555 m n q h1 r). Qed.
Lemma lem210557 (r : nat) (m : nat) (n : nat) (q : nat) : (term18 m n q r) = (term19 r m n q).
Proof. exact (eq_refl (term18 m n q r)). Qed.
Lemma lem210558 (r : nat) (m : nat) (n : nat) (q : nat) (h1 : term11) : term19 r m n q.
Proof. exact (EQ_MP (@lem210557 r m n q) (@lem210556 m n q r h1)). Qed.
Lemma lem210559 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term20 m q r n) : term20 m q r n.
Proof. exact (h1). Qed.
Lemma lem210560 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term11) (h2 : term20 m q r n) : (Nat.div m n) = q.
Proof. exact (@lem210558 r m n q h1 (@lem210559 m q r n h2)). Qed.
Lemma lem210561 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term20 m q r n) : term21 m n q.
Proof. exact (fun h0 : term11 => @lem210560 m q r n h0 h1). Qed.
Lemma lem210562 (m : nat) (q : nat) (n : nat) (h1 : term22 m q n) : term22 m q n.
Proof. exact (h1). Qed.
Lemma lem210563 (m : nat) (q : nat) (n : nat) (h1 : term22 m q n) : term21 m n q.
Proof. exact (ex_elim (@lem210562 m q n h1) (fun r : nat => fun h0 : term23 m q n r => @lem210561 m q r n h0)). Qed.
Lemma lem210564 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem210565 (m : nat) (q : nat) (n : nat) (h1 : term11) (h2 : term22 m q n) : (Nat.div m n) = q.
Proof. exact (@lem210563 m q n h2 (@lem210564 h1)). Qed.
Lemma lem210566 (m : nat) (n : nat) (q : nat) (h1 : term11) : term24 m n q.
Proof. exact (fun h0 : term22 m q n => @lem210565 m q n h1 h0). Qed.
Lemma lem210567 (m : nat) (n : nat) (h1 : term11) : term25 m n.
Proof. exact (fun q : nat => @lem210566 m n q h1). Qed.
Lemma lem210568 (m : nat) (h1 : term11) : term26 m.
Proof. exact (fun n : nat => @lem210567 m n h1). Qed.
Lemma lem210569 (h1 : term11) : term27.
Proof. exact (fun m : nat => @lem210568 m h1). Qed.
Lemma lem210570 : term28.
Proof. exact (fun h0 : term11 => @lem210569 h0). Qed.
Lemma lem210571 : term27.
Proof. exact (@lem210570 (@lem169759)). Qed.
Lemma lem210572 (m : nat) : term29 m.
Proof. exact (@lem210571 m). Qed.
Lemma lem210573 (m : nat) : (term29 m) = (term26 m).
Proof. exact (eq_refl (term29 m)). Qed.
Lemma lem210574 (m : nat) : term26 m.
Proof. exact (EQ_MP (@lem210573 m) (@lem210572 m)). Qed.
Lemma lem210575 (m : nat) (n : nat) : term30 m n.
Proof. exact (@lem210574 m n). Qed.
Lemma lem210576 (m : nat) (n : nat) : (term30 m n) = (term25 m n).
Proof. exact (eq_refl (term30 m n)). Qed.
Lemma lem210577 (m : nat) (n : nat) : term25 m n.
Proof. exact (EQ_MP (@lem210576 m n) (@lem210575 m n)). Qed.
Lemma lem210578 (m : nat) (n : nat) (q : nat) : term31 m n q.
Proof. exact (@lem210577 m n q). Qed.
Lemma lem210579 (m : nat) (n : nat) (q : nat) : (term31 m n q) = (term24 m n q).
Proof. exact (eq_refl (term31 m n q)). Qed.
Lemma lem210581 (n : nat) (h1 : term32 n) : term32 n.
Proof. exact (h1). Qed.
Lemma lem210583 (m : nat) (n : nat) (q : nat) : term24 m n q.
Proof. exact (EQ_MP (@lem210579 m n q) (@lem210578 m n q)). Qed.
Lemma lem210584 (n : nat) : term33 n.
Proof. exact (@lem210583 n n term34). Qed.
Lemma lem210590 (m : nat) : (term10 m) = m.
Proof. exact (EQ_MP (@lem210540 m) (@lem210539 m)). Qed.
Lemma lem210591 (n : nat) : (term35 n) = (term6 n).
Proof. exact (@lem210590 (term6 n)). Qed.
Lemma lem210593 (n : nat) : (term6 n) = n.
Proof. exact (EQ_MP (@lem210512 n) (@lem210511 n)). Qed.
Lemma lem210594 (n : nat) : (term35 n) = n.
Proof. exact (TRANS (@lem210591 n) (@lem210593 n)). Qed.
Lemma lem210595 (n : nat) : (@eq nat n) = (@eq nat n).
Proof. exact (eq_refl (@eq nat n)). Qed.
Lemma lem210596 (n : nat) : (n = (term35 n)) = (n = n).
Proof. exact (MK_COMB (@lem210595 n) (@lem210594 n)). Qed.
Lemma lem210598 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem210599 (x : nat) : (x = x) = True.
Proof. exact (@lem210598 nat x). Qed.
Lemma lem210600 (n : nat) : (n = n) = True.
Proof. exact (@lem210599 n). Qed.
Lemma lem210601 (n : nat) : (n = (term35 n)) = True.
Proof. exact (TRANS (@lem210596 n) (@lem210600 n)). Qed.
Lemma lem210602 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem210603 (n : nat) : (term36 n) = (and True).
Proof. exact (MK_COMB (@lem210602) (@lem210601 n)). Qed.
Lemma lem210604 (n : nat) : (term37 n) = (term37 n).
Proof. exact (eq_refl (term37 n)). Qed.
Lemma lem210605 (n : nat) : (term38 n) = (term39 n).
Proof. exact (MK_COMB (@lem210603 n) (@lem210604 n)). Qed.
Lemma lem210607 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem210608 (n : nat) : (term39 n) = (term37 n).
Proof. exact (@lem210607 (term37 n)). Qed.
Lemma lem210609 (n : nat) : (term38 n) = (term37 n).
Proof. exact (TRANS (@lem210605 n) (@lem210608 n)). Qed.
Lemma lem210610 (n : nat) : (term37 n) = (term38 n).
Proof. exact (SYM (@lem210609 n)). Qed.
Lemma lem210612 (P : nat -> Prop) : term40 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem210613 : term41.
Proof. exact (@lem210612 term42). Qed.
Lemma lem210614 : term43 = term44.
Proof. exact (eq_refl term43). Qed.
Lemma lem210615 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem210616 : term45 = term46.
Proof. exact (MK_COMB (@lem210615) (@lem210614)). Qed.
Lemma lem210617 (n : nat) : (term47 n) = (term48 n).
Proof. exact (eq_refl (term47 n)). Qed.
Lemma lem210618 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem210619 (n : nat) : (term49 n) = (term50 n).
Proof. exact (MK_COMB (@lem210618) (@lem210617 n)). Qed.
Lemma lem210620 (n : nat) : (term51 n) = (term52 n).
Proof. exact (eq_refl (term51 n)). Qed.
Lemma lem210621 (n : nat) : (term53 n) = (term54 n).
Proof. exact (MK_COMB (@lem210619 n) (@lem210620 n)). Qed.
Lemma lem210622 : term55 = term56.
Proof. exact (fun_ext (fun n : nat => @lem210621 n)). Qed.
Lemma lem210623 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem210624 : term57 = term58.
Proof. exact (MK_COMB (@lem210623) (@lem210622)). Qed.
Lemma lem210625 : term59 = term60.
Proof. exact (MK_COMB (@lem210616) (@lem210624)). Qed.
Lemma lem210626 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem210627 : term61 = term62.
Proof. exact (MK_COMB (@lem210626) (@lem210625)). Qed.
Lemma lem210628 (n : nat) : (term47 n) = (term48 n).
Proof. exact (eq_refl (term47 n)). Qed.
Lemma lem210629 : term63 = term42.
Proof. exact (fun_ext (fun n : nat => @lem210628 n)). Qed.
Lemma lem210630 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem210631 : term64 = term65.
Proof. exact (MK_COMB (@lem210630) (@lem210629)). Qed.
Lemma lem210632 : term41 = term66.
Proof. exact (MK_COMB (@lem210627) (@lem210631)). Qed.
Lemma lem210633 : term66.
Proof. exact (EQ_MP (@lem210632) (@lem210613)). Qed.
Lemma lem210638 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem210639 (x : nat) : (x = x) = True.
Proof. exact (@lem210638 nat x). Qed.
Lemma lem210640 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem210639 (NUMERAL 0)). Qed.
Lemma lem210641 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem210642 : term67 = (~ True).
Proof. exact (MK_COMB (@lem210641) (@lem210640)). Qed.
Lemma lem210644 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem210645 : term67 = False.
Proof. exact (TRANS (@lem210642) (@lem210644)). Qed.
Lemma lem210646 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem210647 : term68 = (imp False).
Proof. exact (MK_COMB (@lem210646) (@lem210645)). Qed.
Lemma lem210648 : term69 = term69.
Proof. exact (eq_refl term69). Qed.
Lemma lem210649 : term44 = term70.
Proof. exact (MK_COMB (@lem210647) (@lem210648)). Qed.
Lemma lem210651 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem210652 : term70 = True.
Proof. exact (@lem210651 term69). Qed.
Lemma lem210653 : term44 = True.
Proof. exact (TRANS (@lem210649) (@lem210652)). Qed.
Lemma lem210654 : True = term44.
Proof. exact (SYM (@lem210653)). Qed.
Lemma lem210655 : term44.
Proof. exact (EQ_MP (@lem210654) (@lem0)). Qed.
Lemma lem210661 (n : nat) : (term1 n) = True.
Proof. exact (EQ_MP (@lem210486 n) (@lem210485 n)). Qed.
Lemma lem210662 (n : nat) : (term71 n) = (term71 n).
Proof. exact (eq_refl (term71 n)). Qed.
Lemma lem210663 (n : nat) : (term52 n) = (term72 n).
Proof. exact (MK_COMB (@lem210662 n) (@lem210661 n)). Qed.
Lemma lem210665 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem210666 (n : nat) : (term72 n) = True.
Proof. exact (@lem210665 (term73 n)). Qed.
Lemma lem210667 (n : nat) : (term52 n) = True.
Proof. exact (TRANS (@lem210663 n) (@lem210666 n)). Qed.
Lemma lem210668 (n : nat) : True = (term52 n).
Proof. exact (SYM (@lem210667 n)). Qed.
Lemma lem210669 (n : nat) : term52 n.
Proof. exact (EQ_MP (@lem210668 n) (@lem0)). Qed.
Lemma lem210670 (n : nat) : term54 n.
Proof. exact (fun h0 : term48 n => @lem210669 n). Qed.
Lemma lem210675 : term58.
Proof. exact (fun n : nat => @lem210670 n). Qed.
Lemma lem210676 : term60.
Proof. exact (conj (@lem210655) (@lem210675)). Qed.
Lemma lem210677 : term65.
Proof. exact (@lem210633 (@lem210676)). Qed.
Lemma lem210678 (n : nat) : term47 n.
Proof. exact (@lem210677 n). Qed.
Lemma lem210679 (n : nat) : (term47 n) = (term48 n).
Proof. exact (eq_refl (term47 n)). Qed.
Lemma lem210680 (n : nat) : term48 n.
Proof. exact (EQ_MP (@lem210679 n) (@lem210678 n)). Qed.
Lemma lem210681 (n : nat) (h1 : term32 n) : term37 n.
Proof. exact (@lem210680 n (@lem210581 n h1)). Qed.
Lemma lem210682 (n : nat) (h1 : term32 n) : term38 n.
Proof. exact (EQ_MP (@lem210610 n) (@lem210681 n h1)). Qed.
Lemma lem210683 (n : nat) (h1 : term32 n) : term74 n.
Proof. exact (ex_intro (term75 n) (NUMERAL 0) (@lem210682 n h1)). Qed.
Lemma lem210684 (n : nat) (h1 : term32 n) : (Nat.div n n) = term34.
Proof. exact (@lem210584 n (@lem210683 n h1)). Qed.
Lemma lem210685 (n : nat) (h1 : term32 n) : (term32 n) = ((Nat.div n n) = term34).
Proof. exact (prop_ext (fun h2 : term32 n => @lem210684 n h1) (fun h2 : (Nat.div n n) = term34 => @lem210581 n h1)). Qed.
Lemma lem210686 (n : nat) (h1 : term32 n) : (Nat.div n n) = term34.
Proof. exact (EQ_MP (@lem210685 n h1) (@lem210581 n h1)). Qed.
Lemma lem210687 (n : nat) : term76 n.
Proof. exact (fun h0 : term32 n => @lem210686 n h0). Qed.
Lemma lem210692 : term77.
Proof. exact (fun n : nat => @lem210687 n). Qed.
