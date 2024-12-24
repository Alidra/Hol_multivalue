Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LT_ADD_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import LT_SUC_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Lemma lem100564 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem100565 : term1.
Proof. exact (@lem100564 term2). Qed.
Lemma lem100566 : term3 = term4.
Proof. exact (eq_refl term3). Qed.
Lemma lem100567 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem100568 : term5 = term6.
Proof. exact (MK_COMB (@lem100567) (@lem100566)). Qed.
Lemma lem100569 (m : nat) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem100570 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem100571 (m : nat) : (term9 m) = (term10 m).
Proof. exact (MK_COMB (@lem100570) (@lem100569 m)). Qed.
Lemma lem100572 (m : nat) : (term11 m) = (term12 m).
Proof. exact (eq_refl (term11 m)). Qed.
Lemma lem100573 (m : nat) : (term13 m) = (term14 m).
Proof. exact (MK_COMB (@lem100571 m) (@lem100572 m)). Qed.
Lemma lem100574 : term15 = term16.
Proof. exact (fun_ext (fun m : nat => @lem100573 m)). Qed.
Lemma lem100575 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem100576 : term17 = term18.
Proof. exact (MK_COMB (@lem100575) (@lem100574)). Qed.
Lemma lem100577 : term19 = term20.
Proof. exact (MK_COMB (@lem100568) (@lem100576)). Qed.
Lemma lem100578 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem100579 : term21 = term22.
Proof. exact (MK_COMB (@lem100578) (@lem100577)). Qed.
Lemma lem100580 (m : nat) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem100581 : term23 = term2.
Proof. exact (fun_ext (fun m : nat => @lem100580 m)). Qed.
Lemma lem100582 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem100583 : term24 = term25.
Proof. exact (MK_COMB (@lem100582) (@lem100581)). Qed.
Lemma lem100584 : term1 = term26.
Proof. exact (MK_COMB (@lem100579) (@lem100583)). Qed.
Lemma lem100585 : term26.
Proof. exact (EQ_MP (@lem100584) (@lem100565)). Qed.
Lemma lem100586 (m : nat) (h1 : term8 m) : term8 m.
Proof. exact (h1). Qed.
Lemma lem100613 : term27.
Proof. exact (proj1 (@lem77629)). Qed.
Lemma lem100614 (n : nat) : term28 n.
Proof. exact (@lem100613 n). Qed.
Lemma lem100615 (n : nat) : (term28 n) = ((term29 n) = n).
Proof. exact (eq_refl (term28 n)). Qed.
Lemma lem100624 (n : nat) : (term29 n) = n.
Proof. exact (EQ_MP (@lem100615 n) (@lem100614 n)). Qed.
Lemma lem100625 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem100626 (n : nat) : (term31 n) = (term32 n).
Proof. exact (MK_COMB (@lem100625) (@lem100624 n)). Qed.
Lemma lem100627 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem100628 (n : nat) : (term33 n) = (term34 n).
Proof. exact (MK_COMB (@lem100627) (@lem100626 n)). Qed.
Lemma lem100629 (n : nat) : (term32 n) = (term32 n).
Proof. exact (eq_refl (term32 n)). Qed.
Lemma lem100630 (n : nat) : ((term31 n) = (term32 n)) = ((term32 n) = (term32 n)).
Proof. exact (MK_COMB (@lem100628 n) (@lem100629 n)). Qed.
Lemma lem100632 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem100633 (x : Prop) : (x = x) = True.
Proof. exact (@lem100632 Prop x). Qed.
Lemma lem100634 (n : nat) : ((term32 n) = (term32 n)) = True.
Proof. exact (@lem100633 (term32 n)). Qed.
Lemma lem100635 (n : nat) : ((term31 n) = (term32 n)) = True.
Proof. exact (TRANS (@lem100630 n) (@lem100634 n)). Qed.
Lemma lem100636 : term35 = term36.
Proof. exact (fun_ext (fun n : nat => @lem100635 n)). Qed.
Lemma lem100637 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem100638 : term4 = term37.
Proof. exact (MK_COMB (@lem100637) (@lem100636)). Qed.
Lemma lem100640 {A : Type'} (t : Prop) : (term38 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem100641 (t : Prop) : (term39 t) = t.
Proof. exact (@lem100640 nat t). Qed.
Lemma lem100642 : term37 = True.
Proof. exact (@lem100641 True). Qed.
Lemma lem100643 : term4 = True.
Proof. exact (TRANS (@lem100638) (@lem100642)). Qed.
Lemma lem100644 : True = term4.
Proof. exact (SYM (@lem100643)). Qed.
Lemma lem100645 : term4.
Proof. exact (EQ_MP (@lem100644) (@lem0)). Qed.
Lemma lem100646 (m : nat) : term40 m.
Proof. exact (@lem91415 m). Qed.
Lemma lem100647 (m : nat) : (term40 m) = (term41 m).
Proof. exact (eq_refl (term40 m)). Qed.
Lemma lem100648 (m : nat) : term41 m.
Proof. exact (EQ_MP (@lem100647 m) (@lem100646 m)). Qed.
Lemma lem100649 (m : nat) (n : nat) : term42 m n.
Proof. exact (@lem100648 m n). Qed.
Lemma lem100650 (m : nat) (n : nat) : (term42 m n) = ((term43 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term42 m n)). Qed.
Lemma lem100652 : term44.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem100653 : term45.
Proof. exact (proj2 (@lem100652)). Qed.
Lemma lem100661 : term46.
Proof. exact (proj1 (@lem100653)). Qed.
Lemma lem100662 (m : nat) : term47 m.
Proof. exact (@lem100661 m). Qed.
Lemma lem100663 (m : nat) : (term47 m) = (term48 m).
Proof. exact (eq_refl (term47 m)). Qed.
Lemma lem100664 (m : nat) : term48 m.
Proof. exact (EQ_MP (@lem100663 m) (@lem100662 m)). Qed.
Lemma lem100665 (m : nat) (n : nat) : term49 m n.
Proof. exact (@lem100664 m n). Qed.
Lemma lem100666 (m : nat) (n : nat) : (term49 m n) = ((term50 m n) = (term51 m n)).
Proof. exact (eq_refl (term49 m n)). Qed.
Lemma lem100676 (n : nat) (m : nat) (h1 : term8 m) : term52 m n.
Proof. exact (@lem100586 m h1 n). Qed.
Lemma lem100677 (m : nat) (n : nat) : (term52 m n) = ((term53 m n) = (term32 n)).
Proof. exact (eq_refl (term52 m n)). Qed.
Lemma lem100686 (m : nat) (n : nat) : (term50 m n) = (term51 m n).
Proof. exact (EQ_MP (@lem100666 m n) (@lem100665 m n)). Qed.
Lemma lem100687 (m : nat) : (term54 m) = (term54 m).
Proof. exact (eq_refl (term54 m)). Qed.
Lemma lem100688 (m : nat) (n : nat) : (term55 m n) = (term56 m n).
Proof. exact (MK_COMB (@lem100687 m) (@lem100686 m n)). Qed.
Lemma lem100690 (m : nat) (n : nat) : (term43 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem100650 m n) (@lem100649 m n)). Qed.
Lemma lem100691 (m : nat) (n : nat) : (term56 m n) = (term53 m n).
Proof. exact (@lem100690 m (Nat.add m n)). Qed.
Lemma lem100693 (n : nat) (m : nat) (h1 : term8 m) : (term53 m n) = (term32 n).
Proof. exact (EQ_MP (@lem100677 m n) (@lem100676 n m h1)). Qed.
Lemma lem100694 (n : nat) (m : nat) (h1 : term8 m) : (term56 m n) = (term32 n).
Proof. exact (TRANS (@lem100691 m n) (@lem100693 n m h1)). Qed.
Lemma lem100695 (n : nat) (m : nat) (h1 : term8 m) : (term55 m n) = (term32 n).
Proof. exact (TRANS (@lem100688 m n) (@lem100694 n m h1)). Qed.
Lemma lem100696 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem100697 (n : nat) (m : nat) (h1 : term8 m) : (term57 m n) = (term34 n).
Proof. exact (MK_COMB (@lem100696) (@lem100695 n m h1)). Qed.
Lemma lem100698 (n : nat) : (term32 n) = (term32 n).
Proof. exact (eq_refl (term32 n)). Qed.
Lemma lem100699 (n : nat) (m : nat) (h1 : term8 m) : ((term55 m n) = (term32 n)) = ((term32 n) = (term32 n)).
Proof. exact (MK_COMB (@lem100697 n m h1) (@lem100698 n)). Qed.
Lemma lem100701 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem100702 (x : Prop) : (x = x) = True.
Proof. exact (@lem100701 Prop x). Qed.
Lemma lem100703 (n : nat) : ((term32 n) = (term32 n)) = True.
Proof. exact (@lem100702 (term32 n)). Qed.
Lemma lem100704 (n : nat) (m : nat) (h1 : term8 m) : ((term55 m n) = (term32 n)) = True.
Proof. exact (TRANS (@lem100699 n m h1) (@lem100703 n)). Qed.
Lemma lem100705 (m : nat) (h1 : term8 m) : (term58 m) = term36.
Proof. exact (fun_ext (fun n : nat => @lem100704 n m h1)). Qed.
Lemma lem100706 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem100707 (m : nat) (h1 : term8 m) : (term12 m) = term37.
Proof. exact (MK_COMB (@lem100706) (@lem100705 m h1)). Qed.
Lemma lem100709 {A : Type'} (t : Prop) : (term38 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem100710 (t : Prop) : (term39 t) = t.
Proof. exact (@lem100709 nat t). Qed.
Lemma lem100711 : term37 = True.
Proof. exact (@lem100710 True). Qed.
Lemma lem100712 (m : nat) (h1 : term8 m) : (term12 m) = True.
Proof. exact (TRANS (@lem100707 m h1) (@lem100711)). Qed.
Lemma lem100713 (m : nat) (h1 : term8 m) : True = (term12 m).
Proof. exact (SYM (@lem100712 m h1)). Qed.
Lemma lem100714 (m : nat) (h1 : term8 m) : term12 m.
Proof. exact (EQ_MP (@lem100713 m h1) (@lem0)). Qed.
Lemma lem100715 (m : nat) : term14 m.
Proof. exact (fun h0 : term8 m => @lem100714 m h0). Qed.
Lemma lem100720 : term18.
Proof. exact (fun m : nat => @lem100715 m). Qed.
Lemma lem100721 : term20.
Proof. exact (conj (@lem100645) (@lem100720)). Qed.
Lemma lem100722 : term25.
Proof. exact (@lem100585 (@lem100721)). Qed.
