Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EVEN_EXISTS_LEMMA_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import MULT_2_spec.
Require Import MULT_CLAUSES_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm124233_spec.
Require Import thm1820_spec.
Require Import thm1822_spec.
Require Import thm1843_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Lemma lem128434 : term0.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem128435 : term1.
Proof. exact (proj2 (@lem128434)). Qed.
Lemma lem128436 : term2.
Proof. exact (proj2 (@lem128435)). Qed.
Lemma lem128437 (m : nat) : term3 m.
Proof. exact (@lem128436 m). Qed.
Lemma lem128438 (m : nat) : (term3 m) = (term4 m).
Proof. exact (eq_refl (term3 m)). Qed.
Lemma lem128439 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem128438 m) (@lem128437 m)). Qed.
Lemma lem128440 (m : nat) (n : nat) : term5 m n.
Proof. exact (@lem128439 m n). Qed.
Lemma lem128441 (m : nat) (n : nat) : (term5 m n) = ((term6 m n) = (term7 m n)).
Proof. exact (eq_refl (term5 m n)). Qed.
Lemma lem128443 : term8.
Proof. exact (proj1 (@lem128435)). Qed.
Lemma lem128444 (m : nat) : term9 m.
Proof. exact (@lem128443 m). Qed.
Lemma lem128445 (m : nat) : (term9 m) = (term10 m).
Proof. exact (eq_refl (term9 m)). Qed.
Lemma lem128446 (m : nat) : term10 m.
Proof. exact (EQ_MP (@lem128445 m) (@lem128444 m)). Qed.
Lemma lem128447 (m : nat) (n : nat) : term11 m n.
Proof. exact (@lem128446 m n). Qed.
Lemma lem128448 (m : nat) (n : nat) : (term11 m n) = ((term12 m n) = (term7 m n)).
Proof. exact (eq_refl (term11 m n)). Qed.
Lemma lem128458 (n : nat) : term13 n.
Proof. exact (@lem84996 n). Qed.
Lemma lem128459 (n : nat) : (term13 n) = ((term14 n) = (Nat.add n n)).
Proof. exact (eq_refl (term13 n)). Qed.
Lemma lem128461 : term15.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem128487 : term16.
Proof. exact (proj1 (@lem128461)). Qed.
Lemma lem128488 (m : nat) : term17 m.
Proof. exact (@lem128487 m). Qed.
Lemma lem128489 (m : nat) : (term17 m) = ((term18 m) = (NUMERAL 0)).
Proof. exact (eq_refl (term17 m)). Qed.
Lemma lem128495 : term19.
Proof. exact (proj2 (@lem124233)). Qed.
Lemma lem128496 (n : nat) : term20 n.
Proof. exact (@lem128495 n). Qed.
Lemma lem128497 (n : nat) : (term20 n) = ((term21 n) = (term22 n)).
Proof. exact (eq_refl (term20 n)). Qed.
Lemma lem128501 (P : nat -> Prop) : term23 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem128502 : term24.
Proof. exact (@lem128501 term25). Qed.
Lemma lem128503 : term26 = term27.
Proof. exact (eq_refl term26). Qed.
Lemma lem128504 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem128505 : term28 = term29.
Proof. exact (MK_COMB (@lem128504) (@lem128503)). Qed.
Lemma lem128506 (n : nat) : (term30 n) = (term31 n).
Proof. exact (eq_refl (term30 n)). Qed.
Lemma lem128507 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem128508 (n : nat) : (term32 n) = (term33 n).
Proof. exact (MK_COMB (@lem128507) (@lem128506 n)). Qed.
Lemma lem128509 (n : nat) : (term34 n) = (term35 n).
Proof. exact (eq_refl (term34 n)). Qed.
Lemma lem128510 (n : nat) : (term36 n) = (term37 n).
Proof. exact (MK_COMB (@lem128508 n) (@lem128509 n)). Qed.
Lemma lem128511 : term38 = term39.
Proof. exact (fun_ext (fun n : nat => @lem128510 n)). Qed.
Lemma lem128512 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem128513 : term40 = term41.
Proof. exact (MK_COMB (@lem128512) (@lem128511)). Qed.
Lemma lem128514 : term42 = term43.
Proof. exact (MK_COMB (@lem128505) (@lem128513)). Qed.
Lemma lem128515 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem128516 : term44 = term45.
Proof. exact (MK_COMB (@lem128515) (@lem128514)). Qed.
Lemma lem128517 (n : nat) : (term30 n) = (term31 n).
Proof. exact (eq_refl (term30 n)). Qed.
Lemma lem128518 : term46 = term25.
Proof. exact (fun_ext (fun n : nat => @lem128517 n)). Qed.
Lemma lem128519 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem128520 : term47 = term48.
Proof. exact (MK_COMB (@lem128519) (@lem128518)). Qed.
Lemma lem128521 : term24 = term49.
Proof. exact (MK_COMB (@lem128516) (@lem128520)). Qed.
Lemma lem128522 : term49.
Proof. exact (EQ_MP (@lem128521) (@lem128502)). Qed.
Lemma lem128523 (n : nat) (h1 : term31 n) : term31 n.
Proof. exact (h1). Qed.
Lemma lem128529 : term50 = True.
Proof. exact (proj1 (@lem124233)). Qed.
Lemma lem128530 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem128531 : term51 = (imp True).
Proof. exact (MK_COMB (@lem128530) (@lem128529)). Qed.
Lemma lem128538 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem128539 : term53 = term54.
Proof. exact (MK_COMB (@lem128531) (@lem128538)). Qed.
Lemma lem128541 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem128542 : term54 = term52.
Proof. exact (@lem128541 term52). Qed.
Lemma lem128549 : term53 = term52.
Proof. exact (TRANS (@lem128539) (@lem128542)). Qed.
Lemma lem128550 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem128551 : term55 = term56.
Proof. exact (MK_COMB (@lem128550) (@lem128549)). Qed.
Lemma lem128555 : term50 = True.
Proof. exact (proj1 (@lem124233)). Qed.
Lemma lem128556 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem128557 : term57 = (~ True).
Proof. exact (MK_COMB (@lem128556) (@lem128555)). Qed.
Lemma lem128559 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem128560 : term57 = False.
Proof. exact (TRANS (@lem128557) (@lem128559)). Qed.
Lemma lem128561 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem128562 : term58 = (imp False).
Proof. exact (MK_COMB (@lem128561) (@lem128560)). Qed.
Lemma lem128569 : term59 = term59.
Proof. exact (eq_refl term59). Qed.
Lemma lem128570 : term60 = term61.
Proof. exact (MK_COMB (@lem128562) (@lem128569)). Qed.
Lemma lem128572 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem128573 : term61 = True.
Proof. exact (@lem128572 term59). Qed.
Lemma lem128574 : term60 = True.
Proof. exact (TRANS (@lem128570) (@lem128573)). Qed.
Lemma lem128575 : term27 = term62.
Proof. exact (MK_COMB (@lem128551) (@lem128574)). Qed.
Lemma lem128577 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem128578 : term62 = term52.
Proof. exact (@lem128577 term52). Qed.
Lemma lem128585 : term27 = term52.
Proof. exact (TRANS (@lem128575) (@lem128578)). Qed.
Lemma lem128586 : term52 = term27.
Proof. exact (SYM (@lem128585)). Qed.
Lemma lem128592 (n : nat) : (term21 n) = (term22 n).
Proof. exact (EQ_MP (@lem128497 n) (@lem128496 n)). Qed.
Lemma lem128593 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem128594 (n : nat) : (term63 n) = (term64 n).
Proof. exact (MK_COMB (@lem128593) (@lem128592 n)). Qed.
Lemma lem128601 (n : nat) : (term65 n) = (term65 n).
Proof. exact (eq_refl (term65 n)). Qed.
Lemma lem128602 (n : nat) : (term66 n) = (term67 n).
Proof. exact (MK_COMB (@lem128594 n) (@lem128601 n)). Qed.
Lemma lem128605 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem128606 (n : nat) : (term68 n) = (term69 n).
Proof. exact (MK_COMB (@lem128605) (@lem128602 n)). Qed.
Lemma lem128610 (n : nat) : (term21 n) = (term22 n).
Proof. exact (EQ_MP (@lem128497 n) (@lem128496 n)). Qed.
Lemma lem128611 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem128612 (n : nat) : (term70 n) = (term71 n).
Proof. exact (MK_COMB (@lem128611) (@lem128610 n)). Qed.
Lemma lem128614 (t : Prop) : (term72 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem128615 (n : nat) : (term71 n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (@lem128614 (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem128616 (n : nat) : (term70 n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (TRANS (@lem128612 n) (@lem128615 n)). Qed.
Lemma lem128617 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem128618 (n : nat) : (term73 n) = (term74 n).
Proof. exact (MK_COMB (@lem128617) (@lem128616 n)). Qed.
Lemma lem128625 (n : nat) : (term75 n) = (term75 n).
Proof. exact (eq_refl (term75 n)). Qed.
Lemma lem128626 (n : nat) : (term76 n) = (term77 n).
Proof. exact (MK_COMB (@lem128618 n) (@lem128625 n)). Qed.
Lemma lem128629 (n : nat) : (term35 n) = (term78 n).
Proof. exact (MK_COMB (@lem128606 n) (@lem128626 n)). Qed.
Lemma lem128632 (n : nat) : (term78 n) = (term35 n).
Proof. exact (SYM (@lem128629 n)). Qed.
Lemma lem128636 (m : nat) : (term18 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem128489 m) (@lem128488 m)). Qed.
Lemma lem128637 : term79 = (NUMERAL 0).
Proof. exact (@lem128636 term80). Qed.
Lemma lem128638 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem128639 : ((NUMERAL 0) = term79) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem128638) (@lem128637)). Qed.
Lemma lem128641 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem128642 (x : nat) : (x = x) = True.
Proof. exact (@lem128641 nat x). Qed.
Lemma lem128643 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem128642 (NUMERAL 0)). Qed.
Lemma lem128644 : ((NUMERAL 0) = term79) = True.
Proof. exact (TRANS (@lem128639) (@lem128643)). Qed.
Lemma lem128645 : True = ((NUMERAL 0) = term79).
Proof. exact (SYM (@lem128644)). Qed.
Lemma lem128646 : (NUMERAL 0) = term79.
Proof. exact (EQ_MP (@lem128645) (@lem0)). Qed.
Lemma lem128647 : term52.
Proof. exact (ex_intro term82 (NUMERAL 0) (@lem128646)). Qed.
Lemma lem128648 (n : nat) (h1 : term83 n) : term83 n.
Proof. exact (h1). Qed.
Lemma lem128649 (n : nat) (h1 : term84 n) : term84 n.
Proof. exact (h1). Qed.
Lemma lem128650 (n : nat) (h1 : term22 n) : term22 n.
Proof. exact (h1). Qed.
Lemma lem128654 (n : nat) (h1 : term83 n) : term83 n.
Proof. exact (h1). Qed.
Lemma lem128655 (n : nat) (h1 : term22 n) (h2 : term83 n) : term85 n.
Proof. exact (@lem128654 n h2 (@lem128650 n h1)). Qed.
Lemma lem128657 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : Coq.Arith.PeanoNat.Nat.Even n.
Proof. exact (h1). Qed.
Lemma lem128659 (n : nat) (h1 : term84 n) : term84 n.
Proof. exact (h1). Qed.
Lemma lem128660 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) (h2 : term84 n) : term86 n.
Proof. exact (@lem128659 n h2 (@lem128657 n h1)). Qed.
Lemma lem128671 (n : nat) (m : nat) (h1 : n = (term87 m)) : n = (term87 m).
Proof. exact (h1). Qed.
Lemma lem128672 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem128673 (n : nat) (m : nat) (h1 : n = (term87 m)) : (S n) = (term88 m).
Proof. exact (MK_COMB (@lem128672) (@lem128671 n m h1)). Qed.
Lemma lem128674 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem128675 (n : nat) (m : nat) (h1 : n = (term87 m)) : (term89 n) = (term90 m).
Proof. exact (MK_COMB (@lem128674) (@lem128673 n m h1)). Qed.
Lemma lem128676 (m : nat) : (term91 m) = (term91 m).
Proof. exact (eq_refl (term91 m)). Qed.
Lemma lem128677 (n : nat) (m : nat) (h1 : n = (term87 m)) : ((S n) = (term91 m)) = ((term88 m) = (term91 m)).
Proof. exact (MK_COMB (@lem128675 n m h1) (@lem128676 m)). Qed.
Lemma lem128680 (n : nat) (m : nat) (h1 : n = (term87 m)) : ((term88 m) = (term91 m)) = ((S n) = (term91 m)).
Proof. exact (SYM (@lem128677 n m h1)). Qed.
Lemma lem128684 (n : nat) : (term14 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem128459 n) (@lem128458 n)). Qed.
Lemma lem128685 (m : nat) : (term14 m) = (Nat.add m m).
Proof. exact (@lem128684 m). Qed.
Lemma lem128686 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem128687 (m : nat) : (term87 m) = (term92 m).
Proof. exact (MK_COMB (@lem128686) (@lem128685 m)). Qed.
Lemma lem128688 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem128689 (m : nat) : (term88 m) = (term93 m).
Proof. exact (MK_COMB (@lem128688) (@lem128687 m)). Qed.
Lemma lem128690 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem128691 (m : nat) : (term90 m) = (term94 m).
Proof. exact (MK_COMB (@lem128690) (@lem128689 m)). Qed.
Lemma lem128693 (n : nat) : (term14 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem128459 n) (@lem128458 n)). Qed.
Lemma lem128694 (m : nat) : (term91 m) = (term95 m).
Proof. exact (@lem128693 (S m)). Qed.
Lemma lem128695 (m : nat) : ((term88 m) = (term91 m)) = ((term93 m) = (term95 m)).
Proof. exact (MK_COMB (@lem128691 m) (@lem128694 m)). Qed.
Lemma lem128698 (m : nat) : ((term93 m) = (term95 m)) = ((term88 m) = (term91 m)).
Proof. exact (SYM (@lem128695 m)). Qed.
Lemma lem128702 (m : nat) (n : nat) : (term12 m n) = (term7 m n).
Proof. exact (EQ_MP (@lem128448 m n) (@lem128447 m n)). Qed.
Lemma lem128703 (m : nat) : (term95 m) = (term96 m).
Proof. exact (@lem128702 m (S m)). Qed.
Lemma lem128705 (m : nat) (n : nat) : (term6 m n) = (term7 m n).
Proof. exact (EQ_MP (@lem128441 m n) (@lem128440 m n)). Qed.
Lemma lem128706 (m : nat) : (term97 m) = (term92 m).
Proof. exact (@lem128705 m m). Qed.
Lemma lem128707 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem128708 (m : nat) : (term96 m) = (term93 m).
Proof. exact (MK_COMB (@lem128707) (@lem128706 m)). Qed.
Lemma lem128709 (m : nat) : (term95 m) = (term93 m).
Proof. exact (TRANS (@lem128703 m) (@lem128708 m)). Qed.
Lemma lem128710 (m : nat) : (term94 m) = (term94 m).
Proof. exact (eq_refl (term94 m)). Qed.
Lemma lem128711 (m : nat) : ((term93 m) = (term95 m)) = ((term93 m) = (term93 m)).
Proof. exact (MK_COMB (@lem128710 m) (@lem128709 m)). Qed.
Lemma lem128713 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem128714 (x : nat) : (x = x) = True.
Proof. exact (@lem128713 nat x). Qed.
Lemma lem128715 (m : nat) : ((term93 m) = (term93 m)) = True.
Proof. exact (@lem128714 (term93 m)). Qed.
Lemma lem128716 (m : nat) : ((term93 m) = (term95 m)) = True.
Proof. exact (TRANS (@lem128711 m) (@lem128715 m)). Qed.
Lemma lem128717 (m : nat) : True = ((term93 m) = (term95 m)).
Proof. exact (SYM (@lem128716 m)). Qed.
Lemma lem128718 (m : nat) : (term93 m) = (term95 m).
Proof. exact (EQ_MP (@lem128717 m) (@lem0)). Qed.
Lemma lem128719 (m : nat) : (term88 m) = (term91 m).
Proof. exact (EQ_MP (@lem128698 m) (@lem128718 m)). Qed.
Lemma lem128720 (n : nat) (m : nat) (h1 : n = (term87 m)) : (S n) = (term91 m).
Proof. exact (EQ_MP (@lem128680 n m h1) (@lem128719 m)). Qed.
Lemma lem128721 (n : nat) (m : nat) (h1 : n = (term87 m)) : term65 n.
Proof. exact (ex_intro (term98 n) (S m) (@lem128720 n m h1)). Qed.
Lemma lem128729 (n : nat) (m : nat) (h1 : n = (term14 m)) : n = (term14 m).
Proof. exact (h1). Qed.
Lemma lem128730 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem128731 (n : nat) (m : nat) (h1 : n = (term14 m)) : (S n) = (term87 m).
Proof. exact (MK_COMB (@lem128730) (@lem128729 n m h1)). Qed.
Lemma lem128732 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem128733 (n : nat) (m : nat) (h1 : n = (term14 m)) : (term89 n) = (term99 m).
Proof. exact (MK_COMB (@lem128732) (@lem128731 n m h1)). Qed.
Lemma lem128734 (m : nat) : (term87 m) = (term87 m).
Proof. exact (eq_refl (term87 m)). Qed.
Lemma lem128735 (n : nat) (m : nat) (h1 : n = (term14 m)) : ((S n) = (term87 m)) = ((term87 m) = (term87 m)).
Proof. exact (MK_COMB (@lem128733 n m h1) (@lem128734 m)). Qed.
Lemma lem128737 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem128738 (x : nat) : (x = x) = True.
Proof. exact (@lem128737 nat x). Qed.
Lemma lem128739 (m : nat) : ((term87 m) = (term87 m)) = True.
Proof. exact (@lem128738 (term87 m)). Qed.
Lemma lem128740 (n : nat) (m : nat) (h1 : n = (term14 m)) : ((S n) = (term87 m)) = True.
Proof. exact (TRANS (@lem128735 n m h1) (@lem128739 m)). Qed.
Lemma lem128741 (n : nat) (m : nat) (h1 : n = (term14 m)) : True = ((S n) = (term87 m)).
Proof. exact (SYM (@lem128740 n m h1)). Qed.
Lemma lem128742 (n : nat) (m : nat) (h1 : n = (term14 m)) : (S n) = (term87 m).
Proof. exact (EQ_MP (@lem128741 n m h1) (@lem0)). Qed.
Lemma lem128743 (n : nat) (m : nat) (h1 : n = (term14 m)) : term75 n.
Proof. exact (ex_intro (term100 n) m (@lem128742 n m h1)). Qed.
Lemma lem128744 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) (h2 : term84 n) : term75 n.
Proof. exact (ex_elim (@lem128660 n h1 h2) (fun m : nat => fun h0 : term101 n m => @lem128743 n m h0)). Qed.
Lemma lem128745 (n : nat) (h1 : term84 n) : term77 n.
Proof. exact (fun h0 : Coq.Arith.PeanoNat.Nat.Even n => @lem128744 n h0 h1). Qed.
Lemma lem128746 (n : nat) (h1 : term22 n) (h2 : term83 n) : term65 n.
Proof. exact (ex_elim (@lem128655 n h1 h2) (fun m : nat => fun h0 : term102 n m => @lem128721 n m h0)). Qed.
Lemma lem128747 (n : nat) (h1 : term83 n) : term67 n.
Proof. exact (fun h0 : term22 n => @lem128746 n h0 h1). Qed.
Lemma lem128748 (n : nat) (h1 : term84 n) (h2 : term83 n) : term78 n.
Proof. exact (conj (@lem128747 n h2) (@lem128745 n h1)). Qed.
Lemma lem128749 (n : nat) (h1 : term31 n) : term83 n.
Proof. exact (proj2 (@lem128523 n h1)). Qed.
Lemma lem128750 (n : nat) (h1 : term31 n) : term84 n.
Proof. exact (proj1 (@lem128523 n h1)). Qed.
Lemma lem128751 (n : nat) (h1 : term84 n) (h2 : term83 n) : (term83 n) = (term78 n).
Proof. exact (prop_ext (fun h3 : term83 n => @lem128748 n h1 h2) (fun h3 : term78 n => @lem128648 n h2)). Qed.
Lemma lem128752 (n : nat) (h1 : term84 n) (h2 : term83 n) : term78 n.
Proof. exact (EQ_MP (@lem128751 n h1 h2) (@lem128648 n h2)). Qed.
Lemma lem128753 (n : nat) (h1 : term84 n) (h2 : term83 n) : (term84 n) = (term78 n).
Proof. exact (prop_ext (fun h3 : term84 n => @lem128752 n h1 h2) (fun h3 : term78 n => @lem128649 n h1)). Qed.
Lemma lem128754 (n : nat) (h1 : term84 n) (h2 : term83 n) : term78 n.
Proof. exact (EQ_MP (@lem128753 n h1 h2) (@lem128649 n h1)). Qed.
Lemma lem128755 (n : nat) (h1 : term31 n) (h2 : term84 n) : (term83 n) = (term78 n).
Proof. exact (prop_ext (fun h3 : term83 n => @lem128754 n h2 h3) (fun h3 : term78 n => @lem128749 n h1)). Qed.
Lemma lem128756 (n : nat) (h1 : term31 n) (h2 : term84 n) : term78 n.
Proof. exact (EQ_MP (@lem128755 n h1 h2) (@lem128749 n h1)). Qed.
Lemma lem128757 (n : nat) (h1 : term31 n) : (term84 n) = (term78 n).
Proof. exact (prop_ext (fun h2 : term84 n => @lem128756 n h1 h2) (fun h2 : term78 n => @lem128750 n h1)). Qed.
Lemma lem128758 (n : nat) (h1 : term31 n) : term78 n.
Proof. exact (EQ_MP (@lem128757 n h1) (@lem128750 n h1)). Qed.
Lemma lem128759 (n : nat) (h1 : term31 n) : term35 n.
Proof. exact (EQ_MP (@lem128632 n) (@lem128758 n h1)). Qed.
Lemma lem128760 : term27.
Proof. exact (EQ_MP (@lem128586) (@lem128647)). Qed.
Lemma lem128761 (n : nat) : term37 n.
Proof. exact (fun h0 : term31 n => @lem128759 n h0). Qed.
Lemma lem128766 : term41.
Proof. exact (fun n : nat => @lem128761 n). Qed.
Lemma lem128767 : term43.
Proof. exact (conj (@lem128760) (@lem128766)). Qed.
Lemma lem128768 : term48.
Proof. exact (@lem128522 (@lem128767)). Qed.
