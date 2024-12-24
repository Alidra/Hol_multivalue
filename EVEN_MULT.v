Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EVEN_MULT_term_abbrevs.
Require Import EVEN_ADD_spec.
Require Import EVEN_OR_ODD_spec.
Require Import MULT_CLAUSES_spec.
Require Import NOT_EVEN_spec.
Require Import thm0_spec.
Require Import thm124233_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1831_spec.
Require Import thm1832_spec.
Require Import thm1834_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm82_spec.
Lemma lem125498 (n : nat) (h1 : (term0 n) = (Coq.Arith.PeanoNat.Nat.Odd n)) : (term0 n) = (Coq.Arith.PeanoNat.Nat.Odd n).
Proof. exact (h1). Qed.
Lemma lem125499 (n : nat) (h1 : (term0 n) = (Coq.Arith.PeanoNat.Nat.Odd n)) : (Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n).
Proof. exact (SYM (@lem125498 n h1)). Qed.
Lemma lem125500 (n : nat) (h1 : (Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n)) : (Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n).
Proof. exact (h1). Qed.
Lemma lem125501 (n : nat) (h1 : (Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n)) : (term0 n) = (Coq.Arith.PeanoNat.Nat.Odd n).
Proof. exact (SYM (@lem125500 n h1)). Qed.
Lemma lem125502 (n : nat) : ((term0 n) = (Coq.Arith.PeanoNat.Nat.Odd n)) = ((Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n)).
Proof. exact (prop_ext (fun h1 : (term0 n) = (Coq.Arith.PeanoNat.Nat.Odd n) => @lem125499 n h1) (fun h1 : (Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n) => @lem125501 n h1)). Qed.
Lemma lem125503 : term1 = term2.
Proof. exact (fun_ext (fun n : nat => @lem125502 n)). Qed.
Lemma lem125504 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem125505 : term3 = term4.
Proof. exact (MK_COMB (@lem125504) (@lem125503)). Qed.
Lemma lem125506 : term4.
Proof. exact (EQ_MP (@lem125505) (@lem124715)). Qed.
Lemma lem125507 (n : nat) : term5 n.
Proof. exact (@lem125506 n). Qed.
Lemma lem125508 (n : nat) : (term5 n) = ((Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n)).
Proof. exact (eq_refl (term5 n)). Qed.
Lemma lem125510 (p : nat) : term6 p.
Proof. exact (@lem124909 p). Qed.
Lemma lem125511 (p : nat) : (term6 p) = (term7 p).
Proof. exact (eq_refl (term6 p)). Qed.
Lemma lem125512 (p : nat) : term7 p.
Proof. exact (EQ_MP (@lem125511 p) (@lem125510 p)). Qed.
Lemma lem125513 (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : Coq.Arith.PeanoNat.Nat.Even p.
Proof. exact (h1). Qed.
Lemma lem125514 (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd p) : Coq.Arith.PeanoNat.Nat.Odd p.
Proof. exact (h1). Qed.
Lemma lem125515 (n : nat) : term6 n.
Proof. exact (@lem124909 n). Qed.
Lemma lem125516 (n : nat) : (term6 n) = (term7 n).
Proof. exact (eq_refl (term6 n)). Qed.
Lemma lem125517 (n : nat) : term7 n.
Proof. exact (EQ_MP (@lem125516 n) (@lem125515 n)). Qed.
Lemma lem125518 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : Coq.Arith.PeanoNat.Nat.Even n.
Proof. exact (h1). Qed.
Lemma lem125519 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : Coq.Arith.PeanoNat.Nat.Odd n.
Proof. exact (h1). Qed.
Lemma lem125521 (P : nat -> Prop) : term8 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem125522 : term9.
Proof. exact (@lem125521 term10). Qed.
Lemma lem125523 : term11 = term12.
Proof. exact (eq_refl term11). Qed.
Lemma lem125524 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem125525 : term13 = term14.
Proof. exact (MK_COMB (@lem125524) (@lem125523)). Qed.
Lemma lem125526 (m : nat) : (term15 m) = (term16 m).
Proof. exact (eq_refl (term15 m)). Qed.
Lemma lem125527 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem125528 (m : nat) : (term17 m) = (term18 m).
Proof. exact (MK_COMB (@lem125527) (@lem125526 m)). Qed.
Lemma lem125529 (m : nat) : (term19 m) = (term20 m).
Proof. exact (eq_refl (term19 m)). Qed.
Lemma lem125530 (m : nat) : (term21 m) = (term22 m).
Proof. exact (MK_COMB (@lem125528 m) (@lem125529 m)). Qed.
Lemma lem125531 : term23 = term24.
Proof. exact (fun_ext (fun m : nat => @lem125530 m)). Qed.
Lemma lem125532 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem125533 : term25 = term26.
Proof. exact (MK_COMB (@lem125532) (@lem125531)). Qed.
Lemma lem125534 : term27 = term28.
Proof. exact (MK_COMB (@lem125525) (@lem125533)). Qed.
Lemma lem125535 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem125536 : term29 = term30.
Proof. exact (MK_COMB (@lem125535) (@lem125534)). Qed.
Lemma lem125537 (m : nat) : (term15 m) = (term16 m).
Proof. exact (eq_refl (term15 m)). Qed.
Lemma lem125538 : term31 = term10.
Proof. exact (fun_ext (fun m : nat => @lem125537 m)). Qed.
Lemma lem125539 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem125540 : term32 = term33.
Proof. exact (MK_COMB (@lem125539) (@lem125538)). Qed.
Lemma lem125541 : term9 = term34.
Proof. exact (MK_COMB (@lem125536) (@lem125540)). Qed.
Lemma lem125542 : term34.
Proof. exact (EQ_MP (@lem125541) (@lem125522)). Qed.
Lemma lem125543 (m : nat) (h1 : term16 m) : term16 m.
Proof. exact (h1). Qed.
Lemma lem125585 : term35.
Proof. exact (proj1 (@lem81645)). Qed.
Lemma lem125586 (n : nat) : term36 n.
Proof. exact (@lem125585 n). Qed.
Lemma lem125587 (n : nat) : (term36 n) = ((term37 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term36 n)). Qed.
Lemma lem125596 (n : nat) : (term37 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem125587 n) (@lem125586 n)). Qed.
Lemma lem125597 : Coq.Arith.PeanoNat.Nat.Even = Coq.Arith.PeanoNat.Nat.Even.
Proof. exact (eq_refl Coq.Arith.PeanoNat.Nat.Even). Qed.
Lemma lem125598 (n : nat) : (term38 n) = term39.
Proof. exact (MK_COMB (@lem125597) (@lem125596 n)). Qed.
Lemma lem125600 : term39 = True.
Proof. exact (proj1 (@lem124233)). Qed.
Lemma lem125601 (n : nat) : (term38 n) = True.
Proof. exact (TRANS (@lem125598 n) (@lem125600)). Qed.
Lemma lem125602 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem125603 (n : nat) : (term40 n) = (@eq Prop True).
Proof. exact (MK_COMB (@lem125602) (@lem125601 n)). Qed.
Lemma lem125607 : term39 = True.
Proof. exact (proj1 (@lem124233)). Qed.
Lemma lem125608 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem125609 : term41 = (or True).
Proof. exact (MK_COMB (@lem125608) (@lem125607)). Qed.
Lemma lem125610 (n : nat) : (Coq.Arith.PeanoNat.Nat.Even n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (eq_refl (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem125611 (n : nat) : (term42 n) = (term43 n).
Proof. exact (MK_COMB (@lem125609) (@lem125610 n)). Qed.
Lemma lem125613 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem125614 (n : nat) : (term43 n) = True.
Proof. exact (@lem125613 (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem125615 (n : nat) : (term42 n) = True.
Proof. exact (TRANS (@lem125611 n) (@lem125614 n)). Qed.
Lemma lem125616 (n : nat) : ((term38 n) = (term42 n)) = (True = True).
Proof. exact (MK_COMB (@lem125603 n) (@lem125615 n)). Qed.
Lemma lem125618 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem125619 : (True = True) = True.
Proof. exact (@lem125618 True). Qed.
Lemma lem125620 (n : nat) : ((term38 n) = (term42 n)) = True.
Proof. exact (TRANS (@lem125616 n) (@lem125619)). Qed.
Lemma lem125621 : term44 = term45.
Proof. exact (fun_ext (fun n : nat => @lem125620 n)). Qed.
Lemma lem125622 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem125623 : term12 = term46.
Proof. exact (MK_COMB (@lem125622) (@lem125621)). Qed.
Lemma lem125625 {A : Type'} (t : Prop) : (term47 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem125626 (t : Prop) : (term48 t) = t.
Proof. exact (@lem125625 nat t). Qed.
Lemma lem125627 : term46 = True.
Proof. exact (@lem125626 True). Qed.
Lemma lem125628 : term12 = True.
Proof. exact (TRANS (@lem125623) (@lem125627)). Qed.
Lemma lem125629 : True = term12.
Proof. exact (SYM (@lem125628)). Qed.
Lemma lem125630 : term12.
Proof. exact (EQ_MP (@lem125629) (@lem0)). Qed.
Lemma lem125631 : term49.
Proof. exact (proj2 (@lem124233)). Qed.
Lemma lem125632 (n : nat) : term50 n.
Proof. exact (@lem125631 n). Qed.
Lemma lem125633 (n : nat) : (term50 n) = ((term51 n) = (term0 n)).
Proof. exact (eq_refl (term50 n)). Qed.
Lemma lem125636 (m : nat) : term52 m.
Proof. exact (@lem125496 m). Qed.
Lemma lem125637 (m : nat) : (term52 m) = (term53 m).
Proof. exact (eq_refl (term52 m)). Qed.
Lemma lem125638 (m : nat) : term53 m.
Proof. exact (EQ_MP (@lem125637 m) (@lem125636 m)). Qed.
Lemma lem125639 (m : nat) (n : nat) : term54 m n.
Proof. exact (@lem125638 m n). Qed.
Lemma lem125640 (m : nat) (n : nat) : (term54 m n) = ((term55 m n) = ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n))).
Proof. exact (eq_refl (term54 m n)). Qed.
Lemma lem125642 : term56.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem125643 : term57.
Proof. exact (proj2 (@lem125642)). Qed.
Lemma lem125644 : term58.
Proof. exact (proj2 (@lem125643)). Qed.
Lemma lem125645 : term59.
Proof. exact (proj2 (@lem125644)). Qed.
Lemma lem125653 : term60.
Proof. exact (proj1 (@lem125645)). Qed.
Lemma lem125654 (m : nat) : term61 m.
Proof. exact (@lem125653 m). Qed.
Lemma lem125655 (m : nat) : (term61 m) = (term62 m).
Proof. exact (eq_refl (term61 m)). Qed.
Lemma lem125656 (m : nat) : term62 m.
Proof. exact (EQ_MP (@lem125655 m) (@lem125654 m)). Qed.
Lemma lem125657 (m : nat) (n : nat) : term63 m n.
Proof. exact (@lem125656 m n). Qed.
Lemma lem125658 (m : nat) (n : nat) : (term63 m n) = ((term64 m n) = (term65 m n)).
Proof. exact (eq_refl (term63 m n)). Qed.
Lemma lem125676 (n : nat) (m : nat) (h1 : term16 m) : term66 m n.
Proof. exact (@lem125543 m h1 n). Qed.
Lemma lem125677 (m : nat) (n : nat) : (term66 m n) = ((term67 m n) = (term68 m n)).
Proof. exact (eq_refl (term66 m n)). Qed.
Lemma lem125686 (m : nat) (n : nat) : (term64 m n) = (term65 m n).
Proof. exact (EQ_MP (@lem125658 m n) (@lem125657 m n)). Qed.
Lemma lem125687 : Coq.Arith.PeanoNat.Nat.Even = Coq.Arith.PeanoNat.Nat.Even.
Proof. exact (eq_refl Coq.Arith.PeanoNat.Nat.Even). Qed.
Lemma lem125688 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (MK_COMB (@lem125687) (@lem125686 m n)). Qed.
Lemma lem125690 (m : nat) (n : nat) : (term55 m n) = ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n)).
Proof. exact (EQ_MP (@lem125640 m n) (@lem125639 m n)). Qed.
Lemma lem125691 (m : nat) (n : nat) : (term70 m n) = ((term67 m n) = (Coq.Arith.PeanoNat.Nat.Even n)).
Proof. exact (@lem125690 (Nat.mul m n) n). Qed.
Lemma lem125695 (n : nat) (m : nat) (h1 : term16 m) : (term67 m n) = (term68 m n).
Proof. exact (EQ_MP (@lem125677 m n) (@lem125676 n m h1)). Qed.
Lemma lem125698 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem125699 (n : nat) (m : nat) (h1 : term16 m) : (term71 m n) = (term72 m n).
Proof. exact (MK_COMB (@lem125698) (@lem125695 n m h1)). Qed.
Lemma lem125700 (n : nat) : (Coq.Arith.PeanoNat.Nat.Even n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (eq_refl (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem125701 (n : nat) (m : nat) (h1 : term16 m) : ((term67 m n) = (Coq.Arith.PeanoNat.Nat.Even n)) = ((term68 m n) = (Coq.Arith.PeanoNat.Nat.Even n)).
Proof. exact (MK_COMB (@lem125699 n m h1) (@lem125700 n)). Qed.
Lemma lem125704 (n : nat) (m : nat) (h1 : term16 m) : (term70 m n) = ((term68 m n) = (Coq.Arith.PeanoNat.Nat.Even n)).
Proof. exact (TRANS (@lem125691 m n) (@lem125701 n m h1)). Qed.
Lemma lem125705 (n : nat) (m : nat) (h1 : term16 m) : (term69 m n) = ((term68 m n) = (Coq.Arith.PeanoNat.Nat.Even n)).
Proof. exact (TRANS (@lem125688 m n) (@lem125704 n m h1)). Qed.
Lemma lem125706 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem125707 (n : nat) (m : nat) (h1 : term16 m) : (term73 m n) = (term74 m n).
Proof. exact (MK_COMB (@lem125706) (@lem125705 n m h1)). Qed.
Lemma lem125711 (n : nat) : (term51 n) = (term0 n).
Proof. exact (EQ_MP (@lem125633 n) (@lem125632 n)). Qed.
Lemma lem125712 (m : nat) : (term51 m) = (term0 m).
Proof. exact (@lem125711 m). Qed.
Lemma lem125713 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem125714 (m : nat) : (term75 m) = (term76 m).
Proof. exact (MK_COMB (@lem125713) (@lem125712 m)). Qed.
Lemma lem125715 (n : nat) : (Coq.Arith.PeanoNat.Nat.Even n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (eq_refl (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem125716 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (MK_COMB (@lem125714 m) (@lem125715 n)). Qed.
Lemma lem125719 (n : nat) (m : nat) (h1 : term16 m) : ((term69 m n) = (term77 m n)) = (((term68 m n) = (Coq.Arith.PeanoNat.Nat.Even n)) = (term78 m n)).
Proof. exact (MK_COMB (@lem125707 n m h1) (@lem125716 m n)). Qed.
Lemma lem125722 (m : nat) (h1 : term16 m) : (term79 m) = (term80 m).
Proof. exact (fun_ext (fun n : nat => @lem125719 n m h1)). Qed.
Lemma lem125723 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem125724 (m : nat) (h1 : term16 m) : (term20 m) = (term81 m).
Proof. exact (MK_COMB (@lem125723) (@lem125722 m h1)). Qed.
Lemma lem125729 (m : nat) (h1 : term16 m) : (term81 m) = (term20 m).
Proof. exact (SYM (@lem125724 m h1)). Qed.
Lemma lem125747 (n : nat) : (Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n).
Proof. exact (EQ_MP (@lem125508 n) (@lem125507 n)). Qed.
Lemma lem125748 (p : nat) : (Coq.Arith.PeanoNat.Nat.Odd p) = (term0 p).
Proof. exact (@lem125747 p). Qed.
Lemma lem125749 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem125750 (p : nat) : (term82 p) = (term83 p).
Proof. exact (MK_COMB (@lem125749) (@lem125748 p)). Qed.
Lemma lem125761 (n : nat) (m : nat) (p : nat) : (term84 n m p) = (term84 n m p).
Proof. exact (eq_refl (term84 n m p)). Qed.
Lemma lem125762 (n : nat) (m : nat) (p : nat) : (term85 n m p) = (term86 n m p).
Proof. exact (MK_COMB (@lem125750 p) (@lem125761 n m p)). Qed.
Lemma lem125765 (n : nat) (m : nat) (p : nat) : (term86 n m p) = (term85 n m p).
Proof. exact (SYM (@lem125762 n m p)). Qed.
Lemma lem125771 (n : nat) : (Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n).
Proof. exact (EQ_MP (@lem125508 n) (@lem125507 n)). Qed.
Lemma lem125772 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem125773 (n : nat) : (term82 n) = (term83 n).
Proof. exact (MK_COMB (@lem125772) (@lem125771 n)). Qed.
Lemma lem125782 (m : nat) (p : nat) : (((term68 m p) = (Coq.Arith.PeanoNat.Nat.Even p)) = (term78 m p)) = (((term68 m p) = (Coq.Arith.PeanoNat.Nat.Even p)) = (term78 m p)).
Proof. exact (eq_refl (((term68 m p) = (Coq.Arith.PeanoNat.Nat.Even p)) = (term78 m p))). Qed.
Lemma lem125783 (n : nat) (m : nat) (p : nat) : (term87 n m p) = (term88 n m p).
Proof. exact (MK_COMB (@lem125773 n) (@lem125782 m p)). Qed.
Lemma lem125786 (p : nat) : (term89 p) = (term89 p).
Proof. exact (eq_refl (term89 p)). Qed.
Lemma lem125787 (n : nat) (m : nat) (p : nat) : (term90 n m p) = (term91 n m p).
Proof. exact (MK_COMB (@lem125786 p) (@lem125783 n m p)). Qed.
Lemma lem125790 (n : nat) (m : nat) (p : nat) : (term91 n m p) = (term90 n m p).
Proof. exact (SYM (@lem125787 n m p)). Qed.
Lemma lem125794 (n : nat) : (Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n).
Proof. exact (EQ_MP (@lem125508 n) (@lem125507 n)). Qed.
Lemma lem125795 (p : nat) : (Coq.Arith.PeanoNat.Nat.Odd p) = (term0 p).
Proof. exact (@lem125794 p). Qed.
Lemma lem125796 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem125797 (p : nat) : (term82 p) = (term83 p).
Proof. exact (MK_COMB (@lem125796) (@lem125795 p)). Qed.
Lemma lem125801 (n : nat) : (Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n).
Proof. exact (EQ_MP (@lem125508 n) (@lem125507 n)). Qed.
Lemma lem125802 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem125803 (n : nat) : (term82 n) = (term83 n).
Proof. exact (MK_COMB (@lem125802) (@lem125801 n)). Qed.
Lemma lem125812 (m : nat) (p : nat) : (((term68 m p) = (Coq.Arith.PeanoNat.Nat.Even p)) = (term78 m p)) = (((term68 m p) = (Coq.Arith.PeanoNat.Nat.Even p)) = (term78 m p)).
Proof. exact (eq_refl (((term68 m p) = (Coq.Arith.PeanoNat.Nat.Even p)) = (term78 m p))). Qed.
Lemma lem125813 (n : nat) (m : nat) (p : nat) : (term87 n m p) = (term88 n m p).
Proof. exact (MK_COMB (@lem125803 n) (@lem125812 m p)). Qed.
Lemma lem125816 (n : nat) (m : nat) (p : nat) : (term92 n m p) = (term93 n m p).
Proof. exact (MK_COMB (@lem125797 p) (@lem125813 n m p)). Qed.
Lemma lem125819 (n : nat) (m : nat) (p : nat) : (term93 n m p) = (term92 n m p).
Proof. exact (SYM (@lem125816 n m p)). Qed.
Lemma lem125820 (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : Coq.Arith.PeanoNat.Nat.Even p.
Proof. exact (h1). Qed.
Lemma lem125821 (p : nat) (h1 : term0 p) : term0 p.
Proof. exact (h1). Qed.
Lemma lem125822 (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : Coq.Arith.PeanoNat.Nat.Even p.
Proof. exact (h1). Qed.
Lemma lem125823 (p : nat) (h1 : term0 p) : term0 p.
Proof. exact (h1). Qed.
Lemma lem125827 (p : nat) : (Coq.Arith.PeanoNat.Nat.Even p) = ((Coq.Arith.PeanoNat.Nat.Even p) = True).
Proof. exact (@lem7 (Coq.Arith.PeanoNat.Nat.Even p)). Qed.
Lemma lem125838 (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : (Coq.Arith.PeanoNat.Nat.Even p) = True.
Proof. exact (EQ_MP (@lem125827 p) (@lem125820 p h1)). Qed.
Lemma lem125839 (m : nat) : (term94 m) = (term94 m).
Proof. exact (eq_refl (term94 m)). Qed.
Lemma lem125840 (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : (term68 m p) = (term95 m).
Proof. exact (MK_COMB (@lem125839 m) (@lem125838 p h1)). Qed.
Lemma lem125842 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem125843 (m : nat) : (term95 m) = True.
Proof. exact (@lem125842 (Coq.Arith.PeanoNat.Nat.Even m)). Qed.
Lemma lem125844 (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : (term68 m p) = True.
Proof. exact (TRANS (@lem125840 m p h1) (@lem125843 m)). Qed.
Lemma lem125845 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem125846 (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : (term72 m p) = (@eq Prop True).
Proof. exact (MK_COMB (@lem125845) (@lem125844 m p h1)). Qed.
Lemma lem125848 (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : (Coq.Arith.PeanoNat.Nat.Even p) = True.
Proof. exact (EQ_MP (@lem125827 p) (@lem125820 p h1)). Qed.
Lemma lem125849 (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : ((term68 m p) = (Coq.Arith.PeanoNat.Nat.Even p)) = (True = True).
Proof. exact (MK_COMB (@lem125846 m p h1) (@lem125848 p h1)). Qed.
Lemma lem125851 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem125852 : (True = True) = True.
Proof. exact (@lem125851 True). Qed.
Lemma lem125853 (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : ((term68 m p) = (Coq.Arith.PeanoNat.Nat.Even p)) = True.
Proof. exact (TRANS (@lem125849 m p h1) (@lem125852)). Qed.
Lemma lem125854 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem125855 (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : (term74 m p) = (@eq Prop True).
Proof. exact (MK_COMB (@lem125854) (@lem125853 m p h1)). Qed.
Lemma lem125859 (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : (Coq.Arith.PeanoNat.Nat.Even p) = True.
Proof. exact (EQ_MP (@lem125827 p) (@lem125820 p h1)). Qed.
Lemma lem125860 (m : nat) : (term76 m) = (term76 m).
Proof. exact (eq_refl (term76 m)). Qed.
Lemma lem125861 (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : (term78 m p) = (term96 m).
Proof. exact (MK_COMB (@lem125860 m) (@lem125859 p h1)). Qed.
Lemma lem125863 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem125864 (m : nat) : (term96 m) = True.
Proof. exact (@lem125863 (term0 m)). Qed.
Lemma lem125865 (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : (term78 m p) = True.
Proof. exact (TRANS (@lem125861 m p h1) (@lem125864 m)). Qed.
Lemma lem125866 (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : (((term68 m p) = (Coq.Arith.PeanoNat.Nat.Even p)) = (term78 m p)) = (True = True).
Proof. exact (MK_COMB (@lem125855 m p h1) (@lem125865 m p h1)). Qed.
Lemma lem125868 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem125869 : (True = True) = True.
Proof. exact (@lem125868 True). Qed.
Lemma lem125870 (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : (((term68 m p) = (Coq.Arith.PeanoNat.Nat.Even p)) = (term78 m p)) = True.
Proof. exact (TRANS (@lem125866 m p h1) (@lem125869)). Qed.
Lemma lem125871 (n : nat) : (term89 n) = (term89 n).
Proof. exact (eq_refl (term89 n)). Qed.
Lemma lem125872 (m : nat) (n : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : (term84 n m p) = (term97 n).
Proof. exact (MK_COMB (@lem125871 n) (@lem125870 m p h1)). Qed.
Lemma lem125874 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem125875 (n : nat) : (term97 n) = True.
Proof. exact (@lem125874 (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem125876 (n : nat) (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : (term84 n m p) = True.
Proof. exact (TRANS (@lem125872 m n p h1) (@lem125875 n)). Qed.
Lemma lem125877 (n : nat) (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : True = (term84 n m p).
Proof. exact (SYM (@lem125876 n m p h1)). Qed.
Lemma lem125878 (n : nat) (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : term84 n m p.
Proof. exact (EQ_MP (@lem125877 n m p h1) (@lem0)). Qed.
Lemma lem125882 (p : nat) : term98 p.
Proof. exact (@lem82 (Coq.Arith.PeanoNat.Nat.Even p)). Qed.
Lemma lem125893 (p : nat) (h1 : term0 p) : (Coq.Arith.PeanoNat.Nat.Even p) = False.
Proof. exact (@lem125882 p (@lem125821 p h1)). Qed.
Lemma lem125894 (m : nat) : (term94 m) = (term94 m).
Proof. exact (eq_refl (term94 m)). Qed.
Lemma lem125895 (m : nat) (p : nat) (h1 : term0 p) : (term68 m p) = (term99 m).
Proof. exact (MK_COMB (@lem125894 m) (@lem125893 p h1)). Qed.
Lemma lem125897 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem125898 (m : nat) : (term99 m) = (Coq.Arith.PeanoNat.Nat.Even m).
Proof. exact (@lem125897 (Coq.Arith.PeanoNat.Nat.Even m)). Qed.
Lemma lem125899 (m : nat) (p : nat) (h1 : term0 p) : (term68 m p) = (Coq.Arith.PeanoNat.Nat.Even m).
Proof. exact (TRANS (@lem125895 m p h1) (@lem125898 m)). Qed.
Lemma lem125900 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem125901 (m : nat) (p : nat) (h1 : term0 p) : (term72 m p) = (term100 m).
Proof. exact (MK_COMB (@lem125900) (@lem125899 m p h1)). Qed.
Lemma lem125903 (p : nat) (h1 : term0 p) : (Coq.Arith.PeanoNat.Nat.Even p) = False.
Proof. exact (@lem125882 p (@lem125821 p h1)). Qed.
Lemma lem125904 (m : nat) (p : nat) (h1 : term0 p) : ((term68 m p) = (Coq.Arith.PeanoNat.Nat.Even p)) = ((Coq.Arith.PeanoNat.Nat.Even m) = False).
Proof. exact (MK_COMB (@lem125901 m p h1) (@lem125903 p h1)). Qed.
Lemma lem125906 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem125907 (m : nat) : ((Coq.Arith.PeanoNat.Nat.Even m) = False) = (term0 m).
Proof. exact (@lem125906 (Coq.Arith.PeanoNat.Nat.Even m)). Qed.
Lemma lem125908 (m : nat) (p : nat) (h1 : term0 p) : ((term68 m p) = (Coq.Arith.PeanoNat.Nat.Even p)) = (term0 m).
Proof. exact (TRANS (@lem125904 m p h1) (@lem125907 m)). Qed.
Lemma lem125909 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem125910 (m : nat) (p : nat) (h1 : term0 p) : (term74 m p) = (term101 m).
Proof. exact (MK_COMB (@lem125909) (@lem125908 m p h1)). Qed.
Lemma lem125914 (p : nat) (h1 : term0 p) : (Coq.Arith.PeanoNat.Nat.Even p) = False.
Proof. exact (@lem125882 p (@lem125821 p h1)). Qed.
Lemma lem125915 (m : nat) : (term76 m) = (term76 m).
Proof. exact (eq_refl (term76 m)). Qed.
Lemma lem125916 (m : nat) (p : nat) (h1 : term0 p) : (term78 m p) = (term102 m).
Proof. exact (MK_COMB (@lem125915 m) (@lem125914 p h1)). Qed.
Lemma lem125918 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem125919 (m : nat) : (term102 m) = (term0 m).
Proof. exact (@lem125918 (term0 m)). Qed.
Lemma lem125920 (m : nat) (p : nat) (h1 : term0 p) : (term78 m p) = (term0 m).
Proof. exact (TRANS (@lem125916 m p h1) (@lem125919 m)). Qed.
Lemma lem125921 (m : nat) (p : nat) (h1 : term0 p) : (((term68 m p) = (Coq.Arith.PeanoNat.Nat.Even p)) = (term78 m p)) = ((term0 m) = (term0 m)).
Proof. exact (MK_COMB (@lem125910 m p h1) (@lem125920 m p h1)). Qed.
Lemma lem125923 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem125924 (x : Prop) : (x = x) = True.
Proof. exact (@lem125923 Prop x). Qed.
Lemma lem125925 (m : nat) : ((term0 m) = (term0 m)) = True.
Proof. exact (@lem125924 (term0 m)). Qed.
Lemma lem125926 (m : nat) (p : nat) (h1 : term0 p) : (((term68 m p) = (Coq.Arith.PeanoNat.Nat.Even p)) = (term78 m p)) = True.
Proof. exact (TRANS (@lem125921 m p h1) (@lem125925 m)). Qed.
Lemma lem125927 (n : nat) : (term89 n) = (term89 n).
Proof. exact (eq_refl (term89 n)). Qed.
Lemma lem125928 (m : nat) (n : nat) (p : nat) (h1 : term0 p) : (term84 n m p) = (term97 n).
Proof. exact (MK_COMB (@lem125927 n) (@lem125926 m p h1)). Qed.
Lemma lem125930 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem125931 (n : nat) : (term97 n) = True.
Proof. exact (@lem125930 (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem125932 (n : nat) (m : nat) (p : nat) (h1 : term0 p) : (term84 n m p) = True.
Proof. exact (TRANS (@lem125928 m n p h1) (@lem125931 n)). Qed.
Lemma lem125933 (n : nat) (m : nat) (p : nat) (h1 : term0 p) : True = (term84 n m p).
Proof. exact (SYM (@lem125932 n m p h1)). Qed.
Lemma lem125934 (n : nat) (m : nat) (p : nat) (h1 : term0 p) : term84 n m p.
Proof. exact (EQ_MP (@lem125933 n m p h1) (@lem0)). Qed.
Lemma lem125938 (p : nat) : (Coq.Arith.PeanoNat.Nat.Even p) = ((Coq.Arith.PeanoNat.Nat.Even p) = True).
Proof. exact (@lem7 (Coq.Arith.PeanoNat.Nat.Even p)). Qed.
Lemma lem125949 (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : (Coq.Arith.PeanoNat.Nat.Even p) = True.
Proof. exact (EQ_MP (@lem125938 p) (@lem125822 p h1)). Qed.
Lemma lem125950 (m : nat) : (term94 m) = (term94 m).
Proof. exact (eq_refl (term94 m)). Qed.
Lemma lem125951 (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : (term68 m p) = (term95 m).
Proof. exact (MK_COMB (@lem125950 m) (@lem125949 p h1)). Qed.
Lemma lem125953 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem125954 (m : nat) : (term95 m) = True.
Proof. exact (@lem125953 (Coq.Arith.PeanoNat.Nat.Even m)). Qed.
Lemma lem125955 (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : (term68 m p) = True.
Proof. exact (TRANS (@lem125951 m p h1) (@lem125954 m)). Qed.
Lemma lem125956 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem125957 (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : (term72 m p) = (@eq Prop True).
Proof. exact (MK_COMB (@lem125956) (@lem125955 m p h1)). Qed.
Lemma lem125959 (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : (Coq.Arith.PeanoNat.Nat.Even p) = True.
Proof. exact (EQ_MP (@lem125938 p) (@lem125822 p h1)). Qed.
Lemma lem125960 (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : ((term68 m p) = (Coq.Arith.PeanoNat.Nat.Even p)) = (True = True).
Proof. exact (MK_COMB (@lem125957 m p h1) (@lem125959 p h1)). Qed.
Lemma lem125962 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem125963 : (True = True) = True.
Proof. exact (@lem125962 True). Qed.
Lemma lem125964 (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : ((term68 m p) = (Coq.Arith.PeanoNat.Nat.Even p)) = True.
Proof. exact (TRANS (@lem125960 m p h1) (@lem125963)). Qed.
Lemma lem125965 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem125966 (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : (term74 m p) = (@eq Prop True).
Proof. exact (MK_COMB (@lem125965) (@lem125964 m p h1)). Qed.
Lemma lem125970 (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : (Coq.Arith.PeanoNat.Nat.Even p) = True.
Proof. exact (EQ_MP (@lem125938 p) (@lem125822 p h1)). Qed.
Lemma lem125971 (m : nat) : (term76 m) = (term76 m).
Proof. exact (eq_refl (term76 m)). Qed.
Lemma lem125972 (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : (term78 m p) = (term96 m).
Proof. exact (MK_COMB (@lem125971 m) (@lem125970 p h1)). Qed.
Lemma lem125974 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem125975 (m : nat) : (term96 m) = True.
Proof. exact (@lem125974 (term0 m)). Qed.
Lemma lem125976 (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : (term78 m p) = True.
Proof. exact (TRANS (@lem125972 m p h1) (@lem125975 m)). Qed.
Lemma lem125977 (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : (((term68 m p) = (Coq.Arith.PeanoNat.Nat.Even p)) = (term78 m p)) = (True = True).
Proof. exact (MK_COMB (@lem125966 m p h1) (@lem125976 m p h1)). Qed.
Lemma lem125979 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem125980 : (True = True) = True.
Proof. exact (@lem125979 True). Qed.
Lemma lem125981 (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : (((term68 m p) = (Coq.Arith.PeanoNat.Nat.Even p)) = (term78 m p)) = True.
Proof. exact (TRANS (@lem125977 m p h1) (@lem125980)). Qed.
Lemma lem125982 (n : nat) : (term83 n) = (term83 n).
Proof. exact (eq_refl (term83 n)). Qed.
Lemma lem125983 (m : nat) (n : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : (term88 n m p) = (term103 n).
Proof. exact (MK_COMB (@lem125982 n) (@lem125981 m p h1)). Qed.
Lemma lem125985 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem125986 (n : nat) : (term103 n) = True.
Proof. exact (@lem125985 (term0 n)). Qed.
Lemma lem125987 (n : nat) (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : (term88 n m p) = True.
Proof. exact (TRANS (@lem125983 m n p h1) (@lem125986 n)). Qed.
Lemma lem125988 (n : nat) (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : True = (term88 n m p).
Proof. exact (SYM (@lem125987 n m p h1)). Qed.
Lemma lem125989 (n : nat) (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : term88 n m p.
Proof. exact (EQ_MP (@lem125988 n m p h1) (@lem0)). Qed.
Lemma lem125993 (p : nat) : term98 p.
Proof. exact (@lem82 (Coq.Arith.PeanoNat.Nat.Even p)). Qed.
Lemma lem126004 (p : nat) (h1 : term0 p) : (Coq.Arith.PeanoNat.Nat.Even p) = False.
Proof. exact (@lem125993 p (@lem125823 p h1)). Qed.
Lemma lem126005 (m : nat) : (term94 m) = (term94 m).
Proof. exact (eq_refl (term94 m)). Qed.
Lemma lem126006 (m : nat) (p : nat) (h1 : term0 p) : (term68 m p) = (term99 m).
Proof. exact (MK_COMB (@lem126005 m) (@lem126004 p h1)). Qed.
Lemma lem126008 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem126009 (m : nat) : (term99 m) = (Coq.Arith.PeanoNat.Nat.Even m).
Proof. exact (@lem126008 (Coq.Arith.PeanoNat.Nat.Even m)). Qed.
Lemma lem126010 (m : nat) (p : nat) (h1 : term0 p) : (term68 m p) = (Coq.Arith.PeanoNat.Nat.Even m).
Proof. exact (TRANS (@lem126006 m p h1) (@lem126009 m)). Qed.
Lemma lem126011 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem126012 (m : nat) (p : nat) (h1 : term0 p) : (term72 m p) = (term100 m).
Proof. exact (MK_COMB (@lem126011) (@lem126010 m p h1)). Qed.
Lemma lem126014 (p : nat) (h1 : term0 p) : (Coq.Arith.PeanoNat.Nat.Even p) = False.
Proof. exact (@lem125993 p (@lem125823 p h1)). Qed.
Lemma lem126015 (m : nat) (p : nat) (h1 : term0 p) : ((term68 m p) = (Coq.Arith.PeanoNat.Nat.Even p)) = ((Coq.Arith.PeanoNat.Nat.Even m) = False).
Proof. exact (MK_COMB (@lem126012 m p h1) (@lem126014 p h1)). Qed.
Lemma lem126017 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem126018 (m : nat) : ((Coq.Arith.PeanoNat.Nat.Even m) = False) = (term0 m).
Proof. exact (@lem126017 (Coq.Arith.PeanoNat.Nat.Even m)). Qed.
Lemma lem126019 (m : nat) (p : nat) (h1 : term0 p) : ((term68 m p) = (Coq.Arith.PeanoNat.Nat.Even p)) = (term0 m).
Proof. exact (TRANS (@lem126015 m p h1) (@lem126018 m)). Qed.
Lemma lem126020 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem126021 (m : nat) (p : nat) (h1 : term0 p) : (term74 m p) = (term101 m).
Proof. exact (MK_COMB (@lem126020) (@lem126019 m p h1)). Qed.
Lemma lem126025 (p : nat) (h1 : term0 p) : (Coq.Arith.PeanoNat.Nat.Even p) = False.
Proof. exact (@lem125993 p (@lem125823 p h1)). Qed.
Lemma lem126026 (m : nat) : (term76 m) = (term76 m).
Proof. exact (eq_refl (term76 m)). Qed.
Lemma lem126027 (m : nat) (p : nat) (h1 : term0 p) : (term78 m p) = (term102 m).
Proof. exact (MK_COMB (@lem126026 m) (@lem126025 p h1)). Qed.
Lemma lem126029 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem126030 (m : nat) : (term102 m) = (term0 m).
Proof. exact (@lem126029 (term0 m)). Qed.
Lemma lem126031 (m : nat) (p : nat) (h1 : term0 p) : (term78 m p) = (term0 m).
Proof. exact (TRANS (@lem126027 m p h1) (@lem126030 m)). Qed.
Lemma lem126032 (m : nat) (p : nat) (h1 : term0 p) : (((term68 m p) = (Coq.Arith.PeanoNat.Nat.Even p)) = (term78 m p)) = ((term0 m) = (term0 m)).
Proof. exact (MK_COMB (@lem126021 m p h1) (@lem126031 m p h1)). Qed.
Lemma lem126034 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem126035 (x : Prop) : (x = x) = True.
Proof. exact (@lem126034 Prop x). Qed.
Lemma lem126036 (m : nat) : ((term0 m) = (term0 m)) = True.
Proof. exact (@lem126035 (term0 m)). Qed.
Lemma lem126037 (m : nat) (p : nat) (h1 : term0 p) : (((term68 m p) = (Coq.Arith.PeanoNat.Nat.Even p)) = (term78 m p)) = True.
Proof. exact (TRANS (@lem126032 m p h1) (@lem126036 m)). Qed.
Lemma lem126038 (n : nat) : (term83 n) = (term83 n).
Proof. exact (eq_refl (term83 n)). Qed.
Lemma lem126039 (m : nat) (n : nat) (p : nat) (h1 : term0 p) : (term88 n m p) = (term103 n).
Proof. exact (MK_COMB (@lem126038 n) (@lem126037 m p h1)). Qed.
Lemma lem126041 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem126042 (n : nat) : (term103 n) = True.
Proof. exact (@lem126041 (term0 n)). Qed.
Lemma lem126043 (n : nat) (m : nat) (p : nat) (h1 : term0 p) : (term88 n m p) = True.
Proof. exact (TRANS (@lem126039 m n p h1) (@lem126042 n)). Qed.
Lemma lem126044 (n : nat) (m : nat) (p : nat) (h1 : term0 p) : True = (term88 n m p).
Proof. exact (SYM (@lem126043 n m p h1)). Qed.
Lemma lem126045 (n : nat) (m : nat) (p : nat) (h1 : term0 p) : term88 n m p.
Proof. exact (EQ_MP (@lem126044 n m p h1) (@lem0)). Qed.
Lemma lem126046 (n : nat) (m : nat) (p : nat) : term93 n m p.
Proof. exact (fun h0 : term0 p => @lem126045 n m p h0). Qed.
Lemma lem126047 (n : nat) (m : nat) (p : nat) : term91 n m p.
Proof. exact (fun h0 : Coq.Arith.PeanoNat.Nat.Even p => @lem125989 n m p h0). Qed.
Lemma lem126048 (n : nat) (m : nat) (p : nat) : term86 n m p.
Proof. exact (fun h0 : term0 p => @lem125934 n m p h0). Qed.
Lemma lem126050 (n : nat) (m : nat) (p : nat) : term92 n m p.
Proof. exact (EQ_MP (@lem125819 n m p) (@lem126046 n m p)). Qed.
Lemma lem126051 (n : nat) (m : nat) (p : nat) : term90 n m p.
Proof. exact (EQ_MP (@lem125790 n m p) (@lem126047 n m p)). Qed.
Lemma lem126052 (n : nat) (m : nat) (p : nat) : term85 n m p.
Proof. exact (EQ_MP (@lem125765 n m p) (@lem126048 n m p)). Qed.
Lemma lem126053 (n : nat) (m : nat) (p : nat) : term104 n m p.
Proof. exact (fun h0 : Coq.Arith.PeanoNat.Nat.Even p => @lem125878 n m p h0). Qed.
Lemma lem126054 (n : nat) (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd p) : term87 n m p.
Proof. exact (@lem126050 n m p (@lem125514 p h1)). Qed.
Lemma lem126055 (n : nat) (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : term87 n m p.
Proof. exact (@lem126051 n m p (@lem125513 p h1)). Qed.
Lemma lem126056 (n : nat) (m : nat) (p : nat) : term87 n m p.
Proof. exact (or_elim (@lem125512 p) (fun h0 : Coq.Arith.PeanoNat.Nat.Even p => @lem126055 n m p h0) (fun h0 : Coq.Arith.PeanoNat.Nat.Odd p => @lem126054 n m p h0)). Qed.
Lemma lem126057 (n : nat) (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd p) : term84 n m p.
Proof. exact (@lem126052 n m p (@lem125514 p h1)). Qed.
Lemma lem126058 (n : nat) (m : nat) (p : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even p) : term84 n m p.
Proof. exact (@lem126053 n m p (@lem125513 p h1)). Qed.
Lemma lem126059 (n : nat) (m : nat) (p : nat) : term84 n m p.
Proof. exact (or_elim (@lem125512 p) (fun h0 : Coq.Arith.PeanoNat.Nat.Even p => @lem126058 n m p h0) (fun h0 : Coq.Arith.PeanoNat.Nat.Odd p => @lem126057 n m p h0)). Qed.
Lemma lem126060 (m : nat) (p : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Odd n) : ((term68 m p) = (Coq.Arith.PeanoNat.Nat.Even p)) = (term78 m p).
Proof. exact (@lem126056 n m p (@lem125519 n h1)). Qed.
Lemma lem126061 (m : nat) (p : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : ((term68 m p) = (Coq.Arith.PeanoNat.Nat.Even p)) = (term78 m p).
Proof. exact (@lem126059 n m p (@lem125518 n h1)). Qed.
Lemma lem126062 (m : nat) (p : nat) : ((term68 m p) = (Coq.Arith.PeanoNat.Nat.Even p)) = (term78 m p).
Proof. exact (or_elim (@lem125517 (@el nat)) (fun h0 : Coq.Arith.PeanoNat.Nat.Even (@el nat) => @lem126061 m p (@el nat) h0) (fun h0 : Coq.Arith.PeanoNat.Nat.Odd (@el nat) => @lem126060 m p (@el nat) h0)). Qed.
Lemma lem126067 (m : nat) : term81 m.
Proof. exact (fun p : nat => @lem126062 m p). Qed.
Lemma lem126068 (m : nat) (h1 : term16 m) : term20 m.
Proof. exact (EQ_MP (@lem125729 m h1) (@lem126067 m)). Qed.
Lemma lem126069 (m : nat) : term22 m.
Proof. exact (fun h0 : term16 m => @lem126068 m h0). Qed.
Lemma lem126074 : term26.
Proof. exact (fun m : nat => @lem126069 m). Qed.
Lemma lem126075 : term28.
Proof. exact (conj (@lem125630) (@lem126074)). Qed.
Lemma lem126076 : term33.
Proof. exact (@lem125542 (@lem126075)). Qed.
