Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUB_ADD_LCANCEL_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import SUB_SUC_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Lemma lem136496 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem136497 : term1.
Proof. exact (@lem136496 term2). Qed.
Lemma lem136498 : term3 = term4.
Proof. exact (eq_refl term3). Qed.
Lemma lem136499 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem136500 : term5 = term6.
Proof. exact (MK_COMB (@lem136499) (@lem136498)). Qed.
Lemma lem136501 (m : nat) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem136502 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem136503 (m : nat) : (term9 m) = (term10 m).
Proof. exact (MK_COMB (@lem136502) (@lem136501 m)). Qed.
Lemma lem136504 (m : nat) : (term11 m) = (term12 m).
Proof. exact (eq_refl (term11 m)). Qed.
Lemma lem136505 (m : nat) : (term13 m) = (term14 m).
Proof. exact (MK_COMB (@lem136503 m) (@lem136504 m)). Qed.
Lemma lem136506 : term15 = term16.
Proof. exact (fun_ext (fun m : nat => @lem136505 m)). Qed.
Lemma lem136507 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem136508 : term17 = term18.
Proof. exact (MK_COMB (@lem136507) (@lem136506)). Qed.
Lemma lem136509 : term19 = term20.
Proof. exact (MK_COMB (@lem136500) (@lem136508)). Qed.
Lemma lem136510 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem136511 : term21 = term22.
Proof. exact (MK_COMB (@lem136510) (@lem136509)). Qed.
Lemma lem136512 (m : nat) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem136513 : term23 = term2.
Proof. exact (fun_ext (fun m : nat => @lem136512 m)). Qed.
Lemma lem136514 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem136515 : term24 = term25.
Proof. exact (MK_COMB (@lem136514) (@lem136513)). Qed.
Lemma lem136516 : term1 = term26.
Proof. exact (MK_COMB (@lem136511) (@lem136515)). Qed.
Lemma lem136517 : term26.
Proof. exact (EQ_MP (@lem136516) (@lem136497)). Qed.
Lemma lem136518 (m : nat) (h1 : term8 m) : term8 m.
Proof. exact (h1). Qed.
Lemma lem136550 : term27.
Proof. exact (proj1 (@lem77629)). Qed.
Lemma lem136551 (n : nat) : term28 n.
Proof. exact (@lem136550 n). Qed.
Lemma lem136552 (n : nat) : (term28 n) = ((term29 n) = n).
Proof. exact (eq_refl (term28 n)). Qed.
Lemma lem136565 (n : nat) : (term29 n) = n.
Proof. exact (EQ_MP (@lem136552 n) (@lem136551 n)). Qed.
Lemma lem136566 : Nat.sub = Nat.sub.
Proof. exact (eq_refl Nat.sub). Qed.
Lemma lem136567 (n : nat) : (term30 n) = (Nat.sub n).
Proof. exact (MK_COMB (@lem136566) (@lem136565 n)). Qed.
Lemma lem136569 (n : nat) : (term29 n) = n.
Proof. exact (EQ_MP (@lem136552 n) (@lem136551 n)). Qed.
Lemma lem136570 (p : nat) : (term29 p) = p.
Proof. exact (@lem136569 p). Qed.
Lemma lem136571 (n : nat) (p : nat) : (term31 n p) = (Nat.sub n p).
Proof. exact (MK_COMB (@lem136567 n) (@lem136570 p)). Qed.
Lemma lem136572 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem136573 (n : nat) (p : nat) : (term32 n p) = (term33 n p).
Proof. exact (MK_COMB (@lem136572) (@lem136571 n p)). Qed.
Lemma lem136574 (n : nat) (p : nat) : (Nat.sub n p) = (Nat.sub n p).
Proof. exact (eq_refl (Nat.sub n p)). Qed.
Lemma lem136575 (n : nat) (p : nat) : ((term31 n p) = (Nat.sub n p)) = ((Nat.sub n p) = (Nat.sub n p)).
Proof. exact (MK_COMB (@lem136573 n p) (@lem136574 n p)). Qed.
Lemma lem136577 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem136578 (x : nat) : (x = x) = True.
Proof. exact (@lem136577 nat x). Qed.
Lemma lem136579 (n : nat) (p : nat) : ((Nat.sub n p) = (Nat.sub n p)) = True.
Proof. exact (@lem136578 (Nat.sub n p)). Qed.
Lemma lem136580 (n : nat) (p : nat) : ((term31 n p) = (Nat.sub n p)) = True.
Proof. exact (TRANS (@lem136575 n p) (@lem136579 n p)). Qed.
Lemma lem136581 (n : nat) : (term34 n) = term35.
Proof. exact (fun_ext (fun p : nat => @lem136580 n p)). Qed.
Lemma lem136582 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem136583 (n : nat) : (term36 n) = term37.
Proof. exact (MK_COMB (@lem136582) (@lem136581 n)). Qed.
Lemma lem136585 {A : Type'} (t : Prop) : (term38 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem136586 (t : Prop) : (term39 t) = t.
Proof. exact (@lem136585 nat t). Qed.
Lemma lem136587 : term37 = True.
Proof. exact (@lem136586 True). Qed.
Lemma lem136588 (n : nat) : (term36 n) = True.
Proof. exact (TRANS (@lem136583 n) (@lem136587)). Qed.
Lemma lem136589 : term40 = term35.
Proof. exact (fun_ext (fun n : nat => @lem136588 n)). Qed.
Lemma lem136590 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem136591 : term4 = term37.
Proof. exact (MK_COMB (@lem136590) (@lem136589)). Qed.
Lemma lem136593 {A : Type'} (t : Prop) : (term38 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem136594 (t : Prop) : (term39 t) = t.
Proof. exact (@lem136593 nat t). Qed.
Lemma lem136595 : term37 = True.
Proof. exact (@lem136594 True). Qed.
Lemma lem136596 : term4 = True.
Proof. exact (TRANS (@lem136591) (@lem136595)). Qed.
Lemma lem136597 : True = term4.
Proof. exact (SYM (@lem136596)). Qed.
Lemma lem136598 : term4.
Proof. exact (EQ_MP (@lem136597) (@lem0)). Qed.
Lemma lem136599 (m : nat) : term41 m.
Proof. exact (@lem135645 m). Qed.
Lemma lem136600 (m : nat) : (term41 m) = (term42 m).
Proof. exact (eq_refl (term41 m)). Qed.
Lemma lem136601 (m : nat) : term42 m.
Proof. exact (EQ_MP (@lem136600 m) (@lem136599 m)). Qed.
Lemma lem136602 (m : nat) (n : nat) : term43 m n.
Proof. exact (@lem136601 m n). Qed.
Lemma lem136603 (m : nat) (n : nat) : (term43 m n) = ((term44 m n) = (Nat.sub m n)).
Proof. exact (eq_refl (term43 m n)). Qed.
Lemma lem136610 : term45.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem136611 : term46.
Proof. exact (proj2 (@lem136610)). Qed.
Lemma lem136619 : term47.
Proof. exact (proj1 (@lem136611)). Qed.
Lemma lem136620 (m : nat) : term48 m.
Proof. exact (@lem136619 m). Qed.
Lemma lem136621 (m : nat) : (term48 m) = (term49 m).
Proof. exact (eq_refl (term48 m)). Qed.
Lemma lem136622 (m : nat) : term49 m.
Proof. exact (EQ_MP (@lem136621 m) (@lem136620 m)). Qed.
Lemma lem136623 (m : nat) (n : nat) : term50 m n.
Proof. exact (@lem136622 m n). Qed.
Lemma lem136624 (m : nat) (n : nat) : (term50 m n) = ((term51 m n) = (term52 m n)).
Proof. exact (eq_refl (term50 m n)). Qed.
Lemma lem136634 (n : nat) (m : nat) (h1 : term8 m) : term53 m n.
Proof. exact (@lem136518 m h1 n). Qed.
Lemma lem136635 (m : nat) (n : nat) : (term53 m n) = (term54 m n).
Proof. exact (eq_refl (term53 m n)). Qed.
Lemma lem136636 (n : nat) (m : nat) (h1 : term8 m) : term54 m n.
Proof. exact (EQ_MP (@lem136635 m n) (@lem136634 n m h1)). Qed.
Lemma lem136637 (n : nat) (p : nat) (m : nat) (h1 : term8 m) : term55 m n p.
Proof. exact (@lem136636 n m h1 p). Qed.
Lemma lem136638 (m : nat) (n : nat) (p : nat) : (term55 m n p) = ((term56 n m p) = (Nat.sub n p)).
Proof. exact (eq_refl (term55 m n p)). Qed.
Lemma lem136651 (m : nat) (n : nat) : (term51 m n) = (term52 m n).
Proof. exact (EQ_MP (@lem136624 m n) (@lem136623 m n)). Qed.
Lemma lem136652 : Nat.sub = Nat.sub.
Proof. exact (eq_refl Nat.sub). Qed.
Lemma lem136653 (m : nat) (n : nat) : (term57 m n) = (term58 m n).
Proof. exact (MK_COMB (@lem136652) (@lem136651 m n)). Qed.
Lemma lem136655 (m : nat) (n : nat) : (term51 m n) = (term52 m n).
Proof. exact (EQ_MP (@lem136624 m n) (@lem136623 m n)). Qed.
Lemma lem136656 (m : nat) (p : nat) : (term51 m p) = (term52 m p).
Proof. exact (@lem136655 m p). Qed.
Lemma lem136657 (n : nat) (m : nat) (p : nat) : (term59 n m p) = (term60 n m p).
Proof. exact (MK_COMB (@lem136653 m n) (@lem136656 m p)). Qed.
Lemma lem136659 (m : nat) (n : nat) : (term44 m n) = (Nat.sub m n).
Proof. exact (EQ_MP (@lem136603 m n) (@lem136602 m n)). Qed.
Lemma lem136660 (n : nat) (m : nat) (p : nat) : (term60 n m p) = (term56 n m p).
Proof. exact (@lem136659 (Nat.add m n) (Nat.add m p)). Qed.
Lemma lem136662 (n : nat) (p : nat) (m : nat) (h1 : term8 m) : (term56 n m p) = (Nat.sub n p).
Proof. exact (EQ_MP (@lem136638 m n p) (@lem136637 n p m h1)). Qed.
Lemma lem136663 (n : nat) (p : nat) (m : nat) (h1 : term8 m) : (term60 n m p) = (Nat.sub n p).
Proof. exact (TRANS (@lem136660 n m p) (@lem136662 n p m h1)). Qed.
Lemma lem136664 (n : nat) (p : nat) (m : nat) (h1 : term8 m) : (term59 n m p) = (Nat.sub n p).
Proof. exact (TRANS (@lem136657 n m p) (@lem136663 n p m h1)). Qed.
Lemma lem136665 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem136666 (n : nat) (p : nat) (m : nat) (h1 : term8 m) : (term61 n m p) = (term33 n p).
Proof. exact (MK_COMB (@lem136665) (@lem136664 n p m h1)). Qed.
Lemma lem136667 (n : nat) (p : nat) : (Nat.sub n p) = (Nat.sub n p).
Proof. exact (eq_refl (Nat.sub n p)). Qed.
Lemma lem136668 (n : nat) (p : nat) (m : nat) (h1 : term8 m) : ((term59 n m p) = (Nat.sub n p)) = ((Nat.sub n p) = (Nat.sub n p)).
Proof. exact (MK_COMB (@lem136666 n p m h1) (@lem136667 n p)). Qed.
Lemma lem136670 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem136671 (x : nat) : (x = x) = True.
Proof. exact (@lem136670 nat x). Qed.
Lemma lem136672 (n : nat) (p : nat) : ((Nat.sub n p) = (Nat.sub n p)) = True.
Proof. exact (@lem136671 (Nat.sub n p)). Qed.
Lemma lem136673 (n : nat) (p : nat) (m : nat) (h1 : term8 m) : ((term59 n m p) = (Nat.sub n p)) = True.
Proof. exact (TRANS (@lem136668 n p m h1) (@lem136672 n p)). Qed.
Lemma lem136674 (n : nat) (m : nat) (h1 : term8 m) : (term62 m n) = term35.
Proof. exact (fun_ext (fun p : nat => @lem136673 n p m h1)). Qed.
Lemma lem136675 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem136676 (n : nat) (m : nat) (h1 : term8 m) : (term63 m n) = term37.
Proof. exact (MK_COMB (@lem136675) (@lem136674 n m h1)). Qed.
Lemma lem136678 {A : Type'} (t : Prop) : (term38 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem136679 (t : Prop) : (term39 t) = t.
Proof. exact (@lem136678 nat t). Qed.
Lemma lem136680 : term37 = True.
Proof. exact (@lem136679 True). Qed.
Lemma lem136681 (n : nat) (m : nat) (h1 : term8 m) : (term63 m n) = True.
Proof. exact (TRANS (@lem136676 n m h1) (@lem136680)). Qed.
Lemma lem136682 (m : nat) (h1 : term8 m) : (term64 m) = term35.
Proof. exact (fun_ext (fun n : nat => @lem136681 n m h1)). Qed.
Lemma lem136683 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem136684 (m : nat) (h1 : term8 m) : (term12 m) = term37.
Proof. exact (MK_COMB (@lem136683) (@lem136682 m h1)). Qed.
Lemma lem136686 {A : Type'} (t : Prop) : (term38 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem136687 (t : Prop) : (term39 t) = t.
Proof. exact (@lem136686 nat t). Qed.
Lemma lem136688 : term37 = True.
Proof. exact (@lem136687 True). Qed.
Lemma lem136689 (m : nat) (h1 : term8 m) : (term12 m) = True.
Proof. exact (TRANS (@lem136684 m h1) (@lem136688)). Qed.
Lemma lem136690 (m : nat) (h1 : term8 m) : True = (term12 m).
Proof. exact (SYM (@lem136689 m h1)). Qed.
Lemma lem136691 (m : nat) (h1 : term8 m) : term12 m.
Proof. exact (EQ_MP (@lem136690 m h1) (@lem0)). Qed.
Lemma lem136692 (m : nat) : term14 m.
Proof. exact (fun h0 : term8 m => @lem136691 m h0). Qed.
Lemma lem136697 : term18.
Proof. exact (fun m : nat => @lem136692 m). Qed.
Lemma lem136698 : term20.
Proof. exact (conj (@lem136598) (@lem136697)). Qed.
Lemma lem136699 : term25.
Proof. exact (@lem136517 (@lem136698)). Qed.
