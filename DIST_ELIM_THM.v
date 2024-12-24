Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIST_ELIM_THM_term_abbrevs.
Require Import ADD_ASSOC_spec.
Require Import ADD_CLAUSES_spec.
Require Import ADD_EQ_0_spec.
Require Import ADD_SUB2_spec.
Require Import ADD_SUBR2_spec.
Require Import EQ_ADD_LCANCEL_spec.
Require Import EQ_ADD_LCANCEL_0_spec.
Require Import EQ_SYM_EQ_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import LE_CASES_spec.
Require Import LE_EXISTS_spec.
Require Import dist_spec.
Require Import thm0_spec.
Require Import thm1822_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1844_spec.
Require Import thm1845_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm32_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem1245574 (e : nat) : term0 e.
Proof. exact (@lem9784 (e = (NUMERAL 0))). Qed.
Lemma lem1245575 (e : nat) : (term0 e) = (term1 e).
Proof. exact (eq_refl (term0 e)). Qed.
Lemma lem1245576 (e : nat) : term1 e.
Proof. exact (EQ_MP (@lem1245575 e) (@lem1245574 e)). Qed.
Lemma lem1245578 (e : nat) (h1 : term2 e) : term2 e.
Proof. exact (h1). Qed.
Lemma lem1245582 (m : nat) (n : nat) (p : nat) (h1 : (term3 m n p) = (term4 m n p)) : (term3 m n p) = (term4 m n p).
Proof. exact (h1). Qed.
Lemma lem1245583 (m : nat) (n : nat) (p : nat) (h1 : (term3 m n p) = (term4 m n p)) : (term4 m n p) = (term3 m n p).
Proof. exact (SYM (@lem1245582 m n p h1)). Qed.
Lemma lem1245584 (m : nat) (n : nat) (p : nat) (h1 : (term4 m n p) = (term3 m n p)) : (term4 m n p) = (term3 m n p).
Proof. exact (h1). Qed.
Lemma lem1245585 (m : nat) (n : nat) (p : nat) (h1 : (term4 m n p) = (term3 m n p)) : (term3 m n p) = (term4 m n p).
Proof. exact (SYM (@lem1245584 m n p h1)). Qed.
Lemma lem1245586 (m : nat) (n : nat) (p : nat) : ((term3 m n p) = (term4 m n p)) = ((term4 m n p) = (term3 m n p)).
Proof. exact (prop_ext (fun h1 : (term3 m n p) = (term4 m n p) => @lem1245583 m n p h1) (fun h1 : (term4 m n p) = (term3 m n p) => @lem1245585 m n p h1)). Qed.
Lemma lem1245587 (m : nat) (n : nat) : (term5 m n) = (term6 m n).
Proof. exact (fun_ext (fun p : nat => @lem1245586 m n p)). Qed.
Lemma lem1245588 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1245589 (m : nat) (n : nat) : (term7 m n) = (term8 m n).
Proof. exact (MK_COMB (@lem1245588) (@lem1245587 m n)). Qed.
Lemma lem1245590 (m : nat) : (term9 m) = (term10 m).
Proof. exact (fun_ext (fun n : nat => @lem1245589 m n)). Qed.
Lemma lem1245591 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1245592 (m : nat) : (term11 m) = (term12 m).
Proof. exact (MK_COMB (@lem1245591) (@lem1245590 m)). Qed.
Lemma lem1245593 : term13 = term14.
Proof. exact (fun_ext (fun m : nat => @lem1245592 m)). Qed.
Lemma lem1245594 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1245595 : term15 = term16.
Proof. exact (MK_COMB (@lem1245594) (@lem1245593)). Qed.
Lemma lem1245596 : term16.
Proof. exact (EQ_MP (@lem1245595) (@lem77960)). Qed.
Lemma lem1245597 (m : nat) : term17 m.
Proof. exact (@lem79432 m). Qed.
Lemma lem1245598 (m : nat) : (term17 m) = (term18 m).
Proof. exact (eq_refl (term17 m)). Qed.
Lemma lem1245599 (m : nat) : term18 m.
Proof. exact (EQ_MP (@lem1245598 m) (@lem1245597 m)). Qed.
Lemma lem1245600 (m : nat) (n : nat) : term19 m n.
Proof. exact (@lem1245599 m n). Qed.
Lemma lem1245601 (m : nat) (n : nat) : (term19 m n) = (((Nat.add m n) = (NUMERAL 0)) = (term20 m n)).
Proof. exact (eq_refl (term19 m n)). Qed.
Lemma lem1245603 (m : nat) : term21 m.
Proof. exact (@lem79890 m). Qed.
Lemma lem1245604 (m : nat) : (term21 m) = (term22 m).
Proof. exact (eq_refl (term21 m)). Qed.
Lemma lem1245605 (m : nat) : term22 m.
Proof. exact (EQ_MP (@lem1245604 m) (@lem1245603 m)). Qed.
Lemma lem1245606 (m : nat) (n : nat) : term23 m n.
Proof. exact (@lem1245605 m n). Qed.
Lemma lem1245607 (m : nat) (n : nat) : (term23 m n) = (((Nat.add m n) = m) = (n = (NUMERAL 0))).
Proof. exact (eq_refl (term23 m n)). Qed.
Lemma lem1245609 (m : nat) : term24 m.
Proof. exact (@lem1245596 m). Qed.
Lemma lem1245610 (m : nat) : (term24 m) = (term12 m).
Proof. exact (eq_refl (term24 m)). Qed.
Lemma lem1245611 (m : nat) : term12 m.
Proof. exact (EQ_MP (@lem1245610 m) (@lem1245609 m)). Qed.
Lemma lem1245612 (m : nat) (n : nat) : term25 m n.
Proof. exact (@lem1245611 m n). Qed.
Lemma lem1245613 (m : nat) (n : nat) : (term25 m n) = (term8 m n).
Proof. exact (eq_refl (term25 m n)). Qed.
Lemma lem1245614 (m : nat) (n : nat) : term8 m n.
Proof. exact (EQ_MP (@lem1245613 m n) (@lem1245612 m n)). Qed.
Lemma lem1245615 (m : nat) (n : nat) (p : nat) : term26 m n p.
Proof. exact (@lem1245614 m n p). Qed.
Lemma lem1245616 (m : nat) (n : nat) (p : nat) : (term26 m n p) = ((term4 m n p) = (term3 m n p)).
Proof. exact (eq_refl (term26 m n p)). Qed.
Lemma lem1245618 {A : Type'} (x : A) : term27 A x.
Proof. exact (@lem362 A x). Qed.
Lemma lem1245619 {A : Type'} (x : A) : (term27 A x) = (term28 A x).
Proof. exact (eq_refl (term27 A x)). Qed.
Lemma lem1245620 {A : Type'} (x : A) : term28 A x.
Proof. exact (EQ_MP (@lem1245619 A x) (@lem1245618 A x)). Qed.
Lemma lem1245621 {A : Type'} (x : A) (y : A) : term29 A x y.
Proof. exact (@lem1245620 A x y). Qed.
Lemma lem1245622 {A : Type'} (y : A) (x : A) : (term29 A x y) = ((x = y) = (y = x)).
Proof. exact (eq_refl (term29 A x y)). Qed.
Lemma lem1245624 (m : nat) : term30 m.
Proof. exact (@lem79639 m). Qed.
Lemma lem1245625 (m : nat) : (term30 m) = (term31 m).
Proof. exact (eq_refl (term30 m)). Qed.
Lemma lem1245626 (m : nat) : term31 m.
Proof. exact (EQ_MP (@lem1245625 m) (@lem1245624 m)). Qed.
Lemma lem1245627 (m : nat) (n : nat) : term32 m n.
Proof. exact (@lem1245626 m n). Qed.
Lemma lem1245628 (m : nat) (n : nat) : (term32 m n) = (term33 m n).
Proof. exact (eq_refl (term32 m n)). Qed.
Lemma lem1245629 (m : nat) (n : nat) : term33 m n.
Proof. exact (EQ_MP (@lem1245628 m n) (@lem1245627 m n)). Qed.
Lemma lem1245630 (m : nat) (n : nat) (p : nat) : term34 m n p.
Proof. exact (@lem1245629 m n p). Qed.
Lemma lem1245631 (m : nat) (n : nat) (p : nat) : (term34 m n p) = (((Nat.add m n) = (Nat.add m p)) = (n = p)).
Proof. exact (eq_refl (term34 m n p)). Qed.
Lemma lem1245633 : term35.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem1245649 : term36.
Proof. exact (proj1 (@lem1245633)). Qed.
Lemma lem1245650 (m : nat) : term37 m.
Proof. exact (@lem1245649 m). Qed.
Lemma lem1245651 (m : nat) : (term37 m) = ((term38 m) = m).
Proof. exact (eq_refl (term37 m)). Qed.
Lemma lem1245653 : term39.
Proof. exact (proj1 (@lem77629)). Qed.
Lemma lem1245654 (n : nat) : term40 n.
Proof. exact (@lem1245653 n). Qed.
Lemma lem1245655 (n : nat) : (term40 n) = ((term41 n) = n).
Proof. exact (eq_refl (term40 n)). Qed.
Lemma lem1245657 (m : nat) : term42 m.
Proof. exact (@lem136305 m). Qed.
Lemma lem1245658 (m : nat) : (term42 m) = (term43 m).
Proof. exact (eq_refl (term42 m)). Qed.
Lemma lem1245659 (m : nat) : term43 m.
Proof. exact (EQ_MP (@lem1245658 m) (@lem1245657 m)). Qed.
Lemma lem1245660 (m : nat) (n : nat) : term44 m n.
Proof. exact (@lem1245659 m n). Qed.
Lemma lem1245661 (m : nat) (n : nat) : (term44 m n) = ((term45 m n) = (NUMERAL 0)).
Proof. exact (eq_refl (term44 m n)). Qed.
Lemma lem1245669 (m : nat) : term46 m.
Proof. exact (@lem135939 m). Qed.
Lemma lem1245670 (m : nat) : (term46 m) = (term47 m).
Proof. exact (eq_refl (term46 m)). Qed.
Lemma lem1245671 (m : nat) : term47 m.
Proof. exact (EQ_MP (@lem1245670 m) (@lem1245669 m)). Qed.
Lemma lem1245672 (m : nat) (n : nat) : term48 m n.
Proof. exact (@lem1245671 m n). Qed.
Lemma lem1245673 (m : nat) (n : nat) : (term48 m n) = ((term49 n m) = n).
Proof. exact (eq_refl (term48 m n)). Qed.
Lemma lem1245681 (n : nat) : term50 n.
Proof. exact (@lem1244710 n). Qed.
Lemma lem1245682 (n : nat) : (term50 n) = (term51 n).
Proof. exact (eq_refl (term50 n)). Qed.
Lemma lem1245683 (n : nat) : term51 n.
Proof. exact (EQ_MP (@lem1245682 n) (@lem1245681 n)). Qed.
Lemma lem1245684 (n : nat) (m : nat) : term52 n m.
Proof. exact (@lem1245683 n m). Qed.
Lemma lem1245685 (n : nat) (m : nat) : (term52 n m) = ((term53 m n) = (term54 n m)).
Proof. exact (eq_refl (term52 n m)). Qed.
Lemma lem1245687 (m : nat) : term55 m.
Proof. exact (@lem99708 m). Qed.
Lemma lem1245688 (m : nat) : (term55 m) = (term56 m).
Proof. exact (eq_refl (term55 m)). Qed.
Lemma lem1245689 (m : nat) : term56 m.
Proof. exact (EQ_MP (@lem1245688 m) (@lem1245687 m)). Qed.
Lemma lem1245690 (m : nat) (n : nat) : term57 m n.
Proof. exact (@lem1245689 m n). Qed.
Lemma lem1245691 (n : nat) (m : nat) : (term57 m n) = ((Peano.le m n) = (term58 n m)).
Proof. exact (eq_refl (term57 m n)). Qed.
Lemma lem1245693 (x : nat) : term59 x.
Proof. exact (@lem96155 x). Qed.
Lemma lem1245694 (x : nat) : (term59 x) = (term60 x).
Proof. exact (eq_refl (term59 x)). Qed.
Lemma lem1245695 (x : nat) : term60 x.
Proof. exact (EQ_MP (@lem1245694 x) (@lem1245693 x)). Qed.
Lemma lem1245696 (x : nat) (y : nat) : term61 x y.
Proof. exact (@lem1245695 x y). Qed.
Lemma lem1245697 (y : nat) (x : nat) : (term61 x y) = (term62 y x).
Proof. exact (eq_refl (term61 x y)). Qed.
Lemma lem1245698 (y : nat) (x : nat) : term62 y x.
Proof. exact (EQ_MP (@lem1245697 y x) (@lem1245696 x y)). Qed.
Lemma lem1245699 (x : nat) (y : nat) (h1 : Peano.le x y) : Peano.le x y.
Proof. exact (h1). Qed.
Lemma lem1245700 (y : nat) (x : nat) (h1 : Peano.le y x) : Peano.le y x.
Proof. exact (h1). Qed.
Lemma lem1245702 (n : nat) (m : nat) : (Peano.le m n) = (term58 n m).
Proof. exact (EQ_MP (@lem1245691 n m) (@lem1245690 m n)). Qed.
Lemma lem1245703 (y : nat) (x : nat) : (Peano.le x y) = (term58 y x).
Proof. exact (@lem1245702 y x). Qed.
Lemma lem1245710 (x : nat) (y : nat) (h1 : Peano.le x y) : term58 y x.
Proof. exact (EQ_MP (@lem1245703 y x) (@lem1245699 x y h1)). Qed.
Lemma lem1245711 (y : nat) (x : nat) (e : nat) (h1 : y = (Nat.add x e)) : y = (Nat.add x e).
Proof. exact (h1). Qed.
Lemma lem1245712 (x : nat) (P : nat -> Prop) : (term63 x P) = (term63 x P).
Proof. exact (eq_refl (term63 x P)). Qed.
Lemma lem1245713 (P : nat -> Prop) (y : nat) (x : nat) (e : nat) (h1 : y = (Nat.add x e)) : (term64 x P y) = (term65 P x e).
Proof. exact (MK_COMB (@lem1245712 x P) (@lem1245711 y x e h1)). Qed.
Lemma lem1245714 (e : nat) (x : nat) (P : nat -> Prop) : (term65 P x e) = ((term66 P x e) = (term67 e x P)).
Proof. exact (eq_refl (term65 P x e)). Qed.
Lemma lem1245715 (x : nat) (P : nat -> Prop) (y : nat) : (term68 x P y) = (term68 x P y).
Proof. exact (eq_refl (term68 x P y)). Qed.
Lemma lem1245716 (y : nat) (e : nat) (x : nat) (P : nat -> Prop) : ((term64 x P y) = (term65 P x e)) = ((term64 x P y) = ((term66 P x e) = (term67 e x P))).
Proof. exact (MK_COMB (@lem1245715 x P y) (@lem1245714 e x P)). Qed.
Lemma lem1245717 (y : nat) (x : nat) (P : nat -> Prop) : (term64 x P y) = ((term69 P x y) = (term70 y x P)).
Proof. exact (eq_refl (term64 x P y)). Qed.
Lemma lem1245718 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1245719 (y : nat) (x : nat) (P : nat -> Prop) : (term68 x P y) = (term71 y x P).
Proof. exact (MK_COMB (@lem1245718) (@lem1245717 y x P)). Qed.
Lemma lem1245720 (e : nat) (x : nat) (P : nat -> Prop) : ((term66 P x e) = (term67 e x P)) = ((term66 P x e) = (term67 e x P)).
Proof. exact (eq_refl ((term66 P x e) = (term67 e x P))). Qed.
Lemma lem1245721 (y : nat) (e : nat) (x : nat) (P : nat -> Prop) : ((term64 x P y) = ((term66 P x e) = (term67 e x P))) = (((term69 P x y) = (term70 y x P)) = ((term66 P x e) = (term67 e x P))).
Proof. exact (MK_COMB (@lem1245719 y x P) (@lem1245720 e x P)). Qed.
Lemma lem1245722 (y : nat) (e : nat) (x : nat) (P : nat -> Prop) : ((term64 x P y) = (term65 P x e)) = (((term69 P x y) = (term70 y x P)) = ((term66 P x e) = (term67 e x P))).
Proof. exact (TRANS (@lem1245716 y e x P) (@lem1245721 y e x P)). Qed.
Lemma lem1245723 (P : nat -> Prop) (y : nat) (x : nat) (e : nat) (h1 : y = (Nat.add x e)) : ((term69 P x y) = (term70 y x P)) = ((term66 P x e) = (term67 e x P)).
Proof. exact (EQ_MP (@lem1245722 y e x P) (@lem1245713 P y x e h1)). Qed.
Lemma lem1245724 (P : nat -> Prop) (y : nat) (x : nat) (e : nat) (h1 : y = (Nat.add x e)) : ((term66 P x e) = (term67 e x P)) = ((term69 P x y) = (term70 y x P)).
Proof. exact (SYM (@lem1245723 P y x e h1)). Qed.
Lemma lem1245726 (n : nat) (m : nat) : (Peano.le m n) = (term58 n m).
Proof. exact (EQ_MP (@lem1245691 n m) (@lem1245690 m n)). Qed.
Lemma lem1245727 (x : nat) (y : nat) : (Peano.le y x) = (term58 x y).
Proof. exact (@lem1245726 x y). Qed.
Lemma lem1245734 (y : nat) (x : nat) (h1 : Peano.le y x) : term58 x y.
Proof. exact (EQ_MP (@lem1245727 x y) (@lem1245700 y x h1)). Qed.
Lemma lem1245735 (x : nat) (y : nat) (e : nat) (h1 : x = (Nat.add y e)) : x = (Nat.add y e).
Proof. exact (h1). Qed.
Lemma lem1245736 (y : nat) (P : nat -> Prop) : (term72 y P) = (term72 y P).
Proof. exact (eq_refl (term72 y P)). Qed.
Lemma lem1245737 (P : nat -> Prop) (x : nat) (y : nat) (e : nat) (h1 : x = (Nat.add y e)) : (term73 y P x) = (term74 P y e).
Proof. exact (MK_COMB (@lem1245736 y P) (@lem1245735 x y e h1)). Qed.
Lemma lem1245738 (y : nat) (e : nat) (P : nat -> Prop) : (term74 P y e) = ((term75 P e y) = (term76 y e P)).
Proof. exact (eq_refl (term74 P y e)). Qed.
Lemma lem1245739 (y : nat) (P : nat -> Prop) (x : nat) : (term77 y P x) = (term77 y P x).
Proof. exact (eq_refl (term77 y P x)). Qed.
Lemma lem1245740 (x : nat) (y : nat) (e : nat) (P : nat -> Prop) : ((term73 y P x) = (term74 P y e)) = ((term73 y P x) = ((term75 P e y) = (term76 y e P))).
Proof. exact (MK_COMB (@lem1245739 y P x) (@lem1245738 y e P)). Qed.
Lemma lem1245741 (y : nat) (x : nat) (P : nat -> Prop) : (term73 y P x) = ((term69 P x y) = (term70 y x P)).
Proof. exact (eq_refl (term73 y P x)). Qed.
Lemma lem1245742 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1245743 (y : nat) (x : nat) (P : nat -> Prop) : (term77 y P x) = (term71 y x P).
Proof. exact (MK_COMB (@lem1245742) (@lem1245741 y x P)). Qed.
Lemma lem1245744 (y : nat) (e : nat) (P : nat -> Prop) : ((term75 P e y) = (term76 y e P)) = ((term75 P e y) = (term76 y e P)).
Proof. exact (eq_refl ((term75 P e y) = (term76 y e P))). Qed.
Lemma lem1245745 (x : nat) (y : nat) (e : nat) (P : nat -> Prop) : ((term73 y P x) = ((term75 P e y) = (term76 y e P))) = (((term69 P x y) = (term70 y x P)) = ((term75 P e y) = (term76 y e P))).
Proof. exact (MK_COMB (@lem1245743 y x P) (@lem1245744 y e P)). Qed.
Lemma lem1245746 (x : nat) (y : nat) (e : nat) (P : nat -> Prop) : ((term73 y P x) = (term74 P y e)) = (((term69 P x y) = (term70 y x P)) = ((term75 P e y) = (term76 y e P))).
Proof. exact (TRANS (@lem1245740 x y e P) (@lem1245745 x y e P)). Qed.
Lemma lem1245747 (P : nat -> Prop) (x : nat) (y : nat) (e : nat) (h1 : x = (Nat.add y e)) : ((term69 P x y) = (term70 y x P)) = ((term75 P e y) = (term76 y e P)).
Proof. exact (EQ_MP (@lem1245746 x y e P) (@lem1245737 P x y e h1)). Qed.
Lemma lem1245748 (P : nat -> Prop) (x : nat) (y : nat) (e : nat) (h1 : x = (Nat.add y e)) : ((term75 P e y) = (term76 y e P)) = ((term69 P x y) = (term70 y x P)).
Proof. exact (SYM (@lem1245747 P x y e h1)). Qed.
Lemma lem1245752 (n : nat) (m : nat) : (term53 m n) = (term54 n m).
Proof. exact (EQ_MP (@lem1245685 n m) (@lem1245684 n m)). Qed.
Lemma lem1245753 (e : nat) (x : nat) : (term78 x e) = (term79 e x).
Proof. exact (@lem1245752 (Nat.add x e) x). Qed.
Lemma lem1245755 (m : nat) (n : nat) : (term45 m n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem1245661 m n) (@lem1245660 m n)). Qed.
Lemma lem1245756 (x : nat) (e : nat) : (term45 x e) = (NUMERAL 0).
Proof. exact (@lem1245755 x e). Qed.
Lemma lem1245757 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1245758 (x : nat) (e : nat) : (term80 x e) = term81.
Proof. exact (MK_COMB (@lem1245757) (@lem1245756 x e)). Qed.
Lemma lem1245760 (m : nat) (n : nat) : (term49 n m) = n.
Proof. exact (EQ_MP (@lem1245673 m n) (@lem1245672 m n)). Qed.
Lemma lem1245761 (x : nat) (e : nat) : (term49 e x) = e.
Proof. exact (@lem1245760 x e). Qed.
Lemma lem1245762 (x : nat) (e : nat) : (term79 e x) = (term41 e).
Proof. exact (MK_COMB (@lem1245758 x e) (@lem1245761 x e)). Qed.
Lemma lem1245763 (x : nat) (e : nat) : (term78 x e) = (term41 e).
Proof. exact (TRANS (@lem1245753 e x) (@lem1245762 x e)). Qed.
Lemma lem1245764 (P : nat -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1245765 (x : nat) (P : nat -> Prop) (e : nat) : (term66 P x e) = (term82 P e).
Proof. exact (MK_COMB (@lem1245764 P) (@lem1245763 x e)). Qed.
Lemma lem1245766 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1245767 (x : nat) (P : nat -> Prop) (e : nat) : (term83 P x e) = (term84 P e).
Proof. exact (MK_COMB (@lem1245766) (@lem1245765 x P e)). Qed.
Lemma lem1245786 (e : nat) (x : nat) (P : nat -> Prop) : (term67 e x P) = (term67 e x P).
Proof. exact (eq_refl (term67 e x P)). Qed.
Lemma lem1245787 (e : nat) (x : nat) (P : nat -> Prop) : ((term66 P x e) = (term67 e x P)) = ((term82 P e) = (term67 e x P)).
Proof. exact (MK_COMB (@lem1245767 x P e) (@lem1245786 e x P)). Qed.
Lemma lem1245790 (e : nat) (x : nat) (P : nat -> Prop) : ((term82 P e) = (term67 e x P)) = ((term66 P x e) = (term67 e x P)).
Proof. exact (SYM (@lem1245787 e x P)). Qed.
Lemma lem1245794 (n : nat) (m : nat) : (term53 m n) = (term54 n m).
Proof. exact (EQ_MP (@lem1245685 n m) (@lem1245684 n m)). Qed.
Lemma lem1245795 (y : nat) (e : nat) : (term85 e y) = (term86 y e).
Proof. exact (@lem1245794 y (Nat.add y e)). Qed.
Lemma lem1245797 (m : nat) (n : nat) : (term49 n m) = n.
Proof. exact (EQ_MP (@lem1245673 m n) (@lem1245672 m n)). Qed.
Lemma lem1245798 (y : nat) (e : nat) : (term49 e y) = e.
Proof. exact (@lem1245797 y e). Qed.
Lemma lem1245799 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1245800 (y : nat) (e : nat) : (term87 e y) = (Nat.add e).
Proof. exact (MK_COMB (@lem1245799) (@lem1245798 y e)). Qed.
Lemma lem1245802 (m : nat) (n : nat) : (term45 m n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem1245661 m n) (@lem1245660 m n)). Qed.
Lemma lem1245803 (y : nat) (e : nat) : (term45 y e) = (NUMERAL 0).
Proof. exact (@lem1245802 y e). Qed.
Lemma lem1245804 (y : nat) (e : nat) : (term86 y e) = (term38 e).
Proof. exact (MK_COMB (@lem1245800 y e) (@lem1245803 y e)). Qed.
Lemma lem1245805 (y : nat) (e : nat) : (term85 e y) = (term38 e).
Proof. exact (TRANS (@lem1245795 y e) (@lem1245804 y e)). Qed.
Lemma lem1245806 (P : nat -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1245807 (y : nat) (P : nat -> Prop) (e : nat) : (term75 P e y) = (term88 P e).
Proof. exact (MK_COMB (@lem1245806 P) (@lem1245805 y e)). Qed.
Lemma lem1245808 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1245809 (y : nat) (P : nat -> Prop) (e : nat) : (term89 P e y) = (term90 P e).
Proof. exact (MK_COMB (@lem1245808) (@lem1245807 y P e)). Qed.
Lemma lem1245828 (y : nat) (e : nat) (P : nat -> Prop) : (term76 y e P) = (term76 y e P).
Proof. exact (eq_refl (term76 y e P)). Qed.
Lemma lem1245829 (y : nat) (e : nat) (P : nat -> Prop) : ((term75 P e y) = (term76 y e P)) = ((term88 P e) = (term76 y e P)).
Proof. exact (MK_COMB (@lem1245809 y P e) (@lem1245828 y e P)). Qed.
Lemma lem1245832 (y : nat) (e : nat) (P : nat -> Prop) : ((term88 P e) = (term76 y e P)) = ((term75 P e y) = (term76 y e P)).
Proof. exact (SYM (@lem1245829 y e P)). Qed.
Lemma lem1245836 (n : nat) : (term41 n) = n.
Proof. exact (EQ_MP (@lem1245655 n) (@lem1245654 n)). Qed.
Lemma lem1245837 (e : nat) : (term41 e) = e.
Proof. exact (@lem1245836 e). Qed.
Lemma lem1245838 (P : nat -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1245839 (P : nat -> Prop) (e : nat) : (term82 P e) = (P e).
Proof. exact (MK_COMB (@lem1245838 P) (@lem1245837 e)). Qed.
Lemma lem1245840 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1245841 (P : nat -> Prop) (e : nat) : (term84 P e) = (term91 P e).
Proof. exact (MK_COMB (@lem1245840) (@lem1245839 P e)). Qed.
Lemma lem1245859 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1245631 m n p) (@lem1245630 m n p)). Qed.
Lemma lem1245860 (x : nat) (e : nat) (d : nat) : ((Nat.add x e) = (Nat.add x d)) = (e = d).
Proof. exact (@lem1245859 x e d). Qed.
Lemma lem1245863 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1245864 (x : nat) (e : nat) (d : nat) : (term92 e x d) = (term93 e d).
Proof. exact (MK_COMB (@lem1245863) (@lem1245860 x e d)). Qed.
Lemma lem1245865 (P : nat -> Prop) (d : nat) : (P d) = (P d).
Proof. exact (eq_refl (P d)). Qed.
Lemma lem1245866 (x : nat) (e : nat) (P : nat -> Prop) (d : nat) : (term94 e x P d) = (term95 e P d).
Proof. exact (MK_COMB (@lem1245864 x e d) (@lem1245865 P d)). Qed.
Lemma lem1245871 (x : nat) (e : nat) (P : nat -> Prop) (d : nat) : (term96 x e P d) = (term96 x e P d).
Proof. exact (eq_refl (term96 x e P d)). Qed.
Lemma lem1245872 (x : nat) (e : nat) (P : nat -> Prop) (d : nat) : (term97 e x P d) = (term98 x e P d).
Proof. exact (MK_COMB (@lem1245871 x e P d) (@lem1245866 x e P d)). Qed.
Lemma lem1245875 (x : nat) (e : nat) (P : nat -> Prop) : (term99 e x P) = (term100 x e P).
Proof. exact (fun_ext (fun d : nat => @lem1245872 x e P d)). Qed.
Lemma lem1245876 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1245877 (x : nat) (e : nat) (P : nat -> Prop) : (term67 e x P) = (term101 x e P).
Proof. exact (MK_COMB (@lem1245876) (@lem1245875 x e P)). Qed.
Lemma lem1245882 (x : nat) (e : nat) (P : nat -> Prop) : ((term82 P e) = (term67 e x P)) = ((P e) = (term101 x e P)).
Proof. exact (MK_COMB (@lem1245841 P e) (@lem1245877 x e P)). Qed.
Lemma lem1245885 (e : nat) (x : nat) (P : nat -> Prop) : ((P e) = (term101 x e P)) = ((term82 P e) = (term67 e x P)).
Proof. exact (SYM (@lem1245882 x e P)). Qed.
Lemma lem1245889 (m : nat) : (term38 m) = m.
Proof. exact (EQ_MP (@lem1245651 m) (@lem1245650 m)). Qed.
Lemma lem1245890 (e : nat) : (term38 e) = e.
Proof. exact (@lem1245889 e). Qed.
Lemma lem1245891 (P : nat -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1245892 (P : nat -> Prop) (e : nat) : (term88 P e) = (P e).
Proof. exact (MK_COMB (@lem1245891 P) (@lem1245890 e)). Qed.
Lemma lem1245893 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1245894 (P : nat -> Prop) (e : nat) : (term90 P e) = (term91 P e).
Proof. exact (MK_COMB (@lem1245893) (@lem1245892 P e)). Qed.
Lemma lem1245906 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1245631 m n p) (@lem1245630 m n p)). Qed.
Lemma lem1245907 (y : nat) (e : nat) (d : nat) : ((Nat.add y e) = (Nat.add y d)) = (e = d).
Proof. exact (@lem1245906 y e d). Qed.
Lemma lem1245910 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1245911 (y : nat) (e : nat) (d : nat) : (term92 e y d) = (term93 e d).
Proof. exact (MK_COMB (@lem1245910) (@lem1245907 y e d)). Qed.
Lemma lem1245912 (P : nat -> Prop) (d : nat) : (P d) = (P d).
Proof. exact (eq_refl (P d)). Qed.
Lemma lem1245913 (y : nat) (e : nat) (P : nat -> Prop) (d : nat) : (term94 e y P d) = (term95 e P d).
Proof. exact (MK_COMB (@lem1245911 y e d) (@lem1245912 P d)). Qed.
Lemma lem1245918 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1245919 (y : nat) (e : nat) (P : nat -> Prop) (d : nat) : (term102 e y P d) = (term103 e P d).
Proof. exact (MK_COMB (@lem1245918) (@lem1245913 y e P d)). Qed.
Lemma lem1245926 (y : nat) (e : nat) (P : nat -> Prop) (d : nat) : (term104 y e P d) = (term104 y e P d).
Proof. exact (eq_refl (term104 y e P d)). Qed.
Lemma lem1245927 (y : nat) (e : nat) (P : nat -> Prop) (d : nat) : (term105 y e P d) = (term106 y e P d).
Proof. exact (MK_COMB (@lem1245919 y e P d) (@lem1245926 y e P d)). Qed.
Lemma lem1245930 (y : nat) (e : nat) (P : nat -> Prop) : (term107 y e P) = (term108 y e P).
Proof. exact (fun_ext (fun d : nat => @lem1245927 y e P d)). Qed.
Lemma lem1245931 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1245932 (y : nat) (e : nat) (P : nat -> Prop) : (term76 y e P) = (term109 y e P).
Proof. exact (MK_COMB (@lem1245931) (@lem1245930 y e P)). Qed.
Lemma lem1245937 (y : nat) (e : nat) (P : nat -> Prop) : ((term88 P e) = (term76 y e P)) = ((P e) = (term109 y e P)).
Proof. exact (MK_COMB (@lem1245894 P e) (@lem1245932 y e P)). Qed.
Lemma lem1245940 (y : nat) (e : nat) (P : nat -> Prop) : ((P e) = (term109 y e P)) = ((term88 P e) = (term76 y e P)).
Proof. exact (SYM (@lem1245937 y e P)). Qed.
Lemma lem1245942 {A : Type'} (y : A) (x : A) : (x = y) = (y = x).
Proof. exact (EQ_MP (@lem1245622 A y x) (@lem1245621 A x y)). Qed.
Lemma lem1245943 (y : nat) (x : nat) : (x = y) = (y = x).
Proof. exact (@lem1245942 nat y x). Qed.
Lemma lem1245944 (e : nat) (d : nat) (x : nat) : (x = (term4 x e d)) = ((term4 x e d) = x).
Proof. exact (@lem1245943 (term4 x e d) x). Qed.
Lemma lem1245945 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1245946 (e : nat) (d : nat) (x : nat) : (term110 x e d) = (term111 e d x).
Proof. exact (MK_COMB (@lem1245945) (@lem1245944 e d x)). Qed.
Lemma lem1245947 (P : nat -> Prop) (d : nat) : (P d) = (P d).
Proof. exact (eq_refl (P d)). Qed.
Lemma lem1245948 (e : nat) (x : nat) (P : nat -> Prop) (d : nat) : (term104 x e P d) = (term112 e x P d).
Proof. exact (MK_COMB (@lem1245946 e d x) (@lem1245947 P d)). Qed.
Lemma lem1245949 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1245950 (e : nat) (x : nat) (P : nat -> Prop) (d : nat) : (term96 x e P d) = (term113 e x P d).
Proof. exact (MK_COMB (@lem1245949) (@lem1245948 e x P d)). Qed.
Lemma lem1245952 {A : Type'} (y : A) (x : A) : (x = y) = (y = x).
Proof. exact (EQ_MP (@lem1245622 A y x) (@lem1245621 A x y)). Qed.
Lemma lem1245953 (y : nat) (x : nat) : (x = y) = (y = x).
Proof. exact (@lem1245952 nat y x). Qed.
Lemma lem1245954 (d : nat) (e : nat) : (e = d) = (d = e).
Proof. exact (@lem1245953 d e). Qed.
Lemma lem1245955 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1245956 (d : nat) (e : nat) : (term93 e d) = (term93 d e).
Proof. exact (MK_COMB (@lem1245955) (@lem1245954 d e)). Qed.
Lemma lem1245957 (P : nat -> Prop) (d : nat) : (P d) = (P d).
Proof. exact (eq_refl (P d)). Qed.
Lemma lem1245958 (e : nat) (P : nat -> Prop) (d : nat) : (term95 e P d) = (term114 e P d).
Proof. exact (MK_COMB (@lem1245956 d e) (@lem1245957 P d)). Qed.
Lemma lem1245959 (x : nat) (e : nat) (P : nat -> Prop) (d : nat) : (term98 x e P d) = (term115 x e P d).
Proof. exact (MK_COMB (@lem1245950 e x P d) (@lem1245958 e P d)). Qed.
Lemma lem1245960 (x : nat) (e : nat) (P : nat -> Prop) : (term100 x e P) = (term116 x e P).
Proof. exact (fun_ext (fun d : nat => @lem1245959 x e P d)). Qed.
Lemma lem1245961 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1245962 (x : nat) (e : nat) (P : nat -> Prop) : (term101 x e P) = (term117 x e P).
Proof. exact (MK_COMB (@lem1245961) (@lem1245960 x e P)). Qed.
Lemma lem1245963 (P : nat -> Prop) (e : nat) : (term91 P e) = (term91 P e).
Proof. exact (eq_refl (term91 P e)). Qed.
Lemma lem1245964 (x : nat) (e : nat) (P : nat -> Prop) : ((P e) = (term101 x e P)) = ((P e) = (term117 x e P)).
Proof. exact (MK_COMB (@lem1245963 P e) (@lem1245962 x e P)). Qed.
Lemma lem1245965 (x : nat) (e : nat) (P : nat -> Prop) : ((P e) = (term117 x e P)) = ((P e) = (term101 x e P)).
Proof. exact (SYM (@lem1245964 x e P)). Qed.
Lemma lem1245967 {A : Type'} (y : A) (x : A) : (x = y) = (y = x).
Proof. exact (EQ_MP (@lem1245622 A y x) (@lem1245621 A x y)). Qed.
Lemma lem1245968 (y : nat) (x : nat) : (x = y) = (y = x).
Proof. exact (@lem1245967 nat y x). Qed.
Lemma lem1245969 (d : nat) (e : nat) : (e = d) = (d = e).
Proof. exact (@lem1245968 d e). Qed.
Lemma lem1245970 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1245971 (d : nat) (e : nat) : (term93 e d) = (term93 d e).
Proof. exact (MK_COMB (@lem1245970) (@lem1245969 d e)). Qed.
Lemma lem1245972 (P : nat -> Prop) (d : nat) : (P d) = (P d).
Proof. exact (eq_refl (P d)). Qed.
Lemma lem1245973 (e : nat) (P : nat -> Prop) (d : nat) : (term95 e P d) = (term114 e P d).
Proof. exact (MK_COMB (@lem1245971 d e) (@lem1245972 P d)). Qed.
Lemma lem1245974 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1245975 (e : nat) (P : nat -> Prop) (d : nat) : (term103 e P d) = (term118 e P d).
Proof. exact (MK_COMB (@lem1245974) (@lem1245973 e P d)). Qed.
Lemma lem1245977 {A : Type'} (y : A) (x : A) : (x = y) = (y = x).
Proof. exact (EQ_MP (@lem1245622 A y x) (@lem1245621 A x y)). Qed.
Lemma lem1245978 (y : nat) (x : nat) : (x = y) = (y = x).
Proof. exact (@lem1245977 nat y x). Qed.
Lemma lem1245979 (e : nat) (d : nat) (y : nat) : (y = (term4 y e d)) = ((term4 y e d) = y).
Proof. exact (@lem1245978 (term4 y e d) y). Qed.
Lemma lem1245980 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1245981 (e : nat) (d : nat) (y : nat) : (term110 y e d) = (term111 e d y).
Proof. exact (MK_COMB (@lem1245980) (@lem1245979 e d y)). Qed.
Lemma lem1245982 (P : nat -> Prop) (d : nat) : (P d) = (P d).
Proof. exact (eq_refl (P d)). Qed.
Lemma lem1245983 (e : nat) (y : nat) (P : nat -> Prop) (d : nat) : (term104 y e P d) = (term112 e y P d).
Proof. exact (MK_COMB (@lem1245981 e d y) (@lem1245982 P d)). Qed.
Lemma lem1245984 (e : nat) (y : nat) (P : nat -> Prop) (d : nat) : (term106 y e P d) = (term119 e y P d).
Proof. exact (MK_COMB (@lem1245975 e P d) (@lem1245983 e y P d)). Qed.
Lemma lem1245985 (e : nat) (y : nat) (P : nat -> Prop) : (term108 y e P) = (term120 e y P).
Proof. exact (fun_ext (fun d : nat => @lem1245984 e y P d)). Qed.
Lemma lem1245986 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1245987 (e : nat) (y : nat) (P : nat -> Prop) : (term109 y e P) = (term121 e y P).
Proof. exact (MK_COMB (@lem1245986) (@lem1245985 e y P)). Qed.
Lemma lem1245988 (P : nat -> Prop) (e : nat) : (term91 P e) = (term91 P e).
Proof. exact (eq_refl (term91 P e)). Qed.
Lemma lem1245989 (e : nat) (y : nat) (P : nat -> Prop) : ((P e) = (term109 y e P)) = ((P e) = (term121 e y P)).
Proof. exact (MK_COMB (@lem1245988 P e) (@lem1245987 e y P)). Qed.
Lemma lem1245990 (y : nat) (e : nat) (P : nat -> Prop) : ((P e) = (term121 e y P)) = ((P e) = (term109 y e P)).
Proof. exact (SYM (@lem1245989 e y P)). Qed.
Lemma lem1246008 (m : nat) (n : nat) (p : nat) : (term4 m n p) = (term3 m n p).
Proof. exact (EQ_MP (@lem1245616 m n p) (@lem1245615 m n p)). Qed.
Lemma lem1246009 (x : nat) (e : nat) (d : nat) : (term4 x e d) = (term3 x e d).
Proof. exact (@lem1246008 x e d). Qed.
Lemma lem1246010 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1246011 (x : nat) (e : nat) (d : nat) : (term122 x e d) = (term123 x e d).
Proof. exact (MK_COMB (@lem1246010) (@lem1246009 x e d)). Qed.
Lemma lem1246012 (x : nat) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1246013 (e : nat) (d : nat) (x : nat) : ((term4 x e d) = x) = ((term3 x e d) = x).
Proof. exact (MK_COMB (@lem1246011 x e d) (@lem1246012 x)). Qed.
Lemma lem1246015 (m : nat) (n : nat) : ((Nat.add m n) = m) = (n = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1245607 m n) (@lem1245606 m n)). Qed.
Lemma lem1246016 (x : nat) (e : nat) (d : nat) : ((term3 x e d) = x) = ((Nat.add e d) = (NUMERAL 0)).
Proof. exact (@lem1246015 x (Nat.add e d)). Qed.
Lemma lem1246018 (m : nat) (n : nat) : ((Nat.add m n) = (NUMERAL 0)) = (term20 m n).
Proof. exact (EQ_MP (@lem1245601 m n) (@lem1245600 m n)). Qed.
Lemma lem1246019 (e : nat) (d : nat) : ((Nat.add e d) = (NUMERAL 0)) = (term20 e d).
Proof. exact (@lem1246018 e d). Qed.
Lemma lem1246026 (x : nat) (e : nat) (d : nat) : ((term3 x e d) = x) = (term20 e d).
Proof. exact (TRANS (@lem1246016 x e d) (@lem1246019 e d)). Qed.
Lemma lem1246027 (x : nat) (e : nat) (d : nat) : ((term4 x e d) = x) = (term20 e d).
Proof. exact (TRANS (@lem1246013 e d x) (@lem1246026 x e d)). Qed.
Lemma lem1246028 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1246029 (x : nat) (e : nat) (d : nat) : (term111 e d x) = (term124 e d).
Proof. exact (MK_COMB (@lem1246028) (@lem1246027 x e d)). Qed.
Lemma lem1246030 (P : nat -> Prop) (d : nat) : (P d) = (P d).
Proof. exact (eq_refl (P d)). Qed.
Lemma lem1246031 (x : nat) (e : nat) (P : nat -> Prop) (d : nat) : (term112 e x P d) = (term125 e P d).
Proof. exact (MK_COMB (@lem1246029 x e d) (@lem1246030 P d)). Qed.
Lemma lem1246034 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1246035 (x : nat) (e : nat) (P : nat -> Prop) (d : nat) : (term113 e x P d) = (term126 e P d).
Proof. exact (MK_COMB (@lem1246034) (@lem1246031 x e P d)). Qed.
Lemma lem1246042 (e : nat) (P : nat -> Prop) (d : nat) : (term114 e P d) = (term114 e P d).
Proof. exact (eq_refl (term114 e P d)). Qed.
Lemma lem1246043 (x : nat) (e : nat) (P : nat -> Prop) (d : nat) : (term115 x e P d) = (term127 e P d).
Proof. exact (MK_COMB (@lem1246035 x e P d) (@lem1246042 e P d)). Qed.
Lemma lem1246046 (x : nat) (e : nat) (P : nat -> Prop) : (term116 x e P) = (term128 e P).
Proof. exact (fun_ext (fun d : nat => @lem1246043 x e P d)). Qed.
Lemma lem1246047 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1246048 (x : nat) (e : nat) (P : nat -> Prop) : (term117 x e P) = (term129 e P).
Proof. exact (MK_COMB (@lem1246047) (@lem1246046 x e P)). Qed.
Lemma lem1246053 (P : nat -> Prop) (e : nat) : (term91 P e) = (term91 P e).
Proof. exact (eq_refl (term91 P e)). Qed.
Lemma lem1246054 (x : nat) (e : nat) (P : nat -> Prop) : ((P e) = (term117 x e P)) = ((P e) = (term129 e P)).
Proof. exact (MK_COMB (@lem1246053 P e) (@lem1246048 x e P)). Qed.
Lemma lem1246057 (x : nat) (e : nat) (P : nat -> Prop) : ((P e) = (term129 e P)) = ((P e) = (term117 x e P)).
Proof. exact (SYM (@lem1246054 x e P)). Qed.
Lemma lem1246081 (m : nat) (n : nat) (p : nat) : (term4 m n p) = (term3 m n p).
Proof. exact (EQ_MP (@lem1245616 m n p) (@lem1245615 m n p)). Qed.
Lemma lem1246082 (y : nat) (e : nat) (d : nat) : (term4 y e d) = (term3 y e d).
Proof. exact (@lem1246081 y e d). Qed.
Lemma lem1246083 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1246084 (y : nat) (e : nat) (d : nat) : (term122 y e d) = (term123 y e d).
Proof. exact (MK_COMB (@lem1246083) (@lem1246082 y e d)). Qed.
Lemma lem1246085 (y : nat) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1246086 (e : nat) (d : nat) (y : nat) : ((term4 y e d) = y) = ((term3 y e d) = y).
Proof. exact (MK_COMB (@lem1246084 y e d) (@lem1246085 y)). Qed.
Lemma lem1246088 (m : nat) (n : nat) : ((Nat.add m n) = m) = (n = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1245607 m n) (@lem1245606 m n)). Qed.
Lemma lem1246089 (y : nat) (e : nat) (d : nat) : ((term3 y e d) = y) = ((Nat.add e d) = (NUMERAL 0)).
Proof. exact (@lem1246088 y (Nat.add e d)). Qed.
Lemma lem1246091 (m : nat) (n : nat) : ((Nat.add m n) = (NUMERAL 0)) = (term20 m n).
Proof. exact (EQ_MP (@lem1245601 m n) (@lem1245600 m n)). Qed.
Lemma lem1246092 (e : nat) (d : nat) : ((Nat.add e d) = (NUMERAL 0)) = (term20 e d).
Proof. exact (@lem1246091 e d). Qed.
Lemma lem1246099 (y : nat) (e : nat) (d : nat) : ((term3 y e d) = y) = (term20 e d).
Proof. exact (TRANS (@lem1246089 y e d) (@lem1246092 e d)). Qed.
Lemma lem1246100 (y : nat) (e : nat) (d : nat) : ((term4 y e d) = y) = (term20 e d).
Proof. exact (TRANS (@lem1246086 e d y) (@lem1246099 y e d)). Qed.
Lemma lem1246101 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1246102 (y : nat) (e : nat) (d : nat) : (term111 e d y) = (term124 e d).
Proof. exact (MK_COMB (@lem1246101) (@lem1246100 y e d)). Qed.
Lemma lem1246103 (P : nat -> Prop) (d : nat) : (P d) = (P d).
Proof. exact (eq_refl (P d)). Qed.
Lemma lem1246104 (y : nat) (e : nat) (P : nat -> Prop) (d : nat) : (term112 e y P d) = (term125 e P d).
Proof. exact (MK_COMB (@lem1246102 y e d) (@lem1246103 P d)). Qed.
Lemma lem1246107 (e : nat) (P : nat -> Prop) (d : nat) : (term118 e P d) = (term118 e P d).
Proof. exact (eq_refl (term118 e P d)). Qed.
Lemma lem1246108 (y : nat) (e : nat) (P : nat -> Prop) (d : nat) : (term119 e y P d) = (term130 e P d).
Proof. exact (MK_COMB (@lem1246107 e P d) (@lem1246104 y e P d)). Qed.
Lemma lem1246111 (y : nat) (e : nat) (P : nat -> Prop) : (term120 e y P) = (term131 e P).
Proof. exact (fun_ext (fun d : nat => @lem1246108 y e P d)). Qed.
Lemma lem1246112 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1246113 (y : nat) (e : nat) (P : nat -> Prop) : (term121 e y P) = (term132 e P).
Proof. exact (MK_COMB (@lem1246112) (@lem1246111 y e P)). Qed.
Lemma lem1246118 (P : nat -> Prop) (e : nat) : (term91 P e) = (term91 P e).
Proof. exact (eq_refl (term91 P e)). Qed.
Lemma lem1246119 (y : nat) (e : nat) (P : nat -> Prop) : ((P e) = (term121 e y P)) = ((P e) = (term132 e P)).
Proof. exact (MK_COMB (@lem1246118 P e) (@lem1246113 y e P)). Qed.
Lemma lem1246122 (e : nat) (y : nat) (P : nat -> Prop) : ((P e) = (term132 e P)) = ((P e) = (term121 e y P)).
Proof. exact (SYM (@lem1246119 y e P)). Qed.
Lemma lem1246126 (e : nat) (h1 : e = (NUMERAL 0)) : e = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1246127 (P : nat -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1246128 (P : nat -> Prop) (e : nat) (h1 : e = (NUMERAL 0)) : (P e) = (term133 P).
Proof. exact (MK_COMB (@lem1246127 P) (@lem1246126 e h1)). Qed.
Lemma lem1246129 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1246130 (P : nat -> Prop) (e : nat) (h1 : e = (NUMERAL 0)) : (term91 P e) = (term134 P).
Proof. exact (MK_COMB (@lem1246129) (@lem1246128 P e h1)). Qed.
Lemma lem1246144 (e : nat) (h1 : e = (NUMERAL 0)) : e = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1246145 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1246146 (e : nat) (h1 : e = (NUMERAL 0)) : (@eq nat e) = term135.
Proof. exact (MK_COMB (@lem1246145) (@lem1246144 e h1)). Qed.
Lemma lem1246147 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1246148 (e : nat) (h1 : e = (NUMERAL 0)) : (e = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1246146 e h1) (@lem1246147)). Qed.
Lemma lem1246150 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1246151 (x : nat) : (x = x) = True.
Proof. exact (@lem1246150 nat x). Qed.
Lemma lem1246152 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1246151 (NUMERAL 0)). Qed.
Lemma lem1246153 (e : nat) (h1 : e = (NUMERAL 0)) : (e = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem1246148 e h1) (@lem1246152)). Qed.
Lemma lem1246154 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1246155 (e : nat) (h1 : e = (NUMERAL 0)) : (term136 e) = (and True).
Proof. exact (MK_COMB (@lem1246154) (@lem1246153 e h1)). Qed.
Lemma lem1246158 (d : nat) : (d = (NUMERAL 0)) = (d = (NUMERAL 0)).
Proof. exact (eq_refl (d = (NUMERAL 0))). Qed.
Lemma lem1246159 (d : nat) (e : nat) (h1 : e = (NUMERAL 0)) : (term20 e d) = (term137 d).
Proof. exact (MK_COMB (@lem1246155 e h1) (@lem1246158 d)). Qed.
Lemma lem1246161 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1246162 (d : nat) : (term137 d) = (d = (NUMERAL 0)).
Proof. exact (@lem1246161 (d = (NUMERAL 0))). Qed.
Lemma lem1246165 (d : nat) (e : nat) (h1 : e = (NUMERAL 0)) : (term20 e d) = (d = (NUMERAL 0)).
Proof. exact (TRANS (@lem1246159 d e h1) (@lem1246162 d)). Qed.
Lemma lem1246166 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1246167 (d : nat) (e : nat) (h1 : e = (NUMERAL 0)) : (term124 e d) = (term138 d).
Proof. exact (MK_COMB (@lem1246166) (@lem1246165 d e h1)). Qed.
Lemma lem1246168 (P : nat -> Prop) (d : nat) : (P d) = (P d).
Proof. exact (eq_refl (P d)). Qed.
Lemma lem1246169 (P : nat -> Prop) (d : nat) (e : nat) (h1 : e = (NUMERAL 0)) : (term125 e P d) = (term139 P d).
Proof. exact (MK_COMB (@lem1246167 d e h1) (@lem1246168 P d)). Qed.
Lemma lem1246174 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1246175 (P : nat -> Prop) (d : nat) (e : nat) (h1 : e = (NUMERAL 0)) : (term126 e P d) = (term140 P d).
Proof. exact (MK_COMB (@lem1246174) (@lem1246169 P d e h1)). Qed.
Lemma lem1246183 (e : nat) (h1 : e = (NUMERAL 0)) : e = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1246184 (d : nat) : (@eq nat d) = (@eq nat d).
Proof. exact (eq_refl (@eq nat d)). Qed.
Lemma lem1246185 (d : nat) (e : nat) (h1 : e = (NUMERAL 0)) : (d = e) = (d = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1246184 d) (@lem1246183 e h1)). Qed.
Lemma lem1246188 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1246189 (d : nat) (e : nat) (h1 : e = (NUMERAL 0)) : (term93 d e) = (term138 d).
Proof. exact (MK_COMB (@lem1246188) (@lem1246185 d e h1)). Qed.
Lemma lem1246190 (P : nat -> Prop) (d : nat) : (P d) = (P d).
Proof. exact (eq_refl (P d)). Qed.
Lemma lem1246191 (P : nat -> Prop) (d : nat) (e : nat) (h1 : e = (NUMERAL 0)) : (term114 e P d) = (term139 P d).
Proof. exact (MK_COMB (@lem1246189 d e h1) (@lem1246190 P d)). Qed.
Lemma lem1246196 (P : nat -> Prop) (d : nat) (e : nat) (h1 : e = (NUMERAL 0)) : (term127 e P d) = (term141 P d).
Proof. exact (MK_COMB (@lem1246175 P d e h1) (@lem1246191 P d e h1)). Qed.
Lemma lem1246198 (t : Prop) : (t /\ t) = t.
Proof. exact (proj2 (@lem1845 t)). Qed.
Lemma lem1246199 (P : nat -> Prop) (d : nat) : (term141 P d) = (term139 P d).
Proof. exact (@lem1246198 (term139 P d)). Qed.
Lemma lem1246206 (P : nat -> Prop) (d : nat) (e : nat) (h1 : e = (NUMERAL 0)) : (term127 e P d) = (term139 P d).
Proof. exact (TRANS (@lem1246196 P d e h1) (@lem1246199 P d)). Qed.
Lemma lem1246207 (P : nat -> Prop) (e : nat) (h1 : e = (NUMERAL 0)) : (term128 e P) = (term142 P).
Proof. exact (fun_ext (fun d : nat => @lem1246206 P d e h1)). Qed.
Lemma lem1246208 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1246209 (P : nat -> Prop) (e : nat) (h1 : e = (NUMERAL 0)) : (term129 e P) = (term143 P).
Proof. exact (MK_COMB (@lem1246208) (@lem1246207 P e h1)). Qed.
Lemma lem1246214 (P : nat -> Prop) (e : nat) (h1 : e = (NUMERAL 0)) : ((P e) = (term129 e P)) = ((term133 P) = (term143 P)).
Proof. exact (MK_COMB (@lem1246130 P e h1) (@lem1246209 P e h1)). Qed.
Lemma lem1246217 (P : nat -> Prop) (e : nat) (h1 : e = (NUMERAL 0)) : ((term133 P) = (term143 P)) = ((P e) = (term129 e P)).
Proof. exact (SYM (@lem1246214 P e h1)). Qed.
Lemma lem1246218 (e : nat) : term144 e.
Proof. exact (@lem82 (e = (NUMERAL 0))). Qed.
Lemma lem1246244 (e : nat) (h1 : term2 e) : (e = (NUMERAL 0)) = False.
Proof. exact (@lem1246218 e (@lem1245578 e h1)). Qed.
Lemma lem1246245 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1246246 (e : nat) (h1 : term2 e) : (term136 e) = (and False).
Proof. exact (MK_COMB (@lem1246245) (@lem1246244 e h1)). Qed.
Lemma lem1246249 (d : nat) : (d = (NUMERAL 0)) = (d = (NUMERAL 0)).
Proof. exact (eq_refl (d = (NUMERAL 0))). Qed.
Lemma lem1246250 (d : nat) (e : nat) (h1 : term2 e) : (term20 e d) = (term145 d).
Proof. exact (MK_COMB (@lem1246246 e h1) (@lem1246249 d)). Qed.
Lemma lem1246252 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1246253 (d : nat) : (term145 d) = False.
Proof. exact (@lem1246252 (d = (NUMERAL 0))). Qed.
Lemma lem1246254 (d : nat) (e : nat) (h1 : term2 e) : (term20 e d) = False.
Proof. exact (TRANS (@lem1246250 d e h1) (@lem1246253 d)). Qed.
Lemma lem1246255 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1246256 (d : nat) (e : nat) (h1 : term2 e) : (term124 e d) = (imp False).
Proof. exact (MK_COMB (@lem1246255) (@lem1246254 d e h1)). Qed.
Lemma lem1246257 (P : nat -> Prop) (d : nat) : (P d) = (P d).
Proof. exact (eq_refl (P d)). Qed.
Lemma lem1246258 (P : nat -> Prop) (d : nat) (e : nat) (h1 : term2 e) : (term125 e P d) = (term146 P d).
Proof. exact (MK_COMB (@lem1246256 d e h1) (@lem1246257 P d)). Qed.
Lemma lem1246260 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1246261 (P : nat -> Prop) (d : nat) : (term146 P d) = True.
Proof. exact (@lem1246260 (P d)). Qed.
Lemma lem1246262 (P : nat -> Prop) (d : nat) (e : nat) (h1 : term2 e) : (term125 e P d) = True.
Proof. exact (TRANS (@lem1246258 P d e h1) (@lem1246261 P d)). Qed.
Lemma lem1246263 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1246264 (P : nat -> Prop) (d : nat) (e : nat) (h1 : term2 e) : (term126 e P d) = (and True).
Proof. exact (MK_COMB (@lem1246263) (@lem1246262 P d e h1)). Qed.
Lemma lem1246271 (e : nat) (P : nat -> Prop) (d : nat) : (term114 e P d) = (term114 e P d).
Proof. exact (eq_refl (term114 e P d)). Qed.
Lemma lem1246272 (P : nat -> Prop) (d : nat) (e : nat) (h1 : term2 e) : (term127 e P d) = (term147 e P d).
Proof. exact (MK_COMB (@lem1246264 P d e h1) (@lem1246271 e P d)). Qed.
Lemma lem1246274 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1246275 (e : nat) (P : nat -> Prop) (d : nat) : (term147 e P d) = (term114 e P d).
Proof. exact (@lem1246274 (term114 e P d)). Qed.
Lemma lem1246282 (P : nat -> Prop) (d : nat) (e : nat) (h1 : term2 e) : (term127 e P d) = (term114 e P d).
Proof. exact (TRANS (@lem1246272 P d e h1) (@lem1246275 e P d)). Qed.
Lemma lem1246283 (P : nat -> Prop) (e : nat) (h1 : term2 e) : (term128 e P) = (term148 e P).
Proof. exact (fun_ext (fun d : nat => @lem1246282 P d e h1)). Qed.
Lemma lem1246284 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1246285 (P : nat -> Prop) (e : nat) (h1 : term2 e) : (term129 e P) = (term149 e P).
Proof. exact (MK_COMB (@lem1246284) (@lem1246283 P e h1)). Qed.
Lemma lem1246290 (P : nat -> Prop) (e : nat) : (term91 P e) = (term91 P e).
Proof. exact (eq_refl (term91 P e)). Qed.
Lemma lem1246291 (P : nat -> Prop) (e : nat) (h1 : term2 e) : ((P e) = (term129 e P)) = ((P e) = (term149 e P)).
Proof. exact (MK_COMB (@lem1246290 P e) (@lem1246285 P e h1)). Qed.
Lemma lem1246294 (P : nat -> Prop) (e : nat) (h1 : term2 e) : ((P e) = (term149 e P)) = ((P e) = (term129 e P)).
Proof. exact (SYM (@lem1246291 P e h1)). Qed.
Lemma lem1246298 (e : nat) (h1 : e = (NUMERAL 0)) : e = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1246299 (P : nat -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1246300 (P : nat -> Prop) (e : nat) (h1 : e = (NUMERAL 0)) : (P e) = (term133 P).
Proof. exact (MK_COMB (@lem1246299 P) (@lem1246298 e h1)). Qed.
Lemma lem1246301 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1246302 (P : nat -> Prop) (e : nat) (h1 : e = (NUMERAL 0)) : (term91 P e) = (term134 P).
Proof. exact (MK_COMB (@lem1246301) (@lem1246300 P e h1)). Qed.
Lemma lem1246316 (e : nat) (h1 : e = (NUMERAL 0)) : e = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1246317 (d : nat) : (@eq nat d) = (@eq nat d).
Proof. exact (eq_refl (@eq nat d)). Qed.
Lemma lem1246318 (d : nat) (e : nat) (h1 : e = (NUMERAL 0)) : (d = e) = (d = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1246317 d) (@lem1246316 e h1)). Qed.
Lemma lem1246321 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1246322 (d : nat) (e : nat) (h1 : e = (NUMERAL 0)) : (term93 d e) = (term138 d).
Proof. exact (MK_COMB (@lem1246321) (@lem1246318 d e h1)). Qed.
Lemma lem1246323 (P : nat -> Prop) (d : nat) : (P d) = (P d).
Proof. exact (eq_refl (P d)). Qed.
Lemma lem1246324 (P : nat -> Prop) (d : nat) (e : nat) (h1 : e = (NUMERAL 0)) : (term114 e P d) = (term139 P d).
Proof. exact (MK_COMB (@lem1246322 d e h1) (@lem1246323 P d)). Qed.
Lemma lem1246329 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1246330 (P : nat -> Prop) (d : nat) (e : nat) (h1 : e = (NUMERAL 0)) : (term118 e P d) = (term140 P d).
Proof. exact (MK_COMB (@lem1246329) (@lem1246324 P d e h1)). Qed.
Lemma lem1246338 (e : nat) (h1 : e = (NUMERAL 0)) : e = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1246339 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1246340 (e : nat) (h1 : e = (NUMERAL 0)) : (@eq nat e) = term135.
Proof. exact (MK_COMB (@lem1246339) (@lem1246338 e h1)). Qed.
Lemma lem1246341 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1246342 (e : nat) (h1 : e = (NUMERAL 0)) : (e = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1246340 e h1) (@lem1246341)). Qed.
Lemma lem1246344 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1246345 (x : nat) : (x = x) = True.
Proof. exact (@lem1246344 nat x). Qed.
Lemma lem1246346 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1246345 (NUMERAL 0)). Qed.
Lemma lem1246347 (e : nat) (h1 : e = (NUMERAL 0)) : (e = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem1246342 e h1) (@lem1246346)). Qed.
Lemma lem1246348 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1246349 (e : nat) (h1 : e = (NUMERAL 0)) : (term136 e) = (and True).
Proof. exact (MK_COMB (@lem1246348) (@lem1246347 e h1)). Qed.
Lemma lem1246352 (d : nat) : (d = (NUMERAL 0)) = (d = (NUMERAL 0)).
Proof. exact (eq_refl (d = (NUMERAL 0))). Qed.
Lemma lem1246353 (d : nat) (e : nat) (h1 : e = (NUMERAL 0)) : (term20 e d) = (term137 d).
Proof. exact (MK_COMB (@lem1246349 e h1) (@lem1246352 d)). Qed.
Lemma lem1246355 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1246356 (d : nat) : (term137 d) = (d = (NUMERAL 0)).
Proof. exact (@lem1246355 (d = (NUMERAL 0))). Qed.
Lemma lem1246359 (d : nat) (e : nat) (h1 : e = (NUMERAL 0)) : (term20 e d) = (d = (NUMERAL 0)).
Proof. exact (TRANS (@lem1246353 d e h1) (@lem1246356 d)). Qed.
Lemma lem1246360 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1246361 (d : nat) (e : nat) (h1 : e = (NUMERAL 0)) : (term124 e d) = (term138 d).
Proof. exact (MK_COMB (@lem1246360) (@lem1246359 d e h1)). Qed.
Lemma lem1246362 (P : nat -> Prop) (d : nat) : (P d) = (P d).
Proof. exact (eq_refl (P d)). Qed.
Lemma lem1246363 (P : nat -> Prop) (d : nat) (e : nat) (h1 : e = (NUMERAL 0)) : (term125 e P d) = (term139 P d).
Proof. exact (MK_COMB (@lem1246361 d e h1) (@lem1246362 P d)). Qed.
Lemma lem1246368 (P : nat -> Prop) (d : nat) (e : nat) (h1 : e = (NUMERAL 0)) : (term130 e P d) = (term141 P d).
Proof. exact (MK_COMB (@lem1246330 P d e h1) (@lem1246363 P d e h1)). Qed.
Lemma lem1246370 (t : Prop) : (t /\ t) = t.
Proof. exact (proj2 (@lem1845 t)). Qed.
Lemma lem1246371 (P : nat -> Prop) (d : nat) : (term141 P d) = (term139 P d).
Proof. exact (@lem1246370 (term139 P d)). Qed.
Lemma lem1246378 (P : nat -> Prop) (d : nat) (e : nat) (h1 : e = (NUMERAL 0)) : (term130 e P d) = (term139 P d).
Proof. exact (TRANS (@lem1246368 P d e h1) (@lem1246371 P d)). Qed.
Lemma lem1246379 (P : nat -> Prop) (e : nat) (h1 : e = (NUMERAL 0)) : (term131 e P) = (term142 P).
Proof. exact (fun_ext (fun d : nat => @lem1246378 P d e h1)). Qed.
Lemma lem1246380 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1246381 (P : nat -> Prop) (e : nat) (h1 : e = (NUMERAL 0)) : (term132 e P) = (term143 P).
Proof. exact (MK_COMB (@lem1246380) (@lem1246379 P e h1)). Qed.
Lemma lem1246386 (P : nat -> Prop) (e : nat) (h1 : e = (NUMERAL 0)) : ((P e) = (term132 e P)) = ((term133 P) = (term143 P)).
Proof. exact (MK_COMB (@lem1246302 P e h1) (@lem1246381 P e h1)). Qed.
Lemma lem1246389 (P : nat -> Prop) (e : nat) (h1 : e = (NUMERAL 0)) : ((term133 P) = (term143 P)) = ((P e) = (term132 e P)).
Proof. exact (SYM (@lem1246386 P e h1)). Qed.
Lemma lem1246390 (e : nat) : term144 e.
Proof. exact (@lem82 (e = (NUMERAL 0))). Qed.
Lemma lem1246422 (e : nat) (h1 : term2 e) : (e = (NUMERAL 0)) = False.
Proof. exact (@lem1246390 e (@lem1245578 e h1)). Qed.
Lemma lem1246423 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1246424 (e : nat) (h1 : term2 e) : (term136 e) = (and False).
Proof. exact (MK_COMB (@lem1246423) (@lem1246422 e h1)). Qed.
Lemma lem1246427 (d : nat) : (d = (NUMERAL 0)) = (d = (NUMERAL 0)).
Proof. exact (eq_refl (d = (NUMERAL 0))). Qed.
Lemma lem1246428 (d : nat) (e : nat) (h1 : term2 e) : (term20 e d) = (term145 d).
Proof. exact (MK_COMB (@lem1246424 e h1) (@lem1246427 d)). Qed.
Lemma lem1246430 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1246431 (d : nat) : (term145 d) = False.
Proof. exact (@lem1246430 (d = (NUMERAL 0))). Qed.
Lemma lem1246432 (d : nat) (e : nat) (h1 : term2 e) : (term20 e d) = False.
Proof. exact (TRANS (@lem1246428 d e h1) (@lem1246431 d)). Qed.
Lemma lem1246433 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1246434 (d : nat) (e : nat) (h1 : term2 e) : (term124 e d) = (imp False).
Proof. exact (MK_COMB (@lem1246433) (@lem1246432 d e h1)). Qed.
Lemma lem1246435 (P : nat -> Prop) (d : nat) : (P d) = (P d).
Proof. exact (eq_refl (P d)). Qed.
Lemma lem1246436 (P : nat -> Prop) (d : nat) (e : nat) (h1 : term2 e) : (term125 e P d) = (term146 P d).
Proof. exact (MK_COMB (@lem1246434 d e h1) (@lem1246435 P d)). Qed.
Lemma lem1246438 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1246439 (P : nat -> Prop) (d : nat) : (term146 P d) = True.
Proof. exact (@lem1246438 (P d)). Qed.
Lemma lem1246440 (P : nat -> Prop) (d : nat) (e : nat) (h1 : term2 e) : (term125 e P d) = True.
Proof. exact (TRANS (@lem1246436 P d e h1) (@lem1246439 P d)). Qed.
Lemma lem1246441 (e : nat) (P : nat -> Prop) (d : nat) : (term118 e P d) = (term118 e P d).
Proof. exact (eq_refl (term118 e P d)). Qed.
Lemma lem1246442 (P : nat -> Prop) (d : nat) (e : nat) (h1 : term2 e) : (term130 e P d) = (term150 e P d).
Proof. exact (MK_COMB (@lem1246441 e P d) (@lem1246440 P d e h1)). Qed.
Lemma lem1246444 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1246445 (e : nat) (P : nat -> Prop) (d : nat) : (term150 e P d) = (term114 e P d).
Proof. exact (@lem1246444 (term114 e P d)). Qed.
Lemma lem1246452 (P : nat -> Prop) (d : nat) (e : nat) (h1 : term2 e) : (term130 e P d) = (term114 e P d).
Proof. exact (TRANS (@lem1246442 P d e h1) (@lem1246445 e P d)). Qed.
Lemma lem1246453 (P : nat -> Prop) (e : nat) (h1 : term2 e) : (term131 e P) = (term148 e P).
Proof. exact (fun_ext (fun d : nat => @lem1246452 P d e h1)). Qed.
Lemma lem1246454 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1246455 (P : nat -> Prop) (e : nat) (h1 : term2 e) : (term132 e P) = (term149 e P).
Proof. exact (MK_COMB (@lem1246454) (@lem1246453 P e h1)). Qed.
Lemma lem1246460 (P : nat -> Prop) (e : nat) : (term91 P e) = (term91 P e).
Proof. exact (eq_refl (term91 P e)). Qed.
Lemma lem1246461 (P : nat -> Prop) (e : nat) (h1 : term2 e) : ((P e) = (term132 e P)) = ((P e) = (term149 e P)).
Proof. exact (MK_COMB (@lem1246460 P e) (@lem1246455 P e h1)). Qed.
Lemma lem1246464 (P : nat -> Prop) (e : nat) (h1 : term2 e) : ((P e) = (term149 e P)) = ((P e) = (term132 e P)).
Proof. exact (SYM (@lem1246461 P e h1)). Qed.
Lemma lem1246465 (P : nat -> Prop) (h1 : term133 P) : term133 P.
Proof. exact (h1). Qed.
Lemma lem1246466 (d : nat) (h1 : d = (NUMERAL 0)) : d = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1246467 (P : nat -> Prop) (h1 : term143 P) : term143 P.
Proof. exact (h1). Qed.
Lemma lem1246468 (P : nat -> Prop) (e : nat) (h1 : P e) : P e.
Proof. exact (h1). Qed.
Lemma lem1246469 (d : nat) (e : nat) (h1 : d = e) : d = e.
Proof. exact (h1). Qed.
Lemma lem1246470 (e : nat) (P : nat -> Prop) (h1 : term149 e P) : term149 e P.
Proof. exact (h1). Qed.
Lemma lem1246471 (P : nat -> Prop) (h1 : term133 P) : term133 P.
Proof. exact (h1). Qed.
Lemma lem1246472 (d : nat) (h1 : d = (NUMERAL 0)) : d = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1246473 (P : nat -> Prop) (h1 : term143 P) : term143 P.
Proof. exact (h1). Qed.
Lemma lem1246474 (P : nat -> Prop) (e : nat) (h1 : P e) : P e.
Proof. exact (h1). Qed.
Lemma lem1246475 (d : nat) (e : nat) (h1 : d = e) : d = e.
Proof. exact (h1). Qed.
Lemma lem1246476 (e : nat) (P : nat -> Prop) (h1 : term149 e P) : term149 e P.
Proof. exact (h1). Qed.
Lemma lem1246477 (P : nat -> Prop) : (term133 P) = ((term133 P) = True).
Proof. exact (@lem7 (term133 P)). Qed.
Lemma lem1246480 (d : nat) (h1 : d = (NUMERAL 0)) : d = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1246481 (P : nat -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1246482 (P : nat -> Prop) (d : nat) (h1 : d = (NUMERAL 0)) : (P d) = (term133 P).
Proof. exact (MK_COMB (@lem1246481 P) (@lem1246480 d h1)). Qed.
Lemma lem1246484 (P : nat -> Prop) (h1 : term133 P) : (term133 P) = True.
Proof. exact (EQ_MP (@lem1246477 P) (@lem1246465 P h1)). Qed.
Lemma lem1246485 (P : nat -> Prop) (d : nat) (h1 : term133 P) (h2 : d = (NUMERAL 0)) : (P d) = True.
Proof. exact (TRANS (@lem1246482 P d h2) (@lem1246484 P h1)). Qed.
Lemma lem1246486 (P : nat -> Prop) (d : nat) (h1 : term133 P) (h2 : d = (NUMERAL 0)) : True = (P d).
Proof. exact (SYM (@lem1246485 P d h1 h2)). Qed.
Lemma lem1246487 (P : nat -> Prop) (d : nat) (h1 : term133 P) (h2 : d = (NUMERAL 0)) : P d.
Proof. exact (EQ_MP (@lem1246486 P d h1 h2) (@lem0)). Qed.
Lemma lem1246508 (P : nat -> Prop) (e : nat) : (P e) = ((P e) = True).
Proof. exact (@lem7 (P e)). Qed.
Lemma lem1246511 (d : nat) (e : nat) (h1 : d = e) : d = e.
Proof. exact (h1). Qed.
Lemma lem1246512 (P : nat -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1246513 (P : nat -> Prop) (d : nat) (e : nat) (h1 : d = e) : (P d) = (P e).
Proof. exact (MK_COMB (@lem1246512 P) (@lem1246511 d e h1)). Qed.
Lemma lem1246515 (P : nat -> Prop) (e : nat) (h1 : P e) : (P e) = True.
Proof. exact (EQ_MP (@lem1246508 P e) (@lem1246468 P e h1)). Qed.
Lemma lem1246516 (P : nat -> Prop) (d : nat) (e : nat) (h1 : P e) (h2 : d = e) : (P d) = True.
Proof. exact (TRANS (@lem1246513 P d e h2) (@lem1246515 P e h1)). Qed.
Lemma lem1246517 (P : nat -> Prop) (d : nat) (e : nat) (h1 : P e) (h2 : d = e) : True = (P d).
Proof. exact (SYM (@lem1246516 P d e h1 h2)). Qed.
Lemma lem1246518 (P : nat -> Prop) (d : nat) (e : nat) (h1 : P e) (h2 : d = e) : P d.
Proof. exact (EQ_MP (@lem1246517 P d e h1 h2) (@lem0)). Qed.
Lemma lem1246539 (P : nat -> Prop) : (term133 P) = ((term133 P) = True).
Proof. exact (@lem7 (term133 P)). Qed.
Lemma lem1246542 (d : nat) (h1 : d = (NUMERAL 0)) : d = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1246543 (P : nat -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1246544 (P : nat -> Prop) (d : nat) (h1 : d = (NUMERAL 0)) : (P d) = (term133 P).
Proof. exact (MK_COMB (@lem1246543 P) (@lem1246542 d h1)). Qed.
Lemma lem1246546 (P : nat -> Prop) (h1 : term133 P) : (term133 P) = True.
Proof. exact (EQ_MP (@lem1246539 P) (@lem1246471 P h1)). Qed.
Lemma lem1246547 (P : nat -> Prop) (d : nat) (h1 : term133 P) (h2 : d = (NUMERAL 0)) : (P d) = True.
Proof. exact (TRANS (@lem1246544 P d h2) (@lem1246546 P h1)). Qed.
Lemma lem1246548 (P : nat -> Prop) (d : nat) (h1 : term133 P) (h2 : d = (NUMERAL 0)) : True = (P d).
Proof. exact (SYM (@lem1246547 P d h1 h2)). Qed.
Lemma lem1246549 (P : nat -> Prop) (d : nat) (h1 : term133 P) (h2 : d = (NUMERAL 0)) : P d.
Proof. exact (EQ_MP (@lem1246548 P d h1 h2) (@lem0)). Qed.
Lemma lem1246570 (P : nat -> Prop) (e : nat) : (P e) = ((P e) = True).
Proof. exact (@lem7 (P e)). Qed.
Lemma lem1246573 (d : nat) (e : nat) (h1 : d = e) : d = e.
Proof. exact (h1). Qed.
Lemma lem1246574 (P : nat -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1246575 (P : nat -> Prop) (d : nat) (e : nat) (h1 : d = e) : (P d) = (P e).
Proof. exact (MK_COMB (@lem1246574 P) (@lem1246573 d e h1)). Qed.
Lemma lem1246577 (P : nat -> Prop) (e : nat) (h1 : P e) : (P e) = True.
Proof. exact (EQ_MP (@lem1246570 P e) (@lem1246474 P e h1)). Qed.
Lemma lem1246578 (P : nat -> Prop) (d : nat) (e : nat) (h1 : P e) (h2 : d = e) : (P d) = True.
Proof. exact (TRANS (@lem1246575 P d e h2) (@lem1246577 P e h1)). Qed.
Lemma lem1246579 (P : nat -> Prop) (d : nat) (e : nat) (h1 : P e) (h2 : d = e) : True = (P d).
Proof. exact (SYM (@lem1246578 P d e h1 h2)). Qed.
Lemma lem1246580 (P : nat -> Prop) (d : nat) (e : nat) (h1 : P e) (h2 : d = e) : P d.
Proof. exact (EQ_MP (@lem1246579 P d e h1 h2) (@lem0)). Qed.
Lemma lem1246601 (P : nat -> Prop) (h1 : term143 P) : term143 P.
Proof. exact (h1). Qed.
Lemma lem1246602 (d : nat) (P : nat -> Prop) (h1 : term143 P) : term151 P d.
Proof. exact (@lem1246601 P h1 d). Qed.
Lemma lem1246603 (P : nat -> Prop) (d : nat) : (term151 P d) = (term139 P d).
Proof. exact (eq_refl (term151 P d)). Qed.
Lemma lem1246604 (d : nat) (P : nat -> Prop) (h1 : term143 P) : term139 P d.
Proof. exact (EQ_MP (@lem1246603 P d) (@lem1246602 d P h1)). Qed.
Lemma lem1246605 (d : nat) (h1 : d = (NUMERAL 0)) : d = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1246606 (P : nat -> Prop) (d : nat) (h1 : term143 P) (h2 : d = (NUMERAL 0)) : P d.
Proof. exact (@lem1246604 d P h1 (@lem1246605 d h2)). Qed.
Lemma lem1246607 (P : nat -> Prop) (d : nat) (h1 : d = (NUMERAL 0)) : term152 P d.
Proof. exact (fun h0 : term143 P => @lem1246606 P d h0 h1). Qed.
Lemma lem1246608 (P : nat -> Prop) (h1 : term143 P) : term143 P.
Proof. exact (h1). Qed.
Lemma lem1246609 (P : nat -> Prop) (d : nat) (h1 : term143 P) (h2 : d = (NUMERAL 0)) : P d.
Proof. exact (@lem1246607 P d h2 (@lem1246608 P h1)). Qed.
Lemma lem1246610 (d : nat) (P : nat -> Prop) (h1 : term143 P) : term139 P d.
Proof. exact (fun h0 : d = (NUMERAL 0) => @lem1246609 P d h1 h0). Qed.
Lemma lem1246611 (P : nat -> Prop) (h1 : term143 P) : term143 P.
Proof. exact (fun d : nat => @lem1246610 d P h1). Qed.
Lemma lem1246612 (P : nat -> Prop) : term153 P.
Proof. exact (fun h0 : term143 P => @lem1246611 P h0). Qed.
Lemma lem1246613 (P : nat -> Prop) (h1 : term143 P) : term143 P.
Proof. exact (@lem1246612 P (@lem1246467 P h1)). Qed.
Lemma lem1246614 (d : nat) (P : nat -> Prop) (h1 : term143 P) : term151 P d.
Proof. exact (@lem1246613 P h1 d). Qed.
Lemma lem1246615 (P : nat -> Prop) (d : nat) : (term151 P d) = (term139 P d).
Proof. exact (eq_refl (term151 P d)). Qed.
Lemma lem1246618 (d : nat) (P : nat -> Prop) (h1 : term143 P) : term139 P d.
Proof. exact (EQ_MP (@lem1246615 P d) (@lem1246614 d P h1)). Qed.
Lemma lem1246619 (P : nat -> Prop) (h1 : term143 P) : term154 P.
Proof. exact (@lem1246618 (NUMERAL 0) P h1). Qed.
Lemma lem1246620 (e : nat) (P : nat -> Prop) (h1 : term149 e P) : term149 e P.
Proof. exact (h1). Qed.
Lemma lem1246621 (d : nat) (e : nat) (P : nat -> Prop) (h1 : term149 e P) : term155 e P d.
Proof. exact (@lem1246620 e P h1 d). Qed.
Lemma lem1246622 (e : nat) (P : nat -> Prop) (d : nat) : (term155 e P d) = (term114 e P d).
Proof. exact (eq_refl (term155 e P d)). Qed.
Lemma lem1246623 (d : nat) (e : nat) (P : nat -> Prop) (h1 : term149 e P) : term114 e P d.
Proof. exact (EQ_MP (@lem1246622 e P d) (@lem1246621 d e P h1)). Qed.
Lemma lem1246624 (d : nat) (e : nat) (h1 : d = e) : d = e.
Proof. exact (h1). Qed.
Lemma lem1246625 (P : nat -> Prop) (d : nat) (e : nat) (h1 : term149 e P) (h2 : d = e) : P d.
Proof. exact (@lem1246623 d e P h1 (@lem1246624 d e h2)). Qed.
Lemma lem1246626 (P : nat -> Prop) (d : nat) (e : nat) (h1 : d = e) : term156 e P d.
Proof. exact (fun h0 : term149 e P => @lem1246625 P d e h0 h1). Qed.
Lemma lem1246627 (e : nat) (P : nat -> Prop) (h1 : term149 e P) : term149 e P.
Proof. exact (h1). Qed.
Lemma lem1246628 (P : nat -> Prop) (d : nat) (e : nat) (h1 : term149 e P) (h2 : d = e) : P d.
Proof. exact (@lem1246626 P d e h2 (@lem1246627 e P h1)). Qed.
Lemma lem1246629 (d : nat) (e : nat) (P : nat -> Prop) (h1 : term149 e P) : term114 e P d.
Proof. exact (fun h0 : d = e => @lem1246628 P d e h1 h0). Qed.
Lemma lem1246630 (e : nat) (P : nat -> Prop) (h1 : term149 e P) : term149 e P.
Proof. exact (fun d : nat => @lem1246629 d e P h1). Qed.
Lemma lem1246631 (e : nat) (P : nat -> Prop) : term157 e P.
Proof. exact (fun h0 : term149 e P => @lem1246630 e P h0). Qed.
Lemma lem1246632 (e : nat) (P : nat -> Prop) (h1 : term149 e P) : term149 e P.
Proof. exact (@lem1246631 e P (@lem1246470 e P h1)). Qed.
Lemma lem1246633 (d : nat) (e : nat) (P : nat -> Prop) (h1 : term149 e P) : term155 e P d.
Proof. exact (@lem1246632 e P h1 d). Qed.
Lemma lem1246634 (e : nat) (P : nat -> Prop) (d : nat) : (term155 e P d) = (term114 e P d).
Proof. exact (eq_refl (term155 e P d)). Qed.
Lemma lem1246637 (d : nat) (e : nat) (P : nat -> Prop) (h1 : term149 e P) : term114 e P d.
Proof. exact (EQ_MP (@lem1246634 e P d) (@lem1246633 d e P h1)). Qed.
Lemma lem1246638 (e : nat) (P : nat -> Prop) (h1 : term149 e P) : term158 P e.
Proof. exact (@lem1246637 e e P h1). Qed.
Lemma lem1246639 (P : nat -> Prop) (h1 : term143 P) : term143 P.
Proof. exact (h1). Qed.
Lemma lem1246640 (d : nat) (P : nat -> Prop) (h1 : term143 P) : term151 P d.
Proof. exact (@lem1246639 P h1 d). Qed.
Lemma lem1246641 (P : nat -> Prop) (d : nat) : (term151 P d) = (term139 P d).
Proof. exact (eq_refl (term151 P d)). Qed.
Lemma lem1246642 (d : nat) (P : nat -> Prop) (h1 : term143 P) : term139 P d.
Proof. exact (EQ_MP (@lem1246641 P d) (@lem1246640 d P h1)). Qed.
Lemma lem1246643 (d : nat) (h1 : d = (NUMERAL 0)) : d = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1246644 (P : nat -> Prop) (d : nat) (h1 : term143 P) (h2 : d = (NUMERAL 0)) : P d.
Proof. exact (@lem1246642 d P h1 (@lem1246643 d h2)). Qed.
Lemma lem1246645 (P : nat -> Prop) (d : nat) (h1 : d = (NUMERAL 0)) : term152 P d.
Proof. exact (fun h0 : term143 P => @lem1246644 P d h0 h1). Qed.
Lemma lem1246646 (P : nat -> Prop) (h1 : term143 P) : term143 P.
Proof. exact (h1). Qed.
Lemma lem1246647 (P : nat -> Prop) (d : nat) (h1 : term143 P) (h2 : d = (NUMERAL 0)) : P d.
Proof. exact (@lem1246645 P d h2 (@lem1246646 P h1)). Qed.
Lemma lem1246648 (d : nat) (P : nat -> Prop) (h1 : term143 P) : term139 P d.
Proof. exact (fun h0 : d = (NUMERAL 0) => @lem1246647 P d h1 h0). Qed.
Lemma lem1246649 (P : nat -> Prop) (h1 : term143 P) : term143 P.
Proof. exact (fun d : nat => @lem1246648 d P h1). Qed.
Lemma lem1246650 (P : nat -> Prop) : term153 P.
Proof. exact (fun h0 : term143 P => @lem1246649 P h0). Qed.
Lemma lem1246651 (P : nat -> Prop) (h1 : term143 P) : term143 P.
Proof. exact (@lem1246650 P (@lem1246473 P h1)). Qed.
Lemma lem1246652 (d : nat) (P : nat -> Prop) (h1 : term143 P) : term151 P d.
Proof. exact (@lem1246651 P h1 d). Qed.
Lemma lem1246653 (P : nat -> Prop) (d : nat) : (term151 P d) = (term139 P d).
Proof. exact (eq_refl (term151 P d)). Qed.
Lemma lem1246656 (d : nat) (P : nat -> Prop) (h1 : term143 P) : term139 P d.
Proof. exact (EQ_MP (@lem1246653 P d) (@lem1246652 d P h1)). Qed.
Lemma lem1246657 (P : nat -> Prop) (h1 : term143 P) : term154 P.
Proof. exact (@lem1246656 (NUMERAL 0) P h1). Qed.
Lemma lem1246658 (e : nat) (P : nat -> Prop) (h1 : term149 e P) : term149 e P.
Proof. exact (h1). Qed.
Lemma lem1246659 (d : nat) (e : nat) (P : nat -> Prop) (h1 : term149 e P) : term155 e P d.
Proof. exact (@lem1246658 e P h1 d). Qed.
Lemma lem1246660 (e : nat) (P : nat -> Prop) (d : nat) : (term155 e P d) = (term114 e P d).
Proof. exact (eq_refl (term155 e P d)). Qed.
Lemma lem1246661 (d : nat) (e : nat) (P : nat -> Prop) (h1 : term149 e P) : term114 e P d.
Proof. exact (EQ_MP (@lem1246660 e P d) (@lem1246659 d e P h1)). Qed.
Lemma lem1246662 (d : nat) (e : nat) (h1 : d = e) : d = e.
Proof. exact (h1). Qed.
Lemma lem1246663 (P : nat -> Prop) (d : nat) (e : nat) (h1 : term149 e P) (h2 : d = e) : P d.
Proof. exact (@lem1246661 d e P h1 (@lem1246662 d e h2)). Qed.
Lemma lem1246664 (P : nat -> Prop) (d : nat) (e : nat) (h1 : d = e) : term156 e P d.
Proof. exact (fun h0 : term149 e P => @lem1246663 P d e h0 h1). Qed.
Lemma lem1246665 (e : nat) (P : nat -> Prop) (h1 : term149 e P) : term149 e P.
Proof. exact (h1). Qed.
Lemma lem1246666 (P : nat -> Prop) (d : nat) (e : nat) (h1 : term149 e P) (h2 : d = e) : P d.
Proof. exact (@lem1246664 P d e h2 (@lem1246665 e P h1)). Qed.
Lemma lem1246667 (d : nat) (e : nat) (P : nat -> Prop) (h1 : term149 e P) : term114 e P d.
Proof. exact (fun h0 : d = e => @lem1246666 P d e h1 h0). Qed.
Lemma lem1246668 (e : nat) (P : nat -> Prop) (h1 : term149 e P) : term149 e P.
Proof. exact (fun d : nat => @lem1246667 d e P h1). Qed.
Lemma lem1246669 (e : nat) (P : nat -> Prop) : term157 e P.
Proof. exact (fun h0 : term149 e P => @lem1246668 e P h0). Qed.
Lemma lem1246670 (e : nat) (P : nat -> Prop) (h1 : term149 e P) : term149 e P.
Proof. exact (@lem1246669 e P (@lem1246476 e P h1)). Qed.
Lemma lem1246671 (d : nat) (e : nat) (P : nat -> Prop) (h1 : term149 e P) : term155 e P d.
Proof. exact (@lem1246670 e P h1 d). Qed.
Lemma lem1246672 (e : nat) (P : nat -> Prop) (d : nat) : (term155 e P d) = (term114 e P d).
Proof. exact (eq_refl (term155 e P d)). Qed.
Lemma lem1246675 (d : nat) (e : nat) (P : nat -> Prop) (h1 : term149 e P) : term114 e P d.
Proof. exact (EQ_MP (@lem1246672 e P d) (@lem1246671 d e P h1)). Qed.
Lemma lem1246676 (e : nat) (P : nat -> Prop) (h1 : term149 e P) : term158 P e.
Proof. exact (@lem1246675 e e P h1). Qed.
Lemma lem1246683 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1246684 (x : nat) : (x = x) = True.
Proof. exact (@lem1246683 nat x). Qed.
Lemma lem1246685 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1246684 (NUMERAL 0)). Qed.
Lemma lem1246686 : True = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (SYM (@lem1246685)). Qed.
Lemma lem1246687 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem1246686) (@lem0)). Qed.
Lemma lem1246707 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1246708 (x : nat) : (x = x) = True.
Proof. exact (@lem1246707 nat x). Qed.
Lemma lem1246709 (e : nat) : (e = e) = True.
Proof. exact (@lem1246708 e). Qed.
Lemma lem1246710 (e : nat) : True = (e = e).
Proof. exact (SYM (@lem1246709 e)). Qed.
Lemma lem1246711 (e : nat) : e = e.
Proof. exact (EQ_MP (@lem1246710 e) (@lem0)). Qed.
Lemma lem1246718 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1246719 (x : nat) : (x = x) = True.
Proof. exact (@lem1246718 nat x). Qed.
Lemma lem1246720 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1246719 (NUMERAL 0)). Qed.
Lemma lem1246721 : True = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (SYM (@lem1246720)). Qed.
Lemma lem1246722 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem1246721) (@lem0)). Qed.
Lemma lem1246742 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1246743 (x : nat) : (x = x) = True.
Proof. exact (@lem1246742 nat x). Qed.
Lemma lem1246744 (e : nat) : (e = e) = True.
Proof. exact (@lem1246743 e). Qed.
Lemma lem1246745 (e : nat) : True = (e = e).
Proof. exact (SYM (@lem1246744 e)). Qed.
Lemma lem1246746 (e : nat) : e = e.
Proof. exact (EQ_MP (@lem1246745 e) (@lem0)). Qed.
Lemma lem1246751 (e : nat) (P : nat -> Prop) (h1 : term149 e P) : P e.
Proof. exact (@lem1246676 e P h1 (@lem1246746 e)). Qed.
Lemma lem1246752 (P : nat -> Prop) (h1 : term143 P) : term133 P.
Proof. exact (@lem1246657 P h1 (@lem1246722)). Qed.
Lemma lem1246753 (e : nat) (P : nat -> Prop) (h1 : term149 e P) : P e.
Proof. exact (@lem1246638 e P h1 (@lem1246711 e)). Qed.
Lemma lem1246754 (P : nat -> Prop) (h1 : term143 P) : term133 P.
Proof. exact (@lem1246619 P h1 (@lem1246687)). Qed.
Lemma lem1246755 (e : nat) (P : nat -> Prop) (h1 : term149 e P) : (term149 e P) = (P e).
Proof. exact (prop_ext (fun h2 : term149 e P => @lem1246751 e P h1) (fun h2 : P e => @lem1246476 e P h1)). Qed.
Lemma lem1246756 (e : nat) (P : nat -> Prop) (h1 : term149 e P) : P e.
Proof. exact (EQ_MP (@lem1246755 e P h1) (@lem1246476 e P h1)). Qed.
Lemma lem1246757 (P : nat -> Prop) (e : nat) : term159 P e.
Proof. exact (fun h0 : term149 e P => @lem1246756 e P h0). Qed.
Lemma lem1246758 (P : nat -> Prop) (d : nat) (e : nat) (h1 : P e) (h2 : d = e) : (d = e) = (P d).
Proof. exact (prop_ext (fun h3 : d = e => @lem1246580 P d e h1 h2) (fun h3 : P d => @lem1246475 d e h2)). Qed.
Lemma lem1246759 (P : nat -> Prop) (d : nat) (e : nat) (h1 : P e) (h2 : d = e) : P d.
Proof. exact (EQ_MP (@lem1246758 P d e h1 h2) (@lem1246475 d e h2)). Qed.
Lemma lem1246760 (d : nat) (P : nat -> Prop) (e : nat) (h1 : P e) : term114 e P d.
Proof. exact (fun h0 : d = e => @lem1246759 P d e h1 h0). Qed.
Lemma lem1246765 (P : nat -> Prop) (e : nat) (h1 : P e) : term149 e P.
Proof. exact (fun d : nat => @lem1246760 d P e h1). Qed.
Lemma lem1246766 (P : nat -> Prop) (e : nat) (h1 : P e) : (P e) = (term149 e P).
Proof. exact (prop_ext (fun h2 : P e => @lem1246765 P e h1) (fun h2 : term149 e P => @lem1246474 P e h1)). Qed.
Lemma lem1246767 (P : nat -> Prop) (e : nat) (h1 : P e) : term149 e P.
Proof. exact (EQ_MP (@lem1246766 P e h1) (@lem1246474 P e h1)). Qed.
Lemma lem1246768 (e : nat) (P : nat -> Prop) : term160 e P.
Proof. exact (fun h0 : P e => @lem1246767 P e h0). Qed.
Lemma lem1246769 (P : nat -> Prop) (h1 : term143 P) : (term143 P) = (term133 P).
Proof. exact (prop_ext (fun h2 : term143 P => @lem1246752 P h1) (fun h2 : term133 P => @lem1246473 P h1)). Qed.
Lemma lem1246770 (P : nat -> Prop) (h1 : term143 P) : term133 P.
Proof. exact (EQ_MP (@lem1246769 P h1) (@lem1246473 P h1)). Qed.
Lemma lem1246771 (P : nat -> Prop) : term161 P.
Proof. exact (fun h0 : term143 P => @lem1246770 P h0). Qed.
Lemma lem1246772 (P : nat -> Prop) (d : nat) (h1 : term133 P) (h2 : d = (NUMERAL 0)) : (d = (NUMERAL 0)) = (P d).
Proof. exact (prop_ext (fun h3 : d = (NUMERAL 0) => @lem1246549 P d h1 h2) (fun h3 : P d => @lem1246472 d h2)). Qed.
Lemma lem1246773 (P : nat -> Prop) (d : nat) (h1 : term133 P) (h2 : d = (NUMERAL 0)) : P d.
Proof. exact (EQ_MP (@lem1246772 P d h1 h2) (@lem1246472 d h2)). Qed.
Lemma lem1246774 (d : nat) (P : nat -> Prop) (h1 : term133 P) : term139 P d.
Proof. exact (fun h0 : d = (NUMERAL 0) => @lem1246773 P d h1 h0). Qed.
Lemma lem1246779 (P : nat -> Prop) (h1 : term133 P) : term143 P.
Proof. exact (fun d : nat => @lem1246774 d P h1). Qed.
Lemma lem1246780 (P : nat -> Prop) (h1 : term133 P) : (term133 P) = (term143 P).
Proof. exact (prop_ext (fun h2 : term133 P => @lem1246779 P h1) (fun h2 : term143 P => @lem1246471 P h1)). Qed.
Lemma lem1246781 (P : nat -> Prop) (h1 : term133 P) : term143 P.
Proof. exact (EQ_MP (@lem1246780 P h1) (@lem1246471 P h1)). Qed.
Lemma lem1246782 (P : nat -> Prop) : term162 P.
Proof. exact (fun h0 : term133 P => @lem1246781 P h0). Qed.
Lemma lem1246783 (e : nat) (P : nat -> Prop) (h1 : term149 e P) : (term149 e P) = (P e).
Proof. exact (prop_ext (fun h2 : term149 e P => @lem1246753 e P h1) (fun h2 : P e => @lem1246470 e P h1)). Qed.
Lemma lem1246784 (e : nat) (P : nat -> Prop) (h1 : term149 e P) : P e.
Proof. exact (EQ_MP (@lem1246783 e P h1) (@lem1246470 e P h1)). Qed.
Lemma lem1246785 (P : nat -> Prop) (e : nat) : term159 P e.
Proof. exact (fun h0 : term149 e P => @lem1246784 e P h0). Qed.
Lemma lem1246786 (P : nat -> Prop) (d : nat) (e : nat) (h1 : P e) (h2 : d = e) : (d = e) = (P d).
Proof. exact (prop_ext (fun h3 : d = e => @lem1246518 P d e h1 h2) (fun h3 : P d => @lem1246469 d e h2)). Qed.
Lemma lem1246787 (P : nat -> Prop) (d : nat) (e : nat) (h1 : P e) (h2 : d = e) : P d.
Proof. exact (EQ_MP (@lem1246786 P d e h1 h2) (@lem1246469 d e h2)). Qed.
Lemma lem1246788 (d : nat) (P : nat -> Prop) (e : nat) (h1 : P e) : term114 e P d.
Proof. exact (fun h0 : d = e => @lem1246787 P d e h1 h0). Qed.
Lemma lem1246793 (P : nat -> Prop) (e : nat) (h1 : P e) : term149 e P.
Proof. exact (fun d : nat => @lem1246788 d P e h1). Qed.
Lemma lem1246794 (P : nat -> Prop) (e : nat) (h1 : P e) : (P e) = (term149 e P).
Proof. exact (prop_ext (fun h2 : P e => @lem1246793 P e h1) (fun h2 : term149 e P => @lem1246468 P e h1)). Qed.
Lemma lem1246795 (P : nat -> Prop) (e : nat) (h1 : P e) : term149 e P.
Proof. exact (EQ_MP (@lem1246794 P e h1) (@lem1246468 P e h1)). Qed.
Lemma lem1246796 (e : nat) (P : nat -> Prop) : term160 e P.
Proof. exact (fun h0 : P e => @lem1246795 P e h0). Qed.
Lemma lem1246797 (P : nat -> Prop) (h1 : term143 P) : (term143 P) = (term133 P).
Proof. exact (prop_ext (fun h2 : term143 P => @lem1246754 P h1) (fun h2 : term133 P => @lem1246467 P h1)). Qed.
Lemma lem1246798 (P : nat -> Prop) (h1 : term143 P) : term133 P.
Proof. exact (EQ_MP (@lem1246797 P h1) (@lem1246467 P h1)). Qed.
Lemma lem1246799 (P : nat -> Prop) : term161 P.
Proof. exact (fun h0 : term143 P => @lem1246798 P h0). Qed.
Lemma lem1246800 (P : nat -> Prop) (d : nat) (h1 : term133 P) (h2 : d = (NUMERAL 0)) : (d = (NUMERAL 0)) = (P d).
Proof. exact (prop_ext (fun h3 : d = (NUMERAL 0) => @lem1246487 P d h1 h2) (fun h3 : P d => @lem1246466 d h2)). Qed.
Lemma lem1246801 (P : nat -> Prop) (d : nat) (h1 : term133 P) (h2 : d = (NUMERAL 0)) : P d.
Proof. exact (EQ_MP (@lem1246800 P d h1 h2) (@lem1246466 d h2)). Qed.
Lemma lem1246802 (d : nat) (P : nat -> Prop) (h1 : term133 P) : term139 P d.
Proof. exact (fun h0 : d = (NUMERAL 0) => @lem1246801 P d h1 h0). Qed.
Lemma lem1246807 (P : nat -> Prop) (h1 : term133 P) : term143 P.
Proof. exact (fun d : nat => @lem1246802 d P h1). Qed.
Lemma lem1246808 (P : nat -> Prop) (h1 : term133 P) : (term133 P) = (term143 P).
Proof. exact (prop_ext (fun h2 : term133 P => @lem1246807 P h1) (fun h2 : term143 P => @lem1246465 P h1)). Qed.
Lemma lem1246809 (P : nat -> Prop) (h1 : term133 P) : term143 P.
Proof. exact (EQ_MP (@lem1246808 P h1) (@lem1246465 P h1)). Qed.
Lemma lem1246810 (P : nat -> Prop) : term162 P.
Proof. exact (fun h0 : term133 P => @lem1246809 P h0). Qed.
Lemma lem1246811 (P : nat -> Prop) (e : nat) : term163 P e.
Proof. exact (conj (@lem1246768 e P) (@lem1246757 P e)). Qed.
Lemma lem1246812 (e : nat) (P : nat -> Prop) : (term163 P e) = ((P e) = (term149 e P)).
Proof. exact (@lem32 (P e) (term149 e P)). Qed.
Lemma lem1246813 (e : nat) (P : nat -> Prop) : (P e) = (term149 e P).
Proof. exact (EQ_MP (@lem1246812 e P) (@lem1246811 P e)). Qed.
Lemma lem1246814 (P : nat -> Prop) : term164 P.
Proof. exact (conj (@lem1246782 P) (@lem1246771 P)). Qed.
Lemma lem1246815 (P : nat -> Prop) : (term164 P) = ((term133 P) = (term143 P)).
Proof. exact (@lem32 (term133 P) (term143 P)). Qed.
Lemma lem1246816 (P : nat -> Prop) : (term133 P) = (term143 P).
Proof. exact (EQ_MP (@lem1246815 P) (@lem1246814 P)). Qed.
Lemma lem1246817 (P : nat -> Prop) (e : nat) : term163 P e.
Proof. exact (conj (@lem1246796 e P) (@lem1246785 P e)). Qed.
Lemma lem1246818 (e : nat) (P : nat -> Prop) : (term163 P e) = ((P e) = (term149 e P)).
Proof. exact (@lem32 (P e) (term149 e P)). Qed.
Lemma lem1246819 (e : nat) (P : nat -> Prop) : (P e) = (term149 e P).
Proof. exact (EQ_MP (@lem1246818 e P) (@lem1246817 P e)). Qed.
Lemma lem1246820 (P : nat -> Prop) : term164 P.
Proof. exact (conj (@lem1246810 P) (@lem1246799 P)). Qed.
Lemma lem1246821 (P : nat -> Prop) : (term164 P) = ((term133 P) = (term143 P)).
Proof. exact (@lem32 (term133 P) (term143 P)). Qed.
Lemma lem1246822 (P : nat -> Prop) : (term133 P) = (term143 P).
Proof. exact (EQ_MP (@lem1246821 P) (@lem1246820 P)). Qed.
Lemma lem1246823 (P : nat -> Prop) (e : nat) (h1 : term2 e) : (P e) = (term132 e P).
Proof. exact (EQ_MP (@lem1246464 P e h1) (@lem1246813 e P)). Qed.
Lemma lem1246824 (P : nat -> Prop) (e : nat) (h1 : e = (NUMERAL 0)) : (P e) = (term132 e P).
Proof. exact (EQ_MP (@lem1246389 P e h1) (@lem1246816 P)). Qed.
Lemma lem1246825 (P : nat -> Prop) (e : nat) (h1 : term2 e) : (P e) = (term129 e P).
Proof. exact (EQ_MP (@lem1246294 P e h1) (@lem1246819 e P)). Qed.
Lemma lem1246826 (P : nat -> Prop) (e : nat) (h1 : e = (NUMERAL 0)) : (P e) = (term129 e P).
Proof. exact (EQ_MP (@lem1246217 P e h1) (@lem1246822 P)). Qed.
Lemma lem1246827 (e : nat) (P : nat -> Prop) : (P e) = (term132 e P).
Proof. exact (or_elim (@lem1245576 e) (fun h0 : e = (NUMERAL 0) => @lem1246824 P e h0) (fun h0 : term2 e => @lem1246823 P e h0)). Qed.
Lemma lem1246828 (e : nat) (P : nat -> Prop) : (P e) = (term129 e P).
Proof. exact (or_elim (@lem1245576 e) (fun h0 : e = (NUMERAL 0) => @lem1246826 P e h0) (fun h0 : term2 e => @lem1246825 P e h0)). Qed.
Lemma lem1246829 (e : nat) (y : nat) (P : nat -> Prop) : (P e) = (term121 e y P).
Proof. exact (EQ_MP (@lem1246122 e y P) (@lem1246827 e P)). Qed.
Lemma lem1246830 (x : nat) (e : nat) (P : nat -> Prop) : (P e) = (term117 x e P).
Proof. exact (EQ_MP (@lem1246057 x e P) (@lem1246828 e P)). Qed.
Lemma lem1246831 (y : nat) (e : nat) (P : nat -> Prop) : (P e) = (term109 y e P).
Proof. exact (EQ_MP (@lem1245990 y e P) (@lem1246829 e y P)). Qed.
Lemma lem1246832 (x : nat) (e : nat) (P : nat -> Prop) : (P e) = (term101 x e P).
Proof. exact (EQ_MP (@lem1245965 x e P) (@lem1246830 x e P)). Qed.
Lemma lem1246833 (y : nat) (e : nat) (P : nat -> Prop) : (term88 P e) = (term76 y e P).
Proof. exact (EQ_MP (@lem1245940 y e P) (@lem1246831 y e P)). Qed.
Lemma lem1246834 (e : nat) (x : nat) (P : nat -> Prop) : (term82 P e) = (term67 e x P).
Proof. exact (EQ_MP (@lem1245885 e x P) (@lem1246832 x e P)). Qed.
Lemma lem1246835 (y : nat) (e : nat) (P : nat -> Prop) : (term75 P e y) = (term76 y e P).
Proof. exact (EQ_MP (@lem1245832 y e P) (@lem1246833 y e P)). Qed.
Lemma lem1246836 (e : nat) (x : nat) (P : nat -> Prop) : (term66 P x e) = (term67 e x P).
Proof. exact (EQ_MP (@lem1245790 e x P) (@lem1246834 e x P)). Qed.
Lemma lem1246837 (P : nat -> Prop) (x : nat) (y : nat) (e : nat) (h1 : x = (Nat.add y e)) : (term69 P x y) = (term70 y x P).
Proof. exact (EQ_MP (@lem1245748 P x y e h1) (@lem1246835 y e P)). Qed.
Lemma lem1246838 (P : nat -> Prop) (y : nat) (x : nat) (h1 : Peano.le y x) : (term69 P x y) = (term70 y x P).
Proof. exact (ex_elim (@lem1245734 y x h1) (fun e : nat => fun h0 : term165 x y e => @lem1246837 P x y e h0)). Qed.
Lemma lem1246839 (P : nat -> Prop) (y : nat) (x : nat) (e : nat) (h1 : y = (Nat.add x e)) : (term69 P x y) = (term70 y x P).
Proof. exact (EQ_MP (@lem1245724 P y x e h1) (@lem1246836 e x P)). Qed.
Lemma lem1246840 (P : nat -> Prop) (x : nat) (y : nat) (h1 : Peano.le x y) : (term69 P x y) = (term70 y x P).
Proof. exact (ex_elim (@lem1245710 x y h1) (fun e : nat => fun h0 : term165 y x e => @lem1246839 P y x e h0)). Qed.
Lemma lem1246841 (y : nat) (x : nat) (P : nat -> Prop) : (term69 P x y) = (term70 y x P).
Proof. exact (or_elim (@lem1245698 y x) (fun h0 : Peano.le x y => @lem1246840 P x y h0) (fun h0 : Peano.le y x => @lem1246838 P y x h0)). Qed.
