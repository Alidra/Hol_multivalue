Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2267725_term_abbrevs.
Require Import EXISTS_OR_THM_spec.
Require Import EXISTS_REFL_spec.
Require Import thm0_spec.
Require Import thm1340231_spec.
Require Import thm1831_spec.
Require Import thm2259383_spec.
Require Import thm2267613_spec.
Require Import thm7_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem2267617 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem2267618 {A : Type'} (x : A) (a : A) (h1 : x = a) : a = x.
Proof. exact (SYM (@lem2267617 A x a h1)). Qed.
Lemma lem2267619 {A : Type'} (a : A) (x : A) (h1 : a = x) : a = x.
Proof. exact (h1). Qed.
Lemma lem2267620 {A : Type'} (a : A) (x : A) (h1 : a = x) : x = a.
Proof. exact (SYM (@lem2267619 A a x h1)). Qed.
Lemma lem2267621 {A : Type'} (a : A) (x : A) : (x = a) = (a = x).
Proof. exact (prop_ext (fun h1 : x = a => @lem2267618 A x a h1) (fun h1 : a = x => @lem2267620 A a x h1)). Qed.
Lemma lem2267622 {A : Type'} (a : A) : (term0 A a) = (term1 A a).
Proof. exact (fun_ext (fun x : A => @lem2267621 A a x)). Qed.
Lemma lem2267623 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem2267624 {A : Type'} (a : A) : (term2 A a) = (term3 A a).
Proof. exact (MK_COMB (@lem2267623 A) (@lem2267622 A a)). Qed.
Lemma lem2267625 {A : Type'} : (term4 A) = (term5 A).
Proof. exact (fun_ext (fun a : A => @lem2267624 A a)). Qed.
Lemma lem2267626 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem2267627 {A : Type'} : (term6 A) = (term7 A).
Proof. exact (MK_COMB (@lem2267626 A) (@lem2267625 A)). Qed.
Lemma lem2267628 {A : Type'} : term7 A.
Proof. exact (EQ_MP (@lem2267627 A) (@lem4363 A)). Qed.
Lemma lem2267629 {A : Type'} (a : A) : term8 A a.
Proof. exact (@lem2267628 A a). Qed.
Lemma lem2267630 {A : Type'} (a : A) : (term8 A a) = (term3 A a).
Proof. exact (eq_refl (term8 A a)). Qed.
Lemma lem2267631 {A : Type'} (a : A) : term3 A a.
Proof. exact (EQ_MP (@lem2267630 A a) (@lem2267629 A a)). Qed.
Lemma lem2267632 {A : Type'} (a : A) : (term3 A a) = ((term3 A a) = True).
Proof. exact (@lem7 (term3 A a)). Qed.
Lemma lem2267634 {A : Type'} (P : A -> Prop) : term9 A P.
Proof. exact (@lem5418 A P). Qed.
Lemma lem2267635 {A : Type'} (P : A -> Prop) : (term9 A P) = (term10 A P).
Proof. exact (eq_refl (term9 A P)). Qed.
Lemma lem2267636 {A : Type'} (P : A -> Prop) : term10 A P.
Proof. exact (EQ_MP (@lem2267635 A P) (@lem2267634 A P)). Qed.
Lemma lem2267637 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term11 A P Q.
Proof. exact (@lem2267636 A P Q). Qed.
Lemma lem2267638 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term11 A P Q) = ((term12 A P Q) = (term13 A P Q)).
Proof. exact (eq_refl (term11 A P Q)). Qed.
Lemma lem2267640 (m : nat) : term14 m.
Proof. exact (@lem1340231 m). Qed.
Lemma lem2267641 (m : nat) : (term14 m) = (term15 m).
Proof. exact (eq_refl (term14 m)). Qed.
Lemma lem2267642 (m : nat) : term15 m.
Proof. exact (EQ_MP (@lem2267641 m) (@lem2267640 m)). Qed.
Lemma lem2267643 (m : nat) (n : nat) : term16 m n.
Proof. exact (@lem2267642 m n). Qed.
Lemma lem2267644 (m : nat) (n : nat) : (term16 m n) = (((real_of_num m) = (real_of_num n)) = (m = n)).
Proof. exact (eq_refl (term16 m n)). Qed.
Lemma lem2267647 (x : real) : (integer x) = (term17 x).
Proof. exact (EQ_MP (@lem2259383 x) (@lem2267613 x)). Qed.
Lemma lem2267648 : term18 = term19.
Proof. exact (@lem2267647 term20). Qed.
Lemma lem2267650 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term12 A P Q) = (term13 A P Q).
Proof. exact (EQ_MP (@lem2267638 A P Q) (@lem2267637 A P Q)). Qed.
Lemma lem2267651 (P : nat -> Prop) (Q : nat -> Prop) : (term21 P Q) = (term22 P Q).
Proof. exact (@lem2267650 nat P Q). Qed.
Lemma lem2267652 : term23 = term24.
Proof. exact (@lem2267651 term25 term26). Qed.
Lemma lem2267653 (n : nat) : (term27 n) = (term20 = (real_of_num n)).
Proof. exact (eq_refl (term27 n)). Qed.
Lemma lem2267654 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2267655 (n : nat) : (term28 n) = (term29 n).
Proof. exact (MK_COMB (@lem2267654) (@lem2267653 n)). Qed.
Lemma lem2267656 (n : nat) : (term30 n) = (term20 = (term31 n)).
Proof. exact (eq_refl (term30 n)). Qed.
Lemma lem2267657 (n : nat) : (term32 n) = (term33 n).
Proof. exact (MK_COMB (@lem2267655 n) (@lem2267656 n)). Qed.
Lemma lem2267658 : term34 = term35.
Proof. exact (fun_ext (fun n : nat => @lem2267657 n)). Qed.
Lemma lem2267659 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2267660 : term23 = term19.
Proof. exact (MK_COMB (@lem2267659) (@lem2267658)). Qed.
Lemma lem2267661 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2267662 : term36 = term37.
Proof. exact (MK_COMB (@lem2267661) (@lem2267660)). Qed.
Lemma lem2267663 (n : nat) : (term27 n) = (term20 = (real_of_num n)).
Proof. exact (eq_refl (term27 n)). Qed.
Lemma lem2267664 : term38 = term25.
Proof. exact (fun_ext (fun n : nat => @lem2267663 n)). Qed.
Lemma lem2267665 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2267666 : term39 = term40.
Proof. exact (MK_COMB (@lem2267665) (@lem2267664)). Qed.
Lemma lem2267667 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2267668 : term41 = term42.
Proof. exact (MK_COMB (@lem2267667) (@lem2267666)). Qed.
Lemma lem2267669 (n : nat) : (term30 n) = (term20 = (term31 n)).
Proof. exact (eq_refl (term30 n)). Qed.
Lemma lem2267670 : term43 = term26.
Proof. exact (fun_ext (fun n : nat => @lem2267669 n)). Qed.
Lemma lem2267671 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2267672 : term44 = term45.
Proof. exact (MK_COMB (@lem2267671) (@lem2267670)). Qed.
Lemma lem2267673 : term24 = term46.
Proof. exact (MK_COMB (@lem2267668) (@lem2267672)). Qed.
Lemma lem2267674 : (term23 = term24) = (term19 = term46).
Proof. exact (MK_COMB (@lem2267662) (@lem2267673)). Qed.
Lemma lem2267675 : term19 = term46.
Proof. exact (EQ_MP (@lem2267674) (@lem2267652)). Qed.
Lemma lem2267678 : term18 = term46.
Proof. exact (TRANS (@lem2267648) (@lem2267675)). Qed.
Lemma lem2267686 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = (m = n).
Proof. exact (EQ_MP (@lem2267644 m n) (@lem2267643 m n)). Qed.
Lemma lem2267687 (n : nat) : (term20 = (real_of_num n)) = ((NUMERAL 0) = n).
Proof. exact (@lem2267686 (NUMERAL 0) n). Qed.
Lemma lem2267690 : term25 = term47.
Proof. exact (fun_ext (fun n : nat => @lem2267687 n)). Qed.
Lemma lem2267691 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2267692 : term40 = term48.
Proof. exact (MK_COMB (@lem2267691) (@lem2267690)). Qed.
Lemma lem2267694 {A : Type'} (a : A) : (term3 A a) = True.
Proof. exact (EQ_MP (@lem2267632 A a) (@lem2267631 A a)). Qed.
Lemma lem2267695 (a : nat) : (term49 a) = True.
Proof. exact (@lem2267694 nat a). Qed.
Lemma lem2267696 : term48 = True.
Proof. exact (@lem2267695 (NUMERAL 0)). Qed.
Lemma lem2267697 : term40 = True.
Proof. exact (TRANS (@lem2267692) (@lem2267696)). Qed.
Lemma lem2267698 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2267699 : term42 = (or True).
Proof. exact (MK_COMB (@lem2267698) (@lem2267697)). Qed.
Lemma lem2267708 : term45 = term45.
Proof. exact (eq_refl term45). Qed.
Lemma lem2267709 : term46 = term50.
Proof. exact (MK_COMB (@lem2267699) (@lem2267708)). Qed.
Lemma lem2267711 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem2267712 : term50 = True.
Proof. exact (@lem2267711 term45). Qed.
Lemma lem2267713 : term46 = True.
Proof. exact (TRANS (@lem2267709) (@lem2267712)). Qed.
Lemma lem2267714 : term18 = True.
Proof. exact (TRANS (@lem2267678) (@lem2267713)). Qed.
Lemma lem2267715 : True = term18.
Proof. exact (SYM (@lem2267714)). Qed.
Lemma lem2267716 : term18.
Proof. exact (EQ_MP (@lem2267715) (@lem0)). Qed.
Lemma lem2267717 : term51.
Proof. exact (ex_intro term52 term20 (@lem2267716)). Qed.
Lemma lem2267719 {A : Type'} : (@ex A) = (term53 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem2267720 : (@ex real) = term54.
Proof. exact (@lem2267719 real). Qed.
Lemma lem2267721 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem2267722 : term51 = term55.
Proof. exact (MK_COMB (@lem2267720) (@lem2267721)). Qed.
Lemma lem2267723 : term55 = term56.
Proof. exact (eq_refl term55). Qed.
Lemma lem2267724 : term51 = term56.
Proof. exact (TRANS (@lem2267722) (@lem2267723)). Qed.
Lemma lem2267725 : term56.
Proof. exact (EQ_MP (@lem2267724) (@lem2267717)). Qed.
