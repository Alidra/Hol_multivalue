Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SKOLEM_THM_GEN_term_abbrevs.
Require Import RIGHT_IMP_EXISTS_THM_spec.
Require Import SKOLEM_THM_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem13547 {A B : Type'} (P : type1413 A B) : term0 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem13548 {A B : Type'} (P : type1413 A B) : (term0 A B P) = ((term1 A B P) = (term2 A B P)).
Proof. exact (eq_refl (term0 A B P)). Qed.
Lemma lem13550 {A : Type'} (P : Prop) : term3 A P.
Proof. exact (@lem12262 A P). Qed.
Lemma lem13551 {A : Type'} (P : Prop) : (term3 A P) = (term4 A P).
Proof. exact (eq_refl (term3 A P)). Qed.
Lemma lem13552 {A : Type'} (P : Prop) : term4 A P.
Proof. exact (EQ_MP (@lem13551 A P) (@lem13550 A P)). Qed.
Lemma lem13553 {A : Type'} (P : Prop) (Q : A -> Prop) : term5 A P Q.
Proof. exact (@lem13552 A P Q). Qed.
Lemma lem13554 {A : Type'} (P : Prop) (Q : A -> Prop) : (term5 A P Q) = ((term6 A P Q) = (term7 A P Q)).
Proof. exact (eq_refl (term5 A P Q)). Qed.
Lemma lem13571 {A : Type'} (P : Prop) (Q : A -> Prop) : (term6 A P Q) = (term7 A P Q).
Proof. exact (EQ_MP (@lem13554 A P Q) (@lem13553 A P Q)). Qed.
Lemma lem13572 {_2843 : Type'} (P : Prop) (Q : _2843 -> Prop) : (term6 _2843 P Q) = (term7 _2843 P Q).
Proof. exact (@lem13571 _2843 P Q). Qed.
Lemma lem13573 {_2843 _2845 : Type'} (P : _2845 -> Prop) (R : type1470 _2843 _2845) (x : _2845) : (term8 _2843 _2845 P R x) = (term9 _2843 _2845 P R x).
Proof. exact (@lem13572 _2843 (P x) (term10 _2843 _2845 R x)). Qed.
Lemma lem13574 {_2843 _2845 : Type'} (R : type1470 _2843 _2845) (x : _2845) (y : _2843) : (term11 _2843 _2845 R x y) = (R x y).
Proof. exact (eq_refl (term11 _2843 _2845 R x y)). Qed.
Lemma lem13575 {_2843 _2845 : Type'} (R : type1470 _2843 _2845) (x : _2845) : (term12 _2843 _2845 R x) = (term10 _2843 _2845 R x).
Proof. exact (fun_ext (fun y : _2843 => @lem13574 _2843 _2845 R x y)). Qed.
Lemma lem13576 {_2843 : Type'} : (@ex _2843) = (@ex _2843).
Proof. exact (eq_refl (@ex _2843)). Qed.
Lemma lem13577 {_2843 _2845 : Type'} (R : type1470 _2843 _2845) (x : _2845) : (term13 _2843 _2845 R x) = (term14 _2843 _2845 R x).
Proof. exact (MK_COMB (@lem13576 _2843) (@lem13575 _2843 _2845 R x)). Qed.
Lemma lem13578 {_2845 : Type'} (P : _2845 -> Prop) (x : _2845) : (term15 _2845 P x) = (term15 _2845 P x).
Proof. exact (eq_refl (term15 _2845 P x)). Qed.
Lemma lem13579 {_2843 _2845 : Type'} (P : _2845 -> Prop) (R : type1470 _2843 _2845) (x : _2845) : (term8 _2843 _2845 P R x) = (term16 _2843 _2845 P R x).
Proof. exact (MK_COMB (@lem13578 _2845 P x) (@lem13577 _2843 _2845 R x)). Qed.
Lemma lem13580 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem13581 {_2843 _2845 : Type'} (P : _2845 -> Prop) (R : type1470 _2843 _2845) (x : _2845) : (term17 _2843 _2845 P R x) = (term18 _2843 _2845 P R x).
Proof. exact (MK_COMB (@lem13580) (@lem13579 _2843 _2845 P R x)). Qed.
Lemma lem13582 {_2843 _2845 : Type'} (R : type1470 _2843 _2845) (x : _2845) (y : _2843) : (term11 _2843 _2845 R x y) = (R x y).
Proof. exact (eq_refl (term11 _2843 _2845 R x y)). Qed.
Lemma lem13583 {_2845 : Type'} (P : _2845 -> Prop) (x : _2845) : (term15 _2845 P x) = (term15 _2845 P x).
Proof. exact (eq_refl (term15 _2845 P x)). Qed.
Lemma lem13584 {_2843 _2845 : Type'} (P : _2845 -> Prop) (R : type1470 _2843 _2845) (x : _2845) (y : _2843) : (term19 _2843 _2845 P R x y) = (term20 _2843 _2845 P R x y).
Proof. exact (MK_COMB (@lem13583 _2845 P x) (@lem13582 _2843 _2845 R x y)). Qed.
Lemma lem13585 {_2843 _2845 : Type'} (P : _2845 -> Prop) (R : type1470 _2843 _2845) (x : _2845) : (term21 _2843 _2845 P R x) = (term22 _2843 _2845 P R x).
Proof. exact (fun_ext (fun y : _2843 => @lem13584 _2843 _2845 P R x y)). Qed.
Lemma lem13586 {_2843 : Type'} : (@ex _2843) = (@ex _2843).
Proof. exact (eq_refl (@ex _2843)). Qed.
Lemma lem13587 {_2843 _2845 : Type'} (P : _2845 -> Prop) (R : type1470 _2843 _2845) (x : _2845) : (term9 _2843 _2845 P R x) = (term23 _2843 _2845 P R x).
Proof. exact (MK_COMB (@lem13586 _2843) (@lem13585 _2843 _2845 P R x)). Qed.
Lemma lem13588 {_2843 _2845 : Type'} (P : _2845 -> Prop) (R : type1470 _2843 _2845) (x : _2845) : ((term8 _2843 _2845 P R x) = (term9 _2843 _2845 P R x)) = ((term16 _2843 _2845 P R x) = (term23 _2843 _2845 P R x)).
Proof. exact (MK_COMB (@lem13581 _2843 _2845 P R x) (@lem13587 _2843 _2845 P R x)). Qed.
Lemma lem13589 {_2843 _2845 : Type'} (P : _2845 -> Prop) (R : type1470 _2843 _2845) (x : _2845) : (term16 _2843 _2845 P R x) = (term23 _2843 _2845 P R x).
Proof. exact (EQ_MP (@lem13588 _2843 _2845 P R x) (@lem13573 _2843 _2845 P R x)). Qed.
Lemma lem13596 {_2843 _2845 : Type'} (P : _2845 -> Prop) (R : type1470 _2843 _2845) : (term24 _2843 _2845 P R) = (term25 _2843 _2845 P R).
Proof. exact (fun_ext (fun x : _2845 => @lem13589 _2843 _2845 P R x)). Qed.
Lemma lem13597 {_2845 : Type'} : (@all _2845) = (@all _2845).
Proof. exact (eq_refl (@all _2845)). Qed.
Lemma lem13598 {_2843 _2845 : Type'} (P : _2845 -> Prop) (R : type1470 _2843 _2845) : (term26 _2843 _2845 P R) = (term27 _2843 _2845 P R).
Proof. exact (MK_COMB (@lem13597 _2845) (@lem13596 _2843 _2845 P R)). Qed.
Lemma lem13600 {A B : Type'} (P : type1413 A B) : (term1 A B P) = (term2 A B P).
Proof. exact (EQ_MP (@lem13548 A B P) (@lem13547 A B P)). Qed.
Lemma lem13601 {_2843 _2845 : Type'} (P : type1470 _2843 _2845) : (term28 _2843 _2845 P) = (term29 _2843 _2845 P).
Proof. exact (@lem13600 _2845 _2843 P). Qed.
Lemma lem13602 {_2843 _2845 : Type'} (P : _2845 -> Prop) (R : type1470 _2843 _2845) : (term30 _2843 _2845 P R) = (term31 _2843 _2845 P R).
Proof. exact (@lem13601 _2843 _2845 (term32 _2843 _2845 P R)). Qed.
Lemma lem13603 {_2843 _2845 : Type'} (P : _2845 -> Prop) (R : type1470 _2843 _2845) (x : _2845) : (term33 _2843 _2845 P R x) = (term22 _2843 _2845 P R x).
Proof. exact (eq_refl (term33 _2843 _2845 P R x)). Qed.
Lemma lem13604 {_2843 : Type'} (y : _2843) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem13605 {_2843 _2845 : Type'} (P : _2845 -> Prop) (R : type1470 _2843 _2845) (x : _2845) (y : _2843) : (term34 _2843 _2845 P R x y) = (term35 _2843 _2845 P R x y).
Proof. exact (MK_COMB (@lem13603 _2843 _2845 P R x) (@lem13604 _2843 y)). Qed.
Lemma lem13606 {_2843 _2845 : Type'} (P : _2845 -> Prop) (R : type1470 _2843 _2845) (x : _2845) (y : _2843) : (term35 _2843 _2845 P R x y) = (term20 _2843 _2845 P R x y).
Proof. exact (eq_refl (term35 _2843 _2845 P R x y)). Qed.
Lemma lem13607 {_2843 _2845 : Type'} (P : _2845 -> Prop) (R : type1470 _2843 _2845) (x : _2845) (y : _2843) : (term34 _2843 _2845 P R x y) = (term20 _2843 _2845 P R x y).
Proof. exact (TRANS (@lem13605 _2843 _2845 P R x y) (@lem13606 _2843 _2845 P R x y)). Qed.
Lemma lem13608 {_2843 _2845 : Type'} (P : _2845 -> Prop) (R : type1470 _2843 _2845) (x : _2845) : (term36 _2843 _2845 P R x) = (term22 _2843 _2845 P R x).
Proof. exact (fun_ext (fun y : _2843 => @lem13607 _2843 _2845 P R x y)). Qed.
Lemma lem13609 {_2843 : Type'} : (@ex _2843) = (@ex _2843).
Proof. exact (eq_refl (@ex _2843)). Qed.
Lemma lem13610 {_2843 _2845 : Type'} (P : _2845 -> Prop) (R : type1470 _2843 _2845) (x : _2845) : (term37 _2843 _2845 P R x) = (term23 _2843 _2845 P R x).
Proof. exact (MK_COMB (@lem13609 _2843) (@lem13608 _2843 _2845 P R x)). Qed.
Lemma lem13611 {_2843 _2845 : Type'} (P : _2845 -> Prop) (R : type1470 _2843 _2845) : (term38 _2843 _2845 P R) = (term25 _2843 _2845 P R).
Proof. exact (fun_ext (fun x : _2845 => @lem13610 _2843 _2845 P R x)). Qed.
Lemma lem13612 {_2845 : Type'} : (@all _2845) = (@all _2845).
Proof. exact (eq_refl (@all _2845)). Qed.
Lemma lem13613 {_2843 _2845 : Type'} (P : _2845 -> Prop) (R : type1470 _2843 _2845) : (term30 _2843 _2845 P R) = (term27 _2843 _2845 P R).
Proof. exact (MK_COMB (@lem13612 _2845) (@lem13611 _2843 _2845 P R)). Qed.
Lemma lem13614 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem13615 {_2843 _2845 : Type'} (P : _2845 -> Prop) (R : type1470 _2843 _2845) : (term39 _2843 _2845 P R) = (term40 _2843 _2845 P R).
Proof. exact (MK_COMB (@lem13614) (@lem13613 _2843 _2845 P R)). Qed.
Lemma lem13616 {_2843 _2845 : Type'} (P : _2845 -> Prop) (R : type1470 _2843 _2845) (x : _2845) : (term33 _2843 _2845 P R x) = (term22 _2843 _2845 P R x).
Proof. exact (eq_refl (term33 _2843 _2845 P R x)). Qed.
Lemma lem13617 {_2843 _2845 : Type'} (y : _2845 -> _2843) (x : _2845) : (y x) = (y x).
Proof. exact (eq_refl (y x)). Qed.
Lemma lem13618 {_2843 _2845 : Type'} (P : _2845 -> Prop) (R : type1470 _2843 _2845) (y : _2845 -> _2843) (x : _2845) : (term41 _2843 _2845 P R y x) = (term42 _2843 _2845 P R y x).
Proof. exact (MK_COMB (@lem13616 _2843 _2845 P R x) (@lem13617 _2843 _2845 y x)). Qed.
Lemma lem13619 {_2843 _2845 : Type'} (P : _2845 -> Prop) (R : type1470 _2843 _2845) (y : _2845 -> _2843) (x : _2845) : (term42 _2843 _2845 P R y x) = (term43 _2843 _2845 P R y x).
Proof. exact (eq_refl (term42 _2843 _2845 P R y x)). Qed.
Lemma lem13620 {_2843 _2845 : Type'} (P : _2845 -> Prop) (R : type1470 _2843 _2845) (y : _2845 -> _2843) (x : _2845) : (term41 _2843 _2845 P R y x) = (term43 _2843 _2845 P R y x).
Proof. exact (TRANS (@lem13618 _2843 _2845 P R y x) (@lem13619 _2843 _2845 P R y x)). Qed.
Lemma lem13621 {_2843 _2845 : Type'} (P : _2845 -> Prop) (R : type1470 _2843 _2845) (y : _2845 -> _2843) : (term44 _2843 _2845 P R y) = (term45 _2843 _2845 P R y).
Proof. exact (fun_ext (fun x : _2845 => @lem13620 _2843 _2845 P R y x)). Qed.
Lemma lem13622 {_2845 : Type'} : (@all _2845) = (@all _2845).
Proof. exact (eq_refl (@all _2845)). Qed.
Lemma lem13623 {_2843 _2845 : Type'} (P : _2845 -> Prop) (R : type1470 _2843 _2845) (y : _2845 -> _2843) : (term46 _2843 _2845 P R y) = (term47 _2843 _2845 P R y).
Proof. exact (MK_COMB (@lem13622 _2845) (@lem13621 _2843 _2845 P R y)). Qed.
Lemma lem13624 {_2843 _2845 : Type'} (P : _2845 -> Prop) (R : type1470 _2843 _2845) : (term48 _2843 _2845 P R) = (term49 _2843 _2845 P R).
Proof. exact (fun_ext (fun y : _2845 -> _2843 => @lem13623 _2843 _2845 P R y)). Qed.
Lemma lem13625 {_2843 _2845 : Type'} : (@ex (_2845 -> _2843)) = (@ex (_2845 -> _2843)).
Proof. exact (eq_refl (@ex (_2845 -> _2843))). Qed.
Lemma lem13626 {_2843 _2845 : Type'} (P : _2845 -> Prop) (R : type1470 _2843 _2845) : (term31 _2843 _2845 P R) = (term50 _2843 _2845 P R).
Proof. exact (MK_COMB (@lem13625 _2843 _2845) (@lem13624 _2843 _2845 P R)). Qed.
Lemma lem13627 {_2843 _2845 : Type'} (P : _2845 -> Prop) (R : type1470 _2843 _2845) : ((term30 _2843 _2845 P R) = (term31 _2843 _2845 P R)) = ((term27 _2843 _2845 P R) = (term50 _2843 _2845 P R)).
Proof. exact (MK_COMB (@lem13615 _2843 _2845 P R) (@lem13626 _2843 _2845 P R)). Qed.
Lemma lem13628 {_2843 _2845 : Type'} (P : _2845 -> Prop) (R : type1470 _2843 _2845) : (term27 _2843 _2845 P R) = (term50 _2843 _2845 P R).
Proof. exact (EQ_MP (@lem13627 _2843 _2845 P R) (@lem13602 _2843 _2845 P R)). Qed.
Lemma lem13639 {_2843 _2845 : Type'} (P : _2845 -> Prop) (R : type1470 _2843 _2845) : (term26 _2843 _2845 P R) = (term50 _2843 _2845 P R).
Proof. exact (TRANS (@lem13598 _2843 _2845 P R) (@lem13628 _2843 _2845 P R)). Qed.
Lemma lem13640 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem13641 {_2843 _2845 : Type'} (P : _2845 -> Prop) (R : type1470 _2843 _2845) : (term51 _2843 _2845 P R) = (term52 _2843 _2845 P R).
Proof. exact (MK_COMB (@lem13640) (@lem13639 _2843 _2845 P R)). Qed.
Lemma lem13652 {_2843 _2845 : Type'} (P : _2845 -> Prop) (R : type1470 _2843 _2845) : (term50 _2843 _2845 P R) = (term50 _2843 _2845 P R).
Proof. exact (eq_refl (term50 _2843 _2845 P R)). Qed.
Lemma lem13653 {_2843 _2845 : Type'} (P : _2845 -> Prop) (R : type1470 _2843 _2845) : ((term26 _2843 _2845 P R) = (term50 _2843 _2845 P R)) = ((term50 _2843 _2845 P R) = (term50 _2843 _2845 P R)).
Proof. exact (MK_COMB (@lem13641 _2843 _2845 P R) (@lem13652 _2843 _2845 P R)). Qed.
Lemma lem13655 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem13656 (x : Prop) : (x = x) = True.
Proof. exact (@lem13655 Prop x). Qed.
Lemma lem13657 {_2843 _2845 : Type'} (P : _2845 -> Prop) (R : type1470 _2843 _2845) : ((term50 _2843 _2845 P R) = (term50 _2843 _2845 P R)) = True.
Proof. exact (@lem13656 (term50 _2843 _2845 P R)). Qed.
Lemma lem13660 {_2843 _2845 : Type'} (P : _2845 -> Prop) (R : type1470 _2843 _2845) : (term53 _2843 _2845 P R) = (term53 _2843 _2845 P R).
Proof. exact (eq_refl (term53 _2843 _2845 P R)). Qed.
Lemma lem13661 {_2843 _2845 : Type'} (P : _2845 -> Prop) (R : type1470 _2843 _2845) : (term53 _2843 _2845 P R) = (((term50 _2843 _2845 P R) = (term50 _2843 _2845 P R)) = True).
Proof. exact (eq_refl (term53 _2843 _2845 P R)). Qed.
Lemma lem13662 {_2843 _2845 : Type'} (P : _2845 -> Prop) (R : type1470 _2843 _2845) : (term54 _2843 _2845 P R) = (term54 _2843 _2845 P R).
Proof. exact (eq_refl (term54 _2843 _2845 P R)). Qed.
Lemma lem13663 {_2843 _2845 : Type'} (P : _2845 -> Prop) (R : type1470 _2843 _2845) : ((term53 _2843 _2845 P R) = (term53 _2843 _2845 P R)) = ((term53 _2843 _2845 P R) = (((term50 _2843 _2845 P R) = (term50 _2843 _2845 P R)) = True)).
Proof. exact (MK_COMB (@lem13662 _2843 _2845 P R) (@lem13661 _2843 _2845 P R)). Qed.
Lemma lem13664 {_2843 _2845 : Type'} (P : _2845 -> Prop) (R : type1470 _2843 _2845) : (term53 _2843 _2845 P R) = (((term50 _2843 _2845 P R) = (term50 _2843 _2845 P R)) = True).
Proof. exact (eq_refl (term53 _2843 _2845 P R)). Qed.
Lemma lem13665 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem13666 {_2843 _2845 : Type'} (P : _2845 -> Prop) (R : type1470 _2843 _2845) : (term54 _2843 _2845 P R) = (term55 _2843 _2845 P R).
Proof. exact (MK_COMB (@lem13665) (@lem13664 _2843 _2845 P R)). Qed.
Lemma lem13667 {_2843 _2845 : Type'} (P : _2845 -> Prop) (R : type1470 _2843 _2845) : (((term50 _2843 _2845 P R) = (term50 _2843 _2845 P R)) = True) = (((term50 _2843 _2845 P R) = (term50 _2843 _2845 P R)) = True).
Proof. exact (eq_refl (((term50 _2843 _2845 P R) = (term50 _2843 _2845 P R)) = True)). Qed.
Lemma lem13668 {_2843 _2845 : Type'} (P : _2845 -> Prop) (R : type1470 _2843 _2845) : ((term53 _2843 _2845 P R) = (((term50 _2843 _2845 P R) = (term50 _2843 _2845 P R)) = True)) = ((((term50 _2843 _2845 P R) = (term50 _2843 _2845 P R)) = True) = (((term50 _2843 _2845 P R) = (term50 _2843 _2845 P R)) = True)).
Proof. exact (MK_COMB (@lem13666 _2843 _2845 P R) (@lem13667 _2843 _2845 P R)). Qed.
Lemma lem13669 {_2843 _2845 : Type'} (P : _2845 -> Prop) (R : type1470 _2843 _2845) : ((term53 _2843 _2845 P R) = (term53 _2843 _2845 P R)) = ((((term50 _2843 _2845 P R) = (term50 _2843 _2845 P R)) = True) = (((term50 _2843 _2845 P R) = (term50 _2843 _2845 P R)) = True)).
Proof. exact (TRANS (@lem13663 _2843 _2845 P R) (@lem13668 _2843 _2845 P R)). Qed.
Lemma lem13670 {_2843 _2845 : Type'} (P : _2845 -> Prop) (R : type1470 _2843 _2845) : (((term50 _2843 _2845 P R) = (term50 _2843 _2845 P R)) = True) = (((term50 _2843 _2845 P R) = (term50 _2843 _2845 P R)) = True).
Proof. exact (EQ_MP (@lem13669 _2843 _2845 P R) (@lem13660 _2843 _2845 P R)). Qed.
Lemma lem13671 {_2843 _2845 : Type'} (P : _2845 -> Prop) (R : type1470 _2843 _2845) : ((term50 _2843 _2845 P R) = (term50 _2843 _2845 P R)) = True.
Proof. exact (EQ_MP (@lem13670 _2843 _2845 P R) (@lem13657 _2843 _2845 P R)). Qed.
Lemma lem13672 {_2843 _2845 : Type'} (P : _2845 -> Prop) (R : type1470 _2843 _2845) : ((term26 _2843 _2845 P R) = (term50 _2843 _2845 P R)) = True.
Proof. exact (TRANS (@lem13653 _2843 _2845 P R) (@lem13671 _2843 _2845 P R)). Qed.
Lemma lem13673 {_2843 _2845 : Type'} (P : _2845 -> Prop) : (term56 _2843 _2845 P) = (term57 _2843 _2845).
Proof. exact (fun_ext (fun R : type1470 _2843 _2845 => @lem13672 _2843 _2845 P R)). Qed.
Lemma lem13674 {_2843 _2845 : Type'} : (@all (_2845 -> _2843 -> Prop)) = (@all (_2845 -> _2843 -> Prop)).
Proof. exact (eq_refl (@all (_2845 -> _2843 -> Prop))). Qed.
Lemma lem13675 {_2843 _2845 : Type'} (P : _2845 -> Prop) : (term58 _2843 _2845 P) = (term59 _2843 _2845).
Proof. exact (MK_COMB (@lem13674 _2843 _2845) (@lem13673 _2843 _2845 P)). Qed.
Lemma lem13677 {A : Type'} (t : Prop) : (term60 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem13678 {_2843 _2845 : Type'} (t : Prop) : (term61 _2843 _2845 t) = t.
Proof. exact (@lem13677 (type1470 _2843 _2845) t). Qed.
Lemma lem13679 {_2843 _2845 : Type'} : (term59 _2843 _2845) = True.
Proof. exact (@lem13678 _2843 _2845 True). Qed.
Lemma lem13680 {_2843 _2845 : Type'} (P : _2845 -> Prop) : (term58 _2843 _2845 P) = True.
Proof. exact (TRANS (@lem13675 _2843 _2845 P) (@lem13679 _2843 _2845)). Qed.
Lemma lem13681 {_2843 _2845 : Type'} : (term62 _2843 _2845) = (term63 _2845).
Proof. exact (fun_ext (fun P : _2845 -> Prop => @lem13680 _2843 _2845 P)). Qed.
Lemma lem13682 {_2845 : Type'} : (@all (_2845 -> Prop)) = (@all (_2845 -> Prop)).
Proof. exact (eq_refl (@all (_2845 -> Prop))). Qed.
Lemma lem13683 {_2843 _2845 : Type'} : (term64 _2843 _2845) = (term65 _2845).
Proof. exact (MK_COMB (@lem13682 _2845) (@lem13681 _2843 _2845)). Qed.
Lemma lem13685 {A : Type'} (t : Prop) : (term60 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem13686 {_2845 : Type'} (t : Prop) : (term66 _2845 t) = t.
Proof. exact (@lem13685 (_2845 -> Prop) t). Qed.
Lemma lem13687 {_2845 : Type'} : (term65 _2845) = True.
Proof. exact (@lem13686 _2845 True). Qed.
Lemma lem13688 {_2843 _2845 : Type'} : (term64 _2843 _2845) = True.
Proof. exact (TRANS (@lem13683 _2843 _2845) (@lem13687 _2845)). Qed.
Lemma lem13689 {_2843 _2845 : Type'} : True = (term64 _2843 _2845).
Proof. exact (SYM (@lem13688 _2843 _2845)). Qed.
Lemma lem13690 {_2843 _2845 : Type'} : term64 _2843 _2845.
Proof. exact (EQ_MP (@lem13689 _2843 _2845) (@lem0)). Qed.
