Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SURJECTIVE_ON_RIGHT_INVERSE_term_abbrevs.
Require Import RIGHT_IMP_EXISTS_THM_spec.
Require Import SKOLEM_THM_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem3562582 {A B : Type'} (P : type1413 A B) : term0 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem3562583 {A B : Type'} (P : type1413 A B) : (term0 A B P) = ((term1 A B P) = (term2 A B P)).
Proof. exact (eq_refl (term0 A B P)). Qed.
Lemma lem3562585 {A : Type'} (P : Prop) : term3 A P.
Proof. exact (@lem12262 A P). Qed.
Lemma lem3562586 {A : Type'} (P : Prop) : (term3 A P) = (term4 A P).
Proof. exact (eq_refl (term3 A P)). Qed.
Lemma lem3562587 {A : Type'} (P : Prop) : term4 A P.
Proof. exact (EQ_MP (@lem3562586 A P) (@lem3562585 A P)). Qed.
Lemma lem3562588 {A : Type'} (P : Prop) (Q : A -> Prop) : term5 A P Q.
Proof. exact (@lem3562587 A P Q). Qed.
Lemma lem3562589 {A : Type'} (P : Prop) (Q : A -> Prop) : (term5 A P Q) = ((term6 A P Q) = (term7 A P Q)).
Proof. exact (eq_refl (term5 A P Q)). Qed.
Lemma lem3562606 {A : Type'} (P : Prop) (Q : A -> Prop) : (term6 A P Q) = (term7 A P Q).
Proof. exact (EQ_MP (@lem3562589 A P Q) (@lem3562588 A P Q)). Qed.
Lemma lem3562607 {_91307 : Type'} (P : Prop) (Q : _91307 -> Prop) : (term6 _91307 P Q) = (term7 _91307 P Q).
Proof. exact (@lem3562606 _91307 P Q). Qed.
Lemma lem3562608 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) (y : _91308) : (term8 _91307 _91308 t s f y) = (term9 _91307 _91308 t s f y).
Proof. exact (@lem3562607 _91307 (@IN _91308 y t) (term10 _91307 _91308 s f y)). Qed.
Lemma lem3562609 {_91307 _91308 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91308) (x : _91307) (y : _91308) : (term11 _91307 _91308 s f y x) = (term12 _91307 _91308 s f x y).
Proof. exact (eq_refl (term11 _91307 _91308 s f y x)). Qed.
Lemma lem3562610 {_91307 _91308 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91308) (y : _91308) : (term13 _91307 _91308 s f y) = (term10 _91307 _91308 s f y).
Proof. exact (fun_ext (fun x : _91307 => @lem3562609 _91307 _91308 s f x y)). Qed.
Lemma lem3562611 {_91307 : Type'} : (@ex _91307) = (@ex _91307).
Proof. exact (eq_refl (@ex _91307)). Qed.
Lemma lem3562612 {_91307 _91308 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91308) (y : _91308) : (term14 _91307 _91308 s f y) = (term15 _91307 _91308 s f y).
Proof. exact (MK_COMB (@lem3562611 _91307) (@lem3562610 _91307 _91308 s f y)). Qed.
Lemma lem3562613 {_91308 : Type'} (y : _91308) (t : _91308 -> Prop) : (term16 _91308 y t) = (term16 _91308 y t).
Proof. exact (eq_refl (term16 _91308 y t)). Qed.
Lemma lem3562614 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) (y : _91308) : (term8 _91307 _91308 t s f y) = (term17 _91307 _91308 t s f y).
Proof. exact (MK_COMB (@lem3562613 _91308 y t) (@lem3562612 _91307 _91308 s f y)). Qed.
Lemma lem3562615 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3562616 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) (y : _91308) : (term18 _91307 _91308 t s f y) = (term19 _91307 _91308 t s f y).
Proof. exact (MK_COMB (@lem3562615) (@lem3562614 _91307 _91308 t s f y)). Qed.
Lemma lem3562617 {_91307 _91308 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91308) (x : _91307) (y : _91308) : (term11 _91307 _91308 s f y x) = (term12 _91307 _91308 s f x y).
Proof. exact (eq_refl (term11 _91307 _91308 s f y x)). Qed.
Lemma lem3562618 {_91308 : Type'} (y : _91308) (t : _91308 -> Prop) : (term16 _91308 y t) = (term16 _91308 y t).
Proof. exact (eq_refl (term16 _91308 y t)). Qed.
Lemma lem3562619 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) (x : _91307) (y : _91308) : (term20 _91307 _91308 t s f y x) = (term21 _91307 _91308 t s f x y).
Proof. exact (MK_COMB (@lem3562618 _91308 y t) (@lem3562617 _91307 _91308 s f x y)). Qed.
Lemma lem3562620 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) (y : _91308) : (term22 _91307 _91308 t s f y) = (term23 _91307 _91308 t s f y).
Proof. exact (fun_ext (fun x : _91307 => @lem3562619 _91307 _91308 t s f x y)). Qed.
Lemma lem3562621 {_91307 : Type'} : (@ex _91307) = (@ex _91307).
Proof. exact (eq_refl (@ex _91307)). Qed.
Lemma lem3562622 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) (y : _91308) : (term9 _91307 _91308 t s f y) = (term24 _91307 _91308 t s f y).
Proof. exact (MK_COMB (@lem3562621 _91307) (@lem3562620 _91307 _91308 t s f y)). Qed.
Lemma lem3562623 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) (y : _91308) : ((term8 _91307 _91308 t s f y) = (term9 _91307 _91308 t s f y)) = ((term17 _91307 _91308 t s f y) = (term24 _91307 _91308 t s f y)).
Proof. exact (MK_COMB (@lem3562616 _91307 _91308 t s f y) (@lem3562622 _91307 _91308 t s f y)). Qed.
Lemma lem3562624 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) (y : _91308) : (term17 _91307 _91308 t s f y) = (term24 _91307 _91308 t s f y).
Proof. exact (EQ_MP (@lem3562623 _91307 _91308 t s f y) (@lem3562608 _91307 _91308 t s f y)). Qed.
Lemma lem3562635 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) : (term25 _91307 _91308 t s f) = (term26 _91307 _91308 t s f).
Proof. exact (fun_ext (fun y : _91308 => @lem3562624 _91307 _91308 t s f y)). Qed.
Lemma lem3562636 {_91308 : Type'} : (@all _91308) = (@all _91308).
Proof. exact (eq_refl (@all _91308)). Qed.
Lemma lem3562637 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) : (term27 _91307 _91308 t s f) = (term28 _91307 _91308 t s f).
Proof. exact (MK_COMB (@lem3562636 _91308) (@lem3562635 _91307 _91308 t s f)). Qed.
Lemma lem3562639 {A B : Type'} (P : type1413 A B) : (term1 A B P) = (term2 A B P).
Proof. exact (EQ_MP (@lem3562583 A B P) (@lem3562582 A B P)). Qed.
Lemma lem3562640 {_91307 _91308 : Type'} (P : type1470 _91307 _91308) : (term29 _91307 _91308 P) = (term30 _91307 _91308 P).
Proof. exact (@lem3562639 _91308 _91307 P). Qed.
Lemma lem3562641 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) : (term31 _91307 _91308 t s f) = (term32 _91307 _91308 t s f).
Proof. exact (@lem3562640 _91307 _91308 (term33 _91307 _91308 t s f)). Qed.
Lemma lem3562642 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) (y : _91308) : (term34 _91307 _91308 t s f y) = (term23 _91307 _91308 t s f y).
Proof. exact (eq_refl (term34 _91307 _91308 t s f y)). Qed.
Lemma lem3562643 {_91307 : Type'} (x : _91307) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3562644 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) (y : _91308) (x : _91307) : (term35 _91307 _91308 t s f y x) = (term36 _91307 _91308 t s f y x).
Proof. exact (MK_COMB (@lem3562642 _91307 _91308 t s f y) (@lem3562643 _91307 x)). Qed.
Lemma lem3562645 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) (x : _91307) (y : _91308) : (term36 _91307 _91308 t s f y x) = (term21 _91307 _91308 t s f x y).
Proof. exact (eq_refl (term36 _91307 _91308 t s f y x)). Qed.
Lemma lem3562646 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) (x : _91307) (y : _91308) : (term35 _91307 _91308 t s f y x) = (term21 _91307 _91308 t s f x y).
Proof. exact (TRANS (@lem3562644 _91307 _91308 t s f y x) (@lem3562645 _91307 _91308 t s f x y)). Qed.
Lemma lem3562647 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) (y : _91308) : (term37 _91307 _91308 t s f y) = (term23 _91307 _91308 t s f y).
Proof. exact (fun_ext (fun x : _91307 => @lem3562646 _91307 _91308 t s f x y)). Qed.
Lemma lem3562648 {_91307 : Type'} : (@ex _91307) = (@ex _91307).
Proof. exact (eq_refl (@ex _91307)). Qed.
Lemma lem3562649 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) (y : _91308) : (term38 _91307 _91308 t s f y) = (term24 _91307 _91308 t s f y).
Proof. exact (MK_COMB (@lem3562648 _91307) (@lem3562647 _91307 _91308 t s f y)). Qed.
Lemma lem3562650 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) : (term39 _91307 _91308 t s f) = (term26 _91307 _91308 t s f).
Proof. exact (fun_ext (fun y : _91308 => @lem3562649 _91307 _91308 t s f y)). Qed.
Lemma lem3562651 {_91308 : Type'} : (@all _91308) = (@all _91308).
Proof. exact (eq_refl (@all _91308)). Qed.
Lemma lem3562652 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) : (term31 _91307 _91308 t s f) = (term28 _91307 _91308 t s f).
Proof. exact (MK_COMB (@lem3562651 _91308) (@lem3562650 _91307 _91308 t s f)). Qed.
Lemma lem3562653 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3562654 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) : (term40 _91307 _91308 t s f) = (term41 _91307 _91308 t s f).
Proof. exact (MK_COMB (@lem3562653) (@lem3562652 _91307 _91308 t s f)). Qed.
Lemma lem3562655 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) (y : _91308) : (term34 _91307 _91308 t s f y) = (term23 _91307 _91308 t s f y).
Proof. exact (eq_refl (term34 _91307 _91308 t s f y)). Qed.
Lemma lem3562656 {_91307 _91308 : Type'} (x : _91308 -> _91307) (y : _91308) : (x y) = (x y).
Proof. exact (eq_refl (x y)). Qed.
Lemma lem3562657 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) (x : _91308 -> _91307) (y : _91308) : (term42 _91307 _91308 t s f x y) = (term43 _91307 _91308 t s f x y).
Proof. exact (MK_COMB (@lem3562655 _91307 _91308 t s f y) (@lem3562656 _91307 _91308 x y)). Qed.
Lemma lem3562658 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) (x : _91308 -> _91307) (y : _91308) : (term43 _91307 _91308 t s f x y) = (term44 _91307 _91308 t s f x y).
Proof. exact (eq_refl (term43 _91307 _91308 t s f x y)). Qed.
Lemma lem3562659 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) (x : _91308 -> _91307) (y : _91308) : (term42 _91307 _91308 t s f x y) = (term44 _91307 _91308 t s f x y).
Proof. exact (TRANS (@lem3562657 _91307 _91308 t s f x y) (@lem3562658 _91307 _91308 t s f x y)). Qed.
Lemma lem3562660 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) (x : _91308 -> _91307) : (term45 _91307 _91308 t s f x) = (term46 _91307 _91308 t s f x).
Proof. exact (fun_ext (fun y : _91308 => @lem3562659 _91307 _91308 t s f x y)). Qed.
Lemma lem3562661 {_91308 : Type'} : (@all _91308) = (@all _91308).
Proof. exact (eq_refl (@all _91308)). Qed.
Lemma lem3562662 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) (x : _91308 -> _91307) : (term47 _91307 _91308 t s f x) = (term48 _91307 _91308 t s f x).
Proof. exact (MK_COMB (@lem3562661 _91308) (@lem3562660 _91307 _91308 t s f x)). Qed.
Lemma lem3562663 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) : (term49 _91307 _91308 t s f) = (term50 _91307 _91308 t s f).
Proof. exact (fun_ext (fun x : _91308 -> _91307 => @lem3562662 _91307 _91308 t s f x)). Qed.
Lemma lem3562664 {_91307 _91308 : Type'} : (@ex (_91308 -> _91307)) = (@ex (_91308 -> _91307)).
Proof. exact (eq_refl (@ex (_91308 -> _91307))). Qed.
Lemma lem3562665 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) : (term32 _91307 _91308 t s f) = (term51 _91307 _91308 t s f).
Proof. exact (MK_COMB (@lem3562664 _91307 _91308) (@lem3562663 _91307 _91308 t s f)). Qed.
Lemma lem3562666 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) : ((term31 _91307 _91308 t s f) = (term32 _91307 _91308 t s f)) = ((term28 _91307 _91308 t s f) = (term51 _91307 _91308 t s f)).
Proof. exact (MK_COMB (@lem3562654 _91307 _91308 t s f) (@lem3562665 _91307 _91308 t s f)). Qed.
Lemma lem3562667 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) : (term28 _91307 _91308 t s f) = (term51 _91307 _91308 t s f).
Proof. exact (EQ_MP (@lem3562666 _91307 _91308 t s f) (@lem3562641 _91307 _91308 t s f)). Qed.
Lemma lem3562682 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) : (term27 _91307 _91308 t s f) = (term51 _91307 _91308 t s f).
Proof. exact (TRANS (@lem3562637 _91307 _91308 t s f) (@lem3562667 _91307 _91308 t s f)). Qed.
Lemma lem3562683 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3562684 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) : (term52 _91307 _91308 t s f) = (term53 _91307 _91308 t s f).
Proof. exact (MK_COMB (@lem3562683) (@lem3562682 _91307 _91308 t s f)). Qed.
Lemma lem3562699 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) : (term51 _91307 _91308 t s f) = (term51 _91307 _91308 t s f).
Proof. exact (eq_refl (term51 _91307 _91308 t s f)). Qed.
Lemma lem3562700 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) : ((term27 _91307 _91308 t s f) = (term51 _91307 _91308 t s f)) = ((term51 _91307 _91308 t s f) = (term51 _91307 _91308 t s f)).
Proof. exact (MK_COMB (@lem3562684 _91307 _91308 t s f) (@lem3562699 _91307 _91308 t s f)). Qed.
Lemma lem3562702 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3562703 (x : Prop) : (x = x) = True.
Proof. exact (@lem3562702 Prop x). Qed.
Lemma lem3562704 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) : ((term51 _91307 _91308 t s f) = (term51 _91307 _91308 t s f)) = True.
Proof. exact (@lem3562703 (term51 _91307 _91308 t s f)). Qed.
Lemma lem3562707 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) : (term54 _91307 _91308 t s f) = (term54 _91307 _91308 t s f).
Proof. exact (eq_refl (term54 _91307 _91308 t s f)). Qed.
Lemma lem3562708 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) : (term54 _91307 _91308 t s f) = (((term51 _91307 _91308 t s f) = (term51 _91307 _91308 t s f)) = True).
Proof. exact (eq_refl (term54 _91307 _91308 t s f)). Qed.
Lemma lem3562709 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) : (term55 _91307 _91308 t s f) = (term55 _91307 _91308 t s f).
Proof. exact (eq_refl (term55 _91307 _91308 t s f)). Qed.
Lemma lem3562710 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) : ((term54 _91307 _91308 t s f) = (term54 _91307 _91308 t s f)) = ((term54 _91307 _91308 t s f) = (((term51 _91307 _91308 t s f) = (term51 _91307 _91308 t s f)) = True)).
Proof. exact (MK_COMB (@lem3562709 _91307 _91308 t s f) (@lem3562708 _91307 _91308 t s f)). Qed.
Lemma lem3562711 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) : (term54 _91307 _91308 t s f) = (((term51 _91307 _91308 t s f) = (term51 _91307 _91308 t s f)) = True).
Proof. exact (eq_refl (term54 _91307 _91308 t s f)). Qed.
Lemma lem3562712 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3562713 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) : (term55 _91307 _91308 t s f) = (term56 _91307 _91308 t s f).
Proof. exact (MK_COMB (@lem3562712) (@lem3562711 _91307 _91308 t s f)). Qed.
Lemma lem3562714 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) : (((term51 _91307 _91308 t s f) = (term51 _91307 _91308 t s f)) = True) = (((term51 _91307 _91308 t s f) = (term51 _91307 _91308 t s f)) = True).
Proof. exact (eq_refl (((term51 _91307 _91308 t s f) = (term51 _91307 _91308 t s f)) = True)). Qed.
Lemma lem3562715 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) : ((term54 _91307 _91308 t s f) = (((term51 _91307 _91308 t s f) = (term51 _91307 _91308 t s f)) = True)) = ((((term51 _91307 _91308 t s f) = (term51 _91307 _91308 t s f)) = True) = (((term51 _91307 _91308 t s f) = (term51 _91307 _91308 t s f)) = True)).
Proof. exact (MK_COMB (@lem3562713 _91307 _91308 t s f) (@lem3562714 _91307 _91308 t s f)). Qed.
Lemma lem3562716 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) : ((term54 _91307 _91308 t s f) = (term54 _91307 _91308 t s f)) = ((((term51 _91307 _91308 t s f) = (term51 _91307 _91308 t s f)) = True) = (((term51 _91307 _91308 t s f) = (term51 _91307 _91308 t s f)) = True)).
Proof. exact (TRANS (@lem3562710 _91307 _91308 t s f) (@lem3562715 _91307 _91308 t s f)). Qed.
Lemma lem3562717 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) : (((term51 _91307 _91308 t s f) = (term51 _91307 _91308 t s f)) = True) = (((term51 _91307 _91308 t s f) = (term51 _91307 _91308 t s f)) = True).
Proof. exact (EQ_MP (@lem3562716 _91307 _91308 t s f) (@lem3562707 _91307 _91308 t s f)). Qed.
Lemma lem3562718 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) : ((term51 _91307 _91308 t s f) = (term51 _91307 _91308 t s f)) = True.
Proof. exact (EQ_MP (@lem3562717 _91307 _91308 t s f) (@lem3562704 _91307 _91308 t s f)). Qed.
Lemma lem3562719 {_91307 _91308 : Type'} (t : _91308 -> Prop) (s : _91307 -> Prop) (f : _91307 -> _91308) : ((term27 _91307 _91308 t s f) = (term51 _91307 _91308 t s f)) = True.
Proof. exact (TRANS (@lem3562700 _91307 _91308 t s f) (@lem3562718 _91307 _91308 t s f)). Qed.
Lemma lem3562720 {_91307 _91308 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91308) : (term57 _91307 _91308 s f) = (term58 _91308).
Proof. exact (fun_ext (fun t : _91308 -> Prop => @lem3562719 _91307 _91308 t s f)). Qed.
Lemma lem3562721 {_91308 : Type'} : (@all (_91308 -> Prop)) = (@all (_91308 -> Prop)).
Proof. exact (eq_refl (@all (_91308 -> Prop))). Qed.
Lemma lem3562722 {_91307 _91308 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91308) : (term59 _91307 _91308 s f) = (term60 _91308).
Proof. exact (MK_COMB (@lem3562721 _91308) (@lem3562720 _91307 _91308 s f)). Qed.
Lemma lem3562724 {A : Type'} (t : Prop) : (term61 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3562725 {_91308 : Type'} (t : Prop) : (term62 _91308 t) = t.
Proof. exact (@lem3562724 (_91308 -> Prop) t). Qed.
Lemma lem3562726 {_91308 : Type'} : (term60 _91308) = True.
Proof. exact (@lem3562725 _91308 True). Qed.
Lemma lem3562727 {_91307 _91308 : Type'} (s : _91307 -> Prop) (f : _91307 -> _91308) : (term59 _91307 _91308 s f) = True.
Proof. exact (TRANS (@lem3562722 _91307 _91308 s f) (@lem3562726 _91308)). Qed.
Lemma lem3562728 {_91307 _91308 : Type'} (s : _91307 -> Prop) : (term63 _91307 _91308 s) = (term64 _91307 _91308).
Proof. exact (fun_ext (fun f : _91307 -> _91308 => @lem3562727 _91307 _91308 s f)). Qed.
Lemma lem3562729 {_91307 _91308 : Type'} : (@all (_91307 -> _91308)) = (@all (_91307 -> _91308)).
Proof. exact (eq_refl (@all (_91307 -> _91308))). Qed.
Lemma lem3562730 {_91307 _91308 : Type'} (s : _91307 -> Prop) : (term65 _91307 _91308 s) = (term66 _91307 _91308).
Proof. exact (MK_COMB (@lem3562729 _91307 _91308) (@lem3562728 _91307 _91308 s)). Qed.
Lemma lem3562732 {A : Type'} (t : Prop) : (term61 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3562733 {_91307 _91308 : Type'} (t : Prop) : (term67 _91307 _91308 t) = t.
Proof. exact (@lem3562732 (_91307 -> _91308) t). Qed.
Lemma lem3562734 {_91307 _91308 : Type'} : (term66 _91307 _91308) = True.
Proof. exact (@lem3562733 _91307 _91308 True). Qed.
Lemma lem3562735 {_91307 _91308 : Type'} (s : _91307 -> Prop) : (term65 _91307 _91308 s) = True.
Proof. exact (TRANS (@lem3562730 _91307 _91308 s) (@lem3562734 _91307 _91308)). Qed.
Lemma lem3562736 {_91307 _91308 : Type'} (s : _91307 -> Prop) : True = (term65 _91307 _91308 s).
Proof. exact (SYM (@lem3562735 _91307 _91308 s)). Qed.
Lemma lem3562737 {_91307 _91308 : Type'} (s : _91307 -> Prop) : term65 _91307 _91308 s.
Proof. exact (EQ_MP (@lem3562736 _91307 _91308 s) (@lem0)). Qed.
