Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FST_term_abbrevs.
Require Import FST_DEF_spec.
Require Import PAIR_EQ_spec.
Require Import SELECT_UNIQUE_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm32_spec.
Lemma lem47630 {A B : Type'} (x : A) : term0 A B x.
Proof. exact (@lem47438 A B x). Qed.
Lemma lem47631 {A B : Type'} (x : A) : (term0 A B x) = (term1 A B x).
Proof. exact (eq_refl (term0 A B x)). Qed.
Lemma lem47632 {A B : Type'} (x : A) : term1 A B x.
Proof. exact (EQ_MP (@lem47631 A B x) (@lem47630 A B x)). Qed.
Lemma lem47633 {A B : Type'} (x : A) (y : B) : term2 A B x y.
Proof. exact (@lem47632 A B x y). Qed.
Lemma lem47634 {A B : Type'} (x : A) (y : B) : (term2 A B x y) = (term3 A B x y).
Proof. exact (eq_refl (term2 A B x y)). Qed.
Lemma lem47635 {A B : Type'} (x : A) (y : B) : term3 A B x y.
Proof. exact (EQ_MP (@lem47634 A B x y) (@lem47633 A B x y)). Qed.
Lemma lem47636 {A B : Type'} (x : A) (y : B) (a : A) : term4 A B x y a.
Proof. exact (@lem47635 A B x y a). Qed.
Lemma lem47637 {A B : Type'} (x : A) (a : A) (y : B) : (term4 A B x y a) = (term5 A B x a y).
Proof. exact (eq_refl (term4 A B x y a)). Qed.
Lemma lem47638 {A B : Type'} (x : A) (a : A) (y : B) : term5 A B x a y.
Proof. exact (EQ_MP (@lem47637 A B x a y) (@lem47636 A B x y a)). Qed.
Lemma lem47639 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : term6 A B x a y b.
Proof. exact (@lem47638 A B x a y b). Qed.
Lemma lem47640 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (term6 A B x a y b) = (((@pair A B x y) = (@pair A B a b)) = (term7 A B x a y b)).
Proof. exact (eq_refl (term6 A B x a y b)). Qed.
Lemma lem47642 {A : Type'} (h1 : term8 A) : term8 A.
Proof. exact (h1). Qed.
Lemma lem47643 {A : Type'} (P : A -> Prop) (h1 : term8 A) : term9 A P.
Proof. exact (@lem47642 A h1 P). Qed.
Lemma lem47644 {A : Type'} (P : A -> Prop) : (term9 A P) = (term10 A P).
Proof. exact (eq_refl (term9 A P)). Qed.
Lemma lem47645 {A : Type'} (P : A -> Prop) (h1 : term8 A) : term10 A P.
Proof. exact (EQ_MP (@lem47644 A P) (@lem47643 A P h1)). Qed.
Lemma lem47646 {A : Type'} (P : A -> Prop) (x : A) (h1 : term8 A) : term11 A P x.
Proof. exact (@lem47645 A P h1 x). Qed.
Lemma lem47647 {A : Type'} (P : A -> Prop) (x : A) : (term11 A P x) = (term12 A P x).
Proof. exact (eq_refl (term11 A P x)). Qed.
Lemma lem47648 {A : Type'} (P : A -> Prop) (x : A) (h1 : term8 A) : term12 A P x.
Proof. exact (EQ_MP (@lem47647 A P x) (@lem47646 A P x h1)). Qed.
Lemma lem47649 {A : Type'} (P : A -> Prop) (x : A) (h1 : term13 A P x) : term13 A P x.
Proof. exact (h1). Qed.
Lemma lem47650 {A : Type'} (P : A -> Prop) (x : A) (h1 : term13 A P x) (h2 : term8 A) : (@ε A P) = x.
Proof. exact (@lem47648 A P x h2 (@lem47649 A P x h1)). Qed.
Lemma lem47651 {A : Type'} (P : A -> Prop) (x : A) (h1 : term13 A P x) : term14 A P x.
Proof. exact (fun h0 : term8 A => @lem47650 A P x h1 h0). Qed.
Lemma lem47652 {A : Type'} (h1 : term8 A) : term8 A.
Proof. exact (h1). Qed.
Lemma lem47653 {A : Type'} (P : A -> Prop) (x : A) (h1 : term13 A P x) (h2 : term8 A) : (@ε A P) = x.
Proof. exact (@lem47651 A P x h1 (@lem47652 A h2)). Qed.
Lemma lem47654 {A : Type'} (P : A -> Prop) (x : A) (h1 : term8 A) : term12 A P x.
Proof. exact (fun h0 : term13 A P x => @lem47653 A P x h0 h1). Qed.
Lemma lem47655 {A : Type'} (P : A -> Prop) (h1 : term8 A) : term10 A P.
Proof. exact (fun x : A => @lem47654 A P x h1). Qed.
Lemma lem47656 {A : Type'} (h1 : term8 A) : term8 A.
Proof. exact (fun P : A -> Prop => @lem47655 A P h1). Qed.
Lemma lem47657 {A : Type'} : term15 A.
Proof. exact (fun h0 : term8 A => @lem47656 A h0). Qed.
Lemma lem47658 {A : Type'} : term8 A.
Proof. exact (@lem47657 A (@lem9522 A)). Qed.
Lemma lem47659 {A : Type'} (P : A -> Prop) : term9 A P.
Proof. exact (@lem47658 A P). Qed.
Lemma lem47660 {A : Type'} (P : A -> Prop) : (term9 A P) = (term10 A P).
Proof. exact (eq_refl (term9 A P)). Qed.
Lemma lem47661 {A : Type'} (P : A -> Prop) : term10 A P.
Proof. exact (EQ_MP (@lem47660 A P) (@lem47659 A P)). Qed.
Lemma lem47662 {A : Type'} (P : A -> Prop) (x : A) : term11 A P x.
Proof. exact (@lem47661 A P x). Qed.
Lemma lem47663 {A : Type'} (P : A -> Prop) (x : A) : (term11 A P x) = (term12 A P x).
Proof. exact (eq_refl (term11 A P x)). Qed.
Lemma lem47665 {A B : Type'} (p : prod A B) : term16 A B p.
Proof. exact (@lem45472 A B p). Qed.
Lemma lem47666 {A B : Type'} (p : prod A B) : (term16 A B p) = ((@fst A B p) = (term17 A B p)).
Proof. exact (eq_refl (term16 A B p)). Qed.
Lemma lem47671 {A B : Type'} (p : prod A B) : (@fst A B p) = (term17 A B p).
Proof. exact (EQ_MP (@lem47666 A B p) (@lem47665 A B p)). Qed.
Lemma lem47672 {A B : Type'} (p : prod A B) : (@fst A B p) = (term17 A B p).
Proof. exact (@lem47671 A B p). Qed.
Lemma lem47673 {A B : Type'} (x : A) (y : B) : (term18 A B x y) = (term19 A B x y).
Proof. exact (@lem47672 A B (@pair A B x y)). Qed.
Lemma lem47680 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem47681 {A B : Type'} (x : A) (y : B) : (term20 A B x y) = (term21 A B x y).
Proof. exact (MK_COMB (@lem47680 A) (@lem47673 A B x y)). Qed.
Lemma lem47682 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem47683 {A B : Type'} (y : B) (x : A) : ((term18 A B x y) = x) = ((term19 A B x y) = x).
Proof. exact (MK_COMB (@lem47681 A B x y) (@lem47682 A x)). Qed.
Lemma lem47686 {A B : Type'} (y : B) (x : A) : ((term19 A B x y) = x) = ((term18 A B x y) = x).
Proof. exact (SYM (@lem47683 A B y x)). Qed.
Lemma lem47688 {A : Type'} (P : A -> Prop) (x : A) : term12 A P x.
Proof. exact (EQ_MP (@lem47663 A P x) (@lem47662 A P x)). Qed.
Lemma lem47689 {A : Type'} (P : A -> Prop) (x : A) : term12 A P x.
Proof. exact (@lem47688 A P x). Qed.
Lemma lem47690 {A B : Type'} (y : B) (x : A) : term22 A B y x.
Proof. exact (@lem47689 A (term23 A B x y) x). Qed.
Lemma lem47691 {A B : Type'} (x : A) (y : B) (y' : A) : (term24 A B x y y') = (term25 A B x y y').
Proof. exact (eq_refl (term24 A B x y y')). Qed.
Lemma lem47692 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem47693 {A B : Type'} (x : A) (y : B) (y' : A) : (term26 A B x y y') = (term27 A B x y y').
Proof. exact (MK_COMB (@lem47692) (@lem47691 A B x y y')). Qed.
Lemma lem47694 {A : Type'} (y' : A) (x : A) : (y' = x) = (y' = x).
Proof. exact (eq_refl (y' = x)). Qed.
Lemma lem47695 {A B : Type'} (y : B) (y' : A) (x : A) : ((term24 A B x y y') = (y' = x)) = ((term25 A B x y y') = (y' = x)).
Proof. exact (MK_COMB (@lem47693 A B x y y') (@lem47694 A y' x)). Qed.
Lemma lem47696 {A B : Type'} (y : B) (y' : A) (x : A) : ((term25 A B x y y') = (y' = x)) = ((term24 A B x y y') = (y' = x)).
Proof. exact (SYM (@lem47695 A B y y' x)). Qed.
Lemma lem47704 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : ((@pair A B x y) = (@pair A B a b)) = (term7 A B x a y b).
Proof. exact (EQ_MP (@lem47640 A B x a y b) (@lem47639 A B x a y b)). Qed.
Lemma lem47705 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : ((@pair A B x y) = (@pair A B a b)) = (term7 A B x a y b).
Proof. exact (@lem47704 A B x a y b). Qed.
Lemma lem47706 {A B : Type'} (x : A) (y' : A) (y : B) (y'' : B) : ((@pair A B x y) = (@pair A B y' y'')) = (term7 A B x y' y y'').
Proof. exact (@lem47705 A B x y' y y''). Qed.
Lemma lem47713 {A B : Type'} (x : A) (y' : A) (y : B) : (term28 A B x y y') = (term29 A B x y' y).
Proof. exact (fun_ext (fun y'' : B => @lem47706 A B x y' y y'')). Qed.
Lemma lem47714 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem47715 {A B : Type'} (x : A) (y' : A) (y : B) : (term25 A B x y y') = (term30 A B x y' y).
Proof. exact (MK_COMB (@lem47714 B) (@lem47713 A B x y' y)). Qed.
Lemma lem47720 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem47721 {A B : Type'} (x : A) (y' : A) (y : B) : (term27 A B x y y') = (term31 A B x y' y).
Proof. exact (MK_COMB (@lem47720) (@lem47715 A B x y' y)). Qed.
Lemma lem47724 {A : Type'} (y' : A) (x : A) : (y' = x) = (y' = x).
Proof. exact (eq_refl (y' = x)). Qed.
Lemma lem47725 {A B : Type'} (y : B) (y' : A) (x : A) : ((term25 A B x y y') = (y' = x)) = ((term30 A B x y' y) = (y' = x)).
Proof. exact (MK_COMB (@lem47721 A B x y' y) (@lem47724 A y' x)). Qed.
Lemma lem47728 {A B : Type'} (y : B) (y' : A) (x : A) : ((term30 A B x y' y) = (y' = x)) = ((term25 A B x y y') = (y' = x)).
Proof. exact (SYM (@lem47725 A B y y' x)). Qed.
Lemma lem47729 {A B : Type'} (x : A) (y' : A) (y : B) (h1 : term30 A B x y' y) : term30 A B x y' y.
Proof. exact (h1). Qed.
Lemma lem47730 {A B : Type'} (x : A) (y' : A) (y : B) (y'' : B) (h1 : term7 A B x y' y y'') : term7 A B x y' y y''.
Proof. exact (h1). Qed.
Lemma lem47732 {A : Type'} (x : A) (y' : A) (h1 : x = y') : x = y'.
Proof. exact (h1). Qed.
Lemma lem47733 {A : Type'} (y' : A) (x : A) (h1 : y' = x) : y' = x.
Proof. exact (h1). Qed.
Lemma lem47737 {A : Type'} (x : A) (y' : A) (h1 : x = y') : x = y'.
Proof. exact (h1). Qed.
Lemma lem47738 {A : Type'} (y' : A) : (@eq A y') = (@eq A y').
Proof. exact (eq_refl (@eq A y')). Qed.
Lemma lem47739 {A : Type'} (x : A) (y' : A) (h1 : x = y') : (y' = x) = (y' = y').
Proof. exact (MK_COMB (@lem47738 A y') (@lem47737 A x y' h1)). Qed.
Lemma lem47741 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem47742 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem47741 A x). Qed.
Lemma lem47743 {A : Type'} (y' : A) : (y' = y') = True.
Proof. exact (@lem47742 A y'). Qed.
Lemma lem47744 {A : Type'} (x : A) (y' : A) (h1 : x = y') : (y' = x) = True.
Proof. exact (TRANS (@lem47739 A x y' h1) (@lem47743 A y')). Qed.
Lemma lem47745 {A : Type'} (x : A) (y' : A) (h1 : x = y') : True = (y' = x).
Proof. exact (SYM (@lem47744 A x y' h1)). Qed.
Lemma lem47746 {A : Type'} (x : A) (y' : A) (h1 : x = y') : y' = x.
Proof. exact (EQ_MP (@lem47745 A x y' h1) (@lem0)). Qed.
Lemma lem47756 {A : Type'} (y' : A) (x : A) (h1 : y' = x) : y' = x.
Proof. exact (h1). Qed.
Lemma lem47757 {A : Type'} (x : A) : (@eq A x) = (@eq A x).
Proof. exact (eq_refl (@eq A x)). Qed.
Lemma lem47758 {A : Type'} (y' : A) (x : A) (h1 : y' = x) : (x = y') = (x = x).
Proof. exact (MK_COMB (@lem47757 A x) (@lem47756 A y' x h1)). Qed.
Lemma lem47760 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem47761 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem47760 A x). Qed.
Lemma lem47762 {A : Type'} (y' : A) (x : A) (h1 : y' = x) : (x = y') = True.
Proof. exact (TRANS (@lem47758 A y' x h1) (@lem47761 A x)). Qed.
Lemma lem47763 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem47764 {A : Type'} (y' : A) (x : A) (h1 : y' = x) : (term32 A x y') = (and True).
Proof. exact (MK_COMB (@lem47763) (@lem47762 A y' x h1)). Qed.
Lemma lem47769 {B : Type'} (y : B) (y' : B) : (y = y') = (y = y').
Proof. exact (eq_refl (y = y')). Qed.
Lemma lem47770 {A B : Type'} (y : B) (y' : B) (y'' : A) (x : A) (h1 : y'' = x) : (term7 A B x y'' y y') = (term33 B y y').
Proof. exact (MK_COMB (@lem47764 A y'' x h1) (@lem47769 B y y')). Qed.
Lemma lem47772 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem47773 {B : Type'} (y : B) (y' : B) : (term33 B y y') = (y = y').
Proof. exact (@lem47772 (y = y')). Qed.
Lemma lem47778 {A B : Type'} (y : B) (y' : B) (y'' : A) (x : A) (h1 : y'' = x) : (term7 A B x y'' y y') = (y = y').
Proof. exact (TRANS (@lem47770 A B y y' y'' x h1) (@lem47773 B y y')). Qed.
Lemma lem47779 {A B : Type'} (y : B) (y' : A) (x : A) (h1 : y' = x) : (term29 A B x y' y) = (term34 B y).
Proof. exact (fun_ext (fun y'' : B => @lem47778 A B y y'' y' x h1)). Qed.
Lemma lem47780 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem47781 {A B : Type'} (y : B) (y' : A) (x : A) (h1 : y' = x) : (term30 A B x y' y) = (term35 B y).
Proof. exact (MK_COMB (@lem47780 B) (@lem47779 A B y y' x h1)). Qed.
Lemma lem47786 {A B : Type'} (y : B) (y' : A) (x : A) (h1 : y' = x) : (term35 B y) = (term30 A B x y' y).
Proof. exact (SYM (@lem47781 A B y y' x h1)). Qed.
Lemma lem47788 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem47789 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem47788 B x). Qed.
Lemma lem47790 {B : Type'} (y : B) : (y = y) = True.
Proof. exact (@lem47789 B y). Qed.
Lemma lem47791 {B : Type'} (y : B) : True = (y = y).
Proof. exact (SYM (@lem47790 B y)). Qed.
Lemma lem47792 {B : Type'} (y : B) : y = y.
Proof. exact (EQ_MP (@lem47791 B y) (@lem0)). Qed.
Lemma lem47793 {B : Type'} (y : B) : term35 B y.
Proof. exact (ex_intro (term34 B y) y (@lem47792 B y)). Qed.
Lemma lem47794 {A B : Type'} (y : B) (y' : A) (x : A) (h1 : y' = x) : term30 A B x y' y.
Proof. exact (EQ_MP (@lem47786 A B y y' x h1) (@lem47793 B y)). Qed.
Lemma lem47795 {A B : Type'} (y : B) (y' : A) (x : A) (h1 : y' = x) : (y' = x) = (term30 A B x y' y).
Proof. exact (prop_ext (fun h2 : y' = x => @lem47794 A B y y' x h1) (fun h2 : term30 A B x y' y => @lem47733 A y' x h1)). Qed.
Lemma lem47796 {A B : Type'} (y : B) (y' : A) (x : A) (h1 : y' = x) : term30 A B x y' y.
Proof. exact (EQ_MP (@lem47795 A B y y' x h1) (@lem47733 A y' x h1)). Qed.
Lemma lem47797 {A B : Type'} (x : A) (y' : A) (y : B) : term36 A B x y' y.
Proof. exact (fun h0 : y' = x => @lem47796 A B y y' x h0). Qed.
Lemma lem47799 {A B : Type'} (x : A) (y' : A) (y : B) (y'' : B) (h1 : term7 A B x y' y y'') : x = y'.
Proof. exact (proj1 (@lem47730 A B x y' y y'' h1)). Qed.
Lemma lem47800 {A : Type'} (x : A) (y' : A) (h1 : x = y') : (x = y') = (y' = x).
Proof. exact (prop_ext (fun h2 : x = y' => @lem47746 A x y' h1) (fun h2 : y' = x => @lem47732 A x y' h1)). Qed.
Lemma lem47801 {A : Type'} (x : A) (y' : A) (h1 : x = y') : y' = x.
Proof. exact (EQ_MP (@lem47800 A x y' h1) (@lem47732 A x y' h1)). Qed.
Lemma lem47802 {A B : Type'} (x : A) (y' : A) (y : B) (y'' : B) (h1 : term7 A B x y' y y'') : (x = y') = (y' = x).
Proof. exact (prop_ext (fun h2 : x = y' => @lem47801 A x y' h2) (fun h2 : y' = x => @lem47799 A B x y' y y'' h1)). Qed.
Lemma lem47803 {A B : Type'} (x : A) (y' : A) (y : B) (y'' : B) (h1 : term7 A B x y' y y'') : y' = x.
Proof. exact (EQ_MP (@lem47802 A B x y' y y'' h1) (@lem47799 A B x y' y y'' h1)). Qed.
Lemma lem47804 {A B : Type'} (x : A) (y' : A) (y : B) (h1 : term30 A B x y' y) : y' = x.
Proof. exact (ex_elim (@lem47729 A B x y' y h1) (fun y'' : B => fun h0 : term29 A B x y' y y'' => @lem47803 A B x y' y y'' h0)). Qed.
Lemma lem47805 {A B : Type'} (y : B) (y' : A) (x : A) : term37 A B y y' x.
Proof. exact (fun h0 : term30 A B x y' y => @lem47804 A B x y' y h0). Qed.
Lemma lem47806 {A B : Type'} (x : A) (y' : A) (y : B) : term38 A B x y' y.
Proof. exact (conj (@lem47805 A B y y' x) (@lem47797 A B x y' y)). Qed.
Lemma lem47807 {A B : Type'} (y : B) (y' : A) (x : A) : (term38 A B x y' y) = ((term30 A B x y' y) = (y' = x)).
Proof. exact (@lem32 (term30 A B x y' y) (y' = x)). Qed.
Lemma lem47808 {A B : Type'} (y : B) (y' : A) (x : A) : (term30 A B x y' y) = (y' = x).
Proof. exact (EQ_MP (@lem47807 A B y y' x) (@lem47806 A B x y' y)). Qed.
Lemma lem47809 {A B : Type'} (y : B) (y' : A) (x : A) : (term25 A B x y y') = (y' = x).
Proof. exact (EQ_MP (@lem47728 A B y y' x) (@lem47808 A B y y' x)). Qed.
Lemma lem47810 {A B : Type'} (y : B) (y' : A) (x : A) : (term24 A B x y y') = (y' = x).
Proof. exact (EQ_MP (@lem47696 A B y y' x) (@lem47809 A B y y' x)). Qed.
Lemma lem47815 {A B : Type'} (y : B) (x : A) : term39 A B y x.
Proof. exact (fun y' : A => @lem47810 A B y y' x). Qed.
Lemma lem47816 {A B : Type'} (y : B) (x : A) : (term19 A B x y) = x.
Proof. exact (@lem47690 A B y x (@lem47815 A B y x)). Qed.
Lemma lem47817 {A B : Type'} (y : B) (x : A) : (term18 A B x y) = x.
Proof. exact (EQ_MP (@lem47686 A B y x) (@lem47816 A B y x)). Qed.
Lemma lem47822 {A B : Type'} (x : A) : term40 A B x.
Proof. exact (fun y : B => @lem47817 A B y x). Qed.
Lemma lem47827 {A B : Type'} : term41 A B.
Proof. exact (fun x : A => @lem47822 A B x). Qed.
