Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import UNIQUE_SKOLEM_ALT_term_abbrevs.
Require Import EXISTS_UNIQUE_ALT_spec.
Require Import SKOLEM_THM_spec.
Require Import thm0_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem13691 {A B : Type'} (P : type1413 A B) : term0 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem13692 {A B : Type'} (P : type1413 A B) : (term0 A B P) = ((term1 A B P) = (term2 A B P)).
Proof. exact (eq_refl (term0 A B P)). Qed.
Lemma lem13694 {A : Type'} (P : A -> Prop) : term3 A P.
Proof. exact (@lem8062 A P). Qed.
Lemma lem13695 {A : Type'} (P : A -> Prop) : (term3 A P) = ((term4 A P) = (term5 A P)).
Proof. exact (eq_refl (term3 A P)). Qed.
Lemma lem13704 {A : Type'} (P : A -> Prop) : (term4 A P) = (term5 A P).
Proof. exact (EQ_MP (@lem13695 A P) (@lem13694 A P)). Qed.
Lemma lem13705 {B : Type'} (P : B -> Prop) : (term4 B P) = (term5 B P).
Proof. exact (@lem13704 B P). Qed.
Lemma lem13706 {A B : Type'} (P : type1413 A B) (x : A) : (term6 A B P x) = (term7 A B P x).
Proof. exact (@lem13705 B (term8 A B P x)). Qed.
Lemma lem13707 {A B : Type'} (P : type1413 A B) (x : A) (y : B) : (term9 A B P x y) = (P x y).
Proof. exact (eq_refl (term9 A B P x y)). Qed.
Lemma lem13708 {A B : Type'} (P : type1413 A B) (x : A) : (term10 A B P x) = (term8 A B P x).
Proof. exact (fun_ext (fun y : B => @lem13707 A B P x y)). Qed.
Lemma lem13709 {B : Type'} : (@ex1 B) = (@ex1 B).
Proof. exact (eq_refl (@ex1 B)). Qed.
Lemma lem13710 {A B : Type'} (P : type1413 A B) (x : A) : (term6 A B P x) = (term11 A B P x).
Proof. exact (MK_COMB (@lem13709 B) (@lem13708 A B P x)). Qed.
Lemma lem13711 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem13712 {A B : Type'} (P : type1413 A B) (x : A) : (term12 A B P x) = (term13 A B P x).
Proof. exact (MK_COMB (@lem13711) (@lem13710 A B P x)). Qed.
Lemma lem13713 {A B : Type'} (P : type1413 A B) (x : A) (y' : B) : (term9 A B P x y') = (P x y').
Proof. exact (eq_refl (term9 A B P x y')). Qed.
Lemma lem13714 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem13715 {A B : Type'} (P : type1413 A B) (x : A) (y' : B) : (term14 A B P x y') = (term15 A B P x y').
Proof. exact (MK_COMB (@lem13714) (@lem13713 A B P x y')). Qed.
Lemma lem13716 {B : Type'} (y : B) (y' : B) : (y = y') = (y = y').
Proof. exact (eq_refl (y = y')). Qed.
Lemma lem13717 {A B : Type'} (P : type1413 A B) (x : A) (y : B) (y' : B) : ((term9 A B P x y') = (y = y')) = ((P x y') = (y = y')).
Proof. exact (MK_COMB (@lem13715 A B P x y') (@lem13716 B y y')). Qed.
Lemma lem13718 {A B : Type'} (P : type1413 A B) (x : A) (y : B) : (term16 A B P x y) = (term17 A B P x y).
Proof. exact (fun_ext (fun y' : B => @lem13717 A B P x y y')). Qed.
Lemma lem13719 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem13720 {A B : Type'} (P : type1413 A B) (x : A) (y : B) : (term18 A B P x y) = (term19 A B P x y).
Proof. exact (MK_COMB (@lem13719 B) (@lem13718 A B P x y)). Qed.
Lemma lem13721 {A B : Type'} (P : type1413 A B) (x : A) : (term20 A B P x) = (term21 A B P x).
Proof. exact (fun_ext (fun y : B => @lem13720 A B P x y)). Qed.
Lemma lem13722 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem13723 {A B : Type'} (P : type1413 A B) (x : A) : (term7 A B P x) = (term22 A B P x).
Proof. exact (MK_COMB (@lem13722 B) (@lem13721 A B P x)). Qed.
Lemma lem13724 {A B : Type'} (P : type1413 A B) (x : A) : ((term6 A B P x) = (term7 A B P x)) = ((term11 A B P x) = (term22 A B P x)).
Proof. exact (MK_COMB (@lem13712 A B P x) (@lem13723 A B P x)). Qed.
Lemma lem13725 {A B : Type'} (P : type1413 A B) (x : A) : (term11 A B P x) = (term22 A B P x).
Proof. exact (EQ_MP (@lem13724 A B P x) (@lem13706 A B P x)). Qed.
Lemma lem13738 {A B : Type'} (P : type1413 A B) : (term23 A B P) = (term24 A B P).
Proof. exact (fun_ext (fun x : A => @lem13725 A B P x)). Qed.
Lemma lem13739 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem13740 {A B : Type'} (P : type1413 A B) : (term25 A B P) = (term26 A B P).
Proof. exact (MK_COMB (@lem13739 A) (@lem13738 A B P)). Qed.
Lemma lem13742 {A B : Type'} (P : type1413 A B) : (term1 A B P) = (term2 A B P).
Proof. exact (EQ_MP (@lem13692 A B P) (@lem13691 A B P)). Qed.
Lemma lem13743 {A B : Type'} (P : type1413 A B) : (term1 A B P) = (term2 A B P).
Proof. exact (@lem13742 A B P). Qed.
Lemma lem13744 {A B : Type'} (P : type1413 A B) : (term27 A B P) = (term28 A B P).
Proof. exact (@lem13743 A B (term29 A B P)). Qed.
Lemma lem13745 {A B : Type'} (P : type1413 A B) (x : A) : (term30 A B P x) = (term21 A B P x).
Proof. exact (eq_refl (term30 A B P x)). Qed.
Lemma lem13746 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem13747 {A B : Type'} (P : type1413 A B) (x : A) (y : B) : (term31 A B P x y) = (term32 A B P x y).
Proof. exact (MK_COMB (@lem13745 A B P x) (@lem13746 B y)). Qed.
Lemma lem13748 {A B : Type'} (P : type1413 A B) (x : A) (y : B) : (term32 A B P x y) = (term19 A B P x y).
Proof. exact (eq_refl (term32 A B P x y)). Qed.
Lemma lem13749 {A B : Type'} (P : type1413 A B) (x : A) (y : B) : (term31 A B P x y) = (term19 A B P x y).
Proof. exact (TRANS (@lem13747 A B P x y) (@lem13748 A B P x y)). Qed.
Lemma lem13750 {A B : Type'} (P : type1413 A B) (x : A) : (term33 A B P x) = (term21 A B P x).
Proof. exact (fun_ext (fun y : B => @lem13749 A B P x y)). Qed.
Lemma lem13751 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem13752 {A B : Type'} (P : type1413 A B) (x : A) : (term34 A B P x) = (term22 A B P x).
Proof. exact (MK_COMB (@lem13751 B) (@lem13750 A B P x)). Qed.
Lemma lem13753 {A B : Type'} (P : type1413 A B) : (term35 A B P) = (term24 A B P).
Proof. exact (fun_ext (fun x : A => @lem13752 A B P x)). Qed.
Lemma lem13754 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem13755 {A B : Type'} (P : type1413 A B) : (term27 A B P) = (term26 A B P).
Proof. exact (MK_COMB (@lem13754 A) (@lem13753 A B P)). Qed.
Lemma lem13756 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem13757 {A B : Type'} (P : type1413 A B) : (term36 A B P) = (term37 A B P).
Proof. exact (MK_COMB (@lem13756) (@lem13755 A B P)). Qed.
Lemma lem13758 {A B : Type'} (P : type1413 A B) (x : A) : (term30 A B P x) = (term21 A B P x).
Proof. exact (eq_refl (term30 A B P x)). Qed.
Lemma lem13759 {A B : Type'} (y : A -> B) (x : A) : (y x) = (y x).
Proof. exact (eq_refl (y x)). Qed.
Lemma lem13760 {A B : Type'} (P : type1413 A B) (y : A -> B) (x : A) : (term38 A B P y x) = (term39 A B P y x).
Proof. exact (MK_COMB (@lem13758 A B P x) (@lem13759 A B y x)). Qed.
Lemma lem13761 {A B : Type'} (P : type1413 A B) (y : A -> B) (x : A) : (term39 A B P y x) = (term40 A B P y x).
Proof. exact (eq_refl (term39 A B P y x)). Qed.
Lemma lem13762 {A B : Type'} (P : type1413 A B) (y : A -> B) (x : A) : (term38 A B P y x) = (term40 A B P y x).
Proof. exact (TRANS (@lem13760 A B P y x) (@lem13761 A B P y x)). Qed.
Lemma lem13763 {A B : Type'} (P : type1413 A B) (y : A -> B) : (term41 A B P y) = (term42 A B P y).
Proof. exact (fun_ext (fun x : A => @lem13762 A B P y x)). Qed.
Lemma lem13764 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem13765 {A B : Type'} (P : type1413 A B) (y : A -> B) : (term43 A B P y) = (term44 A B P y).
Proof. exact (MK_COMB (@lem13764 A) (@lem13763 A B P y)). Qed.
Lemma lem13766 {A B : Type'} (P : type1413 A B) : (term45 A B P) = (term46 A B P).
Proof. exact (fun_ext (fun y : A -> B => @lem13765 A B P y)). Qed.
Lemma lem13767 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem13768 {A B : Type'} (P : type1413 A B) : (term28 A B P) = (term47 A B P).
Proof. exact (MK_COMB (@lem13767 A B) (@lem13766 A B P)). Qed.
Lemma lem13769 {A B : Type'} (P : type1413 A B) : ((term27 A B P) = (term28 A B P)) = ((term26 A B P) = (term47 A B P)).
Proof. exact (MK_COMB (@lem13757 A B P) (@lem13768 A B P)). Qed.
Lemma lem13770 {A B : Type'} (P : type1413 A B) : (term26 A B P) = (term47 A B P).
Proof. exact (EQ_MP (@lem13769 A B P) (@lem13744 A B P)). Qed.
Lemma lem13787 {A B : Type'} (P : type1413 A B) : (term25 A B P) = (term47 A B P).
Proof. exact (TRANS (@lem13740 A B P) (@lem13770 A B P)). Qed.
Lemma lem13788 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem13789 {A B : Type'} (P : type1413 A B) : (term48 A B P) = (term49 A B P).
Proof. exact (MK_COMB (@lem13788) (@lem13787 A B P)). Qed.
Lemma lem13806 {A B : Type'} (P : type1413 A B) : (term47 A B P) = (term47 A B P).
Proof. exact (eq_refl (term47 A B P)). Qed.
Lemma lem13807 {A B : Type'} (P : type1413 A B) : ((term25 A B P) = (term47 A B P)) = ((term47 A B P) = (term47 A B P)).
Proof. exact (MK_COMB (@lem13789 A B P) (@lem13806 A B P)). Qed.
Lemma lem13809 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem13810 (x : Prop) : (x = x) = True.
Proof. exact (@lem13809 Prop x). Qed.
Lemma lem13811 {A B : Type'} (P : type1413 A B) : ((term47 A B P) = (term47 A B P)) = True.
Proof. exact (@lem13810 (term47 A B P)). Qed.
Lemma lem13814 {A B : Type'} (P : type1413 A B) : (term50 A B P) = (term50 A B P).
Proof. exact (eq_refl (term50 A B P)). Qed.
Lemma lem13815 {A B : Type'} (P : type1413 A B) : (term50 A B P) = (((term47 A B P) = (term47 A B P)) = True).
Proof. exact (eq_refl (term50 A B P)). Qed.
Lemma lem13816 {A B : Type'} (P : type1413 A B) : (term51 A B P) = (term51 A B P).
Proof. exact (eq_refl (term51 A B P)). Qed.
Lemma lem13817 {A B : Type'} (P : type1413 A B) : ((term50 A B P) = (term50 A B P)) = ((term50 A B P) = (((term47 A B P) = (term47 A B P)) = True)).
Proof. exact (MK_COMB (@lem13816 A B P) (@lem13815 A B P)). Qed.
Lemma lem13818 {A B : Type'} (P : type1413 A B) : (term50 A B P) = (((term47 A B P) = (term47 A B P)) = True).
Proof. exact (eq_refl (term50 A B P)). Qed.
Lemma lem13819 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem13820 {A B : Type'} (P : type1413 A B) : (term51 A B P) = (term52 A B P).
Proof. exact (MK_COMB (@lem13819) (@lem13818 A B P)). Qed.
Lemma lem13821 {A B : Type'} (P : type1413 A B) : (((term47 A B P) = (term47 A B P)) = True) = (((term47 A B P) = (term47 A B P)) = True).
Proof. exact (eq_refl (((term47 A B P) = (term47 A B P)) = True)). Qed.
Lemma lem13822 {A B : Type'} (P : type1413 A B) : ((term50 A B P) = (((term47 A B P) = (term47 A B P)) = True)) = ((((term47 A B P) = (term47 A B P)) = True) = (((term47 A B P) = (term47 A B P)) = True)).
Proof. exact (MK_COMB (@lem13820 A B P) (@lem13821 A B P)). Qed.
Lemma lem13823 {A B : Type'} (P : type1413 A B) : ((term50 A B P) = (term50 A B P)) = ((((term47 A B P) = (term47 A B P)) = True) = (((term47 A B P) = (term47 A B P)) = True)).
Proof. exact (TRANS (@lem13817 A B P) (@lem13822 A B P)). Qed.
Lemma lem13824 {A B : Type'} (P : type1413 A B) : (((term47 A B P) = (term47 A B P)) = True) = (((term47 A B P) = (term47 A B P)) = True).
Proof. exact (EQ_MP (@lem13823 A B P) (@lem13814 A B P)). Qed.
Lemma lem13825 {A B : Type'} (P : type1413 A B) : ((term47 A B P) = (term47 A B P)) = True.
Proof. exact (EQ_MP (@lem13824 A B P) (@lem13811 A B P)). Qed.
Lemma lem13826 {A B : Type'} (P : type1413 A B) : ((term25 A B P) = (term47 A B P)) = True.
Proof. exact (TRANS (@lem13807 A B P) (@lem13825 A B P)). Qed.
Lemma lem13827 {A B : Type'} (P : type1413 A B) : True = ((term25 A B P) = (term47 A B P)).
Proof. exact (SYM (@lem13826 A B P)). Qed.
Lemma lem13828 {A B : Type'} (P : type1413 A B) : (term25 A B P) = (term47 A B P).
Proof. exact (EQ_MP (@lem13827 A B P) (@lem0)). Qed.
Lemma lem13833 {A B : Type'} : term53 A B.
Proof. exact (fun P : type1413 A B => @lem13828 A B P). Qed.
