Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INJECTIVE_ON_IMAGE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import IMAGE_CLAUSES_spec.
Require Import SING_SUBSET_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm1820_spec.
Require Import thm1834_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm32_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211656_spec.
Require Import thm3211657_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm7_spec.
Lemma lem5032608 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5032609 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem5032610 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem5032609 t1) (@lem5032608 t1)). Qed.
Lemma lem5032611 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem5032610 t1 t2). Qed.
Lemma lem5032612 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem5032613 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem5032612 t1 t2) (@lem5032611 t1 t2)). Qed.
Lemma lem5032614 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem5032613 t1 t2 t3). Qed.
Lemma lem5032615 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem5032616 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem5032615 t1 t2 t3) (@lem5032614 t1 t2 t3)). Qed.
Lemma lem5032617 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem5032616 t1 t2 t3)). Qed.
Lemma lem5032618 {A B : Type'} (u : A -> Prop) (f : A -> B) (h1 : term7 A B u f) : term7 A B u f.
Proof. exact (h1). Qed.
Lemma lem5032656 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term8 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem5032657 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term8 A s t).
Proof. exact (@lem5032656 A s t). Qed.
Lemma lem5032658 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (@SUBSET A s u) = (term8 A s u).
Proof. exact (@lem5032657 A s u). Qed.
Lemma lem5032665 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5032666 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term9 A s u) = (term10 A s u).
Proof. exact (MK_COMB (@lem5032665) (@lem5032658 A s u)). Qed.
Lemma lem5032670 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term8 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem5032671 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term8 A s t).
Proof. exact (@lem5032670 A s t). Qed.
Lemma lem5032672 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (@SUBSET A t u) = (term8 A t u).
Proof. exact (@lem5032671 A t u). Qed.
Lemma lem5032679 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5032680 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term9 A t u) = (term10 A t u).
Proof. exact (MK_COMB (@lem5032679) (@lem5032672 A t u)). Qed.
Lemma lem5032684 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term11 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem5032685 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (s = t) = (term11 B s t).
Proof. exact (@lem5032684 B s t). Qed.
Lemma lem5032686 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : ((@IMAGE A B f s) = (@IMAGE A B f t)) = (term12 A B s f t).
Proof. exact (@lem5032685 B (@IMAGE A B f s) (@IMAGE A B f t)). Qed.
Lemma lem5032695 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term13 A B u s f t) = (term14 A B u s f t).
Proof. exact (MK_COMB (@lem5032680 A t u) (@lem5032686 A B s f t)). Qed.
Lemma lem5032698 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term15 A B u s f t) = (term16 A B u s f t).
Proof. exact (MK_COMB (@lem5032666 A s u) (@lem5032695 A B u s f t)). Qed.
Lemma lem5032701 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5032702 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term17 A B u s f t) = (term18 A B u s f t).
Proof. exact (MK_COMB (@lem5032701) (@lem5032698 A B u s f t)). Qed.
Lemma lem5032706 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term11 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem5032707 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term11 A s t).
Proof. exact (@lem5032706 A s t). Qed.
Lemma lem5032716 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term19 A B u f s t) = (term20 A B u f s t).
Proof. exact (MK_COMB (@lem5032702 A B u s f t) (@lem5032707 A s t)). Qed.
Lemma lem5032719 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) : (term21 A B u f s) = (term22 A B u f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem5032716 A B u f s t)). Qed.
Lemma lem5032720 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5032721 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) : (term23 A B u f s) = (term24 A B u f s).
Proof. exact (MK_COMB (@lem5032720 A) (@lem5032719 A B u f s)). Qed.
Lemma lem5032726 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term25 A B u f) = (term26 A B u f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5032721 A B u f s)). Qed.
Lemma lem5032727 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5032728 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term7 A B u f) = (term27 A B u f).
Proof. exact (MK_COMB (@lem5032727 A) (@lem5032726 A B u f)). Qed.
Lemma lem5032733 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term28 A B u f) = (term28 A B u f).
Proof. exact (eq_refl (term28 A B u f)). Qed.
Lemma lem5032734 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term29 A B u f) = (term30 A B u f).
Proof. exact (MK_COMB (@lem5032733 A B u f) (@lem5032728 A B u f)). Qed.
Lemma lem5032737 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term30 A B u f) = (term29 A B u f).
Proof. exact (SYM (@lem5032734 A B u f)). Qed.
Lemma lem5032753 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5032754 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5032753 A P x). Qed.
Lemma lem5032755 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem5032754 A u x). Qed.
Lemma lem5032756 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5032757 {A : Type'} (u : A -> Prop) (x : A) : (term31 A x u) = (term32 A u x).
Proof. exact (MK_COMB (@lem5032756) (@lem5032755 A u x)). Qed.
Lemma lem5032761 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5032762 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5032761 A P x). Qed.
Lemma lem5032763 {A : Type'} (u : A -> Prop) (y : A) : (@IN A y u) = (u y).
Proof. exact (@lem5032762 A u y). Qed.
Lemma lem5032764 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5032765 {A : Type'} (u : A -> Prop) (y : A) : (term31 A y u) = (term32 A u y).
Proof. exact (MK_COMB (@lem5032764) (@lem5032763 A u y)). Qed.
Lemma lem5032768 {A B : Type'} (x : A) (f : A -> B) (y : A) : ((f x) = (f y)) = ((f x) = (f y)).
Proof. exact (eq_refl ((f x) = (f y))). Qed.
Lemma lem5032769 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (y : A) : (term33 A B u x f y) = (term34 A B u x f y).
Proof. exact (MK_COMB (@lem5032765 A u y) (@lem5032768 A B x f y)). Qed.
Lemma lem5032772 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (y : A) : (term35 A B u x f y) = (term36 A B u x f y).
Proof. exact (MK_COMB (@lem5032757 A u x) (@lem5032769 A B u x f y)). Qed.
Lemma lem5032775 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5032776 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (y : A) : (term37 A B u x f y) = (term38 A B u x f y).
Proof. exact (MK_COMB (@lem5032775) (@lem5032772 A B u x f y)). Qed.
Lemma lem5032779 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem5032780 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (y : A) : (term39 A B u f x y) = (term40 A B u f x y).
Proof. exact (MK_COMB (@lem5032776 A B u x f y) (@lem5032779 A x y)). Qed.
Lemma lem5032783 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) : (term41 A B u f x) = (term42 A B u f x).
Proof. exact (fun_ext (fun y : A => @lem5032780 A B u f x y)). Qed.
Lemma lem5032784 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5032785 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) : (term43 A B u f x) = (term44 A B u f x).
Proof. exact (MK_COMB (@lem5032784 A) (@lem5032783 A B u f x)). Qed.
Lemma lem5032790 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term45 A B u f) = (term46 A B u f).
Proof. exact (fun_ext (fun x : A => @lem5032785 A B u f x)). Qed.
Lemma lem5032791 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5032792 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term47 A B u f) = (term48 A B u f).
Proof. exact (MK_COMB (@lem5032791 A) (@lem5032790 A B u f)). Qed.
Lemma lem5032797 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5032798 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term28 A B u f) = (term49 A B u f).
Proof. exact (MK_COMB (@lem5032797) (@lem5032792 A B u f)). Qed.
Lemma lem5032818 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5032819 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5032818 A P x). Qed.
Lemma lem5032820 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem5032819 A s x). Qed.
Lemma lem5032821 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5032822 {A : Type'} (s : A -> Prop) (x : A) : (term50 A x s) = (term51 A s x).
Proof. exact (MK_COMB (@lem5032821) (@lem5032820 A s x)). Qed.
Lemma lem5032824 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5032825 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5032824 A P x). Qed.
Lemma lem5032826 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem5032825 A u x). Qed.
Lemma lem5032827 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term52 A s x u) = (term53 A s u x).
Proof. exact (MK_COMB (@lem5032822 A s x) (@lem5032826 A u x)). Qed.
Lemma lem5032830 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term54 A s u) = (term55 A s u).
Proof. exact (fun_ext (fun x : A => @lem5032827 A s u x)). Qed.
Lemma lem5032831 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5032832 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term8 A s u) = (term56 A s u).
Proof. exact (MK_COMB (@lem5032831 A) (@lem5032830 A s u)). Qed.
Lemma lem5032837 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5032838 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term10 A s u) = (term57 A s u).
Proof. exact (MK_COMB (@lem5032837) (@lem5032832 A s u)). Qed.
Lemma lem5032848 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5032849 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5032848 A P x). Qed.
Lemma lem5032850 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem5032849 A t x). Qed.
Lemma lem5032851 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5032852 {A : Type'} (t : A -> Prop) (x : A) : (term50 A x t) = (term51 A t x).
Proof. exact (MK_COMB (@lem5032851) (@lem5032850 A t x)). Qed.
Lemma lem5032854 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5032855 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5032854 A P x). Qed.
Lemma lem5032856 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem5032855 A u x). Qed.
Lemma lem5032857 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term52 A t x u) = (term53 A t u x).
Proof. exact (MK_COMB (@lem5032852 A t x) (@lem5032856 A u x)). Qed.
Lemma lem5032860 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term54 A t u) = (term55 A t u).
Proof. exact (fun_ext (fun x : A => @lem5032857 A t u x)). Qed.
Lemma lem5032861 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5032862 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term8 A t u) = (term56 A t u).
Proof. exact (MK_COMB (@lem5032861 A) (@lem5032860 A t u)). Qed.
Lemma lem5032867 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5032868 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term10 A t u) = (term57 A t u).
Proof. exact (MK_COMB (@lem5032867) (@lem5032862 A t u)). Qed.
Lemma lem5032876 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term58 A B y f s) = (term59 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem5032877 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term58 A B y f s) = (term59 A B y f s).
Proof. exact (@lem5032876 A B y f s). Qed.
Lemma lem5032878 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term58 A B x f s) = (term59 A B x f s).
Proof. exact (@lem5032877 A B x f s). Qed.
Lemma lem5032888 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5032889 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5032888 A P x). Qed.
Lemma lem5032890 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem5032889 A s x). Qed.
Lemma lem5032891 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term60 A B x f x') = (term60 A B x f x').
Proof. exact (eq_refl (term60 A B x f x')). Qed.
Lemma lem5032892 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term61 A B x f x' s) = (term62 A B x f s x').
Proof. exact (MK_COMB (@lem5032891 A B x f x') (@lem5032890 A s x')). Qed.
Lemma lem5032895 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term63 A B x f s) = (term64 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem5032892 A B x f s x')). Qed.
Lemma lem5032896 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5032897 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term59 A B x f s) = (term65 A B x f s).
Proof. exact (MK_COMB (@lem5032896 A) (@lem5032895 A B x f s)). Qed.
Lemma lem5032902 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term58 A B x f s) = (term65 A B x f s).
Proof. exact (TRANS (@lem5032878 A B x f s) (@lem5032897 A B x f s)). Qed.
Lemma lem5032903 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5032904 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term66 A B x f s) = (term67 A B x f s).
Proof. exact (MK_COMB (@lem5032903) (@lem5032902 A B x f s)). Qed.
Lemma lem5032906 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term58 A B y f s) = (term59 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem5032907 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term58 A B y f s) = (term59 A B y f s).
Proof. exact (@lem5032906 A B y f s). Qed.
Lemma lem5032908 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term58 A B x f t) = (term59 A B x f t).
Proof. exact (@lem5032907 A B x f t). Qed.
Lemma lem5032918 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5032919 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5032918 A P x). Qed.
Lemma lem5032920 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem5032919 A t x). Qed.
Lemma lem5032921 {A B : Type'} (x : B) (f : A -> B) (x' : A) : (term60 A B x f x') = (term60 A B x f x').
Proof. exact (eq_refl (term60 A B x f x')). Qed.
Lemma lem5032922 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term61 A B x f x' t) = (term62 A B x f t x').
Proof. exact (MK_COMB (@lem5032921 A B x f x') (@lem5032920 A t x')). Qed.
Lemma lem5032925 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term63 A B x f t) = (term64 A B x f t).
Proof. exact (fun_ext (fun x' : A => @lem5032922 A B x f t x')). Qed.
Lemma lem5032926 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5032927 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term59 A B x f t) = (term65 A B x f t).
Proof. exact (MK_COMB (@lem5032926 A) (@lem5032925 A B x f t)). Qed.
Lemma lem5032932 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term58 A B x f t) = (term65 A B x f t).
Proof. exact (TRANS (@lem5032908 A B x f t) (@lem5032927 A B x f t)). Qed.
Lemma lem5032933 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : ((term58 A B x f s) = (term58 A B x f t)) = ((term65 A B x f s) = (term65 A B x f t)).
Proof. exact (MK_COMB (@lem5032904 A B x f s) (@lem5032932 A B x f t)). Qed.
Lemma lem5032936 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term68 A B s f t) = (term69 A B s f t).
Proof. exact (fun_ext (fun x : B => @lem5032933 A B s x f t)). Qed.
Lemma lem5032937 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5032938 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term12 A B s f t) = (term70 A B s f t).
Proof. exact (MK_COMB (@lem5032937 B) (@lem5032936 A B s f t)). Qed.
Lemma lem5032943 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term14 A B u s f t) = (term71 A B u s f t).
Proof. exact (MK_COMB (@lem5032868 A t u) (@lem5032938 A B s f t)). Qed.
Lemma lem5032946 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term16 A B u s f t) = (term72 A B u s f t).
Proof. exact (MK_COMB (@lem5032838 A s u) (@lem5032943 A B u s f t)). Qed.
Lemma lem5032949 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5032950 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term18 A B u s f t) = (term73 A B u s f t).
Proof. exact (MK_COMB (@lem5032949) (@lem5032946 A B u s f t)). Qed.
Lemma lem5032958 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5032959 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5032958 A P x). Qed.
Lemma lem5032960 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem5032959 A s x). Qed.
Lemma lem5032961 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5032962 {A : Type'} (s : A -> Prop) (x : A) : (term74 A x s) = (term75 A s x).
Proof. exact (MK_COMB (@lem5032961) (@lem5032960 A s x)). Qed.
Lemma lem5032964 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5032965 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5032964 A P x). Qed.
Lemma lem5032966 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem5032965 A t x). Qed.
Lemma lem5032967 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((@IN A x s) = (@IN A x t)) = ((s x) = (t x)).
Proof. exact (MK_COMB (@lem5032962 A s x) (@lem5032966 A t x)). Qed.
Lemma lem5032970 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term76 A s t) = (term77 A s t).
Proof. exact (fun_ext (fun x : A => @lem5032967 A s t x)). Qed.
Lemma lem5032971 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5032972 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term11 A s t) = (term78 A s t).
Proof. exact (MK_COMB (@lem5032971 A) (@lem5032970 A s t)). Qed.
Lemma lem5032977 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term20 A B u f s t) = (term79 A B u f s t).
Proof. exact (MK_COMB (@lem5032950 A B u s f t) (@lem5032972 A s t)). Qed.
Lemma lem5032980 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) : (term22 A B u f s) = (term80 A B u f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem5032977 A B u f s t)). Qed.
Lemma lem5032981 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5032982 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) : (term24 A B u f s) = (term81 A B u f s).
Proof. exact (MK_COMB (@lem5032981 A) (@lem5032980 A B u f s)). Qed.
Lemma lem5032987 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term26 A B u f) = (term82 A B u f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5032982 A B u f s)). Qed.
Lemma lem5032988 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5032989 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term27 A B u f) = (term83 A B u f).
Proof. exact (MK_COMB (@lem5032988 A) (@lem5032987 A B u f)). Qed.
Lemma lem5032994 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term30 A B u f) = (term84 A B u f).
Proof. exact (MK_COMB (@lem5032798 A B u f) (@lem5032989 A B u f)). Qed.
Lemma lem5032997 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term84 A B u f) = (term30 A B u f).
Proof. exact (SYM (@lem5032994 A B u f)). Qed.
Lemma lem5032999 (p : Prop) : p = (term85 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5033000 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term84 A B u f) = (term86 A B u f).
Proof. exact (@lem5032999 (term84 A B u f)). Qed.
Lemma lem5033001 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term86 A B u f) = (term84 A B u f).
Proof. exact (SYM (@lem5033000 A B u f)). Qed.
Lemma lem5033002 {A B : Type'} (u : A -> Prop) (f : A -> B) (h1 : term87 A B u f) : term87 A B u f.
Proof. exact (h1). Qed.
Lemma lem5033005 {A B : Type'} (u : A -> Prop) (f : A -> B) (h1 : term86 A B u f) : term86 A B u f.
Proof. exact (h1). Qed.
Lemma lem5033006 {A B : Type'} (u : A -> Prop) (f : A -> B) : term88 A B u f.
Proof. exact (fun h0 : term86 A B u f => @lem5033005 A B u f h0). Qed.
Lemma lem5033007 {A B : Type'} (u : A -> Prop) (f : A -> B) (h1 : term88 A B u f) : term88 A B u f.
Proof. exact (h1). Qed.
Lemma lem5033008 {A B : Type'} (u : A -> Prop) (f : A -> B) (h1 : term86 A B u f) : term86 A B u f.
Proof. exact (h1). Qed.
Lemma lem5033009 {A B : Type'} (u : A -> Prop) (f : A -> B) (h1 : term86 A B u f) (h2 : term88 A B u f) : term86 A B u f.
Proof. exact (@lem5033007 A B u f h2 (@lem5033008 A B u f h1)). Qed.
Lemma lem5033010 {A B : Type'} (u : A -> Prop) (f : A -> B) (h1 : term86 A B u f) : term89 A B u f.
Proof. exact (fun h0 : term88 A B u f => @lem5033009 A B u f h1 h0). Qed.
Lemma lem5033011 {A B : Type'} (u : A -> Prop) (f : A -> B) (h1 : term88 A B u f) : term88 A B u f.
Proof. exact (h1). Qed.
Lemma lem5033012 {A B : Type'} (u : A -> Prop) (f : A -> B) (h1 : term86 A B u f) (h2 : term88 A B u f) : term86 A B u f.
Proof. exact (@lem5033010 A B u f h1 (@lem5033011 A B u f h2)). Qed.
Lemma lem5033013 {A B : Type'} (u : A -> Prop) (f : A -> B) (h1 : term88 A B u f) : term88 A B u f.
Proof. exact (fun h0 : term86 A B u f => @lem5033012 A B u f h0 h1). Qed.
Lemma lem5033014 {A B : Type'} (u : A -> Prop) (f : A -> B) : term90 A B u f.
Proof. exact (fun h0 : term88 A B u f => @lem5033013 A B u f h0). Qed.
Lemma lem5033017 {A B : Type'} (u : A -> Prop) (f : A -> B) : term88 A B u f.
Proof. exact (@lem5033014 A B u f (@lem5033006 A B u f)). Qed.
Lemma lem5033018 {A B : Type'} (u : A -> Prop) (f : A -> B) : term88 A B u f.
Proof. exact (@lem5033017 A B u f). Qed.
Lemma lem5033028 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5033029 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term86 A B u f) = (term91 A B u f).
Proof. exact (@lem5033028 (term87 A B u f)). Qed.
Lemma lem5033031 (t : Prop) : (term92 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5033032 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term91 A B u f) = (term84 A B u f).
Proof. exact (@lem5033031 (term84 A B u f)). Qed.
Lemma lem5033035 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term86 A B u f) = (term84 A B u f).
Proof. exact (TRANS (@lem5033029 A B u f) (@lem5033032 A B u f)). Qed.
Lemma lem5033152 {A B : Type'} (f : A -> B) : (term93 A B f) = (term94 A B f).
Proof. exact (fun_ext (fun u : A -> Prop => @lem5033035 A B u f)). Qed.
Lemma lem5033153 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5033154 {A B : Type'} (f : A -> B) : (term95 A B f) = (term96 A B f).
Proof. exact (MK_COMB (@lem5033153 A) (@lem5033152 A B f)). Qed.
Lemma lem5033159 {A B : Type'} : (term97 A B) = (term98 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem5033154 A B f)). Qed.
Lemma lem5033160 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5033169 {A B : Type'} : (term99 A B) = (term100 A B).
Proof. exact (MK_COMB (@lem5033160 A B) (@lem5033159 A B)). Qed.
Lemma lem5033174 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((s x) = (t x)) = ((s x) = (t x)).
Proof. exact (eq_refl ((s x) = (t x))). Qed.
Lemma lem5033175 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term77 A s t) = (term77 A s t).
Proof. exact (fun_ext (fun x : A => @lem5033174 A s t x)). Qed.
Lemma lem5033176 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5033177 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term78 A s t) = (term78 A s t).
Proof. exact (MK_COMB (@lem5033176 A) (@lem5033175 A s t)). Qed.
Lemma lem5033182 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term62 A B x f t x') = (term62 A B x f t x').
Proof. exact (eq_refl (term62 A B x f t x')). Qed.
Lemma lem5033183 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term64 A B x f t) = (term64 A B x f t).
Proof. exact (fun_ext (fun x' : A => @lem5033182 A B x f t x')). Qed.
Lemma lem5033184 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5033185 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term65 A B x f t) = (term65 A B x f t).
Proof. exact (MK_COMB (@lem5033184 A) (@lem5033183 A B x f t)). Qed.
Lemma lem5033190 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term62 A B x f s x') = (term62 A B x f s x').
Proof. exact (eq_refl (term62 A B x f s x')). Qed.
Lemma lem5033191 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term64 A B x f s) = (term64 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem5033190 A B x f s x')). Qed.
Lemma lem5033192 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5033193 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term65 A B x f s) = (term65 A B x f s).
Proof. exact (MK_COMB (@lem5033192 A) (@lem5033191 A B x f s)). Qed.
Lemma lem5033194 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5033195 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term67 A B x f s) = (term67 A B x f s).
Proof. exact (MK_COMB (@lem5033194) (@lem5033193 A B x f s)). Qed.
Lemma lem5033196 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : ((term65 A B x f s) = (term65 A B x f t)) = ((term65 A B x f s) = (term65 A B x f t)).
Proof. exact (MK_COMB (@lem5033195 A B x f s) (@lem5033185 A B x f t)). Qed.
Lemma lem5033197 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term69 A B s f t) = (term69 A B s f t).
Proof. exact (fun_ext (fun x : B => @lem5033196 A B s x f t)). Qed.
Lemma lem5033198 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5033199 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term70 A B s f t) = (term70 A B s f t).
Proof. exact (MK_COMB (@lem5033198 B) (@lem5033197 A B s f t)). Qed.
Lemma lem5033204 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term53 A t u x) = (term53 A t u x).
Proof. exact (eq_refl (term53 A t u x)). Qed.
Lemma lem5033205 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term55 A t u) = (term55 A t u).
Proof. exact (fun_ext (fun x : A => @lem5033204 A t u x)). Qed.
Lemma lem5033206 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5033207 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term56 A t u) = (term56 A t u).
Proof. exact (MK_COMB (@lem5033206 A) (@lem5033205 A t u)). Qed.
Lemma lem5033208 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5033209 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term57 A t u) = (term57 A t u).
Proof. exact (MK_COMB (@lem5033208) (@lem5033207 A t u)). Qed.
Lemma lem5033210 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term71 A B u s f t) = (term71 A B u s f t).
Proof. exact (MK_COMB (@lem5033209 A t u) (@lem5033199 A B s f t)). Qed.
Lemma lem5033215 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term53 A s u x) = (term53 A s u x).
Proof. exact (eq_refl (term53 A s u x)). Qed.
Lemma lem5033216 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term55 A s u) = (term55 A s u).
Proof. exact (fun_ext (fun x : A => @lem5033215 A s u x)). Qed.
Lemma lem5033217 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5033218 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term56 A s u) = (term56 A s u).
Proof. exact (MK_COMB (@lem5033217 A) (@lem5033216 A s u)). Qed.
Lemma lem5033219 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5033220 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term57 A s u) = (term57 A s u).
Proof. exact (MK_COMB (@lem5033219) (@lem5033218 A s u)). Qed.
Lemma lem5033221 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term72 A B u s f t) = (term72 A B u s f t).
Proof. exact (MK_COMB (@lem5033220 A s u) (@lem5033210 A B u s f t)). Qed.
Lemma lem5033222 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5033223 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term73 A B u s f t) = (term73 A B u s f t).
Proof. exact (MK_COMB (@lem5033222) (@lem5033221 A B u s f t)). Qed.
Lemma lem5033224 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term79 A B u f s t) = (term79 A B u f s t).
Proof. exact (MK_COMB (@lem5033223 A B u s f t) (@lem5033177 A s t)). Qed.
Lemma lem5033225 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) : (term80 A B u f s) = (term80 A B u f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem5033224 A B u f s t)). Qed.
Lemma lem5033226 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5033227 {A B : Type'} (u : A -> Prop) (f : A -> B) (s : A -> Prop) : (term81 A B u f s) = (term81 A B u f s).
Proof. exact (MK_COMB (@lem5033226 A) (@lem5033225 A B u f s)). Qed.
Lemma lem5033228 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term82 A B u f) = (term82 A B u f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5033227 A B u f s)). Qed.
Lemma lem5033229 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5033230 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term83 A B u f) = (term83 A B u f).
Proof. exact (MK_COMB (@lem5033229 A) (@lem5033228 A B u f)). Qed.
Lemma lem5033243 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (y : A) : (term40 A B u f x y) = (term40 A B u f x y).
Proof. exact (eq_refl (term40 A B u f x y)). Qed.
Lemma lem5033244 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) : (term42 A B u f x) = (term42 A B u f x).
Proof. exact (fun_ext (fun y : A => @lem5033243 A B u f x y)). Qed.
Lemma lem5033245 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5033246 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) : (term44 A B u f x) = (term44 A B u f x).
Proof. exact (MK_COMB (@lem5033245 A) (@lem5033244 A B u f x)). Qed.
Lemma lem5033247 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term46 A B u f) = (term46 A B u f).
Proof. exact (fun_ext (fun x : A => @lem5033246 A B u f x)). Qed.
Lemma lem5033248 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5033249 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term48 A B u f) = (term48 A B u f).
Proof. exact (MK_COMB (@lem5033248 A) (@lem5033247 A B u f)). Qed.
Lemma lem5033250 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5033251 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term49 A B u f) = (term49 A B u f).
Proof. exact (MK_COMB (@lem5033250) (@lem5033249 A B u f)). Qed.
Lemma lem5033252 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term84 A B u f) = (term84 A B u f).
Proof. exact (MK_COMB (@lem5033251 A B u f) (@lem5033230 A B u f)). Qed.
Lemma lem5033253 {A B : Type'} (f : A -> B) : (term94 A B f) = (term94 A B f).
Proof. exact (fun_ext (fun u : A -> Prop => @lem5033252 A B u f)). Qed.
Lemma lem5033254 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5033255 {A B : Type'} (f : A -> B) : (term96 A B f) = (term96 A B f).
Proof. exact (MK_COMB (@lem5033254 A) (@lem5033253 A B f)). Qed.
Lemma lem5033256 {A B : Type'} : (term98 A B) = (term98 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem5033255 A B f)). Qed.
Lemma lem5033257 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5033258 {A B : Type'} : (term100 A B) = (term100 A B).
Proof. exact (MK_COMB (@lem5033257 A B) (@lem5033256 A B)). Qed.
Lemma lem5033355 {A B : Type'} : (term99 A B) = (term100 A B).
Proof. exact (TRANS (@lem5033169 A B) (@lem5033258 A B)). Qed.
Lemma lem5033356 {A B : Type'} : (term100 A B) = (term99 A B).
Proof. exact (SYM (@lem5033355 A B)). Qed.
Lemma lem5033357 {A B : Type'} (u : A -> Prop) (f : A -> B) (h1 : term48 A B u f) : term48 A B u f.
Proof. exact (h1). Qed.
Lemma lem5033358 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term72 A B u s f t) : term72 A B u s f t.
Proof. exact (h1). Qed.
Lemma lem5033360 (p : Prop) : p = (term85 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5033361 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((s x) = (t x)) = (term101 A s t x).
Proof. exact (@lem5033360 ((s x) = (t x))). Qed.
Lemma lem5033362 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term101 A s t x) = ((s x) = (t x)).
Proof. exact (SYM (@lem5033361 A s t x)). Qed.
Lemma lem5033363 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term102 A s t x) : term102 A s t x.
Proof. exact (h1). Qed.
Lemma lem5033371 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (y : A) : (term103 A B u x f y) = (term104 A B u x f y).
Proof. exact (@lem17045 (u y) ((f x) = (f y))). Qed.
Lemma lem5033373 {A : Type'} (u : A -> Prop) (x : A) : (term105 A u x) = (term105 A u x).
Proof. exact (eq_refl (term105 A u x)). Qed.
Lemma lem5033374 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (y : A) : (term106 A B u x f y) = (term107 A B u x f y).
Proof. exact (MK_COMB (@lem5033373 A u x) (@lem5033371 A B u x f y)). Qed.
Lemma lem5033375 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (y : A) : (term108 A B u x f y) = (term106 A B u x f y).
Proof. exact (@lem17045 (u x) (term34 A B u x f y)). Qed.
Lemma lem5033376 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (y : A) : (term108 A B u x f y) = (term107 A B u x f y).
Proof. exact (TRANS (@lem5033375 A B u x f y) (@lem5033374 A B u x f y)). Qed.
Lemma lem5033377 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem5033378 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5033379 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (y : A) : (term109 A B u x f y) = (term110 A B u x f y).
Proof. exact (MK_COMB (@lem5033378) (@lem5033376 A B u x f y)). Qed.
Lemma lem5033380 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (y : A) : (term111 A B u f x y) = (term112 A B u f x y).
Proof. exact (MK_COMB (@lem5033379 A B u x f y) (@lem5033377 A x y)). Qed.
Lemma lem5033381 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (y : A) : (term40 A B u f x y) = (term111 A B u f x y).
Proof. exact (@lem17265 (term36 A B u x f y) (x = y)). Qed.
Lemma lem5033382 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (y : A) : (term40 A B u f x y) = (term112 A B u f x y).
Proof. exact (TRANS (@lem5033381 A B u f x y) (@lem5033380 A B u f x y)). Qed.
Lemma lem5033383 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) : (term42 A B u f x) = (term113 A B u f x).
Proof. exact (fun_ext (fun y : A => @lem5033382 A B u f x y)). Qed.
Lemma lem5033384 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5033385 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) : (term44 A B u f x) = (term114 A B u f x).
Proof. exact (MK_COMB (@lem5033384 A) (@lem5033383 A B u f x)). Qed.
Lemma lem5033386 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term46 A B u f) = (term115 A B u f).
Proof. exact (fun_ext (fun x : A => @lem5033385 A B u f x)). Qed.
Lemma lem5033387 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5033444 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term48 A B u f) = (term116 A B u f).
Proof. exact (MK_COMB (@lem5033387 A) (@lem5033386 A B u f)). Qed.
Lemma lem5033445 {A B : Type'} (u : A -> Prop) (f : A -> B) (h1 : term48 A B u f) : term116 A B u f.
Proof. exact (EQ_MP (@lem5033444 A B u f) (@lem5033357 A B u f h1)). Qed.
Lemma lem5033452 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term53 A s u x) = (term117 A s u x).
Proof. exact (@lem17265 (s x) (u x)). Qed.
Lemma lem5033453 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term55 A s u) = (term118 A s u).
Proof. exact (fun_ext (fun x : A => @lem5033452 A s u x)). Qed.
Lemma lem5033454 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5033455 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term56 A s u) = (term119 A s u).
Proof. exact (MK_COMB (@lem5033454 A) (@lem5033453 A s u)). Qed.
Lemma lem5033462 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term53 A t u x) = (term117 A t u x).
Proof. exact (@lem17265 (t x) (u x)). Qed.
Lemma lem5033463 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term55 A t u) = (term118 A t u).
Proof. exact (fun_ext (fun x : A => @lem5033462 A t u x)). Qed.
Lemma lem5033464 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5033465 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term56 A t u) = (term119 A t u).
Proof. exact (MK_COMB (@lem5033464 A) (@lem5033463 A t u)). Qed.
Lemma lem5033474 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term120 A B x f s x') = (term121 A B x f s x').
Proof. exact (@lem17045 (x = (f x')) (s x')). Qed.
Lemma lem5033477 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term62 A B x f s x') = (term62 A B x f s x').
Proof. exact (eq_refl (term62 A B x f s x')). Qed.
Lemma lem5033478 {A : Type'} (P : A -> Prop) : (term122 A P) = (term123 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem5033479 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term124 A B x f s) = (term125 A B x f s).
Proof. exact (@lem5033478 A (term64 A B x f s)). Qed.
Lemma lem5033480 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term126 A B x f s x') = (term62 A B x f s x').
Proof. exact (eq_refl (term126 A B x f s x')). Qed.
Lemma lem5033481 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5033482 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term127 A B x f s x') = (term120 A B x f s x').
Proof. exact (MK_COMB (@lem5033481) (@lem5033480 A B x f s x')). Qed.
Lemma lem5033483 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term127 A B x f s x') = (term121 A B x f s x').
Proof. exact (TRANS (@lem5033482 A B x f s x') (@lem5033474 A B x f s x')). Qed.
Lemma lem5033484 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term128 A B x f s) = (term129 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem5033483 A B x f s x')). Qed.
Lemma lem5033485 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5033486 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term125 A B x f s) = (term130 A B x f s).
Proof. exact (MK_COMB (@lem5033485 A) (@lem5033484 A B x f s)). Qed.
Lemma lem5033487 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term124 A B x f s) = (term130 A B x f s).
Proof. exact (TRANS (@lem5033479 A B x f s) (@lem5033486 A B x f s)). Qed.
Lemma lem5033488 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term64 A B x f s) = (term64 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem5033477 A B x f s x')). Qed.
Lemma lem5033489 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5033490 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term65 A B x f s) = (term65 A B x f s).
Proof. exact (MK_COMB (@lem5033489 A) (@lem5033488 A B x f s)). Qed.
Lemma lem5033499 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term120 A B x f t x') = (term121 A B x f t x').
Proof. exact (@lem17045 (x = (f x')) (t x')). Qed.
Lemma lem5033502 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term62 A B x f t x') = (term62 A B x f t x').
Proof. exact (eq_refl (term62 A B x f t x')). Qed.
Lemma lem5033503 {A : Type'} (P : A -> Prop) : (term122 A P) = (term123 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem5033504 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term124 A B x f t) = (term125 A B x f t).
Proof. exact (@lem5033503 A (term64 A B x f t)). Qed.
Lemma lem5033505 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term126 A B x f t x') = (term62 A B x f t x').
Proof. exact (eq_refl (term126 A B x f t x')). Qed.
Lemma lem5033506 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5033507 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term127 A B x f t x') = (term120 A B x f t x').
Proof. exact (MK_COMB (@lem5033506) (@lem5033505 A B x f t x')). Qed.
Lemma lem5033508 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term127 A B x f t x') = (term121 A B x f t x').
Proof. exact (TRANS (@lem5033507 A B x f t x') (@lem5033499 A B x f t x')). Qed.
Lemma lem5033509 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term128 A B x f t) = (term129 A B x f t).
Proof. exact (fun_ext (fun x' : A => @lem5033508 A B x f t x')). Qed.
Lemma lem5033510 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5033511 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term125 A B x f t) = (term130 A B x f t).
Proof. exact (MK_COMB (@lem5033510 A) (@lem5033509 A B x f t)). Qed.
Lemma lem5033512 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term124 A B x f t) = (term130 A B x f t).
Proof. exact (TRANS (@lem5033504 A B x f t) (@lem5033511 A B x f t)). Qed.
Lemma lem5033513 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term64 A B x f t) = (term64 A B x f t).
Proof. exact (fun_ext (fun x' : A => @lem5033502 A B x f t x')). Qed.
Lemma lem5033514 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5033515 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term65 A B x f t) = (term65 A B x f t).
Proof. exact (MK_COMB (@lem5033514 A) (@lem5033513 A B x f t)). Qed.
Lemma lem5033516 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5033517 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term131 A B x f s) = (term132 A B x f s).
Proof. exact (MK_COMB (@lem5033516) (@lem5033487 A B x f s)). Qed.
Lemma lem5033518 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term133 A B s x f t) = (term134 A B s x f t).
Proof. exact (MK_COMB (@lem5033517 A B x f s) (@lem5033515 A B x f t)). Qed.
Lemma lem5033519 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5033520 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term135 A B x f s) = (term135 A B x f s).
Proof. exact (MK_COMB (@lem5033519) (@lem5033490 A B x f s)). Qed.
Lemma lem5033521 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term136 A B s x f t) = (term137 A B s x f t).
Proof. exact (MK_COMB (@lem5033520 A B x f s) (@lem5033512 A B x f t)). Qed.
Lemma lem5033522 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5033523 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term138 A B s x f t) = (term139 A B s x f t).
Proof. exact (MK_COMB (@lem5033522) (@lem5033521 A B s x f t)). Qed.
Lemma lem5033524 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term140 A B s x f t) = (term141 A B s x f t).
Proof. exact (MK_COMB (@lem5033523 A B s x f t) (@lem5033518 A B s x f t)). Qed.
Lemma lem5033525 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : ((term65 A B x f s) = (term65 A B x f t)) = (term140 A B s x f t).
Proof. exact (@lem17784 (term65 A B x f s) (term65 A B x f t)). Qed.
Lemma lem5033526 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : ((term65 A B x f s) = (term65 A B x f t)) = (term141 A B s x f t).
Proof. exact (TRANS (@lem5033525 A B s x f t) (@lem5033524 A B s x f t)). Qed.
Lemma lem5033527 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term69 A B s f t) = (term142 A B s f t).
Proof. exact (fun_ext (fun x : B => @lem5033526 A B s x f t)). Qed.
Lemma lem5033528 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5033529 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term70 A B s f t) = (term143 A B s f t).
Proof. exact (MK_COMB (@lem5033528 B) (@lem5033527 A B s f t)). Qed.
Lemma lem5033530 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5033531 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term57 A t u) = (term144 A t u).
Proof. exact (MK_COMB (@lem5033530) (@lem5033465 A t u)). Qed.
Lemma lem5033532 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term71 A B u s f t) = (term145 A B u s f t).
Proof. exact (MK_COMB (@lem5033531 A t u) (@lem5033529 A B s f t)). Qed.
Lemma lem5033533 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5033534 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term57 A s u) = (term144 A s u).
Proof. exact (MK_COMB (@lem5033533) (@lem5033455 A s u)). Qed.
Lemma lem5033535 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term72 A B u s f t) = (term146 A B u s f t).
Proof. exact (MK_COMB (@lem5033534 A s u) (@lem5033532 A B u s f t)). Qed.
Lemma lem5033601 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term147 A P Q) = (term148 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5033602 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term147 B P Q) = (term148 B P Q).
Proof. exact (@lem5033601 B P Q). Qed.
Lemma lem5033603 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term149 A B s f t) = (term150 A B s f t).
Proof. exact (@lem5033602 B (term151 A B s f t) (term152 A B s f t)). Qed.
Lemma lem5033604 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term153 A B s f t x) = (term137 A B s x f t).
Proof. exact (eq_refl (term153 A B s f t x)). Qed.
Lemma lem5033605 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5033606 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term154 A B s f t x) = (term139 A B s x f t).
Proof. exact (MK_COMB (@lem5033605) (@lem5033604 A B s x f t)). Qed.
Lemma lem5033607 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term155 A B s f t x) = (term134 A B s x f t).
Proof. exact (eq_refl (term155 A B s f t x)). Qed.
Lemma lem5033608 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term156 A B s f t x) = (term141 A B s x f t).
Proof. exact (MK_COMB (@lem5033606 A B s x f t) (@lem5033607 A B s x f t)). Qed.
Lemma lem5033609 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term157 A B s f t) = (term142 A B s f t).
Proof. exact (fun_ext (fun x : B => @lem5033608 A B s x f t)). Qed.
Lemma lem5033610 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5033611 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term149 A B s f t) = (term143 A B s f t).
Proof. exact (MK_COMB (@lem5033610 B) (@lem5033609 A B s f t)). Qed.
Lemma lem5033612 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5033613 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term158 A B s f t) = (term159 A B s f t).
Proof. exact (MK_COMB (@lem5033612) (@lem5033611 A B s f t)). Qed.
Lemma lem5033614 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term153 A B s f t x) = (term137 A B s x f t).
Proof. exact (eq_refl (term153 A B s f t x)). Qed.
Lemma lem5033615 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term160 A B s f t) = (term151 A B s f t).
Proof. exact (fun_ext (fun x : B => @lem5033614 A B s x f t)). Qed.
Lemma lem5033616 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5033617 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term161 A B s f t) = (term162 A B s f t).
Proof. exact (MK_COMB (@lem5033616 B) (@lem5033615 A B s f t)). Qed.
Lemma lem5033618 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5033619 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term163 A B s f t) = (term164 A B s f t).
Proof. exact (MK_COMB (@lem5033618) (@lem5033617 A B s f t)). Qed.
Lemma lem5033620 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term155 A B s f t x) = (term134 A B s x f t).
Proof. exact (eq_refl (term155 A B s f t x)). Qed.
Lemma lem5033621 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term165 A B s f t) = (term152 A B s f t).
Proof. exact (fun_ext (fun x : B => @lem5033620 A B s x f t)). Qed.
Lemma lem5033622 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5033623 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term166 A B s f t) = (term167 A B s f t).
Proof. exact (MK_COMB (@lem5033622 B) (@lem5033621 A B s f t)). Qed.
Lemma lem5033624 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term150 A B s f t) = (term168 A B s f t).
Proof. exact (MK_COMB (@lem5033619 A B s f t) (@lem5033623 A B s f t)). Qed.
Lemma lem5033625 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : ((term149 A B s f t) = (term150 A B s f t)) = ((term143 A B s f t) = (term168 A B s f t)).
Proof. exact (MK_COMB (@lem5033613 A B s f t) (@lem5033624 A B s f t)). Qed.
Lemma lem5033626 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term143 A B s f t) = (term168 A B s f t).
Proof. exact (EQ_MP (@lem5033625 A B s f t) (@lem5033603 A B s f t)). Qed.
Lemma lem5033883 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term144 A t u) = (term144 A t u).
Proof. exact (eq_refl (term144 A t u)). Qed.
Lemma lem5033884 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term145 A B u s f t) = (term169 A B u s f t).
Proof. exact (MK_COMB (@lem5033883 A t u) (@lem5033626 A B s f t)). Qed.
Lemma lem5033885 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term144 A s u) = (term144 A s u).
Proof. exact (eq_refl (term144 A s u)). Qed.
Lemma lem5033886 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term146 A B u s f t) = (term170 A B u s f t).
Proof. exact (MK_COMB (@lem5033885 A s u) (@lem5033884 A B u s f t)). Qed.
Lemma lem5033888 {A : Type'} (P : A -> Prop) (Q : Prop) : (term171 A P Q) = (term172 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5033889 {A : Type'} (P : A -> Prop) (Q : Prop) : (term171 A P Q) = (term172 A P Q).
Proof. exact (@lem5033888 A P Q). Qed.
Lemma lem5033890 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term173 A B s x f t) = (term174 A B s x f t).
Proof. exact (@lem5033889 A (term64 A B x f s) (term130 A B x f t)). Qed.
Lemma lem5033891 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term126 A B x f s x') = (term62 A B x f s x').
Proof. exact (eq_refl (term126 A B x f s x')). Qed.
Lemma lem5033892 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term175 A B x f s) = (term64 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem5033891 A B x f s x')). Qed.
Lemma lem5033893 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5033894 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term176 A B x f s) = (term65 A B x f s).
Proof. exact (MK_COMB (@lem5033893 A) (@lem5033892 A B x f s)). Qed.
Lemma lem5033895 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5033896 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term177 A B x f s) = (term135 A B x f s).
Proof. exact (MK_COMB (@lem5033895) (@lem5033894 A B x f s)). Qed.
Lemma lem5033897 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term130 A B x f t) = (term130 A B x f t).
Proof. exact (eq_refl (term130 A B x f t)). Qed.
Lemma lem5033898 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term173 A B s x f t) = (term137 A B s x f t).
Proof. exact (MK_COMB (@lem5033896 A B x f s) (@lem5033897 A B x f t)). Qed.
Lemma lem5033899 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5033900 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term178 A B s x f t) = (term179 A B s x f t).
Proof. exact (MK_COMB (@lem5033899) (@lem5033898 A B s x f t)). Qed.
Lemma lem5033901 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term126 A B x f s x') = (term62 A B x f s x').
Proof. exact (eq_refl (term126 A B x f s x')). Qed.
Lemma lem5033902 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5033903 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term180 A B x f s x') = (term181 A B x f s x').
Proof. exact (MK_COMB (@lem5033902) (@lem5033901 A B x f s x')). Qed.
Lemma lem5033904 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term130 A B x f t) = (term130 A B x f t).
Proof. exact (eq_refl (term130 A B x f t)). Qed.
Lemma lem5033905 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term182 A B s x x' f t) = (term183 A B s x x' f t).
Proof. exact (MK_COMB (@lem5033903 A B x' f s x) (@lem5033904 A B x' f t)). Qed.
Lemma lem5033906 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term184 A B s x f t) = (term185 A B s x f t).
Proof. exact (fun_ext (fun x' : A => @lem5033905 A B s x' x f t)). Qed.
Lemma lem5033907 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5033908 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term174 A B s x f t) = (term186 A B s x f t).
Proof. exact (MK_COMB (@lem5033907 A) (@lem5033906 A B s x f t)). Qed.
Lemma lem5033909 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : ((term173 A B s x f t) = (term174 A B s x f t)) = ((term137 A B s x f t) = (term186 A B s x f t)).
Proof. exact (MK_COMB (@lem5033900 A B s x f t) (@lem5033908 A B s x f t)). Qed.
Lemma lem5033910 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term137 A B s x f t) = (term186 A B s x f t).
Proof. exact (EQ_MP (@lem5033909 A B s x f t) (@lem5033890 A B s x f t)). Qed.
Lemma lem5033911 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term151 A B s f t) = (term187 A B s f t).
Proof. exact (fun_ext (fun x : B => @lem5033910 A B s x f t)). Qed.
Lemma lem5033912 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5033913 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term162 A B s f t) = (term188 A B s f t).
Proof. exact (MK_COMB (@lem5033912 B) (@lem5033911 A B s f t)). Qed.
Lemma lem5033915 {A B : Type'} (P : type1413 A B) : (term189 A B P) = (term190 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5033916 {A B : Type'} (P : type1470 A B) : (term191 A B P) = (term192 A B P).
Proof. exact (@lem5033915 B A P). Qed.
Lemma lem5033917 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term193 A B s f t) = (term194 A B s f t).
Proof. exact (@lem5033916 A B (term195 A B s f t)). Qed.
Lemma lem5033918 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term196 A B s f t x) = (term185 A B s x f t).
Proof. exact (eq_refl (term196 A B s f t x)). Qed.
Lemma lem5033919 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5033920 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term197 A B s f t x x') = (term198 A B s x f t x').
Proof. exact (MK_COMB (@lem5033918 A B s x f t) (@lem5033919 A x')). Qed.
Lemma lem5033921 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term198 A B s x' f t x) = (term183 A B s x x' f t).
Proof. exact (eq_refl (term198 A B s x' f t x)). Qed.
Lemma lem5033922 {A B : Type'} (s : A -> Prop) (x : A) (x' : B) (f : A -> B) (t : A -> Prop) : (term197 A B s f t x' x) = (term183 A B s x x' f t).
Proof. exact (TRANS (@lem5033920 A B s x' f t x) (@lem5033921 A B s x x' f t)). Qed.
Lemma lem5033923 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term199 A B s f t x) = (term185 A B s x f t).
Proof. exact (fun_ext (fun x' : A => @lem5033922 A B s x' x f t)). Qed.
Lemma lem5033924 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5033925 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term200 A B s f t x) = (term186 A B s x f t).
Proof. exact (MK_COMB (@lem5033924 A) (@lem5033923 A B s x f t)). Qed.
Lemma lem5033926 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term201 A B s f t) = (term187 A B s f t).
Proof. exact (fun_ext (fun x : B => @lem5033925 A B s x f t)). Qed.
Lemma lem5033927 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5033928 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term193 A B s f t) = (term188 A B s f t).
Proof. exact (MK_COMB (@lem5033927 B) (@lem5033926 A B s f t)). Qed.
Lemma lem5033929 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5033930 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term202 A B s f t) = (term203 A B s f t).
Proof. exact (MK_COMB (@lem5033929) (@lem5033928 A B s f t)). Qed.
Lemma lem5033931 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term196 A B s f t x) = (term185 A B s x f t).
Proof. exact (eq_refl (term196 A B s f t x)). Qed.
Lemma lem5033932 {A B : Type'} (x : B -> A) (x' : B) : (x x') = (x x').
Proof. exact (eq_refl (x x')). Qed.
Lemma lem5033933 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x : B -> A) (x' : B) : (term204 A B s f t x x') = (term205 A B s f t x x').
Proof. exact (MK_COMB (@lem5033931 A B s x' f t) (@lem5033932 A B x x')). Qed.
Lemma lem5033934 {A B : Type'} (s : A -> Prop) (x : B -> A) (x' : B) (f : A -> B) (t : A -> Prop) : (term205 A B s f t x x') = (term206 A B s x x' f t).
Proof. exact (eq_refl (term205 A B s f t x x')). Qed.
Lemma lem5033935 {A B : Type'} (s : A -> Prop) (x : B -> A) (x' : B) (f : A -> B) (t : A -> Prop) : (term204 A B s f t x x') = (term206 A B s x x' f t).
Proof. exact (TRANS (@lem5033933 A B s f t x x') (@lem5033934 A B s x x' f t)). Qed.
Lemma lem5033936 {A B : Type'} (s : A -> Prop) (x : B -> A) (f : A -> B) (t : A -> Prop) : (term207 A B s f t x) = (term208 A B s x f t).
Proof. exact (fun_ext (fun x' : B => @lem5033935 A B s x x' f t)). Qed.
Lemma lem5033937 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5033938 {A B : Type'} (s : A -> Prop) (x : B -> A) (f : A -> B) (t : A -> Prop) : (term209 A B s f t x) = (term210 A B s x f t).
Proof. exact (MK_COMB (@lem5033937 B) (@lem5033936 A B s x f t)). Qed.
Lemma lem5033939 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term211 A B s f t) = (term212 A B s f t).
Proof. exact (fun_ext (fun x : B -> A => @lem5033938 A B s x f t)). Qed.
Lemma lem5033940 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem5033941 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term194 A B s f t) = (term213 A B s f t).
Proof. exact (MK_COMB (@lem5033940 A B) (@lem5033939 A B s f t)). Qed.
Lemma lem5033942 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : ((term193 A B s f t) = (term194 A B s f t)) = ((term188 A B s f t) = (term213 A B s f t)).
Proof. exact (MK_COMB (@lem5033930 A B s f t) (@lem5033941 A B s f t)). Qed.
Lemma lem5033943 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term188 A B s f t) = (term213 A B s f t).
Proof. exact (EQ_MP (@lem5033942 A B s f t) (@lem5033917 A B s f t)). Qed.
Lemma lem5033944 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term162 A B s f t) = (term213 A B s f t).
Proof. exact (TRANS (@lem5033913 A B s f t) (@lem5033943 A B s f t)). Qed.
Lemma lem5033945 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5033946 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term164 A B s f t) = (term214 A B s f t).
Proof. exact (MK_COMB (@lem5033945) (@lem5033944 A B s f t)). Qed.
Lemma lem5033948 {A : Type'} (P : Prop) (Q : A -> Prop) : (term215 A P Q) = (term216 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5033949 {A : Type'} (P : Prop) (Q : A -> Prop) : (term215 A P Q) = (term216 A P Q).
Proof. exact (@lem5033948 A P Q). Qed.
Lemma lem5033950 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term217 A B s x f t) = (term218 A B s x f t).
Proof. exact (@lem5033949 A (term130 A B x f s) (term64 A B x f t)). Qed.
Lemma lem5033951 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term126 A B x f t x') = (term62 A B x f t x').
Proof. exact (eq_refl (term126 A B x f t x')). Qed.
Lemma lem5033952 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term175 A B x f t) = (term64 A B x f t).
Proof. exact (fun_ext (fun x' : A => @lem5033951 A B x f t x')). Qed.
Lemma lem5033953 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5033954 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term176 A B x f t) = (term65 A B x f t).
Proof. exact (MK_COMB (@lem5033953 A) (@lem5033952 A B x f t)). Qed.
Lemma lem5033955 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term132 A B x f s) = (term132 A B x f s).
Proof. exact (eq_refl (term132 A B x f s)). Qed.
Lemma lem5033956 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term217 A B s x f t) = (term134 A B s x f t).
Proof. exact (MK_COMB (@lem5033955 A B x f s) (@lem5033954 A B x f t)). Qed.
Lemma lem5033957 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5033958 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term219 A B s x f t) = (term220 A B s x f t).
Proof. exact (MK_COMB (@lem5033957) (@lem5033956 A B s x f t)). Qed.
Lemma lem5033959 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term126 A B x f t x') = (term62 A B x f t x').
Proof. exact (eq_refl (term126 A B x f t x')). Qed.
Lemma lem5033960 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term132 A B x f s) = (term132 A B x f s).
Proof. exact (eq_refl (term132 A B x f s)). Qed.
Lemma lem5033961 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term221 A B s x f t x') = (term222 A B s x f t x').
Proof. exact (MK_COMB (@lem5033960 A B x f s) (@lem5033959 A B x f t x')). Qed.
Lemma lem5033962 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term223 A B s x f t) = (term224 A B s x f t).
Proof. exact (fun_ext (fun x' : A => @lem5033961 A B s x f t x')). Qed.
Lemma lem5033963 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5033964 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term218 A B s x f t) = (term225 A B s x f t).
Proof. exact (MK_COMB (@lem5033963 A) (@lem5033962 A B s x f t)). Qed.
Lemma lem5033965 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : ((term217 A B s x f t) = (term218 A B s x f t)) = ((term134 A B s x f t) = (term225 A B s x f t)).
Proof. exact (MK_COMB (@lem5033958 A B s x f t) (@lem5033964 A B s x f t)). Qed.
Lemma lem5033966 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term134 A B s x f t) = (term225 A B s x f t).
Proof. exact (EQ_MP (@lem5033965 A B s x f t) (@lem5033950 A B s x f t)). Qed.
Lemma lem5033967 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term152 A B s f t) = (term226 A B s f t).
Proof. exact (fun_ext (fun x : B => @lem5033966 A B s x f t)). Qed.
Lemma lem5033968 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5033969 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term167 A B s f t) = (term227 A B s f t).
Proof. exact (MK_COMB (@lem5033968 B) (@lem5033967 A B s f t)). Qed.
Lemma lem5033971 {A B : Type'} (P : type1413 A B) : (term189 A B P) = (term190 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5033972 {A B : Type'} (P : type1470 A B) : (term191 A B P) = (term192 A B P).
Proof. exact (@lem5033971 B A P). Qed.
Lemma lem5033973 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term228 A B s f t) = (term229 A B s f t).
Proof. exact (@lem5033972 A B (term230 A B s f t)). Qed.
Lemma lem5033974 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term231 A B s f t x) = (term224 A B s x f t).
Proof. exact (eq_refl (term231 A B s f t x)). Qed.
Lemma lem5033975 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5033976 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term232 A B s f t x x') = (term233 A B s x f t x').
Proof. exact (MK_COMB (@lem5033974 A B s x f t) (@lem5033975 A x')). Qed.
Lemma lem5033977 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term233 A B s x f t x') = (term222 A B s x f t x').
Proof. exact (eq_refl (term233 A B s x f t x')). Qed.
Lemma lem5033978 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term232 A B s f t x x') = (term222 A B s x f t x').
Proof. exact (TRANS (@lem5033976 A B s x f t x') (@lem5033977 A B s x f t x')). Qed.
Lemma lem5033979 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term234 A B s f t x) = (term224 A B s x f t).
Proof. exact (fun_ext (fun x' : A => @lem5033978 A B s x f t x')). Qed.
Lemma lem5033980 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5033981 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term235 A B s f t x) = (term225 A B s x f t).
Proof. exact (MK_COMB (@lem5033980 A) (@lem5033979 A B s x f t)). Qed.
Lemma lem5033982 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term236 A B s f t) = (term226 A B s f t).
Proof. exact (fun_ext (fun x : B => @lem5033981 A B s x f t)). Qed.
Lemma lem5033983 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5033984 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term228 A B s f t) = (term227 A B s f t).
Proof. exact (MK_COMB (@lem5033983 B) (@lem5033982 A B s f t)). Qed.
Lemma lem5033985 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5033986 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term237 A B s f t) = (term238 A B s f t).
Proof. exact (MK_COMB (@lem5033985) (@lem5033984 A B s f t)). Qed.
Lemma lem5033987 {A B : Type'} (s : A -> Prop) (x : B) (f : A -> B) (t : A -> Prop) : (term231 A B s f t x) = (term224 A B s x f t).
Proof. exact (eq_refl (term231 A B s f t x)). Qed.
Lemma lem5033988 {A B : Type'} (x : B -> A) (x' : B) : (x x') = (x x').
Proof. exact (eq_refl (x x')). Qed.
Lemma lem5033989 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x : B -> A) (x' : B) : (term239 A B s f t x x') = (term240 A B s f t x x').
Proof. exact (MK_COMB (@lem5033987 A B s x' f t) (@lem5033988 A B x x')). Qed.
Lemma lem5033990 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x : B -> A) (x' : B) : (term240 A B s f t x x') = (term241 A B s f t x x').
Proof. exact (eq_refl (term240 A B s f t x x')). Qed.
Lemma lem5033991 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x : B -> A) (x' : B) : (term239 A B s f t x x') = (term241 A B s f t x x').
Proof. exact (TRANS (@lem5033989 A B s f t x x') (@lem5033990 A B s f t x x')). Qed.
Lemma lem5033992 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x : B -> A) : (term242 A B s f t x) = (term243 A B s f t x).
Proof. exact (fun_ext (fun x' : B => @lem5033991 A B s f t x x')). Qed.
Lemma lem5033993 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5033994 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x : B -> A) : (term244 A B s f t x) = (term245 A B s f t x).
Proof. exact (MK_COMB (@lem5033993 B) (@lem5033992 A B s f t x)). Qed.
Lemma lem5033995 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term246 A B s f t) = (term247 A B s f t).
Proof. exact (fun_ext (fun x : B -> A => @lem5033994 A B s f t x)). Qed.
Lemma lem5033996 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem5033997 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term229 A B s f t) = (term248 A B s f t).
Proof. exact (MK_COMB (@lem5033996 A B) (@lem5033995 A B s f t)). Qed.
Lemma lem5033998 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : ((term228 A B s f t) = (term229 A B s f t)) = ((term227 A B s f t) = (term248 A B s f t)).
Proof. exact (MK_COMB (@lem5033986 A B s f t) (@lem5033997 A B s f t)). Qed.
Lemma lem5033999 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term227 A B s f t) = (term248 A B s f t).
Proof. exact (EQ_MP (@lem5033998 A B s f t) (@lem5033973 A B s f t)). Qed.
Lemma lem5034000 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term167 A B s f t) = (term248 A B s f t).
Proof. exact (TRANS (@lem5033969 A B s f t) (@lem5033999 A B s f t)). Qed.
Lemma lem5034001 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term168 A B s f t) = (term249 A B s f t).
Proof. exact (MK_COMB (@lem5033946 A B s f t) (@lem5034000 A B s f t)). Qed.
Lemma lem5034003 {A : Type'} (P : A -> Prop) (Q : Prop) : (term250 A P Q) = (term251 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5034004 {A B : Type'} (P : type805 A B) (Q : Prop) : (term252 A B P Q) = (term253 A B P Q).
Proof. exact (@lem5034003 (B -> A) P Q). Qed.
Lemma lem5034005 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term254 A B s f t) = (term255 A B s f t).
Proof. exact (@lem5034004 A B (term212 A B s f t) (term248 A B s f t)). Qed.
Lemma lem5034006 {A B : Type'} (s : A -> Prop) (x : B -> A) (f : A -> B) (t : A -> Prop) : (term256 A B s f t x) = (term210 A B s x f t).
Proof. exact (eq_refl (term256 A B s f t x)). Qed.
Lemma lem5034007 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term257 A B s f t) = (term212 A B s f t).
Proof. exact (fun_ext (fun x : B -> A => @lem5034006 A B s x f t)). Qed.
Lemma lem5034008 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem5034009 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term258 A B s f t) = (term213 A B s f t).
Proof. exact (MK_COMB (@lem5034008 A B) (@lem5034007 A B s f t)). Qed.
Lemma lem5034010 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5034011 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term259 A B s f t) = (term214 A B s f t).
Proof. exact (MK_COMB (@lem5034010) (@lem5034009 A B s f t)). Qed.
Lemma lem5034012 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term248 A B s f t) = (term248 A B s f t).
Proof. exact (eq_refl (term248 A B s f t)). Qed.
Lemma lem5034013 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term254 A B s f t) = (term249 A B s f t).
Proof. exact (MK_COMB (@lem5034011 A B s f t) (@lem5034012 A B s f t)). Qed.
Lemma lem5034014 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5034015 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term260 A B s f t) = (term261 A B s f t).
Proof. exact (MK_COMB (@lem5034014) (@lem5034013 A B s f t)). Qed.
Lemma lem5034016 {A B : Type'} (s : A -> Prop) (x : B -> A) (f : A -> B) (t : A -> Prop) : (term256 A B s f t x) = (term210 A B s x f t).
Proof. exact (eq_refl (term256 A B s f t x)). Qed.
Lemma lem5034017 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5034018 {A B : Type'} (s : A -> Prop) (x : B -> A) (f : A -> B) (t : A -> Prop) : (term262 A B s f t x) = (term263 A B s x f t).
Proof. exact (MK_COMB (@lem5034017) (@lem5034016 A B s x f t)). Qed.
Lemma lem5034019 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term248 A B s f t) = (term248 A B s f t).
Proof. exact (eq_refl (term248 A B s f t)). Qed.
Lemma lem5034020 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term264 A B x s f t) = (term265 A B x s f t).
Proof. exact (MK_COMB (@lem5034018 A B s x f t) (@lem5034019 A B s f t)). Qed.
Lemma lem5034021 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term266 A B s f t) = (term267 A B s f t).
Proof. exact (fun_ext (fun x : B -> A => @lem5034020 A B x s f t)). Qed.
Lemma lem5034022 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem5034023 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term255 A B s f t) = (term268 A B s f t).
Proof. exact (MK_COMB (@lem5034022 A B) (@lem5034021 A B s f t)). Qed.
Lemma lem5034024 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : ((term254 A B s f t) = (term255 A B s f t)) = ((term249 A B s f t) = (term268 A B s f t)).
Proof. exact (MK_COMB (@lem5034015 A B s f t) (@lem5034023 A B s f t)). Qed.
Lemma lem5034025 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term249 A B s f t) = (term268 A B s f t).
Proof. exact (EQ_MP (@lem5034024 A B s f t) (@lem5034005 A B s f t)). Qed.
Lemma lem5034027 {A : Type'} (P : Prop) (Q : A -> Prop) : (term269 A P Q) = (term270 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5034028 {A B : Type'} (P : Prop) (Q : type805 A B) : (term271 A B P Q) = (term272 A B P Q).
Proof. exact (@lem5034027 (B -> A) P Q). Qed.
Lemma lem5034029 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term273 A B x s f t) = (term274 A B x s f t).
Proof. exact (@lem5034028 A B (term210 A B s x f t) (term247 A B s f t)). Qed.
Lemma lem5034030 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x : B -> A) : (term275 A B s f t x) = (term245 A B s f t x).
Proof. exact (eq_refl (term275 A B s f t x)). Qed.
Lemma lem5034031 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term276 A B s f t) = (term247 A B s f t).
Proof. exact (fun_ext (fun x : B -> A => @lem5034030 A B s f t x)). Qed.
Lemma lem5034032 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem5034033 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term277 A B s f t) = (term248 A B s f t).
Proof. exact (MK_COMB (@lem5034032 A B) (@lem5034031 A B s f t)). Qed.
Lemma lem5034034 {A B : Type'} (s : A -> Prop) (x : B -> A) (f : A -> B) (t : A -> Prop) : (term263 A B s x f t) = (term263 A B s x f t).
Proof. exact (eq_refl (term263 A B s x f t)). Qed.
Lemma lem5034035 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term273 A B x s f t) = (term265 A B x s f t).
Proof. exact (MK_COMB (@lem5034034 A B s x f t) (@lem5034033 A B s f t)). Qed.
Lemma lem5034036 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5034037 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term278 A B x s f t) = (term279 A B x s f t).
Proof. exact (MK_COMB (@lem5034036) (@lem5034035 A B x s f t)). Qed.
Lemma lem5034038 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x' : B -> A) : (term275 A B s f t x') = (term245 A B s f t x').
Proof. exact (eq_refl (term275 A B s f t x')). Qed.
Lemma lem5034039 {A B : Type'} (s : A -> Prop) (x : B -> A) (f : A -> B) (t : A -> Prop) : (term263 A B s x f t) = (term263 A B s x f t).
Proof. exact (eq_refl (term263 A B s x f t)). Qed.
Lemma lem5034040 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x' : B -> A) : (term280 A B x s f t x') = (term281 A B x s f t x').
Proof. exact (MK_COMB (@lem5034039 A B s x f t) (@lem5034038 A B s f t x')). Qed.
Lemma lem5034041 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term282 A B x s f t) = (term283 A B x s f t).
Proof. exact (fun_ext (fun x' : B -> A => @lem5034040 A B x s f t x')). Qed.
Lemma lem5034042 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem5034043 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term274 A B x s f t) = (term284 A B x s f t).
Proof. exact (MK_COMB (@lem5034042 A B) (@lem5034041 A B x s f t)). Qed.
Lemma lem5034044 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : ((term273 A B x s f t) = (term274 A B x s f t)) = ((term265 A B x s f t) = (term284 A B x s f t)).
Proof. exact (MK_COMB (@lem5034037 A B x s f t) (@lem5034043 A B x s f t)). Qed.
Lemma lem5034045 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term265 A B x s f t) = (term284 A B x s f t).
Proof. exact (EQ_MP (@lem5034044 A B x s f t) (@lem5034029 A B x s f t)). Qed.
Lemma lem5034046 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term267 A B s f t) = (term285 A B s f t).
Proof. exact (fun_ext (fun x : B -> A => @lem5034045 A B x s f t)). Qed.
Lemma lem5034047 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem5034048 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term268 A B s f t) = (term286 A B s f t).
Proof. exact (MK_COMB (@lem5034047 A B) (@lem5034046 A B s f t)). Qed.
Lemma lem5034049 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term249 A B s f t) = (term286 A B s f t).
Proof. exact (TRANS (@lem5034025 A B s f t) (@lem5034048 A B s f t)). Qed.
Lemma lem5034050 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term168 A B s f t) = (term286 A B s f t).
Proof. exact (TRANS (@lem5034001 A B s f t) (@lem5034049 A B s f t)). Qed.
Lemma lem5034051 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term144 A t u) = (term144 A t u).
Proof. exact (eq_refl (term144 A t u)). Qed.
Lemma lem5034052 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term169 A B u s f t) = (term287 A B u s f t).
Proof. exact (MK_COMB (@lem5034051 A t u) (@lem5034050 A B s f t)). Qed.
Lemma lem5034054 {A : Type'} (P : Prop) (Q : A -> Prop) : (term269 A P Q) = (term270 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5034055 {A B : Type'} (P : Prop) (Q : type805 A B) : (term271 A B P Q) = (term272 A B P Q).
Proof. exact (@lem5034054 (B -> A) P Q). Qed.
Lemma lem5034056 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term288 A B u s f t) = (term289 A B u s f t).
Proof. exact (@lem5034055 A B (term119 A t u) (term285 A B s f t)). Qed.
Lemma lem5034057 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term290 A B s f t x) = (term284 A B x s f t).
Proof. exact (eq_refl (term290 A B s f t x)). Qed.
Lemma lem5034058 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term291 A B s f t) = (term285 A B s f t).
Proof. exact (fun_ext (fun x : B -> A => @lem5034057 A B x s f t)). Qed.
Lemma lem5034059 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem5034060 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term292 A B s f t) = (term286 A B s f t).
Proof. exact (MK_COMB (@lem5034059 A B) (@lem5034058 A B s f t)). Qed.
Lemma lem5034061 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term144 A t u) = (term144 A t u).
Proof. exact (eq_refl (term144 A t u)). Qed.
Lemma lem5034062 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term288 A B u s f t) = (term287 A B u s f t).
Proof. exact (MK_COMB (@lem5034061 A t u) (@lem5034060 A B s f t)). Qed.
Lemma lem5034063 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5034064 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term293 A B u s f t) = (term294 A B u s f t).
Proof. exact (MK_COMB (@lem5034063) (@lem5034062 A B u s f t)). Qed.
Lemma lem5034065 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term290 A B s f t x) = (term284 A B x s f t).
Proof. exact (eq_refl (term290 A B s f t x)). Qed.
Lemma lem5034066 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term144 A t u) = (term144 A t u).
Proof. exact (eq_refl (term144 A t u)). Qed.
Lemma lem5034067 {A B : Type'} (u : A -> Prop) (x : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term295 A B u s f t x) = (term296 A B u x s f t).
Proof. exact (MK_COMB (@lem5034066 A t u) (@lem5034065 A B x s f t)). Qed.
Lemma lem5034068 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term297 A B u s f t) = (term298 A B u s f t).
Proof. exact (fun_ext (fun x : B -> A => @lem5034067 A B u x s f t)). Qed.
Lemma lem5034069 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem5034070 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term289 A B u s f t) = (term299 A B u s f t).
Proof. exact (MK_COMB (@lem5034069 A B) (@lem5034068 A B u s f t)). Qed.
Lemma lem5034071 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : ((term288 A B u s f t) = (term289 A B u s f t)) = ((term287 A B u s f t) = (term299 A B u s f t)).
Proof. exact (MK_COMB (@lem5034064 A B u s f t) (@lem5034070 A B u s f t)). Qed.
Lemma lem5034072 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term287 A B u s f t) = (term299 A B u s f t).
Proof. exact (EQ_MP (@lem5034071 A B u s f t) (@lem5034056 A B u s f t)). Qed.
Lemma lem5034074 {A : Type'} (P : Prop) (Q : A -> Prop) : (term269 A P Q) = (term270 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5034075 {A B : Type'} (P : Prop) (Q : type805 A B) : (term271 A B P Q) = (term272 A B P Q).
Proof. exact (@lem5034074 (B -> A) P Q). Qed.
Lemma lem5034076 {A B : Type'} (u : A -> Prop) (x : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term300 A B u x s f t) = (term301 A B u x s f t).
Proof. exact (@lem5034075 A B (term119 A t u) (term283 A B x s f t)). Qed.
Lemma lem5034077 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x' : B -> A) : (term302 A B x s f t x') = (term281 A B x s f t x').
Proof. exact (eq_refl (term302 A B x s f t x')). Qed.
Lemma lem5034078 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term303 A B x s f t) = (term283 A B x s f t).
Proof. exact (fun_ext (fun x' : B -> A => @lem5034077 A B x s f t x')). Qed.
Lemma lem5034079 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem5034080 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term304 A B x s f t) = (term284 A B x s f t).
Proof. exact (MK_COMB (@lem5034079 A B) (@lem5034078 A B x s f t)). Qed.
Lemma lem5034081 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term144 A t u) = (term144 A t u).
Proof. exact (eq_refl (term144 A t u)). Qed.
Lemma lem5034082 {A B : Type'} (u : A -> Prop) (x : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term300 A B u x s f t) = (term296 A B u x s f t).
Proof. exact (MK_COMB (@lem5034081 A t u) (@lem5034080 A B x s f t)). Qed.
Lemma lem5034083 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5034084 {A B : Type'} (u : A -> Prop) (x : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term305 A B u x s f t) = (term306 A B u x s f t).
Proof. exact (MK_COMB (@lem5034083) (@lem5034082 A B u x s f t)). Qed.
Lemma lem5034085 {A B : Type'} (x : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x' : B -> A) : (term302 A B x s f t x') = (term281 A B x s f t x').
Proof. exact (eq_refl (term302 A B x s f t x')). Qed.
Lemma lem5034086 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term144 A t u) = (term144 A t u).
Proof. exact (eq_refl (term144 A t u)). Qed.
Lemma lem5034087 {A B : Type'} (u : A -> Prop) (x : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x' : B -> A) : (term307 A B u x s f t x') = (term308 A B u x s f t x').
Proof. exact (MK_COMB (@lem5034086 A t u) (@lem5034085 A B x s f t x')). Qed.
Lemma lem5034088 {A B : Type'} (u : A -> Prop) (x : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term309 A B u x s f t) = (term310 A B u x s f t).
Proof. exact (fun_ext (fun x' : B -> A => @lem5034087 A B u x s f t x')). Qed.
Lemma lem5034089 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem5034090 {A B : Type'} (u : A -> Prop) (x : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term301 A B u x s f t) = (term311 A B u x s f t).
Proof. exact (MK_COMB (@lem5034089 A B) (@lem5034088 A B u x s f t)). Qed.
Lemma lem5034091 {A B : Type'} (u : A -> Prop) (x : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : ((term300 A B u x s f t) = (term301 A B u x s f t)) = ((term296 A B u x s f t) = (term311 A B u x s f t)).
Proof. exact (MK_COMB (@lem5034084 A B u x s f t) (@lem5034090 A B u x s f t)). Qed.
Lemma lem5034092 {A B : Type'} (u : A -> Prop) (x : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term296 A B u x s f t) = (term311 A B u x s f t).
Proof. exact (EQ_MP (@lem5034091 A B u x s f t) (@lem5034076 A B u x s f t)). Qed.
Lemma lem5034093 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term298 A B u s f t) = (term312 A B u s f t).
Proof. exact (fun_ext (fun x : B -> A => @lem5034092 A B u x s f t)). Qed.
Lemma lem5034094 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem5034095 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term299 A B u s f t) = (term313 A B u s f t).
Proof. exact (MK_COMB (@lem5034094 A B) (@lem5034093 A B u s f t)). Qed.
Lemma lem5034096 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term287 A B u s f t) = (term313 A B u s f t).
Proof. exact (TRANS (@lem5034072 A B u s f t) (@lem5034095 A B u s f t)). Qed.
Lemma lem5034097 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term169 A B u s f t) = (term313 A B u s f t).
Proof. exact (TRANS (@lem5034052 A B u s f t) (@lem5034096 A B u s f t)). Qed.
Lemma lem5034098 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term144 A s u) = (term144 A s u).
Proof. exact (eq_refl (term144 A s u)). Qed.
Lemma lem5034099 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term170 A B u s f t) = (term314 A B u s f t).
Proof. exact (MK_COMB (@lem5034098 A s u) (@lem5034097 A B u s f t)). Qed.
Lemma lem5034101 {A : Type'} (P : Prop) (Q : A -> Prop) : (term269 A P Q) = (term270 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5034102 {A B : Type'} (P : Prop) (Q : type805 A B) : (term271 A B P Q) = (term272 A B P Q).
Proof. exact (@lem5034101 (B -> A) P Q). Qed.
Lemma lem5034103 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term315 A B u s f t) = (term316 A B u s f t).
Proof. exact (@lem5034102 A B (term119 A s u) (term312 A B u s f t)). Qed.
Lemma lem5034104 {A B : Type'} (u : A -> Prop) (x : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term317 A B u s f t x) = (term311 A B u x s f t).
Proof. exact (eq_refl (term317 A B u s f t x)). Qed.
Lemma lem5034105 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term318 A B u s f t) = (term312 A B u s f t).
Proof. exact (fun_ext (fun x : B -> A => @lem5034104 A B u x s f t)). Qed.
Lemma lem5034106 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem5034107 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term319 A B u s f t) = (term313 A B u s f t).
Proof. exact (MK_COMB (@lem5034106 A B) (@lem5034105 A B u s f t)). Qed.
Lemma lem5034108 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term144 A s u) = (term144 A s u).
Proof. exact (eq_refl (term144 A s u)). Qed.
Lemma lem5034109 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term315 A B u s f t) = (term314 A B u s f t).
Proof. exact (MK_COMB (@lem5034108 A s u) (@lem5034107 A B u s f t)). Qed.
Lemma lem5034110 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5034111 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term320 A B u s f t) = (term321 A B u s f t).
Proof. exact (MK_COMB (@lem5034110) (@lem5034109 A B u s f t)). Qed.
Lemma lem5034112 {A B : Type'} (u : A -> Prop) (x : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term317 A B u s f t x) = (term311 A B u x s f t).
Proof. exact (eq_refl (term317 A B u s f t x)). Qed.
Lemma lem5034113 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term144 A s u) = (term144 A s u).
Proof. exact (eq_refl (term144 A s u)). Qed.
Lemma lem5034114 {A B : Type'} (u : A -> Prop) (x : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term322 A B u s f t x) = (term323 A B u x s f t).
Proof. exact (MK_COMB (@lem5034113 A s u) (@lem5034112 A B u x s f t)). Qed.
Lemma lem5034115 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term324 A B u s f t) = (term325 A B u s f t).
Proof. exact (fun_ext (fun x : B -> A => @lem5034114 A B u x s f t)). Qed.
Lemma lem5034116 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem5034117 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term316 A B u s f t) = (term326 A B u s f t).
Proof. exact (MK_COMB (@lem5034116 A B) (@lem5034115 A B u s f t)). Qed.
Lemma lem5034118 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : ((term315 A B u s f t) = (term316 A B u s f t)) = ((term314 A B u s f t) = (term326 A B u s f t)).
Proof. exact (MK_COMB (@lem5034111 A B u s f t) (@lem5034117 A B u s f t)). Qed.
Lemma lem5034119 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term314 A B u s f t) = (term326 A B u s f t).
Proof. exact (EQ_MP (@lem5034118 A B u s f t) (@lem5034103 A B u s f t)). Qed.
Lemma lem5034121 {A : Type'} (P : Prop) (Q : A -> Prop) : (term269 A P Q) = (term270 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5034122 {A B : Type'} (P : Prop) (Q : type805 A B) : (term271 A B P Q) = (term272 A B P Q).
Proof. exact (@lem5034121 (B -> A) P Q). Qed.
Lemma lem5034123 {A B : Type'} (u : A -> Prop) (x : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term327 A B u x s f t) = (term328 A B u x s f t).
Proof. exact (@lem5034122 A B (term119 A s u) (term310 A B u x s f t)). Qed.
Lemma lem5034124 {A B : Type'} (u : A -> Prop) (x : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x' : B -> A) : (term329 A B u x s f t x') = (term308 A B u x s f t x').
Proof. exact (eq_refl (term329 A B u x s f t x')). Qed.
Lemma lem5034125 {A B : Type'} (u : A -> Prop) (x : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term330 A B u x s f t) = (term310 A B u x s f t).
Proof. exact (fun_ext (fun x' : B -> A => @lem5034124 A B u x s f t x')). Qed.
Lemma lem5034126 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem5034127 {A B : Type'} (u : A -> Prop) (x : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term331 A B u x s f t) = (term311 A B u x s f t).
Proof. exact (MK_COMB (@lem5034126 A B) (@lem5034125 A B u x s f t)). Qed.
Lemma lem5034128 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term144 A s u) = (term144 A s u).
Proof. exact (eq_refl (term144 A s u)). Qed.
Lemma lem5034129 {A B : Type'} (u : A -> Prop) (x : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term327 A B u x s f t) = (term323 A B u x s f t).
Proof. exact (MK_COMB (@lem5034128 A s u) (@lem5034127 A B u x s f t)). Qed.
Lemma lem5034130 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5034131 {A B : Type'} (u : A -> Prop) (x : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term332 A B u x s f t) = (term333 A B u x s f t).
Proof. exact (MK_COMB (@lem5034130) (@lem5034129 A B u x s f t)). Qed.
Lemma lem5034132 {A B : Type'} (u : A -> Prop) (x : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x' : B -> A) : (term329 A B u x s f t x') = (term308 A B u x s f t x').
Proof. exact (eq_refl (term329 A B u x s f t x')). Qed.
Lemma lem5034133 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term144 A s u) = (term144 A s u).
Proof. exact (eq_refl (term144 A s u)). Qed.
Lemma lem5034134 {A B : Type'} (u : A -> Prop) (x : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x' : B -> A) : (term334 A B u x s f t x') = (term335 A B u x s f t x').
Proof. exact (MK_COMB (@lem5034133 A s u) (@lem5034132 A B u x s f t x')). Qed.
Lemma lem5034135 {A B : Type'} (u : A -> Prop) (x : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term336 A B u x s f t) = (term337 A B u x s f t).
Proof. exact (fun_ext (fun x' : B -> A => @lem5034134 A B u x s f t x')). Qed.
Lemma lem5034136 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem5034137 {A B : Type'} (u : A -> Prop) (x : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term328 A B u x s f t) = (term338 A B u x s f t).
Proof. exact (MK_COMB (@lem5034136 A B) (@lem5034135 A B u x s f t)). Qed.
Lemma lem5034138 {A B : Type'} (u : A -> Prop) (x : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : ((term327 A B u x s f t) = (term328 A B u x s f t)) = ((term323 A B u x s f t) = (term338 A B u x s f t)).
Proof. exact (MK_COMB (@lem5034131 A B u x s f t) (@lem5034137 A B u x s f t)). Qed.
Lemma lem5034139 {A B : Type'} (u : A -> Prop) (x : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term323 A B u x s f t) = (term338 A B u x s f t).
Proof. exact (EQ_MP (@lem5034138 A B u x s f t) (@lem5034123 A B u x s f t)). Qed.
Lemma lem5034140 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term325 A B u s f t) = (term339 A B u s f t).
Proof. exact (fun_ext (fun x : B -> A => @lem5034139 A B u x s f t)). Qed.
Lemma lem5034141 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem5034142 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term326 A B u s f t) = (term340 A B u s f t).
Proof. exact (MK_COMB (@lem5034141 A B) (@lem5034140 A B u s f t)). Qed.
Lemma lem5034143 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term314 A B u s f t) = (term340 A B u s f t).
Proof. exact (TRANS (@lem5034119 A B u s f t) (@lem5034142 A B u s f t)). Qed.
Lemma lem5034144 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term170 A B u s f t) = (term340 A B u s f t).
Proof. exact (TRANS (@lem5034099 A B u s f t) (@lem5034143 A B u s f t)). Qed.
Lemma lem5034145 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term146 A B u s f t) = (term340 A B u s f t).
Proof. exact (TRANS (@lem5033886 A B u s f t) (@lem5034144 A B u s f t)). Qed.
Lemma lem5034146 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term72 A B u s f t) = (term340 A B u s f t).
Proof. exact (TRANS (@lem5033535 A B u s f t) (@lem5034145 A B u s f t)). Qed.
Lemma lem5034147 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term72 A B u s f t) : term340 A B u s f t.
Proof. exact (EQ_MP (@lem5034146 A B u s f t) (@lem5033358 A B u s f t h1)). Qed.
Lemma lem5034166 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term102 A s t x) = (term341 A s t x).
Proof. exact (@lem17646 (s x) (t x)). Qed.
Lemma lem5034168 {A B : Type'} (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term338 A B u x' s f t) : term338 A B u x' s f t.
Proof. exact (h1). Qed.
Lemma lem5034169 {A B : Type'} (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term335 A B u x' s f t x''.
Proof. exact (h1). Qed.
Lemma lem5034204 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (y : A) : (term112 A B u f x y) = (term112 A B u f x y).
Proof. exact (eq_refl (term112 A B u f x y)). Qed.
Lemma lem5034205 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) : (term113 A B u f x) = (term113 A B u f x).
Proof. exact (fun_ext (fun y : A => @lem5034204 A B u f x y)). Qed.
Lemma lem5034206 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5034207 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) : (term114 A B u f x) = (term114 A B u f x).
Proof. exact (MK_COMB (@lem5034206 A) (@lem5034205 A B u f x)). Qed.
Lemma lem5034208 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term115 A B u f) = (term115 A B u f).
Proof. exact (fun_ext (fun x : A => @lem5034207 A B u f x)). Qed.
Lemma lem5034209 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5034210 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term116 A B u f) = (term116 A B u f).
Proof. exact (MK_COMB (@lem5034209 A) (@lem5034208 A B u f)). Qed.
Lemma lem5034211 {A B : Type'} (u : A -> Prop) (f : A -> B) (h1 : term48 A B u f) : term116 A B u f.
Proof. exact (EQ_MP (@lem5034210 A B u f) (@lem5033445 A B u f h1)). Qed.
Lemma lem5034237 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term102 A s t x) : term341 A s t x.
Proof. exact (EQ_MP (@lem5034166 A s t x) (@lem5033363 A s t x h1)). Qed.
Lemma lem5034254 {A B : Type'} (f : A -> B) (t : A -> Prop) (x'' : B -> A) (x : B) : (term342 A B f t x'' x) = (term342 A B f t x'' x).
Proof. exact (eq_refl (term342 A B f t x'' x)). Qed.
Lemma lem5034271 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term121 A B x f s x') = (term121 A B x f s x').
Proof. exact (eq_refl (term121 A B x f s x')). Qed.
Lemma lem5034272 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term129 A B x f s) = (term129 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem5034271 A B x f s x')). Qed.
Lemma lem5034273 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5034274 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term130 A B x f s) = (term130 A B x f s).
Proof. exact (MK_COMB (@lem5034273 A) (@lem5034272 A B x f s)). Qed.
Lemma lem5034275 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5034276 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term132 A B x f s) = (term132 A B x f s).
Proof. exact (MK_COMB (@lem5034275) (@lem5034274 A B x f s)). Qed.
Lemma lem5034277 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (x : B) : (term241 A B s f t x'' x) = (term241 A B s f t x'' x).
Proof. exact (MK_COMB (@lem5034276 A B x f s) (@lem5034254 A B f t x'' x)). Qed.
Lemma lem5034278 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) : (term243 A B s f t x'') = (term243 A B s f t x'').
Proof. exact (fun_ext (fun x : B => @lem5034277 A B s f t x'' x)). Qed.
Lemma lem5034279 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5034280 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) : (term245 A B s f t x'') = (term245 A B s f t x'').
Proof. exact (MK_COMB (@lem5034279 B) (@lem5034278 A B s f t x'')). Qed.
Lemma lem5034297 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term121 A B x f t x') = (term121 A B x f t x').
Proof. exact (eq_refl (term121 A B x f t x')). Qed.
Lemma lem5034298 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term129 A B x f t) = (term129 A B x f t).
Proof. exact (fun_ext (fun x' : A => @lem5034297 A B x f t x')). Qed.
Lemma lem5034299 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5034300 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term130 A B x f t) = (term130 A B x f t).
Proof. exact (MK_COMB (@lem5034299 A) (@lem5034298 A B x f t)). Qed.
Lemma lem5034319 {A B : Type'} (f : A -> B) (s : A -> Prop) (x' : B -> A) (x : B) : (term343 A B f s x' x) = (term343 A B f s x' x).
Proof. exact (eq_refl (term343 A B f s x' x)). Qed.
Lemma lem5034320 {A B : Type'} (s : A -> Prop) (x' : B -> A) (x : B) (f : A -> B) (t : A -> Prop) : (term206 A B s x' x f t) = (term206 A B s x' x f t).
Proof. exact (MK_COMB (@lem5034319 A B f s x' x) (@lem5034300 A B x f t)). Qed.
Lemma lem5034321 {A B : Type'} (s : A -> Prop) (x' : B -> A) (f : A -> B) (t : A -> Prop) : (term208 A B s x' f t) = (term208 A B s x' f t).
Proof. exact (fun_ext (fun x : B => @lem5034320 A B s x' x f t)). Qed.
Lemma lem5034322 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5034323 {A B : Type'} (s : A -> Prop) (x' : B -> A) (f : A -> B) (t : A -> Prop) : (term210 A B s x' f t) = (term210 A B s x' f t).
Proof. exact (MK_COMB (@lem5034322 B) (@lem5034321 A B s x' f t)). Qed.
Lemma lem5034324 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5034325 {A B : Type'} (s : A -> Prop) (x' : B -> A) (f : A -> B) (t : A -> Prop) : (term263 A B s x' f t) = (term263 A B s x' f t).
Proof. exact (MK_COMB (@lem5034324) (@lem5034323 A B s x' f t)). Qed.
Lemma lem5034326 {A B : Type'} (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) : (term281 A B x' s f t x'') = (term281 A B x' s f t x'').
Proof. exact (MK_COMB (@lem5034325 A B s x' f t) (@lem5034280 A B s f t x'')). Qed.
Lemma lem5034337 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term117 A t u x) = (term117 A t u x).
Proof. exact (eq_refl (term117 A t u x)). Qed.
Lemma lem5034338 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term118 A t u) = (term118 A t u).
Proof. exact (fun_ext (fun x : A => @lem5034337 A t u x)). Qed.
Lemma lem5034339 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5034340 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term119 A t u) = (term119 A t u).
Proof. exact (MK_COMB (@lem5034339 A) (@lem5034338 A t u)). Qed.
Lemma lem5034341 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5034342 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term144 A t u) = (term144 A t u).
Proof. exact (MK_COMB (@lem5034341) (@lem5034340 A t u)). Qed.
Lemma lem5034343 {A B : Type'} (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) : (term308 A B u x' s f t x'') = (term308 A B u x' s f t x'').
Proof. exact (MK_COMB (@lem5034342 A t u) (@lem5034326 A B x' s f t x'')). Qed.
Lemma lem5034354 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term117 A s u x) = (term117 A s u x).
Proof. exact (eq_refl (term117 A s u x)). Qed.
Lemma lem5034355 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term118 A s u) = (term118 A s u).
Proof. exact (fun_ext (fun x : A => @lem5034354 A s u x)). Qed.
Lemma lem5034356 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5034357 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term119 A s u) = (term119 A s u).
Proof. exact (MK_COMB (@lem5034356 A) (@lem5034355 A s u)). Qed.
Lemma lem5034358 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5034359 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term144 A s u) = (term144 A s u).
Proof. exact (MK_COMB (@lem5034358) (@lem5034357 A s u)). Qed.
Lemma lem5034360 {A B : Type'} (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) : (term335 A B u x' s f t x'') = (term335 A B u x' s f t x'').
Proof. exact (MK_COMB (@lem5034359 A s u) (@lem5034343 A B u x' s f t x'')). Qed.
Lemma lem5034361 {A B : Type'} (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term335 A B u x' s f t x''.
Proof. exact (EQ_MP (@lem5034360 A B u x' s f t x'') (@lem5034169 A B u x' s f t x'' h1)). Qed.
Lemma lem5034362 {A B : Type'} (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term308 A B u x' s f t x''.
Proof. exact (proj2 (@lem5034361 A B u x' s f t x'' h1)). Qed.
Lemma lem5034363 {A B : Type'} (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term119 A s u.
Proof. exact (proj1 (@lem5034361 A B u x' s f t x'' h1)). Qed.
Lemma lem5034364 {A B : Type'} (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term281 A B x' s f t x''.
Proof. exact (proj2 (@lem5034362 A B u x' s f t x'' h1)). Qed.
Lemma lem5034365 {A B : Type'} (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term119 A t u.
Proof. exact (proj1 (@lem5034362 A B u x' s f t x'' h1)). Qed.
Lemma lem5034366 {A B : Type'} (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term245 A B s f t x''.
Proof. exact (proj2 (@lem5034364 A B u x' s f t x'' h1)). Qed.
Lemma lem5034367 {A B : Type'} (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term210 A B s x' f t.
Proof. exact (proj1 (@lem5034364 A B u x' s f t x'' h1)). Qed.
Lemma lem5034368 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term344 A s t x) : term344 A s t x.
Proof. exact (h1). Qed.
Lemma lem5034369 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term345 A s t x) : term345 A s t x.
Proof. exact (h1). Qed.
Lemma lem5034393 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (y : A) : (term112 A B u f x y) = (term112 A B u f x y).
Proof. exact (eq_refl (term112 A B u f x y)). Qed.
Lemma lem5034394 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) : (term113 A B u f x) = (term113 A B u f x).
Proof. exact (fun_ext (fun y : A => @lem5034393 A B u f x y)). Qed.
Lemma lem5034395 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5034396 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) : (term114 A B u f x) = (term114 A B u f x).
Proof. exact (MK_COMB (@lem5034395 A) (@lem5034394 A B u f x)). Qed.
Lemma lem5034397 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term115 A B u f) = (term115 A B u f).
Proof. exact (fun_ext (fun x : A => @lem5034396 A B u f x)). Qed.
Lemma lem5034398 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5034400 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term116 A B u f) = (term116 A B u f).
Proof. exact (MK_COMB (@lem5034398 A) (@lem5034397 A B u f)). Qed.
Lemma lem5034401 {A B : Type'} (u : A -> Prop) (f : A -> B) (h1 : term48 A B u f) : term116 A B u f.
Proof. exact (EQ_MP (@lem5034400 A B u f) (@lem5034211 A B u f h1)). Qed.
Lemma lem5034409 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term117 A s u x) = (term117 A s u x).
Proof. exact (eq_refl (term117 A s u x)). Qed.
Lemma lem5034410 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term118 A s u) = (term118 A s u).
Proof. exact (fun_ext (fun x : A => @lem5034409 A s u x)). Qed.
Lemma lem5034411 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5034413 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term119 A s u) = (term119 A s u).
Proof. exact (MK_COMB (@lem5034411 A) (@lem5034410 A s u)). Qed.
Lemma lem5034414 {A B : Type'} (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term119 A s u.
Proof. exact (EQ_MP (@lem5034413 A s u) (@lem5034363 A B u x' s f t x'' h1)). Qed.
Lemma lem5034422 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term117 A t u x) = (term117 A t u x).
Proof. exact (eq_refl (term117 A t u x)). Qed.
Lemma lem5034423 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term118 A t u) = (term118 A t u).
Proof. exact (fun_ext (fun x : A => @lem5034422 A t u x)). Qed.
Lemma lem5034424 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5034426 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term119 A t u) = (term119 A t u).
Proof. exact (MK_COMB (@lem5034424 A) (@lem5034423 A t u)). Qed.
Lemma lem5034427 {A B : Type'} (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term119 A t u.
Proof. exact (EQ_MP (@lem5034426 A t u) (@lem5034365 A B u x' s f t x'' h1)). Qed.
Lemma lem5034483 {A : Type'} (P : A -> Prop) (Q : Prop) : (term346 A P Q) = (term347 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem5034484 {A : Type'} (P : A -> Prop) (Q : Prop) : (term346 A P Q) = (term347 A P Q).
Proof. exact (@lem5034483 A P Q). Qed.
Lemma lem5034485 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (x : B) : (term348 A B s f t x'' x) = (term349 A B s f t x'' x).
Proof. exact (@lem5034484 A (term129 A B x f s) (term342 A B f t x'' x)). Qed.
Lemma lem5034486 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term350 A B x f s x') = (term121 A B x f s x').
Proof. exact (eq_refl (term350 A B x f s x')). Qed.
Lemma lem5034487 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term351 A B x f s) = (term129 A B x f s).
Proof. exact (fun_ext (fun x' : A => @lem5034486 A B x f s x')). Qed.
Lemma lem5034488 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5034489 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term352 A B x f s) = (term130 A B x f s).
Proof. exact (MK_COMB (@lem5034488 A) (@lem5034487 A B x f s)). Qed.
Lemma lem5034490 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5034491 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term353 A B x f s) = (term132 A B x f s).
Proof. exact (MK_COMB (@lem5034490) (@lem5034489 A B x f s)). Qed.
Lemma lem5034492 {A B : Type'} (f : A -> B) (t : A -> Prop) (x'' : B -> A) (x : B) : (term342 A B f t x'' x) = (term342 A B f t x'' x).
Proof. exact (eq_refl (term342 A B f t x'' x)). Qed.
Lemma lem5034493 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (x : B) : (term348 A B s f t x'' x) = (term241 A B s f t x'' x).
Proof. exact (MK_COMB (@lem5034491 A B x f s) (@lem5034492 A B f t x'' x)). Qed.
Lemma lem5034494 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5034495 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (x : B) : (term354 A B s f t x'' x) = (term355 A B s f t x'' x).
Proof. exact (MK_COMB (@lem5034494) (@lem5034493 A B s f t x'' x)). Qed.
Lemma lem5034496 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term350 A B x f s x') = (term121 A B x f s x').
Proof. exact (eq_refl (term350 A B x f s x')). Qed.
Lemma lem5034497 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5034498 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term356 A B x f s x') = (term357 A B x f s x').
Proof. exact (MK_COMB (@lem5034497) (@lem5034496 A B x f s x')). Qed.
Lemma lem5034499 {A B : Type'} (f : A -> B) (t : A -> Prop) (x'' : B -> A) (x : B) : (term342 A B f t x'' x) = (term342 A B f t x'' x).
Proof. exact (eq_refl (term342 A B f t x'' x)). Qed.
Lemma lem5034500 {A B : Type'} (s : A -> Prop) (x : A) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (x' : B) : (term358 A B s x f t x'' x') = (term359 A B s x f t x'' x').
Proof. exact (MK_COMB (@lem5034498 A B x' f s x) (@lem5034499 A B f t x'' x')). Qed.
Lemma lem5034501 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (x : B) : (term360 A B s f t x'' x) = (term361 A B s f t x'' x).
Proof. exact (fun_ext (fun x' : A => @lem5034500 A B s x' f t x'' x)). Qed.
Lemma lem5034502 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5034503 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (x : B) : (term349 A B s f t x'' x) = (term362 A B s f t x'' x).
Proof. exact (MK_COMB (@lem5034502 A) (@lem5034501 A B s f t x'' x)). Qed.
Lemma lem5034504 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (x : B) : ((term348 A B s f t x'' x) = (term349 A B s f t x'' x)) = ((term241 A B s f t x'' x) = (term362 A B s f t x'' x)).
Proof. exact (MK_COMB (@lem5034495 A B s f t x'' x) (@lem5034503 A B s f t x'' x)). Qed.
Lemma lem5034505 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (x : B) : (term241 A B s f t x'' x) = (term362 A B s f t x'' x).
Proof. exact (EQ_MP (@lem5034504 A B s f t x'' x) (@lem5034485 A B s f t x'' x)). Qed.
Lemma lem5034506 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) : (term243 A B s f t x'') = (term363 A B s f t x'').
Proof. exact (fun_ext (fun x : B => @lem5034505 A B s f t x'' x)). Qed.
Lemma lem5034507 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5034508 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) : (term245 A B s f t x'') = (term364 A B s f t x'').
Proof. exact (MK_COMB (@lem5034507 B) (@lem5034506 A B s f t x'')). Qed.
Lemma lem5034531 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) (t : A -> Prop) (x'' : B -> A) (x' : B) : (term359 A B s x f t x'' x') = (term365 A B f s x t x'' x').
Proof. exact (@lem19490 (x' = (term366 A B f x'' x')) (term121 A B x' f s x) (term367 A B t x'' x')). Qed.
Lemma lem5034532 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x'' : B -> A) (x : B) : (term361 A B s f t x'' x) = (term368 A B f s t x'' x).
Proof. exact (fun_ext (fun x' : A => @lem5034531 A B f s x' t x'' x)). Qed.
Lemma lem5034533 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5034534 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x'' : B -> A) (x : B) : (term362 A B s f t x'' x) = (term369 A B f s t x'' x).
Proof. exact (MK_COMB (@lem5034533 A) (@lem5034532 A B f s t x'' x)). Qed.
Lemma lem5034535 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x'' : B -> A) : (term363 A B s f t x'') = (term370 A B f s t x'').
Proof. exact (fun_ext (fun x : B => @lem5034534 A B f s t x'' x)). Qed.
Lemma lem5034536 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5034537 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x'' : B -> A) : (term364 A B s f t x'') = (term371 A B f s t x'').
Proof. exact (MK_COMB (@lem5034536 B) (@lem5034535 A B f s t x'')). Qed.
Lemma lem5034538 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x'' : B -> A) : (term245 A B s f t x'') = (term371 A B f s t x'').
Proof. exact (TRANS (@lem5034508 A B s f t x'') (@lem5034537 A B f s t x'')). Qed.
Lemma lem5034539 {A B : Type'} (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term371 A B f s t x''.
Proof. exact (EQ_MP (@lem5034538 A B f s t x'') (@lem5034366 A B u x' s f t x'' h1)). Qed.
Lemma lem5034567 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (y : A) : (term112 A B u f x y) = (term112 A B u f x y).
Proof. exact (eq_refl (term112 A B u f x y)). Qed.
Lemma lem5034568 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) : (term113 A B u f x) = (term113 A B u f x).
Proof. exact (fun_ext (fun y : A => @lem5034567 A B u f x y)). Qed.
Lemma lem5034569 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5034570 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) : (term114 A B u f x) = (term114 A B u f x).
Proof. exact (MK_COMB (@lem5034569 A) (@lem5034568 A B u f x)). Qed.
Lemma lem5034571 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term115 A B u f) = (term115 A B u f).
Proof. exact (fun_ext (fun x : A => @lem5034570 A B u f x)). Qed.
Lemma lem5034572 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5034574 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term116 A B u f) = (term116 A B u f).
Proof. exact (MK_COMB (@lem5034572 A) (@lem5034571 A B u f)). Qed.
Lemma lem5034575 {A B : Type'} (u : A -> Prop) (f : A -> B) (h1 : term48 A B u f) : term116 A B u f.
Proof. exact (EQ_MP (@lem5034574 A B u f) (@lem5034211 A B u f h1)). Qed.
Lemma lem5034583 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term117 A s u x) = (term117 A s u x).
Proof. exact (eq_refl (term117 A s u x)). Qed.
Lemma lem5034584 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term118 A s u) = (term118 A s u).
Proof. exact (fun_ext (fun x : A => @lem5034583 A s u x)). Qed.
Lemma lem5034585 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5034587 {A : Type'} (s : A -> Prop) (u : A -> Prop) : (term119 A s u) = (term119 A s u).
Proof. exact (MK_COMB (@lem5034585 A) (@lem5034584 A s u)). Qed.
Lemma lem5034588 {A B : Type'} (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term119 A s u.
Proof. exact (EQ_MP (@lem5034587 A s u) (@lem5034363 A B u x' s f t x'' h1)). Qed.
Lemma lem5034596 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term117 A t u x) = (term117 A t u x).
Proof. exact (eq_refl (term117 A t u x)). Qed.
Lemma lem5034597 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term118 A t u) = (term118 A t u).
Proof. exact (fun_ext (fun x : A => @lem5034596 A t u x)). Qed.
Lemma lem5034598 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5034600 {A : Type'} (t : A -> Prop) (u : A -> Prop) : (term119 A t u) = (term119 A t u).
Proof. exact (MK_COMB (@lem5034598 A) (@lem5034597 A t u)). Qed.
Lemma lem5034601 {A B : Type'} (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term119 A t u.
Proof. exact (EQ_MP (@lem5034600 A t u) (@lem5034365 A B u x' s f t x'' h1)). Qed.
Lemma lem5034603 {A : Type'} (P : Prop) (Q : A -> Prop) : (term372 A P Q) = (term373 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5034604 {A : Type'} (P : Prop) (Q : A -> Prop) : (term372 A P Q) = (term373 A P Q).
Proof. exact (@lem5034603 A P Q). Qed.
Lemma lem5034605 {A B : Type'} (s : A -> Prop) (x' : B -> A) (x : B) (f : A -> B) (t : A -> Prop) : (term374 A B s x' x f t) = (term375 A B s x' x f t).
Proof. exact (@lem5034604 A (term342 A B f s x' x) (term129 A B x f t)). Qed.
Lemma lem5034606 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term350 A B x f t x') = (term121 A B x f t x').
Proof. exact (eq_refl (term350 A B x f t x')). Qed.
Lemma lem5034607 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term351 A B x f t) = (term129 A B x f t).
Proof. exact (fun_ext (fun x' : A => @lem5034606 A B x f t x')). Qed.
Lemma lem5034608 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5034609 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) : (term352 A B x f t) = (term130 A B x f t).
Proof. exact (MK_COMB (@lem5034608 A) (@lem5034607 A B x f t)). Qed.
Lemma lem5034610 {A B : Type'} (f : A -> B) (s : A -> Prop) (x' : B -> A) (x : B) : (term343 A B f s x' x) = (term343 A B f s x' x).
Proof. exact (eq_refl (term343 A B f s x' x)). Qed.
Lemma lem5034611 {A B : Type'} (s : A -> Prop) (x' : B -> A) (x : B) (f : A -> B) (t : A -> Prop) : (term374 A B s x' x f t) = (term206 A B s x' x f t).
Proof. exact (MK_COMB (@lem5034610 A B f s x' x) (@lem5034609 A B x f t)). Qed.
Lemma lem5034612 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5034613 {A B : Type'} (s : A -> Prop) (x' : B -> A) (x : B) (f : A -> B) (t : A -> Prop) : (term376 A B s x' x f t) = (term377 A B s x' x f t).
Proof. exact (MK_COMB (@lem5034612) (@lem5034611 A B s x' x f t)). Qed.
Lemma lem5034614 {A B : Type'} (x : B) (f : A -> B) (t : A -> Prop) (x' : A) : (term350 A B x f t x') = (term121 A B x f t x').
Proof. exact (eq_refl (term350 A B x f t x')). Qed.
Lemma lem5034615 {A B : Type'} (f : A -> B) (s : A -> Prop) (x' : B -> A) (x : B) : (term343 A B f s x' x) = (term343 A B f s x' x).
Proof. exact (eq_refl (term343 A B f s x' x)). Qed.
Lemma lem5034616 {A B : Type'} (s : A -> Prop) (x' : B -> A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) : (term378 A B s x' x f t x'') = (term379 A B s x' x f t x'').
Proof. exact (MK_COMB (@lem5034615 A B f s x' x) (@lem5034614 A B x f t x'')). Qed.
Lemma lem5034617 {A B : Type'} (s : A -> Prop) (x' : B -> A) (x : B) (f : A -> B) (t : A -> Prop) : (term380 A B s x' x f t) = (term381 A B s x' x f t).
Proof. exact (fun_ext (fun x'' : A => @lem5034616 A B s x' x f t x'')). Qed.
Lemma lem5034618 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5034619 {A B : Type'} (s : A -> Prop) (x' : B -> A) (x : B) (f : A -> B) (t : A -> Prop) : (term375 A B s x' x f t) = (term382 A B s x' x f t).
Proof. exact (MK_COMB (@lem5034618 A) (@lem5034617 A B s x' x f t)). Qed.
Lemma lem5034620 {A B : Type'} (s : A -> Prop) (x' : B -> A) (x : B) (f : A -> B) (t : A -> Prop) : ((term374 A B s x' x f t) = (term375 A B s x' x f t)) = ((term206 A B s x' x f t) = (term382 A B s x' x f t)).
Proof. exact (MK_COMB (@lem5034613 A B s x' x f t) (@lem5034619 A B s x' x f t)). Qed.
Lemma lem5034621 {A B : Type'} (s : A -> Prop) (x' : B -> A) (x : B) (f : A -> B) (t : A -> Prop) : (term206 A B s x' x f t) = (term382 A B s x' x f t).
Proof. exact (EQ_MP (@lem5034620 A B s x' x f t) (@lem5034605 A B s x' x f t)). Qed.
Lemma lem5034622 {A B : Type'} (s : A -> Prop) (x' : B -> A) (f : A -> B) (t : A -> Prop) : (term208 A B s x' f t) = (term383 A B s x' f t).
Proof. exact (fun_ext (fun x : B => @lem5034621 A B s x' x f t)). Qed.
Lemma lem5034623 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5034624 {A B : Type'} (s : A -> Prop) (x' : B -> A) (f : A -> B) (t : A -> Prop) : (term210 A B s x' f t) = (term384 A B s x' f t).
Proof. exact (MK_COMB (@lem5034623 B) (@lem5034622 A B s x' f t)). Qed.
Lemma lem5034647 {A B : Type'} (s : A -> Prop) (x' : B -> A) (x : B) (f : A -> B) (t : A -> Prop) (x'' : A) : (term379 A B s x' x f t x'') = (term385 A B s x' x f t x'').
Proof. exact (@lem19699 (x = (term366 A B f x' x)) (term367 A B s x' x) (term121 A B x f t x'')). Qed.
Lemma lem5034648 {A B : Type'} (s : A -> Prop) (x' : B -> A) (x : B) (f : A -> B) (t : A -> Prop) : (term381 A B s x' x f t) = (term386 A B s x' x f t).
Proof. exact (fun_ext (fun x'' : A => @lem5034647 A B s x' x f t x'')). Qed.
Lemma lem5034649 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5034650 {A B : Type'} (s : A -> Prop) (x' : B -> A) (x : B) (f : A -> B) (t : A -> Prop) : (term382 A B s x' x f t) = (term387 A B s x' x f t).
Proof. exact (MK_COMB (@lem5034649 A) (@lem5034648 A B s x' x f t)). Qed.
Lemma lem5034651 {A B : Type'} (s : A -> Prop) (x' : B -> A) (f : A -> B) (t : A -> Prop) : (term383 A B s x' f t) = (term388 A B s x' f t).
Proof. exact (fun_ext (fun x : B => @lem5034650 A B s x' x f t)). Qed.
Lemma lem5034652 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5034653 {A B : Type'} (s : A -> Prop) (x' : B -> A) (f : A -> B) (t : A -> Prop) : (term384 A B s x' f t) = (term389 A B s x' f t).
Proof. exact (MK_COMB (@lem5034652 B) (@lem5034651 A B s x' f t)). Qed.
Lemma lem5034654 {A B : Type'} (s : A -> Prop) (x' : B -> A) (f : A -> B) (t : A -> Prop) : (term210 A B s x' f t) = (term389 A B s x' f t).
Proof. exact (TRANS (@lem5034624 A B s x' f t) (@lem5034653 A B s x' f t)). Qed.
Lemma lem5034655 {A B : Type'} (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term389 A B s x' f t.
Proof. exact (EQ_MP (@lem5034654 A B s x' f t) (@lem5034367 A B u x' s f t x'' h1)). Qed.
Lemma lem5034722 {A B : Type'} (_64692 : A) (u : A -> Prop) (f : A -> B) (h1 : term48 A B u f) : term390 A B u f _64692.
Proof. exact (@lem5034401 A B u f h1 _64692). Qed.
Lemma lem5034723 {A B : Type'} (u : A -> Prop) (f : A -> B) (_64692 : A) : (term390 A B u f _64692) = (term114 A B u f _64692).
Proof. exact (eq_refl (term390 A B u f _64692)). Qed.
Lemma lem5034724 {A B : Type'} (_64692 : A) (u : A -> Prop) (f : A -> B) (h1 : term48 A B u f) : term114 A B u f _64692.
Proof. exact (EQ_MP (@lem5034723 A B u f _64692) (@lem5034722 A B _64692 u f h1)). Qed.
Lemma lem5034725 {A B : Type'} (_64692 : A) (_64693 : A) (u : A -> Prop) (f : A -> B) (h1 : term48 A B u f) : term391 A B u f _64692 _64693.
Proof. exact (@lem5034724 A B _64692 u f h1 _64693). Qed.
Lemma lem5034726 {A B : Type'} (u : A -> Prop) (f : A -> B) (_64692 : A) (_64693 : A) : (term391 A B u f _64692 _64693) = (term112 A B u f _64692 _64693).
Proof. exact (eq_refl (term391 A B u f _64692 _64693)). Qed.
Lemma lem5034727 {A B : Type'} (_64692 : A) (_64693 : A) (u : A -> Prop) (f : A -> B) (h1 : term48 A B u f) : term112 A B u f _64692 _64693.
Proof. exact (EQ_MP (@lem5034726 A B u f _64692 _64693) (@lem5034725 A B _64692 _64693 u f h1)). Qed.
Lemma lem5034728 {A B : Type'} (_64694 : A) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term392 A s u _64694.
Proof. exact (@lem5034414 A B u x' s f t x'' h1 _64694). Qed.
Lemma lem5034729 {A : Type'} (s : A -> Prop) (u : A -> Prop) (_64694 : A) : (term392 A s u _64694) = (term117 A s u _64694).
Proof. exact (eq_refl (term392 A s u _64694)). Qed.
Lemma lem5034731 {A B : Type'} (_64695 : A) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term392 A t u _64695.
Proof. exact (@lem5034427 A B u x' s f t x'' h1 _64695). Qed.
Lemma lem5034732 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_64695 : A) : (term392 A t u _64695) = (term117 A t u _64695).
Proof. exact (eq_refl (term392 A t u _64695)). Qed.
Lemma lem5034740 {A B : Type'} (_64698 : B) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term393 A B f s t x'' _64698.
Proof. exact (@lem5034539 A B u x' s f t x'' h1 _64698). Qed.
Lemma lem5034741 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x'' : B -> A) (_64698 : B) : (term393 A B f s t x'' _64698) = (term369 A B f s t x'' _64698).
Proof. exact (eq_refl (term393 A B f s t x'' _64698)). Qed.
Lemma lem5034742 {A B : Type'} (_64698 : B) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term369 A B f s t x'' _64698.
Proof. exact (EQ_MP (@lem5034741 A B f s t x'' _64698) (@lem5034740 A B _64698 u x' s f t x'' h1)). Qed.
Lemma lem5034743 {A B : Type'} (_64698 : B) (_64699 : A) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term394 A B f s t x'' _64698 _64699.
Proof. exact (@lem5034742 A B _64698 u x' s f t x'' h1 _64699). Qed.
Lemma lem5034744 {A B : Type'} (f : A -> B) (s : A -> Prop) (_64699 : A) (t : A -> Prop) (x'' : B -> A) (_64698 : B) : (term394 A B f s t x'' _64698 _64699) = (term365 A B f s _64699 t x'' _64698).
Proof. exact (eq_refl (term394 A B f s t x'' _64698 _64699)). Qed.
Lemma lem5034745 {A B : Type'} (_64699 : A) (_64698 : B) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term365 A B f s _64699 t x'' _64698.
Proof. exact (EQ_MP (@lem5034744 A B f s _64699 t x'' _64698) (@lem5034743 A B _64698 _64699 u x' s f t x'' h1)). Qed.
Lemma lem5034746 {A B : Type'} (_64700 : A) (u : A -> Prop) (f : A -> B) (h1 : term48 A B u f) : term390 A B u f _64700.
Proof. exact (@lem5034575 A B u f h1 _64700). Qed.
Lemma lem5034747 {A B : Type'} (u : A -> Prop) (f : A -> B) (_64700 : A) : (term390 A B u f _64700) = (term114 A B u f _64700).
Proof. exact (eq_refl (term390 A B u f _64700)). Qed.
Lemma lem5034748 {A B : Type'} (_64700 : A) (u : A -> Prop) (f : A -> B) (h1 : term48 A B u f) : term114 A B u f _64700.
Proof. exact (EQ_MP (@lem5034747 A B u f _64700) (@lem5034746 A B _64700 u f h1)). Qed.
Lemma lem5034749 {A B : Type'} (_64700 : A) (_64701 : A) (u : A -> Prop) (f : A -> B) (h1 : term48 A B u f) : term391 A B u f _64700 _64701.
Proof. exact (@lem5034748 A B _64700 u f h1 _64701). Qed.
Lemma lem5034750 {A B : Type'} (u : A -> Prop) (f : A -> B) (_64700 : A) (_64701 : A) : (term391 A B u f _64700 _64701) = (term112 A B u f _64700 _64701).
Proof. exact (eq_refl (term391 A B u f _64700 _64701)). Qed.
Lemma lem5034751 {A B : Type'} (_64700 : A) (_64701 : A) (u : A -> Prop) (f : A -> B) (h1 : term48 A B u f) : term112 A B u f _64700 _64701.
Proof. exact (EQ_MP (@lem5034750 A B u f _64700 _64701) (@lem5034749 A B _64700 _64701 u f h1)). Qed.
Lemma lem5034752 {A B : Type'} (_64702 : A) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term392 A s u _64702.
Proof. exact (@lem5034588 A B u x' s f t x'' h1 _64702). Qed.
Lemma lem5034753 {A : Type'} (s : A -> Prop) (u : A -> Prop) (_64702 : A) : (term392 A s u _64702) = (term117 A s u _64702).
Proof. exact (eq_refl (term392 A s u _64702)). Qed.
Lemma lem5034755 {A B : Type'} (_64703 : A) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term392 A t u _64703.
Proof. exact (@lem5034601 A B u x' s f t x'' h1 _64703). Qed.
Lemma lem5034756 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_64703 : A) : (term392 A t u _64703) = (term117 A t u _64703).
Proof. exact (eq_refl (term392 A t u _64703)). Qed.
Lemma lem5034758 {A B : Type'} (_64704 : B) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term395 A B s x' f t _64704.
Proof. exact (@lem5034655 A B u x' s f t x'' h1 _64704). Qed.
Lemma lem5034759 {A B : Type'} (s : A -> Prop) (x' : B -> A) (_64704 : B) (f : A -> B) (t : A -> Prop) : (term395 A B s x' f t _64704) = (term387 A B s x' _64704 f t).
Proof. exact (eq_refl (term395 A B s x' f t _64704)). Qed.
Lemma lem5034760 {A B : Type'} (_64704 : B) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term387 A B s x' _64704 f t.
Proof. exact (EQ_MP (@lem5034759 A B s x' _64704 f t) (@lem5034758 A B _64704 u x' s f t x'' h1)). Qed.
Lemma lem5034761 {A B : Type'} (_64704 : B) (_64705 : A) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term396 A B s x' _64704 f t _64705.
Proof. exact (@lem5034760 A B _64704 u x' s f t x'' h1 _64705). Qed.
Lemma lem5034762 {A B : Type'} (s : A -> Prop) (x' : B -> A) (_64704 : B) (f : A -> B) (t : A -> Prop) (_64705 : A) : (term396 A B s x' _64704 f t _64705) = (term385 A B s x' _64704 f t _64705).
Proof. exact (eq_refl (term396 A B s x' _64704 f t _64705)). Qed.
Lemma lem5034763 {A B : Type'} (_64704 : B) (_64705 : A) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term385 A B s x' _64704 f t _64705.
Proof. exact (EQ_MP (@lem5034762 A B s x' _64704 f t _64705) (@lem5034761 A B _64704 _64705 u x' s f t x'' h1)). Qed.
Lemma lem5034770 {A B : Type'} (_64699 : A) (_64698 : B) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term397 A B f s _64699 t x'' _64698.
Proof. exact (proj2 (@lem5034745 A B _64699 _64698 u x' s f t x'' h1)). Qed.
Lemma lem5034771 {A B : Type'} (_64699 : A) (_64698 : B) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term398 A B s _64699 f x'' _64698.
Proof. exact (proj1 (@lem5034745 A B _64699 _64698 u x' s f t x'' h1)). Qed.
Lemma lem5034781 {A B : Type'} (u : A -> Prop) (f : A -> B) (_64692 : A) (_64693 : A) : (term112 A B u f _64692 _64693) = (term399 A B u f _64692 _64693).
Proof. exact (@lem5032617 (term400 A u _64692) (term104 A B u _64692 f _64693) (_64692 = _64693)). Qed.
Lemma lem5034788 {A B : Type'} (u : A -> Prop) (f : A -> B) (_64692 : A) (_64693 : A) : (term401 A B u f _64692 _64693) = (term402 A B u f _64692 _64693).
Proof. exact (@lem5032617 (term400 A u _64693) (term403 A B _64692 f _64693) (_64692 = _64693)). Qed.
Lemma lem5034789 {A : Type'} (u : A -> Prop) (_64692 : A) : (term105 A u _64692) = (term105 A u _64692).
Proof. exact (eq_refl (term105 A u _64692)). Qed.
Lemma lem5034792 {A B : Type'} (u : A -> Prop) (f : A -> B) (_64692 : A) (_64693 : A) : (term399 A B u f _64692 _64693) = (term404 A B u f _64692 _64693).
Proof. exact (MK_COMB (@lem5034789 A u _64692) (@lem5034788 A B u f _64692 _64693)). Qed.
Lemma lem5034794 {A B : Type'} (u : A -> Prop) (f : A -> B) (_64692 : A) (_64693 : A) : (term112 A B u f _64692 _64693) = (term404 A B u f _64692 _64693).
Proof. exact (TRANS (@lem5034781 A B u f _64692 _64693) (@lem5034792 A B u f _64692 _64693)). Qed.
Lemma lem5034795 {A B : Type'} (_64692 : A) (_64693 : A) (u : A -> Prop) (f : A -> B) (h1 : term48 A B u f) : term404 A B u f _64692 _64693.
Proof. exact (EQ_MP (@lem5034794 A B u f _64692 _64693) (@lem5034727 A B _64692 _64693 u f h1)). Qed.
Lemma lem5034801 {A B : Type'} (_64694 : A) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term117 A s u _64694.
Proof. exact (EQ_MP (@lem5034729 A s u _64694) (@lem5034728 A B _64694 u x' s f t x'' h1)). Qed.
Lemma lem5034807 {A B : Type'} (_64695 : A) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term117 A t u _64695.
Proof. exact (EQ_MP (@lem5034732 A t u _64695) (@lem5034731 A B _64695 u x' s f t x'' h1)). Qed.
Lemma lem5034811 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term344 A s t x) : term400 A t x.
Proof. exact (proj2 (@lem5034368 A s t x h1)). Qed.
Lemma lem5034822 {A B : Type'} (s : A -> Prop) (_64699 : A) (f : A -> B) (x'' : B -> A) (_64698 : B) : (term398 A B s _64699 f x'' _64698) = (term405 A B s _64699 f x'' _64698).
Proof. exact (@lem5032617 (term406 A B _64698 f _64699) (term400 A s _64699) (_64698 = (term366 A B f x'' _64698))). Qed.
Lemma lem5034823 {A B : Type'} (_64699 : A) (_64698 : B) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term405 A B s _64699 f x'' _64698.
Proof. exact (EQ_MP (@lem5034822 A B s _64699 f x'' _64698) (@lem5034771 A B _64699 _64698 u x' s f t x'' h1)). Qed.
Lemma lem5034834 {A B : Type'} (f : A -> B) (s : A -> Prop) (_64699 : A) (t : A -> Prop) (x'' : B -> A) (_64698 : B) : (term397 A B f s _64699 t x'' _64698) = (term407 A B f s _64699 t x'' _64698).
Proof. exact (@lem5032617 (term406 A B _64698 f _64699) (term400 A s _64699) (term367 A B t x'' _64698)). Qed.
Lemma lem5034835 {A B : Type'} (_64699 : A) (_64698 : B) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term407 A B f s _64699 t x'' _64698.
Proof. exact (EQ_MP (@lem5034834 A B f s _64699 t x'' _64698) (@lem5034770 A B _64699 _64698 u x' s f t x'' h1)). Qed.
Lemma lem5034859 {A B : Type'} (u : A -> Prop) (f : A -> B) (_64700 : A) (_64701 : A) : (term112 A B u f _64700 _64701) = (term399 A B u f _64700 _64701).
Proof. exact (@lem5032617 (term400 A u _64700) (term104 A B u _64700 f _64701) (_64700 = _64701)). Qed.
Lemma lem5034866 {A B : Type'} (u : A -> Prop) (f : A -> B) (_64700 : A) (_64701 : A) : (term401 A B u f _64700 _64701) = (term402 A B u f _64700 _64701).
Proof. exact (@lem5032617 (term400 A u _64701) (term403 A B _64700 f _64701) (_64700 = _64701)). Qed.
Lemma lem5034867 {A : Type'} (u : A -> Prop) (_64700 : A) : (term105 A u _64700) = (term105 A u _64700).
Proof. exact (eq_refl (term105 A u _64700)). Qed.
Lemma lem5034870 {A B : Type'} (u : A -> Prop) (f : A -> B) (_64700 : A) (_64701 : A) : (term399 A B u f _64700 _64701) = (term404 A B u f _64700 _64701).
Proof. exact (MK_COMB (@lem5034867 A u _64700) (@lem5034866 A B u f _64700 _64701)). Qed.
Lemma lem5034872 {A B : Type'} (u : A -> Prop) (f : A -> B) (_64700 : A) (_64701 : A) : (term112 A B u f _64700 _64701) = (term404 A B u f _64700 _64701).
Proof. exact (TRANS (@lem5034859 A B u f _64700 _64701) (@lem5034870 A B u f _64700 _64701)). Qed.
Lemma lem5034873 {A B : Type'} (_64700 : A) (_64701 : A) (u : A -> Prop) (f : A -> B) (h1 : term48 A B u f) : term404 A B u f _64700 _64701.
Proof. exact (EQ_MP (@lem5034872 A B u f _64700 _64701) (@lem5034751 A B _64700 _64701 u f h1)). Qed.
Lemma lem5034879 {A B : Type'} (_64702 : A) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term117 A s u _64702.
Proof. exact (EQ_MP (@lem5034753 A s u _64702) (@lem5034752 A B _64702 u x' s f t x'' h1)). Qed.
Lemma lem5034885 {A B : Type'} (_64703 : A) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term117 A t u _64703.
Proof. exact (EQ_MP (@lem5034756 A t u _64703) (@lem5034755 A B _64703 u x' s f t x'' h1)). Qed.
Lemma lem5034887 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term345 A s t x) : term400 A s x.
Proof. exact (proj1 (@lem5034369 A s t x h1)). Qed.
Lemma lem5034923 {A B : Type'} (_64704 : B) (_64705 : A) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term408 A B x' _64704 f t _64705.
Proof. exact (proj1 (@lem5034763 A B _64704 _64705 u x' s f t x'' h1)). Qed.
Lemma lem5034933 {A B : Type'} (_64704 : B) (_64705 : A) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term409 A B s x' _64704 f t _64705.
Proof. exact (proj2 (@lem5034763 A B _64704 _64705 u x' s f t x'' h1)). Qed.
Lemma lem5034934 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5034935 {A : Type'} (_64708 : A) (_64709 : A) (h1 : _64708 = _64709) : _64708 = _64709.
Proof. exact (h1). Qed.
Lemma lem5034936 {A : Type'} (t : A -> Prop) (_64708 : A) (_64709 : A) (h1 : _64708 = _64709) : (t _64708) = (t _64709).
Proof. exact (MK_COMB (@lem5034934 A t) (@lem5034935 A _64708 _64709 h1)). Qed.
Lemma lem5034938 (b : Prop) (a : Prop) : term410 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem5034939 {A : Type'} (_64709 : A) (t : A -> Prop) (_64708 : A) : term411 A _64709 t _64708.
Proof. exact (@lem5034938 (t _64709) (t _64708)). Qed.
Lemma lem5034940 {A : Type'} (t : A -> Prop) (_64708 : A) (_64709 : A) (h1 : _64708 = _64709) : term412 A _64709 t _64708.
Proof. exact (@lem5034939 A _64709 t _64708 (@lem5034936 A t _64708 _64709 h1)). Qed.
Lemma lem5034941 {A : Type'} (_64709 : A) (t : A -> Prop) (_64708 : A) : term413 A _64709 t _64708.
Proof. exact (fun h0 : _64708 = _64709 => @lem5034940 A t _64708 _64709 h0). Qed.
Lemma lem5034943 (a : Prop) (b : Prop) : (a -> b) = (term414 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5034944 {A : Type'} (_64709 : A) (t : A -> Prop) (_64708 : A) : (term413 A _64709 t _64708) = (term415 A _64709 t _64708).
Proof. exact (@lem5034943 (_64708 = _64709) (term412 A _64709 t _64708)). Qed.
Lemma lem5034945 {A : Type'} (_64709 : A) (t : A -> Prop) (_64708 : A) : term415 A _64709 t _64708.
Proof. exact (EQ_MP (@lem5034944 A _64709 t _64708) (@lem5034941 A _64709 t _64708)). Qed.
Lemma lem5034997 {A : Type'} (x : A) (y : A) (z : A) : term416 A x y z.
Proof. exact (@lem21385 A x y z). Qed.
Lemma lem5034999 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term344 A s t x) : s x.
Proof. exact (proj1 (@lem5034368 A s t x h1)). Qed.
Lemma lem5035000 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term344 A s t x) : term417 A s x.
Proof. exact (fun h0 : term400 A s x => @lem5034999 A s t x h1). Qed.
Lemma lem5035002 (p : Prop) : (term418 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5035003 {A : Type'} (s : A -> Prop) (x : A) : (term417 A s x) = (s x).
Proof. exact (@lem5035002 (s x)). Qed.
Lemma lem5035004 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term344 A s t x) : s x.
Proof. exact (EQ_MP (@lem5035003 A s x) (@lem5035000 A s t x h1)). Qed.
Lemma lem5035010 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5035011 {A : Type'} (u : A -> Prop) (s : A -> Prop) (_64694 : A) : (term117 A s u _64694) = (term419 A u s _64694).
Proof. exact (@lem5035010 (u _64694) (term400 A s _64694)). Qed.
Lemma lem5035017 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5035018 {A : Type'} (u : A -> Prop) (s : A -> Prop) (_64694 : A) : (term420 A s u _64694) = (term421 A u s _64694).
Proof. exact (MK_COMB (@lem5035017) (@lem5035011 A u s _64694)). Qed.
Lemma lem5035024 {A : Type'} (u : A -> Prop) (s : A -> Prop) (_64694 : A) : (term419 A u s _64694) = (term419 A u s _64694).
Proof. exact (eq_refl (term419 A u s _64694)). Qed.
Lemma lem5035025 {A : Type'} (u : A -> Prop) (s : A -> Prop) (_64694 : A) : ((term117 A s u _64694) = (term419 A u s _64694)) = ((term419 A u s _64694) = (term419 A u s _64694)).
Proof. exact (MK_COMB (@lem5035018 A u s _64694) (@lem5035024 A u s _64694)). Qed.
Lemma lem5035027 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5035028 (x : Prop) : (x = x) = True.
Proof. exact (@lem5035027 Prop x). Qed.
Lemma lem5035029 {A : Type'} (u : A -> Prop) (s : A -> Prop) (_64694 : A) : ((term419 A u s _64694) = (term419 A u s _64694)) = True.
Proof. exact (@lem5035028 (term419 A u s _64694)). Qed.
Lemma lem5035030 {A : Type'} (u : A -> Prop) (s : A -> Prop) (_64694 : A) : ((term117 A s u _64694) = (term419 A u s _64694)) = True.
Proof. exact (TRANS (@lem5035025 A u s _64694) (@lem5035029 A u s _64694)). Qed.
Lemma lem5035031 {A : Type'} (u : A -> Prop) (s : A -> Prop) (_64694 : A) : True = ((term117 A s u _64694) = (term419 A u s _64694)).
Proof. exact (SYM (@lem5035030 A u s _64694)). Qed.
Lemma lem5035032 {A : Type'} (u : A -> Prop) (s : A -> Prop) (_64694 : A) : (term117 A s u _64694) = (term419 A u s _64694).
Proof. exact (EQ_MP (@lem5035031 A u s _64694) (@lem0)). Qed.
Lemma lem5035033 {A B : Type'} (_64694 : A) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term419 A u s _64694.
Proof. exact (EQ_MP (@lem5035032 A u s _64694) (@lem5034801 A B _64694 u x' s f t x'' h1)). Qed.
Lemma lem5035035 (b : Prop) (a : Prop) : (a \/ b) = (term422 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5035036 {A : Type'} (s : A -> Prop) (u : A -> Prop) (_64694 : A) : (term419 A u s _64694) = (term423 A s u _64694).
Proof. exact (@lem5035035 (term400 A s _64694) (u _64694)). Qed.
Lemma lem5035038 (a : Prop) : (term92 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5035039 {A : Type'} (s : A -> Prop) (_64694 : A) : (term424 A s _64694) = (s _64694).
Proof. exact (@lem5035038 (s _64694)). Qed.
Lemma lem5035040 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5035041 {A : Type'} (s : A -> Prop) (_64694 : A) : (term425 A s _64694) = (term51 A s _64694).
Proof. exact (MK_COMB (@lem5035040) (@lem5035039 A s _64694)). Qed.
Lemma lem5035042 {A : Type'} (u : A -> Prop) (_64694 : A) : (u _64694) = (u _64694).
Proof. exact (eq_refl (u _64694)). Qed.
Lemma lem5035043 {A : Type'} (s : A -> Prop) (u : A -> Prop) (_64694 : A) : (term423 A s u _64694) = (term53 A s u _64694).
Proof. exact (MK_COMB (@lem5035041 A s _64694) (@lem5035042 A u _64694)). Qed.
Lemma lem5035044 {A : Type'} (s : A -> Prop) (u : A -> Prop) (_64694 : A) : (term419 A u s _64694) = (term53 A s u _64694).
Proof. exact (TRANS (@lem5035036 A s u _64694) (@lem5035043 A s u _64694)). Qed.
Lemma lem5035047 {A B : Type'} (_64694 : A) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term53 A s u _64694.
Proof. exact (EQ_MP (@lem5035044 A s u _64694) (@lem5035033 A B _64694 u x' s f t x'' h1)). Qed.
Lemma lem5035048 {A B : Type'} (_64694 : A) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term53 A s u _64694.
Proof. exact (@lem5035047 A B _64694 u x' s f t x'' h1). Qed.
Lemma lem5035049 {A B : Type'} (x : A) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term53 A s u x.
Proof. exact (@lem5035048 A B x u x' s f t x'' h1). Qed.
Lemma lem5035052 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term335 A B u x' s f t x'') (h2 : term344 A s t x) : u x.
Proof. exact (@lem5035049 A B x u x' s f t x'' h1 (@lem5035004 A s t x h2)). Qed.
Lemma lem5035053 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term335 A B u x' s f t x'') (h2 : term344 A s t x) : term417 A u x.
Proof. exact (fun h0 : term400 A u x => @lem5035052 A B u x' f x'' s t x h1 h2). Qed.
Lemma lem5035055 (p : Prop) : (term418 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5035056 {A : Type'} (u : A -> Prop) (x : A) : (term417 A u x) = (u x).
Proof. exact (@lem5035055 (u x)). Qed.
Lemma lem5035057 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term335 A B u x' s f t x'') (h2 : term344 A s t x) : u x.
Proof. exact (EQ_MP (@lem5035056 A u x) (@lem5035053 A B u x' f x'' s t x h1 h2)). Qed.
Lemma lem5035059 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem5035060 {B : Type'} (x : B) : x = x.
Proof. exact (@lem5035059 B x). Qed.
Lemma lem5035061 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (@lem5035060 B (f x)). Qed.
Lemma lem5035062 {A B : Type'} (f : A -> B) (x : A) : term426 A B f x.
Proof. exact (fun h0 : term427 A B f x => @lem5035061 A B f x). Qed.
Lemma lem5035064 (p : Prop) : (term418 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5035065 {A B : Type'} (f : A -> B) (x : A) : (term426 A B f x) = ((f x) = (f x)).
Proof. exact (@lem5035064 ((f x) = (f x))). Qed.
Lemma lem5035066 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (EQ_MP (@lem5035065 A B f x) (@lem5035062 A B f x)). Qed.
Lemma lem5035068 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term344 A s t x) : s x.
Proof. exact (proj1 (@lem5034368 A s t x h1)). Qed.
Lemma lem5035069 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term344 A s t x) : term417 A s x.
Proof. exact (fun h0 : term400 A s x => @lem5035068 A s t x h1). Qed.
Lemma lem5035071 (p : Prop) : (term418 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5035072 {A : Type'} (s : A -> Prop) (x : A) : (term417 A s x) = (s x).
Proof. exact (@lem5035071 (s x)). Qed.
Lemma lem5035073 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term344 A s t x) : s x.
Proof. exact (EQ_MP (@lem5035072 A s x) (@lem5035069 A s t x h1)). Qed.
Lemma lem5035079 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5035080 {A B : Type'} (s : A -> Prop) (f : A -> B) (_64699 : A) (t : A -> Prop) (x'' : B -> A) (_64698 : B) : (term407 A B f s _64699 t x'' _64698) = (term428 A B s f _64699 t x'' _64698).
Proof. exact (@lem5035079 (term400 A s _64699) (term406 A B _64698 f _64699) (term367 A B t x'' _64698)). Qed.
Lemma lem5035094 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5035095 {A B : Type'} (t : A -> Prop) (x'' : B -> A) (_64698 : B) (f : A -> B) (_64699 : A) : (term429 A B f _64699 t x'' _64698) = (term430 A B t x'' _64698 f _64699).
Proof. exact (@lem5035094 (term367 A B t x'' _64698) (term406 A B _64698 f _64699)). Qed.
Lemma lem5035103 {A : Type'} (s : A -> Prop) (_64699 : A) : (term105 A s _64699) = (term105 A s _64699).
Proof. exact (eq_refl (term105 A s _64699)). Qed.
Lemma lem5035104 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (x'' : B -> A) (_64698 : B) (f : A -> B) (_64699 : A) : (term428 A B s f _64699 t x'' _64698) = (term431 A B s t x'' _64698 f _64699).
Proof. exact (MK_COMB (@lem5035103 A s _64699) (@lem5035095 A B t x'' _64698 f _64699)). Qed.
Lemma lem5035108 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5035109 {A B : Type'} (t : A -> Prop) (x'' : B -> A) (s : A -> Prop) (_64698 : B) (f : A -> B) (_64699 : A) : (term431 A B s t x'' _64698 f _64699) = (term432 A B t x'' s _64698 f _64699).
Proof. exact (@lem5035108 (term367 A B t x'' _64698) (term400 A s _64699) (term406 A B _64698 f _64699)). Qed.
Lemma lem5035127 {A B : Type'} (t : A -> Prop) (x'' : B -> A) (s : A -> Prop) (_64698 : B) (f : A -> B) (_64699 : A) : (term428 A B s f _64699 t x'' _64698) = (term432 A B t x'' s _64698 f _64699).
Proof. exact (TRANS (@lem5035104 A B s t x'' _64698 f _64699) (@lem5035109 A B t x'' s _64698 f _64699)). Qed.
Lemma lem5035128 {A B : Type'} (t : A -> Prop) (x'' : B -> A) (s : A -> Prop) (_64698 : B) (f : A -> B) (_64699 : A) : (term407 A B f s _64699 t x'' _64698) = (term432 A B t x'' s _64698 f _64699).
Proof. exact (TRANS (@lem5035080 A B s f _64699 t x'' _64698) (@lem5035127 A B t x'' s _64698 f _64699)). Qed.
Lemma lem5035129 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5035130 {A B : Type'} (t : A -> Prop) (x'' : B -> A) (s : A -> Prop) (_64698 : B) (f : A -> B) (_64699 : A) : (term433 A B f s _64699 t x'' _64698) = (term434 A B t x'' s _64698 f _64699).
Proof. exact (MK_COMB (@lem5035129) (@lem5035128 A B t x'' s _64698 f _64699)). Qed.
Lemma lem5035144 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5035145 {A B : Type'} (s : A -> Prop) (_64698 : B) (f : A -> B) (_64699 : A) : (term121 A B _64698 f s _64699) = (term435 A B s _64698 f _64699).
Proof. exact (@lem5035144 (term400 A s _64699) (term406 A B _64698 f _64699)). Qed.
Lemma lem5035153 {A B : Type'} (t : A -> Prop) (x'' : B -> A) (_64698 : B) : (term436 A B t x'' _64698) = (term436 A B t x'' _64698).
Proof. exact (eq_refl (term436 A B t x'' _64698)). Qed.
Lemma lem5035154 {A B : Type'} (t : A -> Prop) (x'' : B -> A) (s : A -> Prop) (_64698 : B) (f : A -> B) (_64699 : A) : (term409 A B t x'' _64698 f s _64699) = (term432 A B t x'' s _64698 f _64699).
Proof. exact (MK_COMB (@lem5035153 A B t x'' _64698) (@lem5035145 A B s _64698 f _64699)). Qed.
Lemma lem5035165 {A B : Type'} (t : A -> Prop) (x'' : B -> A) (s : A -> Prop) (_64698 : B) (f : A -> B) (_64699 : A) : ((term407 A B f s _64699 t x'' _64698) = (term409 A B t x'' _64698 f s _64699)) = ((term432 A B t x'' s _64698 f _64699) = (term432 A B t x'' s _64698 f _64699)).
Proof. exact (MK_COMB (@lem5035130 A B t x'' s _64698 f _64699) (@lem5035154 A B t x'' s _64698 f _64699)). Qed.
Lemma lem5035167 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5035168 (x : Prop) : (x = x) = True.
Proof. exact (@lem5035167 Prop x). Qed.
Lemma lem5035169 {A B : Type'} (t : A -> Prop) (x'' : B -> A) (s : A -> Prop) (_64698 : B) (f : A -> B) (_64699 : A) : ((term432 A B t x'' s _64698 f _64699) = (term432 A B t x'' s _64698 f _64699)) = True.
Proof. exact (@lem5035168 (term432 A B t x'' s _64698 f _64699)). Qed.
Lemma lem5035170 {A B : Type'} (t : A -> Prop) (x'' : B -> A) (_64698 : B) (f : A -> B) (s : A -> Prop) (_64699 : A) : ((term407 A B f s _64699 t x'' _64698) = (term409 A B t x'' _64698 f s _64699)) = True.
Proof. exact (TRANS (@lem5035165 A B t x'' s _64698 f _64699) (@lem5035169 A B t x'' s _64698 f _64699)). Qed.
Lemma lem5035171 {A B : Type'} (t : A -> Prop) (x'' : B -> A) (_64698 : B) (f : A -> B) (s : A -> Prop) (_64699 : A) : True = ((term407 A B f s _64699 t x'' _64698) = (term409 A B t x'' _64698 f s _64699)).
Proof. exact (SYM (@lem5035170 A B t x'' _64698 f s _64699)). Qed.
Lemma lem5035172 {A B : Type'} (t : A -> Prop) (x'' : B -> A) (_64698 : B) (f : A -> B) (s : A -> Prop) (_64699 : A) : (term407 A B f s _64699 t x'' _64698) = (term409 A B t x'' _64698 f s _64699).
Proof. exact (EQ_MP (@lem5035171 A B t x'' _64698 f s _64699) (@lem0)). Qed.
Lemma lem5035173 {A B : Type'} (_64698 : B) (_64699 : A) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term409 A B t x'' _64698 f s _64699.
Proof. exact (EQ_MP (@lem5035172 A B t x'' _64698 f s _64699) (@lem5034835 A B _64699 _64698 u x' s f t x'' h1)). Qed.
Lemma lem5035175 (b : Prop) (a : Prop) : (a \/ b) = (term422 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5035176 {A B : Type'} (f : A -> B) (s : A -> Prop) (_64699 : A) (t : A -> Prop) (x'' : B -> A) (_64698 : B) : (term409 A B t x'' _64698 f s _64699) = (term437 A B f s _64699 t x'' _64698).
Proof. exact (@lem5035175 (term121 A B _64698 f s _64699) (term367 A B t x'' _64698)). Qed.
Lemma lem5035178 (a : Prop) (b : Prop) : (term438 a b) = (term439 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5035179 {A B : Type'} (_64698 : B) (f : A -> B) (s : A -> Prop) (_64699 : A) : (term440 A B _64698 f s _64699) = (term441 A B _64698 f s _64699).
Proof. exact (@lem5035178 (term406 A B _64698 f _64699) (term400 A s _64699)). Qed.
Lemma lem5035181 (a : Prop) : (term92 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5035182 {A B : Type'} (_64698 : B) (f : A -> B) (_64699 : A) : (term442 A B _64698 f _64699) = (_64698 = (f _64699)).
Proof. exact (@lem5035181 (_64698 = (f _64699))). Qed.
Lemma lem5035183 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5035184 {A B : Type'} (_64698 : B) (f : A -> B) (_64699 : A) : (term443 A B _64698 f _64699) = (term60 A B _64698 f _64699).
Proof. exact (MK_COMB (@lem5035183) (@lem5035182 A B _64698 f _64699)). Qed.
Lemma lem5035186 (a : Prop) : (term92 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5035187 {A : Type'} (s : A -> Prop) (_64699 : A) : (term424 A s _64699) = (s _64699).
Proof. exact (@lem5035186 (s _64699)). Qed.
Lemma lem5035188 {A B : Type'} (_64698 : B) (f : A -> B) (s : A -> Prop) (_64699 : A) : (term441 A B _64698 f s _64699) = (term62 A B _64698 f s _64699).
Proof. exact (MK_COMB (@lem5035184 A B _64698 f _64699) (@lem5035187 A s _64699)). Qed.
Lemma lem5035189 {A B : Type'} (_64698 : B) (f : A -> B) (s : A -> Prop) (_64699 : A) : (term440 A B _64698 f s _64699) = (term62 A B _64698 f s _64699).
Proof. exact (TRANS (@lem5035179 A B _64698 f s _64699) (@lem5035188 A B _64698 f s _64699)). Qed.
Lemma lem5035190 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5035191 {A B : Type'} (_64698 : B) (f : A -> B) (s : A -> Prop) (_64699 : A) : (term444 A B _64698 f s _64699) = (term445 A B _64698 f s _64699).
Proof. exact (MK_COMB (@lem5035190) (@lem5035189 A B _64698 f s _64699)). Qed.
Lemma lem5035192 {A B : Type'} (t : A -> Prop) (x'' : B -> A) (_64698 : B) : (term367 A B t x'' _64698) = (term367 A B t x'' _64698).
Proof. exact (eq_refl (term367 A B t x'' _64698)). Qed.
Lemma lem5035193 {A B : Type'} (f : A -> B) (s : A -> Prop) (_64699 : A) (t : A -> Prop) (x'' : B -> A) (_64698 : B) : (term437 A B f s _64699 t x'' _64698) = (term446 A B f s _64699 t x'' _64698).
Proof. exact (MK_COMB (@lem5035191 A B _64698 f s _64699) (@lem5035192 A B t x'' _64698)). Qed.
Lemma lem5035194 {A B : Type'} (f : A -> B) (s : A -> Prop) (_64699 : A) (t : A -> Prop) (x'' : B -> A) (_64698 : B) : (term409 A B t x'' _64698 f s _64699) = (term446 A B f s _64699 t x'' _64698).
Proof. exact (TRANS (@lem5035176 A B f s _64699 t x'' _64698) (@lem5035193 A B f s _64699 t x'' _64698)). Qed.
Lemma lem5035196 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term344 A s t x) : term447 A B f s x.
Proof. exact (conj (@lem5035066 A B f x) (@lem5035073 A s t x h1)). Qed.
Lemma lem5035198 {A B : Type'} (_64699 : A) (_64698 : B) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term446 A B f s _64699 t x'' _64698.
Proof. exact (EQ_MP (@lem5035194 A B f s _64699 t x'' _64698) (@lem5035173 A B _64698 _64699 u x' s f t x'' h1)). Qed.
Lemma lem5035199 {A B : Type'} (_64699 : A) (_64698 : B) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term446 A B f s _64699 t x'' _64698.
Proof. exact (@lem5035198 A B _64699 _64698 u x' s f t x'' h1). Qed.
Lemma lem5035200 {A B : Type'} (x : A) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term448 A B s t x'' f x.
Proof. exact (@lem5035199 A B x (f x) u x' s f t x'' h1). Qed.
Lemma lem5035203 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term335 A B u x' s f t x'') (h2 : term344 A s t x) : term449 A B t x'' f x.
Proof. exact (@lem5035200 A B x u x' s f t x'' h1 (@lem5035196 A B f s t x h2)). Qed.
Lemma lem5035204 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term335 A B u x' s f t x'') (h2 : term344 A s t x) : term450 A B t x'' f x.
Proof. exact (fun h0 : term451 A B t x'' f x => @lem5035203 A B u x' f x'' s t x h1 h2). Qed.
Lemma lem5035206 (p : Prop) : (term418 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5035207 {A B : Type'} (t : A -> Prop) (x'' : B -> A) (f : A -> B) (x : A) : (term450 A B t x'' f x) = (term449 A B t x'' f x).
Proof. exact (@lem5035206 (term449 A B t x'' f x)). Qed.
Lemma lem5035208 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term335 A B u x' s f t x'') (h2 : term344 A s t x) : term449 A B t x'' f x.
Proof. exact (EQ_MP (@lem5035207 A B t x'' f x) (@lem5035204 A B u x' f x'' s t x h1 h2)). Qed.
Lemma lem5035214 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5035215 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_64695 : A) : (term117 A t u _64695) = (term419 A u t _64695).
Proof. exact (@lem5035214 (u _64695) (term400 A t _64695)). Qed.
Lemma lem5035221 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5035222 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_64695 : A) : (term420 A t u _64695) = (term421 A u t _64695).
Proof. exact (MK_COMB (@lem5035221) (@lem5035215 A u t _64695)). Qed.
Lemma lem5035228 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_64695 : A) : (term419 A u t _64695) = (term419 A u t _64695).
Proof. exact (eq_refl (term419 A u t _64695)). Qed.
Lemma lem5035229 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_64695 : A) : ((term117 A t u _64695) = (term419 A u t _64695)) = ((term419 A u t _64695) = (term419 A u t _64695)).
Proof. exact (MK_COMB (@lem5035222 A u t _64695) (@lem5035228 A u t _64695)). Qed.
Lemma lem5035231 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5035232 (x : Prop) : (x = x) = True.
Proof. exact (@lem5035231 Prop x). Qed.
Lemma lem5035233 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_64695 : A) : ((term419 A u t _64695) = (term419 A u t _64695)) = True.
Proof. exact (@lem5035232 (term419 A u t _64695)). Qed.
Lemma lem5035234 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_64695 : A) : ((term117 A t u _64695) = (term419 A u t _64695)) = True.
Proof. exact (TRANS (@lem5035229 A u t _64695) (@lem5035233 A u t _64695)). Qed.
Lemma lem5035235 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_64695 : A) : True = ((term117 A t u _64695) = (term419 A u t _64695)).
Proof. exact (SYM (@lem5035234 A u t _64695)). Qed.
Lemma lem5035236 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_64695 : A) : (term117 A t u _64695) = (term419 A u t _64695).
Proof. exact (EQ_MP (@lem5035235 A u t _64695) (@lem0)). Qed.
Lemma lem5035237 {A B : Type'} (_64695 : A) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term419 A u t _64695.
Proof. exact (EQ_MP (@lem5035236 A u t _64695) (@lem5034807 A B _64695 u x' s f t x'' h1)). Qed.
Lemma lem5035239 (b : Prop) (a : Prop) : (a \/ b) = (term422 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5035240 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_64695 : A) : (term419 A u t _64695) = (term423 A t u _64695).
Proof. exact (@lem5035239 (term400 A t _64695) (u _64695)). Qed.
Lemma lem5035242 (a : Prop) : (term92 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5035243 {A : Type'} (t : A -> Prop) (_64695 : A) : (term424 A t _64695) = (t _64695).
Proof. exact (@lem5035242 (t _64695)). Qed.
Lemma lem5035244 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5035245 {A : Type'} (t : A -> Prop) (_64695 : A) : (term425 A t _64695) = (term51 A t _64695).
Proof. exact (MK_COMB (@lem5035244) (@lem5035243 A t _64695)). Qed.
Lemma lem5035246 {A : Type'} (u : A -> Prop) (_64695 : A) : (u _64695) = (u _64695).
Proof. exact (eq_refl (u _64695)). Qed.
Lemma lem5035247 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_64695 : A) : (term423 A t u _64695) = (term53 A t u _64695).
Proof. exact (MK_COMB (@lem5035245 A t _64695) (@lem5035246 A u _64695)). Qed.
Lemma lem5035248 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_64695 : A) : (term419 A u t _64695) = (term53 A t u _64695).
Proof. exact (TRANS (@lem5035240 A t u _64695) (@lem5035247 A t u _64695)). Qed.
Lemma lem5035251 {A B : Type'} (_64695 : A) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term53 A t u _64695.
Proof. exact (EQ_MP (@lem5035248 A t u _64695) (@lem5035237 A B _64695 u x' s f t x'' h1)). Qed.
Lemma lem5035252 {A B : Type'} (_64695 : A) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term53 A t u _64695.
Proof. exact (@lem5035251 A B _64695 u x' s f t x'' h1). Qed.
Lemma lem5035253 {A B : Type'} (x : A) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term452 A B t u x'' f x.
Proof. exact (@lem5035252 A B (term453 A B x'' f x) u x' s f t x'' h1). Qed.
Lemma lem5035256 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term335 A B u x' s f t x'') (h2 : term344 A s t x) : term449 A B u x'' f x.
Proof. exact (@lem5035253 A B x u x' s f t x'' h1 (@lem5035208 A B u x' f x'' s t x h1 h2)). Qed.
Lemma lem5035257 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term335 A B u x' s f t x'') (h2 : term344 A s t x) : term450 A B u x'' f x.
Proof. exact (fun h0 : term451 A B u x'' f x => @lem5035256 A B u x' f x'' s t x h1 h2). Qed.
Lemma lem5035259 (p : Prop) : (term418 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5035260 {A B : Type'} (u : A -> Prop) (x'' : B -> A) (f : A -> B) (x : A) : (term450 A B u x'' f x) = (term449 A B u x'' f x).
Proof. exact (@lem5035259 (term449 A B u x'' f x)). Qed.
Lemma lem5035261 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term335 A B u x' s f t x'') (h2 : term344 A s t x) : term449 A B u x'' f x.
Proof. exact (EQ_MP (@lem5035260 A B u x'' f x) (@lem5035257 A B u x' f x'' s t x h1 h2)). Qed.
Lemma lem5035263 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem5035264 {B : Type'} (x : B) : x = x.
Proof. exact (@lem5035263 B x). Qed.
Lemma lem5035265 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (@lem5035264 B (f x)). Qed.
Lemma lem5035266 {A B : Type'} (f : A -> B) (x : A) : term426 A B f x.
Proof. exact (fun h0 : term427 A B f x => @lem5035265 A B f x). Qed.
Lemma lem5035268 (p : Prop) : (term418 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5035269 {A B : Type'} (f : A -> B) (x : A) : (term426 A B f x) = ((f x) = (f x)).
Proof. exact (@lem5035268 ((f x) = (f x))). Qed.
Lemma lem5035270 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (EQ_MP (@lem5035269 A B f x) (@lem5035266 A B f x)). Qed.
Lemma lem5035272 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term344 A s t x) : s x.
Proof. exact (proj1 (@lem5034368 A s t x h1)). Qed.
Lemma lem5035273 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term344 A s t x) : term417 A s x.
Proof. exact (fun h0 : term400 A s x => @lem5035272 A s t x h1). Qed.
Lemma lem5035275 (p : Prop) : (term418 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5035276 {A : Type'} (s : A -> Prop) (x : A) : (term417 A s x) = (s x).
Proof. exact (@lem5035275 (s x)). Qed.
Lemma lem5035277 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term344 A s t x) : s x.
Proof. exact (EQ_MP (@lem5035276 A s x) (@lem5035273 A s t x h1)). Qed.
Lemma lem5035283 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5035284 {A B : Type'} (s : A -> Prop) (_64699 : A) (f : A -> B) (x'' : B -> A) (_64698 : B) : (term405 A B s _64699 f x'' _64698) = (term454 A B s _64699 f x'' _64698).
Proof. exact (@lem5035283 (term400 A s _64699) (term406 A B _64698 f _64699) (_64698 = (term366 A B f x'' _64698))). Qed.
Lemma lem5035298 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5035299 {A B : Type'} (x'' : B -> A) (_64698 : B) (f : A -> B) (_64699 : A) : (term455 A B _64699 f x'' _64698) = (term456 A B x'' _64698 f _64699).
Proof. exact (@lem5035298 (_64698 = (term366 A B f x'' _64698)) (term406 A B _64698 f _64699)). Qed.
Lemma lem5035309 {A : Type'} (s : A -> Prop) (_64699 : A) : (term105 A s _64699) = (term105 A s _64699).
Proof. exact (eq_refl (term105 A s _64699)). Qed.
Lemma lem5035310 {A B : Type'} (s : A -> Prop) (x'' : B -> A) (_64698 : B) (f : A -> B) (_64699 : A) : (term454 A B s _64699 f x'' _64698) = (term457 A B s x'' _64698 f _64699).
Proof. exact (MK_COMB (@lem5035309 A s _64699) (@lem5035299 A B x'' _64698 f _64699)). Qed.
Lemma lem5035314 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5035315 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (_64698 : B) (f : A -> B) (_64699 : A) : (term457 A B s x'' _64698 f _64699) = (term458 A B x'' s _64698 f _64699).
Proof. exact (@lem5035314 (_64698 = (term366 A B f x'' _64698)) (term400 A s _64699) (term406 A B _64698 f _64699)). Qed.
Lemma lem5035335 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (_64698 : B) (f : A -> B) (_64699 : A) : (term454 A B s _64699 f x'' _64698) = (term458 A B x'' s _64698 f _64699).
Proof. exact (TRANS (@lem5035310 A B s x'' _64698 f _64699) (@lem5035315 A B x'' s _64698 f _64699)). Qed.
Lemma lem5035336 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (_64698 : B) (f : A -> B) (_64699 : A) : (term405 A B s _64699 f x'' _64698) = (term458 A B x'' s _64698 f _64699).
Proof. exact (TRANS (@lem5035284 A B s _64699 f x'' _64698) (@lem5035335 A B x'' s _64698 f _64699)). Qed.
Lemma lem5035337 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5035338 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (_64698 : B) (f : A -> B) (_64699 : A) : (term459 A B s _64699 f x'' _64698) = (term460 A B x'' s _64698 f _64699).
Proof. exact (MK_COMB (@lem5035337) (@lem5035336 A B x'' s _64698 f _64699)). Qed.
Lemma lem5035354 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5035355 {A B : Type'} (s : A -> Prop) (_64698 : B) (f : A -> B) (_64699 : A) : (term121 A B _64698 f s _64699) = (term435 A B s _64698 f _64699).
Proof. exact (@lem5035354 (term400 A s _64699) (term406 A B _64698 f _64699)). Qed.
Lemma lem5035363 {A B : Type'} (f : A -> B) (x'' : B -> A) (_64698 : B) : (term461 A B f x'' _64698) = (term461 A B f x'' _64698).
Proof. exact (eq_refl (term461 A B f x'' _64698)). Qed.
Lemma lem5035364 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (_64698 : B) (f : A -> B) (_64699 : A) : (term408 A B x'' _64698 f s _64699) = (term458 A B x'' s _64698 f _64699).
Proof. exact (MK_COMB (@lem5035363 A B f x'' _64698) (@lem5035355 A B s _64698 f _64699)). Qed.
Lemma lem5035375 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (_64698 : B) (f : A -> B) (_64699 : A) : ((term405 A B s _64699 f x'' _64698) = (term408 A B x'' _64698 f s _64699)) = ((term458 A B x'' s _64698 f _64699) = (term458 A B x'' s _64698 f _64699)).
Proof. exact (MK_COMB (@lem5035338 A B x'' s _64698 f _64699) (@lem5035364 A B x'' s _64698 f _64699)). Qed.
Lemma lem5035377 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5035378 (x : Prop) : (x = x) = True.
Proof. exact (@lem5035377 Prop x). Qed.
Lemma lem5035379 {A B : Type'} (x'' : B -> A) (s : A -> Prop) (_64698 : B) (f : A -> B) (_64699 : A) : ((term458 A B x'' s _64698 f _64699) = (term458 A B x'' s _64698 f _64699)) = True.
Proof. exact (@lem5035378 (term458 A B x'' s _64698 f _64699)). Qed.
Lemma lem5035380 {A B : Type'} (x'' : B -> A) (_64698 : B) (f : A -> B) (s : A -> Prop) (_64699 : A) : ((term405 A B s _64699 f x'' _64698) = (term408 A B x'' _64698 f s _64699)) = True.
Proof. exact (TRANS (@lem5035375 A B x'' s _64698 f _64699) (@lem5035379 A B x'' s _64698 f _64699)). Qed.
Lemma lem5035381 {A B : Type'} (x'' : B -> A) (_64698 : B) (f : A -> B) (s : A -> Prop) (_64699 : A) : True = ((term405 A B s _64699 f x'' _64698) = (term408 A B x'' _64698 f s _64699)).
Proof. exact (SYM (@lem5035380 A B x'' _64698 f s _64699)). Qed.
Lemma lem5035382 {A B : Type'} (x'' : B -> A) (_64698 : B) (f : A -> B) (s : A -> Prop) (_64699 : A) : (term405 A B s _64699 f x'' _64698) = (term408 A B x'' _64698 f s _64699).
Proof. exact (EQ_MP (@lem5035381 A B x'' _64698 f s _64699) (@lem0)). Qed.
Lemma lem5035383 {A B : Type'} (_64698 : B) (_64699 : A) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term408 A B x'' _64698 f s _64699.
Proof. exact (EQ_MP (@lem5035382 A B x'' _64698 f s _64699) (@lem5034823 A B _64699 _64698 u x' s f t x'' h1)). Qed.
Lemma lem5035385 (b : Prop) (a : Prop) : (a \/ b) = (term422 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5035386 {A B : Type'} (s : A -> Prop) (_64699 : A) (f : A -> B) (x'' : B -> A) (_64698 : B) : (term408 A B x'' _64698 f s _64699) = (term462 A B s _64699 f x'' _64698).
Proof. exact (@lem5035385 (term121 A B _64698 f s _64699) (_64698 = (term366 A B f x'' _64698))). Qed.
Lemma lem5035388 (a : Prop) (b : Prop) : (term438 a b) = (term439 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5035389 {A B : Type'} (_64698 : B) (f : A -> B) (s : A -> Prop) (_64699 : A) : (term440 A B _64698 f s _64699) = (term441 A B _64698 f s _64699).
Proof. exact (@lem5035388 (term406 A B _64698 f _64699) (term400 A s _64699)). Qed.
Lemma lem5035391 (a : Prop) : (term92 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5035392 {A B : Type'} (_64698 : B) (f : A -> B) (_64699 : A) : (term442 A B _64698 f _64699) = (_64698 = (f _64699)).
Proof. exact (@lem5035391 (_64698 = (f _64699))). Qed.
Lemma lem5035393 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5035394 {A B : Type'} (_64698 : B) (f : A -> B) (_64699 : A) : (term443 A B _64698 f _64699) = (term60 A B _64698 f _64699).
Proof. exact (MK_COMB (@lem5035393) (@lem5035392 A B _64698 f _64699)). Qed.
Lemma lem5035396 (a : Prop) : (term92 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5035397 {A : Type'} (s : A -> Prop) (_64699 : A) : (term424 A s _64699) = (s _64699).
Proof. exact (@lem5035396 (s _64699)). Qed.
Lemma lem5035398 {A B : Type'} (_64698 : B) (f : A -> B) (s : A -> Prop) (_64699 : A) : (term441 A B _64698 f s _64699) = (term62 A B _64698 f s _64699).
Proof. exact (MK_COMB (@lem5035394 A B _64698 f _64699) (@lem5035397 A s _64699)). Qed.
Lemma lem5035399 {A B : Type'} (_64698 : B) (f : A -> B) (s : A -> Prop) (_64699 : A) : (term440 A B _64698 f s _64699) = (term62 A B _64698 f s _64699).
Proof. exact (TRANS (@lem5035389 A B _64698 f s _64699) (@lem5035398 A B _64698 f s _64699)). Qed.
Lemma lem5035400 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5035401 {A B : Type'} (_64698 : B) (f : A -> B) (s : A -> Prop) (_64699 : A) : (term444 A B _64698 f s _64699) = (term445 A B _64698 f s _64699).
Proof. exact (MK_COMB (@lem5035400) (@lem5035399 A B _64698 f s _64699)). Qed.
Lemma lem5035402 {A B : Type'} (f : A -> B) (x'' : B -> A) (_64698 : B) : (_64698 = (term366 A B f x'' _64698)) = (_64698 = (term366 A B f x'' _64698)).
Proof. exact (eq_refl (_64698 = (term366 A B f x'' _64698))). Qed.
Lemma lem5035403 {A B : Type'} (s : A -> Prop) (_64699 : A) (f : A -> B) (x'' : B -> A) (_64698 : B) : (term462 A B s _64699 f x'' _64698) = (term463 A B s _64699 f x'' _64698).
Proof. exact (MK_COMB (@lem5035401 A B _64698 f s _64699) (@lem5035402 A B f x'' _64698)). Qed.
Lemma lem5035404 {A B : Type'} (s : A -> Prop) (_64699 : A) (f : A -> B) (x'' : B -> A) (_64698 : B) : (term408 A B x'' _64698 f s _64699) = (term463 A B s _64699 f x'' _64698).
Proof. exact (TRANS (@lem5035386 A B s _64699 f x'' _64698) (@lem5035403 A B s _64699 f x'' _64698)). Qed.
Lemma lem5035406 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term344 A s t x) : term447 A B f s x.
Proof. exact (conj (@lem5035270 A B f x) (@lem5035277 A s t x h1)). Qed.
Lemma lem5035408 {A B : Type'} (_64699 : A) (_64698 : B) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term463 A B s _64699 f x'' _64698.
Proof. exact (EQ_MP (@lem5035404 A B s _64699 f x'' _64698) (@lem5035383 A B _64698 _64699 u x' s f t x'' h1)). Qed.
Lemma lem5035409 {A B : Type'} (_64699 : A) (_64698 : B) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term463 A B s _64699 f x'' _64698.
Proof. exact (@lem5035408 A B _64699 _64698 u x' s f t x'' h1). Qed.
Lemma lem5035410 {A B : Type'} (x : A) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term464 A B s x'' f x.
Proof. exact (@lem5035409 A B x (f x) u x' s f t x'' h1). Qed.
Lemma lem5035413 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term335 A B u x' s f t x'') (h2 : term344 A s t x) : (f x) = (term465 A B x'' f x).
Proof. exact (@lem5035410 A B x u x' s f t x'' h1 (@lem5035406 A B f s t x h2)). Qed.
Lemma lem5035414 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term335 A B u x' s f t x'') (h2 : term344 A s t x) : term466 A B x'' f x.
Proof. exact (fun h0 : term467 A B x'' f x => @lem5035413 A B u x' f x'' s t x h1 h2). Qed.
Lemma lem5035416 (p : Prop) : (term418 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5035417 {A B : Type'} (x'' : B -> A) (f : A -> B) (x : A) : (term466 A B x'' f x) = ((f x) = (term465 A B x'' f x)).
Proof. exact (@lem5035416 ((f x) = (term465 A B x'' f x))). Qed.
Lemma lem5035418 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term335 A B u x' s f t x'') (h2 : term344 A s t x) : (f x) = (term465 A B x'' f x).
Proof. exact (EQ_MP (@lem5035417 A B x'' f x) (@lem5035414 A B u x' f x'' s t x h1 h2)). Qed.
Lemma lem5035444 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5035445 {A B : Type'} (_64692 : A) (f : A -> B) (_64693 : A) : (term468 A B f _64692 _64693) = (term469 A B _64692 f _64693).
Proof. exact (@lem5035444 (_64692 = _64693) (term403 A B _64692 f _64693)). Qed.
Lemma lem5035455 {A : Type'} (u : A -> Prop) (_64693 : A) : (term105 A u _64693) = (term105 A u _64693).
Proof. exact (eq_refl (term105 A u _64693)). Qed.
Lemma lem5035456 {A B : Type'} (u : A -> Prop) (_64692 : A) (f : A -> B) (_64693 : A) : (term402 A B u f _64692 _64693) = (term470 A B u _64692 f _64693).
Proof. exact (MK_COMB (@lem5035455 A u _64693) (@lem5035445 A B _64692 f _64693)). Qed.
Lemma lem5035460 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5035461 {A B : Type'} (u : A -> Prop) (_64692 : A) (f : A -> B) (_64693 : A) : (term470 A B u _64692 f _64693) = (term471 A B u _64692 f _64693).
Proof. exact (@lem5035460 (_64692 = _64693) (term400 A u _64693) (term403 A B _64692 f _64693)). Qed.
Lemma lem5035481 {A B : Type'} (u : A -> Prop) (_64692 : A) (f : A -> B) (_64693 : A) : (term402 A B u f _64692 _64693) = (term471 A B u _64692 f _64693).
Proof. exact (TRANS (@lem5035456 A B u _64692 f _64693) (@lem5035461 A B u _64692 f _64693)). Qed.
Lemma lem5035482 {A : Type'} (u : A -> Prop) (_64692 : A) : (term105 A u _64692) = (term105 A u _64692).
Proof. exact (eq_refl (term105 A u _64692)). Qed.
Lemma lem5035483 {A B : Type'} (u : A -> Prop) (_64692 : A) (f : A -> B) (_64693 : A) : (term404 A B u f _64692 _64693) = (term472 A B u _64692 f _64693).
Proof. exact (MK_COMB (@lem5035482 A u _64692) (@lem5035481 A B u _64692 f _64693)). Qed.
Lemma lem5035487 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5035488 {A B : Type'} (u : A -> Prop) (_64692 : A) (f : A -> B) (_64693 : A) : (term472 A B u _64692 f _64693) = (term473 A B u _64692 f _64693).
Proof. exact (@lem5035487 (_64692 = _64693) (term400 A u _64692) (term104 A B u _64692 f _64693)). Qed.
Lemma lem5035518 {A B : Type'} (u : A -> Prop) (_64692 : A) (f : A -> B) (_64693 : A) : (term404 A B u f _64692 _64693) = (term473 A B u _64692 f _64693).
Proof. exact (TRANS (@lem5035483 A B u _64692 f _64693) (@lem5035488 A B u _64692 f _64693)). Qed.
Lemma lem5035519 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5035520 {A B : Type'} (u : A -> Prop) (_64692 : A) (f : A -> B) (_64693 : A) : (term474 A B u f _64692 _64693) = (term475 A B u _64692 f _64693).
Proof. exact (MK_COMB (@lem5035519) (@lem5035518 A B u _64692 f _64693)). Qed.
Lemma lem5035550 {A B : Type'} (u : A -> Prop) (_64692 : A) (f : A -> B) (_64693 : A) : (term473 A B u _64692 f _64693) = (term473 A B u _64692 f _64693).
Proof. exact (eq_refl (term473 A B u _64692 f _64693)). Qed.
Lemma lem5035551 {A B : Type'} (u : A -> Prop) (_64692 : A) (f : A -> B) (_64693 : A) : ((term404 A B u f _64692 _64693) = (term473 A B u _64692 f _64693)) = ((term473 A B u _64692 f _64693) = (term473 A B u _64692 f _64693)).
Proof. exact (MK_COMB (@lem5035520 A B u _64692 f _64693) (@lem5035550 A B u _64692 f _64693)). Qed.
Lemma lem5035553 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5035554 (x : Prop) : (x = x) = True.
Proof. exact (@lem5035553 Prop x). Qed.
Lemma lem5035555 {A B : Type'} (u : A -> Prop) (_64692 : A) (f : A -> B) (_64693 : A) : ((term473 A B u _64692 f _64693) = (term473 A B u _64692 f _64693)) = True.
Proof. exact (@lem5035554 (term473 A B u _64692 f _64693)). Qed.
Lemma lem5035556 {A B : Type'} (u : A -> Prop) (_64692 : A) (f : A -> B) (_64693 : A) : ((term404 A B u f _64692 _64693) = (term473 A B u _64692 f _64693)) = True.
Proof. exact (TRANS (@lem5035551 A B u _64692 f _64693) (@lem5035555 A B u _64692 f _64693)). Qed.
Lemma lem5035557 {A B : Type'} (u : A -> Prop) (_64692 : A) (f : A -> B) (_64693 : A) : True = ((term404 A B u f _64692 _64693) = (term473 A B u _64692 f _64693)).
Proof. exact (SYM (@lem5035556 A B u _64692 f _64693)). Qed.
Lemma lem5035558 {A B : Type'} (u : A -> Prop) (_64692 : A) (f : A -> B) (_64693 : A) : (term404 A B u f _64692 _64693) = (term473 A B u _64692 f _64693).
Proof. exact (EQ_MP (@lem5035557 A B u _64692 f _64693) (@lem0)). Qed.
Lemma lem5035559 {A B : Type'} (_64692 : A) (_64693 : A) (u : A -> Prop) (f : A -> B) (h1 : term48 A B u f) : term473 A B u _64692 f _64693.
Proof. exact (EQ_MP (@lem5035558 A B u _64692 f _64693) (@lem5034795 A B _64692 _64693 u f h1)). Qed.
Lemma lem5035561 (b : Prop) (a : Prop) : (a \/ b) = (term422 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5035562 {A B : Type'} (u : A -> Prop) (f : A -> B) (_64692 : A) (_64693 : A) : (term473 A B u _64692 f _64693) = (term476 A B u f _64692 _64693).
Proof. exact (@lem5035561 (term107 A B u _64692 f _64693) (_64692 = _64693)). Qed.
Lemma lem5035564 (a : Prop) (b : Prop) : (term438 a b) = (term439 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5035565 {A B : Type'} (u : A -> Prop) (_64692 : A) (f : A -> B) (_64693 : A) : (term477 A B u _64692 f _64693) = (term478 A B u _64692 f _64693).
Proof. exact (@lem5035564 (term400 A u _64692) (term104 A B u _64692 f _64693)). Qed.
Lemma lem5035567 (a : Prop) : (term92 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5035568 {A : Type'} (u : A -> Prop) (_64692 : A) : (term424 A u _64692) = (u _64692).
Proof. exact (@lem5035567 (u _64692)). Qed.
Lemma lem5035569 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5035570 {A : Type'} (u : A -> Prop) (_64692 : A) : (term479 A u _64692) = (term32 A u _64692).
Proof. exact (MK_COMB (@lem5035569) (@lem5035568 A u _64692)). Qed.
Lemma lem5035572 (a : Prop) (b : Prop) : (term438 a b) = (term439 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5035573 {A B : Type'} (u : A -> Prop) (_64692 : A) (f : A -> B) (_64693 : A) : (term480 A B u _64692 f _64693) = (term481 A B u _64692 f _64693).
Proof. exact (@lem5035572 (term400 A u _64693) (term403 A B _64692 f _64693)). Qed.
Lemma lem5035575 (a : Prop) : (term92 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5035576 {A : Type'} (u : A -> Prop) (_64693 : A) : (term424 A u _64693) = (u _64693).
Proof. exact (@lem5035575 (u _64693)). Qed.
Lemma lem5035577 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5035578 {A : Type'} (u : A -> Prop) (_64693 : A) : (term479 A u _64693) = (term32 A u _64693).
Proof. exact (MK_COMB (@lem5035577) (@lem5035576 A u _64693)). Qed.
Lemma lem5035580 (a : Prop) : (term92 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5035581 {A B : Type'} (_64692 : A) (f : A -> B) (_64693 : A) : (term482 A B _64692 f _64693) = ((f _64692) = (f _64693)).
Proof. exact (@lem5035580 ((f _64692) = (f _64693))). Qed.
Lemma lem5035582 {A B : Type'} (u : A -> Prop) (_64692 : A) (f : A -> B) (_64693 : A) : (term481 A B u _64692 f _64693) = (term34 A B u _64692 f _64693).
Proof. exact (MK_COMB (@lem5035578 A u _64693) (@lem5035581 A B _64692 f _64693)). Qed.
Lemma lem5035583 {A B : Type'} (u : A -> Prop) (_64692 : A) (f : A -> B) (_64693 : A) : (term480 A B u _64692 f _64693) = (term34 A B u _64692 f _64693).
Proof. exact (TRANS (@lem5035573 A B u _64692 f _64693) (@lem5035582 A B u _64692 f _64693)). Qed.
Lemma lem5035584 {A B : Type'} (u : A -> Prop) (_64692 : A) (f : A -> B) (_64693 : A) : (term478 A B u _64692 f _64693) = (term36 A B u _64692 f _64693).
Proof. exact (MK_COMB (@lem5035570 A u _64692) (@lem5035583 A B u _64692 f _64693)). Qed.
Lemma lem5035585 {A B : Type'} (u : A -> Prop) (_64692 : A) (f : A -> B) (_64693 : A) : (term477 A B u _64692 f _64693) = (term36 A B u _64692 f _64693).
Proof. exact (TRANS (@lem5035565 A B u _64692 f _64693) (@lem5035584 A B u _64692 f _64693)). Qed.
Lemma lem5035586 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5035587 {A B : Type'} (u : A -> Prop) (_64692 : A) (f : A -> B) (_64693 : A) : (term483 A B u _64692 f _64693) = (term38 A B u _64692 f _64693).
Proof. exact (MK_COMB (@lem5035586) (@lem5035585 A B u _64692 f _64693)). Qed.
Lemma lem5035588 {A : Type'} (_64692 : A) (_64693 : A) : (_64692 = _64693) = (_64692 = _64693).
Proof. exact (eq_refl (_64692 = _64693)). Qed.
Lemma lem5035589 {A B : Type'} (u : A -> Prop) (f : A -> B) (_64692 : A) (_64693 : A) : (term476 A B u f _64692 _64693) = (term40 A B u f _64692 _64693).
Proof. exact (MK_COMB (@lem5035587 A B u _64692 f _64693) (@lem5035588 A _64692 _64693)). Qed.
Lemma lem5035590 {A B : Type'} (u : A -> Prop) (f : A -> B) (_64692 : A) (_64693 : A) : (term473 A B u _64692 f _64693) = (term40 A B u f _64692 _64693).
Proof. exact (TRANS (@lem5035562 A B u f _64692 _64693) (@lem5035589 A B u f _64692 _64693)). Qed.
Lemma lem5035592 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term335 A B u x' s f t x'') (h2 : term344 A s t x) : term484 A B u x'' f x.
Proof. exact (conj (@lem5035261 A B u x' f x'' s t x h1 h2) (@lem5035418 A B u x' f x'' s t x h1 h2)). Qed.
Lemma lem5035593 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term335 A B u x' s f t x'') (h2 : term344 A s t x) : term485 A B u x'' f x.
Proof. exact (conj (@lem5035057 A B u x' f x'' s t x h1 h2) (@lem5035592 A B u x' f x'' s t x h1 h2)). Qed.
Lemma lem5035595 {A B : Type'} (_64692 : A) (_64693 : A) (u : A -> Prop) (f : A -> B) (h1 : term48 A B u f) : term40 A B u f _64692 _64693.
Proof. exact (EQ_MP (@lem5035590 A B u f _64692 _64693) (@lem5035559 A B _64692 _64693 u f h1)). Qed.
Lemma lem5035596 {A B : Type'} (_64692 : A) (_64693 : A) (u : A -> Prop) (f : A -> B) (h1 : term48 A B u f) : term40 A B u f _64692 _64693.
Proof. exact (@lem5035595 A B _64692 _64693 u f h1). Qed.
Lemma lem5035597 {A B : Type'} (x'' : B -> A) (x : A) (u : A -> Prop) (f : A -> B) (h1 : term48 A B u f) : term486 A B u x'' f x.
Proof. exact (@lem5035596 A B x (term453 A B x'' f x) u f h1). Qed.
Lemma lem5035600 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term48 A B u f) (h2 : term335 A B u x' s f t x'') (h3 : term344 A s t x) : x = (term453 A B x'' f x).
Proof. exact (@lem5035597 A B x'' x u f h1 (@lem5035593 A B u x' f x'' s t x h2 h3)). Qed.
Lemma lem5035601 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term48 A B u f) (h2 : term335 A B u x' s f t x'') (h3 : term344 A s t x) : term487 A B x'' f x.
Proof. exact (fun h0 : term488 A B x'' f x => @lem5035600 A B u x' f x'' s t x h1 h2 h3). Qed.
Lemma lem5035603 (p : Prop) : (term418 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5035604 {A B : Type'} (x'' : B -> A) (f : A -> B) (x : A) : (term487 A B x'' f x) = (x = (term453 A B x'' f x)).
Proof. exact (@lem5035603 (x = (term453 A B x'' f x))). Qed.
Lemma lem5035605 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term48 A B u f) (h2 : term335 A B u x' s f t x'') (h3 : term344 A s t x) : x = (term453 A B x'' f x).
Proof. exact (EQ_MP (@lem5035604 A B x'' f x) (@lem5035601 A B u x' f x'' s t x h1 h2 h3)). Qed.
Lemma lem5035607 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem5035608 {A : Type'} (x : A) : x = x.
Proof. exact (@lem5035607 A x). Qed.
Lemma lem5035609 {A : Type'} (x : A) : term489 A x.
Proof. exact (fun h0 : term490 A x => @lem5035608 A x). Qed.
Lemma lem5035611 (p : Prop) : (term418 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5035612 {A : Type'} (x : A) : (term489 A x) = (x = x).
Proof. exact (@lem5035611 (x = x)). Qed.
Lemma lem5035613 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem5035612 A x) (@lem5035609 A x)). Qed.
Lemma lem5035631 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5035632 {A : Type'} (y : A) (x : A) (z : A) : (term491 A x y z) = (term492 A y x z).
Proof. exact (@lem5035631 (y = z) (term493 A x z)). Qed.
Lemma lem5035642 {A : Type'} (x : A) (y : A) : (term494 A x y) = (term494 A x y).
Proof. exact (eq_refl (term494 A x y)). Qed.
Lemma lem5035643 {A : Type'} (y : A) (x : A) (z : A) : (term416 A x y z) = (term495 A y x z).
Proof. exact (MK_COMB (@lem5035642 A x y) (@lem5035632 A y x z)). Qed.
Lemma lem5035647 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5035648 {A : Type'} (y : A) (x : A) (z : A) : (term495 A y x z) = (term496 A y x z).
Proof. exact (@lem5035647 (y = z) (term493 A x y) (term493 A x z)). Qed.
Lemma lem5035670 {A : Type'} (y : A) (x : A) (z : A) : (term416 A x y z) = (term496 A y x z).
Proof. exact (TRANS (@lem5035643 A y x z) (@lem5035648 A y x z)). Qed.
Lemma lem5035671 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5035672 {A : Type'} (y : A) (x : A) (z : A) : (term497 A x y z) = (term498 A y x z).
Proof. exact (MK_COMB (@lem5035671) (@lem5035670 A y x z)). Qed.
Lemma lem5035694 {A : Type'} (y : A) (x : A) (z : A) : (term496 A y x z) = (term496 A y x z).
Proof. exact (eq_refl (term496 A y x z)). Qed.
Lemma lem5035695 {A : Type'} (y : A) (x : A) (z : A) : ((term416 A x y z) = (term496 A y x z)) = ((term496 A y x z) = (term496 A y x z)).
Proof. exact (MK_COMB (@lem5035672 A y x z) (@lem5035694 A y x z)). Qed.
Lemma lem5035697 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5035698 (x : Prop) : (x = x) = True.
Proof. exact (@lem5035697 Prop x). Qed.
Lemma lem5035699 {A : Type'} (y : A) (x : A) (z : A) : ((term496 A y x z) = (term496 A y x z)) = True.
Proof. exact (@lem5035698 (term496 A y x z)). Qed.
Lemma lem5035700 {A : Type'} (y : A) (x : A) (z : A) : ((term416 A x y z) = (term496 A y x z)) = True.
Proof. exact (TRANS (@lem5035695 A y x z) (@lem5035699 A y x z)). Qed.
Lemma lem5035701 {A : Type'} (y : A) (x : A) (z : A) : True = ((term416 A x y z) = (term496 A y x z)).
Proof. exact (SYM (@lem5035700 A y x z)). Qed.
Lemma lem5035702 {A : Type'} (y : A) (x : A) (z : A) : (term416 A x y z) = (term496 A y x z).
Proof. exact (EQ_MP (@lem5035701 A y x z) (@lem0)). Qed.
Lemma lem5035703 {A : Type'} (y : A) (x : A) (z : A) : term496 A y x z.
Proof. exact (EQ_MP (@lem5035702 A y x z) (@lem5034997 A x y z)). Qed.
Lemma lem5035705 (b : Prop) (a : Prop) : (a \/ b) = (term422 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5035706 {A : Type'} (x : A) (y : A) (z : A) : (term496 A y x z) = (term499 A x y z).
Proof. exact (@lem5035705 (term500 A y x z) (y = z)). Qed.
Lemma lem5035708 (a : Prop) (b : Prop) : (term438 a b) = (term439 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5035709 {A : Type'} (y : A) (x : A) (z : A) : (term501 A y x z) = (term502 A y x z).
Proof. exact (@lem5035708 (term493 A x y) (term493 A x z)). Qed.
Lemma lem5035711 (a : Prop) : (term92 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5035712 {A : Type'} (x : A) (y : A) : (term503 A x y) = (x = y).
Proof. exact (@lem5035711 (x = y)). Qed.
Lemma lem5035713 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5035714 {A : Type'} (x : A) (y : A) : (term504 A x y) = (term505 A x y).
Proof. exact (MK_COMB (@lem5035713) (@lem5035712 A x y)). Qed.
Lemma lem5035716 (a : Prop) : (term92 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5035717 {A : Type'} (x : A) (z : A) : (term503 A x z) = (x = z).
Proof. exact (@lem5035716 (x = z)). Qed.
Lemma lem5035718 {A : Type'} (y : A) (x : A) (z : A) : (term502 A y x z) = (term506 A y x z).
Proof. exact (MK_COMB (@lem5035714 A x y) (@lem5035717 A x z)). Qed.
Lemma lem5035719 {A : Type'} (y : A) (x : A) (z : A) : (term501 A y x z) = (term506 A y x z).
Proof. exact (TRANS (@lem5035709 A y x z) (@lem5035718 A y x z)). Qed.
Lemma lem5035720 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5035721 {A : Type'} (y : A) (x : A) (z : A) : (term507 A y x z) = (term508 A y x z).
Proof. exact (MK_COMB (@lem5035720) (@lem5035719 A y x z)). Qed.
Lemma lem5035722 {A : Type'} (y : A) (z : A) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem5035723 {A : Type'} (x : A) (y : A) (z : A) : (term499 A x y z) = (term509 A x y z).
Proof. exact (MK_COMB (@lem5035721 A y x z) (@lem5035722 A y z)). Qed.
Lemma lem5035724 {A : Type'} (x : A) (y : A) (z : A) : (term496 A y x z) = (term509 A x y z).
Proof. exact (TRANS (@lem5035706 A x y z) (@lem5035723 A x y z)). Qed.
Lemma lem5035726 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term48 A B u f) (h2 : term335 A B u x' s f t x'') (h3 : term344 A s t x) : term510 A B x'' f x.
Proof. exact (conj (@lem5035605 A B u x' f x'' s t x h1 h2 h3) (@lem5035613 A x)). Qed.
Lemma lem5035728 {A : Type'} (x : A) (y : A) (z : A) : term509 A x y z.
Proof. exact (EQ_MP (@lem5035724 A x y z) (@lem5035703 A y x z)). Qed.
Lemma lem5035729 {A : Type'} (x : A) (y : A) (z : A) : term509 A x y z.
Proof. exact (@lem5035728 A x y z). Qed.
Lemma lem5035730 {A B : Type'} (x'' : B -> A) (f : A -> B) (x : A) : term511 A B x'' f x.
Proof. exact (@lem5035729 A x (term453 A B x'' f x) x). Qed.
Lemma lem5035733 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term48 A B u f) (h2 : term335 A B u x' s f t x'') (h3 : term344 A s t x) : (term453 A B x'' f x) = x.
Proof. exact (@lem5035730 A B x'' f x (@lem5035726 A B u x' f x'' s t x h1 h2 h3)). Qed.
Lemma lem5035734 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term48 A B u f) (h2 : term335 A B u x' s f t x'') (h3 : term344 A s t x) : term512 A B x'' f x.
Proof. exact (fun h0 : term513 A B x'' f x => @lem5035733 A B u x' f x'' s t x h1 h2 h3). Qed.
Lemma lem5035736 (p : Prop) : (term418 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5035737 {A B : Type'} (x'' : B -> A) (f : A -> B) (x : A) : (term512 A B x'' f x) = ((term453 A B x'' f x) = x).
Proof. exact (@lem5035736 ((term453 A B x'' f x) = x)). Qed.
Lemma lem5035738 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term48 A B u f) (h2 : term335 A B u x' s f t x'') (h3 : term344 A s t x) : (term453 A B x'' f x) = x.
Proof. exact (EQ_MP (@lem5035737 A B x'' f x) (@lem5035734 A B u x' f x'' s t x h1 h2 h3)). Qed.
Lemma lem5035740 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem5035741 {B : Type'} (x : B) : x = x.
Proof. exact (@lem5035740 B x). Qed.
Lemma lem5035742 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (@lem5035741 B (f x)). Qed.
Lemma lem5035743 {A B : Type'} (f : A -> B) (x : A) : term426 A B f x.
Proof. exact (fun h0 : term427 A B f x => @lem5035742 A B f x). Qed.
Lemma lem5035745 (p : Prop) : (term418 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5035746 {A B : Type'} (f : A -> B) (x : A) : (term426 A B f x) = ((f x) = (f x)).
Proof. exact (@lem5035745 ((f x) = (f x))). Qed.
Lemma lem5035747 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (EQ_MP (@lem5035746 A B f x) (@lem5035743 A B f x)). Qed.
Lemma lem5035749 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term344 A s t x) : s x.
Proof. exact (proj1 (@lem5034368 A s t x h1)). Qed.
Lemma lem5035750 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term344 A s t x) : term417 A s x.
Proof. exact (fun h0 : term400 A s x => @lem5035749 A s t x h1). Qed.
Lemma lem5035752 (p : Prop) : (term418 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5035753 {A : Type'} (s : A -> Prop) (x : A) : (term417 A s x) = (s x).
Proof. exact (@lem5035752 (s x)). Qed.
Lemma lem5035754 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term344 A s t x) : s x.
Proof. exact (EQ_MP (@lem5035753 A s x) (@lem5035750 A s t x h1)). Qed.
Lemma lem5035755 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term344 A s t x) : term447 A B f s x.
Proof. exact (conj (@lem5035747 A B f x) (@lem5035754 A s t x h1)). Qed.
Lemma lem5035757 {A B : Type'} (_64699 : A) (_64698 : B) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term446 A B f s _64699 t x'' _64698.
Proof. exact (EQ_MP (@lem5035194 A B f s _64699 t x'' _64698) (@lem5035173 A B _64698 _64699 u x' s f t x'' h1)). Qed.
Lemma lem5035758 {A B : Type'} (_64699 : A) (_64698 : B) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term446 A B f s _64699 t x'' _64698.
Proof. exact (@lem5035757 A B _64699 _64698 u x' s f t x'' h1). Qed.
Lemma lem5035759 {A B : Type'} (x : A) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term448 A B s t x'' f x.
Proof. exact (@lem5035758 A B x (f x) u x' s f t x'' h1). Qed.
Lemma lem5035762 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term335 A B u x' s f t x'') (h2 : term344 A s t x) : term449 A B t x'' f x.
Proof. exact (@lem5035759 A B x u x' s f t x'' h1 (@lem5035755 A B f s t x h2)). Qed.
Lemma lem5035763 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term335 A B u x' s f t x'') (h2 : term344 A s t x) : term450 A B t x'' f x.
Proof. exact (fun h0 : term451 A B t x'' f x => @lem5035762 A B u x' f x'' s t x h1 h2). Qed.
Lemma lem5035765 (p : Prop) : (term418 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5035766 {A B : Type'} (t : A -> Prop) (x'' : B -> A) (f : A -> B) (x : A) : (term450 A B t x'' f x) = (term449 A B t x'' f x).
Proof. exact (@lem5035765 (term449 A B t x'' f x)). Qed.
Lemma lem5035767 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term335 A B u x' s f t x'') (h2 : term344 A s t x) : term449 A B t x'' f x.
Proof. exact (EQ_MP (@lem5035766 A B t x'' f x) (@lem5035763 A B u x' f x'' s t x h1 h2)). Qed.
Lemma lem5035773 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5035774 {A : Type'} (_64709 : A) (t : A -> Prop) (_64708 : A) : (term415 A _64709 t _64708) = (term514 A _64709 t _64708).
Proof. exact (@lem5035773 (t _64709) (term493 A _64708 _64709) (term400 A t _64708)). Qed.
Lemma lem5035788 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5035789 {A : Type'} (t : A -> Prop) (_64708 : A) (_64709 : A) : (term515 A _64709 t _64708) = (term516 A t _64708 _64709).
Proof. exact (@lem5035788 (term400 A t _64708) (term493 A _64708 _64709)). Qed.
Lemma lem5035797 {A : Type'} (t : A -> Prop) (_64709 : A) : (term517 A t _64709) = (term517 A t _64709).
Proof. exact (eq_refl (term517 A t _64709)). Qed.
Lemma lem5035798 {A : Type'} (t : A -> Prop) (_64708 : A) (_64709 : A) : (term514 A _64709 t _64708) = (term518 A t _64708 _64709).
Proof. exact (MK_COMB (@lem5035797 A t _64709) (@lem5035789 A t _64708 _64709)). Qed.
Lemma lem5035809 {A : Type'} (t : A -> Prop) (_64708 : A) (_64709 : A) : (term415 A _64709 t _64708) = (term518 A t _64708 _64709).
Proof. exact (TRANS (@lem5035774 A _64709 t _64708) (@lem5035798 A t _64708 _64709)). Qed.
Lemma lem5035810 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5035811 {A : Type'} (t : A -> Prop) (_64708 : A) (_64709 : A) : (term519 A _64709 t _64708) = (term520 A t _64708 _64709).
Proof. exact (MK_COMB (@lem5035810) (@lem5035809 A t _64708 _64709)). Qed.
Lemma lem5035825 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5035826 {A : Type'} (t : A -> Prop) (_64708 : A) (_64709 : A) : (term515 A _64709 t _64708) = (term516 A t _64708 _64709).
Proof. exact (@lem5035825 (term400 A t _64708) (term493 A _64708 _64709)). Qed.
Lemma lem5035834 {A : Type'} (t : A -> Prop) (_64709 : A) : (term517 A t _64709) = (term517 A t _64709).
Proof. exact (eq_refl (term517 A t _64709)). Qed.
Lemma lem5035835 {A : Type'} (t : A -> Prop) (_64708 : A) (_64709 : A) : (term514 A _64709 t _64708) = (term518 A t _64708 _64709).
Proof. exact (MK_COMB (@lem5035834 A t _64709) (@lem5035826 A t _64708 _64709)). Qed.
Lemma lem5035846 {A : Type'} (t : A -> Prop) (_64708 : A) (_64709 : A) : ((term415 A _64709 t _64708) = (term514 A _64709 t _64708)) = ((term518 A t _64708 _64709) = (term518 A t _64708 _64709)).
Proof. exact (MK_COMB (@lem5035811 A t _64708 _64709) (@lem5035835 A t _64708 _64709)). Qed.
Lemma lem5035848 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5035849 (x : Prop) : (x = x) = True.
Proof. exact (@lem5035848 Prop x). Qed.
Lemma lem5035850 {A : Type'} (t : A -> Prop) (_64708 : A) (_64709 : A) : ((term518 A t _64708 _64709) = (term518 A t _64708 _64709)) = True.
Proof. exact (@lem5035849 (term518 A t _64708 _64709)). Qed.
Lemma lem5035851 {A : Type'} (_64709 : A) (t : A -> Prop) (_64708 : A) : ((term415 A _64709 t _64708) = (term514 A _64709 t _64708)) = True.
Proof. exact (TRANS (@lem5035846 A t _64708 _64709) (@lem5035850 A t _64708 _64709)). Qed.
Lemma lem5035852 {A : Type'} (_64709 : A) (t : A -> Prop) (_64708 : A) : True = ((term415 A _64709 t _64708) = (term514 A _64709 t _64708)).
Proof. exact (SYM (@lem5035851 A _64709 t _64708)). Qed.
Lemma lem5035853 {A : Type'} (_64709 : A) (t : A -> Prop) (_64708 : A) : (term415 A _64709 t _64708) = (term514 A _64709 t _64708).
Proof. exact (EQ_MP (@lem5035852 A _64709 t _64708) (@lem0)). Qed.
Lemma lem5035854 {A : Type'} (_64709 : A) (t : A -> Prop) (_64708 : A) : term514 A _64709 t _64708.
Proof. exact (EQ_MP (@lem5035853 A _64709 t _64708) (@lem5034945 A _64709 t _64708)). Qed.
Lemma lem5035856 (b : Prop) (a : Prop) : (a \/ b) = (term422 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5035857 {A : Type'} (_64708 : A) (t : A -> Prop) (_64709 : A) : (term514 A _64709 t _64708) = (term521 A _64708 t _64709).
Proof. exact (@lem5035856 (term515 A _64709 t _64708) (t _64709)). Qed.
Lemma lem5035859 (a : Prop) (b : Prop) : (term438 a b) = (term439 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5035860 {A : Type'} (_64709 : A) (t : A -> Prop) (_64708 : A) : (term522 A _64709 t _64708) = (term523 A _64709 t _64708).
Proof. exact (@lem5035859 (term493 A _64708 _64709) (term400 A t _64708)). Qed.
Lemma lem5035862 (a : Prop) : (term92 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5035863 {A : Type'} (_64708 : A) (_64709 : A) : (term503 A _64708 _64709) = (_64708 = _64709).
Proof. exact (@lem5035862 (_64708 = _64709)). Qed.
Lemma lem5035864 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5035865 {A : Type'} (_64708 : A) (_64709 : A) : (term504 A _64708 _64709) = (term505 A _64708 _64709).
Proof. exact (MK_COMB (@lem5035864) (@lem5035863 A _64708 _64709)). Qed.
Lemma lem5035867 (a : Prop) : (term92 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5035868 {A : Type'} (t : A -> Prop) (_64708 : A) : (term424 A t _64708) = (t _64708).
Proof. exact (@lem5035867 (t _64708)). Qed.
Lemma lem5035869 {A : Type'} (_64709 : A) (t : A -> Prop) (_64708 : A) : (term523 A _64709 t _64708) = (term524 A _64709 t _64708).
Proof. exact (MK_COMB (@lem5035865 A _64708 _64709) (@lem5035868 A t _64708)). Qed.
Lemma lem5035870 {A : Type'} (_64709 : A) (t : A -> Prop) (_64708 : A) : (term522 A _64709 t _64708) = (term524 A _64709 t _64708).
Proof. exact (TRANS (@lem5035860 A _64709 t _64708) (@lem5035869 A _64709 t _64708)). Qed.
Lemma lem5035871 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5035872 {A : Type'} (_64709 : A) (t : A -> Prop) (_64708 : A) : (term525 A _64709 t _64708) = (term526 A _64709 t _64708).
Proof. exact (MK_COMB (@lem5035871) (@lem5035870 A _64709 t _64708)). Qed.
Lemma lem5035873 {A : Type'} (t : A -> Prop) (_64709 : A) : (t _64709) = (t _64709).
Proof. exact (eq_refl (t _64709)). Qed.
Lemma lem5035874 {A : Type'} (_64708 : A) (t : A -> Prop) (_64709 : A) : (term521 A _64708 t _64709) = (term527 A _64708 t _64709).
Proof. exact (MK_COMB (@lem5035872 A _64709 t _64708) (@lem5035873 A t _64709)). Qed.
Lemma lem5035875 {A : Type'} (_64708 : A) (t : A -> Prop) (_64709 : A) : (term514 A _64709 t _64708) = (term527 A _64708 t _64709).
Proof. exact (TRANS (@lem5035857 A _64708 t _64709) (@lem5035874 A _64708 t _64709)). Qed.
Lemma lem5035877 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term48 A B u f) (h2 : term335 A B u x' s f t x'') (h3 : term344 A s t x) : term528 A B t x'' f x.
Proof. exact (conj (@lem5035738 A B u x' f x'' s t x h1 h2 h3) (@lem5035767 A B u x' f x'' s t x h2 h3)). Qed.
Lemma lem5035879 {A : Type'} (_64708 : A) (t : A -> Prop) (_64709 : A) : term527 A _64708 t _64709.
Proof. exact (EQ_MP (@lem5035875 A _64708 t _64709) (@lem5035854 A _64709 t _64708)). Qed.
Lemma lem5035880 {A : Type'} (_64708 : A) (t : A -> Prop) (_64709 : A) : term527 A _64708 t _64709.
Proof. exact (@lem5035879 A _64708 t _64709). Qed.
Lemma lem5035881 {A B : Type'} (x'' : B -> A) (f : A -> B) (t : A -> Prop) (x : A) : term529 A B x'' f t x.
Proof. exact (@lem5035880 A (term453 A B x'' f x) t x). Qed.
Lemma lem5035884 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term48 A B u f) (h2 : term335 A B u x' s f t x'') (h3 : term344 A s t x) : t x.
Proof. exact (@lem5035881 A B x'' f t x (@lem5035877 A B u x' f x'' s t x h1 h2 h3)). Qed.
Lemma lem5035885 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term48 A B u f) (h2 : term335 A B u x' s f t x'') (h3 : term344 A s t x) : term417 A t x.
Proof. exact (fun h0 : term400 A t x => @lem5035884 A B u x' f x'' s t x h1 h2 h3). Qed.
Lemma lem5035887 (p : Prop) : (term418 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5035888 {A : Type'} (t : A -> Prop) (x : A) : (term417 A t x) = (t x).
Proof. exact (@lem5035887 (t x)). Qed.
Lemma lem5035889 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term48 A B u f) (h2 : term335 A B u x' s f t x'') (h3 : term344 A s t x) : t x.
Proof. exact (EQ_MP (@lem5035888 A t x) (@lem5035885 A B u x' f x'' s t x h1 h2 h3)). Qed.
Lemma lem5035892 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5035894 {A : Type'} (t : A -> Prop) (x : A) : (term400 A t x) = (term530 A t x).
Proof. exact (@lem5035892 (t x)). Qed.
Lemma lem5035897 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term344 A s t x) : term530 A t x.
Proof. exact (EQ_MP (@lem5035894 A t x) (@lem5034811 A s t x h1)). Qed.
Lemma lem5035900 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term48 A B u f) (h2 : term335 A B u x' s f t x'') (h3 : term344 A s t x) : False.
Proof. exact (@lem5035897 A s t x h3 (@lem5035889 A B u x' f x'' s t x h1 h2 h3)). Qed.
Lemma lem5035901 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term48 A B u f) (h2 : term335 A B u x' s f t x'') (h3 : term344 A s t x) : term531.
Proof. exact (fun h0 : ~ False => @lem5035900 A B u x' f x'' s t x h1 h2 h3). Qed.
Lemma lem5035903 (p : Prop) : (term418 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5035904 : term531 = False.
Proof. exact (@lem5035903 False). Qed.
Lemma lem5035905 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term48 A B u f) (h2 : term335 A B u x' s f t x'') (h3 : term344 A s t x) : False.
Proof. exact (EQ_MP (@lem5035904) (@lem5035901 A B u x' f x'' s t x h1 h2 h3)). Qed.
Lemma lem5035918 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5035919 {A : Type'} (_64722 : A) (_64723 : A) (h1 : _64722 = _64723) : _64722 = _64723.
Proof. exact (h1). Qed.
Lemma lem5035920 {A : Type'} (s : A -> Prop) (_64722 : A) (_64723 : A) (h1 : _64722 = _64723) : (s _64722) = (s _64723).
Proof. exact (MK_COMB (@lem5035918 A s) (@lem5035919 A _64722 _64723 h1)). Qed.
Lemma lem5035922 (b : Prop) (a : Prop) : term410 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem5035923 {A : Type'} (_64723 : A) (s : A -> Prop) (_64722 : A) : term411 A _64723 s _64722.
Proof. exact (@lem5035922 (s _64723) (s _64722)). Qed.
Lemma lem5035924 {A : Type'} (s : A -> Prop) (_64722 : A) (_64723 : A) (h1 : _64722 = _64723) : term412 A _64723 s _64722.
Proof. exact (@lem5035923 A _64723 s _64722 (@lem5035920 A s _64722 _64723 h1)). Qed.
Lemma lem5035925 {A : Type'} (_64723 : A) (s : A -> Prop) (_64722 : A) : term413 A _64723 s _64722.
Proof. exact (fun h0 : _64722 = _64723 => @lem5035924 A s _64722 _64723 h0). Qed.
Lemma lem5035927 (a : Prop) (b : Prop) : (a -> b) = (term414 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5035928 {A : Type'} (_64723 : A) (s : A -> Prop) (_64722 : A) : (term413 A _64723 s _64722) = (term415 A _64723 s _64722).
Proof. exact (@lem5035927 (_64722 = _64723) (term412 A _64723 s _64722)). Qed.
Lemma lem5035929 {A : Type'} (_64723 : A) (s : A -> Prop) (_64722 : A) : term415 A _64723 s _64722.
Proof. exact (EQ_MP (@lem5035928 A _64723 s _64722) (@lem5035925 A _64723 s _64722)). Qed.
Lemma lem5035969 {A : Type'} (x : A) (y : A) (z : A) : term416 A x y z.
Proof. exact (@lem21385 A x y z). Qed.
Lemma lem5035971 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term345 A s t x) : t x.
Proof. exact (proj2 (@lem5034369 A s t x h1)). Qed.
Lemma lem5035972 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term345 A s t x) : term417 A t x.
Proof. exact (fun h0 : term400 A t x => @lem5035971 A s t x h1). Qed.
Lemma lem5035974 (p : Prop) : (term418 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5035975 {A : Type'} (t : A -> Prop) (x : A) : (term417 A t x) = (t x).
Proof. exact (@lem5035974 (t x)). Qed.
Lemma lem5035976 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term345 A s t x) : t x.
Proof. exact (EQ_MP (@lem5035975 A t x) (@lem5035972 A s t x h1)). Qed.
Lemma lem5035982 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5035983 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_64703 : A) : (term117 A t u _64703) = (term419 A u t _64703).
Proof. exact (@lem5035982 (u _64703) (term400 A t _64703)). Qed.
Lemma lem5035989 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5035990 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_64703 : A) : (term420 A t u _64703) = (term421 A u t _64703).
Proof. exact (MK_COMB (@lem5035989) (@lem5035983 A u t _64703)). Qed.
Lemma lem5035996 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_64703 : A) : (term419 A u t _64703) = (term419 A u t _64703).
Proof. exact (eq_refl (term419 A u t _64703)). Qed.
Lemma lem5035997 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_64703 : A) : ((term117 A t u _64703) = (term419 A u t _64703)) = ((term419 A u t _64703) = (term419 A u t _64703)).
Proof. exact (MK_COMB (@lem5035990 A u t _64703) (@lem5035996 A u t _64703)). Qed.
Lemma lem5035999 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5036000 (x : Prop) : (x = x) = True.
Proof. exact (@lem5035999 Prop x). Qed.
Lemma lem5036001 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_64703 : A) : ((term419 A u t _64703) = (term419 A u t _64703)) = True.
Proof. exact (@lem5036000 (term419 A u t _64703)). Qed.
Lemma lem5036002 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_64703 : A) : ((term117 A t u _64703) = (term419 A u t _64703)) = True.
Proof. exact (TRANS (@lem5035997 A u t _64703) (@lem5036001 A u t _64703)). Qed.
Lemma lem5036003 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_64703 : A) : True = ((term117 A t u _64703) = (term419 A u t _64703)).
Proof. exact (SYM (@lem5036002 A u t _64703)). Qed.
Lemma lem5036004 {A : Type'} (u : A -> Prop) (t : A -> Prop) (_64703 : A) : (term117 A t u _64703) = (term419 A u t _64703).
Proof. exact (EQ_MP (@lem5036003 A u t _64703) (@lem0)). Qed.
Lemma lem5036005 {A B : Type'} (_64703 : A) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term419 A u t _64703.
Proof. exact (EQ_MP (@lem5036004 A u t _64703) (@lem5034885 A B _64703 u x' s f t x'' h1)). Qed.
Lemma lem5036007 (b : Prop) (a : Prop) : (a \/ b) = (term422 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5036008 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_64703 : A) : (term419 A u t _64703) = (term423 A t u _64703).
Proof. exact (@lem5036007 (term400 A t _64703) (u _64703)). Qed.
Lemma lem5036010 (a : Prop) : (term92 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5036011 {A : Type'} (t : A -> Prop) (_64703 : A) : (term424 A t _64703) = (t _64703).
Proof. exact (@lem5036010 (t _64703)). Qed.
Lemma lem5036012 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5036013 {A : Type'} (t : A -> Prop) (_64703 : A) : (term425 A t _64703) = (term51 A t _64703).
Proof. exact (MK_COMB (@lem5036012) (@lem5036011 A t _64703)). Qed.
Lemma lem5036014 {A : Type'} (u : A -> Prop) (_64703 : A) : (u _64703) = (u _64703).
Proof. exact (eq_refl (u _64703)). Qed.
Lemma lem5036015 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_64703 : A) : (term423 A t u _64703) = (term53 A t u _64703).
Proof. exact (MK_COMB (@lem5036013 A t _64703) (@lem5036014 A u _64703)). Qed.
Lemma lem5036016 {A : Type'} (t : A -> Prop) (u : A -> Prop) (_64703 : A) : (term419 A u t _64703) = (term53 A t u _64703).
Proof. exact (TRANS (@lem5036008 A t u _64703) (@lem5036015 A t u _64703)). Qed.
Lemma lem5036019 {A B : Type'} (_64703 : A) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term53 A t u _64703.
Proof. exact (EQ_MP (@lem5036016 A t u _64703) (@lem5036005 A B _64703 u x' s f t x'' h1)). Qed.
Lemma lem5036020 {A B : Type'} (_64703 : A) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term53 A t u _64703.
Proof. exact (@lem5036019 A B _64703 u x' s f t x'' h1). Qed.
Lemma lem5036021 {A B : Type'} (x : A) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term53 A t u x.
Proof. exact (@lem5036020 A B x u x' s f t x'' h1). Qed.
Lemma lem5036024 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term335 A B u x' s f t x'') (h2 : term345 A s t x) : u x.
Proof. exact (@lem5036021 A B x u x' s f t x'' h1 (@lem5035976 A s t x h2)). Qed.
Lemma lem5036025 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term335 A B u x' s f t x'') (h2 : term345 A s t x) : term417 A u x.
Proof. exact (fun h0 : term400 A u x => @lem5036024 A B u x' f x'' s t x h1 h2). Qed.
Lemma lem5036027 (p : Prop) : (term418 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5036028 {A : Type'} (u : A -> Prop) (x : A) : (term417 A u x) = (u x).
Proof. exact (@lem5036027 (u x)). Qed.
Lemma lem5036029 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term335 A B u x' s f t x'') (h2 : term345 A s t x) : u x.
Proof. exact (EQ_MP (@lem5036028 A u x) (@lem5036025 A B u x' f x'' s t x h1 h2)). Qed.
Lemma lem5036031 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem5036032 {B : Type'} (x : B) : x = x.
Proof. exact (@lem5036031 B x). Qed.
Lemma lem5036033 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (@lem5036032 B (f x)). Qed.
Lemma lem5036034 {A B : Type'} (f : A -> B) (x : A) : term426 A B f x.
Proof. exact (fun h0 : term427 A B f x => @lem5036033 A B f x). Qed.
Lemma lem5036036 (p : Prop) : (term418 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5036037 {A B : Type'} (f : A -> B) (x : A) : (term426 A B f x) = ((f x) = (f x)).
Proof. exact (@lem5036036 ((f x) = (f x))). Qed.
Lemma lem5036038 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (EQ_MP (@lem5036037 A B f x) (@lem5036034 A B f x)). Qed.
Lemma lem5036040 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term345 A s t x) : t x.
Proof. exact (proj2 (@lem5034369 A s t x h1)). Qed.
Lemma lem5036041 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term345 A s t x) : term417 A t x.
Proof. exact (fun h0 : term400 A t x => @lem5036040 A s t x h1). Qed.
Lemma lem5036043 (p : Prop) : (term418 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5036044 {A : Type'} (t : A -> Prop) (x : A) : (term417 A t x) = (t x).
Proof. exact (@lem5036043 (t x)). Qed.
Lemma lem5036045 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term345 A s t x) : t x.
Proof. exact (EQ_MP (@lem5036044 A t x) (@lem5036041 A s t x h1)). Qed.
Lemma lem5036047 (b : Prop) (a : Prop) : (a \/ b) = (term422 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5036048 {A B : Type'} (f : A -> B) (t : A -> Prop) (_64705 : A) (s : A -> Prop) (x' : B -> A) (_64704 : B) : (term409 A B s x' _64704 f t _64705) = (term437 A B f t _64705 s x' _64704).
Proof. exact (@lem5036047 (term121 A B _64704 f t _64705) (term367 A B s x' _64704)). Qed.
Lemma lem5036050 (a : Prop) (b : Prop) : (term438 a b) = (term439 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5036051 {A B : Type'} (_64704 : B) (f : A -> B) (t : A -> Prop) (_64705 : A) : (term440 A B _64704 f t _64705) = (term441 A B _64704 f t _64705).
Proof. exact (@lem5036050 (term406 A B _64704 f _64705) (term400 A t _64705)). Qed.
Lemma lem5036053 (a : Prop) : (term92 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5036054 {A B : Type'} (_64704 : B) (f : A -> B) (_64705 : A) : (term442 A B _64704 f _64705) = (_64704 = (f _64705)).
Proof. exact (@lem5036053 (_64704 = (f _64705))). Qed.
Lemma lem5036055 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5036056 {A B : Type'} (_64704 : B) (f : A -> B) (_64705 : A) : (term443 A B _64704 f _64705) = (term60 A B _64704 f _64705).
Proof. exact (MK_COMB (@lem5036055) (@lem5036054 A B _64704 f _64705)). Qed.
Lemma lem5036058 (a : Prop) : (term92 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5036059 {A : Type'} (t : A -> Prop) (_64705 : A) : (term424 A t _64705) = (t _64705).
Proof. exact (@lem5036058 (t _64705)). Qed.
Lemma lem5036060 {A B : Type'} (_64704 : B) (f : A -> B) (t : A -> Prop) (_64705 : A) : (term441 A B _64704 f t _64705) = (term62 A B _64704 f t _64705).
Proof. exact (MK_COMB (@lem5036056 A B _64704 f _64705) (@lem5036059 A t _64705)). Qed.
Lemma lem5036061 {A B : Type'} (_64704 : B) (f : A -> B) (t : A -> Prop) (_64705 : A) : (term440 A B _64704 f t _64705) = (term62 A B _64704 f t _64705).
Proof. exact (TRANS (@lem5036051 A B _64704 f t _64705) (@lem5036060 A B _64704 f t _64705)). Qed.
Lemma lem5036062 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5036063 {A B : Type'} (_64704 : B) (f : A -> B) (t : A -> Prop) (_64705 : A) : (term444 A B _64704 f t _64705) = (term445 A B _64704 f t _64705).
Proof. exact (MK_COMB (@lem5036062) (@lem5036061 A B _64704 f t _64705)). Qed.
Lemma lem5036064 {A B : Type'} (s : A -> Prop) (x' : B -> A) (_64704 : B) : (term367 A B s x' _64704) = (term367 A B s x' _64704).
Proof. exact (eq_refl (term367 A B s x' _64704)). Qed.
Lemma lem5036065 {A B : Type'} (f : A -> B) (t : A -> Prop) (_64705 : A) (s : A -> Prop) (x' : B -> A) (_64704 : B) : (term437 A B f t _64705 s x' _64704) = (term446 A B f t _64705 s x' _64704).
Proof. exact (MK_COMB (@lem5036063 A B _64704 f t _64705) (@lem5036064 A B s x' _64704)). Qed.
Lemma lem5036066 {A B : Type'} (f : A -> B) (t : A -> Prop) (_64705 : A) (s : A -> Prop) (x' : B -> A) (_64704 : B) : (term409 A B s x' _64704 f t _64705) = (term446 A B f t _64705 s x' _64704).
Proof. exact (TRANS (@lem5036048 A B f t _64705 s x' _64704) (@lem5036065 A B f t _64705 s x' _64704)). Qed.
Lemma lem5036068 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term345 A s t x) : term447 A B f t x.
Proof. exact (conj (@lem5036038 A B f x) (@lem5036045 A s t x h1)). Qed.
Lemma lem5036070 {A B : Type'} (_64705 : A) (_64704 : B) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term446 A B f t _64705 s x' _64704.
Proof. exact (EQ_MP (@lem5036066 A B f t _64705 s x' _64704) (@lem5034933 A B _64704 _64705 u x' s f t x'' h1)). Qed.
Lemma lem5036071 {A B : Type'} (_64705 : A) (_64704 : B) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term446 A B f t _64705 s x' _64704.
Proof. exact (@lem5036070 A B _64705 _64704 u x' s f t x'' h1). Qed.
Lemma lem5036072 {A B : Type'} (x : A) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term448 A B t s x' f x.
Proof. exact (@lem5036071 A B x (f x) u x' s f t x'' h1). Qed.
Lemma lem5036075 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term335 A B u x' s f t x'') (h2 : term345 A s t x) : term449 A B s x' f x.
Proof. exact (@lem5036072 A B x u x' s f t x'' h1 (@lem5036068 A B f s t x h2)). Qed.
Lemma lem5036076 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term335 A B u x' s f t x'') (h2 : term345 A s t x) : term450 A B s x' f x.
Proof. exact (fun h0 : term451 A B s x' f x => @lem5036075 A B u x' f x'' s t x h1 h2). Qed.
Lemma lem5036078 (p : Prop) : (term418 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5036079 {A B : Type'} (s : A -> Prop) (x' : B -> A) (f : A -> B) (x : A) : (term450 A B s x' f x) = (term449 A B s x' f x).
Proof. exact (@lem5036078 (term449 A B s x' f x)). Qed.
Lemma lem5036080 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term335 A B u x' s f t x'') (h2 : term345 A s t x) : term449 A B s x' f x.
Proof. exact (EQ_MP (@lem5036079 A B s x' f x) (@lem5036076 A B u x' f x'' s t x h1 h2)). Qed.
Lemma lem5036086 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5036087 {A : Type'} (u : A -> Prop) (s : A -> Prop) (_64702 : A) : (term117 A s u _64702) = (term419 A u s _64702).
Proof. exact (@lem5036086 (u _64702) (term400 A s _64702)). Qed.
Lemma lem5036093 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5036094 {A : Type'} (u : A -> Prop) (s : A -> Prop) (_64702 : A) : (term420 A s u _64702) = (term421 A u s _64702).
Proof. exact (MK_COMB (@lem5036093) (@lem5036087 A u s _64702)). Qed.
Lemma lem5036100 {A : Type'} (u : A -> Prop) (s : A -> Prop) (_64702 : A) : (term419 A u s _64702) = (term419 A u s _64702).
Proof. exact (eq_refl (term419 A u s _64702)). Qed.
Lemma lem5036101 {A : Type'} (u : A -> Prop) (s : A -> Prop) (_64702 : A) : ((term117 A s u _64702) = (term419 A u s _64702)) = ((term419 A u s _64702) = (term419 A u s _64702)).
Proof. exact (MK_COMB (@lem5036094 A u s _64702) (@lem5036100 A u s _64702)). Qed.
Lemma lem5036103 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5036104 (x : Prop) : (x = x) = True.
Proof. exact (@lem5036103 Prop x). Qed.
Lemma lem5036105 {A : Type'} (u : A -> Prop) (s : A -> Prop) (_64702 : A) : ((term419 A u s _64702) = (term419 A u s _64702)) = True.
Proof. exact (@lem5036104 (term419 A u s _64702)). Qed.
Lemma lem5036106 {A : Type'} (u : A -> Prop) (s : A -> Prop) (_64702 : A) : ((term117 A s u _64702) = (term419 A u s _64702)) = True.
Proof. exact (TRANS (@lem5036101 A u s _64702) (@lem5036105 A u s _64702)). Qed.
Lemma lem5036107 {A : Type'} (u : A -> Prop) (s : A -> Prop) (_64702 : A) : True = ((term117 A s u _64702) = (term419 A u s _64702)).
Proof. exact (SYM (@lem5036106 A u s _64702)). Qed.
Lemma lem5036108 {A : Type'} (u : A -> Prop) (s : A -> Prop) (_64702 : A) : (term117 A s u _64702) = (term419 A u s _64702).
Proof. exact (EQ_MP (@lem5036107 A u s _64702) (@lem0)). Qed.
Lemma lem5036109 {A B : Type'} (_64702 : A) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term419 A u s _64702.
Proof. exact (EQ_MP (@lem5036108 A u s _64702) (@lem5034879 A B _64702 u x' s f t x'' h1)). Qed.
Lemma lem5036111 (b : Prop) (a : Prop) : (a \/ b) = (term422 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5036112 {A : Type'} (s : A -> Prop) (u : A -> Prop) (_64702 : A) : (term419 A u s _64702) = (term423 A s u _64702).
Proof. exact (@lem5036111 (term400 A s _64702) (u _64702)). Qed.
Lemma lem5036114 (a : Prop) : (term92 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5036115 {A : Type'} (s : A -> Prop) (_64702 : A) : (term424 A s _64702) = (s _64702).
Proof. exact (@lem5036114 (s _64702)). Qed.
Lemma lem5036116 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5036117 {A : Type'} (s : A -> Prop) (_64702 : A) : (term425 A s _64702) = (term51 A s _64702).
Proof. exact (MK_COMB (@lem5036116) (@lem5036115 A s _64702)). Qed.
Lemma lem5036118 {A : Type'} (u : A -> Prop) (_64702 : A) : (u _64702) = (u _64702).
Proof. exact (eq_refl (u _64702)). Qed.
Lemma lem5036119 {A : Type'} (s : A -> Prop) (u : A -> Prop) (_64702 : A) : (term423 A s u _64702) = (term53 A s u _64702).
Proof. exact (MK_COMB (@lem5036117 A s _64702) (@lem5036118 A u _64702)). Qed.
Lemma lem5036120 {A : Type'} (s : A -> Prop) (u : A -> Prop) (_64702 : A) : (term419 A u s _64702) = (term53 A s u _64702).
Proof. exact (TRANS (@lem5036112 A s u _64702) (@lem5036119 A s u _64702)). Qed.
Lemma lem5036123 {A B : Type'} (_64702 : A) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term53 A s u _64702.
Proof. exact (EQ_MP (@lem5036120 A s u _64702) (@lem5036109 A B _64702 u x' s f t x'' h1)). Qed.
Lemma lem5036124 {A B : Type'} (_64702 : A) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term53 A s u _64702.
Proof. exact (@lem5036123 A B _64702 u x' s f t x'' h1). Qed.
Lemma lem5036125 {A B : Type'} (x : A) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term452 A B s u x' f x.
Proof. exact (@lem5036124 A B (term453 A B x' f x) u x' s f t x'' h1). Qed.
Lemma lem5036128 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term335 A B u x' s f t x'') (h2 : term345 A s t x) : term449 A B u x' f x.
Proof. exact (@lem5036125 A B x u x' s f t x'' h1 (@lem5036080 A B u x' f x'' s t x h1 h2)). Qed.
Lemma lem5036129 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term335 A B u x' s f t x'') (h2 : term345 A s t x) : term450 A B u x' f x.
Proof. exact (fun h0 : term451 A B u x' f x => @lem5036128 A B u x' f x'' s t x h1 h2). Qed.
Lemma lem5036131 (p : Prop) : (term418 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5036132 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x : A) : (term450 A B u x' f x) = (term449 A B u x' f x).
Proof. exact (@lem5036131 (term449 A B u x' f x)). Qed.
Lemma lem5036133 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term335 A B u x' s f t x'') (h2 : term345 A s t x) : term449 A B u x' f x.
Proof. exact (EQ_MP (@lem5036132 A B u x' f x) (@lem5036129 A B u x' f x'' s t x h1 h2)). Qed.
Lemma lem5036135 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem5036136 {B : Type'} (x : B) : x = x.
Proof. exact (@lem5036135 B x). Qed.
Lemma lem5036137 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (@lem5036136 B (f x)). Qed.
Lemma lem5036138 {A B : Type'} (f : A -> B) (x : A) : term426 A B f x.
Proof. exact (fun h0 : term427 A B f x => @lem5036137 A B f x). Qed.
Lemma lem5036140 (p : Prop) : (term418 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5036141 {A B : Type'} (f : A -> B) (x : A) : (term426 A B f x) = ((f x) = (f x)).
Proof. exact (@lem5036140 ((f x) = (f x))). Qed.
Lemma lem5036142 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (EQ_MP (@lem5036141 A B f x) (@lem5036138 A B f x)). Qed.
Lemma lem5036144 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term345 A s t x) : t x.
Proof. exact (proj2 (@lem5034369 A s t x h1)). Qed.
Lemma lem5036145 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term345 A s t x) : term417 A t x.
Proof. exact (fun h0 : term400 A t x => @lem5036144 A s t x h1). Qed.
Lemma lem5036147 (p : Prop) : (term418 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5036148 {A : Type'} (t : A -> Prop) (x : A) : (term417 A t x) = (t x).
Proof. exact (@lem5036147 (t x)). Qed.
Lemma lem5036149 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term345 A s t x) : t x.
Proof. exact (EQ_MP (@lem5036148 A t x) (@lem5036145 A s t x h1)). Qed.
Lemma lem5036151 (b : Prop) (a : Prop) : (a \/ b) = (term422 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5036152 {A B : Type'} (t : A -> Prop) (_64705 : A) (f : A -> B) (x' : B -> A) (_64704 : B) : (term408 A B x' _64704 f t _64705) = (term462 A B t _64705 f x' _64704).
Proof. exact (@lem5036151 (term121 A B _64704 f t _64705) (_64704 = (term366 A B f x' _64704))). Qed.
Lemma lem5036154 (a : Prop) (b : Prop) : (term438 a b) = (term439 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5036155 {A B : Type'} (_64704 : B) (f : A -> B) (t : A -> Prop) (_64705 : A) : (term440 A B _64704 f t _64705) = (term441 A B _64704 f t _64705).
Proof. exact (@lem5036154 (term406 A B _64704 f _64705) (term400 A t _64705)). Qed.
Lemma lem5036157 (a : Prop) : (term92 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5036158 {A B : Type'} (_64704 : B) (f : A -> B) (_64705 : A) : (term442 A B _64704 f _64705) = (_64704 = (f _64705)).
Proof. exact (@lem5036157 (_64704 = (f _64705))). Qed.
Lemma lem5036159 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5036160 {A B : Type'} (_64704 : B) (f : A -> B) (_64705 : A) : (term443 A B _64704 f _64705) = (term60 A B _64704 f _64705).
Proof. exact (MK_COMB (@lem5036159) (@lem5036158 A B _64704 f _64705)). Qed.
Lemma lem5036162 (a : Prop) : (term92 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5036163 {A : Type'} (t : A -> Prop) (_64705 : A) : (term424 A t _64705) = (t _64705).
Proof. exact (@lem5036162 (t _64705)). Qed.
Lemma lem5036164 {A B : Type'} (_64704 : B) (f : A -> B) (t : A -> Prop) (_64705 : A) : (term441 A B _64704 f t _64705) = (term62 A B _64704 f t _64705).
Proof. exact (MK_COMB (@lem5036160 A B _64704 f _64705) (@lem5036163 A t _64705)). Qed.
Lemma lem5036165 {A B : Type'} (_64704 : B) (f : A -> B) (t : A -> Prop) (_64705 : A) : (term440 A B _64704 f t _64705) = (term62 A B _64704 f t _64705).
Proof. exact (TRANS (@lem5036155 A B _64704 f t _64705) (@lem5036164 A B _64704 f t _64705)). Qed.
Lemma lem5036166 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5036167 {A B : Type'} (_64704 : B) (f : A -> B) (t : A -> Prop) (_64705 : A) : (term444 A B _64704 f t _64705) = (term445 A B _64704 f t _64705).
Proof. exact (MK_COMB (@lem5036166) (@lem5036165 A B _64704 f t _64705)). Qed.
Lemma lem5036168 {A B : Type'} (f : A -> B) (x' : B -> A) (_64704 : B) : (_64704 = (term366 A B f x' _64704)) = (_64704 = (term366 A B f x' _64704)).
Proof. exact (eq_refl (_64704 = (term366 A B f x' _64704))). Qed.
Lemma lem5036169 {A B : Type'} (t : A -> Prop) (_64705 : A) (f : A -> B) (x' : B -> A) (_64704 : B) : (term462 A B t _64705 f x' _64704) = (term463 A B t _64705 f x' _64704).
Proof. exact (MK_COMB (@lem5036167 A B _64704 f t _64705) (@lem5036168 A B f x' _64704)). Qed.
Lemma lem5036170 {A B : Type'} (t : A -> Prop) (_64705 : A) (f : A -> B) (x' : B -> A) (_64704 : B) : (term408 A B x' _64704 f t _64705) = (term463 A B t _64705 f x' _64704).
Proof. exact (TRANS (@lem5036152 A B t _64705 f x' _64704) (@lem5036169 A B t _64705 f x' _64704)). Qed.
Lemma lem5036172 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term345 A s t x) : term447 A B f t x.
Proof. exact (conj (@lem5036142 A B f x) (@lem5036149 A s t x h1)). Qed.
Lemma lem5036174 {A B : Type'} (_64705 : A) (_64704 : B) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term463 A B t _64705 f x' _64704.
Proof. exact (EQ_MP (@lem5036170 A B t _64705 f x' _64704) (@lem5034923 A B _64704 _64705 u x' s f t x'' h1)). Qed.
Lemma lem5036175 {A B : Type'} (_64705 : A) (_64704 : B) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term463 A B t _64705 f x' _64704.
Proof. exact (@lem5036174 A B _64705 _64704 u x' s f t x'' h1). Qed.
Lemma lem5036176 {A B : Type'} (x : A) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term464 A B t x' f x.
Proof. exact (@lem5036175 A B x (f x) u x' s f t x'' h1). Qed.
Lemma lem5036179 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term335 A B u x' s f t x'') (h2 : term345 A s t x) : (f x) = (term465 A B x' f x).
Proof. exact (@lem5036176 A B x u x' s f t x'' h1 (@lem5036172 A B f s t x h2)). Qed.
Lemma lem5036180 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term335 A B u x' s f t x'') (h2 : term345 A s t x) : term466 A B x' f x.
Proof. exact (fun h0 : term467 A B x' f x => @lem5036179 A B u x' f x'' s t x h1 h2). Qed.
Lemma lem5036182 (p : Prop) : (term418 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5036183 {A B : Type'} (x' : B -> A) (f : A -> B) (x : A) : (term466 A B x' f x) = ((f x) = (term465 A B x' f x)).
Proof. exact (@lem5036182 ((f x) = (term465 A B x' f x))). Qed.
Lemma lem5036184 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term335 A B u x' s f t x'') (h2 : term345 A s t x) : (f x) = (term465 A B x' f x).
Proof. exact (EQ_MP (@lem5036183 A B x' f x) (@lem5036180 A B u x' f x'' s t x h1 h2)). Qed.
Lemma lem5036210 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5036211 {A B : Type'} (_64700 : A) (f : A -> B) (_64701 : A) : (term468 A B f _64700 _64701) = (term469 A B _64700 f _64701).
Proof. exact (@lem5036210 (_64700 = _64701) (term403 A B _64700 f _64701)). Qed.
Lemma lem5036221 {A : Type'} (u : A -> Prop) (_64701 : A) : (term105 A u _64701) = (term105 A u _64701).
Proof. exact (eq_refl (term105 A u _64701)). Qed.
Lemma lem5036222 {A B : Type'} (u : A -> Prop) (_64700 : A) (f : A -> B) (_64701 : A) : (term402 A B u f _64700 _64701) = (term470 A B u _64700 f _64701).
Proof. exact (MK_COMB (@lem5036221 A u _64701) (@lem5036211 A B _64700 f _64701)). Qed.
Lemma lem5036226 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5036227 {A B : Type'} (u : A -> Prop) (_64700 : A) (f : A -> B) (_64701 : A) : (term470 A B u _64700 f _64701) = (term471 A B u _64700 f _64701).
Proof. exact (@lem5036226 (_64700 = _64701) (term400 A u _64701) (term403 A B _64700 f _64701)). Qed.
Lemma lem5036247 {A B : Type'} (u : A -> Prop) (_64700 : A) (f : A -> B) (_64701 : A) : (term402 A B u f _64700 _64701) = (term471 A B u _64700 f _64701).
Proof. exact (TRANS (@lem5036222 A B u _64700 f _64701) (@lem5036227 A B u _64700 f _64701)). Qed.
Lemma lem5036248 {A : Type'} (u : A -> Prop) (_64700 : A) : (term105 A u _64700) = (term105 A u _64700).
Proof. exact (eq_refl (term105 A u _64700)). Qed.
Lemma lem5036249 {A B : Type'} (u : A -> Prop) (_64700 : A) (f : A -> B) (_64701 : A) : (term404 A B u f _64700 _64701) = (term472 A B u _64700 f _64701).
Proof. exact (MK_COMB (@lem5036248 A u _64700) (@lem5036247 A B u _64700 f _64701)). Qed.
Lemma lem5036253 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5036254 {A B : Type'} (u : A -> Prop) (_64700 : A) (f : A -> B) (_64701 : A) : (term472 A B u _64700 f _64701) = (term473 A B u _64700 f _64701).
Proof. exact (@lem5036253 (_64700 = _64701) (term400 A u _64700) (term104 A B u _64700 f _64701)). Qed.
Lemma lem5036284 {A B : Type'} (u : A -> Prop) (_64700 : A) (f : A -> B) (_64701 : A) : (term404 A B u f _64700 _64701) = (term473 A B u _64700 f _64701).
Proof. exact (TRANS (@lem5036249 A B u _64700 f _64701) (@lem5036254 A B u _64700 f _64701)). Qed.
Lemma lem5036285 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5036286 {A B : Type'} (u : A -> Prop) (_64700 : A) (f : A -> B) (_64701 : A) : (term474 A B u f _64700 _64701) = (term475 A B u _64700 f _64701).
Proof. exact (MK_COMB (@lem5036285) (@lem5036284 A B u _64700 f _64701)). Qed.
Lemma lem5036316 {A B : Type'} (u : A -> Prop) (_64700 : A) (f : A -> B) (_64701 : A) : (term473 A B u _64700 f _64701) = (term473 A B u _64700 f _64701).
Proof. exact (eq_refl (term473 A B u _64700 f _64701)). Qed.
Lemma lem5036317 {A B : Type'} (u : A -> Prop) (_64700 : A) (f : A -> B) (_64701 : A) : ((term404 A B u f _64700 _64701) = (term473 A B u _64700 f _64701)) = ((term473 A B u _64700 f _64701) = (term473 A B u _64700 f _64701)).
Proof. exact (MK_COMB (@lem5036286 A B u _64700 f _64701) (@lem5036316 A B u _64700 f _64701)). Qed.
Lemma lem5036319 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5036320 (x : Prop) : (x = x) = True.
Proof. exact (@lem5036319 Prop x). Qed.
Lemma lem5036321 {A B : Type'} (u : A -> Prop) (_64700 : A) (f : A -> B) (_64701 : A) : ((term473 A B u _64700 f _64701) = (term473 A B u _64700 f _64701)) = True.
Proof. exact (@lem5036320 (term473 A B u _64700 f _64701)). Qed.
Lemma lem5036322 {A B : Type'} (u : A -> Prop) (_64700 : A) (f : A -> B) (_64701 : A) : ((term404 A B u f _64700 _64701) = (term473 A B u _64700 f _64701)) = True.
Proof. exact (TRANS (@lem5036317 A B u _64700 f _64701) (@lem5036321 A B u _64700 f _64701)). Qed.
Lemma lem5036323 {A B : Type'} (u : A -> Prop) (_64700 : A) (f : A -> B) (_64701 : A) : True = ((term404 A B u f _64700 _64701) = (term473 A B u _64700 f _64701)).
Proof. exact (SYM (@lem5036322 A B u _64700 f _64701)). Qed.
Lemma lem5036324 {A B : Type'} (u : A -> Prop) (_64700 : A) (f : A -> B) (_64701 : A) : (term404 A B u f _64700 _64701) = (term473 A B u _64700 f _64701).
Proof. exact (EQ_MP (@lem5036323 A B u _64700 f _64701) (@lem0)). Qed.
Lemma lem5036325 {A B : Type'} (_64700 : A) (_64701 : A) (u : A -> Prop) (f : A -> B) (h1 : term48 A B u f) : term473 A B u _64700 f _64701.
Proof. exact (EQ_MP (@lem5036324 A B u _64700 f _64701) (@lem5034873 A B _64700 _64701 u f h1)). Qed.
Lemma lem5036327 (b : Prop) (a : Prop) : (a \/ b) = (term422 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5036328 {A B : Type'} (u : A -> Prop) (f : A -> B) (_64700 : A) (_64701 : A) : (term473 A B u _64700 f _64701) = (term476 A B u f _64700 _64701).
Proof. exact (@lem5036327 (term107 A B u _64700 f _64701) (_64700 = _64701)). Qed.
Lemma lem5036330 (a : Prop) (b : Prop) : (term438 a b) = (term439 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5036331 {A B : Type'} (u : A -> Prop) (_64700 : A) (f : A -> B) (_64701 : A) : (term477 A B u _64700 f _64701) = (term478 A B u _64700 f _64701).
Proof. exact (@lem5036330 (term400 A u _64700) (term104 A B u _64700 f _64701)). Qed.
Lemma lem5036333 (a : Prop) : (term92 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5036334 {A : Type'} (u : A -> Prop) (_64700 : A) : (term424 A u _64700) = (u _64700).
Proof. exact (@lem5036333 (u _64700)). Qed.
Lemma lem5036335 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5036336 {A : Type'} (u : A -> Prop) (_64700 : A) : (term479 A u _64700) = (term32 A u _64700).
Proof. exact (MK_COMB (@lem5036335) (@lem5036334 A u _64700)). Qed.
Lemma lem5036338 (a : Prop) (b : Prop) : (term438 a b) = (term439 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5036339 {A B : Type'} (u : A -> Prop) (_64700 : A) (f : A -> B) (_64701 : A) : (term480 A B u _64700 f _64701) = (term481 A B u _64700 f _64701).
Proof. exact (@lem5036338 (term400 A u _64701) (term403 A B _64700 f _64701)). Qed.
Lemma lem5036341 (a : Prop) : (term92 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5036342 {A : Type'} (u : A -> Prop) (_64701 : A) : (term424 A u _64701) = (u _64701).
Proof. exact (@lem5036341 (u _64701)). Qed.
Lemma lem5036343 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5036344 {A : Type'} (u : A -> Prop) (_64701 : A) : (term479 A u _64701) = (term32 A u _64701).
Proof. exact (MK_COMB (@lem5036343) (@lem5036342 A u _64701)). Qed.
Lemma lem5036346 (a : Prop) : (term92 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5036347 {A B : Type'} (_64700 : A) (f : A -> B) (_64701 : A) : (term482 A B _64700 f _64701) = ((f _64700) = (f _64701)).
Proof. exact (@lem5036346 ((f _64700) = (f _64701))). Qed.
Lemma lem5036348 {A B : Type'} (u : A -> Prop) (_64700 : A) (f : A -> B) (_64701 : A) : (term481 A B u _64700 f _64701) = (term34 A B u _64700 f _64701).
Proof. exact (MK_COMB (@lem5036344 A u _64701) (@lem5036347 A B _64700 f _64701)). Qed.
Lemma lem5036349 {A B : Type'} (u : A -> Prop) (_64700 : A) (f : A -> B) (_64701 : A) : (term480 A B u _64700 f _64701) = (term34 A B u _64700 f _64701).
Proof. exact (TRANS (@lem5036339 A B u _64700 f _64701) (@lem5036348 A B u _64700 f _64701)). Qed.
Lemma lem5036350 {A B : Type'} (u : A -> Prop) (_64700 : A) (f : A -> B) (_64701 : A) : (term478 A B u _64700 f _64701) = (term36 A B u _64700 f _64701).
Proof. exact (MK_COMB (@lem5036336 A u _64700) (@lem5036349 A B u _64700 f _64701)). Qed.
Lemma lem5036351 {A B : Type'} (u : A -> Prop) (_64700 : A) (f : A -> B) (_64701 : A) : (term477 A B u _64700 f _64701) = (term36 A B u _64700 f _64701).
Proof. exact (TRANS (@lem5036331 A B u _64700 f _64701) (@lem5036350 A B u _64700 f _64701)). Qed.
Lemma lem5036352 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5036353 {A B : Type'} (u : A -> Prop) (_64700 : A) (f : A -> B) (_64701 : A) : (term483 A B u _64700 f _64701) = (term38 A B u _64700 f _64701).
Proof. exact (MK_COMB (@lem5036352) (@lem5036351 A B u _64700 f _64701)). Qed.
Lemma lem5036354 {A : Type'} (_64700 : A) (_64701 : A) : (_64700 = _64701) = (_64700 = _64701).
Proof. exact (eq_refl (_64700 = _64701)). Qed.
Lemma lem5036355 {A B : Type'} (u : A -> Prop) (f : A -> B) (_64700 : A) (_64701 : A) : (term476 A B u f _64700 _64701) = (term40 A B u f _64700 _64701).
Proof. exact (MK_COMB (@lem5036353 A B u _64700 f _64701) (@lem5036354 A _64700 _64701)). Qed.
Lemma lem5036356 {A B : Type'} (u : A -> Prop) (f : A -> B) (_64700 : A) (_64701 : A) : (term473 A B u _64700 f _64701) = (term40 A B u f _64700 _64701).
Proof. exact (TRANS (@lem5036328 A B u f _64700 _64701) (@lem5036355 A B u f _64700 _64701)). Qed.
Lemma lem5036358 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term335 A B u x' s f t x'') (h2 : term345 A s t x) : term484 A B u x' f x.
Proof. exact (conj (@lem5036133 A B u x' f x'' s t x h1 h2) (@lem5036184 A B u x' f x'' s t x h1 h2)). Qed.
Lemma lem5036359 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term335 A B u x' s f t x'') (h2 : term345 A s t x) : term485 A B u x' f x.
Proof. exact (conj (@lem5036029 A B u x' f x'' s t x h1 h2) (@lem5036358 A B u x' f x'' s t x h1 h2)). Qed.
Lemma lem5036361 {A B : Type'} (_64700 : A) (_64701 : A) (u : A -> Prop) (f : A -> B) (h1 : term48 A B u f) : term40 A B u f _64700 _64701.
Proof. exact (EQ_MP (@lem5036356 A B u f _64700 _64701) (@lem5036325 A B _64700 _64701 u f h1)). Qed.
Lemma lem5036362 {A B : Type'} (_64700 : A) (_64701 : A) (u : A -> Prop) (f : A -> B) (h1 : term48 A B u f) : term40 A B u f _64700 _64701.
Proof. exact (@lem5036361 A B _64700 _64701 u f h1). Qed.
Lemma lem5036363 {A B : Type'} (x' : B -> A) (x : A) (u : A -> Prop) (f : A -> B) (h1 : term48 A B u f) : term486 A B u x' f x.
Proof. exact (@lem5036362 A B x (term453 A B x' f x) u f h1). Qed.
Lemma lem5036366 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term48 A B u f) (h2 : term335 A B u x' s f t x'') (h3 : term345 A s t x) : x = (term453 A B x' f x).
Proof. exact (@lem5036363 A B x' x u f h1 (@lem5036359 A B u x' f x'' s t x h2 h3)). Qed.
Lemma lem5036367 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term48 A B u f) (h2 : term335 A B u x' s f t x'') (h3 : term345 A s t x) : term487 A B x' f x.
Proof. exact (fun h0 : term488 A B x' f x => @lem5036366 A B u x' f x'' s t x h1 h2 h3). Qed.
Lemma lem5036369 (p : Prop) : (term418 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5036370 {A B : Type'} (x' : B -> A) (f : A -> B) (x : A) : (term487 A B x' f x) = (x = (term453 A B x' f x)).
Proof. exact (@lem5036369 (x = (term453 A B x' f x))). Qed.
Lemma lem5036371 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term48 A B u f) (h2 : term335 A B u x' s f t x'') (h3 : term345 A s t x) : x = (term453 A B x' f x).
Proof. exact (EQ_MP (@lem5036370 A B x' f x) (@lem5036367 A B u x' f x'' s t x h1 h2 h3)). Qed.
Lemma lem5036373 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem5036374 {A : Type'} (x : A) : x = x.
Proof. exact (@lem5036373 A x). Qed.
Lemma lem5036375 {A : Type'} (x : A) : term489 A x.
Proof. exact (fun h0 : term490 A x => @lem5036374 A x). Qed.
Lemma lem5036377 (p : Prop) : (term418 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5036378 {A : Type'} (x : A) : (term489 A x) = (x = x).
Proof. exact (@lem5036377 (x = x)). Qed.
Lemma lem5036379 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem5036378 A x) (@lem5036375 A x)). Qed.
Lemma lem5036397 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5036398 {A : Type'} (y : A) (x : A) (z : A) : (term491 A x y z) = (term492 A y x z).
Proof. exact (@lem5036397 (y = z) (term493 A x z)). Qed.
Lemma lem5036408 {A : Type'} (x : A) (y : A) : (term494 A x y) = (term494 A x y).
Proof. exact (eq_refl (term494 A x y)). Qed.
Lemma lem5036409 {A : Type'} (y : A) (x : A) (z : A) : (term416 A x y z) = (term495 A y x z).
Proof. exact (MK_COMB (@lem5036408 A x y) (@lem5036398 A y x z)). Qed.
Lemma lem5036413 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5036414 {A : Type'} (y : A) (x : A) (z : A) : (term495 A y x z) = (term496 A y x z).
Proof. exact (@lem5036413 (y = z) (term493 A x y) (term493 A x z)). Qed.
Lemma lem5036436 {A : Type'} (y : A) (x : A) (z : A) : (term416 A x y z) = (term496 A y x z).
Proof. exact (TRANS (@lem5036409 A y x z) (@lem5036414 A y x z)). Qed.
Lemma lem5036437 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5036438 {A : Type'} (y : A) (x : A) (z : A) : (term497 A x y z) = (term498 A y x z).
Proof. exact (MK_COMB (@lem5036437) (@lem5036436 A y x z)). Qed.
Lemma lem5036460 {A : Type'} (y : A) (x : A) (z : A) : (term496 A y x z) = (term496 A y x z).
Proof. exact (eq_refl (term496 A y x z)). Qed.
Lemma lem5036461 {A : Type'} (y : A) (x : A) (z : A) : ((term416 A x y z) = (term496 A y x z)) = ((term496 A y x z) = (term496 A y x z)).
Proof. exact (MK_COMB (@lem5036438 A y x z) (@lem5036460 A y x z)). Qed.
Lemma lem5036463 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5036464 (x : Prop) : (x = x) = True.
Proof. exact (@lem5036463 Prop x). Qed.
Lemma lem5036465 {A : Type'} (y : A) (x : A) (z : A) : ((term496 A y x z) = (term496 A y x z)) = True.
Proof. exact (@lem5036464 (term496 A y x z)). Qed.
Lemma lem5036466 {A : Type'} (y : A) (x : A) (z : A) : ((term416 A x y z) = (term496 A y x z)) = True.
Proof. exact (TRANS (@lem5036461 A y x z) (@lem5036465 A y x z)). Qed.
Lemma lem5036467 {A : Type'} (y : A) (x : A) (z : A) : True = ((term416 A x y z) = (term496 A y x z)).
Proof. exact (SYM (@lem5036466 A y x z)). Qed.
Lemma lem5036468 {A : Type'} (y : A) (x : A) (z : A) : (term416 A x y z) = (term496 A y x z).
Proof. exact (EQ_MP (@lem5036467 A y x z) (@lem0)). Qed.
Lemma lem5036469 {A : Type'} (y : A) (x : A) (z : A) : term496 A y x z.
Proof. exact (EQ_MP (@lem5036468 A y x z) (@lem5035969 A x y z)). Qed.
Lemma lem5036471 (b : Prop) (a : Prop) : (a \/ b) = (term422 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5036472 {A : Type'} (x : A) (y : A) (z : A) : (term496 A y x z) = (term499 A x y z).
Proof. exact (@lem5036471 (term500 A y x z) (y = z)). Qed.
Lemma lem5036474 (a : Prop) (b : Prop) : (term438 a b) = (term439 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5036475 {A : Type'} (y : A) (x : A) (z : A) : (term501 A y x z) = (term502 A y x z).
Proof. exact (@lem5036474 (term493 A x y) (term493 A x z)). Qed.
Lemma lem5036477 (a : Prop) : (term92 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5036478 {A : Type'} (x : A) (y : A) : (term503 A x y) = (x = y).
Proof. exact (@lem5036477 (x = y)). Qed.
Lemma lem5036479 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5036480 {A : Type'} (x : A) (y : A) : (term504 A x y) = (term505 A x y).
Proof. exact (MK_COMB (@lem5036479) (@lem5036478 A x y)). Qed.
Lemma lem5036482 (a : Prop) : (term92 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5036483 {A : Type'} (x : A) (z : A) : (term503 A x z) = (x = z).
Proof. exact (@lem5036482 (x = z)). Qed.
Lemma lem5036484 {A : Type'} (y : A) (x : A) (z : A) : (term502 A y x z) = (term506 A y x z).
Proof. exact (MK_COMB (@lem5036480 A x y) (@lem5036483 A x z)). Qed.
Lemma lem5036485 {A : Type'} (y : A) (x : A) (z : A) : (term501 A y x z) = (term506 A y x z).
Proof. exact (TRANS (@lem5036475 A y x z) (@lem5036484 A y x z)). Qed.
Lemma lem5036486 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5036487 {A : Type'} (y : A) (x : A) (z : A) : (term507 A y x z) = (term508 A y x z).
Proof. exact (MK_COMB (@lem5036486) (@lem5036485 A y x z)). Qed.
Lemma lem5036488 {A : Type'} (y : A) (z : A) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem5036489 {A : Type'} (x : A) (y : A) (z : A) : (term499 A x y z) = (term509 A x y z).
Proof. exact (MK_COMB (@lem5036487 A y x z) (@lem5036488 A y z)). Qed.
Lemma lem5036490 {A : Type'} (x : A) (y : A) (z : A) : (term496 A y x z) = (term509 A x y z).
Proof. exact (TRANS (@lem5036472 A x y z) (@lem5036489 A x y z)). Qed.
Lemma lem5036492 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term48 A B u f) (h2 : term335 A B u x' s f t x'') (h3 : term345 A s t x) : term510 A B x' f x.
Proof. exact (conj (@lem5036371 A B u x' f x'' s t x h1 h2 h3) (@lem5036379 A x)). Qed.
Lemma lem5036494 {A : Type'} (x : A) (y : A) (z : A) : term509 A x y z.
Proof. exact (EQ_MP (@lem5036490 A x y z) (@lem5036469 A y x z)). Qed.
Lemma lem5036495 {A : Type'} (x : A) (y : A) (z : A) : term509 A x y z.
Proof. exact (@lem5036494 A x y z). Qed.
Lemma lem5036496 {A B : Type'} (x' : B -> A) (f : A -> B) (x : A) : term511 A B x' f x.
Proof. exact (@lem5036495 A x (term453 A B x' f x) x). Qed.
Lemma lem5036499 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term48 A B u f) (h2 : term335 A B u x' s f t x'') (h3 : term345 A s t x) : (term453 A B x' f x) = x.
Proof. exact (@lem5036496 A B x' f x (@lem5036492 A B u x' f x'' s t x h1 h2 h3)). Qed.
Lemma lem5036500 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term48 A B u f) (h2 : term335 A B u x' s f t x'') (h3 : term345 A s t x) : term512 A B x' f x.
Proof. exact (fun h0 : term513 A B x' f x => @lem5036499 A B u x' f x'' s t x h1 h2 h3). Qed.
Lemma lem5036502 (p : Prop) : (term418 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5036503 {A B : Type'} (x' : B -> A) (f : A -> B) (x : A) : (term512 A B x' f x) = ((term453 A B x' f x) = x).
Proof. exact (@lem5036502 ((term453 A B x' f x) = x)). Qed.
Lemma lem5036504 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term48 A B u f) (h2 : term335 A B u x' s f t x'') (h3 : term345 A s t x) : (term453 A B x' f x) = x.
Proof. exact (EQ_MP (@lem5036503 A B x' f x) (@lem5036500 A B u x' f x'' s t x h1 h2 h3)). Qed.
Lemma lem5036506 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem5036507 {B : Type'} (x : B) : x = x.
Proof. exact (@lem5036506 B x). Qed.
Lemma lem5036508 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (@lem5036507 B (f x)). Qed.
Lemma lem5036509 {A B : Type'} (f : A -> B) (x : A) : term426 A B f x.
Proof. exact (fun h0 : term427 A B f x => @lem5036508 A B f x). Qed.
Lemma lem5036511 (p : Prop) : (term418 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5036512 {A B : Type'} (f : A -> B) (x : A) : (term426 A B f x) = ((f x) = (f x)).
Proof. exact (@lem5036511 ((f x) = (f x))). Qed.
Lemma lem5036513 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (EQ_MP (@lem5036512 A B f x) (@lem5036509 A B f x)). Qed.
Lemma lem5036515 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term345 A s t x) : t x.
Proof. exact (proj2 (@lem5034369 A s t x h1)). Qed.
Lemma lem5036516 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term345 A s t x) : term417 A t x.
Proof. exact (fun h0 : term400 A t x => @lem5036515 A s t x h1). Qed.
Lemma lem5036518 (p : Prop) : (term418 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5036519 {A : Type'} (t : A -> Prop) (x : A) : (term417 A t x) = (t x).
Proof. exact (@lem5036518 (t x)). Qed.
Lemma lem5036520 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term345 A s t x) : t x.
Proof. exact (EQ_MP (@lem5036519 A t x) (@lem5036516 A s t x h1)). Qed.
Lemma lem5036521 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term345 A s t x) : term447 A B f t x.
Proof. exact (conj (@lem5036513 A B f x) (@lem5036520 A s t x h1)). Qed.
Lemma lem5036523 {A B : Type'} (_64705 : A) (_64704 : B) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term446 A B f t _64705 s x' _64704.
Proof. exact (EQ_MP (@lem5036066 A B f t _64705 s x' _64704) (@lem5034933 A B _64704 _64705 u x' s f t x'' h1)). Qed.
Lemma lem5036524 {A B : Type'} (_64705 : A) (_64704 : B) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term446 A B f t _64705 s x' _64704.
Proof. exact (@lem5036523 A B _64705 _64704 u x' s f t x'' h1). Qed.
Lemma lem5036525 {A B : Type'} (x : A) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term335 A B u x' s f t x'') : term448 A B t s x' f x.
Proof. exact (@lem5036524 A B x (f x) u x' s f t x'' h1). Qed.
Lemma lem5036528 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term335 A B u x' s f t x'') (h2 : term345 A s t x) : term449 A B s x' f x.
Proof. exact (@lem5036525 A B x u x' s f t x'' h1 (@lem5036521 A B f s t x h2)). Qed.
Lemma lem5036529 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term335 A B u x' s f t x'') (h2 : term345 A s t x) : term450 A B s x' f x.
Proof. exact (fun h0 : term451 A B s x' f x => @lem5036528 A B u x' f x'' s t x h1 h2). Qed.
Lemma lem5036531 (p : Prop) : (term418 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5036532 {A B : Type'} (s : A -> Prop) (x' : B -> A) (f : A -> B) (x : A) : (term450 A B s x' f x) = (term449 A B s x' f x).
Proof. exact (@lem5036531 (term449 A B s x' f x)). Qed.
Lemma lem5036533 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term335 A B u x' s f t x'') (h2 : term345 A s t x) : term449 A B s x' f x.
Proof. exact (EQ_MP (@lem5036532 A B s x' f x) (@lem5036529 A B u x' f x'' s t x h1 h2)). Qed.
Lemma lem5036539 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5036540 {A : Type'} (_64723 : A) (s : A -> Prop) (_64722 : A) : (term415 A _64723 s _64722) = (term514 A _64723 s _64722).
Proof. exact (@lem5036539 (s _64723) (term493 A _64722 _64723) (term400 A s _64722)). Qed.
Lemma lem5036554 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5036555 {A : Type'} (s : A -> Prop) (_64722 : A) (_64723 : A) : (term515 A _64723 s _64722) = (term516 A s _64722 _64723).
Proof. exact (@lem5036554 (term400 A s _64722) (term493 A _64722 _64723)). Qed.
Lemma lem5036563 {A : Type'} (s : A -> Prop) (_64723 : A) : (term517 A s _64723) = (term517 A s _64723).
Proof. exact (eq_refl (term517 A s _64723)). Qed.
Lemma lem5036564 {A : Type'} (s : A -> Prop) (_64722 : A) (_64723 : A) : (term514 A _64723 s _64722) = (term518 A s _64722 _64723).
Proof. exact (MK_COMB (@lem5036563 A s _64723) (@lem5036555 A s _64722 _64723)). Qed.
Lemma lem5036575 {A : Type'} (s : A -> Prop) (_64722 : A) (_64723 : A) : (term415 A _64723 s _64722) = (term518 A s _64722 _64723).
Proof. exact (TRANS (@lem5036540 A _64723 s _64722) (@lem5036564 A s _64722 _64723)). Qed.
Lemma lem5036576 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5036577 {A : Type'} (s : A -> Prop) (_64722 : A) (_64723 : A) : (term519 A _64723 s _64722) = (term520 A s _64722 _64723).
Proof. exact (MK_COMB (@lem5036576) (@lem5036575 A s _64722 _64723)). Qed.
Lemma lem5036591 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5036592 {A : Type'} (s : A -> Prop) (_64722 : A) (_64723 : A) : (term515 A _64723 s _64722) = (term516 A s _64722 _64723).
Proof. exact (@lem5036591 (term400 A s _64722) (term493 A _64722 _64723)). Qed.
Lemma lem5036600 {A : Type'} (s : A -> Prop) (_64723 : A) : (term517 A s _64723) = (term517 A s _64723).
Proof. exact (eq_refl (term517 A s _64723)). Qed.
Lemma lem5036601 {A : Type'} (s : A -> Prop) (_64722 : A) (_64723 : A) : (term514 A _64723 s _64722) = (term518 A s _64722 _64723).
Proof. exact (MK_COMB (@lem5036600 A s _64723) (@lem5036592 A s _64722 _64723)). Qed.
Lemma lem5036612 {A : Type'} (s : A -> Prop) (_64722 : A) (_64723 : A) : ((term415 A _64723 s _64722) = (term514 A _64723 s _64722)) = ((term518 A s _64722 _64723) = (term518 A s _64722 _64723)).
Proof. exact (MK_COMB (@lem5036577 A s _64722 _64723) (@lem5036601 A s _64722 _64723)). Qed.
Lemma lem5036614 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5036615 (x : Prop) : (x = x) = True.
Proof. exact (@lem5036614 Prop x). Qed.
Lemma lem5036616 {A : Type'} (s : A -> Prop) (_64722 : A) (_64723 : A) : ((term518 A s _64722 _64723) = (term518 A s _64722 _64723)) = True.
Proof. exact (@lem5036615 (term518 A s _64722 _64723)). Qed.
Lemma lem5036617 {A : Type'} (_64723 : A) (s : A -> Prop) (_64722 : A) : ((term415 A _64723 s _64722) = (term514 A _64723 s _64722)) = True.
Proof. exact (TRANS (@lem5036612 A s _64722 _64723) (@lem5036616 A s _64722 _64723)). Qed.
Lemma lem5036618 {A : Type'} (_64723 : A) (s : A -> Prop) (_64722 : A) : True = ((term415 A _64723 s _64722) = (term514 A _64723 s _64722)).
Proof. exact (SYM (@lem5036617 A _64723 s _64722)). Qed.
Lemma lem5036619 {A : Type'} (_64723 : A) (s : A -> Prop) (_64722 : A) : (term415 A _64723 s _64722) = (term514 A _64723 s _64722).
Proof. exact (EQ_MP (@lem5036618 A _64723 s _64722) (@lem0)). Qed.
Lemma lem5036620 {A : Type'} (_64723 : A) (s : A -> Prop) (_64722 : A) : term514 A _64723 s _64722.
Proof. exact (EQ_MP (@lem5036619 A _64723 s _64722) (@lem5035929 A _64723 s _64722)). Qed.
Lemma lem5036622 (b : Prop) (a : Prop) : (a \/ b) = (term422 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5036623 {A : Type'} (_64722 : A) (s : A -> Prop) (_64723 : A) : (term514 A _64723 s _64722) = (term521 A _64722 s _64723).
Proof. exact (@lem5036622 (term515 A _64723 s _64722) (s _64723)). Qed.
Lemma lem5036625 (a : Prop) (b : Prop) : (term438 a b) = (term439 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5036626 {A : Type'} (_64723 : A) (s : A -> Prop) (_64722 : A) : (term522 A _64723 s _64722) = (term523 A _64723 s _64722).
Proof. exact (@lem5036625 (term493 A _64722 _64723) (term400 A s _64722)). Qed.
Lemma lem5036628 (a : Prop) : (term92 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5036629 {A : Type'} (_64722 : A) (_64723 : A) : (term503 A _64722 _64723) = (_64722 = _64723).
Proof. exact (@lem5036628 (_64722 = _64723)). Qed.
Lemma lem5036630 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5036631 {A : Type'} (_64722 : A) (_64723 : A) : (term504 A _64722 _64723) = (term505 A _64722 _64723).
Proof. exact (MK_COMB (@lem5036630) (@lem5036629 A _64722 _64723)). Qed.
Lemma lem5036633 (a : Prop) : (term92 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5036634 {A : Type'} (s : A -> Prop) (_64722 : A) : (term424 A s _64722) = (s _64722).
Proof. exact (@lem5036633 (s _64722)). Qed.
Lemma lem5036635 {A : Type'} (_64723 : A) (s : A -> Prop) (_64722 : A) : (term523 A _64723 s _64722) = (term524 A _64723 s _64722).
Proof. exact (MK_COMB (@lem5036631 A _64722 _64723) (@lem5036634 A s _64722)). Qed.
Lemma lem5036636 {A : Type'} (_64723 : A) (s : A -> Prop) (_64722 : A) : (term522 A _64723 s _64722) = (term524 A _64723 s _64722).
Proof. exact (TRANS (@lem5036626 A _64723 s _64722) (@lem5036635 A _64723 s _64722)). Qed.
Lemma lem5036637 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5036638 {A : Type'} (_64723 : A) (s : A -> Prop) (_64722 : A) : (term525 A _64723 s _64722) = (term526 A _64723 s _64722).
Proof. exact (MK_COMB (@lem5036637) (@lem5036636 A _64723 s _64722)). Qed.
Lemma lem5036639 {A : Type'} (s : A -> Prop) (_64723 : A) : (s _64723) = (s _64723).
Proof. exact (eq_refl (s _64723)). Qed.
Lemma lem5036640 {A : Type'} (_64722 : A) (s : A -> Prop) (_64723 : A) : (term521 A _64722 s _64723) = (term527 A _64722 s _64723).
Proof. exact (MK_COMB (@lem5036638 A _64723 s _64722) (@lem5036639 A s _64723)). Qed.
Lemma lem5036641 {A : Type'} (_64722 : A) (s : A -> Prop) (_64723 : A) : (term514 A _64723 s _64722) = (term527 A _64722 s _64723).
Proof. exact (TRANS (@lem5036623 A _64722 s _64723) (@lem5036640 A _64722 s _64723)). Qed.
Lemma lem5036643 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term48 A B u f) (h2 : term335 A B u x' s f t x'') (h3 : term345 A s t x) : term528 A B s x' f x.
Proof. exact (conj (@lem5036504 A B u x' f x'' s t x h1 h2 h3) (@lem5036533 A B u x' f x'' s t x h2 h3)). Qed.
Lemma lem5036645 {A : Type'} (_64722 : A) (s : A -> Prop) (_64723 : A) : term527 A _64722 s _64723.
Proof. exact (EQ_MP (@lem5036641 A _64722 s _64723) (@lem5036620 A _64723 s _64722)). Qed.
Lemma lem5036646 {A : Type'} (_64722 : A) (s : A -> Prop) (_64723 : A) : term527 A _64722 s _64723.
Proof. exact (@lem5036645 A _64722 s _64723). Qed.
Lemma lem5036647 {A B : Type'} (x' : B -> A) (f : A -> B) (s : A -> Prop) (x : A) : term529 A B x' f s x.
Proof. exact (@lem5036646 A (term453 A B x' f x) s x). Qed.
Lemma lem5036650 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term48 A B u f) (h2 : term335 A B u x' s f t x'') (h3 : term345 A s t x) : s x.
Proof. exact (@lem5036647 A B x' f s x (@lem5036643 A B u x' f x'' s t x h1 h2 h3)). Qed.
Lemma lem5036651 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term48 A B u f) (h2 : term335 A B u x' s f t x'') (h3 : term345 A s t x) : term417 A s x.
Proof. exact (fun h0 : term400 A s x => @lem5036650 A B u x' f x'' s t x h1 h2 h3). Qed.
Lemma lem5036653 (p : Prop) : (term418 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5036654 {A : Type'} (s : A -> Prop) (x : A) : (term417 A s x) = (s x).
Proof. exact (@lem5036653 (s x)). Qed.
Lemma lem5036655 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term48 A B u f) (h2 : term335 A B u x' s f t x'') (h3 : term345 A s t x) : s x.
Proof. exact (EQ_MP (@lem5036654 A s x) (@lem5036651 A B u x' f x'' s t x h1 h2 h3)). Qed.
Lemma lem5036658 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5036660 {A : Type'} (s : A -> Prop) (x : A) : (term400 A s x) = (term530 A s x).
Proof. exact (@lem5036658 (s x)). Qed.
Lemma lem5036663 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term345 A s t x) : term530 A s x.
Proof. exact (EQ_MP (@lem5036660 A s x) (@lem5034887 A s t x h1)). Qed.
Lemma lem5036666 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term48 A B u f) (h2 : term335 A B u x' s f t x'') (h3 : term345 A s t x) : False.
Proof. exact (@lem5036663 A s t x h3 (@lem5036655 A B u x' f x'' s t x h1 h2 h3)). Qed.
Lemma lem5036667 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term48 A B u f) (h2 : term335 A B u x' s f t x'') (h3 : term345 A s t x) : term531.
Proof. exact (fun h0 : ~ False => @lem5036666 A B u x' f x'' s t x h1 h2 h3). Qed.
Lemma lem5036669 (p : Prop) : (term418 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5036670 : term531 = False.
Proof. exact (@lem5036669 False). Qed.
Lemma lem5036671 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (x'' : B -> A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term48 A B u f) (h2 : term335 A B u x' s f t x'') (h3 : term345 A s t x) : False.
Proof. exact (EQ_MP (@lem5036670) (@lem5036667 A B u x' f x'' s t x h1 h2 h3)). Qed.
Lemma lem5036672 {A B : Type'} (x : A) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term48 A B u f) (h2 : term102 A s t x) (h3 : term335 A B u x' s f t x'') : False.
Proof. exact (or_elim (@lem5034237 A s t x h2) (fun h0 : term344 A s t x => @lem5035905 A B u x' f x'' s t x h1 h3 h0) (fun h0 : term345 A s t x => @lem5036671 A B u x' f x'' s t x h1 h3 h0)). Qed.
Lemma lem5036673 {A B : Type'} (x : A) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term48 A B u f) (h2 : term102 A s t x) (h3 : term335 A B u x' s f t x'') : (term335 A B u x' s f t x'') = False.
Proof. exact (prop_ext (fun h4 : term335 A B u x' s f t x'' => @lem5036672 A B x u x' s f t x'' h1 h2 h3) (fun h4 : False => @lem5034361 A B u x' s f t x'' h3)). Qed.
Lemma lem5036674 {A B : Type'} (x : A) (u : A -> Prop) (x' : B -> A) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (x'' : B -> A) (h1 : term48 A B u f) (h2 : term102 A s t x) (h3 : term335 A B u x' s f t x'') : False.
Proof. exact (EQ_MP (@lem5036673 A B x u x' s f t x'' h1 h2 h3) (@lem5034361 A B u x' s f t x'' h3)). Qed.
Lemma lem5036675 {A B : Type'} (u : A -> Prop) (x' : B -> A) (f : A -> B) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term48 A B u f) (h2 : term338 A B u x' s f t) (h3 : term102 A s t x) : False.
Proof. exact (ex_elim (@lem5034168 A B u x' s f t h2) (fun x'' : B -> A => fun h0 : term337 A B u x' s f t x'' => @lem5036674 A B x u x' s f t x'' h1 h3 h0)). Qed.
Lemma lem5036676 {A B : Type'} (x : A) (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term48 A B u f) (h2 : term102 A s t x) (h3 : term72 A B u s f t) : False.
Proof. exact (ex_elim (@lem5034147 A B u s f t h3) (fun x' : B -> A => fun h0 : term339 A B u s f t x' => @lem5036675 A B u x' f s t x h1 h0 h2)). Qed.
Lemma lem5036677 {A B : Type'} (x : A) (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term48 A B u f) (h2 : term102 A s t x) (h3 : term72 A B u s f t) : (term102 A s t x) = False.
Proof. exact (prop_ext (fun h4 : term102 A s t x => @lem5036676 A B x u s f t h1 h2 h3) (fun h4 : False => @lem5033363 A s t x h2)). Qed.
Lemma lem5036678 {A B : Type'} (x : A) (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term48 A B u f) (h2 : term102 A s t x) (h3 : term72 A B u s f t) : False.
Proof. exact (EQ_MP (@lem5036677 A B x u s f t h1 h2 h3) (@lem5033363 A s t x h2)). Qed.
Lemma lem5036679 {A B : Type'} (x : A) (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term48 A B u f) (h2 : term72 A B u s f t) : term101 A s t x.
Proof. exact (fun h0 : term102 A s t x => @lem5036678 A B x u s f t h1 h0 h2). Qed.
Lemma lem5036680 {A B : Type'} (x : A) (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term48 A B u f) (h2 : term72 A B u s f t) : (s x) = (t x).
Proof. exact (EQ_MP (@lem5033362 A s t x) (@lem5036679 A B x u s f t h1 h2)). Qed.
Lemma lem5036685 {A B : Type'} (u : A -> Prop) (s : A -> Prop) (f : A -> B) (t : A -> Prop) (h1 : term48 A B u f) (h2 : term72 A B u s f t) : term78 A s t.
Proof. exact (fun x : A => @lem5036680 A B x u s f t h1 h2). Qed.
Lemma lem5036686 {A B : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (f : A -> B) (h1 : term48 A B u f) : term79 A B u f s t.
Proof. exact (fun h0 : term72 A B u s f t => @lem5036685 A B u s f t h1 h0). Qed.
Lemma lem5036691 {A B : Type'} (s : A -> Prop) (u : A -> Prop) (f : A -> B) (h1 : term48 A B u f) : term81 A B u f s.
Proof. exact (fun t : A -> Prop => @lem5036686 A B s t u f h1). Qed.
Lemma lem5036696 {A B : Type'} (u : A -> Prop) (f : A -> B) (h1 : term48 A B u f) : term83 A B u f.
Proof. exact (fun s : A -> Prop => @lem5036691 A B s u f h1). Qed.
Lemma lem5036697 {A B : Type'} (u : A -> Prop) (f : A -> B) : term84 A B u f.
Proof. exact (fun h0 : term48 A B u f => @lem5036696 A B u f h0). Qed.
Lemma lem5036702 {A B : Type'} (f : A -> B) : term96 A B f.
Proof. exact (fun u : A -> Prop => @lem5036697 A B u f). Qed.
Lemma lem5036707 {A B : Type'} : term100 A B.
Proof. exact (fun f : A -> B => @lem5036702 A B f). Qed.
Lemma lem5036708 {A B : Type'} : term99 A B.
Proof. exact (EQ_MP (@lem5033356 A B) (@lem5036707 A B)). Qed.
Lemma lem5036709 {A B : Type'} (f : A -> B) : term532 A B f.
Proof. exact (@lem5036708 A B f). Qed.
Lemma lem5036710 {A B : Type'} (f : A -> B) : (term532 A B f) = (term95 A B f).
Proof. exact (eq_refl (term532 A B f)). Qed.
Lemma lem5036711 {A B : Type'} (f : A -> B) : term95 A B f.
Proof. exact (EQ_MP (@lem5036710 A B f) (@lem5036709 A B f)). Qed.
Lemma lem5036712 {A B : Type'} (f : A -> B) (u : A -> Prop) : term533 A B f u.
Proof. exact (@lem5036711 A B f u). Qed.
Lemma lem5036713 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term533 A B f u) = (term86 A B u f).
Proof. exact (eq_refl (term533 A B f u)). Qed.
Lemma lem5036714 {A B : Type'} (u : A -> Prop) (f : A -> B) : term86 A B u f.
Proof. exact (EQ_MP (@lem5036713 A B u f) (@lem5036712 A B f u)). Qed.
Lemma lem5036716 {A B : Type'} (u : A -> Prop) (f : A -> B) : term86 A B u f.
Proof. exact (@lem5033018 A B u f (@lem5036714 A B u f)). Qed.
Lemma lem5036717 {A B : Type'} (u : A -> Prop) (f : A -> B) (h1 : term87 A B u f) : False.
Proof. exact (@lem5036716 A B u f (@lem5033002 A B u f h1)). Qed.
Lemma lem5036718 {A B : Type'} (u : A -> Prop) (f : A -> B) (h1 : term87 A B u f) : (term87 A B u f) = False.
Proof. exact (prop_ext (fun h2 : term87 A B u f => @lem5036717 A B u f h1) (fun h2 : False => @lem5033002 A B u f h1)). Qed.
Lemma lem5036719 {A B : Type'} (u : A -> Prop) (f : A -> B) (h1 : term87 A B u f) : False.
Proof. exact (EQ_MP (@lem5036718 A B u f h1) (@lem5033002 A B u f h1)). Qed.
Lemma lem5036720 {A B : Type'} (u : A -> Prop) (f : A -> B) : term86 A B u f.
Proof. exact (fun h0 : term87 A B u f => @lem5036719 A B u f h0). Qed.
Lemma lem5036721 {A B : Type'} (u : A -> Prop) (f : A -> B) : term84 A B u f.
Proof. exact (EQ_MP (@lem5033001 A B u f) (@lem5036720 A B u f)). Qed.
Lemma lem5036722 {A B : Type'} (u : A -> Prop) (f : A -> B) : term30 A B u f.
Proof. exact (EQ_MP (@lem5032997 A B u f) (@lem5036721 A B u f)). Qed.
Lemma lem5036723 {A B : Type'} (u : A -> Prop) (f : A -> B) : term29 A B u f.
Proof. exact (EQ_MP (@lem5032737 A B u f) (@lem5036722 A B u f)). Qed.
Lemma lem5036724 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (y : A) (h1 : term35 A B u x f y) : term35 A B u x f y.
Proof. exact (h1). Qed.
Lemma lem5036725 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (y : A) (h1 : term33 A B u x f y) : term33 A B u x f y.
Proof. exact (h1). Qed.
Lemma lem5036726 {A : Type'} (x : A) (u : A -> Prop) (h1 : @IN A x u) : @IN A x u.
Proof. exact (h1). Qed.
Lemma lem5036727 {A B : Type'} (x : A) (f : A -> B) (y : A) (h1 : (f x) = (f y)) : (f x) = (f y).
Proof. exact (h1). Qed.
Lemma lem5036728 {A : Type'} (y : A) (u : A -> Prop) (h1 : @IN A y u) : @IN A y u.
Proof. exact (h1). Qed.
Lemma lem5036729 {A B : Type'} (x : A) (u : A -> Prop) (f : A -> B) (h1 : term7 A B u f) : term534 A B u f x.
Proof. exact (@lem5032618 A B u f h1 (@INSERT A x (@EMPTY A))). Qed.
Lemma lem5036730 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) : (term534 A B u f x) = (term535 A B u f x).
Proof. exact (eq_refl (term534 A B u f x)). Qed.
Lemma lem5036731 {A B : Type'} (x : A) (u : A -> Prop) (f : A -> B) (h1 : term7 A B u f) : term535 A B u f x.
Proof. exact (EQ_MP (@lem5036730 A B u f x) (@lem5036729 A B x u f h1)). Qed.
Lemma lem5036732 {A B : Type'} (x : A) (y : A) (u : A -> Prop) (f : A -> B) (h1 : term7 A B u f) : term536 A B u f x y.
Proof. exact (@lem5036731 A B x u f h1 (@INSERT A y (@EMPTY A))). Qed.
Lemma lem5036733 {A B : Type'} (u : A -> Prop) (f : A -> B) (x : A) (y : A) : (term536 A B u f x y) = (term537 A B u f x y).
Proof. exact (eq_refl (term536 A B u f x y)). Qed.
Lemma lem5036734 {A B : Type'} (x : A) (y : A) (u : A -> Prop) (f : A -> B) (h1 : term7 A B u f) : term537 A B u f x y.
Proof. exact (EQ_MP (@lem5036733 A B u f x y) (@lem5036732 A B x y u f h1)). Qed.
Lemma lem5036737 {_84443 : Type'} (s : _84443 -> Prop) : term538 _84443 s.
Proof. exact (@lem3221020 _84443 s). Qed.
Lemma lem5036738 {_84443 : Type'} (s : _84443 -> Prop) : (term538 _84443 s) = (term539 _84443 s).
Proof. exact (eq_refl (term538 _84443 s)). Qed.
Lemma lem5036739 {_84443 : Type'} (s : _84443 -> Prop) : term539 _84443 s.
Proof. exact (EQ_MP (@lem5036738 _84443 s) (@lem5036737 _84443 s)). Qed.
Lemma lem5036740 {_84443 : Type'} (s : _84443 -> Prop) (x : _84443) : term540 _84443 s x.
Proof. exact (@lem5036739 _84443 s x). Qed.
Lemma lem5036741 {_84443 : Type'} (x : _84443) (s : _84443 -> Prop) : (term540 _84443 s x) = ((term541 _84443 x s) = (@IN _84443 x s)).
Proof. exact (eq_refl (term540 _84443 s x)). Qed.
Lemma lem5036743 {A : Type'} (x : A) (u : A -> Prop) : (@IN A x u) = ((@IN A x u) = True).
Proof. exact (@lem7 (@IN A x u)). Qed.
Lemma lem5036745 {A : Type'} (y : A) (u : A -> Prop) : (@IN A y u) = ((@IN A y u) = True).
Proof. exact (@lem7 (@IN A y u)). Qed.
Lemma lem5036754 {_84443 : Type'} (x : _84443) (s : _84443 -> Prop) : (term541 _84443 x s) = (@IN _84443 x s).
Proof. exact (EQ_MP (@lem5036741 _84443 x s) (@lem5036740 _84443 s x)). Qed.
Lemma lem5036755 {A : Type'} (x : A) (s : A -> Prop) : (term541 A x s) = (@IN A x s).
Proof. exact (@lem5036754 A x s). Qed.
Lemma lem5036756 {A : Type'} (x : A) (u : A -> Prop) : (term541 A x u) = (@IN A x u).
Proof. exact (@lem5036755 A x u). Qed.
Lemma lem5036758 {A : Type'} (x : A) (u : A -> Prop) (h1 : @IN A x u) : (@IN A x u) = True.
Proof. exact (EQ_MP (@lem5036743 A x u) (@lem5036726 A x u h1)). Qed.
Lemma lem5036759 {A : Type'} (x : A) (u : A -> Prop) (h1 : @IN A x u) : (term541 A x u) = True.
Proof. exact (TRANS (@lem5036756 A x u) (@lem5036758 A x u h1)). Qed.
Lemma lem5036760 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5036761 {A : Type'} (x : A) (u : A -> Prop) (h1 : @IN A x u) : (term542 A x u) = (and True).
Proof. exact (MK_COMB (@lem5036760) (@lem5036759 A x u h1)). Qed.
Lemma lem5036765 {_84443 : Type'} (x : _84443) (s : _84443 -> Prop) : (term541 _84443 x s) = (@IN _84443 x s).
Proof. exact (EQ_MP (@lem5036741 _84443 x s) (@lem5036740 _84443 s x)). Qed.
Lemma lem5036766 {A : Type'} (x : A) (s : A -> Prop) : (term541 A x s) = (@IN A x s).
Proof. exact (@lem5036765 A x s). Qed.
Lemma lem5036767 {A : Type'} (y : A) (u : A -> Prop) : (term541 A y u) = (@IN A y u).
Proof. exact (@lem5036766 A y u). Qed.
Lemma lem5036769 {A : Type'} (y : A) (u : A -> Prop) (h1 : @IN A y u) : (@IN A y u) = True.
Proof. exact (EQ_MP (@lem5036745 A y u) (@lem5036728 A y u h1)). Qed.
Lemma lem5036770 {A : Type'} (y : A) (u : A -> Prop) (h1 : @IN A y u) : (term541 A y u) = True.
Proof. exact (TRANS (@lem5036767 A y u) (@lem5036769 A y u h1)). Qed.
Lemma lem5036771 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5036772 {A : Type'} (y : A) (u : A -> Prop) (h1 : @IN A y u) : (term542 A y u) = (and True).
Proof. exact (MK_COMB (@lem5036771) (@lem5036770 A y u h1)). Qed.
Lemma lem5036776 {_87477 _87481 : Type'} (x : _87477) (f : _87477 -> _87481) (s : _87477 -> Prop) : (term543 _87477 _87481 f x s) = (term544 _87477 _87481 x f s).
Proof. exact (proj2 (@lem3366870 _87477 _87481 x f s)). Qed.
Lemma lem5036777 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term543 A B f x s) = (term544 A B x f s).
Proof. exact (@lem5036776 A B x f s). Qed.
Lemma lem5036778 {A B : Type'} (x : A) (f : A -> B) : (term545 A B f x) = (term546 A B x f).
Proof. exact (@lem5036777 A B x f (@EMPTY A)). Qed.
Lemma lem5036780 {A B : Type'} (x : A) (f : A -> B) (y : A) (h1 : (f x) = (f y)) : (f x) = (f y).
Proof. exact (h1). Qed.
Lemma lem5036781 {B : Type'} : (@INSERT B) = (@INSERT B).
Proof. exact (eq_refl (@INSERT B)). Qed.
Lemma lem5036782 {A B : Type'} (x : A) (f : A -> B) (y : A) (h1 : (f x) = (f y)) : (term547 A B f x) = (term547 A B f y).
Proof. exact (MK_COMB (@lem5036781 B) (@lem5036780 A B x f y h1)). Qed.
Lemma lem5036784 {_87477 _87481 : Type'} (f : _87477 -> _87481) : (@IMAGE _87477 _87481 f (@EMPTY _87477)) = (@EMPTY _87481).
Proof. exact (proj1 (@lem3366870 _87477 _87481 (@el _87477) f (@el (_87477 -> Prop)))). Qed.
Lemma lem5036785 {A B : Type'} (f : A -> B) : (@IMAGE A B f (@EMPTY A)) = (@EMPTY B).
Proof. exact (@lem5036784 A B f). Qed.
Lemma lem5036786 {A B : Type'} (x : A) (f : A -> B) (y : A) (h1 : (f x) = (f y)) : (term546 A B x f) = (term548 A B f y).
Proof. exact (MK_COMB (@lem5036782 A B x f y h1) (@lem5036785 A B f)). Qed.
Lemma lem5036787 {A B : Type'} (x : A) (f : A -> B) (y : A) (h1 : (f x) = (f y)) : (term545 A B f x) = (term548 A B f y).
Proof. exact (TRANS (@lem5036778 A B x f) (@lem5036786 A B x f y h1)). Qed.
Lemma lem5036788 {B : Type'} : (@eq (B -> Prop)) = (@eq (B -> Prop)).
Proof. exact (eq_refl (@eq (B -> Prop))). Qed.
Lemma lem5036789 {A B : Type'} (x : A) (f : A -> B) (y : A) (h1 : (f x) = (f y)) : (term549 A B f x) = (term550 A B f y).
Proof. exact (MK_COMB (@lem5036788 B) (@lem5036787 A B x f y h1)). Qed.
Lemma lem5036791 {_87477 _87481 : Type'} (x : _87477) (f : _87477 -> _87481) (s : _87477 -> Prop) : (term543 _87477 _87481 f x s) = (term544 _87477 _87481 x f s).
Proof. exact (proj2 (@lem3366870 _87477 _87481 x f s)). Qed.
Lemma lem5036792 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term543 A B f x s) = (term544 A B x f s).
Proof. exact (@lem5036791 A B x f s). Qed.
Lemma lem5036793 {A B : Type'} (y : A) (f : A -> B) : (term545 A B f y) = (term546 A B y f).
Proof. exact (@lem5036792 A B y f (@EMPTY A)). Qed.
Lemma lem5036795 {_87477 _87481 : Type'} (f : _87477 -> _87481) : (@IMAGE _87477 _87481 f (@EMPTY _87477)) = (@EMPTY _87481).
Proof. exact (proj1 (@lem3366870 _87477 _87481 (@el _87477) f (@el (_87477 -> Prop)))). Qed.
Lemma lem5036796 {A B : Type'} (f : A -> B) : (@IMAGE A B f (@EMPTY A)) = (@EMPTY B).
Proof. exact (@lem5036795 A B f). Qed.
Lemma lem5036797 {A B : Type'} (f : A -> B) (y : A) : (term547 A B f y) = (term547 A B f y).
Proof. exact (eq_refl (term547 A B f y)). Qed.
Lemma lem5036798 {A B : Type'} (f : A -> B) (y : A) : (term546 A B y f) = (term548 A B f y).
Proof. exact (MK_COMB (@lem5036797 A B f y) (@lem5036796 A B f)). Qed.
Lemma lem5036799 {A B : Type'} (f : A -> B) (y : A) : (term545 A B f y) = (term548 A B f y).
Proof. exact (TRANS (@lem5036793 A B y f) (@lem5036798 A B f y)). Qed.
Lemma lem5036800 {A B : Type'} (x : A) (f : A -> B) (y : A) (h1 : (f x) = (f y)) : ((term545 A B f x) = (term545 A B f y)) = ((term548 A B f y) = (term548 A B f y)).
Proof. exact (MK_COMB (@lem5036789 A B x f y h1) (@lem5036799 A B f y)). Qed.
Lemma lem5036802 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5036803 {B : Type'} (x : B -> Prop) : (x = x) = True.
Proof. exact (@lem5036802 (B -> Prop) x). Qed.
Lemma lem5036804 {A B : Type'} (f : A -> B) (y : A) : ((term548 A B f y) = (term548 A B f y)) = True.
Proof. exact (@lem5036803 B (term548 A B f y)). Qed.
Lemma lem5036805 {A B : Type'} (x : A) (f : A -> B) (y : A) (h1 : (f x) = (f y)) : ((term545 A B f x) = (term545 A B f y)) = True.
Proof. exact (TRANS (@lem5036800 A B x f y h1) (@lem5036804 A B f y)). Qed.
Lemma lem5036806 {A B : Type'} (x : A) (f : A -> B) (y : A) (u : A -> Prop) (h1 : (f x) = (f y)) (h2 : @IN A y u) : (term551 A B u x f y) = (True /\ True).
Proof. exact (MK_COMB (@lem5036772 A y u h2) (@lem5036805 A B x f y h1)). Qed.
Lemma lem5036808 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5036809 : (True /\ True) = True.
Proof. exact (@lem5036808 True). Qed.
Lemma lem5036810 {A B : Type'} (x : A) (f : A -> B) (y : A) (u : A -> Prop) (h1 : (f x) = (f y)) (h2 : @IN A y u) : (term551 A B u x f y) = True.
Proof. exact (TRANS (@lem5036806 A B x f y u h1 h2) (@lem5036809)). Qed.
Lemma lem5036811 {A B : Type'} (f : A -> B) (x : A) (y : A) (u : A -> Prop) (h1 : (f x) = (f y)) (h2 : @IN A x u) (h3 : @IN A y u) : (term552 A B u x f y) = (True /\ True).
Proof. exact (MK_COMB (@lem5036761 A x u h2) (@lem5036810 A B x f y u h1 h3)). Qed.
Lemma lem5036813 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5036814 : (True /\ True) = True.
Proof. exact (@lem5036813 True). Qed.
Lemma lem5036815 {A B : Type'} (f : A -> B) (x : A) (y : A) (u : A -> Prop) (h1 : (f x) = (f y)) (h2 : @IN A x u) (h3 : @IN A y u) : (term552 A B u x f y) = True.
Proof. exact (TRANS (@lem5036811 A B f x y u h1 h2 h3) (@lem5036814)). Qed.
Lemma lem5036816 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5036817 {A B : Type'} (f : A -> B) (x : A) (y : A) (u : A -> Prop) (h1 : (f x) = (f y)) (h2 : @IN A x u) (h3 : @IN A y u) : (term553 A B u x f y) = (imp True).
Proof. exact (MK_COMB (@lem5036816) (@lem5036815 A B f x y u h1 h2 h3)). Qed.
Lemma lem5036820 {A : Type'} (x : A) (y : A) : ((@INSERT A x (@EMPTY A)) = (@INSERT A y (@EMPTY A))) = ((@INSERT A x (@EMPTY A)) = (@INSERT A y (@EMPTY A))).
Proof. exact (eq_refl ((@INSERT A x (@EMPTY A)) = (@INSERT A y (@EMPTY A)))). Qed.
Lemma lem5036821 {A B : Type'} (f : A -> B) (x : A) (y : A) (u : A -> Prop) (h1 : (f x) = (f y)) (h2 : @IN A x u) (h3 : @IN A y u) : (term537 A B u f x y) = (term554 A x y).
Proof. exact (MK_COMB (@lem5036817 A B f x y u h1 h2 h3) (@lem5036820 A x y)). Qed.
Lemma lem5036823 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem5036824 {A : Type'} (x : A) (y : A) : (term554 A x y) = ((@INSERT A x (@EMPTY A)) = (@INSERT A y (@EMPTY A))).
Proof. exact (@lem5036823 ((@INSERT A x (@EMPTY A)) = (@INSERT A y (@EMPTY A)))). Qed.
Lemma lem5036827 {A B : Type'} (f : A -> B) (x : A) (y : A) (u : A -> Prop) (h1 : (f x) = (f y)) (h2 : @IN A x u) (h3 : @IN A y u) : (term537 A B u f x y) = ((@INSERT A x (@EMPTY A)) = (@INSERT A y (@EMPTY A))).
Proof. exact (TRANS (@lem5036821 A B f x y u h1 h2 h3) (@lem5036824 A x y)). Qed.
Lemma lem5036828 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5036829 {A B : Type'} (f : A -> B) (x : A) (y : A) (u : A -> Prop) (h1 : (f x) = (f y)) (h2 : @IN A x u) (h3 : @IN A y u) : (term555 A B u f x y) = (term556 A x y).
Proof. exact (MK_COMB (@lem5036828) (@lem5036827 A B f x y u h1 h2 h3)). Qed.
Lemma lem5036832 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem5036833 {A B : Type'} (f : A -> B) (x : A) (y : A) (u : A -> Prop) (h1 : (f x) = (f y)) (h2 : @IN A x u) (h3 : @IN A y u) : (term557 A B u f x y) = (term558 A x y).
Proof. exact (MK_COMB (@lem5036829 A B f x y u h1 h2 h3) (@lem5036832 A x y)). Qed.
Lemma lem5036838 {A B : Type'} (f : A -> B) (x : A) (y : A) (u : A -> Prop) (h1 : (f x) = (f y)) (h2 : @IN A x u) (h3 : @IN A y u) : (term558 A x y) = (term557 A B u f x y).
Proof. exact (SYM (@lem5036833 A B f x y u h1 h2 h3)). Qed.
Lemma lem5036846 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term11 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem5036847 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term11 A s t).
Proof. exact (@lem5036846 A s t). Qed.
Lemma lem5036848 {A : Type'} (x : A) (y : A) : ((@INSERT A x (@EMPTY A)) = (@INSERT A y (@EMPTY A))) = (term559 A x y).
Proof. exact (@lem5036847 A (@INSERT A x (@EMPTY A)) (@INSERT A y (@EMPTY A))). Qed.
Lemma lem5036857 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5036858 {A : Type'} (x : A) (y : A) : (term556 A x y) = (term560 A x y).
Proof. exact (MK_COMB (@lem5036857) (@lem5036848 A x y)). Qed.
Lemma lem5036863 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem5036864 {A : Type'} (x : A) (y : A) : (term558 A x y) = (term561 A x y).
Proof. exact (MK_COMB (@lem5036858 A x y) (@lem5036863 A x y)). Qed.
Lemma lem5036867 {A : Type'} (x : A) (y : A) : (term561 A x y) = (term558 A x y).
Proof. exact (SYM (@lem5036864 A x y)). Qed.
Lemma lem5036877 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term562 A x y s) = (term563 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem5036878 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term562 A x y s) = (term563 A y x s).
Proof. exact (@lem5036877 A y x s). Qed.
Lemma lem5036879 {A : Type'} (x : A) (x' : A) : (term564 A x' x) = (term565 A x x').
Proof. exact (@lem5036878 A x x' (@EMPTY A)). Qed.
Lemma lem5036885 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem5036886 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem5036885 A x). Qed.
Lemma lem5036887 {A : Type'} (x' : A) : (@IN A x' (@EMPTY A)) = False.
Proof. exact (@lem5036886 A x'). Qed.
Lemma lem5036888 {A : Type'} (x' : A) (x : A) : (term566 A x' x) = (term566 A x' x).
Proof. exact (eq_refl (term566 A x' x)). Qed.
Lemma lem5036889 {A : Type'} (x' : A) (x : A) : (term565 A x x') = (term567 A x' x).
Proof. exact (MK_COMB (@lem5036888 A x' x) (@lem5036887 A x')). Qed.
Lemma lem5036891 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem5036892 {A : Type'} (x' : A) (x : A) : (term567 A x' x) = (x' = x).
Proof. exact (@lem5036891 (x' = x)). Qed.
Lemma lem5036895 {A : Type'} (x' : A) (x : A) : (term565 A x x') = (x' = x).
Proof. exact (TRANS (@lem5036889 A x' x) (@lem5036892 A x' x)). Qed.
Lemma lem5036896 {A : Type'} (x' : A) (x : A) : (term564 A x' x) = (x' = x).
Proof. exact (TRANS (@lem5036879 A x x') (@lem5036895 A x' x)). Qed.
Lemma lem5036897 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5036898 {A : Type'} (x' : A) (x : A) : (term568 A x' x) = (term569 A x' x).
Proof. exact (MK_COMB (@lem5036897) (@lem5036896 A x' x)). Qed.
Lemma lem5036900 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term562 A x y s) = (term563 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem5036901 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term562 A x y s) = (term563 A y x s).
Proof. exact (@lem5036900 A y x s). Qed.
Lemma lem5036902 {A : Type'} (y : A) (x' : A) : (term564 A x' y) = (term565 A y x').
Proof. exact (@lem5036901 A y x' (@EMPTY A)). Qed.
Lemma lem5036908 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem5036909 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem5036908 A x). Qed.
Lemma lem5036910 {A : Type'} (x' : A) : (@IN A x' (@EMPTY A)) = False.
Proof. exact (@lem5036909 A x'). Qed.
Lemma lem5036911 {A : Type'} (x' : A) (y : A) : (term566 A x' y) = (term566 A x' y).
Proof. exact (eq_refl (term566 A x' y)). Qed.
Lemma lem5036912 {A : Type'} (x' : A) (y : A) : (term565 A y x') = (term567 A x' y).
Proof. exact (MK_COMB (@lem5036911 A x' y) (@lem5036910 A x')). Qed.
Lemma lem5036914 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem5036915 {A : Type'} (x' : A) (y : A) : (term567 A x' y) = (x' = y).
Proof. exact (@lem5036914 (x' = y)). Qed.
Lemma lem5036918 {A : Type'} (x' : A) (y : A) : (term565 A y x') = (x' = y).
Proof. exact (TRANS (@lem5036912 A x' y) (@lem5036915 A x' y)). Qed.
Lemma lem5036919 {A : Type'} (x' : A) (y : A) : (term564 A x' y) = (x' = y).
Proof. exact (TRANS (@lem5036902 A y x') (@lem5036918 A x' y)). Qed.
Lemma lem5036920 {A : Type'} (x : A) (x' : A) (y : A) : ((term564 A x' x) = (term564 A x' y)) = ((x' = x) = (x' = y)).
Proof. exact (MK_COMB (@lem5036898 A x' x) (@lem5036919 A x' y)). Qed.
Lemma lem5036923 {A : Type'} (x : A) (y : A) : (term570 A x y) = (term571 A x y).
Proof. exact (fun_ext (fun x' : A => @lem5036920 A x x' y)). Qed.
Lemma lem5036924 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5036925 {A : Type'} (x : A) (y : A) : (term559 A x y) = (term572 A x y).
Proof. exact (MK_COMB (@lem5036924 A) (@lem5036923 A x y)). Qed.
Lemma lem5036930 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5036931 {A : Type'} (x : A) (y : A) : (term560 A x y) = (term573 A x y).
Proof. exact (MK_COMB (@lem5036930) (@lem5036925 A x y)). Qed.
Lemma lem5036934 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem5036935 {A : Type'} (x : A) (y : A) : (term561 A x y) = (term574 A x y).
Proof. exact (MK_COMB (@lem5036931 A x y) (@lem5036934 A x y)). Qed.
Lemma lem5036938 {A : Type'} (x : A) (y : A) : (term574 A x y) = (term561 A x y).
Proof. exact (SYM (@lem5036935 A x y)). Qed.
Lemma lem5036940 (p : Prop) : p = (term85 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5036941 {A : Type'} (x : A) (y : A) : (term574 A x y) = (term575 A x y).
Proof. exact (@lem5036940 (term574 A x y)). Qed.
Lemma lem5036942 {A : Type'} (x : A) (y : A) : (term575 A x y) = (term574 A x y).
Proof. exact (SYM (@lem5036941 A x y)). Qed.
Lemma lem5036943 {A : Type'} (x : A) (y : A) (h1 : term576 A x y) : term576 A x y.
Proof. exact (h1). Qed.
Lemma lem5036946 {A : Type'} (x : A) (y : A) (h1 : term575 A x y) : term575 A x y.
Proof. exact (h1). Qed.
Lemma lem5036947 {A : Type'} (x : A) (y : A) : term577 A x y.
Proof. exact (fun h0 : term575 A x y => @lem5036946 A x y h0). Qed.
Lemma lem5036948 {A : Type'} (x : A) (y : A) (h1 : term577 A x y) : term577 A x y.
Proof. exact (h1). Qed.
Lemma lem5036949 {A : Type'} (x : A) (y : A) (h1 : term575 A x y) : term575 A x y.
Proof. exact (h1). Qed.
Lemma lem5036950 {A : Type'} (x : A) (y : A) (h1 : term575 A x y) (h2 : term577 A x y) : term575 A x y.
Proof. exact (@lem5036948 A x y h2 (@lem5036949 A x y h1)). Qed.
Lemma lem5036951 {A : Type'} (x : A) (y : A) (h1 : term575 A x y) : term578 A x y.
Proof. exact (fun h0 : term577 A x y => @lem5036950 A x y h1 h0). Qed.
Lemma lem5036952 {A : Type'} (x : A) (y : A) (h1 : term577 A x y) : term577 A x y.
Proof. exact (h1). Qed.
Lemma lem5036953 {A : Type'} (x : A) (y : A) (h1 : term575 A x y) (h2 : term577 A x y) : term575 A x y.
Proof. exact (@lem5036951 A x y h1 (@lem5036952 A x y h2)). Qed.
Lemma lem5036954 {A : Type'} (x : A) (y : A) (h1 : term577 A x y) : term577 A x y.
Proof. exact (fun h0 : term575 A x y => @lem5036953 A x y h0 h1). Qed.
Lemma lem5036955 {A : Type'} (x : A) (y : A) : term579 A x y.
Proof. exact (fun h0 : term577 A x y => @lem5036954 A x y h0). Qed.
Lemma lem5036958 {A : Type'} (x : A) (y : A) : term577 A x y.
Proof. exact (@lem5036955 A x y (@lem5036947 A x y)). Qed.
Lemma lem5036959 {A : Type'} (x : A) (y : A) : term577 A x y.
Proof. exact (@lem5036958 A x y). Qed.
Lemma lem5036969 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5036970 {A : Type'} (x : A) (y : A) : (term575 A x y) = (term580 A x y).
Proof. exact (@lem5036969 (term576 A x y)). Qed.
Lemma lem5036972 (t : Prop) : (term92 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5036973 {A : Type'} (x : A) (y : A) : (term580 A x y) = (term574 A x y).
Proof. exact (@lem5036972 (term574 A x y)). Qed.
Lemma lem5036976 {A : Type'} (x : A) (y : A) : (term575 A x y) = (term574 A x y).
Proof. exact (TRANS (@lem5036970 A x y) (@lem5036973 A x y)). Qed.
Lemma lem5036981 {A : Type'} (y : A) : (term581 A y) = (term582 A y).
Proof. exact (fun_ext (fun x : A => @lem5036976 A x y)). Qed.
Lemma lem5036982 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5036983 {A : Type'} (y : A) : (term583 A y) = (term584 A y).
Proof. exact (MK_COMB (@lem5036982 A) (@lem5036981 A y)). Qed.
Lemma lem5036988 {A : Type'} : (term585 A) = (term586 A).
Proof. exact (fun_ext (fun y : A => @lem5036983 A y)). Qed.
Lemma lem5036989 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5036998 {A : Type'} : (term587 A) = (term588 A).
Proof. exact (MK_COMB (@lem5036989 A) (@lem5036988 A)). Qed.
Lemma lem5036999 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem5037004 {A : Type'} (x : A) (x' : A) (y : A) : ((x' = x) = (x' = y)) = ((x' = x) = (x' = y)).
Proof. exact (eq_refl ((x' = x) = (x' = y))). Qed.
Lemma lem5037005 {A : Type'} (x : A) (y : A) : (term571 A x y) = (term571 A x y).
Proof. exact (fun_ext (fun x' : A => @lem5037004 A x x' y)). Qed.
Lemma lem5037006 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5037007 {A : Type'} (x : A) (y : A) : (term572 A x y) = (term572 A x y).
Proof. exact (MK_COMB (@lem5037006 A) (@lem5037005 A x y)). Qed.
Lemma lem5037008 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5037009 {A : Type'} (x : A) (y : A) : (term573 A x y) = (term573 A x y).
Proof. exact (MK_COMB (@lem5037008) (@lem5037007 A x y)). Qed.
Lemma lem5037010 {A : Type'} (x : A) (y : A) : (term574 A x y) = (term574 A x y).
Proof. exact (MK_COMB (@lem5037009 A x y) (@lem5036999 A x y)). Qed.
Lemma lem5037011 {A : Type'} (y : A) : (term582 A y) = (term582 A y).
Proof. exact (fun_ext (fun x : A => @lem5037010 A x y)). Qed.
Lemma lem5037012 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5037013 {A : Type'} (y : A) : (term584 A y) = (term584 A y).
Proof. exact (MK_COMB (@lem5037012 A) (@lem5037011 A y)). Qed.
Lemma lem5037014 {A : Type'} : (term586 A) = (term586 A).
Proof. exact (fun_ext (fun y : A => @lem5037013 A y)). Qed.
Lemma lem5037015 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5037016 {A : Type'} : (term588 A) = (term588 A).
Proof. exact (MK_COMB (@lem5037015 A) (@lem5037014 A)). Qed.
Lemma lem5037039 {A : Type'} : (term587 A) = (term588 A).
Proof. exact (TRANS (@lem5036998 A) (@lem5037016 A)). Qed.
Lemma lem5037040 {A : Type'} : (term588 A) = (term587 A).
Proof. exact (SYM (@lem5037039 A)). Qed.
Lemma lem5037041 {A : Type'} (x : A) (y : A) (h1 : term572 A x y) : term572 A x y.
Proof. exact (h1). Qed.
Lemma lem5037043 (p : Prop) : p = (term85 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5037044 {A : Type'} (x : A) (y : A) : (x = y) = (term589 A x y).
Proof. exact (@lem5037043 (x = y)). Qed.
Lemma lem5037045 {A : Type'} (x : A) (y : A) : (term589 A x y) = (x = y).
Proof. exact (SYM (@lem5037044 A x y)). Qed.
Lemma lem5037046 {A : Type'} (x : A) (y : A) (h1 : term493 A x y) : term493 A x y.
Proof. exact (h1). Qed.
Lemma lem5037061 {A : Type'} (x : A) (x' : A) (y : A) : ((x' = x) = (x' = y)) = (term590 A x x' y).
Proof. exact (@lem17784 (x' = x) (x' = y)). Qed.
Lemma lem5037062 {A : Type'} (x : A) (y : A) : (term571 A x y) = (term591 A x y).
Proof. exact (fun_ext (fun x' : A => @lem5037061 A x x' y)). Qed.
Lemma lem5037063 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5037064 {A : Type'} (x : A) (y : A) : (term572 A x y) = (term592 A x y).
Proof. exact (MK_COMB (@lem5037063 A) (@lem5037062 A x y)). Qed.
Lemma lem5037066 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term147 A P Q) = (term148 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5037067 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term147 A P Q) = (term148 A P Q).
Proof. exact (@lem5037066 A P Q). Qed.
Lemma lem5037068 {A : Type'} (x : A) (y : A) : (term593 A x y) = (term594 A x y).
Proof. exact (@lem5037067 A (term595 A x y) (term596 A x y)). Qed.
Lemma lem5037069 {A : Type'} (x : A) (x' : A) (y : A) : (term597 A x y x') = (term598 A x x' y).
Proof. exact (eq_refl (term597 A x y x')). Qed.
Lemma lem5037070 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5037071 {A : Type'} (x : A) (x' : A) (y : A) : (term599 A x y x') = (term600 A x x' y).
Proof. exact (MK_COMB (@lem5037070) (@lem5037069 A x x' y)). Qed.
Lemma lem5037072 {A : Type'} (x : A) (x' : A) (y : A) : (term601 A x y x') = (term602 A x x' y).
Proof. exact (eq_refl (term601 A x y x')). Qed.
Lemma lem5037073 {A : Type'} (x : A) (x' : A) (y : A) : (term603 A x y x') = (term590 A x x' y).
Proof. exact (MK_COMB (@lem5037071 A x x' y) (@lem5037072 A x x' y)). Qed.
Lemma lem5037074 {A : Type'} (x : A) (y : A) : (term604 A x y) = (term591 A x y).
Proof. exact (fun_ext (fun x' : A => @lem5037073 A x x' y)). Qed.
Lemma lem5037075 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5037076 {A : Type'} (x : A) (y : A) : (term593 A x y) = (term592 A x y).
Proof. exact (MK_COMB (@lem5037075 A) (@lem5037074 A x y)). Qed.
Lemma lem5037077 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5037078 {A : Type'} (x : A) (y : A) : (term605 A x y) = (term606 A x y).
Proof. exact (MK_COMB (@lem5037077) (@lem5037076 A x y)). Qed.
Lemma lem5037079 {A : Type'} (x : A) (x' : A) (y : A) : (term597 A x y x') = (term598 A x x' y).
Proof. exact (eq_refl (term597 A x y x')). Qed.
Lemma lem5037080 {A : Type'} (x : A) (y : A) : (term607 A x y) = (term595 A x y).
Proof. exact (fun_ext (fun x' : A => @lem5037079 A x x' y)). Qed.
Lemma lem5037081 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5037082 {A : Type'} (x : A) (y : A) : (term608 A x y) = (term609 A x y).
Proof. exact (MK_COMB (@lem5037081 A) (@lem5037080 A x y)). Qed.
Lemma lem5037083 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5037084 {A : Type'} (x : A) (y : A) : (term610 A x y) = (term611 A x y).
Proof. exact (MK_COMB (@lem5037083) (@lem5037082 A x y)). Qed.
Lemma lem5037085 {A : Type'} (x : A) (x' : A) (y : A) : (term601 A x y x') = (term602 A x x' y).
Proof. exact (eq_refl (term601 A x y x')). Qed.
Lemma lem5037086 {A : Type'} (x : A) (y : A) : (term612 A x y) = (term596 A x y).
Proof. exact (fun_ext (fun x' : A => @lem5037085 A x x' y)). Qed.
Lemma lem5037087 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5037088 {A : Type'} (x : A) (y : A) : (term613 A x y) = (term614 A x y).
Proof. exact (MK_COMB (@lem5037087 A) (@lem5037086 A x y)). Qed.
Lemma lem5037089 {A : Type'} (x : A) (y : A) : (term594 A x y) = (term615 A x y).
Proof. exact (MK_COMB (@lem5037084 A x y) (@lem5037088 A x y)). Qed.
Lemma lem5037090 {A : Type'} (x : A) (y : A) : ((term593 A x y) = (term594 A x y)) = ((term592 A x y) = (term615 A x y)).
Proof. exact (MK_COMB (@lem5037078 A x y) (@lem5037089 A x y)). Qed.
Lemma lem5037189 {A : Type'} (x : A) (y : A) : (term592 A x y) = (term615 A x y).
Proof. exact (EQ_MP (@lem5037090 A x y) (@lem5037068 A x y)). Qed.
Lemma lem5037190 {A : Type'} (x : A) (y : A) : (term572 A x y) = (term615 A x y).
Proof. exact (TRANS (@lem5037064 A x y) (@lem5037189 A x y)). Qed.
Lemma lem5037191 {A : Type'} (x : A) (y : A) (h1 : term572 A x y) : term615 A x y.
Proof. exact (EQ_MP (@lem5037190 A x y) (@lem5037041 A x y h1)). Qed.
Lemma lem5037197 {A : Type'} (x : A) (y : A) (h1 : term493 A x y) : term493 A x y.
Proof. exact (h1). Qed.
Lemma lem5037212 {A : Type'} (x : A) (x' : A) (y : A) : (term602 A x x' y) = (term602 A x x' y).
Proof. exact (eq_refl (term602 A x x' y)). Qed.
Lemma lem5037213 {A : Type'} (x : A) (y : A) : (term596 A x y) = (term596 A x y).
Proof. exact (fun_ext (fun x' : A => @lem5037212 A x x' y)). Qed.
Lemma lem5037214 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5037215 {A : Type'} (x : A) (y : A) : (term614 A x y) = (term614 A x y).
Proof. exact (MK_COMB (@lem5037214 A) (@lem5037213 A x y)). Qed.
Lemma lem5037230 {A : Type'} (x : A) (x' : A) (y : A) : (term598 A x x' y) = (term598 A x x' y).
Proof. exact (eq_refl (term598 A x x' y)). Qed.
Lemma lem5037231 {A : Type'} (x : A) (y : A) : (term595 A x y) = (term595 A x y).
Proof. exact (fun_ext (fun x' : A => @lem5037230 A x x' y)). Qed.
Lemma lem5037232 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5037233 {A : Type'} (x : A) (y : A) : (term609 A x y) = (term609 A x y).
Proof. exact (MK_COMB (@lem5037232 A) (@lem5037231 A x y)). Qed.
Lemma lem5037234 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5037235 {A : Type'} (x : A) (y : A) : (term611 A x y) = (term611 A x y).
Proof. exact (MK_COMB (@lem5037234) (@lem5037233 A x y)). Qed.
Lemma lem5037236 {A : Type'} (x : A) (y : A) : (term615 A x y) = (term615 A x y).
Proof. exact (MK_COMB (@lem5037235 A x y) (@lem5037215 A x y)). Qed.
Lemma lem5037237 {A : Type'} (x : A) (y : A) (h1 : term572 A x y) : term615 A x y.
Proof. exact (EQ_MP (@lem5037236 A x y) (@lem5037191 A x y h1)). Qed.
Lemma lem5037245 {A : Type'} (x : A) (y : A) (h1 : term493 A x y) : term493 A x y.
Proof. exact (h1). Qed.
Lemma lem5037246 {A : Type'} (x : A) (y : A) (h1 : term572 A x y) : term614 A x y.
Proof. exact (proj2 (@lem5037237 A x y h1)). Qed.
Lemma lem5037251 {A : Type'} (x : A) (y : A) (h1 : term493 A x y) : term493 A x y.
Proof. exact (h1). Qed.
Lemma lem5037272 {A : Type'} (x : A) (x' : A) (y : A) : (term602 A x x' y) = (term602 A x x' y).
Proof. exact (eq_refl (term602 A x x' y)). Qed.
Lemma lem5037273 {A : Type'} (x : A) (y : A) : (term596 A x y) = (term596 A x y).
Proof. exact (fun_ext (fun x' : A => @lem5037272 A x x' y)). Qed.
Lemma lem5037274 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5037276 {A : Type'} (x : A) (y : A) : (term614 A x y) = (term614 A x y).
Proof. exact (MK_COMB (@lem5037274 A) (@lem5037273 A x y)). Qed.
Lemma lem5037277 {A : Type'} (x : A) (y : A) (h1 : term572 A x y) : term614 A x y.
Proof. exact (EQ_MP (@lem5037276 A x y) (@lem5037246 A x y h1)). Qed.
Lemma lem5037281 {A : Type'} (_64733 : A) (x : A) (y : A) (h1 : term572 A x y) : term601 A x y _64733.
Proof. exact (@lem5037277 A x y h1 _64733). Qed.
Lemma lem5037282 {A : Type'} (x : A) (_64733 : A) (y : A) : (term601 A x y _64733) = (term602 A x _64733 y).
Proof. exact (eq_refl (term601 A x y _64733)). Qed.
Lemma lem5037285 {A : Type'} (x : A) (y : A) (h1 : term493 A x y) : term493 A x y.
Proof. exact (h1). Qed.
Lemma lem5037297 {A : Type'} (_64733 : A) (x : A) (y : A) (h1 : term572 A x y) : term602 A x _64733 y.
Proof. exact (EQ_MP (@lem5037282 A x _64733 y) (@lem5037281 A _64733 x y h1)). Qed.
Lemma lem5037301 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem5037302 {A : Type'} (x : A) : x = x.
Proof. exact (@lem5037301 A x). Qed.
Lemma lem5037303 {A : Type'} (x : A) : term489 A x.
Proof. exact (fun h0 : term490 A x => @lem5037302 A x). Qed.
Lemma lem5037305 (p : Prop) : (term418 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5037306 {A : Type'} (x : A) : (term489 A x) = (x = x).
Proof. exact (@lem5037305 (x = x)). Qed.
Lemma lem5037307 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem5037306 A x) (@lem5037303 A x)). Qed.
Lemma lem5037313 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5037314 {A : Type'} (y : A) (_64733 : A) (x : A) : (term602 A x _64733 y) = (term598 A y _64733 x).
Proof. exact (@lem5037313 (_64733 = y) (term493 A _64733 x)). Qed.
Lemma lem5037324 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5037325 {A : Type'} (y : A) (_64733 : A) (x : A) : (term616 A x _64733 y) = (term617 A y _64733 x).
Proof. exact (MK_COMB (@lem5037324) (@lem5037314 A y _64733 x)). Qed.
Lemma lem5037335 {A : Type'} (y : A) (_64733 : A) (x : A) : (term598 A y _64733 x) = (term598 A y _64733 x).
Proof. exact (eq_refl (term598 A y _64733 x)). Qed.
Lemma lem5037336 {A : Type'} (y : A) (_64733 : A) (x : A) : ((term602 A x _64733 y) = (term598 A y _64733 x)) = ((term598 A y _64733 x) = (term598 A y _64733 x)).
Proof. exact (MK_COMB (@lem5037325 A y _64733 x) (@lem5037335 A y _64733 x)). Qed.
Lemma lem5037338 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5037339 (x : Prop) : (x = x) = True.
Proof. exact (@lem5037338 Prop x). Qed.
Lemma lem5037340 {A : Type'} (y : A) (_64733 : A) (x : A) : ((term598 A y _64733 x) = (term598 A y _64733 x)) = True.
Proof. exact (@lem5037339 (term598 A y _64733 x)). Qed.
Lemma lem5037341 {A : Type'} (y : A) (_64733 : A) (x : A) : ((term602 A x _64733 y) = (term598 A y _64733 x)) = True.
Proof. exact (TRANS (@lem5037336 A y _64733 x) (@lem5037340 A y _64733 x)). Qed.
Lemma lem5037342 {A : Type'} (y : A) (_64733 : A) (x : A) : True = ((term602 A x _64733 y) = (term598 A y _64733 x)).
Proof. exact (SYM (@lem5037341 A y _64733 x)). Qed.
Lemma lem5037343 {A : Type'} (y : A) (_64733 : A) (x : A) : (term602 A x _64733 y) = (term598 A y _64733 x).
Proof. exact (EQ_MP (@lem5037342 A y _64733 x) (@lem0)). Qed.
Lemma lem5037344 {A : Type'} (_64733 : A) (x : A) (y : A) (h1 : term572 A x y) : term598 A y _64733 x.
Proof. exact (EQ_MP (@lem5037343 A y _64733 x) (@lem5037297 A _64733 x y h1)). Qed.
Lemma lem5037346 (b : Prop) (a : Prop) : (a \/ b) = (term422 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5037347 {A : Type'} (x : A) (_64733 : A) (y : A) : (term598 A y _64733 x) = (term618 A x _64733 y).
Proof. exact (@lem5037346 (term493 A _64733 x) (_64733 = y)). Qed.
Lemma lem5037349 (a : Prop) : (term92 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5037350 {A : Type'} (_64733 : A) (x : A) : (term503 A _64733 x) = (_64733 = x).
Proof. exact (@lem5037349 (_64733 = x)). Qed.
Lemma lem5037351 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5037352 {A : Type'} (_64733 : A) (x : A) : (term619 A _64733 x) = (term620 A _64733 x).
Proof. exact (MK_COMB (@lem5037351) (@lem5037350 A _64733 x)). Qed.
Lemma lem5037353 {A : Type'} (_64733 : A) (y : A) : (_64733 = y) = (_64733 = y).
Proof. exact (eq_refl (_64733 = y)). Qed.
Lemma lem5037354 {A : Type'} (x : A) (_64733 : A) (y : A) : (term618 A x _64733 y) = (term621 A x _64733 y).
Proof. exact (MK_COMB (@lem5037352 A _64733 x) (@lem5037353 A _64733 y)). Qed.
Lemma lem5037355 {A : Type'} (x : A) (_64733 : A) (y : A) : (term598 A y _64733 x) = (term621 A x _64733 y).
Proof. exact (TRANS (@lem5037347 A x _64733 y) (@lem5037354 A x _64733 y)). Qed.
Lemma lem5037358 {A : Type'} (_64733 : A) (x : A) (y : A) (h1 : term572 A x y) : term621 A x _64733 y.
Proof. exact (EQ_MP (@lem5037355 A x _64733 y) (@lem5037344 A _64733 x y h1)). Qed.
Lemma lem5037359 {A : Type'} (_64733 : A) (x : A) (y : A) (h1 : term572 A x y) : term621 A x _64733 y.
Proof. exact (@lem5037358 A _64733 x y h1). Qed.
Lemma lem5037360 {A : Type'} (x : A) (y : A) (h1 : term572 A x y) : term622 A x y.
Proof. exact (@lem5037359 A x x y h1). Qed.
Lemma lem5037363 {A : Type'} (x : A) (y : A) (h1 : term572 A x y) : x = y.
Proof. exact (@lem5037360 A x y h1 (@lem5037307 A x)). Qed.
Lemma lem5037364 {A : Type'} (x : A) (y : A) (h1 : term572 A x y) : term623 A x y.
Proof. exact (fun h0 : term493 A x y => @lem5037363 A x y h1). Qed.
Lemma lem5037366 (p : Prop) : (term418 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5037367 {A : Type'} (x : A) (y : A) : (term623 A x y) = (x = y).
Proof. exact (@lem5037366 (x = y)). Qed.
Lemma lem5037368 {A : Type'} (x : A) (y : A) (h1 : term572 A x y) : x = y.
Proof. exact (EQ_MP (@lem5037367 A x y) (@lem5037364 A x y h1)). Qed.
Lemma lem5037371 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5037373 {A : Type'} (x : A) (y : A) : (term493 A x y) = (term624 A x y).
Proof. exact (@lem5037371 (x = y)). Qed.
Lemma lem5037376 {A : Type'} (x : A) (y : A) (h1 : term493 A x y) : term624 A x y.
Proof. exact (EQ_MP (@lem5037373 A x y) (@lem5037285 A x y h1)). Qed.
Lemma lem5037379 {A : Type'} (x : A) (y : A) (h1 : term572 A x y) (h2 : term493 A x y) : False.
Proof. exact (@lem5037376 A x y h2 (@lem5037368 A x y h1)). Qed.
Lemma lem5037380 {A : Type'} (x : A) (y : A) (h1 : term572 A x y) (h2 : term493 A x y) : term531.
Proof. exact (fun h0 : ~ False => @lem5037379 A x y h1 h2). Qed.
Lemma lem5037382 (p : Prop) : (term418 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5037383 : term531 = False.
Proof. exact (@lem5037382 False). Qed.
Lemma lem5037384 {A : Type'} (x : A) (y : A) (h1 : term572 A x y) (h2 : term493 A x y) : False.
Proof. exact (EQ_MP (@lem5037383) (@lem5037380 A x y h1 h2)). Qed.
Lemma lem5037385 {A : Type'} (x : A) (y : A) (h1 : term572 A x y) (h2 : term493 A x y) : (term493 A x y) = False.
Proof. exact (prop_ext (fun h3 : term493 A x y => @lem5037384 A x y h1 h2) (fun h3 : False => @lem5037285 A x y h2)). Qed.
Lemma lem5037386 {A : Type'} (x : A) (y : A) (h1 : term572 A x y) (h2 : term493 A x y) : False.
Proof. exact (EQ_MP (@lem5037385 A x y h1 h2) (@lem5037285 A x y h2)). Qed.
Lemma lem5037387 {A : Type'} (x : A) (y : A) (h1 : term572 A x y) (h2 : term493 A x y) : (term493 A x y) = False.
Proof. exact (prop_ext (fun h3 : term493 A x y => @lem5037386 A x y h1 h2) (fun h3 : False => @lem5037251 A x y h2)). Qed.
Lemma lem5037388 {A : Type'} (x : A) (y : A) (h1 : term572 A x y) (h2 : term493 A x y) : False.
Proof. exact (EQ_MP (@lem5037387 A x y h1 h2) (@lem5037251 A x y h2)). Qed.
Lemma lem5037389 {A : Type'} (x : A) (y : A) (h1 : term572 A x y) (h2 : term493 A x y) : (term493 A x y) = False.
Proof. exact (prop_ext (fun h3 : term493 A x y => @lem5037388 A x y h1 h2) (fun h3 : False => @lem5037251 A x y h2)). Qed.
Lemma lem5037390 {A : Type'} (x : A) (y : A) (h1 : term572 A x y) (h2 : term493 A x y) : False.
Proof. exact (EQ_MP (@lem5037389 A x y h1 h2) (@lem5037251 A x y h2)). Qed.
Lemma lem5037391 {A : Type'} (x : A) (y : A) (h1 : term572 A x y) (h2 : term493 A x y) : (term493 A x y) = False.
Proof. exact (prop_ext (fun h3 : term493 A x y => @lem5037390 A x y h1 h2) (fun h3 : False => @lem5037245 A x y h2)). Qed.
Lemma lem5037392 {A : Type'} (x : A) (y : A) (h1 : term572 A x y) (h2 : term493 A x y) : False.
Proof. exact (EQ_MP (@lem5037391 A x y h1 h2) (@lem5037245 A x y h2)). Qed.
Lemma lem5037393 {A : Type'} (x : A) (y : A) (h1 : term572 A x y) (h2 : term493 A x y) : (term493 A x y) = False.
Proof. exact (prop_ext (fun h3 : term493 A x y => @lem5037392 A x y h1 h2) (fun h3 : False => @lem5037197 A x y h2)). Qed.
Lemma lem5037394 {A : Type'} (x : A) (y : A) (h1 : term572 A x y) (h2 : term493 A x y) : False.
Proof. exact (EQ_MP (@lem5037393 A x y h1 h2) (@lem5037197 A x y h2)). Qed.
Lemma lem5037395 {A : Type'} (x : A) (y : A) (h1 : term572 A x y) (h2 : term493 A x y) : (term493 A x y) = False.
Proof. exact (prop_ext (fun h3 : term493 A x y => @lem5037394 A x y h1 h2) (fun h3 : False => @lem5037046 A x y h2)). Qed.
Lemma lem5037396 {A : Type'} (x : A) (y : A) (h1 : term572 A x y) (h2 : term493 A x y) : False.
Proof. exact (EQ_MP (@lem5037395 A x y h1 h2) (@lem5037046 A x y h2)). Qed.
Lemma lem5037397 {A : Type'} (x : A) (y : A) (h1 : term572 A x y) : term589 A x y.
Proof. exact (fun h0 : term493 A x y => @lem5037396 A x y h1 h0). Qed.
Lemma lem5037398 {A : Type'} (x : A) (y : A) (h1 : term572 A x y) : x = y.
Proof. exact (EQ_MP (@lem5037045 A x y) (@lem5037397 A x y h1)). Qed.
Lemma lem5037399 {A : Type'} (x : A) (y : A) : term574 A x y.
Proof. exact (fun h0 : term572 A x y => @lem5037398 A x y h0). Qed.
Lemma lem5037404 {A : Type'} (y : A) : term584 A y.
Proof. exact (fun x : A => @lem5037399 A x y). Qed.
Lemma lem5037409 {A : Type'} : term588 A.
Proof. exact (fun y : A => @lem5037404 A y). Qed.
Lemma lem5037410 {A : Type'} : term587 A.
Proof. exact (EQ_MP (@lem5037040 A) (@lem5037409 A)). Qed.
Lemma lem5037411 {A : Type'} (y : A) : term625 A y.
Proof. exact (@lem5037410 A y). Qed.
Lemma lem5037412 {A : Type'} (y : A) : (term625 A y) = (term583 A y).
Proof. exact (eq_refl (term625 A y)). Qed.
Lemma lem5037413 {A : Type'} (y : A) : term583 A y.
Proof. exact (EQ_MP (@lem5037412 A y) (@lem5037411 A y)). Qed.
Lemma lem5037414 {A : Type'} (y : A) (x : A) : term626 A y x.
Proof. exact (@lem5037413 A y x). Qed.
Lemma lem5037415 {A : Type'} (x : A) (y : A) : (term626 A y x) = (term575 A x y).
Proof. exact (eq_refl (term626 A y x)). Qed.
Lemma lem5037416 {A : Type'} (x : A) (y : A) : term575 A x y.
Proof. exact (EQ_MP (@lem5037415 A x y) (@lem5037414 A y x)). Qed.
Lemma lem5037418 {A : Type'} (x : A) (y : A) : term575 A x y.
Proof. exact (@lem5036959 A x y (@lem5037416 A x y)). Qed.
Lemma lem5037419 {A : Type'} (x : A) (y : A) (h1 : term576 A x y) : False.
Proof. exact (@lem5037418 A x y (@lem5036943 A x y h1)). Qed.
Lemma lem5037420 {A : Type'} (x : A) (y : A) (h1 : term576 A x y) : (term576 A x y) = False.
Proof. exact (prop_ext (fun h2 : term576 A x y => @lem5037419 A x y h1) (fun h2 : False => @lem5036943 A x y h1)). Qed.
Lemma lem5037421 {A : Type'} (x : A) (y : A) (h1 : term576 A x y) : False.
Proof. exact (EQ_MP (@lem5037420 A x y h1) (@lem5036943 A x y h1)). Qed.
Lemma lem5037422 {A : Type'} (x : A) (y : A) : term575 A x y.
Proof. exact (fun h0 : term576 A x y => @lem5037421 A x y h0). Qed.
Lemma lem5037423 {A : Type'} (x : A) (y : A) : term574 A x y.
Proof. exact (EQ_MP (@lem5036942 A x y) (@lem5037422 A x y)). Qed.
Lemma lem5037424 {A : Type'} (x : A) (y : A) : term561 A x y.
Proof. exact (EQ_MP (@lem5036938 A x y) (@lem5037423 A x y)). Qed.
Lemma lem5037425 {A : Type'} (x : A) (y : A) : term558 A x y.
Proof. exact (EQ_MP (@lem5036867 A x y) (@lem5037424 A x y)). Qed.
Lemma lem5037426 {A B : Type'} (f : A -> B) (x : A) (y : A) (u : A -> Prop) (h1 : (f x) = (f y)) (h2 : @IN A x u) (h3 : @IN A y u) : term557 A B u f x y.
Proof. exact (EQ_MP (@lem5036838 A B f x y u h1 h2 h3) (@lem5037425 A x y)). Qed.
Lemma lem5037427 {A B : Type'} (f : A -> B) (x : A) (y : A) (u : A -> Prop) (h1 : term7 A B u f) (h2 : (f x) = (f y)) (h3 : @IN A x u) (h4 : @IN A y u) : x = y.
Proof. exact (@lem5037426 A B f x y u h2 h3 h4 (@lem5036734 A B x y u f h1)). Qed.
Lemma lem5037428 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (y : A) (h1 : term35 A B u x f y) : term33 A B u x f y.
Proof. exact (proj2 (@lem5036724 A B u x f y h1)). Qed.
Lemma lem5037429 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (y : A) (h1 : term35 A B u x f y) : @IN A x u.
Proof. exact (proj1 (@lem5036724 A B u x f y h1)). Qed.
Lemma lem5037430 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (y : A) (h1 : term33 A B u x f y) : (f x) = (f y).
Proof. exact (proj2 (@lem5036725 A B u x f y h1)). Qed.
Lemma lem5037431 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (y : A) (h1 : term33 A B u x f y) : @IN A y u.
Proof. exact (proj1 (@lem5036725 A B u x f y h1)). Qed.
Lemma lem5037432 {A B : Type'} (f : A -> B) (x : A) (y : A) (u : A -> Prop) (h1 : term7 A B u f) (h2 : (f x) = (f y)) (h3 : @IN A x u) (h4 : @IN A y u) : ((f x) = (f y)) = (x = y).
Proof. exact (prop_ext (fun h5 : (f x) = (f y) => @lem5037427 A B f x y u h1 h2 h3 h4) (fun h5 : x = y => @lem5036727 A B x f y h2)). Qed.
Lemma lem5037433 {A B : Type'} (f : A -> B) (x : A) (y : A) (u : A -> Prop) (h1 : term7 A B u f) (h2 : (f x) = (f y)) (h3 : @IN A x u) (h4 : @IN A y u) : x = y.
Proof. exact (EQ_MP (@lem5037432 A B f x y u h1 h2 h3 h4) (@lem5036727 A B x f y h2)). Qed.
Lemma lem5037434 {A B : Type'} (f : A -> B) (x : A) (y : A) (u : A -> Prop) (h1 : term7 A B u f) (h2 : (f x) = (f y)) (h3 : @IN A x u) (h4 : @IN A y u) : (@IN A y u) = (x = y).
Proof. exact (prop_ext (fun h5 : @IN A y u => @lem5037433 A B f x y u h1 h2 h3 h4) (fun h5 : x = y => @lem5036728 A y u h4)). Qed.
Lemma lem5037435 {A B : Type'} (f : A -> B) (x : A) (y : A) (u : A -> Prop) (h1 : term7 A B u f) (h2 : (f x) = (f y)) (h3 : @IN A x u) (h4 : @IN A y u) : x = y.
Proof. exact (EQ_MP (@lem5037434 A B f x y u h1 h2 h3 h4) (@lem5036728 A y u h4)). Qed.
Lemma lem5037436 {A B : Type'} (f : A -> B) (x : A) (y : A) (u : A -> Prop) (h1 : term7 A B u f) (h2 : term33 A B u x f y) (h3 : @IN A x u) (h4 : @IN A y u) : ((f x) = (f y)) = (x = y).
Proof. exact (prop_ext (fun h5 : (f x) = (f y) => @lem5037435 A B f x y u h1 h5 h3 h4) (fun h5 : x = y => @lem5037430 A B u x f y h2)). Qed.
Lemma lem5037437 {A B : Type'} (f : A -> B) (x : A) (y : A) (u : A -> Prop) (h1 : term7 A B u f) (h2 : term33 A B u x f y) (h3 : @IN A x u) (h4 : @IN A y u) : x = y.
Proof. exact (EQ_MP (@lem5037436 A B f x y u h1 h2 h3 h4) (@lem5037430 A B u x f y h2)). Qed.
Lemma lem5037438 {A B : Type'} (f : A -> B) (y : A) (x : A) (u : A -> Prop) (h1 : term7 A B u f) (h2 : term33 A B u x f y) (h3 : @IN A x u) : (@IN A y u) = (x = y).
Proof. exact (prop_ext (fun h4 : @IN A y u => @lem5037437 A B f x y u h1 h2 h3 h4) (fun h4 : x = y => @lem5037431 A B u x f y h2)). Qed.
Lemma lem5037439 {A B : Type'} (f : A -> B) (y : A) (x : A) (u : A -> Prop) (h1 : term7 A B u f) (h2 : term33 A B u x f y) (h3 : @IN A x u) : x = y.
Proof. exact (EQ_MP (@lem5037438 A B f y x u h1 h2 h3) (@lem5037431 A B u x f y h2)). Qed.
Lemma lem5037440 {A B : Type'} (f : A -> B) (y : A) (x : A) (u : A -> Prop) (h1 : term7 A B u f) (h2 : term33 A B u x f y) (h3 : @IN A x u) : (@IN A x u) = (x = y).
Proof. exact (prop_ext (fun h4 : @IN A x u => @lem5037439 A B f y x u h1 h2 h3) (fun h4 : x = y => @lem5036726 A x u h3)). Qed.
Lemma lem5037441 {A B : Type'} (f : A -> B) (y : A) (x : A) (u : A -> Prop) (h1 : term7 A B u f) (h2 : term33 A B u x f y) (h3 : @IN A x u) : x = y.
Proof. exact (EQ_MP (@lem5037440 A B f y x u h1 h2 h3) (@lem5036726 A x u h3)). Qed.
Lemma lem5037442 {A B : Type'} (f : A -> B) (y : A) (x : A) (u : A -> Prop) (h1 : term7 A B u f) (h2 : term35 A B u x f y) (h3 : @IN A x u) : (term33 A B u x f y) = (x = y).
Proof. exact (prop_ext (fun h4 : term33 A B u x f y => @lem5037441 A B f y x u h1 h4 h3) (fun h4 : x = y => @lem5037428 A B u x f y h2)). Qed.
Lemma lem5037443 {A B : Type'} (f : A -> B) (y : A) (x : A) (u : A -> Prop) (h1 : term7 A B u f) (h2 : term35 A B u x f y) (h3 : @IN A x u) : x = y.
Proof. exact (EQ_MP (@lem5037442 A B f y x u h1 h2 h3) (@lem5037428 A B u x f y h2)). Qed.
Lemma lem5037444 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (y : A) (h1 : term7 A B u f) (h2 : term35 A B u x f y) : (@IN A x u) = (x = y).
Proof. exact (prop_ext (fun h3 : @IN A x u => @lem5037443 A B f y x u h1 h2 h3) (fun h3 : x = y => @lem5037429 A B u x f y h2)). Qed.
Lemma lem5037445 {A B : Type'} (u : A -> Prop) (x : A) (f : A -> B) (y : A) (h1 : term7 A B u f) (h2 : term35 A B u x f y) : x = y.
Proof. exact (EQ_MP (@lem5037444 A B u x f y h1 h2) (@lem5037429 A B u x f y h2)). Qed.
Lemma lem5037446 {A B : Type'} (x : A) (y : A) (u : A -> Prop) (f : A -> B) (h1 : term7 A B u f) : term39 A B u f x y.
Proof. exact (fun h0 : term35 A B u x f y => @lem5037445 A B u x f y h1 h0). Qed.
Lemma lem5037451 {A B : Type'} (x : A) (u : A -> Prop) (f : A -> B) (h1 : term7 A B u f) : term43 A B u f x.
Proof. exact (fun y : A => @lem5037446 A B x y u f h1). Qed.
Lemma lem5037456 {A B : Type'} (u : A -> Prop) (f : A -> B) (h1 : term7 A B u f) : term47 A B u f.
Proof. exact (fun x : A => @lem5037451 A B x u f h1). Qed.
Lemma lem5037457 {A B : Type'} (u : A -> Prop) (f : A -> B) : term627 A B u f.
Proof. exact (fun h0 : term7 A B u f => @lem5037456 A B u f h0). Qed.
Lemma lem5037458 {A B : Type'} (u : A -> Prop) (f : A -> B) : term628 A B u f.
Proof. exact (conj (@lem5037457 A B u f) (@lem5036723 A B u f)). Qed.
Lemma lem5037459 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term628 A B u f) = ((term7 A B u f) = (term47 A B u f)).
Proof. exact (@lem32 (term7 A B u f) (term47 A B u f)). Qed.
Lemma lem5037460 {A B : Type'} (u : A -> Prop) (f : A -> B) : (term7 A B u f) = (term47 A B u f).
Proof. exact (EQ_MP (@lem5037459 A B u f) (@lem5037458 A B u f)). Qed.
Lemma lem5037465 {A B : Type'} (f : A -> B) : term629 A B f.
Proof. exact (fun u : A -> Prop => @lem5037460 A B u f). Qed.
Lemma lem5037470 {A B : Type'} : term630 A B.
Proof. exact (fun f : A -> B => @lem5037465 A B f). Qed.
