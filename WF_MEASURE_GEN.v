Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import WF_MEASURE_GEN_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm18392_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
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
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm307612_spec.
Require Import thm309905_spec.
Lemma lem359717 {A : Type'} (lt2 : type1402 A) : (@WF A lt2) = (term0 A lt2).
Proof. exact (EQ_MP (@lem307612 A lt2) (@lem309905 A lt2)). Qed.
Lemma lem359718 {B : Type'} (lt2 : type1402 B) : (@WF B lt2) = (term0 B lt2).
Proof. exact (@lem359717 B lt2). Qed.
Lemma lem359741 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem359742 {B : Type'} (lt2 : type1402 B) : (term1 B lt2) = (term2 B lt2).
Proof. exact (MK_COMB (@lem359741) (@lem359718 B lt2)). Qed.
Lemma lem359744 {A : Type'} (lt2 : type1402 A) : (@WF A lt2) = (term0 A lt2).
Proof. exact (EQ_MP (@lem307612 A lt2) (@lem309905 A lt2)). Qed.
Lemma lem359745 {A : Type'} (lt2 : type1402 A) : (@WF A lt2) = (term0 A lt2).
Proof. exact (@lem359744 A lt2). Qed.
Lemma lem359746 {A B : Type'} (lt2 : type1402 B) (m : A -> B) : (term3 A B lt2 m) = (term4 A B lt2 m).
Proof. exact (@lem359745 A (term5 A B lt2 m)). Qed.
Lemma lem359766 {A B : Type'} (f : A -> B) (y : A) : (term6 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem359767 {A : Type'} (f : type1402 A) (y : A) : (term7 A f y) = (f y).
Proof. exact (@lem359766 A (A -> Prop) f y). Qed.
Lemma lem359768 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (y : A) : (term8 A B lt2 m y) = (term9 A B lt2 m y).
Proof. exact (@lem359767 A (term5 A B lt2 m) y). Qed.
Lemma lem359769 {A B : Type'} (lt2 : type1402 B) (x : A) (m : A -> B) : (term9 A B lt2 m x) = (term10 A B lt2 x m).
Proof. exact (eq_refl (term9 A B lt2 m x)). Qed.
Lemma lem359770 {A B : Type'} (lt2 : type1402 B) (m : A -> B) : (term11 A B lt2 m) = (term5 A B lt2 m).
Proof. exact (fun_ext (fun x : A => @lem359769 A B lt2 x m)). Qed.
Lemma lem359771 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem359772 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (y : A) : (term8 A B lt2 m y) = (term9 A B lt2 m y).
Proof. exact (MK_COMB (@lem359770 A B lt2 m) (@lem359771 A y)). Qed.
Lemma lem359773 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem359774 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (y : A) : (term12 A B lt2 m y) = (term13 A B lt2 m y).
Proof. exact (MK_COMB (@lem359773 A) (@lem359772 A B lt2 m y)). Qed.
Lemma lem359775 {A B : Type'} (lt2 : type1402 B) (y : A) (m : A -> B) : (term9 A B lt2 m y) = (term10 A B lt2 y m).
Proof. exact (eq_refl (term9 A B lt2 m y)). Qed.
Lemma lem359776 {A B : Type'} (lt2 : type1402 B) (y : A) (m : A -> B) : ((term8 A B lt2 m y) = (term9 A B lt2 m y)) = ((term9 A B lt2 m y) = (term10 A B lt2 y m)).
Proof. exact (MK_COMB (@lem359774 A B lt2 m y) (@lem359775 A B lt2 y m)). Qed.
Lemma lem359777 {A B : Type'} (lt2 : type1402 B) (y : A) (m : A -> B) : (term9 A B lt2 m y) = (term10 A B lt2 y m).
Proof. exact (EQ_MP (@lem359776 A B lt2 y m) (@lem359768 A B lt2 m y)). Qed.
Lemma lem359778 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem359779 {A B : Type'} (lt2 : type1402 B) (y : A) (m : A -> B) (x : A) : (term14 A B lt2 m y x) = (term15 A B lt2 y m x).
Proof. exact (MK_COMB (@lem359777 A B lt2 y m) (@lem359778 A x)). Qed.
Lemma lem359781 {A B : Type'} (f : A -> B) (y : A) : (term6 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem359782 {A : Type'} (f : A -> Prop) (y : A) : (term16 A f y) = (f y).
Proof. exact (@lem359781 A Prop f y). Qed.
Lemma lem359783 {A B : Type'} (lt2 : type1402 B) (y : A) (m : A -> B) (x : A) : (term17 A B lt2 y m x) = (term15 A B lt2 y m x).
Proof. exact (@lem359782 A (term10 A B lt2 y m) x). Qed.
Lemma lem359784 {A B : Type'} (lt2 : type1402 B) (y : A) (m : A -> B) (x' : A) : (term15 A B lt2 y m x') = (term18 A B lt2 y m x').
Proof. exact (eq_refl (term15 A B lt2 y m x')). Qed.
Lemma lem359785 {A B : Type'} (lt2 : type1402 B) (y : A) (m : A -> B) : (term19 A B lt2 y m) = (term10 A B lt2 y m).
Proof. exact (fun_ext (fun x' : A => @lem359784 A B lt2 y m x')). Qed.
Lemma lem359786 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem359787 {A B : Type'} (lt2 : type1402 B) (y : A) (m : A -> B) (x : A) : (term17 A B lt2 y m x) = (term15 A B lt2 y m x).
Proof. exact (MK_COMB (@lem359785 A B lt2 y m) (@lem359786 A x)). Qed.
Lemma lem359788 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem359789 {A B : Type'} (lt2 : type1402 B) (y : A) (m : A -> B) (x : A) : (term20 A B lt2 y m x) = (term21 A B lt2 y m x).
Proof. exact (MK_COMB (@lem359788) (@lem359787 A B lt2 y m x)). Qed.
Lemma lem359790 {A B : Type'} (lt2 : type1402 B) (y : A) (m : A -> B) (x : A) : (term15 A B lt2 y m x) = (term18 A B lt2 y m x).
Proof. exact (eq_refl (term15 A B lt2 y m x)). Qed.
Lemma lem359791 {A B : Type'} (lt2 : type1402 B) (y : A) (m : A -> B) (x : A) : ((term17 A B lt2 y m x) = (term15 A B lt2 y m x)) = ((term15 A B lt2 y m x) = (term18 A B lt2 y m x)).
Proof. exact (MK_COMB (@lem359789 A B lt2 y m x) (@lem359790 A B lt2 y m x)). Qed.
Lemma lem359792 {A B : Type'} (lt2 : type1402 B) (y : A) (m : A -> B) (x : A) : (term15 A B lt2 y m x) = (term18 A B lt2 y m x).
Proof. exact (EQ_MP (@lem359791 A B lt2 y m x) (@lem359783 A B lt2 y m x)). Qed.
Lemma lem359793 {A B : Type'} (lt2 : type1402 B) (y : A) (m : A -> B) (x : A) : (term14 A B lt2 m y x) = (term18 A B lt2 y m x).
Proof. exact (TRANS (@lem359779 A B lt2 y m x) (@lem359792 A B lt2 y m x)). Qed.
Lemma lem359794 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem359795 {A B : Type'} (lt2 : type1402 B) (y : A) (m : A -> B) (x : A) : (term22 A B lt2 m y x) = (term23 A B lt2 y m x).
Proof. exact (MK_COMB (@lem359794) (@lem359793 A B lt2 y m x)). Qed.
Lemma lem359796 {A : Type'} (P : A -> Prop) (y : A) : (P y) = (P y).
Proof. exact (eq_refl (P y)). Qed.
Lemma lem359797 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x : A) (P : A -> Prop) (y : A) : (term24 A B lt2 m x P y) = (term25 A B lt2 m x P y).
Proof. exact (MK_COMB (@lem359795 A B lt2 y m x) (@lem359796 A P y)). Qed.
Lemma lem359800 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x : A) (P : A -> Prop) : (term26 A B lt2 m x P) = (term27 A B lt2 m x P).
Proof. exact (fun_ext (fun y : A => @lem359797 A B lt2 m x P y)). Qed.
Lemma lem359801 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem359802 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x : A) (P : A -> Prop) : (term28 A B lt2 m x P) = (term29 A B lt2 m x P).
Proof. exact (MK_COMB (@lem359801 A) (@lem359800 A B lt2 m x P)). Qed.
Lemma lem359807 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem359808 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x : A) (P : A -> Prop) : (term30 A B lt2 m x P) = (term31 A B lt2 m x P).
Proof. exact (MK_COMB (@lem359807) (@lem359802 A B lt2 m x P)). Qed.
Lemma lem359809 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem359810 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (x : A) : (term32 A B lt2 m P x) = (term33 A B lt2 m P x).
Proof. exact (MK_COMB (@lem359808 A B lt2 m x P) (@lem359809 A P x)). Qed.
Lemma lem359813 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term34 A B lt2 m P) = (term35 A B lt2 m P).
Proof. exact (fun_ext (fun x : A => @lem359810 A B lt2 m P x)). Qed.
Lemma lem359814 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem359815 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term36 A B lt2 m P) = (term37 A B lt2 m P).
Proof. exact (MK_COMB (@lem359814 A) (@lem359813 A B lt2 m P)). Qed.
Lemma lem359820 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem359821 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term38 A B lt2 m P) = (term39 A B lt2 m P).
Proof. exact (MK_COMB (@lem359820) (@lem359815 A B lt2 m P)). Qed.
Lemma lem359826 {A : Type'} (P : A -> Prop) : (term40 A P) = (term40 A P).
Proof. exact (eq_refl (term40 A P)). Qed.
Lemma lem359827 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term41 A B lt2 m P) = (term42 A B lt2 m P).
Proof. exact (MK_COMB (@lem359821 A B lt2 m P) (@lem359826 A P)). Qed.
Lemma lem359830 {A B : Type'} (lt2 : type1402 B) (m : A -> B) : (term43 A B lt2 m) = (term44 A B lt2 m).
Proof. exact (fun_ext (fun P : A -> Prop => @lem359827 A B lt2 m P)). Qed.
Lemma lem359831 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem359832 {A B : Type'} (lt2 : type1402 B) (m : A -> B) : (term4 A B lt2 m) = (term45 A B lt2 m).
Proof. exact (MK_COMB (@lem359831 A) (@lem359830 A B lt2 m)). Qed.
Lemma lem359837 {A B : Type'} (lt2 : type1402 B) (m : A -> B) : (term3 A B lt2 m) = (term45 A B lt2 m).
Proof. exact (TRANS (@lem359746 A B lt2 m) (@lem359832 A B lt2 m)). Qed.
Lemma lem359838 {A B : Type'} (lt2 : type1402 B) (m : A -> B) : (term46 A B lt2 m) = (term47 A B lt2 m).
Proof. exact (MK_COMB (@lem359742 B lt2) (@lem359837 A B lt2 m)). Qed.
Lemma lem359841 {A B : Type'} (lt2 : type1402 B) (m : A -> B) : (term47 A B lt2 m) = (term46 A B lt2 m).
Proof. exact (SYM (@lem359838 A B lt2 m)). Qed.
Lemma lem359842 {B : Type'} (lt2 : type1402 B) (h1 : term0 B lt2) : term0 B lt2.
Proof. exact (h1). Qed.
Lemma lem359843 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (h1 : term37 A B lt2 m P) : term37 A B lt2 m P.
Proof. exact (h1). Qed.
Lemma lem359844 {A B : Type'} (m : A -> B) (P : A -> Prop) (lt2 : type1402 B) (h1 : term0 B lt2) : term48 A B lt2 m P.
Proof. exact (@lem359842 B lt2 h1 (term49 A B m P)). Qed.
Lemma lem359845 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term48 A B lt2 m P) = (term50 A B lt2 m P).
Proof. exact (eq_refl (term48 A B lt2 m P)). Qed.
Lemma lem359846 {A B : Type'} (m : A -> B) (P : A -> Prop) (lt2 : type1402 B) (h1 : term0 B lt2) : term50 A B lt2 m P.
Proof. exact (EQ_MP (@lem359845 A B lt2 m P) (@lem359844 A B m P lt2 h1)). Qed.
Lemma lem359878 {A B : Type'} (f : A -> B) (y : A) : (term6 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem359879 {B : Type'} (f : B -> Prop) (y : B) : (term16 B f y) = (f y).
Proof. exact (@lem359878 B Prop f y). Qed.
Lemma lem359880 {A B : Type'} (m : A -> B) (P : A -> Prop) (y : B) : (term51 A B m P y) = (term52 A B m P y).
Proof. exact (@lem359879 B (term49 A B m P) y). Qed.
Lemma lem359881 {A B : Type'} (m : A -> B) (y : B) (P : A -> Prop) : (term52 A B m P y) = (term53 A B m y P).
Proof. exact (eq_refl (term52 A B m P y)). Qed.
Lemma lem359882 {A B : Type'} (m : A -> B) (P : A -> Prop) : (term54 A B m P) = (term49 A B m P).
Proof. exact (fun_ext (fun y : B => @lem359881 A B m y P)). Qed.
Lemma lem359883 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem359884 {A B : Type'} (m : A -> B) (P : A -> Prop) (y : B) : (term51 A B m P y) = (term52 A B m P y).
Proof. exact (MK_COMB (@lem359882 A B m P) (@lem359883 B y)). Qed.
Lemma lem359885 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem359886 {A B : Type'} (m : A -> B) (P : A -> Prop) (y : B) : (term55 A B m P y) = (term56 A B m P y).
Proof. exact (MK_COMB (@lem359885) (@lem359884 A B m P y)). Qed.
Lemma lem359887 {A B : Type'} (m : A -> B) (y : B) (P : A -> Prop) : (term52 A B m P y) = (term53 A B m y P).
Proof. exact (eq_refl (term52 A B m P y)). Qed.
Lemma lem359888 {A B : Type'} (m : A -> B) (y : B) (P : A -> Prop) : ((term51 A B m P y) = (term52 A B m P y)) = ((term52 A B m P y) = (term53 A B m y P)).
Proof. exact (MK_COMB (@lem359886 A B m P y) (@lem359887 A B m y P)). Qed.
Lemma lem359889 {A B : Type'} (m : A -> B) (y : B) (P : A -> Prop) : (term52 A B m P y) = (term53 A B m y P).
Proof. exact (EQ_MP (@lem359888 A B m y P) (@lem359880 A B m P y)). Qed.
Lemma lem359900 {B : Type'} (lt2 : type1402 B) (y : B) (x : B) : (term57 B lt2 y x) = (term57 B lt2 y x).
Proof. exact (eq_refl (term57 B lt2 y x)). Qed.
Lemma lem359901 {A B : Type'} (lt2 : type1402 B) (x : B) (m : A -> B) (y : B) (P : A -> Prop) : (term58 A B lt2 x m P y) = (term59 A B lt2 x m y P).
Proof. exact (MK_COMB (@lem359900 B lt2 y x) (@lem359889 A B m y P)). Qed.
Lemma lem359904 {A B : Type'} (lt2 : type1402 B) (x : B) (m : A -> B) (P : A -> Prop) : (term60 A B lt2 x m P) = (term61 A B lt2 x m P).
Proof. exact (fun_ext (fun y : B => @lem359901 A B lt2 x m y P)). Qed.
Lemma lem359905 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem359906 {A B : Type'} (lt2 : type1402 B) (x : B) (m : A -> B) (P : A -> Prop) : (term62 A B lt2 x m P) = (term63 A B lt2 x m P).
Proof. exact (MK_COMB (@lem359905 B) (@lem359904 A B lt2 x m P)). Qed.
Lemma lem359911 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem359912 {A B : Type'} (lt2 : type1402 B) (x : B) (m : A -> B) (P : A -> Prop) : (term64 A B lt2 x m P) = (term65 A B lt2 x m P).
Proof. exact (MK_COMB (@lem359911) (@lem359906 A B lt2 x m P)). Qed.
Lemma lem359914 {A B : Type'} (f : A -> B) (y : A) : (term6 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem359915 {B : Type'} (f : B -> Prop) (y : B) : (term16 B f y) = (f y).
Proof. exact (@lem359914 B Prop f y). Qed.
Lemma lem359916 {A B : Type'} (m : A -> B) (P : A -> Prop) (x : B) : (term51 A B m P x) = (term52 A B m P x).
Proof. exact (@lem359915 B (term49 A B m P) x). Qed.
Lemma lem359917 {A B : Type'} (m : A -> B) (y : B) (P : A -> Prop) : (term52 A B m P y) = (term53 A B m y P).
Proof. exact (eq_refl (term52 A B m P y)). Qed.
Lemma lem359918 {A B : Type'} (m : A -> B) (P : A -> Prop) : (term54 A B m P) = (term49 A B m P).
Proof. exact (fun_ext (fun y : B => @lem359917 A B m y P)). Qed.
Lemma lem359919 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem359920 {A B : Type'} (m : A -> B) (P : A -> Prop) (x : B) : (term51 A B m P x) = (term52 A B m P x).
Proof. exact (MK_COMB (@lem359918 A B m P) (@lem359919 B x)). Qed.
Lemma lem359921 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem359922 {A B : Type'} (m : A -> B) (P : A -> Prop) (x : B) : (term55 A B m P x) = (term56 A B m P x).
Proof. exact (MK_COMB (@lem359921) (@lem359920 A B m P x)). Qed.
Lemma lem359923 {A B : Type'} (m : A -> B) (x : B) (P : A -> Prop) : (term52 A B m P x) = (term53 A B m x P).
Proof. exact (eq_refl (term52 A B m P x)). Qed.
Lemma lem359924 {A B : Type'} (m : A -> B) (x : B) (P : A -> Prop) : ((term51 A B m P x) = (term52 A B m P x)) = ((term52 A B m P x) = (term53 A B m x P)).
Proof. exact (MK_COMB (@lem359922 A B m P x) (@lem359923 A B m x P)). Qed.
Lemma lem359925 {A B : Type'} (m : A -> B) (x : B) (P : A -> Prop) : (term52 A B m P x) = (term53 A B m x P).
Proof. exact (EQ_MP (@lem359924 A B m x P) (@lem359916 A B m P x)). Qed.
Lemma lem359936 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x : B) (P : A -> Prop) : (term66 A B lt2 m P x) = (term67 A B lt2 m x P).
Proof. exact (MK_COMB (@lem359912 A B lt2 x m P) (@lem359925 A B m x P)). Qed.
Lemma lem359939 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term68 A B lt2 m P) = (term69 A B lt2 m P).
Proof. exact (fun_ext (fun x : B => @lem359936 A B lt2 m x P)). Qed.
Lemma lem359940 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem359941 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term70 A B lt2 m P) = (term71 A B lt2 m P).
Proof. exact (MK_COMB (@lem359940 B) (@lem359939 A B lt2 m P)). Qed.
Lemma lem359946 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem359947 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term72 A B lt2 m P) = (term73 A B lt2 m P).
Proof. exact (MK_COMB (@lem359946) (@lem359941 A B lt2 m P)). Qed.
Lemma lem359953 {A B : Type'} (f : A -> B) (y : A) : (term6 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem359954 {B : Type'} (f : B -> Prop) (y : B) : (term16 B f y) = (f y).
Proof. exact (@lem359953 B Prop f y). Qed.
Lemma lem359955 {A B : Type'} (m : A -> B) (P : A -> Prop) (x : B) : (term51 A B m P x) = (term52 A B m P x).
Proof. exact (@lem359954 B (term49 A B m P) x). Qed.
Lemma lem359956 {A B : Type'} (m : A -> B) (y : B) (P : A -> Prop) : (term52 A B m P y) = (term53 A B m y P).
Proof. exact (eq_refl (term52 A B m P y)). Qed.
Lemma lem359957 {A B : Type'} (m : A -> B) (P : A -> Prop) : (term54 A B m P) = (term49 A B m P).
Proof. exact (fun_ext (fun y : B => @lem359956 A B m y P)). Qed.
Lemma lem359958 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem359959 {A B : Type'} (m : A -> B) (P : A -> Prop) (x : B) : (term51 A B m P x) = (term52 A B m P x).
Proof. exact (MK_COMB (@lem359957 A B m P) (@lem359958 B x)). Qed.
Lemma lem359960 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem359961 {A B : Type'} (m : A -> B) (P : A -> Prop) (x : B) : (term55 A B m P x) = (term56 A B m P x).
Proof. exact (MK_COMB (@lem359960) (@lem359959 A B m P x)). Qed.
Lemma lem359962 {A B : Type'} (m : A -> B) (x : B) (P : A -> Prop) : (term52 A B m P x) = (term53 A B m x P).
Proof. exact (eq_refl (term52 A B m P x)). Qed.
Lemma lem359963 {A B : Type'} (m : A -> B) (x : B) (P : A -> Prop) : ((term51 A B m P x) = (term52 A B m P x)) = ((term52 A B m P x) = (term53 A B m x P)).
Proof. exact (MK_COMB (@lem359961 A B m P x) (@lem359962 A B m x P)). Qed.
Lemma lem359964 {A B : Type'} (m : A -> B) (x : B) (P : A -> Prop) : (term52 A B m P x) = (term53 A B m x P).
Proof. exact (EQ_MP (@lem359963 A B m x P) (@lem359955 A B m P x)). Qed.
Lemma lem359975 {A B : Type'} (m : A -> B) (P : A -> Prop) : (term54 A B m P) = (term49 A B m P).
Proof. exact (fun_ext (fun x : B => @lem359964 A B m x P)). Qed.
Lemma lem359976 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem359977 {A B : Type'} (m : A -> B) (P : A -> Prop) : (term74 A B m P) = (term75 A B m P).
Proof. exact (MK_COMB (@lem359976 B) (@lem359975 A B m P)). Qed.
Lemma lem359982 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term50 A B lt2 m P) = (term76 A B lt2 m P).
Proof. exact (MK_COMB (@lem359947 A B lt2 m P) (@lem359977 A B m P)). Qed.
Lemma lem359985 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem359986 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term77 A B lt2 m P) = (term78 A B lt2 m P).
Proof. exact (MK_COMB (@lem359985) (@lem359982 A B lt2 m P)). Qed.
Lemma lem359987 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem359988 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (x : A) : (term79 A B lt2 m P x) = (term80 A B lt2 m P x).
Proof. exact (MK_COMB (@lem359986 A B lt2 m P) (@lem359987 A P x)). Qed.
Lemma lem359991 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term39 A B lt2 m P) = (term39 A B lt2 m P).
Proof. exact (eq_refl (term39 A B lt2 m P)). Qed.
Lemma lem359992 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (x : A) : (term81 A B lt2 m P x) = (term82 A B lt2 m P x).
Proof. exact (MK_COMB (@lem359991 A B lt2 m P) (@lem359988 A B lt2 m P x)). Qed.
Lemma lem359995 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (x : A) : (term82 A B lt2 m P x) = (term81 A B lt2 m P x).
Proof. exact (SYM (@lem359992 A B lt2 m P x)). Qed.
Lemma lem359997 (p : Prop) : p = (term83 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem359998 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (x : A) : (term82 A B lt2 m P x) = (term84 A B lt2 m P x).
Proof. exact (@lem359997 (term82 A B lt2 m P x)). Qed.
Lemma lem359999 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (x : A) : (term84 A B lt2 m P x) = (term82 A B lt2 m P x).
Proof. exact (SYM (@lem359998 A B lt2 m P x)). Qed.
Lemma lem360000 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (x : A) (h1 : term85 A B lt2 m P x) : term85 A B lt2 m P x.
Proof. exact (h1). Qed.
Lemma lem360003 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (x : A) (h1 : term84 A B lt2 m P x) : term84 A B lt2 m P x.
Proof. exact (h1). Qed.
Lemma lem360004 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (x : A) : term86 A B lt2 m P x.
Proof. exact (fun h0 : term84 A B lt2 m P x => @lem360003 A B lt2 m P x h0). Qed.
Lemma lem360005 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (x : A) (h1 : term86 A B lt2 m P x) : term86 A B lt2 m P x.
Proof. exact (h1). Qed.
Lemma lem360006 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (x : A) (h1 : term84 A B lt2 m P x) : term84 A B lt2 m P x.
Proof. exact (h1). Qed.
Lemma lem360007 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (x : A) (h1 : term84 A B lt2 m P x) (h2 : term86 A B lt2 m P x) : term84 A B lt2 m P x.
Proof. exact (@lem360005 A B lt2 m P x h2 (@lem360006 A B lt2 m P x h1)). Qed.
Lemma lem360008 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (x : A) (h1 : term84 A B lt2 m P x) : term87 A B lt2 m P x.
Proof. exact (fun h0 : term86 A B lt2 m P x => @lem360007 A B lt2 m P x h1 h0). Qed.
Lemma lem360009 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (x : A) (h1 : term86 A B lt2 m P x) : term86 A B lt2 m P x.
Proof. exact (h1). Qed.
Lemma lem360010 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (x : A) (h1 : term84 A B lt2 m P x) (h2 : term86 A B lt2 m P x) : term84 A B lt2 m P x.
Proof. exact (@lem360008 A B lt2 m P x h1 (@lem360009 A B lt2 m P x h2)). Qed.
Lemma lem360011 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (x : A) (h1 : term86 A B lt2 m P x) : term86 A B lt2 m P x.
Proof. exact (fun h0 : term84 A B lt2 m P x => @lem360010 A B lt2 m P x h0 h1). Qed.
Lemma lem360012 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (x : A) : term88 A B lt2 m P x.
Proof. exact (fun h0 : term86 A B lt2 m P x => @lem360011 A B lt2 m P x h0). Qed.
Lemma lem360015 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (x : A) : term86 A B lt2 m P x.
Proof. exact (@lem360012 A B lt2 m P x (@lem360004 A B lt2 m P x)). Qed.
Lemma lem360016 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (x : A) : term86 A B lt2 m P x.
Proof. exact (@lem360015 A B lt2 m P x). Qed.
Lemma lem360034 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem360035 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (x : A) : (term84 A B lt2 m P x) = (term89 A B lt2 m P x).
Proof. exact (@lem360034 (term85 A B lt2 m P x)). Qed.
Lemma lem360037 (t : Prop) : (term90 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem360038 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (x : A) : (term89 A B lt2 m P x) = (term82 A B lt2 m P x).
Proof. exact (@lem360037 (term82 A B lt2 m P x)). Qed.
Lemma lem360041 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (x : A) : (term84 A B lt2 m P x) = (term82 A B lt2 m P x).
Proof. exact (TRANS (@lem360035 A B lt2 m P x) (@lem360038 A B lt2 m P x)). Qed.
Lemma lem360092 {A B : Type'} (m : A -> B) (P : A -> Prop) (x : A) : (term91 A B m P x) = (term92 A B m P x).
Proof. exact (fun_ext (fun lt2 : type1402 B => @lem360041 A B lt2 m P x)). Qed.
Lemma lem360093 {B : Type'} : (@all (B -> B -> Prop)) = (@all (B -> B -> Prop)).
Proof. exact (eq_refl (@all (B -> B -> Prop))). Qed.
Lemma lem360094 {A B : Type'} (m : A -> B) (P : A -> Prop) (x : A) : (term93 A B m P x) = (term94 A B m P x).
Proof. exact (MK_COMB (@lem360093 B) (@lem360092 A B m P x)). Qed.
Lemma lem360099 {A B : Type'} (P : A -> Prop) (x : A) : (term95 A B P x) = (term96 A B P x).
Proof. exact (fun_ext (fun m : A -> B => @lem360094 A B m P x)). Qed.
Lemma lem360100 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem360101 {A B : Type'} (P : A -> Prop) (x : A) : (term97 A B P x) = (term98 A B P x).
Proof. exact (MK_COMB (@lem360100 A B) (@lem360099 A B P x)). Qed.
Lemma lem360106 {A B : Type'} (x : A) : (term99 A B x) = (term100 A B x).
Proof. exact (fun_ext (fun P : A -> Prop => @lem360101 A B P x)). Qed.
Lemma lem360107 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem360108 {A B : Type'} (x : A) : (term101 A B x) = (term102 A B x).
Proof. exact (MK_COMB (@lem360107 A) (@lem360106 A B x)). Qed.
Lemma lem360113 {A B : Type'} : (term103 A B) = (term104 A B).
Proof. exact (fun_ext (fun x : A => @lem360108 A B x)). Qed.
Lemma lem360114 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem360123 {A B : Type'} : (term105 A B) = (term106 A B).
Proof. exact (MK_COMB (@lem360114 A) (@lem360113 A B)). Qed.
Lemma lem360124 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem360129 {A B : Type'} (m : A -> B) (x : B) (P : A -> Prop) (x' : A) : (term107 A B m x P x') = (term107 A B m x P x').
Proof. exact (eq_refl (term107 A B m x P x')). Qed.
Lemma lem360130 {A B : Type'} (m : A -> B) (x : B) (P : A -> Prop) : (term108 A B m x P) = (term108 A B m x P).
Proof. exact (fun_ext (fun x' : A => @lem360129 A B m x P x')). Qed.
Lemma lem360131 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem360132 {A B : Type'} (m : A -> B) (x : B) (P : A -> Prop) : (term53 A B m x P) = (term53 A B m x P).
Proof. exact (MK_COMB (@lem360131 A) (@lem360130 A B m x P)). Qed.
Lemma lem360133 {A B : Type'} (m : A -> B) (P : A -> Prop) : (term49 A B m P) = (term49 A B m P).
Proof. exact (fun_ext (fun x : B => @lem360132 A B m x P)). Qed.
Lemma lem360134 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem360135 {A B : Type'} (m : A -> B) (P : A -> Prop) : (term75 A B m P) = (term75 A B m P).
Proof. exact (MK_COMB (@lem360134 B) (@lem360133 A B m P)). Qed.
Lemma lem360140 {A B : Type'} (m : A -> B) (x : B) (P : A -> Prop) (x' : A) : (term107 A B m x P x') = (term107 A B m x P x').
Proof. exact (eq_refl (term107 A B m x P x')). Qed.
Lemma lem360141 {A B : Type'} (m : A -> B) (x : B) (P : A -> Prop) : (term108 A B m x P) = (term108 A B m x P).
Proof. exact (fun_ext (fun x' : A => @lem360140 A B m x P x')). Qed.
Lemma lem360142 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem360143 {A B : Type'} (m : A -> B) (x : B) (P : A -> Prop) : (term53 A B m x P) = (term53 A B m x P).
Proof. exact (MK_COMB (@lem360142 A) (@lem360141 A B m x P)). Qed.
Lemma lem360148 {A B : Type'} (m : A -> B) (y : B) (P : A -> Prop) (x : A) : (term107 A B m y P x) = (term107 A B m y P x).
Proof. exact (eq_refl (term107 A B m y P x)). Qed.
Lemma lem360149 {A B : Type'} (m : A -> B) (y : B) (P : A -> Prop) : (term108 A B m y P) = (term108 A B m y P).
Proof. exact (fun_ext (fun x : A => @lem360148 A B m y P x)). Qed.
Lemma lem360150 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem360151 {A B : Type'} (m : A -> B) (y : B) (P : A -> Prop) : (term53 A B m y P) = (term53 A B m y P).
Proof. exact (MK_COMB (@lem360150 A) (@lem360149 A B m y P)). Qed.
Lemma lem360154 {B : Type'} (lt2 : type1402 B) (y : B) (x : B) : (term57 B lt2 y x) = (term57 B lt2 y x).
Proof. exact (eq_refl (term57 B lt2 y x)). Qed.
Lemma lem360155 {A B : Type'} (lt2 : type1402 B) (x : B) (m : A -> B) (y : B) (P : A -> Prop) : (term59 A B lt2 x m y P) = (term59 A B lt2 x m y P).
Proof. exact (MK_COMB (@lem360154 B lt2 y x) (@lem360151 A B m y P)). Qed.
Lemma lem360156 {A B : Type'} (lt2 : type1402 B) (x : B) (m : A -> B) (P : A -> Prop) : (term61 A B lt2 x m P) = (term61 A B lt2 x m P).
Proof. exact (fun_ext (fun y : B => @lem360155 A B lt2 x m y P)). Qed.
Lemma lem360157 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem360158 {A B : Type'} (lt2 : type1402 B) (x : B) (m : A -> B) (P : A -> Prop) : (term63 A B lt2 x m P) = (term63 A B lt2 x m P).
Proof. exact (MK_COMB (@lem360157 B) (@lem360156 A B lt2 x m P)). Qed.
Lemma lem360159 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem360160 {A B : Type'} (lt2 : type1402 B) (x : B) (m : A -> B) (P : A -> Prop) : (term65 A B lt2 x m P) = (term65 A B lt2 x m P).
Proof. exact (MK_COMB (@lem360159) (@lem360158 A B lt2 x m P)). Qed.
Lemma lem360161 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x : B) (P : A -> Prop) : (term67 A B lt2 m x P) = (term67 A B lt2 m x P).
Proof. exact (MK_COMB (@lem360160 A B lt2 x m P) (@lem360143 A B m x P)). Qed.
Lemma lem360162 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term69 A B lt2 m P) = (term69 A B lt2 m P).
Proof. exact (fun_ext (fun x : B => @lem360161 A B lt2 m x P)). Qed.
Lemma lem360163 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem360164 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term71 A B lt2 m P) = (term71 A B lt2 m P).
Proof. exact (MK_COMB (@lem360163 B) (@lem360162 A B lt2 m P)). Qed.
Lemma lem360165 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem360166 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term73 A B lt2 m P) = (term73 A B lt2 m P).
Proof. exact (MK_COMB (@lem360165) (@lem360164 A B lt2 m P)). Qed.
Lemma lem360167 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term76 A B lt2 m P) = (term76 A B lt2 m P).
Proof. exact (MK_COMB (@lem360166 A B lt2 m P) (@lem360135 A B m P)). Qed.
Lemma lem360168 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem360169 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term78 A B lt2 m P) = (term78 A B lt2 m P).
Proof. exact (MK_COMB (@lem360168) (@lem360167 A B lt2 m P)). Qed.
Lemma lem360170 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (x : A) : (term80 A B lt2 m P x) = (term80 A B lt2 m P x).
Proof. exact (MK_COMB (@lem360169 A B lt2 m P) (@lem360124 A P x)). Qed.
Lemma lem360171 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem360176 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x : A) (P : A -> Prop) (y : A) : (term25 A B lt2 m x P y) = (term25 A B lt2 m x P y).
Proof. exact (eq_refl (term25 A B lt2 m x P y)). Qed.
Lemma lem360177 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x : A) (P : A -> Prop) : (term27 A B lt2 m x P) = (term27 A B lt2 m x P).
Proof. exact (fun_ext (fun y : A => @lem360176 A B lt2 m x P y)). Qed.
Lemma lem360178 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem360179 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x : A) (P : A -> Prop) : (term29 A B lt2 m x P) = (term29 A B lt2 m x P).
Proof. exact (MK_COMB (@lem360178 A) (@lem360177 A B lt2 m x P)). Qed.
Lemma lem360180 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem360181 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x : A) (P : A -> Prop) : (term31 A B lt2 m x P) = (term31 A B lt2 m x P).
Proof. exact (MK_COMB (@lem360180) (@lem360179 A B lt2 m x P)). Qed.
Lemma lem360182 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (x : A) : (term33 A B lt2 m P x) = (term33 A B lt2 m P x).
Proof. exact (MK_COMB (@lem360181 A B lt2 m x P) (@lem360171 A P x)). Qed.
Lemma lem360183 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term35 A B lt2 m P) = (term35 A B lt2 m P).
Proof. exact (fun_ext (fun x : A => @lem360182 A B lt2 m P x)). Qed.
Lemma lem360184 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem360185 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term37 A B lt2 m P) = (term37 A B lt2 m P).
Proof. exact (MK_COMB (@lem360184 A) (@lem360183 A B lt2 m P)). Qed.
Lemma lem360186 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem360187 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term39 A B lt2 m P) = (term39 A B lt2 m P).
Proof. exact (MK_COMB (@lem360186) (@lem360185 A B lt2 m P)). Qed.
Lemma lem360188 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (x : A) : (term82 A B lt2 m P x) = (term82 A B lt2 m P x).
Proof. exact (MK_COMB (@lem360187 A B lt2 m P) (@lem360170 A B lt2 m P x)). Qed.
Lemma lem360189 {A B : Type'} (m : A -> B) (P : A -> Prop) (x : A) : (term92 A B m P x) = (term92 A B m P x).
Proof. exact (fun_ext (fun lt2 : type1402 B => @lem360188 A B lt2 m P x)). Qed.
Lemma lem360190 {B : Type'} : (@all (B -> B -> Prop)) = (@all (B -> B -> Prop)).
Proof. exact (eq_refl (@all (B -> B -> Prop))). Qed.
Lemma lem360191 {A B : Type'} (m : A -> B) (P : A -> Prop) (x : A) : (term94 A B m P x) = (term94 A B m P x).
Proof. exact (MK_COMB (@lem360190 B) (@lem360189 A B m P x)). Qed.
Lemma lem360192 {A B : Type'} (P : A -> Prop) (x : A) : (term96 A B P x) = (term96 A B P x).
Proof. exact (fun_ext (fun m : A -> B => @lem360191 A B m P x)). Qed.
Lemma lem360193 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem360194 {A B : Type'} (P : A -> Prop) (x : A) : (term98 A B P x) = (term98 A B P x).
Proof. exact (MK_COMB (@lem360193 A B) (@lem360192 A B P x)). Qed.
Lemma lem360195 {A B : Type'} (x : A) : (term100 A B x) = (term100 A B x).
Proof. exact (fun_ext (fun P : A -> Prop => @lem360194 A B P x)). Qed.
Lemma lem360196 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem360197 {A B : Type'} (x : A) : (term102 A B x) = (term102 A B x).
Proof. exact (MK_COMB (@lem360196 A) (@lem360195 A B x)). Qed.
Lemma lem360198 {A B : Type'} : (term104 A B) = (term104 A B).
Proof. exact (fun_ext (fun x : A => @lem360197 A B x)). Qed.
Lemma lem360199 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem360200 {A B : Type'} : (term106 A B) = (term106 A B).
Proof. exact (MK_COMB (@lem360199 A) (@lem360198 A B)). Qed.
Lemma lem360295 {A B : Type'} : (term105 A B) = (term106 A B).
Proof. exact (TRANS (@lem360123 A B) (@lem360200 A B)). Qed.
Lemma lem360296 {A B : Type'} : (term106 A B) = (term105 A B).
Proof. exact (SYM (@lem360295 A B)). Qed.
Lemma lem360297 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (h1 : term37 A B lt2 m P) : term37 A B lt2 m P.
Proof. exact (h1). Qed.
Lemma lem360298 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (h1 : term76 A B lt2 m P) : term76 A B lt2 m P.
Proof. exact (h1). Qed.
Lemma lem360300 (p : Prop) : p = (term83 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem360301 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (term109 A P x).
Proof. exact (@lem360300 (P x)). Qed.
Lemma lem360302 {A : Type'} (P : A -> Prop) (x : A) : (term109 A P x) = (P x).
Proof. exact (SYM (@lem360301 A P x)). Qed.
Lemma lem360303 {A : Type'} (P : A -> Prop) (x : A) (h1 : term110 A P x) : term110 A P x.
Proof. exact (h1). Qed.
Lemma lem360310 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x : A) (P : A -> Prop) (y : A) : (term111 A B lt2 m x P y) = (term112 A B lt2 m x P y).
Proof. exact (@lem17362 (term18 A B lt2 y m x) (P y)). Qed.
Lemma lem360311 {A : Type'} (P : A -> Prop) : (term113 A P) = (term114 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem360312 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x : A) (P : A -> Prop) : (term115 A B lt2 m x P) = (term116 A B lt2 m x P).
Proof. exact (@lem360311 A (term27 A B lt2 m x P)). Qed.
Lemma lem360313 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x : A) (P : A -> Prop) (y : A) : (term117 A B lt2 m x P y) = (term25 A B lt2 m x P y).
Proof. exact (eq_refl (term117 A B lt2 m x P y)). Qed.
Lemma lem360314 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem360315 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x : A) (P : A -> Prop) (y : A) : (term118 A B lt2 m x P y) = (term111 A B lt2 m x P y).
Proof. exact (MK_COMB (@lem360314) (@lem360313 A B lt2 m x P y)). Qed.
Lemma lem360316 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x : A) (P : A -> Prop) (y : A) : (term118 A B lt2 m x P y) = (term112 A B lt2 m x P y).
Proof. exact (TRANS (@lem360315 A B lt2 m x P y) (@lem360310 A B lt2 m x P y)). Qed.
Lemma lem360317 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x : A) (P : A -> Prop) : (term119 A B lt2 m x P) = (term120 A B lt2 m x P).
Proof. exact (fun_ext (fun y : A => @lem360316 A B lt2 m x P y)). Qed.
Lemma lem360318 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem360319 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x : A) (P : A -> Prop) : (term116 A B lt2 m x P) = (term121 A B lt2 m x P).
Proof. exact (MK_COMB (@lem360318 A) (@lem360317 A B lt2 m x P)). Qed.
Lemma lem360320 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x : A) (P : A -> Prop) : (term115 A B lt2 m x P) = (term121 A B lt2 m x P).
Proof. exact (TRANS (@lem360312 A B lt2 m x P) (@lem360319 A B lt2 m x P)). Qed.
Lemma lem360321 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem360322 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem360323 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x : A) (P : A -> Prop) : (term122 A B lt2 m x P) = (term123 A B lt2 m x P).
Proof. exact (MK_COMB (@lem360322) (@lem360320 A B lt2 m x P)). Qed.
Lemma lem360324 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (x : A) : (term124 A B lt2 m P x) = (term125 A B lt2 m P x).
Proof. exact (MK_COMB (@lem360323 A B lt2 m x P) (@lem360321 A P x)). Qed.
Lemma lem360325 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (x : A) : (term33 A B lt2 m P x) = (term124 A B lt2 m P x).
Proof. exact (@lem17265 (term29 A B lt2 m x P) (P x)). Qed.
Lemma lem360326 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (x : A) : (term33 A B lt2 m P x) = (term125 A B lt2 m P x).
Proof. exact (TRANS (@lem360325 A B lt2 m P x) (@lem360324 A B lt2 m P x)). Qed.
Lemma lem360327 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term35 A B lt2 m P) = (term126 A B lt2 m P).
Proof. exact (fun_ext (fun x : A => @lem360326 A B lt2 m P x)). Qed.
Lemma lem360328 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem360329 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term37 A B lt2 m P) = (term127 A B lt2 m P).
Proof. exact (MK_COMB (@lem360328 A) (@lem360327 A B lt2 m P)). Qed.
Lemma lem360412 {A : Type'} (P : A -> Prop) (Q : Prop) : (term128 A P Q) = (term129 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem360413 {A : Type'} (P : A -> Prop) (Q : Prop) : (term128 A P Q) = (term129 A P Q).
Proof. exact (@lem360412 A P Q). Qed.
Lemma lem360414 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (x : A) : (term130 A B lt2 m P x) = (term131 A B lt2 m P x).
Proof. exact (@lem360413 A (term120 A B lt2 m x P) (P x)). Qed.
Lemma lem360415 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x : A) (P : A -> Prop) (y : A) : (term132 A B lt2 m x P y) = (term112 A B lt2 m x P y).
Proof. exact (eq_refl (term132 A B lt2 m x P y)). Qed.
Lemma lem360416 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x : A) (P : A -> Prop) : (term133 A B lt2 m x P) = (term120 A B lt2 m x P).
Proof. exact (fun_ext (fun y : A => @lem360415 A B lt2 m x P y)). Qed.
Lemma lem360417 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem360418 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x : A) (P : A -> Prop) : (term134 A B lt2 m x P) = (term121 A B lt2 m x P).
Proof. exact (MK_COMB (@lem360417 A) (@lem360416 A B lt2 m x P)). Qed.
Lemma lem360419 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem360420 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x : A) (P : A -> Prop) : (term135 A B lt2 m x P) = (term123 A B lt2 m x P).
Proof. exact (MK_COMB (@lem360419) (@lem360418 A B lt2 m x P)). Qed.
Lemma lem360421 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem360422 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (x : A) : (term130 A B lt2 m P x) = (term125 A B lt2 m P x).
Proof. exact (MK_COMB (@lem360420 A B lt2 m x P) (@lem360421 A P x)). Qed.
Lemma lem360423 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem360424 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (x : A) : (term136 A B lt2 m P x) = (term137 A B lt2 m P x).
Proof. exact (MK_COMB (@lem360423) (@lem360422 A B lt2 m P x)). Qed.
Lemma lem360425 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x : A) (P : A -> Prop) (y : A) : (term132 A B lt2 m x P y) = (term112 A B lt2 m x P y).
Proof. exact (eq_refl (term132 A B lt2 m x P y)). Qed.
Lemma lem360426 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem360427 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x : A) (P : A -> Prop) (y : A) : (term138 A B lt2 m x P y) = (term139 A B lt2 m x P y).
Proof. exact (MK_COMB (@lem360426) (@lem360425 A B lt2 m x P y)). Qed.
Lemma lem360428 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem360429 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (y : A) (P : A -> Prop) (x : A) : (term140 A B lt2 m y P x) = (term141 A B lt2 m y P x).
Proof. exact (MK_COMB (@lem360427 A B lt2 m x P y) (@lem360428 A P x)). Qed.
Lemma lem360430 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (x : A) : (term142 A B lt2 m P x) = (term143 A B lt2 m P x).
Proof. exact (fun_ext (fun y : A => @lem360429 A B lt2 m y P x)). Qed.
Lemma lem360431 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem360432 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (x : A) : (term131 A B lt2 m P x) = (term144 A B lt2 m P x).
Proof. exact (MK_COMB (@lem360431 A) (@lem360430 A B lt2 m P x)). Qed.
Lemma lem360433 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (x : A) : ((term130 A B lt2 m P x) = (term131 A B lt2 m P x)) = ((term125 A B lt2 m P x) = (term144 A B lt2 m P x)).
Proof. exact (MK_COMB (@lem360424 A B lt2 m P x) (@lem360432 A B lt2 m P x)). Qed.
Lemma lem360434 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (x : A) : (term125 A B lt2 m P x) = (term144 A B lt2 m P x).
Proof. exact (EQ_MP (@lem360433 A B lt2 m P x) (@lem360414 A B lt2 m P x)). Qed.
Lemma lem360435 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term126 A B lt2 m P) = (term145 A B lt2 m P).
Proof. exact (fun_ext (fun x : A => @lem360434 A B lt2 m P x)). Qed.
Lemma lem360436 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem360437 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term127 A B lt2 m P) = (term146 A B lt2 m P).
Proof. exact (MK_COMB (@lem360436 A) (@lem360435 A B lt2 m P)). Qed.
Lemma lem360439 {A B : Type'} (P : type1413 A B) : (term147 A B P) = (term148 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem360440 {A : Type'} (P : type1402 A) : (term149 A P) = (term150 A P).
Proof. exact (@lem360439 A A P). Qed.
Lemma lem360441 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term151 A B lt2 m P) = (term152 A B lt2 m P).
Proof. exact (@lem360440 A (term153 A B lt2 m P)). Qed.
Lemma lem360442 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (x : A) : (term154 A B lt2 m P x) = (term143 A B lt2 m P x).
Proof. exact (eq_refl (term154 A B lt2 m P x)). Qed.
Lemma lem360443 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem360444 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (x : A) (y : A) : (term155 A B lt2 m P x y) = (term156 A B lt2 m P x y).
Proof. exact (MK_COMB (@lem360442 A B lt2 m P x) (@lem360443 A y)). Qed.
Lemma lem360445 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (y : A) (P : A -> Prop) (x : A) : (term156 A B lt2 m P x y) = (term141 A B lt2 m y P x).
Proof. exact (eq_refl (term156 A B lt2 m P x y)). Qed.
Lemma lem360446 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (y : A) (P : A -> Prop) (x : A) : (term155 A B lt2 m P x y) = (term141 A B lt2 m y P x).
Proof. exact (TRANS (@lem360444 A B lt2 m P x y) (@lem360445 A B lt2 m y P x)). Qed.
Lemma lem360447 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (x : A) : (term157 A B lt2 m P x) = (term143 A B lt2 m P x).
Proof. exact (fun_ext (fun y : A => @lem360446 A B lt2 m y P x)). Qed.
Lemma lem360448 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem360449 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (x : A) : (term158 A B lt2 m P x) = (term144 A B lt2 m P x).
Proof. exact (MK_COMB (@lem360448 A) (@lem360447 A B lt2 m P x)). Qed.
Lemma lem360450 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term159 A B lt2 m P) = (term145 A B lt2 m P).
Proof. exact (fun_ext (fun x : A => @lem360449 A B lt2 m P x)). Qed.
Lemma lem360451 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem360452 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term151 A B lt2 m P) = (term146 A B lt2 m P).
Proof. exact (MK_COMB (@lem360451 A) (@lem360450 A B lt2 m P)). Qed.
Lemma lem360453 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem360454 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term160 A B lt2 m P) = (term161 A B lt2 m P).
Proof. exact (MK_COMB (@lem360453) (@lem360452 A B lt2 m P)). Qed.
Lemma lem360455 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (x : A) : (term154 A B lt2 m P x) = (term143 A B lt2 m P x).
Proof. exact (eq_refl (term154 A B lt2 m P x)). Qed.
Lemma lem360456 {A : Type'} (y : A -> A) (x : A) : (y x) = (y x).
Proof. exact (eq_refl (y x)). Qed.
Lemma lem360457 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (y : A -> A) (x : A) : (term162 A B lt2 m P y x) = (term163 A B lt2 m P y x).
Proof. exact (MK_COMB (@lem360455 A B lt2 m P x) (@lem360456 A y x)). Qed.
Lemma lem360458 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (y : A -> A) (P : A -> Prop) (x : A) : (term163 A B lt2 m P y x) = (term164 A B lt2 m y P x).
Proof. exact (eq_refl (term163 A B lt2 m P y x)). Qed.
Lemma lem360459 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (y : A -> A) (P : A -> Prop) (x : A) : (term162 A B lt2 m P y x) = (term164 A B lt2 m y P x).
Proof. exact (TRANS (@lem360457 A B lt2 m P y x) (@lem360458 A B lt2 m y P x)). Qed.
Lemma lem360460 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (y : A -> A) (P : A -> Prop) : (term165 A B lt2 m P y) = (term166 A B lt2 m y P).
Proof. exact (fun_ext (fun x : A => @lem360459 A B lt2 m y P x)). Qed.
Lemma lem360461 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem360462 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (y : A -> A) (P : A -> Prop) : (term167 A B lt2 m P y) = (term168 A B lt2 m y P).
Proof. exact (MK_COMB (@lem360461 A) (@lem360460 A B lt2 m y P)). Qed.
Lemma lem360463 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term169 A B lt2 m P) = (term170 A B lt2 m P).
Proof. exact (fun_ext (fun y : A -> A => @lem360462 A B lt2 m y P)). Qed.
Lemma lem360464 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem360465 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term152 A B lt2 m P) = (term171 A B lt2 m P).
Proof. exact (MK_COMB (@lem360464 A) (@lem360463 A B lt2 m P)). Qed.
Lemma lem360466 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : ((term151 A B lt2 m P) = (term152 A B lt2 m P)) = ((term146 A B lt2 m P) = (term171 A B lt2 m P)).
Proof. exact (MK_COMB (@lem360454 A B lt2 m P) (@lem360465 A B lt2 m P)). Qed.
Lemma lem360467 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term146 A B lt2 m P) = (term171 A B lt2 m P).
Proof. exact (EQ_MP (@lem360466 A B lt2 m P) (@lem360441 A B lt2 m P)). Qed.
Lemma lem360469 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term127 A B lt2 m P) = (term171 A B lt2 m P).
Proof. exact (TRANS (@lem360437 A B lt2 m P) (@lem360467 A B lt2 m P)). Qed.
Lemma lem360470 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term37 A B lt2 m P) = (term171 A B lt2 m P).
Proof. exact (TRANS (@lem360329 A B lt2 m P) (@lem360469 A B lt2 m P)). Qed.
Lemma lem360471 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (h1 : term37 A B lt2 m P) : term171 A B lt2 m P.
Proof. exact (EQ_MP (@lem360470 A B lt2 m P) (@lem360297 A B lt2 m P h1)). Qed.
Lemma lem360479 {A B : Type'} (m : A -> B) (y : B) (P : A -> Prop) (x : A) : (term107 A B m y P x) = (term172 A B m y P x).
Proof. exact (@lem17265 ((m x) = y) (P x)). Qed.
Lemma lem360480 {A B : Type'} (m : A -> B) (y : B) (P : A -> Prop) : (term108 A B m y P) = (term173 A B m y P).
Proof. exact (fun_ext (fun x : A => @lem360479 A B m y P x)). Qed.
Lemma lem360481 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem360482 {A B : Type'} (m : A -> B) (y : B) (P : A -> Prop) : (term53 A B m y P) = (term174 A B m y P).
Proof. exact (MK_COMB (@lem360481 A) (@lem360480 A B m y P)). Qed.
Lemma lem360484 {B : Type'} (lt2 : type1402 B) (y : B) (x : B) : (term175 B lt2 y x) = (term175 B lt2 y x).
Proof. exact (eq_refl (term175 B lt2 y x)). Qed.
Lemma lem360485 {A B : Type'} (lt2 : type1402 B) (x : B) (m : A -> B) (y : B) (P : A -> Prop) : (term176 A B lt2 x m y P) = (term177 A B lt2 x m y P).
Proof. exact (MK_COMB (@lem360484 B lt2 y x) (@lem360482 A B m y P)). Qed.
Lemma lem360486 {A B : Type'} (lt2 : type1402 B) (x : B) (m : A -> B) (y : B) (P : A -> Prop) : (term59 A B lt2 x m y P) = (term176 A B lt2 x m y P).
Proof. exact (@lem17265 (lt2 y x) (term53 A B m y P)). Qed.
Lemma lem360487 {A B : Type'} (lt2 : type1402 B) (x : B) (m : A -> B) (y : B) (P : A -> Prop) : (term59 A B lt2 x m y P) = (term177 A B lt2 x m y P).
Proof. exact (TRANS (@lem360486 A B lt2 x m y P) (@lem360485 A B lt2 x m y P)). Qed.
Lemma lem360488 {A B : Type'} (lt2 : type1402 B) (x : B) (m : A -> B) (P : A -> Prop) : (term61 A B lt2 x m P) = (term178 A B lt2 x m P).
Proof. exact (fun_ext (fun y : B => @lem360487 A B lt2 x m y P)). Qed.
Lemma lem360489 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem360490 {A B : Type'} (lt2 : type1402 B) (x : B) (m : A -> B) (P : A -> Prop) : (term63 A B lt2 x m P) = (term179 A B lt2 x m P).
Proof. exact (MK_COMB (@lem360489 B) (@lem360488 A B lt2 x m P)). Qed.
Lemma lem360497 {A B : Type'} (m : A -> B) (x : B) (P : A -> Prop) (x' : A) : (term180 A B m x P x') = (term181 A B m x P x').
Proof. exact (@lem17362 ((m x') = x) (P x')). Qed.
Lemma lem360498 {A : Type'} (P : A -> Prop) : (term113 A P) = (term114 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem360499 {A B : Type'} (m : A -> B) (x : B) (P : A -> Prop) : (term182 A B m x P) = (term183 A B m x P).
Proof. exact (@lem360498 A (term108 A B m x P)). Qed.
Lemma lem360500 {A B : Type'} (m : A -> B) (x : B) (P : A -> Prop) (x' : A) : (term184 A B m x P x') = (term107 A B m x P x').
Proof. exact (eq_refl (term184 A B m x P x')). Qed.
Lemma lem360501 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem360502 {A B : Type'} (m : A -> B) (x : B) (P : A -> Prop) (x' : A) : (term185 A B m x P x') = (term180 A B m x P x').
Proof. exact (MK_COMB (@lem360501) (@lem360500 A B m x P x')). Qed.
Lemma lem360503 {A B : Type'} (m : A -> B) (x : B) (P : A -> Prop) (x' : A) : (term185 A B m x P x') = (term181 A B m x P x').
Proof. exact (TRANS (@lem360502 A B m x P x') (@lem360497 A B m x P x')). Qed.
Lemma lem360504 {A B : Type'} (m : A -> B) (x : B) (P : A -> Prop) : (term186 A B m x P) = (term187 A B m x P).
Proof. exact (fun_ext (fun x' : A => @lem360503 A B m x P x')). Qed.
Lemma lem360505 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem360506 {A B : Type'} (m : A -> B) (x : B) (P : A -> Prop) : (term183 A B m x P) = (term188 A B m x P).
Proof. exact (MK_COMB (@lem360505 A) (@lem360504 A B m x P)). Qed.
Lemma lem360507 {A B : Type'} (m : A -> B) (x : B) (P : A -> Prop) : (term182 A B m x P) = (term188 A B m x P).
Proof. exact (TRANS (@lem360499 A B m x P) (@lem360506 A B m x P)). Qed.
Lemma lem360508 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem360509 {A B : Type'} (lt2 : type1402 B) (x : B) (m : A -> B) (P : A -> Prop) : (term189 A B lt2 x m P) = (term190 A B lt2 x m P).
Proof. exact (MK_COMB (@lem360508) (@lem360490 A B lt2 x m P)). Qed.
Lemma lem360510 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x : B) (P : A -> Prop) : (term191 A B lt2 m x P) = (term192 A B lt2 m x P).
Proof. exact (MK_COMB (@lem360509 A B lt2 x m P) (@lem360507 A B m x P)). Qed.
Lemma lem360511 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x : B) (P : A -> Prop) : (term193 A B lt2 m x P) = (term191 A B lt2 m x P).
Proof. exact (@lem17362 (term63 A B lt2 x m P) (term53 A B m x P)). Qed.
Lemma lem360512 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x : B) (P : A -> Prop) : (term193 A B lt2 m x P) = (term192 A B lt2 m x P).
Proof. exact (TRANS (@lem360511 A B lt2 m x P) (@lem360510 A B lt2 m x P)). Qed.
Lemma lem360513 {B : Type'} (P : B -> Prop) : (term113 B P) = (term114 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem360514 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term194 A B lt2 m P) = (term195 A B lt2 m P).
Proof. exact (@lem360513 B (term69 A B lt2 m P)). Qed.
Lemma lem360515 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x : B) (P : A -> Prop) : (term196 A B lt2 m P x) = (term67 A B lt2 m x P).
Proof. exact (eq_refl (term196 A B lt2 m P x)). Qed.
Lemma lem360516 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem360517 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x : B) (P : A -> Prop) : (term197 A B lt2 m P x) = (term193 A B lt2 m x P).
Proof. exact (MK_COMB (@lem360516) (@lem360515 A B lt2 m x P)). Qed.
Lemma lem360518 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x : B) (P : A -> Prop) : (term197 A B lt2 m P x) = (term192 A B lt2 m x P).
Proof. exact (TRANS (@lem360517 A B lt2 m x P) (@lem360512 A B lt2 m x P)). Qed.
Lemma lem360519 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term198 A B lt2 m P) = (term199 A B lt2 m P).
Proof. exact (fun_ext (fun x : B => @lem360518 A B lt2 m x P)). Qed.
Lemma lem360520 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem360521 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term195 A B lt2 m P) = (term200 A B lt2 m P).
Proof. exact (MK_COMB (@lem360520 B) (@lem360519 A B lt2 m P)). Qed.
Lemma lem360522 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term194 A B lt2 m P) = (term200 A B lt2 m P).
Proof. exact (TRANS (@lem360514 A B lt2 m P) (@lem360521 A B lt2 m P)). Qed.
Lemma lem360529 {A B : Type'} (m : A -> B) (x : B) (P : A -> Prop) (x' : A) : (term107 A B m x P x') = (term172 A B m x P x').
Proof. exact (@lem17265 ((m x') = x) (P x')). Qed.
Lemma lem360530 {A B : Type'} (m : A -> B) (x : B) (P : A -> Prop) : (term108 A B m x P) = (term173 A B m x P).
Proof. exact (fun_ext (fun x' : A => @lem360529 A B m x P x')). Qed.
Lemma lem360531 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem360532 {A B : Type'} (m : A -> B) (x : B) (P : A -> Prop) : (term53 A B m x P) = (term174 A B m x P).
Proof. exact (MK_COMB (@lem360531 A) (@lem360530 A B m x P)). Qed.
Lemma lem360533 {A B : Type'} (m : A -> B) (P : A -> Prop) : (term49 A B m P) = (term201 A B m P).
Proof. exact (fun_ext (fun x : B => @lem360532 A B m x P)). Qed.
Lemma lem360534 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem360535 {A B : Type'} (m : A -> B) (P : A -> Prop) : (term75 A B m P) = (term202 A B m P).
Proof. exact (MK_COMB (@lem360534 B) (@lem360533 A B m P)). Qed.
Lemma lem360536 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem360537 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term203 A B lt2 m P) = (term204 A B lt2 m P).
Proof. exact (MK_COMB (@lem360536) (@lem360522 A B lt2 m P)). Qed.
Lemma lem360538 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term205 A B lt2 m P) = (term206 A B lt2 m P).
Proof. exact (MK_COMB (@lem360537 A B lt2 m P) (@lem360535 A B m P)). Qed.
Lemma lem360539 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term76 A B lt2 m P) = (term205 A B lt2 m P).
Proof. exact (@lem17265 (term71 A B lt2 m P) (term75 A B m P)). Qed.
Lemma lem360540 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term76 A B lt2 m P) = (term206 A B lt2 m P).
Proof. exact (TRANS (@lem360539 A B lt2 m P) (@lem360538 A B lt2 m P)). Qed.
Lemma lem360755 {A : Type'} (P : Prop) (Q : A -> Prop) : (term207 A P Q) = (term208 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem360756 {A : Type'} (P : Prop) (Q : A -> Prop) : (term207 A P Q) = (term208 A P Q).
Proof. exact (@lem360755 A P Q). Qed.
Lemma lem360757 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x : B) (P : A -> Prop) : (term209 A B lt2 m x P) = (term210 A B lt2 m x P).
Proof. exact (@lem360756 A (term179 A B lt2 x m P) (term187 A B m x P)). Qed.
Lemma lem360758 {A B : Type'} (m : A -> B) (x : B) (P : A -> Prop) (x' : A) : (term211 A B m x P x') = (term181 A B m x P x').
Proof. exact (eq_refl (term211 A B m x P x')). Qed.
Lemma lem360759 {A B : Type'} (m : A -> B) (x : B) (P : A -> Prop) : (term212 A B m x P) = (term187 A B m x P).
Proof. exact (fun_ext (fun x' : A => @lem360758 A B m x P x')). Qed.
Lemma lem360760 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem360761 {A B : Type'} (m : A -> B) (x : B) (P : A -> Prop) : (term213 A B m x P) = (term188 A B m x P).
Proof. exact (MK_COMB (@lem360760 A) (@lem360759 A B m x P)). Qed.
Lemma lem360762 {A B : Type'} (lt2 : type1402 B) (x : B) (m : A -> B) (P : A -> Prop) : (term190 A B lt2 x m P) = (term190 A B lt2 x m P).
Proof. exact (eq_refl (term190 A B lt2 x m P)). Qed.
Lemma lem360763 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x : B) (P : A -> Prop) : (term209 A B lt2 m x P) = (term192 A B lt2 m x P).
Proof. exact (MK_COMB (@lem360762 A B lt2 x m P) (@lem360761 A B m x P)). Qed.
Lemma lem360764 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem360765 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x : B) (P : A -> Prop) : (term214 A B lt2 m x P) = (term215 A B lt2 m x P).
Proof. exact (MK_COMB (@lem360764) (@lem360763 A B lt2 m x P)). Qed.
Lemma lem360766 {A B : Type'} (m : A -> B) (x : B) (P : A -> Prop) (x' : A) : (term211 A B m x P x') = (term181 A B m x P x').
Proof. exact (eq_refl (term211 A B m x P x')). Qed.
Lemma lem360767 {A B : Type'} (lt2 : type1402 B) (x : B) (m : A -> B) (P : A -> Prop) : (term190 A B lt2 x m P) = (term190 A B lt2 x m P).
Proof. exact (eq_refl (term190 A B lt2 x m P)). Qed.
Lemma lem360768 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x : B) (P : A -> Prop) (x' : A) : (term216 A B lt2 m x P x') = (term217 A B lt2 m x P x').
Proof. exact (MK_COMB (@lem360767 A B lt2 x m P) (@lem360766 A B m x P x')). Qed.
Lemma lem360769 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x : B) (P : A -> Prop) : (term218 A B lt2 m x P) = (term219 A B lt2 m x P).
Proof. exact (fun_ext (fun x' : A => @lem360768 A B lt2 m x P x')). Qed.
Lemma lem360770 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem360771 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x : B) (P : A -> Prop) : (term210 A B lt2 m x P) = (term220 A B lt2 m x P).
Proof. exact (MK_COMB (@lem360770 A) (@lem360769 A B lt2 m x P)). Qed.
Lemma lem360772 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x : B) (P : A -> Prop) : ((term209 A B lt2 m x P) = (term210 A B lt2 m x P)) = ((term192 A B lt2 m x P) = (term220 A B lt2 m x P)).
Proof. exact (MK_COMB (@lem360765 A B lt2 m x P) (@lem360771 A B lt2 m x P)). Qed.
Lemma lem360773 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x : B) (P : A -> Prop) : (term192 A B lt2 m x P) = (term220 A B lt2 m x P).
Proof. exact (EQ_MP (@lem360772 A B lt2 m x P) (@lem360757 A B lt2 m x P)). Qed.
Lemma lem360774 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term199 A B lt2 m P) = (term221 A B lt2 m P).
Proof. exact (fun_ext (fun x : B => @lem360773 A B lt2 m x P)). Qed.
Lemma lem360775 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem360776 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term200 A B lt2 m P) = (term222 A B lt2 m P).
Proof. exact (MK_COMB (@lem360775 B) (@lem360774 A B lt2 m P)). Qed.
Lemma lem360777 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem360778 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term204 A B lt2 m P) = (term223 A B lt2 m P).
Proof. exact (MK_COMB (@lem360777) (@lem360776 A B lt2 m P)). Qed.
Lemma lem360779 {A B : Type'} (m : A -> B) (P : A -> Prop) : (term202 A B m P) = (term202 A B m P).
Proof. exact (eq_refl (term202 A B m P)). Qed.
Lemma lem360780 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term206 A B lt2 m P) = (term224 A B lt2 m P).
Proof. exact (MK_COMB (@lem360778 A B lt2 m P) (@lem360779 A B m P)). Qed.
Lemma lem360782 {A : Type'} (P : A -> Prop) (Q : Prop) : (term128 A P Q) = (term129 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem360783 {B : Type'} (P : B -> Prop) (Q : Prop) : (term128 B P Q) = (term129 B P Q).
Proof. exact (@lem360782 B P Q). Qed.
Lemma lem360784 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term225 A B lt2 m P) = (term226 A B lt2 m P).
Proof. exact (@lem360783 B (term221 A B lt2 m P) (term202 A B m P)). Qed.
Lemma lem360785 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x : B) (P : A -> Prop) : (term227 A B lt2 m P x) = (term220 A B lt2 m x P).
Proof. exact (eq_refl (term227 A B lt2 m P x)). Qed.
Lemma lem360786 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term228 A B lt2 m P) = (term221 A B lt2 m P).
Proof. exact (fun_ext (fun x : B => @lem360785 A B lt2 m x P)). Qed.
Lemma lem360787 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem360788 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term229 A B lt2 m P) = (term222 A B lt2 m P).
Proof. exact (MK_COMB (@lem360787 B) (@lem360786 A B lt2 m P)). Qed.
Lemma lem360789 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem360790 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term230 A B lt2 m P) = (term223 A B lt2 m P).
Proof. exact (MK_COMB (@lem360789) (@lem360788 A B lt2 m P)). Qed.
Lemma lem360791 {A B : Type'} (m : A -> B) (P : A -> Prop) : (term202 A B m P) = (term202 A B m P).
Proof. exact (eq_refl (term202 A B m P)). Qed.
Lemma lem360792 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term225 A B lt2 m P) = (term224 A B lt2 m P).
Proof. exact (MK_COMB (@lem360790 A B lt2 m P) (@lem360791 A B m P)). Qed.
Lemma lem360793 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem360794 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term231 A B lt2 m P) = (term232 A B lt2 m P).
Proof. exact (MK_COMB (@lem360793) (@lem360792 A B lt2 m P)). Qed.
Lemma lem360795 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x : B) (P : A -> Prop) : (term227 A B lt2 m P x) = (term220 A B lt2 m x P).
Proof. exact (eq_refl (term227 A B lt2 m P x)). Qed.
Lemma lem360796 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem360797 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x : B) (P : A -> Prop) : (term233 A B lt2 m P x) = (term234 A B lt2 m x P).
Proof. exact (MK_COMB (@lem360796) (@lem360795 A B lt2 m x P)). Qed.
Lemma lem360798 {A B : Type'} (m : A -> B) (P : A -> Prop) : (term202 A B m P) = (term202 A B m P).
Proof. exact (eq_refl (term202 A B m P)). Qed.
Lemma lem360799 {A B : Type'} (lt2 : type1402 B) (x : B) (m : A -> B) (P : A -> Prop) : (term235 A B lt2 x m P) = (term236 A B lt2 x m P).
Proof. exact (MK_COMB (@lem360797 A B lt2 m x P) (@lem360798 A B m P)). Qed.
Lemma lem360800 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term237 A B lt2 m P) = (term238 A B lt2 m P).
Proof. exact (fun_ext (fun x : B => @lem360799 A B lt2 x m P)). Qed.
Lemma lem360801 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem360802 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term226 A B lt2 m P) = (term239 A B lt2 m P).
Proof. exact (MK_COMB (@lem360801 B) (@lem360800 A B lt2 m P)). Qed.
Lemma lem360803 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : ((term225 A B lt2 m P) = (term226 A B lt2 m P)) = ((term224 A B lt2 m P) = (term239 A B lt2 m P)).
Proof. exact (MK_COMB (@lem360794 A B lt2 m P) (@lem360802 A B lt2 m P)). Qed.
Lemma lem360804 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term224 A B lt2 m P) = (term239 A B lt2 m P).
Proof. exact (EQ_MP (@lem360803 A B lt2 m P) (@lem360784 A B lt2 m P)). Qed.
Lemma lem360806 {A : Type'} (P : A -> Prop) (Q : Prop) : (term128 A P Q) = (term129 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem360807 {A : Type'} (P : A -> Prop) (Q : Prop) : (term128 A P Q) = (term129 A P Q).
Proof. exact (@lem360806 A P Q). Qed.
Lemma lem360808 {A B : Type'} (lt2 : type1402 B) (x : B) (m : A -> B) (P : A -> Prop) : (term240 A B lt2 x m P) = (term241 A B lt2 x m P).
Proof. exact (@lem360807 A (term219 A B lt2 m x P) (term202 A B m P)). Qed.
Lemma lem360809 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x : B) (P : A -> Prop) (x' : A) : (term242 A B lt2 m x P x') = (term217 A B lt2 m x P x').
Proof. exact (eq_refl (term242 A B lt2 m x P x')). Qed.
Lemma lem360810 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x : B) (P : A -> Prop) : (term243 A B lt2 m x P) = (term219 A B lt2 m x P).
Proof. exact (fun_ext (fun x' : A => @lem360809 A B lt2 m x P x')). Qed.
Lemma lem360811 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem360812 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x : B) (P : A -> Prop) : (term244 A B lt2 m x P) = (term220 A B lt2 m x P).
Proof. exact (MK_COMB (@lem360811 A) (@lem360810 A B lt2 m x P)). Qed.
Lemma lem360813 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem360814 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x : B) (P : A -> Prop) : (term245 A B lt2 m x P) = (term234 A B lt2 m x P).
Proof. exact (MK_COMB (@lem360813) (@lem360812 A B lt2 m x P)). Qed.
Lemma lem360815 {A B : Type'} (m : A -> B) (P : A -> Prop) : (term202 A B m P) = (term202 A B m P).
Proof. exact (eq_refl (term202 A B m P)). Qed.
Lemma lem360816 {A B : Type'} (lt2 : type1402 B) (x : B) (m : A -> B) (P : A -> Prop) : (term240 A B lt2 x m P) = (term236 A B lt2 x m P).
Proof. exact (MK_COMB (@lem360814 A B lt2 m x P) (@lem360815 A B m P)). Qed.
Lemma lem360817 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem360818 {A B : Type'} (lt2 : type1402 B) (x : B) (m : A -> B) (P : A -> Prop) : (term246 A B lt2 x m P) = (term247 A B lt2 x m P).
Proof. exact (MK_COMB (@lem360817) (@lem360816 A B lt2 x m P)). Qed.
Lemma lem360819 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x : B) (P : A -> Prop) (x' : A) : (term242 A B lt2 m x P x') = (term217 A B lt2 m x P x').
Proof. exact (eq_refl (term242 A B lt2 m x P x')). Qed.
Lemma lem360820 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem360821 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x : B) (P : A -> Prop) (x' : A) : (term248 A B lt2 m x P x') = (term249 A B lt2 m x P x').
Proof. exact (MK_COMB (@lem360820) (@lem360819 A B lt2 m x P x')). Qed.
Lemma lem360822 {A B : Type'} (m : A -> B) (P : A -> Prop) : (term202 A B m P) = (term202 A B m P).
Proof. exact (eq_refl (term202 A B m P)). Qed.
Lemma lem360823 {A B : Type'} (lt2 : type1402 B) (x : B) (x' : A) (m : A -> B) (P : A -> Prop) : (term250 A B lt2 x x' m P) = (term251 A B lt2 x x' m P).
Proof. exact (MK_COMB (@lem360821 A B lt2 m x P x') (@lem360822 A B m P)). Qed.
Lemma lem360824 {A B : Type'} (lt2 : type1402 B) (x : B) (m : A -> B) (P : A -> Prop) : (term252 A B lt2 x m P) = (term253 A B lt2 x m P).
Proof. exact (fun_ext (fun x' : A => @lem360823 A B lt2 x x' m P)). Qed.
Lemma lem360825 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem360826 {A B : Type'} (lt2 : type1402 B) (x : B) (m : A -> B) (P : A -> Prop) : (term241 A B lt2 x m P) = (term254 A B lt2 x m P).
Proof. exact (MK_COMB (@lem360825 A) (@lem360824 A B lt2 x m P)). Qed.
Lemma lem360827 {A B : Type'} (lt2 : type1402 B) (x : B) (m : A -> B) (P : A -> Prop) : ((term240 A B lt2 x m P) = (term241 A B lt2 x m P)) = ((term236 A B lt2 x m P) = (term254 A B lt2 x m P)).
Proof. exact (MK_COMB (@lem360818 A B lt2 x m P) (@lem360826 A B lt2 x m P)). Qed.
Lemma lem360828 {A B : Type'} (lt2 : type1402 B) (x : B) (m : A -> B) (P : A -> Prop) : (term236 A B lt2 x m P) = (term254 A B lt2 x m P).
Proof. exact (EQ_MP (@lem360827 A B lt2 x m P) (@lem360808 A B lt2 x m P)). Qed.
Lemma lem360829 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term238 A B lt2 m P) = (term255 A B lt2 m P).
Proof. exact (fun_ext (fun x : B => @lem360828 A B lt2 x m P)). Qed.
Lemma lem360830 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem360831 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term239 A B lt2 m P) = (term256 A B lt2 m P).
Proof. exact (MK_COMB (@lem360830 B) (@lem360829 A B lt2 m P)). Qed.
Lemma lem360832 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term224 A B lt2 m P) = (term256 A B lt2 m P).
Proof. exact (TRANS (@lem360804 A B lt2 m P) (@lem360831 A B lt2 m P)). Qed.
Lemma lem360834 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term206 A B lt2 m P) = (term256 A B lt2 m P).
Proof. exact (TRANS (@lem360780 A B lt2 m P) (@lem360832 A B lt2 m P)). Qed.
Lemma lem360835 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) : (term76 A B lt2 m P) = (term256 A B lt2 m P).
Proof. exact (TRANS (@lem360540 A B lt2 m P) (@lem360834 A B lt2 m P)). Qed.
Lemma lem360836 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (h1 : term76 A B lt2 m P) : term256 A B lt2 m P.
Proof. exact (EQ_MP (@lem360835 A B lt2 m P) (@lem360298 A B lt2 m P h1)). Qed.
Lemma lem360842 {A : Type'} (P : A -> Prop) (x : A) (h1 : term110 A P x) : term110 A P x.
Proof. exact (h1). Qed.
Lemma lem360843 {A B : Type'} (lt2 : type1402 B) (x' : B) (m : A -> B) (P : A -> Prop) (h1 : term254 A B lt2 x' m P) : term254 A B lt2 x' m P.
Proof. exact (h1). Qed.
Lemma lem360844 {A B : Type'} (lt2 : type1402 B) (x' : B) (x'' : A) (m : A -> B) (P : A -> Prop) (h1 : term251 A B lt2 x' x'' m P) : term251 A B lt2 x' x'' m P.
Proof. exact (h1). Qed.
Lemma lem360845 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (y : A -> A) (P : A -> Prop) (h1 : term168 A B lt2 m y P) : term168 A B lt2 m y P.
Proof. exact (h1). Qed.
Lemma lem360851 {A : Type'} (P : A -> Prop) (x : A) (h1 : term110 A P x) : term110 A P x.
Proof. exact (h1). Qed.
Lemma lem360866 {A B : Type'} (m : A -> B) (x : B) (P : A -> Prop) (x' : A) : (term172 A B m x P x') = (term172 A B m x P x').
Proof. exact (eq_refl (term172 A B m x P x')). Qed.
Lemma lem360867 {A B : Type'} (m : A -> B) (x : B) (P : A -> Prop) : (term173 A B m x P) = (term173 A B m x P).
Proof. exact (fun_ext (fun x' : A => @lem360866 A B m x P x')). Qed.
Lemma lem360868 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem360869 {A B : Type'} (m : A -> B) (x : B) (P : A -> Prop) : (term174 A B m x P) = (term174 A B m x P).
Proof. exact (MK_COMB (@lem360868 A) (@lem360867 A B m x P)). Qed.
Lemma lem360870 {A B : Type'} (m : A -> B) (P : A -> Prop) : (term201 A B m P) = (term201 A B m P).
Proof. exact (fun_ext (fun x : B => @lem360869 A B m x P)). Qed.
Lemma lem360871 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem360872 {A B : Type'} (m : A -> B) (P : A -> Prop) : (term202 A B m P) = (term202 A B m P).
Proof. exact (MK_COMB (@lem360871 B) (@lem360870 A B m P)). Qed.
Lemma lem360887 {A B : Type'} (m : A -> B) (x' : B) (P : A -> Prop) (x'' : A) : (term181 A B m x' P x'') = (term181 A B m x' P x'').
Proof. exact (eq_refl (term181 A B m x' P x'')). Qed.
Lemma lem360902 {A B : Type'} (m : A -> B) (y : B) (P : A -> Prop) (x : A) : (term172 A B m y P x) = (term172 A B m y P x).
Proof. exact (eq_refl (term172 A B m y P x)). Qed.
Lemma lem360903 {A B : Type'} (m : A -> B) (y : B) (P : A -> Prop) : (term173 A B m y P) = (term173 A B m y P).
Proof. exact (fun_ext (fun x : A => @lem360902 A B m y P x)). Qed.
Lemma lem360904 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem360905 {A B : Type'} (m : A -> B) (y : B) (P : A -> Prop) : (term174 A B m y P) = (term174 A B m y P).
Proof. exact (MK_COMB (@lem360904 A) (@lem360903 A B m y P)). Qed.
Lemma lem360914 {B : Type'} (lt2 : type1402 B) (y : B) (x' : B) : (term175 B lt2 y x') = (term175 B lt2 y x').
Proof. exact (eq_refl (term175 B lt2 y x')). Qed.
Lemma lem360915 {A B : Type'} (lt2 : type1402 B) (x' : B) (m : A -> B) (y : B) (P : A -> Prop) : (term177 A B lt2 x' m y P) = (term177 A B lt2 x' m y P).
Proof. exact (MK_COMB (@lem360914 B lt2 y x') (@lem360905 A B m y P)). Qed.
Lemma lem360916 {A B : Type'} (lt2 : type1402 B) (x' : B) (m : A -> B) (P : A -> Prop) : (term178 A B lt2 x' m P) = (term178 A B lt2 x' m P).
Proof. exact (fun_ext (fun y : B => @lem360915 A B lt2 x' m y P)). Qed.
Lemma lem360917 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem360918 {A B : Type'} (lt2 : type1402 B) (x' : B) (m : A -> B) (P : A -> Prop) : (term179 A B lt2 x' m P) = (term179 A B lt2 x' m P).
Proof. exact (MK_COMB (@lem360917 B) (@lem360916 A B lt2 x' m P)). Qed.
Lemma lem360919 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem360920 {A B : Type'} (lt2 : type1402 B) (x' : B) (m : A -> B) (P : A -> Prop) : (term190 A B lt2 x' m P) = (term190 A B lt2 x' m P).
Proof. exact (MK_COMB (@lem360919) (@lem360918 A B lt2 x' m P)). Qed.
Lemma lem360921 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x' : B) (P : A -> Prop) (x'' : A) : (term217 A B lt2 m x' P x'') = (term217 A B lt2 m x' P x'').
Proof. exact (MK_COMB (@lem360920 A B lt2 x' m P) (@lem360887 A B m x' P x'')). Qed.
Lemma lem360922 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem360923 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x' : B) (P : A -> Prop) (x'' : A) : (term249 A B lt2 m x' P x'') = (term249 A B lt2 m x' P x'').
Proof. exact (MK_COMB (@lem360922) (@lem360921 A B lt2 m x' P x'')). Qed.
Lemma lem360924 {A B : Type'} (lt2 : type1402 B) (x' : B) (x'' : A) (m : A -> B) (P : A -> Prop) : (term251 A B lt2 x' x'' m P) = (term251 A B lt2 x' x'' m P).
Proof. exact (MK_COMB (@lem360923 A B lt2 m x' P x'') (@lem360872 A B m P)). Qed.
Lemma lem360925 {A B : Type'} (lt2 : type1402 B) (x' : B) (x'' : A) (m : A -> B) (P : A -> Prop) (h1 : term251 A B lt2 x' x'' m P) : term251 A B lt2 x' x'' m P.
Proof. exact (EQ_MP (@lem360924 A B lt2 x' x'' m P) (@lem360844 A B lt2 x' x'' m P h1)). Qed.
Lemma lem360952 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (y : A -> A) (P : A -> Prop) (x : A) : (term164 A B lt2 m y P x) = (term164 A B lt2 m y P x).
Proof. exact (eq_refl (term164 A B lt2 m y P x)). Qed.
Lemma lem360953 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (y : A -> A) (P : A -> Prop) : (term166 A B lt2 m y P) = (term166 A B lt2 m y P).
Proof. exact (fun_ext (fun x : A => @lem360952 A B lt2 m y P x)). Qed.
Lemma lem360954 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem360955 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (y : A -> A) (P : A -> Prop) : (term168 A B lt2 m y P) = (term168 A B lt2 m y P).
Proof. exact (MK_COMB (@lem360954 A) (@lem360953 A B lt2 m y P)). Qed.
Lemma lem360956 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (y : A -> A) (P : A -> Prop) (h1 : term168 A B lt2 m y P) : term168 A B lt2 m y P.
Proof. exact (EQ_MP (@lem360955 A B lt2 m y P) (@lem360845 A B lt2 m y P h1)). Qed.
Lemma lem360957 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x' : B) (P : A -> Prop) (x'' : A) (h1 : term217 A B lt2 m x' P x'') : term217 A B lt2 m x' P x''.
Proof. exact (h1). Qed.
Lemma lem360958 {A B : Type'} (m : A -> B) (P : A -> Prop) (h1 : term202 A B m P) : term202 A B m P.
Proof. exact (h1). Qed.
Lemma lem360959 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x' : B) (P : A -> Prop) (x'' : A) (h1 : term217 A B lt2 m x' P x'') : term181 A B m x' P x''.
Proof. exact (proj2 (@lem360957 A B lt2 m x' P x'' h1)). Qed.
Lemma lem360960 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x' : B) (P : A -> Prop) (x'' : A) (h1 : term217 A B lt2 m x' P x'') : term179 A B lt2 x' m P.
Proof. exact (proj1 (@lem360957 A B lt2 m x' P x'' h1)). Qed.
Lemma lem360984 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (y : A -> A) (P : A -> Prop) (x : A) : (term164 A B lt2 m y P x) = (term257 A B lt2 m y P x).
Proof. exact (@lem19699 (term258 A B lt2 y m x) (term259 A P y x) (P x)). Qed.
Lemma lem360985 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (y : A -> A) (P : A -> Prop) : (term166 A B lt2 m y P) = (term260 A B lt2 m y P).
Proof. exact (fun_ext (fun x : A => @lem360984 A B lt2 m y P x)). Qed.
Lemma lem360986 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem360988 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (y : A -> A) (P : A -> Prop) : (term168 A B lt2 m y P) = (term261 A B lt2 m y P).
Proof. exact (MK_COMB (@lem360986 A) (@lem360985 A B lt2 m y P)). Qed.
Lemma lem360989 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (y : A -> A) (P : A -> Prop) (h1 : term168 A B lt2 m y P) : term261 A B lt2 m y P.
Proof. exact (EQ_MP (@lem360988 A B lt2 m y P) (@lem360956 A B lt2 m y P h1)). Qed.
Lemma lem360991 {A : Type'} (P : Prop) (Q : A -> Prop) : (term262 A P Q) = (term263 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem360992 {A : Type'} (P : Prop) (Q : A -> Prop) : (term262 A P Q) = (term263 A P Q).
Proof. exact (@lem360991 A P Q). Qed.
Lemma lem360993 {A B : Type'} (lt2 : type1402 B) (x' : B) (m : A -> B) (y : B) (P : A -> Prop) : (term264 A B lt2 x' m y P) = (term265 A B lt2 x' m y P).
Proof. exact (@lem360992 A (term266 B lt2 y x') (term173 A B m y P)). Qed.
Lemma lem360994 {A B : Type'} (m : A -> B) (y : B) (P : A -> Prop) (x : A) : (term267 A B m y P x) = (term172 A B m y P x).
Proof. exact (eq_refl (term267 A B m y P x)). Qed.
Lemma lem360995 {A B : Type'} (m : A -> B) (y : B) (P : A -> Prop) : (term268 A B m y P) = (term173 A B m y P).
Proof. exact (fun_ext (fun x : A => @lem360994 A B m y P x)). Qed.
Lemma lem360996 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem360997 {A B : Type'} (m : A -> B) (y : B) (P : A -> Prop) : (term269 A B m y P) = (term174 A B m y P).
Proof. exact (MK_COMB (@lem360996 A) (@lem360995 A B m y P)). Qed.
Lemma lem360998 {B : Type'} (lt2 : type1402 B) (y : B) (x' : B) : (term175 B lt2 y x') = (term175 B lt2 y x').
Proof. exact (eq_refl (term175 B lt2 y x')). Qed.
Lemma lem360999 {A B : Type'} (lt2 : type1402 B) (x' : B) (m : A -> B) (y : B) (P : A -> Prop) : (term264 A B lt2 x' m y P) = (term177 A B lt2 x' m y P).
Proof. exact (MK_COMB (@lem360998 B lt2 y x') (@lem360997 A B m y P)). Qed.
Lemma lem361000 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem361001 {A B : Type'} (lt2 : type1402 B) (x' : B) (m : A -> B) (y : B) (P : A -> Prop) : (term270 A B lt2 x' m y P) = (term271 A B lt2 x' m y P).
Proof. exact (MK_COMB (@lem361000) (@lem360999 A B lt2 x' m y P)). Qed.
Lemma lem361002 {A B : Type'} (m : A -> B) (y : B) (P : A -> Prop) (x : A) : (term267 A B m y P x) = (term172 A B m y P x).
Proof. exact (eq_refl (term267 A B m y P x)). Qed.
Lemma lem361003 {B : Type'} (lt2 : type1402 B) (y : B) (x' : B) : (term175 B lt2 y x') = (term175 B lt2 y x').
Proof. exact (eq_refl (term175 B lt2 y x')). Qed.
Lemma lem361004 {A B : Type'} (lt2 : type1402 B) (x' : B) (m : A -> B) (y : B) (P : A -> Prop) (x : A) : (term272 A B lt2 x' m y P x) = (term273 A B lt2 x' m y P x).
Proof. exact (MK_COMB (@lem361003 B lt2 y x') (@lem361002 A B m y P x)). Qed.
Lemma lem361005 {A B : Type'} (lt2 : type1402 B) (x' : B) (m : A -> B) (y : B) (P : A -> Prop) : (term274 A B lt2 x' m y P) = (term275 A B lt2 x' m y P).
Proof. exact (fun_ext (fun x : A => @lem361004 A B lt2 x' m y P x)). Qed.
Lemma lem361006 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem361007 {A B : Type'} (lt2 : type1402 B) (x' : B) (m : A -> B) (y : B) (P : A -> Prop) : (term265 A B lt2 x' m y P) = (term276 A B lt2 x' m y P).
Proof. exact (MK_COMB (@lem361006 A) (@lem361005 A B lt2 x' m y P)). Qed.
Lemma lem361008 {A B : Type'} (lt2 : type1402 B) (x' : B) (m : A -> B) (y : B) (P : A -> Prop) : ((term264 A B lt2 x' m y P) = (term265 A B lt2 x' m y P)) = ((term177 A B lt2 x' m y P) = (term276 A B lt2 x' m y P)).
Proof. exact (MK_COMB (@lem361001 A B lt2 x' m y P) (@lem361007 A B lt2 x' m y P)). Qed.
Lemma lem361009 {A B : Type'} (lt2 : type1402 B) (x' : B) (m : A -> B) (y : B) (P : A -> Prop) : (term177 A B lt2 x' m y P) = (term276 A B lt2 x' m y P).
Proof. exact (EQ_MP (@lem361008 A B lt2 x' m y P) (@lem360993 A B lt2 x' m y P)). Qed.
Lemma lem361010 {A B : Type'} (lt2 : type1402 B) (x' : B) (m : A -> B) (P : A -> Prop) : (term178 A B lt2 x' m P) = (term277 A B lt2 x' m P).
Proof. exact (fun_ext (fun y : B => @lem361009 A B lt2 x' m y P)). Qed.
Lemma lem361011 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem361012 {A B : Type'} (lt2 : type1402 B) (x' : B) (m : A -> B) (P : A -> Prop) : (term179 A B lt2 x' m P) = (term278 A B lt2 x' m P).
Proof. exact (MK_COMB (@lem361011 B) (@lem361010 A B lt2 x' m P)). Qed.
Lemma lem361025 {A B : Type'} (lt2 : type1402 B) (x' : B) (m : A -> B) (y : B) (P : A -> Prop) (x : A) : (term273 A B lt2 x' m y P x) = (term273 A B lt2 x' m y P x).
Proof. exact (eq_refl (term273 A B lt2 x' m y P x)). Qed.
Lemma lem361026 {A B : Type'} (lt2 : type1402 B) (x' : B) (m : A -> B) (y : B) (P : A -> Prop) : (term275 A B lt2 x' m y P) = (term275 A B lt2 x' m y P).
Proof. exact (fun_ext (fun x : A => @lem361025 A B lt2 x' m y P x)). Qed.
Lemma lem361027 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem361028 {A B : Type'} (lt2 : type1402 B) (x' : B) (m : A -> B) (y : B) (P : A -> Prop) : (term276 A B lt2 x' m y P) = (term276 A B lt2 x' m y P).
Proof. exact (MK_COMB (@lem361027 A) (@lem361026 A B lt2 x' m y P)). Qed.
Lemma lem361029 {A B : Type'} (lt2 : type1402 B) (x' : B) (m : A -> B) (P : A -> Prop) : (term277 A B lt2 x' m P) = (term277 A B lt2 x' m P).
Proof. exact (fun_ext (fun y : B => @lem361028 A B lt2 x' m y P)). Qed.
Lemma lem361030 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem361031 {A B : Type'} (lt2 : type1402 B) (x' : B) (m : A -> B) (P : A -> Prop) : (term278 A B lt2 x' m P) = (term278 A B lt2 x' m P).
Proof. exact (MK_COMB (@lem361030 B) (@lem361029 A B lt2 x' m P)). Qed.
Lemma lem361032 {A B : Type'} (lt2 : type1402 B) (x' : B) (m : A -> B) (P : A -> Prop) : (term179 A B lt2 x' m P) = (term278 A B lt2 x' m P).
Proof. exact (TRANS (@lem361012 A B lt2 x' m P) (@lem361031 A B lt2 x' m P)). Qed.
Lemma lem361033 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x' : B) (P : A -> Prop) (x'' : A) (h1 : term217 A B lt2 m x' P x'') : term278 A B lt2 x' m P.
Proof. exact (EQ_MP (@lem361032 A B lt2 x' m P) (@lem360960 A B lt2 m x' P x'' h1)). Qed.
Lemma lem361045 {A : Type'} (P : A -> Prop) (x : A) (h1 : term110 A P x) : term110 A P x.
Proof. exact (h1). Qed.
Lemma lem361076 {A B : Type'} (m : A -> B) (x : B) (P : A -> Prop) (x' : A) : (term172 A B m x P x') = (term172 A B m x P x').
Proof. exact (eq_refl (term172 A B m x P x')). Qed.
Lemma lem361077 {A B : Type'} (m : A -> B) (x : B) (P : A -> Prop) : (term173 A B m x P) = (term173 A B m x P).
Proof. exact (fun_ext (fun x' : A => @lem361076 A B m x P x')). Qed.
Lemma lem361078 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem361079 {A B : Type'} (m : A -> B) (x : B) (P : A -> Prop) : (term174 A B m x P) = (term174 A B m x P).
Proof. exact (MK_COMB (@lem361078 A) (@lem361077 A B m x P)). Qed.
Lemma lem361080 {A B : Type'} (m : A -> B) (P : A -> Prop) : (term201 A B m P) = (term201 A B m P).
Proof. exact (fun_ext (fun x : B => @lem361079 A B m x P)). Qed.
Lemma lem361081 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem361083 {A B : Type'} (m : A -> B) (P : A -> Prop) : (term202 A B m P) = (term202 A B m P).
Proof. exact (MK_COMB (@lem361081 B) (@lem361080 A B m P)). Qed.
Lemma lem361084 {A B : Type'} (m : A -> B) (P : A -> Prop) (h1 : term202 A B m P) : term202 A B m P.
Proof. exact (EQ_MP (@lem361083 A B m P) (@lem360958 A B m P h1)). Qed.
Lemma lem361085 {A B : Type'} (_7795 : A) (lt2 : type1402 B) (m : A -> B) (y : A -> A) (P : A -> Prop) (h1 : term168 A B lt2 m y P) : term279 A B lt2 m y P _7795.
Proof. exact (@lem360989 A B lt2 m y P h1 _7795). Qed.
Lemma lem361086 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (y : A -> A) (P : A -> Prop) (_7795 : A) : (term279 A B lt2 m y P _7795) = (term257 A B lt2 m y P _7795).
Proof. exact (eq_refl (term279 A B lt2 m y P _7795)). Qed.
Lemma lem361087 {A B : Type'} (_7795 : A) (lt2 : type1402 B) (m : A -> B) (y : A -> A) (P : A -> Prop) (h1 : term168 A B lt2 m y P) : term257 A B lt2 m y P _7795.
Proof. exact (EQ_MP (@lem361086 A B lt2 m y P _7795) (@lem361085 A B _7795 lt2 m y P h1)). Qed.
Lemma lem361088 {A B : Type'} (_7796 : B) (lt2 : type1402 B) (m : A -> B) (x' : B) (P : A -> Prop) (x'' : A) (h1 : term217 A B lt2 m x' P x'') : term280 A B lt2 x' m P _7796.
Proof. exact (@lem361033 A B lt2 m x' P x'' h1 _7796). Qed.
Lemma lem361089 {A B : Type'} (lt2 : type1402 B) (x' : B) (m : A -> B) (_7796 : B) (P : A -> Prop) : (term280 A B lt2 x' m P _7796) = (term276 A B lt2 x' m _7796 P).
Proof. exact (eq_refl (term280 A B lt2 x' m P _7796)). Qed.
Lemma lem361090 {A B : Type'} (_7796 : B) (lt2 : type1402 B) (m : A -> B) (x' : B) (P : A -> Prop) (x'' : A) (h1 : term217 A B lt2 m x' P x'') : term276 A B lt2 x' m _7796 P.
Proof. exact (EQ_MP (@lem361089 A B lt2 x' m _7796 P) (@lem361088 A B _7796 lt2 m x' P x'' h1)). Qed.
Lemma lem361091 {A B : Type'} (_7796 : B) (_7797 : A) (lt2 : type1402 B) (m : A -> B) (x' : B) (P : A -> Prop) (x'' : A) (h1 : term217 A B lt2 m x' P x'') : term281 A B lt2 x' m _7796 P _7797.
Proof. exact (@lem361090 A B _7796 lt2 m x' P x'' h1 _7797). Qed.
Lemma lem361092 {A B : Type'} (lt2 : type1402 B) (x' : B) (m : A -> B) (_7796 : B) (P : A -> Prop) (_7797 : A) : (term281 A B lt2 x' m _7796 P _7797) = (term273 A B lt2 x' m _7796 P _7797).
Proof. exact (eq_refl (term281 A B lt2 x' m _7796 P _7797)). Qed.
Lemma lem361097 {A B : Type'} (_7799 : B) (m : A -> B) (P : A -> Prop) (h1 : term202 A B m P) : term282 A B m P _7799.
Proof. exact (@lem361084 A B m P h1 _7799). Qed.
Lemma lem361098 {A B : Type'} (m : A -> B) (_7799 : B) (P : A -> Prop) : (term282 A B m P _7799) = (term174 A B m _7799 P).
Proof. exact (eq_refl (term282 A B m P _7799)). Qed.
Lemma lem361099 {A B : Type'} (_7799 : B) (m : A -> B) (P : A -> Prop) (h1 : term202 A B m P) : term174 A B m _7799 P.
Proof. exact (EQ_MP (@lem361098 A B m _7799 P) (@lem361097 A B _7799 m P h1)). Qed.
Lemma lem361100 {A B : Type'} (_7799 : B) (_7800 : A) (m : A -> B) (P : A -> Prop) (h1 : term202 A B m P) : term267 A B m _7799 P _7800.
Proof. exact (@lem361099 A B _7799 m P h1 _7800). Qed.
Lemma lem361101 {A B : Type'} (m : A -> B) (_7799 : B) (P : A -> Prop) (_7800 : A) : (term267 A B m _7799 P _7800) = (term172 A B m _7799 P _7800).
Proof. exact (eq_refl (term267 A B m _7799 P _7800)). Qed.
Lemma lem361118 {A B : Type'} (_7796 : B) (_7797 : A) (lt2 : type1402 B) (m : A -> B) (x' : B) (P : A -> Prop) (x'' : A) (h1 : term217 A B lt2 m x' P x'') : term273 A B lt2 x' m _7796 P _7797.
Proof. exact (EQ_MP (@lem361092 A B lt2 x' m _7796 P _7797) (@lem361091 A B _7796 _7797 lt2 m x' P x'' h1)). Qed.
Lemma lem361120 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x' : B) (P : A -> Prop) (x'' : A) (h1 : term217 A B lt2 m x' P x'') : (m x'') = x'.
Proof. exact (proj1 (@lem360959 A B lt2 m x' P x'' h1)). Qed.
Lemma lem361136 {A : Type'} (P : A -> Prop) (x : A) (h1 : term110 A P x) : term110 A P x.
Proof. exact (h1). Qed.
Lemma lem361142 {A B : Type'} (_7799 : B) (_7800 : A) (m : A -> B) (P : A -> Prop) (h1 : term202 A B m P) : term172 A B m _7799 P _7800.
Proof. exact (EQ_MP (@lem361101 A B m _7799 P _7800) (@lem361100 A B _7799 _7800 m P h1)). Qed.
Lemma lem361155 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x' : B) (P : A -> Prop) (x'' : A) (h1 : term217 A B lt2 m x' P x'') : x' = (m x'').
Proof. exact (SYM (@lem361120 A B lt2 m x' P x'' h1)). Qed.
Lemma lem361184 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (_7796 : B) (P : A -> Prop) (_7797 : A) : (term283 A B lt2 m _7796 P _7797) = (term283 A B lt2 m _7796 P _7797).
Proof. exact (eq_refl (term283 A B lt2 m _7796 P _7797)). Qed.
Lemma lem361185 {A B : Type'} (_7796 : B) (_7797 : A) (lt2 : type1402 B) (m : A -> B) (x' : B) (P : A -> Prop) (x'' : A) (h1 : term217 A B lt2 m x' P x'') : (term284 A B lt2 m _7796 P _7797 x') = (term285 A B lt2 _7796 P _7797 m x'').
Proof. exact (MK_COMB (@lem361184 A B lt2 m _7796 P _7797) (@lem361155 A B lt2 m x' P x'' h1)). Qed.
Lemma lem361186 {A B : Type'} (lt2 : type1402 B) (x'' : A) (m : A -> B) (_7796 : B) (P : A -> Prop) (_7797 : A) : (term285 A B lt2 _7796 P _7797 m x'') = (term286 A B lt2 x'' m _7796 P _7797).
Proof. exact (eq_refl (term285 A B lt2 _7796 P _7797 m x'')). Qed.
Lemma lem361187 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (_7796 : B) (P : A -> Prop) (_7797 : A) (x' : B) : (term287 A B lt2 m _7796 P _7797 x') = (term287 A B lt2 m _7796 P _7797 x').
Proof. exact (eq_refl (term287 A B lt2 m _7796 P _7797 x')). Qed.
Lemma lem361188 {A B : Type'} (x' : B) (lt2 : type1402 B) (x'' : A) (m : A -> B) (_7796 : B) (P : A -> Prop) (_7797 : A) : ((term284 A B lt2 m _7796 P _7797 x') = (term285 A B lt2 _7796 P _7797 m x'')) = ((term284 A B lt2 m _7796 P _7797 x') = (term286 A B lt2 x'' m _7796 P _7797)).
Proof. exact (MK_COMB (@lem361187 A B lt2 m _7796 P _7797 x') (@lem361186 A B lt2 x'' m _7796 P _7797)). Qed.
Lemma lem361189 {A B : Type'} (lt2 : type1402 B) (x' : B) (m : A -> B) (_7796 : B) (P : A -> Prop) (_7797 : A) : (term284 A B lt2 m _7796 P _7797 x') = (term273 A B lt2 x' m _7796 P _7797).
Proof. exact (eq_refl (term284 A B lt2 m _7796 P _7797 x')). Qed.
Lemma lem361190 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem361191 {A B : Type'} (lt2 : type1402 B) (x' : B) (m : A -> B) (_7796 : B) (P : A -> Prop) (_7797 : A) : (term287 A B lt2 m _7796 P _7797 x') = (term288 A B lt2 x' m _7796 P _7797).
Proof. exact (MK_COMB (@lem361190) (@lem361189 A B lt2 x' m _7796 P _7797)). Qed.
Lemma lem361192 {A B : Type'} (lt2 : type1402 B) (x'' : A) (m : A -> B) (_7796 : B) (P : A -> Prop) (_7797 : A) : (term286 A B lt2 x'' m _7796 P _7797) = (term286 A B lt2 x'' m _7796 P _7797).
Proof. exact (eq_refl (term286 A B lt2 x'' m _7796 P _7797)). Qed.
Lemma lem361193 {A B : Type'} (x' : B) (lt2 : type1402 B) (x'' : A) (m : A -> B) (_7796 : B) (P : A -> Prop) (_7797 : A) : ((term284 A B lt2 m _7796 P _7797 x') = (term286 A B lt2 x'' m _7796 P _7797)) = ((term273 A B lt2 x' m _7796 P _7797) = (term286 A B lt2 x'' m _7796 P _7797)).
Proof. exact (MK_COMB (@lem361191 A B lt2 x' m _7796 P _7797) (@lem361192 A B lt2 x'' m _7796 P _7797)). Qed.
Lemma lem361194 {A B : Type'} (x' : B) (lt2 : type1402 B) (x'' : A) (m : A -> B) (_7796 : B) (P : A -> Prop) (_7797 : A) : ((term284 A B lt2 m _7796 P _7797 x') = (term285 A B lt2 _7796 P _7797 m x'')) = ((term273 A B lt2 x' m _7796 P _7797) = (term286 A B lt2 x'' m _7796 P _7797)).
Proof. exact (TRANS (@lem361188 A B x' lt2 x'' m _7796 P _7797) (@lem361193 A B x' lt2 x'' m _7796 P _7797)). Qed.
Lemma lem361195 {A B : Type'} (_7796 : B) (_7797 : A) (lt2 : type1402 B) (m : A -> B) (x' : B) (P : A -> Prop) (x'' : A) (h1 : term217 A B lt2 m x' P x'') : (term273 A B lt2 x' m _7796 P _7797) = (term286 A B lt2 x'' m _7796 P _7797).
Proof. exact (EQ_MP (@lem361194 A B x' lt2 x'' m _7796 P _7797) (@lem361185 A B _7796 _7797 lt2 m x' P x'' h1)). Qed.
Lemma lem361196 {A B : Type'} (_7796 : B) (_7797 : A) (lt2 : type1402 B) (m : A -> B) (x' : B) (P : A -> Prop) (x'' : A) (h1 : term217 A B lt2 m x' P x'') : term286 A B lt2 x'' m _7796 P _7797.
Proof. exact (EQ_MP (@lem361195 A B _7796 _7797 lt2 m x' P x'' h1) (@lem361118 A B _7796 _7797 lt2 m x' P x'' h1)). Qed.
Lemma lem361210 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x' : B) (P : A -> Prop) (x'' : A) (h1 : term217 A B lt2 m x' P x'') : term110 A P x''.
Proof. exact (proj2 (@lem360959 A B lt2 m x' P x'' h1)). Qed.
Lemma lem361224 {A B : Type'} (_7795 : A) (lt2 : type1402 B) (m : A -> B) (y : A -> A) (P : A -> Prop) (h1 : term168 A B lt2 m y P) : term289 A B lt2 y m P _7795.
Proof. exact (proj1 (@lem361087 A B _7795 lt2 m y P h1)). Qed.
Lemma lem361238 {A B : Type'} (_7795 : A) (lt2 : type1402 B) (m : A -> B) (y : A -> A) (P : A -> Prop) (h1 : term168 A B lt2 m y P) : term290 A y P _7795.
Proof. exact (proj2 (@lem361087 A B _7795 lt2 m y P h1)). Qed.
Lemma lem361292 {A : Type'} (P : A -> Prop) (x'' : A) (h1 : term110 A P x'') : term110 A P x''.
Proof. exact (h1). Qed.
Lemma lem361293 {A : Type'} (P : A -> Prop) (x'' : A) (h1 : term110 A P x'') : term291 A P x''.
Proof. exact (fun h0 : P x'' => @lem361292 A P x'' h1). Qed.
Lemma lem361295 (p : Prop) : (term292 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem361296 {A : Type'} (P : A -> Prop) (x'' : A) : (term291 A P x'') = (term110 A P x'').
Proof. exact (@lem361295 (P x'')). Qed.
Lemma lem361297 {A : Type'} (P : A -> Prop) (x'' : A) (h1 : term110 A P x'') : term110 A P x''.
Proof. exact (EQ_MP (@lem361296 A P x'') (@lem361293 A P x'' h1)). Qed.
Lemma lem361299 (b : Prop) (a : Prop) : (a \/ b) = (term293 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem361302 {A B : Type'} (P : A -> Prop) (lt2 : type1402 B) (y : A -> A) (m : A -> B) (_7795 : A) : (term289 A B lt2 y m P _7795) = (term294 A B P lt2 y m _7795).
Proof. exact (@lem361299 (P _7795) (term258 A B lt2 y m _7795)). Qed.
Lemma lem361305 {A B : Type'} (_7795 : A) (lt2 : type1402 B) (m : A -> B) (y : A -> A) (P : A -> Prop) (h1 : term168 A B lt2 m y P) : term294 A B P lt2 y m _7795.
Proof. exact (EQ_MP (@lem361302 A B P lt2 y m _7795) (@lem361224 A B _7795 lt2 m y P h1)). Qed.
Lemma lem361306 {A B : Type'} (_7795 : A) (lt2 : type1402 B) (m : A -> B) (y : A -> A) (P : A -> Prop) (h1 : term168 A B lt2 m y P) : term294 A B P lt2 y m _7795.
Proof. exact (@lem361305 A B _7795 lt2 m y P h1). Qed.
Lemma lem361307 {A B : Type'} (x'' : A) (lt2 : type1402 B) (m : A -> B) (y : A -> A) (P : A -> Prop) (h1 : term168 A B lt2 m y P) : term294 A B P lt2 y m x''.
Proof. exact (@lem361306 A B x'' lt2 m y P h1). Qed.
Lemma lem361310 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (y : A -> A) (P : A -> Prop) (x'' : A) (h1 : term168 A B lt2 m y P) (h2 : term110 A P x'') : term258 A B lt2 y m x''.
Proof. exact (@lem361307 A B x'' lt2 m y P h1 (@lem361297 A P x'' h2)). Qed.
Lemma lem361311 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (y : A -> A) (P : A -> Prop) (x'' : A) (h1 : term168 A B lt2 m y P) (h2 : term110 A P x'') : term295 A B lt2 y m x''.
Proof. exact (fun h0 : term296 A B lt2 y m x'' => @lem361310 A B lt2 m y P x'' h1 h2). Qed.
Lemma lem361313 (p : Prop) : (term297 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem361314 {A B : Type'} (lt2 : type1402 B) (y : A -> A) (m : A -> B) (x'' : A) : (term295 A B lt2 y m x'') = (term258 A B lt2 y m x'').
Proof. exact (@lem361313 (term258 A B lt2 y m x'')). Qed.
Lemma lem361315 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (y : A -> A) (P : A -> Prop) (x'' : A) (h1 : term168 A B lt2 m y P) (h2 : term110 A P x'') : term258 A B lt2 y m x''.
Proof. exact (EQ_MP (@lem361314 A B lt2 y m x'') (@lem361311 A B lt2 m y P x'' h1 h2)). Qed.
Lemma lem361317 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem361318 {B : Type'} (x : B) : x = x.
Proof. exact (@lem361317 B x). Qed.
Lemma lem361319 {A B : Type'} (m : A -> B) (y : A -> A) (x'' : A) : (term298 A B m y x'') = (term298 A B m y x'').
Proof. exact (@lem361318 B (term298 A B m y x'')). Qed.
Lemma lem361320 {A B : Type'} (m : A -> B) (y : A -> A) (x'' : A) : term299 A B m y x''.
Proof. exact (fun h0 : term300 A B m y x'' => @lem361319 A B m y x''). Qed.
Lemma lem361322 (p : Prop) : (term297 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem361323 {A B : Type'} (m : A -> B) (y : A -> A) (x'' : A) : (term299 A B m y x'') = ((term298 A B m y x'') = (term298 A B m y x'')).
Proof. exact (@lem361322 ((term298 A B m y x'') = (term298 A B m y x''))). Qed.
Lemma lem361324 {A B : Type'} (m : A -> B) (y : A -> A) (x'' : A) : (term298 A B m y x'') = (term298 A B m y x'').
Proof. exact (EQ_MP (@lem361323 A B m y x'') (@lem361320 A B m y x'')). Qed.
Lemma lem361340 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem361341 {A B : Type'} (P : A -> Prop) (m : A -> B) (_7797 : A) (_7796 : B) : (term172 A B m _7796 P _7797) = (term301 A B P m _7797 _7796).
Proof. exact (@lem361340 (P _7797) (term302 A B m _7797 _7796)). Qed.
Lemma lem361349 {A B : Type'} (lt2 : type1402 B) (_7796 : B) (m : A -> B) (x'' : A) : (term303 A B lt2 _7796 m x'') = (term303 A B lt2 _7796 m x'').
Proof. exact (eq_refl (term303 A B lt2 _7796 m x'')). Qed.
Lemma lem361350 {A B : Type'} (lt2 : type1402 B) (x'' : A) (P : A -> Prop) (m : A -> B) (_7797 : A) (_7796 : B) : (term286 A B lt2 x'' m _7796 P _7797) = (term304 A B lt2 x'' P m _7797 _7796).
Proof. exact (MK_COMB (@lem361349 A B lt2 _7796 m x'') (@lem361341 A B P m _7797 _7796)). Qed.
Lemma lem361354 (q : Prop) (p : Prop) (r : Prop) : (term305 p q r) = (term305 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem361355 {A B : Type'} (P : A -> Prop) (lt2 : type1402 B) (x'' : A) (m : A -> B) (_7797 : A) (_7796 : B) : (term304 A B lt2 x'' P m _7797 _7796) = (term306 A B P lt2 x'' m _7797 _7796).
Proof. exact (@lem361354 (P _7797) (term307 A B lt2 _7796 m x'') (term302 A B m _7797 _7796)). Qed.
Lemma lem361373 {A B : Type'} (P : A -> Prop) (lt2 : type1402 B) (x'' : A) (m : A -> B) (_7797 : A) (_7796 : B) : (term286 A B lt2 x'' m _7796 P _7797) = (term306 A B P lt2 x'' m _7797 _7796).
Proof. exact (TRANS (@lem361350 A B lt2 x'' P m _7797 _7796) (@lem361355 A B P lt2 x'' m _7797 _7796)). Qed.
Lemma lem361374 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem361375 {A B : Type'} (P : A -> Prop) (lt2 : type1402 B) (x'' : A) (m : A -> B) (_7797 : A) (_7796 : B) : (term308 A B lt2 x'' m _7796 P _7797) = (term309 A B P lt2 x'' m _7797 _7796).
Proof. exact (MK_COMB (@lem361374) (@lem361373 A B P lt2 x'' m _7797 _7796)). Qed.
Lemma lem361393 {A B : Type'} (P : A -> Prop) (lt2 : type1402 B) (x'' : A) (m : A -> B) (_7797 : A) (_7796 : B) : (term306 A B P lt2 x'' m _7797 _7796) = (term306 A B P lt2 x'' m _7797 _7796).
Proof. exact (eq_refl (term306 A B P lt2 x'' m _7797 _7796)). Qed.
Lemma lem361394 {A B : Type'} (P : A -> Prop) (lt2 : type1402 B) (x'' : A) (m : A -> B) (_7797 : A) (_7796 : B) : ((term286 A B lt2 x'' m _7796 P _7797) = (term306 A B P lt2 x'' m _7797 _7796)) = ((term306 A B P lt2 x'' m _7797 _7796) = (term306 A B P lt2 x'' m _7797 _7796)).
Proof. exact (MK_COMB (@lem361375 A B P lt2 x'' m _7797 _7796) (@lem361393 A B P lt2 x'' m _7797 _7796)). Qed.
Lemma lem361396 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem361397 (x : Prop) : (x = x) = True.
Proof. exact (@lem361396 Prop x). Qed.
Lemma lem361398 {A B : Type'} (P : A -> Prop) (lt2 : type1402 B) (x'' : A) (m : A -> B) (_7797 : A) (_7796 : B) : ((term306 A B P lt2 x'' m _7797 _7796) = (term306 A B P lt2 x'' m _7797 _7796)) = True.
Proof. exact (@lem361397 (term306 A B P lt2 x'' m _7797 _7796)). Qed.
Lemma lem361399 {A B : Type'} (P : A -> Prop) (lt2 : type1402 B) (x'' : A) (m : A -> B) (_7797 : A) (_7796 : B) : ((term286 A B lt2 x'' m _7796 P _7797) = (term306 A B P lt2 x'' m _7797 _7796)) = True.
Proof. exact (TRANS (@lem361394 A B P lt2 x'' m _7797 _7796) (@lem361398 A B P lt2 x'' m _7797 _7796)). Qed.
Lemma lem361400 {A B : Type'} (P : A -> Prop) (lt2 : type1402 B) (x'' : A) (m : A -> B) (_7797 : A) (_7796 : B) : True = ((term286 A B lt2 x'' m _7796 P _7797) = (term306 A B P lt2 x'' m _7797 _7796)).
Proof. exact (SYM (@lem361399 A B P lt2 x'' m _7797 _7796)). Qed.
Lemma lem361401 {A B : Type'} (P : A -> Prop) (lt2 : type1402 B) (x'' : A) (m : A -> B) (_7797 : A) (_7796 : B) : (term286 A B lt2 x'' m _7796 P _7797) = (term306 A B P lt2 x'' m _7797 _7796).
Proof. exact (EQ_MP (@lem361400 A B P lt2 x'' m _7797 _7796) (@lem0)). Qed.
Lemma lem361402 {A B : Type'} (_7797 : A) (_7796 : B) (lt2 : type1402 B) (m : A -> B) (x' : B) (P : A -> Prop) (x'' : A) (h1 : term217 A B lt2 m x' P x'') : term306 A B P lt2 x'' m _7797 _7796.
Proof. exact (EQ_MP (@lem361401 A B P lt2 x'' m _7797 _7796) (@lem361196 A B _7796 _7797 lt2 m x' P x'' h1)). Qed.
Lemma lem361404 (b : Prop) (a : Prop) : (a \/ b) = (term293 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem361405 {A B : Type'} (lt2 : type1402 B) (x'' : A) (m : A -> B) (_7796 : B) (P : A -> Prop) (_7797 : A) : (term306 A B P lt2 x'' m _7797 _7796) = (term310 A B lt2 x'' m _7796 P _7797).
Proof. exact (@lem361404 (term311 A B lt2 x'' m _7797 _7796) (P _7797)). Qed.
Lemma lem361407 (a : Prop) (b : Prop) : (term312 a b) = (term313 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem361408 {A B : Type'} (lt2 : type1402 B) (x'' : A) (m : A -> B) (_7797 : A) (_7796 : B) : (term314 A B lt2 x'' m _7797 _7796) = (term315 A B lt2 x'' m _7797 _7796).
Proof. exact (@lem361407 (term307 A B lt2 _7796 m x'') (term302 A B m _7797 _7796)). Qed.
Lemma lem361410 (a : Prop) : (term90 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem361411 {A B : Type'} (lt2 : type1402 B) (_7796 : B) (m : A -> B) (x'' : A) : (term316 A B lt2 _7796 m x'') = (term317 A B lt2 _7796 m x'').
Proof. exact (@lem361410 (term317 A B lt2 _7796 m x'')). Qed.
Lemma lem361412 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem361413 {A B : Type'} (lt2 : type1402 B) (_7796 : B) (m : A -> B) (x'' : A) : (term318 A B lt2 _7796 m x'') = (term319 A B lt2 _7796 m x'').
Proof. exact (MK_COMB (@lem361412) (@lem361411 A B lt2 _7796 m x'')). Qed.
Lemma lem361415 (a : Prop) : (term90 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem361416 {A B : Type'} (m : A -> B) (_7797 : A) (_7796 : B) : (term320 A B m _7797 _7796) = ((m _7797) = _7796).
Proof. exact (@lem361415 ((m _7797) = _7796)). Qed.
Lemma lem361417 {A B : Type'} (lt2 : type1402 B) (x'' : A) (m : A -> B) (_7797 : A) (_7796 : B) : (term315 A B lt2 x'' m _7797 _7796) = (term321 A B lt2 x'' m _7797 _7796).
Proof. exact (MK_COMB (@lem361413 A B lt2 _7796 m x'') (@lem361416 A B m _7797 _7796)). Qed.
Lemma lem361418 {A B : Type'} (lt2 : type1402 B) (x'' : A) (m : A -> B) (_7797 : A) (_7796 : B) : (term314 A B lt2 x'' m _7797 _7796) = (term321 A B lt2 x'' m _7797 _7796).
Proof. exact (TRANS (@lem361408 A B lt2 x'' m _7797 _7796) (@lem361417 A B lt2 x'' m _7797 _7796)). Qed.
Lemma lem361419 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem361420 {A B : Type'} (lt2 : type1402 B) (x'' : A) (m : A -> B) (_7797 : A) (_7796 : B) : (term322 A B lt2 x'' m _7797 _7796) = (term323 A B lt2 x'' m _7797 _7796).
Proof. exact (MK_COMB (@lem361419) (@lem361418 A B lt2 x'' m _7797 _7796)). Qed.
Lemma lem361421 {A : Type'} (P : A -> Prop) (_7797 : A) : (P _7797) = (P _7797).
Proof. exact (eq_refl (P _7797)). Qed.
Lemma lem361422 {A B : Type'} (lt2 : type1402 B) (x'' : A) (m : A -> B) (_7796 : B) (P : A -> Prop) (_7797 : A) : (term310 A B lt2 x'' m _7796 P _7797) = (term324 A B lt2 x'' m _7796 P _7797).
Proof. exact (MK_COMB (@lem361420 A B lt2 x'' m _7797 _7796) (@lem361421 A P _7797)). Qed.
Lemma lem361423 {A B : Type'} (lt2 : type1402 B) (x'' : A) (m : A -> B) (_7796 : B) (P : A -> Prop) (_7797 : A) : (term306 A B P lt2 x'' m _7797 _7796) = (term324 A B lt2 x'' m _7796 P _7797).
Proof. exact (TRANS (@lem361405 A B lt2 x'' m _7796 P _7797) (@lem361422 A B lt2 x'' m _7796 P _7797)). Qed.
Lemma lem361425 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (y : A -> A) (P : A -> Prop) (x'' : A) (h1 : term168 A B lt2 m y P) (h2 : term110 A P x'') : term325 A B lt2 m y x''.
Proof. exact (conj (@lem361315 A B lt2 m y P x'' h1 h2) (@lem361324 A B m y x'')). Qed.
Lemma lem361427 {A B : Type'} (_7796 : B) (_7797 : A) (lt2 : type1402 B) (m : A -> B) (x' : B) (P : A -> Prop) (x'' : A) (h1 : term217 A B lt2 m x' P x'') : term324 A B lt2 x'' m _7796 P _7797.
Proof. exact (EQ_MP (@lem361423 A B lt2 x'' m _7796 P _7797) (@lem361402 A B _7797 _7796 lt2 m x' P x'' h1)). Qed.
Lemma lem361428 {A B : Type'} (_7796 : B) (_7797 : A) (lt2 : type1402 B) (m : A -> B) (x' : B) (P : A -> Prop) (x'' : A) (h1 : term217 A B lt2 m x' P x'') : term324 A B lt2 x'' m _7796 P _7797.
Proof. exact (@lem361427 A B _7796 _7797 lt2 m x' P x'' h1). Qed.
Lemma lem361429 {A B : Type'} (y : A -> A) (lt2 : type1402 B) (m : A -> B) (x' : B) (P : A -> Prop) (x'' : A) (h1 : term217 A B lt2 m x' P x'') : term326 A B lt2 m P y x''.
Proof. exact (@lem361428 A B (term298 A B m y x'') (y x'') lt2 m x' P x'' h1). Qed.
Lemma lem361432 {A B : Type'} (y : A -> A) (lt2 : type1402 B) (m : A -> B) (x' : B) (P : A -> Prop) (x'' : A) (h1 : term168 A B lt2 m y P) (h2 : term110 A P x'') (h3 : term217 A B lt2 m x' P x'') : term327 A P y x''.
Proof. exact (@lem361429 A B y lt2 m x' P x'' h3 (@lem361425 A B lt2 m y P x'' h1 h2)). Qed.
Lemma lem361433 {A B : Type'} (y : A -> A) (lt2 : type1402 B) (m : A -> B) (x' : B) (P : A -> Prop) (x'' : A) (h1 : term168 A B lt2 m y P) (h2 : term110 A P x'') (h3 : term217 A B lt2 m x' P x'') : term328 A P y x''.
Proof. exact (fun h0 : term259 A P y x'' => @lem361432 A B y lt2 m x' P x'' h1 h2 h3). Qed.
Lemma lem361435 (p : Prop) : (term297 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem361436 {A : Type'} (P : A -> Prop) (y : A -> A) (x'' : A) : (term328 A P y x'') = (term327 A P y x'').
Proof. exact (@lem361435 (term327 A P y x'')). Qed.
Lemma lem361437 {A B : Type'} (y : A -> A) (lt2 : type1402 B) (m : A -> B) (x' : B) (P : A -> Prop) (x'' : A) (h1 : term168 A B lt2 m y P) (h2 : term110 A P x'') (h3 : term217 A B lt2 m x' P x'') : term327 A P y x''.
Proof. exact (EQ_MP (@lem361436 A P y x'') (@lem361433 A B y lt2 m x' P x'' h1 h2 h3)). Qed.
Lemma lem361443 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem361444 {A : Type'} (P : A -> Prop) (y : A -> A) (_7795 : A) : (term290 A y P _7795) = (term329 A P y _7795).
Proof. exact (@lem361443 (P _7795) (term259 A P y _7795)). Qed.
Lemma lem361450 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem361451 {A : Type'} (P : A -> Prop) (y : A -> A) (_7795 : A) : (term330 A y P _7795) = (term331 A P y _7795).
Proof. exact (MK_COMB (@lem361450) (@lem361444 A P y _7795)). Qed.
Lemma lem361457 {A : Type'} (P : A -> Prop) (y : A -> A) (_7795 : A) : (term329 A P y _7795) = (term329 A P y _7795).
Proof. exact (eq_refl (term329 A P y _7795)). Qed.
Lemma lem361458 {A : Type'} (P : A -> Prop) (y : A -> A) (_7795 : A) : ((term290 A y P _7795) = (term329 A P y _7795)) = ((term329 A P y _7795) = (term329 A P y _7795)).
Proof. exact (MK_COMB (@lem361451 A P y _7795) (@lem361457 A P y _7795)). Qed.
Lemma lem361460 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem361461 (x : Prop) : (x = x) = True.
Proof. exact (@lem361460 Prop x). Qed.
Lemma lem361462 {A : Type'} (P : A -> Prop) (y : A -> A) (_7795 : A) : ((term329 A P y _7795) = (term329 A P y _7795)) = True.
Proof. exact (@lem361461 (term329 A P y _7795)). Qed.
Lemma lem361463 {A : Type'} (P : A -> Prop) (y : A -> A) (_7795 : A) : ((term290 A y P _7795) = (term329 A P y _7795)) = True.
Proof. exact (TRANS (@lem361458 A P y _7795) (@lem361462 A P y _7795)). Qed.
Lemma lem361464 {A : Type'} (P : A -> Prop) (y : A -> A) (_7795 : A) : True = ((term290 A y P _7795) = (term329 A P y _7795)).
Proof. exact (SYM (@lem361463 A P y _7795)). Qed.
Lemma lem361465 {A : Type'} (P : A -> Prop) (y : A -> A) (_7795 : A) : (term290 A y P _7795) = (term329 A P y _7795).
Proof. exact (EQ_MP (@lem361464 A P y _7795) (@lem0)). Qed.
Lemma lem361466 {A B : Type'} (_7795 : A) (lt2 : type1402 B) (m : A -> B) (y : A -> A) (P : A -> Prop) (h1 : term168 A B lt2 m y P) : term329 A P y _7795.
Proof. exact (EQ_MP (@lem361465 A P y _7795) (@lem361238 A B _7795 lt2 m y P h1)). Qed.
Lemma lem361468 (b : Prop) (a : Prop) : (a \/ b) = (term293 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem361469 {A : Type'} (y : A -> A) (P : A -> Prop) (_7795 : A) : (term329 A P y _7795) = (term332 A y P _7795).
Proof. exact (@lem361468 (term259 A P y _7795) (P _7795)). Qed.
Lemma lem361471 (a : Prop) : (term90 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem361472 {A : Type'} (P : A -> Prop) (y : A -> A) (_7795 : A) : (term333 A P y _7795) = (term327 A P y _7795).
Proof. exact (@lem361471 (term327 A P y _7795)). Qed.
Lemma lem361473 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem361474 {A : Type'} (P : A -> Prop) (y : A -> A) (_7795 : A) : (term334 A P y _7795) = (term335 A P y _7795).
Proof. exact (MK_COMB (@lem361473) (@lem361472 A P y _7795)). Qed.
Lemma lem361475 {A : Type'} (P : A -> Prop) (_7795 : A) : (P _7795) = (P _7795).
Proof. exact (eq_refl (P _7795)). Qed.
Lemma lem361476 {A : Type'} (y : A -> A) (P : A -> Prop) (_7795 : A) : (term332 A y P _7795) = (term336 A y P _7795).
Proof. exact (MK_COMB (@lem361474 A P y _7795) (@lem361475 A P _7795)). Qed.
Lemma lem361477 {A : Type'} (y : A -> A) (P : A -> Prop) (_7795 : A) : (term329 A P y _7795) = (term336 A y P _7795).
Proof. exact (TRANS (@lem361469 A y P _7795) (@lem361476 A y P _7795)). Qed.
Lemma lem361480 {A B : Type'} (_7795 : A) (lt2 : type1402 B) (m : A -> B) (y : A -> A) (P : A -> Prop) (h1 : term168 A B lt2 m y P) : term336 A y P _7795.
Proof. exact (EQ_MP (@lem361477 A y P _7795) (@lem361466 A B _7795 lt2 m y P h1)). Qed.
Lemma lem361481 {A B : Type'} (_7795 : A) (lt2 : type1402 B) (m : A -> B) (y : A -> A) (P : A -> Prop) (h1 : term168 A B lt2 m y P) : term336 A y P _7795.
Proof. exact (@lem361480 A B _7795 lt2 m y P h1). Qed.
Lemma lem361482 {A B : Type'} (x'' : A) (lt2 : type1402 B) (m : A -> B) (y : A -> A) (P : A -> Prop) (h1 : term168 A B lt2 m y P) : term336 A y P x''.
Proof. exact (@lem361481 A B x'' lt2 m y P h1). Qed.
Lemma lem361485 {A B : Type'} (y : A -> A) (lt2 : type1402 B) (m : A -> B) (x' : B) (P : A -> Prop) (x'' : A) (h1 : term168 A B lt2 m y P) (h2 : term110 A P x'') (h3 : term217 A B lt2 m x' P x'') : P x''.
Proof. exact (@lem361482 A B x'' lt2 m y P h1 (@lem361437 A B y lt2 m x' P x'' h1 h2 h3)). Qed.
Lemma lem361486 {A B : Type'} (y : A -> A) (lt2 : type1402 B) (m : A -> B) (x' : B) (P : A -> Prop) (x'' : A) (h1 : term168 A B lt2 m y P) (h2 : term217 A B lt2 m x' P x'') : term337 A P x''.
Proof. exact (fun h0 : term110 A P x'' => @lem361485 A B y lt2 m x' P x'' h1 h0 h2). Qed.
Lemma lem361488 (p : Prop) : (term297 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem361489 {A : Type'} (P : A -> Prop) (x'' : A) : (term337 A P x'') = (P x'').
Proof. exact (@lem361488 (P x'')). Qed.
Lemma lem361490 {A B : Type'} (y : A -> A) (lt2 : type1402 B) (m : A -> B) (x' : B) (P : A -> Prop) (x'' : A) (h1 : term168 A B lt2 m y P) (h2 : term217 A B lt2 m x' P x'') : P x''.
Proof. exact (EQ_MP (@lem361489 A P x'') (@lem361486 A B y lt2 m x' P x'' h1 h2)). Qed.
Lemma lem361493 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem361495 {A : Type'} (P : A -> Prop) (x'' : A) : (term110 A P x'') = (term338 A P x'').
Proof. exact (@lem361493 (P x'')). Qed.
Lemma lem361498 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (x' : B) (P : A -> Prop) (x'' : A) (h1 : term217 A B lt2 m x' P x'') : term338 A P x''.
Proof. exact (EQ_MP (@lem361495 A P x'') (@lem361210 A B lt2 m x' P x'' h1)). Qed.
Lemma lem361501 {A B : Type'} (y : A -> A) (lt2 : type1402 B) (m : A -> B) (x' : B) (P : A -> Prop) (x'' : A) (h1 : term168 A B lt2 m y P) (h2 : term217 A B lt2 m x' P x'') : False.
Proof. exact (@lem361498 A B lt2 m x' P x'' h2 (@lem361490 A B y lt2 m x' P x'' h1 h2)). Qed.
Lemma lem361502 {A B : Type'} (y : A -> A) (lt2 : type1402 B) (m : A -> B) (x' : B) (P : A -> Prop) (x'' : A) (h1 : term168 A B lt2 m y P) (h2 : term217 A B lt2 m x' P x'') : term339.
Proof. exact (fun h0 : ~ False => @lem361501 A B y lt2 m x' P x'' h1 h2). Qed.
Lemma lem361504 (p : Prop) : (term297 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem361505 : term339 = False.
Proof. exact (@lem361504 False). Qed.
Lemma lem361559 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem361560 {B : Type'} (x : B) : x = x.
Proof. exact (@lem361559 B x). Qed.
Lemma lem361561 {A B : Type'} (m : A -> B) (x : A) : (m x) = (m x).
Proof. exact (@lem361560 B (m x)). Qed.
Lemma lem361562 {A B : Type'} (m : A -> B) (x : A) : term340 A B m x.
Proof. exact (fun h0 : term341 A B m x => @lem361561 A B m x). Qed.
Lemma lem361564 (p : Prop) : (term297 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem361565 {A B : Type'} (m : A -> B) (x : A) : (term340 A B m x) = ((m x) = (m x)).
Proof. exact (@lem361564 ((m x) = (m x))). Qed.
Lemma lem361566 {A B : Type'} (m : A -> B) (x : A) : (m x) = (m x).
Proof. exact (EQ_MP (@lem361565 A B m x) (@lem361562 A B m x)). Qed.
Lemma lem361572 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem361573 {A B : Type'} (P : A -> Prop) (m : A -> B) (_7800 : A) (_7799 : B) : (term172 A B m _7799 P _7800) = (term301 A B P m _7800 _7799).
Proof. exact (@lem361572 (P _7800) (term302 A B m _7800 _7799)). Qed.
Lemma lem361581 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem361582 {A B : Type'} (P : A -> Prop) (m : A -> B) (_7800 : A) (_7799 : B) : (term342 A B m _7799 P _7800) = (term343 A B P m _7800 _7799).
Proof. exact (MK_COMB (@lem361581) (@lem361573 A B P m _7800 _7799)). Qed.
Lemma lem361590 {A B : Type'} (P : A -> Prop) (m : A -> B) (_7800 : A) (_7799 : B) : (term301 A B P m _7800 _7799) = (term301 A B P m _7800 _7799).
Proof. exact (eq_refl (term301 A B P m _7800 _7799)). Qed.
Lemma lem361591 {A B : Type'} (P : A -> Prop) (m : A -> B) (_7800 : A) (_7799 : B) : ((term172 A B m _7799 P _7800) = (term301 A B P m _7800 _7799)) = ((term301 A B P m _7800 _7799) = (term301 A B P m _7800 _7799)).
Proof. exact (MK_COMB (@lem361582 A B P m _7800 _7799) (@lem361590 A B P m _7800 _7799)). Qed.
Lemma lem361593 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem361594 (x : Prop) : (x = x) = True.
Proof. exact (@lem361593 Prop x). Qed.
Lemma lem361595 {A B : Type'} (P : A -> Prop) (m : A -> B) (_7800 : A) (_7799 : B) : ((term301 A B P m _7800 _7799) = (term301 A B P m _7800 _7799)) = True.
Proof. exact (@lem361594 (term301 A B P m _7800 _7799)). Qed.
Lemma lem361596 {A B : Type'} (P : A -> Prop) (m : A -> B) (_7800 : A) (_7799 : B) : ((term172 A B m _7799 P _7800) = (term301 A B P m _7800 _7799)) = True.
Proof. exact (TRANS (@lem361591 A B P m _7800 _7799) (@lem361595 A B P m _7800 _7799)). Qed.
Lemma lem361597 {A B : Type'} (P : A -> Prop) (m : A -> B) (_7800 : A) (_7799 : B) : True = ((term172 A B m _7799 P _7800) = (term301 A B P m _7800 _7799)).
Proof. exact (SYM (@lem361596 A B P m _7800 _7799)). Qed.
Lemma lem361598 {A B : Type'} (P : A -> Prop) (m : A -> B) (_7800 : A) (_7799 : B) : (term172 A B m _7799 P _7800) = (term301 A B P m _7800 _7799).
Proof. exact (EQ_MP (@lem361597 A B P m _7800 _7799) (@lem0)). Qed.
Lemma lem361599 {A B : Type'} (_7800 : A) (_7799 : B) (m : A -> B) (P : A -> Prop) (h1 : term202 A B m P) : term301 A B P m _7800 _7799.
Proof. exact (EQ_MP (@lem361598 A B P m _7800 _7799) (@lem361142 A B _7799 _7800 m P h1)). Qed.
Lemma lem361601 (b : Prop) (a : Prop) : (a \/ b) = (term293 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem361602 {A B : Type'} (m : A -> B) (_7799 : B) (P : A -> Prop) (_7800 : A) : (term301 A B P m _7800 _7799) = (term344 A B m _7799 P _7800).
Proof. exact (@lem361601 (term302 A B m _7800 _7799) (P _7800)). Qed.
Lemma lem361604 (a : Prop) : (term90 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem361605 {A B : Type'} (m : A -> B) (_7800 : A) (_7799 : B) : (term320 A B m _7800 _7799) = ((m _7800) = _7799).
Proof. exact (@lem361604 ((m _7800) = _7799)). Qed.
Lemma lem361606 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem361607 {A B : Type'} (m : A -> B) (_7800 : A) (_7799 : B) : (term345 A B m _7800 _7799) = (term346 A B m _7800 _7799).
Proof. exact (MK_COMB (@lem361606) (@lem361605 A B m _7800 _7799)). Qed.
Lemma lem361608 {A : Type'} (P : A -> Prop) (_7800 : A) : (P _7800) = (P _7800).
Proof. exact (eq_refl (P _7800)). Qed.
Lemma lem361609 {A B : Type'} (m : A -> B) (_7799 : B) (P : A -> Prop) (_7800 : A) : (term344 A B m _7799 P _7800) = (term107 A B m _7799 P _7800).
Proof. exact (MK_COMB (@lem361607 A B m _7800 _7799) (@lem361608 A P _7800)). Qed.
Lemma lem361610 {A B : Type'} (m : A -> B) (_7799 : B) (P : A -> Prop) (_7800 : A) : (term301 A B P m _7800 _7799) = (term107 A B m _7799 P _7800).
Proof. exact (TRANS (@lem361602 A B m _7799 P _7800) (@lem361609 A B m _7799 P _7800)). Qed.
Lemma lem361613 {A B : Type'} (_7799 : B) (_7800 : A) (m : A -> B) (P : A -> Prop) (h1 : term202 A B m P) : term107 A B m _7799 P _7800.
Proof. exact (EQ_MP (@lem361610 A B m _7799 P _7800) (@lem361599 A B _7800 _7799 m P h1)). Qed.
Lemma lem361614 {A B : Type'} (_7799 : B) (_7800 : A) (m : A -> B) (P : A -> Prop) (h1 : term202 A B m P) : term107 A B m _7799 P _7800.
Proof. exact (@lem361613 A B _7799 _7800 m P h1). Qed.
Lemma lem361615 {A B : Type'} (x : A) (m : A -> B) (P : A -> Prop) (h1 : term202 A B m P) : term347 A B m P x.
Proof. exact (@lem361614 A B (m x) x m P h1). Qed.
Lemma lem361618 {A B : Type'} (x : A) (m : A -> B) (P : A -> Prop) (h1 : term202 A B m P) : P x.
Proof. exact (@lem361615 A B x m P h1 (@lem361566 A B m x)). Qed.
Lemma lem361619 {A B : Type'} (x : A) (m : A -> B) (P : A -> Prop) (h1 : term202 A B m P) : P x.
Proof. exact (@lem361618 A B x m P h1). Qed.
Lemma lem361620 {A B : Type'} (x : A) (m : A -> B) (P : A -> Prop) (h1 : term202 A B m P) : term337 A P x.
Proof. exact (fun h0 : term110 A P x => @lem361619 A B x m P h1). Qed.
Lemma lem361622 (p : Prop) : (term297 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem361623 {A : Type'} (P : A -> Prop) (x : A) : (term337 A P x) = (P x).
Proof. exact (@lem361622 (P x)). Qed.
Lemma lem361624 {A B : Type'} (x : A) (m : A -> B) (P : A -> Prop) (h1 : term202 A B m P) : P x.
Proof. exact (EQ_MP (@lem361623 A P x) (@lem361620 A B x m P h1)). Qed.
Lemma lem361627 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem361629 {A : Type'} (P : A -> Prop) (x : A) : (term110 A P x) = (term338 A P x).
Proof. exact (@lem361627 (P x)). Qed.
Lemma lem361632 {A : Type'} (P : A -> Prop) (x : A) (h1 : term110 A P x) : term338 A P x.
Proof. exact (EQ_MP (@lem361629 A P x) (@lem361136 A P x h1)). Qed.
Lemma lem361635 {A B : Type'} (m : A -> B) (P : A -> Prop) (x : A) (h1 : term202 A B m P) (h2 : term110 A P x) : False.
Proof. exact (@lem361632 A P x h2 (@lem361624 A B x m P h1)). Qed.
Lemma lem361636 {A B : Type'} (m : A -> B) (P : A -> Prop) (x : A) (h1 : term202 A B m P) (h2 : term110 A P x) : term339.
Proof. exact (fun h0 : ~ False => @lem361635 A B m P x h1 h2). Qed.
Lemma lem361638 (p : Prop) : (term297 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem361639 : term339 = False.
Proof. exact (@lem361638 False). Qed.
Lemma lem361640 {A B : Type'} (m : A -> B) (P : A -> Prop) (x : A) (h1 : term202 A B m P) (h2 : term110 A P x) : False.
Proof. exact (EQ_MP (@lem361639) (@lem361636 A B m P x h1 h2)). Qed.
Lemma lem361641 {A B : Type'} (y : A -> A) (lt2 : type1402 B) (m : A -> B) (x' : B) (P : A -> Prop) (x'' : A) (h1 : term168 A B lt2 m y P) (h2 : term217 A B lt2 m x' P x'') : False.
Proof. exact (EQ_MP (@lem361505) (@lem361502 A B y lt2 m x' P x'' h1 h2)). Qed.
Lemma lem361642 {A B : Type'} (m : A -> B) (P : A -> Prop) (x : A) (h1 : term202 A B m P) (h2 : term110 A P x) : (term110 A P x) = False.
Proof. exact (prop_ext (fun h3 : term110 A P x => @lem361640 A B m P x h1 h2) (fun h3 : False => @lem361136 A P x h2)). Qed.
Lemma lem361643 {A B : Type'} (m : A -> B) (P : A -> Prop) (x : A) (h1 : term202 A B m P) (h2 : term110 A P x) : False.
Proof. exact (EQ_MP (@lem361642 A B m P x h1 h2) (@lem361136 A P x h2)). Qed.
Lemma lem361644 {A B : Type'} (m : A -> B) (P : A -> Prop) (x : A) (h1 : term202 A B m P) (h2 : term110 A P x) : (term110 A P x) = False.
Proof. exact (prop_ext (fun h3 : term110 A P x => @lem361643 A B m P x h1 h2) (fun h3 : False => @lem361045 A P x h2)). Qed.
Lemma lem361645 {A B : Type'} (m : A -> B) (P : A -> Prop) (x : A) (h1 : term202 A B m P) (h2 : term110 A P x) : False.
Proof. exact (EQ_MP (@lem361644 A B m P x h1 h2) (@lem361045 A P x h2)). Qed.
Lemma lem361646 {A B : Type'} (m : A -> B) (P : A -> Prop) (x : A) (h1 : term202 A B m P) (h2 : term110 A P x) : (term202 A B m P) = False.
Proof. exact (prop_ext (fun h3 : term202 A B m P => @lem361645 A B m P x h1 h2) (fun h3 : False => @lem361084 A B m P h1)). Qed.
Lemma lem361647 {A B : Type'} (m : A -> B) (P : A -> Prop) (x : A) (h1 : term202 A B m P) (h2 : term110 A P x) : False.
Proof. exact (EQ_MP (@lem361646 A B m P x h1 h2) (@lem361084 A B m P h1)). Qed.
Lemma lem361648 {A B : Type'} (m : A -> B) (P : A -> Prop) (x : A) (h1 : term202 A B m P) (h2 : term110 A P x) : (term110 A P x) = False.
Proof. exact (prop_ext (fun h3 : term110 A P x => @lem361647 A B m P x h1 h2) (fun h3 : False => @lem361045 A P x h2)). Qed.
Lemma lem361649 {A B : Type'} (m : A -> B) (P : A -> Prop) (x : A) (h1 : term202 A B m P) (h2 : term110 A P x) : False.
Proof. exact (EQ_MP (@lem361648 A B m P x h1 h2) (@lem361045 A P x h2)). Qed.
Lemma lem361650 {A B : Type'} (y : A -> A) (x : A) (lt2 : type1402 B) (x' : B) (x'' : A) (m : A -> B) (P : A -> Prop) (h1 : term168 A B lt2 m y P) (h2 : term110 A P x) (h3 : term251 A B lt2 x' x'' m P) : False.
Proof. exact (or_elim (@lem360925 A B lt2 x' x'' m P h3) (fun h0 : term217 A B lt2 m x' P x'' => @lem361641 A B y lt2 m x' P x'' h1 h0) (fun h0 : term202 A B m P => @lem361649 A B m P x h0 h2)). Qed.
Lemma lem361651 {A B : Type'} (y : A -> A) (x : A) (lt2 : type1402 B) (x' : B) (x'' : A) (m : A -> B) (P : A -> Prop) (h1 : term168 A B lt2 m y P) (h2 : term110 A P x) (h3 : term251 A B lt2 x' x'' m P) : (term168 A B lt2 m y P) = False.
Proof. exact (prop_ext (fun h4 : term168 A B lt2 m y P => @lem361650 A B y x lt2 x' x'' m P h1 h2 h3) (fun h4 : False => @lem360956 A B lt2 m y P h1)). Qed.
Lemma lem361652 {A B : Type'} (y : A -> A) (x : A) (lt2 : type1402 B) (x' : B) (x'' : A) (m : A -> B) (P : A -> Prop) (h1 : term168 A B lt2 m y P) (h2 : term110 A P x) (h3 : term251 A B lt2 x' x'' m P) : False.
Proof. exact (EQ_MP (@lem361651 A B y x lt2 x' x'' m P h1 h2 h3) (@lem360956 A B lt2 m y P h1)). Qed.
Lemma lem361653 {A B : Type'} (y : A -> A) (x : A) (lt2 : type1402 B) (x' : B) (x'' : A) (m : A -> B) (P : A -> Prop) (h1 : term168 A B lt2 m y P) (h2 : term110 A P x) (h3 : term251 A B lt2 x' x'' m P) : (term251 A B lt2 x' x'' m P) = False.
Proof. exact (prop_ext (fun h4 : term251 A B lt2 x' x'' m P => @lem361652 A B y x lt2 x' x'' m P h1 h2 h3) (fun h4 : False => @lem360925 A B lt2 x' x'' m P h3)). Qed.
Lemma lem361654 {A B : Type'} (y : A -> A) (x : A) (lt2 : type1402 B) (x' : B) (x'' : A) (m : A -> B) (P : A -> Prop) (h1 : term168 A B lt2 m y P) (h2 : term110 A P x) (h3 : term251 A B lt2 x' x'' m P) : False.
Proof. exact (EQ_MP (@lem361653 A B y x lt2 x' x'' m P h1 h2 h3) (@lem360925 A B lt2 x' x'' m P h3)). Qed.
Lemma lem361655 {A B : Type'} (y : A -> A) (x : A) (lt2 : type1402 B) (x' : B) (x'' : A) (m : A -> B) (P : A -> Prop) (h1 : term168 A B lt2 m y P) (h2 : term110 A P x) (h3 : term251 A B lt2 x' x'' m P) : (term110 A P x) = False.
Proof. exact (prop_ext (fun h4 : term110 A P x => @lem361654 A B y x lt2 x' x'' m P h1 h2 h3) (fun h4 : False => @lem360851 A P x h2)). Qed.
Lemma lem361656 {A B : Type'} (y : A -> A) (x : A) (lt2 : type1402 B) (x' : B) (x'' : A) (m : A -> B) (P : A -> Prop) (h1 : term168 A B lt2 m y P) (h2 : term110 A P x) (h3 : term251 A B lt2 x' x'' m P) : False.
Proof. exact (EQ_MP (@lem361655 A B y x lt2 x' x'' m P h1 h2 h3) (@lem360851 A P x h2)). Qed.
Lemma lem361657 {A B : Type'} (x : A) (lt2 : type1402 B) (x' : B) (x'' : A) (m : A -> B) (P : A -> Prop) (h1 : term37 A B lt2 m P) (h2 : term110 A P x) (h3 : term251 A B lt2 x' x'' m P) : False.
Proof. exact (ex_elim (@lem360471 A B lt2 m P h1) (fun y : A -> A => fun h0 : term170 A B lt2 m P y => @lem361656 A B y x lt2 x' x'' m P h0 h2 h3)). Qed.
Lemma lem361658 {A B : Type'} (lt2 : type1402 B) (x' : B) (m : A -> B) (P : A -> Prop) (x : A) (h1 : term37 A B lt2 m P) (h2 : term254 A B lt2 x' m P) (h3 : term110 A P x) : False.
Proof. exact (ex_elim (@lem360843 A B lt2 x' m P h2) (fun x'' : A => fun h0 : term253 A B lt2 x' m P x'' => @lem361657 A B x lt2 x' x'' m P h1 h3 h0)). Qed.
Lemma lem361659 {A B : Type'} (x : A) (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (h1 : term37 A B lt2 m P) (h2 : term110 A P x) (h3 : term76 A B lt2 m P) : False.
Proof. exact (ex_elim (@lem360836 A B lt2 m P h3) (fun x' : B => fun h0 : term255 A B lt2 m P x' => @lem361658 A B lt2 x' m P x h1 h0 h2)). Qed.
Lemma lem361660 {A B : Type'} (x : A) (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (h1 : term37 A B lt2 m P) (h2 : term110 A P x) (h3 : term76 A B lt2 m P) : (term110 A P x) = False.
Proof. exact (prop_ext (fun h4 : term110 A P x => @lem361659 A B x lt2 m P h1 h2 h3) (fun h4 : False => @lem360842 A P x h2)). Qed.
Lemma lem361661 {A B : Type'} (x : A) (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (h1 : term37 A B lt2 m P) (h2 : term110 A P x) (h3 : term76 A B lt2 m P) : False.
Proof. exact (EQ_MP (@lem361660 A B x lt2 m P h1 h2 h3) (@lem360842 A P x h2)). Qed.
Lemma lem361662 {A B : Type'} (x : A) (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (h1 : term37 A B lt2 m P) (h2 : term110 A P x) (h3 : term76 A B lt2 m P) : (term110 A P x) = False.
Proof. exact (prop_ext (fun h4 : term110 A P x => @lem361661 A B x lt2 m P h1 h2 h3) (fun h4 : False => @lem360303 A P x h2)). Qed.
Lemma lem361663 {A B : Type'} (x : A) (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (h1 : term37 A B lt2 m P) (h2 : term110 A P x) (h3 : term76 A B lt2 m P) : False.
Proof. exact (EQ_MP (@lem361662 A B x lt2 m P h1 h2 h3) (@lem360303 A P x h2)). Qed.
Lemma lem361664 {A B : Type'} (x : A) (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (h1 : term37 A B lt2 m P) (h2 : term76 A B lt2 m P) : term109 A P x.
Proof. exact (fun h0 : term110 A P x => @lem361663 A B x lt2 m P h1 h0 h2). Qed.
Lemma lem361665 {A B : Type'} (x : A) (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (h1 : term37 A B lt2 m P) (h2 : term76 A B lt2 m P) : P x.
Proof. exact (EQ_MP (@lem360302 A P x) (@lem361664 A B x lt2 m P h1 h2)). Qed.
Lemma lem361666 {A B : Type'} (x : A) (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (h1 : term37 A B lt2 m P) : term80 A B lt2 m P x.
Proof. exact (fun h0 : term76 A B lt2 m P => @lem361665 A B x lt2 m P h1 h0). Qed.
Lemma lem361667 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (x : A) : term82 A B lt2 m P x.
Proof. exact (fun h0 : term37 A B lt2 m P => @lem361666 A B x lt2 m P h0). Qed.
Lemma lem361672 {A B : Type'} (m : A -> B) (P : A -> Prop) (x : A) : term94 A B m P x.
Proof. exact (fun lt2 : type1402 B => @lem361667 A B lt2 m P x). Qed.
Lemma lem361677 {A B : Type'} (P : A -> Prop) (x : A) : term98 A B P x.
Proof. exact (fun m : A -> B => @lem361672 A B m P x). Qed.
Lemma lem361682 {A B : Type'} (x : A) : term102 A B x.
Proof. exact (fun P : A -> Prop => @lem361677 A B P x). Qed.
Lemma lem361687 {A B : Type'} : term106 A B.
Proof. exact (fun x : A => @lem361682 A B x). Qed.
Lemma lem361688 {A B : Type'} : term105 A B.
Proof. exact (EQ_MP (@lem360296 A B) (@lem361687 A B)). Qed.
Lemma lem361689 {A B : Type'} (x : A) : term348 A B x.
Proof. exact (@lem361688 A B x). Qed.
Lemma lem361690 {A B : Type'} (x : A) : (term348 A B x) = (term101 A B x).
Proof. exact (eq_refl (term348 A B x)). Qed.
Lemma lem361691 {A B : Type'} (x : A) : term101 A B x.
Proof. exact (EQ_MP (@lem361690 A B x) (@lem361689 A B x)). Qed.
Lemma lem361692 {A B : Type'} (x : A) (P : A -> Prop) : term349 A B x P.
Proof. exact (@lem361691 A B x P). Qed.
Lemma lem361693 {A B : Type'} (P : A -> Prop) (x : A) : (term349 A B x P) = (term97 A B P x).
Proof. exact (eq_refl (term349 A B x P)). Qed.
Lemma lem361694 {A B : Type'} (P : A -> Prop) (x : A) : term97 A B P x.
Proof. exact (EQ_MP (@lem361693 A B P x) (@lem361692 A B x P)). Qed.
Lemma lem361695 {A B : Type'} (P : A -> Prop) (x : A) (m : A -> B) : term350 A B P x m.
Proof. exact (@lem361694 A B P x m). Qed.
Lemma lem361696 {A B : Type'} (m : A -> B) (P : A -> Prop) (x : A) : (term350 A B P x m) = (term93 A B m P x).
Proof. exact (eq_refl (term350 A B P x m)). Qed.
Lemma lem361697 {A B : Type'} (m : A -> B) (P : A -> Prop) (x : A) : term93 A B m P x.
Proof. exact (EQ_MP (@lem361696 A B m P x) (@lem361695 A B P x m)). Qed.
Lemma lem361698 {A B : Type'} (m : A -> B) (P : A -> Prop) (x : A) (lt2 : type1402 B) : term351 A B m P x lt2.
Proof. exact (@lem361697 A B m P x lt2). Qed.
Lemma lem361699 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (x : A) : (term351 A B m P x lt2) = (term84 A B lt2 m P x).
Proof. exact (eq_refl (term351 A B m P x lt2)). Qed.
Lemma lem361700 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (x : A) : term84 A B lt2 m P x.
Proof. exact (EQ_MP (@lem361699 A B lt2 m P x) (@lem361698 A B m P x lt2)). Qed.
Lemma lem361702 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (x : A) : term84 A B lt2 m P x.
Proof. exact (@lem360016 A B lt2 m P x (@lem361700 A B lt2 m P x)). Qed.
Lemma lem361703 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (x : A) (h1 : term85 A B lt2 m P x) : False.
Proof. exact (@lem361702 A B lt2 m P x (@lem360000 A B lt2 m P x h1)). Qed.
Lemma lem361704 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (x : A) (h1 : term85 A B lt2 m P x) : (term85 A B lt2 m P x) = False.
Proof. exact (prop_ext (fun h2 : term85 A B lt2 m P x => @lem361703 A B lt2 m P x h1) (fun h2 : False => @lem360000 A B lt2 m P x h1)). Qed.
Lemma lem361705 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (x : A) (h1 : term85 A B lt2 m P x) : False.
Proof. exact (EQ_MP (@lem361704 A B lt2 m P x h1) (@lem360000 A B lt2 m P x h1)). Qed.
Lemma lem361706 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (x : A) : term84 A B lt2 m P x.
Proof. exact (fun h0 : term85 A B lt2 m P x => @lem361705 A B lt2 m P x h0). Qed.
Lemma lem361707 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (x : A) : term82 A B lt2 m P x.
Proof. exact (EQ_MP (@lem359999 A B lt2 m P x) (@lem361706 A B lt2 m P x)). Qed.
Lemma lem361708 {A B : Type'} (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (x : A) : term81 A B lt2 m P x.
Proof. exact (EQ_MP (@lem359995 A B lt2 m P x) (@lem361707 A B lt2 m P x)). Qed.
Lemma lem361709 {A B : Type'} (x : A) (lt2 : type1402 B) (m : A -> B) (P : A -> Prop) (h1 : term37 A B lt2 m P) : term79 A B lt2 m P x.
Proof. exact (@lem361708 A B lt2 m P x (@lem359843 A B lt2 m P h1)). Qed.
Lemma lem361710 {A B : Type'} (x : A) (m : A -> B) (P : A -> Prop) (lt2 : type1402 B) (h1 : term37 A B lt2 m P) (h2 : term0 B lt2) : P x.
Proof. exact (@lem361709 A B x lt2 m P h1 (@lem359846 A B m P lt2 h2)). Qed.
Lemma lem361715 {A B : Type'} (m : A -> B) (P : A -> Prop) (lt2 : type1402 B) (h1 : term37 A B lt2 m P) (h2 : term0 B lt2) : term40 A P.
Proof. exact (fun x : A => @lem361710 A B x m P lt2 h1 h2). Qed.
Lemma lem361716 {A B : Type'} (m : A -> B) (P : A -> Prop) (lt2 : type1402 B) (h1 : term37 A B lt2 m P) (h2 : term0 B lt2) : (term37 A B lt2 m P) = (term40 A P).
Proof. exact (prop_ext (fun h3 : term37 A B lt2 m P => @lem361715 A B m P lt2 h1 h2) (fun h3 : term40 A P => @lem359843 A B lt2 m P h1)). Qed.
Lemma lem361717 {A B : Type'} (m : A -> B) (P : A -> Prop) (lt2 : type1402 B) (h1 : term37 A B lt2 m P) (h2 : term0 B lt2) : term40 A P.
Proof. exact (EQ_MP (@lem361716 A B m P lt2 h1 h2) (@lem359843 A B lt2 m P h1)). Qed.
Lemma lem361718 {A B : Type'} (m : A -> B) (P : A -> Prop) (lt2 : type1402 B) (h1 : term0 B lt2) : term42 A B lt2 m P.
Proof. exact (fun h0 : term37 A B lt2 m P => @lem361717 A B m P lt2 h0 h1). Qed.
Lemma lem361723 {A B : Type'} (m : A -> B) (lt2 : type1402 B) (h1 : term0 B lt2) : term45 A B lt2 m.
Proof. exact (fun P : A -> Prop => @lem361718 A B m P lt2 h1). Qed.
Lemma lem361724 {A B : Type'} (m : A -> B) (lt2 : type1402 B) (h1 : term0 B lt2) : (term0 B lt2) = (term45 A B lt2 m).
Proof. exact (prop_ext (fun h2 : term0 B lt2 => @lem361723 A B m lt2 h1) (fun h2 : term45 A B lt2 m => @lem359842 B lt2 h1)). Qed.
Lemma lem361725 {A B : Type'} (m : A -> B) (lt2 : type1402 B) (h1 : term0 B lt2) : term45 A B lt2 m.
Proof. exact (EQ_MP (@lem361724 A B m lt2 h1) (@lem359842 B lt2 h1)). Qed.
Lemma lem361726 {A B : Type'} (lt2 : type1402 B) (m : A -> B) : term47 A B lt2 m.
Proof. exact (fun h0 : term0 B lt2 => @lem361725 A B m lt2 h0). Qed.
Lemma lem361727 {A B : Type'} (lt2 : type1402 B) (m : A -> B) : term46 A B lt2 m.
Proof. exact (EQ_MP (@lem359841 A B lt2 m) (@lem361726 A B lt2 m)). Qed.
Lemma lem361732 {A B : Type'} (lt2 : type1402 B) : term352 A B lt2.
Proof. exact (fun m : A -> B => @lem361727 A B lt2 m). Qed.
Lemma lem361737 {A B : Type'} : term353 A B.
Proof. exact (fun lt2 : type1402 B => @lem361732 A B lt2). Qed.
