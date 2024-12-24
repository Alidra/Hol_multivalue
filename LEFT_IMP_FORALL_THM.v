Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LEFT_IMP_FORALL_THM_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import LEFT_AND_FORALL_THM_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_EXISTS_THM_spec.
Require Import NOT_IMP_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem11767 {A : Type'} (P : A -> Prop) : term0 A P.
Proof. exact (@lem5247 A P). Qed.
Lemma lem11768 {A : Type'} (P : A -> Prop) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem11769 {A : Type'} (P : A -> Prop) : term1 A P.
Proof. exact (EQ_MP (@lem11768 A P) (@lem11767 A P)). Qed.
Lemma lem11770 {A : Type'} (P : A -> Prop) (Q : Prop) : term2 A P Q.
Proof. exact (@lem11769 A P Q). Qed.
Lemma lem11771 {A : Type'} (P : A -> Prop) (Q : Prop) : (term2 A P Q) = ((term3 A P Q) = (term4 A P Q)).
Proof. exact (eq_refl (term2 A P Q)). Qed.
Lemma lem11773 (t1 : Prop) : term5 t1.
Proof. exact (@lem10299 t1). Qed.
Lemma lem11774 (t1 : Prop) : (term5 t1) = (term6 t1).
Proof. exact (eq_refl (term5 t1)). Qed.
Lemma lem11775 (t1 : Prop) : term6 t1.
Proof. exact (EQ_MP (@lem11774 t1) (@lem11773 t1)). Qed.
Lemma lem11776 (t1 : Prop) (t2 : Prop) : term7 t1 t2.
Proof. exact (@lem11775 t1 t2). Qed.
Lemma lem11777 (t1 : Prop) (t2 : Prop) : (term7 t1 t2) = ((term8 t1 t2) = (term9 t1 t2)).
Proof. exact (eq_refl (term7 t1 t2)). Qed.
Lemma lem11779 {A : Type'} (P : A -> Prop) : term10 A P.
Proof. exact (@lem10660 A P). Qed.
Lemma lem11780 {A : Type'} (P : A -> Prop) : (term10 A P) = ((term11 A P) = (term12 A P)).
Proof. exact (eq_refl (term10 A P)). Qed.
Lemma lem11790 (a : Prop) : term13 a.
Proof. exact (@lem9851 a). Qed.
Lemma lem11791 (a : Prop) : (term13 a) = (term14 a).
Proof. exact (eq_refl (term13 a)). Qed.
Lemma lem11792 (a : Prop) : term14 a.
Proof. exact (EQ_MP (@lem11791 a) (@lem11790 a)). Qed.
Lemma lem11793 (a : Prop) (h1 : a = True) : a = True.
Proof. exact (h1). Qed.
Lemma lem11794 (a : Prop) (h1 : a = False) : a = False.
Proof. exact (h1). Qed.
Lemma lem11803 (b : Prop) : (term15 b) = (term15 b).
Proof. exact (eq_refl (term15 b)). Qed.
Lemma lem11804 (b : Prop) (a : Prop) (h1 : a = True) : (term16 b a) = (term17 b).
Proof. exact (MK_COMB (@lem11803 b) (@lem11793 a h1)). Qed.
Lemma lem11805 (b : Prop) : (term17 b) = ((True = b) = ((~ True) = (~ b))).
Proof. exact (eq_refl (term17 b)). Qed.
Lemma lem11806 (b : Prop) (a : Prop) : (term18 b a) = (term18 b a).
Proof. exact (eq_refl (term18 b a)). Qed.
Lemma lem11807 (a : Prop) (b : Prop) : ((term16 b a) = (term17 b)) = ((term16 b a) = ((True = b) = ((~ True) = (~ b)))).
Proof. exact (MK_COMB (@lem11806 b a) (@lem11805 b)). Qed.
Lemma lem11808 (a : Prop) (b : Prop) : (term16 b a) = ((a = b) = ((~ a) = (~ b))).
Proof. exact (eq_refl (term16 b a)). Qed.
Lemma lem11809 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem11810 (a : Prop) (b : Prop) : (term18 b a) = (term19 a b).
Proof. exact (MK_COMB (@lem11809) (@lem11808 a b)). Qed.
Lemma lem11811 (b : Prop) : ((True = b) = ((~ True) = (~ b))) = ((True = b) = ((~ True) = (~ b))).
Proof. exact (eq_refl ((True = b) = ((~ True) = (~ b)))). Qed.
Lemma lem11812 (a : Prop) (b : Prop) : ((term16 b a) = ((True = b) = ((~ True) = (~ b)))) = (((a = b) = ((~ a) = (~ b))) = ((True = b) = ((~ True) = (~ b)))).
Proof. exact (MK_COMB (@lem11810 a b) (@lem11811 b)). Qed.
Lemma lem11813 (a : Prop) (b : Prop) : ((term16 b a) = (term17 b)) = (((a = b) = ((~ a) = (~ b))) = ((True = b) = ((~ True) = (~ b)))).
Proof. exact (TRANS (@lem11807 a b) (@lem11812 a b)). Qed.
Lemma lem11814 (b : Prop) (a : Prop) (h1 : a = True) : ((a = b) = ((~ a) = (~ b))) = ((True = b) = ((~ True) = (~ b))).
Proof. exact (EQ_MP (@lem11813 a b) (@lem11804 b a h1)). Qed.
Lemma lem11815 (b : Prop) (a : Prop) (h1 : a = True) : ((True = b) = ((~ True) = (~ b))) = ((a = b) = ((~ a) = (~ b))).
Proof. exact (SYM (@lem11814 b a h1)). Qed.
Lemma lem11816 (b : Prop) : (term15 b) = (term15 b).
Proof. exact (eq_refl (term15 b)). Qed.
Lemma lem11817 (b : Prop) (a : Prop) (h1 : a = False) : (term16 b a) = (term20 b).
Proof. exact (MK_COMB (@lem11816 b) (@lem11794 a h1)). Qed.
Lemma lem11818 (b : Prop) : (term20 b) = ((False = b) = ((~ False) = (~ b))).
Proof. exact (eq_refl (term20 b)). Qed.
Lemma lem11819 (b : Prop) (a : Prop) : (term18 b a) = (term18 b a).
Proof. exact (eq_refl (term18 b a)). Qed.
Lemma lem11820 (a : Prop) (b : Prop) : ((term16 b a) = (term20 b)) = ((term16 b a) = ((False = b) = ((~ False) = (~ b)))).
Proof. exact (MK_COMB (@lem11819 b a) (@lem11818 b)). Qed.
Lemma lem11821 (a : Prop) (b : Prop) : (term16 b a) = ((a = b) = ((~ a) = (~ b))).
Proof. exact (eq_refl (term16 b a)). Qed.
Lemma lem11822 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem11823 (a : Prop) (b : Prop) : (term18 b a) = (term19 a b).
Proof. exact (MK_COMB (@lem11822) (@lem11821 a b)). Qed.
Lemma lem11824 (b : Prop) : ((False = b) = ((~ False) = (~ b))) = ((False = b) = ((~ False) = (~ b))).
Proof. exact (eq_refl ((False = b) = ((~ False) = (~ b)))). Qed.
Lemma lem11825 (a : Prop) (b : Prop) : ((term16 b a) = ((False = b) = ((~ False) = (~ b)))) = (((a = b) = ((~ a) = (~ b))) = ((False = b) = ((~ False) = (~ b)))).
Proof. exact (MK_COMB (@lem11823 a b) (@lem11824 b)). Qed.
Lemma lem11826 (a : Prop) (b : Prop) : ((term16 b a) = (term20 b)) = (((a = b) = ((~ a) = (~ b))) = ((False = b) = ((~ False) = (~ b)))).
Proof. exact (TRANS (@lem11820 a b) (@lem11825 a b)). Qed.
Lemma lem11827 (b : Prop) (a : Prop) (h1 : a = False) : ((a = b) = ((~ a) = (~ b))) = ((False = b) = ((~ False) = (~ b))).
Proof. exact (EQ_MP (@lem11826 a b) (@lem11817 b a h1)). Qed.
Lemma lem11828 (b : Prop) (a : Prop) (h1 : a = False) : ((False = b) = ((~ False) = (~ b))) = ((a = b) = ((~ a) = (~ b))).
Proof. exact (SYM (@lem11827 b a h1)). Qed.
Lemma lem11832 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem11833 (b : Prop) : (True = b) = b.
Proof. exact (@lem11832 b). Qed.
Lemma lem11834 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem11835 (b : Prop) : (term21 b) = (@eq Prop b).
Proof. exact (MK_COMB (@lem11834) (@lem11833 b)). Qed.
Lemma lem11839 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem11840 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem11841 : term22 = (@eq Prop False).
Proof. exact (MK_COMB (@lem11840) (@lem11839)). Qed.
Lemma lem11842 (b : Prop) : (~ b) = (~ b).
Proof. exact (eq_refl (~ b)). Qed.
Lemma lem11843 (b : Prop) : ((~ True) = (~ b)) = (False = (~ b)).
Proof. exact (MK_COMB (@lem11841) (@lem11842 b)). Qed.
Lemma lem11845 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem11846 (b : Prop) : (False = (~ b)) = (term23 b).
Proof. exact (@lem11845 (~ b)). Qed.
Lemma lem11847 (b : Prop) : ((~ True) = (~ b)) = (term23 b).
Proof. exact (TRANS (@lem11843 b) (@lem11846 b)). Qed.
Lemma lem11848 (b : Prop) : ((True = b) = ((~ True) = (~ b))) = (b = (term23 b)).
Proof. exact (MK_COMB (@lem11835 b) (@lem11847 b)). Qed.
Lemma lem11851 (b : Prop) : (b = (term23 b)) = ((True = b) = ((~ True) = (~ b))).
Proof. exact (SYM (@lem11848 b)). Qed.
Lemma lem11860 (t : Prop) : (term23 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem11861 (b : Prop) : (term23 b) = b.
Proof. exact (@lem11860 b). Qed.
Lemma lem11862 (b : Prop) : (@eq Prop b) = (@eq Prop b).
Proof. exact (eq_refl (@eq Prop b)). Qed.
Lemma lem11863 (b : Prop) : (b = (term23 b)) = (b = b).
Proof. exact (MK_COMB (@lem11862 b) (@lem11861 b)). Qed.
Lemma lem11865 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem11866 (x : Prop) : (x = x) = True.
Proof. exact (@lem11865 Prop x). Qed.
Lemma lem11867 (b : Prop) : (b = b) = True.
Proof. exact (@lem11866 b). Qed.
Lemma lem11868 (b : Prop) : (b = (term23 b)) = True.
Proof. exact (TRANS (@lem11863 b) (@lem11867 b)). Qed.
Lemma lem11869 (b : Prop) : True = (b = (term23 b)).
Proof. exact (SYM (@lem11868 b)). Qed.
Lemma lem11870 (b : Prop) : b = (term23 b).
Proof. exact (EQ_MP (@lem11869 b) (@lem0)). Qed.
Lemma lem11871 (b : Prop) : (True = b) = ((~ True) = (~ b)).
Proof. exact (EQ_MP (@lem11851 b) (@lem11870 b)). Qed.
Lemma lem11875 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem11876 (b : Prop) : (False = b) = (~ b).
Proof. exact (@lem11875 b). Qed.
Lemma lem11877 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem11878 (b : Prop) : (term24 b) = (term25 b).
Proof. exact (MK_COMB (@lem11877) (@lem11876 b)). Qed.
Lemma lem11882 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem11883 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem11884 : term26 = (@eq Prop True).
Proof. exact (MK_COMB (@lem11883) (@lem11882)). Qed.
Lemma lem11885 (b : Prop) : (~ b) = (~ b).
Proof. exact (eq_refl (~ b)). Qed.
Lemma lem11886 (b : Prop) : ((~ False) = (~ b)) = (True = (~ b)).
Proof. exact (MK_COMB (@lem11884) (@lem11885 b)). Qed.
Lemma lem11888 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem11889 (b : Prop) : (True = (~ b)) = (~ b).
Proof. exact (@lem11888 (~ b)). Qed.
Lemma lem11890 (b : Prop) : ((~ False) = (~ b)) = (~ b).
Proof. exact (TRANS (@lem11886 b) (@lem11889 b)). Qed.
Lemma lem11891 (b : Prop) : ((False = b) = ((~ False) = (~ b))) = ((~ b) = (~ b)).
Proof. exact (MK_COMB (@lem11878 b) (@lem11890 b)). Qed.
Lemma lem11893 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem11894 (x : Prop) : (x = x) = True.
Proof. exact (@lem11893 Prop x). Qed.
Lemma lem11895 (b : Prop) : ((~ b) = (~ b)) = True.
Proof. exact (@lem11894 (~ b)). Qed.
Lemma lem11896 (b : Prop) : ((False = b) = ((~ False) = (~ b))) = True.
Proof. exact (TRANS (@lem11891 b) (@lem11895 b)). Qed.
Lemma lem11897 (b : Prop) : True = ((False = b) = ((~ False) = (~ b))).
Proof. exact (SYM (@lem11896 b)). Qed.
Lemma lem11898 (b : Prop) : (False = b) = ((~ False) = (~ b)).
Proof. exact (EQ_MP (@lem11897 b) (@lem0)). Qed.
Lemma lem11899 (b : Prop) (a : Prop) (h1 : a = False) : (a = b) = ((~ a) = (~ b)).
Proof. exact (EQ_MP (@lem11828 b a h1) (@lem11898 b)). Qed.
Lemma lem11900 (b : Prop) (a : Prop) (h1 : a = True) : (a = b) = ((~ a) = (~ b)).
Proof. exact (EQ_MP (@lem11815 b a h1) (@lem11871 b)). Qed.
Lemma lem11907 (a : Prop) (b : Prop) : (a = b) = ((~ a) = (~ b)).
Proof. exact (or_elim (@lem11792 a) (fun h0 : a = True => @lem11900 b a h0) (fun h0 : a = False => @lem11899 b a h0)). Qed.
Lemma lem11908 {A : Type'} (P : A -> Prop) (Q : Prop) : ((term27 A P Q) = (term28 A P Q)) = ((term29 A P Q) = (term30 A P Q)).
Proof. exact (@lem11907 (term27 A P Q) (term28 A P Q)). Qed.
Lemma lem11909 {A : Type'} (P : A -> Prop) (Q : Prop) : ((term29 A P Q) = (term30 A P Q)) = ((term27 A P Q) = (term28 A P Q)).
Proof. exact (SYM (@lem11908 A P Q)). Qed.
Lemma lem11913 (t1 : Prop) (t2 : Prop) : (term8 t1 t2) = (term9 t1 t2).
Proof. exact (EQ_MP (@lem11777 t1 t2) (@lem11776 t1 t2)). Qed.
Lemma lem11914 {A : Type'} (P : A -> Prop) (Q : Prop) : (term29 A P Q) = (term31 A P Q).
Proof. exact (@lem11913 (term32 A P) Q). Qed.
Lemma lem11916 {A : Type'} (P : A -> Prop) (Q : Prop) : (term3 A P Q) = (term4 A P Q).
Proof. exact (EQ_MP (@lem11771 A P Q) (@lem11770 A P Q)). Qed.
Lemma lem11917 {A : Type'} (P : A -> Prop) (Q : Prop) : (term3 A P Q) = (term4 A P Q).
Proof. exact (@lem11916 A P Q). Qed.
Lemma lem11918 {A : Type'} (P : A -> Prop) (Q : Prop) : (term31 A P Q) = (term33 A P Q).
Proof. exact (@lem11917 A P (~ Q)). Qed.
Lemma lem11923 {A : Type'} (P : A -> Prop) (Q : Prop) : (term29 A P Q) = (term33 A P Q).
Proof. exact (TRANS (@lem11914 A P Q) (@lem11918 A P Q)). Qed.
Lemma lem11926 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem11927 {A : Type'} (P : A -> Prop) (Q : Prop) : (term34 A P Q) = (term35 A P Q).
Proof. exact (MK_COMB (@lem11926) (@lem11923 A P Q)). Qed.
Lemma lem11929 {A : Type'} (P : A -> Prop) : (term11 A P) = (term12 A P).
Proof. exact (EQ_MP (@lem11780 A P) (@lem11779 A P)). Qed.
Lemma lem11930 {A : Type'} (P : A -> Prop) : (term11 A P) = (term12 A P).
Proof. exact (@lem11929 A P). Qed.
Lemma lem11931 {A : Type'} (P : A -> Prop) (Q : Prop) : (term36 A P Q) = (term37 A P Q).
Proof. exact (@lem11930 A (term38 A P Q)). Qed.
Lemma lem11932 {A : Type'} (P : A -> Prop) (x : A) (Q : Prop) : (term39 A P Q x) = (term40 A P x Q).
Proof. exact (eq_refl (term39 A P Q x)). Qed.
Lemma lem11933 {A : Type'} (P : A -> Prop) (Q : Prop) : (term41 A P Q) = (term38 A P Q).
Proof. exact (fun_ext (fun x : A => @lem11932 A P x Q)). Qed.
Lemma lem11934 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem11935 {A : Type'} (P : A -> Prop) (Q : Prop) : (term42 A P Q) = (term28 A P Q).
Proof. exact (MK_COMB (@lem11934 A) (@lem11933 A P Q)). Qed.
Lemma lem11936 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem11937 {A : Type'} (P : A -> Prop) (Q : Prop) : (term36 A P Q) = (term30 A P Q).
Proof. exact (MK_COMB (@lem11936) (@lem11935 A P Q)). Qed.
Lemma lem11938 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem11939 {A : Type'} (P : A -> Prop) (Q : Prop) : (term43 A P Q) = (term44 A P Q).
Proof. exact (MK_COMB (@lem11938) (@lem11937 A P Q)). Qed.
Lemma lem11940 {A : Type'} (P : A -> Prop) (x : A) (Q : Prop) : (term39 A P Q x) = (term40 A P x Q).
Proof. exact (eq_refl (term39 A P Q x)). Qed.
Lemma lem11941 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem11942 {A : Type'} (P : A -> Prop) (x : A) (Q : Prop) : (term45 A P Q x) = (term46 A P x Q).
Proof. exact (MK_COMB (@lem11941) (@lem11940 A P x Q)). Qed.
Lemma lem11943 {A : Type'} (P : A -> Prop) (Q : Prop) : (term47 A P Q) = (term48 A P Q).
Proof. exact (fun_ext (fun x : A => @lem11942 A P x Q)). Qed.
Lemma lem11944 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem11945 {A : Type'} (P : A -> Prop) (Q : Prop) : (term37 A P Q) = (term49 A P Q).
Proof. exact (MK_COMB (@lem11944 A) (@lem11943 A P Q)). Qed.
Lemma lem11946 {A : Type'} (P : A -> Prop) (Q : Prop) : ((term36 A P Q) = (term37 A P Q)) = ((term30 A P Q) = (term49 A P Q)).
Proof. exact (MK_COMB (@lem11939 A P Q) (@lem11945 A P Q)). Qed.
Lemma lem11947 {A : Type'} (P : A -> Prop) (Q : Prop) : (term30 A P Q) = (term49 A P Q).
Proof. exact (EQ_MP (@lem11946 A P Q) (@lem11931 A P Q)). Qed.
Lemma lem11953 (t1 : Prop) (t2 : Prop) : (term8 t1 t2) = (term9 t1 t2).
Proof. exact (EQ_MP (@lem11777 t1 t2) (@lem11776 t1 t2)). Qed.
Lemma lem11954 {A : Type'} (P : A -> Prop) (x : A) (Q : Prop) : (term46 A P x Q) = (term50 A P x Q).
Proof. exact (@lem11953 (P x) Q). Qed.
Lemma lem11957 {A : Type'} (P : A -> Prop) (Q : Prop) : (term48 A P Q) = (term51 A P Q).
Proof. exact (fun_ext (fun x : A => @lem11954 A P x Q)). Qed.
Lemma lem11958 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem11959 {A : Type'} (P : A -> Prop) (Q : Prop) : (term49 A P Q) = (term33 A P Q).
Proof. exact (MK_COMB (@lem11958 A) (@lem11957 A P Q)). Qed.
Lemma lem11964 {A : Type'} (P : A -> Prop) (Q : Prop) : (term30 A P Q) = (term33 A P Q).
Proof. exact (TRANS (@lem11947 A P Q) (@lem11959 A P Q)). Qed.
Lemma lem11965 {A : Type'} (P : A -> Prop) (Q : Prop) : ((term29 A P Q) = (term30 A P Q)) = ((term33 A P Q) = (term33 A P Q)).
Proof. exact (MK_COMB (@lem11927 A P Q) (@lem11964 A P Q)). Qed.
Lemma lem11967 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem11968 (x : Prop) : (x = x) = True.
Proof. exact (@lem11967 Prop x). Qed.
Lemma lem11969 {A : Type'} (P : A -> Prop) (Q : Prop) : ((term33 A P Q) = (term33 A P Q)) = True.
Proof. exact (@lem11968 (term33 A P Q)). Qed.
Lemma lem11970 {A : Type'} (P : A -> Prop) (Q : Prop) : ((term29 A P Q) = (term30 A P Q)) = True.
Proof. exact (TRANS (@lem11965 A P Q) (@lem11969 A P Q)). Qed.
Lemma lem11971 {A : Type'} (P : A -> Prop) (Q : Prop) : True = ((term29 A P Q) = (term30 A P Q)).
Proof. exact (SYM (@lem11970 A P Q)). Qed.
Lemma lem11972 {A : Type'} (P : A -> Prop) (Q : Prop) : (term29 A P Q) = (term30 A P Q).
Proof. exact (EQ_MP (@lem11971 A P Q) (@lem0)). Qed.
Lemma lem11973 {A : Type'} (P : A -> Prop) (Q : Prop) : (term27 A P Q) = (term28 A P Q).
Proof. exact (EQ_MP (@lem11909 A P Q) (@lem11972 A P Q)). Qed.
Lemma lem11978 {A : Type'} (P : A -> Prop) : term52 A P.
Proof. exact (fun Q : Prop => @lem11973 A P Q). Qed.
Lemma lem11983 {A : Type'} : term53 A.
Proof. exact (fun P : A -> Prop => @lem11978 A P). Qed.
