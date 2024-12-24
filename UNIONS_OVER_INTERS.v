Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import UNIONS_OVER_INTERS_term_abbrevs.
Require Import AND_FORALL_THM_spec.
Require Import BOOL_CASES_AX_spec.
Require Import DISJ_ACI_spec.
Require Import EXTENSION_spec.
Require Import IN_INTERS_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_EXISTS_THM_spec.
Require Import NOT_FORALL_THM_spec.
Require Import NOT_IMP_spec.
Require Import SIMPLE_IMAGE_spec.
Require Import SKOLEM_THM_spec.
Require Import UNIONS_IMAGE_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm3464405_spec.
Require Import thm3464408_spec.
Lemma lem3483764 {A B : Type'} (P : type1413 A B) (h1 : (term0 A B P) = (term1 A B P)) : (term0 A B P) = (term1 A B P).
Proof. exact (h1). Qed.
Lemma lem3483765 {A B : Type'} (P : type1413 A B) (h1 : (term0 A B P) = (term1 A B P)) : (term1 A B P) = (term0 A B P).
Proof. exact (SYM (@lem3483764 A B P h1)). Qed.
Lemma lem3483766 {A B : Type'} (P : type1413 A B) (h1 : (term1 A B P) = (term0 A B P)) : (term1 A B P) = (term0 A B P).
Proof. exact (h1). Qed.
Lemma lem3483767 {A B : Type'} (P : type1413 A B) (h1 : (term1 A B P) = (term0 A B P)) : (term0 A B P) = (term1 A B P).
Proof. exact (SYM (@lem3483766 A B P h1)). Qed.
Lemma lem3483768 {A B : Type'} (P : type1413 A B) : ((term0 A B P) = (term1 A B P)) = ((term1 A B P) = (term0 A B P)).
Proof. exact (prop_ext (fun h1 : (term0 A B P) = (term1 A B P) => @lem3483765 A B P h1) (fun h1 : (term1 A B P) = (term0 A B P) => @lem3483767 A B P h1)). Qed.
Lemma lem3483769 {A B : Type'} : (term2 A B) = (term3 A B).
Proof. exact (fun_ext (fun P : type1413 A B => @lem3483768 A B P)). Qed.
Lemma lem3483770 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem3483771 {A B : Type'} : (term4 A B) = (term5 A B).
Proof. exact (MK_COMB (@lem3483770 A B) (@lem3483769 A B)). Qed.
Lemma lem3483772 {A B : Type'} : term5 A B.
Proof. exact (EQ_MP (@lem3483771 A B) (@lem13546 A B)). Qed.
Lemma lem3483773 {A B : Type'} (P : type1413 A B) : term6 A B P.
Proof. exact (@lem3483772 A B P). Qed.
Lemma lem3483774 {A B : Type'} (P : type1413 A B) : (term6 A B P) = ((term1 A B P) = (term0 A B P)).
Proof. exact (eq_refl (term6 A B P)). Qed.
Lemma lem3483776 {A : Type'} (P : A -> Prop) : term7 A P.
Proof. exact (@lem5146 A P). Qed.
Lemma lem3483777 {A : Type'} (P : A -> Prop) : (term7 A P) = (term8 A P).
Proof. exact (eq_refl (term7 A P)). Qed.
Lemma lem3483778 {A : Type'} (P : A -> Prop) : term8 A P.
Proof. exact (EQ_MP (@lem3483777 A P) (@lem3483776 A P)). Qed.
Lemma lem3483779 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term9 A P Q.
Proof. exact (@lem3483778 A P Q). Qed.
Lemma lem3483780 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term9 A P Q) = ((term10 A P Q) = (term11 A P Q)).
Proof. exact (eq_refl (term9 A P Q)). Qed.
Lemma lem3483782 {A : Type'} (P : A -> Prop) : term12 A P.
Proof. exact (@lem10660 A P). Qed.
Lemma lem3483783 {A : Type'} (P : A -> Prop) : (term12 A P) = ((term13 A P) = (term14 A P)).
Proof. exact (eq_refl (term12 A P)). Qed.
Lemma lem3483785 (t1 : Prop) : term15 t1.
Proof. exact (@lem10299 t1). Qed.
Lemma lem3483786 (t1 : Prop) : (term15 t1) = (term16 t1).
Proof. exact (eq_refl (term15 t1)). Qed.
Lemma lem3483787 (t1 : Prop) : term16 t1.
Proof. exact (EQ_MP (@lem3483786 t1) (@lem3483785 t1)). Qed.
Lemma lem3483788 (t1 : Prop) (t2 : Prop) : term17 t1 t2.
Proof. exact (@lem3483787 t1 t2). Qed.
Lemma lem3483789 (t1 : Prop) (t2 : Prop) : (term17 t1 t2) = ((term18 t1 t2) = (term19 t1 t2)).
Proof. exact (eq_refl (term17 t1 t2)). Qed.
Lemma lem3483791 {A : Type'} (P : A -> Prop) : term20 A P.
Proof. exact (@lem10884 A P). Qed.
Lemma lem3483792 {A : Type'} (P : A -> Prop) : (term20 A P) = ((term21 A P) = (term22 A P)).
Proof. exact (eq_refl (term20 A P)). Qed.
Lemma lem3483802 (p : Prop) : term23 p.
Proof. exact (@lem9851 p). Qed.
Lemma lem3483803 (p : Prop) : (term23 p) = (term24 p).
Proof. exact (eq_refl (term23 p)). Qed.
Lemma lem3483804 (p : Prop) : term24 p.
Proof. exact (EQ_MP (@lem3483803 p) (@lem3483802 p)). Qed.
Lemma lem3483805 (p : Prop) (h1 : p = True) : p = True.
Proof. exact (h1). Qed.
Lemma lem3483806 (p : Prop) (h1 : p = False) : p = False.
Proof. exact (h1). Qed.
Lemma lem3483815 (q : Prop) : (term25 q) = (term25 q).
Proof. exact (eq_refl (term25 q)). Qed.
Lemma lem3483816 (q : Prop) (p : Prop) (h1 : p = True) : (term26 q p) = (term27 q).
Proof. exact (MK_COMB (@lem3483815 q) (@lem3483805 p h1)). Qed.
Lemma lem3483817 (q : Prop) : (term27 q) = ((True = q) = ((~ True) = (~ q))).
Proof. exact (eq_refl (term27 q)). Qed.
Lemma lem3483818 (q : Prop) (p : Prop) : (term28 q p) = (term28 q p).
Proof. exact (eq_refl (term28 q p)). Qed.
Lemma lem3483819 (p : Prop) (q : Prop) : ((term26 q p) = (term27 q)) = ((term26 q p) = ((True = q) = ((~ True) = (~ q)))).
Proof. exact (MK_COMB (@lem3483818 q p) (@lem3483817 q)). Qed.
Lemma lem3483820 (p : Prop) (q : Prop) : (term26 q p) = ((p = q) = ((~ p) = (~ q))).
Proof. exact (eq_refl (term26 q p)). Qed.
Lemma lem3483821 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3483822 (p : Prop) (q : Prop) : (term28 q p) = (term29 p q).
Proof. exact (MK_COMB (@lem3483821) (@lem3483820 p q)). Qed.
Lemma lem3483823 (q : Prop) : ((True = q) = ((~ True) = (~ q))) = ((True = q) = ((~ True) = (~ q))).
Proof. exact (eq_refl ((True = q) = ((~ True) = (~ q)))). Qed.
Lemma lem3483824 (p : Prop) (q : Prop) : ((term26 q p) = ((True = q) = ((~ True) = (~ q)))) = (((p = q) = ((~ p) = (~ q))) = ((True = q) = ((~ True) = (~ q)))).
Proof. exact (MK_COMB (@lem3483822 p q) (@lem3483823 q)). Qed.
Lemma lem3483825 (p : Prop) (q : Prop) : ((term26 q p) = (term27 q)) = (((p = q) = ((~ p) = (~ q))) = ((True = q) = ((~ True) = (~ q)))).
Proof. exact (TRANS (@lem3483819 p q) (@lem3483824 p q)). Qed.
Lemma lem3483826 (q : Prop) (p : Prop) (h1 : p = True) : ((p = q) = ((~ p) = (~ q))) = ((True = q) = ((~ True) = (~ q))).
Proof. exact (EQ_MP (@lem3483825 p q) (@lem3483816 q p h1)). Qed.
Lemma lem3483827 (q : Prop) (p : Prop) (h1 : p = True) : ((True = q) = ((~ True) = (~ q))) = ((p = q) = ((~ p) = (~ q))).
Proof. exact (SYM (@lem3483826 q p h1)). Qed.
Lemma lem3483828 (q : Prop) : (term25 q) = (term25 q).
Proof. exact (eq_refl (term25 q)). Qed.
Lemma lem3483829 (q : Prop) (p : Prop) (h1 : p = False) : (term26 q p) = (term30 q).
Proof. exact (MK_COMB (@lem3483828 q) (@lem3483806 p h1)). Qed.
Lemma lem3483830 (q : Prop) : (term30 q) = ((False = q) = ((~ False) = (~ q))).
Proof. exact (eq_refl (term30 q)). Qed.
Lemma lem3483831 (q : Prop) (p : Prop) : (term28 q p) = (term28 q p).
Proof. exact (eq_refl (term28 q p)). Qed.
Lemma lem3483832 (p : Prop) (q : Prop) : ((term26 q p) = (term30 q)) = ((term26 q p) = ((False = q) = ((~ False) = (~ q)))).
Proof. exact (MK_COMB (@lem3483831 q p) (@lem3483830 q)). Qed.
Lemma lem3483833 (p : Prop) (q : Prop) : (term26 q p) = ((p = q) = ((~ p) = (~ q))).
Proof. exact (eq_refl (term26 q p)). Qed.
Lemma lem3483834 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3483835 (p : Prop) (q : Prop) : (term28 q p) = (term29 p q).
Proof. exact (MK_COMB (@lem3483834) (@lem3483833 p q)). Qed.
Lemma lem3483836 (q : Prop) : ((False = q) = ((~ False) = (~ q))) = ((False = q) = ((~ False) = (~ q))).
Proof. exact (eq_refl ((False = q) = ((~ False) = (~ q)))). Qed.
Lemma lem3483837 (p : Prop) (q : Prop) : ((term26 q p) = ((False = q) = ((~ False) = (~ q)))) = (((p = q) = ((~ p) = (~ q))) = ((False = q) = ((~ False) = (~ q)))).
Proof. exact (MK_COMB (@lem3483835 p q) (@lem3483836 q)). Qed.
Lemma lem3483838 (p : Prop) (q : Prop) : ((term26 q p) = (term30 q)) = (((p = q) = ((~ p) = (~ q))) = ((False = q) = ((~ False) = (~ q)))).
Proof. exact (TRANS (@lem3483832 p q) (@lem3483837 p q)). Qed.
Lemma lem3483839 (q : Prop) (p : Prop) (h1 : p = False) : ((p = q) = ((~ p) = (~ q))) = ((False = q) = ((~ False) = (~ q))).
Proof. exact (EQ_MP (@lem3483838 p q) (@lem3483829 q p h1)). Qed.
Lemma lem3483840 (q : Prop) (p : Prop) (h1 : p = False) : ((False = q) = ((~ False) = (~ q))) = ((p = q) = ((~ p) = (~ q))).
Proof. exact (SYM (@lem3483839 q p h1)). Qed.
Lemma lem3483844 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem3483845 (q : Prop) : (True = q) = q.
Proof. exact (@lem3483844 q). Qed.
Lemma lem3483846 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3483847 (q : Prop) : (term31 q) = (@eq Prop q).
Proof. exact (MK_COMB (@lem3483846) (@lem3483845 q)). Qed.
Lemma lem3483851 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem3483852 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3483853 : term32 = (@eq Prop False).
Proof. exact (MK_COMB (@lem3483852) (@lem3483851)). Qed.
Lemma lem3483854 (q : Prop) : (~ q) = (~ q).
Proof. exact (eq_refl (~ q)). Qed.
Lemma lem3483855 (q : Prop) : ((~ True) = (~ q)) = (False = (~ q)).
Proof. exact (MK_COMB (@lem3483853) (@lem3483854 q)). Qed.
Lemma lem3483857 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem3483858 (q : Prop) : (False = (~ q)) = (term33 q).
Proof. exact (@lem3483857 (~ q)). Qed.
Lemma lem3483860 (t : Prop) : (term33 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem3483861 (q : Prop) : (term33 q) = q.
Proof. exact (@lem3483860 q). Qed.
Lemma lem3483862 (q : Prop) : (False = (~ q)) = q.
Proof. exact (TRANS (@lem3483858 q) (@lem3483861 q)). Qed.
Lemma lem3483863 (q : Prop) : ((~ True) = (~ q)) = q.
Proof. exact (TRANS (@lem3483855 q) (@lem3483862 q)). Qed.
Lemma lem3483864 (q : Prop) : ((True = q) = ((~ True) = (~ q))) = (q = q).
Proof. exact (MK_COMB (@lem3483847 q) (@lem3483863 q)). Qed.
Lemma lem3483866 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3483867 (x : Prop) : (x = x) = True.
Proof. exact (@lem3483866 Prop x). Qed.
Lemma lem3483868 (q : Prop) : (q = q) = True.
Proof. exact (@lem3483867 q). Qed.
Lemma lem3483869 (q : Prop) : ((True = q) = ((~ True) = (~ q))) = True.
Proof. exact (TRANS (@lem3483864 q) (@lem3483868 q)). Qed.
Lemma lem3483870 (q : Prop) : True = ((True = q) = ((~ True) = (~ q))).
Proof. exact (SYM (@lem3483869 q)). Qed.
Lemma lem3483871 (q : Prop) : (True = q) = ((~ True) = (~ q)).
Proof. exact (EQ_MP (@lem3483870 q) (@lem0)). Qed.
Lemma lem3483875 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem3483876 (q : Prop) : (False = q) = (~ q).
Proof. exact (@lem3483875 q). Qed.
Lemma lem3483877 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3483878 (q : Prop) : (term34 q) = (term35 q).
Proof. exact (MK_COMB (@lem3483877) (@lem3483876 q)). Qed.
Lemma lem3483882 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3483883 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3483884 : term36 = (@eq Prop True).
Proof. exact (MK_COMB (@lem3483883) (@lem3483882)). Qed.
Lemma lem3483885 (q : Prop) : (~ q) = (~ q).
Proof. exact (eq_refl (~ q)). Qed.
Lemma lem3483886 (q : Prop) : ((~ False) = (~ q)) = (True = (~ q)).
Proof. exact (MK_COMB (@lem3483884) (@lem3483885 q)). Qed.
Lemma lem3483888 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem3483889 (q : Prop) : (True = (~ q)) = (~ q).
Proof. exact (@lem3483888 (~ q)). Qed.
Lemma lem3483890 (q : Prop) : ((~ False) = (~ q)) = (~ q).
Proof. exact (TRANS (@lem3483886 q) (@lem3483889 q)). Qed.
Lemma lem3483891 (q : Prop) : ((False = q) = ((~ False) = (~ q))) = ((~ q) = (~ q)).
Proof. exact (MK_COMB (@lem3483878 q) (@lem3483890 q)). Qed.
Lemma lem3483893 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3483894 (x : Prop) : (x = x) = True.
Proof. exact (@lem3483893 Prop x). Qed.
Lemma lem3483895 (q : Prop) : ((~ q) = (~ q)) = True.
Proof. exact (@lem3483894 (~ q)). Qed.
Lemma lem3483896 (q : Prop) : ((False = q) = ((~ False) = (~ q))) = True.
Proof. exact (TRANS (@lem3483891 q) (@lem3483895 q)). Qed.
Lemma lem3483897 (q : Prop) : True = ((False = q) = ((~ False) = (~ q))).
Proof. exact (SYM (@lem3483896 q)). Qed.
Lemma lem3483898 (q : Prop) : (False = q) = ((~ False) = (~ q)).
Proof. exact (EQ_MP (@lem3483897 q) (@lem0)). Qed.
Lemma lem3483899 (q : Prop) (p : Prop) (h1 : p = False) : (p = q) = ((~ p) = (~ q)).
Proof. exact (EQ_MP (@lem3483840 q p h1) (@lem3483898 q)). Qed.
Lemma lem3483900 (q : Prop) (p : Prop) (h1 : p = True) : (p = q) = ((~ p) = (~ q)).
Proof. exact (EQ_MP (@lem3483827 q p h1) (@lem3483871 q)). Qed.
Lemma lem3483928 {_83095 : Type'} : term37 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem3483929 {_83095 : Type'} (p : _83095 -> Prop) : term38 _83095 p.
Proof. exact (@lem3483928 _83095 p). Qed.
Lemma lem3483930 {_83095 : Type'} (p : _83095 -> Prop) : (term38 _83095 p) = (term39 _83095 p).
Proof. exact (eq_refl (term38 _83095 p)). Qed.
Lemma lem3483931 {_83095 : Type'} (p : _83095 -> Prop) : term39 _83095 p.
Proof. exact (EQ_MP (@lem3483930 _83095 p) (@lem3483929 _83095 p)). Qed.
Lemma lem3483932 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term40 _83095 p x.
Proof. exact (@lem3483931 _83095 p x). Qed.
Lemma lem3483933 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term40 _83095 p x) = ((term41 _83095 x p) = (p x)).
Proof. exact (eq_refl (term40 _83095 p x)). Qed.
Lemma lem3483942 {A : Type'} (s : type686 A) : term42 A s.
Proof. exact (@lem3205364 A s). Qed.
Lemma lem3483943 {A : Type'} (s : type686 A) : (term42 A s) = (term43 A s).
Proof. exact (eq_refl (term42 A s)). Qed.
Lemma lem3483944 {A : Type'} (s : type686 A) : term43 A s.
Proof. exact (EQ_MP (@lem3483943 A s) (@lem3483942 A s)). Qed.
Lemma lem3483945 {A : Type'} (s : type686 A) (x : A) : term44 A s x.
Proof. exact (@lem3483944 A s x). Qed.
Lemma lem3483946 {A : Type'} (s : type686 A) (x : A) : (term44 A s x) = ((term45 A x s) = (term46 A s x)).
Proof. exact (eq_refl (term44 A s x)). Qed.
Lemma lem3483963 {_89711 _89725 : Type'} : term47 _89711 _89725.
Proof. exact (EQ_MP (@lem3464408 _89711 _89725) (@lem3464405 _89711 _89725)). Qed.
Lemma lem3483964 {_89711 _89725 : Type'} (P : _89725 -> Prop) : term48 _89711 _89725 P.
Proof. exact (@lem3483963 _89711 _89725 P). Qed.
Lemma lem3483965 {_89711 _89725 : Type'} (P : _89725 -> Prop) : (term48 _89711 _89725 P) = (term49 _89711 _89725 P).
Proof. exact (eq_refl (term48 _89711 _89725 P)). Qed.
Lemma lem3483966 {_89711 _89725 : Type'} (P : _89725 -> Prop) : term49 _89711 _89725 P.
Proof. exact (EQ_MP (@lem3483965 _89711 _89725 P) (@lem3483964 _89711 _89725 P)). Qed.
Lemma lem3483967 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : term50 _89711 _89725 P f.
Proof. exact (@lem3483966 _89711 _89725 P f). Qed.
Lemma lem3483968 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term50 _89711 _89725 P f) = ((term51 _89711 _89725 P f) = (term52 _89711 _89725 P f)).
Proof. exact (eq_refl (term50 _89711 _89725 P f)). Qed.
Lemma lem3483970 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) : term53 _89422 _89438 f.
Proof. exact (@lem3452302 _89422 _89438 f). Qed.
Lemma lem3483971 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) : (term53 _89422 _89438 f) = (term54 _89422 _89438 f).
Proof. exact (eq_refl (term53 _89422 _89438 f)). Qed.
Lemma lem3483972 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) : term54 _89422 _89438 f.
Proof. exact (EQ_MP (@lem3483971 _89422 _89438 f) (@lem3483970 _89422 _89438 f)). Qed.
Lemma lem3483973 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) : term55 _89422 _89438 f s.
Proof. exact (@lem3483972 _89422 _89438 f s). Qed.
Lemma lem3483974 {_89422 _89438 : Type'} (s : _89438 -> Prop) (f : type1470 _89422 _89438) : (term55 _89422 _89438 f s) = ((term56 _89422 _89438 f s) = (term57 _89422 _89438 s f)).
Proof. exact (eq_refl (term55 _89422 _89438 f s)). Qed.
Lemma lem3483982 {_88128 _88132 : Type'} (f : _88128 -> _88132) : term58 _88128 _88132 f.
Proof. exact (@lem3393993 _88128 _88132 f). Qed.
Lemma lem3483983 {_88128 _88132 : Type'} (f : _88128 -> _88132) : (term58 _88128 _88132 f) = (term59 _88128 _88132 f).
Proof. exact (eq_refl (term58 _88128 _88132 f)). Qed.
Lemma lem3483984 {_88128 _88132 : Type'} (f : _88128 -> _88132) : term59 _88128 _88132 f.
Proof. exact (EQ_MP (@lem3483983 _88128 _88132 f) (@lem3483982 _88128 _88132 f)). Qed.
Lemma lem3483985 {_88128 _88132 : Type'} (f : _88128 -> _88132) (s : _88128 -> Prop) : term60 _88128 _88132 f s.
Proof. exact (@lem3483984 _88128 _88132 f s). Qed.
Lemma lem3483986 {_88128 _88132 : Type'} (f : _88128 -> _88132) (s : _88128 -> Prop) : (term60 _88128 _88132 f s) = ((term61 _88128 _88132 s f) = (@IMAGE _88128 _88132 f s)).
Proof. exact (eq_refl (term60 _88128 _88132 f s)). Qed.
Lemma lem3483988 {A : Type'} (s : A -> Prop) : term62 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem3483989 {A : Type'} (s : A -> Prop) : (term62 A s) = (term63 A s).
Proof. exact (eq_refl (term62 A s)). Qed.
Lemma lem3483990 {A : Type'} (s : A -> Prop) : term63 A s.
Proof. exact (EQ_MP (@lem3483989 A s) (@lem3483988 A s)). Qed.
Lemma lem3483991 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term64 A s t.
Proof. exact (@lem3483990 A s t). Qed.
Lemma lem3483992 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term64 A s t) = ((s = t) = (term65 A s t)).
Proof. exact (eq_refl (term64 A s t)). Qed.
Lemma lem3483995 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term65 A s t).
Proof. exact (EQ_MP (@lem3483992 A s t) (@lem3483991 A s t)). Qed.
Lemma lem3483996 {B : Type'} (s : B -> Prop) (t : B -> Prop) : (s = t) = (term65 B s t).
Proof. exact (@lem3483995 B s t). Qed.
Lemma lem3483997 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : ((term66 A B s f) = (term67 A B f s)) = (term68 A B f s).
Proof. exact (@lem3483996 B (term66 A B s f) (term67 A B f s)). Qed.
Lemma lem3483998 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : (term68 A B f s) = ((term66 A B s f) = (term67 A B f s)).
Proof. exact (SYM (@lem3483997 A B f s)). Qed.
Lemma lem3484006 {_88128 _88132 : Type'} (f : _88128 -> _88132) (s : _88128 -> Prop) : (term61 _88128 _88132 s f) = (@IMAGE _88128 _88132 f s).
Proof. exact (EQ_MP (@lem3483986 _88128 _88132 f s) (@lem3483985 _88128 _88132 f s)). Qed.
Lemma lem3484007 {A B : Type'} (f : type1413 A B) (s : A -> Prop) : (term69 A B s f) = (@IMAGE A (B -> Prop) f s).
Proof. exact (@lem3484006 A (B -> Prop) f s). Qed.
Lemma lem3484008 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : (term70 A B s f) = (term71 A B f s).
Proof. exact (@lem3484007 A B (term72 A B f) s). Qed.
Lemma lem3484009 {A B : Type'} (f : type1374 A B) (x : A) : (term73 A B f x) = (term74 A B f x).
Proof. exact (eq_refl (term73 A B f x)). Qed.
Lemma lem3484010 {A B : Type'} (GEN_PVAR_77 : B -> Prop) (x : A) (s : A -> Prop) : (term75 A B GEN_PVAR_77 x s) = (term75 A B GEN_PVAR_77 x s).
Proof. exact (eq_refl (term75 A B GEN_PVAR_77 x s)). Qed.
Lemma lem3484011 {A B : Type'} (GEN_PVAR_77 : B -> Prop) (s : A -> Prop) (f : type1374 A B) (x : A) : (term76 A B GEN_PVAR_77 s f x) = (term77 A B GEN_PVAR_77 s f x).
Proof. exact (MK_COMB (@lem3484010 A B GEN_PVAR_77 x s) (@lem3484009 A B f x)). Qed.
Lemma lem3484012 {A B : Type'} (GEN_PVAR_77 : B -> Prop) (s : A -> Prop) (f : type1374 A B) : (term78 A B GEN_PVAR_77 s f) = (term79 A B GEN_PVAR_77 s f).
Proof. exact (fun_ext (fun x : A => @lem3484011 A B GEN_PVAR_77 s f x)). Qed.
Lemma lem3484013 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3484014 {A B : Type'} (GEN_PVAR_77 : B -> Prop) (s : A -> Prop) (f : type1374 A B) : (term80 A B GEN_PVAR_77 s f) = (term81 A B GEN_PVAR_77 s f).
Proof. exact (MK_COMB (@lem3484013 A) (@lem3484012 A B GEN_PVAR_77 s f)). Qed.
Lemma lem3484015 {A B : Type'} (s : A -> Prop) (f : type1374 A B) : (term82 A B s f) = (term83 A B s f).
Proof. exact (fun_ext (fun GEN_PVAR_77 : B -> Prop => @lem3484014 A B GEN_PVAR_77 s f)). Qed.
Lemma lem3484016 {B : Type'} : (@GSPEC (B -> Prop)) = (@GSPEC (B -> Prop)).
Proof. exact (eq_refl (@GSPEC (B -> Prop))). Qed.
Lemma lem3484017 {A B : Type'} (s : A -> Prop) (f : type1374 A B) : (term70 A B s f) = (term84 A B s f).
Proof. exact (MK_COMB (@lem3484016 B) (@lem3484015 A B s f)). Qed.
Lemma lem3484018 {B : Type'} : (@eq ((B -> Prop) -> Prop)) = (@eq ((B -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((B -> Prop) -> Prop))). Qed.
Lemma lem3484019 {A B : Type'} (s : A -> Prop) (f : type1374 A B) : (term85 A B s f) = (term86 A B s f).
Proof. exact (MK_COMB (@lem3484018 B) (@lem3484017 A B s f)). Qed.
Lemma lem3484020 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : (term71 A B f s) = (term71 A B f s).
Proof. exact (eq_refl (term71 A B f s)). Qed.
Lemma lem3484021 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : ((term70 A B s f) = (term71 A B f s)) = ((term84 A B s f) = (term71 A B f s)).
Proof. exact (MK_COMB (@lem3484019 A B s f) (@lem3484020 A B f s)). Qed.
Lemma lem3484022 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : (term84 A B s f) = (term71 A B f s).
Proof. exact (EQ_MP (@lem3484021 A B f s) (@lem3484008 A B f s)). Qed.
Lemma lem3484023 {B : Type'} : (@UNIONS B) = (@UNIONS B).
Proof. exact (eq_refl (@UNIONS B)). Qed.
Lemma lem3484024 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : (term66 A B s f) = (term87 A B f s).
Proof. exact (MK_COMB (@lem3484023 B) (@lem3484022 A B f s)). Qed.
Lemma lem3484026 {_89422 _89438 : Type'} (s : _89438 -> Prop) (f : type1470 _89422 _89438) : (term56 _89422 _89438 f s) = (term57 _89422 _89438 s f).
Proof. exact (EQ_MP (@lem3483974 _89422 _89438 s f) (@lem3483973 _89422 _89438 f s)). Qed.
Lemma lem3484027 {A B : Type'} (s : A -> Prop) (f : type1413 A B) : (term88 A B f s) = (term89 A B s f).
Proof. exact (@lem3484026 B A s f). Qed.
Lemma lem3484028 {A B : Type'} (s : A -> Prop) (f : type1374 A B) : (term87 A B f s) = (term90 A B s f).
Proof. exact (@lem3484027 A B s (term72 A B f)). Qed.
Lemma lem3484040 {A B : Type'} (f : A -> B) (y : A) : (term91 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3484041 {A B : Type'} (f : type1413 A B) (y : A) : (term92 A B f y) = (f y).
Proof. exact (@lem3484040 A (B -> Prop) f y). Qed.
Lemma lem3484042 {A B : Type'} (f : type1374 A B) (x : A) : (term93 A B f x) = (term73 A B f x).
Proof. exact (@lem3484041 A B (term72 A B f) x). Qed.
Lemma lem3484043 {A B : Type'} (f : type1374 A B) (x : A) : (term73 A B f x) = (term74 A B f x).
Proof. exact (eq_refl (term73 A B f x)). Qed.
Lemma lem3484044 {A B : Type'} (f : type1374 A B) : (term94 A B f) = (term72 A B f).
Proof. exact (fun_ext (fun x : A => @lem3484043 A B f x)). Qed.
Lemma lem3484045 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3484046 {A B : Type'} (f : type1374 A B) (x : A) : (term93 A B f x) = (term73 A B f x).
Proof. exact (MK_COMB (@lem3484044 A B f) (@lem3484045 A x)). Qed.
Lemma lem3484047 {B : Type'} : (@eq (B -> Prop)) = (@eq (B -> Prop)).
Proof. exact (eq_refl (@eq (B -> Prop))). Qed.
Lemma lem3484048 {A B : Type'} (f : type1374 A B) (x : A) : (term95 A B f x) = (term96 A B f x).
Proof. exact (MK_COMB (@lem3484047 B) (@lem3484046 A B f x)). Qed.
Lemma lem3484049 {A B : Type'} (f : type1374 A B) (x : A) : (term73 A B f x) = (term74 A B f x).
Proof. exact (eq_refl (term73 A B f x)). Qed.
Lemma lem3484050 {A B : Type'} (f : type1374 A B) (x : A) : ((term93 A B f x) = (term73 A B f x)) = ((term73 A B f x) = (term74 A B f x)).
Proof. exact (MK_COMB (@lem3484048 A B f x) (@lem3484049 A B f x)). Qed.
Lemma lem3484051 {A B : Type'} (f : type1374 A B) (x : A) : (term73 A B f x) = (term74 A B f x).
Proof. exact (EQ_MP (@lem3484050 A B f x) (@lem3484042 A B f x)). Qed.
Lemma lem3484052 {B : Type'} (y : B) : (@IN B y) = (@IN B y).
Proof. exact (eq_refl (@IN B y)). Qed.
Lemma lem3484053 {A B : Type'} (y : B) (f : type1374 A B) (x : A) : (term97 A B y f x) = (term98 A B y f x).
Proof. exact (MK_COMB (@lem3484052 B y) (@lem3484051 A B f x)). Qed.
Lemma lem3484054 {A : Type'} (x : A) (s : A -> Prop) : (term99 A x s) = (term99 A x s).
Proof. exact (eq_refl (term99 A x s)). Qed.
Lemma lem3484055 {A B : Type'} (s : A -> Prop) (y : B) (f : type1374 A B) (x : A) : (term100 A B s y f x) = (term101 A B s y f x).
Proof. exact (MK_COMB (@lem3484054 A x s) (@lem3484053 A B y f x)). Qed.
Lemma lem3484058 {A B : Type'} (s : A -> Prop) (y : B) (f : type1374 A B) : (term102 A B s y f) = (term103 A B s y f).
Proof. exact (fun_ext (fun x : A => @lem3484055 A B s y f x)). Qed.
Lemma lem3484059 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3484060 {A B : Type'} (s : A -> Prop) (y : B) (f : type1374 A B) : (term104 A B s y f) = (term105 A B s y f).
Proof. exact (MK_COMB (@lem3484059 A) (@lem3484058 A B s y f)). Qed.
Lemma lem3484065 {B : Type'} (GEN_PVAR_47 : B) : (@SETSPEC B GEN_PVAR_47) = (@SETSPEC B GEN_PVAR_47).
Proof. exact (eq_refl (@SETSPEC B GEN_PVAR_47)). Qed.
Lemma lem3484066 {A B : Type'} (GEN_PVAR_47 : B) (s : A -> Prop) (y : B) (f : type1374 A B) : (term106 A B GEN_PVAR_47 s y f) = (term107 A B GEN_PVAR_47 s y f).
Proof. exact (MK_COMB (@lem3484065 B GEN_PVAR_47) (@lem3484060 A B s y f)). Qed.
Lemma lem3484067 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3484068 {A B : Type'} (GEN_PVAR_47 : B) (s : A -> Prop) (f : type1374 A B) (y : B) : (term108 A B GEN_PVAR_47 s f y) = (term109 A B GEN_PVAR_47 s f y).
Proof. exact (MK_COMB (@lem3484066 A B GEN_PVAR_47 s y f) (@lem3484067 B y)). Qed.
Lemma lem3484069 {A B : Type'} (GEN_PVAR_47 : B) (s : A -> Prop) (f : type1374 A B) : (term110 A B GEN_PVAR_47 s f) = (term111 A B GEN_PVAR_47 s f).
Proof. exact (fun_ext (fun y : B => @lem3484068 A B GEN_PVAR_47 s f y)). Qed.
Lemma lem3484070 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3484071 {A B : Type'} (GEN_PVAR_47 : B) (s : A -> Prop) (f : type1374 A B) : (term112 A B GEN_PVAR_47 s f) = (term113 A B GEN_PVAR_47 s f).
Proof. exact (MK_COMB (@lem3484070 B) (@lem3484069 A B GEN_PVAR_47 s f)). Qed.
Lemma lem3484076 {A B : Type'} (s : A -> Prop) (f : type1374 A B) : (term114 A B s f) = (term115 A B s f).
Proof. exact (fun_ext (fun GEN_PVAR_47 : B => @lem3484071 A B GEN_PVAR_47 s f)). Qed.
Lemma lem3484077 {B : Type'} : (@GSPEC B) = (@GSPEC B).
Proof. exact (eq_refl (@GSPEC B)). Qed.
Lemma lem3484078 {A B : Type'} (s : A -> Prop) (f : type1374 A B) : (term90 A B s f) = (term116 A B s f).
Proof. exact (MK_COMB (@lem3484077 B) (@lem3484076 A B s f)). Qed.
Lemma lem3484079 {A B : Type'} (s : A -> Prop) (f : type1374 A B) : (term87 A B f s) = (term116 A B s f).
Proof. exact (TRANS (@lem3484028 A B s f) (@lem3484078 A B s f)). Qed.
Lemma lem3484080 {A B : Type'} (s : A -> Prop) (f : type1374 A B) : (term66 A B s f) = (term116 A B s f).
Proof. exact (TRANS (@lem3484024 A B f s) (@lem3484079 A B s f)). Qed.
Lemma lem3484081 {B : Type'} (x : B) : (@IN B x) = (@IN B x).
Proof. exact (eq_refl (@IN B x)). Qed.
Lemma lem3484082 {A B : Type'} (x : B) (s : A -> Prop) (f : type1374 A B) : (term117 A B x s f) = (term118 A B x s f).
Proof. exact (MK_COMB (@lem3484081 B x) (@lem3484080 A B s f)). Qed.
Lemma lem3484083 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3484084 {A B : Type'} (x : B) (s : A -> Prop) (f : type1374 A B) : (term119 A B x s f) = (term120 A B x s f).
Proof. exact (MK_COMB (@lem3484083) (@lem3484082 A B x s f)). Qed.
Lemma lem3484086 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term51 _89711 _89725 P f) = (term52 _89711 _89725 P f).
Proof. exact (EQ_MP (@lem3483968 _89711 _89725 P f) (@lem3483967 _89711 _89725 P f)). Qed.
Lemma lem3484087 {A B : Type'} (P : type475 A B) (f : type469 A B) : (term121 A B P f) = (term122 A B P f).
Proof. exact (@lem3484086 B (type1413 A B) P f). Qed.
Lemma lem3484088 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : (term123 A B f s) = (term124 A B f s).
Proof. exact (@lem3484087 A B (term125 A B s f) (term126 A B s)). Qed.
Lemma lem3484089 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) : (term127 A B s f g) = (term128 A B s g f).
Proof. exact (eq_refl (term127 A B s f g)). Qed.
Lemma lem3484090 {B : Type'} (GEN_PVAR_81 : B -> Prop) : (@SETSPEC (B -> Prop) GEN_PVAR_81) = (@SETSPEC (B -> Prop) GEN_PVAR_81).
Proof. exact (eq_refl (@SETSPEC (B -> Prop) GEN_PVAR_81)). Qed.
Lemma lem3484091 {A B : Type'} (GEN_PVAR_81 : B -> Prop) (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) : (term129 A B GEN_PVAR_81 s f g) = (term130 A B GEN_PVAR_81 s g f).
Proof. exact (MK_COMB (@lem3484090 B GEN_PVAR_81) (@lem3484089 A B s g f)). Qed.
Lemma lem3484092 {A B : Type'} (s : A -> Prop) (g : type1413 A B) : (term131 A B s g) = (term132 A B s g).
Proof. exact (eq_refl (term131 A B s g)). Qed.
Lemma lem3484093 {A B : Type'} (GEN_PVAR_81 : B -> Prop) (f : type1374 A B) (s : A -> Prop) (g : type1413 A B) : (term133 A B GEN_PVAR_81 f s g) = (term134 A B GEN_PVAR_81 f s g).
Proof. exact (MK_COMB (@lem3484091 A B GEN_PVAR_81 s g f) (@lem3484092 A B s g)). Qed.
Lemma lem3484094 {A B : Type'} (GEN_PVAR_81 : B -> Prop) (f : type1374 A B) (s : A -> Prop) : (term135 A B GEN_PVAR_81 f s) = (term136 A B GEN_PVAR_81 f s).
Proof. exact (fun_ext (fun g : type1413 A B => @lem3484093 A B GEN_PVAR_81 f s g)). Qed.
Lemma lem3484095 {A B : Type'} : (@ex (A -> B -> Prop)) = (@ex (A -> B -> Prop)).
Proof. exact (eq_refl (@ex (A -> B -> Prop))). Qed.
Lemma lem3484096 {A B : Type'} (GEN_PVAR_81 : B -> Prop) (f : type1374 A B) (s : A -> Prop) : (term137 A B GEN_PVAR_81 f s) = (term138 A B GEN_PVAR_81 f s).
Proof. exact (MK_COMB (@lem3484095 A B) (@lem3484094 A B GEN_PVAR_81 f s)). Qed.
Lemma lem3484097 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : (term139 A B f s) = (term140 A B f s).
Proof. exact (fun_ext (fun GEN_PVAR_81 : B -> Prop => @lem3484096 A B GEN_PVAR_81 f s)). Qed.
Lemma lem3484098 {B : Type'} : (@GSPEC (B -> Prop)) = (@GSPEC (B -> Prop)).
Proof. exact (eq_refl (@GSPEC (B -> Prop))). Qed.
Lemma lem3484099 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : (term141 A B f s) = (term142 A B f s).
Proof. exact (MK_COMB (@lem3484098 B) (@lem3484097 A B f s)). Qed.
Lemma lem3484100 {B : Type'} : (@INTERS B) = (@INTERS B).
Proof. exact (eq_refl (@INTERS B)). Qed.
Lemma lem3484101 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : (term123 A B f s) = (term67 A B f s).
Proof. exact (MK_COMB (@lem3484100 B) (@lem3484099 A B f s)). Qed.
Lemma lem3484102 {B : Type'} : (@eq (B -> Prop)) = (@eq (B -> Prop)).
Proof. exact (eq_refl (@eq (B -> Prop))). Qed.
Lemma lem3484103 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : (term143 A B f s) = (term144 A B f s).
Proof. exact (MK_COMB (@lem3484102 B) (@lem3484101 A B f s)). Qed.
Lemma lem3484104 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) : (term127 A B s f g) = (term128 A B s g f).
Proof. exact (eq_refl (term127 A B s f g)). Qed.
Lemma lem3484105 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3484106 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) : (term145 A B s f g) = (term146 A B s g f).
Proof. exact (MK_COMB (@lem3484105) (@lem3484104 A B s g f)). Qed.
Lemma lem3484107 {A B : Type'} (s : A -> Prop) (g : type1413 A B) : (term131 A B s g) = (term132 A B s g).
Proof. exact (eq_refl (term131 A B s g)). Qed.
Lemma lem3484108 {B : Type'} (a : B) : (@IN B a) = (@IN B a).
Proof. exact (eq_refl (@IN B a)). Qed.
Lemma lem3484109 {A B : Type'} (a : B) (s : A -> Prop) (g : type1413 A B) : (term147 A B a s g) = (term148 A B a s g).
Proof. exact (MK_COMB (@lem3484108 B a) (@lem3484107 A B s g)). Qed.
Lemma lem3484110 {A B : Type'} (f : type1374 A B) (a : B) (s : A -> Prop) (g : type1413 A B) : (term149 A B f a s g) = (term150 A B f a s g).
Proof. exact (MK_COMB (@lem3484106 A B s g f) (@lem3484109 A B a s g)). Qed.
Lemma lem3484111 {A B : Type'} (f : type1374 A B) (a : B) (s : A -> Prop) : (term151 A B f a s) = (term152 A B f a s).
Proof. exact (fun_ext (fun g : type1413 A B => @lem3484110 A B f a s g)). Qed.
Lemma lem3484112 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem3484113 {A B : Type'} (f : type1374 A B) (a : B) (s : A -> Prop) : (term153 A B f a s) = (term154 A B f a s).
Proof. exact (MK_COMB (@lem3484112 A B) (@lem3484111 A B f a s)). Qed.
Lemma lem3484114 {B : Type'} (GEN_PVAR_56 : B) : (@SETSPEC B GEN_PVAR_56) = (@SETSPEC B GEN_PVAR_56).
Proof. exact (eq_refl (@SETSPEC B GEN_PVAR_56)). Qed.
Lemma lem3484115 {A B : Type'} (GEN_PVAR_56 : B) (f : type1374 A B) (a : B) (s : A -> Prop) : (term155 A B GEN_PVAR_56 f a s) = (term156 A B GEN_PVAR_56 f a s).
Proof. exact (MK_COMB (@lem3484114 B GEN_PVAR_56) (@lem3484113 A B f a s)). Qed.
Lemma lem3484116 {B : Type'} (a : B) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3484117 {A B : Type'} (GEN_PVAR_56 : B) (f : type1374 A B) (s : A -> Prop) (a : B) : (term157 A B GEN_PVAR_56 f s a) = (term158 A B GEN_PVAR_56 f s a).
Proof. exact (MK_COMB (@lem3484115 A B GEN_PVAR_56 f a s) (@lem3484116 B a)). Qed.
Lemma lem3484118 {A B : Type'} (GEN_PVAR_56 : B) (f : type1374 A B) (s : A -> Prop) : (term159 A B GEN_PVAR_56 f s) = (term160 A B GEN_PVAR_56 f s).
Proof. exact (fun_ext (fun a : B => @lem3484117 A B GEN_PVAR_56 f s a)). Qed.
Lemma lem3484119 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3484120 {A B : Type'} (GEN_PVAR_56 : B) (f : type1374 A B) (s : A -> Prop) : (term161 A B GEN_PVAR_56 f s) = (term162 A B GEN_PVAR_56 f s).
Proof. exact (MK_COMB (@lem3484119 B) (@lem3484118 A B GEN_PVAR_56 f s)). Qed.
Lemma lem3484121 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : (term163 A B f s) = (term164 A B f s).
Proof. exact (fun_ext (fun GEN_PVAR_56 : B => @lem3484120 A B GEN_PVAR_56 f s)). Qed.
Lemma lem3484122 {B : Type'} : (@GSPEC B) = (@GSPEC B).
Proof. exact (eq_refl (@GSPEC B)). Qed.
Lemma lem3484123 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : (term124 A B f s) = (term165 A B f s).
Proof. exact (MK_COMB (@lem3484122 B) (@lem3484121 A B f s)). Qed.
Lemma lem3484124 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : ((term123 A B f s) = (term124 A B f s)) = ((term67 A B f s) = (term165 A B f s)).
Proof. exact (MK_COMB (@lem3484103 A B f s) (@lem3484123 A B f s)). Qed.
Lemma lem3484125 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : (term67 A B f s) = (term165 A B f s).
Proof. exact (EQ_MP (@lem3484124 A B f s) (@lem3484088 A B f s)). Qed.
Lemma lem3484143 {_88128 _88132 : Type'} (f : _88128 -> _88132) (s : _88128 -> Prop) : (term61 _88128 _88132 s f) = (@IMAGE _88128 _88132 f s).
Proof. exact (EQ_MP (@lem3483986 _88128 _88132 f s) (@lem3483985 _88128 _88132 f s)). Qed.
Lemma lem3484144 {A B : Type'} (f : type1413 A B) (s : A -> Prop) : (term69 A B s f) = (@IMAGE A (B -> Prop) f s).
Proof. exact (@lem3484143 A (B -> Prop) f s). Qed.
Lemma lem3484145 {A B : Type'} (g : type1413 A B) (s : A -> Prop) : (term69 A B s g) = (@IMAGE A (B -> Prop) g s).
Proof. exact (@lem3484144 A B g s). Qed.
Lemma lem3484146 {B : Type'} : (@UNIONS B) = (@UNIONS B).
Proof. exact (eq_refl (@UNIONS B)). Qed.
Lemma lem3484147 {A B : Type'} (g : type1413 A B) (s : A -> Prop) : (term132 A B s g) = (term88 A B g s).
Proof. exact (MK_COMB (@lem3484146 B) (@lem3484145 A B g s)). Qed.
Lemma lem3484149 {_89422 _89438 : Type'} (s : _89438 -> Prop) (f : type1470 _89422 _89438) : (term56 _89422 _89438 f s) = (term57 _89422 _89438 s f).
Proof. exact (EQ_MP (@lem3483974 _89422 _89438 s f) (@lem3483973 _89422 _89438 f s)). Qed.
Lemma lem3484150 {A B : Type'} (s : A -> Prop) (f : type1413 A B) : (term88 A B f s) = (term89 A B s f).
Proof. exact (@lem3484149 B A s f). Qed.
Lemma lem3484151 {A B : Type'} (s : A -> Prop) (g : type1413 A B) : (term88 A B g s) = (term89 A B s g).
Proof. exact (@lem3484150 A B s g). Qed.
Lemma lem3484162 {A B : Type'} (s : A -> Prop) (g : type1413 A B) : (term132 A B s g) = (term89 A B s g).
Proof. exact (TRANS (@lem3484147 A B g s) (@lem3484151 A B s g)). Qed.
Lemma lem3484163 {B : Type'} (a : B) : (@IN B a) = (@IN B a).
Proof. exact (eq_refl (@IN B a)). Qed.
Lemma lem3484164 {A B : Type'} (a : B) (s : A -> Prop) (g : type1413 A B) : (term148 A B a s g) = (term166 A B a s g).
Proof. exact (MK_COMB (@lem3484163 B a) (@lem3484162 A B s g)). Qed.
Lemma lem3484165 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) : (term146 A B s g f) = (term146 A B s g f).
Proof. exact (eq_refl (term146 A B s g f)). Qed.
Lemma lem3484166 {A B : Type'} (f : type1374 A B) (a : B) (s : A -> Prop) (g : type1413 A B) : (term150 A B f a s g) = (term167 A B f a s g).
Proof. exact (MK_COMB (@lem3484165 A B s g f) (@lem3484164 A B a s g)). Qed.
Lemma lem3484169 {A B : Type'} (f : type1374 A B) (a : B) (s : A -> Prop) : (term152 A B f a s) = (term168 A B f a s).
Proof. exact (fun_ext (fun g : type1413 A B => @lem3484166 A B f a s g)). Qed.
Lemma lem3484170 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem3484171 {A B : Type'} (f : type1374 A B) (a : B) (s : A -> Prop) : (term154 A B f a s) = (term169 A B f a s).
Proof. exact (MK_COMB (@lem3484170 A B) (@lem3484169 A B f a s)). Qed.
Lemma lem3484176 {B : Type'} (GEN_PVAR_56 : B) : (@SETSPEC B GEN_PVAR_56) = (@SETSPEC B GEN_PVAR_56).
Proof. exact (eq_refl (@SETSPEC B GEN_PVAR_56)). Qed.
Lemma lem3484177 {A B : Type'} (GEN_PVAR_56 : B) (f : type1374 A B) (a : B) (s : A -> Prop) : (term156 A B GEN_PVAR_56 f a s) = (term170 A B GEN_PVAR_56 f a s).
Proof. exact (MK_COMB (@lem3484176 B GEN_PVAR_56) (@lem3484171 A B f a s)). Qed.
Lemma lem3484178 {B : Type'} (a : B) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3484179 {A B : Type'} (GEN_PVAR_56 : B) (f : type1374 A B) (s : A -> Prop) (a : B) : (term158 A B GEN_PVAR_56 f s a) = (term171 A B GEN_PVAR_56 f s a).
Proof. exact (MK_COMB (@lem3484177 A B GEN_PVAR_56 f a s) (@lem3484178 B a)). Qed.
Lemma lem3484180 {A B : Type'} (GEN_PVAR_56 : B) (f : type1374 A B) (s : A -> Prop) : (term160 A B GEN_PVAR_56 f s) = (term172 A B GEN_PVAR_56 f s).
Proof. exact (fun_ext (fun a : B => @lem3484179 A B GEN_PVAR_56 f s a)). Qed.
Lemma lem3484181 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3484182 {A B : Type'} (GEN_PVAR_56 : B) (f : type1374 A B) (s : A -> Prop) : (term162 A B GEN_PVAR_56 f s) = (term173 A B GEN_PVAR_56 f s).
Proof. exact (MK_COMB (@lem3484181 B) (@lem3484180 A B GEN_PVAR_56 f s)). Qed.
Lemma lem3484187 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : (term164 A B f s) = (term174 A B f s).
Proof. exact (fun_ext (fun GEN_PVAR_56 : B => @lem3484182 A B GEN_PVAR_56 f s)). Qed.
Lemma lem3484188 {B : Type'} : (@GSPEC B) = (@GSPEC B).
Proof. exact (eq_refl (@GSPEC B)). Qed.
Lemma lem3484189 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : (term165 A B f s) = (term175 A B f s).
Proof. exact (MK_COMB (@lem3484188 B) (@lem3484187 A B f s)). Qed.
Lemma lem3484190 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : (term67 A B f s) = (term175 A B f s).
Proof. exact (TRANS (@lem3484125 A B f s) (@lem3484189 A B f s)). Qed.
Lemma lem3484191 {B : Type'} (x : B) : (@IN B x) = (@IN B x).
Proof. exact (eq_refl (@IN B x)). Qed.
Lemma lem3484192 {A B : Type'} (x : B) (f : type1374 A B) (s : A -> Prop) : (term176 A B x f s) = (term177 A B x f s).
Proof. exact (MK_COMB (@lem3484191 B x) (@lem3484190 A B f s)). Qed.
Lemma lem3484193 {A B : Type'} (x : B) (f : type1374 A B) (s : A -> Prop) : ((term117 A B x s f) = (term176 A B x f s)) = ((term118 A B x s f) = (term177 A B x f s)).
Proof. exact (MK_COMB (@lem3484084 A B x s f) (@lem3484192 A B x f s)). Qed.
Lemma lem3484196 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : (term178 A B f s) = (term179 A B f s).
Proof. exact (fun_ext (fun x : B => @lem3484193 A B x f s)). Qed.
Lemma lem3484197 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3484198 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : (term68 A B f s) = (term180 A B f s).
Proof. exact (MK_COMB (@lem3484197 B) (@lem3484196 A B f s)). Qed.
Lemma lem3484203 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : (term180 A B f s) = (term68 A B f s).
Proof. exact (SYM (@lem3484198 A B f s)). Qed.
Lemma lem3484211 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term41 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3483933 _83095 p x) (@lem3483932 _83095 p x)). Qed.
Lemma lem3484212 {B : Type'} (p : B -> Prop) (x : B) : (term41 B x p) = (p x).
Proof. exact (@lem3484211 B p x). Qed.
Lemma lem3484213 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) : (term181 A B x s f) = (term182 A B s f x).
Proof. exact (@lem3484212 B (term183 A B s f) x). Qed.
Lemma lem3484214 {A B : Type'} (s : A -> Prop) (y : B) (f : type1374 A B) : (term182 A B s f y) = (term105 A B s y f).
Proof. exact (eq_refl (term182 A B s f y)). Qed.
Lemma lem3484215 {B : Type'} (GEN_PVAR_47 : B) : (@SETSPEC B GEN_PVAR_47) = (@SETSPEC B GEN_PVAR_47).
Proof. exact (eq_refl (@SETSPEC B GEN_PVAR_47)). Qed.
Lemma lem3484216 {A B : Type'} (GEN_PVAR_47 : B) (s : A -> Prop) (y : B) (f : type1374 A B) : (term184 A B GEN_PVAR_47 s f y) = (term107 A B GEN_PVAR_47 s y f).
Proof. exact (MK_COMB (@lem3484215 B GEN_PVAR_47) (@lem3484214 A B s y f)). Qed.
Lemma lem3484217 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3484218 {A B : Type'} (GEN_PVAR_47 : B) (s : A -> Prop) (f : type1374 A B) (y : B) : (term185 A B GEN_PVAR_47 s f y) = (term109 A B GEN_PVAR_47 s f y).
Proof. exact (MK_COMB (@lem3484216 A B GEN_PVAR_47 s y f) (@lem3484217 B y)). Qed.
Lemma lem3484219 {A B : Type'} (GEN_PVAR_47 : B) (s : A -> Prop) (f : type1374 A B) : (term186 A B GEN_PVAR_47 s f) = (term111 A B GEN_PVAR_47 s f).
Proof. exact (fun_ext (fun y : B => @lem3484218 A B GEN_PVAR_47 s f y)). Qed.
Lemma lem3484220 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3484221 {A B : Type'} (GEN_PVAR_47 : B) (s : A -> Prop) (f : type1374 A B) : (term187 A B GEN_PVAR_47 s f) = (term113 A B GEN_PVAR_47 s f).
Proof. exact (MK_COMB (@lem3484220 B) (@lem3484219 A B GEN_PVAR_47 s f)). Qed.
Lemma lem3484222 {A B : Type'} (s : A -> Prop) (f : type1374 A B) : (term188 A B s f) = (term115 A B s f).
Proof. exact (fun_ext (fun GEN_PVAR_47 : B => @lem3484221 A B GEN_PVAR_47 s f)). Qed.
Lemma lem3484223 {B : Type'} : (@GSPEC B) = (@GSPEC B).
Proof. exact (eq_refl (@GSPEC B)). Qed.
Lemma lem3484224 {A B : Type'} (s : A -> Prop) (f : type1374 A B) : (term189 A B s f) = (term116 A B s f).
Proof. exact (MK_COMB (@lem3484223 B) (@lem3484222 A B s f)). Qed.
Lemma lem3484225 {B : Type'} (x : B) : (@IN B x) = (@IN B x).
Proof. exact (eq_refl (@IN B x)). Qed.
Lemma lem3484226 {A B : Type'} (x : B) (s : A -> Prop) (f : type1374 A B) : (term181 A B x s f) = (term118 A B x s f).
Proof. exact (MK_COMB (@lem3484225 B x) (@lem3484224 A B s f)). Qed.
Lemma lem3484227 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3484228 {A B : Type'} (x : B) (s : A -> Prop) (f : type1374 A B) : (term190 A B x s f) = (term120 A B x s f).
Proof. exact (MK_COMB (@lem3484227) (@lem3484226 A B x s f)). Qed.
Lemma lem3484229 {A B : Type'} (s : A -> Prop) (x : B) (f : type1374 A B) : (term182 A B s f x) = (term105 A B s x f).
Proof. exact (eq_refl (term182 A B s f x)). Qed.
Lemma lem3484230 {A B : Type'} (s : A -> Prop) (x : B) (f : type1374 A B) : ((term181 A B x s f) = (term182 A B s f x)) = ((term118 A B x s f) = (term105 A B s x f)).
Proof. exact (MK_COMB (@lem3484228 A B x s f) (@lem3484229 A B s x f)). Qed.
Lemma lem3484231 {A B : Type'} (s : A -> Prop) (x : B) (f : type1374 A B) : (term118 A B x s f) = (term105 A B s x f).
Proof. exact (EQ_MP (@lem3484230 A B s x f) (@lem3484213 A B s f x)). Qed.
Lemma lem3484239 {A : Type'} (s : type686 A) (x : A) : (term45 A x s) = (term46 A s x).
Proof. exact (EQ_MP (@lem3483946 A s x) (@lem3483945 A s x)). Qed.
Lemma lem3484240 {B : Type'} (s : type686 B) (x : B) : (term45 B x s) = (term46 B s x).
Proof. exact (@lem3484239 B s x). Qed.
Lemma lem3484241 {A B : Type'} (f : type1374 A B) (x : A) (x' : B) : (term98 A B x' f x) = (term191 A B f x x').
Proof. exact (@lem3484240 B (f x) x'). Qed.
Lemma lem3484248 {A : Type'} (x : A) (s : A -> Prop) : (term99 A x s) = (term99 A x s).
Proof. exact (eq_refl (term99 A x s)). Qed.
Lemma lem3484249 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : A) (x' : B) : (term101 A B s x' f x) = (term192 A B s f x x').
Proof. exact (MK_COMB (@lem3484248 A x s) (@lem3484241 A B f x x')). Qed.
Lemma lem3484252 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) : (term103 A B s x f) = (term193 A B s f x).
Proof. exact (fun_ext (fun x' : A => @lem3484249 A B s f x' x)). Qed.
Lemma lem3484253 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3484254 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) : (term105 A B s x f) = (term194 A B s f x).
Proof. exact (MK_COMB (@lem3484253 A) (@lem3484252 A B s f x)). Qed.
Lemma lem3484259 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) : (term118 A B x s f) = (term194 A B s f x).
Proof. exact (TRANS (@lem3484231 A B s x f) (@lem3484254 A B s f x)). Qed.
Lemma lem3484260 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3484261 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) : (term120 A B x s f) = (term195 A B s f x).
Proof. exact (MK_COMB (@lem3484260) (@lem3484259 A B s f x)). Qed.
Lemma lem3484263 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term41 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3483933 _83095 p x) (@lem3483932 _83095 p x)). Qed.
Lemma lem3484264 {B : Type'} (p : B -> Prop) (x : B) : (term41 B x p) = (p x).
Proof. exact (@lem3484263 B p x). Qed.
Lemma lem3484265 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term196 A B x f s) = (term197 A B f s x).
Proof. exact (@lem3484264 B (term198 A B f s) x). Qed.
Lemma lem3484266 {A B : Type'} (f : type1374 A B) (a : B) (s : A -> Prop) : (term197 A B f s a) = (term169 A B f a s).
Proof. exact (eq_refl (term197 A B f s a)). Qed.
Lemma lem3484267 {B : Type'} (GEN_PVAR_56 : B) : (@SETSPEC B GEN_PVAR_56) = (@SETSPEC B GEN_PVAR_56).
Proof. exact (eq_refl (@SETSPEC B GEN_PVAR_56)). Qed.
Lemma lem3484268 {A B : Type'} (GEN_PVAR_56 : B) (f : type1374 A B) (a : B) (s : A -> Prop) : (term199 A B GEN_PVAR_56 f s a) = (term170 A B GEN_PVAR_56 f a s).
Proof. exact (MK_COMB (@lem3484267 B GEN_PVAR_56) (@lem3484266 A B f a s)). Qed.
Lemma lem3484269 {B : Type'} (a : B) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3484270 {A B : Type'} (GEN_PVAR_56 : B) (f : type1374 A B) (s : A -> Prop) (a : B) : (term200 A B GEN_PVAR_56 f s a) = (term171 A B GEN_PVAR_56 f s a).
Proof. exact (MK_COMB (@lem3484268 A B GEN_PVAR_56 f a s) (@lem3484269 B a)). Qed.
Lemma lem3484271 {A B : Type'} (GEN_PVAR_56 : B) (f : type1374 A B) (s : A -> Prop) : (term201 A B GEN_PVAR_56 f s) = (term172 A B GEN_PVAR_56 f s).
Proof. exact (fun_ext (fun a : B => @lem3484270 A B GEN_PVAR_56 f s a)). Qed.
Lemma lem3484272 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3484273 {A B : Type'} (GEN_PVAR_56 : B) (f : type1374 A B) (s : A -> Prop) : (term202 A B GEN_PVAR_56 f s) = (term173 A B GEN_PVAR_56 f s).
Proof. exact (MK_COMB (@lem3484272 B) (@lem3484271 A B GEN_PVAR_56 f s)). Qed.
Lemma lem3484274 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : (term203 A B f s) = (term174 A B f s).
Proof. exact (fun_ext (fun GEN_PVAR_56 : B => @lem3484273 A B GEN_PVAR_56 f s)). Qed.
Lemma lem3484275 {B : Type'} : (@GSPEC B) = (@GSPEC B).
Proof. exact (eq_refl (@GSPEC B)). Qed.
Lemma lem3484276 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : (term204 A B f s) = (term175 A B f s).
Proof. exact (MK_COMB (@lem3484275 B) (@lem3484274 A B f s)). Qed.
Lemma lem3484277 {B : Type'} (x : B) : (@IN B x) = (@IN B x).
Proof. exact (eq_refl (@IN B x)). Qed.
Lemma lem3484278 {A B : Type'} (x : B) (f : type1374 A B) (s : A -> Prop) : (term196 A B x f s) = (term177 A B x f s).
Proof. exact (MK_COMB (@lem3484277 B x) (@lem3484276 A B f s)). Qed.
Lemma lem3484279 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3484280 {A B : Type'} (x : B) (f : type1374 A B) (s : A -> Prop) : (term205 A B x f s) = (term206 A B x f s).
Proof. exact (MK_COMB (@lem3484279) (@lem3484278 A B x f s)). Qed.
Lemma lem3484281 {A B : Type'} (f : type1374 A B) (x : B) (s : A -> Prop) : (term197 A B f s x) = (term169 A B f x s).
Proof. exact (eq_refl (term197 A B f s x)). Qed.
Lemma lem3484282 {A B : Type'} (f : type1374 A B) (x : B) (s : A -> Prop) : ((term196 A B x f s) = (term197 A B f s x)) = ((term177 A B x f s) = (term169 A B f x s)).
Proof. exact (MK_COMB (@lem3484280 A B x f s) (@lem3484281 A B f x s)). Qed.
Lemma lem3484283 {A B : Type'} (f : type1374 A B) (x : B) (s : A -> Prop) : (term177 A B x f s) = (term169 A B f x s).
Proof. exact (EQ_MP (@lem3484282 A B f x s) (@lem3484265 A B f s x)). Qed.
Lemma lem3484297 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term41 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3483933 _83095 p x) (@lem3483932 _83095 p x)). Qed.
Lemma lem3484298 {B : Type'} (p : B -> Prop) (x : B) : (term41 B x p) = (p x).
Proof. exact (@lem3484297 B p x). Qed.
Lemma lem3484299 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (x : B) : (term207 A B x s g) = (term208 A B s g x).
Proof. exact (@lem3484298 B (term209 A B s g) x). Qed.
Lemma lem3484300 {A B : Type'} (s : A -> Prop) (y : B) (g : type1413 A B) : (term208 A B s g y) = (term210 A B s y g).
Proof. exact (eq_refl (term208 A B s g y)). Qed.
Lemma lem3484301 {B : Type'} (GEN_PVAR_47 : B) : (@SETSPEC B GEN_PVAR_47) = (@SETSPEC B GEN_PVAR_47).
Proof. exact (eq_refl (@SETSPEC B GEN_PVAR_47)). Qed.
Lemma lem3484302 {A B : Type'} (GEN_PVAR_47 : B) (s : A -> Prop) (y : B) (g : type1413 A B) : (term211 A B GEN_PVAR_47 s g y) = (term212 A B GEN_PVAR_47 s y g).
Proof. exact (MK_COMB (@lem3484301 B GEN_PVAR_47) (@lem3484300 A B s y g)). Qed.
Lemma lem3484303 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3484304 {A B : Type'} (GEN_PVAR_47 : B) (s : A -> Prop) (g : type1413 A B) (y : B) : (term213 A B GEN_PVAR_47 s g y) = (term214 A B GEN_PVAR_47 s g y).
Proof. exact (MK_COMB (@lem3484302 A B GEN_PVAR_47 s y g) (@lem3484303 B y)). Qed.
Lemma lem3484305 {A B : Type'} (GEN_PVAR_47 : B) (s : A -> Prop) (g : type1413 A B) : (term215 A B GEN_PVAR_47 s g) = (term216 A B GEN_PVAR_47 s g).
Proof. exact (fun_ext (fun y : B => @lem3484304 A B GEN_PVAR_47 s g y)). Qed.
Lemma lem3484306 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3484307 {A B : Type'} (GEN_PVAR_47 : B) (s : A -> Prop) (g : type1413 A B) : (term217 A B GEN_PVAR_47 s g) = (term218 A B GEN_PVAR_47 s g).
Proof. exact (MK_COMB (@lem3484306 B) (@lem3484305 A B GEN_PVAR_47 s g)). Qed.
Lemma lem3484308 {A B : Type'} (s : A -> Prop) (g : type1413 A B) : (term219 A B s g) = (term220 A B s g).
Proof. exact (fun_ext (fun GEN_PVAR_47 : B => @lem3484307 A B GEN_PVAR_47 s g)). Qed.
Lemma lem3484309 {B : Type'} : (@GSPEC B) = (@GSPEC B).
Proof. exact (eq_refl (@GSPEC B)). Qed.
Lemma lem3484310 {A B : Type'} (s : A -> Prop) (g : type1413 A B) : (term221 A B s g) = (term89 A B s g).
Proof. exact (MK_COMB (@lem3484309 B) (@lem3484308 A B s g)). Qed.
Lemma lem3484311 {B : Type'} (x : B) : (@IN B x) = (@IN B x).
Proof. exact (eq_refl (@IN B x)). Qed.
Lemma lem3484312 {A B : Type'} (x : B) (s : A -> Prop) (g : type1413 A B) : (term207 A B x s g) = (term166 A B x s g).
Proof. exact (MK_COMB (@lem3484311 B x) (@lem3484310 A B s g)). Qed.
Lemma lem3484313 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3484314 {A B : Type'} (x : B) (s : A -> Prop) (g : type1413 A B) : (term222 A B x s g) = (term223 A B x s g).
Proof. exact (MK_COMB (@lem3484313) (@lem3484312 A B x s g)). Qed.
Lemma lem3484315 {A B : Type'} (s : A -> Prop) (x : B) (g : type1413 A B) : (term208 A B s g x) = (term210 A B s x g).
Proof. exact (eq_refl (term208 A B s g x)). Qed.
Lemma lem3484316 {A B : Type'} (s : A -> Prop) (x : B) (g : type1413 A B) : ((term207 A B x s g) = (term208 A B s g x)) = ((term166 A B x s g) = (term210 A B s x g)).
Proof. exact (MK_COMB (@lem3484314 A B x s g) (@lem3484315 A B s x g)). Qed.
Lemma lem3484317 {A B : Type'} (s : A -> Prop) (x : B) (g : type1413 A B) : (term166 A B x s g) = (term210 A B s x g).
Proof. exact (EQ_MP (@lem3484316 A B s x g) (@lem3484299 A B s g x)). Qed.
Lemma lem3484324 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) : (term146 A B s g f) = (term146 A B s g f).
Proof. exact (eq_refl (term146 A B s g f)). Qed.
Lemma lem3484325 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) : (term167 A B f x s g) = (term224 A B f s x g).
Proof. exact (MK_COMB (@lem3484324 A B s g f) (@lem3484317 A B s x g)). Qed.
Lemma lem3484328 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term168 A B f x s) = (term225 A B f s x).
Proof. exact (fun_ext (fun g : type1413 A B => @lem3484325 A B f s x g)). Qed.
Lemma lem3484329 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem3484330 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term169 A B f x s) = (term226 A B f s x).
Proof. exact (MK_COMB (@lem3484329 A B) (@lem3484328 A B f s x)). Qed.
Lemma lem3484335 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term177 A B x f s) = (term226 A B f s x).
Proof. exact (TRANS (@lem3484283 A B f x s) (@lem3484330 A B f s x)). Qed.
Lemma lem3484336 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : ((term118 A B x s f) = (term177 A B x f s)) = ((term194 A B s f x) = (term226 A B f s x)).
Proof. exact (MK_COMB (@lem3484261 A B s f x) (@lem3484335 A B f s x)). Qed.
Lemma lem3484339 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : (term179 A B f s) = (term227 A B f s).
Proof. exact (fun_ext (fun x : B => @lem3484336 A B f s x)). Qed.
Lemma lem3484340 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3484341 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : (term180 A B f s) = (term228 A B f s).
Proof. exact (MK_COMB (@lem3484340 B) (@lem3484339 A B f s)). Qed.
Lemma lem3484346 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : (term228 A B f s) = (term180 A B f s).
Proof. exact (SYM (@lem3484341 A B f s)). Qed.
Lemma lem3484350 (p : Prop) (q : Prop) : (p = q) = ((~ p) = (~ q)).
Proof. exact (or_elim (@lem3483804 p) (fun h0 : p = True => @lem3483900 q p h0) (fun h0 : p = False => @lem3483899 q p h0)). Qed.
Lemma lem3484351 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : ((term194 A B s f x) = (term226 A B f s x)) = ((term229 A B s f x) = (term230 A B f s x)).
Proof. exact (@lem3484350 (term194 A B s f x) (term226 A B f s x)). Qed.
Lemma lem3484352 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : ((term229 A B s f x) = (term230 A B f s x)) = ((term194 A B s f x) = (term226 A B f s x)).
Proof. exact (SYM (@lem3484351 A B f s x)). Qed.
Lemma lem3484356 {A : Type'} (P : A -> Prop) : (term13 A P) = (term14 A P).
Proof. exact (EQ_MP (@lem3483783 A P) (@lem3483782 A P)). Qed.
Lemma lem3484357 {A : Type'} (P : A -> Prop) : (term13 A P) = (term14 A P).
Proof. exact (@lem3484356 A P). Qed.
Lemma lem3484358 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) : (term231 A B s f x) = (term232 A B s f x).
Proof. exact (@lem3484357 A (term193 A B s f x)). Qed.
Lemma lem3484359 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : A) (x' : B) : (term233 A B s f x' x) = (term192 A B s f x x').
Proof. exact (eq_refl (term233 A B s f x' x)). Qed.
Lemma lem3484360 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) : (term234 A B s f x) = (term193 A B s f x).
Proof. exact (fun_ext (fun x' : A => @lem3484359 A B s f x' x)). Qed.
Lemma lem3484361 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3484362 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) : (term235 A B s f x) = (term194 A B s f x).
Proof. exact (MK_COMB (@lem3484361 A) (@lem3484360 A B s f x)). Qed.
Lemma lem3484363 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3484364 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) : (term231 A B s f x) = (term229 A B s f x).
Proof. exact (MK_COMB (@lem3484363) (@lem3484362 A B s f x)). Qed.
Lemma lem3484365 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3484366 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) : (term236 A B s f x) = (term237 A B s f x).
Proof. exact (MK_COMB (@lem3484365) (@lem3484364 A B s f x)). Qed.
Lemma lem3484367 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : A) (x' : B) : (term233 A B s f x' x) = (term192 A B s f x x').
Proof. exact (eq_refl (term233 A B s f x' x)). Qed.
Lemma lem3484368 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3484369 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : A) (x' : B) : (term238 A B s f x' x) = (term239 A B s f x x').
Proof. exact (MK_COMB (@lem3484368) (@lem3484367 A B s f x x')). Qed.
Lemma lem3484370 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) : (term240 A B s f x) = (term241 A B s f x).
Proof. exact (fun_ext (fun x' : A => @lem3484369 A B s f x' x)). Qed.
Lemma lem3484371 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3484372 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) : (term232 A B s f x) = (term242 A B s f x).
Proof. exact (MK_COMB (@lem3484371 A) (@lem3484370 A B s f x)). Qed.
Lemma lem3484373 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) : ((term231 A B s f x) = (term232 A B s f x)) = ((term229 A B s f x) = (term242 A B s f x)).
Proof. exact (MK_COMB (@lem3484366 A B s f x) (@lem3484372 A B s f x)). Qed.
Lemma lem3484374 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) : (term229 A B s f x) = (term242 A B s f x).
Proof. exact (EQ_MP (@lem3484373 A B s f x) (@lem3484358 A B s f x)). Qed.
Lemma lem3484387 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3484388 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) : (term237 A B s f x) = (term243 A B s f x).
Proof. exact (MK_COMB (@lem3484387) (@lem3484374 A B s f x)). Qed.
Lemma lem3484390 {A : Type'} (P : A -> Prop) : (term21 A P) = (term22 A P).
Proof. exact (EQ_MP (@lem3483792 A P) (@lem3483791 A P)). Qed.
Lemma lem3484391 {A B : Type'} (P : type475 A B) : (term244 A B P) = (term245 A B P).
Proof. exact (@lem3484390 (type1413 A B) P). Qed.
Lemma lem3484392 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term246 A B f s x) = (term247 A B f s x).
Proof. exact (@lem3484391 A B (term225 A B f s x)). Qed.
Lemma lem3484393 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) : (term248 A B f s x g) = (term224 A B f s x g).
Proof. exact (eq_refl (term248 A B f s x g)). Qed.
Lemma lem3484394 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term249 A B f s x) = (term225 A B f s x).
Proof. exact (fun_ext (fun g : type1413 A B => @lem3484393 A B f s x g)). Qed.
Lemma lem3484395 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem3484396 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term250 A B f s x) = (term226 A B f s x).
Proof. exact (MK_COMB (@lem3484395 A B) (@lem3484394 A B f s x)). Qed.
Lemma lem3484397 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3484398 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term246 A B f s x) = (term230 A B f s x).
Proof. exact (MK_COMB (@lem3484397) (@lem3484396 A B f s x)). Qed.
Lemma lem3484399 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3484400 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term251 A B f s x) = (term252 A B f s x).
Proof. exact (MK_COMB (@lem3484399) (@lem3484398 A B f s x)). Qed.
Lemma lem3484401 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) : (term248 A B f s x g) = (term224 A B f s x g).
Proof. exact (eq_refl (term248 A B f s x g)). Qed.
Lemma lem3484402 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3484403 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) : (term253 A B f s x g) = (term254 A B f s x g).
Proof. exact (MK_COMB (@lem3484402) (@lem3484401 A B f s x g)). Qed.
Lemma lem3484404 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term255 A B f s x) = (term256 A B f s x).
Proof. exact (fun_ext (fun g : type1413 A B => @lem3484403 A B f s x g)). Qed.
Lemma lem3484405 {A B : Type'} : (@ex (A -> B -> Prop)) = (@ex (A -> B -> Prop)).
Proof. exact (eq_refl (@ex (A -> B -> Prop))). Qed.
Lemma lem3484406 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term247 A B f s x) = (term257 A B f s x).
Proof. exact (MK_COMB (@lem3484405 A B) (@lem3484404 A B f s x)). Qed.
Lemma lem3484407 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : ((term246 A B f s x) = (term247 A B f s x)) = ((term230 A B f s x) = (term257 A B f s x)).
Proof. exact (MK_COMB (@lem3484400 A B f s x) (@lem3484406 A B f s x)). Qed.
Lemma lem3484408 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term230 A B f s x) = (term257 A B f s x).
Proof. exact (EQ_MP (@lem3484407 A B f s x) (@lem3484392 A B f s x)). Qed.
Lemma lem3484414 (t1 : Prop) (t2 : Prop) : (term18 t1 t2) = (term19 t1 t2).
Proof. exact (EQ_MP (@lem3483789 t1 t2) (@lem3483788 t1 t2)). Qed.
Lemma lem3484415 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) : (term254 A B f s x g) = (term258 A B f s x g).
Proof. exact (@lem3484414 (term128 A B s g f) (term210 A B s x g)). Qed.
Lemma lem3484425 {A : Type'} (P : A -> Prop) : (term13 A P) = (term14 A P).
Proof. exact (EQ_MP (@lem3483783 A P) (@lem3483782 A P)). Qed.
Lemma lem3484426 {A : Type'} (P : A -> Prop) : (term13 A P) = (term14 A P).
Proof. exact (@lem3484425 A P). Qed.
Lemma lem3484427 {A B : Type'} (s : A -> Prop) (x : B) (g : type1413 A B) : (term259 A B s x g) = (term260 A B s x g).
Proof. exact (@lem3484426 A (term261 A B s x g)). Qed.
Lemma lem3484428 {A B : Type'} (s : A -> Prop) (x : B) (g : type1413 A B) (x' : A) : (term262 A B s x g x') = (term263 A B s x g x').
Proof. exact (eq_refl (term262 A B s x g x')). Qed.
Lemma lem3484429 {A B : Type'} (s : A -> Prop) (x : B) (g : type1413 A B) : (term264 A B s x g) = (term261 A B s x g).
Proof. exact (fun_ext (fun x' : A => @lem3484428 A B s x g x')). Qed.
Lemma lem3484430 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3484431 {A B : Type'} (s : A -> Prop) (x : B) (g : type1413 A B) : (term265 A B s x g) = (term210 A B s x g).
Proof. exact (MK_COMB (@lem3484430 A) (@lem3484429 A B s x g)). Qed.
Lemma lem3484432 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3484433 {A B : Type'} (s : A -> Prop) (x : B) (g : type1413 A B) : (term259 A B s x g) = (term266 A B s x g).
Proof. exact (MK_COMB (@lem3484432) (@lem3484431 A B s x g)). Qed.
Lemma lem3484434 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3484435 {A B : Type'} (s : A -> Prop) (x : B) (g : type1413 A B) : (term267 A B s x g) = (term268 A B s x g).
Proof. exact (MK_COMB (@lem3484434) (@lem3484433 A B s x g)). Qed.
Lemma lem3484436 {A B : Type'} (s : A -> Prop) (x : B) (g : type1413 A B) (x' : A) : (term262 A B s x g x') = (term263 A B s x g x').
Proof. exact (eq_refl (term262 A B s x g x')). Qed.
Lemma lem3484437 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3484438 {A B : Type'} (s : A -> Prop) (x : B) (g : type1413 A B) (x' : A) : (term269 A B s x g x') = (term270 A B s x g x').
Proof. exact (MK_COMB (@lem3484437) (@lem3484436 A B s x g x')). Qed.
Lemma lem3484439 {A B : Type'} (s : A -> Prop) (x : B) (g : type1413 A B) : (term271 A B s x g) = (term272 A B s x g).
Proof. exact (fun_ext (fun x' : A => @lem3484438 A B s x g x')). Qed.
Lemma lem3484440 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3484441 {A B : Type'} (s : A -> Prop) (x : B) (g : type1413 A B) : (term260 A B s x g) = (term273 A B s x g).
Proof. exact (MK_COMB (@lem3484440 A) (@lem3484439 A B s x g)). Qed.
Lemma lem3484442 {A B : Type'} (s : A -> Prop) (x : B) (g : type1413 A B) : ((term259 A B s x g) = (term260 A B s x g)) = ((term266 A B s x g) = (term273 A B s x g)).
Proof. exact (MK_COMB (@lem3484435 A B s x g) (@lem3484441 A B s x g)). Qed.
Lemma lem3484443 {A B : Type'} (s : A -> Prop) (x : B) (g : type1413 A B) : (term266 A B s x g) = (term273 A B s x g).
Proof. exact (EQ_MP (@lem3484442 A B s x g) (@lem3484427 A B s x g)). Qed.
Lemma lem3484450 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) : (term274 A B s g f) = (term274 A B s g f).
Proof. exact (eq_refl (term274 A B s g f)). Qed.
Lemma lem3484451 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) : (term258 A B f s x g) = (term275 A B f s x g).
Proof. exact (MK_COMB (@lem3484450 A B s g f) (@lem3484443 A B s x g)). Qed.
Lemma lem3484454 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) : (term254 A B f s x g) = (term275 A B f s x g).
Proof. exact (TRANS (@lem3484415 A B f s x g) (@lem3484451 A B f s x g)). Qed.
Lemma lem3484455 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term256 A B f s x) = (term276 A B f s x).
Proof. exact (fun_ext (fun g : type1413 A B => @lem3484454 A B f s x g)). Qed.
Lemma lem3484456 {A B : Type'} : (@ex (A -> B -> Prop)) = (@ex (A -> B -> Prop)).
Proof. exact (eq_refl (@ex (A -> B -> Prop))). Qed.
Lemma lem3484457 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term257 A B f s x) = (term277 A B f s x).
Proof. exact (MK_COMB (@lem3484456 A B) (@lem3484455 A B f s x)). Qed.
Lemma lem3484462 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term230 A B f s x) = (term277 A B f s x).
Proof. exact (TRANS (@lem3484408 A B f s x) (@lem3484457 A B f s x)). Qed.
Lemma lem3484463 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : ((term229 A B s f x) = (term230 A B f s x)) = ((term242 A B s f x) = (term277 A B f s x)).
Proof. exact (MK_COMB (@lem3484388 A B s f x) (@lem3484462 A B f s x)). Qed.
Lemma lem3484466 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : ((term242 A B s f x) = (term277 A B f s x)) = ((term229 A B s f x) = (term230 A B f s x)).
Proof. exact (SYM (@lem3484463 A B f s x)). Qed.
Lemma lem3484486 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term10 A P Q) = (term11 A P Q).
Proof. exact (EQ_MP (@lem3483780 A P Q) (@lem3483779 A P Q)). Qed.
Lemma lem3484487 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term10 A P Q) = (term11 A P Q).
Proof. exact (@lem3484486 A P Q). Qed.
Lemma lem3484488 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) : (term278 A B f s x g) = (term279 A B f s x g).
Proof. exact (@lem3484487 A (term280 A B s g f) (term272 A B s x g)). Qed.
Lemma lem3484489 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) (x : A) : (term281 A B s g f x) = (term282 A B s g f x).
Proof. exact (eq_refl (term281 A B s g f x)). Qed.
Lemma lem3484490 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) : (term283 A B s g f) = (term280 A B s g f).
Proof. exact (fun_ext (fun x : A => @lem3484489 A B s g f x)). Qed.
Lemma lem3484491 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3484492 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) : (term284 A B s g f) = (term128 A B s g f).
Proof. exact (MK_COMB (@lem3484491 A) (@lem3484490 A B s g f)). Qed.
Lemma lem3484493 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3484494 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) : (term285 A B s g f) = (term274 A B s g f).
Proof. exact (MK_COMB (@lem3484493) (@lem3484492 A B s g f)). Qed.
Lemma lem3484495 {A B : Type'} (s : A -> Prop) (x : B) (g : type1413 A B) (x' : A) : (term286 A B s x g x') = (term270 A B s x g x').
Proof. exact (eq_refl (term286 A B s x g x')). Qed.
Lemma lem3484496 {A B : Type'} (s : A -> Prop) (x : B) (g : type1413 A B) : (term287 A B s x g) = (term272 A B s x g).
Proof. exact (fun_ext (fun x' : A => @lem3484495 A B s x g x')). Qed.
Lemma lem3484497 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3484498 {A B : Type'} (s : A -> Prop) (x : B) (g : type1413 A B) : (term288 A B s x g) = (term273 A B s x g).
Proof. exact (MK_COMB (@lem3484497 A) (@lem3484496 A B s x g)). Qed.
Lemma lem3484499 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) : (term278 A B f s x g) = (term275 A B f s x g).
Proof. exact (MK_COMB (@lem3484494 A B s g f) (@lem3484498 A B s x g)). Qed.
Lemma lem3484500 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3484501 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) : (term289 A B f s x g) = (term290 A B f s x g).
Proof. exact (MK_COMB (@lem3484500) (@lem3484499 A B f s x g)). Qed.
Lemma lem3484502 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) (x : A) : (term281 A B s g f x) = (term282 A B s g f x).
Proof. exact (eq_refl (term281 A B s g f x)). Qed.
Lemma lem3484503 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3484504 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) (x : A) : (term291 A B s g f x) = (term292 A B s g f x).
Proof. exact (MK_COMB (@lem3484503) (@lem3484502 A B s g f x)). Qed.
Lemma lem3484505 {A B : Type'} (s : A -> Prop) (x : B) (g : type1413 A B) (x' : A) : (term286 A B s x g x') = (term270 A B s x g x').
Proof. exact (eq_refl (term286 A B s x g x')). Qed.
Lemma lem3484506 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (x' : A) : (term293 A B f s x g x') = (term294 A B f s x g x').
Proof. exact (MK_COMB (@lem3484504 A B s g f x') (@lem3484505 A B s x g x')). Qed.
Lemma lem3484507 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) : (term295 A B f s x g) = (term296 A B f s x g).
Proof. exact (fun_ext (fun x' : A => @lem3484506 A B f s x g x')). Qed.
Lemma lem3484508 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3484509 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) : (term279 A B f s x g) = (term297 A B f s x g).
Proof. exact (MK_COMB (@lem3484508 A) (@lem3484507 A B f s x g)). Qed.
Lemma lem3484510 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) : ((term278 A B f s x g) = (term279 A B f s x g)) = ((term275 A B f s x g) = (term297 A B f s x g)).
Proof. exact (MK_COMB (@lem3484501 A B f s x g) (@lem3484509 A B f s x g)). Qed.
Lemma lem3484511 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) : (term275 A B f s x g) = (term297 A B f s x g).
Proof. exact (EQ_MP (@lem3484510 A B f s x g) (@lem3484488 A B f s x g)). Qed.
Lemma lem3484522 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term276 A B f s x) = (term298 A B f s x).
Proof. exact (fun_ext (fun g : type1413 A B => @lem3484511 A B f s x g)). Qed.
Lemma lem3484523 {A B : Type'} : (@ex (A -> B -> Prop)) = (@ex (A -> B -> Prop)).
Proof. exact (eq_refl (@ex (A -> B -> Prop))). Qed.
Lemma lem3484524 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term277 A B f s x) = (term299 A B f s x).
Proof. exact (MK_COMB (@lem3484523 A B) (@lem3484522 A B f s x)). Qed.
Lemma lem3484526 {A B : Type'} (P : type1413 A B) : (term1 A B P) = (term0 A B P).
Proof. exact (EQ_MP (@lem3483774 A B P) (@lem3483773 A B P)). Qed.
Lemma lem3484527 {A B : Type'} (P : type1374 A B) : (term300 A B P) = (term301 A B P).
Proof. exact (@lem3484526 A (B -> Prop) P). Qed.
Lemma lem3484528 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term302 A B f s x) = (term303 A B f s x).
Proof. exact (@lem3484527 A B (term304 A B f s x)). Qed.
Lemma lem3484529 {A B : Type'} (f : type1374 A B) (x : A) (s : A -> Prop) (x' : B) : (term305 A B f s x' x) = (term306 A B f x s x').
Proof. exact (eq_refl (term305 A B f s x' x)). Qed.
Lemma lem3484530 {A B : Type'} (g : type1413 A B) (x : A) : (g x) = (g x).
Proof. exact (eq_refl (g x)). Qed.
Lemma lem3484531 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (x' : A) : (term307 A B f s x g x') = (term308 A B f s x g x').
Proof. exact (MK_COMB (@lem3484529 A B f x' s x) (@lem3484530 A B g x')). Qed.
Lemma lem3484532 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (x' : A) : (term308 A B f s x g x') = (term294 A B f s x g x').
Proof. exact (eq_refl (term308 A B f s x g x')). Qed.
Lemma lem3484533 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (x' : A) : (term307 A B f s x g x') = (term294 A B f s x g x').
Proof. exact (TRANS (@lem3484531 A B f s x g x') (@lem3484532 A B f s x g x')). Qed.
Lemma lem3484534 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) : (term309 A B f s x g) = (term296 A B f s x g).
Proof. exact (fun_ext (fun x' : A => @lem3484533 A B f s x g x')). Qed.
Lemma lem3484535 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3484536 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) : (term310 A B f s x g) = (term297 A B f s x g).
Proof. exact (MK_COMB (@lem3484535 A) (@lem3484534 A B f s x g)). Qed.
Lemma lem3484537 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term311 A B f s x) = (term298 A B f s x).
Proof. exact (fun_ext (fun g : type1413 A B => @lem3484536 A B f s x g)). Qed.
Lemma lem3484538 {A B : Type'} : (@ex (A -> B -> Prop)) = (@ex (A -> B -> Prop)).
Proof. exact (eq_refl (@ex (A -> B -> Prop))). Qed.
Lemma lem3484539 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term302 A B f s x) = (term299 A B f s x).
Proof. exact (MK_COMB (@lem3484538 A B) (@lem3484537 A B f s x)). Qed.
Lemma lem3484540 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3484541 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term312 A B f s x) = (term313 A B f s x).
Proof. exact (MK_COMB (@lem3484540) (@lem3484539 A B f s x)). Qed.
Lemma lem3484542 {A B : Type'} (f : type1374 A B) (x : A) (s : A -> Prop) (x' : B) : (term305 A B f s x' x) = (term306 A B f x s x').
Proof. exact (eq_refl (term305 A B f s x' x)). Qed.
Lemma lem3484543 {B : Type'} (g : B -> Prop) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem3484544 {A B : Type'} (f : type1374 A B) (x : A) (s : A -> Prop) (x' : B) (g : B -> Prop) : (term314 A B f s x' x g) = (term315 A B f x s x' g).
Proof. exact (MK_COMB (@lem3484542 A B f x s x') (@lem3484543 B g)). Qed.
Lemma lem3484545 {A B : Type'} (f : type1374 A B) (x : A) (s : A -> Prop) (x' : B) (g : B -> Prop) : (term315 A B f x s x' g) = (term316 A B f x s x' g).
Proof. exact (eq_refl (term315 A B f x s x' g)). Qed.
Lemma lem3484546 {A B : Type'} (f : type1374 A B) (x : A) (s : A -> Prop) (x' : B) (g : B -> Prop) : (term314 A B f s x' x g) = (term316 A B f x s x' g).
Proof. exact (TRANS (@lem3484544 A B f x s x' g) (@lem3484545 A B f x s x' g)). Qed.
Lemma lem3484547 {A B : Type'} (f : type1374 A B) (x : A) (s : A -> Prop) (x' : B) : (term317 A B f s x' x) = (term306 A B f x s x').
Proof. exact (fun_ext (fun g : B -> Prop => @lem3484546 A B f x s x' g)). Qed.
Lemma lem3484548 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem3484549 {A B : Type'} (f : type1374 A B) (x : A) (s : A -> Prop) (x' : B) : (term318 A B f s x' x) = (term319 A B f x s x').
Proof. exact (MK_COMB (@lem3484548 B) (@lem3484547 A B f x s x')). Qed.
Lemma lem3484550 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term320 A B f s x) = (term321 A B f s x).
Proof. exact (fun_ext (fun x' : A => @lem3484549 A B f x' s x)). Qed.
Lemma lem3484551 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3484552 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term303 A B f s x) = (term322 A B f s x).
Proof. exact (MK_COMB (@lem3484551 A) (@lem3484550 A B f s x)). Qed.
Lemma lem3484553 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : ((term302 A B f s x) = (term303 A B f s x)) = ((term299 A B f s x) = (term322 A B f s x)).
Proof. exact (MK_COMB (@lem3484541 A B f s x) (@lem3484552 A B f s x)). Qed.
Lemma lem3484554 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term299 A B f s x) = (term322 A B f s x).
Proof. exact (EQ_MP (@lem3484553 A B f s x) (@lem3484528 A B f s x)). Qed.
Lemma lem3484569 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term277 A B f s x) = (term322 A B f s x).
Proof. exact (TRANS (@lem3484524 A B f s x) (@lem3484554 A B f s x)). Qed.
Lemma lem3484570 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) : (term243 A B s f x) = (term243 A B s f x).
Proof. exact (eq_refl (term243 A B s f x)). Qed.
Lemma lem3484571 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : ((term242 A B s f x) = (term277 A B f s x)) = ((term242 A B s f x) = (term322 A B f s x)).
Proof. exact (MK_COMB (@lem3484570 A B s f x) (@lem3484569 A B f s x)). Qed.
Lemma lem3484574 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : ((term242 A B s f x) = (term322 A B f s x)) = ((term242 A B s f x) = (term277 A B f s x)).
Proof. exact (SYM (@lem3484571 A B f s x)). Qed.
Lemma lem3484576 (p : Prop) : p = (term323 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3484577 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : ((term242 A B s f x) = (term322 A B f s x)) = (term324 A B f s x).
Proof. exact (@lem3484576 ((term242 A B s f x) = (term322 A B f s x))). Qed.
Lemma lem3484578 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term324 A B f s x) = ((term242 A B s f x) = (term322 A B f s x)).
Proof. exact (SYM (@lem3484577 A B f s x)). Qed.
Lemma lem3484579 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (h1 : term325 A B f s x) : term325 A B f s x.
Proof. exact (h1). Qed.
Lemma lem3484582 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (h1 : term324 A B f s x) : term324 A B f s x.
Proof. exact (h1). Qed.
Lemma lem3484583 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : term326 A B f s x.
Proof. exact (fun h0 : term324 A B f s x => @lem3484582 A B f s x h0). Qed.
Lemma lem3484584 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (h1 : term326 A B f s x) : term326 A B f s x.
Proof. exact (h1). Qed.
Lemma lem3484585 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (h1 : term324 A B f s x) : term324 A B f s x.
Proof. exact (h1). Qed.
Lemma lem3484586 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (h1 : term324 A B f s x) (h2 : term326 A B f s x) : term324 A B f s x.
Proof. exact (@lem3484584 A B f s x h2 (@lem3484585 A B f s x h1)). Qed.
Lemma lem3484587 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (h1 : term324 A B f s x) : term327 A B f s x.
Proof. exact (fun h0 : term326 A B f s x => @lem3484586 A B f s x h1 h0). Qed.
Lemma lem3484588 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (h1 : term326 A B f s x) : term326 A B f s x.
Proof. exact (h1). Qed.
Lemma lem3484589 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (h1 : term324 A B f s x) (h2 : term326 A B f s x) : term324 A B f s x.
Proof. exact (@lem3484587 A B f s x h1 (@lem3484588 A B f s x h2)). Qed.
Lemma lem3484590 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (h1 : term326 A B f s x) : term326 A B f s x.
Proof. exact (fun h0 : term324 A B f s x => @lem3484589 A B f s x h0 h1). Qed.
Lemma lem3484591 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : term328 A B f s x.
Proof. exact (fun h0 : term326 A B f s x => @lem3484590 A B f s x h0). Qed.
Lemma lem3484594 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : term326 A B f s x.
Proof. exact (@lem3484591 A B f s x (@lem3484583 A B f s x)). Qed.
Lemma lem3484595 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : term326 A B f s x.
Proof. exact (@lem3484594 A B f s x). Qed.
Lemma lem3484609 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3484610 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term324 A B f s x) = (term329 A B f s x).
Proof. exact (@lem3484609 (term325 A B f s x)). Qed.
Lemma lem3484612 (t : Prop) : (term33 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3484613 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term329 A B f s x) = ((term242 A B s f x) = (term322 A B f s x)).
Proof. exact (@lem3484612 ((term242 A B s f x) = (term322 A B f s x))). Qed.
Lemma lem3484614 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term324 A B f s x) = ((term242 A B s f x) = (term322 A B f s x)).
Proof. exact (TRANS (@lem3484610 A B f s x) (@lem3484613 A B f s x)). Qed.
Lemma lem3484685 {A B : Type'} (s : A -> Prop) (x : B) : (term330 A B s x) = (term331 A B s x).
Proof. exact (fun_ext (fun f : type1374 A B => @lem3484614 A B f s x)). Qed.
Lemma lem3484686 {A B : Type'} : (@all (A -> (B -> Prop) -> Prop)) = (@all (A -> (B -> Prop) -> Prop)).
Proof. exact (eq_refl (@all (A -> (B -> Prop) -> Prop))). Qed.
Lemma lem3484687 {A B : Type'} (s : A -> Prop) (x : B) : (term332 A B s x) = (term333 A B s x).
Proof. exact (MK_COMB (@lem3484686 A B) (@lem3484685 A B s x)). Qed.
Lemma lem3484692 {A B : Type'} (x : B) : (term334 A B x) = (term335 A B x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3484687 A B s x)). Qed.
Lemma lem3484693 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3484694 {A B : Type'} (x : B) : (term336 A B x) = (term337 A B x).
Proof. exact (MK_COMB (@lem3484693 A) (@lem3484692 A B x)). Qed.
Lemma lem3484699 {A B : Type'} : (term338 A B) = (term339 A B).
Proof. exact (fun_ext (fun x : B => @lem3484694 A B x)). Qed.
Lemma lem3484700 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3484709 {A B : Type'} : (term340 A B) = (term341 A B).
Proof. exact (MK_COMB (@lem3484700 B) (@lem3484699 A B)). Qed.
Lemma lem3484724 {A B : Type'} (f : type1374 A B) (x : A) (s : A -> Prop) (x' : B) (g : B -> Prop) : (term316 A B f x s x' g) = (term316 A B f x s x' g).
Proof. exact (eq_refl (term316 A B f x s x' g)). Qed.
Lemma lem3484725 {A B : Type'} (f : type1374 A B) (x : A) (s : A -> Prop) (x' : B) : (term306 A B f x s x') = (term306 A B f x s x').
Proof. exact (fun_ext (fun g : B -> Prop => @lem3484724 A B f x s x' g)). Qed.
Lemma lem3484726 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem3484727 {A B : Type'} (f : type1374 A B) (x : A) (s : A -> Prop) (x' : B) : (term319 A B f x s x') = (term319 A B f x s x').
Proof. exact (MK_COMB (@lem3484726 B) (@lem3484725 A B f x s x')). Qed.
Lemma lem3484728 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term321 A B f s x) = (term321 A B f s x).
Proof. exact (fun_ext (fun x' : A => @lem3484727 A B f x' s x)). Qed.
Lemma lem3484729 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3484730 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term322 A B f s x) = (term322 A B f s x).
Proof. exact (MK_COMB (@lem3484729 A) (@lem3484728 A B f s x)). Qed.
Lemma lem3484735 {A B : Type'} (f : type1374 A B) (x : A) (x' : B) (t : B -> Prop) : (term342 A B f x x' t) = (term342 A B f x x' t).
Proof. exact (eq_refl (term342 A B f x x' t)). Qed.
Lemma lem3484736 {A B : Type'} (f : type1374 A B) (x : A) (x' : B) : (term343 A B f x x') = (term343 A B f x x').
Proof. exact (fun_ext (fun t : B -> Prop => @lem3484735 A B f x x' t)). Qed.
Lemma lem3484737 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3484738 {A B : Type'} (f : type1374 A B) (x : A) (x' : B) : (term191 A B f x x') = (term191 A B f x x').
Proof. exact (MK_COMB (@lem3484737 B) (@lem3484736 A B f x x')). Qed.
Lemma lem3484741 {A : Type'} (x : A) (s : A -> Prop) : (term99 A x s) = (term99 A x s).
Proof. exact (eq_refl (term99 A x s)). Qed.
Lemma lem3484742 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : A) (x' : B) : (term192 A B s f x x') = (term192 A B s f x x').
Proof. exact (MK_COMB (@lem3484741 A x s) (@lem3484738 A B f x x')). Qed.
Lemma lem3484743 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3484744 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : A) (x' : B) : (term239 A B s f x x') = (term239 A B s f x x').
Proof. exact (MK_COMB (@lem3484743) (@lem3484742 A B s f x x')). Qed.
Lemma lem3484745 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) : (term241 A B s f x) = (term241 A B s f x).
Proof. exact (fun_ext (fun x' : A => @lem3484744 A B s f x' x)). Qed.
Lemma lem3484746 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3484747 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) : (term242 A B s f x) = (term242 A B s f x).
Proof. exact (MK_COMB (@lem3484746 A) (@lem3484745 A B s f x)). Qed.
Lemma lem3484748 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3484749 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) : (term243 A B s f x) = (term243 A B s f x).
Proof. exact (MK_COMB (@lem3484748) (@lem3484747 A B s f x)). Qed.
Lemma lem3484750 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : ((term242 A B s f x) = (term322 A B f s x)) = ((term242 A B s f x) = (term322 A B f s x)).
Proof. exact (MK_COMB (@lem3484749 A B s f x) (@lem3484730 A B f s x)). Qed.
Lemma lem3484751 {A B : Type'} (s : A -> Prop) (x : B) : (term331 A B s x) = (term331 A B s x).
Proof. exact (fun_ext (fun f : type1374 A B => @lem3484750 A B f s x)). Qed.
Lemma lem3484752 {A B : Type'} : (@all (A -> (B -> Prop) -> Prop)) = (@all (A -> (B -> Prop) -> Prop)).
Proof. exact (eq_refl (@all (A -> (B -> Prop) -> Prop))). Qed.
Lemma lem3484753 {A B : Type'} (s : A -> Prop) (x : B) : (term333 A B s x) = (term333 A B s x).
Proof. exact (MK_COMB (@lem3484752 A B) (@lem3484751 A B s x)). Qed.
Lemma lem3484754 {A B : Type'} (x : B) : (term335 A B x) = (term335 A B x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3484753 A B s x)). Qed.
Lemma lem3484755 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3484756 {A B : Type'} (x : B) : (term337 A B x) = (term337 A B x).
Proof. exact (MK_COMB (@lem3484755 A) (@lem3484754 A B x)). Qed.
Lemma lem3484757 {A B : Type'} : (term339 A B) = (term339 A B).
Proof. exact (fun_ext (fun x : B => @lem3484756 A B x)). Qed.
Lemma lem3484758 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3484759 {A B : Type'} : (term341 A B) = (term341 A B).
Proof. exact (MK_COMB (@lem3484758 B) (@lem3484757 A B)). Qed.
Lemma lem3484814 {A B : Type'} : (term340 A B) = (term341 A B).
Proof. exact (TRANS (@lem3484709 A B) (@lem3484759 A B)). Qed.
Lemma lem3484815 {A B : Type'} : (term341 A B) = (term340 A B).
Proof. exact (SYM (@lem3484814 A B)). Qed.
Lemma lem3484817 (p : Prop) : p = (term323 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3484818 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : ((term242 A B s f x) = (term322 A B f s x)) = (term324 A B f s x).
Proof. exact (@lem3484817 ((term242 A B s f x) = (term322 A B f s x))). Qed.
Lemma lem3484819 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term324 A B f s x) = ((term242 A B s f x) = (term322 A B f s x)).
Proof. exact (SYM (@lem3484818 A B f s x)). Qed.
Lemma lem3484820 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (h1 : term325 A B f s x) : term325 A B f s x.
Proof. exact (h1). Qed.
Lemma lem3484831 {A B : Type'} (f : type1374 A B) (x : A) (x' : B) (t : B -> Prop) : (term344 A B f x x' t) = (term345 A B f x x' t).
Proof. exact (@lem17362 (term346 A B t f x) (@IN B x' t)). Qed.
Lemma lem3484836 {A B : Type'} (f : type1374 A B) (x : A) (x' : B) (t : B -> Prop) : (term342 A B f x x' t) = (term347 A B f x x' t).
Proof. exact (@lem17265 (term346 A B t f x) (@IN B x' t)). Qed.
Lemma lem3484837 {B : Type'} (P : type686 B) : (term348 B P) = (term349 B P).
Proof. exact (@lem18392 (B -> Prop) P). Qed.
Lemma lem3484838 {A B : Type'} (f : type1374 A B) (x : A) (x' : B) : (term350 A B f x x') = (term351 A B f x x').
Proof. exact (@lem3484837 B (term343 A B f x x')). Qed.
Lemma lem3484839 {A B : Type'} (f : type1374 A B) (x : A) (x' : B) (t : B -> Prop) : (term352 A B f x x' t) = (term342 A B f x x' t).
Proof. exact (eq_refl (term352 A B f x x' t)). Qed.
Lemma lem3484840 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3484841 {A B : Type'} (f : type1374 A B) (x : A) (x' : B) (t : B -> Prop) : (term353 A B f x x' t) = (term344 A B f x x' t).
Proof. exact (MK_COMB (@lem3484840) (@lem3484839 A B f x x' t)). Qed.
Lemma lem3484842 {A B : Type'} (f : type1374 A B) (x : A) (x' : B) (t : B -> Prop) : (term353 A B f x x' t) = (term345 A B f x x' t).
Proof. exact (TRANS (@lem3484841 A B f x x' t) (@lem3484831 A B f x x' t)). Qed.
Lemma lem3484843 {A B : Type'} (f : type1374 A B) (x : A) (x' : B) : (term354 A B f x x') = (term355 A B f x x').
Proof. exact (fun_ext (fun t : B -> Prop => @lem3484842 A B f x x' t)). Qed.
Lemma lem3484844 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem3484845 {A B : Type'} (f : type1374 A B) (x : A) (x' : B) : (term351 A B f x x') = (term356 A B f x x').
Proof. exact (MK_COMB (@lem3484844 B) (@lem3484843 A B f x x')). Qed.
Lemma lem3484846 {A B : Type'} (f : type1374 A B) (x : A) (x' : B) : (term350 A B f x x') = (term356 A B f x x').
Proof. exact (TRANS (@lem3484838 A B f x x') (@lem3484845 A B f x x')). Qed.
Lemma lem3484847 {A B : Type'} (f : type1374 A B) (x : A) (x' : B) : (term343 A B f x x') = (term357 A B f x x').
Proof. exact (fun_ext (fun t : B -> Prop => @lem3484836 A B f x x' t)). Qed.
Lemma lem3484848 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3484849 {A B : Type'} (f : type1374 A B) (x : A) (x' : B) : (term191 A B f x x') = (term358 A B f x x').
Proof. exact (MK_COMB (@lem3484848 B) (@lem3484847 A B f x x')). Qed.
Lemma lem3484851 {A : Type'} (x : A) (s : A -> Prop) : (term359 A x s) = (term359 A x s).
Proof. exact (eq_refl (term359 A x s)). Qed.
Lemma lem3484852 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : A) (x' : B) : (term360 A B s f x x') = (term361 A B s f x x').
Proof. exact (MK_COMB (@lem3484851 A x s) (@lem3484846 A B f x x')). Qed.
Lemma lem3484853 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : A) (x' : B) : (term239 A B s f x x') = (term360 A B s f x x').
Proof. exact (@lem17045 (@IN A x s) (term191 A B f x x')). Qed.
Lemma lem3484854 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : A) (x' : B) : (term239 A B s f x x') = (term361 A B s f x x').
Proof. exact (TRANS (@lem3484853 A B s f x x') (@lem3484852 A B s f x x')). Qed.
Lemma lem3484856 {A : Type'} (x : A) (s : A -> Prop) : (term99 A x s) = (term99 A x s).
Proof. exact (eq_refl (term99 A x s)). Qed.
Lemma lem3484857 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : A) (x' : B) : (term192 A B s f x x') = (term362 A B s f x x').
Proof. exact (MK_COMB (@lem3484856 A x s) (@lem3484849 A B f x x')). Qed.
Lemma lem3484858 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : A) (x' : B) : (term363 A B s f x x') = (term192 A B s f x x').
Proof. exact (@lem16933 (term192 A B s f x x')). Qed.
Lemma lem3484859 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : A) (x' : B) : (term363 A B s f x x') = (term362 A B s f x x').
Proof. exact (TRANS (@lem3484858 A B s f x x') (@lem3484857 A B s f x x')). Qed.
Lemma lem3484860 {A : Type'} (P : A -> Prop) : (term364 A P) = (term22 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3484861 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) : (term365 A B s f x) = (term366 A B s f x).
Proof. exact (@lem3484860 A (term241 A B s f x)). Qed.
Lemma lem3484862 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : A) (x' : B) : (term367 A B s f x' x) = (term239 A B s f x x').
Proof. exact (eq_refl (term367 A B s f x' x)). Qed.
Lemma lem3484863 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3484864 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : A) (x' : B) : (term368 A B s f x' x) = (term363 A B s f x x').
Proof. exact (MK_COMB (@lem3484863) (@lem3484862 A B s f x x')). Qed.
Lemma lem3484865 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : A) (x' : B) : (term368 A B s f x' x) = (term362 A B s f x x').
Proof. exact (TRANS (@lem3484864 A B s f x x') (@lem3484859 A B s f x x')). Qed.
Lemma lem3484866 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) : (term369 A B s f x) = (term370 A B s f x).
Proof. exact (fun_ext (fun x' : A => @lem3484865 A B s f x' x)). Qed.
Lemma lem3484867 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3484868 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) : (term366 A B s f x) = (term371 A B s f x).
Proof. exact (MK_COMB (@lem3484867 A) (@lem3484866 A B s f x)). Qed.
Lemma lem3484869 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) : (term365 A B s f x) = (term371 A B s f x).
Proof. exact (TRANS (@lem3484861 A B s f x) (@lem3484868 A B s f x)). Qed.
Lemma lem3484870 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) : (term241 A B s f x) = (term372 A B s f x).
Proof. exact (fun_ext (fun x' : A => @lem3484854 A B s f x' x)). Qed.
Lemma lem3484871 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3484872 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) : (term242 A B s f x) = (term373 A B s f x).
Proof. exact (MK_COMB (@lem3484871 A) (@lem3484870 A B s f x)). Qed.
Lemma lem3484881 {A B : Type'} (s : A -> Prop) (g : B -> Prop) (f : type1374 A B) (x : A) : (term374 A B s g f x) = (term375 A B s g f x).
Proof. exact (@lem17362 (@IN A x s) (term346 A B g f x)). Qed.
Lemma lem3484886 {A B : Type'} (s : A -> Prop) (g : B -> Prop) (f : type1374 A B) (x : A) : (term376 A B s g f x) = (term377 A B s g f x).
Proof. exact (@lem17265 (@IN A x s) (term346 A B g f x)). Qed.
Lemma lem3484895 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (g : B -> Prop) : (term378 A B x s x' g) = (term379 A B x s x' g).
Proof. exact (@lem17045 (@IN A x s) (@IN B x' g)). Qed.
Lemma lem3484900 {A B : Type'} (x : A) (s : A -> Prop) (x' : B) (g : B -> Prop) : (term380 A B x s x' g) = (term381 A B x s x' g).
Proof. exact (@lem16933 (term381 A B x s x' g)). Qed.
Lemma lem3484901 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3484902 {A B : Type'} (s : A -> Prop) (g : B -> Prop) (f : type1374 A B) (x : A) : (term382 A B s g f x) = (term383 A B s g f x).
Proof. exact (MK_COMB (@lem3484901) (@lem3484881 A B s g f x)). Qed.
Lemma lem3484903 {A B : Type'} (f : type1374 A B) (x : A) (s : A -> Prop) (x' : B) (g : B -> Prop) : (term384 A B f x s x' g) = (term385 A B f x s x' g).
Proof. exact (MK_COMB (@lem3484902 A B s g f x) (@lem3484900 A B x s x' g)). Qed.
Lemma lem3484904 {A B : Type'} (f : type1374 A B) (x : A) (s : A -> Prop) (x' : B) (g : B -> Prop) : (term386 A B f x s x' g) = (term384 A B f x s x' g).
Proof. exact (@lem17045 (term376 A B s g f x) (term378 A B x s x' g)). Qed.
Lemma lem3484905 {A B : Type'} (f : type1374 A B) (x : A) (s : A -> Prop) (x' : B) (g : B -> Prop) : (term386 A B f x s x' g) = (term385 A B f x s x' g).
Proof. exact (TRANS (@lem3484904 A B f x s x' g) (@lem3484903 A B f x s x' g)). Qed.
Lemma lem3484906 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3484907 {A B : Type'} (s : A -> Prop) (g : B -> Prop) (f : type1374 A B) (x : A) : (term387 A B s g f x) = (term388 A B s g f x).
Proof. exact (MK_COMB (@lem3484906) (@lem3484886 A B s g f x)). Qed.
Lemma lem3484908 {A B : Type'} (f : type1374 A B) (x : A) (s : A -> Prop) (x' : B) (g : B -> Prop) : (term316 A B f x s x' g) = (term389 A B f x s x' g).
Proof. exact (MK_COMB (@lem3484907 A B s g f x) (@lem3484895 A B x s x' g)). Qed.
Lemma lem3484909 {B : Type'} (P : type686 B) : (term390 B P) = (term391 B P).
Proof. exact (@lem18394 (B -> Prop) P). Qed.
Lemma lem3484910 {A B : Type'} (f : type1374 A B) (x : A) (s : A -> Prop) (x' : B) : (term392 A B f x s x') = (term393 A B f x s x').
Proof. exact (@lem3484909 B (term306 A B f x s x')). Qed.
Lemma lem3484911 {A B : Type'} (f : type1374 A B) (x : A) (s : A -> Prop) (x' : B) (g : B -> Prop) : (term315 A B f x s x' g) = (term316 A B f x s x' g).
Proof. exact (eq_refl (term315 A B f x s x' g)). Qed.
Lemma lem3484912 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3484913 {A B : Type'} (f : type1374 A B) (x : A) (s : A -> Prop) (x' : B) (g : B -> Prop) : (term394 A B f x s x' g) = (term386 A B f x s x' g).
Proof. exact (MK_COMB (@lem3484912) (@lem3484911 A B f x s x' g)). Qed.
Lemma lem3484914 {A B : Type'} (f : type1374 A B) (x : A) (s : A -> Prop) (x' : B) (g : B -> Prop) : (term394 A B f x s x' g) = (term385 A B f x s x' g).
Proof. exact (TRANS (@lem3484913 A B f x s x' g) (@lem3484905 A B f x s x' g)). Qed.
Lemma lem3484915 {A B : Type'} (f : type1374 A B) (x : A) (s : A -> Prop) (x' : B) : (term395 A B f x s x') = (term396 A B f x s x').
Proof. exact (fun_ext (fun g : B -> Prop => @lem3484914 A B f x s x' g)). Qed.
Lemma lem3484916 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3484917 {A B : Type'} (f : type1374 A B) (x : A) (s : A -> Prop) (x' : B) : (term393 A B f x s x') = (term397 A B f x s x').
Proof. exact (MK_COMB (@lem3484916 B) (@lem3484915 A B f x s x')). Qed.
Lemma lem3484918 {A B : Type'} (f : type1374 A B) (x : A) (s : A -> Prop) (x' : B) : (term392 A B f x s x') = (term397 A B f x s x').
Proof. exact (TRANS (@lem3484910 A B f x s x') (@lem3484917 A B f x s x')). Qed.
Lemma lem3484919 {A B : Type'} (f : type1374 A B) (x : A) (s : A -> Prop) (x' : B) : (term306 A B f x s x') = (term398 A B f x s x').
Proof. exact (fun_ext (fun g : B -> Prop => @lem3484908 A B f x s x' g)). Qed.
Lemma lem3484920 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem3484921 {A B : Type'} (f : type1374 A B) (x : A) (s : A -> Prop) (x' : B) : (term319 A B f x s x') = (term399 A B f x s x').
Proof. exact (MK_COMB (@lem3484920 B) (@lem3484919 A B f x s x')). Qed.
Lemma lem3484922 {A : Type'} (P : A -> Prop) : (term364 A P) = (term22 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3484923 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term400 A B f s x) = (term401 A B f s x).
Proof. exact (@lem3484922 A (term321 A B f s x)). Qed.
Lemma lem3484924 {A B : Type'} (f : type1374 A B) (x : A) (s : A -> Prop) (x' : B) : (term402 A B f s x' x) = (term319 A B f x s x').
Proof. exact (eq_refl (term402 A B f s x' x)). Qed.
Lemma lem3484925 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3484926 {A B : Type'} (f : type1374 A B) (x : A) (s : A -> Prop) (x' : B) : (term403 A B f s x' x) = (term392 A B f x s x').
Proof. exact (MK_COMB (@lem3484925) (@lem3484924 A B f x s x')). Qed.
Lemma lem3484927 {A B : Type'} (f : type1374 A B) (x : A) (s : A -> Prop) (x' : B) : (term403 A B f s x' x) = (term397 A B f x s x').
Proof. exact (TRANS (@lem3484926 A B f x s x') (@lem3484918 A B f x s x')). Qed.
Lemma lem3484928 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term404 A B f s x) = (term405 A B f s x).
Proof. exact (fun_ext (fun x' : A => @lem3484927 A B f x' s x)). Qed.
Lemma lem3484929 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3484930 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term401 A B f s x) = (term406 A B f s x).
Proof. exact (MK_COMB (@lem3484929 A) (@lem3484928 A B f s x)). Qed.
Lemma lem3484931 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term400 A B f s x) = (term406 A B f s x).
Proof. exact (TRANS (@lem3484923 A B f s x) (@lem3484930 A B f s x)). Qed.
Lemma lem3484932 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term321 A B f s x) = (term407 A B f s x).
Proof. exact (fun_ext (fun x' : A => @lem3484921 A B f x' s x)). Qed.
Lemma lem3484933 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3484934 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term322 A B f s x) = (term408 A B f s x).
Proof. exact (MK_COMB (@lem3484933 A) (@lem3484932 A B f s x)). Qed.
Lemma lem3484935 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3484936 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) : (term409 A B s f x) = (term410 A B s f x).
Proof. exact (MK_COMB (@lem3484935) (@lem3484869 A B s f x)). Qed.
Lemma lem3484937 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term411 A B f s x) = (term412 A B f s x).
Proof. exact (MK_COMB (@lem3484936 A B s f x) (@lem3484934 A B f s x)). Qed.
Lemma lem3484938 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3484939 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) : (term413 A B s f x) = (term414 A B s f x).
Proof. exact (MK_COMB (@lem3484938) (@lem3484872 A B s f x)). Qed.
Lemma lem3484940 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term415 A B f s x) = (term416 A B f s x).
Proof. exact (MK_COMB (@lem3484939 A B s f x) (@lem3484931 A B f s x)). Qed.
Lemma lem3484941 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3484942 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term417 A B f s x) = (term418 A B f s x).
Proof. exact (MK_COMB (@lem3484941) (@lem3484940 A B f s x)). Qed.
Lemma lem3484943 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term419 A B f s x) = (term420 A B f s x).
Proof. exact (MK_COMB (@lem3484942 A B f s x) (@lem3484937 A B f s x)). Qed.
Lemma lem3484944 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term325 A B f s x) = (term419 A B f s x).
Proof. exact (@lem17646 (term242 A B s f x) (term322 A B f s x)). Qed.
Lemma lem3484945 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term325 A B f s x) = (term420 A B f s x).
Proof. exact (TRANS (@lem3484944 A B f s x) (@lem3484943 A B f s x)). Qed.
Lemma lem3485244 {A : Type'} (P : Prop) (Q : A -> Prop) : (term421 A P Q) = (term422 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3485245 {B : Type'} (P : Prop) (Q : type686 B) : (term423 B P Q) = (term424 B P Q).
Proof. exact (@lem3485244 (B -> Prop) P Q). Qed.
Lemma lem3485246 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : A) (x' : B) : (term425 A B s f x x') = (term426 A B s f x x').
Proof. exact (@lem3485245 B (term427 A x s) (term355 A B f x x')). Qed.
Lemma lem3485247 {A B : Type'} (f : type1374 A B) (x : A) (x' : B) (t : B -> Prop) : (term428 A B f x x' t) = (term345 A B f x x' t).
Proof. exact (eq_refl (term428 A B f x x' t)). Qed.
Lemma lem3485248 {A B : Type'} (f : type1374 A B) (x : A) (x' : B) : (term429 A B f x x') = (term355 A B f x x').
Proof. exact (fun_ext (fun t : B -> Prop => @lem3485247 A B f x x' t)). Qed.
Lemma lem3485249 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem3485250 {A B : Type'} (f : type1374 A B) (x : A) (x' : B) : (term430 A B f x x') = (term356 A B f x x').
Proof. exact (MK_COMB (@lem3485249 B) (@lem3485248 A B f x x')). Qed.
Lemma lem3485251 {A : Type'} (x : A) (s : A -> Prop) : (term359 A x s) = (term359 A x s).
Proof. exact (eq_refl (term359 A x s)). Qed.
Lemma lem3485252 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : A) (x' : B) : (term425 A B s f x x') = (term361 A B s f x x').
Proof. exact (MK_COMB (@lem3485251 A x s) (@lem3485250 A B f x x')). Qed.
Lemma lem3485253 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3485254 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : A) (x' : B) : (term431 A B s f x x') = (term432 A B s f x x').
Proof. exact (MK_COMB (@lem3485253) (@lem3485252 A B s f x x')). Qed.
Lemma lem3485255 {A B : Type'} (f : type1374 A B) (x : A) (x' : B) (t : B -> Prop) : (term428 A B f x x' t) = (term345 A B f x x' t).
Proof. exact (eq_refl (term428 A B f x x' t)). Qed.
Lemma lem3485256 {A : Type'} (x : A) (s : A -> Prop) : (term359 A x s) = (term359 A x s).
Proof. exact (eq_refl (term359 A x s)). Qed.
Lemma lem3485257 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : A) (x' : B) (t : B -> Prop) : (term433 A B s f x x' t) = (term434 A B s f x x' t).
Proof. exact (MK_COMB (@lem3485256 A x s) (@lem3485255 A B f x x' t)). Qed.
Lemma lem3485258 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : A) (x' : B) : (term435 A B s f x x') = (term436 A B s f x x').
Proof. exact (fun_ext (fun t : B -> Prop => @lem3485257 A B s f x x' t)). Qed.
Lemma lem3485259 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem3485260 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : A) (x' : B) : (term426 A B s f x x') = (term437 A B s f x x').
Proof. exact (MK_COMB (@lem3485259 B) (@lem3485258 A B s f x x')). Qed.
Lemma lem3485261 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : A) (x' : B) : ((term425 A B s f x x') = (term426 A B s f x x')) = ((term361 A B s f x x') = (term437 A B s f x x')).
Proof. exact (MK_COMB (@lem3485254 A B s f x x') (@lem3485260 A B s f x x')). Qed.
Lemma lem3485262 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : A) (x' : B) : (term361 A B s f x x') = (term437 A B s f x x').
Proof. exact (EQ_MP (@lem3485261 A B s f x x') (@lem3485246 A B s f x x')). Qed.
Lemma lem3485263 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) : (term372 A B s f x) = (term438 A B s f x).
Proof. exact (fun_ext (fun x' : A => @lem3485262 A B s f x' x)). Qed.
Lemma lem3485264 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3485265 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) : (term373 A B s f x) = (term439 A B s f x).
Proof. exact (MK_COMB (@lem3485264 A) (@lem3485263 A B s f x)). Qed.
Lemma lem3485267 {A B : Type'} (P : type1413 A B) : (term0 A B P) = (term1 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3485268 {A B : Type'} (P : type1374 A B) : (term301 A B P) = (term300 A B P).
Proof. exact (@lem3485267 A (B -> Prop) P). Qed.
Lemma lem3485269 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) : (term440 A B s f x) = (term441 A B s f x).
Proof. exact (@lem3485268 A B (term442 A B s f x)). Qed.
Lemma lem3485270 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : A) (x' : B) : (term443 A B s f x' x) = (term436 A B s f x x').
Proof. exact (eq_refl (term443 A B s f x' x)). Qed.
Lemma lem3485271 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3485272 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : A) (x' : B) (t : B -> Prop) : (term444 A B s f x' x t) = (term445 A B s f x x' t).
Proof. exact (MK_COMB (@lem3485270 A B s f x x') (@lem3485271 B t)). Qed.
Lemma lem3485273 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : A) (x' : B) (t : B -> Prop) : (term445 A B s f x x' t) = (term434 A B s f x x' t).
Proof. exact (eq_refl (term445 A B s f x x' t)). Qed.
Lemma lem3485274 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : A) (x' : B) (t : B -> Prop) : (term444 A B s f x' x t) = (term434 A B s f x x' t).
Proof. exact (TRANS (@lem3485272 A B s f x x' t) (@lem3485273 A B s f x x' t)). Qed.
Lemma lem3485275 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : A) (x' : B) : (term446 A B s f x' x) = (term436 A B s f x x').
Proof. exact (fun_ext (fun t : B -> Prop => @lem3485274 A B s f x x' t)). Qed.
Lemma lem3485276 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem3485277 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : A) (x' : B) : (term447 A B s f x' x) = (term437 A B s f x x').
Proof. exact (MK_COMB (@lem3485276 B) (@lem3485275 A B s f x x')). Qed.
Lemma lem3485278 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) : (term448 A B s f x) = (term438 A B s f x).
Proof. exact (fun_ext (fun x' : A => @lem3485277 A B s f x' x)). Qed.
Lemma lem3485279 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3485280 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) : (term440 A B s f x) = (term439 A B s f x).
Proof. exact (MK_COMB (@lem3485279 A) (@lem3485278 A B s f x)). Qed.
Lemma lem3485281 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3485282 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) : (term449 A B s f x) = (term450 A B s f x).
Proof. exact (MK_COMB (@lem3485281) (@lem3485280 A B s f x)). Qed.
Lemma lem3485283 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : A) (x' : B) : (term443 A B s f x' x) = (term436 A B s f x x').
Proof. exact (eq_refl (term443 A B s f x' x)). Qed.
Lemma lem3485284 {A B : Type'} (t : type1413 A B) (x : A) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3485285 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) (t : type1413 A B) (x' : A) : (term451 A B s f x t x') = (term452 A B s f x t x').
Proof. exact (MK_COMB (@lem3485283 A B s f x' x) (@lem3485284 A B t x')). Qed.
Lemma lem3485286 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) (t : type1413 A B) (x' : A) : (term452 A B s f x t x') = (term453 A B s f x t x').
Proof. exact (eq_refl (term452 A B s f x t x')). Qed.
Lemma lem3485287 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) (t : type1413 A B) (x' : A) : (term451 A B s f x t x') = (term453 A B s f x t x').
Proof. exact (TRANS (@lem3485285 A B s f x t x') (@lem3485286 A B s f x t x')). Qed.
Lemma lem3485288 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) (t : type1413 A B) : (term454 A B s f x t) = (term455 A B s f x t).
Proof. exact (fun_ext (fun x' : A => @lem3485287 A B s f x t x')). Qed.
Lemma lem3485289 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3485290 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) (t : type1413 A B) : (term456 A B s f x t) = (term457 A B s f x t).
Proof. exact (MK_COMB (@lem3485289 A) (@lem3485288 A B s f x t)). Qed.
Lemma lem3485291 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) : (term458 A B s f x) = (term459 A B s f x).
Proof. exact (fun_ext (fun t : type1413 A B => @lem3485290 A B s f x t)). Qed.
Lemma lem3485292 {A B : Type'} : (@ex (A -> B -> Prop)) = (@ex (A -> B -> Prop)).
Proof. exact (eq_refl (@ex (A -> B -> Prop))). Qed.
Lemma lem3485293 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) : (term441 A B s f x) = (term460 A B s f x).
Proof. exact (MK_COMB (@lem3485292 A B) (@lem3485291 A B s f x)). Qed.
Lemma lem3485294 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) : ((term440 A B s f x) = (term441 A B s f x)) = ((term439 A B s f x) = (term460 A B s f x)).
Proof. exact (MK_COMB (@lem3485282 A B s f x) (@lem3485293 A B s f x)). Qed.
Lemma lem3485295 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) : (term439 A B s f x) = (term460 A B s f x).
Proof. exact (EQ_MP (@lem3485294 A B s f x) (@lem3485269 A B s f x)). Qed.
Lemma lem3485296 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) : (term373 A B s f x) = (term460 A B s f x).
Proof. exact (TRANS (@lem3485265 A B s f x) (@lem3485295 A B s f x)). Qed.
Lemma lem3485297 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3485298 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) : (term414 A B s f x) = (term461 A B s f x).
Proof. exact (MK_COMB (@lem3485297) (@lem3485296 A B s f x)). Qed.
Lemma lem3485299 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term406 A B f s x) = (term406 A B f s x).
Proof. exact (eq_refl (term406 A B f s x)). Qed.
Lemma lem3485300 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term416 A B f s x) = (term462 A B f s x).
Proof. exact (MK_COMB (@lem3485298 A B s f x) (@lem3485299 A B f s x)). Qed.
Lemma lem3485302 {A : Type'} (P : A -> Prop) (Q : Prop) : (term463 A P Q) = (term464 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3485303 {A B : Type'} (P : type475 A B) (Q : Prop) : (term465 A B P Q) = (term466 A B P Q).
Proof. exact (@lem3485302 (type1413 A B) P Q). Qed.
Lemma lem3485304 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term467 A B f s x) = (term468 A B f s x).
Proof. exact (@lem3485303 A B (term459 A B s f x) (term406 A B f s x)). Qed.
Lemma lem3485305 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) (t : type1413 A B) : (term469 A B s f x t) = (term457 A B s f x t).
Proof. exact (eq_refl (term469 A B s f x t)). Qed.
Lemma lem3485306 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) : (term470 A B s f x) = (term459 A B s f x).
Proof. exact (fun_ext (fun t : type1413 A B => @lem3485305 A B s f x t)). Qed.
Lemma lem3485307 {A B : Type'} : (@ex (A -> B -> Prop)) = (@ex (A -> B -> Prop)).
Proof. exact (eq_refl (@ex (A -> B -> Prop))). Qed.
Lemma lem3485308 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) : (term471 A B s f x) = (term460 A B s f x).
Proof. exact (MK_COMB (@lem3485307 A B) (@lem3485306 A B s f x)). Qed.
Lemma lem3485309 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3485310 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) : (term472 A B s f x) = (term461 A B s f x).
Proof. exact (MK_COMB (@lem3485309) (@lem3485308 A B s f x)). Qed.
Lemma lem3485311 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term406 A B f s x) = (term406 A B f s x).
Proof. exact (eq_refl (term406 A B f s x)). Qed.
Lemma lem3485312 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term467 A B f s x) = (term462 A B f s x).
Proof. exact (MK_COMB (@lem3485310 A B s f x) (@lem3485311 A B f s x)). Qed.
Lemma lem3485313 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3485314 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term473 A B f s x) = (term474 A B f s x).
Proof. exact (MK_COMB (@lem3485313) (@lem3485312 A B f s x)). Qed.
Lemma lem3485315 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) (t : type1413 A B) : (term469 A B s f x t) = (term457 A B s f x t).
Proof. exact (eq_refl (term469 A B s f x t)). Qed.
Lemma lem3485316 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3485317 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) (t : type1413 A B) : (term475 A B s f x t) = (term476 A B s f x t).
Proof. exact (MK_COMB (@lem3485316) (@lem3485315 A B s f x t)). Qed.
Lemma lem3485318 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term406 A B f s x) = (term406 A B f s x).
Proof. exact (eq_refl (term406 A B f s x)). Qed.
Lemma lem3485319 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (x : B) : (term477 A B t f s x) = (term478 A B t f s x).
Proof. exact (MK_COMB (@lem3485317 A B s f x t) (@lem3485318 A B f s x)). Qed.
Lemma lem3485320 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term479 A B f s x) = (term480 A B f s x).
Proof. exact (fun_ext (fun t : type1413 A B => @lem3485319 A B t f s x)). Qed.
Lemma lem3485321 {A B : Type'} : (@ex (A -> B -> Prop)) = (@ex (A -> B -> Prop)).
Proof. exact (eq_refl (@ex (A -> B -> Prop))). Qed.
Lemma lem3485322 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term468 A B f s x) = (term481 A B f s x).
Proof. exact (MK_COMB (@lem3485321 A B) (@lem3485320 A B f s x)). Qed.
Lemma lem3485323 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : ((term467 A B f s x) = (term468 A B f s x)) = ((term462 A B f s x) = (term481 A B f s x)).
Proof. exact (MK_COMB (@lem3485314 A B f s x) (@lem3485322 A B f s x)). Qed.
Lemma lem3485324 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term462 A B f s x) = (term481 A B f s x).
Proof. exact (EQ_MP (@lem3485323 A B f s x) (@lem3485304 A B f s x)). Qed.
Lemma lem3485326 {A : Type'} (P : Prop) (Q : A -> Prop) : (term482 A P Q) = (term483 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3485327 {A : Type'} (P : Prop) (Q : A -> Prop) : (term482 A P Q) = (term483 A P Q).
Proof. exact (@lem3485326 A P Q). Qed.
Lemma lem3485328 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (x : B) : (term484 A B t f s x) = (term485 A B t f s x).
Proof. exact (@lem3485327 A (term457 A B s f x t) (term405 A B f s x)). Qed.
Lemma lem3485329 {A B : Type'} (f : type1374 A B) (x : A) (s : A -> Prop) (x' : B) : (term486 A B f s x' x) = (term397 A B f x s x').
Proof. exact (eq_refl (term486 A B f s x' x)). Qed.
Lemma lem3485330 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term487 A B f s x) = (term405 A B f s x).
Proof. exact (fun_ext (fun x' : A => @lem3485329 A B f x' s x)). Qed.
Lemma lem3485331 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3485332 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term488 A B f s x) = (term406 A B f s x).
Proof. exact (MK_COMB (@lem3485331 A) (@lem3485330 A B f s x)). Qed.
Lemma lem3485333 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) (t : type1413 A B) : (term476 A B s f x t) = (term476 A B s f x t).
Proof. exact (eq_refl (term476 A B s f x t)). Qed.
Lemma lem3485334 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (x : B) : (term484 A B t f s x) = (term478 A B t f s x).
Proof. exact (MK_COMB (@lem3485333 A B s f x t) (@lem3485332 A B f s x)). Qed.
Lemma lem3485335 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3485336 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (x : B) : (term489 A B t f s x) = (term490 A B t f s x).
Proof. exact (MK_COMB (@lem3485335) (@lem3485334 A B t f s x)). Qed.
Lemma lem3485337 {A B : Type'} (f : type1374 A B) (x : A) (s : A -> Prop) (x' : B) : (term486 A B f s x' x) = (term397 A B f x s x').
Proof. exact (eq_refl (term486 A B f s x' x)). Qed.
Lemma lem3485338 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) (t : type1413 A B) : (term476 A B s f x t) = (term476 A B s f x t).
Proof. exact (eq_refl (term476 A B s f x t)). Qed.
Lemma lem3485339 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (x : A) (s : A -> Prop) (x' : B) : (term491 A B t f s x' x) = (term492 A B t f x s x').
Proof. exact (MK_COMB (@lem3485338 A B s f x' t) (@lem3485337 A B f x s x')). Qed.
Lemma lem3485340 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (x : B) : (term493 A B t f s x) = (term494 A B t f s x).
Proof. exact (fun_ext (fun x' : A => @lem3485339 A B t f x' s x)). Qed.
Lemma lem3485341 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3485342 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (x : B) : (term485 A B t f s x) = (term495 A B t f s x).
Proof. exact (MK_COMB (@lem3485341 A) (@lem3485340 A B t f s x)). Qed.
Lemma lem3485343 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (x : B) : ((term484 A B t f s x) = (term485 A B t f s x)) = ((term478 A B t f s x) = (term495 A B t f s x)).
Proof. exact (MK_COMB (@lem3485336 A B t f s x) (@lem3485342 A B t f s x)). Qed.
Lemma lem3485344 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (x : B) : (term478 A B t f s x) = (term495 A B t f s x).
Proof. exact (EQ_MP (@lem3485343 A B t f s x) (@lem3485328 A B t f s x)). Qed.
Lemma lem3485345 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term480 A B f s x) = (term496 A B f s x).
Proof. exact (fun_ext (fun t : type1413 A B => @lem3485344 A B t f s x)). Qed.
Lemma lem3485346 {A B : Type'} : (@ex (A -> B -> Prop)) = (@ex (A -> B -> Prop)).
Proof. exact (eq_refl (@ex (A -> B -> Prop))). Qed.
Lemma lem3485347 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term481 A B f s x) = (term497 A B f s x).
Proof. exact (MK_COMB (@lem3485346 A B) (@lem3485345 A B f s x)). Qed.
Lemma lem3485348 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term462 A B f s x) = (term497 A B f s x).
Proof. exact (TRANS (@lem3485324 A B f s x) (@lem3485347 A B f s x)). Qed.
Lemma lem3485349 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term416 A B f s x) = (term497 A B f s x).
Proof. exact (TRANS (@lem3485300 A B f s x) (@lem3485348 A B f s x)). Qed.
Lemma lem3485350 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3485351 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term418 A B f s x) = (term498 A B f s x).
Proof. exact (MK_COMB (@lem3485350) (@lem3485349 A B f s x)). Qed.
Lemma lem3485353 {A B : Type'} (P : type1413 A B) : (term0 A B P) = (term1 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3485354 {A B : Type'} (P : type1374 A B) : (term301 A B P) = (term300 A B P).
Proof. exact (@lem3485353 A (B -> Prop) P). Qed.
Lemma lem3485355 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term499 A B f s x) = (term500 A B f s x).
Proof. exact (@lem3485354 A B (term501 A B f s x)). Qed.
Lemma lem3485356 {A B : Type'} (f : type1374 A B) (x : A) (s : A -> Prop) (x' : B) : (term502 A B f s x' x) = (term398 A B f x s x').
Proof. exact (eq_refl (term502 A B f s x' x)). Qed.
Lemma lem3485357 {B : Type'} (g : B -> Prop) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem3485358 {A B : Type'} (f : type1374 A B) (x : A) (s : A -> Prop) (x' : B) (g : B -> Prop) : (term503 A B f s x' x g) = (term504 A B f x s x' g).
Proof. exact (MK_COMB (@lem3485356 A B f x s x') (@lem3485357 B g)). Qed.
Lemma lem3485359 {A B : Type'} (f : type1374 A B) (x : A) (s : A -> Prop) (x' : B) (g : B -> Prop) : (term504 A B f x s x' g) = (term389 A B f x s x' g).
Proof. exact (eq_refl (term504 A B f x s x' g)). Qed.
Lemma lem3485360 {A B : Type'} (f : type1374 A B) (x : A) (s : A -> Prop) (x' : B) (g : B -> Prop) : (term503 A B f s x' x g) = (term389 A B f x s x' g).
Proof. exact (TRANS (@lem3485358 A B f x s x' g) (@lem3485359 A B f x s x' g)). Qed.
Lemma lem3485361 {A B : Type'} (f : type1374 A B) (x : A) (s : A -> Prop) (x' : B) : (term505 A B f s x' x) = (term398 A B f x s x').
Proof. exact (fun_ext (fun g : B -> Prop => @lem3485360 A B f x s x' g)). Qed.
Lemma lem3485362 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem3485363 {A B : Type'} (f : type1374 A B) (x : A) (s : A -> Prop) (x' : B) : (term506 A B f s x' x) = (term399 A B f x s x').
Proof. exact (MK_COMB (@lem3485362 B) (@lem3485361 A B f x s x')). Qed.
Lemma lem3485364 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term507 A B f s x) = (term407 A B f s x).
Proof. exact (fun_ext (fun x' : A => @lem3485363 A B f x' s x)). Qed.
Lemma lem3485365 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3485366 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term499 A B f s x) = (term408 A B f s x).
Proof. exact (MK_COMB (@lem3485365 A) (@lem3485364 A B f s x)). Qed.
Lemma lem3485367 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3485368 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term508 A B f s x) = (term509 A B f s x).
Proof. exact (MK_COMB (@lem3485367) (@lem3485366 A B f s x)). Qed.
Lemma lem3485369 {A B : Type'} (f : type1374 A B) (x : A) (s : A -> Prop) (x' : B) : (term502 A B f s x' x) = (term398 A B f x s x').
Proof. exact (eq_refl (term502 A B f s x' x)). Qed.
Lemma lem3485370 {A B : Type'} (g : type1413 A B) (x : A) : (g x) = (g x).
Proof. exact (eq_refl (g x)). Qed.
Lemma lem3485371 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (x' : A) : (term510 A B f s x g x') = (term511 A B f s x g x').
Proof. exact (MK_COMB (@lem3485369 A B f x' s x) (@lem3485370 A B g x')). Qed.
Lemma lem3485372 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (x' : A) : (term511 A B f s x g x') = (term512 A B f s x g x').
Proof. exact (eq_refl (term511 A B f s x g x')). Qed.
Lemma lem3485373 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (x' : A) : (term510 A B f s x g x') = (term512 A B f s x g x').
Proof. exact (TRANS (@lem3485371 A B f s x g x') (@lem3485372 A B f s x g x')). Qed.
Lemma lem3485374 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) : (term513 A B f s x g) = (term514 A B f s x g).
Proof. exact (fun_ext (fun x' : A => @lem3485373 A B f s x g x')). Qed.
Lemma lem3485375 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3485376 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) : (term515 A B f s x g) = (term516 A B f s x g).
Proof. exact (MK_COMB (@lem3485375 A) (@lem3485374 A B f s x g)). Qed.
Lemma lem3485377 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term517 A B f s x) = (term518 A B f s x).
Proof. exact (fun_ext (fun g : type1413 A B => @lem3485376 A B f s x g)). Qed.
Lemma lem3485378 {A B : Type'} : (@ex (A -> B -> Prop)) = (@ex (A -> B -> Prop)).
Proof. exact (eq_refl (@ex (A -> B -> Prop))). Qed.
Lemma lem3485379 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term500 A B f s x) = (term519 A B f s x).
Proof. exact (MK_COMB (@lem3485378 A B) (@lem3485377 A B f s x)). Qed.
Lemma lem3485380 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : ((term499 A B f s x) = (term500 A B f s x)) = ((term408 A B f s x) = (term519 A B f s x)).
Proof. exact (MK_COMB (@lem3485368 A B f s x) (@lem3485379 A B f s x)). Qed.
Lemma lem3485381 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term408 A B f s x) = (term519 A B f s x).
Proof. exact (EQ_MP (@lem3485380 A B f s x) (@lem3485355 A B f s x)). Qed.
Lemma lem3485382 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) : (term410 A B s f x) = (term410 A B s f x).
Proof. exact (eq_refl (term410 A B s f x)). Qed.
Lemma lem3485383 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term412 A B f s x) = (term520 A B f s x).
Proof. exact (MK_COMB (@lem3485382 A B s f x) (@lem3485381 A B f s x)). Qed.
Lemma lem3485385 {A : Type'} (P : A -> Prop) (Q : Prop) : (term463 A P Q) = (term464 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3485386 {A : Type'} (P : A -> Prop) (Q : Prop) : (term463 A P Q) = (term464 A P Q).
Proof. exact (@lem3485385 A P Q). Qed.
Lemma lem3485387 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term521 A B f s x) = (term522 A B f s x).
Proof. exact (@lem3485386 A (term370 A B s f x) (term519 A B f s x)). Qed.
Lemma lem3485388 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : A) (x' : B) : (term523 A B s f x' x) = (term362 A B s f x x').
Proof. exact (eq_refl (term523 A B s f x' x)). Qed.
Lemma lem3485389 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) : (term524 A B s f x) = (term370 A B s f x).
Proof. exact (fun_ext (fun x' : A => @lem3485388 A B s f x' x)). Qed.
Lemma lem3485390 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3485391 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) : (term525 A B s f x) = (term371 A B s f x).
Proof. exact (MK_COMB (@lem3485390 A) (@lem3485389 A B s f x)). Qed.
Lemma lem3485392 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3485393 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) : (term526 A B s f x) = (term410 A B s f x).
Proof. exact (MK_COMB (@lem3485392) (@lem3485391 A B s f x)). Qed.
Lemma lem3485394 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term519 A B f s x) = (term519 A B f s x).
Proof. exact (eq_refl (term519 A B f s x)). Qed.
Lemma lem3485395 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term521 A B f s x) = (term520 A B f s x).
Proof. exact (MK_COMB (@lem3485393 A B s f x) (@lem3485394 A B f s x)). Qed.
Lemma lem3485396 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3485397 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term527 A B f s x) = (term528 A B f s x).
Proof. exact (MK_COMB (@lem3485396) (@lem3485395 A B f s x)). Qed.
Lemma lem3485398 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : A) (x' : B) : (term523 A B s f x' x) = (term362 A B s f x x').
Proof. exact (eq_refl (term523 A B s f x' x)). Qed.
Lemma lem3485399 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3485400 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : A) (x' : B) : (term529 A B s f x' x) = (term530 A B s f x x').
Proof. exact (MK_COMB (@lem3485399) (@lem3485398 A B s f x x')). Qed.
Lemma lem3485401 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term519 A B f s x) = (term519 A B f s x).
Proof. exact (eq_refl (term519 A B f s x)). Qed.
Lemma lem3485402 {A B : Type'} (x : A) (f : type1374 A B) (s : A -> Prop) (x' : B) : (term531 A B x f s x') = (term532 A B x f s x').
Proof. exact (MK_COMB (@lem3485400 A B s f x x') (@lem3485401 A B f s x')). Qed.
Lemma lem3485403 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term533 A B f s x) = (term534 A B f s x).
Proof. exact (fun_ext (fun x' : A => @lem3485402 A B x' f s x)). Qed.
Lemma lem3485404 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3485405 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term522 A B f s x) = (term535 A B f s x).
Proof. exact (MK_COMB (@lem3485404 A) (@lem3485403 A B f s x)). Qed.
Lemma lem3485406 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : ((term521 A B f s x) = (term522 A B f s x)) = ((term520 A B f s x) = (term535 A B f s x)).
Proof. exact (MK_COMB (@lem3485397 A B f s x) (@lem3485405 A B f s x)). Qed.
Lemma lem3485407 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term520 A B f s x) = (term535 A B f s x).
Proof. exact (EQ_MP (@lem3485406 A B f s x) (@lem3485387 A B f s x)). Qed.
Lemma lem3485409 {A : Type'} (P : Prop) (Q : A -> Prop) : (term482 A P Q) = (term483 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3485410 {A B : Type'} (P : Prop) (Q : type475 A B) : (term536 A B P Q) = (term537 A B P Q).
Proof. exact (@lem3485409 (type1413 A B) P Q). Qed.
Lemma lem3485411 {A B : Type'} (x : A) (f : type1374 A B) (s : A -> Prop) (x' : B) : (term538 A B x f s x') = (term539 A B x f s x').
Proof. exact (@lem3485410 A B (term362 A B s f x x') (term518 A B f s x')). Qed.
Lemma lem3485412 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) : (term540 A B f s x g) = (term516 A B f s x g).
Proof. exact (eq_refl (term540 A B f s x g)). Qed.
Lemma lem3485413 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term541 A B f s x) = (term518 A B f s x).
Proof. exact (fun_ext (fun g : type1413 A B => @lem3485412 A B f s x g)). Qed.
Lemma lem3485414 {A B : Type'} : (@ex (A -> B -> Prop)) = (@ex (A -> B -> Prop)).
Proof. exact (eq_refl (@ex (A -> B -> Prop))). Qed.
Lemma lem3485415 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term542 A B f s x) = (term519 A B f s x).
Proof. exact (MK_COMB (@lem3485414 A B) (@lem3485413 A B f s x)). Qed.
Lemma lem3485416 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : A) (x' : B) : (term530 A B s f x x') = (term530 A B s f x x').
Proof. exact (eq_refl (term530 A B s f x x')). Qed.
Lemma lem3485417 {A B : Type'} (x : A) (f : type1374 A B) (s : A -> Prop) (x' : B) : (term538 A B x f s x') = (term532 A B x f s x').
Proof. exact (MK_COMB (@lem3485416 A B s f x x') (@lem3485415 A B f s x')). Qed.
Lemma lem3485418 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3485419 {A B : Type'} (x : A) (f : type1374 A B) (s : A -> Prop) (x' : B) : (term543 A B x f s x') = (term544 A B x f s x').
Proof. exact (MK_COMB (@lem3485418) (@lem3485417 A B x f s x')). Qed.
Lemma lem3485420 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) : (term540 A B f s x g) = (term516 A B f s x g).
Proof. exact (eq_refl (term540 A B f s x g)). Qed.
Lemma lem3485421 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : A) (x' : B) : (term530 A B s f x x') = (term530 A B s f x x').
Proof. exact (eq_refl (term530 A B s f x x')). Qed.
Lemma lem3485422 {A B : Type'} (x : A) (f : type1374 A B) (s : A -> Prop) (x' : B) (g : type1413 A B) : (term545 A B x f s x' g) = (term546 A B x f s x' g).
Proof. exact (MK_COMB (@lem3485421 A B s f x x') (@lem3485420 A B f s x' g)). Qed.
Lemma lem3485423 {A B : Type'} (x : A) (f : type1374 A B) (s : A -> Prop) (x' : B) : (term547 A B x f s x') = (term548 A B x f s x').
Proof. exact (fun_ext (fun g : type1413 A B => @lem3485422 A B x f s x' g)). Qed.
Lemma lem3485424 {A B : Type'} : (@ex (A -> B -> Prop)) = (@ex (A -> B -> Prop)).
Proof. exact (eq_refl (@ex (A -> B -> Prop))). Qed.
Lemma lem3485425 {A B : Type'} (x : A) (f : type1374 A B) (s : A -> Prop) (x' : B) : (term539 A B x f s x') = (term549 A B x f s x').
Proof. exact (MK_COMB (@lem3485424 A B) (@lem3485423 A B x f s x')). Qed.
Lemma lem3485426 {A B : Type'} (x : A) (f : type1374 A B) (s : A -> Prop) (x' : B) : ((term538 A B x f s x') = (term539 A B x f s x')) = ((term532 A B x f s x') = (term549 A B x f s x')).
Proof. exact (MK_COMB (@lem3485419 A B x f s x') (@lem3485425 A B x f s x')). Qed.
Lemma lem3485427 {A B : Type'} (x : A) (f : type1374 A B) (s : A -> Prop) (x' : B) : (term532 A B x f s x') = (term549 A B x f s x').
Proof. exact (EQ_MP (@lem3485426 A B x f s x') (@lem3485411 A B x f s x')). Qed.
Lemma lem3485428 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term534 A B f s x) = (term550 A B f s x).
Proof. exact (fun_ext (fun x' : A => @lem3485427 A B x' f s x)). Qed.
Lemma lem3485429 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3485430 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term535 A B f s x) = (term551 A B f s x).
Proof. exact (MK_COMB (@lem3485429 A) (@lem3485428 A B f s x)). Qed.
Lemma lem3485431 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term520 A B f s x) = (term551 A B f s x).
Proof. exact (TRANS (@lem3485407 A B f s x) (@lem3485430 A B f s x)). Qed.
Lemma lem3485432 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term412 A B f s x) = (term551 A B f s x).
Proof. exact (TRANS (@lem3485383 A B f s x) (@lem3485431 A B f s x)). Qed.
Lemma lem3485433 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term420 A B f s x) = (term552 A B f s x).
Proof. exact (MK_COMB (@lem3485351 A B f s x) (@lem3485432 A B f s x)). Qed.
Lemma lem3485437 {A : Type'} (P : A -> Prop) (Q : Prop) : (term553 A P Q) = (term554 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3485438 {A B : Type'} (P : type475 A B) (Q : Prop) : (term555 A B P Q) = (term556 A B P Q).
Proof. exact (@lem3485437 (type1413 A B) P Q). Qed.
Lemma lem3485439 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term557 A B f s x) = (term558 A B f s x).
Proof. exact (@lem3485438 A B (term496 A B f s x) (term551 A B f s x)). Qed.
Lemma lem3485440 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (x : B) : (term559 A B f s x t) = (term495 A B t f s x).
Proof. exact (eq_refl (term559 A B f s x t)). Qed.
Lemma lem3485441 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term560 A B f s x) = (term496 A B f s x).
Proof. exact (fun_ext (fun t : type1413 A B => @lem3485440 A B t f s x)). Qed.
Lemma lem3485442 {A B : Type'} : (@ex (A -> B -> Prop)) = (@ex (A -> B -> Prop)).
Proof. exact (eq_refl (@ex (A -> B -> Prop))). Qed.
Lemma lem3485443 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term561 A B f s x) = (term497 A B f s x).
Proof. exact (MK_COMB (@lem3485442 A B) (@lem3485441 A B f s x)). Qed.
Lemma lem3485444 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3485445 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term562 A B f s x) = (term498 A B f s x).
Proof. exact (MK_COMB (@lem3485444) (@lem3485443 A B f s x)). Qed.
Lemma lem3485446 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term551 A B f s x) = (term551 A B f s x).
Proof. exact (eq_refl (term551 A B f s x)). Qed.
Lemma lem3485447 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term557 A B f s x) = (term552 A B f s x).
Proof. exact (MK_COMB (@lem3485445 A B f s x) (@lem3485446 A B f s x)). Qed.
Lemma lem3485448 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3485449 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term563 A B f s x) = (term564 A B f s x).
Proof. exact (MK_COMB (@lem3485448) (@lem3485447 A B f s x)). Qed.
Lemma lem3485450 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (x : B) : (term559 A B f s x t) = (term495 A B t f s x).
Proof. exact (eq_refl (term559 A B f s x t)). Qed.
Lemma lem3485451 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3485452 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (x : B) : (term565 A B f s x t) = (term566 A B t f s x).
Proof. exact (MK_COMB (@lem3485451) (@lem3485450 A B t f s x)). Qed.
Lemma lem3485453 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term551 A B f s x) = (term551 A B f s x).
Proof. exact (eq_refl (term551 A B f s x)). Qed.
Lemma lem3485454 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (x : B) : (term567 A B t f s x) = (term568 A B t f s x).
Proof. exact (MK_COMB (@lem3485452 A B t f s x) (@lem3485453 A B f s x)). Qed.
Lemma lem3485455 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term569 A B f s x) = (term570 A B f s x).
Proof. exact (fun_ext (fun t : type1413 A B => @lem3485454 A B t f s x)). Qed.
Lemma lem3485456 {A B : Type'} : (@ex (A -> B -> Prop)) = (@ex (A -> B -> Prop)).
Proof. exact (eq_refl (@ex (A -> B -> Prop))). Qed.
Lemma lem3485457 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term558 A B f s x) = (term571 A B f s x).
Proof. exact (MK_COMB (@lem3485456 A B) (@lem3485455 A B f s x)). Qed.
Lemma lem3485458 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : ((term557 A B f s x) = (term558 A B f s x)) = ((term552 A B f s x) = (term571 A B f s x)).
Proof. exact (MK_COMB (@lem3485449 A B f s x) (@lem3485457 A B f s x)). Qed.
Lemma lem3485459 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term552 A B f s x) = (term571 A B f s x).
Proof. exact (EQ_MP (@lem3485458 A B f s x) (@lem3485439 A B f s x)). Qed.
Lemma lem3485461 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term572 A P Q) = (term573 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3485462 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term572 A P Q) = (term573 A P Q).
Proof. exact (@lem3485461 A P Q). Qed.
Lemma lem3485463 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (x : B) : (term574 A B t f s x) = (term575 A B t f s x).
Proof. exact (@lem3485462 A (term494 A B t f s x) (term550 A B f s x)). Qed.
Lemma lem3485464 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (x : A) (s : A -> Prop) (x' : B) : (term576 A B t f s x' x) = (term492 A B t f x s x').
Proof. exact (eq_refl (term576 A B t f s x' x)). Qed.
Lemma lem3485465 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (x : B) : (term577 A B t f s x) = (term494 A B t f s x).
Proof. exact (fun_ext (fun x' : A => @lem3485464 A B t f x' s x)). Qed.
Lemma lem3485466 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3485467 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (x : B) : (term578 A B t f s x) = (term495 A B t f s x).
Proof. exact (MK_COMB (@lem3485466 A) (@lem3485465 A B t f s x)). Qed.
Lemma lem3485468 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3485469 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (x : B) : (term579 A B t f s x) = (term566 A B t f s x).
Proof. exact (MK_COMB (@lem3485468) (@lem3485467 A B t f s x)). Qed.
Lemma lem3485470 {A B : Type'} (x : A) (f : type1374 A B) (s : A -> Prop) (x' : B) : (term580 A B f s x' x) = (term549 A B x f s x').
Proof. exact (eq_refl (term580 A B f s x' x)). Qed.
Lemma lem3485471 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term581 A B f s x) = (term550 A B f s x).
Proof. exact (fun_ext (fun x' : A => @lem3485470 A B x' f s x)). Qed.
Lemma lem3485472 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3485473 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term582 A B f s x) = (term551 A B f s x).
Proof. exact (MK_COMB (@lem3485472 A) (@lem3485471 A B f s x)). Qed.
Lemma lem3485474 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (x : B) : (term574 A B t f s x) = (term568 A B t f s x).
Proof. exact (MK_COMB (@lem3485469 A B t f s x) (@lem3485473 A B f s x)). Qed.
Lemma lem3485475 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3485476 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (x : B) : (term583 A B t f s x) = (term584 A B t f s x).
Proof. exact (MK_COMB (@lem3485475) (@lem3485474 A B t f s x)). Qed.
Lemma lem3485477 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (x : A) (s : A -> Prop) (x' : B) : (term576 A B t f s x' x) = (term492 A B t f x s x').
Proof. exact (eq_refl (term576 A B t f s x' x)). Qed.
Lemma lem3485478 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3485479 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (x : A) (s : A -> Prop) (x' : B) : (term585 A B t f s x' x) = (term586 A B t f x s x').
Proof. exact (MK_COMB (@lem3485478) (@lem3485477 A B t f x s x')). Qed.
Lemma lem3485480 {A B : Type'} (x : A) (f : type1374 A B) (s : A -> Prop) (x' : B) : (term580 A B f s x' x) = (term549 A B x f s x').
Proof. exact (eq_refl (term580 A B f s x' x)). Qed.
Lemma lem3485481 {A B : Type'} (t : type1413 A B) (x : A) (f : type1374 A B) (s : A -> Prop) (x' : B) : (term587 A B t f s x' x) = (term588 A B t x f s x').
Proof. exact (MK_COMB (@lem3485479 A B t f x s x') (@lem3485480 A B x f s x')). Qed.
Lemma lem3485482 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (x : B) : (term589 A B t f s x) = (term590 A B t f s x).
Proof. exact (fun_ext (fun x' : A => @lem3485481 A B t x' f s x)). Qed.
Lemma lem3485483 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3485484 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (x : B) : (term575 A B t f s x) = (term591 A B t f s x).
Proof. exact (MK_COMB (@lem3485483 A) (@lem3485482 A B t f s x)). Qed.
Lemma lem3485485 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (x : B) : ((term574 A B t f s x) = (term575 A B t f s x)) = ((term568 A B t f s x) = (term591 A B t f s x)).
Proof. exact (MK_COMB (@lem3485476 A B t f s x) (@lem3485484 A B t f s x)). Qed.
Lemma lem3485486 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (x : B) : (term568 A B t f s x) = (term591 A B t f s x).
Proof. exact (EQ_MP (@lem3485485 A B t f s x) (@lem3485463 A B t f s x)). Qed.
Lemma lem3485488 {A : Type'} (P : Prop) (Q : A -> Prop) : (term421 A P Q) = (term422 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3485489 {A B : Type'} (P : Prop) (Q : type475 A B) : (term592 A B P Q) = (term593 A B P Q).
Proof. exact (@lem3485488 (type1413 A B) P Q). Qed.
Lemma lem3485490 {A B : Type'} (t : type1413 A B) (x : A) (f : type1374 A B) (s : A -> Prop) (x' : B) : (term594 A B t x f s x') = (term595 A B t x f s x').
Proof. exact (@lem3485489 A B (term492 A B t f x s x') (term548 A B x f s x')). Qed.
Lemma lem3485491 {A B : Type'} (x : A) (f : type1374 A B) (s : A -> Prop) (x' : B) (g : type1413 A B) : (term596 A B x f s x' g) = (term546 A B x f s x' g).
Proof. exact (eq_refl (term596 A B x f s x' g)). Qed.
Lemma lem3485492 {A B : Type'} (x : A) (f : type1374 A B) (s : A -> Prop) (x' : B) : (term597 A B x f s x') = (term548 A B x f s x').
Proof. exact (fun_ext (fun g : type1413 A B => @lem3485491 A B x f s x' g)). Qed.
Lemma lem3485493 {A B : Type'} : (@ex (A -> B -> Prop)) = (@ex (A -> B -> Prop)).
Proof. exact (eq_refl (@ex (A -> B -> Prop))). Qed.
Lemma lem3485494 {A B : Type'} (x : A) (f : type1374 A B) (s : A -> Prop) (x' : B) : (term598 A B x f s x') = (term549 A B x f s x').
Proof. exact (MK_COMB (@lem3485493 A B) (@lem3485492 A B x f s x')). Qed.
Lemma lem3485495 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (x : A) (s : A -> Prop) (x' : B) : (term586 A B t f x s x') = (term586 A B t f x s x').
Proof. exact (eq_refl (term586 A B t f x s x')). Qed.
Lemma lem3485496 {A B : Type'} (t : type1413 A B) (x : A) (f : type1374 A B) (s : A -> Prop) (x' : B) : (term594 A B t x f s x') = (term588 A B t x f s x').
Proof. exact (MK_COMB (@lem3485495 A B t f x s x') (@lem3485494 A B x f s x')). Qed.
Lemma lem3485497 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3485498 {A B : Type'} (t : type1413 A B) (x : A) (f : type1374 A B) (s : A -> Prop) (x' : B) : (term599 A B t x f s x') = (term600 A B t x f s x').
Proof. exact (MK_COMB (@lem3485497) (@lem3485496 A B t x f s x')). Qed.
Lemma lem3485499 {A B : Type'} (x : A) (f : type1374 A B) (s : A -> Prop) (x' : B) (g : type1413 A B) : (term596 A B x f s x' g) = (term546 A B x f s x' g).
Proof. exact (eq_refl (term596 A B x f s x' g)). Qed.
Lemma lem3485500 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (x : A) (s : A -> Prop) (x' : B) : (term586 A B t f x s x') = (term586 A B t f x s x').
Proof. exact (eq_refl (term586 A B t f x s x')). Qed.
Lemma lem3485501 {A B : Type'} (t : type1413 A B) (x : A) (f : type1374 A B) (s : A -> Prop) (x' : B) (g : type1413 A B) : (term601 A B t x f s x' g) = (term602 A B t x f s x' g).
Proof. exact (MK_COMB (@lem3485500 A B t f x s x') (@lem3485499 A B x f s x' g)). Qed.
Lemma lem3485502 {A B : Type'} (t : type1413 A B) (x : A) (f : type1374 A B) (s : A -> Prop) (x' : B) : (term603 A B t x f s x') = (term604 A B t x f s x').
Proof. exact (fun_ext (fun g : type1413 A B => @lem3485501 A B t x f s x' g)). Qed.
Lemma lem3485503 {A B : Type'} : (@ex (A -> B -> Prop)) = (@ex (A -> B -> Prop)).
Proof. exact (eq_refl (@ex (A -> B -> Prop))). Qed.
Lemma lem3485504 {A B : Type'} (t : type1413 A B) (x : A) (f : type1374 A B) (s : A -> Prop) (x' : B) : (term595 A B t x f s x') = (term605 A B t x f s x').
Proof. exact (MK_COMB (@lem3485503 A B) (@lem3485502 A B t x f s x')). Qed.
Lemma lem3485505 {A B : Type'} (t : type1413 A B) (x : A) (f : type1374 A B) (s : A -> Prop) (x' : B) : ((term594 A B t x f s x') = (term595 A B t x f s x')) = ((term588 A B t x f s x') = (term605 A B t x f s x')).
Proof. exact (MK_COMB (@lem3485498 A B t x f s x') (@lem3485504 A B t x f s x')). Qed.
Lemma lem3485506 {A B : Type'} (t : type1413 A B) (x : A) (f : type1374 A B) (s : A -> Prop) (x' : B) : (term588 A B t x f s x') = (term605 A B t x f s x').
Proof. exact (EQ_MP (@lem3485505 A B t x f s x') (@lem3485490 A B t x f s x')). Qed.
Lemma lem3485507 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (x : B) : (term590 A B t f s x) = (term606 A B t f s x).
Proof. exact (fun_ext (fun x' : A => @lem3485506 A B t x' f s x)). Qed.
Lemma lem3485508 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3485509 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (x : B) : (term591 A B t f s x) = (term607 A B t f s x).
Proof. exact (MK_COMB (@lem3485508 A) (@lem3485507 A B t f s x)). Qed.
Lemma lem3485510 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (x : B) : (term568 A B t f s x) = (term607 A B t f s x).
Proof. exact (TRANS (@lem3485486 A B t f s x) (@lem3485509 A B t f s x)). Qed.
Lemma lem3485511 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term570 A B f s x) = (term608 A B f s x).
Proof. exact (fun_ext (fun t : type1413 A B => @lem3485510 A B t f s x)). Qed.
Lemma lem3485512 {A B : Type'} : (@ex (A -> B -> Prop)) = (@ex (A -> B -> Prop)).
Proof. exact (eq_refl (@ex (A -> B -> Prop))). Qed.
Lemma lem3485513 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term571 A B f s x) = (term609 A B f s x).
Proof. exact (MK_COMB (@lem3485512 A B) (@lem3485511 A B f s x)). Qed.
Lemma lem3485514 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term552 A B f s x) = (term609 A B f s x).
Proof. exact (TRANS (@lem3485459 A B f s x) (@lem3485513 A B f s x)). Qed.
Lemma lem3485516 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term420 A B f s x) = (term609 A B f s x).
Proof. exact (TRANS (@lem3485433 A B f s x) (@lem3485514 A B f s x)). Qed.
Lemma lem3485517 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term325 A B f s x) = (term609 A B f s x).
Proof. exact (TRANS (@lem3484945 A B f s x) (@lem3485516 A B f s x)). Qed.
Lemma lem3485518 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (h1 : term325 A B f s x) : term609 A B f s x.
Proof. exact (EQ_MP (@lem3485517 A B f s x) (@lem3484820 A B f s x h1)). Qed.
Lemma lem3485519 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (x : B) (h1 : term607 A B t f s x) : term607 A B t f s x.
Proof. exact (h1). Qed.
Lemma lem3485520 {A B : Type'} (t : type1413 A B) (x' : A) (f : type1374 A B) (s : A -> Prop) (x : B) (h1 : term605 A B t x' f s x) : term605 A B t x' f s x.
Proof. exact (h1). Qed.
Lemma lem3485521 {A B : Type'} (t : type1413 A B) (x' : A) (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (h1 : term602 A B t x' f s x g) : term602 A B t x' f s x g.
Proof. exact (h1). Qed.
Lemma lem3485562 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (x' : A) : (term512 A B f s x g x') = (term512 A B f s x g x').
Proof. exact (eq_refl (term512 A B f s x g x')). Qed.
Lemma lem3485563 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) : (term514 A B f s x g) = (term514 A B f s x g).
Proof. exact (fun_ext (fun x' : A => @lem3485562 A B f s x g x')). Qed.
Lemma lem3485564 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3485565 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) : (term516 A B f s x g) = (term516 A B f s x g).
Proof. exact (MK_COMB (@lem3485564 A) (@lem3485563 A B f s x g)). Qed.
Lemma lem3485582 {A B : Type'} (f : type1374 A B) (x' : A) (x : B) (t : B -> Prop) : (term347 A B f x' x t) = (term347 A B f x' x t).
Proof. exact (eq_refl (term347 A B f x' x t)). Qed.
Lemma lem3485583 {A B : Type'} (f : type1374 A B) (x' : A) (x : B) : (term357 A B f x' x) = (term357 A B f x' x).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3485582 A B f x' x t)). Qed.
Lemma lem3485584 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3485585 {A B : Type'} (f : type1374 A B) (x' : A) (x : B) : (term358 A B f x' x) = (term358 A B f x' x).
Proof. exact (MK_COMB (@lem3485584 B) (@lem3485583 A B f x' x)). Qed.
Lemma lem3485592 {A : Type'} (x' : A) (s : A -> Prop) : (term99 A x' s) = (term99 A x' s).
Proof. exact (eq_refl (term99 A x' s)). Qed.
Lemma lem3485593 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x' : A) (x : B) : (term362 A B s f x' x) = (term362 A B s f x' x).
Proof. exact (MK_COMB (@lem3485592 A x' s) (@lem3485585 A B f x' x)). Qed.
Lemma lem3485594 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3485595 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x' : A) (x : B) : (term530 A B s f x' x) = (term530 A B s f x' x).
Proof. exact (MK_COMB (@lem3485594) (@lem3485593 A B s f x' x)). Qed.
Lemma lem3485596 {A B : Type'} (x' : A) (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) : (term546 A B x' f s x g) = (term546 A B x' f s x g).
Proof. exact (MK_COMB (@lem3485595 A B s f x' x) (@lem3485565 A B f s x g)). Qed.
Lemma lem3485629 {A B : Type'} (f : type1374 A B) (x' : A) (s : A -> Prop) (x : B) (g : B -> Prop) : (term385 A B f x' s x g) = (term385 A B f x' s x g).
Proof. exact (eq_refl (term385 A B f x' s x g)). Qed.
Lemma lem3485630 {A B : Type'} (f : type1374 A B) (x' : A) (s : A -> Prop) (x : B) : (term396 A B f x' s x) = (term396 A B f x' s x).
Proof. exact (fun_ext (fun g : B -> Prop => @lem3485629 A B f x' s x g)). Qed.
Lemma lem3485631 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3485632 {A B : Type'} (f : type1374 A B) (x' : A) (s : A -> Prop) (x : B) : (term397 A B f x' s x) = (term397 A B f x' s x).
Proof. exact (MK_COMB (@lem3485631 B) (@lem3485630 A B f x' s x)). Qed.
Lemma lem3485663 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) (t : type1413 A B) (x' : A) : (term453 A B s f x t x') = (term453 A B s f x t x').
Proof. exact (eq_refl (term453 A B s f x t x')). Qed.
Lemma lem3485664 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) (t : type1413 A B) : (term455 A B s f x t) = (term455 A B s f x t).
Proof. exact (fun_ext (fun x' : A => @lem3485663 A B s f x t x')). Qed.
Lemma lem3485665 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3485666 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) (t : type1413 A B) : (term457 A B s f x t) = (term457 A B s f x t).
Proof. exact (MK_COMB (@lem3485665 A) (@lem3485664 A B s f x t)). Qed.
Lemma lem3485667 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3485668 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x : B) (t : type1413 A B) : (term476 A B s f x t) = (term476 A B s f x t).
Proof. exact (MK_COMB (@lem3485667) (@lem3485666 A B s f x t)). Qed.
Lemma lem3485669 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (x' : A) (s : A -> Prop) (x : B) : (term492 A B t f x' s x) = (term492 A B t f x' s x).
Proof. exact (MK_COMB (@lem3485668 A B s f x t) (@lem3485632 A B f x' s x)). Qed.
Lemma lem3485670 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3485671 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (x' : A) (s : A -> Prop) (x : B) : (term586 A B t f x' s x) = (term586 A B t f x' s x).
Proof. exact (MK_COMB (@lem3485670) (@lem3485669 A B t f x' s x)). Qed.
Lemma lem3485672 {A B : Type'} (t : type1413 A B) (x' : A) (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) : (term602 A B t x' f s x g) = (term602 A B t x' f s x g).
Proof. exact (MK_COMB (@lem3485671 A B t f x' s x) (@lem3485596 A B x' f s x g)). Qed.
Lemma lem3485673 {A B : Type'} (t : type1413 A B) (x' : A) (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (h1 : term602 A B t x' f s x g) : term602 A B t x' f s x g.
Proof. exact (EQ_MP (@lem3485672 A B t x' f s x g) (@lem3485521 A B t x' f s x g h1)). Qed.
Lemma lem3485674 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (x' : A) (s : A -> Prop) (x : B) (h1 : term492 A B t f x' s x) : term492 A B t f x' s x.
Proof. exact (h1). Qed.
Lemma lem3485675 {A B : Type'} (x' : A) (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (h1 : term546 A B x' f s x g) : term546 A B x' f s x g.
Proof. exact (h1). Qed.
Lemma lem3485676 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (x' : A) (s : A -> Prop) (x : B) (h1 : term492 A B t f x' s x) : term397 A B f x' s x.
Proof. exact (proj2 (@lem3485674 A B t f x' s x h1)). Qed.
Lemma lem3485677 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (x' : A) (s : A -> Prop) (x : B) (h1 : term492 A B t f x' s x) : term457 A B s f x t.
Proof. exact (proj1 (@lem3485674 A B t f x' s x h1)). Qed.
Lemma lem3485678 {A B : Type'} (x' : A) (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (h1 : term546 A B x' f s x g) : term516 A B f s x g.
Proof. exact (proj2 (@lem3485675 A B x' f s x g h1)). Qed.
Lemma lem3485679 {A B : Type'} (x' : A) (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (h1 : term546 A B x' f s x g) : term362 A B s f x' x.
Proof. exact (proj1 (@lem3485675 A B x' f s x g h1)). Qed.
Lemma lem3485680 {A B : Type'} (x' : A) (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (h1 : term546 A B x' f s x g) : term358 A B f x' x.
Proof. exact (proj2 (@lem3485679 A B x' f s x g h1)). Qed.
Lemma lem3485699 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (t : type1413 A B) (x' : A) : (term453 A B s f x t x') = (term512 A B f s x t x').
Proof. exact (@lem19490 (term610 A B t f x') (term427 A x' s) (term611 A B x t x')). Qed.
Lemma lem3485700 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (t : type1413 A B) : (term455 A B s f x t) = (term514 A B f s x t).
Proof. exact (fun_ext (fun x' : A => @lem3485699 A B f s x t x')). Qed.
Lemma lem3485701 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3485703 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (t : type1413 A B) : (term457 A B s f x t) = (term516 A B f s x t).
Proof. exact (MK_COMB (@lem3485701 A) (@lem3485700 A B f s x t)). Qed.
Lemma lem3485704 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (x' : A) (s : A -> Prop) (x : B) (h1 : term492 A B t f x' s x) : term516 A B f s x t.
Proof. exact (EQ_MP (@lem3485703 A B f s x t) (@lem3485677 A B t f x' s x h1)). Qed.
Lemma lem3485719 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x' : A) (x : B) (g : B -> Prop) : (term385 A B f x' s x g) = (term612 A B s f x' x g).
Proof. exact (@lem19490 (@IN A x' s) (term375 A B s g f x') (@IN B x g)). Qed.
Lemma lem3485726 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x' : A) (x : B) (g : B -> Prop) : (term613 A B s f x' x g) = (term614 A B s f x' x g).
Proof. exact (@lem19699 (@IN A x' s) (term615 A B g f x') (@IN B x g)). Qed.
Lemma lem3485733 {A B : Type'} (g : B -> Prop) (f : type1374 A B) (x' : A) (s : A -> Prop) : (term616 A B g f x' s) = (term617 A B g f x' s).
Proof. exact (@lem19699 (@IN A x' s) (term615 A B g f x') (@IN A x' s)). Qed.
Lemma lem3485734 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3485735 {A B : Type'} (g : B -> Prop) (f : type1374 A B) (x' : A) (s : A -> Prop) : (term618 A B g f x' s) = (term619 A B g f x' s).
Proof. exact (MK_COMB (@lem3485734) (@lem3485733 A B g f x' s)). Qed.
Lemma lem3485736 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x' : A) (x : B) (g : B -> Prop) : (term612 A B s f x' x g) = (term620 A B s f x' x g).
Proof. exact (MK_COMB (@lem3485735 A B g f x' s) (@lem3485726 A B s f x' x g)). Qed.
Lemma lem3485738 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x' : A) (x : B) (g : B -> Prop) : (term385 A B f x' s x g) = (term620 A B s f x' x g).
Proof. exact (TRANS (@lem3485719 A B s f x' x g) (@lem3485736 A B s f x' x g)). Qed.
Lemma lem3485739 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x' : A) (x : B) : (term396 A B f x' s x) = (term621 A B s f x' x).
Proof. exact (fun_ext (fun g : B -> Prop => @lem3485738 A B s f x' x g)). Qed.
Lemma lem3485740 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3485742 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x' : A) (x : B) : (term397 A B f x' s x) = (term622 A B s f x' x).
Proof. exact (MK_COMB (@lem3485740 B) (@lem3485739 A B s f x' x)). Qed.
Lemma lem3485743 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (x' : A) (s : A -> Prop) (x : B) (h1 : term492 A B t f x' s x) : term622 A B s f x' x.
Proof. exact (EQ_MP (@lem3485742 A B s f x' x) (@lem3485676 A B t f x' s x h1)). Qed.
Lemma lem3485761 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (x' : A) : (term512 A B f s x g x') = (term512 A B f s x g x').
Proof. exact (eq_refl (term512 A B f s x g x')). Qed.
Lemma lem3485762 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) : (term514 A B f s x g) = (term514 A B f s x g).
Proof. exact (fun_ext (fun x' : A => @lem3485761 A B f s x g x')). Qed.
Lemma lem3485763 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3485765 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) : (term516 A B f s x g) = (term516 A B f s x g).
Proof. exact (MK_COMB (@lem3485763 A) (@lem3485762 A B f s x g)). Qed.
Lemma lem3485766 {A B : Type'} (x' : A) (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (h1 : term546 A B x' f s x g) : term516 A B f s x g.
Proof. exact (EQ_MP (@lem3485765 A B f s x g) (@lem3485678 A B x' f s x g h1)). Qed.
Lemma lem3485778 {A B : Type'} (f : type1374 A B) (x' : A) (x : B) (t : B -> Prop) : (term347 A B f x' x t) = (term347 A B f x' x t).
Proof. exact (eq_refl (term347 A B f x' x t)). Qed.
Lemma lem3485779 {A B : Type'} (f : type1374 A B) (x' : A) (x : B) : (term357 A B f x' x) = (term357 A B f x' x).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3485778 A B f x' x t)). Qed.
Lemma lem3485780 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3485782 {A B : Type'} (f : type1374 A B) (x' : A) (x : B) : (term358 A B f x' x) = (term358 A B f x' x).
Proof. exact (MK_COMB (@lem3485780 B) (@lem3485779 A B f x' x)). Qed.
Lemma lem3485783 {A B : Type'} (x' : A) (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (h1 : term546 A B x' f s x g) : term358 A B f x' x.
Proof. exact (EQ_MP (@lem3485782 A B f x' x) (@lem3485680 A B x' f s x g h1)). Qed.
Lemma lem3485784 {A B : Type'} (_36717 : A) (t : type1413 A B) (f : type1374 A B) (x' : A) (s : A -> Prop) (x : B) (h1 : term492 A B t f x' s x) : term623 A B f s x t _36717.
Proof. exact (@lem3485704 A B t f x' s x h1 _36717). Qed.
Lemma lem3485785 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (t : type1413 A B) (_36717 : A) : (term623 A B f s x t _36717) = (term512 A B f s x t _36717).
Proof. exact (eq_refl (term623 A B f s x t _36717)). Qed.
Lemma lem3485786 {A B : Type'} (_36717 : A) (t : type1413 A B) (f : type1374 A B) (x' : A) (s : A -> Prop) (x : B) (h1 : term492 A B t f x' s x) : term512 A B f s x t _36717.
Proof. exact (EQ_MP (@lem3485785 A B f s x t _36717) (@lem3485784 A B _36717 t f x' s x h1)). Qed.
Lemma lem3485787 {A B : Type'} (_36718 : B -> Prop) (t : type1413 A B) (f : type1374 A B) (x' : A) (s : A -> Prop) (x : B) (h1 : term492 A B t f x' s x) : term624 A B s f x' x _36718.
Proof. exact (@lem3485743 A B t f x' s x h1 _36718). Qed.
Lemma lem3485788 {A B : Type'} (s : A -> Prop) (f : type1374 A B) (x' : A) (x : B) (_36718 : B -> Prop) : (term624 A B s f x' x _36718) = (term620 A B s f x' x _36718).
Proof. exact (eq_refl (term624 A B s f x' x _36718)). Qed.
Lemma lem3485789 {A B : Type'} (_36718 : B -> Prop) (t : type1413 A B) (f : type1374 A B) (x' : A) (s : A -> Prop) (x : B) (h1 : term492 A B t f x' s x) : term620 A B s f x' x _36718.
Proof. exact (EQ_MP (@lem3485788 A B s f x' x _36718) (@lem3485787 A B _36718 t f x' s x h1)). Qed.
Lemma lem3485790 {A B : Type'} (_36719 : A) (x' : A) (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (h1 : term546 A B x' f s x g) : term623 A B f s x g _36719.
Proof. exact (@lem3485766 A B x' f s x g h1 _36719). Qed.
Lemma lem3485791 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (_36719 : A) : (term623 A B f s x g _36719) = (term512 A B f s x g _36719).
Proof. exact (eq_refl (term623 A B f s x g _36719)). Qed.
Lemma lem3485792 {A B : Type'} (_36719 : A) (x' : A) (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (h1 : term546 A B x' f s x g) : term512 A B f s x g _36719.
Proof. exact (EQ_MP (@lem3485791 A B f s x g _36719) (@lem3485790 A B _36719 x' f s x g h1)). Qed.
Lemma lem3485793 {A B : Type'} (_36720 : B -> Prop) (x' : A) (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (h1 : term546 A B x' f s x g) : term625 A B f x' x _36720.
Proof. exact (@lem3485783 A B x' f s x g h1 _36720). Qed.
Lemma lem3485794 {A B : Type'} (f : type1374 A B) (x' : A) (x : B) (_36720 : B -> Prop) : (term625 A B f x' x _36720) = (term347 A B f x' x _36720).
Proof. exact (eq_refl (term625 A B f x' x _36720)). Qed.
Lemma lem3485796 {A B : Type'} (_36718 : B -> Prop) (t : type1413 A B) (f : type1374 A B) (x' : A) (s : A -> Prop) (x : B) (h1 : term492 A B t f x' s x) : term614 A B s f x' x _36718.
Proof. exact (proj2 (@lem3485789 A B _36718 t f x' s x h1)). Qed.
Lemma lem3485797 {A B : Type'} (_36718 : B -> Prop) (t : type1413 A B) (f : type1374 A B) (x' : A) (s : A -> Prop) (x : B) (h1 : term492 A B t f x' s x) : term617 A B _36718 f x' s.
Proof. exact (proj1 (@lem3485789 A B _36718 t f x' s x h1)). Qed.
Lemma lem3485817 {A B : Type'} (_36718 : B -> Prop) (t : type1413 A B) (f : type1374 A B) (x' : A) (s : A -> Prop) (x : B) (h1 : term492 A B t f x' s x) : term347 A B f x' x _36718.
Proof. exact (proj2 (@lem3485796 A B _36718 t f x' s x h1)). Qed.
Lemma lem3485823 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (x' : A) (s : A -> Prop) (x : B) (h1 : term492 A B t f x' s x) : term626 A x' s.
Proof. exact (proj1 (@lem3485797 A B (@el (B -> Prop)) t f x' s x h1)). Qed.
Lemma lem3485835 {A B : Type'} (_36717 : A) (t : type1413 A B) (f : type1374 A B) (x' : A) (s : A -> Prop) (x : B) (h1 : term492 A B t f x' s x) : term627 A B s t f _36717.
Proof. exact (proj1 (@lem3485786 A B _36717 t f x' s x h1)). Qed.
Lemma lem3485841 {A B : Type'} (_36717 : A) (t : type1413 A B) (f : type1374 A B) (x' : A) (s : A -> Prop) (x : B) (h1 : term492 A B t f x' s x) : term628 A B s x t _36717.
Proof. exact (proj2 (@lem3485786 A B _36717 t f x' s x h1)). Qed.
Lemma lem3485849 {A B : Type'} (_36720 : B -> Prop) (x' : A) (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (h1 : term546 A B x' f s x g) : term347 A B f x' x _36720.
Proof. exact (EQ_MP (@lem3485794 A B f x' x _36720) (@lem3485793 A B _36720 x' f s x g h1)). Qed.
Lemma lem3485855 {A B : Type'} (_36719 : A) (x' : A) (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (h1 : term546 A B x' f s x g) : term627 A B s g f _36719.
Proof. exact (proj1 (@lem3485792 A B _36719 x' f s x g h1)). Qed.
Lemma lem3485861 {A B : Type'} (_36719 : A) (x' : A) (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (h1 : term546 A B x' f s x g) : term628 A B s x g _36719.
Proof. exact (proj2 (@lem3485792 A B _36719 x' f s x g h1)). Qed.
Lemma lem3485864 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term427 A x' s) : term427 A x' s.
Proof. exact (h1). Qed.
Lemma lem3485865 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term427 A x' s) : term629 A x' s.
Proof. exact (fun h0 : @IN A x' s => @lem3485864 A x' s h1). Qed.
Lemma lem3485867 (p : Prop) : (term630 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3485868 {A : Type'} (x' : A) (s : A -> Prop) : (term629 A x' s) = (term427 A x' s).
Proof. exact (@lem3485867 (@IN A x' s)). Qed.
Lemma lem3485869 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term427 A x' s) : term427 A x' s.
Proof. exact (EQ_MP (@lem3485868 A x' s) (@lem3485865 A x' s h1)). Qed.
Lemma lem3485871 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3485872 (x : Prop) : (x = x) = True.
Proof. exact (@lem3485871 Prop x). Qed.
Lemma lem3485873 {A : Type'} (x' : A) (s : A -> Prop) : ((term626 A x' s) = (term626 A x' s)) = True.
Proof. exact (@lem3485872 (term626 A x' s)). Qed.
Lemma lem3485874 {A : Type'} (x' : A) (s : A -> Prop) : True = ((term626 A x' s) = (term626 A x' s)).
Proof. exact (SYM (@lem3485873 A x' s)). Qed.
Lemma lem3485875 {A : Type'} (x' : A) (s : A -> Prop) : (term626 A x' s) = (term626 A x' s).
Proof. exact (EQ_MP (@lem3485874 A x' s) (@lem0)). Qed.
Lemma lem3485876 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (x' : A) (s : A -> Prop) (x : B) (h1 : term492 A B t f x' s x) : term626 A x' s.
Proof. exact (EQ_MP (@lem3485875 A x' s) (@lem3485823 A B t f x' s x h1)). Qed.
Lemma lem3485878 (b : Prop) (a : Prop) : (a \/ b) = (term631 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3485881 {A : Type'} (x' : A) (s : A -> Prop) : (term626 A x' s) = (term632 A x' s).
Proof. exact (@lem3485878 (@IN A x' s) (@IN A x' s)). Qed.
Lemma lem3485884 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (x' : A) (s : A -> Prop) (x : B) (h1 : term492 A B t f x' s x) : term632 A x' s.
Proof. exact (EQ_MP (@lem3485881 A x' s) (@lem3485876 A B t f x' s x h1)). Qed.
Lemma lem3485887 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (x' : A) (s : A -> Prop) (x : B) (h1 : term427 A x' s) (h2 : term492 A B t f x' s x) : @IN A x' s.
Proof. exact (@lem3485884 A B t f x' s x h2 (@lem3485869 A x' s h1)). Qed.
Lemma lem3485888 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (x' : A) (s : A -> Prop) (x : B) (h1 : term492 A B t f x' s x) : term632 A x' s.
Proof. exact (fun h0 : term427 A x' s => @lem3485887 A B t f x' s x h0 h1). Qed.
Lemma lem3485890 (p : Prop) : (term633 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3485891 {A : Type'} (x' : A) (s : A -> Prop) : (term632 A x' s) = (@IN A x' s).
Proof. exact (@lem3485890 (@IN A x' s)). Qed.
Lemma lem3485892 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (x' : A) (s : A -> Prop) (x : B) (h1 : term492 A B t f x' s x) : @IN A x' s.
Proof. exact (EQ_MP (@lem3485891 A x' s) (@lem3485888 A B t f x' s x h1)). Qed.
Lemma lem3485895 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term427 A x' s) : term427 A x' s.
Proof. exact (h1). Qed.
Lemma lem3485896 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term427 A x' s) : term629 A x' s.
Proof. exact (fun h0 : @IN A x' s => @lem3485895 A x' s h1). Qed.
Lemma lem3485898 (p : Prop) : (term630 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3485899 {A : Type'} (x' : A) (s : A -> Prop) : (term629 A x' s) = (term427 A x' s).
Proof. exact (@lem3485898 (@IN A x' s)). Qed.
Lemma lem3485900 {A : Type'} (x' : A) (s : A -> Prop) (h1 : term427 A x' s) : term427 A x' s.
Proof. exact (EQ_MP (@lem3485899 A x' s) (@lem3485896 A x' s h1)). Qed.
Lemma lem3485902 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (x' : A) (s : A -> Prop) (x : B) (h1 : term492 A B t f x' s x) : term632 A x' s.
Proof. exact (EQ_MP (@lem3485881 A x' s) (@lem3485876 A B t f x' s x h1)). Qed.
Lemma lem3485905 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (x' : A) (s : A -> Prop) (x : B) (h1 : term427 A x' s) (h2 : term492 A B t f x' s x) : @IN A x' s.
Proof. exact (@lem3485902 A B t f x' s x h2 (@lem3485900 A x' s h1)). Qed.
Lemma lem3485906 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (x' : A) (s : A -> Prop) (x : B) (h1 : term492 A B t f x' s x) : term632 A x' s.
Proof. exact (fun h0 : term427 A x' s => @lem3485905 A B t f x' s x h0 h1). Qed.
Lemma lem3485908 (p : Prop) : (term633 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3485909 {A : Type'} (x' : A) (s : A -> Prop) : (term632 A x' s) = (@IN A x' s).
Proof. exact (@lem3485908 (@IN A x' s)). Qed.
Lemma lem3485910 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (x' : A) (s : A -> Prop) (x : B) (h1 : term492 A B t f x' s x) : @IN A x' s.
Proof. exact (EQ_MP (@lem3485909 A x' s) (@lem3485906 A B t f x' s x h1)). Qed.
Lemma lem3485916 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3485917 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (_36717 : A) (s : A -> Prop) : (term627 A B s t f _36717) = (term634 A B t f _36717 s).
Proof. exact (@lem3485916 (term610 A B t f _36717) (term427 A _36717 s)). Qed.
Lemma lem3485923 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3485924 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (_36717 : A) (s : A -> Prop) : (term635 A B s t f _36717) = (term636 A B t f _36717 s).
Proof. exact (MK_COMB (@lem3485923) (@lem3485917 A B t f _36717 s)). Qed.
Lemma lem3485930 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (_36717 : A) (s : A -> Prop) : (term634 A B t f _36717 s) = (term634 A B t f _36717 s).
Proof. exact (eq_refl (term634 A B t f _36717 s)). Qed.
Lemma lem3485931 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (_36717 : A) (s : A -> Prop) : ((term627 A B s t f _36717) = (term634 A B t f _36717 s)) = ((term634 A B t f _36717 s) = (term634 A B t f _36717 s)).
Proof. exact (MK_COMB (@lem3485924 A B t f _36717 s) (@lem3485930 A B t f _36717 s)). Qed.
Lemma lem3485933 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3485934 (x : Prop) : (x = x) = True.
Proof. exact (@lem3485933 Prop x). Qed.
Lemma lem3485935 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (_36717 : A) (s : A -> Prop) : ((term634 A B t f _36717 s) = (term634 A B t f _36717 s)) = True.
Proof. exact (@lem3485934 (term634 A B t f _36717 s)). Qed.
Lemma lem3485936 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (_36717 : A) (s : A -> Prop) : ((term627 A B s t f _36717) = (term634 A B t f _36717 s)) = True.
Proof. exact (TRANS (@lem3485931 A B t f _36717 s) (@lem3485935 A B t f _36717 s)). Qed.
Lemma lem3485937 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (_36717 : A) (s : A -> Prop) : True = ((term627 A B s t f _36717) = (term634 A B t f _36717 s)).
Proof. exact (SYM (@lem3485936 A B t f _36717 s)). Qed.
Lemma lem3485938 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (_36717 : A) (s : A -> Prop) : (term627 A B s t f _36717) = (term634 A B t f _36717 s).
Proof. exact (EQ_MP (@lem3485937 A B t f _36717 s) (@lem0)). Qed.
Lemma lem3485939 {A B : Type'} (_36717 : A) (t : type1413 A B) (f : type1374 A B) (x' : A) (s : A -> Prop) (x : B) (h1 : term492 A B t f x' s x) : term634 A B t f _36717 s.
Proof. exact (EQ_MP (@lem3485938 A B t f _36717 s) (@lem3485835 A B _36717 t f x' s x h1)). Qed.
Lemma lem3485941 (b : Prop) (a : Prop) : (a \/ b) = (term631 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3485942 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (f : type1374 A B) (_36717 : A) : (term634 A B t f _36717 s) = (term637 A B s t f _36717).
Proof. exact (@lem3485941 (term427 A _36717 s) (term610 A B t f _36717)). Qed.
Lemma lem3485944 (a : Prop) : (term33 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3485945 {A : Type'} (_36717 : A) (s : A -> Prop) : (term638 A _36717 s) = (@IN A _36717 s).
Proof. exact (@lem3485944 (@IN A _36717 s)). Qed.
Lemma lem3485946 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3485947 {A : Type'} (_36717 : A) (s : A -> Prop) : (term639 A _36717 s) = (term640 A _36717 s).
Proof. exact (MK_COMB (@lem3485946) (@lem3485945 A _36717 s)). Qed.
Lemma lem3485948 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (_36717 : A) : (term610 A B t f _36717) = (term610 A B t f _36717).
Proof. exact (eq_refl (term610 A B t f _36717)). Qed.
Lemma lem3485949 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (f : type1374 A B) (_36717 : A) : (term637 A B s t f _36717) = (term282 A B s t f _36717).
Proof. exact (MK_COMB (@lem3485947 A _36717 s) (@lem3485948 A B t f _36717)). Qed.
Lemma lem3485950 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (f : type1374 A B) (_36717 : A) : (term634 A B t f _36717 s) = (term282 A B s t f _36717).
Proof. exact (TRANS (@lem3485942 A B s t f _36717) (@lem3485949 A B s t f _36717)). Qed.
Lemma lem3485953 {A B : Type'} (_36717 : A) (t : type1413 A B) (f : type1374 A B) (x' : A) (s : A -> Prop) (x : B) (h1 : term492 A B t f x' s x) : term282 A B s t f _36717.
Proof. exact (EQ_MP (@lem3485950 A B s t f _36717) (@lem3485939 A B _36717 t f x' s x h1)). Qed.
Lemma lem3485954 {A B : Type'} (_36717 : A) (t : type1413 A B) (f : type1374 A B) (x' : A) (s : A -> Prop) (x : B) (h1 : term492 A B t f x' s x) : term282 A B s t f _36717.
Proof. exact (@lem3485953 A B _36717 t f x' s x h1). Qed.
Lemma lem3485955 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (x' : A) (s : A -> Prop) (x : B) (h1 : term492 A B t f x' s x) : term282 A B s t f x'.
Proof. exact (@lem3485954 A B x' t f x' s x h1). Qed.
Lemma lem3485958 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (x' : A) (s : A -> Prop) (x : B) (h1 : term492 A B t f x' s x) : term610 A B t f x'.
Proof. exact (@lem3485955 A B t f x' s x h1 (@lem3485910 A B t f x' s x h1)). Qed.
Lemma lem3485959 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (x' : A) (s : A -> Prop) (x : B) (h1 : term492 A B t f x' s x) : term641 A B t f x'.
Proof. exact (fun h0 : term642 A B t f x' => @lem3485958 A B t f x' s x h1). Qed.
Lemma lem3485961 (p : Prop) : (term633 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3485962 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (x' : A) : (term641 A B t f x') = (term610 A B t f x').
Proof. exact (@lem3485961 (term610 A B t f x')). Qed.
Lemma lem3485963 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (x' : A) (s : A -> Prop) (x : B) (h1 : term492 A B t f x' s x) : term610 A B t f x'.
Proof. exact (EQ_MP (@lem3485962 A B t f x') (@lem3485959 A B t f x' s x h1)). Qed.
Lemma lem3485969 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3485970 {A B : Type'} (x : B) (_36718 : B -> Prop) (f : type1374 A B) (x' : A) : (term347 A B f x' x _36718) = (term643 A B x _36718 f x').
Proof. exact (@lem3485969 (@IN B x _36718) (term615 A B _36718 f x')). Qed.
Lemma lem3485976 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3485977 {A B : Type'} (x : B) (_36718 : B -> Prop) (f : type1374 A B) (x' : A) : (term644 A B f x' x _36718) = (term645 A B x _36718 f x').
Proof. exact (MK_COMB (@lem3485976) (@lem3485970 A B x _36718 f x')). Qed.
Lemma lem3485983 {A B : Type'} (x : B) (_36718 : B -> Prop) (f : type1374 A B) (x' : A) : (term643 A B x _36718 f x') = (term643 A B x _36718 f x').
Proof. exact (eq_refl (term643 A B x _36718 f x')). Qed.
Lemma lem3485984 {A B : Type'} (x : B) (_36718 : B -> Prop) (f : type1374 A B) (x' : A) : ((term347 A B f x' x _36718) = (term643 A B x _36718 f x')) = ((term643 A B x _36718 f x') = (term643 A B x _36718 f x')).
Proof. exact (MK_COMB (@lem3485977 A B x _36718 f x') (@lem3485983 A B x _36718 f x')). Qed.
Lemma lem3485986 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3485987 (x : Prop) : (x = x) = True.
Proof. exact (@lem3485986 Prop x). Qed.
Lemma lem3485988 {A B : Type'} (x : B) (_36718 : B -> Prop) (f : type1374 A B) (x' : A) : ((term643 A B x _36718 f x') = (term643 A B x _36718 f x')) = True.
Proof. exact (@lem3485987 (term643 A B x _36718 f x')). Qed.
Lemma lem3485989 {A B : Type'} (x : B) (_36718 : B -> Prop) (f : type1374 A B) (x' : A) : ((term347 A B f x' x _36718) = (term643 A B x _36718 f x')) = True.
Proof. exact (TRANS (@lem3485984 A B x _36718 f x') (@lem3485988 A B x _36718 f x')). Qed.
Lemma lem3485990 {A B : Type'} (x : B) (_36718 : B -> Prop) (f : type1374 A B) (x' : A) : True = ((term347 A B f x' x _36718) = (term643 A B x _36718 f x')).
Proof. exact (SYM (@lem3485989 A B x _36718 f x')). Qed.
Lemma lem3485991 {A B : Type'} (x : B) (_36718 : B -> Prop) (f : type1374 A B) (x' : A) : (term347 A B f x' x _36718) = (term643 A B x _36718 f x').
Proof. exact (EQ_MP (@lem3485990 A B x _36718 f x') (@lem0)). Qed.
Lemma lem3485992 {A B : Type'} (_36718 : B -> Prop) (t : type1413 A B) (f : type1374 A B) (x' : A) (s : A -> Prop) (x : B) (h1 : term492 A B t f x' s x) : term643 A B x _36718 f x'.
Proof. exact (EQ_MP (@lem3485991 A B x _36718 f x') (@lem3485817 A B _36718 t f x' s x h1)). Qed.
Lemma lem3485994 (b : Prop) (a : Prop) : (a \/ b) = (term631 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3485995 {A B : Type'} (f : type1374 A B) (x' : A) (x : B) (_36718 : B -> Prop) : (term643 A B x _36718 f x') = (term646 A B f x' x _36718).
Proof. exact (@lem3485994 (term615 A B _36718 f x') (@IN B x _36718)). Qed.
Lemma lem3485997 (a : Prop) : (term33 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3485998 {A B : Type'} (_36718 : B -> Prop) (f : type1374 A B) (x' : A) : (term647 A B _36718 f x') = (term346 A B _36718 f x').
Proof. exact (@lem3485997 (term346 A B _36718 f x')). Qed.
Lemma lem3485999 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3486000 {A B : Type'} (_36718 : B -> Prop) (f : type1374 A B) (x' : A) : (term648 A B _36718 f x') = (term649 A B _36718 f x').
Proof. exact (MK_COMB (@lem3485999) (@lem3485998 A B _36718 f x')). Qed.
Lemma lem3486001 {B : Type'} (x : B) (_36718 : B -> Prop) : (@IN B x _36718) = (@IN B x _36718).
Proof. exact (eq_refl (@IN B x _36718)). Qed.
Lemma lem3486002 {A B : Type'} (f : type1374 A B) (x' : A) (x : B) (_36718 : B -> Prop) : (term646 A B f x' x _36718) = (term342 A B f x' x _36718).
Proof. exact (MK_COMB (@lem3486000 A B _36718 f x') (@lem3486001 B x _36718)). Qed.
Lemma lem3486003 {A B : Type'} (f : type1374 A B) (x' : A) (x : B) (_36718 : B -> Prop) : (term643 A B x _36718 f x') = (term342 A B f x' x _36718).
Proof. exact (TRANS (@lem3485995 A B f x' x _36718) (@lem3486002 A B f x' x _36718)). Qed.
Lemma lem3486006 {A B : Type'} (_36718 : B -> Prop) (t : type1413 A B) (f : type1374 A B) (x' : A) (s : A -> Prop) (x : B) (h1 : term492 A B t f x' s x) : term342 A B f x' x _36718.
Proof. exact (EQ_MP (@lem3486003 A B f x' x _36718) (@lem3485992 A B _36718 t f x' s x h1)). Qed.
Lemma lem3486007 {A B : Type'} (_36718 : B -> Prop) (t : type1413 A B) (f : type1374 A B) (x' : A) (s : A -> Prop) (x : B) (h1 : term492 A B t f x' s x) : term342 A B f x' x _36718.
Proof. exact (@lem3486006 A B _36718 t f x' s x h1). Qed.
Lemma lem3486008 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (x' : A) (s : A -> Prop) (x : B) (h1 : term492 A B t f x' s x) : term650 A B f x t x'.
Proof. exact (@lem3486007 A B (t x') t f x' s x h1). Qed.
Lemma lem3486011 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (x' : A) (s : A -> Prop) (x : B) (h1 : term492 A B t f x' s x) : term651 A B x t x'.
Proof. exact (@lem3486008 A B t f x' s x h1 (@lem3485963 A B t f x' s x h1)). Qed.
Lemma lem3486012 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (x' : A) (s : A -> Prop) (x : B) (h1 : term492 A B t f x' s x) : term652 A B x t x'.
Proof. exact (fun h0 : term611 A B x t x' => @lem3486011 A B t f x' s x h1). Qed.
Lemma lem3486014 (p : Prop) : (term633 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3486015 {A B : Type'} (x : B) (t : type1413 A B) (x' : A) : (term652 A B x t x') = (term651 A B x t x').
Proof. exact (@lem3486014 (term651 A B x t x')). Qed.
Lemma lem3486016 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (x' : A) (s : A -> Prop) (x : B) (h1 : term492 A B t f x' s x) : term651 A B x t x'.
Proof. exact (EQ_MP (@lem3486015 A B x t x') (@lem3486012 A B t f x' s x h1)). Qed.
Lemma lem3486018 (a : Prop) (b : Prop) : (term653 a b) = (term654 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3486019 {A B : Type'} (s : A -> Prop) (x : B) (t : type1413 A B) (_36717 : A) : (term628 A B s x t _36717) = (term270 A B s x t _36717).
Proof. exact (@lem3486018 (@IN A _36717 s) (term651 A B x t _36717)). Qed.
Lemma lem3486021 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3486022 {A B : Type'} (s : A -> Prop) (x : B) (t : type1413 A B) (_36717 : A) : (term270 A B s x t _36717) = (term655 A B s x t _36717).
Proof. exact (@lem3486021 (term263 A B s x t _36717)). Qed.
Lemma lem3486023 {A B : Type'} (s : A -> Prop) (x : B) (t : type1413 A B) (_36717 : A) : (term628 A B s x t _36717) = (term655 A B s x t _36717).
Proof. exact (TRANS (@lem3486019 A B s x t _36717) (@lem3486022 A B s x t _36717)). Qed.
Lemma lem3486025 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (x' : A) (s : A -> Prop) (x : B) (h1 : term492 A B t f x' s x) : term263 A B s x t x'.
Proof. exact (conj (@lem3485892 A B t f x' s x h1) (@lem3486016 A B t f x' s x h1)). Qed.
Lemma lem3486027 {A B : Type'} (_36717 : A) (t : type1413 A B) (f : type1374 A B) (x' : A) (s : A -> Prop) (x : B) (h1 : term492 A B t f x' s x) : term655 A B s x t _36717.
Proof. exact (EQ_MP (@lem3486023 A B s x t _36717) (@lem3485841 A B _36717 t f x' s x h1)). Qed.
Lemma lem3486028 {A B : Type'} (_36717 : A) (t : type1413 A B) (f : type1374 A B) (x' : A) (s : A -> Prop) (x : B) (h1 : term492 A B t f x' s x) : term655 A B s x t _36717.
Proof. exact (@lem3486027 A B _36717 t f x' s x h1). Qed.
Lemma lem3486029 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (x' : A) (s : A -> Prop) (x : B) (h1 : term492 A B t f x' s x) : term655 A B s x t x'.
Proof. exact (@lem3486028 A B x' t f x' s x h1). Qed.
Lemma lem3486032 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (x' : A) (s : A -> Prop) (x : B) (h1 : term492 A B t f x' s x) : False.
Proof. exact (@lem3486029 A B t f x' s x h1 (@lem3486025 A B t f x' s x h1)). Qed.
Lemma lem3486033 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (x' : A) (s : A -> Prop) (x : B) (h1 : term492 A B t f x' s x) : term656.
Proof. exact (fun h0 : ~ False => @lem3486032 A B t f x' s x h1). Qed.
Lemma lem3486035 (p : Prop) : (term633 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3486036 : term656 = False.
Proof. exact (@lem3486035 False). Qed.
Lemma lem3486037 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (x' : A) (s : A -> Prop) (x : B) (h1 : term492 A B t f x' s x) : False.
Proof. exact (EQ_MP (@lem3486036) (@lem3486033 A B t f x' s x h1)). Qed.
Lemma lem3486039 {A B : Type'} (x' : A) (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (h1 : term546 A B x' f s x g) : @IN A x' s.
Proof. exact (proj1 (@lem3485679 A B x' f s x g h1)). Qed.
Lemma lem3486040 {A B : Type'} (x' : A) (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (h1 : term546 A B x' f s x g) : term632 A x' s.
Proof. exact (fun h0 : term427 A x' s => @lem3486039 A B x' f s x g h1). Qed.
Lemma lem3486042 (p : Prop) : (term633 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3486043 {A : Type'} (x' : A) (s : A -> Prop) : (term632 A x' s) = (@IN A x' s).
Proof. exact (@lem3486042 (@IN A x' s)). Qed.
Lemma lem3486044 {A B : Type'} (x' : A) (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (h1 : term546 A B x' f s x g) : @IN A x' s.
Proof. exact (EQ_MP (@lem3486043 A x' s) (@lem3486040 A B x' f s x g h1)). Qed.
Lemma lem3486046 {A B : Type'} (x' : A) (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (h1 : term546 A B x' f s x g) : @IN A x' s.
Proof. exact (proj1 (@lem3485679 A B x' f s x g h1)). Qed.
Lemma lem3486047 {A B : Type'} (x' : A) (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (h1 : term546 A B x' f s x g) : term632 A x' s.
Proof. exact (fun h0 : term427 A x' s => @lem3486046 A B x' f s x g h1). Qed.
Lemma lem3486049 (p : Prop) : (term633 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3486050 {A : Type'} (x' : A) (s : A -> Prop) : (term632 A x' s) = (@IN A x' s).
Proof. exact (@lem3486049 (@IN A x' s)). Qed.
Lemma lem3486051 {A B : Type'} (x' : A) (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (h1 : term546 A B x' f s x g) : @IN A x' s.
Proof. exact (EQ_MP (@lem3486050 A x' s) (@lem3486047 A B x' f s x g h1)). Qed.
Lemma lem3486057 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3486058 {A B : Type'} (g : type1413 A B) (f : type1374 A B) (_36719 : A) (s : A -> Prop) : (term627 A B s g f _36719) = (term634 A B g f _36719 s).
Proof. exact (@lem3486057 (term610 A B g f _36719) (term427 A _36719 s)). Qed.
Lemma lem3486064 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3486065 {A B : Type'} (g : type1413 A B) (f : type1374 A B) (_36719 : A) (s : A -> Prop) : (term635 A B s g f _36719) = (term636 A B g f _36719 s).
Proof. exact (MK_COMB (@lem3486064) (@lem3486058 A B g f _36719 s)). Qed.
Lemma lem3486071 {A B : Type'} (g : type1413 A B) (f : type1374 A B) (_36719 : A) (s : A -> Prop) : (term634 A B g f _36719 s) = (term634 A B g f _36719 s).
Proof. exact (eq_refl (term634 A B g f _36719 s)). Qed.
Lemma lem3486072 {A B : Type'} (g : type1413 A B) (f : type1374 A B) (_36719 : A) (s : A -> Prop) : ((term627 A B s g f _36719) = (term634 A B g f _36719 s)) = ((term634 A B g f _36719 s) = (term634 A B g f _36719 s)).
Proof. exact (MK_COMB (@lem3486065 A B g f _36719 s) (@lem3486071 A B g f _36719 s)). Qed.
Lemma lem3486074 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3486075 (x : Prop) : (x = x) = True.
Proof. exact (@lem3486074 Prop x). Qed.
Lemma lem3486076 {A B : Type'} (g : type1413 A B) (f : type1374 A B) (_36719 : A) (s : A -> Prop) : ((term634 A B g f _36719 s) = (term634 A B g f _36719 s)) = True.
Proof. exact (@lem3486075 (term634 A B g f _36719 s)). Qed.
Lemma lem3486077 {A B : Type'} (g : type1413 A B) (f : type1374 A B) (_36719 : A) (s : A -> Prop) : ((term627 A B s g f _36719) = (term634 A B g f _36719 s)) = True.
Proof. exact (TRANS (@lem3486072 A B g f _36719 s) (@lem3486076 A B g f _36719 s)). Qed.
Lemma lem3486078 {A B : Type'} (g : type1413 A B) (f : type1374 A B) (_36719 : A) (s : A -> Prop) : True = ((term627 A B s g f _36719) = (term634 A B g f _36719 s)).
Proof. exact (SYM (@lem3486077 A B g f _36719 s)). Qed.
Lemma lem3486079 {A B : Type'} (g : type1413 A B) (f : type1374 A B) (_36719 : A) (s : A -> Prop) : (term627 A B s g f _36719) = (term634 A B g f _36719 s).
Proof. exact (EQ_MP (@lem3486078 A B g f _36719 s) (@lem0)). Qed.
Lemma lem3486080 {A B : Type'} (_36719 : A) (x' : A) (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (h1 : term546 A B x' f s x g) : term634 A B g f _36719 s.
Proof. exact (EQ_MP (@lem3486079 A B g f _36719 s) (@lem3485855 A B _36719 x' f s x g h1)). Qed.
Lemma lem3486082 (b : Prop) (a : Prop) : (a \/ b) = (term631 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3486083 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) (_36719 : A) : (term634 A B g f _36719 s) = (term637 A B s g f _36719).
Proof. exact (@lem3486082 (term427 A _36719 s) (term610 A B g f _36719)). Qed.
Lemma lem3486085 (a : Prop) : (term33 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3486086 {A : Type'} (_36719 : A) (s : A -> Prop) : (term638 A _36719 s) = (@IN A _36719 s).
Proof. exact (@lem3486085 (@IN A _36719 s)). Qed.
Lemma lem3486087 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3486088 {A : Type'} (_36719 : A) (s : A -> Prop) : (term639 A _36719 s) = (term640 A _36719 s).
Proof. exact (MK_COMB (@lem3486087) (@lem3486086 A _36719 s)). Qed.
Lemma lem3486089 {A B : Type'} (g : type1413 A B) (f : type1374 A B) (_36719 : A) : (term610 A B g f _36719) = (term610 A B g f _36719).
Proof. exact (eq_refl (term610 A B g f _36719)). Qed.
Lemma lem3486090 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) (_36719 : A) : (term637 A B s g f _36719) = (term282 A B s g f _36719).
Proof. exact (MK_COMB (@lem3486088 A _36719 s) (@lem3486089 A B g f _36719)). Qed.
Lemma lem3486091 {A B : Type'} (s : A -> Prop) (g : type1413 A B) (f : type1374 A B) (_36719 : A) : (term634 A B g f _36719 s) = (term282 A B s g f _36719).
Proof. exact (TRANS (@lem3486083 A B s g f _36719) (@lem3486090 A B s g f _36719)). Qed.
Lemma lem3486094 {A B : Type'} (_36719 : A) (x' : A) (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (h1 : term546 A B x' f s x g) : term282 A B s g f _36719.
Proof. exact (EQ_MP (@lem3486091 A B s g f _36719) (@lem3486080 A B _36719 x' f s x g h1)). Qed.
Lemma lem3486095 {A B : Type'} (_36719 : A) (x' : A) (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (h1 : term546 A B x' f s x g) : term282 A B s g f _36719.
Proof. exact (@lem3486094 A B _36719 x' f s x g h1). Qed.
Lemma lem3486096 {A B : Type'} (x' : A) (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (h1 : term546 A B x' f s x g) : term282 A B s g f x'.
Proof. exact (@lem3486095 A B x' x' f s x g h1). Qed.
Lemma lem3486099 {A B : Type'} (x' : A) (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (h1 : term546 A B x' f s x g) : term610 A B g f x'.
Proof. exact (@lem3486096 A B x' f s x g h1 (@lem3486051 A B x' f s x g h1)). Qed.
Lemma lem3486100 {A B : Type'} (x' : A) (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (h1 : term546 A B x' f s x g) : term641 A B g f x'.
Proof. exact (fun h0 : term642 A B g f x' => @lem3486099 A B x' f s x g h1). Qed.
Lemma lem3486102 (p : Prop) : (term633 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3486103 {A B : Type'} (g : type1413 A B) (f : type1374 A B) (x' : A) : (term641 A B g f x') = (term610 A B g f x').
Proof. exact (@lem3486102 (term610 A B g f x')). Qed.
Lemma lem3486104 {A B : Type'} (x' : A) (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (h1 : term546 A B x' f s x g) : term610 A B g f x'.
Proof. exact (EQ_MP (@lem3486103 A B g f x') (@lem3486100 A B x' f s x g h1)). Qed.
Lemma lem3486110 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3486111 {A B : Type'} (x : B) (_36720 : B -> Prop) (f : type1374 A B) (x' : A) : (term347 A B f x' x _36720) = (term643 A B x _36720 f x').
Proof. exact (@lem3486110 (@IN B x _36720) (term615 A B _36720 f x')). Qed.
Lemma lem3486117 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3486118 {A B : Type'} (x : B) (_36720 : B -> Prop) (f : type1374 A B) (x' : A) : (term644 A B f x' x _36720) = (term645 A B x _36720 f x').
Proof. exact (MK_COMB (@lem3486117) (@lem3486111 A B x _36720 f x')). Qed.
Lemma lem3486124 {A B : Type'} (x : B) (_36720 : B -> Prop) (f : type1374 A B) (x' : A) : (term643 A B x _36720 f x') = (term643 A B x _36720 f x').
Proof. exact (eq_refl (term643 A B x _36720 f x')). Qed.
Lemma lem3486125 {A B : Type'} (x : B) (_36720 : B -> Prop) (f : type1374 A B) (x' : A) : ((term347 A B f x' x _36720) = (term643 A B x _36720 f x')) = ((term643 A B x _36720 f x') = (term643 A B x _36720 f x')).
Proof. exact (MK_COMB (@lem3486118 A B x _36720 f x') (@lem3486124 A B x _36720 f x')). Qed.
Lemma lem3486127 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3486128 (x : Prop) : (x = x) = True.
Proof. exact (@lem3486127 Prop x). Qed.
Lemma lem3486129 {A B : Type'} (x : B) (_36720 : B -> Prop) (f : type1374 A B) (x' : A) : ((term643 A B x _36720 f x') = (term643 A B x _36720 f x')) = True.
Proof. exact (@lem3486128 (term643 A B x _36720 f x')). Qed.
Lemma lem3486130 {A B : Type'} (x : B) (_36720 : B -> Prop) (f : type1374 A B) (x' : A) : ((term347 A B f x' x _36720) = (term643 A B x _36720 f x')) = True.
Proof. exact (TRANS (@lem3486125 A B x _36720 f x') (@lem3486129 A B x _36720 f x')). Qed.
Lemma lem3486131 {A B : Type'} (x : B) (_36720 : B -> Prop) (f : type1374 A B) (x' : A) : True = ((term347 A B f x' x _36720) = (term643 A B x _36720 f x')).
Proof. exact (SYM (@lem3486130 A B x _36720 f x')). Qed.
Lemma lem3486132 {A B : Type'} (x : B) (_36720 : B -> Prop) (f : type1374 A B) (x' : A) : (term347 A B f x' x _36720) = (term643 A B x _36720 f x').
Proof. exact (EQ_MP (@lem3486131 A B x _36720 f x') (@lem0)). Qed.
Lemma lem3486133 {A B : Type'} (_36720 : B -> Prop) (x' : A) (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (h1 : term546 A B x' f s x g) : term643 A B x _36720 f x'.
Proof. exact (EQ_MP (@lem3486132 A B x _36720 f x') (@lem3485849 A B _36720 x' f s x g h1)). Qed.
Lemma lem3486135 (b : Prop) (a : Prop) : (a \/ b) = (term631 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3486136 {A B : Type'} (f : type1374 A B) (x' : A) (x : B) (_36720 : B -> Prop) : (term643 A B x _36720 f x') = (term646 A B f x' x _36720).
Proof. exact (@lem3486135 (term615 A B _36720 f x') (@IN B x _36720)). Qed.
Lemma lem3486138 (a : Prop) : (term33 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3486139 {A B : Type'} (_36720 : B -> Prop) (f : type1374 A B) (x' : A) : (term647 A B _36720 f x') = (term346 A B _36720 f x').
Proof. exact (@lem3486138 (term346 A B _36720 f x')). Qed.
Lemma lem3486140 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3486141 {A B : Type'} (_36720 : B -> Prop) (f : type1374 A B) (x' : A) : (term648 A B _36720 f x') = (term649 A B _36720 f x').
Proof. exact (MK_COMB (@lem3486140) (@lem3486139 A B _36720 f x')). Qed.
Lemma lem3486142 {B : Type'} (x : B) (_36720 : B -> Prop) : (@IN B x _36720) = (@IN B x _36720).
Proof. exact (eq_refl (@IN B x _36720)). Qed.
Lemma lem3486143 {A B : Type'} (f : type1374 A B) (x' : A) (x : B) (_36720 : B -> Prop) : (term646 A B f x' x _36720) = (term342 A B f x' x _36720).
Proof. exact (MK_COMB (@lem3486141 A B _36720 f x') (@lem3486142 B x _36720)). Qed.
Lemma lem3486144 {A B : Type'} (f : type1374 A B) (x' : A) (x : B) (_36720 : B -> Prop) : (term643 A B x _36720 f x') = (term342 A B f x' x _36720).
Proof. exact (TRANS (@lem3486136 A B f x' x _36720) (@lem3486143 A B f x' x _36720)). Qed.
Lemma lem3486147 {A B : Type'} (_36720 : B -> Prop) (x' : A) (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (h1 : term546 A B x' f s x g) : term342 A B f x' x _36720.
Proof. exact (EQ_MP (@lem3486144 A B f x' x _36720) (@lem3486133 A B _36720 x' f s x g h1)). Qed.
Lemma lem3486148 {A B : Type'} (_36720 : B -> Prop) (x' : A) (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (h1 : term546 A B x' f s x g) : term342 A B f x' x _36720.
Proof. exact (@lem3486147 A B _36720 x' f s x g h1). Qed.
Lemma lem3486149 {A B : Type'} (x' : A) (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (h1 : term546 A B x' f s x g) : term650 A B f x g x'.
Proof. exact (@lem3486148 A B (g x') x' f s x g h1). Qed.
Lemma lem3486152 {A B : Type'} (x' : A) (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (h1 : term546 A B x' f s x g) : term651 A B x g x'.
Proof. exact (@lem3486149 A B x' f s x g h1 (@lem3486104 A B x' f s x g h1)). Qed.
Lemma lem3486153 {A B : Type'} (x' : A) (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (h1 : term546 A B x' f s x g) : term652 A B x g x'.
Proof. exact (fun h0 : term611 A B x g x' => @lem3486152 A B x' f s x g h1). Qed.
Lemma lem3486155 (p : Prop) : (term633 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3486156 {A B : Type'} (x : B) (g : type1413 A B) (x' : A) : (term652 A B x g x') = (term651 A B x g x').
Proof. exact (@lem3486155 (term651 A B x g x')). Qed.
Lemma lem3486157 {A B : Type'} (x' : A) (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (h1 : term546 A B x' f s x g) : term651 A B x g x'.
Proof. exact (EQ_MP (@lem3486156 A B x g x') (@lem3486153 A B x' f s x g h1)). Qed.
Lemma lem3486159 (a : Prop) (b : Prop) : (term653 a b) = (term654 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3486160 {A B : Type'} (s : A -> Prop) (x : B) (g : type1413 A B) (_36719 : A) : (term628 A B s x g _36719) = (term270 A B s x g _36719).
Proof. exact (@lem3486159 (@IN A _36719 s) (term651 A B x g _36719)). Qed.
Lemma lem3486162 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3486163 {A B : Type'} (s : A -> Prop) (x : B) (g : type1413 A B) (_36719 : A) : (term270 A B s x g _36719) = (term655 A B s x g _36719).
Proof. exact (@lem3486162 (term263 A B s x g _36719)). Qed.
Lemma lem3486164 {A B : Type'} (s : A -> Prop) (x : B) (g : type1413 A B) (_36719 : A) : (term628 A B s x g _36719) = (term655 A B s x g _36719).
Proof. exact (TRANS (@lem3486160 A B s x g _36719) (@lem3486163 A B s x g _36719)). Qed.
Lemma lem3486166 {A B : Type'} (x' : A) (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (h1 : term546 A B x' f s x g) : term263 A B s x g x'.
Proof. exact (conj (@lem3486044 A B x' f s x g h1) (@lem3486157 A B x' f s x g h1)). Qed.
Lemma lem3486168 {A B : Type'} (_36719 : A) (x' : A) (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (h1 : term546 A B x' f s x g) : term655 A B s x g _36719.
Proof. exact (EQ_MP (@lem3486164 A B s x g _36719) (@lem3485861 A B _36719 x' f s x g h1)). Qed.
Lemma lem3486169 {A B : Type'} (_36719 : A) (x' : A) (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (h1 : term546 A B x' f s x g) : term655 A B s x g _36719.
Proof. exact (@lem3486168 A B _36719 x' f s x g h1). Qed.
Lemma lem3486170 {A B : Type'} (x' : A) (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (h1 : term546 A B x' f s x g) : term655 A B s x g x'.
Proof. exact (@lem3486169 A B x' x' f s x g h1). Qed.
Lemma lem3486173 {A B : Type'} (x' : A) (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (h1 : term546 A B x' f s x g) : False.
Proof. exact (@lem3486170 A B x' f s x g h1 (@lem3486166 A B x' f s x g h1)). Qed.
Lemma lem3486174 {A B : Type'} (x' : A) (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (h1 : term546 A B x' f s x g) : term656.
Proof. exact (fun h0 : ~ False => @lem3486173 A B x' f s x g h1). Qed.
Lemma lem3486176 (p : Prop) : (term633 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3486177 : term656 = False.
Proof. exact (@lem3486176 False). Qed.
Lemma lem3486178 {A B : Type'} (x' : A) (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (h1 : term546 A B x' f s x g) : False.
Proof. exact (EQ_MP (@lem3486177) (@lem3486174 A B x' f s x g h1)). Qed.
Lemma lem3486179 {A B : Type'} (t : type1413 A B) (x' : A) (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (h1 : term602 A B t x' f s x g) : False.
Proof. exact (or_elim (@lem3485673 A B t x' f s x g h1) (fun h0 : term492 A B t f x' s x => @lem3486037 A B t f x' s x h0) (fun h0 : term546 A B x' f s x g => @lem3486178 A B x' f s x g h0)). Qed.
Lemma lem3486180 {A B : Type'} (t : type1413 A B) (x' : A) (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (h1 : term602 A B t x' f s x g) : (term602 A B t x' f s x g) = False.
Proof. exact (prop_ext (fun h2 : term602 A B t x' f s x g => @lem3486179 A B t x' f s x g h1) (fun h2 : False => @lem3485673 A B t x' f s x g h1)). Qed.
Lemma lem3486181 {A B : Type'} (t : type1413 A B) (x' : A) (f : type1374 A B) (s : A -> Prop) (x : B) (g : type1413 A B) (h1 : term602 A B t x' f s x g) : False.
Proof. exact (EQ_MP (@lem3486180 A B t x' f s x g h1) (@lem3485673 A B t x' f s x g h1)). Qed.
Lemma lem3486182 {A B : Type'} (t : type1413 A B) (x' : A) (f : type1374 A B) (s : A -> Prop) (x : B) (h1 : term605 A B t x' f s x) : False.
Proof. exact (ex_elim (@lem3485520 A B t x' f s x h1) (fun g : type1413 A B => fun h0 : term604 A B t x' f s x g => @lem3486181 A B t x' f s x g h0)). Qed.
Lemma lem3486183 {A B : Type'} (t : type1413 A B) (f : type1374 A B) (s : A -> Prop) (x : B) (h1 : term607 A B t f s x) : False.
Proof. exact (ex_elim (@lem3485519 A B t f s x h1) (fun x' : A => fun h0 : term606 A B t f s x x' => @lem3486182 A B t x' f s x h0)). Qed.
Lemma lem3486184 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (h1 : term325 A B f s x) : False.
Proof. exact (ex_elim (@lem3485518 A B f s x h1) (fun t : type1413 A B => fun h0 : term608 A B f s x t => @lem3486183 A B t f s x h0)). Qed.
Lemma lem3486185 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (h1 : term325 A B f s x) : (term325 A B f s x) = False.
Proof. exact (prop_ext (fun h2 : term325 A B f s x => @lem3486184 A B f s x h1) (fun h2 : False => @lem3484820 A B f s x h1)). Qed.
Lemma lem3486186 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (h1 : term325 A B f s x) : False.
Proof. exact (EQ_MP (@lem3486185 A B f s x h1) (@lem3484820 A B f s x h1)). Qed.
Lemma lem3486187 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : term324 A B f s x.
Proof. exact (fun h0 : term325 A B f s x => @lem3486186 A B f s x h0). Qed.
Lemma lem3486188 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term242 A B s f x) = (term322 A B f s x).
Proof. exact (EQ_MP (@lem3484819 A B f s x) (@lem3486187 A B f s x)). Qed.
Lemma lem3486193 {A B : Type'} (s : A -> Prop) (x : B) : term333 A B s x.
Proof. exact (fun f : type1374 A B => @lem3486188 A B f s x). Qed.
Lemma lem3486198 {A B : Type'} (x : B) : term337 A B x.
Proof. exact (fun s : A -> Prop => @lem3486193 A B s x). Qed.
Lemma lem3486203 {A B : Type'} : term341 A B.
Proof. exact (fun x : B => @lem3486198 A B x). Qed.
Lemma lem3486204 {A B : Type'} : term340 A B.
Proof. exact (EQ_MP (@lem3484815 A B) (@lem3486203 A B)). Qed.
Lemma lem3486205 {A B : Type'} (x : B) : term657 A B x.
Proof. exact (@lem3486204 A B x). Qed.
Lemma lem3486206 {A B : Type'} (x : B) : (term657 A B x) = (term336 A B x).
Proof. exact (eq_refl (term657 A B x)). Qed.
Lemma lem3486207 {A B : Type'} (x : B) : term336 A B x.
Proof. exact (EQ_MP (@lem3486206 A B x) (@lem3486205 A B x)). Qed.
Lemma lem3486208 {A B : Type'} (x : B) (s : A -> Prop) : term658 A B x s.
Proof. exact (@lem3486207 A B x s). Qed.
Lemma lem3486209 {A B : Type'} (s : A -> Prop) (x : B) : (term658 A B x s) = (term332 A B s x).
Proof. exact (eq_refl (term658 A B x s)). Qed.
Lemma lem3486210 {A B : Type'} (s : A -> Prop) (x : B) : term332 A B s x.
Proof. exact (EQ_MP (@lem3486209 A B s x) (@lem3486208 A B x s)). Qed.
Lemma lem3486211 {A B : Type'} (s : A -> Prop) (x : B) (f : type1374 A B) : term659 A B s x f.
Proof. exact (@lem3486210 A B s x f). Qed.
Lemma lem3486212 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term659 A B s x f) = (term324 A B f s x).
Proof. exact (eq_refl (term659 A B s x f)). Qed.
Lemma lem3486213 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : term324 A B f s x.
Proof. exact (EQ_MP (@lem3486212 A B f s x) (@lem3486211 A B s x f)). Qed.
Lemma lem3486215 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : term324 A B f s x.
Proof. exact (@lem3484595 A B f s x (@lem3486213 A B f s x)). Qed.
Lemma lem3486216 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (h1 : term325 A B f s x) : False.
Proof. exact (@lem3486215 A B f s x (@lem3484579 A B f s x h1)). Qed.
Lemma lem3486217 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (h1 : term325 A B f s x) : (term325 A B f s x) = False.
Proof. exact (prop_ext (fun h2 : term325 A B f s x => @lem3486216 A B f s x h1) (fun h2 : False => @lem3484579 A B f s x h1)). Qed.
Lemma lem3486218 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) (h1 : term325 A B f s x) : False.
Proof. exact (EQ_MP (@lem3486217 A B f s x h1) (@lem3484579 A B f s x h1)). Qed.
Lemma lem3486219 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : term324 A B f s x.
Proof. exact (fun h0 : term325 A B f s x => @lem3486218 A B f s x h0). Qed.
Lemma lem3486220 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term242 A B s f x) = (term322 A B f s x).
Proof. exact (EQ_MP (@lem3484578 A B f s x) (@lem3486219 A B f s x)). Qed.
Lemma lem3486221 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term242 A B s f x) = (term277 A B f s x).
Proof. exact (EQ_MP (@lem3484574 A B f s x) (@lem3486220 A B f s x)). Qed.
Lemma lem3486222 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term229 A B s f x) = (term230 A B f s x).
Proof. exact (EQ_MP (@lem3484466 A B f s x) (@lem3486221 A B f s x)). Qed.
Lemma lem3486223 {A B : Type'} (f : type1374 A B) (s : A -> Prop) (x : B) : (term194 A B s f x) = (term226 A B f s x).
Proof. exact (EQ_MP (@lem3484352 A B f s x) (@lem3486222 A B f s x)). Qed.
Lemma lem3486228 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : term228 A B f s.
Proof. exact (fun x : B => @lem3486223 A B f s x). Qed.
Lemma lem3486229 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : term180 A B f s.
Proof. exact (EQ_MP (@lem3484346 A B f s) (@lem3486228 A B f s)). Qed.
Lemma lem3486230 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : term68 A B f s.
Proof. exact (EQ_MP (@lem3484203 A B f s) (@lem3486229 A B f s)). Qed.
Lemma lem3486231 {A B : Type'} (f : type1374 A B) (s : A -> Prop) : (term66 A B s f) = (term67 A B f s).
Proof. exact (EQ_MP (@lem3483998 A B f s) (@lem3486230 A B f s)). Qed.
Lemma lem3486236 {A B : Type'} (f : type1374 A B) : term660 A B f.
Proof. exact (fun s : A -> Prop => @lem3486231 A B f s). Qed.
Lemma lem3486241 {A B : Type'} : term661 A B.
Proof. exact (fun f : type1374 A B => @lem3486236 A B f). Qed.
