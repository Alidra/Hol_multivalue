Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_IMAGE_INFINITE_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import CONTRAPOS_THM_spec.
Require Import DISJ_ASSOC_spec.
Require Import FINITE_IMAGE_spec.
Require Import FINITE_UNIONS_spec.
Require Import FORALL_IN_IMAGE_spec.
Require Import INFINITE_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_EXISTS_THM_spec.
Require Import SIMPLE_IMAGE_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1855_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm3211656_spec.
Require Import thm3211657_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm3458971_spec.
Require Import thm3458974_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm951_spec.
Require Import thm952_spec.
Lemma lem4612765 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4612766 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem4612767 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem4612766 t1) (@lem4612765 t1)). Qed.
Lemma lem4612768 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem4612767 t1 t2). Qed.
Lemma lem4612769 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem4612770 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem4612769 t1 t2) (@lem4612768 t1 t2)). Qed.
Lemma lem4612771 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem4612770 t1 t2 t3). Qed.
Lemma lem4612772 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem4612773 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem4612772 t1 t2 t3) (@lem4612771 t1 t2 t3)). Qed.
Lemma lem4612774 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem4612773 t1 t2 t3)). Qed.
Lemma lem4612790 {_89520 _89534 : Type'} : term7 _89520 _89534.
Proof. exact (EQ_MP (@lem3458974 _89520 _89534) (@lem3458971 _89520 _89534)). Qed.
Lemma lem4612791 {_89520 _89534 : Type'} (P : _89534 -> Prop) : term8 _89520 _89534 P.
Proof. exact (@lem4612790 _89520 _89534 P). Qed.
Lemma lem4612792 {_89520 _89534 : Type'} (P : _89534 -> Prop) : (term8 _89520 _89534 P) = (term9 _89520 _89534 P).
Proof. exact (eq_refl (term8 _89520 _89534 P)). Qed.
Lemma lem4612793 {_89520 _89534 : Type'} (P : _89534 -> Prop) : term9 _89520 _89534 P.
Proof. exact (EQ_MP (@lem4612792 _89520 _89534 P) (@lem4612791 _89520 _89534 P)). Qed.
Lemma lem4612794 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) : term10 _89520 _89534 P f.
Proof. exact (@lem4612793 _89520 _89534 P f). Qed.
Lemma lem4612795 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) : (term10 _89520 _89534 P f) = ((term11 _89520 _89534 P f) = (term12 _89520 _89534 P f)).
Proof. exact (eq_refl (term10 _89520 _89534 P f)). Qed.
Lemma lem4612805 (p : Prop) : term13 p.
Proof. exact (@lem9851 p). Qed.
Lemma lem4612806 (p : Prop) : (term13 p) = (term14 p).
Proof. exact (eq_refl (term13 p)). Qed.
Lemma lem4612807 (p : Prop) : term14 p.
Proof. exact (EQ_MP (@lem4612806 p) (@lem4612805 p)). Qed.
Lemma lem4612808 (p : Prop) (h1 : p = True) : p = True.
Proof. exact (h1). Qed.
Lemma lem4612809 (p : Prop) (h1 : p = False) : p = False.
Proof. exact (h1). Qed.
Lemma lem4612818 (q : Prop) : (term15 q) = (term15 q).
Proof. exact (eq_refl (term15 q)). Qed.
Lemma lem4612819 (q : Prop) (p : Prop) (h1 : p = True) : (term16 q p) = (term17 q).
Proof. exact (MK_COMB (@lem4612818 q) (@lem4612808 p h1)). Qed.
Lemma lem4612820 (q : Prop) : (term17 q) = ((term18 q) = (term19 q)).
Proof. exact (eq_refl (term17 q)). Qed.
Lemma lem4612821 (q : Prop) (p : Prop) : (term20 q p) = (term20 q p).
Proof. exact (eq_refl (term20 q p)). Qed.
Lemma lem4612822 (p : Prop) (q : Prop) : ((term16 q p) = (term17 q)) = ((term16 q p) = ((term18 q) = (term19 q))).
Proof. exact (MK_COMB (@lem4612821 q p) (@lem4612820 q)). Qed.
Lemma lem4612823 (p : Prop) (q : Prop) : (term16 q p) = ((term21 p q) = (term22 p q)).
Proof. exact (eq_refl (term16 q p)). Qed.
Lemma lem4612824 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4612825 (p : Prop) (q : Prop) : (term20 q p) = (term23 p q).
Proof. exact (MK_COMB (@lem4612824) (@lem4612823 p q)). Qed.
Lemma lem4612826 (q : Prop) : ((term18 q) = (term19 q)) = ((term18 q) = (term19 q)).
Proof. exact (eq_refl ((term18 q) = (term19 q))). Qed.
Lemma lem4612827 (p : Prop) (q : Prop) : ((term16 q p) = ((term18 q) = (term19 q))) = (((term21 p q) = (term22 p q)) = ((term18 q) = (term19 q))).
Proof. exact (MK_COMB (@lem4612825 p q) (@lem4612826 q)). Qed.
Lemma lem4612828 (p : Prop) (q : Prop) : ((term16 q p) = (term17 q)) = (((term21 p q) = (term22 p q)) = ((term18 q) = (term19 q))).
Proof. exact (TRANS (@lem4612822 p q) (@lem4612827 p q)). Qed.
Lemma lem4612829 (q : Prop) (p : Prop) (h1 : p = True) : ((term21 p q) = (term22 p q)) = ((term18 q) = (term19 q)).
Proof. exact (EQ_MP (@lem4612828 p q) (@lem4612819 q p h1)). Qed.
Lemma lem4612830 (q : Prop) (p : Prop) (h1 : p = True) : ((term18 q) = (term19 q)) = ((term21 p q) = (term22 p q)).
Proof. exact (SYM (@lem4612829 q p h1)). Qed.
Lemma lem4612831 (q : Prop) : (term15 q) = (term15 q).
Proof. exact (eq_refl (term15 q)). Qed.
Lemma lem4612832 (q : Prop) (p : Prop) (h1 : p = False) : (term16 q p) = (term24 q).
Proof. exact (MK_COMB (@lem4612831 q) (@lem4612809 p h1)). Qed.
Lemma lem4612833 (q : Prop) : (term24 q) = ((term25 q) = (term26 q)).
Proof. exact (eq_refl (term24 q)). Qed.
Lemma lem4612834 (q : Prop) (p : Prop) : (term20 q p) = (term20 q p).
Proof. exact (eq_refl (term20 q p)). Qed.
Lemma lem4612835 (p : Prop) (q : Prop) : ((term16 q p) = (term24 q)) = ((term16 q p) = ((term25 q) = (term26 q))).
Proof. exact (MK_COMB (@lem4612834 q p) (@lem4612833 q)). Qed.
Lemma lem4612836 (p : Prop) (q : Prop) : (term16 q p) = ((term21 p q) = (term22 p q)).
Proof. exact (eq_refl (term16 q p)). Qed.
Lemma lem4612837 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4612838 (p : Prop) (q : Prop) : (term20 q p) = (term23 p q).
Proof. exact (MK_COMB (@lem4612837) (@lem4612836 p q)). Qed.
Lemma lem4612839 (q : Prop) : ((term25 q) = (term26 q)) = ((term25 q) = (term26 q)).
Proof. exact (eq_refl ((term25 q) = (term26 q))). Qed.
Lemma lem4612840 (p : Prop) (q : Prop) : ((term16 q p) = ((term25 q) = (term26 q))) = (((term21 p q) = (term22 p q)) = ((term25 q) = (term26 q))).
Proof. exact (MK_COMB (@lem4612838 p q) (@lem4612839 q)). Qed.
Lemma lem4612841 (p : Prop) (q : Prop) : ((term16 q p) = (term24 q)) = (((term21 p q) = (term22 p q)) = ((term25 q) = (term26 q))).
Proof. exact (TRANS (@lem4612835 p q) (@lem4612840 p q)). Qed.
Lemma lem4612842 (q : Prop) (p : Prop) (h1 : p = False) : ((term21 p q) = (term22 p q)) = ((term25 q) = (term26 q)).
Proof. exact (EQ_MP (@lem4612841 p q) (@lem4612832 q p h1)). Qed.
Lemma lem4612843 (q : Prop) (p : Prop) (h1 : p = False) : ((term25 q) = (term26 q)) = ((term21 p q) = (term22 p q)).
Proof. exact (SYM (@lem4612842 q p h1)). Qed.
Lemma lem4612847 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4612848 (q : Prop) : (True /\ q) = q.
Proof. exact (@lem4612847 q). Qed.
Lemma lem4612849 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4612850 (q : Prop) : (term18 q) = (~ q).
Proof. exact (MK_COMB (@lem4612849) (@lem4612848 q)). Qed.
Lemma lem4612851 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4612852 (q : Prop) : (term27 q) = (term28 q).
Proof. exact (MK_COMB (@lem4612851) (@lem4612850 q)). Qed.
Lemma lem4612854 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem4612855 (q : Prop) : (term19 q) = (~ q).
Proof. exact (@lem4612854 (~ q)). Qed.
Lemma lem4612856 (q : Prop) : ((term18 q) = (term19 q)) = ((~ q) = (~ q)).
Proof. exact (MK_COMB (@lem4612852 q) (@lem4612855 q)). Qed.
Lemma lem4612858 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4612859 (x : Prop) : (x = x) = True.
Proof. exact (@lem4612858 Prop x). Qed.
Lemma lem4612860 (q : Prop) : ((~ q) = (~ q)) = True.
Proof. exact (@lem4612859 (~ q)). Qed.
Lemma lem4612861 (q : Prop) : ((term18 q) = (term19 q)) = True.
Proof. exact (TRANS (@lem4612856 q) (@lem4612860 q)). Qed.
Lemma lem4612862 (q : Prop) : True = ((term18 q) = (term19 q)).
Proof. exact (SYM (@lem4612861 q)). Qed.
Lemma lem4612863 (q : Prop) : (term18 q) = (term19 q).
Proof. exact (EQ_MP (@lem4612862 q) (@lem0)). Qed.
Lemma lem4612867 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem4612868 (q : Prop) : (False /\ q) = False.
Proof. exact (@lem4612867 q). Qed.
Lemma lem4612869 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4612870 (q : Prop) : (term25 q) = (~ False).
Proof. exact (MK_COMB (@lem4612869) (@lem4612868 q)). Qed.
Lemma lem4612872 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem4612873 (q : Prop) : (term25 q) = True.
Proof. exact (TRANS (@lem4612870 q) (@lem4612872)). Qed.
Lemma lem4612874 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4612875 (q : Prop) : (term29 q) = (@eq Prop True).
Proof. exact (MK_COMB (@lem4612874) (@lem4612873 q)). Qed.
Lemma lem4612877 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem4612878 (q : Prop) : (term26 q) = True.
Proof. exact (@lem4612877 (~ q)). Qed.
Lemma lem4612879 (q : Prop) : ((term25 q) = (term26 q)) = (True = True).
Proof. exact (MK_COMB (@lem4612875 q) (@lem4612878 q)). Qed.
Lemma lem4612881 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem4612882 : (True = True) = True.
Proof. exact (@lem4612881 True). Qed.
Lemma lem4612883 (q : Prop) : ((term25 q) = (term26 q)) = True.
Proof. exact (TRANS (@lem4612879 q) (@lem4612882)). Qed.
Lemma lem4612884 (q : Prop) : True = ((term25 q) = (term26 q)).
Proof. exact (SYM (@lem4612883 q)). Qed.
Lemma lem4612885 (q : Prop) : (term25 q) = (term26 q).
Proof. exact (EQ_MP (@lem4612884 q) (@lem0)). Qed.
Lemma lem4612886 (q : Prop) (p : Prop) (h1 : p = False) : (term21 p q) = (term22 p q).
Proof. exact (EQ_MP (@lem4612843 q p h1) (@lem4612885 q)). Qed.
Lemma lem4612887 (q : Prop) (p : Prop) (h1 : p = True) : (term21 p q) = (term22 p q).
Proof. exact (EQ_MP (@lem4612830 q p h1) (@lem4612863 q)). Qed.
Lemma lem4612891 {A : Type'} (s : A -> Prop) : term30 A s.
Proof. exact (@lem3198543 A s). Qed.
Lemma lem4612892 {A : Type'} (s : A -> Prop) : (term30 A s) = ((@INFINITE A s) = (term31 A s)).
Proof. exact (eq_refl (term30 A s)). Qed.
Lemma lem4612894 {A : Type'} (P : A -> Prop) : term32 A P.
Proof. exact (@lem10660 A P). Qed.
Lemma lem4612895 {A : Type'} (P : A -> Prop) : (term32 A P) = ((term33 A P) = (term34 A P)).
Proof. exact (eq_refl (term32 A P)). Qed.
Lemma lem4612899 (t2 : Prop) (t1 : Prop) (h1 : (term35 t1 t2) = (t2 -> t1)) : (term35 t1 t2) = (t2 -> t1).
Proof. exact (h1). Qed.
Lemma lem4612900 (t2 : Prop) (t1 : Prop) (h1 : (term35 t1 t2) = (t2 -> t1)) : (t2 -> t1) = (term35 t1 t2).
Proof. exact (SYM (@lem4612899 t2 t1 h1)). Qed.
Lemma lem4612901 (t1 : Prop) (t2 : Prop) (h1 : (t2 -> t1) = (term35 t1 t2)) : (t2 -> t1) = (term35 t1 t2).
Proof. exact (h1). Qed.
Lemma lem4612902 (t1 : Prop) (t2 : Prop) (h1 : (t2 -> t1) = (term35 t1 t2)) : (term35 t1 t2) = (t2 -> t1).
Proof. exact (SYM (@lem4612901 t1 t2 h1)). Qed.
Lemma lem4612903 (t1 : Prop) (t2 : Prop) : ((term35 t1 t2) = (t2 -> t1)) = ((t2 -> t1) = (term35 t1 t2)).
Proof. exact (prop_ext (fun h1 : (term35 t1 t2) = (t2 -> t1) => @lem4612900 t2 t1 h1) (fun h1 : (t2 -> t1) = (term35 t1 t2) => @lem4612902 t1 t2 h1)). Qed.
Lemma lem4612904 (t1 : Prop) : (term36 t1) = (term37 t1).
Proof. exact (fun_ext (fun t2 : Prop => @lem4612903 t1 t2)). Qed.
Lemma lem4612905 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem4612906 (t1 : Prop) : (term38 t1) = (term39 t1).
Proof. exact (MK_COMB (@lem4612905) (@lem4612904 t1)). Qed.
Lemma lem4612907 : term40 = term41.
Proof. exact (fun_ext (fun t1 : Prop => @lem4612906 t1)). Qed.
Lemma lem4612908 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem4612909 : term42 = term43.
Proof. exact (MK_COMB (@lem4612908) (@lem4612907)). Qed.
Lemma lem4612910 : term43.
Proof. exact (EQ_MP (@lem4612909) (@lem10414)). Qed.
Lemma lem4612911 (t1 : Prop) : term44 t1.
Proof. exact (@lem4612910 t1). Qed.
Lemma lem4612912 (t1 : Prop) : (term44 t1) = (term39 t1).
Proof. exact (eq_refl (term44 t1)). Qed.
Lemma lem4612913 (t1 : Prop) : term39 t1.
Proof. exact (EQ_MP (@lem4612912 t1) (@lem4612911 t1)). Qed.
Lemma lem4612914 (t1 : Prop) (t2 : Prop) : term45 t1 t2.
Proof. exact (@lem4612913 t1 t2). Qed.
Lemma lem4612915 (t1 : Prop) (t2 : Prop) : (term45 t1 t2) = ((t2 -> t1) = (term35 t1 t2)).
Proof. exact (eq_refl (term45 t1 t2)). Qed.
Lemma lem4612918 (q : Prop) (p : Prop) (r : Prop) : (term46 p q r) = (term47 q p r).
Proof. exact (EQ_MP (@lem952 q p r) (@lem951 p q r)). Qed.
Lemma lem4612919 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term48 A B s f) = (term49 A B s f).
Proof. exact (@lem4612918 (term50 A B f s) (@INFINITE A s) (term51 A B s f)). Qed.
Lemma lem4612938 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term49 A B s f) = (term48 A B s f).
Proof. exact (SYM (@lem4612919 A B s f)). Qed.
Lemma lem4612939 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term50 A B f s) : term50 A B f s.
Proof. exact (h1). Qed.
Lemma lem4612941 (t1 : Prop) (t2 : Prop) : (t2 -> t1) = (term35 t1 t2).
Proof. exact (EQ_MP (@lem4612915 t1 t2) (@lem4612914 t1 t2)). Qed.
Lemma lem4612942 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term52 A B s f) = (term53 A B f s).
Proof. exact (@lem4612941 (term51 A B s f) (@INFINITE A s)). Qed.
Lemma lem4612943 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term53 A B f s) = (term52 A B s f).
Proof. exact (SYM (@lem4612942 A B f s)). Qed.
Lemma lem4612947 {A : Type'} (P : A -> Prop) : (term33 A P) = (term34 A P).
Proof. exact (EQ_MP (@lem4612895 A P) (@lem4612894 A P)). Qed.
Lemma lem4612948 {A : Type'} (P : A -> Prop) : (term33 A P) = (term34 A P).
Proof. exact (@lem4612947 A P). Qed.
Lemma lem4612949 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term54 A B s f) = (term55 A B s f).
Proof. exact (@lem4612948 A (term56 A B s f)). Qed.
Lemma lem4612950 {A B : Type'} (s : A -> Prop) (f : A -> B) (a : A) : (term57 A B s f a) = (term58 A B s f a).
Proof. exact (eq_refl (term57 A B s f a)). Qed.
Lemma lem4612951 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term59 A B s f) = (term56 A B s f).
Proof. exact (fun_ext (fun a : A => @lem4612950 A B s f a)). Qed.
Lemma lem4612952 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4612953 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term60 A B s f) = (term51 A B s f).
Proof. exact (MK_COMB (@lem4612952 A) (@lem4612951 A B s f)). Qed.
Lemma lem4612954 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4612955 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term54 A B s f) = (term61 A B s f).
Proof. exact (MK_COMB (@lem4612954) (@lem4612953 A B s f)). Qed.
Lemma lem4612956 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4612957 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term62 A B s f) = (term63 A B s f).
Proof. exact (MK_COMB (@lem4612956) (@lem4612955 A B s f)). Qed.
Lemma lem4612958 {A B : Type'} (s : A -> Prop) (f : A -> B) (a : A) : (term57 A B s f a) = (term58 A B s f a).
Proof. exact (eq_refl (term57 A B s f a)). Qed.
Lemma lem4612959 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4612960 {A B : Type'} (s : A -> Prop) (f : A -> B) (a : A) : (term64 A B s f a) = (term65 A B s f a).
Proof. exact (MK_COMB (@lem4612959) (@lem4612958 A B s f a)). Qed.
Lemma lem4612961 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term66 A B s f) = (term67 A B s f).
Proof. exact (fun_ext (fun a : A => @lem4612960 A B s f a)). Qed.
Lemma lem4612962 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4612963 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term55 A B s f) = (term68 A B s f).
Proof. exact (MK_COMB (@lem4612962 A) (@lem4612961 A B s f)). Qed.
Lemma lem4612964 {A B : Type'} (s : A -> Prop) (f : A -> B) : ((term54 A B s f) = (term55 A B s f)) = ((term61 A B s f) = (term68 A B s f)).
Proof. exact (MK_COMB (@lem4612957 A B s f) (@lem4612963 A B s f)). Qed.
Lemma lem4612965 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term61 A B s f) = (term68 A B s f).
Proof. exact (EQ_MP (@lem4612964 A B s f) (@lem4612949 A B s f)). Qed.
Lemma lem4612971 (p : Prop) (q : Prop) : (term21 p q) = (term22 p q).
Proof. exact (or_elim (@lem4612807 p) (fun h0 : p = True => @lem4612887 q p h0) (fun h0 : p = False => @lem4612886 q p h0)). Qed.
Lemma lem4612972 {A B : Type'} (s : A -> Prop) (f : A -> B) (a : A) : (term65 A B s f a) = (term69 A B s f a).
Proof. exact (@lem4612971 (@IN A a s) (term70 A B s f a)). Qed.
Lemma lem4612976 {A : Type'} (s : A -> Prop) : (@INFINITE A s) = (term31 A s).
Proof. exact (EQ_MP (@lem4612892 A s) (@lem4612891 A s)). Qed.
Lemma lem4612977 {A : Type'} (s : A -> Prop) : (@INFINITE A s) = (term31 A s).
Proof. exact (@lem4612976 A s). Qed.
Lemma lem4612978 {A B : Type'} (s : A -> Prop) (f : A -> B) (a : A) : (term70 A B s f a) = (term71 A B s f a).
Proof. exact (@lem4612977 A (term72 A B s f a)). Qed.
Lemma lem4612987 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4612988 {A B : Type'} (s : A -> Prop) (f : A -> B) (a : A) : (term73 A B s f a) = (term74 A B s f a).
Proof. exact (MK_COMB (@lem4612987) (@lem4612978 A B s f a)). Qed.
Lemma lem4612990 (t : Prop) : (term75 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem4612991 {A B : Type'} (s : A -> Prop) (f : A -> B) (a : A) : (term74 A B s f a) = (term76 A B s f a).
Proof. exact (@lem4612990 (term76 A B s f a)). Qed.
Lemma lem4613000 {A B : Type'} (s : A -> Prop) (f : A -> B) (a : A) : (term73 A B s f a) = (term76 A B s f a).
Proof. exact (TRANS (@lem4612988 A B s f a) (@lem4612991 A B s f a)). Qed.
Lemma lem4613001 {A : Type'} (a : A) (s : A -> Prop) : (term77 A a s) = (term77 A a s).
Proof. exact (eq_refl (term77 A a s)). Qed.
Lemma lem4613002 {A B : Type'} (s : A -> Prop) (f : A -> B) (a : A) : (term69 A B s f a) = (term78 A B s f a).
Proof. exact (MK_COMB (@lem4613001 A a s) (@lem4613000 A B s f a)). Qed.
Lemma lem4613005 {A B : Type'} (s : A -> Prop) (f : A -> B) (a : A) : (term65 A B s f a) = (term78 A B s f a).
Proof. exact (TRANS (@lem4612972 A B s f a) (@lem4613002 A B s f a)). Qed.
Lemma lem4613006 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term67 A B s f) = (term79 A B s f).
Proof. exact (fun_ext (fun a : A => @lem4613005 A B s f a)). Qed.
Lemma lem4613007 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4613008 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term68 A B s f) = (term80 A B s f).
Proof. exact (MK_COMB (@lem4613007 A) (@lem4613006 A B s f)). Qed.
Lemma lem4613013 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term61 A B s f) = (term80 A B s f).
Proof. exact (TRANS (@lem4612965 A B s f) (@lem4613008 A B s f)). Qed.
Lemma lem4613014 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4613015 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term81 A B s f) = (term82 A B s f).
Proof. exact (MK_COMB (@lem4613014) (@lem4613013 A B s f)). Qed.
Lemma lem4613017 {A : Type'} (s : A -> Prop) : (@INFINITE A s) = (term31 A s).
Proof. exact (EQ_MP (@lem4612892 A s) (@lem4612891 A s)). Qed.
Lemma lem4613018 {A : Type'} (s : A -> Prop) : (@INFINITE A s) = (term31 A s).
Proof. exact (@lem4613017 A s). Qed.
Lemma lem4613019 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4613020 {A : Type'} (s : A -> Prop) : (term83 A s) = (term84 A s).
Proof. exact (MK_COMB (@lem4613019) (@lem4613018 A s)). Qed.
Lemma lem4613022 (t : Prop) : (term75 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem4613023 {A : Type'} (s : A -> Prop) : (term84 A s) = (@FINITE A s).
Proof. exact (@lem4613022 (@FINITE A s)). Qed.
Lemma lem4613024 {A : Type'} (s : A -> Prop) : (term83 A s) = (@FINITE A s).
Proof. exact (TRANS (@lem4613020 A s) (@lem4613023 A s)). Qed.
Lemma lem4613025 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term53 A B f s) = (term85 A B f s).
Proof. exact (MK_COMB (@lem4613015 A B s f) (@lem4613024 A s)). Qed.
Lemma lem4613028 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term85 A B f s) = (term53 A B f s).
Proof. exact (SYM (@lem4613025 A B f s)). Qed.
Lemma lem4613029 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term80 A B s f) : term80 A B s f.
Proof. exact (h1). Qed.
Lemma lem4613030 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : s = (term86 A B s f)) : s = (term86 A B s f).
Proof. exact (h1). Qed.
Lemma lem4613031 {A : Type'} : (term87 A) = (term87 A).
Proof. exact (eq_refl (term87 A)). Qed.
Lemma lem4613032 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : s = (term86 A B s f)) : (term88 A s) = (term89 A B s f).
Proof. exact (MK_COMB (@lem4613031 A) (@lem4613030 A B s f h1)). Qed.
Lemma lem4613033 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term89 A B s f) = (term90 A B s f).
Proof. exact (eq_refl (term89 A B s f)). Qed.
Lemma lem4613034 {A : Type'} (s : A -> Prop) : (term91 A s) = (term91 A s).
Proof. exact (eq_refl (term91 A s)). Qed.
Lemma lem4613035 {A B : Type'} (s : A -> Prop) (f : A -> B) : ((term88 A s) = (term89 A B s f)) = ((term88 A s) = (term90 A B s f)).
Proof. exact (MK_COMB (@lem4613034 A s) (@lem4613033 A B s f)). Qed.
Lemma lem4613036 {A : Type'} (s : A -> Prop) : (term88 A s) = (@FINITE A s).
Proof. exact (eq_refl (term88 A s)). Qed.
Lemma lem4613037 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4613038 {A : Type'} (s : A -> Prop) : (term91 A s) = (term92 A s).
Proof. exact (MK_COMB (@lem4613037) (@lem4613036 A s)). Qed.
Lemma lem4613039 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term90 A B s f) = (term90 A B s f).
Proof. exact (eq_refl (term90 A B s f)). Qed.
Lemma lem4613040 {A B : Type'} (s : A -> Prop) (f : A -> B) : ((term88 A s) = (term90 A B s f)) = ((@FINITE A s) = (term90 A B s f)).
Proof. exact (MK_COMB (@lem4613038 A s) (@lem4613039 A B s f)). Qed.
Lemma lem4613041 {A B : Type'} (s : A -> Prop) (f : A -> B) : ((term88 A s) = (term89 A B s f)) = ((@FINITE A s) = (term90 A B s f)).
Proof. exact (TRANS (@lem4613035 A B s f) (@lem4613040 A B s f)). Qed.
Lemma lem4613042 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : s = (term86 A B s f)) : (@FINITE A s) = (term90 A B s f).
Proof. exact (EQ_MP (@lem4613041 A B s f) (@lem4613032 A B s f h1)). Qed.
Lemma lem4613043 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : s = (term86 A B s f)) : (term90 A B s f) = (@FINITE A s).
Proof. exact (SYM (@lem4613042 A B s f h1)). Qed.
Lemma lem4613047 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) : (term11 _89520 _89534 P f) = (term12 _89520 _89534 P f).
Proof. exact (EQ_MP (@lem4612795 _89520 _89534 P f) (@lem4612794 _89520 _89534 P f)). Qed.
Lemma lem4613048 {A B : Type'} (P : B -> Prop) (f : type1470 A B) : (term11 A B P f) = (term12 A B P f).
Proof. exact (@lem4613047 A B P f). Qed.
Lemma lem4613049 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term93 A B s f) = (term94 A B s f).
Proof. exact (@lem4613048 A B (term95 A B f s) (term96 A B s f)). Qed.
Lemma lem4613050 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term97 A B f s y) = (term98 A B y f s).
Proof. exact (eq_refl (term97 A B f s y)). Qed.
Lemma lem4613051 {A : Type'} (GEN_PVAR_168 : A -> Prop) : (@SETSPEC (A -> Prop) GEN_PVAR_168) = (@SETSPEC (A -> Prop) GEN_PVAR_168).
Proof. exact (eq_refl (@SETSPEC (A -> Prop) GEN_PVAR_168)). Qed.
Lemma lem4613052 {A B : Type'} (GEN_PVAR_168 : A -> Prop) (y : B) (f : A -> B) (s : A -> Prop) : (term99 A B GEN_PVAR_168 f s y) = (term100 A B GEN_PVAR_168 y f s).
Proof. exact (MK_COMB (@lem4613051 A GEN_PVAR_168) (@lem4613050 A B y f s)). Qed.
Lemma lem4613053 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term101 A B s f y) = (term102 A B s f y).
Proof. exact (eq_refl (term101 A B s f y)). Qed.
Lemma lem4613054 {A B : Type'} (GEN_PVAR_168 : A -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term103 A B GEN_PVAR_168 s f y) = (term104 A B GEN_PVAR_168 s f y).
Proof. exact (MK_COMB (@lem4613052 A B GEN_PVAR_168 y f s) (@lem4613053 A B s f y)). Qed.
Lemma lem4613055 {A B : Type'} (GEN_PVAR_168 : A -> Prop) (s : A -> Prop) (f : A -> B) : (term105 A B GEN_PVAR_168 s f) = (term106 A B GEN_PVAR_168 s f).
Proof. exact (fun_ext (fun y : B => @lem4613054 A B GEN_PVAR_168 s f y)). Qed.
Lemma lem4613056 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4613057 {A B : Type'} (GEN_PVAR_168 : A -> Prop) (s : A -> Prop) (f : A -> B) : (term107 A B GEN_PVAR_168 s f) = (term108 A B GEN_PVAR_168 s f).
Proof. exact (MK_COMB (@lem4613056 B) (@lem4613055 A B GEN_PVAR_168 s f)). Qed.
Lemma lem4613058 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term109 A B s f) = (term110 A B s f).
Proof. exact (fun_ext (fun GEN_PVAR_168 : A -> Prop => @lem4613057 A B GEN_PVAR_168 s f)). Qed.
Lemma lem4613059 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4613060 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term111 A B s f) = (term112 A B s f).
Proof. exact (MK_COMB (@lem4613059 A) (@lem4613058 A B s f)). Qed.
Lemma lem4613061 {A : Type'} : (@UNIONS A) = (@UNIONS A).
Proof. exact (eq_refl (@UNIONS A)). Qed.
Lemma lem4613062 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term93 A B s f) = (term86 A B s f).
Proof. exact (MK_COMB (@lem4613061 A) (@lem4613060 A B s f)). Qed.
Lemma lem4613063 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4613064 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term113 A B s f) = (term114 A B s f).
Proof. exact (MK_COMB (@lem4613063 A) (@lem4613062 A B s f)). Qed.
Lemma lem4613065 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term97 A B f s y) = (term98 A B y f s).
Proof. exact (eq_refl (term97 A B f s y)). Qed.
Lemma lem4613066 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4613067 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term115 A B f s y) = (term116 A B y f s).
Proof. exact (MK_COMB (@lem4613066) (@lem4613065 A B y f s)). Qed.
Lemma lem4613068 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term101 A B s f y) = (term102 A B s f y).
Proof. exact (eq_refl (term101 A B s f y)). Qed.
Lemma lem4613069 {A : Type'} (a : A) : (@IN A a) = (@IN A a).
Proof. exact (eq_refl (@IN A a)). Qed.
Lemma lem4613070 {A B : Type'} (a : A) (s : A -> Prop) (f : A -> B) (y : B) : (term117 A B a s f y) = (term118 A B a s f y).
Proof. exact (MK_COMB (@lem4613069 A a) (@lem4613068 A B s f y)). Qed.
Lemma lem4613071 {A B : Type'} (a : A) (s : A -> Prop) (f : A -> B) (y : B) : (term119 A B a s f y) = (term120 A B a s f y).
Proof. exact (MK_COMB (@lem4613067 A B y f s) (@lem4613070 A B a s f y)). Qed.
Lemma lem4613072 {A B : Type'} (a : A) (s : A -> Prop) (f : A -> B) : (term121 A B a s f) = (term122 A B a s f).
Proof. exact (fun_ext (fun y : B => @lem4613071 A B a s f y)). Qed.
Lemma lem4613073 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4613074 {A B : Type'} (a : A) (s : A -> Prop) (f : A -> B) : (term123 A B a s f) = (term124 A B a s f).
Proof. exact (MK_COMB (@lem4613073 B) (@lem4613072 A B a s f)). Qed.
Lemma lem4613075 {A : Type'} (GEN_PVAR_50 : A) : (@SETSPEC A GEN_PVAR_50) = (@SETSPEC A GEN_PVAR_50).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_50)). Qed.
Lemma lem4613076 {A B : Type'} (GEN_PVAR_50 : A) (a : A) (s : A -> Prop) (f : A -> B) : (term125 A B GEN_PVAR_50 a s f) = (term126 A B GEN_PVAR_50 a s f).
Proof. exact (MK_COMB (@lem4613075 A GEN_PVAR_50) (@lem4613074 A B a s f)). Qed.
Lemma lem4613077 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem4613078 {A B : Type'} (GEN_PVAR_50 : A) (s : A -> Prop) (f : A -> B) (a : A) : (term127 A B GEN_PVAR_50 s f a) = (term128 A B GEN_PVAR_50 s f a).
Proof. exact (MK_COMB (@lem4613076 A B GEN_PVAR_50 a s f) (@lem4613077 A a)). Qed.
Lemma lem4613079 {A B : Type'} (GEN_PVAR_50 : A) (s : A -> Prop) (f : A -> B) : (term129 A B GEN_PVAR_50 s f) = (term130 A B GEN_PVAR_50 s f).
Proof. exact (fun_ext (fun a : A => @lem4613078 A B GEN_PVAR_50 s f a)). Qed.
Lemma lem4613080 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4613081 {A B : Type'} (GEN_PVAR_50 : A) (s : A -> Prop) (f : A -> B) : (term131 A B GEN_PVAR_50 s f) = (term132 A B GEN_PVAR_50 s f).
Proof. exact (MK_COMB (@lem4613080 A) (@lem4613079 A B GEN_PVAR_50 s f)). Qed.
Lemma lem4613082 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term133 A B s f) = (term134 A B s f).
Proof. exact (fun_ext (fun GEN_PVAR_50 : A => @lem4613081 A B GEN_PVAR_50 s f)). Qed.
Lemma lem4613083 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem4613084 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term94 A B s f) = (term135 A B s f).
Proof. exact (MK_COMB (@lem4613083 A) (@lem4613082 A B s f)). Qed.
Lemma lem4613085 {A B : Type'} (s : A -> Prop) (f : A -> B) : ((term93 A B s f) = (term94 A B s f)) = ((term86 A B s f) = (term135 A B s f)).
Proof. exact (MK_COMB (@lem4613064 A B s f) (@lem4613084 A B s f)). Qed.
Lemma lem4613086 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term86 A B s f) = (term135 A B s f).
Proof. exact (EQ_MP (@lem4613085 A B s f) (@lem4613049 A B s f)). Qed.
Lemma lem4613105 {A : Type'} (s : A -> Prop) : (@eq (A -> Prop) s) = (@eq (A -> Prop) s).
Proof. exact (eq_refl (@eq (A -> Prop) s)). Qed.
Lemma lem4613106 {A B : Type'} (s : A -> Prop) (f : A -> B) : (s = (term86 A B s f)) = (s = (term135 A B s f)).
Proof. exact (MK_COMB (@lem4613105 A s) (@lem4613086 A B s f)). Qed.
Lemma lem4613109 {A B : Type'} (s : A -> Prop) (f : A -> B) : (s = (term135 A B s f)) = (s = (term86 A B s f)).
Proof. exact (SYM (@lem4613106 A B s f)). Qed.
Lemma lem4613113 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term136 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4613114 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term136 A s t).
Proof. exact (@lem4613113 A s t). Qed.
Lemma lem4613115 {A B : Type'} (s : A -> Prop) (f : A -> B) : (s = (term135 A B s f)) = (term137 A B s f).
Proof. exact (@lem4613114 A s (term135 A B s f)). Qed.
Lemma lem4613144 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term137 A B s f) = (s = (term135 A B s f)).
Proof. exact (SYM (@lem4613115 A B s f)). Qed.
Lemma lem4613152 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4613153 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4613152 A P x). Qed.
Lemma lem4613154 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4613153 A s x). Qed.
Lemma lem4613155 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4613156 {A : Type'} (s : A -> Prop) (x : A) : (term138 A x s) = (term139 A s x).
Proof. exact (MK_COMB (@lem4613155) (@lem4613154 A s x)). Qed.
Lemma lem4613158 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term140 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem4613159 {A : Type'} (p : A -> Prop) (x : A) : (term140 A x p) = (p x).
Proof. exact (@lem4613158 A p x). Qed.
Lemma lem4613160 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term141 A B x s f) = (term142 A B s f x).
Proof. exact (@lem4613159 A (term143 A B s f) x). Qed.
Lemma lem4613161 {A B : Type'} (a : A) (s : A -> Prop) (f : A -> B) : (term142 A B s f a) = (term124 A B a s f).
Proof. exact (eq_refl (term142 A B s f a)). Qed.
Lemma lem4613162 {A : Type'} (GEN_PVAR_50 : A) : (@SETSPEC A GEN_PVAR_50) = (@SETSPEC A GEN_PVAR_50).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_50)). Qed.
Lemma lem4613163 {A B : Type'} (GEN_PVAR_50 : A) (a : A) (s : A -> Prop) (f : A -> B) : (term144 A B GEN_PVAR_50 s f a) = (term126 A B GEN_PVAR_50 a s f).
Proof. exact (MK_COMB (@lem4613162 A GEN_PVAR_50) (@lem4613161 A B a s f)). Qed.
Lemma lem4613164 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem4613165 {A B : Type'} (GEN_PVAR_50 : A) (s : A -> Prop) (f : A -> B) (a : A) : (term145 A B GEN_PVAR_50 s f a) = (term128 A B GEN_PVAR_50 s f a).
Proof. exact (MK_COMB (@lem4613163 A B GEN_PVAR_50 a s f) (@lem4613164 A a)). Qed.
Lemma lem4613166 {A B : Type'} (GEN_PVAR_50 : A) (s : A -> Prop) (f : A -> B) : (term146 A B GEN_PVAR_50 s f) = (term130 A B GEN_PVAR_50 s f).
Proof. exact (fun_ext (fun a : A => @lem4613165 A B GEN_PVAR_50 s f a)). Qed.
Lemma lem4613167 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4613168 {A B : Type'} (GEN_PVAR_50 : A) (s : A -> Prop) (f : A -> B) : (term147 A B GEN_PVAR_50 s f) = (term132 A B GEN_PVAR_50 s f).
Proof. exact (MK_COMB (@lem4613167 A) (@lem4613166 A B GEN_PVAR_50 s f)). Qed.
Lemma lem4613169 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term148 A B s f) = (term134 A B s f).
Proof. exact (fun_ext (fun GEN_PVAR_50 : A => @lem4613168 A B GEN_PVAR_50 s f)). Qed.
Lemma lem4613170 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem4613171 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term149 A B s f) = (term135 A B s f).
Proof. exact (MK_COMB (@lem4613170 A) (@lem4613169 A B s f)). Qed.
Lemma lem4613172 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem4613173 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) : (term141 A B x s f) = (term150 A B x s f).
Proof. exact (MK_COMB (@lem4613172 A x) (@lem4613171 A B s f)). Qed.
Lemma lem4613174 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4613175 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) : (term151 A B x s f) = (term152 A B x s f).
Proof. exact (MK_COMB (@lem4613174) (@lem4613173 A B x s f)). Qed.
Lemma lem4613176 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) : (term142 A B s f x) = (term124 A B x s f).
Proof. exact (eq_refl (term142 A B s f x)). Qed.
Lemma lem4613177 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) : ((term141 A B x s f) = (term142 A B s f x)) = ((term150 A B x s f) = (term124 A B x s f)).
Proof. exact (MK_COMB (@lem4613175 A B x s f) (@lem4613176 A B x s f)). Qed.
Lemma lem4613178 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) : (term150 A B x s f) = (term124 A B x s f).
Proof. exact (EQ_MP (@lem4613177 A B x s f) (@lem4613160 A B s f x)). Qed.
Lemma lem4613186 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term98 A B y f s) = (term153 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem4613187 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term98 A B y f s) = (term153 A B y f s).
Proof. exact (@lem4613186 A B y f s). Qed.
Lemma lem4613197 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4613198 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4613197 A P x). Qed.
Lemma lem4613199 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4613198 A s x). Qed.
Lemma lem4613200 {A B : Type'} (y : B) (f : A -> B) (x : A) : (term154 A B y f x) = (term154 A B y f x).
Proof. exact (eq_refl (term154 A B y f x)). Qed.
Lemma lem4613201 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) : (term155 A B y f x s) = (term156 A B y f s x).
Proof. exact (MK_COMB (@lem4613200 A B y f x) (@lem4613199 A s x)). Qed.
Lemma lem4613204 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term157 A B y f s) = (term158 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem4613201 A B y f s x)). Qed.
Lemma lem4613205 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4613206 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term153 A B y f s) = (term159 A B y f s).
Proof. exact (MK_COMB (@lem4613205 A) (@lem4613204 A B y f s)). Qed.
Lemma lem4613211 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term98 A B y f s) = (term159 A B y f s).
Proof. exact (TRANS (@lem4613187 A B y f s) (@lem4613206 A B y f s)). Qed.
Lemma lem4613212 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4613213 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term116 A B y f s) = (term160 A B y f s).
Proof. exact (MK_COMB (@lem4613212) (@lem4613211 A B y f s)). Qed.
Lemma lem4613215 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term140 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem4613216 {A : Type'} (p : A -> Prop) (x : A) : (term140 A x p) = (p x).
Proof. exact (@lem4613215 A p x). Qed.
Lemma lem4613217 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term161 A B x s f y) = (term162 A B s f y x).
Proof. exact (@lem4613216 A (term163 A B s f y) x). Qed.
Lemma lem4613218 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term162 A B s f y x) = (term164 A B s f x y).
Proof. exact (eq_refl (term162 A B s f y x)). Qed.
Lemma lem4613219 {A : Type'} (GEN_PVAR_167 : A) : (@SETSPEC A GEN_PVAR_167) = (@SETSPEC A GEN_PVAR_167).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_167)). Qed.
Lemma lem4613220 {A B : Type'} (GEN_PVAR_167 : A) (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term165 A B GEN_PVAR_167 s f y x) = (term166 A B GEN_PVAR_167 s f x y).
Proof. exact (MK_COMB (@lem4613219 A GEN_PVAR_167) (@lem4613218 A B s f x y)). Qed.
Lemma lem4613221 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4613222 {A B : Type'} (GEN_PVAR_167 : A) (s : A -> Prop) (f : A -> B) (y : B) (x : A) : (term167 A B GEN_PVAR_167 s f y x) = (term168 A B GEN_PVAR_167 s f y x).
Proof. exact (MK_COMB (@lem4613220 A B GEN_PVAR_167 s f x y) (@lem4613221 A x)). Qed.
Lemma lem4613223 {A B : Type'} (GEN_PVAR_167 : A) (s : A -> Prop) (f : A -> B) (y : B) : (term169 A B GEN_PVAR_167 s f y) = (term170 A B GEN_PVAR_167 s f y).
Proof. exact (fun_ext (fun x : A => @lem4613222 A B GEN_PVAR_167 s f y x)). Qed.
Lemma lem4613224 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4613225 {A B : Type'} (GEN_PVAR_167 : A) (s : A -> Prop) (f : A -> B) (y : B) : (term171 A B GEN_PVAR_167 s f y) = (term172 A B GEN_PVAR_167 s f y).
Proof. exact (MK_COMB (@lem4613224 A) (@lem4613223 A B GEN_PVAR_167 s f y)). Qed.
Lemma lem4613226 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term173 A B s f y) = (term174 A B s f y).
Proof. exact (fun_ext (fun GEN_PVAR_167 : A => @lem4613225 A B GEN_PVAR_167 s f y)). Qed.
Lemma lem4613227 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem4613228 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term175 A B s f y) = (term102 A B s f y).
Proof. exact (MK_COMB (@lem4613227 A) (@lem4613226 A B s f y)). Qed.
Lemma lem4613229 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem4613230 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (y : B) : (term161 A B x s f y) = (term118 A B x s f y).
Proof. exact (MK_COMB (@lem4613229 A x) (@lem4613228 A B s f y)). Qed.
Lemma lem4613231 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4613232 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (y : B) : (term176 A B x s f y) = (term177 A B x s f y).
Proof. exact (MK_COMB (@lem4613231) (@lem4613230 A B x s f y)). Qed.
Lemma lem4613233 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term162 A B s f y x) = (term164 A B s f x y).
Proof. exact (eq_refl (term162 A B s f y x)). Qed.
Lemma lem4613234 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : ((term161 A B x s f y) = (term162 A B s f y x)) = ((term118 A B x s f y) = (term164 A B s f x y)).
Proof. exact (MK_COMB (@lem4613232 A B x s f y) (@lem4613233 A B s f x y)). Qed.
Lemma lem4613235 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term118 A B x s f y) = (term164 A B s f x y).
Proof. exact (EQ_MP (@lem4613234 A B s f x y) (@lem4613217 A B s f y x)). Qed.
Lemma lem4613239 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4613240 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4613239 A P x). Qed.
Lemma lem4613241 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4613240 A s x). Qed.
Lemma lem4613242 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4613243 {A : Type'} (s : A -> Prop) (x : A) : (term178 A x s) = (term179 A s x).
Proof. exact (MK_COMB (@lem4613242) (@lem4613241 A s x)). Qed.
Lemma lem4613246 {A B : Type'} (f : A -> B) (x : A) (y : B) : ((f x) = y) = ((f x) = y).
Proof. exact (eq_refl ((f x) = y)). Qed.
Lemma lem4613247 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term164 A B s f x y) = (term180 A B s f x y).
Proof. exact (MK_COMB (@lem4613243 A s x) (@lem4613246 A B f x y)). Qed.
Lemma lem4613250 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term118 A B x s f y) = (term180 A B s f x y).
Proof. exact (TRANS (@lem4613235 A B s f x y) (@lem4613247 A B s f x y)). Qed.
Lemma lem4613251 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term120 A B x s f y) = (term181 A B s f x y).
Proof. exact (MK_COMB (@lem4613213 A B y f s) (@lem4613250 A B s f x y)). Qed.
Lemma lem4613254 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term122 A B x s f) = (term182 A B s f x).
Proof. exact (fun_ext (fun y : B => @lem4613251 A B s f x y)). Qed.
Lemma lem4613255 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4613256 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term124 A B x s f) = (term183 A B s f x).
Proof. exact (MK_COMB (@lem4613255 B) (@lem4613254 A B s f x)). Qed.
Lemma lem4613261 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term150 A B x s f) = (term183 A B s f x).
Proof. exact (TRANS (@lem4613178 A B x s f) (@lem4613256 A B s f x)). Qed.
Lemma lem4613262 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : ((@IN A x s) = (term150 A B x s f)) = ((s x) = (term183 A B s f x)).
Proof. exact (MK_COMB (@lem4613156 A s x) (@lem4613261 A B s f x)). Qed.
Lemma lem4613265 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term184 A B s f) = (term185 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4613262 A B s f x)). Qed.
Lemma lem4613266 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4613267 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term137 A B s f) = (term186 A B s f).
Proof. exact (MK_COMB (@lem4613266 A) (@lem4613265 A B s f)). Qed.
Lemma lem4613272 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term186 A B s f) = (term137 A B s f).
Proof. exact (SYM (@lem4613267 A B s f)). Qed.
Lemma lem4613274 (p : Prop) : p = (term187 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4613275 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term186 A B s f) = (term188 A B s f).
Proof. exact (@lem4613274 (term186 A B s f)). Qed.
Lemma lem4613276 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term188 A B s f) = (term186 A B s f).
Proof. exact (SYM (@lem4613275 A B s f)). Qed.
Lemma lem4613277 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term189 A B s f) : term189 A B s f.
Proof. exact (h1). Qed.
Lemma lem4613280 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term188 A B s f) : term188 A B s f.
Proof. exact (h1). Qed.
Lemma lem4613281 {A B : Type'} (s : A -> Prop) (f : A -> B) : term190 A B s f.
Proof. exact (fun h0 : term188 A B s f => @lem4613280 A B s f h0). Qed.
Lemma lem4613282 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term190 A B s f) : term190 A B s f.
Proof. exact (h1). Qed.
Lemma lem4613283 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term188 A B s f) : term188 A B s f.
Proof. exact (h1). Qed.
Lemma lem4613284 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term188 A B s f) (h2 : term190 A B s f) : term188 A B s f.
Proof. exact (@lem4613282 A B s f h2 (@lem4613283 A B s f h1)). Qed.
Lemma lem4613285 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term188 A B s f) : term191 A B s f.
Proof. exact (fun h0 : term190 A B s f => @lem4613284 A B s f h1 h0). Qed.
Lemma lem4613286 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term190 A B s f) : term190 A B s f.
Proof. exact (h1). Qed.
Lemma lem4613287 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term188 A B s f) (h2 : term190 A B s f) : term188 A B s f.
Proof. exact (@lem4613285 A B s f h1 (@lem4613286 A B s f h2)). Qed.
Lemma lem4613288 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term190 A B s f) : term190 A B s f.
Proof. exact (fun h0 : term188 A B s f => @lem4613287 A B s f h0 h1). Qed.
Lemma lem4613289 {A B : Type'} (s : A -> Prop) (f : A -> B) : term192 A B s f.
Proof. exact (fun h0 : term190 A B s f => @lem4613288 A B s f h0). Qed.
Lemma lem4613292 {A B : Type'} (s : A -> Prop) (f : A -> B) : term190 A B s f.
Proof. exact (@lem4613289 A B s f (@lem4613281 A B s f)). Qed.
Lemma lem4613293 {A B : Type'} (s : A -> Prop) (f : A -> B) : term190 A B s f.
Proof. exact (@lem4613292 A B s f). Qed.
Lemma lem4613303 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4613304 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term188 A B s f) = (term193 A B s f).
Proof. exact (@lem4613303 (term189 A B s f)). Qed.
Lemma lem4613306 (t : Prop) : (term75 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4613307 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term193 A B s f) = (term186 A B s f).
Proof. exact (@lem4613306 (term186 A B s f)). Qed.
Lemma lem4613312 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term188 A B s f) = (term186 A B s f).
Proof. exact (TRANS (@lem4613304 A B s f) (@lem4613307 A B s f)). Qed.
Lemma lem4613399 {A B : Type'} (f : A -> B) : (term194 A B f) = (term195 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4613312 A B s f)). Qed.
Lemma lem4613400 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4613401 {A B : Type'} (f : A -> B) : (term196 A B f) = (term197 A B f).
Proof. exact (MK_COMB (@lem4613400 A) (@lem4613399 A B f)). Qed.
Lemma lem4613406 {A B : Type'} : (term198 A B) = (term199 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem4613401 A B f)). Qed.
Lemma lem4613407 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4613416 {A B : Type'} : (term200 A B) = (term201 A B).
Proof. exact (MK_COMB (@lem4613407 A B) (@lem4613406 A B)). Qed.
Lemma lem4613421 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term180 A B s f x y) = (term180 A B s f x y).
Proof. exact (eq_refl (term180 A B s f x y)). Qed.
Lemma lem4613426 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) : (term156 A B y f s x) = (term156 A B y f s x).
Proof. exact (eq_refl (term156 A B y f s x)). Qed.
Lemma lem4613427 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term158 A B y f s) = (term158 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem4613426 A B y f s x)). Qed.
Lemma lem4613428 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4613429 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term159 A B y f s) = (term159 A B y f s).
Proof. exact (MK_COMB (@lem4613428 A) (@lem4613427 A B y f s)). Qed.
Lemma lem4613430 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4613431 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term160 A B y f s) = (term160 A B y f s).
Proof. exact (MK_COMB (@lem4613430) (@lem4613429 A B y f s)). Qed.
Lemma lem4613432 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term181 A B s f x y) = (term181 A B s f x y).
Proof. exact (MK_COMB (@lem4613431 A B y f s) (@lem4613421 A B s f x y)). Qed.
Lemma lem4613433 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term182 A B s f x) = (term182 A B s f x).
Proof. exact (fun_ext (fun y : B => @lem4613432 A B s f x y)). Qed.
Lemma lem4613434 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4613435 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term183 A B s f x) = (term183 A B s f x).
Proof. exact (MK_COMB (@lem4613434 B) (@lem4613433 A B s f x)). Qed.
Lemma lem4613438 {A : Type'} (s : A -> Prop) (x : A) : (term139 A s x) = (term139 A s x).
Proof. exact (eq_refl (term139 A s x)). Qed.
Lemma lem4613439 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : ((s x) = (term183 A B s f x)) = ((s x) = (term183 A B s f x)).
Proof. exact (MK_COMB (@lem4613438 A s x) (@lem4613435 A B s f x)). Qed.
Lemma lem4613440 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term185 A B s f) = (term185 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4613439 A B s f x)). Qed.
Lemma lem4613441 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4613442 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term186 A B s f) = (term186 A B s f).
Proof. exact (MK_COMB (@lem4613441 A) (@lem4613440 A B s f)). Qed.
Lemma lem4613443 {A B : Type'} (f : A -> B) : (term195 A B f) = (term195 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4613442 A B s f)). Qed.
Lemma lem4613444 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4613445 {A B : Type'} (f : A -> B) : (term197 A B f) = (term197 A B f).
Proof. exact (MK_COMB (@lem4613444 A) (@lem4613443 A B f)). Qed.
Lemma lem4613446 {A B : Type'} : (term199 A B) = (term199 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem4613445 A B f)). Qed.
Lemma lem4613447 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4613448 {A B : Type'} : (term201 A B) = (term201 A B).
Proof. exact (MK_COMB (@lem4613447 A B) (@lem4613446 A B)). Qed.
Lemma lem4613487 {A B : Type'} : (term200 A B) = (term201 A B).
Proof. exact (TRANS (@lem4613416 A B) (@lem4613448 A B)). Qed.
Lemma lem4613488 {A B : Type'} : (term201 A B) = (term200 A B).
Proof. exact (SYM (@lem4613487 A B)). Qed.
Lemma lem4613490 (p : Prop) : p = (term187 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4613491 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : ((s x) = (term183 A B s f x)) = (term202 A B s f x).
Proof. exact (@lem4613490 ((s x) = (term183 A B s f x))). Qed.
Lemma lem4613492 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term202 A B s f x) = ((s x) = (term183 A B s f x)).
Proof. exact (SYM (@lem4613491 A B s f x)). Qed.
Lemma lem4613493 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term203 A B s f x) : term203 A B s f x.
Proof. exact (h1). Qed.
Lemma lem4613504 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) : (term204 A B y f s x) = (term205 A B y f s x).
Proof. exact (@lem17045 (y = (f x)) (s x)). Qed.
Lemma lem4613507 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) : (term156 A B y f s x) = (term156 A B y f s x).
Proof. exact (eq_refl (term156 A B y f s x)). Qed.
Lemma lem4613508 {A : Type'} (P : A -> Prop) : (term206 A P) = (term34 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem4613509 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term207 A B y f s) = (term208 A B y f s).
Proof. exact (@lem4613508 A (term158 A B y f s)). Qed.
Lemma lem4613510 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) : (term209 A B y f s x) = (term156 A B y f s x).
Proof. exact (eq_refl (term209 A B y f s x)). Qed.
Lemma lem4613511 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4613512 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) : (term210 A B y f s x) = (term204 A B y f s x).
Proof. exact (MK_COMB (@lem4613511) (@lem4613510 A B y f s x)). Qed.
Lemma lem4613513 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) : (term210 A B y f s x) = (term205 A B y f s x).
Proof. exact (TRANS (@lem4613512 A B y f s x) (@lem4613504 A B y f s x)). Qed.
Lemma lem4613514 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term211 A B y f s) = (term212 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem4613513 A B y f s x)). Qed.
Lemma lem4613515 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4613516 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term208 A B y f s) = (term213 A B y f s).
Proof. exact (MK_COMB (@lem4613515 A) (@lem4613514 A B y f s)). Qed.
Lemma lem4613517 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term207 A B y f s) = (term213 A B y f s).
Proof. exact (TRANS (@lem4613509 A B y f s) (@lem4613516 A B y f s)). Qed.
Lemma lem4613518 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term158 A B y f s) = (term158 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem4613507 A B y f s x)). Qed.
Lemma lem4613519 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4613520 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term159 A B y f s) = (term159 A B y f s).
Proof. exact (MK_COMB (@lem4613519 A) (@lem4613518 A B y f s)). Qed.
Lemma lem4613529 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term214 A B s f x y) = (term215 A B s f x y).
Proof. exact (@lem17045 (s x) ((f x) = y)). Qed.
Lemma lem4613532 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term180 A B s f x y) = (term180 A B s f x y).
Proof. exact (eq_refl (term180 A B s f x y)). Qed.
Lemma lem4613533 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4613534 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term216 A B y f s) = (term217 A B y f s).
Proof. exact (MK_COMB (@lem4613533) (@lem4613517 A B y f s)). Qed.
Lemma lem4613535 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term218 A B s f x y) = (term219 A B s f x y).
Proof. exact (MK_COMB (@lem4613534 A B y f s) (@lem4613529 A B s f x y)). Qed.
Lemma lem4613536 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term220 A B s f x y) = (term218 A B s f x y).
Proof. exact (@lem17045 (term159 A B y f s) (term180 A B s f x y)). Qed.
Lemma lem4613537 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term220 A B s f x y) = (term219 A B s f x y).
Proof. exact (TRANS (@lem4613536 A B s f x y) (@lem4613535 A B s f x y)). Qed.
Lemma lem4613538 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4613539 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term160 A B y f s) = (term160 A B y f s).
Proof. exact (MK_COMB (@lem4613538) (@lem4613520 A B y f s)). Qed.
Lemma lem4613540 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term181 A B s f x y) = (term181 A B s f x y).
Proof. exact (MK_COMB (@lem4613539 A B y f s) (@lem4613532 A B s f x y)). Qed.
Lemma lem4613541 {B : Type'} (P : B -> Prop) : (term206 B P) = (term34 B P).
Proof. exact (@lem18394 B P). Qed.
Lemma lem4613542 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term221 A B s f x) = (term222 A B s f x).
Proof. exact (@lem4613541 B (term182 A B s f x)). Qed.
Lemma lem4613543 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term223 A B s f x y) = (term181 A B s f x y).
Proof. exact (eq_refl (term223 A B s f x y)). Qed.
Lemma lem4613544 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4613545 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term224 A B s f x y) = (term220 A B s f x y).
Proof. exact (MK_COMB (@lem4613544) (@lem4613543 A B s f x y)). Qed.
Lemma lem4613546 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term224 A B s f x y) = (term219 A B s f x y).
Proof. exact (TRANS (@lem4613545 A B s f x y) (@lem4613537 A B s f x y)). Qed.
Lemma lem4613547 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term225 A B s f x) = (term226 A B s f x).
Proof. exact (fun_ext (fun y : B => @lem4613546 A B s f x y)). Qed.
Lemma lem4613548 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4613549 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term222 A B s f x) = (term227 A B s f x).
Proof. exact (MK_COMB (@lem4613548 B) (@lem4613547 A B s f x)). Qed.
Lemma lem4613550 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term221 A B s f x) = (term227 A B s f x).
Proof. exact (TRANS (@lem4613542 A B s f x) (@lem4613549 A B s f x)). Qed.
Lemma lem4613551 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term182 A B s f x) = (term182 A B s f x).
Proof. exact (fun_ext (fun y : B => @lem4613540 A B s f x y)). Qed.
Lemma lem4613552 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4613553 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term183 A B s f x) = (term183 A B s f x).
Proof. exact (MK_COMB (@lem4613552 B) (@lem4613551 A B s f x)). Qed.
Lemma lem4613555 {A : Type'} (s : A -> Prop) (x : A) : (term228 A s x) = (term228 A s x).
Proof. exact (eq_refl (term228 A s x)). Qed.
Lemma lem4613556 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term229 A B s f x) = (term229 A B s f x).
Proof. exact (MK_COMB (@lem4613555 A s x) (@lem4613553 A B s f x)). Qed.
Lemma lem4613558 {A : Type'} (s : A -> Prop) (x : A) : (term179 A s x) = (term179 A s x).
Proof. exact (eq_refl (term179 A s x)). Qed.
Lemma lem4613559 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term230 A B s f x) = (term231 A B s f x).
Proof. exact (MK_COMB (@lem4613558 A s x) (@lem4613550 A B s f x)). Qed.
Lemma lem4613560 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4613561 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term232 A B s f x) = (term233 A B s f x).
Proof. exact (MK_COMB (@lem4613560) (@lem4613559 A B s f x)). Qed.
Lemma lem4613562 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term234 A B s f x) = (term235 A B s f x).
Proof. exact (MK_COMB (@lem4613561 A B s f x) (@lem4613556 A B s f x)). Qed.
Lemma lem4613563 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term203 A B s f x) = (term234 A B s f x).
Proof. exact (@lem17646 (s x) (term183 A B s f x)). Qed.
Lemma lem4613564 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term203 A B s f x) = (term235 A B s f x).
Proof. exact (TRANS (@lem4613563 A B s f x) (@lem4613562 A B s f x)). Qed.
Lemma lem4613743 {A : Type'} (P : A -> Prop) (Q : Prop) : (term236 A P Q) = (term237 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4613744 {A : Type'} (P : A -> Prop) (Q : Prop) : (term236 A P Q) = (term237 A P Q).
Proof. exact (@lem4613743 A P Q). Qed.
Lemma lem4613745 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term238 A B s f x y) = (term239 A B s f x y).
Proof. exact (@lem4613744 A (term158 A B y f s) (term180 A B s f x y)). Qed.
Lemma lem4613746 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) : (term209 A B y f s x) = (term156 A B y f s x).
Proof. exact (eq_refl (term209 A B y f s x)). Qed.
Lemma lem4613747 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term240 A B y f s) = (term158 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem4613746 A B y f s x)). Qed.
Lemma lem4613748 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4613749 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term241 A B y f s) = (term159 A B y f s).
Proof. exact (MK_COMB (@lem4613748 A) (@lem4613747 A B y f s)). Qed.
Lemma lem4613750 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4613751 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term242 A B y f s) = (term160 A B y f s).
Proof. exact (MK_COMB (@lem4613750) (@lem4613749 A B y f s)). Qed.
Lemma lem4613752 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term180 A B s f x y) = (term180 A B s f x y).
Proof. exact (eq_refl (term180 A B s f x y)). Qed.
Lemma lem4613753 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term238 A B s f x y) = (term181 A B s f x y).
Proof. exact (MK_COMB (@lem4613751 A B y f s) (@lem4613752 A B s f x y)). Qed.
Lemma lem4613754 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4613755 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term243 A B s f x y) = (term244 A B s f x y).
Proof. exact (MK_COMB (@lem4613754) (@lem4613753 A B s f x y)). Qed.
Lemma lem4613756 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term209 A B y f s x') = (term156 A B y f s x').
Proof. exact (eq_refl (term209 A B y f s x')). Qed.
Lemma lem4613757 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4613758 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term245 A B y f s x') = (term246 A B y f s x').
Proof. exact (MK_COMB (@lem4613757) (@lem4613756 A B y f s x')). Qed.
Lemma lem4613759 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term180 A B s f x y) = (term180 A B s f x y).
Proof. exact (eq_refl (term180 A B s f x y)). Qed.
Lemma lem4613760 {A B : Type'} (x' : A) (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term247 A B x' s f x y) = (term248 A B x' s f x y).
Proof. exact (MK_COMB (@lem4613758 A B y f s x') (@lem4613759 A B s f x y)). Qed.
Lemma lem4613761 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term249 A B s f x y) = (term250 A B s f x y).
Proof. exact (fun_ext (fun x' : A => @lem4613760 A B x' s f x y)). Qed.
Lemma lem4613762 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4613763 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term239 A B s f x y) = (term251 A B s f x y).
Proof. exact (MK_COMB (@lem4613762 A) (@lem4613761 A B s f x y)). Qed.
Lemma lem4613764 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : ((term238 A B s f x y) = (term239 A B s f x y)) = ((term181 A B s f x y) = (term251 A B s f x y)).
Proof. exact (MK_COMB (@lem4613755 A B s f x y) (@lem4613763 A B s f x y)). Qed.
Lemma lem4613765 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term181 A B s f x y) = (term251 A B s f x y).
Proof. exact (EQ_MP (@lem4613764 A B s f x y) (@lem4613745 A B s f x y)). Qed.
Lemma lem4613766 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term182 A B s f x) = (term252 A B s f x).
Proof. exact (fun_ext (fun y : B => @lem4613765 A B s f x y)). Qed.
Lemma lem4613767 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4613768 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term183 A B s f x) = (term253 A B s f x).
Proof. exact (MK_COMB (@lem4613767 B) (@lem4613766 A B s f x)). Qed.
Lemma lem4613769 {A : Type'} (s : A -> Prop) (x : A) : (term228 A s x) = (term228 A s x).
Proof. exact (eq_refl (term228 A s x)). Qed.
Lemma lem4613770 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term229 A B s f x) = (term254 A B s f x).
Proof. exact (MK_COMB (@lem4613769 A s x) (@lem4613768 A B s f x)). Qed.
Lemma lem4613772 {A : Type'} (P : Prop) (Q : A -> Prop) : (term255 A P Q) = (term256 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4613773 {B : Type'} (P : Prop) (Q : B -> Prop) : (term255 B P Q) = (term256 B P Q).
Proof. exact (@lem4613772 B P Q). Qed.
Lemma lem4613774 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term257 A B s f x) = (term258 A B s f x).
Proof. exact (@lem4613773 B (term259 A s x) (term252 A B s f x)). Qed.
Lemma lem4613775 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term260 A B s f x y) = (term251 A B s f x y).
Proof. exact (eq_refl (term260 A B s f x y)). Qed.
Lemma lem4613776 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term261 A B s f x) = (term252 A B s f x).
Proof. exact (fun_ext (fun y : B => @lem4613775 A B s f x y)). Qed.
Lemma lem4613777 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4613778 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term262 A B s f x) = (term253 A B s f x).
Proof. exact (MK_COMB (@lem4613777 B) (@lem4613776 A B s f x)). Qed.
Lemma lem4613779 {A : Type'} (s : A -> Prop) (x : A) : (term228 A s x) = (term228 A s x).
Proof. exact (eq_refl (term228 A s x)). Qed.
Lemma lem4613780 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term257 A B s f x) = (term254 A B s f x).
Proof. exact (MK_COMB (@lem4613779 A s x) (@lem4613778 A B s f x)). Qed.
Lemma lem4613781 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4613782 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term263 A B s f x) = (term264 A B s f x).
Proof. exact (MK_COMB (@lem4613781) (@lem4613780 A B s f x)). Qed.
Lemma lem4613783 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term260 A B s f x y) = (term251 A B s f x y).
Proof. exact (eq_refl (term260 A B s f x y)). Qed.
Lemma lem4613784 {A : Type'} (s : A -> Prop) (x : A) : (term228 A s x) = (term228 A s x).
Proof. exact (eq_refl (term228 A s x)). Qed.
Lemma lem4613785 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term265 A B s f x y) = (term266 A B s f x y).
Proof. exact (MK_COMB (@lem4613784 A s x) (@lem4613783 A B s f x y)). Qed.
Lemma lem4613786 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term267 A B s f x) = (term268 A B s f x).
Proof. exact (fun_ext (fun y : B => @lem4613785 A B s f x y)). Qed.
Lemma lem4613787 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4613788 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term258 A B s f x) = (term269 A B s f x).
Proof. exact (MK_COMB (@lem4613787 B) (@lem4613786 A B s f x)). Qed.
Lemma lem4613789 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : ((term257 A B s f x) = (term258 A B s f x)) = ((term254 A B s f x) = (term269 A B s f x)).
Proof. exact (MK_COMB (@lem4613782 A B s f x) (@lem4613788 A B s f x)). Qed.
Lemma lem4613790 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term254 A B s f x) = (term269 A B s f x).
Proof. exact (EQ_MP (@lem4613789 A B s f x) (@lem4613774 A B s f x)). Qed.
Lemma lem4613792 {A : Type'} (P : Prop) (Q : A -> Prop) : (term255 A P Q) = (term256 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4613793 {A : Type'} (P : Prop) (Q : A -> Prop) : (term255 A P Q) = (term256 A P Q).
Proof. exact (@lem4613792 A P Q). Qed.
Lemma lem4613794 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term270 A B s f x y) = (term271 A B s f x y).
Proof. exact (@lem4613793 A (term259 A s x) (term250 A B s f x y)). Qed.
Lemma lem4613795 {A B : Type'} (x' : A) (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term272 A B s f x y x') = (term248 A B x' s f x y).
Proof. exact (eq_refl (term272 A B s f x y x')). Qed.
Lemma lem4613796 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term273 A B s f x y) = (term250 A B s f x y).
Proof. exact (fun_ext (fun x' : A => @lem4613795 A B x' s f x y)). Qed.
Lemma lem4613797 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4613798 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term274 A B s f x y) = (term251 A B s f x y).
Proof. exact (MK_COMB (@lem4613797 A) (@lem4613796 A B s f x y)). Qed.
Lemma lem4613799 {A : Type'} (s : A -> Prop) (x : A) : (term228 A s x) = (term228 A s x).
Proof. exact (eq_refl (term228 A s x)). Qed.
Lemma lem4613800 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term270 A B s f x y) = (term266 A B s f x y).
Proof. exact (MK_COMB (@lem4613799 A s x) (@lem4613798 A B s f x y)). Qed.
Lemma lem4613801 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4613802 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term275 A B s f x y) = (term276 A B s f x y).
Proof. exact (MK_COMB (@lem4613801) (@lem4613800 A B s f x y)). Qed.
Lemma lem4613803 {A B : Type'} (x' : A) (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term272 A B s f x y x') = (term248 A B x' s f x y).
Proof. exact (eq_refl (term272 A B s f x y x')). Qed.
Lemma lem4613804 {A : Type'} (s : A -> Prop) (x : A) : (term228 A s x) = (term228 A s x).
Proof. exact (eq_refl (term228 A s x)). Qed.
Lemma lem4613805 {A B : Type'} (x' : A) (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term277 A B s f x y x') = (term278 A B x' s f x y).
Proof. exact (MK_COMB (@lem4613804 A s x) (@lem4613803 A B x' s f x y)). Qed.
Lemma lem4613806 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term279 A B s f x y) = (term280 A B s f x y).
Proof. exact (fun_ext (fun x' : A => @lem4613805 A B x' s f x y)). Qed.
Lemma lem4613807 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4613808 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term271 A B s f x y) = (term281 A B s f x y).
Proof. exact (MK_COMB (@lem4613807 A) (@lem4613806 A B s f x y)). Qed.
Lemma lem4613809 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : ((term270 A B s f x y) = (term271 A B s f x y)) = ((term266 A B s f x y) = (term281 A B s f x y)).
Proof. exact (MK_COMB (@lem4613802 A B s f x y) (@lem4613808 A B s f x y)). Qed.
Lemma lem4613810 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term266 A B s f x y) = (term281 A B s f x y).
Proof. exact (EQ_MP (@lem4613809 A B s f x y) (@lem4613794 A B s f x y)). Qed.
Lemma lem4613811 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term268 A B s f x) = (term282 A B s f x).
Proof. exact (fun_ext (fun y : B => @lem4613810 A B s f x y)). Qed.
Lemma lem4613812 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4613813 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term269 A B s f x) = (term283 A B s f x).
Proof. exact (MK_COMB (@lem4613812 B) (@lem4613811 A B s f x)). Qed.
Lemma lem4613814 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term254 A B s f x) = (term283 A B s f x).
Proof. exact (TRANS (@lem4613790 A B s f x) (@lem4613813 A B s f x)). Qed.
Lemma lem4613815 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term229 A B s f x) = (term283 A B s f x).
Proof. exact (TRANS (@lem4613770 A B s f x) (@lem4613814 A B s f x)). Qed.
Lemma lem4613816 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term233 A B s f x) = (term233 A B s f x).
Proof. exact (eq_refl (term233 A B s f x)). Qed.
Lemma lem4613817 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term235 A B s f x) = (term284 A B s f x).
Proof. exact (MK_COMB (@lem4613816 A B s f x) (@lem4613815 A B s f x)). Qed.
Lemma lem4613819 {A : Type'} (P : Prop) (Q : A -> Prop) : (term285 A P Q) = (term286 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4613820 {B : Type'} (P : Prop) (Q : B -> Prop) : (term285 B P Q) = (term286 B P Q).
Proof. exact (@lem4613819 B P Q). Qed.
Lemma lem4613821 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term287 A B s f x) = (term288 A B s f x).
Proof. exact (@lem4613820 B (term231 A B s f x) (term282 A B s f x)). Qed.
Lemma lem4613822 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term289 A B s f x y) = (term281 A B s f x y).
Proof. exact (eq_refl (term289 A B s f x y)). Qed.
Lemma lem4613823 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term290 A B s f x) = (term282 A B s f x).
Proof. exact (fun_ext (fun y : B => @lem4613822 A B s f x y)). Qed.
Lemma lem4613824 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4613825 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term291 A B s f x) = (term283 A B s f x).
Proof. exact (MK_COMB (@lem4613824 B) (@lem4613823 A B s f x)). Qed.
Lemma lem4613826 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term233 A B s f x) = (term233 A B s f x).
Proof. exact (eq_refl (term233 A B s f x)). Qed.
Lemma lem4613827 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term287 A B s f x) = (term284 A B s f x).
Proof. exact (MK_COMB (@lem4613826 A B s f x) (@lem4613825 A B s f x)). Qed.
Lemma lem4613828 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4613829 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term292 A B s f x) = (term293 A B s f x).
Proof. exact (MK_COMB (@lem4613828) (@lem4613827 A B s f x)). Qed.
Lemma lem4613830 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term289 A B s f x y) = (term281 A B s f x y).
Proof. exact (eq_refl (term289 A B s f x y)). Qed.
Lemma lem4613831 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term233 A B s f x) = (term233 A B s f x).
Proof. exact (eq_refl (term233 A B s f x)). Qed.
Lemma lem4613832 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term294 A B s f x y) = (term295 A B s f x y).
Proof. exact (MK_COMB (@lem4613831 A B s f x) (@lem4613830 A B s f x y)). Qed.
Lemma lem4613833 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term296 A B s f x) = (term297 A B s f x).
Proof. exact (fun_ext (fun y : B => @lem4613832 A B s f x y)). Qed.
Lemma lem4613834 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4613835 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term288 A B s f x) = (term298 A B s f x).
Proof. exact (MK_COMB (@lem4613834 B) (@lem4613833 A B s f x)). Qed.
Lemma lem4613836 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : ((term287 A B s f x) = (term288 A B s f x)) = ((term284 A B s f x) = (term298 A B s f x)).
Proof. exact (MK_COMB (@lem4613829 A B s f x) (@lem4613835 A B s f x)). Qed.
Lemma lem4613837 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term284 A B s f x) = (term298 A B s f x).
Proof. exact (EQ_MP (@lem4613836 A B s f x) (@lem4613821 A B s f x)). Qed.
Lemma lem4613839 {A : Type'} (P : Prop) (Q : A -> Prop) : (term285 A P Q) = (term286 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4613840 {A : Type'} (P : Prop) (Q : A -> Prop) : (term285 A P Q) = (term286 A P Q).
Proof. exact (@lem4613839 A P Q). Qed.
Lemma lem4613841 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term299 A B s f x y) = (term300 A B s f x y).
Proof. exact (@lem4613840 A (term231 A B s f x) (term280 A B s f x y)). Qed.
Lemma lem4613842 {A B : Type'} (x' : A) (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term301 A B s f x y x') = (term278 A B x' s f x y).
Proof. exact (eq_refl (term301 A B s f x y x')). Qed.
Lemma lem4613843 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term302 A B s f x y) = (term280 A B s f x y).
Proof. exact (fun_ext (fun x' : A => @lem4613842 A B x' s f x y)). Qed.
Lemma lem4613844 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4613845 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term303 A B s f x y) = (term281 A B s f x y).
Proof. exact (MK_COMB (@lem4613844 A) (@lem4613843 A B s f x y)). Qed.
Lemma lem4613846 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term233 A B s f x) = (term233 A B s f x).
Proof. exact (eq_refl (term233 A B s f x)). Qed.
Lemma lem4613847 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term299 A B s f x y) = (term295 A B s f x y).
Proof. exact (MK_COMB (@lem4613846 A B s f x) (@lem4613845 A B s f x y)). Qed.
Lemma lem4613848 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4613849 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term304 A B s f x y) = (term305 A B s f x y).
Proof. exact (MK_COMB (@lem4613848) (@lem4613847 A B s f x y)). Qed.
Lemma lem4613850 {A B : Type'} (x' : A) (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term301 A B s f x y x') = (term278 A B x' s f x y).
Proof. exact (eq_refl (term301 A B s f x y x')). Qed.
Lemma lem4613851 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term233 A B s f x) = (term233 A B s f x).
Proof. exact (eq_refl (term233 A B s f x)). Qed.
Lemma lem4613852 {A B : Type'} (x' : A) (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term306 A B s f x y x') = (term307 A B x' s f x y).
Proof. exact (MK_COMB (@lem4613851 A B s f x) (@lem4613850 A B x' s f x y)). Qed.
Lemma lem4613853 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term308 A B s f x y) = (term309 A B s f x y).
Proof. exact (fun_ext (fun x' : A => @lem4613852 A B x' s f x y)). Qed.
Lemma lem4613854 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4613855 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term300 A B s f x y) = (term310 A B s f x y).
Proof. exact (MK_COMB (@lem4613854 A) (@lem4613853 A B s f x y)). Qed.
Lemma lem4613856 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : ((term299 A B s f x y) = (term300 A B s f x y)) = ((term295 A B s f x y) = (term310 A B s f x y)).
Proof. exact (MK_COMB (@lem4613849 A B s f x y) (@lem4613855 A B s f x y)). Qed.
Lemma lem4613857 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term295 A B s f x y) = (term310 A B s f x y).
Proof. exact (EQ_MP (@lem4613856 A B s f x y) (@lem4613841 A B s f x y)). Qed.
Lemma lem4613858 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term297 A B s f x) = (term311 A B s f x).
Proof. exact (fun_ext (fun y : B => @lem4613857 A B s f x y)). Qed.
Lemma lem4613859 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4613860 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term298 A B s f x) = (term312 A B s f x).
Proof. exact (MK_COMB (@lem4613859 B) (@lem4613858 A B s f x)). Qed.
Lemma lem4613861 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term284 A B s f x) = (term312 A B s f x).
Proof. exact (TRANS (@lem4613837 A B s f x) (@lem4613860 A B s f x)). Qed.
Lemma lem4613863 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term235 A B s f x) = (term312 A B s f x).
Proof. exact (TRANS (@lem4613817 A B s f x) (@lem4613861 A B s f x)). Qed.
Lemma lem4613864 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term203 A B s f x) = (term312 A B s f x).
Proof. exact (TRANS (@lem4613564 A B s f x) (@lem4613863 A B s f x)). Qed.
Lemma lem4613865 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term203 A B s f x) : term312 A B s f x.
Proof. exact (EQ_MP (@lem4613864 A B s f x) (@lem4613493 A B s f x h1)). Qed.
Lemma lem4613866 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) (h1 : term310 A B s f x y) : term310 A B s f x y.
Proof. exact (h1). Qed.
Lemma lem4613867 {A B : Type'} (x' : A) (s : A -> Prop) (f : A -> B) (x : A) (y : B) (h1 : term307 A B x' s f x y) : term307 A B x' s f x y.
Proof. exact (h1). Qed.
Lemma lem4613904 {A B : Type'} (x' : A) (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term278 A B x' s f x y) = (term278 A B x' s f x y).
Proof. exact (eq_refl (term278 A B x' s f x y)). Qed.
Lemma lem4613921 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term215 A B s f x y) = (term215 A B s f x y).
Proof. exact (eq_refl (term215 A B s f x y)). Qed.
Lemma lem4613938 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) : (term205 A B y f s x) = (term205 A B y f s x).
Proof. exact (eq_refl (term205 A B y f s x)). Qed.
Lemma lem4613939 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term212 A B y f s) = (term212 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem4613938 A B y f s x)). Qed.
Lemma lem4613940 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4613941 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term213 A B y f s) = (term213 A B y f s).
Proof. exact (MK_COMB (@lem4613940 A) (@lem4613939 A B y f s)). Qed.
Lemma lem4613942 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4613943 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term217 A B y f s) = (term217 A B y f s).
Proof. exact (MK_COMB (@lem4613942) (@lem4613941 A B y f s)). Qed.
Lemma lem4613944 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term219 A B s f x y) = (term219 A B s f x y).
Proof. exact (MK_COMB (@lem4613943 A B y f s) (@lem4613921 A B s f x y)). Qed.
Lemma lem4613945 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term226 A B s f x) = (term226 A B s f x).
Proof. exact (fun_ext (fun y : B => @lem4613944 A B s f x y)). Qed.
Lemma lem4613946 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4613947 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term227 A B s f x) = (term227 A B s f x).
Proof. exact (MK_COMB (@lem4613946 B) (@lem4613945 A B s f x)). Qed.
Lemma lem4613952 {A : Type'} (s : A -> Prop) (x : A) : (term179 A s x) = (term179 A s x).
Proof. exact (eq_refl (term179 A s x)). Qed.
Lemma lem4613953 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term231 A B s f x) = (term231 A B s f x).
Proof. exact (MK_COMB (@lem4613952 A s x) (@lem4613947 A B s f x)). Qed.
Lemma lem4613954 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4613955 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term233 A B s f x) = (term233 A B s f x).
Proof. exact (MK_COMB (@lem4613954) (@lem4613953 A B s f x)). Qed.
Lemma lem4613956 {A B : Type'} (x' : A) (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term307 A B x' s f x y) = (term307 A B x' s f x y).
Proof. exact (MK_COMB (@lem4613955 A B s f x) (@lem4613904 A B x' s f x y)). Qed.
Lemma lem4613957 {A B : Type'} (x' : A) (s : A -> Prop) (f : A -> B) (x : A) (y : B) (h1 : term307 A B x' s f x y) : term307 A B x' s f x y.
Proof. exact (EQ_MP (@lem4613956 A B x' s f x y) (@lem4613867 A B x' s f x y h1)). Qed.
Lemma lem4613958 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term231 A B s f x) : term231 A B s f x.
Proof. exact (h1). Qed.
Lemma lem4613959 {A B : Type'} (x' : A) (s : A -> Prop) (f : A -> B) (x : A) (y : B) (h1 : term278 A B x' s f x y) : term278 A B x' s f x y.
Proof. exact (h1). Qed.
Lemma lem4613960 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term231 A B s f x) : term227 A B s f x.
Proof. exact (proj2 (@lem4613958 A B s f x h1)). Qed.
Lemma lem4613962 {A B : Type'} (x' : A) (s : A -> Prop) (f : A -> B) (x : A) (y : B) (h1 : term278 A B x' s f x y) : term248 A B x' s f x y.
Proof. exact (proj2 (@lem4613959 A B x' s f x y h1)). Qed.
Lemma lem4613964 {A B : Type'} (x' : A) (s : A -> Prop) (f : A -> B) (x : A) (y : B) (h1 : term278 A B x' s f x y) : term180 A B s f x y.
Proof. exact (proj2 (@lem4613962 A B x' s f x y h1)). Qed.
Lemma lem4613975 {A : Type'} (P : A -> Prop) (Q : Prop) : (term313 A P Q) = (term314 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem4613976 {A : Type'} (P : A -> Prop) (Q : Prop) : (term313 A P Q) = (term314 A P Q).
Proof. exact (@lem4613975 A P Q). Qed.
Lemma lem4613977 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term315 A B s f x y) = (term316 A B s f x y).
Proof. exact (@lem4613976 A (term212 A B y f s) (term215 A B s f x y)). Qed.
Lemma lem4613978 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x : A) : (term317 A B y f s x) = (term205 A B y f s x).
Proof. exact (eq_refl (term317 A B y f s x)). Qed.
Lemma lem4613979 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term318 A B y f s) = (term212 A B y f s).
Proof. exact (fun_ext (fun x : A => @lem4613978 A B y f s x)). Qed.
Lemma lem4613980 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4613981 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term319 A B y f s) = (term213 A B y f s).
Proof. exact (MK_COMB (@lem4613980 A) (@lem4613979 A B y f s)). Qed.
Lemma lem4613982 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4613983 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term320 A B y f s) = (term217 A B y f s).
Proof. exact (MK_COMB (@lem4613982) (@lem4613981 A B y f s)). Qed.
Lemma lem4613984 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term215 A B s f x y) = (term215 A B s f x y).
Proof. exact (eq_refl (term215 A B s f x y)). Qed.
Lemma lem4613985 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term315 A B s f x y) = (term219 A B s f x y).
Proof. exact (MK_COMB (@lem4613983 A B y f s) (@lem4613984 A B s f x y)). Qed.
Lemma lem4613986 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4613987 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term321 A B s f x y) = (term322 A B s f x y).
Proof. exact (MK_COMB (@lem4613986) (@lem4613985 A B s f x y)). Qed.
Lemma lem4613988 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term317 A B y f s x') = (term205 A B y f s x').
Proof. exact (eq_refl (term317 A B y f s x')). Qed.
Lemma lem4613989 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4613990 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) (x' : A) : (term323 A B y f s x') = (term324 A B y f s x').
Proof. exact (MK_COMB (@lem4613989) (@lem4613988 A B y f s x')). Qed.
Lemma lem4613991 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term215 A B s f x y) = (term215 A B s f x y).
Proof. exact (eq_refl (term215 A B s f x y)). Qed.
Lemma lem4613992 {A B : Type'} (x' : A) (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term325 A B x' s f x y) = (term326 A B x' s f x y).
Proof. exact (MK_COMB (@lem4613990 A B y f s x') (@lem4613991 A B s f x y)). Qed.
Lemma lem4613993 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term327 A B s f x y) = (term328 A B s f x y).
Proof. exact (fun_ext (fun x' : A => @lem4613992 A B x' s f x y)). Qed.
Lemma lem4613994 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4613995 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term316 A B s f x y) = (term329 A B s f x y).
Proof. exact (MK_COMB (@lem4613994 A) (@lem4613993 A B s f x y)). Qed.
Lemma lem4613996 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : ((term315 A B s f x y) = (term316 A B s f x y)) = ((term219 A B s f x y) = (term329 A B s f x y)).
Proof. exact (MK_COMB (@lem4613987 A B s f x y) (@lem4613995 A B s f x y)). Qed.
Lemma lem4613997 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term219 A B s f x y) = (term329 A B s f x y).
Proof. exact (EQ_MP (@lem4613996 A B s f x y) (@lem4613977 A B s f x y)). Qed.
Lemma lem4613998 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term226 A B s f x) = (term330 A B s f x).
Proof. exact (fun_ext (fun y : B => @lem4613997 A B s f x y)). Qed.
Lemma lem4613999 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4614000 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term227 A B s f x) = (term331 A B s f x).
Proof. exact (MK_COMB (@lem4613999 B) (@lem4613998 A B s f x)). Qed.
Lemma lem4614019 {A B : Type'} (x' : A) (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term326 A B x' s f x y) = (term326 A B x' s f x y).
Proof. exact (eq_refl (term326 A B x' s f x y)). Qed.
Lemma lem4614020 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term328 A B s f x y) = (term328 A B s f x y).
Proof. exact (fun_ext (fun x' : A => @lem4614019 A B x' s f x y)). Qed.
Lemma lem4614021 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4614022 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) : (term329 A B s f x y) = (term329 A B s f x y).
Proof. exact (MK_COMB (@lem4614021 A) (@lem4614020 A B s f x y)). Qed.
Lemma lem4614023 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term330 A B s f x) = (term330 A B s f x).
Proof. exact (fun_ext (fun y : B => @lem4614022 A B s f x y)). Qed.
Lemma lem4614024 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4614025 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term331 A B s f x) = (term331 A B s f x).
Proof. exact (MK_COMB (@lem4614024 B) (@lem4614023 A B s f x)). Qed.
Lemma lem4614026 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term227 A B s f x) = (term331 A B s f x).
Proof. exact (TRANS (@lem4614000 A B s f x) (@lem4614025 A B s f x)). Qed.
Lemma lem4614027 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term231 A B s f x) : term331 A B s f x.
Proof. exact (EQ_MP (@lem4614026 A B s f x) (@lem4613960 A B s f x h1)). Qed.
Lemma lem4614048 {A B : Type'} (_55443 : B) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term231 A B s f x) : term332 A B s f x _55443.
Proof. exact (@lem4614027 A B s f x h1 _55443). Qed.
Lemma lem4614049 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (_55443 : B) : (term332 A B s f x _55443) = (term329 A B s f x _55443).
Proof. exact (eq_refl (term332 A B s f x _55443)). Qed.
Lemma lem4614050 {A B : Type'} (_55443 : B) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term231 A B s f x) : term329 A B s f x _55443.
Proof. exact (EQ_MP (@lem4614049 A B s f x _55443) (@lem4614048 A B _55443 s f x h1)). Qed.
Lemma lem4614051 {A B : Type'} (_55443 : B) (_55444 : A) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term231 A B s f x) : term333 A B s f x _55443 _55444.
Proof. exact (@lem4614050 A B _55443 s f x h1 _55444). Qed.
Lemma lem4614052 {A B : Type'} (_55444 : A) (s : A -> Prop) (f : A -> B) (x : A) (_55443 : B) : (term333 A B s f x _55443 _55444) = (term326 A B _55444 s f x _55443).
Proof. exact (eq_refl (term333 A B s f x _55443 _55444)). Qed.
Lemma lem4614053 {A B : Type'} (_55444 : A) (_55443 : B) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term231 A B s f x) : term326 A B _55444 s f x _55443.
Proof. exact (EQ_MP (@lem4614052 A B _55444 s f x _55443) (@lem4614051 A B _55443 _55444 s f x h1)). Qed.
Lemma lem4614070 {A B : Type'} (_55444 : A) (s : A -> Prop) (f : A -> B) (x : A) (_55443 : B) : (term326 A B _55444 s f x _55443) = (term334 A B _55444 s f x _55443).
Proof. exact (@lem4612774 (term335 A B _55443 f _55444) (term259 A s _55444) (term215 A B s f x _55443)). Qed.
Lemma lem4614071 {A B : Type'} (_55444 : A) (_55443 : B) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term231 A B s f x) : term334 A B _55444 s f x _55443.
Proof. exact (EQ_MP (@lem4614070 A B _55444 s f x _55443) (@lem4614053 A B _55444 _55443 s f x h1)). Qed.
Lemma lem4614109 {A B : Type'} (x' : A) (s : A -> Prop) (f : A -> B) (x : A) (y : B) (h1 : term278 A B x' s f x y) : term259 A s x.
Proof. exact (proj1 (@lem4613959 A B x' s f x y h1)). Qed.
Lemma lem4614176 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem4614177 {B : Type'} (x : B) : x = x.
Proof. exact (@lem4614176 B x). Qed.
Lemma lem4614178 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (@lem4614177 B (f x)). Qed.
Lemma lem4614179 {A B : Type'} (f : A -> B) (x : A) : term336 A B f x.
Proof. exact (fun h0 : term337 A B f x => @lem4614178 A B f x). Qed.
Lemma lem4614181 (p : Prop) : (term338 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4614182 {A B : Type'} (f : A -> B) (x : A) : (term336 A B f x) = ((f x) = (f x)).
Proof. exact (@lem4614181 ((f x) = (f x))). Qed.
Lemma lem4614183 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (EQ_MP (@lem4614182 A B f x) (@lem4614179 A B f x)). Qed.
Lemma lem4614185 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term231 A B s f x) : s x.
Proof. exact (proj1 (@lem4613958 A B s f x h1)). Qed.
Lemma lem4614186 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term231 A B s f x) : term339 A s x.
Proof. exact (fun h0 : term259 A s x => @lem4614185 A B s f x h1). Qed.
Lemma lem4614188 (p : Prop) : (term338 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4614189 {A : Type'} (s : A -> Prop) (x : A) : (term339 A s x) = (s x).
Proof. exact (@lem4614188 (s x)). Qed.
Lemma lem4614190 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term231 A B s f x) : s x.
Proof. exact (EQ_MP (@lem4614189 A s x) (@lem4614186 A B s f x h1)). Qed.
Lemma lem4614192 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term231 A B s f x) : s x.
Proof. exact (proj1 (@lem4613958 A B s f x h1)). Qed.
Lemma lem4614193 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term231 A B s f x) : term339 A s x.
Proof. exact (fun h0 : term259 A s x => @lem4614192 A B s f x h1). Qed.
Lemma lem4614195 (p : Prop) : (term338 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4614196 {A : Type'} (s : A -> Prop) (x : A) : (term339 A s x) = (s x).
Proof. exact (@lem4614195 (s x)). Qed.
Lemma lem4614197 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term231 A B s f x) : s x.
Proof. exact (EQ_MP (@lem4614196 A s x) (@lem4614193 A B s f x h1)). Qed.
Lemma lem4614199 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem4614200 {B : Type'} (x : B) : x = x.
Proof. exact (@lem4614199 B x). Qed.
Lemma lem4614201 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (@lem4614200 B (f x)). Qed.
Lemma lem4614202 {A B : Type'} (f : A -> B) (x : A) : term336 A B f x.
Proof. exact (fun h0 : term337 A B f x => @lem4614201 A B f x). Qed.
Lemma lem4614204 (p : Prop) : (term338 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4614205 {A B : Type'} (f : A -> B) (x : A) : (term336 A B f x) = ((f x) = (f x)).
Proof. exact (@lem4614204 ((f x) = (f x))). Qed.
Lemma lem4614206 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (EQ_MP (@lem4614205 A B f x) (@lem4614202 A B f x)). Qed.
Lemma lem4614208 (a : Prop) (b : Prop) : (term340 a b) = (term21 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4614209 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (_55443 : B) : (term215 A B s f x _55443) = (term214 A B s f x _55443).
Proof. exact (@lem4614208 (s x) ((f x) = _55443)). Qed.
Lemma lem4614210 {A : Type'} (s : A -> Prop) (_55444 : A) : (term341 A s _55444) = (term341 A s _55444).
Proof. exact (eq_refl (term341 A s _55444)). Qed.
Lemma lem4614211 {A B : Type'} (_55444 : A) (s : A -> Prop) (f : A -> B) (x : A) (_55443 : B) : (term342 A B _55444 s f x _55443) = (term343 A B _55444 s f x _55443).
Proof. exact (MK_COMB (@lem4614210 A s _55444) (@lem4614209 A B s f x _55443)). Qed.
Lemma lem4614213 (a : Prop) (b : Prop) : (term340 a b) = (term21 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4614214 {A B : Type'} (_55444 : A) (s : A -> Prop) (f : A -> B) (x : A) (_55443 : B) : (term343 A B _55444 s f x _55443) = (term344 A B _55444 s f x _55443).
Proof. exact (@lem4614213 (s _55444) (term180 A B s f x _55443)). Qed.
Lemma lem4614215 {A B : Type'} (_55444 : A) (s : A -> Prop) (f : A -> B) (x : A) (_55443 : B) : (term342 A B _55444 s f x _55443) = (term344 A B _55444 s f x _55443).
Proof. exact (TRANS (@lem4614211 A B _55444 s f x _55443) (@lem4614214 A B _55444 s f x _55443)). Qed.
Lemma lem4614216 {A B : Type'} (_55443 : B) (f : A -> B) (_55444 : A) : (term345 A B _55443 f _55444) = (term345 A B _55443 f _55444).
Proof. exact (eq_refl (term345 A B _55443 f _55444)). Qed.
Lemma lem4614217 {A B : Type'} (_55444 : A) (s : A -> Prop) (f : A -> B) (x : A) (_55443 : B) : (term334 A B _55444 s f x _55443) = (term346 A B _55444 s f x _55443).
Proof. exact (MK_COMB (@lem4614216 A B _55443 f _55444) (@lem4614215 A B _55444 s f x _55443)). Qed.
Lemma lem4614219 (a : Prop) (b : Prop) : (term340 a b) = (term21 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4614220 {A B : Type'} (_55444 : A) (s : A -> Prop) (f : A -> B) (x : A) (_55443 : B) : (term346 A B _55444 s f x _55443) = (term347 A B _55444 s f x _55443).
Proof. exact (@lem4614219 (_55443 = (f _55444)) (term348 A B _55444 s f x _55443)). Qed.
Lemma lem4614221 {A B : Type'} (_55444 : A) (s : A -> Prop) (f : A -> B) (x : A) (_55443 : B) : (term334 A B _55444 s f x _55443) = (term347 A B _55444 s f x _55443).
Proof. exact (TRANS (@lem4614217 A B _55444 s f x _55443) (@lem4614220 A B _55444 s f x _55443)). Qed.
Lemma lem4614223 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4614224 {A B : Type'} (_55444 : A) (s : A -> Prop) (f : A -> B) (x : A) (_55443 : B) : (term347 A B _55444 s f x _55443) = (term349 A B _55444 s f x _55443).
Proof. exact (@lem4614223 (term350 A B _55444 s f x _55443)). Qed.
Lemma lem4614225 {A B : Type'} (_55444 : A) (s : A -> Prop) (f : A -> B) (x : A) (_55443 : B) : (term334 A B _55444 s f x _55443) = (term349 A B _55444 s f x _55443).
Proof. exact (TRANS (@lem4614221 A B _55444 s f x _55443) (@lem4614224 A B _55444 s f x _55443)). Qed.
Lemma lem4614227 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term231 A B s f x) : term351 A B s f x.
Proof. exact (conj (@lem4614197 A B s f x h1) (@lem4614206 A B f x)). Qed.
Lemma lem4614228 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term231 A B s f x) : term352 A B s f x.
Proof. exact (conj (@lem4614190 A B s f x h1) (@lem4614227 A B s f x h1)). Qed.
Lemma lem4614229 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term231 A B s f x) : term353 A B s f x.
Proof. exact (conj (@lem4614183 A B f x) (@lem4614228 A B s f x h1)). Qed.
Lemma lem4614231 {A B : Type'} (_55444 : A) (_55443 : B) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term231 A B s f x) : term349 A B _55444 s f x _55443.
Proof. exact (EQ_MP (@lem4614225 A B _55444 s f x _55443) (@lem4614071 A B _55444 _55443 s f x h1)). Qed.
Lemma lem4614232 {A B : Type'} (_55444 : A) (_55443 : B) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term231 A B s f x) : term349 A B _55444 s f x _55443.
Proof. exact (@lem4614231 A B _55444 _55443 s f x h1). Qed.
Lemma lem4614233 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term231 A B s f x) : term354 A B s f x.
Proof. exact (@lem4614232 A B x (f x) s f x h1). Qed.
Lemma lem4614236 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term231 A B s f x) : False.
Proof. exact (@lem4614233 A B s f x h1 (@lem4614229 A B s f x h1)). Qed.
Lemma lem4614237 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term231 A B s f x) : term355.
Proof. exact (fun h0 : ~ False => @lem4614236 A B s f x h1). Qed.
Lemma lem4614239 (p : Prop) : (term338 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4614240 : term355 = False.
Proof. exact (@lem4614239 False). Qed.
Lemma lem4614241 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term231 A B s f x) : False.
Proof. exact (EQ_MP (@lem4614240) (@lem4614237 A B s f x h1)). Qed.
Lemma lem4614267 {A B : Type'} (x' : A) (s : A -> Prop) (f : A -> B) (x : A) (y : B) (h1 : term278 A B x' s f x y) : s x.
Proof. exact (proj1 (@lem4613964 A B x' s f x y h1)). Qed.
Lemma lem4614268 {A B : Type'} (x' : A) (s : A -> Prop) (f : A -> B) (x : A) (y : B) (h1 : term278 A B x' s f x y) : term339 A s x.
Proof. exact (fun h0 : term259 A s x => @lem4614267 A B x' s f x y h1). Qed.
Lemma lem4614270 (p : Prop) : (term338 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4614271 {A : Type'} (s : A -> Prop) (x : A) : (term339 A s x) = (s x).
Proof. exact (@lem4614270 (s x)). Qed.
Lemma lem4614272 {A B : Type'} (x' : A) (s : A -> Prop) (f : A -> B) (x : A) (y : B) (h1 : term278 A B x' s f x y) : s x.
Proof. exact (EQ_MP (@lem4614271 A s x) (@lem4614268 A B x' s f x y h1)). Qed.
Lemma lem4614275 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4614277 {A : Type'} (s : A -> Prop) (x : A) : (term259 A s x) = (term356 A s x).
Proof. exact (@lem4614275 (s x)). Qed.
Lemma lem4614280 {A B : Type'} (x' : A) (s : A -> Prop) (f : A -> B) (x : A) (y : B) (h1 : term278 A B x' s f x y) : term356 A s x.
Proof. exact (EQ_MP (@lem4614277 A s x) (@lem4614109 A B x' s f x y h1)). Qed.
Lemma lem4614283 {A B : Type'} (x' : A) (s : A -> Prop) (f : A -> B) (x : A) (y : B) (h1 : term278 A B x' s f x y) : False.
Proof. exact (@lem4614280 A B x' s f x y h1 (@lem4614272 A B x' s f x y h1)). Qed.
Lemma lem4614284 {A B : Type'} (x' : A) (s : A -> Prop) (f : A -> B) (x : A) (y : B) (h1 : term278 A B x' s f x y) : term355.
Proof. exact (fun h0 : ~ False => @lem4614283 A B x' s f x y h1). Qed.
Lemma lem4614286 (p : Prop) : (term338 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4614287 : term355 = False.
Proof. exact (@lem4614286 False). Qed.
Lemma lem4614289 {A B : Type'} (x' : A) (s : A -> Prop) (f : A -> B) (x : A) (y : B) (h1 : term278 A B x' s f x y) : False.
Proof. exact (EQ_MP (@lem4614287) (@lem4614284 A B x' s f x y h1)). Qed.
Lemma lem4614290 {A B : Type'} (x' : A) (s : A -> Prop) (f : A -> B) (x : A) (y : B) (h1 : term307 A B x' s f x y) : False.
Proof. exact (or_elim (@lem4613957 A B x' s f x y h1) (fun h0 : term231 A B s f x => @lem4614241 A B s f x h0) (fun h0 : term278 A B x' s f x y => @lem4614289 A B x' s f x y h0)). Qed.
Lemma lem4614291 {A B : Type'} (x' : A) (s : A -> Prop) (f : A -> B) (x : A) (y : B) (h1 : term307 A B x' s f x y) : (term307 A B x' s f x y) = False.
Proof. exact (prop_ext (fun h2 : term307 A B x' s f x y => @lem4614290 A B x' s f x y h1) (fun h2 : False => @lem4613957 A B x' s f x y h1)). Qed.
Lemma lem4614292 {A B : Type'} (x' : A) (s : A -> Prop) (f : A -> B) (x : A) (y : B) (h1 : term307 A B x' s f x y) : False.
Proof. exact (EQ_MP (@lem4614291 A B x' s f x y h1) (@lem4613957 A B x' s f x y h1)). Qed.
Lemma lem4614293 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : B) (h1 : term310 A B s f x y) : False.
Proof. exact (ex_elim (@lem4613866 A B s f x y h1) (fun x' : A => fun h0 : term309 A B s f x y x' => @lem4614292 A B x' s f x y h0)). Qed.
Lemma lem4614294 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term203 A B s f x) : False.
Proof. exact (ex_elim (@lem4613865 A B s f x h1) (fun y : B => fun h0 : term311 A B s f x y => @lem4614293 A B s f x y h0)). Qed.
Lemma lem4614295 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term203 A B s f x) : (term203 A B s f x) = False.
Proof. exact (prop_ext (fun h2 : term203 A B s f x => @lem4614294 A B s f x h1) (fun h2 : False => @lem4613493 A B s f x h1)). Qed.
Lemma lem4614296 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term203 A B s f x) : False.
Proof. exact (EQ_MP (@lem4614295 A B s f x h1) (@lem4613493 A B s f x h1)). Qed.
Lemma lem4614297 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : term202 A B s f x.
Proof. exact (fun h0 : term203 A B s f x => @lem4614296 A B s f x h0). Qed.
Lemma lem4614298 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (s x) = (term183 A B s f x).
Proof. exact (EQ_MP (@lem4613492 A B s f x) (@lem4614297 A B s f x)). Qed.
Lemma lem4614303 {A B : Type'} (s : A -> Prop) (f : A -> B) : term186 A B s f.
Proof. exact (fun x : A => @lem4614298 A B s f x). Qed.
Lemma lem4614308 {A B : Type'} (f : A -> B) : term197 A B f.
Proof. exact (fun s : A -> Prop => @lem4614303 A B s f). Qed.
Lemma lem4614313 {A B : Type'} : term201 A B.
Proof. exact (fun f : A -> B => @lem4614308 A B f). Qed.
Lemma lem4614314 {A B : Type'} : term200 A B.
Proof. exact (EQ_MP (@lem4613488 A B) (@lem4614313 A B)). Qed.
Lemma lem4614315 {A B : Type'} (f : A -> B) : term357 A B f.
Proof. exact (@lem4614314 A B f). Qed.
Lemma lem4614316 {A B : Type'} (f : A -> B) : (term357 A B f) = (term196 A B f).
Proof. exact (eq_refl (term357 A B f)). Qed.
Lemma lem4614317 {A B : Type'} (f : A -> B) : term196 A B f.
Proof. exact (EQ_MP (@lem4614316 A B f) (@lem4614315 A B f)). Qed.
Lemma lem4614318 {A B : Type'} (f : A -> B) (s : A -> Prop) : term358 A B f s.
Proof. exact (@lem4614317 A B f s). Qed.
Lemma lem4614319 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term358 A B f s) = (term188 A B s f).
Proof. exact (eq_refl (term358 A B f s)). Qed.
Lemma lem4614320 {A B : Type'} (s : A -> Prop) (f : A -> B) : term188 A B s f.
Proof. exact (EQ_MP (@lem4614319 A B s f) (@lem4614318 A B f s)). Qed.
Lemma lem4614322 {A B : Type'} (s : A -> Prop) (f : A -> B) : term188 A B s f.
Proof. exact (@lem4613293 A B s f (@lem4614320 A B s f)). Qed.
Lemma lem4614323 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term189 A B s f) : False.
Proof. exact (@lem4614322 A B s f (@lem4613277 A B s f h1)). Qed.
Lemma lem4614324 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term189 A B s f) : (term189 A B s f) = False.
Proof. exact (prop_ext (fun h2 : term189 A B s f => @lem4614323 A B s f h1) (fun h2 : False => @lem4613277 A B s f h1)). Qed.
Lemma lem4614325 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term189 A B s f) : False.
Proof. exact (EQ_MP (@lem4614324 A B s f h1) (@lem4613277 A B s f h1)). Qed.
Lemma lem4614326 {A B : Type'} (s : A -> Prop) (f : A -> B) : term188 A B s f.
Proof. exact (fun h0 : term189 A B s f => @lem4614325 A B s f h0). Qed.
Lemma lem4614327 {A B : Type'} (s : A -> Prop) (f : A -> B) : term186 A B s f.
Proof. exact (EQ_MP (@lem4613276 A B s f) (@lem4614326 A B s f)). Qed.
Lemma lem4614328 {A B : Type'} (s : A -> Prop) (f : A -> B) : term137 A B s f.
Proof. exact (EQ_MP (@lem4613272 A B s f) (@lem4614327 A B s f)). Qed.
Lemma lem4614329 {A B : Type'} (s : A -> Prop) (f : A -> B) : s = (term135 A B s f).
Proof. exact (EQ_MP (@lem4613144 A B s f) (@lem4614328 A B s f)). Qed.
Lemma lem4614330 {A B : Type'} (s : A -> Prop) (f : A -> B) : s = (term86 A B s f).
Proof. exact (EQ_MP (@lem4613109 A B s f) (@lem4614329 A B s f)). Qed.
Lemma lem4614331 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : term359 _87967 _87968 P f.
Proof. exact (@lem3386920 _87967 _87968 P f). Qed.
Lemma lem4614332 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : (term359 _87967 _87968 P f) = (term360 _87967 _87968 P f).
Proof. exact (eq_refl (term359 _87967 _87968 P f)). Qed.
Lemma lem4614333 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : term360 _87967 _87968 P f.
Proof. exact (EQ_MP (@lem4614332 _87967 _87968 P f) (@lem4614331 _87967 _87968 P f)). Qed.
Lemma lem4614334 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) (s : _87968 -> Prop) : term361 _87967 _87968 P f s.
Proof. exact (@lem4614333 _87967 _87968 P f s). Qed.
Lemma lem4614335 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term361 _87967 _87968 P f s) = ((term362 _87967 _87968 f s P) = (term363 _87967 _87968 s P f)).
Proof. exact (eq_refl (term361 _87967 _87968 P f s)). Qed.
Lemma lem4614337 {A B : Type'} (f : A -> B) : term364 A B f.
Proof. exact (@lem3615104 A B f). Qed.
Lemma lem4614338 {A B : Type'} (f : A -> B) : (term364 A B f) = (term365 A B f).
Proof. exact (eq_refl (term364 A B f)). Qed.
Lemma lem4614339 {A B : Type'} (f : A -> B) : term365 A B f.
Proof. exact (EQ_MP (@lem4614338 A B f) (@lem4614337 A B f)). Qed.
Lemma lem4614340 {A B : Type'} (f : A -> B) (s : A -> Prop) : term366 A B f s.
Proof. exact (@lem4614339 A B f s). Qed.
Lemma lem4614341 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term366 A B f s) = (term367 A B f s).
Proof. exact (eq_refl (term366 A B f s)). Qed.
Lemma lem4614342 {A B : Type'} (f : A -> B) (s : A -> Prop) : term367 A B f s.
Proof. exact (EQ_MP (@lem4614341 A B f s) (@lem4614340 A B f s)). Qed.
Lemma lem4614343 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4614344 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : term50 A B f s.
Proof. exact (@lem4614342 A B f s (@lem4614343 A s h1)). Qed.
Lemma lem4614345 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term50 A B f s) = ((term50 A B f s) = True).
Proof. exact (@lem7 (term50 A B f s)). Qed.
Lemma lem4614346 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : (term50 A B f s) = True.
Proof. exact (EQ_MP (@lem4614345 A B f s) (@lem4614344 A B f s h1)). Qed.
Lemma lem4614352 {_88128 _88132 : Type'} (f : _88128 -> _88132) : term368 _88128 _88132 f.
Proof. exact (@lem3393993 _88128 _88132 f). Qed.
Lemma lem4614353 {_88128 _88132 : Type'} (f : _88128 -> _88132) : (term368 _88128 _88132 f) = (term369 _88128 _88132 f).
Proof. exact (eq_refl (term368 _88128 _88132 f)). Qed.
Lemma lem4614354 {_88128 _88132 : Type'} (f : _88128 -> _88132) : term369 _88128 _88132 f.
Proof. exact (EQ_MP (@lem4614353 _88128 _88132 f) (@lem4614352 _88128 _88132 f)). Qed.
Lemma lem4614355 {_88128 _88132 : Type'} (f : _88128 -> _88132) (s : _88128 -> Prop) : term370 _88128 _88132 f s.
Proof. exact (@lem4614354 _88128 _88132 f s). Qed.
Lemma lem4614356 {_88128 _88132 : Type'} (f : _88128 -> _88132) (s : _88128 -> Prop) : (term370 _88128 _88132 f s) = ((term371 _88128 _88132 s f) = (@IMAGE _88128 _88132 f s)).
Proof. exact (eq_refl (term370 _88128 _88132 f s)). Qed.
Lemma lem4614358 {A : Type'} (s : type686 A) : term372 A s.
Proof. exact (@lem4605902 A s). Qed.
Lemma lem4614359 {A : Type'} (s : type686 A) : (term372 A s) = ((term373 A s) = (term374 A s)).
Proof. exact (eq_refl (term372 A s)). Qed.
Lemma lem4614361 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term50 A B f s) = ((term50 A B f s) = True).
Proof. exact (@lem7 (term50 A B f s)). Qed.
Lemma lem4614363 {A B : Type'} (a : A) (s : A -> Prop) (f : A -> B) (h1 : term80 A B s f) : term375 A B s f a.
Proof. exact (@lem4613029 A B s f h1 a). Qed.
Lemma lem4614364 {A B : Type'} (s : A -> Prop) (f : A -> B) (a : A) : (term375 A B s f a) = (term78 A B s f a).
Proof. exact (eq_refl (term375 A B s f a)). Qed.
Lemma lem4614365 {A B : Type'} (a : A) (s : A -> Prop) (f : A -> B) (h1 : term80 A B s f) : term78 A B s f a.
Proof. exact (EQ_MP (@lem4614364 A B s f a) (@lem4614363 A B a s f h1)). Qed.
Lemma lem4614366 {A : Type'} (a : A) (s : A -> Prop) (h1 : @IN A a s) : @IN A a s.
Proof. exact (h1). Qed.
Lemma lem4614367 {A B : Type'} (f : A -> B) (a : A) (s : A -> Prop) (h1 : term80 A B s f) (h2 : @IN A a s) : term76 A B s f a.
Proof. exact (@lem4614365 A B a s f h1 (@lem4614366 A a s h2)). Qed.
Lemma lem4614368 {A B : Type'} (s : A -> Prop) (f : A -> B) (a : A) : (term76 A B s f a) = ((term76 A B s f a) = True).
Proof. exact (@lem7 (term76 A B s f a)). Qed.
Lemma lem4614369 {A B : Type'} (f : A -> B) (a : A) (s : A -> Prop) (h1 : term80 A B s f) (h2 : @IN A a s) : (term76 A B s f a) = True.
Proof. exact (EQ_MP (@lem4614368 A B s f a) (@lem4614367 A B f a s h1 h2)). Qed.
Lemma lem4614376 {A : Type'} (s : type686 A) : (term373 A s) = (term374 A s).
Proof. exact (EQ_MP (@lem4614359 A s) (@lem4614358 A s)). Qed.
Lemma lem4614377 {A : Type'} (s : type686 A) : (term373 A s) = (term374 A s).
Proof. exact (@lem4614376 A s). Qed.
Lemma lem4614378 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term90 A B s f) = (term376 A B s f).
Proof. exact (@lem4614377 A (term112 A B s f)). Qed.
Lemma lem4614382 {_88128 _88132 : Type'} (f : _88128 -> _88132) (s : _88128 -> Prop) : (term371 _88128 _88132 s f) = (@IMAGE _88128 _88132 f s).
Proof. exact (EQ_MP (@lem4614356 _88128 _88132 f s) (@lem4614355 _88128 _88132 f s)). Qed.
Lemma lem4614383 {A B : Type'} (f : type1470 A B) (s : B -> Prop) : (term377 A B s f) = (@IMAGE B (A -> Prop) f s).
Proof. exact (@lem4614382 B (A -> Prop) f s). Qed.
Lemma lem4614384 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term378 A B s f) = (term379 A B f s).
Proof. exact (@lem4614383 A B (term96 A B s f) (@IMAGE A B f s)). Qed.
Lemma lem4614385 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term101 A B s f y) = (term102 A B s f y).
Proof. exact (eq_refl (term101 A B s f y)). Qed.
Lemma lem4614386 {A B : Type'} (GEN_PVAR_168 : A -> Prop) (y : B) (f : A -> B) (s : A -> Prop) : (term100 A B GEN_PVAR_168 y f s) = (term100 A B GEN_PVAR_168 y f s).
Proof. exact (eq_refl (term100 A B GEN_PVAR_168 y f s)). Qed.
Lemma lem4614387 {A B : Type'} (GEN_PVAR_168 : A -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term380 A B GEN_PVAR_168 s f y) = (term104 A B GEN_PVAR_168 s f y).
Proof. exact (MK_COMB (@lem4614386 A B GEN_PVAR_168 y f s) (@lem4614385 A B s f y)). Qed.
Lemma lem4614388 {A B : Type'} (GEN_PVAR_168 : A -> Prop) (s : A -> Prop) (f : A -> B) : (term381 A B GEN_PVAR_168 s f) = (term106 A B GEN_PVAR_168 s f).
Proof. exact (fun_ext (fun y : B => @lem4614387 A B GEN_PVAR_168 s f y)). Qed.
Lemma lem4614389 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4614390 {A B : Type'} (GEN_PVAR_168 : A -> Prop) (s : A -> Prop) (f : A -> B) : (term382 A B GEN_PVAR_168 s f) = (term108 A B GEN_PVAR_168 s f).
Proof. exact (MK_COMB (@lem4614389 B) (@lem4614388 A B GEN_PVAR_168 s f)). Qed.
Lemma lem4614391 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term383 A B s f) = (term110 A B s f).
Proof. exact (fun_ext (fun GEN_PVAR_168 : A -> Prop => @lem4614390 A B GEN_PVAR_168 s f)). Qed.
Lemma lem4614392 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4614393 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term378 A B s f) = (term112 A B s f).
Proof. exact (MK_COMB (@lem4614392 A) (@lem4614391 A B s f)). Qed.
Lemma lem4614394 {A : Type'} : (@eq ((A -> Prop) -> Prop)) = (@eq ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((A -> Prop) -> Prop))). Qed.
Lemma lem4614395 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term384 A B s f) = (term385 A B s f).
Proof. exact (MK_COMB (@lem4614394 A) (@lem4614393 A B s f)). Qed.
Lemma lem4614396 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term379 A B f s) = (term379 A B f s).
Proof. exact (eq_refl (term379 A B f s)). Qed.
Lemma lem4614397 {A B : Type'} (f : A -> B) (s : A -> Prop) : ((term378 A B s f) = (term379 A B f s)) = ((term112 A B s f) = (term379 A B f s)).
Proof. exact (MK_COMB (@lem4614395 A B s f) (@lem4614396 A B f s)). Qed.
Lemma lem4614398 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term112 A B s f) = (term379 A B f s).
Proof. exact (EQ_MP (@lem4614397 A B f s) (@lem4614384 A B f s)). Qed.
Lemma lem4614407 {A : Type'} : (@FINITE (A -> Prop)) = (@FINITE (A -> Prop)).
Proof. exact (eq_refl (@FINITE (A -> Prop))). Qed.
Lemma lem4614408 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term386 A B s f) = (term387 A B f s).
Proof. exact (MK_COMB (@lem4614407 A) (@lem4614398 A B f s)). Qed.
Lemma lem4614410 {A B : Type'} (f : A -> B) (s : A -> Prop) : term388 A B f s.
Proof. exact (fun h0 : @FINITE A s => @lem4614346 A B f s h0). Qed.
Lemma lem4614411 {A B : Type'} (f : type1470 A B) (s : B -> Prop) : term389 A B f s.
Proof. exact (@lem4614410 B (A -> Prop) f s). Qed.
Lemma lem4614412 {A B : Type'} (f : A -> B) (s : A -> Prop) : term390 A B f s.
Proof. exact (@lem4614411 A B (term96 A B s f) (@IMAGE A B f s)). Qed.
Lemma lem4614414 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term50 A B f s) : (term50 A B f s) = True.
Proof. exact (EQ_MP (@lem4614361 A B f s) (@lem4612939 A B f s h1)). Qed.
Lemma lem4614415 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term50 A B f s) : True = (term50 A B f s).
Proof. exact (SYM (@lem4614414 A B f s h1)). Qed.
Lemma lem4614416 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term50 A B f s) : term50 A B f s.
Proof. exact (EQ_MP (@lem4614415 A B f s h1) (@lem0)). Qed.
Lemma lem4614417 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term50 A B f s) : (term387 A B f s) = True.
Proof. exact (@lem4614412 A B f s (@lem4614416 A B f s h1)). Qed.
Lemma lem4614418 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term50 A B f s) : (term386 A B s f) = True.
Proof. exact (TRANS (@lem4614408 A B f s) (@lem4614417 A B f s h1)). Qed.
Lemma lem4614419 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4614420 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term50 A B f s) : (term391 A B s f) = (and True).
Proof. exact (MK_COMB (@lem4614419) (@lem4614418 A B f s h1)). Qed.
Lemma lem4614428 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term392 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4614429 (p : Prop) (q : Prop) (p' : Prop) : term393 p q p'.
Proof. exact (fun q' : Prop => @lem4614428 p q p' q'). Qed.
Lemma lem4614430 (p : Prop) (q : Prop) : term394 p q.
Proof. exact (fun p' : Prop => @lem4614429 p q p'). Qed.
Lemma lem4614431 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : term395 A B s f t.
Proof. exact (@lem4614430 (term396 A B t s f) (@FINITE A t)). Qed.
Lemma lem4614432 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) (p' : Prop) : term397 A B s f t p'.
Proof. exact (@lem4614431 A B s f t p'). Qed.
Lemma lem4614433 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) (p' : Prop) : (term397 A B s f t p') = (term398 A B s f t p').
Proof. exact (eq_refl (term397 A B s f t p')). Qed.
Lemma lem4614434 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) (p' : Prop) : term398 A B s f t p'.
Proof. exact (EQ_MP (@lem4614433 A B s f t p') (@lem4614432 A B s f t p')). Qed.
Lemma lem4614435 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) (p' : Prop) (q' : Prop) : term399 A B s f t p' q'.
Proof. exact (@lem4614434 A B s f t p' q'). Qed.
Lemma lem4614436 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) (p' : Prop) (q' : Prop) : (term399 A B s f t p' q') = (term400 A B s f t p' q').
Proof. exact (eq_refl (term399 A B s f t p' q')). Qed.
Lemma lem4614437 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) (p' : Prop) (q' : Prop) : term400 A B s f t p' q'.
Proof. exact (EQ_MP (@lem4614436 A B s f t p' q') (@lem4614435 A B s f t p' q')). Qed.
Lemma lem4614439 {_88128 _88132 : Type'} (f : _88128 -> _88132) (s : _88128 -> Prop) : (term371 _88128 _88132 s f) = (@IMAGE _88128 _88132 f s).
Proof. exact (EQ_MP (@lem4614356 _88128 _88132 f s) (@lem4614355 _88128 _88132 f s)). Qed.
Lemma lem4614440 {A B : Type'} (f : type1470 A B) (s : B -> Prop) : (term377 A B s f) = (@IMAGE B (A -> Prop) f s).
Proof. exact (@lem4614439 B (A -> Prop) f s). Qed.
Lemma lem4614441 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term378 A B s f) = (term379 A B f s).
Proof. exact (@lem4614440 A B (term96 A B s f) (@IMAGE A B f s)). Qed.
Lemma lem4614442 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term101 A B s f y) = (term102 A B s f y).
Proof. exact (eq_refl (term101 A B s f y)). Qed.
Lemma lem4614443 {A B : Type'} (GEN_PVAR_168 : A -> Prop) (y : B) (f : A -> B) (s : A -> Prop) : (term100 A B GEN_PVAR_168 y f s) = (term100 A B GEN_PVAR_168 y f s).
Proof. exact (eq_refl (term100 A B GEN_PVAR_168 y f s)). Qed.
Lemma lem4614444 {A B : Type'} (GEN_PVAR_168 : A -> Prop) (s : A -> Prop) (f : A -> B) (y : B) : (term380 A B GEN_PVAR_168 s f y) = (term104 A B GEN_PVAR_168 s f y).
Proof. exact (MK_COMB (@lem4614443 A B GEN_PVAR_168 y f s) (@lem4614442 A B s f y)). Qed.
Lemma lem4614445 {A B : Type'} (GEN_PVAR_168 : A -> Prop) (s : A -> Prop) (f : A -> B) : (term381 A B GEN_PVAR_168 s f) = (term106 A B GEN_PVAR_168 s f).
Proof. exact (fun_ext (fun y : B => @lem4614444 A B GEN_PVAR_168 s f y)). Qed.
Lemma lem4614446 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4614447 {A B : Type'} (GEN_PVAR_168 : A -> Prop) (s : A -> Prop) (f : A -> B) : (term382 A B GEN_PVAR_168 s f) = (term108 A B GEN_PVAR_168 s f).
Proof. exact (MK_COMB (@lem4614446 B) (@lem4614445 A B GEN_PVAR_168 s f)). Qed.
Lemma lem4614448 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term383 A B s f) = (term110 A B s f).
Proof. exact (fun_ext (fun GEN_PVAR_168 : A -> Prop => @lem4614447 A B GEN_PVAR_168 s f)). Qed.
Lemma lem4614449 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4614450 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term378 A B s f) = (term112 A B s f).
Proof. exact (MK_COMB (@lem4614449 A) (@lem4614448 A B s f)). Qed.
Lemma lem4614451 {A : Type'} : (@eq ((A -> Prop) -> Prop)) = (@eq ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((A -> Prop) -> Prop))). Qed.
Lemma lem4614452 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term384 A B s f) = (term385 A B s f).
Proof. exact (MK_COMB (@lem4614451 A) (@lem4614450 A B s f)). Qed.
Lemma lem4614453 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term379 A B f s) = (term379 A B f s).
Proof. exact (eq_refl (term379 A B f s)). Qed.
Lemma lem4614454 {A B : Type'} (f : A -> B) (s : A -> Prop) : ((term378 A B s f) = (term379 A B f s)) = ((term112 A B s f) = (term379 A B f s)).
Proof. exact (MK_COMB (@lem4614452 A B s f) (@lem4614453 A B f s)). Qed.
Lemma lem4614455 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term112 A B s f) = (term379 A B f s).
Proof. exact (EQ_MP (@lem4614454 A B f s) (@lem4614441 A B f s)). Qed.
Lemma lem4614464 {A : Type'} (t : A -> Prop) : (@IN (A -> Prop) t) = (@IN (A -> Prop) t).
Proof. exact (eq_refl (@IN (A -> Prop) t)). Qed.
Lemma lem4614465 {A B : Type'} (t : A -> Prop) (f : A -> B) (s : A -> Prop) : (term396 A B t s f) = (term401 A B t f s).
Proof. exact (MK_COMB (@lem4614464 A t) (@lem4614455 A B f s)). Qed.
Lemma lem4614474 {A B : Type'} (t : A -> Prop) (f : A -> B) (s : A -> Prop) (q' : Prop) : term402 A B t f s q'.
Proof. exact (@lem4614437 A B s f t (term401 A B t f s) q'). Qed.
Lemma lem4614475 {A B : Type'} (t : A -> Prop) (f : A -> B) (s : A -> Prop) (q' : Prop) : term403 A B t f s q'.
Proof. exact (@lem4614474 A B t f s q' (@lem4614465 A B t f s)). Qed.
Lemma lem4614479 {A : Type'} (t : A -> Prop) : (@FINITE A t) = (@FINITE A t).
Proof. exact (eq_refl (@FINITE A t)). Qed.
Lemma lem4614480 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) : term404 A B f s t.
Proof. exact (fun h0 : term401 A B t f s => @lem4614479 A t). Qed.
Lemma lem4614481 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) : term405 A B f s t.
Proof. exact (@lem4614475 A B t f s (@FINITE A t)). Qed.
Lemma lem4614482 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term406 A B s f t) = (term407 A B f s t).
Proof. exact (@lem4614481 A B f s t (@lem4614480 A B f s t)). Qed.
Lemma lem4614522 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term408 A B s f) = (term409 A B f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4614482 A B f s t)). Qed.
Lemma lem4614562 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4614563 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term410 A B s f) = (term411 A B f s).
Proof. exact (MK_COMB (@lem4614562 A) (@lem4614522 A B f s)). Qed.
Lemma lem4614565 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term362 _87967 _87968 f s P) = (term363 _87967 _87968 s P f).
Proof. exact (EQ_MP (@lem4614335 _87967 _87968 s P f) (@lem4614334 _87967 _87968 P f s)). Qed.
Lemma lem4614566 {A B : Type'} (s : B -> Prop) (P : type686 A) (f : type1470 A B) : (term412 A B f s P) = (term413 A B s P f).
Proof. exact (@lem4614565 (A -> Prop) B s P f). Qed.
Lemma lem4614567 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term411 A B f s) = (term414 A B s f).
Proof. exact (@lem4614566 A B (@IMAGE A B f s) (@FINITE A) (term96 A B s f)). Qed.
Lemma lem4614569 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term362 _87967 _87968 f s P) = (term363 _87967 _87968 s P f).
Proof. exact (EQ_MP (@lem4614335 _87967 _87968 s P f) (@lem4614334 _87967 _87968 P f s)). Qed.
Lemma lem4614570 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term415 A B f s P) = (term416 A B s P f).
Proof. exact (@lem4614569 B A s P f). Qed.
Lemma lem4614571 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term417 A B s f) = (term418 A B s f).
Proof. exact (@lem4614570 A B s (term419 A B s f) f). Qed.
Lemma lem4614572 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) : (term420 A B s f x) = (term421 A B s f x).
Proof. exact (eq_refl (term420 A B s f x)). Qed.
Lemma lem4614573 {A B : Type'} (x : B) (f : A -> B) (s : A -> Prop) : (term422 A B x f s) = (term422 A B x f s).
Proof. exact (eq_refl (term422 A B x f s)). Qed.
Lemma lem4614574 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : B) : (term423 A B s f x) = (term424 A B s f x).
Proof. exact (MK_COMB (@lem4614573 A B x f s) (@lem4614572 A B s f x)). Qed.
Lemma lem4614575 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term425 A B s f) = (term426 A B s f).
Proof. exact (fun_ext (fun x : B => @lem4614574 A B s f x)). Qed.
Lemma lem4614576 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4614577 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term417 A B s f) = (term414 A B s f).
Proof. exact (MK_COMB (@lem4614576 B) (@lem4614575 A B s f)). Qed.
Lemma lem4614578 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4614579 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term427 A B s f) = (term428 A B s f).
Proof. exact (MK_COMB (@lem4614578) (@lem4614577 A B s f)). Qed.
Lemma lem4614580 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term429 A B s f x) = (term430 A B s f x).
Proof. exact (eq_refl (term429 A B s f x)). Qed.
Lemma lem4614581 {A : Type'} (x : A) (s : A -> Prop) : (term77 A x s) = (term77 A x s).
Proof. exact (eq_refl (term77 A x s)). Qed.
Lemma lem4614582 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term431 A B s f x) = (term432 A B s f x).
Proof. exact (MK_COMB (@lem4614581 A x s) (@lem4614580 A B s f x)). Qed.
Lemma lem4614583 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term433 A B s f) = (term434 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4614582 A B s f x)). Qed.
Lemma lem4614584 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4614585 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term418 A B s f) = (term435 A B s f).
Proof. exact (MK_COMB (@lem4614584 A) (@lem4614583 A B s f)). Qed.
Lemma lem4614586 {A B : Type'} (s : A -> Prop) (f : A -> B) : ((term417 A B s f) = (term418 A B s f)) = ((term414 A B s f) = (term435 A B s f)).
Proof. exact (MK_COMB (@lem4614579 A B s f) (@lem4614585 A B s f)). Qed.
Lemma lem4614587 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term414 A B s f) = (term435 A B s f).
Proof. exact (EQ_MP (@lem4614586 A B s f) (@lem4614571 A B s f)). Qed.
Lemma lem4614595 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term392 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4614596 (p : Prop) (q : Prop) (p' : Prop) : term393 p q p'.
Proof. exact (fun q' : Prop => @lem4614595 p q p' q'). Qed.
Lemma lem4614597 (p : Prop) (q : Prop) : term394 p q.
Proof. exact (fun p' : Prop => @lem4614596 p q p'). Qed.
Lemma lem4614598 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : term436 A B s f x.
Proof. exact (@lem4614597 (@IN A x s) (term430 A B s f x)). Qed.
Lemma lem4614599 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (p' : Prop) : term437 A B s f x p'.
Proof. exact (@lem4614598 A B s f x p'). Qed.
Lemma lem4614600 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (p' : Prop) : (term437 A B s f x p') = (term438 A B s f x p').
Proof. exact (eq_refl (term437 A B s f x p')). Qed.
Lemma lem4614601 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (p' : Prop) : term438 A B s f x p'.
Proof. exact (EQ_MP (@lem4614600 A B s f x p') (@lem4614599 A B s f x p')). Qed.
Lemma lem4614602 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (p' : Prop) (q' : Prop) : term439 A B s f x p' q'.
Proof. exact (@lem4614601 A B s f x p' q'). Qed.
Lemma lem4614603 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (p' : Prop) (q' : Prop) : (term439 A B s f x p' q') = (term440 A B s f x p' q').
Proof. exact (eq_refl (term439 A B s f x p' q')). Qed.
Lemma lem4614604 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (p' : Prop) (q' : Prop) : term440 A B s f x p' q'.
Proof. exact (EQ_MP (@lem4614603 A B s f x p' q') (@lem4614602 A B s f x p' q')). Qed.
Lemma lem4614605 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@IN A x s).
Proof. exact (eq_refl (@IN A x s)). Qed.
Lemma lem4614606 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (q' : Prop) : term441 A B f x s q'.
Proof. exact (@lem4614604 A B s f x (@IN A x s) q'). Qed.
Lemma lem4614607 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (q' : Prop) : term442 A B f x s q'.
Proof. exact (@lem4614606 A B f x s q' (@lem4614605 A x s)). Qed.
Lemma lem4614608 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem4614609 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = ((@IN A x s) = True).
Proof. exact (@lem7 (@IN A x s)). Qed.
Lemma lem4614612 {A B : Type'} (f : A -> B) (y : A) : (term443 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4614613 {A B : Type'} (f : type1470 A B) (y : B) : (term444 A B f y) = (f y).
Proof. exact (@lem4614612 B (A -> Prop) f y). Qed.
Lemma lem4614614 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term445 A B s f x) = (term446 A B s f x).
Proof. exact (@lem4614613 A B (term96 A B s f) (f x)). Qed.
Lemma lem4614615 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term101 A B s f y) = (term102 A B s f y).
Proof. exact (eq_refl (term101 A B s f y)). Qed.
Lemma lem4614616 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term447 A B s f) = (term96 A B s f).
Proof. exact (fun_ext (fun y : B => @lem4614615 A B s f y)). Qed.
Lemma lem4614617 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem4614618 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term445 A B s f x) = (term446 A B s f x).
Proof. exact (MK_COMB (@lem4614616 A B s f) (@lem4614617 A B f x)). Qed.
Lemma lem4614619 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4614620 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term448 A B s f x) = (term449 A B s f x).
Proof. exact (MK_COMB (@lem4614619 A) (@lem4614618 A B s f x)). Qed.
Lemma lem4614621 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term446 A B s f x) = (term72 A B s f x).
Proof. exact (eq_refl (term446 A B s f x)). Qed.
Lemma lem4614622 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : ((term445 A B s f x) = (term446 A B s f x)) = ((term446 A B s f x) = (term72 A B s f x)).
Proof. exact (MK_COMB (@lem4614620 A B s f x) (@lem4614621 A B s f x)). Qed.
Lemma lem4614623 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term446 A B s f x) = (term72 A B s f x).
Proof. exact (EQ_MP (@lem4614622 A B s f x) (@lem4614614 A B s f x)). Qed.
Lemma lem4614632 {A : Type'} : (@FINITE A) = (@FINITE A).
Proof. exact (eq_refl (@FINITE A)). Qed.
Lemma lem4614633 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term430 A B s f x) = (term76 A B s f x).
Proof. exact (MK_COMB (@lem4614632 A) (@lem4614623 A B s f x)). Qed.
Lemma lem4614635 {A B : Type'} (a : A) (s : A -> Prop) (f : A -> B) (h1 : term80 A B s f) : term450 A B s f a.
Proof. exact (fun h0 : @IN A a s => @lem4614369 A B f a s h1 h0). Qed.
Lemma lem4614636 {A B : Type'} (a : A) (s : A -> Prop) (f : A -> B) (h1 : term80 A B s f) : term450 A B s f a.
Proof. exact (@lem4614635 A B a s f h1). Qed.
Lemma lem4614637 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (h1 : term80 A B s f) : term450 A B s f x.
Proof. exact (@lem4614636 A B x s f h1). Qed.
Lemma lem4614639 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : (@IN A x s) = True.
Proof. exact (EQ_MP (@lem4614609 A x s) (@lem4614608 A x s h1)). Qed.
Lemma lem4614640 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : True = (@IN A x s).
Proof. exact (SYM (@lem4614639 A x s h1)). Qed.
Lemma lem4614641 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (EQ_MP (@lem4614640 A x s h1) (@lem0)). Qed.
Lemma lem4614642 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term80 A B s f) (h2 : @IN A x s) : (term76 A B s f x) = True.
Proof. exact (@lem4614637 A B x s f h1 (@lem4614641 A x s h2)). Qed.
Lemma lem4614643 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term80 A B s f) (h2 : @IN A x s) : (term430 A B s f x) = True.
Proof. exact (TRANS (@lem4614633 A B s f x) (@lem4614642 A B f x s h1 h2)). Qed.
Lemma lem4614644 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (h1 : term80 A B s f) : term451 A B s f x.
Proof. exact (fun h0 : @IN A x s => @lem4614643 A B f x s h1 h0). Qed.
Lemma lem4614645 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : term452 A B f x s.
Proof. exact (@lem4614607 A B f x s True). Qed.
Lemma lem4614646 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (h1 : term80 A B s f) : (term432 A B s f x) = (term453 A x s).
Proof. exact (@lem4614645 A B f x s (@lem4614644 A B x s f h1)). Qed.
Lemma lem4614648 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4614649 {A : Type'} (x : A) (s : A -> Prop) : (term453 A x s) = True.
Proof. exact (@lem4614648 (@IN A x s)). Qed.
Lemma lem4614650 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (h1 : term80 A B s f) : (term432 A B s f x) = True.
Proof. exact (TRANS (@lem4614646 A B x s f h1) (@lem4614649 A x s)). Qed.
Lemma lem4614651 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term80 A B s f) : (term434 A B s f) = (term454 A).
Proof. exact (fun_ext (fun x : A => @lem4614650 A B x s f h1)). Qed.
Lemma lem4614652 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4614653 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term80 A B s f) : (term435 A B s f) = (term455 A).
Proof. exact (MK_COMB (@lem4614652 A) (@lem4614651 A B s f h1)). Qed.
Lemma lem4614655 {A : Type'} (t : Prop) : (term456 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4614656 {A : Type'} (t : Prop) : (term456 A t) = t.
Proof. exact (@lem4614655 A t). Qed.
Lemma lem4614657 {A : Type'} : (term455 A) = True.
Proof. exact (@lem4614656 A True). Qed.
Lemma lem4614658 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term80 A B s f) : (term435 A B s f) = True.
Proof. exact (TRANS (@lem4614653 A B s f h1) (@lem4614657 A)). Qed.
Lemma lem4614659 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term80 A B s f) : (term414 A B s f) = True.
Proof. exact (TRANS (@lem4614587 A B s f) (@lem4614658 A B s f h1)). Qed.
Lemma lem4614660 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term80 A B s f) : (term411 A B f s) = True.
Proof. exact (TRANS (@lem4614567 A B s f) (@lem4614659 A B s f h1)). Qed.
Lemma lem4614661 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term80 A B s f) : (term410 A B s f) = True.
Proof. exact (TRANS (@lem4614563 A B f s) (@lem4614660 A B s f h1)). Qed.
Lemma lem4614662 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term80 A B s f) (h2 : term50 A B f s) : (term376 A B s f) = (True /\ True).
Proof. exact (MK_COMB (@lem4614420 A B f s h2) (@lem4614661 A B s f h1)). Qed.
Lemma lem4614664 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4614665 : (True /\ True) = True.
Proof. exact (@lem4614664 True). Qed.
Lemma lem4614666 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term80 A B s f) (h2 : term50 A B f s) : (term376 A B s f) = True.
Proof. exact (TRANS (@lem4614662 A B f s h1 h2) (@lem4614665)). Qed.
Lemma lem4614667 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term80 A B s f) (h2 : term50 A B f s) : (term90 A B s f) = True.
Proof. exact (TRANS (@lem4614378 A B s f) (@lem4614666 A B f s h1 h2)). Qed.
Lemma lem4614668 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term80 A B s f) (h2 : term50 A B f s) : True = (term90 A B s f).
Proof. exact (SYM (@lem4614667 A B f s h1 h2)). Qed.
Lemma lem4614669 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term80 A B s f) (h2 : term50 A B f s) : term90 A B s f.
Proof. exact (EQ_MP (@lem4614668 A B f s h1 h2) (@lem0)). Qed.
Lemma lem4614670 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term80 A B s f) (h2 : term50 A B f s) (h3 : s = (term86 A B s f)) : @FINITE A s.
Proof. exact (EQ_MP (@lem4613043 A B s f h3) (@lem4614669 A B f s h1 h2)). Qed.
Lemma lem4614671 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term80 A B s f) (h2 : term50 A B f s) : (s = (term86 A B s f)) = (@FINITE A s).
Proof. exact (prop_ext (fun h3 : s = (term86 A B s f) => @lem4614670 A B s f h1 h2 h3) (fun h3 : @FINITE A s => @lem4614330 A B s f)). Qed.
Lemma lem4614672 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term80 A B s f) (h2 : term50 A B f s) : @FINITE A s.
Proof. exact (EQ_MP (@lem4614671 A B f s h1 h2) (@lem4614330 A B s f)). Qed.
Lemma lem4614673 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term50 A B f s) : term85 A B f s.
Proof. exact (fun h0 : term80 A B s f => @lem4614672 A B f s h0 h1). Qed.
Lemma lem4614674 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term50 A B f s) : term53 A B f s.
Proof. exact (EQ_MP (@lem4613028 A B f s) (@lem4614673 A B f s h1)). Qed.
Lemma lem4614675 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term50 A B f s) : term52 A B s f.
Proof. exact (EQ_MP (@lem4612943 A B s f) (@lem4614674 A B f s h1)). Qed.
Lemma lem4614676 {A B : Type'} (s : A -> Prop) (f : A -> B) : term49 A B s f.
Proof. exact (fun h0 : term50 A B f s => @lem4614675 A B f s h0). Qed.
Lemma lem4614677 {A B : Type'} (s : A -> Prop) (f : A -> B) : term48 A B s f.
Proof. exact (EQ_MP (@lem4612938 A B s f) (@lem4614676 A B s f)). Qed.
Lemma lem4614682 {A B : Type'} (f : A -> B) : term457 A B f.
Proof. exact (fun s : A -> Prop => @lem4614677 A B s f). Qed.
Lemma lem4614687 {A B : Type'} : term458 A B.
Proof. exact (fun f : A -> B => @lem4614682 A B f). Qed.
