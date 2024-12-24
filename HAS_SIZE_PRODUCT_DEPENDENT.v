Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HAS_SIZE_PRODUCT_DEPENDENT_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import CARD_CLAUSES_spec.
Require Import DISJOINT_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import EXISTS_REFL_spec.
Require Import EXTENSION_spec.
Require Import FINITE_INDUCT_STRONG_spec.
Require Import FORALL_AND_THM_spec.
Require Import HAS_SIZE_spec.
Require Import HAS_SIZE_0_spec.
Require Import HAS_SIZE_IMAGE_INJ_spec.
Require Import HAS_SIZE_UNION_spec.
Require Import IN_IMAGE_spec.
Require Import IN_INSERT_spec.
Require Import IN_INTER_spec.
Require Import LEFT_FORALL_IMP_THM_spec.
Require Import MULT_CLAUSES_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import PAIR_EQ_spec.
Require Import RIGHT_FORALL_IMP_THM_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm1804_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1812_spec.
Require Import thm1813_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
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
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
Require Import thm19792_spec.
Require Import thm20230_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm3184747_spec.
Require Import thm3184750_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211647_spec.
Require Import thm3211648_spec.
Require Import thm3211656_spec.
Require Import thm3211657_spec.
Require Import thm3211719_spec.
Require Import thm3211720_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm4211_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm885_spec.
Require Import thm886_spec.
Lemma lem4292791 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem4292792 {A : Type'} (x : A) : (term0 A x) = (term1 A x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem4292793 {A : Type'} (x : A) : term1 A x.
Proof. exact (EQ_MP (@lem4292792 A x) (@lem4292791 A x)). Qed.
Lemma lem4292794 {A : Type'} (x : A) : term2 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem4292796 {A : Type'} (s : A -> Prop) : term3 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem4292797 {A : Type'} (s : A -> Prop) : (term3 A s) = (term4 A s).
Proof. exact (eq_refl (term3 A s)). Qed.
Lemma lem4292798 {A : Type'} (s : A -> Prop) : term4 A s.
Proof. exact (EQ_MP (@lem4292797 A s) (@lem4292796 A s)). Qed.
Lemma lem4292799 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term5 A s t.
Proof. exact (@lem4292798 A s t). Qed.
Lemma lem4292800 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term5 A s t) = ((s = t) = (term6 A s t)).
Proof. exact (eq_refl (term5 A s t)). Qed.
Lemma lem4292802 {A : Type'} (s : A -> Prop) : term7 A s.
Proof. exact (@lem3205222 A s). Qed.
Lemma lem4292803 {A : Type'} (s : A -> Prop) : (term7 A s) = (term8 A s).
Proof. exact (eq_refl (term7 A s)). Qed.
Lemma lem4292804 {A : Type'} (s : A -> Prop) : term8 A s.
Proof. exact (EQ_MP (@lem4292803 A s) (@lem4292802 A s)). Qed.
Lemma lem4292805 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term9 A s t.
Proof. exact (@lem4292804 A s t). Qed.
Lemma lem4292806 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term9 A s t) = (term10 A s t).
Proof. exact (eq_refl (term9 A s t)). Qed.
Lemma lem4292807 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term10 A s t.
Proof. exact (EQ_MP (@lem4292806 A s t) (@lem4292805 A s t)). Qed.
Lemma lem4292808 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term11 A s t x.
Proof. exact (@lem4292807 A s t x). Qed.
Lemma lem4292809 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term11 A s t x) = ((term12 A x s t) = (term13 A s x t)).
Proof. exact (eq_refl (term11 A s t x)). Qed.
Lemma lem4292842 {_83064 : Type'} : term14 _83064.
Proof. exact (EQ_MP (@lem3184750 _83064) (@lem3184747 _83064)). Qed.
Lemma lem4292843 {_83064 : Type'} (P : type919 _83064) : term15 _83064 P.
Proof. exact (@lem4292842 _83064 P). Qed.
Lemma lem4292844 {_83064 : Type'} (P : type919 _83064) : (term15 _83064 P) = (term16 _83064 P).
Proof. exact (eq_refl (term15 _83064 P)). Qed.
Lemma lem4292845 {_83064 : Type'} (P : type919 _83064) : term16 _83064 P.
Proof. exact (EQ_MP (@lem4292844 _83064 P) (@lem4292843 _83064 P)). Qed.
Lemma lem4292846 {_83064 : Type'} (P : type919 _83064) (x : _83064) : term17 _83064 P x.
Proof. exact (@lem4292845 _83064 P x). Qed.
Lemma lem4292847 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term17 _83064 P x) = ((term18 _83064 x P) = (term19 _83064 P x)).
Proof. exact (eq_refl (term17 _83064 P x)). Qed.
Lemma lem4292849 {A B : Type'} (y : B) : term20 A B y.
Proof. exact (@lem3206070 A B y). Qed.
Lemma lem4292850 {A B : Type'} (y : B) : (term20 A B y) = (term21 A B y).
Proof. exact (eq_refl (term20 A B y)). Qed.
Lemma lem4292851 {A B : Type'} (y : B) : term21 A B y.
Proof. exact (EQ_MP (@lem4292850 A B y) (@lem4292849 A B y)). Qed.
Lemma lem4292852 {A B : Type'} (y : B) (s : A -> Prop) : term22 A B y s.
Proof. exact (@lem4292851 A B y s). Qed.
Lemma lem4292853 {A B : Type'} (y : B) (s : A -> Prop) : (term22 A B y s) = (term23 A B y s).
Proof. exact (eq_refl (term22 A B y s)). Qed.
Lemma lem4292854 {A B : Type'} (y : B) (s : A -> Prop) : term23 A B y s.
Proof. exact (EQ_MP (@lem4292853 A B y s) (@lem4292852 A B y s)). Qed.
Lemma lem4292855 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : term24 A B y s f.
Proof. exact (@lem4292854 A B y s f). Qed.
Lemma lem4292856 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term24 A B y s f) = ((term25 A B y f s) = (term26 A B y f s)).
Proof. exact (eq_refl (term24 A B y s f)). Qed.
Lemma lem4292858 {A : Type'} (s : A -> Prop) : term27 A s.
Proof. exact (@lem3196110 A s). Qed.
Lemma lem4292859 {A : Type'} (s : A -> Prop) : (term27 A s) = (term28 A s).
Proof. exact (eq_refl (term27 A s)). Qed.
Lemma lem4292860 {A : Type'} (s : A -> Prop) : term28 A s.
Proof. exact (EQ_MP (@lem4292859 A s) (@lem4292858 A s)). Qed.
Lemma lem4292861 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term29 A s t.
Proof. exact (@lem4292860 A s t). Qed.
Lemma lem4292862 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term29 A s t) = ((@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A))).
Proof. exact (eq_refl (term29 A s t)). Qed.
Lemma lem4292864 {_100197 : Type'} (h1 : term30 _100197) : term30 _100197.
Proof. exact (h1). Qed.
Lemma lem4292865 {_100197 : Type'} (s : _100197 -> Prop) (h1 : term30 _100197) : term31 _100197 s.
Proof. exact (@lem4292864 _100197 h1 s). Qed.
Lemma lem4292866 {_100197 : Type'} (s : _100197 -> Prop) : (term31 _100197 s) = (term32 _100197 s).
Proof. exact (eq_refl (term31 _100197 s)). Qed.
Lemma lem4292867 {_100197 : Type'} (s : _100197 -> Prop) (h1 : term30 _100197) : term32 _100197 s.
Proof. exact (EQ_MP (@lem4292866 _100197 s) (@lem4292865 _100197 s h1)). Qed.
Lemma lem4292868 {_100197 : Type'} (s : _100197 -> Prop) (t : _100197 -> Prop) (h1 : term30 _100197) : term33 _100197 s t.
Proof. exact (@lem4292867 _100197 s h1 t). Qed.
Lemma lem4292869 {_100197 : Type'} (s : _100197 -> Prop) (t : _100197 -> Prop) : (term33 _100197 s t) = (term34 _100197 s t).
Proof. exact (eq_refl (term33 _100197 s t)). Qed.
Lemma lem4292870 {_100197 : Type'} (s : _100197 -> Prop) (t : _100197 -> Prop) (h1 : term30 _100197) : term34 _100197 s t.
Proof. exact (EQ_MP (@lem4292869 _100197 s t) (@lem4292868 _100197 s t h1)). Qed.
Lemma lem4292871 {_100197 : Type'} (s : _100197 -> Prop) (t : _100197 -> Prop) (m : nat) (h1 : term30 _100197) : term35 _100197 s t m.
Proof. exact (@lem4292870 _100197 s t h1 m). Qed.
Lemma lem4292872 {_100197 : Type'} (s : _100197 -> Prop) (t : _100197 -> Prop) (m : nat) : (term35 _100197 s t m) = (term36 _100197 s t m).
Proof. exact (eq_refl (term35 _100197 s t m)). Qed.
Lemma lem4292873 {_100197 : Type'} (s : _100197 -> Prop) (t : _100197 -> Prop) (m : nat) (h1 : term30 _100197) : term36 _100197 s t m.
Proof. exact (EQ_MP (@lem4292872 _100197 s t m) (@lem4292871 _100197 s t m h1)). Qed.
Lemma lem4292874 {_100197 : Type'} (s : _100197 -> Prop) (t : _100197 -> Prop) (m : nat) (n : nat) (h1 : term30 _100197) : term37 _100197 s t m n.
Proof. exact (@lem4292873 _100197 s t m h1 n). Qed.
Lemma lem4292875 {_100197 : Type'} (s : _100197 -> Prop) (t : _100197 -> Prop) (m : nat) (n : nat) : (term37 _100197 s t m n) = (term38 _100197 s t m n).
Proof. exact (eq_refl (term37 _100197 s t m n)). Qed.
Lemma lem4292876 {_100197 : Type'} (s : _100197 -> Prop) (t : _100197 -> Prop) (m : nat) (n : nat) (h1 : term30 _100197) : term38 _100197 s t m n.
Proof. exact (EQ_MP (@lem4292875 _100197 s t m n) (@lem4292874 _100197 s t m n h1)). Qed.
Lemma lem4292877 {_100197 : Type'} (m : nat) (n : nat) (s : _100197 -> Prop) (t : _100197 -> Prop) (h1 : term39 _100197 m n s t) : term39 _100197 m n s t.
Proof. exact (h1). Qed.
Lemma lem4292878 {_100197 : Type'} (m : nat) (n : nat) (s : _100197 -> Prop) (t : _100197 -> Prop) (h1 : term30 _100197) (h2 : term39 _100197 m n s t) : term40 _100197 s t m n.
Proof. exact (@lem4292876 _100197 s t m n h1 (@lem4292877 _100197 m n s t h2)). Qed.
Lemma lem4292879 {_100197 : Type'} (m : nat) (n : nat) (s : _100197 -> Prop) (t : _100197 -> Prop) (h1 : term39 _100197 m n s t) : term41 _100197 s t m n.
Proof. exact (fun h0 : term30 _100197 => @lem4292878 _100197 m n s t h0 h1). Qed.
Lemma lem4292880 {_100197 : Type'} (h1 : term30 _100197) : term30 _100197.
Proof. exact (h1). Qed.
Lemma lem4292881 {_100197 : Type'} (m : nat) (n : nat) (s : _100197 -> Prop) (t : _100197 -> Prop) (h1 : term30 _100197) (h2 : term39 _100197 m n s t) : term40 _100197 s t m n.
Proof. exact (@lem4292879 _100197 m n s t h2 (@lem4292880 _100197 h1)). Qed.
Lemma lem4292882 {_100197 : Type'} (s : _100197 -> Prop) (t : _100197 -> Prop) (m : nat) (n : nat) (h1 : term30 _100197) : term38 _100197 s t m n.
Proof. exact (fun h0 : term39 _100197 m n s t => @lem4292881 _100197 m n s t h1 h0). Qed.
Lemma lem4292883 {_100197 : Type'} (s : _100197 -> Prop) (t : _100197 -> Prop) (m : nat) (h1 : term30 _100197) : term36 _100197 s t m.
Proof. exact (fun n : nat => @lem4292882 _100197 s t m n h1). Qed.
Lemma lem4292884 {_100197 : Type'} (s : _100197 -> Prop) (t : _100197 -> Prop) (h1 : term30 _100197) : term34 _100197 s t.
Proof. exact (fun m : nat => @lem4292883 _100197 s t m h1). Qed.
Lemma lem4292885 {_100197 : Type'} (s : _100197 -> Prop) (h1 : term30 _100197) : term32 _100197 s.
Proof. exact (fun t : _100197 -> Prop => @lem4292884 _100197 s t h1). Qed.
Lemma lem4292886 {_100197 : Type'} (h1 : term30 _100197) : term30 _100197.
Proof. exact (fun s : _100197 -> Prop => @lem4292885 _100197 s h1). Qed.
Lemma lem4292887 {_100197 : Type'} : term42 _100197.
Proof. exact (fun h0 : term30 _100197 => @lem4292886 _100197 h0). Qed.
Lemma lem4292888 {_100197 : Type'} : term30 _100197.
Proof. exact (@lem4292887 _100197 (@lem3868180 _100197)). Qed.
Lemma lem4292889 {_100197 : Type'} (s : _100197 -> Prop) : term31 _100197 s.
Proof. exact (@lem4292888 _100197 s). Qed.
Lemma lem4292890 {_100197 : Type'} (s : _100197 -> Prop) : (term31 _100197 s) = (term32 _100197 s).
Proof. exact (eq_refl (term31 _100197 s)). Qed.
Lemma lem4292891 {_100197 : Type'} (s : _100197 -> Prop) : term32 _100197 s.
Proof. exact (EQ_MP (@lem4292890 _100197 s) (@lem4292889 _100197 s)). Qed.
Lemma lem4292892 {_100197 : Type'} (s : _100197 -> Prop) (t : _100197 -> Prop) : term33 _100197 s t.
Proof. exact (@lem4292891 _100197 s t). Qed.
Lemma lem4292893 {_100197 : Type'} (s : _100197 -> Prop) (t : _100197 -> Prop) : (term33 _100197 s t) = (term34 _100197 s t).
Proof. exact (eq_refl (term33 _100197 s t)). Qed.
Lemma lem4292894 {_100197 : Type'} (s : _100197 -> Prop) (t : _100197 -> Prop) : term34 _100197 s t.
Proof. exact (EQ_MP (@lem4292893 _100197 s t) (@lem4292892 _100197 s t)). Qed.
Lemma lem4292895 {_100197 : Type'} (s : _100197 -> Prop) (t : _100197 -> Prop) (m : nat) : term35 _100197 s t m.
Proof. exact (@lem4292894 _100197 s t m). Qed.
Lemma lem4292896 {_100197 : Type'} (s : _100197 -> Prop) (t : _100197 -> Prop) (m : nat) : (term35 _100197 s t m) = (term36 _100197 s t m).
Proof. exact (eq_refl (term35 _100197 s t m)). Qed.
Lemma lem4292897 {_100197 : Type'} (s : _100197 -> Prop) (t : _100197 -> Prop) (m : nat) : term36 _100197 s t m.
Proof. exact (EQ_MP (@lem4292896 _100197 s t m) (@lem4292895 _100197 s t m)). Qed.
Lemma lem4292898 {_100197 : Type'} (s : _100197 -> Prop) (t : _100197 -> Prop) (m : nat) (n : nat) : term37 _100197 s t m n.
Proof. exact (@lem4292897 _100197 s t m n). Qed.
Lemma lem4292899 {_100197 : Type'} (s : _100197 -> Prop) (t : _100197 -> Prop) (m : nat) (n : nat) : (term37 _100197 s t m n) = (term38 _100197 s t m n).
Proof. exact (eq_refl (term37 _100197 s t m n)). Qed.
Lemma lem4292901 (t1 : Prop) : term43 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4292902 (t1 : Prop) : (term43 t1) = (term44 t1).
Proof. exact (eq_refl (term43 t1)). Qed.
Lemma lem4292903 (t1 : Prop) : term44 t1.
Proof. exact (EQ_MP (@lem4292902 t1) (@lem4292901 t1)). Qed.
Lemma lem4292904 (t1 : Prop) (t2 : Prop) : term45 t1 t2.
Proof. exact (@lem4292903 t1 t2). Qed.
Lemma lem4292905 (t1 : Prop) (t2 : Prop) : (term45 t1 t2) = (term46 t1 t2).
Proof. exact (eq_refl (term45 t1 t2)). Qed.
Lemma lem4292906 (t1 : Prop) (t2 : Prop) : term46 t1 t2.
Proof. exact (EQ_MP (@lem4292905 t1 t2) (@lem4292904 t1 t2)). Qed.
Lemma lem4292907 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term47 t1 t2 t3.
Proof. exact (@lem4292906 t1 t2 t3). Qed.
Lemma lem4292908 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term47 t1 t2 t3) = ((term48 t1 t2 t3) = (term49 t1 t2 t3)).
Proof. exact (eq_refl (term47 t1 t2 t3)). Qed.
Lemma lem4292909 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term48 t1 t2 t3) = (term49 t1 t2 t3).
Proof. exact (EQ_MP (@lem4292908 t1 t2 t3) (@lem4292907 t1 t2 t3)). Qed.
Lemma lem4292910 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term49 t1 t2 t3) = (term48 t1 t2 t3).
Proof. exact (SYM (@lem4292909 t1 t2 t3)). Qed.
Lemma lem4292914 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term6 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4292915 {_103141 _103145 : Type'} (s : type1223 _103141 _103145) (t : type1223 _103141 _103145) : (s = t) = (term50 _103141 _103145 s t).
Proof. exact (@lem4292914 (prod _103145 _103141) s t). Qed.
Lemma lem4292916 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (a : _103145) : ((term51 _103141 _103145 a s t) = (term52 _103141 _103145 s t a)) = (term53 _103141 _103145 s t a).
Proof. exact (@lem4292915 _103141 _103145 (term51 _103141 _103145 a s t) (term52 _103141 _103145 s t a)). Qed.
Lemma lem4292951 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (a : _103145) : (term53 _103141 _103145 s t a) = ((term51 _103141 _103145 a s t) = (term52 _103141 _103145 s t a)).
Proof. exact (SYM (@lem4292916 _103141 _103145 s t a)). Qed.
Lemma lem4292959 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term18 _83064 x P) = (term19 _83064 P x).
Proof. exact (EQ_MP (@lem3211648 _83064 P x) (@lem3211647 _83064 P x)). Qed.
Lemma lem4292960 {_103141 _103145 : Type'} (P : type916 _103141 _103145) (x : prod _103145 _103141) : (term54 _103141 _103145 x P) = (term55 _103141 _103145 P x).
Proof. exact (@lem4292959 (prod _103145 _103141) P x). Qed.
Lemma lem4292961 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term56 _103141 _103145 x a s t) = (term57 _103141 _103145 a s t x).
Proof. exact (@lem4292960 _103141 _103145 (term58 _103141 _103145 a s t) x). Qed.
Lemma lem4292962 {_103141 _103145 : Type'} (GEN_PVAR_119 : prod _103145 _103141) (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) : (term59 _103141 _103145 a s t GEN_PVAR_119) = (term60 _103141 _103145 GEN_PVAR_119 a s t).
Proof. exact (eq_refl (term59 _103141 _103145 a s t GEN_PVAR_119)). Qed.
Lemma lem4292963 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) : (term61 _103141 _103145 a s t) = (term62 _103141 _103145 a s t).
Proof. exact (fun_ext (fun GEN_PVAR_119 : prod _103145 _103141 => @lem4292962 _103141 _103145 GEN_PVAR_119 a s t)). Qed.
Lemma lem4292964 {_103141 _103145 : Type'} : (@GSPEC (prod _103145 _103141)) = (@GSPEC (prod _103145 _103141)).
Proof. exact (eq_refl (@GSPEC (prod _103145 _103141))). Qed.
Lemma lem4292965 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) : (term63 _103141 _103145 a s t) = (term51 _103141 _103145 a s t).
Proof. exact (MK_COMB (@lem4292964 _103141 _103145) (@lem4292963 _103141 _103145 a s t)). Qed.
Lemma lem4292966 {_103141 _103145 : Type'} (x : prod _103145 _103141) : (@IN (prod _103145 _103141) x) = (@IN (prod _103145 _103141) x).
Proof. exact (eq_refl (@IN (prod _103145 _103141) x)). Qed.
Lemma lem4292967 {_103141 _103145 : Type'} (x : prod _103145 _103141) (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) : (term56 _103141 _103145 x a s t) = (term64 _103141 _103145 x a s t).
Proof. exact (MK_COMB (@lem4292966 _103141 _103145 x) (@lem4292965 _103141 _103145 a s t)). Qed.
Lemma lem4292968 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4292969 {_103141 _103145 : Type'} (x : prod _103145 _103141) (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) : (term65 _103141 _103145 x a s t) = (term66 _103141 _103145 x a s t).
Proof. exact (MK_COMB (@lem4292968) (@lem4292967 _103141 _103145 x a s t)). Qed.
Lemma lem4292970 {_103141 _103145 : Type'} (x : prod _103145 _103141) (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) : (term57 _103141 _103145 a s t x) = (term67 _103141 _103145 x a s t).
Proof. exact (eq_refl (term57 _103141 _103145 a s t x)). Qed.
Lemma lem4292971 {_103141 _103145 : Type'} (x : prod _103145 _103141) (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) : ((term56 _103141 _103145 x a s t) = (term57 _103141 _103145 a s t x)) = ((term64 _103141 _103145 x a s t) = (term67 _103141 _103145 x a s t)).
Proof. exact (MK_COMB (@lem4292969 _103141 _103145 x a s t) (@lem4292970 _103141 _103145 x a s t)). Qed.
Lemma lem4292972 {_103141 _103145 : Type'} (x : prod _103145 _103141) (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) : (term64 _103141 _103145 x a s t) = (term67 _103141 _103145 x a s t).
Proof. exact (EQ_MP (@lem4292971 _103141 _103145 x a s t) (@lem4292961 _103141 _103145 a s t x)). Qed.
Lemma lem4292982 {A B : Type'} (f : A -> B) (y : A) : (term68 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4292983 {_103141 _103145 : Type'} (f : type1534 _103141 _103145) (y : Prop) : (term69 _103141 _103145 f y) = (f y).
Proof. exact (@lem4292982 Prop (type1223 _103141 _103145) f y). Qed.
Lemma lem4292984 {_103141 _103145 : Type'} (x : prod _103145 _103141) (a : _103145) (s : _103145 -> Prop) (y : _103141) (t : type1470 _103141 _103145) (x' : _103145) : (term70 _103141 _103145 x a s y t x') = (term71 _103141 _103145 x a s y t x').
Proof. exact (@lem4292983 _103141 _103145 (term72 _103141 _103145 x) (term73 _103141 _103145 a s y t x')). Qed.
Lemma lem4292985 {_103141 _103145 : Type'} (p : Prop) (x : prod _103145 _103141) : (term74 _103141 _103145 x p) = (term75 _103141 _103145 p x).
Proof. exact (eq_refl (term74 _103141 _103145 x p)). Qed.
Lemma lem4292986 {_103141 _103145 : Type'} (x : prod _103145 _103141) : (term76 _103141 _103145 x) = (term72 _103141 _103145 x).
Proof. exact (fun_ext (fun p : Prop => @lem4292985 _103141 _103145 p x)). Qed.
Lemma lem4292987 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (y : _103141) (t : type1470 _103141 _103145) (x : _103145) : (term73 _103141 _103145 a s y t x) = (term73 _103141 _103145 a s y t x).
Proof. exact (eq_refl (term73 _103141 _103145 a s y t x)). Qed.
Lemma lem4292988 {_103141 _103145 : Type'} (x : prod _103145 _103141) (a : _103145) (s : _103145 -> Prop) (y : _103141) (t : type1470 _103141 _103145) (x' : _103145) : (term70 _103141 _103145 x a s y t x') = (term71 _103141 _103145 x a s y t x').
Proof. exact (MK_COMB (@lem4292986 _103141 _103145 x) (@lem4292987 _103141 _103145 a s y t x')). Qed.
Lemma lem4292989 {_103141 _103145 : Type'} : (@eq ((prod _103145 _103141) -> Prop)) = (@eq ((prod _103145 _103141) -> Prop)).
Proof. exact (eq_refl (@eq ((prod _103145 _103141) -> Prop))). Qed.
Lemma lem4292990 {_103141 _103145 : Type'} (x : prod _103145 _103141) (a : _103145) (s : _103145 -> Prop) (y : _103141) (t : type1470 _103141 _103145) (x' : _103145) : (term77 _103141 _103145 x a s y t x') = (term78 _103141 _103145 x a s y t x').
Proof. exact (MK_COMB (@lem4292989 _103141 _103145) (@lem4292988 _103141 _103145 x a s y t x')). Qed.
Lemma lem4292991 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (y : _103141) (t : type1470 _103141 _103145) (x : _103145) (x' : prod _103145 _103141) : (term71 _103141 _103145 x' a s y t x) = (term79 _103141 _103145 a s y t x x').
Proof. exact (eq_refl (term71 _103141 _103145 x' a s y t x)). Qed.
Lemma lem4292992 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (y : _103141) (t : type1470 _103141 _103145) (x : _103145) (x' : prod _103145 _103141) : ((term70 _103141 _103145 x' a s y t x) = (term71 _103141 _103145 x' a s y t x)) = ((term71 _103141 _103145 x' a s y t x) = (term79 _103141 _103145 a s y t x x')).
Proof. exact (MK_COMB (@lem4292990 _103141 _103145 x' a s y t x) (@lem4292991 _103141 _103145 a s y t x x')). Qed.
Lemma lem4292993 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (y : _103141) (t : type1470 _103141 _103145) (x : _103145) (x' : prod _103145 _103141) : (term71 _103141 _103145 x' a s y t x) = (term79 _103141 _103145 a s y t x x').
Proof. exact (EQ_MP (@lem4292992 _103141 _103145 a s y t x x') (@lem4292984 _103141 _103145 x' a s y t x)). Qed.
Lemma lem4293003 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4293004 {_103145 : Type'} (P : _103145 -> Prop) (x : _103145) : (@IN _103145 x P) = (P x).
Proof. exact (@lem4293003 _103145 P x). Qed.
Lemma lem4293005 {_103145 : Type'} (s : _103145 -> Prop) (x : _103145) : (@IN _103145 x s) = (s x).
Proof. exact (@lem4293004 _103145 s x). Qed.
Lemma lem4293006 {_103145 : Type'} (x : _103145) (a : _103145) : (term80 _103145 x a) = (term80 _103145 x a).
Proof. exact (eq_refl (term80 _103145 x a)). Qed.
Lemma lem4293007 {_103145 : Type'} (a : _103145) (s : _103145 -> Prop) (x : _103145) : (term81 _103145 a x s) = (term82 _103145 a s x).
Proof. exact (MK_COMB (@lem4293006 _103145 x a) (@lem4293005 _103145 s x)). Qed.
Lemma lem4293010 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4293011 {_103145 : Type'} (a : _103145) (s : _103145 -> Prop) (x : _103145) : (term83 _103145 a x s) = (term84 _103145 a s x).
Proof. exact (MK_COMB (@lem4293010) (@lem4293007 _103145 a s x)). Qed.
Lemma lem4293013 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4293014 {_103141 : Type'} (P : _103141 -> Prop) (x : _103141) : (@IN _103141 x P) = (P x).
Proof. exact (@lem4293013 _103141 P x). Qed.
Lemma lem4293015 {_103141 _103145 : Type'} (t : type1470 _103141 _103145) (x : _103145) (y : _103141) : (term85 _103141 _103145 y t x) = (t x y).
Proof. exact (@lem4293014 _103141 (t x) y). Qed.
Lemma lem4293016 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : _103145) (y : _103141) : (term73 _103141 _103145 a s y t x) = (term86 _103141 _103145 a s t x y).
Proof. exact (MK_COMB (@lem4293011 _103145 a s x) (@lem4293015 _103141 _103145 t x y)). Qed.
Lemma lem4293019 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4293020 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : _103145) (y : _103141) : (term87 _103141 _103145 a s y t x) = (term88 _103141 _103145 a s t x y).
Proof. exact (MK_COMB (@lem4293019) (@lem4293016 _103141 _103145 a s t x y)). Qed.
Lemma lem4293023 {_103141 _103145 : Type'} (x : prod _103145 _103141) (t : prod _103145 _103141) : (x = t) = (x = t).
Proof. exact (eq_refl (x = t)). Qed.
Lemma lem4293024 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : _103145) (y : _103141) (x' : prod _103145 _103141) (t' : prod _103145 _103141) : (term89 _103141 _103145 a s y t x x' t') = (term90 _103141 _103145 a s t x y x' t').
Proof. exact (MK_COMB (@lem4293020 _103141 _103145 a s t x y) (@lem4293023 _103141 _103145 x' t')). Qed.
Lemma lem4293027 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : _103145) (y : _103141) (x' : prod _103145 _103141) : (term79 _103141 _103145 a s y t x x') = (term91 _103141 _103145 a s t x y x').
Proof. exact (fun_ext (fun t' : prod _103145 _103141 => @lem4293024 _103141 _103145 a s t x y x' t')). Qed.
Lemma lem4293028 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : _103145) (y : _103141) (x' : prod _103145 _103141) : (term71 _103141 _103145 x' a s y t x) = (term91 _103141 _103145 a s t x y x').
Proof. exact (TRANS (@lem4292993 _103141 _103145 a s y t x x') (@lem4293027 _103141 _103145 a s t x y x')). Qed.
Lemma lem4293029 {_103141 _103145 : Type'} (x : _103145) (y : _103141) : (@pair _103145 _103141 x y) = (@pair _103145 _103141 x y).
Proof. exact (eq_refl (@pair _103145 _103141 x y)). Qed.
Lemma lem4293030 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) : (term92 _103141 _103145 x a s t x' y) = (term93 _103141 _103145 a s t x x' y).
Proof. exact (MK_COMB (@lem4293028 _103141 _103145 a s t x' y x) (@lem4293029 _103141 _103145 x' y)). Qed.
Lemma lem4293032 {A B : Type'} (f : A -> B) (y : A) : (term68 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4293033 {_103141 _103145 : Type'} (f : type1223 _103141 _103145) (y : prod _103145 _103141) : (term94 _103141 _103145 f y) = (f y).
Proof. exact (@lem4293032 (prod _103145 _103141) Prop f y). Qed.
Lemma lem4293034 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) : (term95 _103141 _103145 a s t x x' y) = (term93 _103141 _103145 a s t x x' y).
Proof. exact (@lem4293033 _103141 _103145 (term91 _103141 _103145 a s t x' y x) (@pair _103145 _103141 x' y)). Qed.
Lemma lem4293035 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : _103145) (y : _103141) (x' : prod _103145 _103141) (t' : prod _103145 _103141) : (term96 _103141 _103145 a s t x y x' t') = (term90 _103141 _103145 a s t x y x' t').
Proof. exact (eq_refl (term96 _103141 _103145 a s t x y x' t')). Qed.
Lemma lem4293036 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : _103145) (y : _103141) (x' : prod _103145 _103141) : (term97 _103141 _103145 a s t x y x') = (term91 _103141 _103145 a s t x y x').
Proof. exact (fun_ext (fun t' : prod _103145 _103141 => @lem4293035 _103141 _103145 a s t x y x' t')). Qed.
Lemma lem4293037 {_103141 _103145 : Type'} (x : _103145) (y : _103141) : (@pair _103145 _103141 x y) = (@pair _103145 _103141 x y).
Proof. exact (eq_refl (@pair _103145 _103141 x y)). Qed.
Lemma lem4293038 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) : (term95 _103141 _103145 a s t x x' y) = (term93 _103141 _103145 a s t x x' y).
Proof. exact (MK_COMB (@lem4293036 _103141 _103145 a s t x' y x) (@lem4293037 _103141 _103145 x' y)). Qed.
Lemma lem4293039 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4293040 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) : (term98 _103141 _103145 a s t x x' y) = (term99 _103141 _103145 a s t x x' y).
Proof. exact (MK_COMB (@lem4293039) (@lem4293038 _103141 _103145 a s t x x' y)). Qed.
Lemma lem4293041 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) : (term93 _103141 _103145 a s t x x' y) = (term100 _103141 _103145 a s t x x' y).
Proof. exact (eq_refl (term93 _103141 _103145 a s t x x' y)). Qed.
Lemma lem4293042 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) : ((term95 _103141 _103145 a s t x x' y) = (term93 _103141 _103145 a s t x x' y)) = ((term93 _103141 _103145 a s t x x' y) = (term100 _103141 _103145 a s t x x' y)).
Proof. exact (MK_COMB (@lem4293040 _103141 _103145 a s t x x' y) (@lem4293041 _103141 _103145 a s t x x' y)). Qed.
Lemma lem4293043 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) : (term93 _103141 _103145 a s t x x' y) = (term100 _103141 _103145 a s t x x' y).
Proof. exact (EQ_MP (@lem4293042 _103141 _103145 a s t x x' y) (@lem4293034 _103141 _103145 a s t x x' y)). Qed.
Lemma lem4293054 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) : (term92 _103141 _103145 x a s t x' y) = (term100 _103141 _103145 a s t x x' y).
Proof. exact (TRANS (@lem4293030 _103141 _103145 a s t x x' y) (@lem4293043 _103141 _103145 a s t x x' y)). Qed.
Lemma lem4293055 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) : (term101 _103141 _103145 x a s t x') = (term102 _103141 _103145 a s t x x').
Proof. exact (fun_ext (fun y : _103141 => @lem4293054 _103141 _103145 a s t x x' y)). Qed.
Lemma lem4293056 {_103141 : Type'} : (@ex _103141) = (@ex _103141).
Proof. exact (eq_refl (@ex _103141)). Qed.
Lemma lem4293057 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) : (term103 _103141 _103145 x a s t x') = (term104 _103141 _103145 a s t x x').
Proof. exact (MK_COMB (@lem4293056 _103141) (@lem4293055 _103141 _103145 a s t x x')). Qed.
Lemma lem4293062 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term105 _103141 _103145 x a s t) = (term106 _103141 _103145 a s t x).
Proof. exact (fun_ext (fun x' : _103145 => @lem4293057 _103141 _103145 a s t x x')). Qed.
Lemma lem4293063 {_103145 : Type'} : (@ex _103145) = (@ex _103145).
Proof. exact (eq_refl (@ex _103145)). Qed.
Lemma lem4293064 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term67 _103141 _103145 x a s t) = (term107 _103141 _103145 a s t x).
Proof. exact (MK_COMB (@lem4293063 _103145) (@lem4293062 _103141 _103145 a s t x)). Qed.
Lemma lem4293069 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term64 _103141 _103145 x a s t) = (term107 _103141 _103145 a s t x).
Proof. exact (TRANS (@lem4292972 _103141 _103145 x a s t) (@lem4293064 _103141 _103145 a s t x)). Qed.
Lemma lem4293070 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4293071 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term66 _103141 _103145 x a s t) = (term108 _103141 _103145 a s t x).
Proof. exact (MK_COMB (@lem4293070) (@lem4293069 _103141 _103145 a s t x)). Qed.
Lemma lem4293073 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term109 A x s t) = (term110 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem4293074 {_103141 _103145 : Type'} (s : type1223 _103141 _103145) (x : prod _103145 _103141) (t : type1223 _103141 _103145) : (term111 _103141 _103145 x s t) = (term112 _103141 _103145 s x t).
Proof. exact (@lem4293073 (prod _103145 _103141) s x t). Qed.
Lemma lem4293075 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term113 _103141 _103145 x s t a) = (term114 _103141 _103145 s x t a).
Proof. exact (@lem4293074 _103141 _103145 (term115 _103141 _103145 s t) x (term116 _103141 _103145 t a)). Qed.
Lemma lem4293079 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term18 _83064 x P) = (term19 _83064 P x).
Proof. exact (EQ_MP (@lem3211648 _83064 P x) (@lem3211647 _83064 P x)). Qed.
Lemma lem4293080 {_103141 _103145 : Type'} (P : type916 _103141 _103145) (x : prod _103145 _103141) : (term54 _103141 _103145 x P) = (term55 _103141 _103145 P x).
Proof. exact (@lem4293079 (prod _103145 _103141) P x). Qed.
Lemma lem4293081 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term117 _103141 _103145 x s t) = (term118 _103141 _103145 s t x).
Proof. exact (@lem4293080 _103141 _103145 (term119 _103141 _103145 s t) x). Qed.
Lemma lem4293082 {_103141 _103145 : Type'} (GEN_PVAR_120 : prod _103145 _103141) (s : _103145 -> Prop) (t : type1470 _103141 _103145) : (term120 _103141 _103145 s t GEN_PVAR_120) = (term121 _103141 _103145 GEN_PVAR_120 s t).
Proof. exact (eq_refl (term120 _103141 _103145 s t GEN_PVAR_120)). Qed.
Lemma lem4293083 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) : (term122 _103141 _103145 s t) = (term123 _103141 _103145 s t).
Proof. exact (fun_ext (fun GEN_PVAR_120 : prod _103145 _103141 => @lem4293082 _103141 _103145 GEN_PVAR_120 s t)). Qed.
Lemma lem4293084 {_103141 _103145 : Type'} : (@GSPEC (prod _103145 _103141)) = (@GSPEC (prod _103145 _103141)).
Proof. exact (eq_refl (@GSPEC (prod _103145 _103141))). Qed.
Lemma lem4293085 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) : (term124 _103141 _103145 s t) = (term115 _103141 _103145 s t).
Proof. exact (MK_COMB (@lem4293084 _103141 _103145) (@lem4293083 _103141 _103145 s t)). Qed.
Lemma lem4293086 {_103141 _103145 : Type'} (x : prod _103145 _103141) : (@IN (prod _103145 _103141) x) = (@IN (prod _103145 _103141) x).
Proof. exact (eq_refl (@IN (prod _103145 _103141) x)). Qed.
Lemma lem4293087 {_103141 _103145 : Type'} (x : prod _103145 _103141) (s : _103145 -> Prop) (t : type1470 _103141 _103145) : (term117 _103141 _103145 x s t) = (term125 _103141 _103145 x s t).
Proof. exact (MK_COMB (@lem4293086 _103141 _103145 x) (@lem4293085 _103141 _103145 s t)). Qed.
Lemma lem4293088 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4293089 {_103141 _103145 : Type'} (x : prod _103145 _103141) (s : _103145 -> Prop) (t : type1470 _103141 _103145) : (term126 _103141 _103145 x s t) = (term127 _103141 _103145 x s t).
Proof. exact (MK_COMB (@lem4293088) (@lem4293087 _103141 _103145 x s t)). Qed.
Lemma lem4293090 {_103141 _103145 : Type'} (x : prod _103145 _103141) (s : _103145 -> Prop) (t : type1470 _103141 _103145) : (term118 _103141 _103145 s t x) = (term128 _103141 _103145 x s t).
Proof. exact (eq_refl (term118 _103141 _103145 s t x)). Qed.
Lemma lem4293091 {_103141 _103145 : Type'} (x : prod _103145 _103141) (s : _103145 -> Prop) (t : type1470 _103141 _103145) : ((term117 _103141 _103145 x s t) = (term118 _103141 _103145 s t x)) = ((term125 _103141 _103145 x s t) = (term128 _103141 _103145 x s t)).
Proof. exact (MK_COMB (@lem4293089 _103141 _103145 x s t) (@lem4293090 _103141 _103145 x s t)). Qed.
Lemma lem4293092 {_103141 _103145 : Type'} (x : prod _103145 _103141) (s : _103145 -> Prop) (t : type1470 _103141 _103145) : (term125 _103141 _103145 x s t) = (term128 _103141 _103145 x s t).
Proof. exact (EQ_MP (@lem4293091 _103141 _103145 x s t) (@lem4293081 _103141 _103145 s t x)). Qed.
Lemma lem4293102 {A B : Type'} (f : A -> B) (y : A) : (term68 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4293103 {_103141 _103145 : Type'} (f : type1534 _103141 _103145) (y : Prop) : (term69 _103141 _103145 f y) = (f y).
Proof. exact (@lem4293102 Prop (type1223 _103141 _103145) f y). Qed.
Lemma lem4293104 {_103141 _103145 : Type'} (x : prod _103145 _103141) (s : _103145 -> Prop) (y : _103141) (t : type1470 _103141 _103145) (x' : _103145) : (term129 _103141 _103145 x s y t x') = (term130 _103141 _103145 x s y t x').
Proof. exact (@lem4293103 _103141 _103145 (term72 _103141 _103145 x) (term131 _103141 _103145 s y t x')). Qed.
Lemma lem4293105 {_103141 _103145 : Type'} (p : Prop) (x : prod _103145 _103141) : (term74 _103141 _103145 x p) = (term75 _103141 _103145 p x).
Proof. exact (eq_refl (term74 _103141 _103145 x p)). Qed.
Lemma lem4293106 {_103141 _103145 : Type'} (x : prod _103145 _103141) : (term76 _103141 _103145 x) = (term72 _103141 _103145 x).
Proof. exact (fun_ext (fun p : Prop => @lem4293105 _103141 _103145 p x)). Qed.
Lemma lem4293107 {_103141 _103145 : Type'} (s : _103145 -> Prop) (y : _103141) (t : type1470 _103141 _103145) (x : _103145) : (term131 _103141 _103145 s y t x) = (term131 _103141 _103145 s y t x).
Proof. exact (eq_refl (term131 _103141 _103145 s y t x)). Qed.
Lemma lem4293108 {_103141 _103145 : Type'} (x : prod _103145 _103141) (s : _103145 -> Prop) (y : _103141) (t : type1470 _103141 _103145) (x' : _103145) : (term129 _103141 _103145 x s y t x') = (term130 _103141 _103145 x s y t x').
Proof. exact (MK_COMB (@lem4293106 _103141 _103145 x) (@lem4293107 _103141 _103145 s y t x')). Qed.
Lemma lem4293109 {_103141 _103145 : Type'} : (@eq ((prod _103145 _103141) -> Prop)) = (@eq ((prod _103145 _103141) -> Prop)).
Proof. exact (eq_refl (@eq ((prod _103145 _103141) -> Prop))). Qed.
Lemma lem4293110 {_103141 _103145 : Type'} (x : prod _103145 _103141) (s : _103145 -> Prop) (y : _103141) (t : type1470 _103141 _103145) (x' : _103145) : (term132 _103141 _103145 x s y t x') = (term133 _103141 _103145 x s y t x').
Proof. exact (MK_COMB (@lem4293109 _103141 _103145) (@lem4293108 _103141 _103145 x s y t x')). Qed.
Lemma lem4293111 {_103141 _103145 : Type'} (s : _103145 -> Prop) (y : _103141) (t : type1470 _103141 _103145) (x : _103145) (x' : prod _103145 _103141) : (term130 _103141 _103145 x' s y t x) = (term134 _103141 _103145 s y t x x').
Proof. exact (eq_refl (term130 _103141 _103145 x' s y t x)). Qed.
Lemma lem4293112 {_103141 _103145 : Type'} (s : _103145 -> Prop) (y : _103141) (t : type1470 _103141 _103145) (x : _103145) (x' : prod _103145 _103141) : ((term129 _103141 _103145 x' s y t x) = (term130 _103141 _103145 x' s y t x)) = ((term130 _103141 _103145 x' s y t x) = (term134 _103141 _103145 s y t x x')).
Proof. exact (MK_COMB (@lem4293110 _103141 _103145 x' s y t x) (@lem4293111 _103141 _103145 s y t x x')). Qed.
Lemma lem4293113 {_103141 _103145 : Type'} (s : _103145 -> Prop) (y : _103141) (t : type1470 _103141 _103145) (x : _103145) (x' : prod _103145 _103141) : (term130 _103141 _103145 x' s y t x) = (term134 _103141 _103145 s y t x x').
Proof. exact (EQ_MP (@lem4293112 _103141 _103145 s y t x x') (@lem4293104 _103141 _103145 x' s y t x)). Qed.
Lemma lem4293119 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4293120 {_103145 : Type'} (P : _103145 -> Prop) (x : _103145) : (@IN _103145 x P) = (P x).
Proof. exact (@lem4293119 _103145 P x). Qed.
Lemma lem4293121 {_103145 : Type'} (s : _103145 -> Prop) (x : _103145) : (@IN _103145 x s) = (s x).
Proof. exact (@lem4293120 _103145 s x). Qed.
Lemma lem4293122 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4293123 {_103145 : Type'} (s : _103145 -> Prop) (x : _103145) : (term135 _103145 x s) = (term136 _103145 s x).
Proof. exact (MK_COMB (@lem4293122) (@lem4293121 _103145 s x)). Qed.
Lemma lem4293125 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4293126 {_103141 : Type'} (P : _103141 -> Prop) (x : _103141) : (@IN _103141 x P) = (P x).
Proof. exact (@lem4293125 _103141 P x). Qed.
Lemma lem4293127 {_103141 _103145 : Type'} (t : type1470 _103141 _103145) (x : _103145) (y : _103141) : (term85 _103141 _103145 y t x) = (t x y).
Proof. exact (@lem4293126 _103141 (t x) y). Qed.
Lemma lem4293128 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : _103145) (y : _103141) : (term131 _103141 _103145 s y t x) = (term137 _103141 _103145 s t x y).
Proof. exact (MK_COMB (@lem4293123 _103145 s x) (@lem4293127 _103141 _103145 t x y)). Qed.
Lemma lem4293131 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4293132 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : _103145) (y : _103141) : (term138 _103141 _103145 s y t x) = (term139 _103141 _103145 s t x y).
Proof. exact (MK_COMB (@lem4293131) (@lem4293128 _103141 _103145 s t x y)). Qed.
Lemma lem4293135 {_103141 _103145 : Type'} (x : prod _103145 _103141) (t : prod _103145 _103141) : (x = t) = (x = t).
Proof. exact (eq_refl (x = t)). Qed.
Lemma lem4293136 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : _103145) (y : _103141) (x' : prod _103145 _103141) (t' : prod _103145 _103141) : (term140 _103141 _103145 s y t x x' t') = (term141 _103141 _103145 s t x y x' t').
Proof. exact (MK_COMB (@lem4293132 _103141 _103145 s t x y) (@lem4293135 _103141 _103145 x' t')). Qed.
Lemma lem4293139 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : _103145) (y : _103141) (x' : prod _103145 _103141) : (term134 _103141 _103145 s y t x x') = (term142 _103141 _103145 s t x y x').
Proof. exact (fun_ext (fun t' : prod _103145 _103141 => @lem4293136 _103141 _103145 s t x y x' t')). Qed.
Lemma lem4293140 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : _103145) (y : _103141) (x' : prod _103145 _103141) : (term130 _103141 _103145 x' s y t x) = (term142 _103141 _103145 s t x y x').
Proof. exact (TRANS (@lem4293113 _103141 _103145 s y t x x') (@lem4293139 _103141 _103145 s t x y x')). Qed.
Lemma lem4293141 {_103141 _103145 : Type'} (x : _103145) (y : _103141) : (@pair _103145 _103141 x y) = (@pair _103145 _103141 x y).
Proof. exact (eq_refl (@pair _103145 _103141 x y)). Qed.
Lemma lem4293142 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) : (term143 _103141 _103145 x s t x' y) = (term144 _103141 _103145 s t x x' y).
Proof. exact (MK_COMB (@lem4293140 _103141 _103145 s t x' y x) (@lem4293141 _103141 _103145 x' y)). Qed.
Lemma lem4293144 {A B : Type'} (f : A -> B) (y : A) : (term68 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4293145 {_103141 _103145 : Type'} (f : type1223 _103141 _103145) (y : prod _103145 _103141) : (term94 _103141 _103145 f y) = (f y).
Proof. exact (@lem4293144 (prod _103145 _103141) Prop f y). Qed.
Lemma lem4293146 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) : (term145 _103141 _103145 s t x x' y) = (term144 _103141 _103145 s t x x' y).
Proof. exact (@lem4293145 _103141 _103145 (term142 _103141 _103145 s t x' y x) (@pair _103145 _103141 x' y)). Qed.
Lemma lem4293147 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : _103145) (y : _103141) (x' : prod _103145 _103141) (t' : prod _103145 _103141) : (term146 _103141 _103145 s t x y x' t') = (term141 _103141 _103145 s t x y x' t').
Proof. exact (eq_refl (term146 _103141 _103145 s t x y x' t')). Qed.
Lemma lem4293148 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : _103145) (y : _103141) (x' : prod _103145 _103141) : (term147 _103141 _103145 s t x y x') = (term142 _103141 _103145 s t x y x').
Proof. exact (fun_ext (fun t' : prod _103145 _103141 => @lem4293147 _103141 _103145 s t x y x' t')). Qed.
Lemma lem4293149 {_103141 _103145 : Type'} (x : _103145) (y : _103141) : (@pair _103145 _103141 x y) = (@pair _103145 _103141 x y).
Proof. exact (eq_refl (@pair _103145 _103141 x y)). Qed.
Lemma lem4293150 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) : (term145 _103141 _103145 s t x x' y) = (term144 _103141 _103145 s t x x' y).
Proof. exact (MK_COMB (@lem4293148 _103141 _103145 s t x' y x) (@lem4293149 _103141 _103145 x' y)). Qed.
Lemma lem4293151 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4293152 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) : (term148 _103141 _103145 s t x x' y) = (term149 _103141 _103145 s t x x' y).
Proof. exact (MK_COMB (@lem4293151) (@lem4293150 _103141 _103145 s t x x' y)). Qed.
Lemma lem4293153 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) : (term144 _103141 _103145 s t x x' y) = (term150 _103141 _103145 s t x x' y).
Proof. exact (eq_refl (term144 _103141 _103145 s t x x' y)). Qed.
Lemma lem4293154 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) : ((term145 _103141 _103145 s t x x' y) = (term144 _103141 _103145 s t x x' y)) = ((term144 _103141 _103145 s t x x' y) = (term150 _103141 _103145 s t x x' y)).
Proof. exact (MK_COMB (@lem4293152 _103141 _103145 s t x x' y) (@lem4293153 _103141 _103145 s t x x' y)). Qed.
Lemma lem4293155 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) : (term144 _103141 _103145 s t x x' y) = (term150 _103141 _103145 s t x x' y).
Proof. exact (EQ_MP (@lem4293154 _103141 _103145 s t x x' y) (@lem4293146 _103141 _103145 s t x x' y)). Qed.
Lemma lem4293162 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) : (term143 _103141 _103145 x s t x' y) = (term150 _103141 _103145 s t x x' y).
Proof. exact (TRANS (@lem4293142 _103141 _103145 s t x x' y) (@lem4293155 _103141 _103145 s t x x' y)). Qed.
Lemma lem4293163 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) : (term151 _103141 _103145 x s t x') = (term152 _103141 _103145 s t x x').
Proof. exact (fun_ext (fun y : _103141 => @lem4293162 _103141 _103145 s t x x' y)). Qed.
Lemma lem4293164 {_103141 : Type'} : (@ex _103141) = (@ex _103141).
Proof. exact (eq_refl (@ex _103141)). Qed.
Lemma lem4293165 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) : (term153 _103141 _103145 x s t x') = (term154 _103141 _103145 s t x x').
Proof. exact (MK_COMB (@lem4293164 _103141) (@lem4293163 _103141 _103145 s t x x')). Qed.
Lemma lem4293170 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term155 _103141 _103145 x s t) = (term156 _103141 _103145 s t x).
Proof. exact (fun_ext (fun x' : _103145 => @lem4293165 _103141 _103145 s t x x')). Qed.
Lemma lem4293171 {_103145 : Type'} : (@ex _103145) = (@ex _103145).
Proof. exact (eq_refl (@ex _103145)). Qed.
Lemma lem4293172 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term128 _103141 _103145 x s t) = (term157 _103141 _103145 s t x).
Proof. exact (MK_COMB (@lem4293171 _103145) (@lem4293170 _103141 _103145 s t x)). Qed.
Lemma lem4293177 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term125 _103141 _103145 x s t) = (term157 _103141 _103145 s t x).
Proof. exact (TRANS (@lem4293092 _103141 _103145 x s t) (@lem4293172 _103141 _103145 s t x)). Qed.
Lemma lem4293178 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4293179 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term158 _103141 _103145 x s t) = (term159 _103141 _103145 s t x).
Proof. exact (MK_COMB (@lem4293178) (@lem4293177 _103141 _103145 s t x)). Qed.
Lemma lem4293181 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term25 A B y f s) = (term26 A B y f s).
Proof. exact (EQ_MP (@lem3211657 A B y f s) (@lem3211656 A B y s f)). Qed.
Lemma lem4293182 {_103141 _103145 : Type'} (y : prod _103145 _103141) (f : type1429 _103141 _103145) (s : _103141 -> Prop) : (term160 _103141 _103145 y f s) = (term161 _103141 _103145 y f s).
Proof. exact (@lem4293181 _103141 (prod _103145 _103141) y f s). Qed.
Lemma lem4293183 {_103141 _103145 : Type'} (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term162 _103141 _103145 x t a) = (term163 _103141 _103145 x t a).
Proof. exact (@lem4293182 _103141 _103145 x (term164 _103141 _103145 a) (t a)). Qed.
Lemma lem4293193 {A B : Type'} (f : A -> B) (y : A) : (term68 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4293194 {_103141 _103145 : Type'} (f : type1429 _103141 _103145) (y : _103141) : (term165 _103141 _103145 f y) = (f y).
Proof. exact (@lem4293193 _103141 (prod _103145 _103141) f y). Qed.
Lemma lem4293195 {_103141 _103145 : Type'} (a : _103145) (x : _103141) : (term166 _103141 _103145 a x) = (term167 _103141 _103145 a x).
Proof. exact (@lem4293194 _103141 _103145 (term164 _103141 _103145 a) x). Qed.
Lemma lem4293196 {_103141 _103145 : Type'} (a : _103145) (y : _103141) : (term167 _103141 _103145 a y) = (@pair _103145 _103141 a y).
Proof. exact (eq_refl (term167 _103141 _103145 a y)). Qed.
Lemma lem4293197 {_103141 _103145 : Type'} (a : _103145) : (term168 _103141 _103145 a) = (term164 _103141 _103145 a).
Proof. exact (fun_ext (fun y : _103141 => @lem4293196 _103141 _103145 a y)). Qed.
Lemma lem4293198 {_103141 : Type'} (x : _103141) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4293199 {_103141 _103145 : Type'} (a : _103145) (x : _103141) : (term166 _103141 _103145 a x) = (term167 _103141 _103145 a x).
Proof. exact (MK_COMB (@lem4293197 _103141 _103145 a) (@lem4293198 _103141 x)). Qed.
Lemma lem4293200 {_103141 _103145 : Type'} : (@eq (prod _103145 _103141)) = (@eq (prod _103145 _103141)).
Proof. exact (eq_refl (@eq (prod _103145 _103141))). Qed.
Lemma lem4293201 {_103141 _103145 : Type'} (a : _103145) (x : _103141) : (term169 _103141 _103145 a x) = (term170 _103141 _103145 a x).
Proof. exact (MK_COMB (@lem4293200 _103141 _103145) (@lem4293199 _103141 _103145 a x)). Qed.
Lemma lem4293202 {_103141 _103145 : Type'} (a : _103145) (x : _103141) : (term167 _103141 _103145 a x) = (@pair _103145 _103141 a x).
Proof. exact (eq_refl (term167 _103141 _103145 a x)). Qed.
Lemma lem4293203 {_103141 _103145 : Type'} (a : _103145) (x : _103141) : ((term166 _103141 _103145 a x) = (term167 _103141 _103145 a x)) = ((term167 _103141 _103145 a x) = (@pair _103145 _103141 a x)).
Proof. exact (MK_COMB (@lem4293201 _103141 _103145 a x) (@lem4293202 _103141 _103145 a x)). Qed.
Lemma lem4293204 {_103141 _103145 : Type'} (a : _103145) (x : _103141) : (term167 _103141 _103145 a x) = (@pair _103145 _103141 a x).
Proof. exact (EQ_MP (@lem4293203 _103141 _103145 a x) (@lem4293195 _103141 _103145 a x)). Qed.
Lemma lem4293205 {_103141 _103145 : Type'} (x : prod _103145 _103141) : (@eq (prod _103145 _103141) x) = (@eq (prod _103145 _103141) x).
Proof. exact (eq_refl (@eq (prod _103145 _103141) x)). Qed.
Lemma lem4293206 {_103141 _103145 : Type'} (x : prod _103145 _103141) (a : _103145) (x' : _103141) : (x = (term167 _103141 _103145 a x')) = (x = (@pair _103145 _103141 a x')).
Proof. exact (MK_COMB (@lem4293205 _103141 _103145 x) (@lem4293204 _103141 _103145 a x')). Qed.
Lemma lem4293209 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4293210 {_103141 _103145 : Type'} (x : prod _103145 _103141) (a : _103145) (x' : _103141) : (term171 _103141 _103145 x a x') = (term172 _103141 _103145 x a x').
Proof. exact (MK_COMB (@lem4293209) (@lem4293206 _103141 _103145 x a x')). Qed.
Lemma lem4293212 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4293213 {_103141 : Type'} (P : _103141 -> Prop) (x : _103141) : (@IN _103141 x P) = (P x).
Proof. exact (@lem4293212 _103141 P x). Qed.
Lemma lem4293214 {_103141 _103145 : Type'} (t : type1470 _103141 _103145) (a : _103145) (x : _103141) : (term85 _103141 _103145 x t a) = (t a x).
Proof. exact (@lem4293213 _103141 (t a) x). Qed.
Lemma lem4293215 {_103141 _103145 : Type'} (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (x' : _103141) : (term173 _103141 _103145 x x' t a) = (term174 _103141 _103145 x t a x').
Proof. exact (MK_COMB (@lem4293210 _103141 _103145 x a x') (@lem4293214 _103141 _103145 t a x')). Qed.
Lemma lem4293218 {_103141 _103145 : Type'} (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term175 _103141 _103145 x t a) = (term176 _103141 _103145 x t a).
Proof. exact (fun_ext (fun x' : _103141 => @lem4293215 _103141 _103145 x t a x')). Qed.
Lemma lem4293219 {_103141 : Type'} : (@ex _103141) = (@ex _103141).
Proof. exact (eq_refl (@ex _103141)). Qed.
Lemma lem4293220 {_103141 _103145 : Type'} (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term163 _103141 _103145 x t a) = (term177 _103141 _103145 x t a).
Proof. exact (MK_COMB (@lem4293219 _103141) (@lem4293218 _103141 _103145 x t a)). Qed.
Lemma lem4293225 {_103141 _103145 : Type'} (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term162 _103141 _103145 x t a) = (term177 _103141 _103145 x t a).
Proof. exact (TRANS (@lem4293183 _103141 _103145 x t a) (@lem4293220 _103141 _103145 x t a)). Qed.
Lemma lem4293226 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term114 _103141 _103145 s x t a) = (term178 _103141 _103145 s x t a).
Proof. exact (MK_COMB (@lem4293179 _103141 _103145 s t x) (@lem4293225 _103141 _103145 x t a)). Qed.
Lemma lem4293229 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term113 _103141 _103145 x s t a) = (term178 _103141 _103145 s x t a).
Proof. exact (TRANS (@lem4293075 _103141 _103145 s x t a) (@lem4293226 _103141 _103145 s x t a)). Qed.
Lemma lem4293230 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : ((term64 _103141 _103145 x a s t) = (term113 _103141 _103145 x s t a)) = ((term107 _103141 _103145 a s t x) = (term178 _103141 _103145 s x t a)).
Proof. exact (MK_COMB (@lem4293071 _103141 _103145 a s t x) (@lem4293229 _103141 _103145 s x t a)). Qed.
Lemma lem4293233 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (a : _103145) : (term179 _103141 _103145 s t a) = (term180 _103141 _103145 s t a).
Proof. exact (fun_ext (fun x : prod _103145 _103141 => @lem4293230 _103141 _103145 s x t a)). Qed.
Lemma lem4293234 {_103141 _103145 : Type'} : (@all (prod _103145 _103141)) = (@all (prod _103145 _103141)).
Proof. exact (eq_refl (@all (prod _103145 _103141))). Qed.
Lemma lem4293235 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (a : _103145) : (term53 _103141 _103145 s t a) = (term181 _103141 _103145 s t a).
Proof. exact (MK_COMB (@lem4293234 _103141 _103145) (@lem4293233 _103141 _103145 s t a)). Qed.
Lemma lem4293240 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (a : _103145) : (term181 _103141 _103145 s t a) = (term53 _103141 _103145 s t a).
Proof. exact (SYM (@lem4293235 _103141 _103145 s t a)). Qed.
Lemma lem4293242 (p : Prop) : p = (term182 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4293243 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (a : _103145) : (term181 _103141 _103145 s t a) = (term183 _103141 _103145 s t a).
Proof. exact (@lem4293242 (term181 _103141 _103145 s t a)). Qed.
Lemma lem4293244 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (a : _103145) : (term183 _103141 _103145 s t a) = (term181 _103141 _103145 s t a).
Proof. exact (SYM (@lem4293243 _103141 _103145 s t a)). Qed.
Lemma lem4293245 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (a : _103145) (h1 : term184 _103141 _103145 s t a) : term184 _103141 _103145 s t a.
Proof. exact (h1). Qed.
Lemma lem4293248 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (a : _103145) (h1 : term183 _103141 _103145 s t a) : term183 _103141 _103145 s t a.
Proof. exact (h1). Qed.
Lemma lem4293249 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (a : _103145) : term185 _103141 _103145 s t a.
Proof. exact (fun h0 : term183 _103141 _103145 s t a => @lem4293248 _103141 _103145 s t a h0). Qed.
Lemma lem4293250 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (a : _103145) (h1 : term185 _103141 _103145 s t a) : term185 _103141 _103145 s t a.
Proof. exact (h1). Qed.
Lemma lem4293251 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (a : _103145) (h1 : term183 _103141 _103145 s t a) : term183 _103141 _103145 s t a.
Proof. exact (h1). Qed.
Lemma lem4293252 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (a : _103145) (h1 : term183 _103141 _103145 s t a) (h2 : term185 _103141 _103145 s t a) : term183 _103141 _103145 s t a.
Proof. exact (@lem4293250 _103141 _103145 s t a h2 (@lem4293251 _103141 _103145 s t a h1)). Qed.
Lemma lem4293253 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (a : _103145) (h1 : term183 _103141 _103145 s t a) : term186 _103141 _103145 s t a.
Proof. exact (fun h0 : term185 _103141 _103145 s t a => @lem4293252 _103141 _103145 s t a h1 h0). Qed.
Lemma lem4293254 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (a : _103145) (h1 : term185 _103141 _103145 s t a) : term185 _103141 _103145 s t a.
Proof. exact (h1). Qed.
Lemma lem4293255 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (a : _103145) (h1 : term183 _103141 _103145 s t a) (h2 : term185 _103141 _103145 s t a) : term183 _103141 _103145 s t a.
Proof. exact (@lem4293253 _103141 _103145 s t a h1 (@lem4293254 _103141 _103145 s t a h2)). Qed.
Lemma lem4293256 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (a : _103145) (h1 : term185 _103141 _103145 s t a) : term185 _103141 _103145 s t a.
Proof. exact (fun h0 : term183 _103141 _103145 s t a => @lem4293255 _103141 _103145 s t a h0 h1). Qed.
Lemma lem4293257 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (a : _103145) : term187 _103141 _103145 s t a.
Proof. exact (fun h0 : term185 _103141 _103145 s t a => @lem4293256 _103141 _103145 s t a h0). Qed.
Lemma lem4293260 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (a : _103145) : term185 _103141 _103145 s t a.
Proof. exact (@lem4293257 _103141 _103145 s t a (@lem4293249 _103141 _103145 s t a)). Qed.
Lemma lem4293261 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (a : _103145) : term185 _103141 _103145 s t a.
Proof. exact (@lem4293260 _103141 _103145 s t a). Qed.
Lemma lem4293275 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4293276 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (a : _103145) : (term183 _103141 _103145 s t a) = (term188 _103141 _103145 s t a).
Proof. exact (@lem4293275 (term184 _103141 _103145 s t a)). Qed.
Lemma lem4293278 (t : Prop) : (term189 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4293279 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (a : _103145) : (term188 _103141 _103145 s t a) = (term181 _103141 _103145 s t a).
Proof. exact (@lem4293278 (term181 _103141 _103145 s t a)). Qed.
Lemma lem4293284 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (a : _103145) : (term183 _103141 _103145 s t a) = (term181 _103141 _103145 s t a).
Proof. exact (TRANS (@lem4293276 _103141 _103145 s t a) (@lem4293279 _103141 _103145 s t a)). Qed.
Lemma lem4293451 {_103141 _103145 : Type'} (t : type1470 _103141 _103145) (a : _103145) : (term190 _103141 _103145 t a) = (term191 _103141 _103145 t a).
Proof. exact (fun_ext (fun s : _103145 -> Prop => @lem4293284 _103141 _103145 s t a)). Qed.
Lemma lem4293452 {_103145 : Type'} : (@all (_103145 -> Prop)) = (@all (_103145 -> Prop)).
Proof. exact (eq_refl (@all (_103145 -> Prop))). Qed.
Lemma lem4293453 {_103141 _103145 : Type'} (t : type1470 _103141 _103145) (a : _103145) : (term192 _103141 _103145 t a) = (term193 _103141 _103145 t a).
Proof. exact (MK_COMB (@lem4293452 _103145) (@lem4293451 _103141 _103145 t a)). Qed.
Lemma lem4293458 {_103141 _103145 : Type'} (a : _103145) : (term194 _103141 _103145 a) = (term195 _103141 _103145 a).
Proof. exact (fun_ext (fun t : type1470 _103141 _103145 => @lem4293453 _103141 _103145 t a)). Qed.
Lemma lem4293459 {_103141 _103145 : Type'} : (@all (_103145 -> _103141 -> Prop)) = (@all (_103145 -> _103141 -> Prop)).
Proof. exact (eq_refl (@all (_103145 -> _103141 -> Prop))). Qed.
Lemma lem4293460 {_103141 _103145 : Type'} (a : _103145) : (term196 _103141 _103145 a) = (term197 _103141 _103145 a).
Proof. exact (MK_COMB (@lem4293459 _103141 _103145) (@lem4293458 _103141 _103145 a)). Qed.
Lemma lem4293465 {_103141 _103145 : Type'} : (term198 _103141 _103145) = (term199 _103141 _103145).
Proof. exact (fun_ext (fun a : _103145 => @lem4293460 _103141 _103145 a)). Qed.
Lemma lem4293466 {_103145 : Type'} : (@all _103145) = (@all _103145).
Proof. exact (eq_refl (@all _103145)). Qed.
Lemma lem4293475 {_103141 _103145 : Type'} : (term200 _103141 _103145) = (term201 _103141 _103145).
Proof. exact (MK_COMB (@lem4293466 _103145) (@lem4293465 _103141 _103145)). Qed.
Lemma lem4293480 {_103141 _103145 : Type'} (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (x' : _103141) : (term174 _103141 _103145 x t a x') = (term174 _103141 _103145 x t a x').
Proof. exact (eq_refl (term174 _103141 _103145 x t a x')). Qed.
Lemma lem4293481 {_103141 _103145 : Type'} (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term176 _103141 _103145 x t a) = (term176 _103141 _103145 x t a).
Proof. exact (fun_ext (fun x' : _103141 => @lem4293480 _103141 _103145 x t a x')). Qed.
Lemma lem4293482 {_103141 : Type'} : (@ex _103141) = (@ex _103141).
Proof. exact (eq_refl (@ex _103141)). Qed.
Lemma lem4293483 {_103141 _103145 : Type'} (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term177 _103141 _103145 x t a) = (term177 _103141 _103145 x t a).
Proof. exact (MK_COMB (@lem4293482 _103141) (@lem4293481 _103141 _103145 x t a)). Qed.
Lemma lem4293492 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) : (term150 _103141 _103145 s t x x' y) = (term150 _103141 _103145 s t x x' y).
Proof. exact (eq_refl (term150 _103141 _103145 s t x x' y)). Qed.
Lemma lem4293493 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) : (term152 _103141 _103145 s t x x') = (term152 _103141 _103145 s t x x').
Proof. exact (fun_ext (fun y : _103141 => @lem4293492 _103141 _103145 s t x x' y)). Qed.
Lemma lem4293494 {_103141 : Type'} : (@ex _103141) = (@ex _103141).
Proof. exact (eq_refl (@ex _103141)). Qed.
Lemma lem4293495 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) : (term154 _103141 _103145 s t x x') = (term154 _103141 _103145 s t x x').
Proof. exact (MK_COMB (@lem4293494 _103141) (@lem4293493 _103141 _103145 s t x x')). Qed.
Lemma lem4293496 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term156 _103141 _103145 s t x) = (term156 _103141 _103145 s t x).
Proof. exact (fun_ext (fun x' : _103145 => @lem4293495 _103141 _103145 s t x x')). Qed.
Lemma lem4293497 {_103145 : Type'} : (@ex _103145) = (@ex _103145).
Proof. exact (eq_refl (@ex _103145)). Qed.
Lemma lem4293498 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term157 _103141 _103145 s t x) = (term157 _103141 _103145 s t x).
Proof. exact (MK_COMB (@lem4293497 _103145) (@lem4293496 _103141 _103145 s t x)). Qed.
Lemma lem4293499 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4293500 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term159 _103141 _103145 s t x) = (term159 _103141 _103145 s t x).
Proof. exact (MK_COMB (@lem4293499) (@lem4293498 _103141 _103145 s t x)). Qed.
Lemma lem4293501 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term178 _103141 _103145 s x t a) = (term178 _103141 _103145 s x t a).
Proof. exact (MK_COMB (@lem4293500 _103141 _103145 s t x) (@lem4293483 _103141 _103145 x t a)). Qed.
Lemma lem4293514 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) : (term100 _103141 _103145 a s t x x' y) = (term100 _103141 _103145 a s t x x' y).
Proof. exact (eq_refl (term100 _103141 _103145 a s t x x' y)). Qed.
Lemma lem4293515 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) : (term102 _103141 _103145 a s t x x') = (term102 _103141 _103145 a s t x x').
Proof. exact (fun_ext (fun y : _103141 => @lem4293514 _103141 _103145 a s t x x' y)). Qed.
Lemma lem4293516 {_103141 : Type'} : (@ex _103141) = (@ex _103141).
Proof. exact (eq_refl (@ex _103141)). Qed.
Lemma lem4293517 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) : (term104 _103141 _103145 a s t x x') = (term104 _103141 _103145 a s t x x').
Proof. exact (MK_COMB (@lem4293516 _103141) (@lem4293515 _103141 _103145 a s t x x')). Qed.
Lemma lem4293518 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term106 _103141 _103145 a s t x) = (term106 _103141 _103145 a s t x).
Proof. exact (fun_ext (fun x' : _103145 => @lem4293517 _103141 _103145 a s t x x')). Qed.
Lemma lem4293519 {_103145 : Type'} : (@ex _103145) = (@ex _103145).
Proof. exact (eq_refl (@ex _103145)). Qed.
Lemma lem4293520 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term107 _103141 _103145 a s t x) = (term107 _103141 _103145 a s t x).
Proof. exact (MK_COMB (@lem4293519 _103145) (@lem4293518 _103141 _103145 a s t x)). Qed.
Lemma lem4293521 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4293522 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term108 _103141 _103145 a s t x) = (term108 _103141 _103145 a s t x).
Proof. exact (MK_COMB (@lem4293521) (@lem4293520 _103141 _103145 a s t x)). Qed.
Lemma lem4293523 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : ((term107 _103141 _103145 a s t x) = (term178 _103141 _103145 s x t a)) = ((term107 _103141 _103145 a s t x) = (term178 _103141 _103145 s x t a)).
Proof. exact (MK_COMB (@lem4293522 _103141 _103145 a s t x) (@lem4293501 _103141 _103145 s x t a)). Qed.
Lemma lem4293524 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (a : _103145) : (term180 _103141 _103145 s t a) = (term180 _103141 _103145 s t a).
Proof. exact (fun_ext (fun x : prod _103145 _103141 => @lem4293523 _103141 _103145 s x t a)). Qed.
Lemma lem4293525 {_103141 _103145 : Type'} : (@all (prod _103145 _103141)) = (@all (prod _103145 _103141)).
Proof. exact (eq_refl (@all (prod _103145 _103141))). Qed.
Lemma lem4293526 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (a : _103145) : (term181 _103141 _103145 s t a) = (term181 _103141 _103145 s t a).
Proof. exact (MK_COMB (@lem4293525 _103141 _103145) (@lem4293524 _103141 _103145 s t a)). Qed.
Lemma lem4293527 {_103141 _103145 : Type'} (t : type1470 _103141 _103145) (a : _103145) : (term191 _103141 _103145 t a) = (term191 _103141 _103145 t a).
Proof. exact (fun_ext (fun s : _103145 -> Prop => @lem4293526 _103141 _103145 s t a)). Qed.
Lemma lem4293528 {_103145 : Type'} : (@all (_103145 -> Prop)) = (@all (_103145 -> Prop)).
Proof. exact (eq_refl (@all (_103145 -> Prop))). Qed.
Lemma lem4293529 {_103141 _103145 : Type'} (t : type1470 _103141 _103145) (a : _103145) : (term193 _103141 _103145 t a) = (term193 _103141 _103145 t a).
Proof. exact (MK_COMB (@lem4293528 _103145) (@lem4293527 _103141 _103145 t a)). Qed.
Lemma lem4293530 {_103141 _103145 : Type'} (a : _103145) : (term195 _103141 _103145 a) = (term195 _103141 _103145 a).
Proof. exact (fun_ext (fun t : type1470 _103141 _103145 => @lem4293529 _103141 _103145 t a)). Qed.
Lemma lem4293531 {_103141 _103145 : Type'} : (@all (_103145 -> _103141 -> Prop)) = (@all (_103145 -> _103141 -> Prop)).
Proof. exact (eq_refl (@all (_103145 -> _103141 -> Prop))). Qed.
Lemma lem4293532 {_103141 _103145 : Type'} (a : _103145) : (term197 _103141 _103145 a) = (term197 _103141 _103145 a).
Proof. exact (MK_COMB (@lem4293531 _103141 _103145) (@lem4293530 _103141 _103145 a)). Qed.
Lemma lem4293533 {_103141 _103145 : Type'} : (term199 _103141 _103145) = (term199 _103141 _103145).
Proof. exact (fun_ext (fun a : _103145 => @lem4293532 _103141 _103145 a)). Qed.
Lemma lem4293534 {_103145 : Type'} : (@all _103145) = (@all _103145).
Proof. exact (eq_refl (@all _103145)). Qed.
Lemma lem4293535 {_103141 _103145 : Type'} : (term201 _103141 _103145) = (term201 _103141 _103145).
Proof. exact (MK_COMB (@lem4293534 _103145) (@lem4293533 _103141 _103145)). Qed.
Lemma lem4293606 {_103141 _103145 : Type'} : (term200 _103141 _103145) = (term201 _103141 _103145).
Proof. exact (TRANS (@lem4293475 _103141 _103145) (@lem4293535 _103141 _103145)). Qed.
Lemma lem4293607 {_103141 _103145 : Type'} : (term201 _103141 _103145) = (term200 _103141 _103145).
Proof. exact (SYM (@lem4293606 _103141 _103145)). Qed.
Lemma lem4293609 (p : Prop) : p = (term182 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4293610 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : ((term107 _103141 _103145 a s t x) = (term178 _103141 _103145 s x t a)) = (term202 _103141 _103145 s x t a).
Proof. exact (@lem4293609 ((term107 _103141 _103145 a s t x) = (term178 _103141 _103145 s x t a))). Qed.
Lemma lem4293611 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term202 _103141 _103145 s x t a) = ((term107 _103141 _103145 a s t x) = (term178 _103141 _103145 s x t a)).
Proof. exact (SYM (@lem4293610 _103141 _103145 s x t a)). Qed.
Lemma lem4293612 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (h1 : term203 _103141 _103145 s x t a) : term203 _103141 _103145 s x t a.
Proof. exact (h1). Qed.
Lemma lem4293621 {_103145 : Type'} (a : _103145) (s : _103145 -> Prop) (x : _103145) : (term204 _103145 a s x) = (term205 _103145 a s x).
Proof. exact (@lem17160 (x = a) (s x)). Qed.
Lemma lem4293625 {_103141 _103145 : Type'} (t : type1470 _103141 _103145) (x : _103145) (y : _103141) : (term206 _103141 _103145 t x y) = (term206 _103141 _103145 t x y).
Proof. exact (eq_refl (term206 _103141 _103145 t x y)). Qed.
Lemma lem4293627 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4293628 {_103145 : Type'} (a : _103145) (s : _103145 -> Prop) (x : _103145) : (term207 _103145 a s x) = (term208 _103145 a s x).
Proof. exact (MK_COMB (@lem4293627) (@lem4293621 _103145 a s x)). Qed.
Lemma lem4293629 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : _103145) (y : _103141) : (term209 _103141 _103145 a s t x y) = (term210 _103141 _103145 a s t x y).
Proof. exact (MK_COMB (@lem4293628 _103145 a s x) (@lem4293625 _103141 _103145 t x y)). Qed.
Lemma lem4293630 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : _103145) (y : _103141) : (term211 _103141 _103145 a s t x y) = (term209 _103141 _103145 a s t x y).
Proof. exact (@lem17045 (term82 _103145 a s x) (t x y)). Qed.
Lemma lem4293631 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : _103145) (y : _103141) : (term211 _103141 _103145 a s t x y) = (term210 _103141 _103145 a s t x y).
Proof. exact (TRANS (@lem4293630 _103141 _103145 a s t x y) (@lem4293629 _103141 _103145 a s t x y)). Qed.
Lemma lem4293635 {_103141 _103145 : Type'} (x : prod _103145 _103141) (x' : _103145) (y : _103141) : (term212 _103141 _103145 x x' y) = (term212 _103141 _103145 x x' y).
Proof. exact (eq_refl (term212 _103141 _103145 x x' y)). Qed.
Lemma lem4293637 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4293638 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : _103145) (y : _103141) : (term213 _103141 _103145 a s t x y) = (term214 _103141 _103145 a s t x y).
Proof. exact (MK_COMB (@lem4293637) (@lem4293631 _103141 _103145 a s t x y)). Qed.
Lemma lem4293639 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) : (term215 _103141 _103145 a s t x x' y) = (term216 _103141 _103145 a s t x x' y).
Proof. exact (MK_COMB (@lem4293638 _103141 _103145 a s t x' y) (@lem4293635 _103141 _103145 x x' y)). Qed.
Lemma lem4293640 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) : (term217 _103141 _103145 a s t x x' y) = (term215 _103141 _103145 a s t x x' y).
Proof. exact (@lem17045 (term86 _103141 _103145 a s t x' y) (x = (@pair _103145 _103141 x' y))). Qed.
Lemma lem4293641 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) : (term217 _103141 _103145 a s t x x' y) = (term216 _103141 _103145 a s t x x' y).
Proof. exact (TRANS (@lem4293640 _103141 _103145 a s t x x' y) (@lem4293639 _103141 _103145 a s t x x' y)). Qed.
Lemma lem4293644 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) : (term100 _103141 _103145 a s t x x' y) = (term100 _103141 _103145 a s t x x' y).
Proof. exact (eq_refl (term100 _103141 _103145 a s t x x' y)). Qed.
Lemma lem4293645 {_103141 : Type'} (P : _103141 -> Prop) : (term218 _103141 P) = (term219 _103141 P).
Proof. exact (@lem18394 _103141 P). Qed.
Lemma lem4293646 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) : (term220 _103141 _103145 a s t x x') = (term221 _103141 _103145 a s t x x').
Proof. exact (@lem4293645 _103141 (term102 _103141 _103145 a s t x x')). Qed.
Lemma lem4293647 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) : (term222 _103141 _103145 a s t x x' y) = (term100 _103141 _103145 a s t x x' y).
Proof. exact (eq_refl (term222 _103141 _103145 a s t x x' y)). Qed.
Lemma lem4293648 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4293649 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) : (term223 _103141 _103145 a s t x x' y) = (term217 _103141 _103145 a s t x x' y).
Proof. exact (MK_COMB (@lem4293648) (@lem4293647 _103141 _103145 a s t x x' y)). Qed.
Lemma lem4293650 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) : (term223 _103141 _103145 a s t x x' y) = (term216 _103141 _103145 a s t x x' y).
Proof. exact (TRANS (@lem4293649 _103141 _103145 a s t x x' y) (@lem4293641 _103141 _103145 a s t x x' y)). Qed.
Lemma lem4293651 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) : (term224 _103141 _103145 a s t x x') = (term225 _103141 _103145 a s t x x').
Proof. exact (fun_ext (fun y : _103141 => @lem4293650 _103141 _103145 a s t x x' y)). Qed.
Lemma lem4293652 {_103141 : Type'} : (@all _103141) = (@all _103141).
Proof. exact (eq_refl (@all _103141)). Qed.
Lemma lem4293653 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) : (term221 _103141 _103145 a s t x x') = (term226 _103141 _103145 a s t x x').
Proof. exact (MK_COMB (@lem4293652 _103141) (@lem4293651 _103141 _103145 a s t x x')). Qed.
Lemma lem4293654 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) : (term220 _103141 _103145 a s t x x') = (term226 _103141 _103145 a s t x x').
Proof. exact (TRANS (@lem4293646 _103141 _103145 a s t x x') (@lem4293653 _103141 _103145 a s t x x')). Qed.
Lemma lem4293655 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) : (term102 _103141 _103145 a s t x x') = (term102 _103141 _103145 a s t x x').
Proof. exact (fun_ext (fun y : _103141 => @lem4293644 _103141 _103145 a s t x x' y)). Qed.
Lemma lem4293656 {_103141 : Type'} : (@ex _103141) = (@ex _103141).
Proof. exact (eq_refl (@ex _103141)). Qed.
Lemma lem4293657 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) : (term104 _103141 _103145 a s t x x') = (term104 _103141 _103145 a s t x x').
Proof. exact (MK_COMB (@lem4293656 _103141) (@lem4293655 _103141 _103145 a s t x x')). Qed.
Lemma lem4293658 {_103145 : Type'} (P : _103145 -> Prop) : (term218 _103145 P) = (term219 _103145 P).
Proof. exact (@lem18394 _103145 P). Qed.
Lemma lem4293659 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term227 _103141 _103145 a s t x) = (term228 _103141 _103145 a s t x).
Proof. exact (@lem4293658 _103145 (term106 _103141 _103145 a s t x)). Qed.
Lemma lem4293660 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) : (term229 _103141 _103145 a s t x x') = (term104 _103141 _103145 a s t x x').
Proof. exact (eq_refl (term229 _103141 _103145 a s t x x')). Qed.
Lemma lem4293661 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4293662 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) : (term230 _103141 _103145 a s t x x') = (term220 _103141 _103145 a s t x x').
Proof. exact (MK_COMB (@lem4293661) (@lem4293660 _103141 _103145 a s t x x')). Qed.
Lemma lem4293663 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) : (term230 _103141 _103145 a s t x x') = (term226 _103141 _103145 a s t x x').
Proof. exact (TRANS (@lem4293662 _103141 _103145 a s t x x') (@lem4293654 _103141 _103145 a s t x x')). Qed.
Lemma lem4293664 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term231 _103141 _103145 a s t x) = (term232 _103141 _103145 a s t x).
Proof. exact (fun_ext (fun x' : _103145 => @lem4293663 _103141 _103145 a s t x x')). Qed.
Lemma lem4293665 {_103145 : Type'} : (@all _103145) = (@all _103145).
Proof. exact (eq_refl (@all _103145)). Qed.
Lemma lem4293666 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term228 _103141 _103145 a s t x) = (term233 _103141 _103145 a s t x).
Proof. exact (MK_COMB (@lem4293665 _103145) (@lem4293664 _103141 _103145 a s t x)). Qed.
Lemma lem4293667 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term227 _103141 _103145 a s t x) = (term233 _103141 _103145 a s t x).
Proof. exact (TRANS (@lem4293659 _103141 _103145 a s t x) (@lem4293666 _103141 _103145 a s t x)). Qed.
Lemma lem4293668 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term106 _103141 _103145 a s t x) = (term106 _103141 _103145 a s t x).
Proof. exact (fun_ext (fun x' : _103145 => @lem4293657 _103141 _103145 a s t x x')). Qed.
Lemma lem4293669 {_103145 : Type'} : (@ex _103145) = (@ex _103145).
Proof. exact (eq_refl (@ex _103145)). Qed.
Lemma lem4293670 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term107 _103141 _103145 a s t x) = (term107 _103141 _103145 a s t x).
Proof. exact (MK_COMB (@lem4293669 _103145) (@lem4293668 _103141 _103145 a s t x)). Qed.
Lemma lem4293679 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : _103145) (y : _103141) : (term234 _103141 _103145 s t x y) = (term235 _103141 _103145 s t x y).
Proof. exact (@lem17045 (s x) (t x y)). Qed.
Lemma lem4293683 {_103141 _103145 : Type'} (x : prod _103145 _103141) (x' : _103145) (y : _103141) : (term212 _103141 _103145 x x' y) = (term212 _103141 _103145 x x' y).
Proof. exact (eq_refl (term212 _103141 _103145 x x' y)). Qed.
Lemma lem4293685 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4293686 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : _103145) (y : _103141) : (term236 _103141 _103145 s t x y) = (term237 _103141 _103145 s t x y).
Proof. exact (MK_COMB (@lem4293685) (@lem4293679 _103141 _103145 s t x y)). Qed.
Lemma lem4293687 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) : (term238 _103141 _103145 s t x x' y) = (term239 _103141 _103145 s t x x' y).
Proof. exact (MK_COMB (@lem4293686 _103141 _103145 s t x' y) (@lem4293683 _103141 _103145 x x' y)). Qed.
Lemma lem4293688 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) : (term240 _103141 _103145 s t x x' y) = (term238 _103141 _103145 s t x x' y).
Proof. exact (@lem17045 (term137 _103141 _103145 s t x' y) (x = (@pair _103145 _103141 x' y))). Qed.
Lemma lem4293689 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) : (term240 _103141 _103145 s t x x' y) = (term239 _103141 _103145 s t x x' y).
Proof. exact (TRANS (@lem4293688 _103141 _103145 s t x x' y) (@lem4293687 _103141 _103145 s t x x' y)). Qed.
Lemma lem4293692 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) : (term150 _103141 _103145 s t x x' y) = (term150 _103141 _103145 s t x x' y).
Proof. exact (eq_refl (term150 _103141 _103145 s t x x' y)). Qed.
Lemma lem4293693 {_103141 : Type'} (P : _103141 -> Prop) : (term218 _103141 P) = (term219 _103141 P).
Proof. exact (@lem18394 _103141 P). Qed.
Lemma lem4293694 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) : (term241 _103141 _103145 s t x x') = (term242 _103141 _103145 s t x x').
Proof. exact (@lem4293693 _103141 (term152 _103141 _103145 s t x x')). Qed.
Lemma lem4293695 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) : (term243 _103141 _103145 s t x x' y) = (term150 _103141 _103145 s t x x' y).
Proof. exact (eq_refl (term243 _103141 _103145 s t x x' y)). Qed.
Lemma lem4293696 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4293697 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) : (term244 _103141 _103145 s t x x' y) = (term240 _103141 _103145 s t x x' y).
Proof. exact (MK_COMB (@lem4293696) (@lem4293695 _103141 _103145 s t x x' y)). Qed.
Lemma lem4293698 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) : (term244 _103141 _103145 s t x x' y) = (term239 _103141 _103145 s t x x' y).
Proof. exact (TRANS (@lem4293697 _103141 _103145 s t x x' y) (@lem4293689 _103141 _103145 s t x x' y)). Qed.
Lemma lem4293699 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) : (term245 _103141 _103145 s t x x') = (term246 _103141 _103145 s t x x').
Proof. exact (fun_ext (fun y : _103141 => @lem4293698 _103141 _103145 s t x x' y)). Qed.
Lemma lem4293700 {_103141 : Type'} : (@all _103141) = (@all _103141).
Proof. exact (eq_refl (@all _103141)). Qed.
Lemma lem4293701 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) : (term242 _103141 _103145 s t x x') = (term247 _103141 _103145 s t x x').
Proof. exact (MK_COMB (@lem4293700 _103141) (@lem4293699 _103141 _103145 s t x x')). Qed.
Lemma lem4293702 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) : (term241 _103141 _103145 s t x x') = (term247 _103141 _103145 s t x x').
Proof. exact (TRANS (@lem4293694 _103141 _103145 s t x x') (@lem4293701 _103141 _103145 s t x x')). Qed.
Lemma lem4293703 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) : (term152 _103141 _103145 s t x x') = (term152 _103141 _103145 s t x x').
Proof. exact (fun_ext (fun y : _103141 => @lem4293692 _103141 _103145 s t x x' y)). Qed.
Lemma lem4293704 {_103141 : Type'} : (@ex _103141) = (@ex _103141).
Proof. exact (eq_refl (@ex _103141)). Qed.
Lemma lem4293705 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) : (term154 _103141 _103145 s t x x') = (term154 _103141 _103145 s t x x').
Proof. exact (MK_COMB (@lem4293704 _103141) (@lem4293703 _103141 _103145 s t x x')). Qed.
Lemma lem4293706 {_103145 : Type'} (P : _103145 -> Prop) : (term218 _103145 P) = (term219 _103145 P).
Proof. exact (@lem18394 _103145 P). Qed.
Lemma lem4293707 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term248 _103141 _103145 s t x) = (term249 _103141 _103145 s t x).
Proof. exact (@lem4293706 _103145 (term156 _103141 _103145 s t x)). Qed.
Lemma lem4293708 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) : (term250 _103141 _103145 s t x x') = (term154 _103141 _103145 s t x x').
Proof. exact (eq_refl (term250 _103141 _103145 s t x x')). Qed.
Lemma lem4293709 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4293710 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) : (term251 _103141 _103145 s t x x') = (term241 _103141 _103145 s t x x').
Proof. exact (MK_COMB (@lem4293709) (@lem4293708 _103141 _103145 s t x x')). Qed.
Lemma lem4293711 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) : (term251 _103141 _103145 s t x x') = (term247 _103141 _103145 s t x x').
Proof. exact (TRANS (@lem4293710 _103141 _103145 s t x x') (@lem4293702 _103141 _103145 s t x x')). Qed.
Lemma lem4293712 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term252 _103141 _103145 s t x) = (term253 _103141 _103145 s t x).
Proof. exact (fun_ext (fun x' : _103145 => @lem4293711 _103141 _103145 s t x x')). Qed.
Lemma lem4293713 {_103145 : Type'} : (@all _103145) = (@all _103145).
Proof. exact (eq_refl (@all _103145)). Qed.
Lemma lem4293714 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term249 _103141 _103145 s t x) = (term254 _103141 _103145 s t x).
Proof. exact (MK_COMB (@lem4293713 _103145) (@lem4293712 _103141 _103145 s t x)). Qed.
Lemma lem4293715 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term248 _103141 _103145 s t x) = (term254 _103141 _103145 s t x).
Proof. exact (TRANS (@lem4293707 _103141 _103145 s t x) (@lem4293714 _103141 _103145 s t x)). Qed.
Lemma lem4293716 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term156 _103141 _103145 s t x) = (term156 _103141 _103145 s t x).
Proof. exact (fun_ext (fun x' : _103145 => @lem4293705 _103141 _103145 s t x x')). Qed.
Lemma lem4293717 {_103145 : Type'} : (@ex _103145) = (@ex _103145).
Proof. exact (eq_refl (@ex _103145)). Qed.
Lemma lem4293718 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term157 _103141 _103145 s t x) = (term157 _103141 _103145 s t x).
Proof. exact (MK_COMB (@lem4293717 _103145) (@lem4293716 _103141 _103145 s t x)). Qed.
Lemma lem4293727 {_103141 _103145 : Type'} (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (x' : _103141) : (term255 _103141 _103145 x t a x') = (term256 _103141 _103145 x t a x').
Proof. exact (@lem17045 (x = (@pair _103145 _103141 a x')) (t a x')). Qed.
Lemma lem4293730 {_103141 _103145 : Type'} (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (x' : _103141) : (term174 _103141 _103145 x t a x') = (term174 _103141 _103145 x t a x').
Proof. exact (eq_refl (term174 _103141 _103145 x t a x')). Qed.
Lemma lem4293731 {_103141 : Type'} (P : _103141 -> Prop) : (term218 _103141 P) = (term219 _103141 P).
Proof. exact (@lem18394 _103141 P). Qed.
Lemma lem4293732 {_103141 _103145 : Type'} (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term257 _103141 _103145 x t a) = (term258 _103141 _103145 x t a).
Proof. exact (@lem4293731 _103141 (term176 _103141 _103145 x t a)). Qed.
Lemma lem4293733 {_103141 _103145 : Type'} (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (x' : _103141) : (term259 _103141 _103145 x t a x') = (term174 _103141 _103145 x t a x').
Proof. exact (eq_refl (term259 _103141 _103145 x t a x')). Qed.
Lemma lem4293734 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4293735 {_103141 _103145 : Type'} (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (x' : _103141) : (term260 _103141 _103145 x t a x') = (term255 _103141 _103145 x t a x').
Proof. exact (MK_COMB (@lem4293734) (@lem4293733 _103141 _103145 x t a x')). Qed.
Lemma lem4293736 {_103141 _103145 : Type'} (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (x' : _103141) : (term260 _103141 _103145 x t a x') = (term256 _103141 _103145 x t a x').
Proof. exact (TRANS (@lem4293735 _103141 _103145 x t a x') (@lem4293727 _103141 _103145 x t a x')). Qed.
Lemma lem4293737 {_103141 _103145 : Type'} (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term261 _103141 _103145 x t a) = (term262 _103141 _103145 x t a).
Proof. exact (fun_ext (fun x' : _103141 => @lem4293736 _103141 _103145 x t a x')). Qed.
Lemma lem4293738 {_103141 : Type'} : (@all _103141) = (@all _103141).
Proof. exact (eq_refl (@all _103141)). Qed.
Lemma lem4293739 {_103141 _103145 : Type'} (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term258 _103141 _103145 x t a) = (term263 _103141 _103145 x t a).
Proof. exact (MK_COMB (@lem4293738 _103141) (@lem4293737 _103141 _103145 x t a)). Qed.
Lemma lem4293740 {_103141 _103145 : Type'} (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term257 _103141 _103145 x t a) = (term263 _103141 _103145 x t a).
Proof. exact (TRANS (@lem4293732 _103141 _103145 x t a) (@lem4293739 _103141 _103145 x t a)). Qed.
Lemma lem4293741 {_103141 _103145 : Type'} (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term176 _103141 _103145 x t a) = (term176 _103141 _103145 x t a).
Proof. exact (fun_ext (fun x' : _103141 => @lem4293730 _103141 _103145 x t a x')). Qed.
Lemma lem4293742 {_103141 : Type'} : (@ex _103141) = (@ex _103141).
Proof. exact (eq_refl (@ex _103141)). Qed.
Lemma lem4293743 {_103141 _103145 : Type'} (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term177 _103141 _103145 x t a) = (term177 _103141 _103145 x t a).
Proof. exact (MK_COMB (@lem4293742 _103141) (@lem4293741 _103141 _103145 x t a)). Qed.
Lemma lem4293744 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4293745 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term264 _103141 _103145 s t x) = (term265 _103141 _103145 s t x).
Proof. exact (MK_COMB (@lem4293744) (@lem4293715 _103141 _103145 s t x)). Qed.
Lemma lem4293746 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term266 _103141 _103145 s x t a) = (term267 _103141 _103145 s x t a).
Proof. exact (MK_COMB (@lem4293745 _103141 _103145 s t x) (@lem4293740 _103141 _103145 x t a)). Qed.
Lemma lem4293747 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term268 _103141 _103145 s x t a) = (term266 _103141 _103145 s x t a).
Proof. exact (@lem17160 (term157 _103141 _103145 s t x) (term177 _103141 _103145 x t a)). Qed.
Lemma lem4293748 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term268 _103141 _103145 s x t a) = (term267 _103141 _103145 s x t a).
Proof. exact (TRANS (@lem4293747 _103141 _103145 s x t a) (@lem4293746 _103141 _103145 s x t a)). Qed.
Lemma lem4293749 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4293750 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term159 _103141 _103145 s t x) = (term159 _103141 _103145 s t x).
Proof. exact (MK_COMB (@lem4293749) (@lem4293718 _103141 _103145 s t x)). Qed.
Lemma lem4293751 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term178 _103141 _103145 s x t a) = (term178 _103141 _103145 s x t a).
Proof. exact (MK_COMB (@lem4293750 _103141 _103145 s t x) (@lem4293743 _103141 _103145 x t a)). Qed.
Lemma lem4293752 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4293753 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term269 _103141 _103145 a s t x) = (term270 _103141 _103145 a s t x).
Proof. exact (MK_COMB (@lem4293752) (@lem4293667 _103141 _103145 a s t x)). Qed.
Lemma lem4293754 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term271 _103141 _103145 s x t a) = (term272 _103141 _103145 s x t a).
Proof. exact (MK_COMB (@lem4293753 _103141 _103145 a s t x) (@lem4293751 _103141 _103145 s x t a)). Qed.
Lemma lem4293755 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4293756 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term273 _103141 _103145 a s t x) = (term273 _103141 _103145 a s t x).
Proof. exact (MK_COMB (@lem4293755) (@lem4293670 _103141 _103145 a s t x)). Qed.
Lemma lem4293757 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term274 _103141 _103145 s x t a) = (term275 _103141 _103145 s x t a).
Proof. exact (MK_COMB (@lem4293756 _103141 _103145 a s t x) (@lem4293748 _103141 _103145 s x t a)). Qed.
Lemma lem4293758 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4293759 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term276 _103141 _103145 s x t a) = (term277 _103141 _103145 s x t a).
Proof. exact (MK_COMB (@lem4293758) (@lem4293757 _103141 _103145 s x t a)). Qed.
Lemma lem4293760 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term278 _103141 _103145 s x t a) = (term279 _103141 _103145 s x t a).
Proof. exact (MK_COMB (@lem4293759 _103141 _103145 s x t a) (@lem4293754 _103141 _103145 s x t a)). Qed.
Lemma lem4293761 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term203 _103141 _103145 s x t a) = (term278 _103141 _103145 s x t a).
Proof. exact (@lem17646 (term107 _103141 _103145 a s t x) (term178 _103141 _103145 s x t a)). Qed.
Lemma lem4293762 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term203 _103141 _103145 s x t a) = (term279 _103141 _103145 s x t a).
Proof. exact (TRANS (@lem4293761 _103141 _103145 s x t a) (@lem4293760 _103141 _103145 s x t a)). Qed.
Lemma lem4294069 {A : Type'} (P : A -> Prop) (Q : Prop) : (term280 A P Q) = (term281 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4294070 {_103145 : Type'} (P : _103145 -> Prop) (Q : Prop) : (term280 _103145 P Q) = (term281 _103145 P Q).
Proof. exact (@lem4294069 _103145 P Q). Qed.
Lemma lem4294071 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term282 _103141 _103145 s x t a) = (term283 _103141 _103145 s x t a).
Proof. exact (@lem4294070 _103145 (term106 _103141 _103145 a s t x) (term267 _103141 _103145 s x t a)). Qed.
Lemma lem4294072 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) : (term229 _103141 _103145 a s t x x') = (term104 _103141 _103145 a s t x x').
Proof. exact (eq_refl (term229 _103141 _103145 a s t x x')). Qed.
Lemma lem4294073 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term284 _103141 _103145 a s t x) = (term106 _103141 _103145 a s t x).
Proof. exact (fun_ext (fun x' : _103145 => @lem4294072 _103141 _103145 a s t x x')). Qed.
Lemma lem4294074 {_103145 : Type'} : (@ex _103145) = (@ex _103145).
Proof. exact (eq_refl (@ex _103145)). Qed.
Lemma lem4294075 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term285 _103141 _103145 a s t x) = (term107 _103141 _103145 a s t x).
Proof. exact (MK_COMB (@lem4294074 _103145) (@lem4294073 _103141 _103145 a s t x)). Qed.
Lemma lem4294076 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4294077 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term286 _103141 _103145 a s t x) = (term273 _103141 _103145 a s t x).
Proof. exact (MK_COMB (@lem4294076) (@lem4294075 _103141 _103145 a s t x)). Qed.
Lemma lem4294078 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term267 _103141 _103145 s x t a) = (term267 _103141 _103145 s x t a).
Proof. exact (eq_refl (term267 _103141 _103145 s x t a)). Qed.
Lemma lem4294079 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term282 _103141 _103145 s x t a) = (term275 _103141 _103145 s x t a).
Proof. exact (MK_COMB (@lem4294077 _103141 _103145 a s t x) (@lem4294078 _103141 _103145 s x t a)). Qed.
Lemma lem4294080 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4294081 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term287 _103141 _103145 s x t a) = (term288 _103141 _103145 s x t a).
Proof. exact (MK_COMB (@lem4294080) (@lem4294079 _103141 _103145 s x t a)). Qed.
Lemma lem4294082 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) : (term229 _103141 _103145 a s t x x') = (term104 _103141 _103145 a s t x x').
Proof. exact (eq_refl (term229 _103141 _103145 a s t x x')). Qed.
Lemma lem4294083 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4294084 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) : (term289 _103141 _103145 a s t x x') = (term290 _103141 _103145 a s t x x').
Proof. exact (MK_COMB (@lem4294083) (@lem4294082 _103141 _103145 a s t x x')). Qed.
Lemma lem4294085 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term267 _103141 _103145 s x t a) = (term267 _103141 _103145 s x t a).
Proof. exact (eq_refl (term267 _103141 _103145 s x t a)). Qed.
Lemma lem4294086 {_103141 _103145 : Type'} (x : _103145) (s : _103145 -> Prop) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term291 _103141 _103145 x s x' t a) = (term292 _103141 _103145 x s x' t a).
Proof. exact (MK_COMB (@lem4294084 _103141 _103145 a s t x' x) (@lem4294085 _103141 _103145 s x' t a)). Qed.
Lemma lem4294087 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term293 _103141 _103145 s x t a) = (term294 _103141 _103145 s x t a).
Proof. exact (fun_ext (fun x' : _103145 => @lem4294086 _103141 _103145 x' s x t a)). Qed.
Lemma lem4294088 {_103145 : Type'} : (@ex _103145) = (@ex _103145).
Proof. exact (eq_refl (@ex _103145)). Qed.
Lemma lem4294089 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term283 _103141 _103145 s x t a) = (term295 _103141 _103145 s x t a).
Proof. exact (MK_COMB (@lem4294088 _103145) (@lem4294087 _103141 _103145 s x t a)). Qed.
Lemma lem4294090 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : ((term282 _103141 _103145 s x t a) = (term283 _103141 _103145 s x t a)) = ((term275 _103141 _103145 s x t a) = (term295 _103141 _103145 s x t a)).
Proof. exact (MK_COMB (@lem4294081 _103141 _103145 s x t a) (@lem4294089 _103141 _103145 s x t a)). Qed.
Lemma lem4294091 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term275 _103141 _103145 s x t a) = (term295 _103141 _103145 s x t a).
Proof. exact (EQ_MP (@lem4294090 _103141 _103145 s x t a) (@lem4294071 _103141 _103145 s x t a)). Qed.
Lemma lem4294093 {A : Type'} (P : A -> Prop) (Q : Prop) : (term280 A P Q) = (term281 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4294094 {_103141 : Type'} (P : _103141 -> Prop) (Q : Prop) : (term280 _103141 P Q) = (term281 _103141 P Q).
Proof. exact (@lem4294093 _103141 P Q). Qed.
Lemma lem4294095 {_103141 _103145 : Type'} (x : _103145) (s : _103145 -> Prop) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term296 _103141 _103145 x s x' t a) = (term297 _103141 _103145 x s x' t a).
Proof. exact (@lem4294094 _103141 (term102 _103141 _103145 a s t x' x) (term267 _103141 _103145 s x' t a)). Qed.
Lemma lem4294096 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) : (term222 _103141 _103145 a s t x x' y) = (term100 _103141 _103145 a s t x x' y).
Proof. exact (eq_refl (term222 _103141 _103145 a s t x x' y)). Qed.
Lemma lem4294097 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) : (term298 _103141 _103145 a s t x x') = (term102 _103141 _103145 a s t x x').
Proof. exact (fun_ext (fun y : _103141 => @lem4294096 _103141 _103145 a s t x x' y)). Qed.
Lemma lem4294098 {_103141 : Type'} : (@ex _103141) = (@ex _103141).
Proof. exact (eq_refl (@ex _103141)). Qed.
Lemma lem4294099 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) : (term299 _103141 _103145 a s t x x') = (term104 _103141 _103145 a s t x x').
Proof. exact (MK_COMB (@lem4294098 _103141) (@lem4294097 _103141 _103145 a s t x x')). Qed.
Lemma lem4294100 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4294101 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) : (term300 _103141 _103145 a s t x x') = (term290 _103141 _103145 a s t x x').
Proof. exact (MK_COMB (@lem4294100) (@lem4294099 _103141 _103145 a s t x x')). Qed.
Lemma lem4294102 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term267 _103141 _103145 s x t a) = (term267 _103141 _103145 s x t a).
Proof. exact (eq_refl (term267 _103141 _103145 s x t a)). Qed.
Lemma lem4294103 {_103141 _103145 : Type'} (x : _103145) (s : _103145 -> Prop) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term296 _103141 _103145 x s x' t a) = (term292 _103141 _103145 x s x' t a).
Proof. exact (MK_COMB (@lem4294101 _103141 _103145 a s t x' x) (@lem4294102 _103141 _103145 s x' t a)). Qed.
Lemma lem4294104 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4294105 {_103141 _103145 : Type'} (x : _103145) (s : _103145 -> Prop) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term301 _103141 _103145 x s x' t a) = (term302 _103141 _103145 x s x' t a).
Proof. exact (MK_COMB (@lem4294104) (@lem4294103 _103141 _103145 x s x' t a)). Qed.
Lemma lem4294106 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) : (term222 _103141 _103145 a s t x x' y) = (term100 _103141 _103145 a s t x x' y).
Proof. exact (eq_refl (term222 _103141 _103145 a s t x x' y)). Qed.
Lemma lem4294107 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4294108 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) : (term303 _103141 _103145 a s t x x' y) = (term304 _103141 _103145 a s t x x' y).
Proof. exact (MK_COMB (@lem4294107) (@lem4294106 _103141 _103145 a s t x x' y)). Qed.
Lemma lem4294109 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term267 _103141 _103145 s x t a) = (term267 _103141 _103145 s x t a).
Proof. exact (eq_refl (term267 _103141 _103145 s x t a)). Qed.
Lemma lem4294110 {_103141 _103145 : Type'} (x : _103145) (y : _103141) (s : _103145 -> Prop) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term305 _103141 _103145 x y s x' t a) = (term306 _103141 _103145 x y s x' t a).
Proof. exact (MK_COMB (@lem4294108 _103141 _103145 a s t x' x y) (@lem4294109 _103141 _103145 s x' t a)). Qed.
Lemma lem4294111 {_103141 _103145 : Type'} (x : _103145) (s : _103145 -> Prop) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term307 _103141 _103145 x s x' t a) = (term308 _103141 _103145 x s x' t a).
Proof. exact (fun_ext (fun y : _103141 => @lem4294110 _103141 _103145 x y s x' t a)). Qed.
Lemma lem4294112 {_103141 : Type'} : (@ex _103141) = (@ex _103141).
Proof. exact (eq_refl (@ex _103141)). Qed.
Lemma lem4294113 {_103141 _103145 : Type'} (x : _103145) (s : _103145 -> Prop) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term297 _103141 _103145 x s x' t a) = (term309 _103141 _103145 x s x' t a).
Proof. exact (MK_COMB (@lem4294112 _103141) (@lem4294111 _103141 _103145 x s x' t a)). Qed.
Lemma lem4294114 {_103141 _103145 : Type'} (x : _103145) (s : _103145 -> Prop) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : ((term296 _103141 _103145 x s x' t a) = (term297 _103141 _103145 x s x' t a)) = ((term292 _103141 _103145 x s x' t a) = (term309 _103141 _103145 x s x' t a)).
Proof. exact (MK_COMB (@lem4294105 _103141 _103145 x s x' t a) (@lem4294113 _103141 _103145 x s x' t a)). Qed.
Lemma lem4294115 {_103141 _103145 : Type'} (x : _103145) (s : _103145 -> Prop) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term292 _103141 _103145 x s x' t a) = (term309 _103141 _103145 x s x' t a).
Proof. exact (EQ_MP (@lem4294114 _103141 _103145 x s x' t a) (@lem4294095 _103141 _103145 x s x' t a)). Qed.
Lemma lem4294116 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term294 _103141 _103145 s x t a) = (term310 _103141 _103145 s x t a).
Proof. exact (fun_ext (fun x' : _103145 => @lem4294115 _103141 _103145 x' s x t a)). Qed.
Lemma lem4294117 {_103145 : Type'} : (@ex _103145) = (@ex _103145).
Proof. exact (eq_refl (@ex _103145)). Qed.
Lemma lem4294118 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term295 _103141 _103145 s x t a) = (term311 _103141 _103145 s x t a).
Proof. exact (MK_COMB (@lem4294117 _103145) (@lem4294116 _103141 _103145 s x t a)). Qed.
Lemma lem4294119 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term275 _103141 _103145 s x t a) = (term311 _103141 _103145 s x t a).
Proof. exact (TRANS (@lem4294091 _103141 _103145 s x t a) (@lem4294118 _103141 _103145 s x t a)). Qed.
Lemma lem4294120 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4294121 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term277 _103141 _103145 s x t a) = (term312 _103141 _103145 s x t a).
Proof. exact (MK_COMB (@lem4294120) (@lem4294119 _103141 _103145 s x t a)). Qed.
Lemma lem4294125 {A : Type'} (P : A -> Prop) (Q : Prop) : (term313 A P Q) = (term314 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4294126 {_103145 : Type'} (P : _103145 -> Prop) (Q : Prop) : (term313 _103145 P Q) = (term314 _103145 P Q).
Proof. exact (@lem4294125 _103145 P Q). Qed.
Lemma lem4294127 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term315 _103141 _103145 s x t a) = (term316 _103141 _103145 s x t a).
Proof. exact (@lem4294126 _103145 (term156 _103141 _103145 s t x) (term177 _103141 _103145 x t a)). Qed.
Lemma lem4294128 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) : (term250 _103141 _103145 s t x x') = (term154 _103141 _103145 s t x x').
Proof. exact (eq_refl (term250 _103141 _103145 s t x x')). Qed.
Lemma lem4294129 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term317 _103141 _103145 s t x) = (term156 _103141 _103145 s t x).
Proof. exact (fun_ext (fun x' : _103145 => @lem4294128 _103141 _103145 s t x x')). Qed.
Lemma lem4294130 {_103145 : Type'} : (@ex _103145) = (@ex _103145).
Proof. exact (eq_refl (@ex _103145)). Qed.
Lemma lem4294131 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term318 _103141 _103145 s t x) = (term157 _103141 _103145 s t x).
Proof. exact (MK_COMB (@lem4294130 _103145) (@lem4294129 _103141 _103145 s t x)). Qed.
Lemma lem4294132 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4294133 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term319 _103141 _103145 s t x) = (term159 _103141 _103145 s t x).
Proof. exact (MK_COMB (@lem4294132) (@lem4294131 _103141 _103145 s t x)). Qed.
Lemma lem4294134 {_103141 _103145 : Type'} (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term177 _103141 _103145 x t a) = (term177 _103141 _103145 x t a).
Proof. exact (eq_refl (term177 _103141 _103145 x t a)). Qed.
Lemma lem4294135 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term315 _103141 _103145 s x t a) = (term178 _103141 _103145 s x t a).
Proof. exact (MK_COMB (@lem4294133 _103141 _103145 s t x) (@lem4294134 _103141 _103145 x t a)). Qed.
Lemma lem4294136 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4294137 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term320 _103141 _103145 s x t a) = (term321 _103141 _103145 s x t a).
Proof. exact (MK_COMB (@lem4294136) (@lem4294135 _103141 _103145 s x t a)). Qed.
Lemma lem4294138 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) : (term250 _103141 _103145 s t x x') = (term154 _103141 _103145 s t x x').
Proof. exact (eq_refl (term250 _103141 _103145 s t x x')). Qed.
Lemma lem4294139 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4294140 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) : (term322 _103141 _103145 s t x x') = (term323 _103141 _103145 s t x x').
Proof. exact (MK_COMB (@lem4294139) (@lem4294138 _103141 _103145 s t x x')). Qed.
Lemma lem4294141 {_103141 _103145 : Type'} (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term177 _103141 _103145 x t a) = (term177 _103141 _103145 x t a).
Proof. exact (eq_refl (term177 _103141 _103145 x t a)). Qed.
Lemma lem4294142 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : _103145) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term324 _103141 _103145 s x x' t a) = (term325 _103141 _103145 s x x' t a).
Proof. exact (MK_COMB (@lem4294140 _103141 _103145 s t x' x) (@lem4294141 _103141 _103145 x' t a)). Qed.
Lemma lem4294143 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term326 _103141 _103145 s x t a) = (term327 _103141 _103145 s x t a).
Proof. exact (fun_ext (fun x' : _103145 => @lem4294142 _103141 _103145 s x' x t a)). Qed.
Lemma lem4294144 {_103145 : Type'} : (@ex _103145) = (@ex _103145).
Proof. exact (eq_refl (@ex _103145)). Qed.
Lemma lem4294145 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term316 _103141 _103145 s x t a) = (term328 _103141 _103145 s x t a).
Proof. exact (MK_COMB (@lem4294144 _103145) (@lem4294143 _103141 _103145 s x t a)). Qed.
Lemma lem4294146 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : ((term315 _103141 _103145 s x t a) = (term316 _103141 _103145 s x t a)) = ((term178 _103141 _103145 s x t a) = (term328 _103141 _103145 s x t a)).
Proof. exact (MK_COMB (@lem4294137 _103141 _103145 s x t a) (@lem4294145 _103141 _103145 s x t a)). Qed.
Lemma lem4294147 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term178 _103141 _103145 s x t a) = (term328 _103141 _103145 s x t a).
Proof. exact (EQ_MP (@lem4294146 _103141 _103145 s x t a) (@lem4294127 _103141 _103145 s x t a)). Qed.
Lemma lem4294149 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term329 A P Q) = (term330 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4294150 {_103141 : Type'} (P : _103141 -> Prop) (Q : _103141 -> Prop) : (term329 _103141 P Q) = (term330 _103141 P Q).
Proof. exact (@lem4294149 _103141 P Q). Qed.
Lemma lem4294151 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : _103145) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term331 _103141 _103145 s x x' t a) = (term332 _103141 _103145 s x x' t a).
Proof. exact (@lem4294150 _103141 (term152 _103141 _103145 s t x' x) (term176 _103141 _103145 x' t a)). Qed.
Lemma lem4294152 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) : (term243 _103141 _103145 s t x x' y) = (term150 _103141 _103145 s t x x' y).
Proof. exact (eq_refl (term243 _103141 _103145 s t x x' y)). Qed.
Lemma lem4294153 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) : (term333 _103141 _103145 s t x x') = (term152 _103141 _103145 s t x x').
Proof. exact (fun_ext (fun y : _103141 => @lem4294152 _103141 _103145 s t x x' y)). Qed.
Lemma lem4294154 {_103141 : Type'} : (@ex _103141) = (@ex _103141).
Proof. exact (eq_refl (@ex _103141)). Qed.
Lemma lem4294155 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) : (term334 _103141 _103145 s t x x') = (term154 _103141 _103145 s t x x').
Proof. exact (MK_COMB (@lem4294154 _103141) (@lem4294153 _103141 _103145 s t x x')). Qed.
Lemma lem4294156 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4294157 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) : (term335 _103141 _103145 s t x x') = (term323 _103141 _103145 s t x x').
Proof. exact (MK_COMB (@lem4294156) (@lem4294155 _103141 _103145 s t x x')). Qed.
Lemma lem4294158 {_103141 _103145 : Type'} (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) : (term259 _103141 _103145 x t a y) = (term174 _103141 _103145 x t a y).
Proof. exact (eq_refl (term259 _103141 _103145 x t a y)). Qed.
Lemma lem4294159 {_103141 _103145 : Type'} (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term336 _103141 _103145 x t a) = (term176 _103141 _103145 x t a).
Proof. exact (fun_ext (fun y : _103141 => @lem4294158 _103141 _103145 x t a y)). Qed.
Lemma lem4294160 {_103141 : Type'} : (@ex _103141) = (@ex _103141).
Proof. exact (eq_refl (@ex _103141)). Qed.
Lemma lem4294161 {_103141 _103145 : Type'} (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term337 _103141 _103145 x t a) = (term177 _103141 _103145 x t a).
Proof. exact (MK_COMB (@lem4294160 _103141) (@lem4294159 _103141 _103145 x t a)). Qed.
Lemma lem4294162 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : _103145) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term331 _103141 _103145 s x x' t a) = (term325 _103141 _103145 s x x' t a).
Proof. exact (MK_COMB (@lem4294157 _103141 _103145 s t x' x) (@lem4294161 _103141 _103145 x' t a)). Qed.
Lemma lem4294163 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4294164 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : _103145) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term338 _103141 _103145 s x x' t a) = (term339 _103141 _103145 s x x' t a).
Proof. exact (MK_COMB (@lem4294163) (@lem4294162 _103141 _103145 s x x' t a)). Qed.
Lemma lem4294165 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) : (term243 _103141 _103145 s t x x' y) = (term150 _103141 _103145 s t x x' y).
Proof. exact (eq_refl (term243 _103141 _103145 s t x x' y)). Qed.
Lemma lem4294166 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4294167 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) : (term340 _103141 _103145 s t x x' y) = (term341 _103141 _103145 s t x x' y).
Proof. exact (MK_COMB (@lem4294166) (@lem4294165 _103141 _103145 s t x x' y)). Qed.
Lemma lem4294168 {_103141 _103145 : Type'} (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) : (term259 _103141 _103145 x t a y) = (term174 _103141 _103145 x t a y).
Proof. exact (eq_refl (term259 _103141 _103145 x t a y)). Qed.
Lemma lem4294169 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : _103145) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) : (term342 _103141 _103145 s x x' t a y) = (term343 _103141 _103145 s x x' t a y).
Proof. exact (MK_COMB (@lem4294167 _103141 _103145 s t x' x y) (@lem4294168 _103141 _103145 x' t a y)). Qed.
Lemma lem4294170 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : _103145) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term344 _103141 _103145 s x x' t a) = (term345 _103141 _103145 s x x' t a).
Proof. exact (fun_ext (fun y : _103141 => @lem4294169 _103141 _103145 s x x' t a y)). Qed.
Lemma lem4294171 {_103141 : Type'} : (@ex _103141) = (@ex _103141).
Proof. exact (eq_refl (@ex _103141)). Qed.
Lemma lem4294172 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : _103145) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term332 _103141 _103145 s x x' t a) = (term346 _103141 _103145 s x x' t a).
Proof. exact (MK_COMB (@lem4294171 _103141) (@lem4294170 _103141 _103145 s x x' t a)). Qed.
Lemma lem4294173 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : _103145) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : ((term331 _103141 _103145 s x x' t a) = (term332 _103141 _103145 s x x' t a)) = ((term325 _103141 _103145 s x x' t a) = (term346 _103141 _103145 s x x' t a)).
Proof. exact (MK_COMB (@lem4294164 _103141 _103145 s x x' t a) (@lem4294172 _103141 _103145 s x x' t a)). Qed.
Lemma lem4294174 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : _103145) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term325 _103141 _103145 s x x' t a) = (term346 _103141 _103145 s x x' t a).
Proof. exact (EQ_MP (@lem4294173 _103141 _103145 s x x' t a) (@lem4294151 _103141 _103145 s x x' t a)). Qed.
Lemma lem4294177 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : _103145) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term347 _103141 _103145 s x x' t a) = (term347 _103141 _103145 s x x' t a).
Proof. exact (eq_refl (term347 _103141 _103145 s x x' t a)). Qed.
Lemma lem4294178 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : _103145) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term347 _103141 _103145 s x x' t a) = ((term325 _103141 _103145 s x x' t a) = (term346 _103141 _103145 s x x' t a)).
Proof. exact (eq_refl (term347 _103141 _103145 s x x' t a)). Qed.
Lemma lem4294179 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : _103145) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term348 _103141 _103145 s x x' t a) = (term348 _103141 _103145 s x x' t a).
Proof. exact (eq_refl (term348 _103141 _103145 s x x' t a)). Qed.
Lemma lem4294180 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : _103145) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : ((term347 _103141 _103145 s x x' t a) = (term347 _103141 _103145 s x x' t a)) = ((term347 _103141 _103145 s x x' t a) = ((term325 _103141 _103145 s x x' t a) = (term346 _103141 _103145 s x x' t a))).
Proof. exact (MK_COMB (@lem4294179 _103141 _103145 s x x' t a) (@lem4294178 _103141 _103145 s x x' t a)). Qed.
Lemma lem4294181 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : _103145) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term347 _103141 _103145 s x x' t a) = ((term325 _103141 _103145 s x x' t a) = (term346 _103141 _103145 s x x' t a)).
Proof. exact (eq_refl (term347 _103141 _103145 s x x' t a)). Qed.
Lemma lem4294182 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4294183 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : _103145) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term348 _103141 _103145 s x x' t a) = (term349 _103141 _103145 s x x' t a).
Proof. exact (MK_COMB (@lem4294182) (@lem4294181 _103141 _103145 s x x' t a)). Qed.
Lemma lem4294184 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : _103145) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : ((term325 _103141 _103145 s x x' t a) = (term346 _103141 _103145 s x x' t a)) = ((term325 _103141 _103145 s x x' t a) = (term346 _103141 _103145 s x x' t a)).
Proof. exact (eq_refl ((term325 _103141 _103145 s x x' t a) = (term346 _103141 _103145 s x x' t a))). Qed.
Lemma lem4294185 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : _103145) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : ((term347 _103141 _103145 s x x' t a) = ((term325 _103141 _103145 s x x' t a) = (term346 _103141 _103145 s x x' t a))) = (((term325 _103141 _103145 s x x' t a) = (term346 _103141 _103145 s x x' t a)) = ((term325 _103141 _103145 s x x' t a) = (term346 _103141 _103145 s x x' t a))).
Proof. exact (MK_COMB (@lem4294183 _103141 _103145 s x x' t a) (@lem4294184 _103141 _103145 s x x' t a)). Qed.
Lemma lem4294186 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : _103145) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : ((term347 _103141 _103145 s x x' t a) = (term347 _103141 _103145 s x x' t a)) = (((term325 _103141 _103145 s x x' t a) = (term346 _103141 _103145 s x x' t a)) = ((term325 _103141 _103145 s x x' t a) = (term346 _103141 _103145 s x x' t a))).
Proof. exact (TRANS (@lem4294180 _103141 _103145 s x x' t a) (@lem4294185 _103141 _103145 s x x' t a)). Qed.
Lemma lem4294187 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : _103145) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : ((term325 _103141 _103145 s x x' t a) = (term346 _103141 _103145 s x x' t a)) = ((term325 _103141 _103145 s x x' t a) = (term346 _103141 _103145 s x x' t a)).
Proof. exact (EQ_MP (@lem4294186 _103141 _103145 s x x' t a) (@lem4294177 _103141 _103145 s x x' t a)). Qed.
Lemma lem4294188 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : _103145) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term325 _103141 _103145 s x x' t a) = (term346 _103141 _103145 s x x' t a).
Proof. exact (EQ_MP (@lem4294187 _103141 _103145 s x x' t a) (@lem4294174 _103141 _103145 s x x' t a)). Qed.
Lemma lem4294189 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term327 _103141 _103145 s x t a) = (term350 _103141 _103145 s x t a).
Proof. exact (fun_ext (fun x' : _103145 => @lem4294188 _103141 _103145 s x' x t a)). Qed.
Lemma lem4294190 {_103145 : Type'} : (@ex _103145) = (@ex _103145).
Proof. exact (eq_refl (@ex _103145)). Qed.
Lemma lem4294191 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term328 _103141 _103145 s x t a) = (term351 _103141 _103145 s x t a).
Proof. exact (MK_COMB (@lem4294190 _103145) (@lem4294189 _103141 _103145 s x t a)). Qed.
Lemma lem4294192 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term178 _103141 _103145 s x t a) = (term351 _103141 _103145 s x t a).
Proof. exact (TRANS (@lem4294147 _103141 _103145 s x t a) (@lem4294191 _103141 _103145 s x t a)). Qed.
Lemma lem4294193 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term270 _103141 _103145 a s t x) = (term270 _103141 _103145 a s t x).
Proof. exact (eq_refl (term270 _103141 _103145 a s t x)). Qed.
Lemma lem4294194 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term272 _103141 _103145 s x t a) = (term352 _103141 _103145 s x t a).
Proof. exact (MK_COMB (@lem4294193 _103141 _103145 a s t x) (@lem4294192 _103141 _103145 s x t a)). Qed.
Lemma lem4294196 {A : Type'} (P : Prop) (Q : A -> Prop) : (term353 A P Q) = (term354 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4294197 {_103145 : Type'} (P : Prop) (Q : _103145 -> Prop) : (term353 _103145 P Q) = (term354 _103145 P Q).
Proof. exact (@lem4294196 _103145 P Q). Qed.
Lemma lem4294198 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term355 _103141 _103145 s x t a) = (term356 _103141 _103145 s x t a).
Proof. exact (@lem4294197 _103145 (term233 _103141 _103145 a s t x) (term350 _103141 _103145 s x t a)). Qed.
Lemma lem4294199 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : _103145) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term357 _103141 _103145 s x' t a x) = (term346 _103141 _103145 s x x' t a).
Proof. exact (eq_refl (term357 _103141 _103145 s x' t a x)). Qed.
Lemma lem4294200 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term358 _103141 _103145 s x t a) = (term350 _103141 _103145 s x t a).
Proof. exact (fun_ext (fun x' : _103145 => @lem4294199 _103141 _103145 s x' x t a)). Qed.
Lemma lem4294201 {_103145 : Type'} : (@ex _103145) = (@ex _103145).
Proof. exact (eq_refl (@ex _103145)). Qed.
Lemma lem4294202 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term359 _103141 _103145 s x t a) = (term351 _103141 _103145 s x t a).
Proof. exact (MK_COMB (@lem4294201 _103145) (@lem4294200 _103141 _103145 s x t a)). Qed.
Lemma lem4294203 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term270 _103141 _103145 a s t x) = (term270 _103141 _103145 a s t x).
Proof. exact (eq_refl (term270 _103141 _103145 a s t x)). Qed.
Lemma lem4294204 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term355 _103141 _103145 s x t a) = (term352 _103141 _103145 s x t a).
Proof. exact (MK_COMB (@lem4294203 _103141 _103145 a s t x) (@lem4294202 _103141 _103145 s x t a)). Qed.
Lemma lem4294205 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4294206 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term360 _103141 _103145 s x t a) = (term361 _103141 _103145 s x t a).
Proof. exact (MK_COMB (@lem4294205) (@lem4294204 _103141 _103145 s x t a)). Qed.
Lemma lem4294207 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : _103145) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term357 _103141 _103145 s x' t a x) = (term346 _103141 _103145 s x x' t a).
Proof. exact (eq_refl (term357 _103141 _103145 s x' t a x)). Qed.
Lemma lem4294208 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term270 _103141 _103145 a s t x) = (term270 _103141 _103145 a s t x).
Proof. exact (eq_refl (term270 _103141 _103145 a s t x)). Qed.
Lemma lem4294209 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : _103145) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term362 _103141 _103145 s x' t a x) = (term363 _103141 _103145 s x x' t a).
Proof. exact (MK_COMB (@lem4294208 _103141 _103145 a s t x') (@lem4294207 _103141 _103145 s x x' t a)). Qed.
Lemma lem4294210 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term364 _103141 _103145 s x t a) = (term365 _103141 _103145 s x t a).
Proof. exact (fun_ext (fun x' : _103145 => @lem4294209 _103141 _103145 s x' x t a)). Qed.
Lemma lem4294211 {_103145 : Type'} : (@ex _103145) = (@ex _103145).
Proof. exact (eq_refl (@ex _103145)). Qed.
Lemma lem4294212 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term356 _103141 _103145 s x t a) = (term366 _103141 _103145 s x t a).
Proof. exact (MK_COMB (@lem4294211 _103145) (@lem4294210 _103141 _103145 s x t a)). Qed.
Lemma lem4294213 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : ((term355 _103141 _103145 s x t a) = (term356 _103141 _103145 s x t a)) = ((term352 _103141 _103145 s x t a) = (term366 _103141 _103145 s x t a)).
Proof. exact (MK_COMB (@lem4294206 _103141 _103145 s x t a) (@lem4294212 _103141 _103145 s x t a)). Qed.
Lemma lem4294214 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term352 _103141 _103145 s x t a) = (term366 _103141 _103145 s x t a).
Proof. exact (EQ_MP (@lem4294213 _103141 _103145 s x t a) (@lem4294198 _103141 _103145 s x t a)). Qed.
Lemma lem4294216 {A : Type'} (P : Prop) (Q : A -> Prop) : (term353 A P Q) = (term354 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4294217 {_103141 : Type'} (P : Prop) (Q : _103141 -> Prop) : (term353 _103141 P Q) = (term354 _103141 P Q).
Proof. exact (@lem4294216 _103141 P Q). Qed.
Lemma lem4294218 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : _103145) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term367 _103141 _103145 s x x' t a) = (term368 _103141 _103145 s x x' t a).
Proof. exact (@lem4294217 _103141 (term233 _103141 _103145 a s t x') (term345 _103141 _103145 s x x' t a)). Qed.
Lemma lem4294219 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : _103145) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) : (term369 _103141 _103145 s x x' t a y) = (term343 _103141 _103145 s x x' t a y).
Proof. exact (eq_refl (term369 _103141 _103145 s x x' t a y)). Qed.
Lemma lem4294220 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : _103145) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term370 _103141 _103145 s x x' t a) = (term345 _103141 _103145 s x x' t a).
Proof. exact (fun_ext (fun y : _103141 => @lem4294219 _103141 _103145 s x x' t a y)). Qed.
Lemma lem4294221 {_103141 : Type'} : (@ex _103141) = (@ex _103141).
Proof. exact (eq_refl (@ex _103141)). Qed.
Lemma lem4294222 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : _103145) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term371 _103141 _103145 s x x' t a) = (term346 _103141 _103145 s x x' t a).
Proof. exact (MK_COMB (@lem4294221 _103141) (@lem4294220 _103141 _103145 s x x' t a)). Qed.
Lemma lem4294223 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term270 _103141 _103145 a s t x) = (term270 _103141 _103145 a s t x).
Proof. exact (eq_refl (term270 _103141 _103145 a s t x)). Qed.
Lemma lem4294224 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : _103145) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term367 _103141 _103145 s x x' t a) = (term363 _103141 _103145 s x x' t a).
Proof. exact (MK_COMB (@lem4294223 _103141 _103145 a s t x') (@lem4294222 _103141 _103145 s x x' t a)). Qed.
Lemma lem4294225 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4294226 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : _103145) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term372 _103141 _103145 s x x' t a) = (term373 _103141 _103145 s x x' t a).
Proof. exact (MK_COMB (@lem4294225) (@lem4294224 _103141 _103145 s x x' t a)). Qed.
Lemma lem4294227 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : _103145) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) : (term369 _103141 _103145 s x x' t a y) = (term343 _103141 _103145 s x x' t a y).
Proof. exact (eq_refl (term369 _103141 _103145 s x x' t a y)). Qed.
Lemma lem4294228 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term270 _103141 _103145 a s t x) = (term270 _103141 _103145 a s t x).
Proof. exact (eq_refl (term270 _103141 _103145 a s t x)). Qed.
Lemma lem4294229 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : _103145) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) : (term374 _103141 _103145 s x x' t a y) = (term375 _103141 _103145 s x x' t a y).
Proof. exact (MK_COMB (@lem4294228 _103141 _103145 a s t x') (@lem4294227 _103141 _103145 s x x' t a y)). Qed.
Lemma lem4294230 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : _103145) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term376 _103141 _103145 s x x' t a) = (term377 _103141 _103145 s x x' t a).
Proof. exact (fun_ext (fun y : _103141 => @lem4294229 _103141 _103145 s x x' t a y)). Qed.
Lemma lem4294231 {_103141 : Type'} : (@ex _103141) = (@ex _103141).
Proof. exact (eq_refl (@ex _103141)). Qed.
Lemma lem4294232 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : _103145) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term368 _103141 _103145 s x x' t a) = (term378 _103141 _103145 s x x' t a).
Proof. exact (MK_COMB (@lem4294231 _103141) (@lem4294230 _103141 _103145 s x x' t a)). Qed.
Lemma lem4294233 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : _103145) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : ((term367 _103141 _103145 s x x' t a) = (term368 _103141 _103145 s x x' t a)) = ((term363 _103141 _103145 s x x' t a) = (term378 _103141 _103145 s x x' t a)).
Proof. exact (MK_COMB (@lem4294226 _103141 _103145 s x x' t a) (@lem4294232 _103141 _103145 s x x' t a)). Qed.
Lemma lem4294234 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : _103145) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term363 _103141 _103145 s x x' t a) = (term378 _103141 _103145 s x x' t a).
Proof. exact (EQ_MP (@lem4294233 _103141 _103145 s x x' t a) (@lem4294218 _103141 _103145 s x x' t a)). Qed.
Lemma lem4294235 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term365 _103141 _103145 s x t a) = (term379 _103141 _103145 s x t a).
Proof. exact (fun_ext (fun x' : _103145 => @lem4294234 _103141 _103145 s x' x t a)). Qed.
Lemma lem4294236 {_103145 : Type'} : (@ex _103145) = (@ex _103145).
Proof. exact (eq_refl (@ex _103145)). Qed.
Lemma lem4294237 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term366 _103141 _103145 s x t a) = (term380 _103141 _103145 s x t a).
Proof. exact (MK_COMB (@lem4294236 _103145) (@lem4294235 _103141 _103145 s x t a)). Qed.
Lemma lem4294238 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term352 _103141 _103145 s x t a) = (term380 _103141 _103145 s x t a).
Proof. exact (TRANS (@lem4294214 _103141 _103145 s x t a) (@lem4294237 _103141 _103145 s x t a)). Qed.
Lemma lem4294239 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term272 _103141 _103145 s x t a) = (term380 _103141 _103145 s x t a).
Proof. exact (TRANS (@lem4294194 _103141 _103145 s x t a) (@lem4294238 _103141 _103145 s x t a)). Qed.
Lemma lem4294240 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term279 _103141 _103145 s x t a) = (term381 _103141 _103145 s x t a).
Proof. exact (MK_COMB (@lem4294121 _103141 _103145 s x t a) (@lem4294239 _103141 _103145 s x t a)). Qed.
Lemma lem4294242 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term329 A P Q) = (term330 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4294243 {_103145 : Type'} (P : _103145 -> Prop) (Q : _103145 -> Prop) : (term329 _103145 P Q) = (term330 _103145 P Q).
Proof. exact (@lem4294242 _103145 P Q). Qed.
Lemma lem4294244 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term382 _103141 _103145 s x t a) = (term383 _103141 _103145 s x t a).
Proof. exact (@lem4294243 _103145 (term310 _103141 _103145 s x t a) (term379 _103141 _103145 s x t a)). Qed.
Lemma lem4294245 {_103141 _103145 : Type'} (x : _103145) (s : _103145 -> Prop) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term384 _103141 _103145 s x' t a x) = (term309 _103141 _103145 x s x' t a).
Proof. exact (eq_refl (term384 _103141 _103145 s x' t a x)). Qed.
Lemma lem4294246 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term385 _103141 _103145 s x t a) = (term310 _103141 _103145 s x t a).
Proof. exact (fun_ext (fun x' : _103145 => @lem4294245 _103141 _103145 x' s x t a)). Qed.
Lemma lem4294247 {_103145 : Type'} : (@ex _103145) = (@ex _103145).
Proof. exact (eq_refl (@ex _103145)). Qed.
Lemma lem4294248 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term386 _103141 _103145 s x t a) = (term311 _103141 _103145 s x t a).
Proof. exact (MK_COMB (@lem4294247 _103145) (@lem4294246 _103141 _103145 s x t a)). Qed.
Lemma lem4294249 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4294250 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term387 _103141 _103145 s x t a) = (term312 _103141 _103145 s x t a).
Proof. exact (MK_COMB (@lem4294249) (@lem4294248 _103141 _103145 s x t a)). Qed.
Lemma lem4294251 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : _103145) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term388 _103141 _103145 s x' t a x) = (term378 _103141 _103145 s x x' t a).
Proof. exact (eq_refl (term388 _103141 _103145 s x' t a x)). Qed.
Lemma lem4294252 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term389 _103141 _103145 s x t a) = (term379 _103141 _103145 s x t a).
Proof. exact (fun_ext (fun x' : _103145 => @lem4294251 _103141 _103145 s x' x t a)). Qed.
Lemma lem4294253 {_103145 : Type'} : (@ex _103145) = (@ex _103145).
Proof. exact (eq_refl (@ex _103145)). Qed.
Lemma lem4294254 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term390 _103141 _103145 s x t a) = (term380 _103141 _103145 s x t a).
Proof. exact (MK_COMB (@lem4294253 _103145) (@lem4294252 _103141 _103145 s x t a)). Qed.
Lemma lem4294255 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term382 _103141 _103145 s x t a) = (term381 _103141 _103145 s x t a).
Proof. exact (MK_COMB (@lem4294250 _103141 _103145 s x t a) (@lem4294254 _103141 _103145 s x t a)). Qed.
Lemma lem4294256 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4294257 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term391 _103141 _103145 s x t a) = (term392 _103141 _103145 s x t a).
Proof. exact (MK_COMB (@lem4294256) (@lem4294255 _103141 _103145 s x t a)). Qed.
Lemma lem4294258 {_103141 _103145 : Type'} (x : _103145) (s : _103145 -> Prop) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term384 _103141 _103145 s x' t a x) = (term309 _103141 _103145 x s x' t a).
Proof. exact (eq_refl (term384 _103141 _103145 s x' t a x)). Qed.
Lemma lem4294259 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4294260 {_103141 _103145 : Type'} (x : _103145) (s : _103145 -> Prop) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term393 _103141 _103145 s x' t a x) = (term394 _103141 _103145 x s x' t a).
Proof. exact (MK_COMB (@lem4294259) (@lem4294258 _103141 _103145 x s x' t a)). Qed.
Lemma lem4294261 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : _103145) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term388 _103141 _103145 s x' t a x) = (term378 _103141 _103145 s x x' t a).
Proof. exact (eq_refl (term388 _103141 _103145 s x' t a x)). Qed.
Lemma lem4294262 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : _103145) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term395 _103141 _103145 s x' t a x) = (term396 _103141 _103145 s x x' t a).
Proof. exact (MK_COMB (@lem4294260 _103141 _103145 x s x' t a) (@lem4294261 _103141 _103145 s x x' t a)). Qed.
Lemma lem4294263 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term397 _103141 _103145 s x t a) = (term398 _103141 _103145 s x t a).
Proof. exact (fun_ext (fun x' : _103145 => @lem4294262 _103141 _103145 s x' x t a)). Qed.
Lemma lem4294264 {_103145 : Type'} : (@ex _103145) = (@ex _103145).
Proof. exact (eq_refl (@ex _103145)). Qed.
Lemma lem4294265 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term383 _103141 _103145 s x t a) = (term399 _103141 _103145 s x t a).
Proof. exact (MK_COMB (@lem4294264 _103145) (@lem4294263 _103141 _103145 s x t a)). Qed.
Lemma lem4294266 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : ((term382 _103141 _103145 s x t a) = (term383 _103141 _103145 s x t a)) = ((term381 _103141 _103145 s x t a) = (term399 _103141 _103145 s x t a)).
Proof. exact (MK_COMB (@lem4294257 _103141 _103145 s x t a) (@lem4294265 _103141 _103145 s x t a)). Qed.
Lemma lem4294267 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term381 _103141 _103145 s x t a) = (term399 _103141 _103145 s x t a).
Proof. exact (EQ_MP (@lem4294266 _103141 _103145 s x t a) (@lem4294244 _103141 _103145 s x t a)). Qed.
Lemma lem4294269 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term329 A P Q) = (term330 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4294270 {_103141 : Type'} (P : _103141 -> Prop) (Q : _103141 -> Prop) : (term329 _103141 P Q) = (term330 _103141 P Q).
Proof. exact (@lem4294269 _103141 P Q). Qed.
Lemma lem4294271 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : _103145) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term400 _103141 _103145 s x x' t a) = (term401 _103141 _103145 s x x' t a).
Proof. exact (@lem4294270 _103141 (term308 _103141 _103145 x s x' t a) (term377 _103141 _103145 s x x' t a)). Qed.
Lemma lem4294272 {_103141 _103145 : Type'} (x : _103145) (y : _103141) (s : _103145 -> Prop) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term402 _103141 _103145 x s x' t a y) = (term306 _103141 _103145 x y s x' t a).
Proof. exact (eq_refl (term402 _103141 _103145 x s x' t a y)). Qed.
Lemma lem4294273 {_103141 _103145 : Type'} (x : _103145) (s : _103145 -> Prop) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term403 _103141 _103145 x s x' t a) = (term308 _103141 _103145 x s x' t a).
Proof. exact (fun_ext (fun y : _103141 => @lem4294272 _103141 _103145 x y s x' t a)). Qed.
Lemma lem4294274 {_103141 : Type'} : (@ex _103141) = (@ex _103141).
Proof. exact (eq_refl (@ex _103141)). Qed.
Lemma lem4294275 {_103141 _103145 : Type'} (x : _103145) (s : _103145 -> Prop) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term404 _103141 _103145 x s x' t a) = (term309 _103141 _103145 x s x' t a).
Proof. exact (MK_COMB (@lem4294274 _103141) (@lem4294273 _103141 _103145 x s x' t a)). Qed.
Lemma lem4294276 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4294277 {_103141 _103145 : Type'} (x : _103145) (s : _103145 -> Prop) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term405 _103141 _103145 x s x' t a) = (term394 _103141 _103145 x s x' t a).
Proof. exact (MK_COMB (@lem4294276) (@lem4294275 _103141 _103145 x s x' t a)). Qed.
Lemma lem4294278 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : _103145) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) : (term406 _103141 _103145 s x x' t a y) = (term375 _103141 _103145 s x x' t a y).
Proof. exact (eq_refl (term406 _103141 _103145 s x x' t a y)). Qed.
Lemma lem4294279 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : _103145) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term407 _103141 _103145 s x x' t a) = (term377 _103141 _103145 s x x' t a).
Proof. exact (fun_ext (fun y : _103141 => @lem4294278 _103141 _103145 s x x' t a y)). Qed.
Lemma lem4294280 {_103141 : Type'} : (@ex _103141) = (@ex _103141).
Proof. exact (eq_refl (@ex _103141)). Qed.
Lemma lem4294281 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : _103145) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term408 _103141 _103145 s x x' t a) = (term378 _103141 _103145 s x x' t a).
Proof. exact (MK_COMB (@lem4294280 _103141) (@lem4294279 _103141 _103145 s x x' t a)). Qed.
Lemma lem4294282 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : _103145) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term400 _103141 _103145 s x x' t a) = (term396 _103141 _103145 s x x' t a).
Proof. exact (MK_COMB (@lem4294277 _103141 _103145 x s x' t a) (@lem4294281 _103141 _103145 s x x' t a)). Qed.
Lemma lem4294283 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4294284 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : _103145) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term409 _103141 _103145 s x x' t a) = (term410 _103141 _103145 s x x' t a).
Proof. exact (MK_COMB (@lem4294283) (@lem4294282 _103141 _103145 s x x' t a)). Qed.
Lemma lem4294285 {_103141 _103145 : Type'} (x : _103145) (y : _103141) (s : _103145 -> Prop) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term402 _103141 _103145 x s x' t a y) = (term306 _103141 _103145 x y s x' t a).
Proof. exact (eq_refl (term402 _103141 _103145 x s x' t a y)). Qed.
Lemma lem4294286 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4294287 {_103141 _103145 : Type'} (x : _103145) (y : _103141) (s : _103145 -> Prop) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term411 _103141 _103145 x s x' t a y) = (term412 _103141 _103145 x y s x' t a).
Proof. exact (MK_COMB (@lem4294286) (@lem4294285 _103141 _103145 x y s x' t a)). Qed.
Lemma lem4294288 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : _103145) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) : (term406 _103141 _103145 s x x' t a y) = (term375 _103141 _103145 s x x' t a y).
Proof. exact (eq_refl (term406 _103141 _103145 s x x' t a y)). Qed.
Lemma lem4294289 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : _103145) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) : (term413 _103141 _103145 s x x' t a y) = (term414 _103141 _103145 s x x' t a y).
Proof. exact (MK_COMB (@lem4294287 _103141 _103145 x y s x' t a) (@lem4294288 _103141 _103145 s x x' t a y)). Qed.
Lemma lem4294290 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : _103145) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term415 _103141 _103145 s x x' t a) = (term416 _103141 _103145 s x x' t a).
Proof. exact (fun_ext (fun y : _103141 => @lem4294289 _103141 _103145 s x x' t a y)). Qed.
Lemma lem4294291 {_103141 : Type'} : (@ex _103141) = (@ex _103141).
Proof. exact (eq_refl (@ex _103141)). Qed.
Lemma lem4294292 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : _103145) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term401 _103141 _103145 s x x' t a) = (term417 _103141 _103145 s x x' t a).
Proof. exact (MK_COMB (@lem4294291 _103141) (@lem4294290 _103141 _103145 s x x' t a)). Qed.
Lemma lem4294293 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : _103145) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : ((term400 _103141 _103145 s x x' t a) = (term401 _103141 _103145 s x x' t a)) = ((term396 _103141 _103145 s x x' t a) = (term417 _103141 _103145 s x x' t a)).
Proof. exact (MK_COMB (@lem4294284 _103141 _103145 s x x' t a) (@lem4294292 _103141 _103145 s x x' t a)). Qed.
Lemma lem4294294 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : _103145) (x' : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term396 _103141 _103145 s x x' t a) = (term417 _103141 _103145 s x x' t a).
Proof. exact (EQ_MP (@lem4294293 _103141 _103145 s x x' t a) (@lem4294271 _103141 _103145 s x x' t a)). Qed.
Lemma lem4294295 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term398 _103141 _103145 s x t a) = (term418 _103141 _103145 s x t a).
Proof. exact (fun_ext (fun x' : _103145 => @lem4294294 _103141 _103145 s x' x t a)). Qed.
Lemma lem4294296 {_103145 : Type'} : (@ex _103145) = (@ex _103145).
Proof. exact (eq_refl (@ex _103145)). Qed.
Lemma lem4294297 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term399 _103141 _103145 s x t a) = (term419 _103141 _103145 s x t a).
Proof. exact (MK_COMB (@lem4294296 _103145) (@lem4294295 _103141 _103145 s x t a)). Qed.
Lemma lem4294298 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term381 _103141 _103145 s x t a) = (term419 _103141 _103145 s x t a).
Proof. exact (TRANS (@lem4294267 _103141 _103145 s x t a) (@lem4294297 _103141 _103145 s x t a)). Qed.
Lemma lem4294300 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term279 _103141 _103145 s x t a) = (term419 _103141 _103145 s x t a).
Proof. exact (TRANS (@lem4294240 _103141 _103145 s x t a) (@lem4294298 _103141 _103145 s x t a)). Qed.
Lemma lem4294301 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term203 _103141 _103145 s x t a) = (term419 _103141 _103145 s x t a).
Proof. exact (TRANS (@lem4293762 _103141 _103145 s x t a) (@lem4294300 _103141 _103145 s x t a)). Qed.
Lemma lem4294302 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (h1 : term203 _103141 _103145 s x t a) : term419 _103141 _103145 s x t a.
Proof. exact (EQ_MP (@lem4294301 _103141 _103145 s x t a) (@lem4293612 _103141 _103145 s x t a h1)). Qed.
Lemma lem4294303 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x' : _103145) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (h1 : term417 _103141 _103145 s x' x t a) : term417 _103141 _103145 s x' x t a.
Proof. exact (h1). Qed.
Lemma lem4294304 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x' : _103145) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) (h1 : term414 _103141 _103145 s x' x t a y) : term414 _103141 _103145 s x' x t a y.
Proof. exact (h1). Qed.
Lemma lem4294347 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x' : _103145) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) : (term343 _103141 _103145 s x' x t a y) = (term343 _103141 _103145 s x' x t a y).
Proof. exact (eq_refl (term343 _103141 _103145 s x' x t a y)). Qed.
Lemma lem4294386 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) : (term216 _103141 _103145 a s t x x' y) = (term216 _103141 _103145 a s t x x' y).
Proof. exact (eq_refl (term216 _103141 _103145 a s t x x' y)). Qed.
Lemma lem4294387 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) : (term225 _103141 _103145 a s t x x') = (term225 _103141 _103145 a s t x x').
Proof. exact (fun_ext (fun y : _103141 => @lem4294386 _103141 _103145 a s t x x' y)). Qed.
Lemma lem4294388 {_103141 : Type'} : (@all _103141) = (@all _103141).
Proof. exact (eq_refl (@all _103141)). Qed.
Lemma lem4294389 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) : (term226 _103141 _103145 a s t x x') = (term226 _103141 _103145 a s t x x').
Proof. exact (MK_COMB (@lem4294388 _103141) (@lem4294387 _103141 _103145 a s t x x')). Qed.
Lemma lem4294390 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term232 _103141 _103145 a s t x) = (term232 _103141 _103145 a s t x).
Proof. exact (fun_ext (fun x' : _103145 => @lem4294389 _103141 _103145 a s t x x')). Qed.
Lemma lem4294391 {_103145 : Type'} : (@all _103145) = (@all _103145).
Proof. exact (eq_refl (@all _103145)). Qed.
Lemma lem4294392 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term233 _103141 _103145 a s t x) = (term233 _103141 _103145 a s t x).
Proof. exact (MK_COMB (@lem4294391 _103145) (@lem4294390 _103141 _103145 a s t x)). Qed.
Lemma lem4294393 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4294394 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term270 _103141 _103145 a s t x) = (term270 _103141 _103145 a s t x).
Proof. exact (MK_COMB (@lem4294393) (@lem4294392 _103141 _103145 a s t x)). Qed.
Lemma lem4294395 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x' : _103145) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) : (term375 _103141 _103145 s x' x t a y) = (term375 _103141 _103145 s x' x t a y).
Proof. exact (MK_COMB (@lem4294394 _103141 _103145 a s t x) (@lem4294347 _103141 _103145 s x' x t a y)). Qed.
Lemma lem4294416 {_103141 _103145 : Type'} (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (x' : _103141) : (term256 _103141 _103145 x t a x') = (term256 _103141 _103145 x t a x').
Proof. exact (eq_refl (term256 _103141 _103145 x t a x')). Qed.
Lemma lem4294417 {_103141 _103145 : Type'} (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term262 _103141 _103145 x t a) = (term262 _103141 _103145 x t a).
Proof. exact (fun_ext (fun x' : _103141 => @lem4294416 _103141 _103145 x t a x')). Qed.
Lemma lem4294418 {_103141 : Type'} : (@all _103141) = (@all _103141).
Proof. exact (eq_refl (@all _103141)). Qed.
Lemma lem4294419 {_103141 _103145 : Type'} (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term263 _103141 _103145 x t a) = (term263 _103141 _103145 x t a).
Proof. exact (MK_COMB (@lem4294418 _103141) (@lem4294417 _103141 _103145 x t a)). Qed.
Lemma lem4294448 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) : (term239 _103141 _103145 s t x x' y) = (term239 _103141 _103145 s t x x' y).
Proof. exact (eq_refl (term239 _103141 _103145 s t x x' y)). Qed.
Lemma lem4294449 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) : (term246 _103141 _103145 s t x x') = (term246 _103141 _103145 s t x x').
Proof. exact (fun_ext (fun y : _103141 => @lem4294448 _103141 _103145 s t x x' y)). Qed.
Lemma lem4294450 {_103141 : Type'} : (@all _103141) = (@all _103141).
Proof. exact (eq_refl (@all _103141)). Qed.
Lemma lem4294451 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) : (term247 _103141 _103145 s t x x') = (term247 _103141 _103145 s t x x').
Proof. exact (MK_COMB (@lem4294450 _103141) (@lem4294449 _103141 _103145 s t x x')). Qed.
Lemma lem4294452 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term253 _103141 _103145 s t x) = (term253 _103141 _103145 s t x).
Proof. exact (fun_ext (fun x' : _103145 => @lem4294451 _103141 _103145 s t x x')). Qed.
Lemma lem4294453 {_103145 : Type'} : (@all _103145) = (@all _103145).
Proof. exact (eq_refl (@all _103145)). Qed.
Lemma lem4294454 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term254 _103141 _103145 s t x) = (term254 _103141 _103145 s t x).
Proof. exact (MK_COMB (@lem4294453 _103145) (@lem4294452 _103141 _103145 s t x)). Qed.
Lemma lem4294455 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4294456 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term265 _103141 _103145 s t x) = (term265 _103141 _103145 s t x).
Proof. exact (MK_COMB (@lem4294455) (@lem4294454 _103141 _103145 s t x)). Qed.
Lemma lem4294457 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term267 _103141 _103145 s x t a) = (term267 _103141 _103145 s x t a).
Proof. exact (MK_COMB (@lem4294456 _103141 _103145 s t x) (@lem4294419 _103141 _103145 x t a)). Qed.
Lemma lem4294490 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) : (term304 _103141 _103145 a s t x x' y) = (term304 _103141 _103145 a s t x x' y).
Proof. exact (eq_refl (term304 _103141 _103145 a s t x x' y)). Qed.
Lemma lem4294491 {_103141 _103145 : Type'} (x' : _103145) (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term306 _103141 _103145 x' y s x t a) = (term306 _103141 _103145 x' y s x t a).
Proof. exact (MK_COMB (@lem4294490 _103141 _103145 a s t x x' y) (@lem4294457 _103141 _103145 s x t a)). Qed.
Lemma lem4294492 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4294493 {_103141 _103145 : Type'} (x' : _103145) (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term412 _103141 _103145 x' y s x t a) = (term412 _103141 _103145 x' y s x t a).
Proof. exact (MK_COMB (@lem4294492) (@lem4294491 _103141 _103145 x' y s x t a)). Qed.
Lemma lem4294494 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x' : _103145) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) : (term414 _103141 _103145 s x' x t a y) = (term414 _103141 _103145 s x' x t a y).
Proof. exact (MK_COMB (@lem4294493 _103141 _103145 x' y s x t a) (@lem4294395 _103141 _103145 s x' x t a y)). Qed.
Lemma lem4294495 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x' : _103145) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) (h1 : term414 _103141 _103145 s x' x t a y) : term414 _103141 _103145 s x' x t a y.
Proof. exact (EQ_MP (@lem4294494 _103141 _103145 s x' x t a y) (@lem4294304 _103141 _103145 s x' x t a y h1)). Qed.
Lemma lem4294496 {_103141 _103145 : Type'} (x' : _103145) (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (h1 : term306 _103141 _103145 x' y s x t a) : term306 _103141 _103145 x' y s x t a.
Proof. exact (h1). Qed.
Lemma lem4294497 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x' : _103145) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) (h1 : term375 _103141 _103145 s x' x t a y) : term375 _103141 _103145 s x' x t a y.
Proof. exact (h1). Qed.
Lemma lem4294498 {_103141 _103145 : Type'} (x' : _103145) (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (h1 : term306 _103141 _103145 x' y s x t a) : term267 _103141 _103145 s x t a.
Proof. exact (proj2 (@lem4294496 _103141 _103145 x' y s x t a h1)). Qed.
Lemma lem4294499 {_103141 _103145 : Type'} (x' : _103145) (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (h1 : term306 _103141 _103145 x' y s x t a) : term100 _103141 _103145 a s t x x' y.
Proof. exact (proj1 (@lem4294496 _103141 _103145 x' y s x t a h1)). Qed.
Lemma lem4294500 {_103141 _103145 : Type'} (x' : _103145) (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (h1 : term306 _103141 _103145 x' y s x t a) : term263 _103141 _103145 x t a.
Proof. exact (proj2 (@lem4294498 _103141 _103145 x' y s x t a h1)). Qed.
Lemma lem4294501 {_103141 _103145 : Type'} (x' : _103145) (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (h1 : term306 _103141 _103145 x' y s x t a) : term254 _103141 _103145 s t x.
Proof. exact (proj1 (@lem4294498 _103141 _103145 x' y s x t a h1)). Qed.
Lemma lem4294503 {_103141 _103145 : Type'} (x' : _103145) (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (h1 : term306 _103141 _103145 x' y s x t a) : term86 _103141 _103145 a s t x' y.
Proof. exact (proj1 (@lem4294499 _103141 _103145 x' y s x t a h1)). Qed.
Lemma lem4294505 {_103141 _103145 : Type'} (x' : _103145) (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (h1 : term306 _103141 _103145 x' y s x t a) : term82 _103145 a s x'.
Proof. exact (proj1 (@lem4294503 _103141 _103145 x' y s x t a h1)). Qed.
Lemma lem4294508 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x' : _103145) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) (h1 : term375 _103141 _103145 s x' x t a y) : term343 _103141 _103145 s x' x t a y.
Proof. exact (proj2 (@lem4294497 _103141 _103145 s x' x t a y h1)). Qed.
Lemma lem4294509 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x' : _103145) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) (h1 : term375 _103141 _103145 s x' x t a y) : term233 _103141 _103145 a s t x.
Proof. exact (proj1 (@lem4294497 _103141 _103145 s x' x t a y h1)). Qed.
Lemma lem4294510 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) (h1 : term150 _103141 _103145 s t x x' y) : term150 _103141 _103145 s t x x' y.
Proof. exact (h1). Qed.
Lemma lem4294511 {_103141 _103145 : Type'} (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) (h1 : term174 _103141 _103145 x t a y) : term174 _103141 _103145 x t a y.
Proof. exact (h1). Qed.
Lemma lem4294513 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) (h1 : term150 _103141 _103145 s t x x' y) : term137 _103141 _103145 s t x' y.
Proof. exact (proj1 (@lem4294510 _103141 _103145 s t x x' y h1)). Qed.
Lemma lem4294547 {_103141 _103145 : Type'} (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (x' : _103141) : (term256 _103141 _103145 x t a x') = (term256 _103141 _103145 x t a x').
Proof. exact (eq_refl (term256 _103141 _103145 x t a x')). Qed.
Lemma lem4294548 {_103141 _103145 : Type'} (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term262 _103141 _103145 x t a) = (term262 _103141 _103145 x t a).
Proof. exact (fun_ext (fun x' : _103141 => @lem4294547 _103141 _103145 x t a x')). Qed.
Lemma lem4294549 {_103141 : Type'} : (@all _103141) = (@all _103141).
Proof. exact (eq_refl (@all _103141)). Qed.
Lemma lem4294551 {_103141 _103145 : Type'} (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term263 _103141 _103145 x t a) = (term263 _103141 _103145 x t a).
Proof. exact (MK_COMB (@lem4294549 _103141) (@lem4294548 _103141 _103145 x t a)). Qed.
Lemma lem4294552 {_103141 _103145 : Type'} (x' : _103145) (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (h1 : term306 _103141 _103145 x' y s x t a) : term263 _103141 _103145 x t a.
Proof. exact (EQ_MP (@lem4294551 _103141 _103145 x t a) (@lem4294500 _103141 _103145 x' y s x t a h1)). Qed.
Lemma lem4294564 {_103145 : Type'} (x' : _103145) (a : _103145) (h1 : x' = a) : x' = a.
Proof. exact (h1). Qed.
Lemma lem4294578 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) : (term239 _103141 _103145 s t x x' y) = (term239 _103141 _103145 s t x x' y).
Proof. exact (eq_refl (term239 _103141 _103145 s t x x' y)). Qed.
Lemma lem4294579 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) : (term246 _103141 _103145 s t x x') = (term246 _103141 _103145 s t x x').
Proof. exact (fun_ext (fun y : _103141 => @lem4294578 _103141 _103145 s t x x' y)). Qed.
Lemma lem4294580 {_103141 : Type'} : (@all _103141) = (@all _103141).
Proof. exact (eq_refl (@all _103141)). Qed.
Lemma lem4294581 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) : (term247 _103141 _103145 s t x x') = (term247 _103141 _103145 s t x x').
Proof. exact (MK_COMB (@lem4294580 _103141) (@lem4294579 _103141 _103145 s t x x')). Qed.
Lemma lem4294582 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term253 _103141 _103145 s t x) = (term253 _103141 _103145 s t x).
Proof. exact (fun_ext (fun x' : _103145 => @lem4294581 _103141 _103145 s t x x')). Qed.
Lemma lem4294583 {_103145 : Type'} : (@all _103145) = (@all _103145).
Proof. exact (eq_refl (@all _103145)). Qed.
Lemma lem4294585 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term254 _103141 _103145 s t x) = (term254 _103141 _103145 s t x).
Proof. exact (MK_COMB (@lem4294583 _103145) (@lem4294582 _103141 _103145 s t x)). Qed.
Lemma lem4294586 {_103141 _103145 : Type'} (x' : _103145) (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (h1 : term306 _103141 _103145 x' y s x t a) : term254 _103141 _103145 s t x.
Proof. exact (EQ_MP (@lem4294585 _103141 _103145 s t x) (@lem4294501 _103141 _103145 x' y s x t a h1)). Qed.
Lemma lem4294611 {_103145 : Type'} (s : _103145 -> Prop) (x' : _103145) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem4294613 {_103141 _103145 : Type'} (x : prod _103145 _103141) (x' : _103145) (y : _103141) : (term212 _103141 _103145 x x' y) = (term212 _103141 _103145 x x' y).
Proof. exact (eq_refl (term212 _103141 _103145 x x' y)). Qed.
Lemma lem4294630 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : _103145) (y : _103141) : (term210 _103141 _103145 a s t x y) = (term420 _103141 _103145 a s t x y).
Proof. exact (@lem19699 (term421 _103145 x a) (term422 _103145 s x) (term206 _103141 _103145 t x y)). Qed.
Lemma lem4294631 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4294632 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : _103145) (y : _103141) : (term214 _103141 _103145 a s t x y) = (term423 _103141 _103145 a s t x y).
Proof. exact (MK_COMB (@lem4294631) (@lem4294630 _103141 _103145 a s t x y)). Qed.
Lemma lem4294633 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) : (term216 _103141 _103145 a s t x x' y) = (term424 _103141 _103145 a s t x x' y).
Proof. exact (MK_COMB (@lem4294632 _103141 _103145 a s t x' y) (@lem4294613 _103141 _103145 x x' y)). Qed.
Lemma lem4294640 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) : (term424 _103141 _103145 a s t x x' y) = (term425 _103141 _103145 a s t x x' y).
Proof. exact (@lem19699 (term426 _103141 _103145 a t x' y) (term235 _103141 _103145 s t x' y) (term212 _103141 _103145 x x' y)). Qed.
Lemma lem4294641 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) : (term216 _103141 _103145 a s t x x' y) = (term425 _103141 _103145 a s t x x' y).
Proof. exact (TRANS (@lem4294633 _103141 _103145 a s t x x' y) (@lem4294640 _103141 _103145 a s t x x' y)). Qed.
Lemma lem4294642 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) : (term225 _103141 _103145 a s t x x') = (term427 _103141 _103145 a s t x x').
Proof. exact (fun_ext (fun y : _103141 => @lem4294641 _103141 _103145 a s t x x' y)). Qed.
Lemma lem4294643 {_103141 : Type'} : (@all _103141) = (@all _103141).
Proof. exact (eq_refl (@all _103141)). Qed.
Lemma lem4294644 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) : (term226 _103141 _103145 a s t x x') = (term428 _103141 _103145 a s t x x').
Proof. exact (MK_COMB (@lem4294643 _103141) (@lem4294642 _103141 _103145 a s t x x')). Qed.
Lemma lem4294645 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term232 _103141 _103145 a s t x) = (term429 _103141 _103145 a s t x).
Proof. exact (fun_ext (fun x' : _103145 => @lem4294644 _103141 _103145 a s t x x')). Qed.
Lemma lem4294646 {_103145 : Type'} : (@all _103145) = (@all _103145).
Proof. exact (eq_refl (@all _103145)). Qed.
Lemma lem4294648 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term233 _103141 _103145 a s t x) = (term430 _103141 _103145 a s t x).
Proof. exact (MK_COMB (@lem4294646 _103145) (@lem4294645 _103141 _103145 a s t x)). Qed.
Lemma lem4294649 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x' : _103145) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) (h1 : term375 _103141 _103145 s x' x t a y) : term430 _103141 _103145 a s t x.
Proof. exact (EQ_MP (@lem4294648 _103141 _103145 a s t x) (@lem4294509 _103141 _103145 s x' x t a y h1)). Qed.
Lemma lem4294663 {_103141 _103145 : Type'} (x : prod _103145 _103141) (x' : _103145) (y : _103141) : (term212 _103141 _103145 x x' y) = (term212 _103141 _103145 x x' y).
Proof. exact (eq_refl (term212 _103141 _103145 x x' y)). Qed.
Lemma lem4294680 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : _103145) (y : _103141) : (term210 _103141 _103145 a s t x y) = (term420 _103141 _103145 a s t x y).
Proof. exact (@lem19699 (term421 _103145 x a) (term422 _103145 s x) (term206 _103141 _103145 t x y)). Qed.
Lemma lem4294681 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4294682 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : _103145) (y : _103141) : (term214 _103141 _103145 a s t x y) = (term423 _103141 _103145 a s t x y).
Proof. exact (MK_COMB (@lem4294681) (@lem4294680 _103141 _103145 a s t x y)). Qed.
Lemma lem4294683 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) : (term216 _103141 _103145 a s t x x' y) = (term424 _103141 _103145 a s t x x' y).
Proof. exact (MK_COMB (@lem4294682 _103141 _103145 a s t x' y) (@lem4294663 _103141 _103145 x x' y)). Qed.
Lemma lem4294690 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) : (term424 _103141 _103145 a s t x x' y) = (term425 _103141 _103145 a s t x x' y).
Proof. exact (@lem19699 (term426 _103141 _103145 a t x' y) (term235 _103141 _103145 s t x' y) (term212 _103141 _103145 x x' y)). Qed.
Lemma lem4294691 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) : (term216 _103141 _103145 a s t x x' y) = (term425 _103141 _103145 a s t x x' y).
Proof. exact (TRANS (@lem4294683 _103141 _103145 a s t x x' y) (@lem4294690 _103141 _103145 a s t x x' y)). Qed.
Lemma lem4294692 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) : (term225 _103141 _103145 a s t x x') = (term427 _103141 _103145 a s t x x').
Proof. exact (fun_ext (fun y : _103141 => @lem4294691 _103141 _103145 a s t x x' y)). Qed.
Lemma lem4294693 {_103141 : Type'} : (@all _103141) = (@all _103141).
Proof. exact (eq_refl (@all _103141)). Qed.
Lemma lem4294694 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) : (term226 _103141 _103145 a s t x x') = (term428 _103141 _103145 a s t x x').
Proof. exact (MK_COMB (@lem4294693 _103141) (@lem4294692 _103141 _103145 a s t x x')). Qed.
Lemma lem4294695 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term232 _103141 _103145 a s t x) = (term429 _103141 _103145 a s t x).
Proof. exact (fun_ext (fun x' : _103145 => @lem4294694 _103141 _103145 a s t x x')). Qed.
Lemma lem4294696 {_103145 : Type'} : (@all _103145) = (@all _103145).
Proof. exact (eq_refl (@all _103145)). Qed.
Lemma lem4294698 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) : (term233 _103141 _103145 a s t x) = (term430 _103141 _103145 a s t x).
Proof. exact (MK_COMB (@lem4294696 _103145) (@lem4294695 _103141 _103145 a s t x)). Qed.
Lemma lem4294699 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x' : _103145) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) (h1 : term375 _103141 _103145 s x' x t a y) : term430 _103141 _103145 a s t x.
Proof. exact (EQ_MP (@lem4294698 _103141 _103145 a s t x) (@lem4294509 _103141 _103145 s x' x t a y h1)). Qed.
Lemma lem4294714 {_103141 _103145 : Type'} (_48688 : _103141) (x' : _103145) (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (h1 : term306 _103141 _103145 x' y s x t a) : term431 _103141 _103145 x t a _48688.
Proof. exact (@lem4294552 _103141 _103145 x' y s x t a h1 _48688). Qed.
Lemma lem4294715 {_103141 _103145 : Type'} (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (_48688 : _103141) : (term431 _103141 _103145 x t a _48688) = (term256 _103141 _103145 x t a _48688).
Proof. exact (eq_refl (term431 _103141 _103145 x t a _48688)). Qed.
Lemma lem4294717 {_103141 _103145 : Type'} (_48689 : _103145) (x' : _103145) (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (h1 : term306 _103141 _103145 x' y s x t a) : term432 _103141 _103145 s t x _48689.
Proof. exact (@lem4294586 _103141 _103145 x' y s x t a h1 _48689). Qed.
Lemma lem4294718 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (_48689 : _103145) : (term432 _103141 _103145 s t x _48689) = (term247 _103141 _103145 s t x _48689).
Proof. exact (eq_refl (term432 _103141 _103145 s t x _48689)). Qed.
Lemma lem4294719 {_103141 _103145 : Type'} (_48689 : _103145) (x' : _103145) (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (h1 : term306 _103141 _103145 x' y s x t a) : term247 _103141 _103145 s t x _48689.
Proof. exact (EQ_MP (@lem4294718 _103141 _103145 s t x _48689) (@lem4294717 _103141 _103145 _48689 x' y s x t a h1)). Qed.
Lemma lem4294720 {_103141 _103145 : Type'} (_48689 : _103145) (_48690 : _103141) (x' : _103145) (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (h1 : term306 _103141 _103145 x' y s x t a) : term433 _103141 _103145 s t x _48689 _48690.
Proof. exact (@lem4294719 _103141 _103145 _48689 x' y s x t a h1 _48690). Qed.
Lemma lem4294721 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (_48689 : _103145) (_48690 : _103141) : (term433 _103141 _103145 s t x _48689 _48690) = (term239 _103141 _103145 s t x _48689 _48690).
Proof. exact (eq_refl (term433 _103141 _103145 s t x _48689 _48690)). Qed.
Lemma lem4294722 {_103141 _103145 : Type'} (_48689 : _103145) (_48690 : _103141) (x' : _103145) (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (h1 : term306 _103141 _103145 x' y s x t a) : term239 _103141 _103145 s t x _48689 _48690.
Proof. exact (EQ_MP (@lem4294721 _103141 _103145 s t x _48689 _48690) (@lem4294720 _103141 _103145 _48689 _48690 x' y s x t a h1)). Qed.
Lemma lem4294726 {_103141 _103145 : Type'} (_48692 : _103145) (s : _103145 -> Prop) (x' : _103145) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) (h1 : term375 _103141 _103145 s x' x t a y) : term434 _103141 _103145 a s t x _48692.
Proof. exact (@lem4294649 _103141 _103145 s x' x t a y h1 _48692). Qed.
Lemma lem4294727 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (_48692 : _103145) : (term434 _103141 _103145 a s t x _48692) = (term428 _103141 _103145 a s t x _48692).
Proof. exact (eq_refl (term434 _103141 _103145 a s t x _48692)). Qed.
Lemma lem4294728 {_103141 _103145 : Type'} (_48692 : _103145) (s : _103145 -> Prop) (x' : _103145) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) (h1 : term375 _103141 _103145 s x' x t a y) : term428 _103141 _103145 a s t x _48692.
Proof. exact (EQ_MP (@lem4294727 _103141 _103145 a s t x _48692) (@lem4294726 _103141 _103145 _48692 s x' x t a y h1)). Qed.
Lemma lem4294729 {_103141 _103145 : Type'} (_48692 : _103145) (_48693 : _103141) (s : _103145 -> Prop) (x' : _103145) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) (h1 : term375 _103141 _103145 s x' x t a y) : term435 _103141 _103145 a s t x _48692 _48693.
Proof. exact (@lem4294728 _103141 _103145 _48692 s x' x t a y h1 _48693). Qed.
Lemma lem4294730 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (_48692 : _103145) (_48693 : _103141) : (term435 _103141 _103145 a s t x _48692 _48693) = (term425 _103141 _103145 a s t x _48692 _48693).
Proof. exact (eq_refl (term435 _103141 _103145 a s t x _48692 _48693)). Qed.
Lemma lem4294731 {_103141 _103145 : Type'} (_48692 : _103145) (_48693 : _103141) (s : _103145 -> Prop) (x' : _103145) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) (h1 : term375 _103141 _103145 s x' x t a y) : term425 _103141 _103145 a s t x _48692 _48693.
Proof. exact (EQ_MP (@lem4294730 _103141 _103145 a s t x _48692 _48693) (@lem4294729 _103141 _103145 _48692 _48693 s x' x t a y h1)). Qed.
Lemma lem4294732 {_103141 _103145 : Type'} (_48694 : _103145) (s : _103145 -> Prop) (x' : _103145) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) (h1 : term375 _103141 _103145 s x' x t a y) : term434 _103141 _103145 a s t x _48694.
Proof. exact (@lem4294699 _103141 _103145 s x' x t a y h1 _48694). Qed.
Lemma lem4294733 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (_48694 : _103145) : (term434 _103141 _103145 a s t x _48694) = (term428 _103141 _103145 a s t x _48694).
Proof. exact (eq_refl (term434 _103141 _103145 a s t x _48694)). Qed.
Lemma lem4294734 {_103141 _103145 : Type'} (_48694 : _103145) (s : _103145 -> Prop) (x' : _103145) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) (h1 : term375 _103141 _103145 s x' x t a y) : term428 _103141 _103145 a s t x _48694.
Proof. exact (EQ_MP (@lem4294733 _103141 _103145 a s t x _48694) (@lem4294732 _103141 _103145 _48694 s x' x t a y h1)). Qed.
Lemma lem4294735 {_103141 _103145 : Type'} (_48694 : _103145) (_48695 : _103141) (s : _103145 -> Prop) (x' : _103145) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) (h1 : term375 _103141 _103145 s x' x t a y) : term435 _103141 _103145 a s t x _48694 _48695.
Proof. exact (@lem4294734 _103141 _103145 _48694 s x' x t a y h1 _48695). Qed.
Lemma lem4294736 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (_48694 : _103145) (_48695 : _103141) : (term435 _103141 _103145 a s t x _48694 _48695) = (term425 _103141 _103145 a s t x _48694 _48695).
Proof. exact (eq_refl (term435 _103141 _103145 a s t x _48694 _48695)). Qed.
Lemma lem4294737 {_103141 _103145 : Type'} (_48694 : _103145) (_48695 : _103141) (s : _103145 -> Prop) (x' : _103145) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) (h1 : term375 _103141 _103145 s x' x t a y) : term425 _103141 _103145 a s t x _48694 _48695.
Proof. exact (EQ_MP (@lem4294736 _103141 _103145 a s t x _48694 _48695) (@lem4294735 _103141 _103145 _48694 _48695 s x' x t a y h1)). Qed.
Lemma lem4294738 {_103141 _103145 : Type'} (_48692 : _103145) (_48693 : _103141) (s : _103145 -> Prop) (x' : _103145) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) (h1 : term375 _103141 _103145 s x' x t a y) : term239 _103141 _103145 s t x _48692 _48693.
Proof. exact (proj2 (@lem4294731 _103141 _103145 _48692 _48693 s x' x t a y h1)). Qed.
Lemma lem4294741 {_103141 _103145 : Type'} (_48694 : _103145) (_48695 : _103141) (s : _103145 -> Prop) (x' : _103145) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) (h1 : term375 _103141 _103145 s x' x t a y) : term436 _103141 _103145 a t x _48694 _48695.
Proof. exact (proj1 (@lem4294737 _103141 _103145 _48694 _48695 s x' x t a y h1)). Qed.
Lemma lem4294761 {_103141 _103145 : Type'} (x' : _103145) (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (h1 : term306 _103141 _103145 x' y s x t a) : x = (@pair _103145 _103141 x' y).
Proof. exact (proj2 (@lem4294499 _103141 _103145 x' y s x t a h1)). Qed.
Lemma lem4294763 {_103141 _103145 : Type'} (x' : _103145) (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (h1 : term306 _103141 _103145 x' y s x t a) : t x' y.
Proof. exact (proj2 (@lem4294503 _103141 _103145 x' y s x t a h1)). Qed.
Lemma lem4294765 {_103145 : Type'} (x' : _103145) (a : _103145) (h1 : x' = a) : x' = a.
Proof. exact (h1). Qed.
Lemma lem4294776 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (_48689 : _103145) (_48690 : _103141) : (term239 _103141 _103145 s t x _48689 _48690) = (term437 _103141 _103145 s t x _48689 _48690).
Proof. exact (@lem4292910 (term422 _103145 s _48689) (term206 _103141 _103145 t _48689 _48690) (term212 _103141 _103145 x _48689 _48690)). Qed.
Lemma lem4294777 {_103141 _103145 : Type'} (_48689 : _103145) (_48690 : _103141) (x' : _103145) (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (h1 : term306 _103141 _103145 x' y s x t a) : term437 _103141 _103145 s t x _48689 _48690.
Proof. exact (EQ_MP (@lem4294776 _103141 _103145 s t x _48689 _48690) (@lem4294722 _103141 _103145 _48689 _48690 x' y s x t a h1)). Qed.
Lemma lem4294785 {_103141 _103145 : Type'} (x' : _103145) (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (h1 : term306 _103141 _103145 x' y s x t a) : x = (@pair _103145 _103141 x' y).
Proof. exact (proj2 (@lem4294499 _103141 _103145 x' y s x t a h1)). Qed.
Lemma lem4294789 {_103145 : Type'} (s : _103145 -> Prop) (x' : _103145) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem4294791 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) (h1 : term150 _103141 _103145 s t x x' y) : x = (@pair _103145 _103141 x' y).
Proof. exact (proj2 (@lem4294510 _103141 _103145 s t x x' y h1)). Qed.
Lemma lem4294818 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (_48692 : _103145) (_48693 : _103141) : (term239 _103141 _103145 s t x _48692 _48693) = (term437 _103141 _103145 s t x _48692 _48693).
Proof. exact (@lem4292910 (term422 _103145 s _48692) (term206 _103141 _103145 t _48692 _48693) (term212 _103141 _103145 x _48692 _48693)). Qed.
Lemma lem4294819 {_103141 _103145 : Type'} (_48692 : _103145) (_48693 : _103141) (s : _103145 -> Prop) (x' : _103145) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) (h1 : term375 _103141 _103145 s x' x t a y) : term437 _103141 _103145 s t x _48692 _48693.
Proof. exact (EQ_MP (@lem4294818 _103141 _103145 s t x _48692 _48693) (@lem4294738 _103141 _103145 _48692 _48693 s x' x t a y h1)). Qed.
Lemma lem4294821 {_103141 _103145 : Type'} (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) (h1 : term174 _103141 _103145 x t a y) : x = (@pair _103145 _103141 a y).
Proof. exact (proj1 (@lem4294511 _103141 _103145 x t a y h1)). Qed.
Lemma lem4294834 {_103141 _103145 : Type'} (a : _103145) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (_48694 : _103145) (_48695 : _103141) : (term436 _103141 _103145 a t x _48694 _48695) = (term438 _103141 _103145 a t x _48694 _48695).
Proof. exact (@lem4292910 (term421 _103145 _48694 a) (term206 _103141 _103145 t _48694 _48695) (term212 _103141 _103145 x _48694 _48695)). Qed.
Lemma lem4294835 {_103141 _103145 : Type'} (_48694 : _103145) (_48695 : _103141) (s : _103145 -> Prop) (x' : _103145) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) (h1 : term375 _103141 _103145 s x' x t a y) : term438 _103141 _103145 a t x _48694 _48695.
Proof. exact (EQ_MP (@lem4294834 _103141 _103145 a t x _48694 _48695) (@lem4294741 _103141 _103145 _48694 _48695 s x' x t a y h1)). Qed.
Lemma lem4294889 {_103141 _103145 : Type'} (_48688 : _103141) (x' : _103145) (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (h1 : term306 _103141 _103145 x' y s x t a) : term256 _103141 _103145 x t a _48688.
Proof. exact (EQ_MP (@lem4294715 _103141 _103145 x t a _48688) (@lem4294714 _103141 _103145 _48688 x' y s x t a h1)). Qed.
Lemma lem4294890 {_103141 _103145 : Type'} (x : prod _103145 _103141) (y : _103141) : (term439 _103141 _103145 x y) = (term439 _103141 _103145 x y).
Proof. exact (eq_refl (term439 _103141 _103145 x y)). Qed.
Lemma lem4294891 {_103141 _103145 : Type'} (x : prod _103145 _103141) (y : _103141) (x' : _103145) (a : _103145) (h1 : x' = a) : (term440 _103141 _103145 x y x') = (term440 _103141 _103145 x y a).
Proof. exact (MK_COMB (@lem4294890 _103141 _103145 x y) (@lem4294765 _103145 x' a h1)). Qed.
Lemma lem4294892 {_103141 _103145 : Type'} (x : prod _103145 _103141) (a : _103145) (y : _103141) : (term440 _103141 _103145 x y a) = (x = (@pair _103145 _103141 a y)).
Proof. exact (eq_refl (term440 _103141 _103145 x y a)). Qed.
Lemma lem4294893 {_103141 _103145 : Type'} (x : prod _103145 _103141) (y : _103141) (x' : _103145) : (term441 _103141 _103145 x y x') = (term441 _103141 _103145 x y x').
Proof. exact (eq_refl (term441 _103141 _103145 x y x')). Qed.
Lemma lem4294894 {_103141 _103145 : Type'} (x' : _103145) (x : prod _103145 _103141) (a : _103145) (y : _103141) : ((term440 _103141 _103145 x y x') = (term440 _103141 _103145 x y a)) = ((term440 _103141 _103145 x y x') = (x = (@pair _103145 _103141 a y))).
Proof. exact (MK_COMB (@lem4294893 _103141 _103145 x y x') (@lem4294892 _103141 _103145 x a y)). Qed.
Lemma lem4294895 {_103141 _103145 : Type'} (x : prod _103145 _103141) (x' : _103145) (y : _103141) : (term440 _103141 _103145 x y x') = (x = (@pair _103145 _103141 x' y)).
Proof. exact (eq_refl (term440 _103141 _103145 x y x')). Qed.
Lemma lem4294896 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4294897 {_103141 _103145 : Type'} (x : prod _103145 _103141) (x' : _103145) (y : _103141) : (term441 _103141 _103145 x y x') = (term442 _103141 _103145 x x' y).
Proof. exact (MK_COMB (@lem4294896) (@lem4294895 _103141 _103145 x x' y)). Qed.
Lemma lem4294898 {_103141 _103145 : Type'} (x : prod _103145 _103141) (a : _103145) (y : _103141) : (x = (@pair _103145 _103141 a y)) = (x = (@pair _103145 _103141 a y)).
Proof. exact (eq_refl (x = (@pair _103145 _103141 a y))). Qed.
Lemma lem4294899 {_103141 _103145 : Type'} (x' : _103145) (x : prod _103145 _103141) (a : _103145) (y : _103141) : ((term440 _103141 _103145 x y x') = (x = (@pair _103145 _103141 a y))) = ((x = (@pair _103145 _103141 x' y)) = (x = (@pair _103145 _103141 a y))).
Proof. exact (MK_COMB (@lem4294897 _103141 _103145 x x' y) (@lem4294898 _103141 _103145 x a y)). Qed.
Lemma lem4294900 {_103141 _103145 : Type'} (x' : _103145) (x : prod _103145 _103141) (a : _103145) (y : _103141) : ((term440 _103141 _103145 x y x') = (term440 _103141 _103145 x y a)) = ((x = (@pair _103145 _103141 x' y)) = (x = (@pair _103145 _103141 a y))).
Proof. exact (TRANS (@lem4294894 _103141 _103145 x' x a y) (@lem4294899 _103141 _103145 x' x a y)). Qed.
Lemma lem4294901 {_103141 _103145 : Type'} (x : prod _103145 _103141) (y : _103141) (x' : _103145) (a : _103145) (h1 : x' = a) : (x = (@pair _103145 _103141 x' y)) = (x = (@pair _103145 _103141 a y)).
Proof. exact (EQ_MP (@lem4294900 _103141 _103145 x' x a y) (@lem4294891 _103141 _103145 x y x' a h1)). Qed.
Lemma lem4294902 {_103141 _103145 : Type'} (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (x' : _103145) (a : _103145) (h1 : term306 _103141 _103145 x' y s x t a) (h2 : x' = a) : x = (@pair _103145 _103141 a y).
Proof. exact (EQ_MP (@lem4294901 _103141 _103145 x y x' a h2) (@lem4294761 _103141 _103145 x' y s x t a h1)). Qed.
Lemma lem4294903 {_103141 _103145 : Type'} (t : type1470 _103141 _103145) (y : _103141) : (term443 _103141 _103145 t y) = (term443 _103141 _103145 t y).
Proof. exact (eq_refl (term443 _103141 _103145 t y)). Qed.
Lemma lem4294904 {_103141 _103145 : Type'} (t : type1470 _103141 _103145) (y : _103141) (x' : _103145) (a : _103145) (h1 : x' = a) : (term444 _103141 _103145 t y x') = (term444 _103141 _103145 t y a).
Proof. exact (MK_COMB (@lem4294903 _103141 _103145 t y) (@lem4294765 _103145 x' a h1)). Qed.
Lemma lem4294905 {_103141 _103145 : Type'} (t : type1470 _103141 _103145) (a : _103145) (y : _103141) : (term444 _103141 _103145 t y a) = (t a y).
Proof. exact (eq_refl (term444 _103141 _103145 t y a)). Qed.
Lemma lem4294906 {_103141 _103145 : Type'} (t : type1470 _103141 _103145) (y : _103141) (x' : _103145) : (term445 _103141 _103145 t y x') = (term445 _103141 _103145 t y x').
Proof. exact (eq_refl (term445 _103141 _103145 t y x')). Qed.
Lemma lem4294907 {_103141 _103145 : Type'} (x' : _103145) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) : ((term444 _103141 _103145 t y x') = (term444 _103141 _103145 t y a)) = ((term444 _103141 _103145 t y x') = (t a y)).
Proof. exact (MK_COMB (@lem4294906 _103141 _103145 t y x') (@lem4294905 _103141 _103145 t a y)). Qed.
Lemma lem4294908 {_103141 _103145 : Type'} (t : type1470 _103141 _103145) (x' : _103145) (y : _103141) : (term444 _103141 _103145 t y x') = (t x' y).
Proof. exact (eq_refl (term444 _103141 _103145 t y x')). Qed.
Lemma lem4294909 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4294910 {_103141 _103145 : Type'} (t : type1470 _103141 _103145) (x' : _103145) (y : _103141) : (term445 _103141 _103145 t y x') = (term446 _103141 _103145 t x' y).
Proof. exact (MK_COMB (@lem4294909) (@lem4294908 _103141 _103145 t x' y)). Qed.
Lemma lem4294911 {_103141 _103145 : Type'} (t : type1470 _103141 _103145) (a : _103145) (y : _103141) : (t a y) = (t a y).
Proof. exact (eq_refl (t a y)). Qed.
Lemma lem4294912 {_103141 _103145 : Type'} (x' : _103145) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) : ((term444 _103141 _103145 t y x') = (t a y)) = ((t x' y) = (t a y)).
Proof. exact (MK_COMB (@lem4294910 _103141 _103145 t x' y) (@lem4294911 _103141 _103145 t a y)). Qed.
Lemma lem4294913 {_103141 _103145 : Type'} (x' : _103145) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) : ((term444 _103141 _103145 t y x') = (term444 _103141 _103145 t y a)) = ((t x' y) = (t a y)).
Proof. exact (TRANS (@lem4294907 _103141 _103145 x' t a y) (@lem4294912 _103141 _103145 x' t a y)). Qed.
Lemma lem4294914 {_103141 _103145 : Type'} (t : type1470 _103141 _103145) (y : _103141) (x' : _103145) (a : _103145) (h1 : x' = a) : (t x' y) = (t a y).
Proof. exact (EQ_MP (@lem4294913 _103141 _103145 x' t a y) (@lem4294904 _103141 _103145 t y x' a h1)). Qed.
Lemma lem4294943 {_103141 _103145 : Type'} (t : type1470 _103141 _103145) (a : _103145) (_48688 : _103141) : (term447 _103141 _103145 t a _48688) = (term447 _103141 _103145 t a _48688).
Proof. exact (eq_refl (term447 _103141 _103145 t a _48688)). Qed.
Lemma lem4294944 {_103141 _103145 : Type'} (_48688 : _103141) (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (x' : _103145) (a : _103145) (h1 : term306 _103141 _103145 x' y s x t a) (h2 : x' = a) : (term448 _103141 _103145 t a _48688 x) = (term449 _103141 _103145 t _48688 a y).
Proof. exact (MK_COMB (@lem4294943 _103141 _103145 t a _48688) (@lem4294902 _103141 _103145 y s x t x' a h1 h2)). Qed.
Lemma lem4294945 {_103141 _103145 : Type'} (y : _103141) (t : type1470 _103141 _103145) (a : _103145) (_48688 : _103141) : (term449 _103141 _103145 t _48688 a y) = (term450 _103141 _103145 y t a _48688).
Proof. exact (eq_refl (term449 _103141 _103145 t _48688 a y)). Qed.
Lemma lem4294946 {_103141 _103145 : Type'} (t : type1470 _103141 _103145) (a : _103145) (_48688 : _103141) (x : prod _103145 _103141) : (term451 _103141 _103145 t a _48688 x) = (term451 _103141 _103145 t a _48688 x).
Proof. exact (eq_refl (term451 _103141 _103145 t a _48688 x)). Qed.
Lemma lem4294947 {_103141 _103145 : Type'} (x : prod _103145 _103141) (y : _103141) (t : type1470 _103141 _103145) (a : _103145) (_48688 : _103141) : ((term448 _103141 _103145 t a _48688 x) = (term449 _103141 _103145 t _48688 a y)) = ((term448 _103141 _103145 t a _48688 x) = (term450 _103141 _103145 y t a _48688)).
Proof. exact (MK_COMB (@lem4294946 _103141 _103145 t a _48688 x) (@lem4294945 _103141 _103145 y t a _48688)). Qed.
Lemma lem4294948 {_103141 _103145 : Type'} (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (_48688 : _103141) : (term448 _103141 _103145 t a _48688 x) = (term256 _103141 _103145 x t a _48688).
Proof. exact (eq_refl (term448 _103141 _103145 t a _48688 x)). Qed.
Lemma lem4294949 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4294950 {_103141 _103145 : Type'} (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (_48688 : _103141) : (term451 _103141 _103145 t a _48688 x) = (term452 _103141 _103145 x t a _48688).
Proof. exact (MK_COMB (@lem4294949) (@lem4294948 _103141 _103145 x t a _48688)). Qed.
Lemma lem4294951 {_103141 _103145 : Type'} (y : _103141) (t : type1470 _103141 _103145) (a : _103145) (_48688 : _103141) : (term450 _103141 _103145 y t a _48688) = (term450 _103141 _103145 y t a _48688).
Proof. exact (eq_refl (term450 _103141 _103145 y t a _48688)). Qed.
Lemma lem4294952 {_103141 _103145 : Type'} (x : prod _103145 _103141) (y : _103141) (t : type1470 _103141 _103145) (a : _103145) (_48688 : _103141) : ((term448 _103141 _103145 t a _48688 x) = (term450 _103141 _103145 y t a _48688)) = ((term256 _103141 _103145 x t a _48688) = (term450 _103141 _103145 y t a _48688)).
Proof. exact (MK_COMB (@lem4294950 _103141 _103145 x t a _48688) (@lem4294951 _103141 _103145 y t a _48688)). Qed.
Lemma lem4294953 {_103141 _103145 : Type'} (x : prod _103145 _103141) (y : _103141) (t : type1470 _103141 _103145) (a : _103145) (_48688 : _103141) : ((term448 _103141 _103145 t a _48688 x) = (term449 _103141 _103145 t _48688 a y)) = ((term256 _103141 _103145 x t a _48688) = (term450 _103141 _103145 y t a _48688)).
Proof. exact (TRANS (@lem4294947 _103141 _103145 x y t a _48688) (@lem4294952 _103141 _103145 x y t a _48688)). Qed.
Lemma lem4294954 {_103141 _103145 : Type'} (_48688 : _103141) (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (x' : _103145) (a : _103145) (h1 : term306 _103141 _103145 x' y s x t a) (h2 : x' = a) : (term256 _103141 _103145 x t a _48688) = (term450 _103141 _103145 y t a _48688).
Proof. exact (EQ_MP (@lem4294953 _103141 _103145 x y t a _48688) (@lem4294944 _103141 _103145 _48688 y s x t x' a h1 h2)). Qed.
Lemma lem4294955 {_103141 _103145 : Type'} (_48688 : _103141) (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (x' : _103145) (a : _103145) (h1 : term306 _103141 _103145 x' y s x t a) (h2 : x' = a) : term450 _103141 _103145 y t a _48688.
Proof. exact (EQ_MP (@lem4294954 _103141 _103145 _48688 y s x t x' a h1 h2) (@lem4294889 _103141 _103145 _48688 x' y s x t a h1)). Qed.
Lemma lem4294984 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (_48689 : _103145) (_48690 : _103141) : (term453 _103141 _103145 s t _48689 _48690) = (term453 _103141 _103145 s t _48689 _48690).
Proof. exact (eq_refl (term453 _103141 _103145 s t _48689 _48690)). Qed.
Lemma lem4294985 {_103141 _103145 : Type'} (_48689 : _103145) (_48690 : _103141) (x' : _103145) (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (h1 : term306 _103141 _103145 x' y s x t a) : (term454 _103141 _103145 s t _48689 _48690 x) = (term455 _103141 _103145 s t _48689 _48690 x' y).
Proof. exact (MK_COMB (@lem4294984 _103141 _103145 s t _48689 _48690) (@lem4294785 _103141 _103145 x' y s x t a h1)). Qed.
Lemma lem4294986 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x' : _103145) (y : _103141) (_48689 : _103145) (_48690 : _103141) : (term455 _103141 _103145 s t _48689 _48690 x' y) = (term456 _103141 _103145 s t x' y _48689 _48690).
Proof. exact (eq_refl (term455 _103141 _103145 s t _48689 _48690 x' y)). Qed.
Lemma lem4294987 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (_48689 : _103145) (_48690 : _103141) (x : prod _103145 _103141) : (term457 _103141 _103145 s t _48689 _48690 x) = (term457 _103141 _103145 s t _48689 _48690 x).
Proof. exact (eq_refl (term457 _103141 _103145 s t _48689 _48690 x)). Qed.
Lemma lem4294988 {_103141 _103145 : Type'} (x : prod _103145 _103141) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x' : _103145) (y : _103141) (_48689 : _103145) (_48690 : _103141) : ((term454 _103141 _103145 s t _48689 _48690 x) = (term455 _103141 _103145 s t _48689 _48690 x' y)) = ((term454 _103141 _103145 s t _48689 _48690 x) = (term456 _103141 _103145 s t x' y _48689 _48690)).
Proof. exact (MK_COMB (@lem4294987 _103141 _103145 s t _48689 _48690 x) (@lem4294986 _103141 _103145 s t x' y _48689 _48690)). Qed.
Lemma lem4294989 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (_48689 : _103145) (_48690 : _103141) : (term454 _103141 _103145 s t _48689 _48690 x) = (term437 _103141 _103145 s t x _48689 _48690).
Proof. exact (eq_refl (term454 _103141 _103145 s t _48689 _48690 x)). Qed.
Lemma lem4294990 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4294991 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (_48689 : _103145) (_48690 : _103141) : (term457 _103141 _103145 s t _48689 _48690 x) = (term458 _103141 _103145 s t x _48689 _48690).
Proof. exact (MK_COMB (@lem4294990) (@lem4294989 _103141 _103145 s t x _48689 _48690)). Qed.
Lemma lem4294992 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x' : _103145) (y : _103141) (_48689 : _103145) (_48690 : _103141) : (term456 _103141 _103145 s t x' y _48689 _48690) = (term456 _103141 _103145 s t x' y _48689 _48690).
Proof. exact (eq_refl (term456 _103141 _103145 s t x' y _48689 _48690)). Qed.
Lemma lem4294993 {_103141 _103145 : Type'} (x : prod _103145 _103141) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x' : _103145) (y : _103141) (_48689 : _103145) (_48690 : _103141) : ((term454 _103141 _103145 s t _48689 _48690 x) = (term456 _103141 _103145 s t x' y _48689 _48690)) = ((term437 _103141 _103145 s t x _48689 _48690) = (term456 _103141 _103145 s t x' y _48689 _48690)).
Proof. exact (MK_COMB (@lem4294991 _103141 _103145 s t x _48689 _48690) (@lem4294992 _103141 _103145 s t x' y _48689 _48690)). Qed.
Lemma lem4294994 {_103141 _103145 : Type'} (x : prod _103145 _103141) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x' : _103145) (y : _103141) (_48689 : _103145) (_48690 : _103141) : ((term454 _103141 _103145 s t _48689 _48690 x) = (term455 _103141 _103145 s t _48689 _48690 x' y)) = ((term437 _103141 _103145 s t x _48689 _48690) = (term456 _103141 _103145 s t x' y _48689 _48690)).
Proof. exact (TRANS (@lem4294988 _103141 _103145 x s t x' y _48689 _48690) (@lem4294993 _103141 _103145 x s t x' y _48689 _48690)). Qed.
Lemma lem4294995 {_103141 _103145 : Type'} (_48689 : _103145) (_48690 : _103141) (x' : _103145) (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (h1 : term306 _103141 _103145 x' y s x t a) : (term437 _103141 _103145 s t x _48689 _48690) = (term456 _103141 _103145 s t x' y _48689 _48690).
Proof. exact (EQ_MP (@lem4294994 _103141 _103145 x s t x' y _48689 _48690) (@lem4294985 _103141 _103145 _48689 _48690 x' y s x t a h1)). Qed.
Lemma lem4294996 {_103141 _103145 : Type'} (_48689 : _103145) (_48690 : _103141) (x' : _103145) (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (h1 : term306 _103141 _103145 x' y s x t a) : term456 _103141 _103145 s t x' y _48689 _48690.
Proof. exact (EQ_MP (@lem4294995 _103141 _103145 _48689 _48690 x' y s x t a h1) (@lem4294777 _103141 _103145 _48689 _48690 x' y s x t a h1)). Qed.
Lemma lem4295037 {_103145 : Type'} (s : _103145 -> Prop) (x' : _103145) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem4295093 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (_48692 : _103145) (_48693 : _103141) : (term453 _103141 _103145 s t _48692 _48693) = (term453 _103141 _103145 s t _48692 _48693).
Proof. exact (eq_refl (term453 _103141 _103145 s t _48692 _48693)). Qed.
Lemma lem4295094 {_103141 _103145 : Type'} (_48692 : _103145) (_48693 : _103141) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) (h1 : term150 _103141 _103145 s t x x' y) : (term454 _103141 _103145 s t _48692 _48693 x) = (term455 _103141 _103145 s t _48692 _48693 x' y).
Proof. exact (MK_COMB (@lem4295093 _103141 _103145 s t _48692 _48693) (@lem4294791 _103141 _103145 s t x x' y h1)). Qed.
Lemma lem4295095 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x' : _103145) (y : _103141) (_48692 : _103145) (_48693 : _103141) : (term455 _103141 _103145 s t _48692 _48693 x' y) = (term456 _103141 _103145 s t x' y _48692 _48693).
Proof. exact (eq_refl (term455 _103141 _103145 s t _48692 _48693 x' y)). Qed.
Lemma lem4295096 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (_48692 : _103145) (_48693 : _103141) (x : prod _103145 _103141) : (term457 _103141 _103145 s t _48692 _48693 x) = (term457 _103141 _103145 s t _48692 _48693 x).
Proof. exact (eq_refl (term457 _103141 _103145 s t _48692 _48693 x)). Qed.
Lemma lem4295097 {_103141 _103145 : Type'} (x : prod _103145 _103141) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x' : _103145) (y : _103141) (_48692 : _103145) (_48693 : _103141) : ((term454 _103141 _103145 s t _48692 _48693 x) = (term455 _103141 _103145 s t _48692 _48693 x' y)) = ((term454 _103141 _103145 s t _48692 _48693 x) = (term456 _103141 _103145 s t x' y _48692 _48693)).
Proof. exact (MK_COMB (@lem4295096 _103141 _103145 s t _48692 _48693 x) (@lem4295095 _103141 _103145 s t x' y _48692 _48693)). Qed.
Lemma lem4295098 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (_48692 : _103145) (_48693 : _103141) : (term454 _103141 _103145 s t _48692 _48693 x) = (term437 _103141 _103145 s t x _48692 _48693).
Proof. exact (eq_refl (term454 _103141 _103145 s t _48692 _48693 x)). Qed.
Lemma lem4295099 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4295100 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (_48692 : _103145) (_48693 : _103141) : (term457 _103141 _103145 s t _48692 _48693 x) = (term458 _103141 _103145 s t x _48692 _48693).
Proof. exact (MK_COMB (@lem4295099) (@lem4295098 _103141 _103145 s t x _48692 _48693)). Qed.
Lemma lem4295101 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x' : _103145) (y : _103141) (_48692 : _103145) (_48693 : _103141) : (term456 _103141 _103145 s t x' y _48692 _48693) = (term456 _103141 _103145 s t x' y _48692 _48693).
Proof. exact (eq_refl (term456 _103141 _103145 s t x' y _48692 _48693)). Qed.
Lemma lem4295102 {_103141 _103145 : Type'} (x : prod _103145 _103141) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x' : _103145) (y : _103141) (_48692 : _103145) (_48693 : _103141) : ((term454 _103141 _103145 s t _48692 _48693 x) = (term456 _103141 _103145 s t x' y _48692 _48693)) = ((term437 _103141 _103145 s t x _48692 _48693) = (term456 _103141 _103145 s t x' y _48692 _48693)).
Proof. exact (MK_COMB (@lem4295100 _103141 _103145 s t x _48692 _48693) (@lem4295101 _103141 _103145 s t x' y _48692 _48693)). Qed.
Lemma lem4295103 {_103141 _103145 : Type'} (x : prod _103145 _103141) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x' : _103145) (y : _103141) (_48692 : _103145) (_48693 : _103141) : ((term454 _103141 _103145 s t _48692 _48693 x) = (term455 _103141 _103145 s t _48692 _48693 x' y)) = ((term437 _103141 _103145 s t x _48692 _48693) = (term456 _103141 _103145 s t x' y _48692 _48693)).
Proof. exact (TRANS (@lem4295097 _103141 _103145 x s t x' y _48692 _48693) (@lem4295102 _103141 _103145 x s t x' y _48692 _48693)). Qed.
Lemma lem4295104 {_103141 _103145 : Type'} (_48692 : _103145) (_48693 : _103141) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) (h1 : term150 _103141 _103145 s t x x' y) : (term437 _103141 _103145 s t x _48692 _48693) = (term456 _103141 _103145 s t x' y _48692 _48693).
Proof. exact (EQ_MP (@lem4295103 _103141 _103145 x s t x' y _48692 _48693) (@lem4295094 _103141 _103145 _48692 _48693 s t x x' y h1)). Qed.
Lemma lem4295105 {_103141 _103145 : Type'} (_48692 : _103145) (_48693 : _103141) (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) (h1 : term375 _103141 _103145 s x' x t a y) (h2 : term150 _103141 _103145 s t x x' y) : term456 _103141 _103145 s t x' y _48692 _48693.
Proof. exact (EQ_MP (@lem4295104 _103141 _103145 _48692 _48693 s t x x' y h2) (@lem4294819 _103141 _103145 _48692 _48693 s x' x t a y h1)). Qed.
Lemma lem4295134 {_103141 _103145 : Type'} (a : _103145) (t : type1470 _103141 _103145) (_48694 : _103145) (_48695 : _103141) : (term459 _103141 _103145 a t _48694 _48695) = (term459 _103141 _103145 a t _48694 _48695).
Proof. exact (eq_refl (term459 _103141 _103145 a t _48694 _48695)). Qed.
Lemma lem4295135 {_103141 _103145 : Type'} (_48694 : _103145) (_48695 : _103141) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) (h1 : term174 _103141 _103145 x t a y) : (term460 _103141 _103145 a t _48694 _48695 x) = (term461 _103141 _103145 t _48694 _48695 a y).
Proof. exact (MK_COMB (@lem4295134 _103141 _103145 a t _48694 _48695) (@lem4294821 _103141 _103145 x t a y h1)). Qed.
Lemma lem4295136 {_103141 _103145 : Type'} (t : type1470 _103141 _103145) (a : _103145) (y : _103141) (_48694 : _103145) (_48695 : _103141) : (term461 _103141 _103145 t _48694 _48695 a y) = (term462 _103141 _103145 t a y _48694 _48695).
Proof. exact (eq_refl (term461 _103141 _103145 t _48694 _48695 a y)). Qed.
Lemma lem4295137 {_103141 _103145 : Type'} (a : _103145) (t : type1470 _103141 _103145) (_48694 : _103145) (_48695 : _103141) (x : prod _103145 _103141) : (term463 _103141 _103145 a t _48694 _48695 x) = (term463 _103141 _103145 a t _48694 _48695 x).
Proof. exact (eq_refl (term463 _103141 _103145 a t _48694 _48695 x)). Qed.
Lemma lem4295138 {_103141 _103145 : Type'} (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) (_48694 : _103145) (_48695 : _103141) : ((term460 _103141 _103145 a t _48694 _48695 x) = (term461 _103141 _103145 t _48694 _48695 a y)) = ((term460 _103141 _103145 a t _48694 _48695 x) = (term462 _103141 _103145 t a y _48694 _48695)).
Proof. exact (MK_COMB (@lem4295137 _103141 _103145 a t _48694 _48695 x) (@lem4295136 _103141 _103145 t a y _48694 _48695)). Qed.
Lemma lem4295139 {_103141 _103145 : Type'} (a : _103145) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (_48694 : _103145) (_48695 : _103141) : (term460 _103141 _103145 a t _48694 _48695 x) = (term438 _103141 _103145 a t x _48694 _48695).
Proof. exact (eq_refl (term460 _103141 _103145 a t _48694 _48695 x)). Qed.
Lemma lem4295140 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4295141 {_103141 _103145 : Type'} (a : _103145) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (_48694 : _103145) (_48695 : _103141) : (term463 _103141 _103145 a t _48694 _48695 x) = (term464 _103141 _103145 a t x _48694 _48695).
Proof. exact (MK_COMB (@lem4295140) (@lem4295139 _103141 _103145 a t x _48694 _48695)). Qed.
Lemma lem4295142 {_103141 _103145 : Type'} (t : type1470 _103141 _103145) (a : _103145) (y : _103141) (_48694 : _103145) (_48695 : _103141) : (term462 _103141 _103145 t a y _48694 _48695) = (term462 _103141 _103145 t a y _48694 _48695).
Proof. exact (eq_refl (term462 _103141 _103145 t a y _48694 _48695)). Qed.
Lemma lem4295143 {_103141 _103145 : Type'} (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) (_48694 : _103145) (_48695 : _103141) : ((term460 _103141 _103145 a t _48694 _48695 x) = (term462 _103141 _103145 t a y _48694 _48695)) = ((term438 _103141 _103145 a t x _48694 _48695) = (term462 _103141 _103145 t a y _48694 _48695)).
Proof. exact (MK_COMB (@lem4295141 _103141 _103145 a t x _48694 _48695) (@lem4295142 _103141 _103145 t a y _48694 _48695)). Qed.
Lemma lem4295144 {_103141 _103145 : Type'} (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) (_48694 : _103145) (_48695 : _103141) : ((term460 _103141 _103145 a t _48694 _48695 x) = (term461 _103141 _103145 t _48694 _48695 a y)) = ((term438 _103141 _103145 a t x _48694 _48695) = (term462 _103141 _103145 t a y _48694 _48695)).
Proof. exact (TRANS (@lem4295138 _103141 _103145 x t a y _48694 _48695) (@lem4295143 _103141 _103145 x t a y _48694 _48695)). Qed.
Lemma lem4295145 {_103141 _103145 : Type'} (_48694 : _103145) (_48695 : _103141) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) (h1 : term174 _103141 _103145 x t a y) : (term438 _103141 _103145 a t x _48694 _48695) = (term462 _103141 _103145 t a y _48694 _48695).
Proof. exact (EQ_MP (@lem4295144 _103141 _103145 x t a y _48694 _48695) (@lem4295135 _103141 _103145 _48694 _48695 x t a y h1)). Qed.
Lemma lem4295146 {_103141 _103145 : Type'} (_48694 : _103145) (_48695 : _103141) (s : _103145 -> Prop) (x' : _103145) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) (h1 : term375 _103141 _103145 s x' x t a y) (h2 : term174 _103141 _103145 x t a y) : term462 _103141 _103145 t a y _48694 _48695.
Proof. exact (EQ_MP (@lem4295145 _103141 _103145 _48694 _48695 x t a y h2) (@lem4294835 _103141 _103145 _48694 _48695 s x' x t a y h1)). Qed.
Lemma lem4295213 {_103141 _103145 : Type'} (x : prod _103145 _103141) : x = x.
Proof. exact (@lem21386 (prod _103145 _103141) x). Qed.
Lemma lem4295214 {_103141 _103145 : Type'} (x : prod _103145 _103141) : x = x.
Proof. exact (@lem4295213 _103141 _103145 x). Qed.
Lemma lem4295215 {_103141 _103145 : Type'} (a : _103145) (y : _103141) : (@pair _103145 _103141 a y) = (@pair _103145 _103141 a y).
Proof. exact (@lem4295214 _103141 _103145 (@pair _103145 _103141 a y)). Qed.
Lemma lem4295216 {_103141 _103145 : Type'} (a : _103145) (y : _103141) : term465 _103141 _103145 a y.
Proof. exact (fun h0 : term466 _103141 _103145 a y => @lem4295215 _103141 _103145 a y). Qed.
Lemma lem4295218 (p : Prop) : (term467 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4295219 {_103141 _103145 : Type'} (a : _103145) (y : _103141) : (term465 _103141 _103145 a y) = ((@pair _103145 _103141 a y) = (@pair _103145 _103141 a y)).
Proof. exact (@lem4295218 ((@pair _103145 _103141 a y) = (@pair _103145 _103141 a y))). Qed.
Lemma lem4295220 {_103141 _103145 : Type'} (a : _103145) (y : _103141) : (@pair _103145 _103141 a y) = (@pair _103145 _103141 a y).
Proof. exact (EQ_MP (@lem4295219 _103141 _103145 a y) (@lem4295216 _103141 _103145 a y)). Qed.
Lemma lem4295222 {_103141 _103145 : Type'} (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (x' : _103145) (a : _103145) (h1 : term306 _103141 _103145 x' y s x t a) (h2 : x' = a) : t a y.
Proof. exact (EQ_MP (@lem4294914 _103141 _103145 t y x' a h2) (@lem4294763 _103141 _103145 x' y s x t a h1)). Qed.
Lemma lem4295223 {_103141 _103145 : Type'} (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (x' : _103145) (a : _103145) (h1 : term306 _103141 _103145 x' y s x t a) (h2 : x' = a) : term468 _103141 _103145 t a y.
Proof. exact (fun h0 : term206 _103141 _103145 t a y => @lem4295222 _103141 _103145 y s x t x' a h1 h2). Qed.
Lemma lem4295225 (p : Prop) : (term467 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4295226 {_103141 _103145 : Type'} (t : type1470 _103141 _103145) (a : _103145) (y : _103141) : (term468 _103141 _103145 t a y) = (t a y).
Proof. exact (@lem4295225 (t a y)). Qed.
Lemma lem4295227 {_103141 _103145 : Type'} (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (x' : _103145) (a : _103145) (h1 : term306 _103141 _103145 x' y s x t a) (h2 : x' = a) : t a y.
Proof. exact (EQ_MP (@lem4295226 _103141 _103145 t a y) (@lem4295223 _103141 _103145 y s x t x' a h1 h2)). Qed.
Lemma lem4295229 (a : Prop) (b : Prop) : (term469 a b) = (term470 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4295230 {_103141 _103145 : Type'} (y : _103141) (t : type1470 _103141 _103145) (a : _103145) (_48688 : _103141) : (term450 _103141 _103145 y t a _48688) = (term471 _103141 _103145 y t a _48688).
Proof. exact (@lem4295229 ((@pair _103145 _103141 a y) = (@pair _103145 _103141 a _48688)) (t a _48688)). Qed.
Lemma lem4295232 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4295233 {_103141 _103145 : Type'} (y : _103141) (t : type1470 _103141 _103145) (a : _103145) (_48688 : _103141) : (term471 _103141 _103145 y t a _48688) = (term472 _103141 _103145 y t a _48688).
Proof. exact (@lem4295232 (term473 _103141 _103145 y t a _48688)). Qed.
Lemma lem4295234 {_103141 _103145 : Type'} (y : _103141) (t : type1470 _103141 _103145) (a : _103145) (_48688 : _103141) : (term450 _103141 _103145 y t a _48688) = (term472 _103141 _103145 y t a _48688).
Proof. exact (TRANS (@lem4295230 _103141 _103145 y t a _48688) (@lem4295233 _103141 _103145 y t a _48688)). Qed.
Lemma lem4295236 {_103141 _103145 : Type'} (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (x' : _103145) (a : _103145) (h1 : term306 _103141 _103145 x' y s x t a) (h2 : x' = a) : term474 _103141 _103145 t a y.
Proof. exact (conj (@lem4295220 _103141 _103145 a y) (@lem4295227 _103141 _103145 y s x t x' a h1 h2)). Qed.
Lemma lem4295238 {_103141 _103145 : Type'} (_48688 : _103141) (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (x' : _103145) (a : _103145) (h1 : term306 _103141 _103145 x' y s x t a) (h2 : x' = a) : term472 _103141 _103145 y t a _48688.
Proof. exact (EQ_MP (@lem4295234 _103141 _103145 y t a _48688) (@lem4294955 _103141 _103145 _48688 y s x t x' a h1 h2)). Qed.
Lemma lem4295239 {_103141 _103145 : Type'} (_48688 : _103141) (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (x' : _103145) (a : _103145) (h1 : term306 _103141 _103145 x' y s x t a) (h2 : x' = a) : term472 _103141 _103145 y t a _48688.
Proof. exact (@lem4295238 _103141 _103145 _48688 y s x t x' a h1 h2). Qed.
Lemma lem4295240 {_103141 _103145 : Type'} (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (x' : _103145) (a : _103145) (h1 : term306 _103141 _103145 x' y s x t a) (h2 : x' = a) : term475 _103141 _103145 t a y.
Proof. exact (@lem4295239 _103141 _103145 y y s x t x' a h1 h2). Qed.
Lemma lem4295243 {_103141 _103145 : Type'} (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (x' : _103145) (a : _103145) (h1 : term306 _103141 _103145 x' y s x t a) (h2 : x' = a) : False.
Proof. exact (@lem4295240 _103141 _103145 y s x t x' a h1 h2 (@lem4295236 _103141 _103145 y s x t x' a h1 h2)). Qed.
Lemma lem4295244 {_103141 _103145 : Type'} (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (x' : _103145) (a : _103145) (h1 : term306 _103141 _103145 x' y s x t a) (h2 : x' = a) : term476.
Proof. exact (fun h0 : ~ False => @lem4295243 _103141 _103145 y s x t x' a h1 h2). Qed.
Lemma lem4295246 (p : Prop) : (term467 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4295247 : term476 = False.
Proof. exact (@lem4295246 False). Qed.
Lemma lem4295302 {_103145 : Type'} (s : _103145 -> Prop) (x' : _103145) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem4295303 {_103145 : Type'} (s : _103145 -> Prop) (x' : _103145) (h1 : s x') : term477 _103145 s x'.
Proof. exact (fun h0 : term422 _103145 s x' => @lem4295302 _103145 s x' h1). Qed.
Lemma lem4295305 (p : Prop) : (term467 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4295306 {_103145 : Type'} (s : _103145 -> Prop) (x' : _103145) : (term477 _103145 s x') = (s x').
Proof. exact (@lem4295305 (s x')). Qed.
Lemma lem4295307 {_103145 : Type'} (s : _103145 -> Prop) (x' : _103145) (h1 : s x') : s x'.
Proof. exact (EQ_MP (@lem4295306 _103145 s x') (@lem4295303 _103145 s x' h1)). Qed.
Lemma lem4295309 {_103141 _103145 : Type'} (x' : _103145) (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (h1 : term306 _103141 _103145 x' y s x t a) : t x' y.
Proof. exact (proj2 (@lem4294503 _103141 _103145 x' y s x t a h1)). Qed.
Lemma lem4295310 {_103141 _103145 : Type'} (x' : _103145) (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (h1 : term306 _103141 _103145 x' y s x t a) : term468 _103141 _103145 t x' y.
Proof. exact (fun h0 : term206 _103141 _103145 t x' y => @lem4295309 _103141 _103145 x' y s x t a h1). Qed.
Lemma lem4295312 (p : Prop) : (term467 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4295313 {_103141 _103145 : Type'} (t : type1470 _103141 _103145) (x' : _103145) (y : _103141) : (term468 _103141 _103145 t x' y) = (t x' y).
Proof. exact (@lem4295312 (t x' y)). Qed.
Lemma lem4295314 {_103141 _103145 : Type'} (x' : _103145) (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (h1 : term306 _103141 _103145 x' y s x t a) : t x' y.
Proof. exact (EQ_MP (@lem4295313 _103141 _103145 t x' y) (@lem4295310 _103141 _103145 x' y s x t a h1)). Qed.
Lemma lem4295316 {_103141 _103145 : Type'} (x : prod _103145 _103141) : x = x.
Proof. exact (@lem21386 (prod _103145 _103141) x). Qed.
Lemma lem4295317 {_103141 _103145 : Type'} (x : prod _103145 _103141) : x = x.
Proof. exact (@lem4295316 _103141 _103145 x). Qed.
Lemma lem4295318 {_103141 _103145 : Type'} (x' : _103145) (y : _103141) : (@pair _103145 _103141 x' y) = (@pair _103145 _103141 x' y).
Proof. exact (@lem4295317 _103141 _103145 (@pair _103145 _103141 x' y)). Qed.
Lemma lem4295319 {_103141 _103145 : Type'} (x' : _103145) (y : _103141) : term465 _103141 _103145 x' y.
Proof. exact (fun h0 : term466 _103141 _103145 x' y => @lem4295318 _103141 _103145 x' y). Qed.
Lemma lem4295321 (p : Prop) : (term467 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4295322 {_103141 _103145 : Type'} (x' : _103145) (y : _103141) : (term465 _103141 _103145 x' y) = ((@pair _103145 _103141 x' y) = (@pair _103145 _103141 x' y)).
Proof. exact (@lem4295321 ((@pair _103145 _103141 x' y) = (@pair _103145 _103141 x' y))). Qed.
Lemma lem4295323 {_103141 _103145 : Type'} (x' : _103145) (y : _103141) : (@pair _103145 _103141 x' y) = (@pair _103145 _103141 x' y).
Proof. exact (EQ_MP (@lem4295322 _103141 _103145 x' y) (@lem4295319 _103141 _103145 x' y)). Qed.
Lemma lem4295325 (a : Prop) (b : Prop) : (term469 a b) = (term470 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4295326 {_103141 _103145 : Type'} (t : type1470 _103141 _103145) (x' : _103145) (y : _103141) (_48689 : _103145) (_48690 : _103141) : (term478 _103141 _103145 t x' y _48689 _48690) = (term479 _103141 _103145 t x' y _48689 _48690).
Proof. exact (@lem4295325 (t _48689 _48690) ((@pair _103145 _103141 x' y) = (@pair _103145 _103141 _48689 _48690))). Qed.
Lemma lem4295327 {_103145 : Type'} (s : _103145 -> Prop) (_48689 : _103145) : (term480 _103145 s _48689) = (term480 _103145 s _48689).
Proof. exact (eq_refl (term480 _103145 s _48689)). Qed.
Lemma lem4295328 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x' : _103145) (y : _103141) (_48689 : _103145) (_48690 : _103141) : (term456 _103141 _103145 s t x' y _48689 _48690) = (term481 _103141 _103145 s t x' y _48689 _48690).
Proof. exact (MK_COMB (@lem4295327 _103145 s _48689) (@lem4295326 _103141 _103145 t x' y _48689 _48690)). Qed.
Lemma lem4295330 (a : Prop) (b : Prop) : (term469 a b) = (term470 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4295331 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x' : _103145) (y : _103141) (_48689 : _103145) (_48690 : _103141) : (term481 _103141 _103145 s t x' y _48689 _48690) = (term482 _103141 _103145 s t x' y _48689 _48690).
Proof. exact (@lem4295330 (s _48689) (term483 _103141 _103145 t x' y _48689 _48690)). Qed.
Lemma lem4295332 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x' : _103145) (y : _103141) (_48689 : _103145) (_48690 : _103141) : (term456 _103141 _103145 s t x' y _48689 _48690) = (term482 _103141 _103145 s t x' y _48689 _48690).
Proof. exact (TRANS (@lem4295328 _103141 _103145 s t x' y _48689 _48690) (@lem4295331 _103141 _103145 s t x' y _48689 _48690)). Qed.
Lemma lem4295334 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4295335 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x' : _103145) (y : _103141) (_48689 : _103145) (_48690 : _103141) : (term482 _103141 _103145 s t x' y _48689 _48690) = (term484 _103141 _103145 s t x' y _48689 _48690).
Proof. exact (@lem4295334 (term485 _103141 _103145 s t x' y _48689 _48690)). Qed.
Lemma lem4295336 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x' : _103145) (y : _103141) (_48689 : _103145) (_48690 : _103141) : (term456 _103141 _103145 s t x' y _48689 _48690) = (term484 _103141 _103145 s t x' y _48689 _48690).
Proof. exact (TRANS (@lem4295332 _103141 _103145 s t x' y _48689 _48690) (@lem4295335 _103141 _103145 s t x' y _48689 _48690)). Qed.
Lemma lem4295338 {_103141 _103145 : Type'} (x' : _103145) (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (h1 : term306 _103141 _103145 x' y s x t a) : term486 _103141 _103145 t x' y.
Proof. exact (conj (@lem4295314 _103141 _103145 x' y s x t a h1) (@lem4295323 _103141 _103145 x' y)). Qed.
Lemma lem4295339 {_103141 _103145 : Type'} (x' : _103145) (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (h1 : s x') (h2 : term306 _103141 _103145 x' y s x t a) : term487 _103141 _103145 s t x' y.
Proof. exact (conj (@lem4295307 _103145 s x' h1) (@lem4295338 _103141 _103145 x' y s x t a h2)). Qed.
Lemma lem4295341 {_103141 _103145 : Type'} (_48689 : _103145) (_48690 : _103141) (x' : _103145) (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (h1 : term306 _103141 _103145 x' y s x t a) : term484 _103141 _103145 s t x' y _48689 _48690.
Proof. exact (EQ_MP (@lem4295336 _103141 _103145 s t x' y _48689 _48690) (@lem4294996 _103141 _103145 _48689 _48690 x' y s x t a h1)). Qed.
Lemma lem4295342 {_103141 _103145 : Type'} (_48689 : _103145) (_48690 : _103141) (x' : _103145) (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (h1 : term306 _103141 _103145 x' y s x t a) : term484 _103141 _103145 s t x' y _48689 _48690.
Proof. exact (@lem4295341 _103141 _103145 _48689 _48690 x' y s x t a h1). Qed.
Lemma lem4295343 {_103141 _103145 : Type'} (x' : _103145) (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (h1 : term306 _103141 _103145 x' y s x t a) : term488 _103141 _103145 s t x' y.
Proof. exact (@lem4295342 _103141 _103145 x' y x' y s x t a h1). Qed.
Lemma lem4295346 {_103141 _103145 : Type'} (x' : _103145) (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (h1 : s x') (h2 : term306 _103141 _103145 x' y s x t a) : False.
Proof. exact (@lem4295343 _103141 _103145 x' y s x t a h2 (@lem4295339 _103141 _103145 x' y s x t a h1 h2)). Qed.
Lemma lem4295347 {_103141 _103145 : Type'} (x' : _103145) (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (h1 : s x') (h2 : term306 _103141 _103145 x' y s x t a) : term476.
Proof. exact (fun h0 : ~ False => @lem4295346 _103141 _103145 x' y s x t a h1 h2). Qed.
Lemma lem4295349 (p : Prop) : (term467 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4295350 : term476 = False.
Proof. exact (@lem4295349 False). Qed.
Lemma lem4295351 {_103141 _103145 : Type'} (x' : _103145) (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (h1 : s x') (h2 : term306 _103141 _103145 x' y s x t a) : False.
Proof. exact (EQ_MP (@lem4295350) (@lem4295347 _103141 _103145 x' y s x t a h1 h2)). Qed.
Lemma lem4295405 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) (h1 : term150 _103141 _103145 s t x x' y) : s x'.
Proof. exact (proj1 (@lem4294513 _103141 _103145 s t x x' y h1)). Qed.
Lemma lem4295406 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) (h1 : term150 _103141 _103145 s t x x' y) : term477 _103145 s x'.
Proof. exact (fun h0 : term422 _103145 s x' => @lem4295405 _103141 _103145 s t x x' y h1). Qed.
Lemma lem4295408 (p : Prop) : (term467 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4295409 {_103145 : Type'} (s : _103145 -> Prop) (x' : _103145) : (term477 _103145 s x') = (s x').
Proof. exact (@lem4295408 (s x')). Qed.
Lemma lem4295410 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) (h1 : term150 _103141 _103145 s t x x' y) : s x'.
Proof. exact (EQ_MP (@lem4295409 _103145 s x') (@lem4295406 _103141 _103145 s t x x' y h1)). Qed.
Lemma lem4295412 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) (h1 : term150 _103141 _103145 s t x x' y) : t x' y.
Proof. exact (proj2 (@lem4294513 _103141 _103145 s t x x' y h1)). Qed.
Lemma lem4295413 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) (h1 : term150 _103141 _103145 s t x x' y) : term468 _103141 _103145 t x' y.
Proof. exact (fun h0 : term206 _103141 _103145 t x' y => @lem4295412 _103141 _103145 s t x x' y h1). Qed.
Lemma lem4295415 (p : Prop) : (term467 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4295416 {_103141 _103145 : Type'} (t : type1470 _103141 _103145) (x' : _103145) (y : _103141) : (term468 _103141 _103145 t x' y) = (t x' y).
Proof. exact (@lem4295415 (t x' y)). Qed.
Lemma lem4295417 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) (h1 : term150 _103141 _103145 s t x x' y) : t x' y.
Proof. exact (EQ_MP (@lem4295416 _103141 _103145 t x' y) (@lem4295413 _103141 _103145 s t x x' y h1)). Qed.
Lemma lem4295419 {_103141 _103145 : Type'} (x : prod _103145 _103141) : x = x.
Proof. exact (@lem21386 (prod _103145 _103141) x). Qed.
Lemma lem4295420 {_103141 _103145 : Type'} (x : prod _103145 _103141) : x = x.
Proof. exact (@lem4295419 _103141 _103145 x). Qed.
Lemma lem4295421 {_103141 _103145 : Type'} (x' : _103145) (y : _103141) : (@pair _103145 _103141 x' y) = (@pair _103145 _103141 x' y).
Proof. exact (@lem4295420 _103141 _103145 (@pair _103145 _103141 x' y)). Qed.
Lemma lem4295422 {_103141 _103145 : Type'} (x' : _103145) (y : _103141) : term465 _103141 _103145 x' y.
Proof. exact (fun h0 : term466 _103141 _103145 x' y => @lem4295421 _103141 _103145 x' y). Qed.
Lemma lem4295424 (p : Prop) : (term467 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4295425 {_103141 _103145 : Type'} (x' : _103145) (y : _103141) : (term465 _103141 _103145 x' y) = ((@pair _103145 _103141 x' y) = (@pair _103145 _103141 x' y)).
Proof. exact (@lem4295424 ((@pair _103145 _103141 x' y) = (@pair _103145 _103141 x' y))). Qed.
Lemma lem4295426 {_103141 _103145 : Type'} (x' : _103145) (y : _103141) : (@pair _103145 _103141 x' y) = (@pair _103145 _103141 x' y).
Proof. exact (EQ_MP (@lem4295425 _103141 _103145 x' y) (@lem4295422 _103141 _103145 x' y)). Qed.
Lemma lem4295428 (a : Prop) (b : Prop) : (term469 a b) = (term470 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4295429 {_103141 _103145 : Type'} (t : type1470 _103141 _103145) (x' : _103145) (y : _103141) (_48692 : _103145) (_48693 : _103141) : (term478 _103141 _103145 t x' y _48692 _48693) = (term479 _103141 _103145 t x' y _48692 _48693).
Proof. exact (@lem4295428 (t _48692 _48693) ((@pair _103145 _103141 x' y) = (@pair _103145 _103141 _48692 _48693))). Qed.
Lemma lem4295430 {_103145 : Type'} (s : _103145 -> Prop) (_48692 : _103145) : (term480 _103145 s _48692) = (term480 _103145 s _48692).
Proof. exact (eq_refl (term480 _103145 s _48692)). Qed.
Lemma lem4295431 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x' : _103145) (y : _103141) (_48692 : _103145) (_48693 : _103141) : (term456 _103141 _103145 s t x' y _48692 _48693) = (term481 _103141 _103145 s t x' y _48692 _48693).
Proof. exact (MK_COMB (@lem4295430 _103145 s _48692) (@lem4295429 _103141 _103145 t x' y _48692 _48693)). Qed.
Lemma lem4295433 (a : Prop) (b : Prop) : (term469 a b) = (term470 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4295434 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x' : _103145) (y : _103141) (_48692 : _103145) (_48693 : _103141) : (term481 _103141 _103145 s t x' y _48692 _48693) = (term482 _103141 _103145 s t x' y _48692 _48693).
Proof. exact (@lem4295433 (s _48692) (term483 _103141 _103145 t x' y _48692 _48693)). Qed.
Lemma lem4295435 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x' : _103145) (y : _103141) (_48692 : _103145) (_48693 : _103141) : (term456 _103141 _103145 s t x' y _48692 _48693) = (term482 _103141 _103145 s t x' y _48692 _48693).
Proof. exact (TRANS (@lem4295431 _103141 _103145 s t x' y _48692 _48693) (@lem4295434 _103141 _103145 s t x' y _48692 _48693)). Qed.
Lemma lem4295437 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4295438 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x' : _103145) (y : _103141) (_48692 : _103145) (_48693 : _103141) : (term482 _103141 _103145 s t x' y _48692 _48693) = (term484 _103141 _103145 s t x' y _48692 _48693).
Proof. exact (@lem4295437 (term485 _103141 _103145 s t x' y _48692 _48693)). Qed.
Lemma lem4295439 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x' : _103145) (y : _103141) (_48692 : _103145) (_48693 : _103141) : (term456 _103141 _103145 s t x' y _48692 _48693) = (term484 _103141 _103145 s t x' y _48692 _48693).
Proof. exact (TRANS (@lem4295435 _103141 _103145 s t x' y _48692 _48693) (@lem4295438 _103141 _103145 s t x' y _48692 _48693)). Qed.
Lemma lem4295441 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) (h1 : term150 _103141 _103145 s t x x' y) : term486 _103141 _103145 t x' y.
Proof. exact (conj (@lem4295417 _103141 _103145 s t x x' y h1) (@lem4295426 _103141 _103145 x' y)). Qed.
Lemma lem4295442 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) (h1 : term150 _103141 _103145 s t x x' y) : term487 _103141 _103145 s t x' y.
Proof. exact (conj (@lem4295410 _103141 _103145 s t x x' y h1) (@lem4295441 _103141 _103145 s t x x' y h1)). Qed.
Lemma lem4295444 {_103141 _103145 : Type'} (_48692 : _103145) (_48693 : _103141) (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) (h1 : term375 _103141 _103145 s x' x t a y) (h2 : term150 _103141 _103145 s t x x' y) : term484 _103141 _103145 s t x' y _48692 _48693.
Proof. exact (EQ_MP (@lem4295439 _103141 _103145 s t x' y _48692 _48693) (@lem4295105 _103141 _103145 _48692 _48693 a s t x x' y h1 h2)). Qed.
Lemma lem4295445 {_103141 _103145 : Type'} (_48692 : _103145) (_48693 : _103141) (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) (h1 : term375 _103141 _103145 s x' x t a y) (h2 : term150 _103141 _103145 s t x x' y) : term484 _103141 _103145 s t x' y _48692 _48693.
Proof. exact (@lem4295444 _103141 _103145 _48692 _48693 a s t x x' y h1 h2). Qed.
Lemma lem4295446 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) (h1 : term375 _103141 _103145 s x' x t a y) (h2 : term150 _103141 _103145 s t x x' y) : term488 _103141 _103145 s t x' y.
Proof. exact (@lem4295445 _103141 _103145 x' y a s t x x' y h1 h2). Qed.
Lemma lem4295449 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) (h1 : term375 _103141 _103145 s x' x t a y) (h2 : term150 _103141 _103145 s t x x' y) : False.
Proof. exact (@lem4295446 _103141 _103145 a s t x x' y h1 h2 (@lem4295442 _103141 _103145 s t x x' y h2)). Qed.
Lemma lem4295450 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) (h1 : term375 _103141 _103145 s x' x t a y) (h2 : term150 _103141 _103145 s t x x' y) : term476.
Proof. exact (fun h0 : ~ False => @lem4295449 _103141 _103145 a s t x x' y h1 h2). Qed.
Lemma lem4295452 (p : Prop) : (term467 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4295453 : term476 = False.
Proof. exact (@lem4295452 False). Qed.
Lemma lem4295508 {_103145 : Type'} (x : _103145) : x = x.
Proof. exact (@lem21386 _103145 x). Qed.
Lemma lem4295509 {_103145 : Type'} (x : _103145) : x = x.
Proof. exact (@lem4295508 _103145 x). Qed.
Lemma lem4295510 {_103145 : Type'} (a : _103145) : a = a.
Proof. exact (@lem4295509 _103145 a). Qed.
Lemma lem4295511 {_103145 : Type'} (a : _103145) : term489 _103145 a.
Proof. exact (fun h0 : term490 _103145 a => @lem4295510 _103145 a). Qed.
Lemma lem4295513 (p : Prop) : (term467 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4295514 {_103145 : Type'} (a : _103145) : (term489 _103145 a) = (a = a).
Proof. exact (@lem4295513 (a = a)). Qed.
Lemma lem4295515 {_103145 : Type'} (a : _103145) : a = a.
Proof. exact (EQ_MP (@lem4295514 _103145 a) (@lem4295511 _103145 a)). Qed.
Lemma lem4295517 {_103141 _103145 : Type'} (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) (h1 : term174 _103141 _103145 x t a y) : t a y.
Proof. exact (proj2 (@lem4294511 _103141 _103145 x t a y h1)). Qed.
Lemma lem4295518 {_103141 _103145 : Type'} (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) (h1 : term174 _103141 _103145 x t a y) : term468 _103141 _103145 t a y.
Proof. exact (fun h0 : term206 _103141 _103145 t a y => @lem4295517 _103141 _103145 x t a y h1). Qed.
Lemma lem4295520 (p : Prop) : (term467 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4295521 {_103141 _103145 : Type'} (t : type1470 _103141 _103145) (a : _103145) (y : _103141) : (term468 _103141 _103145 t a y) = (t a y).
Proof. exact (@lem4295520 (t a y)). Qed.
Lemma lem4295522 {_103141 _103145 : Type'} (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) (h1 : term174 _103141 _103145 x t a y) : t a y.
Proof. exact (EQ_MP (@lem4295521 _103141 _103145 t a y) (@lem4295518 _103141 _103145 x t a y h1)). Qed.
Lemma lem4295524 {_103141 _103145 : Type'} (x : prod _103145 _103141) : x = x.
Proof. exact (@lem21386 (prod _103145 _103141) x). Qed.
Lemma lem4295525 {_103141 _103145 : Type'} (x : prod _103145 _103141) : x = x.
Proof. exact (@lem4295524 _103141 _103145 x). Qed.
Lemma lem4295526 {_103141 _103145 : Type'} (a : _103145) (y : _103141) : (@pair _103145 _103141 a y) = (@pair _103145 _103141 a y).
Proof. exact (@lem4295525 _103141 _103145 (@pair _103145 _103141 a y)). Qed.
Lemma lem4295527 {_103141 _103145 : Type'} (a : _103145) (y : _103141) : term465 _103141 _103145 a y.
Proof. exact (fun h0 : term466 _103141 _103145 a y => @lem4295526 _103141 _103145 a y). Qed.
Lemma lem4295529 (p : Prop) : (term467 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4295530 {_103141 _103145 : Type'} (a : _103145) (y : _103141) : (term465 _103141 _103145 a y) = ((@pair _103145 _103141 a y) = (@pair _103145 _103141 a y)).
Proof. exact (@lem4295529 ((@pair _103145 _103141 a y) = (@pair _103145 _103141 a y))). Qed.
Lemma lem4295531 {_103141 _103145 : Type'} (a : _103145) (y : _103141) : (@pair _103145 _103141 a y) = (@pair _103145 _103141 a y).
Proof. exact (EQ_MP (@lem4295530 _103141 _103145 a y) (@lem4295527 _103141 _103145 a y)). Qed.
Lemma lem4295533 (a : Prop) (b : Prop) : (term469 a b) = (term470 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4295534 {_103141 _103145 : Type'} (t : type1470 _103141 _103145) (a : _103145) (y : _103141) (_48694 : _103145) (_48695 : _103141) : (term478 _103141 _103145 t a y _48694 _48695) = (term479 _103141 _103145 t a y _48694 _48695).
Proof. exact (@lem4295533 (t _48694 _48695) ((@pair _103145 _103141 a y) = (@pair _103145 _103141 _48694 _48695))). Qed.
Lemma lem4295535 {_103145 : Type'} (_48694 : _103145) (a : _103145) : (term491 _103145 _48694 a) = (term491 _103145 _48694 a).
Proof. exact (eq_refl (term491 _103145 _48694 a)). Qed.
Lemma lem4295536 {_103141 _103145 : Type'} (t : type1470 _103141 _103145) (a : _103145) (y : _103141) (_48694 : _103145) (_48695 : _103141) : (term462 _103141 _103145 t a y _48694 _48695) = (term492 _103141 _103145 t a y _48694 _48695).
Proof. exact (MK_COMB (@lem4295535 _103145 _48694 a) (@lem4295534 _103141 _103145 t a y _48694 _48695)). Qed.
Lemma lem4295538 (a : Prop) (b : Prop) : (term469 a b) = (term470 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4295539 {_103141 _103145 : Type'} (t : type1470 _103141 _103145) (a : _103145) (y : _103141) (_48694 : _103145) (_48695 : _103141) : (term492 _103141 _103145 t a y _48694 _48695) = (term493 _103141 _103145 t a y _48694 _48695).
Proof. exact (@lem4295538 (_48694 = a) (term483 _103141 _103145 t a y _48694 _48695)). Qed.
Lemma lem4295540 {_103141 _103145 : Type'} (t : type1470 _103141 _103145) (a : _103145) (y : _103141) (_48694 : _103145) (_48695 : _103141) : (term462 _103141 _103145 t a y _48694 _48695) = (term493 _103141 _103145 t a y _48694 _48695).
Proof. exact (TRANS (@lem4295536 _103141 _103145 t a y _48694 _48695) (@lem4295539 _103141 _103145 t a y _48694 _48695)). Qed.
Lemma lem4295542 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4295543 {_103141 _103145 : Type'} (t : type1470 _103141 _103145) (a : _103145) (y : _103141) (_48694 : _103145) (_48695 : _103141) : (term493 _103141 _103145 t a y _48694 _48695) = (term494 _103141 _103145 t a y _48694 _48695).
Proof. exact (@lem4295542 (term495 _103141 _103145 t a y _48694 _48695)). Qed.
Lemma lem4295544 {_103141 _103145 : Type'} (t : type1470 _103141 _103145) (a : _103145) (y : _103141) (_48694 : _103145) (_48695 : _103141) : (term462 _103141 _103145 t a y _48694 _48695) = (term494 _103141 _103145 t a y _48694 _48695).
Proof. exact (TRANS (@lem4295540 _103141 _103145 t a y _48694 _48695) (@lem4295543 _103141 _103145 t a y _48694 _48695)). Qed.
Lemma lem4295546 {_103141 _103145 : Type'} (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) (h1 : term174 _103141 _103145 x t a y) : term486 _103141 _103145 t a y.
Proof. exact (conj (@lem4295522 _103141 _103145 x t a y h1) (@lem4295531 _103141 _103145 a y)). Qed.
Lemma lem4295547 {_103141 _103145 : Type'} (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) (h1 : term174 _103141 _103145 x t a y) : term496 _103141 _103145 t a y.
Proof. exact (conj (@lem4295515 _103145 a) (@lem4295546 _103141 _103145 x t a y h1)). Qed.
Lemma lem4295549 {_103141 _103145 : Type'} (_48694 : _103145) (_48695 : _103141) (s : _103145 -> Prop) (x' : _103145) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) (h1 : term375 _103141 _103145 s x' x t a y) (h2 : term174 _103141 _103145 x t a y) : term494 _103141 _103145 t a y _48694 _48695.
Proof. exact (EQ_MP (@lem4295544 _103141 _103145 t a y _48694 _48695) (@lem4295146 _103141 _103145 _48694 _48695 s x' x t a y h1 h2)). Qed.
Lemma lem4295550 {_103141 _103145 : Type'} (_48694 : _103145) (_48695 : _103141) (s : _103145 -> Prop) (x' : _103145) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) (h1 : term375 _103141 _103145 s x' x t a y) (h2 : term174 _103141 _103145 x t a y) : term494 _103141 _103145 t a y _48694 _48695.
Proof. exact (@lem4295549 _103141 _103145 _48694 _48695 s x' x t a y h1 h2). Qed.
Lemma lem4295551 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x' : _103145) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) (h1 : term375 _103141 _103145 s x' x t a y) (h2 : term174 _103141 _103145 x t a y) : term497 _103141 _103145 t a y.
Proof. exact (@lem4295550 _103141 _103145 a y s x' x t a y h1 h2). Qed.
Lemma lem4295554 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x' : _103145) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) (h1 : term375 _103141 _103145 s x' x t a y) (h2 : term174 _103141 _103145 x t a y) : False.
Proof. exact (@lem4295551 _103141 _103145 s x' x t a y h1 h2 (@lem4295547 _103141 _103145 x t a y h2)). Qed.
Lemma lem4295555 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x' : _103145) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) (h1 : term375 _103141 _103145 s x' x t a y) (h2 : term174 _103141 _103145 x t a y) : term476.
Proof. exact (fun h0 : ~ False => @lem4295554 _103141 _103145 s x' x t a y h1 h2). Qed.
Lemma lem4295557 (p : Prop) : (term467 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4295558 : term476 = False.
Proof. exact (@lem4295557 False). Qed.
Lemma lem4295560 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x' : _103145) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) (h1 : term375 _103141 _103145 s x' x t a y) (h2 : term174 _103141 _103145 x t a y) : False.
Proof. exact (EQ_MP (@lem4295558) (@lem4295555 _103141 _103145 s x' x t a y h1 h2)). Qed.
Lemma lem4295561 {_103141 _103145 : Type'} (a : _103145) (s : _103145 -> Prop) (t : type1470 _103141 _103145) (x : prod _103145 _103141) (x' : _103145) (y : _103141) (h1 : term375 _103141 _103145 s x' x t a y) (h2 : term150 _103141 _103145 s t x x' y) : False.
Proof. exact (EQ_MP (@lem4295453) (@lem4295450 _103141 _103145 a s t x x' y h1 h2)). Qed.
Lemma lem4295562 {_103141 _103145 : Type'} (x' : _103145) (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (h1 : s x') (h2 : term306 _103141 _103145 x' y s x t a) : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem4295351 _103141 _103145 x' y s x t a h1 h2) (fun h3 : False => @lem4295037 _103145 s x' h1)). Qed.
Lemma lem4295564 {_103141 _103145 : Type'} (x' : _103145) (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (h1 : s x') (h2 : term306 _103141 _103145 x' y s x t a) : False.
Proof. exact (EQ_MP (@lem4295562 _103141 _103145 x' y s x t a h1 h2) (@lem4295037 _103145 s x' h1)). Qed.
Lemma lem4295566 {_103141 _103145 : Type'} (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (x' : _103145) (a : _103145) (h1 : term306 _103141 _103145 x' y s x t a) (h2 : x' = a) : False.
Proof. exact (EQ_MP (@lem4295247) (@lem4295244 _103141 _103145 y s x t x' a h1 h2)). Qed.
Lemma lem4295567 {_103141 _103145 : Type'} (x' : _103145) (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (h1 : s x') (h2 : term306 _103141 _103145 x' y s x t a) : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem4295564 _103141 _103145 x' y s x t a h1 h2) (fun h3 : False => @lem4294789 _103145 s x' h1)). Qed.
Lemma lem4295568 {_103141 _103145 : Type'} (x' : _103145) (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (h1 : s x') (h2 : term306 _103141 _103145 x' y s x t a) : False.
Proof. exact (EQ_MP (@lem4295567 _103141 _103145 x' y s x t a h1 h2) (@lem4294789 _103145 s x' h1)). Qed.
Lemma lem4295569 {_103141 _103145 : Type'} (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (x' : _103145) (a : _103145) (h1 : term306 _103141 _103145 x' y s x t a) (h2 : x' = a) : (x' = a) = False.
Proof. exact (prop_ext (fun h3 : x' = a => @lem4295566 _103141 _103145 y s x t x' a h1 h2) (fun h3 : False => @lem4294765 _103145 x' a h2)). Qed.
Lemma lem4295570 {_103141 _103145 : Type'} (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (x' : _103145) (a : _103145) (h1 : term306 _103141 _103145 x' y s x t a) (h2 : x' = a) : False.
Proof. exact (EQ_MP (@lem4295569 _103141 _103145 y s x t x' a h1 h2) (@lem4294765 _103145 x' a h2)). Qed.
Lemma lem4295571 {_103141 _103145 : Type'} (x' : _103145) (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (h1 : s x') (h2 : term306 _103141 _103145 x' y s x t a) : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem4295568 _103141 _103145 x' y s x t a h1 h2) (fun h3 : False => @lem4294611 _103145 s x' h1)). Qed.
Lemma lem4295572 {_103141 _103145 : Type'} (x' : _103145) (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (h1 : s x') (h2 : term306 _103141 _103145 x' y s x t a) : False.
Proof. exact (EQ_MP (@lem4295571 _103141 _103145 x' y s x t a h1 h2) (@lem4294611 _103145 s x' h1)). Qed.
Lemma lem4295573 {_103141 _103145 : Type'} (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (x' : _103145) (a : _103145) (h1 : term306 _103141 _103145 x' y s x t a) (h2 : x' = a) : (x' = a) = False.
Proof. exact (prop_ext (fun h3 : x' = a => @lem4295570 _103141 _103145 y s x t x' a h1 h2) (fun h3 : False => @lem4294564 _103145 x' a h2)). Qed.
Lemma lem4295574 {_103141 _103145 : Type'} (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (x' : _103145) (a : _103145) (h1 : term306 _103141 _103145 x' y s x t a) (h2 : x' = a) : False.
Proof. exact (EQ_MP (@lem4295573 _103141 _103145 y s x t x' a h1 h2) (@lem4294564 _103145 x' a h2)). Qed.
Lemma lem4295575 {_103141 _103145 : Type'} (x' : _103145) (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (h1 : s x') (h2 : term306 _103141 _103145 x' y s x t a) : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem4295572 _103141 _103145 x' y s x t a h1 h2) (fun h3 : False => @lem4294611 _103145 s x' h1)). Qed.
Lemma lem4295576 {_103141 _103145 : Type'} (x' : _103145) (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (h1 : s x') (h2 : term306 _103141 _103145 x' y s x t a) : False.
Proof. exact (EQ_MP (@lem4295575 _103141 _103145 x' y s x t a h1 h2) (@lem4294611 _103145 s x' h1)). Qed.
Lemma lem4295577 {_103141 _103145 : Type'} (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (x' : _103145) (a : _103145) (h1 : term306 _103141 _103145 x' y s x t a) (h2 : x' = a) : (x' = a) = False.
Proof. exact (prop_ext (fun h3 : x' = a => @lem4295574 _103141 _103145 y s x t x' a h1 h2) (fun h3 : False => @lem4294564 _103145 x' a h2)). Qed.
Lemma lem4295578 {_103141 _103145 : Type'} (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (x' : _103145) (a : _103145) (h1 : term306 _103141 _103145 x' y s x t a) (h2 : x' = a) : False.
Proof. exact (EQ_MP (@lem4295577 _103141 _103145 y s x t x' a h1 h2) (@lem4294564 _103145 x' a h2)). Qed.
Lemma lem4295579 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x' : _103145) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) (h1 : term375 _103141 _103145 s x' x t a y) : False.
Proof. exact (or_elim (@lem4294508 _103141 _103145 s x' x t a y h1) (fun h0 : term150 _103141 _103145 s t x x' y => @lem4295561 _103141 _103145 a s t x x' y h1 h0) (fun h0 : term174 _103141 _103145 x t a y => @lem4295560 _103141 _103145 s x' x t a y h1 h0)). Qed.
Lemma lem4295580 {_103141 _103145 : Type'} (x' : _103145) (y : _103141) (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (h1 : term306 _103141 _103145 x' y s x t a) : False.
Proof. exact (or_elim (@lem4294505 _103141 _103145 x' y s x t a h1) (fun h0 : x' = a => @lem4295578 _103141 _103145 y s x t x' a h1 h0) (fun h0 : s x' => @lem4295576 _103141 _103145 x' y s x t a h0 h1)). Qed.
Lemma lem4295581 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x' : _103145) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) (h1 : term414 _103141 _103145 s x' x t a y) : False.
Proof. exact (or_elim (@lem4294495 _103141 _103145 s x' x t a y h1) (fun h0 : term306 _103141 _103145 x' y s x t a => @lem4295580 _103141 _103145 x' y s x t a h0) (fun h0 : term375 _103141 _103145 s x' x t a y => @lem4295579 _103141 _103145 s x' x t a y h0)). Qed.
Lemma lem4295582 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x' : _103145) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) (h1 : term414 _103141 _103145 s x' x t a y) : (term414 _103141 _103145 s x' x t a y) = False.
Proof. exact (prop_ext (fun h2 : term414 _103141 _103145 s x' x t a y => @lem4295581 _103141 _103145 s x' x t a y h1) (fun h2 : False => @lem4294495 _103141 _103145 s x' x t a y h1)). Qed.
Lemma lem4295583 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x' : _103145) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (y : _103141) (h1 : term414 _103141 _103145 s x' x t a y) : False.
Proof. exact (EQ_MP (@lem4295582 _103141 _103145 s x' x t a y h1) (@lem4294495 _103141 _103145 s x' x t a y h1)). Qed.
Lemma lem4295584 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x' : _103145) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (h1 : term417 _103141 _103145 s x' x t a) : False.
Proof. exact (ex_elim (@lem4294303 _103141 _103145 s x' x t a h1) (fun y : _103141 => fun h0 : term416 _103141 _103145 s x' x t a y => @lem4295583 _103141 _103145 s x' x t a y h0)). Qed.
Lemma lem4295585 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (h1 : term203 _103141 _103145 s x t a) : False.
Proof. exact (ex_elim (@lem4294302 _103141 _103145 s x t a h1) (fun x' : _103145 => fun h0 : term418 _103141 _103145 s x t a x' => @lem4295584 _103141 _103145 s x' x t a h0)). Qed.
Lemma lem4295586 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (h1 : term203 _103141 _103145 s x t a) : (term203 _103141 _103145 s x t a) = False.
Proof. exact (prop_ext (fun h2 : term203 _103141 _103145 s x t a => @lem4295585 _103141 _103145 s x t a h1) (fun h2 : False => @lem4293612 _103141 _103145 s x t a h1)). Qed.
Lemma lem4295587 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) (h1 : term203 _103141 _103145 s x t a) : False.
Proof. exact (EQ_MP (@lem4295586 _103141 _103145 s x t a h1) (@lem4293612 _103141 _103145 s x t a h1)). Qed.
Lemma lem4295588 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : term202 _103141 _103145 s x t a.
Proof. exact (fun h0 : term203 _103141 _103145 s x t a => @lem4295587 _103141 _103145 s x t a h0). Qed.
Lemma lem4295589 {_103141 _103145 : Type'} (s : _103145 -> Prop) (x : prod _103145 _103141) (t : type1470 _103141 _103145) (a : _103145) : (term107 _103141 _103145 a s t x) = (term178 _103141 _103145 s x t a).
Proof. exact (EQ_MP (@lem4293611 _103141 _103145 s x t a) (@lem4295588 _103141 _103145 s x t a)). Qed.
Lemma lem4295594 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (a : _103145) : term181 _103141 _103145 s t a.
Proof. exact (fun x : prod _103145 _103141 => @lem4295589 _103141 _103145 s x t a). Qed.
Lemma lem4295599 {_103141 _103145 : Type'} (t : type1470 _103141 _103145) (a : _103145) : term193 _103141 _103145 t a.
Proof. exact (fun s : _103145 -> Prop => @lem4295594 _103141 _103145 s t a). Qed.
Lemma lem4295604 {_103141 _103145 : Type'} (a : _103145) : term197 _103141 _103145 a.
Proof. exact (fun t : type1470 _103141 _103145 => @lem4295599 _103141 _103145 t a). Qed.
Lemma lem4295609 {_103141 _103145 : Type'} : term201 _103141 _103145.
Proof. exact (fun a : _103145 => @lem4295604 _103141 _103145 a). Qed.
Lemma lem4295610 {_103141 _103145 : Type'} : term200 _103141 _103145.
Proof. exact (EQ_MP (@lem4293607 _103141 _103145) (@lem4295609 _103141 _103145)). Qed.
Lemma lem4295611 {_103141 _103145 : Type'} (a : _103145) : term498 _103141 _103145 a.
Proof. exact (@lem4295610 _103141 _103145 a). Qed.
Lemma lem4295612 {_103141 _103145 : Type'} (a : _103145) : (term498 _103141 _103145 a) = (term196 _103141 _103145 a).
Proof. exact (eq_refl (term498 _103141 _103145 a)). Qed.
Lemma lem4295613 {_103141 _103145 : Type'} (a : _103145) : term196 _103141 _103145 a.
Proof. exact (EQ_MP (@lem4295612 _103141 _103145 a) (@lem4295611 _103141 _103145 a)). Qed.
Lemma lem4295614 {_103141 _103145 : Type'} (a : _103145) (t : type1470 _103141 _103145) : term499 _103141 _103145 a t.
Proof. exact (@lem4295613 _103141 _103145 a t). Qed.
Lemma lem4295615 {_103141 _103145 : Type'} (t : type1470 _103141 _103145) (a : _103145) : (term499 _103141 _103145 a t) = (term192 _103141 _103145 t a).
Proof. exact (eq_refl (term499 _103141 _103145 a t)). Qed.
Lemma lem4295616 {_103141 _103145 : Type'} (t : type1470 _103141 _103145) (a : _103145) : term192 _103141 _103145 t a.
Proof. exact (EQ_MP (@lem4295615 _103141 _103145 t a) (@lem4295614 _103141 _103145 a t)). Qed.
Lemma lem4295617 {_103141 _103145 : Type'} (t : type1470 _103141 _103145) (a : _103145) (s : _103145 -> Prop) : term500 _103141 _103145 t a s.
Proof. exact (@lem4295616 _103141 _103145 t a s). Qed.
Lemma lem4295618 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (a : _103145) : (term500 _103141 _103145 t a s) = (term183 _103141 _103145 s t a).
Proof. exact (eq_refl (term500 _103141 _103145 t a s)). Qed.
Lemma lem4295619 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (a : _103145) : term183 _103141 _103145 s t a.
Proof. exact (EQ_MP (@lem4295618 _103141 _103145 s t a) (@lem4295617 _103141 _103145 t a s)). Qed.
Lemma lem4295621 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (a : _103145) : term183 _103141 _103145 s t a.
Proof. exact (@lem4293261 _103141 _103145 s t a (@lem4295619 _103141 _103145 s t a)). Qed.
Lemma lem4295622 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (a : _103145) (h1 : term184 _103141 _103145 s t a) : False.
Proof. exact (@lem4295621 _103141 _103145 s t a (@lem4293245 _103141 _103145 s t a h1)). Qed.
Lemma lem4295623 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (a : _103145) (h1 : term184 _103141 _103145 s t a) : (term184 _103141 _103145 s t a) = False.
Proof. exact (prop_ext (fun h2 : term184 _103141 _103145 s t a => @lem4295622 _103141 _103145 s t a h1) (fun h2 : False => @lem4293245 _103141 _103145 s t a h1)). Qed.
Lemma lem4295624 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (a : _103145) (h1 : term184 _103141 _103145 s t a) : False.
Proof. exact (EQ_MP (@lem4295623 _103141 _103145 s t a h1) (@lem4293245 _103141 _103145 s t a h1)). Qed.
Lemma lem4295625 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (a : _103145) : term183 _103141 _103145 s t a.
Proof. exact (fun h0 : term184 _103141 _103145 s t a => @lem4295624 _103141 _103145 s t a h0). Qed.
Lemma lem4295626 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (a : _103145) : term181 _103141 _103145 s t a.
Proof. exact (EQ_MP (@lem4293244 _103141 _103145 s t a) (@lem4295625 _103141 _103145 s t a)). Qed.
Lemma lem4295627 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (a : _103145) : term53 _103141 _103145 s t a.
Proof. exact (EQ_MP (@lem4293240 _103141 _103145 s t a) (@lem4295626 _103141 _103145 s t a)). Qed.
Lemma lem4295629 {A : Type'} (a : A) : term501 A a.
Proof. exact (@lem4363 A a). Qed.
Lemma lem4295630 {A : Type'} (a : A) : (term501 A a) = (term502 A a).
Proof. exact (eq_refl (term501 A a)). Qed.
Lemma lem4295631 {A : Type'} (a : A) : term502 A a.
Proof. exact (EQ_MP (@lem4295630 A a) (@lem4295629 A a)). Qed.
Lemma lem4295632 {A : Type'} (a : A) : (term502 A a) = ((term502 A a) = True).
Proof. exact (@lem7 (term502 A a)). Qed.
Lemma lem4295634 {A : Type'} (P : A -> Prop) : term503 A P.
Proof. exact (@lem6754 A P). Qed.
Lemma lem4295635 {A : Type'} (P : A -> Prop) : (term503 A P) = (term504 A P).
Proof. exact (eq_refl (term503 A P)). Qed.
Lemma lem4295636 {A : Type'} (P : A -> Prop) : term504 A P.
Proof. exact (EQ_MP (@lem4295635 A P) (@lem4295634 A P)). Qed.
Lemma lem4295637 {A : Type'} (P : A -> Prop) (Q : Prop) : term505 A P Q.
Proof. exact (@lem4295636 A P Q). Qed.
Lemma lem4295638 {A : Type'} (P : A -> Prop) (Q : Prop) : (term505 A P Q) = ((term506 A P Q) = (term507 A P Q)).
Proof. exact (eq_refl (term505 A P Q)). Qed.
Lemma lem4295640 {A : Type'} (P : A -> Prop) : term508 A P.
Proof. exact (@lem4997 A P). Qed.
Lemma lem4295641 {A : Type'} (P : A -> Prop) : (term508 A P) = (term509 A P).
Proof. exact (eq_refl (term508 A P)). Qed.
Lemma lem4295642 {A : Type'} (P : A -> Prop) : term509 A P.
Proof. exact (EQ_MP (@lem4295641 A P) (@lem4295640 A P)). Qed.
Lemma lem4295643 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term510 A P Q.
Proof. exact (@lem4295642 A P Q). Qed.
Lemma lem4295644 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term510 A P Q) = ((term511 A P Q) = (term512 A P Q)).
Proof. exact (eq_refl (term510 A P Q)). Qed.
Lemma lem4295660 (a : Prop) : term513 a.
Proof. exact (@lem9851 a). Qed.
Lemma lem4295661 (a : Prop) : (term513 a) = (term514 a).
Proof. exact (eq_refl (term513 a)). Qed.
Lemma lem4295662 (a : Prop) : term514 a.
Proof. exact (EQ_MP (@lem4295661 a) (@lem4295660 a)). Qed.
Lemma lem4295663 (a : Prop) (h1 : a = True) : a = True.
Proof. exact (h1). Qed.
Lemma lem4295664 (a : Prop) (h1 : a = False) : a = False.
Proof. exact (h1). Qed.
Lemma lem4295679 (b : Prop) (c : Prop) : (term515 b c) = (term515 b c).
Proof. exact (eq_refl (term515 b c)). Qed.
Lemma lem4295680 (b : Prop) (c : Prop) (a : Prop) (h1 : a = True) : (term516 b c a) = (term517 b c).
Proof. exact (MK_COMB (@lem4295679 b c) (@lem4295663 a h1)). Qed.
Lemma lem4295681 (b : Prop) (c : Prop) : (term517 b c) = ((term518 b c) = (term519 b c)).
Proof. exact (eq_refl (term517 b c)). Qed.
Lemma lem4295682 (b : Prop) (c : Prop) (a : Prop) : (term520 b c a) = (term520 b c a).
Proof. exact (eq_refl (term520 b c a)). Qed.
Lemma lem4295683 (a : Prop) (b : Prop) (c : Prop) : ((term516 b c a) = (term517 b c)) = ((term516 b c a) = ((term518 b c) = (term519 b c))).
Proof. exact (MK_COMB (@lem4295682 b c a) (@lem4295681 b c)). Qed.
Lemma lem4295684 (a : Prop) (b : Prop) (c : Prop) : (term516 b c a) = ((term521 a b c) = (term522 a b c)).
Proof. exact (eq_refl (term516 b c a)). Qed.
Lemma lem4295685 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4295686 (a : Prop) (b : Prop) (c : Prop) : (term520 b c a) = (term523 a b c).
Proof. exact (MK_COMB (@lem4295685) (@lem4295684 a b c)). Qed.
Lemma lem4295687 (b : Prop) (c : Prop) : ((term518 b c) = (term519 b c)) = ((term518 b c) = (term519 b c)).
Proof. exact (eq_refl ((term518 b c) = (term519 b c))). Qed.
Lemma lem4295688 (a : Prop) (b : Prop) (c : Prop) : ((term516 b c a) = ((term518 b c) = (term519 b c))) = (((term521 a b c) = (term522 a b c)) = ((term518 b c) = (term519 b c))).
Proof. exact (MK_COMB (@lem4295686 a b c) (@lem4295687 b c)). Qed.
Lemma lem4295689 (a : Prop) (b : Prop) (c : Prop) : ((term516 b c a) = (term517 b c)) = (((term521 a b c) = (term522 a b c)) = ((term518 b c) = (term519 b c))).
Proof. exact (TRANS (@lem4295683 a b c) (@lem4295688 a b c)). Qed.
Lemma lem4295690 (b : Prop) (c : Prop) (a : Prop) (h1 : a = True) : ((term521 a b c) = (term522 a b c)) = ((term518 b c) = (term519 b c)).
Proof. exact (EQ_MP (@lem4295689 a b c) (@lem4295680 b c a h1)). Qed.
Lemma lem4295691 (b : Prop) (c : Prop) (a : Prop) (h1 : a = True) : ((term518 b c) = (term519 b c)) = ((term521 a b c) = (term522 a b c)).
Proof. exact (SYM (@lem4295690 b c a h1)). Qed.
Lemma lem4295692 (b : Prop) (c : Prop) : (term515 b c) = (term515 b c).
Proof. exact (eq_refl (term515 b c)). Qed.
Lemma lem4295693 (b : Prop) (c : Prop) (a : Prop) (h1 : a = False) : (term516 b c a) = (term524 b c).
Proof. exact (MK_COMB (@lem4295692 b c) (@lem4295664 a h1)). Qed.
Lemma lem4295694 (b : Prop) (c : Prop) : (term524 b c) = ((term525 b c) = (term526 b c)).
Proof. exact (eq_refl (term524 b c)). Qed.
Lemma lem4295695 (b : Prop) (c : Prop) (a : Prop) : (term520 b c a) = (term520 b c a).
Proof. exact (eq_refl (term520 b c a)). Qed.
Lemma lem4295696 (a : Prop) (b : Prop) (c : Prop) : ((term516 b c a) = (term524 b c)) = ((term516 b c a) = ((term525 b c) = (term526 b c))).
Proof. exact (MK_COMB (@lem4295695 b c a) (@lem4295694 b c)). Qed.
Lemma lem4295697 (a : Prop) (b : Prop) (c : Prop) : (term516 b c a) = ((term521 a b c) = (term522 a b c)).
Proof. exact (eq_refl (term516 b c a)). Qed.
Lemma lem4295698 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4295699 (a : Prop) (b : Prop) (c : Prop) : (term520 b c a) = (term523 a b c).
Proof. exact (MK_COMB (@lem4295698) (@lem4295697 a b c)). Qed.
Lemma lem4295700 (b : Prop) (c : Prop) : ((term525 b c) = (term526 b c)) = ((term525 b c) = (term526 b c)).
Proof. exact (eq_refl ((term525 b c) = (term526 b c))). Qed.
Lemma lem4295701 (a : Prop) (b : Prop) (c : Prop) : ((term516 b c a) = ((term525 b c) = (term526 b c))) = (((term521 a b c) = (term522 a b c)) = ((term525 b c) = (term526 b c))).
Proof. exact (MK_COMB (@lem4295699 a b c) (@lem4295700 b c)). Qed.
Lemma lem4295702 (a : Prop) (b : Prop) (c : Prop) : ((term516 b c a) = (term524 b c)) = (((term521 a b c) = (term522 a b c)) = ((term525 b c) = (term526 b c))).
Proof. exact (TRANS (@lem4295696 a b c) (@lem4295701 a b c)). Qed.
Lemma lem4295703 (b : Prop) (c : Prop) (a : Prop) (h1 : a = False) : ((term521 a b c) = (term522 a b c)) = ((term525 b c) = (term526 b c)).
Proof. exact (EQ_MP (@lem4295702 a b c) (@lem4295693 b c a h1)). Qed.
Lemma lem4295704 (b : Prop) (c : Prop) (a : Prop) (h1 : a = False) : ((term525 b c) = (term526 b c)) = ((term521 a b c) = (term522 a b c)).
Proof. exact (SYM (@lem4295703 b c a h1)). Qed.
Lemma lem4295710 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem4295711 (b : Prop) : (True \/ b) = True.
Proof. exact (@lem4295710 b). Qed.
Lemma lem4295712 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4295713 (b : Prop) : (term527 b) = (imp True).
Proof. exact (MK_COMB (@lem4295712) (@lem4295711 b)). Qed.
Lemma lem4295714 (c : Prop) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem4295715 (b : Prop) (c : Prop) : (term518 b c) = (True -> c).
Proof. exact (MK_COMB (@lem4295713 b) (@lem4295714 c)). Qed.
Lemma lem4295717 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem4295718 (c : Prop) : (True -> c) = c.
Proof. exact (@lem4295717 c). Qed.
Lemma lem4295719 (b : Prop) (c : Prop) : (term518 b c) = c.
Proof. exact (TRANS (@lem4295715 b c) (@lem4295718 c)). Qed.
Lemma lem4295720 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4295721 (b : Prop) (c : Prop) : (term528 b c) = (@eq Prop c).
Proof. exact (MK_COMB (@lem4295720) (@lem4295719 b c)). Qed.
Lemma lem4295725 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem4295726 (c : Prop) : (True -> c) = c.
Proof. exact (@lem4295725 c). Qed.
Lemma lem4295727 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4295728 (c : Prop) : (term529 c) = (and c).
Proof. exact (MK_COMB (@lem4295727) (@lem4295726 c)). Qed.
Lemma lem4295731 (b : Prop) (c : Prop) : (b -> c) = (b -> c).
Proof. exact (eq_refl (b -> c)). Qed.
Lemma lem4295732 (b : Prop) (c : Prop) : (term519 b c) = (term530 b c).
Proof. exact (MK_COMB (@lem4295728 c) (@lem4295731 b c)). Qed.
Lemma lem4295735 (b : Prop) (c : Prop) : ((term518 b c) = (term519 b c)) = (c = (term530 b c)).
Proof. exact (MK_COMB (@lem4295721 b c) (@lem4295732 b c)). Qed.
Lemma lem4295738 (b : Prop) (c : Prop) : (c = (term530 b c)) = ((term518 b c) = (term519 b c)).
Proof. exact (SYM (@lem4295735 b c)). Qed.
Lemma lem4295739 (c : Prop) : term513 c.
Proof. exact (@lem9851 c). Qed.
Lemma lem4295740 (c : Prop) : (term513 c) = (term514 c).
Proof. exact (eq_refl (term513 c)). Qed.
Lemma lem4295741 (c : Prop) : term514 c.
Proof. exact (EQ_MP (@lem4295740 c) (@lem4295739 c)). Qed.
Lemma lem4295742 (c : Prop) (h1 : c = True) : c = True.
Proof. exact (h1). Qed.
Lemma lem4295743 (c : Prop) (h1 : c = False) : c = False.
Proof. exact (h1). Qed.
Lemma lem4295752 (b : Prop) : (term531 b) = (term531 b).
Proof. exact (eq_refl (term531 b)). Qed.
Lemma lem4295753 (b : Prop) (c : Prop) (h1 : c = True) : (term532 b c) = (term533 b).
Proof. exact (MK_COMB (@lem4295752 b) (@lem4295742 c h1)). Qed.
Lemma lem4295754 (b : Prop) : (term533 b) = (True = (term534 b)).
Proof. exact (eq_refl (term533 b)). Qed.
Lemma lem4295755 (b : Prop) (c : Prop) : (term535 b c) = (term535 b c).
Proof. exact (eq_refl (term535 b c)). Qed.
Lemma lem4295756 (c : Prop) (b : Prop) : ((term532 b c) = (term533 b)) = ((term532 b c) = (True = (term534 b))).
Proof. exact (MK_COMB (@lem4295755 b c) (@lem4295754 b)). Qed.
Lemma lem4295757 (b : Prop) (c : Prop) : (term532 b c) = (c = (term530 b c)).
Proof. exact (eq_refl (term532 b c)). Qed.
Lemma lem4295758 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4295759 (b : Prop) (c : Prop) : (term535 b c) = (term536 b c).
Proof. exact (MK_COMB (@lem4295758) (@lem4295757 b c)). Qed.
Lemma lem4295760 (b : Prop) : (True = (term534 b)) = (True = (term534 b)).
Proof. exact (eq_refl (True = (term534 b))). Qed.
Lemma lem4295761 (c : Prop) (b : Prop) : ((term532 b c) = (True = (term534 b))) = ((c = (term530 b c)) = (True = (term534 b))).
Proof. exact (MK_COMB (@lem4295759 b c) (@lem4295760 b)). Qed.
Lemma lem4295762 (c : Prop) (b : Prop) : ((term532 b c) = (term533 b)) = ((c = (term530 b c)) = (True = (term534 b))).
Proof. exact (TRANS (@lem4295756 c b) (@lem4295761 c b)). Qed.
Lemma lem4295763 (b : Prop) (c : Prop) (h1 : c = True) : (c = (term530 b c)) = (True = (term534 b)).
Proof. exact (EQ_MP (@lem4295762 c b) (@lem4295753 b c h1)). Qed.
Lemma lem4295764 (b : Prop) (c : Prop) (h1 : c = True) : (True = (term534 b)) = (c = (term530 b c)).
Proof. exact (SYM (@lem4295763 b c h1)). Qed.
Lemma lem4295765 (b : Prop) : (term531 b) = (term531 b).
Proof. exact (eq_refl (term531 b)). Qed.
Lemma lem4295766 (b : Prop) (c : Prop) (h1 : c = False) : (term532 b c) = (term537 b).
Proof. exact (MK_COMB (@lem4295765 b) (@lem4295743 c h1)). Qed.
Lemma lem4295767 (b : Prop) : (term537 b) = (False = (term538 b)).
Proof. exact (eq_refl (term537 b)). Qed.
Lemma lem4295768 (b : Prop) (c : Prop) : (term535 b c) = (term535 b c).
Proof. exact (eq_refl (term535 b c)). Qed.
Lemma lem4295769 (c : Prop) (b : Prop) : ((term532 b c) = (term537 b)) = ((term532 b c) = (False = (term538 b))).
Proof. exact (MK_COMB (@lem4295768 b c) (@lem4295767 b)). Qed.
Lemma lem4295770 (b : Prop) (c : Prop) : (term532 b c) = (c = (term530 b c)).
Proof. exact (eq_refl (term532 b c)). Qed.
Lemma lem4295771 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4295772 (b : Prop) (c : Prop) : (term535 b c) = (term536 b c).
Proof. exact (MK_COMB (@lem4295771) (@lem4295770 b c)). Qed.
Lemma lem4295773 (b : Prop) : (False = (term538 b)) = (False = (term538 b)).
Proof. exact (eq_refl (False = (term538 b))). Qed.
Lemma lem4295774 (c : Prop) (b : Prop) : ((term532 b c) = (False = (term538 b))) = ((c = (term530 b c)) = (False = (term538 b))).
Proof. exact (MK_COMB (@lem4295772 b c) (@lem4295773 b)). Qed.
Lemma lem4295775 (c : Prop) (b : Prop) : ((term532 b c) = (term537 b)) = ((c = (term530 b c)) = (False = (term538 b))).
Proof. exact (TRANS (@lem4295769 c b) (@lem4295774 c b)). Qed.
Lemma lem4295776 (b : Prop) (c : Prop) (h1 : c = False) : (c = (term530 b c)) = (False = (term538 b)).
Proof. exact (EQ_MP (@lem4295775 c b) (@lem4295766 b c h1)). Qed.
Lemma lem4295777 (b : Prop) (c : Prop) (h1 : c = False) : (False = (term538 b)) = (c = (term530 b c)).
Proof. exact (SYM (@lem4295776 b c h1)). Qed.
Lemma lem4295779 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem4295780 (b : Prop) : (True = (term534 b)) = (term534 b).
Proof. exact (@lem4295779 (term534 b)). Qed.
Lemma lem4295782 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4295783 (b : Prop) : (term534 b) = (b -> True).
Proof. exact (@lem4295782 (b -> True)). Qed.
Lemma lem4295785 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4295786 (b : Prop) : (b -> True) = True.
Proof. exact (@lem4295785 b). Qed.
Lemma lem4295787 (b : Prop) : (term534 b) = True.
Proof. exact (TRANS (@lem4295783 b) (@lem4295786 b)). Qed.
Lemma lem4295788 (b : Prop) : (True = (term534 b)) = True.
Proof. exact (TRANS (@lem4295780 b) (@lem4295787 b)). Qed.
Lemma lem4295789 (b : Prop) : True = (True = (term534 b)).
Proof. exact (SYM (@lem4295788 b)). Qed.
Lemma lem4295790 (b : Prop) : True = (term534 b).
Proof. exact (EQ_MP (@lem4295789 b) (@lem0)). Qed.
Lemma lem4295792 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem4295793 (b : Prop) : (False = (term538 b)) = (term539 b).
Proof. exact (@lem4295792 (term538 b)). Qed.
Lemma lem4295795 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem4295796 (b : Prop) : (term538 b) = False.
Proof. exact (@lem4295795 (b -> False)). Qed.
Lemma lem4295797 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4295798 (b : Prop) : (term539 b) = (~ False).
Proof. exact (MK_COMB (@lem4295797) (@lem4295796 b)). Qed.
Lemma lem4295800 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem4295801 (b : Prop) : (term539 b) = True.
Proof. exact (TRANS (@lem4295798 b) (@lem4295800)). Qed.
Lemma lem4295802 (b : Prop) : (False = (term538 b)) = True.
Proof. exact (TRANS (@lem4295793 b) (@lem4295801 b)). Qed.
Lemma lem4295803 (b : Prop) : True = (False = (term538 b)).
Proof. exact (SYM (@lem4295802 b)). Qed.
Lemma lem4295804 (b : Prop) : False = (term538 b).
Proof. exact (EQ_MP (@lem4295803 b) (@lem0)). Qed.
Lemma lem4295805 (b : Prop) (c : Prop) (h1 : c = False) : c = (term530 b c).
Proof. exact (EQ_MP (@lem4295777 b c h1) (@lem4295804 b)). Qed.
Lemma lem4295806 (b : Prop) (c : Prop) (h1 : c = True) : c = (term530 b c).
Proof. exact (EQ_MP (@lem4295764 b c h1) (@lem4295790 b)). Qed.
Lemma lem4295808 (b : Prop) (c : Prop) : c = (term530 b c).
Proof. exact (or_elim (@lem4295741 c) (fun h0 : c = True => @lem4295806 b c h0) (fun h0 : c = False => @lem4295805 b c h0)). Qed.
Lemma lem4295809 (b : Prop) (c : Prop) : (term518 b c) = (term519 b c).
Proof. exact (EQ_MP (@lem4295738 b c) (@lem4295808 b c)). Qed.
Lemma lem4295815 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem4295816 (b : Prop) : (False \/ b) = b.
Proof. exact (@lem4295815 b). Qed.
Lemma lem4295817 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4295818 (b : Prop) : (term540 b) = (imp b).
Proof. exact (MK_COMB (@lem4295817) (@lem4295816 b)). Qed.
Lemma lem4295819 (c : Prop) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem4295820 (b : Prop) (c : Prop) : (term525 b c) = (b -> c).
Proof. exact (MK_COMB (@lem4295818 b) (@lem4295819 c)). Qed.
Lemma lem4295823 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4295824 (b : Prop) (c : Prop) : (term541 b c) = (term542 b c).
Proof. exact (MK_COMB (@lem4295823) (@lem4295820 b c)). Qed.
Lemma lem4295828 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem4295829 (c : Prop) : (False -> c) = True.
Proof. exact (@lem4295828 c). Qed.
Lemma lem4295830 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4295831 (c : Prop) : (term543 c) = (and True).
Proof. exact (MK_COMB (@lem4295830) (@lem4295829 c)). Qed.
Lemma lem4295834 (b : Prop) (c : Prop) : (b -> c) = (b -> c).
Proof. exact (eq_refl (b -> c)). Qed.
Lemma lem4295835 (b : Prop) (c : Prop) : (term526 b c) = (term544 b c).
Proof. exact (MK_COMB (@lem4295831 c) (@lem4295834 b c)). Qed.
Lemma lem4295837 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4295838 (b : Prop) (c : Prop) : (term544 b c) = (b -> c).
Proof. exact (@lem4295837 (b -> c)). Qed.
Lemma lem4295841 (b : Prop) (c : Prop) : (term526 b c) = (b -> c).
Proof. exact (TRANS (@lem4295835 b c) (@lem4295838 b c)). Qed.
Lemma lem4295842 (b : Prop) (c : Prop) : ((term525 b c) = (term526 b c)) = ((b -> c) = (b -> c)).
Proof. exact (MK_COMB (@lem4295824 b c) (@lem4295841 b c)). Qed.
Lemma lem4295844 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4295845 (x : Prop) : (x = x) = True.
Proof. exact (@lem4295844 Prop x). Qed.
Lemma lem4295846 (b : Prop) (c : Prop) : ((b -> c) = (b -> c)) = True.
Proof. exact (@lem4295845 (b -> c)). Qed.
Lemma lem4295847 (b : Prop) (c : Prop) : ((term525 b c) = (term526 b c)) = True.
Proof. exact (TRANS (@lem4295842 b c) (@lem4295846 b c)). Qed.
Lemma lem4295848 (b : Prop) (c : Prop) : True = ((term525 b c) = (term526 b c)).
Proof. exact (SYM (@lem4295847 b c)). Qed.
Lemma lem4295849 (b : Prop) (c : Prop) : (term525 b c) = (term526 b c).
Proof. exact (EQ_MP (@lem4295848 b c) (@lem0)). Qed.
Lemma lem4295850 (b : Prop) (c : Prop) (a : Prop) (h1 : a = False) : (term521 a b c) = (term522 a b c).
Proof. exact (EQ_MP (@lem4295704 b c a h1) (@lem4295849 b c)). Qed.
Lemma lem4295851 (b : Prop) (c : Prop) (a : Prop) (h1 : a = True) : (term521 a b c) = (term522 a b c).
Proof. exact (EQ_MP (@lem4295691 b c a h1) (@lem4295809 b c)). Qed.
Lemma lem4295865 {A : Type'} (s : A -> Prop) : term545 A s.
Proof. exact (@lem3864294 A s). Qed.
Lemma lem4295866 {A : Type'} (s : A -> Prop) : (term545 A s) = ((term546 A s) = (s = (@EMPTY A))).
Proof. exact (eq_refl (term545 A s)). Qed.
Lemma lem4295898 : term547.
Proof. exact (proj1 (@lem81645)). Qed.
Lemma lem4295899 (n : nat) : term548 n.
Proof. exact (@lem4295898 n). Qed.
Lemma lem4295900 (n : nat) : (term548 n) = ((term549 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term548 n)). Qed.
Lemma lem4295902 {A : Type'} (x : A) : term550 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem4295903 {A : Type'} (x : A) : (term550 A x) = (term551 A x).
Proof. exact (eq_refl (term550 A x)). Qed.
Lemma lem4295904 {A : Type'} (x : A) : term551 A x.
Proof. exact (EQ_MP (@lem4295903 A x) (@lem4295902 A x)). Qed.
Lemma lem4295905 {A : Type'} (x : A) (y : A) : term552 A x y.
Proof. exact (@lem4295904 A x y). Qed.
Lemma lem4295906 {A : Type'} (y : A) (x : A) : (term552 A x y) = (term553 A y x).
Proof. exact (eq_refl (term552 A x y)). Qed.
Lemma lem4295907 {A : Type'} (y : A) (x : A) : term553 A y x.
Proof. exact (EQ_MP (@lem4295906 A y x) (@lem4295905 A x y)). Qed.
Lemma lem4295908 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term554 A y x s.
Proof. exact (@lem4295907 A y x s). Qed.
Lemma lem4295909 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term554 A y x s) = ((term555 A x y s) = (term81 A y x s)).
Proof. exact (eq_refl (term554 A y x s)). Qed.
Lemma lem4295911 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem4295912 {A : Type'} (x : A) : (term0 A x) = (term1 A x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem4295913 {A : Type'} (x : A) : term1 A x.
Proof. exact (EQ_MP (@lem4295912 A x) (@lem4295911 A x)). Qed.
Lemma lem4295914 {A : Type'} (x : A) : term2 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem4295916 {A : Type'} : term556 A.
Proof. exact (proj2 (@lem3840691 A)). Qed.
Lemma lem4295917 {A : Type'} (x : A) : term557 A x.
Proof. exact (@lem4295916 A x). Qed.
Lemma lem4295918 {A : Type'} (x : A) : (term557 A x) = (term558 A x).
Proof. exact (eq_refl (term557 A x)). Qed.
Lemma lem4295919 {A : Type'} (x : A) : term558 A x.
Proof. exact (EQ_MP (@lem4295918 A x) (@lem4295917 A x)). Qed.
Lemma lem4295920 {A : Type'} (x : A) (s : A -> Prop) : term559 A x s.
Proof. exact (@lem4295919 A x s). Qed.
Lemma lem4295921 {A : Type'} (x : A) (s : A -> Prop) : (term559 A x s) = (term560 A x s).
Proof. exact (eq_refl (term559 A x s)). Qed.
Lemma lem4295922 {A : Type'} (x : A) (s : A -> Prop) : term560 A x s.
Proof. exact (EQ_MP (@lem4295921 A x s) (@lem4295920 A x s)). Qed.
Lemma lem4295923 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4295924 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : (term561 A x s) = (term562 A x s).
Proof. exact (@lem4295922 A x s (@lem4295923 A s h1)). Qed.
Lemma lem4295931 {A : Type'} (h1 : term563 A) : term563 A.
Proof. exact (h1). Qed.
Lemma lem4295932 {A : Type'} (P : type686 A) (h1 : term563 A) : term564 A P.
Proof. exact (@lem4295931 A h1 P). Qed.
Lemma lem4295933 {A : Type'} (P : type686 A) : (term564 A P) = (term565 A P).
Proof. exact (eq_refl (term564 A P)). Qed.
Lemma lem4295934 {A : Type'} (P : type686 A) (h1 : term563 A) : term565 A P.
Proof. exact (EQ_MP (@lem4295933 A P) (@lem4295932 A P h1)). Qed.
Lemma lem4295935 {A : Type'} (P : type686 A) (h1 : term566 A P) : term566 A P.
Proof. exact (h1). Qed.
Lemma lem4295936 {A : Type'} (P : type686 A) (h1 : term563 A) (h2 : term566 A P) : term567 A P.
Proof. exact (@lem4295934 A P h1 (@lem4295935 A P h2)). Qed.
Lemma lem4295937 {A : Type'} (P : type686 A) (h1 : term566 A P) : term568 A P.
Proof. exact (fun h0 : term563 A => @lem4295936 A P h0 h1). Qed.
Lemma lem4295938 {A : Type'} (h1 : term563 A) : term563 A.
Proof. exact (h1). Qed.
Lemma lem4295939 {A : Type'} (P : type686 A) (h1 : term563 A) (h2 : term566 A P) : term567 A P.
Proof. exact (@lem4295937 A P h2 (@lem4295938 A h1)). Qed.
Lemma lem4295940 {A : Type'} (P : type686 A) (h1 : term563 A) : term565 A P.
Proof. exact (fun h0 : term566 A P => @lem4295939 A P h1 h0). Qed.
Lemma lem4295941 {A : Type'} (h1 : term563 A) : term563 A.
Proof. exact (fun P : type686 A => @lem4295940 A P h1). Qed.
Lemma lem4295942 {A : Type'} : term569 A.
Proof. exact (fun h0 : term563 A => @lem4295941 A h0). Qed.
Lemma lem4295943 {A : Type'} : term563 A.
Proof. exact (@lem4295942 A (@lem3558722 A)). Qed.
Lemma lem4295944 {A : Type'} (P : type686 A) : term564 A P.
Proof. exact (@lem4295943 A P). Qed.
Lemma lem4295945 {A : Type'} (P : type686 A) : (term564 A P) = (term565 A P).
Proof. exact (eq_refl (term564 A P)). Qed.
Lemma lem4295947 {A : Type'} (P : Prop) : term570 A P.
Proof. exact (@lem6534 A P). Qed.
Lemma lem4295948 {A : Type'} (P : Prop) : (term570 A P) = (term571 A P).
Proof. exact (eq_refl (term570 A P)). Qed.
Lemma lem4295949 {A : Type'} (P : Prop) : term571 A P.
Proof. exact (EQ_MP (@lem4295948 A P) (@lem4295947 A P)). Qed.
Lemma lem4295950 {A : Type'} (P : Prop) (Q : A -> Prop) : term572 A P Q.
Proof. exact (@lem4295949 A P Q). Qed.
Lemma lem4295951 {A : Type'} (P : Prop) (Q : A -> Prop) : (term572 A P Q) = ((term573 A P Q) = (term574 A P Q)).
Proof. exact (eq_refl (term572 A P Q)). Qed.
Lemma lem4295953 {_100044 : Type'} (s : _100044 -> Prop) : term575 _100044 s.
Proof. exact (@lem3863773 _100044 s). Qed.
Lemma lem4295954 {_100044 : Type'} (s : _100044 -> Prop) : (term575 _100044 s) = (term576 _100044 s).
Proof. exact (eq_refl (term575 _100044 s)). Qed.
Lemma lem4295955 {_100044 : Type'} (s : _100044 -> Prop) : term576 _100044 s.
Proof. exact (EQ_MP (@lem4295954 _100044 s) (@lem4295953 _100044 s)). Qed.
Lemma lem4295956 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : term577 _100044 s n.
Proof. exact (@lem4295955 _100044 s n). Qed.
Lemma lem4295957 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term577 _100044 s n) = ((@HAS_SIZE _100044 s n) = (term578 _100044 s n)).
Proof. exact (eq_refl (term577 _100044 s n)). Qed.
Lemma lem4295960 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (@HAS_SIZE _100044 s n) = (term578 _100044 s n).
Proof. exact (EQ_MP (@lem4295957 _100044 s n) (@lem4295956 _100044 s n)). Qed.
Lemma lem4295961 {A : Type'} (s : A -> Prop) (n : nat) : (@HAS_SIZE A s n) = (term578 A s n).
Proof. exact (@lem4295960 A s n). Qed.
Lemma lem4295962 {A : Type'} (s : A -> Prop) (m : nat) : (@HAS_SIZE A s m) = (term578 A s m).
Proof. exact (@lem4295961 A s m). Qed.
Lemma lem4295963 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4295964 {A : Type'} (s : A -> Prop) (m : nat) : (term579 A s m) = (term580 A s m).
Proof. exact (MK_COMB (@lem4295963) (@lem4295962 A s m)). Qed.
Lemma lem4295965 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (n : nat) : (term581 A B s t n) = (term581 A B s t n).
Proof. exact (eq_refl (term581 A B s t n)). Qed.
Lemma lem4295966 {A B : Type'} (m : nat) (s : A -> Prop) (t : type1413 A B) (n : nat) : (term582 A B m s t n) = (term583 A B m s t n).
Proof. exact (MK_COMB (@lem4295964 A s m) (@lem4295965 A B s t n)). Qed.
Lemma lem4295967 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4295968 {A B : Type'} (m : nat) (s : A -> Prop) (t : type1413 A B) (n : nat) : (term584 A B m s t n) = (term585 A B m s t n).
Proof. exact (MK_COMB (@lem4295967) (@lem4295966 A B m s t n)). Qed.
Lemma lem4295969 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) : (term586 A B s t m n) = (term586 A B s t m n).
Proof. exact (eq_refl (term586 A B s t m n)). Qed.
Lemma lem4295970 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) : (term587 A B s t m n) = (term588 A B s t m n).
Proof. exact (MK_COMB (@lem4295968 A B m s t n) (@lem4295969 A B s t m n)). Qed.
Lemma lem4295971 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : (term589 A B s t m) = (term590 A B s t m).
Proof. exact (fun_ext (fun n : nat => @lem4295970 A B s t m n)). Qed.
Lemma lem4295972 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4295973 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : (term591 A B s t m) = (term592 A B s t m).
Proof. exact (MK_COMB (@lem4295972) (@lem4295971 A B s t m)). Qed.
Lemma lem4295974 {A B : Type'} (s : A -> Prop) (m : nat) : (term593 A B s m) = (term594 A B s m).
Proof. exact (fun_ext (fun t : type1413 A B => @lem4295973 A B s t m)). Qed.
Lemma lem4295975 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem4295976 {A B : Type'} (s : A -> Prop) (m : nat) : (term595 A B s m) = (term596 A B s m).
Proof. exact (MK_COMB (@lem4295975 A B) (@lem4295974 A B s m)). Qed.
Lemma lem4295977 {A B : Type'} (s : A -> Prop) : (term597 A B s) = (term598 A B s).
Proof. exact (fun_ext (fun m : nat => @lem4295976 A B s m)). Qed.
Lemma lem4295978 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4295979 {A B : Type'} (s : A -> Prop) : (term599 A B s) = (term600 A B s).
Proof. exact (MK_COMB (@lem4295978) (@lem4295977 A B s)). Qed.
Lemma lem4295980 {A B : Type'} : (term601 A B) = (term602 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4295979 A B s)). Qed.
Lemma lem4295981 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4295982 {A B : Type'} : (term603 A B) = (term604 A B).
Proof. exact (MK_COMB (@lem4295981 A) (@lem4295980 A B)). Qed.
Lemma lem4295983 {A B : Type'} : (term604 A B) = (term603 A B).
Proof. exact (SYM (@lem4295982 A B)). Qed.
Lemma lem4296021 (p : Prop) (q : Prop) (r : Prop) : (term605 p q r) = (term606 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem4296022 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) : (term588 A B s t m n) = (term607 A B s t m n).
Proof. exact (@lem4296021 (term578 A s m) (term581 A B s t n) (term586 A B s t m n)). Qed.
Lemma lem4296024 (p : Prop) (q : Prop) (r : Prop) : (term605 p q r) = (term606 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem4296025 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) : (term607 A B s t m n) = (term608 A B s t m n).
Proof. exact (@lem4296024 (@FINITE A s) ((@CARD A s) = m) (term609 A B s t m n)). Qed.
Lemma lem4296028 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) : (term588 A B s t m n) = (term608 A B s t m n).
Proof. exact (TRANS (@lem4296022 A B s t m n) (@lem4296025 A B s t m n)). Qed.
Lemma lem4296073 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : (term590 A B s t m) = (term610 A B s t m).
Proof. exact (fun_ext (fun n : nat => @lem4296028 A B s t m n)). Qed.
Lemma lem4296074 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4296075 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : (term592 A B s t m) = (term611 A B s t m).
Proof. exact (MK_COMB (@lem4296074) (@lem4296073 A B s t m)). Qed.
Lemma lem4296077 {A : Type'} (P : Prop) (Q : A -> Prop) : (term573 A P Q) = (term574 A P Q).
Proof. exact (EQ_MP (@lem4295951 A P Q) (@lem4295950 A P Q)). Qed.
Lemma lem4296078 (P : Prop) (Q : nat -> Prop) : (term612 P Q) = (term613 P Q).
Proof. exact (@lem4296077 nat P Q). Qed.
Lemma lem4296079 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : (term614 A B s t m) = (term615 A B s t m).
Proof. exact (@lem4296078 (@FINITE A s) (term616 A B s t m)). Qed.
Lemma lem4296080 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) : (term617 A B s t m n) = (term618 A B s t m n).
Proof. exact (eq_refl (term617 A B s t m n)). Qed.
Lemma lem4296081 {A : Type'} (s : A -> Prop) : (term619 A s) = (term619 A s).
Proof. exact (eq_refl (term619 A s)). Qed.
Lemma lem4296082 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) : (term620 A B s t m n) = (term608 A B s t m n).
Proof. exact (MK_COMB (@lem4296081 A s) (@lem4296080 A B s t m n)). Qed.
Lemma lem4296083 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : (term621 A B s t m) = (term610 A B s t m).
Proof. exact (fun_ext (fun n : nat => @lem4296082 A B s t m n)). Qed.
Lemma lem4296084 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4296085 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : (term614 A B s t m) = (term611 A B s t m).
Proof. exact (MK_COMB (@lem4296084) (@lem4296083 A B s t m)). Qed.
Lemma lem4296086 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4296087 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : (term622 A B s t m) = (term623 A B s t m).
Proof. exact (MK_COMB (@lem4296086) (@lem4296085 A B s t m)). Qed.
Lemma lem4296088 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) : (term617 A B s t m n) = (term618 A B s t m n).
Proof. exact (eq_refl (term617 A B s t m n)). Qed.
Lemma lem4296089 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : (term624 A B s t m) = (term616 A B s t m).
Proof. exact (fun_ext (fun n : nat => @lem4296088 A B s t m n)). Qed.
Lemma lem4296090 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4296091 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : (term625 A B s t m) = (term626 A B s t m).
Proof. exact (MK_COMB (@lem4296090) (@lem4296089 A B s t m)). Qed.
Lemma lem4296092 {A : Type'} (s : A -> Prop) : (term619 A s) = (term619 A s).
Proof. exact (eq_refl (term619 A s)). Qed.
Lemma lem4296093 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : (term615 A B s t m) = (term627 A B s t m).
Proof. exact (MK_COMB (@lem4296092 A s) (@lem4296091 A B s t m)). Qed.
Lemma lem4296094 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : ((term614 A B s t m) = (term615 A B s t m)) = ((term611 A B s t m) = (term627 A B s t m)).
Proof. exact (MK_COMB (@lem4296087 A B s t m) (@lem4296093 A B s t m)). Qed.
Lemma lem4296095 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : (term611 A B s t m) = (term627 A B s t m).
Proof. exact (EQ_MP (@lem4296094 A B s t m) (@lem4296079 A B s t m)). Qed.
Lemma lem4296099 {A : Type'} (P : Prop) (Q : A -> Prop) : (term573 A P Q) = (term574 A P Q).
Proof. exact (EQ_MP (@lem4295951 A P Q) (@lem4295950 A P Q)). Qed.
Lemma lem4296100 (P : Prop) (Q : nat -> Prop) : (term612 P Q) = (term613 P Q).
Proof. exact (@lem4296099 nat P Q). Qed.
Lemma lem4296101 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : (term628 A B s t m) = (term629 A B s t m).
Proof. exact (@lem4296100 ((@CARD A s) = m) (term630 A B s t m)). Qed.
Lemma lem4296102 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) : (term631 A B s t m n) = (term609 A B s t m n).
Proof. exact (eq_refl (term631 A B s t m n)). Qed.
Lemma lem4296103 {A : Type'} (s : A -> Prop) (m : nat) : (term632 A s m) = (term632 A s m).
Proof. exact (eq_refl (term632 A s m)). Qed.
Lemma lem4296104 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) : (term633 A B s t m n) = (term618 A B s t m n).
Proof. exact (MK_COMB (@lem4296103 A s m) (@lem4296102 A B s t m n)). Qed.
Lemma lem4296105 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : (term634 A B s t m) = (term616 A B s t m).
Proof. exact (fun_ext (fun n : nat => @lem4296104 A B s t m n)). Qed.
Lemma lem4296106 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4296107 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : (term628 A B s t m) = (term626 A B s t m).
Proof. exact (MK_COMB (@lem4296106) (@lem4296105 A B s t m)). Qed.
Lemma lem4296108 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4296109 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : (term635 A B s t m) = (term636 A B s t m).
Proof. exact (MK_COMB (@lem4296108) (@lem4296107 A B s t m)). Qed.
Lemma lem4296110 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) : (term631 A B s t m n) = (term609 A B s t m n).
Proof. exact (eq_refl (term631 A B s t m n)). Qed.
Lemma lem4296111 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : (term637 A B s t m) = (term630 A B s t m).
Proof. exact (fun_ext (fun n : nat => @lem4296110 A B s t m n)). Qed.
Lemma lem4296112 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4296113 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : (term638 A B s t m) = (term639 A B s t m).
Proof. exact (MK_COMB (@lem4296112) (@lem4296111 A B s t m)). Qed.
Lemma lem4296114 {A : Type'} (s : A -> Prop) (m : nat) : (term632 A s m) = (term632 A s m).
Proof. exact (eq_refl (term632 A s m)). Qed.
Lemma lem4296115 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : (term629 A B s t m) = (term640 A B s t m).
Proof. exact (MK_COMB (@lem4296114 A s m) (@lem4296113 A B s t m)). Qed.
Lemma lem4296116 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : ((term628 A B s t m) = (term629 A B s t m)) = ((term626 A B s t m) = (term640 A B s t m)).
Proof. exact (MK_COMB (@lem4296109 A B s t m) (@lem4296115 A B s t m)). Qed.
Lemma lem4296117 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : (term626 A B s t m) = (term640 A B s t m).
Proof. exact (EQ_MP (@lem4296116 A B s t m) (@lem4296101 A B s t m)). Qed.
Lemma lem4296186 {A : Type'} (s : A -> Prop) : (term619 A s) = (term619 A s).
Proof. exact (eq_refl (term619 A s)). Qed.
Lemma lem4296187 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : (term627 A B s t m) = (term641 A B s t m).
Proof. exact (MK_COMB (@lem4296186 A s) (@lem4296117 A B s t m)). Qed.
Lemma lem4296190 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : (term611 A B s t m) = (term641 A B s t m).
Proof. exact (TRANS (@lem4296095 A B s t m) (@lem4296187 A B s t m)). Qed.
Lemma lem4296191 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : (term592 A B s t m) = (term641 A B s t m).
Proof. exact (TRANS (@lem4296075 A B s t m) (@lem4296190 A B s t m)). Qed.
Lemma lem4296192 {A B : Type'} (s : A -> Prop) (m : nat) : (term594 A B s m) = (term642 A B s m).
Proof. exact (fun_ext (fun t : type1413 A B => @lem4296191 A B s t m)). Qed.
Lemma lem4296193 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem4296194 {A B : Type'} (s : A -> Prop) (m : nat) : (term596 A B s m) = (term643 A B s m).
Proof. exact (MK_COMB (@lem4296193 A B) (@lem4296192 A B s m)). Qed.
Lemma lem4296196 {A : Type'} (P : Prop) (Q : A -> Prop) : (term573 A P Q) = (term574 A P Q).
Proof. exact (EQ_MP (@lem4295951 A P Q) (@lem4295950 A P Q)). Qed.
Lemma lem4296197 {A B : Type'} (P : Prop) (Q : type475 A B) : (term644 A B P Q) = (term645 A B P Q).
Proof. exact (@lem4296196 (type1413 A B) P Q). Qed.
Lemma lem4296198 {A B : Type'} (s : A -> Prop) (m : nat) : (term646 A B s m) = (term647 A B s m).
Proof. exact (@lem4296197 A B (@FINITE A s) (term648 A B s m)). Qed.
Lemma lem4296199 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : (term649 A B s m t) = (term640 A B s t m).
Proof. exact (eq_refl (term649 A B s m t)). Qed.
Lemma lem4296200 {A : Type'} (s : A -> Prop) : (term619 A s) = (term619 A s).
Proof. exact (eq_refl (term619 A s)). Qed.
Lemma lem4296201 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : (term650 A B s m t) = (term641 A B s t m).
Proof. exact (MK_COMB (@lem4296200 A s) (@lem4296199 A B s t m)). Qed.
Lemma lem4296202 {A B : Type'} (s : A -> Prop) (m : nat) : (term651 A B s m) = (term642 A B s m).
Proof. exact (fun_ext (fun t : type1413 A B => @lem4296201 A B s t m)). Qed.
Lemma lem4296203 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem4296204 {A B : Type'} (s : A -> Prop) (m : nat) : (term646 A B s m) = (term643 A B s m).
Proof. exact (MK_COMB (@lem4296203 A B) (@lem4296202 A B s m)). Qed.
Lemma lem4296205 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4296206 {A B : Type'} (s : A -> Prop) (m : nat) : (term652 A B s m) = (term653 A B s m).
Proof. exact (MK_COMB (@lem4296205) (@lem4296204 A B s m)). Qed.
Lemma lem4296207 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : (term649 A B s m t) = (term640 A B s t m).
Proof. exact (eq_refl (term649 A B s m t)). Qed.
Lemma lem4296208 {A B : Type'} (s : A -> Prop) (m : nat) : (term654 A B s m) = (term648 A B s m).
Proof. exact (fun_ext (fun t : type1413 A B => @lem4296207 A B s t m)). Qed.
Lemma lem4296209 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem4296210 {A B : Type'} (s : A -> Prop) (m : nat) : (term655 A B s m) = (term656 A B s m).
Proof. exact (MK_COMB (@lem4296209 A B) (@lem4296208 A B s m)). Qed.
Lemma lem4296211 {A : Type'} (s : A -> Prop) : (term619 A s) = (term619 A s).
Proof. exact (eq_refl (term619 A s)). Qed.
Lemma lem4296212 {A B : Type'} (s : A -> Prop) (m : nat) : (term647 A B s m) = (term657 A B s m).
Proof. exact (MK_COMB (@lem4296211 A s) (@lem4296210 A B s m)). Qed.
Lemma lem4296213 {A B : Type'} (s : A -> Prop) (m : nat) : ((term646 A B s m) = (term647 A B s m)) = ((term643 A B s m) = (term657 A B s m)).
Proof. exact (MK_COMB (@lem4296206 A B s m) (@lem4296212 A B s m)). Qed.
Lemma lem4296214 {A B : Type'} (s : A -> Prop) (m : nat) : (term643 A B s m) = (term657 A B s m).
Proof. exact (EQ_MP (@lem4296213 A B s m) (@lem4296198 A B s m)). Qed.
Lemma lem4296218 {A : Type'} (P : Prop) (Q : A -> Prop) : (term573 A P Q) = (term574 A P Q).
Proof. exact (EQ_MP (@lem4295951 A P Q) (@lem4295950 A P Q)). Qed.
Lemma lem4296219 {A B : Type'} (P : Prop) (Q : type475 A B) : (term644 A B P Q) = (term645 A B P Q).
Proof. exact (@lem4296218 (type1413 A B) P Q). Qed.
Lemma lem4296220 {A B : Type'} (s : A -> Prop) (m : nat) : (term658 A B s m) = (term659 A B s m).
Proof. exact (@lem4296219 A B ((@CARD A s) = m) (term660 A B s m)). Qed.
Lemma lem4296221 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : (term661 A B s m t) = (term639 A B s t m).
Proof. exact (eq_refl (term661 A B s m t)). Qed.
Lemma lem4296222 {A : Type'} (s : A -> Prop) (m : nat) : (term632 A s m) = (term632 A s m).
Proof. exact (eq_refl (term632 A s m)). Qed.
Lemma lem4296223 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : (term662 A B s m t) = (term640 A B s t m).
Proof. exact (MK_COMB (@lem4296222 A s m) (@lem4296221 A B s t m)). Qed.
Lemma lem4296224 {A B : Type'} (s : A -> Prop) (m : nat) : (term663 A B s m) = (term648 A B s m).
Proof. exact (fun_ext (fun t : type1413 A B => @lem4296223 A B s t m)). Qed.
Lemma lem4296225 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem4296226 {A B : Type'} (s : A -> Prop) (m : nat) : (term658 A B s m) = (term656 A B s m).
Proof. exact (MK_COMB (@lem4296225 A B) (@lem4296224 A B s m)). Qed.
Lemma lem4296227 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4296228 {A B : Type'} (s : A -> Prop) (m : nat) : (term664 A B s m) = (term665 A B s m).
Proof. exact (MK_COMB (@lem4296227) (@lem4296226 A B s m)). Qed.
Lemma lem4296229 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (m : nat) : (term661 A B s m t) = (term639 A B s t m).
Proof. exact (eq_refl (term661 A B s m t)). Qed.
Lemma lem4296230 {A B : Type'} (s : A -> Prop) (m : nat) : (term666 A B s m) = (term660 A B s m).
Proof. exact (fun_ext (fun t : type1413 A B => @lem4296229 A B s t m)). Qed.
Lemma lem4296231 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem4296232 {A B : Type'} (s : A -> Prop) (m : nat) : (term667 A B s m) = (term668 A B s m).
Proof. exact (MK_COMB (@lem4296231 A B) (@lem4296230 A B s m)). Qed.
Lemma lem4296233 {A : Type'} (s : A -> Prop) (m : nat) : (term632 A s m) = (term632 A s m).
Proof. exact (eq_refl (term632 A s m)). Qed.
Lemma lem4296234 {A B : Type'} (s : A -> Prop) (m : nat) : (term659 A B s m) = (term669 A B s m).
Proof. exact (MK_COMB (@lem4296233 A s m) (@lem4296232 A B s m)). Qed.
Lemma lem4296235 {A B : Type'} (s : A -> Prop) (m : nat) : ((term658 A B s m) = (term659 A B s m)) = ((term656 A B s m) = (term669 A B s m)).
Proof. exact (MK_COMB (@lem4296228 A B s m) (@lem4296234 A B s m)). Qed.
Lemma lem4296236 {A B : Type'} (s : A -> Prop) (m : nat) : (term656 A B s m) = (term669 A B s m).
Proof. exact (EQ_MP (@lem4296235 A B s m) (@lem4296220 A B s m)). Qed.
Lemma lem4296309 {A : Type'} (s : A -> Prop) : (term619 A s) = (term619 A s).
Proof. exact (eq_refl (term619 A s)). Qed.
Lemma lem4296310 {A B : Type'} (s : A -> Prop) (m : nat) : (term657 A B s m) = (term670 A B s m).
Proof. exact (MK_COMB (@lem4296309 A s) (@lem4296236 A B s m)). Qed.
Lemma lem4296313 {A B : Type'} (s : A -> Prop) (m : nat) : (term643 A B s m) = (term670 A B s m).
Proof. exact (TRANS (@lem4296214 A B s m) (@lem4296310 A B s m)). Qed.
Lemma lem4296314 {A B : Type'} (s : A -> Prop) (m : nat) : (term596 A B s m) = (term670 A B s m).
Proof. exact (TRANS (@lem4296194 A B s m) (@lem4296313 A B s m)). Qed.
Lemma lem4296315 {A B : Type'} (s : A -> Prop) : (term598 A B s) = (term671 A B s).
Proof. exact (fun_ext (fun m : nat => @lem4296314 A B s m)). Qed.
Lemma lem4296316 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4296317 {A B : Type'} (s : A -> Prop) : (term600 A B s) = (term672 A B s).
Proof. exact (MK_COMB (@lem4296316) (@lem4296315 A B s)). Qed.
Lemma lem4296319 {A : Type'} (P : Prop) (Q : A -> Prop) : (term573 A P Q) = (term574 A P Q).
Proof. exact (EQ_MP (@lem4295951 A P Q) (@lem4295950 A P Q)). Qed.
Lemma lem4296320 (P : Prop) (Q : nat -> Prop) : (term612 P Q) = (term613 P Q).
Proof. exact (@lem4296319 nat P Q). Qed.
Lemma lem4296321 {A B : Type'} (s : A -> Prop) : (term673 A B s) = (term674 A B s).
Proof. exact (@lem4296320 (@FINITE A s) (term675 A B s)). Qed.
Lemma lem4296322 {A B : Type'} (s : A -> Prop) (m : nat) : (term676 A B s m) = (term669 A B s m).
Proof. exact (eq_refl (term676 A B s m)). Qed.
Lemma lem4296323 {A : Type'} (s : A -> Prop) : (term619 A s) = (term619 A s).
Proof. exact (eq_refl (term619 A s)). Qed.
Lemma lem4296324 {A B : Type'} (s : A -> Prop) (m : nat) : (term677 A B s m) = (term670 A B s m).
Proof. exact (MK_COMB (@lem4296323 A s) (@lem4296322 A B s m)). Qed.
Lemma lem4296325 {A B : Type'} (s : A -> Prop) : (term678 A B s) = (term671 A B s).
Proof. exact (fun_ext (fun m : nat => @lem4296324 A B s m)). Qed.
Lemma lem4296326 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4296327 {A B : Type'} (s : A -> Prop) : (term673 A B s) = (term672 A B s).
Proof. exact (MK_COMB (@lem4296326) (@lem4296325 A B s)). Qed.
Lemma lem4296328 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4296329 {A B : Type'} (s : A -> Prop) : (term679 A B s) = (term680 A B s).
Proof. exact (MK_COMB (@lem4296328) (@lem4296327 A B s)). Qed.
Lemma lem4296330 {A B : Type'} (s : A -> Prop) (m : nat) : (term676 A B s m) = (term669 A B s m).
Proof. exact (eq_refl (term676 A B s m)). Qed.
Lemma lem4296331 {A B : Type'} (s : A -> Prop) : (term681 A B s) = (term675 A B s).
Proof. exact (fun_ext (fun m : nat => @lem4296330 A B s m)). Qed.
Lemma lem4296332 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4296333 {A B : Type'} (s : A -> Prop) : (term682 A B s) = (term683 A B s).
Proof. exact (MK_COMB (@lem4296332) (@lem4296331 A B s)). Qed.
Lemma lem4296334 {A : Type'} (s : A -> Prop) : (term619 A s) = (term619 A s).
Proof. exact (eq_refl (term619 A s)). Qed.
Lemma lem4296335 {A B : Type'} (s : A -> Prop) : (term674 A B s) = (term684 A B s).
Proof. exact (MK_COMB (@lem4296334 A s) (@lem4296333 A B s)). Qed.
Lemma lem4296336 {A B : Type'} (s : A -> Prop) : ((term673 A B s) = (term674 A B s)) = ((term672 A B s) = (term684 A B s)).
Proof. exact (MK_COMB (@lem4296329 A B s) (@lem4296335 A B s)). Qed.
Lemma lem4296337 {A B : Type'} (s : A -> Prop) : (term672 A B s) = (term684 A B s).
Proof. exact (EQ_MP (@lem4296336 A B s) (@lem4296321 A B s)). Qed.
Lemma lem4296436 {A B : Type'} (s : A -> Prop) : (term600 A B s) = (term684 A B s).
Proof. exact (TRANS (@lem4296317 A B s) (@lem4296337 A B s)). Qed.
Lemma lem4296437 {A B : Type'} : (term602 A B) = (term685 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4296436 A B s)). Qed.
Lemma lem4296438 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4296439 {A B : Type'} : (term604 A B) = (term686 A B).
Proof. exact (MK_COMB (@lem4296438 A) (@lem4296437 A B)). Qed.
Lemma lem4296464 {A B : Type'} : (term686 A B) = (term604 A B).
Proof. exact (SYM (@lem4296439 A B)). Qed.
Lemma lem4296466 {A : Type'} (P : type686 A) : term565 A P.
Proof. exact (EQ_MP (@lem4295945 A P) (@lem4295944 A P)). Qed.
Lemma lem4296467 {A : Type'} (P : type686 A) : term565 A P.
Proof. exact (@lem4296466 A P). Qed.
Lemma lem4296468 {A B : Type'} : term687 A B.
Proof. exact (@lem4296467 A (term688 A B)). Qed.
Lemma lem4296469 {A B : Type'} : (term689 A B) = (term690 A B).
Proof. exact (eq_refl (term689 A B)). Qed.
Lemma lem4296470 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4296471 {A B : Type'} : (term691 A B) = (term692 A B).
Proof. exact (MK_COMB (@lem4296470) (@lem4296469 A B)). Qed.
Lemma lem4296472 {A B : Type'} (s : A -> Prop) : (term693 A B s) = (term683 A B s).
Proof. exact (eq_refl (term693 A B s)). Qed.
Lemma lem4296473 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4296474 {A B : Type'} (s : A -> Prop) : (term694 A B s) = (term695 A B s).
Proof. exact (MK_COMB (@lem4296473) (@lem4296472 A B s)). Qed.
Lemma lem4296475 {A : Type'} (x : A) (s : A -> Prop) : (term696 A x s) = (term696 A x s).
Proof. exact (eq_refl (term696 A x s)). Qed.
Lemma lem4296476 {A B : Type'} (x : A) (s : A -> Prop) : (term697 A B x s) = (term698 A B x s).
Proof. exact (MK_COMB (@lem4296474 A B s) (@lem4296475 A x s)). Qed.
Lemma lem4296477 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4296478 {A B : Type'} (x : A) (s : A -> Prop) : (term699 A B x s) = (term700 A B x s).
Proof. exact (MK_COMB (@lem4296477) (@lem4296476 A B x s)). Qed.
Lemma lem4296479 {A B : Type'} (x : A) (s : A -> Prop) : (term701 A B x s) = (term702 A B x s).
Proof. exact (eq_refl (term701 A B x s)). Qed.
Lemma lem4296480 {A B : Type'} (x : A) (s : A -> Prop) : (term703 A B x s) = (term704 A B x s).
Proof. exact (MK_COMB (@lem4296478 A B x s) (@lem4296479 A B x s)). Qed.
Lemma lem4296481 {A B : Type'} (x : A) : (term705 A B x) = (term706 A B x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4296480 A B x s)). Qed.
Lemma lem4296482 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4296483 {A B : Type'} (x : A) : (term707 A B x) = (term708 A B x).
Proof. exact (MK_COMB (@lem4296482 A) (@lem4296481 A B x)). Qed.
Lemma lem4296484 {A B : Type'} : (term709 A B) = (term710 A B).
Proof. exact (fun_ext (fun x : A => @lem4296483 A B x)). Qed.
Lemma lem4296485 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4296486 {A B : Type'} : (term711 A B) = (term712 A B).
Proof. exact (MK_COMB (@lem4296485 A) (@lem4296484 A B)). Qed.
Lemma lem4296487 {A B : Type'} : (term713 A B) = (term714 A B).
Proof. exact (MK_COMB (@lem4296471 A B) (@lem4296486 A B)). Qed.
Lemma lem4296488 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4296489 {A B : Type'} : (term715 A B) = (term716 A B).
Proof. exact (MK_COMB (@lem4296488) (@lem4296487 A B)). Qed.
Lemma lem4296490 {A B : Type'} (s : A -> Prop) : (term693 A B s) = (term683 A B s).
Proof. exact (eq_refl (term693 A B s)). Qed.
Lemma lem4296491 {A : Type'} (s : A -> Prop) : (term619 A s) = (term619 A s).
Proof. exact (eq_refl (term619 A s)). Qed.
Lemma lem4296492 {A B : Type'} (s : A -> Prop) : (term717 A B s) = (term684 A B s).
Proof. exact (MK_COMB (@lem4296491 A s) (@lem4296490 A B s)). Qed.
Lemma lem4296493 {A B : Type'} : (term718 A B) = (term685 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4296492 A B s)). Qed.
Lemma lem4296494 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4296495 {A B : Type'} : (term719 A B) = (term686 A B).
Proof. exact (MK_COMB (@lem4296494 A) (@lem4296493 A B)). Qed.
Lemma lem4296496 {A B : Type'} : (term687 A B) = (term720 A B).
Proof. exact (MK_COMB (@lem4296489 A B) (@lem4296495 A B)). Qed.
Lemma lem4296497 {A B : Type'} : term720 A B.
Proof. exact (EQ_MP (@lem4296496 A B) (@lem4296468 A B)). Qed.
Lemma lem4296509 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term721 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4296510 (p : Prop) (q : Prop) (p' : Prop) : term722 p q p'.
Proof. exact (fun q' : Prop => @lem4296509 p q p' q'). Qed.
Lemma lem4296511 (p : Prop) (q : Prop) : term723 p q.
Proof. exact (fun p' : Prop => @lem4296510 p q p'). Qed.
Lemma lem4296512 {A B : Type'} (m : nat) : term724 A B m.
Proof. exact (@lem4296511 ((@CARD A (@EMPTY A)) = m) (term725 A B m)). Qed.
Lemma lem4296513 {A B : Type'} (m : nat) (p' : Prop) : term726 A B m p'.
Proof. exact (@lem4296512 A B m p'). Qed.
Lemma lem4296514 {A B : Type'} (m : nat) (p' : Prop) : (term726 A B m p') = (term727 A B m p').
Proof. exact (eq_refl (term726 A B m p')). Qed.
Lemma lem4296515 {A B : Type'} (m : nat) (p' : Prop) : term727 A B m p'.
Proof. exact (EQ_MP (@lem4296514 A B m p') (@lem4296513 A B m p')). Qed.
Lemma lem4296516 {A B : Type'} (m : nat) (p' : Prop) (q' : Prop) : term728 A B m p' q'.
Proof. exact (@lem4296515 A B m p' q'). Qed.
Lemma lem4296517 {A B : Type'} (m : nat) (p' : Prop) (q' : Prop) : (term728 A B m p' q') = (term729 A B m p' q').
Proof. exact (eq_refl (term728 A B m p' q')). Qed.
Lemma lem4296518 {A B : Type'} (m : nat) (p' : Prop) (q' : Prop) : term729 A B m p' q'.
Proof. exact (EQ_MP (@lem4296517 A B m p' q') (@lem4296516 A B m p' q')). Qed.
Lemma lem4296522 {A : Type'} : (@CARD A (@EMPTY A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem3840691 A)). Qed.
Lemma lem4296523 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem4296524 {A : Type'} : (term730 A) = term731.
Proof. exact (MK_COMB (@lem4296523) (@lem4296522 A)). Qed.
Lemma lem4296525 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem4296526 {A : Type'} (m : nat) : ((@CARD A (@EMPTY A)) = m) = ((NUMERAL 0) = m).
Proof. exact (MK_COMB (@lem4296524 A) (@lem4296525 m)). Qed.
Lemma lem4296529 {A B : Type'} (m : nat) (q' : Prop) : term732 A B m q'.
Proof. exact (@lem4296518 A B m ((NUMERAL 0) = m) q'). Qed.
Lemma lem4296530 {A B : Type'} (m : nat) (q' : Prop) : term733 A B m q'.
Proof. exact (@lem4296529 A B m q' (@lem4296526 A m)). Qed.
Lemma lem4296543 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term721 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4296544 (p : Prop) (q : Prop) (p' : Prop) : term722 p q p'.
Proof. exact (fun q' : Prop => @lem4296543 p q p' q'). Qed.
Lemma lem4296545 (p : Prop) (q : Prop) : term723 p q.
Proof. exact (fun p' : Prop => @lem4296544 p q p'). Qed.
Lemma lem4296546 {A B : Type'} (t : type1413 A B) (m : nat) (n : nat) : term734 A B t m n.
Proof. exact (@lem4296545 (term735 A B t n) (term736 A B t m n)). Qed.
Lemma lem4296547 {A B : Type'} (t : type1413 A B) (m : nat) (n : nat) (p' : Prop) : term737 A B t m n p'.
Proof. exact (@lem4296546 A B t m n p'). Qed.
Lemma lem4296548 {A B : Type'} (t : type1413 A B) (m : nat) (n : nat) (p' : Prop) : (term737 A B t m n p') = (term738 A B t m n p').
Proof. exact (eq_refl (term737 A B t m n p')). Qed.
Lemma lem4296549 {A B : Type'} (t : type1413 A B) (m : nat) (n : nat) (p' : Prop) : term738 A B t m n p'.
Proof. exact (EQ_MP (@lem4296548 A B t m n p') (@lem4296547 A B t m n p')). Qed.
Lemma lem4296550 {A B : Type'} (t : type1413 A B) (m : nat) (n : nat) (p' : Prop) (q' : Prop) : term739 A B t m n p' q'.
Proof. exact (@lem4296549 A B t m n p' q'). Qed.
Lemma lem4296551 {A B : Type'} (t : type1413 A B) (m : nat) (n : nat) (p' : Prop) (q' : Prop) : (term739 A B t m n p' q') = (term740 A B t m n p' q').
Proof. exact (eq_refl (term739 A B t m n p' q')). Qed.
Lemma lem4296552 {A B : Type'} (t : type1413 A B) (m : nat) (n : nat) (p' : Prop) (q' : Prop) : term740 A B t m n p' q'.
Proof. exact (EQ_MP (@lem4296551 A B t m n p' q') (@lem4296550 A B t m n p' q')). Qed.
Lemma lem4296560 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term721 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4296561 (p : Prop) (q : Prop) (p' : Prop) : term722 p q p'.
Proof. exact (fun q' : Prop => @lem4296560 p q p' q'). Qed.
Lemma lem4296562 (p : Prop) (q : Prop) : term723 p q.
Proof. exact (fun p' : Prop => @lem4296561 p q p'). Qed.
Lemma lem4296563 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) : term741 A B t x n.
Proof. exact (@lem4296562 (@IN A x (@EMPTY A)) (term742 A B t x n)). Qed.
Lemma lem4296564 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) (p' : Prop) : term743 A B t x n p'.
Proof. exact (@lem4296563 A B t x n p'). Qed.
Lemma lem4296565 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) (p' : Prop) : (term743 A B t x n p') = (term744 A B t x n p').
Proof. exact (eq_refl (term743 A B t x n p')). Qed.
Lemma lem4296566 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) (p' : Prop) : term744 A B t x n p'.
Proof. exact (EQ_MP (@lem4296565 A B t x n p') (@lem4296564 A B t x n p')). Qed.
Lemma lem4296567 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) (p' : Prop) (q' : Prop) : term745 A B t x n p' q'.
Proof. exact (@lem4296566 A B t x n p' q'). Qed.
Lemma lem4296568 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) (p' : Prop) (q' : Prop) : (term745 A B t x n p' q') = (term746 A B t x n p' q').
Proof. exact (eq_refl (term745 A B t x n p' q')). Qed.
Lemma lem4296569 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) (p' : Prop) (q' : Prop) : term746 A B t x n p' q'.
Proof. exact (EQ_MP (@lem4296568 A B t x n p' q') (@lem4296567 A B t x n p' q')). Qed.
Lemma lem4296571 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4295914 A x (@lem4295913 A x)). Qed.
Lemma lem4296572 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4296571 A x). Qed.
Lemma lem4296573 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) (q' : Prop) : term747 A B t x n q'.
Proof. exact (@lem4296569 A B t x n False q'). Qed.
Lemma lem4296574 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) (q' : Prop) : term748 A B t x n q'.
Proof. exact (@lem4296573 A B t x n q' (@lem4296572 A x)). Qed.
Lemma lem4296578 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) : (term742 A B t x n) = (term742 A B t x n).
Proof. exact (eq_refl (term742 A B t x n)). Qed.
Lemma lem4296579 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) : term749 A B t x n.
Proof. exact (fun h0 : False => @lem4296578 A B t x n). Qed.
Lemma lem4296580 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) : term750 A B t x n.
Proof. exact (@lem4296574 A B t x n (term742 A B t x n)). Qed.
Lemma lem4296581 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) : (term751 A B t x n) = (term752 A B t x n).
Proof. exact (@lem4296580 A B t x n (@lem4296579 A B t x n)). Qed.
Lemma lem4296583 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem4296584 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) : (term752 A B t x n) = True.
Proof. exact (@lem4296583 (term742 A B t x n)). Qed.
Lemma lem4296585 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) : (term751 A B t x n) = True.
Proof. exact (TRANS (@lem4296581 A B t x n) (@lem4296584 A B t x n)). Qed.
Lemma lem4296586 {A B : Type'} (t : type1413 A B) (n : nat) : (term753 A B t n) = (term754 A).
Proof. exact (fun_ext (fun x : A => @lem4296585 A B t x n)). Qed.
Lemma lem4296587 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4296588 {A B : Type'} (t : type1413 A B) (n : nat) : (term735 A B t n) = (term755 A).
Proof. exact (MK_COMB (@lem4296587 A) (@lem4296586 A B t n)). Qed.
Lemma lem4296590 {A : Type'} (t : Prop) : (term756 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4296591 {A : Type'} (t : Prop) : (term756 A t) = t.
Proof. exact (@lem4296590 A t). Qed.
Lemma lem4296592 {A : Type'} : (term755 A) = True.
Proof. exact (@lem4296591 A True). Qed.
Lemma lem4296593 {A B : Type'} (t : type1413 A B) (n : nat) : (term735 A B t n) = True.
Proof. exact (TRANS (@lem4296588 A B t n) (@lem4296592 A)). Qed.
Lemma lem4296594 {A B : Type'} (t : type1413 A B) (m : nat) (n : nat) (q' : Prop) : term757 A B t m n q'.
Proof. exact (@lem4296552 A B t m n True q'). Qed.
Lemma lem4296595 {A B : Type'} (t : type1413 A B) (m : nat) (n : nat) (q' : Prop) : term758 A B t m n q'.
Proof. exact (@lem4296594 A B t m n q' (@lem4296593 A B t n)). Qed.
Lemma lem4296612 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4295914 A x (@lem4295913 A x)). Qed.
Lemma lem4296613 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4296612 A x). Qed.
Lemma lem4296614 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4296615 {A : Type'} (x : A) : (term759 A x) = (and False).
Proof. exact (MK_COMB (@lem4296614) (@lem4296613 A x)). Qed.
Lemma lem4296616 {A B : Type'} (y : B) (t : type1413 A B) (x : A) : (term760 A B y t x) = (term760 A B y t x).
Proof. exact (eq_refl (term760 A B y t x)). Qed.
Lemma lem4296617 {A B : Type'} (y : B) (t : type1413 A B) (x : A) : (term761 A B y t x) = (term762 A B y t x).
Proof. exact (MK_COMB (@lem4296615 A x) (@lem4296616 A B y t x)). Qed.
Lemma lem4296619 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem4296620 {A B : Type'} (y : B) (t : type1413 A B) (x : A) : (term762 A B y t x) = False.
Proof. exact (@lem4296619 (term760 A B y t x)). Qed.
Lemma lem4296621 {A B : Type'} (y : B) (t : type1413 A B) (x : A) : (term761 A B y t x) = False.
Proof. exact (TRANS (@lem4296617 A B y t x) (@lem4296620 A B y t x)). Qed.
Lemma lem4296622 {A B : Type'} (GEN_PVAR_121 : prod A B) : (@SETSPEC (prod A B) GEN_PVAR_121) = (@SETSPEC (prod A B) GEN_PVAR_121).
Proof. exact (eq_refl (@SETSPEC (prod A B) GEN_PVAR_121)). Qed.
Lemma lem4296623 {A B : Type'} (y : B) (t : type1413 A B) (x : A) (GEN_PVAR_121 : prod A B) : (term763 A B GEN_PVAR_121 y t x) = (@SETSPEC (prod A B) GEN_PVAR_121 False).
Proof. exact (MK_COMB (@lem4296622 A B GEN_PVAR_121) (@lem4296621 A B y t x)). Qed.
Lemma lem4296624 {A B : Type'} (x : A) (y : B) : (@pair A B x y) = (@pair A B x y).
Proof. exact (eq_refl (@pair A B x y)). Qed.
Lemma lem4296625 {A B : Type'} (t : type1413 A B) (GEN_PVAR_121 : prod A B) (x : A) (y : B) : (term764 A B GEN_PVAR_121 t x y) = (term765 A B GEN_PVAR_121 x y).
Proof. exact (MK_COMB (@lem4296623 A B y t x GEN_PVAR_121) (@lem4296624 A B x y)). Qed.
Lemma lem4296626 {A B : Type'} (t : type1413 A B) (GEN_PVAR_121 : prod A B) (x : A) : (term766 A B GEN_PVAR_121 t x) = (term767 A B GEN_PVAR_121 x).
Proof. exact (fun_ext (fun y : B => @lem4296625 A B t GEN_PVAR_121 x y)). Qed.
Lemma lem4296627 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4296628 {A B : Type'} (t : type1413 A B) (GEN_PVAR_121 : prod A B) (x : A) : (term768 A B GEN_PVAR_121 t x) = (term769 A B GEN_PVAR_121 x).
Proof. exact (MK_COMB (@lem4296627 B) (@lem4296626 A B t GEN_PVAR_121 x)). Qed.
Lemma lem4296633 {A B : Type'} (t : type1413 A B) (GEN_PVAR_121 : prod A B) : (term770 A B GEN_PVAR_121 t) = (term771 A B GEN_PVAR_121).
Proof. exact (fun_ext (fun x : A => @lem4296628 A B t GEN_PVAR_121 x)). Qed.
Lemma lem4296638 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4296639 {A B : Type'} (t : type1413 A B) (GEN_PVAR_121 : prod A B) : (term772 A B GEN_PVAR_121 t) = (term773 A B GEN_PVAR_121).
Proof. exact (MK_COMB (@lem4296638 A) (@lem4296633 A B t GEN_PVAR_121)). Qed.
Lemma lem4296648 {A B : Type'} (t : type1413 A B) : (term774 A B t) = (term775 A B).
Proof. exact (fun_ext (fun GEN_PVAR_121 : prod A B => @lem4296639 A B t GEN_PVAR_121)). Qed.
Lemma lem4296657 {A B : Type'} : (@GSPEC (prod A B)) = (@GSPEC (prod A B)).
Proof. exact (eq_refl (@GSPEC (prod A B))). Qed.
Lemma lem4296658 {A B : Type'} (t : type1413 A B) : (term776 A B t) = (term777 A B).
Proof. exact (MK_COMB (@lem4296657 A B) (@lem4296648 A B t)). Qed.
Lemma lem4296667 {A B : Type'} : (@HAS_SIZE (prod A B)) = (@HAS_SIZE (prod A B)).
Proof. exact (eq_refl (@HAS_SIZE (prod A B))). Qed.
Lemma lem4296668 {A B : Type'} (t : type1413 A B) : (term778 A B t) = (term779 A B).
Proof. exact (MK_COMB (@lem4296667 A B) (@lem4296658 A B t)). Qed.
Lemma lem4296677 (m : nat) (n : nat) : (Nat.mul m n) = (Nat.mul m n).
Proof. exact (eq_refl (Nat.mul m n)). Qed.
Lemma lem4296678 {A B : Type'} (t : type1413 A B) (m : nat) (n : nat) : (term736 A B t m n) = (term780 A B m n).
Proof. exact (MK_COMB (@lem4296668 A B t) (@lem4296677 m n)). Qed.
Lemma lem4296687 {A B : Type'} (t : type1413 A B) (m : nat) (n : nat) : term781 A B t m n.
Proof. exact (fun h0 : True => @lem4296678 A B t m n). Qed.
Lemma lem4296688 {A B : Type'} (t : type1413 A B) (m : nat) (n : nat) : term782 A B t m n.
Proof. exact (@lem4296595 A B t m n (term780 A B m n)). Qed.
Lemma lem4296689 {A B : Type'} (t : type1413 A B) (m : nat) (n : nat) : (term783 A B t m n) = (term784 A B m n).
Proof. exact (@lem4296688 A B t m n (@lem4296687 A B t m n)). Qed.
Lemma lem4296691 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem4296692 {A B : Type'} (m : nat) (n : nat) : (term784 A B m n) = (term780 A B m n).
Proof. exact (@lem4296691 (term780 A B m n)). Qed.
Lemma lem4296701 {A B : Type'} (t : type1413 A B) (m : nat) (n : nat) : (term783 A B t m n) = (term780 A B m n).
Proof. exact (TRANS (@lem4296689 A B t m n) (@lem4296692 A B m n)). Qed.
Lemma lem4296702 {A B : Type'} (t : type1413 A B) (m : nat) : (term785 A B t m) = (term786 A B m).
Proof. exact (fun_ext (fun n : nat => @lem4296701 A B t m n)). Qed.
Lemma lem4296711 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4296712 {A B : Type'} (t : type1413 A B) (m : nat) : (term787 A B t m) = (term788 A B m).
Proof. exact (MK_COMB (@lem4296711) (@lem4296702 A B t m)). Qed.
Lemma lem4296725 {A B : Type'} (m : nat) : (term789 A B m) = (term790 A B m).
Proof. exact (fun_ext (fun t : type1413 A B => @lem4296712 A B t m)). Qed.
Lemma lem4296738 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem4296739 {A B : Type'} (m : nat) : (term725 A B m) = (term791 A B m).
Proof. exact (MK_COMB (@lem4296738 A B) (@lem4296725 A B m)). Qed.
Lemma lem4296741 {A : Type'} (t : Prop) : (term756 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4296742 {A B : Type'} (t : Prop) : (term792 A B t) = t.
Proof. exact (@lem4296741 (type1413 A B) t). Qed.
Lemma lem4296743 {A B : Type'} (m : nat) : (term791 A B m) = (term788 A B m).
Proof. exact (@lem4296742 A B (term788 A B m)). Qed.
Lemma lem4296756 {A B : Type'} (m : nat) : (term725 A B m) = (term788 A B m).
Proof. exact (TRANS (@lem4296739 A B m) (@lem4296743 A B m)). Qed.
Lemma lem4296757 {A B : Type'} (m : nat) : term793 A B m.
Proof. exact (fun h0 : (NUMERAL 0) = m => @lem4296756 A B m). Qed.
Lemma lem4296758 {A B : Type'} (m : nat) : term794 A B m.
Proof. exact (@lem4296530 A B m (term788 A B m)). Qed.
Lemma lem4296759 {A B : Type'} (m : nat) : (term795 A B m) = (term796 A B m).
Proof. exact (@lem4296758 A B m (@lem4296757 A B m)). Qed.
Lemma lem4296811 {A B : Type'} : (term797 A B) = (term798 A B).
Proof. exact (fun_ext (fun m : nat => @lem4296759 A B m)). Qed.
Lemma lem4296863 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4296864 {A B : Type'} : (term690 A B) = (term799 A B).
Proof. exact (MK_COMB (@lem4296863) (@lem4296811 A B)). Qed.
Lemma lem4296920 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4296921 {A B : Type'} : (term692 A B) = (term800 A B).
Proof. exact (MK_COMB (@lem4296920) (@lem4296864 A B)). Qed.
Lemma lem4296988 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term721 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4296989 (p : Prop) (q : Prop) (p' : Prop) : term722 p q p'.
Proof. exact (fun q' : Prop => @lem4296988 p q p' q'). Qed.
Lemma lem4296990 (p : Prop) (q : Prop) : term723 p q.
Proof. exact (fun p' : Prop => @lem4296989 p q p'). Qed.
Lemma lem4296991 {A B : Type'} (x : A) (s : A -> Prop) : term801 A B x s.
Proof. exact (@lem4296990 (term698 A B x s) (term702 A B x s)). Qed.
Lemma lem4296992 {A B : Type'} (x : A) (s : A -> Prop) (p' : Prop) : term802 A B x s p'.
Proof. exact (@lem4296991 A B x s p'). Qed.
Lemma lem4296993 {A B : Type'} (x : A) (s : A -> Prop) (p' : Prop) : (term802 A B x s p') = (term803 A B x s p').
Proof. exact (eq_refl (term802 A B x s p')). Qed.
Lemma lem4296994 {A B : Type'} (x : A) (s : A -> Prop) (p' : Prop) : term803 A B x s p'.
Proof. exact (EQ_MP (@lem4296993 A B x s p') (@lem4296992 A B x s p')). Qed.
Lemma lem4296995 {A B : Type'} (x : A) (s : A -> Prop) (p' : Prop) (q' : Prop) : term804 A B x s p' q'.
Proof. exact (@lem4296994 A B x s p' q'). Qed.
Lemma lem4296996 {A B : Type'} (x : A) (s : A -> Prop) (p' : Prop) (q' : Prop) : (term804 A B x s p' q') = (term805 A B x s p' q').
Proof. exact (eq_refl (term804 A B x s p' q')). Qed.
Lemma lem4296997 {A B : Type'} (x : A) (s : A -> Prop) (p' : Prop) (q' : Prop) : term805 A B x s p' q'.
Proof. exact (EQ_MP (@lem4296996 A B x s p' q') (@lem4296995 A B x s p' q')). Qed.
Lemma lem4297263 {A B : Type'} (x : A) (s : A -> Prop) : (term698 A B x s) = (term698 A B x s).
Proof. exact (eq_refl (term698 A B x s)). Qed.
Lemma lem4297264 {A B : Type'} (x : A) (s : A -> Prop) (q' : Prop) : term806 A B x s q'.
Proof. exact (@lem4296997 A B x s (term698 A B x s) q'). Qed.
Lemma lem4297265 {A B : Type'} (x : A) (s : A -> Prop) (q' : Prop) : term807 A B x s q'.
Proof. exact (@lem4297264 A B x s q' (@lem4297263 A B x s)). Qed.
Lemma lem4297266 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term698 A B x s) : term698 A B x s.
Proof. exact (h1). Qed.
Lemma lem4297267 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term698 A B x s) : term696 A x s.
Proof. exact (proj2 (@lem4297266 A B x s h1)). Qed.
Lemma lem4297268 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term698 A B x s) : @FINITE A s.
Proof. exact (proj2 (@lem4297267 A B x s h1)). Qed.
Lemma lem4297269 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem4297271 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term698 A B x s) : term808 A x s.
Proof. exact (proj1 (@lem4297267 A B x s h1)). Qed.
Lemma lem4297272 {A : Type'} (x : A) (s : A -> Prop) : term809 A x s.
Proof. exact (@lem82 (@IN A x s)). Qed.
Lemma lem4297309 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term721 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4297310 (p : Prop) (q : Prop) (p' : Prop) : term722 p q p'.
Proof. exact (fun q' : Prop => @lem4297309 p q p' q'). Qed.
Lemma lem4297311 (p : Prop) (q : Prop) : term723 p q.
Proof. exact (fun p' : Prop => @lem4297310 p q p'). Qed.
Lemma lem4297312 {A B : Type'} (x : A) (s : A -> Prop) (m : nat) : term810 A B x s m.
Proof. exact (@lem4297311 ((term561 A x s) = m) (term811 A B x s m)). Qed.
Lemma lem4297313 {A B : Type'} (x : A) (s : A -> Prop) (m : nat) (p' : Prop) : term812 A B x s m p'.
Proof. exact (@lem4297312 A B x s m p'). Qed.
Lemma lem4297314 {A B : Type'} (x : A) (s : A -> Prop) (m : nat) (p' : Prop) : (term812 A B x s m p') = (term813 A B x s m p').
Proof. exact (eq_refl (term812 A B x s m p')). Qed.
Lemma lem4297315 {A B : Type'} (x : A) (s : A -> Prop) (m : nat) (p' : Prop) : term813 A B x s m p'.
Proof. exact (EQ_MP (@lem4297314 A B x s m p') (@lem4297313 A B x s m p')). Qed.
Lemma lem4297316 {A B : Type'} (x : A) (s : A -> Prop) (m : nat) (p' : Prop) (q' : Prop) : term814 A B x s m p' q'.
Proof. exact (@lem4297315 A B x s m p' q'). Qed.
Lemma lem4297317 {A B : Type'} (x : A) (s : A -> Prop) (m : nat) (p' : Prop) (q' : Prop) : (term814 A B x s m p' q') = (term815 A B x s m p' q').
Proof. exact (eq_refl (term814 A B x s m p' q')). Qed.
Lemma lem4297318 {A B : Type'} (x : A) (s : A -> Prop) (m : nat) (p' : Prop) (q' : Prop) : term815 A B x s m p' q'.
Proof. exact (EQ_MP (@lem4297317 A B x s m p' q') (@lem4297316 A B x s m p' q')). Qed.
Lemma lem4297322 {A : Type'} (x : A) (s : A -> Prop) : term560 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem4295924 A x s h0). Qed.
Lemma lem4297323 {A : Type'} (x : A) (s : A -> Prop) : term560 A x s.
Proof. exact (@lem4297322 A x s). Qed.
Lemma lem4297325 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term698 A B x s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem4297269 A s) (@lem4297268 A B x s h1)). Qed.
Lemma lem4297326 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term698 A B x s) : True = (@FINITE A s).
Proof. exact (SYM (@lem4297325 A B x s h1)). Qed.
Lemma lem4297327 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term698 A B x s) : @FINITE A s.
Proof. exact (EQ_MP (@lem4297326 A B x s h1) (@lem0)). Qed.
Lemma lem4297328 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term698 A B x s) : (term561 A x s) = (term562 A x s).
Proof. exact (@lem4297323 A x s (@lem4297327 A B x s h1)). Qed.
Lemma lem4297330 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term816 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem4297331 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term817 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem4297330 _2963 g t e g' t' e'). Qed.
Lemma lem4297332 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term818 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem4297331 _2963 g t e g' t'). Qed.
Lemma lem4297333 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term819 _2963 g t e.
Proof. exact (fun g' : Prop => @lem4297332 _2963 g t e g'). Qed.
Lemma lem4297334 (g : Prop) (t : nat) (e : nat) : term820 g t e.
Proof. exact (@lem4297333 nat g t e). Qed.
Lemma lem4297335 {A : Type'} (x : A) (s : A -> Prop) : term821 A x s.
Proof. exact (@lem4297334 (@IN A x s) (@CARD A s) (term822 A s)). Qed.
Lemma lem4297336 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) : term823 A x s g'.
Proof. exact (@lem4297335 A x s g'). Qed.
Lemma lem4297337 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) : (term823 A x s g') = (term824 A x s g').
Proof. exact (eq_refl (term823 A x s g')). Qed.
Lemma lem4297338 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) : term824 A x s g'.
Proof. exact (EQ_MP (@lem4297337 A x s g') (@lem4297336 A x s g')). Qed.
Lemma lem4297339 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) (t' : nat) : term825 A x s g' t'.
Proof. exact (@lem4297338 A x s g' t'). Qed.
Lemma lem4297340 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) (t' : nat) : (term825 A x s g' t') = (term826 A x s g' t').
Proof. exact (eq_refl (term825 A x s g' t')). Qed.
Lemma lem4297341 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) (t' : nat) : term826 A x s g' t'.
Proof. exact (EQ_MP (@lem4297340 A x s g' t') (@lem4297339 A x s g' t')). Qed.
Lemma lem4297342 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) (t' : nat) (e' : nat) : term827 A x s g' t' e'.
Proof. exact (@lem4297341 A x s g' t' e'). Qed.
Lemma lem4297343 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) (t' : nat) (e' : nat) : (term827 A x s g' t' e') = (term828 A x s g' t' e').
Proof. exact (eq_refl (term827 A x s g' t' e')). Qed.
Lemma lem4297344 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) (t' : nat) (e' : nat) : term828 A x s g' t' e'.
Proof. exact (EQ_MP (@lem4297343 A x s g' t' e') (@lem4297342 A x s g' t' e')). Qed.
Lemma lem4297346 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term698 A B x s) : (@IN A x s) = False.
Proof. exact (@lem4297272 A x s (@lem4297271 A B x s h1)). Qed.
Lemma lem4297347 {A : Type'} (x : A) (s : A -> Prop) (t' : nat) (e' : nat) : term829 A x s t' e'.
Proof. exact (@lem4297344 A x s False t' e'). Qed.
Lemma lem4297348 {A B : Type'} (t' : nat) (e' : nat) (x : A) (s : A -> Prop) (h1 : term698 A B x s) : term830 A x s t' e'.
Proof. exact (@lem4297347 A x s t' e' (@lem4297346 A B x s h1)). Qed.
Lemma lem4297352 {A : Type'} (s : A -> Prop) : (@CARD A s) = (@CARD A s).
Proof. exact (eq_refl (@CARD A s)). Qed.
Lemma lem4297353 {A : Type'} (s : A -> Prop) : term831 A s.
Proof. exact (fun h0 : False => @lem4297352 A s). Qed.
Lemma lem4297354 {A B : Type'} (e' : nat) (x : A) (s : A -> Prop) (h1 : term698 A B x s) : term832 A x s e'.
Proof. exact (@lem4297348 A B (@CARD A s) e' x s h1). Qed.
Lemma lem4297355 {A B : Type'} (e' : nat) (x : A) (s : A -> Prop) (h1 : term698 A B x s) : term833 A x s e'.
Proof. exact (@lem4297354 A B e' x s h1 (@lem4297353 A s)). Qed.
Lemma lem4297361 {A : Type'} (s : A -> Prop) : (term822 A s) = (term822 A s).
Proof. exact (eq_refl (term822 A s)). Qed.
Lemma lem4297362 {A : Type'} (s : A -> Prop) : term834 A s.
Proof. exact (fun h0 : ~ False => @lem4297361 A s). Qed.
Lemma lem4297363 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term698 A B x s) : term835 A x s.
Proof. exact (@lem4297355 A B (term822 A s) x s h1). Qed.
Lemma lem4297364 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term698 A B x s) : (term562 A x s) = (term836 A s).
Proof. exact (@lem4297363 A B x s h1 (@lem4297362 A s)). Qed.
Lemma lem4297366 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem4297367 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem4297366 nat t1 t2). Qed.
Lemma lem4297368 {A : Type'} (s : A -> Prop) : (term836 A s) = (term822 A s).
Proof. exact (@lem4297367 (@CARD A s) (term822 A s)). Qed.
Lemma lem4297369 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term698 A B x s) : (term562 A x s) = (term822 A s).
Proof. exact (TRANS (@lem4297364 A B x s h1) (@lem4297368 A s)). Qed.
Lemma lem4297370 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term698 A B x s) : (term561 A x s) = (term822 A s).
Proof. exact (TRANS (@lem4297328 A B x s h1) (@lem4297369 A B x s h1)). Qed.
Lemma lem4297371 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem4297372 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term698 A B x s) : (term837 A x s) = (term838 A s).
Proof. exact (MK_COMB (@lem4297371) (@lem4297370 A B x s h1)). Qed.
Lemma lem4297373 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem4297374 {A B : Type'} (m : nat) (x : A) (s : A -> Prop) (h1 : term698 A B x s) : ((term561 A x s) = m) = ((term822 A s) = m).
Proof. exact (MK_COMB (@lem4297372 A B x s h1) (@lem4297373 m)). Qed.
Lemma lem4297377 {A B : Type'} (x : A) (s : A -> Prop) (m : nat) (q' : Prop) : term839 A B x s m q'.
Proof. exact (@lem4297318 A B x s m ((term822 A s) = m) q'). Qed.
Lemma lem4297378 {A B : Type'} (m : nat) (q' : Prop) (x : A) (s : A -> Prop) (h1 : term698 A B x s) : term840 A B x s m q'.
Proof. exact (@lem4297377 A B x s m q' (@lem4297374 A B m x s h1)). Qed.
Lemma lem4297391 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term721 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4297392 (p : Prop) (q : Prop) (p' : Prop) : term722 p q p'.
Proof. exact (fun q' : Prop => @lem4297391 p q p' q'). Qed.
Lemma lem4297393 (p : Prop) (q : Prop) : term723 p q.
Proof. exact (fun p' : Prop => @lem4297392 p q p'). Qed.
Lemma lem4297394 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) : term841 A B x s t m n.
Proof. exact (@lem4297393 (term842 A B x s t n) (term843 A B x s t m n)). Qed.
Lemma lem4297395 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) (p' : Prop) : term844 A B x s t m n p'.
Proof. exact (@lem4297394 A B x s t m n p'). Qed.
Lemma lem4297396 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) (p' : Prop) : (term844 A B x s t m n p') = (term845 A B x s t m n p').
Proof. exact (eq_refl (term844 A B x s t m n p')). Qed.
Lemma lem4297397 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) (p' : Prop) : term845 A B x s t m n p'.
Proof. exact (EQ_MP (@lem4297396 A B x s t m n p') (@lem4297395 A B x s t m n p')). Qed.
Lemma lem4297398 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) (p' : Prop) (q' : Prop) : term846 A B x s t m n p' q'.
Proof. exact (@lem4297397 A B x s t m n p' q'). Qed.
Lemma lem4297399 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) (p' : Prop) (q' : Prop) : (term846 A B x s t m n p' q') = (term847 A B x s t m n p' q').
Proof. exact (eq_refl (term846 A B x s t m n p' q')). Qed.
Lemma lem4297400 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) (p' : Prop) (q' : Prop) : term847 A B x s t m n p' q'.
Proof. exact (EQ_MP (@lem4297399 A B x s t m n p' q') (@lem4297398 A B x s t m n p' q')). Qed.
Lemma lem4297408 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term721 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4297409 (p : Prop) (q : Prop) (p' : Prop) : term722 p q p'.
Proof. exact (fun q' : Prop => @lem4297408 p q p' q'). Qed.
Lemma lem4297410 (p : Prop) (q : Prop) : term723 p q.
Proof. exact (fun p' : Prop => @lem4297409 p q p'). Qed.
Lemma lem4297411 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (x' : A) (n : nat) : term848 A B x s t x' n.
Proof. exact (@lem4297410 (term555 A x' x s) (term742 A B t x' n)). Qed.
Lemma lem4297412 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (x' : A) (n : nat) (p' : Prop) : term849 A B x s t x' n p'.
Proof. exact (@lem4297411 A B x s t x' n p'). Qed.
Lemma lem4297413 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (x' : A) (n : nat) (p' : Prop) : (term849 A B x s t x' n p') = (term850 A B x s t x' n p').
Proof. exact (eq_refl (term849 A B x s t x' n p')). Qed.
Lemma lem4297414 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (x' : A) (n : nat) (p' : Prop) : term850 A B x s t x' n p'.
Proof. exact (EQ_MP (@lem4297413 A B x s t x' n p') (@lem4297412 A B x s t x' n p')). Qed.
Lemma lem4297415 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (x' : A) (n : nat) (p' : Prop) (q' : Prop) : term851 A B x s t x' n p' q'.
Proof. exact (@lem4297414 A B x s t x' n p' q'). Qed.
Lemma lem4297416 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (x' : A) (n : nat) (p' : Prop) (q' : Prop) : (term851 A B x s t x' n p' q') = (term852 A B x s t x' n p' q').
Proof. exact (eq_refl (term851 A B x s t x' n p' q')). Qed.
Lemma lem4297417 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (x' : A) (n : nat) (p' : Prop) (q' : Prop) : term852 A B x s t x' n p' q'.
Proof. exact (EQ_MP (@lem4297416 A B x s t x' n p' q') (@lem4297415 A B x s t x' n p' q')). Qed.
Lemma lem4297419 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term555 A x y s) = (term81 A y x s).
Proof. exact (EQ_MP (@lem4295909 A y x s) (@lem4295908 A y x s)). Qed.
Lemma lem4297420 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term555 A x y s) = (term81 A y x s).
Proof. exact (@lem4297419 A y x s). Qed.
Lemma lem4297421 {A : Type'} (x : A) (x' : A) (s : A -> Prop) : (term555 A x' x s) = (term81 A x x' s).
Proof. exact (@lem4297420 A x x' s). Qed.
Lemma lem4297426 {A B : Type'} (t : type1413 A B) (n : nat) (x : A) (x' : A) (s : A -> Prop) (q' : Prop) : term853 A B t n x x' s q'.
Proof. exact (@lem4297417 A B x s t x' n (term81 A x x' s) q'). Qed.
Lemma lem4297427 {A B : Type'} (t : type1413 A B) (n : nat) (x : A) (x' : A) (s : A -> Prop) (q' : Prop) : term854 A B t n x x' s q'.
Proof. exact (@lem4297426 A B t n x x' s q' (@lem4297421 A x x' s)). Qed.
Lemma lem4297431 {A B : Type'} (t : type1413 A B) (x' : A) (n : nat) : (term742 A B t x' n) = (term742 A B t x' n).
Proof. exact (eq_refl (term742 A B t x' n)). Qed.
Lemma lem4297432 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (x' : A) (n : nat) : term855 A B x s t x' n.
Proof. exact (fun h0 : term81 A x x' s => @lem4297431 A B t x' n). Qed.
Lemma lem4297433 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (x' : A) (n : nat) : term856 A B x s t x' n.
Proof. exact (@lem4297427 A B t n x x' s (term742 A B t x' n)). Qed.
Lemma lem4297434 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (x' : A) (n : nat) : (term857 A B x s t x' n) = (term858 A B x s t x' n).
Proof. exact (@lem4297433 A B x s t x' n (@lem4297432 A B x s t x' n)). Qed.
Lemma lem4297466 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) : (term859 A B x s t n) = (term860 A B x s t n).
Proof. exact (fun_ext (fun x' : A => @lem4297434 A B x s t x' n)). Qed.
Lemma lem4297498 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4297499 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) : (term842 A B x s t n) = (term861 A B x s t n).
Proof. exact (MK_COMB (@lem4297498 A) (@lem4297466 A B x s t n)). Qed.
Lemma lem4297535 {A B : Type'} (m : nat) (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (q' : Prop) : term862 A B m x s t n q'.
Proof. exact (@lem4297400 A B x s t m n (term861 A B x s t n) q'). Qed.
Lemma lem4297536 {A B : Type'} (m : nat) (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (q' : Prop) : term863 A B m x s t n q'.
Proof. exact (@lem4297535 A B m x s t n q' (@lem4297499 A B x s t n)). Qed.
Lemma lem4297561 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term555 A x y s) = (term81 A y x s).
Proof. exact (EQ_MP (@lem4295909 A y x s) (@lem4295908 A y x s)). Qed.
Lemma lem4297562 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term555 A x y s) = (term81 A y x s).
Proof. exact (@lem4297561 A y x s). Qed.
Lemma lem4297563 {A : Type'} (x : A) (x' : A) (s : A -> Prop) : (term555 A x' x s) = (term81 A x x' s).
Proof. exact (@lem4297562 A x x' s). Qed.
Lemma lem4297568 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4297569 {A : Type'} (x : A) (x' : A) (s : A -> Prop) : (term864 A x' x s) = (term83 A x x' s).
Proof. exact (MK_COMB (@lem4297568) (@lem4297563 A x x' s)). Qed.
Lemma lem4297574 {A B : Type'} (y : B) (t : type1413 A B) (x' : A) : (term760 A B y t x') = (term760 A B y t x').
Proof. exact (eq_refl (term760 A B y t x')). Qed.
Lemma lem4297575 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (t : type1413 A B) (x' : A) : (term865 A B x s y t x') = (term866 A B x s y t x').
Proof. exact (MK_COMB (@lem4297569 A x x' s) (@lem4297574 A B y t x')). Qed.
Lemma lem4297582 {A B : Type'} (GEN_PVAR_121 : prod A B) : (@SETSPEC (prod A B) GEN_PVAR_121) = (@SETSPEC (prod A B) GEN_PVAR_121).
Proof. exact (eq_refl (@SETSPEC (prod A B) GEN_PVAR_121)). Qed.
Lemma lem4297583 {A B : Type'} (GEN_PVAR_121 : prod A B) (x : A) (s : A -> Prop) (y : B) (t : type1413 A B) (x' : A) : (term867 A B GEN_PVAR_121 x s y t x') = (term868 A B GEN_PVAR_121 x s y t x').
Proof. exact (MK_COMB (@lem4297582 A B GEN_PVAR_121) (@lem4297575 A B x s y t x')). Qed.
Lemma lem4297590 {A B : Type'} (x' : A) (y : B) : (@pair A B x' y) = (@pair A B x' y).
Proof. exact (eq_refl (@pair A B x' y)). Qed.
Lemma lem4297591 {A B : Type'} (GEN_PVAR_121 : prod A B) (x : A) (s : A -> Prop) (t : type1413 A B) (x' : A) (y : B) : (term869 A B GEN_PVAR_121 x s t x' y) = (term870 A B GEN_PVAR_121 x s t x' y).
Proof. exact (MK_COMB (@lem4297583 A B GEN_PVAR_121 x s y t x') (@lem4297590 A B x' y)). Qed.
Lemma lem4297598 {A B : Type'} (GEN_PVAR_121 : prod A B) (x : A) (s : A -> Prop) (t : type1413 A B) (x' : A) : (term871 A B GEN_PVAR_121 x s t x') = (term872 A B GEN_PVAR_121 x s t x').
Proof. exact (fun_ext (fun y : B => @lem4297591 A B GEN_PVAR_121 x s t x' y)). Qed.
Lemma lem4297605 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4297606 {A B : Type'} (GEN_PVAR_121 : prod A B) (x : A) (s : A -> Prop) (t : type1413 A B) (x' : A) : (term873 A B GEN_PVAR_121 x s t x') = (term874 A B GEN_PVAR_121 x s t x').
Proof. exact (MK_COMB (@lem4297605 B) (@lem4297598 A B GEN_PVAR_121 x s t x')). Qed.
Lemma lem4297617 {A B : Type'} (GEN_PVAR_121 : prod A B) (x : A) (s : A -> Prop) (t : type1413 A B) : (term875 A B GEN_PVAR_121 x s t) = (term876 A B GEN_PVAR_121 x s t).
Proof. exact (fun_ext (fun x' : A => @lem4297606 A B GEN_PVAR_121 x s t x')). Qed.
Lemma lem4297628 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4297629 {A B : Type'} (GEN_PVAR_121 : prod A B) (x : A) (s : A -> Prop) (t : type1413 A B) : (term877 A B GEN_PVAR_121 x s t) = (term878 A B GEN_PVAR_121 x s t).
Proof. exact (MK_COMB (@lem4297628 A) (@lem4297617 A B GEN_PVAR_121 x s t)). Qed.
Lemma lem4297644 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term879 A B x s t) = (term880 A B x s t).
Proof. exact (fun_ext (fun GEN_PVAR_121 : prod A B => @lem4297629 A B GEN_PVAR_121 x s t)). Qed.
Lemma lem4297659 {A B : Type'} : (@GSPEC (prod A B)) = (@GSPEC (prod A B)).
Proof. exact (eq_refl (@GSPEC (prod A B))). Qed.
Lemma lem4297660 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term881 A B x s t) = (term882 A B x s t).
Proof. exact (MK_COMB (@lem4297659 A B) (@lem4297644 A B x s t)). Qed.
Lemma lem4297675 {A B : Type'} : (@HAS_SIZE (prod A B)) = (@HAS_SIZE (prod A B)).
Proof. exact (eq_refl (@HAS_SIZE (prod A B))). Qed.
Lemma lem4297676 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term883 A B x s t) = (term884 A B x s t).
Proof. exact (MK_COMB (@lem4297675 A B) (@lem4297660 A B x s t)). Qed.
Lemma lem4297691 (m : nat) (n : nat) : (Nat.mul m n) = (Nat.mul m n).
Proof. exact (eq_refl (Nat.mul m n)). Qed.
Lemma lem4297692 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) : (term843 A B x s t m n) = (term885 A B x s t m n).
Proof. exact (MK_COMB (@lem4297676 A B x s t) (@lem4297691 m n)). Qed.
Lemma lem4297707 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) : term886 A B x s t m n.
Proof. exact (fun h0 : term861 A B x s t n => @lem4297692 A B x s t m n). Qed.
Lemma lem4297708 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) : term887 A B x s t m n.
Proof. exact (@lem4297536 A B m x s t n (term885 A B x s t m n)). Qed.
Lemma lem4297709 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) : (term888 A B x s t m n) = (term889 A B x s t m n).
Proof. exact (@lem4297708 A B x s t m n (@lem4297707 A B x s t m n)). Qed.
Lemma lem4297841 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (m : nat) : (term890 A B x s t m) = (term891 A B x s t m).
Proof. exact (fun_ext (fun n : nat => @lem4297709 A B x s t m n)). Qed.
Lemma lem4297973 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4297974 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (m : nat) : (term892 A B x s t m) = (term893 A B x s t m).
Proof. exact (MK_COMB (@lem4297973) (@lem4297841 A B x s t m)). Qed.
Lemma lem4298110 {A B : Type'} (x : A) (s : A -> Prop) (m : nat) : (term894 A B x s m) = (term895 A B x s m).
Proof. exact (fun_ext (fun t : type1413 A B => @lem4297974 A B x s t m)). Qed.
Lemma lem4298246 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem4298247 {A B : Type'} (x : A) (s : A -> Prop) (m : nat) : (term811 A B x s m) = (term896 A B x s m).
Proof. exact (MK_COMB (@lem4298246 A B) (@lem4298110 A B x s m)). Qed.
Lemma lem4298387 {A B : Type'} (x : A) (s : A -> Prop) (m : nat) : term897 A B x s m.
Proof. exact (fun h0 : (term822 A s) = m => @lem4298247 A B x s m). Qed.
Lemma lem4298388 {A B : Type'} (m : nat) (x : A) (s : A -> Prop) (h1 : term698 A B x s) : term898 A B x s m.
Proof. exact (@lem4297378 A B m (term896 A B x s m) x s h1). Qed.
Lemma lem4298389 {A B : Type'} (m : nat) (x : A) (s : A -> Prop) (h1 : term698 A B x s) : (term899 A B x s m) = (term900 A B x s m).
Proof. exact (@lem4298388 A B m x s h1 (@lem4298387 A B x s m)). Qed.
Lemma lem4298695 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term698 A B x s) : (term901 A B x s) = (term902 A B x s).
Proof. exact (fun_ext (fun m : nat => @lem4298389 A B m x s h1)). Qed.
Lemma lem4299001 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4299002 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term698 A B x s) : (term702 A B x s) = (term903 A B x s).
Proof. exact (MK_COMB (@lem4299001) (@lem4298695 A B x s h1)). Qed.
Lemma lem4299312 {A B : Type'} (x : A) (s : A -> Prop) : term904 A B x s.
Proof. exact (fun h0 : term698 A B x s => @lem4299002 A B x s h0). Qed.
Lemma lem4299313 {A B : Type'} (x : A) (s : A -> Prop) : term905 A B x s.
Proof. exact (@lem4297265 A B x s (term903 A B x s)). Qed.
Lemma lem4299314 {A B : Type'} (x : A) (s : A -> Prop) : (term704 A B x s) = (term906 A B x s).
Proof. exact (@lem4299313 A B x s (@lem4299312 A B x s)). Qed.
Lemma lem4300517 {A B : Type'} (x : A) : (term706 A B x) = (term907 A B x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4299314 A B x s)). Qed.
Lemma lem4301720 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4301721 {A B : Type'} (x : A) : (term708 A B x) = (term908 A B x).
Proof. exact (MK_COMB (@lem4301720 A) (@lem4300517 A B x)). Qed.
Lemma lem4302928 {A B : Type'} : (term710 A B) = (term909 A B).
Proof. exact (fun_ext (fun x : A => @lem4301721 A B x)). Qed.
Lemma lem4304135 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4304136 {A B : Type'} : (term712 A B) = (term910 A B).
Proof. exact (MK_COMB (@lem4304135 A) (@lem4302928 A B)). Qed.
Lemma lem4305347 {A B : Type'} : (term714 A B) = (term911 A B).
Proof. exact (MK_COMB (@lem4296921 A B) (@lem4304136 A B)). Qed.
Lemma lem4306615 {A B : Type'} : (term911 A B) = (term714 A B).
Proof. exact (SYM (@lem4305347 A B)). Qed.
Lemma lem4306616 (m : nat) (h1 : (NUMERAL 0) = m) : (NUMERAL 0) = m.
Proof. exact (h1). Qed.
Lemma lem4306617 (m : nat) (h1 : (NUMERAL 0) = m) : m = (NUMERAL 0).
Proof. exact (SYM (@lem4306616 m h1)). Qed.
Lemma lem4306618 {A B : Type'} : (term912 A B) = (term912 A B).
Proof. exact (eq_refl (term912 A B)). Qed.
Lemma lem4306619 {A B : Type'} (m : nat) (h1 : (NUMERAL 0) = m) : (term913 A B m) = (term914 A B).
Proof. exact (MK_COMB (@lem4306618 A B) (@lem4306617 m h1)). Qed.
Lemma lem4306620 {A B : Type'} : (term914 A B) = (term915 A B).
Proof. exact (eq_refl (term914 A B)). Qed.
Lemma lem4306621 {A B : Type'} (m : nat) : (term916 A B m) = (term916 A B m).
Proof. exact (eq_refl (term916 A B m)). Qed.
Lemma lem4306622 {A B : Type'} (m : nat) : ((term913 A B m) = (term914 A B)) = ((term913 A B m) = (term915 A B)).
Proof. exact (MK_COMB (@lem4306621 A B m) (@lem4306620 A B)). Qed.
Lemma lem4306623 {A B : Type'} (m : nat) : (term913 A B m) = (term788 A B m).
Proof. exact (eq_refl (term913 A B m)). Qed.
Lemma lem4306624 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4306625 {A B : Type'} (m : nat) : (term916 A B m) = (term917 A B m).
Proof. exact (MK_COMB (@lem4306624) (@lem4306623 A B m)). Qed.
Lemma lem4306626 {A B : Type'} : (term915 A B) = (term915 A B).
Proof. exact (eq_refl (term915 A B)). Qed.
Lemma lem4306627 {A B : Type'} (m : nat) : ((term913 A B m) = (term915 A B)) = ((term788 A B m) = (term915 A B)).
Proof. exact (MK_COMB (@lem4306625 A B m) (@lem4306626 A B)). Qed.
Lemma lem4306628 {A B : Type'} (m : nat) : ((term913 A B m) = (term914 A B)) = ((term788 A B m) = (term915 A B)).
Proof. exact (TRANS (@lem4306622 A B m) (@lem4306627 A B m)). Qed.
Lemma lem4306629 {A B : Type'} (m : nat) (h1 : (NUMERAL 0) = m) : (term788 A B m) = (term915 A B).
Proof. exact (EQ_MP (@lem4306628 A B m) (@lem4306619 A B m h1)). Qed.
Lemma lem4306630 {A B : Type'} (m : nat) (h1 : (NUMERAL 0) = m) : (term915 A B) = (term788 A B m).
Proof. exact (SYM (@lem4306629 A B m h1)). Qed.
Lemma lem4306644 (n : nat) : (term549 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem4295900 n) (@lem4295899 n)). Qed.
Lemma lem4306645 {A B : Type'} : (term779 A B) = (term779 A B).
Proof. exact (eq_refl (term779 A B)). Qed.
Lemma lem4306646 {A B : Type'} (n : nat) : (term918 A B n) = (term919 A B).
Proof. exact (MK_COMB (@lem4306645 A B) (@lem4306644 n)). Qed.
Lemma lem4306648 {A : Type'} (s : A -> Prop) : (term546 A s) = (s = (@EMPTY A)).
Proof. exact (EQ_MP (@lem4295866 A s) (@lem4295865 A s)). Qed.
Lemma lem4306649 {A B : Type'} (s : type1210 A B) : (term920 A B s) = (s = (@EMPTY (prod A B))).
Proof. exact (@lem4306648 (prod A B) s). Qed.
Lemma lem4306650 {A B : Type'} : (term919 A B) = ((term777 A B) = (@EMPTY (prod A B))).
Proof. exact (@lem4306649 A B (term777 A B)). Qed.
Lemma lem4306661 {A B : Type'} (n : nat) : (term918 A B n) = ((term777 A B) = (@EMPTY (prod A B))).
Proof. exact (TRANS (@lem4306646 A B n) (@lem4306650 A B)). Qed.
Lemma lem4306662 {A B : Type'} : (term921 A B) = (term922 A B).
Proof. exact (fun_ext (fun n : nat => @lem4306661 A B n)). Qed.
Lemma lem4306663 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4306664 {A B : Type'} : (term915 A B) = (term923 A B).
Proof. exact (MK_COMB (@lem4306663) (@lem4306662 A B)). Qed.
Lemma lem4306666 {A : Type'} (t : Prop) : (term756 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4306667 (t : Prop) : (term924 t) = t.
Proof. exact (@lem4306666 nat t). Qed.
Lemma lem4306668 {A B : Type'} : (term923 A B) = ((term777 A B) = (@EMPTY (prod A B))).
Proof. exact (@lem4306667 ((term777 A B) = (@EMPTY (prod A B)))). Qed.
Lemma lem4306679 {A B : Type'} : (term915 A B) = ((term777 A B) = (@EMPTY (prod A B))).
Proof. exact (TRANS (@lem4306664 A B) (@lem4306668 A B)). Qed.
Lemma lem4306680 {A B : Type'} : ((term777 A B) = (@EMPTY (prod A B))) = (term915 A B).
Proof. exact (SYM (@lem4306679 A B)). Qed.
Lemma lem4306684 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term6 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4306685 {A B : Type'} (s : type1210 A B) (t : type1210 A B) : (s = t) = (term925 A B s t).
Proof. exact (@lem4306684 (prod A B) s t). Qed.
Lemma lem4306686 {A B : Type'} : ((term777 A B) = (@EMPTY (prod A B))) = (term926 A B).
Proof. exact (@lem4306685 A B (term777 A B) (@EMPTY (prod A B))). Qed.
Lemma lem4306703 {A B : Type'} : (term926 A B) = ((term777 A B) = (@EMPTY (prod A B))).
Proof. exact (SYM (@lem4306686 A B)). Qed.
Lemma lem4306711 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term18 _83064 x P) = (term19 _83064 P x).
Proof. exact (EQ_MP (@lem3211648 _83064 P x) (@lem3211647 _83064 P x)). Qed.
Lemma lem4306712 {A B : Type'} (P : type914 A B) (x : prod A B) : (term927 A B x P) = (term928 A B P x).
Proof. exact (@lem4306711 (prod A B) P x). Qed.
Lemma lem4306713 {A B : Type'} (x : prod A B) : (term929 A B x) = (term930 A B x).
Proof. exact (@lem4306712 A B (term931 A B) x). Qed.
Lemma lem4306714 {A B : Type'} (GEN_PVAR_121 : prod A B) : (term932 A B GEN_PVAR_121) = (term773 A B GEN_PVAR_121).
Proof. exact (eq_refl (term932 A B GEN_PVAR_121)). Qed.
Lemma lem4306715 {A B : Type'} : (term933 A B) = (term775 A B).
Proof. exact (fun_ext (fun GEN_PVAR_121 : prod A B => @lem4306714 A B GEN_PVAR_121)). Qed.
Lemma lem4306716 {A B : Type'} : (@GSPEC (prod A B)) = (@GSPEC (prod A B)).
Proof. exact (eq_refl (@GSPEC (prod A B))). Qed.
Lemma lem4306717 {A B : Type'} : (term934 A B) = (term777 A B).
Proof. exact (MK_COMB (@lem4306716 A B) (@lem4306715 A B)). Qed.
Lemma lem4306718 {A B : Type'} (x : prod A B) : (@IN (prod A B) x) = (@IN (prod A B) x).
Proof. exact (eq_refl (@IN (prod A B) x)). Qed.
Lemma lem4306719 {A B : Type'} (x : prod A B) : (term929 A B x) = (term935 A B x).
Proof. exact (MK_COMB (@lem4306718 A B x) (@lem4306717 A B)). Qed.
Lemma lem4306720 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4306721 {A B : Type'} (x : prod A B) : (term936 A B x) = (term937 A B x).
Proof. exact (MK_COMB (@lem4306720) (@lem4306719 A B x)). Qed.
Lemma lem4306722 {A B : Type'} (x : prod A B) : (term930 A B x) = (term938 A B x).
Proof. exact (eq_refl (term930 A B x)). Qed.
Lemma lem4306723 {A B : Type'} (x : prod A B) : ((term929 A B x) = (term930 A B x)) = ((term935 A B x) = (term938 A B x)).
Proof. exact (MK_COMB (@lem4306721 A B x) (@lem4306722 A B x)). Qed.
Lemma lem4306724 {A B : Type'} (x : prod A B) : (term935 A B x) = (term938 A B x).
Proof. exact (EQ_MP (@lem4306723 A B x) (@lem4306713 A B x)). Qed.
Lemma lem4306734 {A B : Type'} (f : A -> B) (y : A) : (term68 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4306735 {A B : Type'} (f : type1532 A B) (y : Prop) : (term939 A B f y) = (f y).
Proof. exact (@lem4306734 Prop (type1210 A B) f y). Qed.
Lemma lem4306736 {A B : Type'} (x : prod A B) : (term940 A B x) = (term941 A B x).
Proof. exact (@lem4306735 A B (term942 A B x) False). Qed.
Lemma lem4306737 {A B : Type'} (p : Prop) (x : prod A B) : (term943 A B x p) = (term944 A B p x).
Proof. exact (eq_refl (term943 A B x p)). Qed.
Lemma lem4306738 {A B : Type'} (x : prod A B) : (term945 A B x) = (term942 A B x).
Proof. exact (fun_ext (fun p : Prop => @lem4306737 A B p x)). Qed.
Lemma lem4306739 : False = False.
Proof. exact (eq_refl False). Qed.
Lemma lem4306740 {A B : Type'} (x : prod A B) : (term940 A B x) = (term941 A B x).
Proof. exact (MK_COMB (@lem4306738 A B x) (@lem4306739)). Qed.
Lemma lem4306741 {A B : Type'} : (@eq ((prod A B) -> Prop)) = (@eq ((prod A B) -> Prop)).
Proof. exact (eq_refl (@eq ((prod A B) -> Prop))). Qed.
Lemma lem4306742 {A B : Type'} (x : prod A B) : (term946 A B x) = (term947 A B x).
Proof. exact (MK_COMB (@lem4306741 A B) (@lem4306740 A B x)). Qed.
Lemma lem4306743 {A B : Type'} (x : prod A B) : (term941 A B x) = (term948 A B x).
Proof. exact (eq_refl (term941 A B x)). Qed.
Lemma lem4306744 {A B : Type'} (x : prod A B) : ((term940 A B x) = (term941 A B x)) = ((term941 A B x) = (term948 A B x)).
Proof. exact (MK_COMB (@lem4306742 A B x) (@lem4306743 A B x)). Qed.
Lemma lem4306745 {A B : Type'} (x : prod A B) : (term941 A B x) = (term948 A B x).
Proof. exact (EQ_MP (@lem4306744 A B x) (@lem4306736 A B x)). Qed.
Lemma lem4306747 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem4306748 {A B : Type'} (x : prod A B) (t : prod A B) : (term949 A B x t) = False.
Proof. exact (@lem4306747 (x = t)). Qed.
Lemma lem4306749 {A B : Type'} (x : prod A B) : (term948 A B x) = (term950 A B).
Proof. exact (fun_ext (fun t : prod A B => @lem4306748 A B x t)). Qed.
Lemma lem4306750 {A B : Type'} (x : prod A B) : (term941 A B x) = (term950 A B).
Proof. exact (TRANS (@lem4306745 A B x) (@lem4306749 A B x)). Qed.
Lemma lem4306751 {A B : Type'} (x : A) (y : B) : (@pair A B x y) = (@pair A B x y).
Proof. exact (eq_refl (@pair A B x y)). Qed.
Lemma lem4306752 {A B : Type'} (x : prod A B) (x' : A) (y : B) : (term951 A B x x' y) = (term952 A B x' y).
Proof. exact (MK_COMB (@lem4306750 A B x) (@lem4306751 A B x' y)). Qed.
Lemma lem4306754 {A B : Type'} (f : A -> B) (y : A) : (term68 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4306755 {A B : Type'} (f : type1210 A B) (y : prod A B) : (term953 A B f y) = (f y).
Proof. exact (@lem4306754 (prod A B) Prop f y). Qed.
Lemma lem4306756 {A B : Type'} (x : A) (y : B) : (term954 A B x y) = (term952 A B x y).
Proof. exact (@lem4306755 A B (term950 A B) (@pair A B x y)). Qed.
Lemma lem4306757 {A B : Type'} (t : prod A B) : (term955 A B t) = False.
Proof. exact (eq_refl (term955 A B t)). Qed.
Lemma lem4306758 {A B : Type'} : (term956 A B) = (term950 A B).
Proof. exact (fun_ext (fun t : prod A B => @lem4306757 A B t)). Qed.
Lemma lem4306759 {A B : Type'} (x : A) (y : B) : (@pair A B x y) = (@pair A B x y).
Proof. exact (eq_refl (@pair A B x y)). Qed.
Lemma lem4306760 {A B : Type'} (x : A) (y : B) : (term954 A B x y) = (term952 A B x y).
Proof. exact (MK_COMB (@lem4306758 A B) (@lem4306759 A B x y)). Qed.
Lemma lem4306761 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4306762 {A B : Type'} (x : A) (y : B) : (term957 A B x y) = (term958 A B x y).
Proof. exact (MK_COMB (@lem4306761) (@lem4306760 A B x y)). Qed.
Lemma lem4306763 {A B : Type'} (x : A) (y : B) : (term952 A B x y) = False.
Proof. exact (eq_refl (term952 A B x y)). Qed.
Lemma lem4306764 {A B : Type'} (x : A) (y : B) : ((term954 A B x y) = (term952 A B x y)) = ((term952 A B x y) = False).
Proof. exact (MK_COMB (@lem4306762 A B x y) (@lem4306763 A B x y)). Qed.
Lemma lem4306765 {A B : Type'} (x : A) (y : B) : (term952 A B x y) = False.
Proof. exact (EQ_MP (@lem4306764 A B x y) (@lem4306756 A B x y)). Qed.
Lemma lem4306766 {A B : Type'} (x : prod A B) (x' : A) (y : B) : (term951 A B x x' y) = False.
Proof. exact (TRANS (@lem4306752 A B x x' y) (@lem4306765 A B x' y)). Qed.
Lemma lem4306767 {A B : Type'} (x : prod A B) (x' : A) : (term959 A B x x') = (term960 B).
Proof. exact (fun_ext (fun y : B => @lem4306766 A B x x' y)). Qed.
Lemma lem4306768 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4306769 {A B : Type'} (x : prod A B) (x' : A) : (term961 A B x x') = (term962 B).
Proof. exact (MK_COMB (@lem4306768 B) (@lem4306767 A B x x')). Qed.
Lemma lem4306771 {A : Type'} (t : Prop) : (term963 A t) = t.
Proof. exact (EQ_MP (@lem1813 A t) (@lem1812 A t)). Qed.
Lemma lem4306772 {B : Type'} (t : Prop) : (term963 B t) = t.
Proof. exact (@lem4306771 B t). Qed.
Lemma lem4306773 {B : Type'} : (term962 B) = False.
Proof. exact (@lem4306772 B False). Qed.
Lemma lem4306774 {A B : Type'} (x : prod A B) (x' : A) : (term961 A B x x') = False.
Proof. exact (TRANS (@lem4306769 A B x x') (@lem4306773 B)). Qed.
Lemma lem4306775 {A B : Type'} (x : prod A B) : (term964 A B x) = (term960 A).
Proof. exact (fun_ext (fun x' : A => @lem4306774 A B x x')). Qed.
Lemma lem4306776 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4306777 {A B : Type'} (x : prod A B) : (term938 A B x) = (term962 A).
Proof. exact (MK_COMB (@lem4306776 A) (@lem4306775 A B x)). Qed.
Lemma lem4306779 {A : Type'} (t : Prop) : (term963 A t) = t.
Proof. exact (EQ_MP (@lem1813 A t) (@lem1812 A t)). Qed.
Lemma lem4306780 {A : Type'} (t : Prop) : (term963 A t) = t.
Proof. exact (@lem4306779 A t). Qed.
Lemma lem4306781 {A : Type'} : (term962 A) = False.
Proof. exact (@lem4306780 A False). Qed.
Lemma lem4306782 {A B : Type'} (x : prod A B) : (term938 A B x) = False.
Proof. exact (TRANS (@lem4306777 A B x) (@lem4306781 A)). Qed.
Lemma lem4306783 {A B : Type'} (x : prod A B) : (term935 A B x) = False.
Proof. exact (TRANS (@lem4306724 A B x) (@lem4306782 A B x)). Qed.
Lemma lem4306784 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4306785 {A B : Type'} (x : prod A B) : (term937 A B x) = (@eq Prop False).
Proof. exact (MK_COMB (@lem4306784) (@lem4306783 A B x)). Qed.
Lemma lem4306787 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4306788 {A B : Type'} (x : prod A B) : (@IN (prod A B) x (@EMPTY (prod A B))) = False.
Proof. exact (@lem4306787 (prod A B) x). Qed.
Lemma lem4306789 {A B : Type'} (x : prod A B) : ((term935 A B x) = (@IN (prod A B) x (@EMPTY (prod A B)))) = (False = False).
Proof. exact (MK_COMB (@lem4306785 A B x) (@lem4306788 A B x)). Qed.
Lemma lem4306791 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem4306792 : (False = False) = (~ False).
Proof. exact (@lem4306791 False). Qed.
Lemma lem4306794 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem4306795 : (False = False) = True.
Proof. exact (TRANS (@lem4306792) (@lem4306794)). Qed.
Lemma lem4306796 {A B : Type'} (x : prod A B) : ((term935 A B x) = (@IN (prod A B) x (@EMPTY (prod A B)))) = True.
Proof. exact (TRANS (@lem4306789 A B x) (@lem4306795)). Qed.
Lemma lem4306797 {A B : Type'} : (term965 A B) = (term966 A B).
Proof. exact (fun_ext (fun x : prod A B => @lem4306796 A B x)). Qed.
Lemma lem4306798 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem4306799 {A B : Type'} : (term926 A B) = (term967 A B).
Proof. exact (MK_COMB (@lem4306798 A B) (@lem4306797 A B)). Qed.
Lemma lem4306801 {A : Type'} (t : Prop) : (term756 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4306802 {A B : Type'} (t : Prop) : (term968 A B t) = t.
Proof. exact (@lem4306801 (prod A B) t). Qed.
Lemma lem4306803 {A B : Type'} : (term967 A B) = True.
Proof. exact (@lem4306802 A B True). Qed.
Lemma lem4306804 {A B : Type'} : (term926 A B) = True.
Proof. exact (TRANS (@lem4306799 A B) (@lem4306803 A B)). Qed.
Lemma lem4306805 {A B : Type'} : True = (term926 A B).
Proof. exact (SYM (@lem4306804 A B)). Qed.
Lemma lem4306806 {A B : Type'} : term926 A B.
Proof. exact (EQ_MP (@lem4306805 A B) (@lem0)). Qed.
Lemma lem4306807 {A B : Type'} : (term777 A B) = (@EMPTY (prod A B)).
Proof. exact (EQ_MP (@lem4306703 A B) (@lem4306806 A B)). Qed.
Lemma lem4306808 {A B : Type'} : term915 A B.
Proof. exact (EQ_MP (@lem4306680 A B) (@lem4306807 A B)). Qed.
Lemma lem4306809 {A B : Type'} (m : nat) (h1 : (NUMERAL 0) = m) : term788 A B m.
Proof. exact (EQ_MP (@lem4306630 A B m h1) (@lem4306808 A B)). Qed.
Lemma lem4306810 {A B : Type'} (m : nat) : term796 A B m.
Proof. exact (fun h0 : (NUMERAL 0) = m => @lem4306809 A B m h0). Qed.
Lemma lem4306815 {A B : Type'} : term799 A B.
Proof. exact (fun m : nat => @lem4306810 A B m). Qed.
Lemma lem4306816 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term698 A B x s) : term698 A B x s.
Proof. exact (h1). Qed.
Lemma lem4306817 {A : Type'} (x : A) (s : A -> Prop) (h1 : term696 A x s) : term696 A x s.
Proof. exact (h1). Qed.
Lemma lem4306818 {A B : Type'} (s : A -> Prop) (h1 : term683 A B s) : term683 A B s.
Proof. exact (h1). Qed.
Lemma lem4306819 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4306820 {A : Type'} (x : A) (s : A -> Prop) (h1 : term808 A x s) : term808 A x s.
Proof. exact (h1). Qed.
Lemma lem4306821 {A : Type'} (s : A -> Prop) (m : nat) (h1 : (term822 A s) = m) : (term822 A s) = m.
Proof. exact (h1). Qed.
Lemma lem4306822 {A : Type'} (s : A -> Prop) (m : nat) (h1 : (term822 A s) = m) : m = (term822 A s).
Proof. exact (SYM (@lem4306821 A s m h1)). Qed.
Lemma lem4306830 (a : Prop) (b : Prop) (c : Prop) : (term521 a b c) = (term522 a b c).
Proof. exact (or_elim (@lem4295662 a) (fun h0 : a = True => @lem4295851 b c a h0) (fun h0 : a = False => @lem4295850 b c a h0)). Qed.
Lemma lem4306831 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (x' : A) (n : nat) : (term858 A B x s t x' n) = (term969 A B x s t x' n).
Proof. exact (@lem4306830 (x' = x) (@IN A x' s) (term742 A B t x' n)). Qed.
Lemma lem4306842 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) : (term860 A B x s t n) = (term970 A B x s t n).
Proof. exact (fun_ext (fun x' : A => @lem4306831 A B x s t x' n)). Qed.
Lemma lem4306843 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4306844 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) : (term861 A B x s t n) = (term971 A B x s t n).
Proof. exact (MK_COMB (@lem4306843 A) (@lem4306842 A B x s t n)). Qed.
Lemma lem4306849 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4306850 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) : (term972 A B x s t n) = (term973 A B x s t n).
Proof. exact (MK_COMB (@lem4306849) (@lem4306844 A B x s t n)). Qed.
Lemma lem4306865 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) : (term885 A B x s t m n) = (term885 A B x s t m n).
Proof. exact (eq_refl (term885 A B x s t m n)). Qed.
Lemma lem4306866 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) : (term889 A B x s t m n) = (term974 A B x s t m n).
Proof. exact (MK_COMB (@lem4306850 A B x s t n) (@lem4306865 A B x s t m n)). Qed.
Lemma lem4306869 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) : (term974 A B x s t m n) = (term889 A B x s t m n).
Proof. exact (SYM (@lem4306866 A B x s t m n)). Qed.
Lemma lem4306873 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term721 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4306874 (p : Prop) (q : Prop) (p' : Prop) : term722 p q p'.
Proof. exact (fun q' : Prop => @lem4306873 p q p' q'). Qed.
Lemma lem4306875 (p : Prop) (q : Prop) : term723 p q.
Proof. exact (fun p' : Prop => @lem4306874 p q p'). Qed.
Lemma lem4306876 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) : term975 A B x s t m n.
Proof. exact (@lem4306875 (term971 A B x s t n) (term885 A B x s t m n)). Qed.
Lemma lem4306877 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) (p' : Prop) : term976 A B x s t m n p'.
Proof. exact (@lem4306876 A B x s t m n p'). Qed.
Lemma lem4306878 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) (p' : Prop) : (term976 A B x s t m n p') = (term977 A B x s t m n p').
Proof. exact (eq_refl (term976 A B x s t m n p')). Qed.
Lemma lem4306879 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) (p' : Prop) : term977 A B x s t m n p'.
Proof. exact (EQ_MP (@lem4306878 A B x s t m n p') (@lem4306877 A B x s t m n p')). Qed.
Lemma lem4306880 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) (p' : Prop) (q' : Prop) : term978 A B x s t m n p' q'.
Proof. exact (@lem4306879 A B x s t m n p' q'). Qed.
Lemma lem4306881 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) (p' : Prop) (q' : Prop) : (term978 A B x s t m n p' q') = (term979 A B x s t m n p' q').
Proof. exact (eq_refl (term978 A B x s t m n p' q')). Qed.
Lemma lem4306882 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) (p' : Prop) (q' : Prop) : term979 A B x s t m n p' q'.
Proof. exact (EQ_MP (@lem4306881 A B x s t m n p' q') (@lem4306880 A B x s t m n p' q')). Qed.
Lemma lem4306884 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term511 A P Q) = (term512 A P Q).
Proof. exact (EQ_MP (@lem4295644 A P Q) (@lem4295643 A P Q)). Qed.
Lemma lem4306885 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term511 A P Q) = (term512 A P Q).
Proof. exact (@lem4306884 A P Q). Qed.
Lemma lem4306886 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) : (term980 A B x s t n) = (term981 A B x s t n).
Proof. exact (@lem4306885 A (term982 A B x t n) (term983 A B s t n)). Qed.
Lemma lem4306887 {A B : Type'} (x : A) (t : type1413 A B) (x' : A) (n : nat) : (term984 A B x t n x') = (term985 A B x t x' n).
Proof. exact (eq_refl (term984 A B x t n x')). Qed.
Lemma lem4306888 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4306889 {A B : Type'} (x : A) (t : type1413 A B) (x' : A) (n : nat) : (term986 A B x t n x') = (term987 A B x t x' n).
Proof. exact (MK_COMB (@lem4306888) (@lem4306887 A B x t x' n)). Qed.
Lemma lem4306890 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x' : A) (n : nat) : (term988 A B s t n x') = (term989 A B s t x' n).
Proof. exact (eq_refl (term988 A B s t n x')). Qed.
Lemma lem4306891 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (x' : A) (n : nat) : (term990 A B x s t n x') = (term969 A B x s t x' n).
Proof. exact (MK_COMB (@lem4306889 A B x t x' n) (@lem4306890 A B s t x' n)). Qed.
Lemma lem4306892 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) : (term991 A B x s t n) = (term970 A B x s t n).
Proof. exact (fun_ext (fun x' : A => @lem4306891 A B x s t x' n)). Qed.
Lemma lem4306893 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4306894 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) : (term980 A B x s t n) = (term971 A B x s t n).
Proof. exact (MK_COMB (@lem4306893 A) (@lem4306892 A B x s t n)). Qed.
Lemma lem4306895 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4306896 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) : (term992 A B x s t n) = (term993 A B x s t n).
Proof. exact (MK_COMB (@lem4306895) (@lem4306894 A B x s t n)). Qed.
Lemma lem4306897 {A B : Type'} (x : A) (t : type1413 A B) (x' : A) (n : nat) : (term984 A B x t n x') = (term985 A B x t x' n).
Proof. exact (eq_refl (term984 A B x t n x')). Qed.
Lemma lem4306898 {A B : Type'} (x : A) (t : type1413 A B) (n : nat) : (term994 A B x t n) = (term982 A B x t n).
Proof. exact (fun_ext (fun x' : A => @lem4306897 A B x t x' n)). Qed.
Lemma lem4306899 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4306900 {A B : Type'} (x : A) (t : type1413 A B) (n : nat) : (term995 A B x t n) = (term996 A B x t n).
Proof. exact (MK_COMB (@lem4306899 A) (@lem4306898 A B x t n)). Qed.
Lemma lem4306901 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4306902 {A B : Type'} (x : A) (t : type1413 A B) (n : nat) : (term997 A B x t n) = (term998 A B x t n).
Proof. exact (MK_COMB (@lem4306901) (@lem4306900 A B x t n)). Qed.
Lemma lem4306903 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x' : A) (n : nat) : (term988 A B s t n x') = (term989 A B s t x' n).
Proof. exact (eq_refl (term988 A B s t n x')). Qed.
Lemma lem4306904 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (n : nat) : (term999 A B s t n) = (term983 A B s t n).
Proof. exact (fun_ext (fun x' : A => @lem4306903 A B s t x' n)). Qed.
Lemma lem4306905 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4306906 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (n : nat) : (term1000 A B s t n) = (term581 A B s t n).
Proof. exact (MK_COMB (@lem4306905 A) (@lem4306904 A B s t n)). Qed.
Lemma lem4306907 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) : (term981 A B x s t n) = (term1001 A B x s t n).
Proof. exact (MK_COMB (@lem4306902 A B x t n) (@lem4306906 A B s t n)). Qed.
Lemma lem4306908 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) : ((term980 A B x s t n) = (term981 A B x s t n)) = ((term971 A B x s t n) = (term1001 A B x s t n)).
Proof. exact (MK_COMB (@lem4306896 A B x s t n) (@lem4306907 A B x s t n)). Qed.
Lemma lem4306909 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) : (term971 A B x s t n) = (term1001 A B x s t n).
Proof. exact (EQ_MP (@lem4306908 A B x s t n) (@lem4306886 A B x s t n)). Qed.
Lemma lem4306945 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term721 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4306946 (p : Prop) (q : Prop) (p' : Prop) : term722 p q p'.
Proof. exact (fun q' : Prop => @lem4306945 p q p' q'). Qed.
Lemma lem4306947 (p : Prop) (q : Prop) : term723 p q.
Proof. exact (fun p' : Prop => @lem4306946 p q p'). Qed.
Lemma lem4306948 {A B : Type'} (x : A) (t : type1413 A B) (x' : A) (n : nat) : term1002 A B x t x' n.
Proof. exact (@lem4306947 (x' = x) (term742 A B t x' n)). Qed.
Lemma lem4306949 {A B : Type'} (x : A) (t : type1413 A B) (x' : A) (n : nat) (p' : Prop) : term1003 A B x t x' n p'.
Proof. exact (@lem4306948 A B x t x' n p'). Qed.
Lemma lem4306950 {A B : Type'} (x : A) (t : type1413 A B) (x' : A) (n : nat) (p' : Prop) : (term1003 A B x t x' n p') = (term1004 A B x t x' n p').
Proof. exact (eq_refl (term1003 A B x t x' n p')). Qed.
Lemma lem4306951 {A B : Type'} (x : A) (t : type1413 A B) (x' : A) (n : nat) (p' : Prop) : term1004 A B x t x' n p'.
Proof. exact (EQ_MP (@lem4306950 A B x t x' n p') (@lem4306949 A B x t x' n p')). Qed.
Lemma lem4306952 {A B : Type'} (x : A) (t : type1413 A B) (x' : A) (n : nat) (p' : Prop) (q' : Prop) : term1005 A B x t x' n p' q'.
Proof. exact (@lem4306951 A B x t x' n p' q'). Qed.
Lemma lem4306953 {A B : Type'} (x : A) (t : type1413 A B) (x' : A) (n : nat) (p' : Prop) (q' : Prop) : (term1005 A B x t x' n p' q') = (term1006 A B x t x' n p' q').
Proof. exact (eq_refl (term1005 A B x t x' n p' q')). Qed.
Lemma lem4306954 {A B : Type'} (x : A) (t : type1413 A B) (x' : A) (n : nat) (p' : Prop) (q' : Prop) : term1006 A B x t x' n p' q'.
Proof. exact (EQ_MP (@lem4306953 A B x t x' n p' q') (@lem4306952 A B x t x' n p' q')). Qed.
Lemma lem4306957 {A : Type'} (x' : A) (x : A) : (x' = x) = (x' = x).
Proof. exact (eq_refl (x' = x)). Qed.
Lemma lem4306958 {A B : Type'} (t : type1413 A B) (n : nat) (x' : A) (x : A) (q' : Prop) : term1007 A B t n x' x q'.
Proof. exact (@lem4306954 A B x t x' n (x' = x) q'). Qed.
Lemma lem4306959 {A B : Type'} (t : type1413 A B) (n : nat) (x' : A) (x : A) (q' : Prop) : term1008 A B t n x' x q'.
Proof. exact (@lem4306958 A B t n x' x q' (@lem4306957 A x' x)). Qed.
Lemma lem4306962 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem4306963 {A B : Type'} (t : type1413 A B) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4306964 {A B : Type'} (t : type1413 A B) (x' : A) (x : A) (h1 : x' = x) : (t x') = (t x).
Proof. exact (MK_COMB (@lem4306963 A B t) (@lem4306962 A x' x h1)). Qed.
Lemma lem4306965 {B : Type'} : (@HAS_SIZE B) = (@HAS_SIZE B).
Proof. exact (eq_refl (@HAS_SIZE B)). Qed.
Lemma lem4306966 {A B : Type'} (t : type1413 A B) (x' : A) (x : A) (h1 : x' = x) : (term1009 A B t x') = (term1009 A B t x).
Proof. exact (MK_COMB (@lem4306965 B) (@lem4306964 A B t x' x h1)). Qed.
Lemma lem4306967 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem4306968 {A B : Type'} (t : type1413 A B) (n : nat) (x' : A) (x : A) (h1 : x' = x) : (term742 A B t x' n) = (term742 A B t x n).
Proof. exact (MK_COMB (@lem4306966 A B t x' x h1) (@lem4306967 n)). Qed.
Lemma lem4306969 {A B : Type'} (x' : A) (t : type1413 A B) (x : A) (n : nat) : term1010 A B x' t x n.
Proof. exact (fun h0 : x' = x => @lem4306968 A B t n x' x h0). Qed.
Lemma lem4306970 {A B : Type'} (x' : A) (t : type1413 A B) (x : A) (n : nat) : term1011 A B x' t x n.
Proof. exact (@lem4306959 A B t n x' x (term742 A B t x n)). Qed.
Lemma lem4306971 {A B : Type'} (x' : A) (t : type1413 A B) (x : A) (n : nat) : (term985 A B x t x' n) = (term1012 A B x' t x n).
Proof. exact (@lem4306970 A B x' t x n (@lem4306969 A B x' t x n)). Qed.
Lemma lem4306999 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) : (term982 A B x t n) = (term1013 A B t x n).
Proof. exact (fun_ext (fun x' : A => @lem4306971 A B x' t x n)). Qed.
Lemma lem4307027 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4307028 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) : (term996 A B x t n) = (term1014 A B t x n).
Proof. exact (MK_COMB (@lem4307027 A) (@lem4306999 A B t x n)). Qed.
Lemma lem4307030 {A : Type'} (P : A -> Prop) (Q : Prop) : (term506 A P Q) = (term507 A P Q).
Proof. exact (EQ_MP (@lem4295638 A P Q) (@lem4295637 A P Q)). Qed.
Lemma lem4307031 {A : Type'} (P : A -> Prop) (Q : Prop) : (term506 A P Q) = (term507 A P Q).
Proof. exact (@lem4307030 A P Q). Qed.
Lemma lem4307032 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) : (term1015 A B t x n) = (term1016 A B t x n).
Proof. exact (@lem4307031 A (term1017 A x) (term742 A B t x n)). Qed.
Lemma lem4307033 {A : Type'} (x' : A) (x : A) : (term1018 A x x') = (x' = x).
Proof. exact (eq_refl (term1018 A x x')). Qed.
Lemma lem4307034 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4307035 {A : Type'} (x' : A) (x : A) : (term1019 A x x') = (term1020 A x' x).
Proof. exact (MK_COMB (@lem4307034) (@lem4307033 A x' x)). Qed.
Lemma lem4307036 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) : (term742 A B t x n) = (term742 A B t x n).
Proof. exact (eq_refl (term742 A B t x n)). Qed.
Lemma lem4307037 {A B : Type'} (x' : A) (t : type1413 A B) (x : A) (n : nat) : (term1021 A B x' t x n) = (term1012 A B x' t x n).
Proof. exact (MK_COMB (@lem4307035 A x' x) (@lem4307036 A B t x n)). Qed.
Lemma lem4307038 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) : (term1022 A B t x n) = (term1013 A B t x n).
Proof. exact (fun_ext (fun x' : A => @lem4307037 A B x' t x n)). Qed.
Lemma lem4307039 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4307040 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) : (term1015 A B t x n) = (term1014 A B t x n).
Proof. exact (MK_COMB (@lem4307039 A) (@lem4307038 A B t x n)). Qed.
Lemma lem4307041 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4307042 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) : (term1023 A B t x n) = (term1024 A B t x n).
Proof. exact (MK_COMB (@lem4307041) (@lem4307040 A B t x n)). Qed.
Lemma lem4307043 {A : Type'} (x' : A) (x : A) : (term1018 A x x') = (x' = x).
Proof. exact (eq_refl (term1018 A x x')). Qed.
Lemma lem4307044 {A : Type'} (x : A) : (term1025 A x) = (term1017 A x).
Proof. exact (fun_ext (fun x' : A => @lem4307043 A x' x)). Qed.
Lemma lem4307045 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4307046 {A : Type'} (x : A) : (term1026 A x) = (term502 A x).
Proof. exact (MK_COMB (@lem4307045 A) (@lem4307044 A x)). Qed.
Lemma lem4307047 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4307048 {A : Type'} (x : A) : (term1027 A x) = (term1028 A x).
Proof. exact (MK_COMB (@lem4307047) (@lem4307046 A x)). Qed.
Lemma lem4307049 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) : (term742 A B t x n) = (term742 A B t x n).
Proof. exact (eq_refl (term742 A B t x n)). Qed.
Lemma lem4307050 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) : (term1016 A B t x n) = (term1029 A B t x n).
Proof. exact (MK_COMB (@lem4307048 A x) (@lem4307049 A B t x n)). Qed.
Lemma lem4307051 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) : ((term1015 A B t x n) = (term1016 A B t x n)) = ((term1014 A B t x n) = (term1029 A B t x n)).
Proof. exact (MK_COMB (@lem4307042 A B t x n) (@lem4307050 A B t x n)). Qed.
Lemma lem4307052 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) : (term1014 A B t x n) = (term1029 A B t x n).
Proof. exact (EQ_MP (@lem4307051 A B t x n) (@lem4307032 A B t x n)). Qed.
Lemma lem4307056 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term721 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4307057 (p : Prop) (q : Prop) (p' : Prop) : term722 p q p'.
Proof. exact (fun q' : Prop => @lem4307056 p q p' q'). Qed.
Lemma lem4307058 (p : Prop) (q : Prop) : term723 p q.
Proof. exact (fun p' : Prop => @lem4307057 p q p'). Qed.
Lemma lem4307059 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) : term1030 A B t x n.
Proof. exact (@lem4307058 (term502 A x) (term742 A B t x n)). Qed.
Lemma lem4307060 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) (p' : Prop) : term1031 A B t x n p'.
Proof. exact (@lem4307059 A B t x n p'). Qed.
Lemma lem4307061 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) (p' : Prop) : (term1031 A B t x n p') = (term1032 A B t x n p').
Proof. exact (eq_refl (term1031 A B t x n p')). Qed.
Lemma lem4307062 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) (p' : Prop) : term1032 A B t x n p'.
Proof. exact (EQ_MP (@lem4307061 A B t x n p') (@lem4307060 A B t x n p')). Qed.
Lemma lem4307063 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) (p' : Prop) (q' : Prop) : term1033 A B t x n p' q'.
Proof. exact (@lem4307062 A B t x n p' q'). Qed.
Lemma lem4307064 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) (p' : Prop) (q' : Prop) : (term1033 A B t x n p' q') = (term1034 A B t x n p' q').
Proof. exact (eq_refl (term1033 A B t x n p' q')). Qed.
Lemma lem4307065 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) (p' : Prop) (q' : Prop) : term1034 A B t x n p' q'.
Proof. exact (EQ_MP (@lem4307064 A B t x n p' q') (@lem4307063 A B t x n p' q')). Qed.
Lemma lem4307067 {A : Type'} (a : A) : (term502 A a) = True.
Proof. exact (EQ_MP (@lem4295632 A a) (@lem4295631 A a)). Qed.
Lemma lem4307068 {A : Type'} (a : A) : (term502 A a) = True.
Proof. exact (@lem4307067 A a). Qed.
Lemma lem4307069 {A : Type'} (x : A) : (term502 A x) = True.
Proof. exact (@lem4307068 A x). Qed.
Lemma lem4307070 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) (q' : Prop) : term1035 A B t x n q'.
Proof. exact (@lem4307065 A B t x n True q'). Qed.
Lemma lem4307071 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) (q' : Prop) : term1036 A B t x n q'.
Proof. exact (@lem4307070 A B t x n q' (@lem4307069 A x)). Qed.
Lemma lem4307077 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) : (term742 A B t x n) = (term742 A B t x n).
Proof. exact (eq_refl (term742 A B t x n)). Qed.
Lemma lem4307078 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) : term1037 A B t x n.
Proof. exact (fun h0 : True => @lem4307077 A B t x n). Qed.
Lemma lem4307079 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) : term1038 A B t x n.
Proof. exact (@lem4307071 A B t x n (term742 A B t x n)). Qed.
Lemma lem4307080 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) : (term1029 A B t x n) = (term1039 A B t x n).
Proof. exact (@lem4307079 A B t x n (@lem4307078 A B t x n)). Qed.
Lemma lem4307082 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem4307083 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) : (term1039 A B t x n) = (term742 A B t x n).
Proof. exact (@lem4307082 (term742 A B t x n)). Qed.
Lemma lem4307084 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) : (term1029 A B t x n) = (term742 A B t x n).
Proof. exact (TRANS (@lem4307080 A B t x n) (@lem4307083 A B t x n)). Qed.
Lemma lem4307085 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) : (term1014 A B t x n) = (term742 A B t x n).
Proof. exact (TRANS (@lem4307052 A B t x n) (@lem4307084 A B t x n)). Qed.
Lemma lem4307086 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) : (term996 A B x t n) = (term742 A B t x n).
Proof. exact (TRANS (@lem4307028 A B t x n) (@lem4307085 A B t x n)). Qed.
Lemma lem4307087 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4307088 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) : (term998 A B x t n) = (term1040 A B t x n).
Proof. exact (MK_COMB (@lem4307087) (@lem4307086 A B t x n)). Qed.
Lemma lem4307140 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (n : nat) : (term581 A B s t n) = (term581 A B s t n).
Proof. exact (eq_refl (term581 A B s t n)). Qed.
Lemma lem4307141 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) : (term1001 A B x s t n) = (term1041 A B x s t n).
Proof. exact (MK_COMB (@lem4307088 A B t x n) (@lem4307140 A B s t n)). Qed.
Lemma lem4307195 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) : (term971 A B x s t n) = (term1041 A B x s t n).
Proof. exact (TRANS (@lem4306909 A B x s t n) (@lem4307141 A B x s t n)). Qed.
Lemma lem4307196 {A B : Type'} (m : nat) (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (q' : Prop) : term1042 A B m x s t n q'.
Proof. exact (@lem4306882 A B x s t m n (term1041 A B x s t n) q'). Qed.
Lemma lem4307197 {A B : Type'} (m : nat) (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (q' : Prop) : term1043 A B m x s t n q'.
Proof. exact (@lem4307196 A B m x s t n q' (@lem4307195 A B x s t n)). Qed.
Lemma lem4307229 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) : (term885 A B x s t m n) = (term885 A B x s t m n).
Proof. exact (eq_refl (term885 A B x s t m n)). Qed.
Lemma lem4307230 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) : term1044 A B x s t m n.
Proof. exact (fun h0 : term1041 A B x s t n => @lem4307229 A B x s t m n). Qed.
Lemma lem4307231 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) : term1045 A B x s t m n.
Proof. exact (@lem4307197 A B m x s t n (term885 A B x s t m n)). Qed.
Lemma lem4307232 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) : (term974 A B x s t m n) = (term1046 A B x s t m n).
Proof. exact (@lem4307231 A B x s t m n (@lem4307230 A B x s t m n)). Qed.
Lemma lem4307404 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (m : nat) (n : nat) : (term1046 A B x s t m n) = (term974 A B x s t m n).
Proof. exact (SYM (@lem4307232 A B x s t m n)). Qed.
Lemma lem4307405 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term1041 A B x s t n) : term1041 A B x s t n.
Proof. exact (h1). Qed.
Lemma lem4307406 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term581 A B s t n) : term581 A B s t n.
Proof. exact (h1). Qed.
Lemma lem4307407 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) (h1 : term742 A B t x n) : term742 A B t x n.
Proof. exact (h1). Qed.
Lemma lem4307408 {A B : Type'} (s : A -> Prop) (h1 : term683 A B s) : term1047 A B s.
Proof. exact (@lem4306818 A B s h1 (@CARD A s)). Qed.
Lemma lem4307409 {A B : Type'} (s : A -> Prop) : (term1047 A B s) = (term1048 A B s).
Proof. exact (eq_refl (term1047 A B s)). Qed.
Lemma lem4307410 {A B : Type'} (s : A -> Prop) (h1 : term683 A B s) : term1048 A B s.
Proof. exact (EQ_MP (@lem4307409 A B s) (@lem4307408 A B s h1)). Qed.
Lemma lem4307411 : term1049.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem4307412 : term1050.
Proof. exact (proj2 (@lem4307411)). Qed.
Lemma lem4307413 : term1051.
Proof. exact (proj2 (@lem4307412)). Qed.
Lemma lem4307414 : term1052.
Proof. exact (proj2 (@lem4307413)). Qed.
Lemma lem4307422 : term1053.
Proof. exact (proj1 (@lem4307414)). Qed.
Lemma lem4307423 (m : nat) : term1054 m.
Proof. exact (@lem4307422 m). Qed.
Lemma lem4307424 (m : nat) : (term1054 m) = (term1055 m).
Proof. exact (eq_refl (term1054 m)). Qed.
Lemma lem4307425 (m : nat) : term1055 m.
Proof. exact (EQ_MP (@lem4307424 m) (@lem4307423 m)). Qed.
Lemma lem4307426 (m : nat) (n : nat) : term1056 m n.
Proof. exact (@lem4307425 m n). Qed.
Lemma lem4307427 (m : nat) (n : nat) : (term1056 m n) = ((term1057 m n) = (term1058 m n)).
Proof. exact (eq_refl (term1056 m n)). Qed.
Lemma lem4307459 {_739 : Type'} (x : _739) (p : Prop) : (term1059 _739 x p) = p.
Proof. exact (EQ_MP (@lem1804 _739 x p) (@lem0)). Qed.
Lemma lem4307460 (x : nat) (p : Prop) : (term1060 x p) = p.
Proof. exact (@lem4307459 nat x p). Qed.
Lemma lem4307461 {A B : Type'} (s : A -> Prop) : (term1048 A B s) = (term1061 A B s).
Proof. exact (@lem4307460 (@CARD A s) (term1061 A B s)). Qed.
Lemma lem4307627 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4307628 {A B : Type'} (s : A -> Prop) : (term1062 A B s) = (term1063 A B s).
Proof. exact (MK_COMB (@lem4307627) (@lem4307461 A B s)). Qed.
Lemma lem4307644 {A : Type'} (s : A -> Prop) (m : nat) (h1 : (term822 A s) = m) : m = (term822 A s).
Proof. exact (SYM (@lem4306821 A s m h1)). Qed.
Lemma lem4307645 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem4307646 {A : Type'} (s : A -> Prop) (m : nat) (h1 : (term822 A s) = m) : (Nat.mul m) = (term1064 A s).
Proof. exact (MK_COMB (@lem4307645) (@lem4307644 A s m h1)). Qed.
Lemma lem4307647 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem4307648 {A : Type'} (n : nat) (s : A -> Prop) (m : nat) (h1 : (term822 A s) = m) : (Nat.mul m n) = (term1065 A s n).
Proof. exact (MK_COMB (@lem4307646 A s m h1) (@lem4307647 n)). Qed.
Lemma lem4307650 (m : nat) (n : nat) : (term1057 m n) = (term1058 m n).
Proof. exact (EQ_MP (@lem4307427 m n) (@lem4307426 m n)). Qed.
Lemma lem4307651 {A : Type'} (s : A -> Prop) (n : nat) : (term1065 A s n) = (term1066 A s n).
Proof. exact (@lem4307650 (@CARD A s) n). Qed.
Lemma lem4307652 {A : Type'} (n : nat) (s : A -> Prop) (m : nat) (h1 : (term822 A s) = m) : (Nat.mul m n) = (term1066 A s n).
Proof. exact (TRANS (@lem4307648 A n s m h1) (@lem4307651 A s n)). Qed.
Lemma lem4307653 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) : (term884 A B x s t) = (term884 A B x s t).
Proof. exact (eq_refl (term884 A B x s t)). Qed.
Lemma lem4307654 {A B : Type'} (x : A) (t : type1413 A B) (n : nat) (s : A -> Prop) (m : nat) (h1 : (term822 A s) = m) : (term885 A B x s t m n) = (term1067 A B x t s n).
Proof. exact (MK_COMB (@lem4307653 A B x s t) (@lem4307652 A n s m h1)). Qed.
Lemma lem4307655 {A B : Type'} (x : A) (t : type1413 A B) (n : nat) (s : A -> Prop) (m : nat) (h1 : (term822 A s) = m) : (term1068 A B x s t m n) = (term1069 A B x t s n).
Proof. exact (MK_COMB (@lem4307628 A B s) (@lem4307654 A B x t n s m h1)). Qed.
Lemma lem4307658 {A B : Type'} (x : A) (t : type1413 A B) (n : nat) (s : A -> Prop) (m : nat) (h1 : (term822 A s) = m) : (term1069 A B x t s n) = (term1068 A B x s t m n).
Proof. exact (SYM (@lem4307655 A B x t n s m h1)). Qed.
Lemma lem4307659 {A B : Type'} (s : A -> Prop) (h1 : term1061 A B s) : term1061 A B s.
Proof. exact (h1). Qed.
Lemma lem4307661 {_103141 _103145 : Type'} (s : _103145 -> Prop) (t : type1470 _103141 _103145) (a : _103145) : (term51 _103141 _103145 a s t) = (term52 _103141 _103145 s t a).
Proof. exact (EQ_MP (@lem4292951 _103141 _103145 s t a) (@lem4295627 _103141 _103145 s t a)). Qed.
Lemma lem4307662 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (a : A) : (term882 A B a s t) = (term1070 A B s t a).
Proof. exact (@lem4307661 B A s t a). Qed.
Lemma lem4307663 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : A) : (term882 A B x s t) = (term1070 A B s t x).
Proof. exact (@lem4307662 A B s t x). Qed.
Lemma lem4307674 {A B : Type'} : (@HAS_SIZE (prod A B)) = (@HAS_SIZE (prod A B)).
Proof. exact (eq_refl (@HAS_SIZE (prod A B))). Qed.
Lemma lem4307675 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : A) : (term884 A B x s t) = (term1071 A B s t x).
Proof. exact (MK_COMB (@lem4307674 A B) (@lem4307663 A B s t x)). Qed.
Lemma lem4307676 {A : Type'} (s : A -> Prop) (n : nat) : (term1066 A s n) = (term1066 A s n).
Proof. exact (eq_refl (term1066 A s n)). Qed.
Lemma lem4307677 {A B : Type'} (t : type1413 A B) (x : A) (s : A -> Prop) (n : nat) : (term1067 A B x t s n) = (term1072 A B t x s n).
Proof. exact (MK_COMB (@lem4307675 A B s t x) (@lem4307676 A s n)). Qed.
Lemma lem4307678 {A B : Type'} (x : A) (t : type1413 A B) (s : A -> Prop) (n : nat) : (term1072 A B t x s n) = (term1067 A B x t s n).
Proof. exact (SYM (@lem4307677 A B t x s n)). Qed.
Lemma lem4307680 {_100197 : Type'} (s : _100197 -> Prop) (t : _100197 -> Prop) (m : nat) (n : nat) : term38 _100197 s t m n.
Proof. exact (EQ_MP (@lem4292899 _100197 s t m n) (@lem4292898 _100197 s t m n)). Qed.
Lemma lem4307681 {A B : Type'} (s : type1210 A B) (t : type1210 A B) (m : nat) (n : nat) : term1073 A B s t m n.
Proof. exact (@lem4307680 (prod A B) s t m n). Qed.
Lemma lem4307682 {A B : Type'} (t : type1413 A B) (x : A) (s : A -> Prop) (n : nat) : term1074 A B t x s n.
Proof. exact (@lem4307681 A B (term1075 A B s t) (term1076 A B t x) (term1077 A s n) n). Qed.
Lemma lem4307683 {A B : Type'} (x : A) : term1078 A B x.
Proof. exact (@lem47438 A B x). Qed.
Lemma lem4307684 {A B : Type'} (x : A) : (term1078 A B x) = (term1079 A B x).
Proof. exact (eq_refl (term1078 A B x)). Qed.
Lemma lem4307685 {A B : Type'} (x : A) : term1079 A B x.
Proof. exact (EQ_MP (@lem4307684 A B x) (@lem4307683 A B x)). Qed.
Lemma lem4307686 {A B : Type'} (x : A) (y : B) : term1080 A B x y.
Proof. exact (@lem4307685 A B x y). Qed.
Lemma lem4307687 {A B : Type'} (x : A) (y : B) : (term1080 A B x y) = (term1081 A B x y).
Proof. exact (eq_refl (term1080 A B x y)). Qed.
Lemma lem4307688 {A B : Type'} (x : A) (y : B) : term1081 A B x y.
Proof. exact (EQ_MP (@lem4307687 A B x y) (@lem4307686 A B x y)). Qed.
Lemma lem4307689 {A B : Type'} (x : A) (y : B) (a : A) : term1082 A B x y a.
Proof. exact (@lem4307688 A B x y a). Qed.
Lemma lem4307690 {A B : Type'} (x : A) (a : A) (y : B) : (term1082 A B x y a) = (term1083 A B x a y).
Proof. exact (eq_refl (term1082 A B x y a)). Qed.
Lemma lem4307691 {A B : Type'} (x : A) (a : A) (y : B) : term1083 A B x a y.
Proof. exact (EQ_MP (@lem4307690 A B x a y) (@lem4307689 A B x y a)). Qed.
Lemma lem4307692 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : term1084 A B x a y b.
Proof. exact (@lem4307691 A B x a y b). Qed.
Lemma lem4307693 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (term1084 A B x a y b) = (((@pair A B x y) = (@pair A B a b)) = (term1085 A B x a y b)).
Proof. exact (eq_refl (term1084 A B x a y b)). Qed.
Lemma lem4307695 {A B : Type'} (f : A -> B) : term1086 A B f.
Proof. exact (@lem4004559 A B f). Qed.
Lemma lem4307696 {A B : Type'} (f : A -> B) : (term1086 A B f) = (term1087 A B f).
Proof. exact (eq_refl (term1086 A B f)). Qed.
Lemma lem4307697 {A B : Type'} (f : A -> B) : term1087 A B f.
Proof. exact (EQ_MP (@lem4307696 A B f) (@lem4307695 A B f)). Qed.
Lemma lem4307698 {A B : Type'} (f : A -> B) (s : A -> Prop) : term1088 A B f s.
Proof. exact (@lem4307697 A B f s). Qed.
Lemma lem4307699 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term1088 A B f s) = (term1089 A B f s).
Proof. exact (eq_refl (term1088 A B f s)). Qed.
Lemma lem4307700 {A B : Type'} (f : A -> B) (s : A -> Prop) : term1089 A B f s.
Proof. exact (EQ_MP (@lem4307699 A B f s) (@lem4307698 A B f s)). Qed.
Lemma lem4307701 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : term1090 A B f s n.
Proof. exact (@lem4307700 A B f s n). Qed.
Lemma lem4307702 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term1090 A B f s n) = (term1091 A B f s n).
Proof. exact (eq_refl (term1090 A B f s n)). Qed.
Lemma lem4307703 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : term1091 A B f s n.
Proof. exact (EQ_MP (@lem4307702 A B f s n) (@lem4307701 A B f s n)). Qed.
Lemma lem4307704 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term1092 A B f s n) : term1092 A B f s n.
Proof. exact (h1). Qed.
Lemma lem4307705 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term1092 A B f s n) : term1093 A B f s n.
Proof. exact (@lem4307703 A B f s n (@lem4307704 A B f s n h1)). Qed.
Lemma lem4307706 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : (term1093 A B f s n) = ((term1093 A B f s n) = True).
Proof. exact (@lem7 (term1093 A B f s n)). Qed.
Lemma lem4307707 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) (h1 : term1092 A B f s n) : (term1093 A B f s n) = True.
Proof. exact (EQ_MP (@lem4307706 A B f s n) (@lem4307705 A B f s n h1)). Qed.
Lemma lem4307717 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) : (term742 A B t x n) = ((term742 A B t x n) = True).
Proof. exact (@lem7 (term742 A B t x n)). Qed.
Lemma lem4307719 {A B : Type'} (x' : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term581 A B s t n) : term988 A B s t n x'.
Proof. exact (@lem4307406 A B s t n h1 x'). Qed.
Lemma lem4307720 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x' : A) (n : nat) : (term988 A B s t n x') = (term989 A B s t x' n).
Proof. exact (eq_refl (term988 A B s t n x')). Qed.
Lemma lem4307721 {A B : Type'} (x' : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term581 A B s t n) : term989 A B s t x' n.
Proof. exact (EQ_MP (@lem4307720 A B s t x' n) (@lem4307719 A B x' s t n h1)). Qed.
Lemma lem4307722 {A : Type'} (x' : A) (s : A -> Prop) (h1 : @IN A x' s) : @IN A x' s.
Proof. exact (h1). Qed.
Lemma lem4307723 {A B : Type'} (t : type1413 A B) (n : nat) (x' : A) (s : A -> Prop) (h1 : term581 A B s t n) (h2 : @IN A x' s) : term742 A B t x' n.
Proof. exact (@lem4307721 A B x' s t n h1 (@lem4307722 A x' s h2)). Qed.
Lemma lem4307724 {A B : Type'} (t : type1413 A B) (x' : A) (n : nat) : (term742 A B t x' n) = ((term742 A B t x' n) = True).
Proof. exact (@lem7 (term742 A B t x' n)). Qed.
Lemma lem4307725 {A B : Type'} (t : type1413 A B) (n : nat) (x' : A) (s : A -> Prop) (h1 : term581 A B s t n) (h2 : @IN A x' s) : (term742 A B t x' n) = True.
Proof. exact (EQ_MP (@lem4307724 A B t x' n) (@lem4307723 A B t n x' s h1 h2)). Qed.
Lemma lem4307731 {A B : Type'} (t : type1413 A B) (s : A -> Prop) (h1 : term1061 A B s) : term1094 A B s t.
Proof. exact (@lem4307659 A B s h1 t). Qed.
Lemma lem4307732 {A B : Type'} (t : type1413 A B) (s : A -> Prop) : (term1094 A B s t) = (term1095 A B t s).
Proof. exact (eq_refl (term1094 A B s t)). Qed.
Lemma lem4307733 {A B : Type'} (t : type1413 A B) (s : A -> Prop) (h1 : term1061 A B s) : term1095 A B t s.
Proof. exact (EQ_MP (@lem4307732 A B t s) (@lem4307731 A B t s h1)). Qed.
Lemma lem4307734 {A B : Type'} (t : type1413 A B) (n : nat) (s : A -> Prop) (h1 : term1061 A B s) : term1096 A B t s n.
Proof. exact (@lem4307733 A B t s h1 n). Qed.
Lemma lem4307735 {A B : Type'} (t : type1413 A B) (s : A -> Prop) (n : nat) : (term1096 A B t s n) = (term1097 A B t s n).
Proof. exact (eq_refl (term1096 A B t s n)). Qed.
Lemma lem4307736 {A B : Type'} (t : type1413 A B) (n : nat) (s : A -> Prop) (h1 : term1061 A B s) : term1097 A B t s n.
Proof. exact (EQ_MP (@lem4307735 A B t s n) (@lem4307734 A B t n s h1)). Qed.
Lemma lem4307737 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term581 A B s t n) : term581 A B s t n.
Proof. exact (h1). Qed.
Lemma lem4307738 {A B : Type'} (t : type1413 A B) (n : nat) (s : A -> Prop) (h1 : term581 A B s t n) (h2 : term1061 A B s) : term1098 A B t s n.
Proof. exact (@lem4307736 A B t n s h2 (@lem4307737 A B s t n h1)). Qed.
Lemma lem4307739 {A B : Type'} (t : type1413 A B) (s : A -> Prop) (n : nat) : (term1098 A B t s n) = ((term1098 A B t s n) = True).
Proof. exact (@lem7 (term1098 A B t s n)). Qed.
Lemma lem4307740 {A B : Type'} (t : type1413 A B) (n : nat) (s : A -> Prop) (h1 : term581 A B s t n) (h2 : term1061 A B s) : (term1098 A B t s n) = True.
Proof. exact (EQ_MP (@lem4307739 A B t s n) (@lem4307738 A B t n s h1 h2)). Qed.
Lemma lem4307749 {A B : Type'} (t : type1413 A B) (n : nat) (s : A -> Prop) (h1 : term1061 A B s) : term1099 A B t s n.
Proof. exact (fun h0 : term581 A B s t n => @lem4307740 A B t n s h0 h1). Qed.
Lemma lem4307750 {A B : Type'} (t : type1413 A B) (n : nat) (s : A -> Prop) (h1 : term1061 A B s) : term1099 A B t s n.
Proof. exact (@lem4307749 A B t n s h1). Qed.
Lemma lem4307758 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term721 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4307759 (p : Prop) (q : Prop) (p' : Prop) : term722 p q p'.
Proof. exact (fun q' : Prop => @lem4307758 p q p' q'). Qed.
Lemma lem4307760 (p : Prop) (q : Prop) : term723 p q.
Proof. exact (fun p' : Prop => @lem4307759 p q p'). Qed.
Lemma lem4307761 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x' : A) (n : nat) : term1100 A B s t x' n.
Proof. exact (@lem4307760 (@IN A x' s) (term742 A B t x' n)). Qed.
Lemma lem4307762 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x' : A) (n : nat) (p' : Prop) : term1101 A B s t x' n p'.
Proof. exact (@lem4307761 A B s t x' n p'). Qed.
Lemma lem4307763 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x' : A) (n : nat) (p' : Prop) : (term1101 A B s t x' n p') = (term1102 A B s t x' n p').
Proof. exact (eq_refl (term1101 A B s t x' n p')). Qed.
Lemma lem4307764 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x' : A) (n : nat) (p' : Prop) : term1102 A B s t x' n p'.
Proof. exact (EQ_MP (@lem4307763 A B s t x' n p') (@lem4307762 A B s t x' n p')). Qed.
Lemma lem4307765 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x' : A) (n : nat) (p' : Prop) (q' : Prop) : term1103 A B s t x' n p' q'.
Proof. exact (@lem4307764 A B s t x' n p' q'). Qed.
Lemma lem4307766 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x' : A) (n : nat) (p' : Prop) (q' : Prop) : (term1103 A B s t x' n p' q') = (term1104 A B s t x' n p' q').
Proof. exact (eq_refl (term1103 A B s t x' n p' q')). Qed.
Lemma lem4307767 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x' : A) (n : nat) (p' : Prop) (q' : Prop) : term1104 A B s t x' n p' q'.
Proof. exact (EQ_MP (@lem4307766 A B s t x' n p' q') (@lem4307765 A B s t x' n p' q')). Qed.
Lemma lem4307768 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = (@IN A x' s).
Proof. exact (eq_refl (@IN A x' s)). Qed.
Lemma lem4307769 {A B : Type'} (t : type1413 A B) (n : nat) (x' : A) (s : A -> Prop) (q' : Prop) : term1105 A B t n x' s q'.
Proof. exact (@lem4307767 A B s t x' n (@IN A x' s) q'). Qed.
Lemma lem4307770 {A B : Type'} (t : type1413 A B) (n : nat) (x' : A) (s : A -> Prop) (q' : Prop) : term1106 A B t n x' s q'.
Proof. exact (@lem4307769 A B t n x' s q' (@lem4307768 A x' s)). Qed.
Lemma lem4307771 {A : Type'} (x' : A) (s : A -> Prop) (h1 : @IN A x' s) : @IN A x' s.
Proof. exact (h1). Qed.
Lemma lem4307772 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = ((@IN A x' s) = True).
Proof. exact (@lem7 (@IN A x' s)). Qed.
Lemma lem4307775 {A B : Type'} (x' : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term581 A B s t n) : term1107 A B s t x' n.
Proof. exact (fun h0 : @IN A x' s => @lem4307725 A B t n x' s h1 h0). Qed.
Lemma lem4307776 {A B : Type'} (x' : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term581 A B s t n) : term1107 A B s t x' n.
Proof. exact (@lem4307775 A B x' s t n h1). Qed.
Lemma lem4307778 {A : Type'} (x' : A) (s : A -> Prop) (h1 : @IN A x' s) : (@IN A x' s) = True.
Proof. exact (EQ_MP (@lem4307772 A x' s) (@lem4307771 A x' s h1)). Qed.
Lemma lem4307779 {A : Type'} (x' : A) (s : A -> Prop) (h1 : @IN A x' s) : True = (@IN A x' s).
Proof. exact (SYM (@lem4307778 A x' s h1)). Qed.
Lemma lem4307780 {A : Type'} (x' : A) (s : A -> Prop) (h1 : @IN A x' s) : @IN A x' s.
Proof. exact (EQ_MP (@lem4307779 A x' s h1) (@lem0)). Qed.
Lemma lem4307781 {A B : Type'} (t : type1413 A B) (n : nat) (x' : A) (s : A -> Prop) (h1 : term581 A B s t n) (h2 : @IN A x' s) : (term742 A B t x' n) = True.
Proof. exact (@lem4307776 A B x' s t n h1 (@lem4307780 A x' s h2)). Qed.
Lemma lem4307782 {A B : Type'} (x' : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term581 A B s t n) : term1107 A B s t x' n.
Proof. exact (fun h0 : @IN A x' s => @lem4307781 A B t n x' s h1 h0). Qed.
Lemma lem4307783 {A B : Type'} (t : type1413 A B) (n : nat) (x' : A) (s : A -> Prop) : term1108 A B t n x' s.
Proof. exact (@lem4307770 A B t n x' s True). Qed.
Lemma lem4307784 {A B : Type'} (x' : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term581 A B s t n) : (term989 A B s t x' n) = (term1109 A x' s).
Proof. exact (@lem4307783 A B t n x' s (@lem4307782 A B x' s t n h1)). Qed.
Lemma lem4307786 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4307787 {A : Type'} (x' : A) (s : A -> Prop) : (term1109 A x' s) = True.
Proof. exact (@lem4307786 (@IN A x' s)). Qed.
Lemma lem4307788 {A B : Type'} (x' : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term581 A B s t n) : (term989 A B s t x' n) = True.
Proof. exact (TRANS (@lem4307784 A B x' s t n h1) (@lem4307787 A x' s)). Qed.
Lemma lem4307789 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term581 A B s t n) : (term983 A B s t n) = (term754 A).
Proof. exact (fun_ext (fun x' : A => @lem4307788 A B x' s t n h1)). Qed.
Lemma lem4307790 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4307791 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term581 A B s t n) : (term581 A B s t n) = (term755 A).
Proof. exact (MK_COMB (@lem4307790 A) (@lem4307789 A B s t n h1)). Qed.
Lemma lem4307793 {A : Type'} (t : Prop) : (term756 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4307794 {A : Type'} (t : Prop) : (term756 A t) = t.
Proof. exact (@lem4307793 A t). Qed.
Lemma lem4307795 {A : Type'} : (term755 A) = True.
Proof. exact (@lem4307794 A True). Qed.
Lemma lem4307796 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term581 A B s t n) : (term581 A B s t n) = True.
Proof. exact (TRANS (@lem4307791 A B s t n h1) (@lem4307795 A)). Qed.
Lemma lem4307797 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term581 A B s t n) : True = (term581 A B s t n).
Proof. exact (SYM (@lem4307796 A B s t n h1)). Qed.
Lemma lem4307798 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term581 A B s t n) : term581 A B s t n.
Proof. exact (EQ_MP (@lem4307797 A B s t n h1) (@lem0)). Qed.
Lemma lem4307799 {A B : Type'} (t : type1413 A B) (n : nat) (s : A -> Prop) (h1 : term581 A B s t n) (h2 : term1061 A B s) : (term1098 A B t s n) = True.
Proof. exact (@lem4307750 A B t n s h2 (@lem4307798 A B s t n h1)). Qed.
Lemma lem4307800 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4307801 {A B : Type'} (t : type1413 A B) (n : nat) (s : A -> Prop) (h1 : term581 A B s t n) (h2 : term1061 A B s) : (term1110 A B t s n) = (and True).
Proof. exact (MK_COMB (@lem4307800) (@lem4307799 A B t n s h1 h2)). Qed.
Lemma lem4307805 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : term1111 A B f s n.
Proof. exact (fun h0 : term1092 A B f s n => @lem4307707 A B f s n h0). Qed.
Lemma lem4307806 {A B : Type'} (f : type1478 A B) (s : B -> Prop) (n : nat) : term1112 A B f s n.
Proof. exact (@lem4307805 B (prod A B) f s n). Qed.
Lemma lem4307807 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) : term1113 A B t x n.
Proof. exact (@lem4307806 A B (term1114 A B x) (t x) n). Qed.
Lemma lem4307821 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term721 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4307822 (p : Prop) (q : Prop) (p' : Prop) : term722 p q p'.
Proof. exact (fun q' : Prop => @lem4307821 p q p' q'). Qed.
Lemma lem4307823 (p : Prop) (q : Prop) : term723 p q.
Proof. exact (fun p' : Prop => @lem4307822 p q p'). Qed.
Lemma lem4307824 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) : term1115 A B t x x' y.
Proof. exact (@lem4307823 (term1116 A B t x' x y) (x' = y)). Qed.
Lemma lem4307825 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) (p' : Prop) : term1117 A B t x x' y p'.
Proof. exact (@lem4307824 A B t x x' y p'). Qed.
Lemma lem4307826 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) (p' : Prop) : (term1117 A B t x x' y p') = (term1118 A B t x x' y p').
Proof. exact (eq_refl (term1117 A B t x x' y p')). Qed.
Lemma lem4307827 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) (p' : Prop) : term1118 A B t x x' y p'.
Proof. exact (EQ_MP (@lem4307826 A B t x x' y p') (@lem4307825 A B t x x' y p')). Qed.
Lemma lem4307828 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) (p' : Prop) (q' : Prop) : term1119 A B t x x' y p' q'.
Proof. exact (@lem4307827 A B t x x' y p' q'). Qed.
Lemma lem4307829 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) (p' : Prop) (q' : Prop) : (term1119 A B t x x' y p' q') = (term1120 A B t x x' y p' q').
Proof. exact (eq_refl (term1119 A B t x x' y p' q')). Qed.
Lemma lem4307830 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) (p' : Prop) (q' : Prop) : term1120 A B t x x' y p' q'.
Proof. exact (EQ_MP (@lem4307829 A B t x x' y p' q') (@lem4307828 A B t x x' y p' q')). Qed.
Lemma lem4307838 {A B : Type'} (f : A -> B) (y : A) : (term68 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4307839 {A B : Type'} (f : type1478 A B) (y : B) : (term1121 A B f y) = (f y).
Proof. exact (@lem4307838 B (prod A B) f y). Qed.
Lemma lem4307840 {A B : Type'} (x : A) (x' : B) : (term1122 A B x x') = (term1123 A B x x').
Proof. exact (@lem4307839 A B (term1114 A B x) x'). Qed.
Lemma lem4307841 {A B : Type'} (x : A) (y : B) : (term1123 A B x y) = (@pair A B x y).
Proof. exact (eq_refl (term1123 A B x y)). Qed.
Lemma lem4307842 {A B : Type'} (x : A) : (term1124 A B x) = (term1114 A B x).
Proof. exact (fun_ext (fun y : B => @lem4307841 A B x y)). Qed.
Lemma lem4307843 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4307844 {A B : Type'} (x : A) (x' : B) : (term1122 A B x x') = (term1123 A B x x').
Proof. exact (MK_COMB (@lem4307842 A B x) (@lem4307843 B x')). Qed.
Lemma lem4307845 {A B : Type'} : (@eq (prod A B)) = (@eq (prod A B)).
Proof. exact (eq_refl (@eq (prod A B))). Qed.
Lemma lem4307846 {A B : Type'} (x : A) (x' : B) : (term1125 A B x x') = (term1126 A B x x').
Proof. exact (MK_COMB (@lem4307845 A B) (@lem4307844 A B x x')). Qed.
Lemma lem4307847 {A B : Type'} (x : A) (x' : B) : (term1123 A B x x') = (@pair A B x x').
Proof. exact (eq_refl (term1123 A B x x')). Qed.
Lemma lem4307848 {A B : Type'} (x : A) (x' : B) : ((term1122 A B x x') = (term1123 A B x x')) = ((term1123 A B x x') = (@pair A B x x')).
Proof. exact (MK_COMB (@lem4307846 A B x x') (@lem4307847 A B x x')). Qed.
Lemma lem4307849 {A B : Type'} (x : A) (x' : B) : (term1123 A B x x') = (@pair A B x x').
Proof. exact (EQ_MP (@lem4307848 A B x x') (@lem4307840 A B x x')). Qed.
Lemma lem4307850 {A B : Type'} : (@eq (prod A B)) = (@eq (prod A B)).
Proof. exact (eq_refl (@eq (prod A B))). Qed.
Lemma lem4307851 {A B : Type'} (x : A) (x' : B) : (term1126 A B x x') = (term1127 A B x x').
Proof. exact (MK_COMB (@lem4307850 A B) (@lem4307849 A B x x')). Qed.
Lemma lem4307853 {A B : Type'} (f : A -> B) (y : A) : (term68 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4307854 {A B : Type'} (f : type1478 A B) (y : B) : (term1121 A B f y) = (f y).
Proof. exact (@lem4307853 B (prod A B) f y). Qed.
Lemma lem4307855 {A B : Type'} (x : A) (y : B) : (term1122 A B x y) = (term1123 A B x y).
Proof. exact (@lem4307854 A B (term1114 A B x) y). Qed.
Lemma lem4307856 {A B : Type'} (x : A) (y : B) : (term1123 A B x y) = (@pair A B x y).
Proof. exact (eq_refl (term1123 A B x y)). Qed.
Lemma lem4307857 {A B : Type'} (x : A) : (term1124 A B x) = (term1114 A B x).
Proof. exact (fun_ext (fun y : B => @lem4307856 A B x y)). Qed.
Lemma lem4307858 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4307859 {A B : Type'} (x : A) (y : B) : (term1122 A B x y) = (term1123 A B x y).
Proof. exact (MK_COMB (@lem4307857 A B x) (@lem4307858 B y)). Qed.
Lemma lem4307860 {A B : Type'} : (@eq (prod A B)) = (@eq (prod A B)).
Proof. exact (eq_refl (@eq (prod A B))). Qed.
Lemma lem4307861 {A B : Type'} (x : A) (y : B) : (term1125 A B x y) = (term1126 A B x y).
Proof. exact (MK_COMB (@lem4307860 A B) (@lem4307859 A B x y)). Qed.
Lemma lem4307862 {A B : Type'} (x : A) (y : B) : (term1123 A B x y) = (@pair A B x y).
Proof. exact (eq_refl (term1123 A B x y)). Qed.
Lemma lem4307863 {A B : Type'} (x : A) (y : B) : ((term1122 A B x y) = (term1123 A B x y)) = ((term1123 A B x y) = (@pair A B x y)).
Proof. exact (MK_COMB (@lem4307861 A B x y) (@lem4307862 A B x y)). Qed.
Lemma lem4307864 {A B : Type'} (x : A) (y : B) : (term1123 A B x y) = (@pair A B x y).
Proof. exact (EQ_MP (@lem4307863 A B x y) (@lem4307855 A B x y)). Qed.
Lemma lem4307865 {A B : Type'} (x : B) (x' : A) (y : B) : ((term1123 A B x' x) = (term1123 A B x' y)) = ((@pair A B x' x) = (@pair A B x' y)).
Proof. exact (MK_COMB (@lem4307851 A B x' x) (@lem4307864 A B x' y)). Qed.
Lemma lem4307867 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : ((@pair A B x y) = (@pair A B a b)) = (term1085 A B x a y b).
Proof. exact (EQ_MP (@lem4307693 A B x a y b) (@lem4307692 A B x a y b)). Qed.
Lemma lem4307868 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : ((@pair A B x y) = (@pair A B a b)) = (term1085 A B x a y b).
Proof. exact (@lem4307867 A B x a y b). Qed.
Lemma lem4307869 {A B : Type'} (x : A) (x' : B) (y : B) : ((@pair A B x x') = (@pair A B x y)) = (term1128 A B x x' y).
Proof. exact (@lem4307868 A B x x x' y). Qed.
Lemma lem4307873 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4307874 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem4307873 A x). Qed.
Lemma lem4307875 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4307876 {A : Type'} (x : A) : (term1129 A x) = (and True).
Proof. exact (MK_COMB (@lem4307875) (@lem4307874 A x)). Qed.
Lemma lem4307879 {B : Type'} (x : B) (y : B) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4307880 {A B : Type'} (x : A) (x' : B) (y : B) : (term1128 A B x x' y) = (term1130 B x' y).
Proof. exact (MK_COMB (@lem4307876 A x) (@lem4307879 B x' y)). Qed.
Lemma lem4307882 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4307883 {B : Type'} (x : B) (y : B) : (term1130 B x y) = (x = y).
Proof. exact (@lem4307882 (x = y)). Qed.
Lemma lem4307886 {A B : Type'} (x : A) (x' : B) (y : B) : (term1128 A B x x' y) = (x' = y).
Proof. exact (TRANS (@lem4307880 A B x x' y) (@lem4307883 B x' y)). Qed.
Lemma lem4307887 {A B : Type'} (x : A) (x' : B) (y : B) : ((@pair A B x x') = (@pair A B x y)) = (x' = y).
Proof. exact (TRANS (@lem4307869 A B x x' y) (@lem4307886 A B x x' y)). Qed.
Lemma lem4307888 {A B : Type'} (x : A) (x' : B) (y : B) : ((term1123 A B x x') = (term1123 A B x y)) = (x' = y).
Proof. exact (TRANS (@lem4307865 A B x' x y) (@lem4307887 A B x x' y)). Qed.
Lemma lem4307889 {A B : Type'} (y : B) (t : type1413 A B) (x : A) : (term1131 A B y t x) = (term1131 A B y t x).
Proof. exact (eq_refl (term1131 A B y t x)). Qed.
Lemma lem4307890 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) : (term1132 A B t x' x y) = (term1133 A B t x x' y).
Proof. exact (MK_COMB (@lem4307889 A B y t x) (@lem4307888 A B x x' y)). Qed.
Lemma lem4307895 {A B : Type'} (x : B) (t : type1413 A B) (x' : A) : (term1131 A B x t x') = (term1131 A B x t x').
Proof. exact (eq_refl (term1131 A B x t x')). Qed.
Lemma lem4307896 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) : (term1116 A B t x' x y) = (term1134 A B t x x' y).
Proof. exact (MK_COMB (@lem4307895 A B x' t x) (@lem4307890 A B t x x' y)). Qed.
Lemma lem4307903 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) (q' : Prop) : term1135 A B t x x' y q'.
Proof. exact (@lem4307830 A B t x x' y (term1134 A B t x x' y) q'). Qed.
Lemma lem4307904 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) (q' : Prop) : term1136 A B t x x' y q'.
Proof. exact (@lem4307903 A B t x x' y q' (@lem4307896 A B t x x' y)). Qed.
Lemma lem4307905 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) (h1 : term1134 A B t x x' y) : term1134 A B t x x' y.
Proof. exact (h1). Qed.
Lemma lem4307906 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) (h1 : term1134 A B t x x' y) : term1133 A B t x x' y.
Proof. exact (proj2 (@lem4307905 A B t x x' y h1)). Qed.
Lemma lem4307917 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) (h1 : term1134 A B t x x' y) : x' = y.
Proof. exact (proj2 (@lem4307906 A B t x x' y h1)). Qed.
Lemma lem4307918 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4307919 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) (h1 : term1134 A B t x x' y) : (@eq B x') = (@eq B y).
Proof. exact (MK_COMB (@lem4307918 B) (@lem4307917 A B t x x' y h1)). Qed.
Lemma lem4307920 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4307921 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) (h1 : term1134 A B t x x' y) : (x' = y) = (y = y).
Proof. exact (MK_COMB (@lem4307919 A B t x x' y h1) (@lem4307920 B y)). Qed.
Lemma lem4307923 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4307924 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem4307923 B x). Qed.
Lemma lem4307925 {B : Type'} (y : B) : (y = y) = True.
Proof. exact (@lem4307924 B y). Qed.
Lemma lem4307926 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) (h1 : term1134 A B t x x' y) : (x' = y) = True.
Proof. exact (TRANS (@lem4307921 A B t x x' y h1) (@lem4307925 B y)). Qed.
Lemma lem4307927 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) : term1137 A B t x x' y.
Proof. exact (fun h0 : term1134 A B t x x' y => @lem4307926 A B t x x' y h0). Qed.
Lemma lem4307928 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) : term1138 A B t x x' y.
Proof. exact (@lem4307904 A B t x x' y True). Qed.
Lemma lem4307929 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) : (term1139 A B t x x' y) = (term1140 A B t x x' y).
Proof. exact (@lem4307928 A B t x x' y (@lem4307927 A B t x x' y)). Qed.
Lemma lem4307931 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4307932 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) : (term1140 A B t x x' y) = True.
Proof. exact (@lem4307931 (term1134 A B t x x' y)). Qed.
Lemma lem4307933 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) (y : B) : (term1139 A B t x x' y) = True.
Proof. exact (TRANS (@lem4307929 A B t x x' y) (@lem4307932 A B t x x' y)). Qed.
Lemma lem4307934 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) : (term1141 A B t x x') = (term754 B).
Proof. exact (fun_ext (fun y : B => @lem4307933 A B t x x' y)). Qed.
Lemma lem4307935 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4307936 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) : (term1142 A B t x x') = (term755 B).
Proof. exact (MK_COMB (@lem4307935 B) (@lem4307934 A B t x x')). Qed.
Lemma lem4307938 {A : Type'} (t : Prop) : (term756 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4307939 {B : Type'} (t : Prop) : (term756 B t) = t.
Proof. exact (@lem4307938 B t). Qed.
Lemma lem4307940 {B : Type'} : (term755 B) = True.
Proof. exact (@lem4307939 B True). Qed.
Lemma lem4307941 {A B : Type'} (t : type1413 A B) (x : A) (x' : B) : (term1142 A B t x x') = True.
Proof. exact (TRANS (@lem4307936 A B t x x') (@lem4307940 B)). Qed.
Lemma lem4307942 {A B : Type'} (t : type1413 A B) (x : A) : (term1143 A B t x) = (term754 B).
Proof. exact (fun_ext (fun x' : B => @lem4307941 A B t x x')). Qed.
Lemma lem4307943 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4307944 {A B : Type'} (t : type1413 A B) (x : A) : (term1144 A B t x) = (term755 B).
Proof. exact (MK_COMB (@lem4307943 B) (@lem4307942 A B t x)). Qed.
Lemma lem4307946 {A : Type'} (t : Prop) : (term756 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4307947 {B : Type'} (t : Prop) : (term756 B t) = t.
Proof. exact (@lem4307946 B t). Qed.
Lemma lem4307948 {B : Type'} : (term755 B) = True.
Proof. exact (@lem4307947 B True). Qed.
Lemma lem4307949 {A B : Type'} (t : type1413 A B) (x : A) : (term1144 A B t x) = True.
Proof. exact (TRANS (@lem4307944 A B t x) (@lem4307948 B)). Qed.
Lemma lem4307950 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4307951 {A B : Type'} (t : type1413 A B) (x : A) : (term1145 A B t x) = (and True).
Proof. exact (MK_COMB (@lem4307950) (@lem4307949 A B t x)). Qed.
Lemma lem4307953 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) (h1 : term742 A B t x n) : (term742 A B t x n) = True.
Proof. exact (EQ_MP (@lem4307717 A B t x n) (@lem4307407 A B t x n h1)). Qed.
Lemma lem4307954 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) (h1 : term742 A B t x n) : (term1146 A B t x n) = (True /\ True).
Proof. exact (MK_COMB (@lem4307951 A B t x) (@lem4307953 A B t x n h1)). Qed.
Lemma lem4307956 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4307957 : (True /\ True) = True.
Proof. exact (@lem4307956 True). Qed.
Lemma lem4307958 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) (h1 : term742 A B t x n) : (term1146 A B t x n) = True.
Proof. exact (TRANS (@lem4307954 A B t x n h1) (@lem4307957)). Qed.
Lemma lem4307959 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) (h1 : term742 A B t x n) : True = (term1146 A B t x n).
Proof. exact (SYM (@lem4307958 A B t x n h1)). Qed.
Lemma lem4307960 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) (h1 : term742 A B t x n) : term1146 A B t x n.
Proof. exact (EQ_MP (@lem4307959 A B t x n h1) (@lem0)). Qed.
Lemma lem4307961 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) (h1 : term742 A B t x n) : (term1147 A B t x n) = True.
Proof. exact (@lem4307807 A B t x n (@lem4307960 A B t x n h1)). Qed.
Lemma lem4307962 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4307963 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) (h1 : term742 A B t x n) : (term1148 A B t x n) = (and True).
Proof. exact (MK_COMB (@lem4307962) (@lem4307961 A B t x n h1)). Qed.
Lemma lem4307974 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : A) : (term1149 A B s t x) = (term1149 A B s t x).
Proof. exact (eq_refl (term1149 A B s t x)). Qed.
Lemma lem4307975 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : A) (n : nat) (h1 : term742 A B t x n) : (term1150 A B n s t x) = (term1151 A B s t x).
Proof. exact (MK_COMB (@lem4307963 A B t x n h1) (@lem4307974 A B s t x)). Qed.
Lemma lem4307977 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4307978 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : A) : (term1151 A B s t x) = (term1149 A B s t x).
Proof. exact (@lem4307977 (term1149 A B s t x)). Qed.
Lemma lem4307989 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : A) (n : nat) (h1 : term742 A B t x n) : (term1150 A B n s t x) = (term1149 A B s t x).
Proof. exact (TRANS (@lem4307975 A B s t x n h1) (@lem4307978 A B s t x)). Qed.
Lemma lem4307990 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : A) (n : nat) (h1 : term581 A B s t n) (h2 : term1061 A B s) (h3 : term742 A B t x n) : (term1152 A B n s t x) = (term1151 A B s t x).
Proof. exact (MK_COMB (@lem4307801 A B t n s h1 h2) (@lem4307989 A B s t x n h3)). Qed.
Lemma lem4307992 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4307993 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : A) : (term1151 A B s t x) = (term1149 A B s t x).
Proof. exact (@lem4307992 (term1149 A B s t x)). Qed.
Lemma lem4308004 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : A) (n : nat) (h1 : term581 A B s t n) (h2 : term1061 A B s) (h3 : term742 A B t x n) : (term1152 A B n s t x) = (term1149 A B s t x).
Proof. exact (TRANS (@lem4307990 A B s t x n h1 h2 h3) (@lem4307993 A B s t x)). Qed.
Lemma lem4308005 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : A) (n : nat) (h1 : term581 A B s t n) (h2 : term1061 A B s) (h3 : term742 A B t x n) : (term1149 A B s t x) = (term1152 A B n s t x).
Proof. exact (SYM (@lem4308004 A B s t x n h1 h2 h3)). Qed.
Lemma lem4308007 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (EQ_MP (@lem4292862 A s t) (@lem4292861 A s t)). Qed.
Lemma lem4308008 {A B : Type'} (s : type1210 A B) (t : type1210 A B) : (@DISJOINT (prod A B) s t) = ((@INTER (prod A B) s t) = (@EMPTY (prod A B))).
Proof. exact (@lem4308007 (prod A B) s t). Qed.
Lemma lem4308009 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : A) : (term1149 A B s t x) = ((term1153 A B s t x) = (@EMPTY (prod A B))).
Proof. exact (@lem4308008 A B (term1075 A B s t) (term1076 A B t x)). Qed.
Lemma lem4308013 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term6 A s t).
Proof. exact (EQ_MP (@lem4292800 A s t) (@lem4292799 A s t)). Qed.
Lemma lem4308014 {A B : Type'} (s : type1210 A B) (t : type1210 A B) : (s = t) = (term925 A B s t).
Proof. exact (@lem4308013 (prod A B) s t). Qed.
Lemma lem4308015 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : A) : ((term1153 A B s t x) = (@EMPTY (prod A B))) = (term1154 A B s t x).
Proof. exact (@lem4308014 A B (term1153 A B s t x) (@EMPTY (prod A B))). Qed.
Lemma lem4308020 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : A) : (term1149 A B s t x) = (term1154 A B s t x).
Proof. exact (TRANS (@lem4308009 A B s t x) (@lem4308015 A B s t x)). Qed.
Lemma lem4308026 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term12 A x s t) = (term13 A s x t).
Proof. exact (EQ_MP (@lem4292809 A s x t) (@lem4292808 A s t x)). Qed.
Lemma lem4308027 {A B : Type'} (s : type1210 A B) (x : prod A B) (t : type1210 A B) : (term1155 A B x s t) = (term1156 A B s x t).
Proof. exact (@lem4308026 (prod A B) s x t). Qed.
Lemma lem4308028 {A B : Type'} (s : A -> Prop) (x : prod A B) (t : type1413 A B) (x' : A) : (term1157 A B x s t x') = (term1158 A B s x t x').
Proof. exact (@lem4308027 A B (term1075 A B s t) x (term1076 A B t x')). Qed.
Lemma lem4308032 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term18 _83064 x P) = (term19 _83064 P x).
Proof. exact (EQ_MP (@lem4292847 _83064 P x) (@lem4292846 _83064 P x)). Qed.
Lemma lem4308033 {A B : Type'} (P : type914 A B) (x : prod A B) : (term927 A B x P) = (term928 A B P x).
Proof. exact (@lem4308032 (prod A B) P x). Qed.
Lemma lem4308034 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term1159 A B x s t) = (term1160 A B s t x).
Proof. exact (@lem4308033 A B (term1161 A B s t) x). Qed.
Lemma lem4308035 {A B : Type'} (GEN_PVAR_120 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1162 A B s t GEN_PVAR_120) = (term1163 A B GEN_PVAR_120 s t).
Proof. exact (eq_refl (term1162 A B s t GEN_PVAR_120)). Qed.
Lemma lem4308036 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term1164 A B s t) = (term1165 A B s t).
Proof. exact (fun_ext (fun GEN_PVAR_120 : prod A B => @lem4308035 A B GEN_PVAR_120 s t)). Qed.
Lemma lem4308037 {A B : Type'} : (@GSPEC (prod A B)) = (@GSPEC (prod A B)).
Proof. exact (eq_refl (@GSPEC (prod A B))). Qed.
Lemma lem4308038 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term1166 A B s t) = (term1075 A B s t).
Proof. exact (MK_COMB (@lem4308037 A B) (@lem4308036 A B s t)). Qed.
Lemma lem4308039 {A B : Type'} (x : prod A B) : (@IN (prod A B) x) = (@IN (prod A B) x).
Proof. exact (eq_refl (@IN (prod A B) x)). Qed.
Lemma lem4308040 {A B : Type'} (x : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1159 A B x s t) = (term1167 A B x s t).
Proof. exact (MK_COMB (@lem4308039 A B x) (@lem4308038 A B s t)). Qed.
Lemma lem4308041 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4308042 {A B : Type'} (x : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1168 A B x s t) = (term1169 A B x s t).
Proof. exact (MK_COMB (@lem4308041) (@lem4308040 A B x s t)). Qed.
Lemma lem4308043 {A B : Type'} (x : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1160 A B s t x) = (term1170 A B x s t).
Proof. exact (eq_refl (term1160 A B s t x)). Qed.
Lemma lem4308044 {A B : Type'} (x : prod A B) (s : A -> Prop) (t : type1413 A B) : ((term1159 A B x s t) = (term1160 A B s t x)) = ((term1167 A B x s t) = (term1170 A B x s t)).
Proof. exact (MK_COMB (@lem4308042 A B x s t) (@lem4308043 A B x s t)). Qed.
Lemma lem4308045 {A B : Type'} (x : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1167 A B x s t) = (term1170 A B x s t).
Proof. exact (EQ_MP (@lem4308044 A B x s t) (@lem4308034 A B s t x)). Qed.
Lemma lem4308059 {A B : Type'} (f : A -> B) (y : A) : (term68 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4308060 {A B : Type'} (f : type1532 A B) (y : Prop) : (term939 A B f y) = (f y).
Proof. exact (@lem4308059 Prop (type1210 A B) f y). Qed.
Lemma lem4308061 {A B : Type'} (x : prod A B) (s : A -> Prop) (y : B) (t : type1413 A B) (x' : A) : (term1171 A B x s y t x') = (term1172 A B x s y t x').
Proof. exact (@lem4308060 A B (term942 A B x) (term1173 A B s y t x')). Qed.
Lemma lem4308062 {A B : Type'} (p : Prop) (x : prod A B) : (term943 A B x p) = (term944 A B p x).
Proof. exact (eq_refl (term943 A B x p)). Qed.
Lemma lem4308063 {A B : Type'} (x : prod A B) : (term945 A B x) = (term942 A B x).
Proof. exact (fun_ext (fun p : Prop => @lem4308062 A B p x)). Qed.
Lemma lem4308064 {A B : Type'} (s : A -> Prop) (y : B) (t : type1413 A B) (x' : A) : (term1173 A B s y t x') = (term1173 A B s y t x').
Proof. exact (eq_refl (term1173 A B s y t x')). Qed.
Lemma lem4308065 {A B : Type'} (x : prod A B) (s : A -> Prop) (y : B) (t : type1413 A B) (x' : A) : (term1171 A B x s y t x') = (term1172 A B x s y t x').
Proof. exact (MK_COMB (@lem4308063 A B x) (@lem4308064 A B s y t x')). Qed.
Lemma lem4308066 {A B : Type'} : (@eq ((prod A B) -> Prop)) = (@eq ((prod A B) -> Prop)).
Proof. exact (eq_refl (@eq ((prod A B) -> Prop))). Qed.
Lemma lem4308067 {A B : Type'} (x : prod A B) (s : A -> Prop) (y : B) (t : type1413 A B) (x' : A) : (term1174 A B x s y t x') = (term1175 A B x s y t x').
Proof. exact (MK_COMB (@lem4308066 A B) (@lem4308065 A B x s y t x')). Qed.
Lemma lem4308068 {A B : Type'} (s : A -> Prop) (y : B) (t : type1413 A B) (x' : A) (x : prod A B) : (term1172 A B x s y t x') = (term1176 A B s y t x' x).
Proof. exact (eq_refl (term1172 A B x s y t x')). Qed.
Lemma lem4308069 {A B : Type'} (s : A -> Prop) (y : B) (t : type1413 A B) (x' : A) (x : prod A B) : ((term1171 A B x s y t x') = (term1172 A B x s y t x')) = ((term1172 A B x s y t x') = (term1176 A B s y t x' x)).
Proof. exact (MK_COMB (@lem4308067 A B x s y t x') (@lem4308068 A B s y t x' x)). Qed.
Lemma lem4308070 {A B : Type'} (s : A -> Prop) (y : B) (t : type1413 A B) (x' : A) (x : prod A B) : (term1172 A B x s y t x') = (term1176 A B s y t x' x).
Proof. exact (EQ_MP (@lem4308069 A B s y t x' x) (@lem4308061 A B x s y t x')). Qed.
Lemma lem4308079 {A B : Type'} (x' : A) (y : B) : (@pair A B x' y) = (@pair A B x' y).
Proof. exact (eq_refl (@pair A B x' y)). Qed.
Lemma lem4308080 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : (term1177 A B x s t x' y) = (term1178 A B s t x x' y).
Proof. exact (MK_COMB (@lem4308070 A B s y t x' x) (@lem4308079 A B x' y)). Qed.
Lemma lem4308082 {A B : Type'} (f : A -> B) (y : A) : (term68 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4308083 {A B : Type'} (f : type1210 A B) (y : prod A B) : (term953 A B f y) = (f y).
Proof. exact (@lem4308082 (prod A B) Prop f y). Qed.
Lemma lem4308084 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : (term1179 A B s t x x' y) = (term1178 A B s t x x' y).
Proof. exact (@lem4308083 A B (term1176 A B s y t x' x) (@pair A B x' y)). Qed.
Lemma lem4308085 {A B : Type'} (s : A -> Prop) (y : B) (t : type1413 A B) (x' : A) (x : prod A B) (t' : prod A B) : (term1180 A B s y t x' x t') = (term1181 A B s y t x' x t').
Proof. exact (eq_refl (term1180 A B s y t x' x t')). Qed.
Lemma lem4308086 {A B : Type'} (s : A -> Prop) (y : B) (t : type1413 A B) (x' : A) (x : prod A B) : (term1182 A B s y t x' x) = (term1176 A B s y t x' x).
Proof. exact (fun_ext (fun t' : prod A B => @lem4308085 A B s y t x' x t')). Qed.
Lemma lem4308087 {A B : Type'} (x' : A) (y : B) : (@pair A B x' y) = (@pair A B x' y).
Proof. exact (eq_refl (@pair A B x' y)). Qed.
Lemma lem4308088 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : (term1179 A B s t x x' y) = (term1178 A B s t x x' y).
Proof. exact (MK_COMB (@lem4308086 A B s y t x' x) (@lem4308087 A B x' y)). Qed.
Lemma lem4308089 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4308090 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : (term1183 A B s t x x' y) = (term1184 A B s t x x' y).
Proof. exact (MK_COMB (@lem4308089) (@lem4308088 A B s t x x' y)). Qed.
Lemma lem4308091 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : (term1178 A B s t x x' y) = (term1185 A B s t x x' y).
Proof. exact (eq_refl (term1178 A B s t x x' y)). Qed.
Lemma lem4308092 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : ((term1179 A B s t x x' y) = (term1178 A B s t x x' y)) = ((term1178 A B s t x x' y) = (term1185 A B s t x x' y)).
Proof. exact (MK_COMB (@lem4308090 A B s t x x' y) (@lem4308091 A B s t x x' y)). Qed.
Lemma lem4308093 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : (term1178 A B s t x x' y) = (term1185 A B s t x x' y).
Proof. exact (EQ_MP (@lem4308092 A B s t x x' y) (@lem4308084 A B s t x x' y)). Qed.
Lemma lem4308102 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : (term1177 A B x s t x' y) = (term1185 A B s t x x' y).
Proof. exact (TRANS (@lem4308080 A B s t x x' y) (@lem4308093 A B s t x x' y)). Qed.
Lemma lem4308103 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) : (term1186 A B x s t x') = (term1187 A B s t x x').
Proof. exact (fun_ext (fun y : B => @lem4308102 A B s t x x' y)). Qed.
Lemma lem4308104 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4308105 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) : (term1188 A B x s t x') = (term1189 A B s t x x').
Proof. exact (MK_COMB (@lem4308104 B) (@lem4308103 A B s t x x')). Qed.
Lemma lem4308112 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term1190 A B x s t) = (term1191 A B s t x).
Proof. exact (fun_ext (fun x' : A => @lem4308105 A B s t x x')). Qed.
Lemma lem4308113 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4308114 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term1170 A B x s t) = (term1192 A B s t x).
Proof. exact (MK_COMB (@lem4308113 A) (@lem4308112 A B s t x)). Qed.
Lemma lem4308121 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term1167 A B x s t) = (term1192 A B s t x).
Proof. exact (TRANS (@lem4308045 A B x s t) (@lem4308114 A B s t x)). Qed.
Lemma lem4308122 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4308123 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term1193 A B x s t) = (term1194 A B s t x).
Proof. exact (MK_COMB (@lem4308122) (@lem4308121 A B s t x)). Qed.
Lemma lem4308125 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term25 A B y f s) = (term26 A B y f s).
Proof. exact (EQ_MP (@lem4292856 A B y f s) (@lem4292855 A B y s f)). Qed.
Lemma lem4308126 {A B : Type'} (y : prod A B) (f : type1478 A B) (s : B -> Prop) : (term1195 A B y f s) = (term1196 A B y f s).
Proof. exact (@lem4308125 B (prod A B) y f s). Qed.
Lemma lem4308127 {A B : Type'} (x : prod A B) (t : type1413 A B) (x' : A) : (term1197 A B x t x') = (term1198 A B x t x').
Proof. exact (@lem4308126 A B x (term1114 A B x') (t x')). Qed.
Lemma lem4308141 {A B : Type'} (f : A -> B) (y : A) : (term68 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4308142 {A B : Type'} (f : type1478 A B) (y : B) : (term1121 A B f y) = (f y).
Proof. exact (@lem4308141 B (prod A B) f y). Qed.
Lemma lem4308143 {A B : Type'} (x : A) (x' : B) : (term1122 A B x x') = (term1123 A B x x').
Proof. exact (@lem4308142 A B (term1114 A B x) x'). Qed.
Lemma lem4308144 {A B : Type'} (x : A) (y : B) : (term1123 A B x y) = (@pair A B x y).
Proof. exact (eq_refl (term1123 A B x y)). Qed.
Lemma lem4308145 {A B : Type'} (x : A) : (term1124 A B x) = (term1114 A B x).
Proof. exact (fun_ext (fun y : B => @lem4308144 A B x y)). Qed.
Lemma lem4308146 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4308147 {A B : Type'} (x : A) (x' : B) : (term1122 A B x x') = (term1123 A B x x').
Proof. exact (MK_COMB (@lem4308145 A B x) (@lem4308146 B x')). Qed.
Lemma lem4308148 {A B : Type'} : (@eq (prod A B)) = (@eq (prod A B)).
Proof. exact (eq_refl (@eq (prod A B))). Qed.
Lemma lem4308149 {A B : Type'} (x : A) (x' : B) : (term1125 A B x x') = (term1126 A B x x').
Proof. exact (MK_COMB (@lem4308148 A B) (@lem4308147 A B x x')). Qed.
Lemma lem4308150 {A B : Type'} (x : A) (x' : B) : (term1123 A B x x') = (@pair A B x x').
Proof. exact (eq_refl (term1123 A B x x')). Qed.
Lemma lem4308151 {A B : Type'} (x : A) (x' : B) : ((term1122 A B x x') = (term1123 A B x x')) = ((term1123 A B x x') = (@pair A B x x')).
Proof. exact (MK_COMB (@lem4308149 A B x x') (@lem4308150 A B x x')). Qed.
Lemma lem4308152 {A B : Type'} (x : A) (x' : B) : (term1123 A B x x') = (@pair A B x x').
Proof. exact (EQ_MP (@lem4308151 A B x x') (@lem4308143 A B x x')). Qed.
Lemma lem4308153 {A B : Type'} (x : prod A B) : (@eq (prod A B) x) = (@eq (prod A B) x).
Proof. exact (eq_refl (@eq (prod A B) x)). Qed.
Lemma lem4308154 {A B : Type'} (x : prod A B) (x' : A) (x'' : B) : (x = (term1123 A B x' x'')) = (x = (@pair A B x' x'')).
Proof. exact (MK_COMB (@lem4308153 A B x) (@lem4308152 A B x' x'')). Qed.
Lemma lem4308159 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4308160 {A B : Type'} (x : prod A B) (x' : A) (x'' : B) : (term1199 A B x x' x'') = (term1200 A B x x' x'').
Proof. exact (MK_COMB (@lem4308159) (@lem4308154 A B x x' x'')). Qed.
Lemma lem4308161 {A B : Type'} (x : B) (t : type1413 A B) (x' : A) : (term760 A B x t x') = (term760 A B x t x').
Proof. exact (eq_refl (term760 A B x t x')). Qed.
Lemma lem4308162 {A B : Type'} (x : prod A B) (x' : B) (t : type1413 A B) (x'' : A) : (term1201 A B x x' t x'') = (term1202 A B x x' t x'').
Proof. exact (MK_COMB (@lem4308160 A B x x'' x') (@lem4308161 A B x' t x'')). Qed.
Lemma lem4308165 {A B : Type'} (x : prod A B) (t : type1413 A B) (x' : A) : (term1203 A B x t x') = (term1204 A B x t x').
Proof. exact (fun_ext (fun x'' : B => @lem4308162 A B x x'' t x')). Qed.
Lemma lem4308166 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4308167 {A B : Type'} (x : prod A B) (t : type1413 A B) (x' : A) : (term1198 A B x t x') = (term1205 A B x t x').
Proof. exact (MK_COMB (@lem4308166 B) (@lem4308165 A B x t x')). Qed.
Lemma lem4308174 {A B : Type'} (x : prod A B) (t : type1413 A B) (x' : A) : (term1197 A B x t x') = (term1205 A B x t x').
Proof. exact (TRANS (@lem4308127 A B x t x') (@lem4308167 A B x t x')). Qed.
Lemma lem4308175 {A B : Type'} (s : A -> Prop) (x : prod A B) (t : type1413 A B) (x' : A) : (term1158 A B s x t x') = (term1206 A B s x t x').
Proof. exact (MK_COMB (@lem4308123 A B s t x) (@lem4308174 A B x t x')). Qed.
Lemma lem4308178 {A B : Type'} (s : A -> Prop) (x : prod A B) (t : type1413 A B) (x' : A) : (term1157 A B x s t x') = (term1206 A B s x t x').
Proof. exact (TRANS (@lem4308028 A B s x t x') (@lem4308175 A B s x t x')). Qed.
Lemma lem4308179 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4308180 {A B : Type'} (s : A -> Prop) (x : prod A B) (t : type1413 A B) (x' : A) : (term1207 A B x s t x') = (term1208 A B s x t x').
Proof. exact (MK_COMB (@lem4308179) (@lem4308178 A B s x t x')). Qed.
Lemma lem4308182 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4292794 A x (@lem4292793 A x)). Qed.
Lemma lem4308183 {A B : Type'} (x : prod A B) : (@IN (prod A B) x (@EMPTY (prod A B))) = False.
Proof. exact (@lem4308182 (prod A B) x). Qed.
Lemma lem4308184 {A B : Type'} (s : A -> Prop) (x : prod A B) (t : type1413 A B) (x' : A) : ((term1157 A B x s t x') = (@IN (prod A B) x (@EMPTY (prod A B)))) = ((term1206 A B s x t x') = False).
Proof. exact (MK_COMB (@lem4308180 A B s x t x') (@lem4308183 A B x)). Qed.
Lemma lem4308186 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem4308187 {A B : Type'} (s : A -> Prop) (x : prod A B) (t : type1413 A B) (x' : A) : ((term1206 A B s x t x') = False) = (term1209 A B s x t x').
Proof. exact (@lem4308186 (term1206 A B s x t x')). Qed.
Lemma lem4308222 {A B : Type'} (s : A -> Prop) (x : prod A B) (t : type1413 A B) (x' : A) : ((term1157 A B x s t x') = (@IN (prod A B) x (@EMPTY (prod A B)))) = (term1209 A B s x t x').
Proof. exact (TRANS (@lem4308184 A B s x t x') (@lem4308187 A B s x t x')). Qed.
Lemma lem4308223 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : A) : (term1210 A B s t x) = (term1211 A B s t x).
Proof. exact (fun_ext (fun x' : prod A B => @lem4308222 A B s x' t x)). Qed.
Lemma lem4308224 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem4308225 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : A) : (term1154 A B s t x) = (term1212 A B s t x).
Proof. exact (MK_COMB (@lem4308224 A B) (@lem4308223 A B s t x)). Qed.
Lemma lem4308230 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : A) : (term1149 A B s t x) = (term1212 A B s t x).
Proof. exact (TRANS (@lem4308020 A B s t x) (@lem4308225 A B s t x)). Qed.
Lemma lem4308231 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : A) : (term1212 A B s t x) = (term1149 A B s t x).
Proof. exact (SYM (@lem4308230 A B s t x)). Qed.
Lemma lem4308232 {A B : Type'} (s : A -> Prop) (x' : prod A B) (t : type1413 A B) (x : A) (h1 : term1206 A B s x' t x) : term1206 A B s x' t x.
Proof. exact (h1). Qed.
Lemma lem4308233 {A B : Type'} (x' : prod A B) (t : type1413 A B) (x : A) (h1 : term1205 A B x' t x) : term1205 A B x' t x.
Proof. exact (h1). Qed.
Lemma lem4308234 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x' : prod A B) (h1 : term1192 A B s t x') : term1192 A B s t x'.
Proof. exact (h1). Qed.
Lemma lem4308235 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x' : prod A B) (x'' : A) (h1 : term1189 A B s t x' x'') : term1189 A B s t x' x''.
Proof. exact (h1). Qed.
Lemma lem4308236 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x' : prod A B) (x'' : A) (y : B) (h1 : term1185 A B s t x' x'' y) : term1185 A B s t x' x'' y.
Proof. exact (h1). Qed.
Lemma lem4308237 {A B : Type'} (x' : prod A B) (x'' : A) (y : B) (h1 : x' = (@pair A B x'' y)) : x' = (@pair A B x'' y).
Proof. exact (h1). Qed.
Lemma lem4308238 {A B : Type'} (s : A -> Prop) (y : B) (t : type1413 A B) (x'' : A) (h1 : term1173 A B s y t x'') : term1173 A B s y t x''.
Proof. exact (h1). Qed.
Lemma lem4308239 {A B : Type'} (y : B) (t : type1413 A B) (x'' : A) (h1 : term760 A B y t x'') : term760 A B y t x''.
Proof. exact (h1). Qed.
Lemma lem4308240 {A : Type'} (x'' : A) (s : A -> Prop) (h1 : @IN A x'' s) : @IN A x'' s.
Proof. exact (h1). Qed.
Lemma lem4308241 {A B : Type'} (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) (h1 : term1202 A B x' x''' t x) : term1202 A B x' x''' t x.
Proof. exact (h1). Qed.
Lemma lem4308242 {A B : Type'} (x''' : B) (t : type1413 A B) (x : A) (h1 : term760 A B x''' t x) : term760 A B x''' t x.
Proof. exact (h1). Qed.
Lemma lem4308243 {A B : Type'} (x' : prod A B) (x : A) (x''' : B) (h1 : x' = (@pair A B x x''')) : x' = (@pair A B x x''').
Proof. exact (h1). Qed.
Lemma lem4308244 {A B : Type'} : term1213 A B.
Proof. exact (@lem47438 A B). Qed.
Lemma lem4308246 {B : Type'} : term1214 B.
Proof. exact (@lem47438 nat B). Qed.
Lemma lem4308247 {A B : Type'} : term1215 A B.
Proof. exact (@lem47438 (prod A B) B). Qed.
Lemma lem4308248 {A : Type'} : term1216 A.
Proof. exact (@lem47438 A nat). Qed.
Lemma lem4308249 {A B : Type'} : term1217 A B.
Proof. exact (@lem47438 A (prod A B)). Qed.
Lemma lem4308252 {A B : Type'} (m : nat) (n : nat) (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) (h1 : term1218 A B m n s x'' y x' x''' t x) : term1218 A B m n s x'' y x' x''' t x.
Proof. exact (h1). Qed.
Lemma lem4308253 {A B : Type'} (m : nat) (n : nat) (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : term1219 A B m n s x'' y x' x''' t x.
Proof. exact (fun h0 : term1218 A B m n s x'' y x' x''' t x => @lem4308252 A B m n s x'' y x' x''' t x h0). Qed.
Lemma lem4308254 {A B : Type'} (m : nat) (n : nat) (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) (h1 : term1219 A B m n s x'' y x' x''' t x) : term1219 A B m n s x'' y x' x''' t x.
Proof. exact (h1). Qed.
Lemma lem4308255 {A B : Type'} (m : nat) (n : nat) (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) (h1 : term1218 A B m n s x'' y x' x''' t x) : term1218 A B m n s x'' y x' x''' t x.
Proof. exact (h1). Qed.
Lemma lem4308256 {A B : Type'} (m : nat) (n : nat) (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) (h1 : term1218 A B m n s x'' y x' x''' t x) (h2 : term1219 A B m n s x'' y x' x''' t x) : term1218 A B m n s x'' y x' x''' t x.
Proof. exact (@lem4308254 A B m n s x'' y x' x''' t x h2 (@lem4308255 A B m n s x'' y x' x''' t x h1)). Qed.
Lemma lem4308257 {A B : Type'} (m : nat) (n : nat) (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) (h1 : term1218 A B m n s x'' y x' x''' t x) : term1220 A B m n s x'' y x' x''' t x.
Proof. exact (fun h0 : term1219 A B m n s x'' y x' x''' t x => @lem4308256 A B m n s x'' y x' x''' t x h1 h0). Qed.
Lemma lem4308258 {A B : Type'} (m : nat) (n : nat) (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) (h1 : term1219 A B m n s x'' y x' x''' t x) : term1219 A B m n s x'' y x' x''' t x.
Proof. exact (h1). Qed.
Lemma lem4308259 {A B : Type'} (m : nat) (n : nat) (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) (h1 : term1218 A B m n s x'' y x' x''' t x) (h2 : term1219 A B m n s x'' y x' x''' t x) : term1218 A B m n s x'' y x' x''' t x.
Proof. exact (@lem4308257 A B m n s x'' y x' x''' t x h1 (@lem4308258 A B m n s x'' y x' x''' t x h2)). Qed.
Lemma lem4308260 {A B : Type'} (m : nat) (n : nat) (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) (h1 : term1219 A B m n s x'' y x' x''' t x) : term1219 A B m n s x'' y x' x''' t x.
Proof. exact (fun h0 : term1218 A B m n s x'' y x' x''' t x => @lem4308259 A B m n s x'' y x' x''' t x h0 h1). Qed.
Lemma lem4308261 {A B : Type'} (m : nat) (n : nat) (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : term1221 A B m n s x'' y x' x''' t x.
Proof. exact (fun h0 : term1219 A B m n s x'' y x' x''' t x => @lem4308260 A B m n s x'' y x' x''' t x h0). Qed.
Lemma lem4308264 {A B : Type'} (m : nat) (n : nat) (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : term1219 A B m n s x'' y x' x''' t x.
Proof. exact (@lem4308261 A B m n s x'' y x' x''' t x (@lem4308253 A B m n s x'' y x' x''' t x)). Qed.
Lemma lem4308265 {A B : Type'} (m : nat) (n : nat) (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : term1219 A B m n s x'' y x' x''' t x.
Proof. exact (@lem4308264 A B m n s x'' y x' x''' t x). Qed.
Lemma lem4308437 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4308438 {A B : Type'} : (term1222 A B) = (term1223 A B).
Proof. exact (@lem4308437 (term1215 A B)). Qed.
Lemma lem4308457 {B : Type'} : (term1224 B) = (term1224 B).
Proof. exact (eq_refl (term1224 B)). Qed.
Lemma lem4308458 {A B : Type'} : (term1225 A B) = (term1226 A B).
Proof. exact (MK_COMB (@lem4308457 B) (@lem4308438 A B)). Qed.
Lemma lem4308461 {A B : Type'} : (term1227 A B) = (term1227 A B).
Proof. exact (eq_refl (term1227 A B)). Qed.
Lemma lem4308462 {A B : Type'} : (term1228 A B) = (term1229 A B).
Proof. exact (MK_COMB (@lem4308461 A B) (@lem4308458 A B)). Qed.
Lemma lem4308465 {A : Type'} : (term1230 A) = (term1230 A).
Proof. exact (eq_refl (term1230 A)). Qed.
Lemma lem4308466 {A B : Type'} : (term1231 A B) = (term1232 A B).
Proof. exact (MK_COMB (@lem4308465 A) (@lem4308462 A B)). Qed.
Lemma lem4308469 {A B : Type'} : (term1233 A B) = (term1233 A B).
Proof. exact (eq_refl (term1233 A B)). Qed.
Lemma lem4308470 {A B : Type'} : (term1234 A B) = (term1235 A B).
Proof. exact (MK_COMB (@lem4308469 A B) (@lem4308466 A B)). Qed.
Lemma lem4308473 {A B : Type'} (x''' : B) (t : type1413 A B) (x : A) : (term1236 A B x''' t x) = (term1236 A B x''' t x).
Proof. exact (eq_refl (term1236 A B x''' t x)). Qed.
Lemma lem4308474 {A B : Type'} (x''' : B) (t : type1413 A B) (x : A) : (term1237 A B x''' t x) = (term1238 A B x''' t x).
Proof. exact (MK_COMB (@lem4308473 A B x''' t x) (@lem4308470 A B)). Qed.
Lemma lem4308477 {A B : Type'} (x' : prod A B) (x : A) (x''' : B) : (term1239 A B x' x x''') = (term1239 A B x' x x''').
Proof. exact (eq_refl (term1239 A B x' x x''')). Qed.
Lemma lem4308478 {A B : Type'} (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : (term1240 A B x' x''' t x) = (term1241 A B x' x''' t x).
Proof. exact (MK_COMB (@lem4308477 A B x' x x''') (@lem4308474 A B x''' t x)). Qed.
Lemma lem4308481 {A B : Type'} (x' : prod A B) (x'' : A) (y : B) : (term1239 A B x' x'' y) = (term1239 A B x' x'' y).
Proof. exact (eq_refl (term1239 A B x' x'' y)). Qed.
Lemma lem4308482 {A B : Type'} (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : (term1242 A B x'' y x' x''' t x) = (term1243 A B x'' y x' x''' t x).
Proof. exact (MK_COMB (@lem4308481 A B x' x'' y) (@lem4308478 A B x' x''' t x)). Qed.
Lemma lem4308485 {A B : Type'} (y : B) (t : type1413 A B) (x'' : A) : (term1236 A B y t x'') = (term1236 A B y t x'').
Proof. exact (eq_refl (term1236 A B y t x'')). Qed.
Lemma lem4308486 {A B : Type'} (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : (term1244 A B x'' y x' x''' t x) = (term1245 A B x'' y x' x''' t x).
Proof. exact (MK_COMB (@lem4308485 A B y t x'') (@lem4308482 A B x'' y x' x''' t x)). Qed.
Lemma lem4308489 {A : Type'} (x'' : A) (s : A -> Prop) : (term1246 A x'' s) = (term1246 A x'' s).
Proof. exact (eq_refl (term1246 A x'' s)). Qed.
Lemma lem4308490 {A B : Type'} (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : (term1247 A B s x'' y x' x''' t x) = (term1248 A B s x'' y x' x''' t x).
Proof. exact (MK_COMB (@lem4308489 A x'' s) (@lem4308486 A B x'' y x' x''' t x)). Qed.
Lemma lem4308493 {A B : Type'} (s : A -> Prop) : (term1063 A B s) = (term1063 A B s).
Proof. exact (eq_refl (term1063 A B s)). Qed.
Lemma lem4308494 {A B : Type'} (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : (term1249 A B s x'' y x' x''' t x) = (term1250 A B s x'' y x' x''' t x).
Proof. exact (MK_COMB (@lem4308493 A B s) (@lem4308490 A B s x'' y x' x''' t x)). Qed.
Lemma lem4308497 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (n : nat) : (term1251 A B s t n) = (term1251 A B s t n).
Proof. exact (eq_refl (term1251 A B s t n)). Qed.
Lemma lem4308498 {A B : Type'} (n : nat) (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : (term1252 A B n s x'' y x' x''' t x) = (term1253 A B n s x'' y x' x''' t x).
Proof. exact (MK_COMB (@lem4308497 A B s t n) (@lem4308494 A B s x'' y x' x''' t x)). Qed.
Lemma lem4308501 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) : (term1254 A B t x n) = (term1254 A B t x n).
Proof. exact (eq_refl (term1254 A B t x n)). Qed.
Lemma lem4308502 {A B : Type'} (n : nat) (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : (term1255 A B n s x'' y x' x''' t x) = (term1256 A B n s x'' y x' x''' t x).
Proof. exact (MK_COMB (@lem4308501 A B t x n) (@lem4308498 A B n s x'' y x' x''' t x)). Qed.
Lemma lem4308505 {A : Type'} (m : nat) (s : A -> Prop) : (term1257 A m s) = (term1257 A m s).
Proof. exact (eq_refl (term1257 A m s)). Qed.
Lemma lem4308506 {A B : Type'} (m : nat) (n : nat) (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : (term1258 A B m n s x'' y x' x''' t x) = (term1259 A B m n s x'' y x' x''' t x).
Proof. exact (MK_COMB (@lem4308505 A m s) (@lem4308502 A B n s x'' y x' x''' t x)). Qed.
Lemma lem4308509 {A : Type'} (s : A -> Prop) : (term619 A s) = (term619 A s).
Proof. exact (eq_refl (term619 A s)). Qed.
Lemma lem4308510 {A B : Type'} (m : nat) (n : nat) (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : (term1260 A B m n s x'' y x' x''' t x) = (term1261 A B m n s x'' y x' x''' t x).
Proof. exact (MK_COMB (@lem4308509 A s) (@lem4308506 A B m n s x'' y x' x''' t x)). Qed.
Lemma lem4308513 {A : Type'} (x : A) (s : A -> Prop) : (term1262 A x s) = (term1262 A x s).
Proof. exact (eq_refl (term1262 A x s)). Qed.
Lemma lem4308514 {A B : Type'} (m : nat) (n : nat) (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : (term1218 A B m n s x'' y x' x''' t x) = (term1263 A B m n s x'' y x' x''' t x).
Proof. exact (MK_COMB (@lem4308513 A x s) (@lem4308510 A B m n s x'' y x' x''' t x)). Qed.
Lemma lem4308517 {A B : Type'} (n : nat) (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : (term1264 A B n s x'' y x' x''' t x) = (term1265 A B n s x'' y x' x''' t x).
Proof. exact (fun_ext (fun m : nat => @lem4308514 A B m n s x'' y x' x''' t x)). Qed.
Lemma lem4308518 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4308519 {A B : Type'} (n : nat) (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : (term1266 A B n s x'' y x' x''' t x) = (term1267 A B n s x'' y x' x''' t x).
Proof. exact (MK_COMB (@lem4308518) (@lem4308517 A B n s x'' y x' x''' t x)). Qed.
Lemma lem4308524 {A B : Type'} (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : (term1268 A B s x'' y x' x''' t x) = (term1269 A B s x'' y x' x''' t x).
Proof. exact (fun_ext (fun n : nat => @lem4308519 A B n s x'' y x' x''' t x)). Qed.
Lemma lem4308525 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4308526 {A B : Type'} (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : (term1270 A B s x'' y x' x''' t x) = (term1271 A B s x'' y x' x''' t x).
Proof. exact (MK_COMB (@lem4308525) (@lem4308524 A B s x'' y x' x''' t x)). Qed.
Lemma lem4308531 {A B : Type'} (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : (term1272 A B x'' y x' x''' t x) = (term1273 A B x'' y x' x''' t x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4308526 A B s x'' y x' x''' t x)). Qed.
Lemma lem4308532 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4308533 {A B : Type'} (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : (term1274 A B x'' y x' x''' t x) = (term1275 A B x'' y x' x''' t x).
Proof. exact (MK_COMB (@lem4308532 A) (@lem4308531 A B x'' y x' x''' t x)). Qed.
Lemma lem4308538 {A B : Type'} (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : (term1276 A B y x' x''' t x) = (term1277 A B y x' x''' t x).
Proof. exact (fun_ext (fun x'' : A => @lem4308533 A B x'' y x' x''' t x)). Qed.
Lemma lem4308539 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4308540 {A B : Type'} (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : (term1278 A B y x' x''' t x) = (term1279 A B y x' x''' t x).
Proof. exact (MK_COMB (@lem4308539 A) (@lem4308538 A B y x' x''' t x)). Qed.
Lemma lem4308545 {A B : Type'} (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : (term1280 A B x' x''' t x) = (term1281 A B x' x''' t x).
Proof. exact (fun_ext (fun y : B => @lem4308540 A B y x' x''' t x)). Qed.
Lemma lem4308546 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4308547 {A B : Type'} (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : (term1282 A B x' x''' t x) = (term1283 A B x' x''' t x).
Proof. exact (MK_COMB (@lem4308546 B) (@lem4308545 A B x' x''' t x)). Qed.
Lemma lem4308552 {A B : Type'} (x''' : B) (t : type1413 A B) (x : A) : (term1284 A B x''' t x) = (term1285 A B x''' t x).
Proof. exact (fun_ext (fun x' : prod A B => @lem4308547 A B x' x''' t x)). Qed.
Lemma lem4308553 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem4308554 {A B : Type'} (x''' : B) (t : type1413 A B) (x : A) : (term1286 A B x''' t x) = (term1287 A B x''' t x).
Proof. exact (MK_COMB (@lem4308553 A B) (@lem4308552 A B x''' t x)). Qed.
Lemma lem4308559 {A B : Type'} (t : type1413 A B) (x : A) : (term1288 A B t x) = (term1289 A B t x).
Proof. exact (fun_ext (fun x''' : B => @lem4308554 A B x''' t x)). Qed.
Lemma lem4308560 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4308561 {A B : Type'} (t : type1413 A B) (x : A) : (term1290 A B t x) = (term1291 A B t x).
Proof. exact (MK_COMB (@lem4308560 B) (@lem4308559 A B t x)). Qed.
Lemma lem4308566 {A B : Type'} (x : A) : (term1292 A B x) = (term1293 A B x).
Proof. exact (fun_ext (fun t : type1413 A B => @lem4308561 A B t x)). Qed.
Lemma lem4308567 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem4308568 {A B : Type'} (x : A) : (term1294 A B x) = (term1295 A B x).
Proof. exact (MK_COMB (@lem4308567 A B) (@lem4308566 A B x)). Qed.
Lemma lem4308573 {A B : Type'} : (term1296 A B) = (term1297 A B).
Proof. exact (fun_ext (fun x : A => @lem4308568 A B x)). Qed.
Lemma lem4308574 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4308581 {A B : Type'} : (term1298 A B) = (term1299 A B).
Proof. exact (MK_COMB (@lem4308574 A) (@lem4308573 A B)). Qed.
Lemma lem4308582 {A B : Type'} (_48808 : type621 A B) (h1 : _48808 = (term1300 A B)) : _48808 = (term1300 A B).
Proof. exact (h1). Qed.
Lemma lem4308583 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4308584 {A B : Type'} (s : A -> Prop) (_48808 : type621 A B) (h1 : _48808 = (term1300 A B)) : (_48808 s) = (term1301 A B s).
Proof. exact (MK_COMB (@lem4308582 A B _48808 h1) (@lem4308583 A s)). Qed.
Lemma lem4308585 {A B : Type'} (s : A -> Prop) : (term1301 A B s) = (term1302 A B s).
Proof. exact (eq_refl (term1301 A B s)). Qed.
Lemma lem4308586 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1303 A B _48808 s) = (term1303 A B _48808 s).
Proof. exact (eq_refl (term1303 A B _48808 s)). Qed.
Lemma lem4308587 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : ((_48808 s) = (term1301 A B s)) = ((_48808 s) = (term1302 A B s)).
Proof. exact (MK_COMB (@lem4308586 A B _48808 s) (@lem4308585 A B s)). Qed.
Lemma lem4308588 {A B : Type'} (s : A -> Prop) (_48808 : type621 A B) (h1 : _48808 = (term1300 A B)) : (_48808 s) = (term1302 A B s).
Proof. exact (EQ_MP (@lem4308587 A B _48808 s) (@lem4308584 A B s _48808 h1)). Qed.
Lemma lem4308589 {A B : Type'} (t : type1413 A B) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4308590 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (_48808 : type621 A B) (h1 : _48808 = (term1300 A B)) : (_48808 s t) = (term1304 A B s t).
Proof. exact (MK_COMB (@lem4308588 A B s _48808 h1) (@lem4308589 A B t)). Qed.
Lemma lem4308591 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term1304 A B s t) = (term1165 A B s t).
Proof. exact (eq_refl (term1304 A B s t)). Qed.
Lemma lem4308592 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1305 A B _48808 s t) = (term1305 A B _48808 s t).
Proof. exact (eq_refl (term1305 A B _48808 s t)). Qed.
Lemma lem4308593 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : ((_48808 s t) = (term1304 A B s t)) = ((_48808 s t) = (term1165 A B s t)).
Proof. exact (MK_COMB (@lem4308592 A B _48808 s t) (@lem4308591 A B s t)). Qed.
Lemma lem4308594 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (_48808 : type621 A B) (h1 : _48808 = (term1300 A B)) : (_48808 s t) = (term1165 A B s t).
Proof. exact (EQ_MP (@lem4308593 A B _48808 s t) (@lem4308590 A B s t _48808 h1)). Qed.
Lemma lem4308624 {A B : Type'} (x : prod A B) (a : prod A B) (y : B) (b : B) : (((@pair (prod A B) B x y) = (@pair (prod A B) B a b)) = (term1306 A B x a y b)) = (((@pair (prod A B) B x y) = (@pair (prod A B) B a b)) = (term1306 A B x a y b)).
Proof. exact (eq_refl (((@pair (prod A B) B x y) = (@pair (prod A B) B a b)) = (term1306 A B x a y b))). Qed.
Lemma lem4308625 {A B : Type'} (x : prod A B) (a : prod A B) (y : B) : (term1307 A B x a y) = (term1307 A B x a y).
Proof. exact (fun_ext (fun b : B => @lem4308624 A B x a y b)). Qed.
Lemma lem4308626 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4308627 {A B : Type'} (x : prod A B) (a : prod A B) (y : B) : (term1308 A B x a y) = (term1308 A B x a y).
Proof. exact (MK_COMB (@lem4308626 B) (@lem4308625 A B x a y)). Qed.
Lemma lem4308628 {A B : Type'} (x : prod A B) (y : B) : (term1309 A B x y) = (term1309 A B x y).
Proof. exact (fun_ext (fun a : prod A B => @lem4308627 A B x a y)). Qed.
Lemma lem4308629 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem4308630 {A B : Type'} (x : prod A B) (y : B) : (term1310 A B x y) = (term1310 A B x y).
Proof. exact (MK_COMB (@lem4308629 A B) (@lem4308628 A B x y)). Qed.
Lemma lem4308631 {A B : Type'} (x : prod A B) : (term1311 A B x) = (term1311 A B x).
Proof. exact (fun_ext (fun y : B => @lem4308630 A B x y)). Qed.
Lemma lem4308632 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4308633 {A B : Type'} (x : prod A B) : (term1312 A B x) = (term1312 A B x).
Proof. exact (MK_COMB (@lem4308632 B) (@lem4308631 A B x)). Qed.
Lemma lem4308634 {A B : Type'} : (term1313 A B) = (term1313 A B).
Proof. exact (fun_ext (fun x : prod A B => @lem4308633 A B x)). Qed.
Lemma lem4308635 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem4308636 {A B : Type'} : (term1215 A B) = (term1215 A B).
Proof. exact (MK_COMB (@lem4308635 A B) (@lem4308634 A B)). Qed.
Lemma lem4308637 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4308638 {A B : Type'} : (term1223 A B) = (term1223 A B).
Proof. exact (MK_COMB (@lem4308637) (@lem4308636 A B)). Qed.
Lemma lem4308667 {B : Type'} (x : nat) (a : nat) (y : B) (b : B) : (((@pair nat B x y) = (@pair nat B a b)) = (term1314 B x a y b)) = (((@pair nat B x y) = (@pair nat B a b)) = (term1314 B x a y b)).
Proof. exact (eq_refl (((@pair nat B x y) = (@pair nat B a b)) = (term1314 B x a y b))). Qed.
Lemma lem4308668 {B : Type'} (x : nat) (a : nat) (y : B) : (term1315 B x a y) = (term1315 B x a y).
Proof. exact (fun_ext (fun b : B => @lem4308667 B x a y b)). Qed.
Lemma lem4308669 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4308670 {B : Type'} (x : nat) (a : nat) (y : B) : (term1316 B x a y) = (term1316 B x a y).
Proof. exact (MK_COMB (@lem4308669 B) (@lem4308668 B x a y)). Qed.
Lemma lem4308671 {B : Type'} (x : nat) (y : B) : (term1317 B x y) = (term1317 B x y).
Proof. exact (fun_ext (fun a : nat => @lem4308670 B x a y)). Qed.
Lemma lem4308672 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4308673 {B : Type'} (x : nat) (y : B) : (term1318 B x y) = (term1318 B x y).
Proof. exact (MK_COMB (@lem4308672) (@lem4308671 B x y)). Qed.
Lemma lem4308674 {B : Type'} (x : nat) : (term1319 B x) = (term1319 B x).
Proof. exact (fun_ext (fun y : B => @lem4308673 B x y)). Qed.
Lemma lem4308675 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4308676 {B : Type'} (x : nat) : (term1320 B x) = (term1320 B x).
Proof. exact (MK_COMB (@lem4308675 B) (@lem4308674 B x)). Qed.
Lemma lem4308677 {B : Type'} : (term1321 B) = (term1321 B).
Proof. exact (fun_ext (fun x : nat => @lem4308676 B x)). Qed.
Lemma lem4308678 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4308679 {B : Type'} : (term1214 B) = (term1214 B).
Proof. exact (MK_COMB (@lem4308678) (@lem4308677 B)). Qed.
Lemma lem4308680 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4308681 {B : Type'} : (term1224 B) = (term1224 B).
Proof. exact (MK_COMB (@lem4308680) (@lem4308679 B)). Qed.
Lemma lem4308682 {A B : Type'} : (term1226 A B) = (term1226 A B).
Proof. exact (MK_COMB (@lem4308681 B) (@lem4308638 A B)). Qed.
Lemma lem4308711 {A B : Type'} (x : A) (a : A) (y : prod A B) (b : prod A B) : (((@pair A (prod A B) x y) = (@pair A (prod A B) a b)) = (term1322 A B x a y b)) = (((@pair A (prod A B) x y) = (@pair A (prod A B) a b)) = (term1322 A B x a y b)).
Proof. exact (eq_refl (((@pair A (prod A B) x y) = (@pair A (prod A B) a b)) = (term1322 A B x a y b))). Qed.
Lemma lem4308712 {A B : Type'} (x : A) (a : A) (y : prod A B) : (term1323 A B x a y) = (term1323 A B x a y).
Proof. exact (fun_ext (fun b : prod A B => @lem4308711 A B x a y b)). Qed.
Lemma lem4308713 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem4308714 {A B : Type'} (x : A) (a : A) (y : prod A B) : (term1324 A B x a y) = (term1324 A B x a y).
Proof. exact (MK_COMB (@lem4308713 A B) (@lem4308712 A B x a y)). Qed.
Lemma lem4308715 {A B : Type'} (x : A) (y : prod A B) : (term1325 A B x y) = (term1325 A B x y).
Proof. exact (fun_ext (fun a : A => @lem4308714 A B x a y)). Qed.
Lemma lem4308716 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4308717 {A B : Type'} (x : A) (y : prod A B) : (term1326 A B x y) = (term1326 A B x y).
Proof. exact (MK_COMB (@lem4308716 A) (@lem4308715 A B x y)). Qed.
Lemma lem4308718 {A B : Type'} (x : A) : (term1327 A B x) = (term1327 A B x).
Proof. exact (fun_ext (fun y : prod A B => @lem4308717 A B x y)). Qed.
Lemma lem4308719 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem4308720 {A B : Type'} (x : A) : (term1328 A B x) = (term1328 A B x).
Proof. exact (MK_COMB (@lem4308719 A B) (@lem4308718 A B x)). Qed.
Lemma lem4308721 {A B : Type'} : (term1329 A B) = (term1329 A B).
Proof. exact (fun_ext (fun x : A => @lem4308720 A B x)). Qed.
Lemma lem4308722 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4308723 {A B : Type'} : (term1217 A B) = (term1217 A B).
Proof. exact (MK_COMB (@lem4308722 A) (@lem4308721 A B)). Qed.
Lemma lem4308724 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4308725 {A B : Type'} : (term1227 A B) = (term1227 A B).
Proof. exact (MK_COMB (@lem4308724) (@lem4308723 A B)). Qed.
Lemma lem4308726 {A B : Type'} : (term1229 A B) = (term1229 A B).
Proof. exact (MK_COMB (@lem4308725 A B) (@lem4308682 A B)). Qed.
Lemma lem4308755 {A : Type'} (x : A) (a : A) (y : nat) (b : nat) : (((@pair A nat x y) = (@pair A nat a b)) = (term1330 A x a y b)) = (((@pair A nat x y) = (@pair A nat a b)) = (term1330 A x a y b)).
Proof. exact (eq_refl (((@pair A nat x y) = (@pair A nat a b)) = (term1330 A x a y b))). Qed.
Lemma lem4308756 {A : Type'} (x : A) (a : A) (y : nat) : (term1331 A x a y) = (term1331 A x a y).
Proof. exact (fun_ext (fun b : nat => @lem4308755 A x a y b)). Qed.
Lemma lem4308757 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4308758 {A : Type'} (x : A) (a : A) (y : nat) : (term1332 A x a y) = (term1332 A x a y).
Proof. exact (MK_COMB (@lem4308757) (@lem4308756 A x a y)). Qed.
Lemma lem4308759 {A : Type'} (x : A) (y : nat) : (term1333 A x y) = (term1333 A x y).
Proof. exact (fun_ext (fun a : A => @lem4308758 A x a y)). Qed.
Lemma lem4308760 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4308761 {A : Type'} (x : A) (y : nat) : (term1334 A x y) = (term1334 A x y).
Proof. exact (MK_COMB (@lem4308760 A) (@lem4308759 A x y)). Qed.
Lemma lem4308762 {A : Type'} (x : A) : (term1335 A x) = (term1335 A x).
Proof. exact (fun_ext (fun y : nat => @lem4308761 A x y)). Qed.
Lemma lem4308763 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4308764 {A : Type'} (x : A) : (term1336 A x) = (term1336 A x).
Proof. exact (MK_COMB (@lem4308763) (@lem4308762 A x)). Qed.
Lemma lem4308765 {A : Type'} : (term1337 A) = (term1337 A).
Proof. exact (fun_ext (fun x : A => @lem4308764 A x)). Qed.
Lemma lem4308766 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4308767 {A : Type'} : (term1216 A) = (term1216 A).
Proof. exact (MK_COMB (@lem4308766 A) (@lem4308765 A)). Qed.
Lemma lem4308768 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4308769 {A : Type'} : (term1230 A) = (term1230 A).
Proof. exact (MK_COMB (@lem4308768) (@lem4308767 A)). Qed.
Lemma lem4308770 {A B : Type'} : (term1232 A B) = (term1232 A B).
Proof. exact (MK_COMB (@lem4308769 A) (@lem4308726 A B)). Qed.
Lemma lem4308799 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (((@pair A B x y) = (@pair A B a b)) = (term1085 A B x a y b)) = (((@pair A B x y) = (@pair A B a b)) = (term1085 A B x a y b)).
Proof. exact (eq_refl (((@pair A B x y) = (@pair A B a b)) = (term1085 A B x a y b))). Qed.
Lemma lem4308800 {A B : Type'} (x : A) (a : A) (y : B) : (term1338 A B x a y) = (term1338 A B x a y).
Proof. exact (fun_ext (fun b : B => @lem4308799 A B x a y b)). Qed.
Lemma lem4308801 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4308802 {A B : Type'} (x : A) (a : A) (y : B) : (term1083 A B x a y) = (term1083 A B x a y).
Proof. exact (MK_COMB (@lem4308801 B) (@lem4308800 A B x a y)). Qed.
Lemma lem4308803 {A B : Type'} (x : A) (y : B) : (term1339 A B x y) = (term1339 A B x y).
Proof. exact (fun_ext (fun a : A => @lem4308802 A B x a y)). Qed.
Lemma lem4308804 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4308805 {A B : Type'} (x : A) (y : B) : (term1081 A B x y) = (term1081 A B x y).
Proof. exact (MK_COMB (@lem4308804 A) (@lem4308803 A B x y)). Qed.
Lemma lem4308806 {A B : Type'} (x : A) : (term1340 A B x) = (term1340 A B x).
Proof. exact (fun_ext (fun y : B => @lem4308805 A B x y)). Qed.
Lemma lem4308807 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4308808 {A B : Type'} (x : A) : (term1079 A B x) = (term1079 A B x).
Proof. exact (MK_COMB (@lem4308807 B) (@lem4308806 A B x)). Qed.
Lemma lem4308809 {A B : Type'} : (term1341 A B) = (term1341 A B).
Proof. exact (fun_ext (fun x : A => @lem4308808 A B x)). Qed.
Lemma lem4308810 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4308811 {A B : Type'} : (term1213 A B) = (term1213 A B).
Proof. exact (MK_COMB (@lem4308810 A) (@lem4308809 A B)). Qed.
Lemma lem4308812 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4308813 {A B : Type'} : (term1233 A B) = (term1233 A B).
Proof. exact (MK_COMB (@lem4308812) (@lem4308811 A B)). Qed.
Lemma lem4308814 {A B : Type'} : (term1235 A B) = (term1235 A B).
Proof. exact (MK_COMB (@lem4308813 A B) (@lem4308770 A B)). Qed.
Lemma lem4308823 {A B : Type'} (x''' : B) (t : type1413 A B) (x : A) : (term1236 A B x''' t x) = (term1236 A B x''' t x).
Proof. exact (eq_refl (term1236 A B x''' t x)). Qed.
Lemma lem4308824 {A B : Type'} (x''' : B) (t : type1413 A B) (x : A) : (term1238 A B x''' t x) = (term1238 A B x''' t x).
Proof. exact (MK_COMB (@lem4308823 A B x''' t x) (@lem4308814 A B)). Qed.
Lemma lem4308835 {A B : Type'} (x' : prod A B) (x : A) (x''' : B) : (term1239 A B x' x x''') = (term1239 A B x' x x''').
Proof. exact (eq_refl (term1239 A B x' x x''')). Qed.
Lemma lem4308836 {A B : Type'} (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : (term1241 A B x' x''' t x) = (term1241 A B x' x''' t x).
Proof. exact (MK_COMB (@lem4308835 A B x' x x''') (@lem4308824 A B x''' t x)). Qed.
Lemma lem4308847 {A B : Type'} (x' : prod A B) (x'' : A) (y : B) : (term1239 A B x' x'' y) = (term1239 A B x' x'' y).
Proof. exact (eq_refl (term1239 A B x' x'' y)). Qed.
Lemma lem4308848 {A B : Type'} (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : (term1243 A B x'' y x' x''' t x) = (term1243 A B x'' y x' x''' t x).
Proof. exact (MK_COMB (@lem4308847 A B x' x'' y) (@lem4308836 A B x' x''' t x)). Qed.
Lemma lem4308857 {A B : Type'} (y : B) (t : type1413 A B) (x'' : A) : (term1236 A B y t x'') = (term1236 A B y t x'').
Proof. exact (eq_refl (term1236 A B y t x'')). Qed.
Lemma lem4308858 {A B : Type'} (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : (term1245 A B x'' y x' x''' t x) = (term1245 A B x'' y x' x''' t x).
Proof. exact (MK_COMB (@lem4308857 A B y t x'') (@lem4308848 A B x'' y x' x''' t x)). Qed.
Lemma lem4308865 {A : Type'} (x'' : A) (s : A -> Prop) : (term1246 A x'' s) = (term1246 A x'' s).
Proof. exact (eq_refl (term1246 A x'' s)). Qed.
Lemma lem4308866 {A B : Type'} (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : (term1248 A B s x'' y x' x''' t x) = (term1248 A B s x'' y x' x''' t x).
Proof. exact (MK_COMB (@lem4308865 A x'' s) (@lem4308858 A B x'' y x' x''' t x)). Qed.
Lemma lem4308873 {A : Type'} (s : A -> Prop) (n : nat) : (term1077 A s n) = (term1077 A s n).
Proof. exact (eq_refl (term1077 A s n)). Qed.
Lemma lem4308875 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (_48808 : type621 A B) (h1 : _48808 = (term1300 A B)) : (term1165 A B s t) = (_48808 s t).
Proof. exact (SYM (@lem4308594 A B s t _48808 h1)). Qed.
Lemma lem4308876 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (_48808 : type621 A B) (h1 : _48808 = (term1300 A B)) : (term1165 A B s t) = (_48808 s t).
Proof. exact (@lem4308875 A B s t _48808 h1). Qed.
Lemma lem4308877 {A B : Type'} : (@GSPEC (prod A B)) = (@GSPEC (prod A B)).
Proof. exact (eq_refl (@GSPEC (prod A B))). Qed.
Lemma lem4308878 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (_48808 : type621 A B) (h1 : _48808 = (term1300 A B)) : (term1075 A B s t) = (term1342 A B _48808 s t).
Proof. exact (MK_COMB (@lem4308877 A B) (@lem4308876 A B s t _48808 h1)). Qed.
Lemma lem4308879 {A B : Type'} : (@HAS_SIZE (prod A B)) = (@HAS_SIZE (prod A B)).
Proof. exact (eq_refl (@HAS_SIZE (prod A B))). Qed.
Lemma lem4308880 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (_48808 : type621 A B) (h1 : _48808 = (term1300 A B)) : (term1343 A B s t) = (term1344 A B _48808 s t).
Proof. exact (MK_COMB (@lem4308879 A B) (@lem4308878 A B s t _48808 h1)). Qed.
Lemma lem4308881 {A B : Type'} (t : type1413 A B) (s : A -> Prop) (n : nat) (_48808 : type621 A B) (h1 : _48808 = (term1300 A B)) : (term1098 A B t s n) = (term1345 A B _48808 t s n).
Proof. exact (MK_COMB (@lem4308880 A B s t _48808 h1) (@lem4308873 A s n)). Qed.
Lemma lem4308896 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : A) (n : nat) : (term989 A B s t x n) = (term989 A B s t x n).
Proof. exact (eq_refl (term989 A B s t x n)). Qed.
Lemma lem4308897 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (n : nat) : (term983 A B s t n) = (term983 A B s t n).
Proof. exact (fun_ext (fun x : A => @lem4308896 A B s t x n)). Qed.
Lemma lem4308898 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4308899 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (n : nat) : (term581 A B s t n) = (term581 A B s t n).
Proof. exact (MK_COMB (@lem4308898 A) (@lem4308897 A B s t n)). Qed.
Lemma lem4308900 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4308901 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (n : nat) : (term1251 A B s t n) = (term1251 A B s t n).
Proof. exact (MK_COMB (@lem4308900) (@lem4308899 A B s t n)). Qed.
Lemma lem4308902 {A B : Type'} (t : type1413 A B) (s : A -> Prop) (n : nat) (_48808 : type621 A B) (h1 : _48808 = (term1300 A B)) : (term1097 A B t s n) = (term1346 A B _48808 t s n).
Proof. exact (MK_COMB (@lem4308901 A B s t n) (@lem4308881 A B t s n _48808 h1)). Qed.
Lemma lem4308903 {A B : Type'} (t : type1413 A B) (s : A -> Prop) (_48808 : type621 A B) (h1 : _48808 = (term1300 A B)) : (term1347 A B t s) = (term1348 A B _48808 t s).
Proof. exact (fun_ext (fun n : nat => @lem4308902 A B t s n _48808 h1)). Qed.
Lemma lem4308904 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4308905 {A B : Type'} (t : type1413 A B) (s : A -> Prop) (_48808 : type621 A B) (h1 : _48808 = (term1300 A B)) : (term1095 A B t s) = (term1349 A B _48808 t s).
Proof. exact (MK_COMB (@lem4308904) (@lem4308903 A B t s _48808 h1)). Qed.
Lemma lem4308906 {A B : Type'} (s : A -> Prop) (_48808 : type621 A B) (h1 : _48808 = (term1300 A B)) : (term1350 A B s) = (term1351 A B _48808 s).
Proof. exact (fun_ext (fun t : type1413 A B => @lem4308905 A B t s _48808 h1)). Qed.
Lemma lem4308907 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem4308908 {A B : Type'} (s : A -> Prop) (_48808 : type621 A B) (h1 : _48808 = (term1300 A B)) : (term1061 A B s) = (term1352 A B _48808 s).
Proof. exact (MK_COMB (@lem4308907 A B) (@lem4308906 A B s _48808 h1)). Qed.
Lemma lem4308909 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4308910 {A B : Type'} (s : A -> Prop) (_48808 : type621 A B) (h1 : _48808 = (term1300 A B)) : (term1063 A B s) = (term1353 A B _48808 s).
Proof. exact (MK_COMB (@lem4308909) (@lem4308908 A B s _48808 h1)). Qed.
Lemma lem4308911 {A B : Type'} (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) (_48808 : type621 A B) (h1 : _48808 = (term1300 A B)) : (term1250 A B s x'' y x' x''' t x) = (term1354 A B _48808 s x'' y x' x''' t x).
Proof. exact (MK_COMB (@lem4308910 A B s _48808 h1) (@lem4308866 A B s x'' y x' x''' t x)). Qed.
Lemma lem4308926 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x' : A) (n : nat) : (term989 A B s t x' n) = (term989 A B s t x' n).
Proof. exact (eq_refl (term989 A B s t x' n)). Qed.
Lemma lem4308927 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (n : nat) : (term983 A B s t n) = (term983 A B s t n).
Proof. exact (fun_ext (fun x' : A => @lem4308926 A B s t x' n)). Qed.
Lemma lem4308928 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4308929 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (n : nat) : (term581 A B s t n) = (term581 A B s t n).
Proof. exact (MK_COMB (@lem4308928 A) (@lem4308927 A B s t n)). Qed.
Lemma lem4308930 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4308931 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (n : nat) : (term1251 A B s t n) = (term1251 A B s t n).
Proof. exact (MK_COMB (@lem4308930) (@lem4308929 A B s t n)). Qed.
Lemma lem4308932 {A B : Type'} (n : nat) (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) (_48808 : type621 A B) (h1 : _48808 = (term1300 A B)) : (term1253 A B n s x'' y x' x''' t x) = (term1355 A B n _48808 s x'' y x' x''' t x).
Proof. exact (MK_COMB (@lem4308931 A B s t n) (@lem4308911 A B s x'' y x' x''' t x _48808 h1)). Qed.
Lemma lem4308941 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) : (term1254 A B t x n) = (term1254 A B t x n).
Proof. exact (eq_refl (term1254 A B t x n)). Qed.
Lemma lem4308942 {A B : Type'} (n : nat) (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) (_48808 : type621 A B) (h1 : _48808 = (term1300 A B)) : (term1256 A B n s x'' y x' x''' t x) = (term1356 A B n _48808 s x'' y x' x''' t x).
Proof. exact (MK_COMB (@lem4308941 A B t x n) (@lem4308932 A B n s x'' y x' x''' t x _48808 h1)). Qed.
Lemma lem4308953 {A : Type'} (m : nat) (s : A -> Prop) : (term1257 A m s) = (term1257 A m s).
Proof. exact (eq_refl (term1257 A m s)). Qed.
Lemma lem4308954 {A B : Type'} (m : nat) (n : nat) (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) (_48808 : type621 A B) (h1 : _48808 = (term1300 A B)) : (term1259 A B m n s x'' y x' x''' t x) = (term1357 A B m n _48808 s x'' y x' x''' t x).
Proof. exact (MK_COMB (@lem4308953 A m s) (@lem4308942 A B n s x'' y x' x''' t x _48808 h1)). Qed.
Lemma lem4308959 {A : Type'} (s : A -> Prop) : (term619 A s) = (term619 A s).
Proof. exact (eq_refl (term619 A s)). Qed.
Lemma lem4308960 {A B : Type'} (m : nat) (n : nat) (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) (_48808 : type621 A B) (h1 : _48808 = (term1300 A B)) : (term1261 A B m n s x'' y x' x''' t x) = (term1358 A B m n _48808 s x'' y x' x''' t x).
Proof. exact (MK_COMB (@lem4308959 A s) (@lem4308954 A B m n s x'' y x' x''' t x _48808 h1)). Qed.
Lemma lem4308969 {A : Type'} (x : A) (s : A -> Prop) : (term1262 A x s) = (term1262 A x s).
Proof. exact (eq_refl (term1262 A x s)). Qed.
Lemma lem4308970 {A B : Type'} (m : nat) (n : nat) (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) (_48808 : type621 A B) (h1 : _48808 = (term1300 A B)) : (term1263 A B m n s x'' y x' x''' t x) = (term1359 A B m n _48808 s x'' y x' x''' t x).
Proof. exact (MK_COMB (@lem4308969 A x s) (@lem4308960 A B m n s x'' y x' x''' t x _48808 h1)). Qed.
Lemma lem4308971 {A B : Type'} (n : nat) (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) (_48808 : type621 A B) (h1 : _48808 = (term1300 A B)) : (term1265 A B n s x'' y x' x''' t x) = (term1360 A B n _48808 s x'' y x' x''' t x).
Proof. exact (fun_ext (fun m : nat => @lem4308970 A B m n s x'' y x' x''' t x _48808 h1)). Qed.
Lemma lem4308972 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4308973 {A B : Type'} (n : nat) (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) (_48808 : type621 A B) (h1 : _48808 = (term1300 A B)) : (term1267 A B n s x'' y x' x''' t x) = (term1361 A B n _48808 s x'' y x' x''' t x).
Proof. exact (MK_COMB (@lem4308972) (@lem4308971 A B n s x'' y x' x''' t x _48808 h1)). Qed.
Lemma lem4308974 {A B : Type'} (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) (_48808 : type621 A B) (h1 : _48808 = (term1300 A B)) : (term1269 A B s x'' y x' x''' t x) = (term1362 A B _48808 s x'' y x' x''' t x).
Proof. exact (fun_ext (fun n : nat => @lem4308973 A B n s x'' y x' x''' t x _48808 h1)). Qed.
Lemma lem4308975 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4308976 {A B : Type'} (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) (_48808 : type621 A B) (h1 : _48808 = (term1300 A B)) : (term1271 A B s x'' y x' x''' t x) = (term1363 A B _48808 s x'' y x' x''' t x).
Proof. exact (MK_COMB (@lem4308975) (@lem4308974 A B s x'' y x' x''' t x _48808 h1)). Qed.
Lemma lem4308977 {A B : Type'} (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) (_48808 : type621 A B) (h1 : _48808 = (term1300 A B)) : (term1273 A B x'' y x' x''' t x) = (term1364 A B _48808 x'' y x' x''' t x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4308976 A B s x'' y x' x''' t x _48808 h1)). Qed.
Lemma lem4308978 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4308979 {A B : Type'} (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) (_48808 : type621 A B) (h1 : _48808 = (term1300 A B)) : (term1275 A B x'' y x' x''' t x) = (term1365 A B _48808 x'' y x' x''' t x).
Proof. exact (MK_COMB (@lem4308978 A) (@lem4308977 A B x'' y x' x''' t x _48808 h1)). Qed.
Lemma lem4308980 {A B : Type'} (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) (_48808 : type621 A B) (h1 : _48808 = (term1300 A B)) : (term1277 A B y x' x''' t x) = (term1366 A B _48808 y x' x''' t x).
Proof. exact (fun_ext (fun x'' : A => @lem4308979 A B x'' y x' x''' t x _48808 h1)). Qed.
Lemma lem4308981 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4308982 {A B : Type'} (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) (_48808 : type621 A B) (h1 : _48808 = (term1300 A B)) : (term1279 A B y x' x''' t x) = (term1367 A B _48808 y x' x''' t x).
Proof. exact (MK_COMB (@lem4308981 A) (@lem4308980 A B y x' x''' t x _48808 h1)). Qed.
Lemma lem4308983 {A B : Type'} (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) (_48808 : type621 A B) (h1 : _48808 = (term1300 A B)) : (term1281 A B x' x''' t x) = (term1368 A B _48808 x' x''' t x).
Proof. exact (fun_ext (fun y : B => @lem4308982 A B y x' x''' t x _48808 h1)). Qed.
Lemma lem4308984 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4308985 {A B : Type'} (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) (_48808 : type621 A B) (h1 : _48808 = (term1300 A B)) : (term1283 A B x' x''' t x) = (term1369 A B _48808 x' x''' t x).
Proof. exact (MK_COMB (@lem4308984 B) (@lem4308983 A B x' x''' t x _48808 h1)). Qed.
Lemma lem4308986 {A B : Type'} (x''' : B) (t : type1413 A B) (x : A) (_48808 : type621 A B) (h1 : _48808 = (term1300 A B)) : (term1285 A B x''' t x) = (term1370 A B _48808 x''' t x).
Proof. exact (fun_ext (fun x' : prod A B => @lem4308985 A B x' x''' t x _48808 h1)). Qed.
Lemma lem4308987 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem4308988 {A B : Type'} (x''' : B) (t : type1413 A B) (x : A) (_48808 : type621 A B) (h1 : _48808 = (term1300 A B)) : (term1287 A B x''' t x) = (term1371 A B _48808 x''' t x).
Proof. exact (MK_COMB (@lem4308987 A B) (@lem4308986 A B x''' t x _48808 h1)). Qed.
Lemma lem4308989 {A B : Type'} (t : type1413 A B) (x : A) (_48808 : type621 A B) (h1 : _48808 = (term1300 A B)) : (term1289 A B t x) = (term1372 A B _48808 t x).
Proof. exact (fun_ext (fun x''' : B => @lem4308988 A B x''' t x _48808 h1)). Qed.
Lemma lem4308990 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4308991 {A B : Type'} (t : type1413 A B) (x : A) (_48808 : type621 A B) (h1 : _48808 = (term1300 A B)) : (term1291 A B t x) = (term1373 A B _48808 t x).
Proof. exact (MK_COMB (@lem4308990 B) (@lem4308989 A B t x _48808 h1)). Qed.
Lemma lem4308992 {A B : Type'} (x : A) (_48808 : type621 A B) (h1 : _48808 = (term1300 A B)) : (term1293 A B x) = (term1374 A B _48808 x).
Proof. exact (fun_ext (fun t : type1413 A B => @lem4308991 A B t x _48808 h1)). Qed.
Lemma lem4308993 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem4308994 {A B : Type'} (x : A) (_48808 : type621 A B) (h1 : _48808 = (term1300 A B)) : (term1295 A B x) = (term1375 A B _48808 x).
Proof. exact (MK_COMB (@lem4308993 A B) (@lem4308992 A B x _48808 h1)). Qed.
Lemma lem4308995 {A B : Type'} (_48808 : type621 A B) (h1 : _48808 = (term1300 A B)) : (term1297 A B) = (term1376 A B _48808).
Proof. exact (fun_ext (fun x : A => @lem4308994 A B x _48808 h1)). Qed.
Lemma lem4308996 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4308997 {A B : Type'} (_48808 : type621 A B) (h1 : _48808 = (term1300 A B)) : (term1299 A B) = (term1377 A B _48808).
Proof. exact (MK_COMB (@lem4308996 A) (@lem4308995 A B _48808 h1)). Qed.
Lemma lem4308998 {A B : Type'} (_48808 : type621 A B) : term1378 A B _48808.
Proof. exact (fun h0 : _48808 = (term1300 A B) => @lem4308997 A B _48808 h0). Qed.
Lemma lem4308999 {A B : Type'} : term1379 A B.
Proof. exact (fun _48808 : type621 A B => @lem4308998 A B _48808). Qed.
Lemma lem4309001 {_3603 : Type'} (P : Prop) (c : _3603) (Q : _3603 -> Prop) : term1380 _3603 P c Q.
Proof. exact (EQ_MP (@lem20230 _3603 P c Q) (@lem0)). Qed.
Lemma lem4309002 {A B : Type'} (P : Prop) (c : type621 A B) (Q : type130 A B) : term1381 A B P c Q.
Proof. exact (@lem4309001 (type621 A B) P c Q). Qed.
Lemma lem4309003 {A B : Type'} : term1382 A B.
Proof. exact (@lem4309002 A B (term1299 A B) (term1300 A B) (term1383 A B)). Qed.
Lemma lem4309004 {A B : Type'} (_48808 : type621 A B) : (term1384 A B _48808) = (term1377 A B _48808).
Proof. exact (eq_refl (term1384 A B _48808)). Qed.
Lemma lem4309005 {A B : Type'} : (term1385 A B) = (term1385 A B).
Proof. exact (eq_refl (term1385 A B)). Qed.
Lemma lem4309006 {A B : Type'} (_48808 : type621 A B) : ((term1299 A B) = (term1384 A B _48808)) = ((term1299 A B) = (term1377 A B _48808)).
Proof. exact (MK_COMB (@lem4309005 A B) (@lem4309004 A B _48808)). Qed.
Lemma lem4309007 {A B : Type'} (_48808 : type621 A B) : (term1386 A B _48808) = (term1386 A B _48808).
Proof. exact (eq_refl (term1386 A B _48808)). Qed.
Lemma lem4309008 {A B : Type'} (_48808 : type621 A B) : (term1387 A B _48808) = (term1378 A B _48808).
Proof. exact (MK_COMB (@lem4309007 A B _48808) (@lem4309006 A B _48808)). Qed.
Lemma lem4309009 {A B : Type'} : (term1388 A B) = (term1389 A B).
Proof. exact (fun_ext (fun _48808 : type621 A B => @lem4309008 A B _48808)). Qed.
Lemma lem4309010 {A B : Type'} : (@all ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> Prop)) = (@all ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> Prop))). Qed.
Lemma lem4309011 {A B : Type'} : (term1390 A B) = (term1379 A B).
Proof. exact (MK_COMB (@lem4309010 A B) (@lem4309009 A B)). Qed.
Lemma lem4309012 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4309013 {A B : Type'} : (term1391 A B) = (term1392 A B).
Proof. exact (MK_COMB (@lem4309012) (@lem4309011 A B)). Qed.
Lemma lem4309014 {A B : Type'} (_48808 : type621 A B) : (term1384 A B _48808) = (term1377 A B _48808).
Proof. exact (eq_refl (term1384 A B _48808)). Qed.
Lemma lem4309015 {A B : Type'} (_48808 : type621 A B) : (term1386 A B _48808) = (term1386 A B _48808).
Proof. exact (eq_refl (term1386 A B _48808)). Qed.
Lemma lem4309016 {A B : Type'} (_48808 : type621 A B) : (term1393 A B _48808) = (term1394 A B _48808).
Proof. exact (MK_COMB (@lem4309015 A B _48808) (@lem4309014 A B _48808)). Qed.
Lemma lem4309017 {A B : Type'} : (term1395 A B) = (term1396 A B).
Proof. exact (fun_ext (fun _48808 : type621 A B => @lem4309016 A B _48808)). Qed.
Lemma lem4309018 {A B : Type'} : (@all ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> Prop)) = (@all ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> Prop))). Qed.
Lemma lem4309019 {A B : Type'} : (term1397 A B) = (term1398 A B).
Proof. exact (MK_COMB (@lem4309018 A B) (@lem4309017 A B)). Qed.
Lemma lem4309020 {A B : Type'} : (term1385 A B) = (term1385 A B).
Proof. exact (eq_refl (term1385 A B)). Qed.
Lemma lem4309021 {A B : Type'} : ((term1299 A B) = (term1397 A B)) = ((term1299 A B) = (term1398 A B)).
Proof. exact (MK_COMB (@lem4309020 A B) (@lem4309019 A B)). Qed.
Lemma lem4309022 {A B : Type'} : (term1382 A B) = (term1399 A B).
Proof. exact (MK_COMB (@lem4309013 A B) (@lem4309021 A B)). Qed.
Lemma lem4309023 {A B : Type'} : term1399 A B.
Proof. exact (EQ_MP (@lem4309022 A B) (@lem4309003 A B)). Qed.
Lemma lem4309024 {A B : Type'} : (term1299 A B) = (term1398 A B).
Proof. exact (@lem4309023 A B (@lem4308999 A B)). Qed.
Lemma lem4309026 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term1400 _3571 _3575 t)) = (term1401 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem4309027 {A B : Type'} (s : type621 A B) (t : type621 A B) : (s = (term1402 A B t)) = (term1403 A B s t).
Proof. exact (@lem4309026 (type466 A B) (A -> Prop) s t). Qed.
Lemma lem4309028 {A B : Type'} (_48808 : type621 A B) : (_48808 = (term1404 A B)) = (term1405 A B _48808).
Proof. exact (@lem4309027 A B _48808 (term1300 A B)). Qed.
Lemma lem4309029 {A B : Type'} (s : A -> Prop) : (term1301 A B s) = (term1302 A B s).
Proof. exact (eq_refl (term1301 A B s)). Qed.
Lemma lem4309030 {A B : Type'} : (term1404 A B) = (term1300 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4309029 A B s)). Qed.
Lemma lem4309031 {A B : Type'} (_48808 : type621 A B) : (@eq ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> Prop) _48808) = (@eq ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> Prop) _48808).
Proof. exact (eq_refl (@eq ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> Prop) _48808)). Qed.
Lemma lem4309032 {A B : Type'} (_48808 : type621 A B) : (_48808 = (term1404 A B)) = (_48808 = (term1300 A B)).
Proof. exact (MK_COMB (@lem4309031 A B _48808) (@lem4309030 A B)). Qed.
Lemma lem4309033 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4309034 {A B : Type'} (_48808 : type621 A B) : (term1406 A B _48808) = (term1407 A B _48808).
Proof. exact (MK_COMB (@lem4309033) (@lem4309032 A B _48808)). Qed.
Lemma lem4309035 {A B : Type'} (s : A -> Prop) : (term1301 A B s) = (term1302 A B s).
Proof. exact (eq_refl (term1301 A B s)). Qed.
Lemma lem4309036 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1303 A B _48808 s) = (term1303 A B _48808 s).
Proof. exact (eq_refl (term1303 A B _48808 s)). Qed.
Lemma lem4309037 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : ((_48808 s) = (term1301 A B s)) = ((_48808 s) = (term1302 A B s)).
Proof. exact (MK_COMB (@lem4309036 A B _48808 s) (@lem4309035 A B s)). Qed.
Lemma lem4309038 {A B : Type'} (_48808 : type621 A B) : (term1408 A B _48808) = (term1409 A B _48808).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4309037 A B _48808 s)). Qed.
Lemma lem4309039 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4309040 {A B : Type'} (_48808 : type621 A B) : (term1405 A B _48808) = (term1410 A B _48808).
Proof. exact (MK_COMB (@lem4309039 A) (@lem4309038 A B _48808)). Qed.
Lemma lem4309041 {A B : Type'} (_48808 : type621 A B) : ((_48808 = (term1404 A B)) = (term1405 A B _48808)) = ((_48808 = (term1300 A B)) = (term1410 A B _48808)).
Proof. exact (MK_COMB (@lem4309034 A B _48808) (@lem4309040 A B _48808)). Qed.
Lemma lem4309042 {A B : Type'} (_48808 : type621 A B) : (_48808 = (term1300 A B)) = (term1410 A B _48808).
Proof. exact (EQ_MP (@lem4309041 A B _48808) (@lem4309028 A B _48808)). Qed.
Lemma lem4309044 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term1400 _3571 _3575 t)) = (term1401 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem4309045 {A B : Type'} (s : type466 A B) (t : type466 A B) : (s = (term1411 A B t)) = (term1412 A B s t).
Proof. exact (@lem4309044 (type1210 A B) (type1413 A B) s t). Qed.
Lemma lem4309046 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : ((_48808 s) = (term1413 A B s)) = (term1414 A B _48808 s).
Proof. exact (@lem4309045 A B (_48808 s) (term1302 A B s)). Qed.
Lemma lem4309047 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term1304 A B s t) = (term1165 A B s t).
Proof. exact (eq_refl (term1304 A B s t)). Qed.
Lemma lem4309048 {A B : Type'} (s : A -> Prop) : (term1413 A B s) = (term1302 A B s).
Proof. exact (fun_ext (fun t : type1413 A B => @lem4309047 A B s t)). Qed.
Lemma lem4309049 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1303 A B _48808 s) = (term1303 A B _48808 s).
Proof. exact (eq_refl (term1303 A B _48808 s)). Qed.
Lemma lem4309050 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : ((_48808 s) = (term1413 A B s)) = ((_48808 s) = (term1302 A B s)).
Proof. exact (MK_COMB (@lem4309049 A B _48808 s) (@lem4309048 A B s)). Qed.
Lemma lem4309051 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4309052 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1415 A B _48808 s) = (term1416 A B _48808 s).
Proof. exact (MK_COMB (@lem4309051) (@lem4309050 A B _48808 s)). Qed.
Lemma lem4309053 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term1304 A B s t) = (term1165 A B s t).
Proof. exact (eq_refl (term1304 A B s t)). Qed.
Lemma lem4309054 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1305 A B _48808 s t) = (term1305 A B _48808 s t).
Proof. exact (eq_refl (term1305 A B _48808 s t)). Qed.
Lemma lem4309055 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : ((_48808 s t) = (term1304 A B s t)) = ((_48808 s t) = (term1165 A B s t)).
Proof. exact (MK_COMB (@lem4309054 A B _48808 s t) (@lem4309053 A B s t)). Qed.
Lemma lem4309056 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1417 A B _48808 s) = (term1418 A B _48808 s).
Proof. exact (fun_ext (fun t : type1413 A B => @lem4309055 A B _48808 s t)). Qed.
Lemma lem4309057 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem4309058 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1414 A B _48808 s) = (term1419 A B _48808 s).
Proof. exact (MK_COMB (@lem4309057 A B) (@lem4309056 A B _48808 s)). Qed.
Lemma lem4309059 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (((_48808 s) = (term1413 A B s)) = (term1414 A B _48808 s)) = (((_48808 s) = (term1302 A B s)) = (term1419 A B _48808 s)).
Proof. exact (MK_COMB (@lem4309052 A B _48808 s) (@lem4309058 A B _48808 s)). Qed.
Lemma lem4309060 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : ((_48808 s) = (term1302 A B s)) = (term1419 A B _48808 s).
Proof. exact (EQ_MP (@lem4309059 A B _48808 s) (@lem4309046 A B _48808 s)). Qed.
Lemma lem4309062 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term1400 _3571 _3575 t)) = (term1401 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem4309063 {A B : Type'} (s : type1210 A B) (t : type1210 A B) : (s = (term1420 A B t)) = (term1421 A B s t).
Proof. exact (@lem4309062 Prop (prod A B) s t). Qed.
Lemma lem4309064 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : ((_48808 s t) = (term1422 A B s t)) = (term1423 A B _48808 s t).
Proof. exact (@lem4309063 A B (_48808 s t) (term1165 A B s t)). Qed.
Lemma lem4309065 {A B : Type'} (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1424 A B s t GEN_PVAR_121) = (term1163 A B GEN_PVAR_121 s t).
Proof. exact (eq_refl (term1424 A B s t GEN_PVAR_121)). Qed.
Lemma lem4309066 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term1422 A B s t) = (term1165 A B s t).
Proof. exact (fun_ext (fun GEN_PVAR_121 : prod A B => @lem4309065 A B GEN_PVAR_121 s t)). Qed.
Lemma lem4309067 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1305 A B _48808 s t) = (term1305 A B _48808 s t).
Proof. exact (eq_refl (term1305 A B _48808 s t)). Qed.
Lemma lem4309068 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : ((_48808 s t) = (term1422 A B s t)) = ((_48808 s t) = (term1165 A B s t)).
Proof. exact (MK_COMB (@lem4309067 A B _48808 s t) (@lem4309066 A B s t)). Qed.
Lemma lem4309069 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4309070 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1425 A B _48808 s t) = (term1426 A B _48808 s t).
Proof. exact (MK_COMB (@lem4309069) (@lem4309068 A B _48808 s t)). Qed.
Lemma lem4309071 {A B : Type'} (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1424 A B s t GEN_PVAR_121) = (term1163 A B GEN_PVAR_121 s t).
Proof. exact (eq_refl (term1424 A B s t GEN_PVAR_121)). Qed.
Lemma lem4309072 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) (GEN_PVAR_121 : prod A B) : (term1427 A B _48808 s t GEN_PVAR_121) = (term1427 A B _48808 s t GEN_PVAR_121).
Proof. exact (eq_refl (term1427 A B _48808 s t GEN_PVAR_121)). Qed.
Lemma lem4309073 {A B : Type'} (_48808 : type621 A B) (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) : ((_48808 s t GEN_PVAR_121) = (term1424 A B s t GEN_PVAR_121)) = ((_48808 s t GEN_PVAR_121) = (term1163 A B GEN_PVAR_121 s t)).
Proof. exact (MK_COMB (@lem4309072 A B _48808 s t GEN_PVAR_121) (@lem4309071 A B GEN_PVAR_121 s t)). Qed.
Lemma lem4309074 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1428 A B _48808 s t) = (term1429 A B _48808 s t).
Proof. exact (fun_ext (fun GEN_PVAR_121 : prod A B => @lem4309073 A B _48808 GEN_PVAR_121 s t)). Qed.
Lemma lem4309075 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem4309076 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1423 A B _48808 s t) = (term1430 A B _48808 s t).
Proof. exact (MK_COMB (@lem4309075 A B) (@lem4309074 A B _48808 s t)). Qed.
Lemma lem4309077 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (((_48808 s t) = (term1422 A B s t)) = (term1423 A B _48808 s t)) = (((_48808 s t) = (term1165 A B s t)) = (term1430 A B _48808 s t)).
Proof. exact (MK_COMB (@lem4309070 A B _48808 s t) (@lem4309076 A B _48808 s t)). Qed.
Lemma lem4309078 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : ((_48808 s t) = (term1165 A B s t)) = (term1430 A B _48808 s t).
Proof. exact (EQ_MP (@lem4309077 A B _48808 s t) (@lem4309064 A B _48808 s t)). Qed.
Lemma lem4309079 {A B : Type'} (_48808 : type621 A B) (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) : ((_48808 s t GEN_PVAR_121) = (term1163 A B GEN_PVAR_121 s t)) = ((_48808 s t GEN_PVAR_121) = (term1163 A B GEN_PVAR_121 s t)).
Proof. exact (eq_refl ((_48808 s t GEN_PVAR_121) = (term1163 A B GEN_PVAR_121 s t))). Qed.
Lemma lem4309080 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1429 A B _48808 s t) = (term1429 A B _48808 s t).
Proof. exact (fun_ext (fun GEN_PVAR_121 : prod A B => @lem4309079 A B _48808 GEN_PVAR_121 s t)). Qed.
Lemma lem4309081 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem4309082 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1430 A B _48808 s t) = (term1430 A B _48808 s t).
Proof. exact (MK_COMB (@lem4309081 A B) (@lem4309080 A B _48808 s t)). Qed.
Lemma lem4309083 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : ((_48808 s t) = (term1165 A B s t)) = (term1430 A B _48808 s t).
Proof. exact (TRANS (@lem4309078 A B _48808 s t) (@lem4309082 A B _48808 s t)). Qed.
Lemma lem4309084 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1418 A B _48808 s) = (term1431 A B _48808 s).
Proof. exact (fun_ext (fun t : type1413 A B => @lem4309083 A B _48808 s t)). Qed.
Lemma lem4309085 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem4309086 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1419 A B _48808 s) = (term1432 A B _48808 s).
Proof. exact (MK_COMB (@lem4309085 A B) (@lem4309084 A B _48808 s)). Qed.
Lemma lem4309087 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : ((_48808 s) = (term1302 A B s)) = (term1432 A B _48808 s).
Proof. exact (TRANS (@lem4309060 A B _48808 s) (@lem4309086 A B _48808 s)). Qed.
Lemma lem4309088 {A B : Type'} (_48808 : type621 A B) : (term1409 A B _48808) = (term1433 A B _48808).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4309087 A B _48808 s)). Qed.
Lemma lem4309089 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4309090 {A B : Type'} (_48808 : type621 A B) : (term1410 A B _48808) = (term1434 A B _48808).
Proof. exact (MK_COMB (@lem4309089 A) (@lem4309088 A B _48808)). Qed.
Lemma lem4309091 {A B : Type'} (_48808 : type621 A B) : (_48808 = (term1300 A B)) = (term1434 A B _48808).
Proof. exact (TRANS (@lem4309042 A B _48808) (@lem4309090 A B _48808)). Qed.
Lemma lem4309092 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4309093 {A B : Type'} (_48808 : type621 A B) : (term1386 A B _48808) = (term1435 A B _48808).
Proof. exact (MK_COMB (@lem4309092) (@lem4309091 A B _48808)). Qed.
Lemma lem4309094 {A B : Type'} (_48808 : type621 A B) : (term1377 A B _48808) = (term1377 A B _48808).
Proof. exact (eq_refl (term1377 A B _48808)). Qed.
Lemma lem4309095 {A B : Type'} (_48808 : type621 A B) : (term1394 A B _48808) = (term1436 A B _48808).
Proof. exact (MK_COMB (@lem4309093 A B _48808) (@lem4309094 A B _48808)). Qed.
Lemma lem4309096 {A B : Type'} : (term1396 A B) = (term1437 A B).
Proof. exact (fun_ext (fun _48808 : type621 A B => @lem4309095 A B _48808)). Qed.
Lemma lem4309097 {A B : Type'} : (@all ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> Prop)) = (@all ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> Prop))). Qed.
Lemma lem4309098 {A B : Type'} : (term1398 A B) = (term1438 A B).
Proof. exact (MK_COMB (@lem4309097 A B) (@lem4309096 A B)). Qed.
Lemma lem4309099 {A B : Type'} : (term1385 A B) = (term1385 A B).
Proof. exact (eq_refl (term1385 A B)). Qed.
Lemma lem4309100 {A B : Type'} : ((term1299 A B) = (term1398 A B)) = ((term1299 A B) = (term1438 A B)).
Proof. exact (MK_COMB (@lem4309099 A B) (@lem4309098 A B)). Qed.
Lemma lem4309103 {A B : Type'} : (term1299 A B) = (term1438 A B).
Proof. exact (EQ_MP (@lem4309100 A B) (@lem4309024 A B)). Qed.
Lemma lem4309104 {A B : Type'} : (term1298 A B) = (term1438 A B).
Proof. exact (TRANS (@lem4308581 A B) (@lem4309103 A B)). Qed.
Lemma lem4309113 {A B : Type'} (x : prod A B) (a : prod A B) (y : B) (b : B) : (((@pair (prod A B) B x y) = (@pair (prod A B) B a b)) = (term1306 A B x a y b)) = (((@pair (prod A B) B x y) = (@pair (prod A B) B a b)) = (term1306 A B x a y b)).
Proof. exact (eq_refl (((@pair (prod A B) B x y) = (@pair (prod A B) B a b)) = (term1306 A B x a y b))). Qed.
Lemma lem4309114 {A B : Type'} (x : prod A B) (a : prod A B) (y : B) : (term1307 A B x a y) = (term1307 A B x a y).
Proof. exact (fun_ext (fun b : B => @lem4309113 A B x a y b)). Qed.
Lemma lem4309115 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4309116 {A B : Type'} (x : prod A B) (a : prod A B) (y : B) : (term1308 A B x a y) = (term1308 A B x a y).
Proof. exact (MK_COMB (@lem4309115 B) (@lem4309114 A B x a y)). Qed.
Lemma lem4309117 {A B : Type'} (x : prod A B) (y : B) : (term1309 A B x y) = (term1309 A B x y).
Proof. exact (fun_ext (fun a : prod A B => @lem4309116 A B x a y)). Qed.
Lemma lem4309118 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem4309119 {A B : Type'} (x : prod A B) (y : B) : (term1310 A B x y) = (term1310 A B x y).
Proof. exact (MK_COMB (@lem4309118 A B) (@lem4309117 A B x y)). Qed.
Lemma lem4309120 {A B : Type'} (x : prod A B) : (term1311 A B x) = (term1311 A B x).
Proof. exact (fun_ext (fun y : B => @lem4309119 A B x y)). Qed.
Lemma lem4309121 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4309122 {A B : Type'} (x : prod A B) : (term1312 A B x) = (term1312 A B x).
Proof. exact (MK_COMB (@lem4309121 B) (@lem4309120 A B x)). Qed.
Lemma lem4309123 {A B : Type'} : (term1313 A B) = (term1313 A B).
Proof. exact (fun_ext (fun x : prod A B => @lem4309122 A B x)). Qed.
Lemma lem4309124 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem4309125 {A B : Type'} : (term1215 A B) = (term1215 A B).
Proof. exact (MK_COMB (@lem4309124 A B) (@lem4309123 A B)). Qed.
Lemma lem4309126 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4309127 {A B : Type'} : (term1223 A B) = (term1223 A B).
Proof. exact (MK_COMB (@lem4309126) (@lem4309125 A B)). Qed.
Lemma lem4309136 {B : Type'} (x : nat) (a : nat) (y : B) (b : B) : (((@pair nat B x y) = (@pair nat B a b)) = (term1314 B x a y b)) = (((@pair nat B x y) = (@pair nat B a b)) = (term1314 B x a y b)).
Proof. exact (eq_refl (((@pair nat B x y) = (@pair nat B a b)) = (term1314 B x a y b))). Qed.
Lemma lem4309137 {B : Type'} (x : nat) (a : nat) (y : B) : (term1315 B x a y) = (term1315 B x a y).
Proof. exact (fun_ext (fun b : B => @lem4309136 B x a y b)). Qed.
Lemma lem4309138 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4309139 {B : Type'} (x : nat) (a : nat) (y : B) : (term1316 B x a y) = (term1316 B x a y).
Proof. exact (MK_COMB (@lem4309138 B) (@lem4309137 B x a y)). Qed.
Lemma lem4309140 {B : Type'} (x : nat) (y : B) : (term1317 B x y) = (term1317 B x y).
Proof. exact (fun_ext (fun a : nat => @lem4309139 B x a y)). Qed.
Lemma lem4309141 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4309142 {B : Type'} (x : nat) (y : B) : (term1318 B x y) = (term1318 B x y).
Proof. exact (MK_COMB (@lem4309141) (@lem4309140 B x y)). Qed.
Lemma lem4309143 {B : Type'} (x : nat) : (term1319 B x) = (term1319 B x).
Proof. exact (fun_ext (fun y : B => @lem4309142 B x y)). Qed.
Lemma lem4309144 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4309145 {B : Type'} (x : nat) : (term1320 B x) = (term1320 B x).
Proof. exact (MK_COMB (@lem4309144 B) (@lem4309143 B x)). Qed.
Lemma lem4309146 {B : Type'} : (term1321 B) = (term1321 B).
Proof. exact (fun_ext (fun x : nat => @lem4309145 B x)). Qed.
Lemma lem4309147 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4309148 {B : Type'} : (term1214 B) = (term1214 B).
Proof. exact (MK_COMB (@lem4309147) (@lem4309146 B)). Qed.
Lemma lem4309149 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4309150 {B : Type'} : (term1224 B) = (term1224 B).
Proof. exact (MK_COMB (@lem4309149) (@lem4309148 B)). Qed.
Lemma lem4309151 {A B : Type'} : (term1226 A B) = (term1226 A B).
Proof. exact (MK_COMB (@lem4309150 B) (@lem4309127 A B)). Qed.
Lemma lem4309160 {A B : Type'} (x : A) (a : A) (y : prod A B) (b : prod A B) : (((@pair A (prod A B) x y) = (@pair A (prod A B) a b)) = (term1322 A B x a y b)) = (((@pair A (prod A B) x y) = (@pair A (prod A B) a b)) = (term1322 A B x a y b)).
Proof. exact (eq_refl (((@pair A (prod A B) x y) = (@pair A (prod A B) a b)) = (term1322 A B x a y b))). Qed.
Lemma lem4309161 {A B : Type'} (x : A) (a : A) (y : prod A B) : (term1323 A B x a y) = (term1323 A B x a y).
Proof. exact (fun_ext (fun b : prod A B => @lem4309160 A B x a y b)). Qed.
Lemma lem4309162 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem4309163 {A B : Type'} (x : A) (a : A) (y : prod A B) : (term1324 A B x a y) = (term1324 A B x a y).
Proof. exact (MK_COMB (@lem4309162 A B) (@lem4309161 A B x a y)). Qed.
Lemma lem4309164 {A B : Type'} (x : A) (y : prod A B) : (term1325 A B x y) = (term1325 A B x y).
Proof. exact (fun_ext (fun a : A => @lem4309163 A B x a y)). Qed.
Lemma lem4309165 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4309166 {A B : Type'} (x : A) (y : prod A B) : (term1326 A B x y) = (term1326 A B x y).
Proof. exact (MK_COMB (@lem4309165 A) (@lem4309164 A B x y)). Qed.
Lemma lem4309167 {A B : Type'} (x : A) : (term1327 A B x) = (term1327 A B x).
Proof. exact (fun_ext (fun y : prod A B => @lem4309166 A B x y)). Qed.
Lemma lem4309168 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem4309169 {A B : Type'} (x : A) : (term1328 A B x) = (term1328 A B x).
Proof. exact (MK_COMB (@lem4309168 A B) (@lem4309167 A B x)). Qed.
Lemma lem4309170 {A B : Type'} : (term1329 A B) = (term1329 A B).
Proof. exact (fun_ext (fun x : A => @lem4309169 A B x)). Qed.
Lemma lem4309171 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4309172 {A B : Type'} : (term1217 A B) = (term1217 A B).
Proof. exact (MK_COMB (@lem4309171 A) (@lem4309170 A B)). Qed.
Lemma lem4309173 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4309174 {A B : Type'} : (term1227 A B) = (term1227 A B).
Proof. exact (MK_COMB (@lem4309173) (@lem4309172 A B)). Qed.
Lemma lem4309175 {A B : Type'} : (term1229 A B) = (term1229 A B).
Proof. exact (MK_COMB (@lem4309174 A B) (@lem4309151 A B)). Qed.
Lemma lem4309184 {A : Type'} (x : A) (a : A) (y : nat) (b : nat) : (((@pair A nat x y) = (@pair A nat a b)) = (term1330 A x a y b)) = (((@pair A nat x y) = (@pair A nat a b)) = (term1330 A x a y b)).
Proof. exact (eq_refl (((@pair A nat x y) = (@pair A nat a b)) = (term1330 A x a y b))). Qed.
Lemma lem4309185 {A : Type'} (x : A) (a : A) (y : nat) : (term1331 A x a y) = (term1331 A x a y).
Proof. exact (fun_ext (fun b : nat => @lem4309184 A x a y b)). Qed.
Lemma lem4309186 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4309187 {A : Type'} (x : A) (a : A) (y : nat) : (term1332 A x a y) = (term1332 A x a y).
Proof. exact (MK_COMB (@lem4309186) (@lem4309185 A x a y)). Qed.
Lemma lem4309188 {A : Type'} (x : A) (y : nat) : (term1333 A x y) = (term1333 A x y).
Proof. exact (fun_ext (fun a : A => @lem4309187 A x a y)). Qed.
Lemma lem4309189 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4309190 {A : Type'} (x : A) (y : nat) : (term1334 A x y) = (term1334 A x y).
Proof. exact (MK_COMB (@lem4309189 A) (@lem4309188 A x y)). Qed.
Lemma lem4309191 {A : Type'} (x : A) : (term1335 A x) = (term1335 A x).
Proof. exact (fun_ext (fun y : nat => @lem4309190 A x y)). Qed.
Lemma lem4309192 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4309193 {A : Type'} (x : A) : (term1336 A x) = (term1336 A x).
Proof. exact (MK_COMB (@lem4309192) (@lem4309191 A x)). Qed.
Lemma lem4309194 {A : Type'} : (term1337 A) = (term1337 A).
Proof. exact (fun_ext (fun x : A => @lem4309193 A x)). Qed.
Lemma lem4309195 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4309196 {A : Type'} : (term1216 A) = (term1216 A).
Proof. exact (MK_COMB (@lem4309195 A) (@lem4309194 A)). Qed.
Lemma lem4309197 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4309198 {A : Type'} : (term1230 A) = (term1230 A).
Proof. exact (MK_COMB (@lem4309197) (@lem4309196 A)). Qed.
Lemma lem4309199 {A B : Type'} : (term1232 A B) = (term1232 A B).
Proof. exact (MK_COMB (@lem4309198 A) (@lem4309175 A B)). Qed.
Lemma lem4309208 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (((@pair A B x y) = (@pair A B a b)) = (term1085 A B x a y b)) = (((@pair A B x y) = (@pair A B a b)) = (term1085 A B x a y b)).
Proof. exact (eq_refl (((@pair A B x y) = (@pair A B a b)) = (term1085 A B x a y b))). Qed.
Lemma lem4309209 {A B : Type'} (x : A) (a : A) (y : B) : (term1338 A B x a y) = (term1338 A B x a y).
Proof. exact (fun_ext (fun b : B => @lem4309208 A B x a y b)). Qed.
Lemma lem4309210 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4309211 {A B : Type'} (x : A) (a : A) (y : B) : (term1083 A B x a y) = (term1083 A B x a y).
Proof. exact (MK_COMB (@lem4309210 B) (@lem4309209 A B x a y)). Qed.
Lemma lem4309212 {A B : Type'} (x : A) (y : B) : (term1339 A B x y) = (term1339 A B x y).
Proof. exact (fun_ext (fun a : A => @lem4309211 A B x a y)). Qed.
Lemma lem4309213 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4309214 {A B : Type'} (x : A) (y : B) : (term1081 A B x y) = (term1081 A B x y).
Proof. exact (MK_COMB (@lem4309213 A) (@lem4309212 A B x y)). Qed.
Lemma lem4309215 {A B : Type'} (x : A) : (term1340 A B x) = (term1340 A B x).
Proof. exact (fun_ext (fun y : B => @lem4309214 A B x y)). Qed.
Lemma lem4309216 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4309217 {A B : Type'} (x : A) : (term1079 A B x) = (term1079 A B x).
Proof. exact (MK_COMB (@lem4309216 B) (@lem4309215 A B x)). Qed.
Lemma lem4309218 {A B : Type'} : (term1341 A B) = (term1341 A B).
Proof. exact (fun_ext (fun x : A => @lem4309217 A B x)). Qed.
Lemma lem4309219 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4309220 {A B : Type'} : (term1213 A B) = (term1213 A B).
Proof. exact (MK_COMB (@lem4309219 A) (@lem4309218 A B)). Qed.
Lemma lem4309221 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4309222 {A B : Type'} : (term1233 A B) = (term1233 A B).
Proof. exact (MK_COMB (@lem4309221) (@lem4309220 A B)). Qed.
Lemma lem4309223 {A B : Type'} : (term1235 A B) = (term1235 A B).
Proof. exact (MK_COMB (@lem4309222 A B) (@lem4309199 A B)). Qed.
Lemma lem4309226 {A B : Type'} (x''' : B) (t : type1413 A B) (x : A) : (term1236 A B x''' t x) = (term1236 A B x''' t x).
Proof. exact (eq_refl (term1236 A B x''' t x)). Qed.
Lemma lem4309227 {A B : Type'} (x''' : B) (t : type1413 A B) (x : A) : (term1238 A B x''' t x) = (term1238 A B x''' t x).
Proof. exact (MK_COMB (@lem4309226 A B x''' t x) (@lem4309223 A B)). Qed.
Lemma lem4309230 {A B : Type'} (x' : prod A B) (x : A) (x''' : B) : (term1239 A B x' x x''') = (term1239 A B x' x x''').
Proof. exact (eq_refl (term1239 A B x' x x''')). Qed.
Lemma lem4309231 {A B : Type'} (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : (term1241 A B x' x''' t x) = (term1241 A B x' x''' t x).
Proof. exact (MK_COMB (@lem4309230 A B x' x x''') (@lem4309227 A B x''' t x)). Qed.
Lemma lem4309234 {A B : Type'} (x' : prod A B) (x'' : A) (y : B) : (term1239 A B x' x'' y) = (term1239 A B x' x'' y).
Proof. exact (eq_refl (term1239 A B x' x'' y)). Qed.
Lemma lem4309235 {A B : Type'} (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : (term1243 A B x'' y x' x''' t x) = (term1243 A B x'' y x' x''' t x).
Proof. exact (MK_COMB (@lem4309234 A B x' x'' y) (@lem4309231 A B x' x''' t x)). Qed.
Lemma lem4309238 {A B : Type'} (y : B) (t : type1413 A B) (x'' : A) : (term1236 A B y t x'') = (term1236 A B y t x'').
Proof. exact (eq_refl (term1236 A B y t x'')). Qed.
Lemma lem4309239 {A B : Type'} (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : (term1245 A B x'' y x' x''' t x) = (term1245 A B x'' y x' x''' t x).
Proof. exact (MK_COMB (@lem4309238 A B y t x'') (@lem4309235 A B x'' y x' x''' t x)). Qed.
Lemma lem4309242 {A : Type'} (x'' : A) (s : A -> Prop) : (term1246 A x'' s) = (term1246 A x'' s).
Proof. exact (eq_refl (term1246 A x'' s)). Qed.
Lemma lem4309243 {A B : Type'} (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : (term1248 A B s x'' y x' x''' t x) = (term1248 A B s x'' y x' x''' t x).
Proof. exact (MK_COMB (@lem4309242 A x'' s) (@lem4309239 A B x'' y x' x''' t x)). Qed.
Lemma lem4309244 {A B : Type'} (_48808 : type621 A B) (t : type1413 A B) (s : A -> Prop) (n : nat) : (term1345 A B _48808 t s n) = (term1345 A B _48808 t s n).
Proof. exact (eq_refl (term1345 A B _48808 t s n)). Qed.
Lemma lem4309249 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : A) (n : nat) : (term989 A B s t x n) = (term989 A B s t x n).
Proof. exact (eq_refl (term989 A B s t x n)). Qed.
Lemma lem4309250 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (n : nat) : (term983 A B s t n) = (term983 A B s t n).
Proof. exact (fun_ext (fun x : A => @lem4309249 A B s t x n)). Qed.
Lemma lem4309251 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4309252 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (n : nat) : (term581 A B s t n) = (term581 A B s t n).
Proof. exact (MK_COMB (@lem4309251 A) (@lem4309250 A B s t n)). Qed.
Lemma lem4309253 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4309254 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (n : nat) : (term1251 A B s t n) = (term1251 A B s t n).
Proof. exact (MK_COMB (@lem4309253) (@lem4309252 A B s t n)). Qed.
Lemma lem4309255 {A B : Type'} (_48808 : type621 A B) (t : type1413 A B) (s : A -> Prop) (n : nat) : (term1346 A B _48808 t s n) = (term1346 A B _48808 t s n).
Proof. exact (MK_COMB (@lem4309254 A B s t n) (@lem4309244 A B _48808 t s n)). Qed.
Lemma lem4309256 {A B : Type'} (_48808 : type621 A B) (t : type1413 A B) (s : A -> Prop) : (term1348 A B _48808 t s) = (term1348 A B _48808 t s).
Proof. exact (fun_ext (fun n : nat => @lem4309255 A B _48808 t s n)). Qed.
Lemma lem4309257 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4309258 {A B : Type'} (_48808 : type621 A B) (t : type1413 A B) (s : A -> Prop) : (term1349 A B _48808 t s) = (term1349 A B _48808 t s).
Proof. exact (MK_COMB (@lem4309257) (@lem4309256 A B _48808 t s)). Qed.
Lemma lem4309259 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1351 A B _48808 s) = (term1351 A B _48808 s).
Proof. exact (fun_ext (fun t : type1413 A B => @lem4309258 A B _48808 t s)). Qed.
Lemma lem4309260 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem4309261 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1352 A B _48808 s) = (term1352 A B _48808 s).
Proof. exact (MK_COMB (@lem4309260 A B) (@lem4309259 A B _48808 s)). Qed.
Lemma lem4309262 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4309263 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1353 A B _48808 s) = (term1353 A B _48808 s).
Proof. exact (MK_COMB (@lem4309262) (@lem4309261 A B _48808 s)). Qed.
Lemma lem4309264 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : (term1354 A B _48808 s x'' y x' x''' t x) = (term1354 A B _48808 s x'' y x' x''' t x).
Proof. exact (MK_COMB (@lem4309263 A B _48808 s) (@lem4309243 A B s x'' y x' x''' t x)). Qed.
Lemma lem4309269 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x' : A) (n : nat) : (term989 A B s t x' n) = (term989 A B s t x' n).
Proof. exact (eq_refl (term989 A B s t x' n)). Qed.
Lemma lem4309270 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (n : nat) : (term983 A B s t n) = (term983 A B s t n).
Proof. exact (fun_ext (fun x' : A => @lem4309269 A B s t x' n)). Qed.
Lemma lem4309271 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4309272 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (n : nat) : (term581 A B s t n) = (term581 A B s t n).
Proof. exact (MK_COMB (@lem4309271 A) (@lem4309270 A B s t n)). Qed.
Lemma lem4309273 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4309274 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (n : nat) : (term1251 A B s t n) = (term1251 A B s t n).
Proof. exact (MK_COMB (@lem4309273) (@lem4309272 A B s t n)). Qed.
Lemma lem4309275 {A B : Type'} (n : nat) (_48808 : type621 A B) (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : (term1355 A B n _48808 s x'' y x' x''' t x) = (term1355 A B n _48808 s x'' y x' x''' t x).
Proof. exact (MK_COMB (@lem4309274 A B s t n) (@lem4309264 A B _48808 s x'' y x' x''' t x)). Qed.
Lemma lem4309278 {A B : Type'} (t : type1413 A B) (x : A) (n : nat) : (term1254 A B t x n) = (term1254 A B t x n).
Proof. exact (eq_refl (term1254 A B t x n)). Qed.
Lemma lem4309279 {A B : Type'} (n : nat) (_48808 : type621 A B) (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : (term1356 A B n _48808 s x'' y x' x''' t x) = (term1356 A B n _48808 s x'' y x' x''' t x).
Proof. exact (MK_COMB (@lem4309278 A B t x n) (@lem4309275 A B n _48808 s x'' y x' x''' t x)). Qed.
Lemma lem4309282 {A : Type'} (m : nat) (s : A -> Prop) : (term1257 A m s) = (term1257 A m s).
Proof. exact (eq_refl (term1257 A m s)). Qed.
Lemma lem4309283 {A B : Type'} (m : nat) (n : nat) (_48808 : type621 A B) (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : (term1357 A B m n _48808 s x'' y x' x''' t x) = (term1357 A B m n _48808 s x'' y x' x''' t x).
Proof. exact (MK_COMB (@lem4309282 A m s) (@lem4309279 A B n _48808 s x'' y x' x''' t x)). Qed.
Lemma lem4309286 {A : Type'} (s : A -> Prop) : (term619 A s) = (term619 A s).
Proof. exact (eq_refl (term619 A s)). Qed.
Lemma lem4309287 {A B : Type'} (m : nat) (n : nat) (_48808 : type621 A B) (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : (term1358 A B m n _48808 s x'' y x' x''' t x) = (term1358 A B m n _48808 s x'' y x' x''' t x).
Proof. exact (MK_COMB (@lem4309286 A s) (@lem4309283 A B m n _48808 s x'' y x' x''' t x)). Qed.
Lemma lem4309292 {A : Type'} (x : A) (s : A -> Prop) : (term1262 A x s) = (term1262 A x s).
Proof. exact (eq_refl (term1262 A x s)). Qed.
Lemma lem4309293 {A B : Type'} (m : nat) (n : nat) (_48808 : type621 A B) (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : (term1359 A B m n _48808 s x'' y x' x''' t x) = (term1359 A B m n _48808 s x'' y x' x''' t x).
Proof. exact (MK_COMB (@lem4309292 A x s) (@lem4309287 A B m n _48808 s x'' y x' x''' t x)). Qed.
Lemma lem4309294 {A B : Type'} (n : nat) (_48808 : type621 A B) (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : (term1360 A B n _48808 s x'' y x' x''' t x) = (term1360 A B n _48808 s x'' y x' x''' t x).
Proof. exact (fun_ext (fun m : nat => @lem4309293 A B m n _48808 s x'' y x' x''' t x)). Qed.
Lemma lem4309295 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4309296 {A B : Type'} (n : nat) (_48808 : type621 A B) (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : (term1361 A B n _48808 s x'' y x' x''' t x) = (term1361 A B n _48808 s x'' y x' x''' t x).
Proof. exact (MK_COMB (@lem4309295) (@lem4309294 A B n _48808 s x'' y x' x''' t x)). Qed.
Lemma lem4309297 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : (term1362 A B _48808 s x'' y x' x''' t x) = (term1362 A B _48808 s x'' y x' x''' t x).
Proof. exact (fun_ext (fun n : nat => @lem4309296 A B n _48808 s x'' y x' x''' t x)). Qed.
Lemma lem4309298 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4309299 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : (term1363 A B _48808 s x'' y x' x''' t x) = (term1363 A B _48808 s x'' y x' x''' t x).
Proof. exact (MK_COMB (@lem4309298) (@lem4309297 A B _48808 s x'' y x' x''' t x)). Qed.
Lemma lem4309300 {A B : Type'} (_48808 : type621 A B) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : (term1364 A B _48808 x'' y x' x''' t x) = (term1364 A B _48808 x'' y x' x''' t x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4309299 A B _48808 s x'' y x' x''' t x)). Qed.
Lemma lem4309301 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4309302 {A B : Type'} (_48808 : type621 A B) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : (term1365 A B _48808 x'' y x' x''' t x) = (term1365 A B _48808 x'' y x' x''' t x).
Proof. exact (MK_COMB (@lem4309301 A) (@lem4309300 A B _48808 x'' y x' x''' t x)). Qed.
Lemma lem4309303 {A B : Type'} (_48808 : type621 A B) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : (term1366 A B _48808 y x' x''' t x) = (term1366 A B _48808 y x' x''' t x).
Proof. exact (fun_ext (fun x'' : A => @lem4309302 A B _48808 x'' y x' x''' t x)). Qed.
Lemma lem4309304 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4309305 {A B : Type'} (_48808 : type621 A B) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : (term1367 A B _48808 y x' x''' t x) = (term1367 A B _48808 y x' x''' t x).
Proof. exact (MK_COMB (@lem4309304 A) (@lem4309303 A B _48808 y x' x''' t x)). Qed.
Lemma lem4309306 {A B : Type'} (_48808 : type621 A B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : (term1368 A B _48808 x' x''' t x) = (term1368 A B _48808 x' x''' t x).
Proof. exact (fun_ext (fun y : B => @lem4309305 A B _48808 y x' x''' t x)). Qed.
Lemma lem4309307 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4309308 {A B : Type'} (_48808 : type621 A B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : (term1369 A B _48808 x' x''' t x) = (term1369 A B _48808 x' x''' t x).
Proof. exact (MK_COMB (@lem4309307 B) (@lem4309306 A B _48808 x' x''' t x)). Qed.
Lemma lem4309309 {A B : Type'} (_48808 : type621 A B) (x''' : B) (t : type1413 A B) (x : A) : (term1370 A B _48808 x''' t x) = (term1370 A B _48808 x''' t x).
Proof. exact (fun_ext (fun x' : prod A B => @lem4309308 A B _48808 x' x''' t x)). Qed.
Lemma lem4309310 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem4309311 {A B : Type'} (_48808 : type621 A B) (x''' : B) (t : type1413 A B) (x : A) : (term1371 A B _48808 x''' t x) = (term1371 A B _48808 x''' t x).
Proof. exact (MK_COMB (@lem4309310 A B) (@lem4309309 A B _48808 x''' t x)). Qed.
Lemma lem4309312 {A B : Type'} (_48808 : type621 A B) (t : type1413 A B) (x : A) : (term1372 A B _48808 t x) = (term1372 A B _48808 t x).
Proof. exact (fun_ext (fun x''' : B => @lem4309311 A B _48808 x''' t x)). Qed.
Lemma lem4309313 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4309314 {A B : Type'} (_48808 : type621 A B) (t : type1413 A B) (x : A) : (term1373 A B _48808 t x) = (term1373 A B _48808 t x).
Proof. exact (MK_COMB (@lem4309313 B) (@lem4309312 A B _48808 t x)). Qed.
Lemma lem4309315 {A B : Type'} (_48808 : type621 A B) (x : A) : (term1374 A B _48808 x) = (term1374 A B _48808 x).
Proof. exact (fun_ext (fun t : type1413 A B => @lem4309314 A B _48808 t x)). Qed.
Lemma lem4309316 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem4309317 {A B : Type'} (_48808 : type621 A B) (x : A) : (term1375 A B _48808 x) = (term1375 A B _48808 x).
Proof. exact (MK_COMB (@lem4309316 A B) (@lem4309315 A B _48808 x)). Qed.
Lemma lem4309318 {A B : Type'} (_48808 : type621 A B) : (term1376 A B _48808) = (term1376 A B _48808).
Proof. exact (fun_ext (fun x : A => @lem4309317 A B _48808 x)). Qed.
Lemma lem4309319 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4309320 {A B : Type'} (_48808 : type621 A B) : (term1377 A B _48808) = (term1377 A B _48808).
Proof. exact (MK_COMB (@lem4309319 A) (@lem4309318 A B _48808)). Qed.
Lemma lem4309321 {A B : Type'} (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) (x : A) (y : B) : (term1439 A B GEN_PVAR_121 s t x y) = (term1439 A B GEN_PVAR_121 s t x y).
Proof. exact (eq_refl (term1439 A B GEN_PVAR_121 s t x y)). Qed.
Lemma lem4309322 {A B : Type'} (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) (x : A) : (term1440 A B GEN_PVAR_121 s t x) = (term1440 A B GEN_PVAR_121 s t x).
Proof. exact (fun_ext (fun y : B => @lem4309321 A B GEN_PVAR_121 s t x y)). Qed.
Lemma lem4309323 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4309324 {A B : Type'} (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) (x : A) : (term1441 A B GEN_PVAR_121 s t x) = (term1441 A B GEN_PVAR_121 s t x).
Proof. exact (MK_COMB (@lem4309323 B) (@lem4309322 A B GEN_PVAR_121 s t x)). Qed.
Lemma lem4309325 {A B : Type'} (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1442 A B GEN_PVAR_121 s t) = (term1442 A B GEN_PVAR_121 s t).
Proof. exact (fun_ext (fun x : A => @lem4309324 A B GEN_PVAR_121 s t x)). Qed.
Lemma lem4309326 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4309327 {A B : Type'} (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1163 A B GEN_PVAR_121 s t) = (term1163 A B GEN_PVAR_121 s t).
Proof. exact (MK_COMB (@lem4309326 A) (@lem4309325 A B GEN_PVAR_121 s t)). Qed.
Lemma lem4309330 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) (GEN_PVAR_121 : prod A B) : (term1427 A B _48808 s t GEN_PVAR_121) = (term1427 A B _48808 s t GEN_PVAR_121).
Proof. exact (eq_refl (term1427 A B _48808 s t GEN_PVAR_121)). Qed.
Lemma lem4309331 {A B : Type'} (_48808 : type621 A B) (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) : ((_48808 s t GEN_PVAR_121) = (term1163 A B GEN_PVAR_121 s t)) = ((_48808 s t GEN_PVAR_121) = (term1163 A B GEN_PVAR_121 s t)).
Proof. exact (MK_COMB (@lem4309330 A B _48808 s t GEN_PVAR_121) (@lem4309327 A B GEN_PVAR_121 s t)). Qed.
Lemma lem4309332 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1429 A B _48808 s t) = (term1429 A B _48808 s t).
Proof. exact (fun_ext (fun GEN_PVAR_121 : prod A B => @lem4309331 A B _48808 GEN_PVAR_121 s t)). Qed.
Lemma lem4309333 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem4309334 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1430 A B _48808 s t) = (term1430 A B _48808 s t).
Proof. exact (MK_COMB (@lem4309333 A B) (@lem4309332 A B _48808 s t)). Qed.
Lemma lem4309335 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1431 A B _48808 s) = (term1431 A B _48808 s).
Proof. exact (fun_ext (fun t : type1413 A B => @lem4309334 A B _48808 s t)). Qed.
Lemma lem4309336 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem4309337 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1432 A B _48808 s) = (term1432 A B _48808 s).
Proof. exact (MK_COMB (@lem4309336 A B) (@lem4309335 A B _48808 s)). Qed.
Lemma lem4309338 {A B : Type'} (_48808 : type621 A B) : (term1433 A B _48808) = (term1433 A B _48808).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4309337 A B _48808 s)). Qed.
Lemma lem4309339 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4309340 {A B : Type'} (_48808 : type621 A B) : (term1434 A B _48808) = (term1434 A B _48808).
Proof. exact (MK_COMB (@lem4309339 A) (@lem4309338 A B _48808)). Qed.
Lemma lem4309341 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4309342 {A B : Type'} (_48808 : type621 A B) : (term1435 A B _48808) = (term1435 A B _48808).
Proof. exact (MK_COMB (@lem4309341) (@lem4309340 A B _48808)). Qed.
Lemma lem4309343 {A B : Type'} (_48808 : type621 A B) : (term1436 A B _48808) = (term1436 A B _48808).
Proof. exact (MK_COMB (@lem4309342 A B _48808) (@lem4309320 A B _48808)). Qed.
Lemma lem4309344 {A B : Type'} : (term1437 A B) = (term1437 A B).
Proof. exact (fun_ext (fun _48808 : type621 A B => @lem4309343 A B _48808)). Qed.
Lemma lem4309345 {A B : Type'} : (@all ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> Prop)) = (@all ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> Prop))). Qed.
Lemma lem4309346 {A B : Type'} : (term1438 A B) = (term1438 A B).
Proof. exact (MK_COMB (@lem4309345 A B) (@lem4309344 A B)). Qed.
Lemma lem4309633 {A B : Type'} : (term1298 A B) = (term1438 A B).
Proof. exact (TRANS (@lem4309104 A B) (@lem4309346 A B)). Qed.
Lemma lem4309634 {A B : Type'} : (term1438 A B) = (term1298 A B).
Proof. exact (SYM (@lem4309633 A B)). Qed.
Lemma lem4309635 {A B : Type'} (_48808 : type621 A B) (h1 : term1434 A B _48808) : term1434 A B _48808.
Proof. exact (h1). Qed.
Lemma lem4309641 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (h1 : term1352 A B _48808 s) : term1352 A B _48808 s.
Proof. exact (h1). Qed.
Lemma lem4309647 {A B : Type'} (h1 : term1213 A B) : term1213 A B.
Proof. exact (h1). Qed.
Lemma lem4309655 {A B : Type'} (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) (x : A) (y : B) : (term1439 A B GEN_PVAR_121 s t x y) = (term1439 A B GEN_PVAR_121 s t x y).
Proof. exact (eq_refl (term1439 A B GEN_PVAR_121 s t x y)). Qed.
Lemma lem4309656 {B : Type'} (P : B -> Prop) : (term218 B P) = (term219 B P).
Proof. exact (@lem18394 B P). Qed.
Lemma lem4309657 {A B : Type'} (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) (x : A) : (term1443 A B GEN_PVAR_121 s t x) = (term1444 A B GEN_PVAR_121 s t x).
Proof. exact (@lem4309656 B (term1440 A B GEN_PVAR_121 s t x)). Qed.
Lemma lem4309658 {A B : Type'} (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) (x : A) (y : B) : (term1445 A B GEN_PVAR_121 s t x y) = (term1439 A B GEN_PVAR_121 s t x y).
Proof. exact (eq_refl (term1445 A B GEN_PVAR_121 s t x y)). Qed.
Lemma lem4309659 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4309661 {A B : Type'} (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) (x : A) (y : B) : (term1446 A B GEN_PVAR_121 s t x y) = (term1447 A B GEN_PVAR_121 s t x y).
Proof. exact (MK_COMB (@lem4309659) (@lem4309658 A B GEN_PVAR_121 s t x y)). Qed.
Lemma lem4309662 {A B : Type'} (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) (x : A) : (term1448 A B GEN_PVAR_121 s t x) = (term1449 A B GEN_PVAR_121 s t x).
Proof. exact (fun_ext (fun y : B => @lem4309661 A B GEN_PVAR_121 s t x y)). Qed.
Lemma lem4309663 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4309664 {A B : Type'} (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) (x : A) : (term1444 A B GEN_PVAR_121 s t x) = (term1450 A B GEN_PVAR_121 s t x).
Proof. exact (MK_COMB (@lem4309663 B) (@lem4309662 A B GEN_PVAR_121 s t x)). Qed.
Lemma lem4309665 {A B : Type'} (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) (x : A) : (term1443 A B GEN_PVAR_121 s t x) = (term1450 A B GEN_PVAR_121 s t x).
Proof. exact (TRANS (@lem4309657 A B GEN_PVAR_121 s t x) (@lem4309664 A B GEN_PVAR_121 s t x)). Qed.
Lemma lem4309666 {A B : Type'} (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) (x : A) : (term1440 A B GEN_PVAR_121 s t x) = (term1440 A B GEN_PVAR_121 s t x).
Proof. exact (fun_ext (fun y : B => @lem4309655 A B GEN_PVAR_121 s t x y)). Qed.
Lemma lem4309667 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4309668 {A B : Type'} (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) (x : A) : (term1441 A B GEN_PVAR_121 s t x) = (term1441 A B GEN_PVAR_121 s t x).
Proof. exact (MK_COMB (@lem4309667 B) (@lem4309666 A B GEN_PVAR_121 s t x)). Qed.
Lemma lem4309669 {A : Type'} (P : A -> Prop) : (term218 A P) = (term219 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem4309670 {A B : Type'} (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1451 A B GEN_PVAR_121 s t) = (term1452 A B GEN_PVAR_121 s t).
Proof. exact (@lem4309669 A (term1442 A B GEN_PVAR_121 s t)). Qed.
Lemma lem4309671 {A B : Type'} (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) (x : A) : (term1453 A B GEN_PVAR_121 s t x) = (term1441 A B GEN_PVAR_121 s t x).
Proof. exact (eq_refl (term1453 A B GEN_PVAR_121 s t x)). Qed.
Lemma lem4309672 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4309673 {A B : Type'} (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) (x : A) : (term1454 A B GEN_PVAR_121 s t x) = (term1443 A B GEN_PVAR_121 s t x).
Proof. exact (MK_COMB (@lem4309672) (@lem4309671 A B GEN_PVAR_121 s t x)). Qed.
Lemma lem4309674 {A B : Type'} (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) (x : A) : (term1454 A B GEN_PVAR_121 s t x) = (term1450 A B GEN_PVAR_121 s t x).
Proof. exact (TRANS (@lem4309673 A B GEN_PVAR_121 s t x) (@lem4309665 A B GEN_PVAR_121 s t x)). Qed.
Lemma lem4309675 {A B : Type'} (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1455 A B GEN_PVAR_121 s t) = (term1456 A B GEN_PVAR_121 s t).
Proof. exact (fun_ext (fun x : A => @lem4309674 A B GEN_PVAR_121 s t x)). Qed.
Lemma lem4309676 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4309677 {A B : Type'} (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1452 A B GEN_PVAR_121 s t) = (term1457 A B GEN_PVAR_121 s t).
Proof. exact (MK_COMB (@lem4309676 A) (@lem4309675 A B GEN_PVAR_121 s t)). Qed.
Lemma lem4309678 {A B : Type'} (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1451 A B GEN_PVAR_121 s t) = (term1457 A B GEN_PVAR_121 s t).
Proof. exact (TRANS (@lem4309670 A B GEN_PVAR_121 s t) (@lem4309677 A B GEN_PVAR_121 s t)). Qed.
Lemma lem4309679 {A B : Type'} (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1442 A B GEN_PVAR_121 s t) = (term1442 A B GEN_PVAR_121 s t).
Proof. exact (fun_ext (fun x : A => @lem4309668 A B GEN_PVAR_121 s t x)). Qed.
Lemma lem4309680 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4309681 {A B : Type'} (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1163 A B GEN_PVAR_121 s t) = (term1163 A B GEN_PVAR_121 s t).
Proof. exact (MK_COMB (@lem4309680 A) (@lem4309679 A B GEN_PVAR_121 s t)). Qed.
Lemma lem4309683 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) (GEN_PVAR_121 : prod A B) : (term1458 A B _48808 s t GEN_PVAR_121) = (term1458 A B _48808 s t GEN_PVAR_121).
Proof. exact (eq_refl (term1458 A B _48808 s t GEN_PVAR_121)). Qed.
Lemma lem4309684 {A B : Type'} (_48808 : type621 A B) (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1459 A B _48808 GEN_PVAR_121 s t) = (term1459 A B _48808 GEN_PVAR_121 s t).
Proof. exact (MK_COMB (@lem4309683 A B _48808 s t GEN_PVAR_121) (@lem4309681 A B GEN_PVAR_121 s t)). Qed.
Lemma lem4309686 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) (GEN_PVAR_121 : prod A B) : (term1460 A B _48808 s t GEN_PVAR_121) = (term1460 A B _48808 s t GEN_PVAR_121).
Proof. exact (eq_refl (term1460 A B _48808 s t GEN_PVAR_121)). Qed.
Lemma lem4309687 {A B : Type'} (_48808 : type621 A B) (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1461 A B _48808 GEN_PVAR_121 s t) = (term1462 A B _48808 GEN_PVAR_121 s t).
Proof. exact (MK_COMB (@lem4309686 A B _48808 s t GEN_PVAR_121) (@lem4309678 A B GEN_PVAR_121 s t)). Qed.
Lemma lem4309688 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4309689 {A B : Type'} (_48808 : type621 A B) (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1463 A B _48808 GEN_PVAR_121 s t) = (term1464 A B _48808 GEN_PVAR_121 s t).
Proof. exact (MK_COMB (@lem4309688) (@lem4309687 A B _48808 GEN_PVAR_121 s t)). Qed.
Lemma lem4309690 {A B : Type'} (_48808 : type621 A B) (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1465 A B _48808 GEN_PVAR_121 s t) = (term1466 A B _48808 GEN_PVAR_121 s t).
Proof. exact (MK_COMB (@lem4309689 A B _48808 GEN_PVAR_121 s t) (@lem4309684 A B _48808 GEN_PVAR_121 s t)). Qed.
Lemma lem4309691 {A B : Type'} (_48808 : type621 A B) (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) : ((_48808 s t GEN_PVAR_121) = (term1163 A B GEN_PVAR_121 s t)) = (term1465 A B _48808 GEN_PVAR_121 s t).
Proof. exact (@lem17784 (_48808 s t GEN_PVAR_121) (term1163 A B GEN_PVAR_121 s t)). Qed.
Lemma lem4309692 {A B : Type'} (_48808 : type621 A B) (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) : ((_48808 s t GEN_PVAR_121) = (term1163 A B GEN_PVAR_121 s t)) = (term1466 A B _48808 GEN_PVAR_121 s t).
Proof. exact (TRANS (@lem4309691 A B _48808 GEN_PVAR_121 s t) (@lem4309690 A B _48808 GEN_PVAR_121 s t)). Qed.
Lemma lem4309693 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1429 A B _48808 s t) = (term1467 A B _48808 s t).
Proof. exact (fun_ext (fun GEN_PVAR_121 : prod A B => @lem4309692 A B _48808 GEN_PVAR_121 s t)). Qed.
Lemma lem4309694 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem4309695 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1430 A B _48808 s t) = (term1468 A B _48808 s t).
Proof. exact (MK_COMB (@lem4309694 A B) (@lem4309693 A B _48808 s t)). Qed.
Lemma lem4309696 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1431 A B _48808 s) = (term1469 A B _48808 s).
Proof. exact (fun_ext (fun t : type1413 A B => @lem4309695 A B _48808 s t)). Qed.
Lemma lem4309697 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem4309698 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1432 A B _48808 s) = (term1470 A B _48808 s).
Proof. exact (MK_COMB (@lem4309697 A B) (@lem4309696 A B _48808 s)). Qed.
Lemma lem4309699 {A B : Type'} (_48808 : type621 A B) : (term1433 A B _48808) = (term1471 A B _48808).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4309698 A B _48808 s)). Qed.
Lemma lem4309700 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4309701 {A B : Type'} (_48808 : type621 A B) : (term1434 A B _48808) = (term1472 A B _48808).
Proof. exact (MK_COMB (@lem4309700 A) (@lem4309699 A B _48808)). Qed.
Lemma lem4309711 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term511 A P Q) = (term512 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4309712 {A B : Type'} (P : type1210 A B) (Q : type1210 A B) : (term1473 A B P Q) = (term1474 A B P Q).
Proof. exact (@lem4309711 (prod A B) P Q). Qed.
Lemma lem4309713 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1475 A B _48808 s t) = (term1476 A B _48808 s t).
Proof. exact (@lem4309712 A B (term1477 A B _48808 s t) (term1478 A B _48808 s t)). Qed.
Lemma lem4309714 {A B : Type'} (_48808 : type621 A B) (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1479 A B _48808 s t GEN_PVAR_121) = (term1462 A B _48808 GEN_PVAR_121 s t).
Proof. exact (eq_refl (term1479 A B _48808 s t GEN_PVAR_121)). Qed.
Lemma lem4309715 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4309716 {A B : Type'} (_48808 : type621 A B) (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1480 A B _48808 s t GEN_PVAR_121) = (term1464 A B _48808 GEN_PVAR_121 s t).
Proof. exact (MK_COMB (@lem4309715) (@lem4309714 A B _48808 GEN_PVAR_121 s t)). Qed.
Lemma lem4309717 {A B : Type'} (_48808 : type621 A B) (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1481 A B _48808 s t GEN_PVAR_121) = (term1459 A B _48808 GEN_PVAR_121 s t).
Proof. exact (eq_refl (term1481 A B _48808 s t GEN_PVAR_121)). Qed.
Lemma lem4309718 {A B : Type'} (_48808 : type621 A B) (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1482 A B _48808 s t GEN_PVAR_121) = (term1466 A B _48808 GEN_PVAR_121 s t).
Proof. exact (MK_COMB (@lem4309716 A B _48808 GEN_PVAR_121 s t) (@lem4309717 A B _48808 GEN_PVAR_121 s t)). Qed.
Lemma lem4309719 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1483 A B _48808 s t) = (term1467 A B _48808 s t).
Proof. exact (fun_ext (fun GEN_PVAR_121 : prod A B => @lem4309718 A B _48808 GEN_PVAR_121 s t)). Qed.
Lemma lem4309720 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem4309721 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1475 A B _48808 s t) = (term1468 A B _48808 s t).
Proof. exact (MK_COMB (@lem4309720 A B) (@lem4309719 A B _48808 s t)). Qed.
Lemma lem4309722 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4309723 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1484 A B _48808 s t) = (term1485 A B _48808 s t).
Proof. exact (MK_COMB (@lem4309722) (@lem4309721 A B _48808 s t)). Qed.
Lemma lem4309724 {A B : Type'} (_48808 : type621 A B) (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1479 A B _48808 s t GEN_PVAR_121) = (term1462 A B _48808 GEN_PVAR_121 s t).
Proof. exact (eq_refl (term1479 A B _48808 s t GEN_PVAR_121)). Qed.
Lemma lem4309725 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1486 A B _48808 s t) = (term1477 A B _48808 s t).
Proof. exact (fun_ext (fun GEN_PVAR_121 : prod A B => @lem4309724 A B _48808 GEN_PVAR_121 s t)). Qed.
Lemma lem4309726 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem4309727 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1487 A B _48808 s t) = (term1488 A B _48808 s t).
Proof. exact (MK_COMB (@lem4309726 A B) (@lem4309725 A B _48808 s t)). Qed.
Lemma lem4309728 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4309729 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1489 A B _48808 s t) = (term1490 A B _48808 s t).
Proof. exact (MK_COMB (@lem4309728) (@lem4309727 A B _48808 s t)). Qed.
Lemma lem4309730 {A B : Type'} (_48808 : type621 A B) (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1481 A B _48808 s t GEN_PVAR_121) = (term1459 A B _48808 GEN_PVAR_121 s t).
Proof. exact (eq_refl (term1481 A B _48808 s t GEN_PVAR_121)). Qed.
Lemma lem4309731 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1491 A B _48808 s t) = (term1478 A B _48808 s t).
Proof. exact (fun_ext (fun GEN_PVAR_121 : prod A B => @lem4309730 A B _48808 GEN_PVAR_121 s t)). Qed.
Lemma lem4309732 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem4309733 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1492 A B _48808 s t) = (term1493 A B _48808 s t).
Proof. exact (MK_COMB (@lem4309732 A B) (@lem4309731 A B _48808 s t)). Qed.
Lemma lem4309734 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1476 A B _48808 s t) = (term1494 A B _48808 s t).
Proof. exact (MK_COMB (@lem4309729 A B _48808 s t) (@lem4309733 A B _48808 s t)). Qed.
Lemma lem4309735 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : ((term1475 A B _48808 s t) = (term1476 A B _48808 s t)) = ((term1468 A B _48808 s t) = (term1494 A B _48808 s t)).
Proof. exact (MK_COMB (@lem4309723 A B _48808 s t) (@lem4309734 A B _48808 s t)). Qed.
Lemma lem4309736 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1468 A B _48808 s t) = (term1494 A B _48808 s t).
Proof. exact (EQ_MP (@lem4309735 A B _48808 s t) (@lem4309713 A B _48808 s t)). Qed.
Lemma lem4309849 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1469 A B _48808 s) = (term1495 A B _48808 s).
Proof. exact (fun_ext (fun t : type1413 A B => @lem4309736 A B _48808 s t)). Qed.
Lemma lem4309850 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem4309851 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1470 A B _48808 s) = (term1496 A B _48808 s).
Proof. exact (MK_COMB (@lem4309850 A B) (@lem4309849 A B _48808 s)). Qed.
Lemma lem4309853 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term511 A P Q) = (term512 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4309854 {A B : Type'} (P : type475 A B) (Q : type475 A B) : (term1497 A B P Q) = (term1498 A B P Q).
Proof. exact (@lem4309853 (type1413 A B) P Q). Qed.
Lemma lem4309855 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1499 A B _48808 s) = (term1500 A B _48808 s).
Proof. exact (@lem4309854 A B (term1501 A B _48808 s) (term1502 A B _48808 s)). Qed.
Lemma lem4309856 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1503 A B _48808 s t) = (term1488 A B _48808 s t).
Proof. exact (eq_refl (term1503 A B _48808 s t)). Qed.
Lemma lem4309857 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4309858 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1504 A B _48808 s t) = (term1490 A B _48808 s t).
Proof. exact (MK_COMB (@lem4309857) (@lem4309856 A B _48808 s t)). Qed.
Lemma lem4309859 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1505 A B _48808 s t) = (term1493 A B _48808 s t).
Proof. exact (eq_refl (term1505 A B _48808 s t)). Qed.
Lemma lem4309860 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1506 A B _48808 s t) = (term1494 A B _48808 s t).
Proof. exact (MK_COMB (@lem4309858 A B _48808 s t) (@lem4309859 A B _48808 s t)). Qed.
Lemma lem4309861 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1507 A B _48808 s) = (term1495 A B _48808 s).
Proof. exact (fun_ext (fun t : type1413 A B => @lem4309860 A B _48808 s t)). Qed.
Lemma lem4309862 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem4309863 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1499 A B _48808 s) = (term1496 A B _48808 s).
Proof. exact (MK_COMB (@lem4309862 A B) (@lem4309861 A B _48808 s)). Qed.
Lemma lem4309864 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4309865 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1508 A B _48808 s) = (term1509 A B _48808 s).
Proof. exact (MK_COMB (@lem4309864) (@lem4309863 A B _48808 s)). Qed.
Lemma lem4309866 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1503 A B _48808 s t) = (term1488 A B _48808 s t).
Proof. exact (eq_refl (term1503 A B _48808 s t)). Qed.
Lemma lem4309867 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1510 A B _48808 s) = (term1501 A B _48808 s).
Proof. exact (fun_ext (fun t : type1413 A B => @lem4309866 A B _48808 s t)). Qed.
Lemma lem4309868 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem4309869 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1511 A B _48808 s) = (term1512 A B _48808 s).
Proof. exact (MK_COMB (@lem4309868 A B) (@lem4309867 A B _48808 s)). Qed.
Lemma lem4309870 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4309871 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1513 A B _48808 s) = (term1514 A B _48808 s).
Proof. exact (MK_COMB (@lem4309870) (@lem4309869 A B _48808 s)). Qed.
Lemma lem4309872 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1505 A B _48808 s t) = (term1493 A B _48808 s t).
Proof. exact (eq_refl (term1505 A B _48808 s t)). Qed.
Lemma lem4309873 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1515 A B _48808 s) = (term1502 A B _48808 s).
Proof. exact (fun_ext (fun t : type1413 A B => @lem4309872 A B _48808 s t)). Qed.
Lemma lem4309874 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem4309875 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1516 A B _48808 s) = (term1517 A B _48808 s).
Proof. exact (MK_COMB (@lem4309874 A B) (@lem4309873 A B _48808 s)). Qed.
Lemma lem4309876 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1500 A B _48808 s) = (term1518 A B _48808 s).
Proof. exact (MK_COMB (@lem4309871 A B _48808 s) (@lem4309875 A B _48808 s)). Qed.
Lemma lem4309877 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : ((term1499 A B _48808 s) = (term1500 A B _48808 s)) = ((term1496 A B _48808 s) = (term1518 A B _48808 s)).
Proof. exact (MK_COMB (@lem4309865 A B _48808 s) (@lem4309876 A B _48808 s)). Qed.
Lemma lem4309878 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1496 A B _48808 s) = (term1518 A B _48808 s).
Proof. exact (EQ_MP (@lem4309877 A B _48808 s) (@lem4309855 A B _48808 s)). Qed.
Lemma lem4309999 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1470 A B _48808 s) = (term1518 A B _48808 s).
Proof. exact (TRANS (@lem4309851 A B _48808 s) (@lem4309878 A B _48808 s)). Qed.
Lemma lem4310000 {A B : Type'} (_48808 : type621 A B) : (term1471 A B _48808) = (term1519 A B _48808).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4309999 A B _48808 s)). Qed.
Lemma lem4310001 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4310002 {A B : Type'} (_48808 : type621 A B) : (term1472 A B _48808) = (term1520 A B _48808).
Proof. exact (MK_COMB (@lem4310001 A) (@lem4310000 A B _48808)). Qed.
Lemma lem4310004 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term511 A P Q) = (term512 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4310005 {A : Type'} (P : type686 A) (Q : type686 A) : (term1521 A P Q) = (term1522 A P Q).
Proof. exact (@lem4310004 (A -> Prop) P Q). Qed.
Lemma lem4310006 {A B : Type'} (_48808 : type621 A B) : (term1523 A B _48808) = (term1524 A B _48808).
Proof. exact (@lem4310005 A (term1525 A B _48808) (term1526 A B _48808)). Qed.
Lemma lem4310007 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1527 A B _48808 s) = (term1512 A B _48808 s).
Proof. exact (eq_refl (term1527 A B _48808 s)). Qed.
Lemma lem4310008 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4310009 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1528 A B _48808 s) = (term1514 A B _48808 s).
Proof. exact (MK_COMB (@lem4310008) (@lem4310007 A B _48808 s)). Qed.
Lemma lem4310010 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1529 A B _48808 s) = (term1517 A B _48808 s).
Proof. exact (eq_refl (term1529 A B _48808 s)). Qed.
Lemma lem4310011 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1530 A B _48808 s) = (term1518 A B _48808 s).
Proof. exact (MK_COMB (@lem4310009 A B _48808 s) (@lem4310010 A B _48808 s)). Qed.
Lemma lem4310012 {A B : Type'} (_48808 : type621 A B) : (term1531 A B _48808) = (term1519 A B _48808).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4310011 A B _48808 s)). Qed.
Lemma lem4310013 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4310014 {A B : Type'} (_48808 : type621 A B) : (term1523 A B _48808) = (term1520 A B _48808).
Proof. exact (MK_COMB (@lem4310013 A) (@lem4310012 A B _48808)). Qed.
Lemma lem4310015 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4310016 {A B : Type'} (_48808 : type621 A B) : (term1532 A B _48808) = (term1533 A B _48808).
Proof. exact (MK_COMB (@lem4310015) (@lem4310014 A B _48808)). Qed.
Lemma lem4310017 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1527 A B _48808 s) = (term1512 A B _48808 s).
Proof. exact (eq_refl (term1527 A B _48808 s)). Qed.
Lemma lem4310018 {A B : Type'} (_48808 : type621 A B) : (term1534 A B _48808) = (term1525 A B _48808).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4310017 A B _48808 s)). Qed.
Lemma lem4310019 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4310020 {A B : Type'} (_48808 : type621 A B) : (term1535 A B _48808) = (term1536 A B _48808).
Proof. exact (MK_COMB (@lem4310019 A) (@lem4310018 A B _48808)). Qed.
Lemma lem4310021 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4310022 {A B : Type'} (_48808 : type621 A B) : (term1537 A B _48808) = (term1538 A B _48808).
Proof. exact (MK_COMB (@lem4310021) (@lem4310020 A B _48808)). Qed.
Lemma lem4310023 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1529 A B _48808 s) = (term1517 A B _48808 s).
Proof. exact (eq_refl (term1529 A B _48808 s)). Qed.
Lemma lem4310024 {A B : Type'} (_48808 : type621 A B) : (term1539 A B _48808) = (term1526 A B _48808).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4310023 A B _48808 s)). Qed.
Lemma lem4310025 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4310026 {A B : Type'} (_48808 : type621 A B) : (term1540 A B _48808) = (term1541 A B _48808).
Proof. exact (MK_COMB (@lem4310025 A) (@lem4310024 A B _48808)). Qed.
Lemma lem4310027 {A B : Type'} (_48808 : type621 A B) : (term1524 A B _48808) = (term1542 A B _48808).
Proof. exact (MK_COMB (@lem4310022 A B _48808) (@lem4310026 A B _48808)). Qed.
Lemma lem4310028 {A B : Type'} (_48808 : type621 A B) : ((term1523 A B _48808) = (term1524 A B _48808)) = ((term1520 A B _48808) = (term1542 A B _48808)).
Proof. exact (MK_COMB (@lem4310016 A B _48808) (@lem4310027 A B _48808)). Qed.
Lemma lem4310029 {A B : Type'} (_48808 : type621 A B) : (term1520 A B _48808) = (term1542 A B _48808).
Proof. exact (EQ_MP (@lem4310028 A B _48808) (@lem4310006 A B _48808)). Qed.
Lemma lem4310158 {A B : Type'} (_48808 : type621 A B) : (term1472 A B _48808) = (term1542 A B _48808).
Proof. exact (TRANS (@lem4310002 A B _48808) (@lem4310029 A B _48808)). Qed.
Lemma lem4310160 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1543 A P Q) = (term1544 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4310161 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1543 A P Q) = (term1544 A P Q).
Proof. exact (@lem4310160 A P Q). Qed.
Lemma lem4310162 {A B : Type'} (_48808 : type621 A B) (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1545 A B _48808 GEN_PVAR_121 s t) = (term1546 A B _48808 GEN_PVAR_121 s t).
Proof. exact (@lem4310161 A (term1547 A B _48808 s t GEN_PVAR_121) (term1442 A B GEN_PVAR_121 s t)). Qed.
Lemma lem4310163 {A B : Type'} (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) (x : A) : (term1453 A B GEN_PVAR_121 s t x) = (term1441 A B GEN_PVAR_121 s t x).
Proof. exact (eq_refl (term1453 A B GEN_PVAR_121 s t x)). Qed.
Lemma lem4310164 {A B : Type'} (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1548 A B GEN_PVAR_121 s t) = (term1442 A B GEN_PVAR_121 s t).
Proof. exact (fun_ext (fun x : A => @lem4310163 A B GEN_PVAR_121 s t x)). Qed.
Lemma lem4310165 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4310166 {A B : Type'} (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1549 A B GEN_PVAR_121 s t) = (term1163 A B GEN_PVAR_121 s t).
Proof. exact (MK_COMB (@lem4310165 A) (@lem4310164 A B GEN_PVAR_121 s t)). Qed.
Lemma lem4310167 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) (GEN_PVAR_121 : prod A B) : (term1458 A B _48808 s t GEN_PVAR_121) = (term1458 A B _48808 s t GEN_PVAR_121).
Proof. exact (eq_refl (term1458 A B _48808 s t GEN_PVAR_121)). Qed.
Lemma lem4310168 {A B : Type'} (_48808 : type621 A B) (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1545 A B _48808 GEN_PVAR_121 s t) = (term1459 A B _48808 GEN_PVAR_121 s t).
Proof. exact (MK_COMB (@lem4310167 A B _48808 s t GEN_PVAR_121) (@lem4310166 A B GEN_PVAR_121 s t)). Qed.
Lemma lem4310169 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4310170 {A B : Type'} (_48808 : type621 A B) (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1550 A B _48808 GEN_PVAR_121 s t) = (term1551 A B _48808 GEN_PVAR_121 s t).
Proof. exact (MK_COMB (@lem4310169) (@lem4310168 A B _48808 GEN_PVAR_121 s t)). Qed.
Lemma lem4310171 {A B : Type'} (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) (x : A) : (term1453 A B GEN_PVAR_121 s t x) = (term1441 A B GEN_PVAR_121 s t x).
Proof. exact (eq_refl (term1453 A B GEN_PVAR_121 s t x)). Qed.
Lemma lem4310172 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) (GEN_PVAR_121 : prod A B) : (term1458 A B _48808 s t GEN_PVAR_121) = (term1458 A B _48808 s t GEN_PVAR_121).
Proof. exact (eq_refl (term1458 A B _48808 s t GEN_PVAR_121)). Qed.
Lemma lem4310173 {A B : Type'} (_48808 : type621 A B) (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) (x : A) : (term1552 A B _48808 GEN_PVAR_121 s t x) = (term1553 A B _48808 GEN_PVAR_121 s t x).
Proof. exact (MK_COMB (@lem4310172 A B _48808 s t GEN_PVAR_121) (@lem4310171 A B GEN_PVAR_121 s t x)). Qed.
Lemma lem4310174 {A B : Type'} (_48808 : type621 A B) (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1554 A B _48808 GEN_PVAR_121 s t) = (term1555 A B _48808 GEN_PVAR_121 s t).
Proof. exact (fun_ext (fun x : A => @lem4310173 A B _48808 GEN_PVAR_121 s t x)). Qed.
Lemma lem4310175 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4310176 {A B : Type'} (_48808 : type621 A B) (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1546 A B _48808 GEN_PVAR_121 s t) = (term1556 A B _48808 GEN_PVAR_121 s t).
Proof. exact (MK_COMB (@lem4310175 A) (@lem4310174 A B _48808 GEN_PVAR_121 s t)). Qed.
Lemma lem4310177 {A B : Type'} (_48808 : type621 A B) (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) : ((term1545 A B _48808 GEN_PVAR_121 s t) = (term1546 A B _48808 GEN_PVAR_121 s t)) = ((term1459 A B _48808 GEN_PVAR_121 s t) = (term1556 A B _48808 GEN_PVAR_121 s t)).
Proof. exact (MK_COMB (@lem4310170 A B _48808 GEN_PVAR_121 s t) (@lem4310176 A B _48808 GEN_PVAR_121 s t)). Qed.
Lemma lem4310178 {A B : Type'} (_48808 : type621 A B) (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1459 A B _48808 GEN_PVAR_121 s t) = (term1556 A B _48808 GEN_PVAR_121 s t).
Proof. exact (EQ_MP (@lem4310177 A B _48808 GEN_PVAR_121 s t) (@lem4310162 A B _48808 GEN_PVAR_121 s t)). Qed.
Lemma lem4310180 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1543 A P Q) = (term1544 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4310181 {B : Type'} (P : Prop) (Q : B -> Prop) : (term1543 B P Q) = (term1544 B P Q).
Proof. exact (@lem4310180 B P Q). Qed.
Lemma lem4310182 {A B : Type'} (_48808 : type621 A B) (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) (x : A) : (term1557 A B _48808 GEN_PVAR_121 s t x) = (term1558 A B _48808 GEN_PVAR_121 s t x).
Proof. exact (@lem4310181 B (term1547 A B _48808 s t GEN_PVAR_121) (term1440 A B GEN_PVAR_121 s t x)). Qed.
Lemma lem4310183 {A B : Type'} (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) (x : A) (y : B) : (term1445 A B GEN_PVAR_121 s t x y) = (term1439 A B GEN_PVAR_121 s t x y).
Proof. exact (eq_refl (term1445 A B GEN_PVAR_121 s t x y)). Qed.
Lemma lem4310184 {A B : Type'} (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) (x : A) : (term1559 A B GEN_PVAR_121 s t x) = (term1440 A B GEN_PVAR_121 s t x).
Proof. exact (fun_ext (fun y : B => @lem4310183 A B GEN_PVAR_121 s t x y)). Qed.
Lemma lem4310185 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4310186 {A B : Type'} (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) (x : A) : (term1560 A B GEN_PVAR_121 s t x) = (term1441 A B GEN_PVAR_121 s t x).
Proof. exact (MK_COMB (@lem4310185 B) (@lem4310184 A B GEN_PVAR_121 s t x)). Qed.
Lemma lem4310187 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) (GEN_PVAR_121 : prod A B) : (term1458 A B _48808 s t GEN_PVAR_121) = (term1458 A B _48808 s t GEN_PVAR_121).
Proof. exact (eq_refl (term1458 A B _48808 s t GEN_PVAR_121)). Qed.
Lemma lem4310188 {A B : Type'} (_48808 : type621 A B) (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) (x : A) : (term1557 A B _48808 GEN_PVAR_121 s t x) = (term1553 A B _48808 GEN_PVAR_121 s t x).
Proof. exact (MK_COMB (@lem4310187 A B _48808 s t GEN_PVAR_121) (@lem4310186 A B GEN_PVAR_121 s t x)). Qed.
Lemma lem4310189 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4310190 {A B : Type'} (_48808 : type621 A B) (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) (x : A) : (term1561 A B _48808 GEN_PVAR_121 s t x) = (term1562 A B _48808 GEN_PVAR_121 s t x).
Proof. exact (MK_COMB (@lem4310189) (@lem4310188 A B _48808 GEN_PVAR_121 s t x)). Qed.
Lemma lem4310191 {A B : Type'} (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) (x : A) (y : B) : (term1445 A B GEN_PVAR_121 s t x y) = (term1439 A B GEN_PVAR_121 s t x y).
Proof. exact (eq_refl (term1445 A B GEN_PVAR_121 s t x y)). Qed.
Lemma lem4310192 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) (GEN_PVAR_121 : prod A B) : (term1458 A B _48808 s t GEN_PVAR_121) = (term1458 A B _48808 s t GEN_PVAR_121).
Proof. exact (eq_refl (term1458 A B _48808 s t GEN_PVAR_121)). Qed.
Lemma lem4310193 {A B : Type'} (_48808 : type621 A B) (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) (x : A) (y : B) : (term1563 A B _48808 GEN_PVAR_121 s t x y) = (term1564 A B _48808 GEN_PVAR_121 s t x y).
Proof. exact (MK_COMB (@lem4310192 A B _48808 s t GEN_PVAR_121) (@lem4310191 A B GEN_PVAR_121 s t x y)). Qed.
Lemma lem4310194 {A B : Type'} (_48808 : type621 A B) (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) (x : A) : (term1565 A B _48808 GEN_PVAR_121 s t x) = (term1566 A B _48808 GEN_PVAR_121 s t x).
Proof. exact (fun_ext (fun y : B => @lem4310193 A B _48808 GEN_PVAR_121 s t x y)). Qed.
Lemma lem4310195 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4310196 {A B : Type'} (_48808 : type621 A B) (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) (x : A) : (term1558 A B _48808 GEN_PVAR_121 s t x) = (term1567 A B _48808 GEN_PVAR_121 s t x).
Proof. exact (MK_COMB (@lem4310195 B) (@lem4310194 A B _48808 GEN_PVAR_121 s t x)). Qed.
Lemma lem4310197 {A B : Type'} (_48808 : type621 A B) (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) (x : A) : ((term1557 A B _48808 GEN_PVAR_121 s t x) = (term1558 A B _48808 GEN_PVAR_121 s t x)) = ((term1553 A B _48808 GEN_PVAR_121 s t x) = (term1567 A B _48808 GEN_PVAR_121 s t x)).
Proof. exact (MK_COMB (@lem4310190 A B _48808 GEN_PVAR_121 s t x) (@lem4310196 A B _48808 GEN_PVAR_121 s t x)). Qed.
Lemma lem4310198 {A B : Type'} (_48808 : type621 A B) (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) (x : A) : (term1553 A B _48808 GEN_PVAR_121 s t x) = (term1567 A B _48808 GEN_PVAR_121 s t x).
Proof. exact (EQ_MP (@lem4310197 A B _48808 GEN_PVAR_121 s t x) (@lem4310182 A B _48808 GEN_PVAR_121 s t x)). Qed.
Lemma lem4310199 {A B : Type'} (_48808 : type621 A B) (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1555 A B _48808 GEN_PVAR_121 s t) = (term1568 A B _48808 GEN_PVAR_121 s t).
Proof. exact (fun_ext (fun x : A => @lem4310198 A B _48808 GEN_PVAR_121 s t x)). Qed.
Lemma lem4310200 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4310201 {A B : Type'} (_48808 : type621 A B) (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1556 A B _48808 GEN_PVAR_121 s t) = (term1569 A B _48808 GEN_PVAR_121 s t).
Proof. exact (MK_COMB (@lem4310200 A) (@lem4310199 A B _48808 GEN_PVAR_121 s t)). Qed.
Lemma lem4310202 {A B : Type'} (_48808 : type621 A B) (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1459 A B _48808 GEN_PVAR_121 s t) = (term1569 A B _48808 GEN_PVAR_121 s t).
Proof. exact (TRANS (@lem4310178 A B _48808 GEN_PVAR_121 s t) (@lem4310201 A B _48808 GEN_PVAR_121 s t)). Qed.
Lemma lem4310203 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1478 A B _48808 s t) = (term1570 A B _48808 s t).
Proof. exact (fun_ext (fun GEN_PVAR_121 : prod A B => @lem4310202 A B _48808 GEN_PVAR_121 s t)). Qed.
Lemma lem4310204 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem4310205 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1493 A B _48808 s t) = (term1571 A B _48808 s t).
Proof. exact (MK_COMB (@lem4310204 A B) (@lem4310203 A B _48808 s t)). Qed.
Lemma lem4310207 {A B : Type'} (P : type1413 A B) : (term1572 A B P) = (term1573 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4310208 {A B : Type'} (P : type1205 A B) : (term1574 A B P) = (term1575 A B P).
Proof. exact (@lem4310207 (prod A B) A P). Qed.
Lemma lem4310209 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1576 A B _48808 s t) = (term1577 A B _48808 s t).
Proof. exact (@lem4310208 A B (term1578 A B _48808 s t)). Qed.
Lemma lem4310210 {A B : Type'} (_48808 : type621 A B) (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1579 A B _48808 s t GEN_PVAR_121) = (term1568 A B _48808 GEN_PVAR_121 s t).
Proof. exact (eq_refl (term1579 A B _48808 s t GEN_PVAR_121)). Qed.
Lemma lem4310211 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4310212 {A B : Type'} (_48808 : type621 A B) (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) (x : A) : (term1580 A B _48808 s t GEN_PVAR_121 x) = (term1581 A B _48808 GEN_PVAR_121 s t x).
Proof. exact (MK_COMB (@lem4310210 A B _48808 GEN_PVAR_121 s t) (@lem4310211 A x)). Qed.
Lemma lem4310213 {A B : Type'} (_48808 : type621 A B) (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) (x : A) : (term1581 A B _48808 GEN_PVAR_121 s t x) = (term1567 A B _48808 GEN_PVAR_121 s t x).
Proof. exact (eq_refl (term1581 A B _48808 GEN_PVAR_121 s t x)). Qed.
Lemma lem4310214 {A B : Type'} (_48808 : type621 A B) (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) (x : A) : (term1580 A B _48808 s t GEN_PVAR_121 x) = (term1567 A B _48808 GEN_PVAR_121 s t x).
Proof. exact (TRANS (@lem4310212 A B _48808 GEN_PVAR_121 s t x) (@lem4310213 A B _48808 GEN_PVAR_121 s t x)). Qed.
Lemma lem4310215 {A B : Type'} (_48808 : type621 A B) (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1582 A B _48808 s t GEN_PVAR_121) = (term1568 A B _48808 GEN_PVAR_121 s t).
Proof. exact (fun_ext (fun x : A => @lem4310214 A B _48808 GEN_PVAR_121 s t x)). Qed.
Lemma lem4310216 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4310217 {A B : Type'} (_48808 : type621 A B) (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1583 A B _48808 s t GEN_PVAR_121) = (term1569 A B _48808 GEN_PVAR_121 s t).
Proof. exact (MK_COMB (@lem4310216 A) (@lem4310215 A B _48808 GEN_PVAR_121 s t)). Qed.
Lemma lem4310218 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1584 A B _48808 s t) = (term1570 A B _48808 s t).
Proof. exact (fun_ext (fun GEN_PVAR_121 : prod A B => @lem4310217 A B _48808 GEN_PVAR_121 s t)). Qed.
Lemma lem4310219 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem4310220 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1576 A B _48808 s t) = (term1571 A B _48808 s t).
Proof. exact (MK_COMB (@lem4310219 A B) (@lem4310218 A B _48808 s t)). Qed.
Lemma lem4310221 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4310222 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1585 A B _48808 s t) = (term1586 A B _48808 s t).
Proof. exact (MK_COMB (@lem4310221) (@lem4310220 A B _48808 s t)). Qed.
Lemma lem4310223 {A B : Type'} (_48808 : type621 A B) (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term1579 A B _48808 s t GEN_PVAR_121) = (term1568 A B _48808 GEN_PVAR_121 s t).
Proof. exact (eq_refl (term1579 A B _48808 s t GEN_PVAR_121)). Qed.
Lemma lem4310224 {A B : Type'} (x : type1207 A B) (GEN_PVAR_121 : prod A B) : (x GEN_PVAR_121) = (x GEN_PVAR_121).
Proof. exact (eq_refl (x GEN_PVAR_121)). Qed.
Lemma lem4310225 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) (x : type1207 A B) (GEN_PVAR_121 : prod A B) : (term1587 A B _48808 s t x GEN_PVAR_121) = (term1588 A B _48808 s t x GEN_PVAR_121).
Proof. exact (MK_COMB (@lem4310223 A B _48808 GEN_PVAR_121 s t) (@lem4310224 A B x GEN_PVAR_121)). Qed.
Lemma lem4310226 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) (x : type1207 A B) (GEN_PVAR_121 : prod A B) : (term1588 A B _48808 s t x GEN_PVAR_121) = (term1589 A B _48808 s t x GEN_PVAR_121).
Proof. exact (eq_refl (term1588 A B _48808 s t x GEN_PVAR_121)). Qed.
Lemma lem4310227 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) (x : type1207 A B) (GEN_PVAR_121 : prod A B) : (term1587 A B _48808 s t x GEN_PVAR_121) = (term1589 A B _48808 s t x GEN_PVAR_121).
Proof. exact (TRANS (@lem4310225 A B _48808 s t x GEN_PVAR_121) (@lem4310226 A B _48808 s t x GEN_PVAR_121)). Qed.
Lemma lem4310228 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) (x : type1207 A B) : (term1590 A B _48808 s t x) = (term1591 A B _48808 s t x).
Proof. exact (fun_ext (fun GEN_PVAR_121 : prod A B => @lem4310227 A B _48808 s t x GEN_PVAR_121)). Qed.
Lemma lem4310229 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem4310230 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) (x : type1207 A B) : (term1592 A B _48808 s t x) = (term1593 A B _48808 s t x).
Proof. exact (MK_COMB (@lem4310229 A B) (@lem4310228 A B _48808 s t x)). Qed.
Lemma lem4310231 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1594 A B _48808 s t) = (term1595 A B _48808 s t).
Proof. exact (fun_ext (fun x : type1207 A B => @lem4310230 A B _48808 s t x)). Qed.
Lemma lem4310232 {A B : Type'} : (@ex ((prod A B) -> A)) = (@ex ((prod A B) -> A)).
Proof. exact (eq_refl (@ex ((prod A B) -> A))). Qed.
Lemma lem4310233 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1577 A B _48808 s t) = (term1596 A B _48808 s t).
Proof. exact (MK_COMB (@lem4310232 A B) (@lem4310231 A B _48808 s t)). Qed.
Lemma lem4310234 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : ((term1576 A B _48808 s t) = (term1577 A B _48808 s t)) = ((term1571 A B _48808 s t) = (term1596 A B _48808 s t)).
Proof. exact (MK_COMB (@lem4310222 A B _48808 s t) (@lem4310233 A B _48808 s t)). Qed.
Lemma lem4310235 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1571 A B _48808 s t) = (term1596 A B _48808 s t).
Proof. exact (EQ_MP (@lem4310234 A B _48808 s t) (@lem4310209 A B _48808 s t)). Qed.
Lemma lem4310237 {A B : Type'} (P : type1413 A B) : (term1572 A B P) = (term1573 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4310238 {A B : Type'} (P : type1206 A B) : (term1597 A B P) = (term1598 A B P).
Proof. exact (@lem4310237 (prod A B) B P). Qed.
Lemma lem4310239 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) (x : type1207 A B) : (term1599 A B _48808 s t x) = (term1600 A B _48808 s t x).
Proof. exact (@lem4310238 A B (term1601 A B _48808 s t x)). Qed.
Lemma lem4310240 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) (x : type1207 A B) (GEN_PVAR_121 : prod A B) : (term1602 A B _48808 s t x GEN_PVAR_121) = (term1603 A B _48808 s t x GEN_PVAR_121).
Proof. exact (eq_refl (term1602 A B _48808 s t x GEN_PVAR_121)). Qed.
Lemma lem4310241 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4310242 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) (x : type1207 A B) (GEN_PVAR_121 : prod A B) (y : B) : (term1604 A B _48808 s t x GEN_PVAR_121 y) = (term1605 A B _48808 s t x GEN_PVAR_121 y).
Proof. exact (MK_COMB (@lem4310240 A B _48808 s t x GEN_PVAR_121) (@lem4310241 B y)). Qed.
Lemma lem4310243 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) (x : type1207 A B) (GEN_PVAR_121 : prod A B) (y : B) : (term1605 A B _48808 s t x GEN_PVAR_121 y) = (term1606 A B _48808 s t x GEN_PVAR_121 y).
Proof. exact (eq_refl (term1605 A B _48808 s t x GEN_PVAR_121 y)). Qed.
Lemma lem4310244 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) (x : type1207 A B) (GEN_PVAR_121 : prod A B) (y : B) : (term1604 A B _48808 s t x GEN_PVAR_121 y) = (term1606 A B _48808 s t x GEN_PVAR_121 y).
Proof. exact (TRANS (@lem4310242 A B _48808 s t x GEN_PVAR_121 y) (@lem4310243 A B _48808 s t x GEN_PVAR_121 y)). Qed.
Lemma lem4310245 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) (x : type1207 A B) (GEN_PVAR_121 : prod A B) : (term1607 A B _48808 s t x GEN_PVAR_121) = (term1603 A B _48808 s t x GEN_PVAR_121).
Proof. exact (fun_ext (fun y : B => @lem4310244 A B _48808 s t x GEN_PVAR_121 y)). Qed.
Lemma lem4310246 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4310247 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) (x : type1207 A B) (GEN_PVAR_121 : prod A B) : (term1608 A B _48808 s t x GEN_PVAR_121) = (term1589 A B _48808 s t x GEN_PVAR_121).
Proof. exact (MK_COMB (@lem4310246 B) (@lem4310245 A B _48808 s t x GEN_PVAR_121)). Qed.
Lemma lem4310248 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) (x : type1207 A B) : (term1609 A B _48808 s t x) = (term1591 A B _48808 s t x).
Proof. exact (fun_ext (fun GEN_PVAR_121 : prod A B => @lem4310247 A B _48808 s t x GEN_PVAR_121)). Qed.
Lemma lem4310249 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem4310250 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) (x : type1207 A B) : (term1599 A B _48808 s t x) = (term1593 A B _48808 s t x).
Proof. exact (MK_COMB (@lem4310249 A B) (@lem4310248 A B _48808 s t x)). Qed.
Lemma lem4310251 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4310252 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) (x : type1207 A B) : (term1610 A B _48808 s t x) = (term1611 A B _48808 s t x).
Proof. exact (MK_COMB (@lem4310251) (@lem4310250 A B _48808 s t x)). Qed.
Lemma lem4310253 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) (x : type1207 A B) (GEN_PVAR_121 : prod A B) : (term1602 A B _48808 s t x GEN_PVAR_121) = (term1603 A B _48808 s t x GEN_PVAR_121).
Proof. exact (eq_refl (term1602 A B _48808 s t x GEN_PVAR_121)). Qed.
Lemma lem4310254 {A B : Type'} (y : type1208 A B) (GEN_PVAR_121 : prod A B) : (y GEN_PVAR_121) = (y GEN_PVAR_121).
Proof. exact (eq_refl (y GEN_PVAR_121)). Qed.
Lemma lem4310255 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) (x : type1207 A B) (y : type1208 A B) (GEN_PVAR_121 : prod A B) : (term1612 A B _48808 s t x y GEN_PVAR_121) = (term1613 A B _48808 s t x y GEN_PVAR_121).
Proof. exact (MK_COMB (@lem4310253 A B _48808 s t x GEN_PVAR_121) (@lem4310254 A B y GEN_PVAR_121)). Qed.
Lemma lem4310256 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) (x : type1207 A B) (y : type1208 A B) (GEN_PVAR_121 : prod A B) : (term1613 A B _48808 s t x y GEN_PVAR_121) = (term1614 A B _48808 s t x y GEN_PVAR_121).
Proof. exact (eq_refl (term1613 A B _48808 s t x y GEN_PVAR_121)). Qed.
Lemma lem4310257 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) (x : type1207 A B) (y : type1208 A B) (GEN_PVAR_121 : prod A B) : (term1612 A B _48808 s t x y GEN_PVAR_121) = (term1614 A B _48808 s t x y GEN_PVAR_121).
Proof. exact (TRANS (@lem4310255 A B _48808 s t x y GEN_PVAR_121) (@lem4310256 A B _48808 s t x y GEN_PVAR_121)). Qed.
Lemma lem4310258 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) (x : type1207 A B) (y : type1208 A B) : (term1615 A B _48808 s t x y) = (term1616 A B _48808 s t x y).
Proof. exact (fun_ext (fun GEN_PVAR_121 : prod A B => @lem4310257 A B _48808 s t x y GEN_PVAR_121)). Qed.
Lemma lem4310259 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem4310260 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) (x : type1207 A B) (y : type1208 A B) : (term1617 A B _48808 s t x y) = (term1618 A B _48808 s t x y).
Proof. exact (MK_COMB (@lem4310259 A B) (@lem4310258 A B _48808 s t x y)). Qed.
Lemma lem4310261 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) (x : type1207 A B) : (term1619 A B _48808 s t x) = (term1620 A B _48808 s t x).
Proof. exact (fun_ext (fun y : type1208 A B => @lem4310260 A B _48808 s t x y)). Qed.
Lemma lem4310262 {A B : Type'} : (@ex ((prod A B) -> B)) = (@ex ((prod A B) -> B)).
Proof. exact (eq_refl (@ex ((prod A B) -> B))). Qed.
Lemma lem4310263 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) (x : type1207 A B) : (term1600 A B _48808 s t x) = (term1621 A B _48808 s t x).
Proof. exact (MK_COMB (@lem4310262 A B) (@lem4310261 A B _48808 s t x)). Qed.
Lemma lem4310264 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) (x : type1207 A B) : ((term1599 A B _48808 s t x) = (term1600 A B _48808 s t x)) = ((term1593 A B _48808 s t x) = (term1621 A B _48808 s t x)).
Proof. exact (MK_COMB (@lem4310252 A B _48808 s t x) (@lem4310263 A B _48808 s t x)). Qed.
Lemma lem4310265 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) (x : type1207 A B) : (term1593 A B _48808 s t x) = (term1621 A B _48808 s t x).
Proof. exact (EQ_MP (@lem4310264 A B _48808 s t x) (@lem4310239 A B _48808 s t x)). Qed.
Lemma lem4310266 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1595 A B _48808 s t) = (term1622 A B _48808 s t).
Proof. exact (fun_ext (fun x : type1207 A B => @lem4310265 A B _48808 s t x)). Qed.
Lemma lem4310267 {A B : Type'} : (@ex ((prod A B) -> A)) = (@ex ((prod A B) -> A)).
Proof. exact (eq_refl (@ex ((prod A B) -> A))). Qed.
Lemma lem4310268 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1596 A B _48808 s t) = (term1623 A B _48808 s t).
Proof. exact (MK_COMB (@lem4310267 A B) (@lem4310266 A B _48808 s t)). Qed.
Lemma lem4310269 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1571 A B _48808 s t) = (term1623 A B _48808 s t).
Proof. exact (TRANS (@lem4310235 A B _48808 s t) (@lem4310268 A B _48808 s t)). Qed.
Lemma lem4310270 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1493 A B _48808 s t) = (term1623 A B _48808 s t).
Proof. exact (TRANS (@lem4310205 A B _48808 s t) (@lem4310269 A B _48808 s t)). Qed.
Lemma lem4310271 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1502 A B _48808 s) = (term1624 A B _48808 s).
Proof. exact (fun_ext (fun t : type1413 A B => @lem4310270 A B _48808 s t)). Qed.
Lemma lem4310272 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem4310273 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1517 A B _48808 s) = (term1625 A B _48808 s).
Proof. exact (MK_COMB (@lem4310272 A B) (@lem4310271 A B _48808 s)). Qed.
Lemma lem4310275 {A B : Type'} (P : type1413 A B) : (term1572 A B P) = (term1573 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4310276 {A B : Type'} (P : type450 A B) : (term1626 A B P) = (term1627 A B P).
Proof. exact (@lem4310275 (type1413 A B) (type1207 A B) P). Qed.
Lemma lem4310277 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1628 A B _48808 s) = (term1629 A B _48808 s).
Proof. exact (@lem4310276 A B (term1630 A B _48808 s)). Qed.
Lemma lem4310278 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1631 A B _48808 s t) = (term1622 A B _48808 s t).
Proof. exact (eq_refl (term1631 A B _48808 s t)). Qed.
Lemma lem4310279 {A B : Type'} (x : type1207 A B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4310280 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) (x : type1207 A B) : (term1632 A B _48808 s t x) = (term1633 A B _48808 s t x).
Proof. exact (MK_COMB (@lem4310278 A B _48808 s t) (@lem4310279 A B x)). Qed.
Lemma lem4310281 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) (x : type1207 A B) : (term1633 A B _48808 s t x) = (term1621 A B _48808 s t x).
Proof. exact (eq_refl (term1633 A B _48808 s t x)). Qed.
Lemma lem4310282 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) (x : type1207 A B) : (term1632 A B _48808 s t x) = (term1621 A B _48808 s t x).
Proof. exact (TRANS (@lem4310280 A B _48808 s t x) (@lem4310281 A B _48808 s t x)). Qed.
Lemma lem4310283 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1634 A B _48808 s t) = (term1622 A B _48808 s t).
Proof. exact (fun_ext (fun x : type1207 A B => @lem4310282 A B _48808 s t x)). Qed.
Lemma lem4310284 {A B : Type'} : (@ex ((prod A B) -> A)) = (@ex ((prod A B) -> A)).
Proof. exact (eq_refl (@ex ((prod A B) -> A))). Qed.
Lemma lem4310285 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1635 A B _48808 s t) = (term1623 A B _48808 s t).
Proof. exact (MK_COMB (@lem4310284 A B) (@lem4310283 A B _48808 s t)). Qed.
Lemma lem4310286 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1636 A B _48808 s) = (term1624 A B _48808 s).
Proof. exact (fun_ext (fun t : type1413 A B => @lem4310285 A B _48808 s t)). Qed.
Lemma lem4310287 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem4310288 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1628 A B _48808 s) = (term1625 A B _48808 s).
Proof. exact (MK_COMB (@lem4310287 A B) (@lem4310286 A B _48808 s)). Qed.
Lemma lem4310289 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4310290 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1637 A B _48808 s) = (term1638 A B _48808 s).
Proof. exact (MK_COMB (@lem4310289) (@lem4310288 A B _48808 s)). Qed.
Lemma lem4310291 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (t : type1413 A B) : (term1631 A B _48808 s t) = (term1622 A B _48808 s t).
Proof. exact (eq_refl (term1631 A B _48808 s t)). Qed.
Lemma lem4310292 {A B : Type'} (x : type464 A B) (t : type1413 A B) : (x t) = (x t).
Proof. exact (eq_refl (x t)). Qed.
Lemma lem4310293 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (x : type464 A B) (t : type1413 A B) : (term1639 A B _48808 s x t) = (term1640 A B _48808 s x t).
Proof. exact (MK_COMB (@lem4310291 A B _48808 s t) (@lem4310292 A B x t)). Qed.
Lemma lem4310294 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (x : type464 A B) (t : type1413 A B) : (term1640 A B _48808 s x t) = (term1641 A B _48808 s x t).
Proof. exact (eq_refl (term1640 A B _48808 s x t)). Qed.
Lemma lem4310295 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (x : type464 A B) (t : type1413 A B) : (term1639 A B _48808 s x t) = (term1641 A B _48808 s x t).
Proof. exact (TRANS (@lem4310293 A B _48808 s x t) (@lem4310294 A B _48808 s x t)). Qed.
Lemma lem4310296 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (x : type464 A B) : (term1642 A B _48808 s x) = (term1643 A B _48808 s x).
Proof. exact (fun_ext (fun t : type1413 A B => @lem4310295 A B _48808 s x t)). Qed.
Lemma lem4310297 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem4310298 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (x : type464 A B) : (term1644 A B _48808 s x) = (term1645 A B _48808 s x).
Proof. exact (MK_COMB (@lem4310297 A B) (@lem4310296 A B _48808 s x)). Qed.
Lemma lem4310299 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1646 A B _48808 s) = (term1647 A B _48808 s).
Proof. exact (fun_ext (fun x : type464 A B => @lem4310298 A B _48808 s x)). Qed.
Lemma lem4310300 {A B : Type'} : (@ex ((A -> B -> Prop) -> (prod A B) -> A)) = (@ex ((A -> B -> Prop) -> (prod A B) -> A)).
Proof. exact (eq_refl (@ex ((A -> B -> Prop) -> (prod A B) -> A))). Qed.
Lemma lem4310301 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1629 A B _48808 s) = (term1648 A B _48808 s).
Proof. exact (MK_COMB (@lem4310300 A B) (@lem4310299 A B _48808 s)). Qed.
Lemma lem4310302 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : ((term1628 A B _48808 s) = (term1629 A B _48808 s)) = ((term1625 A B _48808 s) = (term1648 A B _48808 s)).
Proof. exact (MK_COMB (@lem4310290 A B _48808 s) (@lem4310301 A B _48808 s)). Qed.
Lemma lem4310303 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1625 A B _48808 s) = (term1648 A B _48808 s).
Proof. exact (EQ_MP (@lem4310302 A B _48808 s) (@lem4310277 A B _48808 s)). Qed.
Lemma lem4310305 {A B : Type'} (P : type1413 A B) : (term1572 A B P) = (term1573 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4310306 {A B : Type'} (P : type451 A B) : (term1649 A B P) = (term1650 A B P).
Proof. exact (@lem4310305 (type1413 A B) (type1208 A B) P). Qed.
Lemma lem4310307 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (x : type464 A B) : (term1651 A B _48808 s x) = (term1652 A B _48808 s x).
Proof. exact (@lem4310306 A B (term1653 A B _48808 s x)). Qed.
Lemma lem4310308 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (x : type464 A B) (t : type1413 A B) : (term1654 A B _48808 s x t) = (term1655 A B _48808 s x t).
Proof. exact (eq_refl (term1654 A B _48808 s x t)). Qed.
Lemma lem4310309 {A B : Type'} (y : type1208 A B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4310310 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (x : type464 A B) (t : type1413 A B) (y : type1208 A B) : (term1656 A B _48808 s x t y) = (term1657 A B _48808 s x t y).
Proof. exact (MK_COMB (@lem4310308 A B _48808 s x t) (@lem4310309 A B y)). Qed.
Lemma lem4310311 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (x : type464 A B) (t : type1413 A B) (y : type1208 A B) : (term1657 A B _48808 s x t y) = (term1658 A B _48808 s x t y).
Proof. exact (eq_refl (term1657 A B _48808 s x t y)). Qed.
Lemma lem4310312 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (x : type464 A B) (t : type1413 A B) (y : type1208 A B) : (term1656 A B _48808 s x t y) = (term1658 A B _48808 s x t y).
Proof. exact (TRANS (@lem4310310 A B _48808 s x t y) (@lem4310311 A B _48808 s x t y)). Qed.
Lemma lem4310313 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (x : type464 A B) (t : type1413 A B) : (term1659 A B _48808 s x t) = (term1655 A B _48808 s x t).
Proof. exact (fun_ext (fun y : type1208 A B => @lem4310312 A B _48808 s x t y)). Qed.
Lemma lem4310314 {A B : Type'} : (@ex ((prod A B) -> B)) = (@ex ((prod A B) -> B)).
Proof. exact (eq_refl (@ex ((prod A B) -> B))). Qed.
Lemma lem4310315 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (x : type464 A B) (t : type1413 A B) : (term1660 A B _48808 s x t) = (term1641 A B _48808 s x t).
Proof. exact (MK_COMB (@lem4310314 A B) (@lem4310313 A B _48808 s x t)). Qed.
Lemma lem4310316 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (x : type464 A B) : (term1661 A B _48808 s x) = (term1643 A B _48808 s x).
Proof. exact (fun_ext (fun t : type1413 A B => @lem4310315 A B _48808 s x t)). Qed.
Lemma lem4310317 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem4310318 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (x : type464 A B) : (term1651 A B _48808 s x) = (term1645 A B _48808 s x).
Proof. exact (MK_COMB (@lem4310317 A B) (@lem4310316 A B _48808 s x)). Qed.
Lemma lem4310319 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4310320 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (x : type464 A B) : (term1662 A B _48808 s x) = (term1663 A B _48808 s x).
Proof. exact (MK_COMB (@lem4310319) (@lem4310318 A B _48808 s x)). Qed.
Lemma lem4310321 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (x : type464 A B) (t : type1413 A B) : (term1654 A B _48808 s x t) = (term1655 A B _48808 s x t).
Proof. exact (eq_refl (term1654 A B _48808 s x t)). Qed.
Lemma lem4310322 {A B : Type'} (y : type465 A B) (t : type1413 A B) : (y t) = (y t).
Proof. exact (eq_refl (y t)). Qed.
Lemma lem4310323 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (x : type464 A B) (y : type465 A B) (t : type1413 A B) : (term1664 A B _48808 s x y t) = (term1665 A B _48808 s x y t).
Proof. exact (MK_COMB (@lem4310321 A B _48808 s x t) (@lem4310322 A B y t)). Qed.
Lemma lem4310324 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (x : type464 A B) (y : type465 A B) (t : type1413 A B) : (term1665 A B _48808 s x y t) = (term1666 A B _48808 s x y t).
Proof. exact (eq_refl (term1665 A B _48808 s x y t)). Qed.
Lemma lem4310325 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (x : type464 A B) (y : type465 A B) (t : type1413 A B) : (term1664 A B _48808 s x y t) = (term1666 A B _48808 s x y t).
Proof. exact (TRANS (@lem4310323 A B _48808 s x y t) (@lem4310324 A B _48808 s x y t)). Qed.
Lemma lem4310326 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (x : type464 A B) (y : type465 A B) : (term1667 A B _48808 s x y) = (term1668 A B _48808 s x y).
Proof. exact (fun_ext (fun t : type1413 A B => @lem4310325 A B _48808 s x y t)). Qed.
Lemma lem4310327 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem4310328 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (x : type464 A B) (y : type465 A B) : (term1669 A B _48808 s x y) = (term1670 A B _48808 s x y).
Proof. exact (MK_COMB (@lem4310327 A B) (@lem4310326 A B _48808 s x y)). Qed.
Lemma lem4310329 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (x : type464 A B) : (term1671 A B _48808 s x) = (term1672 A B _48808 s x).
Proof. exact (fun_ext (fun y : type465 A B => @lem4310328 A B _48808 s x y)). Qed.
Lemma lem4310330 {A B : Type'} : (@ex ((A -> B -> Prop) -> (prod A B) -> B)) = (@ex ((A -> B -> Prop) -> (prod A B) -> B)).
Proof. exact (eq_refl (@ex ((A -> B -> Prop) -> (prod A B) -> B))). Qed.
Lemma lem4310331 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (x : type464 A B) : (term1652 A B _48808 s x) = (term1673 A B _48808 s x).
Proof. exact (MK_COMB (@lem4310330 A B) (@lem4310329 A B _48808 s x)). Qed.
Lemma lem4310332 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (x : type464 A B) : ((term1651 A B _48808 s x) = (term1652 A B _48808 s x)) = ((term1645 A B _48808 s x) = (term1673 A B _48808 s x)).
Proof. exact (MK_COMB (@lem4310320 A B _48808 s x) (@lem4310331 A B _48808 s x)). Qed.
Lemma lem4310333 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (x : type464 A B) : (term1645 A B _48808 s x) = (term1673 A B _48808 s x).
Proof. exact (EQ_MP (@lem4310332 A B _48808 s x) (@lem4310307 A B _48808 s x)). Qed.
Lemma lem4310334 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1647 A B _48808 s) = (term1674 A B _48808 s).
Proof. exact (fun_ext (fun x : type464 A B => @lem4310333 A B _48808 s x)). Qed.
Lemma lem4310335 {A B : Type'} : (@ex ((A -> B -> Prop) -> (prod A B) -> A)) = (@ex ((A -> B -> Prop) -> (prod A B) -> A)).
Proof. exact (eq_refl (@ex ((A -> B -> Prop) -> (prod A B) -> A))). Qed.
Lemma lem4310336 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1648 A B _48808 s) = (term1675 A B _48808 s).
Proof. exact (MK_COMB (@lem4310335 A B) (@lem4310334 A B _48808 s)). Qed.
Lemma lem4310337 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1625 A B _48808 s) = (term1675 A B _48808 s).
Proof. exact (TRANS (@lem4310303 A B _48808 s) (@lem4310336 A B _48808 s)). Qed.
Lemma lem4310338 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1517 A B _48808 s) = (term1675 A B _48808 s).
Proof. exact (TRANS (@lem4310273 A B _48808 s) (@lem4310337 A B _48808 s)). Qed.
Lemma lem4310339 {A B : Type'} (_48808 : type621 A B) : (term1526 A B _48808) = (term1676 A B _48808).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4310338 A B _48808 s)). Qed.
Lemma lem4310340 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4310341 {A B : Type'} (_48808 : type621 A B) : (term1541 A B _48808) = (term1677 A B _48808).
Proof. exact (MK_COMB (@lem4310340 A) (@lem4310339 A B _48808)). Qed.
Lemma lem4310343 {A B : Type'} (P : type1413 A B) : (term1572 A B P) = (term1573 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4310344 {A B : Type'} (P : type584 A B) : (term1678 A B P) = (term1679 A B P).
Proof. exact (@lem4310343 (A -> Prop) (type464 A B) P). Qed.
Lemma lem4310345 {A B : Type'} (_48808 : type621 A B) : (term1680 A B _48808) = (term1681 A B _48808).
Proof. exact (@lem4310344 A B (term1682 A B _48808)). Qed.
Lemma lem4310346 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1683 A B _48808 s) = (term1674 A B _48808 s).
Proof. exact (eq_refl (term1683 A B _48808 s)). Qed.
Lemma lem4310347 {A B : Type'} (x : type464 A B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4310348 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (x : type464 A B) : (term1684 A B _48808 s x) = (term1685 A B _48808 s x).
Proof. exact (MK_COMB (@lem4310346 A B _48808 s) (@lem4310347 A B x)). Qed.
Lemma lem4310349 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (x : type464 A B) : (term1685 A B _48808 s x) = (term1673 A B _48808 s x).
Proof. exact (eq_refl (term1685 A B _48808 s x)). Qed.
Lemma lem4310350 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (x : type464 A B) : (term1684 A B _48808 s x) = (term1673 A B _48808 s x).
Proof. exact (TRANS (@lem4310348 A B _48808 s x) (@lem4310349 A B _48808 s x)). Qed.
Lemma lem4310351 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1686 A B _48808 s) = (term1674 A B _48808 s).
Proof. exact (fun_ext (fun x : type464 A B => @lem4310350 A B _48808 s x)). Qed.
Lemma lem4310352 {A B : Type'} : (@ex ((A -> B -> Prop) -> (prod A B) -> A)) = (@ex ((A -> B -> Prop) -> (prod A B) -> A)).
Proof. exact (eq_refl (@ex ((A -> B -> Prop) -> (prod A B) -> A))). Qed.
Lemma lem4310353 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1687 A B _48808 s) = (term1675 A B _48808 s).
Proof. exact (MK_COMB (@lem4310352 A B) (@lem4310351 A B _48808 s)). Qed.
Lemma lem4310354 {A B : Type'} (_48808 : type621 A B) : (term1688 A B _48808) = (term1676 A B _48808).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4310353 A B _48808 s)). Qed.
Lemma lem4310355 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4310356 {A B : Type'} (_48808 : type621 A B) : (term1680 A B _48808) = (term1677 A B _48808).
Proof. exact (MK_COMB (@lem4310355 A) (@lem4310354 A B _48808)). Qed.
Lemma lem4310357 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4310358 {A B : Type'} (_48808 : type621 A B) : (term1689 A B _48808) = (term1690 A B _48808).
Proof. exact (MK_COMB (@lem4310357) (@lem4310356 A B _48808)). Qed.
Lemma lem4310359 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1683 A B _48808 s) = (term1674 A B _48808 s).
Proof. exact (eq_refl (term1683 A B _48808 s)). Qed.
Lemma lem4310360 {A B : Type'} (x : type619 A B) (s : A -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem4310361 {A B : Type'} (_48808 : type621 A B) (x : type619 A B) (s : A -> Prop) : (term1691 A B _48808 x s) = (term1692 A B _48808 x s).
Proof. exact (MK_COMB (@lem4310359 A B _48808 s) (@lem4310360 A B x s)). Qed.
Lemma lem4310362 {A B : Type'} (_48808 : type621 A B) (x : type619 A B) (s : A -> Prop) : (term1692 A B _48808 x s) = (term1693 A B _48808 x s).
Proof. exact (eq_refl (term1692 A B _48808 x s)). Qed.
Lemma lem4310363 {A B : Type'} (_48808 : type621 A B) (x : type619 A B) (s : A -> Prop) : (term1691 A B _48808 x s) = (term1693 A B _48808 x s).
Proof. exact (TRANS (@lem4310361 A B _48808 x s) (@lem4310362 A B _48808 x s)). Qed.
Lemma lem4310364 {A B : Type'} (_48808 : type621 A B) (x : type619 A B) : (term1694 A B _48808 x) = (term1695 A B _48808 x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4310363 A B _48808 x s)). Qed.
Lemma lem4310365 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4310366 {A B : Type'} (_48808 : type621 A B) (x : type619 A B) : (term1696 A B _48808 x) = (term1697 A B _48808 x).
Proof. exact (MK_COMB (@lem4310365 A) (@lem4310364 A B _48808 x)). Qed.
Lemma lem4310367 {A B : Type'} (_48808 : type621 A B) : (term1698 A B _48808) = (term1699 A B _48808).
Proof. exact (fun_ext (fun x : type619 A B => @lem4310366 A B _48808 x)). Qed.
Lemma lem4310368 {A B : Type'} : (@ex ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> A)) = (@ex ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> A))). Qed.
Lemma lem4310369 {A B : Type'} (_48808 : type621 A B) : (term1681 A B _48808) = (term1700 A B _48808).
Proof. exact (MK_COMB (@lem4310368 A B) (@lem4310367 A B _48808)). Qed.
Lemma lem4310370 {A B : Type'} (_48808 : type621 A B) : ((term1680 A B _48808) = (term1681 A B _48808)) = ((term1677 A B _48808) = (term1700 A B _48808)).
Proof. exact (MK_COMB (@lem4310358 A B _48808) (@lem4310369 A B _48808)). Qed.
Lemma lem4310371 {A B : Type'} (_48808 : type621 A B) : (term1677 A B _48808) = (term1700 A B _48808).
Proof. exact (EQ_MP (@lem4310370 A B _48808) (@lem4310345 A B _48808)). Qed.
Lemma lem4310373 {A B : Type'} (P : type1413 A B) : (term1572 A B P) = (term1573 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4310374 {A B : Type'} (P : type585 A B) : (term1701 A B P) = (term1702 A B P).
Proof. exact (@lem4310373 (A -> Prop) (type465 A B) P). Qed.
Lemma lem4310375 {A B : Type'} (_48808 : type621 A B) (x : type619 A B) : (term1703 A B _48808 x) = (term1704 A B _48808 x).
Proof. exact (@lem4310374 A B (term1705 A B _48808 x)). Qed.
Lemma lem4310376 {A B : Type'} (_48808 : type621 A B) (x : type619 A B) (s : A -> Prop) : (term1706 A B _48808 x s) = (term1707 A B _48808 x s).
Proof. exact (eq_refl (term1706 A B _48808 x s)). Qed.
Lemma lem4310377 {A B : Type'} (y : type465 A B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4310378 {A B : Type'} (_48808 : type621 A B) (x : type619 A B) (s : A -> Prop) (y : type465 A B) : (term1708 A B _48808 x s y) = (term1709 A B _48808 x s y).
Proof. exact (MK_COMB (@lem4310376 A B _48808 x s) (@lem4310377 A B y)). Qed.
Lemma lem4310379 {A B : Type'} (_48808 : type621 A B) (x : type619 A B) (s : A -> Prop) (y : type465 A B) : (term1709 A B _48808 x s y) = (term1710 A B _48808 x s y).
Proof. exact (eq_refl (term1709 A B _48808 x s y)). Qed.
Lemma lem4310380 {A B : Type'} (_48808 : type621 A B) (x : type619 A B) (s : A -> Prop) (y : type465 A B) : (term1708 A B _48808 x s y) = (term1710 A B _48808 x s y).
Proof. exact (TRANS (@lem4310378 A B _48808 x s y) (@lem4310379 A B _48808 x s y)). Qed.
Lemma lem4310381 {A B : Type'} (_48808 : type621 A B) (x : type619 A B) (s : A -> Prop) : (term1711 A B _48808 x s) = (term1707 A B _48808 x s).
Proof. exact (fun_ext (fun y : type465 A B => @lem4310380 A B _48808 x s y)). Qed.
Lemma lem4310382 {A B : Type'} : (@ex ((A -> B -> Prop) -> (prod A B) -> B)) = (@ex ((A -> B -> Prop) -> (prod A B) -> B)).
Proof. exact (eq_refl (@ex ((A -> B -> Prop) -> (prod A B) -> B))). Qed.
Lemma lem4310383 {A B : Type'} (_48808 : type621 A B) (x : type619 A B) (s : A -> Prop) : (term1712 A B _48808 x s) = (term1693 A B _48808 x s).
Proof. exact (MK_COMB (@lem4310382 A B) (@lem4310381 A B _48808 x s)). Qed.
Lemma lem4310384 {A B : Type'} (_48808 : type621 A B) (x : type619 A B) : (term1713 A B _48808 x) = (term1695 A B _48808 x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4310383 A B _48808 x s)). Qed.
Lemma lem4310385 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4310386 {A B : Type'} (_48808 : type621 A B) (x : type619 A B) : (term1703 A B _48808 x) = (term1697 A B _48808 x).
Proof. exact (MK_COMB (@lem4310385 A) (@lem4310384 A B _48808 x)). Qed.
Lemma lem4310387 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4310388 {A B : Type'} (_48808 : type621 A B) (x : type619 A B) : (term1714 A B _48808 x) = (term1715 A B _48808 x).
Proof. exact (MK_COMB (@lem4310387) (@lem4310386 A B _48808 x)). Qed.
Lemma lem4310389 {A B : Type'} (_48808 : type621 A B) (x : type619 A B) (s : A -> Prop) : (term1706 A B _48808 x s) = (term1707 A B _48808 x s).
Proof. exact (eq_refl (term1706 A B _48808 x s)). Qed.
Lemma lem4310390 {A B : Type'} (y : type620 A B) (s : A -> Prop) : (y s) = (y s).
Proof. exact (eq_refl (y s)). Qed.
Lemma lem4310391 {A B : Type'} (_48808 : type621 A B) (x : type619 A B) (y : type620 A B) (s : A -> Prop) : (term1716 A B _48808 x y s) = (term1717 A B _48808 x y s).
Proof. exact (MK_COMB (@lem4310389 A B _48808 x s) (@lem4310390 A B y s)). Qed.
Lemma lem4310392 {A B : Type'} (_48808 : type621 A B) (x : type619 A B) (y : type620 A B) (s : A -> Prop) : (term1717 A B _48808 x y s) = (term1718 A B _48808 x y s).
Proof. exact (eq_refl (term1717 A B _48808 x y s)). Qed.
Lemma lem4310393 {A B : Type'} (_48808 : type621 A B) (x : type619 A B) (y : type620 A B) (s : A -> Prop) : (term1716 A B _48808 x y s) = (term1718 A B _48808 x y s).
Proof. exact (TRANS (@lem4310391 A B _48808 x y s) (@lem4310392 A B _48808 x y s)). Qed.
Lemma lem4310394 {A B : Type'} (_48808 : type621 A B) (x : type619 A B) (y : type620 A B) : (term1719 A B _48808 x y) = (term1720 A B _48808 x y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4310393 A B _48808 x y s)). Qed.
Lemma lem4310395 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4310396 {A B : Type'} (_48808 : type621 A B) (x : type619 A B) (y : type620 A B) : (term1721 A B _48808 x y) = (term1722 A B _48808 x y).
Proof. exact (MK_COMB (@lem4310395 A) (@lem4310394 A B _48808 x y)). Qed.
Lemma lem4310397 {A B : Type'} (_48808 : type621 A B) (x : type619 A B) : (term1723 A B _48808 x) = (term1724 A B _48808 x).
Proof. exact (fun_ext (fun y : type620 A B => @lem4310396 A B _48808 x y)). Qed.
Lemma lem4310398 {A B : Type'} : (@ex ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> B)) = (@ex ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> B)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> B))). Qed.
Lemma lem4310399 {A B : Type'} (_48808 : type621 A B) (x : type619 A B) : (term1704 A B _48808 x) = (term1725 A B _48808 x).
Proof. exact (MK_COMB (@lem4310398 A B) (@lem4310397 A B _48808 x)). Qed.
Lemma lem4310400 {A B : Type'} (_48808 : type621 A B) (x : type619 A B) : ((term1703 A B _48808 x) = (term1704 A B _48808 x)) = ((term1697 A B _48808 x) = (term1725 A B _48808 x)).
Proof. exact (MK_COMB (@lem4310388 A B _48808 x) (@lem4310399 A B _48808 x)). Qed.
Lemma lem4310401 {A B : Type'} (_48808 : type621 A B) (x : type619 A B) : (term1697 A B _48808 x) = (term1725 A B _48808 x).
Proof. exact (EQ_MP (@lem4310400 A B _48808 x) (@lem4310375 A B _48808 x)). Qed.
Lemma lem4310402 {A B : Type'} (_48808 : type621 A B) : (term1699 A B _48808) = (term1726 A B _48808).
Proof. exact (fun_ext (fun x : type619 A B => @lem4310401 A B _48808 x)). Qed.
Lemma lem4310403 {A B : Type'} : (@ex ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> A)) = (@ex ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> A))). Qed.
Lemma lem4310404 {A B : Type'} (_48808 : type621 A B) : (term1700 A B _48808) = (term1727 A B _48808).
Proof. exact (MK_COMB (@lem4310403 A B) (@lem4310402 A B _48808)). Qed.
Lemma lem4310405 {A B : Type'} (_48808 : type621 A B) : (term1677 A B _48808) = (term1727 A B _48808).
Proof. exact (TRANS (@lem4310371 A B _48808) (@lem4310404 A B _48808)). Qed.
Lemma lem4310406 {A B : Type'} (_48808 : type621 A B) : (term1541 A B _48808) = (term1727 A B _48808).
Proof. exact (TRANS (@lem4310341 A B _48808) (@lem4310405 A B _48808)). Qed.
Lemma lem4310407 {A B : Type'} (_48808 : type621 A B) : (term1538 A B _48808) = (term1538 A B _48808).
Proof. exact (eq_refl (term1538 A B _48808)). Qed.
Lemma lem4310408 {A B : Type'} (_48808 : type621 A B) : (term1542 A B _48808) = (term1728 A B _48808).
Proof. exact (MK_COMB (@lem4310407 A B _48808) (@lem4310406 A B _48808)). Qed.
Lemma lem4310410 {A : Type'} (P : Prop) (Q : A -> Prop) : (term353 A P Q) = (term354 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4310411 {A B : Type'} (P : Prop) (Q : type128 A B) : (term1729 A B P Q) = (term1730 A B P Q).
Proof. exact (@lem4310410 (type619 A B) P Q). Qed.
Lemma lem4310412 {A B : Type'} (_48808 : type621 A B) : (term1731 A B _48808) = (term1732 A B _48808).
Proof. exact (@lem4310411 A B (term1536 A B _48808) (term1726 A B _48808)). Qed.
Lemma lem4310413 {A B : Type'} (_48808 : type621 A B) (x : type619 A B) : (term1733 A B _48808 x) = (term1725 A B _48808 x).
Proof. exact (eq_refl (term1733 A B _48808 x)). Qed.
Lemma lem4310414 {A B : Type'} (_48808 : type621 A B) : (term1734 A B _48808) = (term1726 A B _48808).
Proof. exact (fun_ext (fun x : type619 A B => @lem4310413 A B _48808 x)). Qed.
Lemma lem4310415 {A B : Type'} : (@ex ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> A)) = (@ex ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> A))). Qed.
Lemma lem4310416 {A B : Type'} (_48808 : type621 A B) : (term1735 A B _48808) = (term1727 A B _48808).
Proof. exact (MK_COMB (@lem4310415 A B) (@lem4310414 A B _48808)). Qed.
Lemma lem4310417 {A B : Type'} (_48808 : type621 A B) : (term1538 A B _48808) = (term1538 A B _48808).
Proof. exact (eq_refl (term1538 A B _48808)). Qed.
Lemma lem4310418 {A B : Type'} (_48808 : type621 A B) : (term1731 A B _48808) = (term1728 A B _48808).
Proof. exact (MK_COMB (@lem4310417 A B _48808) (@lem4310416 A B _48808)). Qed.
Lemma lem4310419 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4310420 {A B : Type'} (_48808 : type621 A B) : (term1736 A B _48808) = (term1737 A B _48808).
Proof. exact (MK_COMB (@lem4310419) (@lem4310418 A B _48808)). Qed.
Lemma lem4310421 {A B : Type'} (_48808 : type621 A B) (x : type619 A B) : (term1733 A B _48808 x) = (term1725 A B _48808 x).
Proof. exact (eq_refl (term1733 A B _48808 x)). Qed.
Lemma lem4310422 {A B : Type'} (_48808 : type621 A B) : (term1538 A B _48808) = (term1538 A B _48808).
Proof. exact (eq_refl (term1538 A B _48808)). Qed.
Lemma lem4310423 {A B : Type'} (_48808 : type621 A B) (x : type619 A B) : (term1738 A B _48808 x) = (term1739 A B _48808 x).
Proof. exact (MK_COMB (@lem4310422 A B _48808) (@lem4310421 A B _48808 x)). Qed.
Lemma lem4310424 {A B : Type'} (_48808 : type621 A B) : (term1740 A B _48808) = (term1741 A B _48808).
Proof. exact (fun_ext (fun x : type619 A B => @lem4310423 A B _48808 x)). Qed.
Lemma lem4310425 {A B : Type'} : (@ex ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> A)) = (@ex ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> A))). Qed.
Lemma lem4310426 {A B : Type'} (_48808 : type621 A B) : (term1732 A B _48808) = (term1742 A B _48808).
Proof. exact (MK_COMB (@lem4310425 A B) (@lem4310424 A B _48808)). Qed.
Lemma lem4310427 {A B : Type'} (_48808 : type621 A B) : ((term1731 A B _48808) = (term1732 A B _48808)) = ((term1728 A B _48808) = (term1742 A B _48808)).
Proof. exact (MK_COMB (@lem4310420 A B _48808) (@lem4310426 A B _48808)). Qed.
Lemma lem4310428 {A B : Type'} (_48808 : type621 A B) : (term1728 A B _48808) = (term1742 A B _48808).
Proof. exact (EQ_MP (@lem4310427 A B _48808) (@lem4310412 A B _48808)). Qed.
Lemma lem4310430 {A : Type'} (P : Prop) (Q : A -> Prop) : (term353 A P Q) = (term354 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4310431 {A B : Type'} (P : Prop) (Q : type129 A B) : (term1743 A B P Q) = (term1744 A B P Q).
Proof. exact (@lem4310430 (type620 A B) P Q). Qed.
Lemma lem4310432 {A B : Type'} (_48808 : type621 A B) (x : type619 A B) : (term1745 A B _48808 x) = (term1746 A B _48808 x).
Proof. exact (@lem4310431 A B (term1536 A B _48808) (term1724 A B _48808 x)). Qed.
Lemma lem4310433 {A B : Type'} (_48808 : type621 A B) (x : type619 A B) (y : type620 A B) : (term1747 A B _48808 x y) = (term1722 A B _48808 x y).
Proof. exact (eq_refl (term1747 A B _48808 x y)). Qed.
Lemma lem4310434 {A B : Type'} (_48808 : type621 A B) (x : type619 A B) : (term1748 A B _48808 x) = (term1724 A B _48808 x).
Proof. exact (fun_ext (fun y : type620 A B => @lem4310433 A B _48808 x y)). Qed.
Lemma lem4310435 {A B : Type'} : (@ex ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> B)) = (@ex ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> B)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> B))). Qed.
Lemma lem4310436 {A B : Type'} (_48808 : type621 A B) (x : type619 A B) : (term1749 A B _48808 x) = (term1725 A B _48808 x).
Proof. exact (MK_COMB (@lem4310435 A B) (@lem4310434 A B _48808 x)). Qed.
Lemma lem4310437 {A B : Type'} (_48808 : type621 A B) : (term1538 A B _48808) = (term1538 A B _48808).
Proof. exact (eq_refl (term1538 A B _48808)). Qed.
Lemma lem4310438 {A B : Type'} (_48808 : type621 A B) (x : type619 A B) : (term1745 A B _48808 x) = (term1739 A B _48808 x).
Proof. exact (MK_COMB (@lem4310437 A B _48808) (@lem4310436 A B _48808 x)). Qed.
Lemma lem4310439 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4310440 {A B : Type'} (_48808 : type621 A B) (x : type619 A B) : (term1750 A B _48808 x) = (term1751 A B _48808 x).
Proof. exact (MK_COMB (@lem4310439) (@lem4310438 A B _48808 x)). Qed.
Lemma lem4310441 {A B : Type'} (_48808 : type621 A B) (x : type619 A B) (y : type620 A B) : (term1747 A B _48808 x y) = (term1722 A B _48808 x y).
Proof. exact (eq_refl (term1747 A B _48808 x y)). Qed.
Lemma lem4310442 {A B : Type'} (_48808 : type621 A B) : (term1538 A B _48808) = (term1538 A B _48808).
Proof. exact (eq_refl (term1538 A B _48808)). Qed.
Lemma lem4310443 {A B : Type'} (_48808 : type621 A B) (x : type619 A B) (y : type620 A B) : (term1752 A B _48808 x y) = (term1753 A B _48808 x y).
Proof. exact (MK_COMB (@lem4310442 A B _48808) (@lem4310441 A B _48808 x y)). Qed.
Lemma lem4310444 {A B : Type'} (_48808 : type621 A B) (x : type619 A B) : (term1754 A B _48808 x) = (term1755 A B _48808 x).
Proof. exact (fun_ext (fun y : type620 A B => @lem4310443 A B _48808 x y)). Qed.
Lemma lem4310445 {A B : Type'} : (@ex ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> B)) = (@ex ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> B)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> B))). Qed.
Lemma lem4310446 {A B : Type'} (_48808 : type621 A B) (x : type619 A B) : (term1746 A B _48808 x) = (term1756 A B _48808 x).
Proof. exact (MK_COMB (@lem4310445 A B) (@lem4310444 A B _48808 x)). Qed.
Lemma lem4310447 {A B : Type'} (_48808 : type621 A B) (x : type619 A B) : ((term1745 A B _48808 x) = (term1746 A B _48808 x)) = ((term1739 A B _48808 x) = (term1756 A B _48808 x)).
Proof. exact (MK_COMB (@lem4310440 A B _48808 x) (@lem4310446 A B _48808 x)). Qed.
Lemma lem4310448 {A B : Type'} (_48808 : type621 A B) (x : type619 A B) : (term1739 A B _48808 x) = (term1756 A B _48808 x).
Proof. exact (EQ_MP (@lem4310447 A B _48808 x) (@lem4310432 A B _48808 x)). Qed.
Lemma lem4310449 {A B : Type'} (_48808 : type621 A B) : (term1741 A B _48808) = (term1757 A B _48808).
Proof. exact (fun_ext (fun x : type619 A B => @lem4310448 A B _48808 x)). Qed.
Lemma lem4310450 {A B : Type'} : (@ex ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> A)) = (@ex ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> B -> Prop) -> (prod A B) -> A))). Qed.
Lemma lem4310451 {A B : Type'} (_48808 : type621 A B) : (term1742 A B _48808) = (term1758 A B _48808).
Proof. exact (MK_COMB (@lem4310450 A B) (@lem4310449 A B _48808)). Qed.
Lemma lem4310452 {A B : Type'} (_48808 : type621 A B) : (term1728 A B _48808) = (term1758 A B _48808).
Proof. exact (TRANS (@lem4310428 A B _48808) (@lem4310451 A B _48808)). Qed.
Lemma lem4310453 {A B : Type'} (_48808 : type621 A B) : (term1542 A B _48808) = (term1758 A B _48808).
Proof. exact (TRANS (@lem4310408 A B _48808) (@lem4310452 A B _48808)). Qed.
Lemma lem4310454 {A B : Type'} (_48808 : type621 A B) : (term1472 A B _48808) = (term1758 A B _48808).
Proof. exact (TRANS (@lem4310158 A B _48808) (@lem4310453 A B _48808)). Qed.
Lemma lem4310455 {A B : Type'} (_48808 : type621 A B) : (term1434 A B _48808) = (term1758 A B _48808).
Proof. exact (TRANS (@lem4309701 A B _48808) (@lem4310454 A B _48808)). Qed.
Lemma lem4310456 {A B : Type'} (_48808 : type621 A B) (h1 : term1434 A B _48808) : term1758 A B _48808.
Proof. exact (EQ_MP (@lem4310455 A B _48808) (@lem4309635 A B _48808 h1)). Qed.
Lemma lem4310462 {A : Type'} (x : A) (s : A -> Prop) (h1 : term808 A x s) : term808 A x s.
Proof. exact (h1). Qed.
Lemma lem4310550 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : A) (n : nat) : (term1759 A B s t x n) = (term1760 A B s t x n).
Proof. exact (@lem17362 (@IN A x s) (term742 A B t x n)). Qed.
Lemma lem4310551 {A : Type'} (P : A -> Prop) : (term1761 A P) = (term1762 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4310552 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (n : nat) : (term1763 A B s t n) = (term1764 A B s t n).
Proof. exact (@lem4310551 A (term983 A B s t n)). Qed.
Lemma lem4310553 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : A) (n : nat) : (term988 A B s t n x) = (term989 A B s t x n).
Proof. exact (eq_refl (term988 A B s t n x)). Qed.
Lemma lem4310554 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4310555 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : A) (n : nat) : (term1765 A B s t n x) = (term1759 A B s t x n).
Proof. exact (MK_COMB (@lem4310554) (@lem4310553 A B s t x n)). Qed.
Lemma lem4310556 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : A) (n : nat) : (term1765 A B s t n x) = (term1760 A B s t x n).
Proof. exact (TRANS (@lem4310555 A B s t x n) (@lem4310550 A B s t x n)). Qed.
Lemma lem4310557 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (n : nat) : (term1766 A B s t n) = (term1767 A B s t n).
Proof. exact (fun_ext (fun x : A => @lem4310556 A B s t x n)). Qed.
Lemma lem4310558 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4310559 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (n : nat) : (term1764 A B s t n) = (term1768 A B s t n).
Proof. exact (MK_COMB (@lem4310558 A) (@lem4310557 A B s t n)). Qed.
Lemma lem4310560 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (n : nat) : (term1763 A B s t n) = (term1768 A B s t n).
Proof. exact (TRANS (@lem4310552 A B s t n) (@lem4310559 A B s t n)). Qed.
Lemma lem4310561 {A B : Type'} (_48808 : type621 A B) (t : type1413 A B) (s : A -> Prop) (n : nat) : (term1345 A B _48808 t s n) = (term1345 A B _48808 t s n).
Proof. exact (eq_refl (term1345 A B _48808 t s n)). Qed.
Lemma lem4310562 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4310563 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (n : nat) : (term1769 A B s t n) = (term1770 A B s t n).
Proof. exact (MK_COMB (@lem4310562) (@lem4310560 A B s t n)). Qed.
Lemma lem4310564 {A B : Type'} (_48808 : type621 A B) (t : type1413 A B) (s : A -> Prop) (n : nat) : (term1771 A B _48808 t s n) = (term1772 A B _48808 t s n).
Proof. exact (MK_COMB (@lem4310563 A B s t n) (@lem4310561 A B _48808 t s n)). Qed.
Lemma lem4310565 {A B : Type'} (_48808 : type621 A B) (t : type1413 A B) (s : A -> Prop) (n : nat) : (term1346 A B _48808 t s n) = (term1771 A B _48808 t s n).
Proof. exact (@lem17265 (term581 A B s t n) (term1345 A B _48808 t s n)). Qed.
Lemma lem4310566 {A B : Type'} (_48808 : type621 A B) (t : type1413 A B) (s : A -> Prop) (n : nat) : (term1346 A B _48808 t s n) = (term1772 A B _48808 t s n).
Proof. exact (TRANS (@lem4310565 A B _48808 t s n) (@lem4310564 A B _48808 t s n)). Qed.
Lemma lem4310567 {A B : Type'} (_48808 : type621 A B) (t : type1413 A B) (s : A -> Prop) : (term1348 A B _48808 t s) = (term1773 A B _48808 t s).
Proof. exact (fun_ext (fun n : nat => @lem4310566 A B _48808 t s n)). Qed.
Lemma lem4310568 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4310569 {A B : Type'} (_48808 : type621 A B) (t : type1413 A B) (s : A -> Prop) : (term1349 A B _48808 t s) = (term1774 A B _48808 t s).
Proof. exact (MK_COMB (@lem4310568) (@lem4310567 A B _48808 t s)). Qed.
Lemma lem4310570 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1351 A B _48808 s) = (term1775 A B _48808 s).
Proof. exact (fun_ext (fun t : type1413 A B => @lem4310569 A B _48808 t s)). Qed.
Lemma lem4310571 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem4310572 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1352 A B _48808 s) = (term1776 A B _48808 s).
Proof. exact (MK_COMB (@lem4310571 A B) (@lem4310570 A B _48808 s)). Qed.
Lemma lem4310675 {A : Type'} (P : A -> Prop) (Q : Prop) : (term313 A P Q) = (term314 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4310676 {A : Type'} (P : A -> Prop) (Q : Prop) : (term313 A P Q) = (term314 A P Q).
Proof. exact (@lem4310675 A P Q). Qed.
Lemma lem4310677 {A B : Type'} (_48808 : type621 A B) (t : type1413 A B) (s : A -> Prop) (n : nat) : (term1777 A B _48808 t s n) = (term1778 A B _48808 t s n).
Proof. exact (@lem4310676 A (term1767 A B s t n) (term1345 A B _48808 t s n)). Qed.
Lemma lem4310678 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : A) (n : nat) : (term1779 A B s t n x) = (term1760 A B s t x n).
Proof. exact (eq_refl (term1779 A B s t n x)). Qed.
Lemma lem4310679 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (n : nat) : (term1780 A B s t n) = (term1767 A B s t n).
Proof. exact (fun_ext (fun x : A => @lem4310678 A B s t x n)). Qed.
Lemma lem4310680 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4310681 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (n : nat) : (term1781 A B s t n) = (term1768 A B s t n).
Proof. exact (MK_COMB (@lem4310680 A) (@lem4310679 A B s t n)). Qed.
Lemma lem4310682 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4310683 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (n : nat) : (term1782 A B s t n) = (term1770 A B s t n).
Proof. exact (MK_COMB (@lem4310682) (@lem4310681 A B s t n)). Qed.
Lemma lem4310684 {A B : Type'} (_48808 : type621 A B) (t : type1413 A B) (s : A -> Prop) (n : nat) : (term1345 A B _48808 t s n) = (term1345 A B _48808 t s n).
Proof. exact (eq_refl (term1345 A B _48808 t s n)). Qed.
Lemma lem4310685 {A B : Type'} (_48808 : type621 A B) (t : type1413 A B) (s : A -> Prop) (n : nat) : (term1777 A B _48808 t s n) = (term1772 A B _48808 t s n).
Proof. exact (MK_COMB (@lem4310683 A B s t n) (@lem4310684 A B _48808 t s n)). Qed.
Lemma lem4310686 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4310687 {A B : Type'} (_48808 : type621 A B) (t : type1413 A B) (s : A -> Prop) (n : nat) : (term1783 A B _48808 t s n) = (term1784 A B _48808 t s n).
Proof. exact (MK_COMB (@lem4310686) (@lem4310685 A B _48808 t s n)). Qed.
Lemma lem4310688 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : A) (n : nat) : (term1779 A B s t n x) = (term1760 A B s t x n).
Proof. exact (eq_refl (term1779 A B s t n x)). Qed.
Lemma lem4310689 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4310690 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : A) (n : nat) : (term1785 A B s t n x) = (term1786 A B s t x n).
Proof. exact (MK_COMB (@lem4310689) (@lem4310688 A B s t x n)). Qed.
Lemma lem4310691 {A B : Type'} (_48808 : type621 A B) (t : type1413 A B) (s : A -> Prop) (n : nat) : (term1345 A B _48808 t s n) = (term1345 A B _48808 t s n).
Proof. exact (eq_refl (term1345 A B _48808 t s n)). Qed.
Lemma lem4310692 {A B : Type'} (x : A) (_48808 : type621 A B) (t : type1413 A B) (s : A -> Prop) (n : nat) : (term1787 A B x _48808 t s n) = (term1788 A B x _48808 t s n).
Proof. exact (MK_COMB (@lem4310690 A B s t x n) (@lem4310691 A B _48808 t s n)). Qed.
Lemma lem4310693 {A B : Type'} (_48808 : type621 A B) (t : type1413 A B) (s : A -> Prop) (n : nat) : (term1789 A B _48808 t s n) = (term1790 A B _48808 t s n).
Proof. exact (fun_ext (fun x : A => @lem4310692 A B x _48808 t s n)). Qed.
Lemma lem4310694 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4310695 {A B : Type'} (_48808 : type621 A B) (t : type1413 A B) (s : A -> Prop) (n : nat) : (term1778 A B _48808 t s n) = (term1791 A B _48808 t s n).
Proof. exact (MK_COMB (@lem4310694 A) (@lem4310693 A B _48808 t s n)). Qed.
Lemma lem4310696 {A B : Type'} (_48808 : type621 A B) (t : type1413 A B) (s : A -> Prop) (n : nat) : ((term1777 A B _48808 t s n) = (term1778 A B _48808 t s n)) = ((term1772 A B _48808 t s n) = (term1791 A B _48808 t s n)).
Proof. exact (MK_COMB (@lem4310687 A B _48808 t s n) (@lem4310695 A B _48808 t s n)). Qed.
Lemma lem4310697 {A B : Type'} (_48808 : type621 A B) (t : type1413 A B) (s : A -> Prop) (n : nat) : (term1772 A B _48808 t s n) = (term1791 A B _48808 t s n).
Proof. exact (EQ_MP (@lem4310696 A B _48808 t s n) (@lem4310677 A B _48808 t s n)). Qed.
Lemma lem4310698 {A B : Type'} (_48808 : type621 A B) (t : type1413 A B) (s : A -> Prop) : (term1773 A B _48808 t s) = (term1792 A B _48808 t s).
Proof. exact (fun_ext (fun n : nat => @lem4310697 A B _48808 t s n)). Qed.
Lemma lem4310699 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4310700 {A B : Type'} (_48808 : type621 A B) (t : type1413 A B) (s : A -> Prop) : (term1774 A B _48808 t s) = (term1793 A B _48808 t s).
Proof. exact (MK_COMB (@lem4310699) (@lem4310698 A B _48808 t s)). Qed.
Lemma lem4310702 {A B : Type'} (P : type1413 A B) : (term1572 A B P) = (term1573 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4310703 {A : Type'} (P : type1597 A) : (term1794 A P) = (term1795 A P).
Proof. exact (@lem4310702 nat A P). Qed.
Lemma lem4310704 {A B : Type'} (_48808 : type621 A B) (t : type1413 A B) (s : A -> Prop) : (term1796 A B _48808 t s) = (term1797 A B _48808 t s).
Proof. exact (@lem4310703 A (term1798 A B _48808 t s)). Qed.
Lemma lem4310705 {A B : Type'} (_48808 : type621 A B) (t : type1413 A B) (s : A -> Prop) (n : nat) : (term1799 A B _48808 t s n) = (term1790 A B _48808 t s n).
Proof. exact (eq_refl (term1799 A B _48808 t s n)). Qed.
Lemma lem4310706 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4310707 {A B : Type'} (_48808 : type621 A B) (t : type1413 A B) (s : A -> Prop) (n : nat) (x : A) : (term1800 A B _48808 t s n x) = (term1801 A B _48808 t s n x).
Proof. exact (MK_COMB (@lem4310705 A B _48808 t s n) (@lem4310706 A x)). Qed.
Lemma lem4310708 {A B : Type'} (x : A) (_48808 : type621 A B) (t : type1413 A B) (s : A -> Prop) (n : nat) : (term1801 A B _48808 t s n x) = (term1788 A B x _48808 t s n).
Proof. exact (eq_refl (term1801 A B _48808 t s n x)). Qed.
Lemma lem4310709 {A B : Type'} (x : A) (_48808 : type621 A B) (t : type1413 A B) (s : A -> Prop) (n : nat) : (term1800 A B _48808 t s n x) = (term1788 A B x _48808 t s n).
Proof. exact (TRANS (@lem4310707 A B _48808 t s n x) (@lem4310708 A B x _48808 t s n)). Qed.
Lemma lem4310710 {A B : Type'} (_48808 : type621 A B) (t : type1413 A B) (s : A -> Prop) (n : nat) : (term1802 A B _48808 t s n) = (term1790 A B _48808 t s n).
Proof. exact (fun_ext (fun x : A => @lem4310709 A B x _48808 t s n)). Qed.
Lemma lem4310711 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4310712 {A B : Type'} (_48808 : type621 A B) (t : type1413 A B) (s : A -> Prop) (n : nat) : (term1803 A B _48808 t s n) = (term1791 A B _48808 t s n).
Proof. exact (MK_COMB (@lem4310711 A) (@lem4310710 A B _48808 t s n)). Qed.
Lemma lem4310713 {A B : Type'} (_48808 : type621 A B) (t : type1413 A B) (s : A -> Prop) : (term1804 A B _48808 t s) = (term1792 A B _48808 t s).
Proof. exact (fun_ext (fun n : nat => @lem4310712 A B _48808 t s n)). Qed.
Lemma lem4310714 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4310715 {A B : Type'} (_48808 : type621 A B) (t : type1413 A B) (s : A -> Prop) : (term1796 A B _48808 t s) = (term1793 A B _48808 t s).
Proof. exact (MK_COMB (@lem4310714) (@lem4310713 A B _48808 t s)). Qed.
Lemma lem4310716 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4310717 {A B : Type'} (_48808 : type621 A B) (t : type1413 A B) (s : A -> Prop) : (term1805 A B _48808 t s) = (term1806 A B _48808 t s).
Proof. exact (MK_COMB (@lem4310716) (@lem4310715 A B _48808 t s)). Qed.
Lemma lem4310718 {A B : Type'} (_48808 : type621 A B) (t : type1413 A B) (s : A -> Prop) (n : nat) : (term1799 A B _48808 t s n) = (term1790 A B _48808 t s n).
Proof. exact (eq_refl (term1799 A B _48808 t s n)). Qed.
Lemma lem4310719 {A : Type'} (x : nat -> A) (n : nat) : (x n) = (x n).
Proof. exact (eq_refl (x n)). Qed.
Lemma lem4310720 {A B : Type'} (_48808 : type621 A B) (t : type1413 A B) (s : A -> Prop) (x : nat -> A) (n : nat) : (term1807 A B _48808 t s x n) = (term1808 A B _48808 t s x n).
Proof. exact (MK_COMB (@lem4310718 A B _48808 t s n) (@lem4310719 A x n)). Qed.
Lemma lem4310721 {A B : Type'} (x : nat -> A) (_48808 : type621 A B) (t : type1413 A B) (s : A -> Prop) (n : nat) : (term1808 A B _48808 t s x n) = (term1809 A B x _48808 t s n).
Proof. exact (eq_refl (term1808 A B _48808 t s x n)). Qed.
Lemma lem4310722 {A B : Type'} (x : nat -> A) (_48808 : type621 A B) (t : type1413 A B) (s : A -> Prop) (n : nat) : (term1807 A B _48808 t s x n) = (term1809 A B x _48808 t s n).
Proof. exact (TRANS (@lem4310720 A B _48808 t s x n) (@lem4310721 A B x _48808 t s n)). Qed.
Lemma lem4310723 {A B : Type'} (x : nat -> A) (_48808 : type621 A B) (t : type1413 A B) (s : A -> Prop) : (term1810 A B _48808 t s x) = (term1811 A B x _48808 t s).
Proof. exact (fun_ext (fun n : nat => @lem4310722 A B x _48808 t s n)). Qed.
Lemma lem4310724 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4310725 {A B : Type'} (x : nat -> A) (_48808 : type621 A B) (t : type1413 A B) (s : A -> Prop) : (term1812 A B _48808 t s x) = (term1813 A B x _48808 t s).
Proof. exact (MK_COMB (@lem4310724) (@lem4310723 A B x _48808 t s)). Qed.
Lemma lem4310726 {A B : Type'} (_48808 : type621 A B) (t : type1413 A B) (s : A -> Prop) : (term1814 A B _48808 t s) = (term1815 A B _48808 t s).
Proof. exact (fun_ext (fun x : nat -> A => @lem4310725 A B x _48808 t s)). Qed.
Lemma lem4310727 {A : Type'} : (@ex (nat -> A)) = (@ex (nat -> A)).
Proof. exact (eq_refl (@ex (nat -> A))). Qed.
Lemma lem4310728 {A B : Type'} (_48808 : type621 A B) (t : type1413 A B) (s : A -> Prop) : (term1797 A B _48808 t s) = (term1816 A B _48808 t s).
Proof. exact (MK_COMB (@lem4310727 A) (@lem4310726 A B _48808 t s)). Qed.
Lemma lem4310729 {A B : Type'} (_48808 : type621 A B) (t : type1413 A B) (s : A -> Prop) : ((term1796 A B _48808 t s) = (term1797 A B _48808 t s)) = ((term1793 A B _48808 t s) = (term1816 A B _48808 t s)).
Proof. exact (MK_COMB (@lem4310717 A B _48808 t s) (@lem4310728 A B _48808 t s)). Qed.
Lemma lem4310730 {A B : Type'} (_48808 : type621 A B) (t : type1413 A B) (s : A -> Prop) : (term1793 A B _48808 t s) = (term1816 A B _48808 t s).
Proof. exact (EQ_MP (@lem4310729 A B _48808 t s) (@lem4310704 A B _48808 t s)). Qed.
Lemma lem4310731 {A B : Type'} (_48808 : type621 A B) (t : type1413 A B) (s : A -> Prop) : (term1774 A B _48808 t s) = (term1816 A B _48808 t s).
Proof. exact (TRANS (@lem4310700 A B _48808 t s) (@lem4310730 A B _48808 t s)). Qed.
Lemma lem4310732 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1775 A B _48808 s) = (term1817 A B _48808 s).
Proof. exact (fun_ext (fun t : type1413 A B => @lem4310731 A B _48808 t s)). Qed.
Lemma lem4310733 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem4310734 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1776 A B _48808 s) = (term1818 A B _48808 s).
Proof. exact (MK_COMB (@lem4310733 A B) (@lem4310732 A B _48808 s)). Qed.
Lemma lem4310736 {A B : Type'} (P : type1413 A B) : (term1572 A B P) = (term1573 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4310737 {A B : Type'} (P : type461 A B) : (term1819 A B P) = (term1820 A B P).
Proof. exact (@lem4310736 (type1413 A B) (nat -> A) P). Qed.
Lemma lem4310738 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1821 A B _48808 s) = (term1822 A B _48808 s).
Proof. exact (@lem4310737 A B (term1823 A B _48808 s)). Qed.
Lemma lem4310739 {A B : Type'} (_48808 : type621 A B) (t : type1413 A B) (s : A -> Prop) : (term1824 A B _48808 s t) = (term1815 A B _48808 t s).
Proof. exact (eq_refl (term1824 A B _48808 s t)). Qed.
Lemma lem4310740 {A : Type'} (x : nat -> A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4310741 {A B : Type'} (_48808 : type621 A B) (t : type1413 A B) (s : A -> Prop) (x : nat -> A) : (term1825 A B _48808 s t x) = (term1826 A B _48808 t s x).
Proof. exact (MK_COMB (@lem4310739 A B _48808 t s) (@lem4310740 A x)). Qed.
Lemma lem4310742 {A B : Type'} (x : nat -> A) (_48808 : type621 A B) (t : type1413 A B) (s : A -> Prop) : (term1826 A B _48808 t s x) = (term1813 A B x _48808 t s).
Proof. exact (eq_refl (term1826 A B _48808 t s x)). Qed.
Lemma lem4310743 {A B : Type'} (x : nat -> A) (_48808 : type621 A B) (t : type1413 A B) (s : A -> Prop) : (term1825 A B _48808 s t x) = (term1813 A B x _48808 t s).
Proof. exact (TRANS (@lem4310741 A B _48808 t s x) (@lem4310742 A B x _48808 t s)). Qed.
Lemma lem4310744 {A B : Type'} (_48808 : type621 A B) (t : type1413 A B) (s : A -> Prop) : (term1827 A B _48808 s t) = (term1815 A B _48808 t s).
Proof. exact (fun_ext (fun x : nat -> A => @lem4310743 A B x _48808 t s)). Qed.
Lemma lem4310745 {A : Type'} : (@ex (nat -> A)) = (@ex (nat -> A)).
Proof. exact (eq_refl (@ex (nat -> A))). Qed.
Lemma lem4310746 {A B : Type'} (_48808 : type621 A B) (t : type1413 A B) (s : A -> Prop) : (term1828 A B _48808 s t) = (term1816 A B _48808 t s).
Proof. exact (MK_COMB (@lem4310745 A) (@lem4310744 A B _48808 t s)). Qed.
Lemma lem4310747 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1829 A B _48808 s) = (term1817 A B _48808 s).
Proof. exact (fun_ext (fun t : type1413 A B => @lem4310746 A B _48808 t s)). Qed.
Lemma lem4310748 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem4310749 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1821 A B _48808 s) = (term1818 A B _48808 s).
Proof. exact (MK_COMB (@lem4310748 A B) (@lem4310747 A B _48808 s)). Qed.
Lemma lem4310750 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4310751 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1830 A B _48808 s) = (term1831 A B _48808 s).
Proof. exact (MK_COMB (@lem4310750) (@lem4310749 A B _48808 s)). Qed.
Lemma lem4310752 {A B : Type'} (_48808 : type621 A B) (t : type1413 A B) (s : A -> Prop) : (term1824 A B _48808 s t) = (term1815 A B _48808 t s).
Proof. exact (eq_refl (term1824 A B _48808 s t)). Qed.
Lemma lem4310753 {A B : Type'} (x : type471 A B) (t : type1413 A B) : (x t) = (x t).
Proof. exact (eq_refl (x t)). Qed.
Lemma lem4310754 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (x : type471 A B) (t : type1413 A B) : (term1832 A B _48808 s x t) = (term1833 A B _48808 s x t).
Proof. exact (MK_COMB (@lem4310752 A B _48808 t s) (@lem4310753 A B x t)). Qed.
Lemma lem4310755 {A B : Type'} (x : type471 A B) (_48808 : type621 A B) (t : type1413 A B) (s : A -> Prop) : (term1833 A B _48808 s x t) = (term1834 A B x _48808 t s).
Proof. exact (eq_refl (term1833 A B _48808 s x t)). Qed.
Lemma lem4310756 {A B : Type'} (x : type471 A B) (_48808 : type621 A B) (t : type1413 A B) (s : A -> Prop) : (term1832 A B _48808 s x t) = (term1834 A B x _48808 t s).
Proof. exact (TRANS (@lem4310754 A B _48808 s x t) (@lem4310755 A B x _48808 t s)). Qed.
Lemma lem4310757 {A B : Type'} (x : type471 A B) (_48808 : type621 A B) (s : A -> Prop) : (term1835 A B _48808 s x) = (term1836 A B x _48808 s).
Proof. exact (fun_ext (fun t : type1413 A B => @lem4310756 A B x _48808 t s)). Qed.
Lemma lem4310758 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem4310759 {A B : Type'} (x : type471 A B) (_48808 : type621 A B) (s : A -> Prop) : (term1837 A B _48808 s x) = (term1838 A B x _48808 s).
Proof. exact (MK_COMB (@lem4310758 A B) (@lem4310757 A B x _48808 s)). Qed.
Lemma lem4310760 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1839 A B _48808 s) = (term1840 A B _48808 s).
Proof. exact (fun_ext (fun x : type471 A B => @lem4310759 A B x _48808 s)). Qed.
Lemma lem4310761 {A B : Type'} : (@ex ((A -> B -> Prop) -> nat -> A)) = (@ex ((A -> B -> Prop) -> nat -> A)).
Proof. exact (eq_refl (@ex ((A -> B -> Prop) -> nat -> A))). Qed.
Lemma lem4310762 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1822 A B _48808 s) = (term1841 A B _48808 s).
Proof. exact (MK_COMB (@lem4310761 A B) (@lem4310760 A B _48808 s)). Qed.
Lemma lem4310763 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : ((term1821 A B _48808 s) = (term1822 A B _48808 s)) = ((term1818 A B _48808 s) = (term1841 A B _48808 s)).
Proof. exact (MK_COMB (@lem4310751 A B _48808 s) (@lem4310762 A B _48808 s)). Qed.
Lemma lem4310764 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1818 A B _48808 s) = (term1841 A B _48808 s).
Proof. exact (EQ_MP (@lem4310763 A B _48808 s) (@lem4310738 A B _48808 s)). Qed.
Lemma lem4310766 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1776 A B _48808 s) = (term1841 A B _48808 s).
Proof. exact (TRANS (@lem4310734 A B _48808 s) (@lem4310764 A B _48808 s)). Qed.
Lemma lem4310767 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) : (term1352 A B _48808 s) = (term1841 A B _48808 s).
Proof. exact (TRANS (@lem4310572 A B _48808 s) (@lem4310766 A B _48808 s)). Qed.
Lemma lem4310768 {A B : Type'} (_48808 : type621 A B) (s : A -> Prop) (h1 : term1352 A B _48808 s) : term1841 A B _48808 s.
Proof. exact (EQ_MP (@lem4310767 A B _48808 s) (@lem4309641 A B _48808 s h1)). Qed.
Lemma lem4310774 {A : Type'} (x'' : A) (s : A -> Prop) (h1 : @IN A x'' s) : @IN A x'' s.
Proof. exact (h1). Qed.
Lemma lem4310786 {A B : Type'} (x' : prod A B) (x'' : A) (y : B) (h1 : x' = (@pair A B x'' y)) : x' = (@pair A B x'' y).
Proof. exact (h1). Qed.
Lemma lem4310792 {A B : Type'} (x' : prod A B) (x : A) (x''' : B) (h1 : x' = (@pair A B x x''')) : x' = (@pair A B x x''').
Proof. exact (h1). Qed.
Lemma lem4310809 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (term1842 A B x a y b) = (term1843 A B x a y b).
Proof. exact (@lem17045 (x = a) (y = b)). Qed.
Lemma lem4310815 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (term1844 A B x a y b) = (term1844 A B x a y b).
Proof. exact (eq_refl (term1844 A B x a y b)). Qed.
Lemma lem4310817 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : (term1845 A B x y a b) = (term1845 A B x y a b).
Proof. exact (eq_refl (term1845 A B x y a b)). Qed.
Lemma lem4310818 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (term1846 A B x a y b) = (term1847 A B x a y b).
Proof. exact (MK_COMB (@lem4310817 A B x y a b) (@lem4310809 A B x a y b)). Qed.
Lemma lem4310819 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4310820 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (term1848 A B x a y b) = (term1849 A B x a y b).
Proof. exact (MK_COMB (@lem4310819) (@lem4310818 A B x a y b)). Qed.
Lemma lem4310821 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (term1850 A B x a y b) = (term1851 A B x a y b).
Proof. exact (MK_COMB (@lem4310820 A B x a y b) (@lem4310815 A B x a y b)). Qed.
Lemma lem4310822 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (((@pair A B x y) = (@pair A B a b)) = (term1085 A B x a y b)) = (term1850 A B x a y b).
Proof. exact (@lem17784 ((@pair A B x y) = (@pair A B a b)) (term1085 A B x a y b)). Qed.
Lemma lem4310823 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (((@pair A B x y) = (@pair A B a b)) = (term1085 A B x a y b)) = (term1851 A B x a y b).
Proof. exact (TRANS (@lem4310822 A B x a y b) (@lem4310821 A B x a y b)). Qed.
Lemma lem4310824 {A B : Type'} (x : A) (a : A) (y : B) : (term1338 A B x a y) = (term1852 A B x a y).
Proof. exact (fun_ext (fun b : B => @lem4310823 A B x a y b)). Qed.
Lemma lem4310825 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4310826 {A B : Type'} (x : A) (a : A) (y : B) : (term1083 A B x a y) = (term1853 A B x a y).
Proof. exact (MK_COMB (@lem4310825 B) (@lem4310824 A B x a y)). Qed.
Lemma lem4310827 {A B : Type'} (x : A) (y : B) : (term1339 A B x y) = (term1854 A B x y).
Proof. exact (fun_ext (fun a : A => @lem4310826 A B x a y)). Qed.
Lemma lem4310828 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4310829 {A B : Type'} (x : A) (y : B) : (term1081 A B x y) = (term1855 A B x y).
Proof. exact (MK_COMB (@lem4310828 A) (@lem4310827 A B x y)). Qed.
Lemma lem4310830 {A B : Type'} (x : A) : (term1340 A B x) = (term1856 A B x).
Proof. exact (fun_ext (fun y : B => @lem4310829 A B x y)). Qed.
Lemma lem4310831 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4310832 {A B : Type'} (x : A) : (term1079 A B x) = (term1857 A B x).
Proof. exact (MK_COMB (@lem4310831 B) (@lem4310830 A B x)). Qed.
Lemma lem4310833 {A B : Type'} : (term1341 A B) = (term1858 A B).
Proof. exact (fun_ext (fun x : A => @lem4310832 A B x)). Qed.
Lemma lem4310834 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4310835 {A B : Type'} : (term1213 A B) = (term1859 A B).
Proof. exact (MK_COMB (@lem4310834 A) (@lem4310833 A B)). Qed.
Lemma lem4310849 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term511 A P Q) = (term512 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4310850 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term511 B P Q) = (term512 B P Q).
Proof. exact (@lem4310849 B P Q). Qed.
Lemma lem4310851 {A B : Type'} (x : A) (a : A) (y : B) : (term1860 A B x a y) = (term1861 A B x a y).
Proof. exact (@lem4310850 B (term1862 A B x a y) (term1863 A B x a y)). Qed.
Lemma lem4310852 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (term1864 A B x a y b) = (term1847 A B x a y b).
Proof. exact (eq_refl (term1864 A B x a y b)). Qed.
Lemma lem4310853 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4310854 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (term1865 A B x a y b) = (term1849 A B x a y b).
Proof. exact (MK_COMB (@lem4310853) (@lem4310852 A B x a y b)). Qed.
Lemma lem4310855 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (term1866 A B x a y b) = (term1844 A B x a y b).
Proof. exact (eq_refl (term1866 A B x a y b)). Qed.
Lemma lem4310856 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (term1867 A B x a y b) = (term1851 A B x a y b).
Proof. exact (MK_COMB (@lem4310854 A B x a y b) (@lem4310855 A B x a y b)). Qed.
Lemma lem4310857 {A B : Type'} (x : A) (a : A) (y : B) : (term1868 A B x a y) = (term1852 A B x a y).
Proof. exact (fun_ext (fun b : B => @lem4310856 A B x a y b)). Qed.
Lemma lem4310858 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4310859 {A B : Type'} (x : A) (a : A) (y : B) : (term1860 A B x a y) = (term1853 A B x a y).
Proof. exact (MK_COMB (@lem4310858 B) (@lem4310857 A B x a y)). Qed.
Lemma lem4310860 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4310861 {A B : Type'} (x : A) (a : A) (y : B) : (term1869 A B x a y) = (term1870 A B x a y).
Proof. exact (MK_COMB (@lem4310860) (@lem4310859 A B x a y)). Qed.
Lemma lem4310862 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (term1864 A B x a y b) = (term1847 A B x a y b).
Proof. exact (eq_refl (term1864 A B x a y b)). Qed.
Lemma lem4310863 {A B : Type'} (x : A) (a : A) (y : B) : (term1871 A B x a y) = (term1862 A B x a y).
Proof. exact (fun_ext (fun b : B => @lem4310862 A B x a y b)). Qed.
Lemma lem4310864 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4310865 {A B : Type'} (x : A) (a : A) (y : B) : (term1872 A B x a y) = (term1873 A B x a y).
Proof. exact (MK_COMB (@lem4310864 B) (@lem4310863 A B x a y)). Qed.
Lemma lem4310866 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4310867 {A B : Type'} (x : A) (a : A) (y : B) : (term1874 A B x a y) = (term1875 A B x a y).
Proof. exact (MK_COMB (@lem4310866) (@lem4310865 A B x a y)). Qed.
Lemma lem4310868 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (term1866 A B x a y b) = (term1844 A B x a y b).
Proof. exact (eq_refl (term1866 A B x a y b)). Qed.
Lemma lem4310869 {A B : Type'} (x : A) (a : A) (y : B) : (term1876 A B x a y) = (term1863 A B x a y).
Proof. exact (fun_ext (fun b : B => @lem4310868 A B x a y b)). Qed.
Lemma lem4310870 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4310871 {A B : Type'} (x : A) (a : A) (y : B) : (term1877 A B x a y) = (term1878 A B x a y).
Proof. exact (MK_COMB (@lem4310870 B) (@lem4310869 A B x a y)). Qed.
Lemma lem4310872 {A B : Type'} (x : A) (a : A) (y : B) : (term1861 A B x a y) = (term1879 A B x a y).
Proof. exact (MK_COMB (@lem4310867 A B x a y) (@lem4310871 A B x a y)). Qed.
Lemma lem4310873 {A B : Type'} (x : A) (a : A) (y : B) : ((term1860 A B x a y) = (term1861 A B x a y)) = ((term1853 A B x a y) = (term1879 A B x a y)).
Proof. exact (MK_COMB (@lem4310861 A B x a y) (@lem4310872 A B x a y)). Qed.
Lemma lem4310874 {A B : Type'} (x : A) (a : A) (y : B) : (term1853 A B x a y) = (term1879 A B x a y).
Proof. exact (EQ_MP (@lem4310873 A B x a y) (@lem4310851 A B x a y)). Qed.
Lemma lem4310971 {A B : Type'} (x : A) (y : B) : (term1854 A B x y) = (term1880 A B x y).
Proof. exact (fun_ext (fun a : A => @lem4310874 A B x a y)). Qed.
Lemma lem4310972 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4310973 {A B : Type'} (x : A) (y : B) : (term1855 A B x y) = (term1881 A B x y).
Proof. exact (MK_COMB (@lem4310972 A) (@lem4310971 A B x y)). Qed.
Lemma lem4310975 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term511 A P Q) = (term512 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4310976 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term511 A P Q) = (term512 A P Q).
Proof. exact (@lem4310975 A P Q). Qed.
Lemma lem4310977 {A B : Type'} (x : A) (y : B) : (term1882 A B x y) = (term1883 A B x y).
Proof. exact (@lem4310976 A (term1884 A B x y) (term1885 A B x y)). Qed.
Lemma lem4310978 {A B : Type'} (x : A) (a : A) (y : B) : (term1886 A B x y a) = (term1873 A B x a y).
Proof. exact (eq_refl (term1886 A B x y a)). Qed.
Lemma lem4310979 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4310980 {A B : Type'} (x : A) (a : A) (y : B) : (term1887 A B x y a) = (term1875 A B x a y).
Proof. exact (MK_COMB (@lem4310979) (@lem4310978 A B x a y)). Qed.
Lemma lem4310981 {A B : Type'} (x : A) (a : A) (y : B) : (term1888 A B x y a) = (term1878 A B x a y).
Proof. exact (eq_refl (term1888 A B x y a)). Qed.
Lemma lem4310982 {A B : Type'} (x : A) (a : A) (y : B) : (term1889 A B x y a) = (term1879 A B x a y).
Proof. exact (MK_COMB (@lem4310980 A B x a y) (@lem4310981 A B x a y)). Qed.
Lemma lem4310983 {A B : Type'} (x : A) (y : B) : (term1890 A B x y) = (term1880 A B x y).
Proof. exact (fun_ext (fun a : A => @lem4310982 A B x a y)). Qed.
Lemma lem4310984 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4310985 {A B : Type'} (x : A) (y : B) : (term1882 A B x y) = (term1881 A B x y).
Proof. exact (MK_COMB (@lem4310984 A) (@lem4310983 A B x y)). Qed.
Lemma lem4310986 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4310987 {A B : Type'} (x : A) (y : B) : (term1891 A B x y) = (term1892 A B x y).
Proof. exact (MK_COMB (@lem4310986) (@lem4310985 A B x y)). Qed.
Lemma lem4310988 {A B : Type'} (x : A) (a : A) (y : B) : (term1886 A B x y a) = (term1873 A B x a y).
Proof. exact (eq_refl (term1886 A B x y a)). Qed.
Lemma lem4310989 {A B : Type'} (x : A) (y : B) : (term1893 A B x y) = (term1884 A B x y).
Proof. exact (fun_ext (fun a : A => @lem4310988 A B x a y)). Qed.
Lemma lem4310990 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4310991 {A B : Type'} (x : A) (y : B) : (term1894 A B x y) = (term1895 A B x y).
Proof. exact (MK_COMB (@lem4310990 A) (@lem4310989 A B x y)). Qed.
Lemma lem4310992 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4310993 {A B : Type'} (x : A) (y : B) : (term1896 A B x y) = (term1897 A B x y).
Proof. exact (MK_COMB (@lem4310992) (@lem4310991 A B x y)). Qed.
Lemma lem4310994 {A B : Type'} (x : A) (a : A) (y : B) : (term1888 A B x y a) = (term1878 A B x a y).
Proof. exact (eq_refl (term1888 A B x y a)). Qed.
Lemma lem4310995 {A B : Type'} (x : A) (y : B) : (term1898 A B x y) = (term1885 A B x y).
Proof. exact (fun_ext (fun a : A => @lem4310994 A B x a y)). Qed.
Lemma lem4310996 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4310997 {A B : Type'} (x : A) (y : B) : (term1899 A B x y) = (term1900 A B x y).
Proof. exact (MK_COMB (@lem4310996 A) (@lem4310995 A B x y)). Qed.
Lemma lem4310998 {A B : Type'} (x : A) (y : B) : (term1883 A B x y) = (term1901 A B x y).
Proof. exact (MK_COMB (@lem4310993 A B x y) (@lem4310997 A B x y)). Qed.
Lemma lem4310999 {A B : Type'} (x : A) (y : B) : ((term1882 A B x y) = (term1883 A B x y)) = ((term1881 A B x y) = (term1901 A B x y)).
Proof. exact (MK_COMB (@lem4310987 A B x y) (@lem4310998 A B x y)). Qed.
Lemma lem4311000 {A B : Type'} (x : A) (y : B) : (term1881 A B x y) = (term1901 A B x y).
Proof. exact (EQ_MP (@lem4310999 A B x y) (@lem4310977 A B x y)). Qed.
Lemma lem4311105 {A B : Type'} (x : A) (y : B) : (term1855 A B x y) = (term1901 A B x y).
Proof. exact (TRANS (@lem4310973 A B x y) (@lem4311000 A B x y)). Qed.
Lemma lem4311106 {A B : Type'} (x : A) : (term1856 A B x) = (term1902 A B x).
Proof. exact (fun_ext (fun y : B => @lem4311105 A B x y)). Qed.
Lemma lem4311107 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4311108 {A B : Type'} (x : A) : (term1857 A B x) = (term1903 A B x).
Proof. exact (MK_COMB (@lem4311107 B) (@lem4311106 A B x)). Qed.
Lemma lem4311110 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term511 A P Q) = (term512 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4311111 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term511 B P Q) = (term512 B P Q).
Proof. exact (@lem4311110 B P Q). Qed.
Lemma lem4311112 {A B : Type'} (x : A) : (term1904 A B x) = (term1905 A B x).
Proof. exact (@lem4311111 B (term1906 A B x) (term1907 A B x)). Qed.
Lemma lem4311113 {A B : Type'} (x : A) (y : B) : (term1908 A B x y) = (term1895 A B x y).
Proof. exact (eq_refl (term1908 A B x y)). Qed.
Lemma lem4311114 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4311115 {A B : Type'} (x : A) (y : B) : (term1909 A B x y) = (term1897 A B x y).
Proof. exact (MK_COMB (@lem4311114) (@lem4311113 A B x y)). Qed.
Lemma lem4311116 {A B : Type'} (x : A) (y : B) : (term1910 A B x y) = (term1900 A B x y).
Proof. exact (eq_refl (term1910 A B x y)). Qed.
Lemma lem4311117 {A B : Type'} (x : A) (y : B) : (term1911 A B x y) = (term1901 A B x y).
Proof. exact (MK_COMB (@lem4311115 A B x y) (@lem4311116 A B x y)). Qed.
Lemma lem4311118 {A B : Type'} (x : A) : (term1912 A B x) = (term1902 A B x).
Proof. exact (fun_ext (fun y : B => @lem4311117 A B x y)). Qed.
Lemma lem4311119 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4311120 {A B : Type'} (x : A) : (term1904 A B x) = (term1903 A B x).
Proof. exact (MK_COMB (@lem4311119 B) (@lem4311118 A B x)). Qed.
Lemma lem4311121 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4311122 {A B : Type'} (x : A) : (term1913 A B x) = (term1914 A B x).
Proof. exact (MK_COMB (@lem4311121) (@lem4311120 A B x)). Qed.
Lemma lem4311123 {A B : Type'} (x : A) (y : B) : (term1908 A B x y) = (term1895 A B x y).
Proof. exact (eq_refl (term1908 A B x y)). Qed.
Lemma lem4311124 {A B : Type'} (x : A) : (term1915 A B x) = (term1906 A B x).
Proof. exact (fun_ext (fun y : B => @lem4311123 A B x y)). Qed.
Lemma lem4311125 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4311126 {A B : Type'} (x : A) : (term1916 A B x) = (term1917 A B x).
Proof. exact (MK_COMB (@lem4311125 B) (@lem4311124 A B x)). Qed.
Lemma lem4311127 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4311128 {A B : Type'} (x : A) : (term1918 A B x) = (term1919 A B x).
Proof. exact (MK_COMB (@lem4311127) (@lem4311126 A B x)). Qed.
Lemma lem4311129 {A B : Type'} (x : A) (y : B) : (term1910 A B x y) = (term1900 A B x y).
Proof. exact (eq_refl (term1910 A B x y)). Qed.
Lemma lem4311130 {A B : Type'} (x : A) : (term1920 A B x) = (term1907 A B x).
Proof. exact (fun_ext (fun y : B => @lem4311129 A B x y)). Qed.
Lemma lem4311131 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4311132 {A B : Type'} (x : A) : (term1921 A B x) = (term1922 A B x).
Proof. exact (MK_COMB (@lem4311131 B) (@lem4311130 A B x)). Qed.
Lemma lem4311133 {A B : Type'} (x : A) : (term1905 A B x) = (term1923 A B x).
Proof. exact (MK_COMB (@lem4311128 A B x) (@lem4311132 A B x)). Qed.
Lemma lem4311134 {A B : Type'} (x : A) : ((term1904 A B x) = (term1905 A B x)) = ((term1903 A B x) = (term1923 A B x)).
Proof. exact (MK_COMB (@lem4311122 A B x) (@lem4311133 A B x)). Qed.
Lemma lem4311135 {A B : Type'} (x : A) : (term1903 A B x) = (term1923 A B x).
Proof. exact (EQ_MP (@lem4311134 A B x) (@lem4311112 A B x)). Qed.
Lemma lem4311248 {A B : Type'} (x : A) : (term1857 A B x) = (term1923 A B x).
Proof. exact (TRANS (@lem4311108 A B x) (@lem4311135 A B x)). Qed.
Lemma lem4311249 {A B : Type'} : (term1858 A B) = (term1924 A B).
Proof. exact (fun_ext (fun x : A => @lem4311248 A B x)). Qed.
Lemma lem4311250 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4311251 {A B : Type'} : (term1859 A B) = (term1925 A B).
Proof. exact (MK_COMB (@lem4311250 A) (@lem4311249 A B)). Qed.
Lemma lem4311253 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term511 A P Q) = (term512 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4311254 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term511 A P Q) = (term512 A P Q).
Proof. exact (@lem4311253 A P Q). Qed.
Lemma lem4311255 {A B : Type'} : (term1926 A B) = (term1927 A B).
Proof. exact (@lem4311254 A (term1928 A B) (term1929 A B)). Qed.
Lemma lem4311256 {A B : Type'} (x : A) : (term1930 A B x) = (term1917 A B x).
Proof. exact (eq_refl (term1930 A B x)). Qed.
Lemma lem4311257 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4311258 {A B : Type'} (x : A) : (term1931 A B x) = (term1919 A B x).
Proof. exact (MK_COMB (@lem4311257) (@lem4311256 A B x)). Qed.
Lemma lem4311259 {A B : Type'} (x : A) : (term1932 A B x) = (term1922 A B x).
Proof. exact (eq_refl (term1932 A B x)). Qed.
Lemma lem4311260 {A B : Type'} (x : A) : (term1933 A B x) = (term1923 A B x).
Proof. exact (MK_COMB (@lem4311258 A B x) (@lem4311259 A B x)). Qed.
Lemma lem4311261 {A B : Type'} : (term1934 A B) = (term1924 A B).
Proof. exact (fun_ext (fun x : A => @lem4311260 A B x)). Qed.
Lemma lem4311262 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4311263 {A B : Type'} : (term1926 A B) = (term1925 A B).
Proof. exact (MK_COMB (@lem4311262 A) (@lem4311261 A B)). Qed.
Lemma lem4311264 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4311265 {A B : Type'} : (term1935 A B) = (term1936 A B).
Proof. exact (MK_COMB (@lem4311264) (@lem4311263 A B)). Qed.
Lemma lem4311266 {A B : Type'} (x : A) : (term1930 A B x) = (term1917 A B x).
Proof. exact (eq_refl (term1930 A B x)). Qed.
Lemma lem4311267 {A B : Type'} : (term1937 A B) = (term1928 A B).
Proof. exact (fun_ext (fun x : A => @lem4311266 A B x)). Qed.
Lemma lem4311268 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4311269 {A B : Type'} : (term1938 A B) = (term1939 A B).
Proof. exact (MK_COMB (@lem4311268 A) (@lem4311267 A B)). Qed.
Lemma lem4311270 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4311271 {A B : Type'} : (term1940 A B) = (term1941 A B).
Proof. exact (MK_COMB (@lem4311270) (@lem4311269 A B)). Qed.
Lemma lem4311272 {A B : Type'} (x : A) : (term1932 A B x) = (term1922 A B x).
Proof. exact (eq_refl (term1932 A B x)). Qed.
Lemma lem4311273 {A B : Type'} : (term1942 A B) = (term1929 A B).
Proof. exact (fun_ext (fun x : A => @lem4311272 A B x)). Qed.
Lemma lem4311274 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4311275 {A B : Type'} : (term1943 A B) = (term1944 A B).
Proof. exact (MK_COMB (@lem4311274 A) (@lem4311273 A B)). Qed.
Lemma lem4311276 {A B : Type'} : (term1927 A B) = (term1945 A B).
Proof. exact (MK_COMB (@lem4311271 A B) (@lem4311275 A B)). Qed.
Lemma lem4311277 {A B : Type'} : ((term1926 A B) = (term1927 A B)) = ((term1925 A B) = (term1945 A B)).
Proof. exact (MK_COMB (@lem4311265 A B) (@lem4311276 A B)). Qed.
Lemma lem4311278 {A B : Type'} : (term1925 A B) = (term1945 A B).
Proof. exact (EQ_MP (@lem4311277 A B) (@lem4311255 A B)). Qed.
Lemma lem4311401 {A B : Type'} : (term1859 A B) = (term1945 A B).
Proof. exact (TRANS (@lem4311251 A B) (@lem4311278 A B)). Qed.
Lemma lem4311402 {A B : Type'} : (term1213 A B) = (term1945 A B).
Proof. exact (TRANS (@lem4310835 A B) (@lem4311401 A B)). Qed.
Lemma lem4311403 {A B : Type'} (h1 : term1213 A B) : term1945 A B.
Proof. exact (EQ_MP (@lem4311402 A B) (@lem4309647 A B h1)). Qed.
Lemma lem4313825 {A B : Type'} (_48808 : type621 A B) (x''''' : type619 A B) (h1 : term1756 A B _48808 x''''') : term1756 A B _48808 x'''''.
Proof. exact (h1). Qed.
Lemma lem4313827 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4313834 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4313835 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4313834 A (type686 A) f x). Qed.
Lemma lem4313836 {A : Type'} (x : A) : (@IN A x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem4313835 A (@IN A) x). Qed.
Lemma lem4313837 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4313838 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x s).
Proof. exact (MK_COMB (@lem4313836 A x) (@lem4313837 A s)). Qed.
Lemma lem4313840 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4313841 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4313840 (A -> Prop) Prop f x). Qed.
Lemma lem4313842 {A : Type'} (x : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x s) = (term1946 A x s).
Proof. exact (@lem4313841 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) s). Qed.
Lemma lem4313844 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (term1946 A x s).
Proof. exact (TRANS (@lem4313838 A x s) (@lem4313842 A x s)). Qed.
Lemma lem4313845 {A : Type'} (x : A) (s : A -> Prop) : (term808 A x s) = (term1947 A x s).
Proof. exact (MK_COMB (@lem4313827) (@lem4313844 A x s)). Qed.
Lemma lem4313957 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4313958 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4313957 A (type686 A) f x). Qed.
Lemma lem4313959 {A : Type'} (x'' : A) : (@IN A x'') = (@I (A -> (A -> Prop) -> Prop) (@IN A) x'').
Proof. exact (@lem4313958 A (@IN A) x''). Qed.
Lemma lem4313960 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4313961 {A : Type'} (x'' : A) (s : A -> Prop) : (@IN A x'' s) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x'' s).
Proof. exact (MK_COMB (@lem4313959 A x'') (@lem4313960 A s)). Qed.
Lemma lem4313963 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4313964 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4313963 (A -> Prop) Prop f x). Qed.
Lemma lem4313965 {A : Type'} (x'' : A) (s : A -> Prop) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x'' s) = (term1946 A x'' s).
Proof. exact (@lem4313964 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x'') s). Qed.
Lemma lem4313967 {A : Type'} (x'' : A) (s : A -> Prop) : (@IN A x'' s) = (term1946 A x'' s).
Proof. exact (TRANS (@lem4313961 A x'' s) (@lem4313965 A x'' s)). Qed.
Lemma lem4314002 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4314003 {A B : Type'} (f : type1409 A B) (x : A) : (f x) = (@I (A -> B -> prod A B) f x).
Proof. exact (@lem4314002 A (type1478 A B) f x). Qed.
Lemma lem4314004 {A B : Type'} (x'' : A) : (@pair A B x'') = (@I (A -> B -> prod A B) (@pair A B) x'').
Proof. exact (@lem4314003 A B (@pair A B) x''). Qed.
Lemma lem4314005 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4314006 {A B : Type'} (x'' : A) (y : B) : (@pair A B x'' y) = (@I (A -> B -> prod A B) (@pair A B) x'' y).
Proof. exact (MK_COMB (@lem4314004 A B x'') (@lem4314005 B y)). Qed.
Lemma lem4314008 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4314009 {A B : Type'} (f : type1478 A B) (x : B) : (f x) = (@I (B -> prod A B) f x).
Proof. exact (@lem4314008 B (prod A B) f x). Qed.
Lemma lem4314010 {A B : Type'} (x'' : A) (y : B) : (@I (A -> B -> prod A B) (@pair A B) x'' y) = (term1948 A B x'' y).
Proof. exact (@lem4314009 A B (@I (A -> B -> prod A B) (@pair A B) x'') y). Qed.
Lemma lem4314012 {A B : Type'} (x'' : A) (y : B) : (@pair A B x'' y) = (term1948 A B x'' y).
Proof. exact (TRANS (@lem4314006 A B x'' y) (@lem4314010 A B x'' y)). Qed.
Lemma lem4314013 {A B : Type'} (x' : prod A B) : (@eq (prod A B) x') = (@eq (prod A B) x').
Proof. exact (eq_refl (@eq (prod A B) x')). Qed.
Lemma lem4314014 {A B : Type'} (x' : prod A B) (x'' : A) (y : B) : (x' = (@pair A B x'' y)) = (x' = (term1948 A B x'' y)).
Proof. exact (MK_COMB (@lem4314013 A B x') (@lem4314012 A B x'' y)). Qed.
Lemma lem4314024 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4314025 {A B : Type'} (f : type1409 A B) (x : A) : (f x) = (@I (A -> B -> prod A B) f x).
Proof. exact (@lem4314024 A (type1478 A B) f x). Qed.
Lemma lem4314026 {A B : Type'} (x : A) : (@pair A B x) = (@I (A -> B -> prod A B) (@pair A B) x).
Proof. exact (@lem4314025 A B (@pair A B) x). Qed.
Lemma lem4314027 {B : Type'} (x''' : B) : x''' = x'''.
Proof. exact (eq_refl x'''). Qed.
Lemma lem4314028 {A B : Type'} (x : A) (x''' : B) : (@pair A B x x''') = (@I (A -> B -> prod A B) (@pair A B) x x''').
Proof. exact (MK_COMB (@lem4314026 A B x) (@lem4314027 B x''')). Qed.
Lemma lem4314030 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4314031 {A B : Type'} (f : type1478 A B) (x : B) : (f x) = (@I (B -> prod A B) f x).
Proof. exact (@lem4314030 B (prod A B) f x). Qed.
Lemma lem4314032 {A B : Type'} (x : A) (x''' : B) : (@I (A -> B -> prod A B) (@pair A B) x x''') = (term1948 A B x x''').
Proof. exact (@lem4314031 A B (@I (A -> B -> prod A B) (@pair A B) x) x'''). Qed.
Lemma lem4314034 {A B : Type'} (x : A) (x''' : B) : (@pair A B x x''') = (term1948 A B x x''').
Proof. exact (TRANS (@lem4314028 A B x x''') (@lem4314032 A B x x''')). Qed.
Lemma lem4314035 {A B : Type'} (x' : prod A B) : (@eq (prod A B) x') = (@eq (prod A B) x').
Proof. exact (eq_refl (@eq (prod A B) x')). Qed.
Lemma lem4314036 {A B : Type'} (x' : prod A B) (x : A) (x''' : B) : (x' = (@pair A B x x''')) = (x' = (term1948 A B x x''')).
Proof. exact (MK_COMB (@lem4314035 A B x') (@lem4314034 A B x x''')). Qed.
Lemma lem4314075 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (term1085 A B x a y b) = (term1085 A B x a y b).
Proof. exact (eq_refl (term1085 A B x a y b)). Qed.
Lemma lem4314076 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4314077 {A B : Type'} : (@eq (prod A B)) = (@eq (prod A B)).
Proof. exact (eq_refl (@eq (prod A B))). Qed.
Lemma lem4314084 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4314085 {A B : Type'} (f : type1409 A B) (x : A) : (f x) = (@I (A -> B -> prod A B) f x).
Proof. exact (@lem4314084 A (type1478 A B) f x). Qed.
Lemma lem4314086 {A B : Type'} (x : A) : (@pair A B x) = (@I (A -> B -> prod A B) (@pair A B) x).
Proof. exact (@lem4314085 A B (@pair A B) x). Qed.
Lemma lem4314087 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4314088 {A B : Type'} (x : A) (y : B) : (@pair A B x y) = (@I (A -> B -> prod A B) (@pair A B) x y).
Proof. exact (MK_COMB (@lem4314086 A B x) (@lem4314087 B y)). Qed.
Lemma lem4314090 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4314091 {A B : Type'} (f : type1478 A B) (x : B) : (f x) = (@I (B -> prod A B) f x).
Proof. exact (@lem4314090 B (prod A B) f x). Qed.
Lemma lem4314092 {A B : Type'} (x : A) (y : B) : (@I (A -> B -> prod A B) (@pair A B) x y) = (term1948 A B x y).
Proof. exact (@lem4314091 A B (@I (A -> B -> prod A B) (@pair A B) x) y). Qed.
Lemma lem4314094 {A B : Type'} (x : A) (y : B) : (@pair A B x y) = (term1948 A B x y).
Proof. exact (TRANS (@lem4314088 A B x y) (@lem4314092 A B x y)). Qed.
Lemma lem4314101 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4314102 {A B : Type'} (f : type1409 A B) (x : A) : (f x) = (@I (A -> B -> prod A B) f x).
Proof. exact (@lem4314101 A (type1478 A B) f x). Qed.
Lemma lem4314103 {A B : Type'} (a : A) : (@pair A B a) = (@I (A -> B -> prod A B) (@pair A B) a).
Proof. exact (@lem4314102 A B (@pair A B) a). Qed.
Lemma lem4314104 {B : Type'} (b : B) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem4314105 {A B : Type'} (a : A) (b : B) : (@pair A B a b) = (@I (A -> B -> prod A B) (@pair A B) a b).
Proof. exact (MK_COMB (@lem4314103 A B a) (@lem4314104 B b)). Qed.
Lemma lem4314107 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4314108 {A B : Type'} (f : type1478 A B) (x : B) : (f x) = (@I (B -> prod A B) f x).
Proof. exact (@lem4314107 B (prod A B) f x). Qed.
Lemma lem4314109 {A B : Type'} (a : A) (b : B) : (@I (A -> B -> prod A B) (@pair A B) a b) = (term1948 A B a b).
Proof. exact (@lem4314108 A B (@I (A -> B -> prod A B) (@pair A B) a) b). Qed.
Lemma lem4314111 {A B : Type'} (a : A) (b : B) : (@pair A B a b) = (term1948 A B a b).
Proof. exact (TRANS (@lem4314105 A B a b) (@lem4314109 A B a b)). Qed.
Lemma lem4314112 {A B : Type'} (x : A) (y : B) : (term1127 A B x y) = (term1949 A B x y).
Proof. exact (MK_COMB (@lem4314077 A B) (@lem4314094 A B x y)). Qed.
Lemma lem4314113 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : ((@pair A B x y) = (@pair A B a b)) = ((term1948 A B x y) = (term1948 A B a b)).
Proof. exact (MK_COMB (@lem4314112 A B x y) (@lem4314111 A B a b)). Qed.
Lemma lem4314114 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : (term1950 A B x y a b) = (term1951 A B x y a b).
Proof. exact (MK_COMB (@lem4314076) (@lem4314113 A B x y a b)). Qed.
Lemma lem4314115 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4314116 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : (term1952 A B x y a b) = (term1953 A B x y a b).
Proof. exact (MK_COMB (@lem4314115) (@lem4314114 A B x y a b)). Qed.
Lemma lem4314117 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (term1844 A B x a y b) = (term1954 A B x a y b).
Proof. exact (MK_COMB (@lem4314116 A B x y a b) (@lem4314075 A B x a y b)). Qed.
Lemma lem4314118 {A B : Type'} (x : A) (a : A) (y : B) : (term1863 A B x a y) = (term1955 A B x a y).
Proof. exact (fun_ext (fun b : B => @lem4314117 A B x a y b)). Qed.
Lemma lem4314119 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4314120 {A B : Type'} (x : A) (a : A) (y : B) : (term1878 A B x a y) = (term1956 A B x a y).
Proof. exact (MK_COMB (@lem4314119 B) (@lem4314118 A B x a y)). Qed.
Lemma lem4314121 {A B : Type'} (x : A) (y : B) : (term1885 A B x y) = (term1957 A B x y).
Proof. exact (fun_ext (fun a : A => @lem4314120 A B x a y)). Qed.
Lemma lem4314122 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4314123 {A B : Type'} (x : A) (y : B) : (term1900 A B x y) = (term1958 A B x y).
Proof. exact (MK_COMB (@lem4314122 A) (@lem4314121 A B x y)). Qed.
Lemma lem4314124 {A B : Type'} (x : A) : (term1907 A B x) = (term1959 A B x).
Proof. exact (fun_ext (fun y : B => @lem4314123 A B x y)). Qed.
Lemma lem4314125 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4314126 {A B : Type'} (x : A) : (term1922 A B x) = (term1960 A B x).
Proof. exact (MK_COMB (@lem4314125 B) (@lem4314124 A B x)). Qed.
Lemma lem4314127 {A B : Type'} : (term1929 A B) = (term1961 A B).
Proof. exact (fun_ext (fun x : A => @lem4314126 A B x)). Qed.
Lemma lem4314128 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4314129 {A B : Type'} : (term1944 A B) = (term1962 A B).
Proof. exact (MK_COMB (@lem4314128 A) (@lem4314127 A B)). Qed.
Lemma lem4314146 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (term1843 A B x a y b) = (term1843 A B x a y b).
Proof. exact (eq_refl (term1843 A B x a y b)). Qed.
Lemma lem4314147 {A B : Type'} : (@eq (prod A B)) = (@eq (prod A B)).
Proof. exact (eq_refl (@eq (prod A B))). Qed.
Lemma lem4314154 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4314155 {A B : Type'} (f : type1409 A B) (x : A) : (f x) = (@I (A -> B -> prod A B) f x).
Proof. exact (@lem4314154 A (type1478 A B) f x). Qed.
Lemma lem4314156 {A B : Type'} (x : A) : (@pair A B x) = (@I (A -> B -> prod A B) (@pair A B) x).
Proof. exact (@lem4314155 A B (@pair A B) x). Qed.
Lemma lem4314157 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4314158 {A B : Type'} (x : A) (y : B) : (@pair A B x y) = (@I (A -> B -> prod A B) (@pair A B) x y).
Proof. exact (MK_COMB (@lem4314156 A B x) (@lem4314157 B y)). Qed.
Lemma lem4314160 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4314161 {A B : Type'} (f : type1478 A B) (x : B) : (f x) = (@I (B -> prod A B) f x).
Proof. exact (@lem4314160 B (prod A B) f x). Qed.
Lemma lem4314162 {A B : Type'} (x : A) (y : B) : (@I (A -> B -> prod A B) (@pair A B) x y) = (term1948 A B x y).
Proof. exact (@lem4314161 A B (@I (A -> B -> prod A B) (@pair A B) x) y). Qed.
Lemma lem4314164 {A B : Type'} (x : A) (y : B) : (@pair A B x y) = (term1948 A B x y).
Proof. exact (TRANS (@lem4314158 A B x y) (@lem4314162 A B x y)). Qed.
Lemma lem4314171 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4314172 {A B : Type'} (f : type1409 A B) (x : A) : (f x) = (@I (A -> B -> prod A B) f x).
Proof. exact (@lem4314171 A (type1478 A B) f x). Qed.
Lemma lem4314173 {A B : Type'} (a : A) : (@pair A B a) = (@I (A -> B -> prod A B) (@pair A B) a).
Proof. exact (@lem4314172 A B (@pair A B) a). Qed.
Lemma lem4314174 {B : Type'} (b : B) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem4314175 {A B : Type'} (a : A) (b : B) : (@pair A B a b) = (@I (A -> B -> prod A B) (@pair A B) a b).
Proof. exact (MK_COMB (@lem4314173 A B a) (@lem4314174 B b)). Qed.
Lemma lem4314177 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4314178 {A B : Type'} (f : type1478 A B) (x : B) : (f x) = (@I (B -> prod A B) f x).
Proof. exact (@lem4314177 B (prod A B) f x). Qed.
Lemma lem4314179 {A B : Type'} (a : A) (b : B) : (@I (A -> B -> prod A B) (@pair A B) a b) = (term1948 A B a b).
Proof. exact (@lem4314178 A B (@I (A -> B -> prod A B) (@pair A B) a) b). Qed.
Lemma lem4314181 {A B : Type'} (a : A) (b : B) : (@pair A B a b) = (term1948 A B a b).
Proof. exact (TRANS (@lem4314175 A B a b) (@lem4314179 A B a b)). Qed.
Lemma lem4314182 {A B : Type'} (x : A) (y : B) : (term1127 A B x y) = (term1949 A B x y).
Proof. exact (MK_COMB (@lem4314147 A B) (@lem4314164 A B x y)). Qed.
Lemma lem4314183 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : ((@pair A B x y) = (@pair A B a b)) = ((term1948 A B x y) = (term1948 A B a b)).
Proof. exact (MK_COMB (@lem4314182 A B x y) (@lem4314181 A B a b)). Qed.
Lemma lem4314184 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4314185 {A B : Type'} (x : A) (y : B) (a : A) (b : B) : (term1845 A B x y a b) = (term1963 A B x y a b).
Proof. exact (MK_COMB (@lem4314184) (@lem4314183 A B x y a b)). Qed.
Lemma lem4314186 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (term1847 A B x a y b) = (term1964 A B x a y b).
Proof. exact (MK_COMB (@lem4314185 A B x y a b) (@lem4314146 A B x a y b)). Qed.
Lemma lem4314187 {A B : Type'} (x : A) (a : A) (y : B) : (term1862 A B x a y) = (term1965 A B x a y).
Proof. exact (fun_ext (fun b : B => @lem4314186 A B x a y b)). Qed.
Lemma lem4314188 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4314189 {A B : Type'} (x : A) (a : A) (y : B) : (term1873 A B x a y) = (term1966 A B x a y).
Proof. exact (MK_COMB (@lem4314188 B) (@lem4314187 A B x a y)). Qed.
Lemma lem4314190 {A B : Type'} (x : A) (y : B) : (term1884 A B x y) = (term1967 A B x y).
Proof. exact (fun_ext (fun a : A => @lem4314189 A B x a y)). Qed.
Lemma lem4314191 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4314192 {A B : Type'} (x : A) (y : B) : (term1895 A B x y) = (term1968 A B x y).
Proof. exact (MK_COMB (@lem4314191 A) (@lem4314190 A B x y)). Qed.
Lemma lem4314193 {A B : Type'} (x : A) : (term1906 A B x) = (term1969 A B x).
Proof. exact (fun_ext (fun y : B => @lem4314192 A B x y)). Qed.
Lemma lem4314194 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4314195 {A B : Type'} (x : A) : (term1917 A B x) = (term1970 A B x).
Proof. exact (MK_COMB (@lem4314194 B) (@lem4314193 A B x)). Qed.
Lemma lem4314196 {A B : Type'} : (term1928 A B) = (term1971 A B).
Proof. exact (fun_ext (fun x : A => @lem4314195 A B x)). Qed.
Lemma lem4314197 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4314198 {A B : Type'} : (term1939 A B) = (term1972 A B).
Proof. exact (MK_COMB (@lem4314197 A) (@lem4314196 A B)). Qed.
Lemma lem4314199 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4314200 {A B : Type'} : (term1941 A B) = (term1973 A B).
Proof. exact (MK_COMB (@lem4314199) (@lem4314198 A B)). Qed.
Lemma lem4314201 {A B : Type'} : (term1945 A B) = (term1974 A B).
Proof. exact (MK_COMB (@lem4314200 A B) (@lem4314129 A B)). Qed.
Lemma lem4314202 {A B : Type'} (h1 : term1213 A B) : term1974 A B.
Proof. exact (EQ_MP (@lem4314201 A B) (@lem4311403 A B h1)). Qed.
Lemma lem4315309 {A B : Type'} (h1 : term1213 A B) : term1962 A B.
Proof. exact (proj2 (@lem4314202 A B h1)). Qed.
Lemma lem4315767 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (term1954 A B x a y b) = (term1975 A B x a y b).
Proof. exact (@lem19490 (x = a) (term1951 A B x y a b) (y = b)). Qed.
Lemma lem4315768 {A B : Type'} (x : A) (a : A) (y : B) : (term1955 A B x a y) = (term1976 A B x a y).
Proof. exact (fun_ext (fun b : B => @lem4315767 A B x a y b)). Qed.
Lemma lem4315769 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4315770 {A B : Type'} (x : A) (a : A) (y : B) : (term1956 A B x a y) = (term1977 A B x a y).
Proof. exact (MK_COMB (@lem4315769 B) (@lem4315768 A B x a y)). Qed.
Lemma lem4315771 {A B : Type'} (x : A) (y : B) : (term1957 A B x y) = (term1978 A B x y).
Proof. exact (fun_ext (fun a : A => @lem4315770 A B x a y)). Qed.
Lemma lem4315772 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4315773 {A B : Type'} (x : A) (y : B) : (term1958 A B x y) = (term1979 A B x y).
Proof. exact (MK_COMB (@lem4315772 A) (@lem4315771 A B x y)). Qed.
Lemma lem4315774 {A B : Type'} (x : A) : (term1959 A B x) = (term1980 A B x).
Proof. exact (fun_ext (fun y : B => @lem4315773 A B x y)). Qed.
Lemma lem4315775 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4315776 {A B : Type'} (x : A) : (term1960 A B x) = (term1981 A B x).
Proof. exact (MK_COMB (@lem4315775 B) (@lem4315774 A B x)). Qed.
Lemma lem4315777 {A B : Type'} : (term1961 A B) = (term1982 A B).
Proof. exact (fun_ext (fun x : A => @lem4315776 A B x)). Qed.
Lemma lem4315778 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4315780 {A B : Type'} : (term1962 A B) = (term1983 A B).
Proof. exact (MK_COMB (@lem4315778 A) (@lem4315777 A B)). Qed.
Lemma lem4315781 {A B : Type'} (h1 : term1213 A B) : term1983 A B.
Proof. exact (EQ_MP (@lem4315780 A B) (@lem4315309 A B h1)). Qed.
Lemma lem4315923 {A B : Type'} (_48856 : A) (h1 : term1213 A B) : term1984 A B _48856.
Proof. exact (@lem4315781 A B h1 _48856). Qed.
Lemma lem4315924 {A B : Type'} (_48856 : A) : (term1984 A B _48856) = (term1981 A B _48856).
Proof. exact (eq_refl (term1984 A B _48856)). Qed.
Lemma lem4315925 {A B : Type'} (_48856 : A) (h1 : term1213 A B) : term1981 A B _48856.
Proof. exact (EQ_MP (@lem4315924 A B _48856) (@lem4315923 A B _48856 h1)). Qed.
Lemma lem4315926 {A B : Type'} (_48856 : A) (_48857 : B) (h1 : term1213 A B) : term1985 A B _48856 _48857.
Proof. exact (@lem4315925 A B _48856 h1 _48857). Qed.
Lemma lem4315927 {A B : Type'} (_48856 : A) (_48857 : B) : (term1985 A B _48856 _48857) = (term1979 A B _48856 _48857).
Proof. exact (eq_refl (term1985 A B _48856 _48857)). Qed.
Lemma lem4315928 {A B : Type'} (_48856 : A) (_48857 : B) (h1 : term1213 A B) : term1979 A B _48856 _48857.
Proof. exact (EQ_MP (@lem4315927 A B _48856 _48857) (@lem4315926 A B _48856 _48857 h1)). Qed.
Lemma lem4315929 {A B : Type'} (_48856 : A) (_48857 : B) (_48858 : A) (h1 : term1213 A B) : term1986 A B _48856 _48857 _48858.
Proof. exact (@lem4315928 A B _48856 _48857 h1 _48858). Qed.
Lemma lem4315930 {A B : Type'} (_48856 : A) (_48858 : A) (_48857 : B) : (term1986 A B _48856 _48857 _48858) = (term1977 A B _48856 _48858 _48857).
Proof. exact (eq_refl (term1986 A B _48856 _48857 _48858)). Qed.
Lemma lem4315931 {A B : Type'} (_48856 : A) (_48858 : A) (_48857 : B) (h1 : term1213 A B) : term1977 A B _48856 _48858 _48857.
Proof. exact (EQ_MP (@lem4315930 A B _48856 _48858 _48857) (@lem4315929 A B _48856 _48857 _48858 h1)). Qed.
Lemma lem4315932 {A B : Type'} (_48856 : A) (_48858 : A) (_48857 : B) (_48859 : B) (h1 : term1213 A B) : term1987 A B _48856 _48858 _48857 _48859.
Proof. exact (@lem4315931 A B _48856 _48858 _48857 h1 _48859). Qed.
Lemma lem4315933 {A B : Type'} (_48856 : A) (_48858 : A) (_48857 : B) (_48859 : B) : (term1987 A B _48856 _48858 _48857 _48859) = (term1975 A B _48856 _48858 _48857 _48859).
Proof. exact (eq_refl (term1987 A B _48856 _48858 _48857 _48859)). Qed.
Lemma lem4315934 {A B : Type'} (_48856 : A) (_48858 : A) (_48857 : B) (_48859 : B) (h1 : term1213 A B) : term1975 A B _48856 _48858 _48857 _48859.
Proof. exact (EQ_MP (@lem4315933 A B _48856 _48858 _48857 _48859) (@lem4315932 A B _48856 _48858 _48857 _48859 h1)). Qed.
Lemma lem4315966 {A B : Type'} (x' : prod A B) (x'' : A) (y : B) (h1 : x' = (@pair A B x'' y)) : x' = (term1948 A B x'' y).
Proof. exact (EQ_MP (@lem4314014 A B x' x'' y) (@lem4310786 A B x' x'' y h1)). Qed.
Lemma lem4315968 {A B : Type'} (x' : prod A B) (x : A) (x''' : B) (h1 : x' = (@pair A B x x''')) : x' = (term1948 A B x x''').
Proof. exact (EQ_MP (@lem4314036 A B x' x x''') (@lem4310792 A B x' x x''' h1)). Qed.
Lemma lem4316217 {A B : Type'} (x'' : A) (y : B) : (term1988 A B x'' y) = (term1988 A B x'' y).
Proof. exact (eq_refl (term1988 A B x'' y)). Qed.
Lemma lem4316218 {A B : Type'} (x'' : A) (y : B) (x' : prod A B) (x : A) (x''' : B) (h1 : x' = (@pair A B x x''')) : (term1989 A B x'' y x') = (term1990 A B x'' y x x''').
Proof. exact (MK_COMB (@lem4316217 A B x'' y) (@lem4315968 A B x' x x''' h1)). Qed.
Lemma lem4316219 {A B : Type'} (x : A) (x''' : B) (x'' : A) (y : B) : (term1990 A B x'' y x x''') = ((term1948 A B x x''') = (term1948 A B x'' y)).
Proof. exact (eq_refl (term1990 A B x'' y x x''')). Qed.
Lemma lem4316220 {A B : Type'} (x'' : A) (y : B) (x' : prod A B) : (term1991 A B x'' y x') = (term1991 A B x'' y x').
Proof. exact (eq_refl (term1991 A B x'' y x')). Qed.
Lemma lem4316221 {A B : Type'} (x' : prod A B) (x : A) (x''' : B) (x'' : A) (y : B) : ((term1989 A B x'' y x') = (term1990 A B x'' y x x''')) = ((term1989 A B x'' y x') = ((term1948 A B x x''') = (term1948 A B x'' y))).
Proof. exact (MK_COMB (@lem4316220 A B x'' y x') (@lem4316219 A B x x''' x'' y)). Qed.
Lemma lem4316222 {A B : Type'} (x' : prod A B) (x'' : A) (y : B) : (term1989 A B x'' y x') = (x' = (term1948 A B x'' y)).
Proof. exact (eq_refl (term1989 A B x'' y x')). Qed.
Lemma lem4316223 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4316224 {A B : Type'} (x' : prod A B) (x'' : A) (y : B) : (term1991 A B x'' y x') = (term1992 A B x' x'' y).
Proof. exact (MK_COMB (@lem4316223) (@lem4316222 A B x' x'' y)). Qed.
Lemma lem4316225 {A B : Type'} (x : A) (x''' : B) (x'' : A) (y : B) : ((term1948 A B x x''') = (term1948 A B x'' y)) = ((term1948 A B x x''') = (term1948 A B x'' y)).
Proof. exact (eq_refl ((term1948 A B x x''') = (term1948 A B x'' y))). Qed.
Lemma lem4316226 {A B : Type'} (x' : prod A B) (x : A) (x''' : B) (x'' : A) (y : B) : ((term1989 A B x'' y x') = ((term1948 A B x x''') = (term1948 A B x'' y))) = ((x' = (term1948 A B x'' y)) = ((term1948 A B x x''') = (term1948 A B x'' y))).
Proof. exact (MK_COMB (@lem4316224 A B x' x'' y) (@lem4316225 A B x x''' x'' y)). Qed.
Lemma lem4316227 {A B : Type'} (x' : prod A B) (x : A) (x''' : B) (x'' : A) (y : B) : ((term1989 A B x'' y x') = (term1990 A B x'' y x x''')) = ((x' = (term1948 A B x'' y)) = ((term1948 A B x x''') = (term1948 A B x'' y))).
Proof. exact (TRANS (@lem4316221 A B x' x x''' x'' y) (@lem4316226 A B x' x x''' x'' y)). Qed.
Lemma lem4316228 {A B : Type'} (x'' : A) (y : B) (x' : prod A B) (x : A) (x''' : B) (h1 : x' = (@pair A B x x''')) : (x' = (term1948 A B x'' y)) = ((term1948 A B x x''') = (term1948 A B x'' y)).
Proof. exact (EQ_MP (@lem4316227 A B x' x x''' x'' y) (@lem4316218 A B x'' y x' x x''' h1)). Qed.
Lemma lem4316537 {A : Type'} (x : A) (s : A -> Prop) (h1 : term808 A x s) : term1947 A x s.
Proof. exact (EQ_MP (@lem4313845 A x s) (@lem4310462 A x s h1)). Qed.
Lemma lem4316747 {A B : Type'} (_48857 : B) (_48859 : B) (_48856 : A) (_48858 : A) (h1 : term1213 A B) : term1993 A B _48857 _48859 _48856 _48858.
Proof. exact (proj1 (@lem4315934 A B _48856 _48858 _48857 _48859 h1)). Qed.
Lemma lem4316959 {A : Type'} : (@I ((A -> Prop) -> Prop)) = (@I ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@I ((A -> Prop) -> Prop))). Qed.
Lemma lem4316960 {A : Type'} (_48986 : type686 A) (_48988 : type686 A) (h1 : _48986 = _48988) : _48986 = _48988.
Proof. exact (h1). Qed.
Lemma lem4316961 {A : Type'} (_48987 : A -> Prop) (_48989 : A -> Prop) (h1 : _48987 = _48989) : _48987 = _48989.
Proof. exact (h1). Qed.
Lemma lem4316962 {A : Type'} (_48986 : type686 A) (_48988 : type686 A) (h1 : _48986 = _48988) : (@I ((A -> Prop) -> Prop) _48986) = (@I ((A -> Prop) -> Prop) _48988).
Proof. exact (MK_COMB (@lem4316959 A) (@lem4316960 A _48986 _48988 h1)). Qed.
Lemma lem4316963 {A : Type'} (_48987 : A -> Prop) (_48989 : A -> Prop) (_48986 : type686 A) (_48988 : type686 A) (h1 : _48987 = _48989) (h2 : _48986 = _48988) : (@I ((A -> Prop) -> Prop) _48986 _48987) = (@I ((A -> Prop) -> Prop) _48988 _48989).
Proof. exact (MK_COMB (@lem4316962 A _48986 _48988 h2) (@lem4316961 A _48987 _48989 h1)). Qed.
Lemma lem4316965 (b : Prop) (a : Prop) : term1994 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem4316966 {A : Type'} (_48988 : type686 A) (_48989 : A -> Prop) (_48986 : type686 A) (_48987 : A -> Prop) : term1995 A _48988 _48989 _48986 _48987.
Proof. exact (@lem4316965 (@I ((A -> Prop) -> Prop) _48988 _48989) (@I ((A -> Prop) -> Prop) _48986 _48987)). Qed.
Lemma lem4316967 {A : Type'} (_48987 : A -> Prop) (_48989 : A -> Prop) (_48986 : type686 A) (_48988 : type686 A) (h1 : _48987 = _48989) (h2 : _48986 = _48988) : term1996 A _48988 _48989 _48986 _48987.
Proof. exact (@lem4316966 A _48988 _48989 _48986 _48987 (@lem4316963 A _48987 _48989 _48986 _48988 h1 h2)). Qed.
Lemma lem4316968 {A : Type'} (_48988 : type686 A) (_48986 : type686 A) (_48987 : A -> Prop) (_48989 : A -> Prop) (h1 : _48987 = _48989) : term1997 A _48988 _48989 _48986 _48987.
Proof. exact (fun h0 : _48986 = _48988 => @lem4316967 A _48987 _48989 _48986 _48988 h1 h0). Qed.
Lemma lem4316970 (a : Prop) (b : Prop) : (a -> b) = (term1998 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem4316971 {A : Type'} (_48988 : type686 A) (_48989 : A -> Prop) (_48986 : type686 A) (_48987 : A -> Prop) : (term1997 A _48988 _48989 _48986 _48987) = (term1999 A _48988 _48989 _48986 _48987).
Proof. exact (@lem4316970 (_48986 = _48988) (term1996 A _48988 _48989 _48986 _48987)). Qed.
Lemma lem4316972 {A : Type'} (_48988 : type686 A) (_48986 : type686 A) (_48987 : A -> Prop) (_48989 : A -> Prop) (h1 : _48987 = _48989) : term1999 A _48988 _48989 _48986 _48987.
Proof. exact (EQ_MP (@lem4316971 A _48988 _48989 _48986 _48987) (@lem4316968 A _48988 _48986 _48987 _48989 h1)). Qed.
Lemma lem4316973 {A : Type'} (_48988 : type686 A) (_48989 : A -> Prop) (_48986 : type686 A) (_48987 : A -> Prop) : term2000 A _48988 _48989 _48986 _48987.
Proof. exact (fun h0 : _48987 = _48989 => @lem4316972 A _48988 _48986 _48987 _48989 h0). Qed.
Lemma lem4316975 (a : Prop) (b : Prop) : (a -> b) = (term1998 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem4316976 {A : Type'} (_48988 : type686 A) (_48989 : A -> Prop) (_48986 : type686 A) (_48987 : A -> Prop) : (term2000 A _48988 _48989 _48986 _48987) = (term2001 A _48988 _48989 _48986 _48987).
Proof. exact (@lem4316975 (_48987 = _48989) (term1999 A _48988 _48989 _48986 _48987)). Qed.
Lemma lem4316977 {A : Type'} (_48988 : type686 A) (_48989 : A -> Prop) (_48986 : type686 A) (_48987 : A -> Prop) : term2001 A _48988 _48989 _48986 _48987.
Proof. exact (EQ_MP (@lem4316976 A _48988 _48989 _48986 _48987) (@lem4316973 A _48988 _48989 _48986 _48987)). Qed.
Lemma lem4317473 {A : Type'} : (@I (A -> (A -> Prop) -> Prop)) = (@I (A -> (A -> Prop) -> Prop)).
Proof. exact (eq_refl (@I (A -> (A -> Prop) -> Prop))). Qed.
Lemma lem4317474 {A : Type'} (_49122 : type1364 A) (_49124 : type1364 A) (h1 : _49122 = _49124) : _49122 = _49124.
Proof. exact (h1). Qed.
Lemma lem4317475 {A : Type'} (_49123 : A) (_49125 : A) (h1 : _49123 = _49125) : _49123 = _49125.
Proof. exact (h1). Qed.
Lemma lem4317476 {A : Type'} (_49122 : type1364 A) (_49124 : type1364 A) (h1 : _49122 = _49124) : (@I (A -> (A -> Prop) -> Prop) _49122) = (@I (A -> (A -> Prop) -> Prop) _49124).
Proof. exact (MK_COMB (@lem4317473 A) (@lem4317474 A _49122 _49124 h1)). Qed.
Lemma lem4317477 {A : Type'} (_49123 : A) (_49125 : A) (_49122 : type1364 A) (_49124 : type1364 A) (h1 : _49123 = _49125) (h2 : _49122 = _49124) : (@I (A -> (A -> Prop) -> Prop) _49122 _49123) = (@I (A -> (A -> Prop) -> Prop) _49124 _49125).
Proof. exact (MK_COMB (@lem4317476 A _49122 _49124 h2) (@lem4317475 A _49123 _49125 h1)). Qed.
Lemma lem4317478 {A : Type'} (_49122 : type1364 A) (_49124 : type1364 A) (_49123 : A) (_49125 : A) (h1 : _49123 = _49125) : term2002 A _49122 _49123 _49124 _49125.
Proof. exact (fun h0 : _49122 = _49124 => @lem4317477 A _49123 _49125 _49122 _49124 h1 h0). Qed.
Lemma lem4317480 (a : Prop) (b : Prop) : (a -> b) = (term1998 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem4317481 {A : Type'} (_49122 : type1364 A) (_49123 : A) (_49124 : type1364 A) (_49125 : A) : (term2002 A _49122 _49123 _49124 _49125) = (term2003 A _49122 _49123 _49124 _49125).
Proof. exact (@lem4317480 (_49122 = _49124) ((@I (A -> (A -> Prop) -> Prop) _49122 _49123) = (@I (A -> (A -> Prop) -> Prop) _49124 _49125))). Qed.
Lemma lem4317482 {A : Type'} (_49122 : type1364 A) (_49124 : type1364 A) (_49123 : A) (_49125 : A) (h1 : _49123 = _49125) : term2003 A _49122 _49123 _49124 _49125.
Proof. exact (EQ_MP (@lem4317481 A _49122 _49123 _49124 _49125) (@lem4317478 A _49122 _49124 _49123 _49125 h1)). Qed.
Lemma lem4317483 {A : Type'} (_49122 : type1364 A) (_49123 : A) (_49124 : type1364 A) (_49125 : A) : term2004 A _49122 _49123 _49124 _49125.
Proof. exact (fun h0 : _49123 = _49125 => @lem4317482 A _49122 _49124 _49123 _49125 h0). Qed.
Lemma lem4317485 (a : Prop) (b : Prop) : (a -> b) = (term1998 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem4317486 {A : Type'} (_49122 : type1364 A) (_49123 : A) (_49124 : type1364 A) (_49125 : A) : (term2004 A _49122 _49123 _49124 _49125) = (term2005 A _49122 _49123 _49124 _49125).
Proof. exact (@lem4317485 (_49123 = _49125) (term2003 A _49122 _49123 _49124 _49125)). Qed.
Lemma lem4317487 {A : Type'} (_49122 : type1364 A) (_49123 : A) (_49124 : type1364 A) (_49125 : A) : term2005 A _49122 _49123 _49124 _49125.
Proof. exact (EQ_MP (@lem4317486 A _49122 _49123 _49124 _49125) (@lem4317483 A _49122 _49123 _49124 _49125)). Qed.
Lemma lem4317489 {A : Type'} (x : type686 A) (y : type686 A) (z : type686 A) : term2006 A x y z.
Proof. exact (@lem21385 (type686 A) x y z). Qed.
Lemma lem4317579 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem21386 (A -> Prop) x). Qed.
Lemma lem4317580 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem4317579 A x). Qed.
Lemma lem4317581 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (@lem4317580 A s). Qed.
Lemma lem4317582 {A : Type'} (s : A -> Prop) : term2007 A s.
Proof. exact (fun h0 : term2008 A s => @lem4317581 A s). Qed.
Lemma lem4317584 (p : Prop) : (term467 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4317585 {A : Type'} (s : A -> Prop) : (term2007 A s) = (s = s).
Proof. exact (@lem4317584 (s = s)). Qed.
Lemma lem4317586 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (EQ_MP (@lem4317585 A s) (@lem4317582 A s)). Qed.
Lemma lem4317588 {A B : Type'} (x : A) (x''' : B) (x' : prod A B) (x'' : A) (y : B) (h1 : x' = (@pair A B x x''')) (h2 : x' = (@pair A B x'' y)) : (term1948 A B x x''') = (term1948 A B x'' y).
Proof. exact (EQ_MP (@lem4316228 A B x'' y x' x x''' h1) (@lem4315966 A B x' x'' y h2)). Qed.
Lemma lem4317589 {A B : Type'} (x : A) (x''' : B) (x' : prod A B) (x'' : A) (y : B) (h1 : x' = (@pair A B x x''')) (h2 : x' = (@pair A B x'' y)) : term2009 A B x x''' x'' y.
Proof. exact (fun h0 : term1951 A B x x''' x'' y => @lem4317588 A B x x''' x' x'' y h1 h2). Qed.
Lemma lem4317591 (p : Prop) : (term467 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4317592 {A B : Type'} (x : A) (x''' : B) (x'' : A) (y : B) : (term2009 A B x x''' x'' y) = ((term1948 A B x x''') = (term1948 A B x'' y)).
Proof. exact (@lem4317591 ((term1948 A B x x''') = (term1948 A B x'' y))). Qed.
Lemma lem4317593 {A B : Type'} (x : A) (x''' : B) (x' : prod A B) (x'' : A) (y : B) (h1 : x' = (@pair A B x x''')) (h2 : x' = (@pair A B x'' y)) : (term1948 A B x x''') = (term1948 A B x'' y).
Proof. exact (EQ_MP (@lem4317592 A B x x''' x'' y) (@lem4317589 A B x x''' x' x'' y h1 h2)). Qed.
Lemma lem4317599 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4317600 {A B : Type'} (_48856 : A) (_48857 : B) (_48858 : A) (_48859 : B) : (term1993 A B _48857 _48859 _48856 _48858) = (term2010 A B _48856 _48857 _48858 _48859).
Proof. exact (@lem4317599 (_48856 = _48858) (term1951 A B _48856 _48857 _48858 _48859)). Qed.
Lemma lem4317610 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4317611 {A B : Type'} (_48856 : A) (_48857 : B) (_48858 : A) (_48859 : B) : (term2011 A B _48857 _48859 _48856 _48858) = (term2012 A B _48856 _48857 _48858 _48859).
Proof. exact (MK_COMB (@lem4317610) (@lem4317600 A B _48856 _48857 _48858 _48859)). Qed.
Lemma lem4317621 {A B : Type'} (_48856 : A) (_48857 : B) (_48858 : A) (_48859 : B) : (term2010 A B _48856 _48857 _48858 _48859) = (term2010 A B _48856 _48857 _48858 _48859).
Proof. exact (eq_refl (term2010 A B _48856 _48857 _48858 _48859)). Qed.
Lemma lem4317622 {A B : Type'} (_48856 : A) (_48857 : B) (_48858 : A) (_48859 : B) : ((term1993 A B _48857 _48859 _48856 _48858) = (term2010 A B _48856 _48857 _48858 _48859)) = ((term2010 A B _48856 _48857 _48858 _48859) = (term2010 A B _48856 _48857 _48858 _48859)).
Proof. exact (MK_COMB (@lem4317611 A B _48856 _48857 _48858 _48859) (@lem4317621 A B _48856 _48857 _48858 _48859)). Qed.
Lemma lem4317624 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4317625 (x : Prop) : (x = x) = True.
Proof. exact (@lem4317624 Prop x). Qed.
Lemma lem4317626 {A B : Type'} (_48856 : A) (_48857 : B) (_48858 : A) (_48859 : B) : ((term2010 A B _48856 _48857 _48858 _48859) = (term2010 A B _48856 _48857 _48858 _48859)) = True.
Proof. exact (@lem4317625 (term2010 A B _48856 _48857 _48858 _48859)). Qed.
Lemma lem4317627 {A B : Type'} (_48856 : A) (_48857 : B) (_48858 : A) (_48859 : B) : ((term1993 A B _48857 _48859 _48856 _48858) = (term2010 A B _48856 _48857 _48858 _48859)) = True.
Proof. exact (TRANS (@lem4317622 A B _48856 _48857 _48858 _48859) (@lem4317626 A B _48856 _48857 _48858 _48859)). Qed.
Lemma lem4317628 {A B : Type'} (_48856 : A) (_48857 : B) (_48858 : A) (_48859 : B) : True = ((term1993 A B _48857 _48859 _48856 _48858) = (term2010 A B _48856 _48857 _48858 _48859)).
Proof. exact (SYM (@lem4317627 A B _48856 _48857 _48858 _48859)). Qed.
Lemma lem4317629 {A B : Type'} (_48856 : A) (_48857 : B) (_48858 : A) (_48859 : B) : (term1993 A B _48857 _48859 _48856 _48858) = (term2010 A B _48856 _48857 _48858 _48859).
Proof. exact (EQ_MP (@lem4317628 A B _48856 _48857 _48858 _48859) (@lem0)). Qed.
Lemma lem4317630 {A B : Type'} (_48856 : A) (_48857 : B) (_48858 : A) (_48859 : B) (h1 : term1213 A B) : term2010 A B _48856 _48857 _48858 _48859.
Proof. exact (EQ_MP (@lem4317629 A B _48856 _48857 _48858 _48859) (@lem4316747 A B _48857 _48859 _48856 _48858 h1)). Qed.
Lemma lem4317632 (b : Prop) (a : Prop) : (a \/ b) = (term2013 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4317633 {A B : Type'} (_48857 : B) (_48859 : B) (_48856 : A) (_48858 : A) : (term2010 A B _48856 _48857 _48858 _48859) = (term2014 A B _48857 _48859 _48856 _48858).
Proof. exact (@lem4317632 (term1951 A B _48856 _48857 _48858 _48859) (_48856 = _48858)). Qed.
Lemma lem4317635 (a : Prop) : (term189 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4317636 {A B : Type'} (_48856 : A) (_48857 : B) (_48858 : A) (_48859 : B) : (term2015 A B _48856 _48857 _48858 _48859) = ((term1948 A B _48856 _48857) = (term1948 A B _48858 _48859)).
Proof. exact (@lem4317635 ((term1948 A B _48856 _48857) = (term1948 A B _48858 _48859))). Qed.
Lemma lem4317637 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4317638 {A B : Type'} (_48856 : A) (_48857 : B) (_48858 : A) (_48859 : B) : (term2016 A B _48856 _48857 _48858 _48859) = (term2017 A B _48856 _48857 _48858 _48859).
Proof. exact (MK_COMB (@lem4317637) (@lem4317636 A B _48856 _48857 _48858 _48859)). Qed.
Lemma lem4317639 {A : Type'} (_48856 : A) (_48858 : A) : (_48856 = _48858) = (_48856 = _48858).
Proof. exact (eq_refl (_48856 = _48858)). Qed.
Lemma lem4317640 {A B : Type'} (_48857 : B) (_48859 : B) (_48856 : A) (_48858 : A) : (term2014 A B _48857 _48859 _48856 _48858) = (term2018 A B _48857 _48859 _48856 _48858).
Proof. exact (MK_COMB (@lem4317638 A B _48856 _48857 _48858 _48859) (@lem4317639 A _48856 _48858)). Qed.
Lemma lem4317641 {A B : Type'} (_48857 : B) (_48859 : B) (_48856 : A) (_48858 : A) : (term2010 A B _48856 _48857 _48858 _48859) = (term2018 A B _48857 _48859 _48856 _48858).
Proof. exact (TRANS (@lem4317633 A B _48857 _48859 _48856 _48858) (@lem4317640 A B _48857 _48859 _48856 _48858)). Qed.
Lemma lem4317644 {A B : Type'} (_48857 : B) (_48859 : B) (_48856 : A) (_48858 : A) (h1 : term1213 A B) : term2018 A B _48857 _48859 _48856 _48858.
Proof. exact (EQ_MP (@lem4317641 A B _48857 _48859 _48856 _48858) (@lem4317630 A B _48856 _48857 _48858 _48859 h1)). Qed.
Lemma lem4317645 {A B : Type'} (_48857 : B) (_48859 : B) (_48856 : A) (_48858 : A) (h1 : term1213 A B) : term2018 A B _48857 _48859 _48856 _48858.
Proof. exact (@lem4317644 A B _48857 _48859 _48856 _48858 h1). Qed.
Lemma lem4317646 {A B : Type'} (x''' : B) (y : B) (x : A) (x'' : A) (h1 : term1213 A B) : term2018 A B x''' y x x''.
Proof. exact (@lem4317645 A B x''' y x x'' h1). Qed.
Lemma lem4317649 {A B : Type'} (x : A) (x''' : B) (x' : prod A B) (x'' : A) (y : B) (h1 : term1213 A B) (h2 : x' = (@pair A B x x''')) (h3 : x' = (@pair A B x'' y)) : x = x''.
Proof. exact (@lem4317646 A B x''' y x x'' h1 (@lem4317593 A B x x''' x' x'' y h2 h3)). Qed.
Lemma lem4317650 {A B : Type'} (x : A) (x''' : B) (x' : prod A B) (x'' : A) (y : B) (h1 : term1213 A B) (h2 : x' = (@pair A B x x''')) (h3 : x' = (@pair A B x'' y)) : term2019 A x x''.
Proof. exact (fun h0 : term421 A x x'' => @lem4317649 A B x x''' x' x'' y h1 h2 h3). Qed.
Lemma lem4317652 (p : Prop) : (term467 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4317653 {A : Type'} (x : A) (x'' : A) : (term2019 A x x'') = (x = x'').
Proof. exact (@lem4317652 (x = x'')). Qed.
Lemma lem4317654 {A B : Type'} (x : A) (x''' : B) (x' : prod A B) (x'' : A) (y : B) (h1 : term1213 A B) (h2 : x' = (@pair A B x x''')) (h3 : x' = (@pair A B x'' y)) : x = x''.
Proof. exact (EQ_MP (@lem4317653 A x x'') (@lem4317650 A B x x''' x' x'' y h1 h2 h3)). Qed.
Lemma lem4317656 {A : Type'} (x : type1364 A) : x = x.
Proof. exact (@lem21386 (type1364 A) x). Qed.
Lemma lem4317657 {A : Type'} (x : type1364 A) : x = x.
Proof. exact (@lem4317656 A x). Qed.
Lemma lem4317658 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (@lem4317657 A (@IN A)). Qed.
Lemma lem4317659 {A : Type'} : term2020 A.
Proof. exact (fun h0 : term2021 A => @lem4317658 A). Qed.
Lemma lem4317661 (p : Prop) : (term467 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4317662 {A : Type'} : (term2020 A) = ((@IN A) = (@IN A)).
Proof. exact (@lem4317661 ((@IN A) = (@IN A))). Qed.
Lemma lem4317663 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (EQ_MP (@lem4317662 A) (@lem4317659 A)). Qed.
Lemma lem4317681 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4317682 {A : Type'} (_49123 : A) (_49125 : A) (_49122 : type1364 A) (_49124 : type1364 A) : (term2003 A _49122 _49123 _49124 _49125) = (term2022 A _49123 _49125 _49122 _49124).
Proof. exact (@lem4317681 ((@I (A -> (A -> Prop) -> Prop) _49122 _49123) = (@I (A -> (A -> Prop) -> Prop) _49124 _49125)) (term2023 A _49122 _49124)). Qed.
Lemma lem4317692 {A : Type'} (_49123 : A) (_49125 : A) : (term491 A _49123 _49125) = (term491 A _49123 _49125).
Proof. exact (eq_refl (term491 A _49123 _49125)). Qed.
Lemma lem4317693 {A : Type'} (_49123 : A) (_49125 : A) (_49122 : type1364 A) (_49124 : type1364 A) : (term2005 A _49122 _49123 _49124 _49125) = (term2024 A _49123 _49125 _49122 _49124).
Proof. exact (MK_COMB (@lem4317692 A _49123 _49125) (@lem4317682 A _49123 _49125 _49122 _49124)). Qed.
Lemma lem4317697 (q : Prop) (p : Prop) (r : Prop) : (term48 p q r) = (term48 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4317698 {A : Type'} (_49123 : A) (_49125 : A) (_49122 : type1364 A) (_49124 : type1364 A) : (term2024 A _49123 _49125 _49122 _49124) = (term2025 A _49123 _49125 _49122 _49124).
Proof. exact (@lem4317697 ((@I (A -> (A -> Prop) -> Prop) _49122 _49123) = (@I (A -> (A -> Prop) -> Prop) _49124 _49125)) (term421 A _49123 _49125) (term2023 A _49122 _49124)). Qed.
Lemma lem4317720 {A : Type'} (_49123 : A) (_49125 : A) (_49122 : type1364 A) (_49124 : type1364 A) : (term2005 A _49122 _49123 _49124 _49125) = (term2025 A _49123 _49125 _49122 _49124).
Proof. exact (TRANS (@lem4317693 A _49123 _49125 _49122 _49124) (@lem4317698 A _49123 _49125 _49122 _49124)). Qed.
Lemma lem4317721 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4317722 {A : Type'} (_49123 : A) (_49125 : A) (_49122 : type1364 A) (_49124 : type1364 A) : (term2026 A _49122 _49123 _49124 _49125) = (term2027 A _49123 _49125 _49122 _49124).
Proof. exact (MK_COMB (@lem4317721) (@lem4317720 A _49123 _49125 _49122 _49124)). Qed.
Lemma lem4317744 {A : Type'} (_49123 : A) (_49125 : A) (_49122 : type1364 A) (_49124 : type1364 A) : (term2025 A _49123 _49125 _49122 _49124) = (term2025 A _49123 _49125 _49122 _49124).
Proof. exact (eq_refl (term2025 A _49123 _49125 _49122 _49124)). Qed.
Lemma lem4317745 {A : Type'} (_49123 : A) (_49125 : A) (_49122 : type1364 A) (_49124 : type1364 A) : ((term2005 A _49122 _49123 _49124 _49125) = (term2025 A _49123 _49125 _49122 _49124)) = ((term2025 A _49123 _49125 _49122 _49124) = (term2025 A _49123 _49125 _49122 _49124)).
Proof. exact (MK_COMB (@lem4317722 A _49123 _49125 _49122 _49124) (@lem4317744 A _49123 _49125 _49122 _49124)). Qed.
Lemma lem4317747 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4317748 (x : Prop) : (x = x) = True.
Proof. exact (@lem4317747 Prop x). Qed.
Lemma lem4317749 {A : Type'} (_49123 : A) (_49125 : A) (_49122 : type1364 A) (_49124 : type1364 A) : ((term2025 A _49123 _49125 _49122 _49124) = (term2025 A _49123 _49125 _49122 _49124)) = True.
Proof. exact (@lem4317748 (term2025 A _49123 _49125 _49122 _49124)). Qed.
Lemma lem4317750 {A : Type'} (_49123 : A) (_49125 : A) (_49122 : type1364 A) (_49124 : type1364 A) : ((term2005 A _49122 _49123 _49124 _49125) = (term2025 A _49123 _49125 _49122 _49124)) = True.
Proof. exact (TRANS (@lem4317745 A _49123 _49125 _49122 _49124) (@lem4317749 A _49123 _49125 _49122 _49124)). Qed.
Lemma lem4317751 {A : Type'} (_49123 : A) (_49125 : A) (_49122 : type1364 A) (_49124 : type1364 A) : True = ((term2005 A _49122 _49123 _49124 _49125) = (term2025 A _49123 _49125 _49122 _49124)).
Proof. exact (SYM (@lem4317750 A _49123 _49125 _49122 _49124)). Qed.
Lemma lem4317752 {A : Type'} (_49123 : A) (_49125 : A) (_49122 : type1364 A) (_49124 : type1364 A) : (term2005 A _49122 _49123 _49124 _49125) = (term2025 A _49123 _49125 _49122 _49124).
Proof. exact (EQ_MP (@lem4317751 A _49123 _49125 _49122 _49124) (@lem0)). Qed.
Lemma lem4317753 {A : Type'} (_49123 : A) (_49125 : A) (_49122 : type1364 A) (_49124 : type1364 A) : term2025 A _49123 _49125 _49122 _49124.
Proof. exact (EQ_MP (@lem4317752 A _49123 _49125 _49122 _49124) (@lem4317487 A _49122 _49123 _49124 _49125)). Qed.
Lemma lem4317755 (b : Prop) (a : Prop) : (a \/ b) = (term2013 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4317756 {A : Type'} (_49122 : type1364 A) (_49123 : A) (_49124 : type1364 A) (_49125 : A) : (term2025 A _49123 _49125 _49122 _49124) = (term2028 A _49122 _49123 _49124 _49125).
Proof. exact (@lem4317755 (term2029 A _49123 _49125 _49122 _49124) ((@I (A -> (A -> Prop) -> Prop) _49122 _49123) = (@I (A -> (A -> Prop) -> Prop) _49124 _49125))). Qed.
Lemma lem4317758 (a : Prop) (b : Prop) : (term2030 a b) = (term2031 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4317759 {A : Type'} (_49123 : A) (_49125 : A) (_49122 : type1364 A) (_49124 : type1364 A) : (term2032 A _49123 _49125 _49122 _49124) = (term2033 A _49123 _49125 _49122 _49124).
Proof. exact (@lem4317758 (term421 A _49123 _49125) (term2023 A _49122 _49124)). Qed.
Lemma lem4317761 (a : Prop) : (term189 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4317762 {A : Type'} (_49123 : A) (_49125 : A) : (term2034 A _49123 _49125) = (_49123 = _49125).
Proof. exact (@lem4317761 (_49123 = _49125)). Qed.
Lemma lem4317763 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4317764 {A : Type'} (_49123 : A) (_49125 : A) : (term2035 A _49123 _49125) = (term2036 A _49123 _49125).
Proof. exact (MK_COMB (@lem4317763) (@lem4317762 A _49123 _49125)). Qed.
Lemma lem4317766 (a : Prop) : (term189 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4317767 {A : Type'} (_49122 : type1364 A) (_49124 : type1364 A) : (term2037 A _49122 _49124) = (_49122 = _49124).
Proof. exact (@lem4317766 (_49122 = _49124)). Qed.
Lemma lem4317768 {A : Type'} (_49123 : A) (_49125 : A) (_49122 : type1364 A) (_49124 : type1364 A) : (term2033 A _49123 _49125 _49122 _49124) = (term2038 A _49123 _49125 _49122 _49124).
Proof. exact (MK_COMB (@lem4317764 A _49123 _49125) (@lem4317767 A _49122 _49124)). Qed.
Lemma lem4317769 {A : Type'} (_49123 : A) (_49125 : A) (_49122 : type1364 A) (_49124 : type1364 A) : (term2032 A _49123 _49125 _49122 _49124) = (term2038 A _49123 _49125 _49122 _49124).
Proof. exact (TRANS (@lem4317759 A _49123 _49125 _49122 _49124) (@lem4317768 A _49123 _49125 _49122 _49124)). Qed.
Lemma lem4317770 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4317771 {A : Type'} (_49123 : A) (_49125 : A) (_49122 : type1364 A) (_49124 : type1364 A) : (term2039 A _49123 _49125 _49122 _49124) = (term2040 A _49123 _49125 _49122 _49124).
Proof. exact (MK_COMB (@lem4317770) (@lem4317769 A _49123 _49125 _49122 _49124)). Qed.
Lemma lem4317772 {A : Type'} (_49122 : type1364 A) (_49123 : A) (_49124 : type1364 A) (_49125 : A) : ((@I (A -> (A -> Prop) -> Prop) _49122 _49123) = (@I (A -> (A -> Prop) -> Prop) _49124 _49125)) = ((@I (A -> (A -> Prop) -> Prop) _49122 _49123) = (@I (A -> (A -> Prop) -> Prop) _49124 _49125)).
Proof. exact (eq_refl ((@I (A -> (A -> Prop) -> Prop) _49122 _49123) = (@I (A -> (A -> Prop) -> Prop) _49124 _49125))). Qed.
Lemma lem4317773 {A : Type'} (_49122 : type1364 A) (_49123 : A) (_49124 : type1364 A) (_49125 : A) : (term2028 A _49122 _49123 _49124 _49125) = (term2041 A _49122 _49123 _49124 _49125).
Proof. exact (MK_COMB (@lem4317771 A _49123 _49125 _49122 _49124) (@lem4317772 A _49122 _49123 _49124 _49125)). Qed.
Lemma lem4317774 {A : Type'} (_49122 : type1364 A) (_49123 : A) (_49124 : type1364 A) (_49125 : A) : (term2025 A _49123 _49125 _49122 _49124) = (term2041 A _49122 _49123 _49124 _49125).
Proof. exact (TRANS (@lem4317756 A _49122 _49123 _49124 _49125) (@lem4317773 A _49122 _49123 _49124 _49125)). Qed.
Lemma lem4317776 {A B : Type'} (x : A) (x''' : B) (x' : prod A B) (x'' : A) (y : B) (h1 : term1213 A B) (h2 : x' = (@pair A B x x''')) (h3 : x' = (@pair A B x'' y)) : term2042 A x x''.
Proof. exact (conj (@lem4317654 A B x x''' x' x'' y h1 h2 h3) (@lem4317663 A)). Qed.
Lemma lem4317778 {A : Type'} (_49122 : type1364 A) (_49123 : A) (_49124 : type1364 A) (_49125 : A) : term2041 A _49122 _49123 _49124 _49125.
Proof. exact (EQ_MP (@lem4317774 A _49122 _49123 _49124 _49125) (@lem4317753 A _49123 _49125 _49122 _49124)). Qed.
Lemma lem4317779 {A : Type'} (_49122 : type1364 A) (_49123 : A) (_49124 : type1364 A) (_49125 : A) : term2041 A _49122 _49123 _49124 _49125.
Proof. exact (@lem4317778 A _49122 _49123 _49124 _49125). Qed.
Lemma lem4317780 {A : Type'} (x : A) (x'' : A) : term2043 A x x''.
Proof. exact (@lem4317779 A (@IN A) x (@IN A) x''). Qed.
Lemma lem4317783 {A B : Type'} (x : A) (x''' : B) (x' : prod A B) (x'' : A) (y : B) (h1 : term1213 A B) (h2 : x' = (@pair A B x x''')) (h3 : x' = (@pair A B x'' y)) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x'').
Proof. exact (@lem4317780 A x x'' (@lem4317776 A B x x''' x' x'' y h1 h2 h3)). Qed.
Lemma lem4317784 {A B : Type'} (x : A) (x''' : B) (x' : prod A B) (x'' : A) (y : B) (h1 : term1213 A B) (h2 : x' = (@pair A B x x''')) (h3 : x' = (@pair A B x'' y)) : term2044 A x x''.
Proof. exact (fun h0 : term2045 A x x'' => @lem4317783 A B x x''' x' x'' y h1 h2 h3). Qed.
Lemma lem4317786 (p : Prop) : (term467 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4317787 {A : Type'} (x : A) (x'' : A) : (term2044 A x x'') = ((@I (A -> (A -> Prop) -> Prop) (@IN A) x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x'')).
Proof. exact (@lem4317786 ((@I (A -> (A -> Prop) -> Prop) (@IN A) x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x''))). Qed.
Lemma lem4317788 {A B : Type'} (x : A) (x''' : B) (x' : prod A B) (x'' : A) (y : B) (h1 : term1213 A B) (h2 : x' = (@pair A B x x''')) (h3 : x' = (@pair A B x'' y)) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x'').
Proof. exact (EQ_MP (@lem4317787 A x x'') (@lem4317784 A B x x''' x' x'' y h1 h2 h3)). Qed.
Lemma lem4317790 {A : Type'} (x : type686 A) : x = x.
Proof. exact (@lem21386 (type686 A) x). Qed.
Lemma lem4317791 {A : Type'} (x : type686 A) : x = x.
Proof. exact (@lem4317790 A x). Qed.
Lemma lem4317792 {A : Type'} (x : A) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem4317791 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x)). Qed.
Lemma lem4317793 {A : Type'} (x : A) : term2046 A x.
Proof. exact (fun h0 : term2047 A x => @lem4317792 A x). Qed.
Lemma lem4317795 (p : Prop) : (term467 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4317796 {A : Type'} (x : A) : (term2046 A x) = ((@I (A -> (A -> Prop) -> Prop) (@IN A) x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x)).
Proof. exact (@lem4317795 ((@I (A -> (A -> Prop) -> Prop) (@IN A) x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x))). Qed.
Lemma lem4317797 {A : Type'} (x : A) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x) = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (EQ_MP (@lem4317796 A x) (@lem4317793 A x)). Qed.
Lemma lem4317815 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4317816 {A : Type'} (y : type686 A) (x : type686 A) (z : type686 A) : (term2048 A x y z) = (term2049 A y x z).
Proof. exact (@lem4317815 (y = z) (term2050 A x z)). Qed.
Lemma lem4317826 {A : Type'} (x : type686 A) (y : type686 A) : (term2051 A x y) = (term2051 A x y).
Proof. exact (eq_refl (term2051 A x y)). Qed.
Lemma lem4317827 {A : Type'} (y : type686 A) (x : type686 A) (z : type686 A) : (term2006 A x y z) = (term2052 A y x z).
Proof. exact (MK_COMB (@lem4317826 A x y) (@lem4317816 A y x z)). Qed.
Lemma lem4317831 (q : Prop) (p : Prop) (r : Prop) : (term48 p q r) = (term48 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4317832 {A : Type'} (y : type686 A) (x : type686 A) (z : type686 A) : (term2052 A y x z) = (term2053 A y x z).
Proof. exact (@lem4317831 (y = z) (term2050 A x y) (term2050 A x z)). Qed.
Lemma lem4317854 {A : Type'} (y : type686 A) (x : type686 A) (z : type686 A) : (term2006 A x y z) = (term2053 A y x z).
Proof. exact (TRANS (@lem4317827 A y x z) (@lem4317832 A y x z)). Qed.
Lemma lem4317855 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4317856 {A : Type'} (y : type686 A) (x : type686 A) (z : type686 A) : (term2054 A x y z) = (term2055 A y x z).
Proof. exact (MK_COMB (@lem4317855) (@lem4317854 A y x z)). Qed.
Lemma lem4317878 {A : Type'} (y : type686 A) (x : type686 A) (z : type686 A) : (term2053 A y x z) = (term2053 A y x z).
Proof. exact (eq_refl (term2053 A y x z)). Qed.
Lemma lem4317879 {A : Type'} (y : type686 A) (x : type686 A) (z : type686 A) : ((term2006 A x y z) = (term2053 A y x z)) = ((term2053 A y x z) = (term2053 A y x z)).
Proof. exact (MK_COMB (@lem4317856 A y x z) (@lem4317878 A y x z)). Qed.
Lemma lem4317881 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4317882 (x : Prop) : (x = x) = True.
Proof. exact (@lem4317881 Prop x). Qed.
Lemma lem4317883 {A : Type'} (y : type686 A) (x : type686 A) (z : type686 A) : ((term2053 A y x z) = (term2053 A y x z)) = True.
Proof. exact (@lem4317882 (term2053 A y x z)). Qed.
Lemma lem4317884 {A : Type'} (y : type686 A) (x : type686 A) (z : type686 A) : ((term2006 A x y z) = (term2053 A y x z)) = True.
Proof. exact (TRANS (@lem4317879 A y x z) (@lem4317883 A y x z)). Qed.
Lemma lem4317885 {A : Type'} (y : type686 A) (x : type686 A) (z : type686 A) : True = ((term2006 A x y z) = (term2053 A y x z)).
Proof. exact (SYM (@lem4317884 A y x z)). Qed.
Lemma lem4317886 {A : Type'} (y : type686 A) (x : type686 A) (z : type686 A) : (term2006 A x y z) = (term2053 A y x z).
Proof. exact (EQ_MP (@lem4317885 A y x z) (@lem0)). Qed.
Lemma lem4317887 {A : Type'} (y : type686 A) (x : type686 A) (z : type686 A) : term2053 A y x z.
Proof. exact (EQ_MP (@lem4317886 A y x z) (@lem4317489 A x y z)). Qed.
Lemma lem4317889 (b : Prop) (a : Prop) : (a \/ b) = (term2013 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4317890 {A : Type'} (x : type686 A) (y : type686 A) (z : type686 A) : (term2053 A y x z) = (term2056 A x y z).
Proof. exact (@lem4317889 (term2057 A y x z) (y = z)). Qed.
Lemma lem4317892 (a : Prop) (b : Prop) : (term2030 a b) = (term2031 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4317893 {A : Type'} (y : type686 A) (x : type686 A) (z : type686 A) : (term2058 A y x z) = (term2059 A y x z).
Proof. exact (@lem4317892 (term2050 A x y) (term2050 A x z)). Qed.
Lemma lem4317895 (a : Prop) : (term189 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4317896 {A : Type'} (x : type686 A) (y : type686 A) : (term2060 A x y) = (x = y).
Proof. exact (@lem4317895 (x = y)). Qed.
Lemma lem4317897 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4317898 {A : Type'} (x : type686 A) (y : type686 A) : (term2061 A x y) = (term2062 A x y).
Proof. exact (MK_COMB (@lem4317897) (@lem4317896 A x y)). Qed.
Lemma lem4317900 (a : Prop) : (term189 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4317901 {A : Type'} (x : type686 A) (z : type686 A) : (term2060 A x z) = (x = z).
Proof. exact (@lem4317900 (x = z)). Qed.
Lemma lem4317902 {A : Type'} (y : type686 A) (x : type686 A) (z : type686 A) : (term2059 A y x z) = (term2063 A y x z).
Proof. exact (MK_COMB (@lem4317898 A x y) (@lem4317901 A x z)). Qed.
Lemma lem4317903 {A : Type'} (y : type686 A) (x : type686 A) (z : type686 A) : (term2058 A y x z) = (term2063 A y x z).
Proof. exact (TRANS (@lem4317893 A y x z) (@lem4317902 A y x z)). Qed.
Lemma lem4317904 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4317905 {A : Type'} (y : type686 A) (x : type686 A) (z : type686 A) : (term2064 A y x z) = (term2065 A y x z).
Proof. exact (MK_COMB (@lem4317904) (@lem4317903 A y x z)). Qed.
Lemma lem4317906 {A : Type'} (y : type686 A) (z : type686 A) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem4317907 {A : Type'} (x : type686 A) (y : type686 A) (z : type686 A) : (term2056 A x y z) = (term2066 A x y z).
Proof. exact (MK_COMB (@lem4317905 A y x z) (@lem4317906 A y z)). Qed.
Lemma lem4317908 {A : Type'} (x : type686 A) (y : type686 A) (z : type686 A) : (term2053 A y x z) = (term2066 A x y z).
Proof. exact (TRANS (@lem4317890 A x y z) (@lem4317907 A x y z)). Qed.
Lemma lem4317910 {A B : Type'} (x : A) (x''' : B) (x' : prod A B) (x'' : A) (y : B) (h1 : term1213 A B) (h2 : x' = (@pair A B x x''')) (h3 : x' = (@pair A B x'' y)) : term2067 A x'' x.
Proof. exact (conj (@lem4317788 A B x x''' x' x'' y h1 h2 h3) (@lem4317797 A x)). Qed.
Lemma lem4317912 {A : Type'} (x : type686 A) (y : type686 A) (z : type686 A) : term2066 A x y z.
Proof. exact (EQ_MP (@lem4317908 A x y z) (@lem4317887 A y x z)). Qed.
Lemma lem4317913 {A : Type'} (x : type686 A) (y : type686 A) (z : type686 A) : term2066 A x y z.
Proof. exact (@lem4317912 A x y z). Qed.
Lemma lem4317914 {A : Type'} (x'' : A) (x : A) : term2068 A x'' x.
Proof. exact (@lem4317913 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x) (@I (A -> (A -> Prop) -> Prop) (@IN A) x'') (@I (A -> (A -> Prop) -> Prop) (@IN A) x)). Qed.
Lemma lem4317917 {A B : Type'} (x : A) (x''' : B) (x' : prod A B) (x'' : A) (y : B) (h1 : term1213 A B) (h2 : x' = (@pair A B x x''')) (h3 : x' = (@pair A B x'' y)) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x'') = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (@lem4317914 A x'' x (@lem4317910 A B x x''' x' x'' y h1 h2 h3)). Qed.
Lemma lem4317918 {A B : Type'} (x : A) (x''' : B) (x' : prod A B) (x'' : A) (y : B) (h1 : term1213 A B) (h2 : x' = (@pair A B x x''')) (h3 : x' = (@pair A B x'' y)) : term2044 A x'' x.
Proof. exact (fun h0 : term2045 A x'' x => @lem4317917 A B x x''' x' x'' y h1 h2 h3). Qed.
Lemma lem4317920 (p : Prop) : (term467 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4317921 {A : Type'} (x'' : A) (x : A) : (term2044 A x'' x) = ((@I (A -> (A -> Prop) -> Prop) (@IN A) x'') = (@I (A -> (A -> Prop) -> Prop) (@IN A) x)).
Proof. exact (@lem4317920 ((@I (A -> (A -> Prop) -> Prop) (@IN A) x'') = (@I (A -> (A -> Prop) -> Prop) (@IN A) x))). Qed.
Lemma lem4317922 {A B : Type'} (x : A) (x''' : B) (x' : prod A B) (x'' : A) (y : B) (h1 : term1213 A B) (h2 : x' = (@pair A B x x''')) (h3 : x' = (@pair A B x'' y)) : (@I (A -> (A -> Prop) -> Prop) (@IN A) x'') = (@I (A -> (A -> Prop) -> Prop) (@IN A) x).
Proof. exact (EQ_MP (@lem4317921 A x'' x) (@lem4317918 A B x x''' x' x'' y h1 h2 h3)). Qed.
Lemma lem4317924 {A : Type'} (x'' : A) (s : A -> Prop) (h1 : @IN A x'' s) : term1946 A x'' s.
Proof. exact (EQ_MP (@lem4313967 A x'' s) (@lem4310774 A x'' s h1)). Qed.
Lemma lem4317925 {A : Type'} (x'' : A) (s : A -> Prop) (h1 : @IN A x'' s) : term2069 A x'' s.
Proof. exact (fun h0 : term1947 A x'' s => @lem4317924 A x'' s h1). Qed.
Lemma lem4317927 (p : Prop) : (term467 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4317928 {A : Type'} (x'' : A) (s : A -> Prop) : (term2069 A x'' s) = (term1946 A x'' s).
Proof. exact (@lem4317927 (term1946 A x'' s)). Qed.
Lemma lem4317929 {A : Type'} (x'' : A) (s : A -> Prop) (h1 : @IN A x'' s) : term1946 A x'' s.
Proof. exact (EQ_MP (@lem4317928 A x'' s) (@lem4317925 A x'' s h1)). Qed.
Lemma lem4317947 (q : Prop) (p : Prop) (r : Prop) : (term48 p q r) = (term48 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4317948 {A : Type'} (_48989 : A -> Prop) (_48988 : type686 A) (_48986 : type686 A) (_48987 : A -> Prop) : (term1999 A _48988 _48989 _48986 _48987) = (term2070 A _48989 _48988 _48986 _48987).
Proof. exact (@lem4317947 (@I ((A -> Prop) -> Prop) _48988 _48989) (term2050 A _48986 _48988) (term2071 A _48986 _48987)). Qed.
Lemma lem4317966 {A : Type'} (_48987 : A -> Prop) (_48989 : A -> Prop) : (term2072 A _48987 _48989) = (term2072 A _48987 _48989).
Proof. exact (eq_refl (term2072 A _48987 _48989)). Qed.
Lemma lem4317967 {A : Type'} (_48989 : A -> Prop) (_48988 : type686 A) (_48986 : type686 A) (_48987 : A -> Prop) : (term2001 A _48988 _48989 _48986 _48987) = (term2073 A _48989 _48988 _48986 _48987).
Proof. exact (MK_COMB (@lem4317966 A _48987 _48989) (@lem4317948 A _48989 _48988 _48986 _48987)). Qed.
Lemma lem4317971 (q : Prop) (p : Prop) (r : Prop) : (term48 p q r) = (term48 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4317972 {A : Type'} (_48989 : A -> Prop) (_48988 : type686 A) (_48986 : type686 A) (_48987 : A -> Prop) : (term2073 A _48989 _48988 _48986 _48987) = (term2074 A _48989 _48988 _48986 _48987).
Proof. exact (@lem4317971 (@I ((A -> Prop) -> Prop) _48988 _48989) (term2075 A _48987 _48989) (term2076 A _48988 _48986 _48987)). Qed.
Lemma lem4318002 {A : Type'} (_48989 : A -> Prop) (_48988 : type686 A) (_48986 : type686 A) (_48987 : A -> Prop) : (term2001 A _48988 _48989 _48986 _48987) = (term2074 A _48989 _48988 _48986 _48987).
Proof. exact (TRANS (@lem4317967 A _48989 _48988 _48986 _48987) (@lem4317972 A _48989 _48988 _48986 _48987)). Qed.
Lemma lem4318003 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4318004 {A : Type'} (_48989 : A -> Prop) (_48988 : type686 A) (_48986 : type686 A) (_48987 : A -> Prop) : (term2077 A _48988 _48989 _48986 _48987) = (term2078 A _48989 _48988 _48986 _48987).
Proof. exact (MK_COMB (@lem4318003) (@lem4318002 A _48989 _48988 _48986 _48987)). Qed.
Lemma lem4318034 {A : Type'} (_48989 : A -> Prop) (_48988 : type686 A) (_48986 : type686 A) (_48987 : A -> Prop) : (term2074 A _48989 _48988 _48986 _48987) = (term2074 A _48989 _48988 _48986 _48987).
Proof. exact (eq_refl (term2074 A _48989 _48988 _48986 _48987)). Qed.
Lemma lem4318035 {A : Type'} (_48989 : A -> Prop) (_48988 : type686 A) (_48986 : type686 A) (_48987 : A -> Prop) : ((term2001 A _48988 _48989 _48986 _48987) = (term2074 A _48989 _48988 _48986 _48987)) = ((term2074 A _48989 _48988 _48986 _48987) = (term2074 A _48989 _48988 _48986 _48987)).
Proof. exact (MK_COMB (@lem4318004 A _48989 _48988 _48986 _48987) (@lem4318034 A _48989 _48988 _48986 _48987)). Qed.
Lemma lem4318037 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4318038 (x : Prop) : (x = x) = True.
Proof. exact (@lem4318037 Prop x). Qed.
Lemma lem4318039 {A : Type'} (_48989 : A -> Prop) (_48988 : type686 A) (_48986 : type686 A) (_48987 : A -> Prop) : ((term2074 A _48989 _48988 _48986 _48987) = (term2074 A _48989 _48988 _48986 _48987)) = True.
Proof. exact (@lem4318038 (term2074 A _48989 _48988 _48986 _48987)). Qed.
Lemma lem4318040 {A : Type'} (_48989 : A -> Prop) (_48988 : type686 A) (_48986 : type686 A) (_48987 : A -> Prop) : ((term2001 A _48988 _48989 _48986 _48987) = (term2074 A _48989 _48988 _48986 _48987)) = True.
Proof. exact (TRANS (@lem4318035 A _48989 _48988 _48986 _48987) (@lem4318039 A _48989 _48988 _48986 _48987)). Qed.
Lemma lem4318041 {A : Type'} (_48989 : A -> Prop) (_48988 : type686 A) (_48986 : type686 A) (_48987 : A -> Prop) : True = ((term2001 A _48988 _48989 _48986 _48987) = (term2074 A _48989 _48988 _48986 _48987)).
Proof. exact (SYM (@lem4318040 A _48989 _48988 _48986 _48987)). Qed.
Lemma lem4318042 {A : Type'} (_48989 : A -> Prop) (_48988 : type686 A) (_48986 : type686 A) (_48987 : A -> Prop) : (term2001 A _48988 _48989 _48986 _48987) = (term2074 A _48989 _48988 _48986 _48987).
Proof. exact (EQ_MP (@lem4318041 A _48989 _48988 _48986 _48987) (@lem0)). Qed.
Lemma lem4318043 {A : Type'} (_48989 : A -> Prop) (_48988 : type686 A) (_48986 : type686 A) (_48987 : A -> Prop) : term2074 A _48989 _48988 _48986 _48987.
Proof. exact (EQ_MP (@lem4318042 A _48989 _48988 _48986 _48987) (@lem4316977 A _48988 _48989 _48986 _48987)). Qed.
Lemma lem4318045 (b : Prop) (a : Prop) : (a \/ b) = (term2013 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4318046 {A : Type'} (_48986 : type686 A) (_48987 : A -> Prop) (_48988 : type686 A) (_48989 : A -> Prop) : (term2074 A _48989 _48988 _48986 _48987) = (term2079 A _48986 _48987 _48988 _48989).
Proof. exact (@lem4318045 (term2080 A _48989 _48988 _48986 _48987) (@I ((A -> Prop) -> Prop) _48988 _48989)). Qed.
Lemma lem4318048 (a : Prop) (b : Prop) : (term2030 a b) = (term2031 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4318049 {A : Type'} (_48989 : A -> Prop) (_48988 : type686 A) (_48986 : type686 A) (_48987 : A -> Prop) : (term2081 A _48989 _48988 _48986 _48987) = (term2082 A _48989 _48988 _48986 _48987).
Proof. exact (@lem4318048 (term2075 A _48987 _48989) (term2076 A _48988 _48986 _48987)). Qed.
Lemma lem4318051 (a : Prop) : (term189 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4318052 {A : Type'} (_48987 : A -> Prop) (_48989 : A -> Prop) : (term2083 A _48987 _48989) = (_48987 = _48989).
Proof. exact (@lem4318051 (_48987 = _48989)). Qed.
Lemma lem4318053 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4318054 {A : Type'} (_48987 : A -> Prop) (_48989 : A -> Prop) : (term2084 A _48987 _48989) = (term2085 A _48987 _48989).
Proof. exact (MK_COMB (@lem4318053) (@lem4318052 A _48987 _48989)). Qed.
Lemma lem4318056 (a : Prop) (b : Prop) : (term2030 a b) = (term2031 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4318057 {A : Type'} (_48988 : type686 A) (_48986 : type686 A) (_48987 : A -> Prop) : (term2086 A _48988 _48986 _48987) = (term2087 A _48988 _48986 _48987).
Proof. exact (@lem4318056 (term2050 A _48986 _48988) (term2071 A _48986 _48987)). Qed.
Lemma lem4318059 (a : Prop) : (term189 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4318060 {A : Type'} (_48986 : type686 A) (_48988 : type686 A) : (term2060 A _48986 _48988) = (_48986 = _48988).
Proof. exact (@lem4318059 (_48986 = _48988)). Qed.
Lemma lem4318061 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4318062 {A : Type'} (_48986 : type686 A) (_48988 : type686 A) : (term2061 A _48986 _48988) = (term2062 A _48986 _48988).
Proof. exact (MK_COMB (@lem4318061) (@lem4318060 A _48986 _48988)). Qed.
Lemma lem4318064 (a : Prop) : (term189 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4318065 {A : Type'} (_48986 : type686 A) (_48987 : A -> Prop) : (term2088 A _48986 _48987) = (@I ((A -> Prop) -> Prop) _48986 _48987).
Proof. exact (@lem4318064 (@I ((A -> Prop) -> Prop) _48986 _48987)). Qed.
Lemma lem4318066 {A : Type'} (_48988 : type686 A) (_48986 : type686 A) (_48987 : A -> Prop) : (term2087 A _48988 _48986 _48987) = (term2089 A _48988 _48986 _48987).
Proof. exact (MK_COMB (@lem4318062 A _48986 _48988) (@lem4318065 A _48986 _48987)). Qed.
Lemma lem4318067 {A : Type'} (_48988 : type686 A) (_48986 : type686 A) (_48987 : A -> Prop) : (term2086 A _48988 _48986 _48987) = (term2089 A _48988 _48986 _48987).
Proof. exact (TRANS (@lem4318057 A _48988 _48986 _48987) (@lem4318066 A _48988 _48986 _48987)). Qed.
Lemma lem4318068 {A : Type'} (_48989 : A -> Prop) (_48988 : type686 A) (_48986 : type686 A) (_48987 : A -> Prop) : (term2082 A _48989 _48988 _48986 _48987) = (term2090 A _48989 _48988 _48986 _48987).
Proof. exact (MK_COMB (@lem4318054 A _48987 _48989) (@lem4318067 A _48988 _48986 _48987)). Qed.
Lemma lem4318069 {A : Type'} (_48989 : A -> Prop) (_48988 : type686 A) (_48986 : type686 A) (_48987 : A -> Prop) : (term2081 A _48989 _48988 _48986 _48987) = (term2090 A _48989 _48988 _48986 _48987).
Proof. exact (TRANS (@lem4318049 A _48989 _48988 _48986 _48987) (@lem4318068 A _48989 _48988 _48986 _48987)). Qed.
Lemma lem4318070 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4318071 {A : Type'} (_48989 : A -> Prop) (_48988 : type686 A) (_48986 : type686 A) (_48987 : A -> Prop) : (term2091 A _48989 _48988 _48986 _48987) = (term2092 A _48989 _48988 _48986 _48987).
Proof. exact (MK_COMB (@lem4318070) (@lem4318069 A _48989 _48988 _48986 _48987)). Qed.
Lemma lem4318072 {A : Type'} (_48988 : type686 A) (_48989 : A -> Prop) : (@I ((A -> Prop) -> Prop) _48988 _48989) = (@I ((A -> Prop) -> Prop) _48988 _48989).
Proof. exact (eq_refl (@I ((A -> Prop) -> Prop) _48988 _48989)). Qed.
Lemma lem4318073 {A : Type'} (_48986 : type686 A) (_48987 : A -> Prop) (_48988 : type686 A) (_48989 : A -> Prop) : (term2079 A _48986 _48987 _48988 _48989) = (term2093 A _48986 _48987 _48988 _48989).
Proof. exact (MK_COMB (@lem4318071 A _48989 _48988 _48986 _48987) (@lem4318072 A _48988 _48989)). Qed.
Lemma lem4318074 {A : Type'} (_48986 : type686 A) (_48987 : A -> Prop) (_48988 : type686 A) (_48989 : A -> Prop) : (term2074 A _48989 _48988 _48986 _48987) = (term2093 A _48986 _48987 _48988 _48989).
Proof. exact (TRANS (@lem4318046 A _48986 _48987 _48988 _48989) (@lem4318073 A _48986 _48987 _48988 _48989)). Qed.
Lemma lem4318076 {A B : Type'} (x : A) (x''' : B) (x' : prod A B) (y : B) (x'' : A) (s : A -> Prop) (h1 : term1213 A B) (h2 : x' = (@pair A B x x''')) (h3 : x' = (@pair A B x'' y)) (h4 : @IN A x'' s) : term2094 A x x'' s.
Proof. exact (conj (@lem4317922 A B x x''' x' x'' y h1 h2 h3) (@lem4317929 A x'' s h4)). Qed.
Lemma lem4318077 {A B : Type'} (x : A) (x''' : B) (x' : prod A B) (y : B) (x'' : A) (s : A -> Prop) (h1 : term1213 A B) (h2 : x' = (@pair A B x x''')) (h3 : x' = (@pair A B x'' y)) (h4 : @IN A x'' s) : term2095 A x x'' s.
Proof. exact (conj (@lem4317586 A s) (@lem4318076 A B x x''' x' y x'' s h1 h2 h3 h4)). Qed.
Lemma lem4318079 {A : Type'} (_48986 : type686 A) (_48987 : A -> Prop) (_48988 : type686 A) (_48989 : A -> Prop) : term2093 A _48986 _48987 _48988 _48989.
Proof. exact (EQ_MP (@lem4318074 A _48986 _48987 _48988 _48989) (@lem4318043 A _48989 _48988 _48986 _48987)). Qed.
Lemma lem4318080 {A : Type'} (_48986 : type686 A) (_48987 : A -> Prop) (_48988 : type686 A) (_48989 : A -> Prop) : term2093 A _48986 _48987 _48988 _48989.
Proof. exact (@lem4318079 A _48986 _48987 _48988 _48989). Qed.
Lemma lem4318081 {A : Type'} (x'' : A) (x : A) (s : A -> Prop) : term2096 A x'' x s.
Proof. exact (@lem4318080 A (@I (A -> (A -> Prop) -> Prop) (@IN A) x'') s (@I (A -> (A -> Prop) -> Prop) (@IN A) x) s). Qed.
Lemma lem4318084 {A B : Type'} (x : A) (x''' : B) (x' : prod A B) (y : B) (x'' : A) (s : A -> Prop) (h1 : term1213 A B) (h2 : x' = (@pair A B x x''')) (h3 : x' = (@pair A B x'' y)) (h4 : @IN A x'' s) : term1946 A x s.
Proof. exact (@lem4318081 A x'' x s (@lem4318077 A B x x''' x' y x'' s h1 h2 h3 h4)). Qed.
Lemma lem4318085 {A B : Type'} (x : A) (x''' : B) (x' : prod A B) (y : B) (x'' : A) (s : A -> Prop) (h1 : term1213 A B) (h2 : x' = (@pair A B x x''')) (h3 : x' = (@pair A B x'' y)) (h4 : @IN A x'' s) : term2069 A x s.
Proof. exact (fun h0 : term1947 A x s => @lem4318084 A B x x''' x' y x'' s h1 h2 h3 h4). Qed.
Lemma lem4318087 (p : Prop) : (term467 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4318088 {A : Type'} (x : A) (s : A -> Prop) : (term2069 A x s) = (term1946 A x s).
Proof. exact (@lem4318087 (term1946 A x s)). Qed.
Lemma lem4318089 {A B : Type'} (x : A) (x''' : B) (x' : prod A B) (y : B) (x'' : A) (s : A -> Prop) (h1 : term1213 A B) (h2 : x' = (@pair A B x x''')) (h3 : x' = (@pair A B x'' y)) (h4 : @IN A x'' s) : term1946 A x s.
Proof. exact (EQ_MP (@lem4318088 A x s) (@lem4318085 A B x x''' x' y x'' s h1 h2 h3 h4)). Qed.
Lemma lem4318092 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4318094 {A : Type'} (x : A) (s : A -> Prop) : (term1947 A x s) = (term2097 A x s).
Proof. exact (@lem4318092 (term1946 A x s)). Qed.
Lemma lem4318097 {A : Type'} (x : A) (s : A -> Prop) (h1 : term808 A x s) : term2097 A x s.
Proof. exact (EQ_MP (@lem4318094 A x s) (@lem4316537 A x s h1)). Qed.
Lemma lem4318100 {A B : Type'} (x : A) (x''' : B) (x' : prod A B) (y : B) (x'' : A) (s : A -> Prop) (h1 : term1213 A B) (h2 : term808 A x s) (h3 : x' = (@pair A B x x''')) (h4 : x' = (@pair A B x'' y)) (h5 : @IN A x'' s) : False.
Proof. exact (@lem4318097 A x s h2 (@lem4318089 A B x x''' x' y x'' s h1 h3 h4 h5)). Qed.
Lemma lem4318101 {A B : Type'} (x : A) (x''' : B) (x' : prod A B) (y : B) (x'' : A) (s : A -> Prop) (h1 : term1213 A B) (h2 : term808 A x s) (h3 : x' = (@pair A B x x''')) (h4 : x' = (@pair A B x'' y)) (h5 : @IN A x'' s) : term476.
Proof. exact (fun h0 : ~ False => @lem4318100 A B x x''' x' y x'' s h1 h2 h3 h4 h5). Qed.
Lemma lem4318103 (p : Prop) : (term467 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4318104 : term476 = False.
Proof. exact (@lem4318103 False). Qed.
Lemma lem4318107 {A B : Type'} (x : A) (x''' : B) (x' : prod A B) (y : B) (x'' : A) (s : A -> Prop) (h1 : term1213 A B) (h2 : term808 A x s) (h3 : x' = (@pair A B x x''')) (h4 : x' = (@pair A B x'' y)) (h5 : @IN A x'' s) : False.
Proof. exact (EQ_MP (@lem4318104) (@lem4318101 A B x x''' x' y x'' s h1 h2 h3 h4 h5)). Qed.
Lemma lem4318108 {A B : Type'} (_48808 : type621 A B) (x''''' : type619 A B) (x : A) (x''' : B) (x' : prod A B) (y : B) (x'' : A) (s : A -> Prop) (h1 : term1213 A B) (h2 : term1756 A B _48808 x''''') (h3 : term808 A x s) (h4 : x' = (@pair A B x x''')) (h5 : x' = (@pair A B x'' y)) (h6 : @IN A x'' s) : False.
Proof. exact (ex_elim (@lem4313825 A B _48808 x''''' h2) (fun y' : type620 A B => fun h0 : term1755 A B _48808 x''''' y' => @lem4318107 A B x x''' x' y x'' s h1 h3 h4 h5 h6)). Qed.
Lemma lem4318109 {A B : Type'} (_48808 : type621 A B) (x : A) (x''' : B) (x' : prod A B) (y : B) (x'' : A) (s : A -> Prop) (h1 : term1213 A B) (h2 : term1434 A B _48808) (h3 : term808 A x s) (h4 : x' = (@pair A B x x''')) (h5 : x' = (@pair A B x'' y)) (h6 : @IN A x'' s) : False.
Proof. exact (ex_elim (@lem4310456 A B _48808 h2) (fun x''''' : type619 A B => fun h0 : term1757 A B _48808 x''''' => @lem4318108 A B _48808 x''''' x x''' x' y x'' s h1 h0 h3 h4 h5 h6)). Qed.
Lemma lem4318110 {A B : Type'} (_48808 : type621 A B) (x : A) (x''' : B) (x' : prod A B) (y : B) (x'' : A) (s : A -> Prop) (h1 : term1213 A B) (h2 : term1434 A B _48808) (h3 : term1352 A B _48808 s) (h4 : term808 A x s) (h5 : x' = (@pair A B x x''')) (h6 : x' = (@pair A B x'' y)) (h7 : @IN A x'' s) : False.
Proof. exact (ex_elim (@lem4310768 A B _48808 s h3) (fun x'''' : type471 A B => fun h0 : term1840 A B _48808 s x'''' => @lem4318109 A B _48808 x x''' x' y x'' s h1 h2 h4 h5 h6 h7)). Qed.
Lemma lem4318111 {A B : Type'} (_48808 : type621 A B) (x : A) (x''' : B) (x' : prod A B) (y : B) (x'' : A) (s : A -> Prop) (h1 : term1213 A B) (h2 : term1434 A B _48808) (h3 : term1352 A B _48808 s) (h4 : term808 A x s) (h5 : x' = (@pair A B x x''')) (h6 : x' = (@pair A B x'' y)) (h7 : @IN A x'' s) : (x' = (@pair A B x x''')) = False.
Proof. exact (prop_ext (fun h8 : x' = (@pair A B x x''') => @lem4318110 A B _48808 x x''' x' y x'' s h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem4310792 A B x' x x''' h5)). Qed.
Lemma lem4318112 {A B : Type'} (_48808 : type621 A B) (x : A) (x''' : B) (x' : prod A B) (y : B) (x'' : A) (s : A -> Prop) (h1 : term1213 A B) (h2 : term1434 A B _48808) (h3 : term1352 A B _48808 s) (h4 : term808 A x s) (h5 : x' = (@pair A B x x''')) (h6 : x' = (@pair A B x'' y)) (h7 : @IN A x'' s) : False.
Proof. exact (EQ_MP (@lem4318111 A B _48808 x x''' x' y x'' s h1 h2 h3 h4 h5 h6 h7) (@lem4310792 A B x' x x''' h5)). Qed.
Lemma lem4318113 {A B : Type'} (_48808 : type621 A B) (x : A) (x''' : B) (x' : prod A B) (y : B) (x'' : A) (s : A -> Prop) (h1 : term1213 A B) (h2 : term1434 A B _48808) (h3 : term1352 A B _48808 s) (h4 : term808 A x s) (h5 : x' = (@pair A B x x''')) (h6 : x' = (@pair A B x'' y)) (h7 : @IN A x'' s) : (x' = (@pair A B x'' y)) = False.
Proof. exact (prop_ext (fun h8 : x' = (@pair A B x'' y) => @lem4318112 A B _48808 x x''' x' y x'' s h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem4310786 A B x' x'' y h6)). Qed.
Lemma lem4318114 {A B : Type'} (_48808 : type621 A B) (x : A) (x''' : B) (x' : prod A B) (y : B) (x'' : A) (s : A -> Prop) (h1 : term1213 A B) (h2 : term1434 A B _48808) (h3 : term1352 A B _48808 s) (h4 : term808 A x s) (h5 : x' = (@pair A B x x''')) (h6 : x' = (@pair A B x'' y)) (h7 : @IN A x'' s) : False.
Proof. exact (EQ_MP (@lem4318113 A B _48808 x x''' x' y x'' s h1 h2 h3 h4 h5 h6 h7) (@lem4310786 A B x' x'' y h6)). Qed.
Lemma lem4318115 {A B : Type'} (_48808 : type621 A B) (x : A) (x''' : B) (x' : prod A B) (y : B) (x'' : A) (s : A -> Prop) (h1 : term1213 A B) (h2 : term1434 A B _48808) (h3 : term1352 A B _48808 s) (h4 : term808 A x s) (h5 : x' = (@pair A B x x''')) (h6 : x' = (@pair A B x'' y)) (h7 : @IN A x'' s) : (@IN A x'' s) = False.
Proof. exact (prop_ext (fun h8 : @IN A x'' s => @lem4318114 A B _48808 x x''' x' y x'' s h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem4310774 A x'' s h7)). Qed.
Lemma lem4318116 {A B : Type'} (_48808 : type621 A B) (x : A) (x''' : B) (x' : prod A B) (y : B) (x'' : A) (s : A -> Prop) (h1 : term1213 A B) (h2 : term1434 A B _48808) (h3 : term1352 A B _48808 s) (h4 : term808 A x s) (h5 : x' = (@pair A B x x''')) (h6 : x' = (@pair A B x'' y)) (h7 : @IN A x'' s) : False.
Proof. exact (EQ_MP (@lem4318115 A B _48808 x x''' x' y x'' s h1 h2 h3 h4 h5 h6 h7) (@lem4310774 A x'' s h7)). Qed.
Lemma lem4318117 {A B : Type'} (_48808 : type621 A B) (x : A) (x''' : B) (x' : prod A B) (y : B) (x'' : A) (s : A -> Prop) (h1 : term1213 A B) (h2 : term1434 A B _48808) (h3 : term1352 A B _48808 s) (h4 : term808 A x s) (h5 : x' = (@pair A B x x''')) (h6 : x' = (@pair A B x'' y)) (h7 : @IN A x'' s) : (term808 A x s) = False.
Proof. exact (prop_ext (fun h8 : term808 A x s => @lem4318116 A B _48808 x x''' x' y x'' s h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem4310462 A x s h4)). Qed.
Lemma lem4318118 {A B : Type'} (_48808 : type621 A B) (x : A) (x''' : B) (x' : prod A B) (y : B) (x'' : A) (s : A -> Prop) (h1 : term1213 A B) (h2 : term1434 A B _48808) (h3 : term1352 A B _48808 s) (h4 : term808 A x s) (h5 : x' = (@pair A B x x''')) (h6 : x' = (@pair A B x'' y)) (h7 : @IN A x'' s) : False.
Proof. exact (EQ_MP (@lem4318117 A B _48808 x x''' x' y x'' s h1 h2 h3 h4 h5 h6 h7) (@lem4310462 A x s h4)). Qed.
Lemma lem4318119 {A B : Type'} (_48808 : type621 A B) (x : A) (x''' : B) (x' : prod A B) (y : B) (x'' : A) (s : A -> Prop) (h1 : term1213 A B) (h2 : term1434 A B _48808) (h3 : term1352 A B _48808 s) (h4 : term808 A x s) (h5 : x' = (@pair A B x x''')) (h6 : x' = (@pair A B x'' y)) (h7 : @IN A x'' s) : term1222 A B.
Proof. exact (fun h0 : term1215 A B => @lem4318118 A B _48808 x x''' x' y x'' s h1 h2 h3 h4 h5 h6 h7). Qed.
Lemma lem4318120 {A B : Type'} : (term1222 A B) = (term1223 A B).
Proof. exact (@lem69 (term1215 A B)). Qed.
Lemma lem4318121 {A B : Type'} (_48808 : type621 A B) (x : A) (x''' : B) (x' : prod A B) (y : B) (x'' : A) (s : A -> Prop) (h1 : term1213 A B) (h2 : term1434 A B _48808) (h3 : term1352 A B _48808 s) (h4 : term808 A x s) (h5 : x' = (@pair A B x x''')) (h6 : x' = (@pair A B x'' y)) (h7 : @IN A x'' s) : term1223 A B.
Proof. exact (EQ_MP (@lem4318120 A B) (@lem4318119 A B _48808 x x''' x' y x'' s h1 h2 h3 h4 h5 h6 h7)). Qed.
Lemma lem4318122 {A B : Type'} (_48808 : type621 A B) (x : A) (x''' : B) (x' : prod A B) (y : B) (x'' : A) (s : A -> Prop) (h1 : term1213 A B) (h2 : term1434 A B _48808) (h3 : term1352 A B _48808 s) (h4 : term808 A x s) (h5 : x' = (@pair A B x x''')) (h6 : x' = (@pair A B x'' y)) (h7 : @IN A x'' s) : term1226 A B.
Proof. exact (fun h0 : term1214 B => @lem4318121 A B _48808 x x''' x' y x'' s h1 h2 h3 h4 h5 h6 h7). Qed.
Lemma lem4318123 {A B : Type'} (_48808 : type621 A B) (x : A) (x''' : B) (x' : prod A B) (y : B) (x'' : A) (s : A -> Prop) (h1 : term1213 A B) (h2 : term1434 A B _48808) (h3 : term1352 A B _48808 s) (h4 : term808 A x s) (h5 : x' = (@pair A B x x''')) (h6 : x' = (@pair A B x'' y)) (h7 : @IN A x'' s) : term1229 A B.
Proof. exact (fun h0 : term1217 A B => @lem4318122 A B _48808 x x''' x' y x'' s h1 h2 h3 h4 h5 h6 h7). Qed.
Lemma lem4318124 {A B : Type'} (_48808 : type621 A B) (x : A) (x''' : B) (x' : prod A B) (y : B) (x'' : A) (s : A -> Prop) (h1 : term1213 A B) (h2 : term1434 A B _48808) (h3 : term1352 A B _48808 s) (h4 : term808 A x s) (h5 : x' = (@pair A B x x''')) (h6 : x' = (@pair A B x'' y)) (h7 : @IN A x'' s) : term1232 A B.
Proof. exact (fun h0 : term1216 A => @lem4318123 A B _48808 x x''' x' y x'' s h1 h2 h3 h4 h5 h6 h7). Qed.
Lemma lem4318125 {A B : Type'} (_48808 : type621 A B) (x : A) (x''' : B) (x' : prod A B) (y : B) (x'' : A) (s : A -> Prop) (h1 : term1434 A B _48808) (h2 : term1352 A B _48808 s) (h3 : term808 A x s) (h4 : x' = (@pair A B x x''')) (h5 : x' = (@pair A B x'' y)) (h6 : @IN A x'' s) : term1235 A B.
Proof. exact (fun h0 : term1213 A B => @lem4318124 A B _48808 x x''' x' y x'' s h0 h1 h2 h3 h4 h5 h6). Qed.
Lemma lem4318126 {A B : Type'} (t : type1413 A B) (_48808 : type621 A B) (x : A) (x''' : B) (x' : prod A B) (y : B) (x'' : A) (s : A -> Prop) (h1 : term1434 A B _48808) (h2 : term1352 A B _48808 s) (h3 : term808 A x s) (h4 : x' = (@pair A B x x''')) (h5 : x' = (@pair A B x'' y)) (h6 : @IN A x'' s) : term1238 A B x''' t x.
Proof. exact (fun h0 : term760 A B x''' t x => @lem4318125 A B _48808 x x''' x' y x'' s h1 h2 h3 h4 h5 h6). Qed.
Lemma lem4318127 {A B : Type'} (x''' : B) (t : type1413 A B) (_48808 : type621 A B) (x : A) (x' : prod A B) (y : B) (x'' : A) (s : A -> Prop) (h1 : term1434 A B _48808) (h2 : term1352 A B _48808 s) (h3 : term808 A x s) (h4 : x' = (@pair A B x'' y)) (h5 : @IN A x'' s) : term1241 A B x' x''' t x.
Proof. exact (fun h0 : x' = (@pair A B x x''') => @lem4318126 A B t _48808 x x''' x' y x'' s h1 h2 h3 h0 h4 h5). Qed.
Lemma lem4318128 {A B : Type'} (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (_48808 : type621 A B) (x : A) (x'' : A) (s : A -> Prop) (h1 : term1434 A B _48808) (h2 : term1352 A B _48808 s) (h3 : term808 A x s) (h4 : @IN A x'' s) : term1243 A B x'' y x' x''' t x.
Proof. exact (fun h0 : x' = (@pair A B x'' y) => @lem4318127 A B x''' t _48808 x x' y x'' s h1 h2 h3 h0 h4). Qed.
Lemma lem4318129 {A B : Type'} (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (_48808 : type621 A B) (x : A) (x'' : A) (s : A -> Prop) (h1 : term1434 A B _48808) (h2 : term1352 A B _48808 s) (h3 : term808 A x s) (h4 : @IN A x'' s) : term1245 A B x'' y x' x''' t x.
Proof. exact (fun h0 : term760 A B y t x'' => @lem4318128 A B y x' x''' t _48808 x x'' s h1 h2 h3 h4). Qed.
Lemma lem4318130 {A B : Type'} (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (_48808 : type621 A B) (x : A) (s : A -> Prop) (h1 : term1434 A B _48808) (h2 : term1352 A B _48808 s) (h3 : term808 A x s) : term1248 A B s x'' y x' x''' t x.
Proof. exact (fun h0 : @IN A x'' s => @lem4318129 A B y x' x''' t _48808 x x'' s h1 h2 h3 h0). Qed.
Lemma lem4318131 {A B : Type'} (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (_48808 : type621 A B) (x : A) (s : A -> Prop) (h1 : term1434 A B _48808) (h2 : term808 A x s) : term1354 A B _48808 s x'' y x' x''' t x.
Proof. exact (fun h0 : term1352 A B _48808 s => @lem4318130 A B x'' y x' x''' t _48808 x s h1 h0 h2). Qed.
Lemma lem4318132 {A B : Type'} (n : nat) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (_48808 : type621 A B) (x : A) (s : A -> Prop) (h1 : term1434 A B _48808) (h2 : term808 A x s) : term1355 A B n _48808 s x'' y x' x''' t x.
Proof. exact (fun h0 : term581 A B s t n => @lem4318131 A B x'' y x' x''' t _48808 x s h1 h2). Qed.
Lemma lem4318133 {A B : Type'} (n : nat) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (_48808 : type621 A B) (x : A) (s : A -> Prop) (h1 : term1434 A B _48808) (h2 : term808 A x s) : term1356 A B n _48808 s x'' y x' x''' t x.
Proof. exact (fun h0 : term742 A B t x n => @lem4318132 A B n x'' y x' x''' t _48808 x s h1 h2). Qed.
Lemma lem4318134 {A B : Type'} (m : nat) (n : nat) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (_48808 : type621 A B) (x : A) (s : A -> Prop) (h1 : term1434 A B _48808) (h2 : term808 A x s) : term1357 A B m n _48808 s x'' y x' x''' t x.
Proof. exact (fun h0 : m = (term822 A s) => @lem4318133 A B n x'' y x' x''' t _48808 x s h1 h2). Qed.
Lemma lem4318135 {A B : Type'} (m : nat) (n : nat) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (_48808 : type621 A B) (x : A) (s : A -> Prop) (h1 : term1434 A B _48808) (h2 : term808 A x s) : term1358 A B m n _48808 s x'' y x' x''' t x.
Proof. exact (fun h0 : @FINITE A s => @lem4318134 A B m n x'' y x' x''' t _48808 x s h1 h2). Qed.
Lemma lem4318136 {A B : Type'} (m : nat) (n : nat) (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) (_48808 : type621 A B) (h1 : term1434 A B _48808) : term1359 A B m n _48808 s x'' y x' x''' t x.
Proof. exact (fun h0 : term808 A x s => @lem4318135 A B m n x'' y x' x''' t _48808 x s h1 h0). Qed.
Lemma lem4318141 {A B : Type'} (n : nat) (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) (_48808 : type621 A B) (h1 : term1434 A B _48808) : term1361 A B n _48808 s x'' y x' x''' t x.
Proof. exact (fun m : nat => @lem4318136 A B m n s x'' y x' x''' t x _48808 h1). Qed.
Lemma lem4318146 {A B : Type'} (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) (_48808 : type621 A B) (h1 : term1434 A B _48808) : term1363 A B _48808 s x'' y x' x''' t x.
Proof. exact (fun n : nat => @lem4318141 A B n s x'' y x' x''' t x _48808 h1). Qed.
Lemma lem4318151 {A B : Type'} (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) (_48808 : type621 A B) (h1 : term1434 A B _48808) : term1365 A B _48808 x'' y x' x''' t x.
Proof. exact (fun s : A -> Prop => @lem4318146 A B s x'' y x' x''' t x _48808 h1). Qed.
Lemma lem4318156 {A B : Type'} (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) (_48808 : type621 A B) (h1 : term1434 A B _48808) : term1367 A B _48808 y x' x''' t x.
Proof. exact (fun x'' : A => @lem4318151 A B x'' y x' x''' t x _48808 h1). Qed.
Lemma lem4318161 {A B : Type'} (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) (_48808 : type621 A B) (h1 : term1434 A B _48808) : term1369 A B _48808 x' x''' t x.
Proof. exact (fun y : B => @lem4318156 A B y x' x''' t x _48808 h1). Qed.
Lemma lem4318166 {A B : Type'} (x''' : B) (t : type1413 A B) (x : A) (_48808 : type621 A B) (h1 : term1434 A B _48808) : term1371 A B _48808 x''' t x.
Proof. exact (fun x' : prod A B => @lem4318161 A B x' x''' t x _48808 h1). Qed.
Lemma lem4318171 {A B : Type'} (t : type1413 A B) (x : A) (_48808 : type621 A B) (h1 : term1434 A B _48808) : term1373 A B _48808 t x.
Proof. exact (fun x''' : B => @lem4318166 A B x''' t x _48808 h1). Qed.
Lemma lem4318176 {A B : Type'} (x : A) (_48808 : type621 A B) (h1 : term1434 A B _48808) : term1375 A B _48808 x.
Proof. exact (fun t : type1413 A B => @lem4318171 A B t x _48808 h1). Qed.
Lemma lem4318181 {A B : Type'} (_48808 : type621 A B) (h1 : term1434 A B _48808) : term1377 A B _48808.
Proof. exact (fun x : A => @lem4318176 A B x _48808 h1). Qed.
Lemma lem4318182 {A B : Type'} (_48808 : type621 A B) : term1436 A B _48808.
Proof. exact (fun h0 : term1434 A B _48808 => @lem4318181 A B _48808 h0). Qed.
Lemma lem4318187 {A B : Type'} : term1438 A B.
Proof. exact (fun _48808 : type621 A B => @lem4318182 A B _48808). Qed.
Lemma lem4318188 {A B : Type'} : term1298 A B.
Proof. exact (EQ_MP (@lem4309634 A B) (@lem4318187 A B)). Qed.
Lemma lem4318189 {A B : Type'} (x : A) : term2098 A B x.
Proof. exact (@lem4318188 A B x). Qed.
Lemma lem4318190 {A B : Type'} (x : A) : (term2098 A B x) = (term1294 A B x).
Proof. exact (eq_refl (term2098 A B x)). Qed.
Lemma lem4318191 {A B : Type'} (x : A) : term1294 A B x.
Proof. exact (EQ_MP (@lem4318190 A B x) (@lem4318189 A B x)). Qed.
Lemma lem4318192 {A B : Type'} (x : A) (t : type1413 A B) : term2099 A B x t.
Proof. exact (@lem4318191 A B x t). Qed.
Lemma lem4318193 {A B : Type'} (t : type1413 A B) (x : A) : (term2099 A B x t) = (term1290 A B t x).
Proof. exact (eq_refl (term2099 A B x t)). Qed.
Lemma lem4318194 {A B : Type'} (t : type1413 A B) (x : A) : term1290 A B t x.
Proof. exact (EQ_MP (@lem4318193 A B t x) (@lem4318192 A B x t)). Qed.
Lemma lem4318195 {A B : Type'} (t : type1413 A B) (x : A) (x''' : B) : term2100 A B t x x'''.
Proof. exact (@lem4318194 A B t x x'''). Qed.
Lemma lem4318196 {A B : Type'} (x''' : B) (t : type1413 A B) (x : A) : (term2100 A B t x x''') = (term1286 A B x''' t x).
Proof. exact (eq_refl (term2100 A B t x x''')). Qed.
Lemma lem4318197 {A B : Type'} (x''' : B) (t : type1413 A B) (x : A) : term1286 A B x''' t x.
Proof. exact (EQ_MP (@lem4318196 A B x''' t x) (@lem4318195 A B t x x''')). Qed.
Lemma lem4318198 {A B : Type'} (x''' : B) (t : type1413 A B) (x : A) (x' : prod A B) : term2101 A B x''' t x x'.
Proof. exact (@lem4318197 A B x''' t x x'). Qed.
Lemma lem4318199 {A B : Type'} (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : (term2101 A B x''' t x x') = (term1282 A B x' x''' t x).
Proof. exact (eq_refl (term2101 A B x''' t x x')). Qed.
Lemma lem4318200 {A B : Type'} (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : term1282 A B x' x''' t x.
Proof. exact (EQ_MP (@lem4318199 A B x' x''' t x) (@lem4318198 A B x''' t x x')). Qed.
Lemma lem4318201 {A B : Type'} (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) (y : B) : term2102 A B x' x''' t x y.
Proof. exact (@lem4318200 A B x' x''' t x y). Qed.
Lemma lem4318202 {A B : Type'} (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : (term2102 A B x' x''' t x y) = (term1278 A B y x' x''' t x).
Proof. exact (eq_refl (term2102 A B x' x''' t x y)). Qed.
Lemma lem4318203 {A B : Type'} (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : term1278 A B y x' x''' t x.
Proof. exact (EQ_MP (@lem4318202 A B y x' x''' t x) (@lem4318201 A B x' x''' t x y)). Qed.
Lemma lem4318204 {A B : Type'} (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) (x'' : A) : term2103 A B y x' x''' t x x''.
Proof. exact (@lem4318203 A B y x' x''' t x x''). Qed.
Lemma lem4318205 {A B : Type'} (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : (term2103 A B y x' x''' t x x'') = (term1274 A B x'' y x' x''' t x).
Proof. exact (eq_refl (term2103 A B y x' x''' t x x'')). Qed.
Lemma lem4318206 {A B : Type'} (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : term1274 A B x'' y x' x''' t x.
Proof. exact (EQ_MP (@lem4318205 A B x'' y x' x''' t x) (@lem4318204 A B y x' x''' t x x'')). Qed.
Lemma lem4318207 {A B : Type'} (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) (s : A -> Prop) : term2104 A B x'' y x' x''' t x s.
Proof. exact (@lem4318206 A B x'' y x' x''' t x s). Qed.
Lemma lem4318208 {A B : Type'} (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : (term2104 A B x'' y x' x''' t x s) = (term1270 A B s x'' y x' x''' t x).
Proof. exact (eq_refl (term2104 A B x'' y x' x''' t x s)). Qed.
Lemma lem4318209 {A B : Type'} (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : term1270 A B s x'' y x' x''' t x.
Proof. exact (EQ_MP (@lem4318208 A B s x'' y x' x''' t x) (@lem4318207 A B x'' y x' x''' t x s)). Qed.
Lemma lem4318210 {A B : Type'} (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) (n : nat) : term2105 A B s x'' y x' x''' t x n.
Proof. exact (@lem4318209 A B s x'' y x' x''' t x n). Qed.
Lemma lem4318211 {A B : Type'} (n : nat) (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : (term2105 A B s x'' y x' x''' t x n) = (term1266 A B n s x'' y x' x''' t x).
Proof. exact (eq_refl (term2105 A B s x'' y x' x''' t x n)). Qed.
Lemma lem4318212 {A B : Type'} (n : nat) (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : term1266 A B n s x'' y x' x''' t x.
Proof. exact (EQ_MP (@lem4318211 A B n s x'' y x' x''' t x) (@lem4318210 A B s x'' y x' x''' t x n)). Qed.
Lemma lem4318213 {A B : Type'} (n : nat) (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) (m : nat) : term2106 A B n s x'' y x' x''' t x m.
Proof. exact (@lem4318212 A B n s x'' y x' x''' t x m). Qed.
Lemma lem4318214 {A B : Type'} (m : nat) (n : nat) (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : (term2106 A B n s x'' y x' x''' t x m) = (term1218 A B m n s x'' y x' x''' t x).
Proof. exact (eq_refl (term2106 A B n s x'' y x' x''' t x m)). Qed.
Lemma lem4318215 {A B : Type'} (m : nat) (n : nat) (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : term1218 A B m n s x'' y x' x''' t x.
Proof. exact (EQ_MP (@lem4318214 A B m n s x'' y x' x''' t x) (@lem4318213 A B n s x'' y x' x''' t x m)). Qed.
Lemma lem4318217 {A B : Type'} (m : nat) (n : nat) (s : A -> Prop) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) : term1218 A B m n s x'' y x' x''' t x.
Proof. exact (@lem4308265 A B m n s x'' y x' x''' t x (@lem4318215 A B m n s x'' y x' x''' t x)). Qed.
Lemma lem4318218 {A B : Type'} (m : nat) (n : nat) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) (s : A -> Prop) (h1 : term808 A x s) : term1260 A B m n s x'' y x' x''' t x.
Proof. exact (@lem4318217 A B m n s x'' y x' x''' t x (@lem4306820 A x s h1)). Qed.
Lemma lem4318219 {A B : Type'} (m : nat) (n : nat) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term808 A x s) : term1258 A B m n s x'' y x' x''' t x.
Proof. exact (@lem4318218 A B m n x'' y x' x''' t x s h2 (@lem4306819 A s h1)). Qed.
Lemma lem4318220 {A B : Type'} (n : nat) (x'' : A) (y : B) (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) (s : A -> Prop) (m : nat) (h1 : @FINITE A s) (h2 : term808 A x s) (h3 : (term822 A s) = m) : term1255 A B n s x'' y x' x''' t x.
Proof. exact (@lem4318219 A B m n x'' y x' x''' t x s h1 h2 (@lem4306822 A s m h3)). Qed.
Lemma lem4318221 {A B : Type'} (x'' : A) (y : B) (x' : prod A B) (x''' : B) (s : A -> Prop) (m : nat) (t : type1413 A B) (x : A) (n : nat) (h1 : @FINITE A s) (h2 : term808 A x s) (h3 : (term822 A s) = m) (h4 : term742 A B t x n) : term1252 A B n s x'' y x' x''' t x.
Proof. exact (@lem4318220 A B n x'' y x' x''' t x s m h1 h2 h3 (@lem4307407 A B t x n h4)). Qed.
Lemma lem4318222 {A B : Type'} (x'' : A) (y : B) (x' : prod A B) (x''' : B) (s : A -> Prop) (m : nat) (t : type1413 A B) (x : A) (n : nat) (h1 : term581 A B s t n) (h2 : @FINITE A s) (h3 : term808 A x s) (h4 : (term822 A s) = m) (h5 : term742 A B t x n) : term1249 A B s x'' y x' x''' t x.
Proof. exact (@lem4318221 A B x'' y x' x''' s m t x n h2 h3 h4 h5 (@lem4307406 A B s t n h1)). Qed.
Lemma lem4318223 {A B : Type'} (x'' : A) (y : B) (x' : prod A B) (x''' : B) (s : A -> Prop) (m : nat) (t : type1413 A B) (x : A) (n : nat) (h1 : term581 A B s t n) (h2 : term1061 A B s) (h3 : @FINITE A s) (h4 : term808 A x s) (h5 : (term822 A s) = m) (h6 : term742 A B t x n) : term1247 A B s x'' y x' x''' t x.
Proof. exact (@lem4318222 A B x'' y x' x''' s m t x n h1 h3 h4 h5 h6 (@lem4307659 A B s h2)). Qed.
Lemma lem4318224 {A B : Type'} (y : B) (x' : prod A B) (x''' : B) (m : nat) (t : type1413 A B) (x : A) (n : nat) (x'' : A) (s : A -> Prop) (h1 : term581 A B s t n) (h2 : term1061 A B s) (h3 : @FINITE A s) (h4 : term808 A x s) (h5 : (term822 A s) = m) (h6 : term742 A B t x n) (h7 : @IN A x'' s) : term1244 A B x'' y x' x''' t x.
Proof. exact (@lem4318223 A B x'' y x' x''' s m t x n h1 h2 h3 h4 h5 h6 (@lem4308240 A x'' s h7)). Qed.
Lemma lem4318225 {A B : Type'} (x' : prod A B) (x''' : B) (m : nat) (x : A) (n : nat) (s : A -> Prop) (y : B) (t : type1413 A B) (x'' : A) (h1 : term581 A B s t n) (h2 : term1061 A B s) (h3 : @FINITE A s) (h4 : term808 A x s) (h5 : (term822 A s) = m) (h6 : term742 A B t x n) (h7 : @IN A x'' s) (h8 : term760 A B y t x'') : term1242 A B x'' y x' x''' t x.
Proof. exact (@lem4318224 A B y x' x''' m t x n x'' s h1 h2 h3 h4 h5 h6 h7 (@lem4308239 A B y t x'' h8)). Qed.
Lemma lem4318226 {A B : Type'} (x''' : B) (m : nat) (x' : prod A B) (x : A) (n : nat) (s : A -> Prop) (y : B) (t : type1413 A B) (x'' : A) (h1 : term581 A B s t n) (h2 : term1061 A B s) (h3 : @FINITE A s) (h4 : term808 A x s) (h5 : (term822 A s) = m) (h6 : x' = (@pair A B x'' y)) (h7 : term742 A B t x n) (h8 : @IN A x'' s) (h9 : term760 A B y t x'') : term1240 A B x' x''' t x.
Proof. exact (@lem4318225 A B x' x''' m x n s y t x'' h1 h2 h3 h4 h5 h7 h8 h9 (@lem4308237 A B x' x'' y h6)). Qed.
Lemma lem4318227 {A B : Type'} (m : nat) (x''' : B) (x' : prod A B) (x : A) (n : nat) (s : A -> Prop) (y : B) (t : type1413 A B) (x'' : A) (h1 : term581 A B s t n) (h2 : term1061 A B s) (h3 : @FINITE A s) (h4 : term808 A x s) (h5 : (term822 A s) = m) (h6 : x' = (@pair A B x x''')) (h7 : x' = (@pair A B x'' y)) (h8 : term742 A B t x n) (h9 : @IN A x'' s) (h10 : term760 A B y t x'') : term1237 A B x''' t x.
Proof. exact (@lem4318226 A B x''' m x' x n s y t x'' h1 h2 h3 h4 h5 h7 h8 h9 h10 (@lem4308243 A B x' x x''' h6)). Qed.
Lemma lem4318228 {A B : Type'} (m : nat) (x' : prod A B) (n : nat) (s : A -> Prop) (x''' : B) (x : A) (y : B) (t : type1413 A B) (x'' : A) (h1 : term581 A B s t n) (h2 : term1061 A B s) (h3 : @FINITE A s) (h4 : term808 A x s) (h5 : (term822 A s) = m) (h6 : x' = (@pair A B x x''')) (h7 : x' = (@pair A B x'' y)) (h8 : term742 A B t x n) (h9 : @IN A x'' s) (h10 : term760 A B x''' t x) (h11 : term760 A B y t x'') : term1234 A B.
Proof. exact (@lem4318227 A B m x''' x' x n s y t x'' h1 h2 h3 h4 h5 h6 h7 h8 h9 h11 (@lem4308242 A B x''' t x h10)). Qed.
Lemma lem4318229 {A B : Type'} (m : nat) (x' : prod A B) (n : nat) (s : A -> Prop) (x''' : B) (x : A) (y : B) (t : type1413 A B) (x'' : A) (h1 : term581 A B s t n) (h2 : term1061 A B s) (h3 : @FINITE A s) (h4 : term808 A x s) (h5 : (term822 A s) = m) (h6 : x' = (@pair A B x x''')) (h7 : x' = (@pair A B x'' y)) (h8 : term742 A B t x n) (h9 : @IN A x'' s) (h10 : term760 A B x''' t x) (h11 : term760 A B y t x'') : term1231 A B.
Proof. exact (@lem4318228 A B m x' n s x''' x y t x'' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 (@lem4308244 A B)). Qed.
Lemma lem4318230 {A B : Type'} (m : nat) (x' : prod A B) (n : nat) (s : A -> Prop) (x''' : B) (x : A) (y : B) (t : type1413 A B) (x'' : A) (h1 : term581 A B s t n) (h2 : term1061 A B s) (h3 : @FINITE A s) (h4 : term808 A x s) (h5 : (term822 A s) = m) (h6 : x' = (@pair A B x x''')) (h7 : x' = (@pair A B x'' y)) (h8 : term742 A B t x n) (h9 : @IN A x'' s) (h10 : term760 A B x''' t x) (h11 : term760 A B y t x'') : term1228 A B.
Proof. exact (@lem4318229 A B m x' n s x''' x y t x'' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 (@lem4308248 A)). Qed.
Lemma lem4318231 {A B : Type'} (m : nat) (x' : prod A B) (n : nat) (s : A -> Prop) (x''' : B) (x : A) (y : B) (t : type1413 A B) (x'' : A) (h1 : term581 A B s t n) (h2 : term1061 A B s) (h3 : @FINITE A s) (h4 : term808 A x s) (h5 : (term822 A s) = m) (h6 : x' = (@pair A B x x''')) (h7 : x' = (@pair A B x'' y)) (h8 : term742 A B t x n) (h9 : @IN A x'' s) (h10 : term760 A B x''' t x) (h11 : term760 A B y t x'') : term1225 A B.
Proof. exact (@lem4318230 A B m x' n s x''' x y t x'' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 (@lem4308249 A B)). Qed.
Lemma lem4318232 {A B : Type'} (m : nat) (x' : prod A B) (n : nat) (s : A -> Prop) (x''' : B) (x : A) (y : B) (t : type1413 A B) (x'' : A) (h1 : term581 A B s t n) (h2 : term1061 A B s) (h3 : @FINITE A s) (h4 : term808 A x s) (h5 : (term822 A s) = m) (h6 : x' = (@pair A B x x''')) (h7 : x' = (@pair A B x'' y)) (h8 : term742 A B t x n) (h9 : @IN A x'' s) (h10 : term760 A B x''' t x) (h11 : term760 A B y t x'') : term1222 A B.
Proof. exact (@lem4318231 A B m x' n s x''' x y t x'' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 (@lem4308246 B)). Qed.
Lemma lem4318233 {A B : Type'} (m : nat) (x' : prod A B) (n : nat) (s : A -> Prop) (x''' : B) (x : A) (y : B) (t : type1413 A B) (x'' : A) (h1 : term581 A B s t n) (h2 : term1061 A B s) (h3 : @FINITE A s) (h4 : term808 A x s) (h5 : (term822 A s) = m) (h6 : x' = (@pair A B x x''')) (h7 : x' = (@pair A B x'' y)) (h8 : term742 A B t x n) (h9 : @IN A x'' s) (h10 : term760 A B x''' t x) (h11 : term760 A B y t x'') : False.
Proof. exact (@lem4318232 A B m x' n s x''' x y t x'' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 (@lem4308247 A B)). Qed.
Lemma lem4318234 {A B : Type'} (s : A -> Prop) (x' : prod A B) (t : type1413 A B) (x : A) (h1 : term1206 A B s x' t x) : term1205 A B x' t x.
Proof. exact (proj2 (@lem4308232 A B s x' t x h1)). Qed.
Lemma lem4318235 {A B : Type'} (s : A -> Prop) (x' : prod A B) (t : type1413 A B) (x : A) (h1 : term1206 A B s x' t x) : term1192 A B s t x'.
Proof. exact (proj1 (@lem4308232 A B s x' t x h1)). Qed.
Lemma lem4318236 {A B : Type'} (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) (h1 : term1202 A B x' x''' t x) : term760 A B x''' t x.
Proof. exact (proj2 (@lem4308241 A B x' x''' t x h1)). Qed.
Lemma lem4318237 {A B : Type'} (x' : prod A B) (x''' : B) (t : type1413 A B) (x : A) (h1 : term1202 A B x' x''' t x) : x' = (@pair A B x x''').
Proof. exact (proj1 (@lem4308241 A B x' x''' t x h1)). Qed.
Lemma lem4318238 {A B : Type'} (m : nat) (x' : prod A B) (n : nat) (s : A -> Prop) (x''' : B) (x : A) (y : B) (t : type1413 A B) (x'' : A) (h1 : term581 A B s t n) (h2 : term1061 A B s) (h3 : @FINITE A s) (h4 : term808 A x s) (h5 : (term822 A s) = m) (h6 : x' = (@pair A B x x''')) (h7 : x' = (@pair A B x'' y)) (h8 : term742 A B t x n) (h9 : @IN A x'' s) (h10 : term760 A B x''' t x) (h11 : term760 A B y t x'') : (term760 A B x''' t x) = False.
Proof. exact (prop_ext (fun h12 : term760 A B x''' t x => @lem4318233 A B m x' n s x''' x y t x'' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11) (fun h12 : False => @lem4308242 A B x''' t x h10)). Qed.
Lemma lem4318239 {A B : Type'} (m : nat) (x' : prod A B) (n : nat) (s : A -> Prop) (x''' : B) (x : A) (y : B) (t : type1413 A B) (x'' : A) (h1 : term581 A B s t n) (h2 : term1061 A B s) (h3 : @FINITE A s) (h4 : term808 A x s) (h5 : (term822 A s) = m) (h6 : x' = (@pair A B x x''')) (h7 : x' = (@pair A B x'' y)) (h8 : term742 A B t x n) (h9 : @IN A x'' s) (h10 : term760 A B x''' t x) (h11 : term760 A B y t x'') : False.
Proof. exact (EQ_MP (@lem4318238 A B m x' n s x''' x y t x'' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11) (@lem4308242 A B x''' t x h10)). Qed.
Lemma lem4318240 {A B : Type'} (m : nat) (x' : prod A B) (n : nat) (s : A -> Prop) (x''' : B) (x : A) (y : B) (t : type1413 A B) (x'' : A) (h1 : term581 A B s t n) (h2 : term1061 A B s) (h3 : @FINITE A s) (h4 : term808 A x s) (h5 : (term822 A s) = m) (h6 : x' = (@pair A B x x''')) (h7 : x' = (@pair A B x'' y)) (h8 : term742 A B t x n) (h9 : @IN A x'' s) (h10 : term760 A B x''' t x) (h11 : term760 A B y t x'') : (x' = (@pair A B x x''')) = False.
Proof. exact (prop_ext (fun h12 : x' = (@pair A B x x''') => @lem4318239 A B m x' n s x''' x y t x'' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11) (fun h12 : False => @lem4308243 A B x' x x''' h6)). Qed.
Lemma lem4318241 {A B : Type'} (m : nat) (x' : prod A B) (n : nat) (s : A -> Prop) (x''' : B) (x : A) (y : B) (t : type1413 A B) (x'' : A) (h1 : term581 A B s t n) (h2 : term1061 A B s) (h3 : @FINITE A s) (h4 : term808 A x s) (h5 : (term822 A s) = m) (h6 : x' = (@pair A B x x''')) (h7 : x' = (@pair A B x'' y)) (h8 : term742 A B t x n) (h9 : @IN A x'' s) (h10 : term760 A B x''' t x) (h11 : term760 A B y t x'') : False.
Proof. exact (EQ_MP (@lem4318240 A B m x' n s x''' x y t x'' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11) (@lem4308243 A B x' x x''' h6)). Qed.
Lemma lem4318242 {A B : Type'} (m : nat) (x''' : B) (x' : prod A B) (x : A) (n : nat) (s : A -> Prop) (y : B) (t : type1413 A B) (x'' : A) (h1 : term581 A B s t n) (h2 : term1061 A B s) (h3 : @FINITE A s) (h4 : term808 A x s) (h5 : term1202 A B x' x''' t x) (h6 : (term822 A s) = m) (h7 : x' = (@pair A B x x''')) (h8 : x' = (@pair A B x'' y)) (h9 : term742 A B t x n) (h10 : @IN A x'' s) (h11 : term760 A B y t x'') : (term760 A B x''' t x) = False.
Proof. exact (prop_ext (fun h12 : term760 A B x''' t x => @lem4318241 A B m x' n s x''' x y t x'' h1 h2 h3 h4 h6 h7 h8 h9 h10 h12 h11) (fun h12 : False => @lem4318236 A B x' x''' t x h5)). Qed.
Lemma lem4318243 {A B : Type'} (m : nat) (x''' : B) (x' : prod A B) (x : A) (n : nat) (s : A -> Prop) (y : B) (t : type1413 A B) (x'' : A) (h1 : term581 A B s t n) (h2 : term1061 A B s) (h3 : @FINITE A s) (h4 : term808 A x s) (h5 : term1202 A B x' x''' t x) (h6 : (term822 A s) = m) (h7 : x' = (@pair A B x x''')) (h8 : x' = (@pair A B x'' y)) (h9 : term742 A B t x n) (h10 : @IN A x'' s) (h11 : term760 A B y t x'') : False.
Proof. exact (EQ_MP (@lem4318242 A B m x''' x' x n s y t x'' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11) (@lem4318236 A B x' x''' t x h5)). Qed.
Lemma lem4318244 {A B : Type'} (x''' : B) (m : nat) (x' : prod A B) (x : A) (n : nat) (s : A -> Prop) (y : B) (t : type1413 A B) (x'' : A) (h1 : term581 A B s t n) (h2 : term1061 A B s) (h3 : @FINITE A s) (h4 : term808 A x s) (h5 : term1202 A B x' x''' t x) (h6 : (term822 A s) = m) (h7 : x' = (@pair A B x'' y)) (h8 : term742 A B t x n) (h9 : @IN A x'' s) (h10 : term760 A B y t x'') : (x' = (@pair A B x x''')) = False.
Proof. exact (prop_ext (fun h11 : x' = (@pair A B x x''') => @lem4318243 A B m x''' x' x n s y t x'' h1 h2 h3 h4 h5 h6 h11 h7 h8 h9 h10) (fun h11 : False => @lem4318237 A B x' x''' t x h5)). Qed.
Lemma lem4318245 {A B : Type'} (x''' : B) (m : nat) (x' : prod A B) (x : A) (n : nat) (s : A -> Prop) (y : B) (t : type1413 A B) (x'' : A) (h1 : term581 A B s t n) (h2 : term1061 A B s) (h3 : @FINITE A s) (h4 : term808 A x s) (h5 : term1202 A B x' x''' t x) (h6 : (term822 A s) = m) (h7 : x' = (@pair A B x'' y)) (h8 : term742 A B t x n) (h9 : @IN A x'' s) (h10 : term760 A B y t x'') : False.
Proof. exact (EQ_MP (@lem4318244 A B x''' m x' x n s y t x'' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10) (@lem4318237 A B x' x''' t x h5)). Qed.
Lemma lem4318246 {A B : Type'} (m : nat) (x' : prod A B) (x : A) (n : nat) (s : A -> Prop) (y : B) (t : type1413 A B) (x'' : A) (h1 : term581 A B s t n) (h2 : term1061 A B s) (h3 : term1205 A B x' t x) (h4 : @FINITE A s) (h5 : term808 A x s) (h6 : (term822 A s) = m) (h7 : x' = (@pair A B x'' y)) (h8 : term742 A B t x n) (h9 : @IN A x'' s) (h10 : term760 A B y t x'') : False.
Proof. exact (ex_elim (@lem4308233 A B x' t x h3) (fun x''' : B => fun h0 : term1204 A B x' t x x''' => @lem4318245 A B x''' m x' x n s y t x'' h1 h2 h4 h5 h0 h6 h7 h8 h9 h10)). Qed.
Lemma lem4318247 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x' : prod A B) (x'' : A) (y : B) (h1 : term1185 A B s t x' x'' y) : x' = (@pair A B x'' y).
Proof. exact (proj2 (@lem4308236 A B s t x' x'' y h1)). Qed.
Lemma lem4318248 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x' : prod A B) (x'' : A) (y : B) (h1 : term1185 A B s t x' x'' y) : term1173 A B s y t x''.
Proof. exact (proj1 (@lem4308236 A B s t x' x'' y h1)). Qed.
Lemma lem4318249 {A B : Type'} (m : nat) (x' : prod A B) (x : A) (n : nat) (s : A -> Prop) (y : B) (t : type1413 A B) (x'' : A) (h1 : term581 A B s t n) (h2 : term1061 A B s) (h3 : term1205 A B x' t x) (h4 : @FINITE A s) (h5 : term808 A x s) (h6 : (term822 A s) = m) (h7 : x' = (@pair A B x'' y)) (h8 : term742 A B t x n) (h9 : @IN A x'' s) (h10 : term760 A B y t x'') : (x' = (@pair A B x'' y)) = False.
Proof. exact (prop_ext (fun h11 : x' = (@pair A B x'' y) => @lem4318246 A B m x' x n s y t x'' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10) (fun h11 : False => @lem4308237 A B x' x'' y h7)). Qed.
Lemma lem4318250 {A B : Type'} (m : nat) (x' : prod A B) (x : A) (n : nat) (s : A -> Prop) (y : B) (t : type1413 A B) (x'' : A) (h1 : term581 A B s t n) (h2 : term1061 A B s) (h3 : term1205 A B x' t x) (h4 : @FINITE A s) (h5 : term808 A x s) (h6 : (term822 A s) = m) (h7 : x' = (@pair A B x'' y)) (h8 : term742 A B t x n) (h9 : @IN A x'' s) (h10 : term760 A B y t x'') : False.
Proof. exact (EQ_MP (@lem4318249 A B m x' x n s y t x'' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10) (@lem4308237 A B x' x'' y h7)). Qed.
Lemma lem4318251 {A B : Type'} (s : A -> Prop) (y : B) (t : type1413 A B) (x'' : A) (h1 : term1173 A B s y t x'') : term760 A B y t x''.
Proof. exact (proj2 (@lem4308238 A B s y t x'' h1)). Qed.
Lemma lem4318252 {A B : Type'} (s : A -> Prop) (y : B) (t : type1413 A B) (x'' : A) (h1 : term1173 A B s y t x'') : @IN A x'' s.
Proof. exact (proj1 (@lem4308238 A B s y t x'' h1)). Qed.
Lemma lem4318253 {A B : Type'} (m : nat) (x' : prod A B) (x : A) (n : nat) (s : A -> Prop) (y : B) (t : type1413 A B) (x'' : A) (h1 : term581 A B s t n) (h2 : term1061 A B s) (h3 : term1205 A B x' t x) (h4 : @FINITE A s) (h5 : term808 A x s) (h6 : (term822 A s) = m) (h7 : x' = (@pair A B x'' y)) (h8 : term742 A B t x n) (h9 : @IN A x'' s) (h10 : term760 A B y t x'') : (term760 A B y t x'') = False.
Proof. exact (prop_ext (fun h11 : term760 A B y t x'' => @lem4318250 A B m x' x n s y t x'' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10) (fun h11 : False => @lem4308239 A B y t x'' h10)). Qed.
Lemma lem4318254 {A B : Type'} (m : nat) (x' : prod A B) (x : A) (n : nat) (s : A -> Prop) (y : B) (t : type1413 A B) (x'' : A) (h1 : term581 A B s t n) (h2 : term1061 A B s) (h3 : term1205 A B x' t x) (h4 : @FINITE A s) (h5 : term808 A x s) (h6 : (term822 A s) = m) (h7 : x' = (@pair A B x'' y)) (h8 : term742 A B t x n) (h9 : @IN A x'' s) (h10 : term760 A B y t x'') : False.
Proof. exact (EQ_MP (@lem4318253 A B m x' x n s y t x'' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10) (@lem4308239 A B y t x'' h10)). Qed.
Lemma lem4318255 {A B : Type'} (m : nat) (x' : prod A B) (x : A) (n : nat) (s : A -> Prop) (y : B) (t : type1413 A B) (x'' : A) (h1 : term581 A B s t n) (h2 : term1061 A B s) (h3 : term1205 A B x' t x) (h4 : @FINITE A s) (h5 : term808 A x s) (h6 : (term822 A s) = m) (h7 : x' = (@pair A B x'' y)) (h8 : term742 A B t x n) (h9 : @IN A x'' s) (h10 : term760 A B y t x'') : (@IN A x'' s) = False.
Proof. exact (prop_ext (fun h11 : @IN A x'' s => @lem4318254 A B m x' x n s y t x'' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10) (fun h11 : False => @lem4308240 A x'' s h9)). Qed.
Lemma lem4318256 {A B : Type'} (m : nat) (x' : prod A B) (x : A) (n : nat) (s : A -> Prop) (y : B) (t : type1413 A B) (x'' : A) (h1 : term581 A B s t n) (h2 : term1061 A B s) (h3 : term1205 A B x' t x) (h4 : @FINITE A s) (h5 : term808 A x s) (h6 : (term822 A s) = m) (h7 : x' = (@pair A B x'' y)) (h8 : term742 A B t x n) (h9 : @IN A x'' s) (h10 : term760 A B y t x'') : False.
Proof. exact (EQ_MP (@lem4318255 A B m x' x n s y t x'' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10) (@lem4308240 A x'' s h9)). Qed.
Lemma lem4318257 {A B : Type'} (m : nat) (x' : prod A B) (y : B) (t : type1413 A B) (x : A) (n : nat) (x'' : A) (s : A -> Prop) (h1 : term581 A B s t n) (h2 : term1061 A B s) (h3 : term1205 A B x' t x) (h4 : @FINITE A s) (h5 : term808 A x s) (h6 : term1173 A B s y t x'') (h7 : (term822 A s) = m) (h8 : x' = (@pair A B x'' y)) (h9 : term742 A B t x n) (h10 : @IN A x'' s) : (term760 A B y t x'') = False.
Proof. exact (prop_ext (fun h11 : term760 A B y t x'' => @lem4318256 A B m x' x n s y t x'' h1 h2 h3 h4 h5 h7 h8 h9 h10 h11) (fun h11 : False => @lem4318251 A B s y t x'' h6)). Qed.
Lemma lem4318258 {A B : Type'} (m : nat) (x' : prod A B) (y : B) (t : type1413 A B) (x : A) (n : nat) (x'' : A) (s : A -> Prop) (h1 : term581 A B s t n) (h2 : term1061 A B s) (h3 : term1205 A B x' t x) (h4 : @FINITE A s) (h5 : term808 A x s) (h6 : term1173 A B s y t x'') (h7 : (term822 A s) = m) (h8 : x' = (@pair A B x'' y)) (h9 : term742 A B t x n) (h10 : @IN A x'' s) : False.
Proof. exact (EQ_MP (@lem4318257 A B m x' y t x n x'' s h1 h2 h3 h4 h5 h6 h7 h8 h9 h10) (@lem4318251 A B s y t x'' h6)). Qed.
Lemma lem4318259 {A B : Type'} (s : A -> Prop) (m : nat) (x' : prod A B) (x'' : A) (y : B) (t : type1413 A B) (x : A) (n : nat) (h1 : term581 A B s t n) (h2 : term1061 A B s) (h3 : term1205 A B x' t x) (h4 : @FINITE A s) (h5 : term808 A x s) (h6 : term1173 A B s y t x'') (h7 : (term822 A s) = m) (h8 : x' = (@pair A B x'' y)) (h9 : term742 A B t x n) : (@IN A x'' s) = False.
Proof. exact (prop_ext (fun h10 : @IN A x'' s => @lem4318258 A B m x' y t x n x'' s h1 h2 h3 h4 h5 h6 h7 h8 h9 h10) (fun h10 : False => @lem4318252 A B s y t x'' h6)). Qed.
Lemma lem4318260 {A B : Type'} (s : A -> Prop) (m : nat) (x' : prod A B) (x'' : A) (y : B) (t : type1413 A B) (x : A) (n : nat) (h1 : term581 A B s t n) (h2 : term1061 A B s) (h3 : term1205 A B x' t x) (h4 : @FINITE A s) (h5 : term808 A x s) (h6 : term1173 A B s y t x'') (h7 : (term822 A s) = m) (h8 : x' = (@pair A B x'' y)) (h9 : term742 A B t x n) : False.
Proof. exact (EQ_MP (@lem4318259 A B s m x' x'' y t x n h1 h2 h3 h4 h5 h6 h7 h8 h9) (@lem4318252 A B s y t x'' h6)). Qed.
Lemma lem4318261 {A B : Type'} (x' : prod A B) (y : B) (x'' : A) (s : A -> Prop) (m : nat) (t : type1413 A B) (x : A) (n : nat) (h1 : term581 A B s t n) (h2 : term1061 A B s) (h3 : term1205 A B x' t x) (h4 : @FINITE A s) (h5 : term808 A x s) (h6 : term1185 A B s t x' x'' y) (h7 : term1173 A B s y t x'') (h8 : (term822 A s) = m) (h9 : term742 A B t x n) : (x' = (@pair A B x'' y)) = False.
Proof. exact (prop_ext (fun h10 : x' = (@pair A B x'' y) => @lem4318260 A B s m x' x'' y t x n h1 h2 h3 h4 h5 h7 h8 h10 h9) (fun h10 : False => @lem4318247 A B s t x' x'' y h6)). Qed.
Lemma lem4318262 {A B : Type'} (x' : prod A B) (y : B) (x'' : A) (s : A -> Prop) (m : nat) (t : type1413 A B) (x : A) (n : nat) (h1 : term581 A B s t n) (h2 : term1061 A B s) (h3 : term1205 A B x' t x) (h4 : @FINITE A s) (h5 : term808 A x s) (h6 : term1185 A B s t x' x'' y) (h7 : term1173 A B s y t x'') (h8 : (term822 A s) = m) (h9 : term742 A B t x n) : False.
Proof. exact (EQ_MP (@lem4318261 A B x' y x'' s m t x n h1 h2 h3 h4 h5 h6 h7 h8 h9) (@lem4318247 A B s t x' x'' y h6)). Qed.
Lemma lem4318263 {A B : Type'} (x' : prod A B) (x'' : A) (y : B) (s : A -> Prop) (m : nat) (t : type1413 A B) (x : A) (n : nat) (h1 : term581 A B s t n) (h2 : term1061 A B s) (h3 : term1205 A B x' t x) (h4 : @FINITE A s) (h5 : term808 A x s) (h6 : term1185 A B s t x' x'' y) (h7 : (term822 A s) = m) (h8 : term742 A B t x n) : (term1173 A B s y t x'') = False.
Proof. exact (prop_ext (fun h9 : term1173 A B s y t x'' => @lem4318262 A B x' y x'' s m t x n h1 h2 h3 h4 h5 h6 h9 h7 h8) (fun h9 : False => @lem4318248 A B s t x' x'' y h6)). Qed.
Lemma lem4318264 {A B : Type'} (x' : prod A B) (x'' : A) (y : B) (s : A -> Prop) (m : nat) (t : type1413 A B) (x : A) (n : nat) (h1 : term581 A B s t n) (h2 : term1061 A B s) (h3 : term1205 A B x' t x) (h4 : @FINITE A s) (h5 : term808 A x s) (h6 : term1185 A B s t x' x'' y) (h7 : (term822 A s) = m) (h8 : term742 A B t x n) : False.
Proof. exact (EQ_MP (@lem4318263 A B x' x'' y s m t x n h1 h2 h3 h4 h5 h6 h7 h8) (@lem4318248 A B s t x' x'' y h6)). Qed.
Lemma lem4318265 {A B : Type'} (x'' : A) (x' : prod A B) (s : A -> Prop) (m : nat) (t : type1413 A B) (x : A) (n : nat) (h1 : term581 A B s t n) (h2 : term1061 A B s) (h3 : term1189 A B s t x' x'') (h4 : term1205 A B x' t x) (h5 : @FINITE A s) (h6 : term808 A x s) (h7 : (term822 A s) = m) (h8 : term742 A B t x n) : False.
Proof. exact (ex_elim (@lem4308235 A B s t x' x'' h3) (fun y : B => fun h0 : term1187 A B s t x' x'' y => @lem4318264 A B x' x'' y s m t x n h1 h2 h4 h5 h6 h0 h7 h8)). Qed.
Lemma lem4318266 {A B : Type'} (x' : prod A B) (s : A -> Prop) (m : nat) (t : type1413 A B) (x : A) (n : nat) (h1 : term581 A B s t n) (h2 : term1061 A B s) (h3 : term1192 A B s t x') (h4 : term1205 A B x' t x) (h5 : @FINITE A s) (h6 : term808 A x s) (h7 : (term822 A s) = m) (h8 : term742 A B t x n) : False.
Proof. exact (ex_elim (@lem4308234 A B s t x' h3) (fun x'' : A => fun h0 : term1191 A B s t x' x'' => @lem4318265 A B x'' x' s m t x n h1 h2 h0 h4 h5 h6 h7 h8)). Qed.
Lemma lem4318267 {A B : Type'} (x' : prod A B) (s : A -> Prop) (m : nat) (t : type1413 A B) (x : A) (n : nat) (h1 : term581 A B s t n) (h2 : term1061 A B s) (h3 : term1192 A B s t x') (h4 : @FINITE A s) (h5 : term808 A x s) (h6 : term1206 A B s x' t x) (h7 : (term822 A s) = m) (h8 : term742 A B t x n) : (term1205 A B x' t x) = False.
Proof. exact (prop_ext (fun h9 : term1205 A B x' t x => @lem4318266 A B x' s m t x n h1 h2 h3 h9 h4 h5 h7 h8) (fun h9 : False => @lem4318234 A B s x' t x h6)). Qed.
Lemma lem4318268 {A B : Type'} (x' : prod A B) (s : A -> Prop) (m : nat) (t : type1413 A B) (x : A) (n : nat) (h1 : term581 A B s t n) (h2 : term1061 A B s) (h3 : term1192 A B s t x') (h4 : @FINITE A s) (h5 : term808 A x s) (h6 : term1206 A B s x' t x) (h7 : (term822 A s) = m) (h8 : term742 A B t x n) : False.
Proof. exact (EQ_MP (@lem4318267 A B x' s m t x n h1 h2 h3 h4 h5 h6 h7 h8) (@lem4318234 A B s x' t x h6)). Qed.
Lemma lem4318269 {A B : Type'} (x' : prod A B) (s : A -> Prop) (m : nat) (t : type1413 A B) (x : A) (n : nat) (h1 : term581 A B s t n) (h2 : term1061 A B s) (h3 : @FINITE A s) (h4 : term808 A x s) (h5 : term1206 A B s x' t x) (h6 : (term822 A s) = m) (h7 : term742 A B t x n) : (term1192 A B s t x') = False.
Proof. exact (prop_ext (fun h8 : term1192 A B s t x' => @lem4318268 A B x' s m t x n h1 h2 h8 h3 h4 h5 h6 h7) (fun h8 : False => @lem4318235 A B s x' t x h5)). Qed.
Lemma lem4318270 {A B : Type'} (x' : prod A B) (s : A -> Prop) (m : nat) (t : type1413 A B) (x : A) (n : nat) (h1 : term581 A B s t n) (h2 : term1061 A B s) (h3 : @FINITE A s) (h4 : term808 A x s) (h5 : term1206 A B s x' t x) (h6 : (term822 A s) = m) (h7 : term742 A B t x n) : False.
Proof. exact (EQ_MP (@lem4318269 A B x' s m t x n h1 h2 h3 h4 h5 h6 h7) (@lem4318235 A B s x' t x h5)). Qed.
Lemma lem4318271 {A B : Type'} (x' : prod A B) (s : A -> Prop) (m : nat) (t : type1413 A B) (x : A) (n : nat) (h1 : term581 A B s t n) (h2 : term1061 A B s) (h3 : @FINITE A s) (h4 : term808 A x s) (h5 : (term822 A s) = m) (h6 : term742 A B t x n) : term2107 A B s x' t x.
Proof. exact (fun h0 : term1206 A B s x' t x => @lem4318270 A B x' s m t x n h1 h2 h3 h4 h0 h5 h6). Qed.
Lemma lem4318272 {A B : Type'} (s : A -> Prop) (x' : prod A B) (t : type1413 A B) (x : A) : (term2107 A B s x' t x) = (term1209 A B s x' t x).
Proof. exact (@lem69 (term1206 A B s x' t x)). Qed.
Lemma lem4318273 {A B : Type'} (x' : prod A B) (s : A -> Prop) (m : nat) (t : type1413 A B) (x : A) (n : nat) (h1 : term581 A B s t n) (h2 : term1061 A B s) (h3 : @FINITE A s) (h4 : term808 A x s) (h5 : (term822 A s) = m) (h6 : term742 A B t x n) : term1209 A B s x' t x.
Proof. exact (EQ_MP (@lem4318272 A B s x' t x) (@lem4318271 A B x' s m t x n h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem4318278 {A B : Type'} (s : A -> Prop) (m : nat) (t : type1413 A B) (x : A) (n : nat) (h1 : term581 A B s t n) (h2 : term1061 A B s) (h3 : @FINITE A s) (h4 : term808 A x s) (h5 : (term822 A s) = m) (h6 : term742 A B t x n) : term1212 A B s t x.
Proof. exact (fun x' : prod A B => @lem4318273 A B x' s m t x n h1 h2 h3 h4 h5 h6). Qed.
Lemma lem4318279 {A B : Type'} (s : A -> Prop) (m : nat) (t : type1413 A B) (x : A) (n : nat) (h1 : term581 A B s t n) (h2 : term1061 A B s) (h3 : @FINITE A s) (h4 : term808 A x s) (h5 : (term822 A s) = m) (h6 : term742 A B t x n) : term1149 A B s t x.
Proof. exact (EQ_MP (@lem4308231 A B s t x) (@lem4318278 A B s m t x n h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem4318280 {A B : Type'} (s : A -> Prop) (m : nat) (t : type1413 A B) (x : A) (n : nat) (h1 : term581 A B s t n) (h2 : term1061 A B s) (h3 : @FINITE A s) (h4 : term808 A x s) (h5 : (term822 A s) = m) (h6 : term742 A B t x n) : term1152 A B n s t x.
Proof. exact (EQ_MP (@lem4308005 A B s t x n h1 h2 h6) (@lem4318279 A B s m t x n h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem4318281 {A B : Type'} (s : A -> Prop) (m : nat) (t : type1413 A B) (x : A) (n : nat) (h1 : term581 A B s t n) (h2 : term1061 A B s) (h3 : @FINITE A s) (h4 : term808 A x s) (h5 : (term822 A s) = m) (h6 : term742 A B t x n) : term1072 A B t x s n.
Proof. exact (@lem4307682 A B t x s n (@lem4318280 A B s m t x n h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem4318282 {A B : Type'} (s : A -> Prop) (m : nat) (t : type1413 A B) (x : A) (n : nat) (h1 : term581 A B s t n) (h2 : term1061 A B s) (h3 : @FINITE A s) (h4 : term808 A x s) (h5 : (term822 A s) = m) (h6 : term742 A B t x n) : term1067 A B x t s n.
Proof. exact (EQ_MP (@lem4307678 A B x t s n) (@lem4318281 A B s m t x n h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem4318283 {A B : Type'} (s : A -> Prop) (m : nat) (t : type1413 A B) (x : A) (n : nat) (h1 : term581 A B s t n) (h2 : @FINITE A s) (h3 : term808 A x s) (h4 : (term822 A s) = m) (h5 : term742 A B t x n) : term1069 A B x t s n.
Proof. exact (fun h0 : term1061 A B s => @lem4318282 A B s m t x n h1 h0 h2 h3 h4 h5). Qed.
Lemma lem4318284 {A B : Type'} (s : A -> Prop) (m : nat) (t : type1413 A B) (x : A) (n : nat) (h1 : term581 A B s t n) (h2 : @FINITE A s) (h3 : term808 A x s) (h4 : (term822 A s) = m) (h5 : term742 A B t x n) : term1068 A B x s t m n.
Proof. exact (EQ_MP (@lem4307658 A B x t n s m h4) (@lem4318283 A B s m t x n h1 h2 h3 h4 h5)). Qed.
Lemma lem4318285 {A B : Type'} (s : A -> Prop) (m : nat) (t : type1413 A B) (x : A) (n : nat) (h1 : term581 A B s t n) (h2 : term683 A B s) (h3 : @FINITE A s) (h4 : term808 A x s) (h5 : (term822 A s) = m) (h6 : term742 A B t x n) : term885 A B x s t m n.
Proof. exact (@lem4318284 A B s m t x n h1 h3 h4 h5 h6 (@lem4307410 A B s h2)). Qed.
Lemma lem4318286 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term1041 A B x s t n) : term581 A B s t n.
Proof. exact (proj2 (@lem4307405 A B x s t n h1)). Qed.
Lemma lem4318287 {A B : Type'} (x : A) (s : A -> Prop) (t : type1413 A B) (n : nat) (h1 : term1041 A B x s t n) : term742 A B t x n.
Proof. exact (proj1 (@lem4307405 A B x s t n h1)). Qed.
Lemma lem4318288 {A B : Type'} (s : A -> Prop) (m : nat) (t : type1413 A B) (x : A) (n : nat) (h1 : term581 A B s t n) (h2 : term683 A B s) (h3 : @FINITE A s) (h4 : term808 A x s) (h5 : (term822 A s) = m) (h6 : term742 A B t x n) : (term581 A B s t n) = (term885 A B x s t m n).
Proof. exact (prop_ext (fun h7 : term581 A B s t n => @lem4318285 A B s m t x n h1 h2 h3 h4 h5 h6) (fun h7 : term885 A B x s t m n => @lem4307406 A B s t n h1)). Qed.
Lemma lem4318289 {A B : Type'} (s : A -> Prop) (m : nat) (t : type1413 A B) (x : A) (n : nat) (h1 : term581 A B s t n) (h2 : term683 A B s) (h3 : @FINITE A s) (h4 : term808 A x s) (h5 : (term822 A s) = m) (h6 : term742 A B t x n) : term885 A B x s t m n.
Proof. exact (EQ_MP (@lem4318288 A B s m t x n h1 h2 h3 h4 h5 h6) (@lem4307406 A B s t n h1)). Qed.
Lemma lem4318290 {A B : Type'} (s : A -> Prop) (m : nat) (t : type1413 A B) (x : A) (n : nat) (h1 : term581 A B s t n) (h2 : term683 A B s) (h3 : @FINITE A s) (h4 : term808 A x s) (h5 : (term822 A s) = m) (h6 : term742 A B t x n) : (term742 A B t x n) = (term885 A B x s t m n).
Proof. exact (prop_ext (fun h7 : term742 A B t x n => @lem4318289 A B s m t x n h1 h2 h3 h4 h5 h6) (fun h7 : term885 A B x s t m n => @lem4307407 A B t x n h6)). Qed.
Lemma lem4318291 {A B : Type'} (s : A -> Prop) (m : nat) (t : type1413 A B) (x : A) (n : nat) (h1 : term581 A B s t n) (h2 : term683 A B s) (h3 : @FINITE A s) (h4 : term808 A x s) (h5 : (term822 A s) = m) (h6 : term742 A B t x n) : term885 A B x s t m n.
Proof. exact (EQ_MP (@lem4318290 A B s m t x n h1 h2 h3 h4 h5 h6) (@lem4307407 A B t x n h6)). Qed.
Lemma lem4318292 {A B : Type'} (s : A -> Prop) (m : nat) (t : type1413 A B) (x : A) (n : nat) (h1 : term683 A B s) (h2 : @FINITE A s) (h3 : term808 A x s) (h4 : term1041 A B x s t n) (h5 : (term822 A s) = m) (h6 : term742 A B t x n) : (term581 A B s t n) = (term885 A B x s t m n).
Proof. exact (prop_ext (fun h7 : term581 A B s t n => @lem4318291 A B s m t x n h7 h1 h2 h3 h5 h6) (fun h7 : term885 A B x s t m n => @lem4318286 A B x s t n h4)). Qed.
Lemma lem4318293 {A B : Type'} (s : A -> Prop) (m : nat) (t : type1413 A B) (x : A) (n : nat) (h1 : term683 A B s) (h2 : @FINITE A s) (h3 : term808 A x s) (h4 : term1041 A B x s t n) (h5 : (term822 A s) = m) (h6 : term742 A B t x n) : term885 A B x s t m n.
Proof. exact (EQ_MP (@lem4318292 A B s m t x n h1 h2 h3 h4 h5 h6) (@lem4318286 A B x s t n h4)). Qed.
Lemma lem4318294 {A B : Type'} (x : A) (t : type1413 A B) (n : nat) (s : A -> Prop) (m : nat) (h1 : term683 A B s) (h2 : @FINITE A s) (h3 : term808 A x s) (h4 : term1041 A B x s t n) (h5 : (term822 A s) = m) : (term742 A B t x n) = (term885 A B x s t m n).
Proof. exact (prop_ext (fun h6 : term742 A B t x n => @lem4318293 A B s m t x n h1 h2 h3 h4 h5 h6) (fun h6 : term885 A B x s t m n => @lem4318287 A B x s t n h4)). Qed.
Lemma lem4318295 {A B : Type'} (x : A) (t : type1413 A B) (n : nat) (s : A -> Prop) (m : nat) (h1 : term683 A B s) (h2 : @FINITE A s) (h3 : term808 A x s) (h4 : term1041 A B x s t n) (h5 : (term822 A s) = m) : term885 A B x s t m n.
Proof. exact (EQ_MP (@lem4318294 A B x t n s m h1 h2 h3 h4 h5) (@lem4318287 A B x s t n h4)). Qed.
Lemma lem4318296 {A B : Type'} (t : type1413 A B) (n : nat) (x : A) (s : A -> Prop) (m : nat) (h1 : term683 A B s) (h2 : @FINITE A s) (h3 : term808 A x s) (h4 : (term822 A s) = m) : term1046 A B x s t m n.
Proof. exact (fun h0 : term1041 A B x s t n => @lem4318295 A B x t n s m h1 h2 h3 h0 h4). Qed.
Lemma lem4318297 {A B : Type'} (t : type1413 A B) (n : nat) (x : A) (s : A -> Prop) (m : nat) (h1 : term683 A B s) (h2 : @FINITE A s) (h3 : term808 A x s) (h4 : (term822 A s) = m) : term974 A B x s t m n.
Proof. exact (EQ_MP (@lem4307404 A B x s t m n) (@lem4318296 A B t n x s m h1 h2 h3 h4)). Qed.
Lemma lem4318298 {A B : Type'} (t : type1413 A B) (n : nat) (x : A) (s : A -> Prop) (m : nat) (h1 : term683 A B s) (h2 : @FINITE A s) (h3 : term808 A x s) (h4 : (term822 A s) = m) : term889 A B x s t m n.
Proof. exact (EQ_MP (@lem4306869 A B x s t m n) (@lem4318297 A B t n x s m h1 h2 h3 h4)). Qed.
Lemma lem4318303 {A B : Type'} (t : type1413 A B) (x : A) (s : A -> Prop) (m : nat) (h1 : term683 A B s) (h2 : @FINITE A s) (h3 : term808 A x s) (h4 : (term822 A s) = m) : term893 A B x s t m.
Proof. exact (fun n : nat => @lem4318298 A B t n x s m h1 h2 h3 h4). Qed.
Lemma lem4318308 {A B : Type'} (x : A) (s : A -> Prop) (m : nat) (h1 : term683 A B s) (h2 : @FINITE A s) (h3 : term808 A x s) (h4 : (term822 A s) = m) : term896 A B x s m.
Proof. exact (fun t : type1413 A B => @lem4318303 A B t x s m h1 h2 h3 h4). Qed.
Lemma lem4318309 {A B : Type'} (m : nat) (x : A) (s : A -> Prop) (h1 : term683 A B s) (h2 : @FINITE A s) (h3 : term808 A x s) : term900 A B x s m.
Proof. exact (fun h0 : (term822 A s) = m => @lem4318308 A B x s m h1 h2 h3 h0). Qed.
Lemma lem4318314 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term683 A B s) (h2 : @FINITE A s) (h3 : term808 A x s) : term903 A B x s.
Proof. exact (fun m : nat => @lem4318309 A B m x s h1 h2 h3). Qed.
Lemma lem4318315 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term698 A B x s) : term696 A x s.
Proof. exact (proj2 (@lem4306816 A B x s h1)). Qed.
Lemma lem4318316 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term698 A B x s) : term683 A B s.
Proof. exact (proj1 (@lem4306816 A B x s h1)). Qed.
Lemma lem4318317 {A : Type'} (x : A) (s : A -> Prop) (h1 : term696 A x s) : @FINITE A s.
Proof. exact (proj2 (@lem4306817 A x s h1)). Qed.
Lemma lem4318318 {A : Type'} (x : A) (s : A -> Prop) (h1 : term696 A x s) : term808 A x s.
Proof. exact (proj1 (@lem4306817 A x s h1)). Qed.
Lemma lem4318319 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term683 A B s) (h2 : @FINITE A s) (h3 : term808 A x s) : (@FINITE A s) = (term903 A B x s).
Proof. exact (prop_ext (fun h4 : @FINITE A s => @lem4318314 A B x s h1 h2 h3) (fun h4 : term903 A B x s => @lem4306819 A s h2)). Qed.
Lemma lem4318320 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term683 A B s) (h2 : @FINITE A s) (h3 : term808 A x s) : term903 A B x s.
Proof. exact (EQ_MP (@lem4318319 A B x s h1 h2 h3) (@lem4306819 A s h2)). Qed.
Lemma lem4318321 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term683 A B s) (h2 : @FINITE A s) (h3 : term808 A x s) : (term808 A x s) = (term903 A B x s).
Proof. exact (prop_ext (fun h4 : term808 A x s => @lem4318320 A B x s h1 h2 h3) (fun h4 : term903 A B x s => @lem4306820 A x s h3)). Qed.
Lemma lem4318322 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term683 A B s) (h2 : @FINITE A s) (h3 : term808 A x s) : term903 A B x s.
Proof. exact (EQ_MP (@lem4318321 A B x s h1 h2 h3) (@lem4306820 A x s h3)). Qed.
Lemma lem4318323 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term683 A B s) (h2 : term808 A x s) (h3 : term696 A x s) : (@FINITE A s) = (term903 A B x s).
Proof. exact (prop_ext (fun h4 : @FINITE A s => @lem4318322 A B x s h1 h4 h2) (fun h4 : term903 A B x s => @lem4318317 A x s h3)). Qed.
Lemma lem4318324 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term683 A B s) (h2 : term808 A x s) (h3 : term696 A x s) : term903 A B x s.
Proof. exact (EQ_MP (@lem4318323 A B x s h1 h2 h3) (@lem4318317 A x s h3)). Qed.
Lemma lem4318325 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term683 A B s) (h2 : term696 A x s) : (term808 A x s) = (term903 A B x s).
Proof. exact (prop_ext (fun h3 : term808 A x s => @lem4318324 A B x s h1 h3 h2) (fun h3 : term903 A B x s => @lem4318318 A x s h2)). Qed.
Lemma lem4318326 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term683 A B s) (h2 : term696 A x s) : term903 A B x s.
Proof. exact (EQ_MP (@lem4318325 A B x s h1 h2) (@lem4318318 A x s h2)). Qed.
Lemma lem4318327 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term683 A B s) (h2 : term696 A x s) : (term683 A B s) = (term903 A B x s).
Proof. exact (prop_ext (fun h3 : term683 A B s => @lem4318326 A B x s h1 h2) (fun h3 : term903 A B x s => @lem4306818 A B s h1)). Qed.
Lemma lem4318328 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term683 A B s) (h2 : term696 A x s) : term903 A B x s.
Proof. exact (EQ_MP (@lem4318327 A B x s h1 h2) (@lem4306818 A B s h1)). Qed.
Lemma lem4318329 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term683 A B s) (h2 : term698 A B x s) : (term696 A x s) = (term903 A B x s).
Proof. exact (prop_ext (fun h3 : term696 A x s => @lem4318328 A B x s h1 h3) (fun h3 : term903 A B x s => @lem4318315 A B x s h2)). Qed.
Lemma lem4318330 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term683 A B s) (h2 : term698 A B x s) : term903 A B x s.
Proof. exact (EQ_MP (@lem4318329 A B x s h1 h2) (@lem4318315 A B x s h2)). Qed.
Lemma lem4318331 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term698 A B x s) : (term683 A B s) = (term903 A B x s).
Proof. exact (prop_ext (fun h2 : term683 A B s => @lem4318330 A B x s h2 h1) (fun h2 : term903 A B x s => @lem4318316 A B x s h1)). Qed.
Lemma lem4318332 {A B : Type'} (x : A) (s : A -> Prop) (h1 : term698 A B x s) : term903 A B x s.
Proof. exact (EQ_MP (@lem4318331 A B x s h1) (@lem4318316 A B x s h1)). Qed.
Lemma lem4318333 {A B : Type'} (x : A) (s : A -> Prop) : term906 A B x s.
Proof. exact (fun h0 : term698 A B x s => @lem4318332 A B x s h0). Qed.
Lemma lem4318338 {A B : Type'} (x : A) : term908 A B x.
Proof. exact (fun s : A -> Prop => @lem4318333 A B x s). Qed.
Lemma lem4318343 {A B : Type'} : term910 A B.
Proof. exact (fun x : A => @lem4318338 A B x). Qed.
Lemma lem4318344 {A B : Type'} : term911 A B.
Proof. exact (conj (@lem4306815 A B) (@lem4318343 A B)). Qed.
Lemma lem4318345 {A B : Type'} : term714 A B.
Proof. exact (EQ_MP (@lem4306615 A B) (@lem4318344 A B)). Qed.
Lemma lem4318346 {A B : Type'} : term686 A B.
Proof. exact (@lem4296497 A B (@lem4318345 A B)). Qed.
Lemma lem4318347 {A B : Type'} : term604 A B.
Proof. exact (EQ_MP (@lem4296464 A B) (@lem4318346 A B)). Qed.
Lemma lem4318348 {A B : Type'} : term603 A B.
Proof. exact (EQ_MP (@lem4295983 A B) (@lem4318347 A B)). Qed.
