Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_UNIONS_NONZERO_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FINITE_INDUCT_STRONG_spec.
Require Import FINITE_UNIONS_spec.
Require Import IN_INSERT_spec.
Require Import IN_INTER_spec.
Require Import IN_UNIONS_spec.
Require Import SUM_CLAUSES_spec.
Require Import SUM_UNION_NONZERO_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm129_spec.
Require Import thm137_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1831_spec.
Require Import thm1832_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
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
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm3322101_spec.
Require Import thm3322164_spec.
Require Import thm3324017_spec.
Require Import thm3325374_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm885_spec.
Require Import thm886_spec.
Lemma lem7178809 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem7178810 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem7178811 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem7178810 t1) (@lem7178809 t1)). Qed.
Lemma lem7178812 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem7178811 t1 t2). Qed.
Lemma lem7178813 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem7178814 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem7178813 t1 t2) (@lem7178812 t1 t2)). Qed.
Lemma lem7178815 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem7178814 t1 t2 t3). Qed.
Lemma lem7178816 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem7178817 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem7178816 t1 t2 t3) (@lem7178815 t1 t2 t3)). Qed.
Lemma lem7178818 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem7178817 t1 t2 t3)). Qed.
Lemma lem7178819 {_135252 : Type'} (h1 : term7 _135252) : term7 _135252.
Proof. exact (h1). Qed.
Lemma lem7178820 {_135252 : Type'} (f : _135252 -> real) (h1 : term7 _135252) : term8 _135252 f.
Proof. exact (@lem7178819 _135252 h1 f). Qed.
Lemma lem7178821 {_135252 : Type'} (f : _135252 -> real) : (term8 _135252 f) = (term9 _135252 f).
Proof. exact (eq_refl (term8 _135252 f)). Qed.
Lemma lem7178822 {_135252 : Type'} (f : _135252 -> real) (h1 : term7 _135252) : term9 _135252 f.
Proof. exact (EQ_MP (@lem7178821 _135252 f) (@lem7178820 _135252 f h1)). Qed.
Lemma lem7178823 {_135252 : Type'} (f : _135252 -> real) (s : _135252 -> Prop) (h1 : term7 _135252) : term10 _135252 f s.
Proof. exact (@lem7178822 _135252 f h1 s). Qed.
Lemma lem7178824 {_135252 : Type'} (s : _135252 -> Prop) (f : _135252 -> real) : (term10 _135252 f s) = (term11 _135252 s f).
Proof. exact (eq_refl (term10 _135252 f s)). Qed.
Lemma lem7178825 {_135252 : Type'} (s : _135252 -> Prop) (f : _135252 -> real) (h1 : term7 _135252) : term11 _135252 s f.
Proof. exact (EQ_MP (@lem7178824 _135252 s f) (@lem7178823 _135252 f s h1)). Qed.
Lemma lem7178826 {_135252 : Type'} (s : _135252 -> Prop) (f : _135252 -> real) (t : _135252 -> Prop) (h1 : term7 _135252) : term12 _135252 s f t.
Proof. exact (@lem7178825 _135252 s f h1 t). Qed.
Lemma lem7178827 {_135252 : Type'} (s : _135252 -> Prop) (t : _135252 -> Prop) (f : _135252 -> real) : (term12 _135252 s f t) = (term13 _135252 s t f).
Proof. exact (eq_refl (term12 _135252 s f t)). Qed.
Lemma lem7178828 {_135252 : Type'} (s : _135252 -> Prop) (t : _135252 -> Prop) (f : _135252 -> real) (h1 : term7 _135252) : term13 _135252 s t f.
Proof. exact (EQ_MP (@lem7178827 _135252 s t f) (@lem7178826 _135252 s f t h1)). Qed.
Lemma lem7178829 {_135252 : Type'} (s : _135252 -> Prop) (t : _135252 -> Prop) (f : _135252 -> real) (h1 : term14 _135252 s t f) : term14 _135252 s t f.
Proof. exact (h1). Qed.
Lemma lem7178830 {_135252 : Type'} (s : _135252 -> Prop) (t : _135252 -> Prop) (f : _135252 -> real) (h1 : term7 _135252) (h2 : term14 _135252 s t f) : (term15 _135252 s t f) = (term16 _135252 s t f).
Proof. exact (@lem7178828 _135252 s t f h1 (@lem7178829 _135252 s t f h2)). Qed.
Lemma lem7178831 {_135252 : Type'} (s : _135252 -> Prop) (t : _135252 -> Prop) (f : _135252 -> real) (h1 : term14 _135252 s t f) : term17 _135252 s t f.
Proof. exact (fun h0 : term7 _135252 => @lem7178830 _135252 s t f h0 h1). Qed.
Lemma lem7178832 {_135252 : Type'} (h1 : term7 _135252) : term7 _135252.
Proof. exact (h1). Qed.
Lemma lem7178833 {_135252 : Type'} (s : _135252 -> Prop) (t : _135252 -> Prop) (f : _135252 -> real) (h1 : term7 _135252) (h2 : term14 _135252 s t f) : (term15 _135252 s t f) = (term16 _135252 s t f).
Proof. exact (@lem7178831 _135252 s t f h2 (@lem7178832 _135252 h1)). Qed.
Lemma lem7178834 {_135252 : Type'} (s : _135252 -> Prop) (t : _135252 -> Prop) (f : _135252 -> real) (h1 : term7 _135252) : term13 _135252 s t f.
Proof. exact (fun h0 : term14 _135252 s t f => @lem7178833 _135252 s t f h1 h0). Qed.
Lemma lem7178835 {_135252 : Type'} (s : _135252 -> Prop) (t : _135252 -> Prop) (h1 : term7 _135252) : term18 _135252 s t.
Proof. exact (fun f : _135252 -> real => @lem7178834 _135252 s t f h1). Qed.
Lemma lem7178836 {_135252 : Type'} (s : _135252 -> Prop) (h1 : term7 _135252) : term19 _135252 s.
Proof. exact (fun t : _135252 -> Prop => @lem7178835 _135252 s t h1). Qed.
Lemma lem7178837 {_135252 : Type'} (h1 : term7 _135252) : term20 _135252.
Proof. exact (fun s : _135252 -> Prop => @lem7178836 _135252 s h1). Qed.
Lemma lem7178838 {_135252 : Type'} : term21 _135252.
Proof. exact (fun h0 : term7 _135252 => @lem7178837 _135252 h0). Qed.
Lemma lem7178839 {_135252 : Type'} : term20 _135252.
Proof. exact (@lem7178838 _135252 (@lem7178808 _135252)). Qed.
Lemma lem7178840 {_135252 : Type'} (s : _135252 -> Prop) : term22 _135252 s.
Proof. exact (@lem7178839 _135252 s). Qed.
Lemma lem7178841 {_135252 : Type'} (s : _135252 -> Prop) : (term22 _135252 s) = (term19 _135252 s).
Proof. exact (eq_refl (term22 _135252 s)). Qed.
Lemma lem7178842 {_135252 : Type'} (s : _135252 -> Prop) : term19 _135252 s.
Proof. exact (EQ_MP (@lem7178841 _135252 s) (@lem7178840 _135252 s)). Qed.
Lemma lem7178843 {_135252 : Type'} (s : _135252 -> Prop) (t : _135252 -> Prop) : term23 _135252 s t.
Proof. exact (@lem7178842 _135252 s t). Qed.
Lemma lem7178844 {_135252 : Type'} (s : _135252 -> Prop) (t : _135252 -> Prop) : (term23 _135252 s t) = (term18 _135252 s t).
Proof. exact (eq_refl (term23 _135252 s t)). Qed.
Lemma lem7178845 {_135252 : Type'} (s : _135252 -> Prop) (t : _135252 -> Prop) : term18 _135252 s t.
Proof. exact (EQ_MP (@lem7178844 _135252 s t) (@lem7178843 _135252 s t)). Qed.
Lemma lem7178846 {_135252 : Type'} (s : _135252 -> Prop) (t : _135252 -> Prop) (f : _135252 -> real) : term24 _135252 s t f.
Proof. exact (@lem7178845 _135252 s t f). Qed.
Lemma lem7178847 {_135252 : Type'} (s : _135252 -> Prop) (t : _135252 -> Prop) (f : _135252 -> real) : (term24 _135252 s t f) = (term13 _135252 s t f).
Proof. exact (eq_refl (term24 _135252 s t f)). Qed.
Lemma lem7178849 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem7178850 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem7178851 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem7178850 t1) (@lem7178849 t1)). Qed.
Lemma lem7178852 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem7178851 t1 t2). Qed.
Lemma lem7178853 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem7178854 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem7178853 t1 t2) (@lem7178852 t1 t2)). Qed.
Lemma lem7178855 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem7178854 t1 t2 t3). Qed.
Lemma lem7178856 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem7178857 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem7178856 t1 t2 t3) (@lem7178855 t1 t2 t3)). Qed.
Lemma lem7178858 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem7178857 t1 t2 t3)). Qed.
Lemma lem7178859 {A : Type'} (x : A) : term25 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem7178860 {A : Type'} (x : A) : (term25 A x) = (term26 A x).
Proof. exact (eq_refl (term25 A x)). Qed.
Lemma lem7178861 {A : Type'} (x : A) : term26 A x.
Proof. exact (EQ_MP (@lem7178860 A x) (@lem7178859 A x)). Qed.
Lemma lem7178862 {A : Type'} (x : A) (y : A) : term27 A x y.
Proof. exact (@lem7178861 A x y). Qed.
Lemma lem7178863 {A : Type'} (y : A) (x : A) : (term27 A x y) = (term28 A y x).
Proof. exact (eq_refl (term27 A x y)). Qed.
Lemma lem7178864 {A : Type'} (y : A) (x : A) : term28 A y x.
Proof. exact (EQ_MP (@lem7178863 A y x) (@lem7178862 A x y)). Qed.
Lemma lem7178865 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term29 A y x s.
Proof. exact (@lem7178864 A y x s). Qed.
Lemma lem7178866 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term29 A y x s) = ((term30 A x y s) = (term31 A y x s)).
Proof. exact (eq_refl (term29 A y x s)). Qed.
Lemma lem7178880 {_131483 : Type'} : term32 _131483.
Proof. exact (proj1 (@lem7067645 _131483 Prop)). Qed.
Lemma lem7178881 {_131483 : Type'} (f : _131483 -> real) : term33 _131483 f.
Proof. exact (@lem7178880 _131483 f). Qed.
Lemma lem7178882 {_131483 : Type'} (f : _131483 -> real) : (term33 _131483 f) = ((@sum _131483 (@EMPTY _131483) f) = term34).
Proof. exact (eq_refl (term33 _131483 f)). Qed.
Lemma lem7178884 {A : Type'} (h1 : term35 A) : term35 A.
Proof. exact (h1). Qed.
Lemma lem7178885 {A : Type'} (P : type686 A) (h1 : term35 A) : term36 A P.
Proof. exact (@lem7178884 A h1 P). Qed.
Lemma lem7178886 {A : Type'} (P : type686 A) : (term36 A P) = (term37 A P).
Proof. exact (eq_refl (term36 A P)). Qed.
Lemma lem7178887 {A : Type'} (P : type686 A) (h1 : term35 A) : term37 A P.
Proof. exact (EQ_MP (@lem7178886 A P) (@lem7178885 A P h1)). Qed.
Lemma lem7178888 {A : Type'} (P : type686 A) (h1 : term38 A P) : term38 A P.
Proof. exact (h1). Qed.
Lemma lem7178889 {A : Type'} (P : type686 A) (h1 : term35 A) (h2 : term38 A P) : term39 A P.
Proof. exact (@lem7178887 A P h1 (@lem7178888 A P h2)). Qed.
Lemma lem7178890 {A : Type'} (P : type686 A) (h1 : term38 A P) : term40 A P.
Proof. exact (fun h0 : term35 A => @lem7178889 A P h0 h1). Qed.
Lemma lem7178891 {A : Type'} (h1 : term35 A) : term35 A.
Proof. exact (h1). Qed.
Lemma lem7178892 {A : Type'} (P : type686 A) (h1 : term35 A) (h2 : term38 A P) : term39 A P.
Proof. exact (@lem7178890 A P h2 (@lem7178891 A h1)). Qed.
Lemma lem7178893 {A : Type'} (P : type686 A) (h1 : term35 A) : term37 A P.
Proof. exact (fun h0 : term38 A P => @lem7178892 A P h1 h0). Qed.
Lemma lem7178894 {A : Type'} (h1 : term35 A) : term35 A.
Proof. exact (fun P : type686 A => @lem7178893 A P h1). Qed.
Lemma lem7178895 {A : Type'} : term41 A.
Proof. exact (fun h0 : term35 A => @lem7178894 A h0). Qed.
Lemma lem7178896 {A : Type'} : term35 A.
Proof. exact (@lem7178895 A (@lem3558722 A)). Qed.
Lemma lem7178897 {A : Type'} (P : type686 A) : term36 A P.
Proof. exact (@lem7178896 A P). Qed.
Lemma lem7178898 {A : Type'} (P : type686 A) : (term36 A P) = (term37 A P).
Proof. exact (eq_refl (term36 A P)). Qed.
Lemma lem7178905 (p : Prop) (q : Prop) (r : Prop) : (term42 p q r) = (term43 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem7178906 {A : Type'} (s : type686 A) (f : A -> real) : (term44 A s f) = (term45 A s f).
Proof. exact (@lem7178905 (@FINITE (A -> Prop) s) (term46 A s f) ((term47 A s f) = (term48 A s f))). Qed.
Lemma lem7178907 {A : Type'} (f : A -> real) : (term49 A f) = (term50 A f).
Proof. exact (fun_ext (fun s : type686 A => @lem7178906 A s f)). Qed.
Lemma lem7178908 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem7178909 {A : Type'} (f : A -> real) : (term51 A f) = (term52 A f).
Proof. exact (MK_COMB (@lem7178908 A) (@lem7178907 A f)). Qed.
Lemma lem7178910 {A : Type'} (f : A -> real) : (term52 A f) = (term51 A f).
Proof. exact (SYM (@lem7178909 A f)). Qed.
Lemma lem7178912 {A : Type'} (P : type686 A) : term37 A P.
Proof. exact (EQ_MP (@lem7178898 A P) (@lem7178897 A P)). Qed.
Lemma lem7178913 {A : Type'} (P : type180 A) : term53 A P.
Proof. exact (@lem7178912 (A -> Prop) P). Qed.
Lemma lem7178914 {A : Type'} (f : A -> real) : term54 A f.
Proof. exact (@lem7178913 A (term55 A f)). Qed.
Lemma lem7178915 {A : Type'} (f : A -> real) : (term56 A f) = (term57 A f).
Proof. exact (eq_refl (term56 A f)). Qed.
Lemma lem7178916 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7178917 {A : Type'} (f : A -> real) : (term58 A f) = (term59 A f).
Proof. exact (MK_COMB (@lem7178916) (@lem7178915 A f)). Qed.
Lemma lem7178918 {A : Type'} (s : type686 A) (f : A -> real) : (term60 A f s) = (term61 A s f).
Proof. exact (eq_refl (term60 A f s)). Qed.
Lemma lem7178919 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7178920 {A : Type'} (s : type686 A) (f : A -> real) : (term62 A f s) = (term63 A s f).
Proof. exact (MK_COMB (@lem7178919) (@lem7178918 A s f)). Qed.
Lemma lem7178921 {A : Type'} (x : A -> Prop) (s : type686 A) : (term64 A x s) = (term64 A x s).
Proof. exact (eq_refl (term64 A x s)). Qed.
Lemma lem7178922 {A : Type'} (f : A -> real) (x : A -> Prop) (s : type686 A) : (term65 A f x s) = (term66 A f x s).
Proof. exact (MK_COMB (@lem7178920 A s f) (@lem7178921 A x s)). Qed.
Lemma lem7178923 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7178924 {A : Type'} (f : A -> real) (x : A -> Prop) (s : type686 A) : (term67 A f x s) = (term68 A f x s).
Proof. exact (MK_COMB (@lem7178923) (@lem7178922 A f x s)). Qed.
Lemma lem7178925 {A : Type'} (x : A -> Prop) (s : type686 A) (f : A -> real) : (term69 A f x s) = (term70 A x s f).
Proof. exact (eq_refl (term69 A f x s)). Qed.
Lemma lem7178926 {A : Type'} (x : A -> Prop) (s : type686 A) (f : A -> real) : (term71 A f x s) = (term72 A x s f).
Proof. exact (MK_COMB (@lem7178924 A f x s) (@lem7178925 A x s f)). Qed.
Lemma lem7178927 {A : Type'} (x : A -> Prop) (f : A -> real) : (term73 A f x) = (term74 A x f).
Proof. exact (fun_ext (fun s : type686 A => @lem7178926 A x s f)). Qed.
Lemma lem7178928 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem7178929 {A : Type'} (x : A -> Prop) (f : A -> real) : (term75 A f x) = (term76 A x f).
Proof. exact (MK_COMB (@lem7178928 A) (@lem7178927 A x f)). Qed.
Lemma lem7178930 {A : Type'} (f : A -> real) : (term77 A f) = (term78 A f).
Proof. exact (fun_ext (fun x : A -> Prop => @lem7178929 A x f)). Qed.
Lemma lem7178931 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7178932 {A : Type'} (f : A -> real) : (term79 A f) = (term80 A f).
Proof. exact (MK_COMB (@lem7178931 A) (@lem7178930 A f)). Qed.
Lemma lem7178933 {A : Type'} (f : A -> real) : (term81 A f) = (term82 A f).
Proof. exact (MK_COMB (@lem7178917 A f) (@lem7178932 A f)). Qed.
Lemma lem7178934 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7178935 {A : Type'} (f : A -> real) : (term83 A f) = (term84 A f).
Proof. exact (MK_COMB (@lem7178934) (@lem7178933 A f)). Qed.
Lemma lem7178936 {A : Type'} (s : type686 A) (f : A -> real) : (term60 A f s) = (term61 A s f).
Proof. exact (eq_refl (term60 A f s)). Qed.
Lemma lem7178937 {A : Type'} (s : type686 A) : (term85 A s) = (term85 A s).
Proof. exact (eq_refl (term85 A s)). Qed.
Lemma lem7178938 {A : Type'} (s : type686 A) (f : A -> real) : (term86 A f s) = (term45 A s f).
Proof. exact (MK_COMB (@lem7178937 A s) (@lem7178936 A s f)). Qed.
Lemma lem7178939 {A : Type'} (f : A -> real) : (term87 A f) = (term50 A f).
Proof. exact (fun_ext (fun s : type686 A => @lem7178938 A s f)). Qed.
Lemma lem7178940 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem7178941 {A : Type'} (f : A -> real) : (term88 A f) = (term52 A f).
Proof. exact (MK_COMB (@lem7178940 A) (@lem7178939 A f)). Qed.
Lemma lem7178942 {A : Type'} (f : A -> real) : (term54 A f) = (term89 A f).
Proof. exact (MK_COMB (@lem7178935 A f) (@lem7178941 A f)). Qed.
Lemma lem7178943 {A : Type'} (f : A -> real) : term89 A f.
Proof. exact (EQ_MP (@lem7178942 A f) (@lem7178914 A f)). Qed.
Lemma lem7178985 {_86801 : Type'} : (@UNIONS _86801 (@EMPTY (_86801 -> Prop))) = (@EMPTY _86801).
Proof. exact (EQ_MP (@lem3322101 _86801) (@lem3322164 _86801)). Qed.
Lemma lem7178986 {A : Type'} : (@UNIONS A (@EMPTY (A -> Prop))) = (@EMPTY A).
Proof. exact (@lem7178985 A). Qed.
Lemma lem7178987 {A : Type'} : (@sum A) = (@sum A).
Proof. exact (eq_refl (@sum A)). Qed.
Lemma lem7178988 {A : Type'} : (term90 A) = (@sum A (@EMPTY A)).
Proof. exact (MK_COMB (@lem7178987 A) (@lem7178986 A)). Qed.
Lemma lem7178989 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7178990 {A : Type'} (f : A -> real) : (term91 A f) = (@sum A (@EMPTY A) f).
Proof. exact (MK_COMB (@lem7178988 A) (@lem7178989 A f)). Qed.
Lemma lem7178992 {_131483 : Type'} (f : _131483 -> real) : (@sum _131483 (@EMPTY _131483) f) = term34.
Proof. exact (EQ_MP (@lem7178882 _131483 f) (@lem7178881 _131483 f)). Qed.
Lemma lem7178993 {A : Type'} (f : A -> real) : (@sum A (@EMPTY A) f) = term34.
Proof. exact (@lem7178992 A f). Qed.
Lemma lem7178994 {A : Type'} (f : A -> real) : (term91 A f) = term34.
Proof. exact (TRANS (@lem7178990 A f) (@lem7178993 A f)). Qed.
Lemma lem7178995 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7178996 {A : Type'} (f : A -> real) : (term92 A f) = term93.
Proof. exact (MK_COMB (@lem7178995) (@lem7178994 A f)). Qed.
Lemma lem7178998 {_131483 : Type'} (f : _131483 -> real) : (@sum _131483 (@EMPTY _131483) f) = term34.
Proof. exact (EQ_MP (@lem7178882 _131483 f) (@lem7178881 _131483 f)). Qed.
Lemma lem7178999 {A : Type'} (f : type688 A) : (@sum (A -> Prop) (@EMPTY (A -> Prop)) f) = term34.
Proof. exact (@lem7178998 (A -> Prop) f). Qed.
Lemma lem7179000 {A : Type'} (f : A -> real) : (term94 A f) = term34.
Proof. exact (@lem7178999 A (term95 A f)). Qed.
Lemma lem7179001 {A : Type'} (f : A -> real) : ((term91 A f) = (term94 A f)) = (term34 = term34).
Proof. exact (MK_COMB (@lem7178996 A f) (@lem7179000 A f)). Qed.
Lemma lem7179003 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7179004 (x : real) : (x = x) = True.
Proof. exact (@lem7179003 real x). Qed.
Lemma lem7179005 : (term34 = term34) = True.
Proof. exact (@lem7179004 term34). Qed.
Lemma lem7179006 {A : Type'} (f : A -> real) : ((term91 A f) = (term94 A f)) = True.
Proof. exact (TRANS (@lem7179001 A f) (@lem7179005)). Qed.
Lemma lem7179007 {A : Type'} (f : A -> real) : (term96 A f) = (term96 A f).
Proof. exact (eq_refl (term96 A f)). Qed.
Lemma lem7179008 {A : Type'} (f : A -> real) : (term57 A f) = (term97 A f).
Proof. exact (MK_COMB (@lem7179007 A f) (@lem7179006 A f)). Qed.
Lemma lem7179010 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7179011 {A : Type'} (f : A -> real) : (term97 A f) = True.
Proof. exact (@lem7179010 (term98 A f)). Qed.
Lemma lem7179012 {A : Type'} (f : A -> real) : (term57 A f) = True.
Proof. exact (TRANS (@lem7179008 A f) (@lem7179011 A f)). Qed.
Lemma lem7179013 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7179014 {A : Type'} (f : A -> real) : (term59 A f) = (and True).
Proof. exact (MK_COMB (@lem7179013) (@lem7179012 A f)). Qed.
Lemma lem7179078 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term30 A x y s) = (term31 A y x s).
Proof. exact (EQ_MP (@lem7178866 A y x s) (@lem7178865 A y x s)). Qed.
Lemma lem7179079 {A : Type'} (y : A -> Prop) (x : A -> Prop) (s : type686 A) : (term99 A x y s) = (term100 A y x s).
Proof. exact (@lem7179078 (A -> Prop) y x s). Qed.
Lemma lem7179080 {A : Type'} (x : A -> Prop) (t : A -> Prop) (s : type686 A) : (term99 A t x s) = (term100 A x t s).
Proof. exact (@lem7179079 A x t s). Qed.
Lemma lem7179085 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7179086 {A : Type'} (x : A -> Prop) (t : A -> Prop) (s : type686 A) : (term101 A t x s) = (term102 A x t s).
Proof. exact (MK_COMB (@lem7179085) (@lem7179080 A x t s)). Qed.
Lemma lem7179087 {A : Type'} (t : A -> Prop) : (@FINITE A t) = (@FINITE A t).
Proof. exact (eq_refl (@FINITE A t)). Qed.
Lemma lem7179088 {A : Type'} (x : A -> Prop) (s : type686 A) (t : A -> Prop) : (term103 A x s t) = (term104 A x s t).
Proof. exact (MK_COMB (@lem7179086 A x t s) (@lem7179087 A t)). Qed.
Lemma lem7179091 {A : Type'} (x : A -> Prop) (s : type686 A) : (term105 A x s) = (term106 A x s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7179088 A x s t)). Qed.
Lemma lem7179092 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7179093 {A : Type'} (x : A -> Prop) (s : type686 A) : (term107 A x s) = (term108 A x s).
Proof. exact (MK_COMB (@lem7179092 A) (@lem7179091 A x s)). Qed.
Lemma lem7179098 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7179099 {A : Type'} (x : A -> Prop) (s : type686 A) : (term109 A x s) = (term110 A x s).
Proof. exact (MK_COMB (@lem7179098) (@lem7179093 A x s)). Qed.
Lemma lem7179117 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term30 A x y s) = (term31 A y x s).
Proof. exact (EQ_MP (@lem7178866 A y x s) (@lem7178865 A y x s)). Qed.
Lemma lem7179118 {A : Type'} (y : A -> Prop) (x : A -> Prop) (s : type686 A) : (term99 A x y s) = (term100 A y x s).
Proof. exact (@lem7179117 (A -> Prop) y x s). Qed.
Lemma lem7179119 {A : Type'} (x : A -> Prop) (t1 : A -> Prop) (s : type686 A) : (term99 A t1 x s) = (term100 A x t1 s).
Proof. exact (@lem7179118 A x t1 s). Qed.
Lemma lem7179124 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7179125 {A : Type'} (x : A -> Prop) (t1 : A -> Prop) (s : type686 A) : (term111 A t1 x s) = (term112 A x t1 s).
Proof. exact (MK_COMB (@lem7179124) (@lem7179119 A x t1 s)). Qed.
Lemma lem7179129 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term30 A x y s) = (term31 A y x s).
Proof. exact (EQ_MP (@lem7178866 A y x s) (@lem7178865 A y x s)). Qed.
Lemma lem7179130 {A : Type'} (y : A -> Prop) (x : A -> Prop) (s : type686 A) : (term99 A x y s) = (term100 A y x s).
Proof. exact (@lem7179129 (A -> Prop) y x s). Qed.
Lemma lem7179131 {A : Type'} (x : A -> Prop) (t2 : A -> Prop) (s : type686 A) : (term99 A t2 x s) = (term100 A x t2 s).
Proof. exact (@lem7179130 A x t2 s). Qed.
Lemma lem7179136 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7179137 {A : Type'} (x : A -> Prop) (t2 : A -> Prop) (s : type686 A) : (term111 A t2 x s) = (term112 A x t2 s).
Proof. exact (MK_COMB (@lem7179136) (@lem7179131 A x t2 s)). Qed.
Lemma lem7179144 {A : Type'} (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term113 A t1 x t2) = (term113 A t1 x t2).
Proof. exact (eq_refl (term113 A t1 x t2)). Qed.
Lemma lem7179145 {A : Type'} (x : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x' : A) (t2 : A -> Prop) : (term114 A x s t1 x' t2) = (term115 A x s t1 x' t2).
Proof. exact (MK_COMB (@lem7179137 A x t2 s) (@lem7179144 A t1 x' t2)). Qed.
Lemma lem7179148 {A : Type'} (x : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x' : A) (t2 : A -> Prop) : (term116 A x s t1 x' t2) = (term117 A x s t1 x' t2).
Proof. exact (MK_COMB (@lem7179125 A x t1 s) (@lem7179145 A x s t1 x' t2)). Qed.
Lemma lem7179151 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7179152 {A : Type'} (x : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x' : A) (t2 : A -> Prop) : (term118 A x s t1 x' t2) = (term119 A x s t1 x' t2).
Proof. exact (MK_COMB (@lem7179151) (@lem7179148 A x s t1 x' t2)). Qed.
Lemma lem7179155 {A : Type'} (f : A -> real) (x : A) : ((f x) = term34) = ((f x) = term34).
Proof. exact (eq_refl ((f x) = term34)). Qed.
Lemma lem7179156 {A : Type'} (x : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> real) (x' : A) : (term120 A x s t1 t2 f x') = (term121 A x s t1 t2 f x').
Proof. exact (MK_COMB (@lem7179152 A x s t1 x' t2) (@lem7179155 A f x')). Qed.
Lemma lem7179159 {A : Type'} (x : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> real) : (term122 A x s t1 t2 f) = (term123 A x s t1 t2 f).
Proof. exact (fun_ext (fun x' : A => @lem7179156 A x s t1 t2 f x')). Qed.
Lemma lem7179160 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7179161 {A : Type'} (x : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> real) : (term124 A x s t1 t2 f) = (term125 A x s t1 t2 f).
Proof. exact (MK_COMB (@lem7179160 A) (@lem7179159 A x s t1 t2 f)). Qed.
Lemma lem7179166 {A : Type'} (x : A -> Prop) (s : type686 A) (t1 : A -> Prop) (f : A -> real) : (term126 A x s t1 f) = (term127 A x s t1 f).
Proof. exact (fun_ext (fun t2 : A -> Prop => @lem7179161 A x s t1 t2 f)). Qed.
Lemma lem7179167 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7179168 {A : Type'} (x : A -> Prop) (s : type686 A) (t1 : A -> Prop) (f : A -> real) : (term128 A x s t1 f) = (term129 A x s t1 f).
Proof. exact (MK_COMB (@lem7179167 A) (@lem7179166 A x s t1 f)). Qed.
Lemma lem7179173 {A : Type'} (x : A -> Prop) (s : type686 A) (f : A -> real) : (term130 A x s f) = (term131 A x s f).
Proof. exact (fun_ext (fun t1 : A -> Prop => @lem7179168 A x s t1 f)). Qed.
Lemma lem7179174 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7179175 {A : Type'} (x : A -> Prop) (s : type686 A) (f : A -> real) : (term132 A x s f) = (term133 A x s f).
Proof. exact (MK_COMB (@lem7179174 A) (@lem7179173 A x s f)). Qed.
Lemma lem7179180 {A : Type'} (x : A -> Prop) (s : type686 A) (f : A -> real) : (term134 A x s f) = (term135 A x s f).
Proof. exact (MK_COMB (@lem7179099 A x s) (@lem7179175 A x s f)). Qed.
Lemma lem7179183 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7179184 {A : Type'} (x : A -> Prop) (s : type686 A) (f : A -> real) : (term136 A x s f) = (term137 A x s f).
Proof. exact (MK_COMB (@lem7179183) (@lem7179180 A x s f)). Qed.
Lemma lem7179188 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) : (term138 _86841 s u) = (term139 _86841 s u).
Proof. exact (EQ_MP (@lem3324017 _86841 s u) (@lem3325374 _86841 s u)). Qed.
Lemma lem7179189 {A : Type'} (s : A -> Prop) (u : type686 A) : (term138 A s u) = (term139 A s u).
Proof. exact (@lem7179188 A s u). Qed.
Lemma lem7179190 {A : Type'} (x : A -> Prop) (s : type686 A) : (term138 A x s) = (term139 A x s).
Proof. exact (@lem7179189 A x s). Qed.
Lemma lem7179191 {A : Type'} : (@sum A) = (@sum A).
Proof. exact (eq_refl (@sum A)). Qed.
Lemma lem7179192 {A : Type'} (x : A -> Prop) (s : type686 A) : (term140 A x s) = (term141 A x s).
Proof. exact (MK_COMB (@lem7179191 A) (@lem7179190 A x s)). Qed.
Lemma lem7179193 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7179194 {A : Type'} (x : A -> Prop) (s : type686 A) (f : A -> real) : (term142 A x s f) = (term143 A x s f).
Proof. exact (MK_COMB (@lem7179192 A x s) (@lem7179193 A f)). Qed.
Lemma lem7179195 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7179196 {A : Type'} (x : A -> Prop) (s : type686 A) (f : A -> real) : (term144 A x s f) = (term145 A x s f).
Proof. exact (MK_COMB (@lem7179195) (@lem7179194 A x s f)). Qed.
Lemma lem7179197 {A : Type'} (x : A -> Prop) (s : type686 A) (f : A -> real) : (term146 A x s f) = (term146 A x s f).
Proof. exact (eq_refl (term146 A x s f)). Qed.
Lemma lem7179198 {A : Type'} (x : A -> Prop) (s : type686 A) (f : A -> real) : ((term142 A x s f) = (term146 A x s f)) = ((term143 A x s f) = (term146 A x s f)).
Proof. exact (MK_COMB (@lem7179196 A x s f) (@lem7179197 A x s f)). Qed.
Lemma lem7179201 {A : Type'} (x : A -> Prop) (s : type686 A) (f : A -> real) : (term70 A x s f) = (term147 A x s f).
Proof. exact (MK_COMB (@lem7179184 A x s f) (@lem7179198 A x s f)). Qed.
Lemma lem7179204 {A : Type'} (f : A -> real) (x : A -> Prop) (s : type686 A) : (term68 A f x s) = (term68 A f x s).
Proof. exact (eq_refl (term68 A f x s)). Qed.
Lemma lem7179205 {A : Type'} (x : A -> Prop) (s : type686 A) (f : A -> real) : (term72 A x s f) = (term148 A x s f).
Proof. exact (MK_COMB (@lem7179204 A f x s) (@lem7179201 A x s f)). Qed.
Lemma lem7179208 {A : Type'} (x : A -> Prop) (f : A -> real) : (term74 A x f) = (term149 A x f).
Proof. exact (fun_ext (fun s : type686 A => @lem7179205 A x s f)). Qed.
Lemma lem7179209 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem7179210 {A : Type'} (x : A -> Prop) (f : A -> real) : (term76 A x f) = (term150 A x f).
Proof. exact (MK_COMB (@lem7179209 A) (@lem7179208 A x f)). Qed.
Lemma lem7179215 {A : Type'} (f : A -> real) : (term78 A f) = (term151 A f).
Proof. exact (fun_ext (fun x : A -> Prop => @lem7179210 A x f)). Qed.
Lemma lem7179216 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7179217 {A : Type'} (f : A -> real) : (term80 A f) = (term152 A f).
Proof. exact (MK_COMB (@lem7179216 A) (@lem7179215 A f)). Qed.
Lemma lem7179222 {A : Type'} (f : A -> real) : (term82 A f) = (term153 A f).
Proof. exact (MK_COMB (@lem7179014 A f) (@lem7179217 A f)). Qed.
Lemma lem7179224 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7179225 {A : Type'} (f : A -> real) : (term153 A f) = (term152 A f).
Proof. exact (@lem7179224 (term152 A f)). Qed.
Lemma lem7179328 {A : Type'} (f : A -> real) : (term82 A f) = (term152 A f).
Proof. exact (TRANS (@lem7179222 A f) (@lem7179225 A f)). Qed.
Lemma lem7179329 {A : Type'} (f : A -> real) : (term152 A f) = (term82 A f).
Proof. exact (SYM (@lem7179328 A f)). Qed.
Lemma lem7179330 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term66 A f t s) : term66 A f t s.
Proof. exact (h1). Qed.
Lemma lem7179331 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term135 A t s f) : term135 A t s f.
Proof. exact (h1). Qed.
Lemma lem7179332 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term133 A t s f) : term133 A t s f.
Proof. exact (h1). Qed.
Lemma lem7179333 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term108 A t s) : term108 A t s.
Proof. exact (h1). Qed.
Lemma lem7179335 (p : Prop) (q : Prop) (r : Prop) : (term42 p q r) = (term43 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem7179336 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term154 A t s f) = (term155 A t s f).
Proof. exact (@lem7179335 (term61 A s f) (term64 A t s) ((term143 A t s f) = (term146 A t s f))). Qed.
Lemma lem7179337 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term155 A t s f) = (term154 A t s f).
Proof. exact (SYM (@lem7179336 A t s f)). Qed.
Lemma lem7179338 {_131524 : Type'} : term156 _131524.
Proof. exact (proj2 (@lem7067645 Prop _131524)). Qed.
Lemma lem7179339 {_131524 : Type'} (x : _131524) : term157 _131524 x.
Proof. exact (@lem7179338 _131524 x). Qed.
Lemma lem7179340 {_131524 : Type'} (x : _131524) : (term157 _131524 x) = (term158 _131524 x).
Proof. exact (eq_refl (term157 _131524 x)). Qed.
Lemma lem7179341 {_131524 : Type'} (x : _131524) : term158 _131524 x.
Proof. exact (EQ_MP (@lem7179340 _131524 x) (@lem7179339 _131524 x)). Qed.
Lemma lem7179342 {_131524 : Type'} (x : _131524) (f : _131524 -> real) : term159 _131524 x f.
Proof. exact (@lem7179341 _131524 x f). Qed.
Lemma lem7179343 {_131524 : Type'} (x : _131524) (f : _131524 -> real) : (term159 _131524 x f) = (term160 _131524 x f).
Proof. exact (eq_refl (term159 _131524 x f)). Qed.
Lemma lem7179344 {_131524 : Type'} (x : _131524) (f : _131524 -> real) : term160 _131524 x f.
Proof. exact (EQ_MP (@lem7179343 _131524 x f) (@lem7179342 _131524 x f)). Qed.
Lemma lem7179345 {_131524 : Type'} (x : _131524) (f : _131524 -> real) (s : _131524 -> Prop) : term161 _131524 x f s.
Proof. exact (@lem7179344 _131524 x f s). Qed.
Lemma lem7179346 {_131524 : Type'} (x : _131524) (s : _131524 -> Prop) (f : _131524 -> real) : (term161 _131524 x f s) = (term162 _131524 x s f).
Proof. exact (eq_refl (term161 _131524 x f s)). Qed.
Lemma lem7179347 {_131524 : Type'} (x : _131524) (s : _131524 -> Prop) (f : _131524 -> real) : term162 _131524 x s f.
Proof. exact (EQ_MP (@lem7179346 _131524 x s f) (@lem7179345 _131524 x f s)). Qed.
Lemma lem7179348 {_131524 : Type'} (s : _131524 -> Prop) (h1 : @FINITE _131524 s) : @FINITE _131524 s.
Proof. exact (h1). Qed.
Lemma lem7179349 {_131524 : Type'} (x : _131524) (f : _131524 -> real) (s : _131524 -> Prop) (h1 : @FINITE _131524 s) : (term163 _131524 x s f) = (term164 _131524 x s f).
Proof. exact (@lem7179347 _131524 x s f (@lem7179348 _131524 s h1)). Qed.
Lemma lem7179359 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (s : type686 A) (h1 : term108 A t s) : term165 A t s t'.
Proof. exact (@lem7179333 A t s h1 t'). Qed.
Lemma lem7179360 {A : Type'} (t : A -> Prop) (s : type686 A) (t' : A -> Prop) : (term165 A t s t') = (term104 A t s t').
Proof. exact (eq_refl (term165 A t s t')). Qed.
Lemma lem7179361 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (s : type686 A) (h1 : term108 A t s) : term104 A t s t'.
Proof. exact (EQ_MP (@lem7179360 A t s t') (@lem7179359 A t' t s h1)). Qed.
Lemma lem7179362 {A : Type'} (t : A -> Prop) (t' : A -> Prop) (s : type686 A) (h1 : term100 A t t' s) : term100 A t t' s.
Proof. exact (h1). Qed.
Lemma lem7179363 {A : Type'} (t : A -> Prop) (t' : A -> Prop) (s : type686 A) (h1 : term108 A t s) (h2 : term100 A t t' s) : @FINITE A t'.
Proof. exact (@lem7179361 A t' t s h1 (@lem7179362 A t t' s h2)). Qed.
Lemma lem7179364 {A : Type'} (t' : A -> Prop) : (@FINITE A t') = ((@FINITE A t') = True).
Proof. exact (@lem7 (@FINITE A t')). Qed.
Lemma lem7179365 {A : Type'} (t : A -> Prop) (t' : A -> Prop) (s : type686 A) (h1 : term108 A t s) (h2 : term100 A t t' s) : (@FINITE A t') = True.
Proof. exact (EQ_MP (@lem7179364 A t') (@lem7179363 A t t' s h1 h2)). Qed.
Lemma lem7179442 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term166 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7179443 (p : Prop) (q : Prop) (p' : Prop) : term167 p q p'.
Proof. exact (fun q' : Prop => @lem7179442 p q p' q'). Qed.
Lemma lem7179444 (p : Prop) (q : Prop) : term168 p q.
Proof. exact (fun p' : Prop => @lem7179443 p q p'). Qed.
Lemma lem7179445 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : term169 A t s f.
Proof. exact (@lem7179444 (term61 A s f) (term170 A t s f)). Qed.
Lemma lem7179446 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (p' : Prop) : term171 A t s f p'.
Proof. exact (@lem7179445 A t s f p'). Qed.
Lemma lem7179447 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (p' : Prop) : (term171 A t s f p') = (term172 A t s f p').
Proof. exact (eq_refl (term171 A t s f p')). Qed.
Lemma lem7179448 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (p' : Prop) : term172 A t s f p'.
Proof. exact (EQ_MP (@lem7179447 A t s f p') (@lem7179446 A t s f p')). Qed.
Lemma lem7179449 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (p' : Prop) (q' : Prop) : term173 A t s f p' q'.
Proof. exact (@lem7179448 A t s f p' q'). Qed.
Lemma lem7179450 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (p' : Prop) (q' : Prop) : (term173 A t s f p' q') = (term174 A t s f p' q').
Proof. exact (eq_refl (term173 A t s f p' q')). Qed.
Lemma lem7179451 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (p' : Prop) (q' : Prop) : term174 A t s f p' q'.
Proof. exact (EQ_MP (@lem7179450 A t s f p' q') (@lem7179449 A t s f p' q')). Qed.
Lemma lem7179455 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term166 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7179456 (p : Prop) (q : Prop) (p' : Prop) : term167 p q p'.
Proof. exact (fun q' : Prop => @lem7179455 p q p' q'). Qed.
Lemma lem7179457 (p : Prop) (q : Prop) : term168 p q.
Proof. exact (fun p' : Prop => @lem7179456 p q p'). Qed.
Lemma lem7179458 {A : Type'} (s : type686 A) (f : A -> real) : term175 A s f.
Proof. exact (@lem7179457 (term46 A s f) ((term47 A s f) = (term48 A s f))). Qed.
Lemma lem7179459 {A : Type'} (s : type686 A) (f : A -> real) (p' : Prop) : term176 A s f p'.
Proof. exact (@lem7179458 A s f p'). Qed.
Lemma lem7179460 {A : Type'} (s : type686 A) (f : A -> real) (p' : Prop) : (term176 A s f p') = (term177 A s f p').
Proof. exact (eq_refl (term176 A s f p')). Qed.
Lemma lem7179461 {A : Type'} (s : type686 A) (f : A -> real) (p' : Prop) : term177 A s f p'.
Proof. exact (EQ_MP (@lem7179460 A s f p') (@lem7179459 A s f p')). Qed.
Lemma lem7179462 {A : Type'} (s : type686 A) (f : A -> real) (p' : Prop) (q' : Prop) : term178 A s f p' q'.
Proof. exact (@lem7179461 A s f p' q'). Qed.
Lemma lem7179463 {A : Type'} (s : type686 A) (f : A -> real) (p' : Prop) (q' : Prop) : (term178 A s f p' q') = (term179 A s f p' q').
Proof. exact (eq_refl (term178 A s f p' q')). Qed.
Lemma lem7179464 {A : Type'} (s : type686 A) (f : A -> real) (p' : Prop) (q' : Prop) : term179 A s f p' q'.
Proof. exact (EQ_MP (@lem7179463 A s f p' q') (@lem7179462 A s f p' q')). Qed.
Lemma lem7179522 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term166 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7179523 (p : Prop) (q : Prop) (p' : Prop) : term167 p q p'.
Proof. exact (fun q' : Prop => @lem7179522 p q p' q'). Qed.
Lemma lem7179524 (p : Prop) (q : Prop) : term168 p q.
Proof. exact (fun p' : Prop => @lem7179523 p q p'). Qed.
Lemma lem7179525 {A : Type'} (s : type686 A) (_96154 : A -> Prop) : term180 A s _96154.
Proof. exact (@lem7179524 (@IN (A -> Prop) _96154 s) (@FINITE A _96154)). Qed.
Lemma lem7179526 {A : Type'} (s : type686 A) (_96154 : A -> Prop) (p' : Prop) : term181 A s _96154 p'.
Proof. exact (@lem7179525 A s _96154 p'). Qed.
Lemma lem7179527 {A : Type'} (s : type686 A) (_96154 : A -> Prop) (p' : Prop) : (term181 A s _96154 p') = (term182 A s _96154 p').
Proof. exact (eq_refl (term181 A s _96154 p')). Qed.
Lemma lem7179528 {A : Type'} (s : type686 A) (_96154 : A -> Prop) (p' : Prop) : term182 A s _96154 p'.
Proof. exact (EQ_MP (@lem7179527 A s _96154 p') (@lem7179526 A s _96154 p')). Qed.
Lemma lem7179529 {A : Type'} (s : type686 A) (_96154 : A -> Prop) (p' : Prop) (q' : Prop) : term183 A s _96154 p' q'.
Proof. exact (@lem7179528 A s _96154 p' q'). Qed.
Lemma lem7179530 {A : Type'} (s : type686 A) (_96154 : A -> Prop) (p' : Prop) (q' : Prop) : (term183 A s _96154 p' q') = (term184 A s _96154 p' q').
Proof. exact (eq_refl (term183 A s _96154 p' q')). Qed.
Lemma lem7179531 {A : Type'} (s : type686 A) (_96154 : A -> Prop) (p' : Prop) (q' : Prop) : term184 A s _96154 p' q'.
Proof. exact (EQ_MP (@lem7179530 A s _96154 p' q') (@lem7179529 A s _96154 p' q')). Qed.
Lemma lem7179532 {A : Type'} (_96154 : A -> Prop) (s : type686 A) : (@IN (A -> Prop) _96154 s) = (@IN (A -> Prop) _96154 s).
Proof. exact (eq_refl (@IN (A -> Prop) _96154 s)). Qed.
Lemma lem7179533 {A : Type'} (_96154 : A -> Prop) (s : type686 A) (q' : Prop) : term185 A _96154 s q'.
Proof. exact (@lem7179531 A s _96154 (@IN (A -> Prop) _96154 s) q'). Qed.
Lemma lem7179534 {A : Type'} (_96154 : A -> Prop) (s : type686 A) (q' : Prop) : term186 A _96154 s q'.
Proof. exact (@lem7179533 A _96154 s q' (@lem7179532 A _96154 s)). Qed.
Lemma lem7179535 {A : Type'} (_96154 : A -> Prop) (s : type686 A) (h1 : @IN (A -> Prop) _96154 s) : @IN (A -> Prop) _96154 s.
Proof. exact (h1). Qed.
Lemma lem7179536 {A : Type'} (_96154 : A -> Prop) (s : type686 A) : (@IN (A -> Prop) _96154 s) = ((@IN (A -> Prop) _96154 s) = True).
Proof. exact (@lem7 (@IN (A -> Prop) _96154 s)). Qed.
Lemma lem7179539 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (s : type686 A) (h1 : term108 A t s) : term187 A t s t'.
Proof. exact (fun h0 : term100 A t t' s => @lem7179365 A t t' s h1 h0). Qed.
Lemma lem7179540 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (s : type686 A) (h1 : term108 A t s) : term187 A t s t'.
Proof. exact (@lem7179539 A t' t s h1). Qed.
Lemma lem7179541 {A : Type'} (_96154 : A -> Prop) (t : A -> Prop) (s : type686 A) (h1 : term108 A t s) : term187 A t s _96154.
Proof. exact (@lem7179540 A _96154 t s h1). Qed.
Lemma lem7179547 {A : Type'} (_96154 : A -> Prop) (s : type686 A) (h1 : @IN (A -> Prop) _96154 s) : (@IN (A -> Prop) _96154 s) = True.
Proof. exact (EQ_MP (@lem7179536 A _96154 s) (@lem7179535 A _96154 s h1)). Qed.
Lemma lem7179548 {A : Type'} (_96154 : A -> Prop) (t : A -> Prop) : (term188 A _96154 t) = (term188 A _96154 t).
Proof. exact (eq_refl (term188 A _96154 t)). Qed.
Lemma lem7179549 {A : Type'} (t : A -> Prop) (_96154 : A -> Prop) (s : type686 A) (h1 : @IN (A -> Prop) _96154 s) : (term100 A t _96154 s) = (term189 A _96154 t).
Proof. exact (MK_COMB (@lem7179548 A _96154 t) (@lem7179547 A _96154 s h1)). Qed.
Lemma lem7179551 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem7179552 {A : Type'} (_96154 : A -> Prop) (t : A -> Prop) : (term189 A _96154 t) = True.
Proof. exact (@lem7179551 (_96154 = t)). Qed.
Lemma lem7179553 {A : Type'} (t : A -> Prop) (_96154 : A -> Prop) (s : type686 A) (h1 : @IN (A -> Prop) _96154 s) : (term100 A t _96154 s) = True.
Proof. exact (TRANS (@lem7179549 A t _96154 s h1) (@lem7179552 A _96154 t)). Qed.
Lemma lem7179554 {A : Type'} (t : A -> Prop) (_96154 : A -> Prop) (s : type686 A) (h1 : @IN (A -> Prop) _96154 s) : True = (term100 A t _96154 s).
Proof. exact (SYM (@lem7179553 A t _96154 s h1)). Qed.
Lemma lem7179555 {A : Type'} (t : A -> Prop) (_96154 : A -> Prop) (s : type686 A) (h1 : @IN (A -> Prop) _96154 s) : term100 A t _96154 s.
Proof. exact (EQ_MP (@lem7179554 A t _96154 s h1) (@lem0)). Qed.
Lemma lem7179556 {A : Type'} (t : A -> Prop) (_96154 : A -> Prop) (s : type686 A) (h1 : term108 A t s) (h2 : @IN (A -> Prop) _96154 s) : (@FINITE A _96154) = True.
Proof. exact (@lem7179541 A _96154 t s h1 (@lem7179555 A t _96154 s h2)). Qed.
Lemma lem7179557 {A : Type'} (_96154 : A -> Prop) (t : A -> Prop) (s : type686 A) (h1 : term108 A t s) : term190 A s _96154.
Proof. exact (fun h0 : @IN (A -> Prop) _96154 s => @lem7179556 A t _96154 s h1 h0). Qed.
Lemma lem7179558 {A : Type'} (_96154 : A -> Prop) (s : type686 A) : term191 A _96154 s.
Proof. exact (@lem7179534 A _96154 s True). Qed.
Lemma lem7179559 {A : Type'} (_96154 : A -> Prop) (t : A -> Prop) (s : type686 A) (h1 : term108 A t s) : (term192 A s _96154) = (term193 A _96154 s).
Proof. exact (@lem7179558 A _96154 s (@lem7179557 A _96154 t s h1)). Qed.
Lemma lem7179561 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7179562 {A : Type'} (_96154 : A -> Prop) (s : type686 A) : (term193 A _96154 s) = True.
Proof. exact (@lem7179561 (@IN (A -> Prop) _96154 s)). Qed.
Lemma lem7179563 {A : Type'} (_96154 : A -> Prop) (t : A -> Prop) (s : type686 A) (h1 : term108 A t s) : (term192 A s _96154) = True.
Proof. exact (TRANS (@lem7179559 A _96154 t s h1) (@lem7179562 A _96154 s)). Qed.
Lemma lem7179566 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term108 A t s) : (term194 A s) = (term195 A).
Proof. exact (fun_ext (fun _96154 : A -> Prop => @lem7179563 A _96154 t s h1)). Qed.
Lemma lem7179567 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7179568 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term108 A t s) : (term196 A s) = (term197 A).
Proof. exact (MK_COMB (@lem7179567 A) (@lem7179566 A t s h1)). Qed.
Lemma lem7179570 {A : Type'} (t : Prop) : (term198 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7179571 {A : Type'} (t : Prop) : (term199 A t) = t.
Proof. exact (@lem7179570 (A -> Prop) t). Qed.
Lemma lem7179572 {A : Type'} : (term197 A) = True.
Proof. exact (@lem7179571 A True). Qed.
Lemma lem7179573 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term108 A t s) : (term196 A s) = True.
Proof. exact (TRANS (@lem7179568 A t s h1) (@lem7179572 A)). Qed.
Lemma lem7179574 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7179575 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term108 A t s) : (term200 A s) = (and True).
Proof. exact (MK_COMB (@lem7179574) (@lem7179573 A t s h1)). Qed.
Lemma lem7180040 {A : Type'} (s : type686 A) (f : A -> real) : (term201 A s f) = (term201 A s f).
Proof. exact (eq_refl (term201 A s f)). Qed.
Lemma lem7180041 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term108 A t s) : (term46 A s f) = (term202 A s f).
Proof. exact (MK_COMB (@lem7179575 A t s h1) (@lem7180040 A s f)). Qed.
Lemma lem7180043 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7180044 {A : Type'} (s : type686 A) (f : A -> real) : (term202 A s f) = (term201 A s f).
Proof. exact (@lem7180043 (term201 A s f)). Qed.
Lemma lem7180509 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term108 A t s) : (term46 A s f) = (term201 A s f).
Proof. exact (TRANS (@lem7180041 A f t s h1) (@lem7180044 A s f)). Qed.
Lemma lem7180510 {A : Type'} (s : type686 A) (f : A -> real) (q' : Prop) : term203 A s f q'.
Proof. exact (@lem7179464 A s f (term201 A s f) q'). Qed.
Lemma lem7180511 {A : Type'} (f : A -> real) (q' : Prop) (t : A -> Prop) (s : type686 A) (h1 : term108 A t s) : term204 A s f q'.
Proof. exact (@lem7180510 A s f q' (@lem7180509 A f t s h1)). Qed.
Lemma lem7180583 {A : Type'} (s : type686 A) (f : A -> real) : ((term47 A s f) = (term48 A s f)) = ((term47 A s f) = (term48 A s f)).
Proof. exact (eq_refl ((term47 A s f) = (term48 A s f))). Qed.
Lemma lem7180584 {A : Type'} (s : type686 A) (f : A -> real) : term205 A s f.
Proof. exact (fun h0 : term201 A s f => @lem7180583 A s f). Qed.
Lemma lem7180585 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term108 A t s) : term206 A s f.
Proof. exact (@lem7180511 A f ((term47 A s f) = (term48 A s f)) t s h1). Qed.
Lemma lem7180586 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term108 A t s) : (term61 A s f) = (term207 A s f).
Proof. exact (@lem7180585 A f t s h1 (@lem7180584 A s f)). Qed.
Lemma lem7181608 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (q' : Prop) : term208 A t s f q'.
Proof. exact (@lem7179451 A t s f (term207 A s f) q'). Qed.
Lemma lem7181609 {A : Type'} (f : A -> real) (q' : Prop) (t : A -> Prop) (s : type686 A) (h1 : term108 A t s) : term209 A t s f q'.
Proof. exact (@lem7181608 A t s f q' (@lem7180586 A f t s h1)). Qed.
Lemma lem7181621 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term166 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7181622 (p : Prop) (q : Prop) (p' : Prop) : term167 p q p'.
Proof. exact (fun q' : Prop => @lem7181621 p q p' q'). Qed.
Lemma lem7181623 (p : Prop) (q : Prop) : term168 p q.
Proof. exact (fun p' : Prop => @lem7181622 p q p'). Qed.
Lemma lem7181624 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : term210 A t s f.
Proof. exact (@lem7181623 (term64 A t s) ((term143 A t s f) = (term146 A t s f))). Qed.
Lemma lem7181625 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (p' : Prop) : term211 A t s f p'.
Proof. exact (@lem7181624 A t s f p'). Qed.
Lemma lem7181626 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (p' : Prop) : (term211 A t s f p') = (term212 A t s f p').
Proof. exact (eq_refl (term211 A t s f p')). Qed.
Lemma lem7181627 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (p' : Prop) : term212 A t s f p'.
Proof. exact (EQ_MP (@lem7181626 A t s f p') (@lem7181625 A t s f p')). Qed.
Lemma lem7181628 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (p' : Prop) (q' : Prop) : term213 A t s f p' q'.
Proof. exact (@lem7181627 A t s f p' q'). Qed.
Lemma lem7181629 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (p' : Prop) (q' : Prop) : (term213 A t s f p' q') = (term214 A t s f p' q').
Proof. exact (eq_refl (term213 A t s f p' q')). Qed.
Lemma lem7181630 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (p' : Prop) (q' : Prop) : term214 A t s f p' q'.
Proof. exact (EQ_MP (@lem7181629 A t s f p' q') (@lem7181628 A t s f p' q')). Qed.
Lemma lem7181637 {A : Type'} (t : A -> Prop) (s : type686 A) : (term64 A t s) = (term64 A t s).
Proof. exact (eq_refl (term64 A t s)). Qed.
Lemma lem7181638 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (q' : Prop) : term215 A f t s q'.
Proof. exact (@lem7181630 A t s f (term64 A t s) q'). Qed.
Lemma lem7181639 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (q' : Prop) : term216 A f t s q'.
Proof. exact (@lem7181638 A f t s q' (@lem7181637 A t s)). Qed.
Lemma lem7181640 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term64 A t s) : term64 A t s.
Proof. exact (h1). Qed.
Lemma lem7181641 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term64 A t s) : @FINITE (A -> Prop) s.
Proof. exact (proj2 (@lem7181640 A t s h1)). Qed.
Lemma lem7181642 {A : Type'} (s : type686 A) : (@FINITE (A -> Prop) s) = ((@FINITE (A -> Prop) s) = True).
Proof. exact (@lem7 (@FINITE (A -> Prop) s)). Qed.
Lemma lem7181644 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term64 A t s) : term217 A t s.
Proof. exact (proj1 (@lem7181640 A t s h1)). Qed.
Lemma lem7181645 {A : Type'} (t : A -> Prop) (s : type686 A) : term218 A t s.
Proof. exact (@lem82 (@IN (A -> Prop) t s)). Qed.
Lemma lem7181650 {_131524 : Type'} (x : _131524) (s : _131524 -> Prop) (f : _131524 -> real) : term162 _131524 x s f.
Proof. exact (fun h0 : @FINITE _131524 s => @lem7179349 _131524 x f s h0). Qed.
Lemma lem7181651 {A : Type'} (x : A -> Prop) (s : type686 A) (f : type688 A) : term219 A x s f.
Proof. exact (@lem7181650 (A -> Prop) x s f). Qed.
Lemma lem7181652 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : term220 A t s f.
Proof. exact (@lem7181651 A t s (term95 A f)). Qed.
Lemma lem7181654 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term64 A t s) : (@FINITE (A -> Prop) s) = True.
Proof. exact (EQ_MP (@lem7181642 A s) (@lem7181641 A t s h1)). Qed.
Lemma lem7181655 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term64 A t s) : True = (@FINITE (A -> Prop) s).
Proof. exact (SYM (@lem7181654 A t s h1)). Qed.
Lemma lem7181656 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term64 A t s) : @FINITE (A -> Prop) s.
Proof. exact (EQ_MP (@lem7181655 A t s h1) (@lem0)). Qed.
Lemma lem7181657 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term64 A t s) : (term146 A t s f) = (term221 A t s f).
Proof. exact (@lem7181652 A t s f (@lem7181656 A t s h1)). Qed.
Lemma lem7181659 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term222 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem7181660 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term223 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem7181659 _2963 g t e g' t' e'). Qed.
Lemma lem7181661 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term224 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem7181660 _2963 g t e g' t'). Qed.
Lemma lem7181662 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term225 _2963 g t e.
Proof. exact (fun g' : Prop => @lem7181661 _2963 g t e g'). Qed.
Lemma lem7181663 (g : Prop) (t : real) (e : real) : term226 g t e.
Proof. exact (@lem7181662 real g t e). Qed.
Lemma lem7181664 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : term227 A t s f.
Proof. exact (@lem7181663 (@IN (A -> Prop) t s) (term48 A s f) (term228 A t s f)). Qed.
Lemma lem7181665 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (g' : Prop) : term229 A t s f g'.
Proof. exact (@lem7181664 A t s f g'). Qed.
Lemma lem7181666 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (g' : Prop) : (term229 A t s f g') = (term230 A t s f g').
Proof. exact (eq_refl (term229 A t s f g')). Qed.
Lemma lem7181667 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (g' : Prop) : term230 A t s f g'.
Proof. exact (EQ_MP (@lem7181666 A t s f g') (@lem7181665 A t s f g')). Qed.
Lemma lem7181668 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (g' : Prop) (t' : real) : term231 A t s f g' t'.
Proof. exact (@lem7181667 A t s f g' t'). Qed.
Lemma lem7181669 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (g' : Prop) (t' : real) : (term231 A t s f g' t') = (term232 A t s f g' t').
Proof. exact (eq_refl (term231 A t s f g' t')). Qed.
Lemma lem7181670 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (g' : Prop) (t' : real) : term232 A t s f g' t'.
Proof. exact (EQ_MP (@lem7181669 A t s f g' t') (@lem7181668 A t s f g' t')). Qed.
Lemma lem7181671 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (g' : Prop) (t' : real) (e' : real) : term233 A t s f g' t' e'.
Proof. exact (@lem7181670 A t s f g' t' e'). Qed.
Lemma lem7181672 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (g' : Prop) (t' : real) (e' : real) : (term233 A t s f g' t' e') = (term234 A t s f g' t' e').
Proof. exact (eq_refl (term233 A t s f g' t' e')). Qed.
Lemma lem7181673 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (g' : Prop) (t' : real) (e' : real) : term234 A t s f g' t' e'.
Proof. exact (EQ_MP (@lem7181672 A t s f g' t' e') (@lem7181671 A t s f g' t' e')). Qed.
Lemma lem7181675 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term64 A t s) : (@IN (A -> Prop) t s) = False.
Proof. exact (@lem7181645 A t s (@lem7181644 A t s h1)). Qed.
Lemma lem7181676 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (t' : real) (e' : real) : term235 A t s f t' e'.
Proof. exact (@lem7181673 A t s f False t' e'). Qed.
Lemma lem7181677 {A : Type'} (f : A -> real) (t' : real) (e' : real) (t : A -> Prop) (s : type686 A) (h1 : term64 A t s) : term236 A t s f t' e'.
Proof. exact (@lem7181676 A t s f t' e' (@lem7181675 A t s h1)). Qed.
Lemma lem7181681 {A : Type'} (s : type686 A) (f : A -> real) : (term48 A s f) = (term48 A s f).
Proof. exact (eq_refl (term48 A s f)). Qed.
Lemma lem7181682 {A : Type'} (s : type686 A) (f : A -> real) : term237 A s f.
Proof. exact (fun h0 : False => @lem7181681 A s f). Qed.
Lemma lem7181683 {A : Type'} (f : A -> real) (e' : real) (t : A -> Prop) (s : type686 A) (h1 : term64 A t s) : term238 A t s f e'.
Proof. exact (@lem7181677 A f (term48 A s f) e' t s h1). Qed.
Lemma lem7181684 {A : Type'} (f : A -> real) (e' : real) (t : A -> Prop) (s : type686 A) (h1 : term64 A t s) : term239 A t s f e'.
Proof. exact (@lem7181683 A f e' t s h1 (@lem7181682 A s f)). Qed.
Lemma lem7181691 {A B : Type'} (f : A -> B) (y : A) : (term240 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7181692 {A : Type'} (f : type688 A) (y : A -> Prop) : (term241 A f y) = (f y).
Proof. exact (@lem7181691 (A -> Prop) real f y). Qed.
Lemma lem7181693 {A : Type'} (f : A -> real) (t : A -> Prop) : (term242 A f t) = (term243 A f t).
Proof. exact (@lem7181692 A (term95 A f) t). Qed.
Lemma lem7181694 {A : Type'} (t : A -> Prop) (f : A -> real) : (term243 A f t) = (@sum A t f).
Proof. exact (eq_refl (term243 A f t)). Qed.
Lemma lem7181695 {A : Type'} (f : A -> real) : (term244 A f) = (term95 A f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7181694 A t f)). Qed.
Lemma lem7181696 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem7181697 {A : Type'} (f : A -> real) (t : A -> Prop) : (term242 A f t) = (term243 A f t).
Proof. exact (MK_COMB (@lem7181695 A f) (@lem7181696 A t)). Qed.
Lemma lem7181698 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7181699 {A : Type'} (f : A -> real) (t : A -> Prop) : (term245 A f t) = (term246 A f t).
Proof. exact (MK_COMB (@lem7181698) (@lem7181697 A f t)). Qed.
Lemma lem7181700 {A : Type'} (t : A -> Prop) (f : A -> real) : (term243 A f t) = (@sum A t f).
Proof. exact (eq_refl (term243 A f t)). Qed.
Lemma lem7181701 {A : Type'} (t : A -> Prop) (f : A -> real) : ((term242 A f t) = (term243 A f t)) = ((term243 A f t) = (@sum A t f)).
Proof. exact (MK_COMB (@lem7181699 A f t) (@lem7181700 A t f)). Qed.
Lemma lem7181702 {A : Type'} (t : A -> Prop) (f : A -> real) : (term243 A f t) = (@sum A t f).
Proof. exact (EQ_MP (@lem7181701 A t f) (@lem7181693 A f t)). Qed.
Lemma lem7181703 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7181704 {A : Type'} (t : A -> Prop) (f : A -> real) : (term247 A f t) = (term248 A t f).
Proof. exact (MK_COMB (@lem7181703) (@lem7181702 A t f)). Qed.
Lemma lem7181705 {A : Type'} (s : type686 A) (f : A -> real) : (term48 A s f) = (term48 A s f).
Proof. exact (eq_refl (term48 A s f)). Qed.
Lemma lem7181706 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term228 A t s f) = (term249 A t s f).
Proof. exact (MK_COMB (@lem7181704 A t f) (@lem7181705 A s f)). Qed.
Lemma lem7181707 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : term250 A t s f.
Proof. exact (fun h0 : ~ False => @lem7181706 A t s f). Qed.
Lemma lem7181708 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term64 A t s) : term251 A t s f.
Proof. exact (@lem7181684 A f (term249 A t s f) t s h1). Qed.
Lemma lem7181709 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term64 A t s) : (term221 A t s f) = (term252 A t s f).
Proof. exact (@lem7181708 A f t s h1 (@lem7181707 A t s f)). Qed.
Lemma lem7181711 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem7181712 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem7181711 real t1 t2). Qed.
Lemma lem7181713 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term252 A t s f) = (term249 A t s f).
Proof. exact (@lem7181712 (term48 A s f) (term249 A t s f)). Qed.
Lemma lem7181714 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term64 A t s) : (term221 A t s f) = (term249 A t s f).
Proof. exact (TRANS (@lem7181709 A f t s h1) (@lem7181713 A t s f)). Qed.
Lemma lem7181715 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term64 A t s) : (term146 A t s f) = (term249 A t s f).
Proof. exact (TRANS (@lem7181657 A f t s h1) (@lem7181714 A f t s h1)). Qed.
Lemma lem7181716 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term145 A t s f) = (term145 A t s f).
Proof. exact (eq_refl (term145 A t s f)). Qed.
Lemma lem7181717 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term64 A t s) : ((term143 A t s f) = (term146 A t s f)) = ((term143 A t s f) = (term249 A t s f)).
Proof. exact (MK_COMB (@lem7181716 A t s f) (@lem7181715 A f t s h1)). Qed.
Lemma lem7181720 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : term253 A t s f.
Proof. exact (fun h0 : term64 A t s => @lem7181717 A f t s h0). Qed.
Lemma lem7181721 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : term254 A t s f.
Proof. exact (@lem7181639 A f t s ((term143 A t s f) = (term249 A t s f))). Qed.
Lemma lem7181722 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term170 A t s f) = (term255 A t s f).
Proof. exact (@lem7181721 A t s f (@lem7181720 A t s f)). Qed.
Lemma lem7181766 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : term256 A t s f.
Proof. exact (fun h0 : term207 A s f => @lem7181722 A t s f). Qed.
Lemma lem7181767 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term108 A t s) : term257 A t s f.
Proof. exact (@lem7181609 A f (term255 A t s f) t s h1). Qed.
Lemma lem7181768 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term108 A t s) : (term155 A t s f) = (term258 A t s f).
Proof. exact (@lem7181767 A f t s h1 (@lem7181766 A t s f)). Qed.
Lemma lem7183925 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term108 A t s) : (term258 A t s f) = (term155 A t s f).
Proof. exact (SYM (@lem7181768 A f t s h1)). Qed.
Lemma lem7183927 (p : Prop) (q : Prop) (r : Prop) : term259 p q r.
Proof. exact (@lem137 p q r (@lem129 p q r)). Qed.
Lemma lem7183928 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : term260 A t s f.
Proof. exact (@lem7183927 (term201 A s f) ((term47 A s f) = (term48 A s f)) (term255 A t s f)). Qed.
Lemma lem7183930 (p : Prop) : p = (term261 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7183931 {A : Type'} (s : type686 A) (f : A -> real) : (term201 A s f) = (term262 A s f).
Proof. exact (@lem7183930 (term201 A s f)). Qed.
Lemma lem7183932 {A : Type'} (s : type686 A) (f : A -> real) : (term262 A s f) = (term201 A s f).
Proof. exact (SYM (@lem7183931 A s f)). Qed.
Lemma lem7183933 {A : Type'} (s : type686 A) (f : A -> real) (h1 : term263 A s f) : term263 A s f.
Proof. exact (h1). Qed.
Lemma lem7183936 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term264 A t s f) : term264 A t s f.
Proof. exact (h1). Qed.
Lemma lem7183937 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : term265 A t s f.
Proof. exact (fun h0 : term264 A t s f => @lem7183936 A t s f h0). Qed.
Lemma lem7183938 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term265 A t s f) : term265 A t s f.
Proof. exact (h1). Qed.
Lemma lem7183939 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term264 A t s f) : term264 A t s f.
Proof. exact (h1). Qed.
Lemma lem7183940 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term264 A t s f) (h2 : term265 A t s f) : term264 A t s f.
Proof. exact (@lem7183938 A t s f h2 (@lem7183939 A t s f h1)). Qed.
Lemma lem7183941 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term264 A t s f) : term266 A t s f.
Proof. exact (fun h0 : term265 A t s f => @lem7183940 A t s f h1 h0). Qed.
Lemma lem7183942 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term265 A t s f) : term265 A t s f.
Proof. exact (h1). Qed.
Lemma lem7183943 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term264 A t s f) (h2 : term265 A t s f) : term264 A t s f.
Proof. exact (@lem7183941 A t s f h1 (@lem7183942 A t s f h2)). Qed.
Lemma lem7183944 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term265 A t s f) : term265 A t s f.
Proof. exact (fun h0 : term264 A t s f => @lem7183943 A t s f h0 h1). Qed.
Lemma lem7183945 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : term267 A t s f.
Proof. exact (fun h0 : term265 A t s f => @lem7183944 A t s f h0). Qed.
Lemma lem7183948 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : term265 A t s f.
Proof. exact (@lem7183945 A t s f (@lem7183937 A t s f)). Qed.
Lemma lem7183949 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : term265 A t s f.
Proof. exact (@lem7183948 A t s f). Qed.
Lemma lem7184001 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7184002 {A : Type'} (s : type686 A) (f : A -> real) : (term262 A s f) = (term268 A s f).
Proof. exact (@lem7184001 (term263 A s f)). Qed.
Lemma lem7184004 (t : Prop) : (term269 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7184005 {A : Type'} (s : type686 A) (f : A -> real) : (term268 A s f) = (term201 A s f).
Proof. exact (@lem7184004 (term201 A s f)). Qed.
Lemma lem7184010 {A : Type'} (s : type686 A) (f : A -> real) : (term262 A s f) = (term201 A s f).
Proof. exact (TRANS (@lem7184002 A s f) (@lem7184005 A s f)). Qed.
Lemma lem7184029 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term270 A t s f) = (term270 A t s f).
Proof. exact (eq_refl (term270 A t s f)). Qed.
Lemma lem7184030 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term271 A t s f) = (term272 A t s f).
Proof. exact (MK_COMB (@lem7184029 A t s f) (@lem7184010 A s f)). Qed.
Lemma lem7184033 {A : Type'} (t : A -> Prop) (s : type686 A) : (term273 A t s) = (term273 A t s).
Proof. exact (eq_refl (term273 A t s)). Qed.
Lemma lem7184034 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term264 A t s f) = (term274 A t s f).
Proof. exact (MK_COMB (@lem7184033 A t s) (@lem7184030 A t s f)). Qed.
Lemma lem7184037 {A : Type'} (s : type686 A) (f : A -> real) : (term275 A s f) = (term276 A s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7184034 A t s f)). Qed.
Lemma lem7184038 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7184039 {A : Type'} (s : type686 A) (f : A -> real) : (term277 A s f) = (term278 A s f).
Proof. exact (MK_COMB (@lem7184038 A) (@lem7184037 A s f)). Qed.
Lemma lem7184044 {A : Type'} (f : A -> real) : (term279 A f) = (term280 A f).
Proof. exact (fun_ext (fun s : type686 A => @lem7184039 A s f)). Qed.
Lemma lem7184045 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem7184046 {A : Type'} (f : A -> real) : (term281 A f) = (term282 A f).
Proof. exact (MK_COMB (@lem7184045 A) (@lem7184044 A f)). Qed.
Lemma lem7184051 {A : Type'} : (term283 A) = (term284 A).
Proof. exact (fun_ext (fun f : A -> real => @lem7184046 A f)). Qed.
Lemma lem7184052 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7184061 {A : Type'} : (term285 A) = (term286 A).
Proof. exact (MK_COMB (@lem7184052 A) (@lem7184051 A)). Qed.
Lemma lem7184084 {A : Type'} (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> real) (x : A) : (term287 A s t1 t2 f x) = (term287 A s t1 t2 f x).
Proof. exact (eq_refl (term287 A s t1 t2 f x)). Qed.
Lemma lem7184085 {A : Type'} (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> real) : (term288 A s t1 t2 f) = (term288 A s t1 t2 f).
Proof. exact (fun_ext (fun x : A => @lem7184084 A s t1 t2 f x)). Qed.
Lemma lem7184086 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7184087 {A : Type'} (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> real) : (term289 A s t1 t2 f) = (term289 A s t1 t2 f).
Proof. exact (MK_COMB (@lem7184086 A) (@lem7184085 A s t1 t2 f)). Qed.
Lemma lem7184088 {A : Type'} (s : type686 A) (t1 : A -> Prop) (f : A -> real) : (term290 A s t1 f) = (term290 A s t1 f).
Proof. exact (fun_ext (fun t2 : A -> Prop => @lem7184087 A s t1 t2 f)). Qed.
Lemma lem7184089 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7184090 {A : Type'} (s : type686 A) (t1 : A -> Prop) (f : A -> real) : (term291 A s t1 f) = (term291 A s t1 f).
Proof. exact (MK_COMB (@lem7184089 A) (@lem7184088 A s t1 f)). Qed.
Lemma lem7184091 {A : Type'} (s : type686 A) (f : A -> real) : (term292 A s f) = (term292 A s f).
Proof. exact (fun_ext (fun t1 : A -> Prop => @lem7184090 A s t1 f)). Qed.
Lemma lem7184092 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7184093 {A : Type'} (s : type686 A) (f : A -> real) : (term201 A s f) = (term201 A s f).
Proof. exact (MK_COMB (@lem7184092 A) (@lem7184091 A s f)). Qed.
Lemma lem7184124 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> real) (x : A) : (term121 A t s t1 t2 f x) = (term121 A t s t1 t2 f x).
Proof. exact (eq_refl (term121 A t s t1 t2 f x)). Qed.
Lemma lem7184125 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> real) : (term123 A t s t1 t2 f) = (term123 A t s t1 t2 f).
Proof. exact (fun_ext (fun x : A => @lem7184124 A t s t1 t2 f x)). Qed.
Lemma lem7184126 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7184127 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> real) : (term125 A t s t1 t2 f) = (term125 A t s t1 t2 f).
Proof. exact (MK_COMB (@lem7184126 A) (@lem7184125 A t s t1 t2 f)). Qed.
Lemma lem7184128 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (f : A -> real) : (term127 A t s t1 f) = (term127 A t s t1 f).
Proof. exact (fun_ext (fun t2 : A -> Prop => @lem7184127 A t s t1 t2 f)). Qed.
Lemma lem7184129 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7184130 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (f : A -> real) : (term129 A t s t1 f) = (term129 A t s t1 f).
Proof. exact (MK_COMB (@lem7184129 A) (@lem7184128 A t s t1 f)). Qed.
Lemma lem7184131 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term131 A t s f) = (term131 A t s f).
Proof. exact (fun_ext (fun t1 : A -> Prop => @lem7184130 A t s t1 f)). Qed.
Lemma lem7184132 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7184133 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term133 A t s f) = (term133 A t s f).
Proof. exact (MK_COMB (@lem7184132 A) (@lem7184131 A t s f)). Qed.
Lemma lem7184134 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7184135 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term270 A t s f) = (term270 A t s f).
Proof. exact (MK_COMB (@lem7184134) (@lem7184133 A t s f)). Qed.
Lemma lem7184136 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term272 A t s f) = (term272 A t s f).
Proof. exact (MK_COMB (@lem7184135 A t s f) (@lem7184093 A s f)). Qed.
Lemma lem7184145 {A : Type'} (t : A -> Prop) (s : type686 A) (t' : A -> Prop) : (term104 A t s t') = (term104 A t s t').
Proof. exact (eq_refl (term104 A t s t')). Qed.
Lemma lem7184146 {A : Type'} (t : A -> Prop) (s : type686 A) : (term106 A t s) = (term106 A t s).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem7184145 A t s t')). Qed.
Lemma lem7184147 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7184148 {A : Type'} (t : A -> Prop) (s : type686 A) : (term108 A t s) = (term108 A t s).
Proof. exact (MK_COMB (@lem7184147 A) (@lem7184146 A t s)). Qed.
Lemma lem7184149 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7184150 {A : Type'} (t : A -> Prop) (s : type686 A) : (term273 A t s) = (term273 A t s).
Proof. exact (MK_COMB (@lem7184149) (@lem7184148 A t s)). Qed.
Lemma lem7184151 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term274 A t s f) = (term274 A t s f).
Proof. exact (MK_COMB (@lem7184150 A t s) (@lem7184136 A t s f)). Qed.
Lemma lem7184152 {A : Type'} (s : type686 A) (f : A -> real) : (term276 A s f) = (term276 A s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7184151 A t s f)). Qed.
Lemma lem7184153 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7184154 {A : Type'} (s : type686 A) (f : A -> real) : (term278 A s f) = (term278 A s f).
Proof. exact (MK_COMB (@lem7184153 A) (@lem7184152 A s f)). Qed.
Lemma lem7184155 {A : Type'} (f : A -> real) : (term280 A f) = (term280 A f).
Proof. exact (fun_ext (fun s : type686 A => @lem7184154 A s f)). Qed.
Lemma lem7184156 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem7184157 {A : Type'} (f : A -> real) : (term282 A f) = (term282 A f).
Proof. exact (MK_COMB (@lem7184156 A) (@lem7184155 A f)). Qed.
Lemma lem7184158 {A : Type'} : (term284 A) = (term284 A).
Proof. exact (fun_ext (fun f : A -> real => @lem7184157 A f)). Qed.
Lemma lem7184159 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7184160 {A : Type'} : (term286 A) = (term286 A).
Proof. exact (MK_COMB (@lem7184159 A) (@lem7184158 A)). Qed.
Lemma lem7184255 {A : Type'} : (term285 A) = (term286 A).
Proof. exact (TRANS (@lem7184061 A) (@lem7184160 A)). Qed.
Lemma lem7184256 {A : Type'} : (term286 A) = (term285 A).
Proof. exact (SYM (@lem7184255 A)). Qed.
Lemma lem7184258 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term133 A t s f) : term133 A t s f.
Proof. exact (h1). Qed.
Lemma lem7184261 (p : Prop) : p = (term261 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7184262 {A : Type'} (f : A -> real) (x : A) : ((f x) = term34) = (term293 A f x).
Proof. exact (@lem7184261 ((f x) = term34)). Qed.
Lemma lem7184263 {A : Type'} (f : A -> real) (x : A) : (term293 A f x) = ((f x) = term34).
Proof. exact (SYM (@lem7184262 A f x)). Qed.
Lemma lem7184264 {A : Type'} (f : A -> real) (x : A) (h1 : term294 A f x) : term294 A f x.
Proof. exact (h1). Qed.
Lemma lem7184324 {A : Type'} (t : A -> Prop) (t1 : A -> Prop) (s : type686 A) : (term295 A t t1 s) = (term296 A t t1 s).
Proof. exact (@lem17160 (t1 = t) (@IN (A -> Prop) t1 s)). Qed.
Lemma lem7184331 {A : Type'} (t : A -> Prop) (t2 : A -> Prop) (s : type686 A) : (term295 A t t2 s) = (term296 A t t2 s).
Proof. exact (@lem17160 (t2 = t) (@IN (A -> Prop) t2 s)). Qed.
Lemma lem7184334 {A : Type'} (t1 : A -> Prop) (t2 : A -> Prop) : (term297 A t1 t2) = (t1 = t2).
Proof. exact (@lem16933 (t1 = t2)). Qed.
Lemma lem7184341 {A : Type'} (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term298 A t1 x t2) = (term299 A t1 x t2).
Proof. exact (@lem17045 (@IN A x t1) (@IN A x t2)). Qed.
Lemma lem7184342 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7184343 {A : Type'} (t1 : A -> Prop) (t2 : A -> Prop) : (term300 A t1 t2) = (term188 A t1 t2).
Proof. exact (MK_COMB (@lem7184342) (@lem7184334 A t1 t2)). Qed.
Lemma lem7184344 {A : Type'} (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term301 A t1 x t2) = (term302 A t1 x t2).
Proof. exact (MK_COMB (@lem7184343 A t1 t2) (@lem7184341 A t1 x t2)). Qed.
Lemma lem7184345 {A : Type'} (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term303 A t1 x t2) = (term301 A t1 x t2).
Proof. exact (@lem17045 (term304 A t1 t2) (term305 A t1 x t2)). Qed.
Lemma lem7184346 {A : Type'} (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term303 A t1 x t2) = (term302 A t1 x t2).
Proof. exact (TRANS (@lem7184345 A t1 x t2) (@lem7184344 A t1 x t2)). Qed.
Lemma lem7184347 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7184348 {A : Type'} (t : A -> Prop) (t2 : A -> Prop) (s : type686 A) : (term306 A t t2 s) = (term307 A t t2 s).
Proof. exact (MK_COMB (@lem7184347) (@lem7184331 A t t2 s)). Qed.
Lemma lem7184349 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term308 A t s t1 x t2) = (term309 A t s t1 x t2).
Proof. exact (MK_COMB (@lem7184348 A t t2 s) (@lem7184346 A t1 x t2)). Qed.
Lemma lem7184350 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term310 A t s t1 x t2) = (term308 A t s t1 x t2).
Proof. exact (@lem17045 (term100 A t t2 s) (term113 A t1 x t2)). Qed.
Lemma lem7184351 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term310 A t s t1 x t2) = (term309 A t s t1 x t2).
Proof. exact (TRANS (@lem7184350 A t s t1 x t2) (@lem7184349 A t s t1 x t2)). Qed.
Lemma lem7184352 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7184353 {A : Type'} (t : A -> Prop) (t1 : A -> Prop) (s : type686 A) : (term306 A t t1 s) = (term307 A t t1 s).
Proof. exact (MK_COMB (@lem7184352) (@lem7184324 A t t1 s)). Qed.
Lemma lem7184354 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term311 A t s t1 x t2) = (term312 A t s t1 x t2).
Proof. exact (MK_COMB (@lem7184353 A t t1 s) (@lem7184351 A t s t1 x t2)). Qed.
Lemma lem7184355 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term313 A t s t1 x t2) = (term311 A t s t1 x t2).
Proof. exact (@lem17045 (term100 A t t1 s) (term115 A t s t1 x t2)). Qed.
Lemma lem7184356 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term313 A t s t1 x t2) = (term312 A t s t1 x t2).
Proof. exact (TRANS (@lem7184355 A t s t1 x t2) (@lem7184354 A t s t1 x t2)). Qed.
Lemma lem7184357 {A : Type'} (f : A -> real) (x : A) : ((f x) = term34) = ((f x) = term34).
Proof. exact (eq_refl ((f x) = term34)). Qed.
Lemma lem7184358 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7184359 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term314 A t s t1 x t2) = (term315 A t s t1 x t2).
Proof. exact (MK_COMB (@lem7184358) (@lem7184356 A t s t1 x t2)). Qed.
Lemma lem7184360 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> real) (x : A) : (term316 A t s t1 t2 f x) = (term317 A t s t1 t2 f x).
Proof. exact (MK_COMB (@lem7184359 A t s t1 x t2) (@lem7184357 A f x)). Qed.
Lemma lem7184361 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> real) (x : A) : (term121 A t s t1 t2 f x) = (term316 A t s t1 t2 f x).
Proof. exact (@lem17265 (term117 A t s t1 x t2) ((f x) = term34)). Qed.
Lemma lem7184362 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> real) (x : A) : (term121 A t s t1 t2 f x) = (term317 A t s t1 t2 f x).
Proof. exact (TRANS (@lem7184361 A t s t1 t2 f x) (@lem7184360 A t s t1 t2 f x)). Qed.
Lemma lem7184363 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> real) : (term123 A t s t1 t2 f) = (term318 A t s t1 t2 f).
Proof. exact (fun_ext (fun x : A => @lem7184362 A t s t1 t2 f x)). Qed.
Lemma lem7184364 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7184365 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> real) : (term125 A t s t1 t2 f) = (term319 A t s t1 t2 f).
Proof. exact (MK_COMB (@lem7184364 A) (@lem7184363 A t s t1 t2 f)). Qed.
Lemma lem7184366 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (f : A -> real) : (term127 A t s t1 f) = (term320 A t s t1 f).
Proof. exact (fun_ext (fun t2 : A -> Prop => @lem7184365 A t s t1 t2 f)). Qed.
Lemma lem7184367 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7184368 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (f : A -> real) : (term129 A t s t1 f) = (term321 A t s t1 f).
Proof. exact (MK_COMB (@lem7184367 A) (@lem7184366 A t s t1 f)). Qed.
Lemma lem7184369 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term131 A t s f) = (term322 A t s f).
Proof. exact (fun_ext (fun t1 : A -> Prop => @lem7184368 A t s t1 f)). Qed.
Lemma lem7184370 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7184431 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term133 A t s f) = (term323 A t s f).
Proof. exact (MK_COMB (@lem7184370 A) (@lem7184369 A t s f)). Qed.
Lemma lem7184432 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term133 A t s f) : term323 A t s f.
Proof. exact (EQ_MP (@lem7184431 A t s f) (@lem7184258 A t s f h1)). Qed.
Lemma lem7184454 {A : Type'} (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term324 A s t1 x t2) : term324 A s t1 x t2.
Proof. exact (h1). Qed.
Lemma lem7184460 {A : Type'} (f : A -> real) (x : A) (h1 : term294 A f x) : term294 A f x.
Proof. exact (h1). Qed.
Lemma lem7184566 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> real) (x : A) : (term317 A t s t1 t2 f x) = (term317 A t s t1 t2 f x).
Proof. exact (eq_refl (term317 A t s t1 t2 f x)). Qed.
Lemma lem7184567 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> real) : (term318 A t s t1 t2 f) = (term318 A t s t1 t2 f).
Proof. exact (fun_ext (fun x : A => @lem7184566 A t s t1 t2 f x)). Qed.
Lemma lem7184568 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7184569 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> real) : (term319 A t s t1 t2 f) = (term319 A t s t1 t2 f).
Proof. exact (MK_COMB (@lem7184568 A) (@lem7184567 A t s t1 t2 f)). Qed.
Lemma lem7184570 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (f : A -> real) : (term320 A t s t1 f) = (term320 A t s t1 f).
Proof. exact (fun_ext (fun t2 : A -> Prop => @lem7184569 A t s t1 t2 f)). Qed.
Lemma lem7184571 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7184572 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (f : A -> real) : (term321 A t s t1 f) = (term321 A t s t1 f).
Proof. exact (MK_COMB (@lem7184571 A) (@lem7184570 A t s t1 f)). Qed.
Lemma lem7184573 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term322 A t s f) = (term322 A t s f).
Proof. exact (fun_ext (fun t1 : A -> Prop => @lem7184572 A t s t1 f)). Qed.
Lemma lem7184574 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7184575 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term323 A t s f) = (term323 A t s f).
Proof. exact (MK_COMB (@lem7184574 A) (@lem7184573 A t s f)). Qed.
Lemma lem7184576 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term133 A t s f) : term323 A t s f.
Proof. exact (EQ_MP (@lem7184575 A t s f) (@lem7184432 A t s f h1)). Qed.
Lemma lem7184616 {A : Type'} (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term324 A s t1 x t2) : term324 A s t1 x t2.
Proof. exact (h1). Qed.
Lemma lem7184630 {A : Type'} (f : A -> real) (x : A) (h1 : term294 A f x) : term294 A f x.
Proof. exact (h1). Qed.
Lemma lem7184631 {A : Type'} (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term324 A s t1 x t2) : term325 A s t1 x t2.
Proof. exact (proj2 (@lem7184616 A s t1 x t2 h1)). Qed.
Lemma lem7184633 {A : Type'} (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term324 A s t1 x t2) : term113 A t1 x t2.
Proof. exact (proj2 (@lem7184631 A s t1 x t2 h1)). Qed.
Lemma lem7184635 {A : Type'} (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term324 A s t1 x t2) : term305 A t1 x t2.
Proof. exact (proj2 (@lem7184633 A s t1 x t2 h1)). Qed.
Lemma lem7184663 {A : Type'} (f : A -> real) (x : A) : ((f x) = term34) = ((f x) = term34).
Proof. exact (eq_refl ((f x) = term34)). Qed.
Lemma lem7184692 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term309 A t s t1 x t2) = (term326 A t s t1 x t2).
Proof. exact (@lem19699 (term304 A t2 t) (term217 A t2 s) (term302 A t1 x t2)). Qed.
Lemma lem7184699 {A : Type'} (t : A -> Prop) (t1 : A -> Prop) (s : type686 A) : (term307 A t t1 s) = (term307 A t t1 s).
Proof. exact (eq_refl (term307 A t t1 s)). Qed.
Lemma lem7184700 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term312 A t s t1 x t2) = (term327 A t s t1 x t2).
Proof. exact (MK_COMB (@lem7184699 A t t1 s) (@lem7184692 A t s t1 x t2)). Qed.
Lemma lem7184701 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term327 A t s t1 x t2) = (term328 A t s t1 x t2).
Proof. exact (@lem19490 (term329 A t t1 x t2) (term296 A t t1 s) (term330 A s t1 x t2)). Qed.
Lemma lem7184708 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term331 A t s t1 x t2) = (term332 A t s t1 x t2).
Proof. exact (@lem19699 (term304 A t1 t) (term217 A t1 s) (term330 A s t1 x t2)). Qed.
Lemma lem7184715 {A : Type'} (s : type686 A) (t : A -> Prop) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term333 A s t t1 x t2) = (term334 A s t t1 x t2).
Proof. exact (@lem19699 (term304 A t1 t) (term217 A t1 s) (term329 A t t1 x t2)). Qed.
Lemma lem7184716 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7184717 {A : Type'} (s : type686 A) (t : A -> Prop) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term335 A s t t1 x t2) = (term336 A s t t1 x t2).
Proof. exact (MK_COMB (@lem7184716) (@lem7184715 A s t t1 x t2)). Qed.
Lemma lem7184718 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term328 A t s t1 x t2) = (term337 A t s t1 x t2).
Proof. exact (MK_COMB (@lem7184717 A s t t1 x t2) (@lem7184708 A t s t1 x t2)). Qed.
Lemma lem7184719 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term327 A t s t1 x t2) = (term337 A t s t1 x t2).
Proof. exact (TRANS (@lem7184701 A t s t1 x t2) (@lem7184718 A t s t1 x t2)). Qed.
Lemma lem7184720 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term312 A t s t1 x t2) = (term337 A t s t1 x t2).
Proof. exact (TRANS (@lem7184700 A t s t1 x t2) (@lem7184719 A t s t1 x t2)). Qed.
Lemma lem7184721 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7184722 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term315 A t s t1 x t2) = (term338 A t s t1 x t2).
Proof. exact (MK_COMB (@lem7184721) (@lem7184720 A t s t1 x t2)). Qed.
Lemma lem7184723 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> real) (x : A) : (term317 A t s t1 t2 f x) = (term339 A t s t1 t2 f x).
Proof. exact (MK_COMB (@lem7184722 A t s t1 x t2) (@lem7184663 A f x)). Qed.
Lemma lem7184724 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> real) (x : A) : (term339 A t s t1 t2 f x) = (term340 A t s t1 t2 f x).
Proof. exact (@lem19699 (term334 A s t t1 x t2) (term332 A t s t1 x t2) ((f x) = term34)). Qed.
Lemma lem7184731 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> real) (x : A) : (term341 A t s t1 t2 f x) = (term342 A t s t1 t2 f x).
Proof. exact (@lem19699 (term343 A t s t1 x t2) (term344 A s t1 x t2) ((f x) = term34)). Qed.
Lemma lem7184738 {A : Type'} (s : type686 A) (t : A -> Prop) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> real) (x : A) : (term345 A s t t1 t2 f x) = (term346 A s t t1 t2 f x).
Proof. exact (@lem19699 (term347 A t t1 x t2) (term348 A s t t1 x t2) ((f x) = term34)). Qed.
Lemma lem7184739 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7184740 {A : Type'} (s : type686 A) (t : A -> Prop) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> real) (x : A) : (term349 A s t t1 t2 f x) = (term350 A s t t1 t2 f x).
Proof. exact (MK_COMB (@lem7184739) (@lem7184738 A s t t1 t2 f x)). Qed.
Lemma lem7184741 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> real) (x : A) : (term340 A t s t1 t2 f x) = (term351 A t s t1 t2 f x).
Proof. exact (MK_COMB (@lem7184740 A s t t1 t2 f x) (@lem7184731 A t s t1 t2 f x)). Qed.
Lemma lem7184742 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> real) (x : A) : (term339 A t s t1 t2 f x) = (term351 A t s t1 t2 f x).
Proof. exact (TRANS (@lem7184724 A t s t1 t2 f x) (@lem7184741 A t s t1 t2 f x)). Qed.
Lemma lem7184743 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> real) (x : A) : (term317 A t s t1 t2 f x) = (term351 A t s t1 t2 f x).
Proof. exact (TRANS (@lem7184723 A t s t1 t2 f x) (@lem7184742 A t s t1 t2 f x)). Qed.
Lemma lem7184744 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> real) : (term318 A t s t1 t2 f) = (term352 A t s t1 t2 f).
Proof. exact (fun_ext (fun x : A => @lem7184743 A t s t1 t2 f x)). Qed.
Lemma lem7184745 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7184746 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> real) : (term319 A t s t1 t2 f) = (term353 A t s t1 t2 f).
Proof. exact (MK_COMB (@lem7184745 A) (@lem7184744 A t s t1 t2 f)). Qed.
Lemma lem7184747 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (f : A -> real) : (term320 A t s t1 f) = (term354 A t s t1 f).
Proof. exact (fun_ext (fun t2 : A -> Prop => @lem7184746 A t s t1 t2 f)). Qed.
Lemma lem7184748 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7184749 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (f : A -> real) : (term321 A t s t1 f) = (term355 A t s t1 f).
Proof. exact (MK_COMB (@lem7184748 A) (@lem7184747 A t s t1 f)). Qed.
Lemma lem7184750 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term322 A t s f) = (term356 A t s f).
Proof. exact (fun_ext (fun t1 : A -> Prop => @lem7184749 A t s t1 f)). Qed.
Lemma lem7184751 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7184753 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term323 A t s f) = (term357 A t s f).
Proof. exact (MK_COMB (@lem7184751 A) (@lem7184750 A t s f)). Qed.
Lemma lem7184754 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term133 A t s f) : term357 A t s f.
Proof. exact (EQ_MP (@lem7184753 A t s f) (@lem7184576 A t s f h1)). Qed.
Lemma lem7184758 {A : Type'} (f : A -> real) (x : A) (h1 : term294 A f x) : term294 A f x.
Proof. exact (h1). Qed.
Lemma lem7184782 {A : Type'} (_96196 : A -> Prop) (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term133 A t s f) : term358 A t s f _96196.
Proof. exact (@lem7184754 A t s f h1 _96196). Qed.
Lemma lem7184783 {A : Type'} (t : A -> Prop) (s : type686 A) (_96196 : A -> Prop) (f : A -> real) : (term358 A t s f _96196) = (term355 A t s _96196 f).
Proof. exact (eq_refl (term358 A t s f _96196)). Qed.
Lemma lem7184784 {A : Type'} (_96196 : A -> Prop) (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term133 A t s f) : term355 A t s _96196 f.
Proof. exact (EQ_MP (@lem7184783 A t s _96196 f) (@lem7184782 A _96196 t s f h1)). Qed.
Lemma lem7184785 {A : Type'} (_96196 : A -> Prop) (_96197 : A -> Prop) (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term133 A t s f) : term359 A t s _96196 f _96197.
Proof. exact (@lem7184784 A _96196 t s f h1 _96197). Qed.
Lemma lem7184786 {A : Type'} (t : A -> Prop) (s : type686 A) (_96196 : A -> Prop) (_96197 : A -> Prop) (f : A -> real) : (term359 A t s _96196 f _96197) = (term353 A t s _96196 _96197 f).
Proof. exact (eq_refl (term359 A t s _96196 f _96197)). Qed.
Lemma lem7184787 {A : Type'} (_96196 : A -> Prop) (_96197 : A -> Prop) (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term133 A t s f) : term353 A t s _96196 _96197 f.
Proof. exact (EQ_MP (@lem7184786 A t s _96196 _96197 f) (@lem7184785 A _96196 _96197 t s f h1)). Qed.
Lemma lem7184788 {A : Type'} (_96196 : A -> Prop) (_96197 : A -> Prop) (_96198 : A) (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term133 A t s f) : term360 A t s _96196 _96197 f _96198.
Proof. exact (@lem7184787 A _96196 _96197 t s f h1 _96198). Qed.
Lemma lem7184789 {A : Type'} (t : A -> Prop) (s : type686 A) (_96196 : A -> Prop) (_96197 : A -> Prop) (f : A -> real) (_96198 : A) : (term360 A t s _96196 _96197 f _96198) = (term351 A t s _96196 _96197 f _96198).
Proof. exact (eq_refl (term360 A t s _96196 _96197 f _96198)). Qed.
Lemma lem7184790 {A : Type'} (_96196 : A -> Prop) (_96197 : A -> Prop) (_96198 : A) (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term133 A t s f) : term351 A t s _96196 _96197 f _96198.
Proof. exact (EQ_MP (@lem7184789 A t s _96196 _96197 f _96198) (@lem7184788 A _96196 _96197 _96198 t s f h1)). Qed.
Lemma lem7184791 {A : Type'} (_96196 : A -> Prop) (_96197 : A -> Prop) (_96198 : A) (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term133 A t s f) : term342 A t s _96196 _96197 f _96198.
Proof. exact (proj2 (@lem7184790 A _96196 _96197 _96198 t s f h1)). Qed.
Lemma lem7184793 {A : Type'} (_96196 : A -> Prop) (_96197 : A -> Prop) (_96198 : A) (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term133 A t s f) : term361 A s _96196 _96197 f _96198.
Proof. exact (proj2 (@lem7184791 A _96196 _96197 _96198 t s f h1)). Qed.
Lemma lem7184800 {A : Type'} (f : A -> real) (x : A) (h1 : term294 A f x) : term294 A f x.
Proof. exact (h1). Qed.
Lemma lem7184806 {A : Type'} (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term324 A s t1 x t2) : term304 A t1 t2.
Proof. exact (proj1 (@lem7184633 A s t1 x t2 h1)). Qed.
Lemma lem7184844 {A : Type'} (s : type686 A) (_96196 : A -> Prop) (_96197 : A -> Prop) (f : A -> real) (_96198 : A) : (term361 A s _96196 _96197 f _96198) = (term362 A s _96196 _96197 f _96198).
Proof. exact (@lem7178858 (term217 A _96196 s) (term330 A s _96196 _96198 _96197) ((f _96198) = term34)). Qed.
Lemma lem7184845 {A : Type'} (s : type686 A) (_96196 : A -> Prop) (_96197 : A -> Prop) (f : A -> real) (_96198 : A) : (term363 A s _96196 _96197 f _96198) = (term364 A s _96196 _96197 f _96198).
Proof. exact (@lem7178858 (term217 A _96197 s) (term302 A _96196 _96198 _96197) ((f _96198) = term34)). Qed.
Lemma lem7184846 {A : Type'} (_96196 : A -> Prop) (_96197 : A -> Prop) (f : A -> real) (_96198 : A) : (term365 A _96196 _96197 f _96198) = (term366 A _96196 _96197 f _96198).
Proof. exact (@lem7178858 (_96196 = _96197) (term299 A _96196 _96198 _96197) ((f _96198) = term34)). Qed.
Lemma lem7184853 {A : Type'} (_96196 : A -> Prop) (_96197 : A -> Prop) (f : A -> real) (_96198 : A) : (term367 A _96196 _96197 f _96198) = (term368 A _96196 _96197 f _96198).
Proof. exact (@lem7178858 (term369 A _96198 _96196) (term369 A _96198 _96197) ((f _96198) = term34)). Qed.
Lemma lem7184854 {A : Type'} (_96196 : A -> Prop) (_96197 : A -> Prop) : (term188 A _96196 _96197) = (term188 A _96196 _96197).
Proof. exact (eq_refl (term188 A _96196 _96197)). Qed.
Lemma lem7184857 {A : Type'} (_96196 : A -> Prop) (_96197 : A -> Prop) (f : A -> real) (_96198 : A) : (term366 A _96196 _96197 f _96198) = (term370 A _96196 _96197 f _96198).
Proof. exact (MK_COMB (@lem7184854 A _96196 _96197) (@lem7184853 A _96196 _96197 f _96198)). Qed.
Lemma lem7184858 {A : Type'} (_96196 : A -> Prop) (_96197 : A -> Prop) (f : A -> real) (_96198 : A) : (term365 A _96196 _96197 f _96198) = (term370 A _96196 _96197 f _96198).
Proof. exact (TRANS (@lem7184846 A _96196 _96197 f _96198) (@lem7184857 A _96196 _96197 f _96198)). Qed.
Lemma lem7184859 {A : Type'} (_96197 : A -> Prop) (s : type686 A) : (term371 A _96197 s) = (term371 A _96197 s).
Proof. exact (eq_refl (term371 A _96197 s)). Qed.
Lemma lem7184862 {A : Type'} (s : type686 A) (_96196 : A -> Prop) (_96197 : A -> Prop) (f : A -> real) (_96198 : A) : (term364 A s _96196 _96197 f _96198) = (term372 A s _96196 _96197 f _96198).
Proof. exact (MK_COMB (@lem7184859 A _96197 s) (@lem7184858 A _96196 _96197 f _96198)). Qed.
Lemma lem7184863 {A : Type'} (s : type686 A) (_96196 : A -> Prop) (_96197 : A -> Prop) (f : A -> real) (_96198 : A) : (term363 A s _96196 _96197 f _96198) = (term372 A s _96196 _96197 f _96198).
Proof. exact (TRANS (@lem7184845 A s _96196 _96197 f _96198) (@lem7184862 A s _96196 _96197 f _96198)). Qed.
Lemma lem7184864 {A : Type'} (_96196 : A -> Prop) (s : type686 A) : (term371 A _96196 s) = (term371 A _96196 s).
Proof. exact (eq_refl (term371 A _96196 s)). Qed.
Lemma lem7184867 {A : Type'} (s : type686 A) (_96196 : A -> Prop) (_96197 : A -> Prop) (f : A -> real) (_96198 : A) : (term362 A s _96196 _96197 f _96198) = (term373 A s _96196 _96197 f _96198).
Proof. exact (MK_COMB (@lem7184864 A _96196 s) (@lem7184863 A s _96196 _96197 f _96198)). Qed.
Lemma lem7184869 {A : Type'} (s : type686 A) (_96196 : A -> Prop) (_96197 : A -> Prop) (f : A -> real) (_96198 : A) : (term361 A s _96196 _96197 f _96198) = (term373 A s _96196 _96197 f _96198).
Proof. exact (TRANS (@lem7184844 A s _96196 _96197 f _96198) (@lem7184867 A s _96196 _96197 f _96198)). Qed.
Lemma lem7184870 {A : Type'} (_96196 : A -> Prop) (_96197 : A -> Prop) (_96198 : A) (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term133 A t s f) : term373 A s _96196 _96197 f _96198.
Proof. exact (EQ_MP (@lem7184869 A s _96196 _96197 f _96198) (@lem7184793 A _96196 _96197 _96198 t s f h1)). Qed.
Lemma lem7185028 {A : Type'} (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term324 A s t1 x t2) : @IN (A -> Prop) t1 s.
Proof. exact (proj1 (@lem7184616 A s t1 x t2 h1)). Qed.
Lemma lem7185029 {A : Type'} (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term324 A s t1 x t2) : term374 A t1 s.
Proof. exact (fun h0 : term217 A t1 s => @lem7185028 A s t1 x t2 h1). Qed.
Lemma lem7185031 (p : Prop) : (term375 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7185032 {A : Type'} (t1 : A -> Prop) (s : type686 A) : (term374 A t1 s) = (@IN (A -> Prop) t1 s).
Proof. exact (@lem7185031 (@IN (A -> Prop) t1 s)). Qed.
Lemma lem7185033 {A : Type'} (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term324 A s t1 x t2) : @IN (A -> Prop) t1 s.
Proof. exact (EQ_MP (@lem7185032 A t1 s) (@lem7185029 A s t1 x t2 h1)). Qed.
Lemma lem7185035 {A : Type'} (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term324 A s t1 x t2) : @IN (A -> Prop) t2 s.
Proof. exact (proj1 (@lem7184631 A s t1 x t2 h1)). Qed.
Lemma lem7185036 {A : Type'} (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term324 A s t1 x t2) : term374 A t2 s.
Proof. exact (fun h0 : term217 A t2 s => @lem7185035 A s t1 x t2 h1). Qed.
Lemma lem7185038 (p : Prop) : (term375 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7185039 {A : Type'} (t2 : A -> Prop) (s : type686 A) : (term374 A t2 s) = (@IN (A -> Prop) t2 s).
Proof. exact (@lem7185038 (@IN (A -> Prop) t2 s)). Qed.
Lemma lem7185040 {A : Type'} (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term324 A s t1 x t2) : @IN (A -> Prop) t2 s.
Proof. exact (EQ_MP (@lem7185039 A t2 s) (@lem7185036 A s t1 x t2 h1)). Qed.
Lemma lem7185042 {A : Type'} (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term324 A s t1 x t2) : @IN A x t1.
Proof. exact (proj1 (@lem7184635 A s t1 x t2 h1)). Qed.
Lemma lem7185043 {A : Type'} (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term324 A s t1 x t2) : term376 A x t1.
Proof. exact (fun h0 : term369 A x t1 => @lem7185042 A s t1 x t2 h1). Qed.
Lemma lem7185045 (p : Prop) : (term375 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7185046 {A : Type'} (x : A) (t1 : A -> Prop) : (term376 A x t1) = (@IN A x t1).
Proof. exact (@lem7185045 (@IN A x t1)). Qed.
Lemma lem7185047 {A : Type'} (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term324 A s t1 x t2) : @IN A x t1.
Proof. exact (EQ_MP (@lem7185046 A x t1) (@lem7185043 A s t1 x t2 h1)). Qed.
Lemma lem7185049 {A : Type'} (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term324 A s t1 x t2) : @IN A x t2.
Proof. exact (proj2 (@lem7184635 A s t1 x t2 h1)). Qed.
Lemma lem7185050 {A : Type'} (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term324 A s t1 x t2) : term376 A x t2.
Proof. exact (fun h0 : term369 A x t2 => @lem7185049 A s t1 x t2 h1). Qed.
Lemma lem7185052 (p : Prop) : (term375 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7185053 {A : Type'} (x : A) (t2 : A -> Prop) : (term376 A x t2) = (@IN A x t2).
Proof. exact (@lem7185052 (@IN A x t2)). Qed.
Lemma lem7185054 {A : Type'} (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term324 A s t1 x t2) : @IN A x t2.
Proof. exact (EQ_MP (@lem7185053 A x t2) (@lem7185050 A s t1 x t2 h1)). Qed.
Lemma lem7185056 {A : Type'} (f : A -> real) (x : A) (h1 : term294 A f x) : term294 A f x.
Proof. exact (h1). Qed.
Lemma lem7185057 {A : Type'} (f : A -> real) (x : A) (h1 : term294 A f x) : term377 A f x.
Proof. exact (fun h0 : (f x) = term34 => @lem7185056 A f x h1). Qed.
Lemma lem7185059 (p : Prop) : (term378 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7185060 {A : Type'} (f : A -> real) (x : A) : (term377 A f x) = (term294 A f x).
Proof. exact (@lem7185059 ((f x) = term34)). Qed.
Lemma lem7185061 {A : Type'} (f : A -> real) (x : A) (h1 : term294 A f x) : term294 A f x.
Proof. exact (EQ_MP (@lem7185060 A f x) (@lem7185057 A f x h1)). Qed.
Lemma lem7185077 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7185078 {A : Type'} (s : type686 A) (_96196 : A -> Prop) (_96197 : A -> Prop) (f : A -> real) (_96198 : A) : (term372 A s _96196 _96197 f _96198) = (term379 A s _96196 _96197 f _96198).
Proof. exact (@lem7185077 (_96196 = _96197) (term217 A _96197 s) (term368 A _96196 _96197 f _96198)). Qed.
Lemma lem7185094 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7185095 {A : Type'} (_96196 : A -> Prop) (s : type686 A) (_96197 : A -> Prop) (f : A -> real) (_96198 : A) : (term380 A s _96196 _96197 f _96198) = (term381 A _96196 s _96197 f _96198).
Proof. exact (@lem7185094 (term369 A _96198 _96196) (term217 A _96197 s) (term382 A _96197 f _96198)). Qed.
Lemma lem7185109 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7185110 {A : Type'} (_96197 : A -> Prop) (s : type686 A) (f : A -> real) (_96198 : A) : (term383 A s _96197 f _96198) = (term384 A _96197 s f _96198).
Proof. exact (@lem7185109 (term369 A _96198 _96197) (term217 A _96197 s) ((f _96198) = term34)). Qed.
Lemma lem7185124 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7185125 {A : Type'} (f : A -> real) (_96198 : A) (_96197 : A -> Prop) (s : type686 A) : (term385 A _96197 s f _96198) = (term386 A f _96198 _96197 s).
Proof. exact (@lem7185124 ((f _96198) = term34) (term217 A _96197 s)). Qed.
Lemma lem7185133 {A : Type'} (_96198 : A) (_96197 : A -> Prop) : (term387 A _96198 _96197) = (term387 A _96198 _96197).
Proof. exact (eq_refl (term387 A _96198 _96197)). Qed.
Lemma lem7185134 {A : Type'} (f : A -> real) (_96198 : A) (_96197 : A -> Prop) (s : type686 A) : (term384 A _96197 s f _96198) = (term388 A f _96198 _96197 s).
Proof. exact (MK_COMB (@lem7185133 A _96198 _96197) (@lem7185125 A f _96198 _96197 s)). Qed.
Lemma lem7185138 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7185139 {A : Type'} (f : A -> real) (_96198 : A) (_96197 : A -> Prop) (s : type686 A) : (term388 A f _96198 _96197 s) = (term389 A f _96198 _96197 s).
Proof. exact (@lem7185138 ((f _96198) = term34) (term369 A _96198 _96197) (term217 A _96197 s)). Qed.
Lemma lem7185157 {A : Type'} (f : A -> real) (_96198 : A) (_96197 : A -> Prop) (s : type686 A) : (term384 A _96197 s f _96198) = (term389 A f _96198 _96197 s).
Proof. exact (TRANS (@lem7185134 A f _96198 _96197 s) (@lem7185139 A f _96198 _96197 s)). Qed.
Lemma lem7185158 {A : Type'} (f : A -> real) (_96198 : A) (_96197 : A -> Prop) (s : type686 A) : (term383 A s _96197 f _96198) = (term389 A f _96198 _96197 s).
Proof. exact (TRANS (@lem7185110 A _96197 s f _96198) (@lem7185157 A f _96198 _96197 s)). Qed.
Lemma lem7185159 {A : Type'} (_96198 : A) (_96196 : A -> Prop) : (term387 A _96198 _96196) = (term387 A _96198 _96196).
Proof. exact (eq_refl (term387 A _96198 _96196)). Qed.
Lemma lem7185160 {A : Type'} (_96196 : A -> Prop) (f : A -> real) (_96198 : A) (_96197 : A -> Prop) (s : type686 A) : (term381 A _96196 s _96197 f _96198) = (term390 A _96196 f _96198 _96197 s).
Proof. exact (MK_COMB (@lem7185159 A _96198 _96196) (@lem7185158 A f _96198 _96197 s)). Qed.
Lemma lem7185164 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7185165 {A : Type'} (f : A -> real) (_96196 : A -> Prop) (_96198 : A) (_96197 : A -> Prop) (s : type686 A) : (term390 A _96196 f _96198 _96197 s) = (term391 A f _96196 _96198 _96197 s).
Proof. exact (@lem7185164 ((f _96198) = term34) (term369 A _96198 _96196) (term392 A _96198 _96197 s)). Qed.
Lemma lem7185193 {A : Type'} (f : A -> real) (_96196 : A -> Prop) (_96198 : A) (_96197 : A -> Prop) (s : type686 A) : (term381 A _96196 s _96197 f _96198) = (term391 A f _96196 _96198 _96197 s).
Proof. exact (TRANS (@lem7185160 A _96196 f _96198 _96197 s) (@lem7185165 A f _96196 _96198 _96197 s)). Qed.
Lemma lem7185194 {A : Type'} (f : A -> real) (_96196 : A -> Prop) (_96198 : A) (_96197 : A -> Prop) (s : type686 A) : (term380 A s _96196 _96197 f _96198) = (term391 A f _96196 _96198 _96197 s).
Proof. exact (TRANS (@lem7185095 A _96196 s _96197 f _96198) (@lem7185193 A f _96196 _96198 _96197 s)). Qed.
Lemma lem7185195 {A : Type'} (_96196 : A -> Prop) (_96197 : A -> Prop) : (term188 A _96196 _96197) = (term188 A _96196 _96197).
Proof. exact (eq_refl (term188 A _96196 _96197)). Qed.
Lemma lem7185196 {A : Type'} (f : A -> real) (_96196 : A -> Prop) (_96198 : A) (_96197 : A -> Prop) (s : type686 A) : (term379 A s _96196 _96197 f _96198) = (term393 A f _96196 _96198 _96197 s).
Proof. exact (MK_COMB (@lem7185195 A _96196 _96197) (@lem7185194 A f _96196 _96198 _96197 s)). Qed.
Lemma lem7185207 {A : Type'} (f : A -> real) (_96196 : A -> Prop) (_96198 : A) (_96197 : A -> Prop) (s : type686 A) : (term372 A s _96196 _96197 f _96198) = (term393 A f _96196 _96198 _96197 s).
Proof. exact (TRANS (@lem7185078 A s _96196 _96197 f _96198) (@lem7185196 A f _96196 _96198 _96197 s)). Qed.
Lemma lem7185208 {A : Type'} (_96196 : A -> Prop) (s : type686 A) : (term371 A _96196 s) = (term371 A _96196 s).
Proof. exact (eq_refl (term371 A _96196 s)). Qed.
Lemma lem7185209 {A : Type'} (f : A -> real) (_96196 : A -> Prop) (_96198 : A) (_96197 : A -> Prop) (s : type686 A) : (term373 A s _96196 _96197 f _96198) = (term394 A f _96196 _96198 _96197 s).
Proof. exact (MK_COMB (@lem7185208 A _96196 s) (@lem7185207 A f _96196 _96198 _96197 s)). Qed.
Lemma lem7185213 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7185214 {A : Type'} (f : A -> real) (_96196 : A -> Prop) (_96198 : A) (_96197 : A -> Prop) (s : type686 A) : (term394 A f _96196 _96198 _96197 s) = (term395 A f _96196 _96198 _96197 s).
Proof. exact (@lem7185213 (_96196 = _96197) (term217 A _96196 s) (term391 A f _96196 _96198 _96197 s)). Qed.
Lemma lem7185230 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7185231 {A : Type'} (f : A -> real) (_96196 : A -> Prop) (_96198 : A) (_96197 : A -> Prop) (s : type686 A) : (term396 A f _96196 _96198 _96197 s) = (term397 A f _96196 _96198 _96197 s).
Proof. exact (@lem7185230 ((f _96198) = term34) (term217 A _96196 s) (term398 A _96196 _96198 _96197 s)). Qed.
Lemma lem7185247 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7185248 {A : Type'} (_96196 : A -> Prop) (_96198 : A) (_96197 : A -> Prop) (s : type686 A) : (term399 A _96196 _96198 _96197 s) = (term400 A _96196 _96198 _96197 s).
Proof. exact (@lem7185247 (term369 A _96198 _96196) (term217 A _96196 s) (term392 A _96198 _96197 s)). Qed.
Lemma lem7185262 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7185263 {A : Type'} (_96198 : A) (_96196 : A -> Prop) (_96197 : A -> Prop) (s : type686 A) : (term401 A _96196 _96198 _96197 s) = (term402 A _96198 _96196 _96197 s).
Proof. exact (@lem7185262 (term369 A _96198 _96197) (term217 A _96196 s) (term217 A _96197 s)). Qed.
Lemma lem7185279 {A : Type'} (_96198 : A) (_96196 : A -> Prop) : (term387 A _96198 _96196) = (term387 A _96198 _96196).
Proof. exact (eq_refl (term387 A _96198 _96196)). Qed.
Lemma lem7185280 {A : Type'} (_96198 : A) (_96196 : A -> Prop) (_96197 : A -> Prop) (s : type686 A) : (term400 A _96196 _96198 _96197 s) = (term403 A _96198 _96196 _96197 s).
Proof. exact (MK_COMB (@lem7185279 A _96198 _96196) (@lem7185263 A _96198 _96196 _96197 s)). Qed.
Lemma lem7185291 {A : Type'} (_96198 : A) (_96196 : A -> Prop) (_96197 : A -> Prop) (s : type686 A) : (term399 A _96196 _96198 _96197 s) = (term403 A _96198 _96196 _96197 s).
Proof. exact (TRANS (@lem7185248 A _96196 _96198 _96197 s) (@lem7185280 A _96198 _96196 _96197 s)). Qed.
Lemma lem7185292 {A : Type'} (f : A -> real) (_96198 : A) : (term404 A f _96198) = (term404 A f _96198).
Proof. exact (eq_refl (term404 A f _96198)). Qed.
Lemma lem7185293 {A : Type'} (f : A -> real) (_96198 : A) (_96196 : A -> Prop) (_96197 : A -> Prop) (s : type686 A) : (term397 A f _96196 _96198 _96197 s) = (term405 A f _96198 _96196 _96197 s).
Proof. exact (MK_COMB (@lem7185292 A f _96198) (@lem7185291 A _96198 _96196 _96197 s)). Qed.
Lemma lem7185304 {A : Type'} (f : A -> real) (_96198 : A) (_96196 : A -> Prop) (_96197 : A -> Prop) (s : type686 A) : (term396 A f _96196 _96198 _96197 s) = (term405 A f _96198 _96196 _96197 s).
Proof. exact (TRANS (@lem7185231 A f _96196 _96198 _96197 s) (@lem7185293 A f _96198 _96196 _96197 s)). Qed.
Lemma lem7185305 {A : Type'} (_96196 : A -> Prop) (_96197 : A -> Prop) : (term188 A _96196 _96197) = (term188 A _96196 _96197).
Proof. exact (eq_refl (term188 A _96196 _96197)). Qed.
Lemma lem7185306 {A : Type'} (f : A -> real) (_96198 : A) (_96196 : A -> Prop) (_96197 : A -> Prop) (s : type686 A) : (term395 A f _96196 _96198 _96197 s) = (term406 A f _96198 _96196 _96197 s).
Proof. exact (MK_COMB (@lem7185305 A _96196 _96197) (@lem7185304 A f _96198 _96196 _96197 s)). Qed.
Lemma lem7185317 {A : Type'} (f : A -> real) (_96198 : A) (_96196 : A -> Prop) (_96197 : A -> Prop) (s : type686 A) : (term394 A f _96196 _96198 _96197 s) = (term406 A f _96198 _96196 _96197 s).
Proof. exact (TRANS (@lem7185214 A f _96196 _96198 _96197 s) (@lem7185306 A f _96198 _96196 _96197 s)). Qed.
Lemma lem7185318 {A : Type'} (f : A -> real) (_96198 : A) (_96196 : A -> Prop) (_96197 : A -> Prop) (s : type686 A) : (term373 A s _96196 _96197 f _96198) = (term406 A f _96198 _96196 _96197 s).
Proof. exact (TRANS (@lem7185209 A f _96196 _96198 _96197 s) (@lem7185317 A f _96198 _96196 _96197 s)). Qed.
Lemma lem7185319 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7185320 {A : Type'} (f : A -> real) (_96198 : A) (_96196 : A -> Prop) (_96197 : A -> Prop) (s : type686 A) : (term407 A s _96196 _96197 f _96198) = (term408 A f _96198 _96196 _96197 s).
Proof. exact (MK_COMB (@lem7185319) (@lem7185318 A f _96198 _96196 _96197 s)). Qed.
Lemma lem7185346 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7185347 {A : Type'} (_96196 : A -> Prop) (s : type686 A) (_96197 : A -> Prop) (f : A -> real) (_96198 : A) : (term380 A s _96196 _96197 f _96198) = (term381 A _96196 s _96197 f _96198).
Proof. exact (@lem7185346 (term369 A _96198 _96196) (term217 A _96197 s) (term382 A _96197 f _96198)). Qed.
Lemma lem7185361 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7185362 {A : Type'} (_96197 : A -> Prop) (s : type686 A) (f : A -> real) (_96198 : A) : (term383 A s _96197 f _96198) = (term384 A _96197 s f _96198).
Proof. exact (@lem7185361 (term369 A _96198 _96197) (term217 A _96197 s) ((f _96198) = term34)). Qed.
Lemma lem7185376 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7185377 {A : Type'} (f : A -> real) (_96198 : A) (_96197 : A -> Prop) (s : type686 A) : (term385 A _96197 s f _96198) = (term386 A f _96198 _96197 s).
Proof. exact (@lem7185376 ((f _96198) = term34) (term217 A _96197 s)). Qed.
Lemma lem7185385 {A : Type'} (_96198 : A) (_96197 : A -> Prop) : (term387 A _96198 _96197) = (term387 A _96198 _96197).
Proof. exact (eq_refl (term387 A _96198 _96197)). Qed.
Lemma lem7185386 {A : Type'} (f : A -> real) (_96198 : A) (_96197 : A -> Prop) (s : type686 A) : (term384 A _96197 s f _96198) = (term388 A f _96198 _96197 s).
Proof. exact (MK_COMB (@lem7185385 A _96198 _96197) (@lem7185377 A f _96198 _96197 s)). Qed.
Lemma lem7185390 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7185391 {A : Type'} (f : A -> real) (_96198 : A) (_96197 : A -> Prop) (s : type686 A) : (term388 A f _96198 _96197 s) = (term389 A f _96198 _96197 s).
Proof. exact (@lem7185390 ((f _96198) = term34) (term369 A _96198 _96197) (term217 A _96197 s)). Qed.
Lemma lem7185409 {A : Type'} (f : A -> real) (_96198 : A) (_96197 : A -> Prop) (s : type686 A) : (term384 A _96197 s f _96198) = (term389 A f _96198 _96197 s).
Proof. exact (TRANS (@lem7185386 A f _96198 _96197 s) (@lem7185391 A f _96198 _96197 s)). Qed.
Lemma lem7185410 {A : Type'} (f : A -> real) (_96198 : A) (_96197 : A -> Prop) (s : type686 A) : (term383 A s _96197 f _96198) = (term389 A f _96198 _96197 s).
Proof. exact (TRANS (@lem7185362 A _96197 s f _96198) (@lem7185409 A f _96198 _96197 s)). Qed.
Lemma lem7185411 {A : Type'} (_96198 : A) (_96196 : A -> Prop) : (term387 A _96198 _96196) = (term387 A _96198 _96196).
Proof. exact (eq_refl (term387 A _96198 _96196)). Qed.
Lemma lem7185412 {A : Type'} (_96196 : A -> Prop) (f : A -> real) (_96198 : A) (_96197 : A -> Prop) (s : type686 A) : (term381 A _96196 s _96197 f _96198) = (term390 A _96196 f _96198 _96197 s).
Proof. exact (MK_COMB (@lem7185411 A _96198 _96196) (@lem7185410 A f _96198 _96197 s)). Qed.
Lemma lem7185416 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7185417 {A : Type'} (f : A -> real) (_96196 : A -> Prop) (_96198 : A) (_96197 : A -> Prop) (s : type686 A) : (term390 A _96196 f _96198 _96197 s) = (term391 A f _96196 _96198 _96197 s).
Proof. exact (@lem7185416 ((f _96198) = term34) (term369 A _96198 _96196) (term392 A _96198 _96197 s)). Qed.
Lemma lem7185445 {A : Type'} (f : A -> real) (_96196 : A -> Prop) (_96198 : A) (_96197 : A -> Prop) (s : type686 A) : (term381 A _96196 s _96197 f _96198) = (term391 A f _96196 _96198 _96197 s).
Proof. exact (TRANS (@lem7185412 A _96196 f _96198 _96197 s) (@lem7185417 A f _96196 _96198 _96197 s)). Qed.
Lemma lem7185446 {A : Type'} (f : A -> real) (_96196 : A -> Prop) (_96198 : A) (_96197 : A -> Prop) (s : type686 A) : (term380 A s _96196 _96197 f _96198) = (term391 A f _96196 _96198 _96197 s).
Proof. exact (TRANS (@lem7185347 A _96196 s _96197 f _96198) (@lem7185445 A f _96196 _96198 _96197 s)). Qed.
Lemma lem7185447 {A : Type'} (_96196 : A -> Prop) (s : type686 A) : (term371 A _96196 s) = (term371 A _96196 s).
Proof. exact (eq_refl (term371 A _96196 s)). Qed.
Lemma lem7185448 {A : Type'} (f : A -> real) (_96196 : A -> Prop) (_96198 : A) (_96197 : A -> Prop) (s : type686 A) : (term409 A s _96196 _96197 f _96198) = (term396 A f _96196 _96198 _96197 s).
Proof. exact (MK_COMB (@lem7185447 A _96196 s) (@lem7185446 A f _96196 _96198 _96197 s)). Qed.
Lemma lem7185452 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7185453 {A : Type'} (f : A -> real) (_96196 : A -> Prop) (_96198 : A) (_96197 : A -> Prop) (s : type686 A) : (term396 A f _96196 _96198 _96197 s) = (term397 A f _96196 _96198 _96197 s).
Proof. exact (@lem7185452 ((f _96198) = term34) (term217 A _96196 s) (term398 A _96196 _96198 _96197 s)). Qed.
Lemma lem7185469 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7185470 {A : Type'} (_96196 : A -> Prop) (_96198 : A) (_96197 : A -> Prop) (s : type686 A) : (term399 A _96196 _96198 _96197 s) = (term400 A _96196 _96198 _96197 s).
Proof. exact (@lem7185469 (term369 A _96198 _96196) (term217 A _96196 s) (term392 A _96198 _96197 s)). Qed.
Lemma lem7185484 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7185485 {A : Type'} (_96198 : A) (_96196 : A -> Prop) (_96197 : A -> Prop) (s : type686 A) : (term401 A _96196 _96198 _96197 s) = (term402 A _96198 _96196 _96197 s).
Proof. exact (@lem7185484 (term369 A _96198 _96197) (term217 A _96196 s) (term217 A _96197 s)). Qed.
Lemma lem7185501 {A : Type'} (_96198 : A) (_96196 : A -> Prop) : (term387 A _96198 _96196) = (term387 A _96198 _96196).
Proof. exact (eq_refl (term387 A _96198 _96196)). Qed.
Lemma lem7185502 {A : Type'} (_96198 : A) (_96196 : A -> Prop) (_96197 : A -> Prop) (s : type686 A) : (term400 A _96196 _96198 _96197 s) = (term403 A _96198 _96196 _96197 s).
Proof. exact (MK_COMB (@lem7185501 A _96198 _96196) (@lem7185485 A _96198 _96196 _96197 s)). Qed.
Lemma lem7185513 {A : Type'} (_96198 : A) (_96196 : A -> Prop) (_96197 : A -> Prop) (s : type686 A) : (term399 A _96196 _96198 _96197 s) = (term403 A _96198 _96196 _96197 s).
Proof. exact (TRANS (@lem7185470 A _96196 _96198 _96197 s) (@lem7185502 A _96198 _96196 _96197 s)). Qed.
Lemma lem7185514 {A : Type'} (f : A -> real) (_96198 : A) : (term404 A f _96198) = (term404 A f _96198).
Proof. exact (eq_refl (term404 A f _96198)). Qed.
Lemma lem7185515 {A : Type'} (f : A -> real) (_96198 : A) (_96196 : A -> Prop) (_96197 : A -> Prop) (s : type686 A) : (term397 A f _96196 _96198 _96197 s) = (term405 A f _96198 _96196 _96197 s).
Proof. exact (MK_COMB (@lem7185514 A f _96198) (@lem7185513 A _96198 _96196 _96197 s)). Qed.
Lemma lem7185526 {A : Type'} (f : A -> real) (_96198 : A) (_96196 : A -> Prop) (_96197 : A -> Prop) (s : type686 A) : (term396 A f _96196 _96198 _96197 s) = (term405 A f _96198 _96196 _96197 s).
Proof. exact (TRANS (@lem7185453 A f _96196 _96198 _96197 s) (@lem7185515 A f _96198 _96196 _96197 s)). Qed.
Lemma lem7185527 {A : Type'} (f : A -> real) (_96198 : A) (_96196 : A -> Prop) (_96197 : A -> Prop) (s : type686 A) : (term409 A s _96196 _96197 f _96198) = (term405 A f _96198 _96196 _96197 s).
Proof. exact (TRANS (@lem7185448 A f _96196 _96198 _96197 s) (@lem7185526 A f _96198 _96196 _96197 s)). Qed.
Lemma lem7185528 {A : Type'} (_96196 : A -> Prop) (_96197 : A -> Prop) : (term188 A _96196 _96197) = (term188 A _96196 _96197).
Proof. exact (eq_refl (term188 A _96196 _96197)). Qed.
Lemma lem7185529 {A : Type'} (f : A -> real) (_96198 : A) (_96196 : A -> Prop) (_96197 : A -> Prop) (s : type686 A) : (term410 A s _96196 _96197 f _96198) = (term406 A f _96198 _96196 _96197 s).
Proof. exact (MK_COMB (@lem7185528 A _96196 _96197) (@lem7185527 A f _96198 _96196 _96197 s)). Qed.
Lemma lem7185540 {A : Type'} (f : A -> real) (_96198 : A) (_96196 : A -> Prop) (_96197 : A -> Prop) (s : type686 A) : ((term373 A s _96196 _96197 f _96198) = (term410 A s _96196 _96197 f _96198)) = ((term406 A f _96198 _96196 _96197 s) = (term406 A f _96198 _96196 _96197 s)).
Proof. exact (MK_COMB (@lem7185320 A f _96198 _96196 _96197 s) (@lem7185529 A f _96198 _96196 _96197 s)). Qed.
Lemma lem7185542 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7185543 (x : Prop) : (x = x) = True.
Proof. exact (@lem7185542 Prop x). Qed.
Lemma lem7185544 {A : Type'} (f : A -> real) (_96198 : A) (_96196 : A -> Prop) (_96197 : A -> Prop) (s : type686 A) : ((term406 A f _96198 _96196 _96197 s) = (term406 A f _96198 _96196 _96197 s)) = True.
Proof. exact (@lem7185543 (term406 A f _96198 _96196 _96197 s)). Qed.
Lemma lem7185545 {A : Type'} (s : type686 A) (_96196 : A -> Prop) (_96197 : A -> Prop) (f : A -> real) (_96198 : A) : ((term373 A s _96196 _96197 f _96198) = (term410 A s _96196 _96197 f _96198)) = True.
Proof. exact (TRANS (@lem7185540 A f _96198 _96196 _96197 s) (@lem7185544 A f _96198 _96196 _96197 s)). Qed.
Lemma lem7185546 {A : Type'} (s : type686 A) (_96196 : A -> Prop) (_96197 : A -> Prop) (f : A -> real) (_96198 : A) : True = ((term373 A s _96196 _96197 f _96198) = (term410 A s _96196 _96197 f _96198)).
Proof. exact (SYM (@lem7185545 A s _96196 _96197 f _96198)). Qed.
Lemma lem7185547 {A : Type'} (s : type686 A) (_96196 : A -> Prop) (_96197 : A -> Prop) (f : A -> real) (_96198 : A) : (term373 A s _96196 _96197 f _96198) = (term410 A s _96196 _96197 f _96198).
Proof. exact (EQ_MP (@lem7185546 A s _96196 _96197 f _96198) (@lem0)). Qed.
Lemma lem7185548 {A : Type'} (_96196 : A -> Prop) (_96197 : A -> Prop) (_96198 : A) (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term133 A t s f) : term410 A s _96196 _96197 f _96198.
Proof. exact (EQ_MP (@lem7185547 A s _96196 _96197 f _96198) (@lem7184870 A _96196 _96197 _96198 t s f h1)). Qed.
Lemma lem7185550 (b : Prop) (a : Prop) : (a \/ b) = (term411 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7185551 {A : Type'} (s : type686 A) (f : A -> real) (_96198 : A) (_96196 : A -> Prop) (_96197 : A -> Prop) : (term410 A s _96196 _96197 f _96198) = (term412 A s f _96198 _96196 _96197).
Proof. exact (@lem7185550 (term409 A s _96196 _96197 f _96198) (_96196 = _96197)). Qed.
Lemma lem7185553 (a : Prop) (b : Prop) : (term413 a b) = (term414 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7185554 {A : Type'} (s : type686 A) (_96196 : A -> Prop) (_96197 : A -> Prop) (f : A -> real) (_96198 : A) : (term415 A s _96196 _96197 f _96198) = (term416 A s _96196 _96197 f _96198).
Proof. exact (@lem7185553 (term217 A _96196 s) (term380 A s _96196 _96197 f _96198)). Qed.
Lemma lem7185556 (a : Prop) : (term269 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7185557 {A : Type'} (_96196 : A -> Prop) (s : type686 A) : (term417 A _96196 s) = (@IN (A -> Prop) _96196 s).
Proof. exact (@lem7185556 (@IN (A -> Prop) _96196 s)). Qed.
Lemma lem7185558 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7185559 {A : Type'} (_96196 : A -> Prop) (s : type686 A) : (term418 A _96196 s) = (term419 A _96196 s).
Proof. exact (MK_COMB (@lem7185558) (@lem7185557 A _96196 s)). Qed.
Lemma lem7185561 (a : Prop) (b : Prop) : (term413 a b) = (term414 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7185562 {A : Type'} (s : type686 A) (_96196 : A -> Prop) (_96197 : A -> Prop) (f : A -> real) (_96198 : A) : (term420 A s _96196 _96197 f _96198) = (term421 A s _96196 _96197 f _96198).
Proof. exact (@lem7185561 (term217 A _96197 s) (term368 A _96196 _96197 f _96198)). Qed.
Lemma lem7185564 (a : Prop) : (term269 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7185565 {A : Type'} (_96197 : A -> Prop) (s : type686 A) : (term417 A _96197 s) = (@IN (A -> Prop) _96197 s).
Proof. exact (@lem7185564 (@IN (A -> Prop) _96197 s)). Qed.
Lemma lem7185566 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7185567 {A : Type'} (_96197 : A -> Prop) (s : type686 A) : (term418 A _96197 s) = (term419 A _96197 s).
Proof. exact (MK_COMB (@lem7185566) (@lem7185565 A _96197 s)). Qed.
Lemma lem7185569 (a : Prop) (b : Prop) : (term413 a b) = (term414 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7185570 {A : Type'} (_96196 : A -> Prop) (_96197 : A -> Prop) (f : A -> real) (_96198 : A) : (term422 A _96196 _96197 f _96198) = (term423 A _96196 _96197 f _96198).
Proof. exact (@lem7185569 (term369 A _96198 _96196) (term382 A _96197 f _96198)). Qed.
Lemma lem7185572 (a : Prop) : (term269 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7185573 {A : Type'} (_96198 : A) (_96196 : A -> Prop) : (term424 A _96198 _96196) = (@IN A _96198 _96196).
Proof. exact (@lem7185572 (@IN A _96198 _96196)). Qed.
Lemma lem7185574 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7185575 {A : Type'} (_96198 : A) (_96196 : A -> Prop) : (term425 A _96198 _96196) = (term426 A _96198 _96196).
Proof. exact (MK_COMB (@lem7185574) (@lem7185573 A _96198 _96196)). Qed.
Lemma lem7185577 (a : Prop) (b : Prop) : (term413 a b) = (term414 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7185578 {A : Type'} (_96197 : A -> Prop) (f : A -> real) (_96198 : A) : (term427 A _96197 f _96198) = (term428 A _96197 f _96198).
Proof. exact (@lem7185577 (term369 A _96198 _96197) ((f _96198) = term34)). Qed.
Lemma lem7185580 (a : Prop) : (term269 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7185581 {A : Type'} (_96198 : A) (_96197 : A -> Prop) : (term424 A _96198 _96197) = (@IN A _96198 _96197).
Proof. exact (@lem7185580 (@IN A _96198 _96197)). Qed.
Lemma lem7185582 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7185583 {A : Type'} (_96198 : A) (_96197 : A -> Prop) : (term425 A _96198 _96197) = (term426 A _96198 _96197).
Proof. exact (MK_COMB (@lem7185582) (@lem7185581 A _96198 _96197)). Qed.
Lemma lem7185584 {A : Type'} (f : A -> real) (_96198 : A) : (term294 A f _96198) = (term294 A f _96198).
Proof. exact (eq_refl (term294 A f _96198)). Qed.
Lemma lem7185585 {A : Type'} (_96197 : A -> Prop) (f : A -> real) (_96198 : A) : (term428 A _96197 f _96198) = (term429 A _96197 f _96198).
Proof. exact (MK_COMB (@lem7185583 A _96198 _96197) (@lem7185584 A f _96198)). Qed.
Lemma lem7185586 {A : Type'} (_96197 : A -> Prop) (f : A -> real) (_96198 : A) : (term427 A _96197 f _96198) = (term429 A _96197 f _96198).
Proof. exact (TRANS (@lem7185578 A _96197 f _96198) (@lem7185585 A _96197 f _96198)). Qed.
Lemma lem7185587 {A : Type'} (_96196 : A -> Prop) (_96197 : A -> Prop) (f : A -> real) (_96198 : A) : (term423 A _96196 _96197 f _96198) = (term430 A _96196 _96197 f _96198).
Proof. exact (MK_COMB (@lem7185575 A _96198 _96196) (@lem7185586 A _96197 f _96198)). Qed.
Lemma lem7185588 {A : Type'} (_96196 : A -> Prop) (_96197 : A -> Prop) (f : A -> real) (_96198 : A) : (term422 A _96196 _96197 f _96198) = (term430 A _96196 _96197 f _96198).
Proof. exact (TRANS (@lem7185570 A _96196 _96197 f _96198) (@lem7185587 A _96196 _96197 f _96198)). Qed.
Lemma lem7185589 {A : Type'} (s : type686 A) (_96196 : A -> Prop) (_96197 : A -> Prop) (f : A -> real) (_96198 : A) : (term421 A s _96196 _96197 f _96198) = (term431 A s _96196 _96197 f _96198).
Proof. exact (MK_COMB (@lem7185567 A _96197 s) (@lem7185588 A _96196 _96197 f _96198)). Qed.
Lemma lem7185590 {A : Type'} (s : type686 A) (_96196 : A -> Prop) (_96197 : A -> Prop) (f : A -> real) (_96198 : A) : (term420 A s _96196 _96197 f _96198) = (term431 A s _96196 _96197 f _96198).
Proof. exact (TRANS (@lem7185562 A s _96196 _96197 f _96198) (@lem7185589 A s _96196 _96197 f _96198)). Qed.
Lemma lem7185591 {A : Type'} (s : type686 A) (_96196 : A -> Prop) (_96197 : A -> Prop) (f : A -> real) (_96198 : A) : (term416 A s _96196 _96197 f _96198) = (term432 A s _96196 _96197 f _96198).
Proof. exact (MK_COMB (@lem7185559 A _96196 s) (@lem7185590 A s _96196 _96197 f _96198)). Qed.
Lemma lem7185592 {A : Type'} (s : type686 A) (_96196 : A -> Prop) (_96197 : A -> Prop) (f : A -> real) (_96198 : A) : (term415 A s _96196 _96197 f _96198) = (term432 A s _96196 _96197 f _96198).
Proof. exact (TRANS (@lem7185554 A s _96196 _96197 f _96198) (@lem7185591 A s _96196 _96197 f _96198)). Qed.
Lemma lem7185593 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7185594 {A : Type'} (s : type686 A) (_96196 : A -> Prop) (_96197 : A -> Prop) (f : A -> real) (_96198 : A) : (term433 A s _96196 _96197 f _96198) = (term434 A s _96196 _96197 f _96198).
Proof. exact (MK_COMB (@lem7185593) (@lem7185592 A s _96196 _96197 f _96198)). Qed.
Lemma lem7185595 {A : Type'} (_96196 : A -> Prop) (_96197 : A -> Prop) : (_96196 = _96197) = (_96196 = _96197).
Proof. exact (eq_refl (_96196 = _96197)). Qed.
Lemma lem7185596 {A : Type'} (s : type686 A) (f : A -> real) (_96198 : A) (_96196 : A -> Prop) (_96197 : A -> Prop) : (term412 A s f _96198 _96196 _96197) = (term435 A s f _96198 _96196 _96197).
Proof. exact (MK_COMB (@lem7185594 A s _96196 _96197 f _96198) (@lem7185595 A _96196 _96197)). Qed.
Lemma lem7185597 {A : Type'} (s : type686 A) (f : A -> real) (_96198 : A) (_96196 : A -> Prop) (_96197 : A -> Prop) : (term410 A s _96196 _96197 f _96198) = (term435 A s f _96198 _96196 _96197).
Proof. exact (TRANS (@lem7185551 A s f _96198 _96196 _96197) (@lem7185596 A s f _96198 _96196 _96197)). Qed.
Lemma lem7185599 {A : Type'} (f : A -> real) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term294 A f x) (h2 : term324 A s t1 x t2) : term429 A t2 f x.
Proof. exact (conj (@lem7185054 A s t1 x t2 h2) (@lem7185061 A f x h1)). Qed.
Lemma lem7185600 {A : Type'} (f : A -> real) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term294 A f x) (h2 : term324 A s t1 x t2) : term430 A t1 t2 f x.
Proof. exact (conj (@lem7185047 A s t1 x t2 h2) (@lem7185599 A f s t1 x t2 h1 h2)). Qed.
Lemma lem7185601 {A : Type'} (f : A -> real) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term294 A f x) (h2 : term324 A s t1 x t2) : term431 A s t1 t2 f x.
Proof. exact (conj (@lem7185040 A s t1 x t2 h2) (@lem7185600 A f s t1 x t2 h1 h2)). Qed.
Lemma lem7185602 {A : Type'} (f : A -> real) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term294 A f x) (h2 : term324 A s t1 x t2) : term432 A s t1 t2 f x.
Proof. exact (conj (@lem7185033 A s t1 x t2 h2) (@lem7185601 A f s t1 x t2 h1 h2)). Qed.
Lemma lem7185604 {A : Type'} (_96198 : A) (_96196 : A -> Prop) (_96197 : A -> Prop) (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term133 A t s f) : term435 A s f _96198 _96196 _96197.
Proof. exact (EQ_MP (@lem7185597 A s f _96198 _96196 _96197) (@lem7185548 A _96196 _96197 _96198 t s f h1)). Qed.
Lemma lem7185605 {A : Type'} (_96198 : A) (_96196 : A -> Prop) (_96197 : A -> Prop) (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term133 A t s f) : term435 A s f _96198 _96196 _96197.
Proof. exact (@lem7185604 A _96198 _96196 _96197 t s f h1). Qed.
Lemma lem7185606 {A : Type'} (x : A) (t1 : A -> Prop) (t2 : A -> Prop) (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term133 A t s f) : term435 A s f x t1 t2.
Proof. exact (@lem7185605 A x t1 t2 t s f h1). Qed.
Lemma lem7185609 {A : Type'} (t : A -> Prop) (f : A -> real) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term133 A t s f) (h2 : term294 A f x) (h3 : term324 A s t1 x t2) : t1 = t2.
Proof. exact (@lem7185606 A x t1 t2 t s f h1 (@lem7185602 A f s t1 x t2 h2 h3)). Qed.
Lemma lem7185610 {A : Type'} (t : A -> Prop) (f : A -> real) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term133 A t s f) (h2 : term294 A f x) (h3 : term324 A s t1 x t2) : term436 A t1 t2.
Proof. exact (fun h0 : term304 A t1 t2 => @lem7185609 A t f s t1 x t2 h1 h2 h3). Qed.
Lemma lem7185612 (p : Prop) : (term375 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7185613 {A : Type'} (t1 : A -> Prop) (t2 : A -> Prop) : (term436 A t1 t2) = (t1 = t2).
Proof. exact (@lem7185612 (t1 = t2)). Qed.
Lemma lem7185614 {A : Type'} (t : A -> Prop) (f : A -> real) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term133 A t s f) (h2 : term294 A f x) (h3 : term324 A s t1 x t2) : t1 = t2.
Proof. exact (EQ_MP (@lem7185613 A t1 t2) (@lem7185610 A t f s t1 x t2 h1 h2 h3)). Qed.
Lemma lem7185617 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7185619 {A : Type'} (t1 : A -> Prop) (t2 : A -> Prop) : (term304 A t1 t2) = (term437 A t1 t2).
Proof. exact (@lem7185617 (t1 = t2)). Qed.
Lemma lem7185622 {A : Type'} (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term324 A s t1 x t2) : term437 A t1 t2.
Proof. exact (EQ_MP (@lem7185619 A t1 t2) (@lem7184806 A s t1 x t2 h1)). Qed.
Lemma lem7185625 {A : Type'} (t : A -> Prop) (f : A -> real) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term133 A t s f) (h2 : term294 A f x) (h3 : term324 A s t1 x t2) : False.
Proof. exact (@lem7185622 A s t1 x t2 h3 (@lem7185614 A t f s t1 x t2 h1 h2 h3)). Qed.
Lemma lem7185626 {A : Type'} (t : A -> Prop) (f : A -> real) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term133 A t s f) (h2 : term294 A f x) (h3 : term324 A s t1 x t2) : term438.
Proof. exact (fun h0 : ~ False => @lem7185625 A t f s t1 x t2 h1 h2 h3). Qed.
Lemma lem7185628 (p : Prop) : (term375 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7185629 : term438 = False.
Proof. exact (@lem7185628 False). Qed.
Lemma lem7185630 {A : Type'} (t : A -> Prop) (f : A -> real) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term133 A t s f) (h2 : term294 A f x) (h3 : term324 A s t1 x t2) : False.
Proof. exact (EQ_MP (@lem7185629) (@lem7185626 A t f s t1 x t2 h1 h2 h3)). Qed.
Lemma lem7185631 {A : Type'} (t : A -> Prop) (f : A -> real) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term133 A t s f) (h2 : term294 A f x) (h3 : term324 A s t1 x t2) : (term294 A f x) = False.
Proof. exact (prop_ext (fun h4 : term294 A f x => @lem7185630 A t f s t1 x t2 h1 h2 h3) (fun h4 : False => @lem7184800 A f x h2)). Qed.
Lemma lem7185632 {A : Type'} (t : A -> Prop) (f : A -> real) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term133 A t s f) (h2 : term294 A f x) (h3 : term324 A s t1 x t2) : False.
Proof. exact (EQ_MP (@lem7185631 A t f s t1 x t2 h1 h2 h3) (@lem7184800 A f x h2)). Qed.
Lemma lem7185633 {A : Type'} (t : A -> Prop) (f : A -> real) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term133 A t s f) (h2 : term294 A f x) (h3 : term324 A s t1 x t2) : (term294 A f x) = False.
Proof. exact (prop_ext (fun h4 : term294 A f x => @lem7185632 A t f s t1 x t2 h1 h2 h3) (fun h4 : False => @lem7184758 A f x h2)). Qed.
Lemma lem7185634 {A : Type'} (t : A -> Prop) (f : A -> real) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term133 A t s f) (h2 : term294 A f x) (h3 : term324 A s t1 x t2) : False.
Proof. exact (EQ_MP (@lem7185633 A t f s t1 x t2 h1 h2 h3) (@lem7184758 A f x h2)). Qed.
Lemma lem7185635 {A : Type'} (t : A -> Prop) (f : A -> real) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term133 A t s f) (h2 : term294 A f x) (h3 : term324 A s t1 x t2) : (term294 A f x) = False.
Proof. exact (prop_ext (fun h4 : term294 A f x => @lem7185634 A t f s t1 x t2 h1 h2 h3) (fun h4 : False => @lem7184758 A f x h2)). Qed.
Lemma lem7185636 {A : Type'} (t : A -> Prop) (f : A -> real) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term133 A t s f) (h2 : term294 A f x) (h3 : term324 A s t1 x t2) : False.
Proof. exact (EQ_MP (@lem7185635 A t f s t1 x t2 h1 h2 h3) (@lem7184758 A f x h2)). Qed.
Lemma lem7185637 {A : Type'} (t : A -> Prop) (f : A -> real) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term133 A t s f) (h2 : term294 A f x) (h3 : term324 A s t1 x t2) : (term294 A f x) = False.
Proof. exact (prop_ext (fun h4 : term294 A f x => @lem7185636 A t f s t1 x t2 h1 h2 h3) (fun h4 : False => @lem7184630 A f x h2)). Qed.
Lemma lem7185638 {A : Type'} (t : A -> Prop) (f : A -> real) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term133 A t s f) (h2 : term294 A f x) (h3 : term324 A s t1 x t2) : False.
Proof. exact (EQ_MP (@lem7185637 A t f s t1 x t2 h1 h2 h3) (@lem7184630 A f x h2)). Qed.
Lemma lem7185639 {A : Type'} (t : A -> Prop) (f : A -> real) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term133 A t s f) (h2 : term294 A f x) (h3 : term324 A s t1 x t2) : (term324 A s t1 x t2) = False.
Proof. exact (prop_ext (fun h4 : term324 A s t1 x t2 => @lem7185638 A t f s t1 x t2 h1 h2 h3) (fun h4 : False => @lem7184616 A s t1 x t2 h3)). Qed.
Lemma lem7185640 {A : Type'} (t : A -> Prop) (f : A -> real) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term133 A t s f) (h2 : term294 A f x) (h3 : term324 A s t1 x t2) : False.
Proof. exact (EQ_MP (@lem7185639 A t f s t1 x t2 h1 h2 h3) (@lem7184616 A s t1 x t2 h3)). Qed.
Lemma lem7185641 {A : Type'} (t : A -> Prop) (f : A -> real) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term133 A t s f) (h2 : term294 A f x) (h3 : term324 A s t1 x t2) : (term294 A f x) = False.
Proof. exact (prop_ext (fun h4 : term294 A f x => @lem7185640 A t f s t1 x t2 h1 h2 h3) (fun h4 : False => @lem7184460 A f x h2)). Qed.
Lemma lem7185642 {A : Type'} (t : A -> Prop) (f : A -> real) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term133 A t s f) (h2 : term294 A f x) (h3 : term324 A s t1 x t2) : False.
Proof. exact (EQ_MP (@lem7185641 A t f s t1 x t2 h1 h2 h3) (@lem7184460 A f x h2)). Qed.
Lemma lem7185643 {A : Type'} (t : A -> Prop) (f : A -> real) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term133 A t s f) (h2 : term294 A f x) (h3 : term324 A s t1 x t2) : (term324 A s t1 x t2) = False.
Proof. exact (prop_ext (fun h4 : term324 A s t1 x t2 => @lem7185642 A t f s t1 x t2 h1 h2 h3) (fun h4 : False => @lem7184454 A s t1 x t2 h3)). Qed.
Lemma lem7185644 {A : Type'} (t : A -> Prop) (f : A -> real) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term133 A t s f) (h2 : term294 A f x) (h3 : term324 A s t1 x t2) : False.
Proof. exact (EQ_MP (@lem7185643 A t f s t1 x t2 h1 h2 h3) (@lem7184454 A s t1 x t2 h3)). Qed.
Lemma lem7185645 {A : Type'} (t : A -> Prop) (f : A -> real) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term133 A t s f) (h2 : term294 A f x) (h3 : term324 A s t1 x t2) : (term294 A f x) = False.
Proof. exact (prop_ext (fun h4 : term294 A f x => @lem7185644 A t f s t1 x t2 h1 h2 h3) (fun h4 : False => @lem7184264 A f x h2)). Qed.
Lemma lem7185646 {A : Type'} (t : A -> Prop) (f : A -> real) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term133 A t s f) (h2 : term294 A f x) (h3 : term324 A s t1 x t2) : False.
Proof. exact (EQ_MP (@lem7185645 A t f s t1 x t2 h1 h2 h3) (@lem7184264 A f x h2)). Qed.
Lemma lem7185647 {A : Type'} (t : A -> Prop) (f : A -> real) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term133 A t s f) (h2 : term324 A s t1 x t2) : term293 A f x.
Proof. exact (fun h0 : term294 A f x => @lem7185646 A t f s t1 x t2 h1 h0 h2). Qed.
Lemma lem7185648 {A : Type'} (t : A -> Prop) (f : A -> real) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) (h1 : term133 A t s f) (h2 : term324 A s t1 x t2) : (f x) = term34.
Proof. exact (EQ_MP (@lem7184263 A f x) (@lem7185647 A t f s t1 x t2 h1 h2)). Qed.
Lemma lem7185649 {A : Type'} (t1 : A -> Prop) (t2 : A -> Prop) (x : A) (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term133 A t s f) : term287 A s t1 t2 f x.
Proof. exact (fun h0 : term324 A s t1 x t2 => @lem7185648 A t f s t1 x t2 h1 h0). Qed.
Lemma lem7185654 {A : Type'} (t1 : A -> Prop) (t2 : A -> Prop) (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term133 A t s f) : term289 A s t1 t2 f.
Proof. exact (fun x : A => @lem7185649 A t1 t2 x t s f h1). Qed.
Lemma lem7185659 {A : Type'} (t1 : A -> Prop) (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term133 A t s f) : term291 A s t1 f.
Proof. exact (fun t2 : A -> Prop => @lem7185654 A t1 t2 t s f h1). Qed.
Lemma lem7185664 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term133 A t s f) : term201 A s f.
Proof. exact (fun t1 : A -> Prop => @lem7185659 A t1 t s f h1). Qed.
Lemma lem7185665 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : term272 A t s f.
Proof. exact (fun h0 : term133 A t s f => @lem7185664 A t s f h0). Qed.
Lemma lem7185666 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : term274 A t s f.
Proof. exact (fun h0 : term108 A t s => @lem7185665 A t s f). Qed.
Lemma lem7185671 {A : Type'} (s : type686 A) (f : A -> real) : term278 A s f.
Proof. exact (fun t : A -> Prop => @lem7185666 A t s f). Qed.
Lemma lem7185676 {A : Type'} (f : A -> real) : term282 A f.
Proof. exact (fun s : type686 A => @lem7185671 A s f). Qed.
Lemma lem7185681 {A : Type'} : term286 A.
Proof. exact (fun f : A -> real => @lem7185676 A f). Qed.
Lemma lem7185682 {A : Type'} : term285 A.
Proof. exact (EQ_MP (@lem7184256 A) (@lem7185681 A)). Qed.
Lemma lem7185683 {A : Type'} (f : A -> real) : term439 A f.
Proof. exact (@lem7185682 A f). Qed.
Lemma lem7185684 {A : Type'} (f : A -> real) : (term439 A f) = (term281 A f).
Proof. exact (eq_refl (term439 A f)). Qed.
Lemma lem7185685 {A : Type'} (f : A -> real) : term281 A f.
Proof. exact (EQ_MP (@lem7185684 A f) (@lem7185683 A f)). Qed.
Lemma lem7185686 {A : Type'} (f : A -> real) (s : type686 A) : term440 A f s.
Proof. exact (@lem7185685 A f s). Qed.
Lemma lem7185687 {A : Type'} (s : type686 A) (f : A -> real) : (term440 A f s) = (term277 A s f).
Proof. exact (eq_refl (term440 A f s)). Qed.
Lemma lem7185688 {A : Type'} (s : type686 A) (f : A -> real) : term277 A s f.
Proof. exact (EQ_MP (@lem7185687 A s f) (@lem7185686 A f s)). Qed.
Lemma lem7185689 {A : Type'} (s : type686 A) (f : A -> real) (t : A -> Prop) : term441 A s f t.
Proof. exact (@lem7185688 A s f t). Qed.
Lemma lem7185690 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term441 A s f t) = (term264 A t s f).
Proof. exact (eq_refl (term441 A s f t)). Qed.
Lemma lem7185691 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : term264 A t s f.
Proof. exact (EQ_MP (@lem7185690 A t s f) (@lem7185689 A s f t)). Qed.
Lemma lem7185693 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : term264 A t s f.
Proof. exact (@lem7183949 A t s f (@lem7185691 A t s f)). Qed.
Lemma lem7185694 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term108 A t s) : term271 A t s f.
Proof. exact (@lem7185693 A t s f (@lem7179333 A t s h1)). Qed.
Lemma lem7185695 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term133 A t s f) (h2 : term108 A t s) : term262 A s f.
Proof. exact (@lem7185694 A f t s h2 (@lem7179332 A t s f h1)). Qed.
Lemma lem7185696 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term133 A t s f) (h2 : term108 A t s) (h3 : term263 A s f) : False.
Proof. exact (@lem7185695 A f t s h1 h2 (@lem7183933 A s f h3)). Qed.
Lemma lem7185697 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term133 A t s f) (h2 : term108 A t s) (h3 : term263 A s f) : (term263 A s f) = False.
Proof. exact (prop_ext (fun h4 : term263 A s f => @lem7185696 A t s f h1 h2 h3) (fun h4 : False => @lem7183933 A s f h3)). Qed.
Lemma lem7185698 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term133 A t s f) (h2 : term108 A t s) (h3 : term263 A s f) : False.
Proof. exact (EQ_MP (@lem7185697 A t s f h1 h2 h3) (@lem7183933 A s f h3)). Qed.
Lemma lem7185699 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term133 A t s f) (h2 : term108 A t s) : term262 A s f.
Proof. exact (fun h0 : term263 A s f => @lem7185698 A t s f h1 h2 h0). Qed.
Lemma lem7185700 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term133 A t s f) (h2 : term108 A t s) : term201 A s f.
Proof. exact (EQ_MP (@lem7183932 A s f) (@lem7185699 A f t s h1 h2)). Qed.
Lemma lem7185701 {A : Type'} (s : type686 A) (f : A -> real) (h1 : (term47 A s f) = (term48 A s f)) : (term47 A s f) = (term48 A s f).
Proof. exact (h1). Qed.
Lemma lem7185702 {A : Type'} (s : type686 A) (f : A -> real) (h1 : (term47 A s f) = (term48 A s f)) : (term48 A s f) = (term47 A s f).
Proof. exact (SYM (@lem7185701 A s f h1)). Qed.
Lemma lem7185703 {A : Type'} (s : type686 A) (t : A -> Prop) (f : A -> real) : (term442 A s t f) = (term442 A s t f).
Proof. exact (eq_refl (term442 A s t f)). Qed.
Lemma lem7185704 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : (term47 A s f) = (term48 A s f)) : (term443 A t s f) = (term444 A t s f).
Proof. exact (MK_COMB (@lem7185703 A s t f) (@lem7185702 A s f h1)). Qed.
Lemma lem7185705 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term444 A t s f) = (term445 A t s f).
Proof. exact (eq_refl (term444 A t s f)). Qed.
Lemma lem7185706 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term446 A t s f) = (term446 A t s f).
Proof. exact (eq_refl (term446 A t s f)). Qed.
Lemma lem7185707 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : ((term443 A t s f) = (term444 A t s f)) = ((term443 A t s f) = (term445 A t s f)).
Proof. exact (MK_COMB (@lem7185706 A t s f) (@lem7185705 A t s f)). Qed.
Lemma lem7185708 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term443 A t s f) = (term255 A t s f).
Proof. exact (eq_refl (term443 A t s f)). Qed.
Lemma lem7185709 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7185710 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term446 A t s f) = (term447 A t s f).
Proof. exact (MK_COMB (@lem7185709) (@lem7185708 A t s f)). Qed.
Lemma lem7185711 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term445 A t s f) = (term445 A t s f).
Proof. exact (eq_refl (term445 A t s f)). Qed.
Lemma lem7185712 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : ((term443 A t s f) = (term445 A t s f)) = ((term255 A t s f) = (term445 A t s f)).
Proof. exact (MK_COMB (@lem7185710 A t s f) (@lem7185711 A t s f)). Qed.
Lemma lem7185713 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : ((term443 A t s f) = (term444 A t s f)) = ((term255 A t s f) = (term445 A t s f)).
Proof. exact (TRANS (@lem7185707 A t s f) (@lem7185712 A t s f)). Qed.
Lemma lem7185714 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : (term47 A s f) = (term48 A s f)) : (term255 A t s f) = (term445 A t s f).
Proof. exact (EQ_MP (@lem7185713 A t s f) (@lem7185704 A t s f h1)). Qed.
Lemma lem7185715 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : (term47 A s f) = (term48 A s f)) : (term445 A t s f) = (term255 A t s f).
Proof. exact (SYM (@lem7185714 A t s f h1)). Qed.
Lemma lem7185729 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term108 A t s) : term108 A t s.
Proof. exact (h1). Qed.
Lemma lem7185743 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term133 A t s f) : term133 A t s f.
Proof. exact (h1). Qed.
Lemma lem7185744 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term64 A t s) : term64 A t s.
Proof. exact (h1). Qed.
Lemma lem7185745 {A : Type'} (s : type686 A) (h1 : @FINITE (A -> Prop) s) : @FINITE (A -> Prop) s.
Proof. exact (h1). Qed.
Lemma lem7185746 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term217 A t s) : term217 A t s.
Proof. exact (h1). Qed.
Lemma lem7185748 {_135252 : Type'} (s : _135252 -> Prop) (t : _135252 -> Prop) (f : _135252 -> real) : term13 _135252 s t f.
Proof. exact (EQ_MP (@lem7178847 _135252 s t f) (@lem7178846 _135252 s t f)). Qed.
Lemma lem7185749 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> real) : term13 A s t f.
Proof. exact (@lem7185748 A s t f). Qed.
Lemma lem7185750 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : term448 A t s f.
Proof. exact (@lem7185749 A t (@UNIONS A s) f). Qed.
Lemma lem7185751 {A : Type'} (s : type686 A) : term449 A s.
Proof. exact (@lem3205091 A s). Qed.
Lemma lem7185752 {A : Type'} (s : type686 A) : (term449 A s) = (term450 A s).
Proof. exact (eq_refl (term449 A s)). Qed.
Lemma lem7185753 {A : Type'} (s : type686 A) : term450 A s.
Proof. exact (EQ_MP (@lem7185752 A s) (@lem7185751 A s)). Qed.
Lemma lem7185754 {A : Type'} (s : type686 A) (x : A) : term451 A s x.
Proof. exact (@lem7185753 A s x). Qed.
Lemma lem7185755 {A : Type'} (s : type686 A) (x : A) : (term451 A s x) = ((term452 A x s) = (term453 A s x)).
Proof. exact (eq_refl (term451 A s x)). Qed.
Lemma lem7185757 {A : Type'} (s : A -> Prop) : term454 A s.
Proof. exact (@lem3205222 A s). Qed.
Lemma lem7185758 {A : Type'} (s : A -> Prop) : (term454 A s) = (term455 A s).
Proof. exact (eq_refl (term454 A s)). Qed.
Lemma lem7185759 {A : Type'} (s : A -> Prop) : term455 A s.
Proof. exact (EQ_MP (@lem7185758 A s) (@lem7185757 A s)). Qed.
Lemma lem7185760 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term456 A s t.
Proof. exact (@lem7185759 A s t). Qed.
Lemma lem7185761 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term456 A s t) = (term457 A s t).
Proof. exact (eq_refl (term456 A s t)). Qed.
Lemma lem7185762 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term457 A s t.
Proof. exact (EQ_MP (@lem7185761 A s t) (@lem7185760 A s t)). Qed.
Lemma lem7185763 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term458 A s t x.
Proof. exact (@lem7185762 A s t x). Qed.
Lemma lem7185764 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term458 A s t x) = ((term459 A x s t) = (term305 A s x t)).
Proof. exact (eq_refl (term458 A s t x)). Qed.
Lemma lem7185766 {A : Type'} (s : type686 A) : term460 A s.
Proof. exact (@lem4605902 A s). Qed.
Lemma lem7185767 {A : Type'} (s : type686 A) : (term460 A s) = ((term461 A s) = (term462 A s)).
Proof. exact (eq_refl (term460 A s)). Qed.
Lemma lem7185769 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (s : type686 A) (h1 : term108 A t s) : term165 A t s t'.
Proof. exact (@lem7185729 A t s h1 t'). Qed.
Lemma lem7185770 {A : Type'} (t : A -> Prop) (s : type686 A) (t' : A -> Prop) : (term165 A t s t') = (term104 A t s t').
Proof. exact (eq_refl (term165 A t s t')). Qed.
Lemma lem7185771 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (s : type686 A) (h1 : term108 A t s) : term104 A t s t'.
Proof. exact (EQ_MP (@lem7185770 A t s t') (@lem7185769 A t' t s h1)). Qed.
Lemma lem7185772 {A : Type'} (t : A -> Prop) (t' : A -> Prop) (s : type686 A) (h1 : term100 A t t' s) : term100 A t t' s.
Proof. exact (h1). Qed.
Lemma lem7185773 {A : Type'} (t : A -> Prop) (t' : A -> Prop) (s : type686 A) (h1 : term108 A t s) (h2 : term100 A t t' s) : @FINITE A t'.
Proof. exact (@lem7185771 A t' t s h1 (@lem7185772 A t t' s h2)). Qed.
Lemma lem7185774 {A : Type'} (t' : A -> Prop) : (@FINITE A t') = ((@FINITE A t') = True).
Proof. exact (@lem7 (@FINITE A t')). Qed.
Lemma lem7185775 {A : Type'} (t : A -> Prop) (t' : A -> Prop) (s : type686 A) (h1 : term108 A t s) (h2 : term100 A t t' s) : (@FINITE A t') = True.
Proof. exact (EQ_MP (@lem7185774 A t') (@lem7185773 A t t' s h1 h2)). Qed.
Lemma lem7185849 {A : Type'} (t : A -> Prop) (s : type686 A) : term218 A t s.
Proof. exact (@lem82 (@IN (A -> Prop) t s)). Qed.
Lemma lem7185851 {A : Type'} (s : type686 A) : (@FINITE (A -> Prop) s) = ((@FINITE (A -> Prop) s) = True).
Proof. exact (@lem7 (@FINITE (A -> Prop) s)). Qed.
Lemma lem7185856 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (s : type686 A) (h1 : term108 A t s) : term187 A t s t'.
Proof. exact (fun h0 : term100 A t t' s => @lem7185775 A t t' s h1 h0). Qed.
Lemma lem7185857 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (s : type686 A) (h1 : term108 A t s) : term187 A t s t'.
Proof. exact (@lem7185856 A t' t s h1). Qed.
Lemma lem7185858 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term108 A t s) : term463 A s t.
Proof. exact (@lem7185857 A t t s h1). Qed.
Lemma lem7185862 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7185863 {A : Type'} (x : A -> Prop) : (x = x) = True.
Proof. exact (@lem7185862 (A -> Prop) x). Qed.
Lemma lem7185864 {A : Type'} (t : A -> Prop) : (t = t) = True.
Proof. exact (@lem7185863 A t). Qed.
Lemma lem7185865 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7185866 {A : Type'} (t : A -> Prop) : (term464 A t) = (or True).
Proof. exact (MK_COMB (@lem7185865) (@lem7185864 A t)). Qed.
Lemma lem7185868 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term217 A t s) : (@IN (A -> Prop) t s) = False.
Proof. exact (@lem7185849 A t s (@lem7185746 A t s h1)). Qed.
Lemma lem7185869 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term217 A t s) : (term465 A t s) = (True \/ False).
Proof. exact (MK_COMB (@lem7185866 A t) (@lem7185868 A t s h1)). Qed.
Lemma lem7185871 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem7185872 : (True \/ False) = True.
Proof. exact (@lem7185871 False). Qed.
Lemma lem7185873 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term217 A t s) : (term465 A t s) = True.
Proof. exact (TRANS (@lem7185869 A t s h1) (@lem7185872)). Qed.
Lemma lem7185874 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term217 A t s) : True = (term465 A t s).
Proof. exact (SYM (@lem7185873 A t s h1)). Qed.
Lemma lem7185875 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term217 A t s) : term465 A t s.
Proof. exact (EQ_MP (@lem7185874 A t s h1) (@lem0)). Qed.
Lemma lem7185876 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term108 A t s) (h2 : term217 A t s) : (@FINITE A t) = True.
Proof. exact (@lem7185858 A t s h1 (@lem7185875 A t s h2)). Qed.
Lemma lem7185877 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7185878 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term108 A t s) (h2 : term217 A t s) : (term466 A t) = (and True).
Proof. exact (MK_COMB (@lem7185877) (@lem7185876 A t s h1 h2)). Qed.
Lemma lem7185882 {A : Type'} (s : type686 A) : (term461 A s) = (term462 A s).
Proof. exact (EQ_MP (@lem7185767 A s) (@lem7185766 A s)). Qed.
Lemma lem7185883 {A : Type'} (s : type686 A) : (term461 A s) = (term462 A s).
Proof. exact (@lem7185882 A s). Qed.
Lemma lem7185887 {A : Type'} (s : type686 A) (h1 : @FINITE (A -> Prop) s) : (@FINITE (A -> Prop) s) = True.
Proof. exact (EQ_MP (@lem7185851 A s) (@lem7185745 A s h1)). Qed.
Lemma lem7185888 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7185889 {A : Type'} (s : type686 A) (h1 : @FINITE (A -> Prop) s) : (term467 A s) = (and True).
Proof. exact (MK_COMB (@lem7185888) (@lem7185887 A s h1)). Qed.
Lemma lem7185949 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term166 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7185950 (p : Prop) (q : Prop) (p' : Prop) : term167 p q p'.
Proof. exact (fun q' : Prop => @lem7185949 p q p' q'). Qed.
Lemma lem7185951 (p : Prop) (q : Prop) : term168 p q.
Proof. exact (fun p' : Prop => @lem7185950 p q p'). Qed.
Lemma lem7185952 {A : Type'} (s : type686 A) (_96221 : A -> Prop) : term180 A s _96221.
Proof. exact (@lem7185951 (@IN (A -> Prop) _96221 s) (@FINITE A _96221)). Qed.
Lemma lem7185953 {A : Type'} (s : type686 A) (_96221 : A -> Prop) (p' : Prop) : term181 A s _96221 p'.
Proof. exact (@lem7185952 A s _96221 p'). Qed.
Lemma lem7185954 {A : Type'} (s : type686 A) (_96221 : A -> Prop) (p' : Prop) : (term181 A s _96221 p') = (term182 A s _96221 p').
Proof. exact (eq_refl (term181 A s _96221 p')). Qed.
Lemma lem7185955 {A : Type'} (s : type686 A) (_96221 : A -> Prop) (p' : Prop) : term182 A s _96221 p'.
Proof. exact (EQ_MP (@lem7185954 A s _96221 p') (@lem7185953 A s _96221 p')). Qed.
Lemma lem7185956 {A : Type'} (s : type686 A) (_96221 : A -> Prop) (p' : Prop) (q' : Prop) : term183 A s _96221 p' q'.
Proof. exact (@lem7185955 A s _96221 p' q'). Qed.
Lemma lem7185957 {A : Type'} (s : type686 A) (_96221 : A -> Prop) (p' : Prop) (q' : Prop) : (term183 A s _96221 p' q') = (term184 A s _96221 p' q').
Proof. exact (eq_refl (term183 A s _96221 p' q')). Qed.
Lemma lem7185958 {A : Type'} (s : type686 A) (_96221 : A -> Prop) (p' : Prop) (q' : Prop) : term184 A s _96221 p' q'.
Proof. exact (EQ_MP (@lem7185957 A s _96221 p' q') (@lem7185956 A s _96221 p' q')). Qed.
Lemma lem7185959 {A : Type'} (_96221 : A -> Prop) (s : type686 A) : (@IN (A -> Prop) _96221 s) = (@IN (A -> Prop) _96221 s).
Proof. exact (eq_refl (@IN (A -> Prop) _96221 s)). Qed.
Lemma lem7185960 {A : Type'} (_96221 : A -> Prop) (s : type686 A) (q' : Prop) : term185 A _96221 s q'.
Proof. exact (@lem7185958 A s _96221 (@IN (A -> Prop) _96221 s) q'). Qed.
Lemma lem7185961 {A : Type'} (_96221 : A -> Prop) (s : type686 A) (q' : Prop) : term186 A _96221 s q'.
Proof. exact (@lem7185960 A _96221 s q' (@lem7185959 A _96221 s)). Qed.
Lemma lem7185962 {A : Type'} (_96221 : A -> Prop) (s : type686 A) (h1 : @IN (A -> Prop) _96221 s) : @IN (A -> Prop) _96221 s.
Proof. exact (h1). Qed.
Lemma lem7185963 {A : Type'} (_96221 : A -> Prop) (s : type686 A) : (@IN (A -> Prop) _96221 s) = ((@IN (A -> Prop) _96221 s) = True).
Proof. exact (@lem7 (@IN (A -> Prop) _96221 s)). Qed.
Lemma lem7185966 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (s : type686 A) (h1 : term108 A t s) : term187 A t s t'.
Proof. exact (fun h0 : term100 A t t' s => @lem7185775 A t t' s h1 h0). Qed.
Lemma lem7185967 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (s : type686 A) (h1 : term108 A t s) : term187 A t s t'.
Proof. exact (@lem7185966 A t' t s h1). Qed.
Lemma lem7185968 {A : Type'} (_96221 : A -> Prop) (t : A -> Prop) (s : type686 A) (h1 : term108 A t s) : term187 A t s _96221.
Proof. exact (@lem7185967 A _96221 t s h1). Qed.
Lemma lem7185974 {A : Type'} (_96221 : A -> Prop) (s : type686 A) (h1 : @IN (A -> Prop) _96221 s) : (@IN (A -> Prop) _96221 s) = True.
Proof. exact (EQ_MP (@lem7185963 A _96221 s) (@lem7185962 A _96221 s h1)). Qed.
Lemma lem7185975 {A : Type'} (_96221 : A -> Prop) (t : A -> Prop) : (term188 A _96221 t) = (term188 A _96221 t).
Proof. exact (eq_refl (term188 A _96221 t)). Qed.
Lemma lem7185976 {A : Type'} (t : A -> Prop) (_96221 : A -> Prop) (s : type686 A) (h1 : @IN (A -> Prop) _96221 s) : (term100 A t _96221 s) = (term189 A _96221 t).
Proof. exact (MK_COMB (@lem7185975 A _96221 t) (@lem7185974 A _96221 s h1)). Qed.
Lemma lem7185978 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem7185979 {A : Type'} (_96221 : A -> Prop) (t : A -> Prop) : (term189 A _96221 t) = True.
Proof. exact (@lem7185978 (_96221 = t)). Qed.
Lemma lem7185980 {A : Type'} (t : A -> Prop) (_96221 : A -> Prop) (s : type686 A) (h1 : @IN (A -> Prop) _96221 s) : (term100 A t _96221 s) = True.
Proof. exact (TRANS (@lem7185976 A t _96221 s h1) (@lem7185979 A _96221 t)). Qed.
Lemma lem7185981 {A : Type'} (t : A -> Prop) (_96221 : A -> Prop) (s : type686 A) (h1 : @IN (A -> Prop) _96221 s) : True = (term100 A t _96221 s).
Proof. exact (SYM (@lem7185980 A t _96221 s h1)). Qed.
Lemma lem7185982 {A : Type'} (t : A -> Prop) (_96221 : A -> Prop) (s : type686 A) (h1 : @IN (A -> Prop) _96221 s) : term100 A t _96221 s.
Proof. exact (EQ_MP (@lem7185981 A t _96221 s h1) (@lem0)). Qed.
Lemma lem7185983 {A : Type'} (t : A -> Prop) (_96221 : A -> Prop) (s : type686 A) (h1 : term108 A t s) (h2 : @IN (A -> Prop) _96221 s) : (@FINITE A _96221) = True.
Proof. exact (@lem7185968 A _96221 t s h1 (@lem7185982 A t _96221 s h2)). Qed.
Lemma lem7185984 {A : Type'} (_96221 : A -> Prop) (t : A -> Prop) (s : type686 A) (h1 : term108 A t s) : term190 A s _96221.
Proof. exact (fun h0 : @IN (A -> Prop) _96221 s => @lem7185983 A t _96221 s h1 h0). Qed.
Lemma lem7185985 {A : Type'} (_96221 : A -> Prop) (s : type686 A) : term191 A _96221 s.
Proof. exact (@lem7185961 A _96221 s True). Qed.
Lemma lem7185986 {A : Type'} (_96221 : A -> Prop) (t : A -> Prop) (s : type686 A) (h1 : term108 A t s) : (term192 A s _96221) = (term193 A _96221 s).
Proof. exact (@lem7185985 A _96221 s (@lem7185984 A _96221 t s h1)). Qed.
Lemma lem7185988 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7185989 {A : Type'} (_96221 : A -> Prop) (s : type686 A) : (term193 A _96221 s) = True.
Proof. exact (@lem7185988 (@IN (A -> Prop) _96221 s)). Qed.
Lemma lem7185990 {A : Type'} (_96221 : A -> Prop) (t : A -> Prop) (s : type686 A) (h1 : term108 A t s) : (term192 A s _96221) = True.
Proof. exact (TRANS (@lem7185986 A _96221 t s h1) (@lem7185989 A _96221 s)). Qed.
Lemma lem7185993 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term108 A t s) : (term194 A s) = (term195 A).
Proof. exact (fun_ext (fun _96221 : A -> Prop => @lem7185990 A _96221 t s h1)). Qed.
Lemma lem7185994 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7185995 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term108 A t s) : (term196 A s) = (term197 A).
Proof. exact (MK_COMB (@lem7185994 A) (@lem7185993 A t s h1)). Qed.
Lemma lem7185997 {A : Type'} (t : Prop) : (term198 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7185998 {A : Type'} (t : Prop) : (term199 A t) = t.
Proof. exact (@lem7185997 (A -> Prop) t). Qed.
Lemma lem7185999 {A : Type'} : (term197 A) = True.
Proof. exact (@lem7185998 A True). Qed.
Lemma lem7186000 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term108 A t s) : (term196 A s) = True.
Proof. exact (TRANS (@lem7185995 A t s h1) (@lem7185999 A)). Qed.
Lemma lem7186001 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term108 A t s) (h2 : @FINITE (A -> Prop) s) : (term462 A s) = (True /\ True).
Proof. exact (MK_COMB (@lem7185889 A s h2) (@lem7186000 A t s h1)). Qed.
Lemma lem7186003 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7186004 : (True /\ True) = True.
Proof. exact (@lem7186003 True). Qed.
Lemma lem7186005 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term108 A t s) (h2 : @FINITE (A -> Prop) s) : (term462 A s) = True.
Proof. exact (TRANS (@lem7186001 A t s h1 h2) (@lem7186004)). Qed.
Lemma lem7186006 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term108 A t s) (h2 : @FINITE (A -> Prop) s) : (term461 A s) = True.
Proof. exact (TRANS (@lem7185883 A s) (@lem7186005 A t s h1 h2)). Qed.
Lemma lem7186007 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7186008 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term108 A t s) (h2 : @FINITE (A -> Prop) s) : (term468 A s) = (and True).
Proof. exact (MK_COMB (@lem7186007) (@lem7186006 A t s h1 h2)). Qed.
Lemma lem7186016 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term166 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7186017 (p : Prop) (q : Prop) (p' : Prop) : term167 p q p'.
Proof. exact (fun q' : Prop => @lem7186016 p q p' q'). Qed.
Lemma lem7186018 (p : Prop) (q : Prop) : term168 p q.
Proof. exact (fun p' : Prop => @lem7186017 p q p'). Qed.
Lemma lem7186019 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (x : A) : term469 A t s f x.
Proof. exact (@lem7186018 (term470 A x t s) ((f x) = term34)). Qed.
Lemma lem7186020 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (x : A) (p' : Prop) : term471 A t s f x p'.
Proof. exact (@lem7186019 A t s f x p'). Qed.
Lemma lem7186021 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (x : A) (p' : Prop) : (term471 A t s f x p') = (term472 A t s f x p').
Proof. exact (eq_refl (term471 A t s f x p')). Qed.
Lemma lem7186022 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (x : A) (p' : Prop) : term472 A t s f x p'.
Proof. exact (EQ_MP (@lem7186021 A t s f x p') (@lem7186020 A t s f x p')). Qed.
Lemma lem7186023 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (x : A) (p' : Prop) (q' : Prop) : term473 A t s f x p' q'.
Proof. exact (@lem7186022 A t s f x p' q'). Qed.
Lemma lem7186024 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (x : A) (p' : Prop) (q' : Prop) : (term473 A t s f x p' q') = (term474 A t s f x p' q').
Proof. exact (eq_refl (term473 A t s f x p' q')). Qed.
Lemma lem7186025 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (x : A) (p' : Prop) (q' : Prop) : term474 A t s f x p' q'.
Proof. exact (EQ_MP (@lem7186024 A t s f x p' q') (@lem7186023 A t s f x p' q')). Qed.
Lemma lem7186027 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term459 A x s t) = (term305 A s x t).
Proof. exact (EQ_MP (@lem7185764 A s x t) (@lem7185763 A s t x)). Qed.
Lemma lem7186028 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term459 A x s t) = (term305 A s x t).
Proof. exact (@lem7186027 A s x t). Qed.
Lemma lem7186029 {A : Type'} (t : A -> Prop) (x : A) (s : type686 A) : (term470 A x t s) = (term475 A t x s).
Proof. exact (@lem7186028 A t x (@UNIONS A s)). Qed.
Lemma lem7186033 {A : Type'} (s : type686 A) (x : A) : (term452 A x s) = (term453 A s x).
Proof. exact (EQ_MP (@lem7185755 A s x) (@lem7185754 A s x)). Qed.
Lemma lem7186034 {A : Type'} (s : type686 A) (x : A) : (term452 A x s) = (term453 A s x).
Proof. exact (@lem7186033 A s x). Qed.
Lemma lem7186053 {A : Type'} (x : A) (t : A -> Prop) : (term426 A x t) = (term426 A x t).
Proof. exact (eq_refl (term426 A x t)). Qed.
Lemma lem7186054 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) : (term475 A t x s) = (term476 A t s x).
Proof. exact (MK_COMB (@lem7186053 A x t) (@lem7186034 A s x)). Qed.
Lemma lem7186075 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) : (term470 A x t s) = (term476 A t s x).
Proof. exact (TRANS (@lem7186029 A t x s) (@lem7186054 A t s x)). Qed.
Lemma lem7186076 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (x : A) (q' : Prop) : term477 A f t s x q'.
Proof. exact (@lem7186025 A t s f x (term476 A t s x) q'). Qed.
Lemma lem7186077 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (x : A) (q' : Prop) : term478 A f t s x q'.
Proof. exact (@lem7186076 A f t s x q' (@lem7186075 A t s x)). Qed.
Lemma lem7186118 {A : Type'} (f : A -> real) (x : A) : ((f x) = term34) = ((f x) = term34).
Proof. exact (eq_refl ((f x) = term34)). Qed.
Lemma lem7186119 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (x : A) : term479 A t s f x.
Proof. exact (fun h0 : term476 A t s x => @lem7186118 A f x). Qed.
Lemma lem7186120 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (x : A) : term480 A t s f x.
Proof. exact (@lem7186077 A f t s x ((f x) = term34)). Qed.
Lemma lem7186121 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (x : A) : (term481 A t s f x) = (term482 A t s f x).
Proof. exact (@lem7186120 A t s f x (@lem7186119 A t s f x)). Qed.
Lemma lem7186255 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term483 A t s f) = (term484 A t s f).
Proof. exact (fun_ext (fun x : A => @lem7186121 A t s f x)). Qed.
Lemma lem7186389 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7186390 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term485 A t s f) = (term486 A t s f).
Proof. exact (MK_COMB (@lem7186389 A) (@lem7186255 A t s f)). Qed.
Lemma lem7186528 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term108 A t s) (h2 : @FINITE (A -> Prop) s) : (term487 A t s f) = (term488 A t s f).
Proof. exact (MK_COMB (@lem7186008 A t s h1 h2) (@lem7186390 A t s f)). Qed.
Lemma lem7186530 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7186531 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term488 A t s f) = (term486 A t s f).
Proof. exact (@lem7186530 (term486 A t s f)). Qed.
Lemma lem7186669 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term108 A t s) (h2 : @FINITE (A -> Prop) s) : (term487 A t s f) = (term486 A t s f).
Proof. exact (TRANS (@lem7186528 A f t s h1 h2) (@lem7186531 A t s f)). Qed.
Lemma lem7186670 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term108 A t s) (h2 : @FINITE (A -> Prop) s) (h3 : term217 A t s) : (term489 A t s f) = (term488 A t s f).
Proof. exact (MK_COMB (@lem7185878 A t s h1 h3) (@lem7186669 A f t s h1 h2)). Qed.
Lemma lem7186672 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7186673 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term488 A t s f) = (term486 A t s f).
Proof. exact (@lem7186672 (term486 A t s f)). Qed.
Lemma lem7186811 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term108 A t s) (h2 : @FINITE (A -> Prop) s) (h3 : term217 A t s) : (term489 A t s f) = (term486 A t s f).
Proof. exact (TRANS (@lem7186670 A f t s h1 h2 h3) (@lem7186673 A t s f)). Qed.
Lemma lem7186812 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term108 A t s) (h2 : @FINITE (A -> Prop) s) (h3 : term217 A t s) : (term486 A t s f) = (term489 A t s f).
Proof. exact (SYM (@lem7186811 A f t s h1 h2 h3)). Qed.
Lemma lem7186814 (p : Prop) : p = (term261 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7186815 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term486 A t s f) = (term490 A t s f).
Proof. exact (@lem7186814 (term486 A t s f)). Qed.
Lemma lem7186816 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term490 A t s f) = (term486 A t s f).
Proof. exact (SYM (@lem7186815 A t s f)). Qed.
Lemma lem7186817 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term491 A t s f) : term491 A t s f.
Proof. exact (h1). Qed.
Lemma lem7186820 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term492 A t s f) : term492 A t s f.
Proof. exact (h1). Qed.
Lemma lem7186821 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : term493 A t s f.
Proof. exact (fun h0 : term492 A t s f => @lem7186820 A t s f h0). Qed.
Lemma lem7186822 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term493 A t s f) : term493 A t s f.
Proof. exact (h1). Qed.
Lemma lem7186823 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term492 A t s f) : term492 A t s f.
Proof. exact (h1). Qed.
Lemma lem7186824 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term492 A t s f) (h2 : term493 A t s f) : term492 A t s f.
Proof. exact (@lem7186822 A t s f h2 (@lem7186823 A t s f h1)). Qed.
Lemma lem7186825 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term492 A t s f) : term494 A t s f.
Proof. exact (fun h0 : term493 A t s f => @lem7186824 A t s f h1 h0). Qed.
Lemma lem7186826 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term493 A t s f) : term493 A t s f.
Proof. exact (h1). Qed.
Lemma lem7186827 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term492 A t s f) (h2 : term493 A t s f) : term492 A t s f.
Proof. exact (@lem7186825 A t s f h1 (@lem7186826 A t s f h2)). Qed.
Lemma lem7186828 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term493 A t s f) : term493 A t s f.
Proof. exact (fun h0 : term492 A t s f => @lem7186827 A t s f h0 h1). Qed.
Lemma lem7186829 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : term495 A t s f.
Proof. exact (fun h0 : term493 A t s f => @lem7186828 A t s f h0). Qed.
Lemma lem7186832 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : term493 A t s f.
Proof. exact (@lem7186829 A t s f (@lem7186821 A t s f)). Qed.
Lemma lem7186833 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : term493 A t s f.
Proof. exact (@lem7186832 A t s f). Qed.
Lemma lem7186889 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7186890 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term490 A t s f) = (term496 A t s f).
Proof. exact (@lem7186889 (term491 A t s f)). Qed.
Lemma lem7186892 (t : Prop) : (term269 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7186893 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term496 A t s f) = (term486 A t s f).
Proof. exact (@lem7186892 (term486 A t s f)). Qed.
Lemma lem7186898 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term490 A t s f) = (term486 A t s f).
Proof. exact (TRANS (@lem7186890 A t s f) (@lem7186893 A t s f)). Qed.
Lemma lem7186953 {A : Type'} (s : type686 A) : (term85 A s) = (term85 A s).
Proof. exact (eq_refl (term85 A s)). Qed.
Lemma lem7186954 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term497 A t s f) = (term498 A t s f).
Proof. exact (MK_COMB (@lem7186953 A s) (@lem7186898 A t s f)). Qed.
Lemma lem7186957 {A : Type'} (t : A -> Prop) (s : type686 A) : (term499 A t s) = (term499 A t s).
Proof. exact (eq_refl (term499 A t s)). Qed.
Lemma lem7186958 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term500 A t s f) = (term501 A t s f).
Proof. exact (MK_COMB (@lem7186957 A t s) (@lem7186954 A t s f)). Qed.
Lemma lem7186961 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term270 A t s f) = (term270 A t s f).
Proof. exact (eq_refl (term270 A t s f)). Qed.
Lemma lem7186962 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term502 A t s f) = (term503 A t s f).
Proof. exact (MK_COMB (@lem7186961 A t s f) (@lem7186958 A t s f)). Qed.
Lemma lem7186965 {A : Type'} (t : A -> Prop) (s : type686 A) : (term273 A t s) = (term273 A t s).
Proof. exact (eq_refl (term273 A t s)). Qed.
Lemma lem7186966 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term492 A t s f) = (term504 A t s f).
Proof. exact (MK_COMB (@lem7186965 A t s) (@lem7186962 A t s f)). Qed.
Lemma lem7186969 {A : Type'} (s : type686 A) (f : A -> real) : (term505 A s f) = (term506 A s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7186966 A t s f)). Qed.
Lemma lem7186970 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7186971 {A : Type'} (s : type686 A) (f : A -> real) : (term507 A s f) = (term508 A s f).
Proof. exact (MK_COMB (@lem7186970 A) (@lem7186969 A s f)). Qed.
Lemma lem7186976 {A : Type'} (f : A -> real) : (term509 A f) = (term510 A f).
Proof. exact (fun_ext (fun s : type686 A => @lem7186971 A s f)). Qed.
Lemma lem7186977 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem7186978 {A : Type'} (f : A -> real) : (term511 A f) = (term512 A f).
Proof. exact (MK_COMB (@lem7186977 A) (@lem7186976 A f)). Qed.
Lemma lem7186983 {A : Type'} : (term513 A) = (term514 A).
Proof. exact (fun_ext (fun f : A -> real => @lem7186978 A f)). Qed.
Lemma lem7186984 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7186993 {A : Type'} : (term515 A) = (term516 A).
Proof. exact (MK_COMB (@lem7186984 A) (@lem7186983 A)). Qed.
Lemma lem7186994 {A : Type'} (f : A -> real) (x : A) : ((f x) = term34) = ((f x) = term34).
Proof. exact (eq_refl ((f x) = term34)). Qed.
Lemma lem7186999 {A : Type'} (s : type686 A) (x : A) (t : A -> Prop) : (term517 A s x t) = (term517 A s x t).
Proof. exact (eq_refl (term517 A s x t)). Qed.
Lemma lem7187000 {A : Type'} (s : type686 A) (x : A) : (term518 A s x) = (term518 A s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7186999 A s x t)). Qed.
Lemma lem7187001 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem7187002 {A : Type'} (s : type686 A) (x : A) : (term453 A s x) = (term453 A s x).
Proof. exact (MK_COMB (@lem7187001 A) (@lem7187000 A s x)). Qed.
Lemma lem7187005 {A : Type'} (x : A) (t : A -> Prop) : (term426 A x t) = (term426 A x t).
Proof. exact (eq_refl (term426 A x t)). Qed.
Lemma lem7187006 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) : (term476 A t s x) = (term476 A t s x).
Proof. exact (MK_COMB (@lem7187005 A x t) (@lem7187002 A s x)). Qed.
Lemma lem7187007 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7187008 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) : (term519 A t s x) = (term519 A t s x).
Proof. exact (MK_COMB (@lem7187007) (@lem7187006 A t s x)). Qed.
Lemma lem7187009 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (x : A) : (term482 A t s f x) = (term482 A t s f x).
Proof. exact (MK_COMB (@lem7187008 A t s x) (@lem7186994 A f x)). Qed.
Lemma lem7187010 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term484 A t s f) = (term484 A t s f).
Proof. exact (fun_ext (fun x : A => @lem7187009 A t s f x)). Qed.
Lemma lem7187011 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7187012 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term486 A t s f) = (term486 A t s f).
Proof. exact (MK_COMB (@lem7187011 A) (@lem7187010 A t s f)). Qed.
Lemma lem7187015 {A : Type'} (s : type686 A) : (term85 A s) = (term85 A s).
Proof. exact (eq_refl (term85 A s)). Qed.
Lemma lem7187016 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term498 A t s f) = (term498 A t s f).
Proof. exact (MK_COMB (@lem7187015 A s) (@lem7187012 A t s f)). Qed.
Lemma lem7187021 {A : Type'} (t : A -> Prop) (s : type686 A) : (term499 A t s) = (term499 A t s).
Proof. exact (eq_refl (term499 A t s)). Qed.
Lemma lem7187022 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term501 A t s f) = (term501 A t s f).
Proof. exact (MK_COMB (@lem7187021 A t s) (@lem7187016 A t s f)). Qed.
Lemma lem7187053 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> real) (x : A) : (term121 A t s t1 t2 f x) = (term121 A t s t1 t2 f x).
Proof. exact (eq_refl (term121 A t s t1 t2 f x)). Qed.
Lemma lem7187054 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> real) : (term123 A t s t1 t2 f) = (term123 A t s t1 t2 f).
Proof. exact (fun_ext (fun x : A => @lem7187053 A t s t1 t2 f x)). Qed.
Lemma lem7187055 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7187056 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> real) : (term125 A t s t1 t2 f) = (term125 A t s t1 t2 f).
Proof. exact (MK_COMB (@lem7187055 A) (@lem7187054 A t s t1 t2 f)). Qed.
Lemma lem7187057 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (f : A -> real) : (term127 A t s t1 f) = (term127 A t s t1 f).
Proof. exact (fun_ext (fun t2 : A -> Prop => @lem7187056 A t s t1 t2 f)). Qed.
Lemma lem7187058 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7187059 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (f : A -> real) : (term129 A t s t1 f) = (term129 A t s t1 f).
Proof. exact (MK_COMB (@lem7187058 A) (@lem7187057 A t s t1 f)). Qed.
Lemma lem7187060 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term131 A t s f) = (term131 A t s f).
Proof. exact (fun_ext (fun t1 : A -> Prop => @lem7187059 A t s t1 f)). Qed.
Lemma lem7187061 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7187062 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term133 A t s f) = (term133 A t s f).
Proof. exact (MK_COMB (@lem7187061 A) (@lem7187060 A t s f)). Qed.
Lemma lem7187063 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7187064 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term270 A t s f) = (term270 A t s f).
Proof. exact (MK_COMB (@lem7187063) (@lem7187062 A t s f)). Qed.
Lemma lem7187065 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term503 A t s f) = (term503 A t s f).
Proof. exact (MK_COMB (@lem7187064 A t s f) (@lem7187022 A t s f)). Qed.
Lemma lem7187074 {A : Type'} (t : A -> Prop) (s : type686 A) (t' : A -> Prop) : (term104 A t s t') = (term104 A t s t').
Proof. exact (eq_refl (term104 A t s t')). Qed.
Lemma lem7187075 {A : Type'} (t : A -> Prop) (s : type686 A) : (term106 A t s) = (term106 A t s).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem7187074 A t s t')). Qed.
Lemma lem7187076 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7187077 {A : Type'} (t : A -> Prop) (s : type686 A) : (term108 A t s) = (term108 A t s).
Proof. exact (MK_COMB (@lem7187076 A) (@lem7187075 A t s)). Qed.
Lemma lem7187078 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7187079 {A : Type'} (t : A -> Prop) (s : type686 A) : (term273 A t s) = (term273 A t s).
Proof. exact (MK_COMB (@lem7187078) (@lem7187077 A t s)). Qed.
Lemma lem7187080 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term504 A t s f) = (term504 A t s f).
Proof. exact (MK_COMB (@lem7187079 A t s) (@lem7187065 A t s f)). Qed.
Lemma lem7187081 {A : Type'} (s : type686 A) (f : A -> real) : (term506 A s f) = (term506 A s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7187080 A t s f)). Qed.
Lemma lem7187082 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7187083 {A : Type'} (s : type686 A) (f : A -> real) : (term508 A s f) = (term508 A s f).
Proof. exact (MK_COMB (@lem7187082 A) (@lem7187081 A s f)). Qed.
Lemma lem7187084 {A : Type'} (f : A -> real) : (term510 A f) = (term510 A f).
Proof. exact (fun_ext (fun s : type686 A => @lem7187083 A s f)). Qed.
Lemma lem7187085 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem7187086 {A : Type'} (f : A -> real) : (term512 A f) = (term512 A f).
Proof. exact (MK_COMB (@lem7187085 A) (@lem7187084 A f)). Qed.
Lemma lem7187087 {A : Type'} : (term514 A) = (term514 A).
Proof. exact (fun_ext (fun f : A -> real => @lem7187086 A f)). Qed.
Lemma lem7187088 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7187089 {A : Type'} : (term516 A) = (term516 A).
Proof. exact (MK_COMB (@lem7187088 A) (@lem7187087 A)). Qed.
Lemma lem7187178 {A : Type'} : (term515 A) = (term516 A).
Proof. exact (TRANS (@lem7186993 A) (@lem7187089 A)). Qed.
Lemma lem7187179 {A : Type'} : (term516 A) = (term515 A).
Proof. exact (SYM (@lem7187178 A)). Qed.
Lemma lem7187181 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term133 A t s f) : term133 A t s f.
Proof. exact (h1). Qed.
Lemma lem7187184 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) (h1 : term476 A t s x) : term476 A t s x.
Proof. exact (h1). Qed.
Lemma lem7187186 (p : Prop) : p = (term261 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7187187 {A : Type'} (f : A -> real) (x : A) : ((f x) = term34) = (term293 A f x).
Proof. exact (@lem7187186 ((f x) = term34)). Qed.
Lemma lem7187188 {A : Type'} (f : A -> real) (x : A) : (term293 A f x) = ((f x) = term34).
Proof. exact (SYM (@lem7187187 A f x)). Qed.
Lemma lem7187189 {A : Type'} (f : A -> real) (x : A) (h1 : term294 A f x) : term294 A f x.
Proof. exact (h1). Qed.
Lemma lem7187249 {A : Type'} (t : A -> Prop) (t1 : A -> Prop) (s : type686 A) : (term295 A t t1 s) = (term296 A t t1 s).
Proof. exact (@lem17160 (t1 = t) (@IN (A -> Prop) t1 s)). Qed.
Lemma lem7187256 {A : Type'} (t : A -> Prop) (t2 : A -> Prop) (s : type686 A) : (term295 A t t2 s) = (term296 A t t2 s).
Proof. exact (@lem17160 (t2 = t) (@IN (A -> Prop) t2 s)). Qed.
Lemma lem7187259 {A : Type'} (t1 : A -> Prop) (t2 : A -> Prop) : (term297 A t1 t2) = (t1 = t2).
Proof. exact (@lem16933 (t1 = t2)). Qed.
Lemma lem7187266 {A : Type'} (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term298 A t1 x t2) = (term299 A t1 x t2).
Proof. exact (@lem17045 (@IN A x t1) (@IN A x t2)). Qed.
Lemma lem7187267 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7187268 {A : Type'} (t1 : A -> Prop) (t2 : A -> Prop) : (term300 A t1 t2) = (term188 A t1 t2).
Proof. exact (MK_COMB (@lem7187267) (@lem7187259 A t1 t2)). Qed.
Lemma lem7187269 {A : Type'} (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term301 A t1 x t2) = (term302 A t1 x t2).
Proof. exact (MK_COMB (@lem7187268 A t1 t2) (@lem7187266 A t1 x t2)). Qed.
Lemma lem7187270 {A : Type'} (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term303 A t1 x t2) = (term301 A t1 x t2).
Proof. exact (@lem17045 (term304 A t1 t2) (term305 A t1 x t2)). Qed.
Lemma lem7187271 {A : Type'} (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term303 A t1 x t2) = (term302 A t1 x t2).
Proof. exact (TRANS (@lem7187270 A t1 x t2) (@lem7187269 A t1 x t2)). Qed.
Lemma lem7187272 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7187273 {A : Type'} (t : A -> Prop) (t2 : A -> Prop) (s : type686 A) : (term306 A t t2 s) = (term307 A t t2 s).
Proof. exact (MK_COMB (@lem7187272) (@lem7187256 A t t2 s)). Qed.
Lemma lem7187274 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term308 A t s t1 x t2) = (term309 A t s t1 x t2).
Proof. exact (MK_COMB (@lem7187273 A t t2 s) (@lem7187271 A t1 x t2)). Qed.
Lemma lem7187275 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term310 A t s t1 x t2) = (term308 A t s t1 x t2).
Proof. exact (@lem17045 (term100 A t t2 s) (term113 A t1 x t2)). Qed.
Lemma lem7187276 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term310 A t s t1 x t2) = (term309 A t s t1 x t2).
Proof. exact (TRANS (@lem7187275 A t s t1 x t2) (@lem7187274 A t s t1 x t2)). Qed.
Lemma lem7187277 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7187278 {A : Type'} (t : A -> Prop) (t1 : A -> Prop) (s : type686 A) : (term306 A t t1 s) = (term307 A t t1 s).
Proof. exact (MK_COMB (@lem7187277) (@lem7187249 A t t1 s)). Qed.
Lemma lem7187279 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term311 A t s t1 x t2) = (term312 A t s t1 x t2).
Proof. exact (MK_COMB (@lem7187278 A t t1 s) (@lem7187276 A t s t1 x t2)). Qed.
Lemma lem7187280 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term313 A t s t1 x t2) = (term311 A t s t1 x t2).
Proof. exact (@lem17045 (term100 A t t1 s) (term115 A t s t1 x t2)). Qed.
Lemma lem7187281 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term313 A t s t1 x t2) = (term312 A t s t1 x t2).
Proof. exact (TRANS (@lem7187280 A t s t1 x t2) (@lem7187279 A t s t1 x t2)). Qed.
Lemma lem7187282 {A : Type'} (f : A -> real) (x : A) : ((f x) = term34) = ((f x) = term34).
Proof. exact (eq_refl ((f x) = term34)). Qed.
Lemma lem7187283 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7187284 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term314 A t s t1 x t2) = (term315 A t s t1 x t2).
Proof. exact (MK_COMB (@lem7187283) (@lem7187281 A t s t1 x t2)). Qed.
Lemma lem7187285 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> real) (x : A) : (term316 A t s t1 t2 f x) = (term317 A t s t1 t2 f x).
Proof. exact (MK_COMB (@lem7187284 A t s t1 x t2) (@lem7187282 A f x)). Qed.
Lemma lem7187286 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> real) (x : A) : (term121 A t s t1 t2 f x) = (term316 A t s t1 t2 f x).
Proof. exact (@lem17265 (term117 A t s t1 x t2) ((f x) = term34)). Qed.
Lemma lem7187287 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> real) (x : A) : (term121 A t s t1 t2 f x) = (term317 A t s t1 t2 f x).
Proof. exact (TRANS (@lem7187286 A t s t1 t2 f x) (@lem7187285 A t s t1 t2 f x)). Qed.
Lemma lem7187288 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> real) : (term123 A t s t1 t2 f) = (term318 A t s t1 t2 f).
Proof. exact (fun_ext (fun x : A => @lem7187287 A t s t1 t2 f x)). Qed.
Lemma lem7187289 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7187290 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> real) : (term125 A t s t1 t2 f) = (term319 A t s t1 t2 f).
Proof. exact (MK_COMB (@lem7187289 A) (@lem7187288 A t s t1 t2 f)). Qed.
Lemma lem7187291 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (f : A -> real) : (term127 A t s t1 f) = (term320 A t s t1 f).
Proof. exact (fun_ext (fun t2 : A -> Prop => @lem7187290 A t s t1 t2 f)). Qed.
Lemma lem7187292 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7187293 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (f : A -> real) : (term129 A t s t1 f) = (term321 A t s t1 f).
Proof. exact (MK_COMB (@lem7187292 A) (@lem7187291 A t s t1 f)). Qed.
Lemma lem7187294 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term131 A t s f) = (term322 A t s f).
Proof. exact (fun_ext (fun t1 : A -> Prop => @lem7187293 A t s t1 f)). Qed.
Lemma lem7187295 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7187356 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term133 A t s f) = (term323 A t s f).
Proof. exact (MK_COMB (@lem7187295 A) (@lem7187294 A t s f)). Qed.
Lemma lem7187357 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term133 A t s f) : term323 A t s f.
Proof. exact (EQ_MP (@lem7187356 A t s f) (@lem7187181 A t s f h1)). Qed.
Lemma lem7187363 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term217 A t s) : term217 A t s.
Proof. exact (h1). Qed.
Lemma lem7187375 {A : Type'} (s : type686 A) (x : A) (t : A -> Prop) : (term517 A s x t) = (term517 A s x t).
Proof. exact (eq_refl (term517 A s x t)). Qed.
Lemma lem7187376 {A : Type'} (s : type686 A) (x : A) : (term518 A s x) = (term518 A s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7187375 A s x t)). Qed.
Lemma lem7187377 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem7187378 {A : Type'} (s : type686 A) (x : A) : (term453 A s x) = (term453 A s x).
Proof. exact (MK_COMB (@lem7187377 A) (@lem7187376 A s x)). Qed.
Lemma lem7187380 {A : Type'} (x : A) (t : A -> Prop) : (term426 A x t) = (term426 A x t).
Proof. exact (eq_refl (term426 A x t)). Qed.
Lemma lem7187381 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) : (term476 A t s x) = (term476 A t s x).
Proof. exact (MK_COMB (@lem7187380 A x t) (@lem7187378 A s x)). Qed.
Lemma lem7187432 {A : Type'} (P : Prop) (Q : A -> Prop) : (term520 A P Q) = (term521 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem7187433 {A : Type'} (P : Prop) (Q : type686 A) : (term522 A P Q) = (term523 A P Q).
Proof. exact (@lem7187432 (A -> Prop) P Q). Qed.
Lemma lem7187434 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) : (term524 A t s x) = (term525 A t s x).
Proof. exact (@lem7187433 A (@IN A x t) (term518 A s x)). Qed.
Lemma lem7187435 {A : Type'} (s : type686 A) (x : A) (t : A -> Prop) : (term526 A s x t) = (term517 A s x t).
Proof. exact (eq_refl (term526 A s x t)). Qed.
Lemma lem7187436 {A : Type'} (s : type686 A) (x : A) : (term527 A s x) = (term518 A s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem7187435 A s x t)). Qed.
Lemma lem7187437 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem7187438 {A : Type'} (s : type686 A) (x : A) : (term528 A s x) = (term453 A s x).
Proof. exact (MK_COMB (@lem7187437 A) (@lem7187436 A s x)). Qed.
Lemma lem7187439 {A : Type'} (x : A) (t : A -> Prop) : (term426 A x t) = (term426 A x t).
Proof. exact (eq_refl (term426 A x t)). Qed.
Lemma lem7187440 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) : (term524 A t s x) = (term476 A t s x).
Proof. exact (MK_COMB (@lem7187439 A x t) (@lem7187438 A s x)). Qed.
Lemma lem7187441 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7187442 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) : (term529 A t s x) = (term530 A t s x).
Proof. exact (MK_COMB (@lem7187441) (@lem7187440 A t s x)). Qed.
Lemma lem7187443 {A : Type'} (s : type686 A) (x : A) (t' : A -> Prop) : (term526 A s x t') = (term517 A s x t').
Proof. exact (eq_refl (term526 A s x t')). Qed.
Lemma lem7187444 {A : Type'} (x : A) (t : A -> Prop) : (term426 A x t) = (term426 A x t).
Proof. exact (eq_refl (term426 A x t)). Qed.
Lemma lem7187445 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) : (term531 A t s x t') = (term532 A t s x t').
Proof. exact (MK_COMB (@lem7187444 A x t) (@lem7187443 A s x t')). Qed.
Lemma lem7187446 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) : (term533 A t s x) = (term534 A t s x).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem7187445 A t s x t')). Qed.
Lemma lem7187447 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem7187448 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) : (term525 A t s x) = (term535 A t s x).
Proof. exact (MK_COMB (@lem7187447 A) (@lem7187446 A t s x)). Qed.
Lemma lem7187449 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) : ((term524 A t s x) = (term525 A t s x)) = ((term476 A t s x) = (term535 A t s x)).
Proof. exact (MK_COMB (@lem7187442 A t s x) (@lem7187448 A t s x)). Qed.
Lemma lem7187451 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) : (term476 A t s x) = (term535 A t s x).
Proof. exact (EQ_MP (@lem7187449 A t s x) (@lem7187434 A t s x)). Qed.
Lemma lem7187452 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) : (term476 A t s x) = (term535 A t s x).
Proof. exact (TRANS (@lem7187381 A t s x) (@lem7187451 A t s x)). Qed.
Lemma lem7187453 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) (h1 : term476 A t s x) : term535 A t s x.
Proof. exact (EQ_MP (@lem7187452 A t s x) (@lem7187184 A t s x h1)). Qed.
Lemma lem7187459 {A : Type'} (f : A -> real) (x : A) (h1 : term294 A f x) : term294 A f x.
Proof. exact (h1). Qed.
Lemma lem7187566 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> real) (x : A) : (term317 A t s t1 t2 f x) = (term317 A t s t1 t2 f x).
Proof. exact (eq_refl (term317 A t s t1 t2 f x)). Qed.
Lemma lem7187567 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> real) : (term318 A t s t1 t2 f) = (term318 A t s t1 t2 f).
Proof. exact (fun_ext (fun x : A => @lem7187566 A t s t1 t2 f x)). Qed.
Lemma lem7187568 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7187569 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> real) : (term319 A t s t1 t2 f) = (term319 A t s t1 t2 f).
Proof. exact (MK_COMB (@lem7187568 A) (@lem7187567 A t s t1 t2 f)). Qed.
Lemma lem7187570 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (f : A -> real) : (term320 A t s t1 f) = (term320 A t s t1 f).
Proof. exact (fun_ext (fun t2 : A -> Prop => @lem7187569 A t s t1 t2 f)). Qed.
Lemma lem7187571 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7187572 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (f : A -> real) : (term321 A t s t1 f) = (term321 A t s t1 f).
Proof. exact (MK_COMB (@lem7187571 A) (@lem7187570 A t s t1 f)). Qed.
Lemma lem7187573 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term322 A t s f) = (term322 A t s f).
Proof. exact (fun_ext (fun t1 : A -> Prop => @lem7187572 A t s t1 f)). Qed.
Lemma lem7187574 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7187575 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term323 A t s f) = (term323 A t s f).
Proof. exact (MK_COMB (@lem7187574 A) (@lem7187573 A t s f)). Qed.
Lemma lem7187576 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term133 A t s f) : term323 A t s f.
Proof. exact (EQ_MP (@lem7187575 A t s f) (@lem7187357 A t s f h1)). Qed.
Lemma lem7187584 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term217 A t s) : term217 A t s.
Proof. exact (h1). Qed.
Lemma lem7187602 {A : Type'} (f : A -> real) (x : A) (h1 : term294 A f x) : term294 A f x.
Proof. exact (h1). Qed.
Lemma lem7187624 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term532 A t s x t') : term532 A t s x t'.
Proof. exact (h1). Qed.
Lemma lem7187625 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term532 A t s x t') : term517 A s x t'.
Proof. exact (proj2 (@lem7187624 A t s x t' h1)). Qed.
Lemma lem7187653 {A : Type'} (f : A -> real) (x : A) : ((f x) = term34) = ((f x) = term34).
Proof. exact (eq_refl ((f x) = term34)). Qed.
Lemma lem7187682 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term309 A t s t1 x t2) = (term326 A t s t1 x t2).
Proof. exact (@lem19699 (term304 A t2 t) (term217 A t2 s) (term302 A t1 x t2)). Qed.
Lemma lem7187689 {A : Type'} (t : A -> Prop) (t1 : A -> Prop) (s : type686 A) : (term307 A t t1 s) = (term307 A t t1 s).
Proof. exact (eq_refl (term307 A t t1 s)). Qed.
Lemma lem7187690 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term312 A t s t1 x t2) = (term327 A t s t1 x t2).
Proof. exact (MK_COMB (@lem7187689 A t t1 s) (@lem7187682 A t s t1 x t2)). Qed.
Lemma lem7187691 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term327 A t s t1 x t2) = (term328 A t s t1 x t2).
Proof. exact (@lem19490 (term329 A t t1 x t2) (term296 A t t1 s) (term330 A s t1 x t2)). Qed.
Lemma lem7187698 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term331 A t s t1 x t2) = (term332 A t s t1 x t2).
Proof. exact (@lem19699 (term304 A t1 t) (term217 A t1 s) (term330 A s t1 x t2)). Qed.
Lemma lem7187705 {A : Type'} (s : type686 A) (t : A -> Prop) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term333 A s t t1 x t2) = (term334 A s t t1 x t2).
Proof. exact (@lem19699 (term304 A t1 t) (term217 A t1 s) (term329 A t t1 x t2)). Qed.
Lemma lem7187706 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7187707 {A : Type'} (s : type686 A) (t : A -> Prop) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term335 A s t t1 x t2) = (term336 A s t t1 x t2).
Proof. exact (MK_COMB (@lem7187706) (@lem7187705 A s t t1 x t2)). Qed.
Lemma lem7187708 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term328 A t s t1 x t2) = (term337 A t s t1 x t2).
Proof. exact (MK_COMB (@lem7187707 A s t t1 x t2) (@lem7187698 A t s t1 x t2)). Qed.
Lemma lem7187709 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term327 A t s t1 x t2) = (term337 A t s t1 x t2).
Proof. exact (TRANS (@lem7187691 A t s t1 x t2) (@lem7187708 A t s t1 x t2)). Qed.
Lemma lem7187710 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term312 A t s t1 x t2) = (term337 A t s t1 x t2).
Proof. exact (TRANS (@lem7187690 A t s t1 x t2) (@lem7187709 A t s t1 x t2)). Qed.
Lemma lem7187711 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7187712 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (x : A) (t2 : A -> Prop) : (term315 A t s t1 x t2) = (term338 A t s t1 x t2).
Proof. exact (MK_COMB (@lem7187711) (@lem7187710 A t s t1 x t2)). Qed.
Lemma lem7187713 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> real) (x : A) : (term317 A t s t1 t2 f x) = (term339 A t s t1 t2 f x).
Proof. exact (MK_COMB (@lem7187712 A t s t1 x t2) (@lem7187653 A f x)). Qed.
Lemma lem7187714 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> real) (x : A) : (term339 A t s t1 t2 f x) = (term340 A t s t1 t2 f x).
Proof. exact (@lem19699 (term334 A s t t1 x t2) (term332 A t s t1 x t2) ((f x) = term34)). Qed.
Lemma lem7187721 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> real) (x : A) : (term341 A t s t1 t2 f x) = (term342 A t s t1 t2 f x).
Proof. exact (@lem19699 (term343 A t s t1 x t2) (term344 A s t1 x t2) ((f x) = term34)). Qed.
Lemma lem7187728 {A : Type'} (s : type686 A) (t : A -> Prop) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> real) (x : A) : (term345 A s t t1 t2 f x) = (term346 A s t t1 t2 f x).
Proof. exact (@lem19699 (term347 A t t1 x t2) (term348 A s t t1 x t2) ((f x) = term34)). Qed.
Lemma lem7187729 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7187730 {A : Type'} (s : type686 A) (t : A -> Prop) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> real) (x : A) : (term349 A s t t1 t2 f x) = (term350 A s t t1 t2 f x).
Proof. exact (MK_COMB (@lem7187729) (@lem7187728 A s t t1 t2 f x)). Qed.
Lemma lem7187731 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> real) (x : A) : (term340 A t s t1 t2 f x) = (term351 A t s t1 t2 f x).
Proof. exact (MK_COMB (@lem7187730 A s t t1 t2 f x) (@lem7187721 A t s t1 t2 f x)). Qed.
Lemma lem7187732 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> real) (x : A) : (term339 A t s t1 t2 f x) = (term351 A t s t1 t2 f x).
Proof. exact (TRANS (@lem7187714 A t s t1 t2 f x) (@lem7187731 A t s t1 t2 f x)). Qed.
Lemma lem7187733 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> real) (x : A) : (term317 A t s t1 t2 f x) = (term351 A t s t1 t2 f x).
Proof. exact (TRANS (@lem7187713 A t s t1 t2 f x) (@lem7187732 A t s t1 t2 f x)). Qed.
Lemma lem7187734 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> real) : (term318 A t s t1 t2 f) = (term352 A t s t1 t2 f).
Proof. exact (fun_ext (fun x : A => @lem7187733 A t s t1 t2 f x)). Qed.
Lemma lem7187735 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7187736 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (t2 : A -> Prop) (f : A -> real) : (term319 A t s t1 t2 f) = (term353 A t s t1 t2 f).
Proof. exact (MK_COMB (@lem7187735 A) (@lem7187734 A t s t1 t2 f)). Qed.
Lemma lem7187737 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (f : A -> real) : (term320 A t s t1 f) = (term354 A t s t1 f).
Proof. exact (fun_ext (fun t2 : A -> Prop => @lem7187736 A t s t1 t2 f)). Qed.
Lemma lem7187738 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7187739 {A : Type'} (t : A -> Prop) (s : type686 A) (t1 : A -> Prop) (f : A -> real) : (term321 A t s t1 f) = (term355 A t s t1 f).
Proof. exact (MK_COMB (@lem7187738 A) (@lem7187737 A t s t1 f)). Qed.
Lemma lem7187740 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term322 A t s f) = (term356 A t s f).
Proof. exact (fun_ext (fun t1 : A -> Prop => @lem7187739 A t s t1 f)). Qed.
Lemma lem7187741 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7187743 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term323 A t s f) = (term357 A t s f).
Proof. exact (MK_COMB (@lem7187741 A) (@lem7187740 A t s f)). Qed.
Lemma lem7187744 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term133 A t s f) : term357 A t s f.
Proof. exact (EQ_MP (@lem7187743 A t s f) (@lem7187576 A t s f h1)). Qed.
Lemma lem7187748 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term217 A t s) : term217 A t s.
Proof. exact (h1). Qed.
Lemma lem7187756 {A : Type'} (f : A -> real) (x : A) (h1 : term294 A f x) : term294 A f x.
Proof. exact (h1). Qed.
Lemma lem7187772 {A : Type'} (_96241 : A -> Prop) (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term133 A t s f) : term358 A t s f _96241.
Proof. exact (@lem7187744 A t s f h1 _96241). Qed.
Lemma lem7187773 {A : Type'} (t : A -> Prop) (s : type686 A) (_96241 : A -> Prop) (f : A -> real) : (term358 A t s f _96241) = (term355 A t s _96241 f).
Proof. exact (eq_refl (term358 A t s f _96241)). Qed.
Lemma lem7187774 {A : Type'} (_96241 : A -> Prop) (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term133 A t s f) : term355 A t s _96241 f.
Proof. exact (EQ_MP (@lem7187773 A t s _96241 f) (@lem7187772 A _96241 t s f h1)). Qed.
Lemma lem7187775 {A : Type'} (_96241 : A -> Prop) (_96242 : A -> Prop) (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term133 A t s f) : term359 A t s _96241 f _96242.
Proof. exact (@lem7187774 A _96241 t s f h1 _96242). Qed.
Lemma lem7187776 {A : Type'} (t : A -> Prop) (s : type686 A) (_96241 : A -> Prop) (_96242 : A -> Prop) (f : A -> real) : (term359 A t s _96241 f _96242) = (term353 A t s _96241 _96242 f).
Proof. exact (eq_refl (term359 A t s _96241 f _96242)). Qed.
Lemma lem7187777 {A : Type'} (_96241 : A -> Prop) (_96242 : A -> Prop) (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term133 A t s f) : term353 A t s _96241 _96242 f.
Proof. exact (EQ_MP (@lem7187776 A t s _96241 _96242 f) (@lem7187775 A _96241 _96242 t s f h1)). Qed.
Lemma lem7187778 {A : Type'} (_96241 : A -> Prop) (_96242 : A -> Prop) (_96243 : A) (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term133 A t s f) : term360 A t s _96241 _96242 f _96243.
Proof. exact (@lem7187777 A _96241 _96242 t s f h1 _96243). Qed.
Lemma lem7187779 {A : Type'} (t : A -> Prop) (s : type686 A) (_96241 : A -> Prop) (_96242 : A -> Prop) (f : A -> real) (_96243 : A) : (term360 A t s _96241 _96242 f _96243) = (term351 A t s _96241 _96242 f _96243).
Proof. exact (eq_refl (term360 A t s _96241 _96242 f _96243)). Qed.
Lemma lem7187780 {A : Type'} (_96241 : A -> Prop) (_96242 : A -> Prop) (_96243 : A) (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term133 A t s f) : term351 A t s _96241 _96242 f _96243.
Proof. exact (EQ_MP (@lem7187779 A t s _96241 _96242 f _96243) (@lem7187778 A _96241 _96242 _96243 t s f h1)). Qed.
Lemma lem7187782 {A : Type'} (_96241 : A -> Prop) (_96242 : A -> Prop) (_96243 : A) (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term133 A t s f) : term346 A s t _96241 _96242 f _96243.
Proof. exact (proj1 (@lem7187780 A _96241 _96242 _96243 t s f h1)). Qed.
Lemma lem7187785 {A : Type'} (_96241 : A -> Prop) (_96242 : A -> Prop) (_96243 : A) (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term133 A t s f) : term536 A s t _96241 _96242 f _96243.
Proof. exact (proj2 (@lem7187782 A _96241 _96242 _96243 t s f h1)). Qed.
Lemma lem7187790 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term217 A t s) : term217 A t s.
Proof. exact (h1). Qed.
Lemma lem7187794 {A : Type'} (f : A -> real) (x : A) (h1 : term294 A f x) : term294 A f x.
Proof. exact (h1). Qed.
Lemma lem7187894 {A : Type'} (s : type686 A) (t : A -> Prop) (_96241 : A -> Prop) (_96242 : A -> Prop) (f : A -> real) (_96243 : A) : (term536 A s t _96241 _96242 f _96243) = (term537 A s t _96241 _96242 f _96243).
Proof. exact (@lem7178818 (term217 A _96241 s) (term329 A t _96241 _96243 _96242) ((f _96243) = term34)). Qed.
Lemma lem7187895 {A : Type'} (t : A -> Prop) (_96241 : A -> Prop) (_96242 : A -> Prop) (f : A -> real) (_96243 : A) : (term538 A t _96241 _96242 f _96243) = (term539 A t _96241 _96242 f _96243).
Proof. exact (@lem7178818 (term304 A _96242 t) (term302 A _96241 _96243 _96242) ((f _96243) = term34)). Qed.
Lemma lem7187896 {A : Type'} (_96241 : A -> Prop) (_96242 : A -> Prop) (f : A -> real) (_96243 : A) : (term365 A _96241 _96242 f _96243) = (term366 A _96241 _96242 f _96243).
Proof. exact (@lem7178818 (_96241 = _96242) (term299 A _96241 _96243 _96242) ((f _96243) = term34)). Qed.
Lemma lem7187903 {A : Type'} (_96241 : A -> Prop) (_96242 : A -> Prop) (f : A -> real) (_96243 : A) : (term367 A _96241 _96242 f _96243) = (term368 A _96241 _96242 f _96243).
Proof. exact (@lem7178818 (term369 A _96243 _96241) (term369 A _96243 _96242) ((f _96243) = term34)). Qed.
Lemma lem7187904 {A : Type'} (_96241 : A -> Prop) (_96242 : A -> Prop) : (term188 A _96241 _96242) = (term188 A _96241 _96242).
Proof. exact (eq_refl (term188 A _96241 _96242)). Qed.
Lemma lem7187907 {A : Type'} (_96241 : A -> Prop) (_96242 : A -> Prop) (f : A -> real) (_96243 : A) : (term366 A _96241 _96242 f _96243) = (term370 A _96241 _96242 f _96243).
Proof. exact (MK_COMB (@lem7187904 A _96241 _96242) (@lem7187903 A _96241 _96242 f _96243)). Qed.
Lemma lem7187908 {A : Type'} (_96241 : A -> Prop) (_96242 : A -> Prop) (f : A -> real) (_96243 : A) : (term365 A _96241 _96242 f _96243) = (term370 A _96241 _96242 f _96243).
Proof. exact (TRANS (@lem7187896 A _96241 _96242 f _96243) (@lem7187907 A _96241 _96242 f _96243)). Qed.
Lemma lem7187909 {A : Type'} (_96242 : A -> Prop) (t : A -> Prop) : (term540 A _96242 t) = (term540 A _96242 t).
Proof. exact (eq_refl (term540 A _96242 t)). Qed.
Lemma lem7187912 {A : Type'} (t : A -> Prop) (_96241 : A -> Prop) (_96242 : A -> Prop) (f : A -> real) (_96243 : A) : (term539 A t _96241 _96242 f _96243) = (term541 A t _96241 _96242 f _96243).
Proof. exact (MK_COMB (@lem7187909 A _96242 t) (@lem7187908 A _96241 _96242 f _96243)). Qed.
Lemma lem7187913 {A : Type'} (t : A -> Prop) (_96241 : A -> Prop) (_96242 : A -> Prop) (f : A -> real) (_96243 : A) : (term538 A t _96241 _96242 f _96243) = (term541 A t _96241 _96242 f _96243).
Proof. exact (TRANS (@lem7187895 A t _96241 _96242 f _96243) (@lem7187912 A t _96241 _96242 f _96243)). Qed.
Lemma lem7187914 {A : Type'} (_96241 : A -> Prop) (s : type686 A) : (term371 A _96241 s) = (term371 A _96241 s).
Proof. exact (eq_refl (term371 A _96241 s)). Qed.
Lemma lem7187917 {A : Type'} (s : type686 A) (t : A -> Prop) (_96241 : A -> Prop) (_96242 : A -> Prop) (f : A -> real) (_96243 : A) : (term537 A s t _96241 _96242 f _96243) = (term542 A s t _96241 _96242 f _96243).
Proof. exact (MK_COMB (@lem7187914 A _96241 s) (@lem7187913 A t _96241 _96242 f _96243)). Qed.
Lemma lem7187919 {A : Type'} (s : type686 A) (t : A -> Prop) (_96241 : A -> Prop) (_96242 : A -> Prop) (f : A -> real) (_96243 : A) : (term536 A s t _96241 _96242 f _96243) = (term542 A s t _96241 _96242 f _96243).
Proof. exact (TRANS (@lem7187894 A s t _96241 _96242 f _96243) (@lem7187917 A s t _96241 _96242 f _96243)). Qed.
Lemma lem7187920 {A : Type'} (_96241 : A -> Prop) (_96242 : A -> Prop) (_96243 : A) (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term133 A t s f) : term542 A s t _96241 _96242 f _96243.
Proof. exact (EQ_MP (@lem7187919 A s t _96241 _96242 f _96243) (@lem7187785 A _96241 _96242 _96243 t s f h1)). Qed.
Lemma lem7187976 {A : Type'} : (@IN (A -> Prop)) = (@IN (A -> Prop)).
Proof. exact (eq_refl (@IN (A -> Prop))). Qed.
Lemma lem7187977 {A : Type'} (_96252 : A -> Prop) (_96254 : A -> Prop) (h1 : _96252 = _96254) : _96252 = _96254.
Proof. exact (h1). Qed.
Lemma lem7187978 {A : Type'} (_96253 : type686 A) (_96255 : type686 A) (h1 : _96253 = _96255) : _96253 = _96255.
Proof. exact (h1). Qed.
Lemma lem7187979 {A : Type'} (_96252 : A -> Prop) (_96254 : A -> Prop) (h1 : _96252 = _96254) : (@IN (A -> Prop) _96252) = (@IN (A -> Prop) _96254).
Proof. exact (MK_COMB (@lem7187976 A) (@lem7187977 A _96252 _96254 h1)). Qed.
Lemma lem7187980 {A : Type'} (_96252 : A -> Prop) (_96254 : A -> Prop) (_96253 : type686 A) (_96255 : type686 A) (h1 : _96252 = _96254) (h2 : _96253 = _96255) : (@IN (A -> Prop) _96252 _96253) = (@IN (A -> Prop) _96254 _96255).
Proof. exact (MK_COMB (@lem7187979 A _96252 _96254 h1) (@lem7187978 A _96253 _96255 h2)). Qed.
Lemma lem7187982 (b : Prop) (a : Prop) : term543 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem7187983 {A : Type'} (_96254 : A -> Prop) (_96255 : type686 A) (_96252 : A -> Prop) (_96253 : type686 A) : term544 A _96254 _96255 _96252 _96253.
Proof. exact (@lem7187982 (@IN (A -> Prop) _96254 _96255) (@IN (A -> Prop) _96252 _96253)). Qed.
Lemma lem7187984 {A : Type'} (_96252 : A -> Prop) (_96254 : A -> Prop) (_96253 : type686 A) (_96255 : type686 A) (h1 : _96252 = _96254) (h2 : _96253 = _96255) : term545 A _96254 _96255 _96252 _96253.
Proof. exact (@lem7187983 A _96254 _96255 _96252 _96253 (@lem7187980 A _96252 _96254 _96253 _96255 h1 h2)). Qed.
Lemma lem7187985 {A : Type'} (_96255 : type686 A) (_96253 : type686 A) (_96252 : A -> Prop) (_96254 : A -> Prop) (h1 : _96252 = _96254) : term546 A _96254 _96255 _96252 _96253.
Proof. exact (fun h0 : _96253 = _96255 => @lem7187984 A _96252 _96254 _96253 _96255 h1 h0). Qed.
Lemma lem7187987 (a : Prop) (b : Prop) : (a -> b) = (term547 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem7187988 {A : Type'} (_96254 : A -> Prop) (_96255 : type686 A) (_96252 : A -> Prop) (_96253 : type686 A) : (term546 A _96254 _96255 _96252 _96253) = (term548 A _96254 _96255 _96252 _96253).
Proof. exact (@lem7187987 (_96253 = _96255) (term545 A _96254 _96255 _96252 _96253)). Qed.
Lemma lem7187989 {A : Type'} (_96255 : type686 A) (_96253 : type686 A) (_96252 : A -> Prop) (_96254 : A -> Prop) (h1 : _96252 = _96254) : term548 A _96254 _96255 _96252 _96253.
Proof. exact (EQ_MP (@lem7187988 A _96254 _96255 _96252 _96253) (@lem7187985 A _96255 _96253 _96252 _96254 h1)). Qed.
Lemma lem7187990 {A : Type'} (_96254 : A -> Prop) (_96255 : type686 A) (_96252 : A -> Prop) (_96253 : type686 A) : term549 A _96254 _96255 _96252 _96253.
Proof. exact (fun h0 : _96252 = _96254 => @lem7187989 A _96255 _96253 _96252 _96254 h0). Qed.
Lemma lem7187992 (a : Prop) (b : Prop) : (a -> b) = (term547 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem7187993 {A : Type'} (_96254 : A -> Prop) (_96255 : type686 A) (_96252 : A -> Prop) (_96253 : type686 A) : (term549 A _96254 _96255 _96252 _96253) = (term550 A _96254 _96255 _96252 _96253).
Proof. exact (@lem7187992 (_96252 = _96254) (term548 A _96254 _96255 _96252 _96253)). Qed.
Lemma lem7187994 {A : Type'} (_96254 : A -> Prop) (_96255 : type686 A) (_96252 : A -> Prop) (_96253 : type686 A) : term550 A _96254 _96255 _96252 _96253.
Proof. exact (EQ_MP (@lem7187993 A _96254 _96255 _96252 _96253) (@lem7187990 A _96254 _96255 _96252 _96253)). Qed.
Lemma lem7188030 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term532 A t s x t') : @IN (A -> Prop) t' s.
Proof. exact (proj1 (@lem7187625 A t s x t' h1)). Qed.
Lemma lem7188031 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term532 A t s x t') : term374 A t' s.
Proof. exact (fun h0 : term217 A t' s => @lem7188030 A t s x t' h1). Qed.
Lemma lem7188033 (p : Prop) : (term375 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7188034 {A : Type'} (t' : A -> Prop) (s : type686 A) : (term374 A t' s) = (@IN (A -> Prop) t' s).
Proof. exact (@lem7188033 (@IN (A -> Prop) t' s)). Qed.
Lemma lem7188035 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term532 A t s x t') : @IN (A -> Prop) t' s.
Proof. exact (EQ_MP (@lem7188034 A t' s) (@lem7188031 A t s x t' h1)). Qed.
Lemma lem7188037 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem21386 (A -> Prop) x). Qed.
Lemma lem7188038 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem7188037 A x). Qed.
Lemma lem7188039 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (@lem7188038 A t). Qed.
Lemma lem7188040 {A : Type'} (t : A -> Prop) : term551 A t.
Proof. exact (fun h0 : term552 A t => @lem7188039 A t). Qed.
Lemma lem7188042 (p : Prop) : (term375 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7188043 {A : Type'} (t : A -> Prop) : (term551 A t) = (t = t).
Proof. exact (@lem7188042 (t = t)). Qed.
Lemma lem7188044 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (EQ_MP (@lem7188043 A t) (@lem7188040 A t)). Qed.
Lemma lem7188046 {A : Type'} (x : type686 A) : x = x.
Proof. exact (@lem21386 (type686 A) x). Qed.
Lemma lem7188047 {A : Type'} (x : type686 A) : x = x.
Proof. exact (@lem7188046 A x). Qed.
Lemma lem7188048 {A : Type'} (s : type686 A) : s = s.
Proof. exact (@lem7188047 A s). Qed.
Lemma lem7188049 {A : Type'} (s : type686 A) : term553 A s.
Proof. exact (fun h0 : term554 A s => @lem7188048 A s). Qed.
Lemma lem7188051 (p : Prop) : (term375 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7188052 {A : Type'} (s : type686 A) : (term553 A s) = (s = s).
Proof. exact (@lem7188051 (s = s)). Qed.
Lemma lem7188053 {A : Type'} (s : type686 A) : s = s.
Proof. exact (EQ_MP (@lem7188052 A s) (@lem7188049 A s)). Qed.
Lemma lem7188055 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term217 A t s) : term217 A t s.
Proof. exact (h1). Qed.
Lemma lem7188056 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term217 A t s) : term555 A t s.
Proof. exact (fun h0 : @IN (A -> Prop) t s => @lem7188055 A t s h1). Qed.
Lemma lem7188058 (p : Prop) : (term378 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7188059 {A : Type'} (t : A -> Prop) (s : type686 A) : (term555 A t s) = (term217 A t s).
Proof. exact (@lem7188058 (@IN (A -> Prop) t s)). Qed.
Lemma lem7188060 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term217 A t s) : term217 A t s.
Proof. exact (EQ_MP (@lem7188059 A t s) (@lem7188056 A t s h1)). Qed.
Lemma lem7188062 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term532 A t s x t') : @IN (A -> Prop) t' s.
Proof. exact (proj1 (@lem7187625 A t s x t' h1)). Qed.
Lemma lem7188063 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term532 A t s x t') : term374 A t' s.
Proof. exact (fun h0 : term217 A t' s => @lem7188062 A t s x t' h1). Qed.
Lemma lem7188065 (p : Prop) : (term375 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7188066 {A : Type'} (t' : A -> Prop) (s : type686 A) : (term374 A t' s) = (@IN (A -> Prop) t' s).
Proof. exact (@lem7188065 (@IN (A -> Prop) t' s)). Qed.
Lemma lem7188067 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term532 A t s x t') : @IN (A -> Prop) t' s.
Proof. exact (EQ_MP (@lem7188066 A t' s) (@lem7188063 A t s x t' h1)). Qed.
Lemma lem7188069 (b : Prop) (a : Prop) : (a \/ b) = (term411 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7188070 {A : Type'} (_96255 : type686 A) (_96253 : type686 A) (_96252 : A -> Prop) (_96254 : A -> Prop) : (term550 A _96254 _96255 _96252 _96253) = (term556 A _96255 _96253 _96252 _96254).
Proof. exact (@lem7188069 (term548 A _96254 _96255 _96252 _96253) (term304 A _96252 _96254)). Qed.
Lemma lem7188072 (a : Prop) (b : Prop) : (term413 a b) = (term414 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7188073 {A : Type'} (_96254 : A -> Prop) (_96255 : type686 A) (_96252 : A -> Prop) (_96253 : type686 A) : (term557 A _96254 _96255 _96252 _96253) = (term558 A _96254 _96255 _96252 _96253).
Proof. exact (@lem7188072 (term559 A _96253 _96255) (term545 A _96254 _96255 _96252 _96253)). Qed.
Lemma lem7188075 (a : Prop) : (term269 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7188076 {A : Type'} (_96253 : type686 A) (_96255 : type686 A) : (term560 A _96253 _96255) = (_96253 = _96255).
Proof. exact (@lem7188075 (_96253 = _96255)). Qed.
Lemma lem7188077 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7188078 {A : Type'} (_96253 : type686 A) (_96255 : type686 A) : (term561 A _96253 _96255) = (term562 A _96253 _96255).
Proof. exact (MK_COMB (@lem7188077) (@lem7188076 A _96253 _96255)). Qed.
Lemma lem7188080 (a : Prop) (b : Prop) : (term413 a b) = (term414 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7188081 {A : Type'} (_96254 : A -> Prop) (_96255 : type686 A) (_96252 : A -> Prop) (_96253 : type686 A) : (term563 A _96254 _96255 _96252 _96253) = (term564 A _96254 _96255 _96252 _96253).
Proof. exact (@lem7188080 (@IN (A -> Prop) _96254 _96255) (term217 A _96252 _96253)). Qed.
Lemma lem7188083 (a : Prop) : (term269 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7188084 {A : Type'} (_96252 : A -> Prop) (_96253 : type686 A) : (term417 A _96252 _96253) = (@IN (A -> Prop) _96252 _96253).
Proof. exact (@lem7188083 (@IN (A -> Prop) _96252 _96253)). Qed.
Lemma lem7188085 {A : Type'} (_96254 : A -> Prop) (_96255 : type686 A) : (term565 A _96254 _96255) = (term565 A _96254 _96255).
Proof. exact (eq_refl (term565 A _96254 _96255)). Qed.
Lemma lem7188086 {A : Type'} (_96254 : A -> Prop) (_96255 : type686 A) (_96252 : A -> Prop) (_96253 : type686 A) : (term564 A _96254 _96255 _96252 _96253) = (term566 A _96254 _96255 _96252 _96253).
Proof. exact (MK_COMB (@lem7188085 A _96254 _96255) (@lem7188084 A _96252 _96253)). Qed.
Lemma lem7188087 {A : Type'} (_96254 : A -> Prop) (_96255 : type686 A) (_96252 : A -> Prop) (_96253 : type686 A) : (term563 A _96254 _96255 _96252 _96253) = (term566 A _96254 _96255 _96252 _96253).
Proof. exact (TRANS (@lem7188081 A _96254 _96255 _96252 _96253) (@lem7188086 A _96254 _96255 _96252 _96253)). Qed.
Lemma lem7188088 {A : Type'} (_96254 : A -> Prop) (_96255 : type686 A) (_96252 : A -> Prop) (_96253 : type686 A) : (term558 A _96254 _96255 _96252 _96253) = (term567 A _96254 _96255 _96252 _96253).
Proof. exact (MK_COMB (@lem7188078 A _96253 _96255) (@lem7188087 A _96254 _96255 _96252 _96253)). Qed.
Lemma lem7188089 {A : Type'} (_96254 : A -> Prop) (_96255 : type686 A) (_96252 : A -> Prop) (_96253 : type686 A) : (term557 A _96254 _96255 _96252 _96253) = (term567 A _96254 _96255 _96252 _96253).
Proof. exact (TRANS (@lem7188073 A _96254 _96255 _96252 _96253) (@lem7188088 A _96254 _96255 _96252 _96253)). Qed.
Lemma lem7188090 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7188091 {A : Type'} (_96254 : A -> Prop) (_96255 : type686 A) (_96252 : A -> Prop) (_96253 : type686 A) : (term568 A _96254 _96255 _96252 _96253) = (term569 A _96254 _96255 _96252 _96253).
Proof. exact (MK_COMB (@lem7188090) (@lem7188089 A _96254 _96255 _96252 _96253)). Qed.
Lemma lem7188092 {A : Type'} (_96252 : A -> Prop) (_96254 : A -> Prop) : (term304 A _96252 _96254) = (term304 A _96252 _96254).
Proof. exact (eq_refl (term304 A _96252 _96254)). Qed.
Lemma lem7188093 {A : Type'} (_96255 : type686 A) (_96253 : type686 A) (_96252 : A -> Prop) (_96254 : A -> Prop) : (term556 A _96255 _96253 _96252 _96254) = (term570 A _96255 _96253 _96252 _96254).
Proof. exact (MK_COMB (@lem7188091 A _96254 _96255 _96252 _96253) (@lem7188092 A _96252 _96254)). Qed.
Lemma lem7188094 {A : Type'} (_96255 : type686 A) (_96253 : type686 A) (_96252 : A -> Prop) (_96254 : A -> Prop) : (term550 A _96254 _96255 _96252 _96253) = (term570 A _96255 _96253 _96252 _96254).
Proof. exact (TRANS (@lem7188070 A _96255 _96253 _96252 _96254) (@lem7188093 A _96255 _96253 _96252 _96254)). Qed.
Lemma lem7188096 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term217 A t s) (h2 : term532 A t s x t') : term571 A t t' s.
Proof. exact (conj (@lem7188060 A t s h1) (@lem7188067 A t s x t' h2)). Qed.
Lemma lem7188097 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term217 A t s) (h2 : term532 A t s x t') : term572 A t t' s.
Proof. exact (conj (@lem7188053 A s) (@lem7188096 A t s x t' h1 h2)). Qed.
Lemma lem7188099 {A : Type'} (_96255 : type686 A) (_96253 : type686 A) (_96252 : A -> Prop) (_96254 : A -> Prop) : term570 A _96255 _96253 _96252 _96254.
Proof. exact (EQ_MP (@lem7188094 A _96255 _96253 _96252 _96254) (@lem7187994 A _96254 _96255 _96252 _96253)). Qed.
Lemma lem7188100 {A : Type'} (_96255 : type686 A) (_96253 : type686 A) (_96252 : A -> Prop) (_96254 : A -> Prop) : term570 A _96255 _96253 _96252 _96254.
Proof. exact (@lem7188099 A _96255 _96253 _96252 _96254). Qed.
Lemma lem7188101 {A : Type'} (s : type686 A) (t' : A -> Prop) (t : A -> Prop) : term573 A s t' t.
Proof. exact (@lem7188100 A s s t' t). Qed.
Lemma lem7188104 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term217 A t s) (h2 : term532 A t s x t') : term304 A t' t.
Proof. exact (@lem7188101 A s t' t (@lem7188097 A t s x t' h1 h2)). Qed.
Lemma lem7188105 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term217 A t s) (h2 : term532 A t s x t') : term574 A t' t.
Proof. exact (fun h0 : t' = t => @lem7188104 A t s x t' h1 h2). Qed.
Lemma lem7188107 (p : Prop) : (term378 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7188108 {A : Type'} (t' : A -> Prop) (t : A -> Prop) : (term574 A t' t) = (term304 A t' t).
Proof. exact (@lem7188107 (t' = t)). Qed.
Lemma lem7188109 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term217 A t s) (h2 : term532 A t s x t') : term304 A t' t.
Proof. exact (EQ_MP (@lem7188108 A t' t) (@lem7188105 A t s x t' h1 h2)). Qed.
Lemma lem7188111 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term532 A t s x t') : @IN A x t'.
Proof. exact (proj2 (@lem7187625 A t s x t' h1)). Qed.
Lemma lem7188112 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term532 A t s x t') : term376 A x t'.
Proof. exact (fun h0 : term369 A x t' => @lem7188111 A t s x t' h1). Qed.
Lemma lem7188114 (p : Prop) : (term375 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7188115 {A : Type'} (x : A) (t' : A -> Prop) : (term376 A x t') = (@IN A x t').
Proof. exact (@lem7188114 (@IN A x t')). Qed.
Lemma lem7188116 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term532 A t s x t') : @IN A x t'.
Proof. exact (EQ_MP (@lem7188115 A x t') (@lem7188112 A t s x t' h1)). Qed.
Lemma lem7188118 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term532 A t s x t') : @IN A x t.
Proof. exact (proj1 (@lem7187624 A t s x t' h1)). Qed.
Lemma lem7188119 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term532 A t s x t') : term376 A x t.
Proof. exact (fun h0 : term369 A x t => @lem7188118 A t s x t' h1). Qed.
Lemma lem7188121 (p : Prop) : (term375 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7188122 {A : Type'} (x : A) (t : A -> Prop) : (term376 A x t) = (@IN A x t).
Proof. exact (@lem7188121 (@IN A x t)). Qed.
Lemma lem7188123 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term532 A t s x t') : @IN A x t.
Proof. exact (EQ_MP (@lem7188122 A x t) (@lem7188119 A t s x t' h1)). Qed.
Lemma lem7188129 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7188130 {A : Type'} (t : A -> Prop) (s : type686 A) (_96241 : A -> Prop) (_96242 : A -> Prop) (f : A -> real) (_96243 : A) : (term542 A s t _96241 _96242 f _96243) = (term575 A t s _96241 _96242 f _96243).
Proof. exact (@lem7188129 (term304 A _96242 t) (term217 A _96241 s) (term370 A _96241 _96242 f _96243)). Qed.
Lemma lem7188146 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7188147 {A : Type'} (s : type686 A) (_96241 : A -> Prop) (_96242 : A -> Prop) (f : A -> real) (_96243 : A) : (term576 A s _96241 _96242 f _96243) = (term577 A s _96241 _96242 f _96243).
Proof. exact (@lem7188146 (_96241 = _96242) (term217 A _96241 s) (term368 A _96241 _96242 f _96243)). Qed.
Lemma lem7188163 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7188164 {A : Type'} (_96241 : A -> Prop) (s : type686 A) (_96242 : A -> Prop) (f : A -> real) (_96243 : A) : (term578 A s _96241 _96242 f _96243) = (term579 A _96241 s _96242 f _96243).
Proof. exact (@lem7188163 (term369 A _96243 _96241) (term217 A _96241 s) (term382 A _96242 f _96243)). Qed.
Lemma lem7188178 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7188179 {A : Type'} (_96242 : A -> Prop) (_96241 : A -> Prop) (s : type686 A) (f : A -> real) (_96243 : A) : (term580 A _96241 s _96242 f _96243) = (term581 A _96242 _96241 s f _96243).
Proof. exact (@lem7188178 (term369 A _96243 _96242) (term217 A _96241 s) ((f _96243) = term34)). Qed.
Lemma lem7188193 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7188194 {A : Type'} (f : A -> real) (_96243 : A) (_96241 : A -> Prop) (s : type686 A) : (term385 A _96241 s f _96243) = (term386 A f _96243 _96241 s).
Proof. exact (@lem7188193 ((f _96243) = term34) (term217 A _96241 s)). Qed.
Lemma lem7188202 {A : Type'} (_96243 : A) (_96242 : A -> Prop) : (term387 A _96243 _96242) = (term387 A _96243 _96242).
Proof. exact (eq_refl (term387 A _96243 _96242)). Qed.
Lemma lem7188203 {A : Type'} (_96242 : A -> Prop) (f : A -> real) (_96243 : A) (_96241 : A -> Prop) (s : type686 A) : (term581 A _96242 _96241 s f _96243) = (term582 A _96242 f _96243 _96241 s).
Proof. exact (MK_COMB (@lem7188202 A _96243 _96242) (@lem7188194 A f _96243 _96241 s)). Qed.
Lemma lem7188207 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7188208 {A : Type'} (f : A -> real) (_96243 : A) (_96242 : A -> Prop) (_96241 : A -> Prop) (s : type686 A) : (term582 A _96242 f _96243 _96241 s) = (term583 A f _96243 _96242 _96241 s).
Proof. exact (@lem7188207 ((f _96243) = term34) (term369 A _96243 _96242) (term217 A _96241 s)). Qed.
Lemma lem7188226 {A : Type'} (f : A -> real) (_96243 : A) (_96242 : A -> Prop) (_96241 : A -> Prop) (s : type686 A) : (term581 A _96242 _96241 s f _96243) = (term583 A f _96243 _96242 _96241 s).
Proof. exact (TRANS (@lem7188203 A _96242 f _96243 _96241 s) (@lem7188208 A f _96243 _96242 _96241 s)). Qed.
Lemma lem7188227 {A : Type'} (f : A -> real) (_96243 : A) (_96242 : A -> Prop) (_96241 : A -> Prop) (s : type686 A) : (term580 A _96241 s _96242 f _96243) = (term583 A f _96243 _96242 _96241 s).
Proof. exact (TRANS (@lem7188179 A _96242 _96241 s f _96243) (@lem7188226 A f _96243 _96242 _96241 s)). Qed.
Lemma lem7188228 {A : Type'} (_96243 : A) (_96241 : A -> Prop) : (term387 A _96243 _96241) = (term387 A _96243 _96241).
Proof. exact (eq_refl (term387 A _96243 _96241)). Qed.
Lemma lem7188229 {A : Type'} (f : A -> real) (_96243 : A) (_96242 : A -> Prop) (_96241 : A -> Prop) (s : type686 A) : (term579 A _96241 s _96242 f _96243) = (term584 A f _96243 _96242 _96241 s).
Proof. exact (MK_COMB (@lem7188228 A _96243 _96241) (@lem7188227 A f _96243 _96242 _96241 s)). Qed.
Lemma lem7188233 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7188234 {A : Type'} (f : A -> real) (_96243 : A) (_96242 : A -> Prop) (_96241 : A -> Prop) (s : type686 A) : (term584 A f _96243 _96242 _96241 s) = (term585 A f _96243 _96242 _96241 s).
Proof. exact (@lem7188233 ((f _96243) = term34) (term369 A _96243 _96241) (term586 A _96243 _96242 _96241 s)). Qed.
Lemma lem7188262 {A : Type'} (f : A -> real) (_96243 : A) (_96242 : A -> Prop) (_96241 : A -> Prop) (s : type686 A) : (term579 A _96241 s _96242 f _96243) = (term585 A f _96243 _96242 _96241 s).
Proof. exact (TRANS (@lem7188229 A f _96243 _96242 _96241 s) (@lem7188234 A f _96243 _96242 _96241 s)). Qed.
Lemma lem7188263 {A : Type'} (f : A -> real) (_96243 : A) (_96242 : A -> Prop) (_96241 : A -> Prop) (s : type686 A) : (term578 A s _96241 _96242 f _96243) = (term585 A f _96243 _96242 _96241 s).
Proof. exact (TRANS (@lem7188164 A _96241 s _96242 f _96243) (@lem7188262 A f _96243 _96242 _96241 s)). Qed.
Lemma lem7188264 {A : Type'} (_96241 : A -> Prop) (_96242 : A -> Prop) : (term188 A _96241 _96242) = (term188 A _96241 _96242).
Proof. exact (eq_refl (term188 A _96241 _96242)). Qed.
Lemma lem7188265 {A : Type'} (f : A -> real) (_96243 : A) (_96242 : A -> Prop) (_96241 : A -> Prop) (s : type686 A) : (term577 A s _96241 _96242 f _96243) = (term587 A f _96243 _96242 _96241 s).
Proof. exact (MK_COMB (@lem7188264 A _96241 _96242) (@lem7188263 A f _96243 _96242 _96241 s)). Qed.
Lemma lem7188276 {A : Type'} (f : A -> real) (_96243 : A) (_96242 : A -> Prop) (_96241 : A -> Prop) (s : type686 A) : (term576 A s _96241 _96242 f _96243) = (term587 A f _96243 _96242 _96241 s).
Proof. exact (TRANS (@lem7188147 A s _96241 _96242 f _96243) (@lem7188265 A f _96243 _96242 _96241 s)). Qed.
Lemma lem7188277 {A : Type'} (_96242 : A -> Prop) (t : A -> Prop) : (term540 A _96242 t) = (term540 A _96242 t).
Proof. exact (eq_refl (term540 A _96242 t)). Qed.
Lemma lem7188278 {A : Type'} (t : A -> Prop) (f : A -> real) (_96243 : A) (_96242 : A -> Prop) (_96241 : A -> Prop) (s : type686 A) : (term575 A t s _96241 _96242 f _96243) = (term588 A t f _96243 _96242 _96241 s).
Proof. exact (MK_COMB (@lem7188277 A _96242 t) (@lem7188276 A f _96243 _96242 _96241 s)). Qed.
Lemma lem7188282 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7188283 {A : Type'} (t : A -> Prop) (f : A -> real) (_96243 : A) (_96242 : A -> Prop) (_96241 : A -> Prop) (s : type686 A) : (term588 A t f _96243 _96242 _96241 s) = (term589 A t f _96243 _96242 _96241 s).
Proof. exact (@lem7188282 (_96241 = _96242) (term304 A _96242 t) (term585 A f _96243 _96242 _96241 s)). Qed.
Lemma lem7188299 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7188300 {A : Type'} (f : A -> real) (t : A -> Prop) (_96243 : A) (_96242 : A -> Prop) (_96241 : A -> Prop) (s : type686 A) : (term590 A t f _96243 _96242 _96241 s) = (term591 A f t _96243 _96242 _96241 s).
Proof. exact (@lem7188299 ((f _96243) = term34) (term304 A _96242 t) (term592 A _96243 _96242 _96241 s)). Qed.
Lemma lem7188340 {A : Type'} (_96241 : A -> Prop) (_96242 : A -> Prop) : (term188 A _96241 _96242) = (term188 A _96241 _96242).
Proof. exact (eq_refl (term188 A _96241 _96242)). Qed.
Lemma lem7188341 {A : Type'} (f : A -> real) (t : A -> Prop) (_96243 : A) (_96242 : A -> Prop) (_96241 : A -> Prop) (s : type686 A) : (term589 A t f _96243 _96242 _96241 s) = (term593 A f t _96243 _96242 _96241 s).
Proof. exact (MK_COMB (@lem7188340 A _96241 _96242) (@lem7188300 A f t _96243 _96242 _96241 s)). Qed.
Lemma lem7188352 {A : Type'} (f : A -> real) (t : A -> Prop) (_96243 : A) (_96242 : A -> Prop) (_96241 : A -> Prop) (s : type686 A) : (term588 A t f _96243 _96242 _96241 s) = (term593 A f t _96243 _96242 _96241 s).
Proof. exact (TRANS (@lem7188283 A t f _96243 _96242 _96241 s) (@lem7188341 A f t _96243 _96242 _96241 s)). Qed.
Lemma lem7188353 {A : Type'} (f : A -> real) (t : A -> Prop) (_96243 : A) (_96242 : A -> Prop) (_96241 : A -> Prop) (s : type686 A) : (term575 A t s _96241 _96242 f _96243) = (term593 A f t _96243 _96242 _96241 s).
Proof. exact (TRANS (@lem7188278 A t f _96243 _96242 _96241 s) (@lem7188352 A f t _96243 _96242 _96241 s)). Qed.
Lemma lem7188354 {A : Type'} (f : A -> real) (t : A -> Prop) (_96243 : A) (_96242 : A -> Prop) (_96241 : A -> Prop) (s : type686 A) : (term542 A s t _96241 _96242 f _96243) = (term593 A f t _96243 _96242 _96241 s).
Proof. exact (TRANS (@lem7188130 A t s _96241 _96242 f _96243) (@lem7188353 A f t _96243 _96242 _96241 s)). Qed.
Lemma lem7188355 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7188356 {A : Type'} (f : A -> real) (t : A -> Prop) (_96243 : A) (_96242 : A -> Prop) (_96241 : A -> Prop) (s : type686 A) : (term594 A s t _96241 _96242 f _96243) = (term595 A f t _96243 _96242 _96241 s).
Proof. exact (MK_COMB (@lem7188355) (@lem7188354 A f t _96243 _96242 _96241 s)). Qed.
Lemma lem7188372 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7188373 {A : Type'} (t : A -> Prop) (s : type686 A) (_96241 : A -> Prop) (_96243 : A) (_96242 : A -> Prop) : (term348 A s t _96241 _96243 _96242) = (term596 A t s _96241 _96243 _96242).
Proof. exact (@lem7188372 (term304 A _96242 t) (term217 A _96241 s) (term302 A _96241 _96243 _96242)). Qed.
Lemma lem7188389 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7188390 {A : Type'} (s : type686 A) (_96241 : A -> Prop) (_96243 : A) (_96242 : A -> Prop) : (term597 A s _96241 _96243 _96242) = (term598 A s _96241 _96243 _96242).
Proof. exact (@lem7188389 (_96241 = _96242) (term217 A _96241 s) (term299 A _96241 _96243 _96242)). Qed.
Lemma lem7188406 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7188407 {A : Type'} (_96241 : A -> Prop) (s : type686 A) (_96243 : A) (_96242 : A -> Prop) : (term599 A s _96241 _96243 _96242) = (term600 A _96241 s _96243 _96242).
Proof. exact (@lem7188406 (term369 A _96243 _96241) (term217 A _96241 s) (term369 A _96243 _96242)). Qed.
Lemma lem7188421 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7188422 {A : Type'} (_96243 : A) (_96242 : A -> Prop) (_96241 : A -> Prop) (s : type686 A) : (term601 A _96241 s _96243 _96242) = (term586 A _96243 _96242 _96241 s).
Proof. exact (@lem7188421 (term369 A _96243 _96242) (term217 A _96241 s)). Qed.
Lemma lem7188428 {A : Type'} (_96243 : A) (_96241 : A -> Prop) : (term387 A _96243 _96241) = (term387 A _96243 _96241).
Proof. exact (eq_refl (term387 A _96243 _96241)). Qed.
Lemma lem7188429 {A : Type'} (_96243 : A) (_96242 : A -> Prop) (_96241 : A -> Prop) (s : type686 A) : (term600 A _96241 s _96243 _96242) = (term592 A _96243 _96242 _96241 s).
Proof. exact (MK_COMB (@lem7188428 A _96243 _96241) (@lem7188422 A _96243 _96242 _96241 s)). Qed.
Lemma lem7188440 {A : Type'} (_96243 : A) (_96242 : A -> Prop) (_96241 : A -> Prop) (s : type686 A) : (term599 A s _96241 _96243 _96242) = (term592 A _96243 _96242 _96241 s).
Proof. exact (TRANS (@lem7188407 A _96241 s _96243 _96242) (@lem7188429 A _96243 _96242 _96241 s)). Qed.
Lemma lem7188441 {A : Type'} (_96241 : A -> Prop) (_96242 : A -> Prop) : (term188 A _96241 _96242) = (term188 A _96241 _96242).
Proof. exact (eq_refl (term188 A _96241 _96242)). Qed.
Lemma lem7188442 {A : Type'} (_96243 : A) (_96242 : A -> Prop) (_96241 : A -> Prop) (s : type686 A) : (term598 A s _96241 _96243 _96242) = (term602 A _96243 _96242 _96241 s).
Proof. exact (MK_COMB (@lem7188441 A _96241 _96242) (@lem7188440 A _96243 _96242 _96241 s)). Qed.
Lemma lem7188453 {A : Type'} (_96243 : A) (_96242 : A -> Prop) (_96241 : A -> Prop) (s : type686 A) : (term597 A s _96241 _96243 _96242) = (term602 A _96243 _96242 _96241 s).
Proof. exact (TRANS (@lem7188390 A s _96241 _96243 _96242) (@lem7188442 A _96243 _96242 _96241 s)). Qed.
Lemma lem7188454 {A : Type'} (_96242 : A -> Prop) (t : A -> Prop) : (term540 A _96242 t) = (term540 A _96242 t).
Proof. exact (eq_refl (term540 A _96242 t)). Qed.
Lemma lem7188455 {A : Type'} (t : A -> Prop) (_96243 : A) (_96242 : A -> Prop) (_96241 : A -> Prop) (s : type686 A) : (term596 A t s _96241 _96243 _96242) = (term603 A t _96243 _96242 _96241 s).
Proof. exact (MK_COMB (@lem7188454 A _96242 t) (@lem7188453 A _96243 _96242 _96241 s)). Qed.
Lemma lem7188459 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7188460 {A : Type'} (t : A -> Prop) (_96243 : A) (_96242 : A -> Prop) (_96241 : A -> Prop) (s : type686 A) : (term603 A t _96243 _96242 _96241 s) = (term604 A t _96243 _96242 _96241 s).
Proof. exact (@lem7188459 (_96241 = _96242) (term304 A _96242 t) (term592 A _96243 _96242 _96241 s)). Qed.
Lemma lem7188500 {A : Type'} (t : A -> Prop) (_96243 : A) (_96242 : A -> Prop) (_96241 : A -> Prop) (s : type686 A) : (term596 A t s _96241 _96243 _96242) = (term604 A t _96243 _96242 _96241 s).
Proof. exact (TRANS (@lem7188455 A t _96243 _96242 _96241 s) (@lem7188460 A t _96243 _96242 _96241 s)). Qed.
Lemma lem7188501 {A : Type'} (t : A -> Prop) (_96243 : A) (_96242 : A -> Prop) (_96241 : A -> Prop) (s : type686 A) : (term348 A s t _96241 _96243 _96242) = (term604 A t _96243 _96242 _96241 s).
Proof. exact (TRANS (@lem7188373 A t s _96241 _96243 _96242) (@lem7188500 A t _96243 _96242 _96241 s)). Qed.
Lemma lem7188502 {A : Type'} (f : A -> real) (_96243 : A) : (term404 A f _96243) = (term404 A f _96243).
Proof. exact (eq_refl (term404 A f _96243)). Qed.
Lemma lem7188503 {A : Type'} (f : A -> real) (t : A -> Prop) (_96243 : A) (_96242 : A -> Prop) (_96241 : A -> Prop) (s : type686 A) : (term605 A f s t _96241 _96243 _96242) = (term606 A f t _96243 _96242 _96241 s).
Proof. exact (MK_COMB (@lem7188502 A f _96243) (@lem7188501 A t _96243 _96242 _96241 s)). Qed.
Lemma lem7188507 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7188508 {A : Type'} (f : A -> real) (t : A -> Prop) (_96243 : A) (_96242 : A -> Prop) (_96241 : A -> Prop) (s : type686 A) : (term606 A f t _96243 _96242 _96241 s) = (term593 A f t _96243 _96242 _96241 s).
Proof. exact (@lem7188507 (_96241 = _96242) ((f _96243) = term34) (term607 A t _96243 _96242 _96241 s)). Qed.
Lemma lem7188560 {A : Type'} (f : A -> real) (t : A -> Prop) (_96243 : A) (_96242 : A -> Prop) (_96241 : A -> Prop) (s : type686 A) : (term605 A f s t _96241 _96243 _96242) = (term593 A f t _96243 _96242 _96241 s).
Proof. exact (TRANS (@lem7188503 A f t _96243 _96242 _96241 s) (@lem7188508 A f t _96243 _96242 _96241 s)). Qed.
Lemma lem7188561 {A : Type'} (f : A -> real) (t : A -> Prop) (_96243 : A) (_96242 : A -> Prop) (_96241 : A -> Prop) (s : type686 A) : ((term542 A s t _96241 _96242 f _96243) = (term605 A f s t _96241 _96243 _96242)) = ((term593 A f t _96243 _96242 _96241 s) = (term593 A f t _96243 _96242 _96241 s)).
Proof. exact (MK_COMB (@lem7188356 A f t _96243 _96242 _96241 s) (@lem7188560 A f t _96243 _96242 _96241 s)). Qed.
Lemma lem7188563 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7188564 (x : Prop) : (x = x) = True.
Proof. exact (@lem7188563 Prop x). Qed.
Lemma lem7188565 {A : Type'} (f : A -> real) (t : A -> Prop) (_96243 : A) (_96242 : A -> Prop) (_96241 : A -> Prop) (s : type686 A) : ((term593 A f t _96243 _96242 _96241 s) = (term593 A f t _96243 _96242 _96241 s)) = True.
Proof. exact (@lem7188564 (term593 A f t _96243 _96242 _96241 s)). Qed.
Lemma lem7188566 {A : Type'} (f : A -> real) (s : type686 A) (t : A -> Prop) (_96241 : A -> Prop) (_96243 : A) (_96242 : A -> Prop) : ((term542 A s t _96241 _96242 f _96243) = (term605 A f s t _96241 _96243 _96242)) = True.
Proof. exact (TRANS (@lem7188561 A f t _96243 _96242 _96241 s) (@lem7188565 A f t _96243 _96242 _96241 s)). Qed.
Lemma lem7188567 {A : Type'} (f : A -> real) (s : type686 A) (t : A -> Prop) (_96241 : A -> Prop) (_96243 : A) (_96242 : A -> Prop) : True = ((term542 A s t _96241 _96242 f _96243) = (term605 A f s t _96241 _96243 _96242)).
Proof. exact (SYM (@lem7188566 A f s t _96241 _96243 _96242)). Qed.
Lemma lem7188568 {A : Type'} (f : A -> real) (s : type686 A) (t : A -> Prop) (_96241 : A -> Prop) (_96243 : A) (_96242 : A -> Prop) : (term542 A s t _96241 _96242 f _96243) = (term605 A f s t _96241 _96243 _96242).
Proof. exact (EQ_MP (@lem7188567 A f s t _96241 _96243 _96242) (@lem0)). Qed.
Lemma lem7188569 {A : Type'} (_96241 : A -> Prop) (_96243 : A) (_96242 : A -> Prop) (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term133 A t s f) : term605 A f s t _96241 _96243 _96242.
Proof. exact (EQ_MP (@lem7188568 A f s t _96241 _96243 _96242) (@lem7187920 A _96241 _96242 _96243 t s f h1)). Qed.
Lemma lem7188571 (b : Prop) (a : Prop) : (a \/ b) = (term411 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7188572 {A : Type'} (s : type686 A) (t : A -> Prop) (_96241 : A -> Prop) (_96242 : A -> Prop) (f : A -> real) (_96243 : A) : (term605 A f s t _96241 _96243 _96242) = (term608 A s t _96241 _96242 f _96243).
Proof. exact (@lem7188571 (term348 A s t _96241 _96243 _96242) ((f _96243) = term34)). Qed.
Lemma lem7188574 (a : Prop) (b : Prop) : (term413 a b) = (term414 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7188575 {A : Type'} (s : type686 A) (t : A -> Prop) (_96241 : A -> Prop) (_96243 : A) (_96242 : A -> Prop) : (term609 A s t _96241 _96243 _96242) = (term610 A s t _96241 _96243 _96242).
Proof. exact (@lem7188574 (term217 A _96241 s) (term329 A t _96241 _96243 _96242)). Qed.
Lemma lem7188577 (a : Prop) : (term269 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7188578 {A : Type'} (_96241 : A -> Prop) (s : type686 A) : (term417 A _96241 s) = (@IN (A -> Prop) _96241 s).
Proof. exact (@lem7188577 (@IN (A -> Prop) _96241 s)). Qed.
Lemma lem7188579 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7188580 {A : Type'} (_96241 : A -> Prop) (s : type686 A) : (term418 A _96241 s) = (term419 A _96241 s).
Proof. exact (MK_COMB (@lem7188579) (@lem7188578 A _96241 s)). Qed.
Lemma lem7188582 (a : Prop) (b : Prop) : (term413 a b) = (term414 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7188583 {A : Type'} (t : A -> Prop) (_96241 : A -> Prop) (_96243 : A) (_96242 : A -> Prop) : (term611 A t _96241 _96243 _96242) = (term612 A t _96241 _96243 _96242).
Proof. exact (@lem7188582 (term304 A _96242 t) (term302 A _96241 _96243 _96242)). Qed.
Lemma lem7188585 (a : Prop) : (term269 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7188586 {A : Type'} (_96242 : A -> Prop) (t : A -> Prop) : (term297 A _96242 t) = (_96242 = t).
Proof. exact (@lem7188585 (_96242 = t)). Qed.
Lemma lem7188587 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7188588 {A : Type'} (_96242 : A -> Prop) (t : A -> Prop) : (term613 A _96242 t) = (term614 A _96242 t).
Proof. exact (MK_COMB (@lem7188587) (@lem7188586 A _96242 t)). Qed.
Lemma lem7188590 (a : Prop) (b : Prop) : (term413 a b) = (term414 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7188591 {A : Type'} (_96241 : A -> Prop) (_96243 : A) (_96242 : A -> Prop) : (term615 A _96241 _96243 _96242) = (term616 A _96241 _96243 _96242).
Proof. exact (@lem7188590 (_96241 = _96242) (term299 A _96241 _96243 _96242)). Qed.
Lemma lem7188593 (a : Prop) (b : Prop) : (term413 a b) = (term414 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7188594 {A : Type'} (_96241 : A -> Prop) (_96243 : A) (_96242 : A -> Prop) : (term617 A _96241 _96243 _96242) = (term618 A _96241 _96243 _96242).
Proof. exact (@lem7188593 (term369 A _96243 _96241) (term369 A _96243 _96242)). Qed.
Lemma lem7188596 (a : Prop) : (term269 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7188597 {A : Type'} (_96243 : A) (_96241 : A -> Prop) : (term424 A _96243 _96241) = (@IN A _96243 _96241).
Proof. exact (@lem7188596 (@IN A _96243 _96241)). Qed.
Lemma lem7188598 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7188599 {A : Type'} (_96243 : A) (_96241 : A -> Prop) : (term425 A _96243 _96241) = (term426 A _96243 _96241).
Proof. exact (MK_COMB (@lem7188598) (@lem7188597 A _96243 _96241)). Qed.
Lemma lem7188601 (a : Prop) : (term269 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7188602 {A : Type'} (_96243 : A) (_96242 : A -> Prop) : (term424 A _96243 _96242) = (@IN A _96243 _96242).
Proof. exact (@lem7188601 (@IN A _96243 _96242)). Qed.
Lemma lem7188603 {A : Type'} (_96241 : A -> Prop) (_96243 : A) (_96242 : A -> Prop) : (term618 A _96241 _96243 _96242) = (term305 A _96241 _96243 _96242).
Proof. exact (MK_COMB (@lem7188599 A _96243 _96241) (@lem7188602 A _96243 _96242)). Qed.
Lemma lem7188604 {A : Type'} (_96241 : A -> Prop) (_96243 : A) (_96242 : A -> Prop) : (term617 A _96241 _96243 _96242) = (term305 A _96241 _96243 _96242).
Proof. exact (TRANS (@lem7188594 A _96241 _96243 _96242) (@lem7188603 A _96241 _96243 _96242)). Qed.
Lemma lem7188605 {A : Type'} (_96241 : A -> Prop) (_96242 : A -> Prop) : (term619 A _96241 _96242) = (term619 A _96241 _96242).
Proof. exact (eq_refl (term619 A _96241 _96242)). Qed.
Lemma lem7188606 {A : Type'} (_96241 : A -> Prop) (_96243 : A) (_96242 : A -> Prop) : (term616 A _96241 _96243 _96242) = (term113 A _96241 _96243 _96242).
Proof. exact (MK_COMB (@lem7188605 A _96241 _96242) (@lem7188604 A _96241 _96243 _96242)). Qed.
Lemma lem7188607 {A : Type'} (_96241 : A -> Prop) (_96243 : A) (_96242 : A -> Prop) : (term615 A _96241 _96243 _96242) = (term113 A _96241 _96243 _96242).
Proof. exact (TRANS (@lem7188591 A _96241 _96243 _96242) (@lem7188606 A _96241 _96243 _96242)). Qed.
Lemma lem7188608 {A : Type'} (t : A -> Prop) (_96241 : A -> Prop) (_96243 : A) (_96242 : A -> Prop) : (term612 A t _96241 _96243 _96242) = (term620 A t _96241 _96243 _96242).
Proof. exact (MK_COMB (@lem7188588 A _96242 t) (@lem7188607 A _96241 _96243 _96242)). Qed.
Lemma lem7188609 {A : Type'} (t : A -> Prop) (_96241 : A -> Prop) (_96243 : A) (_96242 : A -> Prop) : (term611 A t _96241 _96243 _96242) = (term620 A t _96241 _96243 _96242).
Proof. exact (TRANS (@lem7188583 A t _96241 _96243 _96242) (@lem7188608 A t _96241 _96243 _96242)). Qed.
Lemma lem7188610 {A : Type'} (s : type686 A) (t : A -> Prop) (_96241 : A -> Prop) (_96243 : A) (_96242 : A -> Prop) : (term610 A s t _96241 _96243 _96242) = (term621 A s t _96241 _96243 _96242).
Proof. exact (MK_COMB (@lem7188580 A _96241 s) (@lem7188609 A t _96241 _96243 _96242)). Qed.
Lemma lem7188611 {A : Type'} (s : type686 A) (t : A -> Prop) (_96241 : A -> Prop) (_96243 : A) (_96242 : A -> Prop) : (term609 A s t _96241 _96243 _96242) = (term621 A s t _96241 _96243 _96242).
Proof. exact (TRANS (@lem7188575 A s t _96241 _96243 _96242) (@lem7188610 A s t _96241 _96243 _96242)). Qed.
Lemma lem7188612 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7188613 {A : Type'} (s : type686 A) (t : A -> Prop) (_96241 : A -> Prop) (_96243 : A) (_96242 : A -> Prop) : (term622 A s t _96241 _96243 _96242) = (term623 A s t _96241 _96243 _96242).
Proof. exact (MK_COMB (@lem7188612) (@lem7188611 A s t _96241 _96243 _96242)). Qed.
Lemma lem7188614 {A : Type'} (f : A -> real) (_96243 : A) : ((f _96243) = term34) = ((f _96243) = term34).
Proof. exact (eq_refl ((f _96243) = term34)). Qed.
Lemma lem7188615 {A : Type'} (s : type686 A) (t : A -> Prop) (_96241 : A -> Prop) (_96242 : A -> Prop) (f : A -> real) (_96243 : A) : (term608 A s t _96241 _96242 f _96243) = (term624 A s t _96241 _96242 f _96243).
Proof. exact (MK_COMB (@lem7188613 A s t _96241 _96243 _96242) (@lem7188614 A f _96243)). Qed.
Lemma lem7188616 {A : Type'} (s : type686 A) (t : A -> Prop) (_96241 : A -> Prop) (_96242 : A -> Prop) (f : A -> real) (_96243 : A) : (term605 A f s t _96241 _96243 _96242) = (term624 A s t _96241 _96242 f _96243).
Proof. exact (TRANS (@lem7188572 A s t _96241 _96242 f _96243) (@lem7188615 A s t _96241 _96242 f _96243)). Qed.
Lemma lem7188618 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term532 A t s x t') : term305 A t' x t.
Proof. exact (conj (@lem7188116 A t s x t' h1) (@lem7188123 A t s x t' h1)). Qed.
Lemma lem7188619 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term217 A t s) (h2 : term532 A t s x t') : term113 A t' x t.
Proof. exact (conj (@lem7188109 A t s x t' h1 h2) (@lem7188618 A t s x t' h2)). Qed.
Lemma lem7188620 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term217 A t s) (h2 : term532 A t s x t') : term625 A t' x t.
Proof. exact (conj (@lem7188044 A t) (@lem7188619 A t s x t' h1 h2)). Qed.
Lemma lem7188621 {A : Type'} (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term217 A t s) (h2 : term532 A t s x t') : term626 A s t' x t.
Proof. exact (conj (@lem7188035 A t s x t' h2) (@lem7188620 A t s x t' h1 h2)). Qed.
Lemma lem7188623 {A : Type'} (_96241 : A -> Prop) (_96242 : A -> Prop) (_96243 : A) (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term133 A t s f) : term624 A s t _96241 _96242 f _96243.
Proof. exact (EQ_MP (@lem7188616 A s t _96241 _96242 f _96243) (@lem7188569 A _96241 _96243 _96242 t s f h1)). Qed.
Lemma lem7188624 {A : Type'} (_96241 : A -> Prop) (_96242 : A -> Prop) (_96243 : A) (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term133 A t s f) : term624 A s t _96241 _96242 f _96243.
Proof. exact (@lem7188623 A _96241 _96242 _96243 t s f h1). Qed.
Lemma lem7188625 {A : Type'} (t' : A -> Prop) (x : A) (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term133 A t s f) : term627 A s t' t f x.
Proof. exact (@lem7188624 A t' t x t s f h1). Qed.
Lemma lem7188628 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term133 A t s f) (h2 : term217 A t s) (h3 : term532 A t s x t') : (f x) = term34.
Proof. exact (@lem7188625 A t' x t s f h1 (@lem7188621 A t s x t' h2 h3)). Qed.
Lemma lem7188629 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term133 A t s f) (h2 : term217 A t s) (h3 : term532 A t s x t') : term628 A f x.
Proof. exact (fun h0 : term294 A f x => @lem7188628 A f t s x t' h1 h2 h3). Qed.
Lemma lem7188631 (p : Prop) : (term375 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7188632 {A : Type'} (f : A -> real) (x : A) : (term628 A f x) = ((f x) = term34).
Proof. exact (@lem7188631 ((f x) = term34)). Qed.
Lemma lem7188633 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term133 A t s f) (h2 : term217 A t s) (h3 : term532 A t s x t') : (f x) = term34.
Proof. exact (EQ_MP (@lem7188632 A f x) (@lem7188629 A f t s x t' h1 h2 h3)). Qed.
Lemma lem7188636 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7188638 {A : Type'} (f : A -> real) (x : A) : (term294 A f x) = (term629 A f x).
Proof. exact (@lem7188636 ((f x) = term34)). Qed.
Lemma lem7188641 {A : Type'} (f : A -> real) (x : A) (h1 : term294 A f x) : term629 A f x.
Proof. exact (EQ_MP (@lem7188638 A f x) (@lem7187794 A f x h1)). Qed.
Lemma lem7188644 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term133 A t s f) (h2 : term294 A f x) (h3 : term217 A t s) (h4 : term532 A t s x t') : False.
Proof. exact (@lem7188641 A f x h2 (@lem7188633 A f t s x t' h1 h3 h4)). Qed.
Lemma lem7188645 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term133 A t s f) (h2 : term294 A f x) (h3 : term217 A t s) (h4 : term532 A t s x t') : term438.
Proof. exact (fun h0 : ~ False => @lem7188644 A f t s x t' h1 h2 h3 h4). Qed.
Lemma lem7188647 (p : Prop) : (term375 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7188648 : term438 = False.
Proof. exact (@lem7188647 False). Qed.
Lemma lem7188649 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term133 A t s f) (h2 : term294 A f x) (h3 : term217 A t s) (h4 : term532 A t s x t') : False.
Proof. exact (EQ_MP (@lem7188648) (@lem7188645 A f t s x t' h1 h2 h3 h4)). Qed.
Lemma lem7188650 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term133 A t s f) (h2 : term294 A f x) (h3 : term217 A t s) (h4 : term532 A t s x t') : (term294 A f x) = False.
Proof. exact (prop_ext (fun h5 : term294 A f x => @lem7188649 A f t s x t' h1 h2 h3 h4) (fun h5 : False => @lem7187794 A f x h2)). Qed.
Lemma lem7188651 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term133 A t s f) (h2 : term294 A f x) (h3 : term217 A t s) (h4 : term532 A t s x t') : False.
Proof. exact (EQ_MP (@lem7188650 A f t s x t' h1 h2 h3 h4) (@lem7187794 A f x h2)). Qed.
Lemma lem7188652 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term133 A t s f) (h2 : term294 A f x) (h3 : term217 A t s) (h4 : term532 A t s x t') : (term217 A t s) = False.
Proof. exact (prop_ext (fun h5 : term217 A t s => @lem7188651 A f t s x t' h1 h2 h3 h4) (fun h5 : False => @lem7187790 A t s h3)). Qed.
Lemma lem7188653 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term133 A t s f) (h2 : term294 A f x) (h3 : term217 A t s) (h4 : term532 A t s x t') : False.
Proof. exact (EQ_MP (@lem7188652 A f t s x t' h1 h2 h3 h4) (@lem7187790 A t s h3)). Qed.
Lemma lem7188654 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term133 A t s f) (h2 : term294 A f x) (h3 : term217 A t s) (h4 : term532 A t s x t') : (term294 A f x) = False.
Proof. exact (prop_ext (fun h5 : term294 A f x => @lem7188653 A f t s x t' h1 h2 h3 h4) (fun h5 : False => @lem7187756 A f x h2)). Qed.
Lemma lem7188655 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term133 A t s f) (h2 : term294 A f x) (h3 : term217 A t s) (h4 : term532 A t s x t') : False.
Proof. exact (EQ_MP (@lem7188654 A f t s x t' h1 h2 h3 h4) (@lem7187756 A f x h2)). Qed.
Lemma lem7188656 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term133 A t s f) (h2 : term294 A f x) (h3 : term217 A t s) (h4 : term532 A t s x t') : (term217 A t s) = False.
Proof. exact (prop_ext (fun h5 : term217 A t s => @lem7188655 A f t s x t' h1 h2 h3 h4) (fun h5 : False => @lem7187748 A t s h3)). Qed.
Lemma lem7188657 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term133 A t s f) (h2 : term294 A f x) (h3 : term217 A t s) (h4 : term532 A t s x t') : False.
Proof. exact (EQ_MP (@lem7188656 A f t s x t' h1 h2 h3 h4) (@lem7187748 A t s h3)). Qed.
Lemma lem7188658 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term133 A t s f) (h2 : term294 A f x) (h3 : term217 A t s) (h4 : term532 A t s x t') : (term294 A f x) = False.
Proof. exact (prop_ext (fun h5 : term294 A f x => @lem7188657 A f t s x t' h1 h2 h3 h4) (fun h5 : False => @lem7187756 A f x h2)). Qed.
Lemma lem7188659 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term133 A t s f) (h2 : term294 A f x) (h3 : term217 A t s) (h4 : term532 A t s x t') : False.
Proof. exact (EQ_MP (@lem7188658 A f t s x t' h1 h2 h3 h4) (@lem7187756 A f x h2)). Qed.
Lemma lem7188660 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term133 A t s f) (h2 : term294 A f x) (h3 : term217 A t s) (h4 : term532 A t s x t') : (term217 A t s) = False.
Proof. exact (prop_ext (fun h5 : term217 A t s => @lem7188659 A f t s x t' h1 h2 h3 h4) (fun h5 : False => @lem7187748 A t s h3)). Qed.
Lemma lem7188661 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term133 A t s f) (h2 : term294 A f x) (h3 : term217 A t s) (h4 : term532 A t s x t') : False.
Proof. exact (EQ_MP (@lem7188660 A f t s x t' h1 h2 h3 h4) (@lem7187748 A t s h3)). Qed.
Lemma lem7188662 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term133 A t s f) (h2 : term294 A f x) (h3 : term217 A t s) (h4 : term532 A t s x t') : (term532 A t s x t') = False.
Proof. exact (prop_ext (fun h5 : term532 A t s x t' => @lem7188661 A f t s x t' h1 h2 h3 h4) (fun h5 : False => @lem7187624 A t s x t' h4)). Qed.
Lemma lem7188663 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term133 A t s f) (h2 : term294 A f x) (h3 : term217 A t s) (h4 : term532 A t s x t') : False.
Proof. exact (EQ_MP (@lem7188662 A f t s x t' h1 h2 h3 h4) (@lem7187624 A t s x t' h4)). Qed.
Lemma lem7188664 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term133 A t s f) (h2 : term294 A f x) (h3 : term217 A t s) (h4 : term532 A t s x t') : (term294 A f x) = False.
Proof. exact (prop_ext (fun h5 : term294 A f x => @lem7188663 A f t s x t' h1 h2 h3 h4) (fun h5 : False => @lem7187602 A f x h2)). Qed.
Lemma lem7188665 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term133 A t s f) (h2 : term294 A f x) (h3 : term217 A t s) (h4 : term532 A t s x t') : False.
Proof. exact (EQ_MP (@lem7188664 A f t s x t' h1 h2 h3 h4) (@lem7187602 A f x h2)). Qed.
Lemma lem7188666 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term133 A t s f) (h2 : term294 A f x) (h3 : term217 A t s) (h4 : term532 A t s x t') : (term217 A t s) = False.
Proof. exact (prop_ext (fun h5 : term217 A t s => @lem7188665 A f t s x t' h1 h2 h3 h4) (fun h5 : False => @lem7187584 A t s h3)). Qed.
Lemma lem7188667 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (x : A) (t' : A -> Prop) (h1 : term133 A t s f) (h2 : term294 A f x) (h3 : term217 A t s) (h4 : term532 A t s x t') : False.
Proof. exact (EQ_MP (@lem7188666 A f t s x t' h1 h2 h3 h4) (@lem7187584 A t s h3)). Qed.
Lemma lem7188668 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (x : A) (h1 : term133 A t s f) (h2 : term294 A f x) (h3 : term217 A t s) (h4 : term476 A t s x) : False.
Proof. exact (ex_elim (@lem7187453 A t s x h4) (fun t' : A -> Prop => fun h0 : term534 A t s x t' => @lem7188667 A f t s x t' h1 h2 h3 h0)). Qed.
Lemma lem7188669 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (x : A) (h1 : term133 A t s f) (h2 : term294 A f x) (h3 : term217 A t s) (h4 : term476 A t s x) : (term294 A f x) = False.
Proof. exact (prop_ext (fun h5 : term294 A f x => @lem7188668 A f t s x h1 h2 h3 h4) (fun h5 : False => @lem7187459 A f x h2)). Qed.
Lemma lem7188670 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (x : A) (h1 : term133 A t s f) (h2 : term294 A f x) (h3 : term217 A t s) (h4 : term476 A t s x) : False.
Proof. exact (EQ_MP (@lem7188669 A f t s x h1 h2 h3 h4) (@lem7187459 A f x h2)). Qed.
Lemma lem7188671 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (x : A) (h1 : term133 A t s f) (h2 : term294 A f x) (h3 : term217 A t s) (h4 : term476 A t s x) : (term217 A t s) = False.
Proof. exact (prop_ext (fun h5 : term217 A t s => @lem7188670 A f t s x h1 h2 h3 h4) (fun h5 : False => @lem7187363 A t s h3)). Qed.
Lemma lem7188672 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (x : A) (h1 : term133 A t s f) (h2 : term294 A f x) (h3 : term217 A t s) (h4 : term476 A t s x) : False.
Proof. exact (EQ_MP (@lem7188671 A f t s x h1 h2 h3 h4) (@lem7187363 A t s h3)). Qed.
Lemma lem7188673 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (x : A) (h1 : term133 A t s f) (h2 : term294 A f x) (h3 : term217 A t s) (h4 : term476 A t s x) : (term294 A f x) = False.
Proof. exact (prop_ext (fun h5 : term294 A f x => @lem7188672 A f t s x h1 h2 h3 h4) (fun h5 : False => @lem7187189 A f x h2)). Qed.
Lemma lem7188674 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (x : A) (h1 : term133 A t s f) (h2 : term294 A f x) (h3 : term217 A t s) (h4 : term476 A t s x) : False.
Proof. exact (EQ_MP (@lem7188673 A f t s x h1 h2 h3 h4) (@lem7187189 A f x h2)). Qed.
Lemma lem7188675 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (x : A) (h1 : term133 A t s f) (h2 : term217 A t s) (h3 : term476 A t s x) : term293 A f x.
Proof. exact (fun h0 : term294 A f x => @lem7188674 A f t s x h1 h0 h2 h3). Qed.
Lemma lem7188676 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (x : A) (h1 : term133 A t s f) (h2 : term217 A t s) (h3 : term476 A t s x) : (f x) = term34.
Proof. exact (EQ_MP (@lem7187188 A f x) (@lem7188675 A f t s x h1 h2 h3)). Qed.
Lemma lem7188677 {A : Type'} (x : A) (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term133 A t s f) (h2 : term217 A t s) : term482 A t s f x.
Proof. exact (fun h0 : term476 A t s x => @lem7188676 A f t s x h1 h2 h0). Qed.
Lemma lem7188682 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term133 A t s f) (h2 : term217 A t s) : term486 A t s f.
Proof. exact (fun x : A => @lem7188677 A x f t s h1 h2). Qed.
Lemma lem7188683 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term133 A t s f) (h2 : term217 A t s) : term498 A t s f.
Proof. exact (fun h0 : @FINITE (A -> Prop) s => @lem7188682 A f t s h1 h2). Qed.
Lemma lem7188684 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term133 A t s f) : term501 A t s f.
Proof. exact (fun h0 : term217 A t s => @lem7188683 A f t s h1 h0). Qed.
Lemma lem7188685 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : term503 A t s f.
Proof. exact (fun h0 : term133 A t s f => @lem7188684 A t s f h0). Qed.
Lemma lem7188686 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : term504 A t s f.
Proof. exact (fun h0 : term108 A t s => @lem7188685 A t s f). Qed.
Lemma lem7188691 {A : Type'} (s : type686 A) (f : A -> real) : term508 A s f.
Proof. exact (fun t : A -> Prop => @lem7188686 A t s f). Qed.
Lemma lem7188696 {A : Type'} (f : A -> real) : term512 A f.
Proof. exact (fun s : type686 A => @lem7188691 A s f). Qed.
Lemma lem7188701 {A : Type'} : term516 A.
Proof. exact (fun f : A -> real => @lem7188696 A f). Qed.
Lemma lem7188702 {A : Type'} : term515 A.
Proof. exact (EQ_MP (@lem7187179 A) (@lem7188701 A)). Qed.
Lemma lem7188703 {A : Type'} (f : A -> real) : term630 A f.
Proof. exact (@lem7188702 A f). Qed.
Lemma lem7188704 {A : Type'} (f : A -> real) : (term630 A f) = (term511 A f).
Proof. exact (eq_refl (term630 A f)). Qed.
Lemma lem7188705 {A : Type'} (f : A -> real) : term511 A f.
Proof. exact (EQ_MP (@lem7188704 A f) (@lem7188703 A f)). Qed.
Lemma lem7188706 {A : Type'} (f : A -> real) (s : type686 A) : term631 A f s.
Proof. exact (@lem7188705 A f s). Qed.
Lemma lem7188707 {A : Type'} (s : type686 A) (f : A -> real) : (term631 A f s) = (term507 A s f).
Proof. exact (eq_refl (term631 A f s)). Qed.
Lemma lem7188708 {A : Type'} (s : type686 A) (f : A -> real) : term507 A s f.
Proof. exact (EQ_MP (@lem7188707 A s f) (@lem7188706 A f s)). Qed.
Lemma lem7188709 {A : Type'} (s : type686 A) (f : A -> real) (t : A -> Prop) : term632 A s f t.
Proof. exact (@lem7188708 A s f t). Qed.
Lemma lem7188710 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : (term632 A s f t) = (term492 A t s f).
Proof. exact (eq_refl (term632 A s f t)). Qed.
Lemma lem7188711 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : term492 A t s f.
Proof. exact (EQ_MP (@lem7188710 A t s f) (@lem7188709 A s f t)). Qed.
Lemma lem7188713 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : term492 A t s f.
Proof. exact (@lem7186833 A t s f (@lem7188711 A t s f)). Qed.
Lemma lem7188714 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term108 A t s) : term502 A t s f.
Proof. exact (@lem7188713 A t s f (@lem7185729 A t s h1)). Qed.
Lemma lem7188715 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term133 A t s f) (h2 : term108 A t s) : term500 A t s f.
Proof. exact (@lem7188714 A f t s h2 (@lem7185743 A t s f h1)). Qed.
Lemma lem7188716 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term133 A t s f) (h2 : term108 A t s) (h3 : term217 A t s) : term497 A t s f.
Proof. exact (@lem7188715 A f t s h1 h2 (@lem7185746 A t s h3)). Qed.
Lemma lem7188717 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term133 A t s f) (h2 : term108 A t s) (h3 : @FINITE (A -> Prop) s) (h4 : term217 A t s) : term490 A t s f.
Proof. exact (@lem7188716 A f t s h1 h2 h4 (@lem7185745 A s h3)). Qed.
Lemma lem7188718 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term133 A t s f) (h2 : term108 A t s) (h3 : @FINITE (A -> Prop) s) (h4 : term491 A t s f) (h5 : term217 A t s) : False.
Proof. exact (@lem7188717 A f t s h1 h2 h3 h5 (@lem7186817 A t s f h4)). Qed.
Lemma lem7188719 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term133 A t s f) (h2 : term108 A t s) (h3 : @FINITE (A -> Prop) s) (h4 : term491 A t s f) (h5 : term217 A t s) : (term491 A t s f) = False.
Proof. exact (prop_ext (fun h6 : term491 A t s f => @lem7188718 A f t s h1 h2 h3 h4 h5) (fun h6 : False => @lem7186817 A t s f h4)). Qed.
Lemma lem7188720 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term133 A t s f) (h2 : term108 A t s) (h3 : @FINITE (A -> Prop) s) (h4 : term491 A t s f) (h5 : term217 A t s) : False.
Proof. exact (EQ_MP (@lem7188719 A f t s h1 h2 h3 h4 h5) (@lem7186817 A t s f h4)). Qed.
Lemma lem7188721 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term133 A t s f) (h2 : term108 A t s) (h3 : @FINITE (A -> Prop) s) (h4 : term217 A t s) : term490 A t s f.
Proof. exact (fun h0 : term491 A t s f => @lem7188720 A f t s h1 h2 h3 h0 h4). Qed.
Lemma lem7188722 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term133 A t s f) (h2 : term108 A t s) (h3 : @FINITE (A -> Prop) s) (h4 : term217 A t s) : term486 A t s f.
Proof. exact (EQ_MP (@lem7186816 A t s f) (@lem7188721 A f t s h1 h2 h3 h4)). Qed.
Lemma lem7188723 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term133 A t s f) (h2 : term108 A t s) (h3 : @FINITE (A -> Prop) s) (h4 : term217 A t s) : term489 A t s f.
Proof. exact (EQ_MP (@lem7186812 A f t s h2 h3 h4) (@lem7188722 A f t s h1 h2 h3 h4)). Qed.
Lemma lem7188724 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term133 A t s f) (h2 : term108 A t s) (h3 : @FINITE (A -> Prop) s) (h4 : term217 A t s) : (term143 A t s f) = (term633 A t s f).
Proof. exact (@lem7185750 A t s f (@lem7188723 A f t s h1 h2 h3 h4)). Qed.
Lemma lem7188725 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term64 A t s) : @FINITE (A -> Prop) s.
Proof. exact (proj2 (@lem7185744 A t s h1)). Qed.
Lemma lem7188726 {A : Type'} (t : A -> Prop) (s : type686 A) (h1 : term64 A t s) : term217 A t s.
Proof. exact (proj1 (@lem7185744 A t s h1)). Qed.
Lemma lem7188727 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term133 A t s f) (h2 : term108 A t s) (h3 : @FINITE (A -> Prop) s) (h4 : term217 A t s) : (@FINITE (A -> Prop) s) = ((term143 A t s f) = (term633 A t s f)).
Proof. exact (prop_ext (fun h5 : @FINITE (A -> Prop) s => @lem7188724 A f t s h1 h2 h3 h4) (fun h5 : (term143 A t s f) = (term633 A t s f) => @lem7185745 A s h3)). Qed.
Lemma lem7188728 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term133 A t s f) (h2 : term108 A t s) (h3 : @FINITE (A -> Prop) s) (h4 : term217 A t s) : (term143 A t s f) = (term633 A t s f).
Proof. exact (EQ_MP (@lem7188727 A f t s h1 h2 h3 h4) (@lem7185745 A s h3)). Qed.
Lemma lem7188729 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term133 A t s f) (h2 : term108 A t s) (h3 : @FINITE (A -> Prop) s) (h4 : term217 A t s) : (term217 A t s) = ((term143 A t s f) = (term633 A t s f)).
Proof. exact (prop_ext (fun h5 : term217 A t s => @lem7188728 A f t s h1 h2 h3 h4) (fun h5 : (term143 A t s f) = (term633 A t s f) => @lem7185746 A t s h4)). Qed.
Lemma lem7188730 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term133 A t s f) (h2 : term108 A t s) (h3 : @FINITE (A -> Prop) s) (h4 : term217 A t s) : (term143 A t s f) = (term633 A t s f).
Proof. exact (EQ_MP (@lem7188729 A f t s h1 h2 h3 h4) (@lem7185746 A t s h4)). Qed.
Lemma lem7188731 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term133 A t s f) (h2 : term108 A t s) (h3 : term217 A t s) (h4 : term64 A t s) : (@FINITE (A -> Prop) s) = ((term143 A t s f) = (term633 A t s f)).
Proof. exact (prop_ext (fun h5 : @FINITE (A -> Prop) s => @lem7188730 A f t s h1 h2 h5 h3) (fun h5 : (term143 A t s f) = (term633 A t s f) => @lem7188725 A t s h4)). Qed.
Lemma lem7188732 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term133 A t s f) (h2 : term108 A t s) (h3 : term217 A t s) (h4 : term64 A t s) : (term143 A t s f) = (term633 A t s f).
Proof. exact (EQ_MP (@lem7188731 A f t s h1 h2 h3 h4) (@lem7188725 A t s h4)). Qed.
Lemma lem7188733 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term133 A t s f) (h2 : term108 A t s) (h3 : term64 A t s) : (term217 A t s) = ((term143 A t s f) = (term633 A t s f)).
Proof. exact (prop_ext (fun h4 : term217 A t s => @lem7188732 A f t s h1 h2 h4 h3) (fun h4 : (term143 A t s f) = (term633 A t s f) => @lem7188726 A t s h3)). Qed.
Lemma lem7188734 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term133 A t s f) (h2 : term108 A t s) (h3 : term64 A t s) : (term143 A t s f) = (term633 A t s f).
Proof. exact (EQ_MP (@lem7188733 A f t s h1 h2 h3) (@lem7188726 A t s h3)). Qed.
Lemma lem7188735 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term133 A t s f) (h2 : term108 A t s) : term445 A t s f.
Proof. exact (fun h0 : term64 A t s => @lem7188734 A f t s h1 h2 h0). Qed.
Lemma lem7188736 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term133 A t s f) (h2 : term108 A t s) : (term133 A t s f) = (term445 A t s f).
Proof. exact (prop_ext (fun h3 : term133 A t s f => @lem7188735 A f t s h1 h2) (fun h3 : term445 A t s f => @lem7185743 A t s f h1)). Qed.
Lemma lem7188737 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term133 A t s f) (h2 : term108 A t s) : term445 A t s f.
Proof. exact (EQ_MP (@lem7188736 A f t s h1 h2) (@lem7185743 A t s f h1)). Qed.
Lemma lem7188738 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term133 A t s f) (h2 : term108 A t s) : (term108 A t s) = (term445 A t s f).
Proof. exact (prop_ext (fun h3 : term108 A t s => @lem7188737 A f t s h1 h2) (fun h3 : term445 A t s f => @lem7185729 A t s h2)). Qed.
Lemma lem7188739 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term133 A t s f) (h2 : term108 A t s) : term445 A t s f.
Proof. exact (EQ_MP (@lem7188738 A f t s h1 h2) (@lem7185729 A t s h2)). Qed.
Lemma lem7188740 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term133 A t s f) (h2 : term108 A t s) (h3 : (term47 A s f) = (term48 A s f)) : term255 A t s f.
Proof. exact (EQ_MP (@lem7185715 A t s f h3) (@lem7188739 A f t s h1 h2)). Qed.
Lemma lem7188741 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term133 A t s f) (h2 : term108 A t s) : term634 A t s f.
Proof. exact (fun h0 : (term47 A s f) = (term48 A s f) => @lem7188740 A t s f h1 h2 h0). Qed.
Lemma lem7188742 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term133 A t s f) (h2 : term108 A t s) : term635 A t s f.
Proof. exact (conj (@lem7185700 A f t s h1 h2) (@lem7188741 A f t s h1 h2)). Qed.
Lemma lem7188743 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term133 A t s f) (h2 : term108 A t s) : term258 A t s f.
Proof. exact (@lem7183928 A t s f (@lem7188742 A f t s h1 h2)). Qed.
Lemma lem7188744 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term133 A t s f) (h2 : term108 A t s) : term155 A t s f.
Proof. exact (EQ_MP (@lem7183925 A f t s h2) (@lem7188743 A f t s h1 h2)). Qed.
Lemma lem7188745 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term133 A t s f) (h2 : term108 A t s) : term154 A t s f.
Proof. exact (EQ_MP (@lem7179337 A t s f) (@lem7188744 A f t s h1 h2)). Qed.
Lemma lem7188746 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term133 A t s f) (h2 : term108 A t s) (h3 : term66 A f t s) : (term143 A t s f) = (term146 A t s f).
Proof. exact (@lem7188745 A f t s h1 h2 (@lem7179330 A f t s h3)). Qed.
Lemma lem7188747 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term135 A t s f) : term133 A t s f.
Proof. exact (proj2 (@lem7179331 A t s f h1)). Qed.
Lemma lem7188748 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) (h1 : term135 A t s f) : term108 A t s.
Proof. exact (proj1 (@lem7179331 A t s f h1)). Qed.
Lemma lem7188749 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term133 A t s f) (h2 : term108 A t s) (h3 : term66 A f t s) : (term133 A t s f) = ((term143 A t s f) = (term146 A t s f)).
Proof. exact (prop_ext (fun h4 : term133 A t s f => @lem7188746 A f t s h1 h2 h3) (fun h4 : (term143 A t s f) = (term146 A t s f) => @lem7179332 A t s f h1)). Qed.
Lemma lem7188750 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term133 A t s f) (h2 : term108 A t s) (h3 : term66 A f t s) : (term143 A t s f) = (term146 A t s f).
Proof. exact (EQ_MP (@lem7188749 A f t s h1 h2 h3) (@lem7179332 A t s f h1)). Qed.
Lemma lem7188751 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term133 A t s f) (h2 : term108 A t s) (h3 : term66 A f t s) : (term108 A t s) = ((term143 A t s f) = (term146 A t s f)).
Proof. exact (prop_ext (fun h4 : term108 A t s => @lem7188750 A f t s h1 h2 h3) (fun h4 : (term143 A t s f) = (term146 A t s f) => @lem7179333 A t s h2)). Qed.
Lemma lem7188752 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term133 A t s f) (h2 : term108 A t s) (h3 : term66 A f t s) : (term143 A t s f) = (term146 A t s f).
Proof. exact (EQ_MP (@lem7188751 A f t s h1 h2 h3) (@lem7179333 A t s h2)). Qed.
Lemma lem7188753 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term108 A t s) (h2 : term135 A t s f) (h3 : term66 A f t s) : (term133 A t s f) = ((term143 A t s f) = (term146 A t s f)).
Proof. exact (prop_ext (fun h4 : term133 A t s f => @lem7188752 A f t s h4 h1 h3) (fun h4 : (term143 A t s f) = (term146 A t s f) => @lem7188747 A t s f h2)). Qed.
Lemma lem7188754 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term108 A t s) (h2 : term135 A t s f) (h3 : term66 A f t s) : (term143 A t s f) = (term146 A t s f).
Proof. exact (EQ_MP (@lem7188753 A f t s h1 h2 h3) (@lem7188747 A t s f h2)). Qed.
Lemma lem7188755 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term135 A t s f) (h2 : term66 A f t s) : (term108 A t s) = ((term143 A t s f) = (term146 A t s f)).
Proof. exact (prop_ext (fun h3 : term108 A t s => @lem7188754 A f t s h3 h1 h2) (fun h3 : (term143 A t s f) = (term146 A t s f) => @lem7188748 A t s f h1)). Qed.
Lemma lem7188756 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term135 A t s f) (h2 : term66 A f t s) : (term143 A t s f) = (term146 A t s f).
Proof. exact (EQ_MP (@lem7188755 A f t s h1 h2) (@lem7188748 A t s f h1)). Qed.
Lemma lem7188757 {A : Type'} (f : A -> real) (t : A -> Prop) (s : type686 A) (h1 : term66 A f t s) : term147 A t s f.
Proof. exact (fun h0 : term135 A t s f => @lem7188756 A f t s h0 h1). Qed.
Lemma lem7188758 {A : Type'} (t : A -> Prop) (s : type686 A) (f : A -> real) : term148 A t s f.
Proof. exact (fun h0 : term66 A f t s => @lem7188757 A f t s h0). Qed.
Lemma lem7188763 {A : Type'} (t : A -> Prop) (f : A -> real) : term150 A t f.
Proof. exact (fun s : type686 A => @lem7188758 A t s f). Qed.
Lemma lem7188768 {A : Type'} (f : A -> real) : term152 A f.
Proof. exact (fun t : A -> Prop => @lem7188763 A t f). Qed.
Lemma lem7188769 {A : Type'} (f : A -> real) : term82 A f.
Proof. exact (EQ_MP (@lem7179329 A f) (@lem7188768 A f)). Qed.
Lemma lem7188770 {A : Type'} (f : A -> real) : term52 A f.
Proof. exact (@lem7178943 A f (@lem7188769 A f)). Qed.
Lemma lem7188771 {A : Type'} (f : A -> real) : term51 A f.
Proof. exact (EQ_MP (@lem7178910 A f) (@lem7188770 A f)). Qed.
Lemma lem7188776 {A : Type'} : term636 A.
Proof. exact (fun f : A -> real => @lem7188771 A f). Qed.
