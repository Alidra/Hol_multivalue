Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import POLYNOMIAL_FUNCTION_MUL_term_abbrevs.
Require Import ADD1_spec.
Require Import ADD_EQ_0_spec.
Require Import ADD_SUB_spec.
Require Import ARITH_EQ_spec.
Require Import EXISTS_REFL_spec.
Require Import FUN_EQ_THM_spec.
Require Import LEFT_FORALL_IMP_THM_spec.
Require Import LEFT_IMP_EXISTS_THM_spec.
Require Import LE_0_spec.
Require Import POLYNOMIAL_FUNCTION_ADD_spec.
Require Import POLYNOMIAL_FUNCTION_RMUL_spec.
Require Import REAL_POW_1_spec.
Require Import REAL_POW_ADD_spec.
Require Import RIGHT_FORALL_IMP_THM_spec.
Require Import SUM_CLAUSES_LEFT_spec.
Require Import SUM_OFFSET_spec.
Require Import SUM_RMUL_spec.
Require Import SUM_SING_NUMSEG_spec.
Require Import polynomial_function_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm1338912_spec.
Require Import thm1339188_spec.
Require Import thm1344310_spec.
Require Import thm1344311_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm15249_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17646_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm1845_spec.
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
Require Import thm18931_spec.
Require Import thm18932_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980255_spec.
Require Import thm1980265_spec.
Require Import thm1980266_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982729_spec.
Require Import thm1982747_spec.
Require Import thm1982777_spec.
Require Import thm1982779_spec.
Require Import thm1982785_spec.
Require Import thm1982792_spec.
Require Import thm1988318_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm7261461_spec.
Require Import thm7261462_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm885_spec.
Require Import thm886_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem7567847 {A : Type'} (f : A -> real) : term0 A f.
Proof. exact (@lem7070368 A f). Qed.
Lemma lem7567848 {A : Type'} (f : A -> real) : (term0 A f) = (term1 A f).
Proof. exact (eq_refl (term0 A f)). Qed.
Lemma lem7567849 {A : Type'} (f : A -> real) : term1 A f.
Proof. exact (EQ_MP (@lem7567848 A f) (@lem7567847 A f)). Qed.
Lemma lem7567850 {A : Type'} (f : A -> real) (c : real) : term2 A f c.
Proof. exact (@lem7567849 A f c). Qed.
Lemma lem7567851 {A : Type'} (f : A -> real) (c : real) : (term2 A f c) = (term3 A f c).
Proof. exact (eq_refl (term2 A f c)). Qed.
Lemma lem7567852 {A : Type'} (f : A -> real) (c : real) : term3 A f c.
Proof. exact (EQ_MP (@lem7567851 A f c) (@lem7567850 A f c)). Qed.
Lemma lem7567853 {A : Type'} (f : A -> real) (c : real) (s : A -> Prop) : term4 A f c s.
Proof. exact (@lem7567852 A f c s). Qed.
Lemma lem7567854 {A : Type'} (s : A -> Prop) (f : A -> real) (c : real) : (term4 A f c s) = ((term5 A s f c) = (term6 A s f c)).
Proof. exact (eq_refl (term4 A f c s)). Qed.
Lemma lem7567856 (x : real) : term7 x.
Proof. exact (@lem1338912 x). Qed.
Lemma lem7567857 (x : real) : (term7 x) = (term8 x).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem7567858 (x : real) : term8 x.
Proof. exact (EQ_MP (@lem7567857 x) (@lem7567856 x)). Qed.
Lemma lem7567859 (x : real) (y : real) : term9 x y.
Proof. exact (@lem7567858 x y). Qed.
Lemma lem7567860 (x : real) (y : real) : (term9 x y) = (term10 x y).
Proof. exact (eq_refl (term9 x y)). Qed.
Lemma lem7567861 (x : real) (y : real) : term10 x y.
Proof. exact (EQ_MP (@lem7567860 x y) (@lem7567859 x y)). Qed.
Lemma lem7567862 (x : real) (y : real) (z : real) : term11 x y z.
Proof. exact (@lem7567861 x y z). Qed.
Lemma lem7567863 (x : real) (y : real) (z : real) : (term11 x y z) = ((term12 x y z) = (term13 x y z)).
Proof. exact (eq_refl (term11 x y z)). Qed.
Lemma lem7567865 (x : real) : term14 x.
Proof. exact (@lem1596102 x). Qed.
Lemma lem7567866 (x : real) : (term14 x) = (term15 x).
Proof. exact (eq_refl (term14 x)). Qed.
Lemma lem7567867 (x : real) : term15 x.
Proof. exact (EQ_MP (@lem7567866 x) (@lem7567865 x)). Qed.
Lemma lem7567868 (x : real) (m : nat) : term16 x m.
Proof. exact (@lem7567867 x m). Qed.
Lemma lem7567869 (m : nat) (x : real) : (term16 x m) = (term17 m x).
Proof. exact (eq_refl (term16 x m)). Qed.
Lemma lem7567870 (m : nat) (x : real) : term17 m x.
Proof. exact (EQ_MP (@lem7567869 m x) (@lem7567868 x m)). Qed.
Lemma lem7567871 (m : nat) (x : real) (n : nat) : term18 m x n.
Proof. exact (@lem7567870 m x n). Qed.
Lemma lem7567872 (m : nat) (x : real) (n : nat) : (term18 m x n) = ((term19 x m n) = (term20 m x n)).
Proof. exact (eq_refl (term18 m x n)). Qed.
Lemma lem7567874 : term21.
Proof. exact (@lem7223171 term22). Qed.
Lemma lem7567875 : term21 = term23.
Proof. exact (eq_refl term21). Qed.
Lemma lem7567876 : term23.
Proof. exact (EQ_MP (@lem7567875) (@lem7567874)). Qed.
Lemma lem7567877 (n : nat) : term24 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem7567878 (n : nat) : (term24 n) = (term25 n).
Proof. exact (eq_refl (term24 n)). Qed.
Lemma lem7567879 (n : nat) : term25 n.
Proof. exact (EQ_MP (@lem7567878 n) (@lem7567877 n)). Qed.
Lemma lem7567880 (n : nat) : (term25 n) = ((term25 n) = True).
Proof. exact (@lem7 (term25 n)). Qed.
Lemma lem7567882 (f : nat -> real) : term26 f.
Proof. exact (@lem7226008 f). Qed.
Lemma lem7567883 (f : nat -> real) : (term26 f) = (term27 f).
Proof. exact (eq_refl (term26 f)). Qed.
Lemma lem7567884 (f : nat -> real) : term27 f.
Proof. exact (EQ_MP (@lem7567883 f) (@lem7567882 f)). Qed.
Lemma lem7567885 (f : nat -> real) (m : nat) : term28 f m.
Proof. exact (@lem7567884 f m). Qed.
Lemma lem7567886 (m : nat) (f : nat -> real) : (term28 f m) = (term29 m f).
Proof. exact (eq_refl (term28 f m)). Qed.
Lemma lem7567887 (m : nat) (f : nat -> real) : term29 m f.
Proof. exact (EQ_MP (@lem7567886 m f) (@lem7567885 f m)). Qed.
Lemma lem7567888 (m : nat) (f : nat -> real) (n : nat) : term30 m f n.
Proof. exact (@lem7567887 m f n). Qed.
Lemma lem7567889 (m : nat) (n : nat) (f : nat -> real) : (term30 m f n) = (term31 m n f).
Proof. exact (eq_refl (term30 m f n)). Qed.
Lemma lem7567890 (m : nat) (n : nat) (f : nat -> real) : term31 m n f.
Proof. exact (EQ_MP (@lem7567889 m n f) (@lem7567888 m f n)). Qed.
Lemma lem7567891 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem7567892 (f : nat -> real) (m : nat) (n : nat) (h1 : Peano.le m n) : (term32 m n f) = (term33 m n f).
Proof. exact (@lem7567890 m n f (@lem7567891 m n h1)). Qed.
Lemma lem7567898 {A : Type'} (P : A -> Prop) : term34 A P.
Proof. exact (@lem6644 A P). Qed.
Lemma lem7567899 {A : Type'} (P : A -> Prop) : (term34 A P) = (term35 A P).
Proof. exact (eq_refl (term34 A P)). Qed.
Lemma lem7567900 {A : Type'} (P : A -> Prop) : term35 A P.
Proof. exact (EQ_MP (@lem7567899 A P) (@lem7567898 A P)). Qed.
Lemma lem7567901 {A : Type'} (P : A -> Prop) (Q : Prop) : term36 A P Q.
Proof. exact (@lem7567900 A P Q). Qed.
Lemma lem7567902 {A : Type'} (P : A -> Prop) (Q : Prop) : (term36 A P Q) = ((term37 A P Q) = (term38 A P Q)).
Proof. exact (eq_refl (term36 A P Q)). Qed.
Lemma lem7567904 (p : real -> real) : term39 p.
Proof. exact (@lem7553488 p). Qed.
Lemma lem7567905 (p : real -> real) : (term39 p) = ((polynomial_function p) = (term40 p)).
Proof. exact (eq_refl (term39 p)). Qed.
Lemma lem7567907 {A B : Type'} (f : A -> B) : term41 A B f.
Proof. exact (@lem9220 A B f). Qed.
Lemma lem7567908 {A B : Type'} (f : A -> B) : (term41 A B f) = (term42 A B f).
Proof. exact (eq_refl (term41 A B f)). Qed.
Lemma lem7567909 {A B : Type'} (f : A -> B) : term42 A B f.
Proof. exact (EQ_MP (@lem7567908 A B f) (@lem7567907 A B f)). Qed.
Lemma lem7567910 {A B : Type'} (f : A -> B) (g : A -> B) : term43 A B f g.
Proof. exact (@lem7567909 A B f g). Qed.
Lemma lem7567911 {A B : Type'} (f : A -> B) (g : A -> B) : (term43 A B f g) = ((f = g) = (term44 A B f g)).
Proof. exact (eq_refl (term43 A B f g)). Qed.
Lemma lem7567913 (p : real -> real) (m : nat) (c : nat -> real) (q : real -> real) (h1 : (term45 p m c) = q) : (term45 p m c) = q.
Proof. exact (h1). Qed.
Lemma lem7567914 (p : real -> real) (m : nat) (c : nat -> real) (q : real -> real) (h1 : (term45 p m c) = q) : term46 p m c.
Proof. exact (ex_intro (term47 p m c) q (@lem7567913 p m c q h1)). Qed.
Lemma lem7567915 (p : real -> real) (m : nat) (c : nat -> real) (h1 : term46 p m c) : term46 p m c.
Proof. exact (h1). Qed.
Lemma lem7567916 (p : real -> real) (m : nat) (c : nat -> real) (h1 : term46 p m c) : term46 p m c.
Proof. exact (ex_elim (@lem7567915 p m c h1) (fun q : real -> real => fun h0 : term47 p m c q => @lem7567914 p m c q h0)). Qed.
Lemma lem7567917 (p : real -> real) (m : nat) (c : nat -> real) : (term45 p m c) = (term45 p m c).
Proof. exact (eq_refl (term45 p m c)). Qed.
Lemma lem7567918 (p : real -> real) (m : nat) (c : nat -> real) : term46 p m c.
Proof. exact (ex_intro (term47 p m c) (term45 p m c) (@lem7567917 p m c)). Qed.
Lemma lem7567919 (p : real -> real) (m : nat) (c : nat -> real) : (term46 p m c) = (term46 p m c).
Proof. exact (prop_ext (fun h1 : term46 p m c => @lem7567916 p m c h1) (fun h1 : term46 p m c => @lem7567918 p m c)). Qed.
Lemma lem7567920 (p : real -> real) (m : nat) (c : nat -> real) : term46 p m c.
Proof. exact (EQ_MP (@lem7567919 p m c) (@lem7567918 p m c)). Qed.
Lemma lem7567921 {A : Type'} (f : A -> real) : term0 A f.
Proof. exact (@lem7070368 A f). Qed.
Lemma lem7567922 {A : Type'} (f : A -> real) : (term0 A f) = (term1 A f).
Proof. exact (eq_refl (term0 A f)). Qed.
Lemma lem7567923 {A : Type'} (f : A -> real) : term1 A f.
Proof. exact (EQ_MP (@lem7567922 A f) (@lem7567921 A f)). Qed.
Lemma lem7567924 {A : Type'} (f : A -> real) (c : real) : term2 A f c.
Proof. exact (@lem7567923 A f c). Qed.
Lemma lem7567925 {A : Type'} (f : A -> real) (c : real) : (term2 A f c) = (term3 A f c).
Proof. exact (eq_refl (term2 A f c)). Qed.
Lemma lem7567926 {A : Type'} (f : A -> real) (c : real) : term3 A f c.
Proof. exact (EQ_MP (@lem7567925 A f c) (@lem7567924 A f c)). Qed.
Lemma lem7567927 {A : Type'} (f : A -> real) (c : real) (s : A -> Prop) : term4 A f c s.
Proof. exact (@lem7567926 A f c s). Qed.
Lemma lem7567928 {A : Type'} (s : A -> Prop) (f : A -> real) (c : real) : (term4 A f c s) = ((term5 A s f c) = (term6 A s f c)).
Proof. exact (eq_refl (term4 A f c s)). Qed.
Lemma lem7567930 (x : real) : term7 x.
Proof. exact (@lem1338912 x). Qed.
Lemma lem7567931 (x : real) : (term7 x) = (term8 x).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem7567932 (x : real) : term8 x.
Proof. exact (EQ_MP (@lem7567931 x) (@lem7567930 x)). Qed.
Lemma lem7567933 (x : real) (y : real) : term9 x y.
Proof. exact (@lem7567932 x y). Qed.
Lemma lem7567934 (x : real) (y : real) : (term9 x y) = (term10 x y).
Proof. exact (eq_refl (term9 x y)). Qed.
Lemma lem7567935 (x : real) (y : real) : term10 x y.
Proof. exact (EQ_MP (@lem7567934 x y) (@lem7567933 x y)). Qed.
Lemma lem7567936 (x : real) (y : real) (z : real) : term11 x y z.
Proof. exact (@lem7567935 x y z). Qed.
Lemma lem7567937 (x : real) (y : real) (z : real) : (term11 x y z) = ((term12 x y z) = (term13 x y z)).
Proof. exact (eq_refl (term11 x y z)). Qed.
Lemma lem7567939 (x : real) : term48 x.
Proof. exact (@lem1631005 x). Qed.
Lemma lem7567940 (x : real) : (term48 x) = ((term49 x) = x).
Proof. exact (eq_refl (term48 x)). Qed.
Lemma lem7567942 (x : real) : term14 x.
Proof. exact (@lem1596102 x). Qed.
Lemma lem7567943 (x : real) : (term14 x) = (term15 x).
Proof. exact (eq_refl (term14 x)). Qed.
Lemma lem7567944 (x : real) : term15 x.
Proof. exact (EQ_MP (@lem7567943 x) (@lem7567942 x)). Qed.
Lemma lem7567945 (x : real) (m : nat) : term16 x m.
Proof. exact (@lem7567944 x m). Qed.
Lemma lem7567946 (m : nat) (x : real) : (term16 x m) = (term17 m x).
Proof. exact (eq_refl (term16 x m)). Qed.
Lemma lem7567947 (m : nat) (x : real) : term17 m x.
Proof. exact (EQ_MP (@lem7567946 m x) (@lem7567945 x m)). Qed.
Lemma lem7567948 (m : nat) (x : real) (n : nat) : term18 m x n.
Proof. exact (@lem7567947 m x n). Qed.
Lemma lem7567949 (m : nat) (x : real) (n : nat) : (term18 m x n) = ((term19 x m n) = (term20 m x n)).
Proof. exact (eq_refl (term18 m x n)). Qed.
Lemma lem7567951 : term21.
Proof. exact (@lem7223171 term22). Qed.
Lemma lem7567952 : term21 = term23.
Proof. exact (eq_refl term21). Qed.
Lemma lem7567953 : term23.
Proof. exact (EQ_MP (@lem7567952) (@lem7567951)). Qed.
Lemma lem7567954 (f : nat -> real) : term50 f.
Proof. exact (@lem7567953 f). Qed.
Lemma lem7567955 (f : nat -> real) : (term50 f) = (term51 f).
Proof. exact (eq_refl (term50 f)). Qed.
Lemma lem7567956 (f : nat -> real) : term51 f.
Proof. exact (EQ_MP (@lem7567955 f) (@lem7567954 f)). Qed.
Lemma lem7567957 (f : nat -> real) (m : nat) : term52 f m.
Proof. exact (@lem7567956 f m). Qed.
Lemma lem7567958 (m : nat) (f : nat -> real) : (term52 f m) = (term53 m f).
Proof. exact (eq_refl (term52 f m)). Qed.
Lemma lem7567959 (m : nat) (f : nat -> real) : term53 m f.
Proof. exact (EQ_MP (@lem7567958 m f) (@lem7567957 f m)). Qed.
Lemma lem7567960 (m : nat) (f : nat -> real) (n : nat) : term54 m f n.
Proof. exact (@lem7567959 m f n). Qed.
Lemma lem7567961 (m : nat) (n : nat) (f : nat -> real) : (term54 m f n) = ((term55 m n f) = (term56 m n f)).
Proof. exact (eq_refl (term54 m f n)). Qed.
Lemma lem7567963 (h1 : term57) : term57.
Proof. exact (h1). Qed.
Lemma lem7567964 (p : real -> real) (h1 : term57) : term58 p.
Proof. exact (@lem7567963 h1 p). Qed.
Lemma lem7567965 (p : real -> real) : (term58 p) = (term59 p).
Proof. exact (eq_refl (term58 p)). Qed.
Lemma lem7567966 (p : real -> real) (h1 : term57) : term59 p.
Proof. exact (EQ_MP (@lem7567965 p) (@lem7567964 p h1)). Qed.
Lemma lem7567967 (p : real -> real) (q : real -> real) (h1 : term57) : term60 p q.
Proof. exact (@lem7567966 p h1 q). Qed.
Lemma lem7567968 (p : real -> real) (q : real -> real) : (term60 p q) = (term61 p q).
Proof. exact (eq_refl (term60 p q)). Qed.
Lemma lem7567969 (p : real -> real) (q : real -> real) (h1 : term57) : term61 p q.
Proof. exact (EQ_MP (@lem7567968 p q) (@lem7567967 p q h1)). Qed.
Lemma lem7567970 (p : real -> real) (q : real -> real) (h1 : term62 p q) : term62 p q.
Proof. exact (h1). Qed.
Lemma lem7567971 (p : real -> real) (q : real -> real) (h1 : term57) (h2 : term62 p q) : term63 p q.
Proof. exact (@lem7567969 p q h1 (@lem7567970 p q h2)). Qed.
Lemma lem7567972 (p : real -> real) (q : real -> real) (h1 : term62 p q) : term64 p q.
Proof. exact (fun h0 : term57 => @lem7567971 p q h0 h1). Qed.
Lemma lem7567973 (h1 : term57) : term57.
Proof. exact (h1). Qed.
Lemma lem7567974 (p : real -> real) (q : real -> real) (h1 : term57) (h2 : term62 p q) : term63 p q.
Proof. exact (@lem7567972 p q h2 (@lem7567973 h1)). Qed.
Lemma lem7567975 (p : real -> real) (q : real -> real) (h1 : term57) : term61 p q.
Proof. exact (fun h0 : term62 p q => @lem7567974 p q h1 h0). Qed.
Lemma lem7567976 (p : real -> real) (h1 : term57) : term59 p.
Proof. exact (fun q : real -> real => @lem7567975 p q h1). Qed.
Lemma lem7567977 (h1 : term57) : term57.
Proof. exact (fun p : real -> real => @lem7567976 p h1). Qed.
Lemma lem7567978 : term65.
Proof. exact (fun h0 : term57 => @lem7567977 h0). Qed.
Lemma lem7567979 : term57.
Proof. exact (@lem7567978 (@lem7567170)). Qed.
Lemma lem7567980 (p : real -> real) : term58 p.
Proof. exact (@lem7567979 p). Qed.
Lemma lem7567981 (p : real -> real) : (term58 p) = (term59 p).
Proof. exact (eq_refl (term58 p)). Qed.
Lemma lem7567982 (p : real -> real) : term59 p.
Proof. exact (EQ_MP (@lem7567981 p) (@lem7567980 p)). Qed.
Lemma lem7567983 (p : real -> real) (q : real -> real) : term60 p q.
Proof. exact (@lem7567982 p q). Qed.
Lemma lem7567984 (p : real -> real) (q : real -> real) : (term60 p q) = (term61 p q).
Proof. exact (eq_refl (term60 p q)). Qed.
Lemma lem7567991 (x : real) : term66 x.
Proof. exact (@lem1339188 x). Qed.
Lemma lem7567992 (x : real) : (term66 x) = (term67 x).
Proof. exact (eq_refl (term66 x)). Qed.
Lemma lem7567993 (x : real) : term67 x.
Proof. exact (EQ_MP (@lem7567992 x) (@lem7567991 x)). Qed.
Lemma lem7567994 (x : real) (y : real) : term68 x y.
Proof. exact (@lem7567993 x y). Qed.
Lemma lem7567995 (y : real) (x : real) : (term68 x y) = (term69 y x).
Proof. exact (eq_refl (term68 x y)). Qed.
Lemma lem7567996 (y : real) (x : real) : term69 y x.
Proof. exact (EQ_MP (@lem7567995 y x) (@lem7567994 x y)). Qed.
Lemma lem7567997 (y : real) (x : real) (z : real) : term70 y x z.
Proof. exact (@lem7567996 y x z). Qed.
Lemma lem7567998 (y : real) (x : real) (z : real) : (term70 y x z) = ((term71 x y z) = (term72 y x z)).
Proof. exact (eq_refl (term70 y x z)). Qed.
Lemma lem7568000 (m : nat) : term73 m.
Proof. exact (@lem80621 m). Qed.
Lemma lem7568001 (m : nat) : (term73 m) = ((S m) = (term74 m)).
Proof. exact (eq_refl (term73 m)). Qed.
Lemma lem7568003 (n : nat) : term24 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem7568004 (n : nat) : (term24 n) = (term25 n).
Proof. exact (eq_refl (term24 n)). Qed.
Lemma lem7568005 (n : nat) : term25 n.
Proof. exact (EQ_MP (@lem7568004 n) (@lem7568003 n)). Qed.
Lemma lem7568006 (n : nat) : (term25 n) = ((term25 n) = True).
Proof. exact (@lem7 (term25 n)). Qed.
Lemma lem7568008 (f : nat -> real) : term26 f.
Proof. exact (@lem7226008 f). Qed.
Lemma lem7568009 (f : nat -> real) : (term26 f) = (term27 f).
Proof. exact (eq_refl (term26 f)). Qed.
Lemma lem7568010 (f : nat -> real) : term27 f.
Proof. exact (EQ_MP (@lem7568009 f) (@lem7568008 f)). Qed.
Lemma lem7568011 (f : nat -> real) (m : nat) : term28 f m.
Proof. exact (@lem7568010 f m). Qed.
Lemma lem7568012 (m : nat) (f : nat -> real) : (term28 f m) = (term29 m f).
Proof. exact (eq_refl (term28 f m)). Qed.
Lemma lem7568013 (m : nat) (f : nat -> real) : term29 m f.
Proof. exact (EQ_MP (@lem7568012 m f) (@lem7568011 f m)). Qed.
Lemma lem7568014 (m : nat) (f : nat -> real) (n : nat) : term30 m f n.
Proof. exact (@lem7568013 m f n). Qed.
Lemma lem7568015 (m : nat) (n : nat) (f : nat -> real) : (term30 m f n) = (term31 m n f).
Proof. exact (eq_refl (term30 m f n)). Qed.
Lemma lem7568016 (m : nat) (n : nat) (f : nat -> real) : term31 m n f.
Proof. exact (EQ_MP (@lem7568015 m n f) (@lem7568014 m f n)). Qed.
Lemma lem7568017 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem7568018 (f : nat -> real) (m : nat) (n : nat) (h1 : Peano.le m n) : (term32 m n f) = (term33 m n f).
Proof. exact (@lem7568016 m n f (@lem7568017 m n h1)). Qed.
Lemma lem7568024 {A : Type'} (a : A) : term75 A a.
Proof. exact (@lem4363 A a). Qed.
Lemma lem7568025 {A : Type'} (a : A) : (term75 A a) = (term76 A a).
Proof. exact (eq_refl (term75 A a)). Qed.
Lemma lem7568026 {A : Type'} (a : A) : term76 A a.
Proof. exact (EQ_MP (@lem7568025 A a) (@lem7568024 A a)). Qed.
Lemma lem7568027 {A : Type'} (a : A) : (term76 A a) = ((term76 A a) = True).
Proof. exact (@lem7 (term76 A a)). Qed.
Lemma lem7568029 {A : Type'} (P : A -> Prop) : term77 A P.
Proof. exact (@lem6754 A P). Qed.
Lemma lem7568030 {A : Type'} (P : A -> Prop) : (term77 A P) = (term78 A P).
Proof. exact (eq_refl (term77 A P)). Qed.
Lemma lem7568031 {A : Type'} (P : A -> Prop) : term78 A P.
Proof. exact (EQ_MP (@lem7568030 A P) (@lem7568029 A P)). Qed.
Lemma lem7568032 {A : Type'} (P : A -> Prop) (Q : Prop) : term79 A P Q.
Proof. exact (@lem7568031 A P Q). Qed.
Lemma lem7568033 {A : Type'} (P : A -> Prop) (Q : Prop) : (term79 A P Q) = ((term38 A P Q) = (term37 A P Q)).
Proof. exact (eq_refl (term79 A P Q)). Qed.
Lemma lem7568037 {A B : Type'} (f : A -> B) (g : A -> B) (h1 : (f = g) = (term44 A B f g)) : (f = g) = (term44 A B f g).
Proof. exact (h1). Qed.
Lemma lem7568038 {A B : Type'} (f : A -> B) (g : A -> B) (h1 : (f = g) = (term44 A B f g)) : (term44 A B f g) = (f = g).
Proof. exact (SYM (@lem7568037 A B f g h1)). Qed.
Lemma lem7568039 {A B : Type'} (f : A -> B) (g : A -> B) (h1 : (term44 A B f g) = (f = g)) : (term44 A B f g) = (f = g).
Proof. exact (h1). Qed.
Lemma lem7568040 {A B : Type'} (f : A -> B) (g : A -> B) (h1 : (term44 A B f g) = (f = g)) : (f = g) = (term44 A B f g).
Proof. exact (SYM (@lem7568039 A B f g h1)). Qed.
Lemma lem7568041 {A B : Type'} (f : A -> B) (g : A -> B) : ((f = g) = (term44 A B f g)) = ((term44 A B f g) = (f = g)).
Proof. exact (prop_ext (fun h1 : (f = g) = (term44 A B f g) => @lem7568038 A B f g h1) (fun h1 : (term44 A B f g) = (f = g) => @lem7568040 A B f g h1)). Qed.
Lemma lem7568042 {A B : Type'} (f : A -> B) : (term80 A B f) = (term81 A B f).
Proof. exact (fun_ext (fun g : A -> B => @lem7568041 A B f g)). Qed.
Lemma lem7568043 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem7568044 {A B : Type'} (f : A -> B) : (term42 A B f) = (term82 A B f).
Proof. exact (MK_COMB (@lem7568043 A B) (@lem7568042 A B f)). Qed.
Lemma lem7568045 {A B : Type'} : (term83 A B) = (term84 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem7568044 A B f)). Qed.
Lemma lem7568046 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem7568047 {A B : Type'} : (term85 A B) = (term86 A B).
Proof. exact (MK_COMB (@lem7568046 A B) (@lem7568045 A B)). Qed.
Lemma lem7568048 {A B : Type'} : term86 A B.
Proof. exact (EQ_MP (@lem7568047 A B) (@lem9220 A B)). Qed.
Lemma lem7568049 {A B : Type'} (f : A -> B) : term87 A B f.
Proof. exact (@lem7568048 A B f). Qed.
Lemma lem7568050 {A B : Type'} (f : A -> B) : (term87 A B f) = (term82 A B f).
Proof. exact (eq_refl (term87 A B f)). Qed.
Lemma lem7568051 {A B : Type'} (f : A -> B) : term82 A B f.
Proof. exact (EQ_MP (@lem7568050 A B f) (@lem7568049 A B f)). Qed.
Lemma lem7568052 {A B : Type'} (f : A -> B) (g : A -> B) : term88 A B f g.
Proof. exact (@lem7568051 A B f g). Qed.
Lemma lem7568053 {A B : Type'} (f : A -> B) (g : A -> B) : (term88 A B f g) = ((term44 A B f g) = (f = g)).
Proof. exact (eq_refl (term88 A B f g)). Qed.
Lemma lem7568066 (p : Prop) : p = (term89 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7568067 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : ((term90 _139146 _139147 _139148 P) = (term91 _139146 _139147 _139148 P)) = (term92 _139146 _139147 _139148 P).
Proof. exact (@lem7568066 ((term90 _139146 _139147 _139148 P) = (term91 _139146 _139147 _139148 P))). Qed.
Lemma lem7568068 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term92 _139146 _139147 _139148 P) = ((term90 _139146 _139147 _139148 P) = (term91 _139146 _139147 _139148 P)).
Proof. exact (SYM (@lem7568067 _139146 _139147 _139148 P)). Qed.
Lemma lem7568069 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (h1 : term93 _139146 _139147 _139148 P) : term93 _139146 _139147 _139148 P.
Proof. exact (h1). Qed.
Lemma lem7568072 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (h1 : term92 _139146 _139147 _139148 P) : term92 _139146 _139147 _139148 P.
Proof. exact (h1). Qed.
Lemma lem7568073 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : term94 _139146 _139147 _139148 P.
Proof. exact (fun h0 : term92 _139146 _139147 _139148 P => @lem7568072 _139146 _139147 _139148 P h0). Qed.
Lemma lem7568074 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (h1 : term94 _139146 _139147 _139148 P) : term94 _139146 _139147 _139148 P.
Proof. exact (h1). Qed.
Lemma lem7568075 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (h1 : term92 _139146 _139147 _139148 P) : term92 _139146 _139147 _139148 P.
Proof. exact (h1). Qed.
Lemma lem7568076 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (h1 : term92 _139146 _139147 _139148 P) (h2 : term94 _139146 _139147 _139148 P) : term92 _139146 _139147 _139148 P.
Proof. exact (@lem7568074 _139146 _139147 _139148 P h2 (@lem7568075 _139146 _139147 _139148 P h1)). Qed.
Lemma lem7568077 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (h1 : term92 _139146 _139147 _139148 P) : term95 _139146 _139147 _139148 P.
Proof. exact (fun h0 : term94 _139146 _139147 _139148 P => @lem7568076 _139146 _139147 _139148 P h1 h0). Qed.
Lemma lem7568078 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (h1 : term94 _139146 _139147 _139148 P) : term94 _139146 _139147 _139148 P.
Proof. exact (h1). Qed.
Lemma lem7568079 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (h1 : term92 _139146 _139147 _139148 P) (h2 : term94 _139146 _139147 _139148 P) : term92 _139146 _139147 _139148 P.
Proof. exact (@lem7568077 _139146 _139147 _139148 P h1 (@lem7568078 _139146 _139147 _139148 P h2)). Qed.
Lemma lem7568080 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (h1 : term94 _139146 _139147 _139148 P) : term94 _139146 _139147 _139148 P.
Proof. exact (fun h0 : term92 _139146 _139147 _139148 P => @lem7568079 _139146 _139147 _139148 P h0 h1). Qed.
Lemma lem7568081 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : term96 _139146 _139147 _139148 P.
Proof. exact (fun h0 : term94 _139146 _139147 _139148 P => @lem7568080 _139146 _139147 _139148 P h0). Qed.
Lemma lem7568084 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : term94 _139146 _139147 _139148 P.
Proof. exact (@lem7568081 _139146 _139147 _139148 P (@lem7568073 _139146 _139147 _139148 P)). Qed.
Lemma lem7568085 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : term94 _139146 _139147 _139148 P.
Proof. exact (@lem7568084 _139146 _139147 _139148 P). Qed.
Lemma lem7568091 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7568092 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term92 _139146 _139147 _139148 P) = (term97 _139146 _139147 _139148 P).
Proof. exact (@lem7568091 (term93 _139146 _139147 _139148 P)). Qed.
Lemma lem7568094 (t : Prop) : (term98 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7568095 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term97 _139146 _139147 _139148 P) = ((term90 _139146 _139147 _139148 P) = (term91 _139146 _139147 _139148 P)).
Proof. exact (@lem7568094 ((term90 _139146 _139147 _139148 P) = (term91 _139146 _139147 _139148 P))). Qed.
Lemma lem7568096 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term92 _139146 _139147 _139148 P) = ((term90 _139146 _139147 _139148 P) = (term91 _139146 _139147 _139148 P)).
Proof. exact (TRANS (@lem7568092 _139146 _139147 _139148 P) (@lem7568095 _139146 _139147 _139148 P)). Qed.
Lemma lem7568121 {_139146 _139147 _139148 : Type'} : (term99 _139146 _139147 _139148) = (term100 _139146 _139147 _139148).
Proof. exact (fun_ext (fun P : type1517 _139146 _139147 _139148 => @lem7568096 _139146 _139147 _139148 P)). Qed.
Lemma lem7568122 {_139146 _139147 _139148 : Type'} : (@all (_139148 -> _139147 -> _139146 -> Prop)) = (@all (_139148 -> _139147 -> _139146 -> Prop)).
Proof. exact (eq_refl (@all (_139148 -> _139147 -> _139146 -> Prop))). Qed.
Lemma lem7568131 {_139146 _139147 _139148 : Type'} : (term101 _139146 _139147 _139148) = (term102 _139146 _139147 _139148).
Proof. exact (MK_COMB (@lem7568122 _139146 _139147 _139148) (@lem7568121 _139146 _139147 _139148)). Qed.
Lemma lem7568132 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) (c : _139146) : (P q m c) = (P q m c).
Proof. exact (eq_refl (P q m c)). Qed.
Lemma lem7568133 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) (c : _139146) : (term103 _139146 _139147 _139148 P m c) = (term103 _139146 _139147 _139148 P m c).
Proof. exact (fun_ext (fun q : _139148 => @lem7568132 _139146 _139147 _139148 P q m c)). Qed.
Lemma lem7568134 {_139148 : Type'} : (@all _139148) = (@all _139148).
Proof. exact (eq_refl (@all _139148)). Qed.
Lemma lem7568135 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) (c : _139146) : (term104 _139146 _139147 _139148 P m c) = (term104 _139146 _139147 _139148 P m c).
Proof. exact (MK_COMB (@lem7568134 _139148) (@lem7568133 _139146 _139147 _139148 P m c)). Qed.
Lemma lem7568136 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) : (term105 _139146 _139147 _139148 P m) = (term105 _139146 _139147 _139148 P m).
Proof. exact (fun_ext (fun c : _139146 => @lem7568135 _139146 _139147 _139148 P m c)). Qed.
Lemma lem7568137 {_139146 : Type'} : (@all _139146) = (@all _139146).
Proof. exact (eq_refl (@all _139146)). Qed.
Lemma lem7568138 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) : (term106 _139146 _139147 _139148 P m) = (term106 _139146 _139147 _139148 P m).
Proof. exact (MK_COMB (@lem7568137 _139146) (@lem7568136 _139146 _139147 _139148 P m)). Qed.
Lemma lem7568139 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term107 _139146 _139147 _139148 P) = (term107 _139146 _139147 _139148 P).
Proof. exact (fun_ext (fun m : _139147 => @lem7568138 _139146 _139147 _139148 P m)). Qed.
Lemma lem7568140 {_139147 : Type'} : (@all _139147) = (@all _139147).
Proof. exact (eq_refl (@all _139147)). Qed.
Lemma lem7568141 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term91 _139146 _139147 _139148 P) = (term91 _139146 _139147 _139148 P).
Proof. exact (MK_COMB (@lem7568140 _139147) (@lem7568139 _139146 _139147 _139148 P)). Qed.
Lemma lem7568142 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) (c : _139146) : (P q m c) = (P q m c).
Proof. exact (eq_refl (P q m c)). Qed.
Lemma lem7568143 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) : (term108 _139146 _139147 _139148 P q m) = (term108 _139146 _139147 _139148 P q m).
Proof. exact (fun_ext (fun c : _139146 => @lem7568142 _139146 _139147 _139148 P q m c)). Qed.
Lemma lem7568144 {_139146 : Type'} : (@all _139146) = (@all _139146).
Proof. exact (eq_refl (@all _139146)). Qed.
Lemma lem7568145 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) : (term109 _139146 _139147 _139148 P q m) = (term109 _139146 _139147 _139148 P q m).
Proof. exact (MK_COMB (@lem7568144 _139146) (@lem7568143 _139146 _139147 _139148 P q m)). Qed.
Lemma lem7568146 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) : (term110 _139146 _139147 _139148 P q) = (term110 _139146 _139147 _139148 P q).
Proof. exact (fun_ext (fun m : _139147 => @lem7568145 _139146 _139147 _139148 P q m)). Qed.
Lemma lem7568147 {_139147 : Type'} : (@all _139147) = (@all _139147).
Proof. exact (eq_refl (@all _139147)). Qed.
Lemma lem7568148 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) : (term111 _139146 _139147 _139148 P q) = (term111 _139146 _139147 _139148 P q).
Proof. exact (MK_COMB (@lem7568147 _139147) (@lem7568146 _139146 _139147 _139148 P q)). Qed.
Lemma lem7568149 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term112 _139146 _139147 _139148 P) = (term112 _139146 _139147 _139148 P).
Proof. exact (fun_ext (fun q : _139148 => @lem7568148 _139146 _139147 _139148 P q)). Qed.
Lemma lem7568150 {_139148 : Type'} : (@all _139148) = (@all _139148).
Proof. exact (eq_refl (@all _139148)). Qed.
Lemma lem7568151 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term90 _139146 _139147 _139148 P) = (term90 _139146 _139147 _139148 P).
Proof. exact (MK_COMB (@lem7568150 _139148) (@lem7568149 _139146 _139147 _139148 P)). Qed.
Lemma lem7568152 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7568153 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term113 _139146 _139147 _139148 P) = (term113 _139146 _139147 _139148 P).
Proof. exact (MK_COMB (@lem7568152) (@lem7568151 _139146 _139147 _139148 P)). Qed.
Lemma lem7568154 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : ((term90 _139146 _139147 _139148 P) = (term91 _139146 _139147 _139148 P)) = ((term90 _139146 _139147 _139148 P) = (term91 _139146 _139147 _139148 P)).
Proof. exact (MK_COMB (@lem7568153 _139146 _139147 _139148 P) (@lem7568141 _139146 _139147 _139148 P)). Qed.
Lemma lem7568155 {_139146 _139147 _139148 : Type'} : (term100 _139146 _139147 _139148) = (term100 _139146 _139147 _139148).
Proof. exact (fun_ext (fun P : type1517 _139146 _139147 _139148 => @lem7568154 _139146 _139147 _139148 P)). Qed.
Lemma lem7568156 {_139146 _139147 _139148 : Type'} : (@all (_139148 -> _139147 -> _139146 -> Prop)) = (@all (_139148 -> _139147 -> _139146 -> Prop)).
Proof. exact (eq_refl (@all (_139148 -> _139147 -> _139146 -> Prop))). Qed.
Lemma lem7568157 {_139146 _139147 _139148 : Type'} : (term102 _139146 _139147 _139148) = (term102 _139146 _139147 _139148).
Proof. exact (MK_COMB (@lem7568156 _139146 _139147 _139148) (@lem7568155 _139146 _139147 _139148)). Qed.
Lemma lem7568202 {_139146 _139147 _139148 : Type'} : (term101 _139146 _139147 _139148) = (term102 _139146 _139147 _139148).
Proof. exact (TRANS (@lem7568131 _139146 _139147 _139148) (@lem7568157 _139146 _139147 _139148)). Qed.
Lemma lem7568203 {_139146 _139147 _139148 : Type'} : (term102 _139146 _139147 _139148) = (term101 _139146 _139147 _139148).
Proof. exact (SYM (@lem7568202 _139146 _139147 _139148)). Qed.
Lemma lem7568205 (p : Prop) : p = (term89 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7568206 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : ((term90 _139146 _139147 _139148 P) = (term91 _139146 _139147 _139148 P)) = (term92 _139146 _139147 _139148 P).
Proof. exact (@lem7568205 ((term90 _139146 _139147 _139148 P) = (term91 _139146 _139147 _139148 P))). Qed.
Lemma lem7568207 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term92 _139146 _139147 _139148 P) = ((term90 _139146 _139147 _139148 P) = (term91 _139146 _139147 _139148 P)).
Proof. exact (SYM (@lem7568206 _139146 _139147 _139148 P)). Qed.
Lemma lem7568208 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (h1 : term93 _139146 _139147 _139148 P) : term93 _139146 _139147 _139148 P.
Proof. exact (h1). Qed.
Lemma lem7568210 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) (c : _139146) : (P q m c) = (P q m c).
Proof. exact (eq_refl (P q m c)). Qed.
Lemma lem7568211 {_139146 : Type'} (P : _139146 -> Prop) : (term114 _139146 P) = (term115 _139146 P).
Proof. exact (@lem18392 _139146 P). Qed.
Lemma lem7568212 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) : (term116 _139146 _139147 _139148 P q m) = (term117 _139146 _139147 _139148 P q m).
Proof. exact (@lem7568211 _139146 (term108 _139146 _139147 _139148 P q m)). Qed.
Lemma lem7568213 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) (c : _139146) : (term118 _139146 _139147 _139148 P q m c) = (P q m c).
Proof. exact (eq_refl (term118 _139146 _139147 _139148 P q m c)). Qed.
Lemma lem7568214 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7568216 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) (c : _139146) : (term119 _139146 _139147 _139148 P q m c) = (term120 _139146 _139147 _139148 P q m c).
Proof. exact (MK_COMB (@lem7568214) (@lem7568213 _139146 _139147 _139148 P q m c)). Qed.
Lemma lem7568217 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) : (term121 _139146 _139147 _139148 P q m) = (term122 _139146 _139147 _139148 P q m).
Proof. exact (fun_ext (fun c : _139146 => @lem7568216 _139146 _139147 _139148 P q m c)). Qed.
Lemma lem7568218 {_139146 : Type'} : (@ex _139146) = (@ex _139146).
Proof. exact (eq_refl (@ex _139146)). Qed.
Lemma lem7568219 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) : (term117 _139146 _139147 _139148 P q m) = (term123 _139146 _139147 _139148 P q m).
Proof. exact (MK_COMB (@lem7568218 _139146) (@lem7568217 _139146 _139147 _139148 P q m)). Qed.
Lemma lem7568220 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) : (term116 _139146 _139147 _139148 P q m) = (term123 _139146 _139147 _139148 P q m).
Proof. exact (TRANS (@lem7568212 _139146 _139147 _139148 P q m) (@lem7568219 _139146 _139147 _139148 P q m)). Qed.
Lemma lem7568221 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) : (term108 _139146 _139147 _139148 P q m) = (term108 _139146 _139147 _139148 P q m).
Proof. exact (fun_ext (fun c : _139146 => @lem7568210 _139146 _139147 _139148 P q m c)). Qed.
Lemma lem7568222 {_139146 : Type'} : (@all _139146) = (@all _139146).
Proof. exact (eq_refl (@all _139146)). Qed.
Lemma lem7568223 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) : (term109 _139146 _139147 _139148 P q m) = (term109 _139146 _139147 _139148 P q m).
Proof. exact (MK_COMB (@lem7568222 _139146) (@lem7568221 _139146 _139147 _139148 P q m)). Qed.
Lemma lem7568224 {_139147 : Type'} (P : _139147 -> Prop) : (term114 _139147 P) = (term115 _139147 P).
Proof. exact (@lem18392 _139147 P). Qed.
Lemma lem7568225 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) : (term124 _139146 _139147 _139148 P q) = (term125 _139146 _139147 _139148 P q).
Proof. exact (@lem7568224 _139147 (term110 _139146 _139147 _139148 P q)). Qed.
Lemma lem7568226 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) : (term126 _139146 _139147 _139148 P q m) = (term109 _139146 _139147 _139148 P q m).
Proof. exact (eq_refl (term126 _139146 _139147 _139148 P q m)). Qed.
Lemma lem7568227 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7568228 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) : (term127 _139146 _139147 _139148 P q m) = (term116 _139146 _139147 _139148 P q m).
Proof. exact (MK_COMB (@lem7568227) (@lem7568226 _139146 _139147 _139148 P q m)). Qed.
Lemma lem7568229 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) : (term127 _139146 _139147 _139148 P q m) = (term123 _139146 _139147 _139148 P q m).
Proof. exact (TRANS (@lem7568228 _139146 _139147 _139148 P q m) (@lem7568220 _139146 _139147 _139148 P q m)). Qed.
Lemma lem7568230 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) : (term128 _139146 _139147 _139148 P q) = (term129 _139146 _139147 _139148 P q).
Proof. exact (fun_ext (fun m : _139147 => @lem7568229 _139146 _139147 _139148 P q m)). Qed.
Lemma lem7568231 {_139147 : Type'} : (@ex _139147) = (@ex _139147).
Proof. exact (eq_refl (@ex _139147)). Qed.
Lemma lem7568232 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) : (term125 _139146 _139147 _139148 P q) = (term130 _139146 _139147 _139148 P q).
Proof. exact (MK_COMB (@lem7568231 _139147) (@lem7568230 _139146 _139147 _139148 P q)). Qed.
Lemma lem7568233 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) : (term124 _139146 _139147 _139148 P q) = (term130 _139146 _139147 _139148 P q).
Proof. exact (TRANS (@lem7568225 _139146 _139147 _139148 P q) (@lem7568232 _139146 _139147 _139148 P q)). Qed.
Lemma lem7568234 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) : (term110 _139146 _139147 _139148 P q) = (term110 _139146 _139147 _139148 P q).
Proof. exact (fun_ext (fun m : _139147 => @lem7568223 _139146 _139147 _139148 P q m)). Qed.
Lemma lem7568235 {_139147 : Type'} : (@all _139147) = (@all _139147).
Proof. exact (eq_refl (@all _139147)). Qed.
Lemma lem7568236 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) : (term111 _139146 _139147 _139148 P q) = (term111 _139146 _139147 _139148 P q).
Proof. exact (MK_COMB (@lem7568235 _139147) (@lem7568234 _139146 _139147 _139148 P q)). Qed.
Lemma lem7568237 {_139148 : Type'} (P : _139148 -> Prop) : (term114 _139148 P) = (term115 _139148 P).
Proof. exact (@lem18392 _139148 P). Qed.
Lemma lem7568238 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term131 _139146 _139147 _139148 P) = (term132 _139146 _139147 _139148 P).
Proof. exact (@lem7568237 _139148 (term112 _139146 _139147 _139148 P)). Qed.
Lemma lem7568239 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) : (term133 _139146 _139147 _139148 P q) = (term111 _139146 _139147 _139148 P q).
Proof. exact (eq_refl (term133 _139146 _139147 _139148 P q)). Qed.
Lemma lem7568240 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7568241 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) : (term134 _139146 _139147 _139148 P q) = (term124 _139146 _139147 _139148 P q).
Proof. exact (MK_COMB (@lem7568240) (@lem7568239 _139146 _139147 _139148 P q)). Qed.
Lemma lem7568242 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) : (term134 _139146 _139147 _139148 P q) = (term130 _139146 _139147 _139148 P q).
Proof. exact (TRANS (@lem7568241 _139146 _139147 _139148 P q) (@lem7568233 _139146 _139147 _139148 P q)). Qed.
Lemma lem7568243 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term135 _139146 _139147 _139148 P) = (term136 _139146 _139147 _139148 P).
Proof. exact (fun_ext (fun q : _139148 => @lem7568242 _139146 _139147 _139148 P q)). Qed.
Lemma lem7568244 {_139148 : Type'} : (@ex _139148) = (@ex _139148).
Proof. exact (eq_refl (@ex _139148)). Qed.
Lemma lem7568245 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term132 _139146 _139147 _139148 P) = (term137 _139146 _139147 _139148 P).
Proof. exact (MK_COMB (@lem7568244 _139148) (@lem7568243 _139146 _139147 _139148 P)). Qed.
Lemma lem7568246 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term131 _139146 _139147 _139148 P) = (term137 _139146 _139147 _139148 P).
Proof. exact (TRANS (@lem7568238 _139146 _139147 _139148 P) (@lem7568245 _139146 _139147 _139148 P)). Qed.
Lemma lem7568247 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term112 _139146 _139147 _139148 P) = (term112 _139146 _139147 _139148 P).
Proof. exact (fun_ext (fun q : _139148 => @lem7568236 _139146 _139147 _139148 P q)). Qed.
Lemma lem7568248 {_139148 : Type'} : (@all _139148) = (@all _139148).
Proof. exact (eq_refl (@all _139148)). Qed.
Lemma lem7568249 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term90 _139146 _139147 _139148 P) = (term90 _139146 _139147 _139148 P).
Proof. exact (MK_COMB (@lem7568248 _139148) (@lem7568247 _139146 _139147 _139148 P)). Qed.
Lemma lem7568251 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) (c : _139146) : (P q m c) = (P q m c).
Proof. exact (eq_refl (P q m c)). Qed.
Lemma lem7568252 {_139148 : Type'} (P : _139148 -> Prop) : (term114 _139148 P) = (term115 _139148 P).
Proof. exact (@lem18392 _139148 P). Qed.
Lemma lem7568253 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) (c : _139146) : (term138 _139146 _139147 _139148 P m c) = (term139 _139146 _139147 _139148 P m c).
Proof. exact (@lem7568252 _139148 (term103 _139146 _139147 _139148 P m c)). Qed.
Lemma lem7568254 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) (c : _139146) : (term140 _139146 _139147 _139148 P m c q) = (P q m c).
Proof. exact (eq_refl (term140 _139146 _139147 _139148 P m c q)). Qed.
Lemma lem7568255 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7568257 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) (c : _139146) : (term141 _139146 _139147 _139148 P m c q) = (term120 _139146 _139147 _139148 P q m c).
Proof. exact (MK_COMB (@lem7568255) (@lem7568254 _139146 _139147 _139148 P q m c)). Qed.
Lemma lem7568258 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) (c : _139146) : (term142 _139146 _139147 _139148 P m c) = (term143 _139146 _139147 _139148 P m c).
Proof. exact (fun_ext (fun q : _139148 => @lem7568257 _139146 _139147 _139148 P q m c)). Qed.
Lemma lem7568259 {_139148 : Type'} : (@ex _139148) = (@ex _139148).
Proof. exact (eq_refl (@ex _139148)). Qed.
Lemma lem7568260 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) (c : _139146) : (term139 _139146 _139147 _139148 P m c) = (term144 _139146 _139147 _139148 P m c).
Proof. exact (MK_COMB (@lem7568259 _139148) (@lem7568258 _139146 _139147 _139148 P m c)). Qed.
Lemma lem7568261 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) (c : _139146) : (term138 _139146 _139147 _139148 P m c) = (term144 _139146 _139147 _139148 P m c).
Proof. exact (TRANS (@lem7568253 _139146 _139147 _139148 P m c) (@lem7568260 _139146 _139147 _139148 P m c)). Qed.
Lemma lem7568262 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) (c : _139146) : (term103 _139146 _139147 _139148 P m c) = (term103 _139146 _139147 _139148 P m c).
Proof. exact (fun_ext (fun q : _139148 => @lem7568251 _139146 _139147 _139148 P q m c)). Qed.
Lemma lem7568263 {_139148 : Type'} : (@all _139148) = (@all _139148).
Proof. exact (eq_refl (@all _139148)). Qed.
Lemma lem7568264 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) (c : _139146) : (term104 _139146 _139147 _139148 P m c) = (term104 _139146 _139147 _139148 P m c).
Proof. exact (MK_COMB (@lem7568263 _139148) (@lem7568262 _139146 _139147 _139148 P m c)). Qed.
Lemma lem7568265 {_139146 : Type'} (P : _139146 -> Prop) : (term114 _139146 P) = (term115 _139146 P).
Proof. exact (@lem18392 _139146 P). Qed.
Lemma lem7568266 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) : (term145 _139146 _139147 _139148 P m) = (term146 _139146 _139147 _139148 P m).
Proof. exact (@lem7568265 _139146 (term105 _139146 _139147 _139148 P m)). Qed.
Lemma lem7568267 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) (c : _139146) : (term147 _139146 _139147 _139148 P m c) = (term104 _139146 _139147 _139148 P m c).
Proof. exact (eq_refl (term147 _139146 _139147 _139148 P m c)). Qed.
Lemma lem7568268 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7568269 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) (c : _139146) : (term148 _139146 _139147 _139148 P m c) = (term138 _139146 _139147 _139148 P m c).
Proof. exact (MK_COMB (@lem7568268) (@lem7568267 _139146 _139147 _139148 P m c)). Qed.
Lemma lem7568270 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) (c : _139146) : (term148 _139146 _139147 _139148 P m c) = (term144 _139146 _139147 _139148 P m c).
Proof. exact (TRANS (@lem7568269 _139146 _139147 _139148 P m c) (@lem7568261 _139146 _139147 _139148 P m c)). Qed.
Lemma lem7568271 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) : (term149 _139146 _139147 _139148 P m) = (term150 _139146 _139147 _139148 P m).
Proof. exact (fun_ext (fun c : _139146 => @lem7568270 _139146 _139147 _139148 P m c)). Qed.
Lemma lem7568272 {_139146 : Type'} : (@ex _139146) = (@ex _139146).
Proof. exact (eq_refl (@ex _139146)). Qed.
Lemma lem7568273 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) : (term146 _139146 _139147 _139148 P m) = (term151 _139146 _139147 _139148 P m).
Proof. exact (MK_COMB (@lem7568272 _139146) (@lem7568271 _139146 _139147 _139148 P m)). Qed.
Lemma lem7568274 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) : (term145 _139146 _139147 _139148 P m) = (term151 _139146 _139147 _139148 P m).
Proof. exact (TRANS (@lem7568266 _139146 _139147 _139148 P m) (@lem7568273 _139146 _139147 _139148 P m)). Qed.
Lemma lem7568275 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) : (term105 _139146 _139147 _139148 P m) = (term105 _139146 _139147 _139148 P m).
Proof. exact (fun_ext (fun c : _139146 => @lem7568264 _139146 _139147 _139148 P m c)). Qed.
Lemma lem7568276 {_139146 : Type'} : (@all _139146) = (@all _139146).
Proof. exact (eq_refl (@all _139146)). Qed.
Lemma lem7568277 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) : (term106 _139146 _139147 _139148 P m) = (term106 _139146 _139147 _139148 P m).
Proof. exact (MK_COMB (@lem7568276 _139146) (@lem7568275 _139146 _139147 _139148 P m)). Qed.
Lemma lem7568278 {_139147 : Type'} (P : _139147 -> Prop) : (term114 _139147 P) = (term115 _139147 P).
Proof. exact (@lem18392 _139147 P). Qed.
Lemma lem7568279 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term152 _139146 _139147 _139148 P) = (term153 _139146 _139147 _139148 P).
Proof. exact (@lem7568278 _139147 (term107 _139146 _139147 _139148 P)). Qed.
Lemma lem7568280 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) : (term154 _139146 _139147 _139148 P m) = (term106 _139146 _139147 _139148 P m).
Proof. exact (eq_refl (term154 _139146 _139147 _139148 P m)). Qed.
Lemma lem7568281 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7568282 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) : (term155 _139146 _139147 _139148 P m) = (term145 _139146 _139147 _139148 P m).
Proof. exact (MK_COMB (@lem7568281) (@lem7568280 _139146 _139147 _139148 P m)). Qed.
Lemma lem7568283 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) : (term155 _139146 _139147 _139148 P m) = (term151 _139146 _139147 _139148 P m).
Proof. exact (TRANS (@lem7568282 _139146 _139147 _139148 P m) (@lem7568274 _139146 _139147 _139148 P m)). Qed.
Lemma lem7568284 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term156 _139146 _139147 _139148 P) = (term157 _139146 _139147 _139148 P).
Proof. exact (fun_ext (fun m : _139147 => @lem7568283 _139146 _139147 _139148 P m)). Qed.
Lemma lem7568285 {_139147 : Type'} : (@ex _139147) = (@ex _139147).
Proof. exact (eq_refl (@ex _139147)). Qed.
Lemma lem7568286 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term153 _139146 _139147 _139148 P) = (term158 _139146 _139147 _139148 P).
Proof. exact (MK_COMB (@lem7568285 _139147) (@lem7568284 _139146 _139147 _139148 P)). Qed.
Lemma lem7568287 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term152 _139146 _139147 _139148 P) = (term158 _139146 _139147 _139148 P).
Proof. exact (TRANS (@lem7568279 _139146 _139147 _139148 P) (@lem7568286 _139146 _139147 _139148 P)). Qed.
Lemma lem7568288 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term107 _139146 _139147 _139148 P) = (term107 _139146 _139147 _139148 P).
Proof. exact (fun_ext (fun m : _139147 => @lem7568277 _139146 _139147 _139148 P m)). Qed.
Lemma lem7568289 {_139147 : Type'} : (@all _139147) = (@all _139147).
Proof. exact (eq_refl (@all _139147)). Qed.
Lemma lem7568290 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term91 _139146 _139147 _139148 P) = (term91 _139146 _139147 _139148 P).
Proof. exact (MK_COMB (@lem7568289 _139147) (@lem7568288 _139146 _139147 _139148 P)). Qed.
Lemma lem7568291 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7568292 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term159 _139146 _139147 _139148 P) = (term160 _139146 _139147 _139148 P).
Proof. exact (MK_COMB (@lem7568291) (@lem7568246 _139146 _139147 _139148 P)). Qed.
Lemma lem7568293 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term161 _139146 _139147 _139148 P) = (term162 _139146 _139147 _139148 P).
Proof. exact (MK_COMB (@lem7568292 _139146 _139147 _139148 P) (@lem7568290 _139146 _139147 _139148 P)). Qed.
Lemma lem7568294 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7568295 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term163 _139146 _139147 _139148 P) = (term163 _139146 _139147 _139148 P).
Proof. exact (MK_COMB (@lem7568294) (@lem7568249 _139146 _139147 _139148 P)). Qed.
Lemma lem7568296 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term164 _139146 _139147 _139148 P) = (term165 _139146 _139147 _139148 P).
Proof. exact (MK_COMB (@lem7568295 _139146 _139147 _139148 P) (@lem7568287 _139146 _139147 _139148 P)). Qed.
Lemma lem7568297 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7568298 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term166 _139146 _139147 _139148 P) = (term167 _139146 _139147 _139148 P).
Proof. exact (MK_COMB (@lem7568297) (@lem7568296 _139146 _139147 _139148 P)). Qed.
Lemma lem7568299 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term168 _139146 _139147 _139148 P) = (term169 _139146 _139147 _139148 P).
Proof. exact (MK_COMB (@lem7568298 _139146 _139147 _139148 P) (@lem7568293 _139146 _139147 _139148 P)). Qed.
Lemma lem7568300 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term93 _139146 _139147 _139148 P) = (term168 _139146 _139147 _139148 P).
Proof. exact (@lem17646 (term90 _139146 _139147 _139148 P) (term91 _139146 _139147 _139148 P)). Qed.
Lemma lem7568301 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term93 _139146 _139147 _139148 P) = (term169 _139146 _139147 _139148 P).
Proof. exact (TRANS (@lem7568300 _139146 _139147 _139148 P) (@lem7568299 _139146 _139147 _139148 P)). Qed.
Lemma lem7568352 {A : Type'} (P : Prop) (Q : A -> Prop) : (term170 A P Q) = (term171 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem7568353 {_139147 : Type'} (P : Prop) (Q : _139147 -> Prop) : (term170 _139147 P Q) = (term171 _139147 P Q).
Proof. exact (@lem7568352 _139147 P Q). Qed.
Lemma lem7568354 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term172 _139146 _139147 _139148 P) = (term173 _139146 _139147 _139148 P).
Proof. exact (@lem7568353 _139147 (term90 _139146 _139147 _139148 P) (term157 _139146 _139147 _139148 P)). Qed.
Lemma lem7568355 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) : (term174 _139146 _139147 _139148 P m) = (term151 _139146 _139147 _139148 P m).
Proof. exact (eq_refl (term174 _139146 _139147 _139148 P m)). Qed.
Lemma lem7568356 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term175 _139146 _139147 _139148 P) = (term157 _139146 _139147 _139148 P).
Proof. exact (fun_ext (fun m : _139147 => @lem7568355 _139146 _139147 _139148 P m)). Qed.
Lemma lem7568357 {_139147 : Type'} : (@ex _139147) = (@ex _139147).
Proof. exact (eq_refl (@ex _139147)). Qed.
Lemma lem7568358 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term176 _139146 _139147 _139148 P) = (term158 _139146 _139147 _139148 P).
Proof. exact (MK_COMB (@lem7568357 _139147) (@lem7568356 _139146 _139147 _139148 P)). Qed.
Lemma lem7568359 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term163 _139146 _139147 _139148 P) = (term163 _139146 _139147 _139148 P).
Proof. exact (eq_refl (term163 _139146 _139147 _139148 P)). Qed.
Lemma lem7568360 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term172 _139146 _139147 _139148 P) = (term165 _139146 _139147 _139148 P).
Proof. exact (MK_COMB (@lem7568359 _139146 _139147 _139148 P) (@lem7568358 _139146 _139147 _139148 P)). Qed.
Lemma lem7568361 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7568362 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term177 _139146 _139147 _139148 P) = (term178 _139146 _139147 _139148 P).
Proof. exact (MK_COMB (@lem7568361) (@lem7568360 _139146 _139147 _139148 P)). Qed.
Lemma lem7568363 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) : (term174 _139146 _139147 _139148 P m) = (term151 _139146 _139147 _139148 P m).
Proof. exact (eq_refl (term174 _139146 _139147 _139148 P m)). Qed.
Lemma lem7568364 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term163 _139146 _139147 _139148 P) = (term163 _139146 _139147 _139148 P).
Proof. exact (eq_refl (term163 _139146 _139147 _139148 P)). Qed.
Lemma lem7568365 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) : (term179 _139146 _139147 _139148 P m) = (term180 _139146 _139147 _139148 P m).
Proof. exact (MK_COMB (@lem7568364 _139146 _139147 _139148 P) (@lem7568363 _139146 _139147 _139148 P m)). Qed.
Lemma lem7568366 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term181 _139146 _139147 _139148 P) = (term182 _139146 _139147 _139148 P).
Proof. exact (fun_ext (fun m : _139147 => @lem7568365 _139146 _139147 _139148 P m)). Qed.
Lemma lem7568367 {_139147 : Type'} : (@ex _139147) = (@ex _139147).
Proof. exact (eq_refl (@ex _139147)). Qed.
Lemma lem7568368 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term173 _139146 _139147 _139148 P) = (term183 _139146 _139147 _139148 P).
Proof. exact (MK_COMB (@lem7568367 _139147) (@lem7568366 _139146 _139147 _139148 P)). Qed.
Lemma lem7568369 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : ((term172 _139146 _139147 _139148 P) = (term173 _139146 _139147 _139148 P)) = ((term165 _139146 _139147 _139148 P) = (term183 _139146 _139147 _139148 P)).
Proof. exact (MK_COMB (@lem7568362 _139146 _139147 _139148 P) (@lem7568368 _139146 _139147 _139148 P)). Qed.
Lemma lem7568370 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term165 _139146 _139147 _139148 P) = (term183 _139146 _139147 _139148 P).
Proof. exact (EQ_MP (@lem7568369 _139146 _139147 _139148 P) (@lem7568354 _139146 _139147 _139148 P)). Qed.
Lemma lem7568372 {A : Type'} (P : Prop) (Q : A -> Prop) : (term170 A P Q) = (term171 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem7568373 {_139146 : Type'} (P : Prop) (Q : _139146 -> Prop) : (term170 _139146 P Q) = (term171 _139146 P Q).
Proof. exact (@lem7568372 _139146 P Q). Qed.
Lemma lem7568374 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) : (term184 _139146 _139147 _139148 P m) = (term185 _139146 _139147 _139148 P m).
Proof. exact (@lem7568373 _139146 (term90 _139146 _139147 _139148 P) (term150 _139146 _139147 _139148 P m)). Qed.
Lemma lem7568375 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) (c : _139146) : (term186 _139146 _139147 _139148 P m c) = (term144 _139146 _139147 _139148 P m c).
Proof. exact (eq_refl (term186 _139146 _139147 _139148 P m c)). Qed.
Lemma lem7568376 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) : (term187 _139146 _139147 _139148 P m) = (term150 _139146 _139147 _139148 P m).
Proof. exact (fun_ext (fun c : _139146 => @lem7568375 _139146 _139147 _139148 P m c)). Qed.
Lemma lem7568377 {_139146 : Type'} : (@ex _139146) = (@ex _139146).
Proof. exact (eq_refl (@ex _139146)). Qed.
Lemma lem7568378 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) : (term188 _139146 _139147 _139148 P m) = (term151 _139146 _139147 _139148 P m).
Proof. exact (MK_COMB (@lem7568377 _139146) (@lem7568376 _139146 _139147 _139148 P m)). Qed.
Lemma lem7568379 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term163 _139146 _139147 _139148 P) = (term163 _139146 _139147 _139148 P).
Proof. exact (eq_refl (term163 _139146 _139147 _139148 P)). Qed.
Lemma lem7568380 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) : (term184 _139146 _139147 _139148 P m) = (term180 _139146 _139147 _139148 P m).
Proof. exact (MK_COMB (@lem7568379 _139146 _139147 _139148 P) (@lem7568378 _139146 _139147 _139148 P m)). Qed.
Lemma lem7568381 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7568382 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) : (term189 _139146 _139147 _139148 P m) = (term190 _139146 _139147 _139148 P m).
Proof. exact (MK_COMB (@lem7568381) (@lem7568380 _139146 _139147 _139148 P m)). Qed.
Lemma lem7568383 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) (c : _139146) : (term186 _139146 _139147 _139148 P m c) = (term144 _139146 _139147 _139148 P m c).
Proof. exact (eq_refl (term186 _139146 _139147 _139148 P m c)). Qed.
Lemma lem7568384 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term163 _139146 _139147 _139148 P) = (term163 _139146 _139147 _139148 P).
Proof. exact (eq_refl (term163 _139146 _139147 _139148 P)). Qed.
Lemma lem7568385 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) (c : _139146) : (term191 _139146 _139147 _139148 P m c) = (term192 _139146 _139147 _139148 P m c).
Proof. exact (MK_COMB (@lem7568384 _139146 _139147 _139148 P) (@lem7568383 _139146 _139147 _139148 P m c)). Qed.
Lemma lem7568386 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) : (term193 _139146 _139147 _139148 P m) = (term194 _139146 _139147 _139148 P m).
Proof. exact (fun_ext (fun c : _139146 => @lem7568385 _139146 _139147 _139148 P m c)). Qed.
Lemma lem7568387 {_139146 : Type'} : (@ex _139146) = (@ex _139146).
Proof. exact (eq_refl (@ex _139146)). Qed.
Lemma lem7568388 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) : (term185 _139146 _139147 _139148 P m) = (term195 _139146 _139147 _139148 P m).
Proof. exact (MK_COMB (@lem7568387 _139146) (@lem7568386 _139146 _139147 _139148 P m)). Qed.
Lemma lem7568389 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) : ((term184 _139146 _139147 _139148 P m) = (term185 _139146 _139147 _139148 P m)) = ((term180 _139146 _139147 _139148 P m) = (term195 _139146 _139147 _139148 P m)).
Proof. exact (MK_COMB (@lem7568382 _139146 _139147 _139148 P m) (@lem7568388 _139146 _139147 _139148 P m)). Qed.
Lemma lem7568390 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) : (term180 _139146 _139147 _139148 P m) = (term195 _139146 _139147 _139148 P m).
Proof. exact (EQ_MP (@lem7568389 _139146 _139147 _139148 P m) (@lem7568374 _139146 _139147 _139148 P m)). Qed.
Lemma lem7568392 {A : Type'} (P : Prop) (Q : A -> Prop) : (term170 A P Q) = (term171 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem7568393 {_139148 : Type'} (P : Prop) (Q : _139148 -> Prop) : (term170 _139148 P Q) = (term171 _139148 P Q).
Proof. exact (@lem7568392 _139148 P Q). Qed.
Lemma lem7568394 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) (c : _139146) : (term196 _139146 _139147 _139148 P m c) = (term197 _139146 _139147 _139148 P m c).
Proof. exact (@lem7568393 _139148 (term90 _139146 _139147 _139148 P) (term143 _139146 _139147 _139148 P m c)). Qed.
Lemma lem7568395 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) (c : _139146) : (term198 _139146 _139147 _139148 P m c q) = (term120 _139146 _139147 _139148 P q m c).
Proof. exact (eq_refl (term198 _139146 _139147 _139148 P m c q)). Qed.
Lemma lem7568396 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) (c : _139146) : (term199 _139146 _139147 _139148 P m c) = (term143 _139146 _139147 _139148 P m c).
Proof. exact (fun_ext (fun q : _139148 => @lem7568395 _139146 _139147 _139148 P q m c)). Qed.
Lemma lem7568397 {_139148 : Type'} : (@ex _139148) = (@ex _139148).
Proof. exact (eq_refl (@ex _139148)). Qed.
Lemma lem7568398 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) (c : _139146) : (term200 _139146 _139147 _139148 P m c) = (term144 _139146 _139147 _139148 P m c).
Proof. exact (MK_COMB (@lem7568397 _139148) (@lem7568396 _139146 _139147 _139148 P m c)). Qed.
Lemma lem7568399 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term163 _139146 _139147 _139148 P) = (term163 _139146 _139147 _139148 P).
Proof. exact (eq_refl (term163 _139146 _139147 _139148 P)). Qed.
Lemma lem7568400 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) (c : _139146) : (term196 _139146 _139147 _139148 P m c) = (term192 _139146 _139147 _139148 P m c).
Proof. exact (MK_COMB (@lem7568399 _139146 _139147 _139148 P) (@lem7568398 _139146 _139147 _139148 P m c)). Qed.
Lemma lem7568401 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7568402 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) (c : _139146) : (term201 _139146 _139147 _139148 P m c) = (term202 _139146 _139147 _139148 P m c).
Proof. exact (MK_COMB (@lem7568401) (@lem7568400 _139146 _139147 _139148 P m c)). Qed.
Lemma lem7568403 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) (c : _139146) : (term198 _139146 _139147 _139148 P m c q) = (term120 _139146 _139147 _139148 P q m c).
Proof. exact (eq_refl (term198 _139146 _139147 _139148 P m c q)). Qed.
Lemma lem7568404 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term163 _139146 _139147 _139148 P) = (term163 _139146 _139147 _139148 P).
Proof. exact (eq_refl (term163 _139146 _139147 _139148 P)). Qed.
Lemma lem7568405 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) (c : _139146) : (term203 _139146 _139147 _139148 P m c q) = (term204 _139146 _139147 _139148 P q m c).
Proof. exact (MK_COMB (@lem7568404 _139146 _139147 _139148 P) (@lem7568403 _139146 _139147 _139148 P q m c)). Qed.
Lemma lem7568406 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) (c : _139146) : (term205 _139146 _139147 _139148 P m c) = (term206 _139146 _139147 _139148 P m c).
Proof. exact (fun_ext (fun q : _139148 => @lem7568405 _139146 _139147 _139148 P q m c)). Qed.
Lemma lem7568407 {_139148 : Type'} : (@ex _139148) = (@ex _139148).
Proof. exact (eq_refl (@ex _139148)). Qed.
Lemma lem7568408 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) (c : _139146) : (term197 _139146 _139147 _139148 P m c) = (term207 _139146 _139147 _139148 P m c).
Proof. exact (MK_COMB (@lem7568407 _139148) (@lem7568406 _139146 _139147 _139148 P m c)). Qed.
Lemma lem7568409 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) (c : _139146) : ((term196 _139146 _139147 _139148 P m c) = (term197 _139146 _139147 _139148 P m c)) = ((term192 _139146 _139147 _139148 P m c) = (term207 _139146 _139147 _139148 P m c)).
Proof. exact (MK_COMB (@lem7568402 _139146 _139147 _139148 P m c) (@lem7568408 _139146 _139147 _139148 P m c)). Qed.
Lemma lem7568410 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) (c : _139146) : (term192 _139146 _139147 _139148 P m c) = (term207 _139146 _139147 _139148 P m c).
Proof. exact (EQ_MP (@lem7568409 _139146 _139147 _139148 P m c) (@lem7568394 _139146 _139147 _139148 P m c)). Qed.
Lemma lem7568411 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) : (term194 _139146 _139147 _139148 P m) = (term208 _139146 _139147 _139148 P m).
Proof. exact (fun_ext (fun c : _139146 => @lem7568410 _139146 _139147 _139148 P m c)). Qed.
Lemma lem7568412 {_139146 : Type'} : (@ex _139146) = (@ex _139146).
Proof. exact (eq_refl (@ex _139146)). Qed.
Lemma lem7568413 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) : (term195 _139146 _139147 _139148 P m) = (term209 _139146 _139147 _139148 P m).
Proof. exact (MK_COMB (@lem7568412 _139146) (@lem7568411 _139146 _139147 _139148 P m)). Qed.
Lemma lem7568414 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) : (term180 _139146 _139147 _139148 P m) = (term209 _139146 _139147 _139148 P m).
Proof. exact (TRANS (@lem7568390 _139146 _139147 _139148 P m) (@lem7568413 _139146 _139147 _139148 P m)). Qed.
Lemma lem7568415 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term182 _139146 _139147 _139148 P) = (term210 _139146 _139147 _139148 P).
Proof. exact (fun_ext (fun m : _139147 => @lem7568414 _139146 _139147 _139148 P m)). Qed.
Lemma lem7568416 {_139147 : Type'} : (@ex _139147) = (@ex _139147).
Proof. exact (eq_refl (@ex _139147)). Qed.
Lemma lem7568417 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term183 _139146 _139147 _139148 P) = (term211 _139146 _139147 _139148 P).
Proof. exact (MK_COMB (@lem7568416 _139147) (@lem7568415 _139146 _139147 _139148 P)). Qed.
Lemma lem7568418 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term165 _139146 _139147 _139148 P) = (term211 _139146 _139147 _139148 P).
Proof. exact (TRANS (@lem7568370 _139146 _139147 _139148 P) (@lem7568417 _139146 _139147 _139148 P)). Qed.
Lemma lem7568419 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7568420 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term167 _139146 _139147 _139148 P) = (term212 _139146 _139147 _139148 P).
Proof. exact (MK_COMB (@lem7568419) (@lem7568418 _139146 _139147 _139148 P)). Qed.
Lemma lem7568422 {A : Type'} (P : A -> Prop) (Q : Prop) : (term213 A P Q) = (term214 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem7568423 {_139148 : Type'} (P : _139148 -> Prop) (Q : Prop) : (term213 _139148 P Q) = (term214 _139148 P Q).
Proof. exact (@lem7568422 _139148 P Q). Qed.
Lemma lem7568424 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term215 _139146 _139147 _139148 P) = (term216 _139146 _139147 _139148 P).
Proof. exact (@lem7568423 _139148 (term136 _139146 _139147 _139148 P) (term91 _139146 _139147 _139148 P)). Qed.
Lemma lem7568425 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) : (term217 _139146 _139147 _139148 P q) = (term130 _139146 _139147 _139148 P q).
Proof. exact (eq_refl (term217 _139146 _139147 _139148 P q)). Qed.
Lemma lem7568426 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term218 _139146 _139147 _139148 P) = (term136 _139146 _139147 _139148 P).
Proof. exact (fun_ext (fun q : _139148 => @lem7568425 _139146 _139147 _139148 P q)). Qed.
Lemma lem7568427 {_139148 : Type'} : (@ex _139148) = (@ex _139148).
Proof. exact (eq_refl (@ex _139148)). Qed.
Lemma lem7568428 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term219 _139146 _139147 _139148 P) = (term137 _139146 _139147 _139148 P).
Proof. exact (MK_COMB (@lem7568427 _139148) (@lem7568426 _139146 _139147 _139148 P)). Qed.
Lemma lem7568429 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7568430 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term220 _139146 _139147 _139148 P) = (term160 _139146 _139147 _139148 P).
Proof. exact (MK_COMB (@lem7568429) (@lem7568428 _139146 _139147 _139148 P)). Qed.
Lemma lem7568431 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term91 _139146 _139147 _139148 P) = (term91 _139146 _139147 _139148 P).
Proof. exact (eq_refl (term91 _139146 _139147 _139148 P)). Qed.
Lemma lem7568432 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term215 _139146 _139147 _139148 P) = (term162 _139146 _139147 _139148 P).
Proof. exact (MK_COMB (@lem7568430 _139146 _139147 _139148 P) (@lem7568431 _139146 _139147 _139148 P)). Qed.
Lemma lem7568433 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7568434 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term221 _139146 _139147 _139148 P) = (term222 _139146 _139147 _139148 P).
Proof. exact (MK_COMB (@lem7568433) (@lem7568432 _139146 _139147 _139148 P)). Qed.
Lemma lem7568435 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) : (term217 _139146 _139147 _139148 P q) = (term130 _139146 _139147 _139148 P q).
Proof. exact (eq_refl (term217 _139146 _139147 _139148 P q)). Qed.
Lemma lem7568436 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7568437 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) : (term223 _139146 _139147 _139148 P q) = (term224 _139146 _139147 _139148 P q).
Proof. exact (MK_COMB (@lem7568436) (@lem7568435 _139146 _139147 _139148 P q)). Qed.
Lemma lem7568438 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term91 _139146 _139147 _139148 P) = (term91 _139146 _139147 _139148 P).
Proof. exact (eq_refl (term91 _139146 _139147 _139148 P)). Qed.
Lemma lem7568439 {_139146 _139147 _139148 : Type'} (q : _139148) (P : type1517 _139146 _139147 _139148) : (term225 _139146 _139147 _139148 q P) = (term226 _139146 _139147 _139148 q P).
Proof. exact (MK_COMB (@lem7568437 _139146 _139147 _139148 P q) (@lem7568438 _139146 _139147 _139148 P)). Qed.
Lemma lem7568440 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term227 _139146 _139147 _139148 P) = (term228 _139146 _139147 _139148 P).
Proof. exact (fun_ext (fun q : _139148 => @lem7568439 _139146 _139147 _139148 q P)). Qed.
Lemma lem7568441 {_139148 : Type'} : (@ex _139148) = (@ex _139148).
Proof. exact (eq_refl (@ex _139148)). Qed.
Lemma lem7568442 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term216 _139146 _139147 _139148 P) = (term229 _139146 _139147 _139148 P).
Proof. exact (MK_COMB (@lem7568441 _139148) (@lem7568440 _139146 _139147 _139148 P)). Qed.
Lemma lem7568443 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : ((term215 _139146 _139147 _139148 P) = (term216 _139146 _139147 _139148 P)) = ((term162 _139146 _139147 _139148 P) = (term229 _139146 _139147 _139148 P)).
Proof. exact (MK_COMB (@lem7568434 _139146 _139147 _139148 P) (@lem7568442 _139146 _139147 _139148 P)). Qed.
Lemma lem7568444 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term162 _139146 _139147 _139148 P) = (term229 _139146 _139147 _139148 P).
Proof. exact (EQ_MP (@lem7568443 _139146 _139147 _139148 P) (@lem7568424 _139146 _139147 _139148 P)). Qed.
Lemma lem7568446 {A : Type'} (P : A -> Prop) (Q : Prop) : (term213 A P Q) = (term214 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem7568447 {_139147 : Type'} (P : _139147 -> Prop) (Q : Prop) : (term213 _139147 P Q) = (term214 _139147 P Q).
Proof. exact (@lem7568446 _139147 P Q). Qed.
Lemma lem7568448 {_139146 _139147 _139148 : Type'} (q : _139148) (P : type1517 _139146 _139147 _139148) : (term230 _139146 _139147 _139148 q P) = (term231 _139146 _139147 _139148 q P).
Proof. exact (@lem7568447 _139147 (term129 _139146 _139147 _139148 P q) (term91 _139146 _139147 _139148 P)). Qed.
Lemma lem7568449 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) : (term232 _139146 _139147 _139148 P q m) = (term123 _139146 _139147 _139148 P q m).
Proof. exact (eq_refl (term232 _139146 _139147 _139148 P q m)). Qed.
Lemma lem7568450 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) : (term233 _139146 _139147 _139148 P q) = (term129 _139146 _139147 _139148 P q).
Proof. exact (fun_ext (fun m : _139147 => @lem7568449 _139146 _139147 _139148 P q m)). Qed.
Lemma lem7568451 {_139147 : Type'} : (@ex _139147) = (@ex _139147).
Proof. exact (eq_refl (@ex _139147)). Qed.
Lemma lem7568452 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) : (term234 _139146 _139147 _139148 P q) = (term130 _139146 _139147 _139148 P q).
Proof. exact (MK_COMB (@lem7568451 _139147) (@lem7568450 _139146 _139147 _139148 P q)). Qed.
Lemma lem7568453 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7568454 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) : (term235 _139146 _139147 _139148 P q) = (term224 _139146 _139147 _139148 P q).
Proof. exact (MK_COMB (@lem7568453) (@lem7568452 _139146 _139147 _139148 P q)). Qed.
Lemma lem7568455 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term91 _139146 _139147 _139148 P) = (term91 _139146 _139147 _139148 P).
Proof. exact (eq_refl (term91 _139146 _139147 _139148 P)). Qed.
Lemma lem7568456 {_139146 _139147 _139148 : Type'} (q : _139148) (P : type1517 _139146 _139147 _139148) : (term230 _139146 _139147 _139148 q P) = (term226 _139146 _139147 _139148 q P).
Proof. exact (MK_COMB (@lem7568454 _139146 _139147 _139148 P q) (@lem7568455 _139146 _139147 _139148 P)). Qed.
Lemma lem7568457 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7568458 {_139146 _139147 _139148 : Type'} (q : _139148) (P : type1517 _139146 _139147 _139148) : (term236 _139146 _139147 _139148 q P) = (term237 _139146 _139147 _139148 q P).
Proof. exact (MK_COMB (@lem7568457) (@lem7568456 _139146 _139147 _139148 q P)). Qed.
Lemma lem7568459 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) : (term232 _139146 _139147 _139148 P q m) = (term123 _139146 _139147 _139148 P q m).
Proof. exact (eq_refl (term232 _139146 _139147 _139148 P q m)). Qed.
Lemma lem7568460 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7568461 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) : (term238 _139146 _139147 _139148 P q m) = (term239 _139146 _139147 _139148 P q m).
Proof. exact (MK_COMB (@lem7568460) (@lem7568459 _139146 _139147 _139148 P q m)). Qed.
Lemma lem7568462 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term91 _139146 _139147 _139148 P) = (term91 _139146 _139147 _139148 P).
Proof. exact (eq_refl (term91 _139146 _139147 _139148 P)). Qed.
Lemma lem7568463 {_139146 _139147 _139148 : Type'} (q : _139148) (m : _139147) (P : type1517 _139146 _139147 _139148) : (term240 _139146 _139147 _139148 q m P) = (term241 _139146 _139147 _139148 q m P).
Proof. exact (MK_COMB (@lem7568461 _139146 _139147 _139148 P q m) (@lem7568462 _139146 _139147 _139148 P)). Qed.
Lemma lem7568464 {_139146 _139147 _139148 : Type'} (q : _139148) (P : type1517 _139146 _139147 _139148) : (term242 _139146 _139147 _139148 q P) = (term243 _139146 _139147 _139148 q P).
Proof. exact (fun_ext (fun m : _139147 => @lem7568463 _139146 _139147 _139148 q m P)). Qed.
Lemma lem7568465 {_139147 : Type'} : (@ex _139147) = (@ex _139147).
Proof. exact (eq_refl (@ex _139147)). Qed.
Lemma lem7568466 {_139146 _139147 _139148 : Type'} (q : _139148) (P : type1517 _139146 _139147 _139148) : (term231 _139146 _139147 _139148 q P) = (term244 _139146 _139147 _139148 q P).
Proof. exact (MK_COMB (@lem7568465 _139147) (@lem7568464 _139146 _139147 _139148 q P)). Qed.
Lemma lem7568467 {_139146 _139147 _139148 : Type'} (q : _139148) (P : type1517 _139146 _139147 _139148) : ((term230 _139146 _139147 _139148 q P) = (term231 _139146 _139147 _139148 q P)) = ((term226 _139146 _139147 _139148 q P) = (term244 _139146 _139147 _139148 q P)).
Proof. exact (MK_COMB (@lem7568458 _139146 _139147 _139148 q P) (@lem7568466 _139146 _139147 _139148 q P)). Qed.
Lemma lem7568468 {_139146 _139147 _139148 : Type'} (q : _139148) (P : type1517 _139146 _139147 _139148) : (term226 _139146 _139147 _139148 q P) = (term244 _139146 _139147 _139148 q P).
Proof. exact (EQ_MP (@lem7568467 _139146 _139147 _139148 q P) (@lem7568448 _139146 _139147 _139148 q P)). Qed.
Lemma lem7568470 {A : Type'} (P : A -> Prop) (Q : Prop) : (term213 A P Q) = (term214 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem7568471 {_139146 : Type'} (P : _139146 -> Prop) (Q : Prop) : (term213 _139146 P Q) = (term214 _139146 P Q).
Proof. exact (@lem7568470 _139146 P Q). Qed.
Lemma lem7568472 {_139146 _139147 _139148 : Type'} (q : _139148) (m : _139147) (P : type1517 _139146 _139147 _139148) : (term245 _139146 _139147 _139148 q m P) = (term246 _139146 _139147 _139148 q m P).
Proof. exact (@lem7568471 _139146 (term122 _139146 _139147 _139148 P q m) (term91 _139146 _139147 _139148 P)). Qed.
Lemma lem7568473 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) (c : _139146) : (term247 _139146 _139147 _139148 P q m c) = (term120 _139146 _139147 _139148 P q m c).
Proof. exact (eq_refl (term247 _139146 _139147 _139148 P q m c)). Qed.
Lemma lem7568474 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) : (term248 _139146 _139147 _139148 P q m) = (term122 _139146 _139147 _139148 P q m).
Proof. exact (fun_ext (fun c : _139146 => @lem7568473 _139146 _139147 _139148 P q m c)). Qed.
Lemma lem7568475 {_139146 : Type'} : (@ex _139146) = (@ex _139146).
Proof. exact (eq_refl (@ex _139146)). Qed.
Lemma lem7568476 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) : (term249 _139146 _139147 _139148 P q m) = (term123 _139146 _139147 _139148 P q m).
Proof. exact (MK_COMB (@lem7568475 _139146) (@lem7568474 _139146 _139147 _139148 P q m)). Qed.
Lemma lem7568477 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7568478 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) : (term250 _139146 _139147 _139148 P q m) = (term239 _139146 _139147 _139148 P q m).
Proof. exact (MK_COMB (@lem7568477) (@lem7568476 _139146 _139147 _139148 P q m)). Qed.
Lemma lem7568479 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term91 _139146 _139147 _139148 P) = (term91 _139146 _139147 _139148 P).
Proof. exact (eq_refl (term91 _139146 _139147 _139148 P)). Qed.
Lemma lem7568480 {_139146 _139147 _139148 : Type'} (q : _139148) (m : _139147) (P : type1517 _139146 _139147 _139148) : (term245 _139146 _139147 _139148 q m P) = (term241 _139146 _139147 _139148 q m P).
Proof. exact (MK_COMB (@lem7568478 _139146 _139147 _139148 P q m) (@lem7568479 _139146 _139147 _139148 P)). Qed.
Lemma lem7568481 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7568482 {_139146 _139147 _139148 : Type'} (q : _139148) (m : _139147) (P : type1517 _139146 _139147 _139148) : (term251 _139146 _139147 _139148 q m P) = (term252 _139146 _139147 _139148 q m P).
Proof. exact (MK_COMB (@lem7568481) (@lem7568480 _139146 _139147 _139148 q m P)). Qed.
Lemma lem7568483 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) (c : _139146) : (term247 _139146 _139147 _139148 P q m c) = (term120 _139146 _139147 _139148 P q m c).
Proof. exact (eq_refl (term247 _139146 _139147 _139148 P q m c)). Qed.
Lemma lem7568484 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7568485 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) (c : _139146) : (term253 _139146 _139147 _139148 P q m c) = (term254 _139146 _139147 _139148 P q m c).
Proof. exact (MK_COMB (@lem7568484) (@lem7568483 _139146 _139147 _139148 P q m c)). Qed.
Lemma lem7568486 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term91 _139146 _139147 _139148 P) = (term91 _139146 _139147 _139148 P).
Proof. exact (eq_refl (term91 _139146 _139147 _139148 P)). Qed.
Lemma lem7568487 {_139146 _139147 _139148 : Type'} (q : _139148) (m : _139147) (c : _139146) (P : type1517 _139146 _139147 _139148) : (term255 _139146 _139147 _139148 q m c P) = (term256 _139146 _139147 _139148 q m c P).
Proof. exact (MK_COMB (@lem7568485 _139146 _139147 _139148 P q m c) (@lem7568486 _139146 _139147 _139148 P)). Qed.
Lemma lem7568488 {_139146 _139147 _139148 : Type'} (q : _139148) (m : _139147) (P : type1517 _139146 _139147 _139148) : (term257 _139146 _139147 _139148 q m P) = (term258 _139146 _139147 _139148 q m P).
Proof. exact (fun_ext (fun c : _139146 => @lem7568487 _139146 _139147 _139148 q m c P)). Qed.
Lemma lem7568489 {_139146 : Type'} : (@ex _139146) = (@ex _139146).
Proof. exact (eq_refl (@ex _139146)). Qed.
Lemma lem7568490 {_139146 _139147 _139148 : Type'} (q : _139148) (m : _139147) (P : type1517 _139146 _139147 _139148) : (term246 _139146 _139147 _139148 q m P) = (term259 _139146 _139147 _139148 q m P).
Proof. exact (MK_COMB (@lem7568489 _139146) (@lem7568488 _139146 _139147 _139148 q m P)). Qed.
Lemma lem7568491 {_139146 _139147 _139148 : Type'} (q : _139148) (m : _139147) (P : type1517 _139146 _139147 _139148) : ((term245 _139146 _139147 _139148 q m P) = (term246 _139146 _139147 _139148 q m P)) = ((term241 _139146 _139147 _139148 q m P) = (term259 _139146 _139147 _139148 q m P)).
Proof. exact (MK_COMB (@lem7568482 _139146 _139147 _139148 q m P) (@lem7568490 _139146 _139147 _139148 q m P)). Qed.
Lemma lem7568492 {_139146 _139147 _139148 : Type'} (q : _139148) (m : _139147) (P : type1517 _139146 _139147 _139148) : (term241 _139146 _139147 _139148 q m P) = (term259 _139146 _139147 _139148 q m P).
Proof. exact (EQ_MP (@lem7568491 _139146 _139147 _139148 q m P) (@lem7568472 _139146 _139147 _139148 q m P)). Qed.
Lemma lem7568493 {_139146 _139147 _139148 : Type'} (q : _139148) (P : type1517 _139146 _139147 _139148) : (term243 _139146 _139147 _139148 q P) = (term260 _139146 _139147 _139148 q P).
Proof. exact (fun_ext (fun m : _139147 => @lem7568492 _139146 _139147 _139148 q m P)). Qed.
Lemma lem7568494 {_139147 : Type'} : (@ex _139147) = (@ex _139147).
Proof. exact (eq_refl (@ex _139147)). Qed.
Lemma lem7568495 {_139146 _139147 _139148 : Type'} (q : _139148) (P : type1517 _139146 _139147 _139148) : (term244 _139146 _139147 _139148 q P) = (term261 _139146 _139147 _139148 q P).
Proof. exact (MK_COMB (@lem7568494 _139147) (@lem7568493 _139146 _139147 _139148 q P)). Qed.
Lemma lem7568496 {_139146 _139147 _139148 : Type'} (q : _139148) (P : type1517 _139146 _139147 _139148) : (term226 _139146 _139147 _139148 q P) = (term261 _139146 _139147 _139148 q P).
Proof. exact (TRANS (@lem7568468 _139146 _139147 _139148 q P) (@lem7568495 _139146 _139147 _139148 q P)). Qed.
Lemma lem7568497 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term228 _139146 _139147 _139148 P) = (term262 _139146 _139147 _139148 P).
Proof. exact (fun_ext (fun q : _139148 => @lem7568496 _139146 _139147 _139148 q P)). Qed.
Lemma lem7568498 {_139148 : Type'} : (@ex _139148) = (@ex _139148).
Proof. exact (eq_refl (@ex _139148)). Qed.
Lemma lem7568499 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term229 _139146 _139147 _139148 P) = (term263 _139146 _139147 _139148 P).
Proof. exact (MK_COMB (@lem7568498 _139148) (@lem7568497 _139146 _139147 _139148 P)). Qed.
Lemma lem7568500 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term162 _139146 _139147 _139148 P) = (term263 _139146 _139147 _139148 P).
Proof. exact (TRANS (@lem7568444 _139146 _139147 _139148 P) (@lem7568499 _139146 _139147 _139148 P)). Qed.
Lemma lem7568501 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term169 _139146 _139147 _139148 P) = (term264 _139146 _139147 _139148 P).
Proof. exact (MK_COMB (@lem7568420 _139146 _139147 _139148 P) (@lem7568500 _139146 _139147 _139148 P)). Qed.
Lemma lem7568505 {A : Type'} (P : A -> Prop) (Q : Prop) : (term265 A P Q) = (term266 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7568506 {_139147 : Type'} (P : _139147 -> Prop) (Q : Prop) : (term265 _139147 P Q) = (term266 _139147 P Q).
Proof. exact (@lem7568505 _139147 P Q). Qed.
Lemma lem7568507 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term267 _139146 _139147 _139148 P) = (term268 _139146 _139147 _139148 P).
Proof. exact (@lem7568506 _139147 (term210 _139146 _139147 _139148 P) (term263 _139146 _139147 _139148 P)). Qed.
Lemma lem7568508 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) : (term269 _139146 _139147 _139148 P m) = (term209 _139146 _139147 _139148 P m).
Proof. exact (eq_refl (term269 _139146 _139147 _139148 P m)). Qed.
Lemma lem7568509 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term270 _139146 _139147 _139148 P) = (term210 _139146 _139147 _139148 P).
Proof. exact (fun_ext (fun m : _139147 => @lem7568508 _139146 _139147 _139148 P m)). Qed.
Lemma lem7568510 {_139147 : Type'} : (@ex _139147) = (@ex _139147).
Proof. exact (eq_refl (@ex _139147)). Qed.
Lemma lem7568511 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term271 _139146 _139147 _139148 P) = (term211 _139146 _139147 _139148 P).
Proof. exact (MK_COMB (@lem7568510 _139147) (@lem7568509 _139146 _139147 _139148 P)). Qed.
Lemma lem7568512 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7568513 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term272 _139146 _139147 _139148 P) = (term212 _139146 _139147 _139148 P).
Proof. exact (MK_COMB (@lem7568512) (@lem7568511 _139146 _139147 _139148 P)). Qed.
Lemma lem7568514 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term263 _139146 _139147 _139148 P) = (term263 _139146 _139147 _139148 P).
Proof. exact (eq_refl (term263 _139146 _139147 _139148 P)). Qed.
Lemma lem7568515 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term267 _139146 _139147 _139148 P) = (term264 _139146 _139147 _139148 P).
Proof. exact (MK_COMB (@lem7568513 _139146 _139147 _139148 P) (@lem7568514 _139146 _139147 _139148 P)). Qed.
Lemma lem7568516 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7568517 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term273 _139146 _139147 _139148 P) = (term274 _139146 _139147 _139148 P).
Proof. exact (MK_COMB (@lem7568516) (@lem7568515 _139146 _139147 _139148 P)). Qed.
Lemma lem7568518 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) : (term269 _139146 _139147 _139148 P m) = (term209 _139146 _139147 _139148 P m).
Proof. exact (eq_refl (term269 _139146 _139147 _139148 P m)). Qed.
Lemma lem7568519 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7568520 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) : (term275 _139146 _139147 _139148 P m) = (term276 _139146 _139147 _139148 P m).
Proof. exact (MK_COMB (@lem7568519) (@lem7568518 _139146 _139147 _139148 P m)). Qed.
Lemma lem7568521 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term263 _139146 _139147 _139148 P) = (term263 _139146 _139147 _139148 P).
Proof. exact (eq_refl (term263 _139146 _139147 _139148 P)). Qed.
Lemma lem7568522 {_139146 _139147 _139148 : Type'} (m : _139147) (P : type1517 _139146 _139147 _139148) : (term277 _139146 _139147 _139148 m P) = (term278 _139146 _139147 _139148 m P).
Proof. exact (MK_COMB (@lem7568520 _139146 _139147 _139148 P m) (@lem7568521 _139146 _139147 _139148 P)). Qed.
Lemma lem7568523 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term279 _139146 _139147 _139148 P) = (term280 _139146 _139147 _139148 P).
Proof. exact (fun_ext (fun m : _139147 => @lem7568522 _139146 _139147 _139148 m P)). Qed.
Lemma lem7568524 {_139147 : Type'} : (@ex _139147) = (@ex _139147).
Proof. exact (eq_refl (@ex _139147)). Qed.
Lemma lem7568525 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term268 _139146 _139147 _139148 P) = (term281 _139146 _139147 _139148 P).
Proof. exact (MK_COMB (@lem7568524 _139147) (@lem7568523 _139146 _139147 _139148 P)). Qed.
Lemma lem7568526 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : ((term267 _139146 _139147 _139148 P) = (term268 _139146 _139147 _139148 P)) = ((term264 _139146 _139147 _139148 P) = (term281 _139146 _139147 _139148 P)).
Proof. exact (MK_COMB (@lem7568517 _139146 _139147 _139148 P) (@lem7568525 _139146 _139147 _139148 P)). Qed.
Lemma lem7568527 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term264 _139146 _139147 _139148 P) = (term281 _139146 _139147 _139148 P).
Proof. exact (EQ_MP (@lem7568526 _139146 _139147 _139148 P) (@lem7568507 _139146 _139147 _139148 P)). Qed.
Lemma lem7568531 {A : Type'} (P : A -> Prop) (Q : Prop) : (term265 A P Q) = (term266 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7568532 {_139146 : Type'} (P : _139146 -> Prop) (Q : Prop) : (term265 _139146 P Q) = (term266 _139146 P Q).
Proof. exact (@lem7568531 _139146 P Q). Qed.
Lemma lem7568533 {_139146 _139147 _139148 : Type'} (m : _139147) (P : type1517 _139146 _139147 _139148) : (term282 _139146 _139147 _139148 m P) = (term283 _139146 _139147 _139148 m P).
Proof. exact (@lem7568532 _139146 (term208 _139146 _139147 _139148 P m) (term263 _139146 _139147 _139148 P)). Qed.
Lemma lem7568534 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) (c : _139146) : (term284 _139146 _139147 _139148 P m c) = (term207 _139146 _139147 _139148 P m c).
Proof. exact (eq_refl (term284 _139146 _139147 _139148 P m c)). Qed.
Lemma lem7568535 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) : (term285 _139146 _139147 _139148 P m) = (term208 _139146 _139147 _139148 P m).
Proof. exact (fun_ext (fun c : _139146 => @lem7568534 _139146 _139147 _139148 P m c)). Qed.
Lemma lem7568536 {_139146 : Type'} : (@ex _139146) = (@ex _139146).
Proof. exact (eq_refl (@ex _139146)). Qed.
Lemma lem7568537 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) : (term286 _139146 _139147 _139148 P m) = (term209 _139146 _139147 _139148 P m).
Proof. exact (MK_COMB (@lem7568536 _139146) (@lem7568535 _139146 _139147 _139148 P m)). Qed.
Lemma lem7568538 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7568539 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) : (term287 _139146 _139147 _139148 P m) = (term276 _139146 _139147 _139148 P m).
Proof. exact (MK_COMB (@lem7568538) (@lem7568537 _139146 _139147 _139148 P m)). Qed.
Lemma lem7568540 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term263 _139146 _139147 _139148 P) = (term263 _139146 _139147 _139148 P).
Proof. exact (eq_refl (term263 _139146 _139147 _139148 P)). Qed.
Lemma lem7568541 {_139146 _139147 _139148 : Type'} (m : _139147) (P : type1517 _139146 _139147 _139148) : (term282 _139146 _139147 _139148 m P) = (term278 _139146 _139147 _139148 m P).
Proof. exact (MK_COMB (@lem7568539 _139146 _139147 _139148 P m) (@lem7568540 _139146 _139147 _139148 P)). Qed.
Lemma lem7568542 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7568543 {_139146 _139147 _139148 : Type'} (m : _139147) (P : type1517 _139146 _139147 _139148) : (term288 _139146 _139147 _139148 m P) = (term289 _139146 _139147 _139148 m P).
Proof. exact (MK_COMB (@lem7568542) (@lem7568541 _139146 _139147 _139148 m P)). Qed.
Lemma lem7568544 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) (c : _139146) : (term284 _139146 _139147 _139148 P m c) = (term207 _139146 _139147 _139148 P m c).
Proof. exact (eq_refl (term284 _139146 _139147 _139148 P m c)). Qed.
Lemma lem7568545 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7568546 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) (c : _139146) : (term290 _139146 _139147 _139148 P m c) = (term291 _139146 _139147 _139148 P m c).
Proof. exact (MK_COMB (@lem7568545) (@lem7568544 _139146 _139147 _139148 P m c)). Qed.
Lemma lem7568547 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term263 _139146 _139147 _139148 P) = (term263 _139146 _139147 _139148 P).
Proof. exact (eq_refl (term263 _139146 _139147 _139148 P)). Qed.
Lemma lem7568548 {_139146 _139147 _139148 : Type'} (m : _139147) (c : _139146) (P : type1517 _139146 _139147 _139148) : (term292 _139146 _139147 _139148 m c P) = (term293 _139146 _139147 _139148 m c P).
Proof. exact (MK_COMB (@lem7568546 _139146 _139147 _139148 P m c) (@lem7568547 _139146 _139147 _139148 P)). Qed.
Lemma lem7568549 {_139146 _139147 _139148 : Type'} (m : _139147) (P : type1517 _139146 _139147 _139148) : (term294 _139146 _139147 _139148 m P) = (term295 _139146 _139147 _139148 m P).
Proof. exact (fun_ext (fun c : _139146 => @lem7568548 _139146 _139147 _139148 m c P)). Qed.
Lemma lem7568550 {_139146 : Type'} : (@ex _139146) = (@ex _139146).
Proof. exact (eq_refl (@ex _139146)). Qed.
Lemma lem7568551 {_139146 _139147 _139148 : Type'} (m : _139147) (P : type1517 _139146 _139147 _139148) : (term283 _139146 _139147 _139148 m P) = (term296 _139146 _139147 _139148 m P).
Proof. exact (MK_COMB (@lem7568550 _139146) (@lem7568549 _139146 _139147 _139148 m P)). Qed.
Lemma lem7568552 {_139146 _139147 _139148 : Type'} (m : _139147) (P : type1517 _139146 _139147 _139148) : ((term282 _139146 _139147 _139148 m P) = (term283 _139146 _139147 _139148 m P)) = ((term278 _139146 _139147 _139148 m P) = (term296 _139146 _139147 _139148 m P)).
Proof. exact (MK_COMB (@lem7568543 _139146 _139147 _139148 m P) (@lem7568551 _139146 _139147 _139148 m P)). Qed.
Lemma lem7568553 {_139146 _139147 _139148 : Type'} (m : _139147) (P : type1517 _139146 _139147 _139148) : (term278 _139146 _139147 _139148 m P) = (term296 _139146 _139147 _139148 m P).
Proof. exact (EQ_MP (@lem7568552 _139146 _139147 _139148 m P) (@lem7568533 _139146 _139147 _139148 m P)). Qed.
Lemma lem7568555 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term297 A P Q) = (term298 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem7568556 {_139148 : Type'} (P : _139148 -> Prop) (Q : _139148 -> Prop) : (term297 _139148 P Q) = (term298 _139148 P Q).
Proof. exact (@lem7568555 _139148 P Q). Qed.
Lemma lem7568557 {_139146 _139147 _139148 : Type'} (m : _139147) (c : _139146) (P : type1517 _139146 _139147 _139148) : (term299 _139146 _139147 _139148 m c P) = (term300 _139146 _139147 _139148 m c P).
Proof. exact (@lem7568556 _139148 (term206 _139146 _139147 _139148 P m c) (term262 _139146 _139147 _139148 P)). Qed.
Lemma lem7568558 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) (c : _139146) : (term301 _139146 _139147 _139148 P m c q) = (term204 _139146 _139147 _139148 P q m c).
Proof. exact (eq_refl (term301 _139146 _139147 _139148 P m c q)). Qed.
Lemma lem7568559 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) (c : _139146) : (term302 _139146 _139147 _139148 P m c) = (term206 _139146 _139147 _139148 P m c).
Proof. exact (fun_ext (fun q : _139148 => @lem7568558 _139146 _139147 _139148 P q m c)). Qed.
Lemma lem7568560 {_139148 : Type'} : (@ex _139148) = (@ex _139148).
Proof. exact (eq_refl (@ex _139148)). Qed.
Lemma lem7568561 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) (c : _139146) : (term303 _139146 _139147 _139148 P m c) = (term207 _139146 _139147 _139148 P m c).
Proof. exact (MK_COMB (@lem7568560 _139148) (@lem7568559 _139146 _139147 _139148 P m c)). Qed.
Lemma lem7568562 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7568563 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) (c : _139146) : (term304 _139146 _139147 _139148 P m c) = (term291 _139146 _139147 _139148 P m c).
Proof. exact (MK_COMB (@lem7568562) (@lem7568561 _139146 _139147 _139148 P m c)). Qed.
Lemma lem7568564 {_139146 _139147 _139148 : Type'} (q : _139148) (P : type1517 _139146 _139147 _139148) : (term305 _139146 _139147 _139148 P q) = (term261 _139146 _139147 _139148 q P).
Proof. exact (eq_refl (term305 _139146 _139147 _139148 P q)). Qed.
Lemma lem7568565 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term306 _139146 _139147 _139148 P) = (term262 _139146 _139147 _139148 P).
Proof. exact (fun_ext (fun q : _139148 => @lem7568564 _139146 _139147 _139148 q P)). Qed.
Lemma lem7568566 {_139148 : Type'} : (@ex _139148) = (@ex _139148).
Proof. exact (eq_refl (@ex _139148)). Qed.
Lemma lem7568567 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term307 _139146 _139147 _139148 P) = (term263 _139146 _139147 _139148 P).
Proof. exact (MK_COMB (@lem7568566 _139148) (@lem7568565 _139146 _139147 _139148 P)). Qed.
Lemma lem7568568 {_139146 _139147 _139148 : Type'} (m : _139147) (c : _139146) (P : type1517 _139146 _139147 _139148) : (term299 _139146 _139147 _139148 m c P) = (term293 _139146 _139147 _139148 m c P).
Proof. exact (MK_COMB (@lem7568563 _139146 _139147 _139148 P m c) (@lem7568567 _139146 _139147 _139148 P)). Qed.
Lemma lem7568569 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7568570 {_139146 _139147 _139148 : Type'} (m : _139147) (c : _139146) (P : type1517 _139146 _139147 _139148) : (term308 _139146 _139147 _139148 m c P) = (term309 _139146 _139147 _139148 m c P).
Proof. exact (MK_COMB (@lem7568569) (@lem7568568 _139146 _139147 _139148 m c P)). Qed.
Lemma lem7568571 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) (c : _139146) : (term301 _139146 _139147 _139148 P m c q) = (term204 _139146 _139147 _139148 P q m c).
Proof. exact (eq_refl (term301 _139146 _139147 _139148 P m c q)). Qed.
Lemma lem7568572 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7568573 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) (c : _139146) : (term310 _139146 _139147 _139148 P m c q) = (term311 _139146 _139147 _139148 P q m c).
Proof. exact (MK_COMB (@lem7568572) (@lem7568571 _139146 _139147 _139148 P q m c)). Qed.
Lemma lem7568574 {_139146 _139147 _139148 : Type'} (q : _139148) (P : type1517 _139146 _139147 _139148) : (term305 _139146 _139147 _139148 P q) = (term261 _139146 _139147 _139148 q P).
Proof. exact (eq_refl (term305 _139146 _139147 _139148 P q)). Qed.
Lemma lem7568575 {_139146 _139147 _139148 : Type'} (m : _139147) (c : _139146) (q : _139148) (P : type1517 _139146 _139147 _139148) : (term312 _139146 _139147 _139148 m c P q) = (term313 _139146 _139147 _139148 m c q P).
Proof. exact (MK_COMB (@lem7568573 _139146 _139147 _139148 P q m c) (@lem7568574 _139146 _139147 _139148 q P)). Qed.
Lemma lem7568576 {_139146 _139147 _139148 : Type'} (m : _139147) (c : _139146) (P : type1517 _139146 _139147 _139148) : (term314 _139146 _139147 _139148 m c P) = (term315 _139146 _139147 _139148 m c P).
Proof. exact (fun_ext (fun q : _139148 => @lem7568575 _139146 _139147 _139148 m c q P)). Qed.
Lemma lem7568577 {_139148 : Type'} : (@ex _139148) = (@ex _139148).
Proof. exact (eq_refl (@ex _139148)). Qed.
Lemma lem7568578 {_139146 _139147 _139148 : Type'} (m : _139147) (c : _139146) (P : type1517 _139146 _139147 _139148) : (term300 _139146 _139147 _139148 m c P) = (term316 _139146 _139147 _139148 m c P).
Proof. exact (MK_COMB (@lem7568577 _139148) (@lem7568576 _139146 _139147 _139148 m c P)). Qed.
Lemma lem7568579 {_139146 _139147 _139148 : Type'} (m : _139147) (c : _139146) (P : type1517 _139146 _139147 _139148) : ((term299 _139146 _139147 _139148 m c P) = (term300 _139146 _139147 _139148 m c P)) = ((term293 _139146 _139147 _139148 m c P) = (term316 _139146 _139147 _139148 m c P)).
Proof. exact (MK_COMB (@lem7568570 _139146 _139147 _139148 m c P) (@lem7568578 _139146 _139147 _139148 m c P)). Qed.
Lemma lem7568580 {_139146 _139147 _139148 : Type'} (m : _139147) (c : _139146) (P : type1517 _139146 _139147 _139148) : (term293 _139146 _139147 _139148 m c P) = (term316 _139146 _139147 _139148 m c P).
Proof. exact (EQ_MP (@lem7568579 _139146 _139147 _139148 m c P) (@lem7568557 _139146 _139147 _139148 m c P)). Qed.
Lemma lem7568582 {A : Type'} (P : Prop) (Q : A -> Prop) : (term317 A P Q) = (term318 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7568583 {_139147 : Type'} (P : Prop) (Q : _139147 -> Prop) : (term317 _139147 P Q) = (term318 _139147 P Q).
Proof. exact (@lem7568582 _139147 P Q). Qed.
Lemma lem7568584 {_139146 _139147 _139148 : Type'} (m : _139147) (c : _139146) (q : _139148) (P : type1517 _139146 _139147 _139148) : (term319 _139146 _139147 _139148 m c q P) = (term320 _139146 _139147 _139148 m c q P).
Proof. exact (@lem7568583 _139147 (term204 _139146 _139147 _139148 P q m c) (term260 _139146 _139147 _139148 q P)). Qed.
Lemma lem7568585 {_139146 _139147 _139148 : Type'} (q : _139148) (m : _139147) (P : type1517 _139146 _139147 _139148) : (term321 _139146 _139147 _139148 q P m) = (term259 _139146 _139147 _139148 q m P).
Proof. exact (eq_refl (term321 _139146 _139147 _139148 q P m)). Qed.
Lemma lem7568586 {_139146 _139147 _139148 : Type'} (q : _139148) (P : type1517 _139146 _139147 _139148) : (term322 _139146 _139147 _139148 q P) = (term260 _139146 _139147 _139148 q P).
Proof. exact (fun_ext (fun m : _139147 => @lem7568585 _139146 _139147 _139148 q m P)). Qed.
Lemma lem7568587 {_139147 : Type'} : (@ex _139147) = (@ex _139147).
Proof. exact (eq_refl (@ex _139147)). Qed.
Lemma lem7568588 {_139146 _139147 _139148 : Type'} (q : _139148) (P : type1517 _139146 _139147 _139148) : (term323 _139146 _139147 _139148 q P) = (term261 _139146 _139147 _139148 q P).
Proof. exact (MK_COMB (@lem7568587 _139147) (@lem7568586 _139146 _139147 _139148 q P)). Qed.
Lemma lem7568589 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) (c : _139146) : (term311 _139146 _139147 _139148 P q m c) = (term311 _139146 _139147 _139148 P q m c).
Proof. exact (eq_refl (term311 _139146 _139147 _139148 P q m c)). Qed.
Lemma lem7568590 {_139146 _139147 _139148 : Type'} (m : _139147) (c : _139146) (q : _139148) (P : type1517 _139146 _139147 _139148) : (term319 _139146 _139147 _139148 m c q P) = (term313 _139146 _139147 _139148 m c q P).
Proof. exact (MK_COMB (@lem7568589 _139146 _139147 _139148 P q m c) (@lem7568588 _139146 _139147 _139148 q P)). Qed.
Lemma lem7568591 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7568592 {_139146 _139147 _139148 : Type'} (m : _139147) (c : _139146) (q : _139148) (P : type1517 _139146 _139147 _139148) : (term324 _139146 _139147 _139148 m c q P) = (term325 _139146 _139147 _139148 m c q P).
Proof. exact (MK_COMB (@lem7568591) (@lem7568590 _139146 _139147 _139148 m c q P)). Qed.
Lemma lem7568593 {_139146 _139147 _139148 : Type'} (q : _139148) (m' : _139147) (P : type1517 _139146 _139147 _139148) : (term321 _139146 _139147 _139148 q P m') = (term259 _139146 _139147 _139148 q m' P).
Proof. exact (eq_refl (term321 _139146 _139147 _139148 q P m')). Qed.
Lemma lem7568594 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) (c : _139146) : (term311 _139146 _139147 _139148 P q m c) = (term311 _139146 _139147 _139148 P q m c).
Proof. exact (eq_refl (term311 _139146 _139147 _139148 P q m c)). Qed.
Lemma lem7568595 {_139146 _139147 _139148 : Type'} (m : _139147) (c : _139146) (q : _139148) (m' : _139147) (P : type1517 _139146 _139147 _139148) : (term326 _139146 _139147 _139148 m c q P m') = (term327 _139146 _139147 _139148 m c q m' P).
Proof. exact (MK_COMB (@lem7568594 _139146 _139147 _139148 P q m c) (@lem7568593 _139146 _139147 _139148 q m' P)). Qed.
Lemma lem7568596 {_139146 _139147 _139148 : Type'} (m : _139147) (c : _139146) (q : _139148) (P : type1517 _139146 _139147 _139148) : (term328 _139146 _139147 _139148 m c q P) = (term329 _139146 _139147 _139148 m c q P).
Proof. exact (fun_ext (fun m' : _139147 => @lem7568595 _139146 _139147 _139148 m c q m' P)). Qed.
Lemma lem7568597 {_139147 : Type'} : (@ex _139147) = (@ex _139147).
Proof. exact (eq_refl (@ex _139147)). Qed.
Lemma lem7568598 {_139146 _139147 _139148 : Type'} (m : _139147) (c : _139146) (q : _139148) (P : type1517 _139146 _139147 _139148) : (term320 _139146 _139147 _139148 m c q P) = (term330 _139146 _139147 _139148 m c q P).
Proof. exact (MK_COMB (@lem7568597 _139147) (@lem7568596 _139146 _139147 _139148 m c q P)). Qed.
Lemma lem7568599 {_139146 _139147 _139148 : Type'} (m : _139147) (c : _139146) (q : _139148) (P : type1517 _139146 _139147 _139148) : ((term319 _139146 _139147 _139148 m c q P) = (term320 _139146 _139147 _139148 m c q P)) = ((term313 _139146 _139147 _139148 m c q P) = (term330 _139146 _139147 _139148 m c q P)).
Proof. exact (MK_COMB (@lem7568592 _139146 _139147 _139148 m c q P) (@lem7568598 _139146 _139147 _139148 m c q P)). Qed.
Lemma lem7568600 {_139146 _139147 _139148 : Type'} (m : _139147) (c : _139146) (q : _139148) (P : type1517 _139146 _139147 _139148) : (term313 _139146 _139147 _139148 m c q P) = (term330 _139146 _139147 _139148 m c q P).
Proof. exact (EQ_MP (@lem7568599 _139146 _139147 _139148 m c q P) (@lem7568584 _139146 _139147 _139148 m c q P)). Qed.
Lemma lem7568602 {A : Type'} (P : Prop) (Q : A -> Prop) : (term317 A P Q) = (term318 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7568603 {_139146 : Type'} (P : Prop) (Q : _139146 -> Prop) : (term317 _139146 P Q) = (term318 _139146 P Q).
Proof. exact (@lem7568602 _139146 P Q). Qed.
Lemma lem7568604 {_139146 _139147 _139148 : Type'} (m : _139147) (c : _139146) (q : _139148) (m' : _139147) (P : type1517 _139146 _139147 _139148) : (term331 _139146 _139147 _139148 m c q m' P) = (term332 _139146 _139147 _139148 m c q m' P).
Proof. exact (@lem7568603 _139146 (term204 _139146 _139147 _139148 P q m c) (term258 _139146 _139147 _139148 q m' P)). Qed.
Lemma lem7568605 {_139146 _139147 _139148 : Type'} (q : _139148) (m' : _139147) (c : _139146) (P : type1517 _139146 _139147 _139148) : (term333 _139146 _139147 _139148 q m' P c) = (term256 _139146 _139147 _139148 q m' c P).
Proof. exact (eq_refl (term333 _139146 _139147 _139148 q m' P c)). Qed.
Lemma lem7568606 {_139146 _139147 _139148 : Type'} (q : _139148) (m' : _139147) (P : type1517 _139146 _139147 _139148) : (term334 _139146 _139147 _139148 q m' P) = (term258 _139146 _139147 _139148 q m' P).
Proof. exact (fun_ext (fun c : _139146 => @lem7568605 _139146 _139147 _139148 q m' c P)). Qed.
Lemma lem7568607 {_139146 : Type'} : (@ex _139146) = (@ex _139146).
Proof. exact (eq_refl (@ex _139146)). Qed.
Lemma lem7568608 {_139146 _139147 _139148 : Type'} (q : _139148) (m' : _139147) (P : type1517 _139146 _139147 _139148) : (term335 _139146 _139147 _139148 q m' P) = (term259 _139146 _139147 _139148 q m' P).
Proof. exact (MK_COMB (@lem7568607 _139146) (@lem7568606 _139146 _139147 _139148 q m' P)). Qed.
Lemma lem7568609 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) (c : _139146) : (term311 _139146 _139147 _139148 P q m c) = (term311 _139146 _139147 _139148 P q m c).
Proof. exact (eq_refl (term311 _139146 _139147 _139148 P q m c)). Qed.
Lemma lem7568610 {_139146 _139147 _139148 : Type'} (m : _139147) (c : _139146) (q : _139148) (m' : _139147) (P : type1517 _139146 _139147 _139148) : (term331 _139146 _139147 _139148 m c q m' P) = (term327 _139146 _139147 _139148 m c q m' P).
Proof. exact (MK_COMB (@lem7568609 _139146 _139147 _139148 P q m c) (@lem7568608 _139146 _139147 _139148 q m' P)). Qed.
Lemma lem7568611 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7568612 {_139146 _139147 _139148 : Type'} (m : _139147) (c : _139146) (q : _139148) (m' : _139147) (P : type1517 _139146 _139147 _139148) : (term336 _139146 _139147 _139148 m c q m' P) = (term337 _139146 _139147 _139148 m c q m' P).
Proof. exact (MK_COMB (@lem7568611) (@lem7568610 _139146 _139147 _139148 m c q m' P)). Qed.
Lemma lem7568613 {_139146 _139147 _139148 : Type'} (q : _139148) (m' : _139147) (c' : _139146) (P : type1517 _139146 _139147 _139148) : (term333 _139146 _139147 _139148 q m' P c') = (term256 _139146 _139147 _139148 q m' c' P).
Proof. exact (eq_refl (term333 _139146 _139147 _139148 q m' P c')). Qed.
Lemma lem7568614 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) (c : _139146) : (term311 _139146 _139147 _139148 P q m c) = (term311 _139146 _139147 _139148 P q m c).
Proof. exact (eq_refl (term311 _139146 _139147 _139148 P q m c)). Qed.
Lemma lem7568615 {_139146 _139147 _139148 : Type'} (m : _139147) (c : _139146) (q : _139148) (m' : _139147) (c' : _139146) (P : type1517 _139146 _139147 _139148) : (term338 _139146 _139147 _139148 m c q m' P c') = (term339 _139146 _139147 _139148 m c q m' c' P).
Proof. exact (MK_COMB (@lem7568614 _139146 _139147 _139148 P q m c) (@lem7568613 _139146 _139147 _139148 q m' c' P)). Qed.
Lemma lem7568616 {_139146 _139147 _139148 : Type'} (m : _139147) (c : _139146) (q : _139148) (m' : _139147) (P : type1517 _139146 _139147 _139148) : (term340 _139146 _139147 _139148 m c q m' P) = (term341 _139146 _139147 _139148 m c q m' P).
Proof. exact (fun_ext (fun c' : _139146 => @lem7568615 _139146 _139147 _139148 m c q m' c' P)). Qed.
Lemma lem7568617 {_139146 : Type'} : (@ex _139146) = (@ex _139146).
Proof. exact (eq_refl (@ex _139146)). Qed.
Lemma lem7568618 {_139146 _139147 _139148 : Type'} (m : _139147) (c : _139146) (q : _139148) (m' : _139147) (P : type1517 _139146 _139147 _139148) : (term332 _139146 _139147 _139148 m c q m' P) = (term342 _139146 _139147 _139148 m c q m' P).
Proof. exact (MK_COMB (@lem7568617 _139146) (@lem7568616 _139146 _139147 _139148 m c q m' P)). Qed.
Lemma lem7568619 {_139146 _139147 _139148 : Type'} (m : _139147) (c : _139146) (q : _139148) (m' : _139147) (P : type1517 _139146 _139147 _139148) : ((term331 _139146 _139147 _139148 m c q m' P) = (term332 _139146 _139147 _139148 m c q m' P)) = ((term327 _139146 _139147 _139148 m c q m' P) = (term342 _139146 _139147 _139148 m c q m' P)).
Proof. exact (MK_COMB (@lem7568612 _139146 _139147 _139148 m c q m' P) (@lem7568618 _139146 _139147 _139148 m c q m' P)). Qed.
Lemma lem7568620 {_139146 _139147 _139148 : Type'} (m : _139147) (c : _139146) (q : _139148) (m' : _139147) (P : type1517 _139146 _139147 _139148) : (term327 _139146 _139147 _139148 m c q m' P) = (term342 _139146 _139147 _139148 m c q m' P).
Proof. exact (EQ_MP (@lem7568619 _139146 _139147 _139148 m c q m' P) (@lem7568604 _139146 _139147 _139148 m c q m' P)). Qed.
Lemma lem7568621 {_139146 _139147 _139148 : Type'} (m : _139147) (c : _139146) (q : _139148) (P : type1517 _139146 _139147 _139148) : (term329 _139146 _139147 _139148 m c q P) = (term343 _139146 _139147 _139148 m c q P).
Proof. exact (fun_ext (fun m' : _139147 => @lem7568620 _139146 _139147 _139148 m c q m' P)). Qed.
Lemma lem7568622 {_139147 : Type'} : (@ex _139147) = (@ex _139147).
Proof. exact (eq_refl (@ex _139147)). Qed.
Lemma lem7568623 {_139146 _139147 _139148 : Type'} (m : _139147) (c : _139146) (q : _139148) (P : type1517 _139146 _139147 _139148) : (term330 _139146 _139147 _139148 m c q P) = (term344 _139146 _139147 _139148 m c q P).
Proof. exact (MK_COMB (@lem7568622 _139147) (@lem7568621 _139146 _139147 _139148 m c q P)). Qed.
Lemma lem7568624 {_139146 _139147 _139148 : Type'} (m : _139147) (c : _139146) (q : _139148) (P : type1517 _139146 _139147 _139148) : (term313 _139146 _139147 _139148 m c q P) = (term344 _139146 _139147 _139148 m c q P).
Proof. exact (TRANS (@lem7568600 _139146 _139147 _139148 m c q P) (@lem7568623 _139146 _139147 _139148 m c q P)). Qed.
Lemma lem7568625 {_139146 _139147 _139148 : Type'} (m : _139147) (c : _139146) (P : type1517 _139146 _139147 _139148) : (term315 _139146 _139147 _139148 m c P) = (term345 _139146 _139147 _139148 m c P).
Proof. exact (fun_ext (fun q : _139148 => @lem7568624 _139146 _139147 _139148 m c q P)). Qed.
Lemma lem7568626 {_139148 : Type'} : (@ex _139148) = (@ex _139148).
Proof. exact (eq_refl (@ex _139148)). Qed.
Lemma lem7568627 {_139146 _139147 _139148 : Type'} (m : _139147) (c : _139146) (P : type1517 _139146 _139147 _139148) : (term316 _139146 _139147 _139148 m c P) = (term346 _139146 _139147 _139148 m c P).
Proof. exact (MK_COMB (@lem7568626 _139148) (@lem7568625 _139146 _139147 _139148 m c P)). Qed.
Lemma lem7568628 {_139146 _139147 _139148 : Type'} (m : _139147) (c : _139146) (P : type1517 _139146 _139147 _139148) : (term293 _139146 _139147 _139148 m c P) = (term346 _139146 _139147 _139148 m c P).
Proof. exact (TRANS (@lem7568580 _139146 _139147 _139148 m c P) (@lem7568627 _139146 _139147 _139148 m c P)). Qed.
Lemma lem7568629 {_139146 _139147 _139148 : Type'} (m : _139147) (P : type1517 _139146 _139147 _139148) : (term295 _139146 _139147 _139148 m P) = (term347 _139146 _139147 _139148 m P).
Proof. exact (fun_ext (fun c : _139146 => @lem7568628 _139146 _139147 _139148 m c P)). Qed.
Lemma lem7568630 {_139146 : Type'} : (@ex _139146) = (@ex _139146).
Proof. exact (eq_refl (@ex _139146)). Qed.
Lemma lem7568631 {_139146 _139147 _139148 : Type'} (m : _139147) (P : type1517 _139146 _139147 _139148) : (term296 _139146 _139147 _139148 m P) = (term348 _139146 _139147 _139148 m P).
Proof. exact (MK_COMB (@lem7568630 _139146) (@lem7568629 _139146 _139147 _139148 m P)). Qed.
Lemma lem7568632 {_139146 _139147 _139148 : Type'} (m : _139147) (P : type1517 _139146 _139147 _139148) : (term278 _139146 _139147 _139148 m P) = (term348 _139146 _139147 _139148 m P).
Proof. exact (TRANS (@lem7568553 _139146 _139147 _139148 m P) (@lem7568631 _139146 _139147 _139148 m P)). Qed.
Lemma lem7568633 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term280 _139146 _139147 _139148 P) = (term349 _139146 _139147 _139148 P).
Proof. exact (fun_ext (fun m : _139147 => @lem7568632 _139146 _139147 _139148 m P)). Qed.
Lemma lem7568634 {_139147 : Type'} : (@ex _139147) = (@ex _139147).
Proof. exact (eq_refl (@ex _139147)). Qed.
Lemma lem7568635 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term281 _139146 _139147 _139148 P) = (term350 _139146 _139147 _139148 P).
Proof. exact (MK_COMB (@lem7568634 _139147) (@lem7568633 _139146 _139147 _139148 P)). Qed.
Lemma lem7568636 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term264 _139146 _139147 _139148 P) = (term350 _139146 _139147 _139148 P).
Proof. exact (TRANS (@lem7568527 _139146 _139147 _139148 P) (@lem7568635 _139146 _139147 _139148 P)). Qed.
Lemma lem7568638 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term169 _139146 _139147 _139148 P) = (term350 _139146 _139147 _139148 P).
Proof. exact (TRANS (@lem7568501 _139146 _139147 _139148 P) (@lem7568636 _139146 _139147 _139148 P)). Qed.
Lemma lem7568639 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term93 _139146 _139147 _139148 P) = (term350 _139146 _139147 _139148 P).
Proof. exact (TRANS (@lem7568301 _139146 _139147 _139148 P) (@lem7568638 _139146 _139147 _139148 P)). Qed.
Lemma lem7568640 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (h1 : term93 _139146 _139147 _139148 P) : term350 _139146 _139147 _139148 P.
Proof. exact (EQ_MP (@lem7568639 _139146 _139147 _139148 P) (@lem7568208 _139146 _139147 _139148 P h1)). Qed.
Lemma lem7568641 {_139146 _139147 _139148 : Type'} (m : _139147) (P : type1517 _139146 _139147 _139148) (h1 : term348 _139146 _139147 _139148 m P) : term348 _139146 _139147 _139148 m P.
Proof. exact (h1). Qed.
Lemma lem7568642 {_139146 _139147 _139148 : Type'} (m : _139147) (c : _139146) (P : type1517 _139146 _139147 _139148) (h1 : term346 _139146 _139147 _139148 m c P) : term346 _139146 _139147 _139148 m c P.
Proof. exact (h1). Qed.
Lemma lem7568643 {_139146 _139147 _139148 : Type'} (m : _139147) (c : _139146) (q : _139148) (P : type1517 _139146 _139147 _139148) (h1 : term344 _139146 _139147 _139148 m c q P) : term344 _139146 _139147 _139148 m c q P.
Proof. exact (h1). Qed.
Lemma lem7568644 {_139146 _139147 _139148 : Type'} (m : _139147) (c : _139146) (q : _139148) (m' : _139147) (P : type1517 _139146 _139147 _139148) (h1 : term342 _139146 _139147 _139148 m c q m' P) : term342 _139146 _139147 _139148 m c q m' P.
Proof. exact (h1). Qed.
Lemma lem7568645 {_139146 _139147 _139148 : Type'} (m : _139147) (c : _139146) (q : _139148) (m' : _139147) (c' : _139146) (P : type1517 _139146 _139147 _139148) (h1 : term339 _139146 _139147 _139148 m c q m' c' P) : term339 _139146 _139147 _139148 m c q m' c' P.
Proof. exact (h1). Qed.
Lemma lem7568652 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) (c : _139146) : (P q m c) = (P q m c).
Proof. exact (eq_refl (P q m c)). Qed.
Lemma lem7568653 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) (c : _139146) : (term103 _139146 _139147 _139148 P m c) = (term103 _139146 _139147 _139148 P m c).
Proof. exact (fun_ext (fun q : _139148 => @lem7568652 _139146 _139147 _139148 P q m c)). Qed.
Lemma lem7568654 {_139148 : Type'} : (@all _139148) = (@all _139148).
Proof. exact (eq_refl (@all _139148)). Qed.
Lemma lem7568655 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) (c : _139146) : (term104 _139146 _139147 _139148 P m c) = (term104 _139146 _139147 _139148 P m c).
Proof. exact (MK_COMB (@lem7568654 _139148) (@lem7568653 _139146 _139147 _139148 P m c)). Qed.
Lemma lem7568656 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) : (term105 _139146 _139147 _139148 P m) = (term105 _139146 _139147 _139148 P m).
Proof. exact (fun_ext (fun c : _139146 => @lem7568655 _139146 _139147 _139148 P m c)). Qed.
Lemma lem7568657 {_139146 : Type'} : (@all _139146) = (@all _139146).
Proof. exact (eq_refl (@all _139146)). Qed.
Lemma lem7568658 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) : (term106 _139146 _139147 _139148 P m) = (term106 _139146 _139147 _139148 P m).
Proof. exact (MK_COMB (@lem7568657 _139146) (@lem7568656 _139146 _139147 _139148 P m)). Qed.
Lemma lem7568659 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term107 _139146 _139147 _139148 P) = (term107 _139146 _139147 _139148 P).
Proof. exact (fun_ext (fun m : _139147 => @lem7568658 _139146 _139147 _139148 P m)). Qed.
Lemma lem7568660 {_139147 : Type'} : (@all _139147) = (@all _139147).
Proof. exact (eq_refl (@all _139147)). Qed.
Lemma lem7568661 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term91 _139146 _139147 _139148 P) = (term91 _139146 _139147 _139148 P).
Proof. exact (MK_COMB (@lem7568660 _139147) (@lem7568659 _139146 _139147 _139148 P)). Qed.
Lemma lem7568672 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m' : _139147) (c' : _139146) : (term254 _139146 _139147 _139148 P q m' c') = (term254 _139146 _139147 _139148 P q m' c').
Proof. exact (eq_refl (term254 _139146 _139147 _139148 P q m' c')). Qed.
Lemma lem7568673 {_139146 _139147 _139148 : Type'} (q : _139148) (m' : _139147) (c' : _139146) (P : type1517 _139146 _139147 _139148) : (term256 _139146 _139147 _139148 q m' c' P) = (term256 _139146 _139147 _139148 q m' c' P).
Proof. exact (MK_COMB (@lem7568672 _139146 _139147 _139148 P q m' c') (@lem7568661 _139146 _139147 _139148 P)). Qed.
Lemma lem7568682 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) (c : _139146) : (term120 _139146 _139147 _139148 P q m c) = (term120 _139146 _139147 _139148 P q m c).
Proof. exact (eq_refl (term120 _139146 _139147 _139148 P q m c)). Qed.
Lemma lem7568689 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) (c : _139146) : (P q m c) = (P q m c).
Proof. exact (eq_refl (P q m c)). Qed.
Lemma lem7568690 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) : (term108 _139146 _139147 _139148 P q m) = (term108 _139146 _139147 _139148 P q m).
Proof. exact (fun_ext (fun c : _139146 => @lem7568689 _139146 _139147 _139148 P q m c)). Qed.
Lemma lem7568691 {_139146 : Type'} : (@all _139146) = (@all _139146).
Proof. exact (eq_refl (@all _139146)). Qed.
Lemma lem7568692 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) : (term109 _139146 _139147 _139148 P q m) = (term109 _139146 _139147 _139148 P q m).
Proof. exact (MK_COMB (@lem7568691 _139146) (@lem7568690 _139146 _139147 _139148 P q m)). Qed.
Lemma lem7568693 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) : (term110 _139146 _139147 _139148 P q) = (term110 _139146 _139147 _139148 P q).
Proof. exact (fun_ext (fun m : _139147 => @lem7568692 _139146 _139147 _139148 P q m)). Qed.
Lemma lem7568694 {_139147 : Type'} : (@all _139147) = (@all _139147).
Proof. exact (eq_refl (@all _139147)). Qed.
Lemma lem7568695 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) : (term111 _139146 _139147 _139148 P q) = (term111 _139146 _139147 _139148 P q).
Proof. exact (MK_COMB (@lem7568694 _139147) (@lem7568693 _139146 _139147 _139148 P q)). Qed.
Lemma lem7568696 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term112 _139146 _139147 _139148 P) = (term112 _139146 _139147 _139148 P).
Proof. exact (fun_ext (fun q : _139148 => @lem7568695 _139146 _139147 _139148 P q)). Qed.
Lemma lem7568697 {_139148 : Type'} : (@all _139148) = (@all _139148).
Proof. exact (eq_refl (@all _139148)). Qed.
Lemma lem7568698 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term90 _139146 _139147 _139148 P) = (term90 _139146 _139147 _139148 P).
Proof. exact (MK_COMB (@lem7568697 _139148) (@lem7568696 _139146 _139147 _139148 P)). Qed.
Lemma lem7568699 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7568700 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term163 _139146 _139147 _139148 P) = (term163 _139146 _139147 _139148 P).
Proof. exact (MK_COMB (@lem7568699) (@lem7568698 _139146 _139147 _139148 P)). Qed.
Lemma lem7568701 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) (c : _139146) : (term204 _139146 _139147 _139148 P q m c) = (term204 _139146 _139147 _139148 P q m c).
Proof. exact (MK_COMB (@lem7568700 _139146 _139147 _139148 P) (@lem7568682 _139146 _139147 _139148 P q m c)). Qed.
Lemma lem7568702 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7568703 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) (c : _139146) : (term311 _139146 _139147 _139148 P q m c) = (term311 _139146 _139147 _139148 P q m c).
Proof. exact (MK_COMB (@lem7568702) (@lem7568701 _139146 _139147 _139148 P q m c)). Qed.
Lemma lem7568704 {_139146 _139147 _139148 : Type'} (m : _139147) (c : _139146) (q : _139148) (m' : _139147) (c' : _139146) (P : type1517 _139146 _139147 _139148) : (term339 _139146 _139147 _139148 m c q m' c' P) = (term339 _139146 _139147 _139148 m c q m' c' P).
Proof. exact (MK_COMB (@lem7568703 _139146 _139147 _139148 P q m c) (@lem7568673 _139146 _139147 _139148 q m' c' P)). Qed.
Lemma lem7568705 {_139146 _139147 _139148 : Type'} (m : _139147) (c : _139146) (q : _139148) (m' : _139147) (c' : _139146) (P : type1517 _139146 _139147 _139148) (h1 : term339 _139146 _139147 _139148 m c q m' c' P) : term339 _139146 _139147 _139148 m c q m' c' P.
Proof. exact (EQ_MP (@lem7568704 _139146 _139147 _139148 m c q m' c' P) (@lem7568645 _139146 _139147 _139148 m c q m' c' P h1)). Qed.
Lemma lem7568706 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) (c : _139146) (h1 : term204 _139146 _139147 _139148 P q m c) : term204 _139146 _139147 _139148 P q m c.
Proof. exact (h1). Qed.
Lemma lem7568707 {_139146 _139147 _139148 : Type'} (q : _139148) (m' : _139147) (c' : _139146) (P : type1517 _139146 _139147 _139148) (h1 : term256 _139146 _139147 _139148 q m' c' P) : term256 _139146 _139147 _139148 q m' c' P.
Proof. exact (h1). Qed.
Lemma lem7568709 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) (c : _139146) (h1 : term204 _139146 _139147 _139148 P q m c) : term90 _139146 _139147 _139148 P.
Proof. exact (proj1 (@lem7568706 _139146 _139147 _139148 P q m c h1)). Qed.
Lemma lem7568710 {_139146 _139147 _139148 : Type'} (q : _139148) (m' : _139147) (c' : _139146) (P : type1517 _139146 _139147 _139148) (h1 : term256 _139146 _139147 _139148 q m' c' P) : term91 _139146 _139147 _139148 P.
Proof. exact (proj2 (@lem7568707 _139146 _139147 _139148 q m' c' P h1)). Qed.
Lemma lem7568713 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) (c : _139146) : (P q m c) = (P q m c).
Proof. exact (eq_refl (P q m c)). Qed.
Lemma lem7568714 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) : (term108 _139146 _139147 _139148 P q m) = (term108 _139146 _139147 _139148 P q m).
Proof. exact (fun_ext (fun c : _139146 => @lem7568713 _139146 _139147 _139148 P q m c)). Qed.
Lemma lem7568715 {_139146 : Type'} : (@all _139146) = (@all _139146).
Proof. exact (eq_refl (@all _139146)). Qed.
Lemma lem7568716 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) : (term109 _139146 _139147 _139148 P q m) = (term109 _139146 _139147 _139148 P q m).
Proof. exact (MK_COMB (@lem7568715 _139146) (@lem7568714 _139146 _139147 _139148 P q m)). Qed.
Lemma lem7568717 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) : (term110 _139146 _139147 _139148 P q) = (term110 _139146 _139147 _139148 P q).
Proof. exact (fun_ext (fun m : _139147 => @lem7568716 _139146 _139147 _139148 P q m)). Qed.
Lemma lem7568718 {_139147 : Type'} : (@all _139147) = (@all _139147).
Proof. exact (eq_refl (@all _139147)). Qed.
Lemma lem7568719 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) : (term111 _139146 _139147 _139148 P q) = (term111 _139146 _139147 _139148 P q).
Proof. exact (MK_COMB (@lem7568718 _139147) (@lem7568717 _139146 _139147 _139148 P q)). Qed.
Lemma lem7568720 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term112 _139146 _139147 _139148 P) = (term112 _139146 _139147 _139148 P).
Proof. exact (fun_ext (fun q : _139148 => @lem7568719 _139146 _139147 _139148 P q)). Qed.
Lemma lem7568721 {_139148 : Type'} : (@all _139148) = (@all _139148).
Proof. exact (eq_refl (@all _139148)). Qed.
Lemma lem7568723 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term90 _139146 _139147 _139148 P) = (term90 _139146 _139147 _139148 P).
Proof. exact (MK_COMB (@lem7568721 _139148) (@lem7568720 _139146 _139147 _139148 P)). Qed.
Lemma lem7568724 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) (c : _139146) (h1 : term204 _139146 _139147 _139148 P q m c) : term90 _139146 _139147 _139148 P.
Proof. exact (EQ_MP (@lem7568723 _139146 _139147 _139148 P) (@lem7568709 _139146 _139147 _139148 P q m c h1)). Qed.
Lemma lem7568734 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) (c : _139146) : (P q m c) = (P q m c).
Proof. exact (eq_refl (P q m c)). Qed.
Lemma lem7568735 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) (c : _139146) : (term103 _139146 _139147 _139148 P m c) = (term103 _139146 _139147 _139148 P m c).
Proof. exact (fun_ext (fun q : _139148 => @lem7568734 _139146 _139147 _139148 P q m c)). Qed.
Lemma lem7568736 {_139148 : Type'} : (@all _139148) = (@all _139148).
Proof. exact (eq_refl (@all _139148)). Qed.
Lemma lem7568737 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) (c : _139146) : (term104 _139146 _139147 _139148 P m c) = (term104 _139146 _139147 _139148 P m c).
Proof. exact (MK_COMB (@lem7568736 _139148) (@lem7568735 _139146 _139147 _139148 P m c)). Qed.
Lemma lem7568738 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) : (term105 _139146 _139147 _139148 P m) = (term105 _139146 _139147 _139148 P m).
Proof. exact (fun_ext (fun c : _139146 => @lem7568737 _139146 _139147 _139148 P m c)). Qed.
Lemma lem7568739 {_139146 : Type'} : (@all _139146) = (@all _139146).
Proof. exact (eq_refl (@all _139146)). Qed.
Lemma lem7568740 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (m : _139147) : (term106 _139146 _139147 _139148 P m) = (term106 _139146 _139147 _139148 P m).
Proof. exact (MK_COMB (@lem7568739 _139146) (@lem7568738 _139146 _139147 _139148 P m)). Qed.
Lemma lem7568741 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term107 _139146 _139147 _139148 P) = (term107 _139146 _139147 _139148 P).
Proof. exact (fun_ext (fun m : _139147 => @lem7568740 _139146 _139147 _139148 P m)). Qed.
Lemma lem7568742 {_139147 : Type'} : (@all _139147) = (@all _139147).
Proof. exact (eq_refl (@all _139147)). Qed.
Lemma lem7568744 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term91 _139146 _139147 _139148 P) = (term91 _139146 _139147 _139148 P).
Proof. exact (MK_COMB (@lem7568742 _139147) (@lem7568741 _139146 _139147 _139148 P)). Qed.
Lemma lem7568745 {_139146 _139147 _139148 : Type'} (q : _139148) (m' : _139147) (c' : _139146) (P : type1517 _139146 _139147 _139148) (h1 : term256 _139146 _139147 _139148 q m' c' P) : term91 _139146 _139147 _139148 P.
Proof. exact (EQ_MP (@lem7568744 _139146 _139147 _139148 P) (@lem7568710 _139146 _139147 _139148 q m' c' P h1)). Qed.
Lemma lem7568746 {_139146 _139147 _139148 : Type'} (_97579 : _139148) (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) (c : _139146) (h1 : term204 _139146 _139147 _139148 P q m c) : term133 _139146 _139147 _139148 P _97579.
Proof. exact (@lem7568724 _139146 _139147 _139148 P q m c h1 _97579). Qed.
Lemma lem7568747 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (_97579 : _139148) : (term133 _139146 _139147 _139148 P _97579) = (term111 _139146 _139147 _139148 P _97579).
Proof. exact (eq_refl (term133 _139146 _139147 _139148 P _97579)). Qed.
Lemma lem7568748 {_139146 _139147 _139148 : Type'} (_97579 : _139148) (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) (c : _139146) (h1 : term204 _139146 _139147 _139148 P q m c) : term111 _139146 _139147 _139148 P _97579.
Proof. exact (EQ_MP (@lem7568747 _139146 _139147 _139148 P _97579) (@lem7568746 _139146 _139147 _139148 _97579 P q m c h1)). Qed.
Lemma lem7568749 {_139146 _139147 _139148 : Type'} (_97579 : _139148) (_97580 : _139147) (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) (c : _139146) (h1 : term204 _139146 _139147 _139148 P q m c) : term126 _139146 _139147 _139148 P _97579 _97580.
Proof. exact (@lem7568748 _139146 _139147 _139148 _97579 P q m c h1 _97580). Qed.
Lemma lem7568750 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (_97579 : _139148) (_97580 : _139147) : (term126 _139146 _139147 _139148 P _97579 _97580) = (term109 _139146 _139147 _139148 P _97579 _97580).
Proof. exact (eq_refl (term126 _139146 _139147 _139148 P _97579 _97580)). Qed.
Lemma lem7568751 {_139146 _139147 _139148 : Type'} (_97579 : _139148) (_97580 : _139147) (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) (c : _139146) (h1 : term204 _139146 _139147 _139148 P q m c) : term109 _139146 _139147 _139148 P _97579 _97580.
Proof. exact (EQ_MP (@lem7568750 _139146 _139147 _139148 P _97579 _97580) (@lem7568749 _139146 _139147 _139148 _97579 _97580 P q m c h1)). Qed.
Lemma lem7568752 {_139146 _139147 _139148 : Type'} (_97579 : _139148) (_97580 : _139147) (_97581 : _139146) (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) (c : _139146) (h1 : term204 _139146 _139147 _139148 P q m c) : term118 _139146 _139147 _139148 P _97579 _97580 _97581.
Proof. exact (@lem7568751 _139146 _139147 _139148 _97579 _97580 P q m c h1 _97581). Qed.
Lemma lem7568753 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (_97579 : _139148) (_97580 : _139147) (_97581 : _139146) : (term118 _139146 _139147 _139148 P _97579 _97580 _97581) = (P _97579 _97580 _97581).
Proof. exact (eq_refl (term118 _139146 _139147 _139148 P _97579 _97580 _97581)). Qed.
Lemma lem7568755 {_139146 _139147 _139148 : Type'} (_97582 : _139147) (q : _139148) (m' : _139147) (c' : _139146) (P : type1517 _139146 _139147 _139148) (h1 : term256 _139146 _139147 _139148 q m' c' P) : term154 _139146 _139147 _139148 P _97582.
Proof. exact (@lem7568745 _139146 _139147 _139148 q m' c' P h1 _97582). Qed.
Lemma lem7568756 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (_97582 : _139147) : (term154 _139146 _139147 _139148 P _97582) = (term106 _139146 _139147 _139148 P _97582).
Proof. exact (eq_refl (term154 _139146 _139147 _139148 P _97582)). Qed.
Lemma lem7568757 {_139146 _139147 _139148 : Type'} (_97582 : _139147) (q : _139148) (m' : _139147) (c' : _139146) (P : type1517 _139146 _139147 _139148) (h1 : term256 _139146 _139147 _139148 q m' c' P) : term106 _139146 _139147 _139148 P _97582.
Proof. exact (EQ_MP (@lem7568756 _139146 _139147 _139148 P _97582) (@lem7568755 _139146 _139147 _139148 _97582 q m' c' P h1)). Qed.
Lemma lem7568758 {_139146 _139147 _139148 : Type'} (_97582 : _139147) (_97583 : _139146) (q : _139148) (m' : _139147) (c' : _139146) (P : type1517 _139146 _139147 _139148) (h1 : term256 _139146 _139147 _139148 q m' c' P) : term147 _139146 _139147 _139148 P _97582 _97583.
Proof. exact (@lem7568757 _139146 _139147 _139148 _97582 q m' c' P h1 _97583). Qed.
Lemma lem7568759 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (_97582 : _139147) (_97583 : _139146) : (term147 _139146 _139147 _139148 P _97582 _97583) = (term104 _139146 _139147 _139148 P _97582 _97583).
Proof. exact (eq_refl (term147 _139146 _139147 _139148 P _97582 _97583)). Qed.
Lemma lem7568760 {_139146 _139147 _139148 : Type'} (_97582 : _139147) (_97583 : _139146) (q : _139148) (m' : _139147) (c' : _139146) (P : type1517 _139146 _139147 _139148) (h1 : term256 _139146 _139147 _139148 q m' c' P) : term104 _139146 _139147 _139148 P _97582 _97583.
Proof. exact (EQ_MP (@lem7568759 _139146 _139147 _139148 P _97582 _97583) (@lem7568758 _139146 _139147 _139148 _97582 _97583 q m' c' P h1)). Qed.
Lemma lem7568761 {_139146 _139147 _139148 : Type'} (_97582 : _139147) (_97583 : _139146) (_97584 : _139148) (q : _139148) (m' : _139147) (c' : _139146) (P : type1517 _139146 _139147 _139148) (h1 : term256 _139146 _139147 _139148 q m' c' P) : term140 _139146 _139147 _139148 P _97582 _97583 _97584.
Proof. exact (@lem7568760 _139146 _139147 _139148 _97582 _97583 q m' c' P h1 _97584). Qed.
Lemma lem7568762 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (_97584 : _139148) (_97582 : _139147) (_97583 : _139146) : (term140 _139146 _139147 _139148 P _97582 _97583 _97584) = (P _97584 _97582 _97583).
Proof. exact (eq_refl (term140 _139146 _139147 _139148 P _97582 _97583 _97584)). Qed.
Lemma lem7568767 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) (c : _139146) (h1 : term204 _139146 _139147 _139148 P q m c) : term120 _139146 _139147 _139148 P q m c.
Proof. exact (proj2 (@lem7568706 _139146 _139147 _139148 P q m c h1)). Qed.
Lemma lem7568769 {_139146 _139147 _139148 : Type'} (q : _139148) (m' : _139147) (c' : _139146) (P : type1517 _139146 _139147 _139148) (h1 : term256 _139146 _139147 _139148 q m' c' P) : term120 _139146 _139147 _139148 P q m' c'.
Proof. exact (proj1 (@lem7568707 _139146 _139147 _139148 q m' c' P h1)). Qed.
Lemma lem7568773 {_139146 _139147 _139148 : Type'} (_97579 : _139148) (_97580 : _139147) (_97581 : _139146) (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) (c : _139146) (h1 : term204 _139146 _139147 _139148 P q m c) : P _97579 _97580 _97581.
Proof. exact (EQ_MP (@lem7568753 _139146 _139147 _139148 P _97579 _97580 _97581) (@lem7568752 _139146 _139147 _139148 _97579 _97580 _97581 P q m c h1)). Qed.
Lemma lem7568774 {_139146 _139147 _139148 : Type'} (_97579 : _139148) (_97580 : _139147) (_97581 : _139146) (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) (c : _139146) (h1 : term204 _139146 _139147 _139148 P q m c) : P _97579 _97580 _97581.
Proof. exact (@lem7568773 _139146 _139147 _139148 _97579 _97580 _97581 P q m c h1). Qed.
Lemma lem7568775 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) (c : _139146) (h1 : term204 _139146 _139147 _139148 P q m c) : P q m c.
Proof. exact (@lem7568774 _139146 _139147 _139148 q m c P q m c h1). Qed.
Lemma lem7568776 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) (c : _139146) (h1 : term204 _139146 _139147 _139148 P q m c) : term351 _139146 _139147 _139148 P q m c.
Proof. exact (fun h0 : term120 _139146 _139147 _139148 P q m c => @lem7568775 _139146 _139147 _139148 P q m c h1). Qed.
Lemma lem7568778 (p : Prop) : (term352 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7568779 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) (c : _139146) : (term351 _139146 _139147 _139148 P q m c) = (P q m c).
Proof. exact (@lem7568778 (P q m c)). Qed.
Lemma lem7568780 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) (c : _139146) (h1 : term204 _139146 _139147 _139148 P q m c) : P q m c.
Proof. exact (EQ_MP (@lem7568779 _139146 _139147 _139148 P q m c) (@lem7568776 _139146 _139147 _139148 P q m c h1)). Qed.
Lemma lem7568783 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7568785 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) (c : _139146) : (term120 _139146 _139147 _139148 P q m c) = (term353 _139146 _139147 _139148 P q m c).
Proof. exact (@lem7568783 (P q m c)). Qed.
Lemma lem7568788 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) (c : _139146) (h1 : term204 _139146 _139147 _139148 P q m c) : term353 _139146 _139147 _139148 P q m c.
Proof. exact (EQ_MP (@lem7568785 _139146 _139147 _139148 P q m c) (@lem7568767 _139146 _139147 _139148 P q m c h1)). Qed.
Lemma lem7568791 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) (c : _139146) (h1 : term204 _139146 _139147 _139148 P q m c) : False.
Proof. exact (@lem7568788 _139146 _139147 _139148 P q m c h1 (@lem7568780 _139146 _139147 _139148 P q m c h1)). Qed.
Lemma lem7568792 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) (c : _139146) (h1 : term204 _139146 _139147 _139148 P q m c) : term354.
Proof. exact (fun h0 : ~ False => @lem7568791 _139146 _139147 _139148 P q m c h1). Qed.
Lemma lem7568794 (p : Prop) : (term352 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7568795 : term354 = False.
Proof. exact (@lem7568794 False). Qed.
Lemma lem7568796 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m : _139147) (c : _139146) (h1 : term204 _139146 _139147 _139148 P q m c) : False.
Proof. exact (EQ_MP (@lem7568795) (@lem7568792 _139146 _139147 _139148 P q m c h1)). Qed.
Lemma lem7568798 {_139146 _139147 _139148 : Type'} (_97584 : _139148) (_97582 : _139147) (_97583 : _139146) (q : _139148) (m' : _139147) (c' : _139146) (P : type1517 _139146 _139147 _139148) (h1 : term256 _139146 _139147 _139148 q m' c' P) : P _97584 _97582 _97583.
Proof. exact (EQ_MP (@lem7568762 _139146 _139147 _139148 P _97584 _97582 _97583) (@lem7568761 _139146 _139147 _139148 _97582 _97583 _97584 q m' c' P h1)). Qed.
Lemma lem7568799 {_139146 _139147 _139148 : Type'} (_97584 : _139148) (_97582 : _139147) (_97583 : _139146) (q : _139148) (m' : _139147) (c' : _139146) (P : type1517 _139146 _139147 _139148) (h1 : term256 _139146 _139147 _139148 q m' c' P) : P _97584 _97582 _97583.
Proof. exact (@lem7568798 _139146 _139147 _139148 _97584 _97582 _97583 q m' c' P h1). Qed.
Lemma lem7568800 {_139146 _139147 _139148 : Type'} (q : _139148) (m' : _139147) (c' : _139146) (P : type1517 _139146 _139147 _139148) (h1 : term256 _139146 _139147 _139148 q m' c' P) : P q m' c'.
Proof. exact (@lem7568799 _139146 _139147 _139148 q m' c' q m' c' P h1). Qed.
Lemma lem7568801 {_139146 _139147 _139148 : Type'} (q : _139148) (m' : _139147) (c' : _139146) (P : type1517 _139146 _139147 _139148) (h1 : term256 _139146 _139147 _139148 q m' c' P) : term351 _139146 _139147 _139148 P q m' c'.
Proof. exact (fun h0 : term120 _139146 _139147 _139148 P q m' c' => @lem7568800 _139146 _139147 _139148 q m' c' P h1). Qed.
Lemma lem7568803 (p : Prop) : (term352 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7568804 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m' : _139147) (c' : _139146) : (term351 _139146 _139147 _139148 P q m' c') = (P q m' c').
Proof. exact (@lem7568803 (P q m' c')). Qed.
Lemma lem7568805 {_139146 _139147 _139148 : Type'} (q : _139148) (m' : _139147) (c' : _139146) (P : type1517 _139146 _139147 _139148) (h1 : term256 _139146 _139147 _139148 q m' c' P) : P q m' c'.
Proof. exact (EQ_MP (@lem7568804 _139146 _139147 _139148 P q m' c') (@lem7568801 _139146 _139147 _139148 q m' c' P h1)). Qed.
Lemma lem7568808 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7568810 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (q : _139148) (m' : _139147) (c' : _139146) : (term120 _139146 _139147 _139148 P q m' c') = (term353 _139146 _139147 _139148 P q m' c').
Proof. exact (@lem7568808 (P q m' c')). Qed.
Lemma lem7568813 {_139146 _139147 _139148 : Type'} (q : _139148) (m' : _139147) (c' : _139146) (P : type1517 _139146 _139147 _139148) (h1 : term256 _139146 _139147 _139148 q m' c' P) : term353 _139146 _139147 _139148 P q m' c'.
Proof. exact (EQ_MP (@lem7568810 _139146 _139147 _139148 P q m' c') (@lem7568769 _139146 _139147 _139148 q m' c' P h1)). Qed.
Lemma lem7568816 {_139146 _139147 _139148 : Type'} (q : _139148) (m' : _139147) (c' : _139146) (P : type1517 _139146 _139147 _139148) (h1 : term256 _139146 _139147 _139148 q m' c' P) : False.
Proof. exact (@lem7568813 _139146 _139147 _139148 q m' c' P h1 (@lem7568805 _139146 _139147 _139148 q m' c' P h1)). Qed.
Lemma lem7568817 {_139146 _139147 _139148 : Type'} (q : _139148) (m' : _139147) (c' : _139146) (P : type1517 _139146 _139147 _139148) (h1 : term256 _139146 _139147 _139148 q m' c' P) : term354.
Proof. exact (fun h0 : ~ False => @lem7568816 _139146 _139147 _139148 q m' c' P h1). Qed.
Lemma lem7568819 (p : Prop) : (term352 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7568820 : term354 = False.
Proof. exact (@lem7568819 False). Qed.
Lemma lem7568821 {_139146 _139147 _139148 : Type'} (q : _139148) (m' : _139147) (c' : _139146) (P : type1517 _139146 _139147 _139148) (h1 : term256 _139146 _139147 _139148 q m' c' P) : False.
Proof. exact (EQ_MP (@lem7568820) (@lem7568817 _139146 _139147 _139148 q m' c' P h1)). Qed.
Lemma lem7568822 {_139146 _139147 _139148 : Type'} (m : _139147) (c : _139146) (q : _139148) (m' : _139147) (c' : _139146) (P : type1517 _139146 _139147 _139148) (h1 : term339 _139146 _139147 _139148 m c q m' c' P) : False.
Proof. exact (or_elim (@lem7568705 _139146 _139147 _139148 m c q m' c' P h1) (fun h0 : term204 _139146 _139147 _139148 P q m c => @lem7568796 _139146 _139147 _139148 P q m c h0) (fun h0 : term256 _139146 _139147 _139148 q m' c' P => @lem7568821 _139146 _139147 _139148 q m' c' P h0)). Qed.
Lemma lem7568823 {_139146 _139147 _139148 : Type'} (m : _139147) (c : _139146) (q : _139148) (m' : _139147) (c' : _139146) (P : type1517 _139146 _139147 _139148) (h1 : term339 _139146 _139147 _139148 m c q m' c' P) : (term339 _139146 _139147 _139148 m c q m' c' P) = False.
Proof. exact (prop_ext (fun h2 : term339 _139146 _139147 _139148 m c q m' c' P => @lem7568822 _139146 _139147 _139148 m c q m' c' P h1) (fun h2 : False => @lem7568705 _139146 _139147 _139148 m c q m' c' P h1)). Qed.
Lemma lem7568824 {_139146 _139147 _139148 : Type'} (m : _139147) (c : _139146) (q : _139148) (m' : _139147) (c' : _139146) (P : type1517 _139146 _139147 _139148) (h1 : term339 _139146 _139147 _139148 m c q m' c' P) : False.
Proof. exact (EQ_MP (@lem7568823 _139146 _139147 _139148 m c q m' c' P h1) (@lem7568705 _139146 _139147 _139148 m c q m' c' P h1)). Qed.
Lemma lem7568825 {_139146 _139147 _139148 : Type'} (m : _139147) (c : _139146) (q : _139148) (m' : _139147) (P : type1517 _139146 _139147 _139148) (h1 : term342 _139146 _139147 _139148 m c q m' P) : False.
Proof. exact (ex_elim (@lem7568644 _139146 _139147 _139148 m c q m' P h1) (fun c' : _139146 => fun h0 : term341 _139146 _139147 _139148 m c q m' P c' => @lem7568824 _139146 _139147 _139148 m c q m' c' P h0)). Qed.
Lemma lem7568826 {_139146 _139147 _139148 : Type'} (m : _139147) (c : _139146) (q : _139148) (P : type1517 _139146 _139147 _139148) (h1 : term344 _139146 _139147 _139148 m c q P) : False.
Proof. exact (ex_elim (@lem7568643 _139146 _139147 _139148 m c q P h1) (fun m' : _139147 => fun h0 : term343 _139146 _139147 _139148 m c q P m' => @lem7568825 _139146 _139147 _139148 m c q m' P h0)). Qed.
Lemma lem7568827 {_139146 _139147 _139148 : Type'} (m : _139147) (c : _139146) (P : type1517 _139146 _139147 _139148) (h1 : term346 _139146 _139147 _139148 m c P) : False.
Proof. exact (ex_elim (@lem7568642 _139146 _139147 _139148 m c P h1) (fun q : _139148 => fun h0 : term345 _139146 _139147 _139148 m c P q => @lem7568826 _139146 _139147 _139148 m c q P h0)). Qed.
Lemma lem7568828 {_139146 _139147 _139148 : Type'} (m : _139147) (P : type1517 _139146 _139147 _139148) (h1 : term348 _139146 _139147 _139148 m P) : False.
Proof. exact (ex_elim (@lem7568641 _139146 _139147 _139148 m P h1) (fun c : _139146 => fun h0 : term347 _139146 _139147 _139148 m P c => @lem7568827 _139146 _139147 _139148 m c P h0)). Qed.
Lemma lem7568829 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (h1 : term93 _139146 _139147 _139148 P) : False.
Proof. exact (ex_elim (@lem7568640 _139146 _139147 _139148 P h1) (fun m : _139147 => fun h0 : term349 _139146 _139147 _139148 P m => @lem7568828 _139146 _139147 _139148 m P h0)). Qed.
Lemma lem7568830 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (h1 : term93 _139146 _139147 _139148 P) : (term93 _139146 _139147 _139148 P) = False.
Proof. exact (prop_ext (fun h2 : term93 _139146 _139147 _139148 P => @lem7568829 _139146 _139147 _139148 P h1) (fun h2 : False => @lem7568208 _139146 _139147 _139148 P h1)). Qed.
Lemma lem7568831 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (h1 : term93 _139146 _139147 _139148 P) : False.
Proof. exact (EQ_MP (@lem7568830 _139146 _139147 _139148 P h1) (@lem7568208 _139146 _139147 _139148 P h1)). Qed.
Lemma lem7568832 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : term92 _139146 _139147 _139148 P.
Proof. exact (fun h0 : term93 _139146 _139147 _139148 P => @lem7568831 _139146 _139147 _139148 P h0). Qed.
Lemma lem7568833 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term90 _139146 _139147 _139148 P) = (term91 _139146 _139147 _139148 P).
Proof. exact (EQ_MP (@lem7568207 _139146 _139147 _139148 P) (@lem7568832 _139146 _139147 _139148 P)). Qed.
Lemma lem7568838 {_139146 _139147 _139148 : Type'} : term102 _139146 _139147 _139148.
Proof. exact (fun P : type1517 _139146 _139147 _139148 => @lem7568833 _139146 _139147 _139148 P). Qed.
Lemma lem7568839 {_139146 _139147 _139148 : Type'} : term101 _139146 _139147 _139148.
Proof. exact (EQ_MP (@lem7568203 _139146 _139147 _139148) (@lem7568838 _139146 _139147 _139148)). Qed.
Lemma lem7568840 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : term355 _139146 _139147 _139148 P.
Proof. exact (@lem7568839 _139146 _139147 _139148 P). Qed.
Lemma lem7568841 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term355 _139146 _139147 _139148 P) = (term92 _139146 _139147 _139148 P).
Proof. exact (eq_refl (term355 _139146 _139147 _139148 P)). Qed.
Lemma lem7568842 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : term92 _139146 _139147 _139148 P.
Proof. exact (EQ_MP (@lem7568841 _139146 _139147 _139148 P) (@lem7568840 _139146 _139147 _139148 P)). Qed.
Lemma lem7568844 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : term92 _139146 _139147 _139148 P.
Proof. exact (@lem7568085 _139146 _139147 _139148 P (@lem7568842 _139146 _139147 _139148 P)). Qed.
Lemma lem7568845 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (h1 : term93 _139146 _139147 _139148 P) : False.
Proof. exact (@lem7568844 _139146 _139147 _139148 P (@lem7568069 _139146 _139147 _139148 P h1)). Qed.
Lemma lem7568846 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (h1 : term93 _139146 _139147 _139148 P) : (term93 _139146 _139147 _139148 P) = False.
Proof. exact (prop_ext (fun h2 : term93 _139146 _139147 _139148 P => @lem7568845 _139146 _139147 _139148 P h1) (fun h2 : False => @lem7568069 _139146 _139147 _139148 P h1)). Qed.
Lemma lem7568847 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) (h1 : term93 _139146 _139147 _139148 P) : False.
Proof. exact (EQ_MP (@lem7568846 _139146 _139147 _139148 P h1) (@lem7568069 _139146 _139147 _139148 P h1)). Qed.
Lemma lem7568848 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : term92 _139146 _139147 _139148 P.
Proof. exact (fun h0 : term93 _139146 _139147 _139148 P => @lem7568847 _139146 _139147 _139148 P h0). Qed.
Lemma lem7568850 {A : Type'} (P : A -> Prop) : term34 A P.
Proof. exact (@lem6644 A P). Qed.
Lemma lem7568851 {A : Type'} (P : A -> Prop) : (term34 A P) = (term35 A P).
Proof. exact (eq_refl (term34 A P)). Qed.
Lemma lem7568852 {A : Type'} (P : A -> Prop) : term35 A P.
Proof. exact (EQ_MP (@lem7568851 A P) (@lem7568850 A P)). Qed.
Lemma lem7568853 {A : Type'} (P : A -> Prop) (Q : Prop) : term36 A P Q.
Proof. exact (@lem7568852 A P Q). Qed.
Lemma lem7568854 {A : Type'} (P : A -> Prop) (Q : Prop) : (term36 A P Q) = ((term37 A P Q) = (term38 A P Q)).
Proof. exact (eq_refl (term36 A P Q)). Qed.
Lemma lem7568856 (p : real -> real) : term39 p.
Proof. exact (@lem7553488 p). Qed.
Lemma lem7568857 (p : real -> real) : (term39 p) = ((polynomial_function p) = (term40 p)).
Proof. exact (eq_refl (term39 p)). Qed.
Lemma lem7568859 {A : Type'} (P : Prop) : term356 A P.
Proof. exact (@lem6534 A P). Qed.
Lemma lem7568860 {A : Type'} (P : Prop) : (term356 A P) = (term357 A P).
Proof. exact (eq_refl (term356 A P)). Qed.
Lemma lem7568861 {A : Type'} (P : Prop) : term357 A P.
Proof. exact (EQ_MP (@lem7568860 A P) (@lem7568859 A P)). Qed.
Lemma lem7568862 {A : Type'} (P : Prop) (Q : A -> Prop) : term358 A P Q.
Proof. exact (@lem7568861 A P Q). Qed.
Lemma lem7568863 {A : Type'} (P : Prop) (Q : A -> Prop) : (term358 A P Q) = ((term359 A P Q) = (term360 A P Q)).
Proof. exact (eq_refl (term358 A P Q)). Qed.
Lemma lem7568894 (p : Prop) (q : Prop) (r : Prop) : (term361 p q r) = (term362 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem7568895 (p : real -> real) (q : real -> real) : (term363 p q) = (term364 p q).
Proof. exact (@lem7568894 (polynomial_function p) (polynomial_function q) (term365 p q)). Qed.
Lemma lem7568900 (p : real -> real) : (term366 p) = (term367 p).
Proof. exact (fun_ext (fun q : real -> real => @lem7568895 p q)). Qed.
Lemma lem7568901 : (@all (real -> real)) = (@all (real -> real)).
Proof. exact (eq_refl (@all (real -> real))). Qed.
Lemma lem7568902 (p : real -> real) : (term368 p) = (term369 p).
Proof. exact (MK_COMB (@lem7568901) (@lem7568900 p)). Qed.
Lemma lem7568904 {A : Type'} (P : Prop) (Q : A -> Prop) : (term359 A P Q) = (term360 A P Q).
Proof. exact (EQ_MP (@lem7568863 A P Q) (@lem7568862 A P Q)). Qed.
Lemma lem7568905 (P : Prop) (Q : type1028) : (term370 P Q) = (term371 P Q).
Proof. exact (@lem7568904 (real -> real) P Q). Qed.
Lemma lem7568906 (p : real -> real) : (term372 p) = (term373 p).
Proof. exact (@lem7568905 (polynomial_function p) (term374 p)). Qed.
Lemma lem7568907 (p : real -> real) (q : real -> real) : (term375 p q) = (term376 p q).
Proof. exact (eq_refl (term375 p q)). Qed.
Lemma lem7568908 (p : real -> real) : (term377 p) = (term377 p).
Proof. exact (eq_refl (term377 p)). Qed.
Lemma lem7568909 (p : real -> real) (q : real -> real) : (term378 p q) = (term364 p q).
Proof. exact (MK_COMB (@lem7568908 p) (@lem7568907 p q)). Qed.
Lemma lem7568910 (p : real -> real) : (term379 p) = (term367 p).
Proof. exact (fun_ext (fun q : real -> real => @lem7568909 p q)). Qed.
Lemma lem7568911 : (@all (real -> real)) = (@all (real -> real)).
Proof. exact (eq_refl (@all (real -> real))). Qed.
Lemma lem7568912 (p : real -> real) : (term372 p) = (term369 p).
Proof. exact (MK_COMB (@lem7568911) (@lem7568910 p)). Qed.
Lemma lem7568913 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7568914 (p : real -> real) : (term380 p) = (term381 p).
Proof. exact (MK_COMB (@lem7568913) (@lem7568912 p)). Qed.
Lemma lem7568915 (p : real -> real) (q : real -> real) : (term375 p q) = (term376 p q).
Proof. exact (eq_refl (term375 p q)). Qed.
Lemma lem7568916 (p : real -> real) : (term382 p) = (term374 p).
Proof. exact (fun_ext (fun q : real -> real => @lem7568915 p q)). Qed.
Lemma lem7568917 : (@all (real -> real)) = (@all (real -> real)).
Proof. exact (eq_refl (@all (real -> real))). Qed.
Lemma lem7568918 (p : real -> real) : (term383 p) = (term384 p).
Proof. exact (MK_COMB (@lem7568917) (@lem7568916 p)). Qed.
Lemma lem7568919 (p : real -> real) : (term377 p) = (term377 p).
Proof. exact (eq_refl (term377 p)). Qed.
Lemma lem7568920 (p : real -> real) : (term373 p) = (term385 p).
Proof. exact (MK_COMB (@lem7568919 p) (@lem7568918 p)). Qed.
Lemma lem7568921 (p : real -> real) : ((term372 p) = (term373 p)) = ((term369 p) = (term385 p)).
Proof. exact (MK_COMB (@lem7568914 p) (@lem7568920 p)). Qed.
Lemma lem7568922 (p : real -> real) : (term369 p) = (term385 p).
Proof. exact (EQ_MP (@lem7568921 p) (@lem7568906 p)). Qed.
Lemma lem7568951 (p : real -> real) : (term368 p) = (term385 p).
Proof. exact (TRANS (@lem7568902 p) (@lem7568922 p)). Qed.
Lemma lem7568952 : term386 = term387.
Proof. exact (fun_ext (fun p : real -> real => @lem7568951 p)). Qed.
Lemma lem7568953 : (@all (real -> real)) = (@all (real -> real)).
Proof. exact (eq_refl (@all (real -> real))). Qed.
Lemma lem7568954 : term388 = term389.
Proof. exact (MK_COMB (@lem7568953) (@lem7568952)). Qed.
Lemma lem7568979 : term389 = term388.
Proof. exact (SYM (@lem7568954)). Qed.
Lemma lem7568980 (p : real -> real) (h1 : polynomial_function p) : polynomial_function p.
Proof. exact (h1). Qed.
Lemma lem7568982 (p : real -> real) : (polynomial_function p) = (term40 p).
Proof. exact (EQ_MP (@lem7568857 p) (@lem7568856 p)). Qed.
Lemma lem7568983 (q : real -> real) : (polynomial_function q) = (term40 q).
Proof. exact (@lem7568982 q). Qed.
Lemma lem7568984 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7568985 (q : real -> real) : (term377 q) = (term390 q).
Proof. exact (MK_COMB (@lem7568984) (@lem7568983 q)). Qed.
Lemma lem7568986 (p : real -> real) (q : real -> real) : (term365 p q) = (term365 p q).
Proof. exact (eq_refl (term365 p q)). Qed.
Lemma lem7568987 (p : real -> real) (q : real -> real) : (term376 p q) = (term391 p q).
Proof. exact (MK_COMB (@lem7568985 q) (@lem7568986 p q)). Qed.
Lemma lem7568988 (p : real -> real) : (term374 p) = (term392 p).
Proof. exact (fun_ext (fun q : real -> real => @lem7568987 p q)). Qed.
Lemma lem7568989 : (@all (real -> real)) = (@all (real -> real)).
Proof. exact (eq_refl (@all (real -> real))). Qed.
Lemma lem7568990 (p : real -> real) : (term384 p) = (term393 p).
Proof. exact (MK_COMB (@lem7568989) (@lem7568988 p)). Qed.
Lemma lem7568991 (p : real -> real) : (term393 p) = (term384 p).
Proof. exact (SYM (@lem7568990 p)). Qed.
Lemma lem7568997 {A : Type'} (P : A -> Prop) (Q : Prop) : (term37 A P Q) = (term38 A P Q).
Proof. exact (EQ_MP (@lem7568854 A P Q) (@lem7568853 A P Q)). Qed.
Lemma lem7568998 (P : nat -> Prop) (Q : Prop) : (term394 P Q) = (term395 P Q).
Proof. exact (@lem7568997 nat P Q). Qed.
Lemma lem7568999 (p : real -> real) (q : real -> real) : (term396 p q) = (term397 p q).
Proof. exact (@lem7568998 (term398 q) (term365 p q)). Qed.
Lemma lem7569000 (q : real -> real) (m : nat) : (term399 q m) = (term400 q m).
Proof. exact (eq_refl (term399 q m)). Qed.
Lemma lem7569001 (q : real -> real) : (term401 q) = (term398 q).
Proof. exact (fun_ext (fun m : nat => @lem7569000 q m)). Qed.
Lemma lem7569002 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7569003 (q : real -> real) : (term402 q) = (term40 q).
Proof. exact (MK_COMB (@lem7569002) (@lem7569001 q)). Qed.
Lemma lem7569004 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7569005 (q : real -> real) : (term403 q) = (term390 q).
Proof. exact (MK_COMB (@lem7569004) (@lem7569003 q)). Qed.
Lemma lem7569006 (p : real -> real) (q : real -> real) : (term365 p q) = (term365 p q).
Proof. exact (eq_refl (term365 p q)). Qed.
Lemma lem7569007 (p : real -> real) (q : real -> real) : (term396 p q) = (term391 p q).
Proof. exact (MK_COMB (@lem7569005 q) (@lem7569006 p q)). Qed.
Lemma lem7569008 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7569009 (p : real -> real) (q : real -> real) : (term404 p q) = (term405 p q).
Proof. exact (MK_COMB (@lem7569008) (@lem7569007 p q)). Qed.
Lemma lem7569010 (q : real -> real) (m : nat) : (term399 q m) = (term400 q m).
Proof. exact (eq_refl (term399 q m)). Qed.
Lemma lem7569011 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7569012 (q : real -> real) (m : nat) : (term406 q m) = (term407 q m).
Proof. exact (MK_COMB (@lem7569011) (@lem7569010 q m)). Qed.
Lemma lem7569013 (p : real -> real) (q : real -> real) : (term365 p q) = (term365 p q).
Proof. exact (eq_refl (term365 p q)). Qed.
Lemma lem7569014 (m : nat) (p : real -> real) (q : real -> real) : (term408 m p q) = (term409 m p q).
Proof. exact (MK_COMB (@lem7569012 q m) (@lem7569013 p q)). Qed.
Lemma lem7569015 (p : real -> real) (q : real -> real) : (term410 p q) = (term411 p q).
Proof. exact (fun_ext (fun m : nat => @lem7569014 m p q)). Qed.
Lemma lem7569016 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7569017 (p : real -> real) (q : real -> real) : (term397 p q) = (term412 p q).
Proof. exact (MK_COMB (@lem7569016) (@lem7569015 p q)). Qed.
Lemma lem7569018 (p : real -> real) (q : real -> real) : ((term396 p q) = (term397 p q)) = ((term391 p q) = (term412 p q)).
Proof. exact (MK_COMB (@lem7569009 p q) (@lem7569017 p q)). Qed.
Lemma lem7569019 (p : real -> real) (q : real -> real) : (term391 p q) = (term412 p q).
Proof. exact (EQ_MP (@lem7569018 p q) (@lem7568999 p q)). Qed.
Lemma lem7569025 {A : Type'} (P : A -> Prop) (Q : Prop) : (term37 A P Q) = (term38 A P Q).
Proof. exact (EQ_MP (@lem7568854 A P Q) (@lem7568853 A P Q)). Qed.
Lemma lem7569026 (P : type1010) (Q : Prop) : (term413 P Q) = (term414 P Q).
Proof. exact (@lem7569025 (nat -> real) P Q). Qed.
Lemma lem7569027 (m : nat) (p : real -> real) (q : real -> real) : (term415 m p q) = (term416 m p q).
Proof. exact (@lem7569026 (term417 q m) (term365 p q)). Qed.
Lemma lem7569028 (q : real -> real) (m : nat) (c : nat -> real) : (term418 q m c) = (term419 q m c).
Proof. exact (eq_refl (term418 q m c)). Qed.
Lemma lem7569029 (q : real -> real) (m : nat) : (term420 q m) = (term417 q m).
Proof. exact (fun_ext (fun c : nat -> real => @lem7569028 q m c)). Qed.
Lemma lem7569030 : (@ex (nat -> real)) = (@ex (nat -> real)).
Proof. exact (eq_refl (@ex (nat -> real))). Qed.
Lemma lem7569031 (q : real -> real) (m : nat) : (term421 q m) = (term400 q m).
Proof. exact (MK_COMB (@lem7569030) (@lem7569029 q m)). Qed.
Lemma lem7569032 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7569033 (q : real -> real) (m : nat) : (term422 q m) = (term407 q m).
Proof. exact (MK_COMB (@lem7569032) (@lem7569031 q m)). Qed.
Lemma lem7569034 (p : real -> real) (q : real -> real) : (term365 p q) = (term365 p q).
Proof. exact (eq_refl (term365 p q)). Qed.
Lemma lem7569035 (m : nat) (p : real -> real) (q : real -> real) : (term415 m p q) = (term409 m p q).
Proof. exact (MK_COMB (@lem7569033 q m) (@lem7569034 p q)). Qed.
Lemma lem7569036 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7569037 (m : nat) (p : real -> real) (q : real -> real) : (term423 m p q) = (term424 m p q).
Proof. exact (MK_COMB (@lem7569036) (@lem7569035 m p q)). Qed.
Lemma lem7569038 (q : real -> real) (m : nat) (c : nat -> real) : (term418 q m c) = (term419 q m c).
Proof. exact (eq_refl (term418 q m c)). Qed.
Lemma lem7569039 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7569040 (q : real -> real) (m : nat) (c : nat -> real) : (term425 q m c) = (term426 q m c).
Proof. exact (MK_COMB (@lem7569039) (@lem7569038 q m c)). Qed.
Lemma lem7569041 (p : real -> real) (q : real -> real) : (term365 p q) = (term365 p q).
Proof. exact (eq_refl (term365 p q)). Qed.
Lemma lem7569042 (m : nat) (c : nat -> real) (p : real -> real) (q : real -> real) : (term427 m c p q) = (term428 m c p q).
Proof. exact (MK_COMB (@lem7569040 q m c) (@lem7569041 p q)). Qed.
Lemma lem7569043 (m : nat) (p : real -> real) (q : real -> real) : (term429 m p q) = (term430 m p q).
Proof. exact (fun_ext (fun c : nat -> real => @lem7569042 m c p q)). Qed.
Lemma lem7569044 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7569045 (m : nat) (p : real -> real) (q : real -> real) : (term416 m p q) = (term431 m p q).
Proof. exact (MK_COMB (@lem7569044) (@lem7569043 m p q)). Qed.
Lemma lem7569046 (m : nat) (p : real -> real) (q : real -> real) : ((term415 m p q) = (term416 m p q)) = ((term409 m p q) = (term431 m p q)).
Proof. exact (MK_COMB (@lem7569037 m p q) (@lem7569045 m p q)). Qed.
Lemma lem7569047 (m : nat) (p : real -> real) (q : real -> real) : (term409 m p q) = (term431 m p q).
Proof. exact (EQ_MP (@lem7569046 m p q) (@lem7569027 m p q)). Qed.
Lemma lem7569055 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term432 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7569056 (p : Prop) (q : Prop) (p' : Prop) : term433 p q p'.
Proof. exact (fun q' : Prop => @lem7569055 p q p' q'). Qed.
Lemma lem7569057 (p : Prop) (q : Prop) : term434 p q.
Proof. exact (fun p' : Prop => @lem7569056 p q p'). Qed.
Lemma lem7569058 (m : nat) (c : nat -> real) (p : real -> real) (q : real -> real) : term435 m c p q.
Proof. exact (@lem7569057 (term419 q m c) (term365 p q)). Qed.
Lemma lem7569059 (m : nat) (c : nat -> real) (p : real -> real) (q : real -> real) (p' : Prop) : term436 m c p q p'.
Proof. exact (@lem7569058 m c p q p'). Qed.
Lemma lem7569060 (m : nat) (c : nat -> real) (p : real -> real) (q : real -> real) (p' : Prop) : (term436 m c p q p') = (term437 m c p q p').
Proof. exact (eq_refl (term436 m c p q p')). Qed.
Lemma lem7569061 (m : nat) (c : nat -> real) (p : real -> real) (q : real -> real) (p' : Prop) : term437 m c p q p'.
Proof. exact (EQ_MP (@lem7569060 m c p q p') (@lem7569059 m c p q p')). Qed.
Lemma lem7569062 (m : nat) (c : nat -> real) (p : real -> real) (q : real -> real) (p' : Prop) (q' : Prop) : term438 m c p q p' q'.
Proof. exact (@lem7569061 m c p q p' q'). Qed.
Lemma lem7569063 (m : nat) (c : nat -> real) (p : real -> real) (q : real -> real) (p' : Prop) (q' : Prop) : (term438 m c p q p' q') = (term439 m c p q p' q').
Proof. exact (eq_refl (term438 m c p q p' q')). Qed.
Lemma lem7569064 (m : nat) (c : nat -> real) (p : real -> real) (q : real -> real) (p' : Prop) (q' : Prop) : term439 m c p q p' q'.
Proof. exact (EQ_MP (@lem7569063 m c p q p' q') (@lem7569062 m c p q p' q')). Qed.
Lemma lem7569186 (q : real -> real) (m : nat) (c : nat -> real) : (term419 q m c) = (term419 q m c).
Proof. exact (eq_refl (term419 q m c)). Qed.
Lemma lem7569187 (p : real -> real) (q : real -> real) (m : nat) (c : nat -> real) (q' : Prop) : term440 p q m c q'.
Proof. exact (@lem7569064 m c p q (term419 q m c) q'). Qed.
Lemma lem7569188 (p : real -> real) (q : real -> real) (m : nat) (c : nat -> real) (q' : Prop) : term441 p q m c q'.
Proof. exact (@lem7569187 p q m c q' (@lem7569186 q m c)). Qed.
Lemma lem7569189 (q : real -> real) (m : nat) (c : nat -> real) (h1 : term419 q m c) : term419 q m c.
Proof. exact (h1). Qed.
Lemma lem7569190 (x : real) (q : real -> real) (m : nat) (c : nat -> real) (h1 : term419 q m c) : term442 q m c x.
Proof. exact (@lem7569189 q m c h1 x). Qed.
Lemma lem7569191 (q : real -> real) (m : nat) (c : nat -> real) (x : real) : (term442 q m c x) = ((q x) = (term443 m c x)).
Proof. exact (eq_refl (term442 q m c x)). Qed.
Lemma lem7569194 (x : real) (q : real -> real) (m : nat) (c : nat -> real) (h1 : term419 q m c) : (q x) = (term443 m c x).
Proof. exact (EQ_MP (@lem7569191 q m c x) (@lem7569190 x q m c h1)). Qed.
Lemma lem7569310 (p : real -> real) (x : real) : (term444 p x) = (term444 p x).
Proof. exact (eq_refl (term444 p x)). Qed.
Lemma lem7569311 (p : real -> real) (x : real) (q : real -> real) (m : nat) (c : nat -> real) (h1 : term419 q m c) : (term445 p q x) = (term446 p m c x).
Proof. exact (MK_COMB (@lem7569310 p x) (@lem7569194 x q m c h1)). Qed.
Lemma lem7569427 (p : real -> real) (q : real -> real) (m : nat) (c : nat -> real) (h1 : term419 q m c) : (term447 p q) = (term448 p m c).
Proof. exact (fun_ext (fun x : real => @lem7569311 p x q m c h1)). Qed.
Lemma lem7569543 : polynomial_function = polynomial_function.
Proof. exact (eq_refl polynomial_function). Qed.
Lemma lem7569544 (p : real -> real) (q : real -> real) (m : nat) (c : nat -> real) (h1 : term419 q m c) : (term365 p q) = (term449 p m c).
Proof. exact (MK_COMB (@lem7569543) (@lem7569427 p q m c h1)). Qed.
Lemma lem7569660 (q : real -> real) (p : real -> real) (m : nat) (c : nat -> real) : term450 q p m c.
Proof. exact (fun h0 : term419 q m c => @lem7569544 p q m c h0). Qed.
Lemma lem7569661 (q : real -> real) (p : real -> real) (m : nat) (c : nat -> real) : term451 q p m c.
Proof. exact (@lem7569188 p q m c (term449 p m c)). Qed.
Lemma lem7569662 (q : real -> real) (p : real -> real) (m : nat) (c : nat -> real) : (term428 m c p q) = (term452 q p m c).
Proof. exact (@lem7569661 q p m c (@lem7569660 q p m c)). Qed.
Lemma lem7570159 (q : real -> real) (p : real -> real) (m : nat) : (term430 m p q) = (term453 q p m).
Proof. exact (fun_ext (fun c : nat -> real => @lem7569662 q p m c)). Qed.
Lemma lem7570656 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7570657 (q : real -> real) (p : real -> real) (m : nat) : (term431 m p q) = (term454 q p m).
Proof. exact (MK_COMB (@lem7570656) (@lem7570159 q p m)). Qed.
Lemma lem7571158 (q : real -> real) (p : real -> real) (m : nat) : (term409 m p q) = (term454 q p m).
Proof. exact (TRANS (@lem7569047 m p q) (@lem7570657 q p m)). Qed.
Lemma lem7571159 (q : real -> real) (p : real -> real) : (term411 p q) = (term455 q p).
Proof. exact (fun_ext (fun m : nat => @lem7571158 q p m)). Qed.
Lemma lem7571660 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7571661 (q : real -> real) (p : real -> real) : (term412 p q) = (term456 q p).
Proof. exact (MK_COMB (@lem7571660) (@lem7571159 q p)). Qed.
Lemma lem7572166 (q : real -> real) (p : real -> real) : (term391 p q) = (term456 q p).
Proof. exact (TRANS (@lem7569019 p q) (@lem7571661 q p)). Qed.
Lemma lem7572167 (p : real -> real) : (term392 p) = (term457 p).
Proof. exact (fun_ext (fun q : real -> real => @lem7572166 q p)). Qed.
Lemma lem7572672 : (@all (real -> real)) = (@all (real -> real)).
Proof. exact (eq_refl (@all (real -> real))). Qed.
Lemma lem7572673 (p : real -> real) : (term393 p) = (term458 p).
Proof. exact (MK_COMB (@lem7572672) (@lem7572167 p)). Qed.
Lemma lem7573182 (p : real -> real) : (term458 p) = (term393 p).
Proof. exact (SYM (@lem7572673 p)). Qed.
Lemma lem7573184 {_139146 _139147 _139148 : Type'} (P : type1517 _139146 _139147 _139148) : (term90 _139146 _139147 _139148 P) = (term91 _139146 _139147 _139148 P).
Proof. exact (EQ_MP (@lem7568068 _139146 _139147 _139148 P) (@lem7568848 _139146 _139147 _139148 P)). Qed.
Lemma lem7573185 (P : type1026) : (term459 P) = (term460 P).
Proof. exact (@lem7573184 (nat -> real) nat (real -> real) P). Qed.
Lemma lem7573186 (p : real -> real) : (term461 p) = (term462 p).
Proof. exact (@lem7573185 (term463 p)). Qed.
Lemma lem7573187 (q : real -> real) (p : real -> real) : (term464 p q) = (term465 q p).
Proof. exact (eq_refl (term464 p q)). Qed.
Lemma lem7573188 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem7573189 (q : real -> real) (p : real -> real) (m : nat) : (term466 p q m) = (term467 q p m).
Proof. exact (MK_COMB (@lem7573187 q p) (@lem7573188 m)). Qed.
Lemma lem7573190 (q : real -> real) (p : real -> real) (m : nat) : (term467 q p m) = (term453 q p m).
Proof. exact (eq_refl (term467 q p m)). Qed.
Lemma lem7573191 (q : real -> real) (p : real -> real) (m : nat) : (term466 p q m) = (term453 q p m).
Proof. exact (TRANS (@lem7573189 q p m) (@lem7573190 q p m)). Qed.
Lemma lem7573192 (c : nat -> real) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem7573193 (q : real -> real) (p : real -> real) (m : nat) (c : nat -> real) : (term468 p q m c) = (term469 q p m c).
Proof. exact (MK_COMB (@lem7573191 q p m) (@lem7573192 c)). Qed.
Lemma lem7573194 (q : real -> real) (p : real -> real) (m : nat) (c : nat -> real) : (term469 q p m c) = (term452 q p m c).
Proof. exact (eq_refl (term469 q p m c)). Qed.
Lemma lem7573195 (q : real -> real) (p : real -> real) (m : nat) (c : nat -> real) : (term468 p q m c) = (term452 q p m c).
Proof. exact (TRANS (@lem7573193 q p m c) (@lem7573194 q p m c)). Qed.
Lemma lem7573196 (q : real -> real) (p : real -> real) (m : nat) : (term470 p q m) = (term453 q p m).
Proof. exact (fun_ext (fun c : nat -> real => @lem7573195 q p m c)). Qed.
Lemma lem7573197 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7573198 (q : real -> real) (p : real -> real) (m : nat) : (term471 p q m) = (term454 q p m).
Proof. exact (MK_COMB (@lem7573197) (@lem7573196 q p m)). Qed.
Lemma lem7573199 (q : real -> real) (p : real -> real) : (term472 p q) = (term455 q p).
Proof. exact (fun_ext (fun m : nat => @lem7573198 q p m)). Qed.
Lemma lem7573200 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7573201 (q : real -> real) (p : real -> real) : (term473 p q) = (term456 q p).
Proof. exact (MK_COMB (@lem7573200) (@lem7573199 q p)). Qed.
Lemma lem7573202 (p : real -> real) : (term474 p) = (term457 p).
Proof. exact (fun_ext (fun q : real -> real => @lem7573201 q p)). Qed.
Lemma lem7573203 : (@all (real -> real)) = (@all (real -> real)).
Proof. exact (eq_refl (@all (real -> real))). Qed.
Lemma lem7573204 (p : real -> real) : (term461 p) = (term458 p).
Proof. exact (MK_COMB (@lem7573203) (@lem7573202 p)). Qed.
Lemma lem7573205 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7573206 (p : real -> real) : (term475 p) = (term476 p).
Proof. exact (MK_COMB (@lem7573205) (@lem7573204 p)). Qed.
Lemma lem7573207 (q : real -> real) (p : real -> real) : (term464 p q) = (term465 q p).
Proof. exact (eq_refl (term464 p q)). Qed.
Lemma lem7573208 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem7573209 (q : real -> real) (p : real -> real) (m : nat) : (term466 p q m) = (term467 q p m).
Proof. exact (MK_COMB (@lem7573207 q p) (@lem7573208 m)). Qed.
Lemma lem7573210 (q : real -> real) (p : real -> real) (m : nat) : (term467 q p m) = (term453 q p m).
Proof. exact (eq_refl (term467 q p m)). Qed.
Lemma lem7573211 (q : real -> real) (p : real -> real) (m : nat) : (term466 p q m) = (term453 q p m).
Proof. exact (TRANS (@lem7573209 q p m) (@lem7573210 q p m)). Qed.
Lemma lem7573212 (c : nat -> real) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem7573213 (q : real -> real) (p : real -> real) (m : nat) (c : nat -> real) : (term468 p q m c) = (term469 q p m c).
Proof. exact (MK_COMB (@lem7573211 q p m) (@lem7573212 c)). Qed.
Lemma lem7573214 (q : real -> real) (p : real -> real) (m : nat) (c : nat -> real) : (term469 q p m c) = (term452 q p m c).
Proof. exact (eq_refl (term469 q p m c)). Qed.
Lemma lem7573215 (q : real -> real) (p : real -> real) (m : nat) (c : nat -> real) : (term468 p q m c) = (term452 q p m c).
Proof. exact (TRANS (@lem7573213 q p m c) (@lem7573214 q p m c)). Qed.
Lemma lem7573216 (p : real -> real) (m : nat) (c : nat -> real) : (term477 p m c) = (term478 p m c).
Proof. exact (fun_ext (fun q : real -> real => @lem7573215 q p m c)). Qed.
Lemma lem7573217 : (@all (real -> real)) = (@all (real -> real)).
Proof. exact (eq_refl (@all (real -> real))). Qed.
Lemma lem7573218 (p : real -> real) (m : nat) (c : nat -> real) : (term479 p m c) = (term480 p m c).
Proof. exact (MK_COMB (@lem7573217) (@lem7573216 p m c)). Qed.
Lemma lem7573219 (p : real -> real) (m : nat) : (term481 p m) = (term482 p m).
Proof. exact (fun_ext (fun c : nat -> real => @lem7573218 p m c)). Qed.
Lemma lem7573220 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7573221 (p : real -> real) (m : nat) : (term483 p m) = (term484 p m).
Proof. exact (MK_COMB (@lem7573220) (@lem7573219 p m)). Qed.
Lemma lem7573222 (p : real -> real) : (term485 p) = (term486 p).
Proof. exact (fun_ext (fun m : nat => @lem7573221 p m)). Qed.
Lemma lem7573223 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7573224 (p : real -> real) : (term462 p) = (term487 p).
Proof. exact (MK_COMB (@lem7573223) (@lem7573222 p)). Qed.
Lemma lem7573225 (p : real -> real) : ((term461 p) = (term462 p)) = ((term458 p) = (term487 p)).
Proof. exact (MK_COMB (@lem7573206 p) (@lem7573224 p)). Qed.
Lemma lem7573226 (p : real -> real) : (term458 p) = (term487 p).
Proof. exact (EQ_MP (@lem7573225 p) (@lem7573186 p)). Qed.
Lemma lem7573227 (p : real -> real) : (term487 p) = (term458 p).
Proof. exact (SYM (@lem7573226 p)). Qed.
Lemma lem7573243 {A B : Type'} (f : A -> B) (g : A -> B) : (term44 A B f g) = (f = g).
Proof. exact (EQ_MP (@lem7568053 A B f g) (@lem7568052 A B f g)). Qed.
Lemma lem7573244 (f : real -> real) (g : real -> real) : (term488 f g) = (f = g).
Proof. exact (@lem7573243 real real f g). Qed.
Lemma lem7573245 (q : real -> real) (m : nat) (c : nat -> real) : (term489 q m c) = (q = (term490 m c)).
Proof. exact (@lem7573244 q (term490 m c)). Qed.
Lemma lem7573246 (m : nat) (c : nat -> real) (x : real) : (term491 m c x) = (term443 m c x).
Proof. exact (eq_refl (term491 m c x)). Qed.
Lemma lem7573247 (q : real -> real) (x : real) : (term492 q x) = (term492 q x).
Proof. exact (eq_refl (term492 q x)). Qed.
Lemma lem7573248 (q : real -> real) (m : nat) (c : nat -> real) (x : real) : ((q x) = (term491 m c x)) = ((q x) = (term443 m c x)).
Proof. exact (MK_COMB (@lem7573247 q x) (@lem7573246 m c x)). Qed.
Lemma lem7573249 (q : real -> real) (m : nat) (c : nat -> real) : (term493 q m c) = (term494 q m c).
Proof. exact (fun_ext (fun x : real => @lem7573248 q m c x)). Qed.
Lemma lem7573250 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7573251 (q : real -> real) (m : nat) (c : nat -> real) : (term489 q m c) = (term419 q m c).
Proof. exact (MK_COMB (@lem7573250) (@lem7573249 q m c)). Qed.
Lemma lem7573252 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7573253 (q : real -> real) (m : nat) (c : nat -> real) : (term495 q m c) = (term496 q m c).
Proof. exact (MK_COMB (@lem7573252) (@lem7573251 q m c)). Qed.
Lemma lem7573254 (q : real -> real) (m : nat) (c : nat -> real) : (q = (term490 m c)) = (q = (term490 m c)).
Proof. exact (eq_refl (q = (term490 m c))). Qed.
Lemma lem7573255 (q : real -> real) (m : nat) (c : nat -> real) : ((term489 q m c) = (q = (term490 m c))) = ((term419 q m c) = (q = (term490 m c))).
Proof. exact (MK_COMB (@lem7573253 q m c) (@lem7573254 q m c)). Qed.
Lemma lem7573256 (q : real -> real) (m : nat) (c : nat -> real) : (term419 q m c) = (q = (term490 m c)).
Proof. exact (EQ_MP (@lem7573255 q m c) (@lem7573245 q m c)). Qed.
Lemma lem7573257 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7573258 (q : real -> real) (m : nat) (c : nat -> real) : (term426 q m c) = (term497 q m c).
Proof. exact (MK_COMB (@lem7573257) (@lem7573256 q m c)). Qed.
Lemma lem7573259 (p : real -> real) (m : nat) (c : nat -> real) : (term449 p m c) = (term449 p m c).
Proof. exact (eq_refl (term449 p m c)). Qed.
Lemma lem7573260 (q : real -> real) (p : real -> real) (m : nat) (c : nat -> real) : (term452 q p m c) = (term498 q p m c).
Proof. exact (MK_COMB (@lem7573258 q m c) (@lem7573259 p m c)). Qed.
Lemma lem7573261 (p : real -> real) (m : nat) (c : nat -> real) : (term478 p m c) = (term499 p m c).
Proof. exact (fun_ext (fun q : real -> real => @lem7573260 q p m c)). Qed.
Lemma lem7573262 : (@all (real -> real)) = (@all (real -> real)).
Proof. exact (eq_refl (@all (real -> real))). Qed.
Lemma lem7573263 (p : real -> real) (m : nat) (c : nat -> real) : (term480 p m c) = (term500 p m c).
Proof. exact (MK_COMB (@lem7573262) (@lem7573261 p m c)). Qed.
Lemma lem7573264 (p : real -> real) (m : nat) : (term482 p m) = (term501 p m).
Proof. exact (fun_ext (fun c : nat -> real => @lem7573263 p m c)). Qed.
Lemma lem7573265 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7573266 (p : real -> real) (m : nat) : (term484 p m) = (term502 p m).
Proof. exact (MK_COMB (@lem7573265) (@lem7573264 p m)). Qed.
Lemma lem7573267 (p : real -> real) : (term486 p) = (term503 p).
Proof. exact (fun_ext (fun m : nat => @lem7573266 p m)). Qed.
Lemma lem7573268 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7573269 (p : real -> real) : (term487 p) = (term504 p).
Proof. exact (MK_COMB (@lem7573268) (@lem7573267 p)). Qed.
Lemma lem7573270 (p : real -> real) : (term504 p) = (term487 p).
Proof. exact (SYM (@lem7573269 p)). Qed.
Lemma lem7573280 {A : Type'} (P : A -> Prop) (Q : Prop) : (term38 A P Q) = (term37 A P Q).
Proof. exact (EQ_MP (@lem7568033 A P Q) (@lem7568032 A P Q)). Qed.
Lemma lem7573281 (P : type1028) (Q : Prop) : (term505 P Q) = (term506 P Q).
Proof. exact (@lem7573280 (real -> real) P Q). Qed.
Lemma lem7573282 (p : real -> real) (m : nat) (c : nat -> real) : (term507 p m c) = (term508 p m c).
Proof. exact (@lem7573281 (term509 m c) (term449 p m c)). Qed.
Lemma lem7573283 (q : real -> real) (m : nat) (c : nat -> real) : (term510 m c q) = (q = (term490 m c)).
Proof. exact (eq_refl (term510 m c q)). Qed.
Lemma lem7573284 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7573285 (q : real -> real) (m : nat) (c : nat -> real) : (term511 m c q) = (term497 q m c).
Proof. exact (MK_COMB (@lem7573284) (@lem7573283 q m c)). Qed.
Lemma lem7573286 (p : real -> real) (m : nat) (c : nat -> real) : (term449 p m c) = (term449 p m c).
Proof. exact (eq_refl (term449 p m c)). Qed.
Lemma lem7573287 (q : real -> real) (p : real -> real) (m : nat) (c : nat -> real) : (term512 q p m c) = (term498 q p m c).
Proof. exact (MK_COMB (@lem7573285 q m c) (@lem7573286 p m c)). Qed.
Lemma lem7573288 (p : real -> real) (m : nat) (c : nat -> real) : (term513 p m c) = (term499 p m c).
Proof. exact (fun_ext (fun q : real -> real => @lem7573287 q p m c)). Qed.
Lemma lem7573289 : (@all (real -> real)) = (@all (real -> real)).
Proof. exact (eq_refl (@all (real -> real))). Qed.
Lemma lem7573290 (p : real -> real) (m : nat) (c : nat -> real) : (term507 p m c) = (term500 p m c).
Proof. exact (MK_COMB (@lem7573289) (@lem7573288 p m c)). Qed.
Lemma lem7573291 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7573292 (p : real -> real) (m : nat) (c : nat -> real) : (term514 p m c) = (term515 p m c).
Proof. exact (MK_COMB (@lem7573291) (@lem7573290 p m c)). Qed.
Lemma lem7573293 (q : real -> real) (m : nat) (c : nat -> real) : (term510 m c q) = (q = (term490 m c)).
Proof. exact (eq_refl (term510 m c q)). Qed.
Lemma lem7573294 (m : nat) (c : nat -> real) : (term516 m c) = (term509 m c).
Proof. exact (fun_ext (fun q : real -> real => @lem7573293 q m c)). Qed.
Lemma lem7573295 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem7573296 (m : nat) (c : nat -> real) : (term517 m c) = (term518 m c).
Proof. exact (MK_COMB (@lem7573295) (@lem7573294 m c)). Qed.
Lemma lem7573297 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7573298 (m : nat) (c : nat -> real) : (term519 m c) = (term520 m c).
Proof. exact (MK_COMB (@lem7573297) (@lem7573296 m c)). Qed.
Lemma lem7573299 (p : real -> real) (m : nat) (c : nat -> real) : (term449 p m c) = (term449 p m c).
Proof. exact (eq_refl (term449 p m c)). Qed.
Lemma lem7573300 (p : real -> real) (m : nat) (c : nat -> real) : (term508 p m c) = (term521 p m c).
Proof. exact (MK_COMB (@lem7573298 m c) (@lem7573299 p m c)). Qed.
Lemma lem7573301 (p : real -> real) (m : nat) (c : nat -> real) : ((term507 p m c) = (term508 p m c)) = ((term500 p m c) = (term521 p m c)).
Proof. exact (MK_COMB (@lem7573292 p m c) (@lem7573300 p m c)). Qed.
Lemma lem7573302 (p : real -> real) (m : nat) (c : nat -> real) : (term500 p m c) = (term521 p m c).
Proof. exact (EQ_MP (@lem7573301 p m c) (@lem7573282 p m c)). Qed.
Lemma lem7573306 {A : Type'} (a : A) : (term76 A a) = True.
Proof. exact (EQ_MP (@lem7568027 A a) (@lem7568026 A a)). Qed.
Lemma lem7573307 (a : real -> real) : (term522 a) = True.
Proof. exact (@lem7573306 (real -> real) a). Qed.
Lemma lem7573308 (m : nat) (c : nat -> real) : (term518 m c) = True.
Proof. exact (@lem7573307 (term490 m c)). Qed.
Lemma lem7573309 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7573310 (m : nat) (c : nat -> real) : (term520 m c) = (imp True).
Proof. exact (MK_COMB (@lem7573309) (@lem7573308 m c)). Qed.
Lemma lem7573311 (p : real -> real) (m : nat) (c : nat -> real) : (term449 p m c) = (term449 p m c).
Proof. exact (eq_refl (term449 p m c)). Qed.
Lemma lem7573312 (p : real -> real) (m : nat) (c : nat -> real) : (term521 p m c) = (term523 p m c).
Proof. exact (MK_COMB (@lem7573310 m c) (@lem7573311 p m c)). Qed.
Lemma lem7573314 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem7573315 (p : real -> real) (m : nat) (c : nat -> real) : (term523 p m c) = (term449 p m c).
Proof. exact (@lem7573314 (term449 p m c)). Qed.
Lemma lem7573316 (p : real -> real) (m : nat) (c : nat -> real) : (term521 p m c) = (term449 p m c).
Proof. exact (TRANS (@lem7573312 p m c) (@lem7573315 p m c)). Qed.
Lemma lem7573317 (p : real -> real) (m : nat) (c : nat -> real) : (term500 p m c) = (term449 p m c).
Proof. exact (TRANS (@lem7573302 p m c) (@lem7573316 p m c)). Qed.
Lemma lem7573318 (p : real -> real) (m : nat) : (term501 p m) = (term524 p m).
Proof. exact (fun_ext (fun c : nat -> real => @lem7573317 p m c)). Qed.
Lemma lem7573319 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7573320 (p : real -> real) (m : nat) : (term502 p m) = (term525 p m).
Proof. exact (MK_COMB (@lem7573319) (@lem7573318 p m)). Qed.
Lemma lem7573325 (p : real -> real) : (term503 p) = (term526 p).
Proof. exact (fun_ext (fun m : nat => @lem7573320 p m)). Qed.
Lemma lem7573326 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7573327 (p : real -> real) : (term504 p) = (term527 p).
Proof. exact (MK_COMB (@lem7573326) (@lem7573325 p)). Qed.
Lemma lem7573332 (p : real -> real) : (term527 p) = (term504 p).
Proof. exact (SYM (@lem7573327 p)). Qed.
Lemma lem7573334 (P : nat -> Prop) : term528 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem7573335 (p : real -> real) : term529 p.
Proof. exact (@lem7573334 (term526 p)). Qed.
Lemma lem7573336 (p : real -> real) : (term530 p) = (term531 p).
Proof. exact (eq_refl (term530 p)). Qed.
Lemma lem7573337 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7573338 (p : real -> real) : (term532 p) = (term533 p).
Proof. exact (MK_COMB (@lem7573337) (@lem7573336 p)). Qed.
Lemma lem7573339 (p : real -> real) (m : nat) : (term534 p m) = (term525 p m).
Proof. exact (eq_refl (term534 p m)). Qed.
Lemma lem7573340 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7573341 (p : real -> real) (m : nat) : (term535 p m) = (term536 p m).
Proof. exact (MK_COMB (@lem7573340) (@lem7573339 p m)). Qed.
Lemma lem7573342 (p : real -> real) (m : nat) : (term537 p m) = (term538 p m).
Proof. exact (eq_refl (term537 p m)). Qed.
Lemma lem7573343 (p : real -> real) (m : nat) : (term539 p m) = (term540 p m).
Proof. exact (MK_COMB (@lem7573341 p m) (@lem7573342 p m)). Qed.
Lemma lem7573344 (p : real -> real) : (term541 p) = (term542 p).
Proof. exact (fun_ext (fun m : nat => @lem7573343 p m)). Qed.
Lemma lem7573345 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7573346 (p : real -> real) : (term543 p) = (term544 p).
Proof. exact (MK_COMB (@lem7573345) (@lem7573344 p)). Qed.
Lemma lem7573347 (p : real -> real) : (term545 p) = (term546 p).
Proof. exact (MK_COMB (@lem7573338 p) (@lem7573346 p)). Qed.
Lemma lem7573348 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7573349 (p : real -> real) : (term547 p) = (term548 p).
Proof. exact (MK_COMB (@lem7573348) (@lem7573347 p)). Qed.
Lemma lem7573350 (p : real -> real) (m : nat) : (term534 p m) = (term525 p m).
Proof. exact (eq_refl (term534 p m)). Qed.
Lemma lem7573351 (p : real -> real) : (term549 p) = (term526 p).
Proof. exact (fun_ext (fun m : nat => @lem7573350 p m)). Qed.
Lemma lem7573352 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7573353 (p : real -> real) : (term550 p) = (term527 p).
Proof. exact (MK_COMB (@lem7573352) (@lem7573351 p)). Qed.
Lemma lem7573354 (p : real -> real) : (term529 p) = (term551 p).
Proof. exact (MK_COMB (@lem7573349 p) (@lem7573353 p)). Qed.
Lemma lem7573355 (p : real -> real) : term551 p.
Proof. exact (EQ_MP (@lem7573354 p) (@lem7573335 p)). Qed.
Lemma lem7573356 (p : real -> real) (m : nat) (h1 : term525 p m) : term525 p m.
Proof. exact (h1). Qed.
Lemma lem7573357 (p : real -> real) : term552 p.
Proof. exact (@lem7567593 p). Qed.
Lemma lem7573358 (p : real -> real) : (term552 p) = (term553 p).
Proof. exact (eq_refl (term552 p)). Qed.
Lemma lem7573359 (p : real -> real) : term553 p.
Proof. exact (EQ_MP (@lem7573358 p) (@lem7573357 p)). Qed.
Lemma lem7573360 (p : real -> real) (c : real) : term554 p c.
Proof. exact (@lem7573359 p c). Qed.
Lemma lem7573361 (p : real -> real) (c : real) : (term554 p c) = (term555 p c).
Proof. exact (eq_refl (term554 p c)). Qed.
Lemma lem7573362 (p : real -> real) (c : real) : term555 p c.
Proof. exact (EQ_MP (@lem7573361 p c) (@lem7573360 p c)). Qed.
Lemma lem7573363 (p : real -> real) (h1 : polynomial_function p) : polynomial_function p.
Proof. exact (h1). Qed.
Lemma lem7573364 (c : real) (p : real -> real) (h1 : polynomial_function p) : term556 p c.
Proof. exact (@lem7573362 p c (@lem7573363 p h1)). Qed.
Lemma lem7573365 (p : real -> real) (c : real) : (term556 p c) = ((term556 p c) = True).
Proof. exact (@lem7 (term556 p c)). Qed.
Lemma lem7573366 (c : real) (p : real -> real) (h1 : polynomial_function p) : (term556 p c) = True.
Proof. exact (EQ_MP (@lem7573365 p c) (@lem7573364 c p h1)). Qed.
Lemma lem7573377 (f : nat -> real) : term557 f.
Proof. exact (@lem7221565 f). Qed.
Lemma lem7573378 (f : nat -> real) : (term557 f) = (term558 f).
Proof. exact (eq_refl (term557 f)). Qed.
Lemma lem7573379 (f : nat -> real) : term558 f.
Proof. exact (EQ_MP (@lem7573378 f) (@lem7573377 f)). Qed.
Lemma lem7573380 (f : nat -> real) (n : nat) : term559 f n.
Proof. exact (@lem7573379 f n). Qed.
Lemma lem7573381 (f : nat -> real) (n : nat) : (term559 f n) = ((term560 n f) = (f n)).
Proof. exact (eq_refl (term559 f n)). Qed.
Lemma lem7573383 (p : real -> real) : (polynomial_function p) = ((polynomial_function p) = True).
Proof. exact (@lem7 (polynomial_function p)). Qed.
Lemma lem7573393 (f : nat -> real) (n : nat) : (term560 n f) = (f n).
Proof. exact (EQ_MP (@lem7573381 f n) (@lem7573380 f n)). Qed.
Lemma lem7573394 (c : nat -> real) (x : real) : (term561 c x) = (term562 c x).
Proof. exact (@lem7573393 (term563 c x) (NUMERAL 0)). Qed.
Lemma lem7573396 {A B : Type'} (f : A -> B) (y : A) : (term564 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7573397 (f : nat -> real) (y : nat) : (term565 f y) = (f y).
Proof. exact (@lem7573396 nat real f y). Qed.
Lemma lem7573398 (c : nat -> real) (x : real) : (term566 c x) = (term562 c x).
Proof. exact (@lem7573397 (term563 c x) (NUMERAL 0)). Qed.
Lemma lem7573399 (c : nat -> real) (x : real) (i : nat) : (term567 c x i) = (term568 c x i).
Proof. exact (eq_refl (term567 c x i)). Qed.
Lemma lem7573400 (c : nat -> real) (x : real) : (term569 c x) = (term563 c x).
Proof. exact (fun_ext (fun i : nat => @lem7573399 c x i)). Qed.
Lemma lem7573401 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem7573402 (c : nat -> real) (x : real) : (term566 c x) = (term562 c x).
Proof. exact (MK_COMB (@lem7573400 c x) (@lem7573401)). Qed.
Lemma lem7573403 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7573404 (c : nat -> real) (x : real) : (term570 c x) = (term571 c x).
Proof. exact (MK_COMB (@lem7573403) (@lem7573402 c x)). Qed.
Lemma lem7573405 (c : nat -> real) (x : real) : (term562 c x) = (term572 c x).
Proof. exact (eq_refl (term562 c x)). Qed.
Lemma lem7573406 (c : nat -> real) (x : real) : ((term566 c x) = (term562 c x)) = ((term562 c x) = (term572 c x)).
Proof. exact (MK_COMB (@lem7573404 c x) (@lem7573405 c x)). Qed.
Lemma lem7573407 (c : nat -> real) (x : real) : (term562 c x) = (term572 c x).
Proof. exact (EQ_MP (@lem7573406 c x) (@lem7573398 c x)). Qed.
Lemma lem7573409 (x : real) : (term573 x) = term574.
Proof. exact (EQ_MP (@lem1344311 x) (@lem1344310 x)). Qed.
Lemma lem7573410 (c : nat -> real) : (term575 c) = (term575 c).
Proof. exact (eq_refl (term575 c)). Qed.
Lemma lem7573411 (x : real) (c : nat -> real) : (term572 c x) = (term576 c).
Proof. exact (MK_COMB (@lem7573410 c) (@lem7573409 x)). Qed.
Lemma lem7573412 (x : real) (c : nat -> real) : (term562 c x) = (term576 c).
Proof. exact (TRANS (@lem7573407 c x) (@lem7573411 x c)). Qed.
Lemma lem7573413 (x : real) (c : nat -> real) : (term561 c x) = (term576 c).
Proof. exact (TRANS (@lem7573394 c x) (@lem7573412 x c)). Qed.
Lemma lem7573414 (p : real -> real) (x : real) : (term444 p x) = (term444 p x).
Proof. exact (eq_refl (term444 p x)). Qed.
Lemma lem7573415 (p : real -> real) (x : real) (c : nat -> real) : (term577 p c x) = (term578 p x c).
Proof. exact (MK_COMB (@lem7573414 p x) (@lem7573413 x c)). Qed.
Lemma lem7573416 (p : real -> real) (c : nat -> real) : (term579 p c) = (term580 p c).
Proof. exact (fun_ext (fun x : real => @lem7573415 p x c)). Qed.
Lemma lem7573417 : polynomial_function = polynomial_function.
Proof. exact (eq_refl polynomial_function). Qed.
Lemma lem7573418 (p : real -> real) (c : nat -> real) : (term581 p c) = (term582 p c).
Proof. exact (MK_COMB (@lem7573417) (@lem7573416 p c)). Qed.
Lemma lem7573420 (p : real -> real) (c : real) : term583 p c.
Proof. exact (fun h0 : polynomial_function p => @lem7573366 c p h0). Qed.
Lemma lem7573421 (p : real -> real) (c : nat -> real) : term584 p c.
Proof. exact (@lem7573420 p (term576 c)). Qed.
Lemma lem7573423 (p : real -> real) (h1 : polynomial_function p) : (polynomial_function p) = True.
Proof. exact (EQ_MP (@lem7573383 p) (@lem7568980 p h1)). Qed.
Lemma lem7573424 (p : real -> real) (h1 : polynomial_function p) : True = (polynomial_function p).
Proof. exact (SYM (@lem7573423 p h1)). Qed.
Lemma lem7573425 (p : real -> real) (h1 : polynomial_function p) : polynomial_function p.
Proof. exact (EQ_MP (@lem7573424 p h1) (@lem0)). Qed.
Lemma lem7573426 (c : nat -> real) (p : real -> real) (h1 : polynomial_function p) : (term582 p c) = True.
Proof. exact (@lem7573421 p c (@lem7573425 p h1)). Qed.
Lemma lem7573427 (c : nat -> real) (p : real -> real) (h1 : polynomial_function p) : (term581 p c) = True.
Proof. exact (TRANS (@lem7573418 p c) (@lem7573426 c p h1)). Qed.
Lemma lem7573428 (p : real -> real) (h1 : polynomial_function p) : (term585 p) = term586.
Proof. exact (fun_ext (fun c : nat -> real => @lem7573427 c p h1)). Qed.
Lemma lem7573429 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7573430 (p : real -> real) (h1 : polynomial_function p) : (term531 p) = term587.
Proof. exact (MK_COMB (@lem7573429) (@lem7573428 p h1)). Qed.
Lemma lem7573432 {A : Type'} (t : Prop) : (term588 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7573433 (t : Prop) : (term589 t) = t.
Proof. exact (@lem7573432 (nat -> real) t). Qed.
Lemma lem7573434 : term587 = True.
Proof. exact (@lem7573433 True). Qed.
Lemma lem7573435 (p : real -> real) (h1 : polynomial_function p) : (term531 p) = True.
Proof. exact (TRANS (@lem7573430 p h1) (@lem7573434)). Qed.
Lemma lem7573436 (p : real -> real) (h1 : polynomial_function p) : True = (term531 p).
Proof. exact (SYM (@lem7573435 p h1)). Qed.
Lemma lem7573437 (p : real -> real) (h1 : polynomial_function p) : term531 p.
Proof. exact (EQ_MP (@lem7573436 p h1) (@lem0)). Qed.
Lemma lem7573598 (m : nat) (n : nat) (f : nat -> real) : term31 m n f.
Proof. exact (fun h0 : Peano.le m n => @lem7568018 f m n h0). Qed.
Lemma lem7573599 (m : nat) (c : nat -> real) (x : real) : term590 m c x.
Proof. exact (@lem7573598 (NUMERAL 0) (S m) (term563 c x)). Qed.
Lemma lem7573601 (n : nat) : (term25 n) = True.
Proof. exact (EQ_MP (@lem7568006 n) (@lem7568005 n)). Qed.
Lemma lem7573602 (m : nat) : (term591 m) = True.
Proof. exact (@lem7573601 (S m)). Qed.
Lemma lem7573603 (m : nat) : True = (term591 m).
Proof. exact (SYM (@lem7573602 m)). Qed.
Lemma lem7573604 (m : nat) : term591 m.
Proof. exact (EQ_MP (@lem7573603 m) (@lem0)). Qed.
Lemma lem7573605 (m : nat) (c : nat -> real) (x : real) : (term592 m c x) = (term593 m c x).
Proof. exact (@lem7573599 m c x (@lem7573604 m)). Qed.
Lemma lem7573607 {A B : Type'} (f : A -> B) (y : A) : (term564 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7573608 (f : nat -> real) (y : nat) : (term565 f y) = (f y).
Proof. exact (@lem7573607 nat real f y). Qed.
Lemma lem7573609 (c : nat -> real) (x : real) : (term566 c x) = (term562 c x).
Proof. exact (@lem7573608 (term563 c x) (NUMERAL 0)). Qed.
Lemma lem7573610 (c : nat -> real) (x : real) (i : nat) : (term567 c x i) = (term568 c x i).
Proof. exact (eq_refl (term567 c x i)). Qed.
Lemma lem7573611 (c : nat -> real) (x : real) : (term569 c x) = (term563 c x).
Proof. exact (fun_ext (fun i : nat => @lem7573610 c x i)). Qed.
Lemma lem7573612 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem7573613 (c : nat -> real) (x : real) : (term566 c x) = (term562 c x).
Proof. exact (MK_COMB (@lem7573611 c x) (@lem7573612)). Qed.
Lemma lem7573614 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7573615 (c : nat -> real) (x : real) : (term570 c x) = (term571 c x).
Proof. exact (MK_COMB (@lem7573614) (@lem7573613 c x)). Qed.
Lemma lem7573616 (c : nat -> real) (x : real) : (term562 c x) = (term572 c x).
Proof. exact (eq_refl (term562 c x)). Qed.
Lemma lem7573617 (c : nat -> real) (x : real) : ((term566 c x) = (term562 c x)) = ((term562 c x) = (term572 c x)).
Proof. exact (MK_COMB (@lem7573615 c x) (@lem7573616 c x)). Qed.
Lemma lem7573618 (c : nat -> real) (x : real) : (term562 c x) = (term572 c x).
Proof. exact (EQ_MP (@lem7573617 c x) (@lem7573609 c x)). Qed.
Lemma lem7573619 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7573620 (c : nat -> real) (x : real) : (term594 c x) = (term595 c x).
Proof. exact (MK_COMB (@lem7573619) (@lem7573618 c x)). Qed.
Lemma lem7573745 (m : nat) : (S m) = (term74 m).
Proof. exact (EQ_MP (@lem7568001 m) (@lem7568000 m)). Qed.
Lemma lem7573746 : term596 = term596.
Proof. exact (eq_refl term596). Qed.
Lemma lem7573747 (m : nat) : (term597 m) = (term598 m).
Proof. exact (MK_COMB (@lem7573746) (@lem7573745 m)). Qed.
Lemma lem7573748 : (@sum nat) = (@sum nat).
Proof. exact (eq_refl (@sum nat)). Qed.
Lemma lem7573749 (m : nat) : (term599 m) = (term600 m).
Proof. exact (MK_COMB (@lem7573748) (@lem7573747 m)). Qed.
Lemma lem7573750 (c : nat -> real) (x : real) : (term563 c x) = (term563 c x).
Proof. exact (eq_refl (term563 c x)). Qed.
Lemma lem7573751 (m : nat) (c : nat -> real) (x : real) : (term601 m c x) = (term602 m c x).
Proof. exact (MK_COMB (@lem7573749 m) (@lem7573750 c x)). Qed.
Lemma lem7573872 (m : nat) (c : nat -> real) (x : real) : (term593 m c x) = (term603 m c x).
Proof. exact (MK_COMB (@lem7573620 c x) (@lem7573751 m c x)). Qed.
Lemma lem7573993 (m : nat) (c : nat -> real) (x : real) : (term592 m c x) = (term603 m c x).
Proof. exact (TRANS (@lem7573605 m c x) (@lem7573872 m c x)). Qed.
Lemma lem7573994 (p : real -> real) (x : real) : (term444 p x) = (term444 p x).
Proof. exact (eq_refl (term444 p x)). Qed.
Lemma lem7573995 (p : real -> real) (m : nat) (c : nat -> real) (x : real) : (term604 p m c x) = (term605 p m c x).
Proof. exact (MK_COMB (@lem7573994 p x) (@lem7573993 m c x)). Qed.
Lemma lem7574116 (p : real -> real) (m : nat) (c : nat -> real) : (term606 p m c) = (term607 p m c).
Proof. exact (fun_ext (fun x : real => @lem7573995 p m c x)). Qed.
Lemma lem7574237 : polynomial_function = polynomial_function.
Proof. exact (eq_refl polynomial_function). Qed.
Lemma lem7574238 (p : real -> real) (m : nat) (c : nat -> real) : (term608 p m c) = (term609 p m c).
Proof. exact (MK_COMB (@lem7574237) (@lem7574116 p m c)). Qed.
Lemma lem7574359 (p : real -> real) (m : nat) (c : nat -> real) : (term609 p m c) = (term608 p m c).
Proof. exact (SYM (@lem7574238 p m c)). Qed.
Lemma lem7574361 (y : real) (x : real) (z : real) : (term71 x y z) = (term72 y x z).
Proof. exact (EQ_MP (@lem7567998 y x z) (@lem7567997 y x z)). Qed.
Lemma lem7574362 (p : real -> real) (m : nat) (c : nat -> real) (x : real) : (term605 p m c x) = (term610 p m c x).
Proof. exact (@lem7574361 (term572 c x) (p x) (term602 m c x)). Qed.
Lemma lem7574364 (x : real) : (term573 x) = term574.
Proof. exact (EQ_MP (@lem1344311 x) (@lem1344310 x)). Qed.
Lemma lem7574365 (c : nat -> real) : (term575 c) = (term575 c).
Proof. exact (eq_refl (term575 c)). Qed.
Lemma lem7574366 (x : real) (c : nat -> real) : (term572 c x) = (term576 c).
Proof. exact (MK_COMB (@lem7574365 c) (@lem7574364 x)). Qed.
Lemma lem7574367 (p : real -> real) (x : real) : (term444 p x) = (term444 p x).
Proof. exact (eq_refl (term444 p x)). Qed.
Lemma lem7574368 (p : real -> real) (x : real) (c : nat -> real) : (term611 p c x) = (term578 p x c).
Proof. exact (MK_COMB (@lem7574367 p x) (@lem7574366 x c)). Qed.
Lemma lem7574369 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7574370 (p : real -> real) (x : real) (c : nat -> real) : (term612 p c x) = (term613 p x c).
Proof. exact (MK_COMB (@lem7574369) (@lem7574368 p x c)). Qed.
Lemma lem7574371 (p : real -> real) (m : nat) (c : nat -> real) (x : real) : (term614 p m c x) = (term614 p m c x).
Proof. exact (eq_refl (term614 p m c x)). Qed.
Lemma lem7574372 (p : real -> real) (m : nat) (c : nat -> real) (x : real) : (term610 p m c x) = (term615 p m c x).
Proof. exact (MK_COMB (@lem7574370 p x c) (@lem7574371 p m c x)). Qed.
Lemma lem7574373 (p : real -> real) (m : nat) (c : nat -> real) (x : real) : (term605 p m c x) = (term615 p m c x).
Proof. exact (TRANS (@lem7574362 p m c x) (@lem7574372 p m c x)). Qed.
Lemma lem7574374 (p : real -> real) (m : nat) (c : nat -> real) : (term607 p m c) = (term616 p m c).
Proof. exact (fun_ext (fun x : real => @lem7574373 p m c x)). Qed.
Lemma lem7574375 : polynomial_function = polynomial_function.
Proof. exact (eq_refl polynomial_function). Qed.
Lemma lem7574376 (p : real -> real) (m : nat) (c : nat -> real) : (term609 p m c) = (term617 p m c).
Proof. exact (MK_COMB (@lem7574375) (@lem7574374 p m c)). Qed.
Lemma lem7574377 (p : real -> real) (m : nat) (c : nat -> real) : (term617 p m c) = (term609 p m c).
Proof. exact (SYM (@lem7574376 p m c)). Qed.
Lemma lem7574379 (p : real -> real) (q : real -> real) : term61 p q.
Proof. exact (EQ_MP (@lem7567984 p q) (@lem7567983 p q)). Qed.
Lemma lem7574380 (p : real -> real) (m : nat) (c : nat -> real) : term618 p m c.
Proof. exact (@lem7574379 (term580 p c) (term619 p m c)). Qed.
Lemma lem7574381 (p : real -> real) (x : real) (c : nat -> real) : (term620 p c x) = (term578 p x c).
Proof. exact (eq_refl (term620 p c x)). Qed.
Lemma lem7574382 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7574383 (p : real -> real) (x : real) (c : nat -> real) : (term621 p c x) = (term613 p x c).
Proof. exact (MK_COMB (@lem7574382) (@lem7574381 p x c)). Qed.
Lemma lem7574384 (p : real -> real) (m : nat) (c : nat -> real) (x : real) : (term622 p m c x) = (term614 p m c x).
Proof. exact (eq_refl (term622 p m c x)). Qed.
Lemma lem7574385 (p : real -> real) (m : nat) (c : nat -> real) (x : real) : (term623 p m c x) = (term615 p m c x).
Proof. exact (MK_COMB (@lem7574383 p x c) (@lem7574384 p m c x)). Qed.
Lemma lem7574386 (p : real -> real) (m : nat) (c : nat -> real) : (term624 p m c) = (term616 p m c).
Proof. exact (fun_ext (fun x : real => @lem7574385 p m c x)). Qed.
Lemma lem7574387 : polynomial_function = polynomial_function.
Proof. exact (eq_refl polynomial_function). Qed.
Lemma lem7574388 (p : real -> real) (m : nat) (c : nat -> real) : (term625 p m c) = (term617 p m c).
Proof. exact (MK_COMB (@lem7574387) (@lem7574386 p m c)). Qed.
Lemma lem7574389 (p : real -> real) (m : nat) (c : nat -> real) : (term626 p m c) = (term626 p m c).
Proof. exact (eq_refl (term626 p m c)). Qed.
Lemma lem7574390 (p : real -> real) (m : nat) (c : nat -> real) : (term618 p m c) = (term627 p m c).
Proof. exact (MK_COMB (@lem7574389 p m c) (@lem7574388 p m c)). Qed.
Lemma lem7574391 (p : real -> real) (m : nat) (c : nat -> real) : term627 p m c.
Proof. exact (EQ_MP (@lem7574390 p m c) (@lem7574380 p m c)). Qed.
Lemma lem7574392 (p : real -> real) : term552 p.
Proof. exact (@lem7567593 p). Qed.
Lemma lem7574393 (p : real -> real) : (term552 p) = (term553 p).
Proof. exact (eq_refl (term552 p)). Qed.
Lemma lem7574394 (p : real -> real) : term553 p.
Proof. exact (EQ_MP (@lem7574393 p) (@lem7574392 p)). Qed.
Lemma lem7574395 (p : real -> real) (c : real) : term554 p c.
Proof. exact (@lem7574394 p c). Qed.
Lemma lem7574396 (p : real -> real) (c : real) : (term554 p c) = (term555 p c).
Proof. exact (eq_refl (term554 p c)). Qed.
Lemma lem7574397 (p : real -> real) (c : real) : term555 p c.
Proof. exact (EQ_MP (@lem7574396 p c) (@lem7574395 p c)). Qed.
Lemma lem7574398 (p : real -> real) (h1 : polynomial_function p) : polynomial_function p.
Proof. exact (h1). Qed.
Lemma lem7574399 (c : real) (p : real -> real) (h1 : polynomial_function p) : term556 p c.
Proof. exact (@lem7574397 p c (@lem7574398 p h1)). Qed.
Lemma lem7574400 (p : real -> real) (c : real) : (term556 p c) = ((term556 p c) = True).
Proof. exact (@lem7 (term556 p c)). Qed.
Lemma lem7574401 (c : real) (p : real -> real) (h1 : polynomial_function p) : (term556 p c) = True.
Proof. exact (EQ_MP (@lem7574400 p c) (@lem7574399 c p h1)). Qed.
Lemma lem7574407 (p : real -> real) : (polynomial_function p) = ((polynomial_function p) = True).
Proof. exact (@lem7 (polynomial_function p)). Qed.
Lemma lem7574417 (p : real -> real) (c : real) : term583 p c.
Proof. exact (fun h0 : polynomial_function p => @lem7574401 c p h0). Qed.
Lemma lem7574418 (p : real -> real) (c : nat -> real) : term584 p c.
Proof. exact (@lem7574417 p (term576 c)). Qed.
Lemma lem7574420 (p : real -> real) (h1 : polynomial_function p) : (polynomial_function p) = True.
Proof. exact (EQ_MP (@lem7574407 p) (@lem7568980 p h1)). Qed.
Lemma lem7574421 (p : real -> real) (h1 : polynomial_function p) : True = (polynomial_function p).
Proof. exact (SYM (@lem7574420 p h1)). Qed.
Lemma lem7574422 (p : real -> real) (h1 : polynomial_function p) : polynomial_function p.
Proof. exact (EQ_MP (@lem7574421 p h1) (@lem0)). Qed.
Lemma lem7574423 (c : nat -> real) (p : real -> real) (h1 : polynomial_function p) : (term582 p c) = True.
Proof. exact (@lem7574418 p c (@lem7574422 p h1)). Qed.
Lemma lem7574424 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7574425 (c : nat -> real) (p : real -> real) (h1 : polynomial_function p) : (term628 p c) = (and True).
Proof. exact (MK_COMB (@lem7574424) (@lem7574423 c p h1)). Qed.
Lemma lem7574544 (p : real -> real) (m : nat) (c : nat -> real) : (term629 p m c) = (term629 p m c).
Proof. exact (eq_refl (term629 p m c)). Qed.
Lemma lem7574545 (m : nat) (c : nat -> real) (p : real -> real) (h1 : polynomial_function p) : (term630 p m c) = (term631 p m c).
Proof. exact (MK_COMB (@lem7574425 c p h1) (@lem7574544 p m c)). Qed.
Lemma lem7574547 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7574548 (p : real -> real) (m : nat) (c : nat -> real) : (term631 p m c) = (term629 p m c).
Proof. exact (@lem7574547 (term629 p m c)). Qed.
Lemma lem7574667 (m : nat) (c : nat -> real) (p : real -> real) (h1 : polynomial_function p) : (term630 p m c) = (term629 p m c).
Proof. exact (TRANS (@lem7574545 m c p h1) (@lem7574548 p m c)). Qed.
Lemma lem7574668 (m : nat) (c : nat -> real) (p : real -> real) (h1 : polynomial_function p) : (term629 p m c) = (term630 p m c).
Proof. exact (SYM (@lem7574667 m c p h1)). Qed.
Lemma lem7574670 (m : nat) (n : nat) (f : nat -> real) : (term55 m n f) = (term56 m n f).
Proof. exact (EQ_MP (@lem7567961 m n f) (@lem7567960 m f n)). Qed.
Lemma lem7574671 (m : nat) (c : nat -> real) (x : real) : (term602 m c x) = (term632 m c x).
Proof. exact (@lem7574670 (NUMERAL 0) m (term563 c x)). Qed.
Lemma lem7574673 {A B : Type'} (f : A -> B) (y : A) : (term564 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7574674 (f : nat -> real) (y : nat) : (term565 f y) = (f y).
Proof. exact (@lem7574673 nat real f y). Qed.
Lemma lem7574675 (c : nat -> real) (x : real) (i : nat) : (term633 c x i) = (term634 c x i).
Proof. exact (@lem7574674 (term563 c x) (term74 i)). Qed.
Lemma lem7574676 (c : nat -> real) (x : real) (i : nat) : (term567 c x i) = (term568 c x i).
Proof. exact (eq_refl (term567 c x i)). Qed.
Lemma lem7574677 (c : nat -> real) (x : real) : (term569 c x) = (term563 c x).
Proof. exact (fun_ext (fun i : nat => @lem7574676 c x i)). Qed.
Lemma lem7574678 (i : nat) : (term74 i) = (term74 i).
Proof. exact (eq_refl (term74 i)). Qed.
Lemma lem7574679 (c : nat -> real) (x : real) (i : nat) : (term633 c x i) = (term634 c x i).
Proof. exact (MK_COMB (@lem7574677 c x) (@lem7574678 i)). Qed.
Lemma lem7574680 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7574681 (c : nat -> real) (x : real) (i : nat) : (term635 c x i) = (term636 c x i).
Proof. exact (MK_COMB (@lem7574680) (@lem7574679 c x i)). Qed.
Lemma lem7574682 (c : nat -> real) (x : real) (i : nat) : (term634 c x i) = (term637 c x i).
Proof. exact (eq_refl (term634 c x i)). Qed.
Lemma lem7574683 (c : nat -> real) (x : real) (i : nat) : ((term633 c x i) = (term634 c x i)) = ((term634 c x i) = (term637 c x i)).
Proof. exact (MK_COMB (@lem7574681 c x i) (@lem7574682 c x i)). Qed.
Lemma lem7574684 (c : nat -> real) (x : real) (i : nat) : (term634 c x i) = (term637 c x i).
Proof. exact (EQ_MP (@lem7574683 c x i) (@lem7574675 c x i)). Qed.
Lemma lem7574685 (c : nat -> real) (x : real) : (term638 c x) = (term639 c x).
Proof. exact (fun_ext (fun i : nat => @lem7574684 c x i)). Qed.
Lemma lem7574686 (m : nat) : (term640 m) = (term640 m).
Proof. exact (eq_refl (term640 m)). Qed.
Lemma lem7574687 (m : nat) (c : nat -> real) (x : real) : (term632 m c x) = (term641 m c x).
Proof. exact (MK_COMB (@lem7574686 m) (@lem7574685 c x)). Qed.
Lemma lem7574688 (m : nat) (c : nat -> real) (x : real) : (term602 m c x) = (term641 m c x).
Proof. exact (TRANS (@lem7574671 m c x) (@lem7574687 m c x)). Qed.
Lemma lem7574689 (p : real -> real) (x : real) : (term444 p x) = (term444 p x).
Proof. exact (eq_refl (term444 p x)). Qed.
Lemma lem7574690 (p : real -> real) (m : nat) (c : nat -> real) (x : real) : (term614 p m c x) = (term642 p m c x).
Proof. exact (MK_COMB (@lem7574689 p x) (@lem7574688 m c x)). Qed.
Lemma lem7574691 (p : real -> real) (m : nat) (c : nat -> real) : (term619 p m c) = (term643 p m c).
Proof. exact (fun_ext (fun x : real => @lem7574690 p m c x)). Qed.
Lemma lem7574692 : polynomial_function = polynomial_function.
Proof. exact (eq_refl polynomial_function). Qed.
Lemma lem7574693 (p : real -> real) (m : nat) (c : nat -> real) : (term629 p m c) = (term644 p m c).
Proof. exact (MK_COMB (@lem7574692) (@lem7574691 p m c)). Qed.
Lemma lem7574694 (p : real -> real) (m : nat) (c : nat -> real) : (term644 p m c) = (term629 p m c).
Proof. exact (SYM (@lem7574693 p m c)). Qed.
Lemma lem7574713 (m : nat) (x : real) (n : nat) : (term19 x m n) = (term20 m x n).
Proof. exact (EQ_MP (@lem7567949 m x n) (@lem7567948 m x n)). Qed.
Lemma lem7574714 (i : nat) (x : real) : (term645 x i) = (term646 i x).
Proof. exact (@lem7574713 i x term22). Qed.
Lemma lem7574716 (x : real) : (term49 x) = x.
Proof. exact (EQ_MP (@lem7567940 x) (@lem7567939 x)). Qed.
Lemma lem7574717 (x : real) (i : nat) : (term647 x i) = (term647 x i).
Proof. exact (eq_refl (term647 x i)). Qed.
Lemma lem7574718 (i : nat) (x : real) : (term646 i x) = (term648 i x).
Proof. exact (MK_COMB (@lem7574717 x i) (@lem7574716 x)). Qed.
Lemma lem7574719 (i : nat) (x : real) : (term645 x i) = (term648 i x).
Proof. exact (TRANS (@lem7574714 i x) (@lem7574718 i x)). Qed.
Lemma lem7574720 (c : nat -> real) (i : nat) : (term649 c i) = (term649 c i).
Proof. exact (eq_refl (term649 c i)). Qed.
Lemma lem7574721 (c : nat -> real) (i : nat) (x : real) : (term637 c x i) = (term650 c i x).
Proof. exact (MK_COMB (@lem7574720 c i) (@lem7574719 i x)). Qed.
Lemma lem7574723 (x : real) (y : real) (z : real) : (term12 x y z) = (term13 x y z).
Proof. exact (EQ_MP (@lem7567937 x y z) (@lem7567936 x y z)). Qed.
Lemma lem7574724 (c : nat -> real) (i : nat) (x : real) : (term650 c i x) = (term651 c i x).
Proof. exact (@lem7574723 (term652 c i) (real_pow x i) x). Qed.
Lemma lem7574725 (c : nat -> real) (i : nat) (x : real) : (term637 c x i) = (term651 c i x).
Proof. exact (TRANS (@lem7574721 c i x) (@lem7574724 c i x)). Qed.
Lemma lem7574726 (c : nat -> real) (x : real) : (term639 c x) = (term653 c x).
Proof. exact (fun_ext (fun i : nat => @lem7574725 c i x)). Qed.
Lemma lem7574727 (m : nat) : (term640 m) = (term640 m).
Proof. exact (eq_refl (term640 m)). Qed.
Lemma lem7574728 (m : nat) (c : nat -> real) (x : real) : (term641 m c x) = (term654 m c x).
Proof. exact (MK_COMB (@lem7574727 m) (@lem7574726 c x)). Qed.
Lemma lem7574730 {A : Type'} (s : A -> Prop) (f : A -> real) (c : real) : (term5 A s f c) = (term6 A s f c).
Proof. exact (EQ_MP (@lem7567928 A s f c) (@lem7567927 A f c s)). Qed.
Lemma lem7574731 (s : nat -> Prop) (f : nat -> real) (c : real) : (term655 s f c) = (term656 s f c).
Proof. exact (@lem7574730 nat s f c). Qed.
Lemma lem7574732 (m : nat) (c : nat -> real) (x : real) : (term657 m c x) = (term658 m c x).
Proof. exact (@lem7574731 (term659 m) (term660 c x) x). Qed.
Lemma lem7574733 (c : nat -> real) (x : real) (i : nat) : (term661 c x i) = (term662 c x i).
Proof. exact (eq_refl (term661 c x i)). Qed.
Lemma lem7574734 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7574735 (c : nat -> real) (x : real) (i : nat) : (term663 c x i) = (term664 c x i).
Proof. exact (MK_COMB (@lem7574734) (@lem7574733 c x i)). Qed.
Lemma lem7574736 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7574737 (c : nat -> real) (i : nat) (x : real) : (term665 c i x) = (term651 c i x).
Proof. exact (MK_COMB (@lem7574735 c x i) (@lem7574736 x)). Qed.
Lemma lem7574738 (c : nat -> real) (x : real) : (term666 c x) = (term653 c x).
Proof. exact (fun_ext (fun i : nat => @lem7574737 c i x)). Qed.
Lemma lem7574739 (m : nat) : (term640 m) = (term640 m).
Proof. exact (eq_refl (term640 m)). Qed.
Lemma lem7574740 (m : nat) (c : nat -> real) (x : real) : (term657 m c x) = (term654 m c x).
Proof. exact (MK_COMB (@lem7574739 m) (@lem7574738 c x)). Qed.
Lemma lem7574741 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7574742 (m : nat) (c : nat -> real) (x : real) : (term667 m c x) = (term668 m c x).
Proof. exact (MK_COMB (@lem7574741) (@lem7574740 m c x)). Qed.
Lemma lem7574743 (m : nat) (c : nat -> real) (x : real) : (term658 m c x) = (term658 m c x).
Proof. exact (eq_refl (term658 m c x)). Qed.
Lemma lem7574744 (m : nat) (c : nat -> real) (x : real) : ((term657 m c x) = (term658 m c x)) = ((term654 m c x) = (term658 m c x)).
Proof. exact (MK_COMB (@lem7574742 m c x) (@lem7574743 m c x)). Qed.
Lemma lem7574745 (m : nat) (c : nat -> real) (x : real) : (term654 m c x) = (term658 m c x).
Proof. exact (EQ_MP (@lem7574744 m c x) (@lem7574732 m c x)). Qed.
Lemma lem7574763 (m : nat) (c : nat -> real) (x : real) : (term641 m c x) = (term658 m c x).
Proof. exact (TRANS (@lem7574728 m c x) (@lem7574745 m c x)). Qed.
Lemma lem7574764 (p : real -> real) (x : real) : (term444 p x) = (term444 p x).
Proof. exact (eq_refl (term444 p x)). Qed.
Lemma lem7574765 (p : real -> real) (m : nat) (c : nat -> real) (x : real) : (term642 p m c x) = (term669 p m c x).
Proof. exact (MK_COMB (@lem7574764 p x) (@lem7574763 m c x)). Qed.
Lemma lem7574767 (x : real) (y : real) (z : real) : (term12 x y z) = (term13 x y z).
Proof. exact (EQ_MP (@lem7567937 x y z) (@lem7567936 x y z)). Qed.
Lemma lem7574768 (p : real -> real) (m : nat) (c : nat -> real) (x : real) : (term669 p m c x) = (term670 p m c x).
Proof. exact (@lem7574767 (p x) (term671 m c x) x). Qed.
Lemma lem7574786 (p : real -> real) (m : nat) (c : nat -> real) (x : real) : (term642 p m c x) = (term670 p m c x).
Proof. exact (TRANS (@lem7574765 p m c x) (@lem7574768 p m c x)). Qed.
Lemma lem7574787 (p : real -> real) (m : nat) (c : nat -> real) : (term643 p m c) = (term672 p m c).
Proof. exact (fun_ext (fun x : real => @lem7574786 p m c x)). Qed.
Lemma lem7574788 : polynomial_function = polynomial_function.
Proof. exact (eq_refl polynomial_function). Qed.
Lemma lem7574789 (p : real -> real) (m : nat) (c : nat -> real) : (term644 p m c) = (term673 p m c).
Proof. exact (MK_COMB (@lem7574788) (@lem7574787 p m c)). Qed.
Lemma lem7574790 (p : real -> real) (m : nat) (c : nat -> real) : (term673 p m c) = (term644 p m c).
Proof. exact (SYM (@lem7574789 p m c)). Qed.
Lemma lem7574791 (c : nat -> real) (p : real -> real) (m : nat) (h1 : term525 p m) : term674 p m c.
Proof. exact (@lem7573356 p m h1 (term675 c)). Qed.
Lemma lem7574792 (p : real -> real) (m : nat) (c : nat -> real) : (term674 p m c) = (term676 p m c).
Proof. exact (eq_refl (term674 p m c)). Qed.
Lemma lem7574793 (c : nat -> real) (p : real -> real) (m : nat) (h1 : term525 p m) : term676 p m c.
Proof. exact (EQ_MP (@lem7574792 p m c) (@lem7574791 c p m h1)). Qed.
Lemma lem7574794 (p : real -> real) (m : nat) (c : nat -> real) (q : real -> real) (h1 : (term45 p m c) = q) : (term45 p m c) = q.
Proof. exact (h1). Qed.
Lemma lem7574804 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term44 A B f g).
Proof. exact (EQ_MP (@lem7567911 A B f g) (@lem7567910 A B f g)). Qed.
Lemma lem7574805 (f : real -> real) (g : real -> real) : (f = g) = (term488 f g).
Proof. exact (@lem7574804 real real f g). Qed.
Lemma lem7574806 (p : real -> real) (m : nat) (c : nat -> real) (q : real -> real) : ((term45 p m c) = q) = (term677 p m c q).
Proof. exact (@lem7574805 (term45 p m c) q). Qed.
Lemma lem7574816 {A B : Type'} (f : A -> B) (y : A) : (term564 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7574817 (f : real -> real) (y : real) : (term678 f y) = (f y).
Proof. exact (@lem7574816 real real f y). Qed.
Lemma lem7574818 (p : real -> real) (m : nat) (c : nat -> real) (x : real) : (term679 p m c x) = (term680 p m c x).
Proof. exact (@lem7574817 (term45 p m c) x). Qed.
Lemma lem7574819 (p : real -> real) (m : nat) (c : nat -> real) (x : real) : (term680 p m c x) = (term681 p m c x).
Proof. exact (eq_refl (term680 p m c x)). Qed.
Lemma lem7574820 (p : real -> real) (m : nat) (c : nat -> real) : (term682 p m c) = (term45 p m c).
Proof. exact (fun_ext (fun x : real => @lem7574819 p m c x)). Qed.
Lemma lem7574821 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7574822 (p : real -> real) (m : nat) (c : nat -> real) (x : real) : (term679 p m c x) = (term680 p m c x).
Proof. exact (MK_COMB (@lem7574820 p m c) (@lem7574821 x)). Qed.
Lemma lem7574823 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7574824 (p : real -> real) (m : nat) (c : nat -> real) (x : real) : (term683 p m c x) = (term684 p m c x).
Proof. exact (MK_COMB (@lem7574823) (@lem7574822 p m c x)). Qed.
Lemma lem7574825 (p : real -> real) (m : nat) (c : nat -> real) (x : real) : (term680 p m c x) = (term681 p m c x).
Proof. exact (eq_refl (term680 p m c x)). Qed.
Lemma lem7574826 (p : real -> real) (m : nat) (c : nat -> real) (x : real) : ((term679 p m c x) = (term680 p m c x)) = ((term680 p m c x) = (term681 p m c x)).
Proof. exact (MK_COMB (@lem7574824 p m c x) (@lem7574825 p m c x)). Qed.
Lemma lem7574827 (p : real -> real) (m : nat) (c : nat -> real) (x : real) : (term680 p m c x) = (term681 p m c x).
Proof. exact (EQ_MP (@lem7574826 p m c x) (@lem7574818 p m c x)). Qed.
Lemma lem7574828 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7574829 (p : real -> real) (m : nat) (c : nat -> real) (x : real) : (term684 p m c x) = (term685 p m c x).
Proof. exact (MK_COMB (@lem7574828) (@lem7574827 p m c x)). Qed.
Lemma lem7574830 (q : real -> real) (x : real) : (q x) = (q x).
Proof. exact (eq_refl (q x)). Qed.
Lemma lem7574831 (p : real -> real) (m : nat) (c : nat -> real) (q : real -> real) (x : real) : ((term680 p m c x) = (q x)) = ((term681 p m c x) = (q x)).
Proof. exact (MK_COMB (@lem7574829 p m c x) (@lem7574830 q x)). Qed.
Lemma lem7574836 (p : real -> real) (m : nat) (c : nat -> real) (q : real -> real) : (term686 p m c q) = (term687 p m c q).
Proof. exact (fun_ext (fun x : real => @lem7574831 p m c q x)). Qed.
Lemma lem7574837 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7574838 (p : real -> real) (m : nat) (c : nat -> real) (q : real -> real) : (term677 p m c q) = (term688 p m c q).
Proof. exact (MK_COMB (@lem7574837) (@lem7574836 p m c q)). Qed.
Lemma lem7574843 (p : real -> real) (m : nat) (c : nat -> real) (q : real -> real) : ((term45 p m c) = q) = (term688 p m c q).
Proof. exact (TRANS (@lem7574806 p m c q) (@lem7574838 p m c q)). Qed.
Lemma lem7574844 (p : real -> real) (m : nat) (c : nat -> real) (q : real -> real) (h1 : (term45 p m c) = q) : term688 p m c q.
Proof. exact (EQ_MP (@lem7574843 p m c q) (@lem7574794 p m c q h1)). Qed.
Lemma lem7574847 (x : real) (p : real -> real) (m : nat) (c : nat -> real) (q : real -> real) (h1 : (term45 p m c) = q) : term689 p m c q x.
Proof. exact (@lem7574844 p m c q h1 x). Qed.
Lemma lem7574848 (p : real -> real) (m : nat) (c : nat -> real) (q : real -> real) (x : real) : (term689 p m c q x) = ((term681 p m c x) = (q x)).
Proof. exact (eq_refl (term689 p m c q x)). Qed.
Lemma lem7574853 {A B : Type'} (f : A -> B) (y : A) : (term564 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7574854 (f : nat -> real) (y : nat) : (term565 f y) = (f y).
Proof. exact (@lem7574853 nat real f y). Qed.
Lemma lem7574855 (c : nat -> real) (i : nat) : (term690 c i) = (term691 c i).
Proof. exact (@lem7574854 (term675 c) i). Qed.
Lemma lem7574856 (c : nat -> real) (i : nat) : (term691 c i) = (term652 c i).
Proof. exact (eq_refl (term691 c i)). Qed.
Lemma lem7574857 (c : nat -> real) : (term692 c) = (term675 c).
Proof. exact (fun_ext (fun i : nat => @lem7574856 c i)). Qed.
Lemma lem7574858 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem7574859 (c : nat -> real) (i : nat) : (term690 c i) = (term691 c i).
Proof. exact (MK_COMB (@lem7574857 c) (@lem7574858 i)). Qed.
Lemma lem7574860 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7574861 (c : nat -> real) (i : nat) : (term693 c i) = (term694 c i).
Proof. exact (MK_COMB (@lem7574860) (@lem7574859 c i)). Qed.
Lemma lem7574862 (c : nat -> real) (i : nat) : (term691 c i) = (term652 c i).
Proof. exact (eq_refl (term691 c i)). Qed.
Lemma lem7574863 (c : nat -> real) (i : nat) : ((term690 c i) = (term691 c i)) = ((term691 c i) = (term652 c i)).
Proof. exact (MK_COMB (@lem7574861 c i) (@lem7574862 c i)). Qed.
Lemma lem7574864 (c : nat -> real) (i : nat) : (term691 c i) = (term652 c i).
Proof. exact (EQ_MP (@lem7574863 c i) (@lem7574855 c i)). Qed.
Lemma lem7574865 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7574866 (c : nat -> real) (i : nat) : (term695 c i) = (term649 c i).
Proof. exact (MK_COMB (@lem7574865) (@lem7574864 c i)). Qed.
Lemma lem7574867 (x : real) (i : nat) : (real_pow x i) = (real_pow x i).
Proof. exact (eq_refl (real_pow x i)). Qed.
Lemma lem7574868 (c : nat -> real) (x : real) (i : nat) : (term696 c x i) = (term662 c x i).
Proof. exact (MK_COMB (@lem7574866 c i) (@lem7574867 x i)). Qed.
Lemma lem7574869 (c : nat -> real) (x : real) : (term697 c x) = (term660 c x).
Proof. exact (fun_ext (fun i : nat => @lem7574868 c x i)). Qed.
Lemma lem7574870 (m : nat) : (term640 m) = (term640 m).
Proof. exact (eq_refl (term640 m)). Qed.
Lemma lem7574871 (m : nat) (c : nat -> real) (x : real) : (term698 m c x) = (term671 m c x).
Proof. exact (MK_COMB (@lem7574870 m) (@lem7574869 c x)). Qed.
Lemma lem7574872 (p : real -> real) (x : real) : (term444 p x) = (term444 p x).
Proof. exact (eq_refl (term444 p x)). Qed.
Lemma lem7574873 (p : real -> real) (m : nat) (c : nat -> real) (x : real) : (term699 p m c x) = (term681 p m c x).
Proof. exact (MK_COMB (@lem7574872 p x) (@lem7574871 m c x)). Qed.
Lemma lem7574875 (x : real) (p : real -> real) (m : nat) (c : nat -> real) (q : real -> real) (h1 : (term45 p m c) = q) : (term681 p m c x) = (q x).
Proof. exact (EQ_MP (@lem7574848 p m c q x) (@lem7574847 x p m c q h1)). Qed.
Lemma lem7574876 (x : real) (p : real -> real) (m : nat) (c : nat -> real) (q : real -> real) (h1 : (term45 p m c) = q) : (term699 p m c x) = (q x).
Proof. exact (TRANS (@lem7574873 p m c x) (@lem7574875 x p m c q h1)). Qed.
Lemma lem7574877 (p : real -> real) (m : nat) (c : nat -> real) (q : real -> real) (h1 : (term45 p m c) = q) : (term700 p m c) = (term701 q).
Proof. exact (fun_ext (fun x : real => @lem7574876 x p m c q h1)). Qed.
Lemma lem7574878 : polynomial_function = polynomial_function.
Proof. exact (eq_refl polynomial_function). Qed.
Lemma lem7574879 (p : real -> real) (m : nat) (c : nat -> real) (q : real -> real) (h1 : (term45 p m c) = q) : (term676 p m c) = (term702 q).
Proof. exact (MK_COMB (@lem7574878) (@lem7574877 p m c q h1)). Qed.
Lemma lem7574880 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7574881 (p : real -> real) (m : nat) (c : nat -> real) (q : real -> real) (h1 : (term45 p m c) = q) : (term703 p m c) = (term704 q).
Proof. exact (MK_COMB (@lem7574880) (@lem7574879 p m c q h1)). Qed.
Lemma lem7574883 (x : real) (p : real -> real) (m : nat) (c : nat -> real) (q : real -> real) (h1 : (term45 p m c) = q) : (term681 p m c x) = (q x).
Proof. exact (EQ_MP (@lem7574848 p m c q x) (@lem7574847 x p m c q h1)). Qed.
Lemma lem7574884 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7574885 (x : real) (p : real -> real) (m : nat) (c : nat -> real) (q : real -> real) (h1 : (term45 p m c) = q) : (term705 p m c x) = (term444 q x).
Proof. exact (MK_COMB (@lem7574884) (@lem7574883 x p m c q h1)). Qed.
Lemma lem7574886 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7574887 (x : real) (p : real -> real) (m : nat) (c : nat -> real) (q : real -> real) (h1 : (term45 p m c) = q) : (term670 p m c x) = (term706 q x).
Proof. exact (MK_COMB (@lem7574885 x p m c q h1) (@lem7574886 x)). Qed.
Lemma lem7574888 (p : real -> real) (m : nat) (c : nat -> real) (q : real -> real) (h1 : (term45 p m c) = q) : (term672 p m c) = (term707 q).
Proof. exact (fun_ext (fun x : real => @lem7574887 x p m c q h1)). Qed.
Lemma lem7574889 : polynomial_function = polynomial_function.
Proof. exact (eq_refl polynomial_function). Qed.
Lemma lem7574890 (p : real -> real) (m : nat) (c : nat -> real) (q : real -> real) (h1 : (term45 p m c) = q) : (term673 p m c) = (term708 q).
Proof. exact (MK_COMB (@lem7574889) (@lem7574888 p m c q h1)). Qed.
Lemma lem7574891 (p : real -> real) (m : nat) (c : nat -> real) (q : real -> real) (h1 : (term45 p m c) = q) : (term709 p m c) = (term710 q).
Proof. exact (MK_COMB (@lem7574881 p m c q h1) (@lem7574890 p m c q h1)). Qed.
Lemma lem7574894 (p : real -> real) (m : nat) (c : nat -> real) (q : real -> real) (h1 : (term45 p m c) = q) : (term710 q) = (term709 p m c).
Proof. exact (SYM (@lem7574891 p m c q h1)). Qed.
Lemma lem7574898 (p : real -> real) : (polynomial_function p) = (term40 p).
Proof. exact (EQ_MP (@lem7567905 p) (@lem7567904 p)). Qed.
Lemma lem7574899 (q : real -> real) : (term702 q) = (term711 q).
Proof. exact (@lem7574898 (term701 q)). Qed.
Lemma lem7574915 {A B : Type'} (f : A -> B) (y : A) : (term564 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7574916 (f : real -> real) (y : real) : (term678 f y) = (f y).
Proof. exact (@lem7574915 real real f y). Qed.
Lemma lem7574917 (q : real -> real) (x : real) : (term678 q x) = (q x).
Proof. exact (@lem7574916 q x). Qed.
Lemma lem7574918 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7574919 (q : real -> real) (x : real) : (term712 q x) = (term492 q x).
Proof. exact (MK_COMB (@lem7574918) (@lem7574917 q x)). Qed.
Lemma lem7574920 (m : nat) (c : nat -> real) (x : real) : (term443 m c x) = (term443 m c x).
Proof. exact (eq_refl (term443 m c x)). Qed.
Lemma lem7574921 (q : real -> real) (m : nat) (c : nat -> real) (x : real) : ((term678 q x) = (term443 m c x)) = ((q x) = (term443 m c x)).
Proof. exact (MK_COMB (@lem7574919 q x) (@lem7574920 m c x)). Qed.
Lemma lem7574924 (q : real -> real) (m : nat) (c : nat -> real) : (term713 q m c) = (term494 q m c).
Proof. exact (fun_ext (fun x : real => @lem7574921 q m c x)). Qed.
Lemma lem7574925 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7574926 (q : real -> real) (m : nat) (c : nat -> real) : (term714 q m c) = (term419 q m c).
Proof. exact (MK_COMB (@lem7574925) (@lem7574924 q m c)). Qed.
Lemma lem7574931 (q : real -> real) (m : nat) : (term715 q m) = (term417 q m).
Proof. exact (fun_ext (fun c : nat -> real => @lem7574926 q m c)). Qed.
Lemma lem7574932 : (@ex (nat -> real)) = (@ex (nat -> real)).
Proof. exact (eq_refl (@ex (nat -> real))). Qed.
Lemma lem7574933 (q : real -> real) (m : nat) : (term716 q m) = (term400 q m).
Proof. exact (MK_COMB (@lem7574932) (@lem7574931 q m)). Qed.
Lemma lem7574938 (q : real -> real) : (term717 q) = (term398 q).
Proof. exact (fun_ext (fun m : nat => @lem7574933 q m)). Qed.
Lemma lem7574939 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7574940 (q : real -> real) : (term711 q) = (term40 q).
Proof. exact (MK_COMB (@lem7574939) (@lem7574938 q)). Qed.
Lemma lem7574945 (q : real -> real) : (term702 q) = (term40 q).
Proof. exact (TRANS (@lem7574899 q) (@lem7574940 q)). Qed.
Lemma lem7574946 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7574947 (q : real -> real) : (term704 q) = (term390 q).
Proof. exact (MK_COMB (@lem7574946) (@lem7574945 q)). Qed.
Lemma lem7574949 (p : real -> real) : (polynomial_function p) = (term40 p).
Proof. exact (EQ_MP (@lem7567905 p) (@lem7567904 p)). Qed.
Lemma lem7574950 (q : real -> real) : (term708 q) = (term718 q).
Proof. exact (@lem7574949 (term707 q)). Qed.
Lemma lem7574966 {A B : Type'} (f : A -> B) (y : A) : (term564 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7574967 (f : real -> real) (y : real) : (term678 f y) = (f y).
Proof. exact (@lem7574966 real real f y). Qed.
Lemma lem7574968 (q : real -> real) (x : real) : (term719 q x) = (term720 q x).
Proof. exact (@lem7574967 (term707 q) x). Qed.
Lemma lem7574969 (q : real -> real) (x : real) : (term720 q x) = (term706 q x).
Proof. exact (eq_refl (term720 q x)). Qed.
Lemma lem7574970 (q : real -> real) : (term721 q) = (term707 q).
Proof. exact (fun_ext (fun x : real => @lem7574969 q x)). Qed.
Lemma lem7574971 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7574972 (q : real -> real) (x : real) : (term719 q x) = (term720 q x).
Proof. exact (MK_COMB (@lem7574970 q) (@lem7574971 x)). Qed.
Lemma lem7574973 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7574974 (q : real -> real) (x : real) : (term722 q x) = (term723 q x).
Proof. exact (MK_COMB (@lem7574973) (@lem7574972 q x)). Qed.
Lemma lem7574975 (q : real -> real) (x : real) : (term720 q x) = (term706 q x).
Proof. exact (eq_refl (term720 q x)). Qed.
Lemma lem7574976 (q : real -> real) (x : real) : ((term719 q x) = (term720 q x)) = ((term720 q x) = (term706 q x)).
Proof. exact (MK_COMB (@lem7574974 q x) (@lem7574975 q x)). Qed.
Lemma lem7574977 (q : real -> real) (x : real) : (term720 q x) = (term706 q x).
Proof. exact (EQ_MP (@lem7574976 q x) (@lem7574968 q x)). Qed.
Lemma lem7574978 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7574979 (q : real -> real) (x : real) : (term723 q x) = (term724 q x).
Proof. exact (MK_COMB (@lem7574978) (@lem7574977 q x)). Qed.
Lemma lem7574980 (m : nat) (c : nat -> real) (x : real) : (term443 m c x) = (term443 m c x).
Proof. exact (eq_refl (term443 m c x)). Qed.
Lemma lem7574981 (q : real -> real) (m : nat) (c : nat -> real) (x : real) : ((term720 q x) = (term443 m c x)) = ((term706 q x) = (term443 m c x)).
Proof. exact (MK_COMB (@lem7574979 q x) (@lem7574980 m c x)). Qed.
Lemma lem7574984 (q : real -> real) (m : nat) (c : nat -> real) : (term725 q m c) = (term726 q m c).
Proof. exact (fun_ext (fun x : real => @lem7574981 q m c x)). Qed.
Lemma lem7574985 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7574986 (q : real -> real) (m : nat) (c : nat -> real) : (term727 q m c) = (term728 q m c).
Proof. exact (MK_COMB (@lem7574985) (@lem7574984 q m c)). Qed.
Lemma lem7574991 (q : real -> real) (m : nat) : (term729 q m) = (term730 q m).
Proof. exact (fun_ext (fun c : nat -> real => @lem7574986 q m c)). Qed.
Lemma lem7574992 : (@ex (nat -> real)) = (@ex (nat -> real)).
Proof. exact (eq_refl (@ex (nat -> real))). Qed.
Lemma lem7574993 (q : real -> real) (m : nat) : (term731 q m) = (term732 q m).
Proof. exact (MK_COMB (@lem7574992) (@lem7574991 q m)). Qed.
Lemma lem7574998 (q : real -> real) : (term733 q) = (term734 q).
Proof. exact (fun_ext (fun m : nat => @lem7574993 q m)). Qed.
Lemma lem7574999 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7575000 (q : real -> real) : (term718 q) = (term735 q).
Proof. exact (MK_COMB (@lem7574999) (@lem7574998 q)). Qed.
Lemma lem7575005 (q : real -> real) : (term708 q) = (term735 q).
Proof. exact (TRANS (@lem7574950 q) (@lem7575000 q)). Qed.
Lemma lem7575006 (q : real -> real) : (term710 q) = (term736 q).
Proof. exact (MK_COMB (@lem7574947 q) (@lem7575005 q)). Qed.
Lemma lem7575008 {A : Type'} (P : A -> Prop) (Q : Prop) : (term37 A P Q) = (term38 A P Q).
Proof. exact (EQ_MP (@lem7567902 A P Q) (@lem7567901 A P Q)). Qed.
Lemma lem7575009 (P : nat -> Prop) (Q : Prop) : (term394 P Q) = (term395 P Q).
Proof. exact (@lem7575008 nat P Q). Qed.
Lemma lem7575010 (q : real -> real) : (term737 q) = (term738 q).
Proof. exact (@lem7575009 (term398 q) (term735 q)). Qed.
Lemma lem7575011 (q : real -> real) (m : nat) : (term399 q m) = (term400 q m).
Proof. exact (eq_refl (term399 q m)). Qed.
Lemma lem7575012 (q : real -> real) : (term401 q) = (term398 q).
Proof. exact (fun_ext (fun m : nat => @lem7575011 q m)). Qed.
Lemma lem7575013 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7575014 (q : real -> real) : (term402 q) = (term40 q).
Proof. exact (MK_COMB (@lem7575013) (@lem7575012 q)). Qed.
Lemma lem7575015 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7575016 (q : real -> real) : (term403 q) = (term390 q).
Proof. exact (MK_COMB (@lem7575015) (@lem7575014 q)). Qed.
Lemma lem7575017 (q : real -> real) : (term735 q) = (term735 q).
Proof. exact (eq_refl (term735 q)). Qed.
Lemma lem7575018 (q : real -> real) : (term737 q) = (term736 q).
Proof. exact (MK_COMB (@lem7575016 q) (@lem7575017 q)). Qed.
Lemma lem7575019 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7575020 (q : real -> real) : (term739 q) = (term740 q).
Proof. exact (MK_COMB (@lem7575019) (@lem7575018 q)). Qed.
Lemma lem7575021 (q : real -> real) (m : nat) : (term399 q m) = (term400 q m).
Proof. exact (eq_refl (term399 q m)). Qed.
Lemma lem7575022 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7575023 (q : real -> real) (m : nat) : (term406 q m) = (term407 q m).
Proof. exact (MK_COMB (@lem7575022) (@lem7575021 q m)). Qed.
Lemma lem7575024 (q : real -> real) : (term735 q) = (term735 q).
Proof. exact (eq_refl (term735 q)). Qed.
Lemma lem7575025 (m : nat) (q : real -> real) : (term741 m q) = (term742 m q).
Proof. exact (MK_COMB (@lem7575023 q m) (@lem7575024 q)). Qed.
Lemma lem7575026 (q : real -> real) : (term743 q) = (term744 q).
Proof. exact (fun_ext (fun m : nat => @lem7575025 m q)). Qed.
Lemma lem7575027 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7575028 (q : real -> real) : (term738 q) = (term745 q).
Proof. exact (MK_COMB (@lem7575027) (@lem7575026 q)). Qed.
Lemma lem7575029 (q : real -> real) : ((term737 q) = (term738 q)) = ((term736 q) = (term745 q)).
Proof. exact (MK_COMB (@lem7575020 q) (@lem7575028 q)). Qed.
Lemma lem7575030 (q : real -> real) : (term736 q) = (term745 q).
Proof. exact (EQ_MP (@lem7575029 q) (@lem7575010 q)). Qed.
Lemma lem7575036 {A : Type'} (P : A -> Prop) (Q : Prop) : (term37 A P Q) = (term38 A P Q).
Proof. exact (EQ_MP (@lem7567902 A P Q) (@lem7567901 A P Q)). Qed.
Lemma lem7575037 (P : type1010) (Q : Prop) : (term413 P Q) = (term414 P Q).
Proof. exact (@lem7575036 (nat -> real) P Q). Qed.
Lemma lem7575038 (m : nat) (q : real -> real) : (term746 m q) = (term747 m q).
Proof. exact (@lem7575037 (term417 q m) (term735 q)). Qed.
Lemma lem7575039 (q : real -> real) (m : nat) (c : nat -> real) : (term418 q m c) = (term419 q m c).
Proof. exact (eq_refl (term418 q m c)). Qed.
Lemma lem7575040 (q : real -> real) (m : nat) : (term420 q m) = (term417 q m).
Proof. exact (fun_ext (fun c : nat -> real => @lem7575039 q m c)). Qed.
Lemma lem7575041 : (@ex (nat -> real)) = (@ex (nat -> real)).
Proof. exact (eq_refl (@ex (nat -> real))). Qed.
Lemma lem7575042 (q : real -> real) (m : nat) : (term421 q m) = (term400 q m).
Proof. exact (MK_COMB (@lem7575041) (@lem7575040 q m)). Qed.
Lemma lem7575043 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7575044 (q : real -> real) (m : nat) : (term422 q m) = (term407 q m).
Proof. exact (MK_COMB (@lem7575043) (@lem7575042 q m)). Qed.
Lemma lem7575045 (q : real -> real) : (term735 q) = (term735 q).
Proof. exact (eq_refl (term735 q)). Qed.
Lemma lem7575046 (m : nat) (q : real -> real) : (term746 m q) = (term742 m q).
Proof. exact (MK_COMB (@lem7575044 q m) (@lem7575045 q)). Qed.
Lemma lem7575047 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7575048 (m : nat) (q : real -> real) : (term748 m q) = (term749 m q).
Proof. exact (MK_COMB (@lem7575047) (@lem7575046 m q)). Qed.
Lemma lem7575049 (q : real -> real) (m : nat) (c : nat -> real) : (term418 q m c) = (term419 q m c).
Proof. exact (eq_refl (term418 q m c)). Qed.
Lemma lem7575050 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7575051 (q : real -> real) (m : nat) (c : nat -> real) : (term425 q m c) = (term426 q m c).
Proof. exact (MK_COMB (@lem7575050) (@lem7575049 q m c)). Qed.
Lemma lem7575052 (q : real -> real) : (term735 q) = (term735 q).
Proof. exact (eq_refl (term735 q)). Qed.
Lemma lem7575053 (m : nat) (c : nat -> real) (q : real -> real) : (term750 m c q) = (term751 m c q).
Proof. exact (MK_COMB (@lem7575051 q m c) (@lem7575052 q)). Qed.
Lemma lem7575054 (m : nat) (q : real -> real) : (term752 m q) = (term753 m q).
Proof. exact (fun_ext (fun c : nat -> real => @lem7575053 m c q)). Qed.
Lemma lem7575055 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7575056 (m : nat) (q : real -> real) : (term747 m q) = (term754 m q).
Proof. exact (MK_COMB (@lem7575055) (@lem7575054 m q)). Qed.
Lemma lem7575057 (m : nat) (q : real -> real) : ((term746 m q) = (term747 m q)) = ((term742 m q) = (term754 m q)).
Proof. exact (MK_COMB (@lem7575048 m q) (@lem7575056 m q)). Qed.
Lemma lem7575058 (m : nat) (q : real -> real) : (term742 m q) = (term754 m q).
Proof. exact (EQ_MP (@lem7575057 m q) (@lem7575038 m q)). Qed.
Lemma lem7575085 (q : real -> real) : (term744 q) = (term755 q).
Proof. exact (fun_ext (fun m : nat => @lem7575058 m q)). Qed.
Lemma lem7575086 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7575087 (q : real -> real) : (term745 q) = (term756 q).
Proof. exact (MK_COMB (@lem7575086) (@lem7575085 q)). Qed.
Lemma lem7575092 (q : real -> real) : (term736 q) = (term756 q).
Proof. exact (TRANS (@lem7575030 q) (@lem7575087 q)). Qed.
Lemma lem7575093 (q : real -> real) : (term710 q) = (term756 q).
Proof. exact (TRANS (@lem7575006 q) (@lem7575092 q)). Qed.
Lemma lem7575094 (q : real -> real) : (term756 q) = (term710 q).
Proof. exact (SYM (@lem7575093 q)). Qed.
Lemma lem7575095 (q : real -> real) (n : nat) (a : nat -> real) (h1 : term419 q n a) : term419 q n a.
Proof. exact (h1). Qed.
Lemma lem7575103 (m : nat) (n : nat) (f : nat -> real) : term31 m n f.
Proof. exact (fun h0 : Peano.le m n => @lem7567892 f m n h0). Qed.
Lemma lem7575104 (n : nat) (a : nat -> real) (x : real) : term757 n a x.
Proof. exact (@lem7575103 (NUMERAL 0) (term74 n) (term758 a x)). Qed.
Lemma lem7575106 (n : nat) : (term25 n) = True.
Proof. exact (EQ_MP (@lem7567880 n) (@lem7567879 n)). Qed.
Lemma lem7575107 (n : nat) : (term759 n) = True.
Proof. exact (@lem7575106 (term74 n)). Qed.
Lemma lem7575108 (n : nat) : True = (term759 n).
Proof. exact (SYM (@lem7575107 n)). Qed.
Lemma lem7575109 (n : nat) : term759 n.
Proof. exact (EQ_MP (@lem7575108 n) (@lem0)). Qed.
Lemma lem7575110 (n : nat) (a : nat -> real) (x : real) : (term760 n a x) = (term761 n a x).
Proof. exact (@lem7575104 n a x (@lem7575109 n)). Qed.
Lemma lem7575112 {A B : Type'} (f : A -> B) (y : A) : (term564 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7575113 (f : nat -> real) (y : nat) : (term565 f y) = (f y).
Proof. exact (@lem7575112 nat real f y). Qed.
Lemma lem7575114 (a : nat -> real) (x : real) : (term762 a x) = (term763 a x).
Proof. exact (@lem7575113 (term758 a x) (NUMERAL 0)). Qed.
Lemma lem7575115 (a : nat -> real) (x : real) (i : nat) : (term764 a x i) = (term765 a x i).
Proof. exact (eq_refl (term764 a x i)). Qed.
Lemma lem7575116 (a : nat -> real) (x : real) : (term766 a x) = (term758 a x).
Proof. exact (fun_ext (fun i : nat => @lem7575115 a x i)). Qed.
Lemma lem7575117 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem7575118 (a : nat -> real) (x : real) : (term762 a x) = (term763 a x).
Proof. exact (MK_COMB (@lem7575116 a x) (@lem7575117)). Qed.
Lemma lem7575119 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7575120 (a : nat -> real) (x : real) : (term767 a x) = (term768 a x).
Proof. exact (MK_COMB (@lem7575119) (@lem7575118 a x)). Qed.
Lemma lem7575121 (a : nat -> real) (x : real) : (term763 a x) = (term769 a x).
Proof. exact (eq_refl (term763 a x)). Qed.
Lemma lem7575122 (a : nat -> real) (x : real) : ((term762 a x) = (term763 a x)) = ((term763 a x) = (term769 a x)).
Proof. exact (MK_COMB (@lem7575120 a x) (@lem7575121 a x)). Qed.
Lemma lem7575123 (a : nat -> real) (x : real) : (term763 a x) = (term769 a x).
Proof. exact (EQ_MP (@lem7575122 a x) (@lem7575114 a x)). Qed.
Lemma lem7575125 {A B : Type'} (f : A -> B) (y : A) : (term564 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7575126 (f : nat -> real) (y : nat) : (term565 f y) = (f y).
Proof. exact (@lem7575125 nat real f y). Qed.
Lemma lem7575127 (a : nat -> real) : (term770 a) = (term771 a).
Proof. exact (@lem7575126 (term772 a) (NUMERAL 0)). Qed.
Lemma lem7575128 (a : nat -> real) (i : nat) : (term773 a i) = (term774 a i).
Proof. exact (eq_refl (term773 a i)). Qed.
Lemma lem7575129 (a : nat -> real) : (term775 a) = (term772 a).
Proof. exact (fun_ext (fun i : nat => @lem7575128 a i)). Qed.
Lemma lem7575130 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem7575131 (a : nat -> real) : (term770 a) = (term771 a).
Proof. exact (MK_COMB (@lem7575129 a) (@lem7575130)). Qed.
Lemma lem7575132 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7575133 (a : nat -> real) : (term776 a) = (term777 a).
Proof. exact (MK_COMB (@lem7575132) (@lem7575131 a)). Qed.
Lemma lem7575134 (a : nat -> real) : (term771 a) = (term778 a).
Proof. exact (eq_refl (term771 a)). Qed.
Lemma lem7575135 (a : nat -> real) : ((term770 a) = (term771 a)) = ((term771 a) = (term778 a)).
Proof. exact (MK_COMB (@lem7575133 a) (@lem7575134 a)). Qed.
Lemma lem7575136 (a : nat -> real) : (term771 a) = (term778 a).
Proof. exact (EQ_MP (@lem7575135 a) (@lem7575127 a)). Qed.
Lemma lem7575138 {_2975 _2982 : Type'} (x : _2982) (z : _2975) (y : _2975) : (term779 _2975 _2982 x y z) = y.
Proof. exact (EQ_MP (@lem15249 _2975 _2982 x z y) (@lem0)). Qed.
Lemma lem7575139 (x : nat) (z : real) (y : real) : (term780 x y z) = y.
Proof. exact (@lem7575138 real nat x z y). Qed.
Lemma lem7575140 (a : nat -> real) : (term778 a) = term781.
Proof. exact (@lem7575139 (NUMERAL 0) (term782 a) term781). Qed.
Lemma lem7575141 (a : nat -> real) : (term771 a) = term781.
Proof. exact (TRANS (@lem7575136 a) (@lem7575140 a)). Qed.
Lemma lem7575142 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7575143 (a : nat -> real) : (term783 a) = term784.
Proof. exact (MK_COMB (@lem7575142) (@lem7575141 a)). Qed.
Lemma lem7575144 (x : real) : (term573 x) = (term573 x).
Proof. exact (eq_refl (term573 x)). Qed.
Lemma lem7575145 (a : nat -> real) (x : real) : (term769 a x) = (term785 x).
Proof. exact (MK_COMB (@lem7575143 a) (@lem7575144 x)). Qed.
Lemma lem7575146 (a : nat -> real) (x : real) : (term763 a x) = (term785 x).
Proof. exact (TRANS (@lem7575123 a x) (@lem7575145 a x)). Qed.
Lemma lem7575147 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7575148 (a : nat -> real) (x : real) : (term786 a x) = (term787 x).
Proof. exact (MK_COMB (@lem7575147) (@lem7575146 a x)). Qed.
Lemma lem7575155 (f : nat -> real) (a : nat) (b : nat) (g : nat -> real) : term788 f a b g.
Proof. exact (EQ_MP (@lem7261462 f a b g) (@lem7261461 f a g b)). Qed.
Lemma lem7575156 (f : nat -> real) (a : nat) (b : nat) : term789 f a b.
Proof. exact (fun g : nat -> real => @lem7575155 f a b g). Qed.
Lemma lem7575157 (a : nat -> real) (x : real) (n : nat) : term790 a x n.
Proof. exact (@lem7575156 (term758 a x) term791 (term74 n)). Qed.
Lemma lem7575158 (a : nat -> real) (x : real) (i : nat) : (term764 a x i) = (term765 a x i).
Proof. exact (eq_refl (term764 a x i)). Qed.
Lemma lem7575159 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7575160 (a : nat -> real) (x : real) (i : nat) : (term792 a x i) = (term793 a x i).
Proof. exact (MK_COMB (@lem7575159) (@lem7575158 a x i)). Qed.
Lemma lem7575161 (g : nat -> real) (i : nat) : (g i) = (g i).
Proof. exact (eq_refl (g i)). Qed.
Lemma lem7575162 (a : nat -> real) (x : real) (g : nat -> real) (i : nat) : ((term764 a x i) = (g i)) = ((term765 a x i) = (g i)).
Proof. exact (MK_COMB (@lem7575160 a x i) (@lem7575161 g i)). Qed.
Lemma lem7575163 (i : nat) (n : nat) : (term794 i n) = (term794 i n).
Proof. exact (eq_refl (term794 i n)). Qed.
Lemma lem7575164 (n : nat) (a : nat -> real) (x : real) (g : nat -> real) (i : nat) : (term795 n a x g i) = (term796 n a x g i).
Proof. exact (MK_COMB (@lem7575163 i n) (@lem7575162 a x g i)). Qed.
Lemma lem7575165 (n : nat) (a : nat -> real) (x : real) (g : nat -> real) : (term797 n a x g) = (term798 n a x g).
Proof. exact (fun_ext (fun i : nat => @lem7575164 n a x g i)). Qed.
Lemma lem7575166 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7575167 (n : nat) (a : nat -> real) (x : real) (g : nat -> real) : (term799 n a x g) = (term800 n a x g).
Proof. exact (MK_COMB (@lem7575166) (@lem7575165 n a x g)). Qed.
Lemma lem7575168 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7575169 (n : nat) (a : nat -> real) (x : real) (g : nat -> real) : (term801 n a x g) = (term802 n a x g).
Proof. exact (MK_COMB (@lem7575168) (@lem7575167 n a x g)). Qed.
Lemma lem7575170 (a : nat -> real) (x : real) (i : nat) : (term764 a x i) = (term765 a x i).
Proof. exact (eq_refl (term764 a x i)). Qed.
Lemma lem7575171 (a : nat -> real) (x : real) : (term766 a x) = (term758 a x).
Proof. exact (fun_ext (fun i : nat => @lem7575170 a x i)). Qed.
Lemma lem7575172 (n : nat) : (term600 n) = (term600 n).
Proof. exact (eq_refl (term600 n)). Qed.
Lemma lem7575173 (n : nat) (a : nat -> real) (x : real) : (term803 n a x) = (term804 n a x).
Proof. exact (MK_COMB (@lem7575172 n) (@lem7575171 a x)). Qed.
Lemma lem7575174 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7575175 (n : nat) (a : nat -> real) (x : real) : (term805 n a x) = (term806 n a x).
Proof. exact (MK_COMB (@lem7575174) (@lem7575173 n a x)). Qed.
Lemma lem7575176 (n : nat) (g : nat -> real) : (term807 n g) = (term807 n g).
Proof. exact (eq_refl (term807 n g)). Qed.
Lemma lem7575177 (a : nat -> real) (x : real) (n : nat) (g : nat -> real) : ((term803 n a x) = (term807 n g)) = ((term804 n a x) = (term807 n g)).
Proof. exact (MK_COMB (@lem7575175 n a x) (@lem7575176 n g)). Qed.
Lemma lem7575178 (a : nat -> real) (x : real) (n : nat) (g : nat -> real) : (term808 a x n g) = (term809 a x n g).
Proof. exact (MK_COMB (@lem7575169 n a x g) (@lem7575177 a x n g)). Qed.
Lemma lem7575179 (a : nat -> real) (x : real) (n : nat) : (term810 a x n) = (term811 a x n).
Proof. exact (fun_ext (fun g : nat -> real => @lem7575178 a x n g)). Qed.
Lemma lem7575180 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7575181 (a : nat -> real) (x : real) (n : nat) : (term790 a x n) = (term812 a x n).
Proof. exact (MK_COMB (@lem7575180) (@lem7575179 a x n)). Qed.
Lemma lem7575182 (a : nat -> real) (x : real) (n : nat) : term812 a x n.
Proof. exact (EQ_MP (@lem7575181 a x n) (@lem7575157 a x n)). Qed.
Lemma lem7575183 (a : nat -> real) (x : real) (n : nat) (g : nat -> real) : term813 a x n g.
Proof. exact (@lem7575182 a x n g). Qed.
Lemma lem7575184 (a : nat -> real) (x : real) (n : nat) (g : nat -> real) : (term813 a x n g) = (term809 a x n g).
Proof. exact (eq_refl (term813 a x n g)). Qed.
Lemma lem7575194 {A B : Type'} (f : A -> B) (y : A) : (term564 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7575195 (f : nat -> real) (y : nat) : (term565 f y) = (f y).
Proof. exact (@lem7575194 nat real f y). Qed.
Lemma lem7575196 (a : nat -> real) (i : nat) : (term814 a i) = (term773 a i).
Proof. exact (@lem7575195 (term772 a) i). Qed.
Lemma lem7575197 (a : nat -> real) (i : nat) : (term773 a i) = (term774 a i).
Proof. exact (eq_refl (term773 a i)). Qed.
Lemma lem7575198 (a : nat -> real) : (term775 a) = (term772 a).
Proof. exact (fun_ext (fun i : nat => @lem7575197 a i)). Qed.
Lemma lem7575199 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem7575200 (a : nat -> real) (i : nat) : (term814 a i) = (term773 a i).
Proof. exact (MK_COMB (@lem7575198 a) (@lem7575199 i)). Qed.
Lemma lem7575201 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7575202 (a : nat -> real) (i : nat) : (term815 a i) = (term816 a i).
Proof. exact (MK_COMB (@lem7575201) (@lem7575200 a i)). Qed.
Lemma lem7575203 (a : nat -> real) (i : nat) : (term773 a i) = (term774 a i).
Proof. exact (eq_refl (term773 a i)). Qed.
Lemma lem7575204 (a : nat -> real) (i : nat) : ((term814 a i) = (term773 a i)) = ((term773 a i) = (term774 a i)).
Proof. exact (MK_COMB (@lem7575202 a i) (@lem7575203 a i)). Qed.
Lemma lem7575205 (a : nat -> real) (i : nat) : (term773 a i) = (term774 a i).
Proof. exact (EQ_MP (@lem7575204 a i) (@lem7575196 a i)). Qed.
Lemma lem7575254 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7575255 (a : nat -> real) (i : nat) : (term817 a i) = (term818 a i).
Proof. exact (MK_COMB (@lem7575254) (@lem7575205 a i)). Qed.
Lemma lem7575304 (x : real) (i : nat) : (real_pow x i) = (real_pow x i).
Proof. exact (eq_refl (real_pow x i)). Qed.
Lemma lem7575305 (a : nat -> real) (x : real) (i : nat) : (term765 a x i) = (term819 a x i).
Proof. exact (MK_COMB (@lem7575255 a i) (@lem7575304 x i)). Qed.
Lemma lem7575354 (n : nat) (a : nat -> real) (x : real) (i : nat) : term820 n a x i.
Proof. exact (fun h0 : term821 i n => @lem7575305 a x i). Qed.
Lemma lem7575355 (n : nat) (a : nat -> real) (x : real) : term822 n a x.
Proof. exact (fun i : nat => @lem7575354 n a x i). Qed.
Lemma lem7575357 (a : nat -> real) (x : real) (n : nat) (g : nat -> real) : term809 a x n g.
Proof. exact (EQ_MP (@lem7575184 a x n g) (@lem7575183 a x n g)). Qed.
Lemma lem7575358 (n : nat) (a : nat -> real) (x : real) : term823 n a x.
Proof. exact (@lem7575357 a x n (term824 a x)). Qed.
Lemma lem7575359 (a : nat -> real) (x : real) (i : nat) : (term825 a x i) = (term819 a x i).
Proof. exact (eq_refl (term825 a x i)). Qed.
Lemma lem7575360 (a : nat -> real) (x : real) (i : nat) : (term793 a x i) = (term793 a x i).
Proof. exact (eq_refl (term793 a x i)). Qed.
Lemma lem7575361 (a : nat -> real) (x : real) (i : nat) : ((term765 a x i) = (term825 a x i)) = ((term765 a x i) = (term819 a x i)).
Proof. exact (MK_COMB (@lem7575360 a x i) (@lem7575359 a x i)). Qed.
Lemma lem7575362 (i : nat) (n : nat) : (term794 i n) = (term794 i n).
Proof. exact (eq_refl (term794 i n)). Qed.
Lemma lem7575363 (n : nat) (a : nat -> real) (x : real) (i : nat) : (term826 n a x i) = (term820 n a x i).
Proof. exact (MK_COMB (@lem7575362 i n) (@lem7575361 a x i)). Qed.
Lemma lem7575364 (n : nat) (a : nat -> real) (x : real) : (term827 n a x) = (term828 n a x).
Proof. exact (fun_ext (fun i : nat => @lem7575363 n a x i)). Qed.
Lemma lem7575365 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7575366 (n : nat) (a : nat -> real) (x : real) : (term829 n a x) = (term822 n a x).
Proof. exact (MK_COMB (@lem7575365) (@lem7575364 n a x)). Qed.
Lemma lem7575367 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7575368 (n : nat) (a : nat -> real) (x : real) : (term830 n a x) = (term831 n a x).
Proof. exact (MK_COMB (@lem7575367) (@lem7575366 n a x)). Qed.
Lemma lem7575369 (n : nat) (a : nat -> real) (x : real) : ((term804 n a x) = (term832 n a x)) = ((term804 n a x) = (term832 n a x)).
Proof. exact (eq_refl ((term804 n a x) = (term832 n a x))). Qed.
Lemma lem7575370 (n : nat) (a : nat -> real) (x : real) : (term823 n a x) = (term833 n a x).
Proof. exact (MK_COMB (@lem7575368 n a x) (@lem7575369 n a x)). Qed.
Lemma lem7575371 (n : nat) (a : nat -> real) (x : real) : term833 n a x.
Proof. exact (EQ_MP (@lem7575370 n a x) (@lem7575358 n a x)). Qed.
Lemma lem7575372 (n : nat) (a : nat -> real) (x : real) : (term804 n a x) = (term832 n a x).
Proof. exact (@lem7575371 n a x (@lem7575355 n a x)). Qed.
Lemma lem7575637 (n : nat) (a : nat -> real) (x : real) : (term761 n a x) = (term834 n a x).
Proof. exact (MK_COMB (@lem7575148 a x) (@lem7575372 n a x)). Qed.
Lemma lem7575902 (n : nat) (a : nat -> real) (x : real) : (term760 n a x) = (term834 n a x).
Proof. exact (TRANS (@lem7575110 n a x) (@lem7575637 n a x)). Qed.
Lemma lem7575903 (q : real -> real) (x : real) : (term724 q x) = (term724 q x).
Proof. exact (eq_refl (term724 q x)). Qed.
Lemma lem7575904 (q : real -> real) (n : nat) (a : nat -> real) (x : real) : ((term706 q x) = (term760 n a x)) = ((term706 q x) = (term834 n a x)).
Proof. exact (MK_COMB (@lem7575903 q x) (@lem7575902 n a x)). Qed.
Lemma lem7576171 (q : real -> real) (n : nat) (a : nat -> real) : (term835 q n a) = (term836 q n a).
Proof. exact (fun_ext (fun x : real => @lem7575904 q n a x)). Qed.
Lemma lem7576438 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7576439 (q : real -> real) (n : nat) (a : nat -> real) : (term837 q n a) = (term838 q n a).
Proof. exact (MK_COMB (@lem7576438) (@lem7576171 q n a)). Qed.
Lemma lem7576710 (q : real -> real) (n : nat) (a : nat -> real) : (term838 q n a) = (term837 q n a).
Proof. exact (SYM (@lem7576439 q n a)). Qed.
Lemma lem7576711 (m : nat) : term839 m.
Proof. exact (@lem135886 m). Qed.
Lemma lem7576712 (m : nat) : (term839 m) = (term840 m).
Proof. exact (eq_refl (term839 m)). Qed.
Lemma lem7576713 (m : nat) : term840 m.
Proof. exact (EQ_MP (@lem7576712 m) (@lem7576711 m)). Qed.
Lemma lem7576714 (m : nat) (n : nat) : term841 m n.
Proof. exact (@lem7576713 m n). Qed.
Lemma lem7576715 (n : nat) (m : nat) : (term841 m n) = ((term842 m n) = m).
Proof. exact (eq_refl (term841 m n)). Qed.
Lemma lem7576717 : term843.
Proof. exact (proj2 (@lem522076)). Qed.
Lemma lem7576718 : term844.
Proof. exact (proj2 (@lem7576717)). Qed.
Lemma lem7576719 : term845.
Proof. exact (proj2 (@lem7576718)). Qed.
Lemma lem7576761 : term846.
Proof. exact (proj1 (@lem7576719)). Qed.
Lemma lem7576762 (n : nat) : term847 n.
Proof. exact (@lem7576761 n). Qed.
Lemma lem7576763 (n : nat) : (term847 n) = (((BIT1 n) = 0) = False).
Proof. exact (eq_refl (term847 n)). Qed.
Lemma lem7576770 : term848.
Proof. exact (proj1 (@lem522076)). Qed.
Lemma lem7576771 (m : nat) : term849 m.
Proof. exact (@lem7576770 m). Qed.
Lemma lem7576772 (m : nat) : (term849 m) = (term850 m).
Proof. exact (eq_refl (term849 m)). Qed.
Lemma lem7576773 (m : nat) : term850 m.
Proof. exact (EQ_MP (@lem7576772 m) (@lem7576771 m)). Qed.
Lemma lem7576774 (m : nat) (n : nat) : term851 m n.
Proof. exact (@lem7576773 m n). Qed.
Lemma lem7576775 (m : nat) (n : nat) : (term851 m n) = (((NUMERAL m) = (NUMERAL n)) = (m = n)).
Proof. exact (eq_refl (term851 m n)). Qed.
Lemma lem7576777 (m : nat) : term852 m.
Proof. exact (@lem79432 m). Qed.
Lemma lem7576778 (m : nat) : (term852 m) = (term853 m).
Proof. exact (eq_refl (term852 m)). Qed.
Lemma lem7576779 (m : nat) : term853 m.
Proof. exact (EQ_MP (@lem7576778 m) (@lem7576777 m)). Qed.
Lemma lem7576780 (m : nat) (n : nat) : term854 m n.
Proof. exact (@lem7576779 m n). Qed.
Lemma lem7576781 (m : nat) (n : nat) : (term854 m n) = (((Nat.add m n) = (NUMERAL 0)) = (term855 m n)).
Proof. exact (eq_refl (term854 m n)). Qed.
Lemma lem7576783 (f : nat -> real) : term50 f.
Proof. exact (@lem7567876 f). Qed.
Lemma lem7576784 (f : nat -> real) : (term50 f) = (term51 f).
Proof. exact (eq_refl (term50 f)). Qed.
Lemma lem7576785 (f : nat -> real) : term51 f.
Proof. exact (EQ_MP (@lem7576784 f) (@lem7576783 f)). Qed.
Lemma lem7576786 (f : nat -> real) (m : nat) : term52 f m.
Proof. exact (@lem7576785 f m). Qed.
Lemma lem7576787 (m : nat) (f : nat -> real) : (term52 f m) = (term53 m f).
Proof. exact (eq_refl (term52 f m)). Qed.
Lemma lem7576788 (m : nat) (f : nat -> real) : term53 m f.
Proof. exact (EQ_MP (@lem7576787 m f) (@lem7576786 f m)). Qed.
Lemma lem7576789 (m : nat) (f : nat -> real) (n : nat) : term54 m f n.
Proof. exact (@lem7576788 m f n). Qed.
Lemma lem7576790 (m : nat) (n : nat) (f : nat -> real) : (term54 m f n) = ((term55 m n f) = (term56 m n f)).
Proof. exact (eq_refl (term54 m f n)). Qed.
Lemma lem7576797 (x : real) (q : real -> real) (n : nat) (a : nat -> real) (h1 : term419 q n a) : term442 q n a x.
Proof. exact (@lem7575095 q n a h1 x). Qed.
Lemma lem7576798 (q : real -> real) (n : nat) (a : nat -> real) (x : real) : (term442 q n a x) = ((q x) = (term443 n a x)).
Proof. exact (eq_refl (term442 q n a x)). Qed.
Lemma lem7576807 (x : real) (q : real -> real) (n : nat) (a : nat -> real) (h1 : term419 q n a) : (q x) = (term443 n a x).
Proof. exact (EQ_MP (@lem7576798 q n a x) (@lem7576797 x q n a h1)). Qed.
Lemma lem7576808 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7576809 (x : real) (q : real -> real) (n : nat) (a : nat -> real) (h1 : term419 q n a) : (term444 q x) = (term856 n a x).
Proof. exact (MK_COMB (@lem7576808) (@lem7576807 x q n a h1)). Qed.
Lemma lem7576810 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7576811 (x : real) (q : real -> real) (n : nat) (a : nat -> real) (h1 : term419 q n a) : (term706 q x) = (term857 n a x).
Proof. exact (MK_COMB (@lem7576809 x q n a h1) (@lem7576810 x)). Qed.
Lemma lem7576812 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7576813 (x : real) (q : real -> real) (n : nat) (a : nat -> real) (h1 : term419 q n a) : (term724 q x) = (term858 n a x).
Proof. exact (MK_COMB (@lem7576812) (@lem7576811 x q n a h1)). Qed.
Lemma lem7576815 (m : nat) (n : nat) (f : nat -> real) : (term55 m n f) = (term56 m n f).
Proof. exact (EQ_MP (@lem7576790 m n f) (@lem7576789 m f n)). Qed.
Lemma lem7576816 (n : nat) (a : nat -> real) (x : real) : (term832 n a x) = (term859 n a x).
Proof. exact (@lem7576815 (NUMERAL 0) n (term824 a x)). Qed.
Lemma lem7576818 {A B : Type'} (f : A -> B) (y : A) : (term564 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7576819 (f : nat -> real) (y : nat) : (term565 f y) = (f y).
Proof. exact (@lem7576818 nat real f y). Qed.
Lemma lem7576820 (a : nat -> real) (x : real) (i : nat) : (term860 a x i) = (term861 a x i).
Proof. exact (@lem7576819 (term824 a x) (term74 i)). Qed.
Lemma lem7576821 (a : nat -> real) (x : real) (i : nat) : (term825 a x i) = (term819 a x i).
Proof. exact (eq_refl (term825 a x i)). Qed.
Lemma lem7576822 (a : nat -> real) (x : real) : (term862 a x) = (term824 a x).
Proof. exact (fun_ext (fun i : nat => @lem7576821 a x i)). Qed.
Lemma lem7576823 (i : nat) : (term74 i) = (term74 i).
Proof. exact (eq_refl (term74 i)). Qed.
Lemma lem7576824 (a : nat -> real) (x : real) (i : nat) : (term860 a x i) = (term861 a x i).
Proof. exact (MK_COMB (@lem7576822 a x) (@lem7576823 i)). Qed.
Lemma lem7576825 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7576826 (a : nat -> real) (x : real) (i : nat) : (term863 a x i) = (term864 a x i).
Proof. exact (MK_COMB (@lem7576825) (@lem7576824 a x i)). Qed.
Lemma lem7576827 (a : nat -> real) (x : real) (i : nat) : (term861 a x i) = (term865 a x i).
Proof. exact (eq_refl (term861 a x i)). Qed.
Lemma lem7576828 (a : nat -> real) (x : real) (i : nat) : ((term860 a x i) = (term861 a x i)) = ((term861 a x i) = (term865 a x i)).
Proof. exact (MK_COMB (@lem7576826 a x i) (@lem7576827 a x i)). Qed.
Lemma lem7576829 (a : nat -> real) (x : real) (i : nat) : (term861 a x i) = (term865 a x i).
Proof. exact (EQ_MP (@lem7576828 a x i) (@lem7576820 a x i)). Qed.
Lemma lem7576833 (m : nat) (n : nat) : ((Nat.add m n) = (NUMERAL 0)) = (term855 m n).
Proof. exact (EQ_MP (@lem7576781 m n) (@lem7576780 m n)). Qed.
Lemma lem7576834 (i : nat) : ((term74 i) = (NUMERAL 0)) = (term866 i).
Proof. exact (@lem7576833 i term22). Qed.
Lemma lem7576840 (m : nat) (n : nat) : ((NUMERAL m) = (NUMERAL n)) = (m = n).
Proof. exact (EQ_MP (@lem7576775 m n) (@lem7576774 m n)). Qed.
Lemma lem7576841 : (term22 = (NUMERAL 0)) = ((BIT1 0) = 0).
Proof. exact (@lem7576840 (BIT1 0) 0). Qed.
Lemma lem7576843 (n : nat) : ((BIT1 n) = 0) = False.
Proof. exact (EQ_MP (@lem7576763 n) (@lem7576762 n)). Qed.
Lemma lem7576844 : ((BIT1 0) = 0) = False.
Proof. exact (@lem7576843 0). Qed.
Lemma lem7576845 : (term22 = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem7576841) (@lem7576844)). Qed.
Lemma lem7576846 (i : nat) : (term867 i) = (term867 i).
Proof. exact (eq_refl (term867 i)). Qed.
Lemma lem7576847 (i : nat) : (term866 i) = (term868 i).
Proof. exact (MK_COMB (@lem7576846 i) (@lem7576845)). Qed.
Lemma lem7576849 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem7576850 (i : nat) : (term868 i) = False.
Proof. exact (@lem7576849 (i = (NUMERAL 0))). Qed.
Lemma lem7576851 (i : nat) : (term866 i) = False.
Proof. exact (TRANS (@lem7576847 i) (@lem7576850 i)). Qed.
Lemma lem7576852 (i : nat) : ((term74 i) = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem7576834 i) (@lem7576851 i)). Qed.
Lemma lem7576853 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem7576854 (i : nat) : (term869 i) = (@COND real False).
Proof. exact (MK_COMB (@lem7576853) (@lem7576852 i)). Qed.
Lemma lem7576855 : term781 = term781.
Proof. exact (eq_refl term781). Qed.
Lemma lem7576856 (i : nat) : (term870 i) = term871.
Proof. exact (MK_COMB (@lem7576854 i) (@lem7576855)). Qed.
Lemma lem7576858 (n : nat) (m : nat) : (term842 m n) = m.
Proof. exact (EQ_MP (@lem7576715 n m) (@lem7576714 m n)). Qed.
Lemma lem7576859 (i : nat) : (term872 i) = i.
Proof. exact (@lem7576858 term22 i). Qed.
Lemma lem7576860 (a : nat -> real) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem7576861 (a : nat -> real) (i : nat) : (term873 a i) = (a i).
Proof. exact (MK_COMB (@lem7576860 a) (@lem7576859 i)). Qed.
Lemma lem7576862 (a : nat -> real) (i : nat) : (term874 a i) = (term875 a i).
Proof. exact (MK_COMB (@lem7576856 i) (@lem7576861 a i)). Qed.
Lemma lem7576864 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem7576865 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem7576864 real t1 t2). Qed.
Lemma lem7576866 (a : nat -> real) (i : nat) : (term875 a i) = (a i).
Proof. exact (@lem7576865 term781 (a i)). Qed.
Lemma lem7576867 (a : nat -> real) (i : nat) : (term874 a i) = (a i).
Proof. exact (TRANS (@lem7576862 a i) (@lem7576866 a i)). Qed.
Lemma lem7576868 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7576869 (a : nat -> real) (i : nat) : (term876 a i) = (term877 a i).
Proof. exact (MK_COMB (@lem7576868) (@lem7576867 a i)). Qed.
Lemma lem7576870 (x : real) (i : nat) : (term645 x i) = (term645 x i).
Proof. exact (eq_refl (term645 x i)). Qed.
Lemma lem7576871 (a : nat -> real) (x : real) (i : nat) : (term865 a x i) = (term878 a x i).
Proof. exact (MK_COMB (@lem7576869 a i) (@lem7576870 x i)). Qed.
Lemma lem7576872 (a : nat -> real) (x : real) (i : nat) : (term861 a x i) = (term878 a x i).
Proof. exact (TRANS (@lem7576829 a x i) (@lem7576871 a x i)). Qed.
Lemma lem7576873 (a : nat -> real) (x : real) : (term879 a x) = (term880 a x).
Proof. exact (fun_ext (fun i : nat => @lem7576872 a x i)). Qed.
Lemma lem7576874 (n : nat) : (term640 n) = (term640 n).
Proof. exact (eq_refl (term640 n)). Qed.
Lemma lem7576875 (n : nat) (a : nat -> real) (x : real) : (term859 n a x) = (term881 n a x).
Proof. exact (MK_COMB (@lem7576874 n) (@lem7576873 a x)). Qed.
Lemma lem7576876 (n : nat) (a : nat -> real) (x : real) : (term832 n a x) = (term881 n a x).
Proof. exact (TRANS (@lem7576816 n a x) (@lem7576875 n a x)). Qed.
Lemma lem7576877 (x : real) : (term787 x) = (term787 x).
Proof. exact (eq_refl (term787 x)). Qed.
Lemma lem7576878 (n : nat) (a : nat -> real) (x : real) : (term834 n a x) = (term882 n a x).
Proof. exact (MK_COMB (@lem7576877 x) (@lem7576876 n a x)). Qed.
Lemma lem7576879 (x : real) (q : real -> real) (n : nat) (a : nat -> real) (h1 : term419 q n a) : ((term706 q x) = (term834 n a x)) = ((term857 n a x) = (term882 n a x)).
Proof. exact (MK_COMB (@lem7576813 x q n a h1) (@lem7576878 n a x)). Qed.
Lemma lem7576882 (q : real -> real) (n : nat) (a : nat -> real) (h1 : term419 q n a) : (term836 q n a) = (term883 n a).
Proof. exact (fun_ext (fun x : real => @lem7576879 x q n a h1)). Qed.
Lemma lem7576883 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7576884 (q : real -> real) (n : nat) (a : nat -> real) (h1 : term419 q n a) : (term838 q n a) = (term884 n a).
Proof. exact (MK_COMB (@lem7576883) (@lem7576882 q n a h1)). Qed.
Lemma lem7576889 (q : real -> real) (n : nat) (a : nat -> real) (h1 : term419 q n a) : (term884 n a) = (term838 q n a).
Proof. exact (SYM (@lem7576884 q n a h1)). Qed.
Lemma lem7576905 (m : nat) (x : real) (n : nat) : (term19 x m n) = (term20 m x n).
Proof. exact (EQ_MP (@lem7567872 m x n) (@lem7567871 m x n)). Qed.
Lemma lem7576906 (i : nat) (x : real) : (term645 x i) = (term646 i x).
Proof. exact (@lem7576905 i x term22). Qed.
Lemma lem7576907 (a : nat -> real) (i : nat) : (term877 a i) = (term877 a i).
Proof. exact (eq_refl (term877 a i)). Qed.
Lemma lem7576908 (a : nat -> real) (i : nat) (x : real) : (term878 a x i) = (term885 a i x).
Proof. exact (MK_COMB (@lem7576907 a i) (@lem7576906 i x)). Qed.
Lemma lem7576910 (x : real) (y : real) (z : real) : (term12 x y z) = (term13 x y z).
Proof. exact (EQ_MP (@lem7567863 x y z) (@lem7567862 x y z)). Qed.
Lemma lem7576911 (a : nat -> real) (i : nat) (x : real) : (term885 a i x) = (term886 a i x).
Proof. exact (@lem7576910 (a i) (real_pow x i) (term49 x)). Qed.
Lemma lem7576912 (a : nat -> real) (i : nat) (x : real) : (term878 a x i) = (term886 a i x).
Proof. exact (TRANS (@lem7576908 a i x) (@lem7576911 a i x)). Qed.
Lemma lem7576913 (a : nat -> real) (x : real) : (term880 a x) = (term887 a x).
Proof. exact (fun_ext (fun i : nat => @lem7576912 a i x)). Qed.
Lemma lem7576914 (n : nat) : (term640 n) = (term640 n).
Proof. exact (eq_refl (term640 n)). Qed.
Lemma lem7576915 (n : nat) (a : nat -> real) (x : real) : (term881 n a x) = (term888 n a x).
Proof. exact (MK_COMB (@lem7576914 n) (@lem7576913 a x)). Qed.
Lemma lem7576917 {A : Type'} (s : A -> Prop) (f : A -> real) (c : real) : (term5 A s f c) = (term6 A s f c).
Proof. exact (EQ_MP (@lem7567854 A s f c) (@lem7567853 A f c s)). Qed.
Lemma lem7576918 (s : nat -> Prop) (f : nat -> real) (c : real) : (term655 s f c) = (term656 s f c).
Proof. exact (@lem7576917 nat s f c). Qed.
Lemma lem7576919 (n : nat) (a : nat -> real) (x : real) : (term889 n a x) = (term890 n a x).
Proof. exact (@lem7576918 (term659 n) (term563 a x) (term49 x)). Qed.
Lemma lem7576920 (a : nat -> real) (x : real) (i : nat) : (term567 a x i) = (term568 a x i).
Proof. exact (eq_refl (term567 a x i)). Qed.
Lemma lem7576921 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7576922 (a : nat -> real) (x : real) (i : nat) : (term891 a x i) = (term892 a x i).
Proof. exact (MK_COMB (@lem7576921) (@lem7576920 a x i)). Qed.
Lemma lem7576923 (x : real) : (term49 x) = (term49 x).
Proof. exact (eq_refl (term49 x)). Qed.
Lemma lem7576924 (a : nat -> real) (i : nat) (x : real) : (term893 a i x) = (term886 a i x).
Proof. exact (MK_COMB (@lem7576922 a x i) (@lem7576923 x)). Qed.
Lemma lem7576925 (a : nat -> real) (x : real) : (term894 a x) = (term887 a x).
Proof. exact (fun_ext (fun i : nat => @lem7576924 a i x)). Qed.
Lemma lem7576926 (n : nat) : (term640 n) = (term640 n).
Proof. exact (eq_refl (term640 n)). Qed.
Lemma lem7576927 (n : nat) (a : nat -> real) (x : real) : (term889 n a x) = (term888 n a x).
Proof. exact (MK_COMB (@lem7576926 n) (@lem7576925 a x)). Qed.
Lemma lem7576928 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7576929 (n : nat) (a : nat -> real) (x : real) : (term895 n a x) = (term896 n a x).
Proof. exact (MK_COMB (@lem7576928) (@lem7576927 n a x)). Qed.
Lemma lem7576930 (n : nat) (a : nat -> real) (x : real) : (term890 n a x) = (term890 n a x).
Proof. exact (eq_refl (term890 n a x)). Qed.
Lemma lem7576931 (n : nat) (a : nat -> real) (x : real) : ((term889 n a x) = (term890 n a x)) = ((term888 n a x) = (term890 n a x)).
Proof. exact (MK_COMB (@lem7576929 n a x) (@lem7576930 n a x)). Qed.
Lemma lem7576932 (n : nat) (a : nat -> real) (x : real) : (term888 n a x) = (term890 n a x).
Proof. exact (EQ_MP (@lem7576931 n a x) (@lem7576919 n a x)). Qed.
Lemma lem7576937 (n : nat) (a : nat -> real) (x : real) : (term881 n a x) = (term890 n a x).
Proof. exact (TRANS (@lem7576915 n a x) (@lem7576932 n a x)). Qed.
Lemma lem7576938 (x : real) : (term787 x) = (term787 x).
Proof. exact (eq_refl (term787 x)). Qed.
Lemma lem7576939 (n : nat) (a : nat -> real) (x : real) : (term882 n a x) = (term897 n a x).
Proof. exact (MK_COMB (@lem7576938 x) (@lem7576937 n a x)). Qed.
Lemma lem7576940 (n : nat) (a : nat -> real) (x : real) : (term858 n a x) = (term858 n a x).
Proof. exact (eq_refl (term858 n a x)). Qed.
Lemma lem7576941 (n : nat) (a : nat -> real) (x : real) : ((term857 n a x) = (term882 n a x)) = ((term857 n a x) = (term897 n a x)).
Proof. exact (MK_COMB (@lem7576940 n a x) (@lem7576939 n a x)). Qed.
Lemma lem7576944 (n : nat) (a : nat -> real) : (term883 n a) = (term898 n a).
Proof. exact (fun_ext (fun x : real => @lem7576941 n a x)). Qed.
Lemma lem7576945 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7576946 (n : nat) (a : nat -> real) : (term884 n a) = (term899 n a).
Proof. exact (MK_COMB (@lem7576945) (@lem7576944 n a)). Qed.
Lemma lem7576951 (n : nat) (a : nat -> real) : (term899 n a) = (term884 n a).
Proof. exact (SYM (@lem7576946 n a)). Qed.
Lemma lem7576961 (P : real -> Prop) : (term900 P) = (term901 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem7576962 (n : nat) (a : nat -> real) : (term902 n a) = (term903 n a).
Proof. exact (@lem7576961 (term898 n a)). Qed.
Lemma lem7576963 (n : nat) (a : nat -> real) (x : real) : (term904 n a x) = ((term857 n a x) = (term897 n a x)).
Proof. exact (eq_refl (term904 n a x)). Qed.
Lemma lem7576964 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7576966 (n : nat) (a : nat -> real) (x : real) : (term905 n a x) = (term906 n a x).
Proof. exact (MK_COMB (@lem7576964) (@lem7576963 n a x)). Qed.
Lemma lem7576967 (n : nat) (a : nat -> real) : (term907 n a) = (term908 n a).
Proof. exact (fun_ext (fun x : real => @lem7576966 n a x)). Qed.
Lemma lem7576968 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7576969 (n : nat) (a : nat -> real) : (term903 n a) = (term909 n a).
Proof. exact (MK_COMB (@lem7576968) (@lem7576967 n a)). Qed.
Lemma lem7576971 (n : nat) (a : nat -> real) : (term902 n a) = (term909 n a).
Proof. exact (TRANS (@lem7576962 n a) (@lem7576969 n a)). Qed.
Lemma lem7576974 (n : nat) (a : nat -> real) (x : real) : (term906 n a x) = (term906 n a x).
Proof. exact (eq_refl (term906 n a x)). Qed.
Lemma lem7576975 (n : nat) (a : nat -> real) : (term908 n a) = (term908 n a).
Proof. exact (fun_ext (fun x : real => @lem7576974 n a x)). Qed.
Lemma lem7576976 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7576977 (n : nat) (a : nat -> real) : (term909 n a) = (term909 n a).
Proof. exact (MK_COMB (@lem7576976) (@lem7576975 n a)). Qed.
Lemma lem7576978 (n : nat) (a : nat -> real) : (term902 n a) = (term909 n a).
Proof. exact (TRANS (@lem7576971 n a) (@lem7576977 n a)). Qed.
Lemma lem7576979 (n : nat) (a : nat -> real) (x : real) : (term906 n a x) = (term910 n a x).
Proof. exact (@lem1988318 (term857 n a x) (term897 n a x)). Qed.
Lemma lem7576986 (x : real) : (term49 x) = x.
Proof. exact (@lem1982779 x). Qed.
Lemma lem7576989 (n : nat) (a : nat -> real) (x : real) : (term856 n a x) = (term856 n a x).
Proof. exact (eq_refl (term856 n a x)). Qed.
Lemma lem7576990 (n : nat) (a : nat -> real) (x : real) : (term890 n a x) = (term857 n a x).
Proof. exact (MK_COMB (@lem7576989 n a x) (@lem7576986 x)). Qed.
Lemma lem7576991 (n : nat) (a : nat -> real) (x : real) : (term857 n a x) = (term911 n a x).
Proof. exact (@lem1982747 x (term443 n a x)). Qed.
Lemma lem7576992 (n : nat) (a : nat -> real) (x : real) : (term890 n a x) = (term911 n a x).
Proof. exact (TRANS (@lem7576990 n a x) (@lem7576991 n a x)). Qed.
Lemma lem7576999 (x : real) : (term573 x) = term574.
Proof. exact (@lem1982777 x). Qed.
Lemma lem7577002 : term784 = term784.
Proof. exact (eq_refl term784). Qed.
Lemma lem7577003 (x : real) : (term785 x) = term912.
Proof. exact (MK_COMB (@lem7577002) (@lem7576999 x)). Qed.
Lemma lem7577004 : term912 = term781.
Proof. exact (@lem1982729 term574). Qed.
Lemma lem7577005 (x : real) : (term785 x) = term781.
Proof. exact (TRANS (@lem7577003 x) (@lem7577004)). Qed.
Lemma lem7577006 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7577007 (x : real) : (term787 x) = term913.
Proof. exact (MK_COMB (@lem7577006) (@lem7577005 x)). Qed.
Lemma lem7577008 (n : nat) (a : nat -> real) (x : real) : (term897 n a x) = (term914 n a x).
Proof. exact (MK_COMB (@lem7577007 x) (@lem7576992 n a x)). Qed.
Lemma lem7577009 (n : nat) (a : nat -> real) (x : real) : (term914 n a x) = (term911 n a x).
Proof. exact (@lem1982721 (term911 n a x)). Qed.
Lemma lem7577010 (n : nat) (a : nat -> real) (x : real) : (term897 n a x) = (term911 n a x).
Proof. exact (TRANS (@lem7577008 n a x) (@lem7577009 n a x)). Qed.
Lemma lem7577017 (n : nat) (a : nat -> real) (x : real) : (term857 n a x) = (term911 n a x).
Proof. exact (@lem1982747 x (term443 n a x)). Qed.
Lemma lem7577018 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem7577019 (n : nat) (a : nat -> real) (x : real) : (term915 n a x) = (term916 n a x).
Proof. exact (MK_COMB (@lem7577018) (@lem7577017 n a x)). Qed.
Lemma lem7577020 (n : nat) (a : nat -> real) (x : real) : (term917 n a x) = (term918 n a x).
Proof. exact (MK_COMB (@lem7577019 n a x) (@lem7577010 n a x)). Qed.
Lemma lem7577021 (n : nat) (a : nat -> real) (x : real) : (term918 n a x) = (term919 n a x).
Proof. exact (@lem1982792 (term911 n a x) (term911 n a x)). Qed.
Lemma lem7577025 (n : nat) (a : nat -> real) (x : real) : (term919 n a x) = (term920 n a x).
Proof. exact (@lem1982715 term921 (term911 n a x)). Qed.
Lemma lem7577027 (x : nat) : (real_of_num x) = (term922 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7577028 : term574 = term923.
Proof. exact (@lem7577027 term22). Qed.
Lemma lem7577030 (x : nat) : (term924 x) = (term925 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7577031 : term921 = term926.
Proof. exact (@lem7577030 term22). Qed.
Lemma lem7577032 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7577033 : term927 = term928.
Proof. exact (MK_COMB (@lem7577032) (@lem7577031)). Qed.
Lemma lem7577034 : term929 = term930.
Proof. exact (MK_COMB (@lem7577033) (@lem7577028)). Qed.
Lemma lem7577035 : term931.
Proof. exact (@lem1981473 term921 term574 term574 term574 term781 term574). Qed.
Lemma lem7577037 (m : nat) (n : nat) : (term932 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7577038 : term933 = term934.
Proof. exact (@lem7577037 (NUMERAL 0) term22). Qed.
Lemma lem7577039 : term935 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7577040 (h1 : term935 = (BIT1 0)) : term934 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7577041 : (term935 = (BIT1 0)) = (term934 = True).
Proof. exact (prop_ext (fun h1 : term935 = (BIT1 0) => @lem7577040 h1) (fun h1 : term934 = True => @lem7577039)). Qed.
Lemma lem7577042 : term934 = True.
Proof. exact (EQ_MP (@lem7577041) (@lem7577039)). Qed.
Lemma lem7577043 : term933 = True.
Proof. exact (TRANS (@lem7577038) (@lem7577042)). Qed.
Lemma lem7577044 : True = term933.
Proof. exact (SYM (@lem7577043)). Qed.
Lemma lem7577045 : term933.
Proof. exact (EQ_MP (@lem7577044) (@lem0)). Qed.
Lemma lem7577046 : term936.
Proof. exact (@lem7577035 (@lem7577045)). Qed.
Lemma lem7577048 (m : nat) (n : nat) : (term932 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7577049 : term933 = term934.
Proof. exact (@lem7577048 (NUMERAL 0) term22). Qed.
Lemma lem7577050 : term935 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7577051 (h1 : term935 = (BIT1 0)) : term934 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7577052 : (term935 = (BIT1 0)) = (term934 = True).
Proof. exact (prop_ext (fun h1 : term935 = (BIT1 0) => @lem7577051 h1) (fun h1 : term934 = True => @lem7577050)). Qed.
Lemma lem7577053 : term934 = True.
Proof. exact (EQ_MP (@lem7577052) (@lem7577050)). Qed.
Lemma lem7577054 : term933 = True.
Proof. exact (TRANS (@lem7577049) (@lem7577053)). Qed.
Lemma lem7577055 : True = term933.
Proof. exact (SYM (@lem7577054)). Qed.
Lemma lem7577056 : term933.
Proof. exact (EQ_MP (@lem7577055) (@lem0)). Qed.
Lemma lem7577057 : term937.
Proof. exact (@lem7577046 (@lem7577056)). Qed.
Lemma lem7577059 (m : nat) (n : nat) : (term932 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7577060 : term933 = term934.
Proof. exact (@lem7577059 (NUMERAL 0) term22). Qed.
Lemma lem7577061 : term935 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7577062 (h1 : term935 = (BIT1 0)) : term934 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7577063 : (term935 = (BIT1 0)) = (term934 = True).
Proof. exact (prop_ext (fun h1 : term935 = (BIT1 0) => @lem7577062 h1) (fun h1 : term934 = True => @lem7577061)). Qed.
Lemma lem7577064 : term934 = True.
Proof. exact (EQ_MP (@lem7577063) (@lem7577061)). Qed.
Lemma lem7577065 : term933 = True.
Proof. exact (TRANS (@lem7577060) (@lem7577064)). Qed.
Lemma lem7577066 : True = term933.
Proof. exact (SYM (@lem7577065)). Qed.
Lemma lem7577067 : term933.
Proof. exact (EQ_MP (@lem7577066) (@lem0)). Qed.
Lemma lem7577068 : term938.
Proof. exact (@lem7577057 (@lem7577067)). Qed.
Lemma lem7577070 (m : nat) (n : nat) : (term939 m n) = (term940 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7577071 : term941 = term942.
Proof. exact (@lem7577070 term22 term22). Qed.
Lemma lem7577072 : (term943 = (BIT1 0)) = (term944 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7577073 : term944 = term22.
Proof. exact (EQ_MP (@lem7577072) (@lem940073)). Qed.
Lemma lem7577074 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7577075 : term942 = term574.
Proof. exact (MK_COMB (@lem7577074) (@lem7577073)). Qed.
Lemma lem7577076 : term941 = term574.
Proof. exact (TRANS (@lem7577071) (@lem7577075)). Qed.
Lemma lem7577078 (m : nat) (n : nat) : (term945 m n) = (term946 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7577079 : term947 = term948.
Proof. exact (@lem7577078 term22 term22). Qed.
Lemma lem7577080 : (term943 = (BIT1 0)) = (term944 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7577081 : term944 = term22.
Proof. exact (EQ_MP (@lem7577080) (@lem940073)). Qed.
Lemma lem7577082 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7577083 : term942 = term574.
Proof. exact (MK_COMB (@lem7577082) (@lem7577081)). Qed.
Lemma lem7577084 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7577085 : term948 = term921.
Proof. exact (MK_COMB (@lem7577084) (@lem7577083)). Qed.
Lemma lem7577086 : term947 = term921.
Proof. exact (TRANS (@lem7577079) (@lem7577085)). Qed.
Lemma lem7577087 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7577088 : term949 = term927.
Proof. exact (MK_COMB (@lem7577087) (@lem7577086)). Qed.
Lemma lem7577089 : term950 = term929.
Proof. exact (MK_COMB (@lem7577088) (@lem7577076)). Qed.
Lemma lem7577091 (m : nat) : (term951 m) = term781.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7577092 : term929 = term781.
Proof. exact (@lem7577091 term22). Qed.
Lemma lem7577093 : term950 = term781.
Proof. exact (TRANS (@lem7577089) (@lem7577092)). Qed.
Lemma lem7577094 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7577095 : term952 = term784.
Proof. exact (MK_COMB (@lem7577094) (@lem7577093)). Qed.
Lemma lem7577096 : term574 = term574.
Proof. exact (eq_refl term574). Qed.
Lemma lem7577097 : term953 = term912.
Proof. exact (MK_COMB (@lem7577095) (@lem7577096)). Qed.
Lemma lem7577099 (x : nat) : (term954 x) = term781.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7577100 : term912 = term781.
Proof. exact (@lem7577099 term22). Qed.
Lemma lem7577101 : term953 = term781.
Proof. exact (TRANS (@lem7577097) (@lem7577100)). Qed.
Lemma lem7577103 (m : nat) (n : nat) : (term939 m n) = (term940 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7577104 : term941 = term942.
Proof. exact (@lem7577103 term22 term22). Qed.
Lemma lem7577105 : (term943 = (BIT1 0)) = (term944 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7577106 : term944 = term22.
Proof. exact (EQ_MP (@lem7577105) (@lem940073)). Qed.
Lemma lem7577107 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7577108 : term942 = term574.
Proof. exact (MK_COMB (@lem7577107) (@lem7577106)). Qed.
Lemma lem7577109 : term941 = term574.
Proof. exact (TRANS (@lem7577104) (@lem7577108)). Qed.
Lemma lem7577110 : term784 = term784.
Proof. exact (eq_refl term784). Qed.
Lemma lem7577111 : term955 = term912.
Proof. exact (MK_COMB (@lem7577110) (@lem7577109)). Qed.
Lemma lem7577113 (x : nat) : (term954 x) = term781.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7577114 : term912 = term781.
Proof. exact (@lem7577113 term22). Qed.
Lemma lem7577115 : term955 = term781.
Proof. exact (TRANS (@lem7577111) (@lem7577114)). Qed.
Lemma lem7577116 : term781 = term955.
Proof. exact (SYM (@lem7577115)). Qed.
Lemma lem7577117 : term953 = term955.
Proof. exact (TRANS (@lem7577101) (@lem7577116)). Qed.
Lemma lem7577118 : term930 = term956.
Proof. exact (@lem7577068 (@lem7577117)). Qed.
Lemma lem7577119 : term929 = term956.
Proof. exact (TRANS (@lem7577034) (@lem7577118)). Qed.
Lemma lem7577121 (x : real) : (term957 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7577122 : term956 = term781.
Proof. exact (@lem7577121 term781). Qed.
Lemma lem7577123 : term929 = term781.
Proof. exact (TRANS (@lem7577119) (@lem7577122)). Qed.
Lemma lem7577124 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7577125 : term958 = term784.
Proof. exact (MK_COMB (@lem7577124) (@lem7577123)). Qed.
Lemma lem7577126 (n : nat) (a : nat -> real) (x : real) : (term911 n a x) = (term911 n a x).
Proof. exact (eq_refl (term911 n a x)). Qed.
Lemma lem7577127 (n : nat) (a : nat -> real) (x : real) : (term920 n a x) = (term959 n a x).
Proof. exact (MK_COMB (@lem7577125) (@lem7577126 n a x)). Qed.
Lemma lem7577128 (n : nat) (a : nat -> real) (x : real) : (term919 n a x) = (term959 n a x).
Proof. exact (TRANS (@lem7577025 n a x) (@lem7577127 n a x)). Qed.
Lemma lem7577129 (n : nat) (a : nat -> real) (x : real) : (term959 n a x) = term781.
Proof. exact (@lem1982719 (term911 n a x)). Qed.
Lemma lem7577131 (n : nat) (a : nat -> real) (x : real) : (term919 n a x) = term781.
Proof. exact (TRANS (@lem7577128 n a x) (@lem7577129 n a x)). Qed.
Lemma lem7577132 (n : nat) (a : nat -> real) (x : real) : (term918 n a x) = term781.
Proof. exact (TRANS (@lem7577021 n a x) (@lem7577131 n a x)). Qed.
Lemma lem7577133 (n : nat) (a : nat -> real) (x : real) : (term917 n a x) = term781.
Proof. exact (TRANS (@lem7577020 n a x) (@lem7577132 n a x)). Qed.
Lemma lem7577134 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7577135 (n : nat) (a : nat -> real) (x : real) : (term960 n a x) = term961.
Proof. exact (MK_COMB (@lem7577134) (@lem7577133 n a x)). Qed.
Lemma lem7577136 : term961 = term962.
Proof. exact (@lem1982785 term781). Qed.
Lemma lem7577138 (x : nat) : (real_of_num x) = (term922 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7577139 : term781 = term956.
Proof. exact (@lem7577138 (NUMERAL 0)). Qed.
Lemma lem7577141 (x : nat) : (term924 x) = (term925 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7577142 : term921 = term926.
Proof. exact (@lem7577141 term22). Qed.
Lemma lem7577143 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7577144 : term963 = term964.
Proof. exact (MK_COMB (@lem7577143) (@lem7577142)). Qed.
Lemma lem7577145 : term962 = term965.
Proof. exact (MK_COMB (@lem7577144) (@lem7577139)). Qed.
Lemma lem7577146 : term965 = term966.
Proof. exact (@lem1981613 term921 term781 term574 term574). Qed.
Lemma lem7577148 (m : nat) (n : nat) : (term939 m n) = (term940 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7577149 : term941 = term942.
Proof. exact (@lem7577148 term22 term22). Qed.
Lemma lem7577150 : (term943 = (BIT1 0)) = (term944 = term22).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7577151 : term944 = term22.
Proof. exact (EQ_MP (@lem7577150) (@lem940073)). Qed.
Lemma lem7577152 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7577153 : term942 = term574.
Proof. exact (MK_COMB (@lem7577152) (@lem7577151)). Qed.
Lemma lem7577154 : term941 = term574.
Proof. exact (TRANS (@lem7577149) (@lem7577153)). Qed.
Lemma lem7577156 (x : nat) : (term967 x) = term781.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7577157 : term962 = term781.
Proof. exact (@lem7577156 term22). Qed.
Lemma lem7577158 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7577159 : term968 = term969.
Proof. exact (MK_COMB (@lem7577158) (@lem7577157)). Qed.
Lemma lem7577160 : term966 = term956.
Proof. exact (MK_COMB (@lem7577159) (@lem7577154)). Qed.
Lemma lem7577161 : term965 = term956.
Proof. exact (TRANS (@lem7577146) (@lem7577160)). Qed.
Lemma lem7577162 : term962 = term956.
Proof. exact (TRANS (@lem7577145) (@lem7577161)). Qed.
Lemma lem7577164 (x : real) : (term957 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7577165 : term956 = term781.
Proof. exact (@lem7577164 term781). Qed.
Lemma lem7577166 : term962 = term781.
Proof. exact (TRANS (@lem7577162) (@lem7577165)). Qed.
Lemma lem7577167 : term961 = term781.
Proof. exact (TRANS (@lem7577136) (@lem7577166)). Qed.
Lemma lem7577168 (n : nat) (a : nat -> real) (x : real) : (term970 n a x) = (term970 n a x).
Proof. exact (eq_refl (term970 n a x)). Qed.
Lemma lem7577169 (n : nat) (a : nat -> real) (x : real) : ((term960 n a x) = term961) = ((term960 n a x) = term781).
Proof. exact (MK_COMB (@lem7577168 n a x) (@lem7577167)). Qed.
Lemma lem7577170 (n : nat) (a : nat -> real) (x : real) : (term960 n a x) = term781.
Proof. exact (EQ_MP (@lem7577169 n a x) (@lem7577135 n a x)). Qed.
Lemma lem7577171 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7577172 (n : nat) (a : nat -> real) (x : real) : (term971 n a x) = term972.
Proof. exact (MK_COMB (@lem7577171) (@lem7577170 n a x)). Qed.
Lemma lem7577173 : term781 = term781.
Proof. exact (eq_refl term781). Qed.
Lemma lem7577174 (n : nat) (a : nat -> real) (x : real) : (term973 n a x) = term974.
Proof. exact (MK_COMB (@lem7577172 n a x) (@lem7577173)). Qed.
Lemma lem7577175 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7577176 (n : nat) (a : nat -> real) (x : real) : (term975 n a x) = term972.
Proof. exact (MK_COMB (@lem7577175) (@lem7577133 n a x)). Qed.
Lemma lem7577177 : term781 = term781.
Proof. exact (eq_refl term781). Qed.
Lemma lem7577178 (n : nat) (a : nat -> real) (x : real) : (term976 n a x) = term974.
Proof. exact (MK_COMB (@lem7577176 n a x) (@lem7577177)). Qed.
Lemma lem7577179 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7577180 (n : nat) (a : nat -> real) (x : real) : (term977 n a x) = term978.
Proof. exact (MK_COMB (@lem7577179) (@lem7577178 n a x)). Qed.
Lemma lem7577181 (n : nat) (a : nat -> real) (x : real) : (term910 n a x) = term979.
Proof. exact (MK_COMB (@lem7577180 n a x) (@lem7577174 n a x)). Qed.
Lemma lem7577182 (n : nat) (a : nat -> real) (x : real) : (term906 n a x) = term979.
Proof. exact (TRANS (@lem7576979 n a x) (@lem7577181 n a x)). Qed.
Lemma lem7577183 (n : nat) (a : nat -> real) : (term908 n a) = term980.
Proof. exact (fun_ext (fun x : real => @lem7577182 n a x)). Qed.
Lemma lem7577184 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7577185 (n : nat) (a : nat -> real) : (term909 n a) = term981.
Proof. exact (MK_COMB (@lem7577184) (@lem7577183 n a)). Qed.
Lemma lem7577186 (n : nat) (a : nat -> real) : (term902 n a) = term981.
Proof. exact (TRANS (@lem7576978 n a) (@lem7577185 n a)). Qed.
Lemma lem7577188 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term298 A P Q) = (term297 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem7577189 (P : real -> Prop) (Q : real -> Prop) : (term982 P Q) = (term983 P Q).
Proof. exact (@lem7577188 real P Q). Qed.
Lemma lem7577190 : term984 = term985.
Proof. exact (@lem7577189 term986 term986). Qed.
Lemma lem7577191 (x : real) : (term987 x) = term974.
Proof. exact (eq_refl (term987 x)). Qed.
Lemma lem7577192 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7577193 (x : real) : (term988 x) = term978.
Proof. exact (MK_COMB (@lem7577192) (@lem7577191 x)). Qed.
Lemma lem7577194 (x : real) : (term987 x) = term974.
Proof. exact (eq_refl (term987 x)). Qed.
Lemma lem7577195 (x : real) : (term989 x) = term979.
Proof. exact (MK_COMB (@lem7577193 x) (@lem7577194 x)). Qed.
Lemma lem7577196 : term990 = term980.
Proof. exact (fun_ext (fun x : real => @lem7577195 x)). Qed.
Lemma lem7577197 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7577198 : term984 = term981.
Proof. exact (MK_COMB (@lem7577197) (@lem7577196)). Qed.
Lemma lem7577199 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7577200 : term991 = term992.
Proof. exact (MK_COMB (@lem7577199) (@lem7577198)). Qed.
Lemma lem7577201 (x : real) : (term987 x) = term974.
Proof. exact (eq_refl (term987 x)). Qed.
Lemma lem7577202 : term993 = term986.
Proof. exact (fun_ext (fun x : real => @lem7577201 x)). Qed.
Lemma lem7577203 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7577204 : term994 = term995.
Proof. exact (MK_COMB (@lem7577203) (@lem7577202)). Qed.
Lemma lem7577205 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7577206 : term996 = term997.
Proof. exact (MK_COMB (@lem7577205) (@lem7577204)). Qed.
Lemma lem7577207 (x : real) : (term987 x) = term974.
Proof. exact (eq_refl (term987 x)). Qed.
Lemma lem7577208 : term993 = term986.
Proof. exact (fun_ext (fun x : real => @lem7577207 x)). Qed.
Lemma lem7577209 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7577210 : term994 = term995.
Proof. exact (MK_COMB (@lem7577209) (@lem7577208)). Qed.
Lemma lem7577211 : term985 = term998.
Proof. exact (MK_COMB (@lem7577206) (@lem7577210)). Qed.
Lemma lem7577212 : (term984 = term985) = (term981 = term998).
Proof. exact (MK_COMB (@lem7577200) (@lem7577211)). Qed.
Lemma lem7577213 : term981 = term998.
Proof. exact (EQ_MP (@lem7577212) (@lem7577190)). Qed.
Lemma lem7577215 {A : Type'} (t : Prop) : (term999 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem7577216 (t : Prop) : (term1000 t) = t.
Proof. exact (@lem7577215 real t). Qed.
Lemma lem7577217 : term995 = term974.
Proof. exact (@lem7577216 term974). Qed.
Lemma lem7577218 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7577219 : term997 = term978.
Proof. exact (MK_COMB (@lem7577218) (@lem7577217)). Qed.
Lemma lem7577221 {A : Type'} (t : Prop) : (term999 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem7577222 (t : Prop) : (term1000 t) = t.
Proof. exact (@lem7577221 real t). Qed.
Lemma lem7577223 : term995 = term974.
Proof. exact (@lem7577222 term974). Qed.
Lemma lem7577224 : term998 = term979.
Proof. exact (MK_COMB (@lem7577219) (@lem7577223)). Qed.
Lemma lem7577227 : term981 = term979.
Proof. exact (TRANS (@lem7577213) (@lem7577224)). Qed.
Lemma lem7577236 (n : nat) (a : nat -> real) : (term902 n a) = term979.
Proof. exact (TRANS (@lem7577186 n a) (@lem7577227)). Qed.
Lemma lem7577246 (h1 : term979) : term979.
Proof. exact (h1). Qed.
Lemma lem7577247 (h1 : term974) : term974.
Proof. exact (h1). Qed.
Lemma lem7577249 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7577250 : term974 = term1001.
Proof. exact (@lem7577249 term781 term781). Qed.
Lemma lem7577252 (x : nat) : (real_of_num x) = (term922 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7577253 : term781 = term956.
Proof. exact (@lem7577252 (NUMERAL 0)). Qed.
Lemma lem7577255 (x : nat) : (real_of_num x) = (term922 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7577256 : term781 = term956.
Proof. exact (@lem7577255 (NUMERAL 0)). Qed.
Lemma lem7577257 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7577258 : term1002 = term1003.
Proof. exact (MK_COMB (@lem7577257) (@lem7577256)). Qed.
Lemma lem7577259 : term1001 = term1004.
Proof. exact (MK_COMB (@lem7577258) (@lem7577253)). Qed.
Lemma lem7577260 : term1005.
Proof. exact (@lem1980255 term781 term574 term781 term574). Qed.
Lemma lem7577262 (m : nat) (n : nat) : (term932 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7577263 : term933 = term934.
Proof. exact (@lem7577262 (NUMERAL 0) term22). Qed.
Lemma lem7577264 : term935 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7577265 (h1 : term935 = (BIT1 0)) : term934 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7577266 : (term935 = (BIT1 0)) = (term934 = True).
Proof. exact (prop_ext (fun h1 : term935 = (BIT1 0) => @lem7577265 h1) (fun h1 : term934 = True => @lem7577264)). Qed.
Lemma lem7577267 : term934 = True.
Proof. exact (EQ_MP (@lem7577266) (@lem7577264)). Qed.
Lemma lem7577268 : term933 = True.
Proof. exact (TRANS (@lem7577263) (@lem7577267)). Qed.
Lemma lem7577269 : True = term933.
Proof. exact (SYM (@lem7577268)). Qed.
Lemma lem7577270 : term933.
Proof. exact (EQ_MP (@lem7577269) (@lem0)). Qed.
Lemma lem7577271 : term1006.
Proof. exact (@lem7577260 (@lem7577270)). Qed.
Lemma lem7577273 (m : nat) (n : nat) : (term932 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7577274 : term933 = term934.
Proof. exact (@lem7577273 (NUMERAL 0) term22). Qed.
Lemma lem7577275 : term935 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7577276 (h1 : term935 = (BIT1 0)) : term934 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7577277 : (term935 = (BIT1 0)) = (term934 = True).
Proof. exact (prop_ext (fun h1 : term935 = (BIT1 0) => @lem7577276 h1) (fun h1 : term934 = True => @lem7577275)). Qed.
Lemma lem7577278 : term934 = True.
Proof. exact (EQ_MP (@lem7577277) (@lem7577275)). Qed.
Lemma lem7577279 : term933 = True.
Proof. exact (TRANS (@lem7577274) (@lem7577278)). Qed.
Lemma lem7577280 : True = term933.
Proof. exact (SYM (@lem7577279)). Qed.
Lemma lem7577281 : term933.
Proof. exact (EQ_MP (@lem7577280) (@lem0)). Qed.
Lemma lem7577282 : term1004 = term1007.
Proof. exact (@lem7577271 (@lem7577281)). Qed.
Lemma lem7577284 (x : nat) : (term954 x) = term781.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7577285 : term912 = term781.
Proof. exact (@lem7577284 term22). Qed.
Lemma lem7577287 (x : nat) : (term954 x) = term781.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7577288 : term912 = term781.
Proof. exact (@lem7577287 term22). Qed.
Lemma lem7577289 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7577290 : term1008 = term1002.
Proof. exact (MK_COMB (@lem7577289) (@lem7577288)). Qed.
Lemma lem7577291 : term1007 = term1001.
Proof. exact (MK_COMB (@lem7577290) (@lem7577285)). Qed.
Lemma lem7577293 (m : nat) (n : nat) : (term932 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7577294 : term1001 = term1009.
Proof. exact (@lem7577293 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem7577295 : term1009 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem7577296 : term1001 = False.
Proof. exact (TRANS (@lem7577294) (@lem7577295)). Qed.
Lemma lem7577297 : term1007 = False.
Proof. exact (TRANS (@lem7577291) (@lem7577296)). Qed.
Lemma lem7577298 : term1004 = False.
Proof. exact (TRANS (@lem7577282) (@lem7577297)). Qed.
Lemma lem7577299 : term1001 = False.
Proof. exact (TRANS (@lem7577259) (@lem7577298)). Qed.
Lemma lem7577300 : term974 = False.
Proof. exact (TRANS (@lem7577250) (@lem7577299)). Qed.
Lemma lem7577301 (h1 : term974) : False.
Proof. exact (EQ_MP (@lem7577300) (@lem7577247 h1)). Qed.
Lemma lem7577302 (h1 : term974) : term974.
Proof. exact (h1). Qed.
Lemma lem7577304 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7577305 : term974 = term1001.
Proof. exact (@lem7577304 term781 term781). Qed.
Lemma lem7577307 (x : nat) : (real_of_num x) = (term922 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7577308 : term781 = term956.
Proof. exact (@lem7577307 (NUMERAL 0)). Qed.
Lemma lem7577310 (x : nat) : (real_of_num x) = (term922 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7577311 : term781 = term956.
Proof. exact (@lem7577310 (NUMERAL 0)). Qed.
Lemma lem7577312 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7577313 : term1002 = term1003.
Proof. exact (MK_COMB (@lem7577312) (@lem7577311)). Qed.
Lemma lem7577314 : term1001 = term1004.
Proof. exact (MK_COMB (@lem7577313) (@lem7577308)). Qed.
Lemma lem7577315 : term1005.
Proof. exact (@lem1980255 term781 term574 term781 term574). Qed.
Lemma lem7577317 (m : nat) (n : nat) : (term932 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7577318 : term933 = term934.
Proof. exact (@lem7577317 (NUMERAL 0) term22). Qed.
Lemma lem7577319 : term935 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7577320 (h1 : term935 = (BIT1 0)) : term934 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7577321 : (term935 = (BIT1 0)) = (term934 = True).
Proof. exact (prop_ext (fun h1 : term935 = (BIT1 0) => @lem7577320 h1) (fun h1 : term934 = True => @lem7577319)). Qed.
Lemma lem7577322 : term934 = True.
Proof. exact (EQ_MP (@lem7577321) (@lem7577319)). Qed.
Lemma lem7577323 : term933 = True.
Proof. exact (TRANS (@lem7577318) (@lem7577322)). Qed.
Lemma lem7577324 : True = term933.
Proof. exact (SYM (@lem7577323)). Qed.
Lemma lem7577325 : term933.
Proof. exact (EQ_MP (@lem7577324) (@lem0)). Qed.
Lemma lem7577326 : term1006.
Proof. exact (@lem7577315 (@lem7577325)). Qed.
Lemma lem7577328 (m : nat) (n : nat) : (term932 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7577329 : term933 = term934.
Proof. exact (@lem7577328 (NUMERAL 0) term22). Qed.
Lemma lem7577330 : term935 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7577331 (h1 : term935 = (BIT1 0)) : term934 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7577332 : (term935 = (BIT1 0)) = (term934 = True).
Proof. exact (prop_ext (fun h1 : term935 = (BIT1 0) => @lem7577331 h1) (fun h1 : term934 = True => @lem7577330)). Qed.
Lemma lem7577333 : term934 = True.
Proof. exact (EQ_MP (@lem7577332) (@lem7577330)). Qed.
Lemma lem7577334 : term933 = True.
Proof. exact (TRANS (@lem7577329) (@lem7577333)). Qed.
Lemma lem7577335 : True = term933.
Proof. exact (SYM (@lem7577334)). Qed.
Lemma lem7577336 : term933.
Proof. exact (EQ_MP (@lem7577335) (@lem0)). Qed.
Lemma lem7577337 : term1004 = term1007.
Proof. exact (@lem7577326 (@lem7577336)). Qed.
Lemma lem7577339 (x : nat) : (term954 x) = term781.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7577340 : term912 = term781.
Proof. exact (@lem7577339 term22). Qed.
Lemma lem7577342 (x : nat) : (term954 x) = term781.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7577343 : term912 = term781.
Proof. exact (@lem7577342 term22). Qed.
Lemma lem7577344 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7577345 : term1008 = term1002.
Proof. exact (MK_COMB (@lem7577344) (@lem7577343)). Qed.
Lemma lem7577346 : term1007 = term1001.
Proof. exact (MK_COMB (@lem7577345) (@lem7577340)). Qed.
Lemma lem7577348 (m : nat) (n : nat) : (term932 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7577349 : term1001 = term1009.
Proof. exact (@lem7577348 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem7577350 : term1009 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem7577351 : term1001 = False.
Proof. exact (TRANS (@lem7577349) (@lem7577350)). Qed.
Lemma lem7577352 : term1007 = False.
Proof. exact (TRANS (@lem7577346) (@lem7577351)). Qed.
Lemma lem7577353 : term1004 = False.
Proof. exact (TRANS (@lem7577337) (@lem7577352)). Qed.
Lemma lem7577354 : term1001 = False.
Proof. exact (TRANS (@lem7577314) (@lem7577353)). Qed.
Lemma lem7577355 : term974 = False.
Proof. exact (TRANS (@lem7577305) (@lem7577354)). Qed.
Lemma lem7577356 (h1 : term974) : False.
Proof. exact (EQ_MP (@lem7577355) (@lem7577302 h1)). Qed.
Lemma lem7577357 (h1 : term979) : False.
Proof. exact (or_elim (@lem7577246 h1) (fun h0 : term974 => @lem7577301 h0) (fun h0 : term974 => @lem7577356 h0)). Qed.
Lemma lem7577359 (h1 : term979) : term979.
Proof. exact (h1). Qed.
Lemma lem7577360 (h1 : term979) : term979 = False.
Proof. exact (prop_ext (fun h2 : term979 => @lem7577357 h1) (fun h2 : False => @lem7577359 h1)). Qed.
Lemma lem7577361 (h1 : term979) : False.
Proof. exact (EQ_MP (@lem7577360 h1) (@lem7577359 h1)). Qed.
Lemma lem7577362 (n : nat) (a : nat -> real) (h1 : term902 n a) : term902 n a.
Proof. exact (h1). Qed.
Lemma lem7577363 (n : nat) (a : nat -> real) (h1 : term902 n a) : term979.
Proof. exact (EQ_MP (@lem7577236 n a) (@lem7577362 n a h1)). Qed.
Lemma lem7577364 (n : nat) (a : nat -> real) (h1 : term902 n a) : term979 = False.
Proof. exact (prop_ext (fun h2 : term979 => @lem7577361 h2) (fun h2 : False => @lem7577363 n a h1)). Qed.
Lemma lem7577365 (n : nat) (a : nat -> real) (h1 : term902 n a) : False.
Proof. exact (EQ_MP (@lem7577364 n a h1) (@lem7577363 n a h1)). Qed.
Lemma lem7577366 (n : nat) (a : nat -> real) : term1010 n a.
Proof. exact (fun h0 : term902 n a => @lem7577365 n a h0). Qed.
Lemma lem7577367 (n : nat) (a : nat -> real) : term1011 n a.
Proof. exact (@lem1386578 (term899 n a)). Qed.
Lemma lem7577370 (n : nat) (a : nat -> real) : term899 n a.
Proof. exact (@lem7577367 n a (@lem7577366 n a)). Qed.
Lemma lem7577371 (n : nat) (a : nat -> real) : term884 n a.
Proof. exact (EQ_MP (@lem7576951 n a) (@lem7577370 n a)). Qed.
Lemma lem7577372 (q : real -> real) (n : nat) (a : nat -> real) (h1 : term419 q n a) : term838 q n a.
Proof. exact (EQ_MP (@lem7576889 q n a h1) (@lem7577371 n a)). Qed.
Lemma lem7577373 (q : real -> real) (n : nat) (a : nat -> real) (h1 : term419 q n a) : term837 q n a.
Proof. exact (EQ_MP (@lem7576710 q n a) (@lem7577372 q n a h1)). Qed.
Lemma lem7577374 (q : real -> real) (n : nat) (a : nat -> real) (h1 : term419 q n a) : term1012 q n.
Proof. exact (ex_intro (term1013 q n) (term772 a) (@lem7577373 q n a h1)). Qed.
Lemma lem7577375 (q : real -> real) (n : nat) (a : nat -> real) (h1 : term419 q n a) : term735 q.
Proof. exact (ex_intro (term734 q) (term74 n) (@lem7577374 q n a h1)). Qed.
Lemma lem7577376 (q : real -> real) (n : nat) (a : nat -> real) (h1 : term419 q n a) : (term419 q n a) = (term735 q).
Proof. exact (prop_ext (fun h2 : term419 q n a => @lem7577375 q n a h1) (fun h2 : term735 q => @lem7575095 q n a h1)). Qed.
Lemma lem7577377 (q : real -> real) (n : nat) (a : nat -> real) (h1 : term419 q n a) : term735 q.
Proof. exact (EQ_MP (@lem7577376 q n a h1) (@lem7575095 q n a h1)). Qed.
Lemma lem7577378 (n : nat) (a : nat -> real) (q : real -> real) : term751 n a q.
Proof. exact (fun h0 : term419 q n a => @lem7577377 q n a h0). Qed.
Lemma lem7577383 (n : nat) (q : real -> real) : term754 n q.
Proof. exact (fun a : nat -> real => @lem7577378 n a q). Qed.
Lemma lem7577388 (q : real -> real) : term756 q.
Proof. exact (fun n : nat => @lem7577383 n q). Qed.
Lemma lem7577389 (q : real -> real) : term710 q.
Proof. exact (EQ_MP (@lem7575094 q) (@lem7577388 q)). Qed.
Lemma lem7577390 (p : real -> real) (m : nat) (c : nat -> real) (q : real -> real) (h1 : (term45 p m c) = q) : term709 p m c.
Proof. exact (EQ_MP (@lem7574894 p m c q h1) (@lem7577389 q)). Qed.
Lemma lem7577391 (p : real -> real) (m : nat) (c : nat -> real) (q : real -> real) (h1 : (term45 p m c) = q) : ((term45 p m c) = q) = (term709 p m c).
Proof. exact (prop_ext (fun h2 : (term45 p m c) = q => @lem7577390 p m c q h1) (fun h2 : term709 p m c => @lem7574794 p m c q h1)). Qed.
Lemma lem7577393 (p : real -> real) (m : nat) (c : nat -> real) (q : real -> real) (h1 : (term45 p m c) = q) : term709 p m c.
Proof. exact (EQ_MP (@lem7577391 p m c q h1) (@lem7574794 p m c q h1)). Qed.
Lemma lem7577394 (p : real -> real) (m : nat) (c : nat -> real) : term709 p m c.
Proof. exact (ex_elim (@lem7567920 p m c) (fun q : real -> real => fun h0 : term47 p m c q => @lem7577393 p m c q h0)). Qed.
Lemma lem7577395 (c : nat -> real) (p : real -> real) (m : nat) (h1 : term525 p m) : term673 p m c.
Proof. exact (@lem7577394 p m c (@lem7574793 c p m h1)). Qed.
Lemma lem7577396 (c : nat -> real) (p : real -> real) (m : nat) (h1 : term525 p m) : term644 p m c.
Proof. exact (EQ_MP (@lem7574790 p m c) (@lem7577395 c p m h1)). Qed.
Lemma lem7577397 (c : nat -> real) (p : real -> real) (m : nat) (h1 : term525 p m) : term629 p m c.
Proof. exact (EQ_MP (@lem7574694 p m c) (@lem7577396 c p m h1)). Qed.
Lemma lem7577398 (c : nat -> real) (m : nat) (p : real -> real) (h1 : term525 p m) (h2 : polynomial_function p) : term630 p m c.
Proof. exact (EQ_MP (@lem7574668 m c p h2) (@lem7577397 c p m h1)). Qed.
Lemma lem7577399 (c : nat -> real) (m : nat) (p : real -> real) (h1 : term525 p m) (h2 : polynomial_function p) : term617 p m c.
Proof. exact (@lem7574391 p m c (@lem7577398 c m p h1 h2)). Qed.
Lemma lem7577400 (c : nat -> real) (m : nat) (p : real -> real) (h1 : term525 p m) (h2 : polynomial_function p) : term609 p m c.
Proof. exact (EQ_MP (@lem7574377 p m c) (@lem7577399 c m p h1 h2)). Qed.
Lemma lem7577401 (c : nat -> real) (m : nat) (p : real -> real) (h1 : term525 p m) (h2 : polynomial_function p) : term608 p m c.
Proof. exact (EQ_MP (@lem7574359 p m c) (@lem7577400 c m p h1 h2)). Qed.
Lemma lem7577407 (m : nat) (p : real -> real) (h1 : term525 p m) (h2 : polynomial_function p) : term538 p m.
Proof. exact (fun c : nat -> real => @lem7577401 c m p h1 h2). Qed.
Lemma lem7577408 (m : nat) (p : real -> real) (h1 : polynomial_function p) : term540 p m.
Proof. exact (fun h0 : term525 p m => @lem7577407 m p h0 h1). Qed.
Lemma lem7577413 (p : real -> real) (h1 : polynomial_function p) : term544 p.
Proof. exact (fun m : nat => @lem7577408 m p h1). Qed.
Lemma lem7577414 (p : real -> real) (h1 : polynomial_function p) : term546 p.
Proof. exact (conj (@lem7573437 p h1) (@lem7577413 p h1)). Qed.
Lemma lem7577415 (p : real -> real) (h1 : polynomial_function p) : term527 p.
Proof. exact (@lem7573355 p (@lem7577414 p h1)). Qed.
Lemma lem7577416 (p : real -> real) (h1 : polynomial_function p) : term504 p.
Proof. exact (EQ_MP (@lem7573332 p) (@lem7577415 p h1)). Qed.
Lemma lem7577417 (p : real -> real) (h1 : polynomial_function p) : term487 p.
Proof. exact (EQ_MP (@lem7573270 p) (@lem7577416 p h1)). Qed.
Lemma lem7577418 (p : real -> real) (h1 : polynomial_function p) : term458 p.
Proof. exact (EQ_MP (@lem7573227 p) (@lem7577417 p h1)). Qed.
Lemma lem7577419 (p : real -> real) (h1 : polynomial_function p) : term393 p.
Proof. exact (EQ_MP (@lem7573182 p) (@lem7577418 p h1)). Qed.
Lemma lem7577420 (p : real -> real) (h1 : polynomial_function p) : term384 p.
Proof. exact (EQ_MP (@lem7568991 p) (@lem7577419 p h1)). Qed.
Lemma lem7577421 (p : real -> real) : term385 p.
Proof. exact (fun h0 : polynomial_function p => @lem7577420 p h0). Qed.
Lemma lem7577426 : term389.
Proof. exact (fun p : real -> real => @lem7577421 p). Qed.
Lemma lem7577427 : term388.
Proof. exact (EQ_MP (@lem7568979) (@lem7577426)). Qed.
