Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_INT_SEG_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import FINITE_EMPTY_spec.
Require Import FINITE_IMAGE_spec.
Require Import FINITE_NUMSEG_spec.
Require Import FINITE_SUBSET_spec.
Require Import INT_OF_NUM_LE_spec.
Require Import INT_OF_NUM_OF_INT_spec.
Require Import INT_SUB_LE_spec.
Require Import IN_IMAGE_spec.
Require Import IN_NUMSEG_spec.
Require Import MONO_FORALL_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import SUBSET_spec.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367763_spec.
Require Import thm1386578_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17362_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1820_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1844_spec.
Require Import thm1845_spec.
Require Import thm19158_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980026_spec.
Require Import thm1980255_spec.
Require Import thm1980259_spec.
Require Import thm1980260_spec.
Require Import thm1980265_spec.
Require Import thm1980266_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982709_spec.
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982733_spec.
Require Import thm1982749_spec.
Require Import thm1982753_spec.
Require Import thm1982755_spec.
Require Import thm1982757_spec.
Require Import thm1982759_spec.
Require Import thm1982761_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988332_spec.
Require Import thm1988342_spec.
Require Import thm2841542_spec.
Require Import thm2841544_spec.
Require Import thm2841573_spec.
Require Import thm2841574_spec.
Require Import thm2841585_spec.
Require Import thm2841586_spec.
Require Import thm2841591_spec.
Require Import thm2841592_spec.
Require Import thm2841615_spec.
Require Import thm2841616_spec.
Require Import thm2954598_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm3399706_spec.
Require Import thm3399757_spec.
Require Import thm7_spec.
Require Import thm706885_spec.
Require Import thm82_spec.
Require Import thm912739_spec.
Require Import thm912803_spec.
Require Import thm940073_spec.
Require Import thm951_spec.
Require Import thm952_spec.
Require Import thm996237_spec.
Lemma lem5700877 (m : nat) (n : nat) (h1 : (term0 m n) = (Peano.le m n)) : (term0 m n) = (Peano.le m n).
Proof. exact (h1). Qed.
Lemma lem5700878 (m : nat) (n : nat) (h1 : (term0 m n) = (Peano.le m n)) : (Peano.le m n) = (term0 m n).
Proof. exact (SYM (@lem5700877 m n h1)). Qed.
Lemma lem5700879 (m : nat) (n : nat) (h1 : (Peano.le m n) = (term0 m n)) : (Peano.le m n) = (term0 m n).
Proof. exact (h1). Qed.
Lemma lem5700880 (m : nat) (n : nat) (h1 : (Peano.le m n) = (term0 m n)) : (term0 m n) = (Peano.le m n).
Proof. exact (SYM (@lem5700879 m n h1)). Qed.
Lemma lem5700881 (m : nat) (n : nat) : ((term0 m n) = (Peano.le m n)) = ((Peano.le m n) = (term0 m n)).
Proof. exact (prop_ext (fun h1 : (term0 m n) = (Peano.le m n) => @lem5700878 m n h1) (fun h1 : (Peano.le m n) = (term0 m n) => @lem5700880 m n h1)). Qed.
Lemma lem5700882 (m : nat) : (term1 m) = (term2 m).
Proof. exact (fun_ext (fun n : nat => @lem5700881 m n)). Qed.
Lemma lem5700883 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5700884 (m : nat) : (term3 m) = (term4 m).
Proof. exact (MK_COMB (@lem5700883) (@lem5700882 m)). Qed.
Lemma lem5700885 : term5 = term6.
Proof. exact (fun_ext (fun m : nat => @lem5700884 m)). Qed.
Lemma lem5700886 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5700887 : term7 = term8.
Proof. exact (MK_COMB (@lem5700886) (@lem5700885)). Qed.
Lemma lem5700888 : term8.
Proof. exact (EQ_MP (@lem5700887) (@lem2307222)). Qed.
Lemma lem5700889 (m : nat) : term9 m.
Proof. exact (@lem5371273 m). Qed.
Lemma lem5700890 (m : nat) : (term9 m) = (term10 m).
Proof. exact (eq_refl (term9 m)). Qed.
Lemma lem5700891 (m : nat) : term10 m.
Proof. exact (EQ_MP (@lem5700890 m) (@lem5700889 m)). Qed.
Lemma lem5700892 (m : nat) (n : nat) : term11 m n.
Proof. exact (@lem5700891 m n). Qed.
Lemma lem5700893 (m : nat) (n : nat) : (term11 m n) = (term12 m n).
Proof. exact (eq_refl (term11 m n)). Qed.
Lemma lem5700894 (m : nat) (n : nat) : term12 m n.
Proof. exact (EQ_MP (@lem5700893 m n) (@lem5700892 m n)). Qed.
Lemma lem5700895 (m : nat) (n : nat) (p : nat) : term13 m n p.
Proof. exact (@lem5700894 m n p). Qed.
Lemma lem5700896 (m : nat) (p : nat) (n : nat) : (term13 m n p) = ((term14 p m n) = (term15 m p n)).
Proof. exact (eq_refl (term13 m n p)). Qed.
Lemma lem5700898 (m : nat) : term16 m.
Proof. exact (@lem5700888 m). Qed.
Lemma lem5700899 (m : nat) : (term16 m) = (term4 m).
Proof. exact (eq_refl (term16 m)). Qed.
Lemma lem5700900 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem5700899 m) (@lem5700898 m)). Qed.
Lemma lem5700901 (m : nat) (n : nat) : term17 m n.
Proof. exact (@lem5700900 m n). Qed.
Lemma lem5700902 (m : nat) (n : nat) : (term17 m n) = ((Peano.le m n) = (term0 m n)).
Proof. exact (eq_refl (term17 m n)). Qed.
Lemma lem5700928 {_83095 : Type'} : term18 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem5700929 {_83095 : Type'} (p : _83095 -> Prop) : term19 _83095 p.
Proof. exact (@lem5700928 _83095 p). Qed.
Lemma lem5700930 {_83095 : Type'} (p : _83095 -> Prop) : (term19 _83095 p) = (term20 _83095 p).
Proof. exact (eq_refl (term19 _83095 p)). Qed.
Lemma lem5700931 {_83095 : Type'} (p : _83095 -> Prop) : term20 _83095 p.
Proof. exact (EQ_MP (@lem5700930 _83095 p) (@lem5700929 _83095 p)). Qed.
Lemma lem5700932 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term21 _83095 p x.
Proof. exact (@lem5700931 _83095 p x). Qed.
Lemma lem5700933 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term21 _83095 p x) = ((term22 _83095 x p) = (p x)).
Proof. exact (eq_refl (term21 _83095 p x)). Qed.
Lemma lem5700942 {A B : Type'} (y : B) : term23 A B y.
Proof. exact (@lem3206070 A B y). Qed.
Lemma lem5700943 {A B : Type'} (y : B) : (term23 A B y) = (term24 A B y).
Proof. exact (eq_refl (term23 A B y)). Qed.
Lemma lem5700944 {A B : Type'} (y : B) : term24 A B y.
Proof. exact (EQ_MP (@lem5700943 A B y) (@lem5700942 A B y)). Qed.
Lemma lem5700945 {A B : Type'} (y : B) (s : A -> Prop) : term25 A B y s.
Proof. exact (@lem5700944 A B y s). Qed.
Lemma lem5700946 {A B : Type'} (y : B) (s : A -> Prop) : (term25 A B y s) = (term26 A B y s).
Proof. exact (eq_refl (term25 A B y s)). Qed.
Lemma lem5700947 {A B : Type'} (y : B) (s : A -> Prop) : term26 A B y s.
Proof. exact (EQ_MP (@lem5700946 A B y s) (@lem5700945 A B y s)). Qed.
Lemma lem5700948 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : term27 A B y s f.
Proof. exact (@lem5700947 A B y s f). Qed.
Lemma lem5700949 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term27 A B y s f) = ((term28 A B y f s) = (term29 A B y f s)).
Proof. exact (eq_refl (term27 A B y s f)). Qed.
Lemma lem5700951 {A : Type'} (s : A -> Prop) : term30 A s.
Proof. exact (@lem3194148 A s). Qed.
Lemma lem5700952 {A : Type'} (s : A -> Prop) : (term30 A s) = (term31 A s).
Proof. exact (eq_refl (term30 A s)). Qed.
Lemma lem5700953 {A : Type'} (s : A -> Prop) : term31 A s.
Proof. exact (EQ_MP (@lem5700952 A s) (@lem5700951 A s)). Qed.
Lemma lem5700954 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term32 A s t.
Proof. exact (@lem5700953 A s t). Qed.
Lemma lem5700955 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term32 A s t) = ((@SUBSET A s t) = (term33 A s t)).
Proof. exact (eq_refl (term32 A s t)). Qed.
Lemma lem5700957 {A : Type'} (h1 : term34 A) : term34 A.
Proof. exact (h1). Qed.
Lemma lem5700958 {A : Type'} (s : A -> Prop) (h1 : term34 A) : term35 A s.
Proof. exact (@lem5700957 A h1 s). Qed.
Lemma lem5700959 {A : Type'} (s : A -> Prop) : (term35 A s) = (term36 A s).
Proof. exact (eq_refl (term35 A s)). Qed.
Lemma lem5700960 {A : Type'} (s : A -> Prop) (h1 : term34 A) : term36 A s.
Proof. exact (EQ_MP (@lem5700959 A s) (@lem5700958 A s h1)). Qed.
Lemma lem5700961 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term34 A) : term37 A s t.
Proof. exact (@lem5700960 A s h1 t). Qed.
Lemma lem5700962 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term37 A s t) = (term38 A t s).
Proof. exact (eq_refl (term37 A s t)). Qed.
Lemma lem5700963 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term34 A) : term38 A t s.
Proof. exact (EQ_MP (@lem5700962 A t s) (@lem5700961 A s t h1)). Qed.
Lemma lem5700964 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term39 A s t) : term39 A s t.
Proof. exact (h1). Qed.
Lemma lem5700965 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term34 A) (h2 : term39 A s t) : @FINITE A s.
Proof. exact (@lem5700963 A t s h1 (@lem5700964 A s t h2)). Qed.
Lemma lem5700966 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term39 A s t) : term40 A s.
Proof. exact (fun h0 : term34 A => @lem5700965 A s t h0 h1). Qed.
Lemma lem5700967 {A : Type'} (s : A -> Prop) (h1 : term41 A s) : term41 A s.
Proof. exact (h1). Qed.
Lemma lem5700968 {A : Type'} (s : A -> Prop) (h1 : term41 A s) : term40 A s.
Proof. exact (ex_elim (@lem5700967 A s h1) (fun t : A -> Prop => fun h0 : term42 A s t => @lem5700966 A s t h0)). Qed.
Lemma lem5700969 {A : Type'} (h1 : term34 A) : term34 A.
Proof. exact (h1). Qed.
Lemma lem5700970 {A : Type'} (s : A -> Prop) (h1 : term34 A) (h2 : term41 A s) : @FINITE A s.
Proof. exact (@lem5700968 A s h2 (@lem5700969 A h1)). Qed.
Lemma lem5700971 {A : Type'} (s : A -> Prop) (h1 : term34 A) : term43 A s.
Proof. exact (fun h0 : term41 A s => @lem5700970 A s h1 h0). Qed.
Lemma lem5700972 {A : Type'} (h1 : term34 A) : term44 A.
Proof. exact (fun s : A -> Prop => @lem5700971 A s h1). Qed.
Lemma lem5700973 {A : Type'} : term45 A.
Proof. exact (fun h0 : term34 A => @lem5700972 A h0). Qed.
Lemma lem5700974 {A : Type'} : term44 A.
Proof. exact (@lem5700973 A (@lem3599924 A)). Qed.
Lemma lem5700975 {A : Type'} (s : A -> Prop) : term46 A s.
Proof. exact (@lem5700974 A s). Qed.
Lemma lem5700976 {A : Type'} (s : A -> Prop) : (term46 A s) = (term43 A s).
Proof. exact (eq_refl (term46 A s)). Qed.
Lemma lem5700978 (l : int) (x : int) (r : int) : (term47 l x r) = (term48 l x r).
Proof. exact (@lem2954598 (term48 l x r)). Qed.
Lemma lem5700995 (l : int) (x : int) (r : int) : (term49 l x r) = (term50 l x r).
Proof. exact (@lem16933 (term50 l x r)). Qed.
Lemma lem5700997 (r : int) (l : int) : (term51 r l) = (term51 r l).
Proof. exact (eq_refl (term51 r l)). Qed.
Lemma lem5700998 (l : int) (x : int) (r : int) : (term52 l x r) = (term53 l x r).
Proof. exact (MK_COMB (@lem5700997 r l) (@lem5700995 l x r)). Qed.
Lemma lem5700999 (l : int) (x : int) (r : int) : (term54 l x r) = (term52 l x r).
Proof. exact (@lem17362 (term55 r l) (term56 l x r)). Qed.
Lemma lem5701026 (l : int) (x : int) (r : int) : (term54 l x r) = (term53 l x r).
Proof. exact (TRANS (@lem5700999 l x r) (@lem5700998 l x r)). Qed.
Lemma lem5701028 (y : int) (x : int) : (term57 x y) = (term58 y x).
Proof. exact (proj1 (@lem2841542 x y)). Qed.
Lemma lem5701029 (r : int) (l : int) : (term55 r l) = (term59 r l).
Proof. exact (@lem5701028 (int_sub r l) term60). Qed.
Lemma lem5701031 (x : int) (y : int) : (int_le x y) = (term61 x y).
Proof. exact (EQ_MP (@lem2841616 x y) (@lem2841615 x y)). Qed.
Lemma lem5701032 (r : int) (l : int) : (term59 r l) = (term62 r l).
Proof. exact (@lem5701031 (term63 r l) term60). Qed.
Lemma lem5701034 (x : int) (y : int) : (term64 x y) = (term65 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem5701035 (r : int) (l : int) : (term66 r l) = (term67 r l).
Proof. exact (@lem5701034 (int_sub r l) term68). Qed.
Lemma lem5701037 (x : int) (y : int) : (term69 x y) = (term70 x y).
Proof. exact (EQ_MP (@lem2841574 x y) (@lem2841573 x y)). Qed.
Lemma lem5701038 (r : int) (l : int) : (term69 r l) = (term70 r l).
Proof. exact (@lem5701037 r l). Qed.
Lemma lem5701039 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5701040 (r : int) (l : int) : (term71 r l) = (term72 r l).
Proof. exact (MK_COMB (@lem5701039) (@lem5701038 r l)). Qed.
Lemma lem5701042 (n : nat) : (term73 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem5701043 : term74 = term75.
Proof. exact (@lem5701042 term76). Qed.
Lemma lem5701044 (r : int) (l : int) : (term67 r l) = (term77 r l).
Proof. exact (MK_COMB (@lem5701040 r l) (@lem5701043)). Qed.
Lemma lem5701045 (r : int) (l : int) : (term66 r l) = (term77 r l).
Proof. exact (TRANS (@lem5701035 r l) (@lem5701044 r l)). Qed.
Lemma lem5701046 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5701047 (r : int) (l : int) : (term78 r l) = (term79 r l).
Proof. exact (MK_COMB (@lem5701046) (@lem5701045 r l)). Qed.
Lemma lem5701049 (n : nat) : (term73 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem5701050 : term80 = term81.
Proof. exact (@lem5701049 (NUMERAL 0)). Qed.
Lemma lem5701051 (r : int) (l : int) : (term62 r l) = (term82 r l).
Proof. exact (MK_COMB (@lem5701047 r l) (@lem5701050)). Qed.
Lemma lem5701052 (r : int) (l : int) : (term59 r l) = (term82 r l).
Proof. exact (TRANS (@lem5701032 r l) (@lem5701051 r l)). Qed.
Lemma lem5701053 (r : int) (l : int) : (term55 r l) = (term82 r l).
Proof. exact (TRANS (@lem5701029 r l) (@lem5701052 r l)). Qed.
Lemma lem5701056 (x : int) (y : int) : (int_le x y) = (term61 x y).
Proof. exact (EQ_MP (@lem2841616 x y) (@lem2841615 x y)). Qed.
Lemma lem5701058 (l : int) (x : int) : (int_le l x) = (term61 l x).
Proof. exact (@lem5701056 l x). Qed.
Lemma lem5701061 (x : int) (y : int) : (int_le x y) = (term61 x y).
Proof. exact (EQ_MP (@lem2841616 x y) (@lem2841615 x y)). Qed.
Lemma lem5701063 (x : int) (r : int) : (int_le x r) = (term61 x r).
Proof. exact (@lem5701061 x r). Qed.
Lemma lem5701064 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5701065 (l : int) (x : int) : (term83 l x) = (term84 l x).
Proof. exact (MK_COMB (@lem5701064) (@lem5701058 l x)). Qed.
Lemma lem5701066 (l : int) (x : int) (r : int) : (term50 l x r) = (term85 l x r).
Proof. exact (MK_COMB (@lem5701065 l x) (@lem5701063 x r)). Qed.
Lemma lem5701067 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5701068 (r : int) (l : int) : (term51 r l) = (term86 r l).
Proof. exact (MK_COMB (@lem5701067) (@lem5701053 r l)). Qed.
Lemma lem5701069 (l : int) (x : int) (r : int) : (term53 l x r) = (term87 l x r).
Proof. exact (MK_COMB (@lem5701068 r l) (@lem5701066 l x r)). Qed.
Lemma lem5701070 (l : int) (x : int) (r : int) : (term54 l x r) = (term87 l x r).
Proof. exact (TRANS (@lem5701026 l x r) (@lem5701069 l x r)). Qed.
Lemma lem5701074 (t : Prop) : (term88 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5701100 (l : int) (x : int) (r : int) : (term89 l x r) = (term87 l x r).
Proof. exact (@lem5701074 (term87 l x r)). Qed.
Lemma lem5701101 (r : int) (l : int) : (term82 r l) = (term90 r l).
Proof. exact (@lem1988287 term81 (term77 r l)). Qed.
Lemma lem5701102 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem5701108 (r : int) (l : int) : (term70 r l) = (term91 r l).
Proof. exact (@lem1982792 (real_of_int r) (real_of_int l)). Qed.
Lemma lem5701113 (l : int) (r : int) : (term91 r l) = (term92 l r).
Proof. exact (@lem1982761 (term93 l) (real_of_int r)). Qed.
Lemma lem5701115 (l : int) (r : int) : (term70 r l) = (term92 l r).
Proof. exact (TRANS (@lem5701108 r l) (@lem5701113 l r)). Qed.
Lemma lem5701116 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5701117 (l : int) (r : int) : (term72 r l) = (term94 l r).
Proof. exact (MK_COMB (@lem5701116) (@lem5701115 l r)). Qed.
Lemma lem5701118 (l : int) (r : int) : (term77 r l) = (term95 l r).
Proof. exact (MK_COMB (@lem5701117 l r) (@lem5701102)). Qed.
Lemma lem5701123 (l : int) (r : int) : (term95 l r) = (term96 l r).
Proof. exact (@lem1982755 (term93 l) (real_of_int r) term75). Qed.
Lemma lem5701124 (l : int) (r : int) : (term77 r l) = (term96 l r).
Proof. exact (TRANS (@lem5701118 l r) (@lem5701123 l r)). Qed.
Lemma lem5701127 : term97 = term97.
Proof. exact (eq_refl term97). Qed.
Lemma lem5701128 (l : int) (r : int) : (term98 r l) = (term99 l r).
Proof. exact (MK_COMB (@lem5701127) (@lem5701124 l r)). Qed.
Lemma lem5701129 (l : int) (r : int) : (term99 l r) = (term100 l r).
Proof. exact (@lem1982792 term81 (term96 l r)). Qed.
Lemma lem5701130 (l : int) (r : int) : (term101 l r) = (term102 l r).
Proof. exact (@lem1982781 (term93 l) term103 (term104 r)). Qed.
Lemma lem5701131 (r : int) : (term105 r) = (term106 r).
Proof. exact (@lem1982781 (real_of_int r) term103 term75). Qed.
Lemma lem5701133 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5701134 : term75 = term108.
Proof. exact (@lem5701133 term76). Qed.
Lemma lem5701136 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5701137 : term103 = term111.
Proof. exact (@lem5701136 term76). Qed.
Lemma lem5701138 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5701139 : term112 = term113.
Proof. exact (MK_COMB (@lem5701138) (@lem5701137)). Qed.
Lemma lem5701140 : term114 = term115.
Proof. exact (MK_COMB (@lem5701139) (@lem5701134)). Qed.
Lemma lem5701141 : term115 = term116.
Proof. exact (@lem1981613 term103 term75 term75 term75). Qed.
Lemma lem5701143 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5701144 : term119 = term120.
Proof. exact (@lem5701143 term76 term76). Qed.
Lemma lem5701145 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5701146 : term122 = term76.
Proof. exact (EQ_MP (@lem5701145) (@lem940073)). Qed.
Lemma lem5701147 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5701148 : term120 = term75.
Proof. exact (MK_COMB (@lem5701147) (@lem5701146)). Qed.
Lemma lem5701149 : term119 = term75.
Proof. exact (TRANS (@lem5701144) (@lem5701148)). Qed.
Lemma lem5701151 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5701152 : term114 = term125.
Proof. exact (@lem5701151 term76 term76). Qed.
Lemma lem5701153 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5701154 : term122 = term76.
Proof. exact (EQ_MP (@lem5701153) (@lem940073)). Qed.
Lemma lem5701155 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5701156 : term120 = term75.
Proof. exact (MK_COMB (@lem5701155) (@lem5701154)). Qed.
Lemma lem5701157 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5701158 : term125 = term103.
Proof. exact (MK_COMB (@lem5701157) (@lem5701156)). Qed.
Lemma lem5701159 : term114 = term103.
Proof. exact (TRANS (@lem5701152) (@lem5701158)). Qed.
Lemma lem5701160 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5701161 : term126 = term127.
Proof. exact (MK_COMB (@lem5701160) (@lem5701159)). Qed.
Lemma lem5701162 : term116 = term111.
Proof. exact (MK_COMB (@lem5701161) (@lem5701149)). Qed.
Lemma lem5701163 : term115 = term111.
Proof. exact (TRANS (@lem5701141) (@lem5701162)). Qed.
Lemma lem5701164 : term114 = term111.
Proof. exact (TRANS (@lem5701140) (@lem5701163)). Qed.
Lemma lem5701166 (x : real) : (term128 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5701167 : term111 = term103.
Proof. exact (@lem5701166 term103). Qed.
Lemma lem5701168 : term114 = term103.
Proof. exact (TRANS (@lem5701164) (@lem5701167)). Qed.
Lemma lem5701171 (r : int) : (term129 r) = (term129 r).
Proof. exact (eq_refl (term129 r)). Qed.
Lemma lem5701172 (r : int) : (term106 r) = (term130 r).
Proof. exact (MK_COMB (@lem5701171 r) (@lem5701168)). Qed.
Lemma lem5701173 (r : int) : (term105 r) = (term130 r).
Proof. exact (TRANS (@lem5701131 r) (@lem5701172 r)). Qed.
Lemma lem5701174 (l : int) : (term131 l) = (term132 l).
Proof. exact (@lem1982749 term103 term103 (real_of_int l)). Qed.
Lemma lem5701176 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5701177 : term103 = term111.
Proof. exact (@lem5701176 term76). Qed.
Lemma lem5701179 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5701180 : term103 = term111.
Proof. exact (@lem5701179 term76). Qed.
Lemma lem5701181 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5701182 : term112 = term113.
Proof. exact (MK_COMB (@lem5701181) (@lem5701180)). Qed.
Lemma lem5701183 : term133 = term134.
Proof. exact (MK_COMB (@lem5701182) (@lem5701177)). Qed.
Lemma lem5701184 : term134 = term135.
Proof. exact (@lem1981613 term103 term103 term75 term75). Qed.
Lemma lem5701186 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5701187 : term119 = term120.
Proof. exact (@lem5701186 term76 term76). Qed.
Lemma lem5701188 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5701189 : term122 = term76.
Proof. exact (EQ_MP (@lem5701188) (@lem940073)). Qed.
Lemma lem5701190 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5701191 : term120 = term75.
Proof. exact (MK_COMB (@lem5701190) (@lem5701189)). Qed.
Lemma lem5701192 : term119 = term75.
Proof. exact (TRANS (@lem5701187) (@lem5701191)). Qed.
Lemma lem5701194 (m : nat) (n : nat) : (term136 m n) = (term118 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem5701195 : term133 = term120.
Proof. exact (@lem5701194 term76 term76). Qed.
Lemma lem5701196 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5701197 : term122 = term76.
Proof. exact (EQ_MP (@lem5701196) (@lem940073)). Qed.
Lemma lem5701198 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5701199 : term120 = term75.
Proof. exact (MK_COMB (@lem5701198) (@lem5701197)). Qed.
Lemma lem5701200 : term133 = term75.
Proof. exact (TRANS (@lem5701195) (@lem5701199)). Qed.
Lemma lem5701201 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5701202 : term137 = term138.
Proof. exact (MK_COMB (@lem5701201) (@lem5701200)). Qed.
Lemma lem5701203 : term135 = term108.
Proof. exact (MK_COMB (@lem5701202) (@lem5701192)). Qed.
Lemma lem5701204 : term134 = term108.
Proof. exact (TRANS (@lem5701184) (@lem5701203)). Qed.
Lemma lem5701205 : term133 = term108.
Proof. exact (TRANS (@lem5701183) (@lem5701204)). Qed.
Lemma lem5701207 (x : real) : (term128 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5701208 : term108 = term75.
Proof. exact (@lem5701207 term75). Qed.
Lemma lem5701209 : term133 = term75.
Proof. exact (TRANS (@lem5701205) (@lem5701208)). Qed.
Lemma lem5701210 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5701211 : term139 = term140.
Proof. exact (MK_COMB (@lem5701210) (@lem5701209)). Qed.
Lemma lem5701212 (l : int) : (real_of_int l) = (real_of_int l).
Proof. exact (eq_refl (real_of_int l)). Qed.
Lemma lem5701213 (l : int) : (term132 l) = (term141 l).
Proof. exact (MK_COMB (@lem5701211) (@lem5701212 l)). Qed.
Lemma lem5701214 (l : int) : (term131 l) = (term141 l).
Proof. exact (TRANS (@lem5701174 l) (@lem5701213 l)). Qed.
Lemma lem5701215 (l : int) : (term141 l) = (real_of_int l).
Proof. exact (@lem1982709 (real_of_int l)). Qed.
Lemma lem5701216 (l : int) : (term131 l) = (real_of_int l).
Proof. exact (TRANS (@lem5701214 l) (@lem5701215 l)). Qed.
Lemma lem5701217 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5701218 (l : int) : (term142 l) = (term143 l).
Proof. exact (MK_COMB (@lem5701217) (@lem5701216 l)). Qed.
Lemma lem5701219 (l : int) (r : int) : (term102 l r) = (term144 l r).
Proof. exact (MK_COMB (@lem5701218 l) (@lem5701173 r)). Qed.
Lemma lem5701220 (l : int) (r : int) : (term101 l r) = (term144 l r).
Proof. exact (TRANS (@lem5701130 l r) (@lem5701219 l r)). Qed.
Lemma lem5701221 : term145 = term145.
Proof. exact (eq_refl term145). Qed.
Lemma lem5701222 (l : int) (r : int) : (term100 l r) = (term146 l r).
Proof. exact (MK_COMB (@lem5701221) (@lem5701220 l r)). Qed.
Lemma lem5701223 (l : int) (r : int) : (term146 l r) = (term144 l r).
Proof. exact (@lem1982721 (term144 l r)). Qed.
Lemma lem5701224 (l : int) (r : int) : (term100 l r) = (term144 l r).
Proof. exact (TRANS (@lem5701222 l r) (@lem5701223 l r)). Qed.
Lemma lem5701225 (l : int) (r : int) : (term99 l r) = (term144 l r).
Proof. exact (TRANS (@lem5701129 l r) (@lem5701224 l r)). Qed.
Lemma lem5701226 (l : int) (r : int) : (term98 r l) = (term144 l r).
Proof. exact (TRANS (@lem5701128 l r) (@lem5701225 l r)). Qed.
Lemma lem5701227 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5701228 (l : int) (r : int) : (term147 r l) = (term148 l r).
Proof. exact (MK_COMB (@lem5701227) (@lem5701226 l r)). Qed.
Lemma lem5701229 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem5701230 (l : int) (r : int) : (term90 r l) = (term149 l r).
Proof. exact (MK_COMB (@lem5701228 l r) (@lem5701229)). Qed.
Lemma lem5701231 (l : int) (r : int) : (term82 r l) = (term149 l r).
Proof. exact (TRANS (@lem5701101 r l) (@lem5701230 l r)). Qed.
Lemma lem5701232 (x : int) (l : int) : (term61 l x) = (term150 x l).
Proof. exact (@lem1988287 (real_of_int x) (real_of_int l)). Qed.
Lemma lem5701238 (x : int) (l : int) : (term70 x l) = (term91 x l).
Proof. exact (@lem1982792 (real_of_int x) (real_of_int l)). Qed.
Lemma lem5701243 (l : int) (x : int) : (term91 x l) = (term92 l x).
Proof. exact (@lem1982761 (term93 l) (real_of_int x)). Qed.
Lemma lem5701245 (l : int) (x : int) : (term70 x l) = (term92 l x).
Proof. exact (TRANS (@lem5701238 x l) (@lem5701243 l x)). Qed.
Lemma lem5701246 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5701247 (l : int) (x : int) : (term151 x l) = (term152 l x).
Proof. exact (MK_COMB (@lem5701246) (@lem5701245 l x)). Qed.
Lemma lem5701248 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem5701249 (l : int) (x : int) : (term150 x l) = (term153 l x).
Proof. exact (MK_COMB (@lem5701247 l x) (@lem5701248)). Qed.
Lemma lem5701250 (l : int) (x : int) : (term61 l x) = (term153 l x).
Proof. exact (TRANS (@lem5701232 x l) (@lem5701249 l x)). Qed.
Lemma lem5701251 (r : int) (x : int) : (term61 x r) = (term150 r x).
Proof. exact (@lem1988287 (real_of_int r) (real_of_int x)). Qed.
Lemma lem5701264 (r : int) (x : int) : (term70 r x) = (term91 r x).
Proof. exact (@lem1982792 (real_of_int r) (real_of_int x)). Qed.
Lemma lem5701265 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5701266 (r : int) (x : int) : (term151 r x) = (term154 r x).
Proof. exact (MK_COMB (@lem5701265) (@lem5701264 r x)). Qed.
Lemma lem5701267 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem5701268 (r : int) (x : int) : (term150 r x) = (term155 r x).
Proof. exact (MK_COMB (@lem5701266 r x) (@lem5701267)). Qed.
Lemma lem5701269 (r : int) (x : int) : (term61 x r) = (term155 r x).
Proof. exact (TRANS (@lem5701251 r x) (@lem5701268 r x)). Qed.
Lemma lem5701270 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5701271 (l : int) (x : int) : (term84 l x) = (term156 l x).
Proof. exact (MK_COMB (@lem5701270) (@lem5701250 l x)). Qed.
Lemma lem5701272 (l : int) (r : int) (x : int) : (term85 l x r) = (term157 l r x).
Proof. exact (MK_COMB (@lem5701271 l x) (@lem5701269 r x)). Qed.
Lemma lem5701273 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5701274 (l : int) (r : int) : (term86 r l) = (term158 l r).
Proof. exact (MK_COMB (@lem5701273) (@lem5701231 l r)). Qed.
Lemma lem5701275 (l : int) (r : int) (x : int) : (term87 l x r) = (term159 l r x).
Proof. exact (MK_COMB (@lem5701274 l r) (@lem5701272 l r x)). Qed.
Lemma lem5701296 (l : int) (r : int) (x : int) : (term89 l x r) = (term159 l r x).
Proof. exact (TRANS (@lem5701100 l x r) (@lem5701275 l r x)). Qed.
Lemma lem5701300 (l : int) (r : int) (x : int) (h1 : term159 l r x) : term159 l r x.
Proof. exact (h1). Qed.
Lemma lem5701301 (l : int) (r : int) (x : int) (h1 : term159 l r x) : term157 l r x.
Proof. exact (proj2 (@lem5701300 l r x h1)). Qed.
Lemma lem5701302 (l : int) (r : int) (x : int) (h1 : term159 l r x) : term149 l r.
Proof. exact (proj1 (@lem5701300 l r x h1)). Qed.
Lemma lem5701303 (l : int) (r : int) (x : int) (h1 : term159 l r x) : term155 r x.
Proof. exact (proj2 (@lem5701301 l r x h1)). Qed.
Lemma lem5701304 (l : int) (r : int) (x : int) (h1 : term159 l r x) : term153 l x.
Proof. exact (proj1 (@lem5701301 l r x h1)). Qed.
Lemma lem5701306 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5701307 : term160 = term161.
Proof. exact (@lem5701306 term81 term75). Qed.
Lemma lem5701309 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5701310 : term75 = term108.
Proof. exact (@lem5701309 term76). Qed.
Lemma lem5701312 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5701313 : term81 = term162.
Proof. exact (@lem5701312 (NUMERAL 0)). Qed.
Lemma lem5701314 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5701315 : term163 = term164.
Proof. exact (MK_COMB (@lem5701314) (@lem5701313)). Qed.
Lemma lem5701316 : term161 = term165.
Proof. exact (MK_COMB (@lem5701315) (@lem5701310)). Qed.
Lemma lem5701317 : term166.
Proof. exact (@lem1980255 term81 term75 term75 term75). Qed.
Lemma lem5701319 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5701320 : term161 = term168.
Proof. exact (@lem5701319 (NUMERAL 0) term76). Qed.
Lemma lem5701321 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5701322 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5701323 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5701322 h1) (fun h1 : term168 = True => @lem5701321)). Qed.
Lemma lem5701324 : term168 = True.
Proof. exact (EQ_MP (@lem5701323) (@lem5701321)). Qed.
Lemma lem5701325 : term161 = True.
Proof. exact (TRANS (@lem5701320) (@lem5701324)). Qed.
Lemma lem5701326 : True = term161.
Proof. exact (SYM (@lem5701325)). Qed.
Lemma lem5701327 : term161.
Proof. exact (EQ_MP (@lem5701326) (@lem0)). Qed.
Lemma lem5701328 : term170.
Proof. exact (@lem5701317 (@lem5701327)). Qed.
Lemma lem5701330 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5701331 : term161 = term168.
Proof. exact (@lem5701330 (NUMERAL 0) term76). Qed.
Lemma lem5701332 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5701333 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5701334 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5701333 h1) (fun h1 : term168 = True => @lem5701332)). Qed.
Lemma lem5701335 : term168 = True.
Proof. exact (EQ_MP (@lem5701334) (@lem5701332)). Qed.
Lemma lem5701336 : term161 = True.
Proof. exact (TRANS (@lem5701331) (@lem5701335)). Qed.
Lemma lem5701337 : True = term161.
Proof. exact (SYM (@lem5701336)). Qed.
Lemma lem5701338 : term161.
Proof. exact (EQ_MP (@lem5701337) (@lem0)). Qed.
Lemma lem5701339 : term165 = term171.
Proof. exact (@lem5701328 (@lem5701338)). Qed.
Lemma lem5701341 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5701342 : term119 = term120.
Proof. exact (@lem5701341 term76 term76). Qed.
Lemma lem5701343 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5701344 : term122 = term76.
Proof. exact (EQ_MP (@lem5701343) (@lem940073)). Qed.
Lemma lem5701345 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5701346 : term120 = term75.
Proof. exact (MK_COMB (@lem5701345) (@lem5701344)). Qed.
Lemma lem5701347 : term119 = term75.
Proof. exact (TRANS (@lem5701342) (@lem5701346)). Qed.
Lemma lem5701349 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5701350 : term173 = term81.
Proof. exact (@lem5701349 term76). Qed.
Lemma lem5701351 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5701352 : term174 = term163.
Proof. exact (MK_COMB (@lem5701351) (@lem5701350)). Qed.
Lemma lem5701353 : term171 = term161.
Proof. exact (MK_COMB (@lem5701352) (@lem5701347)). Qed.
Lemma lem5701355 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5701356 : term161 = term168.
Proof. exact (@lem5701355 (NUMERAL 0) term76). Qed.
Lemma lem5701357 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5701358 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5701359 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5701358 h1) (fun h1 : term168 = True => @lem5701357)). Qed.
Lemma lem5701360 : term168 = True.
Proof. exact (EQ_MP (@lem5701359) (@lem5701357)). Qed.
Lemma lem5701361 : term161 = True.
Proof. exact (TRANS (@lem5701356) (@lem5701360)). Qed.
Lemma lem5701362 : term171 = True.
Proof. exact (TRANS (@lem5701353) (@lem5701361)). Qed.
Lemma lem5701363 : term165 = True.
Proof. exact (TRANS (@lem5701339) (@lem5701362)). Qed.
Lemma lem5701364 : term161 = True.
Proof. exact (TRANS (@lem5701316) (@lem5701363)). Qed.
Lemma lem5701365 : term160 = True.
Proof. exact (TRANS (@lem5701307) (@lem5701364)). Qed.
Lemma lem5701366 : True = term160.
Proof. exact (SYM (@lem5701365)). Qed.
Lemma lem5701367 : term160.
Proof. exact (EQ_MP (@lem5701366) (@lem0)). Qed.
Lemma lem5701368 (l : int) (r : int) (x : int) (h1 : term159 l r x) : term175 r x.
Proof. exact (conj (@lem5701367) (@lem5701303 l r x h1)). Qed.
Lemma lem5701370 (x : real) (y : real) : term176 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5701371 (r : int) (x : int) : term177 r x.
Proof. exact (@lem5701370 term75 (term91 r x)). Qed.
Lemma lem5701372 (l : int) (r : int) (x : int) (h1 : term159 l r x) : term178 r x.
Proof. exact (@lem5701371 r x (@lem5701368 l r x h1)). Qed.
Lemma lem5701373 (r : int) (x : int) : (term179 r x) = (term91 r x).
Proof. exact (@lem1982733 (term91 r x)). Qed.
Lemma lem5701374 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5701375 (r : int) (x : int) : (term180 r x) = (term154 r x).
Proof. exact (MK_COMB (@lem5701374) (@lem5701373 r x)). Qed.
Lemma lem5701376 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem5701377 (r : int) (x : int) : (term178 r x) = (term155 r x).
Proof. exact (MK_COMB (@lem5701375 r x) (@lem5701376)). Qed.
Lemma lem5701378 (l : int) (r : int) (x : int) (h1 : term159 l r x) : term155 r x.
Proof. exact (EQ_MP (@lem5701377 r x) (@lem5701372 l r x h1)). Qed.
Lemma lem5701380 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5701381 : term160 = term161.
Proof. exact (@lem5701380 term81 term75). Qed.
Lemma lem5701383 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5701384 : term75 = term108.
Proof. exact (@lem5701383 term76). Qed.
Lemma lem5701386 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5701387 : term81 = term162.
Proof. exact (@lem5701386 (NUMERAL 0)). Qed.
Lemma lem5701388 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5701389 : term163 = term164.
Proof. exact (MK_COMB (@lem5701388) (@lem5701387)). Qed.
Lemma lem5701390 : term161 = term165.
Proof. exact (MK_COMB (@lem5701389) (@lem5701384)). Qed.
Lemma lem5701391 : term166.
Proof. exact (@lem1980255 term81 term75 term75 term75). Qed.
Lemma lem5701393 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5701394 : term161 = term168.
Proof. exact (@lem5701393 (NUMERAL 0) term76). Qed.
Lemma lem5701395 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5701396 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5701397 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5701396 h1) (fun h1 : term168 = True => @lem5701395)). Qed.
Lemma lem5701398 : term168 = True.
Proof. exact (EQ_MP (@lem5701397) (@lem5701395)). Qed.
Lemma lem5701399 : term161 = True.
Proof. exact (TRANS (@lem5701394) (@lem5701398)). Qed.
Lemma lem5701400 : True = term161.
Proof. exact (SYM (@lem5701399)). Qed.
Lemma lem5701401 : term161.
Proof. exact (EQ_MP (@lem5701400) (@lem0)). Qed.
Lemma lem5701402 : term170.
Proof. exact (@lem5701391 (@lem5701401)). Qed.
Lemma lem5701404 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5701405 : term161 = term168.
Proof. exact (@lem5701404 (NUMERAL 0) term76). Qed.
Lemma lem5701406 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5701407 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5701408 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5701407 h1) (fun h1 : term168 = True => @lem5701406)). Qed.
Lemma lem5701409 : term168 = True.
Proof. exact (EQ_MP (@lem5701408) (@lem5701406)). Qed.
Lemma lem5701410 : term161 = True.
Proof. exact (TRANS (@lem5701405) (@lem5701409)). Qed.
Lemma lem5701411 : True = term161.
Proof. exact (SYM (@lem5701410)). Qed.
Lemma lem5701412 : term161.
Proof. exact (EQ_MP (@lem5701411) (@lem0)). Qed.
Lemma lem5701413 : term165 = term171.
Proof. exact (@lem5701402 (@lem5701412)). Qed.
Lemma lem5701415 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5701416 : term119 = term120.
Proof. exact (@lem5701415 term76 term76). Qed.
Lemma lem5701417 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5701418 : term122 = term76.
Proof. exact (EQ_MP (@lem5701417) (@lem940073)). Qed.
Lemma lem5701419 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5701420 : term120 = term75.
Proof. exact (MK_COMB (@lem5701419) (@lem5701418)). Qed.
Lemma lem5701421 : term119 = term75.
Proof. exact (TRANS (@lem5701416) (@lem5701420)). Qed.
Lemma lem5701423 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5701424 : term173 = term81.
Proof. exact (@lem5701423 term76). Qed.
Lemma lem5701425 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5701426 : term174 = term163.
Proof. exact (MK_COMB (@lem5701425) (@lem5701424)). Qed.
Lemma lem5701427 : term171 = term161.
Proof. exact (MK_COMB (@lem5701426) (@lem5701421)). Qed.
Lemma lem5701429 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5701430 : term161 = term168.
Proof. exact (@lem5701429 (NUMERAL 0) term76). Qed.
Lemma lem5701431 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5701432 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5701433 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5701432 h1) (fun h1 : term168 = True => @lem5701431)). Qed.
Lemma lem5701434 : term168 = True.
Proof. exact (EQ_MP (@lem5701433) (@lem5701431)). Qed.
Lemma lem5701435 : term161 = True.
Proof. exact (TRANS (@lem5701430) (@lem5701434)). Qed.
Lemma lem5701436 : term171 = True.
Proof. exact (TRANS (@lem5701427) (@lem5701435)). Qed.
Lemma lem5701437 : term165 = True.
Proof. exact (TRANS (@lem5701413) (@lem5701436)). Qed.
Lemma lem5701438 : term161 = True.
Proof. exact (TRANS (@lem5701390) (@lem5701437)). Qed.
Lemma lem5701439 : term160 = True.
Proof. exact (TRANS (@lem5701381) (@lem5701438)). Qed.
Lemma lem5701440 : True = term160.
Proof. exact (SYM (@lem5701439)). Qed.
Lemma lem5701441 : term160.
Proof. exact (EQ_MP (@lem5701440) (@lem0)). Qed.
Lemma lem5701442 (l : int) (r : int) (x : int) (h1 : term159 l r x) : term181 l r.
Proof. exact (conj (@lem5701441) (@lem5701302 l r x h1)). Qed.
Lemma lem5701444 (x : real) (y : real) : term176 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5701445 (l : int) (r : int) : term182 l r.
Proof. exact (@lem5701444 term75 (term144 l r)). Qed.
Lemma lem5701446 (l : int) (r : int) (x : int) (h1 : term159 l r x) : term183 l r.
Proof. exact (@lem5701445 l r (@lem5701442 l r x h1)). Qed.
Lemma lem5701447 (l : int) (r : int) : (term184 l r) = (term144 l r).
Proof. exact (@lem1982733 (term144 l r)). Qed.
Lemma lem5701448 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5701449 (l : int) (r : int) : (term185 l r) = (term148 l r).
Proof. exact (MK_COMB (@lem5701448) (@lem5701447 l r)). Qed.
Lemma lem5701450 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem5701451 (l : int) (r : int) : (term183 l r) = (term149 l r).
Proof. exact (MK_COMB (@lem5701449 l r) (@lem5701450)). Qed.
Lemma lem5701452 (l : int) (r : int) (x : int) (h1 : term159 l r x) : term149 l r.
Proof. exact (EQ_MP (@lem5701451 l r) (@lem5701446 l r x h1)). Qed.
Lemma lem5701453 (l : int) (r : int) (x : int) (h1 : term159 l r x) : term186 l r x.
Proof. exact (conj (@lem5701452 l r x h1) (@lem5701378 l r x h1)). Qed.
Lemma lem5701455 (x : real) (y : real) : term187 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5701456 (l : int) (r : int) (x : int) : term188 l r x.
Proof. exact (@lem5701455 (term144 l r) (term91 r x)). Qed.
Lemma lem5701457 (l : int) (r : int) (x : int) (h1 : term159 l r x) : term189 l r x.
Proof. exact (@lem5701456 l r x (@lem5701453 l r x h1)). Qed.
Lemma lem5701458 (l : int) (r : int) (x : int) : (term190 l r x) = (term191 l r x).
Proof. exact (@lem1982755 (real_of_int l) (term130 r) (term91 r x)). Qed.
Lemma lem5701459 (r : int) (x : int) : (term192 r x) = (term193 r x).
Proof. exact (@lem1982753 (term93 r) (real_of_int r) term103 (term93 x)). Qed.
Lemma lem5701460 (r : int) : (term194 r) = (term195 r).
Proof. exact (@lem1982713 term103 (real_of_int r)). Qed.
Lemma lem5701462 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5701463 : term75 = term108.
Proof. exact (@lem5701462 term76). Qed.
Lemma lem5701465 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5701466 : term103 = term111.
Proof. exact (@lem5701465 term76). Qed.
Lemma lem5701467 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5701468 : term196 = term197.
Proof. exact (MK_COMB (@lem5701467) (@lem5701466)). Qed.
Lemma lem5701469 : term198 = term199.
Proof. exact (MK_COMB (@lem5701468) (@lem5701463)). Qed.
Lemma lem5701470 : term200.
Proof. exact (@lem1981473 term103 term75 term75 term75 term81 term75). Qed.
Lemma lem5701472 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5701473 : term161 = term168.
Proof. exact (@lem5701472 (NUMERAL 0) term76). Qed.
Lemma lem5701474 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5701475 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5701476 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5701475 h1) (fun h1 : term168 = True => @lem5701474)). Qed.
Lemma lem5701477 : term168 = True.
Proof. exact (EQ_MP (@lem5701476) (@lem5701474)). Qed.
Lemma lem5701478 : term161 = True.
Proof. exact (TRANS (@lem5701473) (@lem5701477)). Qed.
Lemma lem5701479 : True = term161.
Proof. exact (SYM (@lem5701478)). Qed.
Lemma lem5701480 : term161.
Proof. exact (EQ_MP (@lem5701479) (@lem0)). Qed.
Lemma lem5701481 : term201.
Proof. exact (@lem5701470 (@lem5701480)). Qed.
Lemma lem5701483 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5701484 : term161 = term168.
Proof. exact (@lem5701483 (NUMERAL 0) term76). Qed.
Lemma lem5701485 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5701486 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5701487 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5701486 h1) (fun h1 : term168 = True => @lem5701485)). Qed.
Lemma lem5701488 : term168 = True.
Proof. exact (EQ_MP (@lem5701487) (@lem5701485)). Qed.
Lemma lem5701489 : term161 = True.
Proof. exact (TRANS (@lem5701484) (@lem5701488)). Qed.
Lemma lem5701490 : True = term161.
Proof. exact (SYM (@lem5701489)). Qed.
Lemma lem5701491 : term161.
Proof. exact (EQ_MP (@lem5701490) (@lem0)). Qed.
Lemma lem5701492 : term202.
Proof. exact (@lem5701481 (@lem5701491)). Qed.
Lemma lem5701494 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5701495 : term161 = term168.
Proof. exact (@lem5701494 (NUMERAL 0) term76). Qed.
Lemma lem5701496 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5701497 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5701498 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5701497 h1) (fun h1 : term168 = True => @lem5701496)). Qed.
Lemma lem5701499 : term168 = True.
Proof. exact (EQ_MP (@lem5701498) (@lem5701496)). Qed.
Lemma lem5701500 : term161 = True.
Proof. exact (TRANS (@lem5701495) (@lem5701499)). Qed.
Lemma lem5701501 : True = term161.
Proof. exact (SYM (@lem5701500)). Qed.
Lemma lem5701502 : term161.
Proof. exact (EQ_MP (@lem5701501) (@lem0)). Qed.
Lemma lem5701503 : term203.
Proof. exact (@lem5701492 (@lem5701502)). Qed.
Lemma lem5701505 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5701506 : term119 = term120.
Proof. exact (@lem5701505 term76 term76). Qed.
Lemma lem5701507 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5701508 : term122 = term76.
Proof. exact (EQ_MP (@lem5701507) (@lem940073)). Qed.
Lemma lem5701509 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5701510 : term120 = term75.
Proof. exact (MK_COMB (@lem5701509) (@lem5701508)). Qed.
Lemma lem5701511 : term119 = term75.
Proof. exact (TRANS (@lem5701506) (@lem5701510)). Qed.
Lemma lem5701513 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5701514 : term114 = term125.
Proof. exact (@lem5701513 term76 term76). Qed.
Lemma lem5701515 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5701516 : term122 = term76.
Proof. exact (EQ_MP (@lem5701515) (@lem940073)). Qed.
Lemma lem5701517 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5701518 : term120 = term75.
Proof. exact (MK_COMB (@lem5701517) (@lem5701516)). Qed.
Lemma lem5701519 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5701520 : term125 = term103.
Proof. exact (MK_COMB (@lem5701519) (@lem5701518)). Qed.
Lemma lem5701521 : term114 = term103.
Proof. exact (TRANS (@lem5701514) (@lem5701520)). Qed.
Lemma lem5701522 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5701523 : term204 = term196.
Proof. exact (MK_COMB (@lem5701522) (@lem5701521)). Qed.
Lemma lem5701524 : term205 = term198.
Proof. exact (MK_COMB (@lem5701523) (@lem5701511)). Qed.
Lemma lem5701526 (m : nat) : (term206 m) = term81.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5701527 : term198 = term81.
Proof. exact (@lem5701526 term76). Qed.
Lemma lem5701528 : term205 = term81.
Proof. exact (TRANS (@lem5701524) (@lem5701527)). Qed.
Lemma lem5701529 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5701530 : term207 = term208.
Proof. exact (MK_COMB (@lem5701529) (@lem5701528)). Qed.
Lemma lem5701531 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem5701532 : term209 = term173.
Proof. exact (MK_COMB (@lem5701530) (@lem5701531)). Qed.
Lemma lem5701534 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5701535 : term173 = term81.
Proof. exact (@lem5701534 term76). Qed.
Lemma lem5701536 : term209 = term81.
Proof. exact (TRANS (@lem5701532) (@lem5701535)). Qed.
Lemma lem5701538 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5701539 : term119 = term120.
Proof. exact (@lem5701538 term76 term76). Qed.
Lemma lem5701540 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5701541 : term122 = term76.
Proof. exact (EQ_MP (@lem5701540) (@lem940073)). Qed.
Lemma lem5701542 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5701543 : term120 = term75.
Proof. exact (MK_COMB (@lem5701542) (@lem5701541)). Qed.
Lemma lem5701544 : term119 = term75.
Proof. exact (TRANS (@lem5701539) (@lem5701543)). Qed.
Lemma lem5701545 : term208 = term208.
Proof. exact (eq_refl term208). Qed.
Lemma lem5701546 : term210 = term173.
Proof. exact (MK_COMB (@lem5701545) (@lem5701544)). Qed.
Lemma lem5701548 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5701549 : term173 = term81.
Proof. exact (@lem5701548 term76). Qed.
Lemma lem5701550 : term210 = term81.
Proof. exact (TRANS (@lem5701546) (@lem5701549)). Qed.
Lemma lem5701551 : term81 = term210.
Proof. exact (SYM (@lem5701550)). Qed.
Lemma lem5701552 : term209 = term210.
Proof. exact (TRANS (@lem5701536) (@lem5701551)). Qed.
Lemma lem5701553 : term199 = term162.
Proof. exact (@lem5701503 (@lem5701552)). Qed.
Lemma lem5701554 : term198 = term162.
Proof. exact (TRANS (@lem5701469) (@lem5701553)). Qed.
Lemma lem5701556 (x : real) : (term128 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5701557 : term162 = term81.
Proof. exact (@lem5701556 term81). Qed.
Lemma lem5701558 : term198 = term81.
Proof. exact (TRANS (@lem5701554) (@lem5701557)). Qed.
Lemma lem5701559 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5701560 : term211 = term208.
Proof. exact (MK_COMB (@lem5701559) (@lem5701558)). Qed.
Lemma lem5701561 (r : int) : (real_of_int r) = (real_of_int r).
Proof. exact (eq_refl (real_of_int r)). Qed.
Lemma lem5701562 (r : int) : (term195 r) = (term212 r).
Proof. exact (MK_COMB (@lem5701560) (@lem5701561 r)). Qed.
Lemma lem5701563 (r : int) : (term194 r) = (term212 r).
Proof. exact (TRANS (@lem5701460 r) (@lem5701562 r)). Qed.
Lemma lem5701564 (r : int) : (term212 r) = term81.
Proof. exact (@lem1982719 (real_of_int r)). Qed.
Lemma lem5701565 (r : int) : (term194 r) = term81.
Proof. exact (TRANS (@lem5701563 r) (@lem5701564 r)). Qed.
Lemma lem5701566 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5701567 (r : int) : (term213 r) = term145.
Proof. exact (MK_COMB (@lem5701566) (@lem5701565 r)). Qed.
Lemma lem5701568 (x : int) : (term214 x) = (term130 x).
Proof. exact (@lem1982761 (term93 x) term103). Qed.
Lemma lem5701569 (r : int) (x : int) : (term193 r x) = (term215 x).
Proof. exact (MK_COMB (@lem5701567 r) (@lem5701568 x)). Qed.
Lemma lem5701570 (r : int) (x : int) : (term192 r x) = (term215 x).
Proof. exact (TRANS (@lem5701459 r x) (@lem5701569 r x)). Qed.
Lemma lem5701571 (x : int) : (term215 x) = (term130 x).
Proof. exact (@lem1982721 (term130 x)). Qed.
Lemma lem5701572 (r : int) (x : int) : (term192 r x) = (term130 x).
Proof. exact (TRANS (@lem5701570 r x) (@lem5701571 x)). Qed.
Lemma lem5701573 (l : int) : (term143 l) = (term143 l).
Proof. exact (eq_refl (term143 l)). Qed.
Lemma lem5701574 (r : int) (l : int) (x : int) : (term191 l r x) = (term144 l x).
Proof. exact (MK_COMB (@lem5701573 l) (@lem5701572 r x)). Qed.
Lemma lem5701575 (r : int) (l : int) (x : int) : (term190 l r x) = (term144 l x).
Proof. exact (TRANS (@lem5701458 l r x) (@lem5701574 r l x)). Qed.
Lemma lem5701576 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5701577 (r : int) (l : int) (x : int) : (term216 l r x) = (term148 l x).
Proof. exact (MK_COMB (@lem5701576) (@lem5701575 r l x)). Qed.
Lemma lem5701578 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem5701579 (r : int) (l : int) (x : int) : (term189 l r x) = (term149 l x).
Proof. exact (MK_COMB (@lem5701577 r l x) (@lem5701578)). Qed.
Lemma lem5701580 (l : int) (r : int) (x : int) (h1 : term159 l r x) : term149 l x.
Proof. exact (EQ_MP (@lem5701579 r l x) (@lem5701457 l r x h1)). Qed.
Lemma lem5701582 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5701583 : term160 = term161.
Proof. exact (@lem5701582 term81 term75). Qed.
Lemma lem5701585 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5701586 : term75 = term108.
Proof. exact (@lem5701585 term76). Qed.
Lemma lem5701588 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5701589 : term81 = term162.
Proof. exact (@lem5701588 (NUMERAL 0)). Qed.
Lemma lem5701590 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5701591 : term163 = term164.
Proof. exact (MK_COMB (@lem5701590) (@lem5701589)). Qed.
Lemma lem5701592 : term161 = term165.
Proof. exact (MK_COMB (@lem5701591) (@lem5701586)). Qed.
Lemma lem5701593 : term166.
Proof. exact (@lem1980255 term81 term75 term75 term75). Qed.
Lemma lem5701595 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5701596 : term161 = term168.
Proof. exact (@lem5701595 (NUMERAL 0) term76). Qed.
Lemma lem5701597 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5701598 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5701599 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5701598 h1) (fun h1 : term168 = True => @lem5701597)). Qed.
Lemma lem5701600 : term168 = True.
Proof. exact (EQ_MP (@lem5701599) (@lem5701597)). Qed.
Lemma lem5701601 : term161 = True.
Proof. exact (TRANS (@lem5701596) (@lem5701600)). Qed.
Lemma lem5701602 : True = term161.
Proof. exact (SYM (@lem5701601)). Qed.
Lemma lem5701603 : term161.
Proof. exact (EQ_MP (@lem5701602) (@lem0)). Qed.
Lemma lem5701604 : term170.
Proof. exact (@lem5701593 (@lem5701603)). Qed.
Lemma lem5701606 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5701607 : term161 = term168.
Proof. exact (@lem5701606 (NUMERAL 0) term76). Qed.
Lemma lem5701608 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5701609 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5701610 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5701609 h1) (fun h1 : term168 = True => @lem5701608)). Qed.
Lemma lem5701611 : term168 = True.
Proof. exact (EQ_MP (@lem5701610) (@lem5701608)). Qed.
Lemma lem5701612 : term161 = True.
Proof. exact (TRANS (@lem5701607) (@lem5701611)). Qed.
Lemma lem5701613 : True = term161.
Proof. exact (SYM (@lem5701612)). Qed.
Lemma lem5701614 : term161.
Proof. exact (EQ_MP (@lem5701613) (@lem0)). Qed.
Lemma lem5701615 : term165 = term171.
Proof. exact (@lem5701604 (@lem5701614)). Qed.
Lemma lem5701617 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5701618 : term119 = term120.
Proof. exact (@lem5701617 term76 term76). Qed.
Lemma lem5701619 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5701620 : term122 = term76.
Proof. exact (EQ_MP (@lem5701619) (@lem940073)). Qed.
Lemma lem5701621 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5701622 : term120 = term75.
Proof. exact (MK_COMB (@lem5701621) (@lem5701620)). Qed.
Lemma lem5701623 : term119 = term75.
Proof. exact (TRANS (@lem5701618) (@lem5701622)). Qed.
Lemma lem5701625 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5701626 : term173 = term81.
Proof. exact (@lem5701625 term76). Qed.
Lemma lem5701627 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5701628 : term174 = term163.
Proof. exact (MK_COMB (@lem5701627) (@lem5701626)). Qed.
Lemma lem5701629 : term171 = term161.
Proof. exact (MK_COMB (@lem5701628) (@lem5701623)). Qed.
Lemma lem5701631 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5701632 : term161 = term168.
Proof. exact (@lem5701631 (NUMERAL 0) term76). Qed.
Lemma lem5701633 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5701634 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5701635 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5701634 h1) (fun h1 : term168 = True => @lem5701633)). Qed.
Lemma lem5701636 : term168 = True.
Proof. exact (EQ_MP (@lem5701635) (@lem5701633)). Qed.
Lemma lem5701637 : term161 = True.
Proof. exact (TRANS (@lem5701632) (@lem5701636)). Qed.
Lemma lem5701638 : term171 = True.
Proof. exact (TRANS (@lem5701629) (@lem5701637)). Qed.
Lemma lem5701639 : term165 = True.
Proof. exact (TRANS (@lem5701615) (@lem5701638)). Qed.
Lemma lem5701640 : term161 = True.
Proof. exact (TRANS (@lem5701592) (@lem5701639)). Qed.
Lemma lem5701641 : term160 = True.
Proof. exact (TRANS (@lem5701583) (@lem5701640)). Qed.
Lemma lem5701642 : True = term160.
Proof. exact (SYM (@lem5701641)). Qed.
Lemma lem5701643 : term160.
Proof. exact (EQ_MP (@lem5701642) (@lem0)). Qed.
Lemma lem5701644 (l : int) (r : int) (x : int) (h1 : term159 l r x) : term181 l x.
Proof. exact (conj (@lem5701643) (@lem5701580 l r x h1)). Qed.
Lemma lem5701646 (x : real) (y : real) : term176 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5701647 (l : int) (x : int) : term182 l x.
Proof. exact (@lem5701646 term75 (term144 l x)). Qed.
Lemma lem5701648 (l : int) (r : int) (x : int) (h1 : term159 l r x) : term183 l x.
Proof. exact (@lem5701647 l x (@lem5701644 l r x h1)). Qed.
Lemma lem5701649 (l : int) (x : int) : (term184 l x) = (term144 l x).
Proof. exact (@lem1982733 (term144 l x)). Qed.
Lemma lem5701650 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5701651 (l : int) (x : int) : (term185 l x) = (term148 l x).
Proof. exact (MK_COMB (@lem5701650) (@lem5701649 l x)). Qed.
Lemma lem5701652 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem5701653 (l : int) (x : int) : (term183 l x) = (term149 l x).
Proof. exact (MK_COMB (@lem5701651 l x) (@lem5701652)). Qed.
Lemma lem5701654 (l : int) (r : int) (x : int) (h1 : term159 l r x) : term149 l x.
Proof. exact (EQ_MP (@lem5701653 l x) (@lem5701648 l r x h1)). Qed.
Lemma lem5701656 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5701657 : term160 = term161.
Proof. exact (@lem5701656 term81 term75). Qed.
Lemma lem5701659 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5701660 : term75 = term108.
Proof. exact (@lem5701659 term76). Qed.
Lemma lem5701662 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5701663 : term81 = term162.
Proof. exact (@lem5701662 (NUMERAL 0)). Qed.
Lemma lem5701664 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5701665 : term163 = term164.
Proof. exact (MK_COMB (@lem5701664) (@lem5701663)). Qed.
Lemma lem5701666 : term161 = term165.
Proof. exact (MK_COMB (@lem5701665) (@lem5701660)). Qed.
Lemma lem5701667 : term166.
Proof. exact (@lem1980255 term81 term75 term75 term75). Qed.
Lemma lem5701669 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5701670 : term161 = term168.
Proof. exact (@lem5701669 (NUMERAL 0) term76). Qed.
Lemma lem5701671 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5701672 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5701673 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5701672 h1) (fun h1 : term168 = True => @lem5701671)). Qed.
Lemma lem5701674 : term168 = True.
Proof. exact (EQ_MP (@lem5701673) (@lem5701671)). Qed.
Lemma lem5701675 : term161 = True.
Proof. exact (TRANS (@lem5701670) (@lem5701674)). Qed.
Lemma lem5701676 : True = term161.
Proof. exact (SYM (@lem5701675)). Qed.
Lemma lem5701677 : term161.
Proof. exact (EQ_MP (@lem5701676) (@lem0)). Qed.
Lemma lem5701678 : term170.
Proof. exact (@lem5701667 (@lem5701677)). Qed.
Lemma lem5701680 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5701681 : term161 = term168.
Proof. exact (@lem5701680 (NUMERAL 0) term76). Qed.
Lemma lem5701682 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5701683 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5701684 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5701683 h1) (fun h1 : term168 = True => @lem5701682)). Qed.
Lemma lem5701685 : term168 = True.
Proof. exact (EQ_MP (@lem5701684) (@lem5701682)). Qed.
Lemma lem5701686 : term161 = True.
Proof. exact (TRANS (@lem5701681) (@lem5701685)). Qed.
Lemma lem5701687 : True = term161.
Proof. exact (SYM (@lem5701686)). Qed.
Lemma lem5701688 : term161.
Proof. exact (EQ_MP (@lem5701687) (@lem0)). Qed.
Lemma lem5701689 : term165 = term171.
Proof. exact (@lem5701678 (@lem5701688)). Qed.
Lemma lem5701691 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5701692 : term119 = term120.
Proof. exact (@lem5701691 term76 term76). Qed.
Lemma lem5701693 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5701694 : term122 = term76.
Proof. exact (EQ_MP (@lem5701693) (@lem940073)). Qed.
Lemma lem5701695 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5701696 : term120 = term75.
Proof. exact (MK_COMB (@lem5701695) (@lem5701694)). Qed.
Lemma lem5701697 : term119 = term75.
Proof. exact (TRANS (@lem5701692) (@lem5701696)). Qed.
Lemma lem5701699 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5701700 : term173 = term81.
Proof. exact (@lem5701699 term76). Qed.
Lemma lem5701701 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5701702 : term174 = term163.
Proof. exact (MK_COMB (@lem5701701) (@lem5701700)). Qed.
Lemma lem5701703 : term171 = term161.
Proof. exact (MK_COMB (@lem5701702) (@lem5701697)). Qed.
Lemma lem5701705 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5701706 : term161 = term168.
Proof. exact (@lem5701705 (NUMERAL 0) term76). Qed.
Lemma lem5701707 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5701708 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5701709 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5701708 h1) (fun h1 : term168 = True => @lem5701707)). Qed.
Lemma lem5701710 : term168 = True.
Proof. exact (EQ_MP (@lem5701709) (@lem5701707)). Qed.
Lemma lem5701711 : term161 = True.
Proof. exact (TRANS (@lem5701706) (@lem5701710)). Qed.
Lemma lem5701712 : term171 = True.
Proof. exact (TRANS (@lem5701703) (@lem5701711)). Qed.
Lemma lem5701713 : term165 = True.
Proof. exact (TRANS (@lem5701689) (@lem5701712)). Qed.
Lemma lem5701714 : term161 = True.
Proof. exact (TRANS (@lem5701666) (@lem5701713)). Qed.
Lemma lem5701715 : term160 = True.
Proof. exact (TRANS (@lem5701657) (@lem5701714)). Qed.
Lemma lem5701716 : True = term160.
Proof. exact (SYM (@lem5701715)). Qed.
Lemma lem5701717 : term160.
Proof. exact (EQ_MP (@lem5701716) (@lem0)). Qed.
Lemma lem5701718 (l : int) (r : int) (x : int) (h1 : term159 l r x) : term217 l x.
Proof. exact (conj (@lem5701717) (@lem5701304 l r x h1)). Qed.
Lemma lem5701720 (x : real) (y : real) : term176 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5701721 (l : int) (x : int) : term218 l x.
Proof. exact (@lem5701720 term75 (term92 l x)). Qed.
Lemma lem5701722 (l : int) (r : int) (x : int) (h1 : term159 l r x) : term219 l x.
Proof. exact (@lem5701721 l x (@lem5701718 l r x h1)). Qed.
Lemma lem5701723 (l : int) (x : int) : (term220 l x) = (term92 l x).
Proof. exact (@lem1982733 (term92 l x)). Qed.
Lemma lem5701724 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5701725 (l : int) (x : int) : (term221 l x) = (term152 l x).
Proof. exact (MK_COMB (@lem5701724) (@lem5701723 l x)). Qed.
Lemma lem5701726 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem5701727 (l : int) (x : int) : (term219 l x) = (term153 l x).
Proof. exact (MK_COMB (@lem5701725 l x) (@lem5701726)). Qed.
Lemma lem5701728 (l : int) (r : int) (x : int) (h1 : term159 l r x) : term153 l x.
Proof. exact (EQ_MP (@lem5701727 l x) (@lem5701722 l r x h1)). Qed.
Lemma lem5701729 (l : int) (r : int) (x : int) (h1 : term159 l r x) : term222 l x.
Proof. exact (conj (@lem5701728 l r x h1) (@lem5701654 l r x h1)). Qed.
Lemma lem5701731 (x : real) (y : real) : term187 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5701732 (l : int) (x : int) : term223 l x.
Proof. exact (@lem5701731 (term92 l x) (term144 l x)). Qed.
Lemma lem5701733 (l : int) (r : int) (x : int) (h1 : term159 l r x) : term224 l x.
Proof. exact (@lem5701732 l x (@lem5701729 l r x h1)). Qed.
Lemma lem5701734 (l : int) (x : int) : (term225 l x) = (term226 l x).
Proof. exact (@lem1982753 (term93 l) (real_of_int l) (real_of_int x) (term130 x)). Qed.
Lemma lem5701735 (l : int) : (term194 l) = (term195 l).
Proof. exact (@lem1982713 term103 (real_of_int l)). Qed.
Lemma lem5701737 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5701738 : term75 = term108.
Proof. exact (@lem5701737 term76). Qed.
Lemma lem5701740 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5701741 : term103 = term111.
Proof. exact (@lem5701740 term76). Qed.
Lemma lem5701742 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5701743 : term196 = term197.
Proof. exact (MK_COMB (@lem5701742) (@lem5701741)). Qed.
Lemma lem5701744 : term198 = term199.
Proof. exact (MK_COMB (@lem5701743) (@lem5701738)). Qed.
Lemma lem5701745 : term200.
Proof. exact (@lem1981473 term103 term75 term75 term75 term81 term75). Qed.
Lemma lem5701747 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5701748 : term161 = term168.
Proof. exact (@lem5701747 (NUMERAL 0) term76). Qed.
Lemma lem5701749 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5701750 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5701751 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5701750 h1) (fun h1 : term168 = True => @lem5701749)). Qed.
Lemma lem5701752 : term168 = True.
Proof. exact (EQ_MP (@lem5701751) (@lem5701749)). Qed.
Lemma lem5701753 : term161 = True.
Proof. exact (TRANS (@lem5701748) (@lem5701752)). Qed.
Lemma lem5701754 : True = term161.
Proof. exact (SYM (@lem5701753)). Qed.
Lemma lem5701755 : term161.
Proof. exact (EQ_MP (@lem5701754) (@lem0)). Qed.
Lemma lem5701756 : term201.
Proof. exact (@lem5701745 (@lem5701755)). Qed.
Lemma lem5701758 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5701759 : term161 = term168.
Proof. exact (@lem5701758 (NUMERAL 0) term76). Qed.
Lemma lem5701760 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5701761 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5701762 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5701761 h1) (fun h1 : term168 = True => @lem5701760)). Qed.
Lemma lem5701763 : term168 = True.
Proof. exact (EQ_MP (@lem5701762) (@lem5701760)). Qed.
Lemma lem5701764 : term161 = True.
Proof. exact (TRANS (@lem5701759) (@lem5701763)). Qed.
Lemma lem5701765 : True = term161.
Proof. exact (SYM (@lem5701764)). Qed.
Lemma lem5701766 : term161.
Proof. exact (EQ_MP (@lem5701765) (@lem0)). Qed.
Lemma lem5701767 : term202.
Proof. exact (@lem5701756 (@lem5701766)). Qed.
Lemma lem5701769 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5701770 : term161 = term168.
Proof. exact (@lem5701769 (NUMERAL 0) term76). Qed.
Lemma lem5701771 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5701772 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5701773 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5701772 h1) (fun h1 : term168 = True => @lem5701771)). Qed.
Lemma lem5701774 : term168 = True.
Proof. exact (EQ_MP (@lem5701773) (@lem5701771)). Qed.
Lemma lem5701775 : term161 = True.
Proof. exact (TRANS (@lem5701770) (@lem5701774)). Qed.
Lemma lem5701776 : True = term161.
Proof. exact (SYM (@lem5701775)). Qed.
Lemma lem5701777 : term161.
Proof. exact (EQ_MP (@lem5701776) (@lem0)). Qed.
Lemma lem5701778 : term203.
Proof. exact (@lem5701767 (@lem5701777)). Qed.
Lemma lem5701780 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5701781 : term119 = term120.
Proof. exact (@lem5701780 term76 term76). Qed.
Lemma lem5701782 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5701783 : term122 = term76.
Proof. exact (EQ_MP (@lem5701782) (@lem940073)). Qed.
Lemma lem5701784 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5701785 : term120 = term75.
Proof. exact (MK_COMB (@lem5701784) (@lem5701783)). Qed.
Lemma lem5701786 : term119 = term75.
Proof. exact (TRANS (@lem5701781) (@lem5701785)). Qed.
Lemma lem5701788 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5701789 : term114 = term125.
Proof. exact (@lem5701788 term76 term76). Qed.
Lemma lem5701790 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5701791 : term122 = term76.
Proof. exact (EQ_MP (@lem5701790) (@lem940073)). Qed.
Lemma lem5701792 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5701793 : term120 = term75.
Proof. exact (MK_COMB (@lem5701792) (@lem5701791)). Qed.
Lemma lem5701794 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5701795 : term125 = term103.
Proof. exact (MK_COMB (@lem5701794) (@lem5701793)). Qed.
Lemma lem5701796 : term114 = term103.
Proof. exact (TRANS (@lem5701789) (@lem5701795)). Qed.
Lemma lem5701797 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5701798 : term204 = term196.
Proof. exact (MK_COMB (@lem5701797) (@lem5701796)). Qed.
Lemma lem5701799 : term205 = term198.
Proof. exact (MK_COMB (@lem5701798) (@lem5701786)). Qed.
Lemma lem5701801 (m : nat) : (term206 m) = term81.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5701802 : term198 = term81.
Proof. exact (@lem5701801 term76). Qed.
Lemma lem5701803 : term205 = term81.
Proof. exact (TRANS (@lem5701799) (@lem5701802)). Qed.
Lemma lem5701804 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5701805 : term207 = term208.
Proof. exact (MK_COMB (@lem5701804) (@lem5701803)). Qed.
Lemma lem5701806 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem5701807 : term209 = term173.
Proof. exact (MK_COMB (@lem5701805) (@lem5701806)). Qed.
Lemma lem5701809 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5701810 : term173 = term81.
Proof. exact (@lem5701809 term76). Qed.
Lemma lem5701811 : term209 = term81.
Proof. exact (TRANS (@lem5701807) (@lem5701810)). Qed.
Lemma lem5701813 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5701814 : term119 = term120.
Proof. exact (@lem5701813 term76 term76). Qed.
Lemma lem5701815 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5701816 : term122 = term76.
Proof. exact (EQ_MP (@lem5701815) (@lem940073)). Qed.
Lemma lem5701817 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5701818 : term120 = term75.
Proof. exact (MK_COMB (@lem5701817) (@lem5701816)). Qed.
Lemma lem5701819 : term119 = term75.
Proof. exact (TRANS (@lem5701814) (@lem5701818)). Qed.
Lemma lem5701820 : term208 = term208.
Proof. exact (eq_refl term208). Qed.
Lemma lem5701821 : term210 = term173.
Proof. exact (MK_COMB (@lem5701820) (@lem5701819)). Qed.
Lemma lem5701823 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5701824 : term173 = term81.
Proof. exact (@lem5701823 term76). Qed.
Lemma lem5701825 : term210 = term81.
Proof. exact (TRANS (@lem5701821) (@lem5701824)). Qed.
Lemma lem5701826 : term81 = term210.
Proof. exact (SYM (@lem5701825)). Qed.
Lemma lem5701827 : term209 = term210.
Proof. exact (TRANS (@lem5701811) (@lem5701826)). Qed.
Lemma lem5701828 : term199 = term162.
Proof. exact (@lem5701778 (@lem5701827)). Qed.
Lemma lem5701829 : term198 = term162.
Proof. exact (TRANS (@lem5701744) (@lem5701828)). Qed.
Lemma lem5701831 (x : real) : (term128 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5701832 : term162 = term81.
Proof. exact (@lem5701831 term81). Qed.
Lemma lem5701833 : term198 = term81.
Proof. exact (TRANS (@lem5701829) (@lem5701832)). Qed.
Lemma lem5701834 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5701835 : term211 = term208.
Proof. exact (MK_COMB (@lem5701834) (@lem5701833)). Qed.
Lemma lem5701836 (l : int) : (real_of_int l) = (real_of_int l).
Proof. exact (eq_refl (real_of_int l)). Qed.
Lemma lem5701837 (l : int) : (term195 l) = (term212 l).
Proof. exact (MK_COMB (@lem5701835) (@lem5701836 l)). Qed.
Lemma lem5701838 (l : int) : (term194 l) = (term212 l).
Proof. exact (TRANS (@lem5701735 l) (@lem5701837 l)). Qed.
Lemma lem5701839 (l : int) : (term212 l) = term81.
Proof. exact (@lem1982719 (real_of_int l)). Qed.
Lemma lem5701840 (l : int) : (term194 l) = term81.
Proof. exact (TRANS (@lem5701838 l) (@lem5701839 l)). Qed.
Lemma lem5701841 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5701842 (l : int) : (term213 l) = term145.
Proof. exact (MK_COMB (@lem5701841) (@lem5701840 l)). Qed.
Lemma lem5701843 (x : int) : (term227 x) = (term228 x).
Proof. exact (@lem1982763 (real_of_int x) (term93 x) term103). Qed.
Lemma lem5701844 (x : int) : (term229 x) = (term195 x).
Proof. exact (@lem1982715 term103 (real_of_int x)). Qed.
Lemma lem5701846 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5701847 : term75 = term108.
Proof. exact (@lem5701846 term76). Qed.
Lemma lem5701849 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5701850 : term103 = term111.
Proof. exact (@lem5701849 term76). Qed.
Lemma lem5701851 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5701852 : term196 = term197.
Proof. exact (MK_COMB (@lem5701851) (@lem5701850)). Qed.
Lemma lem5701853 : term198 = term199.
Proof. exact (MK_COMB (@lem5701852) (@lem5701847)). Qed.
Lemma lem5701854 : term200.
Proof. exact (@lem1981473 term103 term75 term75 term75 term81 term75). Qed.
Lemma lem5701856 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5701857 : term161 = term168.
Proof. exact (@lem5701856 (NUMERAL 0) term76). Qed.
Lemma lem5701858 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5701859 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5701860 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5701859 h1) (fun h1 : term168 = True => @lem5701858)). Qed.
Lemma lem5701861 : term168 = True.
Proof. exact (EQ_MP (@lem5701860) (@lem5701858)). Qed.
Lemma lem5701862 : term161 = True.
Proof. exact (TRANS (@lem5701857) (@lem5701861)). Qed.
Lemma lem5701863 : True = term161.
Proof. exact (SYM (@lem5701862)). Qed.
Lemma lem5701864 : term161.
Proof. exact (EQ_MP (@lem5701863) (@lem0)). Qed.
Lemma lem5701865 : term201.
Proof. exact (@lem5701854 (@lem5701864)). Qed.
Lemma lem5701867 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5701868 : term161 = term168.
Proof. exact (@lem5701867 (NUMERAL 0) term76). Qed.
Lemma lem5701869 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5701870 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5701871 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5701870 h1) (fun h1 : term168 = True => @lem5701869)). Qed.
Lemma lem5701872 : term168 = True.
Proof. exact (EQ_MP (@lem5701871) (@lem5701869)). Qed.
Lemma lem5701873 : term161 = True.
Proof. exact (TRANS (@lem5701868) (@lem5701872)). Qed.
Lemma lem5701874 : True = term161.
Proof. exact (SYM (@lem5701873)). Qed.
Lemma lem5701875 : term161.
Proof. exact (EQ_MP (@lem5701874) (@lem0)). Qed.
Lemma lem5701876 : term202.
Proof. exact (@lem5701865 (@lem5701875)). Qed.
Lemma lem5701878 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5701879 : term161 = term168.
Proof. exact (@lem5701878 (NUMERAL 0) term76). Qed.
Lemma lem5701880 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5701881 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5701882 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5701881 h1) (fun h1 : term168 = True => @lem5701880)). Qed.
Lemma lem5701883 : term168 = True.
Proof. exact (EQ_MP (@lem5701882) (@lem5701880)). Qed.
Lemma lem5701884 : term161 = True.
Proof. exact (TRANS (@lem5701879) (@lem5701883)). Qed.
Lemma lem5701885 : True = term161.
Proof. exact (SYM (@lem5701884)). Qed.
Lemma lem5701886 : term161.
Proof. exact (EQ_MP (@lem5701885) (@lem0)). Qed.
Lemma lem5701887 : term203.
Proof. exact (@lem5701876 (@lem5701886)). Qed.
Lemma lem5701889 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5701890 : term119 = term120.
Proof. exact (@lem5701889 term76 term76). Qed.
Lemma lem5701891 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5701892 : term122 = term76.
Proof. exact (EQ_MP (@lem5701891) (@lem940073)). Qed.
Lemma lem5701893 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5701894 : term120 = term75.
Proof. exact (MK_COMB (@lem5701893) (@lem5701892)). Qed.
Lemma lem5701895 : term119 = term75.
Proof. exact (TRANS (@lem5701890) (@lem5701894)). Qed.
Lemma lem5701897 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5701898 : term114 = term125.
Proof. exact (@lem5701897 term76 term76). Qed.
Lemma lem5701899 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5701900 : term122 = term76.
Proof. exact (EQ_MP (@lem5701899) (@lem940073)). Qed.
Lemma lem5701901 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5701902 : term120 = term75.
Proof. exact (MK_COMB (@lem5701901) (@lem5701900)). Qed.
Lemma lem5701903 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5701904 : term125 = term103.
Proof. exact (MK_COMB (@lem5701903) (@lem5701902)). Qed.
Lemma lem5701905 : term114 = term103.
Proof. exact (TRANS (@lem5701898) (@lem5701904)). Qed.
Lemma lem5701906 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5701907 : term204 = term196.
Proof. exact (MK_COMB (@lem5701906) (@lem5701905)). Qed.
Lemma lem5701908 : term205 = term198.
Proof. exact (MK_COMB (@lem5701907) (@lem5701895)). Qed.
Lemma lem5701910 (m : nat) : (term206 m) = term81.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5701911 : term198 = term81.
Proof. exact (@lem5701910 term76). Qed.
Lemma lem5701912 : term205 = term81.
Proof. exact (TRANS (@lem5701908) (@lem5701911)). Qed.
Lemma lem5701913 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5701914 : term207 = term208.
Proof. exact (MK_COMB (@lem5701913) (@lem5701912)). Qed.
Lemma lem5701915 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem5701916 : term209 = term173.
Proof. exact (MK_COMB (@lem5701914) (@lem5701915)). Qed.
Lemma lem5701918 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5701919 : term173 = term81.
Proof. exact (@lem5701918 term76). Qed.
Lemma lem5701920 : term209 = term81.
Proof. exact (TRANS (@lem5701916) (@lem5701919)). Qed.
Lemma lem5701922 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5701923 : term119 = term120.
Proof. exact (@lem5701922 term76 term76). Qed.
Lemma lem5701924 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5701925 : term122 = term76.
Proof. exact (EQ_MP (@lem5701924) (@lem940073)). Qed.
Lemma lem5701926 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5701927 : term120 = term75.
Proof. exact (MK_COMB (@lem5701926) (@lem5701925)). Qed.
Lemma lem5701928 : term119 = term75.
Proof. exact (TRANS (@lem5701923) (@lem5701927)). Qed.
Lemma lem5701929 : term208 = term208.
Proof. exact (eq_refl term208). Qed.
Lemma lem5701930 : term210 = term173.
Proof. exact (MK_COMB (@lem5701929) (@lem5701928)). Qed.
Lemma lem5701932 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5701933 : term173 = term81.
Proof. exact (@lem5701932 term76). Qed.
Lemma lem5701934 : term210 = term81.
Proof. exact (TRANS (@lem5701930) (@lem5701933)). Qed.
Lemma lem5701935 : term81 = term210.
Proof. exact (SYM (@lem5701934)). Qed.
Lemma lem5701936 : term209 = term210.
Proof. exact (TRANS (@lem5701920) (@lem5701935)). Qed.
Lemma lem5701937 : term199 = term162.
Proof. exact (@lem5701887 (@lem5701936)). Qed.
Lemma lem5701938 : term198 = term162.
Proof. exact (TRANS (@lem5701853) (@lem5701937)). Qed.
Lemma lem5701940 (x : real) : (term128 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5701941 : term162 = term81.
Proof. exact (@lem5701940 term81). Qed.
Lemma lem5701942 : term198 = term81.
Proof. exact (TRANS (@lem5701938) (@lem5701941)). Qed.
Lemma lem5701943 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5701944 : term211 = term208.
Proof. exact (MK_COMB (@lem5701943) (@lem5701942)). Qed.
Lemma lem5701945 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem5701946 (x : int) : (term195 x) = (term212 x).
Proof. exact (MK_COMB (@lem5701944) (@lem5701945 x)). Qed.
Lemma lem5701947 (x : int) : (term229 x) = (term212 x).
Proof. exact (TRANS (@lem5701844 x) (@lem5701946 x)). Qed.
Lemma lem5701948 (x : int) : (term212 x) = term81.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem5701949 (x : int) : (term229 x) = term81.
Proof. exact (TRANS (@lem5701947 x) (@lem5701948 x)). Qed.
Lemma lem5701950 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5701951 (x : int) : (term230 x) = term145.
Proof. exact (MK_COMB (@lem5701950) (@lem5701949 x)). Qed.
Lemma lem5701952 : term103 = term103.
Proof. exact (eq_refl term103). Qed.
Lemma lem5701953 (x : int) : (term228 x) = term231.
Proof. exact (MK_COMB (@lem5701951 x) (@lem5701952)). Qed.
Lemma lem5701954 (x : int) : (term227 x) = term231.
Proof. exact (TRANS (@lem5701843 x) (@lem5701953 x)). Qed.
Lemma lem5701955 : term231 = term103.
Proof. exact (@lem1982721 term103). Qed.
Lemma lem5701956 (x : int) : (term227 x) = term103.
Proof. exact (TRANS (@lem5701954 x) (@lem5701955)). Qed.
Lemma lem5701957 (l : int) (x : int) : (term226 l x) = term231.
Proof. exact (MK_COMB (@lem5701842 l) (@lem5701956 x)). Qed.
Lemma lem5701958 (l : int) (x : int) : (term225 l x) = term231.
Proof. exact (TRANS (@lem5701734 l x) (@lem5701957 l x)). Qed.
Lemma lem5701959 : term231 = term103.
Proof. exact (@lem1982721 term103). Qed.
Lemma lem5701960 (l : int) (x : int) : (term225 l x) = term103.
Proof. exact (TRANS (@lem5701958 l x) (@lem5701959)). Qed.
Lemma lem5701961 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5701962 (l : int) (x : int) : (term232 l x) = term233.
Proof. exact (MK_COMB (@lem5701961) (@lem5701960 l x)). Qed.
Lemma lem5701963 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem5701964 (l : int) (x : int) : (term224 l x) = term234.
Proof. exact (MK_COMB (@lem5701962 l x) (@lem5701963)). Qed.
Lemma lem5701965 (l : int) (r : int) (x : int) (h1 : term159 l r x) : term234.
Proof. exact (EQ_MP (@lem5701964 l x) (@lem5701733 l r x h1)). Qed.
Lemma lem5701967 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5701968 : term234 = term235.
Proof. exact (@lem5701967 term81 term103). Qed.
Lemma lem5701970 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5701971 : term103 = term111.
Proof. exact (@lem5701970 term76). Qed.
Lemma lem5701973 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5701974 : term81 = term162.
Proof. exact (@lem5701973 (NUMERAL 0)). Qed.
Lemma lem5701975 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5701976 : term236 = term237.
Proof. exact (MK_COMB (@lem5701975) (@lem5701974)). Qed.
Lemma lem5701977 : term235 = term238.
Proof. exact (MK_COMB (@lem5701976) (@lem5701971)). Qed.
Lemma lem5701978 : term239.
Proof. exact (@lem1980026 term81 term75 term103 term75). Qed.
Lemma lem5701980 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5701981 : term161 = term168.
Proof. exact (@lem5701980 (NUMERAL 0) term76). Qed.
Lemma lem5701982 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5701983 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5701984 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5701983 h1) (fun h1 : term168 = True => @lem5701982)). Qed.
Lemma lem5701985 : term168 = True.
Proof. exact (EQ_MP (@lem5701984) (@lem5701982)). Qed.
Lemma lem5701986 : term161 = True.
Proof. exact (TRANS (@lem5701981) (@lem5701985)). Qed.
Lemma lem5701987 : True = term161.
Proof. exact (SYM (@lem5701986)). Qed.
Lemma lem5701988 : term161.
Proof. exact (EQ_MP (@lem5701987) (@lem0)). Qed.
Lemma lem5701989 : term240.
Proof. exact (@lem5701978 (@lem5701988)). Qed.
Lemma lem5701991 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5701992 : term161 = term168.
Proof. exact (@lem5701991 (NUMERAL 0) term76). Qed.
Lemma lem5701993 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5701994 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5701995 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5701994 h1) (fun h1 : term168 = True => @lem5701993)). Qed.
Lemma lem5701996 : term168 = True.
Proof. exact (EQ_MP (@lem5701995) (@lem5701993)). Qed.
Lemma lem5701997 : term161 = True.
Proof. exact (TRANS (@lem5701992) (@lem5701996)). Qed.
Lemma lem5701998 : True = term161.
Proof. exact (SYM (@lem5701997)). Qed.
Lemma lem5701999 : term161.
Proof. exact (EQ_MP (@lem5701998) (@lem0)). Qed.
Lemma lem5702000 : term238 = term241.
Proof. exact (@lem5701989 (@lem5701999)). Qed.
Lemma lem5702002 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5702003 : term114 = term125.
Proof. exact (@lem5702002 term76 term76). Qed.
Lemma lem5702004 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5702005 : term122 = term76.
Proof. exact (EQ_MP (@lem5702004) (@lem940073)). Qed.
Lemma lem5702006 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5702007 : term120 = term75.
Proof. exact (MK_COMB (@lem5702006) (@lem5702005)). Qed.
Lemma lem5702008 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5702009 : term125 = term103.
Proof. exact (MK_COMB (@lem5702008) (@lem5702007)). Qed.
Lemma lem5702010 : term114 = term103.
Proof. exact (TRANS (@lem5702003) (@lem5702009)). Qed.
Lemma lem5702012 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5702013 : term173 = term81.
Proof. exact (@lem5702012 term76). Qed.
Lemma lem5702014 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5702015 : term242 = term236.
Proof. exact (MK_COMB (@lem5702014) (@lem5702013)). Qed.
Lemma lem5702016 : term241 = term235.
Proof. exact (MK_COMB (@lem5702015) (@lem5702010)). Qed.
Lemma lem5702018 (m : nat) (n : nat) : (term243 m n) = (term244 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5702019 : term235 = term245.
Proof. exact (@lem5702018 (NUMERAL 0) term76). Qed.
Lemma lem5702020 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5702021 (h1 : term169 = (BIT1 0)) : (term76 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5702022 : (term169 = (BIT1 0)) = ((term76 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5702021 h1) (fun h1 : (term76 = (NUMERAL 0)) = False => @lem5702020)). Qed.
Lemma lem5702023 : (term76 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5702022) (@lem5702020)). Qed.
Lemma lem5702024 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5702025 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5702026 : term246 = (and True).
Proof. exact (MK_COMB (@lem5702025) (@lem5702024)). Qed.
Lemma lem5702027 : term245 = (True /\ False).
Proof. exact (MK_COMB (@lem5702026) (@lem5702023)). Qed.
Lemma lem5702029 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5702030 : term245 = False.
Proof. exact (TRANS (@lem5702027) (@lem5702029)). Qed.
Lemma lem5702031 : term235 = False.
Proof. exact (TRANS (@lem5702019) (@lem5702030)). Qed.
Lemma lem5702032 : term241 = False.
Proof. exact (TRANS (@lem5702016) (@lem5702031)). Qed.
Lemma lem5702033 : term238 = False.
Proof. exact (TRANS (@lem5702000) (@lem5702032)). Qed.
Lemma lem5702034 : term235 = False.
Proof. exact (TRANS (@lem5701977) (@lem5702033)). Qed.
Lemma lem5702035 : term234 = False.
Proof. exact (TRANS (@lem5701968) (@lem5702034)). Qed.
Lemma lem5702036 (l : int) (r : int) (x : int) (h1 : term159 l r x) : False.
Proof. exact (EQ_MP (@lem5702035) (@lem5701965 l r x h1)). Qed.
Lemma lem5702038 (l : int) (r : int) (x : int) (h1 : term159 l r x) : term159 l r x.
Proof. exact (h1). Qed.
Lemma lem5702039 (l : int) (r : int) (x : int) (h1 : term159 l r x) : (term159 l r x) = False.
Proof. exact (prop_ext (fun h2 : term159 l r x => @lem5702036 l r x h1) (fun h2 : False => @lem5702038 l r x h1)). Qed.
Lemma lem5702040 (l : int) (r : int) (x : int) (h1 : term159 l r x) : False.
Proof. exact (EQ_MP (@lem5702039 l r x h1) (@lem5702038 l r x h1)). Qed.
Lemma lem5702041 (l : int) (x : int) (r : int) (h1 : term89 l x r) : term89 l x r.
Proof. exact (h1). Qed.
Lemma lem5702042 (l : int) (x : int) (r : int) (h1 : term89 l x r) : term159 l r x.
Proof. exact (EQ_MP (@lem5701296 l r x) (@lem5702041 l x r h1)). Qed.
Lemma lem5702043 (l : int) (x : int) (r : int) (h1 : term89 l x r) : (term159 l r x) = False.
Proof. exact (prop_ext (fun h2 : term159 l r x => @lem5702040 l r x h2) (fun h2 : False => @lem5702042 l x r h1)). Qed.
Lemma lem5702044 (l : int) (x : int) (r : int) (h1 : term89 l x r) : False.
Proof. exact (EQ_MP (@lem5702043 l x r h1) (@lem5702042 l x r h1)). Qed.
Lemma lem5702045 (l : int) (x : int) (r : int) : term247 l x r.
Proof. exact (fun h0 : term89 l x r => @lem5702044 l x r h0). Qed.
Lemma lem5702046 (l : int) (x : int) (r : int) : term248 l x r.
Proof. exact (@lem1386578 (term249 l x r)). Qed.
Lemma lem5702049 (l : int) (x : int) (r : int) : term249 l x r.
Proof. exact (@lem5702046 l x r (@lem5702045 l x r)). Qed.
Lemma lem5702050 (l : int) (x : int) (r : int) : (term87 l x r) = (term54 l x r).
Proof. exact (SYM (@lem5701070 l x r)). Qed.
Lemma lem5702051 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5702052 (l : int) (x : int) (r : int) : (term249 l x r) = (term47 l x r).
Proof. exact (MK_COMB (@lem5702051) (@lem5702050 l x r)). Qed.
Lemma lem5702053 (l : int) (x : int) (r : int) : term47 l x r.
Proof. exact (EQ_MP (@lem5702052 l x r) (@lem5702049 l x r)). Qed.
Lemma lem5702054 (l : int) (x : int) (r : int) : term48 l x r.
Proof. exact (EQ_MP (@lem5700978 l x r) (@lem5702053 l x r)). Qed.
Lemma lem5702055 (r : int) (l : int) : term250 r l.
Proof. exact (@lem9784 (term251 r l)). Qed.
Lemma lem5702056 (r : int) (l : int) : (term250 r l) = (term252 r l).
Proof. exact (eq_refl (term250 r l)). Qed.
Lemma lem5702057 (r : int) (l : int) : term252 r l.
Proof. exact (EQ_MP (@lem5702056 r l) (@lem5702055 r l)). Qed.
Lemma lem5702058 (r : int) (l : int) (h1 : term251 r l) : term251 r l.
Proof. exact (h1). Qed.
Lemma lem5702059 (r : int) (l : int) (h1 : term55 r l) : term55 r l.
Proof. exact (h1). Qed.
Lemma lem5702084 {_83095 : Type'} : term18 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem5702085 {_83095 : Type'} (p : _83095 -> Prop) : term19 _83095 p.
Proof. exact (@lem5702084 _83095 p). Qed.
Lemma lem5702086 {_83095 : Type'} (p : _83095 -> Prop) : (term19 _83095 p) = (term20 _83095 p).
Proof. exact (eq_refl (term19 _83095 p)). Qed.
Lemma lem5702087 {_83095 : Type'} (p : _83095 -> Prop) : term20 _83095 p.
Proof. exact (EQ_MP (@lem5702086 _83095 p) (@lem5702085 _83095 p)). Qed.
Lemma lem5702088 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term21 _83095 p x.
Proof. exact (@lem5702087 _83095 p x). Qed.
Lemma lem5702089 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term21 _83095 p x) = ((term22 _83095 x p) = (p x)).
Proof. exact (eq_refl (term21 _83095 p x)). Qed.
Lemma lem5702098 {A : Type'} (s : A -> Prop) : term30 A s.
Proof. exact (@lem3194148 A s). Qed.
Lemma lem5702099 {A : Type'} (s : A -> Prop) : (term30 A s) = (term31 A s).
Proof. exact (eq_refl (term30 A s)). Qed.
Lemma lem5702100 {A : Type'} (s : A -> Prop) : term31 A s.
Proof. exact (EQ_MP (@lem5702099 A s) (@lem5702098 A s)). Qed.
Lemma lem5702101 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term32 A s t.
Proof. exact (@lem5702100 A s t). Qed.
Lemma lem5702102 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term32 A s t) = ((@SUBSET A s t) = (term33 A s t)).
Proof. exact (eq_refl (term32 A s t)). Qed.
Lemma lem5702113 (q : Prop) (p : Prop) (r : Prop) : (term253 p q r) = (term254 q p r).
Proof. exact (EQ_MP (@lem952 q p r) (@lem951 p q r)). Qed.
Lemma lem5702114 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term38 A t s) = (term255 A t s).
Proof. exact (@lem5702113 (@SUBSET A s t) (@FINITE A t) (@FINITE A s)). Qed.
Lemma lem5702119 {A : Type'} (s : A -> Prop) : (term256 A s) = (term257 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem5702114 A t s)). Qed.
Lemma lem5702120 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5702121 {A : Type'} (s : A -> Prop) : (term36 A s) = (term258 A s).
Proof. exact (MK_COMB (@lem5702120 A) (@lem5702119 A s)). Qed.
Lemma lem5702126 {A : Type'} : (term259 A) = (term260 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5702121 A s)). Qed.
Lemma lem5702127 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5702128 {A : Type'} : (term34 A) = (term261 A).
Proof. exact (MK_COMB (@lem5702127 A) (@lem5702126 A)). Qed.
Lemma lem5702133 {A : Type'} : term261 A.
Proof. exact (EQ_MP (@lem5702128 A) (@lem3599924 A)). Qed.
Lemma lem5702134 {A : Type'} (h1 : term261 A) : term261 A.
Proof. exact (h1). Qed.
Lemma lem5702135 {A : Type'} (s : A -> Prop) (h1 : term261 A) : term262 A s.
Proof. exact (@lem5702134 A h1 s). Qed.
Lemma lem5702136 {A : Type'} (s : A -> Prop) : (term262 A s) = (term258 A s).
Proof. exact (eq_refl (term262 A s)). Qed.
Lemma lem5702137 {A : Type'} (s : A -> Prop) (h1 : term261 A) : term258 A s.
Proof. exact (EQ_MP (@lem5702136 A s) (@lem5702135 A s h1)). Qed.
Lemma lem5702138 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term261 A) : term263 A s t.
Proof. exact (@lem5702137 A s h1 t). Qed.
Lemma lem5702139 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term263 A s t) = (term255 A t s).
Proof. exact (eq_refl (term263 A s t)). Qed.
Lemma lem5702140 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term261 A) : term255 A t s.
Proof. exact (EQ_MP (@lem5702139 A t s) (@lem5702138 A s t h1)). Qed.
Lemma lem5702141 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @SUBSET A s t) : @SUBSET A s t.
Proof. exact (h1). Qed.
Lemma lem5702142 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term261 A) (h2 : @SUBSET A s t) : term264 A t s.
Proof. exact (@lem5702140 A t s h1 (@lem5702141 A s t h2)). Qed.
Lemma lem5702143 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @SUBSET A s t) : term265 A t s.
Proof. exact (fun h0 : term261 A => @lem5702142 A s t h0 h1). Qed.
Lemma lem5702144 {A : Type'} (h1 : term261 A) : term261 A.
Proof. exact (h1). Qed.
Lemma lem5702145 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term261 A) (h2 : @SUBSET A s t) : term264 A t s.
Proof. exact (@lem5702143 A s t h2 (@lem5702144 A h1)). Qed.
Lemma lem5702146 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term261 A) : term255 A t s.
Proof. exact (fun h0 : @SUBSET A s t => @lem5702145 A s t h1 h0). Qed.
Lemma lem5702147 {A : Type'} (t : A -> Prop) (h1 : term261 A) : term266 A t.
Proof. exact (fun s : A -> Prop => @lem5702146 A t s h1). Qed.
Lemma lem5702148 {A : Type'} (h1 : term261 A) : term267 A.
Proof. exact (fun t : A -> Prop => @lem5702147 A t h1). Qed.
Lemma lem5702149 {A : Type'} : term268 A.
Proof. exact (fun h0 : term261 A => @lem5702148 A h0). Qed.
Lemma lem5702150 {A : Type'} : term267 A.
Proof. exact (@lem5702149 A (@lem5702133 A)). Qed.
Lemma lem5702151 {A : Type'} (t : A -> Prop) : term269 A t.
Proof. exact (@lem5702150 A t). Qed.
Lemma lem5702152 {A : Type'} (t : A -> Prop) : (term269 A t) = (term266 A t).
Proof. exact (eq_refl (term269 A t)). Qed.
Lemma lem5702153 {A : Type'} (t : A -> Prop) : term266 A t.
Proof. exact (EQ_MP (@lem5702152 A t) (@lem5702151 A t)). Qed.
Lemma lem5702154 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term270 A t s.
Proof. exact (@lem5702153 A t s). Qed.
Lemma lem5702155 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term270 A t s) = (term255 A t s).
Proof. exact (eq_refl (term270 A t s)). Qed.
Lemma lem5702157 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term271 A P Q) : term271 A P Q.
Proof. exact (h1). Qed.
Lemma lem5702158 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term272 A P Q) : term272 A P Q.
Proof. exact (h1). Qed.
Lemma lem5702159 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term272 A P Q) (h2 : term271 A P Q) : term273 A P Q.
Proof. exact (@lem5702157 A P Q h2 (@lem5702158 A P Q h1)). Qed.
Lemma lem5702160 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term272 A P Q) : term274 A P Q.
Proof. exact (fun h0 : term271 A P Q => @lem5702159 A P Q h1 h0). Qed.
Lemma lem5702161 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term271 A P Q) : term271 A P Q.
Proof. exact (h1). Qed.
Lemma lem5702162 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term272 A P Q) (h2 : term271 A P Q) : term273 A P Q.
Proof. exact (@lem5702160 A P Q h1 (@lem5702161 A P Q h2)). Qed.
Lemma lem5702163 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term271 A P Q) : term271 A P Q.
Proof. exact (fun h0 : term272 A P Q => @lem5702162 A P Q h0 h1). Qed.
Lemma lem5702164 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term275 A P Q.
Proof. exact (fun h0 : term271 A P Q => @lem5702163 A P Q h0). Qed.
Lemma lem5702176 (a : Prop) : term276 a.
Proof. exact (@lem9851 a). Qed.
Lemma lem5702177 (a : Prop) : (term276 a) = (term277 a).
Proof. exact (eq_refl (term276 a)). Qed.
Lemma lem5702178 (a : Prop) : term277 a.
Proof. exact (EQ_MP (@lem5702177 a) (@lem5702176 a)). Qed.
Lemma lem5702179 (a : Prop) (h1 : a = True) : a = True.
Proof. exact (h1). Qed.
Lemma lem5702180 (a : Prop) (h1 : a = False) : a = False.
Proof. exact (h1). Qed.
Lemma lem5702191 (b : Prop) : (term278 b) = (term278 b).
Proof. exact (eq_refl (term278 b)). Qed.
Lemma lem5702192 (b : Prop) (a : Prop) (h1 : a = True) : (term279 b a) = (term280 b).
Proof. exact (MK_COMB (@lem5702191 b) (@lem5702179 a h1)). Qed.
Lemma lem5702193 (b : Prop) : (term280 b) = (term281 b).
Proof. exact (eq_refl (term280 b)). Qed.
Lemma lem5702194 (b : Prop) (a : Prop) : (term282 b a) = (term282 b a).
Proof. exact (eq_refl (term282 b a)). Qed.
Lemma lem5702195 (a : Prop) (b : Prop) : ((term279 b a) = (term280 b)) = ((term279 b a) = (term281 b)).
Proof. exact (MK_COMB (@lem5702194 b a) (@lem5702193 b)). Qed.
Lemma lem5702196 (a : Prop) (b : Prop) : (term279 b a) = (term283 a b).
Proof. exact (eq_refl (term279 b a)). Qed.
Lemma lem5702197 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5702198 (a : Prop) (b : Prop) : (term282 b a) = (term284 a b).
Proof. exact (MK_COMB (@lem5702197) (@lem5702196 a b)). Qed.
Lemma lem5702199 (b : Prop) : (term281 b) = (term281 b).
Proof. exact (eq_refl (term281 b)). Qed.
Lemma lem5702200 (a : Prop) (b : Prop) : ((term279 b a) = (term281 b)) = ((term283 a b) = (term281 b)).
Proof. exact (MK_COMB (@lem5702198 a b) (@lem5702199 b)). Qed.
Lemma lem5702201 (a : Prop) (b : Prop) : ((term279 b a) = (term280 b)) = ((term283 a b) = (term281 b)).
Proof. exact (TRANS (@lem5702195 a b) (@lem5702200 a b)). Qed.
Lemma lem5702202 (b : Prop) (a : Prop) (h1 : a = True) : (term283 a b) = (term281 b).
Proof. exact (EQ_MP (@lem5702201 a b) (@lem5702192 b a h1)). Qed.
Lemma lem5702203 (b : Prop) (a : Prop) (h1 : a = True) : (term281 b) = (term283 a b).
Proof. exact (SYM (@lem5702202 b a h1)). Qed.
Lemma lem5702204 (b : Prop) : (term278 b) = (term278 b).
Proof. exact (eq_refl (term278 b)). Qed.
Lemma lem5702205 (b : Prop) (a : Prop) (h1 : a = False) : (term279 b a) = (term285 b).
Proof. exact (MK_COMB (@lem5702204 b) (@lem5702180 a h1)). Qed.
Lemma lem5702206 (b : Prop) : (term285 b) = (term286 b).
Proof. exact (eq_refl (term285 b)). Qed.
Lemma lem5702207 (b : Prop) (a : Prop) : (term282 b a) = (term282 b a).
Proof. exact (eq_refl (term282 b a)). Qed.
Lemma lem5702208 (a : Prop) (b : Prop) : ((term279 b a) = (term285 b)) = ((term279 b a) = (term286 b)).
Proof. exact (MK_COMB (@lem5702207 b a) (@lem5702206 b)). Qed.
Lemma lem5702209 (a : Prop) (b : Prop) : (term279 b a) = (term283 a b).
Proof. exact (eq_refl (term279 b a)). Qed.
Lemma lem5702210 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5702211 (a : Prop) (b : Prop) : (term282 b a) = (term284 a b).
Proof. exact (MK_COMB (@lem5702210) (@lem5702209 a b)). Qed.
Lemma lem5702212 (b : Prop) : (term286 b) = (term286 b).
Proof. exact (eq_refl (term286 b)). Qed.
Lemma lem5702213 (a : Prop) (b : Prop) : ((term279 b a) = (term286 b)) = ((term283 a b) = (term286 b)).
Proof. exact (MK_COMB (@lem5702211 a b) (@lem5702212 b)). Qed.
Lemma lem5702214 (a : Prop) (b : Prop) : ((term279 b a) = (term285 b)) = ((term283 a b) = (term286 b)).
Proof. exact (TRANS (@lem5702208 a b) (@lem5702213 a b)). Qed.
Lemma lem5702215 (b : Prop) (a : Prop) (h1 : a = False) : (term283 a b) = (term286 b).
Proof. exact (EQ_MP (@lem5702214 a b) (@lem5702205 b a h1)). Qed.
Lemma lem5702216 (b : Prop) (a : Prop) (h1 : a = False) : (term286 b) = (term283 a b).
Proof. exact (SYM (@lem5702215 b a h1)). Qed.
Lemma lem5702220 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem5702221 (b : Prop) : (term287 b) = (True -> b).
Proof. exact (@lem5702220 (True -> b)). Qed.
Lemma lem5702223 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem5702224 (b : Prop) : (True -> b) = b.
Proof. exact (@lem5702223 b). Qed.
Lemma lem5702225 (b : Prop) : (term287 b) = b.
Proof. exact (TRANS (@lem5702221 b) (@lem5702224 b)). Qed.
Lemma lem5702226 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5702227 (b : Prop) : (term288 b) = (imp b).
Proof. exact (MK_COMB (@lem5702226) (@lem5702225 b)). Qed.
Lemma lem5702229 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5702230 (b : Prop) : (True /\ b) = b.
Proof. exact (@lem5702229 b). Qed.
Lemma lem5702231 (b : Prop) : (term281 b) = (b -> b).
Proof. exact (MK_COMB (@lem5702227 b) (@lem5702230 b)). Qed.
Lemma lem5702233 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem5702234 (b : Prop) : (b -> b) = True.
Proof. exact (@lem5702233 b). Qed.
Lemma lem5702235 (b : Prop) : (term281 b) = True.
Proof. exact (TRANS (@lem5702231 b) (@lem5702234 b)). Qed.
Lemma lem5702236 (b : Prop) : True = (term281 b).
Proof. exact (SYM (@lem5702235 b)). Qed.
Lemma lem5702237 (b : Prop) : term281 b.
Proof. exact (EQ_MP (@lem5702236 b) (@lem0)). Qed.
Lemma lem5702241 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem5702242 (b : Prop) : (term289 b) = False.
Proof. exact (@lem5702241 (False -> b)). Qed.
Lemma lem5702243 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5702244 (b : Prop) : (term290 b) = (imp False).
Proof. exact (MK_COMB (@lem5702243) (@lem5702242 b)). Qed.
Lemma lem5702246 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem5702247 (b : Prop) : (False /\ b) = False.
Proof. exact (@lem5702246 b). Qed.
Lemma lem5702248 (b : Prop) : (term286 b) = (False -> False).
Proof. exact (MK_COMB (@lem5702244 b) (@lem5702247 b)). Qed.
Lemma lem5702250 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem5702251 : (False -> False) = True.
Proof. exact (@lem5702250 False). Qed.
Lemma lem5702252 (b : Prop) : (term286 b) = True.
Proof. exact (TRANS (@lem5702248 b) (@lem5702251)). Qed.
Lemma lem5702253 (b : Prop) : True = (term286 b).
Proof. exact (SYM (@lem5702252 b)). Qed.
Lemma lem5702254 (b : Prop) : term286 b.
Proof. exact (EQ_MP (@lem5702253 b) (@lem0)). Qed.
Lemma lem5702255 (b : Prop) (a : Prop) (h1 : a = False) : term283 a b.
Proof. exact (EQ_MP (@lem5702216 b a h1) (@lem5702254 b)). Qed.
Lemma lem5702256 (b : Prop) (a : Prop) (h1 : a = True) : term283 a b.
Proof. exact (EQ_MP (@lem5702203 b a h1) (@lem5702237 b)). Qed.
Lemma lem5702259 (a : Prop) (b : Prop) : term283 a b.
Proof. exact (or_elim (@lem5702178 a) (fun h0 : a = True => @lem5702256 b a h0) (fun h0 : a = False => @lem5702255 b a h0)). Qed.
Lemma lem5702260 (a : Prop) (b : Prop) (h1 : term283 a b) : term283 a b.
Proof. exact (h1). Qed.
Lemma lem5702261 (b : Prop) (a : Prop) (h1 : term291 b a) : term291 b a.
Proof. exact (h1). Qed.
Lemma lem5702262 (a : Prop) (b : Prop) (h1 : term291 b a) (h2 : term283 a b) : a /\ b.
Proof. exact (@lem5702260 a b h2 (@lem5702261 b a h1)). Qed.
Lemma lem5702263 (b : Prop) (a : Prop) (h1 : term291 b a) : term292 a b.
Proof. exact (fun h0 : term283 a b => @lem5702262 a b h1 h0). Qed.
Lemma lem5702264 (a : Prop) (b : Prop) (h1 : term283 a b) : term283 a b.
Proof. exact (h1). Qed.
Lemma lem5702265 (a : Prop) (b : Prop) (h1 : term291 b a) (h2 : term283 a b) : a /\ b.
Proof. exact (@lem5702263 b a h1 (@lem5702264 a b h2)). Qed.
Lemma lem5702266 (a : Prop) (b : Prop) (h1 : term283 a b) : term283 a b.
Proof. exact (fun h0 : term291 b a => @lem5702265 a b h0 h1). Qed.
Lemma lem5702267 (a : Prop) (b : Prop) : term293 a b.
Proof. exact (fun h0 : term283 a b => @lem5702266 a b h0). Qed.
Lemma lem5702270 (a : Prop) (b : Prop) : term283 a b.
Proof. exact (@lem5702267 a b (@lem5702259 a b)). Qed.
Lemma lem5702271 : term294.
Proof. exact (@lem5702270 term295 term296). Qed.
Lemma lem5702272 (h1 : term295) : term295.
Proof. exact (h1). Qed.
Lemma lem5702274 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term271 A P Q.
Proof. exact (@lem5702164 A P Q (@lem7363 A P Q)). Qed.
Lemma lem5702275 (P : int -> Prop) (Q : int -> Prop) : term297 P Q.
Proof. exact (@lem5702274 int P Q). Qed.
Lemma lem5702276 : term298.
Proof. exact (@lem5702275 term299 term300). Qed.
Lemma lem5702277 (l : int) : (term301 l) = (term302 l).
Proof. exact (eq_refl (term301 l)). Qed.
Lemma lem5702278 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5702279 (l : int) : (term303 l) = (term304 l).
Proof. exact (MK_COMB (@lem5702278) (@lem5702277 l)). Qed.
Lemma lem5702280 (l : int) : (term305 l) = (term306 l).
Proof. exact (eq_refl (term305 l)). Qed.
Lemma lem5702281 (l : int) : (term307 l) = (term308 l).
Proof. exact (MK_COMB (@lem5702279 l) (@lem5702280 l)). Qed.
Lemma lem5702282 : term309 = term310.
Proof. exact (fun_ext (fun l : int => @lem5702281 l)). Qed.
Lemma lem5702283 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem5702284 : term311 = term312.
Proof. exact (MK_COMB (@lem5702283) (@lem5702282)). Qed.
Lemma lem5702285 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5702286 : term313 = term314.
Proof. exact (MK_COMB (@lem5702285) (@lem5702284)). Qed.
Lemma lem5702287 (l : int) : (term301 l) = (term302 l).
Proof. exact (eq_refl (term301 l)). Qed.
Lemma lem5702288 : term315 = term299.
Proof. exact (fun_ext (fun l : int => @lem5702287 l)). Qed.
Lemma lem5702289 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem5702290 : term316 = term295.
Proof. exact (MK_COMB (@lem5702289) (@lem5702288)). Qed.
Lemma lem5702291 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5702292 : term317 = term318.
Proof. exact (MK_COMB (@lem5702291) (@lem5702290)). Qed.
Lemma lem5702293 (l : int) : (term305 l) = (term306 l).
Proof. exact (eq_refl (term305 l)). Qed.
Lemma lem5702294 : term319 = term300.
Proof. exact (fun_ext (fun l : int => @lem5702293 l)). Qed.
Lemma lem5702295 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem5702296 : term320 = term321.
Proof. exact (MK_COMB (@lem5702295) (@lem5702294)). Qed.
Lemma lem5702297 : term322 = term323.
Proof. exact (MK_COMB (@lem5702292) (@lem5702296)). Qed.
Lemma lem5702298 : term298 = term324.
Proof. exact (MK_COMB (@lem5702286) (@lem5702297)). Qed.
Lemma lem5702299 : term324.
Proof. exact (EQ_MP (@lem5702298) (@lem5702276)). Qed.
Lemma lem5702301 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term271 A P Q.
Proof. exact (@lem5702164 A P Q (@lem7363 A P Q)). Qed.
Lemma lem5702302 (P : int -> Prop) (Q : int -> Prop) : term297 P Q.
Proof. exact (@lem5702301 int P Q). Qed.
Lemma lem5702303 (l : int) : term325 l.
Proof. exact (@lem5702302 (term326 l) (term327 l)). Qed.
Lemma lem5702304 (l : int) (r : int) : (term328 l r) = (term329 l r).
Proof. exact (eq_refl (term328 l r)). Qed.
Lemma lem5702305 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5702306 (l : int) (r : int) : (term330 l r) = (term331 l r).
Proof. exact (MK_COMB (@lem5702305) (@lem5702304 l r)). Qed.
Lemma lem5702307 (l : int) (r : int) : (term332 l r) = (term333 l r).
Proof. exact (eq_refl (term332 l r)). Qed.
Lemma lem5702308 (l : int) (r : int) : (term334 l r) = (term335 l r).
Proof. exact (MK_COMB (@lem5702306 l r) (@lem5702307 l r)). Qed.
Lemma lem5702309 (l : int) : (term336 l) = (term337 l).
Proof. exact (fun_ext (fun r : int => @lem5702308 l r)). Qed.
Lemma lem5702310 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem5702311 (l : int) : (term338 l) = (term339 l).
Proof. exact (MK_COMB (@lem5702310) (@lem5702309 l)). Qed.
Lemma lem5702312 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5702313 (l : int) : (term340 l) = (term341 l).
Proof. exact (MK_COMB (@lem5702312) (@lem5702311 l)). Qed.
Lemma lem5702314 (l : int) (r : int) : (term328 l r) = (term329 l r).
Proof. exact (eq_refl (term328 l r)). Qed.
Lemma lem5702315 (l : int) : (term342 l) = (term326 l).
Proof. exact (fun_ext (fun r : int => @lem5702314 l r)). Qed.
Lemma lem5702316 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem5702317 (l : int) : (term343 l) = (term302 l).
Proof. exact (MK_COMB (@lem5702316) (@lem5702315 l)). Qed.
Lemma lem5702318 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5702319 (l : int) : (term344 l) = (term304 l).
Proof. exact (MK_COMB (@lem5702318) (@lem5702317 l)). Qed.
Lemma lem5702320 (l : int) (r : int) : (term332 l r) = (term333 l r).
Proof. exact (eq_refl (term332 l r)). Qed.
Lemma lem5702321 (l : int) : (term345 l) = (term327 l).
Proof. exact (fun_ext (fun r : int => @lem5702320 l r)). Qed.
Lemma lem5702322 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem5702323 (l : int) : (term346 l) = (term306 l).
Proof. exact (MK_COMB (@lem5702322) (@lem5702321 l)). Qed.
Lemma lem5702324 (l : int) : (term347 l) = (term308 l).
Proof. exact (MK_COMB (@lem5702319 l) (@lem5702323 l)). Qed.
Lemma lem5702325 (l : int) : (term325 l) = (term348 l).
Proof. exact (MK_COMB (@lem5702313 l) (@lem5702324 l)). Qed.
Lemma lem5702326 (l : int) : term348 l.
Proof. exact (EQ_MP (@lem5702325 l) (@lem5702303 l)). Qed.
Lemma lem5702330 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term271 A P Q.
Proof. exact (@lem5702164 A P Q (@lem7363 A P Q)). Qed.
Lemma lem5702331 (P : int -> Prop) (Q : int -> Prop) : term297 P Q.
Proof. exact (@lem5702330 int P Q). Qed.
Lemma lem5702332 : term349.
Proof. exact (@lem5702331 term299 term350). Qed.
Lemma lem5702333 (l : int) : (term301 l) = (term302 l).
Proof. exact (eq_refl (term301 l)). Qed.
Lemma lem5702334 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5702335 (l : int) : (term303 l) = (term304 l).
Proof. exact (MK_COMB (@lem5702334) (@lem5702333 l)). Qed.
Lemma lem5702336 (l : int) : (term351 l) = (term352 l).
Proof. exact (eq_refl (term351 l)). Qed.
Lemma lem5702337 (l : int) : (term353 l) = (term354 l).
Proof. exact (MK_COMB (@lem5702335 l) (@lem5702336 l)). Qed.
Lemma lem5702338 : term355 = term356.
Proof. exact (fun_ext (fun l : int => @lem5702337 l)). Qed.
Lemma lem5702339 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem5702340 : term357 = term358.
Proof. exact (MK_COMB (@lem5702339) (@lem5702338)). Qed.
Lemma lem5702341 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5702342 : term359 = term360.
Proof. exact (MK_COMB (@lem5702341) (@lem5702340)). Qed.
Lemma lem5702343 (l : int) : (term301 l) = (term302 l).
Proof. exact (eq_refl (term301 l)). Qed.
Lemma lem5702344 : term315 = term299.
Proof. exact (fun_ext (fun l : int => @lem5702343 l)). Qed.
Lemma lem5702345 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem5702346 : term316 = term295.
Proof. exact (MK_COMB (@lem5702345) (@lem5702344)). Qed.
Lemma lem5702347 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5702348 : term317 = term318.
Proof. exact (MK_COMB (@lem5702347) (@lem5702346)). Qed.
Lemma lem5702349 (l : int) : (term351 l) = (term352 l).
Proof. exact (eq_refl (term351 l)). Qed.
Lemma lem5702350 : term361 = term350.
Proof. exact (fun_ext (fun l : int => @lem5702349 l)). Qed.
Lemma lem5702351 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem5702352 : term362 = term363.
Proof. exact (MK_COMB (@lem5702351) (@lem5702350)). Qed.
Lemma lem5702353 : term364 = term365.
Proof. exact (MK_COMB (@lem5702348) (@lem5702352)). Qed.
Lemma lem5702354 : term349 = term366.
Proof. exact (MK_COMB (@lem5702342) (@lem5702353)). Qed.
Lemma lem5702355 : term366.
Proof. exact (EQ_MP (@lem5702354) (@lem5702332)). Qed.
Lemma lem5702357 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term271 A P Q.
Proof. exact (@lem5702164 A P Q (@lem7363 A P Q)). Qed.
Lemma lem5702358 (P : int -> Prop) (Q : int -> Prop) : term297 P Q.
Proof. exact (@lem5702357 int P Q). Qed.
Lemma lem5702359 (l : int) : term367 l.
Proof. exact (@lem5702358 (term326 l) (term368 l)). Qed.
Lemma lem5702360 (l : int) (r : int) : (term328 l r) = (term329 l r).
Proof. exact (eq_refl (term328 l r)). Qed.
Lemma lem5702361 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5702362 (l : int) (r : int) : (term330 l r) = (term331 l r).
Proof. exact (MK_COMB (@lem5702361) (@lem5702360 l r)). Qed.
Lemma lem5702363 (l : int) (r : int) : (term369 l r) = (term370 l r).
Proof. exact (eq_refl (term369 l r)). Qed.
Lemma lem5702364 (l : int) (r : int) : (term371 l r) = (term372 l r).
Proof. exact (MK_COMB (@lem5702362 l r) (@lem5702363 l r)). Qed.
Lemma lem5702365 (l : int) : (term373 l) = (term374 l).
Proof. exact (fun_ext (fun r : int => @lem5702364 l r)). Qed.
Lemma lem5702366 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem5702367 (l : int) : (term375 l) = (term376 l).
Proof. exact (MK_COMB (@lem5702366) (@lem5702365 l)). Qed.
Lemma lem5702368 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5702369 (l : int) : (term377 l) = (term378 l).
Proof. exact (MK_COMB (@lem5702368) (@lem5702367 l)). Qed.
Lemma lem5702370 (l : int) (r : int) : (term328 l r) = (term329 l r).
Proof. exact (eq_refl (term328 l r)). Qed.
Lemma lem5702371 (l : int) : (term342 l) = (term326 l).
Proof. exact (fun_ext (fun r : int => @lem5702370 l r)). Qed.
Lemma lem5702372 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem5702373 (l : int) : (term343 l) = (term302 l).
Proof. exact (MK_COMB (@lem5702372) (@lem5702371 l)). Qed.
Lemma lem5702374 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5702375 (l : int) : (term344 l) = (term304 l).
Proof. exact (MK_COMB (@lem5702374) (@lem5702373 l)). Qed.
Lemma lem5702376 (l : int) (r : int) : (term369 l r) = (term370 l r).
Proof. exact (eq_refl (term369 l r)). Qed.
Lemma lem5702377 (l : int) : (term379 l) = (term368 l).
Proof. exact (fun_ext (fun r : int => @lem5702376 l r)). Qed.
Lemma lem5702378 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem5702379 (l : int) : (term380 l) = (term352 l).
Proof. exact (MK_COMB (@lem5702378) (@lem5702377 l)). Qed.
Lemma lem5702380 (l : int) : (term381 l) = (term354 l).
Proof. exact (MK_COMB (@lem5702375 l) (@lem5702379 l)). Qed.
Lemma lem5702381 (l : int) : (term367 l) = (term382 l).
Proof. exact (MK_COMB (@lem5702369 l) (@lem5702380 l)). Qed.
Lemma lem5702382 (l : int) : term382 l.
Proof. exact (EQ_MP (@lem5702381 l) (@lem5702359 l)). Qed.
Lemma lem5702386 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term271 A P Q.
Proof. exact (@lem5702164 A P Q (@lem7363 A P Q)). Qed.
Lemma lem5702387 (P : int -> Prop) (Q : int -> Prop) : term297 P Q.
Proof. exact (@lem5702386 int P Q). Qed.
Lemma lem5702388 : term383.
Proof. exact (@lem5702387 term299 term384). Qed.
Lemma lem5702389 (l : int) : (term301 l) = (term302 l).
Proof. exact (eq_refl (term301 l)). Qed.
Lemma lem5702390 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5702391 (l : int) : (term303 l) = (term304 l).
Proof. exact (MK_COMB (@lem5702390) (@lem5702389 l)). Qed.
Lemma lem5702392 (l : int) : (term385 l) = (term386 l).
Proof. exact (eq_refl (term385 l)). Qed.
Lemma lem5702393 (l : int) : (term387 l) = (term388 l).
Proof. exact (MK_COMB (@lem5702391 l) (@lem5702392 l)). Qed.
Lemma lem5702394 : term389 = term390.
Proof. exact (fun_ext (fun l : int => @lem5702393 l)). Qed.
Lemma lem5702395 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem5702396 : term391 = term392.
Proof. exact (MK_COMB (@lem5702395) (@lem5702394)). Qed.
Lemma lem5702397 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5702398 : term393 = term394.
Proof. exact (MK_COMB (@lem5702397) (@lem5702396)). Qed.
Lemma lem5702399 (l : int) : (term301 l) = (term302 l).
Proof. exact (eq_refl (term301 l)). Qed.
Lemma lem5702400 : term315 = term299.
Proof. exact (fun_ext (fun l : int => @lem5702399 l)). Qed.
Lemma lem5702401 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem5702402 : term316 = term295.
Proof. exact (MK_COMB (@lem5702401) (@lem5702400)). Qed.
Lemma lem5702403 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5702404 : term317 = term318.
Proof. exact (MK_COMB (@lem5702403) (@lem5702402)). Qed.
Lemma lem5702405 (l : int) : (term385 l) = (term386 l).
Proof. exact (eq_refl (term385 l)). Qed.
Lemma lem5702406 : term395 = term384.
Proof. exact (fun_ext (fun l : int => @lem5702405 l)). Qed.
Lemma lem5702407 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem5702408 : term396 = term397.
Proof. exact (MK_COMB (@lem5702407) (@lem5702406)). Qed.
Lemma lem5702409 : term398 = term399.
Proof. exact (MK_COMB (@lem5702404) (@lem5702408)). Qed.
Lemma lem5702410 : term383 = term400.
Proof. exact (MK_COMB (@lem5702398) (@lem5702409)). Qed.
Lemma lem5702411 : term400.
Proof. exact (EQ_MP (@lem5702410) (@lem5702388)). Qed.
Lemma lem5702413 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term271 A P Q.
Proof. exact (@lem5702164 A P Q (@lem7363 A P Q)). Qed.
Lemma lem5702414 (P : int -> Prop) (Q : int -> Prop) : term297 P Q.
Proof. exact (@lem5702413 int P Q). Qed.
Lemma lem5702415 (l : int) : term401 l.
Proof. exact (@lem5702414 (term326 l) (term402 l)). Qed.
Lemma lem5702416 (l : int) (r : int) : (term328 l r) = (term329 l r).
Proof. exact (eq_refl (term328 l r)). Qed.
Lemma lem5702417 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5702418 (l : int) (r : int) : (term330 l r) = (term331 l r).
Proof. exact (MK_COMB (@lem5702417) (@lem5702416 l r)). Qed.
Lemma lem5702419 (l : int) (r : int) : (term403 l r) = (term404 l r).
Proof. exact (eq_refl (term403 l r)). Qed.
Lemma lem5702420 (l : int) (r : int) : (term405 l r) = (term406 l r).
Proof. exact (MK_COMB (@lem5702418 l r) (@lem5702419 l r)). Qed.
Lemma lem5702421 (l : int) : (term407 l) = (term408 l).
Proof. exact (fun_ext (fun r : int => @lem5702420 l r)). Qed.
Lemma lem5702422 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem5702423 (l : int) : (term409 l) = (term410 l).
Proof. exact (MK_COMB (@lem5702422) (@lem5702421 l)). Qed.
Lemma lem5702424 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5702425 (l : int) : (term411 l) = (term412 l).
Proof. exact (MK_COMB (@lem5702424) (@lem5702423 l)). Qed.
Lemma lem5702426 (l : int) (r : int) : (term328 l r) = (term329 l r).
Proof. exact (eq_refl (term328 l r)). Qed.
Lemma lem5702427 (l : int) : (term342 l) = (term326 l).
Proof. exact (fun_ext (fun r : int => @lem5702426 l r)). Qed.
Lemma lem5702428 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem5702429 (l : int) : (term343 l) = (term302 l).
Proof. exact (MK_COMB (@lem5702428) (@lem5702427 l)). Qed.
Lemma lem5702430 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5702431 (l : int) : (term344 l) = (term304 l).
Proof. exact (MK_COMB (@lem5702430) (@lem5702429 l)). Qed.
Lemma lem5702432 (l : int) (r : int) : (term403 l r) = (term404 l r).
Proof. exact (eq_refl (term403 l r)). Qed.
Lemma lem5702433 (l : int) : (term413 l) = (term402 l).
Proof. exact (fun_ext (fun r : int => @lem5702432 l r)). Qed.
Lemma lem5702434 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem5702435 (l : int) : (term414 l) = (term386 l).
Proof. exact (MK_COMB (@lem5702434) (@lem5702433 l)). Qed.
Lemma lem5702436 (l : int) : (term415 l) = (term388 l).
Proof. exact (MK_COMB (@lem5702431 l) (@lem5702435 l)). Qed.
Lemma lem5702437 (l : int) : (term401 l) = (term416 l).
Proof. exact (MK_COMB (@lem5702425 l) (@lem5702436 l)). Qed.
Lemma lem5702438 (l : int) : term416 l.
Proof. exact (EQ_MP (@lem5702437 l) (@lem5702415 l)). Qed.
Lemma lem5702442 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term255 A t s.
Proof. exact (EQ_MP (@lem5702155 A t s) (@lem5702154 A t s)). Qed.
Lemma lem5702443 (t : int -> Prop) (s : int -> Prop) : term417 t s.
Proof. exact (@lem5702442 int t s). Qed.
Lemma lem5702444 (l : int) (r : int) : term418 l r.
Proof. exact (@lem5702443 (term419 l r) (term420 l r)). Qed.
Lemma lem5702446 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term255 A t s.
Proof. exact (EQ_MP (@lem5702155 A t s) (@lem5702154 A t s)). Qed.
Lemma lem5702447 (t : int -> Prop) (s : int -> Prop) : term417 t s.
Proof. exact (@lem5702446 int t s). Qed.
Lemma lem5702448 (l : int) (r : int) : term421 l r.
Proof. exact (@lem5702447 (term419 l r) (term422 l r)). Qed.
Lemma lem5702450 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term255 A t s.
Proof. exact (EQ_MP (@lem5702155 A t s) (@lem5702154 A t s)). Qed.
Lemma lem5702451 (t : int -> Prop) (s : int -> Prop) : term417 t s.
Proof. exact (@lem5702450 int t s). Qed.
Lemma lem5702452 (l : int) (r : int) : term423 l r.
Proof. exact (@lem5702451 (term419 l r) (term424 l r)). Qed.
Lemma lem5702454 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term33 A s t).
Proof. exact (EQ_MP (@lem5702102 A s t) (@lem5702101 A s t)). Qed.
Lemma lem5702455 (s : int -> Prop) (t : int -> Prop) : (@SUBSET int s t) = (term425 s t).
Proof. exact (@lem5702454 int s t). Qed.
Lemma lem5702456 (l : int) (r : int) : (term426 l r) = (term427 l r).
Proof. exact (@lem5702455 (term420 l r) (term419 l r)). Qed.
Lemma lem5702464 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term22 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem5702089 _83095 p x) (@lem5702088 _83095 p x)). Qed.
Lemma lem5702465 (p : int -> Prop) (x : int) : (term428 x p) = (p x).
Proof. exact (@lem5702464 int p x). Qed.
Lemma lem5702466 (l : int) (r : int) (x : int) : (term429 x l r) = (term430 l r x).
Proof. exact (@lem5702465 (term431 l r) x). Qed.
Lemma lem5702467 (l : int) (x : int) (r : int) : (term430 l r x) = (term432 l x r).
Proof. exact (eq_refl (term430 l r x)). Qed.
Lemma lem5702468 (GEN_PVAR_234 : int) : (@SETSPEC int GEN_PVAR_234) = (@SETSPEC int GEN_PVAR_234).
Proof. exact (eq_refl (@SETSPEC int GEN_PVAR_234)). Qed.
Lemma lem5702469 (GEN_PVAR_234 : int) (l : int) (x : int) (r : int) : (term433 GEN_PVAR_234 l r x) = (term434 GEN_PVAR_234 l x r).
Proof. exact (MK_COMB (@lem5702468 GEN_PVAR_234) (@lem5702467 l x r)). Qed.
Lemma lem5702470 (x : int) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5702471 (GEN_PVAR_234 : int) (l : int) (r : int) (x : int) : (term435 GEN_PVAR_234 l r x) = (term436 GEN_PVAR_234 l r x).
Proof. exact (MK_COMB (@lem5702469 GEN_PVAR_234 l x r) (@lem5702470 x)). Qed.
Lemma lem5702472 (GEN_PVAR_234 : int) (l : int) (r : int) : (term437 GEN_PVAR_234 l r) = (term438 GEN_PVAR_234 l r).
Proof. exact (fun_ext (fun x : int => @lem5702471 GEN_PVAR_234 l r x)). Qed.
Lemma lem5702473 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem5702474 (GEN_PVAR_234 : int) (l : int) (r : int) : (term439 GEN_PVAR_234 l r) = (term440 GEN_PVAR_234 l r).
Proof. exact (MK_COMB (@lem5702473) (@lem5702472 GEN_PVAR_234 l r)). Qed.
Lemma lem5702475 (l : int) (r : int) : (term441 l r) = (term442 l r).
Proof. exact (fun_ext (fun GEN_PVAR_234 : int => @lem5702474 GEN_PVAR_234 l r)). Qed.
Lemma lem5702476 : (@GSPEC int) = (@GSPEC int).
Proof. exact (eq_refl (@GSPEC int)). Qed.
Lemma lem5702477 (l : int) (r : int) : (term443 l r) = (term420 l r).
Proof. exact (MK_COMB (@lem5702476) (@lem5702475 l r)). Qed.
Lemma lem5702478 (x : int) : (@IN int x) = (@IN int x).
Proof. exact (eq_refl (@IN int x)). Qed.
Lemma lem5702479 (x : int) (l : int) (r : int) : (term429 x l r) = (term444 x l r).
Proof. exact (MK_COMB (@lem5702478 x) (@lem5702477 l r)). Qed.
Lemma lem5702480 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5702481 (x : int) (l : int) (r : int) : (term445 x l r) = (term446 x l r).
Proof. exact (MK_COMB (@lem5702480) (@lem5702479 x l r)). Qed.
Lemma lem5702482 (l : int) (x : int) (r : int) : (term430 l r x) = (term432 l x r).
Proof. exact (eq_refl (term430 l r x)). Qed.
Lemma lem5702483 (l : int) (x : int) (r : int) : ((term429 x l r) = (term430 l r x)) = ((term444 x l r) = (term432 l x r)).
Proof. exact (MK_COMB (@lem5702481 x l r) (@lem5702482 l x r)). Qed.
Lemma lem5702484 (l : int) (x : int) (r : int) : (term444 x l r) = (term432 l x r).
Proof. exact (EQ_MP (@lem5702483 l x r) (@lem5702466 l r x)). Qed.
Lemma lem5702487 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5702488 (l : int) (x : int) (r : int) : (term447 x l r) = (term448 l x r).
Proof. exact (MK_COMB (@lem5702487) (@lem5702484 l x r)). Qed.
Lemma lem5702490 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term22 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem5702089 _83095 p x) (@lem5702088 _83095 p x)). Qed.
Lemma lem5702491 (p : int -> Prop) (x : int) : (term428 x p) = (p x).
Proof. exact (@lem5702490 int p x). Qed.
Lemma lem5702492 (l : int) (r : int) (x : int) : (term449 x l r) = (term450 l r x).
Proof. exact (@lem5702491 (term451 l r) x). Qed.
Lemma lem5702493 (l : int) (x : int) (r : int) : (term450 l r x) = (term50 l x r).
Proof. exact (eq_refl (term450 l r x)). Qed.
Lemma lem5702494 (GEN_PVAR_233 : int) : (@SETSPEC int GEN_PVAR_233) = (@SETSPEC int GEN_PVAR_233).
Proof. exact (eq_refl (@SETSPEC int GEN_PVAR_233)). Qed.
Lemma lem5702495 (GEN_PVAR_233 : int) (l : int) (x : int) (r : int) : (term452 GEN_PVAR_233 l r x) = (term453 GEN_PVAR_233 l x r).
Proof. exact (MK_COMB (@lem5702494 GEN_PVAR_233) (@lem5702493 l x r)). Qed.
Lemma lem5702496 (x : int) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5702497 (GEN_PVAR_233 : int) (l : int) (r : int) (x : int) : (term454 GEN_PVAR_233 l r x) = (term455 GEN_PVAR_233 l r x).
Proof. exact (MK_COMB (@lem5702495 GEN_PVAR_233 l x r) (@lem5702496 x)). Qed.
Lemma lem5702498 (GEN_PVAR_233 : int) (l : int) (r : int) : (term456 GEN_PVAR_233 l r) = (term457 GEN_PVAR_233 l r).
Proof. exact (fun_ext (fun x : int => @lem5702497 GEN_PVAR_233 l r x)). Qed.
Lemma lem5702499 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem5702500 (GEN_PVAR_233 : int) (l : int) (r : int) : (term458 GEN_PVAR_233 l r) = (term459 GEN_PVAR_233 l r).
Proof. exact (MK_COMB (@lem5702499) (@lem5702498 GEN_PVAR_233 l r)). Qed.
Lemma lem5702501 (l : int) (r : int) : (term460 l r) = (term461 l r).
Proof. exact (fun_ext (fun GEN_PVAR_233 : int => @lem5702500 GEN_PVAR_233 l r)). Qed.
Lemma lem5702502 : (@GSPEC int) = (@GSPEC int).
Proof. exact (eq_refl (@GSPEC int)). Qed.
Lemma lem5702503 (l : int) (r : int) : (term462 l r) = (term419 l r).
Proof. exact (MK_COMB (@lem5702502) (@lem5702501 l r)). Qed.
Lemma lem5702504 (x : int) : (@IN int x) = (@IN int x).
Proof. exact (eq_refl (@IN int x)). Qed.
Lemma lem5702505 (x : int) (l : int) (r : int) : (term449 x l r) = (term463 x l r).
Proof. exact (MK_COMB (@lem5702504 x) (@lem5702503 l r)). Qed.
Lemma lem5702506 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5702507 (x : int) (l : int) (r : int) : (term464 x l r) = (term465 x l r).
Proof. exact (MK_COMB (@lem5702506) (@lem5702505 x l r)). Qed.
Lemma lem5702508 (l : int) (x : int) (r : int) : (term450 l r x) = (term50 l x r).
Proof. exact (eq_refl (term450 l r x)). Qed.
Lemma lem5702509 (l : int) (x : int) (r : int) : ((term449 x l r) = (term450 l r x)) = ((term463 x l r) = (term50 l x r)).
Proof. exact (MK_COMB (@lem5702507 x l r) (@lem5702508 l x r)). Qed.
Lemma lem5702510 (l : int) (x : int) (r : int) : (term463 x l r) = (term50 l x r).
Proof. exact (EQ_MP (@lem5702509 l x r) (@lem5702492 l r x)). Qed.
Lemma lem5702513 (l : int) (x : int) (r : int) : (term466 x l r) = (term467 l x r).
Proof. exact (MK_COMB (@lem5702488 l x r) (@lem5702510 l x r)). Qed.
Lemma lem5702516 (l : int) (r : int) : (term468 l r) = (term469 l r).
Proof. exact (fun_ext (fun x : int => @lem5702513 l x r)). Qed.
Lemma lem5702517 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem5702518 (l : int) (r : int) : (term427 l r) = (term470 l r).
Proof. exact (MK_COMB (@lem5702517) (@lem5702516 l r)). Qed.
Lemma lem5702523 (l : int) (r : int) : (term426 l r) = (term470 l r).
Proof. exact (TRANS (@lem5702456 l r) (@lem5702518 l r)). Qed.
Lemma lem5702524 (l : int) (r : int) : (term470 l r) = (term426 l r).
Proof. exact (SYM (@lem5702523 l r)). Qed.
Lemma lem5702526 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term33 A s t).
Proof. exact (EQ_MP (@lem5702102 A s t) (@lem5702101 A s t)). Qed.
Lemma lem5702527 (s : int -> Prop) (t : int -> Prop) : (@SUBSET int s t) = (term425 s t).
Proof. exact (@lem5702526 int s t). Qed.
Lemma lem5702528 (l : int) (r : int) : (term471 l r) = (term472 l r).
Proof. exact (@lem5702527 (term422 l r) (term419 l r)). Qed.
Lemma lem5702536 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term22 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem5702089 _83095 p x) (@lem5702088 _83095 p x)). Qed.
Lemma lem5702537 (p : int -> Prop) (x : int) : (term428 x p) = (p x).
Proof. exact (@lem5702536 int p x). Qed.
Lemma lem5702538 (l : int) (r : int) (x : int) : (term473 x l r) = (term474 l r x).
Proof. exact (@lem5702537 (term475 l r) x). Qed.
Lemma lem5702539 (l : int) (x : int) (r : int) : (term474 l r x) = (term476 l x r).
Proof. exact (eq_refl (term474 l r x)). Qed.
Lemma lem5702540 (GEN_PVAR_235 : int) : (@SETSPEC int GEN_PVAR_235) = (@SETSPEC int GEN_PVAR_235).
Proof. exact (eq_refl (@SETSPEC int GEN_PVAR_235)). Qed.
Lemma lem5702541 (GEN_PVAR_235 : int) (l : int) (x : int) (r : int) : (term477 GEN_PVAR_235 l r x) = (term478 GEN_PVAR_235 l x r).
Proof. exact (MK_COMB (@lem5702540 GEN_PVAR_235) (@lem5702539 l x r)). Qed.
Lemma lem5702542 (x : int) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5702543 (GEN_PVAR_235 : int) (l : int) (r : int) (x : int) : (term479 GEN_PVAR_235 l r x) = (term480 GEN_PVAR_235 l r x).
Proof. exact (MK_COMB (@lem5702541 GEN_PVAR_235 l x r) (@lem5702542 x)). Qed.
Lemma lem5702544 (GEN_PVAR_235 : int) (l : int) (r : int) : (term481 GEN_PVAR_235 l r) = (term482 GEN_PVAR_235 l r).
Proof. exact (fun_ext (fun x : int => @lem5702543 GEN_PVAR_235 l r x)). Qed.
Lemma lem5702545 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem5702546 (GEN_PVAR_235 : int) (l : int) (r : int) : (term483 GEN_PVAR_235 l r) = (term484 GEN_PVAR_235 l r).
Proof. exact (MK_COMB (@lem5702545) (@lem5702544 GEN_PVAR_235 l r)). Qed.
Lemma lem5702547 (l : int) (r : int) : (term485 l r) = (term486 l r).
Proof. exact (fun_ext (fun GEN_PVAR_235 : int => @lem5702546 GEN_PVAR_235 l r)). Qed.
Lemma lem5702548 : (@GSPEC int) = (@GSPEC int).
Proof. exact (eq_refl (@GSPEC int)). Qed.
Lemma lem5702549 (l : int) (r : int) : (term487 l r) = (term422 l r).
Proof. exact (MK_COMB (@lem5702548) (@lem5702547 l r)). Qed.
Lemma lem5702550 (x : int) : (@IN int x) = (@IN int x).
Proof. exact (eq_refl (@IN int x)). Qed.
Lemma lem5702551 (x : int) (l : int) (r : int) : (term473 x l r) = (term488 x l r).
Proof. exact (MK_COMB (@lem5702550 x) (@lem5702549 l r)). Qed.
Lemma lem5702552 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5702553 (x : int) (l : int) (r : int) : (term489 x l r) = (term490 x l r).
Proof. exact (MK_COMB (@lem5702552) (@lem5702551 x l r)). Qed.
Lemma lem5702554 (l : int) (x : int) (r : int) : (term474 l r x) = (term476 l x r).
Proof. exact (eq_refl (term474 l r x)). Qed.
Lemma lem5702555 (l : int) (x : int) (r : int) : ((term473 x l r) = (term474 l r x)) = ((term488 x l r) = (term476 l x r)).
Proof. exact (MK_COMB (@lem5702553 x l r) (@lem5702554 l x r)). Qed.
Lemma lem5702556 (l : int) (x : int) (r : int) : (term488 x l r) = (term476 l x r).
Proof. exact (EQ_MP (@lem5702555 l x r) (@lem5702538 l r x)). Qed.
Lemma lem5702559 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5702560 (l : int) (x : int) (r : int) : (term491 x l r) = (term492 l x r).
Proof. exact (MK_COMB (@lem5702559) (@lem5702556 l x r)). Qed.
Lemma lem5702562 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term22 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem5702089 _83095 p x) (@lem5702088 _83095 p x)). Qed.
Lemma lem5702563 (p : int -> Prop) (x : int) : (term428 x p) = (p x).
Proof. exact (@lem5702562 int p x). Qed.
Lemma lem5702564 (l : int) (r : int) (x : int) : (term449 x l r) = (term450 l r x).
Proof. exact (@lem5702563 (term451 l r) x). Qed.
Lemma lem5702565 (l : int) (x : int) (r : int) : (term450 l r x) = (term50 l x r).
Proof. exact (eq_refl (term450 l r x)). Qed.
Lemma lem5702566 (GEN_PVAR_233 : int) : (@SETSPEC int GEN_PVAR_233) = (@SETSPEC int GEN_PVAR_233).
Proof. exact (eq_refl (@SETSPEC int GEN_PVAR_233)). Qed.
Lemma lem5702567 (GEN_PVAR_233 : int) (l : int) (x : int) (r : int) : (term452 GEN_PVAR_233 l r x) = (term453 GEN_PVAR_233 l x r).
Proof. exact (MK_COMB (@lem5702566 GEN_PVAR_233) (@lem5702565 l x r)). Qed.
Lemma lem5702568 (x : int) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5702569 (GEN_PVAR_233 : int) (l : int) (r : int) (x : int) : (term454 GEN_PVAR_233 l r x) = (term455 GEN_PVAR_233 l r x).
Proof. exact (MK_COMB (@lem5702567 GEN_PVAR_233 l x r) (@lem5702568 x)). Qed.
Lemma lem5702570 (GEN_PVAR_233 : int) (l : int) (r : int) : (term456 GEN_PVAR_233 l r) = (term457 GEN_PVAR_233 l r).
Proof. exact (fun_ext (fun x : int => @lem5702569 GEN_PVAR_233 l r x)). Qed.
Lemma lem5702571 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem5702572 (GEN_PVAR_233 : int) (l : int) (r : int) : (term458 GEN_PVAR_233 l r) = (term459 GEN_PVAR_233 l r).
Proof. exact (MK_COMB (@lem5702571) (@lem5702570 GEN_PVAR_233 l r)). Qed.
Lemma lem5702573 (l : int) (r : int) : (term460 l r) = (term461 l r).
Proof. exact (fun_ext (fun GEN_PVAR_233 : int => @lem5702572 GEN_PVAR_233 l r)). Qed.
Lemma lem5702574 : (@GSPEC int) = (@GSPEC int).
Proof. exact (eq_refl (@GSPEC int)). Qed.
Lemma lem5702575 (l : int) (r : int) : (term462 l r) = (term419 l r).
Proof. exact (MK_COMB (@lem5702574) (@lem5702573 l r)). Qed.
Lemma lem5702576 (x : int) : (@IN int x) = (@IN int x).
Proof. exact (eq_refl (@IN int x)). Qed.
Lemma lem5702577 (x : int) (l : int) (r : int) : (term449 x l r) = (term463 x l r).
Proof. exact (MK_COMB (@lem5702576 x) (@lem5702575 l r)). Qed.
Lemma lem5702578 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5702579 (x : int) (l : int) (r : int) : (term464 x l r) = (term465 x l r).
Proof. exact (MK_COMB (@lem5702578) (@lem5702577 x l r)). Qed.
Lemma lem5702580 (l : int) (x : int) (r : int) : (term450 l r x) = (term50 l x r).
Proof. exact (eq_refl (term450 l r x)). Qed.
Lemma lem5702581 (l : int) (x : int) (r : int) : ((term449 x l r) = (term450 l r x)) = ((term463 x l r) = (term50 l x r)).
Proof. exact (MK_COMB (@lem5702579 x l r) (@lem5702580 l x r)). Qed.
Lemma lem5702582 (l : int) (x : int) (r : int) : (term463 x l r) = (term50 l x r).
Proof. exact (EQ_MP (@lem5702581 l x r) (@lem5702564 l r x)). Qed.
Lemma lem5702585 (l : int) (x : int) (r : int) : (term493 x l r) = (term494 l x r).
Proof. exact (MK_COMB (@lem5702560 l x r) (@lem5702582 l x r)). Qed.
Lemma lem5702588 (l : int) (r : int) : (term495 l r) = (term496 l r).
Proof. exact (fun_ext (fun x : int => @lem5702585 l x r)). Qed.
Lemma lem5702589 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem5702590 (l : int) (r : int) : (term472 l r) = (term497 l r).
Proof. exact (MK_COMB (@lem5702589) (@lem5702588 l r)). Qed.
Lemma lem5702595 (l : int) (r : int) : (term471 l r) = (term497 l r).
Proof. exact (TRANS (@lem5702528 l r) (@lem5702590 l r)). Qed.
Lemma lem5702596 (l : int) (r : int) : (term497 l r) = (term471 l r).
Proof. exact (SYM (@lem5702595 l r)). Qed.
Lemma lem5702598 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term33 A s t).
Proof. exact (EQ_MP (@lem5702102 A s t) (@lem5702101 A s t)). Qed.
Lemma lem5702599 (s : int -> Prop) (t : int -> Prop) : (@SUBSET int s t) = (term425 s t).
Proof. exact (@lem5702598 int s t). Qed.
Lemma lem5702600 (l : int) (r : int) : (term498 l r) = (term499 l r).
Proof. exact (@lem5702599 (term424 l r) (term419 l r)). Qed.
Lemma lem5702608 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term22 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem5702089 _83095 p x) (@lem5702088 _83095 p x)). Qed.
Lemma lem5702609 (p : int -> Prop) (x : int) : (term428 x p) = (p x).
Proof. exact (@lem5702608 int p x). Qed.
Lemma lem5702610 (l : int) (r : int) (x : int) : (term500 x l r) = (term501 l r x).
Proof. exact (@lem5702609 (term502 l r) x). Qed.
Lemma lem5702611 (l : int) (x : int) (r : int) : (term501 l r x) = (term503 l x r).
Proof. exact (eq_refl (term501 l r x)). Qed.
Lemma lem5702612 (GEN_PVAR_236 : int) : (@SETSPEC int GEN_PVAR_236) = (@SETSPEC int GEN_PVAR_236).
Proof. exact (eq_refl (@SETSPEC int GEN_PVAR_236)). Qed.
Lemma lem5702613 (GEN_PVAR_236 : int) (l : int) (x : int) (r : int) : (term504 GEN_PVAR_236 l r x) = (term505 GEN_PVAR_236 l x r).
Proof. exact (MK_COMB (@lem5702612 GEN_PVAR_236) (@lem5702611 l x r)). Qed.
Lemma lem5702614 (x : int) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5702615 (GEN_PVAR_236 : int) (l : int) (r : int) (x : int) : (term506 GEN_PVAR_236 l r x) = (term507 GEN_PVAR_236 l r x).
Proof. exact (MK_COMB (@lem5702613 GEN_PVAR_236 l x r) (@lem5702614 x)). Qed.
Lemma lem5702616 (GEN_PVAR_236 : int) (l : int) (r : int) : (term508 GEN_PVAR_236 l r) = (term509 GEN_PVAR_236 l r).
Proof. exact (fun_ext (fun x : int => @lem5702615 GEN_PVAR_236 l r x)). Qed.
Lemma lem5702617 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem5702618 (GEN_PVAR_236 : int) (l : int) (r : int) : (term510 GEN_PVAR_236 l r) = (term511 GEN_PVAR_236 l r).
Proof. exact (MK_COMB (@lem5702617) (@lem5702616 GEN_PVAR_236 l r)). Qed.
Lemma lem5702619 (l : int) (r : int) : (term512 l r) = (term513 l r).
Proof. exact (fun_ext (fun GEN_PVAR_236 : int => @lem5702618 GEN_PVAR_236 l r)). Qed.
Lemma lem5702620 : (@GSPEC int) = (@GSPEC int).
Proof. exact (eq_refl (@GSPEC int)). Qed.
Lemma lem5702621 (l : int) (r : int) : (term514 l r) = (term424 l r).
Proof. exact (MK_COMB (@lem5702620) (@lem5702619 l r)). Qed.
Lemma lem5702622 (x : int) : (@IN int x) = (@IN int x).
Proof. exact (eq_refl (@IN int x)). Qed.
Lemma lem5702623 (x : int) (l : int) (r : int) : (term500 x l r) = (term515 x l r).
Proof. exact (MK_COMB (@lem5702622 x) (@lem5702621 l r)). Qed.
Lemma lem5702624 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5702625 (x : int) (l : int) (r : int) : (term516 x l r) = (term517 x l r).
Proof. exact (MK_COMB (@lem5702624) (@lem5702623 x l r)). Qed.
Lemma lem5702626 (l : int) (x : int) (r : int) : (term501 l r x) = (term503 l x r).
Proof. exact (eq_refl (term501 l r x)). Qed.
Lemma lem5702627 (l : int) (x : int) (r : int) : ((term500 x l r) = (term501 l r x)) = ((term515 x l r) = (term503 l x r)).
Proof. exact (MK_COMB (@lem5702625 x l r) (@lem5702626 l x r)). Qed.
Lemma lem5702628 (l : int) (x : int) (r : int) : (term515 x l r) = (term503 l x r).
Proof. exact (EQ_MP (@lem5702627 l x r) (@lem5702610 l r x)). Qed.
Lemma lem5702631 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5702632 (l : int) (x : int) (r : int) : (term518 x l r) = (term519 l x r).
Proof. exact (MK_COMB (@lem5702631) (@lem5702628 l x r)). Qed.
Lemma lem5702634 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term22 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem5702089 _83095 p x) (@lem5702088 _83095 p x)). Qed.
Lemma lem5702635 (p : int -> Prop) (x : int) : (term428 x p) = (p x).
Proof. exact (@lem5702634 int p x). Qed.
Lemma lem5702636 (l : int) (r : int) (x : int) : (term449 x l r) = (term450 l r x).
Proof. exact (@lem5702635 (term451 l r) x). Qed.
Lemma lem5702637 (l : int) (x : int) (r : int) : (term450 l r x) = (term50 l x r).
Proof. exact (eq_refl (term450 l r x)). Qed.
Lemma lem5702638 (GEN_PVAR_233 : int) : (@SETSPEC int GEN_PVAR_233) = (@SETSPEC int GEN_PVAR_233).
Proof. exact (eq_refl (@SETSPEC int GEN_PVAR_233)). Qed.
Lemma lem5702639 (GEN_PVAR_233 : int) (l : int) (x : int) (r : int) : (term452 GEN_PVAR_233 l r x) = (term453 GEN_PVAR_233 l x r).
Proof. exact (MK_COMB (@lem5702638 GEN_PVAR_233) (@lem5702637 l x r)). Qed.
Lemma lem5702640 (x : int) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5702641 (GEN_PVAR_233 : int) (l : int) (r : int) (x : int) : (term454 GEN_PVAR_233 l r x) = (term455 GEN_PVAR_233 l r x).
Proof. exact (MK_COMB (@lem5702639 GEN_PVAR_233 l x r) (@lem5702640 x)). Qed.
Lemma lem5702642 (GEN_PVAR_233 : int) (l : int) (r : int) : (term456 GEN_PVAR_233 l r) = (term457 GEN_PVAR_233 l r).
Proof. exact (fun_ext (fun x : int => @lem5702641 GEN_PVAR_233 l r x)). Qed.
Lemma lem5702643 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem5702644 (GEN_PVAR_233 : int) (l : int) (r : int) : (term458 GEN_PVAR_233 l r) = (term459 GEN_PVAR_233 l r).
Proof. exact (MK_COMB (@lem5702643) (@lem5702642 GEN_PVAR_233 l r)). Qed.
Lemma lem5702645 (l : int) (r : int) : (term460 l r) = (term461 l r).
Proof. exact (fun_ext (fun GEN_PVAR_233 : int => @lem5702644 GEN_PVAR_233 l r)). Qed.
Lemma lem5702646 : (@GSPEC int) = (@GSPEC int).
Proof. exact (eq_refl (@GSPEC int)). Qed.
Lemma lem5702647 (l : int) (r : int) : (term462 l r) = (term419 l r).
Proof. exact (MK_COMB (@lem5702646) (@lem5702645 l r)). Qed.
Lemma lem5702648 (x : int) : (@IN int x) = (@IN int x).
Proof. exact (eq_refl (@IN int x)). Qed.
Lemma lem5702649 (x : int) (l : int) (r : int) : (term449 x l r) = (term463 x l r).
Proof. exact (MK_COMB (@lem5702648 x) (@lem5702647 l r)). Qed.
Lemma lem5702650 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5702651 (x : int) (l : int) (r : int) : (term464 x l r) = (term465 x l r).
Proof. exact (MK_COMB (@lem5702650) (@lem5702649 x l r)). Qed.
Lemma lem5702652 (l : int) (x : int) (r : int) : (term450 l r x) = (term50 l x r).
Proof. exact (eq_refl (term450 l r x)). Qed.
Lemma lem5702653 (l : int) (x : int) (r : int) : ((term449 x l r) = (term450 l r x)) = ((term463 x l r) = (term50 l x r)).
Proof. exact (MK_COMB (@lem5702651 x l r) (@lem5702652 l x r)). Qed.
Lemma lem5702654 (l : int) (x : int) (r : int) : (term463 x l r) = (term50 l x r).
Proof. exact (EQ_MP (@lem5702653 l x r) (@lem5702636 l r x)). Qed.
Lemma lem5702657 (l : int) (x : int) (r : int) : (term520 x l r) = (term521 l x r).
Proof. exact (MK_COMB (@lem5702632 l x r) (@lem5702654 l x r)). Qed.
Lemma lem5702660 (l : int) (r : int) : (term522 l r) = (term523 l r).
Proof. exact (fun_ext (fun x : int => @lem5702657 l x r)). Qed.
Lemma lem5702661 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem5702662 (l : int) (r : int) : (term499 l r) = (term524 l r).
Proof. exact (MK_COMB (@lem5702661) (@lem5702660 l r)). Qed.
Lemma lem5702667 (l : int) (r : int) : (term498 l r) = (term524 l r).
Proof. exact (TRANS (@lem5702600 l r) (@lem5702662 l r)). Qed.
Lemma lem5702668 (l : int) (r : int) : (term524 l r) = (term498 l r).
Proof. exact (SYM (@lem5702667 l r)). Qed.
Lemma lem5702669 (l : int) (r : int) : (term525 l r) = (term470 l r).
Proof. exact (@lem2954598 (term470 l r)). Qed.
Lemma lem5702696 (l : int) (x : int) (r : int) : (term56 l x r) = (term526 l x r).
Proof. exact (@lem17045 (int_le l x) (int_le x r)). Qed.
Lemma lem5702698 (l : int) (x : int) (r : int) : (term527 l x r) = (term527 l x r).
Proof. exact (eq_refl (term527 l x r)). Qed.
Lemma lem5702699 (l : int) (x : int) (r : int) : (term528 l x r) = (term529 l x r).
Proof. exact (MK_COMB (@lem5702698 l x r) (@lem5702696 l x r)). Qed.
Lemma lem5702700 (l : int) (x : int) (r : int) : (term530 l x r) = (term528 l x r).
Proof. exact (@lem17362 (term432 l x r) (term50 l x r)). Qed.
Lemma lem5702701 (l : int) (x : int) (r : int) : (term530 l x r) = (term529 l x r).
Proof. exact (TRANS (@lem5702700 l x r) (@lem5702699 l x r)). Qed.
Lemma lem5702702 (P : int -> Prop) : (term531 P) = (term532 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem5702703 (l : int) (r : int) : (term533 l r) = (term534 l r).
Proof. exact (@lem5702702 (term469 l r)). Qed.
Lemma lem5702704 (l : int) (x : int) (r : int) : (term535 l r x) = (term467 l x r).
Proof. exact (eq_refl (term535 l r x)). Qed.
Lemma lem5702705 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5702706 (l : int) (x : int) (r : int) : (term536 l r x) = (term530 l x r).
Proof. exact (MK_COMB (@lem5702705) (@lem5702704 l x r)). Qed.
Lemma lem5702707 (l : int) (x : int) (r : int) : (term536 l r x) = (term529 l x r).
Proof. exact (TRANS (@lem5702706 l x r) (@lem5702701 l x r)). Qed.
Lemma lem5702708 (l : int) (r : int) : (term537 l r) = (term538 l r).
Proof. exact (fun_ext (fun x : int => @lem5702707 l x r)). Qed.
Lemma lem5702709 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem5702710 (l : int) (r : int) : (term534 l r) = (term539 l r).
Proof. exact (MK_COMB (@lem5702709) (@lem5702708 l r)). Qed.
Lemma lem5702712 (l : int) (r : int) : (term533 l r) = (term539 l r).
Proof. exact (TRANS (@lem5702703 l r) (@lem5702710 l r)). Qed.
Lemma lem5702729 (l : int) (x : int) (r : int) : (term529 l x r) = (term529 l x r).
Proof. exact (eq_refl (term529 l x r)). Qed.
Lemma lem5702730 (l : int) (r : int) : (term538 l r) = (term538 l r).
Proof. exact (fun_ext (fun x : int => @lem5702729 l x r)). Qed.
Lemma lem5702731 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem5702732 (l : int) (r : int) : (term539 l r) = (term539 l r).
Proof. exact (MK_COMB (@lem5702731) (@lem5702730 l r)). Qed.
Lemma lem5702745 (l : int) (r : int) : (term533 l r) = (term539 l r).
Proof. exact (TRANS (@lem5702712 l r) (@lem5702732 l r)). Qed.
Lemma lem5702746 (l : int) (x : int) (r : int) : (term529 l x r) = (term529 l x r).
Proof. exact (eq_refl (term529 l x r)). Qed.
Lemma lem5702747 (l : int) (r : int) : (term538 l r) = (term538 l r).
Proof. exact (fun_ext (fun x : int => @lem5702746 l x r)). Qed.
Lemma lem5702748 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem5702749 (l : int) (r : int) : (term539 l r) = (term539 l r).
Proof. exact (MK_COMB (@lem5702748) (@lem5702747 l r)). Qed.
Lemma lem5702750 (l : int) (r : int) : (term533 l r) = (term539 l r).
Proof. exact (TRANS (@lem5702745 l r) (@lem5702749 l r)). Qed.
Lemma lem5702753 (x : int) (y : int) : (int_le x y) = (term61 x y).
Proof. exact (EQ_MP (@lem2841616 x y) (@lem2841615 x y)). Qed.
Lemma lem5702755 (l : int) (x : int) : (int_le l x) = (term61 l x).
Proof. exact (@lem5702753 l x). Qed.
Lemma lem5702757 (x : int) (y : int) : (int_lt x y) = (term58 x y).
Proof. exact (proj2 (@lem2841544 x y)). Qed.
Lemma lem5702758 (x : int) (r : int) : (int_lt x r) = (term58 x r).
Proof. exact (@lem5702757 x r). Qed.
Lemma lem5702760 (x : int) (y : int) : (int_le x y) = (term61 x y).
Proof. exact (EQ_MP (@lem2841616 x y) (@lem2841615 x y)). Qed.
Lemma lem5702761 (x : int) (r : int) : (term58 x r) = (term540 x r).
Proof. exact (@lem5702760 (term541 x) r). Qed.
Lemma lem5702763 (x : int) (y : int) : (term64 x y) = (term65 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem5702764 (x : int) : (term542 x) = (term543 x).
Proof. exact (@lem5702763 x term68). Qed.
Lemma lem5702766 (n : nat) : (term73 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem5702767 : term74 = term75.
Proof. exact (@lem5702766 term76). Qed.
Lemma lem5702768 (x : int) : (term143 x) = (term143 x).
Proof. exact (eq_refl (term143 x)). Qed.
Lemma lem5702769 (x : int) : (term543 x) = (term104 x).
Proof. exact (MK_COMB (@lem5702768 x) (@lem5702767)). Qed.
Lemma lem5702770 (x : int) : (term542 x) = (term104 x).
Proof. exact (TRANS (@lem5702764 x) (@lem5702769 x)). Qed.
Lemma lem5702771 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5702772 (x : int) : (term544 x) = (term545 x).
Proof. exact (MK_COMB (@lem5702771) (@lem5702770 x)). Qed.
Lemma lem5702773 (r : int) : (real_of_int r) = (real_of_int r).
Proof. exact (eq_refl (real_of_int r)). Qed.
Lemma lem5702774 (x : int) (r : int) : (term540 x r) = (term546 x r).
Proof. exact (MK_COMB (@lem5702772 x) (@lem5702773 r)). Qed.
Lemma lem5702775 (x : int) (r : int) : (term58 x r) = (term546 x r).
Proof. exact (TRANS (@lem5702761 x r) (@lem5702774 x r)). Qed.
Lemma lem5702776 (x : int) (r : int) : (int_lt x r) = (term546 x r).
Proof. exact (TRANS (@lem5702758 x r) (@lem5702775 x r)). Qed.
Lemma lem5702777 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5702778 (l : int) (x : int) : (term83 l x) = (term84 l x).
Proof. exact (MK_COMB (@lem5702777) (@lem5702755 l x)). Qed.
Lemma lem5702779 (l : int) (x : int) (r : int) : (term432 l x r) = (term547 l x r).
Proof. exact (MK_COMB (@lem5702778 l x) (@lem5702776 x r)). Qed.
Lemma lem5702781 (y : int) (x : int) : (term57 x y) = (term58 y x).
Proof. exact (proj1 (@lem2841542 x y)). Qed.
Lemma lem5702782 (x : int) (l : int) : (term57 l x) = (term58 x l).
Proof. exact (@lem5702781 x l). Qed.
Lemma lem5702784 (x : int) (y : int) : (int_le x y) = (term61 x y).
Proof. exact (EQ_MP (@lem2841616 x y) (@lem2841615 x y)). Qed.
Lemma lem5702785 (x : int) (l : int) : (term58 x l) = (term540 x l).
Proof. exact (@lem5702784 (term541 x) l). Qed.
Lemma lem5702787 (x : int) (y : int) : (term64 x y) = (term65 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem5702788 (x : int) : (term542 x) = (term543 x).
Proof. exact (@lem5702787 x term68). Qed.
Lemma lem5702790 (n : nat) : (term73 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem5702791 : term74 = term75.
Proof. exact (@lem5702790 term76). Qed.
Lemma lem5702792 (x : int) : (term143 x) = (term143 x).
Proof. exact (eq_refl (term143 x)). Qed.
Lemma lem5702793 (x : int) : (term543 x) = (term104 x).
Proof. exact (MK_COMB (@lem5702792 x) (@lem5702791)). Qed.
Lemma lem5702794 (x : int) : (term542 x) = (term104 x).
Proof. exact (TRANS (@lem5702788 x) (@lem5702793 x)). Qed.
Lemma lem5702795 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5702796 (x : int) : (term544 x) = (term545 x).
Proof. exact (MK_COMB (@lem5702795) (@lem5702794 x)). Qed.
Lemma lem5702797 (l : int) : (real_of_int l) = (real_of_int l).
Proof. exact (eq_refl (real_of_int l)). Qed.
Lemma lem5702798 (x : int) (l : int) : (term540 x l) = (term546 x l).
Proof. exact (MK_COMB (@lem5702796 x) (@lem5702797 l)). Qed.
Lemma lem5702799 (x : int) (l : int) : (term58 x l) = (term546 x l).
Proof. exact (TRANS (@lem5702785 x l) (@lem5702798 x l)). Qed.
Lemma lem5702800 (x : int) (l : int) : (term57 l x) = (term546 x l).
Proof. exact (TRANS (@lem5702782 x l) (@lem5702799 x l)). Qed.
Lemma lem5702802 (y : int) (x : int) : (term57 x y) = (term58 y x).
Proof. exact (proj1 (@lem2841542 x y)). Qed.
Lemma lem5702803 (r : int) (x : int) : (term57 x r) = (term58 r x).
Proof. exact (@lem5702802 r x). Qed.
Lemma lem5702805 (x : int) (y : int) : (int_le x y) = (term61 x y).
Proof. exact (EQ_MP (@lem2841616 x y) (@lem2841615 x y)). Qed.
Lemma lem5702806 (r : int) (x : int) : (term58 r x) = (term540 r x).
Proof. exact (@lem5702805 (term541 r) x). Qed.
Lemma lem5702808 (x : int) (y : int) : (term64 x y) = (term65 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem5702809 (r : int) : (term542 r) = (term543 r).
Proof. exact (@lem5702808 r term68). Qed.
Lemma lem5702811 (n : nat) : (term73 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem5702812 : term74 = term75.
Proof. exact (@lem5702811 term76). Qed.
Lemma lem5702813 (r : int) : (term143 r) = (term143 r).
Proof. exact (eq_refl (term143 r)). Qed.
Lemma lem5702814 (r : int) : (term543 r) = (term104 r).
Proof. exact (MK_COMB (@lem5702813 r) (@lem5702812)). Qed.
Lemma lem5702815 (r : int) : (term542 r) = (term104 r).
Proof. exact (TRANS (@lem5702809 r) (@lem5702814 r)). Qed.
Lemma lem5702816 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5702817 (r : int) : (term544 r) = (term545 r).
Proof. exact (MK_COMB (@lem5702816) (@lem5702815 r)). Qed.
Lemma lem5702818 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem5702819 (r : int) (x : int) : (term540 r x) = (term546 r x).
Proof. exact (MK_COMB (@lem5702817 r) (@lem5702818 x)). Qed.
Lemma lem5702820 (r : int) (x : int) : (term58 r x) = (term546 r x).
Proof. exact (TRANS (@lem5702806 r x) (@lem5702819 r x)). Qed.
Lemma lem5702821 (r : int) (x : int) : (term57 x r) = (term546 r x).
Proof. exact (TRANS (@lem5702803 r x) (@lem5702820 r x)). Qed.
Lemma lem5702822 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5702823 (x : int) (l : int) : (term548 l x) = (term549 x l).
Proof. exact (MK_COMB (@lem5702822) (@lem5702800 x l)). Qed.
Lemma lem5702824 (l : int) (r : int) (x : int) : (term526 l x r) = (term550 l r x).
Proof. exact (MK_COMB (@lem5702823 x l) (@lem5702821 r x)). Qed.
Lemma lem5702825 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5702826 (l : int) (x : int) (r : int) : (term527 l x r) = (term551 l x r).
Proof. exact (MK_COMB (@lem5702825) (@lem5702779 l x r)). Qed.
Lemma lem5702827 (l : int) (r : int) (x : int) : (term529 l x r) = (term552 l r x).
Proof. exact (MK_COMB (@lem5702826 l x r) (@lem5702824 l r x)). Qed.
Lemma lem5702828 (l : int) (r : int) : (term538 l r) = (term553 l r).
Proof. exact (fun_ext (fun x : int => @lem5702827 l r x)). Qed.
Lemma lem5702829 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem5702830 (l : int) (r : int) : (term539 l r) = (term554 l r).
Proof. exact (MK_COMB (@lem5702829) (@lem5702828 l r)). Qed.
Lemma lem5702831 (l : int) (r : int) : (term533 l r) = (term554 l r).
Proof. exact (TRANS (@lem5702750 l r) (@lem5702830 l r)). Qed.
Lemma lem5702835 (t : Prop) : (term88 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5702891 (l : int) (r : int) : (term555 l r) = (term554 l r).
Proof. exact (@lem5702835 (term554 l r)). Qed.
Lemma lem5702904 (l : int) (r : int) (x : int) : (term552 l r x) = (term552 l r x).
Proof. exact (eq_refl (term552 l r x)). Qed.
Lemma lem5702905 (l : int) (r : int) : (term553 l r) = (term553 l r).
Proof. exact (fun_ext (fun x : int => @lem5702904 l r x)). Qed.
Lemma lem5702906 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem5702907 (l : int) (r : int) : (term554 l r) = (term554 l r).
Proof. exact (MK_COMB (@lem5702906) (@lem5702905 l r)). Qed.
Lemma lem5702908 (l : int) (r : int) : (term555 l r) = (term554 l r).
Proof. exact (TRANS (@lem5702891 l r) (@lem5702907 l r)). Qed.
Lemma lem5702921 (l : int) (r : int) (x : int) : (term552 l r x) = (term552 l r x).
Proof. exact (eq_refl (term552 l r x)). Qed.
Lemma lem5702922 (l : int) (r : int) : (term553 l r) = (term553 l r).
Proof. exact (fun_ext (fun x : int => @lem5702921 l r x)). Qed.
Lemma lem5702923 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem5702924 (l : int) (r : int) : (term554 l r) = (term554 l r).
Proof. exact (MK_COMB (@lem5702923) (@lem5702922 l r)). Qed.
Lemma lem5702925 (l : int) (r : int) : (term555 l r) = (term554 l r).
Proof. exact (TRANS (@lem5702908 l r) (@lem5702924 l r)). Qed.
Lemma lem5702926 (x : int) (l : int) : (term61 l x) = (term150 x l).
Proof. exact (@lem1988287 (real_of_int x) (real_of_int l)). Qed.
Lemma lem5702932 (x : int) (l : int) : (term70 x l) = (term91 x l).
Proof. exact (@lem1982792 (real_of_int x) (real_of_int l)). Qed.
Lemma lem5702937 (l : int) (x : int) : (term91 x l) = (term92 l x).
Proof. exact (@lem1982761 (term93 l) (real_of_int x)). Qed.
Lemma lem5702939 (l : int) (x : int) : (term70 x l) = (term92 l x).
Proof. exact (TRANS (@lem5702932 x l) (@lem5702937 l x)). Qed.
Lemma lem5702940 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5702941 (l : int) (x : int) : (term151 x l) = (term152 l x).
Proof. exact (MK_COMB (@lem5702940) (@lem5702939 l x)). Qed.
Lemma lem5702942 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem5702943 (l : int) (x : int) : (term150 x l) = (term153 l x).
Proof. exact (MK_COMB (@lem5702941 l x) (@lem5702942)). Qed.
Lemma lem5702944 (l : int) (x : int) : (term61 l x) = (term153 l x).
Proof. exact (TRANS (@lem5702926 x l) (@lem5702943 l x)). Qed.
Lemma lem5702945 (r : int) (x : int) : (term546 x r) = (term556 r x).
Proof. exact (@lem1988287 (real_of_int r) (term104 x)). Qed.
Lemma lem5702957 (r : int) (x : int) : (term557 r x) = (term558 r x).
Proof. exact (@lem1982792 (real_of_int r) (term104 x)). Qed.
Lemma lem5702958 (x : int) : (term105 x) = (term106 x).
Proof. exact (@lem1982781 (real_of_int x) term103 term75). Qed.
Lemma lem5702960 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5702961 : term75 = term108.
Proof. exact (@lem5702960 term76). Qed.
Lemma lem5702963 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5702964 : term103 = term111.
Proof. exact (@lem5702963 term76). Qed.
Lemma lem5702965 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5702966 : term112 = term113.
Proof. exact (MK_COMB (@lem5702965) (@lem5702964)). Qed.
Lemma lem5702967 : term114 = term115.
Proof. exact (MK_COMB (@lem5702966) (@lem5702961)). Qed.
Lemma lem5702968 : term115 = term116.
Proof. exact (@lem1981613 term103 term75 term75 term75). Qed.
Lemma lem5702970 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5702971 : term119 = term120.
Proof. exact (@lem5702970 term76 term76). Qed.
Lemma lem5702972 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5702973 : term122 = term76.
Proof. exact (EQ_MP (@lem5702972) (@lem940073)). Qed.
Lemma lem5702974 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5702975 : term120 = term75.
Proof. exact (MK_COMB (@lem5702974) (@lem5702973)). Qed.
Lemma lem5702976 : term119 = term75.
Proof. exact (TRANS (@lem5702971) (@lem5702975)). Qed.
Lemma lem5702978 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5702979 : term114 = term125.
Proof. exact (@lem5702978 term76 term76). Qed.
Lemma lem5702980 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5702981 : term122 = term76.
Proof. exact (EQ_MP (@lem5702980) (@lem940073)). Qed.
Lemma lem5702982 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5702983 : term120 = term75.
Proof. exact (MK_COMB (@lem5702982) (@lem5702981)). Qed.
Lemma lem5702984 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5702985 : term125 = term103.
Proof. exact (MK_COMB (@lem5702984) (@lem5702983)). Qed.
Lemma lem5702986 : term114 = term103.
Proof. exact (TRANS (@lem5702979) (@lem5702985)). Qed.
Lemma lem5702987 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5702988 : term126 = term127.
Proof. exact (MK_COMB (@lem5702987) (@lem5702986)). Qed.
Lemma lem5702989 : term116 = term111.
Proof. exact (MK_COMB (@lem5702988) (@lem5702976)). Qed.
Lemma lem5702990 : term115 = term111.
Proof. exact (TRANS (@lem5702968) (@lem5702989)). Qed.
Lemma lem5702991 : term114 = term111.
Proof. exact (TRANS (@lem5702967) (@lem5702990)). Qed.
Lemma lem5702993 (x : real) : (term128 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5702994 : term111 = term103.
Proof. exact (@lem5702993 term103). Qed.
Lemma lem5702995 : term114 = term103.
Proof. exact (TRANS (@lem5702991) (@lem5702994)). Qed.
Lemma lem5702998 (x : int) : (term129 x) = (term129 x).
Proof. exact (eq_refl (term129 x)). Qed.
Lemma lem5702999 (x : int) : (term106 x) = (term130 x).
Proof. exact (MK_COMB (@lem5702998 x) (@lem5702995)). Qed.
Lemma lem5703000 (x : int) : (term105 x) = (term130 x).
Proof. exact (TRANS (@lem5702958 x) (@lem5702999 x)). Qed.
Lemma lem5703001 (r : int) : (term143 r) = (term143 r).
Proof. exact (eq_refl (term143 r)). Qed.
Lemma lem5703004 (r : int) (x : int) : (term558 r x) = (term144 r x).
Proof. exact (MK_COMB (@lem5703001 r) (@lem5703000 x)). Qed.
Lemma lem5703006 (r : int) (x : int) : (term557 r x) = (term144 r x).
Proof. exact (TRANS (@lem5702957 r x) (@lem5703004 r x)). Qed.
Lemma lem5703007 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5703008 (r : int) (x : int) : (term559 r x) = (term148 r x).
Proof. exact (MK_COMB (@lem5703007) (@lem5703006 r x)). Qed.
Lemma lem5703009 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem5703010 (r : int) (x : int) : (term556 r x) = (term149 r x).
Proof. exact (MK_COMB (@lem5703008 r x) (@lem5703009)). Qed.
Lemma lem5703011 (r : int) (x : int) : (term546 x r) = (term149 r x).
Proof. exact (TRANS (@lem5702945 r x) (@lem5703010 r x)). Qed.
Lemma lem5703012 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5703013 (l : int) (x : int) : (term84 l x) = (term156 l x).
Proof. exact (MK_COMB (@lem5703012) (@lem5702944 l x)). Qed.
Lemma lem5703014 (l : int) (r : int) (x : int) : (term547 l x r) = (term560 l r x).
Proof. exact (MK_COMB (@lem5703013 l x) (@lem5703011 r x)). Qed.
Lemma lem5703015 (l : int) (x : int) : (term546 x l) = (term556 l x).
Proof. exact (@lem1988287 (real_of_int l) (term104 x)). Qed.
Lemma lem5703027 (l : int) (x : int) : (term557 l x) = (term558 l x).
Proof. exact (@lem1982792 (real_of_int l) (term104 x)). Qed.
Lemma lem5703028 (x : int) : (term105 x) = (term106 x).
Proof. exact (@lem1982781 (real_of_int x) term103 term75). Qed.
Lemma lem5703030 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5703031 : term75 = term108.
Proof. exact (@lem5703030 term76). Qed.
Lemma lem5703033 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5703034 : term103 = term111.
Proof. exact (@lem5703033 term76). Qed.
Lemma lem5703035 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5703036 : term112 = term113.
Proof. exact (MK_COMB (@lem5703035) (@lem5703034)). Qed.
Lemma lem5703037 : term114 = term115.
Proof. exact (MK_COMB (@lem5703036) (@lem5703031)). Qed.
Lemma lem5703038 : term115 = term116.
Proof. exact (@lem1981613 term103 term75 term75 term75). Qed.
Lemma lem5703040 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5703041 : term119 = term120.
Proof. exact (@lem5703040 term76 term76). Qed.
Lemma lem5703042 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5703043 : term122 = term76.
Proof. exact (EQ_MP (@lem5703042) (@lem940073)). Qed.
Lemma lem5703044 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5703045 : term120 = term75.
Proof. exact (MK_COMB (@lem5703044) (@lem5703043)). Qed.
Lemma lem5703046 : term119 = term75.
Proof. exact (TRANS (@lem5703041) (@lem5703045)). Qed.
Lemma lem5703048 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5703049 : term114 = term125.
Proof. exact (@lem5703048 term76 term76). Qed.
Lemma lem5703050 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5703051 : term122 = term76.
Proof. exact (EQ_MP (@lem5703050) (@lem940073)). Qed.
Lemma lem5703052 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5703053 : term120 = term75.
Proof. exact (MK_COMB (@lem5703052) (@lem5703051)). Qed.
Lemma lem5703054 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5703055 : term125 = term103.
Proof. exact (MK_COMB (@lem5703054) (@lem5703053)). Qed.
Lemma lem5703056 : term114 = term103.
Proof. exact (TRANS (@lem5703049) (@lem5703055)). Qed.
Lemma lem5703057 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5703058 : term126 = term127.
Proof. exact (MK_COMB (@lem5703057) (@lem5703056)). Qed.
Lemma lem5703059 : term116 = term111.
Proof. exact (MK_COMB (@lem5703058) (@lem5703046)). Qed.
Lemma lem5703060 : term115 = term111.
Proof. exact (TRANS (@lem5703038) (@lem5703059)). Qed.
Lemma lem5703061 : term114 = term111.
Proof. exact (TRANS (@lem5703037) (@lem5703060)). Qed.
Lemma lem5703063 (x : real) : (term128 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5703064 : term111 = term103.
Proof. exact (@lem5703063 term103). Qed.
Lemma lem5703065 : term114 = term103.
Proof. exact (TRANS (@lem5703061) (@lem5703064)). Qed.
Lemma lem5703068 (x : int) : (term129 x) = (term129 x).
Proof. exact (eq_refl (term129 x)). Qed.
Lemma lem5703069 (x : int) : (term106 x) = (term130 x).
Proof. exact (MK_COMB (@lem5703068 x) (@lem5703065)). Qed.
Lemma lem5703070 (x : int) : (term105 x) = (term130 x).
Proof. exact (TRANS (@lem5703028 x) (@lem5703069 x)). Qed.
Lemma lem5703071 (l : int) : (term143 l) = (term143 l).
Proof. exact (eq_refl (term143 l)). Qed.
Lemma lem5703074 (l : int) (x : int) : (term558 l x) = (term144 l x).
Proof. exact (MK_COMB (@lem5703071 l) (@lem5703070 x)). Qed.
Lemma lem5703076 (l : int) (x : int) : (term557 l x) = (term144 l x).
Proof. exact (TRANS (@lem5703027 l x) (@lem5703074 l x)). Qed.
Lemma lem5703077 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5703078 (l : int) (x : int) : (term559 l x) = (term148 l x).
Proof. exact (MK_COMB (@lem5703077) (@lem5703076 l x)). Qed.
Lemma lem5703079 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem5703080 (l : int) (x : int) : (term556 l x) = (term149 l x).
Proof. exact (MK_COMB (@lem5703078 l x) (@lem5703079)). Qed.
Lemma lem5703081 (l : int) (x : int) : (term546 x l) = (term149 l x).
Proof. exact (TRANS (@lem5703015 l x) (@lem5703080 l x)). Qed.
Lemma lem5703082 (x : int) (r : int) : (term546 r x) = (term556 x r).
Proof. exact (@lem1988287 (real_of_int x) (term104 r)). Qed.
Lemma lem5703094 (x : int) (r : int) : (term557 x r) = (term558 x r).
Proof. exact (@lem1982792 (real_of_int x) (term104 r)). Qed.
Lemma lem5703095 (r : int) : (term105 r) = (term106 r).
Proof. exact (@lem1982781 (real_of_int r) term103 term75). Qed.
Lemma lem5703097 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5703098 : term75 = term108.
Proof. exact (@lem5703097 term76). Qed.
Lemma lem5703100 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5703101 : term103 = term111.
Proof. exact (@lem5703100 term76). Qed.
Lemma lem5703102 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5703103 : term112 = term113.
Proof. exact (MK_COMB (@lem5703102) (@lem5703101)). Qed.
Lemma lem5703104 : term114 = term115.
Proof. exact (MK_COMB (@lem5703103) (@lem5703098)). Qed.
Lemma lem5703105 : term115 = term116.
Proof. exact (@lem1981613 term103 term75 term75 term75). Qed.
Lemma lem5703107 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5703108 : term119 = term120.
Proof. exact (@lem5703107 term76 term76). Qed.
Lemma lem5703109 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5703110 : term122 = term76.
Proof. exact (EQ_MP (@lem5703109) (@lem940073)). Qed.
Lemma lem5703111 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5703112 : term120 = term75.
Proof. exact (MK_COMB (@lem5703111) (@lem5703110)). Qed.
Lemma lem5703113 : term119 = term75.
Proof. exact (TRANS (@lem5703108) (@lem5703112)). Qed.
Lemma lem5703115 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5703116 : term114 = term125.
Proof. exact (@lem5703115 term76 term76). Qed.
Lemma lem5703117 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5703118 : term122 = term76.
Proof. exact (EQ_MP (@lem5703117) (@lem940073)). Qed.
Lemma lem5703119 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5703120 : term120 = term75.
Proof. exact (MK_COMB (@lem5703119) (@lem5703118)). Qed.
Lemma lem5703121 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5703122 : term125 = term103.
Proof. exact (MK_COMB (@lem5703121) (@lem5703120)). Qed.
Lemma lem5703123 : term114 = term103.
Proof. exact (TRANS (@lem5703116) (@lem5703122)). Qed.
Lemma lem5703124 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5703125 : term126 = term127.
Proof. exact (MK_COMB (@lem5703124) (@lem5703123)). Qed.
Lemma lem5703126 : term116 = term111.
Proof. exact (MK_COMB (@lem5703125) (@lem5703113)). Qed.
Lemma lem5703127 : term115 = term111.
Proof. exact (TRANS (@lem5703105) (@lem5703126)). Qed.
Lemma lem5703128 : term114 = term111.
Proof. exact (TRANS (@lem5703104) (@lem5703127)). Qed.
Lemma lem5703130 (x : real) : (term128 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5703131 : term111 = term103.
Proof. exact (@lem5703130 term103). Qed.
Lemma lem5703132 : term114 = term103.
Proof. exact (TRANS (@lem5703128) (@lem5703131)). Qed.
Lemma lem5703135 (r : int) : (term129 r) = (term129 r).
Proof. exact (eq_refl (term129 r)). Qed.
Lemma lem5703136 (r : int) : (term106 r) = (term130 r).
Proof. exact (MK_COMB (@lem5703135 r) (@lem5703132)). Qed.
Lemma lem5703137 (r : int) : (term105 r) = (term130 r).
Proof. exact (TRANS (@lem5703095 r) (@lem5703136 r)). Qed.
Lemma lem5703138 (x : int) : (term143 x) = (term143 x).
Proof. exact (eq_refl (term143 x)). Qed.
Lemma lem5703139 (x : int) (r : int) : (term558 x r) = (term144 x r).
Proof. exact (MK_COMB (@lem5703138 x) (@lem5703137 r)). Qed.
Lemma lem5703144 (r : int) (x : int) : (term144 x r) = (term561 r x).
Proof. exact (@lem1982757 (term93 r) (real_of_int x) term103). Qed.
Lemma lem5703145 (r : int) (x : int) : (term558 x r) = (term561 r x).
Proof. exact (TRANS (@lem5703139 x r) (@lem5703144 r x)). Qed.
Lemma lem5703147 (r : int) (x : int) : (term557 x r) = (term561 r x).
Proof. exact (TRANS (@lem5703094 x r) (@lem5703145 r x)). Qed.
Lemma lem5703148 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5703149 (r : int) (x : int) : (term559 x r) = (term562 r x).
Proof. exact (MK_COMB (@lem5703148) (@lem5703147 r x)). Qed.
Lemma lem5703150 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem5703151 (r : int) (x : int) : (term556 x r) = (term563 r x).
Proof. exact (MK_COMB (@lem5703149 r x) (@lem5703150)). Qed.
Lemma lem5703152 (r : int) (x : int) : (term546 r x) = (term563 r x).
Proof. exact (TRANS (@lem5703082 x r) (@lem5703151 r x)). Qed.
Lemma lem5703153 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5703154 (l : int) (x : int) : (term549 x l) = (term564 l x).
Proof. exact (MK_COMB (@lem5703153) (@lem5703081 l x)). Qed.
Lemma lem5703155 (l : int) (r : int) (x : int) : (term550 l r x) = (term565 l r x).
Proof. exact (MK_COMB (@lem5703154 l x) (@lem5703152 r x)). Qed.
Lemma lem5703156 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5703157 (l : int) (r : int) (x : int) : (term551 l x r) = (term566 l r x).
Proof. exact (MK_COMB (@lem5703156) (@lem5703014 l r x)). Qed.
Lemma lem5703158 (l : int) (r : int) (x : int) : (term552 l r x) = (term567 l r x).
Proof. exact (MK_COMB (@lem5703157 l r x) (@lem5703155 l r x)). Qed.
Lemma lem5703159 (l : int) (r : int) : (term553 l r) = (term568 l r).
Proof. exact (fun_ext (fun x : int => @lem5703158 l r x)). Qed.
Lemma lem5703160 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem5703161 (l : int) (r : int) : (term554 l r) = (term569 l r).
Proof. exact (MK_COMB (@lem5703160) (@lem5703159 l r)). Qed.
Lemma lem5703216 (l : int) (r : int) : (term555 l r) = (term569 l r).
Proof. exact (TRANS (@lem5702925 l r) (@lem5703161 l r)). Qed.
Lemma lem5703239 (l : int) (r : int) (x : int) : (term567 l r x) = (term570 l r x).
Proof. exact (@lem19158 (term149 l x) (term560 l r x) (term563 r x)). Qed.
Lemma lem5703240 (l : int) (r : int) : (term568 l r) = (term571 l r).
Proof. exact (fun_ext (fun x : int => @lem5703239 l r x)). Qed.
Lemma lem5703241 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem5703242 (l : int) (r : int) : (term569 l r) = (term572 l r).
Proof. exact (MK_COMB (@lem5703241) (@lem5703240 l r)). Qed.
Lemma lem5703243 (l : int) (r : int) : (term555 l r) = (term572 l r).
Proof. exact (TRANS (@lem5703216 l r) (@lem5703242 l r)). Qed.
Lemma lem5703253 (l : int) (r : int) (x : int) (h1 : term570 l r x) : term570 l r x.
Proof. exact (h1). Qed.
Lemma lem5703254 (r : int) (l : int) (x : int) (h1 : term573 r l x) : term573 r l x.
Proof. exact (h1). Qed.
Lemma lem5703255 (r : int) (l : int) (x : int) (h1 : term573 r l x) : term149 l x.
Proof. exact (proj2 (@lem5703254 r l x h1)). Qed.
Lemma lem5703256 (r : int) (l : int) (x : int) (h1 : term573 r l x) : term560 l r x.
Proof. exact (proj1 (@lem5703254 r l x h1)). Qed.
Lemma lem5703258 (r : int) (l : int) (x : int) (h1 : term573 r l x) : term153 l x.
Proof. exact (proj1 (@lem5703256 r l x h1)). Qed.
Lemma lem5703260 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5703261 : term160 = term161.
Proof. exact (@lem5703260 term81 term75). Qed.
Lemma lem5703263 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5703264 : term75 = term108.
Proof. exact (@lem5703263 term76). Qed.
Lemma lem5703266 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5703267 : term81 = term162.
Proof. exact (@lem5703266 (NUMERAL 0)). Qed.
Lemma lem5703268 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5703269 : term163 = term164.
Proof. exact (MK_COMB (@lem5703268) (@lem5703267)). Qed.
Lemma lem5703270 : term161 = term165.
Proof. exact (MK_COMB (@lem5703269) (@lem5703264)). Qed.
Lemma lem5703271 : term166.
Proof. exact (@lem1980255 term81 term75 term75 term75). Qed.
Lemma lem5703273 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5703274 : term161 = term168.
Proof. exact (@lem5703273 (NUMERAL 0) term76). Qed.
Lemma lem5703275 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5703276 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5703277 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5703276 h1) (fun h1 : term168 = True => @lem5703275)). Qed.
Lemma lem5703278 : term168 = True.
Proof. exact (EQ_MP (@lem5703277) (@lem5703275)). Qed.
Lemma lem5703279 : term161 = True.
Proof. exact (TRANS (@lem5703274) (@lem5703278)). Qed.
Lemma lem5703280 : True = term161.
Proof. exact (SYM (@lem5703279)). Qed.
Lemma lem5703281 : term161.
Proof. exact (EQ_MP (@lem5703280) (@lem0)). Qed.
Lemma lem5703282 : term170.
Proof. exact (@lem5703271 (@lem5703281)). Qed.
Lemma lem5703284 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5703285 : term161 = term168.
Proof. exact (@lem5703284 (NUMERAL 0) term76). Qed.
Lemma lem5703286 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5703287 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5703288 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5703287 h1) (fun h1 : term168 = True => @lem5703286)). Qed.
Lemma lem5703289 : term168 = True.
Proof. exact (EQ_MP (@lem5703288) (@lem5703286)). Qed.
Lemma lem5703290 : term161 = True.
Proof. exact (TRANS (@lem5703285) (@lem5703289)). Qed.
Lemma lem5703291 : True = term161.
Proof. exact (SYM (@lem5703290)). Qed.
Lemma lem5703292 : term161.
Proof. exact (EQ_MP (@lem5703291) (@lem0)). Qed.
Lemma lem5703293 : term165 = term171.
Proof. exact (@lem5703282 (@lem5703292)). Qed.
Lemma lem5703295 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5703296 : term119 = term120.
Proof. exact (@lem5703295 term76 term76). Qed.
Lemma lem5703297 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5703298 : term122 = term76.
Proof. exact (EQ_MP (@lem5703297) (@lem940073)). Qed.
Lemma lem5703299 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5703300 : term120 = term75.
Proof. exact (MK_COMB (@lem5703299) (@lem5703298)). Qed.
Lemma lem5703301 : term119 = term75.
Proof. exact (TRANS (@lem5703296) (@lem5703300)). Qed.
Lemma lem5703303 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5703304 : term173 = term81.
Proof. exact (@lem5703303 term76). Qed.
Lemma lem5703305 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5703306 : term174 = term163.
Proof. exact (MK_COMB (@lem5703305) (@lem5703304)). Qed.
Lemma lem5703307 : term171 = term161.
Proof. exact (MK_COMB (@lem5703306) (@lem5703301)). Qed.
Lemma lem5703309 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5703310 : term161 = term168.
Proof. exact (@lem5703309 (NUMERAL 0) term76). Qed.
Lemma lem5703311 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5703312 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5703313 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5703312 h1) (fun h1 : term168 = True => @lem5703311)). Qed.
Lemma lem5703314 : term168 = True.
Proof. exact (EQ_MP (@lem5703313) (@lem5703311)). Qed.
Lemma lem5703315 : term161 = True.
Proof. exact (TRANS (@lem5703310) (@lem5703314)). Qed.
Lemma lem5703316 : term171 = True.
Proof. exact (TRANS (@lem5703307) (@lem5703315)). Qed.
Lemma lem5703317 : term165 = True.
Proof. exact (TRANS (@lem5703293) (@lem5703316)). Qed.
Lemma lem5703318 : term161 = True.
Proof. exact (TRANS (@lem5703270) (@lem5703317)). Qed.
Lemma lem5703319 : term160 = True.
Proof. exact (TRANS (@lem5703261) (@lem5703318)). Qed.
Lemma lem5703320 : True = term160.
Proof. exact (SYM (@lem5703319)). Qed.
Lemma lem5703321 : term160.
Proof. exact (EQ_MP (@lem5703320) (@lem0)). Qed.
Lemma lem5703322 (r : int) (l : int) (x : int) (h1 : term573 r l x) : term217 l x.
Proof. exact (conj (@lem5703321) (@lem5703258 r l x h1)). Qed.
Lemma lem5703324 (x : real) (y : real) : term176 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5703325 (l : int) (x : int) : term218 l x.
Proof. exact (@lem5703324 term75 (term92 l x)). Qed.
Lemma lem5703326 (r : int) (l : int) (x : int) (h1 : term573 r l x) : term219 l x.
Proof. exact (@lem5703325 l x (@lem5703322 r l x h1)). Qed.
Lemma lem5703327 (l : int) (x : int) : (term220 l x) = (term92 l x).
Proof. exact (@lem1982733 (term92 l x)). Qed.
Lemma lem5703328 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5703329 (l : int) (x : int) : (term221 l x) = (term152 l x).
Proof. exact (MK_COMB (@lem5703328) (@lem5703327 l x)). Qed.
Lemma lem5703330 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem5703331 (l : int) (x : int) : (term219 l x) = (term153 l x).
Proof. exact (MK_COMB (@lem5703329 l x) (@lem5703330)). Qed.
Lemma lem5703332 (r : int) (l : int) (x : int) (h1 : term573 r l x) : term153 l x.
Proof. exact (EQ_MP (@lem5703331 l x) (@lem5703326 r l x h1)). Qed.
Lemma lem5703334 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5703335 : term160 = term161.
Proof. exact (@lem5703334 term81 term75). Qed.
Lemma lem5703337 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5703338 : term75 = term108.
Proof. exact (@lem5703337 term76). Qed.
Lemma lem5703340 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5703341 : term81 = term162.
Proof. exact (@lem5703340 (NUMERAL 0)). Qed.
Lemma lem5703342 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5703343 : term163 = term164.
Proof. exact (MK_COMB (@lem5703342) (@lem5703341)). Qed.
Lemma lem5703344 : term161 = term165.
Proof. exact (MK_COMB (@lem5703343) (@lem5703338)). Qed.
Lemma lem5703345 : term166.
Proof. exact (@lem1980255 term81 term75 term75 term75). Qed.
Lemma lem5703347 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5703348 : term161 = term168.
Proof. exact (@lem5703347 (NUMERAL 0) term76). Qed.
Lemma lem5703349 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5703350 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5703351 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5703350 h1) (fun h1 : term168 = True => @lem5703349)). Qed.
Lemma lem5703352 : term168 = True.
Proof. exact (EQ_MP (@lem5703351) (@lem5703349)). Qed.
Lemma lem5703353 : term161 = True.
Proof. exact (TRANS (@lem5703348) (@lem5703352)). Qed.
Lemma lem5703354 : True = term161.
Proof. exact (SYM (@lem5703353)). Qed.
Lemma lem5703355 : term161.
Proof. exact (EQ_MP (@lem5703354) (@lem0)). Qed.
Lemma lem5703356 : term170.
Proof. exact (@lem5703345 (@lem5703355)). Qed.
Lemma lem5703358 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5703359 : term161 = term168.
Proof. exact (@lem5703358 (NUMERAL 0) term76). Qed.
Lemma lem5703360 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5703361 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5703362 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5703361 h1) (fun h1 : term168 = True => @lem5703360)). Qed.
Lemma lem5703363 : term168 = True.
Proof. exact (EQ_MP (@lem5703362) (@lem5703360)). Qed.
Lemma lem5703364 : term161 = True.
Proof. exact (TRANS (@lem5703359) (@lem5703363)). Qed.
Lemma lem5703365 : True = term161.
Proof. exact (SYM (@lem5703364)). Qed.
Lemma lem5703366 : term161.
Proof. exact (EQ_MP (@lem5703365) (@lem0)). Qed.
Lemma lem5703367 : term165 = term171.
Proof. exact (@lem5703356 (@lem5703366)). Qed.
Lemma lem5703369 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5703370 : term119 = term120.
Proof. exact (@lem5703369 term76 term76). Qed.
Lemma lem5703371 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5703372 : term122 = term76.
Proof. exact (EQ_MP (@lem5703371) (@lem940073)). Qed.
Lemma lem5703373 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5703374 : term120 = term75.
Proof. exact (MK_COMB (@lem5703373) (@lem5703372)). Qed.
Lemma lem5703375 : term119 = term75.
Proof. exact (TRANS (@lem5703370) (@lem5703374)). Qed.
Lemma lem5703377 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5703378 : term173 = term81.
Proof. exact (@lem5703377 term76). Qed.
Lemma lem5703379 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5703380 : term174 = term163.
Proof. exact (MK_COMB (@lem5703379) (@lem5703378)). Qed.
Lemma lem5703381 : term171 = term161.
Proof. exact (MK_COMB (@lem5703380) (@lem5703375)). Qed.
Lemma lem5703383 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5703384 : term161 = term168.
Proof. exact (@lem5703383 (NUMERAL 0) term76). Qed.
Lemma lem5703385 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5703386 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5703387 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5703386 h1) (fun h1 : term168 = True => @lem5703385)). Qed.
Lemma lem5703388 : term168 = True.
Proof. exact (EQ_MP (@lem5703387) (@lem5703385)). Qed.
Lemma lem5703389 : term161 = True.
Proof. exact (TRANS (@lem5703384) (@lem5703388)). Qed.
Lemma lem5703390 : term171 = True.
Proof. exact (TRANS (@lem5703381) (@lem5703389)). Qed.
Lemma lem5703391 : term165 = True.
Proof. exact (TRANS (@lem5703367) (@lem5703390)). Qed.
Lemma lem5703392 : term161 = True.
Proof. exact (TRANS (@lem5703344) (@lem5703391)). Qed.
Lemma lem5703393 : term160 = True.
Proof. exact (TRANS (@lem5703335) (@lem5703392)). Qed.
Lemma lem5703394 : True = term160.
Proof. exact (SYM (@lem5703393)). Qed.
Lemma lem5703395 : term160.
Proof. exact (EQ_MP (@lem5703394) (@lem0)). Qed.
Lemma lem5703396 (r : int) (l : int) (x : int) (h1 : term573 r l x) : term181 l x.
Proof. exact (conj (@lem5703395) (@lem5703255 r l x h1)). Qed.
Lemma lem5703398 (x : real) (y : real) : term176 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5703399 (l : int) (x : int) : term182 l x.
Proof. exact (@lem5703398 term75 (term144 l x)). Qed.
Lemma lem5703400 (r : int) (l : int) (x : int) (h1 : term573 r l x) : term183 l x.
Proof. exact (@lem5703399 l x (@lem5703396 r l x h1)). Qed.
Lemma lem5703401 (l : int) (x : int) : (term184 l x) = (term144 l x).
Proof. exact (@lem1982733 (term144 l x)). Qed.
Lemma lem5703402 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5703403 (l : int) (x : int) : (term185 l x) = (term148 l x).
Proof. exact (MK_COMB (@lem5703402) (@lem5703401 l x)). Qed.
Lemma lem5703404 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem5703405 (l : int) (x : int) : (term183 l x) = (term149 l x).
Proof. exact (MK_COMB (@lem5703403 l x) (@lem5703404)). Qed.
Lemma lem5703406 (r : int) (l : int) (x : int) (h1 : term573 r l x) : term149 l x.
Proof. exact (EQ_MP (@lem5703405 l x) (@lem5703400 r l x h1)). Qed.
Lemma lem5703407 (r : int) (l : int) (x : int) (h1 : term573 r l x) : term574 l x.
Proof. exact (conj (@lem5703406 r l x h1) (@lem5703332 r l x h1)). Qed.
Lemma lem5703409 (x : real) (y : real) : term187 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5703410 (l : int) (x : int) : term575 l x.
Proof. exact (@lem5703409 (term144 l x) (term92 l x)). Qed.
Lemma lem5703411 (r : int) (l : int) (x : int) (h1 : term573 r l x) : term576 l x.
Proof. exact (@lem5703410 l x (@lem5703407 r l x h1)). Qed.
Lemma lem5703412 (l : int) (x : int) : (term577 l x) = (term578 l x).
Proof. exact (@lem1982753 (real_of_int l) (term93 l) (term130 x) (real_of_int x)). Qed.
Lemma lem5703413 (l : int) : (term229 l) = (term195 l).
Proof. exact (@lem1982715 term103 (real_of_int l)). Qed.
Lemma lem5703415 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5703416 : term75 = term108.
Proof. exact (@lem5703415 term76). Qed.
Lemma lem5703418 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5703419 : term103 = term111.
Proof. exact (@lem5703418 term76). Qed.
Lemma lem5703420 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5703421 : term196 = term197.
Proof. exact (MK_COMB (@lem5703420) (@lem5703419)). Qed.
Lemma lem5703422 : term198 = term199.
Proof. exact (MK_COMB (@lem5703421) (@lem5703416)). Qed.
Lemma lem5703423 : term200.
Proof. exact (@lem1981473 term103 term75 term75 term75 term81 term75). Qed.
Lemma lem5703425 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5703426 : term161 = term168.
Proof. exact (@lem5703425 (NUMERAL 0) term76). Qed.
Lemma lem5703427 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5703428 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5703429 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5703428 h1) (fun h1 : term168 = True => @lem5703427)). Qed.
Lemma lem5703430 : term168 = True.
Proof. exact (EQ_MP (@lem5703429) (@lem5703427)). Qed.
Lemma lem5703431 : term161 = True.
Proof. exact (TRANS (@lem5703426) (@lem5703430)). Qed.
Lemma lem5703432 : True = term161.
Proof. exact (SYM (@lem5703431)). Qed.
Lemma lem5703433 : term161.
Proof. exact (EQ_MP (@lem5703432) (@lem0)). Qed.
Lemma lem5703434 : term201.
Proof. exact (@lem5703423 (@lem5703433)). Qed.
Lemma lem5703436 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5703437 : term161 = term168.
Proof. exact (@lem5703436 (NUMERAL 0) term76). Qed.
Lemma lem5703438 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5703439 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5703440 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5703439 h1) (fun h1 : term168 = True => @lem5703438)). Qed.
Lemma lem5703441 : term168 = True.
Proof. exact (EQ_MP (@lem5703440) (@lem5703438)). Qed.
Lemma lem5703442 : term161 = True.
Proof. exact (TRANS (@lem5703437) (@lem5703441)). Qed.
Lemma lem5703443 : True = term161.
Proof. exact (SYM (@lem5703442)). Qed.
Lemma lem5703444 : term161.
Proof. exact (EQ_MP (@lem5703443) (@lem0)). Qed.
Lemma lem5703445 : term202.
Proof. exact (@lem5703434 (@lem5703444)). Qed.
Lemma lem5703447 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5703448 : term161 = term168.
Proof. exact (@lem5703447 (NUMERAL 0) term76). Qed.
Lemma lem5703449 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5703450 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5703451 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5703450 h1) (fun h1 : term168 = True => @lem5703449)). Qed.
Lemma lem5703452 : term168 = True.
Proof. exact (EQ_MP (@lem5703451) (@lem5703449)). Qed.
Lemma lem5703453 : term161 = True.
Proof. exact (TRANS (@lem5703448) (@lem5703452)). Qed.
Lemma lem5703454 : True = term161.
Proof. exact (SYM (@lem5703453)). Qed.
Lemma lem5703455 : term161.
Proof. exact (EQ_MP (@lem5703454) (@lem0)). Qed.
Lemma lem5703456 : term203.
Proof. exact (@lem5703445 (@lem5703455)). Qed.
Lemma lem5703458 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5703459 : term119 = term120.
Proof. exact (@lem5703458 term76 term76). Qed.
Lemma lem5703460 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5703461 : term122 = term76.
Proof. exact (EQ_MP (@lem5703460) (@lem940073)). Qed.
Lemma lem5703462 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5703463 : term120 = term75.
Proof. exact (MK_COMB (@lem5703462) (@lem5703461)). Qed.
Lemma lem5703464 : term119 = term75.
Proof. exact (TRANS (@lem5703459) (@lem5703463)). Qed.
Lemma lem5703466 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5703467 : term114 = term125.
Proof. exact (@lem5703466 term76 term76). Qed.
Lemma lem5703468 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5703469 : term122 = term76.
Proof. exact (EQ_MP (@lem5703468) (@lem940073)). Qed.
Lemma lem5703470 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5703471 : term120 = term75.
Proof. exact (MK_COMB (@lem5703470) (@lem5703469)). Qed.
Lemma lem5703472 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5703473 : term125 = term103.
Proof. exact (MK_COMB (@lem5703472) (@lem5703471)). Qed.
Lemma lem5703474 : term114 = term103.
Proof. exact (TRANS (@lem5703467) (@lem5703473)). Qed.
Lemma lem5703475 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5703476 : term204 = term196.
Proof. exact (MK_COMB (@lem5703475) (@lem5703474)). Qed.
Lemma lem5703477 : term205 = term198.
Proof. exact (MK_COMB (@lem5703476) (@lem5703464)). Qed.
Lemma lem5703479 (m : nat) : (term206 m) = term81.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5703480 : term198 = term81.
Proof. exact (@lem5703479 term76). Qed.
Lemma lem5703481 : term205 = term81.
Proof. exact (TRANS (@lem5703477) (@lem5703480)). Qed.
Lemma lem5703482 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5703483 : term207 = term208.
Proof. exact (MK_COMB (@lem5703482) (@lem5703481)). Qed.
Lemma lem5703484 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem5703485 : term209 = term173.
Proof. exact (MK_COMB (@lem5703483) (@lem5703484)). Qed.
Lemma lem5703487 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5703488 : term173 = term81.
Proof. exact (@lem5703487 term76). Qed.
Lemma lem5703489 : term209 = term81.
Proof. exact (TRANS (@lem5703485) (@lem5703488)). Qed.
Lemma lem5703491 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5703492 : term119 = term120.
Proof. exact (@lem5703491 term76 term76). Qed.
Lemma lem5703493 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5703494 : term122 = term76.
Proof. exact (EQ_MP (@lem5703493) (@lem940073)). Qed.
Lemma lem5703495 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5703496 : term120 = term75.
Proof. exact (MK_COMB (@lem5703495) (@lem5703494)). Qed.
Lemma lem5703497 : term119 = term75.
Proof. exact (TRANS (@lem5703492) (@lem5703496)). Qed.
Lemma lem5703498 : term208 = term208.
Proof. exact (eq_refl term208). Qed.
Lemma lem5703499 : term210 = term173.
Proof. exact (MK_COMB (@lem5703498) (@lem5703497)). Qed.
Lemma lem5703501 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5703502 : term173 = term81.
Proof. exact (@lem5703501 term76). Qed.
Lemma lem5703503 : term210 = term81.
Proof. exact (TRANS (@lem5703499) (@lem5703502)). Qed.
Lemma lem5703504 : term81 = term210.
Proof. exact (SYM (@lem5703503)). Qed.
Lemma lem5703505 : term209 = term210.
Proof. exact (TRANS (@lem5703489) (@lem5703504)). Qed.
Lemma lem5703506 : term199 = term162.
Proof. exact (@lem5703456 (@lem5703505)). Qed.
Lemma lem5703507 : term198 = term162.
Proof. exact (TRANS (@lem5703422) (@lem5703506)). Qed.
Lemma lem5703509 (x : real) : (term128 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5703510 : term162 = term81.
Proof. exact (@lem5703509 term81). Qed.
Lemma lem5703511 : term198 = term81.
Proof. exact (TRANS (@lem5703507) (@lem5703510)). Qed.
Lemma lem5703512 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5703513 : term211 = term208.
Proof. exact (MK_COMB (@lem5703512) (@lem5703511)). Qed.
Lemma lem5703514 (l : int) : (real_of_int l) = (real_of_int l).
Proof. exact (eq_refl (real_of_int l)). Qed.
Lemma lem5703515 (l : int) : (term195 l) = (term212 l).
Proof. exact (MK_COMB (@lem5703513) (@lem5703514 l)). Qed.
Lemma lem5703516 (l : int) : (term229 l) = (term212 l).
Proof. exact (TRANS (@lem5703413 l) (@lem5703515 l)). Qed.
Lemma lem5703517 (l : int) : (term212 l) = term81.
Proof. exact (@lem1982719 (real_of_int l)). Qed.
Lemma lem5703518 (l : int) : (term229 l) = term81.
Proof. exact (TRANS (@lem5703516 l) (@lem5703517 l)). Qed.
Lemma lem5703519 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5703520 (l : int) : (term230 l) = term145.
Proof. exact (MK_COMB (@lem5703519) (@lem5703518 l)). Qed.
Lemma lem5703521 (x : int) : (term579 x) = (term580 x).
Proof. exact (@lem1982759 (term93 x) (real_of_int x) term103). Qed.
Lemma lem5703522 (x : int) : (term194 x) = (term195 x).
Proof. exact (@lem1982713 term103 (real_of_int x)). Qed.
Lemma lem5703524 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5703525 : term75 = term108.
Proof. exact (@lem5703524 term76). Qed.
Lemma lem5703527 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5703528 : term103 = term111.
Proof. exact (@lem5703527 term76). Qed.
Lemma lem5703529 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5703530 : term196 = term197.
Proof. exact (MK_COMB (@lem5703529) (@lem5703528)). Qed.
Lemma lem5703531 : term198 = term199.
Proof. exact (MK_COMB (@lem5703530) (@lem5703525)). Qed.
Lemma lem5703532 : term200.
Proof. exact (@lem1981473 term103 term75 term75 term75 term81 term75). Qed.
Lemma lem5703534 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5703535 : term161 = term168.
Proof. exact (@lem5703534 (NUMERAL 0) term76). Qed.
Lemma lem5703536 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5703537 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5703538 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5703537 h1) (fun h1 : term168 = True => @lem5703536)). Qed.
Lemma lem5703539 : term168 = True.
Proof. exact (EQ_MP (@lem5703538) (@lem5703536)). Qed.
Lemma lem5703540 : term161 = True.
Proof. exact (TRANS (@lem5703535) (@lem5703539)). Qed.
Lemma lem5703541 : True = term161.
Proof. exact (SYM (@lem5703540)). Qed.
Lemma lem5703542 : term161.
Proof. exact (EQ_MP (@lem5703541) (@lem0)). Qed.
Lemma lem5703543 : term201.
Proof. exact (@lem5703532 (@lem5703542)). Qed.
Lemma lem5703545 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5703546 : term161 = term168.
Proof. exact (@lem5703545 (NUMERAL 0) term76). Qed.
Lemma lem5703547 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5703548 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5703549 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5703548 h1) (fun h1 : term168 = True => @lem5703547)). Qed.
Lemma lem5703550 : term168 = True.
Proof. exact (EQ_MP (@lem5703549) (@lem5703547)). Qed.
Lemma lem5703551 : term161 = True.
Proof. exact (TRANS (@lem5703546) (@lem5703550)). Qed.
Lemma lem5703552 : True = term161.
Proof. exact (SYM (@lem5703551)). Qed.
Lemma lem5703553 : term161.
Proof. exact (EQ_MP (@lem5703552) (@lem0)). Qed.
Lemma lem5703554 : term202.
Proof. exact (@lem5703543 (@lem5703553)). Qed.
Lemma lem5703556 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5703557 : term161 = term168.
Proof. exact (@lem5703556 (NUMERAL 0) term76). Qed.
Lemma lem5703558 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5703559 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5703560 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5703559 h1) (fun h1 : term168 = True => @lem5703558)). Qed.
Lemma lem5703561 : term168 = True.
Proof. exact (EQ_MP (@lem5703560) (@lem5703558)). Qed.
Lemma lem5703562 : term161 = True.
Proof. exact (TRANS (@lem5703557) (@lem5703561)). Qed.
Lemma lem5703563 : True = term161.
Proof. exact (SYM (@lem5703562)). Qed.
Lemma lem5703564 : term161.
Proof. exact (EQ_MP (@lem5703563) (@lem0)). Qed.
Lemma lem5703565 : term203.
Proof. exact (@lem5703554 (@lem5703564)). Qed.
Lemma lem5703567 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5703568 : term119 = term120.
Proof. exact (@lem5703567 term76 term76). Qed.
Lemma lem5703569 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5703570 : term122 = term76.
Proof. exact (EQ_MP (@lem5703569) (@lem940073)). Qed.
Lemma lem5703571 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5703572 : term120 = term75.
Proof. exact (MK_COMB (@lem5703571) (@lem5703570)). Qed.
Lemma lem5703573 : term119 = term75.
Proof. exact (TRANS (@lem5703568) (@lem5703572)). Qed.
Lemma lem5703575 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5703576 : term114 = term125.
Proof. exact (@lem5703575 term76 term76). Qed.
Lemma lem5703577 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5703578 : term122 = term76.
Proof. exact (EQ_MP (@lem5703577) (@lem940073)). Qed.
Lemma lem5703579 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5703580 : term120 = term75.
Proof. exact (MK_COMB (@lem5703579) (@lem5703578)). Qed.
Lemma lem5703581 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5703582 : term125 = term103.
Proof. exact (MK_COMB (@lem5703581) (@lem5703580)). Qed.
Lemma lem5703583 : term114 = term103.
Proof. exact (TRANS (@lem5703576) (@lem5703582)). Qed.
Lemma lem5703584 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5703585 : term204 = term196.
Proof. exact (MK_COMB (@lem5703584) (@lem5703583)). Qed.
Lemma lem5703586 : term205 = term198.
Proof. exact (MK_COMB (@lem5703585) (@lem5703573)). Qed.
Lemma lem5703588 (m : nat) : (term206 m) = term81.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5703589 : term198 = term81.
Proof. exact (@lem5703588 term76). Qed.
Lemma lem5703590 : term205 = term81.
Proof. exact (TRANS (@lem5703586) (@lem5703589)). Qed.
Lemma lem5703591 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5703592 : term207 = term208.
Proof. exact (MK_COMB (@lem5703591) (@lem5703590)). Qed.
Lemma lem5703593 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem5703594 : term209 = term173.
Proof. exact (MK_COMB (@lem5703592) (@lem5703593)). Qed.
Lemma lem5703596 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5703597 : term173 = term81.
Proof. exact (@lem5703596 term76). Qed.
Lemma lem5703598 : term209 = term81.
Proof. exact (TRANS (@lem5703594) (@lem5703597)). Qed.
Lemma lem5703600 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5703601 : term119 = term120.
Proof. exact (@lem5703600 term76 term76). Qed.
Lemma lem5703602 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5703603 : term122 = term76.
Proof. exact (EQ_MP (@lem5703602) (@lem940073)). Qed.
Lemma lem5703604 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5703605 : term120 = term75.
Proof. exact (MK_COMB (@lem5703604) (@lem5703603)). Qed.
Lemma lem5703606 : term119 = term75.
Proof. exact (TRANS (@lem5703601) (@lem5703605)). Qed.
Lemma lem5703607 : term208 = term208.
Proof. exact (eq_refl term208). Qed.
Lemma lem5703608 : term210 = term173.
Proof. exact (MK_COMB (@lem5703607) (@lem5703606)). Qed.
Lemma lem5703610 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5703611 : term173 = term81.
Proof. exact (@lem5703610 term76). Qed.
Lemma lem5703612 : term210 = term81.
Proof. exact (TRANS (@lem5703608) (@lem5703611)). Qed.
Lemma lem5703613 : term81 = term210.
Proof. exact (SYM (@lem5703612)). Qed.
Lemma lem5703614 : term209 = term210.
Proof. exact (TRANS (@lem5703598) (@lem5703613)). Qed.
Lemma lem5703615 : term199 = term162.
Proof. exact (@lem5703565 (@lem5703614)). Qed.
Lemma lem5703616 : term198 = term162.
Proof. exact (TRANS (@lem5703531) (@lem5703615)). Qed.
Lemma lem5703618 (x : real) : (term128 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5703619 : term162 = term81.
Proof. exact (@lem5703618 term81). Qed.
Lemma lem5703620 : term198 = term81.
Proof. exact (TRANS (@lem5703616) (@lem5703619)). Qed.
Lemma lem5703621 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5703622 : term211 = term208.
Proof. exact (MK_COMB (@lem5703621) (@lem5703620)). Qed.
Lemma lem5703623 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem5703624 (x : int) : (term195 x) = (term212 x).
Proof. exact (MK_COMB (@lem5703622) (@lem5703623 x)). Qed.
Lemma lem5703625 (x : int) : (term194 x) = (term212 x).
Proof. exact (TRANS (@lem5703522 x) (@lem5703624 x)). Qed.
Lemma lem5703626 (x : int) : (term212 x) = term81.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem5703627 (x : int) : (term194 x) = term81.
Proof. exact (TRANS (@lem5703625 x) (@lem5703626 x)). Qed.
Lemma lem5703628 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5703629 (x : int) : (term213 x) = term145.
Proof. exact (MK_COMB (@lem5703628) (@lem5703627 x)). Qed.
Lemma lem5703630 : term103 = term103.
Proof. exact (eq_refl term103). Qed.
Lemma lem5703631 (x : int) : (term580 x) = term231.
Proof. exact (MK_COMB (@lem5703629 x) (@lem5703630)). Qed.
Lemma lem5703632 (x : int) : (term579 x) = term231.
Proof. exact (TRANS (@lem5703521 x) (@lem5703631 x)). Qed.
Lemma lem5703633 : term231 = term103.
Proof. exact (@lem1982721 term103). Qed.
Lemma lem5703634 (x : int) : (term579 x) = term103.
Proof. exact (TRANS (@lem5703632 x) (@lem5703633)). Qed.
Lemma lem5703635 (l : int) (x : int) : (term578 l x) = term231.
Proof. exact (MK_COMB (@lem5703520 l) (@lem5703634 x)). Qed.
Lemma lem5703636 (l : int) (x : int) : (term577 l x) = term231.
Proof. exact (TRANS (@lem5703412 l x) (@lem5703635 l x)). Qed.
Lemma lem5703637 : term231 = term103.
Proof. exact (@lem1982721 term103). Qed.
Lemma lem5703638 (l : int) (x : int) : (term577 l x) = term103.
Proof. exact (TRANS (@lem5703636 l x) (@lem5703637)). Qed.
Lemma lem5703639 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5703640 (l : int) (x : int) : (term581 l x) = term233.
Proof. exact (MK_COMB (@lem5703639) (@lem5703638 l x)). Qed.
Lemma lem5703641 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem5703642 (l : int) (x : int) : (term576 l x) = term234.
Proof. exact (MK_COMB (@lem5703640 l x) (@lem5703641)). Qed.
Lemma lem5703643 (r : int) (l : int) (x : int) (h1 : term573 r l x) : term234.
Proof. exact (EQ_MP (@lem5703642 l x) (@lem5703411 r l x h1)). Qed.
Lemma lem5703645 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5703646 : term234 = term235.
Proof. exact (@lem5703645 term81 term103). Qed.
Lemma lem5703648 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5703649 : term103 = term111.
Proof. exact (@lem5703648 term76). Qed.
Lemma lem5703651 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5703652 : term81 = term162.
Proof. exact (@lem5703651 (NUMERAL 0)). Qed.
Lemma lem5703653 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5703654 : term236 = term237.
Proof. exact (MK_COMB (@lem5703653) (@lem5703652)). Qed.
Lemma lem5703655 : term235 = term238.
Proof. exact (MK_COMB (@lem5703654) (@lem5703649)). Qed.
Lemma lem5703656 : term239.
Proof. exact (@lem1980026 term81 term75 term103 term75). Qed.
Lemma lem5703658 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5703659 : term161 = term168.
Proof. exact (@lem5703658 (NUMERAL 0) term76). Qed.
Lemma lem5703660 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5703661 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5703662 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5703661 h1) (fun h1 : term168 = True => @lem5703660)). Qed.
Lemma lem5703663 : term168 = True.
Proof. exact (EQ_MP (@lem5703662) (@lem5703660)). Qed.
Lemma lem5703664 : term161 = True.
Proof. exact (TRANS (@lem5703659) (@lem5703663)). Qed.
Lemma lem5703665 : True = term161.
Proof. exact (SYM (@lem5703664)). Qed.
Lemma lem5703666 : term161.
Proof. exact (EQ_MP (@lem5703665) (@lem0)). Qed.
Lemma lem5703667 : term240.
Proof. exact (@lem5703656 (@lem5703666)). Qed.
Lemma lem5703669 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5703670 : term161 = term168.
Proof. exact (@lem5703669 (NUMERAL 0) term76). Qed.
Lemma lem5703671 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5703672 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5703673 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5703672 h1) (fun h1 : term168 = True => @lem5703671)). Qed.
Lemma lem5703674 : term168 = True.
Proof. exact (EQ_MP (@lem5703673) (@lem5703671)). Qed.
Lemma lem5703675 : term161 = True.
Proof. exact (TRANS (@lem5703670) (@lem5703674)). Qed.
Lemma lem5703676 : True = term161.
Proof. exact (SYM (@lem5703675)). Qed.
Lemma lem5703677 : term161.
Proof. exact (EQ_MP (@lem5703676) (@lem0)). Qed.
Lemma lem5703678 : term238 = term241.
Proof. exact (@lem5703667 (@lem5703677)). Qed.
Lemma lem5703680 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5703681 : term114 = term125.
Proof. exact (@lem5703680 term76 term76). Qed.
Lemma lem5703682 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5703683 : term122 = term76.
Proof. exact (EQ_MP (@lem5703682) (@lem940073)). Qed.
Lemma lem5703684 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5703685 : term120 = term75.
Proof. exact (MK_COMB (@lem5703684) (@lem5703683)). Qed.
Lemma lem5703686 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5703687 : term125 = term103.
Proof. exact (MK_COMB (@lem5703686) (@lem5703685)). Qed.
Lemma lem5703688 : term114 = term103.
Proof. exact (TRANS (@lem5703681) (@lem5703687)). Qed.
Lemma lem5703690 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5703691 : term173 = term81.
Proof. exact (@lem5703690 term76). Qed.
Lemma lem5703692 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5703693 : term242 = term236.
Proof. exact (MK_COMB (@lem5703692) (@lem5703691)). Qed.
Lemma lem5703694 : term241 = term235.
Proof. exact (MK_COMB (@lem5703693) (@lem5703688)). Qed.
Lemma lem5703696 (m : nat) (n : nat) : (term243 m n) = (term244 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5703697 : term235 = term245.
Proof. exact (@lem5703696 (NUMERAL 0) term76). Qed.
Lemma lem5703698 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5703699 (h1 : term169 = (BIT1 0)) : (term76 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5703700 : (term169 = (BIT1 0)) = ((term76 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5703699 h1) (fun h1 : (term76 = (NUMERAL 0)) = False => @lem5703698)). Qed.
Lemma lem5703701 : (term76 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5703700) (@lem5703698)). Qed.
Lemma lem5703702 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5703703 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5703704 : term246 = (and True).
Proof. exact (MK_COMB (@lem5703703) (@lem5703702)). Qed.
Lemma lem5703705 : term245 = (True /\ False).
Proof. exact (MK_COMB (@lem5703704) (@lem5703701)). Qed.
Lemma lem5703707 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5703708 : term245 = False.
Proof. exact (TRANS (@lem5703705) (@lem5703707)). Qed.
Lemma lem5703709 : term235 = False.
Proof. exact (TRANS (@lem5703697) (@lem5703708)). Qed.
Lemma lem5703710 : term241 = False.
Proof. exact (TRANS (@lem5703694) (@lem5703709)). Qed.
Lemma lem5703711 : term238 = False.
Proof. exact (TRANS (@lem5703678) (@lem5703710)). Qed.
Lemma lem5703712 : term235 = False.
Proof. exact (TRANS (@lem5703655) (@lem5703711)). Qed.
Lemma lem5703713 : term234 = False.
Proof. exact (TRANS (@lem5703646) (@lem5703712)). Qed.
Lemma lem5703714 (r : int) (l : int) (x : int) (h1 : term573 r l x) : False.
Proof. exact (EQ_MP (@lem5703713) (@lem5703643 r l x h1)). Qed.
Lemma lem5703715 (l : int) (r : int) (x : int) (h1 : term582 l r x) : term582 l r x.
Proof. exact (h1). Qed.
Lemma lem5703716 (l : int) (r : int) (x : int) (h1 : term582 l r x) : term563 r x.
Proof. exact (proj2 (@lem5703715 l r x h1)). Qed.
Lemma lem5703717 (l : int) (r : int) (x : int) (h1 : term582 l r x) : term560 l r x.
Proof. exact (proj1 (@lem5703715 l r x h1)). Qed.
Lemma lem5703718 (l : int) (r : int) (x : int) (h1 : term582 l r x) : term149 r x.
Proof. exact (proj2 (@lem5703717 l r x h1)). Qed.
Lemma lem5703721 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5703722 : term160 = term161.
Proof. exact (@lem5703721 term81 term75). Qed.
Lemma lem5703724 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5703725 : term75 = term108.
Proof. exact (@lem5703724 term76). Qed.
Lemma lem5703727 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5703728 : term81 = term162.
Proof. exact (@lem5703727 (NUMERAL 0)). Qed.
Lemma lem5703729 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5703730 : term163 = term164.
Proof. exact (MK_COMB (@lem5703729) (@lem5703728)). Qed.
Lemma lem5703731 : term161 = term165.
Proof. exact (MK_COMB (@lem5703730) (@lem5703725)). Qed.
Lemma lem5703732 : term166.
Proof. exact (@lem1980255 term81 term75 term75 term75). Qed.
Lemma lem5703734 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5703735 : term161 = term168.
Proof. exact (@lem5703734 (NUMERAL 0) term76). Qed.
Lemma lem5703736 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5703737 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5703738 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5703737 h1) (fun h1 : term168 = True => @lem5703736)). Qed.
Lemma lem5703739 : term168 = True.
Proof. exact (EQ_MP (@lem5703738) (@lem5703736)). Qed.
Lemma lem5703740 : term161 = True.
Proof. exact (TRANS (@lem5703735) (@lem5703739)). Qed.
Lemma lem5703741 : True = term161.
Proof. exact (SYM (@lem5703740)). Qed.
Lemma lem5703742 : term161.
Proof. exact (EQ_MP (@lem5703741) (@lem0)). Qed.
Lemma lem5703743 : term170.
Proof. exact (@lem5703732 (@lem5703742)). Qed.
Lemma lem5703745 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5703746 : term161 = term168.
Proof. exact (@lem5703745 (NUMERAL 0) term76). Qed.
Lemma lem5703747 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5703748 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5703749 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5703748 h1) (fun h1 : term168 = True => @lem5703747)). Qed.
Lemma lem5703750 : term168 = True.
Proof. exact (EQ_MP (@lem5703749) (@lem5703747)). Qed.
Lemma lem5703751 : term161 = True.
Proof. exact (TRANS (@lem5703746) (@lem5703750)). Qed.
Lemma lem5703752 : True = term161.
Proof. exact (SYM (@lem5703751)). Qed.
Lemma lem5703753 : term161.
Proof. exact (EQ_MP (@lem5703752) (@lem0)). Qed.
Lemma lem5703754 : term165 = term171.
Proof. exact (@lem5703743 (@lem5703753)). Qed.
Lemma lem5703756 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5703757 : term119 = term120.
Proof. exact (@lem5703756 term76 term76). Qed.
Lemma lem5703758 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5703759 : term122 = term76.
Proof. exact (EQ_MP (@lem5703758) (@lem940073)). Qed.
Lemma lem5703760 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5703761 : term120 = term75.
Proof. exact (MK_COMB (@lem5703760) (@lem5703759)). Qed.
Lemma lem5703762 : term119 = term75.
Proof. exact (TRANS (@lem5703757) (@lem5703761)). Qed.
Lemma lem5703764 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5703765 : term173 = term81.
Proof. exact (@lem5703764 term76). Qed.
Lemma lem5703766 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5703767 : term174 = term163.
Proof. exact (MK_COMB (@lem5703766) (@lem5703765)). Qed.
Lemma lem5703768 : term171 = term161.
Proof. exact (MK_COMB (@lem5703767) (@lem5703762)). Qed.
Lemma lem5703770 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5703771 : term161 = term168.
Proof. exact (@lem5703770 (NUMERAL 0) term76). Qed.
Lemma lem5703772 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5703773 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5703774 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5703773 h1) (fun h1 : term168 = True => @lem5703772)). Qed.
Lemma lem5703775 : term168 = True.
Proof. exact (EQ_MP (@lem5703774) (@lem5703772)). Qed.
Lemma lem5703776 : term161 = True.
Proof. exact (TRANS (@lem5703771) (@lem5703775)). Qed.
Lemma lem5703777 : term171 = True.
Proof. exact (TRANS (@lem5703768) (@lem5703776)). Qed.
Lemma lem5703778 : term165 = True.
Proof. exact (TRANS (@lem5703754) (@lem5703777)). Qed.
Lemma lem5703779 : term161 = True.
Proof. exact (TRANS (@lem5703731) (@lem5703778)). Qed.
Lemma lem5703780 : term160 = True.
Proof. exact (TRANS (@lem5703722) (@lem5703779)). Qed.
Lemma lem5703781 : True = term160.
Proof. exact (SYM (@lem5703780)). Qed.
Lemma lem5703782 : term160.
Proof. exact (EQ_MP (@lem5703781) (@lem0)). Qed.
Lemma lem5703783 (l : int) (r : int) (x : int) (h1 : term582 l r x) : term583 r x.
Proof. exact (conj (@lem5703782) (@lem5703716 l r x h1)). Qed.
Lemma lem5703785 (x : real) (y : real) : term176 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5703786 (r : int) (x : int) : term584 r x.
Proof. exact (@lem5703785 term75 (term561 r x)). Qed.
Lemma lem5703787 (l : int) (r : int) (x : int) (h1 : term582 l r x) : term585 r x.
Proof. exact (@lem5703786 r x (@lem5703783 l r x h1)). Qed.
Lemma lem5703788 (r : int) (x : int) : (term586 r x) = (term561 r x).
Proof. exact (@lem1982733 (term561 r x)). Qed.
Lemma lem5703789 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5703790 (r : int) (x : int) : (term587 r x) = (term562 r x).
Proof. exact (MK_COMB (@lem5703789) (@lem5703788 r x)). Qed.
Lemma lem5703791 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem5703792 (r : int) (x : int) : (term585 r x) = (term563 r x).
Proof. exact (MK_COMB (@lem5703790 r x) (@lem5703791)). Qed.
Lemma lem5703793 (l : int) (r : int) (x : int) (h1 : term582 l r x) : term563 r x.
Proof. exact (EQ_MP (@lem5703792 r x) (@lem5703787 l r x h1)). Qed.
Lemma lem5703795 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5703796 : term160 = term161.
Proof. exact (@lem5703795 term81 term75). Qed.
Lemma lem5703798 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5703799 : term75 = term108.
Proof. exact (@lem5703798 term76). Qed.
Lemma lem5703801 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5703802 : term81 = term162.
Proof. exact (@lem5703801 (NUMERAL 0)). Qed.
Lemma lem5703803 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5703804 : term163 = term164.
Proof. exact (MK_COMB (@lem5703803) (@lem5703802)). Qed.
Lemma lem5703805 : term161 = term165.
Proof. exact (MK_COMB (@lem5703804) (@lem5703799)). Qed.
Lemma lem5703806 : term166.
Proof. exact (@lem1980255 term81 term75 term75 term75). Qed.
Lemma lem5703808 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5703809 : term161 = term168.
Proof. exact (@lem5703808 (NUMERAL 0) term76). Qed.
Lemma lem5703810 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5703811 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5703812 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5703811 h1) (fun h1 : term168 = True => @lem5703810)). Qed.
Lemma lem5703813 : term168 = True.
Proof. exact (EQ_MP (@lem5703812) (@lem5703810)). Qed.
Lemma lem5703814 : term161 = True.
Proof. exact (TRANS (@lem5703809) (@lem5703813)). Qed.
Lemma lem5703815 : True = term161.
Proof. exact (SYM (@lem5703814)). Qed.
Lemma lem5703816 : term161.
Proof. exact (EQ_MP (@lem5703815) (@lem0)). Qed.
Lemma lem5703817 : term170.
Proof. exact (@lem5703806 (@lem5703816)). Qed.
Lemma lem5703819 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5703820 : term161 = term168.
Proof. exact (@lem5703819 (NUMERAL 0) term76). Qed.
Lemma lem5703821 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5703822 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5703823 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5703822 h1) (fun h1 : term168 = True => @lem5703821)). Qed.
Lemma lem5703824 : term168 = True.
Proof. exact (EQ_MP (@lem5703823) (@lem5703821)). Qed.
Lemma lem5703825 : term161 = True.
Proof. exact (TRANS (@lem5703820) (@lem5703824)). Qed.
Lemma lem5703826 : True = term161.
Proof. exact (SYM (@lem5703825)). Qed.
Lemma lem5703827 : term161.
Proof. exact (EQ_MP (@lem5703826) (@lem0)). Qed.
Lemma lem5703828 : term165 = term171.
Proof. exact (@lem5703817 (@lem5703827)). Qed.
Lemma lem5703830 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5703831 : term119 = term120.
Proof. exact (@lem5703830 term76 term76). Qed.
Lemma lem5703832 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5703833 : term122 = term76.
Proof. exact (EQ_MP (@lem5703832) (@lem940073)). Qed.
Lemma lem5703834 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5703835 : term120 = term75.
Proof. exact (MK_COMB (@lem5703834) (@lem5703833)). Qed.
Lemma lem5703836 : term119 = term75.
Proof. exact (TRANS (@lem5703831) (@lem5703835)). Qed.
Lemma lem5703838 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5703839 : term173 = term81.
Proof. exact (@lem5703838 term76). Qed.
Lemma lem5703840 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5703841 : term174 = term163.
Proof. exact (MK_COMB (@lem5703840) (@lem5703839)). Qed.
Lemma lem5703842 : term171 = term161.
Proof. exact (MK_COMB (@lem5703841) (@lem5703836)). Qed.
Lemma lem5703844 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5703845 : term161 = term168.
Proof. exact (@lem5703844 (NUMERAL 0) term76). Qed.
Lemma lem5703846 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5703847 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5703848 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5703847 h1) (fun h1 : term168 = True => @lem5703846)). Qed.
Lemma lem5703849 : term168 = True.
Proof. exact (EQ_MP (@lem5703848) (@lem5703846)). Qed.
Lemma lem5703850 : term161 = True.
Proof. exact (TRANS (@lem5703845) (@lem5703849)). Qed.
Lemma lem5703851 : term171 = True.
Proof. exact (TRANS (@lem5703842) (@lem5703850)). Qed.
Lemma lem5703852 : term165 = True.
Proof. exact (TRANS (@lem5703828) (@lem5703851)). Qed.
Lemma lem5703853 : term161 = True.
Proof. exact (TRANS (@lem5703805) (@lem5703852)). Qed.
Lemma lem5703854 : term160 = True.
Proof. exact (TRANS (@lem5703796) (@lem5703853)). Qed.
Lemma lem5703855 : True = term160.
Proof. exact (SYM (@lem5703854)). Qed.
Lemma lem5703856 : term160.
Proof. exact (EQ_MP (@lem5703855) (@lem0)). Qed.
Lemma lem5703857 (l : int) (r : int) (x : int) (h1 : term582 l r x) : term181 r x.
Proof. exact (conj (@lem5703856) (@lem5703718 l r x h1)). Qed.
Lemma lem5703859 (x : real) (y : real) : term176 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5703860 (r : int) (x : int) : term182 r x.
Proof. exact (@lem5703859 term75 (term144 r x)). Qed.
Lemma lem5703861 (l : int) (r : int) (x : int) (h1 : term582 l r x) : term183 r x.
Proof. exact (@lem5703860 r x (@lem5703857 l r x h1)). Qed.
Lemma lem5703862 (r : int) (x : int) : (term184 r x) = (term144 r x).
Proof. exact (@lem1982733 (term144 r x)). Qed.
Lemma lem5703863 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5703864 (r : int) (x : int) : (term185 r x) = (term148 r x).
Proof. exact (MK_COMB (@lem5703863) (@lem5703862 r x)). Qed.
Lemma lem5703865 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem5703866 (r : int) (x : int) : (term183 r x) = (term149 r x).
Proof. exact (MK_COMB (@lem5703864 r x) (@lem5703865)). Qed.
Lemma lem5703867 (l : int) (r : int) (x : int) (h1 : term582 l r x) : term149 r x.
Proof. exact (EQ_MP (@lem5703866 r x) (@lem5703861 l r x h1)). Qed.
Lemma lem5703868 (l : int) (r : int) (x : int) (h1 : term582 l r x) : term588 r x.
Proof. exact (conj (@lem5703867 l r x h1) (@lem5703793 l r x h1)). Qed.
Lemma lem5703870 (x : real) (y : real) : term187 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5703871 (r : int) (x : int) : term589 r x.
Proof. exact (@lem5703870 (term144 r x) (term561 r x)). Qed.
Lemma lem5703872 (l : int) (r : int) (x : int) (h1 : term582 l r x) : term590 r x.
Proof. exact (@lem5703871 r x (@lem5703868 l r x h1)). Qed.
Lemma lem5703873 (r : int) (x : int) : (term591 r x) = (term592 r x).
Proof. exact (@lem1982753 (real_of_int r) (term93 r) (term130 x) (term593 x)). Qed.
Lemma lem5703874 (r : int) : (term229 r) = (term195 r).
Proof. exact (@lem1982715 term103 (real_of_int r)). Qed.
Lemma lem5703876 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5703877 : term75 = term108.
Proof. exact (@lem5703876 term76). Qed.
Lemma lem5703879 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5703880 : term103 = term111.
Proof. exact (@lem5703879 term76). Qed.
Lemma lem5703881 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5703882 : term196 = term197.
Proof. exact (MK_COMB (@lem5703881) (@lem5703880)). Qed.
Lemma lem5703883 : term198 = term199.
Proof. exact (MK_COMB (@lem5703882) (@lem5703877)). Qed.
Lemma lem5703884 : term200.
Proof. exact (@lem1981473 term103 term75 term75 term75 term81 term75). Qed.
Lemma lem5703886 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5703887 : term161 = term168.
Proof. exact (@lem5703886 (NUMERAL 0) term76). Qed.
Lemma lem5703888 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5703889 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5703890 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5703889 h1) (fun h1 : term168 = True => @lem5703888)). Qed.
Lemma lem5703891 : term168 = True.
Proof. exact (EQ_MP (@lem5703890) (@lem5703888)). Qed.
Lemma lem5703892 : term161 = True.
Proof. exact (TRANS (@lem5703887) (@lem5703891)). Qed.
Lemma lem5703893 : True = term161.
Proof. exact (SYM (@lem5703892)). Qed.
Lemma lem5703894 : term161.
Proof. exact (EQ_MP (@lem5703893) (@lem0)). Qed.
Lemma lem5703895 : term201.
Proof. exact (@lem5703884 (@lem5703894)). Qed.
Lemma lem5703897 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5703898 : term161 = term168.
Proof. exact (@lem5703897 (NUMERAL 0) term76). Qed.
Lemma lem5703899 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5703900 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5703901 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5703900 h1) (fun h1 : term168 = True => @lem5703899)). Qed.
Lemma lem5703902 : term168 = True.
Proof. exact (EQ_MP (@lem5703901) (@lem5703899)). Qed.
Lemma lem5703903 : term161 = True.
Proof. exact (TRANS (@lem5703898) (@lem5703902)). Qed.
Lemma lem5703904 : True = term161.
Proof. exact (SYM (@lem5703903)). Qed.
Lemma lem5703905 : term161.
Proof. exact (EQ_MP (@lem5703904) (@lem0)). Qed.
Lemma lem5703906 : term202.
Proof. exact (@lem5703895 (@lem5703905)). Qed.
Lemma lem5703908 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5703909 : term161 = term168.
Proof. exact (@lem5703908 (NUMERAL 0) term76). Qed.
Lemma lem5703910 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5703911 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5703912 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5703911 h1) (fun h1 : term168 = True => @lem5703910)). Qed.
Lemma lem5703913 : term168 = True.
Proof. exact (EQ_MP (@lem5703912) (@lem5703910)). Qed.
Lemma lem5703914 : term161 = True.
Proof. exact (TRANS (@lem5703909) (@lem5703913)). Qed.
Lemma lem5703915 : True = term161.
Proof. exact (SYM (@lem5703914)). Qed.
Lemma lem5703916 : term161.
Proof. exact (EQ_MP (@lem5703915) (@lem0)). Qed.
Lemma lem5703917 : term203.
Proof. exact (@lem5703906 (@lem5703916)). Qed.
Lemma lem5703919 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5703920 : term119 = term120.
Proof. exact (@lem5703919 term76 term76). Qed.
Lemma lem5703921 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5703922 : term122 = term76.
Proof. exact (EQ_MP (@lem5703921) (@lem940073)). Qed.
Lemma lem5703923 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5703924 : term120 = term75.
Proof. exact (MK_COMB (@lem5703923) (@lem5703922)). Qed.
Lemma lem5703925 : term119 = term75.
Proof. exact (TRANS (@lem5703920) (@lem5703924)). Qed.
Lemma lem5703927 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5703928 : term114 = term125.
Proof. exact (@lem5703927 term76 term76). Qed.
Lemma lem5703929 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5703930 : term122 = term76.
Proof. exact (EQ_MP (@lem5703929) (@lem940073)). Qed.
Lemma lem5703931 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5703932 : term120 = term75.
Proof. exact (MK_COMB (@lem5703931) (@lem5703930)). Qed.
Lemma lem5703933 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5703934 : term125 = term103.
Proof. exact (MK_COMB (@lem5703933) (@lem5703932)). Qed.
Lemma lem5703935 : term114 = term103.
Proof. exact (TRANS (@lem5703928) (@lem5703934)). Qed.
Lemma lem5703936 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5703937 : term204 = term196.
Proof. exact (MK_COMB (@lem5703936) (@lem5703935)). Qed.
Lemma lem5703938 : term205 = term198.
Proof. exact (MK_COMB (@lem5703937) (@lem5703925)). Qed.
Lemma lem5703940 (m : nat) : (term206 m) = term81.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5703941 : term198 = term81.
Proof. exact (@lem5703940 term76). Qed.
Lemma lem5703942 : term205 = term81.
Proof. exact (TRANS (@lem5703938) (@lem5703941)). Qed.
Lemma lem5703943 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5703944 : term207 = term208.
Proof. exact (MK_COMB (@lem5703943) (@lem5703942)). Qed.
Lemma lem5703945 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem5703946 : term209 = term173.
Proof. exact (MK_COMB (@lem5703944) (@lem5703945)). Qed.
Lemma lem5703948 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5703949 : term173 = term81.
Proof. exact (@lem5703948 term76). Qed.
Lemma lem5703950 : term209 = term81.
Proof. exact (TRANS (@lem5703946) (@lem5703949)). Qed.
Lemma lem5703952 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5703953 : term119 = term120.
Proof. exact (@lem5703952 term76 term76). Qed.
Lemma lem5703954 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5703955 : term122 = term76.
Proof. exact (EQ_MP (@lem5703954) (@lem940073)). Qed.
Lemma lem5703956 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5703957 : term120 = term75.
Proof. exact (MK_COMB (@lem5703956) (@lem5703955)). Qed.
Lemma lem5703958 : term119 = term75.
Proof. exact (TRANS (@lem5703953) (@lem5703957)). Qed.
Lemma lem5703959 : term208 = term208.
Proof. exact (eq_refl term208). Qed.
Lemma lem5703960 : term210 = term173.
Proof. exact (MK_COMB (@lem5703959) (@lem5703958)). Qed.
Lemma lem5703962 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5703963 : term173 = term81.
Proof. exact (@lem5703962 term76). Qed.
Lemma lem5703964 : term210 = term81.
Proof. exact (TRANS (@lem5703960) (@lem5703963)). Qed.
Lemma lem5703965 : term81 = term210.
Proof. exact (SYM (@lem5703964)). Qed.
Lemma lem5703966 : term209 = term210.
Proof. exact (TRANS (@lem5703950) (@lem5703965)). Qed.
Lemma lem5703967 : term199 = term162.
Proof. exact (@lem5703917 (@lem5703966)). Qed.
Lemma lem5703968 : term198 = term162.
Proof. exact (TRANS (@lem5703883) (@lem5703967)). Qed.
Lemma lem5703970 (x : real) : (term128 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5703971 : term162 = term81.
Proof. exact (@lem5703970 term81). Qed.
Lemma lem5703972 : term198 = term81.
Proof. exact (TRANS (@lem5703968) (@lem5703971)). Qed.
Lemma lem5703973 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5703974 : term211 = term208.
Proof. exact (MK_COMB (@lem5703973) (@lem5703972)). Qed.
Lemma lem5703975 (r : int) : (real_of_int r) = (real_of_int r).
Proof. exact (eq_refl (real_of_int r)). Qed.
Lemma lem5703976 (r : int) : (term195 r) = (term212 r).
Proof. exact (MK_COMB (@lem5703974) (@lem5703975 r)). Qed.
Lemma lem5703977 (r : int) : (term229 r) = (term212 r).
Proof. exact (TRANS (@lem5703874 r) (@lem5703976 r)). Qed.
Lemma lem5703978 (r : int) : (term212 r) = term81.
Proof. exact (@lem1982719 (real_of_int r)). Qed.
Lemma lem5703979 (r : int) : (term229 r) = term81.
Proof. exact (TRANS (@lem5703977 r) (@lem5703978 r)). Qed.
Lemma lem5703980 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5703981 (r : int) : (term230 r) = term145.
Proof. exact (MK_COMB (@lem5703980) (@lem5703979 r)). Qed.
Lemma lem5703982 (x : int) : (term594 x) = (term595 x).
Proof. exact (@lem1982753 (term93 x) (real_of_int x) term103 term103). Qed.
Lemma lem5703983 (x : int) : (term194 x) = (term195 x).
Proof. exact (@lem1982713 term103 (real_of_int x)). Qed.
Lemma lem5703985 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5703986 : term75 = term108.
Proof. exact (@lem5703985 term76). Qed.
Lemma lem5703988 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5703989 : term103 = term111.
Proof. exact (@lem5703988 term76). Qed.
Lemma lem5703990 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5703991 : term196 = term197.
Proof. exact (MK_COMB (@lem5703990) (@lem5703989)). Qed.
Lemma lem5703992 : term198 = term199.
Proof. exact (MK_COMB (@lem5703991) (@lem5703986)). Qed.
Lemma lem5703993 : term200.
Proof. exact (@lem1981473 term103 term75 term75 term75 term81 term75). Qed.
Lemma lem5703995 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5703996 : term161 = term168.
Proof. exact (@lem5703995 (NUMERAL 0) term76). Qed.
Lemma lem5703997 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5703998 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5703999 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5703998 h1) (fun h1 : term168 = True => @lem5703997)). Qed.
Lemma lem5704000 : term168 = True.
Proof. exact (EQ_MP (@lem5703999) (@lem5703997)). Qed.
Lemma lem5704001 : term161 = True.
Proof. exact (TRANS (@lem5703996) (@lem5704000)). Qed.
Lemma lem5704002 : True = term161.
Proof. exact (SYM (@lem5704001)). Qed.
Lemma lem5704003 : term161.
Proof. exact (EQ_MP (@lem5704002) (@lem0)). Qed.
Lemma lem5704004 : term201.
Proof. exact (@lem5703993 (@lem5704003)). Qed.
Lemma lem5704006 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5704007 : term161 = term168.
Proof. exact (@lem5704006 (NUMERAL 0) term76). Qed.
Lemma lem5704008 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5704009 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5704010 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5704009 h1) (fun h1 : term168 = True => @lem5704008)). Qed.
Lemma lem5704011 : term168 = True.
Proof. exact (EQ_MP (@lem5704010) (@lem5704008)). Qed.
Lemma lem5704012 : term161 = True.
Proof. exact (TRANS (@lem5704007) (@lem5704011)). Qed.
Lemma lem5704013 : True = term161.
Proof. exact (SYM (@lem5704012)). Qed.
Lemma lem5704014 : term161.
Proof. exact (EQ_MP (@lem5704013) (@lem0)). Qed.
Lemma lem5704015 : term202.
Proof. exact (@lem5704004 (@lem5704014)). Qed.
Lemma lem5704017 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5704018 : term161 = term168.
Proof. exact (@lem5704017 (NUMERAL 0) term76). Qed.
Lemma lem5704019 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5704020 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5704021 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5704020 h1) (fun h1 : term168 = True => @lem5704019)). Qed.
Lemma lem5704022 : term168 = True.
Proof. exact (EQ_MP (@lem5704021) (@lem5704019)). Qed.
Lemma lem5704023 : term161 = True.
Proof. exact (TRANS (@lem5704018) (@lem5704022)). Qed.
Lemma lem5704024 : True = term161.
Proof. exact (SYM (@lem5704023)). Qed.
Lemma lem5704025 : term161.
Proof. exact (EQ_MP (@lem5704024) (@lem0)). Qed.
Lemma lem5704026 : term203.
Proof. exact (@lem5704015 (@lem5704025)). Qed.
Lemma lem5704028 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5704029 : term119 = term120.
Proof. exact (@lem5704028 term76 term76). Qed.
Lemma lem5704030 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5704031 : term122 = term76.
Proof. exact (EQ_MP (@lem5704030) (@lem940073)). Qed.
Lemma lem5704032 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5704033 : term120 = term75.
Proof. exact (MK_COMB (@lem5704032) (@lem5704031)). Qed.
Lemma lem5704034 : term119 = term75.
Proof. exact (TRANS (@lem5704029) (@lem5704033)). Qed.
Lemma lem5704036 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5704037 : term114 = term125.
Proof. exact (@lem5704036 term76 term76). Qed.
Lemma lem5704038 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5704039 : term122 = term76.
Proof. exact (EQ_MP (@lem5704038) (@lem940073)). Qed.
Lemma lem5704040 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5704041 : term120 = term75.
Proof. exact (MK_COMB (@lem5704040) (@lem5704039)). Qed.
Lemma lem5704042 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5704043 : term125 = term103.
Proof. exact (MK_COMB (@lem5704042) (@lem5704041)). Qed.
Lemma lem5704044 : term114 = term103.
Proof. exact (TRANS (@lem5704037) (@lem5704043)). Qed.
Lemma lem5704045 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5704046 : term204 = term196.
Proof. exact (MK_COMB (@lem5704045) (@lem5704044)). Qed.
Lemma lem5704047 : term205 = term198.
Proof. exact (MK_COMB (@lem5704046) (@lem5704034)). Qed.
Lemma lem5704049 (m : nat) : (term206 m) = term81.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5704050 : term198 = term81.
Proof. exact (@lem5704049 term76). Qed.
Lemma lem5704051 : term205 = term81.
Proof. exact (TRANS (@lem5704047) (@lem5704050)). Qed.
Lemma lem5704052 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5704053 : term207 = term208.
Proof. exact (MK_COMB (@lem5704052) (@lem5704051)). Qed.
Lemma lem5704054 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem5704055 : term209 = term173.
Proof. exact (MK_COMB (@lem5704053) (@lem5704054)). Qed.
Lemma lem5704057 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5704058 : term173 = term81.
Proof. exact (@lem5704057 term76). Qed.
Lemma lem5704059 : term209 = term81.
Proof. exact (TRANS (@lem5704055) (@lem5704058)). Qed.
Lemma lem5704061 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5704062 : term119 = term120.
Proof. exact (@lem5704061 term76 term76). Qed.
Lemma lem5704063 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5704064 : term122 = term76.
Proof. exact (EQ_MP (@lem5704063) (@lem940073)). Qed.
Lemma lem5704065 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5704066 : term120 = term75.
Proof. exact (MK_COMB (@lem5704065) (@lem5704064)). Qed.
Lemma lem5704067 : term119 = term75.
Proof. exact (TRANS (@lem5704062) (@lem5704066)). Qed.
Lemma lem5704068 : term208 = term208.
Proof. exact (eq_refl term208). Qed.
Lemma lem5704069 : term210 = term173.
Proof. exact (MK_COMB (@lem5704068) (@lem5704067)). Qed.
Lemma lem5704071 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5704072 : term173 = term81.
Proof. exact (@lem5704071 term76). Qed.
Lemma lem5704073 : term210 = term81.
Proof. exact (TRANS (@lem5704069) (@lem5704072)). Qed.
Lemma lem5704074 : term81 = term210.
Proof. exact (SYM (@lem5704073)). Qed.
Lemma lem5704075 : term209 = term210.
Proof. exact (TRANS (@lem5704059) (@lem5704074)). Qed.
Lemma lem5704076 : term199 = term162.
Proof. exact (@lem5704026 (@lem5704075)). Qed.
Lemma lem5704077 : term198 = term162.
Proof. exact (TRANS (@lem5703992) (@lem5704076)). Qed.
Lemma lem5704079 (x : real) : (term128 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5704080 : term162 = term81.
Proof. exact (@lem5704079 term81). Qed.
Lemma lem5704081 : term198 = term81.
Proof. exact (TRANS (@lem5704077) (@lem5704080)). Qed.
Lemma lem5704082 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5704083 : term211 = term208.
Proof. exact (MK_COMB (@lem5704082) (@lem5704081)). Qed.
Lemma lem5704084 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem5704085 (x : int) : (term195 x) = (term212 x).
Proof. exact (MK_COMB (@lem5704083) (@lem5704084 x)). Qed.
Lemma lem5704086 (x : int) : (term194 x) = (term212 x).
Proof. exact (TRANS (@lem5703983 x) (@lem5704085 x)). Qed.
Lemma lem5704087 (x : int) : (term212 x) = term81.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem5704088 (x : int) : (term194 x) = term81.
Proof. exact (TRANS (@lem5704086 x) (@lem5704087 x)). Qed.
Lemma lem5704089 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5704090 (x : int) : (term213 x) = term145.
Proof. exact (MK_COMB (@lem5704089) (@lem5704088 x)). Qed.
Lemma lem5704092 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5704093 : term103 = term111.
Proof. exact (@lem5704092 term76). Qed.
Lemma lem5704095 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5704096 : term103 = term111.
Proof. exact (@lem5704095 term76). Qed.
Lemma lem5704097 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5704098 : term196 = term197.
Proof. exact (MK_COMB (@lem5704097) (@lem5704096)). Qed.
Lemma lem5704099 : term596 = term597.
Proof. exact (MK_COMB (@lem5704098) (@lem5704093)). Qed.
Lemma lem5704100 : term598.
Proof. exact (@lem1981473 term103 term75 term103 term75 term599 term75). Qed.
Lemma lem5704102 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5704103 : term161 = term168.
Proof. exact (@lem5704102 (NUMERAL 0) term76). Qed.
Lemma lem5704104 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5704105 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5704106 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5704105 h1) (fun h1 : term168 = True => @lem5704104)). Qed.
Lemma lem5704107 : term168 = True.
Proof. exact (EQ_MP (@lem5704106) (@lem5704104)). Qed.
Lemma lem5704108 : term161 = True.
Proof. exact (TRANS (@lem5704103) (@lem5704107)). Qed.
Lemma lem5704109 : True = term161.
Proof. exact (SYM (@lem5704108)). Qed.
Lemma lem5704110 : term161.
Proof. exact (EQ_MP (@lem5704109) (@lem0)). Qed.
Lemma lem5704111 : term600.
Proof. exact (@lem5704100 (@lem5704110)). Qed.
Lemma lem5704113 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5704114 : term161 = term168.
Proof. exact (@lem5704113 (NUMERAL 0) term76). Qed.
Lemma lem5704115 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5704116 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5704117 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5704116 h1) (fun h1 : term168 = True => @lem5704115)). Qed.
Lemma lem5704118 : term168 = True.
Proof. exact (EQ_MP (@lem5704117) (@lem5704115)). Qed.
Lemma lem5704119 : term161 = True.
Proof. exact (TRANS (@lem5704114) (@lem5704118)). Qed.
Lemma lem5704120 : True = term161.
Proof. exact (SYM (@lem5704119)). Qed.
Lemma lem5704121 : term161.
Proof. exact (EQ_MP (@lem5704120) (@lem0)). Qed.
Lemma lem5704122 : term601.
Proof. exact (@lem5704111 (@lem5704121)). Qed.
Lemma lem5704124 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5704125 : term161 = term168.
Proof. exact (@lem5704124 (NUMERAL 0) term76). Qed.
Lemma lem5704126 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5704127 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5704128 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5704127 h1) (fun h1 : term168 = True => @lem5704126)). Qed.
Lemma lem5704129 : term168 = True.
Proof. exact (EQ_MP (@lem5704128) (@lem5704126)). Qed.
Lemma lem5704130 : term161 = True.
Proof. exact (TRANS (@lem5704125) (@lem5704129)). Qed.
Lemma lem5704131 : True = term161.
Proof. exact (SYM (@lem5704130)). Qed.
Lemma lem5704132 : term161.
Proof. exact (EQ_MP (@lem5704131) (@lem0)). Qed.
Lemma lem5704133 : term602.
Proof. exact (@lem5704122 (@lem5704132)). Qed.
Lemma lem5704135 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5704136 : term114 = term125.
Proof. exact (@lem5704135 term76 term76). Qed.
Lemma lem5704137 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5704138 : term122 = term76.
Proof. exact (EQ_MP (@lem5704137) (@lem940073)). Qed.
Lemma lem5704139 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5704140 : term120 = term75.
Proof. exact (MK_COMB (@lem5704139) (@lem5704138)). Qed.
Lemma lem5704141 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5704142 : term125 = term103.
Proof. exact (MK_COMB (@lem5704141) (@lem5704140)). Qed.
Lemma lem5704143 : term114 = term103.
Proof. exact (TRANS (@lem5704136) (@lem5704142)). Qed.
Lemma lem5704145 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5704146 : term114 = term125.
Proof. exact (@lem5704145 term76 term76). Qed.
Lemma lem5704147 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5704148 : term122 = term76.
Proof. exact (EQ_MP (@lem5704147) (@lem940073)). Qed.
Lemma lem5704149 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5704150 : term120 = term75.
Proof. exact (MK_COMB (@lem5704149) (@lem5704148)). Qed.
Lemma lem5704151 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5704152 : term125 = term103.
Proof. exact (MK_COMB (@lem5704151) (@lem5704150)). Qed.
Lemma lem5704153 : term114 = term103.
Proof. exact (TRANS (@lem5704146) (@lem5704152)). Qed.
Lemma lem5704154 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5704155 : term204 = term196.
Proof. exact (MK_COMB (@lem5704154) (@lem5704153)). Qed.
Lemma lem5704156 : term603 = term596.
Proof. exact (MK_COMB (@lem5704155) (@lem5704143)). Qed.
Lemma lem5704157 : term596 = term604.
Proof. exact (@lem1367763 term76 term76). Qed.
Lemma lem5704158 : term605 = term606.
Proof. exact (@lem706885). Qed.
Lemma lem5704159 : (term605 = term606) = (term607 = term608).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term606). Qed.
Lemma lem5704160 : term607 = term608.
Proof. exact (EQ_MP (@lem5704159) (@lem5704158)). Qed.
Lemma lem5704161 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5704162 : term609 = term610.
Proof. exact (MK_COMB (@lem5704161) (@lem5704160)). Qed.
Lemma lem5704163 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5704164 : term604 = term599.
Proof. exact (MK_COMB (@lem5704163) (@lem5704162)). Qed.
Lemma lem5704165 : term596 = term599.
Proof. exact (TRANS (@lem5704157) (@lem5704164)). Qed.
Lemma lem5704166 : term603 = term599.
Proof. exact (TRANS (@lem5704156) (@lem5704165)). Qed.
Lemma lem5704167 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5704168 : term611 = term612.
Proof. exact (MK_COMB (@lem5704167) (@lem5704166)). Qed.
Lemma lem5704169 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem5704170 : term613 = term614.
Proof. exact (MK_COMB (@lem5704168) (@lem5704169)). Qed.
Lemma lem5704172 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5704173 : term614 = term615.
Proof. exact (@lem5704172 term608 term76). Qed.
Lemma lem5704174 : term616 = term606.
Proof. exact (@lem996237 term606). Qed.
Lemma lem5704175 : (term616 = term606) = (term617 = term608).
Proof. exact (@lem1007663 term606 (BIT1 0) term606). Qed.
Lemma lem5704176 : term617 = term608.
Proof. exact (EQ_MP (@lem5704175) (@lem5704174)). Qed.
Lemma lem5704177 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5704178 : term618 = term610.
Proof. exact (MK_COMB (@lem5704177) (@lem5704176)). Qed.
Lemma lem5704179 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5704180 : term615 = term599.
Proof. exact (MK_COMB (@lem5704179) (@lem5704178)). Qed.
Lemma lem5704181 : term614 = term599.
Proof. exact (TRANS (@lem5704173) (@lem5704180)). Qed.
Lemma lem5704182 : term613 = term599.
Proof. exact (TRANS (@lem5704170) (@lem5704181)). Qed.
Lemma lem5704184 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5704185 : term119 = term120.
Proof. exact (@lem5704184 term76 term76). Qed.
Lemma lem5704186 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5704187 : term122 = term76.
Proof. exact (EQ_MP (@lem5704186) (@lem940073)). Qed.
Lemma lem5704188 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5704189 : term120 = term75.
Proof. exact (MK_COMB (@lem5704188) (@lem5704187)). Qed.
Lemma lem5704190 : term119 = term75.
Proof. exact (TRANS (@lem5704185) (@lem5704189)). Qed.
Lemma lem5704191 : term612 = term612.
Proof. exact (eq_refl term612). Qed.
Lemma lem5704192 : term619 = term614.
Proof. exact (MK_COMB (@lem5704191) (@lem5704190)). Qed.
Lemma lem5704194 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5704195 : term614 = term615.
Proof. exact (@lem5704194 term608 term76). Qed.
Lemma lem5704196 : term616 = term606.
Proof. exact (@lem996237 term606). Qed.
Lemma lem5704197 : (term616 = term606) = (term617 = term608).
Proof. exact (@lem1007663 term606 (BIT1 0) term606). Qed.
Lemma lem5704198 : term617 = term608.
Proof. exact (EQ_MP (@lem5704197) (@lem5704196)). Qed.
Lemma lem5704199 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5704200 : term618 = term610.
Proof. exact (MK_COMB (@lem5704199) (@lem5704198)). Qed.
Lemma lem5704201 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5704202 : term615 = term599.
Proof. exact (MK_COMB (@lem5704201) (@lem5704200)). Qed.
Lemma lem5704203 : term614 = term599.
Proof. exact (TRANS (@lem5704195) (@lem5704202)). Qed.
Lemma lem5704204 : term619 = term599.
Proof. exact (TRANS (@lem5704192) (@lem5704203)). Qed.
Lemma lem5704205 : term599 = term619.
Proof. exact (SYM (@lem5704204)). Qed.
Lemma lem5704206 : term613 = term619.
Proof. exact (TRANS (@lem5704182) (@lem5704205)). Qed.
Lemma lem5704207 : term597 = term620.
Proof. exact (@lem5704133 (@lem5704206)). Qed.
Lemma lem5704208 : term596 = term620.
Proof. exact (TRANS (@lem5704099) (@lem5704207)). Qed.
Lemma lem5704210 (x : real) : (term128 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5704211 : term620 = term599.
Proof. exact (@lem5704210 term599). Qed.
Lemma lem5704212 : term596 = term599.
Proof. exact (TRANS (@lem5704208) (@lem5704211)). Qed.
Lemma lem5704213 (x : int) : (term595 x) = term621.
Proof. exact (MK_COMB (@lem5704090 x) (@lem5704212)). Qed.
Lemma lem5704214 (x : int) : (term594 x) = term621.
Proof. exact (TRANS (@lem5703982 x) (@lem5704213 x)). Qed.
Lemma lem5704215 : term621 = term599.
Proof. exact (@lem1982721 term599). Qed.
Lemma lem5704216 (x : int) : (term594 x) = term599.
Proof. exact (TRANS (@lem5704214 x) (@lem5704215)). Qed.
Lemma lem5704217 (r : int) (x : int) : (term592 r x) = term621.
Proof. exact (MK_COMB (@lem5703981 r) (@lem5704216 x)). Qed.
Lemma lem5704218 (r : int) (x : int) : (term591 r x) = term621.
Proof. exact (TRANS (@lem5703873 r x) (@lem5704217 r x)). Qed.
Lemma lem5704219 : term621 = term599.
Proof. exact (@lem1982721 term599). Qed.
Lemma lem5704220 (r : int) (x : int) : (term591 r x) = term599.
Proof. exact (TRANS (@lem5704218 r x) (@lem5704219)). Qed.
Lemma lem5704221 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5704222 (r : int) (x : int) : (term622 r x) = term623.
Proof. exact (MK_COMB (@lem5704221) (@lem5704220 r x)). Qed.
Lemma lem5704223 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem5704224 (r : int) (x : int) : (term590 r x) = term624.
Proof. exact (MK_COMB (@lem5704222 r x) (@lem5704223)). Qed.
Lemma lem5704225 (l : int) (r : int) (x : int) (h1 : term582 l r x) : term624.
Proof. exact (EQ_MP (@lem5704224 r x) (@lem5703872 l r x h1)). Qed.
Lemma lem5704227 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5704228 : term624 = term625.
Proof. exact (@lem5704227 term81 term599). Qed.
Lemma lem5704230 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5704231 : term599 = term620.
Proof. exact (@lem5704230 term608). Qed.
Lemma lem5704233 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5704234 : term81 = term162.
Proof. exact (@lem5704233 (NUMERAL 0)). Qed.
Lemma lem5704235 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5704236 : term236 = term237.
Proof. exact (MK_COMB (@lem5704235) (@lem5704234)). Qed.
Lemma lem5704237 : term625 = term626.
Proof. exact (MK_COMB (@lem5704236) (@lem5704231)). Qed.
Lemma lem5704238 : term627.
Proof. exact (@lem1980026 term81 term75 term599 term75). Qed.
Lemma lem5704240 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5704241 : term161 = term168.
Proof. exact (@lem5704240 (NUMERAL 0) term76). Qed.
Lemma lem5704242 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5704243 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5704244 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5704243 h1) (fun h1 : term168 = True => @lem5704242)). Qed.
Lemma lem5704245 : term168 = True.
Proof. exact (EQ_MP (@lem5704244) (@lem5704242)). Qed.
Lemma lem5704246 : term161 = True.
Proof. exact (TRANS (@lem5704241) (@lem5704245)). Qed.
Lemma lem5704247 : True = term161.
Proof. exact (SYM (@lem5704246)). Qed.
Lemma lem5704248 : term161.
Proof. exact (EQ_MP (@lem5704247) (@lem0)). Qed.
Lemma lem5704249 : term628.
Proof. exact (@lem5704238 (@lem5704248)). Qed.
Lemma lem5704251 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5704252 : term161 = term168.
Proof. exact (@lem5704251 (NUMERAL 0) term76). Qed.
Lemma lem5704253 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5704254 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5704255 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5704254 h1) (fun h1 : term168 = True => @lem5704253)). Qed.
Lemma lem5704256 : term168 = True.
Proof. exact (EQ_MP (@lem5704255) (@lem5704253)). Qed.
Lemma lem5704257 : term161 = True.
Proof. exact (TRANS (@lem5704252) (@lem5704256)). Qed.
Lemma lem5704258 : True = term161.
Proof. exact (SYM (@lem5704257)). Qed.
Lemma lem5704259 : term161.
Proof. exact (EQ_MP (@lem5704258) (@lem0)). Qed.
Lemma lem5704260 : term626 = term629.
Proof. exact (@lem5704249 (@lem5704259)). Qed.
Lemma lem5704262 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5704263 : term614 = term615.
Proof. exact (@lem5704262 term608 term76). Qed.
Lemma lem5704264 : term616 = term606.
Proof. exact (@lem996237 term606). Qed.
Lemma lem5704265 : (term616 = term606) = (term617 = term608).
Proof. exact (@lem1007663 term606 (BIT1 0) term606). Qed.
Lemma lem5704266 : term617 = term608.
Proof. exact (EQ_MP (@lem5704265) (@lem5704264)). Qed.
Lemma lem5704267 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5704268 : term618 = term610.
Proof. exact (MK_COMB (@lem5704267) (@lem5704266)). Qed.
Lemma lem5704269 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5704270 : term615 = term599.
Proof. exact (MK_COMB (@lem5704269) (@lem5704268)). Qed.
Lemma lem5704271 : term614 = term599.
Proof. exact (TRANS (@lem5704263) (@lem5704270)). Qed.
Lemma lem5704273 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5704274 : term173 = term81.
Proof. exact (@lem5704273 term76). Qed.
Lemma lem5704275 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5704276 : term242 = term236.
Proof. exact (MK_COMB (@lem5704275) (@lem5704274)). Qed.
Lemma lem5704277 : term629 = term625.
Proof. exact (MK_COMB (@lem5704276) (@lem5704271)). Qed.
Lemma lem5704279 (m : nat) (n : nat) : (term243 m n) = (term244 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5704280 : term625 = term630.
Proof. exact (@lem5704279 (NUMERAL 0) term608). Qed.
Lemma lem5704281 : term631 = term606.
Proof. exact (@lem912803). Qed.
Lemma lem5704282 (h1 : term631 = term606) : (term608 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term606 h1). Qed.
Lemma lem5704283 : (term631 = term606) = ((term608 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term631 = term606 => @lem5704282 h1) (fun h1 : (term608 = (NUMERAL 0)) = False => @lem5704281)). Qed.
Lemma lem5704284 : (term608 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5704283) (@lem5704281)). Qed.
Lemma lem5704285 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5704286 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5704287 : term246 = (and True).
Proof. exact (MK_COMB (@lem5704286) (@lem5704285)). Qed.
Lemma lem5704288 : term630 = (True /\ False).
Proof. exact (MK_COMB (@lem5704287) (@lem5704284)). Qed.
Lemma lem5704290 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5704291 : term630 = False.
Proof. exact (TRANS (@lem5704288) (@lem5704290)). Qed.
Lemma lem5704292 : term625 = False.
Proof. exact (TRANS (@lem5704280) (@lem5704291)). Qed.
Lemma lem5704293 : term629 = False.
Proof. exact (TRANS (@lem5704277) (@lem5704292)). Qed.
Lemma lem5704294 : term626 = False.
Proof. exact (TRANS (@lem5704260) (@lem5704293)). Qed.
Lemma lem5704295 : term625 = False.
Proof. exact (TRANS (@lem5704237) (@lem5704294)). Qed.
Lemma lem5704296 : term624 = False.
Proof. exact (TRANS (@lem5704228) (@lem5704295)). Qed.
Lemma lem5704297 (l : int) (r : int) (x : int) (h1 : term582 l r x) : False.
Proof. exact (EQ_MP (@lem5704296) (@lem5704225 l r x h1)). Qed.
Lemma lem5704298 (l : int) (r : int) (x : int) (h1 : term570 l r x) : False.
Proof. exact (or_elim (@lem5703253 l r x h1) (fun h0 : term573 r l x => @lem5703714 r l x h0) (fun h0 : term582 l r x => @lem5704297 l r x h0)). Qed.
Lemma lem5704300 (l : int) (r : int) (x : int) (h1 : term570 l r x) : term570 l r x.
Proof. exact (h1). Qed.
Lemma lem5704301 (l : int) (r : int) (x : int) (h1 : term570 l r x) : (term570 l r x) = False.
Proof. exact (prop_ext (fun h2 : term570 l r x => @lem5704298 l r x h1) (fun h2 : False => @lem5704300 l r x h1)). Qed.
Lemma lem5704302 (l : int) (r : int) (x : int) (h1 : term570 l r x) : False.
Proof. exact (EQ_MP (@lem5704301 l r x h1) (@lem5704300 l r x h1)). Qed.
Lemma lem5704303 (l : int) (r : int) (h1 : term572 l r) : term572 l r.
Proof. exact (h1). Qed.
Lemma lem5704304 (l : int) (r : int) (h1 : term572 l r) : False.
Proof. exact (ex_elim (@lem5704303 l r h1) (fun x : int => fun h0 : term571 l r x => @lem5704302 l r x h0)). Qed.
Lemma lem5704305 (l : int) (r : int) (h1 : term555 l r) : term555 l r.
Proof. exact (h1). Qed.
Lemma lem5704306 (l : int) (r : int) (h1 : term555 l r) : term572 l r.
Proof. exact (EQ_MP (@lem5703243 l r) (@lem5704305 l r h1)). Qed.
Lemma lem5704307 (l : int) (r : int) (h1 : term555 l r) : (term572 l r) = False.
Proof. exact (prop_ext (fun h2 : term572 l r => @lem5704304 l r h2) (fun h2 : False => @lem5704306 l r h1)). Qed.
Lemma lem5704308 (l : int) (r : int) (h1 : term555 l r) : False.
Proof. exact (EQ_MP (@lem5704307 l r h1) (@lem5704306 l r h1)). Qed.
Lemma lem5704309 (l : int) (r : int) : term632 l r.
Proof. exact (fun h0 : term555 l r => @lem5704308 l r h0). Qed.
Lemma lem5704310 (l : int) (r : int) : term633 l r.
Proof. exact (@lem1386578 (term634 l r)). Qed.
Lemma lem5704313 (l : int) (r : int) : term634 l r.
Proof. exact (@lem5704310 l r (@lem5704309 l r)). Qed.
Lemma lem5704314 (l : int) (r : int) : (term554 l r) = (term533 l r).
Proof. exact (SYM (@lem5702831 l r)). Qed.
Lemma lem5704315 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5704316 (l : int) (r : int) : (term634 l r) = (term525 l r).
Proof. exact (MK_COMB (@lem5704315) (@lem5704314 l r)). Qed.
Lemma lem5704317 (l : int) (r : int) : term525 l r.
Proof. exact (EQ_MP (@lem5704316 l r) (@lem5704313 l r)). Qed.
Lemma lem5704318 (l : int) (r : int) : term470 l r.
Proof. exact (EQ_MP (@lem5702669 l r) (@lem5704317 l r)). Qed.
Lemma lem5704319 (l : int) (r : int) : (term470 l r) = ((term470 l r) = True).
Proof. exact (@lem7 (term470 l r)). Qed.
Lemma lem5704320 (l : int) (r : int) : (term470 l r) = True.
Proof. exact (EQ_MP (@lem5704319 l r) (@lem5704318 l r)). Qed.
Lemma lem5704321 (l : int) (r : int) : True = (term470 l r).
Proof. exact (SYM (@lem5704320 l r)). Qed.
Lemma lem5704322 (l : int) (r : int) : term470 l r.
Proof. exact (EQ_MP (@lem5704321 l r) (@lem0)). Qed.
Lemma lem5704323 (l : int) (r : int) : (term635 l r) = (term497 l r).
Proof. exact (@lem2954598 (term497 l r)). Qed.
Lemma lem5704350 (l : int) (x : int) (r : int) : (term56 l x r) = (term526 l x r).
Proof. exact (@lem17045 (int_le l x) (int_le x r)). Qed.
Lemma lem5704352 (l : int) (x : int) (r : int) : (term636 l x r) = (term636 l x r).
Proof. exact (eq_refl (term636 l x r)). Qed.
Lemma lem5704353 (l : int) (x : int) (r : int) : (term637 l x r) = (term638 l x r).
Proof. exact (MK_COMB (@lem5704352 l x r) (@lem5704350 l x r)). Qed.
Lemma lem5704354 (l : int) (x : int) (r : int) : (term639 l x r) = (term637 l x r).
Proof. exact (@lem17362 (term476 l x r) (term50 l x r)). Qed.
Lemma lem5704355 (l : int) (x : int) (r : int) : (term639 l x r) = (term638 l x r).
Proof. exact (TRANS (@lem5704354 l x r) (@lem5704353 l x r)). Qed.
Lemma lem5704356 (P : int -> Prop) : (term531 P) = (term532 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem5704357 (l : int) (r : int) : (term640 l r) = (term641 l r).
Proof. exact (@lem5704356 (term496 l r)). Qed.
Lemma lem5704358 (l : int) (x : int) (r : int) : (term642 l r x) = (term494 l x r).
Proof. exact (eq_refl (term642 l r x)). Qed.
Lemma lem5704359 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5704360 (l : int) (x : int) (r : int) : (term643 l r x) = (term639 l x r).
Proof. exact (MK_COMB (@lem5704359) (@lem5704358 l x r)). Qed.
Lemma lem5704361 (l : int) (x : int) (r : int) : (term643 l r x) = (term638 l x r).
Proof. exact (TRANS (@lem5704360 l x r) (@lem5704355 l x r)). Qed.
Lemma lem5704362 (l : int) (r : int) : (term644 l r) = (term645 l r).
Proof. exact (fun_ext (fun x : int => @lem5704361 l x r)). Qed.
Lemma lem5704363 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem5704364 (l : int) (r : int) : (term641 l r) = (term646 l r).
Proof. exact (MK_COMB (@lem5704363) (@lem5704362 l r)). Qed.
Lemma lem5704366 (l : int) (r : int) : (term640 l r) = (term646 l r).
Proof. exact (TRANS (@lem5704357 l r) (@lem5704364 l r)). Qed.
Lemma lem5704383 (l : int) (x : int) (r : int) : (term638 l x r) = (term638 l x r).
Proof. exact (eq_refl (term638 l x r)). Qed.
Lemma lem5704384 (l : int) (r : int) : (term645 l r) = (term645 l r).
Proof. exact (fun_ext (fun x : int => @lem5704383 l x r)). Qed.
Lemma lem5704385 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem5704386 (l : int) (r : int) : (term646 l r) = (term646 l r).
Proof. exact (MK_COMB (@lem5704385) (@lem5704384 l r)). Qed.
Lemma lem5704399 (l : int) (r : int) : (term640 l r) = (term646 l r).
Proof. exact (TRANS (@lem5704366 l r) (@lem5704386 l r)). Qed.
Lemma lem5704400 (l : int) (x : int) (r : int) : (term638 l x r) = (term638 l x r).
Proof. exact (eq_refl (term638 l x r)). Qed.
Lemma lem5704401 (l : int) (r : int) : (term645 l r) = (term645 l r).
Proof. exact (fun_ext (fun x : int => @lem5704400 l x r)). Qed.
Lemma lem5704402 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem5704403 (l : int) (r : int) : (term646 l r) = (term646 l r).
Proof. exact (MK_COMB (@lem5704402) (@lem5704401 l r)). Qed.
Lemma lem5704404 (l : int) (r : int) : (term640 l r) = (term646 l r).
Proof. exact (TRANS (@lem5704399 l r) (@lem5704403 l r)). Qed.
Lemma lem5704406 (x : int) (y : int) : (int_lt x y) = (term58 x y).
Proof. exact (proj2 (@lem2841544 x y)). Qed.
Lemma lem5704407 (l : int) (x : int) : (int_lt l x) = (term58 l x).
Proof. exact (@lem5704406 l x). Qed.
Lemma lem5704409 (x : int) (y : int) : (int_le x y) = (term61 x y).
Proof. exact (EQ_MP (@lem2841616 x y) (@lem2841615 x y)). Qed.
Lemma lem5704410 (l : int) (x : int) : (term58 l x) = (term540 l x).
Proof. exact (@lem5704409 (term541 l) x). Qed.
Lemma lem5704412 (x : int) (y : int) : (term64 x y) = (term65 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem5704413 (l : int) : (term542 l) = (term543 l).
Proof. exact (@lem5704412 l term68). Qed.
Lemma lem5704415 (n : nat) : (term73 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem5704416 : term74 = term75.
Proof. exact (@lem5704415 term76). Qed.
Lemma lem5704417 (l : int) : (term143 l) = (term143 l).
Proof. exact (eq_refl (term143 l)). Qed.
Lemma lem5704418 (l : int) : (term543 l) = (term104 l).
Proof. exact (MK_COMB (@lem5704417 l) (@lem5704416)). Qed.
Lemma lem5704419 (l : int) : (term542 l) = (term104 l).
Proof. exact (TRANS (@lem5704413 l) (@lem5704418 l)). Qed.
Lemma lem5704420 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5704421 (l : int) : (term544 l) = (term545 l).
Proof. exact (MK_COMB (@lem5704420) (@lem5704419 l)). Qed.
Lemma lem5704422 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem5704423 (l : int) (x : int) : (term540 l x) = (term546 l x).
Proof. exact (MK_COMB (@lem5704421 l) (@lem5704422 x)). Qed.
Lemma lem5704424 (l : int) (x : int) : (term58 l x) = (term546 l x).
Proof. exact (TRANS (@lem5704410 l x) (@lem5704423 l x)). Qed.
Lemma lem5704425 (l : int) (x : int) : (int_lt l x) = (term546 l x).
Proof. exact (TRANS (@lem5704407 l x) (@lem5704424 l x)). Qed.
Lemma lem5704428 (x : int) (y : int) : (int_le x y) = (term61 x y).
Proof. exact (EQ_MP (@lem2841616 x y) (@lem2841615 x y)). Qed.
Lemma lem5704430 (x : int) (r : int) : (int_le x r) = (term61 x r).
Proof. exact (@lem5704428 x r). Qed.
Lemma lem5704431 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5704432 (l : int) (x : int) : (term647 l x) = (term648 l x).
Proof. exact (MK_COMB (@lem5704431) (@lem5704425 l x)). Qed.
Lemma lem5704433 (l : int) (x : int) (r : int) : (term476 l x r) = (term649 l x r).
Proof. exact (MK_COMB (@lem5704432 l x) (@lem5704430 x r)). Qed.
Lemma lem5704435 (y : int) (x : int) : (term57 x y) = (term58 y x).
Proof. exact (proj1 (@lem2841542 x y)). Qed.
Lemma lem5704436 (x : int) (l : int) : (term57 l x) = (term58 x l).
Proof. exact (@lem5704435 x l). Qed.
Lemma lem5704438 (x : int) (y : int) : (int_le x y) = (term61 x y).
Proof. exact (EQ_MP (@lem2841616 x y) (@lem2841615 x y)). Qed.
Lemma lem5704439 (x : int) (l : int) : (term58 x l) = (term540 x l).
Proof. exact (@lem5704438 (term541 x) l). Qed.
Lemma lem5704441 (x : int) (y : int) : (term64 x y) = (term65 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem5704442 (x : int) : (term542 x) = (term543 x).
Proof. exact (@lem5704441 x term68). Qed.
Lemma lem5704444 (n : nat) : (term73 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem5704445 : term74 = term75.
Proof. exact (@lem5704444 term76). Qed.
Lemma lem5704446 (x : int) : (term143 x) = (term143 x).
Proof. exact (eq_refl (term143 x)). Qed.
Lemma lem5704447 (x : int) : (term543 x) = (term104 x).
Proof. exact (MK_COMB (@lem5704446 x) (@lem5704445)). Qed.
Lemma lem5704448 (x : int) : (term542 x) = (term104 x).
Proof. exact (TRANS (@lem5704442 x) (@lem5704447 x)). Qed.
Lemma lem5704449 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5704450 (x : int) : (term544 x) = (term545 x).
Proof. exact (MK_COMB (@lem5704449) (@lem5704448 x)). Qed.
Lemma lem5704451 (l : int) : (real_of_int l) = (real_of_int l).
Proof. exact (eq_refl (real_of_int l)). Qed.
Lemma lem5704452 (x : int) (l : int) : (term540 x l) = (term546 x l).
Proof. exact (MK_COMB (@lem5704450 x) (@lem5704451 l)). Qed.
Lemma lem5704453 (x : int) (l : int) : (term58 x l) = (term546 x l).
Proof. exact (TRANS (@lem5704439 x l) (@lem5704452 x l)). Qed.
Lemma lem5704454 (x : int) (l : int) : (term57 l x) = (term546 x l).
Proof. exact (TRANS (@lem5704436 x l) (@lem5704453 x l)). Qed.
Lemma lem5704456 (y : int) (x : int) : (term57 x y) = (term58 y x).
Proof. exact (proj1 (@lem2841542 x y)). Qed.
Lemma lem5704457 (r : int) (x : int) : (term57 x r) = (term58 r x).
Proof. exact (@lem5704456 r x). Qed.
Lemma lem5704459 (x : int) (y : int) : (int_le x y) = (term61 x y).
Proof. exact (EQ_MP (@lem2841616 x y) (@lem2841615 x y)). Qed.
Lemma lem5704460 (r : int) (x : int) : (term58 r x) = (term540 r x).
Proof. exact (@lem5704459 (term541 r) x). Qed.
Lemma lem5704462 (x : int) (y : int) : (term64 x y) = (term65 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem5704463 (r : int) : (term542 r) = (term543 r).
Proof. exact (@lem5704462 r term68). Qed.
Lemma lem5704465 (n : nat) : (term73 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem5704466 : term74 = term75.
Proof. exact (@lem5704465 term76). Qed.
Lemma lem5704467 (r : int) : (term143 r) = (term143 r).
Proof. exact (eq_refl (term143 r)). Qed.
Lemma lem5704468 (r : int) : (term543 r) = (term104 r).
Proof. exact (MK_COMB (@lem5704467 r) (@lem5704466)). Qed.
Lemma lem5704469 (r : int) : (term542 r) = (term104 r).
Proof. exact (TRANS (@lem5704463 r) (@lem5704468 r)). Qed.
Lemma lem5704470 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5704471 (r : int) : (term544 r) = (term545 r).
Proof. exact (MK_COMB (@lem5704470) (@lem5704469 r)). Qed.
Lemma lem5704472 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem5704473 (r : int) (x : int) : (term540 r x) = (term546 r x).
Proof. exact (MK_COMB (@lem5704471 r) (@lem5704472 x)). Qed.
Lemma lem5704474 (r : int) (x : int) : (term58 r x) = (term546 r x).
Proof. exact (TRANS (@lem5704460 r x) (@lem5704473 r x)). Qed.
Lemma lem5704475 (r : int) (x : int) : (term57 x r) = (term546 r x).
Proof. exact (TRANS (@lem5704457 r x) (@lem5704474 r x)). Qed.
Lemma lem5704476 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5704477 (x : int) (l : int) : (term548 l x) = (term549 x l).
Proof. exact (MK_COMB (@lem5704476) (@lem5704454 x l)). Qed.
Lemma lem5704478 (l : int) (r : int) (x : int) : (term526 l x r) = (term550 l r x).
Proof. exact (MK_COMB (@lem5704477 x l) (@lem5704475 r x)). Qed.
Lemma lem5704479 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5704480 (l : int) (x : int) (r : int) : (term636 l x r) = (term650 l x r).
Proof. exact (MK_COMB (@lem5704479) (@lem5704433 l x r)). Qed.
Lemma lem5704481 (l : int) (r : int) (x : int) : (term638 l x r) = (term651 l r x).
Proof. exact (MK_COMB (@lem5704480 l x r) (@lem5704478 l r x)). Qed.
Lemma lem5704482 (l : int) (r : int) : (term645 l r) = (term652 l r).
Proof. exact (fun_ext (fun x : int => @lem5704481 l r x)). Qed.
Lemma lem5704483 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem5704484 (l : int) (r : int) : (term646 l r) = (term653 l r).
Proof. exact (MK_COMB (@lem5704483) (@lem5704482 l r)). Qed.
Lemma lem5704485 (l : int) (r : int) : (term640 l r) = (term653 l r).
Proof. exact (TRANS (@lem5704404 l r) (@lem5704484 l r)). Qed.
Lemma lem5704489 (t : Prop) : (term88 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5704545 (l : int) (r : int) : (term654 l r) = (term653 l r).
Proof. exact (@lem5704489 (term653 l r)). Qed.
Lemma lem5704558 (l : int) (r : int) (x : int) : (term651 l r x) = (term651 l r x).
Proof. exact (eq_refl (term651 l r x)). Qed.
Lemma lem5704559 (l : int) (r : int) : (term652 l r) = (term652 l r).
Proof. exact (fun_ext (fun x : int => @lem5704558 l r x)). Qed.
Lemma lem5704560 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem5704561 (l : int) (r : int) : (term653 l r) = (term653 l r).
Proof. exact (MK_COMB (@lem5704560) (@lem5704559 l r)). Qed.
Lemma lem5704562 (l : int) (r : int) : (term654 l r) = (term653 l r).
Proof. exact (TRANS (@lem5704545 l r) (@lem5704561 l r)). Qed.
Lemma lem5704575 (l : int) (r : int) (x : int) : (term651 l r x) = (term651 l r x).
Proof. exact (eq_refl (term651 l r x)). Qed.
Lemma lem5704576 (l : int) (r : int) : (term652 l r) = (term652 l r).
Proof. exact (fun_ext (fun x : int => @lem5704575 l r x)). Qed.
Lemma lem5704577 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem5704578 (l : int) (r : int) : (term653 l r) = (term653 l r).
Proof. exact (MK_COMB (@lem5704577) (@lem5704576 l r)). Qed.
Lemma lem5704579 (l : int) (r : int) : (term654 l r) = (term653 l r).
Proof. exact (TRANS (@lem5704562 l r) (@lem5704578 l r)). Qed.
Lemma lem5704580 (x : int) (l : int) : (term546 l x) = (term556 x l).
Proof. exact (@lem1988287 (real_of_int x) (term104 l)). Qed.
Lemma lem5704592 (x : int) (l : int) : (term557 x l) = (term558 x l).
Proof. exact (@lem1982792 (real_of_int x) (term104 l)). Qed.
Lemma lem5704593 (l : int) : (term105 l) = (term106 l).
Proof. exact (@lem1982781 (real_of_int l) term103 term75). Qed.
Lemma lem5704595 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5704596 : term75 = term108.
Proof. exact (@lem5704595 term76). Qed.
Lemma lem5704598 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5704599 : term103 = term111.
Proof. exact (@lem5704598 term76). Qed.
Lemma lem5704600 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5704601 : term112 = term113.
Proof. exact (MK_COMB (@lem5704600) (@lem5704599)). Qed.
Lemma lem5704602 : term114 = term115.
Proof. exact (MK_COMB (@lem5704601) (@lem5704596)). Qed.
Lemma lem5704603 : term115 = term116.
Proof. exact (@lem1981613 term103 term75 term75 term75). Qed.
Lemma lem5704605 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5704606 : term119 = term120.
Proof. exact (@lem5704605 term76 term76). Qed.
Lemma lem5704607 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5704608 : term122 = term76.
Proof. exact (EQ_MP (@lem5704607) (@lem940073)). Qed.
Lemma lem5704609 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5704610 : term120 = term75.
Proof. exact (MK_COMB (@lem5704609) (@lem5704608)). Qed.
Lemma lem5704611 : term119 = term75.
Proof. exact (TRANS (@lem5704606) (@lem5704610)). Qed.
Lemma lem5704613 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5704614 : term114 = term125.
Proof. exact (@lem5704613 term76 term76). Qed.
Lemma lem5704615 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5704616 : term122 = term76.
Proof. exact (EQ_MP (@lem5704615) (@lem940073)). Qed.
Lemma lem5704617 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5704618 : term120 = term75.
Proof. exact (MK_COMB (@lem5704617) (@lem5704616)). Qed.
Lemma lem5704619 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5704620 : term125 = term103.
Proof. exact (MK_COMB (@lem5704619) (@lem5704618)). Qed.
Lemma lem5704621 : term114 = term103.
Proof. exact (TRANS (@lem5704614) (@lem5704620)). Qed.
Lemma lem5704622 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5704623 : term126 = term127.
Proof. exact (MK_COMB (@lem5704622) (@lem5704621)). Qed.
Lemma lem5704624 : term116 = term111.
Proof. exact (MK_COMB (@lem5704623) (@lem5704611)). Qed.
Lemma lem5704625 : term115 = term111.
Proof. exact (TRANS (@lem5704603) (@lem5704624)). Qed.
Lemma lem5704626 : term114 = term111.
Proof. exact (TRANS (@lem5704602) (@lem5704625)). Qed.
Lemma lem5704628 (x : real) : (term128 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5704629 : term111 = term103.
Proof. exact (@lem5704628 term103). Qed.
Lemma lem5704630 : term114 = term103.
Proof. exact (TRANS (@lem5704626) (@lem5704629)). Qed.
Lemma lem5704633 (l : int) : (term129 l) = (term129 l).
Proof. exact (eq_refl (term129 l)). Qed.
Lemma lem5704634 (l : int) : (term106 l) = (term130 l).
Proof. exact (MK_COMB (@lem5704633 l) (@lem5704630)). Qed.
Lemma lem5704635 (l : int) : (term105 l) = (term130 l).
Proof. exact (TRANS (@lem5704593 l) (@lem5704634 l)). Qed.
Lemma lem5704636 (x : int) : (term143 x) = (term143 x).
Proof. exact (eq_refl (term143 x)). Qed.
Lemma lem5704637 (x : int) (l : int) : (term558 x l) = (term144 x l).
Proof. exact (MK_COMB (@lem5704636 x) (@lem5704635 l)). Qed.
Lemma lem5704642 (l : int) (x : int) : (term144 x l) = (term561 l x).
Proof. exact (@lem1982757 (term93 l) (real_of_int x) term103). Qed.
Lemma lem5704643 (l : int) (x : int) : (term558 x l) = (term561 l x).
Proof. exact (TRANS (@lem5704637 x l) (@lem5704642 l x)). Qed.
Lemma lem5704645 (l : int) (x : int) : (term557 x l) = (term561 l x).
Proof. exact (TRANS (@lem5704592 x l) (@lem5704643 l x)). Qed.
Lemma lem5704646 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5704647 (l : int) (x : int) : (term559 x l) = (term562 l x).
Proof. exact (MK_COMB (@lem5704646) (@lem5704645 l x)). Qed.
Lemma lem5704648 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem5704649 (l : int) (x : int) : (term556 x l) = (term563 l x).
Proof. exact (MK_COMB (@lem5704647 l x) (@lem5704648)). Qed.
Lemma lem5704650 (l : int) (x : int) : (term546 l x) = (term563 l x).
Proof. exact (TRANS (@lem5704580 x l) (@lem5704649 l x)). Qed.
Lemma lem5704651 (r : int) (x : int) : (term61 x r) = (term150 r x).
Proof. exact (@lem1988287 (real_of_int r) (real_of_int x)). Qed.
Lemma lem5704664 (r : int) (x : int) : (term70 r x) = (term91 r x).
Proof. exact (@lem1982792 (real_of_int r) (real_of_int x)). Qed.
Lemma lem5704665 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5704666 (r : int) (x : int) : (term151 r x) = (term154 r x).
Proof. exact (MK_COMB (@lem5704665) (@lem5704664 r x)). Qed.
Lemma lem5704667 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem5704668 (r : int) (x : int) : (term150 r x) = (term155 r x).
Proof. exact (MK_COMB (@lem5704666 r x) (@lem5704667)). Qed.
Lemma lem5704669 (r : int) (x : int) : (term61 x r) = (term155 r x).
Proof. exact (TRANS (@lem5704651 r x) (@lem5704668 r x)). Qed.
Lemma lem5704670 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5704671 (l : int) (x : int) : (term648 l x) = (term655 l x).
Proof. exact (MK_COMB (@lem5704670) (@lem5704650 l x)). Qed.
Lemma lem5704672 (l : int) (r : int) (x : int) : (term649 l x r) = (term656 l r x).
Proof. exact (MK_COMB (@lem5704671 l x) (@lem5704669 r x)). Qed.
Lemma lem5704673 (l : int) (x : int) : (term546 x l) = (term556 l x).
Proof. exact (@lem1988287 (real_of_int l) (term104 x)). Qed.
Lemma lem5704685 (l : int) (x : int) : (term557 l x) = (term558 l x).
Proof. exact (@lem1982792 (real_of_int l) (term104 x)). Qed.
Lemma lem5704686 (x : int) : (term105 x) = (term106 x).
Proof. exact (@lem1982781 (real_of_int x) term103 term75). Qed.
Lemma lem5704688 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5704689 : term75 = term108.
Proof. exact (@lem5704688 term76). Qed.
Lemma lem5704691 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5704692 : term103 = term111.
Proof. exact (@lem5704691 term76). Qed.
Lemma lem5704693 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5704694 : term112 = term113.
Proof. exact (MK_COMB (@lem5704693) (@lem5704692)). Qed.
Lemma lem5704695 : term114 = term115.
Proof. exact (MK_COMB (@lem5704694) (@lem5704689)). Qed.
Lemma lem5704696 : term115 = term116.
Proof. exact (@lem1981613 term103 term75 term75 term75). Qed.
Lemma lem5704698 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5704699 : term119 = term120.
Proof. exact (@lem5704698 term76 term76). Qed.
Lemma lem5704700 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5704701 : term122 = term76.
Proof. exact (EQ_MP (@lem5704700) (@lem940073)). Qed.
Lemma lem5704702 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5704703 : term120 = term75.
Proof. exact (MK_COMB (@lem5704702) (@lem5704701)). Qed.
Lemma lem5704704 : term119 = term75.
Proof. exact (TRANS (@lem5704699) (@lem5704703)). Qed.
Lemma lem5704706 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5704707 : term114 = term125.
Proof. exact (@lem5704706 term76 term76). Qed.
Lemma lem5704708 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5704709 : term122 = term76.
Proof. exact (EQ_MP (@lem5704708) (@lem940073)). Qed.
Lemma lem5704710 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5704711 : term120 = term75.
Proof. exact (MK_COMB (@lem5704710) (@lem5704709)). Qed.
Lemma lem5704712 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5704713 : term125 = term103.
Proof. exact (MK_COMB (@lem5704712) (@lem5704711)). Qed.
Lemma lem5704714 : term114 = term103.
Proof. exact (TRANS (@lem5704707) (@lem5704713)). Qed.
Lemma lem5704715 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5704716 : term126 = term127.
Proof. exact (MK_COMB (@lem5704715) (@lem5704714)). Qed.
Lemma lem5704717 : term116 = term111.
Proof. exact (MK_COMB (@lem5704716) (@lem5704704)). Qed.
Lemma lem5704718 : term115 = term111.
Proof. exact (TRANS (@lem5704696) (@lem5704717)). Qed.
Lemma lem5704719 : term114 = term111.
Proof. exact (TRANS (@lem5704695) (@lem5704718)). Qed.
Lemma lem5704721 (x : real) : (term128 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5704722 : term111 = term103.
Proof. exact (@lem5704721 term103). Qed.
Lemma lem5704723 : term114 = term103.
Proof. exact (TRANS (@lem5704719) (@lem5704722)). Qed.
Lemma lem5704726 (x : int) : (term129 x) = (term129 x).
Proof. exact (eq_refl (term129 x)). Qed.
Lemma lem5704727 (x : int) : (term106 x) = (term130 x).
Proof. exact (MK_COMB (@lem5704726 x) (@lem5704723)). Qed.
Lemma lem5704728 (x : int) : (term105 x) = (term130 x).
Proof. exact (TRANS (@lem5704686 x) (@lem5704727 x)). Qed.
Lemma lem5704729 (l : int) : (term143 l) = (term143 l).
Proof. exact (eq_refl (term143 l)). Qed.
Lemma lem5704732 (l : int) (x : int) : (term558 l x) = (term144 l x).
Proof. exact (MK_COMB (@lem5704729 l) (@lem5704728 x)). Qed.
Lemma lem5704734 (l : int) (x : int) : (term557 l x) = (term144 l x).
Proof. exact (TRANS (@lem5704685 l x) (@lem5704732 l x)). Qed.
Lemma lem5704735 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5704736 (l : int) (x : int) : (term559 l x) = (term148 l x).
Proof. exact (MK_COMB (@lem5704735) (@lem5704734 l x)). Qed.
Lemma lem5704737 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem5704738 (l : int) (x : int) : (term556 l x) = (term149 l x).
Proof. exact (MK_COMB (@lem5704736 l x) (@lem5704737)). Qed.
Lemma lem5704739 (l : int) (x : int) : (term546 x l) = (term149 l x).
Proof. exact (TRANS (@lem5704673 l x) (@lem5704738 l x)). Qed.
Lemma lem5704740 (x : int) (r : int) : (term546 r x) = (term556 x r).
Proof. exact (@lem1988287 (real_of_int x) (term104 r)). Qed.
Lemma lem5704752 (x : int) (r : int) : (term557 x r) = (term558 x r).
Proof. exact (@lem1982792 (real_of_int x) (term104 r)). Qed.
Lemma lem5704753 (r : int) : (term105 r) = (term106 r).
Proof. exact (@lem1982781 (real_of_int r) term103 term75). Qed.
Lemma lem5704755 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5704756 : term75 = term108.
Proof. exact (@lem5704755 term76). Qed.
Lemma lem5704758 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5704759 : term103 = term111.
Proof. exact (@lem5704758 term76). Qed.
Lemma lem5704760 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5704761 : term112 = term113.
Proof. exact (MK_COMB (@lem5704760) (@lem5704759)). Qed.
Lemma lem5704762 : term114 = term115.
Proof. exact (MK_COMB (@lem5704761) (@lem5704756)). Qed.
Lemma lem5704763 : term115 = term116.
Proof. exact (@lem1981613 term103 term75 term75 term75). Qed.
Lemma lem5704765 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5704766 : term119 = term120.
Proof. exact (@lem5704765 term76 term76). Qed.
Lemma lem5704767 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5704768 : term122 = term76.
Proof. exact (EQ_MP (@lem5704767) (@lem940073)). Qed.
Lemma lem5704769 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5704770 : term120 = term75.
Proof. exact (MK_COMB (@lem5704769) (@lem5704768)). Qed.
Lemma lem5704771 : term119 = term75.
Proof. exact (TRANS (@lem5704766) (@lem5704770)). Qed.
Lemma lem5704773 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5704774 : term114 = term125.
Proof. exact (@lem5704773 term76 term76). Qed.
Lemma lem5704775 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5704776 : term122 = term76.
Proof. exact (EQ_MP (@lem5704775) (@lem940073)). Qed.
Lemma lem5704777 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5704778 : term120 = term75.
Proof. exact (MK_COMB (@lem5704777) (@lem5704776)). Qed.
Lemma lem5704779 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5704780 : term125 = term103.
Proof. exact (MK_COMB (@lem5704779) (@lem5704778)). Qed.
Lemma lem5704781 : term114 = term103.
Proof. exact (TRANS (@lem5704774) (@lem5704780)). Qed.
Lemma lem5704782 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5704783 : term126 = term127.
Proof. exact (MK_COMB (@lem5704782) (@lem5704781)). Qed.
Lemma lem5704784 : term116 = term111.
Proof. exact (MK_COMB (@lem5704783) (@lem5704771)). Qed.
Lemma lem5704785 : term115 = term111.
Proof. exact (TRANS (@lem5704763) (@lem5704784)). Qed.
Lemma lem5704786 : term114 = term111.
Proof. exact (TRANS (@lem5704762) (@lem5704785)). Qed.
Lemma lem5704788 (x : real) : (term128 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5704789 : term111 = term103.
Proof. exact (@lem5704788 term103). Qed.
Lemma lem5704790 : term114 = term103.
Proof. exact (TRANS (@lem5704786) (@lem5704789)). Qed.
Lemma lem5704793 (r : int) : (term129 r) = (term129 r).
Proof. exact (eq_refl (term129 r)). Qed.
Lemma lem5704794 (r : int) : (term106 r) = (term130 r).
Proof. exact (MK_COMB (@lem5704793 r) (@lem5704790)). Qed.
Lemma lem5704795 (r : int) : (term105 r) = (term130 r).
Proof. exact (TRANS (@lem5704753 r) (@lem5704794 r)). Qed.
Lemma lem5704796 (x : int) : (term143 x) = (term143 x).
Proof. exact (eq_refl (term143 x)). Qed.
Lemma lem5704797 (x : int) (r : int) : (term558 x r) = (term144 x r).
Proof. exact (MK_COMB (@lem5704796 x) (@lem5704795 r)). Qed.
Lemma lem5704802 (r : int) (x : int) : (term144 x r) = (term561 r x).
Proof. exact (@lem1982757 (term93 r) (real_of_int x) term103). Qed.
Lemma lem5704803 (r : int) (x : int) : (term558 x r) = (term561 r x).
Proof. exact (TRANS (@lem5704797 x r) (@lem5704802 r x)). Qed.
Lemma lem5704805 (r : int) (x : int) : (term557 x r) = (term561 r x).
Proof. exact (TRANS (@lem5704752 x r) (@lem5704803 r x)). Qed.
Lemma lem5704806 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5704807 (r : int) (x : int) : (term559 x r) = (term562 r x).
Proof. exact (MK_COMB (@lem5704806) (@lem5704805 r x)). Qed.
Lemma lem5704808 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem5704809 (r : int) (x : int) : (term556 x r) = (term563 r x).
Proof. exact (MK_COMB (@lem5704807 r x) (@lem5704808)). Qed.
Lemma lem5704810 (r : int) (x : int) : (term546 r x) = (term563 r x).
Proof. exact (TRANS (@lem5704740 x r) (@lem5704809 r x)). Qed.
Lemma lem5704811 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5704812 (l : int) (x : int) : (term549 x l) = (term564 l x).
Proof. exact (MK_COMB (@lem5704811) (@lem5704739 l x)). Qed.
Lemma lem5704813 (l : int) (r : int) (x : int) : (term550 l r x) = (term565 l r x).
Proof. exact (MK_COMB (@lem5704812 l x) (@lem5704810 r x)). Qed.
Lemma lem5704814 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5704815 (l : int) (r : int) (x : int) : (term650 l x r) = (term657 l r x).
Proof. exact (MK_COMB (@lem5704814) (@lem5704672 l r x)). Qed.
Lemma lem5704816 (l : int) (r : int) (x : int) : (term651 l r x) = (term658 l r x).
Proof. exact (MK_COMB (@lem5704815 l r x) (@lem5704813 l r x)). Qed.
Lemma lem5704817 (l : int) (r : int) : (term652 l r) = (term659 l r).
Proof. exact (fun_ext (fun x : int => @lem5704816 l r x)). Qed.
Lemma lem5704818 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem5704819 (l : int) (r : int) : (term653 l r) = (term660 l r).
Proof. exact (MK_COMB (@lem5704818) (@lem5704817 l r)). Qed.
Lemma lem5704874 (l : int) (r : int) : (term654 l r) = (term660 l r).
Proof. exact (TRANS (@lem5704579 l r) (@lem5704819 l r)). Qed.
Lemma lem5704897 (l : int) (r : int) (x : int) : (term658 l r x) = (term661 l r x).
Proof. exact (@lem19158 (term149 l x) (term656 l r x) (term563 r x)). Qed.
Lemma lem5704898 (l : int) (r : int) : (term659 l r) = (term662 l r).
Proof. exact (fun_ext (fun x : int => @lem5704897 l r x)). Qed.
Lemma lem5704899 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem5704900 (l : int) (r : int) : (term660 l r) = (term663 l r).
Proof. exact (MK_COMB (@lem5704899) (@lem5704898 l r)). Qed.
Lemma lem5704901 (l : int) (r : int) : (term654 l r) = (term663 l r).
Proof. exact (TRANS (@lem5704874 l r) (@lem5704900 l r)). Qed.
Lemma lem5704911 (l : int) (r : int) (x : int) (h1 : term661 l r x) : term661 l r x.
Proof. exact (h1). Qed.
Lemma lem5704912 (r : int) (l : int) (x : int) (h1 : term664 r l x) : term664 r l x.
Proof. exact (h1). Qed.
Lemma lem5704913 (r : int) (l : int) (x : int) (h1 : term664 r l x) : term149 l x.
Proof. exact (proj2 (@lem5704912 r l x h1)). Qed.
Lemma lem5704914 (r : int) (l : int) (x : int) (h1 : term664 r l x) : term656 l r x.
Proof. exact (proj1 (@lem5704912 r l x h1)). Qed.
Lemma lem5704916 (r : int) (l : int) (x : int) (h1 : term664 r l x) : term563 l x.
Proof. exact (proj1 (@lem5704914 r l x h1)). Qed.
Lemma lem5704918 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5704919 : term160 = term161.
Proof. exact (@lem5704918 term81 term75). Qed.
Lemma lem5704921 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5704922 : term75 = term108.
Proof. exact (@lem5704921 term76). Qed.
Lemma lem5704924 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5704925 : term81 = term162.
Proof. exact (@lem5704924 (NUMERAL 0)). Qed.
Lemma lem5704926 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5704927 : term163 = term164.
Proof. exact (MK_COMB (@lem5704926) (@lem5704925)). Qed.
Lemma lem5704928 : term161 = term165.
Proof. exact (MK_COMB (@lem5704927) (@lem5704922)). Qed.
Lemma lem5704929 : term166.
Proof. exact (@lem1980255 term81 term75 term75 term75). Qed.
Lemma lem5704931 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5704932 : term161 = term168.
Proof. exact (@lem5704931 (NUMERAL 0) term76). Qed.
Lemma lem5704933 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5704934 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5704935 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5704934 h1) (fun h1 : term168 = True => @lem5704933)). Qed.
Lemma lem5704936 : term168 = True.
Proof. exact (EQ_MP (@lem5704935) (@lem5704933)). Qed.
Lemma lem5704937 : term161 = True.
Proof. exact (TRANS (@lem5704932) (@lem5704936)). Qed.
Lemma lem5704938 : True = term161.
Proof. exact (SYM (@lem5704937)). Qed.
Lemma lem5704939 : term161.
Proof. exact (EQ_MP (@lem5704938) (@lem0)). Qed.
Lemma lem5704940 : term170.
Proof. exact (@lem5704929 (@lem5704939)). Qed.
Lemma lem5704942 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5704943 : term161 = term168.
Proof. exact (@lem5704942 (NUMERAL 0) term76). Qed.
Lemma lem5704944 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5704945 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5704946 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5704945 h1) (fun h1 : term168 = True => @lem5704944)). Qed.
Lemma lem5704947 : term168 = True.
Proof. exact (EQ_MP (@lem5704946) (@lem5704944)). Qed.
Lemma lem5704948 : term161 = True.
Proof. exact (TRANS (@lem5704943) (@lem5704947)). Qed.
Lemma lem5704949 : True = term161.
Proof. exact (SYM (@lem5704948)). Qed.
Lemma lem5704950 : term161.
Proof. exact (EQ_MP (@lem5704949) (@lem0)). Qed.
Lemma lem5704951 : term165 = term171.
Proof. exact (@lem5704940 (@lem5704950)). Qed.
Lemma lem5704953 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5704954 : term119 = term120.
Proof. exact (@lem5704953 term76 term76). Qed.
Lemma lem5704955 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5704956 : term122 = term76.
Proof. exact (EQ_MP (@lem5704955) (@lem940073)). Qed.
Lemma lem5704957 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5704958 : term120 = term75.
Proof. exact (MK_COMB (@lem5704957) (@lem5704956)). Qed.
Lemma lem5704959 : term119 = term75.
Proof. exact (TRANS (@lem5704954) (@lem5704958)). Qed.
Lemma lem5704961 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5704962 : term173 = term81.
Proof. exact (@lem5704961 term76). Qed.
Lemma lem5704963 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5704964 : term174 = term163.
Proof. exact (MK_COMB (@lem5704963) (@lem5704962)). Qed.
Lemma lem5704965 : term171 = term161.
Proof. exact (MK_COMB (@lem5704964) (@lem5704959)). Qed.
Lemma lem5704967 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5704968 : term161 = term168.
Proof. exact (@lem5704967 (NUMERAL 0) term76). Qed.
Lemma lem5704969 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5704970 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5704971 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5704970 h1) (fun h1 : term168 = True => @lem5704969)). Qed.
Lemma lem5704972 : term168 = True.
Proof. exact (EQ_MP (@lem5704971) (@lem5704969)). Qed.
Lemma lem5704973 : term161 = True.
Proof. exact (TRANS (@lem5704968) (@lem5704972)). Qed.
Lemma lem5704974 : term171 = True.
Proof. exact (TRANS (@lem5704965) (@lem5704973)). Qed.
Lemma lem5704975 : term165 = True.
Proof. exact (TRANS (@lem5704951) (@lem5704974)). Qed.
Lemma lem5704976 : term161 = True.
Proof. exact (TRANS (@lem5704928) (@lem5704975)). Qed.
Lemma lem5704977 : term160 = True.
Proof. exact (TRANS (@lem5704919) (@lem5704976)). Qed.
Lemma lem5704978 : True = term160.
Proof. exact (SYM (@lem5704977)). Qed.
Lemma lem5704979 : term160.
Proof. exact (EQ_MP (@lem5704978) (@lem0)). Qed.
Lemma lem5704980 (r : int) (l : int) (x : int) (h1 : term664 r l x) : term583 l x.
Proof. exact (conj (@lem5704979) (@lem5704916 r l x h1)). Qed.
Lemma lem5704982 (x : real) (y : real) : term176 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5704983 (l : int) (x : int) : term584 l x.
Proof. exact (@lem5704982 term75 (term561 l x)). Qed.
Lemma lem5704984 (r : int) (l : int) (x : int) (h1 : term664 r l x) : term585 l x.
Proof. exact (@lem5704983 l x (@lem5704980 r l x h1)). Qed.
Lemma lem5704985 (l : int) (x : int) : (term586 l x) = (term561 l x).
Proof. exact (@lem1982733 (term561 l x)). Qed.
Lemma lem5704986 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5704987 (l : int) (x : int) : (term587 l x) = (term562 l x).
Proof. exact (MK_COMB (@lem5704986) (@lem5704985 l x)). Qed.
Lemma lem5704988 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem5704989 (l : int) (x : int) : (term585 l x) = (term563 l x).
Proof. exact (MK_COMB (@lem5704987 l x) (@lem5704988)). Qed.
Lemma lem5704990 (r : int) (l : int) (x : int) (h1 : term664 r l x) : term563 l x.
Proof. exact (EQ_MP (@lem5704989 l x) (@lem5704984 r l x h1)). Qed.
Lemma lem5704992 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5704993 : term160 = term161.
Proof. exact (@lem5704992 term81 term75). Qed.
Lemma lem5704995 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5704996 : term75 = term108.
Proof. exact (@lem5704995 term76). Qed.
Lemma lem5704998 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5704999 : term81 = term162.
Proof. exact (@lem5704998 (NUMERAL 0)). Qed.
Lemma lem5705000 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5705001 : term163 = term164.
Proof. exact (MK_COMB (@lem5705000) (@lem5704999)). Qed.
Lemma lem5705002 : term161 = term165.
Proof. exact (MK_COMB (@lem5705001) (@lem5704996)). Qed.
Lemma lem5705003 : term166.
Proof. exact (@lem1980255 term81 term75 term75 term75). Qed.
Lemma lem5705005 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5705006 : term161 = term168.
Proof. exact (@lem5705005 (NUMERAL 0) term76). Qed.
Lemma lem5705007 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5705008 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5705009 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5705008 h1) (fun h1 : term168 = True => @lem5705007)). Qed.
Lemma lem5705010 : term168 = True.
Proof. exact (EQ_MP (@lem5705009) (@lem5705007)). Qed.
Lemma lem5705011 : term161 = True.
Proof. exact (TRANS (@lem5705006) (@lem5705010)). Qed.
Lemma lem5705012 : True = term161.
Proof. exact (SYM (@lem5705011)). Qed.
Lemma lem5705013 : term161.
Proof. exact (EQ_MP (@lem5705012) (@lem0)). Qed.
Lemma lem5705014 : term170.
Proof. exact (@lem5705003 (@lem5705013)). Qed.
Lemma lem5705016 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5705017 : term161 = term168.
Proof. exact (@lem5705016 (NUMERAL 0) term76). Qed.
Lemma lem5705018 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5705019 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5705020 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5705019 h1) (fun h1 : term168 = True => @lem5705018)). Qed.
Lemma lem5705021 : term168 = True.
Proof. exact (EQ_MP (@lem5705020) (@lem5705018)). Qed.
Lemma lem5705022 : term161 = True.
Proof. exact (TRANS (@lem5705017) (@lem5705021)). Qed.
Lemma lem5705023 : True = term161.
Proof. exact (SYM (@lem5705022)). Qed.
Lemma lem5705024 : term161.
Proof. exact (EQ_MP (@lem5705023) (@lem0)). Qed.
Lemma lem5705025 : term165 = term171.
Proof. exact (@lem5705014 (@lem5705024)). Qed.
Lemma lem5705027 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5705028 : term119 = term120.
Proof. exact (@lem5705027 term76 term76). Qed.
Lemma lem5705029 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5705030 : term122 = term76.
Proof. exact (EQ_MP (@lem5705029) (@lem940073)). Qed.
Lemma lem5705031 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5705032 : term120 = term75.
Proof. exact (MK_COMB (@lem5705031) (@lem5705030)). Qed.
Lemma lem5705033 : term119 = term75.
Proof. exact (TRANS (@lem5705028) (@lem5705032)). Qed.
Lemma lem5705035 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5705036 : term173 = term81.
Proof. exact (@lem5705035 term76). Qed.
Lemma lem5705037 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5705038 : term174 = term163.
Proof. exact (MK_COMB (@lem5705037) (@lem5705036)). Qed.
Lemma lem5705039 : term171 = term161.
Proof. exact (MK_COMB (@lem5705038) (@lem5705033)). Qed.
Lemma lem5705041 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5705042 : term161 = term168.
Proof. exact (@lem5705041 (NUMERAL 0) term76). Qed.
Lemma lem5705043 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5705044 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5705045 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5705044 h1) (fun h1 : term168 = True => @lem5705043)). Qed.
Lemma lem5705046 : term168 = True.
Proof. exact (EQ_MP (@lem5705045) (@lem5705043)). Qed.
Lemma lem5705047 : term161 = True.
Proof. exact (TRANS (@lem5705042) (@lem5705046)). Qed.
Lemma lem5705048 : term171 = True.
Proof. exact (TRANS (@lem5705039) (@lem5705047)). Qed.
Lemma lem5705049 : term165 = True.
Proof. exact (TRANS (@lem5705025) (@lem5705048)). Qed.
Lemma lem5705050 : term161 = True.
Proof. exact (TRANS (@lem5705002) (@lem5705049)). Qed.
Lemma lem5705051 : term160 = True.
Proof. exact (TRANS (@lem5704993) (@lem5705050)). Qed.
Lemma lem5705052 : True = term160.
Proof. exact (SYM (@lem5705051)). Qed.
Lemma lem5705053 : term160.
Proof. exact (EQ_MP (@lem5705052) (@lem0)). Qed.
Lemma lem5705054 (r : int) (l : int) (x : int) (h1 : term664 r l x) : term181 l x.
Proof. exact (conj (@lem5705053) (@lem5704913 r l x h1)). Qed.
Lemma lem5705056 (x : real) (y : real) : term176 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5705057 (l : int) (x : int) : term182 l x.
Proof. exact (@lem5705056 term75 (term144 l x)). Qed.
Lemma lem5705058 (r : int) (l : int) (x : int) (h1 : term664 r l x) : term183 l x.
Proof. exact (@lem5705057 l x (@lem5705054 r l x h1)). Qed.
Lemma lem5705059 (l : int) (x : int) : (term184 l x) = (term144 l x).
Proof. exact (@lem1982733 (term144 l x)). Qed.
Lemma lem5705060 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5705061 (l : int) (x : int) : (term185 l x) = (term148 l x).
Proof. exact (MK_COMB (@lem5705060) (@lem5705059 l x)). Qed.
Lemma lem5705062 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem5705063 (l : int) (x : int) : (term183 l x) = (term149 l x).
Proof. exact (MK_COMB (@lem5705061 l x) (@lem5705062)). Qed.
Lemma lem5705064 (r : int) (l : int) (x : int) (h1 : term664 r l x) : term149 l x.
Proof. exact (EQ_MP (@lem5705063 l x) (@lem5705058 r l x h1)). Qed.
Lemma lem5705065 (r : int) (l : int) (x : int) (h1 : term664 r l x) : term588 l x.
Proof. exact (conj (@lem5705064 r l x h1) (@lem5704990 r l x h1)). Qed.
Lemma lem5705067 (x : real) (y : real) : term187 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5705068 (l : int) (x : int) : term589 l x.
Proof. exact (@lem5705067 (term144 l x) (term561 l x)). Qed.
Lemma lem5705069 (r : int) (l : int) (x : int) (h1 : term664 r l x) : term590 l x.
Proof. exact (@lem5705068 l x (@lem5705065 r l x h1)). Qed.
Lemma lem5705070 (l : int) (x : int) : (term591 l x) = (term592 l x).
Proof. exact (@lem1982753 (real_of_int l) (term93 l) (term130 x) (term593 x)). Qed.
Lemma lem5705071 (l : int) : (term229 l) = (term195 l).
Proof. exact (@lem1982715 term103 (real_of_int l)). Qed.
Lemma lem5705073 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5705074 : term75 = term108.
Proof. exact (@lem5705073 term76). Qed.
Lemma lem5705076 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5705077 : term103 = term111.
Proof. exact (@lem5705076 term76). Qed.
Lemma lem5705078 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5705079 : term196 = term197.
Proof. exact (MK_COMB (@lem5705078) (@lem5705077)). Qed.
Lemma lem5705080 : term198 = term199.
Proof. exact (MK_COMB (@lem5705079) (@lem5705074)). Qed.
Lemma lem5705081 : term200.
Proof. exact (@lem1981473 term103 term75 term75 term75 term81 term75). Qed.
Lemma lem5705083 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5705084 : term161 = term168.
Proof. exact (@lem5705083 (NUMERAL 0) term76). Qed.
Lemma lem5705085 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5705086 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5705087 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5705086 h1) (fun h1 : term168 = True => @lem5705085)). Qed.
Lemma lem5705088 : term168 = True.
Proof. exact (EQ_MP (@lem5705087) (@lem5705085)). Qed.
Lemma lem5705089 : term161 = True.
Proof. exact (TRANS (@lem5705084) (@lem5705088)). Qed.
Lemma lem5705090 : True = term161.
Proof. exact (SYM (@lem5705089)). Qed.
Lemma lem5705091 : term161.
Proof. exact (EQ_MP (@lem5705090) (@lem0)). Qed.
Lemma lem5705092 : term201.
Proof. exact (@lem5705081 (@lem5705091)). Qed.
Lemma lem5705094 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5705095 : term161 = term168.
Proof. exact (@lem5705094 (NUMERAL 0) term76). Qed.
Lemma lem5705096 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5705097 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5705098 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5705097 h1) (fun h1 : term168 = True => @lem5705096)). Qed.
Lemma lem5705099 : term168 = True.
Proof. exact (EQ_MP (@lem5705098) (@lem5705096)). Qed.
Lemma lem5705100 : term161 = True.
Proof. exact (TRANS (@lem5705095) (@lem5705099)). Qed.
Lemma lem5705101 : True = term161.
Proof. exact (SYM (@lem5705100)). Qed.
Lemma lem5705102 : term161.
Proof. exact (EQ_MP (@lem5705101) (@lem0)). Qed.
Lemma lem5705103 : term202.
Proof. exact (@lem5705092 (@lem5705102)). Qed.
Lemma lem5705105 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5705106 : term161 = term168.
Proof. exact (@lem5705105 (NUMERAL 0) term76). Qed.
Lemma lem5705107 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5705108 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5705109 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5705108 h1) (fun h1 : term168 = True => @lem5705107)). Qed.
Lemma lem5705110 : term168 = True.
Proof. exact (EQ_MP (@lem5705109) (@lem5705107)). Qed.
Lemma lem5705111 : term161 = True.
Proof. exact (TRANS (@lem5705106) (@lem5705110)). Qed.
Lemma lem5705112 : True = term161.
Proof. exact (SYM (@lem5705111)). Qed.
Lemma lem5705113 : term161.
Proof. exact (EQ_MP (@lem5705112) (@lem0)). Qed.
Lemma lem5705114 : term203.
Proof. exact (@lem5705103 (@lem5705113)). Qed.
Lemma lem5705116 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5705117 : term119 = term120.
Proof. exact (@lem5705116 term76 term76). Qed.
Lemma lem5705118 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5705119 : term122 = term76.
Proof. exact (EQ_MP (@lem5705118) (@lem940073)). Qed.
Lemma lem5705120 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5705121 : term120 = term75.
Proof. exact (MK_COMB (@lem5705120) (@lem5705119)). Qed.
Lemma lem5705122 : term119 = term75.
Proof. exact (TRANS (@lem5705117) (@lem5705121)). Qed.
Lemma lem5705124 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5705125 : term114 = term125.
Proof. exact (@lem5705124 term76 term76). Qed.
Lemma lem5705126 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5705127 : term122 = term76.
Proof. exact (EQ_MP (@lem5705126) (@lem940073)). Qed.
Lemma lem5705128 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5705129 : term120 = term75.
Proof. exact (MK_COMB (@lem5705128) (@lem5705127)). Qed.
Lemma lem5705130 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5705131 : term125 = term103.
Proof. exact (MK_COMB (@lem5705130) (@lem5705129)). Qed.
Lemma lem5705132 : term114 = term103.
Proof. exact (TRANS (@lem5705125) (@lem5705131)). Qed.
Lemma lem5705133 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5705134 : term204 = term196.
Proof. exact (MK_COMB (@lem5705133) (@lem5705132)). Qed.
Lemma lem5705135 : term205 = term198.
Proof. exact (MK_COMB (@lem5705134) (@lem5705122)). Qed.
Lemma lem5705137 (m : nat) : (term206 m) = term81.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5705138 : term198 = term81.
Proof. exact (@lem5705137 term76). Qed.
Lemma lem5705139 : term205 = term81.
Proof. exact (TRANS (@lem5705135) (@lem5705138)). Qed.
Lemma lem5705140 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5705141 : term207 = term208.
Proof. exact (MK_COMB (@lem5705140) (@lem5705139)). Qed.
Lemma lem5705142 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem5705143 : term209 = term173.
Proof. exact (MK_COMB (@lem5705141) (@lem5705142)). Qed.
Lemma lem5705145 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5705146 : term173 = term81.
Proof. exact (@lem5705145 term76). Qed.
Lemma lem5705147 : term209 = term81.
Proof. exact (TRANS (@lem5705143) (@lem5705146)). Qed.
Lemma lem5705149 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5705150 : term119 = term120.
Proof. exact (@lem5705149 term76 term76). Qed.
Lemma lem5705151 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5705152 : term122 = term76.
Proof. exact (EQ_MP (@lem5705151) (@lem940073)). Qed.
Lemma lem5705153 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5705154 : term120 = term75.
Proof. exact (MK_COMB (@lem5705153) (@lem5705152)). Qed.
Lemma lem5705155 : term119 = term75.
Proof. exact (TRANS (@lem5705150) (@lem5705154)). Qed.
Lemma lem5705156 : term208 = term208.
Proof. exact (eq_refl term208). Qed.
Lemma lem5705157 : term210 = term173.
Proof. exact (MK_COMB (@lem5705156) (@lem5705155)). Qed.
Lemma lem5705159 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5705160 : term173 = term81.
Proof. exact (@lem5705159 term76). Qed.
Lemma lem5705161 : term210 = term81.
Proof. exact (TRANS (@lem5705157) (@lem5705160)). Qed.
Lemma lem5705162 : term81 = term210.
Proof. exact (SYM (@lem5705161)). Qed.
Lemma lem5705163 : term209 = term210.
Proof. exact (TRANS (@lem5705147) (@lem5705162)). Qed.
Lemma lem5705164 : term199 = term162.
Proof. exact (@lem5705114 (@lem5705163)). Qed.
Lemma lem5705165 : term198 = term162.
Proof. exact (TRANS (@lem5705080) (@lem5705164)). Qed.
Lemma lem5705167 (x : real) : (term128 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5705168 : term162 = term81.
Proof. exact (@lem5705167 term81). Qed.
Lemma lem5705169 : term198 = term81.
Proof. exact (TRANS (@lem5705165) (@lem5705168)). Qed.
Lemma lem5705170 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5705171 : term211 = term208.
Proof. exact (MK_COMB (@lem5705170) (@lem5705169)). Qed.
Lemma lem5705172 (l : int) : (real_of_int l) = (real_of_int l).
Proof. exact (eq_refl (real_of_int l)). Qed.
Lemma lem5705173 (l : int) : (term195 l) = (term212 l).
Proof. exact (MK_COMB (@lem5705171) (@lem5705172 l)). Qed.
Lemma lem5705174 (l : int) : (term229 l) = (term212 l).
Proof. exact (TRANS (@lem5705071 l) (@lem5705173 l)). Qed.
Lemma lem5705175 (l : int) : (term212 l) = term81.
Proof. exact (@lem1982719 (real_of_int l)). Qed.
Lemma lem5705176 (l : int) : (term229 l) = term81.
Proof. exact (TRANS (@lem5705174 l) (@lem5705175 l)). Qed.
Lemma lem5705177 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5705178 (l : int) : (term230 l) = term145.
Proof. exact (MK_COMB (@lem5705177) (@lem5705176 l)). Qed.
Lemma lem5705179 (x : int) : (term594 x) = (term595 x).
Proof. exact (@lem1982753 (term93 x) (real_of_int x) term103 term103). Qed.
Lemma lem5705180 (x : int) : (term194 x) = (term195 x).
Proof. exact (@lem1982713 term103 (real_of_int x)). Qed.
Lemma lem5705182 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5705183 : term75 = term108.
Proof. exact (@lem5705182 term76). Qed.
Lemma lem5705185 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5705186 : term103 = term111.
Proof. exact (@lem5705185 term76). Qed.
Lemma lem5705187 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5705188 : term196 = term197.
Proof. exact (MK_COMB (@lem5705187) (@lem5705186)). Qed.
Lemma lem5705189 : term198 = term199.
Proof. exact (MK_COMB (@lem5705188) (@lem5705183)). Qed.
Lemma lem5705190 : term200.
Proof. exact (@lem1981473 term103 term75 term75 term75 term81 term75). Qed.
Lemma lem5705192 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5705193 : term161 = term168.
Proof. exact (@lem5705192 (NUMERAL 0) term76). Qed.
Lemma lem5705194 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5705195 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5705196 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5705195 h1) (fun h1 : term168 = True => @lem5705194)). Qed.
Lemma lem5705197 : term168 = True.
Proof. exact (EQ_MP (@lem5705196) (@lem5705194)). Qed.
Lemma lem5705198 : term161 = True.
Proof. exact (TRANS (@lem5705193) (@lem5705197)). Qed.
Lemma lem5705199 : True = term161.
Proof. exact (SYM (@lem5705198)). Qed.
Lemma lem5705200 : term161.
Proof. exact (EQ_MP (@lem5705199) (@lem0)). Qed.
Lemma lem5705201 : term201.
Proof. exact (@lem5705190 (@lem5705200)). Qed.
Lemma lem5705203 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5705204 : term161 = term168.
Proof. exact (@lem5705203 (NUMERAL 0) term76). Qed.
Lemma lem5705205 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5705206 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5705207 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5705206 h1) (fun h1 : term168 = True => @lem5705205)). Qed.
Lemma lem5705208 : term168 = True.
Proof. exact (EQ_MP (@lem5705207) (@lem5705205)). Qed.
Lemma lem5705209 : term161 = True.
Proof. exact (TRANS (@lem5705204) (@lem5705208)). Qed.
Lemma lem5705210 : True = term161.
Proof. exact (SYM (@lem5705209)). Qed.
Lemma lem5705211 : term161.
Proof. exact (EQ_MP (@lem5705210) (@lem0)). Qed.
Lemma lem5705212 : term202.
Proof. exact (@lem5705201 (@lem5705211)). Qed.
Lemma lem5705214 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5705215 : term161 = term168.
Proof. exact (@lem5705214 (NUMERAL 0) term76). Qed.
Lemma lem5705216 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5705217 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5705218 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5705217 h1) (fun h1 : term168 = True => @lem5705216)). Qed.
Lemma lem5705219 : term168 = True.
Proof. exact (EQ_MP (@lem5705218) (@lem5705216)). Qed.
Lemma lem5705220 : term161 = True.
Proof. exact (TRANS (@lem5705215) (@lem5705219)). Qed.
Lemma lem5705221 : True = term161.
Proof. exact (SYM (@lem5705220)). Qed.
Lemma lem5705222 : term161.
Proof. exact (EQ_MP (@lem5705221) (@lem0)). Qed.
Lemma lem5705223 : term203.
Proof. exact (@lem5705212 (@lem5705222)). Qed.
Lemma lem5705225 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5705226 : term119 = term120.
Proof. exact (@lem5705225 term76 term76). Qed.
Lemma lem5705227 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5705228 : term122 = term76.
Proof. exact (EQ_MP (@lem5705227) (@lem940073)). Qed.
Lemma lem5705229 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5705230 : term120 = term75.
Proof. exact (MK_COMB (@lem5705229) (@lem5705228)). Qed.
Lemma lem5705231 : term119 = term75.
Proof. exact (TRANS (@lem5705226) (@lem5705230)). Qed.
Lemma lem5705233 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5705234 : term114 = term125.
Proof. exact (@lem5705233 term76 term76). Qed.
Lemma lem5705235 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5705236 : term122 = term76.
Proof. exact (EQ_MP (@lem5705235) (@lem940073)). Qed.
Lemma lem5705237 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5705238 : term120 = term75.
Proof. exact (MK_COMB (@lem5705237) (@lem5705236)). Qed.
Lemma lem5705239 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5705240 : term125 = term103.
Proof. exact (MK_COMB (@lem5705239) (@lem5705238)). Qed.
Lemma lem5705241 : term114 = term103.
Proof. exact (TRANS (@lem5705234) (@lem5705240)). Qed.
Lemma lem5705242 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5705243 : term204 = term196.
Proof. exact (MK_COMB (@lem5705242) (@lem5705241)). Qed.
Lemma lem5705244 : term205 = term198.
Proof. exact (MK_COMB (@lem5705243) (@lem5705231)). Qed.
Lemma lem5705246 (m : nat) : (term206 m) = term81.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5705247 : term198 = term81.
Proof. exact (@lem5705246 term76). Qed.
Lemma lem5705248 : term205 = term81.
Proof. exact (TRANS (@lem5705244) (@lem5705247)). Qed.
Lemma lem5705249 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5705250 : term207 = term208.
Proof. exact (MK_COMB (@lem5705249) (@lem5705248)). Qed.
Lemma lem5705251 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem5705252 : term209 = term173.
Proof. exact (MK_COMB (@lem5705250) (@lem5705251)). Qed.
Lemma lem5705254 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5705255 : term173 = term81.
Proof. exact (@lem5705254 term76). Qed.
Lemma lem5705256 : term209 = term81.
Proof. exact (TRANS (@lem5705252) (@lem5705255)). Qed.
Lemma lem5705258 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5705259 : term119 = term120.
Proof. exact (@lem5705258 term76 term76). Qed.
Lemma lem5705260 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5705261 : term122 = term76.
Proof. exact (EQ_MP (@lem5705260) (@lem940073)). Qed.
Lemma lem5705262 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5705263 : term120 = term75.
Proof. exact (MK_COMB (@lem5705262) (@lem5705261)). Qed.
Lemma lem5705264 : term119 = term75.
Proof. exact (TRANS (@lem5705259) (@lem5705263)). Qed.
Lemma lem5705265 : term208 = term208.
Proof. exact (eq_refl term208). Qed.
Lemma lem5705266 : term210 = term173.
Proof. exact (MK_COMB (@lem5705265) (@lem5705264)). Qed.
Lemma lem5705268 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5705269 : term173 = term81.
Proof. exact (@lem5705268 term76). Qed.
Lemma lem5705270 : term210 = term81.
Proof. exact (TRANS (@lem5705266) (@lem5705269)). Qed.
Lemma lem5705271 : term81 = term210.
Proof. exact (SYM (@lem5705270)). Qed.
Lemma lem5705272 : term209 = term210.
Proof. exact (TRANS (@lem5705256) (@lem5705271)). Qed.
Lemma lem5705273 : term199 = term162.
Proof. exact (@lem5705223 (@lem5705272)). Qed.
Lemma lem5705274 : term198 = term162.
Proof. exact (TRANS (@lem5705189) (@lem5705273)). Qed.
Lemma lem5705276 (x : real) : (term128 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5705277 : term162 = term81.
Proof. exact (@lem5705276 term81). Qed.
Lemma lem5705278 : term198 = term81.
Proof. exact (TRANS (@lem5705274) (@lem5705277)). Qed.
Lemma lem5705279 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5705280 : term211 = term208.
Proof. exact (MK_COMB (@lem5705279) (@lem5705278)). Qed.
Lemma lem5705281 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem5705282 (x : int) : (term195 x) = (term212 x).
Proof. exact (MK_COMB (@lem5705280) (@lem5705281 x)). Qed.
Lemma lem5705283 (x : int) : (term194 x) = (term212 x).
Proof. exact (TRANS (@lem5705180 x) (@lem5705282 x)). Qed.
Lemma lem5705284 (x : int) : (term212 x) = term81.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem5705285 (x : int) : (term194 x) = term81.
Proof. exact (TRANS (@lem5705283 x) (@lem5705284 x)). Qed.
Lemma lem5705286 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5705287 (x : int) : (term213 x) = term145.
Proof. exact (MK_COMB (@lem5705286) (@lem5705285 x)). Qed.
Lemma lem5705289 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5705290 : term103 = term111.
Proof. exact (@lem5705289 term76). Qed.
Lemma lem5705292 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5705293 : term103 = term111.
Proof. exact (@lem5705292 term76). Qed.
Lemma lem5705294 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5705295 : term196 = term197.
Proof. exact (MK_COMB (@lem5705294) (@lem5705293)). Qed.
Lemma lem5705296 : term596 = term597.
Proof. exact (MK_COMB (@lem5705295) (@lem5705290)). Qed.
Lemma lem5705297 : term598.
Proof. exact (@lem1981473 term103 term75 term103 term75 term599 term75). Qed.
Lemma lem5705299 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5705300 : term161 = term168.
Proof. exact (@lem5705299 (NUMERAL 0) term76). Qed.
Lemma lem5705301 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5705302 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5705303 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5705302 h1) (fun h1 : term168 = True => @lem5705301)). Qed.
Lemma lem5705304 : term168 = True.
Proof. exact (EQ_MP (@lem5705303) (@lem5705301)). Qed.
Lemma lem5705305 : term161 = True.
Proof. exact (TRANS (@lem5705300) (@lem5705304)). Qed.
Lemma lem5705306 : True = term161.
Proof. exact (SYM (@lem5705305)). Qed.
Lemma lem5705307 : term161.
Proof. exact (EQ_MP (@lem5705306) (@lem0)). Qed.
Lemma lem5705308 : term600.
Proof. exact (@lem5705297 (@lem5705307)). Qed.
Lemma lem5705310 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5705311 : term161 = term168.
Proof. exact (@lem5705310 (NUMERAL 0) term76). Qed.
Lemma lem5705312 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5705313 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5705314 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5705313 h1) (fun h1 : term168 = True => @lem5705312)). Qed.
Lemma lem5705315 : term168 = True.
Proof. exact (EQ_MP (@lem5705314) (@lem5705312)). Qed.
Lemma lem5705316 : term161 = True.
Proof. exact (TRANS (@lem5705311) (@lem5705315)). Qed.
Lemma lem5705317 : True = term161.
Proof. exact (SYM (@lem5705316)). Qed.
Lemma lem5705318 : term161.
Proof. exact (EQ_MP (@lem5705317) (@lem0)). Qed.
Lemma lem5705319 : term601.
Proof. exact (@lem5705308 (@lem5705318)). Qed.
Lemma lem5705321 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5705322 : term161 = term168.
Proof. exact (@lem5705321 (NUMERAL 0) term76). Qed.
Lemma lem5705323 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5705324 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5705325 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5705324 h1) (fun h1 : term168 = True => @lem5705323)). Qed.
Lemma lem5705326 : term168 = True.
Proof. exact (EQ_MP (@lem5705325) (@lem5705323)). Qed.
Lemma lem5705327 : term161 = True.
Proof. exact (TRANS (@lem5705322) (@lem5705326)). Qed.
Lemma lem5705328 : True = term161.
Proof. exact (SYM (@lem5705327)). Qed.
Lemma lem5705329 : term161.
Proof. exact (EQ_MP (@lem5705328) (@lem0)). Qed.
Lemma lem5705330 : term602.
Proof. exact (@lem5705319 (@lem5705329)). Qed.
Lemma lem5705332 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5705333 : term114 = term125.
Proof. exact (@lem5705332 term76 term76). Qed.
Lemma lem5705334 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5705335 : term122 = term76.
Proof. exact (EQ_MP (@lem5705334) (@lem940073)). Qed.
Lemma lem5705336 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5705337 : term120 = term75.
Proof. exact (MK_COMB (@lem5705336) (@lem5705335)). Qed.
Lemma lem5705338 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5705339 : term125 = term103.
Proof. exact (MK_COMB (@lem5705338) (@lem5705337)). Qed.
Lemma lem5705340 : term114 = term103.
Proof. exact (TRANS (@lem5705333) (@lem5705339)). Qed.
Lemma lem5705342 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5705343 : term114 = term125.
Proof. exact (@lem5705342 term76 term76). Qed.
Lemma lem5705344 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5705345 : term122 = term76.
Proof. exact (EQ_MP (@lem5705344) (@lem940073)). Qed.
Lemma lem5705346 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5705347 : term120 = term75.
Proof. exact (MK_COMB (@lem5705346) (@lem5705345)). Qed.
Lemma lem5705348 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5705349 : term125 = term103.
Proof. exact (MK_COMB (@lem5705348) (@lem5705347)). Qed.
Lemma lem5705350 : term114 = term103.
Proof. exact (TRANS (@lem5705343) (@lem5705349)). Qed.
Lemma lem5705351 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5705352 : term204 = term196.
Proof. exact (MK_COMB (@lem5705351) (@lem5705350)). Qed.
Lemma lem5705353 : term603 = term596.
Proof. exact (MK_COMB (@lem5705352) (@lem5705340)). Qed.
Lemma lem5705354 : term596 = term604.
Proof. exact (@lem1367763 term76 term76). Qed.
Lemma lem5705355 : term605 = term606.
Proof. exact (@lem706885). Qed.
Lemma lem5705356 : (term605 = term606) = (term607 = term608).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term606). Qed.
Lemma lem5705357 : term607 = term608.
Proof. exact (EQ_MP (@lem5705356) (@lem5705355)). Qed.
Lemma lem5705358 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5705359 : term609 = term610.
Proof. exact (MK_COMB (@lem5705358) (@lem5705357)). Qed.
Lemma lem5705360 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5705361 : term604 = term599.
Proof. exact (MK_COMB (@lem5705360) (@lem5705359)). Qed.
Lemma lem5705362 : term596 = term599.
Proof. exact (TRANS (@lem5705354) (@lem5705361)). Qed.
Lemma lem5705363 : term603 = term599.
Proof. exact (TRANS (@lem5705353) (@lem5705362)). Qed.
Lemma lem5705364 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5705365 : term611 = term612.
Proof. exact (MK_COMB (@lem5705364) (@lem5705363)). Qed.
Lemma lem5705366 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem5705367 : term613 = term614.
Proof. exact (MK_COMB (@lem5705365) (@lem5705366)). Qed.
Lemma lem5705369 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5705370 : term614 = term615.
Proof. exact (@lem5705369 term608 term76). Qed.
Lemma lem5705371 : term616 = term606.
Proof. exact (@lem996237 term606). Qed.
Lemma lem5705372 : (term616 = term606) = (term617 = term608).
Proof. exact (@lem1007663 term606 (BIT1 0) term606). Qed.
Lemma lem5705373 : term617 = term608.
Proof. exact (EQ_MP (@lem5705372) (@lem5705371)). Qed.
Lemma lem5705374 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5705375 : term618 = term610.
Proof. exact (MK_COMB (@lem5705374) (@lem5705373)). Qed.
Lemma lem5705376 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5705377 : term615 = term599.
Proof. exact (MK_COMB (@lem5705376) (@lem5705375)). Qed.
Lemma lem5705378 : term614 = term599.
Proof. exact (TRANS (@lem5705370) (@lem5705377)). Qed.
Lemma lem5705379 : term613 = term599.
Proof. exact (TRANS (@lem5705367) (@lem5705378)). Qed.
Lemma lem5705381 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5705382 : term119 = term120.
Proof. exact (@lem5705381 term76 term76). Qed.
Lemma lem5705383 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5705384 : term122 = term76.
Proof. exact (EQ_MP (@lem5705383) (@lem940073)). Qed.
Lemma lem5705385 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5705386 : term120 = term75.
Proof. exact (MK_COMB (@lem5705385) (@lem5705384)). Qed.
Lemma lem5705387 : term119 = term75.
Proof. exact (TRANS (@lem5705382) (@lem5705386)). Qed.
Lemma lem5705388 : term612 = term612.
Proof. exact (eq_refl term612). Qed.
Lemma lem5705389 : term619 = term614.
Proof. exact (MK_COMB (@lem5705388) (@lem5705387)). Qed.
Lemma lem5705391 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5705392 : term614 = term615.
Proof. exact (@lem5705391 term608 term76). Qed.
Lemma lem5705393 : term616 = term606.
Proof. exact (@lem996237 term606). Qed.
Lemma lem5705394 : (term616 = term606) = (term617 = term608).
Proof. exact (@lem1007663 term606 (BIT1 0) term606). Qed.
Lemma lem5705395 : term617 = term608.
Proof. exact (EQ_MP (@lem5705394) (@lem5705393)). Qed.
Lemma lem5705396 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5705397 : term618 = term610.
Proof. exact (MK_COMB (@lem5705396) (@lem5705395)). Qed.
Lemma lem5705398 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5705399 : term615 = term599.
Proof. exact (MK_COMB (@lem5705398) (@lem5705397)). Qed.
Lemma lem5705400 : term614 = term599.
Proof. exact (TRANS (@lem5705392) (@lem5705399)). Qed.
Lemma lem5705401 : term619 = term599.
Proof. exact (TRANS (@lem5705389) (@lem5705400)). Qed.
Lemma lem5705402 : term599 = term619.
Proof. exact (SYM (@lem5705401)). Qed.
Lemma lem5705403 : term613 = term619.
Proof. exact (TRANS (@lem5705379) (@lem5705402)). Qed.
Lemma lem5705404 : term597 = term620.
Proof. exact (@lem5705330 (@lem5705403)). Qed.
Lemma lem5705405 : term596 = term620.
Proof. exact (TRANS (@lem5705296) (@lem5705404)). Qed.
Lemma lem5705407 (x : real) : (term128 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5705408 : term620 = term599.
Proof. exact (@lem5705407 term599). Qed.
Lemma lem5705409 : term596 = term599.
Proof. exact (TRANS (@lem5705405) (@lem5705408)). Qed.
Lemma lem5705410 (x : int) : (term595 x) = term621.
Proof. exact (MK_COMB (@lem5705287 x) (@lem5705409)). Qed.
Lemma lem5705411 (x : int) : (term594 x) = term621.
Proof. exact (TRANS (@lem5705179 x) (@lem5705410 x)). Qed.
Lemma lem5705412 : term621 = term599.
Proof. exact (@lem1982721 term599). Qed.
Lemma lem5705413 (x : int) : (term594 x) = term599.
Proof. exact (TRANS (@lem5705411 x) (@lem5705412)). Qed.
Lemma lem5705414 (l : int) (x : int) : (term592 l x) = term621.
Proof. exact (MK_COMB (@lem5705178 l) (@lem5705413 x)). Qed.
Lemma lem5705415 (l : int) (x : int) : (term591 l x) = term621.
Proof. exact (TRANS (@lem5705070 l x) (@lem5705414 l x)). Qed.
Lemma lem5705416 : term621 = term599.
Proof. exact (@lem1982721 term599). Qed.
Lemma lem5705417 (l : int) (x : int) : (term591 l x) = term599.
Proof. exact (TRANS (@lem5705415 l x) (@lem5705416)). Qed.
Lemma lem5705418 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5705419 (l : int) (x : int) : (term622 l x) = term623.
Proof. exact (MK_COMB (@lem5705418) (@lem5705417 l x)). Qed.
Lemma lem5705420 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem5705421 (l : int) (x : int) : (term590 l x) = term624.
Proof. exact (MK_COMB (@lem5705419 l x) (@lem5705420)). Qed.
Lemma lem5705422 (r : int) (l : int) (x : int) (h1 : term664 r l x) : term624.
Proof. exact (EQ_MP (@lem5705421 l x) (@lem5705069 r l x h1)). Qed.
Lemma lem5705424 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5705425 : term624 = term625.
Proof. exact (@lem5705424 term81 term599). Qed.
Lemma lem5705427 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5705428 : term599 = term620.
Proof. exact (@lem5705427 term608). Qed.
Lemma lem5705430 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5705431 : term81 = term162.
Proof. exact (@lem5705430 (NUMERAL 0)). Qed.
Lemma lem5705432 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5705433 : term236 = term237.
Proof. exact (MK_COMB (@lem5705432) (@lem5705431)). Qed.
Lemma lem5705434 : term625 = term626.
Proof. exact (MK_COMB (@lem5705433) (@lem5705428)). Qed.
Lemma lem5705435 : term627.
Proof. exact (@lem1980026 term81 term75 term599 term75). Qed.
Lemma lem5705437 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5705438 : term161 = term168.
Proof. exact (@lem5705437 (NUMERAL 0) term76). Qed.
Lemma lem5705439 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5705440 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5705441 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5705440 h1) (fun h1 : term168 = True => @lem5705439)). Qed.
Lemma lem5705442 : term168 = True.
Proof. exact (EQ_MP (@lem5705441) (@lem5705439)). Qed.
Lemma lem5705443 : term161 = True.
Proof. exact (TRANS (@lem5705438) (@lem5705442)). Qed.
Lemma lem5705444 : True = term161.
Proof. exact (SYM (@lem5705443)). Qed.
Lemma lem5705445 : term161.
Proof. exact (EQ_MP (@lem5705444) (@lem0)). Qed.
Lemma lem5705446 : term628.
Proof. exact (@lem5705435 (@lem5705445)). Qed.
Lemma lem5705448 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5705449 : term161 = term168.
Proof. exact (@lem5705448 (NUMERAL 0) term76). Qed.
Lemma lem5705450 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5705451 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5705452 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5705451 h1) (fun h1 : term168 = True => @lem5705450)). Qed.
Lemma lem5705453 : term168 = True.
Proof. exact (EQ_MP (@lem5705452) (@lem5705450)). Qed.
Lemma lem5705454 : term161 = True.
Proof. exact (TRANS (@lem5705449) (@lem5705453)). Qed.
Lemma lem5705455 : True = term161.
Proof. exact (SYM (@lem5705454)). Qed.
Lemma lem5705456 : term161.
Proof. exact (EQ_MP (@lem5705455) (@lem0)). Qed.
Lemma lem5705457 : term626 = term629.
Proof. exact (@lem5705446 (@lem5705456)). Qed.
Lemma lem5705459 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5705460 : term614 = term615.
Proof. exact (@lem5705459 term608 term76). Qed.
Lemma lem5705461 : term616 = term606.
Proof. exact (@lem996237 term606). Qed.
Lemma lem5705462 : (term616 = term606) = (term617 = term608).
Proof. exact (@lem1007663 term606 (BIT1 0) term606). Qed.
Lemma lem5705463 : term617 = term608.
Proof. exact (EQ_MP (@lem5705462) (@lem5705461)). Qed.
Lemma lem5705464 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5705465 : term618 = term610.
Proof. exact (MK_COMB (@lem5705464) (@lem5705463)). Qed.
Lemma lem5705466 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5705467 : term615 = term599.
Proof. exact (MK_COMB (@lem5705466) (@lem5705465)). Qed.
Lemma lem5705468 : term614 = term599.
Proof. exact (TRANS (@lem5705460) (@lem5705467)). Qed.
Lemma lem5705470 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5705471 : term173 = term81.
Proof. exact (@lem5705470 term76). Qed.
Lemma lem5705472 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5705473 : term242 = term236.
Proof. exact (MK_COMB (@lem5705472) (@lem5705471)). Qed.
Lemma lem5705474 : term629 = term625.
Proof. exact (MK_COMB (@lem5705473) (@lem5705468)). Qed.
Lemma lem5705476 (m : nat) (n : nat) : (term243 m n) = (term244 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5705477 : term625 = term630.
Proof. exact (@lem5705476 (NUMERAL 0) term608). Qed.
Lemma lem5705478 : term631 = term606.
Proof. exact (@lem912803). Qed.
Lemma lem5705479 (h1 : term631 = term606) : (term608 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term606 h1). Qed.
Lemma lem5705480 : (term631 = term606) = ((term608 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term631 = term606 => @lem5705479 h1) (fun h1 : (term608 = (NUMERAL 0)) = False => @lem5705478)). Qed.
Lemma lem5705481 : (term608 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5705480) (@lem5705478)). Qed.
Lemma lem5705482 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5705483 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5705484 : term246 = (and True).
Proof. exact (MK_COMB (@lem5705483) (@lem5705482)). Qed.
Lemma lem5705485 : term630 = (True /\ False).
Proof. exact (MK_COMB (@lem5705484) (@lem5705481)). Qed.
Lemma lem5705487 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5705488 : term630 = False.
Proof. exact (TRANS (@lem5705485) (@lem5705487)). Qed.
Lemma lem5705489 : term625 = False.
Proof. exact (TRANS (@lem5705477) (@lem5705488)). Qed.
Lemma lem5705490 : term629 = False.
Proof. exact (TRANS (@lem5705474) (@lem5705489)). Qed.
Lemma lem5705491 : term626 = False.
Proof. exact (TRANS (@lem5705457) (@lem5705490)). Qed.
Lemma lem5705492 : term625 = False.
Proof. exact (TRANS (@lem5705434) (@lem5705491)). Qed.
Lemma lem5705493 : term624 = False.
Proof. exact (TRANS (@lem5705425) (@lem5705492)). Qed.
Lemma lem5705494 (r : int) (l : int) (x : int) (h1 : term664 r l x) : False.
Proof. exact (EQ_MP (@lem5705493) (@lem5705422 r l x h1)). Qed.
Lemma lem5705495 (l : int) (r : int) (x : int) (h1 : term665 l r x) : term665 l r x.
Proof. exact (h1). Qed.
Lemma lem5705496 (l : int) (r : int) (x : int) (h1 : term665 l r x) : term563 r x.
Proof. exact (proj2 (@lem5705495 l r x h1)). Qed.
Lemma lem5705497 (l : int) (r : int) (x : int) (h1 : term665 l r x) : term656 l r x.
Proof. exact (proj1 (@lem5705495 l r x h1)). Qed.
Lemma lem5705498 (l : int) (r : int) (x : int) (h1 : term665 l r x) : term155 r x.
Proof. exact (proj2 (@lem5705497 l r x h1)). Qed.
Lemma lem5705501 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5705502 : term160 = term161.
Proof. exact (@lem5705501 term81 term75). Qed.
Lemma lem5705504 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5705505 : term75 = term108.
Proof. exact (@lem5705504 term76). Qed.
Lemma lem5705507 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5705508 : term81 = term162.
Proof. exact (@lem5705507 (NUMERAL 0)). Qed.
Lemma lem5705509 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5705510 : term163 = term164.
Proof. exact (MK_COMB (@lem5705509) (@lem5705508)). Qed.
Lemma lem5705511 : term161 = term165.
Proof. exact (MK_COMB (@lem5705510) (@lem5705505)). Qed.
Lemma lem5705512 : term166.
Proof. exact (@lem1980255 term81 term75 term75 term75). Qed.
Lemma lem5705514 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5705515 : term161 = term168.
Proof. exact (@lem5705514 (NUMERAL 0) term76). Qed.
Lemma lem5705516 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5705517 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5705518 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5705517 h1) (fun h1 : term168 = True => @lem5705516)). Qed.
Lemma lem5705519 : term168 = True.
Proof. exact (EQ_MP (@lem5705518) (@lem5705516)). Qed.
Lemma lem5705520 : term161 = True.
Proof. exact (TRANS (@lem5705515) (@lem5705519)). Qed.
Lemma lem5705521 : True = term161.
Proof. exact (SYM (@lem5705520)). Qed.
Lemma lem5705522 : term161.
Proof. exact (EQ_MP (@lem5705521) (@lem0)). Qed.
Lemma lem5705523 : term170.
Proof. exact (@lem5705512 (@lem5705522)). Qed.
Lemma lem5705525 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5705526 : term161 = term168.
Proof. exact (@lem5705525 (NUMERAL 0) term76). Qed.
Lemma lem5705527 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5705528 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5705529 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5705528 h1) (fun h1 : term168 = True => @lem5705527)). Qed.
Lemma lem5705530 : term168 = True.
Proof. exact (EQ_MP (@lem5705529) (@lem5705527)). Qed.
Lemma lem5705531 : term161 = True.
Proof. exact (TRANS (@lem5705526) (@lem5705530)). Qed.
Lemma lem5705532 : True = term161.
Proof. exact (SYM (@lem5705531)). Qed.
Lemma lem5705533 : term161.
Proof. exact (EQ_MP (@lem5705532) (@lem0)). Qed.
Lemma lem5705534 : term165 = term171.
Proof. exact (@lem5705523 (@lem5705533)). Qed.
Lemma lem5705536 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5705537 : term119 = term120.
Proof. exact (@lem5705536 term76 term76). Qed.
Lemma lem5705538 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5705539 : term122 = term76.
Proof. exact (EQ_MP (@lem5705538) (@lem940073)). Qed.
Lemma lem5705540 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5705541 : term120 = term75.
Proof. exact (MK_COMB (@lem5705540) (@lem5705539)). Qed.
Lemma lem5705542 : term119 = term75.
Proof. exact (TRANS (@lem5705537) (@lem5705541)). Qed.
Lemma lem5705544 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5705545 : term173 = term81.
Proof. exact (@lem5705544 term76). Qed.
Lemma lem5705546 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5705547 : term174 = term163.
Proof. exact (MK_COMB (@lem5705546) (@lem5705545)). Qed.
Lemma lem5705548 : term171 = term161.
Proof. exact (MK_COMB (@lem5705547) (@lem5705542)). Qed.
Lemma lem5705550 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5705551 : term161 = term168.
Proof. exact (@lem5705550 (NUMERAL 0) term76). Qed.
Lemma lem5705552 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5705553 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5705554 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5705553 h1) (fun h1 : term168 = True => @lem5705552)). Qed.
Lemma lem5705555 : term168 = True.
Proof. exact (EQ_MP (@lem5705554) (@lem5705552)). Qed.
Lemma lem5705556 : term161 = True.
Proof. exact (TRANS (@lem5705551) (@lem5705555)). Qed.
Lemma lem5705557 : term171 = True.
Proof. exact (TRANS (@lem5705548) (@lem5705556)). Qed.
Lemma lem5705558 : term165 = True.
Proof. exact (TRANS (@lem5705534) (@lem5705557)). Qed.
Lemma lem5705559 : term161 = True.
Proof. exact (TRANS (@lem5705511) (@lem5705558)). Qed.
Lemma lem5705560 : term160 = True.
Proof. exact (TRANS (@lem5705502) (@lem5705559)). Qed.
Lemma lem5705561 : True = term160.
Proof. exact (SYM (@lem5705560)). Qed.
Lemma lem5705562 : term160.
Proof. exact (EQ_MP (@lem5705561) (@lem0)). Qed.
Lemma lem5705563 (l : int) (r : int) (x : int) (h1 : term665 l r x) : term583 r x.
Proof. exact (conj (@lem5705562) (@lem5705496 l r x h1)). Qed.
Lemma lem5705565 (x : real) (y : real) : term176 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5705566 (r : int) (x : int) : term584 r x.
Proof. exact (@lem5705565 term75 (term561 r x)). Qed.
Lemma lem5705567 (l : int) (r : int) (x : int) (h1 : term665 l r x) : term585 r x.
Proof. exact (@lem5705566 r x (@lem5705563 l r x h1)). Qed.
Lemma lem5705568 (r : int) (x : int) : (term586 r x) = (term561 r x).
Proof. exact (@lem1982733 (term561 r x)). Qed.
Lemma lem5705569 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5705570 (r : int) (x : int) : (term587 r x) = (term562 r x).
Proof. exact (MK_COMB (@lem5705569) (@lem5705568 r x)). Qed.
Lemma lem5705571 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem5705572 (r : int) (x : int) : (term585 r x) = (term563 r x).
Proof. exact (MK_COMB (@lem5705570 r x) (@lem5705571)). Qed.
Lemma lem5705573 (l : int) (r : int) (x : int) (h1 : term665 l r x) : term563 r x.
Proof. exact (EQ_MP (@lem5705572 r x) (@lem5705567 l r x h1)). Qed.
Lemma lem5705575 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5705576 : term160 = term161.
Proof. exact (@lem5705575 term81 term75). Qed.
Lemma lem5705578 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5705579 : term75 = term108.
Proof. exact (@lem5705578 term76). Qed.
Lemma lem5705581 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5705582 : term81 = term162.
Proof. exact (@lem5705581 (NUMERAL 0)). Qed.
Lemma lem5705583 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5705584 : term163 = term164.
Proof. exact (MK_COMB (@lem5705583) (@lem5705582)). Qed.
Lemma lem5705585 : term161 = term165.
Proof. exact (MK_COMB (@lem5705584) (@lem5705579)). Qed.
Lemma lem5705586 : term166.
Proof. exact (@lem1980255 term81 term75 term75 term75). Qed.
Lemma lem5705588 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5705589 : term161 = term168.
Proof. exact (@lem5705588 (NUMERAL 0) term76). Qed.
Lemma lem5705590 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5705591 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5705592 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5705591 h1) (fun h1 : term168 = True => @lem5705590)). Qed.
Lemma lem5705593 : term168 = True.
Proof. exact (EQ_MP (@lem5705592) (@lem5705590)). Qed.
Lemma lem5705594 : term161 = True.
Proof. exact (TRANS (@lem5705589) (@lem5705593)). Qed.
Lemma lem5705595 : True = term161.
Proof. exact (SYM (@lem5705594)). Qed.
Lemma lem5705596 : term161.
Proof. exact (EQ_MP (@lem5705595) (@lem0)). Qed.
Lemma lem5705597 : term170.
Proof. exact (@lem5705586 (@lem5705596)). Qed.
Lemma lem5705599 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5705600 : term161 = term168.
Proof. exact (@lem5705599 (NUMERAL 0) term76). Qed.
Lemma lem5705601 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5705602 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5705603 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5705602 h1) (fun h1 : term168 = True => @lem5705601)). Qed.
Lemma lem5705604 : term168 = True.
Proof. exact (EQ_MP (@lem5705603) (@lem5705601)). Qed.
Lemma lem5705605 : term161 = True.
Proof. exact (TRANS (@lem5705600) (@lem5705604)). Qed.
Lemma lem5705606 : True = term161.
Proof. exact (SYM (@lem5705605)). Qed.
Lemma lem5705607 : term161.
Proof. exact (EQ_MP (@lem5705606) (@lem0)). Qed.
Lemma lem5705608 : term165 = term171.
Proof. exact (@lem5705597 (@lem5705607)). Qed.
Lemma lem5705610 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5705611 : term119 = term120.
Proof. exact (@lem5705610 term76 term76). Qed.
Lemma lem5705612 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5705613 : term122 = term76.
Proof. exact (EQ_MP (@lem5705612) (@lem940073)). Qed.
Lemma lem5705614 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5705615 : term120 = term75.
Proof. exact (MK_COMB (@lem5705614) (@lem5705613)). Qed.
Lemma lem5705616 : term119 = term75.
Proof. exact (TRANS (@lem5705611) (@lem5705615)). Qed.
Lemma lem5705618 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5705619 : term173 = term81.
Proof. exact (@lem5705618 term76). Qed.
Lemma lem5705620 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5705621 : term174 = term163.
Proof. exact (MK_COMB (@lem5705620) (@lem5705619)). Qed.
Lemma lem5705622 : term171 = term161.
Proof. exact (MK_COMB (@lem5705621) (@lem5705616)). Qed.
Lemma lem5705624 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5705625 : term161 = term168.
Proof. exact (@lem5705624 (NUMERAL 0) term76). Qed.
Lemma lem5705626 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5705627 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5705628 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5705627 h1) (fun h1 : term168 = True => @lem5705626)). Qed.
Lemma lem5705629 : term168 = True.
Proof. exact (EQ_MP (@lem5705628) (@lem5705626)). Qed.
Lemma lem5705630 : term161 = True.
Proof. exact (TRANS (@lem5705625) (@lem5705629)). Qed.
Lemma lem5705631 : term171 = True.
Proof. exact (TRANS (@lem5705622) (@lem5705630)). Qed.
Lemma lem5705632 : term165 = True.
Proof. exact (TRANS (@lem5705608) (@lem5705631)). Qed.
Lemma lem5705633 : term161 = True.
Proof. exact (TRANS (@lem5705585) (@lem5705632)). Qed.
Lemma lem5705634 : term160 = True.
Proof. exact (TRANS (@lem5705576) (@lem5705633)). Qed.
Lemma lem5705635 : True = term160.
Proof. exact (SYM (@lem5705634)). Qed.
Lemma lem5705636 : term160.
Proof. exact (EQ_MP (@lem5705635) (@lem0)). Qed.
Lemma lem5705637 (l : int) (r : int) (x : int) (h1 : term665 l r x) : term175 r x.
Proof. exact (conj (@lem5705636) (@lem5705498 l r x h1)). Qed.
Lemma lem5705639 (x : real) (y : real) : term176 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5705640 (r : int) (x : int) : term177 r x.
Proof. exact (@lem5705639 term75 (term91 r x)). Qed.
Lemma lem5705641 (l : int) (r : int) (x : int) (h1 : term665 l r x) : term178 r x.
Proof. exact (@lem5705640 r x (@lem5705637 l r x h1)). Qed.
Lemma lem5705642 (r : int) (x : int) : (term179 r x) = (term91 r x).
Proof. exact (@lem1982733 (term91 r x)). Qed.
Lemma lem5705643 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5705644 (r : int) (x : int) : (term180 r x) = (term154 r x).
Proof. exact (MK_COMB (@lem5705643) (@lem5705642 r x)). Qed.
Lemma lem5705645 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem5705646 (r : int) (x : int) : (term178 r x) = (term155 r x).
Proof. exact (MK_COMB (@lem5705644 r x) (@lem5705645)). Qed.
Lemma lem5705647 (l : int) (r : int) (x : int) (h1 : term665 l r x) : term155 r x.
Proof. exact (EQ_MP (@lem5705646 r x) (@lem5705641 l r x h1)). Qed.
Lemma lem5705648 (l : int) (r : int) (x : int) (h1 : term665 l r x) : term666 r x.
Proof. exact (conj (@lem5705647 l r x h1) (@lem5705573 l r x h1)). Qed.
Lemma lem5705650 (x : real) (y : real) : term187 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5705651 (r : int) (x : int) : term667 r x.
Proof. exact (@lem5705650 (term91 r x) (term561 r x)). Qed.
Lemma lem5705652 (l : int) (r : int) (x : int) (h1 : term665 l r x) : term668 r x.
Proof. exact (@lem5705651 r x (@lem5705648 l r x h1)). Qed.
Lemma lem5705653 (r : int) (x : int) : (term669 r x) = (term670 r x).
Proof. exact (@lem1982753 (real_of_int r) (term93 r) (term93 x) (term593 x)). Qed.
Lemma lem5705654 (r : int) : (term229 r) = (term195 r).
Proof. exact (@lem1982715 term103 (real_of_int r)). Qed.
Lemma lem5705656 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5705657 : term75 = term108.
Proof. exact (@lem5705656 term76). Qed.
Lemma lem5705659 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5705660 : term103 = term111.
Proof. exact (@lem5705659 term76). Qed.
Lemma lem5705661 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5705662 : term196 = term197.
Proof. exact (MK_COMB (@lem5705661) (@lem5705660)). Qed.
Lemma lem5705663 : term198 = term199.
Proof. exact (MK_COMB (@lem5705662) (@lem5705657)). Qed.
Lemma lem5705664 : term200.
Proof. exact (@lem1981473 term103 term75 term75 term75 term81 term75). Qed.
Lemma lem5705666 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5705667 : term161 = term168.
Proof. exact (@lem5705666 (NUMERAL 0) term76). Qed.
Lemma lem5705668 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5705669 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5705670 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5705669 h1) (fun h1 : term168 = True => @lem5705668)). Qed.
Lemma lem5705671 : term168 = True.
Proof. exact (EQ_MP (@lem5705670) (@lem5705668)). Qed.
Lemma lem5705672 : term161 = True.
Proof. exact (TRANS (@lem5705667) (@lem5705671)). Qed.
Lemma lem5705673 : True = term161.
Proof. exact (SYM (@lem5705672)). Qed.
Lemma lem5705674 : term161.
Proof. exact (EQ_MP (@lem5705673) (@lem0)). Qed.
Lemma lem5705675 : term201.
Proof. exact (@lem5705664 (@lem5705674)). Qed.
Lemma lem5705677 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5705678 : term161 = term168.
Proof. exact (@lem5705677 (NUMERAL 0) term76). Qed.
Lemma lem5705679 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5705680 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5705681 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5705680 h1) (fun h1 : term168 = True => @lem5705679)). Qed.
Lemma lem5705682 : term168 = True.
Proof. exact (EQ_MP (@lem5705681) (@lem5705679)). Qed.
Lemma lem5705683 : term161 = True.
Proof. exact (TRANS (@lem5705678) (@lem5705682)). Qed.
Lemma lem5705684 : True = term161.
Proof. exact (SYM (@lem5705683)). Qed.
Lemma lem5705685 : term161.
Proof. exact (EQ_MP (@lem5705684) (@lem0)). Qed.
Lemma lem5705686 : term202.
Proof. exact (@lem5705675 (@lem5705685)). Qed.
Lemma lem5705688 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5705689 : term161 = term168.
Proof. exact (@lem5705688 (NUMERAL 0) term76). Qed.
Lemma lem5705690 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5705691 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5705692 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5705691 h1) (fun h1 : term168 = True => @lem5705690)). Qed.
Lemma lem5705693 : term168 = True.
Proof. exact (EQ_MP (@lem5705692) (@lem5705690)). Qed.
Lemma lem5705694 : term161 = True.
Proof. exact (TRANS (@lem5705689) (@lem5705693)). Qed.
Lemma lem5705695 : True = term161.
Proof. exact (SYM (@lem5705694)). Qed.
Lemma lem5705696 : term161.
Proof. exact (EQ_MP (@lem5705695) (@lem0)). Qed.
Lemma lem5705697 : term203.
Proof. exact (@lem5705686 (@lem5705696)). Qed.
Lemma lem5705699 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5705700 : term119 = term120.
Proof. exact (@lem5705699 term76 term76). Qed.
Lemma lem5705701 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5705702 : term122 = term76.
Proof. exact (EQ_MP (@lem5705701) (@lem940073)). Qed.
Lemma lem5705703 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5705704 : term120 = term75.
Proof. exact (MK_COMB (@lem5705703) (@lem5705702)). Qed.
Lemma lem5705705 : term119 = term75.
Proof. exact (TRANS (@lem5705700) (@lem5705704)). Qed.
Lemma lem5705707 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5705708 : term114 = term125.
Proof. exact (@lem5705707 term76 term76). Qed.
Lemma lem5705709 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5705710 : term122 = term76.
Proof. exact (EQ_MP (@lem5705709) (@lem940073)). Qed.
Lemma lem5705711 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5705712 : term120 = term75.
Proof. exact (MK_COMB (@lem5705711) (@lem5705710)). Qed.
Lemma lem5705713 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5705714 : term125 = term103.
Proof. exact (MK_COMB (@lem5705713) (@lem5705712)). Qed.
Lemma lem5705715 : term114 = term103.
Proof. exact (TRANS (@lem5705708) (@lem5705714)). Qed.
Lemma lem5705716 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5705717 : term204 = term196.
Proof. exact (MK_COMB (@lem5705716) (@lem5705715)). Qed.
Lemma lem5705718 : term205 = term198.
Proof. exact (MK_COMB (@lem5705717) (@lem5705705)). Qed.
Lemma lem5705720 (m : nat) : (term206 m) = term81.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5705721 : term198 = term81.
Proof. exact (@lem5705720 term76). Qed.
Lemma lem5705722 : term205 = term81.
Proof. exact (TRANS (@lem5705718) (@lem5705721)). Qed.
Lemma lem5705723 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5705724 : term207 = term208.
Proof. exact (MK_COMB (@lem5705723) (@lem5705722)). Qed.
Lemma lem5705725 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem5705726 : term209 = term173.
Proof. exact (MK_COMB (@lem5705724) (@lem5705725)). Qed.
Lemma lem5705728 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5705729 : term173 = term81.
Proof. exact (@lem5705728 term76). Qed.
Lemma lem5705730 : term209 = term81.
Proof. exact (TRANS (@lem5705726) (@lem5705729)). Qed.
Lemma lem5705732 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5705733 : term119 = term120.
Proof. exact (@lem5705732 term76 term76). Qed.
Lemma lem5705734 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5705735 : term122 = term76.
Proof. exact (EQ_MP (@lem5705734) (@lem940073)). Qed.
Lemma lem5705736 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5705737 : term120 = term75.
Proof. exact (MK_COMB (@lem5705736) (@lem5705735)). Qed.
Lemma lem5705738 : term119 = term75.
Proof. exact (TRANS (@lem5705733) (@lem5705737)). Qed.
Lemma lem5705739 : term208 = term208.
Proof. exact (eq_refl term208). Qed.
Lemma lem5705740 : term210 = term173.
Proof. exact (MK_COMB (@lem5705739) (@lem5705738)). Qed.
Lemma lem5705742 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5705743 : term173 = term81.
Proof. exact (@lem5705742 term76). Qed.
Lemma lem5705744 : term210 = term81.
Proof. exact (TRANS (@lem5705740) (@lem5705743)). Qed.
Lemma lem5705745 : term81 = term210.
Proof. exact (SYM (@lem5705744)). Qed.
Lemma lem5705746 : term209 = term210.
Proof. exact (TRANS (@lem5705730) (@lem5705745)). Qed.
Lemma lem5705747 : term199 = term162.
Proof. exact (@lem5705697 (@lem5705746)). Qed.
Lemma lem5705748 : term198 = term162.
Proof. exact (TRANS (@lem5705663) (@lem5705747)). Qed.
Lemma lem5705750 (x : real) : (term128 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5705751 : term162 = term81.
Proof. exact (@lem5705750 term81). Qed.
Lemma lem5705752 : term198 = term81.
Proof. exact (TRANS (@lem5705748) (@lem5705751)). Qed.
Lemma lem5705753 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5705754 : term211 = term208.
Proof. exact (MK_COMB (@lem5705753) (@lem5705752)). Qed.
Lemma lem5705755 (r : int) : (real_of_int r) = (real_of_int r).
Proof. exact (eq_refl (real_of_int r)). Qed.
Lemma lem5705756 (r : int) : (term195 r) = (term212 r).
Proof. exact (MK_COMB (@lem5705754) (@lem5705755 r)). Qed.
Lemma lem5705757 (r : int) : (term229 r) = (term212 r).
Proof. exact (TRANS (@lem5705654 r) (@lem5705756 r)). Qed.
Lemma lem5705758 (r : int) : (term212 r) = term81.
Proof. exact (@lem1982719 (real_of_int r)). Qed.
Lemma lem5705759 (r : int) : (term229 r) = term81.
Proof. exact (TRANS (@lem5705757 r) (@lem5705758 r)). Qed.
Lemma lem5705760 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5705761 (r : int) : (term230 r) = term145.
Proof. exact (MK_COMB (@lem5705760) (@lem5705759 r)). Qed.
Lemma lem5705762 (x : int) : (term671 x) = (term580 x).
Proof. exact (@lem1982763 (term93 x) (real_of_int x) term103). Qed.
Lemma lem5705763 (x : int) : (term194 x) = (term195 x).
Proof. exact (@lem1982713 term103 (real_of_int x)). Qed.
Lemma lem5705765 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5705766 : term75 = term108.
Proof. exact (@lem5705765 term76). Qed.
Lemma lem5705768 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5705769 : term103 = term111.
Proof. exact (@lem5705768 term76). Qed.
Lemma lem5705770 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5705771 : term196 = term197.
Proof. exact (MK_COMB (@lem5705770) (@lem5705769)). Qed.
Lemma lem5705772 : term198 = term199.
Proof. exact (MK_COMB (@lem5705771) (@lem5705766)). Qed.
Lemma lem5705773 : term200.
Proof. exact (@lem1981473 term103 term75 term75 term75 term81 term75). Qed.
Lemma lem5705775 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5705776 : term161 = term168.
Proof. exact (@lem5705775 (NUMERAL 0) term76). Qed.
Lemma lem5705777 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5705778 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5705779 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5705778 h1) (fun h1 : term168 = True => @lem5705777)). Qed.
Lemma lem5705780 : term168 = True.
Proof. exact (EQ_MP (@lem5705779) (@lem5705777)). Qed.
Lemma lem5705781 : term161 = True.
Proof. exact (TRANS (@lem5705776) (@lem5705780)). Qed.
Lemma lem5705782 : True = term161.
Proof. exact (SYM (@lem5705781)). Qed.
Lemma lem5705783 : term161.
Proof. exact (EQ_MP (@lem5705782) (@lem0)). Qed.
Lemma lem5705784 : term201.
Proof. exact (@lem5705773 (@lem5705783)). Qed.
Lemma lem5705786 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5705787 : term161 = term168.
Proof. exact (@lem5705786 (NUMERAL 0) term76). Qed.
Lemma lem5705788 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5705789 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5705790 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5705789 h1) (fun h1 : term168 = True => @lem5705788)). Qed.
Lemma lem5705791 : term168 = True.
Proof. exact (EQ_MP (@lem5705790) (@lem5705788)). Qed.
Lemma lem5705792 : term161 = True.
Proof. exact (TRANS (@lem5705787) (@lem5705791)). Qed.
Lemma lem5705793 : True = term161.
Proof. exact (SYM (@lem5705792)). Qed.
Lemma lem5705794 : term161.
Proof. exact (EQ_MP (@lem5705793) (@lem0)). Qed.
Lemma lem5705795 : term202.
Proof. exact (@lem5705784 (@lem5705794)). Qed.
Lemma lem5705797 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5705798 : term161 = term168.
Proof. exact (@lem5705797 (NUMERAL 0) term76). Qed.
Lemma lem5705799 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5705800 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5705801 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5705800 h1) (fun h1 : term168 = True => @lem5705799)). Qed.
Lemma lem5705802 : term168 = True.
Proof. exact (EQ_MP (@lem5705801) (@lem5705799)). Qed.
Lemma lem5705803 : term161 = True.
Proof. exact (TRANS (@lem5705798) (@lem5705802)). Qed.
Lemma lem5705804 : True = term161.
Proof. exact (SYM (@lem5705803)). Qed.
Lemma lem5705805 : term161.
Proof. exact (EQ_MP (@lem5705804) (@lem0)). Qed.
Lemma lem5705806 : term203.
Proof. exact (@lem5705795 (@lem5705805)). Qed.
Lemma lem5705808 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5705809 : term119 = term120.
Proof. exact (@lem5705808 term76 term76). Qed.
Lemma lem5705810 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5705811 : term122 = term76.
Proof. exact (EQ_MP (@lem5705810) (@lem940073)). Qed.
Lemma lem5705812 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5705813 : term120 = term75.
Proof. exact (MK_COMB (@lem5705812) (@lem5705811)). Qed.
Lemma lem5705814 : term119 = term75.
Proof. exact (TRANS (@lem5705809) (@lem5705813)). Qed.
Lemma lem5705816 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5705817 : term114 = term125.
Proof. exact (@lem5705816 term76 term76). Qed.
Lemma lem5705818 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5705819 : term122 = term76.
Proof. exact (EQ_MP (@lem5705818) (@lem940073)). Qed.
Lemma lem5705820 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5705821 : term120 = term75.
Proof. exact (MK_COMB (@lem5705820) (@lem5705819)). Qed.
Lemma lem5705822 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5705823 : term125 = term103.
Proof. exact (MK_COMB (@lem5705822) (@lem5705821)). Qed.
Lemma lem5705824 : term114 = term103.
Proof. exact (TRANS (@lem5705817) (@lem5705823)). Qed.
Lemma lem5705825 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5705826 : term204 = term196.
Proof. exact (MK_COMB (@lem5705825) (@lem5705824)). Qed.
Lemma lem5705827 : term205 = term198.
Proof. exact (MK_COMB (@lem5705826) (@lem5705814)). Qed.
Lemma lem5705829 (m : nat) : (term206 m) = term81.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5705830 : term198 = term81.
Proof. exact (@lem5705829 term76). Qed.
Lemma lem5705831 : term205 = term81.
Proof. exact (TRANS (@lem5705827) (@lem5705830)). Qed.
Lemma lem5705832 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5705833 : term207 = term208.
Proof. exact (MK_COMB (@lem5705832) (@lem5705831)). Qed.
Lemma lem5705834 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem5705835 : term209 = term173.
Proof. exact (MK_COMB (@lem5705833) (@lem5705834)). Qed.
Lemma lem5705837 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5705838 : term173 = term81.
Proof. exact (@lem5705837 term76). Qed.
Lemma lem5705839 : term209 = term81.
Proof. exact (TRANS (@lem5705835) (@lem5705838)). Qed.
Lemma lem5705841 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5705842 : term119 = term120.
Proof. exact (@lem5705841 term76 term76). Qed.
Lemma lem5705843 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5705844 : term122 = term76.
Proof. exact (EQ_MP (@lem5705843) (@lem940073)). Qed.
Lemma lem5705845 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5705846 : term120 = term75.
Proof. exact (MK_COMB (@lem5705845) (@lem5705844)). Qed.
Lemma lem5705847 : term119 = term75.
Proof. exact (TRANS (@lem5705842) (@lem5705846)). Qed.
Lemma lem5705848 : term208 = term208.
Proof. exact (eq_refl term208). Qed.
Lemma lem5705849 : term210 = term173.
Proof. exact (MK_COMB (@lem5705848) (@lem5705847)). Qed.
Lemma lem5705851 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5705852 : term173 = term81.
Proof. exact (@lem5705851 term76). Qed.
Lemma lem5705853 : term210 = term81.
Proof. exact (TRANS (@lem5705849) (@lem5705852)). Qed.
Lemma lem5705854 : term81 = term210.
Proof. exact (SYM (@lem5705853)). Qed.
Lemma lem5705855 : term209 = term210.
Proof. exact (TRANS (@lem5705839) (@lem5705854)). Qed.
Lemma lem5705856 : term199 = term162.
Proof. exact (@lem5705806 (@lem5705855)). Qed.
Lemma lem5705857 : term198 = term162.
Proof. exact (TRANS (@lem5705772) (@lem5705856)). Qed.
Lemma lem5705859 (x : real) : (term128 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5705860 : term162 = term81.
Proof. exact (@lem5705859 term81). Qed.
Lemma lem5705861 : term198 = term81.
Proof. exact (TRANS (@lem5705857) (@lem5705860)). Qed.
Lemma lem5705862 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5705863 : term211 = term208.
Proof. exact (MK_COMB (@lem5705862) (@lem5705861)). Qed.
Lemma lem5705864 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem5705865 (x : int) : (term195 x) = (term212 x).
Proof. exact (MK_COMB (@lem5705863) (@lem5705864 x)). Qed.
Lemma lem5705866 (x : int) : (term194 x) = (term212 x).
Proof. exact (TRANS (@lem5705763 x) (@lem5705865 x)). Qed.
Lemma lem5705867 (x : int) : (term212 x) = term81.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem5705868 (x : int) : (term194 x) = term81.
Proof. exact (TRANS (@lem5705866 x) (@lem5705867 x)). Qed.
Lemma lem5705869 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5705870 (x : int) : (term213 x) = term145.
Proof. exact (MK_COMB (@lem5705869) (@lem5705868 x)). Qed.
Lemma lem5705871 : term103 = term103.
Proof. exact (eq_refl term103). Qed.
Lemma lem5705872 (x : int) : (term580 x) = term231.
Proof. exact (MK_COMB (@lem5705870 x) (@lem5705871)). Qed.
Lemma lem5705873 (x : int) : (term671 x) = term231.
Proof. exact (TRANS (@lem5705762 x) (@lem5705872 x)). Qed.
Lemma lem5705874 : term231 = term103.
Proof. exact (@lem1982721 term103). Qed.
Lemma lem5705875 (x : int) : (term671 x) = term103.
Proof. exact (TRANS (@lem5705873 x) (@lem5705874)). Qed.
Lemma lem5705876 (r : int) (x : int) : (term670 r x) = term231.
Proof. exact (MK_COMB (@lem5705761 r) (@lem5705875 x)). Qed.
Lemma lem5705877 (r : int) (x : int) : (term669 r x) = term231.
Proof. exact (TRANS (@lem5705653 r x) (@lem5705876 r x)). Qed.
Lemma lem5705878 : term231 = term103.
Proof. exact (@lem1982721 term103). Qed.
Lemma lem5705879 (r : int) (x : int) : (term669 r x) = term103.
Proof. exact (TRANS (@lem5705877 r x) (@lem5705878)). Qed.
Lemma lem5705880 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5705881 (r : int) (x : int) : (term672 r x) = term233.
Proof. exact (MK_COMB (@lem5705880) (@lem5705879 r x)). Qed.
Lemma lem5705882 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem5705883 (r : int) (x : int) : (term668 r x) = term234.
Proof. exact (MK_COMB (@lem5705881 r x) (@lem5705882)). Qed.
Lemma lem5705884 (l : int) (r : int) (x : int) (h1 : term665 l r x) : term234.
Proof. exact (EQ_MP (@lem5705883 r x) (@lem5705652 l r x h1)). Qed.
Lemma lem5705886 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5705887 : term234 = term235.
Proof. exact (@lem5705886 term81 term103). Qed.
Lemma lem5705889 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5705890 : term103 = term111.
Proof. exact (@lem5705889 term76). Qed.
Lemma lem5705892 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5705893 : term81 = term162.
Proof. exact (@lem5705892 (NUMERAL 0)). Qed.
Lemma lem5705894 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5705895 : term236 = term237.
Proof. exact (MK_COMB (@lem5705894) (@lem5705893)). Qed.
Lemma lem5705896 : term235 = term238.
Proof. exact (MK_COMB (@lem5705895) (@lem5705890)). Qed.
Lemma lem5705897 : term239.
Proof. exact (@lem1980026 term81 term75 term103 term75). Qed.
Lemma lem5705899 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5705900 : term161 = term168.
Proof. exact (@lem5705899 (NUMERAL 0) term76). Qed.
Lemma lem5705901 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5705902 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5705903 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5705902 h1) (fun h1 : term168 = True => @lem5705901)). Qed.
Lemma lem5705904 : term168 = True.
Proof. exact (EQ_MP (@lem5705903) (@lem5705901)). Qed.
Lemma lem5705905 : term161 = True.
Proof. exact (TRANS (@lem5705900) (@lem5705904)). Qed.
Lemma lem5705906 : True = term161.
Proof. exact (SYM (@lem5705905)). Qed.
Lemma lem5705907 : term161.
Proof. exact (EQ_MP (@lem5705906) (@lem0)). Qed.
Lemma lem5705908 : term240.
Proof. exact (@lem5705897 (@lem5705907)). Qed.
Lemma lem5705910 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5705911 : term161 = term168.
Proof. exact (@lem5705910 (NUMERAL 0) term76). Qed.
Lemma lem5705912 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5705913 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5705914 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5705913 h1) (fun h1 : term168 = True => @lem5705912)). Qed.
Lemma lem5705915 : term168 = True.
Proof. exact (EQ_MP (@lem5705914) (@lem5705912)). Qed.
Lemma lem5705916 : term161 = True.
Proof. exact (TRANS (@lem5705911) (@lem5705915)). Qed.
Lemma lem5705917 : True = term161.
Proof. exact (SYM (@lem5705916)). Qed.
Lemma lem5705918 : term161.
Proof. exact (EQ_MP (@lem5705917) (@lem0)). Qed.
Lemma lem5705919 : term238 = term241.
Proof. exact (@lem5705908 (@lem5705918)). Qed.
Lemma lem5705921 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5705922 : term114 = term125.
Proof. exact (@lem5705921 term76 term76). Qed.
Lemma lem5705923 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5705924 : term122 = term76.
Proof. exact (EQ_MP (@lem5705923) (@lem940073)). Qed.
Lemma lem5705925 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5705926 : term120 = term75.
Proof. exact (MK_COMB (@lem5705925) (@lem5705924)). Qed.
Lemma lem5705927 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5705928 : term125 = term103.
Proof. exact (MK_COMB (@lem5705927) (@lem5705926)). Qed.
Lemma lem5705929 : term114 = term103.
Proof. exact (TRANS (@lem5705922) (@lem5705928)). Qed.
Lemma lem5705931 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5705932 : term173 = term81.
Proof. exact (@lem5705931 term76). Qed.
Lemma lem5705933 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5705934 : term242 = term236.
Proof. exact (MK_COMB (@lem5705933) (@lem5705932)). Qed.
Lemma lem5705935 : term241 = term235.
Proof. exact (MK_COMB (@lem5705934) (@lem5705929)). Qed.
Lemma lem5705937 (m : nat) (n : nat) : (term243 m n) = (term244 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5705938 : term235 = term245.
Proof. exact (@lem5705937 (NUMERAL 0) term76). Qed.
Lemma lem5705939 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5705940 (h1 : term169 = (BIT1 0)) : (term76 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5705941 : (term169 = (BIT1 0)) = ((term76 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5705940 h1) (fun h1 : (term76 = (NUMERAL 0)) = False => @lem5705939)). Qed.
Lemma lem5705942 : (term76 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5705941) (@lem5705939)). Qed.
Lemma lem5705943 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5705944 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5705945 : term246 = (and True).
Proof. exact (MK_COMB (@lem5705944) (@lem5705943)). Qed.
Lemma lem5705946 : term245 = (True /\ False).
Proof. exact (MK_COMB (@lem5705945) (@lem5705942)). Qed.
Lemma lem5705948 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5705949 : term245 = False.
Proof. exact (TRANS (@lem5705946) (@lem5705948)). Qed.
Lemma lem5705950 : term235 = False.
Proof. exact (TRANS (@lem5705938) (@lem5705949)). Qed.
Lemma lem5705951 : term241 = False.
Proof. exact (TRANS (@lem5705935) (@lem5705950)). Qed.
Lemma lem5705952 : term238 = False.
Proof. exact (TRANS (@lem5705919) (@lem5705951)). Qed.
Lemma lem5705953 : term235 = False.
Proof. exact (TRANS (@lem5705896) (@lem5705952)). Qed.
Lemma lem5705954 : term234 = False.
Proof. exact (TRANS (@lem5705887) (@lem5705953)). Qed.
Lemma lem5705955 (l : int) (r : int) (x : int) (h1 : term665 l r x) : False.
Proof. exact (EQ_MP (@lem5705954) (@lem5705884 l r x h1)). Qed.
Lemma lem5705956 (l : int) (r : int) (x : int) (h1 : term661 l r x) : False.
Proof. exact (or_elim (@lem5704911 l r x h1) (fun h0 : term664 r l x => @lem5705494 r l x h0) (fun h0 : term665 l r x => @lem5705955 l r x h0)). Qed.
Lemma lem5705958 (l : int) (r : int) (x : int) (h1 : term661 l r x) : term661 l r x.
Proof. exact (h1). Qed.
Lemma lem5705959 (l : int) (r : int) (x : int) (h1 : term661 l r x) : (term661 l r x) = False.
Proof. exact (prop_ext (fun h2 : term661 l r x => @lem5705956 l r x h1) (fun h2 : False => @lem5705958 l r x h1)). Qed.
Lemma lem5705960 (l : int) (r : int) (x : int) (h1 : term661 l r x) : False.
Proof. exact (EQ_MP (@lem5705959 l r x h1) (@lem5705958 l r x h1)). Qed.
Lemma lem5705961 (l : int) (r : int) (h1 : term663 l r) : term663 l r.
Proof. exact (h1). Qed.
Lemma lem5705962 (l : int) (r : int) (h1 : term663 l r) : False.
Proof. exact (ex_elim (@lem5705961 l r h1) (fun x : int => fun h0 : term662 l r x => @lem5705960 l r x h0)). Qed.
Lemma lem5705963 (l : int) (r : int) (h1 : term654 l r) : term654 l r.
Proof. exact (h1). Qed.
Lemma lem5705964 (l : int) (r : int) (h1 : term654 l r) : term663 l r.
Proof. exact (EQ_MP (@lem5704901 l r) (@lem5705963 l r h1)). Qed.
Lemma lem5705965 (l : int) (r : int) (h1 : term654 l r) : (term663 l r) = False.
Proof. exact (prop_ext (fun h2 : term663 l r => @lem5705962 l r h2) (fun h2 : False => @lem5705964 l r h1)). Qed.
Lemma lem5705966 (l : int) (r : int) (h1 : term654 l r) : False.
Proof. exact (EQ_MP (@lem5705965 l r h1) (@lem5705964 l r h1)). Qed.
Lemma lem5705967 (l : int) (r : int) : term673 l r.
Proof. exact (fun h0 : term654 l r => @lem5705966 l r h0). Qed.
Lemma lem5705968 (l : int) (r : int) : term674 l r.
Proof. exact (@lem1386578 (term675 l r)). Qed.
Lemma lem5705971 (l : int) (r : int) : term675 l r.
Proof. exact (@lem5705968 l r (@lem5705967 l r)). Qed.
Lemma lem5705972 (l : int) (r : int) : (term653 l r) = (term640 l r).
Proof. exact (SYM (@lem5704485 l r)). Qed.
Lemma lem5705973 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5705974 (l : int) (r : int) : (term675 l r) = (term635 l r).
Proof. exact (MK_COMB (@lem5705973) (@lem5705972 l r)). Qed.
Lemma lem5705975 (l : int) (r : int) : term635 l r.
Proof. exact (EQ_MP (@lem5705974 l r) (@lem5705971 l r)). Qed.
Lemma lem5705976 (l : int) (r : int) : term497 l r.
Proof. exact (EQ_MP (@lem5704323 l r) (@lem5705975 l r)). Qed.
Lemma lem5705977 (l : int) (r : int) : (term497 l r) = ((term497 l r) = True).
Proof. exact (@lem7 (term497 l r)). Qed.
Lemma lem5705978 (l : int) (r : int) : (term497 l r) = True.
Proof. exact (EQ_MP (@lem5705977 l r) (@lem5705976 l r)). Qed.
Lemma lem5705979 (l : int) (r : int) : True = (term497 l r).
Proof. exact (SYM (@lem5705978 l r)). Qed.
Lemma lem5705980 (l : int) (r : int) : term497 l r.
Proof. exact (EQ_MP (@lem5705979 l r) (@lem0)). Qed.
Lemma lem5705981 (l : int) (r : int) : (term676 l r) = (term524 l r).
Proof. exact (@lem2954598 (term524 l r)). Qed.
Lemma lem5706008 (l : int) (x : int) (r : int) : (term56 l x r) = (term526 l x r).
Proof. exact (@lem17045 (int_le l x) (int_le x r)). Qed.
Lemma lem5706010 (l : int) (x : int) (r : int) : (term677 l x r) = (term677 l x r).
Proof. exact (eq_refl (term677 l x r)). Qed.
Lemma lem5706011 (l : int) (x : int) (r : int) : (term678 l x r) = (term679 l x r).
Proof. exact (MK_COMB (@lem5706010 l x r) (@lem5706008 l x r)). Qed.
Lemma lem5706012 (l : int) (x : int) (r : int) : (term680 l x r) = (term678 l x r).
Proof. exact (@lem17362 (term503 l x r) (term50 l x r)). Qed.
Lemma lem5706013 (l : int) (x : int) (r : int) : (term680 l x r) = (term679 l x r).
Proof. exact (TRANS (@lem5706012 l x r) (@lem5706011 l x r)). Qed.
Lemma lem5706014 (P : int -> Prop) : (term531 P) = (term532 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem5706015 (l : int) (r : int) : (term681 l r) = (term682 l r).
Proof. exact (@lem5706014 (term523 l r)). Qed.
Lemma lem5706016 (l : int) (x : int) (r : int) : (term683 l r x) = (term521 l x r).
Proof. exact (eq_refl (term683 l r x)). Qed.
Lemma lem5706017 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5706018 (l : int) (x : int) (r : int) : (term684 l r x) = (term680 l x r).
Proof. exact (MK_COMB (@lem5706017) (@lem5706016 l x r)). Qed.
Lemma lem5706019 (l : int) (x : int) (r : int) : (term684 l r x) = (term679 l x r).
Proof. exact (TRANS (@lem5706018 l x r) (@lem5706013 l x r)). Qed.
Lemma lem5706020 (l : int) (r : int) : (term685 l r) = (term686 l r).
Proof. exact (fun_ext (fun x : int => @lem5706019 l x r)). Qed.
Lemma lem5706021 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem5706022 (l : int) (r : int) : (term682 l r) = (term687 l r).
Proof. exact (MK_COMB (@lem5706021) (@lem5706020 l r)). Qed.
Lemma lem5706024 (l : int) (r : int) : (term681 l r) = (term687 l r).
Proof. exact (TRANS (@lem5706015 l r) (@lem5706022 l r)). Qed.
Lemma lem5706041 (l : int) (x : int) (r : int) : (term679 l x r) = (term679 l x r).
Proof. exact (eq_refl (term679 l x r)). Qed.
Lemma lem5706042 (l : int) (r : int) : (term686 l r) = (term686 l r).
Proof. exact (fun_ext (fun x : int => @lem5706041 l x r)). Qed.
Lemma lem5706043 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem5706044 (l : int) (r : int) : (term687 l r) = (term687 l r).
Proof. exact (MK_COMB (@lem5706043) (@lem5706042 l r)). Qed.
Lemma lem5706057 (l : int) (r : int) : (term681 l r) = (term687 l r).
Proof. exact (TRANS (@lem5706024 l r) (@lem5706044 l r)). Qed.
Lemma lem5706058 (l : int) (x : int) (r : int) : (term679 l x r) = (term679 l x r).
Proof. exact (eq_refl (term679 l x r)). Qed.
Lemma lem5706059 (l : int) (r : int) : (term686 l r) = (term686 l r).
Proof. exact (fun_ext (fun x : int => @lem5706058 l x r)). Qed.
Lemma lem5706060 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem5706061 (l : int) (r : int) : (term687 l r) = (term687 l r).
Proof. exact (MK_COMB (@lem5706060) (@lem5706059 l r)). Qed.
Lemma lem5706062 (l : int) (r : int) : (term681 l r) = (term687 l r).
Proof. exact (TRANS (@lem5706057 l r) (@lem5706061 l r)). Qed.
Lemma lem5706064 (x : int) (y : int) : (int_lt x y) = (term58 x y).
Proof. exact (proj2 (@lem2841544 x y)). Qed.
Lemma lem5706065 (l : int) (x : int) : (int_lt l x) = (term58 l x).
Proof. exact (@lem5706064 l x). Qed.
Lemma lem5706067 (x : int) (y : int) : (int_le x y) = (term61 x y).
Proof. exact (EQ_MP (@lem2841616 x y) (@lem2841615 x y)). Qed.
Lemma lem5706068 (l : int) (x : int) : (term58 l x) = (term540 l x).
Proof. exact (@lem5706067 (term541 l) x). Qed.
Lemma lem5706070 (x : int) (y : int) : (term64 x y) = (term65 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem5706071 (l : int) : (term542 l) = (term543 l).
Proof. exact (@lem5706070 l term68). Qed.
Lemma lem5706073 (n : nat) : (term73 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem5706074 : term74 = term75.
Proof. exact (@lem5706073 term76). Qed.
Lemma lem5706075 (l : int) : (term143 l) = (term143 l).
Proof. exact (eq_refl (term143 l)). Qed.
Lemma lem5706076 (l : int) : (term543 l) = (term104 l).
Proof. exact (MK_COMB (@lem5706075 l) (@lem5706074)). Qed.
Lemma lem5706077 (l : int) : (term542 l) = (term104 l).
Proof. exact (TRANS (@lem5706071 l) (@lem5706076 l)). Qed.
Lemma lem5706078 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5706079 (l : int) : (term544 l) = (term545 l).
Proof. exact (MK_COMB (@lem5706078) (@lem5706077 l)). Qed.
Lemma lem5706080 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem5706081 (l : int) (x : int) : (term540 l x) = (term546 l x).
Proof. exact (MK_COMB (@lem5706079 l) (@lem5706080 x)). Qed.
Lemma lem5706082 (l : int) (x : int) : (term58 l x) = (term546 l x).
Proof. exact (TRANS (@lem5706068 l x) (@lem5706081 l x)). Qed.
Lemma lem5706083 (l : int) (x : int) : (int_lt l x) = (term546 l x).
Proof. exact (TRANS (@lem5706065 l x) (@lem5706082 l x)). Qed.
Lemma lem5706085 (x : int) (y : int) : (int_lt x y) = (term58 x y).
Proof. exact (proj2 (@lem2841544 x y)). Qed.
Lemma lem5706086 (x : int) (r : int) : (int_lt x r) = (term58 x r).
Proof. exact (@lem5706085 x r). Qed.
Lemma lem5706088 (x : int) (y : int) : (int_le x y) = (term61 x y).
Proof. exact (EQ_MP (@lem2841616 x y) (@lem2841615 x y)). Qed.
Lemma lem5706089 (x : int) (r : int) : (term58 x r) = (term540 x r).
Proof. exact (@lem5706088 (term541 x) r). Qed.
Lemma lem5706091 (x : int) (y : int) : (term64 x y) = (term65 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem5706092 (x : int) : (term542 x) = (term543 x).
Proof. exact (@lem5706091 x term68). Qed.
Lemma lem5706094 (n : nat) : (term73 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem5706095 : term74 = term75.
Proof. exact (@lem5706094 term76). Qed.
Lemma lem5706096 (x : int) : (term143 x) = (term143 x).
Proof. exact (eq_refl (term143 x)). Qed.
Lemma lem5706097 (x : int) : (term543 x) = (term104 x).
Proof. exact (MK_COMB (@lem5706096 x) (@lem5706095)). Qed.
Lemma lem5706098 (x : int) : (term542 x) = (term104 x).
Proof. exact (TRANS (@lem5706092 x) (@lem5706097 x)). Qed.
Lemma lem5706099 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5706100 (x : int) : (term544 x) = (term545 x).
Proof. exact (MK_COMB (@lem5706099) (@lem5706098 x)). Qed.
Lemma lem5706101 (r : int) : (real_of_int r) = (real_of_int r).
Proof. exact (eq_refl (real_of_int r)). Qed.
Lemma lem5706102 (x : int) (r : int) : (term540 x r) = (term546 x r).
Proof. exact (MK_COMB (@lem5706100 x) (@lem5706101 r)). Qed.
Lemma lem5706103 (x : int) (r : int) : (term58 x r) = (term546 x r).
Proof. exact (TRANS (@lem5706089 x r) (@lem5706102 x r)). Qed.
Lemma lem5706104 (x : int) (r : int) : (int_lt x r) = (term546 x r).
Proof. exact (TRANS (@lem5706086 x r) (@lem5706103 x r)). Qed.
Lemma lem5706105 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5706106 (l : int) (x : int) : (term647 l x) = (term648 l x).
Proof. exact (MK_COMB (@lem5706105) (@lem5706083 l x)). Qed.
Lemma lem5706107 (l : int) (x : int) (r : int) : (term503 l x r) = (term688 l x r).
Proof. exact (MK_COMB (@lem5706106 l x) (@lem5706104 x r)). Qed.
Lemma lem5706109 (y : int) (x : int) : (term57 x y) = (term58 y x).
Proof. exact (proj1 (@lem2841542 x y)). Qed.
Lemma lem5706110 (x : int) (l : int) : (term57 l x) = (term58 x l).
Proof. exact (@lem5706109 x l). Qed.
Lemma lem5706112 (x : int) (y : int) : (int_le x y) = (term61 x y).
Proof. exact (EQ_MP (@lem2841616 x y) (@lem2841615 x y)). Qed.
Lemma lem5706113 (x : int) (l : int) : (term58 x l) = (term540 x l).
Proof. exact (@lem5706112 (term541 x) l). Qed.
Lemma lem5706115 (x : int) (y : int) : (term64 x y) = (term65 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem5706116 (x : int) : (term542 x) = (term543 x).
Proof. exact (@lem5706115 x term68). Qed.
Lemma lem5706118 (n : nat) : (term73 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem5706119 : term74 = term75.
Proof. exact (@lem5706118 term76). Qed.
Lemma lem5706120 (x : int) : (term143 x) = (term143 x).
Proof. exact (eq_refl (term143 x)). Qed.
Lemma lem5706121 (x : int) : (term543 x) = (term104 x).
Proof. exact (MK_COMB (@lem5706120 x) (@lem5706119)). Qed.
Lemma lem5706122 (x : int) : (term542 x) = (term104 x).
Proof. exact (TRANS (@lem5706116 x) (@lem5706121 x)). Qed.
Lemma lem5706123 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5706124 (x : int) : (term544 x) = (term545 x).
Proof. exact (MK_COMB (@lem5706123) (@lem5706122 x)). Qed.
Lemma lem5706125 (l : int) : (real_of_int l) = (real_of_int l).
Proof. exact (eq_refl (real_of_int l)). Qed.
Lemma lem5706126 (x : int) (l : int) : (term540 x l) = (term546 x l).
Proof. exact (MK_COMB (@lem5706124 x) (@lem5706125 l)). Qed.
Lemma lem5706127 (x : int) (l : int) : (term58 x l) = (term546 x l).
Proof. exact (TRANS (@lem5706113 x l) (@lem5706126 x l)). Qed.
Lemma lem5706128 (x : int) (l : int) : (term57 l x) = (term546 x l).
Proof. exact (TRANS (@lem5706110 x l) (@lem5706127 x l)). Qed.
Lemma lem5706130 (y : int) (x : int) : (term57 x y) = (term58 y x).
Proof. exact (proj1 (@lem2841542 x y)). Qed.
Lemma lem5706131 (r : int) (x : int) : (term57 x r) = (term58 r x).
Proof. exact (@lem5706130 r x). Qed.
Lemma lem5706133 (x : int) (y : int) : (int_le x y) = (term61 x y).
Proof. exact (EQ_MP (@lem2841616 x y) (@lem2841615 x y)). Qed.
Lemma lem5706134 (r : int) (x : int) : (term58 r x) = (term540 r x).
Proof. exact (@lem5706133 (term541 r) x). Qed.
Lemma lem5706136 (x : int) (y : int) : (term64 x y) = (term65 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem5706137 (r : int) : (term542 r) = (term543 r).
Proof. exact (@lem5706136 r term68). Qed.
Lemma lem5706139 (n : nat) : (term73 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem5706140 : term74 = term75.
Proof. exact (@lem5706139 term76). Qed.
Lemma lem5706141 (r : int) : (term143 r) = (term143 r).
Proof. exact (eq_refl (term143 r)). Qed.
Lemma lem5706142 (r : int) : (term543 r) = (term104 r).
Proof. exact (MK_COMB (@lem5706141 r) (@lem5706140)). Qed.
Lemma lem5706143 (r : int) : (term542 r) = (term104 r).
Proof. exact (TRANS (@lem5706137 r) (@lem5706142 r)). Qed.
Lemma lem5706144 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5706145 (r : int) : (term544 r) = (term545 r).
Proof. exact (MK_COMB (@lem5706144) (@lem5706143 r)). Qed.
Lemma lem5706146 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem5706147 (r : int) (x : int) : (term540 r x) = (term546 r x).
Proof. exact (MK_COMB (@lem5706145 r) (@lem5706146 x)). Qed.
Lemma lem5706148 (r : int) (x : int) : (term58 r x) = (term546 r x).
Proof. exact (TRANS (@lem5706134 r x) (@lem5706147 r x)). Qed.
Lemma lem5706149 (r : int) (x : int) : (term57 x r) = (term546 r x).
Proof. exact (TRANS (@lem5706131 r x) (@lem5706148 r x)). Qed.
Lemma lem5706150 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5706151 (x : int) (l : int) : (term548 l x) = (term549 x l).
Proof. exact (MK_COMB (@lem5706150) (@lem5706128 x l)). Qed.
Lemma lem5706152 (l : int) (r : int) (x : int) : (term526 l x r) = (term550 l r x).
Proof. exact (MK_COMB (@lem5706151 x l) (@lem5706149 r x)). Qed.
Lemma lem5706153 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5706154 (l : int) (x : int) (r : int) : (term677 l x r) = (term689 l x r).
Proof. exact (MK_COMB (@lem5706153) (@lem5706107 l x r)). Qed.
Lemma lem5706155 (l : int) (r : int) (x : int) : (term679 l x r) = (term690 l r x).
Proof. exact (MK_COMB (@lem5706154 l x r) (@lem5706152 l r x)). Qed.
Lemma lem5706156 (l : int) (r : int) : (term686 l r) = (term691 l r).
Proof. exact (fun_ext (fun x : int => @lem5706155 l r x)). Qed.
Lemma lem5706157 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem5706158 (l : int) (r : int) : (term687 l r) = (term692 l r).
Proof. exact (MK_COMB (@lem5706157) (@lem5706156 l r)). Qed.
Lemma lem5706159 (l : int) (r : int) : (term681 l r) = (term692 l r).
Proof. exact (TRANS (@lem5706062 l r) (@lem5706158 l r)). Qed.
Lemma lem5706163 (t : Prop) : (term88 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5706219 (l : int) (r : int) : (term693 l r) = (term692 l r).
Proof. exact (@lem5706163 (term692 l r)). Qed.
Lemma lem5706232 (l : int) (r : int) (x : int) : (term690 l r x) = (term690 l r x).
Proof. exact (eq_refl (term690 l r x)). Qed.
Lemma lem5706233 (l : int) (r : int) : (term691 l r) = (term691 l r).
Proof. exact (fun_ext (fun x : int => @lem5706232 l r x)). Qed.
Lemma lem5706234 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem5706235 (l : int) (r : int) : (term692 l r) = (term692 l r).
Proof. exact (MK_COMB (@lem5706234) (@lem5706233 l r)). Qed.
Lemma lem5706236 (l : int) (r : int) : (term693 l r) = (term692 l r).
Proof. exact (TRANS (@lem5706219 l r) (@lem5706235 l r)). Qed.
Lemma lem5706249 (l : int) (r : int) (x : int) : (term690 l r x) = (term690 l r x).
Proof. exact (eq_refl (term690 l r x)). Qed.
Lemma lem5706250 (l : int) (r : int) : (term691 l r) = (term691 l r).
Proof. exact (fun_ext (fun x : int => @lem5706249 l r x)). Qed.
Lemma lem5706251 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem5706252 (l : int) (r : int) : (term692 l r) = (term692 l r).
Proof. exact (MK_COMB (@lem5706251) (@lem5706250 l r)). Qed.
Lemma lem5706253 (l : int) (r : int) : (term693 l r) = (term692 l r).
Proof. exact (TRANS (@lem5706236 l r) (@lem5706252 l r)). Qed.
Lemma lem5706254 (x : int) (l : int) : (term546 l x) = (term556 x l).
Proof. exact (@lem1988287 (real_of_int x) (term104 l)). Qed.
Lemma lem5706266 (x : int) (l : int) : (term557 x l) = (term558 x l).
Proof. exact (@lem1982792 (real_of_int x) (term104 l)). Qed.
Lemma lem5706267 (l : int) : (term105 l) = (term106 l).
Proof. exact (@lem1982781 (real_of_int l) term103 term75). Qed.
Lemma lem5706269 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5706270 : term75 = term108.
Proof. exact (@lem5706269 term76). Qed.
Lemma lem5706272 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5706273 : term103 = term111.
Proof. exact (@lem5706272 term76). Qed.
Lemma lem5706274 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5706275 : term112 = term113.
Proof. exact (MK_COMB (@lem5706274) (@lem5706273)). Qed.
Lemma lem5706276 : term114 = term115.
Proof. exact (MK_COMB (@lem5706275) (@lem5706270)). Qed.
Lemma lem5706277 : term115 = term116.
Proof. exact (@lem1981613 term103 term75 term75 term75). Qed.
Lemma lem5706279 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5706280 : term119 = term120.
Proof. exact (@lem5706279 term76 term76). Qed.
Lemma lem5706281 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5706282 : term122 = term76.
Proof. exact (EQ_MP (@lem5706281) (@lem940073)). Qed.
Lemma lem5706283 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5706284 : term120 = term75.
Proof. exact (MK_COMB (@lem5706283) (@lem5706282)). Qed.
Lemma lem5706285 : term119 = term75.
Proof. exact (TRANS (@lem5706280) (@lem5706284)). Qed.
Lemma lem5706287 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5706288 : term114 = term125.
Proof. exact (@lem5706287 term76 term76). Qed.
Lemma lem5706289 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5706290 : term122 = term76.
Proof. exact (EQ_MP (@lem5706289) (@lem940073)). Qed.
Lemma lem5706291 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5706292 : term120 = term75.
Proof. exact (MK_COMB (@lem5706291) (@lem5706290)). Qed.
Lemma lem5706293 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5706294 : term125 = term103.
Proof. exact (MK_COMB (@lem5706293) (@lem5706292)). Qed.
Lemma lem5706295 : term114 = term103.
Proof. exact (TRANS (@lem5706288) (@lem5706294)). Qed.
Lemma lem5706296 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5706297 : term126 = term127.
Proof. exact (MK_COMB (@lem5706296) (@lem5706295)). Qed.
Lemma lem5706298 : term116 = term111.
Proof. exact (MK_COMB (@lem5706297) (@lem5706285)). Qed.
Lemma lem5706299 : term115 = term111.
Proof. exact (TRANS (@lem5706277) (@lem5706298)). Qed.
Lemma lem5706300 : term114 = term111.
Proof. exact (TRANS (@lem5706276) (@lem5706299)). Qed.
Lemma lem5706302 (x : real) : (term128 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5706303 : term111 = term103.
Proof. exact (@lem5706302 term103). Qed.
Lemma lem5706304 : term114 = term103.
Proof. exact (TRANS (@lem5706300) (@lem5706303)). Qed.
Lemma lem5706307 (l : int) : (term129 l) = (term129 l).
Proof. exact (eq_refl (term129 l)). Qed.
Lemma lem5706308 (l : int) : (term106 l) = (term130 l).
Proof. exact (MK_COMB (@lem5706307 l) (@lem5706304)). Qed.
Lemma lem5706309 (l : int) : (term105 l) = (term130 l).
Proof. exact (TRANS (@lem5706267 l) (@lem5706308 l)). Qed.
Lemma lem5706310 (x : int) : (term143 x) = (term143 x).
Proof. exact (eq_refl (term143 x)). Qed.
Lemma lem5706311 (x : int) (l : int) : (term558 x l) = (term144 x l).
Proof. exact (MK_COMB (@lem5706310 x) (@lem5706309 l)). Qed.
Lemma lem5706316 (l : int) (x : int) : (term144 x l) = (term561 l x).
Proof. exact (@lem1982757 (term93 l) (real_of_int x) term103). Qed.
Lemma lem5706317 (l : int) (x : int) : (term558 x l) = (term561 l x).
Proof. exact (TRANS (@lem5706311 x l) (@lem5706316 l x)). Qed.
Lemma lem5706319 (l : int) (x : int) : (term557 x l) = (term561 l x).
Proof. exact (TRANS (@lem5706266 x l) (@lem5706317 l x)). Qed.
Lemma lem5706320 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5706321 (l : int) (x : int) : (term559 x l) = (term562 l x).
Proof. exact (MK_COMB (@lem5706320) (@lem5706319 l x)). Qed.
Lemma lem5706322 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem5706323 (l : int) (x : int) : (term556 x l) = (term563 l x).
Proof. exact (MK_COMB (@lem5706321 l x) (@lem5706322)). Qed.
Lemma lem5706324 (l : int) (x : int) : (term546 l x) = (term563 l x).
Proof. exact (TRANS (@lem5706254 x l) (@lem5706323 l x)). Qed.
Lemma lem5706325 (r : int) (x : int) : (term546 x r) = (term556 r x).
Proof. exact (@lem1988287 (real_of_int r) (term104 x)). Qed.
Lemma lem5706337 (r : int) (x : int) : (term557 r x) = (term558 r x).
Proof. exact (@lem1982792 (real_of_int r) (term104 x)). Qed.
Lemma lem5706338 (x : int) : (term105 x) = (term106 x).
Proof. exact (@lem1982781 (real_of_int x) term103 term75). Qed.
Lemma lem5706340 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5706341 : term75 = term108.
Proof. exact (@lem5706340 term76). Qed.
Lemma lem5706343 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5706344 : term103 = term111.
Proof. exact (@lem5706343 term76). Qed.
Lemma lem5706345 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5706346 : term112 = term113.
Proof. exact (MK_COMB (@lem5706345) (@lem5706344)). Qed.
Lemma lem5706347 : term114 = term115.
Proof. exact (MK_COMB (@lem5706346) (@lem5706341)). Qed.
Lemma lem5706348 : term115 = term116.
Proof. exact (@lem1981613 term103 term75 term75 term75). Qed.
Lemma lem5706350 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5706351 : term119 = term120.
Proof. exact (@lem5706350 term76 term76). Qed.
Lemma lem5706352 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5706353 : term122 = term76.
Proof. exact (EQ_MP (@lem5706352) (@lem940073)). Qed.
Lemma lem5706354 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5706355 : term120 = term75.
Proof. exact (MK_COMB (@lem5706354) (@lem5706353)). Qed.
Lemma lem5706356 : term119 = term75.
Proof. exact (TRANS (@lem5706351) (@lem5706355)). Qed.
Lemma lem5706358 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5706359 : term114 = term125.
Proof. exact (@lem5706358 term76 term76). Qed.
Lemma lem5706360 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5706361 : term122 = term76.
Proof. exact (EQ_MP (@lem5706360) (@lem940073)). Qed.
Lemma lem5706362 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5706363 : term120 = term75.
Proof. exact (MK_COMB (@lem5706362) (@lem5706361)). Qed.
Lemma lem5706364 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5706365 : term125 = term103.
Proof. exact (MK_COMB (@lem5706364) (@lem5706363)). Qed.
Lemma lem5706366 : term114 = term103.
Proof. exact (TRANS (@lem5706359) (@lem5706365)). Qed.
Lemma lem5706367 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5706368 : term126 = term127.
Proof. exact (MK_COMB (@lem5706367) (@lem5706366)). Qed.
Lemma lem5706369 : term116 = term111.
Proof. exact (MK_COMB (@lem5706368) (@lem5706356)). Qed.
Lemma lem5706370 : term115 = term111.
Proof. exact (TRANS (@lem5706348) (@lem5706369)). Qed.
Lemma lem5706371 : term114 = term111.
Proof. exact (TRANS (@lem5706347) (@lem5706370)). Qed.
Lemma lem5706373 (x : real) : (term128 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5706374 : term111 = term103.
Proof. exact (@lem5706373 term103). Qed.
Lemma lem5706375 : term114 = term103.
Proof. exact (TRANS (@lem5706371) (@lem5706374)). Qed.
Lemma lem5706378 (x : int) : (term129 x) = (term129 x).
Proof. exact (eq_refl (term129 x)). Qed.
Lemma lem5706379 (x : int) : (term106 x) = (term130 x).
Proof. exact (MK_COMB (@lem5706378 x) (@lem5706375)). Qed.
Lemma lem5706380 (x : int) : (term105 x) = (term130 x).
Proof. exact (TRANS (@lem5706338 x) (@lem5706379 x)). Qed.
Lemma lem5706381 (r : int) : (term143 r) = (term143 r).
Proof. exact (eq_refl (term143 r)). Qed.
Lemma lem5706384 (r : int) (x : int) : (term558 r x) = (term144 r x).
Proof. exact (MK_COMB (@lem5706381 r) (@lem5706380 x)). Qed.
Lemma lem5706386 (r : int) (x : int) : (term557 r x) = (term144 r x).
Proof. exact (TRANS (@lem5706337 r x) (@lem5706384 r x)). Qed.
Lemma lem5706387 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5706388 (r : int) (x : int) : (term559 r x) = (term148 r x).
Proof. exact (MK_COMB (@lem5706387) (@lem5706386 r x)). Qed.
Lemma lem5706389 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem5706390 (r : int) (x : int) : (term556 r x) = (term149 r x).
Proof. exact (MK_COMB (@lem5706388 r x) (@lem5706389)). Qed.
Lemma lem5706391 (r : int) (x : int) : (term546 x r) = (term149 r x).
Proof. exact (TRANS (@lem5706325 r x) (@lem5706390 r x)). Qed.
Lemma lem5706392 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5706393 (l : int) (x : int) : (term648 l x) = (term655 l x).
Proof. exact (MK_COMB (@lem5706392) (@lem5706324 l x)). Qed.
Lemma lem5706394 (l : int) (r : int) (x : int) : (term688 l x r) = (term694 l r x).
Proof. exact (MK_COMB (@lem5706393 l x) (@lem5706391 r x)). Qed.
Lemma lem5706395 (l : int) (x : int) : (term546 x l) = (term556 l x).
Proof. exact (@lem1988287 (real_of_int l) (term104 x)). Qed.
Lemma lem5706407 (l : int) (x : int) : (term557 l x) = (term558 l x).
Proof. exact (@lem1982792 (real_of_int l) (term104 x)). Qed.
Lemma lem5706408 (x : int) : (term105 x) = (term106 x).
Proof. exact (@lem1982781 (real_of_int x) term103 term75). Qed.
Lemma lem5706410 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5706411 : term75 = term108.
Proof. exact (@lem5706410 term76). Qed.
Lemma lem5706413 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5706414 : term103 = term111.
Proof. exact (@lem5706413 term76). Qed.
Lemma lem5706415 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5706416 : term112 = term113.
Proof. exact (MK_COMB (@lem5706415) (@lem5706414)). Qed.
Lemma lem5706417 : term114 = term115.
Proof. exact (MK_COMB (@lem5706416) (@lem5706411)). Qed.
Lemma lem5706418 : term115 = term116.
Proof. exact (@lem1981613 term103 term75 term75 term75). Qed.
Lemma lem5706420 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5706421 : term119 = term120.
Proof. exact (@lem5706420 term76 term76). Qed.
Lemma lem5706422 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5706423 : term122 = term76.
Proof. exact (EQ_MP (@lem5706422) (@lem940073)). Qed.
Lemma lem5706424 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5706425 : term120 = term75.
Proof. exact (MK_COMB (@lem5706424) (@lem5706423)). Qed.
Lemma lem5706426 : term119 = term75.
Proof. exact (TRANS (@lem5706421) (@lem5706425)). Qed.
Lemma lem5706428 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5706429 : term114 = term125.
Proof. exact (@lem5706428 term76 term76). Qed.
Lemma lem5706430 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5706431 : term122 = term76.
Proof. exact (EQ_MP (@lem5706430) (@lem940073)). Qed.
Lemma lem5706432 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5706433 : term120 = term75.
Proof. exact (MK_COMB (@lem5706432) (@lem5706431)). Qed.
Lemma lem5706434 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5706435 : term125 = term103.
Proof. exact (MK_COMB (@lem5706434) (@lem5706433)). Qed.
Lemma lem5706436 : term114 = term103.
Proof. exact (TRANS (@lem5706429) (@lem5706435)). Qed.
Lemma lem5706437 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5706438 : term126 = term127.
Proof. exact (MK_COMB (@lem5706437) (@lem5706436)). Qed.
Lemma lem5706439 : term116 = term111.
Proof. exact (MK_COMB (@lem5706438) (@lem5706426)). Qed.
Lemma lem5706440 : term115 = term111.
Proof. exact (TRANS (@lem5706418) (@lem5706439)). Qed.
Lemma lem5706441 : term114 = term111.
Proof. exact (TRANS (@lem5706417) (@lem5706440)). Qed.
Lemma lem5706443 (x : real) : (term128 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5706444 : term111 = term103.
Proof. exact (@lem5706443 term103). Qed.
Lemma lem5706445 : term114 = term103.
Proof. exact (TRANS (@lem5706441) (@lem5706444)). Qed.
Lemma lem5706448 (x : int) : (term129 x) = (term129 x).
Proof. exact (eq_refl (term129 x)). Qed.
Lemma lem5706449 (x : int) : (term106 x) = (term130 x).
Proof. exact (MK_COMB (@lem5706448 x) (@lem5706445)). Qed.
Lemma lem5706450 (x : int) : (term105 x) = (term130 x).
Proof. exact (TRANS (@lem5706408 x) (@lem5706449 x)). Qed.
Lemma lem5706451 (l : int) : (term143 l) = (term143 l).
Proof. exact (eq_refl (term143 l)). Qed.
Lemma lem5706454 (l : int) (x : int) : (term558 l x) = (term144 l x).
Proof. exact (MK_COMB (@lem5706451 l) (@lem5706450 x)). Qed.
Lemma lem5706456 (l : int) (x : int) : (term557 l x) = (term144 l x).
Proof. exact (TRANS (@lem5706407 l x) (@lem5706454 l x)). Qed.
Lemma lem5706457 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5706458 (l : int) (x : int) : (term559 l x) = (term148 l x).
Proof. exact (MK_COMB (@lem5706457) (@lem5706456 l x)). Qed.
Lemma lem5706459 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem5706460 (l : int) (x : int) : (term556 l x) = (term149 l x).
Proof. exact (MK_COMB (@lem5706458 l x) (@lem5706459)). Qed.
Lemma lem5706461 (l : int) (x : int) : (term546 x l) = (term149 l x).
Proof. exact (TRANS (@lem5706395 l x) (@lem5706460 l x)). Qed.
Lemma lem5706462 (x : int) (r : int) : (term546 r x) = (term556 x r).
Proof. exact (@lem1988287 (real_of_int x) (term104 r)). Qed.
Lemma lem5706474 (x : int) (r : int) : (term557 x r) = (term558 x r).
Proof. exact (@lem1982792 (real_of_int x) (term104 r)). Qed.
Lemma lem5706475 (r : int) : (term105 r) = (term106 r).
Proof. exact (@lem1982781 (real_of_int r) term103 term75). Qed.
Lemma lem5706477 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5706478 : term75 = term108.
Proof. exact (@lem5706477 term76). Qed.
Lemma lem5706480 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5706481 : term103 = term111.
Proof. exact (@lem5706480 term76). Qed.
Lemma lem5706482 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5706483 : term112 = term113.
Proof. exact (MK_COMB (@lem5706482) (@lem5706481)). Qed.
Lemma lem5706484 : term114 = term115.
Proof. exact (MK_COMB (@lem5706483) (@lem5706478)). Qed.
Lemma lem5706485 : term115 = term116.
Proof. exact (@lem1981613 term103 term75 term75 term75). Qed.
Lemma lem5706487 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5706488 : term119 = term120.
Proof. exact (@lem5706487 term76 term76). Qed.
Lemma lem5706489 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5706490 : term122 = term76.
Proof. exact (EQ_MP (@lem5706489) (@lem940073)). Qed.
Lemma lem5706491 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5706492 : term120 = term75.
Proof. exact (MK_COMB (@lem5706491) (@lem5706490)). Qed.
Lemma lem5706493 : term119 = term75.
Proof. exact (TRANS (@lem5706488) (@lem5706492)). Qed.
Lemma lem5706495 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5706496 : term114 = term125.
Proof. exact (@lem5706495 term76 term76). Qed.
Lemma lem5706497 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5706498 : term122 = term76.
Proof. exact (EQ_MP (@lem5706497) (@lem940073)). Qed.
Lemma lem5706499 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5706500 : term120 = term75.
Proof. exact (MK_COMB (@lem5706499) (@lem5706498)). Qed.
Lemma lem5706501 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5706502 : term125 = term103.
Proof. exact (MK_COMB (@lem5706501) (@lem5706500)). Qed.
Lemma lem5706503 : term114 = term103.
Proof. exact (TRANS (@lem5706496) (@lem5706502)). Qed.
Lemma lem5706504 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5706505 : term126 = term127.
Proof. exact (MK_COMB (@lem5706504) (@lem5706503)). Qed.
Lemma lem5706506 : term116 = term111.
Proof. exact (MK_COMB (@lem5706505) (@lem5706493)). Qed.
Lemma lem5706507 : term115 = term111.
Proof. exact (TRANS (@lem5706485) (@lem5706506)). Qed.
Lemma lem5706508 : term114 = term111.
Proof. exact (TRANS (@lem5706484) (@lem5706507)). Qed.
Lemma lem5706510 (x : real) : (term128 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5706511 : term111 = term103.
Proof. exact (@lem5706510 term103). Qed.
Lemma lem5706512 : term114 = term103.
Proof. exact (TRANS (@lem5706508) (@lem5706511)). Qed.
Lemma lem5706515 (r : int) : (term129 r) = (term129 r).
Proof. exact (eq_refl (term129 r)). Qed.
Lemma lem5706516 (r : int) : (term106 r) = (term130 r).
Proof. exact (MK_COMB (@lem5706515 r) (@lem5706512)). Qed.
Lemma lem5706517 (r : int) : (term105 r) = (term130 r).
Proof. exact (TRANS (@lem5706475 r) (@lem5706516 r)). Qed.
Lemma lem5706518 (x : int) : (term143 x) = (term143 x).
Proof. exact (eq_refl (term143 x)). Qed.
Lemma lem5706519 (x : int) (r : int) : (term558 x r) = (term144 x r).
Proof. exact (MK_COMB (@lem5706518 x) (@lem5706517 r)). Qed.
Lemma lem5706524 (r : int) (x : int) : (term144 x r) = (term561 r x).
Proof. exact (@lem1982757 (term93 r) (real_of_int x) term103). Qed.
Lemma lem5706525 (r : int) (x : int) : (term558 x r) = (term561 r x).
Proof. exact (TRANS (@lem5706519 x r) (@lem5706524 r x)). Qed.
Lemma lem5706527 (r : int) (x : int) : (term557 x r) = (term561 r x).
Proof. exact (TRANS (@lem5706474 x r) (@lem5706525 r x)). Qed.
Lemma lem5706528 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5706529 (r : int) (x : int) : (term559 x r) = (term562 r x).
Proof. exact (MK_COMB (@lem5706528) (@lem5706527 r x)). Qed.
Lemma lem5706530 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem5706531 (r : int) (x : int) : (term556 x r) = (term563 r x).
Proof. exact (MK_COMB (@lem5706529 r x) (@lem5706530)). Qed.
Lemma lem5706532 (r : int) (x : int) : (term546 r x) = (term563 r x).
Proof. exact (TRANS (@lem5706462 x r) (@lem5706531 r x)). Qed.
Lemma lem5706533 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5706534 (l : int) (x : int) : (term549 x l) = (term564 l x).
Proof. exact (MK_COMB (@lem5706533) (@lem5706461 l x)). Qed.
Lemma lem5706535 (l : int) (r : int) (x : int) : (term550 l r x) = (term565 l r x).
Proof. exact (MK_COMB (@lem5706534 l x) (@lem5706532 r x)). Qed.
Lemma lem5706536 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5706537 (l : int) (r : int) (x : int) : (term689 l x r) = (term695 l r x).
Proof. exact (MK_COMB (@lem5706536) (@lem5706394 l r x)). Qed.
Lemma lem5706538 (l : int) (r : int) (x : int) : (term690 l r x) = (term696 l r x).
Proof. exact (MK_COMB (@lem5706537 l r x) (@lem5706535 l r x)). Qed.
Lemma lem5706539 (l : int) (r : int) : (term691 l r) = (term697 l r).
Proof. exact (fun_ext (fun x : int => @lem5706538 l r x)). Qed.
Lemma lem5706540 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem5706541 (l : int) (r : int) : (term692 l r) = (term698 l r).
Proof. exact (MK_COMB (@lem5706540) (@lem5706539 l r)). Qed.
Lemma lem5706596 (l : int) (r : int) : (term693 l r) = (term698 l r).
Proof. exact (TRANS (@lem5706253 l r) (@lem5706541 l r)). Qed.
Lemma lem5706619 (l : int) (r : int) (x : int) : (term696 l r x) = (term699 l r x).
Proof. exact (@lem19158 (term149 l x) (term694 l r x) (term563 r x)). Qed.
Lemma lem5706620 (l : int) (r : int) : (term697 l r) = (term700 l r).
Proof. exact (fun_ext (fun x : int => @lem5706619 l r x)). Qed.
Lemma lem5706621 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem5706622 (l : int) (r : int) : (term698 l r) = (term701 l r).
Proof. exact (MK_COMB (@lem5706621) (@lem5706620 l r)). Qed.
Lemma lem5706623 (l : int) (r : int) : (term693 l r) = (term701 l r).
Proof. exact (TRANS (@lem5706596 l r) (@lem5706622 l r)). Qed.
Lemma lem5706633 (l : int) (r : int) (x : int) (h1 : term699 l r x) : term699 l r x.
Proof. exact (h1). Qed.
Lemma lem5706634 (r : int) (l : int) (x : int) (h1 : term702 r l x) : term702 r l x.
Proof. exact (h1). Qed.
Lemma lem5706635 (r : int) (l : int) (x : int) (h1 : term702 r l x) : term149 l x.
Proof. exact (proj2 (@lem5706634 r l x h1)). Qed.
Lemma lem5706636 (r : int) (l : int) (x : int) (h1 : term702 r l x) : term694 l r x.
Proof. exact (proj1 (@lem5706634 r l x h1)). Qed.
Lemma lem5706638 (r : int) (l : int) (x : int) (h1 : term702 r l x) : term563 l x.
Proof. exact (proj1 (@lem5706636 r l x h1)). Qed.
Lemma lem5706640 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5706641 : term160 = term161.
Proof. exact (@lem5706640 term81 term75). Qed.
Lemma lem5706643 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5706644 : term75 = term108.
Proof. exact (@lem5706643 term76). Qed.
Lemma lem5706646 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5706647 : term81 = term162.
Proof. exact (@lem5706646 (NUMERAL 0)). Qed.
Lemma lem5706648 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5706649 : term163 = term164.
Proof. exact (MK_COMB (@lem5706648) (@lem5706647)). Qed.
Lemma lem5706650 : term161 = term165.
Proof. exact (MK_COMB (@lem5706649) (@lem5706644)). Qed.
Lemma lem5706651 : term166.
Proof. exact (@lem1980255 term81 term75 term75 term75). Qed.
Lemma lem5706653 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5706654 : term161 = term168.
Proof. exact (@lem5706653 (NUMERAL 0) term76). Qed.
Lemma lem5706655 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5706656 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5706657 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5706656 h1) (fun h1 : term168 = True => @lem5706655)). Qed.
Lemma lem5706658 : term168 = True.
Proof. exact (EQ_MP (@lem5706657) (@lem5706655)). Qed.
Lemma lem5706659 : term161 = True.
Proof. exact (TRANS (@lem5706654) (@lem5706658)). Qed.
Lemma lem5706660 : True = term161.
Proof. exact (SYM (@lem5706659)). Qed.
Lemma lem5706661 : term161.
Proof. exact (EQ_MP (@lem5706660) (@lem0)). Qed.
Lemma lem5706662 : term170.
Proof. exact (@lem5706651 (@lem5706661)). Qed.
Lemma lem5706664 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5706665 : term161 = term168.
Proof. exact (@lem5706664 (NUMERAL 0) term76). Qed.
Lemma lem5706666 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5706667 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5706668 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5706667 h1) (fun h1 : term168 = True => @lem5706666)). Qed.
Lemma lem5706669 : term168 = True.
Proof. exact (EQ_MP (@lem5706668) (@lem5706666)). Qed.
Lemma lem5706670 : term161 = True.
Proof. exact (TRANS (@lem5706665) (@lem5706669)). Qed.
Lemma lem5706671 : True = term161.
Proof. exact (SYM (@lem5706670)). Qed.
Lemma lem5706672 : term161.
Proof. exact (EQ_MP (@lem5706671) (@lem0)). Qed.
Lemma lem5706673 : term165 = term171.
Proof. exact (@lem5706662 (@lem5706672)). Qed.
Lemma lem5706675 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5706676 : term119 = term120.
Proof. exact (@lem5706675 term76 term76). Qed.
Lemma lem5706677 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5706678 : term122 = term76.
Proof. exact (EQ_MP (@lem5706677) (@lem940073)). Qed.
Lemma lem5706679 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5706680 : term120 = term75.
Proof. exact (MK_COMB (@lem5706679) (@lem5706678)). Qed.
Lemma lem5706681 : term119 = term75.
Proof. exact (TRANS (@lem5706676) (@lem5706680)). Qed.
Lemma lem5706683 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5706684 : term173 = term81.
Proof. exact (@lem5706683 term76). Qed.
Lemma lem5706685 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5706686 : term174 = term163.
Proof. exact (MK_COMB (@lem5706685) (@lem5706684)). Qed.
Lemma lem5706687 : term171 = term161.
Proof. exact (MK_COMB (@lem5706686) (@lem5706681)). Qed.
Lemma lem5706689 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5706690 : term161 = term168.
Proof. exact (@lem5706689 (NUMERAL 0) term76). Qed.
Lemma lem5706691 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5706692 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5706693 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5706692 h1) (fun h1 : term168 = True => @lem5706691)). Qed.
Lemma lem5706694 : term168 = True.
Proof. exact (EQ_MP (@lem5706693) (@lem5706691)). Qed.
Lemma lem5706695 : term161 = True.
Proof. exact (TRANS (@lem5706690) (@lem5706694)). Qed.
Lemma lem5706696 : term171 = True.
Proof. exact (TRANS (@lem5706687) (@lem5706695)). Qed.
Lemma lem5706697 : term165 = True.
Proof. exact (TRANS (@lem5706673) (@lem5706696)). Qed.
Lemma lem5706698 : term161 = True.
Proof. exact (TRANS (@lem5706650) (@lem5706697)). Qed.
Lemma lem5706699 : term160 = True.
Proof. exact (TRANS (@lem5706641) (@lem5706698)). Qed.
Lemma lem5706700 : True = term160.
Proof. exact (SYM (@lem5706699)). Qed.
Lemma lem5706701 : term160.
Proof. exact (EQ_MP (@lem5706700) (@lem0)). Qed.
Lemma lem5706702 (r : int) (l : int) (x : int) (h1 : term702 r l x) : term583 l x.
Proof. exact (conj (@lem5706701) (@lem5706638 r l x h1)). Qed.
Lemma lem5706704 (x : real) (y : real) : term176 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5706705 (l : int) (x : int) : term584 l x.
Proof. exact (@lem5706704 term75 (term561 l x)). Qed.
Lemma lem5706706 (r : int) (l : int) (x : int) (h1 : term702 r l x) : term585 l x.
Proof. exact (@lem5706705 l x (@lem5706702 r l x h1)). Qed.
Lemma lem5706707 (l : int) (x : int) : (term586 l x) = (term561 l x).
Proof. exact (@lem1982733 (term561 l x)). Qed.
Lemma lem5706708 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5706709 (l : int) (x : int) : (term587 l x) = (term562 l x).
Proof. exact (MK_COMB (@lem5706708) (@lem5706707 l x)). Qed.
Lemma lem5706710 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem5706711 (l : int) (x : int) : (term585 l x) = (term563 l x).
Proof. exact (MK_COMB (@lem5706709 l x) (@lem5706710)). Qed.
Lemma lem5706712 (r : int) (l : int) (x : int) (h1 : term702 r l x) : term563 l x.
Proof. exact (EQ_MP (@lem5706711 l x) (@lem5706706 r l x h1)). Qed.
Lemma lem5706714 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5706715 : term160 = term161.
Proof. exact (@lem5706714 term81 term75). Qed.
Lemma lem5706717 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5706718 : term75 = term108.
Proof. exact (@lem5706717 term76). Qed.
Lemma lem5706720 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5706721 : term81 = term162.
Proof. exact (@lem5706720 (NUMERAL 0)). Qed.
Lemma lem5706722 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5706723 : term163 = term164.
Proof. exact (MK_COMB (@lem5706722) (@lem5706721)). Qed.
Lemma lem5706724 : term161 = term165.
Proof. exact (MK_COMB (@lem5706723) (@lem5706718)). Qed.
Lemma lem5706725 : term166.
Proof. exact (@lem1980255 term81 term75 term75 term75). Qed.
Lemma lem5706727 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5706728 : term161 = term168.
Proof. exact (@lem5706727 (NUMERAL 0) term76). Qed.
Lemma lem5706729 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5706730 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5706731 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5706730 h1) (fun h1 : term168 = True => @lem5706729)). Qed.
Lemma lem5706732 : term168 = True.
Proof. exact (EQ_MP (@lem5706731) (@lem5706729)). Qed.
Lemma lem5706733 : term161 = True.
Proof. exact (TRANS (@lem5706728) (@lem5706732)). Qed.
Lemma lem5706734 : True = term161.
Proof. exact (SYM (@lem5706733)). Qed.
Lemma lem5706735 : term161.
Proof. exact (EQ_MP (@lem5706734) (@lem0)). Qed.
Lemma lem5706736 : term170.
Proof. exact (@lem5706725 (@lem5706735)). Qed.
Lemma lem5706738 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5706739 : term161 = term168.
Proof. exact (@lem5706738 (NUMERAL 0) term76). Qed.
Lemma lem5706740 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5706741 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5706742 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5706741 h1) (fun h1 : term168 = True => @lem5706740)). Qed.
Lemma lem5706743 : term168 = True.
Proof. exact (EQ_MP (@lem5706742) (@lem5706740)). Qed.
Lemma lem5706744 : term161 = True.
Proof. exact (TRANS (@lem5706739) (@lem5706743)). Qed.
Lemma lem5706745 : True = term161.
Proof. exact (SYM (@lem5706744)). Qed.
Lemma lem5706746 : term161.
Proof. exact (EQ_MP (@lem5706745) (@lem0)). Qed.
Lemma lem5706747 : term165 = term171.
Proof. exact (@lem5706736 (@lem5706746)). Qed.
Lemma lem5706749 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5706750 : term119 = term120.
Proof. exact (@lem5706749 term76 term76). Qed.
Lemma lem5706751 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5706752 : term122 = term76.
Proof. exact (EQ_MP (@lem5706751) (@lem940073)). Qed.
Lemma lem5706753 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5706754 : term120 = term75.
Proof. exact (MK_COMB (@lem5706753) (@lem5706752)). Qed.
Lemma lem5706755 : term119 = term75.
Proof. exact (TRANS (@lem5706750) (@lem5706754)). Qed.
Lemma lem5706757 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5706758 : term173 = term81.
Proof. exact (@lem5706757 term76). Qed.
Lemma lem5706759 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5706760 : term174 = term163.
Proof. exact (MK_COMB (@lem5706759) (@lem5706758)). Qed.
Lemma lem5706761 : term171 = term161.
Proof. exact (MK_COMB (@lem5706760) (@lem5706755)). Qed.
Lemma lem5706763 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5706764 : term161 = term168.
Proof. exact (@lem5706763 (NUMERAL 0) term76). Qed.
Lemma lem5706765 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5706766 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5706767 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5706766 h1) (fun h1 : term168 = True => @lem5706765)). Qed.
Lemma lem5706768 : term168 = True.
Proof. exact (EQ_MP (@lem5706767) (@lem5706765)). Qed.
Lemma lem5706769 : term161 = True.
Proof. exact (TRANS (@lem5706764) (@lem5706768)). Qed.
Lemma lem5706770 : term171 = True.
Proof. exact (TRANS (@lem5706761) (@lem5706769)). Qed.
Lemma lem5706771 : term165 = True.
Proof. exact (TRANS (@lem5706747) (@lem5706770)). Qed.
Lemma lem5706772 : term161 = True.
Proof. exact (TRANS (@lem5706724) (@lem5706771)). Qed.
Lemma lem5706773 : term160 = True.
Proof. exact (TRANS (@lem5706715) (@lem5706772)). Qed.
Lemma lem5706774 : True = term160.
Proof. exact (SYM (@lem5706773)). Qed.
Lemma lem5706775 : term160.
Proof. exact (EQ_MP (@lem5706774) (@lem0)). Qed.
Lemma lem5706776 (r : int) (l : int) (x : int) (h1 : term702 r l x) : term181 l x.
Proof. exact (conj (@lem5706775) (@lem5706635 r l x h1)). Qed.
Lemma lem5706778 (x : real) (y : real) : term176 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5706779 (l : int) (x : int) : term182 l x.
Proof. exact (@lem5706778 term75 (term144 l x)). Qed.
Lemma lem5706780 (r : int) (l : int) (x : int) (h1 : term702 r l x) : term183 l x.
Proof. exact (@lem5706779 l x (@lem5706776 r l x h1)). Qed.
Lemma lem5706781 (l : int) (x : int) : (term184 l x) = (term144 l x).
Proof. exact (@lem1982733 (term144 l x)). Qed.
Lemma lem5706782 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5706783 (l : int) (x : int) : (term185 l x) = (term148 l x).
Proof. exact (MK_COMB (@lem5706782) (@lem5706781 l x)). Qed.
Lemma lem5706784 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem5706785 (l : int) (x : int) : (term183 l x) = (term149 l x).
Proof. exact (MK_COMB (@lem5706783 l x) (@lem5706784)). Qed.
Lemma lem5706786 (r : int) (l : int) (x : int) (h1 : term702 r l x) : term149 l x.
Proof. exact (EQ_MP (@lem5706785 l x) (@lem5706780 r l x h1)). Qed.
Lemma lem5706787 (r : int) (l : int) (x : int) (h1 : term702 r l x) : term588 l x.
Proof. exact (conj (@lem5706786 r l x h1) (@lem5706712 r l x h1)). Qed.
Lemma lem5706789 (x : real) (y : real) : term187 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5706790 (l : int) (x : int) : term589 l x.
Proof. exact (@lem5706789 (term144 l x) (term561 l x)). Qed.
Lemma lem5706791 (r : int) (l : int) (x : int) (h1 : term702 r l x) : term590 l x.
Proof. exact (@lem5706790 l x (@lem5706787 r l x h1)). Qed.
Lemma lem5706792 (l : int) (x : int) : (term591 l x) = (term592 l x).
Proof. exact (@lem1982753 (real_of_int l) (term93 l) (term130 x) (term593 x)). Qed.
Lemma lem5706793 (l : int) : (term229 l) = (term195 l).
Proof. exact (@lem1982715 term103 (real_of_int l)). Qed.
Lemma lem5706795 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5706796 : term75 = term108.
Proof. exact (@lem5706795 term76). Qed.
Lemma lem5706798 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5706799 : term103 = term111.
Proof. exact (@lem5706798 term76). Qed.
Lemma lem5706800 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5706801 : term196 = term197.
Proof. exact (MK_COMB (@lem5706800) (@lem5706799)). Qed.
Lemma lem5706802 : term198 = term199.
Proof. exact (MK_COMB (@lem5706801) (@lem5706796)). Qed.
Lemma lem5706803 : term200.
Proof. exact (@lem1981473 term103 term75 term75 term75 term81 term75). Qed.
Lemma lem5706805 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5706806 : term161 = term168.
Proof. exact (@lem5706805 (NUMERAL 0) term76). Qed.
Lemma lem5706807 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5706808 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5706809 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5706808 h1) (fun h1 : term168 = True => @lem5706807)). Qed.
Lemma lem5706810 : term168 = True.
Proof. exact (EQ_MP (@lem5706809) (@lem5706807)). Qed.
Lemma lem5706811 : term161 = True.
Proof. exact (TRANS (@lem5706806) (@lem5706810)). Qed.
Lemma lem5706812 : True = term161.
Proof. exact (SYM (@lem5706811)). Qed.
Lemma lem5706813 : term161.
Proof. exact (EQ_MP (@lem5706812) (@lem0)). Qed.
Lemma lem5706814 : term201.
Proof. exact (@lem5706803 (@lem5706813)). Qed.
Lemma lem5706816 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5706817 : term161 = term168.
Proof. exact (@lem5706816 (NUMERAL 0) term76). Qed.
Lemma lem5706818 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5706819 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5706820 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5706819 h1) (fun h1 : term168 = True => @lem5706818)). Qed.
Lemma lem5706821 : term168 = True.
Proof. exact (EQ_MP (@lem5706820) (@lem5706818)). Qed.
Lemma lem5706822 : term161 = True.
Proof. exact (TRANS (@lem5706817) (@lem5706821)). Qed.
Lemma lem5706823 : True = term161.
Proof. exact (SYM (@lem5706822)). Qed.
Lemma lem5706824 : term161.
Proof. exact (EQ_MP (@lem5706823) (@lem0)). Qed.
Lemma lem5706825 : term202.
Proof. exact (@lem5706814 (@lem5706824)). Qed.
Lemma lem5706827 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5706828 : term161 = term168.
Proof. exact (@lem5706827 (NUMERAL 0) term76). Qed.
Lemma lem5706829 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5706830 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5706831 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5706830 h1) (fun h1 : term168 = True => @lem5706829)). Qed.
Lemma lem5706832 : term168 = True.
Proof. exact (EQ_MP (@lem5706831) (@lem5706829)). Qed.
Lemma lem5706833 : term161 = True.
Proof. exact (TRANS (@lem5706828) (@lem5706832)). Qed.
Lemma lem5706834 : True = term161.
Proof. exact (SYM (@lem5706833)). Qed.
Lemma lem5706835 : term161.
Proof. exact (EQ_MP (@lem5706834) (@lem0)). Qed.
Lemma lem5706836 : term203.
Proof. exact (@lem5706825 (@lem5706835)). Qed.
Lemma lem5706838 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5706839 : term119 = term120.
Proof. exact (@lem5706838 term76 term76). Qed.
Lemma lem5706840 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5706841 : term122 = term76.
Proof. exact (EQ_MP (@lem5706840) (@lem940073)). Qed.
Lemma lem5706842 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5706843 : term120 = term75.
Proof. exact (MK_COMB (@lem5706842) (@lem5706841)). Qed.
Lemma lem5706844 : term119 = term75.
Proof. exact (TRANS (@lem5706839) (@lem5706843)). Qed.
Lemma lem5706846 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5706847 : term114 = term125.
Proof. exact (@lem5706846 term76 term76). Qed.
Lemma lem5706848 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5706849 : term122 = term76.
Proof. exact (EQ_MP (@lem5706848) (@lem940073)). Qed.
Lemma lem5706850 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5706851 : term120 = term75.
Proof. exact (MK_COMB (@lem5706850) (@lem5706849)). Qed.
Lemma lem5706852 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5706853 : term125 = term103.
Proof. exact (MK_COMB (@lem5706852) (@lem5706851)). Qed.
Lemma lem5706854 : term114 = term103.
Proof. exact (TRANS (@lem5706847) (@lem5706853)). Qed.
Lemma lem5706855 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5706856 : term204 = term196.
Proof. exact (MK_COMB (@lem5706855) (@lem5706854)). Qed.
Lemma lem5706857 : term205 = term198.
Proof. exact (MK_COMB (@lem5706856) (@lem5706844)). Qed.
Lemma lem5706859 (m : nat) : (term206 m) = term81.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5706860 : term198 = term81.
Proof. exact (@lem5706859 term76). Qed.
Lemma lem5706861 : term205 = term81.
Proof. exact (TRANS (@lem5706857) (@lem5706860)). Qed.
Lemma lem5706862 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5706863 : term207 = term208.
Proof. exact (MK_COMB (@lem5706862) (@lem5706861)). Qed.
Lemma lem5706864 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem5706865 : term209 = term173.
Proof. exact (MK_COMB (@lem5706863) (@lem5706864)). Qed.
Lemma lem5706867 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5706868 : term173 = term81.
Proof. exact (@lem5706867 term76). Qed.
Lemma lem5706869 : term209 = term81.
Proof. exact (TRANS (@lem5706865) (@lem5706868)). Qed.
Lemma lem5706871 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5706872 : term119 = term120.
Proof. exact (@lem5706871 term76 term76). Qed.
Lemma lem5706873 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5706874 : term122 = term76.
Proof. exact (EQ_MP (@lem5706873) (@lem940073)). Qed.
Lemma lem5706875 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5706876 : term120 = term75.
Proof. exact (MK_COMB (@lem5706875) (@lem5706874)). Qed.
Lemma lem5706877 : term119 = term75.
Proof. exact (TRANS (@lem5706872) (@lem5706876)). Qed.
Lemma lem5706878 : term208 = term208.
Proof. exact (eq_refl term208). Qed.
Lemma lem5706879 : term210 = term173.
Proof. exact (MK_COMB (@lem5706878) (@lem5706877)). Qed.
Lemma lem5706881 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5706882 : term173 = term81.
Proof. exact (@lem5706881 term76). Qed.
Lemma lem5706883 : term210 = term81.
Proof. exact (TRANS (@lem5706879) (@lem5706882)). Qed.
Lemma lem5706884 : term81 = term210.
Proof. exact (SYM (@lem5706883)). Qed.
Lemma lem5706885 : term209 = term210.
Proof. exact (TRANS (@lem5706869) (@lem5706884)). Qed.
Lemma lem5706886 : term199 = term162.
Proof. exact (@lem5706836 (@lem5706885)). Qed.
Lemma lem5706887 : term198 = term162.
Proof. exact (TRANS (@lem5706802) (@lem5706886)). Qed.
Lemma lem5706889 (x : real) : (term128 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5706890 : term162 = term81.
Proof. exact (@lem5706889 term81). Qed.
Lemma lem5706891 : term198 = term81.
Proof. exact (TRANS (@lem5706887) (@lem5706890)). Qed.
Lemma lem5706892 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5706893 : term211 = term208.
Proof. exact (MK_COMB (@lem5706892) (@lem5706891)). Qed.
Lemma lem5706894 (l : int) : (real_of_int l) = (real_of_int l).
Proof. exact (eq_refl (real_of_int l)). Qed.
Lemma lem5706895 (l : int) : (term195 l) = (term212 l).
Proof. exact (MK_COMB (@lem5706893) (@lem5706894 l)). Qed.
Lemma lem5706896 (l : int) : (term229 l) = (term212 l).
Proof. exact (TRANS (@lem5706793 l) (@lem5706895 l)). Qed.
Lemma lem5706897 (l : int) : (term212 l) = term81.
Proof. exact (@lem1982719 (real_of_int l)). Qed.
Lemma lem5706898 (l : int) : (term229 l) = term81.
Proof. exact (TRANS (@lem5706896 l) (@lem5706897 l)). Qed.
Lemma lem5706899 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5706900 (l : int) : (term230 l) = term145.
Proof. exact (MK_COMB (@lem5706899) (@lem5706898 l)). Qed.
Lemma lem5706901 (x : int) : (term594 x) = (term595 x).
Proof. exact (@lem1982753 (term93 x) (real_of_int x) term103 term103). Qed.
Lemma lem5706902 (x : int) : (term194 x) = (term195 x).
Proof. exact (@lem1982713 term103 (real_of_int x)). Qed.
Lemma lem5706904 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5706905 : term75 = term108.
Proof. exact (@lem5706904 term76). Qed.
Lemma lem5706907 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5706908 : term103 = term111.
Proof. exact (@lem5706907 term76). Qed.
Lemma lem5706909 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5706910 : term196 = term197.
Proof. exact (MK_COMB (@lem5706909) (@lem5706908)). Qed.
Lemma lem5706911 : term198 = term199.
Proof. exact (MK_COMB (@lem5706910) (@lem5706905)). Qed.
Lemma lem5706912 : term200.
Proof. exact (@lem1981473 term103 term75 term75 term75 term81 term75). Qed.
Lemma lem5706914 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5706915 : term161 = term168.
Proof. exact (@lem5706914 (NUMERAL 0) term76). Qed.
Lemma lem5706916 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5706917 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5706918 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5706917 h1) (fun h1 : term168 = True => @lem5706916)). Qed.
Lemma lem5706919 : term168 = True.
Proof. exact (EQ_MP (@lem5706918) (@lem5706916)). Qed.
Lemma lem5706920 : term161 = True.
Proof. exact (TRANS (@lem5706915) (@lem5706919)). Qed.
Lemma lem5706921 : True = term161.
Proof. exact (SYM (@lem5706920)). Qed.
Lemma lem5706922 : term161.
Proof. exact (EQ_MP (@lem5706921) (@lem0)). Qed.
Lemma lem5706923 : term201.
Proof. exact (@lem5706912 (@lem5706922)). Qed.
Lemma lem5706925 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5706926 : term161 = term168.
Proof. exact (@lem5706925 (NUMERAL 0) term76). Qed.
Lemma lem5706927 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5706928 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5706929 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5706928 h1) (fun h1 : term168 = True => @lem5706927)). Qed.
Lemma lem5706930 : term168 = True.
Proof. exact (EQ_MP (@lem5706929) (@lem5706927)). Qed.
Lemma lem5706931 : term161 = True.
Proof. exact (TRANS (@lem5706926) (@lem5706930)). Qed.
Lemma lem5706932 : True = term161.
Proof. exact (SYM (@lem5706931)). Qed.
Lemma lem5706933 : term161.
Proof. exact (EQ_MP (@lem5706932) (@lem0)). Qed.
Lemma lem5706934 : term202.
Proof. exact (@lem5706923 (@lem5706933)). Qed.
Lemma lem5706936 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5706937 : term161 = term168.
Proof. exact (@lem5706936 (NUMERAL 0) term76). Qed.
Lemma lem5706938 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5706939 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5706940 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5706939 h1) (fun h1 : term168 = True => @lem5706938)). Qed.
Lemma lem5706941 : term168 = True.
Proof. exact (EQ_MP (@lem5706940) (@lem5706938)). Qed.
Lemma lem5706942 : term161 = True.
Proof. exact (TRANS (@lem5706937) (@lem5706941)). Qed.
Lemma lem5706943 : True = term161.
Proof. exact (SYM (@lem5706942)). Qed.
Lemma lem5706944 : term161.
Proof. exact (EQ_MP (@lem5706943) (@lem0)). Qed.
Lemma lem5706945 : term203.
Proof. exact (@lem5706934 (@lem5706944)). Qed.
Lemma lem5706947 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5706948 : term119 = term120.
Proof. exact (@lem5706947 term76 term76). Qed.
Lemma lem5706949 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5706950 : term122 = term76.
Proof. exact (EQ_MP (@lem5706949) (@lem940073)). Qed.
Lemma lem5706951 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5706952 : term120 = term75.
Proof. exact (MK_COMB (@lem5706951) (@lem5706950)). Qed.
Lemma lem5706953 : term119 = term75.
Proof. exact (TRANS (@lem5706948) (@lem5706952)). Qed.
Lemma lem5706955 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5706956 : term114 = term125.
Proof. exact (@lem5706955 term76 term76). Qed.
Lemma lem5706957 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5706958 : term122 = term76.
Proof. exact (EQ_MP (@lem5706957) (@lem940073)). Qed.
Lemma lem5706959 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5706960 : term120 = term75.
Proof. exact (MK_COMB (@lem5706959) (@lem5706958)). Qed.
Lemma lem5706961 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5706962 : term125 = term103.
Proof. exact (MK_COMB (@lem5706961) (@lem5706960)). Qed.
Lemma lem5706963 : term114 = term103.
Proof. exact (TRANS (@lem5706956) (@lem5706962)). Qed.
Lemma lem5706964 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5706965 : term204 = term196.
Proof. exact (MK_COMB (@lem5706964) (@lem5706963)). Qed.
Lemma lem5706966 : term205 = term198.
Proof. exact (MK_COMB (@lem5706965) (@lem5706953)). Qed.
Lemma lem5706968 (m : nat) : (term206 m) = term81.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5706969 : term198 = term81.
Proof. exact (@lem5706968 term76). Qed.
Lemma lem5706970 : term205 = term81.
Proof. exact (TRANS (@lem5706966) (@lem5706969)). Qed.
Lemma lem5706971 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5706972 : term207 = term208.
Proof. exact (MK_COMB (@lem5706971) (@lem5706970)). Qed.
Lemma lem5706973 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem5706974 : term209 = term173.
Proof. exact (MK_COMB (@lem5706972) (@lem5706973)). Qed.
Lemma lem5706976 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5706977 : term173 = term81.
Proof. exact (@lem5706976 term76). Qed.
Lemma lem5706978 : term209 = term81.
Proof. exact (TRANS (@lem5706974) (@lem5706977)). Qed.
Lemma lem5706980 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5706981 : term119 = term120.
Proof. exact (@lem5706980 term76 term76). Qed.
Lemma lem5706982 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5706983 : term122 = term76.
Proof. exact (EQ_MP (@lem5706982) (@lem940073)). Qed.
Lemma lem5706984 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5706985 : term120 = term75.
Proof. exact (MK_COMB (@lem5706984) (@lem5706983)). Qed.
Lemma lem5706986 : term119 = term75.
Proof. exact (TRANS (@lem5706981) (@lem5706985)). Qed.
Lemma lem5706987 : term208 = term208.
Proof. exact (eq_refl term208). Qed.
Lemma lem5706988 : term210 = term173.
Proof. exact (MK_COMB (@lem5706987) (@lem5706986)). Qed.
Lemma lem5706990 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5706991 : term173 = term81.
Proof. exact (@lem5706990 term76). Qed.
Lemma lem5706992 : term210 = term81.
Proof. exact (TRANS (@lem5706988) (@lem5706991)). Qed.
Lemma lem5706993 : term81 = term210.
Proof. exact (SYM (@lem5706992)). Qed.
Lemma lem5706994 : term209 = term210.
Proof. exact (TRANS (@lem5706978) (@lem5706993)). Qed.
Lemma lem5706995 : term199 = term162.
Proof. exact (@lem5706945 (@lem5706994)). Qed.
Lemma lem5706996 : term198 = term162.
Proof. exact (TRANS (@lem5706911) (@lem5706995)). Qed.
Lemma lem5706998 (x : real) : (term128 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5706999 : term162 = term81.
Proof. exact (@lem5706998 term81). Qed.
Lemma lem5707000 : term198 = term81.
Proof. exact (TRANS (@lem5706996) (@lem5706999)). Qed.
Lemma lem5707001 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5707002 : term211 = term208.
Proof. exact (MK_COMB (@lem5707001) (@lem5707000)). Qed.
Lemma lem5707003 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem5707004 (x : int) : (term195 x) = (term212 x).
Proof. exact (MK_COMB (@lem5707002) (@lem5707003 x)). Qed.
Lemma lem5707005 (x : int) : (term194 x) = (term212 x).
Proof. exact (TRANS (@lem5706902 x) (@lem5707004 x)). Qed.
Lemma lem5707006 (x : int) : (term212 x) = term81.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem5707007 (x : int) : (term194 x) = term81.
Proof. exact (TRANS (@lem5707005 x) (@lem5707006 x)). Qed.
Lemma lem5707008 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5707009 (x : int) : (term213 x) = term145.
Proof. exact (MK_COMB (@lem5707008) (@lem5707007 x)). Qed.
Lemma lem5707011 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5707012 : term103 = term111.
Proof. exact (@lem5707011 term76). Qed.
Lemma lem5707014 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5707015 : term103 = term111.
Proof. exact (@lem5707014 term76). Qed.
Lemma lem5707016 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5707017 : term196 = term197.
Proof. exact (MK_COMB (@lem5707016) (@lem5707015)). Qed.
Lemma lem5707018 : term596 = term597.
Proof. exact (MK_COMB (@lem5707017) (@lem5707012)). Qed.
Lemma lem5707019 : term598.
Proof. exact (@lem1981473 term103 term75 term103 term75 term599 term75). Qed.
Lemma lem5707021 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5707022 : term161 = term168.
Proof. exact (@lem5707021 (NUMERAL 0) term76). Qed.
Lemma lem5707023 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5707024 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5707025 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5707024 h1) (fun h1 : term168 = True => @lem5707023)). Qed.
Lemma lem5707026 : term168 = True.
Proof. exact (EQ_MP (@lem5707025) (@lem5707023)). Qed.
Lemma lem5707027 : term161 = True.
Proof. exact (TRANS (@lem5707022) (@lem5707026)). Qed.
Lemma lem5707028 : True = term161.
Proof. exact (SYM (@lem5707027)). Qed.
Lemma lem5707029 : term161.
Proof. exact (EQ_MP (@lem5707028) (@lem0)). Qed.
Lemma lem5707030 : term600.
Proof. exact (@lem5707019 (@lem5707029)). Qed.
Lemma lem5707032 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5707033 : term161 = term168.
Proof. exact (@lem5707032 (NUMERAL 0) term76). Qed.
Lemma lem5707034 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5707035 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5707036 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5707035 h1) (fun h1 : term168 = True => @lem5707034)). Qed.
Lemma lem5707037 : term168 = True.
Proof. exact (EQ_MP (@lem5707036) (@lem5707034)). Qed.
Lemma lem5707038 : term161 = True.
Proof. exact (TRANS (@lem5707033) (@lem5707037)). Qed.
Lemma lem5707039 : True = term161.
Proof. exact (SYM (@lem5707038)). Qed.
Lemma lem5707040 : term161.
Proof. exact (EQ_MP (@lem5707039) (@lem0)). Qed.
Lemma lem5707041 : term601.
Proof. exact (@lem5707030 (@lem5707040)). Qed.
Lemma lem5707043 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5707044 : term161 = term168.
Proof. exact (@lem5707043 (NUMERAL 0) term76). Qed.
Lemma lem5707045 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5707046 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5707047 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5707046 h1) (fun h1 : term168 = True => @lem5707045)). Qed.
Lemma lem5707048 : term168 = True.
Proof. exact (EQ_MP (@lem5707047) (@lem5707045)). Qed.
Lemma lem5707049 : term161 = True.
Proof. exact (TRANS (@lem5707044) (@lem5707048)). Qed.
Lemma lem5707050 : True = term161.
Proof. exact (SYM (@lem5707049)). Qed.
Lemma lem5707051 : term161.
Proof. exact (EQ_MP (@lem5707050) (@lem0)). Qed.
Lemma lem5707052 : term602.
Proof. exact (@lem5707041 (@lem5707051)). Qed.
Lemma lem5707054 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5707055 : term114 = term125.
Proof. exact (@lem5707054 term76 term76). Qed.
Lemma lem5707056 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5707057 : term122 = term76.
Proof. exact (EQ_MP (@lem5707056) (@lem940073)). Qed.
Lemma lem5707058 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5707059 : term120 = term75.
Proof. exact (MK_COMB (@lem5707058) (@lem5707057)). Qed.
Lemma lem5707060 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5707061 : term125 = term103.
Proof. exact (MK_COMB (@lem5707060) (@lem5707059)). Qed.
Lemma lem5707062 : term114 = term103.
Proof. exact (TRANS (@lem5707055) (@lem5707061)). Qed.
Lemma lem5707064 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5707065 : term114 = term125.
Proof. exact (@lem5707064 term76 term76). Qed.
Lemma lem5707066 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5707067 : term122 = term76.
Proof. exact (EQ_MP (@lem5707066) (@lem940073)). Qed.
Lemma lem5707068 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5707069 : term120 = term75.
Proof. exact (MK_COMB (@lem5707068) (@lem5707067)). Qed.
Lemma lem5707070 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5707071 : term125 = term103.
Proof. exact (MK_COMB (@lem5707070) (@lem5707069)). Qed.
Lemma lem5707072 : term114 = term103.
Proof. exact (TRANS (@lem5707065) (@lem5707071)). Qed.
Lemma lem5707073 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5707074 : term204 = term196.
Proof. exact (MK_COMB (@lem5707073) (@lem5707072)). Qed.
Lemma lem5707075 : term603 = term596.
Proof. exact (MK_COMB (@lem5707074) (@lem5707062)). Qed.
Lemma lem5707076 : term596 = term604.
Proof. exact (@lem1367763 term76 term76). Qed.
Lemma lem5707077 : term605 = term606.
Proof. exact (@lem706885). Qed.
Lemma lem5707078 : (term605 = term606) = (term607 = term608).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term606). Qed.
Lemma lem5707079 : term607 = term608.
Proof. exact (EQ_MP (@lem5707078) (@lem5707077)). Qed.
Lemma lem5707080 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5707081 : term609 = term610.
Proof. exact (MK_COMB (@lem5707080) (@lem5707079)). Qed.
Lemma lem5707082 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5707083 : term604 = term599.
Proof. exact (MK_COMB (@lem5707082) (@lem5707081)). Qed.
Lemma lem5707084 : term596 = term599.
Proof. exact (TRANS (@lem5707076) (@lem5707083)). Qed.
Lemma lem5707085 : term603 = term599.
Proof. exact (TRANS (@lem5707075) (@lem5707084)). Qed.
Lemma lem5707086 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5707087 : term611 = term612.
Proof. exact (MK_COMB (@lem5707086) (@lem5707085)). Qed.
Lemma lem5707088 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem5707089 : term613 = term614.
Proof. exact (MK_COMB (@lem5707087) (@lem5707088)). Qed.
Lemma lem5707091 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5707092 : term614 = term615.
Proof. exact (@lem5707091 term608 term76). Qed.
Lemma lem5707093 : term616 = term606.
Proof. exact (@lem996237 term606). Qed.
Lemma lem5707094 : (term616 = term606) = (term617 = term608).
Proof. exact (@lem1007663 term606 (BIT1 0) term606). Qed.
Lemma lem5707095 : term617 = term608.
Proof. exact (EQ_MP (@lem5707094) (@lem5707093)). Qed.
Lemma lem5707096 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5707097 : term618 = term610.
Proof. exact (MK_COMB (@lem5707096) (@lem5707095)). Qed.
Lemma lem5707098 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5707099 : term615 = term599.
Proof. exact (MK_COMB (@lem5707098) (@lem5707097)). Qed.
Lemma lem5707100 : term614 = term599.
Proof. exact (TRANS (@lem5707092) (@lem5707099)). Qed.
Lemma lem5707101 : term613 = term599.
Proof. exact (TRANS (@lem5707089) (@lem5707100)). Qed.
Lemma lem5707103 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5707104 : term119 = term120.
Proof. exact (@lem5707103 term76 term76). Qed.
Lemma lem5707105 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5707106 : term122 = term76.
Proof. exact (EQ_MP (@lem5707105) (@lem940073)). Qed.
Lemma lem5707107 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5707108 : term120 = term75.
Proof. exact (MK_COMB (@lem5707107) (@lem5707106)). Qed.
Lemma lem5707109 : term119 = term75.
Proof. exact (TRANS (@lem5707104) (@lem5707108)). Qed.
Lemma lem5707110 : term612 = term612.
Proof. exact (eq_refl term612). Qed.
Lemma lem5707111 : term619 = term614.
Proof. exact (MK_COMB (@lem5707110) (@lem5707109)). Qed.
Lemma lem5707113 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5707114 : term614 = term615.
Proof. exact (@lem5707113 term608 term76). Qed.
Lemma lem5707115 : term616 = term606.
Proof. exact (@lem996237 term606). Qed.
Lemma lem5707116 : (term616 = term606) = (term617 = term608).
Proof. exact (@lem1007663 term606 (BIT1 0) term606). Qed.
Lemma lem5707117 : term617 = term608.
Proof. exact (EQ_MP (@lem5707116) (@lem5707115)). Qed.
Lemma lem5707118 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5707119 : term618 = term610.
Proof. exact (MK_COMB (@lem5707118) (@lem5707117)). Qed.
Lemma lem5707120 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5707121 : term615 = term599.
Proof. exact (MK_COMB (@lem5707120) (@lem5707119)). Qed.
Lemma lem5707122 : term614 = term599.
Proof. exact (TRANS (@lem5707114) (@lem5707121)). Qed.
Lemma lem5707123 : term619 = term599.
Proof. exact (TRANS (@lem5707111) (@lem5707122)). Qed.
Lemma lem5707124 : term599 = term619.
Proof. exact (SYM (@lem5707123)). Qed.
Lemma lem5707125 : term613 = term619.
Proof. exact (TRANS (@lem5707101) (@lem5707124)). Qed.
Lemma lem5707126 : term597 = term620.
Proof. exact (@lem5707052 (@lem5707125)). Qed.
Lemma lem5707127 : term596 = term620.
Proof. exact (TRANS (@lem5707018) (@lem5707126)). Qed.
Lemma lem5707129 (x : real) : (term128 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5707130 : term620 = term599.
Proof. exact (@lem5707129 term599). Qed.
Lemma lem5707131 : term596 = term599.
Proof. exact (TRANS (@lem5707127) (@lem5707130)). Qed.
Lemma lem5707132 (x : int) : (term595 x) = term621.
Proof. exact (MK_COMB (@lem5707009 x) (@lem5707131)). Qed.
Lemma lem5707133 (x : int) : (term594 x) = term621.
Proof. exact (TRANS (@lem5706901 x) (@lem5707132 x)). Qed.
Lemma lem5707134 : term621 = term599.
Proof. exact (@lem1982721 term599). Qed.
Lemma lem5707135 (x : int) : (term594 x) = term599.
Proof. exact (TRANS (@lem5707133 x) (@lem5707134)). Qed.
Lemma lem5707136 (l : int) (x : int) : (term592 l x) = term621.
Proof. exact (MK_COMB (@lem5706900 l) (@lem5707135 x)). Qed.
Lemma lem5707137 (l : int) (x : int) : (term591 l x) = term621.
Proof. exact (TRANS (@lem5706792 l x) (@lem5707136 l x)). Qed.
Lemma lem5707138 : term621 = term599.
Proof. exact (@lem1982721 term599). Qed.
Lemma lem5707139 (l : int) (x : int) : (term591 l x) = term599.
Proof. exact (TRANS (@lem5707137 l x) (@lem5707138)). Qed.
Lemma lem5707140 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5707141 (l : int) (x : int) : (term622 l x) = term623.
Proof. exact (MK_COMB (@lem5707140) (@lem5707139 l x)). Qed.
Lemma lem5707142 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem5707143 (l : int) (x : int) : (term590 l x) = term624.
Proof. exact (MK_COMB (@lem5707141 l x) (@lem5707142)). Qed.
Lemma lem5707144 (r : int) (l : int) (x : int) (h1 : term702 r l x) : term624.
Proof. exact (EQ_MP (@lem5707143 l x) (@lem5706791 r l x h1)). Qed.
Lemma lem5707146 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5707147 : term624 = term625.
Proof. exact (@lem5707146 term81 term599). Qed.
Lemma lem5707149 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5707150 : term599 = term620.
Proof. exact (@lem5707149 term608). Qed.
Lemma lem5707152 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5707153 : term81 = term162.
Proof. exact (@lem5707152 (NUMERAL 0)). Qed.
Lemma lem5707154 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5707155 : term236 = term237.
Proof. exact (MK_COMB (@lem5707154) (@lem5707153)). Qed.
Lemma lem5707156 : term625 = term626.
Proof. exact (MK_COMB (@lem5707155) (@lem5707150)). Qed.
Lemma lem5707157 : term627.
Proof. exact (@lem1980026 term81 term75 term599 term75). Qed.
Lemma lem5707159 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5707160 : term161 = term168.
Proof. exact (@lem5707159 (NUMERAL 0) term76). Qed.
Lemma lem5707161 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5707162 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5707163 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5707162 h1) (fun h1 : term168 = True => @lem5707161)). Qed.
Lemma lem5707164 : term168 = True.
Proof. exact (EQ_MP (@lem5707163) (@lem5707161)). Qed.
Lemma lem5707165 : term161 = True.
Proof. exact (TRANS (@lem5707160) (@lem5707164)). Qed.
Lemma lem5707166 : True = term161.
Proof. exact (SYM (@lem5707165)). Qed.
Lemma lem5707167 : term161.
Proof. exact (EQ_MP (@lem5707166) (@lem0)). Qed.
Lemma lem5707168 : term628.
Proof. exact (@lem5707157 (@lem5707167)). Qed.
Lemma lem5707170 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5707171 : term161 = term168.
Proof. exact (@lem5707170 (NUMERAL 0) term76). Qed.
Lemma lem5707172 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5707173 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5707174 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5707173 h1) (fun h1 : term168 = True => @lem5707172)). Qed.
Lemma lem5707175 : term168 = True.
Proof. exact (EQ_MP (@lem5707174) (@lem5707172)). Qed.
Lemma lem5707176 : term161 = True.
Proof. exact (TRANS (@lem5707171) (@lem5707175)). Qed.
Lemma lem5707177 : True = term161.
Proof. exact (SYM (@lem5707176)). Qed.
Lemma lem5707178 : term161.
Proof. exact (EQ_MP (@lem5707177) (@lem0)). Qed.
Lemma lem5707179 : term626 = term629.
Proof. exact (@lem5707168 (@lem5707178)). Qed.
Lemma lem5707181 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5707182 : term614 = term615.
Proof. exact (@lem5707181 term608 term76). Qed.
Lemma lem5707183 : term616 = term606.
Proof. exact (@lem996237 term606). Qed.
Lemma lem5707184 : (term616 = term606) = (term617 = term608).
Proof. exact (@lem1007663 term606 (BIT1 0) term606). Qed.
Lemma lem5707185 : term617 = term608.
Proof. exact (EQ_MP (@lem5707184) (@lem5707183)). Qed.
Lemma lem5707186 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5707187 : term618 = term610.
Proof. exact (MK_COMB (@lem5707186) (@lem5707185)). Qed.
Lemma lem5707188 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5707189 : term615 = term599.
Proof. exact (MK_COMB (@lem5707188) (@lem5707187)). Qed.
Lemma lem5707190 : term614 = term599.
Proof. exact (TRANS (@lem5707182) (@lem5707189)). Qed.
Lemma lem5707192 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5707193 : term173 = term81.
Proof. exact (@lem5707192 term76). Qed.
Lemma lem5707194 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5707195 : term242 = term236.
Proof. exact (MK_COMB (@lem5707194) (@lem5707193)). Qed.
Lemma lem5707196 : term629 = term625.
Proof. exact (MK_COMB (@lem5707195) (@lem5707190)). Qed.
Lemma lem5707198 (m : nat) (n : nat) : (term243 m n) = (term244 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5707199 : term625 = term630.
Proof. exact (@lem5707198 (NUMERAL 0) term608). Qed.
Lemma lem5707200 : term631 = term606.
Proof. exact (@lem912803). Qed.
Lemma lem5707201 (h1 : term631 = term606) : (term608 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term606 h1). Qed.
Lemma lem5707202 : (term631 = term606) = ((term608 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term631 = term606 => @lem5707201 h1) (fun h1 : (term608 = (NUMERAL 0)) = False => @lem5707200)). Qed.
Lemma lem5707203 : (term608 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5707202) (@lem5707200)). Qed.
Lemma lem5707204 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5707205 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5707206 : term246 = (and True).
Proof. exact (MK_COMB (@lem5707205) (@lem5707204)). Qed.
Lemma lem5707207 : term630 = (True /\ False).
Proof. exact (MK_COMB (@lem5707206) (@lem5707203)). Qed.
Lemma lem5707209 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5707210 : term630 = False.
Proof. exact (TRANS (@lem5707207) (@lem5707209)). Qed.
Lemma lem5707211 : term625 = False.
Proof. exact (TRANS (@lem5707199) (@lem5707210)). Qed.
Lemma lem5707212 : term629 = False.
Proof. exact (TRANS (@lem5707196) (@lem5707211)). Qed.
Lemma lem5707213 : term626 = False.
Proof. exact (TRANS (@lem5707179) (@lem5707212)). Qed.
Lemma lem5707214 : term625 = False.
Proof. exact (TRANS (@lem5707156) (@lem5707213)). Qed.
Lemma lem5707215 : term624 = False.
Proof. exact (TRANS (@lem5707147) (@lem5707214)). Qed.
Lemma lem5707216 (r : int) (l : int) (x : int) (h1 : term702 r l x) : False.
Proof. exact (EQ_MP (@lem5707215) (@lem5707144 r l x h1)). Qed.
Lemma lem5707217 (l : int) (r : int) (x : int) (h1 : term703 l r x) : term703 l r x.
Proof. exact (h1). Qed.
Lemma lem5707218 (l : int) (r : int) (x : int) (h1 : term703 l r x) : term563 r x.
Proof. exact (proj2 (@lem5707217 l r x h1)). Qed.
Lemma lem5707219 (l : int) (r : int) (x : int) (h1 : term703 l r x) : term694 l r x.
Proof. exact (proj1 (@lem5707217 l r x h1)). Qed.
Lemma lem5707220 (l : int) (r : int) (x : int) (h1 : term703 l r x) : term149 r x.
Proof. exact (proj2 (@lem5707219 l r x h1)). Qed.
Lemma lem5707223 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5707224 : term160 = term161.
Proof. exact (@lem5707223 term81 term75). Qed.
Lemma lem5707226 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5707227 : term75 = term108.
Proof. exact (@lem5707226 term76). Qed.
Lemma lem5707229 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5707230 : term81 = term162.
Proof. exact (@lem5707229 (NUMERAL 0)). Qed.
Lemma lem5707231 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5707232 : term163 = term164.
Proof. exact (MK_COMB (@lem5707231) (@lem5707230)). Qed.
Lemma lem5707233 : term161 = term165.
Proof. exact (MK_COMB (@lem5707232) (@lem5707227)). Qed.
Lemma lem5707234 : term166.
Proof. exact (@lem1980255 term81 term75 term75 term75). Qed.
Lemma lem5707236 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5707237 : term161 = term168.
Proof. exact (@lem5707236 (NUMERAL 0) term76). Qed.
Lemma lem5707238 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5707239 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5707240 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5707239 h1) (fun h1 : term168 = True => @lem5707238)). Qed.
Lemma lem5707241 : term168 = True.
Proof. exact (EQ_MP (@lem5707240) (@lem5707238)). Qed.
Lemma lem5707242 : term161 = True.
Proof. exact (TRANS (@lem5707237) (@lem5707241)). Qed.
Lemma lem5707243 : True = term161.
Proof. exact (SYM (@lem5707242)). Qed.
Lemma lem5707244 : term161.
Proof. exact (EQ_MP (@lem5707243) (@lem0)). Qed.
Lemma lem5707245 : term170.
Proof. exact (@lem5707234 (@lem5707244)). Qed.
Lemma lem5707247 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5707248 : term161 = term168.
Proof. exact (@lem5707247 (NUMERAL 0) term76). Qed.
Lemma lem5707249 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5707250 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5707251 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5707250 h1) (fun h1 : term168 = True => @lem5707249)). Qed.
Lemma lem5707252 : term168 = True.
Proof. exact (EQ_MP (@lem5707251) (@lem5707249)). Qed.
Lemma lem5707253 : term161 = True.
Proof. exact (TRANS (@lem5707248) (@lem5707252)). Qed.
Lemma lem5707254 : True = term161.
Proof. exact (SYM (@lem5707253)). Qed.
Lemma lem5707255 : term161.
Proof. exact (EQ_MP (@lem5707254) (@lem0)). Qed.
Lemma lem5707256 : term165 = term171.
Proof. exact (@lem5707245 (@lem5707255)). Qed.
Lemma lem5707258 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5707259 : term119 = term120.
Proof. exact (@lem5707258 term76 term76). Qed.
Lemma lem5707260 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5707261 : term122 = term76.
Proof. exact (EQ_MP (@lem5707260) (@lem940073)). Qed.
Lemma lem5707262 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5707263 : term120 = term75.
Proof. exact (MK_COMB (@lem5707262) (@lem5707261)). Qed.
Lemma lem5707264 : term119 = term75.
Proof. exact (TRANS (@lem5707259) (@lem5707263)). Qed.
Lemma lem5707266 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5707267 : term173 = term81.
Proof. exact (@lem5707266 term76). Qed.
Lemma lem5707268 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5707269 : term174 = term163.
Proof. exact (MK_COMB (@lem5707268) (@lem5707267)). Qed.
Lemma lem5707270 : term171 = term161.
Proof. exact (MK_COMB (@lem5707269) (@lem5707264)). Qed.
Lemma lem5707272 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5707273 : term161 = term168.
Proof. exact (@lem5707272 (NUMERAL 0) term76). Qed.
Lemma lem5707274 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5707275 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5707276 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5707275 h1) (fun h1 : term168 = True => @lem5707274)). Qed.
Lemma lem5707277 : term168 = True.
Proof. exact (EQ_MP (@lem5707276) (@lem5707274)). Qed.
Lemma lem5707278 : term161 = True.
Proof. exact (TRANS (@lem5707273) (@lem5707277)). Qed.
Lemma lem5707279 : term171 = True.
Proof. exact (TRANS (@lem5707270) (@lem5707278)). Qed.
Lemma lem5707280 : term165 = True.
Proof. exact (TRANS (@lem5707256) (@lem5707279)). Qed.
Lemma lem5707281 : term161 = True.
Proof. exact (TRANS (@lem5707233) (@lem5707280)). Qed.
Lemma lem5707282 : term160 = True.
Proof. exact (TRANS (@lem5707224) (@lem5707281)). Qed.
Lemma lem5707283 : True = term160.
Proof. exact (SYM (@lem5707282)). Qed.
Lemma lem5707284 : term160.
Proof. exact (EQ_MP (@lem5707283) (@lem0)). Qed.
Lemma lem5707285 (l : int) (r : int) (x : int) (h1 : term703 l r x) : term583 r x.
Proof. exact (conj (@lem5707284) (@lem5707218 l r x h1)). Qed.
Lemma lem5707287 (x : real) (y : real) : term176 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5707288 (r : int) (x : int) : term584 r x.
Proof. exact (@lem5707287 term75 (term561 r x)). Qed.
Lemma lem5707289 (l : int) (r : int) (x : int) (h1 : term703 l r x) : term585 r x.
Proof. exact (@lem5707288 r x (@lem5707285 l r x h1)). Qed.
Lemma lem5707290 (r : int) (x : int) : (term586 r x) = (term561 r x).
Proof. exact (@lem1982733 (term561 r x)). Qed.
Lemma lem5707291 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5707292 (r : int) (x : int) : (term587 r x) = (term562 r x).
Proof. exact (MK_COMB (@lem5707291) (@lem5707290 r x)). Qed.
Lemma lem5707293 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem5707294 (r : int) (x : int) : (term585 r x) = (term563 r x).
Proof. exact (MK_COMB (@lem5707292 r x) (@lem5707293)). Qed.
Lemma lem5707295 (l : int) (r : int) (x : int) (h1 : term703 l r x) : term563 r x.
Proof. exact (EQ_MP (@lem5707294 r x) (@lem5707289 l r x h1)). Qed.
Lemma lem5707297 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5707298 : term160 = term161.
Proof. exact (@lem5707297 term81 term75). Qed.
Lemma lem5707300 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5707301 : term75 = term108.
Proof. exact (@lem5707300 term76). Qed.
Lemma lem5707303 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5707304 : term81 = term162.
Proof. exact (@lem5707303 (NUMERAL 0)). Qed.
Lemma lem5707305 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5707306 : term163 = term164.
Proof. exact (MK_COMB (@lem5707305) (@lem5707304)). Qed.
Lemma lem5707307 : term161 = term165.
Proof. exact (MK_COMB (@lem5707306) (@lem5707301)). Qed.
Lemma lem5707308 : term166.
Proof. exact (@lem1980255 term81 term75 term75 term75). Qed.
Lemma lem5707310 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5707311 : term161 = term168.
Proof. exact (@lem5707310 (NUMERAL 0) term76). Qed.
Lemma lem5707312 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5707313 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5707314 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5707313 h1) (fun h1 : term168 = True => @lem5707312)). Qed.
Lemma lem5707315 : term168 = True.
Proof. exact (EQ_MP (@lem5707314) (@lem5707312)). Qed.
Lemma lem5707316 : term161 = True.
Proof. exact (TRANS (@lem5707311) (@lem5707315)). Qed.
Lemma lem5707317 : True = term161.
Proof. exact (SYM (@lem5707316)). Qed.
Lemma lem5707318 : term161.
Proof. exact (EQ_MP (@lem5707317) (@lem0)). Qed.
Lemma lem5707319 : term170.
Proof. exact (@lem5707308 (@lem5707318)). Qed.
Lemma lem5707321 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5707322 : term161 = term168.
Proof. exact (@lem5707321 (NUMERAL 0) term76). Qed.
Lemma lem5707323 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5707324 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5707325 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5707324 h1) (fun h1 : term168 = True => @lem5707323)). Qed.
Lemma lem5707326 : term168 = True.
Proof. exact (EQ_MP (@lem5707325) (@lem5707323)). Qed.
Lemma lem5707327 : term161 = True.
Proof. exact (TRANS (@lem5707322) (@lem5707326)). Qed.
Lemma lem5707328 : True = term161.
Proof. exact (SYM (@lem5707327)). Qed.
Lemma lem5707329 : term161.
Proof. exact (EQ_MP (@lem5707328) (@lem0)). Qed.
Lemma lem5707330 : term165 = term171.
Proof. exact (@lem5707319 (@lem5707329)). Qed.
Lemma lem5707332 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5707333 : term119 = term120.
Proof. exact (@lem5707332 term76 term76). Qed.
Lemma lem5707334 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5707335 : term122 = term76.
Proof. exact (EQ_MP (@lem5707334) (@lem940073)). Qed.
Lemma lem5707336 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5707337 : term120 = term75.
Proof. exact (MK_COMB (@lem5707336) (@lem5707335)). Qed.
Lemma lem5707338 : term119 = term75.
Proof. exact (TRANS (@lem5707333) (@lem5707337)). Qed.
Lemma lem5707340 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5707341 : term173 = term81.
Proof. exact (@lem5707340 term76). Qed.
Lemma lem5707342 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5707343 : term174 = term163.
Proof. exact (MK_COMB (@lem5707342) (@lem5707341)). Qed.
Lemma lem5707344 : term171 = term161.
Proof. exact (MK_COMB (@lem5707343) (@lem5707338)). Qed.
Lemma lem5707346 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5707347 : term161 = term168.
Proof. exact (@lem5707346 (NUMERAL 0) term76). Qed.
Lemma lem5707348 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5707349 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5707350 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5707349 h1) (fun h1 : term168 = True => @lem5707348)). Qed.
Lemma lem5707351 : term168 = True.
Proof. exact (EQ_MP (@lem5707350) (@lem5707348)). Qed.
Lemma lem5707352 : term161 = True.
Proof. exact (TRANS (@lem5707347) (@lem5707351)). Qed.
Lemma lem5707353 : term171 = True.
Proof. exact (TRANS (@lem5707344) (@lem5707352)). Qed.
Lemma lem5707354 : term165 = True.
Proof. exact (TRANS (@lem5707330) (@lem5707353)). Qed.
Lemma lem5707355 : term161 = True.
Proof. exact (TRANS (@lem5707307) (@lem5707354)). Qed.
Lemma lem5707356 : term160 = True.
Proof. exact (TRANS (@lem5707298) (@lem5707355)). Qed.
Lemma lem5707357 : True = term160.
Proof. exact (SYM (@lem5707356)). Qed.
Lemma lem5707358 : term160.
Proof. exact (EQ_MP (@lem5707357) (@lem0)). Qed.
Lemma lem5707359 (l : int) (r : int) (x : int) (h1 : term703 l r x) : term181 r x.
Proof. exact (conj (@lem5707358) (@lem5707220 l r x h1)). Qed.
Lemma lem5707361 (x : real) (y : real) : term176 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5707362 (r : int) (x : int) : term182 r x.
Proof. exact (@lem5707361 term75 (term144 r x)). Qed.
Lemma lem5707363 (l : int) (r : int) (x : int) (h1 : term703 l r x) : term183 r x.
Proof. exact (@lem5707362 r x (@lem5707359 l r x h1)). Qed.
Lemma lem5707364 (r : int) (x : int) : (term184 r x) = (term144 r x).
Proof. exact (@lem1982733 (term144 r x)). Qed.
Lemma lem5707365 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5707366 (r : int) (x : int) : (term185 r x) = (term148 r x).
Proof. exact (MK_COMB (@lem5707365) (@lem5707364 r x)). Qed.
Lemma lem5707367 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem5707368 (r : int) (x : int) : (term183 r x) = (term149 r x).
Proof. exact (MK_COMB (@lem5707366 r x) (@lem5707367)). Qed.
Lemma lem5707369 (l : int) (r : int) (x : int) (h1 : term703 l r x) : term149 r x.
Proof. exact (EQ_MP (@lem5707368 r x) (@lem5707363 l r x h1)). Qed.
Lemma lem5707370 (l : int) (r : int) (x : int) (h1 : term703 l r x) : term588 r x.
Proof. exact (conj (@lem5707369 l r x h1) (@lem5707295 l r x h1)). Qed.
Lemma lem5707372 (x : real) (y : real) : term187 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5707373 (r : int) (x : int) : term589 r x.
Proof. exact (@lem5707372 (term144 r x) (term561 r x)). Qed.
Lemma lem5707374 (l : int) (r : int) (x : int) (h1 : term703 l r x) : term590 r x.
Proof. exact (@lem5707373 r x (@lem5707370 l r x h1)). Qed.
Lemma lem5707375 (r : int) (x : int) : (term591 r x) = (term592 r x).
Proof. exact (@lem1982753 (real_of_int r) (term93 r) (term130 x) (term593 x)). Qed.
Lemma lem5707376 (r : int) : (term229 r) = (term195 r).
Proof. exact (@lem1982715 term103 (real_of_int r)). Qed.
Lemma lem5707378 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5707379 : term75 = term108.
Proof. exact (@lem5707378 term76). Qed.
Lemma lem5707381 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5707382 : term103 = term111.
Proof. exact (@lem5707381 term76). Qed.
Lemma lem5707383 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5707384 : term196 = term197.
Proof. exact (MK_COMB (@lem5707383) (@lem5707382)). Qed.
Lemma lem5707385 : term198 = term199.
Proof. exact (MK_COMB (@lem5707384) (@lem5707379)). Qed.
Lemma lem5707386 : term200.
Proof. exact (@lem1981473 term103 term75 term75 term75 term81 term75). Qed.
Lemma lem5707388 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5707389 : term161 = term168.
Proof. exact (@lem5707388 (NUMERAL 0) term76). Qed.
Lemma lem5707390 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5707391 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5707392 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5707391 h1) (fun h1 : term168 = True => @lem5707390)). Qed.
Lemma lem5707393 : term168 = True.
Proof. exact (EQ_MP (@lem5707392) (@lem5707390)). Qed.
Lemma lem5707394 : term161 = True.
Proof. exact (TRANS (@lem5707389) (@lem5707393)). Qed.
Lemma lem5707395 : True = term161.
Proof. exact (SYM (@lem5707394)). Qed.
Lemma lem5707396 : term161.
Proof. exact (EQ_MP (@lem5707395) (@lem0)). Qed.
Lemma lem5707397 : term201.
Proof. exact (@lem5707386 (@lem5707396)). Qed.
Lemma lem5707399 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5707400 : term161 = term168.
Proof. exact (@lem5707399 (NUMERAL 0) term76). Qed.
Lemma lem5707401 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5707402 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5707403 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5707402 h1) (fun h1 : term168 = True => @lem5707401)). Qed.
Lemma lem5707404 : term168 = True.
Proof. exact (EQ_MP (@lem5707403) (@lem5707401)). Qed.
Lemma lem5707405 : term161 = True.
Proof. exact (TRANS (@lem5707400) (@lem5707404)). Qed.
Lemma lem5707406 : True = term161.
Proof. exact (SYM (@lem5707405)). Qed.
Lemma lem5707407 : term161.
Proof. exact (EQ_MP (@lem5707406) (@lem0)). Qed.
Lemma lem5707408 : term202.
Proof. exact (@lem5707397 (@lem5707407)). Qed.
Lemma lem5707410 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5707411 : term161 = term168.
Proof. exact (@lem5707410 (NUMERAL 0) term76). Qed.
Lemma lem5707412 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5707413 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5707414 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5707413 h1) (fun h1 : term168 = True => @lem5707412)). Qed.
Lemma lem5707415 : term168 = True.
Proof. exact (EQ_MP (@lem5707414) (@lem5707412)). Qed.
Lemma lem5707416 : term161 = True.
Proof. exact (TRANS (@lem5707411) (@lem5707415)). Qed.
Lemma lem5707417 : True = term161.
Proof. exact (SYM (@lem5707416)). Qed.
Lemma lem5707418 : term161.
Proof. exact (EQ_MP (@lem5707417) (@lem0)). Qed.
Lemma lem5707419 : term203.
Proof. exact (@lem5707408 (@lem5707418)). Qed.
Lemma lem5707421 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5707422 : term119 = term120.
Proof. exact (@lem5707421 term76 term76). Qed.
Lemma lem5707423 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5707424 : term122 = term76.
Proof. exact (EQ_MP (@lem5707423) (@lem940073)). Qed.
Lemma lem5707425 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5707426 : term120 = term75.
Proof. exact (MK_COMB (@lem5707425) (@lem5707424)). Qed.
Lemma lem5707427 : term119 = term75.
Proof. exact (TRANS (@lem5707422) (@lem5707426)). Qed.
Lemma lem5707429 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5707430 : term114 = term125.
Proof. exact (@lem5707429 term76 term76). Qed.
Lemma lem5707431 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5707432 : term122 = term76.
Proof. exact (EQ_MP (@lem5707431) (@lem940073)). Qed.
Lemma lem5707433 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5707434 : term120 = term75.
Proof. exact (MK_COMB (@lem5707433) (@lem5707432)). Qed.
Lemma lem5707435 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5707436 : term125 = term103.
Proof. exact (MK_COMB (@lem5707435) (@lem5707434)). Qed.
Lemma lem5707437 : term114 = term103.
Proof. exact (TRANS (@lem5707430) (@lem5707436)). Qed.
Lemma lem5707438 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5707439 : term204 = term196.
Proof. exact (MK_COMB (@lem5707438) (@lem5707437)). Qed.
Lemma lem5707440 : term205 = term198.
Proof. exact (MK_COMB (@lem5707439) (@lem5707427)). Qed.
Lemma lem5707442 (m : nat) : (term206 m) = term81.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5707443 : term198 = term81.
Proof. exact (@lem5707442 term76). Qed.
Lemma lem5707444 : term205 = term81.
Proof. exact (TRANS (@lem5707440) (@lem5707443)). Qed.
Lemma lem5707445 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5707446 : term207 = term208.
Proof. exact (MK_COMB (@lem5707445) (@lem5707444)). Qed.
Lemma lem5707447 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem5707448 : term209 = term173.
Proof. exact (MK_COMB (@lem5707446) (@lem5707447)). Qed.
Lemma lem5707450 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5707451 : term173 = term81.
Proof. exact (@lem5707450 term76). Qed.
Lemma lem5707452 : term209 = term81.
Proof. exact (TRANS (@lem5707448) (@lem5707451)). Qed.
Lemma lem5707454 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5707455 : term119 = term120.
Proof. exact (@lem5707454 term76 term76). Qed.
Lemma lem5707456 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5707457 : term122 = term76.
Proof. exact (EQ_MP (@lem5707456) (@lem940073)). Qed.
Lemma lem5707458 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5707459 : term120 = term75.
Proof. exact (MK_COMB (@lem5707458) (@lem5707457)). Qed.
Lemma lem5707460 : term119 = term75.
Proof. exact (TRANS (@lem5707455) (@lem5707459)). Qed.
Lemma lem5707461 : term208 = term208.
Proof. exact (eq_refl term208). Qed.
Lemma lem5707462 : term210 = term173.
Proof. exact (MK_COMB (@lem5707461) (@lem5707460)). Qed.
Lemma lem5707464 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5707465 : term173 = term81.
Proof. exact (@lem5707464 term76). Qed.
Lemma lem5707466 : term210 = term81.
Proof. exact (TRANS (@lem5707462) (@lem5707465)). Qed.
Lemma lem5707467 : term81 = term210.
Proof. exact (SYM (@lem5707466)). Qed.
Lemma lem5707468 : term209 = term210.
Proof. exact (TRANS (@lem5707452) (@lem5707467)). Qed.
Lemma lem5707469 : term199 = term162.
Proof. exact (@lem5707419 (@lem5707468)). Qed.
Lemma lem5707470 : term198 = term162.
Proof. exact (TRANS (@lem5707385) (@lem5707469)). Qed.
Lemma lem5707472 (x : real) : (term128 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5707473 : term162 = term81.
Proof. exact (@lem5707472 term81). Qed.
Lemma lem5707474 : term198 = term81.
Proof. exact (TRANS (@lem5707470) (@lem5707473)). Qed.
Lemma lem5707475 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5707476 : term211 = term208.
Proof. exact (MK_COMB (@lem5707475) (@lem5707474)). Qed.
Lemma lem5707477 (r : int) : (real_of_int r) = (real_of_int r).
Proof. exact (eq_refl (real_of_int r)). Qed.
Lemma lem5707478 (r : int) : (term195 r) = (term212 r).
Proof. exact (MK_COMB (@lem5707476) (@lem5707477 r)). Qed.
Lemma lem5707479 (r : int) : (term229 r) = (term212 r).
Proof. exact (TRANS (@lem5707376 r) (@lem5707478 r)). Qed.
Lemma lem5707480 (r : int) : (term212 r) = term81.
Proof. exact (@lem1982719 (real_of_int r)). Qed.
Lemma lem5707481 (r : int) : (term229 r) = term81.
Proof. exact (TRANS (@lem5707479 r) (@lem5707480 r)). Qed.
Lemma lem5707482 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5707483 (r : int) : (term230 r) = term145.
Proof. exact (MK_COMB (@lem5707482) (@lem5707481 r)). Qed.
Lemma lem5707484 (x : int) : (term594 x) = (term595 x).
Proof. exact (@lem1982753 (term93 x) (real_of_int x) term103 term103). Qed.
Lemma lem5707485 (x : int) : (term194 x) = (term195 x).
Proof. exact (@lem1982713 term103 (real_of_int x)). Qed.
Lemma lem5707487 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5707488 : term75 = term108.
Proof. exact (@lem5707487 term76). Qed.
Lemma lem5707490 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5707491 : term103 = term111.
Proof. exact (@lem5707490 term76). Qed.
Lemma lem5707492 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5707493 : term196 = term197.
Proof. exact (MK_COMB (@lem5707492) (@lem5707491)). Qed.
Lemma lem5707494 : term198 = term199.
Proof. exact (MK_COMB (@lem5707493) (@lem5707488)). Qed.
Lemma lem5707495 : term200.
Proof. exact (@lem1981473 term103 term75 term75 term75 term81 term75). Qed.
Lemma lem5707497 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5707498 : term161 = term168.
Proof. exact (@lem5707497 (NUMERAL 0) term76). Qed.
Lemma lem5707499 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5707500 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5707501 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5707500 h1) (fun h1 : term168 = True => @lem5707499)). Qed.
Lemma lem5707502 : term168 = True.
Proof. exact (EQ_MP (@lem5707501) (@lem5707499)). Qed.
Lemma lem5707503 : term161 = True.
Proof. exact (TRANS (@lem5707498) (@lem5707502)). Qed.
Lemma lem5707504 : True = term161.
Proof. exact (SYM (@lem5707503)). Qed.
Lemma lem5707505 : term161.
Proof. exact (EQ_MP (@lem5707504) (@lem0)). Qed.
Lemma lem5707506 : term201.
Proof. exact (@lem5707495 (@lem5707505)). Qed.
Lemma lem5707508 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5707509 : term161 = term168.
Proof. exact (@lem5707508 (NUMERAL 0) term76). Qed.
Lemma lem5707510 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5707511 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5707512 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5707511 h1) (fun h1 : term168 = True => @lem5707510)). Qed.
Lemma lem5707513 : term168 = True.
Proof. exact (EQ_MP (@lem5707512) (@lem5707510)). Qed.
Lemma lem5707514 : term161 = True.
Proof. exact (TRANS (@lem5707509) (@lem5707513)). Qed.
Lemma lem5707515 : True = term161.
Proof. exact (SYM (@lem5707514)). Qed.
Lemma lem5707516 : term161.
Proof. exact (EQ_MP (@lem5707515) (@lem0)). Qed.
Lemma lem5707517 : term202.
Proof. exact (@lem5707506 (@lem5707516)). Qed.
Lemma lem5707519 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5707520 : term161 = term168.
Proof. exact (@lem5707519 (NUMERAL 0) term76). Qed.
Lemma lem5707521 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5707522 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5707523 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5707522 h1) (fun h1 : term168 = True => @lem5707521)). Qed.
Lemma lem5707524 : term168 = True.
Proof. exact (EQ_MP (@lem5707523) (@lem5707521)). Qed.
Lemma lem5707525 : term161 = True.
Proof. exact (TRANS (@lem5707520) (@lem5707524)). Qed.
Lemma lem5707526 : True = term161.
Proof. exact (SYM (@lem5707525)). Qed.
Lemma lem5707527 : term161.
Proof. exact (EQ_MP (@lem5707526) (@lem0)). Qed.
Lemma lem5707528 : term203.
Proof. exact (@lem5707517 (@lem5707527)). Qed.
Lemma lem5707530 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5707531 : term119 = term120.
Proof. exact (@lem5707530 term76 term76). Qed.
Lemma lem5707532 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5707533 : term122 = term76.
Proof. exact (EQ_MP (@lem5707532) (@lem940073)). Qed.
Lemma lem5707534 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5707535 : term120 = term75.
Proof. exact (MK_COMB (@lem5707534) (@lem5707533)). Qed.
Lemma lem5707536 : term119 = term75.
Proof. exact (TRANS (@lem5707531) (@lem5707535)). Qed.
Lemma lem5707538 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5707539 : term114 = term125.
Proof. exact (@lem5707538 term76 term76). Qed.
Lemma lem5707540 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5707541 : term122 = term76.
Proof. exact (EQ_MP (@lem5707540) (@lem940073)). Qed.
Lemma lem5707542 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5707543 : term120 = term75.
Proof. exact (MK_COMB (@lem5707542) (@lem5707541)). Qed.
Lemma lem5707544 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5707545 : term125 = term103.
Proof. exact (MK_COMB (@lem5707544) (@lem5707543)). Qed.
Lemma lem5707546 : term114 = term103.
Proof. exact (TRANS (@lem5707539) (@lem5707545)). Qed.
Lemma lem5707547 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5707548 : term204 = term196.
Proof. exact (MK_COMB (@lem5707547) (@lem5707546)). Qed.
Lemma lem5707549 : term205 = term198.
Proof. exact (MK_COMB (@lem5707548) (@lem5707536)). Qed.
Lemma lem5707551 (m : nat) : (term206 m) = term81.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5707552 : term198 = term81.
Proof. exact (@lem5707551 term76). Qed.
Lemma lem5707553 : term205 = term81.
Proof. exact (TRANS (@lem5707549) (@lem5707552)). Qed.
Lemma lem5707554 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5707555 : term207 = term208.
Proof. exact (MK_COMB (@lem5707554) (@lem5707553)). Qed.
Lemma lem5707556 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem5707557 : term209 = term173.
Proof. exact (MK_COMB (@lem5707555) (@lem5707556)). Qed.
Lemma lem5707559 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5707560 : term173 = term81.
Proof. exact (@lem5707559 term76). Qed.
Lemma lem5707561 : term209 = term81.
Proof. exact (TRANS (@lem5707557) (@lem5707560)). Qed.
Lemma lem5707563 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5707564 : term119 = term120.
Proof. exact (@lem5707563 term76 term76). Qed.
Lemma lem5707565 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5707566 : term122 = term76.
Proof. exact (EQ_MP (@lem5707565) (@lem940073)). Qed.
Lemma lem5707567 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5707568 : term120 = term75.
Proof. exact (MK_COMB (@lem5707567) (@lem5707566)). Qed.
Lemma lem5707569 : term119 = term75.
Proof. exact (TRANS (@lem5707564) (@lem5707568)). Qed.
Lemma lem5707570 : term208 = term208.
Proof. exact (eq_refl term208). Qed.
Lemma lem5707571 : term210 = term173.
Proof. exact (MK_COMB (@lem5707570) (@lem5707569)). Qed.
Lemma lem5707573 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5707574 : term173 = term81.
Proof. exact (@lem5707573 term76). Qed.
Lemma lem5707575 : term210 = term81.
Proof. exact (TRANS (@lem5707571) (@lem5707574)). Qed.
Lemma lem5707576 : term81 = term210.
Proof. exact (SYM (@lem5707575)). Qed.
Lemma lem5707577 : term209 = term210.
Proof. exact (TRANS (@lem5707561) (@lem5707576)). Qed.
Lemma lem5707578 : term199 = term162.
Proof. exact (@lem5707528 (@lem5707577)). Qed.
Lemma lem5707579 : term198 = term162.
Proof. exact (TRANS (@lem5707494) (@lem5707578)). Qed.
Lemma lem5707581 (x : real) : (term128 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5707582 : term162 = term81.
Proof. exact (@lem5707581 term81). Qed.
Lemma lem5707583 : term198 = term81.
Proof. exact (TRANS (@lem5707579) (@lem5707582)). Qed.
Lemma lem5707584 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5707585 : term211 = term208.
Proof. exact (MK_COMB (@lem5707584) (@lem5707583)). Qed.
Lemma lem5707586 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem5707587 (x : int) : (term195 x) = (term212 x).
Proof. exact (MK_COMB (@lem5707585) (@lem5707586 x)). Qed.
Lemma lem5707588 (x : int) : (term194 x) = (term212 x).
Proof. exact (TRANS (@lem5707485 x) (@lem5707587 x)). Qed.
Lemma lem5707589 (x : int) : (term212 x) = term81.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem5707590 (x : int) : (term194 x) = term81.
Proof. exact (TRANS (@lem5707588 x) (@lem5707589 x)). Qed.
Lemma lem5707591 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5707592 (x : int) : (term213 x) = term145.
Proof. exact (MK_COMB (@lem5707591) (@lem5707590 x)). Qed.
Lemma lem5707594 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5707595 : term103 = term111.
Proof. exact (@lem5707594 term76). Qed.
Lemma lem5707597 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5707598 : term103 = term111.
Proof. exact (@lem5707597 term76). Qed.
Lemma lem5707599 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5707600 : term196 = term197.
Proof. exact (MK_COMB (@lem5707599) (@lem5707598)). Qed.
Lemma lem5707601 : term596 = term597.
Proof. exact (MK_COMB (@lem5707600) (@lem5707595)). Qed.
Lemma lem5707602 : term598.
Proof. exact (@lem1981473 term103 term75 term103 term75 term599 term75). Qed.
Lemma lem5707604 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5707605 : term161 = term168.
Proof. exact (@lem5707604 (NUMERAL 0) term76). Qed.
Lemma lem5707606 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5707607 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5707608 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5707607 h1) (fun h1 : term168 = True => @lem5707606)). Qed.
Lemma lem5707609 : term168 = True.
Proof. exact (EQ_MP (@lem5707608) (@lem5707606)). Qed.
Lemma lem5707610 : term161 = True.
Proof. exact (TRANS (@lem5707605) (@lem5707609)). Qed.
Lemma lem5707611 : True = term161.
Proof. exact (SYM (@lem5707610)). Qed.
Lemma lem5707612 : term161.
Proof. exact (EQ_MP (@lem5707611) (@lem0)). Qed.
Lemma lem5707613 : term600.
Proof. exact (@lem5707602 (@lem5707612)). Qed.
Lemma lem5707615 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5707616 : term161 = term168.
Proof. exact (@lem5707615 (NUMERAL 0) term76). Qed.
Lemma lem5707617 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5707618 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5707619 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5707618 h1) (fun h1 : term168 = True => @lem5707617)). Qed.
Lemma lem5707620 : term168 = True.
Proof. exact (EQ_MP (@lem5707619) (@lem5707617)). Qed.
Lemma lem5707621 : term161 = True.
Proof. exact (TRANS (@lem5707616) (@lem5707620)). Qed.
Lemma lem5707622 : True = term161.
Proof. exact (SYM (@lem5707621)). Qed.
Lemma lem5707623 : term161.
Proof. exact (EQ_MP (@lem5707622) (@lem0)). Qed.
Lemma lem5707624 : term601.
Proof. exact (@lem5707613 (@lem5707623)). Qed.
Lemma lem5707626 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5707627 : term161 = term168.
Proof. exact (@lem5707626 (NUMERAL 0) term76). Qed.
Lemma lem5707628 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5707629 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5707630 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5707629 h1) (fun h1 : term168 = True => @lem5707628)). Qed.
Lemma lem5707631 : term168 = True.
Proof. exact (EQ_MP (@lem5707630) (@lem5707628)). Qed.
Lemma lem5707632 : term161 = True.
Proof. exact (TRANS (@lem5707627) (@lem5707631)). Qed.
Lemma lem5707633 : True = term161.
Proof. exact (SYM (@lem5707632)). Qed.
Lemma lem5707634 : term161.
Proof. exact (EQ_MP (@lem5707633) (@lem0)). Qed.
Lemma lem5707635 : term602.
Proof. exact (@lem5707624 (@lem5707634)). Qed.
Lemma lem5707637 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5707638 : term114 = term125.
Proof. exact (@lem5707637 term76 term76). Qed.
Lemma lem5707639 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5707640 : term122 = term76.
Proof. exact (EQ_MP (@lem5707639) (@lem940073)). Qed.
Lemma lem5707641 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5707642 : term120 = term75.
Proof. exact (MK_COMB (@lem5707641) (@lem5707640)). Qed.
Lemma lem5707643 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5707644 : term125 = term103.
Proof. exact (MK_COMB (@lem5707643) (@lem5707642)). Qed.
Lemma lem5707645 : term114 = term103.
Proof. exact (TRANS (@lem5707638) (@lem5707644)). Qed.
Lemma lem5707647 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5707648 : term114 = term125.
Proof. exact (@lem5707647 term76 term76). Qed.
Lemma lem5707649 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5707650 : term122 = term76.
Proof. exact (EQ_MP (@lem5707649) (@lem940073)). Qed.
Lemma lem5707651 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5707652 : term120 = term75.
Proof. exact (MK_COMB (@lem5707651) (@lem5707650)). Qed.
Lemma lem5707653 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5707654 : term125 = term103.
Proof. exact (MK_COMB (@lem5707653) (@lem5707652)). Qed.
Lemma lem5707655 : term114 = term103.
Proof. exact (TRANS (@lem5707648) (@lem5707654)). Qed.
Lemma lem5707656 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5707657 : term204 = term196.
Proof. exact (MK_COMB (@lem5707656) (@lem5707655)). Qed.
Lemma lem5707658 : term603 = term596.
Proof. exact (MK_COMB (@lem5707657) (@lem5707645)). Qed.
Lemma lem5707659 : term596 = term604.
Proof. exact (@lem1367763 term76 term76). Qed.
Lemma lem5707660 : term605 = term606.
Proof. exact (@lem706885). Qed.
Lemma lem5707661 : (term605 = term606) = (term607 = term608).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term606). Qed.
Lemma lem5707662 : term607 = term608.
Proof. exact (EQ_MP (@lem5707661) (@lem5707660)). Qed.
Lemma lem5707663 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5707664 : term609 = term610.
Proof. exact (MK_COMB (@lem5707663) (@lem5707662)). Qed.
Lemma lem5707665 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5707666 : term604 = term599.
Proof. exact (MK_COMB (@lem5707665) (@lem5707664)). Qed.
Lemma lem5707667 : term596 = term599.
Proof. exact (TRANS (@lem5707659) (@lem5707666)). Qed.
Lemma lem5707668 : term603 = term599.
Proof. exact (TRANS (@lem5707658) (@lem5707667)). Qed.
Lemma lem5707669 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5707670 : term611 = term612.
Proof. exact (MK_COMB (@lem5707669) (@lem5707668)). Qed.
Lemma lem5707671 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem5707672 : term613 = term614.
Proof. exact (MK_COMB (@lem5707670) (@lem5707671)). Qed.
Lemma lem5707674 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5707675 : term614 = term615.
Proof. exact (@lem5707674 term608 term76). Qed.
Lemma lem5707676 : term616 = term606.
Proof. exact (@lem996237 term606). Qed.
Lemma lem5707677 : (term616 = term606) = (term617 = term608).
Proof. exact (@lem1007663 term606 (BIT1 0) term606). Qed.
Lemma lem5707678 : term617 = term608.
Proof. exact (EQ_MP (@lem5707677) (@lem5707676)). Qed.
Lemma lem5707679 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5707680 : term618 = term610.
Proof. exact (MK_COMB (@lem5707679) (@lem5707678)). Qed.
Lemma lem5707681 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5707682 : term615 = term599.
Proof. exact (MK_COMB (@lem5707681) (@lem5707680)). Qed.
Lemma lem5707683 : term614 = term599.
Proof. exact (TRANS (@lem5707675) (@lem5707682)). Qed.
Lemma lem5707684 : term613 = term599.
Proof. exact (TRANS (@lem5707672) (@lem5707683)). Qed.
Lemma lem5707686 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5707687 : term119 = term120.
Proof. exact (@lem5707686 term76 term76). Qed.
Lemma lem5707688 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5707689 : term122 = term76.
Proof. exact (EQ_MP (@lem5707688) (@lem940073)). Qed.
Lemma lem5707690 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5707691 : term120 = term75.
Proof. exact (MK_COMB (@lem5707690) (@lem5707689)). Qed.
Lemma lem5707692 : term119 = term75.
Proof. exact (TRANS (@lem5707687) (@lem5707691)). Qed.
Lemma lem5707693 : term612 = term612.
Proof. exact (eq_refl term612). Qed.
Lemma lem5707694 : term619 = term614.
Proof. exact (MK_COMB (@lem5707693) (@lem5707692)). Qed.
Lemma lem5707696 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5707697 : term614 = term615.
Proof. exact (@lem5707696 term608 term76). Qed.
Lemma lem5707698 : term616 = term606.
Proof. exact (@lem996237 term606). Qed.
Lemma lem5707699 : (term616 = term606) = (term617 = term608).
Proof. exact (@lem1007663 term606 (BIT1 0) term606). Qed.
Lemma lem5707700 : term617 = term608.
Proof. exact (EQ_MP (@lem5707699) (@lem5707698)). Qed.
Lemma lem5707701 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5707702 : term618 = term610.
Proof. exact (MK_COMB (@lem5707701) (@lem5707700)). Qed.
Lemma lem5707703 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5707704 : term615 = term599.
Proof. exact (MK_COMB (@lem5707703) (@lem5707702)). Qed.
Lemma lem5707705 : term614 = term599.
Proof. exact (TRANS (@lem5707697) (@lem5707704)). Qed.
Lemma lem5707706 : term619 = term599.
Proof. exact (TRANS (@lem5707694) (@lem5707705)). Qed.
Lemma lem5707707 : term599 = term619.
Proof. exact (SYM (@lem5707706)). Qed.
Lemma lem5707708 : term613 = term619.
Proof. exact (TRANS (@lem5707684) (@lem5707707)). Qed.
Lemma lem5707709 : term597 = term620.
Proof. exact (@lem5707635 (@lem5707708)). Qed.
Lemma lem5707710 : term596 = term620.
Proof. exact (TRANS (@lem5707601) (@lem5707709)). Qed.
Lemma lem5707712 (x : real) : (term128 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5707713 : term620 = term599.
Proof. exact (@lem5707712 term599). Qed.
Lemma lem5707714 : term596 = term599.
Proof. exact (TRANS (@lem5707710) (@lem5707713)). Qed.
Lemma lem5707715 (x : int) : (term595 x) = term621.
Proof. exact (MK_COMB (@lem5707592 x) (@lem5707714)). Qed.
Lemma lem5707716 (x : int) : (term594 x) = term621.
Proof. exact (TRANS (@lem5707484 x) (@lem5707715 x)). Qed.
Lemma lem5707717 : term621 = term599.
Proof. exact (@lem1982721 term599). Qed.
Lemma lem5707718 (x : int) : (term594 x) = term599.
Proof. exact (TRANS (@lem5707716 x) (@lem5707717)). Qed.
Lemma lem5707719 (r : int) (x : int) : (term592 r x) = term621.
Proof. exact (MK_COMB (@lem5707483 r) (@lem5707718 x)). Qed.
Lemma lem5707720 (r : int) (x : int) : (term591 r x) = term621.
Proof. exact (TRANS (@lem5707375 r x) (@lem5707719 r x)). Qed.
Lemma lem5707721 : term621 = term599.
Proof. exact (@lem1982721 term599). Qed.
Lemma lem5707722 (r : int) (x : int) : (term591 r x) = term599.
Proof. exact (TRANS (@lem5707720 r x) (@lem5707721)). Qed.
Lemma lem5707723 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5707724 (r : int) (x : int) : (term622 r x) = term623.
Proof. exact (MK_COMB (@lem5707723) (@lem5707722 r x)). Qed.
Lemma lem5707725 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem5707726 (r : int) (x : int) : (term590 r x) = term624.
Proof. exact (MK_COMB (@lem5707724 r x) (@lem5707725)). Qed.
Lemma lem5707727 (l : int) (r : int) (x : int) (h1 : term703 l r x) : term624.
Proof. exact (EQ_MP (@lem5707726 r x) (@lem5707374 l r x h1)). Qed.
Lemma lem5707729 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5707730 : term624 = term625.
Proof. exact (@lem5707729 term81 term599). Qed.
Lemma lem5707732 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5707733 : term599 = term620.
Proof. exact (@lem5707732 term608). Qed.
Lemma lem5707735 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5707736 : term81 = term162.
Proof. exact (@lem5707735 (NUMERAL 0)). Qed.
Lemma lem5707737 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5707738 : term236 = term237.
Proof. exact (MK_COMB (@lem5707737) (@lem5707736)). Qed.
Lemma lem5707739 : term625 = term626.
Proof. exact (MK_COMB (@lem5707738) (@lem5707733)). Qed.
Lemma lem5707740 : term627.
Proof. exact (@lem1980026 term81 term75 term599 term75). Qed.
Lemma lem5707742 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5707743 : term161 = term168.
Proof. exact (@lem5707742 (NUMERAL 0) term76). Qed.
Lemma lem5707744 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5707745 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5707746 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5707745 h1) (fun h1 : term168 = True => @lem5707744)). Qed.
Lemma lem5707747 : term168 = True.
Proof. exact (EQ_MP (@lem5707746) (@lem5707744)). Qed.
Lemma lem5707748 : term161 = True.
Proof. exact (TRANS (@lem5707743) (@lem5707747)). Qed.
Lemma lem5707749 : True = term161.
Proof. exact (SYM (@lem5707748)). Qed.
Lemma lem5707750 : term161.
Proof. exact (EQ_MP (@lem5707749) (@lem0)). Qed.
Lemma lem5707751 : term628.
Proof. exact (@lem5707740 (@lem5707750)). Qed.
Lemma lem5707753 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5707754 : term161 = term168.
Proof. exact (@lem5707753 (NUMERAL 0) term76). Qed.
Lemma lem5707755 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5707756 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5707757 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5707756 h1) (fun h1 : term168 = True => @lem5707755)). Qed.
Lemma lem5707758 : term168 = True.
Proof. exact (EQ_MP (@lem5707757) (@lem5707755)). Qed.
Lemma lem5707759 : term161 = True.
Proof. exact (TRANS (@lem5707754) (@lem5707758)). Qed.
Lemma lem5707760 : True = term161.
Proof. exact (SYM (@lem5707759)). Qed.
Lemma lem5707761 : term161.
Proof. exact (EQ_MP (@lem5707760) (@lem0)). Qed.
Lemma lem5707762 : term626 = term629.
Proof. exact (@lem5707751 (@lem5707761)). Qed.
Lemma lem5707764 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5707765 : term614 = term615.
Proof. exact (@lem5707764 term608 term76). Qed.
Lemma lem5707766 : term616 = term606.
Proof. exact (@lem996237 term606). Qed.
Lemma lem5707767 : (term616 = term606) = (term617 = term608).
Proof. exact (@lem1007663 term606 (BIT1 0) term606). Qed.
Lemma lem5707768 : term617 = term608.
Proof. exact (EQ_MP (@lem5707767) (@lem5707766)). Qed.
Lemma lem5707769 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5707770 : term618 = term610.
Proof. exact (MK_COMB (@lem5707769) (@lem5707768)). Qed.
Lemma lem5707771 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5707772 : term615 = term599.
Proof. exact (MK_COMB (@lem5707771) (@lem5707770)). Qed.
Lemma lem5707773 : term614 = term599.
Proof. exact (TRANS (@lem5707765) (@lem5707772)). Qed.
Lemma lem5707775 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5707776 : term173 = term81.
Proof. exact (@lem5707775 term76). Qed.
Lemma lem5707777 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5707778 : term242 = term236.
Proof. exact (MK_COMB (@lem5707777) (@lem5707776)). Qed.
Lemma lem5707779 : term629 = term625.
Proof. exact (MK_COMB (@lem5707778) (@lem5707773)). Qed.
Lemma lem5707781 (m : nat) (n : nat) : (term243 m n) = (term244 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5707782 : term625 = term630.
Proof. exact (@lem5707781 (NUMERAL 0) term608). Qed.
Lemma lem5707783 : term631 = term606.
Proof. exact (@lem912803). Qed.
Lemma lem5707784 (h1 : term631 = term606) : (term608 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term606 h1). Qed.
Lemma lem5707785 : (term631 = term606) = ((term608 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term631 = term606 => @lem5707784 h1) (fun h1 : (term608 = (NUMERAL 0)) = False => @lem5707783)). Qed.
Lemma lem5707786 : (term608 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5707785) (@lem5707783)). Qed.
Lemma lem5707787 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5707788 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5707789 : term246 = (and True).
Proof. exact (MK_COMB (@lem5707788) (@lem5707787)). Qed.
Lemma lem5707790 : term630 = (True /\ False).
Proof. exact (MK_COMB (@lem5707789) (@lem5707786)). Qed.
Lemma lem5707792 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5707793 : term630 = False.
Proof. exact (TRANS (@lem5707790) (@lem5707792)). Qed.
Lemma lem5707794 : term625 = False.
Proof. exact (TRANS (@lem5707782) (@lem5707793)). Qed.
Lemma lem5707795 : term629 = False.
Proof. exact (TRANS (@lem5707779) (@lem5707794)). Qed.
Lemma lem5707796 : term626 = False.
Proof. exact (TRANS (@lem5707762) (@lem5707795)). Qed.
Lemma lem5707797 : term625 = False.
Proof. exact (TRANS (@lem5707739) (@lem5707796)). Qed.
Lemma lem5707798 : term624 = False.
Proof. exact (TRANS (@lem5707730) (@lem5707797)). Qed.
Lemma lem5707799 (l : int) (r : int) (x : int) (h1 : term703 l r x) : False.
Proof. exact (EQ_MP (@lem5707798) (@lem5707727 l r x h1)). Qed.
Lemma lem5707800 (l : int) (r : int) (x : int) (h1 : term699 l r x) : False.
Proof. exact (or_elim (@lem5706633 l r x h1) (fun h0 : term702 r l x => @lem5707216 r l x h0) (fun h0 : term703 l r x => @lem5707799 l r x h0)). Qed.
Lemma lem5707802 (l : int) (r : int) (x : int) (h1 : term699 l r x) : term699 l r x.
Proof. exact (h1). Qed.
Lemma lem5707803 (l : int) (r : int) (x : int) (h1 : term699 l r x) : (term699 l r x) = False.
Proof. exact (prop_ext (fun h2 : term699 l r x => @lem5707800 l r x h1) (fun h2 : False => @lem5707802 l r x h1)). Qed.
Lemma lem5707804 (l : int) (r : int) (x : int) (h1 : term699 l r x) : False.
Proof. exact (EQ_MP (@lem5707803 l r x h1) (@lem5707802 l r x h1)). Qed.
Lemma lem5707805 (l : int) (r : int) (h1 : term701 l r) : term701 l r.
Proof. exact (h1). Qed.
Lemma lem5707806 (l : int) (r : int) (h1 : term701 l r) : False.
Proof. exact (ex_elim (@lem5707805 l r h1) (fun x : int => fun h0 : term700 l r x => @lem5707804 l r x h0)). Qed.
Lemma lem5707807 (l : int) (r : int) (h1 : term693 l r) : term693 l r.
Proof. exact (h1). Qed.
Lemma lem5707808 (l : int) (r : int) (h1 : term693 l r) : term701 l r.
Proof. exact (EQ_MP (@lem5706623 l r) (@lem5707807 l r h1)). Qed.
Lemma lem5707809 (l : int) (r : int) (h1 : term693 l r) : (term701 l r) = False.
Proof. exact (prop_ext (fun h2 : term701 l r => @lem5707806 l r h2) (fun h2 : False => @lem5707808 l r h1)). Qed.
Lemma lem5707810 (l : int) (r : int) (h1 : term693 l r) : False.
Proof. exact (EQ_MP (@lem5707809 l r h1) (@lem5707808 l r h1)). Qed.
Lemma lem5707811 (l : int) (r : int) : term704 l r.
Proof. exact (fun h0 : term693 l r => @lem5707810 l r h0). Qed.
Lemma lem5707812 (l : int) (r : int) : term705 l r.
Proof. exact (@lem1386578 (term706 l r)). Qed.
Lemma lem5707815 (l : int) (r : int) : term706 l r.
Proof. exact (@lem5707812 l r (@lem5707811 l r)). Qed.
Lemma lem5707816 (l : int) (r : int) : (term692 l r) = (term681 l r).
Proof. exact (SYM (@lem5706159 l r)). Qed.
Lemma lem5707817 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5707818 (l : int) (r : int) : (term706 l r) = (term676 l r).
Proof. exact (MK_COMB (@lem5707817) (@lem5707816 l r)). Qed.
Lemma lem5707819 (l : int) (r : int) : term676 l r.
Proof. exact (EQ_MP (@lem5707818 l r) (@lem5707815 l r)). Qed.
Lemma lem5707820 (l : int) (r : int) : term524 l r.
Proof. exact (EQ_MP (@lem5705981 l r) (@lem5707819 l r)). Qed.
Lemma lem5707821 (l : int) (r : int) : (term524 l r) = ((term524 l r) = True).
Proof. exact (@lem7 (term524 l r)). Qed.
Lemma lem5707822 (l : int) (r : int) : (term524 l r) = True.
Proof. exact (EQ_MP (@lem5707821 l r) (@lem5707820 l r)). Qed.
Lemma lem5707823 (l : int) (r : int) : True = (term524 l r).
Proof. exact (SYM (@lem5707822 l r)). Qed.
Lemma lem5707824 (l : int) (r : int) : term524 l r.
Proof. exact (EQ_MP (@lem5707823 l r) (@lem0)). Qed.
Lemma lem5707825 (l : int) (r : int) : term498 l r.
Proof. exact (EQ_MP (@lem5702668 l r) (@lem5707824 l r)). Qed.
Lemma lem5707826 (l : int) (r : int) : term471 l r.
Proof. exact (EQ_MP (@lem5702596 l r) (@lem5705980 l r)). Qed.
Lemma lem5707827 (l : int) (r : int) : term426 l r.
Proof. exact (EQ_MP (@lem5702524 l r) (@lem5704322 l r)). Qed.
Lemma lem5707828 (l : int) (r : int) : term406 l r.
Proof. exact (@lem5702452 l r (@lem5707825 l r)). Qed.
Lemma lem5707829 (l : int) (r : int) : term372 l r.
Proof. exact (@lem5702448 l r (@lem5707826 l r)). Qed.
Lemma lem5707830 (l : int) (r : int) : term335 l r.
Proof. exact (@lem5702444 l r (@lem5707827 l r)). Qed.
Lemma lem5707835 (l : int) : term410 l.
Proof. exact (fun r : int => @lem5707828 l r). Qed.
Lemma lem5707836 (l : int) : term388 l.
Proof. exact (@lem5702438 l (@lem5707835 l)). Qed.
Lemma lem5707841 : term392.
Proof. exact (fun l : int => @lem5707836 l). Qed.
Lemma lem5707842 : term399.
Proof. exact (@lem5702411 (@lem5707841)). Qed.
Lemma lem5707847 (l : int) : term376 l.
Proof. exact (fun r : int => @lem5707829 l r). Qed.
Lemma lem5707848 (l : int) : term354 l.
Proof. exact (@lem5702382 l (@lem5707847 l)). Qed.
Lemma lem5707853 : term358.
Proof. exact (fun l : int => @lem5707848 l). Qed.
Lemma lem5707854 : term365.
Proof. exact (@lem5702355 (@lem5707853)). Qed.
Lemma lem5707859 (l : int) : term339 l.
Proof. exact (fun r : int => @lem5707830 l r). Qed.
Lemma lem5707860 (l : int) : term308 l.
Proof. exact (@lem5702326 l (@lem5707859 l)). Qed.
Lemma lem5707865 : term312.
Proof. exact (fun l : int => @lem5707860 l). Qed.
Lemma lem5707866 : term323.
Proof. exact (@lem5702299 (@lem5707865)). Qed.
Lemma lem5707867 (h1 : term295) : term397.
Proof. exact (@lem5707842 (@lem5702272 h1)). Qed.
Lemma lem5707868 (h1 : term295) : term363.
Proof. exact (@lem5707854 (@lem5702272 h1)). Qed.
Lemma lem5707869 (h1 : term295) : term321.
Proof. exact (@lem5707866 (@lem5702272 h1)). Qed.
Lemma lem5707870 (h1 : term295) : term707.
Proof. exact (conj (@lem5707868 h1) (@lem5707867 h1)). Qed.
Lemma lem5707871 (h1 : term295) : term296.
Proof. exact (conj (@lem5707869 h1) (@lem5707870 h1)). Qed.
Lemma lem5707872 : term708.
Proof. exact (fun h0 : term295 => @lem5707871 h0). Qed.
Lemma lem5707902 (r : int) (l : int) (h1 : term55 r l) : term55 r l.
Proof. exact (h1). Qed.
Lemma lem5707903 (x : int) (r : int) (l : int) (h1 : term55 r l) : term56 l x r.
Proof. exact (@lem5702054 l x r (@lem5707902 r l h1)). Qed.
Lemma lem5707904 (l : int) (x : int) (r : int) : term709 l x r.
Proof. exact (@lem82 (term50 l x r)). Qed.
Lemma lem5707905 (x : int) (r : int) (l : int) (h1 : term55 r l) : (term50 l x r) = False.
Proof. exact (@lem5707904 l x r (@lem5707903 x r l h1)). Qed.
Lemma lem5707911 (r : int) (l : int) : term710 r l.
Proof. exact (@lem82 (term251 r l)). Qed.
Lemma lem5707918 (l : int) (x : int) (r : int) : term711 l x r.
Proof. exact (fun h0 : term55 r l => @lem5707905 x r l h0). Qed.
Lemma lem5707920 (r : int) (l : int) (h1 : term55 r l) : (term251 r l) = False.
Proof. exact (@lem5707911 r l (@lem5702059 r l h1)). Qed.
Lemma lem5707921 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5707922 (r : int) (l : int) (h1 : term55 r l) : (term55 r l) = (~ False).
Proof. exact (MK_COMB (@lem5707921) (@lem5707920 r l h1)). Qed.
Lemma lem5707924 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem5707925 (r : int) (l : int) (h1 : term55 r l) : (term55 r l) = True.
Proof. exact (TRANS (@lem5707922 r l h1) (@lem5707924)). Qed.
Lemma lem5707926 (r : int) (l : int) (h1 : term55 r l) : True = (term55 r l).
Proof. exact (SYM (@lem5707925 r l h1)). Qed.
Lemma lem5707927 (r : int) (l : int) (h1 : term55 r l) : term55 r l.
Proof. exact (EQ_MP (@lem5707926 r l h1) (@lem0)). Qed.
Lemma lem5707928 (x : int) (r : int) (l : int) (h1 : term55 r l) : (term50 l x r) = False.
Proof. exact (@lem5707918 l x r (@lem5707927 r l h1)). Qed.
Lemma lem5707929 (GEN_PVAR_233 : int) : (@SETSPEC int GEN_PVAR_233) = (@SETSPEC int GEN_PVAR_233).
Proof. exact (eq_refl (@SETSPEC int GEN_PVAR_233)). Qed.
Lemma lem5707930 (x : int) (GEN_PVAR_233 : int) (r : int) (l : int) (h1 : term55 r l) : (term453 GEN_PVAR_233 l x r) = (@SETSPEC int GEN_PVAR_233 False).
Proof. exact (MK_COMB (@lem5707929 GEN_PVAR_233) (@lem5707928 x r l h1)). Qed.
Lemma lem5707931 (x : int) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5707932 (GEN_PVAR_233 : int) (x : int) (r : int) (l : int) (h1 : term55 r l) : (term455 GEN_PVAR_233 l r x) = (@SETSPEC int GEN_PVAR_233 False x).
Proof. exact (MK_COMB (@lem5707930 x GEN_PVAR_233 r l h1) (@lem5707931 x)). Qed.
Lemma lem5707933 (GEN_PVAR_233 : int) (r : int) (l : int) (h1 : term55 r l) : (term457 GEN_PVAR_233 l r) = (term712 GEN_PVAR_233).
Proof. exact (fun_ext (fun x : int => @lem5707932 GEN_PVAR_233 x r l h1)). Qed.
Lemma lem5707934 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem5707935 (GEN_PVAR_233 : int) (r : int) (l : int) (h1 : term55 r l) : (term459 GEN_PVAR_233 l r) = (term713 GEN_PVAR_233).
Proof. exact (MK_COMB (@lem5707934) (@lem5707933 GEN_PVAR_233 r l h1)). Qed.
Lemma lem5707940 (r : int) (l : int) (h1 : term55 r l) : (term461 l r) = term714.
Proof. exact (fun_ext (fun GEN_PVAR_233 : int => @lem5707935 GEN_PVAR_233 r l h1)). Qed.
Lemma lem5707945 : (@GSPEC int) = (@GSPEC int).
Proof. exact (eq_refl (@GSPEC int)). Qed.
Lemma lem5707946 (r : int) (l : int) (h1 : term55 r l) : (term419 l r) = term715.
Proof. exact (MK_COMB (@lem5707945) (@lem5707940 r l h1)). Qed.
Lemma lem5707951 : (@FINITE int) = (@FINITE int).
Proof. exact (eq_refl (@FINITE int)). Qed.
Lemma lem5707952 (r : int) (l : int) (h1 : term55 r l) : (term329 l r) = term716.
Proof. exact (MK_COMB (@lem5707951) (@lem5707946 r l h1)). Qed.
Lemma lem5707957 (r : int) (l : int) (h1 : term55 r l) : term716 = (term329 l r).
Proof. exact (SYM (@lem5707952 r l h1)). Qed.
Lemma lem5707970 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = ((@FINITE _92140 (@EMPTY _92140)) = True).
Proof. exact (@lem7 (@FINITE _92140 (@EMPTY _92140))). Qed.
Lemma lem5707975 {_88295 : Type'} : (term717 _88295) = (@EMPTY _88295).
Proof. exact (EQ_MP (@lem3399706 _88295) (@lem3399757 _88295)). Qed.
Lemma lem5707976 : term715 = (@EMPTY int).
Proof. exact (@lem5707975 int). Qed.
Lemma lem5707977 : (@FINITE int) = (@FINITE int).
Proof. exact (eq_refl (@FINITE int)). Qed.
Lemma lem5707978 : term716 = (@FINITE int (@EMPTY int)).
Proof. exact (MK_COMB (@lem5707977) (@lem5707976)). Qed.
Lemma lem5707980 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = True.
Proof. exact (EQ_MP (@lem5707970 _92140) (@lem3596285 _92140)). Qed.
Lemma lem5707981 : (@FINITE int (@EMPTY int)) = True.
Proof. exact (@lem5707980 int). Qed.
Lemma lem5707982 : term716 = True.
Proof. exact (TRANS (@lem5707978) (@lem5707981)). Qed.
Lemma lem5707983 : True = term716.
Proof. exact (SYM (@lem5707982)). Qed.
Lemma lem5707984 : term716.
Proof. exact (EQ_MP (@lem5707983) (@lem0)). Qed.
Lemma lem5707986 {A : Type'} (s : A -> Prop) : term43 A s.
Proof. exact (EQ_MP (@lem5700976 A s) (@lem5700975 A s)). Qed.
Lemma lem5707987 (s : int -> Prop) : term718 s.
Proof. exact (@lem5707986 int s). Qed.
Lemma lem5707988 (l : int) (r : int) : term719 l r.
Proof. exact (@lem5707987 (term419 l r)). Qed.
Lemma lem5707989 (m : nat) : term720 m.
Proof. exact (@lem5329299 m). Qed.
Lemma lem5707990 (m : nat) : (term720 m) = (term721 m).
Proof. exact (eq_refl (term720 m)). Qed.
Lemma lem5707991 (m : nat) : term721 m.
Proof. exact (EQ_MP (@lem5707990 m) (@lem5707989 m)). Qed.
Lemma lem5707992 (m : nat) (n : nat) : term722 m n.
Proof. exact (@lem5707991 m n). Qed.
Lemma lem5707993 (m : nat) (n : nat) : (term722 m n) = (term723 m n).
Proof. exact (eq_refl (term722 m n)). Qed.
Lemma lem5707994 (m : nat) (n : nat) : term723 m n.
Proof. exact (EQ_MP (@lem5707993 m n) (@lem5707992 m n)). Qed.
Lemma lem5707995 (m : nat) (n : nat) : (term723 m n) = ((term723 m n) = True).
Proof. exact (@lem7 (term723 m n)). Qed.
Lemma lem5707997 {A B : Type'} (f : A -> B) : term724 A B f.
Proof. exact (@lem3615104 A B f). Qed.
Lemma lem5707998 {A B : Type'} (f : A -> B) : (term724 A B f) = (term725 A B f).
Proof. exact (eq_refl (term724 A B f)). Qed.
Lemma lem5707999 {A B : Type'} (f : A -> B) : term725 A B f.
Proof. exact (EQ_MP (@lem5707998 A B f) (@lem5707997 A B f)). Qed.
Lemma lem5708000 {A B : Type'} (f : A -> B) (s : A -> Prop) : term726 A B f s.
Proof. exact (@lem5707999 A B f s). Qed.
Lemma lem5708001 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term726 A B f s) = (term727 A B f s).
Proof. exact (eq_refl (term726 A B f s)). Qed.
Lemma lem5708002 {A B : Type'} (f : A -> B) (s : A -> Prop) : term727 A B f s.
Proof. exact (EQ_MP (@lem5708001 A B f s) (@lem5708000 A B f s)). Qed.
Lemma lem5708003 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem5708004 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : term728 A B f s.
Proof. exact (@lem5708002 A B f s (@lem5708003 A s h1)). Qed.
Lemma lem5708005 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term728 A B f s) = ((term728 A B f s) = True).
Proof. exact (@lem7 (term728 A B f s)). Qed.
Lemma lem5708006 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : (term728 A B f s) = True.
Proof. exact (EQ_MP (@lem5708005 A B f s) (@lem5708004 A B f s h1)). Qed.
Lemma lem5708017 {A B : Type'} (f : A -> B) (s : A -> Prop) : term729 A B f s.
Proof. exact (fun h0 : @FINITE A s => @lem5708006 A B f s h0). Qed.
Lemma lem5708018 (f : nat -> int) (s : nat -> Prop) : term730 f s.
Proof. exact (@lem5708017 nat int f s). Qed.
Lemma lem5708019 (r : int) (l : int) : term731 r l.
Proof. exact (@lem5708018 (term732 l) (term733 r l)). Qed.
Lemma lem5708021 (m : nat) (n : nat) : (term723 m n) = True.
Proof. exact (EQ_MP (@lem5707995 m n) (@lem5707994 m n)). Qed.
Lemma lem5708022 (r : int) (l : int) : (term734 r l) = True.
Proof. exact (@lem5708021 (NUMERAL 0) (term735 r l)). Qed.
Lemma lem5708023 (r : int) (l : int) : True = (term734 r l).
Proof. exact (SYM (@lem5708022 r l)). Qed.
Lemma lem5708024 (r : int) (l : int) : term734 r l.
Proof. exact (EQ_MP (@lem5708023 r l) (@lem0)). Qed.
Lemma lem5708025 (r : int) (l : int) : (term736 r l) = True.
Proof. exact (@lem5708019 r l (@lem5708024 r l)). Qed.
Lemma lem5708026 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5708027 (r : int) (l : int) : (term737 r l) = (and True).
Proof. exact (MK_COMB (@lem5708026) (@lem5708025 r l)). Qed.
Lemma lem5708034 (r : int) (l : int) : (term738 r l) = (term738 r l).
Proof. exact (eq_refl (term738 r l)). Qed.
Lemma lem5708035 (r : int) (l : int) : (term739 r l) = (term740 r l).
Proof. exact (MK_COMB (@lem5708027 r l) (@lem5708034 r l)). Qed.
Lemma lem5708037 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5708038 (r : int) (l : int) : (term740 r l) = (term738 r l).
Proof. exact (@lem5708037 (term738 r l)). Qed.
Lemma lem5708045 (r : int) (l : int) : (term739 r l) = (term738 r l).
Proof. exact (TRANS (@lem5708035 r l) (@lem5708038 r l)). Qed.
Lemma lem5708046 (r : int) (l : int) : (term738 r l) = (term739 r l).
Proof. exact (SYM (@lem5708045 r l)). Qed.
Lemma lem5708048 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term33 A s t).
Proof. exact (EQ_MP (@lem5700955 A s t) (@lem5700954 A s t)). Qed.
Lemma lem5708049 (s : int -> Prop) (t : int -> Prop) : (@SUBSET int s t) = (term425 s t).
Proof. exact (@lem5708048 int s t). Qed.
Lemma lem5708050 (r : int) (l : int) : (term738 r l) = (term741 r l).
Proof. exact (@lem5708049 (term419 l r) (term742 r l)). Qed.
Lemma lem5708058 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term22 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem5700933 _83095 p x) (@lem5700932 _83095 p x)). Qed.
Lemma lem5708059 (p : int -> Prop) (x : int) : (term428 x p) = (p x).
Proof. exact (@lem5708058 int p x). Qed.
Lemma lem5708060 (l : int) (r : int) (x : int) : (term449 x l r) = (term450 l r x).
Proof. exact (@lem5708059 (term451 l r) x). Qed.
Lemma lem5708061 (l : int) (x : int) (r : int) : (term450 l r x) = (term50 l x r).
Proof. exact (eq_refl (term450 l r x)). Qed.
Lemma lem5708062 (GEN_PVAR_233 : int) : (@SETSPEC int GEN_PVAR_233) = (@SETSPEC int GEN_PVAR_233).
Proof. exact (eq_refl (@SETSPEC int GEN_PVAR_233)). Qed.
Lemma lem5708063 (GEN_PVAR_233 : int) (l : int) (x : int) (r : int) : (term452 GEN_PVAR_233 l r x) = (term453 GEN_PVAR_233 l x r).
Proof. exact (MK_COMB (@lem5708062 GEN_PVAR_233) (@lem5708061 l x r)). Qed.
Lemma lem5708064 (x : int) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5708065 (GEN_PVAR_233 : int) (l : int) (r : int) (x : int) : (term454 GEN_PVAR_233 l r x) = (term455 GEN_PVAR_233 l r x).
Proof. exact (MK_COMB (@lem5708063 GEN_PVAR_233 l x r) (@lem5708064 x)). Qed.
Lemma lem5708066 (GEN_PVAR_233 : int) (l : int) (r : int) : (term456 GEN_PVAR_233 l r) = (term457 GEN_PVAR_233 l r).
Proof. exact (fun_ext (fun x : int => @lem5708065 GEN_PVAR_233 l r x)). Qed.
Lemma lem5708067 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem5708068 (GEN_PVAR_233 : int) (l : int) (r : int) : (term458 GEN_PVAR_233 l r) = (term459 GEN_PVAR_233 l r).
Proof. exact (MK_COMB (@lem5708067) (@lem5708066 GEN_PVAR_233 l r)). Qed.
Lemma lem5708069 (l : int) (r : int) : (term460 l r) = (term461 l r).
Proof. exact (fun_ext (fun GEN_PVAR_233 : int => @lem5708068 GEN_PVAR_233 l r)). Qed.
Lemma lem5708070 : (@GSPEC int) = (@GSPEC int).
Proof. exact (eq_refl (@GSPEC int)). Qed.
Lemma lem5708071 (l : int) (r : int) : (term462 l r) = (term419 l r).
Proof. exact (MK_COMB (@lem5708070) (@lem5708069 l r)). Qed.
Lemma lem5708072 (x : int) : (@IN int x) = (@IN int x).
Proof. exact (eq_refl (@IN int x)). Qed.
Lemma lem5708073 (x : int) (l : int) (r : int) : (term449 x l r) = (term463 x l r).
Proof. exact (MK_COMB (@lem5708072 x) (@lem5708071 l r)). Qed.
Lemma lem5708074 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5708075 (x : int) (l : int) (r : int) : (term464 x l r) = (term465 x l r).
Proof. exact (MK_COMB (@lem5708074) (@lem5708073 x l r)). Qed.
Lemma lem5708076 (l : int) (x : int) (r : int) : (term450 l r x) = (term50 l x r).
Proof. exact (eq_refl (term450 l r x)). Qed.
Lemma lem5708077 (l : int) (x : int) (r : int) : ((term449 x l r) = (term450 l r x)) = ((term463 x l r) = (term50 l x r)).
Proof. exact (MK_COMB (@lem5708075 x l r) (@lem5708076 l x r)). Qed.
Lemma lem5708078 (l : int) (x : int) (r : int) : (term463 x l r) = (term50 l x r).
Proof. exact (EQ_MP (@lem5708077 l x r) (@lem5708060 l r x)). Qed.
Lemma lem5708081 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5708082 (l : int) (x : int) (r : int) : (term743 x l r) = (term744 l x r).
Proof. exact (MK_COMB (@lem5708081) (@lem5708078 l x r)). Qed.
Lemma lem5708084 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term28 A B y f s) = (term29 A B y f s).
Proof. exact (EQ_MP (@lem5700949 A B y f s) (@lem5700948 A B y s f)). Qed.
Lemma lem5708085 (y : int) (f : nat -> int) (s : nat -> Prop) : (term745 y f s) = (term746 y f s).
Proof. exact (@lem5708084 nat int y f s). Qed.
Lemma lem5708086 (x : int) (r : int) (l : int) : (term747 x r l) = (term748 x r l).
Proof. exact (@lem5708085 x (term732 l) (term733 r l)). Qed.
Lemma lem5708096 {A B : Type'} (f : A -> B) (y : A) : (term749 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem5708097 (f : nat -> int) (y : nat) : (term750 f y) = (f y).
Proof. exact (@lem5708096 nat int f y). Qed.
Lemma lem5708098 (l : int) (x : nat) : (term751 l x) = (term752 l x).
Proof. exact (@lem5708097 (term732 l) x). Qed.
Lemma lem5708099 (l : int) (n : nat) : (term752 l n) = (term753 l n).
Proof. exact (eq_refl (term752 l n)). Qed.
Lemma lem5708100 (l : int) : (term754 l) = (term732 l).
Proof. exact (fun_ext (fun n : nat => @lem5708099 l n)). Qed.
Lemma lem5708101 (x : nat) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5708102 (l : int) (x : nat) : (term751 l x) = (term752 l x).
Proof. exact (MK_COMB (@lem5708100 l) (@lem5708101 x)). Qed.
Lemma lem5708103 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem5708104 (l : int) (x : nat) : (term755 l x) = (term756 l x).
Proof. exact (MK_COMB (@lem5708103) (@lem5708102 l x)). Qed.
Lemma lem5708105 (l : int) (x : nat) : (term752 l x) = (term753 l x).
Proof. exact (eq_refl (term752 l x)). Qed.
Lemma lem5708106 (l : int) (x : nat) : ((term751 l x) = (term752 l x)) = ((term752 l x) = (term753 l x)).
Proof. exact (MK_COMB (@lem5708104 l x) (@lem5708105 l x)). Qed.
Lemma lem5708107 (l : int) (x : nat) : (term752 l x) = (term753 l x).
Proof. exact (EQ_MP (@lem5708106 l x) (@lem5708098 l x)). Qed.
Lemma lem5708108 (x : int) : (@eq int x) = (@eq int x).
Proof. exact (eq_refl (@eq int x)). Qed.
Lemma lem5708109 (x : int) (l : int) (x' : nat) : (x = (term752 l x')) = (x = (term753 l x')).
Proof. exact (MK_COMB (@lem5708108 x) (@lem5708107 l x')). Qed.
Lemma lem5708112 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5708113 (x : int) (l : int) (x' : nat) : (term757 x l x') = (term758 x l x').
Proof. exact (MK_COMB (@lem5708112) (@lem5708109 x l x')). Qed.
Lemma lem5708114 (x : nat) (r : int) (l : int) : (term759 x r l) = (term759 x r l).
Proof. exact (eq_refl (term759 x r l)). Qed.
Lemma lem5708115 (x : int) (x' : nat) (r : int) (l : int) : (term760 x x' r l) = (term761 x x' r l).
Proof. exact (MK_COMB (@lem5708113 x l x') (@lem5708114 x' r l)). Qed.
Lemma lem5708118 (x : int) (r : int) (l : int) : (term762 x r l) = (term763 x r l).
Proof. exact (fun_ext (fun x' : nat => @lem5708115 x x' r l)). Qed.
Lemma lem5708119 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5708120 (x : int) (r : int) (l : int) : (term748 x r l) = (term764 x r l).
Proof. exact (MK_COMB (@lem5708119) (@lem5708118 x r l)). Qed.
Lemma lem5708125 (x : int) (r : int) (l : int) : (term747 x r l) = (term764 x r l).
Proof. exact (TRANS (@lem5708086 x r l) (@lem5708120 x r l)). Qed.
Lemma lem5708126 (x : int) (r : int) (l : int) : (term765 x r l) = (term766 x r l).
Proof. exact (MK_COMB (@lem5708082 l x r) (@lem5708125 x r l)). Qed.
Lemma lem5708129 (r : int) (l : int) : (term767 r l) = (term768 r l).
Proof. exact (fun_ext (fun x : int => @lem5708126 x r l)). Qed.
Lemma lem5708130 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem5708131 (r : int) (l : int) : (term741 r l) = (term769 r l).
Proof. exact (MK_COMB (@lem5708130) (@lem5708129 r l)). Qed.
Lemma lem5708136 (r : int) (l : int) : (term738 r l) = (term769 r l).
Proof. exact (TRANS (@lem5708050 r l) (@lem5708131 r l)). Qed.
Lemma lem5708137 (r : int) (l : int) : (term769 r l) = (term738 r l).
Proof. exact (SYM (@lem5708136 r l)). Qed.
Lemma lem5708155 (m : nat) (p : nat) (n : nat) : (term14 p m n) = (term15 m p n).
Proof. exact (EQ_MP (@lem5700896 m p n) (@lem5700895 m n p)). Qed.
Lemma lem5708156 (x : nat) (r : int) (l : int) : (term759 x r l) = (term770 x r l).
Proof. exact (@lem5708155 (NUMERAL 0) x (term735 r l)). Qed.
Lemma lem5708160 (m : nat) (n : nat) : (Peano.le m n) = (term0 m n).
Proof. exact (EQ_MP (@lem5700902 m n) (@lem5700901 m n)). Qed.
Lemma lem5708161 (x : nat) : (term771 x) = (term772 x).
Proof. exact (@lem5708160 (NUMERAL 0) x). Qed.
Lemma lem5708162 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5708163 (x : nat) : (term773 x) = (term774 x).
Proof. exact (MK_COMB (@lem5708162) (@lem5708161 x)). Qed.
Lemma lem5708165 (m : nat) (n : nat) : (Peano.le m n) = (term0 m n).
Proof. exact (EQ_MP (@lem5700902 m n) (@lem5700901 m n)). Qed.
Lemma lem5708166 (x : nat) (r : int) (l : int) : (term775 x r l) = (term776 x r l).
Proof. exact (@lem5708165 x (term735 r l)). Qed.
Lemma lem5708167 (x : nat) (r : int) (l : int) : (term770 x r l) = (term777 x r l).
Proof. exact (MK_COMB (@lem5708163 x) (@lem5708166 x r l)). Qed.
Lemma lem5708170 (x : nat) (r : int) (l : int) : (term759 x r l) = (term777 x r l).
Proof. exact (TRANS (@lem5708156 x r l) (@lem5708167 x r l)). Qed.
Lemma lem5708171 (x : int) (l : int) (x' : nat) : (term758 x l x') = (term758 x l x').
Proof. exact (eq_refl (term758 x l x')). Qed.
Lemma lem5708172 (x : int) (x' : nat) (r : int) (l : int) : (term761 x x' r l) = (term778 x x' r l).
Proof. exact (MK_COMB (@lem5708171 x l x') (@lem5708170 x' r l)). Qed.
Lemma lem5708175 (x : int) (r : int) (l : int) : (term763 x r l) = (term779 x r l).
Proof. exact (fun_ext (fun x' : nat => @lem5708172 x x' r l)). Qed.
Lemma lem5708176 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5708177 (x : int) (r : int) (l : int) : (term764 x r l) = (term780 x r l).
Proof. exact (MK_COMB (@lem5708176) (@lem5708175 x r l)). Qed.
Lemma lem5708182 (l : int) (x : int) (r : int) : (term744 l x r) = (term744 l x r).
Proof. exact (eq_refl (term744 l x r)). Qed.
Lemma lem5708183 (x : int) (r : int) (l : int) : (term766 x r l) = (term781 x r l).
Proof. exact (MK_COMB (@lem5708182 l x r) (@lem5708177 x r l)). Qed.
Lemma lem5708186 (r : int) (l : int) : (term768 r l) = (term782 r l).
Proof. exact (fun_ext (fun x : int => @lem5708183 x r l)). Qed.
Lemma lem5708187 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem5708188 (r : int) (l : int) : (term769 r l) = (term783 r l).
Proof. exact (MK_COMB (@lem5708187) (@lem5708186 r l)). Qed.
Lemma lem5708193 (r : int) (l : int) : (term783 r l) = (term769 r l).
Proof. exact (SYM (@lem5708188 r l)). Qed.
Lemma lem5708194 (l : int) (x : int) (r : int) (h1 : term50 l x r) : term50 l x r.
Proof. exact (h1). Qed.
Lemma lem5708195 (x : int) (r : int) (h1 : int_le x r) : int_le x r.
Proof. exact (h1). Qed.
Lemma lem5708196 (l : int) (x : int) (h1 : int_le l x) : int_le l x.
Proof. exact (h1). Qed.
Lemma lem5708197 (x : int) : term784 x.
Proof. exact (@lem2310219 x). Qed.
Lemma lem5708198 (x : int) : (term784 x) = (term785 x).
Proof. exact (eq_refl (term784 x)). Qed.
Lemma lem5708199 (x : int) : term785 x.
Proof. exact (EQ_MP (@lem5708198 x) (@lem5708197 x)). Qed.
Lemma lem5708200 (x : int) (y : int) : term786 x y.
Proof. exact (@lem5708199 x y). Qed.
Lemma lem5708201 (y : int) (x : int) : (term786 x y) = ((term251 x y) = (int_le y x)).
Proof. exact (eq_refl (term786 x y)). Qed.
Lemma lem5708203 (x : int) : term787 x.
Proof. exact (@lem2834258 x). Qed.
Lemma lem5708204 (x : int) : (term787 x) = (term788 x).
Proof. exact (eq_refl (term787 x)). Qed.
Lemma lem5708205 (x : int) : term788 x.
Proof. exact (EQ_MP (@lem5708204 x) (@lem5708203 x)). Qed.
Lemma lem5708206 (x : int) (h1 : term789 x) : term789 x.
Proof. exact (h1). Qed.
Lemma lem5708207 (x : int) (h1 : term789 x) : (term790 x) = x.
Proof. exact (@lem5708205 x (@lem5708206 x h1)). Qed.
Lemma lem5708213 (r : int) (l : int) : (term251 r l) = ((term251 r l) = True).
Proof. exact (@lem7 (term251 r l)). Qed.
Lemma lem5708215 (l : int) (x : int) : (int_le l x) = ((int_le l x) = True).
Proof. exact (@lem7 (int_le l x)). Qed.
Lemma lem5708224 (x : int) : term788 x.
Proof. exact (fun h0 : term789 x => @lem5708207 x h0). Qed.
Lemma lem5708225 (x : int) (l : int) : term791 x l.
Proof. exact (@lem5708224 (int_sub x l)). Qed.
Lemma lem5708227 (y : int) (x : int) : (term251 x y) = (int_le y x).
Proof. exact (EQ_MP (@lem5708201 y x) (@lem5708200 x y)). Qed.
Lemma lem5708228 (l : int) (x : int) : (term251 x l) = (int_le l x).
Proof. exact (@lem5708227 l x). Qed.
Lemma lem5708230 (l : int) (x : int) (h1 : int_le l x) : (int_le l x) = True.
Proof. exact (EQ_MP (@lem5708215 l x) (@lem5708196 l x h1)). Qed.
Lemma lem5708231 (l : int) (x : int) (h1 : int_le l x) : (term251 x l) = True.
Proof. exact (TRANS (@lem5708228 l x) (@lem5708230 l x h1)). Qed.
Lemma lem5708232 (l : int) (x : int) (h1 : int_le l x) : True = (term251 x l).
Proof. exact (SYM (@lem5708231 l x h1)). Qed.
Lemma lem5708233 (l : int) (x : int) (h1 : int_le l x) : term251 x l.
Proof. exact (EQ_MP (@lem5708232 l x h1) (@lem0)). Qed.
Lemma lem5708234 (l : int) (x : int) (h1 : int_le l x) : (term792 x l) = (int_sub x l).
Proof. exact (@lem5708225 x l (@lem5708233 l x h1)). Qed.
Lemma lem5708235 (l : int) : (int_add l) = (int_add l).
Proof. exact (eq_refl (int_add l)). Qed.
Lemma lem5708236 (l : int) (x : int) (h1 : int_le l x) : (term793 x l) = (term794 x l).
Proof. exact (MK_COMB (@lem5708235 l) (@lem5708234 l x h1)). Qed.
Lemma lem5708237 (x : int) : (@eq int x) = (@eq int x).
Proof. exact (eq_refl (@eq int x)). Qed.
Lemma lem5708238 (l : int) (x : int) (h1 : int_le l x) : (x = (term793 x l)) = (x = (term794 x l)).
Proof. exact (MK_COMB (@lem5708237 x) (@lem5708236 l x h1)). Qed.
Lemma lem5708241 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5708242 (l : int) (x : int) (h1 : int_le l x) : (term795 x l) = (term796 x l).
Proof. exact (MK_COMB (@lem5708241) (@lem5708238 l x h1)). Qed.
Lemma lem5708248 (x : int) : term788 x.
Proof. exact (fun h0 : term789 x => @lem5708207 x h0). Qed.
Lemma lem5708249 (x : int) (l : int) : term791 x l.
Proof. exact (@lem5708248 (int_sub x l)). Qed.
Lemma lem5708251 (y : int) (x : int) : (term251 x y) = (int_le y x).
Proof. exact (EQ_MP (@lem5708201 y x) (@lem5708200 x y)). Qed.
Lemma lem5708252 (l : int) (x : int) : (term251 x l) = (int_le l x).
Proof. exact (@lem5708251 l x). Qed.
Lemma lem5708254 (l : int) (x : int) (h1 : int_le l x) : (int_le l x) = True.
Proof. exact (EQ_MP (@lem5708215 l x) (@lem5708196 l x h1)). Qed.
Lemma lem5708255 (l : int) (x : int) (h1 : int_le l x) : (term251 x l) = True.
Proof. exact (TRANS (@lem5708252 l x) (@lem5708254 l x h1)). Qed.
Lemma lem5708256 (l : int) (x : int) (h1 : int_le l x) : True = (term251 x l).
Proof. exact (SYM (@lem5708255 l x h1)). Qed.
Lemma lem5708257 (l : int) (x : int) (h1 : int_le l x) : term251 x l.
Proof. exact (EQ_MP (@lem5708256 l x h1) (@lem0)). Qed.
Lemma lem5708258 (l : int) (x : int) (h1 : int_le l x) : (term792 x l) = (int_sub x l).
Proof. exact (@lem5708249 x l (@lem5708257 l x h1)). Qed.
Lemma lem5708259 : term797 = term797.
Proof. exact (eq_refl term797). Qed.
Lemma lem5708260 (l : int) (x : int) (h1 : int_le l x) : (term798 x l) = (term251 x l).
Proof. exact (MK_COMB (@lem5708259) (@lem5708258 l x h1)). Qed.
Lemma lem5708262 (y : int) (x : int) : (term251 x y) = (int_le y x).
Proof. exact (EQ_MP (@lem5708201 y x) (@lem5708200 x y)). Qed.
Lemma lem5708263 (l : int) (x : int) : (term251 x l) = (int_le l x).
Proof. exact (@lem5708262 l x). Qed.
Lemma lem5708265 (l : int) (x : int) (h1 : int_le l x) : (int_le l x) = True.
Proof. exact (EQ_MP (@lem5708215 l x) (@lem5708196 l x h1)). Qed.
Lemma lem5708266 (l : int) (x : int) (h1 : int_le l x) : (term251 x l) = True.
Proof. exact (TRANS (@lem5708263 l x) (@lem5708265 l x h1)). Qed.
Lemma lem5708267 (l : int) (x : int) (h1 : int_le l x) : (term798 x l) = True.
Proof. exact (TRANS (@lem5708260 l x h1) (@lem5708266 l x h1)). Qed.
Lemma lem5708268 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5708269 (l : int) (x : int) (h1 : int_le l x) : (term799 x l) = (and True).
Proof. exact (MK_COMB (@lem5708268) (@lem5708267 l x h1)). Qed.
Lemma lem5708271 (x : int) : term788 x.
Proof. exact (fun h0 : term789 x => @lem5708207 x h0). Qed.
Lemma lem5708272 (x : int) (l : int) : term791 x l.
Proof. exact (@lem5708271 (int_sub x l)). Qed.
Lemma lem5708274 (y : int) (x : int) : (term251 x y) = (int_le y x).
Proof. exact (EQ_MP (@lem5708201 y x) (@lem5708200 x y)). Qed.
Lemma lem5708275 (l : int) (x : int) : (term251 x l) = (int_le l x).
Proof. exact (@lem5708274 l x). Qed.
Lemma lem5708277 (l : int) (x : int) (h1 : int_le l x) : (int_le l x) = True.
Proof. exact (EQ_MP (@lem5708215 l x) (@lem5708196 l x h1)). Qed.
Lemma lem5708278 (l : int) (x : int) (h1 : int_le l x) : (term251 x l) = True.
Proof. exact (TRANS (@lem5708275 l x) (@lem5708277 l x h1)). Qed.
Lemma lem5708279 (l : int) (x : int) (h1 : int_le l x) : True = (term251 x l).
Proof. exact (SYM (@lem5708278 l x h1)). Qed.
Lemma lem5708280 (l : int) (x : int) (h1 : int_le l x) : term251 x l.
Proof. exact (EQ_MP (@lem5708279 l x h1) (@lem0)). Qed.
Lemma lem5708281 (l : int) (x : int) (h1 : int_le l x) : (term792 x l) = (int_sub x l).
Proof. exact (@lem5708272 x l (@lem5708280 l x h1)). Qed.
Lemma lem5708282 : int_le = int_le.
Proof. exact (eq_refl int_le). Qed.
Lemma lem5708283 (l : int) (x : int) (h1 : int_le l x) : (term800 x l) = (term801 x l).
Proof. exact (MK_COMB (@lem5708282) (@lem5708281 l x h1)). Qed.
Lemma lem5708285 (x : int) : term788 x.
Proof. exact (fun h0 : term789 x => @lem5708207 x h0). Qed.
Lemma lem5708286 (r : int) (l : int) : term791 r l.
Proof. exact (@lem5708285 (int_sub r l)). Qed.
Lemma lem5708288 (r : int) (l : int) (h1 : term251 r l) : (term251 r l) = True.
Proof. exact (EQ_MP (@lem5708213 r l) (@lem5702058 r l h1)). Qed.
Lemma lem5708289 (r : int) (l : int) (h1 : term251 r l) : True = (term251 r l).
Proof. exact (SYM (@lem5708288 r l h1)). Qed.
Lemma lem5708290 (r : int) (l : int) (h1 : term251 r l) : term251 r l.
Proof. exact (EQ_MP (@lem5708289 r l h1) (@lem0)). Qed.
Lemma lem5708291 (r : int) (l : int) (h1 : term251 r l) : (term792 r l) = (int_sub r l).
Proof. exact (@lem5708286 r l (@lem5708290 r l h1)). Qed.
Lemma lem5708292 (x : int) (r : int) (l : int) (h1 : int_le l x) (h2 : term251 r l) : (term802 x r l) = (term803 x r l).
Proof. exact (MK_COMB (@lem5708283 l x h1) (@lem5708291 r l h2)). Qed.
Lemma lem5708293 (x : int) (r : int) (l : int) (h1 : int_le l x) (h2 : term251 r l) : (term804 x r l) = (term805 x r l).
Proof. exact (MK_COMB (@lem5708269 l x h1) (@lem5708292 x r l h1 h2)). Qed.
Lemma lem5708295 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5708296 (x : int) (r : int) (l : int) : (term805 x r l) = (term803 x r l).
Proof. exact (@lem5708295 (term803 x r l)). Qed.
Lemma lem5708297 (x : int) (r : int) (l : int) (h1 : int_le l x) (h2 : term251 r l) : (term804 x r l) = (term803 x r l).
Proof. exact (TRANS (@lem5708293 x r l h1 h2) (@lem5708296 x r l)). Qed.
Lemma lem5708298 (x : int) (r : int) (l : int) (h1 : int_le l x) (h2 : term251 r l) : (term806 x r l) = (term807 x r l).
Proof. exact (MK_COMB (@lem5708242 l x h1) (@lem5708297 x r l h1 h2)). Qed.
Lemma lem5708303 (x : int) (r : int) (l : int) (h1 : int_le l x) (h2 : term251 r l) : (term807 x r l) = (term806 x r l).
Proof. exact (SYM (@lem5708298 x r l h1 h2)). Qed.
Lemma lem5708304 (x : int) (r : int) (l : int) : (term808 x r l) = (term809 x r l).
Proof. exact (@lem2954598 (term809 x r l)). Qed.
Lemma lem5708327 (x : int) (r : int) (l : int) : (term810 x r l) = (term811 x r l).
Proof. exact (@lem17045 (x = (term794 x l)) (term803 x r l)). Qed.
Lemma lem5708329 (x : int) (r : int) : (term83 x r) = (term83 x r).
Proof. exact (eq_refl (term83 x r)). Qed.
Lemma lem5708330 (x : int) (r : int) (l : int) : (term812 x r l) = (term813 x r l).
Proof. exact (MK_COMB (@lem5708329 x r) (@lem5708327 x r l)). Qed.
Lemma lem5708331 (x : int) (r : int) (l : int) : (term814 x r l) = (term812 x r l).
Proof. exact (@lem17362 (int_le x r) (term807 x r l)). Qed.
Lemma lem5708332 (x : int) (r : int) (l : int) : (term814 x r l) = (term813 x r l).
Proof. exact (TRANS (@lem5708331 x r l) (@lem5708330 x r l)). Qed.
Lemma lem5708334 (l : int) (x : int) : (term83 l x) = (term83 l x).
Proof. exact (eq_refl (term83 l x)). Qed.
Lemma lem5708335 (x : int) (r : int) (l : int) : (term815 x r l) = (term816 x r l).
Proof. exact (MK_COMB (@lem5708334 l x) (@lem5708332 x r l)). Qed.
Lemma lem5708336 (x : int) (r : int) (l : int) : (term817 x r l) = (term815 x r l).
Proof. exact (@lem17362 (int_le l x) (term818 x r l)). Qed.
Lemma lem5708337 (x : int) (r : int) (l : int) : (term817 x r l) = (term816 x r l).
Proof. exact (TRANS (@lem5708336 x r l) (@lem5708335 x r l)). Qed.
Lemma lem5708339 (r : int) (l : int) : (term819 r l) = (term819 r l).
Proof. exact (eq_refl (term819 r l)). Qed.
Lemma lem5708340 (x : int) (r : int) (l : int) : (term820 x r l) = (term821 x r l).
Proof. exact (MK_COMB (@lem5708339 r l) (@lem5708337 x r l)). Qed.
Lemma lem5708341 (x : int) (r : int) (l : int) : (term822 x r l) = (term820 x r l).
Proof. exact (@lem17362 (term251 r l) (term823 x r l)). Qed.
Lemma lem5708399 (x : int) (r : int) (l : int) : (term822 x r l) = (term821 x r l).
Proof. exact (TRANS (@lem5708341 x r l) (@lem5708340 x r l)). Qed.
Lemma lem5708402 (x : int) (y : int) : (int_le x y) = (term61 x y).
Proof. exact (EQ_MP (@lem2841616 x y) (@lem2841615 x y)). Qed.
Lemma lem5708403 (r : int) (l : int) : (term251 r l) = (term824 r l).
Proof. exact (@lem5708402 term60 (int_sub r l)). Qed.
Lemma lem5708405 (n : nat) : (term73 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem5708406 : term80 = term81.
Proof. exact (@lem5708405 (NUMERAL 0)). Qed.
Lemma lem5708407 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5708408 : term825 = term236.
Proof. exact (MK_COMB (@lem5708407) (@lem5708406)). Qed.
Lemma lem5708410 (x : int) (y : int) : (term69 x y) = (term70 x y).
Proof. exact (EQ_MP (@lem2841574 x y) (@lem2841573 x y)). Qed.
Lemma lem5708411 (r : int) (l : int) : (term69 r l) = (term70 r l).
Proof. exact (@lem5708410 r l). Qed.
Lemma lem5708412 (r : int) (l : int) : (term824 r l) = (term826 r l).
Proof. exact (MK_COMB (@lem5708408) (@lem5708411 r l)). Qed.
Lemma lem5708414 (r : int) (l : int) : (term251 r l) = (term826 r l).
Proof. exact (TRANS (@lem5708403 r l) (@lem5708412 r l)). Qed.
Lemma lem5708417 (x : int) (y : int) : (int_le x y) = (term61 x y).
Proof. exact (EQ_MP (@lem2841616 x y) (@lem2841615 x y)). Qed.
Lemma lem5708419 (l : int) (x : int) : (int_le l x) = (term61 l x).
Proof. exact (@lem5708417 l x). Qed.
Lemma lem5708422 (x : int) (y : int) : (int_le x y) = (term61 x y).
Proof. exact (EQ_MP (@lem2841616 x y) (@lem2841615 x y)). Qed.
Lemma lem5708424 (x : int) (r : int) : (int_le x r) = (term61 x r).
Proof. exact (@lem5708422 x r). Qed.
Lemma lem5708426 (y : int) (x : int) : (term827 x y) = (term828 y x).
Proof. exact (proj1 (@lem2841544 x y)). Qed.
Lemma lem5708427 (l : int) (x : int) : (term829 x l) = (term830 l x).
Proof. exact (@lem5708426 (term794 x l) x). Qed.
Lemma lem5708429 (x : int) (y : int) : (int_le x y) = (term61 x y).
Proof. exact (EQ_MP (@lem2841616 x y) (@lem2841615 x y)). Qed.
Lemma lem5708430 (x : int) (l : int) : (term831 x l) = (term832 x l).
Proof. exact (@lem5708429 (term541 x) (term794 x l)). Qed.
Lemma lem5708432 (x : int) (y : int) : (term64 x y) = (term65 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem5708433 (x : int) : (term542 x) = (term543 x).
Proof. exact (@lem5708432 x term68). Qed.
Lemma lem5708435 (n : nat) : (term73 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem5708436 : term74 = term75.
Proof. exact (@lem5708435 term76). Qed.
Lemma lem5708437 (x : int) : (term143 x) = (term143 x).
Proof. exact (eq_refl (term143 x)). Qed.
Lemma lem5708438 (x : int) : (term543 x) = (term104 x).
Proof. exact (MK_COMB (@lem5708437 x) (@lem5708436)). Qed.
Lemma lem5708439 (x : int) : (term542 x) = (term104 x).
Proof. exact (TRANS (@lem5708433 x) (@lem5708438 x)). Qed.
Lemma lem5708440 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5708441 (x : int) : (term544 x) = (term545 x).
Proof. exact (MK_COMB (@lem5708440) (@lem5708439 x)). Qed.
Lemma lem5708443 (x : int) (y : int) : (term64 x y) = (term65 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem5708444 (x : int) (l : int) : (term833 x l) = (term834 x l).
Proof. exact (@lem5708443 l (int_sub x l)). Qed.
Lemma lem5708446 (x : int) (y : int) : (term69 x y) = (term70 x y).
Proof. exact (EQ_MP (@lem2841574 x y) (@lem2841573 x y)). Qed.
Lemma lem5708447 (x : int) (l : int) : (term69 x l) = (term70 x l).
Proof. exact (@lem5708446 x l). Qed.
Lemma lem5708448 (l : int) : (term143 l) = (term143 l).
Proof. exact (eq_refl (term143 l)). Qed.
Lemma lem5708449 (x : int) (l : int) : (term834 x l) = (term835 x l).
Proof. exact (MK_COMB (@lem5708448 l) (@lem5708447 x l)). Qed.
Lemma lem5708450 (x : int) (l : int) : (term833 x l) = (term835 x l).
Proof. exact (TRANS (@lem5708444 x l) (@lem5708449 x l)). Qed.
Lemma lem5708451 (x : int) (l : int) : (term832 x l) = (term836 x l).
Proof. exact (MK_COMB (@lem5708441 x) (@lem5708450 x l)). Qed.
Lemma lem5708452 (x : int) (l : int) : (term831 x l) = (term836 x l).
Proof. exact (TRANS (@lem5708430 x l) (@lem5708451 x l)). Qed.
Lemma lem5708453 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5708454 (x : int) (l : int) : (term837 x l) = (term838 x l).
Proof. exact (MK_COMB (@lem5708453) (@lem5708452 x l)). Qed.
Lemma lem5708456 (x : int) (y : int) : (int_le x y) = (term61 x y).
Proof. exact (EQ_MP (@lem2841616 x y) (@lem2841615 x y)). Qed.
Lemma lem5708457 (l : int) (x : int) : (term839 l x) = (term840 l x).
Proof. exact (@lem5708456 (term841 x l) x). Qed.
Lemma lem5708459 (x : int) (y : int) : (term64 x y) = (term65 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem5708460 (x : int) (l : int) : (term842 x l) = (term843 x l).
Proof. exact (@lem5708459 (term794 x l) term68). Qed.
Lemma lem5708462 (x : int) (y : int) : (term64 x y) = (term65 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem5708463 (x : int) (l : int) : (term833 x l) = (term834 x l).
Proof. exact (@lem5708462 l (int_sub x l)). Qed.
Lemma lem5708465 (x : int) (y : int) : (term69 x y) = (term70 x y).
Proof. exact (EQ_MP (@lem2841574 x y) (@lem2841573 x y)). Qed.
Lemma lem5708466 (x : int) (l : int) : (term69 x l) = (term70 x l).
Proof. exact (@lem5708465 x l). Qed.
Lemma lem5708467 (l : int) : (term143 l) = (term143 l).
Proof. exact (eq_refl (term143 l)). Qed.
Lemma lem5708468 (x : int) (l : int) : (term834 x l) = (term835 x l).
Proof. exact (MK_COMB (@lem5708467 l) (@lem5708466 x l)). Qed.
Lemma lem5708469 (x : int) (l : int) : (term833 x l) = (term835 x l).
Proof. exact (TRANS (@lem5708463 x l) (@lem5708468 x l)). Qed.
Lemma lem5708470 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5708471 (x : int) (l : int) : (term844 x l) = (term845 x l).
Proof. exact (MK_COMB (@lem5708470) (@lem5708469 x l)). Qed.
Lemma lem5708473 (n : nat) : (term73 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem5708474 : term74 = term75.
Proof. exact (@lem5708473 term76). Qed.
Lemma lem5708475 (x : int) (l : int) : (term843 x l) = (term846 x l).
Proof. exact (MK_COMB (@lem5708471 x l) (@lem5708474)). Qed.
Lemma lem5708476 (x : int) (l : int) : (term842 x l) = (term846 x l).
Proof. exact (TRANS (@lem5708460 x l) (@lem5708475 x l)). Qed.
Lemma lem5708477 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5708478 (x : int) (l : int) : (term847 x l) = (term848 x l).
Proof. exact (MK_COMB (@lem5708477) (@lem5708476 x l)). Qed.
Lemma lem5708479 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem5708480 (l : int) (x : int) : (term840 l x) = (term849 l x).
Proof. exact (MK_COMB (@lem5708478 x l) (@lem5708479 x)). Qed.
Lemma lem5708481 (l : int) (x : int) : (term839 l x) = (term849 l x).
Proof. exact (TRANS (@lem5708457 l x) (@lem5708480 l x)). Qed.
Lemma lem5708482 (l : int) (x : int) : (term830 l x) = (term850 l x).
Proof. exact (MK_COMB (@lem5708454 x l) (@lem5708481 l x)). Qed.
Lemma lem5708483 (l : int) (x : int) : (term829 x l) = (term850 l x).
Proof. exact (TRANS (@lem5708427 l x) (@lem5708482 l x)). Qed.
Lemma lem5708485 (y : int) (x : int) : (term57 x y) = (term58 y x).
Proof. exact (proj1 (@lem2841542 x y)). Qed.
Lemma lem5708486 (r : int) (x : int) (l : int) : (term851 x r l) = (term852 r x l).
Proof. exact (@lem5708485 (int_sub r l) (int_sub x l)). Qed.
Lemma lem5708488 (x : int) (y : int) : (int_le x y) = (term61 x y).
Proof. exact (EQ_MP (@lem2841616 x y) (@lem2841615 x y)). Qed.
Lemma lem5708489 (r : int) (x : int) (l : int) : (term852 r x l) = (term853 r x l).
Proof. exact (@lem5708488 (term63 r l) (int_sub x l)). Qed.
Lemma lem5708491 (x : int) (y : int) : (term64 x y) = (term65 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem5708492 (r : int) (l : int) : (term66 r l) = (term67 r l).
Proof. exact (@lem5708491 (int_sub r l) term68). Qed.
Lemma lem5708494 (x : int) (y : int) : (term69 x y) = (term70 x y).
Proof. exact (EQ_MP (@lem2841574 x y) (@lem2841573 x y)). Qed.
Lemma lem5708495 (r : int) (l : int) : (term69 r l) = (term70 r l).
Proof. exact (@lem5708494 r l). Qed.
Lemma lem5708496 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5708497 (r : int) (l : int) : (term71 r l) = (term72 r l).
Proof. exact (MK_COMB (@lem5708496) (@lem5708495 r l)). Qed.
Lemma lem5708499 (n : nat) : (term73 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem5708500 : term74 = term75.
Proof. exact (@lem5708499 term76). Qed.
Lemma lem5708501 (r : int) (l : int) : (term67 r l) = (term77 r l).
Proof. exact (MK_COMB (@lem5708497 r l) (@lem5708500)). Qed.
Lemma lem5708502 (r : int) (l : int) : (term66 r l) = (term77 r l).
Proof. exact (TRANS (@lem5708492 r l) (@lem5708501 r l)). Qed.
Lemma lem5708503 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5708504 (r : int) (l : int) : (term78 r l) = (term79 r l).
Proof. exact (MK_COMB (@lem5708503) (@lem5708502 r l)). Qed.
Lemma lem5708506 (x : int) (y : int) : (term69 x y) = (term70 x y).
Proof. exact (EQ_MP (@lem2841574 x y) (@lem2841573 x y)). Qed.
Lemma lem5708507 (x : int) (l : int) : (term69 x l) = (term70 x l).
Proof. exact (@lem5708506 x l). Qed.
Lemma lem5708508 (r : int) (x : int) (l : int) : (term853 r x l) = (term854 r x l).
Proof. exact (MK_COMB (@lem5708504 r l) (@lem5708507 x l)). Qed.
Lemma lem5708509 (r : int) (x : int) (l : int) : (term852 r x l) = (term854 r x l).
Proof. exact (TRANS (@lem5708489 r x l) (@lem5708508 r x l)). Qed.
Lemma lem5708510 (r : int) (x : int) (l : int) : (term851 x r l) = (term854 r x l).
Proof. exact (TRANS (@lem5708486 r x l) (@lem5708509 r x l)). Qed.
Lemma lem5708511 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5708512 (l : int) (x : int) : (term855 x l) = (term856 l x).
Proof. exact (MK_COMB (@lem5708511) (@lem5708483 l x)). Qed.
Lemma lem5708513 (r : int) (x : int) (l : int) : (term811 x r l) = (term857 r x l).
Proof. exact (MK_COMB (@lem5708512 l x) (@lem5708510 r x l)). Qed.
Lemma lem5708514 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5708515 (x : int) (r : int) : (term83 x r) = (term84 x r).
Proof. exact (MK_COMB (@lem5708514) (@lem5708424 x r)). Qed.
Lemma lem5708516 (r : int) (x : int) (l : int) : (term813 x r l) = (term858 r x l).
Proof. exact (MK_COMB (@lem5708515 x r) (@lem5708513 r x l)). Qed.
Lemma lem5708517 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5708518 (l : int) (x : int) : (term83 l x) = (term84 l x).
Proof. exact (MK_COMB (@lem5708517) (@lem5708419 l x)). Qed.
Lemma lem5708519 (r : int) (x : int) (l : int) : (term816 x r l) = (term859 r x l).
Proof. exact (MK_COMB (@lem5708518 l x) (@lem5708516 r x l)). Qed.
Lemma lem5708520 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5708521 (r : int) (l : int) : (term819 r l) = (term860 r l).
Proof. exact (MK_COMB (@lem5708520) (@lem5708414 r l)). Qed.
Lemma lem5708522 (r : int) (x : int) (l : int) : (term821 x r l) = (term861 r x l).
Proof. exact (MK_COMB (@lem5708521 r l) (@lem5708519 r x l)). Qed.
Lemma lem5708523 (r : int) (x : int) (l : int) : (term822 x r l) = (term861 r x l).
Proof. exact (TRANS (@lem5708399 x r l) (@lem5708522 r x l)). Qed.
Lemma lem5708527 (t : Prop) : (term88 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5708583 (r : int) (x : int) (l : int) : (term862 r x l) = (term861 r x l).
Proof. exact (@lem5708527 (term861 r x l)). Qed.
Lemma lem5708584 (r : int) (l : int) : (term826 r l) = (term863 r l).
Proof. exact (@lem1988287 (term70 r l) term81). Qed.
Lemma lem5708585 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem5708591 (r : int) (l : int) : (term70 r l) = (term91 r l).
Proof. exact (@lem1982792 (real_of_int r) (real_of_int l)). Qed.
Lemma lem5708596 (l : int) (r : int) : (term91 r l) = (term92 l r).
Proof. exact (@lem1982761 (term93 l) (real_of_int r)). Qed.
Lemma lem5708598 (l : int) (r : int) : (term70 r l) = (term92 l r).
Proof. exact (TRANS (@lem5708591 r l) (@lem5708596 l r)). Qed.
Lemma lem5708599 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem5708600 (l : int) (r : int) : (term864 r l) = (term865 l r).
Proof. exact (MK_COMB (@lem5708599) (@lem5708598 l r)). Qed.
Lemma lem5708601 (l : int) (r : int) : (term866 r l) = (term867 l r).
Proof. exact (MK_COMB (@lem5708600 l r) (@lem5708585)). Qed.
Lemma lem5708602 (l : int) (r : int) : (term867 l r) = (term868 l r).
Proof. exact (@lem1982792 (term92 l r) term81). Qed.
Lemma lem5708604 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5708605 : term81 = term162.
Proof. exact (@lem5708604 (NUMERAL 0)). Qed.
Lemma lem5708607 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5708608 : term103 = term111.
Proof. exact (@lem5708607 term76). Qed.
Lemma lem5708609 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5708610 : term112 = term113.
Proof. exact (MK_COMB (@lem5708609) (@lem5708608)). Qed.
Lemma lem5708611 : term869 = term870.
Proof. exact (MK_COMB (@lem5708610) (@lem5708605)). Qed.
Lemma lem5708612 : term870 = term871.
Proof. exact (@lem1981613 term103 term81 term75 term75). Qed.
Lemma lem5708614 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5708615 : term119 = term120.
Proof. exact (@lem5708614 term76 term76). Qed.
Lemma lem5708616 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5708617 : term122 = term76.
Proof. exact (EQ_MP (@lem5708616) (@lem940073)). Qed.
Lemma lem5708618 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5708619 : term120 = term75.
Proof. exact (MK_COMB (@lem5708618) (@lem5708617)). Qed.
Lemma lem5708620 : term119 = term75.
Proof. exact (TRANS (@lem5708615) (@lem5708619)). Qed.
Lemma lem5708622 (x : nat) : (term872 x) = term81.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5708623 : term869 = term81.
Proof. exact (@lem5708622 term76). Qed.
Lemma lem5708624 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5708625 : term873 = term874.
Proof. exact (MK_COMB (@lem5708624) (@lem5708623)). Qed.
Lemma lem5708626 : term871 = term162.
Proof. exact (MK_COMB (@lem5708625) (@lem5708620)). Qed.
Lemma lem5708627 : term870 = term162.
Proof. exact (TRANS (@lem5708612) (@lem5708626)). Qed.
Lemma lem5708628 : term869 = term162.
Proof. exact (TRANS (@lem5708611) (@lem5708627)). Qed.
Lemma lem5708630 (x : real) : (term128 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5708631 : term162 = term81.
Proof. exact (@lem5708630 term81). Qed.
Lemma lem5708632 : term869 = term81.
Proof. exact (TRANS (@lem5708628) (@lem5708631)). Qed.
Lemma lem5708633 (l : int) (r : int) : (term94 l r) = (term94 l r).
Proof. exact (eq_refl (term94 l r)). Qed.
Lemma lem5708634 (l : int) (r : int) : (term868 l r) = (term875 l r).
Proof. exact (MK_COMB (@lem5708633 l r) (@lem5708632)). Qed.
Lemma lem5708635 (l : int) (r : int) : (term875 l r) = (term92 l r).
Proof. exact (@lem1982723 (term92 l r)). Qed.
Lemma lem5708636 (l : int) (r : int) : (term868 l r) = (term92 l r).
Proof. exact (TRANS (@lem5708634 l r) (@lem5708635 l r)). Qed.
Lemma lem5708637 (l : int) (r : int) : (term867 l r) = (term92 l r).
Proof. exact (TRANS (@lem5708602 l r) (@lem5708636 l r)). Qed.
Lemma lem5708638 (l : int) (r : int) : (term866 r l) = (term92 l r).
Proof. exact (TRANS (@lem5708601 l r) (@lem5708637 l r)). Qed.
Lemma lem5708639 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5708640 (l : int) (r : int) : (term876 r l) = (term152 l r).
Proof. exact (MK_COMB (@lem5708639) (@lem5708638 l r)). Qed.
Lemma lem5708641 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem5708642 (l : int) (r : int) : (term863 r l) = (term153 l r).
Proof. exact (MK_COMB (@lem5708640 l r) (@lem5708641)). Qed.
Lemma lem5708643 (l : int) (r : int) : (term826 r l) = (term153 l r).
Proof. exact (TRANS (@lem5708584 r l) (@lem5708642 l r)). Qed.
Lemma lem5708644 (x : int) (l : int) : (term61 l x) = (term150 x l).
Proof. exact (@lem1988287 (real_of_int x) (real_of_int l)). Qed.
Lemma lem5708650 (x : int) (l : int) : (term70 x l) = (term91 x l).
Proof. exact (@lem1982792 (real_of_int x) (real_of_int l)). Qed.
Lemma lem5708655 (l : int) (x : int) : (term91 x l) = (term92 l x).
Proof. exact (@lem1982761 (term93 l) (real_of_int x)). Qed.
Lemma lem5708657 (l : int) (x : int) : (term70 x l) = (term92 l x).
Proof. exact (TRANS (@lem5708650 x l) (@lem5708655 l x)). Qed.
Lemma lem5708658 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5708659 (l : int) (x : int) : (term151 x l) = (term152 l x).
Proof. exact (MK_COMB (@lem5708658) (@lem5708657 l x)). Qed.
Lemma lem5708660 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem5708661 (l : int) (x : int) : (term150 x l) = (term153 l x).
Proof. exact (MK_COMB (@lem5708659 l x) (@lem5708660)). Qed.
Lemma lem5708662 (l : int) (x : int) : (term61 l x) = (term153 l x).
Proof. exact (TRANS (@lem5708644 x l) (@lem5708661 l x)). Qed.
Lemma lem5708663 (r : int) (x : int) : (term61 x r) = (term150 r x).
Proof. exact (@lem1988287 (real_of_int r) (real_of_int x)). Qed.
Lemma lem5708676 (r : int) (x : int) : (term70 r x) = (term91 r x).
Proof. exact (@lem1982792 (real_of_int r) (real_of_int x)). Qed.
Lemma lem5708677 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5708678 (r : int) (x : int) : (term151 r x) = (term154 r x).
Proof. exact (MK_COMB (@lem5708677) (@lem5708676 r x)). Qed.
Lemma lem5708679 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem5708680 (r : int) (x : int) : (term150 r x) = (term155 r x).
Proof. exact (MK_COMB (@lem5708678 r x) (@lem5708679)). Qed.
Lemma lem5708681 (r : int) (x : int) : (term61 x r) = (term155 r x).
Proof. exact (TRANS (@lem5708663 r x) (@lem5708680 r x)). Qed.
Lemma lem5708682 (l : int) (x : int) : (term836 x l) = (term877 l x).
Proof. exact (@lem1988287 (term835 x l) (term104 x)). Qed.
Lemma lem5708689 (x : int) : (term104 x) = (term104 x).
Proof. exact (eq_refl (term104 x)). Qed.
Lemma lem5708695 (x : int) (l : int) : (term70 x l) = (term91 x l).
Proof. exact (@lem1982792 (real_of_int x) (real_of_int l)). Qed.
Lemma lem5708700 (l : int) (x : int) : (term91 x l) = (term92 l x).
Proof. exact (@lem1982761 (term93 l) (real_of_int x)). Qed.
Lemma lem5708702 (l : int) (x : int) : (term70 x l) = (term92 l x).
Proof. exact (TRANS (@lem5708695 x l) (@lem5708700 l x)). Qed.
Lemma lem5708705 (l : int) : (term143 l) = (term143 l).
Proof. exact (eq_refl (term143 l)). Qed.
Lemma lem5708706 (l : int) (x : int) : (term835 x l) = (term878 l x).
Proof. exact (MK_COMB (@lem5708705 l) (@lem5708702 l x)). Qed.
Lemma lem5708707 (l : int) (x : int) : (term878 l x) = (term879 l x).
Proof. exact (@lem1982763 (real_of_int l) (term93 l) (real_of_int x)). Qed.
Lemma lem5708708 (l : int) : (term229 l) = (term195 l).
Proof. exact (@lem1982715 term103 (real_of_int l)). Qed.
Lemma lem5708710 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5708711 : term75 = term108.
Proof. exact (@lem5708710 term76). Qed.
Lemma lem5708713 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5708714 : term103 = term111.
Proof. exact (@lem5708713 term76). Qed.
Lemma lem5708715 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5708716 : term196 = term197.
Proof. exact (MK_COMB (@lem5708715) (@lem5708714)). Qed.
Lemma lem5708717 : term198 = term199.
Proof. exact (MK_COMB (@lem5708716) (@lem5708711)). Qed.
Lemma lem5708718 : term200.
Proof. exact (@lem1981473 term103 term75 term75 term75 term81 term75). Qed.
Lemma lem5708720 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5708721 : term161 = term168.
Proof. exact (@lem5708720 (NUMERAL 0) term76). Qed.
Lemma lem5708722 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5708723 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5708724 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5708723 h1) (fun h1 : term168 = True => @lem5708722)). Qed.
Lemma lem5708725 : term168 = True.
Proof. exact (EQ_MP (@lem5708724) (@lem5708722)). Qed.
Lemma lem5708726 : term161 = True.
Proof. exact (TRANS (@lem5708721) (@lem5708725)). Qed.
Lemma lem5708727 : True = term161.
Proof. exact (SYM (@lem5708726)). Qed.
Lemma lem5708728 : term161.
Proof. exact (EQ_MP (@lem5708727) (@lem0)). Qed.
Lemma lem5708729 : term201.
Proof. exact (@lem5708718 (@lem5708728)). Qed.
Lemma lem5708731 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5708732 : term161 = term168.
Proof. exact (@lem5708731 (NUMERAL 0) term76). Qed.
Lemma lem5708733 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5708734 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5708735 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5708734 h1) (fun h1 : term168 = True => @lem5708733)). Qed.
Lemma lem5708736 : term168 = True.
Proof. exact (EQ_MP (@lem5708735) (@lem5708733)). Qed.
Lemma lem5708737 : term161 = True.
Proof. exact (TRANS (@lem5708732) (@lem5708736)). Qed.
Lemma lem5708738 : True = term161.
Proof. exact (SYM (@lem5708737)). Qed.
Lemma lem5708739 : term161.
Proof. exact (EQ_MP (@lem5708738) (@lem0)). Qed.
Lemma lem5708740 : term202.
Proof. exact (@lem5708729 (@lem5708739)). Qed.
Lemma lem5708742 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5708743 : term161 = term168.
Proof. exact (@lem5708742 (NUMERAL 0) term76). Qed.
Lemma lem5708744 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5708745 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5708746 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5708745 h1) (fun h1 : term168 = True => @lem5708744)). Qed.
Lemma lem5708747 : term168 = True.
Proof. exact (EQ_MP (@lem5708746) (@lem5708744)). Qed.
Lemma lem5708748 : term161 = True.
Proof. exact (TRANS (@lem5708743) (@lem5708747)). Qed.
Lemma lem5708749 : True = term161.
Proof. exact (SYM (@lem5708748)). Qed.
Lemma lem5708750 : term161.
Proof. exact (EQ_MP (@lem5708749) (@lem0)). Qed.
Lemma lem5708751 : term203.
Proof. exact (@lem5708740 (@lem5708750)). Qed.
Lemma lem5708753 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5708754 : term119 = term120.
Proof. exact (@lem5708753 term76 term76). Qed.
Lemma lem5708755 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5708756 : term122 = term76.
Proof. exact (EQ_MP (@lem5708755) (@lem940073)). Qed.
Lemma lem5708757 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5708758 : term120 = term75.
Proof. exact (MK_COMB (@lem5708757) (@lem5708756)). Qed.
Lemma lem5708759 : term119 = term75.
Proof. exact (TRANS (@lem5708754) (@lem5708758)). Qed.
Lemma lem5708761 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5708762 : term114 = term125.
Proof. exact (@lem5708761 term76 term76). Qed.
Lemma lem5708763 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5708764 : term122 = term76.
Proof. exact (EQ_MP (@lem5708763) (@lem940073)). Qed.
Lemma lem5708765 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5708766 : term120 = term75.
Proof. exact (MK_COMB (@lem5708765) (@lem5708764)). Qed.
Lemma lem5708767 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5708768 : term125 = term103.
Proof. exact (MK_COMB (@lem5708767) (@lem5708766)). Qed.
Lemma lem5708769 : term114 = term103.
Proof. exact (TRANS (@lem5708762) (@lem5708768)). Qed.
Lemma lem5708770 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5708771 : term204 = term196.
Proof. exact (MK_COMB (@lem5708770) (@lem5708769)). Qed.
Lemma lem5708772 : term205 = term198.
Proof. exact (MK_COMB (@lem5708771) (@lem5708759)). Qed.
Lemma lem5708774 (m : nat) : (term206 m) = term81.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5708775 : term198 = term81.
Proof. exact (@lem5708774 term76). Qed.
Lemma lem5708776 : term205 = term81.
Proof. exact (TRANS (@lem5708772) (@lem5708775)). Qed.
Lemma lem5708777 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5708778 : term207 = term208.
Proof. exact (MK_COMB (@lem5708777) (@lem5708776)). Qed.
Lemma lem5708779 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem5708780 : term209 = term173.
Proof. exact (MK_COMB (@lem5708778) (@lem5708779)). Qed.
Lemma lem5708782 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5708783 : term173 = term81.
Proof. exact (@lem5708782 term76). Qed.
Lemma lem5708784 : term209 = term81.
Proof. exact (TRANS (@lem5708780) (@lem5708783)). Qed.
Lemma lem5708786 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5708787 : term119 = term120.
Proof. exact (@lem5708786 term76 term76). Qed.
Lemma lem5708788 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5708789 : term122 = term76.
Proof. exact (EQ_MP (@lem5708788) (@lem940073)). Qed.
Lemma lem5708790 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5708791 : term120 = term75.
Proof. exact (MK_COMB (@lem5708790) (@lem5708789)). Qed.
Lemma lem5708792 : term119 = term75.
Proof. exact (TRANS (@lem5708787) (@lem5708791)). Qed.
Lemma lem5708793 : term208 = term208.
Proof. exact (eq_refl term208). Qed.
Lemma lem5708794 : term210 = term173.
Proof. exact (MK_COMB (@lem5708793) (@lem5708792)). Qed.
Lemma lem5708796 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5708797 : term173 = term81.
Proof. exact (@lem5708796 term76). Qed.
Lemma lem5708798 : term210 = term81.
Proof. exact (TRANS (@lem5708794) (@lem5708797)). Qed.
Lemma lem5708799 : term81 = term210.
Proof. exact (SYM (@lem5708798)). Qed.
Lemma lem5708800 : term209 = term210.
Proof. exact (TRANS (@lem5708784) (@lem5708799)). Qed.
Lemma lem5708801 : term199 = term162.
Proof. exact (@lem5708751 (@lem5708800)). Qed.
Lemma lem5708802 : term198 = term162.
Proof. exact (TRANS (@lem5708717) (@lem5708801)). Qed.
Lemma lem5708804 (x : real) : (term128 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5708805 : term162 = term81.
Proof. exact (@lem5708804 term81). Qed.
Lemma lem5708806 : term198 = term81.
Proof. exact (TRANS (@lem5708802) (@lem5708805)). Qed.
Lemma lem5708807 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5708808 : term211 = term208.
Proof. exact (MK_COMB (@lem5708807) (@lem5708806)). Qed.
Lemma lem5708809 (l : int) : (real_of_int l) = (real_of_int l).
Proof. exact (eq_refl (real_of_int l)). Qed.
Lemma lem5708810 (l : int) : (term195 l) = (term212 l).
Proof. exact (MK_COMB (@lem5708808) (@lem5708809 l)). Qed.
Lemma lem5708811 (l : int) : (term229 l) = (term212 l).
Proof. exact (TRANS (@lem5708708 l) (@lem5708810 l)). Qed.
Lemma lem5708812 (l : int) : (term212 l) = term81.
Proof. exact (@lem1982719 (real_of_int l)). Qed.
Lemma lem5708813 (l : int) : (term229 l) = term81.
Proof. exact (TRANS (@lem5708811 l) (@lem5708812 l)). Qed.
Lemma lem5708814 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5708815 (l : int) : (term230 l) = term145.
Proof. exact (MK_COMB (@lem5708814) (@lem5708813 l)). Qed.
Lemma lem5708816 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem5708817 (l : int) (x : int) : (term879 l x) = (term880 x).
Proof. exact (MK_COMB (@lem5708815 l) (@lem5708816 x)). Qed.
Lemma lem5708818 (l : int) (x : int) : (term878 l x) = (term880 x).
Proof. exact (TRANS (@lem5708707 l x) (@lem5708817 l x)). Qed.
Lemma lem5708819 (x : int) : (term880 x) = (real_of_int x).
Proof. exact (@lem1982721 (real_of_int x)). Qed.
Lemma lem5708820 (l : int) (x : int) : (term878 l x) = (real_of_int x).
Proof. exact (TRANS (@lem5708818 l x) (@lem5708819 x)). Qed.
Lemma lem5708821 (l : int) (x : int) : (term835 x l) = (real_of_int x).
Proof. exact (TRANS (@lem5708706 l x) (@lem5708820 l x)). Qed.
Lemma lem5708822 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem5708823 (l : int) (x : int) : (term881 x l) = (term882 x).
Proof. exact (MK_COMB (@lem5708822) (@lem5708821 l x)). Qed.
Lemma lem5708824 (l : int) (x : int) : (term883 l x) = (term884 x).
Proof. exact (MK_COMB (@lem5708823 l x) (@lem5708689 x)). Qed.
Lemma lem5708825 (x : int) : (term884 x) = (term885 x).
Proof. exact (@lem1982792 (real_of_int x) (term104 x)). Qed.
Lemma lem5708826 (x : int) : (term105 x) = (term106 x).
Proof. exact (@lem1982781 (real_of_int x) term103 term75). Qed.
Lemma lem5708828 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5708829 : term75 = term108.
Proof. exact (@lem5708828 term76). Qed.
Lemma lem5708831 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5708832 : term103 = term111.
Proof. exact (@lem5708831 term76). Qed.
Lemma lem5708833 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5708834 : term112 = term113.
Proof. exact (MK_COMB (@lem5708833) (@lem5708832)). Qed.
Lemma lem5708835 : term114 = term115.
Proof. exact (MK_COMB (@lem5708834) (@lem5708829)). Qed.
Lemma lem5708836 : term115 = term116.
Proof. exact (@lem1981613 term103 term75 term75 term75). Qed.
Lemma lem5708838 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5708839 : term119 = term120.
Proof. exact (@lem5708838 term76 term76). Qed.
Lemma lem5708840 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5708841 : term122 = term76.
Proof. exact (EQ_MP (@lem5708840) (@lem940073)). Qed.
Lemma lem5708842 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5708843 : term120 = term75.
Proof. exact (MK_COMB (@lem5708842) (@lem5708841)). Qed.
Lemma lem5708844 : term119 = term75.
Proof. exact (TRANS (@lem5708839) (@lem5708843)). Qed.
Lemma lem5708846 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5708847 : term114 = term125.
Proof. exact (@lem5708846 term76 term76). Qed.
Lemma lem5708848 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5708849 : term122 = term76.
Proof. exact (EQ_MP (@lem5708848) (@lem940073)). Qed.
Lemma lem5708850 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5708851 : term120 = term75.
Proof. exact (MK_COMB (@lem5708850) (@lem5708849)). Qed.
Lemma lem5708852 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5708853 : term125 = term103.
Proof. exact (MK_COMB (@lem5708852) (@lem5708851)). Qed.
Lemma lem5708854 : term114 = term103.
Proof. exact (TRANS (@lem5708847) (@lem5708853)). Qed.
Lemma lem5708855 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5708856 : term126 = term127.
Proof. exact (MK_COMB (@lem5708855) (@lem5708854)). Qed.
Lemma lem5708857 : term116 = term111.
Proof. exact (MK_COMB (@lem5708856) (@lem5708844)). Qed.
Lemma lem5708858 : term115 = term111.
Proof. exact (TRANS (@lem5708836) (@lem5708857)). Qed.
Lemma lem5708859 : term114 = term111.
Proof. exact (TRANS (@lem5708835) (@lem5708858)). Qed.
Lemma lem5708861 (x : real) : (term128 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5708862 : term111 = term103.
Proof. exact (@lem5708861 term103). Qed.
Lemma lem5708863 : term114 = term103.
Proof. exact (TRANS (@lem5708859) (@lem5708862)). Qed.
Lemma lem5708866 (x : int) : (term129 x) = (term129 x).
Proof. exact (eq_refl (term129 x)). Qed.
Lemma lem5708867 (x : int) : (term106 x) = (term130 x).
Proof. exact (MK_COMB (@lem5708866 x) (@lem5708863)). Qed.
Lemma lem5708868 (x : int) : (term105 x) = (term130 x).
Proof. exact (TRANS (@lem5708826 x) (@lem5708867 x)). Qed.
Lemma lem5708869 (x : int) : (term143 x) = (term143 x).
Proof. exact (eq_refl (term143 x)). Qed.
Lemma lem5708870 (x : int) : (term885 x) = (term227 x).
Proof. exact (MK_COMB (@lem5708869 x) (@lem5708868 x)). Qed.
Lemma lem5708871 (x : int) : (term227 x) = (term228 x).
Proof. exact (@lem1982763 (real_of_int x) (term93 x) term103). Qed.
Lemma lem5708872 (x : int) : (term229 x) = (term195 x).
Proof. exact (@lem1982715 term103 (real_of_int x)). Qed.
Lemma lem5708874 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5708875 : term75 = term108.
Proof. exact (@lem5708874 term76). Qed.
Lemma lem5708877 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5708878 : term103 = term111.
Proof. exact (@lem5708877 term76). Qed.
Lemma lem5708879 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5708880 : term196 = term197.
Proof. exact (MK_COMB (@lem5708879) (@lem5708878)). Qed.
Lemma lem5708881 : term198 = term199.
Proof. exact (MK_COMB (@lem5708880) (@lem5708875)). Qed.
Lemma lem5708882 : term200.
Proof. exact (@lem1981473 term103 term75 term75 term75 term81 term75). Qed.
Lemma lem5708884 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5708885 : term161 = term168.
Proof. exact (@lem5708884 (NUMERAL 0) term76). Qed.
Lemma lem5708886 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5708887 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5708888 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5708887 h1) (fun h1 : term168 = True => @lem5708886)). Qed.
Lemma lem5708889 : term168 = True.
Proof. exact (EQ_MP (@lem5708888) (@lem5708886)). Qed.
Lemma lem5708890 : term161 = True.
Proof. exact (TRANS (@lem5708885) (@lem5708889)). Qed.
Lemma lem5708891 : True = term161.
Proof. exact (SYM (@lem5708890)). Qed.
Lemma lem5708892 : term161.
Proof. exact (EQ_MP (@lem5708891) (@lem0)). Qed.
Lemma lem5708893 : term201.
Proof. exact (@lem5708882 (@lem5708892)). Qed.
Lemma lem5708895 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5708896 : term161 = term168.
Proof. exact (@lem5708895 (NUMERAL 0) term76). Qed.
Lemma lem5708897 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5708898 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5708899 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5708898 h1) (fun h1 : term168 = True => @lem5708897)). Qed.
Lemma lem5708900 : term168 = True.
Proof. exact (EQ_MP (@lem5708899) (@lem5708897)). Qed.
Lemma lem5708901 : term161 = True.
Proof. exact (TRANS (@lem5708896) (@lem5708900)). Qed.
Lemma lem5708902 : True = term161.
Proof. exact (SYM (@lem5708901)). Qed.
Lemma lem5708903 : term161.
Proof. exact (EQ_MP (@lem5708902) (@lem0)). Qed.
Lemma lem5708904 : term202.
Proof. exact (@lem5708893 (@lem5708903)). Qed.
Lemma lem5708906 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5708907 : term161 = term168.
Proof. exact (@lem5708906 (NUMERAL 0) term76). Qed.
Lemma lem5708908 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5708909 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5708910 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5708909 h1) (fun h1 : term168 = True => @lem5708908)). Qed.
Lemma lem5708911 : term168 = True.
Proof. exact (EQ_MP (@lem5708910) (@lem5708908)). Qed.
Lemma lem5708912 : term161 = True.
Proof. exact (TRANS (@lem5708907) (@lem5708911)). Qed.
Lemma lem5708913 : True = term161.
Proof. exact (SYM (@lem5708912)). Qed.
Lemma lem5708914 : term161.
Proof. exact (EQ_MP (@lem5708913) (@lem0)). Qed.
Lemma lem5708915 : term203.
Proof. exact (@lem5708904 (@lem5708914)). Qed.
Lemma lem5708917 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5708918 : term119 = term120.
Proof. exact (@lem5708917 term76 term76). Qed.
Lemma lem5708919 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5708920 : term122 = term76.
Proof. exact (EQ_MP (@lem5708919) (@lem940073)). Qed.
Lemma lem5708921 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5708922 : term120 = term75.
Proof. exact (MK_COMB (@lem5708921) (@lem5708920)). Qed.
Lemma lem5708923 : term119 = term75.
Proof. exact (TRANS (@lem5708918) (@lem5708922)). Qed.
Lemma lem5708925 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5708926 : term114 = term125.
Proof. exact (@lem5708925 term76 term76). Qed.
Lemma lem5708927 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5708928 : term122 = term76.
Proof. exact (EQ_MP (@lem5708927) (@lem940073)). Qed.
Lemma lem5708929 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5708930 : term120 = term75.
Proof. exact (MK_COMB (@lem5708929) (@lem5708928)). Qed.
Lemma lem5708931 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5708932 : term125 = term103.
Proof. exact (MK_COMB (@lem5708931) (@lem5708930)). Qed.
Lemma lem5708933 : term114 = term103.
Proof. exact (TRANS (@lem5708926) (@lem5708932)). Qed.
Lemma lem5708934 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5708935 : term204 = term196.
Proof. exact (MK_COMB (@lem5708934) (@lem5708933)). Qed.
Lemma lem5708936 : term205 = term198.
Proof. exact (MK_COMB (@lem5708935) (@lem5708923)). Qed.
Lemma lem5708938 (m : nat) : (term206 m) = term81.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5708939 : term198 = term81.
Proof. exact (@lem5708938 term76). Qed.
Lemma lem5708940 : term205 = term81.
Proof. exact (TRANS (@lem5708936) (@lem5708939)). Qed.
Lemma lem5708941 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5708942 : term207 = term208.
Proof. exact (MK_COMB (@lem5708941) (@lem5708940)). Qed.
Lemma lem5708943 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem5708944 : term209 = term173.
Proof. exact (MK_COMB (@lem5708942) (@lem5708943)). Qed.
Lemma lem5708946 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5708947 : term173 = term81.
Proof. exact (@lem5708946 term76). Qed.
Lemma lem5708948 : term209 = term81.
Proof. exact (TRANS (@lem5708944) (@lem5708947)). Qed.
Lemma lem5708950 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5708951 : term119 = term120.
Proof. exact (@lem5708950 term76 term76). Qed.
Lemma lem5708952 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5708953 : term122 = term76.
Proof. exact (EQ_MP (@lem5708952) (@lem940073)). Qed.
Lemma lem5708954 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5708955 : term120 = term75.
Proof. exact (MK_COMB (@lem5708954) (@lem5708953)). Qed.
Lemma lem5708956 : term119 = term75.
Proof. exact (TRANS (@lem5708951) (@lem5708955)). Qed.
Lemma lem5708957 : term208 = term208.
Proof. exact (eq_refl term208). Qed.
Lemma lem5708958 : term210 = term173.
Proof. exact (MK_COMB (@lem5708957) (@lem5708956)). Qed.
Lemma lem5708960 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5708961 : term173 = term81.
Proof. exact (@lem5708960 term76). Qed.
Lemma lem5708962 : term210 = term81.
Proof. exact (TRANS (@lem5708958) (@lem5708961)). Qed.
Lemma lem5708963 : term81 = term210.
Proof. exact (SYM (@lem5708962)). Qed.
Lemma lem5708964 : term209 = term210.
Proof. exact (TRANS (@lem5708948) (@lem5708963)). Qed.
Lemma lem5708965 : term199 = term162.
Proof. exact (@lem5708915 (@lem5708964)). Qed.
Lemma lem5708966 : term198 = term162.
Proof. exact (TRANS (@lem5708881) (@lem5708965)). Qed.
Lemma lem5708968 (x : real) : (term128 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5708969 : term162 = term81.
Proof. exact (@lem5708968 term81). Qed.
Lemma lem5708970 : term198 = term81.
Proof. exact (TRANS (@lem5708966) (@lem5708969)). Qed.
Lemma lem5708971 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5708972 : term211 = term208.
Proof. exact (MK_COMB (@lem5708971) (@lem5708970)). Qed.
Lemma lem5708973 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem5708974 (x : int) : (term195 x) = (term212 x).
Proof. exact (MK_COMB (@lem5708972) (@lem5708973 x)). Qed.
Lemma lem5708975 (x : int) : (term229 x) = (term212 x).
Proof. exact (TRANS (@lem5708872 x) (@lem5708974 x)). Qed.
Lemma lem5708976 (x : int) : (term212 x) = term81.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem5708977 (x : int) : (term229 x) = term81.
Proof. exact (TRANS (@lem5708975 x) (@lem5708976 x)). Qed.
Lemma lem5708978 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5708979 (x : int) : (term230 x) = term145.
Proof. exact (MK_COMB (@lem5708978) (@lem5708977 x)). Qed.
Lemma lem5708980 : term103 = term103.
Proof. exact (eq_refl term103). Qed.
Lemma lem5708981 (x : int) : (term228 x) = term231.
Proof. exact (MK_COMB (@lem5708979 x) (@lem5708980)). Qed.
Lemma lem5708982 (x : int) : (term227 x) = term231.
Proof. exact (TRANS (@lem5708871 x) (@lem5708981 x)). Qed.
Lemma lem5708983 : term231 = term103.
Proof. exact (@lem1982721 term103). Qed.
Lemma lem5708984 (x : int) : (term227 x) = term103.
Proof. exact (TRANS (@lem5708982 x) (@lem5708983)). Qed.
Lemma lem5708985 (x : int) : (term885 x) = term103.
Proof. exact (TRANS (@lem5708870 x) (@lem5708984 x)). Qed.
Lemma lem5708986 (x : int) : (term884 x) = term103.
Proof. exact (TRANS (@lem5708825 x) (@lem5708985 x)). Qed.
Lemma lem5708987 (l : int) (x : int) : (term883 l x) = term103.
Proof. exact (TRANS (@lem5708824 l x) (@lem5708986 x)). Qed.
Lemma lem5708988 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5708989 (l : int) (x : int) : (term886 l x) = term233.
Proof. exact (MK_COMB (@lem5708988) (@lem5708987 l x)). Qed.
Lemma lem5708990 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem5708991 (l : int) (x : int) : (term877 l x) = term234.
Proof. exact (MK_COMB (@lem5708989 l x) (@lem5708990)). Qed.
Lemma lem5708992 (x : int) (l : int) : (term836 x l) = term234.
Proof. exact (TRANS (@lem5708682 l x) (@lem5708991 l x)). Qed.
Lemma lem5708993 (x : int) (l : int) : (term849 l x) = (term887 x l).
Proof. exact (@lem1988287 (real_of_int x) (term846 x l)). Qed.
Lemma lem5708994 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem5709000 (x : int) (l : int) : (term70 x l) = (term91 x l).
Proof. exact (@lem1982792 (real_of_int x) (real_of_int l)). Qed.
Lemma lem5709005 (l : int) (x : int) : (term91 x l) = (term92 l x).
Proof. exact (@lem1982761 (term93 l) (real_of_int x)). Qed.
Lemma lem5709007 (l : int) (x : int) : (term70 x l) = (term92 l x).
Proof. exact (TRANS (@lem5709000 x l) (@lem5709005 l x)). Qed.
Lemma lem5709010 (l : int) : (term143 l) = (term143 l).
Proof. exact (eq_refl (term143 l)). Qed.
Lemma lem5709011 (l : int) (x : int) : (term835 x l) = (term878 l x).
Proof. exact (MK_COMB (@lem5709010 l) (@lem5709007 l x)). Qed.
Lemma lem5709012 (l : int) (x : int) : (term878 l x) = (term879 l x).
Proof. exact (@lem1982763 (real_of_int l) (term93 l) (real_of_int x)). Qed.
Lemma lem5709013 (l : int) : (term229 l) = (term195 l).
Proof. exact (@lem1982715 term103 (real_of_int l)). Qed.
Lemma lem5709015 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5709016 : term75 = term108.
Proof. exact (@lem5709015 term76). Qed.
Lemma lem5709018 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5709019 : term103 = term111.
Proof. exact (@lem5709018 term76). Qed.
Lemma lem5709020 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5709021 : term196 = term197.
Proof. exact (MK_COMB (@lem5709020) (@lem5709019)). Qed.
Lemma lem5709022 : term198 = term199.
Proof. exact (MK_COMB (@lem5709021) (@lem5709016)). Qed.
Lemma lem5709023 : term200.
Proof. exact (@lem1981473 term103 term75 term75 term75 term81 term75). Qed.
Lemma lem5709025 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5709026 : term161 = term168.
Proof. exact (@lem5709025 (NUMERAL 0) term76). Qed.
Lemma lem5709027 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5709028 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5709029 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5709028 h1) (fun h1 : term168 = True => @lem5709027)). Qed.
Lemma lem5709030 : term168 = True.
Proof. exact (EQ_MP (@lem5709029) (@lem5709027)). Qed.
Lemma lem5709031 : term161 = True.
Proof. exact (TRANS (@lem5709026) (@lem5709030)). Qed.
Lemma lem5709032 : True = term161.
Proof. exact (SYM (@lem5709031)). Qed.
Lemma lem5709033 : term161.
Proof. exact (EQ_MP (@lem5709032) (@lem0)). Qed.
Lemma lem5709034 : term201.
Proof. exact (@lem5709023 (@lem5709033)). Qed.
Lemma lem5709036 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5709037 : term161 = term168.
Proof. exact (@lem5709036 (NUMERAL 0) term76). Qed.
Lemma lem5709038 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5709039 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5709040 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5709039 h1) (fun h1 : term168 = True => @lem5709038)). Qed.
Lemma lem5709041 : term168 = True.
Proof. exact (EQ_MP (@lem5709040) (@lem5709038)). Qed.
Lemma lem5709042 : term161 = True.
Proof. exact (TRANS (@lem5709037) (@lem5709041)). Qed.
Lemma lem5709043 : True = term161.
Proof. exact (SYM (@lem5709042)). Qed.
Lemma lem5709044 : term161.
Proof. exact (EQ_MP (@lem5709043) (@lem0)). Qed.
Lemma lem5709045 : term202.
Proof. exact (@lem5709034 (@lem5709044)). Qed.
Lemma lem5709047 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5709048 : term161 = term168.
Proof. exact (@lem5709047 (NUMERAL 0) term76). Qed.
Lemma lem5709049 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5709050 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5709051 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5709050 h1) (fun h1 : term168 = True => @lem5709049)). Qed.
Lemma lem5709052 : term168 = True.
Proof. exact (EQ_MP (@lem5709051) (@lem5709049)). Qed.
Lemma lem5709053 : term161 = True.
Proof. exact (TRANS (@lem5709048) (@lem5709052)). Qed.
Lemma lem5709054 : True = term161.
Proof. exact (SYM (@lem5709053)). Qed.
Lemma lem5709055 : term161.
Proof. exact (EQ_MP (@lem5709054) (@lem0)). Qed.
Lemma lem5709056 : term203.
Proof. exact (@lem5709045 (@lem5709055)). Qed.
Lemma lem5709058 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5709059 : term119 = term120.
Proof. exact (@lem5709058 term76 term76). Qed.
Lemma lem5709060 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5709061 : term122 = term76.
Proof. exact (EQ_MP (@lem5709060) (@lem940073)). Qed.
Lemma lem5709062 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5709063 : term120 = term75.
Proof. exact (MK_COMB (@lem5709062) (@lem5709061)). Qed.
Lemma lem5709064 : term119 = term75.
Proof. exact (TRANS (@lem5709059) (@lem5709063)). Qed.
Lemma lem5709066 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5709067 : term114 = term125.
Proof. exact (@lem5709066 term76 term76). Qed.
Lemma lem5709068 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5709069 : term122 = term76.
Proof. exact (EQ_MP (@lem5709068) (@lem940073)). Qed.
Lemma lem5709070 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5709071 : term120 = term75.
Proof. exact (MK_COMB (@lem5709070) (@lem5709069)). Qed.
Lemma lem5709072 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5709073 : term125 = term103.
Proof. exact (MK_COMB (@lem5709072) (@lem5709071)). Qed.
Lemma lem5709074 : term114 = term103.
Proof. exact (TRANS (@lem5709067) (@lem5709073)). Qed.
Lemma lem5709075 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5709076 : term204 = term196.
Proof. exact (MK_COMB (@lem5709075) (@lem5709074)). Qed.
Lemma lem5709077 : term205 = term198.
Proof. exact (MK_COMB (@lem5709076) (@lem5709064)). Qed.
Lemma lem5709079 (m : nat) : (term206 m) = term81.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5709080 : term198 = term81.
Proof. exact (@lem5709079 term76). Qed.
Lemma lem5709081 : term205 = term81.
Proof. exact (TRANS (@lem5709077) (@lem5709080)). Qed.
Lemma lem5709082 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5709083 : term207 = term208.
Proof. exact (MK_COMB (@lem5709082) (@lem5709081)). Qed.
Lemma lem5709084 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem5709085 : term209 = term173.
Proof. exact (MK_COMB (@lem5709083) (@lem5709084)). Qed.
Lemma lem5709087 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5709088 : term173 = term81.
Proof. exact (@lem5709087 term76). Qed.
Lemma lem5709089 : term209 = term81.
Proof. exact (TRANS (@lem5709085) (@lem5709088)). Qed.
Lemma lem5709091 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5709092 : term119 = term120.
Proof. exact (@lem5709091 term76 term76). Qed.
Lemma lem5709093 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5709094 : term122 = term76.
Proof. exact (EQ_MP (@lem5709093) (@lem940073)). Qed.
Lemma lem5709095 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5709096 : term120 = term75.
Proof. exact (MK_COMB (@lem5709095) (@lem5709094)). Qed.
Lemma lem5709097 : term119 = term75.
Proof. exact (TRANS (@lem5709092) (@lem5709096)). Qed.
Lemma lem5709098 : term208 = term208.
Proof. exact (eq_refl term208). Qed.
Lemma lem5709099 : term210 = term173.
Proof. exact (MK_COMB (@lem5709098) (@lem5709097)). Qed.
Lemma lem5709101 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5709102 : term173 = term81.
Proof. exact (@lem5709101 term76). Qed.
Lemma lem5709103 : term210 = term81.
Proof. exact (TRANS (@lem5709099) (@lem5709102)). Qed.
Lemma lem5709104 : term81 = term210.
Proof. exact (SYM (@lem5709103)). Qed.
Lemma lem5709105 : term209 = term210.
Proof. exact (TRANS (@lem5709089) (@lem5709104)). Qed.
Lemma lem5709106 : term199 = term162.
Proof. exact (@lem5709056 (@lem5709105)). Qed.
Lemma lem5709107 : term198 = term162.
Proof. exact (TRANS (@lem5709022) (@lem5709106)). Qed.
Lemma lem5709109 (x : real) : (term128 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5709110 : term162 = term81.
Proof. exact (@lem5709109 term81). Qed.
Lemma lem5709111 : term198 = term81.
Proof. exact (TRANS (@lem5709107) (@lem5709110)). Qed.
Lemma lem5709112 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5709113 : term211 = term208.
Proof. exact (MK_COMB (@lem5709112) (@lem5709111)). Qed.
Lemma lem5709114 (l : int) : (real_of_int l) = (real_of_int l).
Proof. exact (eq_refl (real_of_int l)). Qed.
Lemma lem5709115 (l : int) : (term195 l) = (term212 l).
Proof. exact (MK_COMB (@lem5709113) (@lem5709114 l)). Qed.
Lemma lem5709116 (l : int) : (term229 l) = (term212 l).
Proof. exact (TRANS (@lem5709013 l) (@lem5709115 l)). Qed.
Lemma lem5709117 (l : int) : (term212 l) = term81.
Proof. exact (@lem1982719 (real_of_int l)). Qed.
Lemma lem5709118 (l : int) : (term229 l) = term81.
Proof. exact (TRANS (@lem5709116 l) (@lem5709117 l)). Qed.
Lemma lem5709119 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5709120 (l : int) : (term230 l) = term145.
Proof. exact (MK_COMB (@lem5709119) (@lem5709118 l)). Qed.
Lemma lem5709121 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem5709122 (l : int) (x : int) : (term879 l x) = (term880 x).
Proof. exact (MK_COMB (@lem5709120 l) (@lem5709121 x)). Qed.
Lemma lem5709123 (l : int) (x : int) : (term878 l x) = (term880 x).
Proof. exact (TRANS (@lem5709012 l x) (@lem5709122 l x)). Qed.
Lemma lem5709124 (x : int) : (term880 x) = (real_of_int x).
Proof. exact (@lem1982721 (real_of_int x)). Qed.
Lemma lem5709125 (l : int) (x : int) : (term878 l x) = (real_of_int x).
Proof. exact (TRANS (@lem5709123 l x) (@lem5709124 x)). Qed.
Lemma lem5709126 (l : int) (x : int) : (term835 x l) = (real_of_int x).
Proof. exact (TRANS (@lem5709011 l x) (@lem5709125 l x)). Qed.
Lemma lem5709127 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5709128 (l : int) (x : int) : (term845 x l) = (term143 x).
Proof. exact (MK_COMB (@lem5709127) (@lem5709126 l x)). Qed.
Lemma lem5709131 (l : int) (x : int) : (term846 x l) = (term104 x).
Proof. exact (MK_COMB (@lem5709128 l x) (@lem5708994)). Qed.
Lemma lem5709134 (x : int) : (term882 x) = (term882 x).
Proof. exact (eq_refl (term882 x)). Qed.
Lemma lem5709135 (l : int) (x : int) : (term888 x l) = (term884 x).
Proof. exact (MK_COMB (@lem5709134 x) (@lem5709131 l x)). Qed.
Lemma lem5709136 (x : int) : (term884 x) = (term885 x).
Proof. exact (@lem1982792 (real_of_int x) (term104 x)). Qed.
Lemma lem5709137 (x : int) : (term105 x) = (term106 x).
Proof. exact (@lem1982781 (real_of_int x) term103 term75). Qed.
Lemma lem5709139 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5709140 : term75 = term108.
Proof. exact (@lem5709139 term76). Qed.
Lemma lem5709142 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5709143 : term103 = term111.
Proof. exact (@lem5709142 term76). Qed.
Lemma lem5709144 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5709145 : term112 = term113.
Proof. exact (MK_COMB (@lem5709144) (@lem5709143)). Qed.
Lemma lem5709146 : term114 = term115.
Proof. exact (MK_COMB (@lem5709145) (@lem5709140)). Qed.
Lemma lem5709147 : term115 = term116.
Proof. exact (@lem1981613 term103 term75 term75 term75). Qed.
Lemma lem5709149 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5709150 : term119 = term120.
Proof. exact (@lem5709149 term76 term76). Qed.
Lemma lem5709151 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5709152 : term122 = term76.
Proof. exact (EQ_MP (@lem5709151) (@lem940073)). Qed.
Lemma lem5709153 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5709154 : term120 = term75.
Proof. exact (MK_COMB (@lem5709153) (@lem5709152)). Qed.
Lemma lem5709155 : term119 = term75.
Proof. exact (TRANS (@lem5709150) (@lem5709154)). Qed.
Lemma lem5709157 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5709158 : term114 = term125.
Proof. exact (@lem5709157 term76 term76). Qed.
Lemma lem5709159 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5709160 : term122 = term76.
Proof. exact (EQ_MP (@lem5709159) (@lem940073)). Qed.
Lemma lem5709161 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5709162 : term120 = term75.
Proof. exact (MK_COMB (@lem5709161) (@lem5709160)). Qed.
Lemma lem5709163 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5709164 : term125 = term103.
Proof. exact (MK_COMB (@lem5709163) (@lem5709162)). Qed.
Lemma lem5709165 : term114 = term103.
Proof. exact (TRANS (@lem5709158) (@lem5709164)). Qed.
Lemma lem5709166 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5709167 : term126 = term127.
Proof. exact (MK_COMB (@lem5709166) (@lem5709165)). Qed.
Lemma lem5709168 : term116 = term111.
Proof. exact (MK_COMB (@lem5709167) (@lem5709155)). Qed.
Lemma lem5709169 : term115 = term111.
Proof. exact (TRANS (@lem5709147) (@lem5709168)). Qed.
Lemma lem5709170 : term114 = term111.
Proof. exact (TRANS (@lem5709146) (@lem5709169)). Qed.
Lemma lem5709172 (x : real) : (term128 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5709173 : term111 = term103.
Proof. exact (@lem5709172 term103). Qed.
Lemma lem5709174 : term114 = term103.
Proof. exact (TRANS (@lem5709170) (@lem5709173)). Qed.
Lemma lem5709177 (x : int) : (term129 x) = (term129 x).
Proof. exact (eq_refl (term129 x)). Qed.
Lemma lem5709178 (x : int) : (term106 x) = (term130 x).
Proof. exact (MK_COMB (@lem5709177 x) (@lem5709174)). Qed.
Lemma lem5709179 (x : int) : (term105 x) = (term130 x).
Proof. exact (TRANS (@lem5709137 x) (@lem5709178 x)). Qed.
Lemma lem5709180 (x : int) : (term143 x) = (term143 x).
Proof. exact (eq_refl (term143 x)). Qed.
Lemma lem5709181 (x : int) : (term885 x) = (term227 x).
Proof. exact (MK_COMB (@lem5709180 x) (@lem5709179 x)). Qed.
Lemma lem5709182 (x : int) : (term227 x) = (term228 x).
Proof. exact (@lem1982763 (real_of_int x) (term93 x) term103). Qed.
Lemma lem5709183 (x : int) : (term229 x) = (term195 x).
Proof. exact (@lem1982715 term103 (real_of_int x)). Qed.
Lemma lem5709185 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5709186 : term75 = term108.
Proof. exact (@lem5709185 term76). Qed.
Lemma lem5709188 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5709189 : term103 = term111.
Proof. exact (@lem5709188 term76). Qed.
Lemma lem5709190 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5709191 : term196 = term197.
Proof. exact (MK_COMB (@lem5709190) (@lem5709189)). Qed.
Lemma lem5709192 : term198 = term199.
Proof. exact (MK_COMB (@lem5709191) (@lem5709186)). Qed.
Lemma lem5709193 : term200.
Proof. exact (@lem1981473 term103 term75 term75 term75 term81 term75). Qed.
Lemma lem5709195 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5709196 : term161 = term168.
Proof. exact (@lem5709195 (NUMERAL 0) term76). Qed.
Lemma lem5709197 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5709198 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5709199 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5709198 h1) (fun h1 : term168 = True => @lem5709197)). Qed.
Lemma lem5709200 : term168 = True.
Proof. exact (EQ_MP (@lem5709199) (@lem5709197)). Qed.
Lemma lem5709201 : term161 = True.
Proof. exact (TRANS (@lem5709196) (@lem5709200)). Qed.
Lemma lem5709202 : True = term161.
Proof. exact (SYM (@lem5709201)). Qed.
Lemma lem5709203 : term161.
Proof. exact (EQ_MP (@lem5709202) (@lem0)). Qed.
Lemma lem5709204 : term201.
Proof. exact (@lem5709193 (@lem5709203)). Qed.
Lemma lem5709206 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5709207 : term161 = term168.
Proof. exact (@lem5709206 (NUMERAL 0) term76). Qed.
Lemma lem5709208 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5709209 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5709210 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5709209 h1) (fun h1 : term168 = True => @lem5709208)). Qed.
Lemma lem5709211 : term168 = True.
Proof. exact (EQ_MP (@lem5709210) (@lem5709208)). Qed.
Lemma lem5709212 : term161 = True.
Proof. exact (TRANS (@lem5709207) (@lem5709211)). Qed.
Lemma lem5709213 : True = term161.
Proof. exact (SYM (@lem5709212)). Qed.
Lemma lem5709214 : term161.
Proof. exact (EQ_MP (@lem5709213) (@lem0)). Qed.
Lemma lem5709215 : term202.
Proof. exact (@lem5709204 (@lem5709214)). Qed.
Lemma lem5709217 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5709218 : term161 = term168.
Proof. exact (@lem5709217 (NUMERAL 0) term76). Qed.
Lemma lem5709219 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5709220 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5709221 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5709220 h1) (fun h1 : term168 = True => @lem5709219)). Qed.
Lemma lem5709222 : term168 = True.
Proof. exact (EQ_MP (@lem5709221) (@lem5709219)). Qed.
Lemma lem5709223 : term161 = True.
Proof. exact (TRANS (@lem5709218) (@lem5709222)). Qed.
Lemma lem5709224 : True = term161.
Proof. exact (SYM (@lem5709223)). Qed.
Lemma lem5709225 : term161.
Proof. exact (EQ_MP (@lem5709224) (@lem0)). Qed.
Lemma lem5709226 : term203.
Proof. exact (@lem5709215 (@lem5709225)). Qed.
Lemma lem5709228 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5709229 : term119 = term120.
Proof. exact (@lem5709228 term76 term76). Qed.
Lemma lem5709230 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5709231 : term122 = term76.
Proof. exact (EQ_MP (@lem5709230) (@lem940073)). Qed.
Lemma lem5709232 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5709233 : term120 = term75.
Proof. exact (MK_COMB (@lem5709232) (@lem5709231)). Qed.
Lemma lem5709234 : term119 = term75.
Proof. exact (TRANS (@lem5709229) (@lem5709233)). Qed.
Lemma lem5709236 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5709237 : term114 = term125.
Proof. exact (@lem5709236 term76 term76). Qed.
Lemma lem5709238 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5709239 : term122 = term76.
Proof. exact (EQ_MP (@lem5709238) (@lem940073)). Qed.
Lemma lem5709240 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5709241 : term120 = term75.
Proof. exact (MK_COMB (@lem5709240) (@lem5709239)). Qed.
Lemma lem5709242 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5709243 : term125 = term103.
Proof. exact (MK_COMB (@lem5709242) (@lem5709241)). Qed.
Lemma lem5709244 : term114 = term103.
Proof. exact (TRANS (@lem5709237) (@lem5709243)). Qed.
Lemma lem5709245 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5709246 : term204 = term196.
Proof. exact (MK_COMB (@lem5709245) (@lem5709244)). Qed.
Lemma lem5709247 : term205 = term198.
Proof. exact (MK_COMB (@lem5709246) (@lem5709234)). Qed.
Lemma lem5709249 (m : nat) : (term206 m) = term81.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5709250 : term198 = term81.
Proof. exact (@lem5709249 term76). Qed.
Lemma lem5709251 : term205 = term81.
Proof. exact (TRANS (@lem5709247) (@lem5709250)). Qed.
Lemma lem5709252 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5709253 : term207 = term208.
Proof. exact (MK_COMB (@lem5709252) (@lem5709251)). Qed.
Lemma lem5709254 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem5709255 : term209 = term173.
Proof. exact (MK_COMB (@lem5709253) (@lem5709254)). Qed.
Lemma lem5709257 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5709258 : term173 = term81.
Proof. exact (@lem5709257 term76). Qed.
Lemma lem5709259 : term209 = term81.
Proof. exact (TRANS (@lem5709255) (@lem5709258)). Qed.
Lemma lem5709261 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5709262 : term119 = term120.
Proof. exact (@lem5709261 term76 term76). Qed.
Lemma lem5709263 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5709264 : term122 = term76.
Proof. exact (EQ_MP (@lem5709263) (@lem940073)). Qed.
Lemma lem5709265 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5709266 : term120 = term75.
Proof. exact (MK_COMB (@lem5709265) (@lem5709264)). Qed.
Lemma lem5709267 : term119 = term75.
Proof. exact (TRANS (@lem5709262) (@lem5709266)). Qed.
Lemma lem5709268 : term208 = term208.
Proof. exact (eq_refl term208). Qed.
Lemma lem5709269 : term210 = term173.
Proof. exact (MK_COMB (@lem5709268) (@lem5709267)). Qed.
Lemma lem5709271 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5709272 : term173 = term81.
Proof. exact (@lem5709271 term76). Qed.
Lemma lem5709273 : term210 = term81.
Proof. exact (TRANS (@lem5709269) (@lem5709272)). Qed.
Lemma lem5709274 : term81 = term210.
Proof. exact (SYM (@lem5709273)). Qed.
Lemma lem5709275 : term209 = term210.
Proof. exact (TRANS (@lem5709259) (@lem5709274)). Qed.
Lemma lem5709276 : term199 = term162.
Proof. exact (@lem5709226 (@lem5709275)). Qed.
Lemma lem5709277 : term198 = term162.
Proof. exact (TRANS (@lem5709192) (@lem5709276)). Qed.
Lemma lem5709279 (x : real) : (term128 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5709280 : term162 = term81.
Proof. exact (@lem5709279 term81). Qed.
Lemma lem5709281 : term198 = term81.
Proof. exact (TRANS (@lem5709277) (@lem5709280)). Qed.
Lemma lem5709282 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5709283 : term211 = term208.
Proof. exact (MK_COMB (@lem5709282) (@lem5709281)). Qed.
Lemma lem5709284 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem5709285 (x : int) : (term195 x) = (term212 x).
Proof. exact (MK_COMB (@lem5709283) (@lem5709284 x)). Qed.
Lemma lem5709286 (x : int) : (term229 x) = (term212 x).
Proof. exact (TRANS (@lem5709183 x) (@lem5709285 x)). Qed.
Lemma lem5709287 (x : int) : (term212 x) = term81.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem5709288 (x : int) : (term229 x) = term81.
Proof. exact (TRANS (@lem5709286 x) (@lem5709287 x)). Qed.
Lemma lem5709289 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5709290 (x : int) : (term230 x) = term145.
Proof. exact (MK_COMB (@lem5709289) (@lem5709288 x)). Qed.
Lemma lem5709291 : term103 = term103.
Proof. exact (eq_refl term103). Qed.
Lemma lem5709292 (x : int) : (term228 x) = term231.
Proof. exact (MK_COMB (@lem5709290 x) (@lem5709291)). Qed.
Lemma lem5709293 (x : int) : (term227 x) = term231.
Proof. exact (TRANS (@lem5709182 x) (@lem5709292 x)). Qed.
Lemma lem5709294 : term231 = term103.
Proof. exact (@lem1982721 term103). Qed.
Lemma lem5709295 (x : int) : (term227 x) = term103.
Proof. exact (TRANS (@lem5709293 x) (@lem5709294)). Qed.
Lemma lem5709296 (x : int) : (term885 x) = term103.
Proof. exact (TRANS (@lem5709181 x) (@lem5709295 x)). Qed.
Lemma lem5709297 (x : int) : (term884 x) = term103.
Proof. exact (TRANS (@lem5709136 x) (@lem5709296 x)). Qed.
Lemma lem5709298 (x : int) (l : int) : (term888 x l) = term103.
Proof. exact (TRANS (@lem5709135 l x) (@lem5709297 x)). Qed.
Lemma lem5709299 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5709300 (x : int) (l : int) : (term889 x l) = term233.
Proof. exact (MK_COMB (@lem5709299) (@lem5709298 x l)). Qed.
Lemma lem5709301 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem5709302 (x : int) (l : int) : (term887 x l) = term234.
Proof. exact (MK_COMB (@lem5709300 x l) (@lem5709301)). Qed.
Lemma lem5709303 (l : int) (x : int) : (term849 l x) = term234.
Proof. exact (TRANS (@lem5708993 x l) (@lem5709302 x l)). Qed.
Lemma lem5709304 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5709305 (x : int) (l : int) : (term838 x l) = term890.
Proof. exact (MK_COMB (@lem5709304) (@lem5708992 x l)). Qed.
Lemma lem5709306 (l : int) (x : int) : (term850 l x) = term891.
Proof. exact (MK_COMB (@lem5709305 x l) (@lem5709303 l x)). Qed.
Lemma lem5709307 (x : int) (r : int) (l : int) : (term854 r x l) = (term892 x r l).
Proof. exact (@lem1988287 (term70 x l) (term77 r l)). Qed.
Lemma lem5709308 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem5709314 (r : int) (l : int) : (term70 r l) = (term91 r l).
Proof. exact (@lem1982792 (real_of_int r) (real_of_int l)). Qed.
Lemma lem5709319 (l : int) (r : int) : (term91 r l) = (term92 l r).
Proof. exact (@lem1982761 (term93 l) (real_of_int r)). Qed.
Lemma lem5709321 (l : int) (r : int) : (term70 r l) = (term92 l r).
Proof. exact (TRANS (@lem5709314 r l) (@lem5709319 l r)). Qed.
Lemma lem5709322 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5709323 (l : int) (r : int) : (term72 r l) = (term94 l r).
Proof. exact (MK_COMB (@lem5709322) (@lem5709321 l r)). Qed.
Lemma lem5709324 (l : int) (r : int) : (term77 r l) = (term95 l r).
Proof. exact (MK_COMB (@lem5709323 l r) (@lem5709308)). Qed.
Lemma lem5709329 (l : int) (r : int) : (term95 l r) = (term96 l r).
Proof. exact (@lem1982755 (term93 l) (real_of_int r) term75). Qed.
Lemma lem5709330 (l : int) (r : int) : (term77 r l) = (term96 l r).
Proof. exact (TRANS (@lem5709324 l r) (@lem5709329 l r)). Qed.
Lemma lem5709336 (x : int) (l : int) : (term70 x l) = (term91 x l).
Proof. exact (@lem1982792 (real_of_int x) (real_of_int l)). Qed.
Lemma lem5709341 (l : int) (x : int) : (term91 x l) = (term92 l x).
Proof. exact (@lem1982761 (term93 l) (real_of_int x)). Qed.
Lemma lem5709343 (l : int) (x : int) : (term70 x l) = (term92 l x).
Proof. exact (TRANS (@lem5709336 x l) (@lem5709341 l x)). Qed.
Lemma lem5709344 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem5709345 (l : int) (x : int) : (term864 x l) = (term865 l x).
Proof. exact (MK_COMB (@lem5709344) (@lem5709343 l x)). Qed.
Lemma lem5709346 (x : int) (l : int) (r : int) : (term893 x r l) = (term894 x l r).
Proof. exact (MK_COMB (@lem5709345 l x) (@lem5709330 l r)). Qed.
Lemma lem5709347 (x : int) (l : int) (r : int) : (term894 x l r) = (term895 x l r).
Proof. exact (@lem1982792 (term92 l x) (term96 l r)). Qed.
Lemma lem5709348 (l : int) (r : int) : (term101 l r) = (term102 l r).
Proof. exact (@lem1982781 (term93 l) term103 (term104 r)). Qed.
Lemma lem5709349 (r : int) : (term105 r) = (term106 r).
Proof. exact (@lem1982781 (real_of_int r) term103 term75). Qed.
Lemma lem5709351 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5709352 : term75 = term108.
Proof. exact (@lem5709351 term76). Qed.
Lemma lem5709354 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5709355 : term103 = term111.
Proof. exact (@lem5709354 term76). Qed.
Lemma lem5709356 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5709357 : term112 = term113.
Proof. exact (MK_COMB (@lem5709356) (@lem5709355)). Qed.
Lemma lem5709358 : term114 = term115.
Proof. exact (MK_COMB (@lem5709357) (@lem5709352)). Qed.
Lemma lem5709359 : term115 = term116.
Proof. exact (@lem1981613 term103 term75 term75 term75). Qed.
Lemma lem5709361 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5709362 : term119 = term120.
Proof. exact (@lem5709361 term76 term76). Qed.
Lemma lem5709363 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5709364 : term122 = term76.
Proof. exact (EQ_MP (@lem5709363) (@lem940073)). Qed.
Lemma lem5709365 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5709366 : term120 = term75.
Proof. exact (MK_COMB (@lem5709365) (@lem5709364)). Qed.
Lemma lem5709367 : term119 = term75.
Proof. exact (TRANS (@lem5709362) (@lem5709366)). Qed.
Lemma lem5709369 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5709370 : term114 = term125.
Proof. exact (@lem5709369 term76 term76). Qed.
Lemma lem5709371 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5709372 : term122 = term76.
Proof. exact (EQ_MP (@lem5709371) (@lem940073)). Qed.
Lemma lem5709373 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5709374 : term120 = term75.
Proof. exact (MK_COMB (@lem5709373) (@lem5709372)). Qed.
Lemma lem5709375 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5709376 : term125 = term103.
Proof. exact (MK_COMB (@lem5709375) (@lem5709374)). Qed.
Lemma lem5709377 : term114 = term103.
Proof. exact (TRANS (@lem5709370) (@lem5709376)). Qed.
Lemma lem5709378 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5709379 : term126 = term127.
Proof. exact (MK_COMB (@lem5709378) (@lem5709377)). Qed.
Lemma lem5709380 : term116 = term111.
Proof. exact (MK_COMB (@lem5709379) (@lem5709367)). Qed.
Lemma lem5709381 : term115 = term111.
Proof. exact (TRANS (@lem5709359) (@lem5709380)). Qed.
Lemma lem5709382 : term114 = term111.
Proof. exact (TRANS (@lem5709358) (@lem5709381)). Qed.
Lemma lem5709384 (x : real) : (term128 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5709385 : term111 = term103.
Proof. exact (@lem5709384 term103). Qed.
Lemma lem5709386 : term114 = term103.
Proof. exact (TRANS (@lem5709382) (@lem5709385)). Qed.
Lemma lem5709389 (r : int) : (term129 r) = (term129 r).
Proof. exact (eq_refl (term129 r)). Qed.
Lemma lem5709390 (r : int) : (term106 r) = (term130 r).
Proof. exact (MK_COMB (@lem5709389 r) (@lem5709386)). Qed.
Lemma lem5709391 (r : int) : (term105 r) = (term130 r).
Proof. exact (TRANS (@lem5709349 r) (@lem5709390 r)). Qed.
Lemma lem5709392 (l : int) : (term131 l) = (term132 l).
Proof. exact (@lem1982749 term103 term103 (real_of_int l)). Qed.
Lemma lem5709394 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5709395 : term103 = term111.
Proof. exact (@lem5709394 term76). Qed.
Lemma lem5709397 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5709398 : term103 = term111.
Proof. exact (@lem5709397 term76). Qed.
Lemma lem5709399 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5709400 : term112 = term113.
Proof. exact (MK_COMB (@lem5709399) (@lem5709398)). Qed.
Lemma lem5709401 : term133 = term134.
Proof. exact (MK_COMB (@lem5709400) (@lem5709395)). Qed.
Lemma lem5709402 : term134 = term135.
Proof. exact (@lem1981613 term103 term103 term75 term75). Qed.
Lemma lem5709404 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5709405 : term119 = term120.
Proof. exact (@lem5709404 term76 term76). Qed.
Lemma lem5709406 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5709407 : term122 = term76.
Proof. exact (EQ_MP (@lem5709406) (@lem940073)). Qed.
Lemma lem5709408 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5709409 : term120 = term75.
Proof. exact (MK_COMB (@lem5709408) (@lem5709407)). Qed.
Lemma lem5709410 : term119 = term75.
Proof. exact (TRANS (@lem5709405) (@lem5709409)). Qed.
Lemma lem5709412 (m : nat) (n : nat) : (term136 m n) = (term118 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem5709413 : term133 = term120.
Proof. exact (@lem5709412 term76 term76). Qed.
Lemma lem5709414 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5709415 : term122 = term76.
Proof. exact (EQ_MP (@lem5709414) (@lem940073)). Qed.
Lemma lem5709416 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5709417 : term120 = term75.
Proof. exact (MK_COMB (@lem5709416) (@lem5709415)). Qed.
Lemma lem5709418 : term133 = term75.
Proof. exact (TRANS (@lem5709413) (@lem5709417)). Qed.
Lemma lem5709419 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5709420 : term137 = term138.
Proof. exact (MK_COMB (@lem5709419) (@lem5709418)). Qed.
Lemma lem5709421 : term135 = term108.
Proof. exact (MK_COMB (@lem5709420) (@lem5709410)). Qed.
Lemma lem5709422 : term134 = term108.
Proof. exact (TRANS (@lem5709402) (@lem5709421)). Qed.
Lemma lem5709423 : term133 = term108.
Proof. exact (TRANS (@lem5709401) (@lem5709422)). Qed.
Lemma lem5709425 (x : real) : (term128 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5709426 : term108 = term75.
Proof. exact (@lem5709425 term75). Qed.
Lemma lem5709427 : term133 = term75.
Proof. exact (TRANS (@lem5709423) (@lem5709426)). Qed.
Lemma lem5709428 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5709429 : term139 = term140.
Proof. exact (MK_COMB (@lem5709428) (@lem5709427)). Qed.
Lemma lem5709430 (l : int) : (real_of_int l) = (real_of_int l).
Proof. exact (eq_refl (real_of_int l)). Qed.
Lemma lem5709431 (l : int) : (term132 l) = (term141 l).
Proof. exact (MK_COMB (@lem5709429) (@lem5709430 l)). Qed.
Lemma lem5709432 (l : int) : (term131 l) = (term141 l).
Proof. exact (TRANS (@lem5709392 l) (@lem5709431 l)). Qed.
Lemma lem5709433 (l : int) : (term141 l) = (real_of_int l).
Proof. exact (@lem1982709 (real_of_int l)). Qed.
Lemma lem5709434 (l : int) : (term131 l) = (real_of_int l).
Proof. exact (TRANS (@lem5709432 l) (@lem5709433 l)). Qed.
Lemma lem5709435 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5709436 (l : int) : (term142 l) = (term143 l).
Proof. exact (MK_COMB (@lem5709435) (@lem5709434 l)). Qed.
Lemma lem5709437 (l : int) (r : int) : (term102 l r) = (term144 l r).
Proof. exact (MK_COMB (@lem5709436 l) (@lem5709391 r)). Qed.
Lemma lem5709438 (l : int) (r : int) : (term101 l r) = (term144 l r).
Proof. exact (TRANS (@lem5709348 l r) (@lem5709437 l r)). Qed.
Lemma lem5709439 (l : int) (x : int) : (term94 l x) = (term94 l x).
Proof. exact (eq_refl (term94 l x)). Qed.
Lemma lem5709440 (x : int) (l : int) (r : int) : (term895 x l r) = (term896 x l r).
Proof. exact (MK_COMB (@lem5709439 l x) (@lem5709438 l r)). Qed.
Lemma lem5709441 (l : int) (x : int) (r : int) : (term896 x l r) = (term897 l x r).
Proof. exact (@lem1982753 (term93 l) (real_of_int l) (real_of_int x) (term130 r)). Qed.
Lemma lem5709442 (l : int) : (term194 l) = (term195 l).
Proof. exact (@lem1982713 term103 (real_of_int l)). Qed.
Lemma lem5709444 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5709445 : term75 = term108.
Proof. exact (@lem5709444 term76). Qed.
Lemma lem5709447 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5709448 : term103 = term111.
Proof. exact (@lem5709447 term76). Qed.
Lemma lem5709449 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5709450 : term196 = term197.
Proof. exact (MK_COMB (@lem5709449) (@lem5709448)). Qed.
Lemma lem5709451 : term198 = term199.
Proof. exact (MK_COMB (@lem5709450) (@lem5709445)). Qed.
Lemma lem5709452 : term200.
Proof. exact (@lem1981473 term103 term75 term75 term75 term81 term75). Qed.
Lemma lem5709454 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5709455 : term161 = term168.
Proof. exact (@lem5709454 (NUMERAL 0) term76). Qed.
Lemma lem5709456 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5709457 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5709458 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5709457 h1) (fun h1 : term168 = True => @lem5709456)). Qed.
Lemma lem5709459 : term168 = True.
Proof. exact (EQ_MP (@lem5709458) (@lem5709456)). Qed.
Lemma lem5709460 : term161 = True.
Proof. exact (TRANS (@lem5709455) (@lem5709459)). Qed.
Lemma lem5709461 : True = term161.
Proof. exact (SYM (@lem5709460)). Qed.
Lemma lem5709462 : term161.
Proof. exact (EQ_MP (@lem5709461) (@lem0)). Qed.
Lemma lem5709463 : term201.
Proof. exact (@lem5709452 (@lem5709462)). Qed.
Lemma lem5709465 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5709466 : term161 = term168.
Proof. exact (@lem5709465 (NUMERAL 0) term76). Qed.
Lemma lem5709467 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5709468 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5709469 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5709468 h1) (fun h1 : term168 = True => @lem5709467)). Qed.
Lemma lem5709470 : term168 = True.
Proof. exact (EQ_MP (@lem5709469) (@lem5709467)). Qed.
Lemma lem5709471 : term161 = True.
Proof. exact (TRANS (@lem5709466) (@lem5709470)). Qed.
Lemma lem5709472 : True = term161.
Proof. exact (SYM (@lem5709471)). Qed.
Lemma lem5709473 : term161.
Proof. exact (EQ_MP (@lem5709472) (@lem0)). Qed.
Lemma lem5709474 : term202.
Proof. exact (@lem5709463 (@lem5709473)). Qed.
Lemma lem5709476 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5709477 : term161 = term168.
Proof. exact (@lem5709476 (NUMERAL 0) term76). Qed.
Lemma lem5709478 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5709479 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5709480 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5709479 h1) (fun h1 : term168 = True => @lem5709478)). Qed.
Lemma lem5709481 : term168 = True.
Proof. exact (EQ_MP (@lem5709480) (@lem5709478)). Qed.
Lemma lem5709482 : term161 = True.
Proof. exact (TRANS (@lem5709477) (@lem5709481)). Qed.
Lemma lem5709483 : True = term161.
Proof. exact (SYM (@lem5709482)). Qed.
Lemma lem5709484 : term161.
Proof. exact (EQ_MP (@lem5709483) (@lem0)). Qed.
Lemma lem5709485 : term203.
Proof. exact (@lem5709474 (@lem5709484)). Qed.
Lemma lem5709487 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5709488 : term119 = term120.
Proof. exact (@lem5709487 term76 term76). Qed.
Lemma lem5709489 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5709490 : term122 = term76.
Proof. exact (EQ_MP (@lem5709489) (@lem940073)). Qed.
Lemma lem5709491 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5709492 : term120 = term75.
Proof. exact (MK_COMB (@lem5709491) (@lem5709490)). Qed.
Lemma lem5709493 : term119 = term75.
Proof. exact (TRANS (@lem5709488) (@lem5709492)). Qed.
Lemma lem5709495 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5709496 : term114 = term125.
Proof. exact (@lem5709495 term76 term76). Qed.
Lemma lem5709497 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5709498 : term122 = term76.
Proof. exact (EQ_MP (@lem5709497) (@lem940073)). Qed.
Lemma lem5709499 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5709500 : term120 = term75.
Proof. exact (MK_COMB (@lem5709499) (@lem5709498)). Qed.
Lemma lem5709501 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5709502 : term125 = term103.
Proof. exact (MK_COMB (@lem5709501) (@lem5709500)). Qed.
Lemma lem5709503 : term114 = term103.
Proof. exact (TRANS (@lem5709496) (@lem5709502)). Qed.
Lemma lem5709504 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5709505 : term204 = term196.
Proof. exact (MK_COMB (@lem5709504) (@lem5709503)). Qed.
Lemma lem5709506 : term205 = term198.
Proof. exact (MK_COMB (@lem5709505) (@lem5709493)). Qed.
Lemma lem5709508 (m : nat) : (term206 m) = term81.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5709509 : term198 = term81.
Proof. exact (@lem5709508 term76). Qed.
Lemma lem5709510 : term205 = term81.
Proof. exact (TRANS (@lem5709506) (@lem5709509)). Qed.
Lemma lem5709511 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5709512 : term207 = term208.
Proof. exact (MK_COMB (@lem5709511) (@lem5709510)). Qed.
Lemma lem5709513 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem5709514 : term209 = term173.
Proof. exact (MK_COMB (@lem5709512) (@lem5709513)). Qed.
Lemma lem5709516 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5709517 : term173 = term81.
Proof. exact (@lem5709516 term76). Qed.
Lemma lem5709518 : term209 = term81.
Proof. exact (TRANS (@lem5709514) (@lem5709517)). Qed.
Lemma lem5709520 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5709521 : term119 = term120.
Proof. exact (@lem5709520 term76 term76). Qed.
Lemma lem5709522 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5709523 : term122 = term76.
Proof. exact (EQ_MP (@lem5709522) (@lem940073)). Qed.
Lemma lem5709524 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5709525 : term120 = term75.
Proof. exact (MK_COMB (@lem5709524) (@lem5709523)). Qed.
Lemma lem5709526 : term119 = term75.
Proof. exact (TRANS (@lem5709521) (@lem5709525)). Qed.
Lemma lem5709527 : term208 = term208.
Proof. exact (eq_refl term208). Qed.
Lemma lem5709528 : term210 = term173.
Proof. exact (MK_COMB (@lem5709527) (@lem5709526)). Qed.
Lemma lem5709530 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5709531 : term173 = term81.
Proof. exact (@lem5709530 term76). Qed.
Lemma lem5709532 : term210 = term81.
Proof. exact (TRANS (@lem5709528) (@lem5709531)). Qed.
Lemma lem5709533 : term81 = term210.
Proof. exact (SYM (@lem5709532)). Qed.
Lemma lem5709534 : term209 = term210.
Proof. exact (TRANS (@lem5709518) (@lem5709533)). Qed.
Lemma lem5709535 : term199 = term162.
Proof. exact (@lem5709485 (@lem5709534)). Qed.
Lemma lem5709536 : term198 = term162.
Proof. exact (TRANS (@lem5709451) (@lem5709535)). Qed.
Lemma lem5709538 (x : real) : (term128 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5709539 : term162 = term81.
Proof. exact (@lem5709538 term81). Qed.
Lemma lem5709540 : term198 = term81.
Proof. exact (TRANS (@lem5709536) (@lem5709539)). Qed.
Lemma lem5709541 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5709542 : term211 = term208.
Proof. exact (MK_COMB (@lem5709541) (@lem5709540)). Qed.
Lemma lem5709543 (l : int) : (real_of_int l) = (real_of_int l).
Proof. exact (eq_refl (real_of_int l)). Qed.
Lemma lem5709544 (l : int) : (term195 l) = (term212 l).
Proof. exact (MK_COMB (@lem5709542) (@lem5709543 l)). Qed.
Lemma lem5709545 (l : int) : (term194 l) = (term212 l).
Proof. exact (TRANS (@lem5709442 l) (@lem5709544 l)). Qed.
Lemma lem5709546 (l : int) : (term212 l) = term81.
Proof. exact (@lem1982719 (real_of_int l)). Qed.
Lemma lem5709547 (l : int) : (term194 l) = term81.
Proof. exact (TRANS (@lem5709545 l) (@lem5709546 l)). Qed.
Lemma lem5709548 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5709549 (l : int) : (term213 l) = term145.
Proof. exact (MK_COMB (@lem5709548) (@lem5709547 l)). Qed.
Lemma lem5709554 (r : int) (x : int) : (term144 x r) = (term561 r x).
Proof. exact (@lem1982757 (term93 r) (real_of_int x) term103). Qed.
Lemma lem5709555 (l : int) (r : int) (x : int) : (term897 l x r) = (term898 r x).
Proof. exact (MK_COMB (@lem5709549 l) (@lem5709554 r x)). Qed.
Lemma lem5709556 (l : int) (r : int) (x : int) : (term896 x l r) = (term898 r x).
Proof. exact (TRANS (@lem5709441 l x r) (@lem5709555 l r x)). Qed.
Lemma lem5709557 (r : int) (x : int) : (term898 r x) = (term561 r x).
Proof. exact (@lem1982721 (term561 r x)). Qed.
Lemma lem5709558 (l : int) (r : int) (x : int) : (term896 x l r) = (term561 r x).
Proof. exact (TRANS (@lem5709556 l r x) (@lem5709557 r x)). Qed.
Lemma lem5709559 (l : int) (r : int) (x : int) : (term895 x l r) = (term561 r x).
Proof. exact (TRANS (@lem5709440 x l r) (@lem5709558 l r x)). Qed.
Lemma lem5709560 (l : int) (r : int) (x : int) : (term894 x l r) = (term561 r x).
Proof. exact (TRANS (@lem5709347 x l r) (@lem5709559 l r x)). Qed.
Lemma lem5709561 (l : int) (r : int) (x : int) : (term893 x r l) = (term561 r x).
Proof. exact (TRANS (@lem5709346 x l r) (@lem5709560 l r x)). Qed.
Lemma lem5709562 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5709563 (l : int) (r : int) (x : int) : (term899 x r l) = (term562 r x).
Proof. exact (MK_COMB (@lem5709562) (@lem5709561 l r x)). Qed.
Lemma lem5709564 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem5709565 (l : int) (r : int) (x : int) : (term892 x r l) = (term563 r x).
Proof. exact (MK_COMB (@lem5709563 l r x) (@lem5709564)). Qed.
Lemma lem5709566 (l : int) (r : int) (x : int) : (term854 r x l) = (term563 r x).
Proof. exact (TRANS (@lem5709307 x r l) (@lem5709565 l r x)). Qed.
Lemma lem5709567 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5709568 (l : int) (x : int) : (term856 l x) = term900.
Proof. exact (MK_COMB (@lem5709567) (@lem5709306 l x)). Qed.
Lemma lem5709569 (l : int) (r : int) (x : int) : (term857 r x l) = (term901 r x).
Proof. exact (MK_COMB (@lem5709568 l x) (@lem5709566 l r x)). Qed.
Lemma lem5709570 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5709571 (r : int) (x : int) : (term84 x r) = (term902 r x).
Proof. exact (MK_COMB (@lem5709570) (@lem5708681 r x)). Qed.
Lemma lem5709572 (l : int) (r : int) (x : int) : (term858 r x l) = (term903 r x).
Proof. exact (MK_COMB (@lem5709571 r x) (@lem5709569 l r x)). Qed.
Lemma lem5709573 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5709574 (l : int) (x : int) : (term84 l x) = (term156 l x).
Proof. exact (MK_COMB (@lem5709573) (@lem5708662 l x)). Qed.
Lemma lem5709575 (l : int) (r : int) (x : int) : (term859 r x l) = (term904 l r x).
Proof. exact (MK_COMB (@lem5709574 l x) (@lem5709572 l r x)). Qed.
Lemma lem5709576 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5709577 (l : int) (r : int) : (term860 r l) = (term156 l r).
Proof. exact (MK_COMB (@lem5709576) (@lem5708643 l r)). Qed.
Lemma lem5709578 (l : int) (r : int) (x : int) : (term861 r x l) = (term905 l r x).
Proof. exact (MK_COMB (@lem5709577 l r) (@lem5709575 l r x)). Qed.
Lemma lem5709585 (l : int) (r : int) (x : int) : (term862 r x l) = (term905 l r x).
Proof. exact (TRANS (@lem5708583 r x l) (@lem5709578 l r x)). Qed.
Lemma lem5709599 (r : int) (x : int) : (term903 r x) = (term906 r x).
Proof. exact (@lem19158 term891 (term155 r x) (term563 r x)). Qed.
Lemma lem5709600 (r : int) (x : int) : (term666 r x) = (term666 r x).
Proof. exact (eq_refl (term666 r x)). Qed.
Lemma lem5709607 (r : int) (x : int) : (term907 r x) = (term908 r x).
Proof. exact (@lem19158 term234 (term155 r x) term234). Qed.
Lemma lem5709608 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5709609 (r : int) (x : int) : (term909 r x) = (term910 r x).
Proof. exact (MK_COMB (@lem5709608) (@lem5709607 r x)). Qed.
Lemma lem5709610 (r : int) (x : int) : (term906 r x) = (term911 r x).
Proof. exact (MK_COMB (@lem5709609 r x) (@lem5709600 r x)). Qed.
Lemma lem5709612 (r : int) (x : int) : (term903 r x) = (term911 r x).
Proof. exact (TRANS (@lem5709599 r x) (@lem5709610 r x)). Qed.
Lemma lem5709615 (l : int) (x : int) : (term156 l x) = (term156 l x).
Proof. exact (eq_refl (term156 l x)). Qed.
Lemma lem5709616 (l : int) (r : int) (x : int) : (term904 l r x) = (term912 l r x).
Proof. exact (MK_COMB (@lem5709615 l x) (@lem5709612 r x)). Qed.
Lemma lem5709617 (l : int) (r : int) (x : int) : (term912 l r x) = (term913 l r x).
Proof. exact (@lem19158 (term908 r x) (term153 l x) (term666 r x)). Qed.
Lemma lem5709618 (l : int) (r : int) (x : int) : (term914 l r x) = (term914 l r x).
Proof. exact (eq_refl (term914 l r x)). Qed.
Lemma lem5709625 (l : int) (r : int) (x : int) : (term915 l r x) = (term916 l r x).
Proof. exact (@lem19158 (term917 r x) (term153 l x) (term917 r x)). Qed.
Lemma lem5709626 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5709627 (l : int) (r : int) (x : int) : (term918 l r x) = (term919 l r x).
Proof. exact (MK_COMB (@lem5709626) (@lem5709625 l r x)). Qed.
Lemma lem5709628 (l : int) (r : int) (x : int) : (term913 l r x) = (term920 l r x).
Proof. exact (MK_COMB (@lem5709627 l r x) (@lem5709618 l r x)). Qed.
Lemma lem5709629 (l : int) (r : int) (x : int) : (term912 l r x) = (term920 l r x).
Proof. exact (TRANS (@lem5709617 l r x) (@lem5709628 l r x)). Qed.
Lemma lem5709630 (l : int) (r : int) (x : int) : (term904 l r x) = (term920 l r x).
Proof. exact (TRANS (@lem5709616 l r x) (@lem5709629 l r x)). Qed.
Lemma lem5709633 (l : int) (r : int) : (term156 l r) = (term156 l r).
Proof. exact (eq_refl (term156 l r)). Qed.
Lemma lem5709634 (l : int) (r : int) (x : int) : (term905 l r x) = (term921 l r x).
Proof. exact (MK_COMB (@lem5709633 l r) (@lem5709630 l r x)). Qed.
Lemma lem5709635 (l : int) (r : int) (x : int) : (term921 l r x) = (term922 l r x).
Proof. exact (@lem19158 (term916 l r x) (term153 l r) (term914 l r x)). Qed.
Lemma lem5709636 (l : int) (r : int) (x : int) : (term923 l r x) = (term923 l r x).
Proof. exact (eq_refl (term923 l r x)). Qed.
Lemma lem5709643 (l : int) (r : int) (x : int) : (term924 l r x) = (term925 l r x).
Proof. exact (@lem19158 (term926 l r x) (term153 l r) (term926 l r x)). Qed.
Lemma lem5709644 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5709645 (l : int) (r : int) (x : int) : (term927 l r x) = (term928 l r x).
Proof. exact (MK_COMB (@lem5709644) (@lem5709643 l r x)). Qed.
Lemma lem5709646 (l : int) (r : int) (x : int) : (term922 l r x) = (term929 l r x).
Proof. exact (MK_COMB (@lem5709645 l r x) (@lem5709636 l r x)). Qed.
Lemma lem5709647 (l : int) (r : int) (x : int) : (term921 l r x) = (term929 l r x).
Proof. exact (TRANS (@lem5709635 l r x) (@lem5709646 l r x)). Qed.
Lemma lem5709648 (l : int) (r : int) (x : int) : (term905 l r x) = (term929 l r x).
Proof. exact (TRANS (@lem5709634 l r x) (@lem5709647 l r x)). Qed.
Lemma lem5709649 (l : int) (r : int) (x : int) : (term862 r x l) = (term929 l r x).
Proof. exact (TRANS (@lem5709585 l r x) (@lem5709648 l r x)). Qed.
Lemma lem5709665 (l : int) (r : int) (x : int) (h1 : term929 l r x) : term929 l r x.
Proof. exact (h1). Qed.
Lemma lem5709666 (l : int) (r : int) (x : int) (h1 : term925 l r x) : term925 l r x.
Proof. exact (h1). Qed.
Lemma lem5709667 (l : int) (r : int) (x : int) (h1 : term930 l r x) : term930 l r x.
Proof. exact (h1). Qed.
Lemma lem5709668 (l : int) (r : int) (x : int) (h1 : term930 l r x) : term926 l r x.
Proof. exact (proj2 (@lem5709667 l r x h1)). Qed.
Lemma lem5709670 (l : int) (r : int) (x : int) (h1 : term930 l r x) : term917 r x.
Proof. exact (proj2 (@lem5709668 l r x h1)). Qed.
Lemma lem5709672 (l : int) (r : int) (x : int) (h1 : term930 l r x) : term234.
Proof. exact (proj2 (@lem5709670 l r x h1)). Qed.
Lemma lem5709675 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5709676 : term234 = term235.
Proof. exact (@lem5709675 term81 term103). Qed.
Lemma lem5709678 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5709679 : term103 = term111.
Proof. exact (@lem5709678 term76). Qed.
Lemma lem5709681 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5709682 : term81 = term162.
Proof. exact (@lem5709681 (NUMERAL 0)). Qed.
Lemma lem5709683 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5709684 : term236 = term237.
Proof. exact (MK_COMB (@lem5709683) (@lem5709682)). Qed.
Lemma lem5709685 : term235 = term238.
Proof. exact (MK_COMB (@lem5709684) (@lem5709679)). Qed.
Lemma lem5709686 : term239.
Proof. exact (@lem1980026 term81 term75 term103 term75). Qed.
Lemma lem5709688 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5709689 : term161 = term168.
Proof. exact (@lem5709688 (NUMERAL 0) term76). Qed.
Lemma lem5709690 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5709691 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5709692 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5709691 h1) (fun h1 : term168 = True => @lem5709690)). Qed.
Lemma lem5709693 : term168 = True.
Proof. exact (EQ_MP (@lem5709692) (@lem5709690)). Qed.
Lemma lem5709694 : term161 = True.
Proof. exact (TRANS (@lem5709689) (@lem5709693)). Qed.
Lemma lem5709695 : True = term161.
Proof. exact (SYM (@lem5709694)). Qed.
Lemma lem5709696 : term161.
Proof. exact (EQ_MP (@lem5709695) (@lem0)). Qed.
Lemma lem5709697 : term240.
Proof. exact (@lem5709686 (@lem5709696)). Qed.
Lemma lem5709699 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5709700 : term161 = term168.
Proof. exact (@lem5709699 (NUMERAL 0) term76). Qed.
Lemma lem5709701 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5709702 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5709703 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5709702 h1) (fun h1 : term168 = True => @lem5709701)). Qed.
Lemma lem5709704 : term168 = True.
Proof. exact (EQ_MP (@lem5709703) (@lem5709701)). Qed.
Lemma lem5709705 : term161 = True.
Proof. exact (TRANS (@lem5709700) (@lem5709704)). Qed.
Lemma lem5709706 : True = term161.
Proof. exact (SYM (@lem5709705)). Qed.
Lemma lem5709707 : term161.
Proof. exact (EQ_MP (@lem5709706) (@lem0)). Qed.
Lemma lem5709708 : term238 = term241.
Proof. exact (@lem5709697 (@lem5709707)). Qed.
Lemma lem5709710 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5709711 : term114 = term125.
Proof. exact (@lem5709710 term76 term76). Qed.
Lemma lem5709712 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5709713 : term122 = term76.
Proof. exact (EQ_MP (@lem5709712) (@lem940073)). Qed.
Lemma lem5709714 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5709715 : term120 = term75.
Proof. exact (MK_COMB (@lem5709714) (@lem5709713)). Qed.
Lemma lem5709716 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5709717 : term125 = term103.
Proof. exact (MK_COMB (@lem5709716) (@lem5709715)). Qed.
Lemma lem5709718 : term114 = term103.
Proof. exact (TRANS (@lem5709711) (@lem5709717)). Qed.
Lemma lem5709720 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5709721 : term173 = term81.
Proof. exact (@lem5709720 term76). Qed.
Lemma lem5709722 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5709723 : term242 = term236.
Proof. exact (MK_COMB (@lem5709722) (@lem5709721)). Qed.
Lemma lem5709724 : term241 = term235.
Proof. exact (MK_COMB (@lem5709723) (@lem5709718)). Qed.
Lemma lem5709726 (m : nat) (n : nat) : (term243 m n) = (term244 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5709727 : term235 = term245.
Proof. exact (@lem5709726 (NUMERAL 0) term76). Qed.
Lemma lem5709728 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5709729 (h1 : term169 = (BIT1 0)) : (term76 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5709730 : (term169 = (BIT1 0)) = ((term76 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5709729 h1) (fun h1 : (term76 = (NUMERAL 0)) = False => @lem5709728)). Qed.
Lemma lem5709731 : (term76 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5709730) (@lem5709728)). Qed.
Lemma lem5709732 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5709733 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5709734 : term246 = (and True).
Proof. exact (MK_COMB (@lem5709733) (@lem5709732)). Qed.
Lemma lem5709735 : term245 = (True /\ False).
Proof. exact (MK_COMB (@lem5709734) (@lem5709731)). Qed.
Lemma lem5709737 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5709738 : term245 = False.
Proof. exact (TRANS (@lem5709735) (@lem5709737)). Qed.
Lemma lem5709739 : term235 = False.
Proof. exact (TRANS (@lem5709727) (@lem5709738)). Qed.
Lemma lem5709740 : term241 = False.
Proof. exact (TRANS (@lem5709724) (@lem5709739)). Qed.
Lemma lem5709741 : term238 = False.
Proof. exact (TRANS (@lem5709708) (@lem5709740)). Qed.
Lemma lem5709742 : term235 = False.
Proof. exact (TRANS (@lem5709685) (@lem5709741)). Qed.
Lemma lem5709743 : term234 = False.
Proof. exact (TRANS (@lem5709676) (@lem5709742)). Qed.
Lemma lem5709744 (l : int) (r : int) (x : int) (h1 : term930 l r x) : False.
Proof. exact (EQ_MP (@lem5709743) (@lem5709672 l r x h1)). Qed.
Lemma lem5709745 (l : int) (r : int) (x : int) (h1 : term930 l r x) : term930 l r x.
Proof. exact (h1). Qed.
Lemma lem5709746 (l : int) (r : int) (x : int) (h1 : term930 l r x) : term926 l r x.
Proof. exact (proj2 (@lem5709745 l r x h1)). Qed.
Lemma lem5709748 (l : int) (r : int) (x : int) (h1 : term930 l r x) : term917 r x.
Proof. exact (proj2 (@lem5709746 l r x h1)). Qed.
Lemma lem5709750 (l : int) (r : int) (x : int) (h1 : term930 l r x) : term234.
Proof. exact (proj2 (@lem5709748 l r x h1)). Qed.
Lemma lem5709753 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5709754 : term234 = term235.
Proof. exact (@lem5709753 term81 term103). Qed.
Lemma lem5709756 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5709757 : term103 = term111.
Proof. exact (@lem5709756 term76). Qed.
Lemma lem5709759 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5709760 : term81 = term162.
Proof. exact (@lem5709759 (NUMERAL 0)). Qed.
Lemma lem5709761 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5709762 : term236 = term237.
Proof. exact (MK_COMB (@lem5709761) (@lem5709760)). Qed.
Lemma lem5709763 : term235 = term238.
Proof. exact (MK_COMB (@lem5709762) (@lem5709757)). Qed.
Lemma lem5709764 : term239.
Proof. exact (@lem1980026 term81 term75 term103 term75). Qed.
Lemma lem5709766 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5709767 : term161 = term168.
Proof. exact (@lem5709766 (NUMERAL 0) term76). Qed.
Lemma lem5709768 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5709769 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5709770 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5709769 h1) (fun h1 : term168 = True => @lem5709768)). Qed.
Lemma lem5709771 : term168 = True.
Proof. exact (EQ_MP (@lem5709770) (@lem5709768)). Qed.
Lemma lem5709772 : term161 = True.
Proof. exact (TRANS (@lem5709767) (@lem5709771)). Qed.
Lemma lem5709773 : True = term161.
Proof. exact (SYM (@lem5709772)). Qed.
Lemma lem5709774 : term161.
Proof. exact (EQ_MP (@lem5709773) (@lem0)). Qed.
Lemma lem5709775 : term240.
Proof. exact (@lem5709764 (@lem5709774)). Qed.
Lemma lem5709777 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5709778 : term161 = term168.
Proof. exact (@lem5709777 (NUMERAL 0) term76). Qed.
Lemma lem5709779 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5709780 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5709781 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5709780 h1) (fun h1 : term168 = True => @lem5709779)). Qed.
Lemma lem5709782 : term168 = True.
Proof. exact (EQ_MP (@lem5709781) (@lem5709779)). Qed.
Lemma lem5709783 : term161 = True.
Proof. exact (TRANS (@lem5709778) (@lem5709782)). Qed.
Lemma lem5709784 : True = term161.
Proof. exact (SYM (@lem5709783)). Qed.
Lemma lem5709785 : term161.
Proof. exact (EQ_MP (@lem5709784) (@lem0)). Qed.
Lemma lem5709786 : term238 = term241.
Proof. exact (@lem5709775 (@lem5709785)). Qed.
Lemma lem5709788 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5709789 : term114 = term125.
Proof. exact (@lem5709788 term76 term76). Qed.
Lemma lem5709790 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5709791 : term122 = term76.
Proof. exact (EQ_MP (@lem5709790) (@lem940073)). Qed.
Lemma lem5709792 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5709793 : term120 = term75.
Proof. exact (MK_COMB (@lem5709792) (@lem5709791)). Qed.
Lemma lem5709794 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5709795 : term125 = term103.
Proof. exact (MK_COMB (@lem5709794) (@lem5709793)). Qed.
Lemma lem5709796 : term114 = term103.
Proof. exact (TRANS (@lem5709789) (@lem5709795)). Qed.
Lemma lem5709798 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5709799 : term173 = term81.
Proof. exact (@lem5709798 term76). Qed.
Lemma lem5709800 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5709801 : term242 = term236.
Proof. exact (MK_COMB (@lem5709800) (@lem5709799)). Qed.
Lemma lem5709802 : term241 = term235.
Proof. exact (MK_COMB (@lem5709801) (@lem5709796)). Qed.
Lemma lem5709804 (m : nat) (n : nat) : (term243 m n) = (term244 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5709805 : term235 = term245.
Proof. exact (@lem5709804 (NUMERAL 0) term76). Qed.
Lemma lem5709806 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5709807 (h1 : term169 = (BIT1 0)) : (term76 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5709808 : (term169 = (BIT1 0)) = ((term76 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5709807 h1) (fun h1 : (term76 = (NUMERAL 0)) = False => @lem5709806)). Qed.
Lemma lem5709809 : (term76 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5709808) (@lem5709806)). Qed.
Lemma lem5709810 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5709811 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5709812 : term246 = (and True).
Proof. exact (MK_COMB (@lem5709811) (@lem5709810)). Qed.
Lemma lem5709813 : term245 = (True /\ False).
Proof. exact (MK_COMB (@lem5709812) (@lem5709809)). Qed.
Lemma lem5709815 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5709816 : term245 = False.
Proof. exact (TRANS (@lem5709813) (@lem5709815)). Qed.
Lemma lem5709817 : term235 = False.
Proof. exact (TRANS (@lem5709805) (@lem5709816)). Qed.
Lemma lem5709818 : term241 = False.
Proof. exact (TRANS (@lem5709802) (@lem5709817)). Qed.
Lemma lem5709819 : term238 = False.
Proof. exact (TRANS (@lem5709786) (@lem5709818)). Qed.
Lemma lem5709820 : term235 = False.
Proof. exact (TRANS (@lem5709763) (@lem5709819)). Qed.
Lemma lem5709821 : term234 = False.
Proof. exact (TRANS (@lem5709754) (@lem5709820)). Qed.
Lemma lem5709822 (l : int) (r : int) (x : int) (h1 : term930 l r x) : False.
Proof. exact (EQ_MP (@lem5709821) (@lem5709750 l r x h1)). Qed.
Lemma lem5709823 (l : int) (r : int) (x : int) (h1 : term925 l r x) : False.
Proof. exact (or_elim (@lem5709666 l r x h1) (fun h0 : term930 l r x => @lem5709744 l r x h0) (fun h0 : term930 l r x => @lem5709822 l r x h0)). Qed.
Lemma lem5709824 (l : int) (r : int) (x : int) (h1 : term923 l r x) : term923 l r x.
Proof. exact (h1). Qed.
Lemma lem5709825 (l : int) (r : int) (x : int) (h1 : term923 l r x) : term914 l r x.
Proof. exact (proj2 (@lem5709824 l r x h1)). Qed.
Lemma lem5709827 (l : int) (r : int) (x : int) (h1 : term923 l r x) : term666 r x.
Proof. exact (proj2 (@lem5709825 l r x h1)). Qed.
Lemma lem5709829 (l : int) (r : int) (x : int) (h1 : term923 l r x) : term563 r x.
Proof. exact (proj2 (@lem5709827 l r x h1)). Qed.
Lemma lem5709830 (l : int) (r : int) (x : int) (h1 : term923 l r x) : term155 r x.
Proof. exact (proj1 (@lem5709827 l r x h1)). Qed.
Lemma lem5709832 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5709833 : term160 = term161.
Proof. exact (@lem5709832 term81 term75). Qed.
Lemma lem5709835 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5709836 : term75 = term108.
Proof. exact (@lem5709835 term76). Qed.
Lemma lem5709838 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5709839 : term81 = term162.
Proof. exact (@lem5709838 (NUMERAL 0)). Qed.
Lemma lem5709840 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5709841 : term163 = term164.
Proof. exact (MK_COMB (@lem5709840) (@lem5709839)). Qed.
Lemma lem5709842 : term161 = term165.
Proof. exact (MK_COMB (@lem5709841) (@lem5709836)). Qed.
Lemma lem5709843 : term166.
Proof. exact (@lem1980255 term81 term75 term75 term75). Qed.
Lemma lem5709845 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5709846 : term161 = term168.
Proof. exact (@lem5709845 (NUMERAL 0) term76). Qed.
Lemma lem5709847 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5709848 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5709849 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5709848 h1) (fun h1 : term168 = True => @lem5709847)). Qed.
Lemma lem5709850 : term168 = True.
Proof. exact (EQ_MP (@lem5709849) (@lem5709847)). Qed.
Lemma lem5709851 : term161 = True.
Proof. exact (TRANS (@lem5709846) (@lem5709850)). Qed.
Lemma lem5709852 : True = term161.
Proof. exact (SYM (@lem5709851)). Qed.
Lemma lem5709853 : term161.
Proof. exact (EQ_MP (@lem5709852) (@lem0)). Qed.
Lemma lem5709854 : term170.
Proof. exact (@lem5709843 (@lem5709853)). Qed.
Lemma lem5709856 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5709857 : term161 = term168.
Proof. exact (@lem5709856 (NUMERAL 0) term76). Qed.
Lemma lem5709858 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5709859 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5709860 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5709859 h1) (fun h1 : term168 = True => @lem5709858)). Qed.
Lemma lem5709861 : term168 = True.
Proof. exact (EQ_MP (@lem5709860) (@lem5709858)). Qed.
Lemma lem5709862 : term161 = True.
Proof. exact (TRANS (@lem5709857) (@lem5709861)). Qed.
Lemma lem5709863 : True = term161.
Proof. exact (SYM (@lem5709862)). Qed.
Lemma lem5709864 : term161.
Proof. exact (EQ_MP (@lem5709863) (@lem0)). Qed.
Lemma lem5709865 : term165 = term171.
Proof. exact (@lem5709854 (@lem5709864)). Qed.
Lemma lem5709867 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5709868 : term119 = term120.
Proof. exact (@lem5709867 term76 term76). Qed.
Lemma lem5709869 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5709870 : term122 = term76.
Proof. exact (EQ_MP (@lem5709869) (@lem940073)). Qed.
Lemma lem5709871 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5709872 : term120 = term75.
Proof. exact (MK_COMB (@lem5709871) (@lem5709870)). Qed.
Lemma lem5709873 : term119 = term75.
Proof. exact (TRANS (@lem5709868) (@lem5709872)). Qed.
Lemma lem5709875 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5709876 : term173 = term81.
Proof. exact (@lem5709875 term76). Qed.
Lemma lem5709877 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5709878 : term174 = term163.
Proof. exact (MK_COMB (@lem5709877) (@lem5709876)). Qed.
Lemma lem5709879 : term171 = term161.
Proof. exact (MK_COMB (@lem5709878) (@lem5709873)). Qed.
Lemma lem5709881 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5709882 : term161 = term168.
Proof. exact (@lem5709881 (NUMERAL 0) term76). Qed.
Lemma lem5709883 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5709884 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5709885 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5709884 h1) (fun h1 : term168 = True => @lem5709883)). Qed.
Lemma lem5709886 : term168 = True.
Proof. exact (EQ_MP (@lem5709885) (@lem5709883)). Qed.
Lemma lem5709887 : term161 = True.
Proof. exact (TRANS (@lem5709882) (@lem5709886)). Qed.
Lemma lem5709888 : term171 = True.
Proof. exact (TRANS (@lem5709879) (@lem5709887)). Qed.
Lemma lem5709889 : term165 = True.
Proof. exact (TRANS (@lem5709865) (@lem5709888)). Qed.
Lemma lem5709890 : term161 = True.
Proof. exact (TRANS (@lem5709842) (@lem5709889)). Qed.
Lemma lem5709891 : term160 = True.
Proof. exact (TRANS (@lem5709833) (@lem5709890)). Qed.
Lemma lem5709892 : True = term160.
Proof. exact (SYM (@lem5709891)). Qed.
Lemma lem5709893 : term160.
Proof. exact (EQ_MP (@lem5709892) (@lem0)). Qed.
Lemma lem5709894 (l : int) (r : int) (x : int) (h1 : term923 l r x) : term175 r x.
Proof. exact (conj (@lem5709893) (@lem5709830 l r x h1)). Qed.
Lemma lem5709896 (x : real) (y : real) : term176 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5709897 (r : int) (x : int) : term177 r x.
Proof. exact (@lem5709896 term75 (term91 r x)). Qed.
Lemma lem5709898 (l : int) (r : int) (x : int) (h1 : term923 l r x) : term178 r x.
Proof. exact (@lem5709897 r x (@lem5709894 l r x h1)). Qed.
Lemma lem5709899 (r : int) (x : int) : (term179 r x) = (term91 r x).
Proof. exact (@lem1982733 (term91 r x)). Qed.
Lemma lem5709900 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5709901 (r : int) (x : int) : (term180 r x) = (term154 r x).
Proof. exact (MK_COMB (@lem5709900) (@lem5709899 r x)). Qed.
Lemma lem5709902 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem5709903 (r : int) (x : int) : (term178 r x) = (term155 r x).
Proof. exact (MK_COMB (@lem5709901 r x) (@lem5709902)). Qed.
Lemma lem5709904 (l : int) (r : int) (x : int) (h1 : term923 l r x) : term155 r x.
Proof. exact (EQ_MP (@lem5709903 r x) (@lem5709898 l r x h1)). Qed.
Lemma lem5709906 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5709907 : term160 = term161.
Proof. exact (@lem5709906 term81 term75). Qed.
Lemma lem5709909 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5709910 : term75 = term108.
Proof. exact (@lem5709909 term76). Qed.
Lemma lem5709912 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5709913 : term81 = term162.
Proof. exact (@lem5709912 (NUMERAL 0)). Qed.
Lemma lem5709914 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5709915 : term163 = term164.
Proof. exact (MK_COMB (@lem5709914) (@lem5709913)). Qed.
Lemma lem5709916 : term161 = term165.
Proof. exact (MK_COMB (@lem5709915) (@lem5709910)). Qed.
Lemma lem5709917 : term166.
Proof. exact (@lem1980255 term81 term75 term75 term75). Qed.
Lemma lem5709919 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5709920 : term161 = term168.
Proof. exact (@lem5709919 (NUMERAL 0) term76). Qed.
Lemma lem5709921 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5709922 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5709923 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5709922 h1) (fun h1 : term168 = True => @lem5709921)). Qed.
Lemma lem5709924 : term168 = True.
Proof. exact (EQ_MP (@lem5709923) (@lem5709921)). Qed.
Lemma lem5709925 : term161 = True.
Proof. exact (TRANS (@lem5709920) (@lem5709924)). Qed.
Lemma lem5709926 : True = term161.
Proof. exact (SYM (@lem5709925)). Qed.
Lemma lem5709927 : term161.
Proof. exact (EQ_MP (@lem5709926) (@lem0)). Qed.
Lemma lem5709928 : term170.
Proof. exact (@lem5709917 (@lem5709927)). Qed.
Lemma lem5709930 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5709931 : term161 = term168.
Proof. exact (@lem5709930 (NUMERAL 0) term76). Qed.
Lemma lem5709932 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5709933 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5709934 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5709933 h1) (fun h1 : term168 = True => @lem5709932)). Qed.
Lemma lem5709935 : term168 = True.
Proof. exact (EQ_MP (@lem5709934) (@lem5709932)). Qed.
Lemma lem5709936 : term161 = True.
Proof. exact (TRANS (@lem5709931) (@lem5709935)). Qed.
Lemma lem5709937 : True = term161.
Proof. exact (SYM (@lem5709936)). Qed.
Lemma lem5709938 : term161.
Proof. exact (EQ_MP (@lem5709937) (@lem0)). Qed.
Lemma lem5709939 : term165 = term171.
Proof. exact (@lem5709928 (@lem5709938)). Qed.
Lemma lem5709941 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5709942 : term119 = term120.
Proof. exact (@lem5709941 term76 term76). Qed.
Lemma lem5709943 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5709944 : term122 = term76.
Proof. exact (EQ_MP (@lem5709943) (@lem940073)). Qed.
Lemma lem5709945 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5709946 : term120 = term75.
Proof. exact (MK_COMB (@lem5709945) (@lem5709944)). Qed.
Lemma lem5709947 : term119 = term75.
Proof. exact (TRANS (@lem5709942) (@lem5709946)). Qed.
Lemma lem5709949 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5709950 : term173 = term81.
Proof. exact (@lem5709949 term76). Qed.
Lemma lem5709951 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5709952 : term174 = term163.
Proof. exact (MK_COMB (@lem5709951) (@lem5709950)). Qed.
Lemma lem5709953 : term171 = term161.
Proof. exact (MK_COMB (@lem5709952) (@lem5709947)). Qed.
Lemma lem5709955 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5709956 : term161 = term168.
Proof. exact (@lem5709955 (NUMERAL 0) term76). Qed.
Lemma lem5709957 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5709958 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5709959 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5709958 h1) (fun h1 : term168 = True => @lem5709957)). Qed.
Lemma lem5709960 : term168 = True.
Proof. exact (EQ_MP (@lem5709959) (@lem5709957)). Qed.
Lemma lem5709961 : term161 = True.
Proof. exact (TRANS (@lem5709956) (@lem5709960)). Qed.
Lemma lem5709962 : term171 = True.
Proof. exact (TRANS (@lem5709953) (@lem5709961)). Qed.
Lemma lem5709963 : term165 = True.
Proof. exact (TRANS (@lem5709939) (@lem5709962)). Qed.
Lemma lem5709964 : term161 = True.
Proof. exact (TRANS (@lem5709916) (@lem5709963)). Qed.
Lemma lem5709965 : term160 = True.
Proof. exact (TRANS (@lem5709907) (@lem5709964)). Qed.
Lemma lem5709966 : True = term160.
Proof. exact (SYM (@lem5709965)). Qed.
Lemma lem5709967 : term160.
Proof. exact (EQ_MP (@lem5709966) (@lem0)). Qed.
Lemma lem5709968 (l : int) (r : int) (x : int) (h1 : term923 l r x) : term583 r x.
Proof. exact (conj (@lem5709967) (@lem5709829 l r x h1)). Qed.
Lemma lem5709970 (x : real) (y : real) : term176 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5709971 (r : int) (x : int) : term584 r x.
Proof. exact (@lem5709970 term75 (term561 r x)). Qed.
Lemma lem5709972 (l : int) (r : int) (x : int) (h1 : term923 l r x) : term585 r x.
Proof. exact (@lem5709971 r x (@lem5709968 l r x h1)). Qed.
Lemma lem5709973 (r : int) (x : int) : (term586 r x) = (term561 r x).
Proof. exact (@lem1982733 (term561 r x)). Qed.
Lemma lem5709974 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5709975 (r : int) (x : int) : (term587 r x) = (term562 r x).
Proof. exact (MK_COMB (@lem5709974) (@lem5709973 r x)). Qed.
Lemma lem5709976 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem5709977 (r : int) (x : int) : (term585 r x) = (term563 r x).
Proof. exact (MK_COMB (@lem5709975 r x) (@lem5709976)). Qed.
Lemma lem5709978 (l : int) (r : int) (x : int) (h1 : term923 l r x) : term563 r x.
Proof. exact (EQ_MP (@lem5709977 r x) (@lem5709972 l r x h1)). Qed.
Lemma lem5709979 (l : int) (r : int) (x : int) (h1 : term923 l r x) : term931 r x.
Proof. exact (conj (@lem5709978 l r x h1) (@lem5709904 l r x h1)). Qed.
Lemma lem5709981 (x : real) (y : real) : term187 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5709982 (r : int) (x : int) : term932 r x.
Proof. exact (@lem5709981 (term561 r x) (term91 r x)). Qed.
Lemma lem5709983 (l : int) (r : int) (x : int) (h1 : term923 l r x) : term933 r x.
Proof. exact (@lem5709982 r x (@lem5709979 l r x h1)). Qed.
Lemma lem5709984 (r : int) (x : int) : (term934 r x) = (term935 r x).
Proof. exact (@lem1982753 (term93 r) (real_of_int r) (term593 x) (term93 x)). Qed.
Lemma lem5709985 (r : int) : (term194 r) = (term195 r).
Proof. exact (@lem1982713 term103 (real_of_int r)). Qed.
Lemma lem5709987 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5709988 : term75 = term108.
Proof. exact (@lem5709987 term76). Qed.
Lemma lem5709990 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5709991 : term103 = term111.
Proof. exact (@lem5709990 term76). Qed.
Lemma lem5709992 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5709993 : term196 = term197.
Proof. exact (MK_COMB (@lem5709992) (@lem5709991)). Qed.
Lemma lem5709994 : term198 = term199.
Proof. exact (MK_COMB (@lem5709993) (@lem5709988)). Qed.
Lemma lem5709995 : term200.
Proof. exact (@lem1981473 term103 term75 term75 term75 term81 term75). Qed.
Lemma lem5709997 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5709998 : term161 = term168.
Proof. exact (@lem5709997 (NUMERAL 0) term76). Qed.
Lemma lem5709999 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5710000 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5710001 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5710000 h1) (fun h1 : term168 = True => @lem5709999)). Qed.
Lemma lem5710002 : term168 = True.
Proof. exact (EQ_MP (@lem5710001) (@lem5709999)). Qed.
Lemma lem5710003 : term161 = True.
Proof. exact (TRANS (@lem5709998) (@lem5710002)). Qed.
Lemma lem5710004 : True = term161.
Proof. exact (SYM (@lem5710003)). Qed.
Lemma lem5710005 : term161.
Proof. exact (EQ_MP (@lem5710004) (@lem0)). Qed.
Lemma lem5710006 : term201.
Proof. exact (@lem5709995 (@lem5710005)). Qed.
Lemma lem5710008 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5710009 : term161 = term168.
Proof. exact (@lem5710008 (NUMERAL 0) term76). Qed.
Lemma lem5710010 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5710011 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5710012 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5710011 h1) (fun h1 : term168 = True => @lem5710010)). Qed.
Lemma lem5710013 : term168 = True.
Proof. exact (EQ_MP (@lem5710012) (@lem5710010)). Qed.
Lemma lem5710014 : term161 = True.
Proof. exact (TRANS (@lem5710009) (@lem5710013)). Qed.
Lemma lem5710015 : True = term161.
Proof. exact (SYM (@lem5710014)). Qed.
Lemma lem5710016 : term161.
Proof. exact (EQ_MP (@lem5710015) (@lem0)). Qed.
Lemma lem5710017 : term202.
Proof. exact (@lem5710006 (@lem5710016)). Qed.
Lemma lem5710019 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5710020 : term161 = term168.
Proof. exact (@lem5710019 (NUMERAL 0) term76). Qed.
Lemma lem5710021 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5710022 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5710023 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5710022 h1) (fun h1 : term168 = True => @lem5710021)). Qed.
Lemma lem5710024 : term168 = True.
Proof. exact (EQ_MP (@lem5710023) (@lem5710021)). Qed.
Lemma lem5710025 : term161 = True.
Proof. exact (TRANS (@lem5710020) (@lem5710024)). Qed.
Lemma lem5710026 : True = term161.
Proof. exact (SYM (@lem5710025)). Qed.
Lemma lem5710027 : term161.
Proof. exact (EQ_MP (@lem5710026) (@lem0)). Qed.
Lemma lem5710028 : term203.
Proof. exact (@lem5710017 (@lem5710027)). Qed.
Lemma lem5710030 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5710031 : term119 = term120.
Proof. exact (@lem5710030 term76 term76). Qed.
Lemma lem5710032 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5710033 : term122 = term76.
Proof. exact (EQ_MP (@lem5710032) (@lem940073)). Qed.
Lemma lem5710034 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5710035 : term120 = term75.
Proof. exact (MK_COMB (@lem5710034) (@lem5710033)). Qed.
Lemma lem5710036 : term119 = term75.
Proof. exact (TRANS (@lem5710031) (@lem5710035)). Qed.
Lemma lem5710038 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5710039 : term114 = term125.
Proof. exact (@lem5710038 term76 term76). Qed.
Lemma lem5710040 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5710041 : term122 = term76.
Proof. exact (EQ_MP (@lem5710040) (@lem940073)). Qed.
Lemma lem5710042 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5710043 : term120 = term75.
Proof. exact (MK_COMB (@lem5710042) (@lem5710041)). Qed.
Lemma lem5710044 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5710045 : term125 = term103.
Proof. exact (MK_COMB (@lem5710044) (@lem5710043)). Qed.
Lemma lem5710046 : term114 = term103.
Proof. exact (TRANS (@lem5710039) (@lem5710045)). Qed.
Lemma lem5710047 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5710048 : term204 = term196.
Proof. exact (MK_COMB (@lem5710047) (@lem5710046)). Qed.
Lemma lem5710049 : term205 = term198.
Proof. exact (MK_COMB (@lem5710048) (@lem5710036)). Qed.
Lemma lem5710051 (m : nat) : (term206 m) = term81.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5710052 : term198 = term81.
Proof. exact (@lem5710051 term76). Qed.
Lemma lem5710053 : term205 = term81.
Proof. exact (TRANS (@lem5710049) (@lem5710052)). Qed.
Lemma lem5710054 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5710055 : term207 = term208.
Proof. exact (MK_COMB (@lem5710054) (@lem5710053)). Qed.
Lemma lem5710056 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem5710057 : term209 = term173.
Proof. exact (MK_COMB (@lem5710055) (@lem5710056)). Qed.
Lemma lem5710059 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5710060 : term173 = term81.
Proof. exact (@lem5710059 term76). Qed.
Lemma lem5710061 : term209 = term81.
Proof. exact (TRANS (@lem5710057) (@lem5710060)). Qed.
Lemma lem5710063 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5710064 : term119 = term120.
Proof. exact (@lem5710063 term76 term76). Qed.
Lemma lem5710065 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5710066 : term122 = term76.
Proof. exact (EQ_MP (@lem5710065) (@lem940073)). Qed.
Lemma lem5710067 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5710068 : term120 = term75.
Proof. exact (MK_COMB (@lem5710067) (@lem5710066)). Qed.
Lemma lem5710069 : term119 = term75.
Proof. exact (TRANS (@lem5710064) (@lem5710068)). Qed.
Lemma lem5710070 : term208 = term208.
Proof. exact (eq_refl term208). Qed.
Lemma lem5710071 : term210 = term173.
Proof. exact (MK_COMB (@lem5710070) (@lem5710069)). Qed.
Lemma lem5710073 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5710074 : term173 = term81.
Proof. exact (@lem5710073 term76). Qed.
Lemma lem5710075 : term210 = term81.
Proof. exact (TRANS (@lem5710071) (@lem5710074)). Qed.
Lemma lem5710076 : term81 = term210.
Proof. exact (SYM (@lem5710075)). Qed.
Lemma lem5710077 : term209 = term210.
Proof. exact (TRANS (@lem5710061) (@lem5710076)). Qed.
Lemma lem5710078 : term199 = term162.
Proof. exact (@lem5710028 (@lem5710077)). Qed.
Lemma lem5710079 : term198 = term162.
Proof. exact (TRANS (@lem5709994) (@lem5710078)). Qed.
Lemma lem5710081 (x : real) : (term128 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5710082 : term162 = term81.
Proof. exact (@lem5710081 term81). Qed.
Lemma lem5710083 : term198 = term81.
Proof. exact (TRANS (@lem5710079) (@lem5710082)). Qed.
Lemma lem5710084 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5710085 : term211 = term208.
Proof. exact (MK_COMB (@lem5710084) (@lem5710083)). Qed.
Lemma lem5710086 (r : int) : (real_of_int r) = (real_of_int r).
Proof. exact (eq_refl (real_of_int r)). Qed.
Lemma lem5710087 (r : int) : (term195 r) = (term212 r).
Proof. exact (MK_COMB (@lem5710085) (@lem5710086 r)). Qed.
Lemma lem5710088 (r : int) : (term194 r) = (term212 r).
Proof. exact (TRANS (@lem5709985 r) (@lem5710087 r)). Qed.
Lemma lem5710089 (r : int) : (term212 r) = term81.
Proof. exact (@lem1982719 (real_of_int r)). Qed.
Lemma lem5710090 (r : int) : (term194 r) = term81.
Proof. exact (TRANS (@lem5710088 r) (@lem5710089 r)). Qed.
Lemma lem5710091 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5710092 (r : int) : (term213 r) = term145.
Proof. exact (MK_COMB (@lem5710091) (@lem5710090 r)). Qed.
Lemma lem5710093 (x : int) : (term936 x) = (term228 x).
Proof. exact (@lem1982759 (real_of_int x) (term93 x) term103). Qed.
Lemma lem5710094 (x : int) : (term229 x) = (term195 x).
Proof. exact (@lem1982715 term103 (real_of_int x)). Qed.
Lemma lem5710096 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5710097 : term75 = term108.
Proof. exact (@lem5710096 term76). Qed.
Lemma lem5710099 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5710100 : term103 = term111.
Proof. exact (@lem5710099 term76). Qed.
Lemma lem5710101 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5710102 : term196 = term197.
Proof. exact (MK_COMB (@lem5710101) (@lem5710100)). Qed.
Lemma lem5710103 : term198 = term199.
Proof. exact (MK_COMB (@lem5710102) (@lem5710097)). Qed.
Lemma lem5710104 : term200.
Proof. exact (@lem1981473 term103 term75 term75 term75 term81 term75). Qed.
Lemma lem5710106 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5710107 : term161 = term168.
Proof. exact (@lem5710106 (NUMERAL 0) term76). Qed.
Lemma lem5710108 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5710109 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5710110 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5710109 h1) (fun h1 : term168 = True => @lem5710108)). Qed.
Lemma lem5710111 : term168 = True.
Proof. exact (EQ_MP (@lem5710110) (@lem5710108)). Qed.
Lemma lem5710112 : term161 = True.
Proof. exact (TRANS (@lem5710107) (@lem5710111)). Qed.
Lemma lem5710113 : True = term161.
Proof. exact (SYM (@lem5710112)). Qed.
Lemma lem5710114 : term161.
Proof. exact (EQ_MP (@lem5710113) (@lem0)). Qed.
Lemma lem5710115 : term201.
Proof. exact (@lem5710104 (@lem5710114)). Qed.
Lemma lem5710117 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5710118 : term161 = term168.
Proof. exact (@lem5710117 (NUMERAL 0) term76). Qed.
Lemma lem5710119 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5710120 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5710121 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5710120 h1) (fun h1 : term168 = True => @lem5710119)). Qed.
Lemma lem5710122 : term168 = True.
Proof. exact (EQ_MP (@lem5710121) (@lem5710119)). Qed.
Lemma lem5710123 : term161 = True.
Proof. exact (TRANS (@lem5710118) (@lem5710122)). Qed.
Lemma lem5710124 : True = term161.
Proof. exact (SYM (@lem5710123)). Qed.
Lemma lem5710125 : term161.
Proof. exact (EQ_MP (@lem5710124) (@lem0)). Qed.
Lemma lem5710126 : term202.
Proof. exact (@lem5710115 (@lem5710125)). Qed.
Lemma lem5710128 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5710129 : term161 = term168.
Proof. exact (@lem5710128 (NUMERAL 0) term76). Qed.
Lemma lem5710130 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5710131 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5710132 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5710131 h1) (fun h1 : term168 = True => @lem5710130)). Qed.
Lemma lem5710133 : term168 = True.
Proof. exact (EQ_MP (@lem5710132) (@lem5710130)). Qed.
Lemma lem5710134 : term161 = True.
Proof. exact (TRANS (@lem5710129) (@lem5710133)). Qed.
Lemma lem5710135 : True = term161.
Proof. exact (SYM (@lem5710134)). Qed.
Lemma lem5710136 : term161.
Proof. exact (EQ_MP (@lem5710135) (@lem0)). Qed.
Lemma lem5710137 : term203.
Proof. exact (@lem5710126 (@lem5710136)). Qed.
Lemma lem5710139 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5710140 : term119 = term120.
Proof. exact (@lem5710139 term76 term76). Qed.
Lemma lem5710141 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5710142 : term122 = term76.
Proof. exact (EQ_MP (@lem5710141) (@lem940073)). Qed.
Lemma lem5710143 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5710144 : term120 = term75.
Proof. exact (MK_COMB (@lem5710143) (@lem5710142)). Qed.
Lemma lem5710145 : term119 = term75.
Proof. exact (TRANS (@lem5710140) (@lem5710144)). Qed.
Lemma lem5710147 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5710148 : term114 = term125.
Proof. exact (@lem5710147 term76 term76). Qed.
Lemma lem5710149 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5710150 : term122 = term76.
Proof. exact (EQ_MP (@lem5710149) (@lem940073)). Qed.
Lemma lem5710151 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5710152 : term120 = term75.
Proof. exact (MK_COMB (@lem5710151) (@lem5710150)). Qed.
Lemma lem5710153 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5710154 : term125 = term103.
Proof. exact (MK_COMB (@lem5710153) (@lem5710152)). Qed.
Lemma lem5710155 : term114 = term103.
Proof. exact (TRANS (@lem5710148) (@lem5710154)). Qed.
Lemma lem5710156 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5710157 : term204 = term196.
Proof. exact (MK_COMB (@lem5710156) (@lem5710155)). Qed.
Lemma lem5710158 : term205 = term198.
Proof. exact (MK_COMB (@lem5710157) (@lem5710145)). Qed.
Lemma lem5710160 (m : nat) : (term206 m) = term81.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5710161 : term198 = term81.
Proof. exact (@lem5710160 term76). Qed.
Lemma lem5710162 : term205 = term81.
Proof. exact (TRANS (@lem5710158) (@lem5710161)). Qed.
Lemma lem5710163 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5710164 : term207 = term208.
Proof. exact (MK_COMB (@lem5710163) (@lem5710162)). Qed.
Lemma lem5710165 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem5710166 : term209 = term173.
Proof. exact (MK_COMB (@lem5710164) (@lem5710165)). Qed.
Lemma lem5710168 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5710169 : term173 = term81.
Proof. exact (@lem5710168 term76). Qed.
Lemma lem5710170 : term209 = term81.
Proof. exact (TRANS (@lem5710166) (@lem5710169)). Qed.
Lemma lem5710172 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5710173 : term119 = term120.
Proof. exact (@lem5710172 term76 term76). Qed.
Lemma lem5710174 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5710175 : term122 = term76.
Proof. exact (EQ_MP (@lem5710174) (@lem940073)). Qed.
Lemma lem5710176 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5710177 : term120 = term75.
Proof. exact (MK_COMB (@lem5710176) (@lem5710175)). Qed.
Lemma lem5710178 : term119 = term75.
Proof. exact (TRANS (@lem5710173) (@lem5710177)). Qed.
Lemma lem5710179 : term208 = term208.
Proof. exact (eq_refl term208). Qed.
Lemma lem5710180 : term210 = term173.
Proof. exact (MK_COMB (@lem5710179) (@lem5710178)). Qed.
Lemma lem5710182 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5710183 : term173 = term81.
Proof. exact (@lem5710182 term76). Qed.
Lemma lem5710184 : term210 = term81.
Proof. exact (TRANS (@lem5710180) (@lem5710183)). Qed.
Lemma lem5710185 : term81 = term210.
Proof. exact (SYM (@lem5710184)). Qed.
Lemma lem5710186 : term209 = term210.
Proof. exact (TRANS (@lem5710170) (@lem5710185)). Qed.
Lemma lem5710187 : term199 = term162.
Proof. exact (@lem5710137 (@lem5710186)). Qed.
Lemma lem5710188 : term198 = term162.
Proof. exact (TRANS (@lem5710103) (@lem5710187)). Qed.
Lemma lem5710190 (x : real) : (term128 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5710191 : term162 = term81.
Proof. exact (@lem5710190 term81). Qed.
Lemma lem5710192 : term198 = term81.
Proof. exact (TRANS (@lem5710188) (@lem5710191)). Qed.
Lemma lem5710193 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5710194 : term211 = term208.
Proof. exact (MK_COMB (@lem5710193) (@lem5710192)). Qed.
Lemma lem5710195 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem5710196 (x : int) : (term195 x) = (term212 x).
Proof. exact (MK_COMB (@lem5710194) (@lem5710195 x)). Qed.
Lemma lem5710197 (x : int) : (term229 x) = (term212 x).
Proof. exact (TRANS (@lem5710094 x) (@lem5710196 x)). Qed.
Lemma lem5710198 (x : int) : (term212 x) = term81.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem5710199 (x : int) : (term229 x) = term81.
Proof. exact (TRANS (@lem5710197 x) (@lem5710198 x)). Qed.
Lemma lem5710200 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5710201 (x : int) : (term230 x) = term145.
Proof. exact (MK_COMB (@lem5710200) (@lem5710199 x)). Qed.
Lemma lem5710202 : term103 = term103.
Proof. exact (eq_refl term103). Qed.
Lemma lem5710203 (x : int) : (term228 x) = term231.
Proof. exact (MK_COMB (@lem5710201 x) (@lem5710202)). Qed.
Lemma lem5710204 (x : int) : (term936 x) = term231.
Proof. exact (TRANS (@lem5710093 x) (@lem5710203 x)). Qed.
Lemma lem5710205 : term231 = term103.
Proof. exact (@lem1982721 term103). Qed.
Lemma lem5710206 (x : int) : (term936 x) = term103.
Proof. exact (TRANS (@lem5710204 x) (@lem5710205)). Qed.
Lemma lem5710207 (r : int) (x : int) : (term935 r x) = term231.
Proof. exact (MK_COMB (@lem5710092 r) (@lem5710206 x)). Qed.
Lemma lem5710208 (r : int) (x : int) : (term934 r x) = term231.
Proof. exact (TRANS (@lem5709984 r x) (@lem5710207 r x)). Qed.
Lemma lem5710209 : term231 = term103.
Proof. exact (@lem1982721 term103). Qed.
Lemma lem5710210 (r : int) (x : int) : (term934 r x) = term103.
Proof. exact (TRANS (@lem5710208 r x) (@lem5710209)). Qed.
Lemma lem5710211 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5710212 (r : int) (x : int) : (term937 r x) = term233.
Proof. exact (MK_COMB (@lem5710211) (@lem5710210 r x)). Qed.
Lemma lem5710213 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem5710214 (r : int) (x : int) : (term933 r x) = term234.
Proof. exact (MK_COMB (@lem5710212 r x) (@lem5710213)). Qed.
Lemma lem5710215 (l : int) (r : int) (x : int) (h1 : term923 l r x) : term234.
Proof. exact (EQ_MP (@lem5710214 r x) (@lem5709983 l r x h1)). Qed.
Lemma lem5710217 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5710218 : term234 = term235.
Proof. exact (@lem5710217 term81 term103). Qed.
Lemma lem5710220 (x : nat) : (term109 x) = (term110 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5710221 : term103 = term111.
Proof. exact (@lem5710220 term76). Qed.
Lemma lem5710223 (x : nat) : (real_of_num x) = (term107 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5710224 : term81 = term162.
Proof. exact (@lem5710223 (NUMERAL 0)). Qed.
Lemma lem5710225 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5710226 : term236 = term237.
Proof. exact (MK_COMB (@lem5710225) (@lem5710224)). Qed.
Lemma lem5710227 : term235 = term238.
Proof. exact (MK_COMB (@lem5710226) (@lem5710221)). Qed.
Lemma lem5710228 : term239.
Proof. exact (@lem1980026 term81 term75 term103 term75). Qed.
Lemma lem5710230 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5710231 : term161 = term168.
Proof. exact (@lem5710230 (NUMERAL 0) term76). Qed.
Lemma lem5710232 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5710233 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5710234 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5710233 h1) (fun h1 : term168 = True => @lem5710232)). Qed.
Lemma lem5710235 : term168 = True.
Proof. exact (EQ_MP (@lem5710234) (@lem5710232)). Qed.
Lemma lem5710236 : term161 = True.
Proof. exact (TRANS (@lem5710231) (@lem5710235)). Qed.
Lemma lem5710237 : True = term161.
Proof. exact (SYM (@lem5710236)). Qed.
Lemma lem5710238 : term161.
Proof. exact (EQ_MP (@lem5710237) (@lem0)). Qed.
Lemma lem5710239 : term240.
Proof. exact (@lem5710228 (@lem5710238)). Qed.
Lemma lem5710241 (m : nat) (n : nat) : (term167 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5710242 : term161 = term168.
Proof. exact (@lem5710241 (NUMERAL 0) term76). Qed.
Lemma lem5710243 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5710244 (h1 : term169 = (BIT1 0)) : term168 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5710245 : (term169 = (BIT1 0)) = (term168 = True).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5710244 h1) (fun h1 : term168 = True => @lem5710243)). Qed.
Lemma lem5710246 : term168 = True.
Proof. exact (EQ_MP (@lem5710245) (@lem5710243)). Qed.
Lemma lem5710247 : term161 = True.
Proof. exact (TRANS (@lem5710242) (@lem5710246)). Qed.
Lemma lem5710248 : True = term161.
Proof. exact (SYM (@lem5710247)). Qed.
Lemma lem5710249 : term161.
Proof. exact (EQ_MP (@lem5710248) (@lem0)). Qed.
Lemma lem5710250 : term238 = term241.
Proof. exact (@lem5710239 (@lem5710249)). Qed.
Lemma lem5710252 (m : nat) (n : nat) : (term123 m n) = (term124 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5710253 : term114 = term125.
Proof. exact (@lem5710252 term76 term76). Qed.
Lemma lem5710254 : (term121 = (BIT1 0)) = (term122 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5710255 : term122 = term76.
Proof. exact (EQ_MP (@lem5710254) (@lem940073)). Qed.
Lemma lem5710256 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5710257 : term120 = term75.
Proof. exact (MK_COMB (@lem5710256) (@lem5710255)). Qed.
Lemma lem5710258 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5710259 : term125 = term103.
Proof. exact (MK_COMB (@lem5710258) (@lem5710257)). Qed.
Lemma lem5710260 : term114 = term103.
Proof. exact (TRANS (@lem5710253) (@lem5710259)). Qed.
Lemma lem5710262 (x : nat) : (term172 x) = term81.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5710263 : term173 = term81.
Proof. exact (@lem5710262 term76). Qed.
Lemma lem5710264 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5710265 : term242 = term236.
Proof. exact (MK_COMB (@lem5710264) (@lem5710263)). Qed.
Lemma lem5710266 : term241 = term235.
Proof. exact (MK_COMB (@lem5710265) (@lem5710260)). Qed.
Lemma lem5710268 (m : nat) (n : nat) : (term243 m n) = (term244 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5710269 : term235 = term245.
Proof. exact (@lem5710268 (NUMERAL 0) term76). Qed.
Lemma lem5710270 : term169 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5710271 (h1 : term169 = (BIT1 0)) : (term76 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5710272 : (term169 = (BIT1 0)) = ((term76 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term169 = (BIT1 0) => @lem5710271 h1) (fun h1 : (term76 = (NUMERAL 0)) = False => @lem5710270)). Qed.
Lemma lem5710273 : (term76 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5710272) (@lem5710270)). Qed.
Lemma lem5710274 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5710275 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5710276 : term246 = (and True).
Proof. exact (MK_COMB (@lem5710275) (@lem5710274)). Qed.
Lemma lem5710277 : term245 = (True /\ False).
Proof. exact (MK_COMB (@lem5710276) (@lem5710273)). Qed.
Lemma lem5710279 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5710280 : term245 = False.
Proof. exact (TRANS (@lem5710277) (@lem5710279)). Qed.
Lemma lem5710281 : term235 = False.
Proof. exact (TRANS (@lem5710269) (@lem5710280)). Qed.
Lemma lem5710282 : term241 = False.
Proof. exact (TRANS (@lem5710266) (@lem5710281)). Qed.
Lemma lem5710283 : term238 = False.
Proof. exact (TRANS (@lem5710250) (@lem5710282)). Qed.
Lemma lem5710284 : term235 = False.
Proof. exact (TRANS (@lem5710227) (@lem5710283)). Qed.
Lemma lem5710285 : term234 = False.
Proof. exact (TRANS (@lem5710218) (@lem5710284)). Qed.
Lemma lem5710286 (l : int) (r : int) (x : int) (h1 : term923 l r x) : False.
Proof. exact (EQ_MP (@lem5710285) (@lem5710215 l r x h1)). Qed.
Lemma lem5710287 (l : int) (r : int) (x : int) (h1 : term929 l r x) : False.
Proof. exact (or_elim (@lem5709665 l r x h1) (fun h0 : term925 l r x => @lem5709823 l r x h0) (fun h0 : term923 l r x => @lem5710286 l r x h0)). Qed.
Lemma lem5710289 (l : int) (r : int) (x : int) (h1 : term929 l r x) : term929 l r x.
Proof. exact (h1). Qed.
Lemma lem5710290 (l : int) (r : int) (x : int) (h1 : term929 l r x) : (term929 l r x) = False.
Proof. exact (prop_ext (fun h2 : term929 l r x => @lem5710287 l r x h1) (fun h2 : False => @lem5710289 l r x h1)). Qed.
Lemma lem5710291 (l : int) (r : int) (x : int) (h1 : term929 l r x) : False.
Proof. exact (EQ_MP (@lem5710290 l r x h1) (@lem5710289 l r x h1)). Qed.
Lemma lem5710292 (r : int) (x : int) (l : int) (h1 : term862 r x l) : term862 r x l.
Proof. exact (h1). Qed.
Lemma lem5710293 (r : int) (x : int) (l : int) (h1 : term862 r x l) : term929 l r x.
Proof. exact (EQ_MP (@lem5709649 l r x) (@lem5710292 r x l h1)). Qed.
Lemma lem5710294 (r : int) (x : int) (l : int) (h1 : term862 r x l) : (term929 l r x) = False.
Proof. exact (prop_ext (fun h2 : term929 l r x => @lem5710291 l r x h2) (fun h2 : False => @lem5710293 r x l h1)). Qed.
Lemma lem5710295 (r : int) (x : int) (l : int) (h1 : term862 r x l) : False.
Proof. exact (EQ_MP (@lem5710294 r x l h1) (@lem5710293 r x l h1)). Qed.
Lemma lem5710296 (r : int) (x : int) (l : int) : term938 r x l.
Proof. exact (fun h0 : term862 r x l => @lem5710295 r x l h0). Qed.
Lemma lem5710297 (r : int) (x : int) (l : int) : term939 r x l.
Proof. exact (@lem1386578 (term940 r x l)). Qed.
Lemma lem5710300 (r : int) (x : int) (l : int) : term940 r x l.
Proof. exact (@lem5710297 r x l (@lem5710296 r x l)). Qed.
Lemma lem5710301 (x : int) (r : int) (l : int) : (term861 r x l) = (term822 x r l).
Proof. exact (SYM (@lem5708523 r x l)). Qed.
Lemma lem5710302 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5710303 (x : int) (r : int) (l : int) : (term940 r x l) = (term808 x r l).
Proof. exact (MK_COMB (@lem5710302) (@lem5710301 x r l)). Qed.
Lemma lem5710304 (x : int) (r : int) (l : int) : term808 x r l.
Proof. exact (EQ_MP (@lem5710303 x r l) (@lem5710300 r x l)). Qed.
Lemma lem5710305 (x : int) (r : int) (l : int) : term809 x r l.
Proof. exact (EQ_MP (@lem5708304 x r l) (@lem5710304 x r l)). Qed.
Lemma lem5710306 (x : int) (r : int) (l : int) : (term809 x r l) = ((term809 x r l) = True).
Proof. exact (@lem7 (term809 x r l)). Qed.
Lemma lem5710307 (x : int) (r : int) (l : int) : (term809 x r l) = True.
Proof. exact (EQ_MP (@lem5710306 x r l) (@lem5710305 x r l)). Qed.
Lemma lem5710308 (x : int) (r : int) (l : int) : True = (term809 x r l).
Proof. exact (SYM (@lem5710307 x r l)). Qed.
Lemma lem5710309 (x : int) (r : int) (l : int) : term809 x r l.
Proof. exact (EQ_MP (@lem5710308 x r l) (@lem0)). Qed.
Lemma lem5710310 (x : int) (r : int) (l : int) (h1 : term251 r l) : term823 x r l.
Proof. exact (@lem5710309 x r l (@lem5702058 r l h1)). Qed.
Lemma lem5710311 (x : int) (r : int) (l : int) (h1 : int_le l x) (h2 : term251 r l) : term818 x r l.
Proof. exact (@lem5710310 x r l h2 (@lem5708196 l x h1)). Qed.
Lemma lem5710312 (x : int) (r : int) (l : int) (h1 : int_le l x) (h2 : int_le x r) (h3 : term251 r l) : term807 x r l.
Proof. exact (@lem5710311 x r l h1 h3 (@lem5708195 x r h2)). Qed.
Lemma lem5710313 (x : int) (r : int) (l : int) (h1 : int_le l x) (h2 : int_le x r) (h3 : term251 r l) : term806 x r l.
Proof. exact (EQ_MP (@lem5708303 x r l h1 h3) (@lem5710312 x r l h1 h2 h3)). Qed.
Lemma lem5710314 (x : int) (r : int) (l : int) (h1 : int_le l x) (h2 : int_le x r) (h3 : term251 r l) : term780 x r l.
Proof. exact (ex_intro (term779 x r l) (term735 x l) (@lem5710313 x r l h1 h2 h3)). Qed.
Lemma lem5710315 (l : int) (x : int) (r : int) (h1 : term50 l x r) : int_le x r.
Proof. exact (proj2 (@lem5708194 l x r h1)). Qed.
Lemma lem5710316 (l : int) (x : int) (r : int) (h1 : term50 l x r) : int_le l x.
Proof. exact (proj1 (@lem5708194 l x r h1)). Qed.
Lemma lem5710317 (x : int) (r : int) (l : int) (h1 : int_le l x) (h2 : int_le x r) (h3 : term251 r l) : (int_le x r) = (term780 x r l).
Proof. exact (prop_ext (fun h4 : int_le x r => @lem5710314 x r l h1 h2 h3) (fun h4 : term780 x r l => @lem5708195 x r h2)). Qed.
Lemma lem5710318 (x : int) (r : int) (l : int) (h1 : int_le l x) (h2 : int_le x r) (h3 : term251 r l) : term780 x r l.
Proof. exact (EQ_MP (@lem5710317 x r l h1 h2 h3) (@lem5708195 x r h2)). Qed.
Lemma lem5710319 (x : int) (r : int) (l : int) (h1 : int_le l x) (h2 : int_le x r) (h3 : term251 r l) : (int_le l x) = (term780 x r l).
Proof. exact (prop_ext (fun h4 : int_le l x => @lem5710318 x r l h1 h2 h3) (fun h4 : term780 x r l => @lem5708196 l x h1)). Qed.
Lemma lem5710320 (x : int) (r : int) (l : int) (h1 : int_le l x) (h2 : int_le x r) (h3 : term251 r l) : term780 x r l.
Proof. exact (EQ_MP (@lem5710319 x r l h1 h2 h3) (@lem5708196 l x h1)). Qed.
Lemma lem5710321 (x : int) (r : int) (l : int) (h1 : term50 l x r) (h2 : int_le l x) (h3 : term251 r l) : (int_le x r) = (term780 x r l).
Proof. exact (prop_ext (fun h4 : int_le x r => @lem5710320 x r l h2 h4 h3) (fun h4 : term780 x r l => @lem5710315 l x r h1)). Qed.
Lemma lem5710322 (x : int) (r : int) (l : int) (h1 : term50 l x r) (h2 : int_le l x) (h3 : term251 r l) : term780 x r l.
Proof. exact (EQ_MP (@lem5710321 x r l h1 h2 h3) (@lem5710315 l x r h1)). Qed.
Lemma lem5710323 (x : int) (r : int) (l : int) (h1 : term50 l x r) (h2 : term251 r l) : (int_le l x) = (term780 x r l).
Proof. exact (prop_ext (fun h3 : int_le l x => @lem5710322 x r l h1 h3 h2) (fun h3 : term780 x r l => @lem5710316 l x r h1)). Qed.
Lemma lem5710324 (x : int) (r : int) (l : int) (h1 : term50 l x r) (h2 : term251 r l) : term780 x r l.
Proof. exact (EQ_MP (@lem5710323 x r l h1 h2) (@lem5710316 l x r h1)). Qed.
Lemma lem5710325 (x : int) (r : int) (l : int) (h1 : term251 r l) : term781 x r l.
Proof. exact (fun h0 : term50 l x r => @lem5710324 x r l h0 h1). Qed.
Lemma lem5710330 (r : int) (l : int) (h1 : term251 r l) : term783 r l.
Proof. exact (fun x : int => @lem5710325 x r l h1). Qed.
Lemma lem5710331 (r : int) (l : int) (h1 : term251 r l) : term769 r l.
Proof. exact (EQ_MP (@lem5708193 r l) (@lem5710330 r l h1)). Qed.
Lemma lem5710332 (r : int) (l : int) (h1 : term251 r l) : term738 r l.
Proof. exact (EQ_MP (@lem5708137 r l) (@lem5710331 r l h1)). Qed.
Lemma lem5710333 (r : int) (l : int) (h1 : term251 r l) : term739 r l.
Proof. exact (EQ_MP (@lem5708046 r l) (@lem5710332 r l h1)). Qed.
Lemma lem5710334 (r : int) (l : int) (h1 : term251 r l) : term941 l r.
Proof. exact (ex_intro (term942 l r) (term742 r l) (@lem5710333 r l h1)). Qed.
Lemma lem5710337 (r : int) (l : int) (h1 : term55 r l) : term329 l r.
Proof. exact (EQ_MP (@lem5707957 r l h1) (@lem5707984)). Qed.
Lemma lem5710338 (r : int) (l : int) (h1 : term251 r l) : term329 l r.
Proof. exact (@lem5707988 l r (@lem5710334 r l h1)). Qed.
Lemma lem5710339 (l : int) (r : int) : term329 l r.
Proof. exact (or_elim (@lem5702057 r l) (fun h0 : term251 r l => @lem5710338 r l h0) (fun h0 : term55 r l => @lem5710337 r l h0)). Qed.
Lemma lem5710344 (l : int) : term302 l.
Proof. exact (fun r : int => @lem5710339 l r). Qed.
Lemma lem5710349 : term295.
Proof. exact (fun l : int => @lem5710344 l). Qed.
Lemma lem5710350 : term943.
Proof. exact (conj (@lem5707872) (@lem5710349)). Qed.
Lemma lem5710351 : term944.
Proof. exact (@lem5702271 (@lem5710350)). Qed.
