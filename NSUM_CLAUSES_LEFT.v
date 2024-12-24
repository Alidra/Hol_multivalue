Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_CLAUSES_LEFT_term_abbrevs.
Require Import FINITE_NUMSEG_spec.
Require Import INT_POS_spec.
Require Import IN_NUMSEG_spec.
Require Import NSUM_CLAUSES_spec.
Require Import NUMSEG_LREC_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm12653_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1832_spec.
Require Import thm1843_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19158_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980026_spec.
Require Import thm1980259_spec.
Require Import thm1980260_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982755_spec.
Require Import thm1982757_spec.
Require Import thm1982761_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm20425_spec.
Require Import thm20611_spec.
Require Import thm20612_spec.
Require Import thm2318497_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318604_spec.
Require Import thm2841383_spec.
Require Import thm2841384_spec.
Require Import thm2841407_spec.
Require Import thm2841408_spec.
Require Import thm2841413_spec.
Require Import thm2841414_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem7048897 (m : nat) (n : nat) (h1 : (term0 m n) = (dotdot m n)) : (term0 m n) = (dotdot m n).
Proof. exact (h1). Qed.
Lemma lem7048898 (m : nat) (n : nat) (h1 : (term0 m n) = (dotdot m n)) : (dotdot m n) = (term0 m n).
Proof. exact (SYM (@lem7048897 m n h1)). Qed.
Lemma lem7048899 (m : nat) (n : nat) (h1 : (dotdot m n) = (term0 m n)) : (dotdot m n) = (term0 m n).
Proof. exact (h1). Qed.
Lemma lem7048900 (m : nat) (n : nat) (h1 : (dotdot m n) = (term0 m n)) : (term0 m n) = (dotdot m n).
Proof. exact (SYM (@lem7048899 m n h1)). Qed.
Lemma lem7048901 (m : nat) (n : nat) : ((term0 m n) = (dotdot m n)) = ((dotdot m n) = (term0 m n)).
Proof. exact (prop_ext (fun h1 : (term0 m n) = (dotdot m n) => @lem7048898 m n h1) (fun h1 : (dotdot m n) = (term0 m n) => @lem7048900 m n h1)). Qed.
Lemma lem7048902 (m : nat) (n : nat) : (term1 m n) = (term1 m n).
Proof. exact (eq_refl (term1 m n)). Qed.
Lemma lem7048903 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (MK_COMB (@lem7048902 m n) (@lem7048901 m n)). Qed.
Lemma lem7048904 (m : nat) : (term4 m) = (term5 m).
Proof. exact (fun_ext (fun n : nat => @lem7048903 m n)). Qed.
Lemma lem7048905 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7048906 (m : nat) : (term6 m) = (term7 m).
Proof. exact (MK_COMB (@lem7048905) (@lem7048904 m)). Qed.
Lemma lem7048907 : term8 = term9.
Proof. exact (fun_ext (fun m : nat => @lem7048906 m)). Qed.
Lemma lem7048908 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7048909 : term10 = term11.
Proof. exact (MK_COMB (@lem7048908) (@lem7048907)). Qed.
Lemma lem7048910 : term11.
Proof. exact (EQ_MP (@lem7048909) (@lem5357842)). Qed.
Lemma lem7048911 (m : nat) : term12 m.
Proof. exact (@lem5371273 m). Qed.
Lemma lem7048912 (m : nat) : (term12 m) = (term13 m).
Proof. exact (eq_refl (term12 m)). Qed.
Lemma lem7048913 (m : nat) : term13 m.
Proof. exact (EQ_MP (@lem7048912 m) (@lem7048911 m)). Qed.
Lemma lem7048914 (m : nat) (n : nat) : term14 m n.
Proof. exact (@lem7048913 m n). Qed.
Lemma lem7048915 (m : nat) (n : nat) : (term14 m n) = (term15 m n).
Proof. exact (eq_refl (term14 m n)). Qed.
Lemma lem7048916 (m : nat) (n : nat) : term15 m n.
Proof. exact (EQ_MP (@lem7048915 m n) (@lem7048914 m n)). Qed.
Lemma lem7048917 (m : nat) (n : nat) (p : nat) : term16 m n p.
Proof. exact (@lem7048916 m n p). Qed.
Lemma lem7048918 (m : nat) (p : nat) (n : nat) : (term16 m n p) = ((term17 p m n) = (term18 m p n)).
Proof. exact (eq_refl (term16 m n p)). Qed.
Lemma lem7048920 (m : nat) : term19 m.
Proof. exact (@lem5329299 m). Qed.
Lemma lem7048921 (m : nat) : (term19 m) = (term20 m).
Proof. exact (eq_refl (term19 m)). Qed.
Lemma lem7048922 (m : nat) : term20 m.
Proof. exact (EQ_MP (@lem7048921 m) (@lem7048920 m)). Qed.
Lemma lem7048923 (m : nat) (n : nat) : term21 m n.
Proof. exact (@lem7048922 m n). Qed.
Lemma lem7048924 (m : nat) (n : nat) : (term21 m n) = (term22 m n).
Proof. exact (eq_refl (term21 m n)). Qed.
Lemma lem7048925 (m : nat) (n : nat) : term22 m n.
Proof. exact (EQ_MP (@lem7048924 m n) (@lem7048923 m n)). Qed.
Lemma lem7048926 (m : nat) (n : nat) : (term22 m n) = ((term22 m n) = True).
Proof. exact (@lem7 (term22 m n)). Qed.
Lemma lem7048928 {_126525 : Type'} : term23 _126525.
Proof. exact (proj2 (@lem6924916 Prop _126525)). Qed.
Lemma lem7048929 {_126525 : Type'} (x : _126525) : term24 _126525 x.
Proof. exact (@lem7048928 _126525 x). Qed.
Lemma lem7048930 {_126525 : Type'} (x : _126525) : (term24 _126525 x) = (term25 _126525 x).
Proof. exact (eq_refl (term24 _126525 x)). Qed.
Lemma lem7048931 {_126525 : Type'} (x : _126525) : term25 _126525 x.
Proof. exact (EQ_MP (@lem7048930 _126525 x) (@lem7048929 _126525 x)). Qed.
Lemma lem7048932 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) : term26 _126525 x f.
Proof. exact (@lem7048931 _126525 x f). Qed.
Lemma lem7048933 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) : (term26 _126525 x f) = (term27 _126525 x f).
Proof. exact (eq_refl (term26 _126525 x f)). Qed.
Lemma lem7048934 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) : term27 _126525 x f.
Proof. exact (EQ_MP (@lem7048933 _126525 x f) (@lem7048932 _126525 x f)). Qed.
Lemma lem7048935 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) (s : _126525 -> Prop) : term28 _126525 x f s.
Proof. exact (@lem7048934 _126525 x f s). Qed.
Lemma lem7048936 {_126525 : Type'} (x : _126525) (s : _126525 -> Prop) (f : _126525 -> nat) : (term28 _126525 x f s) = (term29 _126525 x s f).
Proof. exact (eq_refl (term28 _126525 x f s)). Qed.
Lemma lem7048937 {_126525 : Type'} (x : _126525) (s : _126525 -> Prop) (f : _126525 -> nat) : term29 _126525 x s f.
Proof. exact (EQ_MP (@lem7048936 _126525 x s f) (@lem7048935 _126525 x f s)). Qed.
Lemma lem7048938 {_126525 : Type'} (s : _126525 -> Prop) (h1 : @FINITE _126525 s) : @FINITE _126525 s.
Proof. exact (h1). Qed.
Lemma lem7048939 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) (s : _126525 -> Prop) (h1 : @FINITE _126525 s) : (term30 _126525 x s f) = (term31 _126525 x s f).
Proof. exact (@lem7048937 _126525 x s f (@lem7048938 _126525 s h1)). Qed.
Lemma lem7048949 (m : nat) : term32 m.
Proof. exact (@lem7048910 m). Qed.
Lemma lem7048950 (m : nat) : (term32 m) = (term7 m).
Proof. exact (eq_refl (term32 m)). Qed.
Lemma lem7048951 (m : nat) : term7 m.
Proof. exact (EQ_MP (@lem7048950 m) (@lem7048949 m)). Qed.
Lemma lem7048952 (m : nat) (n : nat) : term33 m n.
Proof. exact (@lem7048951 m n). Qed.
Lemma lem7048953 (m : nat) (n : nat) : (term33 m n) = (term3 m n).
Proof. exact (eq_refl (term33 m n)). Qed.
Lemma lem7048954 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem7048953 m n) (@lem7048952 m n)). Qed.
Lemma lem7048955 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem7048956 (m : nat) (n : nat) (h1 : Peano.le m n) : (dotdot m n) = (term0 m n).
Proof. exact (@lem7048954 m n (@lem7048955 m n h1)). Qed.
Lemma lem7048977 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term34 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7048978 (p : Prop) (q : Prop) (p' : Prop) : term35 p q p'.
Proof. exact (fun q' : Prop => @lem7048977 p q p' q'). Qed.
Lemma lem7048979 (p : Prop) (q : Prop) : term36 p q.
Proof. exact (fun p' : Prop => @lem7048978 p q p'). Qed.
Lemma lem7048980 (m : nat) (n : nat) (f : nat -> nat) : term37 m n f.
Proof. exact (@lem7048979 (Peano.le m n) ((term38 m n f) = (term39 m n f))). Qed.
Lemma lem7048981 (m : nat) (n : nat) (f : nat -> nat) (p' : Prop) : term40 m n f p'.
Proof. exact (@lem7048980 m n f p'). Qed.
Lemma lem7048982 (m : nat) (n : nat) (f : nat -> nat) (p' : Prop) : (term40 m n f p') = (term41 m n f p').
Proof. exact (eq_refl (term40 m n f p')). Qed.
Lemma lem7048983 (m : nat) (n : nat) (f : nat -> nat) (p' : Prop) : term41 m n f p'.
Proof. exact (EQ_MP (@lem7048982 m n f p') (@lem7048981 m n f p')). Qed.
Lemma lem7048984 (m : nat) (n : nat) (f : nat -> nat) (p' : Prop) (q' : Prop) : term42 m n f p' q'.
Proof. exact (@lem7048983 m n f p' q'). Qed.
Lemma lem7048985 (m : nat) (n : nat) (f : nat -> nat) (p' : Prop) (q' : Prop) : (term42 m n f p' q') = (term43 m n f p' q').
Proof. exact (eq_refl (term42 m n f p' q')). Qed.
Lemma lem7048986 (m : nat) (n : nat) (f : nat -> nat) (p' : Prop) (q' : Prop) : term43 m n f p' q'.
Proof. exact (EQ_MP (@lem7048985 m n f p' q') (@lem7048984 m n f p' q')). Qed.
Lemma lem7048987 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem7048988 (f : nat -> nat) (m : nat) (n : nat) (q' : Prop) : term44 f m n q'.
Proof. exact (@lem7048986 m n f (Peano.le m n) q'). Qed.
Lemma lem7048989 (f : nat -> nat) (m : nat) (n : nat) (q' : Prop) : term45 f m n q'.
Proof. exact (@lem7048988 f m n q' (@lem7048987 m n)). Qed.
Lemma lem7048990 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem7048991 (m : nat) (n : nat) : (Peano.le m n) = ((Peano.le m n) = True).
Proof. exact (@lem7 (Peano.le m n)). Qed.
Lemma lem7048996 (m : nat) (n : nat) : term3 m n.
Proof. exact (fun h0 : Peano.le m n => @lem7048956 m n h0). Qed.
Lemma lem7048998 (m : nat) (n : nat) (h1 : Peano.le m n) : (Peano.le m n) = True.
Proof. exact (EQ_MP (@lem7048991 m n) (@lem7048990 m n h1)). Qed.
Lemma lem7048999 (m : nat) (n : nat) (h1 : Peano.le m n) : True = (Peano.le m n).
Proof. exact (SYM (@lem7048998 m n h1)). Qed.
Lemma lem7049000 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (EQ_MP (@lem7048999 m n h1) (@lem0)). Qed.
Lemma lem7049001 (m : nat) (n : nat) (h1 : Peano.le m n) : (dotdot m n) = (term0 m n).
Proof. exact (@lem7048996 m n (@lem7049000 m n h1)). Qed.
Lemma lem7049007 : (@nsum nat) = (@nsum nat).
Proof. exact (eq_refl (@nsum nat)). Qed.
Lemma lem7049008 (m : nat) (n : nat) (h1 : Peano.le m n) : (term46 m n) = (term47 m n).
Proof. exact (MK_COMB (@lem7049007) (@lem7049001 m n h1)). Qed.
Lemma lem7049014 (f : nat -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7049015 (f : nat -> nat) (m : nat) (n : nat) (h1 : Peano.le m n) : (term38 m n f) = (term48 m n f).
Proof. exact (MK_COMB (@lem7049008 m n h1) (@lem7049014 f)). Qed.
Lemma lem7049017 {_126525 : Type'} (x : _126525) (s : _126525 -> Prop) (f : _126525 -> nat) : term29 _126525 x s f.
Proof. exact (fun h0 : @FINITE _126525 s => @lem7048939 _126525 x f s h0). Qed.
Lemma lem7049018 (x : nat) (s : nat -> Prop) (f : nat -> nat) : term49 x s f.
Proof. exact (@lem7049017 nat x s f). Qed.
Lemma lem7049019 (m : nat) (n : nat) (f : nat -> nat) : term50 m n f.
Proof. exact (@lem7049018 m (term51 m n) f). Qed.
Lemma lem7049021 (m : nat) (n : nat) : (term22 m n) = True.
Proof. exact (EQ_MP (@lem7048926 m n) (@lem7048925 m n)). Qed.
Lemma lem7049022 (m : nat) (n : nat) : (term52 m n) = True.
Proof. exact (@lem7049021 (term53 m) n). Qed.
Lemma lem7049023 (m : nat) (n : nat) : True = (term52 m n).
Proof. exact (SYM (@lem7049022 m n)). Qed.
Lemma lem7049024 (m : nat) (n : nat) : term52 m n.
Proof. exact (EQ_MP (@lem7049023 m n) (@lem0)). Qed.
Lemma lem7049025 (m : nat) (n : nat) (f : nat -> nat) : (term48 m n f) = (term54 m n f).
Proof. exact (@lem7049019 m n f (@lem7049024 m n)). Qed.
Lemma lem7049027 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term55 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem7049028 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term56 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem7049027 _2963 g t e g' t' e'). Qed.
Lemma lem7049029 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term57 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem7049028 _2963 g t e g' t'). Qed.
Lemma lem7049030 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term58 _2963 g t e.
Proof. exact (fun g' : Prop => @lem7049029 _2963 g t e g'). Qed.
Lemma lem7049031 (g : Prop) (t : nat) (e : nat) : term59 g t e.
Proof. exact (@lem7049030 nat g t e). Qed.
Lemma lem7049032 (m : nat) (n : nat) (f : nat -> nat) : term60 m n f.
Proof. exact (@lem7049031 (term61 m n) (term62 m n f) (term39 m n f)). Qed.
Lemma lem7049033 (m : nat) (n : nat) (f : nat -> nat) (g' : Prop) : term63 m n f g'.
Proof. exact (@lem7049032 m n f g'). Qed.
Lemma lem7049034 (m : nat) (n : nat) (f : nat -> nat) (g' : Prop) : (term63 m n f g') = (term64 m n f g').
Proof. exact (eq_refl (term63 m n f g')). Qed.
Lemma lem7049035 (m : nat) (n : nat) (f : nat -> nat) (g' : Prop) : term64 m n f g'.
Proof. exact (EQ_MP (@lem7049034 m n f g') (@lem7049033 m n f g')). Qed.
Lemma lem7049036 (m : nat) (n : nat) (f : nat -> nat) (g' : Prop) (t' : nat) : term65 m n f g' t'.
Proof. exact (@lem7049035 m n f g' t'). Qed.
Lemma lem7049037 (m : nat) (n : nat) (f : nat -> nat) (g' : Prop) (t' : nat) : (term65 m n f g' t') = (term66 m n f g' t').
Proof. exact (eq_refl (term65 m n f g' t')). Qed.
Lemma lem7049038 (m : nat) (n : nat) (f : nat -> nat) (g' : Prop) (t' : nat) : term66 m n f g' t'.
Proof. exact (EQ_MP (@lem7049037 m n f g' t') (@lem7049036 m n f g' t')). Qed.
Lemma lem7049039 (m : nat) (n : nat) (f : nat -> nat) (g' : Prop) (t' : nat) (e' : nat) : term67 m n f g' t' e'.
Proof. exact (@lem7049038 m n f g' t' e'). Qed.
Lemma lem7049040 (m : nat) (n : nat) (f : nat -> nat) (g' : Prop) (t' : nat) (e' : nat) : (term67 m n f g' t' e') = (term68 m n f g' t' e').
Proof. exact (eq_refl (term67 m n f g' t' e')). Qed.
Lemma lem7049041 (m : nat) (n : nat) (f : nat -> nat) (g' : Prop) (t' : nat) (e' : nat) : term68 m n f g' t' e'.
Proof. exact (EQ_MP (@lem7049040 m n f g' t' e') (@lem7049039 m n f g' t' e')). Qed.
Lemma lem7049043 (m : nat) (p : nat) (n : nat) : (term17 p m n) = (term18 m p n).
Proof. exact (EQ_MP (@lem7048918 m p n) (@lem7048917 m n p)). Qed.
Lemma lem7049044 (m : nat) (n : nat) : (term61 m n) = (term69 m n).
Proof. exact (@lem7049043 (term53 m) m n). Qed.
Lemma lem7049048 (m : nat) (n : nat) (h1 : Peano.le m n) : (Peano.le m n) = True.
Proof. exact (EQ_MP (@lem7048991 m n) (@lem7048990 m n h1)). Qed.
Lemma lem7049049 (m : nat) : (term70 m) = (term70 m).
Proof. exact (eq_refl (term70 m)). Qed.
Lemma lem7049050 (m : nat) (n : nat) (h1 : Peano.le m n) : (term69 m n) = (term71 m).
Proof. exact (MK_COMB (@lem7049049 m) (@lem7049048 m n h1)). Qed.
Lemma lem7049052 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem7049053 (m : nat) : (term71 m) = (term72 m).
Proof. exact (@lem7049052 (term72 m)). Qed.
Lemma lem7049054 (m : nat) (n : nat) (h1 : Peano.le m n) : (term69 m n) = (term72 m).
Proof. exact (TRANS (@lem7049050 m n h1) (@lem7049053 m)). Qed.
Lemma lem7049055 (m : nat) (n : nat) (h1 : Peano.le m n) : (term61 m n) = (term72 m).
Proof. exact (TRANS (@lem7049044 m n) (@lem7049054 m n h1)). Qed.
Lemma lem7049056 (n : nat) (f : nat -> nat) (m : nat) (t' : nat) (e' : nat) : term73 n f m t' e'.
Proof. exact (@lem7049041 m n f (term72 m) t' e'). Qed.
Lemma lem7049057 (f : nat -> nat) (t' : nat) (e' : nat) (m : nat) (n : nat) (h1 : Peano.le m n) : term74 n f m t' e'.
Proof. exact (@lem7049056 n f m t' e' (@lem7049055 m n h1)). Qed.
Lemma lem7049066 (m : nat) (n : nat) (f : nat -> nat) : (term62 m n f) = (term62 m n f).
Proof. exact (eq_refl (term62 m n f)). Qed.
Lemma lem7049067 (m : nat) (n : nat) (f : nat -> nat) : term75 m n f.
Proof. exact (fun h0 : term72 m => @lem7049066 m n f). Qed.
Lemma lem7049068 (f : nat -> nat) (e' : nat) (m : nat) (n : nat) (h1 : Peano.le m n) : term76 m n f e'.
Proof. exact (@lem7049057 f (term62 m n f) e' m n h1). Qed.
Lemma lem7049069 (f : nat -> nat) (e' : nat) (m : nat) (n : nat) (h1 : Peano.le m n) : term77 m n f e'.
Proof. exact (@lem7049068 f e' m n h1 (@lem7049067 m n f)). Qed.
Lemma lem7049078 (m : nat) (n : nat) (f : nat -> nat) : (term39 m n f) = (term39 m n f).
Proof. exact (eq_refl (term39 m n f)). Qed.
Lemma lem7049079 (m : nat) (n : nat) (f : nat -> nat) : term78 m n f.
Proof. exact (fun h0 : term79 m => @lem7049078 m n f). Qed.
Lemma lem7049080 (f : nat -> nat) (m : nat) (n : nat) (h1 : Peano.le m n) : term80 m n f.
Proof. exact (@lem7049069 f (term39 m n f) m n h1). Qed.
Lemma lem7049081 (f : nat -> nat) (m : nat) (n : nat) (h1 : Peano.le m n) : (term54 m n f) = (term81 m n f).
Proof. exact (@lem7049080 f m n h1 (@lem7049079 m n f)). Qed.
Lemma lem7049135 (f : nat -> nat) (m : nat) (n : nat) (h1 : Peano.le m n) : (term48 m n f) = (term81 m n f).
Proof. exact (TRANS (@lem7049025 m n f) (@lem7049081 f m n h1)). Qed.
Lemma lem7049136 (f : nat -> nat) (m : nat) (n : nat) (h1 : Peano.le m n) : (term38 m n f) = (term81 m n f).
Proof. exact (TRANS (@lem7049015 f m n h1) (@lem7049135 f m n h1)). Qed.
Lemma lem7049137 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7049138 (f : nat -> nat) (m : nat) (n : nat) (h1 : Peano.le m n) : (term82 m n f) = (term83 m n f).
Proof. exact (MK_COMB (@lem7049137) (@lem7049136 f m n h1)). Qed.
Lemma lem7049197 (m : nat) (n : nat) (f : nat -> nat) : (term39 m n f) = (term39 m n f).
Proof. exact (eq_refl (term39 m n f)). Qed.
Lemma lem7049198 (f : nat -> nat) (m : nat) (n : nat) (h1 : Peano.le m n) : ((term38 m n f) = (term39 m n f)) = ((term81 m n f) = (term39 m n f)).
Proof. exact (MK_COMB (@lem7049138 f m n h1) (@lem7049197 m n f)). Qed.
Lemma lem7049259 (m : nat) (n : nat) (f : nat -> nat) : term84 m n f.
Proof. exact (fun h0 : Peano.le m n => @lem7049198 f m n h0). Qed.
Lemma lem7049260 (m : nat) (n : nat) (f : nat -> nat) : term85 m n f.
Proof. exact (@lem7048989 f m n ((term81 m n f) = (term39 m n f))). Qed.
Lemma lem7049261 (m : nat) (n : nat) (f : nat -> nat) : (term86 m n f) = (term87 m n f).
Proof. exact (@lem7049260 m n f (@lem7049259 m n f)). Qed.
Lemma lem7049405 (m : nat) (f : nat -> nat) : (term88 m f) = (term89 m f).
Proof. exact (fun_ext (fun n : nat => @lem7049261 m n f)). Qed.
Lemma lem7049549 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7049550 (m : nat) (f : nat -> nat) : (term90 m f) = (term91 m f).
Proof. exact (MK_COMB (@lem7049549) (@lem7049405 m f)). Qed.
Lemma lem7049698 (f : nat -> nat) : (term92 f) = (term93 f).
Proof. exact (fun_ext (fun m : nat => @lem7049550 m f)). Qed.
Lemma lem7049846 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7049847 (f : nat -> nat) : (term94 f) = (term95 f).
Proof. exact (MK_COMB (@lem7049846) (@lem7049698 f)). Qed.
Lemma lem7049999 : term96 = term97.
Proof. exact (fun_ext (fun f : nat -> nat => @lem7049847 f)). Qed.
Lemma lem7050151 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7050152 : term98 = term99.
Proof. exact (MK_COMB (@lem7050151) (@lem7049999)). Qed.
Lemma lem7050308 : term99 = term98.
Proof. exact (SYM (@lem7050152)). Qed.
Lemma lem7050329 (m : nat) (h1 : (term72 m) = False) : (term72 m) = False.
Proof. exact (h1). Qed.
Lemma lem7050330 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem7050331 (m : nat) (h1 : (term72 m) = False) : (term100 m) = (@COND nat False).
Proof. exact (MK_COMB (@lem7050330) (@lem7050329 m h1)). Qed.
Lemma lem7050332 (m : nat) (n : nat) (f : nat -> nat) : (term62 m n f) = (term62 m n f).
Proof. exact (eq_refl (term62 m n f)). Qed.
Lemma lem7050333 (n : nat) (f : nat -> nat) (m : nat) (h1 : (term72 m) = False) : (term101 m n f) = (term102 m n f).
Proof. exact (MK_COMB (@lem7050331 m h1) (@lem7050332 m n f)). Qed.
Lemma lem7050334 (m : nat) (n : nat) (f : nat -> nat) : (term39 m n f) = (term39 m n f).
Proof. exact (eq_refl (term39 m n f)). Qed.
Lemma lem7050335 (n : nat) (f : nat -> nat) (m : nat) (h1 : (term72 m) = False) : (term81 m n f) = (term103 m n f).
Proof. exact (MK_COMB (@lem7050333 n f m h1) (@lem7050334 m n f)). Qed.
Lemma lem7050337 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem7050338 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem7050337 nat t1 t2). Qed.
Lemma lem7050339 (m : nat) (n : nat) (f : nat -> nat) : (term103 m n f) = (term39 m n f).
Proof. exact (@lem7050338 (term62 m n f) (term39 m n f)). Qed.
Lemma lem7050340 (n : nat) (f : nat -> nat) (m : nat) (h1 : (term72 m) = False) : (term81 m n f) = (term39 m n f).
Proof. exact (TRANS (@lem7050335 n f m h1) (@lem7050339 m n f)). Qed.
Lemma lem7050341 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7050342 (n : nat) (f : nat -> nat) (m : nat) (h1 : (term72 m) = False) : (term83 m n f) = (term104 m n f).
Proof. exact (MK_COMB (@lem7050341) (@lem7050340 n f m h1)). Qed.
Lemma lem7050343 (m : nat) (n : nat) (f : nat -> nat) : (term39 m n f) = (term39 m n f).
Proof. exact (eq_refl (term39 m n f)). Qed.
Lemma lem7050344 (n : nat) (f : nat -> nat) (m : nat) (h1 : (term72 m) = False) : ((term81 m n f) = (term39 m n f)) = ((term39 m n f) = (term39 m n f)).
Proof. exact (MK_COMB (@lem7050342 n f m h1) (@lem7050343 m n f)). Qed.
Lemma lem7050346 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7050347 (x : nat) : (x = x) = True.
Proof. exact (@lem7050346 nat x). Qed.
Lemma lem7050348 (m : nat) (n : nat) (f : nat -> nat) : ((term39 m n f) = (term39 m n f)) = True.
Proof. exact (@lem7050347 (term39 m n f)). Qed.
Lemma lem7050349 (n : nat) (f : nat -> nat) (m : nat) (h1 : (term72 m) = False) : ((term81 m n f) = (term39 m n f)) = True.
Proof. exact (TRANS (@lem7050344 n f m h1) (@lem7050348 m n f)). Qed.
Lemma lem7050350 (m : nat) (n : nat) : (term1 m n) = (term1 m n).
Proof. exact (eq_refl (term1 m n)). Qed.
Lemma lem7050351 (f : nat -> nat) (n : nat) (m : nat) (h1 : (term72 m) = False) : (term87 m n f) = (term105 m n).
Proof. exact (MK_COMB (@lem7050350 m n) (@lem7050349 n f m h1)). Qed.
Lemma lem7050353 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7050354 (m : nat) (n : nat) : (term105 m n) = True.
Proof. exact (@lem7050353 (Peano.le m n)). Qed.
Lemma lem7050355 (n : nat) (f : nat -> nat) (m : nat) (h1 : (term72 m) = False) : (term87 m n f) = True.
Proof. exact (TRANS (@lem7050351 f n m h1) (@lem7050354 m n)). Qed.
Lemma lem7050356 (f : nat -> nat) (m : nat) (h1 : (term72 m) = False) : (term89 m f) = term106.
Proof. exact (fun_ext (fun n : nat => @lem7050355 n f m h1)). Qed.
Lemma lem7050357 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7050358 (f : nat -> nat) (m : nat) (h1 : (term72 m) = False) : (term91 m f) = term107.
Proof. exact (MK_COMB (@lem7050357) (@lem7050356 f m h1)). Qed.
Lemma lem7050360 {A : Type'} (t : Prop) : (term108 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7050361 (t : Prop) : (term109 t) = t.
Proof. exact (@lem7050360 nat t). Qed.
Lemma lem7050362 : term107 = True.
Proof. exact (@lem7050361 True). Qed.
Lemma lem7050363 (f : nat -> nat) (m : nat) (h1 : (term72 m) = False) : (term91 m f) = True.
Proof. exact (TRANS (@lem7050358 f m h1) (@lem7050362)). Qed.
Lemma lem7050364 (m : nat) (f : nat -> nat) : term110 m f.
Proof. exact (fun h0 : (term72 m) = False => @lem7050363 f m h0). Qed.
Lemma lem7050366 (m : nat) (h1 : (term72 m) = True) : (term72 m) = True.
Proof. exact (h1). Qed.
Lemma lem7050367 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem7050368 (m : nat) (h1 : (term72 m) = True) : (term100 m) = (@COND nat True).
Proof. exact (MK_COMB (@lem7050367) (@lem7050366 m h1)). Qed.
Lemma lem7050369 (m : nat) (n : nat) (f : nat -> nat) : (term62 m n f) = (term62 m n f).
Proof. exact (eq_refl (term62 m n f)). Qed.
Lemma lem7050370 (n : nat) (f : nat -> nat) (m : nat) (h1 : (term72 m) = True) : (term101 m n f) = (term111 m n f).
Proof. exact (MK_COMB (@lem7050368 m h1) (@lem7050369 m n f)). Qed.
Lemma lem7050371 (m : nat) (n : nat) (f : nat -> nat) : (term39 m n f) = (term39 m n f).
Proof. exact (eq_refl (term39 m n f)). Qed.
Lemma lem7050372 (n : nat) (f : nat -> nat) (m : nat) (h1 : (term72 m) = True) : (term81 m n f) = (term112 m n f).
Proof. exact (MK_COMB (@lem7050370 n f m h1) (@lem7050371 m n f)). Qed.
Lemma lem7050374 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem7050375 (t2 : nat) (t1 : nat) : (@COND nat True t1 t2) = t1.
Proof. exact (@lem7050374 nat t2 t1). Qed.
Lemma lem7050376 (m : nat) (n : nat) (f : nat -> nat) : (term112 m n f) = (term62 m n f).
Proof. exact (@lem7050375 (term39 m n f) (term62 m n f)). Qed.
Lemma lem7050377 (n : nat) (f : nat -> nat) (m : nat) (h1 : (term72 m) = True) : (term81 m n f) = (term62 m n f).
Proof. exact (TRANS (@lem7050372 n f m h1) (@lem7050376 m n f)). Qed.
Lemma lem7050378 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7050379 (n : nat) (f : nat -> nat) (m : nat) (h1 : (term72 m) = True) : (term83 m n f) = (term113 m n f).
Proof. exact (MK_COMB (@lem7050378) (@lem7050377 n f m h1)). Qed.
Lemma lem7050380 (m : nat) (n : nat) (f : nat -> nat) : (term39 m n f) = (term39 m n f).
Proof. exact (eq_refl (term39 m n f)). Qed.
Lemma lem7050381 (n : nat) (f : nat -> nat) (m : nat) (h1 : (term72 m) = True) : ((term81 m n f) = (term39 m n f)) = ((term62 m n f) = (term39 m n f)).
Proof. exact (MK_COMB (@lem7050379 n f m h1) (@lem7050380 m n f)). Qed.
Lemma lem7050384 (m : nat) (n : nat) : (term1 m n) = (term1 m n).
Proof. exact (eq_refl (term1 m n)). Qed.
Lemma lem7050385 (n : nat) (f : nat -> nat) (m : nat) (h1 : (term72 m) = True) : (term87 m n f) = (term114 m n f).
Proof. exact (MK_COMB (@lem7050384 m n) (@lem7050381 n f m h1)). Qed.
Lemma lem7050388 (f : nat -> nat) (m : nat) (h1 : (term72 m) = True) : (term89 m f) = (term115 m f).
Proof. exact (fun_ext (fun n : nat => @lem7050385 n f m h1)). Qed.
Lemma lem7050389 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7050390 (f : nat -> nat) (m : nat) (h1 : (term72 m) = True) : (term91 m f) = (term116 m f).
Proof. exact (MK_COMB (@lem7050389) (@lem7050388 f m h1)). Qed.
Lemma lem7050395 (m : nat) (f : nat -> nat) : term117 m f.
Proof. exact (fun h0 : (term72 m) = True => @lem7050390 f m h0). Qed.
Lemma lem7050396 (m : nat) (f : nat -> nat) : term118 m f.
Proof. exact (conj (@lem7050364 m f) (@lem7050395 m f)). Qed.
Lemma lem7050398 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term119 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem7050399 (f : nat -> nat) (m : nat) : term120 f m.
Proof. exact (@lem7050398 (term91 m f) (term116 m f) (term72 m) True). Qed.
Lemma lem7050400 (f : nat -> nat) (m : nat) : (term91 m f) = (term121 f m).
Proof. exact (@lem7050399 f m (@lem7050396 m f)). Qed.
Lemma lem7050402 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem7050403 (m : nat) : (term122 m) = True.
Proof. exact (@lem7050402 (term72 m)). Qed.
Lemma lem7050408 (m : nat) (f : nat -> nat) : (term123 m f) = (term123 m f).
Proof. exact (eq_refl (term123 m f)). Qed.
Lemma lem7050409 (m : nat) (f : nat -> nat) : (term121 f m) = (term124 m f).
Proof. exact (MK_COMB (@lem7050408 m f) (@lem7050403 m)). Qed.
Lemma lem7050411 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem7050412 (m : nat) (f : nat -> nat) : (term124 m f) = (term125 m f).
Proof. exact (@lem7050411 (term125 m f)). Qed.
Lemma lem7050413 (m : nat) (f : nat -> nat) : (term121 f m) = (term125 m f).
Proof. exact (TRANS (@lem7050409 m f) (@lem7050412 m f)). Qed.
Lemma lem7050414 (m : nat) (f : nat -> nat) : (term91 m f) = (term125 m f).
Proof. exact (TRANS (@lem7050400 f m) (@lem7050413 m f)). Qed.
Lemma lem7050419 (m : nat) (n : nat) (f : nat -> nat) : (term114 m n f) = (term114 m n f).
Proof. exact (eq_refl (term114 m n f)). Qed.
Lemma lem7050420 (m : nat) (f : nat -> nat) : (term115 m f) = (term115 m f).
Proof. exact (fun_ext (fun n : nat => @lem7050419 m n f)). Qed.
Lemma lem7050421 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7050422 (m : nat) (f : nat -> nat) : (term116 m f) = (term116 m f).
Proof. exact (MK_COMB (@lem7050421) (@lem7050420 m f)). Qed.
Lemma lem7050427 (m : nat) : (term126 m) = (term126 m).
Proof. exact (eq_refl (term126 m)). Qed.
Lemma lem7050428 (m : nat) (f : nat -> nat) : (term125 m f) = (term125 m f).
Proof. exact (MK_COMB (@lem7050427 m) (@lem7050422 m f)). Qed.
Lemma lem7050429 (m : nat) (f : nat -> nat) : (term127 m f) = (term127 m f).
Proof. exact (eq_refl (term127 m f)). Qed.
Lemma lem7050430 (m : nat) (f : nat -> nat) : ((term91 m f) = (term125 m f)) = ((term91 m f) = (term125 m f)).
Proof. exact (MK_COMB (@lem7050429 m f) (@lem7050428 m f)). Qed.
Lemma lem7050431 (m : nat) (f : nat -> nat) : (term91 m f) = (term125 m f).
Proof. exact (EQ_MP (@lem7050430 m f) (@lem7050414 m f)). Qed.
Lemma lem7050432 (f : nat -> nat) : (term93 f) = (term128 f).
Proof. exact (fun_ext (fun m : nat => @lem7050431 m f)). Qed.
Lemma lem7050433 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7050434 (f : nat -> nat) : (term95 f) = (term129 f).
Proof. exact (MK_COMB (@lem7050433) (@lem7050432 f)). Qed.
Lemma lem7050435 : term97 = term130.
Proof. exact (fun_ext (fun f : nat -> nat => @lem7050434 f)). Qed.
Lemma lem7050436 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7050438 : term99 = term131.
Proof. exact (MK_COMB (@lem7050436) (@lem7050435)). Qed.
Lemma lem7050446 (m : nat) (n : nat) (f : nat -> nat) : (term114 m n f) = (term132 m n f).
Proof. exact (@lem17265 (Peano.le m n) ((term62 m n f) = (term39 m n f))). Qed.
Lemma lem7050447 (m : nat) (f : nat -> nat) : (term115 m f) = (term133 m f).
Proof. exact (fun_ext (fun n : nat => @lem7050446 m n f)). Qed.
Lemma lem7050448 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7050449 (m : nat) (f : nat -> nat) : (term116 m f) = (term134 m f).
Proof. exact (MK_COMB (@lem7050448) (@lem7050447 m f)). Qed.
Lemma lem7050451 (m : nat) : (term126 m) = (term126 m).
Proof. exact (eq_refl (term126 m)). Qed.
Lemma lem7050452 (m : nat) (f : nat -> nat) : (term125 m f) = (term135 m f).
Proof. exact (MK_COMB (@lem7050451 m) (@lem7050449 m f)). Qed.
Lemma lem7050453 (f : nat -> nat) : (term128 f) = (term136 f).
Proof. exact (fun_ext (fun m : nat => @lem7050452 m f)). Qed.
Lemma lem7050454 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7050455 (f : nat -> nat) : (term129 f) = (term137 f).
Proof. exact (MK_COMB (@lem7050454) (@lem7050453 f)). Qed.
Lemma lem7050456 : term130 = term138.
Proof. exact (fun_ext (fun f : nat -> nat => @lem7050455 f)). Qed.
Lemma lem7050457 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7050458 : term131 = term139.
Proof. exact (MK_COMB (@lem7050457) (@lem7050456)). Qed.
Lemma lem7050459 : term99 = term139.
Proof. exact (TRANS (@lem7050438) (@lem7050458)). Qed.
Lemma lem7050460 (m : nat) (n : nat) (f : nat -> nat) : (term132 m n f) = (term132 m n f).
Proof. exact (eq_refl (term132 m n f)). Qed.
Lemma lem7050461 (m : nat) (f : nat -> nat) : (term133 m f) = (term133 m f).
Proof. exact (fun_ext (fun n : nat => @lem7050460 m n f)). Qed.
Lemma lem7050462 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7050463 (m : nat) (f : nat -> nat) : (term134 m f) = (term134 m f).
Proof. exact (MK_COMB (@lem7050462) (@lem7050461 m f)). Qed.
Lemma lem7050466 (m : nat) : (term126 m) = (term126 m).
Proof. exact (eq_refl (term126 m)). Qed.
Lemma lem7050467 (m : nat) (f : nat -> nat) : (term135 m f) = (term135 m f).
Proof. exact (MK_COMB (@lem7050466 m) (@lem7050463 m f)). Qed.
Lemma lem7050468 (f : nat -> nat) : (term136 f) = (term136 f).
Proof. exact (fun_ext (fun m : nat => @lem7050467 m f)). Qed.
Lemma lem7050469 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7050470 (f : nat -> nat) : (term137 f) = (term137 f).
Proof. exact (MK_COMB (@lem7050469) (@lem7050468 f)). Qed.
Lemma lem7050471 : term138 = term138.
Proof. exact (fun_ext (fun f : nat -> nat => @lem7050470 f)). Qed.
Lemma lem7050472 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7050473 : term139 = term139.
Proof. exact (MK_COMB (@lem7050472) (@lem7050471)). Qed.
Lemma lem7050498 : term99 = term139.
Proof. exact (TRANS (@lem7050459) (@lem7050473)). Qed.
Lemma lem7050519 (m : nat) (n : nat) (f : nat -> nat) : (term132 m n f) = (term132 m n f).
Proof. exact (eq_refl (term132 m n f)). Qed.
Lemma lem7050520 (m : nat) (f : nat -> nat) : (term133 m f) = (term133 m f).
Proof. exact (fun_ext (fun n : nat => @lem7050519 m n f)). Qed.
Lemma lem7050521 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7050522 (m : nat) (f : nat -> nat) : (term134 m f) = (term134 m f).
Proof. exact (MK_COMB (@lem7050521) (@lem7050520 m f)). Qed.
Lemma lem7050537 (m : nat) : (term126 m) = (term126 m).
Proof. exact (eq_refl (term126 m)). Qed.
Lemma lem7050538 (m : nat) (f : nat -> nat) : (term135 m f) = (term135 m f).
Proof. exact (MK_COMB (@lem7050537 m) (@lem7050522 m f)). Qed.
Lemma lem7050539 (f : nat -> nat) : (term136 f) = (term136 f).
Proof. exact (fun_ext (fun m : nat => @lem7050538 m f)). Qed.
Lemma lem7050540 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7050541 (f : nat -> nat) : (term137 f) = (term137 f).
Proof. exact (MK_COMB (@lem7050540) (@lem7050539 f)). Qed.
Lemma lem7050542 : term138 = term138.
Proof. exact (fun_ext (fun f : nat -> nat => @lem7050541 f)). Qed.
Lemma lem7050543 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7050544 : term139 = term139.
Proof. exact (MK_COMB (@lem7050543) (@lem7050542)). Qed.
Lemma lem7050545 : term99 = term139.
Proof. exact (TRANS (@lem7050498) (@lem7050544)). Qed.
Lemma lem7050547 {A : Type'} (P : Prop) (Q : A -> Prop) : (term140 A P Q) = (term141 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem7050548 (P : Prop) (Q : nat -> Prop) : (term142 P Q) = (term143 P Q).
Proof. exact (@lem7050547 nat P Q). Qed.
Lemma lem7050549 (m : nat) (f : nat -> nat) : (term144 m f) = (term145 m f).
Proof. exact (@lem7050548 (term79 m) (term133 m f)). Qed.
Lemma lem7050550 (m : nat) (n : nat) (f : nat -> nat) : (term146 m f n) = (term132 m n f).
Proof. exact (eq_refl (term146 m f n)). Qed.
Lemma lem7050551 (m : nat) (f : nat -> nat) : (term147 m f) = (term133 m f).
Proof. exact (fun_ext (fun n : nat => @lem7050550 m n f)). Qed.
Lemma lem7050552 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7050553 (m : nat) (f : nat -> nat) : (term148 m f) = (term134 m f).
Proof. exact (MK_COMB (@lem7050552) (@lem7050551 m f)). Qed.
Lemma lem7050554 (m : nat) : (term126 m) = (term126 m).
Proof. exact (eq_refl (term126 m)). Qed.
Lemma lem7050555 (m : nat) (f : nat -> nat) : (term144 m f) = (term135 m f).
Proof. exact (MK_COMB (@lem7050554 m) (@lem7050553 m f)). Qed.
Lemma lem7050556 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7050557 (m : nat) (f : nat -> nat) : (term149 m f) = (term150 m f).
Proof. exact (MK_COMB (@lem7050556) (@lem7050555 m f)). Qed.
Lemma lem7050558 (m : nat) (n : nat) (f : nat -> nat) : (term146 m f n) = (term132 m n f).
Proof. exact (eq_refl (term146 m f n)). Qed.
Lemma lem7050559 (m : nat) : (term126 m) = (term126 m).
Proof. exact (eq_refl (term126 m)). Qed.
Lemma lem7050560 (m : nat) (n : nat) (f : nat -> nat) : (term151 m f n) = (term152 m n f).
Proof. exact (MK_COMB (@lem7050559 m) (@lem7050558 m n f)). Qed.
Lemma lem7050561 (m : nat) (f : nat -> nat) : (term153 m f) = (term154 m f).
Proof. exact (fun_ext (fun n : nat => @lem7050560 m n f)). Qed.
Lemma lem7050562 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7050563 (m : nat) (f : nat -> nat) : (term145 m f) = (term155 m f).
Proof. exact (MK_COMB (@lem7050562) (@lem7050561 m f)). Qed.
Lemma lem7050564 (m : nat) (f : nat -> nat) : ((term144 m f) = (term145 m f)) = ((term135 m f) = (term155 m f)).
Proof. exact (MK_COMB (@lem7050557 m f) (@lem7050563 m f)). Qed.
Lemma lem7050565 (m : nat) (f : nat -> nat) : (term135 m f) = (term155 m f).
Proof. exact (EQ_MP (@lem7050564 m f) (@lem7050549 m f)). Qed.
Lemma lem7050566 (f : nat -> nat) : (term136 f) = (term156 f).
Proof. exact (fun_ext (fun m : nat => @lem7050565 m f)). Qed.
Lemma lem7050567 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7050568 (f : nat -> nat) : (term137 f) = (term157 f).
Proof. exact (MK_COMB (@lem7050567) (@lem7050566 f)). Qed.
Lemma lem7050569 : term138 = term158.
Proof. exact (fun_ext (fun f : nat -> nat => @lem7050568 f)). Qed.
Lemma lem7050570 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7050571 : term139 = term159.
Proof. exact (MK_COMB (@lem7050570) (@lem7050569)). Qed.
Lemma lem7050572 : term99 = term159.
Proof. exact (TRANS (@lem7050545) (@lem7050571)). Qed.
Lemma lem7050574 (m : nat) (n : nat) : (Peano.le m n) = (term160 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7050575 (m : nat) : (term72 m) = (term161 m).
Proof. exact (@lem7050574 (term53 m) m). Qed.
Lemma lem7050577 (m : nat) (n : nat) : (term162 m n) = (term163 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem7050578 (m : nat) : (term164 m) = (term165 m).
Proof. exact (@lem7050577 m term166). Qed.
Lemma lem7050579 : int_le = int_le.
Proof. exact (eq_refl int_le). Qed.
Lemma lem7050580 (m : nat) : (term167 m) = (term168 m).
Proof. exact (MK_COMB (@lem7050579) (@lem7050578 m)). Qed.
Lemma lem7050581 (m : nat) : (int_of_num m) = (int_of_num m).
Proof. exact (eq_refl (int_of_num m)). Qed.
Lemma lem7050582 (m : nat) : (term161 m) = (term169 m).
Proof. exact (MK_COMB (@lem7050580 m) (@lem7050581 m)). Qed.
Lemma lem7050583 (m : nat) : (term72 m) = (term169 m).
Proof. exact (TRANS (@lem7050575 m) (@lem7050582 m)). Qed.
Lemma lem7050584 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7050585 (m : nat) : (term79 m) = (term170 m).
Proof. exact (MK_COMB (@lem7050584) (@lem7050583 m)). Qed.
Lemma lem7050586 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7050587 (m : nat) : (term126 m) = (term171 m).
Proof. exact (MK_COMB (@lem7050586) (@lem7050585 m)). Qed.
Lemma lem7050589 (m : nat) (n : nat) : (Peano.le m n) = (term160 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7050590 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7050591 (m : nat) (n : nat) : (term172 m n) = (term173 m n).
Proof. exact (MK_COMB (@lem7050590) (@lem7050589 m n)). Qed.
Lemma lem7050592 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7050593 (m : nat) (n : nat) : (term174 m n) = (term175 m n).
Proof. exact (MK_COMB (@lem7050592) (@lem7050591 m n)). Qed.
Lemma lem7050595 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem7050596 (m : nat) (n : nat) (f : nat -> nat) : ((term62 m n f) = (term39 m n f)) = ((term176 m n f) = (term177 m n f)).
Proof. exact (@lem7050595 (term62 m n f) (term39 m n f)). Qed.
Lemma lem7050600 (m : nat) (n : nat) : (term162 m n) = (term163 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem7050601 (m : nat) (n : nat) (f : nat -> nat) : (term177 m n f) = (term178 m n f).
Proof. exact (@lem7050600 (f m) (term62 m n f)). Qed.
Lemma lem7050602 (m : nat) (n : nat) (f : nat -> nat) : (term179 m n f) = (term179 m n f).
Proof. exact (eq_refl (term179 m n f)). Qed.
Lemma lem7050603 (m : nat) (n : nat) (f : nat -> nat) : ((term176 m n f) = (term177 m n f)) = ((term176 m n f) = (term178 m n f)).
Proof. exact (MK_COMB (@lem7050602 m n f) (@lem7050601 m n f)). Qed.
Lemma lem7050604 (m : nat) (n : nat) (f : nat -> nat) : ((term62 m n f) = (term39 m n f)) = ((term176 m n f) = (term178 m n f)).
Proof. exact (TRANS (@lem7050596 m n f) (@lem7050603 m n f)). Qed.
Lemma lem7050605 (m : nat) (n : nat) (f : nat -> nat) : (term132 m n f) = (term180 m n f).
Proof. exact (MK_COMB (@lem7050593 m n) (@lem7050604 m n f)). Qed.
Lemma lem7050606 (m : nat) (n : nat) (f : nat -> nat) : (term152 m n f) = (term181 m n f).
Proof. exact (MK_COMB (@lem7050587 m) (@lem7050605 m n f)). Qed.
Lemma lem7050607 (m : nat) (f : nat -> nat) : (term154 m f) = (term182 m f).
Proof. exact (fun_ext (fun n : nat => @lem7050606 m n f)). Qed.
Lemma lem7050608 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7050609 (m : nat) (f : nat -> nat) : (term155 m f) = (term183 m f).
Proof. exact (MK_COMB (@lem7050608) (@lem7050607 m f)). Qed.
Lemma lem7050610 (f : nat -> nat) : (term156 f) = (term184 f).
Proof. exact (fun_ext (fun m : nat => @lem7050609 m f)). Qed.
Lemma lem7050611 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7050612 (f : nat -> nat) : (term157 f) = (term185 f).
Proof. exact (MK_COMB (@lem7050611) (@lem7050610 f)). Qed.
Lemma lem7050613 : term158 = term186.
Proof. exact (fun_ext (fun f : nat -> nat => @lem7050612 f)). Qed.
Lemma lem7050614 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7050615 : term159 = term187.
Proof. exact (MK_COMB (@lem7050614) (@lem7050613)). Qed.
Lemma lem7050616 : term99 = term187.
Proof. exact (TRANS (@lem7050572) (@lem7050615)). Qed.
Lemma lem7050617 (m : nat) : term188 m.
Proof. exact (@lem2307535 m). Qed.
Lemma lem7050618 (m : nat) : (term188 m) = (term189 m).
Proof. exact (eq_refl (term188 m)). Qed.
Lemma lem7050619 (m : nat) : term189 m.
Proof. exact (EQ_MP (@lem7050618 m) (@lem7050617 m)). Qed.
Lemma lem7050620 (n : nat) : term188 n.
Proof. exact (@lem2307535 n). Qed.
Lemma lem7050621 (n : nat) : (term188 n) = (term189 n).
Proof. exact (eq_refl (term188 n)). Qed.
Lemma lem7050622 (n : nat) : term189 n.
Proof. exact (EQ_MP (@lem7050621 n) (@lem7050620 n)). Qed.
Lemma lem7050623 (f : nat -> nat) (m : nat) : term190 f m.
Proof. exact (@lem2307535 (f m)). Qed.
Lemma lem7050624 (f : nat -> nat) (m : nat) : (term190 f m) = (term191 f m).
Proof. exact (eq_refl (term190 f m)). Qed.
Lemma lem7050625 (f : nat -> nat) (m : nat) : term191 f m.
Proof. exact (EQ_MP (@lem7050624 f m) (@lem7050623 f m)). Qed.
Lemma lem7050626 (m : nat) (n : nat) (f : nat -> nat) : term192 m n f.
Proof. exact (@lem2307535 (term62 m n f)). Qed.
Lemma lem7050627 (m : nat) (n : nat) (f : nat -> nat) : (term192 m n f) = (term193 m n f).
Proof. exact (eq_refl (term192 m n f)). Qed.
Lemma lem7050628 (m : nat) (n : nat) (f : nat -> nat) : term193 m n f.
Proof. exact (EQ_MP (@lem7050627 m n f) (@lem7050626 m n f)). Qed.
Lemma lem7050629 (_94148 : int) (_94149 : int) (_94150 : int) (_94151 : int) : (term194 _94148 _94149 _94150 _94151) = (term195 _94148 _94149 _94150 _94151).
Proof. exact (@lem2318604 (term195 _94148 _94149 _94150 _94151)). Qed.
Lemma lem7050653 (_94148 : int) : (term196 _94148) = (term197 _94148).
Proof. exact (@lem16933 (term197 _94148)). Qed.
Lemma lem7050656 (_94148 : int) (_94149 : int) : (term198 _94148 _94149) = (int_le _94148 _94149).
Proof. exact (@lem16933 (int_le _94148 _94149)). Qed.
Lemma lem7050657 (_94150 : int) (_94151 : int) : (term199 _94150 _94151) = (term199 _94150 _94151).
Proof. exact (eq_refl (term199 _94150 _94151)). Qed.
Lemma lem7050658 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7050659 (_94148 : int) (_94149 : int) : (term200 _94148 _94149) = (term201 _94148 _94149).
Proof. exact (MK_COMB (@lem7050658) (@lem7050656 _94148 _94149)). Qed.
Lemma lem7050660 (_94148 : int) (_94149 : int) (_94150 : int) (_94151 : int) : (term202 _94148 _94149 _94150 _94151) = (term203 _94148 _94149 _94150 _94151).
Proof. exact (MK_COMB (@lem7050659 _94148 _94149) (@lem7050657 _94150 _94151)). Qed.
Lemma lem7050661 (_94148 : int) (_94149 : int) (_94150 : int) (_94151 : int) : (term204 _94148 _94149 _94150 _94151) = (term202 _94148 _94149 _94150 _94151).
Proof. exact (@lem17160 (term205 _94148 _94149) (_94151 = (int_add _94150 _94151))). Qed.
Lemma lem7050662 (_94148 : int) (_94149 : int) (_94150 : int) (_94151 : int) : (term204 _94148 _94149 _94150 _94151) = (term203 _94148 _94149 _94150 _94151).
Proof. exact (TRANS (@lem7050661 _94148 _94149 _94150 _94151) (@lem7050660 _94148 _94149 _94150 _94151)). Qed.
Lemma lem7050663 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7050664 (_94148 : int) : (term206 _94148) = (term207 _94148).
Proof. exact (MK_COMB (@lem7050663) (@lem7050653 _94148)). Qed.
Lemma lem7050665 (_94148 : int) (_94149 : int) (_94150 : int) (_94151 : int) : (term208 _94148 _94149 _94150 _94151) = (term209 _94148 _94149 _94150 _94151).
Proof. exact (MK_COMB (@lem7050664 _94148) (@lem7050662 _94148 _94149 _94150 _94151)). Qed.
Lemma lem7050666 (_94148 : int) (_94149 : int) (_94150 : int) (_94151 : int) : (term210 _94148 _94149 _94150 _94151) = (term208 _94148 _94149 _94150 _94151).
Proof. exact (@lem17160 (term211 _94148) (term212 _94148 _94149 _94150 _94151)). Qed.
Lemma lem7050667 (_94148 : int) (_94149 : int) (_94150 : int) (_94151 : int) : (term210 _94148 _94149 _94150 _94151) = (term209 _94148 _94149 _94150 _94151).
Proof. exact (TRANS (@lem7050666 _94148 _94149 _94150 _94151) (@lem7050665 _94148 _94149 _94150 _94151)). Qed.
Lemma lem7050669 (_94151 : int) : (term213 _94151) = (term213 _94151).
Proof. exact (eq_refl (term213 _94151)). Qed.
Lemma lem7050670 (_94148 : int) (_94149 : int) (_94150 : int) (_94151 : int) : (term214 _94148 _94149 _94150 _94151) = (term215 _94148 _94149 _94150 _94151).
Proof. exact (MK_COMB (@lem7050669 _94151) (@lem7050667 _94148 _94149 _94150 _94151)). Qed.
Lemma lem7050671 (_94148 : int) (_94149 : int) (_94150 : int) (_94151 : int) : (term216 _94148 _94149 _94150 _94151) = (term214 _94148 _94149 _94150 _94151).
Proof. exact (@lem17362 (term217 _94151) (term218 _94148 _94149 _94150 _94151)). Qed.
Lemma lem7050672 (_94148 : int) (_94149 : int) (_94150 : int) (_94151 : int) : (term216 _94148 _94149 _94150 _94151) = (term215 _94148 _94149 _94150 _94151).
Proof. exact (TRANS (@lem7050671 _94148 _94149 _94150 _94151) (@lem7050670 _94148 _94149 _94150 _94151)). Qed.
Lemma lem7050674 (_94150 : int) : (term213 _94150) = (term213 _94150).
Proof. exact (eq_refl (term213 _94150)). Qed.
Lemma lem7050675 (_94148 : int) (_94149 : int) (_94150 : int) (_94151 : int) : (term219 _94148 _94149 _94150 _94151) = (term220 _94148 _94149 _94150 _94151).
Proof. exact (MK_COMB (@lem7050674 _94150) (@lem7050672 _94148 _94149 _94150 _94151)). Qed.
Lemma lem7050676 (_94148 : int) (_94149 : int) (_94150 : int) (_94151 : int) : (term221 _94148 _94149 _94150 _94151) = (term219 _94148 _94149 _94150 _94151).
Proof. exact (@lem17362 (term217 _94150) (term222 _94148 _94149 _94150 _94151)). Qed.
Lemma lem7050677 (_94148 : int) (_94149 : int) (_94150 : int) (_94151 : int) : (term221 _94148 _94149 _94150 _94151) = (term220 _94148 _94149 _94150 _94151).
Proof. exact (TRANS (@lem7050676 _94148 _94149 _94150 _94151) (@lem7050675 _94148 _94149 _94150 _94151)). Qed.
Lemma lem7050679 (_94149 : int) : (term213 _94149) = (term213 _94149).
Proof. exact (eq_refl (term213 _94149)). Qed.
Lemma lem7050680 (_94148 : int) (_94149 : int) (_94150 : int) (_94151 : int) : (term223 _94148 _94149 _94150 _94151) = (term224 _94148 _94149 _94150 _94151).
Proof. exact (MK_COMB (@lem7050679 _94149) (@lem7050677 _94148 _94149 _94150 _94151)). Qed.
Lemma lem7050681 (_94148 : int) (_94149 : int) (_94150 : int) (_94151 : int) : (term225 _94148 _94149 _94150 _94151) = (term223 _94148 _94149 _94150 _94151).
Proof. exact (@lem17362 (term217 _94149) (term226 _94148 _94149 _94150 _94151)). Qed.
Lemma lem7050682 (_94148 : int) (_94149 : int) (_94150 : int) (_94151 : int) : (term225 _94148 _94149 _94150 _94151) = (term224 _94148 _94149 _94150 _94151).
Proof. exact (TRANS (@lem7050681 _94148 _94149 _94150 _94151) (@lem7050680 _94148 _94149 _94150 _94151)). Qed.
Lemma lem7050684 (_94148 : int) : (term213 _94148) = (term213 _94148).
Proof. exact (eq_refl (term213 _94148)). Qed.
Lemma lem7050685 (_94148 : int) (_94149 : int) (_94150 : int) (_94151 : int) : (term227 _94148 _94149 _94150 _94151) = (term228 _94148 _94149 _94150 _94151).
Proof. exact (MK_COMB (@lem7050684 _94148) (@lem7050682 _94148 _94149 _94150 _94151)). Qed.
Lemma lem7050686 (_94148 : int) (_94149 : int) (_94150 : int) (_94151 : int) : (term229 _94148 _94149 _94150 _94151) = (term227 _94148 _94149 _94150 _94151).
Proof. exact (@lem17362 (term217 _94148) (term230 _94148 _94149 _94150 _94151)). Qed.
Lemma lem7050716 (_94148 : int) (_94149 : int) (_94150 : int) (_94151 : int) : (term229 _94148 _94149 _94150 _94151) = (term228 _94148 _94149 _94150 _94151).
Proof. exact (TRANS (@lem7050686 _94148 _94149 _94150 _94151) (@lem7050685 _94148 _94149 _94150 _94151)). Qed.
Lemma lem7050719 (x : int) (y : int) : (int_le x y) = (term231 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7050720 (_94148 : int) : (term217 _94148) = (term232 _94148).
Proof. exact (@lem7050719 term233 _94148). Qed.
Lemma lem7050722 (n : nat) : (term234 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7050723 : term235 = term236.
Proof. exact (@lem7050722 (NUMERAL 0)). Qed.
Lemma lem7050724 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7050725 : term237 = term238.
Proof. exact (MK_COMB (@lem7050724) (@lem7050723)). Qed.
Lemma lem7050726 (_94148 : int) : (real_of_int _94148) = (real_of_int _94148).
Proof. exact (eq_refl (real_of_int _94148)). Qed.
Lemma lem7050727 (_94148 : int) : (term232 _94148) = (term239 _94148).
Proof. exact (MK_COMB (@lem7050725) (@lem7050726 _94148)). Qed.
Lemma lem7050729 (_94148 : int) : (term217 _94148) = (term239 _94148).
Proof. exact (TRANS (@lem7050720 _94148) (@lem7050727 _94148)). Qed.
Lemma lem7050732 (x : int) (y : int) : (int_le x y) = (term231 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7050733 (_94149 : int) : (term217 _94149) = (term232 _94149).
Proof. exact (@lem7050732 term233 _94149). Qed.
Lemma lem7050735 (n : nat) : (term234 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7050736 : term235 = term236.
Proof. exact (@lem7050735 (NUMERAL 0)). Qed.
Lemma lem7050737 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7050738 : term237 = term238.
Proof. exact (MK_COMB (@lem7050737) (@lem7050736)). Qed.
Lemma lem7050739 (_94149 : int) : (real_of_int _94149) = (real_of_int _94149).
Proof. exact (eq_refl (real_of_int _94149)). Qed.
Lemma lem7050740 (_94149 : int) : (term232 _94149) = (term239 _94149).
Proof. exact (MK_COMB (@lem7050738) (@lem7050739 _94149)). Qed.
Lemma lem7050742 (_94149 : int) : (term217 _94149) = (term239 _94149).
Proof. exact (TRANS (@lem7050733 _94149) (@lem7050740 _94149)). Qed.
Lemma lem7050745 (x : int) (y : int) : (int_le x y) = (term231 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7050746 (_94150 : int) : (term217 _94150) = (term232 _94150).
Proof. exact (@lem7050745 term233 _94150). Qed.
Lemma lem7050748 (n : nat) : (term234 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7050749 : term235 = term236.
Proof. exact (@lem7050748 (NUMERAL 0)). Qed.
Lemma lem7050750 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7050751 : term237 = term238.
Proof. exact (MK_COMB (@lem7050750) (@lem7050749)). Qed.
Lemma lem7050752 (_94150 : int) : (real_of_int _94150) = (real_of_int _94150).
Proof. exact (eq_refl (real_of_int _94150)). Qed.
Lemma lem7050753 (_94150 : int) : (term232 _94150) = (term239 _94150).
Proof. exact (MK_COMB (@lem7050751) (@lem7050752 _94150)). Qed.
Lemma lem7050755 (_94150 : int) : (term217 _94150) = (term239 _94150).
Proof. exact (TRANS (@lem7050746 _94150) (@lem7050753 _94150)). Qed.
Lemma lem7050758 (x : int) (y : int) : (int_le x y) = (term231 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7050759 (_94151 : int) : (term217 _94151) = (term232 _94151).
Proof. exact (@lem7050758 term233 _94151). Qed.
Lemma lem7050761 (n : nat) : (term234 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7050762 : term235 = term236.
Proof. exact (@lem7050761 (NUMERAL 0)). Qed.
Lemma lem7050763 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7050764 : term237 = term238.
Proof. exact (MK_COMB (@lem7050763) (@lem7050762)). Qed.
Lemma lem7050765 (_94151 : int) : (real_of_int _94151) = (real_of_int _94151).
Proof. exact (eq_refl (real_of_int _94151)). Qed.
Lemma lem7050766 (_94151 : int) : (term232 _94151) = (term239 _94151).
Proof. exact (MK_COMB (@lem7050764) (@lem7050765 _94151)). Qed.
Lemma lem7050768 (_94151 : int) : (term217 _94151) = (term239 _94151).
Proof. exact (TRANS (@lem7050759 _94151) (@lem7050766 _94151)). Qed.
Lemma lem7050771 (x : int) (y : int) : (int_le x y) = (term231 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7050772 (_94148 : int) : (term197 _94148) = (term240 _94148).
Proof. exact (@lem7050771 (term241 _94148) _94148). Qed.
Lemma lem7050774 (x : int) (y : int) : (term242 x y) = (term243 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7050775 (_94148 : int) : (term244 _94148) = (term245 _94148).
Proof. exact (@lem7050774 _94148 term246). Qed.
Lemma lem7050777 (n : nat) : (term234 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7050778 : term247 = term248.
Proof. exact (@lem7050777 term166). Qed.
Lemma lem7050779 (_94148 : int) : (term249 _94148) = (term249 _94148).
Proof. exact (eq_refl (term249 _94148)). Qed.
Lemma lem7050780 (_94148 : int) : (term245 _94148) = (term250 _94148).
Proof. exact (MK_COMB (@lem7050779 _94148) (@lem7050778)). Qed.
Lemma lem7050781 (_94148 : int) : (term244 _94148) = (term250 _94148).
Proof. exact (TRANS (@lem7050775 _94148) (@lem7050780 _94148)). Qed.
Lemma lem7050782 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7050783 (_94148 : int) : (term251 _94148) = (term252 _94148).
Proof. exact (MK_COMB (@lem7050782) (@lem7050781 _94148)). Qed.
Lemma lem7050784 (_94148 : int) : (real_of_int _94148) = (real_of_int _94148).
Proof. exact (eq_refl (real_of_int _94148)). Qed.
Lemma lem7050785 (_94148 : int) : (term240 _94148) = (term253 _94148).
Proof. exact (MK_COMB (@lem7050783 _94148) (@lem7050784 _94148)). Qed.
Lemma lem7050787 (_94148 : int) : (term197 _94148) = (term253 _94148).
Proof. exact (TRANS (@lem7050772 _94148) (@lem7050785 _94148)). Qed.
Lemma lem7050790 (x : int) (y : int) : (int_le x y) = (term231 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7050792 (_94148 : int) (_94149 : int) : (int_le _94148 _94149) = (term231 _94148 _94149).
Proof. exact (@lem7050790 _94148 _94149). Qed.
Lemma lem7050794 (y : int) (x : int) : (term254 x y) = (term255 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem7050795 (_94150 : int) (_94151 : int) : (term199 _94150 _94151) = (term256 _94150 _94151).
Proof. exact (@lem7050794 (int_add _94150 _94151) _94151). Qed.
Lemma lem7050797 (x : int) (y : int) : (int_le x y) = (term231 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7050798 (_94150 : int) (_94151 : int) : (term257 _94150 _94151) = (term258 _94150 _94151).
Proof. exact (@lem7050797 (term241 _94151) (int_add _94150 _94151)). Qed.
Lemma lem7050800 (x : int) (y : int) : (term242 x y) = (term243 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7050801 (_94151 : int) : (term244 _94151) = (term245 _94151).
Proof. exact (@lem7050800 _94151 term246). Qed.
Lemma lem7050803 (n : nat) : (term234 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7050804 : term247 = term248.
Proof. exact (@lem7050803 term166). Qed.
Lemma lem7050805 (_94151 : int) : (term249 _94151) = (term249 _94151).
Proof. exact (eq_refl (term249 _94151)). Qed.
Lemma lem7050806 (_94151 : int) : (term245 _94151) = (term250 _94151).
Proof. exact (MK_COMB (@lem7050805 _94151) (@lem7050804)). Qed.
Lemma lem7050807 (_94151 : int) : (term244 _94151) = (term250 _94151).
Proof. exact (TRANS (@lem7050801 _94151) (@lem7050806 _94151)). Qed.
Lemma lem7050808 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7050809 (_94151 : int) : (term251 _94151) = (term252 _94151).
Proof. exact (MK_COMB (@lem7050808) (@lem7050807 _94151)). Qed.
Lemma lem7050811 (x : int) (y : int) : (term242 x y) = (term243 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7050812 (_94150 : int) (_94151 : int) : (term242 _94150 _94151) = (term243 _94150 _94151).
Proof. exact (@lem7050811 _94150 _94151). Qed.
Lemma lem7050813 (_94150 : int) (_94151 : int) : (term258 _94150 _94151) = (term259 _94150 _94151).
Proof. exact (MK_COMB (@lem7050809 _94151) (@lem7050812 _94150 _94151)). Qed.
Lemma lem7050814 (_94150 : int) (_94151 : int) : (term257 _94150 _94151) = (term259 _94150 _94151).
Proof. exact (TRANS (@lem7050798 _94150 _94151) (@lem7050813 _94150 _94151)). Qed.
Lemma lem7050815 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7050816 (_94150 : int) (_94151 : int) : (term260 _94150 _94151) = (term261 _94150 _94151).
Proof. exact (MK_COMB (@lem7050815) (@lem7050814 _94150 _94151)). Qed.
Lemma lem7050818 (x : int) (y : int) : (int_le x y) = (term231 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7050819 (_94150 : int) (_94151 : int) : (term262 _94150 _94151) = (term263 _94150 _94151).
Proof. exact (@lem7050818 (term264 _94150 _94151) _94151). Qed.
Lemma lem7050821 (x : int) (y : int) : (term242 x y) = (term243 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7050822 (_94150 : int) (_94151 : int) : (term265 _94150 _94151) = (term266 _94150 _94151).
Proof. exact (@lem7050821 (int_add _94150 _94151) term246). Qed.
Lemma lem7050824 (x : int) (y : int) : (term242 x y) = (term243 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7050825 (_94150 : int) (_94151 : int) : (term242 _94150 _94151) = (term243 _94150 _94151).
Proof. exact (@lem7050824 _94150 _94151). Qed.
Lemma lem7050826 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7050827 (_94150 : int) (_94151 : int) : (term267 _94150 _94151) = (term268 _94150 _94151).
Proof. exact (MK_COMB (@lem7050826) (@lem7050825 _94150 _94151)). Qed.
Lemma lem7050829 (n : nat) : (term234 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7050830 : term247 = term248.
Proof. exact (@lem7050829 term166). Qed.
Lemma lem7050831 (_94150 : int) (_94151 : int) : (term266 _94150 _94151) = (term269 _94150 _94151).
Proof. exact (MK_COMB (@lem7050827 _94150 _94151) (@lem7050830)). Qed.
Lemma lem7050832 (_94150 : int) (_94151 : int) : (term265 _94150 _94151) = (term269 _94150 _94151).
Proof. exact (TRANS (@lem7050822 _94150 _94151) (@lem7050831 _94150 _94151)). Qed.
Lemma lem7050833 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7050834 (_94150 : int) (_94151 : int) : (term270 _94150 _94151) = (term271 _94150 _94151).
Proof. exact (MK_COMB (@lem7050833) (@lem7050832 _94150 _94151)). Qed.
Lemma lem7050835 (_94151 : int) : (real_of_int _94151) = (real_of_int _94151).
Proof. exact (eq_refl (real_of_int _94151)). Qed.
Lemma lem7050836 (_94150 : int) (_94151 : int) : (term263 _94150 _94151) = (term272 _94150 _94151).
Proof. exact (MK_COMB (@lem7050834 _94150 _94151) (@lem7050835 _94151)). Qed.
Lemma lem7050837 (_94150 : int) (_94151 : int) : (term262 _94150 _94151) = (term272 _94150 _94151).
Proof. exact (TRANS (@lem7050819 _94150 _94151) (@lem7050836 _94150 _94151)). Qed.
Lemma lem7050838 (_94150 : int) (_94151 : int) : (term256 _94150 _94151) = (term273 _94150 _94151).
Proof. exact (MK_COMB (@lem7050816 _94150 _94151) (@lem7050837 _94150 _94151)). Qed.
Lemma lem7050839 (_94150 : int) (_94151 : int) : (term199 _94150 _94151) = (term273 _94150 _94151).
Proof. exact (TRANS (@lem7050795 _94150 _94151) (@lem7050838 _94150 _94151)). Qed.
Lemma lem7050840 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7050841 (_94148 : int) (_94149 : int) : (term201 _94148 _94149) = (term274 _94148 _94149).
Proof. exact (MK_COMB (@lem7050840) (@lem7050792 _94148 _94149)). Qed.
Lemma lem7050842 (_94148 : int) (_94149 : int) (_94150 : int) (_94151 : int) : (term203 _94148 _94149 _94150 _94151) = (term275 _94148 _94149 _94150 _94151).
Proof. exact (MK_COMB (@lem7050841 _94148 _94149) (@lem7050839 _94150 _94151)). Qed.
Lemma lem7050843 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7050844 (_94148 : int) : (term207 _94148) = (term276 _94148).
Proof. exact (MK_COMB (@lem7050843) (@lem7050787 _94148)). Qed.
Lemma lem7050845 (_94148 : int) (_94149 : int) (_94150 : int) (_94151 : int) : (term209 _94148 _94149 _94150 _94151) = (term277 _94148 _94149 _94150 _94151).
Proof. exact (MK_COMB (@lem7050844 _94148) (@lem7050842 _94148 _94149 _94150 _94151)). Qed.
Lemma lem7050846 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7050847 (_94151 : int) : (term213 _94151) = (term278 _94151).
Proof. exact (MK_COMB (@lem7050846) (@lem7050768 _94151)). Qed.
Lemma lem7050848 (_94148 : int) (_94149 : int) (_94150 : int) (_94151 : int) : (term215 _94148 _94149 _94150 _94151) = (term279 _94148 _94149 _94150 _94151).
Proof. exact (MK_COMB (@lem7050847 _94151) (@lem7050845 _94148 _94149 _94150 _94151)). Qed.
Lemma lem7050849 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7050850 (_94150 : int) : (term213 _94150) = (term278 _94150).
Proof. exact (MK_COMB (@lem7050849) (@lem7050755 _94150)). Qed.
Lemma lem7050851 (_94148 : int) (_94149 : int) (_94150 : int) (_94151 : int) : (term220 _94148 _94149 _94150 _94151) = (term280 _94148 _94149 _94150 _94151).
Proof. exact (MK_COMB (@lem7050850 _94150) (@lem7050848 _94148 _94149 _94150 _94151)). Qed.
Lemma lem7050852 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7050853 (_94149 : int) : (term213 _94149) = (term278 _94149).
Proof. exact (MK_COMB (@lem7050852) (@lem7050742 _94149)). Qed.
Lemma lem7050854 (_94148 : int) (_94149 : int) (_94150 : int) (_94151 : int) : (term224 _94148 _94149 _94150 _94151) = (term281 _94148 _94149 _94150 _94151).
Proof. exact (MK_COMB (@lem7050853 _94149) (@lem7050851 _94148 _94149 _94150 _94151)). Qed.
Lemma lem7050855 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7050856 (_94148 : int) : (term213 _94148) = (term278 _94148).
Proof. exact (MK_COMB (@lem7050855) (@lem7050729 _94148)). Qed.
Lemma lem7050857 (_94148 : int) (_94149 : int) (_94150 : int) (_94151 : int) : (term228 _94148 _94149 _94150 _94151) = (term282 _94148 _94149 _94150 _94151).
Proof. exact (MK_COMB (@lem7050856 _94148) (@lem7050854 _94148 _94149 _94150 _94151)). Qed.
Lemma lem7050858 (_94148 : int) (_94149 : int) (_94150 : int) (_94151 : int) : (term229 _94148 _94149 _94150 _94151) = (term282 _94148 _94149 _94150 _94151).
Proof. exact (TRANS (@lem7050716 _94148 _94149 _94150 _94151) (@lem7050857 _94148 _94149 _94150 _94151)). Qed.
Lemma lem7050862 (t : Prop) : (term283 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7050938 (_94148 : int) (_94149 : int) (_94150 : int) (_94151 : int) : (term284 _94148 _94149 _94150 _94151) = (term282 _94148 _94149 _94150 _94151).
Proof. exact (@lem7050862 (term282 _94148 _94149 _94150 _94151)). Qed.
Lemma lem7050939 (_94148 : int) : (term239 _94148) = (term285 _94148).
Proof. exact (@lem1988287 (real_of_int _94148) term236). Qed.
Lemma lem7050945 (_94148 : int) : (term286 _94148) = (term287 _94148).
Proof. exact (@lem1982792 (real_of_int _94148) term236). Qed.
Lemma lem7050947 (x : nat) : (real_of_num x) = (term288 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7050948 : term236 = term289.
Proof. exact (@lem7050947 (NUMERAL 0)). Qed.
Lemma lem7050950 (x : nat) : (term290 x) = (term291 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7050951 : term292 = term293.
Proof. exact (@lem7050950 term166). Qed.
Lemma lem7050952 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7050953 : term294 = term295.
Proof. exact (MK_COMB (@lem7050952) (@lem7050951)). Qed.
Lemma lem7050954 : term296 = term297.
Proof. exact (MK_COMB (@lem7050953) (@lem7050948)). Qed.
Lemma lem7050955 : term297 = term298.
Proof. exact (@lem1981613 term292 term236 term248 term248). Qed.
Lemma lem7050957 (m : nat) (n : nat) : (term299 m n) = (term300 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7050958 : term301 = term302.
Proof. exact (@lem7050957 term166 term166). Qed.
Lemma lem7050959 : (term303 = (BIT1 0)) = (term304 = term166).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7050960 : term304 = term166.
Proof. exact (EQ_MP (@lem7050959) (@lem940073)). Qed.
Lemma lem7050961 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7050962 : term302 = term248.
Proof. exact (MK_COMB (@lem7050961) (@lem7050960)). Qed.
Lemma lem7050963 : term301 = term248.
Proof. exact (TRANS (@lem7050958) (@lem7050962)). Qed.
Lemma lem7050965 (x : nat) : (term305 x) = term236.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7050966 : term296 = term236.
Proof. exact (@lem7050965 term166). Qed.
Lemma lem7050967 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7050968 : term306 = term307.
Proof. exact (MK_COMB (@lem7050967) (@lem7050966)). Qed.
Lemma lem7050969 : term298 = term289.
Proof. exact (MK_COMB (@lem7050968) (@lem7050963)). Qed.
Lemma lem7050970 : term297 = term289.
Proof. exact (TRANS (@lem7050955) (@lem7050969)). Qed.
Lemma lem7050971 : term296 = term289.
Proof. exact (TRANS (@lem7050954) (@lem7050970)). Qed.
Lemma lem7050973 (x : real) : (term308 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7050974 : term289 = term236.
Proof. exact (@lem7050973 term236). Qed.
Lemma lem7050975 : term296 = term236.
Proof. exact (TRANS (@lem7050971) (@lem7050974)). Qed.
Lemma lem7050976 (_94148 : int) : (term249 _94148) = (term249 _94148).
Proof. exact (eq_refl (term249 _94148)). Qed.
Lemma lem7050977 (_94148 : int) : (term287 _94148) = (term309 _94148).
Proof. exact (MK_COMB (@lem7050976 _94148) (@lem7050975)). Qed.
Lemma lem7050978 (_94148 : int) : (term309 _94148) = (real_of_int _94148).
Proof. exact (@lem1982723 (real_of_int _94148)). Qed.
Lemma lem7050979 (_94148 : int) : (term287 _94148) = (real_of_int _94148).
Proof. exact (TRANS (@lem7050977 _94148) (@lem7050978 _94148)). Qed.
Lemma lem7050981 (_94148 : int) : (term286 _94148) = (real_of_int _94148).
Proof. exact (TRANS (@lem7050945 _94148) (@lem7050979 _94148)). Qed.
Lemma lem7050982 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7050983 (_94148 : int) : (term310 _94148) = (term311 _94148).
Proof. exact (MK_COMB (@lem7050982) (@lem7050981 _94148)). Qed.
Lemma lem7050984 : term236 = term236.
Proof. exact (eq_refl term236). Qed.
Lemma lem7050985 (_94148 : int) : (term285 _94148) = (term312 _94148).
Proof. exact (MK_COMB (@lem7050983 _94148) (@lem7050984)). Qed.
Lemma lem7050986 (_94148 : int) : (term239 _94148) = (term312 _94148).
Proof. exact (TRANS (@lem7050939 _94148) (@lem7050985 _94148)). Qed.
Lemma lem7050987 (_94149 : int) : (term239 _94149) = (term285 _94149).
Proof. exact (@lem1988287 (real_of_int _94149) term236). Qed.
Lemma lem7050993 (_94149 : int) : (term286 _94149) = (term287 _94149).
Proof. exact (@lem1982792 (real_of_int _94149) term236). Qed.
Lemma lem7050995 (x : nat) : (real_of_num x) = (term288 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7050996 : term236 = term289.
Proof. exact (@lem7050995 (NUMERAL 0)). Qed.
Lemma lem7050998 (x : nat) : (term290 x) = (term291 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7050999 : term292 = term293.
Proof. exact (@lem7050998 term166). Qed.
Lemma lem7051000 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7051001 : term294 = term295.
Proof. exact (MK_COMB (@lem7051000) (@lem7050999)). Qed.
Lemma lem7051002 : term296 = term297.
Proof. exact (MK_COMB (@lem7051001) (@lem7050996)). Qed.
Lemma lem7051003 : term297 = term298.
Proof. exact (@lem1981613 term292 term236 term248 term248). Qed.
Lemma lem7051005 (m : nat) (n : nat) : (term299 m n) = (term300 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7051006 : term301 = term302.
Proof. exact (@lem7051005 term166 term166). Qed.
Lemma lem7051007 : (term303 = (BIT1 0)) = (term304 = term166).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7051008 : term304 = term166.
Proof. exact (EQ_MP (@lem7051007) (@lem940073)). Qed.
Lemma lem7051009 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7051010 : term302 = term248.
Proof. exact (MK_COMB (@lem7051009) (@lem7051008)). Qed.
Lemma lem7051011 : term301 = term248.
Proof. exact (TRANS (@lem7051006) (@lem7051010)). Qed.
Lemma lem7051013 (x : nat) : (term305 x) = term236.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7051014 : term296 = term236.
Proof. exact (@lem7051013 term166). Qed.
Lemma lem7051015 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7051016 : term306 = term307.
Proof. exact (MK_COMB (@lem7051015) (@lem7051014)). Qed.
Lemma lem7051017 : term298 = term289.
Proof. exact (MK_COMB (@lem7051016) (@lem7051011)). Qed.
Lemma lem7051018 : term297 = term289.
Proof. exact (TRANS (@lem7051003) (@lem7051017)). Qed.
Lemma lem7051019 : term296 = term289.
Proof. exact (TRANS (@lem7051002) (@lem7051018)). Qed.
Lemma lem7051021 (x : real) : (term308 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7051022 : term289 = term236.
Proof. exact (@lem7051021 term236). Qed.
Lemma lem7051023 : term296 = term236.
Proof. exact (TRANS (@lem7051019) (@lem7051022)). Qed.
Lemma lem7051024 (_94149 : int) : (term249 _94149) = (term249 _94149).
Proof. exact (eq_refl (term249 _94149)). Qed.
Lemma lem7051025 (_94149 : int) : (term287 _94149) = (term309 _94149).
Proof. exact (MK_COMB (@lem7051024 _94149) (@lem7051023)). Qed.
Lemma lem7051026 (_94149 : int) : (term309 _94149) = (real_of_int _94149).
Proof. exact (@lem1982723 (real_of_int _94149)). Qed.
Lemma lem7051027 (_94149 : int) : (term287 _94149) = (real_of_int _94149).
Proof. exact (TRANS (@lem7051025 _94149) (@lem7051026 _94149)). Qed.
Lemma lem7051029 (_94149 : int) : (term286 _94149) = (real_of_int _94149).
Proof. exact (TRANS (@lem7050993 _94149) (@lem7051027 _94149)). Qed.
Lemma lem7051030 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7051031 (_94149 : int) : (term310 _94149) = (term311 _94149).
Proof. exact (MK_COMB (@lem7051030) (@lem7051029 _94149)). Qed.
Lemma lem7051032 : term236 = term236.
Proof. exact (eq_refl term236). Qed.
Lemma lem7051033 (_94149 : int) : (term285 _94149) = (term312 _94149).
Proof. exact (MK_COMB (@lem7051031 _94149) (@lem7051032)). Qed.
Lemma lem7051034 (_94149 : int) : (term239 _94149) = (term312 _94149).
Proof. exact (TRANS (@lem7050987 _94149) (@lem7051033 _94149)). Qed.
Lemma lem7051035 (_94150 : int) : (term239 _94150) = (term285 _94150).
Proof. exact (@lem1988287 (real_of_int _94150) term236). Qed.
Lemma lem7051041 (_94150 : int) : (term286 _94150) = (term287 _94150).
Proof. exact (@lem1982792 (real_of_int _94150) term236). Qed.
Lemma lem7051043 (x : nat) : (real_of_num x) = (term288 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7051044 : term236 = term289.
Proof. exact (@lem7051043 (NUMERAL 0)). Qed.
Lemma lem7051046 (x : nat) : (term290 x) = (term291 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7051047 : term292 = term293.
Proof. exact (@lem7051046 term166). Qed.
Lemma lem7051048 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7051049 : term294 = term295.
Proof. exact (MK_COMB (@lem7051048) (@lem7051047)). Qed.
Lemma lem7051050 : term296 = term297.
Proof. exact (MK_COMB (@lem7051049) (@lem7051044)). Qed.
Lemma lem7051051 : term297 = term298.
Proof. exact (@lem1981613 term292 term236 term248 term248). Qed.
Lemma lem7051053 (m : nat) (n : nat) : (term299 m n) = (term300 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7051054 : term301 = term302.
Proof. exact (@lem7051053 term166 term166). Qed.
Lemma lem7051055 : (term303 = (BIT1 0)) = (term304 = term166).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7051056 : term304 = term166.
Proof. exact (EQ_MP (@lem7051055) (@lem940073)). Qed.
Lemma lem7051057 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7051058 : term302 = term248.
Proof. exact (MK_COMB (@lem7051057) (@lem7051056)). Qed.
Lemma lem7051059 : term301 = term248.
Proof. exact (TRANS (@lem7051054) (@lem7051058)). Qed.
Lemma lem7051061 (x : nat) : (term305 x) = term236.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7051062 : term296 = term236.
Proof. exact (@lem7051061 term166). Qed.
Lemma lem7051063 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7051064 : term306 = term307.
Proof. exact (MK_COMB (@lem7051063) (@lem7051062)). Qed.
Lemma lem7051065 : term298 = term289.
Proof. exact (MK_COMB (@lem7051064) (@lem7051059)). Qed.
Lemma lem7051066 : term297 = term289.
Proof. exact (TRANS (@lem7051051) (@lem7051065)). Qed.
Lemma lem7051067 : term296 = term289.
Proof. exact (TRANS (@lem7051050) (@lem7051066)). Qed.
Lemma lem7051069 (x : real) : (term308 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7051070 : term289 = term236.
Proof. exact (@lem7051069 term236). Qed.
Lemma lem7051071 : term296 = term236.
Proof. exact (TRANS (@lem7051067) (@lem7051070)). Qed.
Lemma lem7051072 (_94150 : int) : (term249 _94150) = (term249 _94150).
Proof. exact (eq_refl (term249 _94150)). Qed.
Lemma lem7051073 (_94150 : int) : (term287 _94150) = (term309 _94150).
Proof. exact (MK_COMB (@lem7051072 _94150) (@lem7051071)). Qed.
Lemma lem7051074 (_94150 : int) : (term309 _94150) = (real_of_int _94150).
Proof. exact (@lem1982723 (real_of_int _94150)). Qed.
Lemma lem7051075 (_94150 : int) : (term287 _94150) = (real_of_int _94150).
Proof. exact (TRANS (@lem7051073 _94150) (@lem7051074 _94150)). Qed.
Lemma lem7051077 (_94150 : int) : (term286 _94150) = (real_of_int _94150).
Proof. exact (TRANS (@lem7051041 _94150) (@lem7051075 _94150)). Qed.
Lemma lem7051078 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7051079 (_94150 : int) : (term310 _94150) = (term311 _94150).
Proof. exact (MK_COMB (@lem7051078) (@lem7051077 _94150)). Qed.
Lemma lem7051080 : term236 = term236.
Proof. exact (eq_refl term236). Qed.
Lemma lem7051081 (_94150 : int) : (term285 _94150) = (term312 _94150).
Proof. exact (MK_COMB (@lem7051079 _94150) (@lem7051080)). Qed.
Lemma lem7051082 (_94150 : int) : (term239 _94150) = (term312 _94150).
Proof. exact (TRANS (@lem7051035 _94150) (@lem7051081 _94150)). Qed.
Lemma lem7051083 (_94151 : int) : (term239 _94151) = (term285 _94151).
Proof. exact (@lem1988287 (real_of_int _94151) term236). Qed.
Lemma lem7051089 (_94151 : int) : (term286 _94151) = (term287 _94151).
Proof. exact (@lem1982792 (real_of_int _94151) term236). Qed.
Lemma lem7051091 (x : nat) : (real_of_num x) = (term288 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7051092 : term236 = term289.
Proof. exact (@lem7051091 (NUMERAL 0)). Qed.
Lemma lem7051094 (x : nat) : (term290 x) = (term291 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7051095 : term292 = term293.
Proof. exact (@lem7051094 term166). Qed.
Lemma lem7051096 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7051097 : term294 = term295.
Proof. exact (MK_COMB (@lem7051096) (@lem7051095)). Qed.
Lemma lem7051098 : term296 = term297.
Proof. exact (MK_COMB (@lem7051097) (@lem7051092)). Qed.
Lemma lem7051099 : term297 = term298.
Proof. exact (@lem1981613 term292 term236 term248 term248). Qed.
Lemma lem7051101 (m : nat) (n : nat) : (term299 m n) = (term300 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7051102 : term301 = term302.
Proof. exact (@lem7051101 term166 term166). Qed.
Lemma lem7051103 : (term303 = (BIT1 0)) = (term304 = term166).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7051104 : term304 = term166.
Proof. exact (EQ_MP (@lem7051103) (@lem940073)). Qed.
Lemma lem7051105 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7051106 : term302 = term248.
Proof. exact (MK_COMB (@lem7051105) (@lem7051104)). Qed.
Lemma lem7051107 : term301 = term248.
Proof. exact (TRANS (@lem7051102) (@lem7051106)). Qed.
Lemma lem7051109 (x : nat) : (term305 x) = term236.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7051110 : term296 = term236.
Proof. exact (@lem7051109 term166). Qed.
Lemma lem7051111 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7051112 : term306 = term307.
Proof. exact (MK_COMB (@lem7051111) (@lem7051110)). Qed.
Lemma lem7051113 : term298 = term289.
Proof. exact (MK_COMB (@lem7051112) (@lem7051107)). Qed.
Lemma lem7051114 : term297 = term289.
Proof. exact (TRANS (@lem7051099) (@lem7051113)). Qed.
Lemma lem7051115 : term296 = term289.
Proof. exact (TRANS (@lem7051098) (@lem7051114)). Qed.
Lemma lem7051117 (x : real) : (term308 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7051118 : term289 = term236.
Proof. exact (@lem7051117 term236). Qed.
Lemma lem7051119 : term296 = term236.
Proof. exact (TRANS (@lem7051115) (@lem7051118)). Qed.
Lemma lem7051120 (_94151 : int) : (term249 _94151) = (term249 _94151).
Proof. exact (eq_refl (term249 _94151)). Qed.
Lemma lem7051121 (_94151 : int) : (term287 _94151) = (term309 _94151).
Proof. exact (MK_COMB (@lem7051120 _94151) (@lem7051119)). Qed.
Lemma lem7051122 (_94151 : int) : (term309 _94151) = (real_of_int _94151).
Proof. exact (@lem1982723 (real_of_int _94151)). Qed.
Lemma lem7051123 (_94151 : int) : (term287 _94151) = (real_of_int _94151).
Proof. exact (TRANS (@lem7051121 _94151) (@lem7051122 _94151)). Qed.
Lemma lem7051125 (_94151 : int) : (term286 _94151) = (real_of_int _94151).
Proof. exact (TRANS (@lem7051089 _94151) (@lem7051123 _94151)). Qed.
Lemma lem7051126 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7051127 (_94151 : int) : (term310 _94151) = (term311 _94151).
Proof. exact (MK_COMB (@lem7051126) (@lem7051125 _94151)). Qed.
Lemma lem7051128 : term236 = term236.
Proof. exact (eq_refl term236). Qed.
Lemma lem7051129 (_94151 : int) : (term285 _94151) = (term312 _94151).
Proof. exact (MK_COMB (@lem7051127 _94151) (@lem7051128)). Qed.
Lemma lem7051130 (_94151 : int) : (term239 _94151) = (term312 _94151).
Proof. exact (TRANS (@lem7051083 _94151) (@lem7051129 _94151)). Qed.
Lemma lem7051131 (_94148 : int) : (term253 _94148) = (term313 _94148).
Proof. exact (@lem1988287 (real_of_int _94148) (term250 _94148)). Qed.
Lemma lem7051143 (_94148 : int) : (term314 _94148) = (term315 _94148).
Proof. exact (@lem1982792 (real_of_int _94148) (term250 _94148)). Qed.
Lemma lem7051144 (_94148 : int) : (term316 _94148) = (term317 _94148).
Proof. exact (@lem1982781 (real_of_int _94148) term292 term248). Qed.
Lemma lem7051146 (x : nat) : (real_of_num x) = (term288 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7051147 : term248 = term318.
Proof. exact (@lem7051146 term166). Qed.
Lemma lem7051149 (x : nat) : (term290 x) = (term291 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7051150 : term292 = term293.
Proof. exact (@lem7051149 term166). Qed.
Lemma lem7051151 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7051152 : term294 = term295.
Proof. exact (MK_COMB (@lem7051151) (@lem7051150)). Qed.
Lemma lem7051153 : term319 = term320.
Proof. exact (MK_COMB (@lem7051152) (@lem7051147)). Qed.
Lemma lem7051154 : term320 = term321.
Proof. exact (@lem1981613 term292 term248 term248 term248). Qed.
Lemma lem7051156 (m : nat) (n : nat) : (term299 m n) = (term300 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7051157 : term301 = term302.
Proof. exact (@lem7051156 term166 term166). Qed.
Lemma lem7051158 : (term303 = (BIT1 0)) = (term304 = term166).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7051159 : term304 = term166.
Proof. exact (EQ_MP (@lem7051158) (@lem940073)). Qed.
Lemma lem7051160 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7051161 : term302 = term248.
Proof. exact (MK_COMB (@lem7051160) (@lem7051159)). Qed.
Lemma lem7051162 : term301 = term248.
Proof. exact (TRANS (@lem7051157) (@lem7051161)). Qed.
Lemma lem7051164 (m : nat) (n : nat) : (term322 m n) = (term323 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7051165 : term319 = term324.
Proof. exact (@lem7051164 term166 term166). Qed.
Lemma lem7051166 : (term303 = (BIT1 0)) = (term304 = term166).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7051167 : term304 = term166.
Proof. exact (EQ_MP (@lem7051166) (@lem940073)). Qed.
Lemma lem7051168 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7051169 : term302 = term248.
Proof. exact (MK_COMB (@lem7051168) (@lem7051167)). Qed.
Lemma lem7051170 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7051171 : term324 = term292.
Proof. exact (MK_COMB (@lem7051170) (@lem7051169)). Qed.
Lemma lem7051172 : term319 = term292.
Proof. exact (TRANS (@lem7051165) (@lem7051171)). Qed.
Lemma lem7051173 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7051174 : term325 = term326.
Proof. exact (MK_COMB (@lem7051173) (@lem7051172)). Qed.
Lemma lem7051175 : term321 = term293.
Proof. exact (MK_COMB (@lem7051174) (@lem7051162)). Qed.
Lemma lem7051176 : term320 = term293.
Proof. exact (TRANS (@lem7051154) (@lem7051175)). Qed.
Lemma lem7051177 : term319 = term293.
Proof. exact (TRANS (@lem7051153) (@lem7051176)). Qed.
Lemma lem7051179 (x : real) : (term308 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7051180 : term293 = term292.
Proof. exact (@lem7051179 term292). Qed.
Lemma lem7051181 : term319 = term292.
Proof. exact (TRANS (@lem7051177) (@lem7051180)). Qed.
Lemma lem7051184 (_94148 : int) : (term327 _94148) = (term327 _94148).
Proof. exact (eq_refl (term327 _94148)). Qed.
Lemma lem7051185 (_94148 : int) : (term317 _94148) = (term328 _94148).
Proof. exact (MK_COMB (@lem7051184 _94148) (@lem7051181)). Qed.
Lemma lem7051186 (_94148 : int) : (term316 _94148) = (term328 _94148).
Proof. exact (TRANS (@lem7051144 _94148) (@lem7051185 _94148)). Qed.
Lemma lem7051187 (_94148 : int) : (term249 _94148) = (term249 _94148).
Proof. exact (eq_refl (term249 _94148)). Qed.
Lemma lem7051188 (_94148 : int) : (term315 _94148) = (term329 _94148).
Proof. exact (MK_COMB (@lem7051187 _94148) (@lem7051186 _94148)). Qed.
Lemma lem7051189 (_94148 : int) : (term329 _94148) = (term330 _94148).
Proof. exact (@lem1982763 (real_of_int _94148) (term331 _94148) term292). Qed.
Lemma lem7051190 (_94148 : int) : (term332 _94148) = (term333 _94148).
Proof. exact (@lem1982715 term292 (real_of_int _94148)). Qed.
Lemma lem7051192 (x : nat) : (real_of_num x) = (term288 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7051193 : term248 = term318.
Proof. exact (@lem7051192 term166). Qed.
Lemma lem7051195 (x : nat) : (term290 x) = (term291 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7051196 : term292 = term293.
Proof. exact (@lem7051195 term166). Qed.
Lemma lem7051197 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7051198 : term334 = term335.
Proof. exact (MK_COMB (@lem7051197) (@lem7051196)). Qed.
Lemma lem7051199 : term336 = term337.
Proof. exact (MK_COMB (@lem7051198) (@lem7051193)). Qed.
Lemma lem7051200 : term338.
Proof. exact (@lem1981473 term292 term248 term248 term248 term236 term248). Qed.
Lemma lem7051202 (m : nat) (n : nat) : (term339 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7051203 : term340 = term341.
Proof. exact (@lem7051202 (NUMERAL 0) term166). Qed.
Lemma lem7051204 : term342 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7051205 (h1 : term342 = (BIT1 0)) : term341 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7051206 : (term342 = (BIT1 0)) = (term341 = True).
Proof. exact (prop_ext (fun h1 : term342 = (BIT1 0) => @lem7051205 h1) (fun h1 : term341 = True => @lem7051204)). Qed.
Lemma lem7051207 : term341 = True.
Proof. exact (EQ_MP (@lem7051206) (@lem7051204)). Qed.
Lemma lem7051208 : term340 = True.
Proof. exact (TRANS (@lem7051203) (@lem7051207)). Qed.
Lemma lem7051209 : True = term340.
Proof. exact (SYM (@lem7051208)). Qed.
Lemma lem7051210 : term340.
Proof. exact (EQ_MP (@lem7051209) (@lem0)). Qed.
Lemma lem7051211 : term343.
Proof. exact (@lem7051200 (@lem7051210)). Qed.
Lemma lem7051213 (m : nat) (n : nat) : (term339 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7051214 : term340 = term341.
Proof. exact (@lem7051213 (NUMERAL 0) term166). Qed.
Lemma lem7051215 : term342 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7051216 (h1 : term342 = (BIT1 0)) : term341 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7051217 : (term342 = (BIT1 0)) = (term341 = True).
Proof. exact (prop_ext (fun h1 : term342 = (BIT1 0) => @lem7051216 h1) (fun h1 : term341 = True => @lem7051215)). Qed.
Lemma lem7051218 : term341 = True.
Proof. exact (EQ_MP (@lem7051217) (@lem7051215)). Qed.
Lemma lem7051219 : term340 = True.
Proof. exact (TRANS (@lem7051214) (@lem7051218)). Qed.
Lemma lem7051220 : True = term340.
Proof. exact (SYM (@lem7051219)). Qed.
Lemma lem7051221 : term340.
Proof. exact (EQ_MP (@lem7051220) (@lem0)). Qed.
Lemma lem7051222 : term344.
Proof. exact (@lem7051211 (@lem7051221)). Qed.
Lemma lem7051224 (m : nat) (n : nat) : (term339 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7051225 : term340 = term341.
Proof. exact (@lem7051224 (NUMERAL 0) term166). Qed.
Lemma lem7051226 : term342 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7051227 (h1 : term342 = (BIT1 0)) : term341 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7051228 : (term342 = (BIT1 0)) = (term341 = True).
Proof. exact (prop_ext (fun h1 : term342 = (BIT1 0) => @lem7051227 h1) (fun h1 : term341 = True => @lem7051226)). Qed.
Lemma lem7051229 : term341 = True.
Proof. exact (EQ_MP (@lem7051228) (@lem7051226)). Qed.
Lemma lem7051230 : term340 = True.
Proof. exact (TRANS (@lem7051225) (@lem7051229)). Qed.
Lemma lem7051231 : True = term340.
Proof. exact (SYM (@lem7051230)). Qed.
Lemma lem7051232 : term340.
Proof. exact (EQ_MP (@lem7051231) (@lem0)). Qed.
Lemma lem7051233 : term345.
Proof. exact (@lem7051222 (@lem7051232)). Qed.
Lemma lem7051235 (m : nat) (n : nat) : (term299 m n) = (term300 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7051236 : term301 = term302.
Proof. exact (@lem7051235 term166 term166). Qed.
Lemma lem7051237 : (term303 = (BIT1 0)) = (term304 = term166).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7051238 : term304 = term166.
Proof. exact (EQ_MP (@lem7051237) (@lem940073)). Qed.
Lemma lem7051239 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7051240 : term302 = term248.
Proof. exact (MK_COMB (@lem7051239) (@lem7051238)). Qed.
Lemma lem7051241 : term301 = term248.
Proof. exact (TRANS (@lem7051236) (@lem7051240)). Qed.
Lemma lem7051243 (m : nat) (n : nat) : (term322 m n) = (term323 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7051244 : term319 = term324.
Proof. exact (@lem7051243 term166 term166). Qed.
Lemma lem7051245 : (term303 = (BIT1 0)) = (term304 = term166).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7051246 : term304 = term166.
Proof. exact (EQ_MP (@lem7051245) (@lem940073)). Qed.
Lemma lem7051247 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7051248 : term302 = term248.
Proof. exact (MK_COMB (@lem7051247) (@lem7051246)). Qed.
Lemma lem7051249 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7051250 : term324 = term292.
Proof. exact (MK_COMB (@lem7051249) (@lem7051248)). Qed.
Lemma lem7051251 : term319 = term292.
Proof. exact (TRANS (@lem7051244) (@lem7051250)). Qed.
Lemma lem7051252 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7051253 : term346 = term334.
Proof. exact (MK_COMB (@lem7051252) (@lem7051251)). Qed.
Lemma lem7051254 : term347 = term336.
Proof. exact (MK_COMB (@lem7051253) (@lem7051241)). Qed.
Lemma lem7051256 (m : nat) : (term348 m) = term236.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7051257 : term336 = term236.
Proof. exact (@lem7051256 term166). Qed.
Lemma lem7051258 : term347 = term236.
Proof. exact (TRANS (@lem7051254) (@lem7051257)). Qed.
Lemma lem7051259 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7051260 : term349 = term350.
Proof. exact (MK_COMB (@lem7051259) (@lem7051258)). Qed.
Lemma lem7051261 : term248 = term248.
Proof. exact (eq_refl term248). Qed.
Lemma lem7051262 : term351 = term352.
Proof. exact (MK_COMB (@lem7051260) (@lem7051261)). Qed.
Lemma lem7051264 (x : nat) : (term353 x) = term236.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7051265 : term352 = term236.
Proof. exact (@lem7051264 term166). Qed.
Lemma lem7051266 : term351 = term236.
Proof. exact (TRANS (@lem7051262) (@lem7051265)). Qed.
Lemma lem7051268 (m : nat) (n : nat) : (term299 m n) = (term300 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7051269 : term301 = term302.
Proof. exact (@lem7051268 term166 term166). Qed.
Lemma lem7051270 : (term303 = (BIT1 0)) = (term304 = term166).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7051271 : term304 = term166.
Proof. exact (EQ_MP (@lem7051270) (@lem940073)). Qed.
Lemma lem7051272 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7051273 : term302 = term248.
Proof. exact (MK_COMB (@lem7051272) (@lem7051271)). Qed.
Lemma lem7051274 : term301 = term248.
Proof. exact (TRANS (@lem7051269) (@lem7051273)). Qed.
Lemma lem7051275 : term350 = term350.
Proof. exact (eq_refl term350). Qed.
Lemma lem7051276 : term354 = term352.
Proof. exact (MK_COMB (@lem7051275) (@lem7051274)). Qed.
Lemma lem7051278 (x : nat) : (term353 x) = term236.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7051279 : term352 = term236.
Proof. exact (@lem7051278 term166). Qed.
Lemma lem7051280 : term354 = term236.
Proof. exact (TRANS (@lem7051276) (@lem7051279)). Qed.
Lemma lem7051281 : term236 = term354.
Proof. exact (SYM (@lem7051280)). Qed.
Lemma lem7051282 : term351 = term354.
Proof. exact (TRANS (@lem7051266) (@lem7051281)). Qed.
Lemma lem7051283 : term337 = term289.
Proof. exact (@lem7051233 (@lem7051282)). Qed.
Lemma lem7051284 : term336 = term289.
Proof. exact (TRANS (@lem7051199) (@lem7051283)). Qed.
Lemma lem7051286 (x : real) : (term308 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7051287 : term289 = term236.
Proof. exact (@lem7051286 term236). Qed.
Lemma lem7051288 : term336 = term236.
Proof. exact (TRANS (@lem7051284) (@lem7051287)). Qed.
Lemma lem7051289 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7051290 : term355 = term350.
Proof. exact (MK_COMB (@lem7051289) (@lem7051288)). Qed.
Lemma lem7051291 (_94148 : int) : (real_of_int _94148) = (real_of_int _94148).
Proof. exact (eq_refl (real_of_int _94148)). Qed.
Lemma lem7051292 (_94148 : int) : (term333 _94148) = (term356 _94148).
Proof. exact (MK_COMB (@lem7051290) (@lem7051291 _94148)). Qed.
Lemma lem7051293 (_94148 : int) : (term332 _94148) = (term356 _94148).
Proof. exact (TRANS (@lem7051190 _94148) (@lem7051292 _94148)). Qed.
Lemma lem7051294 (_94148 : int) : (term356 _94148) = term236.
Proof. exact (@lem1982719 (real_of_int _94148)). Qed.
Lemma lem7051295 (_94148 : int) : (term332 _94148) = term236.
Proof. exact (TRANS (@lem7051293 _94148) (@lem7051294 _94148)). Qed.
Lemma lem7051296 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7051297 (_94148 : int) : (term357 _94148) = term358.
Proof. exact (MK_COMB (@lem7051296) (@lem7051295 _94148)). Qed.
Lemma lem7051298 : term292 = term292.
Proof. exact (eq_refl term292). Qed.
Lemma lem7051299 (_94148 : int) : (term330 _94148) = term359.
Proof. exact (MK_COMB (@lem7051297 _94148) (@lem7051298)). Qed.
Lemma lem7051300 (_94148 : int) : (term329 _94148) = term359.
Proof. exact (TRANS (@lem7051189 _94148) (@lem7051299 _94148)). Qed.
Lemma lem7051301 : term359 = term292.
Proof. exact (@lem1982721 term292). Qed.
Lemma lem7051302 (_94148 : int) : (term329 _94148) = term292.
Proof. exact (TRANS (@lem7051300 _94148) (@lem7051301)). Qed.
Lemma lem7051303 (_94148 : int) : (term315 _94148) = term292.
Proof. exact (TRANS (@lem7051188 _94148) (@lem7051302 _94148)). Qed.
Lemma lem7051305 (_94148 : int) : (term314 _94148) = term292.
Proof. exact (TRANS (@lem7051143 _94148) (@lem7051303 _94148)). Qed.
Lemma lem7051306 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7051307 (_94148 : int) : (term360 _94148) = term361.
Proof. exact (MK_COMB (@lem7051306) (@lem7051305 _94148)). Qed.
Lemma lem7051308 : term236 = term236.
Proof. exact (eq_refl term236). Qed.
Lemma lem7051309 (_94148 : int) : (term313 _94148) = term362.
Proof. exact (MK_COMB (@lem7051307 _94148) (@lem7051308)). Qed.
Lemma lem7051310 (_94148 : int) : (term253 _94148) = term362.
Proof. exact (TRANS (@lem7051131 _94148) (@lem7051309 _94148)). Qed.
Lemma lem7051311 (_94149 : int) (_94148 : int) : (term231 _94148 _94149) = (term363 _94149 _94148).
Proof. exact (@lem1988287 (real_of_int _94149) (real_of_int _94148)). Qed.
Lemma lem7051317 (_94149 : int) (_94148 : int) : (term364 _94149 _94148) = (term365 _94149 _94148).
Proof. exact (@lem1982792 (real_of_int _94149) (real_of_int _94148)). Qed.
Lemma lem7051322 (_94148 : int) (_94149 : int) : (term365 _94149 _94148) = (term366 _94148 _94149).
Proof. exact (@lem1982761 (term331 _94148) (real_of_int _94149)). Qed.
Lemma lem7051324 (_94148 : int) (_94149 : int) : (term364 _94149 _94148) = (term366 _94148 _94149).
Proof. exact (TRANS (@lem7051317 _94149 _94148) (@lem7051322 _94148 _94149)). Qed.
Lemma lem7051325 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7051326 (_94148 : int) (_94149 : int) : (term367 _94149 _94148) = (term368 _94148 _94149).
Proof. exact (MK_COMB (@lem7051325) (@lem7051324 _94148 _94149)). Qed.
Lemma lem7051327 : term236 = term236.
Proof. exact (eq_refl term236). Qed.
Lemma lem7051328 (_94148 : int) (_94149 : int) : (term363 _94149 _94148) = (term369 _94148 _94149).
Proof. exact (MK_COMB (@lem7051326 _94148 _94149) (@lem7051327)). Qed.
Lemma lem7051329 (_94148 : int) (_94149 : int) : (term231 _94148 _94149) = (term369 _94148 _94149).
Proof. exact (TRANS (@lem7051311 _94149 _94148) (@lem7051328 _94148 _94149)). Qed.
Lemma lem7051330 (_94150 : int) (_94151 : int) : (term259 _94150 _94151) = (term370 _94150 _94151).
Proof. exact (@lem1988287 (term243 _94150 _94151) (term250 _94151)). Qed.
Lemma lem7051348 (_94150 : int) (_94151 : int) : (term371 _94150 _94151) = (term372 _94150 _94151).
Proof. exact (@lem1982792 (term243 _94150 _94151) (term250 _94151)). Qed.
Lemma lem7051349 (_94151 : int) : (term316 _94151) = (term317 _94151).
Proof. exact (@lem1982781 (real_of_int _94151) term292 term248). Qed.
Lemma lem7051351 (x : nat) : (real_of_num x) = (term288 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7051352 : term248 = term318.
Proof. exact (@lem7051351 term166). Qed.
Lemma lem7051354 (x : nat) : (term290 x) = (term291 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7051355 : term292 = term293.
Proof. exact (@lem7051354 term166). Qed.
Lemma lem7051356 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7051357 : term294 = term295.
Proof. exact (MK_COMB (@lem7051356) (@lem7051355)). Qed.
Lemma lem7051358 : term319 = term320.
Proof. exact (MK_COMB (@lem7051357) (@lem7051352)). Qed.
Lemma lem7051359 : term320 = term321.
Proof. exact (@lem1981613 term292 term248 term248 term248). Qed.
Lemma lem7051361 (m : nat) (n : nat) : (term299 m n) = (term300 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7051362 : term301 = term302.
Proof. exact (@lem7051361 term166 term166). Qed.
Lemma lem7051363 : (term303 = (BIT1 0)) = (term304 = term166).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7051364 : term304 = term166.
Proof. exact (EQ_MP (@lem7051363) (@lem940073)). Qed.
Lemma lem7051365 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7051366 : term302 = term248.
Proof. exact (MK_COMB (@lem7051365) (@lem7051364)). Qed.
Lemma lem7051367 : term301 = term248.
Proof. exact (TRANS (@lem7051362) (@lem7051366)). Qed.
Lemma lem7051369 (m : nat) (n : nat) : (term322 m n) = (term323 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7051370 : term319 = term324.
Proof. exact (@lem7051369 term166 term166). Qed.
Lemma lem7051371 : (term303 = (BIT1 0)) = (term304 = term166).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7051372 : term304 = term166.
Proof. exact (EQ_MP (@lem7051371) (@lem940073)). Qed.
Lemma lem7051373 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7051374 : term302 = term248.
Proof. exact (MK_COMB (@lem7051373) (@lem7051372)). Qed.
Lemma lem7051375 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7051376 : term324 = term292.
Proof. exact (MK_COMB (@lem7051375) (@lem7051374)). Qed.
Lemma lem7051377 : term319 = term292.
Proof. exact (TRANS (@lem7051370) (@lem7051376)). Qed.
Lemma lem7051378 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7051379 : term325 = term326.
Proof. exact (MK_COMB (@lem7051378) (@lem7051377)). Qed.
Lemma lem7051380 : term321 = term293.
Proof. exact (MK_COMB (@lem7051379) (@lem7051367)). Qed.
Lemma lem7051381 : term320 = term293.
Proof. exact (TRANS (@lem7051359) (@lem7051380)). Qed.
Lemma lem7051382 : term319 = term293.
Proof. exact (TRANS (@lem7051358) (@lem7051381)). Qed.
Lemma lem7051384 (x : real) : (term308 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7051385 : term293 = term292.
Proof. exact (@lem7051384 term292). Qed.
Lemma lem7051386 : term319 = term292.
Proof. exact (TRANS (@lem7051382) (@lem7051385)). Qed.
Lemma lem7051389 (_94151 : int) : (term327 _94151) = (term327 _94151).
Proof. exact (eq_refl (term327 _94151)). Qed.
Lemma lem7051390 (_94151 : int) : (term317 _94151) = (term328 _94151).
Proof. exact (MK_COMB (@lem7051389 _94151) (@lem7051386)). Qed.
Lemma lem7051391 (_94151 : int) : (term316 _94151) = (term328 _94151).
Proof. exact (TRANS (@lem7051349 _94151) (@lem7051390 _94151)). Qed.
Lemma lem7051392 (_94150 : int) (_94151 : int) : (term268 _94150 _94151) = (term268 _94150 _94151).
Proof. exact (eq_refl (term268 _94150 _94151)). Qed.
Lemma lem7051393 (_94150 : int) (_94151 : int) : (term372 _94150 _94151) = (term373 _94150 _94151).
Proof. exact (MK_COMB (@lem7051392 _94150 _94151) (@lem7051391 _94151)). Qed.
Lemma lem7051394 (_94150 : int) (_94151 : int) : (term373 _94150 _94151) = (term374 _94150 _94151).
Proof. exact (@lem1982755 (real_of_int _94150) (real_of_int _94151) (term328 _94151)). Qed.
Lemma lem7051395 (_94151 : int) : (term329 _94151) = (term330 _94151).
Proof. exact (@lem1982763 (real_of_int _94151) (term331 _94151) term292). Qed.
Lemma lem7051396 (_94151 : int) : (term332 _94151) = (term333 _94151).
Proof. exact (@lem1982715 term292 (real_of_int _94151)). Qed.
Lemma lem7051398 (x : nat) : (real_of_num x) = (term288 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7051399 : term248 = term318.
Proof. exact (@lem7051398 term166). Qed.
Lemma lem7051401 (x : nat) : (term290 x) = (term291 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7051402 : term292 = term293.
Proof. exact (@lem7051401 term166). Qed.
Lemma lem7051403 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7051404 : term334 = term335.
Proof. exact (MK_COMB (@lem7051403) (@lem7051402)). Qed.
Lemma lem7051405 : term336 = term337.
Proof. exact (MK_COMB (@lem7051404) (@lem7051399)). Qed.
Lemma lem7051406 : term338.
Proof. exact (@lem1981473 term292 term248 term248 term248 term236 term248). Qed.
Lemma lem7051408 (m : nat) (n : nat) : (term339 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7051409 : term340 = term341.
Proof. exact (@lem7051408 (NUMERAL 0) term166). Qed.
Lemma lem7051410 : term342 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7051411 (h1 : term342 = (BIT1 0)) : term341 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7051412 : (term342 = (BIT1 0)) = (term341 = True).
Proof. exact (prop_ext (fun h1 : term342 = (BIT1 0) => @lem7051411 h1) (fun h1 : term341 = True => @lem7051410)). Qed.
Lemma lem7051413 : term341 = True.
Proof. exact (EQ_MP (@lem7051412) (@lem7051410)). Qed.
Lemma lem7051414 : term340 = True.
Proof. exact (TRANS (@lem7051409) (@lem7051413)). Qed.
Lemma lem7051415 : True = term340.
Proof. exact (SYM (@lem7051414)). Qed.
Lemma lem7051416 : term340.
Proof. exact (EQ_MP (@lem7051415) (@lem0)). Qed.
Lemma lem7051417 : term343.
Proof. exact (@lem7051406 (@lem7051416)). Qed.
Lemma lem7051419 (m : nat) (n : nat) : (term339 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7051420 : term340 = term341.
Proof. exact (@lem7051419 (NUMERAL 0) term166). Qed.
Lemma lem7051421 : term342 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7051422 (h1 : term342 = (BIT1 0)) : term341 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7051423 : (term342 = (BIT1 0)) = (term341 = True).
Proof. exact (prop_ext (fun h1 : term342 = (BIT1 0) => @lem7051422 h1) (fun h1 : term341 = True => @lem7051421)). Qed.
Lemma lem7051424 : term341 = True.
Proof. exact (EQ_MP (@lem7051423) (@lem7051421)). Qed.
Lemma lem7051425 : term340 = True.
Proof. exact (TRANS (@lem7051420) (@lem7051424)). Qed.
Lemma lem7051426 : True = term340.
Proof. exact (SYM (@lem7051425)). Qed.
Lemma lem7051427 : term340.
Proof. exact (EQ_MP (@lem7051426) (@lem0)). Qed.
Lemma lem7051428 : term344.
Proof. exact (@lem7051417 (@lem7051427)). Qed.
Lemma lem7051430 (m : nat) (n : nat) : (term339 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7051431 : term340 = term341.
Proof. exact (@lem7051430 (NUMERAL 0) term166). Qed.
Lemma lem7051432 : term342 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7051433 (h1 : term342 = (BIT1 0)) : term341 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7051434 : (term342 = (BIT1 0)) = (term341 = True).
Proof. exact (prop_ext (fun h1 : term342 = (BIT1 0) => @lem7051433 h1) (fun h1 : term341 = True => @lem7051432)). Qed.
Lemma lem7051435 : term341 = True.
Proof. exact (EQ_MP (@lem7051434) (@lem7051432)). Qed.
Lemma lem7051436 : term340 = True.
Proof. exact (TRANS (@lem7051431) (@lem7051435)). Qed.
Lemma lem7051437 : True = term340.
Proof. exact (SYM (@lem7051436)). Qed.
Lemma lem7051438 : term340.
Proof. exact (EQ_MP (@lem7051437) (@lem0)). Qed.
Lemma lem7051439 : term345.
Proof. exact (@lem7051428 (@lem7051438)). Qed.
Lemma lem7051441 (m : nat) (n : nat) : (term299 m n) = (term300 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7051442 : term301 = term302.
Proof. exact (@lem7051441 term166 term166). Qed.
Lemma lem7051443 : (term303 = (BIT1 0)) = (term304 = term166).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7051444 : term304 = term166.
Proof. exact (EQ_MP (@lem7051443) (@lem940073)). Qed.
Lemma lem7051445 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7051446 : term302 = term248.
Proof. exact (MK_COMB (@lem7051445) (@lem7051444)). Qed.
Lemma lem7051447 : term301 = term248.
Proof. exact (TRANS (@lem7051442) (@lem7051446)). Qed.
Lemma lem7051449 (m : nat) (n : nat) : (term322 m n) = (term323 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7051450 : term319 = term324.
Proof. exact (@lem7051449 term166 term166). Qed.
Lemma lem7051451 : (term303 = (BIT1 0)) = (term304 = term166).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7051452 : term304 = term166.
Proof. exact (EQ_MP (@lem7051451) (@lem940073)). Qed.
Lemma lem7051453 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7051454 : term302 = term248.
Proof. exact (MK_COMB (@lem7051453) (@lem7051452)). Qed.
Lemma lem7051455 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7051456 : term324 = term292.
Proof. exact (MK_COMB (@lem7051455) (@lem7051454)). Qed.
Lemma lem7051457 : term319 = term292.
Proof. exact (TRANS (@lem7051450) (@lem7051456)). Qed.
Lemma lem7051458 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7051459 : term346 = term334.
Proof. exact (MK_COMB (@lem7051458) (@lem7051457)). Qed.
Lemma lem7051460 : term347 = term336.
Proof. exact (MK_COMB (@lem7051459) (@lem7051447)). Qed.
Lemma lem7051462 (m : nat) : (term348 m) = term236.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7051463 : term336 = term236.
Proof. exact (@lem7051462 term166). Qed.
Lemma lem7051464 : term347 = term236.
Proof. exact (TRANS (@lem7051460) (@lem7051463)). Qed.
Lemma lem7051465 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7051466 : term349 = term350.
Proof. exact (MK_COMB (@lem7051465) (@lem7051464)). Qed.
Lemma lem7051467 : term248 = term248.
Proof. exact (eq_refl term248). Qed.
Lemma lem7051468 : term351 = term352.
Proof. exact (MK_COMB (@lem7051466) (@lem7051467)). Qed.
Lemma lem7051470 (x : nat) : (term353 x) = term236.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7051471 : term352 = term236.
Proof. exact (@lem7051470 term166). Qed.
Lemma lem7051472 : term351 = term236.
Proof. exact (TRANS (@lem7051468) (@lem7051471)). Qed.
Lemma lem7051474 (m : nat) (n : nat) : (term299 m n) = (term300 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7051475 : term301 = term302.
Proof. exact (@lem7051474 term166 term166). Qed.
Lemma lem7051476 : (term303 = (BIT1 0)) = (term304 = term166).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7051477 : term304 = term166.
Proof. exact (EQ_MP (@lem7051476) (@lem940073)). Qed.
Lemma lem7051478 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7051479 : term302 = term248.
Proof. exact (MK_COMB (@lem7051478) (@lem7051477)). Qed.
Lemma lem7051480 : term301 = term248.
Proof. exact (TRANS (@lem7051475) (@lem7051479)). Qed.
Lemma lem7051481 : term350 = term350.
Proof. exact (eq_refl term350). Qed.
Lemma lem7051482 : term354 = term352.
Proof. exact (MK_COMB (@lem7051481) (@lem7051480)). Qed.
Lemma lem7051484 (x : nat) : (term353 x) = term236.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7051485 : term352 = term236.
Proof. exact (@lem7051484 term166). Qed.
Lemma lem7051486 : term354 = term236.
Proof. exact (TRANS (@lem7051482) (@lem7051485)). Qed.
Lemma lem7051487 : term236 = term354.
Proof. exact (SYM (@lem7051486)). Qed.
Lemma lem7051488 : term351 = term354.
Proof. exact (TRANS (@lem7051472) (@lem7051487)). Qed.
Lemma lem7051489 : term337 = term289.
Proof. exact (@lem7051439 (@lem7051488)). Qed.
Lemma lem7051490 : term336 = term289.
Proof. exact (TRANS (@lem7051405) (@lem7051489)). Qed.
Lemma lem7051492 (x : real) : (term308 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7051493 : term289 = term236.
Proof. exact (@lem7051492 term236). Qed.
Lemma lem7051494 : term336 = term236.
Proof. exact (TRANS (@lem7051490) (@lem7051493)). Qed.
Lemma lem7051495 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7051496 : term355 = term350.
Proof. exact (MK_COMB (@lem7051495) (@lem7051494)). Qed.
Lemma lem7051497 (_94151 : int) : (real_of_int _94151) = (real_of_int _94151).
Proof. exact (eq_refl (real_of_int _94151)). Qed.
Lemma lem7051498 (_94151 : int) : (term333 _94151) = (term356 _94151).
Proof. exact (MK_COMB (@lem7051496) (@lem7051497 _94151)). Qed.
Lemma lem7051499 (_94151 : int) : (term332 _94151) = (term356 _94151).
Proof. exact (TRANS (@lem7051396 _94151) (@lem7051498 _94151)). Qed.
Lemma lem7051500 (_94151 : int) : (term356 _94151) = term236.
Proof. exact (@lem1982719 (real_of_int _94151)). Qed.
Lemma lem7051501 (_94151 : int) : (term332 _94151) = term236.
Proof. exact (TRANS (@lem7051499 _94151) (@lem7051500 _94151)). Qed.
Lemma lem7051502 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7051503 (_94151 : int) : (term357 _94151) = term358.
Proof. exact (MK_COMB (@lem7051502) (@lem7051501 _94151)). Qed.
Lemma lem7051504 : term292 = term292.
Proof. exact (eq_refl term292). Qed.
Lemma lem7051505 (_94151 : int) : (term330 _94151) = term359.
Proof. exact (MK_COMB (@lem7051503 _94151) (@lem7051504)). Qed.
Lemma lem7051506 (_94151 : int) : (term329 _94151) = term359.
Proof. exact (TRANS (@lem7051395 _94151) (@lem7051505 _94151)). Qed.
Lemma lem7051507 : term359 = term292.
Proof. exact (@lem1982721 term292). Qed.
Lemma lem7051508 (_94151 : int) : (term329 _94151) = term292.
Proof. exact (TRANS (@lem7051506 _94151) (@lem7051507)). Qed.
Lemma lem7051509 (_94150 : int) : (term249 _94150) = (term249 _94150).
Proof. exact (eq_refl (term249 _94150)). Qed.
Lemma lem7051510 (_94151 : int) (_94150 : int) : (term374 _94150 _94151) = (term375 _94150).
Proof. exact (MK_COMB (@lem7051509 _94150) (@lem7051508 _94151)). Qed.
Lemma lem7051511 (_94151 : int) (_94150 : int) : (term373 _94150 _94151) = (term375 _94150).
Proof. exact (TRANS (@lem7051394 _94150 _94151) (@lem7051510 _94151 _94150)). Qed.
Lemma lem7051512 (_94151 : int) (_94150 : int) : (term372 _94150 _94151) = (term375 _94150).
Proof. exact (TRANS (@lem7051393 _94150 _94151) (@lem7051511 _94151 _94150)). Qed.
Lemma lem7051514 (_94151 : int) (_94150 : int) : (term371 _94150 _94151) = (term375 _94150).
Proof. exact (TRANS (@lem7051348 _94150 _94151) (@lem7051512 _94151 _94150)). Qed.
Lemma lem7051515 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7051516 (_94151 : int) (_94150 : int) : (term376 _94150 _94151) = (term377 _94150).
Proof. exact (MK_COMB (@lem7051515) (@lem7051514 _94151 _94150)). Qed.
Lemma lem7051517 : term236 = term236.
Proof. exact (eq_refl term236). Qed.
Lemma lem7051518 (_94151 : int) (_94150 : int) : (term370 _94150 _94151) = (term378 _94150).
Proof. exact (MK_COMB (@lem7051516 _94151 _94150) (@lem7051517)). Qed.
Lemma lem7051519 (_94151 : int) (_94150 : int) : (term259 _94150 _94151) = (term378 _94150).
Proof. exact (TRANS (@lem7051330 _94150 _94151) (@lem7051518 _94151 _94150)). Qed.
Lemma lem7051520 (_94150 : int) (_94151 : int) : (term272 _94150 _94151) = (term379 _94150 _94151).
Proof. exact (@lem1988287 (real_of_int _94151) (term269 _94150 _94151)). Qed.
Lemma lem7051537 (_94150 : int) (_94151 : int) : (term269 _94150 _94151) = (term380 _94150 _94151).
Proof. exact (@lem1982755 (real_of_int _94150) (real_of_int _94151) term248). Qed.
Lemma lem7051540 (_94151 : int) : (term381 _94151) = (term381 _94151).
Proof. exact (eq_refl (term381 _94151)). Qed.
Lemma lem7051541 (_94150 : int) (_94151 : int) : (term382 _94150 _94151) = (term383 _94150 _94151).
Proof. exact (MK_COMB (@lem7051540 _94151) (@lem7051537 _94150 _94151)). Qed.
Lemma lem7051542 (_94150 : int) (_94151 : int) : (term383 _94150 _94151) = (term384 _94150 _94151).
Proof. exact (@lem1982792 (real_of_int _94151) (term380 _94150 _94151)). Qed.
Lemma lem7051543 (_94150 : int) (_94151 : int) : (term385 _94150 _94151) = (term386 _94150 _94151).
Proof. exact (@lem1982781 (real_of_int _94150) term292 (term250 _94151)). Qed.
Lemma lem7051544 (_94151 : int) : (term316 _94151) = (term317 _94151).
Proof. exact (@lem1982781 (real_of_int _94151) term292 term248). Qed.
Lemma lem7051546 (x : nat) : (real_of_num x) = (term288 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7051547 : term248 = term318.
Proof. exact (@lem7051546 term166). Qed.
Lemma lem7051549 (x : nat) : (term290 x) = (term291 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7051550 : term292 = term293.
Proof. exact (@lem7051549 term166). Qed.
Lemma lem7051551 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7051552 : term294 = term295.
Proof. exact (MK_COMB (@lem7051551) (@lem7051550)). Qed.
Lemma lem7051553 : term319 = term320.
Proof. exact (MK_COMB (@lem7051552) (@lem7051547)). Qed.
Lemma lem7051554 : term320 = term321.
Proof. exact (@lem1981613 term292 term248 term248 term248). Qed.
Lemma lem7051556 (m : nat) (n : nat) : (term299 m n) = (term300 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7051557 : term301 = term302.
Proof. exact (@lem7051556 term166 term166). Qed.
Lemma lem7051558 : (term303 = (BIT1 0)) = (term304 = term166).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7051559 : term304 = term166.
Proof. exact (EQ_MP (@lem7051558) (@lem940073)). Qed.
Lemma lem7051560 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7051561 : term302 = term248.
Proof. exact (MK_COMB (@lem7051560) (@lem7051559)). Qed.
Lemma lem7051562 : term301 = term248.
Proof. exact (TRANS (@lem7051557) (@lem7051561)). Qed.
Lemma lem7051564 (m : nat) (n : nat) : (term322 m n) = (term323 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7051565 : term319 = term324.
Proof. exact (@lem7051564 term166 term166). Qed.
Lemma lem7051566 : (term303 = (BIT1 0)) = (term304 = term166).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7051567 : term304 = term166.
Proof. exact (EQ_MP (@lem7051566) (@lem940073)). Qed.
Lemma lem7051568 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7051569 : term302 = term248.
Proof. exact (MK_COMB (@lem7051568) (@lem7051567)). Qed.
Lemma lem7051570 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7051571 : term324 = term292.
Proof. exact (MK_COMB (@lem7051570) (@lem7051569)). Qed.
Lemma lem7051572 : term319 = term292.
Proof. exact (TRANS (@lem7051565) (@lem7051571)). Qed.
Lemma lem7051573 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7051574 : term325 = term326.
Proof. exact (MK_COMB (@lem7051573) (@lem7051572)). Qed.
Lemma lem7051575 : term321 = term293.
Proof. exact (MK_COMB (@lem7051574) (@lem7051562)). Qed.
Lemma lem7051576 : term320 = term293.
Proof. exact (TRANS (@lem7051554) (@lem7051575)). Qed.
Lemma lem7051577 : term319 = term293.
Proof. exact (TRANS (@lem7051553) (@lem7051576)). Qed.
Lemma lem7051579 (x : real) : (term308 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7051580 : term293 = term292.
Proof. exact (@lem7051579 term292). Qed.
Lemma lem7051581 : term319 = term292.
Proof. exact (TRANS (@lem7051577) (@lem7051580)). Qed.
Lemma lem7051584 (_94151 : int) : (term327 _94151) = (term327 _94151).
Proof. exact (eq_refl (term327 _94151)). Qed.
Lemma lem7051585 (_94151 : int) : (term317 _94151) = (term328 _94151).
Proof. exact (MK_COMB (@lem7051584 _94151) (@lem7051581)). Qed.
Lemma lem7051586 (_94151 : int) : (term316 _94151) = (term328 _94151).
Proof. exact (TRANS (@lem7051544 _94151) (@lem7051585 _94151)). Qed.
Lemma lem7051589 (_94150 : int) : (term327 _94150) = (term327 _94150).
Proof. exact (eq_refl (term327 _94150)). Qed.
Lemma lem7051590 (_94150 : int) (_94151 : int) : (term386 _94150 _94151) = (term387 _94150 _94151).
Proof. exact (MK_COMB (@lem7051589 _94150) (@lem7051586 _94151)). Qed.
Lemma lem7051591 (_94150 : int) (_94151 : int) : (term385 _94150 _94151) = (term387 _94150 _94151).
Proof. exact (TRANS (@lem7051543 _94150 _94151) (@lem7051590 _94150 _94151)). Qed.
Lemma lem7051592 (_94151 : int) : (term249 _94151) = (term249 _94151).
Proof. exact (eq_refl (term249 _94151)). Qed.
Lemma lem7051593 (_94150 : int) (_94151 : int) : (term384 _94150 _94151) = (term388 _94150 _94151).
Proof. exact (MK_COMB (@lem7051592 _94151) (@lem7051591 _94150 _94151)). Qed.
Lemma lem7051594 (_94150 : int) (_94151 : int) : (term388 _94150 _94151) = (term389 _94150 _94151).
Proof. exact (@lem1982757 (term331 _94150) (real_of_int _94151) (term328 _94151)). Qed.
Lemma lem7051595 (_94151 : int) : (term329 _94151) = (term330 _94151).
Proof. exact (@lem1982763 (real_of_int _94151) (term331 _94151) term292). Qed.
Lemma lem7051596 (_94151 : int) : (term332 _94151) = (term333 _94151).
Proof. exact (@lem1982715 term292 (real_of_int _94151)). Qed.
Lemma lem7051598 (x : nat) : (real_of_num x) = (term288 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7051599 : term248 = term318.
Proof. exact (@lem7051598 term166). Qed.
Lemma lem7051601 (x : nat) : (term290 x) = (term291 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7051602 : term292 = term293.
Proof. exact (@lem7051601 term166). Qed.
Lemma lem7051603 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7051604 : term334 = term335.
Proof. exact (MK_COMB (@lem7051603) (@lem7051602)). Qed.
Lemma lem7051605 : term336 = term337.
Proof. exact (MK_COMB (@lem7051604) (@lem7051599)). Qed.
Lemma lem7051606 : term338.
Proof. exact (@lem1981473 term292 term248 term248 term248 term236 term248). Qed.
Lemma lem7051608 (m : nat) (n : nat) : (term339 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7051609 : term340 = term341.
Proof. exact (@lem7051608 (NUMERAL 0) term166). Qed.
Lemma lem7051610 : term342 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7051611 (h1 : term342 = (BIT1 0)) : term341 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7051612 : (term342 = (BIT1 0)) = (term341 = True).
Proof. exact (prop_ext (fun h1 : term342 = (BIT1 0) => @lem7051611 h1) (fun h1 : term341 = True => @lem7051610)). Qed.
Lemma lem7051613 : term341 = True.
Proof. exact (EQ_MP (@lem7051612) (@lem7051610)). Qed.
Lemma lem7051614 : term340 = True.
Proof. exact (TRANS (@lem7051609) (@lem7051613)). Qed.
Lemma lem7051615 : True = term340.
Proof. exact (SYM (@lem7051614)). Qed.
Lemma lem7051616 : term340.
Proof. exact (EQ_MP (@lem7051615) (@lem0)). Qed.
Lemma lem7051617 : term343.
Proof. exact (@lem7051606 (@lem7051616)). Qed.
Lemma lem7051619 (m : nat) (n : nat) : (term339 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7051620 : term340 = term341.
Proof. exact (@lem7051619 (NUMERAL 0) term166). Qed.
Lemma lem7051621 : term342 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7051622 (h1 : term342 = (BIT1 0)) : term341 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7051623 : (term342 = (BIT1 0)) = (term341 = True).
Proof. exact (prop_ext (fun h1 : term342 = (BIT1 0) => @lem7051622 h1) (fun h1 : term341 = True => @lem7051621)). Qed.
Lemma lem7051624 : term341 = True.
Proof. exact (EQ_MP (@lem7051623) (@lem7051621)). Qed.
Lemma lem7051625 : term340 = True.
Proof. exact (TRANS (@lem7051620) (@lem7051624)). Qed.
Lemma lem7051626 : True = term340.
Proof. exact (SYM (@lem7051625)). Qed.
Lemma lem7051627 : term340.
Proof. exact (EQ_MP (@lem7051626) (@lem0)). Qed.
Lemma lem7051628 : term344.
Proof. exact (@lem7051617 (@lem7051627)). Qed.
Lemma lem7051630 (m : nat) (n : nat) : (term339 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7051631 : term340 = term341.
Proof. exact (@lem7051630 (NUMERAL 0) term166). Qed.
Lemma lem7051632 : term342 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7051633 (h1 : term342 = (BIT1 0)) : term341 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7051634 : (term342 = (BIT1 0)) = (term341 = True).
Proof. exact (prop_ext (fun h1 : term342 = (BIT1 0) => @lem7051633 h1) (fun h1 : term341 = True => @lem7051632)). Qed.
Lemma lem7051635 : term341 = True.
Proof. exact (EQ_MP (@lem7051634) (@lem7051632)). Qed.
Lemma lem7051636 : term340 = True.
Proof. exact (TRANS (@lem7051631) (@lem7051635)). Qed.
Lemma lem7051637 : True = term340.
Proof. exact (SYM (@lem7051636)). Qed.
Lemma lem7051638 : term340.
Proof. exact (EQ_MP (@lem7051637) (@lem0)). Qed.
Lemma lem7051639 : term345.
Proof. exact (@lem7051628 (@lem7051638)). Qed.
Lemma lem7051641 (m : nat) (n : nat) : (term299 m n) = (term300 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7051642 : term301 = term302.
Proof. exact (@lem7051641 term166 term166). Qed.
Lemma lem7051643 : (term303 = (BIT1 0)) = (term304 = term166).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7051644 : term304 = term166.
Proof. exact (EQ_MP (@lem7051643) (@lem940073)). Qed.
Lemma lem7051645 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7051646 : term302 = term248.
Proof. exact (MK_COMB (@lem7051645) (@lem7051644)). Qed.
Lemma lem7051647 : term301 = term248.
Proof. exact (TRANS (@lem7051642) (@lem7051646)). Qed.
Lemma lem7051649 (m : nat) (n : nat) : (term322 m n) = (term323 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7051650 : term319 = term324.
Proof. exact (@lem7051649 term166 term166). Qed.
Lemma lem7051651 : (term303 = (BIT1 0)) = (term304 = term166).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7051652 : term304 = term166.
Proof. exact (EQ_MP (@lem7051651) (@lem940073)). Qed.
Lemma lem7051653 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7051654 : term302 = term248.
Proof. exact (MK_COMB (@lem7051653) (@lem7051652)). Qed.
Lemma lem7051655 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7051656 : term324 = term292.
Proof. exact (MK_COMB (@lem7051655) (@lem7051654)). Qed.
Lemma lem7051657 : term319 = term292.
Proof. exact (TRANS (@lem7051650) (@lem7051656)). Qed.
Lemma lem7051658 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7051659 : term346 = term334.
Proof. exact (MK_COMB (@lem7051658) (@lem7051657)). Qed.
Lemma lem7051660 : term347 = term336.
Proof. exact (MK_COMB (@lem7051659) (@lem7051647)). Qed.
Lemma lem7051662 (m : nat) : (term348 m) = term236.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7051663 : term336 = term236.
Proof. exact (@lem7051662 term166). Qed.
Lemma lem7051664 : term347 = term236.
Proof. exact (TRANS (@lem7051660) (@lem7051663)). Qed.
Lemma lem7051665 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7051666 : term349 = term350.
Proof. exact (MK_COMB (@lem7051665) (@lem7051664)). Qed.
Lemma lem7051667 : term248 = term248.
Proof. exact (eq_refl term248). Qed.
Lemma lem7051668 : term351 = term352.
Proof. exact (MK_COMB (@lem7051666) (@lem7051667)). Qed.
Lemma lem7051670 (x : nat) : (term353 x) = term236.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7051671 : term352 = term236.
Proof. exact (@lem7051670 term166). Qed.
Lemma lem7051672 : term351 = term236.
Proof. exact (TRANS (@lem7051668) (@lem7051671)). Qed.
Lemma lem7051674 (m : nat) (n : nat) : (term299 m n) = (term300 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7051675 : term301 = term302.
Proof. exact (@lem7051674 term166 term166). Qed.
Lemma lem7051676 : (term303 = (BIT1 0)) = (term304 = term166).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7051677 : term304 = term166.
Proof. exact (EQ_MP (@lem7051676) (@lem940073)). Qed.
Lemma lem7051678 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7051679 : term302 = term248.
Proof. exact (MK_COMB (@lem7051678) (@lem7051677)). Qed.
Lemma lem7051680 : term301 = term248.
Proof. exact (TRANS (@lem7051675) (@lem7051679)). Qed.
Lemma lem7051681 : term350 = term350.
Proof. exact (eq_refl term350). Qed.
Lemma lem7051682 : term354 = term352.
Proof. exact (MK_COMB (@lem7051681) (@lem7051680)). Qed.
Lemma lem7051684 (x : nat) : (term353 x) = term236.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7051685 : term352 = term236.
Proof. exact (@lem7051684 term166). Qed.
Lemma lem7051686 : term354 = term236.
Proof. exact (TRANS (@lem7051682) (@lem7051685)). Qed.
Lemma lem7051687 : term236 = term354.
Proof. exact (SYM (@lem7051686)). Qed.
Lemma lem7051688 : term351 = term354.
Proof. exact (TRANS (@lem7051672) (@lem7051687)). Qed.
Lemma lem7051689 : term337 = term289.
Proof. exact (@lem7051639 (@lem7051688)). Qed.
Lemma lem7051690 : term336 = term289.
Proof. exact (TRANS (@lem7051605) (@lem7051689)). Qed.
Lemma lem7051692 (x : real) : (term308 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7051693 : term289 = term236.
Proof. exact (@lem7051692 term236). Qed.
Lemma lem7051694 : term336 = term236.
Proof. exact (TRANS (@lem7051690) (@lem7051693)). Qed.
Lemma lem7051695 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7051696 : term355 = term350.
Proof. exact (MK_COMB (@lem7051695) (@lem7051694)). Qed.
Lemma lem7051697 (_94151 : int) : (real_of_int _94151) = (real_of_int _94151).
Proof. exact (eq_refl (real_of_int _94151)). Qed.
Lemma lem7051698 (_94151 : int) : (term333 _94151) = (term356 _94151).
Proof. exact (MK_COMB (@lem7051696) (@lem7051697 _94151)). Qed.
Lemma lem7051699 (_94151 : int) : (term332 _94151) = (term356 _94151).
Proof. exact (TRANS (@lem7051596 _94151) (@lem7051698 _94151)). Qed.
Lemma lem7051700 (_94151 : int) : (term356 _94151) = term236.
Proof. exact (@lem1982719 (real_of_int _94151)). Qed.
Lemma lem7051701 (_94151 : int) : (term332 _94151) = term236.
Proof. exact (TRANS (@lem7051699 _94151) (@lem7051700 _94151)). Qed.
Lemma lem7051702 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7051703 (_94151 : int) : (term357 _94151) = term358.
Proof. exact (MK_COMB (@lem7051702) (@lem7051701 _94151)). Qed.
Lemma lem7051704 : term292 = term292.
Proof. exact (eq_refl term292). Qed.
Lemma lem7051705 (_94151 : int) : (term330 _94151) = term359.
Proof. exact (MK_COMB (@lem7051703 _94151) (@lem7051704)). Qed.
Lemma lem7051706 (_94151 : int) : (term329 _94151) = term359.
Proof. exact (TRANS (@lem7051595 _94151) (@lem7051705 _94151)). Qed.
Lemma lem7051707 : term359 = term292.
Proof. exact (@lem1982721 term292). Qed.
Lemma lem7051708 (_94151 : int) : (term329 _94151) = term292.
Proof. exact (TRANS (@lem7051706 _94151) (@lem7051707)). Qed.
Lemma lem7051709 (_94150 : int) : (term327 _94150) = (term327 _94150).
Proof. exact (eq_refl (term327 _94150)). Qed.
Lemma lem7051710 (_94151 : int) (_94150 : int) : (term389 _94150 _94151) = (term328 _94150).
Proof. exact (MK_COMB (@lem7051709 _94150) (@lem7051708 _94151)). Qed.
Lemma lem7051711 (_94151 : int) (_94150 : int) : (term388 _94150 _94151) = (term328 _94150).
Proof. exact (TRANS (@lem7051594 _94150 _94151) (@lem7051710 _94151 _94150)). Qed.
Lemma lem7051712 (_94151 : int) (_94150 : int) : (term384 _94150 _94151) = (term328 _94150).
Proof. exact (TRANS (@lem7051593 _94150 _94151) (@lem7051711 _94151 _94150)). Qed.
Lemma lem7051713 (_94151 : int) (_94150 : int) : (term383 _94150 _94151) = (term328 _94150).
Proof. exact (TRANS (@lem7051542 _94150 _94151) (@lem7051712 _94151 _94150)). Qed.
Lemma lem7051714 (_94151 : int) (_94150 : int) : (term382 _94150 _94151) = (term328 _94150).
Proof. exact (TRANS (@lem7051541 _94150 _94151) (@lem7051713 _94151 _94150)). Qed.
Lemma lem7051715 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7051716 (_94151 : int) (_94150 : int) : (term390 _94150 _94151) = (term391 _94150).
Proof. exact (MK_COMB (@lem7051715) (@lem7051714 _94151 _94150)). Qed.
Lemma lem7051717 : term236 = term236.
Proof. exact (eq_refl term236). Qed.
Lemma lem7051718 (_94151 : int) (_94150 : int) : (term379 _94150 _94151) = (term392 _94150).
Proof. exact (MK_COMB (@lem7051716 _94151 _94150) (@lem7051717)). Qed.
Lemma lem7051719 (_94151 : int) (_94150 : int) : (term272 _94150 _94151) = (term392 _94150).
Proof. exact (TRANS (@lem7051520 _94150 _94151) (@lem7051718 _94151 _94150)). Qed.
Lemma lem7051720 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7051721 (_94151 : int) (_94150 : int) : (term261 _94150 _94151) = (term393 _94150).
Proof. exact (MK_COMB (@lem7051720) (@lem7051519 _94151 _94150)). Qed.
Lemma lem7051722 (_94151 : int) (_94150 : int) : (term273 _94150 _94151) = (term394 _94150).
Proof. exact (MK_COMB (@lem7051721 _94151 _94150) (@lem7051719 _94151 _94150)). Qed.
Lemma lem7051723 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7051724 (_94148 : int) (_94149 : int) : (term274 _94148 _94149) = (term395 _94148 _94149).
Proof. exact (MK_COMB (@lem7051723) (@lem7051329 _94148 _94149)). Qed.
Lemma lem7051725 (_94151 : int) (_94148 : int) (_94149 : int) (_94150 : int) : (term275 _94148 _94149 _94150 _94151) = (term396 _94148 _94149 _94150).
Proof. exact (MK_COMB (@lem7051724 _94148 _94149) (@lem7051722 _94151 _94150)). Qed.
Lemma lem7051726 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7051727 (_94148 : int) : (term276 _94148) = term397.
Proof. exact (MK_COMB (@lem7051726) (@lem7051310 _94148)). Qed.
Lemma lem7051728 (_94151 : int) (_94148 : int) (_94149 : int) (_94150 : int) : (term277 _94148 _94149 _94150 _94151) = (term398 _94148 _94149 _94150).
Proof. exact (MK_COMB (@lem7051727 _94148) (@lem7051725 _94151 _94148 _94149 _94150)). Qed.
Lemma lem7051729 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7051730 (_94151 : int) : (term278 _94151) = (term399 _94151).
Proof. exact (MK_COMB (@lem7051729) (@lem7051130 _94151)). Qed.
Lemma lem7051731 (_94151 : int) (_94148 : int) (_94149 : int) (_94150 : int) : (term279 _94148 _94149 _94150 _94151) = (term400 _94151 _94148 _94149 _94150).
Proof. exact (MK_COMB (@lem7051730 _94151) (@lem7051728 _94151 _94148 _94149 _94150)). Qed.
Lemma lem7051732 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7051733 (_94150 : int) : (term278 _94150) = (term399 _94150).
Proof. exact (MK_COMB (@lem7051732) (@lem7051082 _94150)). Qed.
Lemma lem7051734 (_94151 : int) (_94148 : int) (_94149 : int) (_94150 : int) : (term280 _94148 _94149 _94150 _94151) = (term401 _94151 _94148 _94149 _94150).
Proof. exact (MK_COMB (@lem7051733 _94150) (@lem7051731 _94151 _94148 _94149 _94150)). Qed.
Lemma lem7051735 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7051736 (_94149 : int) : (term278 _94149) = (term399 _94149).
Proof. exact (MK_COMB (@lem7051735) (@lem7051034 _94149)). Qed.
Lemma lem7051737 (_94151 : int) (_94148 : int) (_94149 : int) (_94150 : int) : (term281 _94148 _94149 _94150 _94151) = (term402 _94151 _94148 _94149 _94150).
Proof. exact (MK_COMB (@lem7051736 _94149) (@lem7051734 _94151 _94148 _94149 _94150)). Qed.
Lemma lem7051738 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7051739 (_94148 : int) : (term278 _94148) = (term399 _94148).
Proof. exact (MK_COMB (@lem7051738) (@lem7050986 _94148)). Qed.
Lemma lem7051740 (_94151 : int) (_94148 : int) (_94149 : int) (_94150 : int) : (term282 _94148 _94149 _94150 _94151) = (term403 _94151 _94148 _94149 _94150).
Proof. exact (MK_COMB (@lem7051739 _94148) (@lem7051737 _94151 _94148 _94149 _94150)). Qed.
Lemma lem7051747 (_94151 : int) (_94148 : int) (_94149 : int) (_94150 : int) : (term284 _94148 _94149 _94150 _94151) = (term403 _94151 _94148 _94149 _94150).
Proof. exact (TRANS (@lem7050938 _94148 _94149 _94150 _94151) (@lem7051740 _94151 _94148 _94149 _94150)). Qed.
Lemma lem7051764 (_94148 : int) (_94149 : int) (_94150 : int) : (term396 _94148 _94149 _94150) = (term404 _94148 _94149 _94150).
Proof. exact (@lem19158 (term378 _94150) (term369 _94148 _94149) (term392 _94150)). Qed.
Lemma lem7051767 : term397 = term397.
Proof. exact (eq_refl term397). Qed.
Lemma lem7051768 (_94148 : int) (_94149 : int) (_94150 : int) : (term398 _94148 _94149 _94150) = (term405 _94148 _94149 _94150).
Proof. exact (MK_COMB (@lem7051767) (@lem7051764 _94148 _94149 _94150)). Qed.
Lemma lem7051775 (_94148 : int) (_94149 : int) (_94150 : int) : (term405 _94148 _94149 _94150) = (term406 _94148 _94149 _94150).
Proof. exact (@lem19158 (term407 _94148 _94149 _94150) term362 (term408 _94148 _94149 _94150)). Qed.
Lemma lem7051776 (_94148 : int) (_94149 : int) (_94150 : int) : (term398 _94148 _94149 _94150) = (term406 _94148 _94149 _94150).
Proof. exact (TRANS (@lem7051768 _94148 _94149 _94150) (@lem7051775 _94148 _94149 _94150)). Qed.
Lemma lem7051779 (_94151 : int) : (term399 _94151) = (term399 _94151).
Proof. exact (eq_refl (term399 _94151)). Qed.
Lemma lem7051780 (_94151 : int) (_94148 : int) (_94149 : int) (_94150 : int) : (term400 _94151 _94148 _94149 _94150) = (term409 _94151 _94148 _94149 _94150).
Proof. exact (MK_COMB (@lem7051779 _94151) (@lem7051776 _94148 _94149 _94150)). Qed.
Lemma lem7051787 (_94151 : int) (_94148 : int) (_94149 : int) (_94150 : int) : (term409 _94151 _94148 _94149 _94150) = (term410 _94151 _94148 _94149 _94150).
Proof. exact (@lem19158 (term411 _94148 _94149 _94150) (term312 _94151) (term412 _94148 _94149 _94150)). Qed.
Lemma lem7051788 (_94151 : int) (_94148 : int) (_94149 : int) (_94150 : int) : (term400 _94151 _94148 _94149 _94150) = (term410 _94151 _94148 _94149 _94150).
Proof. exact (TRANS (@lem7051780 _94151 _94148 _94149 _94150) (@lem7051787 _94151 _94148 _94149 _94150)). Qed.
Lemma lem7051791 (_94150 : int) : (term399 _94150) = (term399 _94150).
Proof. exact (eq_refl (term399 _94150)). Qed.
Lemma lem7051792 (_94151 : int) (_94148 : int) (_94149 : int) (_94150 : int) : (term401 _94151 _94148 _94149 _94150) = (term413 _94151 _94148 _94149 _94150).
Proof. exact (MK_COMB (@lem7051791 _94150) (@lem7051788 _94151 _94148 _94149 _94150)). Qed.
Lemma lem7051799 (_94151 : int) (_94148 : int) (_94149 : int) (_94150 : int) : (term413 _94151 _94148 _94149 _94150) = (term414 _94151 _94148 _94149 _94150).
Proof. exact (@lem19158 (term415 _94151 _94148 _94149 _94150) (term312 _94150) (term416 _94151 _94148 _94149 _94150)). Qed.
Lemma lem7051800 (_94151 : int) (_94148 : int) (_94149 : int) (_94150 : int) : (term401 _94151 _94148 _94149 _94150) = (term414 _94151 _94148 _94149 _94150).
Proof. exact (TRANS (@lem7051792 _94151 _94148 _94149 _94150) (@lem7051799 _94151 _94148 _94149 _94150)). Qed.
Lemma lem7051803 (_94149 : int) : (term399 _94149) = (term399 _94149).
Proof. exact (eq_refl (term399 _94149)). Qed.
Lemma lem7051804 (_94151 : int) (_94148 : int) (_94149 : int) (_94150 : int) : (term402 _94151 _94148 _94149 _94150) = (term417 _94151 _94148 _94149 _94150).
Proof. exact (MK_COMB (@lem7051803 _94149) (@lem7051800 _94151 _94148 _94149 _94150)). Qed.
Lemma lem7051811 (_94151 : int) (_94148 : int) (_94149 : int) (_94150 : int) : (term417 _94151 _94148 _94149 _94150) = (term418 _94151 _94148 _94149 _94150).
Proof. exact (@lem19158 (term419 _94151 _94148 _94149 _94150) (term312 _94149) (term420 _94151 _94148 _94149 _94150)). Qed.
Lemma lem7051812 (_94151 : int) (_94148 : int) (_94149 : int) (_94150 : int) : (term402 _94151 _94148 _94149 _94150) = (term418 _94151 _94148 _94149 _94150).
Proof. exact (TRANS (@lem7051804 _94151 _94148 _94149 _94150) (@lem7051811 _94151 _94148 _94149 _94150)). Qed.
Lemma lem7051815 (_94148 : int) : (term399 _94148) = (term399 _94148).
Proof. exact (eq_refl (term399 _94148)). Qed.
Lemma lem7051816 (_94151 : int) (_94148 : int) (_94149 : int) (_94150 : int) : (term403 _94151 _94148 _94149 _94150) = (term421 _94151 _94148 _94149 _94150).
Proof. exact (MK_COMB (@lem7051815 _94148) (@lem7051812 _94151 _94148 _94149 _94150)). Qed.
Lemma lem7051823 (_94151 : int) (_94148 : int) (_94149 : int) (_94150 : int) : (term421 _94151 _94148 _94149 _94150) = (term422 _94151 _94148 _94149 _94150).
Proof. exact (@lem19158 (term423 _94151 _94148 _94149 _94150) (term312 _94148) (term424 _94151 _94148 _94149 _94150)). Qed.
Lemma lem7051824 (_94151 : int) (_94148 : int) (_94149 : int) (_94150 : int) : (term403 _94151 _94148 _94149 _94150) = (term422 _94151 _94148 _94149 _94150).
Proof. exact (TRANS (@lem7051816 _94151 _94148 _94149 _94150) (@lem7051823 _94151 _94148 _94149 _94150)). Qed.
Lemma lem7051825 (_94151 : int) (_94148 : int) (_94149 : int) (_94150 : int) : (term284 _94148 _94149 _94150 _94151) = (term422 _94151 _94148 _94149 _94150).
Proof. exact (TRANS (@lem7051747 _94151 _94148 _94149 _94150) (@lem7051824 _94151 _94148 _94149 _94150)). Qed.
Lemma lem7051835 (_94151 : int) (_94148 : int) (_94149 : int) (_94150 : int) (h1 : term422 _94151 _94148 _94149 _94150) : term422 _94151 _94148 _94149 _94150.
Proof. exact (h1). Qed.
Lemma lem7051836 (_94151 : int) (_94148 : int) (_94149 : int) (_94150 : int) (h1 : term425 _94151 _94148 _94149 _94150) : term425 _94151 _94148 _94149 _94150.
Proof. exact (h1). Qed.
Lemma lem7051837 (_94151 : int) (_94148 : int) (_94149 : int) (_94150 : int) (h1 : term425 _94151 _94148 _94149 _94150) : term423 _94151 _94148 _94149 _94150.
Proof. exact (proj2 (@lem7051836 _94151 _94148 _94149 _94150 h1)). Qed.
Lemma lem7051839 (_94151 : int) (_94148 : int) (_94149 : int) (_94150 : int) (h1 : term425 _94151 _94148 _94149 _94150) : term419 _94151 _94148 _94149 _94150.
Proof. exact (proj2 (@lem7051837 _94151 _94148 _94149 _94150 h1)). Qed.
Lemma lem7051841 (_94151 : int) (_94148 : int) (_94149 : int) (_94150 : int) (h1 : term425 _94151 _94148 _94149 _94150) : term415 _94151 _94148 _94149 _94150.
Proof. exact (proj2 (@lem7051839 _94151 _94148 _94149 _94150 h1)). Qed.
Lemma lem7051843 (_94151 : int) (_94148 : int) (_94149 : int) (_94150 : int) (h1 : term425 _94151 _94148 _94149 _94150) : term411 _94148 _94149 _94150.
Proof. exact (proj2 (@lem7051841 _94151 _94148 _94149 _94150 h1)). Qed.
Lemma lem7051846 (_94151 : int) (_94148 : int) (_94149 : int) (_94150 : int) (h1 : term425 _94151 _94148 _94149 _94150) : term362.
Proof. exact (proj1 (@lem7051843 _94151 _94148 _94149 _94150 h1)). Qed.
Lemma lem7051850 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7051851 : term362 = term426.
Proof. exact (@lem7051850 term236 term292). Qed.
Lemma lem7051853 (x : nat) : (term290 x) = (term291 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7051854 : term292 = term293.
Proof. exact (@lem7051853 term166). Qed.
Lemma lem7051856 (x : nat) : (real_of_num x) = (term288 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7051857 : term236 = term289.
Proof. exact (@lem7051856 (NUMERAL 0)). Qed.
Lemma lem7051858 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7051859 : term238 = term427.
Proof. exact (MK_COMB (@lem7051858) (@lem7051857)). Qed.
Lemma lem7051860 : term426 = term428.
Proof. exact (MK_COMB (@lem7051859) (@lem7051854)). Qed.
Lemma lem7051861 : term429.
Proof. exact (@lem1980026 term236 term248 term292 term248). Qed.
Lemma lem7051863 (m : nat) (n : nat) : (term339 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7051864 : term340 = term341.
Proof. exact (@lem7051863 (NUMERAL 0) term166). Qed.
Lemma lem7051865 : term342 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7051866 (h1 : term342 = (BIT1 0)) : term341 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7051867 : (term342 = (BIT1 0)) = (term341 = True).
Proof. exact (prop_ext (fun h1 : term342 = (BIT1 0) => @lem7051866 h1) (fun h1 : term341 = True => @lem7051865)). Qed.
Lemma lem7051868 : term341 = True.
Proof. exact (EQ_MP (@lem7051867) (@lem7051865)). Qed.
Lemma lem7051869 : term340 = True.
Proof. exact (TRANS (@lem7051864) (@lem7051868)). Qed.
Lemma lem7051870 : True = term340.
Proof. exact (SYM (@lem7051869)). Qed.
Lemma lem7051871 : term340.
Proof. exact (EQ_MP (@lem7051870) (@lem0)). Qed.
Lemma lem7051872 : term430.
Proof. exact (@lem7051861 (@lem7051871)). Qed.
Lemma lem7051874 (m : nat) (n : nat) : (term339 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7051875 : term340 = term341.
Proof. exact (@lem7051874 (NUMERAL 0) term166). Qed.
Lemma lem7051876 : term342 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7051877 (h1 : term342 = (BIT1 0)) : term341 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7051878 : (term342 = (BIT1 0)) = (term341 = True).
Proof. exact (prop_ext (fun h1 : term342 = (BIT1 0) => @lem7051877 h1) (fun h1 : term341 = True => @lem7051876)). Qed.
Lemma lem7051879 : term341 = True.
Proof. exact (EQ_MP (@lem7051878) (@lem7051876)). Qed.
Lemma lem7051880 : term340 = True.
Proof. exact (TRANS (@lem7051875) (@lem7051879)). Qed.
Lemma lem7051881 : True = term340.
Proof. exact (SYM (@lem7051880)). Qed.
Lemma lem7051882 : term340.
Proof. exact (EQ_MP (@lem7051881) (@lem0)). Qed.
Lemma lem7051883 : term428 = term431.
Proof. exact (@lem7051872 (@lem7051882)). Qed.
Lemma lem7051885 (m : nat) (n : nat) : (term322 m n) = (term323 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7051886 : term319 = term324.
Proof. exact (@lem7051885 term166 term166). Qed.
Lemma lem7051887 : (term303 = (BIT1 0)) = (term304 = term166).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7051888 : term304 = term166.
Proof. exact (EQ_MP (@lem7051887) (@lem940073)). Qed.
Lemma lem7051889 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7051890 : term302 = term248.
Proof. exact (MK_COMB (@lem7051889) (@lem7051888)). Qed.
Lemma lem7051891 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7051892 : term324 = term292.
Proof. exact (MK_COMB (@lem7051891) (@lem7051890)). Qed.
Lemma lem7051893 : term319 = term292.
Proof. exact (TRANS (@lem7051886) (@lem7051892)). Qed.
Lemma lem7051895 (x : nat) : (term353 x) = term236.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7051896 : term352 = term236.
Proof. exact (@lem7051895 term166). Qed.
Lemma lem7051897 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7051898 : term432 = term238.
Proof. exact (MK_COMB (@lem7051897) (@lem7051896)). Qed.
Lemma lem7051899 : term431 = term426.
Proof. exact (MK_COMB (@lem7051898) (@lem7051893)). Qed.
Lemma lem7051901 (m : nat) (n : nat) : (term433 m n) = (term434 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7051902 : term426 = term435.
Proof. exact (@lem7051901 (NUMERAL 0) term166). Qed.
Lemma lem7051903 : term342 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7051904 (h1 : term342 = (BIT1 0)) : (term166 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7051905 : (term342 = (BIT1 0)) = ((term166 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term342 = (BIT1 0) => @lem7051904 h1) (fun h1 : (term166 = (NUMERAL 0)) = False => @lem7051903)). Qed.
Lemma lem7051906 : (term166 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7051905) (@lem7051903)). Qed.
Lemma lem7051907 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7051908 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7051909 : term436 = (and True).
Proof. exact (MK_COMB (@lem7051908) (@lem7051907)). Qed.
Lemma lem7051910 : term435 = (True /\ False).
Proof. exact (MK_COMB (@lem7051909) (@lem7051906)). Qed.
Lemma lem7051912 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7051913 : term435 = False.
Proof. exact (TRANS (@lem7051910) (@lem7051912)). Qed.
Lemma lem7051914 : term426 = False.
Proof. exact (TRANS (@lem7051902) (@lem7051913)). Qed.
Lemma lem7051915 : term431 = False.
Proof. exact (TRANS (@lem7051899) (@lem7051914)). Qed.
Lemma lem7051916 : term428 = False.
Proof. exact (TRANS (@lem7051883) (@lem7051915)). Qed.
Lemma lem7051917 : term426 = False.
Proof. exact (TRANS (@lem7051860) (@lem7051916)). Qed.
Lemma lem7051918 : term362 = False.
Proof. exact (TRANS (@lem7051851) (@lem7051917)). Qed.
Lemma lem7051919 (_94151 : int) (_94148 : int) (_94149 : int) (_94150 : int) (h1 : term425 _94151 _94148 _94149 _94150) : False.
Proof. exact (EQ_MP (@lem7051918) (@lem7051846 _94151 _94148 _94149 _94150 h1)). Qed.
Lemma lem7051920 (_94151 : int) (_94148 : int) (_94149 : int) (_94150 : int) (h1 : term437 _94151 _94148 _94149 _94150) : term437 _94151 _94148 _94149 _94150.
Proof. exact (h1). Qed.
Lemma lem7051921 (_94151 : int) (_94148 : int) (_94149 : int) (_94150 : int) (h1 : term437 _94151 _94148 _94149 _94150) : term424 _94151 _94148 _94149 _94150.
Proof. exact (proj2 (@lem7051920 _94151 _94148 _94149 _94150 h1)). Qed.
Lemma lem7051923 (_94151 : int) (_94148 : int) (_94149 : int) (_94150 : int) (h1 : term437 _94151 _94148 _94149 _94150) : term420 _94151 _94148 _94149 _94150.
Proof. exact (proj2 (@lem7051921 _94151 _94148 _94149 _94150 h1)). Qed.
Lemma lem7051925 (_94151 : int) (_94148 : int) (_94149 : int) (_94150 : int) (h1 : term437 _94151 _94148 _94149 _94150) : term416 _94151 _94148 _94149 _94150.
Proof. exact (proj2 (@lem7051923 _94151 _94148 _94149 _94150 h1)). Qed.
Lemma lem7051927 (_94151 : int) (_94148 : int) (_94149 : int) (_94150 : int) (h1 : term437 _94151 _94148 _94149 _94150) : term412 _94148 _94149 _94150.
Proof. exact (proj2 (@lem7051925 _94151 _94148 _94149 _94150 h1)). Qed.
Lemma lem7051930 (_94151 : int) (_94148 : int) (_94149 : int) (_94150 : int) (h1 : term437 _94151 _94148 _94149 _94150) : term362.
Proof. exact (proj1 (@lem7051927 _94151 _94148 _94149 _94150 h1)). Qed.
Lemma lem7051934 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7051935 : term362 = term426.
Proof. exact (@lem7051934 term236 term292). Qed.
Lemma lem7051937 (x : nat) : (term290 x) = (term291 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7051938 : term292 = term293.
Proof. exact (@lem7051937 term166). Qed.
Lemma lem7051940 (x : nat) : (real_of_num x) = (term288 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7051941 : term236 = term289.
Proof. exact (@lem7051940 (NUMERAL 0)). Qed.
Lemma lem7051942 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7051943 : term238 = term427.
Proof. exact (MK_COMB (@lem7051942) (@lem7051941)). Qed.
Lemma lem7051944 : term426 = term428.
Proof. exact (MK_COMB (@lem7051943) (@lem7051938)). Qed.
Lemma lem7051945 : term429.
Proof. exact (@lem1980026 term236 term248 term292 term248). Qed.
Lemma lem7051947 (m : nat) (n : nat) : (term339 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7051948 : term340 = term341.
Proof. exact (@lem7051947 (NUMERAL 0) term166). Qed.
Lemma lem7051949 : term342 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7051950 (h1 : term342 = (BIT1 0)) : term341 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7051951 : (term342 = (BIT1 0)) = (term341 = True).
Proof. exact (prop_ext (fun h1 : term342 = (BIT1 0) => @lem7051950 h1) (fun h1 : term341 = True => @lem7051949)). Qed.
Lemma lem7051952 : term341 = True.
Proof. exact (EQ_MP (@lem7051951) (@lem7051949)). Qed.
Lemma lem7051953 : term340 = True.
Proof. exact (TRANS (@lem7051948) (@lem7051952)). Qed.
Lemma lem7051954 : True = term340.
Proof. exact (SYM (@lem7051953)). Qed.
Lemma lem7051955 : term340.
Proof. exact (EQ_MP (@lem7051954) (@lem0)). Qed.
Lemma lem7051956 : term430.
Proof. exact (@lem7051945 (@lem7051955)). Qed.
Lemma lem7051958 (m : nat) (n : nat) : (term339 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7051959 : term340 = term341.
Proof. exact (@lem7051958 (NUMERAL 0) term166). Qed.
Lemma lem7051960 : term342 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7051961 (h1 : term342 = (BIT1 0)) : term341 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7051962 : (term342 = (BIT1 0)) = (term341 = True).
Proof. exact (prop_ext (fun h1 : term342 = (BIT1 0) => @lem7051961 h1) (fun h1 : term341 = True => @lem7051960)). Qed.
Lemma lem7051963 : term341 = True.
Proof. exact (EQ_MP (@lem7051962) (@lem7051960)). Qed.
Lemma lem7051964 : term340 = True.
Proof. exact (TRANS (@lem7051959) (@lem7051963)). Qed.
Lemma lem7051965 : True = term340.
Proof. exact (SYM (@lem7051964)). Qed.
Lemma lem7051966 : term340.
Proof. exact (EQ_MP (@lem7051965) (@lem0)). Qed.
Lemma lem7051967 : term428 = term431.
Proof. exact (@lem7051956 (@lem7051966)). Qed.
Lemma lem7051969 (m : nat) (n : nat) : (term322 m n) = (term323 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7051970 : term319 = term324.
Proof. exact (@lem7051969 term166 term166). Qed.
Lemma lem7051971 : (term303 = (BIT1 0)) = (term304 = term166).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7051972 : term304 = term166.
Proof. exact (EQ_MP (@lem7051971) (@lem940073)). Qed.
Lemma lem7051973 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7051974 : term302 = term248.
Proof. exact (MK_COMB (@lem7051973) (@lem7051972)). Qed.
Lemma lem7051975 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7051976 : term324 = term292.
Proof. exact (MK_COMB (@lem7051975) (@lem7051974)). Qed.
Lemma lem7051977 : term319 = term292.
Proof. exact (TRANS (@lem7051970) (@lem7051976)). Qed.
Lemma lem7051979 (x : nat) : (term353 x) = term236.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7051980 : term352 = term236.
Proof. exact (@lem7051979 term166). Qed.
Lemma lem7051981 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7051982 : term432 = term238.
Proof. exact (MK_COMB (@lem7051981) (@lem7051980)). Qed.
Lemma lem7051983 : term431 = term426.
Proof. exact (MK_COMB (@lem7051982) (@lem7051977)). Qed.
Lemma lem7051985 (m : nat) (n : nat) : (term433 m n) = (term434 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7051986 : term426 = term435.
Proof. exact (@lem7051985 (NUMERAL 0) term166). Qed.
Lemma lem7051987 : term342 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7051988 (h1 : term342 = (BIT1 0)) : (term166 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7051989 : (term342 = (BIT1 0)) = ((term166 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term342 = (BIT1 0) => @lem7051988 h1) (fun h1 : (term166 = (NUMERAL 0)) = False => @lem7051987)). Qed.
Lemma lem7051990 : (term166 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7051989) (@lem7051987)). Qed.
Lemma lem7051991 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7051992 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7051993 : term436 = (and True).
Proof. exact (MK_COMB (@lem7051992) (@lem7051991)). Qed.
Lemma lem7051994 : term435 = (True /\ False).
Proof. exact (MK_COMB (@lem7051993) (@lem7051990)). Qed.
Lemma lem7051996 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7051997 : term435 = False.
Proof. exact (TRANS (@lem7051994) (@lem7051996)). Qed.
Lemma lem7051998 : term426 = False.
Proof. exact (TRANS (@lem7051986) (@lem7051997)). Qed.
Lemma lem7051999 : term431 = False.
Proof. exact (TRANS (@lem7051983) (@lem7051998)). Qed.
Lemma lem7052000 : term428 = False.
Proof. exact (TRANS (@lem7051967) (@lem7051999)). Qed.
Lemma lem7052001 : term426 = False.
Proof. exact (TRANS (@lem7051944) (@lem7052000)). Qed.
Lemma lem7052002 : term362 = False.
Proof. exact (TRANS (@lem7051935) (@lem7052001)). Qed.
Lemma lem7052003 (_94151 : int) (_94148 : int) (_94149 : int) (_94150 : int) (h1 : term437 _94151 _94148 _94149 _94150) : False.
Proof. exact (EQ_MP (@lem7052002) (@lem7051930 _94151 _94148 _94149 _94150 h1)). Qed.
Lemma lem7052004 (_94151 : int) (_94148 : int) (_94149 : int) (_94150 : int) (h1 : term422 _94151 _94148 _94149 _94150) : False.
Proof. exact (or_elim (@lem7051835 _94151 _94148 _94149 _94150 h1) (fun h0 : term425 _94151 _94148 _94149 _94150 => @lem7051919 _94151 _94148 _94149 _94150 h0) (fun h0 : term437 _94151 _94148 _94149 _94150 => @lem7052003 _94151 _94148 _94149 _94150 h0)). Qed.
Lemma lem7052006 (_94151 : int) (_94148 : int) (_94149 : int) (_94150 : int) (h1 : term422 _94151 _94148 _94149 _94150) : term422 _94151 _94148 _94149 _94150.
Proof. exact (h1). Qed.
Lemma lem7052007 (_94151 : int) (_94148 : int) (_94149 : int) (_94150 : int) (h1 : term422 _94151 _94148 _94149 _94150) : (term422 _94151 _94148 _94149 _94150) = False.
Proof. exact (prop_ext (fun h2 : term422 _94151 _94148 _94149 _94150 => @lem7052004 _94151 _94148 _94149 _94150 h1) (fun h2 : False => @lem7052006 _94151 _94148 _94149 _94150 h1)). Qed.
Lemma lem7052008 (_94151 : int) (_94148 : int) (_94149 : int) (_94150 : int) (h1 : term422 _94151 _94148 _94149 _94150) : False.
Proof. exact (EQ_MP (@lem7052007 _94151 _94148 _94149 _94150 h1) (@lem7052006 _94151 _94148 _94149 _94150 h1)). Qed.
Lemma lem7052009 (_94148 : int) (_94149 : int) (_94150 : int) (_94151 : int) (h1 : term284 _94148 _94149 _94150 _94151) : term284 _94148 _94149 _94150 _94151.
Proof. exact (h1). Qed.
Lemma lem7052010 (_94148 : int) (_94149 : int) (_94150 : int) (_94151 : int) (h1 : term284 _94148 _94149 _94150 _94151) : term422 _94151 _94148 _94149 _94150.
Proof. exact (EQ_MP (@lem7051825 _94151 _94148 _94149 _94150) (@lem7052009 _94148 _94149 _94150 _94151 h1)). Qed.
Lemma lem7052011 (_94148 : int) (_94149 : int) (_94150 : int) (_94151 : int) (h1 : term284 _94148 _94149 _94150 _94151) : (term422 _94151 _94148 _94149 _94150) = False.
Proof. exact (prop_ext (fun h2 : term422 _94151 _94148 _94149 _94150 => @lem7052008 _94151 _94148 _94149 _94150 h2) (fun h2 : False => @lem7052010 _94148 _94149 _94150 _94151 h1)). Qed.
Lemma lem7052012 (_94148 : int) (_94149 : int) (_94150 : int) (_94151 : int) (h1 : term284 _94148 _94149 _94150 _94151) : False.
Proof. exact (EQ_MP (@lem7052011 _94148 _94149 _94150 _94151 h1) (@lem7052010 _94148 _94149 _94150 _94151 h1)). Qed.
Lemma lem7052013 (_94148 : int) (_94149 : int) (_94150 : int) (_94151 : int) : term438 _94148 _94149 _94150 _94151.
Proof. exact (fun h0 : term284 _94148 _94149 _94150 _94151 => @lem7052012 _94148 _94149 _94150 _94151 h0). Qed.
Lemma lem7052014 (_94148 : int) (_94149 : int) (_94150 : int) (_94151 : int) : term439 _94148 _94149 _94150 _94151.
Proof. exact (@lem1386578 (term440 _94148 _94149 _94150 _94151)). Qed.
Lemma lem7052017 (_94148 : int) (_94149 : int) (_94150 : int) (_94151 : int) : term440 _94148 _94149 _94150 _94151.
Proof. exact (@lem7052014 _94148 _94149 _94150 _94151 (@lem7052013 _94148 _94149 _94150 _94151)). Qed.
Lemma lem7052018 (_94148 : int) (_94149 : int) (_94150 : int) (_94151 : int) : (term282 _94148 _94149 _94150 _94151) = (term229 _94148 _94149 _94150 _94151).
Proof. exact (SYM (@lem7050858 _94148 _94149 _94150 _94151)). Qed.
Lemma lem7052019 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7052020 (_94148 : int) (_94149 : int) (_94150 : int) (_94151 : int) : (term440 _94148 _94149 _94150 _94151) = (term194 _94148 _94149 _94150 _94151).
Proof. exact (MK_COMB (@lem7052019) (@lem7052018 _94148 _94149 _94150 _94151)). Qed.
Lemma lem7052021 (_94148 : int) (_94149 : int) (_94150 : int) (_94151 : int) : term194 _94148 _94149 _94150 _94151.
Proof. exact (EQ_MP (@lem7052020 _94148 _94149 _94150 _94151) (@lem7052017 _94148 _94149 _94150 _94151)). Qed.
Lemma lem7052022 (_94148 : int) (_94149 : int) (_94150 : int) (_94151 : int) : term195 _94148 _94149 _94150 _94151.
Proof. exact (EQ_MP (@lem7050629 _94148 _94149 _94150 _94151) (@lem7052021 _94148 _94149 _94150 _94151)). Qed.
Lemma lem7052023 (m : nat) (n : nat) (f : nat -> nat) : term441 m n f.
Proof. exact (@lem7052022 (int_of_num m) (int_of_num n) (term442 f m) (term176 m n f)). Qed.
Lemma lem7052024 (m : nat) (n : nat) (f : nat -> nat) : term443 m n f.
Proof. exact (@lem7052023 m n f (@lem7050619 m)). Qed.
Lemma lem7052025 (m : nat) (n : nat) (f : nat -> nat) : term444 m n f.
Proof. exact (@lem7052024 m n f (@lem7050622 n)). Qed.
Lemma lem7052026 (m : nat) (n : nat) (f : nat -> nat) : term445 m n f.
Proof. exact (@lem7052025 m n f (@lem7050625 f m)). Qed.
Lemma lem7052027 (m : nat) (n : nat) (f : nat -> nat) : term181 m n f.
Proof. exact (@lem7052026 m n f (@lem7050628 m n f)). Qed.
Lemma lem7052028 (m : nat) (f : nat -> nat) : term183 m f.
Proof. exact (fun n : nat => @lem7052027 m n f). Qed.
Lemma lem7052029 (f : nat -> nat) : term185 f.
Proof. exact (fun m : nat => @lem7052028 m f). Qed.
Lemma lem7052030 : term187.
Proof. exact (fun f : nat -> nat => @lem7052029 f). Qed.
Lemma lem7052031 : term187 = term99.
Proof. exact (SYM (@lem7050616)). Qed.
Lemma lem7052032 : term99.
Proof. exact (EQ_MP (@lem7052031) (@lem7052030)). Qed.
Lemma lem7052033 : term99 = (term99 = True).
Proof. exact (@lem7 term99). Qed.
Lemma lem7052034 : term99 = True.
Proof. exact (EQ_MP (@lem7052033) (@lem7052032)). Qed.
Lemma lem7052035 : True = term99.
Proof. exact (SYM (@lem7052034)). Qed.
Lemma lem7052036 : term99.
Proof. exact (EQ_MP (@lem7052035) (@lem0)). Qed.
Lemma lem7052037 : term98.
Proof. exact (EQ_MP (@lem7050308) (@lem7052036)). Qed.
