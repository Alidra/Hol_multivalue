Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_CONST_term_abbrevs.
Require Import CARD_CLAUSES_spec.
Require Import FINITE_INDUCT_STRONG_spec.
Require Import INT_POS_spec.
Require Import NSUM_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1032046_spec.
Require Import thm1032062_spec.
Require Import thm1032066_spec.
Require Import thm1032084_spec.
Require Import thm1032098_spec.
Require Import thm1032118_spec.
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
Require Import thm16485_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17362_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
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
Require Import thm1982753_spec.
Require Import thm1982755_spec.
Require Import thm1982761_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
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
Require Import thm2841413_spec.
Require Import thm2841414_spec.
Require Import thm2841416_spec.
Require Import thm2841417_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem6938832 {A : Type'} : term0 A.
Proof. exact (proj2 (@lem3840691 A)). Qed.
Lemma lem6938833 {A : Type'} (x : A) : term1 A x.
Proof. exact (@lem6938832 A x). Qed.
Lemma lem6938834 {A : Type'} (x : A) : (term1 A x) = (term2 A x).
Proof. exact (eq_refl (term1 A x)). Qed.
Lemma lem6938835 {A : Type'} (x : A) : term2 A x.
Proof. exact (EQ_MP (@lem6938834 A x) (@lem6938833 A x)). Qed.
Lemma lem6938836 {A : Type'} (x : A) (s : A -> Prop) : term3 A x s.
Proof. exact (@lem6938835 A x s). Qed.
Lemma lem6938837 {A : Type'} (x : A) (s : A -> Prop) : (term3 A x s) = (term4 A x s).
Proof. exact (eq_refl (term3 A x s)). Qed.
Lemma lem6938838 {A : Type'} (x : A) (s : A -> Prop) : term4 A x s.
Proof. exact (EQ_MP (@lem6938837 A x s) (@lem6938836 A x s)). Qed.
Lemma lem6938839 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem6938840 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : (term5 A x s) = (term6 A x s).
Proof. exact (@lem6938838 A x s (@lem6938839 A s h1)). Qed.
Lemma lem6938847 {_126525 : Type'} : term7 _126525.
Proof. exact (proj2 (@lem6924916 Prop _126525)). Qed.
Lemma lem6938848 {_126525 : Type'} (x : _126525) : term8 _126525 x.
Proof. exact (@lem6938847 _126525 x). Qed.
Lemma lem6938849 {_126525 : Type'} (x : _126525) : (term8 _126525 x) = (term9 _126525 x).
Proof. exact (eq_refl (term8 _126525 x)). Qed.
Lemma lem6938850 {_126525 : Type'} (x : _126525) : term9 _126525 x.
Proof. exact (EQ_MP (@lem6938849 _126525 x) (@lem6938848 _126525 x)). Qed.
Lemma lem6938851 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) : term10 _126525 x f.
Proof. exact (@lem6938850 _126525 x f). Qed.
Lemma lem6938852 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) : (term10 _126525 x f) = (term11 _126525 x f).
Proof. exact (eq_refl (term10 _126525 x f)). Qed.
Lemma lem6938853 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) : term11 _126525 x f.
Proof. exact (EQ_MP (@lem6938852 _126525 x f) (@lem6938851 _126525 x f)). Qed.
Lemma lem6938854 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) (s : _126525 -> Prop) : term12 _126525 x f s.
Proof. exact (@lem6938853 _126525 x f s). Qed.
Lemma lem6938855 {_126525 : Type'} (x : _126525) (s : _126525 -> Prop) (f : _126525 -> nat) : (term12 _126525 x f s) = (term13 _126525 x s f).
Proof. exact (eq_refl (term12 _126525 x f s)). Qed.
Lemma lem6938856 {_126525 : Type'} (x : _126525) (s : _126525 -> Prop) (f : _126525 -> nat) : term13 _126525 x s f.
Proof. exact (EQ_MP (@lem6938855 _126525 x s f) (@lem6938854 _126525 x f s)). Qed.
Lemma lem6938857 {_126525 : Type'} (s : _126525 -> Prop) (h1 : @FINITE _126525 s) : @FINITE _126525 s.
Proof. exact (h1). Qed.
Lemma lem6938858 {_126525 : Type'} (x : _126525) (f : _126525 -> nat) (s : _126525 -> Prop) (h1 : @FINITE _126525 s) : (term14 _126525 x s f) = (term15 _126525 x s f).
Proof. exact (@lem6938856 _126525 x s f (@lem6938857 _126525 s h1)). Qed.
Lemma lem6938864 {_126486 : Type'} : term16 _126486.
Proof. exact (proj1 (@lem6924916 _126486 Prop)). Qed.
Lemma lem6938865 {_126486 : Type'} (f : _126486 -> nat) : term17 _126486 f.
Proof. exact (@lem6938864 _126486 f). Qed.
Lemma lem6938866 {_126486 : Type'} (f : _126486 -> nat) : (term17 _126486 f) = ((@nsum _126486 (@EMPTY _126486) f) = (NUMERAL 0)).
Proof. exact (eq_refl (term17 _126486 f)). Qed.
Lemma lem6938868 {A : Type'} (h1 : term18 A) : term18 A.
Proof. exact (h1). Qed.
Lemma lem6938869 {A : Type'} (P : type686 A) (h1 : term18 A) : term19 A P.
Proof. exact (@lem6938868 A h1 P). Qed.
Lemma lem6938870 {A : Type'} (P : type686 A) : (term19 A P) = (term20 A P).
Proof. exact (eq_refl (term19 A P)). Qed.
Lemma lem6938871 {A : Type'} (P : type686 A) (h1 : term18 A) : term20 A P.
Proof. exact (EQ_MP (@lem6938870 A P) (@lem6938869 A P h1)). Qed.
Lemma lem6938872 {A : Type'} (P : type686 A) (h1 : term21 A P) : term21 A P.
Proof. exact (h1). Qed.
Lemma lem6938873 {A : Type'} (P : type686 A) (h1 : term18 A) (h2 : term21 A P) : term22 A P.
Proof. exact (@lem6938871 A P h1 (@lem6938872 A P h2)). Qed.
Lemma lem6938874 {A : Type'} (P : type686 A) (h1 : term21 A P) : term23 A P.
Proof. exact (fun h0 : term18 A => @lem6938873 A P h0 h1). Qed.
Lemma lem6938875 {A : Type'} (h1 : term18 A) : term18 A.
Proof. exact (h1). Qed.
Lemma lem6938876 {A : Type'} (P : type686 A) (h1 : term18 A) (h2 : term21 A P) : term22 A P.
Proof. exact (@lem6938874 A P h2 (@lem6938875 A h1)). Qed.
Lemma lem6938877 {A : Type'} (P : type686 A) (h1 : term18 A) : term20 A P.
Proof. exact (fun h0 : term21 A P => @lem6938876 A P h1 h0). Qed.
Lemma lem6938878 {A : Type'} (h1 : term18 A) : term18 A.
Proof. exact (fun P : type686 A => @lem6938877 A P h1). Qed.
Lemma lem6938879 {A : Type'} : term24 A.
Proof. exact (fun h0 : term18 A => @lem6938878 A h0). Qed.
Lemma lem6938880 {A : Type'} : term18 A.
Proof. exact (@lem6938879 A (@lem3558722 A)). Qed.
Lemma lem6938881 {A : Type'} (P : type686 A) : term19 A P.
Proof. exact (@lem6938880 A P). Qed.
Lemma lem6938882 {A : Type'} (P : type686 A) : (term19 A P) = (term20 A P).
Proof. exact (eq_refl (term19 A P)). Qed.
Lemma lem6938885 {A : Type'} (P : type686 A) : term20 A P.
Proof. exact (EQ_MP (@lem6938882 A P) (@lem6938881 A P)). Qed.
Lemma lem6938886 {_127196 : Type'} (P : type686 _127196) : term20 _127196 P.
Proof. exact (@lem6938885 _127196 P). Qed.
Lemma lem6938887 {_127196 : Type'} (c : nat) : term25 _127196 c.
Proof. exact (@lem6938886 _127196 (term26 _127196 c)). Qed.
Lemma lem6938888 {_127196 : Type'} (c : nat) : (term27 _127196 c) = ((term28 _127196 c) = (term29 _127196 c)).
Proof. exact (eq_refl (term27 _127196 c)). Qed.
Lemma lem6938889 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6938890 {_127196 : Type'} (c : nat) : (term30 _127196 c) = (term31 _127196 c).
Proof. exact (MK_COMB (@lem6938889) (@lem6938888 _127196 c)). Qed.
Lemma lem6938891 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : (term32 _127196 c s) = ((term33 _127196 s c) = (term34 _127196 s c)).
Proof. exact (eq_refl (term32 _127196 c s)). Qed.
Lemma lem6938892 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6938893 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : (term35 _127196 c s) = (term36 _127196 s c).
Proof. exact (MK_COMB (@lem6938892) (@lem6938891 _127196 s c)). Qed.
Lemma lem6938894 {_127196 : Type'} (x : _127196) (s : _127196 -> Prop) : (term37 _127196 x s) = (term37 _127196 x s).
Proof. exact (eq_refl (term37 _127196 x s)). Qed.
Lemma lem6938895 {_127196 : Type'} (c : nat) (x : _127196) (s : _127196 -> Prop) : (term38 _127196 c x s) = (term39 _127196 c x s).
Proof. exact (MK_COMB (@lem6938893 _127196 s c) (@lem6938894 _127196 x s)). Qed.
Lemma lem6938896 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6938897 {_127196 : Type'} (c : nat) (x : _127196) (s : _127196 -> Prop) : (term40 _127196 c x s) = (term41 _127196 c x s).
Proof. exact (MK_COMB (@lem6938896) (@lem6938895 _127196 c x s)). Qed.
Lemma lem6938898 {_127196 : Type'} (x : _127196) (s : _127196 -> Prop) (c : nat) : (term42 _127196 c x s) = ((term43 _127196 x s c) = (term44 _127196 x s c)).
Proof. exact (eq_refl (term42 _127196 c x s)). Qed.
Lemma lem6938899 {_127196 : Type'} (x : _127196) (s : _127196 -> Prop) (c : nat) : (term45 _127196 c x s) = (term46 _127196 x s c).
Proof. exact (MK_COMB (@lem6938897 _127196 c x s) (@lem6938898 _127196 x s c)). Qed.
Lemma lem6938900 {_127196 : Type'} (x : _127196) (c : nat) : (term47 _127196 c x) = (term48 _127196 x c).
Proof. exact (fun_ext (fun s : _127196 -> Prop => @lem6938899 _127196 x s c)). Qed.
Lemma lem6938901 {_127196 : Type'} : (@all (_127196 -> Prop)) = (@all (_127196 -> Prop)).
Proof. exact (eq_refl (@all (_127196 -> Prop))). Qed.
Lemma lem6938902 {_127196 : Type'} (x : _127196) (c : nat) : (term49 _127196 c x) = (term50 _127196 x c).
Proof. exact (MK_COMB (@lem6938901 _127196) (@lem6938900 _127196 x c)). Qed.
Lemma lem6938903 {_127196 : Type'} (c : nat) : (term51 _127196 c) = (term52 _127196 c).
Proof. exact (fun_ext (fun x : _127196 => @lem6938902 _127196 x c)). Qed.
Lemma lem6938904 {_127196 : Type'} : (@all _127196) = (@all _127196).
Proof. exact (eq_refl (@all _127196)). Qed.
Lemma lem6938905 {_127196 : Type'} (c : nat) : (term53 _127196 c) = (term54 _127196 c).
Proof. exact (MK_COMB (@lem6938904 _127196) (@lem6938903 _127196 c)). Qed.
Lemma lem6938906 {_127196 : Type'} (c : nat) : (term55 _127196 c) = (term56 _127196 c).
Proof. exact (MK_COMB (@lem6938890 _127196 c) (@lem6938905 _127196 c)). Qed.
Lemma lem6938907 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6938908 {_127196 : Type'} (c : nat) : (term57 _127196 c) = (term58 _127196 c).
Proof. exact (MK_COMB (@lem6938907) (@lem6938906 _127196 c)). Qed.
Lemma lem6938909 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : (term32 _127196 c s) = ((term33 _127196 s c) = (term34 _127196 s c)).
Proof. exact (eq_refl (term32 _127196 c s)). Qed.
Lemma lem6938910 {_127196 : Type'} (s : _127196 -> Prop) : (term59 _127196 s) = (term59 _127196 s).
Proof. exact (eq_refl (term59 _127196 s)). Qed.
Lemma lem6938911 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : (term60 _127196 c s) = (term61 _127196 s c).
Proof. exact (MK_COMB (@lem6938910 _127196 s) (@lem6938909 _127196 s c)). Qed.
Lemma lem6938912 {_127196 : Type'} (c : nat) : (term62 _127196 c) = (term63 _127196 c).
Proof. exact (fun_ext (fun s : _127196 -> Prop => @lem6938911 _127196 s c)). Qed.
Lemma lem6938913 {_127196 : Type'} : (@all (_127196 -> Prop)) = (@all (_127196 -> Prop)).
Proof. exact (eq_refl (@all (_127196 -> Prop))). Qed.
Lemma lem6938914 {_127196 : Type'} (c : nat) : (term64 _127196 c) = (term65 _127196 c).
Proof. exact (MK_COMB (@lem6938913 _127196) (@lem6938912 _127196 c)). Qed.
Lemma lem6938915 {_127196 : Type'} (c : nat) : (term25 _127196 c) = (term66 _127196 c).
Proof. exact (MK_COMB (@lem6938908 _127196 c) (@lem6938914 _127196 c)). Qed.
Lemma lem6938916 {_127196 : Type'} (c : nat) : term66 _127196 c.
Proof. exact (EQ_MP (@lem6938915 _127196 c) (@lem6938887 _127196 c)). Qed.
Lemma lem6938922 {_126486 : Type'} (f : _126486 -> nat) : (@nsum _126486 (@EMPTY _126486) f) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem6938866 _126486 f) (@lem6938865 _126486 f)). Qed.
Lemma lem6938923 {_127196 : Type'} (f : _127196 -> nat) : (@nsum _127196 (@EMPTY _127196) f) = (NUMERAL 0).
Proof. exact (@lem6938922 _127196 f). Qed.
Lemma lem6938924 {_127196 : Type'} (c : nat) : (term28 _127196 c) = (NUMERAL 0).
Proof. exact (@lem6938923 _127196 (term67 _127196 c)). Qed.
Lemma lem6938925 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6938926 {_127196 : Type'} (c : nat) : (term68 _127196 c) = term69.
Proof. exact (MK_COMB (@lem6938925) (@lem6938924 _127196 c)). Qed.
Lemma lem6938928 {A : Type'} : (@CARD A (@EMPTY A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem3840691 A)). Qed.
Lemma lem6938929 {_127196 : Type'} : (@CARD _127196 (@EMPTY _127196)) = (NUMERAL 0).
Proof. exact (@lem6938928 _127196). Qed.
Lemma lem6938930 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem6938931 {_127196 : Type'} : (term70 _127196) = term71.
Proof. exact (MK_COMB (@lem6938930) (@lem6938929 _127196)). Qed.
Lemma lem6938932 (c : nat) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem6938933 {_127196 : Type'} (c : nat) : (term29 _127196 c) = (term72 c).
Proof. exact (MK_COMB (@lem6938931 _127196) (@lem6938932 c)). Qed.
Lemma lem6938934 {_127196 : Type'} (c : nat) : ((term28 _127196 c) = (term29 _127196 c)) = ((NUMERAL 0) = (term72 c)).
Proof. exact (MK_COMB (@lem6938926 _127196 c) (@lem6938933 _127196 c)). Qed.
Lemma lem6938937 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6938938 {_127196 : Type'} (c : nat) : (term31 _127196 c) = (term73 c).
Proof. exact (MK_COMB (@lem6938937) (@lem6938934 _127196 c)). Qed.
Lemma lem6938952 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term74 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6938953 (p : Prop) (q : Prop) (p' : Prop) : term75 p q p'.
Proof. exact (fun q' : Prop => @lem6938952 p q p' q'). Qed.
Lemma lem6938954 (p : Prop) (q : Prop) : term76 p q.
Proof. exact (fun p' : Prop => @lem6938953 p q p'). Qed.
Lemma lem6938955 {_127196 : Type'} (x : _127196) (s : _127196 -> Prop) (c : nat) : term77 _127196 x s c.
Proof. exact (@lem6938954 (term39 _127196 c x s) ((term43 _127196 x s c) = (term44 _127196 x s c))). Qed.
Lemma lem6938956 {_127196 : Type'} (x : _127196) (s : _127196 -> Prop) (c : nat) (p' : Prop) : term78 _127196 x s c p'.
Proof. exact (@lem6938955 _127196 x s c p'). Qed.
Lemma lem6938957 {_127196 : Type'} (x : _127196) (s : _127196 -> Prop) (c : nat) (p' : Prop) : (term78 _127196 x s c p') = (term79 _127196 x s c p').
Proof. exact (eq_refl (term78 _127196 x s c p')). Qed.
Lemma lem6938958 {_127196 : Type'} (x : _127196) (s : _127196 -> Prop) (c : nat) (p' : Prop) : term79 _127196 x s c p'.
Proof. exact (EQ_MP (@lem6938957 _127196 x s c p') (@lem6938956 _127196 x s c p')). Qed.
Lemma lem6938959 {_127196 : Type'} (x : _127196) (s : _127196 -> Prop) (c : nat) (p' : Prop) (q' : Prop) : term80 _127196 x s c p' q'.
Proof. exact (@lem6938958 _127196 x s c p' q'). Qed.
Lemma lem6938960 {_127196 : Type'} (x : _127196) (s : _127196 -> Prop) (c : nat) (p' : Prop) (q' : Prop) : (term80 _127196 x s c p' q') = (term81 _127196 x s c p' q').
Proof. exact (eq_refl (term80 _127196 x s c p' q')). Qed.
Lemma lem6938961 {_127196 : Type'} (x : _127196) (s : _127196 -> Prop) (c : nat) (p' : Prop) (q' : Prop) : term81 _127196 x s c p' q'.
Proof. exact (EQ_MP (@lem6938960 _127196 x s c p' q') (@lem6938959 _127196 x s c p' q')). Qed.
Lemma lem6938968 {_127196 : Type'} (c : nat) (x : _127196) (s : _127196 -> Prop) : (term39 _127196 c x s) = (term39 _127196 c x s).
Proof. exact (eq_refl (term39 _127196 c x s)). Qed.
Lemma lem6938969 {_127196 : Type'} (c : nat) (x : _127196) (s : _127196 -> Prop) (q' : Prop) : term82 _127196 c x s q'.
Proof. exact (@lem6938961 _127196 x s c (term39 _127196 c x s) q'). Qed.
Lemma lem6938970 {_127196 : Type'} (c : nat) (x : _127196) (s : _127196 -> Prop) (q' : Prop) : term83 _127196 c x s q'.
Proof. exact (@lem6938969 _127196 c x s q' (@lem6938968 _127196 c x s)). Qed.
Lemma lem6938971 {_127196 : Type'} (c : nat) (x : _127196) (s : _127196 -> Prop) (h1 : term39 _127196 c x s) : term39 _127196 c x s.
Proof. exact (h1). Qed.
Lemma lem6938972 {_127196 : Type'} (c : nat) (x : _127196) (s : _127196 -> Prop) (h1 : term39 _127196 c x s) : term37 _127196 x s.
Proof. exact (proj2 (@lem6938971 _127196 c x s h1)). Qed.
Lemma lem6938973 {_127196 : Type'} (c : nat) (x : _127196) (s : _127196 -> Prop) (h1 : term39 _127196 c x s) : @FINITE _127196 s.
Proof. exact (proj2 (@lem6938972 _127196 c x s h1)). Qed.
Lemma lem6938974 {_127196 : Type'} (s : _127196 -> Prop) : (@FINITE _127196 s) = ((@FINITE _127196 s) = True).
Proof. exact (@lem7 (@FINITE _127196 s)). Qed.
Lemma lem6938976 {_127196 : Type'} (c : nat) (x : _127196) (s : _127196 -> Prop) (h1 : term39 _127196 c x s) : term84 _127196 x s.
Proof. exact (proj1 (@lem6938972 _127196 c x s h1)). Qed.
Lemma lem6938977 {_127196 : Type'} (x : _127196) (s : _127196 -> Prop) : term85 _127196 x s.
Proof. exact (@lem82 (@IN _127196 x s)). Qed.
Lemma lem6938983 {_126525 : Type'} (x : _126525) (s : _126525 -> Prop) (f : _126525 -> nat) : term13 _126525 x s f.
Proof. exact (fun h0 : @FINITE _126525 s => @lem6938858 _126525 x f s h0). Qed.
Lemma lem6938984 {_127196 : Type'} (x : _127196) (s : _127196 -> Prop) (f : _127196 -> nat) : term13 _127196 x s f.
Proof. exact (@lem6938983 _127196 x s f). Qed.
Lemma lem6938985 {_127196 : Type'} (x : _127196) (s : _127196 -> Prop) (c : nat) : term86 _127196 x s c.
Proof. exact (@lem6938984 _127196 x s (term67 _127196 c)). Qed.
Lemma lem6938987 {_127196 : Type'} (c : nat) (x : _127196) (s : _127196 -> Prop) (h1 : term39 _127196 c x s) : (@FINITE _127196 s) = True.
Proof. exact (EQ_MP (@lem6938974 _127196 s) (@lem6938973 _127196 c x s h1)). Qed.
Lemma lem6938988 {_127196 : Type'} (c : nat) (x : _127196) (s : _127196 -> Prop) (h1 : term39 _127196 c x s) : True = (@FINITE _127196 s).
Proof. exact (SYM (@lem6938987 _127196 c x s h1)). Qed.
Lemma lem6938989 {_127196 : Type'} (c : nat) (x : _127196) (s : _127196 -> Prop) (h1 : term39 _127196 c x s) : @FINITE _127196 s.
Proof. exact (EQ_MP (@lem6938988 _127196 c x s h1) (@lem0)). Qed.
Lemma lem6938990 {_127196 : Type'} (c : nat) (x : _127196) (s : _127196 -> Prop) (h1 : term39 _127196 c x s) : (term43 _127196 x s c) = (term87 _127196 x s c).
Proof. exact (@lem6938985 _127196 x s c (@lem6938989 _127196 c x s h1)). Qed.
Lemma lem6938992 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term88 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem6938993 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term89 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem6938992 _2963 g t e g' t' e'). Qed.
Lemma lem6938994 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term90 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem6938993 _2963 g t e g' t'). Qed.
Lemma lem6938995 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term91 _2963 g t e.
Proof. exact (fun g' : Prop => @lem6938994 _2963 g t e g'). Qed.
Lemma lem6938996 (g : Prop) (t : nat) (e : nat) : term92 g t e.
Proof. exact (@lem6938995 nat g t e). Qed.
Lemma lem6938997 {_127196 : Type'} (x : _127196) (s : _127196 -> Prop) (c : nat) : term93 _127196 x s c.
Proof. exact (@lem6938996 (@IN _127196 x s) (term33 _127196 s c) (term94 _127196 x s c)). Qed.
Lemma lem6938998 {_127196 : Type'} (x : _127196) (s : _127196 -> Prop) (c : nat) (g' : Prop) : term95 _127196 x s c g'.
Proof. exact (@lem6938997 _127196 x s c g'). Qed.
Lemma lem6938999 {_127196 : Type'} (x : _127196) (s : _127196 -> Prop) (c : nat) (g' : Prop) : (term95 _127196 x s c g') = (term96 _127196 x s c g').
Proof. exact (eq_refl (term95 _127196 x s c g')). Qed.
Lemma lem6939000 {_127196 : Type'} (x : _127196) (s : _127196 -> Prop) (c : nat) (g' : Prop) : term96 _127196 x s c g'.
Proof. exact (EQ_MP (@lem6938999 _127196 x s c g') (@lem6938998 _127196 x s c g')). Qed.
Lemma lem6939001 {_127196 : Type'} (x : _127196) (s : _127196 -> Prop) (c : nat) (g' : Prop) (t' : nat) : term97 _127196 x s c g' t'.
Proof. exact (@lem6939000 _127196 x s c g' t'). Qed.
Lemma lem6939002 {_127196 : Type'} (x : _127196) (s : _127196 -> Prop) (c : nat) (g' : Prop) (t' : nat) : (term97 _127196 x s c g' t') = (term98 _127196 x s c g' t').
Proof. exact (eq_refl (term97 _127196 x s c g' t')). Qed.
Lemma lem6939003 {_127196 : Type'} (x : _127196) (s : _127196 -> Prop) (c : nat) (g' : Prop) (t' : nat) : term98 _127196 x s c g' t'.
Proof. exact (EQ_MP (@lem6939002 _127196 x s c g' t') (@lem6939001 _127196 x s c g' t')). Qed.
Lemma lem6939004 {_127196 : Type'} (x : _127196) (s : _127196 -> Prop) (c : nat) (g' : Prop) (t' : nat) (e' : nat) : term99 _127196 x s c g' t' e'.
Proof. exact (@lem6939003 _127196 x s c g' t' e'). Qed.
Lemma lem6939005 {_127196 : Type'} (x : _127196) (s : _127196 -> Prop) (c : nat) (g' : Prop) (t' : nat) (e' : nat) : (term99 _127196 x s c g' t' e') = (term100 _127196 x s c g' t' e').
Proof. exact (eq_refl (term99 _127196 x s c g' t' e')). Qed.
Lemma lem6939006 {_127196 : Type'} (x : _127196) (s : _127196 -> Prop) (c : nat) (g' : Prop) (t' : nat) (e' : nat) : term100 _127196 x s c g' t' e'.
Proof. exact (EQ_MP (@lem6939005 _127196 x s c g' t' e') (@lem6939004 _127196 x s c g' t' e')). Qed.
Lemma lem6939008 {_127196 : Type'} (c : nat) (x : _127196) (s : _127196 -> Prop) (h1 : term39 _127196 c x s) : (@IN _127196 x s) = False.
Proof. exact (@lem6938977 _127196 x s (@lem6938976 _127196 c x s h1)). Qed.
Lemma lem6939009 {_127196 : Type'} (x : _127196) (s : _127196 -> Prop) (c : nat) (t' : nat) (e' : nat) : term101 _127196 x s c t' e'.
Proof. exact (@lem6939006 _127196 x s c False t' e'). Qed.
Lemma lem6939010 {_127196 : Type'} (t' : nat) (e' : nat) (c : nat) (x : _127196) (s : _127196 -> Prop) (h1 : term39 _127196 c x s) : term102 _127196 x s c t' e'.
Proof. exact (@lem6939009 _127196 x s c t' e' (@lem6939008 _127196 c x s h1)). Qed.
Lemma lem6939015 {_127196 : Type'} (c : nat) (x : _127196) (s : _127196 -> Prop) (h1 : term39 _127196 c x s) : (term33 _127196 s c) = (term34 _127196 s c).
Proof. exact (proj1 (@lem6938971 _127196 c x s h1)). Qed.
Lemma lem6939016 {_127196 : Type'} (c : nat) (x : _127196) (s : _127196 -> Prop) (h1 : term39 _127196 c x s) : (term33 _127196 s c) = (term34 _127196 s c).
Proof. exact (@lem6939015 _127196 c x s h1). Qed.
Lemma lem6939017 {_127196 : Type'} (c : nat) (x : _127196) (s : _127196 -> Prop) (h1 : term39 _127196 c x s) : term103 _127196 s c.
Proof. exact (fun h0 : False => @lem6939016 _127196 c x s h1). Qed.
Lemma lem6939018 {_127196 : Type'} (e' : nat) (c : nat) (x : _127196) (s : _127196 -> Prop) (h1 : term39 _127196 c x s) : term104 _127196 x s c e'.
Proof. exact (@lem6939010 _127196 (term34 _127196 s c) e' c x s h1). Qed.
Lemma lem6939019 {_127196 : Type'} (e' : nat) (c : nat) (x : _127196) (s : _127196 -> Prop) (h1 : term39 _127196 c x s) : term105 _127196 x s c e'.
Proof. exact (@lem6939018 _127196 e' c x s h1 (@lem6939017 _127196 c x s h1)). Qed.
Lemma lem6939026 {A B : Type'} (f : A -> B) (y : A) : (term106 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem6939027 {_127196 : Type'} (f : _127196 -> nat) (y : _127196) : (term107 _127196 f y) = (f y).
Proof. exact (@lem6939026 _127196 nat f y). Qed.
Lemma lem6939028 {_127196 : Type'} (c : nat) (x : _127196) : (term108 _127196 c x) = (term109 _127196 c x).
Proof. exact (@lem6939027 _127196 (term67 _127196 c) x). Qed.
Lemma lem6939029 {_127196 : Type'} (n : _127196) (c : nat) : (term109 _127196 c n) = c.
Proof. exact (eq_refl (term109 _127196 c n)). Qed.
Lemma lem6939030 {_127196 : Type'} (c : nat) : (term110 _127196 c) = (term67 _127196 c).
Proof. exact (fun_ext (fun n : _127196 => @lem6939029 _127196 n c)). Qed.
Lemma lem6939031 {_127196 : Type'} (x : _127196) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6939032 {_127196 : Type'} (c : nat) (x : _127196) : (term108 _127196 c x) = (term109 _127196 c x).
Proof. exact (MK_COMB (@lem6939030 _127196 c) (@lem6939031 _127196 x)). Qed.
Lemma lem6939033 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6939034 {_127196 : Type'} (c : nat) (x : _127196) : (term111 _127196 c x) = (term112 _127196 c x).
Proof. exact (MK_COMB (@lem6939033) (@lem6939032 _127196 c x)). Qed.
Lemma lem6939035 {_127196 : Type'} (x : _127196) (c : nat) : (term109 _127196 c x) = c.
Proof. exact (eq_refl (term109 _127196 c x)). Qed.
Lemma lem6939036 {_127196 : Type'} (x : _127196) (c : nat) : ((term108 _127196 c x) = (term109 _127196 c x)) = ((term109 _127196 c x) = c).
Proof. exact (MK_COMB (@lem6939034 _127196 c x) (@lem6939035 _127196 x c)). Qed.
Lemma lem6939037 {_127196 : Type'} (x : _127196) (c : nat) : (term109 _127196 c x) = c.
Proof. exact (EQ_MP (@lem6939036 _127196 x c) (@lem6939028 _127196 c x)). Qed.
Lemma lem6939038 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem6939039 {_127196 : Type'} (x : _127196) (c : nat) : (term113 _127196 c x) = (Nat.add c).
Proof. exact (MK_COMB (@lem6939038) (@lem6939037 _127196 x c)). Qed.
Lemma lem6939041 {_127196 : Type'} (c : nat) (x : _127196) (s : _127196 -> Prop) (h1 : term39 _127196 c x s) : (term33 _127196 s c) = (term34 _127196 s c).
Proof. exact (proj1 (@lem6938971 _127196 c x s h1)). Qed.
Lemma lem6939042 {_127196 : Type'} (c : nat) (x : _127196) (s : _127196 -> Prop) (h1 : term39 _127196 c x s) : (term33 _127196 s c) = (term34 _127196 s c).
Proof. exact (@lem6939041 _127196 c x s h1). Qed.
Lemma lem6939043 {_127196 : Type'} (c : nat) (x : _127196) (s : _127196 -> Prop) (h1 : term39 _127196 c x s) : (term94 _127196 x s c) = (term114 _127196 s c).
Proof. exact (MK_COMB (@lem6939039 _127196 x c) (@lem6939042 _127196 c x s h1)). Qed.
Lemma lem6939044 {_127196 : Type'} (c : nat) (x : _127196) (s : _127196 -> Prop) (h1 : term39 _127196 c x s) : term115 _127196 x s c.
Proof. exact (fun h0 : ~ False => @lem6939043 _127196 c x s h1). Qed.
Lemma lem6939045 {_127196 : Type'} (c : nat) (x : _127196) (s : _127196 -> Prop) (h1 : term39 _127196 c x s) : term116 _127196 x s c.
Proof. exact (@lem6939019 _127196 (term114 _127196 s c) c x s h1). Qed.
Lemma lem6939046 {_127196 : Type'} (c : nat) (x : _127196) (s : _127196 -> Prop) (h1 : term39 _127196 c x s) : (term87 _127196 x s c) = (term117 _127196 s c).
Proof. exact (@lem6939045 _127196 c x s h1 (@lem6939044 _127196 c x s h1)). Qed.
Lemma lem6939048 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem6939049 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem6939048 nat t1 t2). Qed.
Lemma lem6939050 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : (term117 _127196 s c) = (term114 _127196 s c).
Proof. exact (@lem6939049 (term34 _127196 s c) (term114 _127196 s c)). Qed.
Lemma lem6939051 {_127196 : Type'} (c : nat) (x : _127196) (s : _127196 -> Prop) (h1 : term39 _127196 c x s) : (term87 _127196 x s c) = (term114 _127196 s c).
Proof. exact (TRANS (@lem6939046 _127196 c x s h1) (@lem6939050 _127196 s c)). Qed.
Lemma lem6939052 {_127196 : Type'} (c : nat) (x : _127196) (s : _127196 -> Prop) (h1 : term39 _127196 c x s) : (term43 _127196 x s c) = (term114 _127196 s c).
Proof. exact (TRANS (@lem6938990 _127196 c x s h1) (@lem6939051 _127196 c x s h1)). Qed.
Lemma lem6939053 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6939054 {_127196 : Type'} (c : nat) (x : _127196) (s : _127196 -> Prop) (h1 : term39 _127196 c x s) : (term118 _127196 x s c) = (term119 _127196 s c).
Proof. exact (MK_COMB (@lem6939053) (@lem6939052 _127196 c x s h1)). Qed.
Lemma lem6939056 {A : Type'} (x : A) (s : A -> Prop) : term4 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem6938840 A x s h0). Qed.
Lemma lem6939057 {_127196 : Type'} (x : _127196) (s : _127196 -> Prop) : term4 _127196 x s.
Proof. exact (@lem6939056 _127196 x s). Qed.
Lemma lem6939059 {_127196 : Type'} (c : nat) (x : _127196) (s : _127196 -> Prop) (h1 : term39 _127196 c x s) : (@FINITE _127196 s) = True.
Proof. exact (EQ_MP (@lem6938974 _127196 s) (@lem6938973 _127196 c x s h1)). Qed.
Lemma lem6939060 {_127196 : Type'} (c : nat) (x : _127196) (s : _127196 -> Prop) (h1 : term39 _127196 c x s) : True = (@FINITE _127196 s).
Proof. exact (SYM (@lem6939059 _127196 c x s h1)). Qed.
Lemma lem6939061 {_127196 : Type'} (c : nat) (x : _127196) (s : _127196 -> Prop) (h1 : term39 _127196 c x s) : @FINITE _127196 s.
Proof. exact (EQ_MP (@lem6939060 _127196 c x s h1) (@lem0)). Qed.
Lemma lem6939062 {_127196 : Type'} (c : nat) (x : _127196) (s : _127196 -> Prop) (h1 : term39 _127196 c x s) : (term5 _127196 x s) = (term6 _127196 x s).
Proof. exact (@lem6939057 _127196 x s (@lem6939061 _127196 c x s h1)). Qed.
Lemma lem6939064 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term88 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem6939065 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term89 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem6939064 _2963 g t e g' t' e'). Qed.
Lemma lem6939066 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term90 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem6939065 _2963 g t e g' t'). Qed.
Lemma lem6939067 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term91 _2963 g t e.
Proof. exact (fun g' : Prop => @lem6939066 _2963 g t e g'). Qed.
Lemma lem6939068 (g : Prop) (t : nat) (e : nat) : term92 g t e.
Proof. exact (@lem6939067 nat g t e). Qed.
Lemma lem6939069 {_127196 : Type'} (x : _127196) (s : _127196 -> Prop) : term120 _127196 x s.
Proof. exact (@lem6939068 (@IN _127196 x s) (@CARD _127196 s) (term121 _127196 s)). Qed.
Lemma lem6939070 {_127196 : Type'} (x : _127196) (s : _127196 -> Prop) (g' : Prop) : term122 _127196 x s g'.
Proof. exact (@lem6939069 _127196 x s g'). Qed.
Lemma lem6939071 {_127196 : Type'} (x : _127196) (s : _127196 -> Prop) (g' : Prop) : (term122 _127196 x s g') = (term123 _127196 x s g').
Proof. exact (eq_refl (term122 _127196 x s g')). Qed.
Lemma lem6939072 {_127196 : Type'} (x : _127196) (s : _127196 -> Prop) (g' : Prop) : term123 _127196 x s g'.
Proof. exact (EQ_MP (@lem6939071 _127196 x s g') (@lem6939070 _127196 x s g')). Qed.
Lemma lem6939073 {_127196 : Type'} (x : _127196) (s : _127196 -> Prop) (g' : Prop) (t' : nat) : term124 _127196 x s g' t'.
Proof. exact (@lem6939072 _127196 x s g' t'). Qed.
Lemma lem6939074 {_127196 : Type'} (x : _127196) (s : _127196 -> Prop) (g' : Prop) (t' : nat) : (term124 _127196 x s g' t') = (term125 _127196 x s g' t').
Proof. exact (eq_refl (term124 _127196 x s g' t')). Qed.
Lemma lem6939075 {_127196 : Type'} (x : _127196) (s : _127196 -> Prop) (g' : Prop) (t' : nat) : term125 _127196 x s g' t'.
Proof. exact (EQ_MP (@lem6939074 _127196 x s g' t') (@lem6939073 _127196 x s g' t')). Qed.
Lemma lem6939076 {_127196 : Type'} (x : _127196) (s : _127196 -> Prop) (g' : Prop) (t' : nat) (e' : nat) : term126 _127196 x s g' t' e'.
Proof. exact (@lem6939075 _127196 x s g' t' e'). Qed.
Lemma lem6939077 {_127196 : Type'} (x : _127196) (s : _127196 -> Prop) (g' : Prop) (t' : nat) (e' : nat) : (term126 _127196 x s g' t' e') = (term127 _127196 x s g' t' e').
Proof. exact (eq_refl (term126 _127196 x s g' t' e')). Qed.
Lemma lem6939078 {_127196 : Type'} (x : _127196) (s : _127196 -> Prop) (g' : Prop) (t' : nat) (e' : nat) : term127 _127196 x s g' t' e'.
Proof. exact (EQ_MP (@lem6939077 _127196 x s g' t' e') (@lem6939076 _127196 x s g' t' e')). Qed.
Lemma lem6939080 {_127196 : Type'} (c : nat) (x : _127196) (s : _127196 -> Prop) (h1 : term39 _127196 c x s) : (@IN _127196 x s) = False.
Proof. exact (@lem6938977 _127196 x s (@lem6938976 _127196 c x s h1)). Qed.
Lemma lem6939081 {_127196 : Type'} (x : _127196) (s : _127196 -> Prop) (t' : nat) (e' : nat) : term128 _127196 x s t' e'.
Proof. exact (@lem6939078 _127196 x s False t' e'). Qed.
Lemma lem6939082 {_127196 : Type'} (t' : nat) (e' : nat) (c : nat) (x : _127196) (s : _127196 -> Prop) (h1 : term39 _127196 c x s) : term129 _127196 x s t' e'.
Proof. exact (@lem6939081 _127196 x s t' e' (@lem6939080 _127196 c x s h1)). Qed.
Lemma lem6939086 {_127196 : Type'} (s : _127196 -> Prop) : (@CARD _127196 s) = (@CARD _127196 s).
Proof. exact (eq_refl (@CARD _127196 s)). Qed.
Lemma lem6939087 {_127196 : Type'} (s : _127196 -> Prop) : term130 _127196 s.
Proof. exact (fun h0 : False => @lem6939086 _127196 s). Qed.
Lemma lem6939088 {_127196 : Type'} (e' : nat) (c : nat) (x : _127196) (s : _127196 -> Prop) (h1 : term39 _127196 c x s) : term131 _127196 x s e'.
Proof. exact (@lem6939082 _127196 (@CARD _127196 s) e' c x s h1). Qed.
Lemma lem6939089 {_127196 : Type'} (e' : nat) (c : nat) (x : _127196) (s : _127196 -> Prop) (h1 : term39 _127196 c x s) : term132 _127196 x s e'.
Proof. exact (@lem6939088 _127196 e' c x s h1 (@lem6939087 _127196 s)). Qed.
Lemma lem6939095 {_127196 : Type'} (s : _127196 -> Prop) : (term121 _127196 s) = (term121 _127196 s).
Proof. exact (eq_refl (term121 _127196 s)). Qed.
Lemma lem6939096 {_127196 : Type'} (s : _127196 -> Prop) : term133 _127196 s.
Proof. exact (fun h0 : ~ False => @lem6939095 _127196 s). Qed.
Lemma lem6939097 {_127196 : Type'} (c : nat) (x : _127196) (s : _127196 -> Prop) (h1 : term39 _127196 c x s) : term134 _127196 x s.
Proof. exact (@lem6939089 _127196 (term121 _127196 s) c x s h1). Qed.
Lemma lem6939098 {_127196 : Type'} (c : nat) (x : _127196) (s : _127196 -> Prop) (h1 : term39 _127196 c x s) : (term6 _127196 x s) = (term135 _127196 s).
Proof. exact (@lem6939097 _127196 c x s h1 (@lem6939096 _127196 s)). Qed.
Lemma lem6939100 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem6939101 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem6939100 nat t1 t2). Qed.
Lemma lem6939102 {_127196 : Type'} (s : _127196 -> Prop) : (term135 _127196 s) = (term121 _127196 s).
Proof. exact (@lem6939101 (@CARD _127196 s) (term121 _127196 s)). Qed.
Lemma lem6939103 {_127196 : Type'} (c : nat) (x : _127196) (s : _127196 -> Prop) (h1 : term39 _127196 c x s) : (term6 _127196 x s) = (term121 _127196 s).
Proof. exact (TRANS (@lem6939098 _127196 c x s h1) (@lem6939102 _127196 s)). Qed.
Lemma lem6939104 {_127196 : Type'} (c : nat) (x : _127196) (s : _127196 -> Prop) (h1 : term39 _127196 c x s) : (term5 _127196 x s) = (term121 _127196 s).
Proof. exact (TRANS (@lem6939062 _127196 c x s h1) (@lem6939103 _127196 c x s h1)). Qed.
Lemma lem6939105 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem6939106 {_127196 : Type'} (c : nat) (x : _127196) (s : _127196 -> Prop) (h1 : term39 _127196 c x s) : (term136 _127196 x s) = (term137 _127196 s).
Proof. exact (MK_COMB (@lem6939105) (@lem6939104 _127196 c x s h1)). Qed.
Lemma lem6939107 (c : nat) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem6939108 {_127196 : Type'} (c : nat) (x : _127196) (s : _127196 -> Prop) (h1 : term39 _127196 c x s) : (term44 _127196 x s c) = (term138 _127196 s c).
Proof. exact (MK_COMB (@lem6939106 _127196 c x s h1) (@lem6939107 c)). Qed.
Lemma lem6939109 {_127196 : Type'} (c : nat) (x : _127196) (s : _127196 -> Prop) (h1 : term39 _127196 c x s) : ((term43 _127196 x s c) = (term44 _127196 x s c)) = ((term114 _127196 s c) = (term138 _127196 s c)).
Proof. exact (MK_COMB (@lem6939054 _127196 c x s h1) (@lem6939108 _127196 c x s h1)). Qed.
Lemma lem6939112 {_127196 : Type'} (x : _127196) (s : _127196 -> Prop) (c : nat) : term139 _127196 x s c.
Proof. exact (fun h0 : term39 _127196 c x s => @lem6939109 _127196 c x s h0). Qed.
Lemma lem6939113 {_127196 : Type'} (x : _127196) (s : _127196 -> Prop) (c : nat) : term140 _127196 x s c.
Proof. exact (@lem6938970 _127196 c x s ((term114 _127196 s c) = (term138 _127196 s c))). Qed.
Lemma lem6939114 {_127196 : Type'} (x : _127196) (s : _127196 -> Prop) (c : nat) : (term46 _127196 x s c) = (term141 _127196 x s c).
Proof. exact (@lem6939113 _127196 x s c (@lem6939112 _127196 x s c)). Qed.
Lemma lem6939160 {_127196 : Type'} (x : _127196) (c : nat) : (term48 _127196 x c) = (term142 _127196 x c).
Proof. exact (fun_ext (fun s : _127196 -> Prop => @lem6939114 _127196 x s c)). Qed.
Lemma lem6939206 {_127196 : Type'} : (@all (_127196 -> Prop)) = (@all (_127196 -> Prop)).
Proof. exact (eq_refl (@all (_127196 -> Prop))). Qed.
Lemma lem6939207 {_127196 : Type'} (x : _127196) (c : nat) : (term50 _127196 x c) = (term143 _127196 x c).
Proof. exact (MK_COMB (@lem6939206 _127196) (@lem6939160 _127196 x c)). Qed.
Lemma lem6939257 {_127196 : Type'} (c : nat) : (term52 _127196 c) = (term144 _127196 c).
Proof. exact (fun_ext (fun x : _127196 => @lem6939207 _127196 x c)). Qed.
Lemma lem6939307 {_127196 : Type'} : (@all _127196) = (@all _127196).
Proof. exact (eq_refl (@all _127196)). Qed.
Lemma lem6939308 {_127196 : Type'} (c : nat) : (term54 _127196 c) = (term145 _127196 c).
Proof. exact (MK_COMB (@lem6939307 _127196) (@lem6939257 _127196 c)). Qed.
Lemma lem6939362 {_127196 : Type'} (c : nat) : (term56 _127196 c) = (term146 _127196 c).
Proof. exact (MK_COMB (@lem6938938 _127196 c) (@lem6939308 _127196 c)). Qed.
Lemma lem6939420 {_127196 : Type'} (c : nat) : (term146 _127196 c) = (term56 _127196 c).
Proof. exact (SYM (@lem6939362 _127196 c)). Qed.
Lemma lem6939449 (c : nat) : (term72 c) = (NUMERAL 0).
Proof. exact (@lem1032066 c). Qed.
Lemma lem6939452 : term69 = term69.
Proof. exact (eq_refl term69). Qed.
Lemma lem6939456 (c : nat) : ((NUMERAL 0) = (term72 c)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem6939452) (@lem6939449 c)). Qed.
Lemma lem6939458 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem6939459 : ((NUMERAL 0) = (NUMERAL 0)) = (term147 = term147).
Proof. exact (@lem6939458 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem6939462 (c : nat) : ((NUMERAL 0) = (term72 c)) = (term147 = term147).
Proof. exact (TRANS (@lem6939456 c) (@lem6939459)). Qed.
Lemma lem6939463 : term148 = (term147 = term147).
Proof. exact (@lem2318604 (term147 = term147)). Qed.
Lemma lem6939476 (y : int) (x : int) : (term149 x y) = (term150 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem6939477 : term151 = term152.
Proof. exact (@lem6939476 term147 term147). Qed.
Lemma lem6939479 (x : int) (y : int) : (int_le x y) = (term153 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6939480 : term154 = term155.
Proof. exact (@lem6939479 term156 term147). Qed.
Lemma lem6939482 (x : int) (y : int) : (term157 x y) = (term158 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6939483 : term159 = term160.
Proof. exact (@lem6939482 term147 term161). Qed.
Lemma lem6939485 (n : nat) : (term162 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6939486 : term163 = term164.
Proof. exact (@lem6939485 (NUMERAL 0)). Qed.
Lemma lem6939487 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6939488 : term165 = term166.
Proof. exact (MK_COMB (@lem6939487) (@lem6939486)). Qed.
Lemma lem6939490 (n : nat) : (term162 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6939491 : term167 = term168.
Proof. exact (@lem6939490 term169). Qed.
Lemma lem6939492 : term160 = term170.
Proof. exact (MK_COMB (@lem6939488) (@lem6939491)). Qed.
Lemma lem6939493 : term159 = term170.
Proof. exact (TRANS (@lem6939483) (@lem6939492)). Qed.
Lemma lem6939494 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6939495 : term171 = term172.
Proof. exact (MK_COMB (@lem6939494) (@lem6939493)). Qed.
Lemma lem6939497 (n : nat) : (term162 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6939498 : term163 = term164.
Proof. exact (@lem6939497 (NUMERAL 0)). Qed.
Lemma lem6939499 : term155 = term173.
Proof. exact (MK_COMB (@lem6939495) (@lem6939498)). Qed.
Lemma lem6939500 : term154 = term173.
Proof. exact (TRANS (@lem6939480) (@lem6939499)). Qed.
Lemma lem6939501 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6939502 : term174 = term175.
Proof. exact (MK_COMB (@lem6939501) (@lem6939500)). Qed.
Lemma lem6939504 (x : int) (y : int) : (int_le x y) = (term153 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6939505 : term154 = term155.
Proof. exact (@lem6939504 term156 term147). Qed.
Lemma lem6939507 (x : int) (y : int) : (term157 x y) = (term158 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6939508 : term159 = term160.
Proof. exact (@lem6939507 term147 term161). Qed.
Lemma lem6939510 (n : nat) : (term162 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6939511 : term163 = term164.
Proof. exact (@lem6939510 (NUMERAL 0)). Qed.
Lemma lem6939512 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6939513 : term165 = term166.
Proof. exact (MK_COMB (@lem6939512) (@lem6939511)). Qed.
Lemma lem6939515 (n : nat) : (term162 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6939516 : term167 = term168.
Proof. exact (@lem6939515 term169). Qed.
Lemma lem6939517 : term160 = term170.
Proof. exact (MK_COMB (@lem6939513) (@lem6939516)). Qed.
Lemma lem6939518 : term159 = term170.
Proof. exact (TRANS (@lem6939508) (@lem6939517)). Qed.
Lemma lem6939519 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6939520 : term171 = term172.
Proof. exact (MK_COMB (@lem6939519) (@lem6939518)). Qed.
Lemma lem6939522 (n : nat) : (term162 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6939523 : term163 = term164.
Proof. exact (@lem6939522 (NUMERAL 0)). Qed.
Lemma lem6939524 : term155 = term173.
Proof. exact (MK_COMB (@lem6939520) (@lem6939523)). Qed.
Lemma lem6939525 : term154 = term173.
Proof. exact (TRANS (@lem6939505) (@lem6939524)). Qed.
Lemma lem6939526 : term152 = term176.
Proof. exact (MK_COMB (@lem6939502) (@lem6939525)). Qed.
Lemma lem6939528 : term151 = term176.
Proof. exact (TRANS (@lem6939477) (@lem6939526)). Qed.
Lemma lem6939532 (t : Prop) : (term177 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem6939533 : term178 = term176.
Proof. exact (@lem6939532 term176). Qed.
Lemma lem6939535 (t : Prop) : (t \/ t) = t.
Proof. exact (proj2 (@lem16485 t)). Qed.
Lemma lem6939536 : term176 = term173.
Proof. exact (@lem6939535 term173). Qed.
Lemma lem6939542 : term178 = term173.
Proof. exact (TRANS (@lem6939533) (@lem6939536)). Qed.
Lemma lem6939543 : term173 = term179.
Proof. exact (@lem1988287 term164 term170). Qed.
Lemma lem6939550 : term170 = term168.
Proof. exact (@lem1982721 term168). Qed.
Lemma lem6939553 : term180 = term180.
Proof. exact (eq_refl term180). Qed.
Lemma lem6939554 : term181 = term182.
Proof. exact (MK_COMB (@lem6939553) (@lem6939550)). Qed.
Lemma lem6939555 : term182 = term183.
Proof. exact (@lem1982792 term164 term168). Qed.
Lemma lem6939557 (x : nat) : (real_of_num x) = (term184 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6939558 : term168 = term185.
Proof. exact (@lem6939557 term169). Qed.
Lemma lem6939560 (x : nat) : (term186 x) = (term187 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6939561 : term188 = term189.
Proof. exact (@lem6939560 term169). Qed.
Lemma lem6939562 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6939563 : term190 = term191.
Proof. exact (MK_COMB (@lem6939562) (@lem6939561)). Qed.
Lemma lem6939564 : term192 = term193.
Proof. exact (MK_COMB (@lem6939563) (@lem6939558)). Qed.
Lemma lem6939565 : term193 = term194.
Proof. exact (@lem1981613 term188 term168 term168 term168). Qed.
Lemma lem6939567 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6939568 : term197 = term198.
Proof. exact (@lem6939567 term169 term169). Qed.
Lemma lem6939569 : (term199 = (BIT1 0)) = (term200 = term169).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6939570 : term200 = term169.
Proof. exact (EQ_MP (@lem6939569) (@lem940073)). Qed.
Lemma lem6939571 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6939572 : term198 = term168.
Proof. exact (MK_COMB (@lem6939571) (@lem6939570)). Qed.
Lemma lem6939573 : term197 = term168.
Proof. exact (TRANS (@lem6939568) (@lem6939572)). Qed.
Lemma lem6939575 (m : nat) (n : nat) : (term201 m n) = (term202 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6939576 : term192 = term203.
Proof. exact (@lem6939575 term169 term169). Qed.
Lemma lem6939577 : (term199 = (BIT1 0)) = (term200 = term169).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6939578 : term200 = term169.
Proof. exact (EQ_MP (@lem6939577) (@lem940073)). Qed.
Lemma lem6939579 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6939580 : term198 = term168.
Proof. exact (MK_COMB (@lem6939579) (@lem6939578)). Qed.
Lemma lem6939581 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6939582 : term203 = term188.
Proof. exact (MK_COMB (@lem6939581) (@lem6939580)). Qed.
Lemma lem6939583 : term192 = term188.
Proof. exact (TRANS (@lem6939576) (@lem6939582)). Qed.
Lemma lem6939584 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6939585 : term204 = term205.
Proof. exact (MK_COMB (@lem6939584) (@lem6939583)). Qed.
Lemma lem6939586 : term194 = term189.
Proof. exact (MK_COMB (@lem6939585) (@lem6939573)). Qed.
Lemma lem6939587 : term193 = term189.
Proof. exact (TRANS (@lem6939565) (@lem6939586)). Qed.
Lemma lem6939588 : term192 = term189.
Proof. exact (TRANS (@lem6939564) (@lem6939587)). Qed.
Lemma lem6939590 (x : real) : (term206 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6939591 : term189 = term188.
Proof. exact (@lem6939590 term188). Qed.
Lemma lem6939592 : term192 = term188.
Proof. exact (TRANS (@lem6939588) (@lem6939591)). Qed.
Lemma lem6939593 : term166 = term166.
Proof. exact (eq_refl term166). Qed.
Lemma lem6939594 : term183 = term207.
Proof. exact (MK_COMB (@lem6939593) (@lem6939592)). Qed.
Lemma lem6939595 : term207 = term188.
Proof. exact (@lem1982721 term188). Qed.
Lemma lem6939596 : term183 = term188.
Proof. exact (TRANS (@lem6939594) (@lem6939595)). Qed.
Lemma lem6939597 : term182 = term188.
Proof. exact (TRANS (@lem6939555) (@lem6939596)). Qed.
Lemma lem6939598 : term181 = term188.
Proof. exact (TRANS (@lem6939554) (@lem6939597)). Qed.
Lemma lem6939599 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6939600 : term208 = term209.
Proof. exact (MK_COMB (@lem6939599) (@lem6939598)). Qed.
Lemma lem6939601 : term164 = term164.
Proof. exact (eq_refl term164). Qed.
Lemma lem6939602 : term179 = term210.
Proof. exact (MK_COMB (@lem6939600) (@lem6939601)). Qed.
Lemma lem6939603 : term173 = term210.
Proof. exact (TRANS (@lem6939543) (@lem6939602)). Qed.
Lemma lem6939612 : term178 = term210.
Proof. exact (TRANS (@lem6939542) (@lem6939603)). Qed.
Lemma lem6939616 (h1 : term210) : term210.
Proof. exact (h1). Qed.
Lemma lem6939618 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6939619 : term210 = term211.
Proof. exact (@lem6939618 term164 term188). Qed.
Lemma lem6939621 (x : nat) : (term186 x) = (term187 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6939622 : term188 = term189.
Proof. exact (@lem6939621 term169). Qed.
Lemma lem6939624 (x : nat) : (real_of_num x) = (term184 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6939625 : term164 = term212.
Proof. exact (@lem6939624 (NUMERAL 0)). Qed.
Lemma lem6939626 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6939627 : term213 = term214.
Proof. exact (MK_COMB (@lem6939626) (@lem6939625)). Qed.
Lemma lem6939628 : term211 = term215.
Proof. exact (MK_COMB (@lem6939627) (@lem6939622)). Qed.
Lemma lem6939629 : term216.
Proof. exact (@lem1980026 term164 term168 term188 term168). Qed.
Lemma lem6939631 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6939632 : term218 = term219.
Proof. exact (@lem6939631 (NUMERAL 0) term169). Qed.
Lemma lem6939633 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6939634 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6939635 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem6939634 h1) (fun h1 : term219 = True => @lem6939633)). Qed.
Lemma lem6939636 : term219 = True.
Proof. exact (EQ_MP (@lem6939635) (@lem6939633)). Qed.
Lemma lem6939637 : term218 = True.
Proof. exact (TRANS (@lem6939632) (@lem6939636)). Qed.
Lemma lem6939638 : True = term218.
Proof. exact (SYM (@lem6939637)). Qed.
Lemma lem6939639 : term218.
Proof. exact (EQ_MP (@lem6939638) (@lem0)). Qed.
Lemma lem6939640 : term221.
Proof. exact (@lem6939629 (@lem6939639)). Qed.
Lemma lem6939642 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6939643 : term218 = term219.
Proof. exact (@lem6939642 (NUMERAL 0) term169). Qed.
Lemma lem6939644 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6939645 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6939646 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem6939645 h1) (fun h1 : term219 = True => @lem6939644)). Qed.
Lemma lem6939647 : term219 = True.
Proof. exact (EQ_MP (@lem6939646) (@lem6939644)). Qed.
Lemma lem6939648 : term218 = True.
Proof. exact (TRANS (@lem6939643) (@lem6939647)). Qed.
Lemma lem6939649 : True = term218.
Proof. exact (SYM (@lem6939648)). Qed.
Lemma lem6939650 : term218.
Proof. exact (EQ_MP (@lem6939649) (@lem0)). Qed.
Lemma lem6939651 : term215 = term222.
Proof. exact (@lem6939640 (@lem6939650)). Qed.
Lemma lem6939653 (m : nat) (n : nat) : (term201 m n) = (term202 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6939654 : term192 = term203.
Proof. exact (@lem6939653 term169 term169). Qed.
Lemma lem6939655 : (term199 = (BIT1 0)) = (term200 = term169).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6939656 : term200 = term169.
Proof. exact (EQ_MP (@lem6939655) (@lem940073)). Qed.
Lemma lem6939657 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6939658 : term198 = term168.
Proof. exact (MK_COMB (@lem6939657) (@lem6939656)). Qed.
Lemma lem6939659 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6939660 : term203 = term188.
Proof. exact (MK_COMB (@lem6939659) (@lem6939658)). Qed.
Lemma lem6939661 : term192 = term188.
Proof. exact (TRANS (@lem6939654) (@lem6939660)). Qed.
Lemma lem6939663 (x : nat) : (term223 x) = term164.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6939664 : term224 = term164.
Proof. exact (@lem6939663 term169). Qed.
Lemma lem6939665 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6939666 : term225 = term213.
Proof. exact (MK_COMB (@lem6939665) (@lem6939664)). Qed.
Lemma lem6939667 : term222 = term211.
Proof. exact (MK_COMB (@lem6939666) (@lem6939661)). Qed.
Lemma lem6939669 (m : nat) (n : nat) : (term226 m n) = (term227 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6939670 : term211 = term228.
Proof. exact (@lem6939669 (NUMERAL 0) term169). Qed.
Lemma lem6939671 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6939672 (h1 : term220 = (BIT1 0)) : (term169 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6939673 : (term220 = (BIT1 0)) = ((term169 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem6939672 h1) (fun h1 : (term169 = (NUMERAL 0)) = False => @lem6939671)). Qed.
Lemma lem6939674 : (term169 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6939673) (@lem6939671)). Qed.
Lemma lem6939675 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6939676 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6939677 : term229 = (and True).
Proof. exact (MK_COMB (@lem6939676) (@lem6939675)). Qed.
Lemma lem6939678 : term228 = (True /\ False).
Proof. exact (MK_COMB (@lem6939677) (@lem6939674)). Qed.
Lemma lem6939680 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6939681 : term228 = False.
Proof. exact (TRANS (@lem6939678) (@lem6939680)). Qed.
Lemma lem6939682 : term211 = False.
Proof. exact (TRANS (@lem6939670) (@lem6939681)). Qed.
Lemma lem6939683 : term222 = False.
Proof. exact (TRANS (@lem6939667) (@lem6939682)). Qed.
Lemma lem6939684 : term215 = False.
Proof. exact (TRANS (@lem6939651) (@lem6939683)). Qed.
Lemma lem6939685 : term211 = False.
Proof. exact (TRANS (@lem6939628) (@lem6939684)). Qed.
Lemma lem6939686 : term210 = False.
Proof. exact (TRANS (@lem6939619) (@lem6939685)). Qed.
Lemma lem6939687 (h1 : term210) : False.
Proof. exact (EQ_MP (@lem6939686) (@lem6939616 h1)). Qed.
Lemma lem6939689 (h1 : term210) : term210.
Proof. exact (h1). Qed.
Lemma lem6939690 (h1 : term210) : term210 = False.
Proof. exact (prop_ext (fun h2 : term210 => @lem6939687 h1) (fun h2 : False => @lem6939689 h1)). Qed.
Lemma lem6939691 (h1 : term210) : False.
Proof. exact (EQ_MP (@lem6939690 h1) (@lem6939689 h1)). Qed.
Lemma lem6939692 (h1 : term178) : term178.
Proof. exact (h1). Qed.
Lemma lem6939693 (h1 : term178) : term210.
Proof. exact (EQ_MP (@lem6939612) (@lem6939692 h1)). Qed.
Lemma lem6939694 (h1 : term178) : term210 = False.
Proof. exact (prop_ext (fun h2 : term210 => @lem6939691 h2) (fun h2 : False => @lem6939693 h1)). Qed.
Lemma lem6939695 (h1 : term178) : False.
Proof. exact (EQ_MP (@lem6939694 h1) (@lem6939693 h1)). Qed.
Lemma lem6939696 : term230.
Proof. exact (fun h0 : term178 => @lem6939695 h0). Qed.
Lemma lem6939697 : term231.
Proof. exact (@lem1386578 term232). Qed.
Lemma lem6939700 : term232.
Proof. exact (@lem6939697 (@lem6939696)). Qed.
Lemma lem6939701 : term176 = term151.
Proof. exact (SYM (@lem6939528)). Qed.
Lemma lem6939702 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6939703 : term232 = term148.
Proof. exact (MK_COMB (@lem6939702) (@lem6939701)). Qed.
Lemma lem6939704 : term148.
Proof. exact (EQ_MP (@lem6939703) (@lem6939700)). Qed.
Lemma lem6939705 : term147 = term147.
Proof. exact (EQ_MP (@lem6939463) (@lem6939704)). Qed.
Lemma lem6939706 (c : nat) : (term147 = term147) = ((NUMERAL 0) = (term72 c)).
Proof. exact (SYM (@lem6939462 c)). Qed.
Lemma lem6939707 (c : nat) : (NUMERAL 0) = (term72 c).
Proof. exact (EQ_MP (@lem6939706 c) (@lem6939705)). Qed.
Lemma lem6939708 (c : nat) : ((NUMERAL 0) = (term72 c)) = (((NUMERAL 0) = (term72 c)) = True).
Proof. exact (@lem7 ((NUMERAL 0) = (term72 c))). Qed.
Lemma lem6939709 (c : nat) : ((NUMERAL 0) = (term72 c)) = True.
Proof. exact (EQ_MP (@lem6939708 c) (@lem6939707 c)). Qed.
Lemma lem6939710 (c : nat) : True = ((NUMERAL 0) = (term72 c)).
Proof. exact (SYM (@lem6939709 c)). Qed.
Lemma lem6939711 (c : nat) : (NUMERAL 0) = (term72 c).
Proof. exact (EQ_MP (@lem6939710 c) (@lem0)). Qed.
Lemma lem6939728 (m : nat) : (S m) = (term233 m).
Proof. exact (EQ_MP (@lem2841417 m) (@lem2841416 m)). Qed.
Lemma lem6939729 {_127196 : Type'} (s : _127196 -> Prop) : (term121 _127196 s) = (term234 _127196 s).
Proof. exact (@lem6939728 (@CARD _127196 s)). Qed.
Lemma lem6939730 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem6939731 {_127196 : Type'} (s : _127196 -> Prop) : (term137 _127196 s) = (term235 _127196 s).
Proof. exact (MK_COMB (@lem6939730) (@lem6939729 _127196 s)). Qed.
Lemma lem6939732 (c : nat) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem6939733 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : (term138 _127196 s c) = (term236 _127196 s c).
Proof. exact (MK_COMB (@lem6939731 _127196 s) (@lem6939732 c)). Qed.
Lemma lem6939734 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : (term119 _127196 s c) = (term119 _127196 s c).
Proof. exact (eq_refl (term119 _127196 s c)). Qed.
Lemma lem6939736 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : ((term114 _127196 s c) = (term138 _127196 s c)) = ((term114 _127196 s c) = (term236 _127196 s c)).
Proof. exact (MK_COMB (@lem6939734 _127196 s c) (@lem6939733 _127196 s c)). Qed.
Lemma lem6939748 {_127196 : Type'} (c : nat) (s : _127196 -> Prop) : (term236 _127196 s c) = (term237 _127196 c s).
Proof. exact (@lem1032062 c (term234 _127196 s)). Qed.
Lemma lem6939749 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : (term237 _127196 c s) = (term238 _127196 s c).
Proof. exact (@lem1032118 (@CARD _127196 s) c term169). Qed.
Lemma lem6939750 (c : nat) : (term239 c) = (term240 c).
Proof. exact (@lem1032084 term169 c). Qed.
Lemma lem6939751 (c : nat) : (term240 c) = c.
Proof. exact (@lem1032046 c). Qed.
Lemma lem6939752 (c : nat) : (term239 c) = c.
Proof. exact (TRANS (@lem6939750 c) (@lem6939751 c)). Qed.
Lemma lem6939755 {_127196 : Type'} (c : nat) (s : _127196 -> Prop) : (term241 _127196 c s) = (term241 _127196 c s).
Proof. exact (eq_refl (term241 _127196 c s)). Qed.
Lemma lem6939756 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : (term238 _127196 s c) = (term242 _127196 s c).
Proof. exact (MK_COMB (@lem6939755 _127196 c s) (@lem6939752 c)). Qed.
Lemma lem6939757 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : (term237 _127196 c s) = (term242 _127196 s c).
Proof. exact (TRANS (@lem6939749 _127196 s c) (@lem6939756 _127196 s c)). Qed.
Lemma lem6939759 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : (term236 _127196 s c) = (term242 _127196 s c).
Proof. exact (TRANS (@lem6939748 _127196 c s) (@lem6939757 _127196 s c)). Qed.
Lemma lem6939766 {_127196 : Type'} (c : nat) (s : _127196 -> Prop) : (term34 _127196 s c) = (term243 _127196 c s).
Proof. exact (@lem1032084 c (@CARD _127196 s)). Qed.
Lemma lem6939769 (c : nat) : (Nat.add c) = (Nat.add c).
Proof. exact (eq_refl (Nat.add c)). Qed.
Lemma lem6939770 {_127196 : Type'} (c : nat) (s : _127196 -> Prop) : (term114 _127196 s c) = (term244 _127196 c s).
Proof. exact (MK_COMB (@lem6939769 c) (@lem6939766 _127196 c s)). Qed.
Lemma lem6939771 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : (term244 _127196 c s) = (term242 _127196 s c).
Proof. exact (@lem1032098 (term243 _127196 c s) c). Qed.
Lemma lem6939772 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : (term114 _127196 s c) = (term242 _127196 s c).
Proof. exact (TRANS (@lem6939770 _127196 c s) (@lem6939771 _127196 s c)). Qed.
Lemma lem6939773 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6939774 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : (term119 _127196 s c) = (term245 _127196 s c).
Proof. exact (MK_COMB (@lem6939773) (@lem6939772 _127196 s c)). Qed.
Lemma lem6939775 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : ((term114 _127196 s c) = (term236 _127196 s c)) = ((term242 _127196 s c) = (term242 _127196 s c)).
Proof. exact (MK_COMB (@lem6939774 _127196 s c) (@lem6939759 _127196 s c)). Qed.
Lemma lem6939778 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : ((term114 _127196 s c) = (term138 _127196 s c)) = ((term242 _127196 s c) = (term242 _127196 s c)).
Proof. exact (TRANS (@lem6939736 _127196 s c) (@lem6939775 _127196 s c)). Qed.
Lemma lem6939780 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem6939781 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : ((term242 _127196 s c) = (term242 _127196 s c)) = ((term246 _127196 s c) = (term246 _127196 s c)).
Proof. exact (@lem6939780 (term242 _127196 s c) (term242 _127196 s c)). Qed.
Lemma lem6939785 (m : nat) (n : nat) : (term247 m n) = (term248 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem6939786 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : (term246 _127196 s c) = (term249 _127196 s c).
Proof. exact (@lem6939785 (term243 _127196 c s) c). Qed.
Lemma lem6939787 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem6939788 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : (term250 _127196 s c) = (term251 _127196 s c).
Proof. exact (MK_COMB (@lem6939787) (@lem6939786 _127196 s c)). Qed.
Lemma lem6939790 (m : nat) (n : nat) : (term247 m n) = (term248 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem6939791 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : (term246 _127196 s c) = (term249 _127196 s c).
Proof. exact (@lem6939790 (term243 _127196 c s) c). Qed.
Lemma lem6939792 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : ((term246 _127196 s c) = (term246 _127196 s c)) = ((term249 _127196 s c) = (term249 _127196 s c)).
Proof. exact (MK_COMB (@lem6939788 _127196 s c) (@lem6939791 _127196 s c)). Qed.
Lemma lem6939793 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : ((term242 _127196 s c) = (term242 _127196 s c)) = ((term249 _127196 s c) = (term249 _127196 s c)).
Proof. exact (TRANS (@lem6939781 _127196 s c) (@lem6939792 _127196 s c)). Qed.
Lemma lem6939794 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : ((term114 _127196 s c) = (term138 _127196 s c)) = ((term249 _127196 s c) = (term249 _127196 s c)).
Proof. exact (TRANS (@lem6939778 _127196 s c) (@lem6939793 _127196 s c)). Qed.
Lemma lem6939795 (c : nat) : term252 c.
Proof. exact (@lem2307535 c). Qed.
Lemma lem6939796 (c : nat) : (term252 c) = (term253 c).
Proof. exact (eq_refl (term252 c)). Qed.
Lemma lem6939797 (c : nat) : term253 c.
Proof. exact (EQ_MP (@lem6939796 c) (@lem6939795 c)). Qed.
Lemma lem6939798 {_127196 : Type'} (c : nat) (s : _127196 -> Prop) : term254 _127196 c s.
Proof. exact (@lem2307535 (term243 _127196 c s)). Qed.
Lemma lem6939799 {_127196 : Type'} (c : nat) (s : _127196 -> Prop) : (term254 _127196 c s) = (term255 _127196 c s).
Proof. exact (eq_refl (term254 _127196 c s)). Qed.
Lemma lem6939800 {_127196 : Type'} (c : nat) (s : _127196 -> Prop) : term255 _127196 c s.
Proof. exact (EQ_MP (@lem6939799 _127196 c s) (@lem6939798 _127196 c s)). Qed.
Lemma lem6939801 (_92528 : int) (_92527 : int) : (term256 _92528 _92527) = (term257 _92528 _92527).
Proof. exact (@lem2318604 (term257 _92528 _92527)). Qed.
Lemma lem6939818 (_92528 : int) (_92527 : int) : (term258 _92528 _92527) = (term259 _92528 _92527).
Proof. exact (@lem17362 (term260 _92528) ((int_add _92528 _92527) = (int_add _92528 _92527))). Qed.
Lemma lem6939820 (_92527 : int) : (term261 _92527) = (term261 _92527).
Proof. exact (eq_refl (term261 _92527)). Qed.
Lemma lem6939821 (_92528 : int) (_92527 : int) : (term262 _92528 _92527) = (term263 _92528 _92527).
Proof. exact (MK_COMB (@lem6939820 _92527) (@lem6939818 _92528 _92527)). Qed.
Lemma lem6939822 (_92528 : int) (_92527 : int) : (term264 _92528 _92527) = (term262 _92528 _92527).
Proof. exact (@lem17362 (term260 _92527) (term265 _92528 _92527)). Qed.
Lemma lem6939836 (_92528 : int) (_92527 : int) : (term264 _92528 _92527) = (term263 _92528 _92527).
Proof. exact (TRANS (@lem6939822 _92528 _92527) (@lem6939821 _92528 _92527)). Qed.
Lemma lem6939839 (x : int) (y : int) : (int_le x y) = (term153 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6939840 (_92527 : int) : (term260 _92527) = (term266 _92527).
Proof. exact (@lem6939839 term147 _92527). Qed.
Lemma lem6939842 (n : nat) : (term162 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6939843 : term163 = term164.
Proof. exact (@lem6939842 (NUMERAL 0)). Qed.
Lemma lem6939844 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6939845 : term267 = term213.
Proof. exact (MK_COMB (@lem6939844) (@lem6939843)). Qed.
Lemma lem6939846 (_92527 : int) : (real_of_int _92527) = (real_of_int _92527).
Proof. exact (eq_refl (real_of_int _92527)). Qed.
Lemma lem6939847 (_92527 : int) : (term266 _92527) = (term268 _92527).
Proof. exact (MK_COMB (@lem6939845) (@lem6939846 _92527)). Qed.
Lemma lem6939849 (_92527 : int) : (term260 _92527) = (term268 _92527).
Proof. exact (TRANS (@lem6939840 _92527) (@lem6939847 _92527)). Qed.
Lemma lem6939852 (x : int) (y : int) : (int_le x y) = (term153 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6939853 (_92528 : int) : (term260 _92528) = (term266 _92528).
Proof. exact (@lem6939852 term147 _92528). Qed.
Lemma lem6939855 (n : nat) : (term162 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6939856 : term163 = term164.
Proof. exact (@lem6939855 (NUMERAL 0)). Qed.
Lemma lem6939857 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6939858 : term267 = term213.
Proof. exact (MK_COMB (@lem6939857) (@lem6939856)). Qed.
Lemma lem6939859 (_92528 : int) : (real_of_int _92528) = (real_of_int _92528).
Proof. exact (eq_refl (real_of_int _92528)). Qed.
Lemma lem6939860 (_92528 : int) : (term266 _92528) = (term268 _92528).
Proof. exact (MK_COMB (@lem6939858) (@lem6939859 _92528)). Qed.
Lemma lem6939862 (_92528 : int) : (term260 _92528) = (term268 _92528).
Proof. exact (TRANS (@lem6939853 _92528) (@lem6939860 _92528)). Qed.
Lemma lem6939864 (y : int) (x : int) : (term149 x y) = (term150 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem6939865 (_92528 : int) (_92527 : int) : (term269 _92528 _92527) = (term270 _92528 _92527).
Proof. exact (@lem6939864 (int_add _92528 _92527) (int_add _92528 _92527)). Qed.
Lemma lem6939867 (x : int) (y : int) : (int_le x y) = (term153 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6939868 (_92528 : int) (_92527 : int) : (term271 _92528 _92527) = (term272 _92528 _92527).
Proof. exact (@lem6939867 (term273 _92528 _92527) (int_add _92528 _92527)). Qed.
Lemma lem6939870 (x : int) (y : int) : (term157 x y) = (term158 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6939871 (_92528 : int) (_92527 : int) : (term274 _92528 _92527) = (term275 _92528 _92527).
Proof. exact (@lem6939870 (int_add _92528 _92527) term161). Qed.
Lemma lem6939873 (x : int) (y : int) : (term157 x y) = (term158 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6939874 (_92528 : int) (_92527 : int) : (term157 _92528 _92527) = (term158 _92528 _92527).
Proof. exact (@lem6939873 _92528 _92527). Qed.
Lemma lem6939875 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6939876 (_92528 : int) (_92527 : int) : (term276 _92528 _92527) = (term277 _92528 _92527).
Proof. exact (MK_COMB (@lem6939875) (@lem6939874 _92528 _92527)). Qed.
Lemma lem6939878 (n : nat) : (term162 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6939879 : term167 = term168.
Proof. exact (@lem6939878 term169). Qed.
Lemma lem6939880 (_92528 : int) (_92527 : int) : (term275 _92528 _92527) = (term278 _92528 _92527).
Proof. exact (MK_COMB (@lem6939876 _92528 _92527) (@lem6939879)). Qed.
Lemma lem6939881 (_92528 : int) (_92527 : int) : (term274 _92528 _92527) = (term278 _92528 _92527).
Proof. exact (TRANS (@lem6939871 _92528 _92527) (@lem6939880 _92528 _92527)). Qed.
Lemma lem6939882 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6939883 (_92528 : int) (_92527 : int) : (term279 _92528 _92527) = (term280 _92528 _92527).
Proof. exact (MK_COMB (@lem6939882) (@lem6939881 _92528 _92527)). Qed.
Lemma lem6939885 (x : int) (y : int) : (term157 x y) = (term158 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6939886 (_92528 : int) (_92527 : int) : (term157 _92528 _92527) = (term158 _92528 _92527).
Proof. exact (@lem6939885 _92528 _92527). Qed.
Lemma lem6939887 (_92528 : int) (_92527 : int) : (term272 _92528 _92527) = (term281 _92528 _92527).
Proof. exact (MK_COMB (@lem6939883 _92528 _92527) (@lem6939886 _92528 _92527)). Qed.
Lemma lem6939888 (_92528 : int) (_92527 : int) : (term271 _92528 _92527) = (term281 _92528 _92527).
Proof. exact (TRANS (@lem6939868 _92528 _92527) (@lem6939887 _92528 _92527)). Qed.
Lemma lem6939889 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6939890 (_92528 : int) (_92527 : int) : (term282 _92528 _92527) = (term283 _92528 _92527).
Proof. exact (MK_COMB (@lem6939889) (@lem6939888 _92528 _92527)). Qed.
Lemma lem6939892 (x : int) (y : int) : (int_le x y) = (term153 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6939893 (_92528 : int) (_92527 : int) : (term271 _92528 _92527) = (term272 _92528 _92527).
Proof. exact (@lem6939892 (term273 _92528 _92527) (int_add _92528 _92527)). Qed.
Lemma lem6939895 (x : int) (y : int) : (term157 x y) = (term158 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6939896 (_92528 : int) (_92527 : int) : (term274 _92528 _92527) = (term275 _92528 _92527).
Proof. exact (@lem6939895 (int_add _92528 _92527) term161). Qed.
Lemma lem6939898 (x : int) (y : int) : (term157 x y) = (term158 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6939899 (_92528 : int) (_92527 : int) : (term157 _92528 _92527) = (term158 _92528 _92527).
Proof. exact (@lem6939898 _92528 _92527). Qed.
Lemma lem6939900 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6939901 (_92528 : int) (_92527 : int) : (term276 _92528 _92527) = (term277 _92528 _92527).
Proof. exact (MK_COMB (@lem6939900) (@lem6939899 _92528 _92527)). Qed.
Lemma lem6939903 (n : nat) : (term162 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6939904 : term167 = term168.
Proof. exact (@lem6939903 term169). Qed.
Lemma lem6939905 (_92528 : int) (_92527 : int) : (term275 _92528 _92527) = (term278 _92528 _92527).
Proof. exact (MK_COMB (@lem6939901 _92528 _92527) (@lem6939904)). Qed.
Lemma lem6939906 (_92528 : int) (_92527 : int) : (term274 _92528 _92527) = (term278 _92528 _92527).
Proof. exact (TRANS (@lem6939896 _92528 _92527) (@lem6939905 _92528 _92527)). Qed.
Lemma lem6939907 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6939908 (_92528 : int) (_92527 : int) : (term279 _92528 _92527) = (term280 _92528 _92527).
Proof. exact (MK_COMB (@lem6939907) (@lem6939906 _92528 _92527)). Qed.
Lemma lem6939910 (x : int) (y : int) : (term157 x y) = (term158 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6939911 (_92528 : int) (_92527 : int) : (term157 _92528 _92527) = (term158 _92528 _92527).
Proof. exact (@lem6939910 _92528 _92527). Qed.
Lemma lem6939912 (_92528 : int) (_92527 : int) : (term272 _92528 _92527) = (term281 _92528 _92527).
Proof. exact (MK_COMB (@lem6939908 _92528 _92527) (@lem6939911 _92528 _92527)). Qed.
Lemma lem6939913 (_92528 : int) (_92527 : int) : (term271 _92528 _92527) = (term281 _92528 _92527).
Proof. exact (TRANS (@lem6939893 _92528 _92527) (@lem6939912 _92528 _92527)). Qed.
Lemma lem6939914 (_92528 : int) (_92527 : int) : (term270 _92528 _92527) = (term284 _92528 _92527).
Proof. exact (MK_COMB (@lem6939890 _92528 _92527) (@lem6939913 _92528 _92527)). Qed.
Lemma lem6939915 (_92528 : int) (_92527 : int) : (term269 _92528 _92527) = (term284 _92528 _92527).
Proof. exact (TRANS (@lem6939865 _92528 _92527) (@lem6939914 _92528 _92527)). Qed.
Lemma lem6939916 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6939917 (_92528 : int) : (term261 _92528) = (term285 _92528).
Proof. exact (MK_COMB (@lem6939916) (@lem6939862 _92528)). Qed.
Lemma lem6939918 (_92528 : int) (_92527 : int) : (term259 _92528 _92527) = (term286 _92528 _92527).
Proof. exact (MK_COMB (@lem6939917 _92528) (@lem6939915 _92528 _92527)). Qed.
Lemma lem6939919 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6939920 (_92527 : int) : (term261 _92527) = (term285 _92527).
Proof. exact (MK_COMB (@lem6939919) (@lem6939849 _92527)). Qed.
Lemma lem6939921 (_92528 : int) (_92527 : int) : (term263 _92528 _92527) = (term287 _92528 _92527).
Proof. exact (MK_COMB (@lem6939920 _92527) (@lem6939918 _92528 _92527)). Qed.
Lemma lem6939922 (_92528 : int) (_92527 : int) : (term264 _92528 _92527) = (term287 _92528 _92527).
Proof. exact (TRANS (@lem6939836 _92528 _92527) (@lem6939921 _92528 _92527)). Qed.
Lemma lem6939926 (t : Prop) : (term177 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem6939927 (_92528 : int) (_92527 : int) : (term288 _92528 _92527) = (term287 _92528 _92527).
Proof. exact (@lem6939926 (term287 _92528 _92527)). Qed.
Lemma lem6939933 (t : Prop) : (t \/ t) = t.
Proof. exact (proj2 (@lem16485 t)). Qed.
Lemma lem6939934 (_92528 : int) (_92527 : int) : (term284 _92528 _92527) = (term281 _92528 _92527).
Proof. exact (@lem6939933 (term281 _92528 _92527)). Qed.
Lemma lem6939935 (_92528 : int) : (term285 _92528) = (term285 _92528).
Proof. exact (eq_refl (term285 _92528)). Qed.
Lemma lem6939936 (_92528 : int) (_92527 : int) : (term286 _92528 _92527) = (term289 _92528 _92527).
Proof. exact (MK_COMB (@lem6939935 _92528) (@lem6939934 _92528 _92527)). Qed.
Lemma lem6939939 (_92527 : int) : (term285 _92527) = (term285 _92527).
Proof. exact (eq_refl (term285 _92527)). Qed.
Lemma lem6939940 (_92528 : int) (_92527 : int) : (term287 _92528 _92527) = (term290 _92528 _92527).
Proof. exact (MK_COMB (@lem6939939 _92527) (@lem6939936 _92528 _92527)). Qed.
Lemma lem6939964 (_92528 : int) (_92527 : int) : (term288 _92528 _92527) = (term290 _92528 _92527).
Proof. exact (TRANS (@lem6939927 _92528 _92527) (@lem6939940 _92528 _92527)). Qed.
Lemma lem6939965 (_92527 : int) : (term268 _92527) = (term291 _92527).
Proof. exact (@lem1988287 (real_of_int _92527) term164). Qed.
Lemma lem6939971 (_92527 : int) : (term292 _92527) = (term293 _92527).
Proof. exact (@lem1982792 (real_of_int _92527) term164). Qed.
Lemma lem6939973 (x : nat) : (real_of_num x) = (term184 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6939974 : term164 = term212.
Proof. exact (@lem6939973 (NUMERAL 0)). Qed.
Lemma lem6939976 (x : nat) : (term186 x) = (term187 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6939977 : term188 = term189.
Proof. exact (@lem6939976 term169). Qed.
Lemma lem6939978 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6939979 : term190 = term191.
Proof. exact (MK_COMB (@lem6939978) (@lem6939977)). Qed.
Lemma lem6939980 : term294 = term295.
Proof. exact (MK_COMB (@lem6939979) (@lem6939974)). Qed.
Lemma lem6939981 : term295 = term296.
Proof. exact (@lem1981613 term188 term164 term168 term168). Qed.
Lemma lem6939983 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6939984 : term197 = term198.
Proof. exact (@lem6939983 term169 term169). Qed.
Lemma lem6939985 : (term199 = (BIT1 0)) = (term200 = term169).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6939986 : term200 = term169.
Proof. exact (EQ_MP (@lem6939985) (@lem940073)). Qed.
Lemma lem6939987 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6939988 : term198 = term168.
Proof. exact (MK_COMB (@lem6939987) (@lem6939986)). Qed.
Lemma lem6939989 : term197 = term168.
Proof. exact (TRANS (@lem6939984) (@lem6939988)). Qed.
Lemma lem6939991 (x : nat) : (term297 x) = term164.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem6939992 : term294 = term164.
Proof. exact (@lem6939991 term169). Qed.
Lemma lem6939993 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6939994 : term298 = term299.
Proof. exact (MK_COMB (@lem6939993) (@lem6939992)). Qed.
Lemma lem6939995 : term296 = term212.
Proof. exact (MK_COMB (@lem6939994) (@lem6939989)). Qed.
Lemma lem6939996 : term295 = term212.
Proof. exact (TRANS (@lem6939981) (@lem6939995)). Qed.
Lemma lem6939997 : term294 = term212.
Proof. exact (TRANS (@lem6939980) (@lem6939996)). Qed.
Lemma lem6939999 (x : real) : (term206 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6940000 : term212 = term164.
Proof. exact (@lem6939999 term164). Qed.
Lemma lem6940001 : term294 = term164.
Proof. exact (TRANS (@lem6939997) (@lem6940000)). Qed.
Lemma lem6940002 (_92527 : int) : (term300 _92527) = (term300 _92527).
Proof. exact (eq_refl (term300 _92527)). Qed.
Lemma lem6940003 (_92527 : int) : (term293 _92527) = (term301 _92527).
Proof. exact (MK_COMB (@lem6940002 _92527) (@lem6940001)). Qed.
Lemma lem6940004 (_92527 : int) : (term301 _92527) = (real_of_int _92527).
Proof. exact (@lem1982723 (real_of_int _92527)). Qed.
Lemma lem6940005 (_92527 : int) : (term293 _92527) = (real_of_int _92527).
Proof. exact (TRANS (@lem6940003 _92527) (@lem6940004 _92527)). Qed.
Lemma lem6940007 (_92527 : int) : (term292 _92527) = (real_of_int _92527).
Proof. exact (TRANS (@lem6939971 _92527) (@lem6940005 _92527)). Qed.
Lemma lem6940008 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6940009 (_92527 : int) : (term302 _92527) = (term303 _92527).
Proof. exact (MK_COMB (@lem6940008) (@lem6940007 _92527)). Qed.
Lemma lem6940010 : term164 = term164.
Proof. exact (eq_refl term164). Qed.
Lemma lem6940011 (_92527 : int) : (term291 _92527) = (term304 _92527).
Proof. exact (MK_COMB (@lem6940009 _92527) (@lem6940010)). Qed.
Lemma lem6940012 (_92527 : int) : (term268 _92527) = (term304 _92527).
Proof. exact (TRANS (@lem6939965 _92527) (@lem6940011 _92527)). Qed.
Lemma lem6940013 (_92528 : int) : (term268 _92528) = (term291 _92528).
Proof. exact (@lem1988287 (real_of_int _92528) term164). Qed.
Lemma lem6940019 (_92528 : int) : (term292 _92528) = (term293 _92528).
Proof. exact (@lem1982792 (real_of_int _92528) term164). Qed.
Lemma lem6940021 (x : nat) : (real_of_num x) = (term184 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6940022 : term164 = term212.
Proof. exact (@lem6940021 (NUMERAL 0)). Qed.
Lemma lem6940024 (x : nat) : (term186 x) = (term187 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6940025 : term188 = term189.
Proof. exact (@lem6940024 term169). Qed.
Lemma lem6940026 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6940027 : term190 = term191.
Proof. exact (MK_COMB (@lem6940026) (@lem6940025)). Qed.
Lemma lem6940028 : term294 = term295.
Proof. exact (MK_COMB (@lem6940027) (@lem6940022)). Qed.
Lemma lem6940029 : term295 = term296.
Proof. exact (@lem1981613 term188 term164 term168 term168). Qed.
Lemma lem6940031 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6940032 : term197 = term198.
Proof. exact (@lem6940031 term169 term169). Qed.
Lemma lem6940033 : (term199 = (BIT1 0)) = (term200 = term169).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6940034 : term200 = term169.
Proof. exact (EQ_MP (@lem6940033) (@lem940073)). Qed.
Lemma lem6940035 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6940036 : term198 = term168.
Proof. exact (MK_COMB (@lem6940035) (@lem6940034)). Qed.
Lemma lem6940037 : term197 = term168.
Proof. exact (TRANS (@lem6940032) (@lem6940036)). Qed.
Lemma lem6940039 (x : nat) : (term297 x) = term164.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem6940040 : term294 = term164.
Proof. exact (@lem6940039 term169). Qed.
Lemma lem6940041 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6940042 : term298 = term299.
Proof. exact (MK_COMB (@lem6940041) (@lem6940040)). Qed.
Lemma lem6940043 : term296 = term212.
Proof. exact (MK_COMB (@lem6940042) (@lem6940037)). Qed.
Lemma lem6940044 : term295 = term212.
Proof. exact (TRANS (@lem6940029) (@lem6940043)). Qed.
Lemma lem6940045 : term294 = term212.
Proof. exact (TRANS (@lem6940028) (@lem6940044)). Qed.
Lemma lem6940047 (x : real) : (term206 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6940048 : term212 = term164.
Proof. exact (@lem6940047 term164). Qed.
Lemma lem6940049 : term294 = term164.
Proof. exact (TRANS (@lem6940045) (@lem6940048)). Qed.
Lemma lem6940050 (_92528 : int) : (term300 _92528) = (term300 _92528).
Proof. exact (eq_refl (term300 _92528)). Qed.
Lemma lem6940051 (_92528 : int) : (term293 _92528) = (term301 _92528).
Proof. exact (MK_COMB (@lem6940050 _92528) (@lem6940049)). Qed.
Lemma lem6940052 (_92528 : int) : (term301 _92528) = (real_of_int _92528).
Proof. exact (@lem1982723 (real_of_int _92528)). Qed.
Lemma lem6940053 (_92528 : int) : (term293 _92528) = (real_of_int _92528).
Proof. exact (TRANS (@lem6940051 _92528) (@lem6940052 _92528)). Qed.
Lemma lem6940055 (_92528 : int) : (term292 _92528) = (real_of_int _92528).
Proof. exact (TRANS (@lem6940019 _92528) (@lem6940053 _92528)). Qed.
Lemma lem6940056 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6940057 (_92528 : int) : (term302 _92528) = (term303 _92528).
Proof. exact (MK_COMB (@lem6940056) (@lem6940055 _92528)). Qed.
Lemma lem6940058 : term164 = term164.
Proof. exact (eq_refl term164). Qed.
Lemma lem6940059 (_92528 : int) : (term291 _92528) = (term304 _92528).
Proof. exact (MK_COMB (@lem6940057 _92528) (@lem6940058)). Qed.
Lemma lem6940060 (_92528 : int) : (term268 _92528) = (term304 _92528).
Proof. exact (TRANS (@lem6940013 _92528) (@lem6940059 _92528)). Qed.
Lemma lem6940061 (_92528 : int) (_92527 : int) : (term281 _92528 _92527) = (term305 _92528 _92527).
Proof. exact (@lem1988287 (term158 _92528 _92527) (term278 _92528 _92527)). Qed.
Lemma lem6940062 : term168 = term168.
Proof. exact (eq_refl term168). Qed.
Lemma lem6940069 (_92527 : int) (_92528 : int) : (term158 _92528 _92527) = (term158 _92527 _92528).
Proof. exact (@lem1982761 (real_of_int _92527) (real_of_int _92528)). Qed.
Lemma lem6940070 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6940071 (_92527 : int) (_92528 : int) : (term277 _92528 _92527) = (term277 _92527 _92528).
Proof. exact (MK_COMB (@lem6940070) (@lem6940069 _92527 _92528)). Qed.
Lemma lem6940072 (_92527 : int) (_92528 : int) : (term278 _92528 _92527) = (term278 _92527 _92528).
Proof. exact (MK_COMB (@lem6940071 _92527 _92528) (@lem6940062)). Qed.
Lemma lem6940077 (_92527 : int) (_92528 : int) : (term278 _92527 _92528) = (term306 _92527 _92528).
Proof. exact (@lem1982755 (real_of_int _92527) (real_of_int _92528) term168). Qed.
Lemma lem6940078 (_92527 : int) (_92528 : int) : (term278 _92528 _92527) = (term306 _92527 _92528).
Proof. exact (TRANS (@lem6940072 _92527 _92528) (@lem6940077 _92527 _92528)). Qed.
Lemma lem6940085 (_92527 : int) (_92528 : int) : (term158 _92528 _92527) = (term158 _92527 _92528).
Proof. exact (@lem1982761 (real_of_int _92527) (real_of_int _92528)). Qed.
Lemma lem6940086 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem6940087 (_92527 : int) (_92528 : int) : (term307 _92528 _92527) = (term307 _92527 _92528).
Proof. exact (MK_COMB (@lem6940086) (@lem6940085 _92527 _92528)). Qed.
Lemma lem6940088 (_92527 : int) (_92528 : int) : (term308 _92528 _92527) = (term309 _92527 _92528).
Proof. exact (MK_COMB (@lem6940087 _92527 _92528) (@lem6940078 _92527 _92528)). Qed.
Lemma lem6940089 (_92527 : int) (_92528 : int) : (term309 _92527 _92528) = (term310 _92527 _92528).
Proof. exact (@lem1982792 (term158 _92527 _92528) (term306 _92527 _92528)). Qed.
Lemma lem6940090 (_92527 : int) (_92528 : int) : (term311 _92527 _92528) = (term312 _92527 _92528).
Proof. exact (@lem1982781 (real_of_int _92527) term188 (term313 _92528)). Qed.
Lemma lem6940091 (_92528 : int) : (term314 _92528) = (term315 _92528).
Proof. exact (@lem1982781 (real_of_int _92528) term188 term168). Qed.
Lemma lem6940093 (x : nat) : (real_of_num x) = (term184 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6940094 : term168 = term185.
Proof. exact (@lem6940093 term169). Qed.
Lemma lem6940096 (x : nat) : (term186 x) = (term187 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6940097 : term188 = term189.
Proof. exact (@lem6940096 term169). Qed.
Lemma lem6940098 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6940099 : term190 = term191.
Proof. exact (MK_COMB (@lem6940098) (@lem6940097)). Qed.
Lemma lem6940100 : term192 = term193.
Proof. exact (MK_COMB (@lem6940099) (@lem6940094)). Qed.
Lemma lem6940101 : term193 = term194.
Proof. exact (@lem1981613 term188 term168 term168 term168). Qed.
Lemma lem6940103 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6940104 : term197 = term198.
Proof. exact (@lem6940103 term169 term169). Qed.
Lemma lem6940105 : (term199 = (BIT1 0)) = (term200 = term169).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6940106 : term200 = term169.
Proof. exact (EQ_MP (@lem6940105) (@lem940073)). Qed.
Lemma lem6940107 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6940108 : term198 = term168.
Proof. exact (MK_COMB (@lem6940107) (@lem6940106)). Qed.
Lemma lem6940109 : term197 = term168.
Proof. exact (TRANS (@lem6940104) (@lem6940108)). Qed.
Lemma lem6940111 (m : nat) (n : nat) : (term201 m n) = (term202 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6940112 : term192 = term203.
Proof. exact (@lem6940111 term169 term169). Qed.
Lemma lem6940113 : (term199 = (BIT1 0)) = (term200 = term169).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6940114 : term200 = term169.
Proof. exact (EQ_MP (@lem6940113) (@lem940073)). Qed.
Lemma lem6940115 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6940116 : term198 = term168.
Proof. exact (MK_COMB (@lem6940115) (@lem6940114)). Qed.
Lemma lem6940117 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6940118 : term203 = term188.
Proof. exact (MK_COMB (@lem6940117) (@lem6940116)). Qed.
Lemma lem6940119 : term192 = term188.
Proof. exact (TRANS (@lem6940112) (@lem6940118)). Qed.
Lemma lem6940120 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6940121 : term204 = term205.
Proof. exact (MK_COMB (@lem6940120) (@lem6940119)). Qed.
Lemma lem6940122 : term194 = term189.
Proof. exact (MK_COMB (@lem6940121) (@lem6940109)). Qed.
Lemma lem6940123 : term193 = term189.
Proof. exact (TRANS (@lem6940101) (@lem6940122)). Qed.
Lemma lem6940124 : term192 = term189.
Proof. exact (TRANS (@lem6940100) (@lem6940123)). Qed.
Lemma lem6940126 (x : real) : (term206 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6940127 : term189 = term188.
Proof. exact (@lem6940126 term188). Qed.
Lemma lem6940128 : term192 = term188.
Proof. exact (TRANS (@lem6940124) (@lem6940127)). Qed.
Lemma lem6940131 (_92528 : int) : (term316 _92528) = (term316 _92528).
Proof. exact (eq_refl (term316 _92528)). Qed.
Lemma lem6940132 (_92528 : int) : (term315 _92528) = (term317 _92528).
Proof. exact (MK_COMB (@lem6940131 _92528) (@lem6940128)). Qed.
Lemma lem6940133 (_92528 : int) : (term314 _92528) = (term317 _92528).
Proof. exact (TRANS (@lem6940091 _92528) (@lem6940132 _92528)). Qed.
Lemma lem6940136 (_92527 : int) : (term316 _92527) = (term316 _92527).
Proof. exact (eq_refl (term316 _92527)). Qed.
Lemma lem6940137 (_92527 : int) (_92528 : int) : (term312 _92527 _92528) = (term318 _92527 _92528).
Proof. exact (MK_COMB (@lem6940136 _92527) (@lem6940133 _92528)). Qed.
Lemma lem6940138 (_92527 : int) (_92528 : int) : (term311 _92527 _92528) = (term318 _92527 _92528).
Proof. exact (TRANS (@lem6940090 _92527 _92528) (@lem6940137 _92527 _92528)). Qed.
Lemma lem6940139 (_92527 : int) (_92528 : int) : (term277 _92527 _92528) = (term277 _92527 _92528).
Proof. exact (eq_refl (term277 _92527 _92528)). Qed.
Lemma lem6940140 (_92527 : int) (_92528 : int) : (term310 _92527 _92528) = (term319 _92527 _92528).
Proof. exact (MK_COMB (@lem6940139 _92527 _92528) (@lem6940138 _92527 _92528)). Qed.
Lemma lem6940141 (_92527 : int) (_92528 : int) : (term319 _92527 _92528) = (term320 _92527 _92528).
Proof. exact (@lem1982753 (real_of_int _92527) (term321 _92527) (real_of_int _92528) (term317 _92528)). Qed.
Lemma lem6940142 (_92527 : int) : (term322 _92527) = (term323 _92527).
Proof. exact (@lem1982715 term188 (real_of_int _92527)). Qed.
Lemma lem6940144 (x : nat) : (real_of_num x) = (term184 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6940145 : term168 = term185.
Proof. exact (@lem6940144 term169). Qed.
Lemma lem6940147 (x : nat) : (term186 x) = (term187 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6940148 : term188 = term189.
Proof. exact (@lem6940147 term169). Qed.
Lemma lem6940149 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6940150 : term324 = term325.
Proof. exact (MK_COMB (@lem6940149) (@lem6940148)). Qed.
Lemma lem6940151 : term326 = term327.
Proof. exact (MK_COMB (@lem6940150) (@lem6940145)). Qed.
Lemma lem6940152 : term328.
Proof. exact (@lem1981473 term188 term168 term168 term168 term164 term168). Qed.
Lemma lem6940154 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6940155 : term218 = term219.
Proof. exact (@lem6940154 (NUMERAL 0) term169). Qed.
Lemma lem6940156 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6940157 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6940158 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem6940157 h1) (fun h1 : term219 = True => @lem6940156)). Qed.
Lemma lem6940159 : term219 = True.
Proof. exact (EQ_MP (@lem6940158) (@lem6940156)). Qed.
Lemma lem6940160 : term218 = True.
Proof. exact (TRANS (@lem6940155) (@lem6940159)). Qed.
Lemma lem6940161 : True = term218.
Proof. exact (SYM (@lem6940160)). Qed.
Lemma lem6940162 : term218.
Proof. exact (EQ_MP (@lem6940161) (@lem0)). Qed.
Lemma lem6940163 : term329.
Proof. exact (@lem6940152 (@lem6940162)). Qed.
Lemma lem6940165 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6940166 : term218 = term219.
Proof. exact (@lem6940165 (NUMERAL 0) term169). Qed.
Lemma lem6940167 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6940168 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6940169 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem6940168 h1) (fun h1 : term219 = True => @lem6940167)). Qed.
Lemma lem6940170 : term219 = True.
Proof. exact (EQ_MP (@lem6940169) (@lem6940167)). Qed.
Lemma lem6940171 : term218 = True.
Proof. exact (TRANS (@lem6940166) (@lem6940170)). Qed.
Lemma lem6940172 : True = term218.
Proof. exact (SYM (@lem6940171)). Qed.
Lemma lem6940173 : term218.
Proof. exact (EQ_MP (@lem6940172) (@lem0)). Qed.
Lemma lem6940174 : term330.
Proof. exact (@lem6940163 (@lem6940173)). Qed.
Lemma lem6940176 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6940177 : term218 = term219.
Proof. exact (@lem6940176 (NUMERAL 0) term169). Qed.
Lemma lem6940178 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6940179 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6940180 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem6940179 h1) (fun h1 : term219 = True => @lem6940178)). Qed.
Lemma lem6940181 : term219 = True.
Proof. exact (EQ_MP (@lem6940180) (@lem6940178)). Qed.
Lemma lem6940182 : term218 = True.
Proof. exact (TRANS (@lem6940177) (@lem6940181)). Qed.
Lemma lem6940183 : True = term218.
Proof. exact (SYM (@lem6940182)). Qed.
Lemma lem6940184 : term218.
Proof. exact (EQ_MP (@lem6940183) (@lem0)). Qed.
Lemma lem6940185 : term331.
Proof. exact (@lem6940174 (@lem6940184)). Qed.
Lemma lem6940187 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6940188 : term197 = term198.
Proof. exact (@lem6940187 term169 term169). Qed.
Lemma lem6940189 : (term199 = (BIT1 0)) = (term200 = term169).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6940190 : term200 = term169.
Proof. exact (EQ_MP (@lem6940189) (@lem940073)). Qed.
Lemma lem6940191 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6940192 : term198 = term168.
Proof. exact (MK_COMB (@lem6940191) (@lem6940190)). Qed.
Lemma lem6940193 : term197 = term168.
Proof. exact (TRANS (@lem6940188) (@lem6940192)). Qed.
Lemma lem6940195 (m : nat) (n : nat) : (term201 m n) = (term202 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6940196 : term192 = term203.
Proof. exact (@lem6940195 term169 term169). Qed.
Lemma lem6940197 : (term199 = (BIT1 0)) = (term200 = term169).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6940198 : term200 = term169.
Proof. exact (EQ_MP (@lem6940197) (@lem940073)). Qed.
Lemma lem6940199 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6940200 : term198 = term168.
Proof. exact (MK_COMB (@lem6940199) (@lem6940198)). Qed.
Lemma lem6940201 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6940202 : term203 = term188.
Proof. exact (MK_COMB (@lem6940201) (@lem6940200)). Qed.
Lemma lem6940203 : term192 = term188.
Proof. exact (TRANS (@lem6940196) (@lem6940202)). Qed.
Lemma lem6940204 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6940205 : term332 = term324.
Proof. exact (MK_COMB (@lem6940204) (@lem6940203)). Qed.
Lemma lem6940206 : term333 = term326.
Proof. exact (MK_COMB (@lem6940205) (@lem6940193)). Qed.
Lemma lem6940208 (m : nat) : (term334 m) = term164.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6940209 : term326 = term164.
Proof. exact (@lem6940208 term169). Qed.
Lemma lem6940210 : term333 = term164.
Proof. exact (TRANS (@lem6940206) (@lem6940209)). Qed.
Lemma lem6940211 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6940212 : term335 = term336.
Proof. exact (MK_COMB (@lem6940211) (@lem6940210)). Qed.
Lemma lem6940213 : term168 = term168.
Proof. exact (eq_refl term168). Qed.
Lemma lem6940214 : term337 = term224.
Proof. exact (MK_COMB (@lem6940212) (@lem6940213)). Qed.
Lemma lem6940216 (x : nat) : (term223 x) = term164.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6940217 : term224 = term164.
Proof. exact (@lem6940216 term169). Qed.
Lemma lem6940218 : term337 = term164.
Proof. exact (TRANS (@lem6940214) (@lem6940217)). Qed.
Lemma lem6940220 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6940221 : term197 = term198.
Proof. exact (@lem6940220 term169 term169). Qed.
Lemma lem6940222 : (term199 = (BIT1 0)) = (term200 = term169).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6940223 : term200 = term169.
Proof. exact (EQ_MP (@lem6940222) (@lem940073)). Qed.
Lemma lem6940224 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6940225 : term198 = term168.
Proof. exact (MK_COMB (@lem6940224) (@lem6940223)). Qed.
Lemma lem6940226 : term197 = term168.
Proof. exact (TRANS (@lem6940221) (@lem6940225)). Qed.
Lemma lem6940227 : term336 = term336.
Proof. exact (eq_refl term336). Qed.
Lemma lem6940228 : term338 = term224.
Proof. exact (MK_COMB (@lem6940227) (@lem6940226)). Qed.
Lemma lem6940230 (x : nat) : (term223 x) = term164.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6940231 : term224 = term164.
Proof. exact (@lem6940230 term169). Qed.
Lemma lem6940232 : term338 = term164.
Proof. exact (TRANS (@lem6940228) (@lem6940231)). Qed.
Lemma lem6940233 : term164 = term338.
Proof. exact (SYM (@lem6940232)). Qed.
Lemma lem6940234 : term337 = term338.
Proof. exact (TRANS (@lem6940218) (@lem6940233)). Qed.
Lemma lem6940235 : term327 = term212.
Proof. exact (@lem6940185 (@lem6940234)). Qed.
Lemma lem6940236 : term326 = term212.
Proof. exact (TRANS (@lem6940151) (@lem6940235)). Qed.
Lemma lem6940238 (x : real) : (term206 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6940239 : term212 = term164.
Proof. exact (@lem6940238 term164). Qed.
Lemma lem6940240 : term326 = term164.
Proof. exact (TRANS (@lem6940236) (@lem6940239)). Qed.
Lemma lem6940241 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6940242 : term339 = term336.
Proof. exact (MK_COMB (@lem6940241) (@lem6940240)). Qed.
Lemma lem6940243 (_92527 : int) : (real_of_int _92527) = (real_of_int _92527).
Proof. exact (eq_refl (real_of_int _92527)). Qed.
Lemma lem6940244 (_92527 : int) : (term323 _92527) = (term340 _92527).
Proof. exact (MK_COMB (@lem6940242) (@lem6940243 _92527)). Qed.
Lemma lem6940245 (_92527 : int) : (term322 _92527) = (term340 _92527).
Proof. exact (TRANS (@lem6940142 _92527) (@lem6940244 _92527)). Qed.
Lemma lem6940246 (_92527 : int) : (term340 _92527) = term164.
Proof. exact (@lem1982719 (real_of_int _92527)). Qed.
Lemma lem6940247 (_92527 : int) : (term322 _92527) = term164.
Proof. exact (TRANS (@lem6940245 _92527) (@lem6940246 _92527)). Qed.
Lemma lem6940248 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6940249 (_92527 : int) : (term341 _92527) = term166.
Proof. exact (MK_COMB (@lem6940248) (@lem6940247 _92527)). Qed.
Lemma lem6940250 (_92528 : int) : (term342 _92528) = (term343 _92528).
Proof. exact (@lem1982763 (real_of_int _92528) (term321 _92528) term188). Qed.
Lemma lem6940251 (_92528 : int) : (term322 _92528) = (term323 _92528).
Proof. exact (@lem1982715 term188 (real_of_int _92528)). Qed.
Lemma lem6940253 (x : nat) : (real_of_num x) = (term184 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6940254 : term168 = term185.
Proof. exact (@lem6940253 term169). Qed.
Lemma lem6940256 (x : nat) : (term186 x) = (term187 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6940257 : term188 = term189.
Proof. exact (@lem6940256 term169). Qed.
Lemma lem6940258 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6940259 : term324 = term325.
Proof. exact (MK_COMB (@lem6940258) (@lem6940257)). Qed.
Lemma lem6940260 : term326 = term327.
Proof. exact (MK_COMB (@lem6940259) (@lem6940254)). Qed.
Lemma lem6940261 : term328.
Proof. exact (@lem1981473 term188 term168 term168 term168 term164 term168). Qed.
Lemma lem6940263 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6940264 : term218 = term219.
Proof. exact (@lem6940263 (NUMERAL 0) term169). Qed.
Lemma lem6940265 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6940266 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6940267 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem6940266 h1) (fun h1 : term219 = True => @lem6940265)). Qed.
Lemma lem6940268 : term219 = True.
Proof. exact (EQ_MP (@lem6940267) (@lem6940265)). Qed.
Lemma lem6940269 : term218 = True.
Proof. exact (TRANS (@lem6940264) (@lem6940268)). Qed.
Lemma lem6940270 : True = term218.
Proof. exact (SYM (@lem6940269)). Qed.
Lemma lem6940271 : term218.
Proof. exact (EQ_MP (@lem6940270) (@lem0)). Qed.
Lemma lem6940272 : term329.
Proof. exact (@lem6940261 (@lem6940271)). Qed.
Lemma lem6940274 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6940275 : term218 = term219.
Proof. exact (@lem6940274 (NUMERAL 0) term169). Qed.
Lemma lem6940276 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6940277 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6940278 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem6940277 h1) (fun h1 : term219 = True => @lem6940276)). Qed.
Lemma lem6940279 : term219 = True.
Proof. exact (EQ_MP (@lem6940278) (@lem6940276)). Qed.
Lemma lem6940280 : term218 = True.
Proof. exact (TRANS (@lem6940275) (@lem6940279)). Qed.
Lemma lem6940281 : True = term218.
Proof. exact (SYM (@lem6940280)). Qed.
Lemma lem6940282 : term218.
Proof. exact (EQ_MP (@lem6940281) (@lem0)). Qed.
Lemma lem6940283 : term330.
Proof. exact (@lem6940272 (@lem6940282)). Qed.
Lemma lem6940285 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6940286 : term218 = term219.
Proof. exact (@lem6940285 (NUMERAL 0) term169). Qed.
Lemma lem6940287 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6940288 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6940289 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem6940288 h1) (fun h1 : term219 = True => @lem6940287)). Qed.
Lemma lem6940290 : term219 = True.
Proof. exact (EQ_MP (@lem6940289) (@lem6940287)). Qed.
Lemma lem6940291 : term218 = True.
Proof. exact (TRANS (@lem6940286) (@lem6940290)). Qed.
Lemma lem6940292 : True = term218.
Proof. exact (SYM (@lem6940291)). Qed.
Lemma lem6940293 : term218.
Proof. exact (EQ_MP (@lem6940292) (@lem0)). Qed.
Lemma lem6940294 : term331.
Proof. exact (@lem6940283 (@lem6940293)). Qed.
Lemma lem6940296 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6940297 : term197 = term198.
Proof. exact (@lem6940296 term169 term169). Qed.
Lemma lem6940298 : (term199 = (BIT1 0)) = (term200 = term169).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6940299 : term200 = term169.
Proof. exact (EQ_MP (@lem6940298) (@lem940073)). Qed.
Lemma lem6940300 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6940301 : term198 = term168.
Proof. exact (MK_COMB (@lem6940300) (@lem6940299)). Qed.
Lemma lem6940302 : term197 = term168.
Proof. exact (TRANS (@lem6940297) (@lem6940301)). Qed.
Lemma lem6940304 (m : nat) (n : nat) : (term201 m n) = (term202 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6940305 : term192 = term203.
Proof. exact (@lem6940304 term169 term169). Qed.
Lemma lem6940306 : (term199 = (BIT1 0)) = (term200 = term169).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6940307 : term200 = term169.
Proof. exact (EQ_MP (@lem6940306) (@lem940073)). Qed.
Lemma lem6940308 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6940309 : term198 = term168.
Proof. exact (MK_COMB (@lem6940308) (@lem6940307)). Qed.
Lemma lem6940310 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6940311 : term203 = term188.
Proof. exact (MK_COMB (@lem6940310) (@lem6940309)). Qed.
Lemma lem6940312 : term192 = term188.
Proof. exact (TRANS (@lem6940305) (@lem6940311)). Qed.
Lemma lem6940313 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6940314 : term332 = term324.
Proof. exact (MK_COMB (@lem6940313) (@lem6940312)). Qed.
Lemma lem6940315 : term333 = term326.
Proof. exact (MK_COMB (@lem6940314) (@lem6940302)). Qed.
Lemma lem6940317 (m : nat) : (term334 m) = term164.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6940318 : term326 = term164.
Proof. exact (@lem6940317 term169). Qed.
Lemma lem6940319 : term333 = term164.
Proof. exact (TRANS (@lem6940315) (@lem6940318)). Qed.
Lemma lem6940320 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6940321 : term335 = term336.
Proof. exact (MK_COMB (@lem6940320) (@lem6940319)). Qed.
Lemma lem6940322 : term168 = term168.
Proof. exact (eq_refl term168). Qed.
Lemma lem6940323 : term337 = term224.
Proof. exact (MK_COMB (@lem6940321) (@lem6940322)). Qed.
Lemma lem6940325 (x : nat) : (term223 x) = term164.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6940326 : term224 = term164.
Proof. exact (@lem6940325 term169). Qed.
Lemma lem6940327 : term337 = term164.
Proof. exact (TRANS (@lem6940323) (@lem6940326)). Qed.
Lemma lem6940329 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6940330 : term197 = term198.
Proof. exact (@lem6940329 term169 term169). Qed.
Lemma lem6940331 : (term199 = (BIT1 0)) = (term200 = term169).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6940332 : term200 = term169.
Proof. exact (EQ_MP (@lem6940331) (@lem940073)). Qed.
Lemma lem6940333 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6940334 : term198 = term168.
Proof. exact (MK_COMB (@lem6940333) (@lem6940332)). Qed.
Lemma lem6940335 : term197 = term168.
Proof. exact (TRANS (@lem6940330) (@lem6940334)). Qed.
Lemma lem6940336 : term336 = term336.
Proof. exact (eq_refl term336). Qed.
Lemma lem6940337 : term338 = term224.
Proof. exact (MK_COMB (@lem6940336) (@lem6940335)). Qed.
Lemma lem6940339 (x : nat) : (term223 x) = term164.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6940340 : term224 = term164.
Proof. exact (@lem6940339 term169). Qed.
Lemma lem6940341 : term338 = term164.
Proof. exact (TRANS (@lem6940337) (@lem6940340)). Qed.
Lemma lem6940342 : term164 = term338.
Proof. exact (SYM (@lem6940341)). Qed.
Lemma lem6940343 : term337 = term338.
Proof. exact (TRANS (@lem6940327) (@lem6940342)). Qed.
Lemma lem6940344 : term327 = term212.
Proof. exact (@lem6940294 (@lem6940343)). Qed.
Lemma lem6940345 : term326 = term212.
Proof. exact (TRANS (@lem6940260) (@lem6940344)). Qed.
Lemma lem6940347 (x : real) : (term206 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6940348 : term212 = term164.
Proof. exact (@lem6940347 term164). Qed.
Lemma lem6940349 : term326 = term164.
Proof. exact (TRANS (@lem6940345) (@lem6940348)). Qed.
Lemma lem6940350 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6940351 : term339 = term336.
Proof. exact (MK_COMB (@lem6940350) (@lem6940349)). Qed.
Lemma lem6940352 (_92528 : int) : (real_of_int _92528) = (real_of_int _92528).
Proof. exact (eq_refl (real_of_int _92528)). Qed.
Lemma lem6940353 (_92528 : int) : (term323 _92528) = (term340 _92528).
Proof. exact (MK_COMB (@lem6940351) (@lem6940352 _92528)). Qed.
Lemma lem6940354 (_92528 : int) : (term322 _92528) = (term340 _92528).
Proof. exact (TRANS (@lem6940251 _92528) (@lem6940353 _92528)). Qed.
Lemma lem6940355 (_92528 : int) : (term340 _92528) = term164.
Proof. exact (@lem1982719 (real_of_int _92528)). Qed.
Lemma lem6940356 (_92528 : int) : (term322 _92528) = term164.
Proof. exact (TRANS (@lem6940354 _92528) (@lem6940355 _92528)). Qed.
Lemma lem6940357 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6940358 (_92528 : int) : (term341 _92528) = term166.
Proof. exact (MK_COMB (@lem6940357) (@lem6940356 _92528)). Qed.
Lemma lem6940359 : term188 = term188.
Proof. exact (eq_refl term188). Qed.
Lemma lem6940360 (_92528 : int) : (term343 _92528) = term207.
Proof. exact (MK_COMB (@lem6940358 _92528) (@lem6940359)). Qed.
Lemma lem6940361 (_92528 : int) : (term342 _92528) = term207.
Proof. exact (TRANS (@lem6940250 _92528) (@lem6940360 _92528)). Qed.
Lemma lem6940362 : term207 = term188.
Proof. exact (@lem1982721 term188). Qed.
Lemma lem6940363 (_92528 : int) : (term342 _92528) = term188.
Proof. exact (TRANS (@lem6940361 _92528) (@lem6940362)). Qed.
Lemma lem6940364 (_92527 : int) (_92528 : int) : (term320 _92527 _92528) = term207.
Proof. exact (MK_COMB (@lem6940249 _92527) (@lem6940363 _92528)). Qed.
Lemma lem6940365 (_92527 : int) (_92528 : int) : (term319 _92527 _92528) = term207.
Proof. exact (TRANS (@lem6940141 _92527 _92528) (@lem6940364 _92527 _92528)). Qed.
Lemma lem6940366 : term207 = term188.
Proof. exact (@lem1982721 term188). Qed.
Lemma lem6940367 (_92527 : int) (_92528 : int) : (term319 _92527 _92528) = term188.
Proof. exact (TRANS (@lem6940365 _92527 _92528) (@lem6940366)). Qed.
Lemma lem6940368 (_92527 : int) (_92528 : int) : (term310 _92527 _92528) = term188.
Proof. exact (TRANS (@lem6940140 _92527 _92528) (@lem6940367 _92527 _92528)). Qed.
Lemma lem6940369 (_92527 : int) (_92528 : int) : (term309 _92527 _92528) = term188.
Proof. exact (TRANS (@lem6940089 _92527 _92528) (@lem6940368 _92527 _92528)). Qed.
Lemma lem6940370 (_92528 : int) (_92527 : int) : (term308 _92528 _92527) = term188.
Proof. exact (TRANS (@lem6940088 _92527 _92528) (@lem6940369 _92527 _92528)). Qed.
Lemma lem6940371 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6940372 (_92528 : int) (_92527 : int) : (term344 _92528 _92527) = term209.
Proof. exact (MK_COMB (@lem6940371) (@lem6940370 _92528 _92527)). Qed.
Lemma lem6940373 : term164 = term164.
Proof. exact (eq_refl term164). Qed.
Lemma lem6940374 (_92528 : int) (_92527 : int) : (term305 _92528 _92527) = term210.
Proof. exact (MK_COMB (@lem6940372 _92528 _92527) (@lem6940373)). Qed.
Lemma lem6940375 (_92528 : int) (_92527 : int) : (term281 _92528 _92527) = term210.
Proof. exact (TRANS (@lem6940061 _92528 _92527) (@lem6940374 _92528 _92527)). Qed.
Lemma lem6940376 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6940377 (_92528 : int) : (term285 _92528) = (term345 _92528).
Proof. exact (MK_COMB (@lem6940376) (@lem6940060 _92528)). Qed.
Lemma lem6940378 (_92527 : int) (_92528 : int) : (term289 _92528 _92527) = (term346 _92528).
Proof. exact (MK_COMB (@lem6940377 _92528) (@lem6940375 _92528 _92527)). Qed.
Lemma lem6940379 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6940380 (_92527 : int) : (term285 _92527) = (term345 _92527).
Proof. exact (MK_COMB (@lem6940379) (@lem6940012 _92527)). Qed.
Lemma lem6940381 (_92527 : int) (_92528 : int) : (term290 _92528 _92527) = (term347 _92527 _92528).
Proof. exact (MK_COMB (@lem6940380 _92527) (@lem6940378 _92527 _92528)). Qed.
Lemma lem6940402 (_92527 : int) (_92528 : int) : (term288 _92528 _92527) = (term347 _92527 _92528).
Proof. exact (TRANS (@lem6939964 _92528 _92527) (@lem6940381 _92527 _92528)). Qed.
Lemma lem6940406 (_92527 : int) (_92528 : int) (h1 : term347 _92527 _92528) : term347 _92527 _92528.
Proof. exact (h1). Qed.
Lemma lem6940407 (_92527 : int) (_92528 : int) (h1 : term347 _92527 _92528) : term346 _92528.
Proof. exact (proj2 (@lem6940406 _92527 _92528 h1)). Qed.
Lemma lem6940409 (_92527 : int) (_92528 : int) (h1 : term347 _92527 _92528) : term210.
Proof. exact (proj2 (@lem6940407 _92527 _92528 h1)). Qed.
Lemma lem6940412 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6940413 : term210 = term211.
Proof. exact (@lem6940412 term164 term188). Qed.
Lemma lem6940415 (x : nat) : (term186 x) = (term187 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6940416 : term188 = term189.
Proof. exact (@lem6940415 term169). Qed.
Lemma lem6940418 (x : nat) : (real_of_num x) = (term184 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6940419 : term164 = term212.
Proof. exact (@lem6940418 (NUMERAL 0)). Qed.
Lemma lem6940420 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6940421 : term213 = term214.
Proof. exact (MK_COMB (@lem6940420) (@lem6940419)). Qed.
Lemma lem6940422 : term211 = term215.
Proof. exact (MK_COMB (@lem6940421) (@lem6940416)). Qed.
Lemma lem6940423 : term216.
Proof. exact (@lem1980026 term164 term168 term188 term168). Qed.
Lemma lem6940425 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6940426 : term218 = term219.
Proof. exact (@lem6940425 (NUMERAL 0) term169). Qed.
Lemma lem6940427 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6940428 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6940429 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem6940428 h1) (fun h1 : term219 = True => @lem6940427)). Qed.
Lemma lem6940430 : term219 = True.
Proof. exact (EQ_MP (@lem6940429) (@lem6940427)). Qed.
Lemma lem6940431 : term218 = True.
Proof. exact (TRANS (@lem6940426) (@lem6940430)). Qed.
Lemma lem6940432 : True = term218.
Proof. exact (SYM (@lem6940431)). Qed.
Lemma lem6940433 : term218.
Proof. exact (EQ_MP (@lem6940432) (@lem0)). Qed.
Lemma lem6940434 : term221.
Proof. exact (@lem6940423 (@lem6940433)). Qed.
Lemma lem6940436 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6940437 : term218 = term219.
Proof. exact (@lem6940436 (NUMERAL 0) term169). Qed.
Lemma lem6940438 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6940439 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6940440 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem6940439 h1) (fun h1 : term219 = True => @lem6940438)). Qed.
Lemma lem6940441 : term219 = True.
Proof. exact (EQ_MP (@lem6940440) (@lem6940438)). Qed.
Lemma lem6940442 : term218 = True.
Proof. exact (TRANS (@lem6940437) (@lem6940441)). Qed.
Lemma lem6940443 : True = term218.
Proof. exact (SYM (@lem6940442)). Qed.
Lemma lem6940444 : term218.
Proof. exact (EQ_MP (@lem6940443) (@lem0)). Qed.
Lemma lem6940445 : term215 = term222.
Proof. exact (@lem6940434 (@lem6940444)). Qed.
Lemma lem6940447 (m : nat) (n : nat) : (term201 m n) = (term202 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6940448 : term192 = term203.
Proof. exact (@lem6940447 term169 term169). Qed.
Lemma lem6940449 : (term199 = (BIT1 0)) = (term200 = term169).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6940450 : term200 = term169.
Proof. exact (EQ_MP (@lem6940449) (@lem940073)). Qed.
Lemma lem6940451 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6940452 : term198 = term168.
Proof. exact (MK_COMB (@lem6940451) (@lem6940450)). Qed.
Lemma lem6940453 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6940454 : term203 = term188.
Proof. exact (MK_COMB (@lem6940453) (@lem6940452)). Qed.
Lemma lem6940455 : term192 = term188.
Proof. exact (TRANS (@lem6940448) (@lem6940454)). Qed.
Lemma lem6940457 (x : nat) : (term223 x) = term164.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6940458 : term224 = term164.
Proof. exact (@lem6940457 term169). Qed.
Lemma lem6940459 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6940460 : term225 = term213.
Proof. exact (MK_COMB (@lem6940459) (@lem6940458)). Qed.
Lemma lem6940461 : term222 = term211.
Proof. exact (MK_COMB (@lem6940460) (@lem6940455)). Qed.
Lemma lem6940463 (m : nat) (n : nat) : (term226 m n) = (term227 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6940464 : term211 = term228.
Proof. exact (@lem6940463 (NUMERAL 0) term169). Qed.
Lemma lem6940465 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6940466 (h1 : term220 = (BIT1 0)) : (term169 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6940467 : (term220 = (BIT1 0)) = ((term169 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem6940466 h1) (fun h1 : (term169 = (NUMERAL 0)) = False => @lem6940465)). Qed.
Lemma lem6940468 : (term169 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6940467) (@lem6940465)). Qed.
Lemma lem6940469 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6940470 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6940471 : term229 = (and True).
Proof. exact (MK_COMB (@lem6940470) (@lem6940469)). Qed.
Lemma lem6940472 : term228 = (True /\ False).
Proof. exact (MK_COMB (@lem6940471) (@lem6940468)). Qed.
Lemma lem6940474 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6940475 : term228 = False.
Proof. exact (TRANS (@lem6940472) (@lem6940474)). Qed.
Lemma lem6940476 : term211 = False.
Proof. exact (TRANS (@lem6940464) (@lem6940475)). Qed.
Lemma lem6940477 : term222 = False.
Proof. exact (TRANS (@lem6940461) (@lem6940476)). Qed.
Lemma lem6940478 : term215 = False.
Proof. exact (TRANS (@lem6940445) (@lem6940477)). Qed.
Lemma lem6940479 : term211 = False.
Proof. exact (TRANS (@lem6940422) (@lem6940478)). Qed.
Lemma lem6940480 : term210 = False.
Proof. exact (TRANS (@lem6940413) (@lem6940479)). Qed.
Lemma lem6940481 (_92527 : int) (_92528 : int) (h1 : term347 _92527 _92528) : False.
Proof. exact (EQ_MP (@lem6940480) (@lem6940409 _92527 _92528 h1)). Qed.
Lemma lem6940483 (_92527 : int) (_92528 : int) (h1 : term347 _92527 _92528) : term347 _92527 _92528.
Proof. exact (h1). Qed.
Lemma lem6940484 (_92527 : int) (_92528 : int) (h1 : term347 _92527 _92528) : (term347 _92527 _92528) = False.
Proof. exact (prop_ext (fun h2 : term347 _92527 _92528 => @lem6940481 _92527 _92528 h1) (fun h2 : False => @lem6940483 _92527 _92528 h1)). Qed.
Lemma lem6940485 (_92527 : int) (_92528 : int) (h1 : term347 _92527 _92528) : False.
Proof. exact (EQ_MP (@lem6940484 _92527 _92528 h1) (@lem6940483 _92527 _92528 h1)). Qed.
Lemma lem6940486 (_92528 : int) (_92527 : int) (h1 : term288 _92528 _92527) : term288 _92528 _92527.
Proof. exact (h1). Qed.
Lemma lem6940487 (_92528 : int) (_92527 : int) (h1 : term288 _92528 _92527) : term347 _92527 _92528.
Proof. exact (EQ_MP (@lem6940402 _92527 _92528) (@lem6940486 _92528 _92527 h1)). Qed.
Lemma lem6940488 (_92528 : int) (_92527 : int) (h1 : term288 _92528 _92527) : (term347 _92527 _92528) = False.
Proof. exact (prop_ext (fun h2 : term347 _92527 _92528 => @lem6940485 _92527 _92528 h2) (fun h2 : False => @lem6940487 _92528 _92527 h1)). Qed.
Lemma lem6940489 (_92528 : int) (_92527 : int) (h1 : term288 _92528 _92527) : False.
Proof. exact (EQ_MP (@lem6940488 _92528 _92527 h1) (@lem6940487 _92528 _92527 h1)). Qed.
Lemma lem6940490 (_92528 : int) (_92527 : int) : term348 _92528 _92527.
Proof. exact (fun h0 : term288 _92528 _92527 => @lem6940489 _92528 _92527 h0). Qed.
Lemma lem6940491 (_92528 : int) (_92527 : int) : term349 _92528 _92527.
Proof. exact (@lem1386578 (term350 _92528 _92527)). Qed.
Lemma lem6940494 (_92528 : int) (_92527 : int) : term350 _92528 _92527.
Proof. exact (@lem6940491 _92528 _92527 (@lem6940490 _92528 _92527)). Qed.
Lemma lem6940495 (_92528 : int) (_92527 : int) : (term287 _92528 _92527) = (term264 _92528 _92527).
Proof. exact (SYM (@lem6939922 _92528 _92527)). Qed.
Lemma lem6940496 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6940497 (_92528 : int) (_92527 : int) : (term350 _92528 _92527) = (term256 _92528 _92527).
Proof. exact (MK_COMB (@lem6940496) (@lem6940495 _92528 _92527)). Qed.
Lemma lem6940498 (_92528 : int) (_92527 : int) : term256 _92528 _92527.
Proof. exact (EQ_MP (@lem6940497 _92528 _92527) (@lem6940494 _92528 _92527)). Qed.
Lemma lem6940499 (_92528 : int) (_92527 : int) : term257 _92528 _92527.
Proof. exact (EQ_MP (@lem6939801 _92528 _92527) (@lem6940498 _92528 _92527)). Qed.
Lemma lem6940500 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : term351 _127196 s c.
Proof. exact (@lem6940499 (term352 _127196 c s) (int_of_num c)). Qed.
Lemma lem6940501 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : term353 _127196 s c.
Proof. exact (@lem6940500 _127196 s c (@lem6939797 c)). Qed.
Lemma lem6940502 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : (term249 _127196 s c) = (term249 _127196 s c).
Proof. exact (@lem6940501 _127196 s c (@lem6939800 _127196 c s)). Qed.
Lemma lem6940503 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : ((term249 _127196 s c) = (term249 _127196 s c)) = ((term114 _127196 s c) = (term138 _127196 s c)).
Proof. exact (SYM (@lem6939794 _127196 s c)). Qed.
Lemma lem6940504 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : (term114 _127196 s c) = (term138 _127196 s c).
Proof. exact (EQ_MP (@lem6940503 _127196 s c) (@lem6940502 _127196 s c)). Qed.
Lemma lem6940505 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : ((term114 _127196 s c) = (term138 _127196 s c)) = (((term114 _127196 s c) = (term138 _127196 s c)) = True).
Proof. exact (@lem7 ((term114 _127196 s c) = (term138 _127196 s c))). Qed.
Lemma lem6940506 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : ((term114 _127196 s c) = (term138 _127196 s c)) = True.
Proof. exact (EQ_MP (@lem6940505 _127196 s c) (@lem6940504 _127196 s c)). Qed.
Lemma lem6940507 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : True = ((term114 _127196 s c) = (term138 _127196 s c)).
Proof. exact (SYM (@lem6940506 _127196 s c)). Qed.
Lemma lem6940508 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : (term114 _127196 s c) = (term138 _127196 s c).
Proof. exact (EQ_MP (@lem6940507 _127196 s c) (@lem0)). Qed.
Lemma lem6940513 {_127196 : Type'} (x : _127196) (s : _127196 -> Prop) (c : nat) : term141 _127196 x s c.
Proof. exact (fun h0 : term39 _127196 c x s => @lem6940508 _127196 s c). Qed.
Lemma lem6940518 {_127196 : Type'} (x : _127196) (c : nat) : term143 _127196 x c.
Proof. exact (fun s : _127196 -> Prop => @lem6940513 _127196 x s c). Qed.
Lemma lem6940523 {_127196 : Type'} (c : nat) : term145 _127196 c.
Proof. exact (fun x : _127196 => @lem6940518 _127196 x c). Qed.
Lemma lem6940524 {_127196 : Type'} (c : nat) : term146 _127196 c.
Proof. exact (conj (@lem6939711 c) (@lem6940523 _127196 c)). Qed.
Lemma lem6940525 {_127196 : Type'} (c : nat) : term56 _127196 c.
Proof. exact (EQ_MP (@lem6939420 _127196 c) (@lem6940524 _127196 c)). Qed.
Lemma lem6940526 {_127196 : Type'} (c : nat) : term65 _127196 c.
Proof. exact (@lem6938916 _127196 c (@lem6940525 _127196 c)). Qed.
Lemma lem6940531 {_127196 : Type'} : term354 _127196.
Proof. exact (fun c : nat => @lem6940526 _127196 c). Qed.
