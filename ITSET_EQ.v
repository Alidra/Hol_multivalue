Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ITSET_EQ_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import FINITE_INDUCT_STRONG_spec.
Require Import FINITE_RECURSION_spec.
Require Import IN_INSERT_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import RIGHT_FORALL_IMP_THM_spec.
Require Import RIGHT_IMP_FORALL_THM_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1831_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
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
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18958_spec.
Require Import thm18959_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm196_spec.
Require Import thm19699_spec.
Require Import thm197_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm885_spec.
Require Import thm886_spec.
Lemma lem3817870 {A : Type'} (P : Prop) : term0 A P.
Proof. exact (@lem6418 A P). Qed.
Lemma lem3817871 {A : Type'} (P : Prop) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem3817872 {A : Type'} (P : Prop) : term1 A P.
Proof. exact (EQ_MP (@lem3817871 A P) (@lem3817870 A P)). Qed.
Lemma lem3817873 {A : Type'} (P : Prop) (Q : A -> Prop) : term2 A P Q.
Proof. exact (@lem3817872 A P Q). Qed.
Lemma lem3817874 {A : Type'} (P : Prop) (Q : A -> Prop) : (term2 A P Q) = ((term3 A P Q) = (term4 A P Q)).
Proof. exact (eq_refl (term2 A P Q)). Qed.
Lemma lem3817876 {A : Type'} (x : A) : term5 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem3817877 {A : Type'} (x : A) : (term5 A x) = (term6 A x).
Proof. exact (eq_refl (term5 A x)). Qed.
Lemma lem3817878 {A : Type'} (x : A) : term6 A x.
Proof. exact (EQ_MP (@lem3817877 A x) (@lem3817876 A x)). Qed.
Lemma lem3817879 {A : Type'} (x : A) (y : A) : term7 A x y.
Proof. exact (@lem3817878 A x y). Qed.
Lemma lem3817880 {A : Type'} (y : A) (x : A) : (term7 A x y) = (term8 A y x).
Proof. exact (eq_refl (term7 A x y)). Qed.
Lemma lem3817881 {A : Type'} (y : A) (x : A) : term8 A y x.
Proof. exact (EQ_MP (@lem3817880 A y x) (@lem3817879 A x y)). Qed.
Lemma lem3817882 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term9 A y x s.
Proof. exact (@lem3817881 A y x s). Qed.
Lemma lem3817883 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term9 A y x s) = ((term10 A x y s) = (term11 A y x s)).
Proof. exact (eq_refl (term9 A y x s)). Qed.
Lemma lem3817885 {A : Type'} (x : A) : term12 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem3817886 {A : Type'} (x : A) : (term12 A x) = (term13 A x).
Proof. exact (eq_refl (term12 A x)). Qed.
Lemma lem3817887 {A : Type'} (x : A) : term13 A x.
Proof. exact (EQ_MP (@lem3817886 A x) (@lem3817885 A x)). Qed.
Lemma lem3817888 {A : Type'} (x : A) : term14 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem3817890 {A B : Type'} (f : type1411 A B) : term15 A B f.
Proof. exact (@lem3816218 A B f). Qed.
Lemma lem3817891 {A B : Type'} (f : type1411 A B) : (term15 A B f) = (term16 A B f).
Proof. exact (eq_refl (term15 A B f)). Qed.
Lemma lem3817892 {A B : Type'} (f : type1411 A B) : term16 A B f.
Proof. exact (EQ_MP (@lem3817891 A B f) (@lem3817890 A B f)). Qed.
Lemma lem3817893 {A B : Type'} (f : type1411 A B) (b : B) : term17 A B f b.
Proof. exact (@lem3817892 A B f b). Qed.
Lemma lem3817894 {A B : Type'} (f : type1411 A B) (b : B) : (term17 A B f b) = (term18 A B f b).
Proof. exact (eq_refl (term17 A B f b)). Qed.
Lemma lem3817895 {A B : Type'} (f : type1411 A B) (b : B) : term18 A B f b.
Proof. exact (EQ_MP (@lem3817894 A B f b) (@lem3817893 A B f b)). Qed.
Lemma lem3817896 {A B : Type'} (f : type1411 A B) (h1 : term19 A B f) : term19 A B f.
Proof. exact (h1). Qed.
Lemma lem3817897 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term19 A B f) : term20 A B f b.
Proof. exact (@lem3817895 A B f b (@lem3817896 A B f h1)). Qed.
Lemma lem3817898 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term19 A B f) : term21 A B f b.
Proof. exact (proj2 (@lem3817897 A B b f h1)). Qed.
Lemma lem3817899 {A B : Type'} (b : B) (x : A) (f : type1411 A B) (h1 : term19 A B f) : term22 A B f b x.
Proof. exact (@lem3817898 A B b f h1 x). Qed.
Lemma lem3817900 {A B : Type'} (x : A) (f : type1411 A B) (b : B) : (term22 A B f b x) = (term23 A B x f b).
Proof. exact (eq_refl (term22 A B f b x)). Qed.
Lemma lem3817901 {A B : Type'} (x : A) (b : B) (f : type1411 A B) (h1 : term19 A B f) : term23 A B x f b.
Proof. exact (EQ_MP (@lem3817900 A B x f b) (@lem3817899 A B b x f h1)). Qed.
Lemma lem3817902 {A B : Type'} (x : A) (b : B) (s : A -> Prop) (f : type1411 A B) (h1 : term19 A B f) : term24 A B x f b s.
Proof. exact (@lem3817901 A B x b f h1 s). Qed.
Lemma lem3817903 {A B : Type'} (x : A) (f : type1411 A B) (s : A -> Prop) (b : B) : (term24 A B x f b s) = (term25 A B x f s b).
Proof. exact (eq_refl (term24 A B x f b s)). Qed.
Lemma lem3817904 {A B : Type'} (x : A) (s : A -> Prop) (b : B) (f : type1411 A B) (h1 : term19 A B f) : term25 A B x f s b.
Proof. exact (EQ_MP (@lem3817903 A B x f s b) (@lem3817902 A B x b s f h1)). Qed.
Lemma lem3817905 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3817906 {A B : Type'} (x : A) (b : B) (f : type1411 A B) (s : A -> Prop) (h1 : term19 A B f) (h2 : @FINITE A s) : (term26 A B f x s b) = (term27 A B x f s b).
Proof. exact (@lem3817904 A B x s b f h1 (@lem3817905 A s h2)). Qed.
Lemma lem3817907 {A B : Type'} (x : A) (s : A -> Prop) (b : B) (f : type1411 A B) (h1 : term19 A B f) : term25 A B x f s b.
Proof. exact (fun h0 : @FINITE A s => @lem3817906 A B x b f s h1 h0). Qed.
Lemma lem3817908 {A B : Type'} (x : A) (f : type1411 A B) (s : A -> Prop) (b : B) : term28 A B x f s b.
Proof. exact (fun h0 : term19 A B f => @lem3817907 A B x s b f h0). Qed.
Lemma lem3817910 (p : Prop) (q : Prop) (r : Prop) : (term29 p q r) = (term30 p q r).
Proof. exact (EQ_MP (@lem197 p q r) (@lem196 p q r)). Qed.
Lemma lem3817915 {A B : Type'} (x : A) (f : type1411 A B) (s : A -> Prop) (b : B) : (term28 A B x f s b) = (term31 A B x f s b).
Proof. exact (@lem3817910 (term19 A B f) (@FINITE A s) ((term26 A B f x s b) = (term27 A B x f s b))). Qed.
Lemma lem3817917 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term19 A B f) : (@ITSET B A f (@EMPTY A) b) = b.
Proof. exact (proj1 (@lem3817897 A B b f h1)). Qed.
Lemma lem3817923 {A : Type'} (h1 : term32 A) : term32 A.
Proof. exact (h1). Qed.
Lemma lem3817924 {A : Type'} (P : type686 A) (h1 : term32 A) : term33 A P.
Proof. exact (@lem3817923 A h1 P). Qed.
Lemma lem3817925 {A : Type'} (P : type686 A) : (term33 A P) = (term34 A P).
Proof. exact (eq_refl (term33 A P)). Qed.
Lemma lem3817926 {A : Type'} (P : type686 A) (h1 : term32 A) : term34 A P.
Proof. exact (EQ_MP (@lem3817925 A P) (@lem3817924 A P h1)). Qed.
Lemma lem3817927 {A : Type'} (P : type686 A) (h1 : term35 A P) : term35 A P.
Proof. exact (h1). Qed.
Lemma lem3817928 {A : Type'} (P : type686 A) (h1 : term32 A) (h2 : term35 A P) : term36 A P.
Proof. exact (@lem3817926 A P h1 (@lem3817927 A P h2)). Qed.
Lemma lem3817929 {A : Type'} (P : type686 A) (h1 : term35 A P) : term37 A P.
Proof. exact (fun h0 : term32 A => @lem3817928 A P h0 h1). Qed.
Lemma lem3817930 {A : Type'} (h1 : term32 A) : term32 A.
Proof. exact (h1). Qed.
Lemma lem3817931 {A : Type'} (P : type686 A) (h1 : term32 A) (h2 : term35 A P) : term36 A P.
Proof. exact (@lem3817929 A P h2 (@lem3817930 A h1)). Qed.
Lemma lem3817932 {A : Type'} (P : type686 A) (h1 : term32 A) : term34 A P.
Proof. exact (fun h0 : term35 A P => @lem3817931 A P h1 h0). Qed.
Lemma lem3817933 {A : Type'} (h1 : term32 A) : term32 A.
Proof. exact (fun P : type686 A => @lem3817932 A P h1). Qed.
Lemma lem3817934 {A : Type'} : term38 A.
Proof. exact (fun h0 : term32 A => @lem3817933 A h0). Qed.
Lemma lem3817935 {A : Type'} : term32 A.
Proof. exact (@lem3817934 A (@lem3558722 A)). Qed.
Lemma lem3817936 {A : Type'} (P : type686 A) : term33 A P.
Proof. exact (@lem3817935 A P). Qed.
Lemma lem3817937 {A : Type'} (P : type686 A) : (term33 A P) = (term34 A P).
Proof. exact (eq_refl (term33 A P)). Qed.
Lemma lem3817939 {A : Type'} (P : Prop) : term39 A P.
Proof. exact (@lem6534 A P). Qed.
Lemma lem3817940 {A : Type'} (P : Prop) : (term39 A P) = (term40 A P).
Proof. exact (eq_refl (term39 A P)). Qed.
Lemma lem3817941 {A : Type'} (P : Prop) : term40 A P.
Proof. exact (EQ_MP (@lem3817940 A P) (@lem3817939 A P)). Qed.
Lemma lem3817942 {A : Type'} (P : Prop) (Q : A -> Prop) : term41 A P Q.
Proof. exact (@lem3817941 A P Q). Qed.
Lemma lem3817943 {A : Type'} (P : Prop) (Q : A -> Prop) : (term41 A P Q) = ((term4 A P Q) = (term3 A P Q)).
Proof. exact (eq_refl (term41 A P Q)). Qed.
Lemma lem3817962 (p : Prop) (q : Prop) (r : Prop) : (term30 p q r) = (term29 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem3817963 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) (b : _99547) : (term42 _99546 _99547 f g s b) = (term43 _99546 _99547 f g s b).
Proof. exact (@lem3817962 (@FINITE _99546 s) (term44 _99546 _99547 s f g) ((@ITSET _99547 _99546 f s b) = (@ITSET _99547 _99546 g s b))). Qed.
Lemma lem3817964 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term45 _99546 _99547 f g s) = (term46 _99546 _99547 f g s).
Proof. exact (fun_ext (fun b : _99547 => @lem3817963 _99546 _99547 f g s b)). Qed.
Lemma lem3817965 {_99547 : Type'} : (@all _99547) = (@all _99547).
Proof. exact (eq_refl (@all _99547)). Qed.
Lemma lem3817966 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term47 _99546 _99547 f g s) = (term48 _99546 _99547 f g s).
Proof. exact (MK_COMB (@lem3817965 _99547) (@lem3817964 _99546 _99547 f g s)). Qed.
Lemma lem3817967 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term49 _99546 _99547 f s) = (term50 _99546 _99547 f s).
Proof. exact (fun_ext (fun g : type1411 _99546 _99547 => @lem3817966 _99546 _99547 f g s)). Qed.
Lemma lem3817968 {_99546 _99547 : Type'} : (@all (_99546 -> _99547 -> _99547)) = (@all (_99546 -> _99547 -> _99547)).
Proof. exact (eq_refl (@all (_99546 -> _99547 -> _99547))). Qed.
Lemma lem3817969 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term51 _99546 _99547 f s) = (term52 _99546 _99547 f s).
Proof. exact (MK_COMB (@lem3817968 _99546 _99547) (@lem3817967 _99546 _99547 f s)). Qed.
Lemma lem3817970 {_99546 _99547 : Type'} (s : _99546 -> Prop) : (term53 _99546 _99547 s) = (term54 _99546 _99547 s).
Proof. exact (fun_ext (fun f : type1411 _99546 _99547 => @lem3817969 _99546 _99547 f s)). Qed.
Lemma lem3817971 {_99546 _99547 : Type'} : (@all (_99546 -> _99547 -> _99547)) = (@all (_99546 -> _99547 -> _99547)).
Proof. exact (eq_refl (@all (_99546 -> _99547 -> _99547))). Qed.
Lemma lem3817972 {_99546 _99547 : Type'} (s : _99546 -> Prop) : (term55 _99546 _99547 s) = (term56 _99546 _99547 s).
Proof. exact (MK_COMB (@lem3817971 _99546 _99547) (@lem3817970 _99546 _99547 s)). Qed.
Lemma lem3817973 {_99546 _99547 : Type'} : (term57 _99546 _99547) = (term58 _99546 _99547).
Proof. exact (fun_ext (fun s : _99546 -> Prop => @lem3817972 _99546 _99547 s)). Qed.
Lemma lem3817974 {_99546 : Type'} : (@all (_99546 -> Prop)) = (@all (_99546 -> Prop)).
Proof. exact (eq_refl (@all (_99546 -> Prop))). Qed.
Lemma lem3817975 {_99546 _99547 : Type'} : (term59 _99546 _99547) = (term60 _99546 _99547).
Proof. exact (MK_COMB (@lem3817974 _99546) (@lem3817973 _99546 _99547)). Qed.
Lemma lem3817976 {_99546 _99547 : Type'} : (term60 _99546 _99547) = (term59 _99546 _99547).
Proof. exact (SYM (@lem3817975 _99546 _99547)). Qed.
Lemma lem3817990 {A : Type'} (P : Prop) (Q : A -> Prop) : (term4 A P Q) = (term3 A P Q).
Proof. exact (EQ_MP (@lem3817943 A P Q) (@lem3817942 A P Q)). Qed.
Lemma lem3817991 {_99547 : Type'} (P : Prop) (Q : _99547 -> Prop) : (term4 _99547 P Q) = (term3 _99547 P Q).
Proof. exact (@lem3817990 _99547 P Q). Qed.
Lemma lem3817992 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term61 _99546 _99547 f g s) = (term62 _99546 _99547 f g s).
Proof. exact (@lem3817991 _99547 (@FINITE _99546 s) (term63 _99546 _99547 f g s)). Qed.
Lemma lem3817993 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) (b : _99547) : (term64 _99546 _99547 f g s b) = (term65 _99546 _99547 f g s b).
Proof. exact (eq_refl (term64 _99546 _99547 f g s b)). Qed.
Lemma lem3817994 {_99546 : Type'} (s : _99546 -> Prop) : (term66 _99546 s) = (term66 _99546 s).
Proof. exact (eq_refl (term66 _99546 s)). Qed.
Lemma lem3817995 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) (b : _99547) : (term67 _99546 _99547 f g s b) = (term43 _99546 _99547 f g s b).
Proof. exact (MK_COMB (@lem3817994 _99546 s) (@lem3817993 _99546 _99547 f g s b)). Qed.
Lemma lem3817996 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term68 _99546 _99547 f g s) = (term46 _99546 _99547 f g s).
Proof. exact (fun_ext (fun b : _99547 => @lem3817995 _99546 _99547 f g s b)). Qed.
Lemma lem3817997 {_99547 : Type'} : (@all _99547) = (@all _99547).
Proof. exact (eq_refl (@all _99547)). Qed.
Lemma lem3817998 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term61 _99546 _99547 f g s) = (term48 _99546 _99547 f g s).
Proof. exact (MK_COMB (@lem3817997 _99547) (@lem3817996 _99546 _99547 f g s)). Qed.
Lemma lem3817999 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3818000 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term69 _99546 _99547 f g s) = (term70 _99546 _99547 f g s).
Proof. exact (MK_COMB (@lem3817999) (@lem3817998 _99546 _99547 f g s)). Qed.
Lemma lem3818001 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) (b : _99547) : (term64 _99546 _99547 f g s b) = (term65 _99546 _99547 f g s b).
Proof. exact (eq_refl (term64 _99546 _99547 f g s b)). Qed.
Lemma lem3818002 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term71 _99546 _99547 f g s) = (term63 _99546 _99547 f g s).
Proof. exact (fun_ext (fun b : _99547 => @lem3818001 _99546 _99547 f g s b)). Qed.
Lemma lem3818003 {_99547 : Type'} : (@all _99547) = (@all _99547).
Proof. exact (eq_refl (@all _99547)). Qed.
Lemma lem3818004 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term72 _99546 _99547 f g s) = (term73 _99546 _99547 f g s).
Proof. exact (MK_COMB (@lem3818003 _99547) (@lem3818002 _99546 _99547 f g s)). Qed.
Lemma lem3818005 {_99546 : Type'} (s : _99546 -> Prop) : (term66 _99546 s) = (term66 _99546 s).
Proof. exact (eq_refl (term66 _99546 s)). Qed.
Lemma lem3818006 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term62 _99546 _99547 f g s) = (term74 _99546 _99547 f g s).
Proof. exact (MK_COMB (@lem3818005 _99546 s) (@lem3818004 _99546 _99547 f g s)). Qed.
Lemma lem3818007 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : ((term61 _99546 _99547 f g s) = (term62 _99546 _99547 f g s)) = ((term48 _99546 _99547 f g s) = (term74 _99546 _99547 f g s)).
Proof. exact (MK_COMB (@lem3818000 _99546 _99547 f g s) (@lem3818006 _99546 _99547 f g s)). Qed.
Lemma lem3818008 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term48 _99546 _99547 f g s) = (term74 _99546 _99547 f g s).
Proof. exact (EQ_MP (@lem3818007 _99546 _99547 f g s) (@lem3817992 _99546 _99547 f g s)). Qed.
Lemma lem3818012 {A : Type'} (P : Prop) (Q : A -> Prop) : (term4 A P Q) = (term3 A P Q).
Proof. exact (EQ_MP (@lem3817943 A P Q) (@lem3817942 A P Q)). Qed.
Lemma lem3818013 {_99547 : Type'} (P : Prop) (Q : _99547 -> Prop) : (term4 _99547 P Q) = (term3 _99547 P Q).
Proof. exact (@lem3818012 _99547 P Q). Qed.
Lemma lem3818014 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term75 _99546 _99547 f g s) = (term76 _99546 _99547 f g s).
Proof. exact (@lem3818013 _99547 (term44 _99546 _99547 s f g) (term77 _99546 _99547 f g s)). Qed.
Lemma lem3818015 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) (b : _99547) : (term78 _99546 _99547 f g s b) = ((@ITSET _99547 _99546 f s b) = (@ITSET _99547 _99546 g s b)).
Proof. exact (eq_refl (term78 _99546 _99547 f g s b)). Qed.
Lemma lem3818016 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term79 _99546 _99547 s f g) = (term79 _99546 _99547 s f g).
Proof. exact (eq_refl (term79 _99546 _99547 s f g)). Qed.
Lemma lem3818017 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) (b : _99547) : (term80 _99546 _99547 f g s b) = (term65 _99546 _99547 f g s b).
Proof. exact (MK_COMB (@lem3818016 _99546 _99547 s f g) (@lem3818015 _99546 _99547 f g s b)). Qed.
Lemma lem3818018 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term81 _99546 _99547 f g s) = (term63 _99546 _99547 f g s).
Proof. exact (fun_ext (fun b : _99547 => @lem3818017 _99546 _99547 f g s b)). Qed.
Lemma lem3818019 {_99547 : Type'} : (@all _99547) = (@all _99547).
Proof. exact (eq_refl (@all _99547)). Qed.
Lemma lem3818020 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term75 _99546 _99547 f g s) = (term73 _99546 _99547 f g s).
Proof. exact (MK_COMB (@lem3818019 _99547) (@lem3818018 _99546 _99547 f g s)). Qed.
Lemma lem3818021 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3818022 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term82 _99546 _99547 f g s) = (term83 _99546 _99547 f g s).
Proof. exact (MK_COMB (@lem3818021) (@lem3818020 _99546 _99547 f g s)). Qed.
Lemma lem3818023 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) (b : _99547) : (term78 _99546 _99547 f g s b) = ((@ITSET _99547 _99546 f s b) = (@ITSET _99547 _99546 g s b)).
Proof. exact (eq_refl (term78 _99546 _99547 f g s b)). Qed.
Lemma lem3818024 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term84 _99546 _99547 f g s) = (term77 _99546 _99547 f g s).
Proof. exact (fun_ext (fun b : _99547 => @lem3818023 _99546 _99547 f g s b)). Qed.
Lemma lem3818025 {_99547 : Type'} : (@all _99547) = (@all _99547).
Proof. exact (eq_refl (@all _99547)). Qed.
Lemma lem3818026 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term85 _99546 _99547 f g s) = (term86 _99546 _99547 f g s).
Proof. exact (MK_COMB (@lem3818025 _99547) (@lem3818024 _99546 _99547 f g s)). Qed.
Lemma lem3818027 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term79 _99546 _99547 s f g) = (term79 _99546 _99547 s f g).
Proof. exact (eq_refl (term79 _99546 _99547 s f g)). Qed.
Lemma lem3818028 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term76 _99546 _99547 f g s) = (term87 _99546 _99547 f g s).
Proof. exact (MK_COMB (@lem3818027 _99546 _99547 s f g) (@lem3818026 _99546 _99547 f g s)). Qed.
Lemma lem3818029 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : ((term75 _99546 _99547 f g s) = (term76 _99546 _99547 f g s)) = ((term73 _99546 _99547 f g s) = (term87 _99546 _99547 f g s)).
Proof. exact (MK_COMB (@lem3818022 _99546 _99547 f g s) (@lem3818028 _99546 _99547 f g s)). Qed.
Lemma lem3818030 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term73 _99546 _99547 f g s) = (term87 _99546 _99547 f g s).
Proof. exact (EQ_MP (@lem3818029 _99546 _99547 f g s) (@lem3818014 _99546 _99547 f g s)). Qed.
Lemma lem3818074 {A : Type'} (P : Prop) (Q : A -> Prop) : (term4 A P Q) = (term3 A P Q).
Proof. exact (EQ_MP (@lem3817943 A P Q) (@lem3817942 A P Q)). Qed.
Lemma lem3818075 {_99547 : Type'} (P : Prop) (Q : _99547 -> Prop) : (term4 _99547 P Q) = (term3 _99547 P Q).
Proof. exact (@lem3818074 _99547 P Q). Qed.
Lemma lem3818076 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term88 _99546 _99547 y f x) = (term89 _99546 _99547 y f x).
Proof. exact (@lem3818075 _99547 (term90 _99546 x y) (term91 _99546 _99547 y f x)). Qed.
Lemma lem3818077 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term92 _99546 _99547 y f x s) = ((term93 _99546 _99547 x f y s) = (term93 _99546 _99547 y f x s)).
Proof. exact (eq_refl (term92 _99546 _99547 y f x s)). Qed.
Lemma lem3818078 {_99546 : Type'} (x : _99546) (y : _99546) : (term94 _99546 x y) = (term94 _99546 x y).
Proof. exact (eq_refl (term94 _99546 x y)). Qed.
Lemma lem3818079 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term95 _99546 _99547 y f x s) = (term96 _99546 _99547 y f x s).
Proof. exact (MK_COMB (@lem3818078 _99546 x y) (@lem3818077 _99546 _99547 y f x s)). Qed.
Lemma lem3818080 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term97 _99546 _99547 y f x) = (term98 _99546 _99547 y f x).
Proof. exact (fun_ext (fun s : _99547 => @lem3818079 _99546 _99547 y f x s)). Qed.
Lemma lem3818081 {_99547 : Type'} : (@all _99547) = (@all _99547).
Proof. exact (eq_refl (@all _99547)). Qed.
Lemma lem3818082 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term88 _99546 _99547 y f x) = (term99 _99546 _99547 y f x).
Proof. exact (MK_COMB (@lem3818081 _99547) (@lem3818080 _99546 _99547 y f x)). Qed.
Lemma lem3818083 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3818084 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term100 _99546 _99547 y f x) = (term101 _99546 _99547 y f x).
Proof. exact (MK_COMB (@lem3818083) (@lem3818082 _99546 _99547 y f x)). Qed.
Lemma lem3818085 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term92 _99546 _99547 y f x s) = ((term93 _99546 _99547 x f y s) = (term93 _99546 _99547 y f x s)).
Proof. exact (eq_refl (term92 _99546 _99547 y f x s)). Qed.
Lemma lem3818086 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term102 _99546 _99547 y f x) = (term91 _99546 _99547 y f x).
Proof. exact (fun_ext (fun s : _99547 => @lem3818085 _99546 _99547 y f x s)). Qed.
Lemma lem3818087 {_99547 : Type'} : (@all _99547) = (@all _99547).
Proof. exact (eq_refl (@all _99547)). Qed.
Lemma lem3818088 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term103 _99546 _99547 y f x) = (term104 _99546 _99547 y f x).
Proof. exact (MK_COMB (@lem3818087 _99547) (@lem3818086 _99546 _99547 y f x)). Qed.
Lemma lem3818089 {_99546 : Type'} (x : _99546) (y : _99546) : (term94 _99546 x y) = (term94 _99546 x y).
Proof. exact (eq_refl (term94 _99546 x y)). Qed.
Lemma lem3818090 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term89 _99546 _99547 y f x) = (term105 _99546 _99547 y f x).
Proof. exact (MK_COMB (@lem3818089 _99546 x y) (@lem3818088 _99546 _99547 y f x)). Qed.
Lemma lem3818091 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : ((term88 _99546 _99547 y f x) = (term89 _99546 _99547 y f x)) = ((term99 _99546 _99547 y f x) = (term105 _99546 _99547 y f x)).
Proof. exact (MK_COMB (@lem3818084 _99546 _99547 y f x) (@lem3818090 _99546 _99547 y f x)). Qed.
Lemma lem3818092 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term99 _99546 _99547 y f x) = (term105 _99546 _99547 y f x).
Proof. exact (EQ_MP (@lem3818091 _99546 _99547 y f x) (@lem3818076 _99546 _99547 y f x)). Qed.
Lemma lem3818103 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (term106 _99546 _99547 f x) = (term107 _99546 _99547 f x).
Proof. exact (fun_ext (fun y : _99546 => @lem3818092 _99546 _99547 y f x)). Qed.
Lemma lem3818104 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3818105 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (term108 _99546 _99547 f x) = (term109 _99546 _99547 f x).
Proof. exact (MK_COMB (@lem3818104 _99546) (@lem3818103 _99546 _99547 f x)). Qed.
Lemma lem3818130 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term110 _99546 _99547 f) = (term111 _99546 _99547 f).
Proof. exact (fun_ext (fun x : _99546 => @lem3818105 _99546 _99547 f x)). Qed.
Lemma lem3818131 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3818132 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term19 _99546 _99547 f) = (term112 _99546 _99547 f).
Proof. exact (MK_COMB (@lem3818131 _99546) (@lem3818130 _99546 _99547 f)). Qed.
Lemma lem3818137 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3818138 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term113 _99546 _99547 f) = (term114 _99546 _99547 f).
Proof. exact (MK_COMB (@lem3818137) (@lem3818132 _99546 _99547 f)). Qed.
Lemma lem3818148 {A : Type'} (P : Prop) (Q : A -> Prop) : (term4 A P Q) = (term3 A P Q).
Proof. exact (EQ_MP (@lem3817943 A P Q) (@lem3817942 A P Q)). Qed.
Lemma lem3818149 {_99547 : Type'} (P : Prop) (Q : _99547 -> Prop) : (term4 _99547 P Q) = (term3 _99547 P Q).
Proof. exact (@lem3818148 _99547 P Q). Qed.
Lemma lem3818150 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term88 _99546 _99547 y g x) = (term89 _99546 _99547 y g x).
Proof. exact (@lem3818149 _99547 (term90 _99546 x y) (term91 _99546 _99547 y g x)). Qed.
Lemma lem3818151 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term92 _99546 _99547 y g x s) = ((term93 _99546 _99547 x g y s) = (term93 _99546 _99547 y g x s)).
Proof. exact (eq_refl (term92 _99546 _99547 y g x s)). Qed.
Lemma lem3818152 {_99546 : Type'} (x : _99546) (y : _99546) : (term94 _99546 x y) = (term94 _99546 x y).
Proof. exact (eq_refl (term94 _99546 x y)). Qed.
Lemma lem3818153 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term95 _99546 _99547 y g x s) = (term96 _99546 _99547 y g x s).
Proof. exact (MK_COMB (@lem3818152 _99546 x y) (@lem3818151 _99546 _99547 y g x s)). Qed.
Lemma lem3818154 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term97 _99546 _99547 y g x) = (term98 _99546 _99547 y g x).
Proof. exact (fun_ext (fun s : _99547 => @lem3818153 _99546 _99547 y g x s)). Qed.
Lemma lem3818155 {_99547 : Type'} : (@all _99547) = (@all _99547).
Proof. exact (eq_refl (@all _99547)). Qed.
Lemma lem3818156 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term88 _99546 _99547 y g x) = (term99 _99546 _99547 y g x).
Proof. exact (MK_COMB (@lem3818155 _99547) (@lem3818154 _99546 _99547 y g x)). Qed.
Lemma lem3818157 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3818158 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term100 _99546 _99547 y g x) = (term101 _99546 _99547 y g x).
Proof. exact (MK_COMB (@lem3818157) (@lem3818156 _99546 _99547 y g x)). Qed.
Lemma lem3818159 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term92 _99546 _99547 y g x s) = ((term93 _99546 _99547 x g y s) = (term93 _99546 _99547 y g x s)).
Proof. exact (eq_refl (term92 _99546 _99547 y g x s)). Qed.
Lemma lem3818160 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term102 _99546 _99547 y g x) = (term91 _99546 _99547 y g x).
Proof. exact (fun_ext (fun s : _99547 => @lem3818159 _99546 _99547 y g x s)). Qed.
Lemma lem3818161 {_99547 : Type'} : (@all _99547) = (@all _99547).
Proof. exact (eq_refl (@all _99547)). Qed.
Lemma lem3818162 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term103 _99546 _99547 y g x) = (term104 _99546 _99547 y g x).
Proof. exact (MK_COMB (@lem3818161 _99547) (@lem3818160 _99546 _99547 y g x)). Qed.
Lemma lem3818163 {_99546 : Type'} (x : _99546) (y : _99546) : (term94 _99546 x y) = (term94 _99546 x y).
Proof. exact (eq_refl (term94 _99546 x y)). Qed.
Lemma lem3818164 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term89 _99546 _99547 y g x) = (term105 _99546 _99547 y g x).
Proof. exact (MK_COMB (@lem3818163 _99546 x y) (@lem3818162 _99546 _99547 y g x)). Qed.
Lemma lem3818165 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : ((term88 _99546 _99547 y g x) = (term89 _99546 _99547 y g x)) = ((term99 _99546 _99547 y g x) = (term105 _99546 _99547 y g x)).
Proof. exact (MK_COMB (@lem3818158 _99546 _99547 y g x) (@lem3818164 _99546 _99547 y g x)). Qed.
Lemma lem3818166 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term99 _99546 _99547 y g x) = (term105 _99546 _99547 y g x).
Proof. exact (EQ_MP (@lem3818165 _99546 _99547 y g x) (@lem3818150 _99546 _99547 y g x)). Qed.
Lemma lem3818177 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) : (term106 _99546 _99547 g x) = (term107 _99546 _99547 g x).
Proof. exact (fun_ext (fun y : _99546 => @lem3818166 _99546 _99547 y g x)). Qed.
Lemma lem3818178 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3818179 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) : (term108 _99546 _99547 g x) = (term109 _99546 _99547 g x).
Proof. exact (MK_COMB (@lem3818178 _99546) (@lem3818177 _99546 _99547 g x)). Qed.
Lemma lem3818204 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) : (term110 _99546 _99547 g) = (term111 _99546 _99547 g).
Proof. exact (fun_ext (fun x : _99546 => @lem3818179 _99546 _99547 g x)). Qed.
Lemma lem3818205 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3818206 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) : (term19 _99546 _99547 g) = (term112 _99546 _99547 g).
Proof. exact (MK_COMB (@lem3818205 _99546) (@lem3818204 _99546 _99547 g)). Qed.
Lemma lem3818211 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term115 _99546 _99547 f g) = (term116 _99546 _99547 f g).
Proof. exact (MK_COMB (@lem3818138 _99546 _99547 f) (@lem3818206 _99546 _99547 g)). Qed.
Lemma lem3818214 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term117 _99546 _99547 s f g) = (term117 _99546 _99547 s f g).
Proof. exact (eq_refl (term117 _99546 _99547 s f g)). Qed.
Lemma lem3818215 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term44 _99546 _99547 s f g) = (term118 _99546 _99547 s f g).
Proof. exact (MK_COMB (@lem3818214 _99546 _99547 s f g) (@lem3818211 _99546 _99547 f g)). Qed.
Lemma lem3818218 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3818219 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term79 _99546 _99547 s f g) = (term119 _99546 _99547 s f g).
Proof. exact (MK_COMB (@lem3818218) (@lem3818215 _99546 _99547 s f g)). Qed.
Lemma lem3818226 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term86 _99546 _99547 f g s) = (term86 _99546 _99547 f g s).
Proof. exact (eq_refl (term86 _99546 _99547 f g s)). Qed.
Lemma lem3818227 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term87 _99546 _99547 f g s) = (term120 _99546 _99547 f g s).
Proof. exact (MK_COMB (@lem3818219 _99546 _99547 s f g) (@lem3818226 _99546 _99547 f g s)). Qed.
Lemma lem3818230 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term73 _99546 _99547 f g s) = (term120 _99546 _99547 f g s).
Proof. exact (TRANS (@lem3818030 _99546 _99547 f g s) (@lem3818227 _99546 _99547 f g s)). Qed.
Lemma lem3818231 {_99546 : Type'} (s : _99546 -> Prop) : (term66 _99546 s) = (term66 _99546 s).
Proof. exact (eq_refl (term66 _99546 s)). Qed.
Lemma lem3818232 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term74 _99546 _99547 f g s) = (term121 _99546 _99547 f g s).
Proof. exact (MK_COMB (@lem3818231 _99546 s) (@lem3818230 _99546 _99547 f g s)). Qed.
Lemma lem3818235 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term48 _99546 _99547 f g s) = (term121 _99546 _99547 f g s).
Proof. exact (TRANS (@lem3818008 _99546 _99547 f g s) (@lem3818232 _99546 _99547 f g s)). Qed.
Lemma lem3818236 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term50 _99546 _99547 f s) = (term122 _99546 _99547 f s).
Proof. exact (fun_ext (fun g : type1411 _99546 _99547 => @lem3818235 _99546 _99547 f g s)). Qed.
Lemma lem3818237 {_99546 _99547 : Type'} : (@all (_99546 -> _99547 -> _99547)) = (@all (_99546 -> _99547 -> _99547)).
Proof. exact (eq_refl (@all (_99546 -> _99547 -> _99547))). Qed.
Lemma lem3818238 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term52 _99546 _99547 f s) = (term123 _99546 _99547 f s).
Proof. exact (MK_COMB (@lem3818237 _99546 _99547) (@lem3818236 _99546 _99547 f s)). Qed.
Lemma lem3818240 {A : Type'} (P : Prop) (Q : A -> Prop) : (term4 A P Q) = (term3 A P Q).
Proof. exact (EQ_MP (@lem3817943 A P Q) (@lem3817942 A P Q)). Qed.
Lemma lem3818241 {_99546 _99547 : Type'} (P : Prop) (Q : type436 _99546 _99547) : (term124 _99546 _99547 P Q) = (term125 _99546 _99547 P Q).
Proof. exact (@lem3818240 (type1411 _99546 _99547) P Q). Qed.
Lemma lem3818242 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term126 _99546 _99547 f s) = (term127 _99546 _99547 f s).
Proof. exact (@lem3818241 _99546 _99547 (@FINITE _99546 s) (term128 _99546 _99547 f s)). Qed.
Lemma lem3818243 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term129 _99546 _99547 f s g) = (term120 _99546 _99547 f g s).
Proof. exact (eq_refl (term129 _99546 _99547 f s g)). Qed.
Lemma lem3818244 {_99546 : Type'} (s : _99546 -> Prop) : (term66 _99546 s) = (term66 _99546 s).
Proof. exact (eq_refl (term66 _99546 s)). Qed.
Lemma lem3818245 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term130 _99546 _99547 f s g) = (term121 _99546 _99547 f g s).
Proof. exact (MK_COMB (@lem3818244 _99546 s) (@lem3818243 _99546 _99547 f g s)). Qed.
Lemma lem3818246 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term131 _99546 _99547 f s) = (term122 _99546 _99547 f s).
Proof. exact (fun_ext (fun g : type1411 _99546 _99547 => @lem3818245 _99546 _99547 f g s)). Qed.
Lemma lem3818247 {_99546 _99547 : Type'} : (@all (_99546 -> _99547 -> _99547)) = (@all (_99546 -> _99547 -> _99547)).
Proof. exact (eq_refl (@all (_99546 -> _99547 -> _99547))). Qed.
Lemma lem3818248 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term126 _99546 _99547 f s) = (term123 _99546 _99547 f s).
Proof. exact (MK_COMB (@lem3818247 _99546 _99547) (@lem3818246 _99546 _99547 f s)). Qed.
Lemma lem3818249 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3818250 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term132 _99546 _99547 f s) = (term133 _99546 _99547 f s).
Proof. exact (MK_COMB (@lem3818249) (@lem3818248 _99546 _99547 f s)). Qed.
Lemma lem3818251 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term129 _99546 _99547 f s g) = (term120 _99546 _99547 f g s).
Proof. exact (eq_refl (term129 _99546 _99547 f s g)). Qed.
Lemma lem3818252 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term134 _99546 _99547 f s) = (term128 _99546 _99547 f s).
Proof. exact (fun_ext (fun g : type1411 _99546 _99547 => @lem3818251 _99546 _99547 f g s)). Qed.
Lemma lem3818253 {_99546 _99547 : Type'} : (@all (_99546 -> _99547 -> _99547)) = (@all (_99546 -> _99547 -> _99547)).
Proof. exact (eq_refl (@all (_99546 -> _99547 -> _99547))). Qed.
Lemma lem3818254 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term135 _99546 _99547 f s) = (term136 _99546 _99547 f s).
Proof. exact (MK_COMB (@lem3818253 _99546 _99547) (@lem3818252 _99546 _99547 f s)). Qed.
Lemma lem3818255 {_99546 : Type'} (s : _99546 -> Prop) : (term66 _99546 s) = (term66 _99546 s).
Proof. exact (eq_refl (term66 _99546 s)). Qed.
Lemma lem3818256 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term127 _99546 _99547 f s) = (term137 _99546 _99547 f s).
Proof. exact (MK_COMB (@lem3818255 _99546 s) (@lem3818254 _99546 _99547 f s)). Qed.
Lemma lem3818257 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) : ((term126 _99546 _99547 f s) = (term127 _99546 _99547 f s)) = ((term123 _99546 _99547 f s) = (term137 _99546 _99547 f s)).
Proof. exact (MK_COMB (@lem3818250 _99546 _99547 f s) (@lem3818256 _99546 _99547 f s)). Qed.
Lemma lem3818258 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term123 _99546 _99547 f s) = (term137 _99546 _99547 f s).
Proof. exact (EQ_MP (@lem3818257 _99546 _99547 f s) (@lem3818242 _99546 _99547 f s)). Qed.
Lemma lem3818401 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term52 _99546 _99547 f s) = (term137 _99546 _99547 f s).
Proof. exact (TRANS (@lem3818238 _99546 _99547 f s) (@lem3818258 _99546 _99547 f s)). Qed.
Lemma lem3818402 {_99546 _99547 : Type'} (s : _99546 -> Prop) : (term54 _99546 _99547 s) = (term138 _99546 _99547 s).
Proof. exact (fun_ext (fun f : type1411 _99546 _99547 => @lem3818401 _99546 _99547 f s)). Qed.
Lemma lem3818403 {_99546 _99547 : Type'} : (@all (_99546 -> _99547 -> _99547)) = (@all (_99546 -> _99547 -> _99547)).
Proof. exact (eq_refl (@all (_99546 -> _99547 -> _99547))). Qed.
Lemma lem3818404 {_99546 _99547 : Type'} (s : _99546 -> Prop) : (term56 _99546 _99547 s) = (term139 _99546 _99547 s).
Proof. exact (MK_COMB (@lem3818403 _99546 _99547) (@lem3818402 _99546 _99547 s)). Qed.
Lemma lem3818406 {A : Type'} (P : Prop) (Q : A -> Prop) : (term4 A P Q) = (term3 A P Q).
Proof. exact (EQ_MP (@lem3817943 A P Q) (@lem3817942 A P Q)). Qed.
Lemma lem3818407 {_99546 _99547 : Type'} (P : Prop) (Q : type436 _99546 _99547) : (term124 _99546 _99547 P Q) = (term125 _99546 _99547 P Q).
Proof. exact (@lem3818406 (type1411 _99546 _99547) P Q). Qed.
Lemma lem3818408 {_99546 _99547 : Type'} (s : _99546 -> Prop) : (term140 _99546 _99547 s) = (term141 _99546 _99547 s).
Proof. exact (@lem3818407 _99546 _99547 (@FINITE _99546 s) (term142 _99546 _99547 s)). Qed.
Lemma lem3818409 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term143 _99546 _99547 s f) = (term136 _99546 _99547 f s).
Proof. exact (eq_refl (term143 _99546 _99547 s f)). Qed.
Lemma lem3818410 {_99546 : Type'} (s : _99546 -> Prop) : (term66 _99546 s) = (term66 _99546 s).
Proof. exact (eq_refl (term66 _99546 s)). Qed.
Lemma lem3818411 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term144 _99546 _99547 s f) = (term137 _99546 _99547 f s).
Proof. exact (MK_COMB (@lem3818410 _99546 s) (@lem3818409 _99546 _99547 f s)). Qed.
Lemma lem3818412 {_99546 _99547 : Type'} (s : _99546 -> Prop) : (term145 _99546 _99547 s) = (term138 _99546 _99547 s).
Proof. exact (fun_ext (fun f : type1411 _99546 _99547 => @lem3818411 _99546 _99547 f s)). Qed.
Lemma lem3818413 {_99546 _99547 : Type'} : (@all (_99546 -> _99547 -> _99547)) = (@all (_99546 -> _99547 -> _99547)).
Proof. exact (eq_refl (@all (_99546 -> _99547 -> _99547))). Qed.
Lemma lem3818414 {_99546 _99547 : Type'} (s : _99546 -> Prop) : (term140 _99546 _99547 s) = (term139 _99546 _99547 s).
Proof. exact (MK_COMB (@lem3818413 _99546 _99547) (@lem3818412 _99546 _99547 s)). Qed.
Lemma lem3818415 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3818416 {_99546 _99547 : Type'} (s : _99546 -> Prop) : (term146 _99546 _99547 s) = (term147 _99546 _99547 s).
Proof. exact (MK_COMB (@lem3818415) (@lem3818414 _99546 _99547 s)). Qed.
Lemma lem3818417 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term143 _99546 _99547 s f) = (term136 _99546 _99547 f s).
Proof. exact (eq_refl (term143 _99546 _99547 s f)). Qed.
Lemma lem3818418 {_99546 _99547 : Type'} (s : _99546 -> Prop) : (term148 _99546 _99547 s) = (term142 _99546 _99547 s).
Proof. exact (fun_ext (fun f : type1411 _99546 _99547 => @lem3818417 _99546 _99547 f s)). Qed.
Lemma lem3818419 {_99546 _99547 : Type'} : (@all (_99546 -> _99547 -> _99547)) = (@all (_99546 -> _99547 -> _99547)).
Proof. exact (eq_refl (@all (_99546 -> _99547 -> _99547))). Qed.
Lemma lem3818420 {_99546 _99547 : Type'} (s : _99546 -> Prop) : (term149 _99546 _99547 s) = (term150 _99546 _99547 s).
Proof. exact (MK_COMB (@lem3818419 _99546 _99547) (@lem3818418 _99546 _99547 s)). Qed.
Lemma lem3818421 {_99546 : Type'} (s : _99546 -> Prop) : (term66 _99546 s) = (term66 _99546 s).
Proof. exact (eq_refl (term66 _99546 s)). Qed.
Lemma lem3818422 {_99546 _99547 : Type'} (s : _99546 -> Prop) : (term141 _99546 _99547 s) = (term151 _99546 _99547 s).
Proof. exact (MK_COMB (@lem3818421 _99546 s) (@lem3818420 _99546 _99547 s)). Qed.
Lemma lem3818423 {_99546 _99547 : Type'} (s : _99546 -> Prop) : ((term140 _99546 _99547 s) = (term141 _99546 _99547 s)) = ((term139 _99546 _99547 s) = (term151 _99546 _99547 s)).
Proof. exact (MK_COMB (@lem3818416 _99546 _99547 s) (@lem3818422 _99546 _99547 s)). Qed.
Lemma lem3818424 {_99546 _99547 : Type'} (s : _99546 -> Prop) : (term139 _99546 _99547 s) = (term151 _99546 _99547 s).
Proof. exact (EQ_MP (@lem3818423 _99546 _99547 s) (@lem3818408 _99546 _99547 s)). Qed.
Lemma lem3818571 {_99546 _99547 : Type'} (s : _99546 -> Prop) : (term56 _99546 _99547 s) = (term151 _99546 _99547 s).
Proof. exact (TRANS (@lem3818404 _99546 _99547 s) (@lem3818424 _99546 _99547 s)). Qed.
Lemma lem3818572 {_99546 _99547 : Type'} : (term58 _99546 _99547) = (term152 _99546 _99547).
Proof. exact (fun_ext (fun s : _99546 -> Prop => @lem3818571 _99546 _99547 s)). Qed.
Lemma lem3818573 {_99546 : Type'} : (@all (_99546 -> Prop)) = (@all (_99546 -> Prop)).
Proof. exact (eq_refl (@all (_99546 -> Prop))). Qed.
Lemma lem3818574 {_99546 _99547 : Type'} : (term60 _99546 _99547) = (term153 _99546 _99547).
Proof. exact (MK_COMB (@lem3818573 _99546) (@lem3818572 _99546 _99547)). Qed.
Lemma lem3818599 {_99546 _99547 : Type'} : (term153 _99546 _99547) = (term60 _99546 _99547).
Proof. exact (SYM (@lem3818574 _99546 _99547)). Qed.
Lemma lem3818601 {A : Type'} (P : type686 A) : term34 A P.
Proof. exact (EQ_MP (@lem3817937 A P) (@lem3817936 A P)). Qed.
Lemma lem3818602 {_99546 : Type'} (P : type686 _99546) : term34 _99546 P.
Proof. exact (@lem3818601 _99546 P). Qed.
Lemma lem3818603 {_99546 _99547 : Type'} : term154 _99546 _99547.
Proof. exact (@lem3818602 _99546 (term155 _99546 _99547)). Qed.
Lemma lem3818604 {_99546 _99547 : Type'} : (term156 _99546 _99547) = (term157 _99546 _99547).
Proof. exact (eq_refl (term156 _99546 _99547)). Qed.
Lemma lem3818605 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3818606 {_99546 _99547 : Type'} : (term158 _99546 _99547) = (term159 _99546 _99547).
Proof. exact (MK_COMB (@lem3818605) (@lem3818604 _99546 _99547)). Qed.
Lemma lem3818607 {_99546 _99547 : Type'} (s : _99546 -> Prop) : (term160 _99546 _99547 s) = (term150 _99546 _99547 s).
Proof. exact (eq_refl (term160 _99546 _99547 s)). Qed.
Lemma lem3818608 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3818609 {_99546 _99547 : Type'} (s : _99546 -> Prop) : (term161 _99546 _99547 s) = (term162 _99546 _99547 s).
Proof. exact (MK_COMB (@lem3818608) (@lem3818607 _99546 _99547 s)). Qed.
Lemma lem3818610 {_99546 : Type'} (x : _99546) (s : _99546 -> Prop) : (term163 _99546 x s) = (term163 _99546 x s).
Proof. exact (eq_refl (term163 _99546 x s)). Qed.
Lemma lem3818611 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) : (term164 _99546 _99547 x s) = (term165 _99546 _99547 x s).
Proof. exact (MK_COMB (@lem3818609 _99546 _99547 s) (@lem3818610 _99546 x s)). Qed.
Lemma lem3818612 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3818613 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) : (term166 _99546 _99547 x s) = (term167 _99546 _99547 x s).
Proof. exact (MK_COMB (@lem3818612) (@lem3818611 _99546 _99547 x s)). Qed.
Lemma lem3818614 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) : (term168 _99546 _99547 x s) = (term169 _99546 _99547 x s).
Proof. exact (eq_refl (term168 _99546 _99547 x s)). Qed.
Lemma lem3818615 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) : (term170 _99546 _99547 x s) = (term171 _99546 _99547 x s).
Proof. exact (MK_COMB (@lem3818613 _99546 _99547 x s) (@lem3818614 _99546 _99547 x s)). Qed.
Lemma lem3818616 {_99546 _99547 : Type'} (x : _99546) : (term172 _99546 _99547 x) = (term173 _99546 _99547 x).
Proof. exact (fun_ext (fun s : _99546 -> Prop => @lem3818615 _99546 _99547 x s)). Qed.
Lemma lem3818617 {_99546 : Type'} : (@all (_99546 -> Prop)) = (@all (_99546 -> Prop)).
Proof. exact (eq_refl (@all (_99546 -> Prop))). Qed.
Lemma lem3818618 {_99546 _99547 : Type'} (x : _99546) : (term174 _99546 _99547 x) = (term175 _99546 _99547 x).
Proof. exact (MK_COMB (@lem3818617 _99546) (@lem3818616 _99546 _99547 x)). Qed.
Lemma lem3818619 {_99546 _99547 : Type'} : (term176 _99546 _99547) = (term177 _99546 _99547).
Proof. exact (fun_ext (fun x : _99546 => @lem3818618 _99546 _99547 x)). Qed.
Lemma lem3818620 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3818621 {_99546 _99547 : Type'} : (term178 _99546 _99547) = (term179 _99546 _99547).
Proof. exact (MK_COMB (@lem3818620 _99546) (@lem3818619 _99546 _99547)). Qed.
Lemma lem3818622 {_99546 _99547 : Type'} : (term180 _99546 _99547) = (term181 _99546 _99547).
Proof. exact (MK_COMB (@lem3818606 _99546 _99547) (@lem3818621 _99546 _99547)). Qed.
Lemma lem3818623 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3818624 {_99546 _99547 : Type'} : (term182 _99546 _99547) = (term183 _99546 _99547).
Proof. exact (MK_COMB (@lem3818623) (@lem3818622 _99546 _99547)). Qed.
Lemma lem3818625 {_99546 _99547 : Type'} (s : _99546 -> Prop) : (term160 _99546 _99547 s) = (term150 _99546 _99547 s).
Proof. exact (eq_refl (term160 _99546 _99547 s)). Qed.
Lemma lem3818626 {_99546 : Type'} (s : _99546 -> Prop) : (term66 _99546 s) = (term66 _99546 s).
Proof. exact (eq_refl (term66 _99546 s)). Qed.
Lemma lem3818627 {_99546 _99547 : Type'} (s : _99546 -> Prop) : (term184 _99546 _99547 s) = (term151 _99546 _99547 s).
Proof. exact (MK_COMB (@lem3818626 _99546 s) (@lem3818625 _99546 _99547 s)). Qed.
Lemma lem3818628 {_99546 _99547 : Type'} : (term185 _99546 _99547) = (term152 _99546 _99547).
Proof. exact (fun_ext (fun s : _99546 -> Prop => @lem3818627 _99546 _99547 s)). Qed.
Lemma lem3818629 {_99546 : Type'} : (@all (_99546 -> Prop)) = (@all (_99546 -> Prop)).
Proof. exact (eq_refl (@all (_99546 -> Prop))). Qed.
Lemma lem3818630 {_99546 _99547 : Type'} : (term186 _99546 _99547) = (term153 _99546 _99547).
Proof. exact (MK_COMB (@lem3818629 _99546) (@lem3818628 _99546 _99547)). Qed.
Lemma lem3818631 {_99546 _99547 : Type'} : (term154 _99546 _99547) = (term187 _99546 _99547).
Proof. exact (MK_COMB (@lem3818624 _99546 _99547) (@lem3818630 _99546 _99547)). Qed.
Lemma lem3818632 {_99546 _99547 : Type'} : term187 _99546 _99547.
Proof. exact (EQ_MP (@lem3818631 _99546 _99547) (@lem3818603 _99546 _99547)). Qed.
Lemma lem3818646 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term188 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem3818647 (p : Prop) (q : Prop) (p' : Prop) : term189 p q p'.
Proof. exact (fun q' : Prop => @lem3818646 p q p' q'). Qed.
Lemma lem3818648 (p : Prop) (q : Prop) : term190 p q.
Proof. exact (fun p' : Prop => @lem3818647 p q p'). Qed.
Lemma lem3818649 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : term191 _99546 _99547 f g.
Proof. exact (@lem3818648 (term192 _99546 _99547 f g) (term193 _99546 _99547 f g)). Qed.
Lemma lem3818650 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (p' : Prop) : term194 _99546 _99547 f g p'.
Proof. exact (@lem3818649 _99546 _99547 f g p'). Qed.
Lemma lem3818651 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (p' : Prop) : (term194 _99546 _99547 f g p') = (term195 _99546 _99547 f g p').
Proof. exact (eq_refl (term194 _99546 _99547 f g p')). Qed.
Lemma lem3818652 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (p' : Prop) : term195 _99546 _99547 f g p'.
Proof. exact (EQ_MP (@lem3818651 _99546 _99547 f g p') (@lem3818650 _99546 _99547 f g p')). Qed.
Lemma lem3818653 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (p' : Prop) (q' : Prop) : term196 _99546 _99547 f g p' q'.
Proof. exact (@lem3818652 _99546 _99547 f g p' q'). Qed.
Lemma lem3818654 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (p' : Prop) (q' : Prop) : (term196 _99546 _99547 f g p' q') = (term197 _99546 _99547 f g p' q').
Proof. exact (eq_refl (term196 _99546 _99547 f g p' q')). Qed.
Lemma lem3818655 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (p' : Prop) (q' : Prop) : term197 _99546 _99547 f g p' q'.
Proof. exact (EQ_MP (@lem3818654 _99546 _99547 f g p' q') (@lem3818653 _99546 _99547 f g p' q')). Qed.
Lemma lem3818665 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term188 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem3818666 (p : Prop) (q : Prop) (p' : Prop) : term189 p q p'.
Proof. exact (fun q' : Prop => @lem3818665 p q p' q'). Qed.
Lemma lem3818667 (p : Prop) (q : Prop) : term190 p q.
Proof. exact (fun p' : Prop => @lem3818666 p q p'). Qed.
Lemma lem3818668 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : term198 _99546 _99547 f g x.
Proof. exact (@lem3818667 (@IN _99546 x (@EMPTY _99546)) ((f x) = (g x))). Qed.
Lemma lem3818669 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (p' : Prop) : term199 _99546 _99547 f g x p'.
Proof. exact (@lem3818668 _99546 _99547 f g x p'). Qed.
Lemma lem3818670 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (p' : Prop) : (term199 _99546 _99547 f g x p') = (term200 _99546 _99547 f g x p').
Proof. exact (eq_refl (term199 _99546 _99547 f g x p')). Qed.
Lemma lem3818671 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (p' : Prop) : term200 _99546 _99547 f g x p'.
Proof. exact (EQ_MP (@lem3818670 _99546 _99547 f g x p') (@lem3818669 _99546 _99547 f g x p')). Qed.
Lemma lem3818672 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (p' : Prop) (q' : Prop) : term201 _99546 _99547 f g x p' q'.
Proof. exact (@lem3818671 _99546 _99547 f g x p' q'). Qed.
Lemma lem3818673 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (p' : Prop) (q' : Prop) : (term201 _99546 _99547 f g x p' q') = (term202 _99546 _99547 f g x p' q').
Proof. exact (eq_refl (term201 _99546 _99547 f g x p' q')). Qed.
Lemma lem3818674 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (p' : Prop) (q' : Prop) : term202 _99546 _99547 f g x p' q'.
Proof. exact (EQ_MP (@lem3818673 _99546 _99547 f g x p' q') (@lem3818672 _99546 _99547 f g x p' q')). Qed.
Lemma lem3818676 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3817888 A x (@lem3817887 A x)). Qed.
Lemma lem3818677 {_99546 : Type'} (x : _99546) : (@IN _99546 x (@EMPTY _99546)) = False.
Proof. exact (@lem3818676 _99546 x). Qed.
Lemma lem3818678 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (q' : Prop) : term203 _99546 _99547 f g x q'.
Proof. exact (@lem3818674 _99546 _99547 f g x False q'). Qed.
Lemma lem3818679 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (q' : Prop) : term204 _99546 _99547 f g x q'.
Proof. exact (@lem3818678 _99546 _99547 f g x q' (@lem3818677 _99546 x)). Qed.
Lemma lem3818685 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : ((f x) = (g x)) = ((f x) = (g x)).
Proof. exact (eq_refl ((f x) = (g x))). Qed.
Lemma lem3818686 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : term205 _99546 _99547 f g x.
Proof. exact (fun h0 : False => @lem3818685 _99546 _99547 f g x). Qed.
Lemma lem3818687 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : term206 _99546 _99547 f g x.
Proof. exact (@lem3818679 _99546 _99547 f g x ((f x) = (g x))). Qed.
Lemma lem3818688 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term207 _99546 _99547 f g x) = (term208 _99546 _99547 f g x).
Proof. exact (@lem3818687 _99546 _99547 f g x (@lem3818686 _99546 _99547 f g x)). Qed.
Lemma lem3818690 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem3818691 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term208 _99546 _99547 f g x) = True.
Proof. exact (@lem3818690 ((f x) = (g x))). Qed.
Lemma lem3818692 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term207 _99546 _99547 f g x) = True.
Proof. exact (TRANS (@lem3818688 _99546 _99547 f g x) (@lem3818691 _99546 _99547 f g x)). Qed.
Lemma lem3818693 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term209 _99546 _99547 f g) = (term210 _99546).
Proof. exact (fun_ext (fun x : _99546 => @lem3818692 _99546 _99547 f g x)). Qed.
Lemma lem3818694 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3818695 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term211 _99546 _99547 f g) = (term212 _99546).
Proof. exact (MK_COMB (@lem3818694 _99546) (@lem3818693 _99546 _99547 f g)). Qed.
Lemma lem3818697 {A : Type'} (t : Prop) : (term213 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3818698 {_99546 : Type'} (t : Prop) : (term213 _99546 t) = t.
Proof. exact (@lem3818697 _99546 t). Qed.
Lemma lem3818699 {_99546 : Type'} : (term212 _99546) = True.
Proof. exact (@lem3818698 _99546 True). Qed.
Lemma lem3818700 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term211 _99546 _99547 f g) = True.
Proof. exact (TRANS (@lem3818695 _99546 _99547 f g) (@lem3818699 _99546)). Qed.
Lemma lem3818701 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3818702 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term214 _99546 _99547 f g) = (and True).
Proof. exact (MK_COMB (@lem3818701) (@lem3818700 _99546 _99547 f g)). Qed.
Lemma lem3818821 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term116 _99546 _99547 f g) = (term116 _99546 _99547 f g).
Proof. exact (eq_refl (term116 _99546 _99547 f g)). Qed.
Lemma lem3818822 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term192 _99546 _99547 f g) = (term215 _99546 _99547 f g).
Proof. exact (MK_COMB (@lem3818702 _99546 _99547 f g) (@lem3818821 _99546 _99547 f g)). Qed.
Lemma lem3818824 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3818825 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term215 _99546 _99547 f g) = (term116 _99546 _99547 f g).
Proof. exact (@lem3818824 (term116 _99546 _99547 f g)). Qed.
Lemma lem3818944 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term192 _99546 _99547 f g) = (term116 _99546 _99547 f g).
Proof. exact (TRANS (@lem3818822 _99546 _99547 f g) (@lem3818825 _99546 _99547 f g)). Qed.
Lemma lem3818945 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (q' : Prop) : term216 _99546 _99547 f g q'.
Proof. exact (@lem3818655 _99546 _99547 f g (term116 _99546 _99547 f g) q'). Qed.
Lemma lem3818946 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (q' : Prop) : term217 _99546 _99547 f g q'.
Proof. exact (@lem3818945 _99546 _99547 f g q' (@lem3818944 _99546 _99547 f g)). Qed.
Lemma lem3818947 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : term116 _99546 _99547 f g.
Proof. exact (h1). Qed.
Lemma lem3818948 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : term112 _99546 _99547 g.
Proof. exact (proj2 (@lem3818947 _99546 _99547 f g h1)). Qed.
Lemma lem3818949 {_99546 _99547 : Type'} (x : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : term218 _99546 _99547 g x.
Proof. exact (@lem3818948 _99546 _99547 f g h1 x). Qed.
Lemma lem3818950 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) : (term218 _99546 _99547 g x) = (term109 _99546 _99547 g x).
Proof. exact (eq_refl (term218 _99546 _99547 g x)). Qed.
Lemma lem3818951 {_99546 _99547 : Type'} (x : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : term109 _99546 _99547 g x.
Proof. exact (EQ_MP (@lem3818950 _99546 _99547 g x) (@lem3818949 _99546 _99547 x f g h1)). Qed.
Lemma lem3818952 {_99546 _99547 : Type'} (x : _99546) (y : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : term219 _99546 _99547 g x y.
Proof. exact (@lem3818951 _99546 _99547 x f g h1 y). Qed.
Lemma lem3818953 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term219 _99546 _99547 g x y) = (term105 _99546 _99547 y g x).
Proof. exact (eq_refl (term219 _99546 _99547 g x y)). Qed.
Lemma lem3818954 {_99546 _99547 : Type'} (y : _99546) (x : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : term105 _99546 _99547 y g x.
Proof. exact (EQ_MP (@lem3818953 _99546 _99547 y g x) (@lem3818952 _99546 _99547 x y f g h1)). Qed.
Lemma lem3818955 {_99546 : Type'} (x : _99546) (y : _99546) (h1 : term90 _99546 x y) : term90 _99546 x y.
Proof. exact (h1). Qed.
Lemma lem3818956 {_99546 _99547 : Type'} (x : _99546) (y : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term90 _99546 x y) (h2 : term116 _99546 _99547 f g) : term104 _99546 _99547 y g x.
Proof. exact (@lem3818954 _99546 _99547 y x f g h2 (@lem3818955 _99546 x y h1)). Qed.
Lemma lem3818957 {_99546 _99547 : Type'} (s : _99547) (x : _99546) (y : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term90 _99546 x y) (h2 : term116 _99546 _99547 f g) : term92 _99546 _99547 y g x s.
Proof. exact (@lem3818956 _99546 _99547 x y f g h1 h2 s). Qed.
Lemma lem3818958 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term92 _99546 _99547 y g x s) = ((term93 _99546 _99547 x g y s) = (term93 _99546 _99547 y g x s)).
Proof. exact (eq_refl (term92 _99546 _99547 y g x s)). Qed.
Lemma lem3818959 {_99546 _99547 : Type'} (s : _99547) (x : _99546) (y : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term90 _99546 x y) (h2 : term116 _99546 _99547 f g) : (term93 _99546 _99547 x g y s) = (term93 _99546 _99547 y g x s).
Proof. exact (EQ_MP (@lem3818958 _99546 _99547 y g x s) (@lem3818957 _99546 _99547 s x y f g h1 h2)). Qed.
Lemma lem3818965 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : term112 _99546 _99547 f.
Proof. exact (proj1 (@lem3818947 _99546 _99547 f g h1)). Qed.
Lemma lem3818966 {_99546 _99547 : Type'} (x : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : term218 _99546 _99547 f x.
Proof. exact (@lem3818965 _99546 _99547 f g h1 x). Qed.
Lemma lem3818967 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (term218 _99546 _99547 f x) = (term109 _99546 _99547 f x).
Proof. exact (eq_refl (term218 _99546 _99547 f x)). Qed.
Lemma lem3818968 {_99546 _99547 : Type'} (x : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : term109 _99546 _99547 f x.
Proof. exact (EQ_MP (@lem3818967 _99546 _99547 f x) (@lem3818966 _99546 _99547 x f g h1)). Qed.
Lemma lem3818969 {_99546 _99547 : Type'} (x : _99546) (y : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : term219 _99546 _99547 f x y.
Proof. exact (@lem3818968 _99546 _99547 x f g h1 y). Qed.
Lemma lem3818970 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term219 _99546 _99547 f x y) = (term105 _99546 _99547 y f x).
Proof. exact (eq_refl (term219 _99546 _99547 f x y)). Qed.
Lemma lem3818971 {_99546 _99547 : Type'} (y : _99546) (x : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : term105 _99546 _99547 y f x.
Proof. exact (EQ_MP (@lem3818970 _99546 _99547 y f x) (@lem3818969 _99546 _99547 x y f g h1)). Qed.
Lemma lem3818972 {_99546 : Type'} (x : _99546) (y : _99546) (h1 : term90 _99546 x y) : term90 _99546 x y.
Proof. exact (h1). Qed.
Lemma lem3818973 {_99546 _99547 : Type'} (x : _99546) (y : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term90 _99546 x y) (h2 : term116 _99546 _99547 f g) : term104 _99546 _99547 y f x.
Proof. exact (@lem3818971 _99546 _99547 y x f g h2 (@lem3818972 _99546 x y h1)). Qed.
Lemma lem3818974 {_99546 _99547 : Type'} (s : _99547) (x : _99546) (y : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term90 _99546 x y) (h2 : term116 _99546 _99547 f g) : term92 _99546 _99547 y f x s.
Proof. exact (@lem3818973 _99546 _99547 x y f g h1 h2 s). Qed.
Lemma lem3818975 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term92 _99546 _99547 y f x s) = ((term93 _99546 _99547 x f y s) = (term93 _99546 _99547 y f x s)).
Proof. exact (eq_refl (term92 _99546 _99547 y f x s)). Qed.
Lemma lem3818976 {_99546 _99547 : Type'} (s : _99547) (x : _99546) (y : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term90 _99546 x y) (h2 : term116 _99546 _99547 f g) : (term93 _99546 _99547 x f y s) = (term93 _99546 _99547 y f x s).
Proof. exact (EQ_MP (@lem3818975 _99546 _99547 y f x s) (@lem3818974 _99546 _99547 s x y f g h1 h2)). Qed.
Lemma lem3818989 {A B : Type'} (f : type1411 A B) (b : B) : term220 A B f b.
Proof. exact (fun h0 : term19 A B f => @lem3817917 A B b f h0). Qed.
Lemma lem3818990 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (b : _99547) : term220 _99546 _99547 f b.
Proof. exact (@lem3818989 _99546 _99547 f b). Qed.
Lemma lem3819006 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term188 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem3819007 (p : Prop) (q : Prop) (p' : Prop) : term189 p q p'.
Proof. exact (fun q' : Prop => @lem3819006 p q p' q'). Qed.
Lemma lem3819008 (p : Prop) (q : Prop) : term190 p q.
Proof. exact (fun p' : Prop => @lem3819007 p q p'). Qed.
Lemma lem3819009 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) (s : _99547) : term221 _99546 _99547 y f x s.
Proof. exact (@lem3819008 (term90 _99546 x y) ((term93 _99546 _99547 x f y s) = (term93 _99546 _99547 y f x s))). Qed.
Lemma lem3819010 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) (s : _99547) (p' : Prop) : term222 _99546 _99547 y f x s p'.
Proof. exact (@lem3819009 _99546 _99547 y f x s p'). Qed.
Lemma lem3819011 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) (s : _99547) (p' : Prop) : (term222 _99546 _99547 y f x s p') = (term223 _99546 _99547 y f x s p').
Proof. exact (eq_refl (term222 _99546 _99547 y f x s p')). Qed.
Lemma lem3819012 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) (s : _99547) (p' : Prop) : term223 _99546 _99547 y f x s p'.
Proof. exact (EQ_MP (@lem3819011 _99546 _99547 y f x s p') (@lem3819010 _99546 _99547 y f x s p')). Qed.
Lemma lem3819013 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) (s : _99547) (p' : Prop) (q' : Prop) : term224 _99546 _99547 y f x s p' q'.
Proof. exact (@lem3819012 _99546 _99547 y f x s p' q'). Qed.
Lemma lem3819014 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) (s : _99547) (p' : Prop) (q' : Prop) : (term224 _99546 _99547 y f x s p' q') = (term225 _99546 _99547 y f x s p' q').
Proof. exact (eq_refl (term224 _99546 _99547 y f x s p' q')). Qed.
Lemma lem3819015 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) (s : _99547) (p' : Prop) (q' : Prop) : term225 _99546 _99547 y f x s p' q'.
Proof. exact (EQ_MP (@lem3819014 _99546 _99547 y f x s p' q') (@lem3819013 _99546 _99547 y f x s p' q')). Qed.
Lemma lem3819018 {_99546 : Type'} (x : _99546) (y : _99546) : (term90 _99546 x y) = (term90 _99546 x y).
Proof. exact (eq_refl (term90 _99546 x y)). Qed.
Lemma lem3819019 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99547) (x : _99546) (y : _99546) (q' : Prop) : term226 _99546 _99547 f s x y q'.
Proof. exact (@lem3819015 _99546 _99547 y f x s (term90 _99546 x y) q'). Qed.
Lemma lem3819020 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99547) (x : _99546) (y : _99546) (q' : Prop) : term227 _99546 _99547 f s x y q'.
Proof. exact (@lem3819019 _99546 _99547 f s x y q' (@lem3819018 _99546 x y)). Qed.
Lemma lem3819021 {_99546 : Type'} (x : _99546) (y : _99546) (h1 : term90 _99546 x y) : term90 _99546 x y.
Proof. exact (h1). Qed.
Lemma lem3819025 {_99546 : Type'} (x : _99546) (y : _99546) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem3819026 {_99546 : Type'} (x : _99546) (y : _99546) (h1 : x = y) : y = x.
Proof. exact (SYM (@lem3819025 _99546 x y h1)). Qed.
Lemma lem3819027 {_99546 : Type'} (y : _99546) (x : _99546) (h1 : y = x) : y = x.
Proof. exact (h1). Qed.
Lemma lem3819028 {_99546 : Type'} (y : _99546) (x : _99546) (h1 : y = x) : x = y.
Proof. exact (SYM (@lem3819027 _99546 y x h1)). Qed.
Lemma lem3819029 {_99546 : Type'} (y : _99546) (x : _99546) : (x = y) = (y = x).
Proof. exact (prop_ext (fun h1 : x = y => @lem3819026 _99546 x y h1) (fun h1 : y = x => @lem3819028 _99546 y x h1)). Qed.
Lemma lem3819030 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3819031 {_99546 : Type'} (y : _99546) (x : _99546) : (term90 _99546 x y) = (term90 _99546 y x).
Proof. exact (MK_COMB (@lem3819030) (@lem3819029 _99546 y x)). Qed.
Lemma lem3819032 {_99546 : Type'} (x : _99546) (y : _99546) (h1 : term90 _99546 x y) : term90 _99546 y x.
Proof. exact (EQ_MP (@lem3819031 _99546 y x) (@lem3819021 _99546 x y h1)). Qed.
Lemma lem3819033 {_99546 : Type'} (y : _99546) (x : _99546) : term228 _99546 y x.
Proof. exact (@lem82 (y = x)). Qed.
Lemma lem3819041 {_99546 _99547 : Type'} (y : _99546) (x : _99546) (s : _99547) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : term96 _99546 _99547 y f x s.
Proof. exact (fun h0 : term90 _99546 x y => @lem3818976 _99546 _99547 s x y f g h0 h1). Qed.
Lemma lem3819042 {_99546 _99547 : Type'} (y : _99546) (x : _99546) (s : _99547) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : term96 _99546 _99547 y f x s.
Proof. exact (@lem3819041 _99546 _99547 y x s f g h1). Qed.
Lemma lem3819043 {_99546 _99547 : Type'} (x : _99546) (y : _99546) (s : _99547) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : term96 _99546 _99547 x f y s.
Proof. exact (@lem3819042 _99546 _99547 x y s f g h1). Qed.
Lemma lem3819045 {_99546 : Type'} (x : _99546) (y : _99546) (h1 : term90 _99546 x y) : (y = x) = False.
Proof. exact (@lem3819033 _99546 y x (@lem3819032 _99546 x y h1)). Qed.
Lemma lem3819046 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3819047 {_99546 : Type'} (x : _99546) (y : _99546) (h1 : term90 _99546 x y) : (term90 _99546 y x) = (~ False).
Proof. exact (MK_COMB (@lem3819046) (@lem3819045 _99546 x y h1)). Qed.
Lemma lem3819049 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3819050 {_99546 : Type'} (x : _99546) (y : _99546) (h1 : term90 _99546 x y) : (term90 _99546 y x) = True.
Proof. exact (TRANS (@lem3819047 _99546 x y h1) (@lem3819049)). Qed.
Lemma lem3819051 {_99546 : Type'} (x : _99546) (y : _99546) (h1 : term90 _99546 x y) : True = (term90 _99546 y x).
Proof. exact (SYM (@lem3819050 _99546 x y h1)). Qed.
Lemma lem3819052 {_99546 : Type'} (x : _99546) (y : _99546) (h1 : term90 _99546 x y) : term90 _99546 y x.
Proof. exact (EQ_MP (@lem3819051 _99546 x y h1) (@lem0)). Qed.
Lemma lem3819053 {_99546 _99547 : Type'} (s : _99547) (x : _99546) (y : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term90 _99546 x y) (h2 : term116 _99546 _99547 f g) : (term93 _99546 _99547 y f x s) = (term93 _99546 _99547 x f y s).
Proof. exact (@lem3819043 _99546 _99547 x y s f g h2 (@lem3819052 _99546 x y h1)). Qed.
Lemma lem3819057 {_99546 _99547 : Type'} (x : _99546) (f : type1411 _99546 _99547) (y : _99546) (s : _99547) : (term229 _99546 _99547 x f y s) = (term229 _99546 _99547 x f y s).
Proof. exact (eq_refl (term229 _99546 _99547 x f y s)). Qed.
Lemma lem3819058 {_99546 _99547 : Type'} (s : _99547) (x : _99546) (y : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term90 _99546 x y) (h2 : term116 _99546 _99547 f g) : ((term93 _99546 _99547 x f y s) = (term93 _99546 _99547 y f x s)) = ((term93 _99546 _99547 x f y s) = (term93 _99546 _99547 x f y s)).
Proof. exact (MK_COMB (@lem3819057 _99546 _99547 x f y s) (@lem3819053 _99546 _99547 s x y f g h1 h2)). Qed.
Lemma lem3819060 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3819061 {_99547 : Type'} (x : _99547) : (x = x) = True.
Proof. exact (@lem3819060 _99547 x). Qed.
Lemma lem3819062 {_99546 _99547 : Type'} (x : _99546) (f : type1411 _99546 _99547) (y : _99546) (s : _99547) : ((term93 _99546 _99547 x f y s) = (term93 _99546 _99547 x f y s)) = True.
Proof. exact (@lem3819061 _99547 (term93 _99546 _99547 x f y s)). Qed.
Lemma lem3819063 {_99546 _99547 : Type'} (s : _99547) (x : _99546) (y : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term90 _99546 x y) (h2 : term116 _99546 _99547 f g) : ((term93 _99546 _99547 x f y s) = (term93 _99546 _99547 y f x s)) = True.
Proof. exact (TRANS (@lem3819058 _99546 _99547 s x y f g h1 h2) (@lem3819062 _99546 _99547 x f y s)). Qed.
Lemma lem3819064 {_99546 _99547 : Type'} (y : _99546) (x : _99546) (s : _99547) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : term230 _99546 _99547 y f x s.
Proof. exact (fun h0 : term90 _99546 x y => @lem3819063 _99546 _99547 s x y f g h0 h1). Qed.
Lemma lem3819065 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99547) (x : _99546) (y : _99546) : term231 _99546 _99547 f s x y.
Proof. exact (@lem3819020 _99546 _99547 f s x y True). Qed.
Lemma lem3819066 {_99546 _99547 : Type'} (s : _99547) (x : _99546) (y : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : (term96 _99546 _99547 y f x s) = (term232 _99546 x y).
Proof. exact (@lem3819065 _99546 _99547 f s x y (@lem3819064 _99546 _99547 y x s f g h1)). Qed.
Lemma lem3819068 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem3819069 {_99546 : Type'} (x : _99546) (y : _99546) : (term232 _99546 x y) = True.
Proof. exact (@lem3819068 (term90 _99546 x y)). Qed.
Lemma lem3819070 {_99546 _99547 : Type'} (y : _99546) (x : _99546) (s : _99547) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : (term96 _99546 _99547 y f x s) = True.
Proof. exact (TRANS (@lem3819066 _99546 _99547 s x y f g h1) (@lem3819069 _99546 x y)). Qed.
Lemma lem3819071 {_99546 _99547 : Type'} (y : _99546) (x : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : (term98 _99546 _99547 y f x) = (term210 _99547).
Proof. exact (fun_ext (fun s : _99547 => @lem3819070 _99546 _99547 y x s f g h1)). Qed.
Lemma lem3819072 {_99547 : Type'} : (@all _99547) = (@all _99547).
Proof. exact (eq_refl (@all _99547)). Qed.
Lemma lem3819073 {_99546 _99547 : Type'} (y : _99546) (x : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : (term99 _99546 _99547 y f x) = (term212 _99547).
Proof. exact (MK_COMB (@lem3819072 _99547) (@lem3819071 _99546 _99547 y x f g h1)). Qed.
Lemma lem3819075 {A : Type'} (t : Prop) : (term213 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3819076 {_99547 : Type'} (t : Prop) : (term213 _99547 t) = t.
Proof. exact (@lem3819075 _99547 t). Qed.
Lemma lem3819077 {_99547 : Type'} : (term212 _99547) = True.
Proof. exact (@lem3819076 _99547 True). Qed.
Lemma lem3819078 {_99546 _99547 : Type'} (y : _99546) (x : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : (term99 _99546 _99547 y f x) = True.
Proof. exact (TRANS (@lem3819073 _99546 _99547 y x f g h1) (@lem3819077 _99547)). Qed.
Lemma lem3819079 {_99546 _99547 : Type'} (x : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : (term106 _99546 _99547 f x) = (term210 _99546).
Proof. exact (fun_ext (fun y : _99546 => @lem3819078 _99546 _99547 y x f g h1)). Qed.
Lemma lem3819080 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3819081 {_99546 _99547 : Type'} (x : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : (term108 _99546 _99547 f x) = (term212 _99546).
Proof. exact (MK_COMB (@lem3819080 _99546) (@lem3819079 _99546 _99547 x f g h1)). Qed.
Lemma lem3819083 {A : Type'} (t : Prop) : (term213 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3819084 {_99546 : Type'} (t : Prop) : (term213 _99546 t) = t.
Proof. exact (@lem3819083 _99546 t). Qed.
Lemma lem3819085 {_99546 : Type'} : (term212 _99546) = True.
Proof. exact (@lem3819084 _99546 True). Qed.
Lemma lem3819086 {_99546 _99547 : Type'} (x : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : (term108 _99546 _99547 f x) = True.
Proof. exact (TRANS (@lem3819081 _99546 _99547 x f g h1) (@lem3819085 _99546)). Qed.
Lemma lem3819087 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : (term110 _99546 _99547 f) = (term210 _99546).
Proof. exact (fun_ext (fun x : _99546 => @lem3819086 _99546 _99547 x f g h1)). Qed.
Lemma lem3819088 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3819089 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : (term19 _99546 _99547 f) = (term212 _99546).
Proof. exact (MK_COMB (@lem3819088 _99546) (@lem3819087 _99546 _99547 f g h1)). Qed.
Lemma lem3819091 {A : Type'} (t : Prop) : (term213 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3819092 {_99546 : Type'} (t : Prop) : (term213 _99546 t) = t.
Proof. exact (@lem3819091 _99546 t). Qed.
Lemma lem3819093 {_99546 : Type'} : (term212 _99546) = True.
Proof. exact (@lem3819092 _99546 True). Qed.
Lemma lem3819094 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : (term19 _99546 _99547 f) = True.
Proof. exact (TRANS (@lem3819089 _99546 _99547 f g h1) (@lem3819093 _99546)). Qed.
Lemma lem3819095 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : True = (term19 _99546 _99547 f).
Proof. exact (SYM (@lem3819094 _99546 _99547 f g h1)). Qed.
Lemma lem3819096 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : term19 _99546 _99547 f.
Proof. exact (EQ_MP (@lem3819095 _99546 _99547 f g h1) (@lem0)). Qed.
Lemma lem3819097 {_99546 _99547 : Type'} (b : _99547) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : (@ITSET _99547 _99546 f (@EMPTY _99546) b) = b.
Proof. exact (@lem3818990 _99546 _99547 f b (@lem3819096 _99546 _99547 f g h1)). Qed.
Lemma lem3819098 {_99547 : Type'} : (@eq _99547) = (@eq _99547).
Proof. exact (eq_refl (@eq _99547)). Qed.
Lemma lem3819099 {_99546 _99547 : Type'} (b : _99547) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : (term233 _99546 _99547 f b) = (@eq _99547 b).
Proof. exact (MK_COMB (@lem3819098 _99547) (@lem3819097 _99546 _99547 b f g h1)). Qed.
Lemma lem3819101 {A B : Type'} (f : type1411 A B) (b : B) : term220 A B f b.
Proof. exact (fun h0 : term19 A B f => @lem3817917 A B b f h0). Qed.
Lemma lem3819102 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (b : _99547) : term220 _99546 _99547 f b.
Proof. exact (@lem3819101 _99546 _99547 f b). Qed.
Lemma lem3819103 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (b : _99547) : term220 _99546 _99547 g b.
Proof. exact (@lem3819102 _99546 _99547 g b). Qed.
Lemma lem3819119 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term188 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem3819120 (p : Prop) (q : Prop) (p' : Prop) : term189 p q p'.
Proof. exact (fun q' : Prop => @lem3819119 p q p' q'). Qed.
Lemma lem3819121 (p : Prop) (q : Prop) : term190 p q.
Proof. exact (fun p' : Prop => @lem3819120 p q p'). Qed.
Lemma lem3819122 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) : term221 _99546 _99547 y g x s.
Proof. exact (@lem3819121 (term90 _99546 x y) ((term93 _99546 _99547 x g y s) = (term93 _99546 _99547 y g x s))). Qed.
Lemma lem3819123 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) (p' : Prop) : term222 _99546 _99547 y g x s p'.
Proof. exact (@lem3819122 _99546 _99547 y g x s p'). Qed.
Lemma lem3819124 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) (p' : Prop) : (term222 _99546 _99547 y g x s p') = (term223 _99546 _99547 y g x s p').
Proof. exact (eq_refl (term222 _99546 _99547 y g x s p')). Qed.
Lemma lem3819125 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) (p' : Prop) : term223 _99546 _99547 y g x s p'.
Proof. exact (EQ_MP (@lem3819124 _99546 _99547 y g x s p') (@lem3819123 _99546 _99547 y g x s p')). Qed.
Lemma lem3819126 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) (p' : Prop) (q' : Prop) : term224 _99546 _99547 y g x s p' q'.
Proof. exact (@lem3819125 _99546 _99547 y g x s p' q'). Qed.
Lemma lem3819127 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) (p' : Prop) (q' : Prop) : (term224 _99546 _99547 y g x s p' q') = (term225 _99546 _99547 y g x s p' q').
Proof. exact (eq_refl (term224 _99546 _99547 y g x s p' q')). Qed.
Lemma lem3819128 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) (p' : Prop) (q' : Prop) : term225 _99546 _99547 y g x s p' q'.
Proof. exact (EQ_MP (@lem3819127 _99546 _99547 y g x s p' q') (@lem3819126 _99546 _99547 y g x s p' q')). Qed.
Lemma lem3819131 {_99546 : Type'} (x : _99546) (y : _99546) : (term90 _99546 x y) = (term90 _99546 x y).
Proof. exact (eq_refl (term90 _99546 x y)). Qed.
Lemma lem3819132 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (s : _99547) (x : _99546) (y : _99546) (q' : Prop) : term226 _99546 _99547 g s x y q'.
Proof. exact (@lem3819128 _99546 _99547 y g x s (term90 _99546 x y) q'). Qed.
Lemma lem3819133 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (s : _99547) (x : _99546) (y : _99546) (q' : Prop) : term227 _99546 _99547 g s x y q'.
Proof. exact (@lem3819132 _99546 _99547 g s x y q' (@lem3819131 _99546 x y)). Qed.
Lemma lem3819134 {_99546 : Type'} (x : _99546) (y : _99546) (h1 : term90 _99546 x y) : term90 _99546 x y.
Proof. exact (h1). Qed.
Lemma lem3819138 {_99546 : Type'} (x : _99546) (y : _99546) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem3819139 {_99546 : Type'} (x : _99546) (y : _99546) (h1 : x = y) : y = x.
Proof. exact (SYM (@lem3819138 _99546 x y h1)). Qed.
Lemma lem3819140 {_99546 : Type'} (y : _99546) (x : _99546) (h1 : y = x) : y = x.
Proof. exact (h1). Qed.
Lemma lem3819141 {_99546 : Type'} (y : _99546) (x : _99546) (h1 : y = x) : x = y.
Proof. exact (SYM (@lem3819140 _99546 y x h1)). Qed.
Lemma lem3819142 {_99546 : Type'} (y : _99546) (x : _99546) : (x = y) = (y = x).
Proof. exact (prop_ext (fun h1 : x = y => @lem3819139 _99546 x y h1) (fun h1 : y = x => @lem3819141 _99546 y x h1)). Qed.
Lemma lem3819143 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3819144 {_99546 : Type'} (y : _99546) (x : _99546) : (term90 _99546 x y) = (term90 _99546 y x).
Proof. exact (MK_COMB (@lem3819143) (@lem3819142 _99546 y x)). Qed.
Lemma lem3819145 {_99546 : Type'} (x : _99546) (y : _99546) (h1 : term90 _99546 x y) : term90 _99546 y x.
Proof. exact (EQ_MP (@lem3819144 _99546 y x) (@lem3819134 _99546 x y h1)). Qed.
Lemma lem3819146 {_99546 : Type'} (y : _99546) (x : _99546) : term228 _99546 y x.
Proof. exact (@lem82 (y = x)). Qed.
Lemma lem3819154 {_99546 _99547 : Type'} (y : _99546) (x : _99546) (s : _99547) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : term96 _99546 _99547 y g x s.
Proof. exact (fun h0 : term90 _99546 x y => @lem3818959 _99546 _99547 s x y f g h0 h1). Qed.
Lemma lem3819155 {_99546 _99547 : Type'} (y : _99546) (x : _99546) (s : _99547) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : term96 _99546 _99547 y g x s.
Proof. exact (@lem3819154 _99546 _99547 y x s f g h1). Qed.
Lemma lem3819156 {_99546 _99547 : Type'} (x : _99546) (y : _99546) (s : _99547) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : term96 _99546 _99547 x g y s.
Proof. exact (@lem3819155 _99546 _99547 x y s f g h1). Qed.
Lemma lem3819158 {_99546 : Type'} (x : _99546) (y : _99546) (h1 : term90 _99546 x y) : (y = x) = False.
Proof. exact (@lem3819146 _99546 y x (@lem3819145 _99546 x y h1)). Qed.
Lemma lem3819159 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3819160 {_99546 : Type'} (x : _99546) (y : _99546) (h1 : term90 _99546 x y) : (term90 _99546 y x) = (~ False).
Proof. exact (MK_COMB (@lem3819159) (@lem3819158 _99546 x y h1)). Qed.
Lemma lem3819162 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3819163 {_99546 : Type'} (x : _99546) (y : _99546) (h1 : term90 _99546 x y) : (term90 _99546 y x) = True.
Proof. exact (TRANS (@lem3819160 _99546 x y h1) (@lem3819162)). Qed.
Lemma lem3819164 {_99546 : Type'} (x : _99546) (y : _99546) (h1 : term90 _99546 x y) : True = (term90 _99546 y x).
Proof. exact (SYM (@lem3819163 _99546 x y h1)). Qed.
Lemma lem3819165 {_99546 : Type'} (x : _99546) (y : _99546) (h1 : term90 _99546 x y) : term90 _99546 y x.
Proof. exact (EQ_MP (@lem3819164 _99546 x y h1) (@lem0)). Qed.
Lemma lem3819166 {_99546 _99547 : Type'} (s : _99547) (x : _99546) (y : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term90 _99546 x y) (h2 : term116 _99546 _99547 f g) : (term93 _99546 _99547 y g x s) = (term93 _99546 _99547 x g y s).
Proof. exact (@lem3819156 _99546 _99547 x y s f g h2 (@lem3819165 _99546 x y h1)). Qed.
Lemma lem3819170 {_99546 _99547 : Type'} (x : _99546) (g : type1411 _99546 _99547) (y : _99546) (s : _99547) : (term229 _99546 _99547 x g y s) = (term229 _99546 _99547 x g y s).
Proof. exact (eq_refl (term229 _99546 _99547 x g y s)). Qed.
Lemma lem3819171 {_99546 _99547 : Type'} (s : _99547) (x : _99546) (y : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term90 _99546 x y) (h2 : term116 _99546 _99547 f g) : ((term93 _99546 _99547 x g y s) = (term93 _99546 _99547 y g x s)) = ((term93 _99546 _99547 x g y s) = (term93 _99546 _99547 x g y s)).
Proof. exact (MK_COMB (@lem3819170 _99546 _99547 x g y s) (@lem3819166 _99546 _99547 s x y f g h1 h2)). Qed.
Lemma lem3819173 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3819174 {_99547 : Type'} (x : _99547) : (x = x) = True.
Proof. exact (@lem3819173 _99547 x). Qed.
Lemma lem3819175 {_99546 _99547 : Type'} (x : _99546) (g : type1411 _99546 _99547) (y : _99546) (s : _99547) : ((term93 _99546 _99547 x g y s) = (term93 _99546 _99547 x g y s)) = True.
Proof. exact (@lem3819174 _99547 (term93 _99546 _99547 x g y s)). Qed.
Lemma lem3819176 {_99546 _99547 : Type'} (s : _99547) (x : _99546) (y : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term90 _99546 x y) (h2 : term116 _99546 _99547 f g) : ((term93 _99546 _99547 x g y s) = (term93 _99546 _99547 y g x s)) = True.
Proof. exact (TRANS (@lem3819171 _99546 _99547 s x y f g h1 h2) (@lem3819175 _99546 _99547 x g y s)). Qed.
Lemma lem3819177 {_99546 _99547 : Type'} (y : _99546) (x : _99546) (s : _99547) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : term230 _99546 _99547 y g x s.
Proof. exact (fun h0 : term90 _99546 x y => @lem3819176 _99546 _99547 s x y f g h0 h1). Qed.
Lemma lem3819178 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (s : _99547) (x : _99546) (y : _99546) : term231 _99546 _99547 g s x y.
Proof. exact (@lem3819133 _99546 _99547 g s x y True). Qed.
Lemma lem3819179 {_99546 _99547 : Type'} (s : _99547) (x : _99546) (y : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : (term96 _99546 _99547 y g x s) = (term232 _99546 x y).
Proof. exact (@lem3819178 _99546 _99547 g s x y (@lem3819177 _99546 _99547 y x s f g h1)). Qed.
Lemma lem3819181 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem3819182 {_99546 : Type'} (x : _99546) (y : _99546) : (term232 _99546 x y) = True.
Proof. exact (@lem3819181 (term90 _99546 x y)). Qed.
Lemma lem3819183 {_99546 _99547 : Type'} (y : _99546) (x : _99546) (s : _99547) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : (term96 _99546 _99547 y g x s) = True.
Proof. exact (TRANS (@lem3819179 _99546 _99547 s x y f g h1) (@lem3819182 _99546 x y)). Qed.
Lemma lem3819184 {_99546 _99547 : Type'} (y : _99546) (x : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : (term98 _99546 _99547 y g x) = (term210 _99547).
Proof. exact (fun_ext (fun s : _99547 => @lem3819183 _99546 _99547 y x s f g h1)). Qed.
Lemma lem3819185 {_99547 : Type'} : (@all _99547) = (@all _99547).
Proof. exact (eq_refl (@all _99547)). Qed.
Lemma lem3819186 {_99546 _99547 : Type'} (y : _99546) (x : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : (term99 _99546 _99547 y g x) = (term212 _99547).
Proof. exact (MK_COMB (@lem3819185 _99547) (@lem3819184 _99546 _99547 y x f g h1)). Qed.
Lemma lem3819188 {A : Type'} (t : Prop) : (term213 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3819189 {_99547 : Type'} (t : Prop) : (term213 _99547 t) = t.
Proof. exact (@lem3819188 _99547 t). Qed.
Lemma lem3819190 {_99547 : Type'} : (term212 _99547) = True.
Proof. exact (@lem3819189 _99547 True). Qed.
Lemma lem3819191 {_99546 _99547 : Type'} (y : _99546) (x : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : (term99 _99546 _99547 y g x) = True.
Proof. exact (TRANS (@lem3819186 _99546 _99547 y x f g h1) (@lem3819190 _99547)). Qed.
Lemma lem3819192 {_99546 _99547 : Type'} (x : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : (term106 _99546 _99547 g x) = (term210 _99546).
Proof. exact (fun_ext (fun y : _99546 => @lem3819191 _99546 _99547 y x f g h1)). Qed.
Lemma lem3819193 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3819194 {_99546 _99547 : Type'} (x : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : (term108 _99546 _99547 g x) = (term212 _99546).
Proof. exact (MK_COMB (@lem3819193 _99546) (@lem3819192 _99546 _99547 x f g h1)). Qed.
Lemma lem3819196 {A : Type'} (t : Prop) : (term213 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3819197 {_99546 : Type'} (t : Prop) : (term213 _99546 t) = t.
Proof. exact (@lem3819196 _99546 t). Qed.
Lemma lem3819198 {_99546 : Type'} : (term212 _99546) = True.
Proof. exact (@lem3819197 _99546 True). Qed.
Lemma lem3819199 {_99546 _99547 : Type'} (x : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : (term108 _99546 _99547 g x) = True.
Proof. exact (TRANS (@lem3819194 _99546 _99547 x f g h1) (@lem3819198 _99546)). Qed.
Lemma lem3819200 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : (term110 _99546 _99547 g) = (term210 _99546).
Proof. exact (fun_ext (fun x : _99546 => @lem3819199 _99546 _99547 x f g h1)). Qed.
Lemma lem3819201 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3819202 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : (term19 _99546 _99547 g) = (term212 _99546).
Proof. exact (MK_COMB (@lem3819201 _99546) (@lem3819200 _99546 _99547 f g h1)). Qed.
Lemma lem3819204 {A : Type'} (t : Prop) : (term213 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3819205 {_99546 : Type'} (t : Prop) : (term213 _99546 t) = t.
Proof. exact (@lem3819204 _99546 t). Qed.
Lemma lem3819206 {_99546 : Type'} : (term212 _99546) = True.
Proof. exact (@lem3819205 _99546 True). Qed.
Lemma lem3819207 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : (term19 _99546 _99547 g) = True.
Proof. exact (TRANS (@lem3819202 _99546 _99547 f g h1) (@lem3819206 _99546)). Qed.
Lemma lem3819208 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : True = (term19 _99546 _99547 g).
Proof. exact (SYM (@lem3819207 _99546 _99547 f g h1)). Qed.
Lemma lem3819209 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : term19 _99546 _99547 g.
Proof. exact (EQ_MP (@lem3819208 _99546 _99547 f g h1) (@lem0)). Qed.
Lemma lem3819210 {_99546 _99547 : Type'} (b : _99547) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : (@ITSET _99547 _99546 g (@EMPTY _99546) b) = b.
Proof. exact (@lem3819103 _99546 _99547 g b (@lem3819209 _99546 _99547 f g h1)). Qed.
Lemma lem3819211 {_99546 _99547 : Type'} (b : _99547) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : ((@ITSET _99547 _99546 f (@EMPTY _99546) b) = (@ITSET _99547 _99546 g (@EMPTY _99546) b)) = (b = b).
Proof. exact (MK_COMB (@lem3819099 _99546 _99547 b f g h1) (@lem3819210 _99546 _99547 b f g h1)). Qed.
Lemma lem3819213 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3819214 {_99547 : Type'} (x : _99547) : (x = x) = True.
Proof. exact (@lem3819213 _99547 x). Qed.
Lemma lem3819215 {_99547 : Type'} (b : _99547) : (b = b) = True.
Proof. exact (@lem3819214 _99547 b). Qed.
Lemma lem3819216 {_99546 _99547 : Type'} (b : _99547) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : ((@ITSET _99547 _99546 f (@EMPTY _99546) b) = (@ITSET _99547 _99546 g (@EMPTY _99546) b)) = True.
Proof. exact (TRANS (@lem3819211 _99546 _99547 b f g h1) (@lem3819215 _99547 b)). Qed.
Lemma lem3819217 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : (term234 _99546 _99547 f g) = (term210 _99547).
Proof. exact (fun_ext (fun b : _99547 => @lem3819216 _99546 _99547 b f g h1)). Qed.
Lemma lem3819218 {_99547 : Type'} : (@all _99547) = (@all _99547).
Proof. exact (eq_refl (@all _99547)). Qed.
Lemma lem3819219 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : (term193 _99546 _99547 f g) = (term212 _99547).
Proof. exact (MK_COMB (@lem3819218 _99547) (@lem3819217 _99546 _99547 f g h1)). Qed.
Lemma lem3819221 {A : Type'} (t : Prop) : (term213 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3819222 {_99547 : Type'} (t : Prop) : (term213 _99547 t) = t.
Proof. exact (@lem3819221 _99547 t). Qed.
Lemma lem3819223 {_99547 : Type'} : (term212 _99547) = True.
Proof. exact (@lem3819222 _99547 True). Qed.
Lemma lem3819224 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : (term193 _99546 _99547 f g) = True.
Proof. exact (TRANS (@lem3819219 _99546 _99547 f g h1) (@lem3819223 _99547)). Qed.
Lemma lem3819225 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : term235 _99546 _99547 f g.
Proof. exact (fun h0 : term116 _99546 _99547 f g => @lem3819224 _99546 _99547 f g h0). Qed.
Lemma lem3819226 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : term236 _99546 _99547 f g.
Proof. exact (@lem3818946 _99546 _99547 f g True). Qed.
Lemma lem3819227 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term237 _99546 _99547 f g) = (term238 _99546 _99547 f g).
Proof. exact (@lem3819226 _99546 _99547 f g (@lem3819225 _99546 _99547 f g)). Qed.
Lemma lem3819229 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem3819230 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term238 _99546 _99547 f g) = True.
Proof. exact (@lem3819229 (term116 _99546 _99547 f g)). Qed.
Lemma lem3819231 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term237 _99546 _99547 f g) = True.
Proof. exact (TRANS (@lem3819227 _99546 _99547 f g) (@lem3819230 _99546 _99547 f g)). Qed.
Lemma lem3819232 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term239 _99546 _99547 f) = (term240 _99546 _99547).
Proof. exact (fun_ext (fun g : type1411 _99546 _99547 => @lem3819231 _99546 _99547 f g)). Qed.
Lemma lem3819233 {_99546 _99547 : Type'} : (@all (_99546 -> _99547 -> _99547)) = (@all (_99546 -> _99547 -> _99547)).
Proof. exact (eq_refl (@all (_99546 -> _99547 -> _99547))). Qed.
Lemma lem3819234 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term241 _99546 _99547 f) = (term242 _99546 _99547).
Proof. exact (MK_COMB (@lem3819233 _99546 _99547) (@lem3819232 _99546 _99547 f)). Qed.
Lemma lem3819236 {A : Type'} (t : Prop) : (term213 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3819237 {_99546 _99547 : Type'} (t : Prop) : (term243 _99546 _99547 t) = t.
Proof. exact (@lem3819236 (type1411 _99546 _99547) t). Qed.
Lemma lem3819238 {_99546 _99547 : Type'} : (term242 _99546 _99547) = True.
Proof. exact (@lem3819237 _99546 _99547 True). Qed.
Lemma lem3819239 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term241 _99546 _99547 f) = True.
Proof. exact (TRANS (@lem3819234 _99546 _99547 f) (@lem3819238 _99546 _99547)). Qed.
Lemma lem3819240 {_99546 _99547 : Type'} : (term244 _99546 _99547) = (term240 _99546 _99547).
Proof. exact (fun_ext (fun f : type1411 _99546 _99547 => @lem3819239 _99546 _99547 f)). Qed.
Lemma lem3819241 {_99546 _99547 : Type'} : (@all (_99546 -> _99547 -> _99547)) = (@all (_99546 -> _99547 -> _99547)).
Proof. exact (eq_refl (@all (_99546 -> _99547 -> _99547))). Qed.
Lemma lem3819242 {_99546 _99547 : Type'} : (term157 _99546 _99547) = (term242 _99546 _99547).
Proof. exact (MK_COMB (@lem3819241 _99546 _99547) (@lem3819240 _99546 _99547)). Qed.
Lemma lem3819244 {A : Type'} (t : Prop) : (term213 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3819245 {_99546 _99547 : Type'} (t : Prop) : (term243 _99546 _99547 t) = t.
Proof. exact (@lem3819244 (type1411 _99546 _99547) t). Qed.
Lemma lem3819246 {_99546 _99547 : Type'} : (term242 _99546 _99547) = True.
Proof. exact (@lem3819245 _99546 _99547 True). Qed.
Lemma lem3819247 {_99546 _99547 : Type'} : (term157 _99546 _99547) = True.
Proof. exact (TRANS (@lem3819242 _99546 _99547) (@lem3819246 _99546 _99547)). Qed.
Lemma lem3819248 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3819249 {_99546 _99547 : Type'} : (term159 _99546 _99547) = (and True).
Proof. exact (MK_COMB (@lem3819248) (@lem3819247 _99546 _99547)). Qed.
Lemma lem3819261 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term188 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem3819262 (p : Prop) (q : Prop) (p' : Prop) : term189 p q p'.
Proof. exact (fun q' : Prop => @lem3819261 p q p' q'). Qed.
Lemma lem3819263 (p : Prop) (q : Prop) : term190 p q.
Proof. exact (fun p' : Prop => @lem3819262 p q p'). Qed.
Lemma lem3819264 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) : term245 _99546 _99547 x s.
Proof. exact (@lem3819263 (term165 _99546 _99547 x s) (term169 _99546 _99547 x s)). Qed.
Lemma lem3819265 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (p' : Prop) : term246 _99546 _99547 x s p'.
Proof. exact (@lem3819264 _99546 _99547 x s p'). Qed.
Lemma lem3819266 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (p' : Prop) : (term246 _99546 _99547 x s p') = (term247 _99546 _99547 x s p').
Proof. exact (eq_refl (term246 _99546 _99547 x s p')). Qed.
Lemma lem3819267 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (p' : Prop) : term247 _99546 _99547 x s p'.
Proof. exact (EQ_MP (@lem3819266 _99546 _99547 x s p') (@lem3819265 _99546 _99547 x s p')). Qed.
Lemma lem3819268 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (p' : Prop) (q' : Prop) : term248 _99546 _99547 x s p' q'.
Proof. exact (@lem3819267 _99546 _99547 x s p' q'). Qed.
Lemma lem3819269 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (p' : Prop) (q' : Prop) : (term248 _99546 _99547 x s p' q') = (term249 _99546 _99547 x s p' q').
Proof. exact (eq_refl (term248 _99546 _99547 x s p' q')). Qed.
Lemma lem3819270 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (p' : Prop) (q' : Prop) : term249 _99546 _99547 x s p' q'.
Proof. exact (EQ_MP (@lem3819269 _99546 _99547 x s p' q') (@lem3819268 _99546 _99547 x s p' q')). Qed.
Lemma lem3819664 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) : (term165 _99546 _99547 x s) = (term165 _99546 _99547 x s).
Proof. exact (eq_refl (term165 _99546 _99547 x s)). Qed.
Lemma lem3819665 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (q' : Prop) : term250 _99546 _99547 x s q'.
Proof. exact (@lem3819270 _99546 _99547 x s (term165 _99546 _99547 x s) q'). Qed.
Lemma lem3819666 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (q' : Prop) : term251 _99546 _99547 x s q'.
Proof. exact (@lem3819665 _99546 _99547 x s q' (@lem3819664 _99546 _99547 x s)). Qed.
Lemma lem3819667 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (h1 : term165 _99546 _99547 x s) : term165 _99546 _99547 x s.
Proof. exact (h1). Qed.
Lemma lem3819668 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (h1 : term165 _99546 _99547 x s) : term163 _99546 x s.
Proof. exact (proj2 (@lem3819667 _99546 _99547 x s h1)). Qed.
Lemma lem3819669 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (h1 : term165 _99546 _99547 x s) : @FINITE _99546 s.
Proof. exact (proj2 (@lem3819668 _99546 _99547 x s h1)). Qed.
Lemma lem3819670 {_99546 : Type'} (s : _99546 -> Prop) : (@FINITE _99546 s) = ((@FINITE _99546 s) = True).
Proof. exact (@lem7 (@FINITE _99546 s)). Qed.
Lemma lem3819672 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (h1 : term165 _99546 _99547 x s) : term252 _99546 x s.
Proof. exact (proj1 (@lem3819668 _99546 _99547 x s h1)). Qed.
Lemma lem3819673 {_99546 : Type'} (x : _99546) (s : _99546 -> Prop) : term253 _99546 x s.
Proof. exact (@lem82 (@IN _99546 x s)). Qed.
Lemma lem3819703 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term188 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem3819704 (p : Prop) (q : Prop) (p' : Prop) : term189 p q p'.
Proof. exact (fun q' : Prop => @lem3819703 p q p' q'). Qed.
Lemma lem3819705 (p : Prop) (q : Prop) : term190 p q.
Proof. exact (fun p' : Prop => @lem3819704 p q p'). Qed.
Lemma lem3819706 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (s : _99546 -> Prop) : term254 _99546 _99547 f g x s.
Proof. exact (@lem3819705 (term255 _99546 _99547 x s f g) (term256 _99546 _99547 f g x s)). Qed.
Lemma lem3819707 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (s : _99546 -> Prop) (p' : Prop) : term257 _99546 _99547 f g x s p'.
Proof. exact (@lem3819706 _99546 _99547 f g x s p'). Qed.
Lemma lem3819708 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (s : _99546 -> Prop) (p' : Prop) : (term257 _99546 _99547 f g x s p') = (term258 _99546 _99547 f g x s p').
Proof. exact (eq_refl (term257 _99546 _99547 f g x s p')). Qed.
Lemma lem3819709 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (s : _99546 -> Prop) (p' : Prop) : term258 _99546 _99547 f g x s p'.
Proof. exact (EQ_MP (@lem3819708 _99546 _99547 f g x s p') (@lem3819707 _99546 _99547 f g x s p')). Qed.
Lemma lem3819710 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (s : _99546 -> Prop) (p' : Prop) (q' : Prop) : term259 _99546 _99547 f g x s p' q'.
Proof. exact (@lem3819709 _99546 _99547 f g x s p' q'). Qed.
Lemma lem3819711 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (s : _99546 -> Prop) (p' : Prop) (q' : Prop) : (term259 _99546 _99547 f g x s p' q') = (term260 _99546 _99547 f g x s p' q').
Proof. exact (eq_refl (term259 _99546 _99547 f g x s p' q')). Qed.
Lemma lem3819712 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (s : _99546 -> Prop) (p' : Prop) (q' : Prop) : term260 _99546 _99547 f g x s p' q'.
Proof. exact (EQ_MP (@lem3819711 _99546 _99547 f g x s p' q') (@lem3819710 _99546 _99547 f g x s p' q')). Qed.
Lemma lem3819722 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term188 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem3819723 (p : Prop) (q : Prop) (p' : Prop) : term189 p q p'.
Proof. exact (fun q' : Prop => @lem3819722 p q p' q'). Qed.
Lemma lem3819724 (p : Prop) (q : Prop) : term190 p q.
Proof. exact (fun p' : Prop => @lem3819723 p q p'). Qed.
Lemma lem3819725 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x' : _99546) : term261 _99546 _99547 x s f g x'.
Proof. exact (@lem3819724 (term10 _99546 x' x s) ((f x') = (g x'))). Qed.
Lemma lem3819726 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x' : _99546) (p' : Prop) : term262 _99546 _99547 x s f g x' p'.
Proof. exact (@lem3819725 _99546 _99547 x s f g x' p'). Qed.
Lemma lem3819727 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x' : _99546) (p' : Prop) : (term262 _99546 _99547 x s f g x' p') = (term263 _99546 _99547 x s f g x' p').
Proof. exact (eq_refl (term262 _99546 _99547 x s f g x' p')). Qed.
Lemma lem3819728 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x' : _99546) (p' : Prop) : term263 _99546 _99547 x s f g x' p'.
Proof. exact (EQ_MP (@lem3819727 _99546 _99547 x s f g x' p') (@lem3819726 _99546 _99547 x s f g x' p')). Qed.
Lemma lem3819729 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x' : _99546) (p' : Prop) (q' : Prop) : term264 _99546 _99547 x s f g x' p' q'.
Proof. exact (@lem3819728 _99546 _99547 x s f g x' p' q'). Qed.
Lemma lem3819730 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x' : _99546) (p' : Prop) (q' : Prop) : (term264 _99546 _99547 x s f g x' p' q') = (term265 _99546 _99547 x s f g x' p' q').
Proof. exact (eq_refl (term264 _99546 _99547 x s f g x' p' q')). Qed.
Lemma lem3819731 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x' : _99546) (p' : Prop) (q' : Prop) : term265 _99546 _99547 x s f g x' p' q'.
Proof. exact (EQ_MP (@lem3819730 _99546 _99547 x s f g x' p' q') (@lem3819729 _99546 _99547 x s f g x' p' q')). Qed.
Lemma lem3819733 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term10 A x y s) = (term11 A y x s).
Proof. exact (EQ_MP (@lem3817883 A y x s) (@lem3817882 A y x s)). Qed.
Lemma lem3819734 {_99546 : Type'} (y : _99546) (x : _99546) (s : _99546 -> Prop) : (term10 _99546 x y s) = (term11 _99546 y x s).
Proof. exact (@lem3819733 _99546 y x s). Qed.
Lemma lem3819735 {_99546 : Type'} (x : _99546) (x' : _99546) (s : _99546 -> Prop) : (term10 _99546 x' x s) = (term11 _99546 x x' s).
Proof. exact (@lem3819734 _99546 x x' s). Qed.
Lemma lem3819740 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (x' : _99546) (s : _99546 -> Prop) (q' : Prop) : term266 _99546 _99547 f g x x' s q'.
Proof. exact (@lem3819731 _99546 _99547 x s f g x' (term11 _99546 x x' s) q'). Qed.
Lemma lem3819741 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (x' : _99546) (s : _99546 -> Prop) (q' : Prop) : term267 _99546 _99547 f g x x' s q'.
Proof. exact (@lem3819740 _99546 _99547 f g x x' s q' (@lem3819735 _99546 x x' s)). Qed.
Lemma lem3819747 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x' : _99546) : ((f x') = (g x')) = ((f x') = (g x')).
Proof. exact (eq_refl ((f x') = (g x'))). Qed.
Lemma lem3819748 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x' : _99546) : term268 _99546 _99547 x s f g x'.
Proof. exact (fun h0 : term11 _99546 x x' s => @lem3819747 _99546 _99547 f g x'). Qed.
Lemma lem3819749 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x' : _99546) : term269 _99546 _99547 x s f g x'.
Proof. exact (@lem3819741 _99546 _99547 f g x x' s ((f x') = (g x'))). Qed.
Lemma lem3819750 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x' : _99546) : (term270 _99546 _99547 x s f g x') = (term271 _99546 _99547 x s f g x').
Proof. exact (@lem3819749 _99546 _99547 x s f g x' (@lem3819748 _99546 _99547 x s f g x')). Qed.
Lemma lem3819786 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term272 _99546 _99547 x s f g) = (term273 _99546 _99547 x s f g).
Proof. exact (fun_ext (fun x' : _99546 => @lem3819750 _99546 _99547 x s f g x')). Qed.
Lemma lem3819822 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3819823 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term274 _99546 _99547 x s f g) = (term275 _99546 _99547 x s f g).
Proof. exact (MK_COMB (@lem3819822 _99546) (@lem3819786 _99546 _99547 x s f g)). Qed.
Lemma lem3819863 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3819864 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term276 _99546 _99547 x s f g) = (term277 _99546 _99547 x s f g).
Proof. exact (MK_COMB (@lem3819863) (@lem3819823 _99546 _99547 x s f g)). Qed.
Lemma lem3820022 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term116 _99546 _99547 f g) = (term116 _99546 _99547 f g).
Proof. exact (eq_refl (term116 _99546 _99547 f g)). Qed.
Lemma lem3820023 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term255 _99546 _99547 x s f g) = (term278 _99546 _99547 x s f g).
Proof. exact (MK_COMB (@lem3819864 _99546 _99547 x s f g) (@lem3820022 _99546 _99547 f g)). Qed.
Lemma lem3820183 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (q' : Prop) : term279 _99546 _99547 x s f g q'.
Proof. exact (@lem3819712 _99546 _99547 f g x s (term278 _99546 _99547 x s f g) q'). Qed.
Lemma lem3820184 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (q' : Prop) : term280 _99546 _99547 x s f g q'.
Proof. exact (@lem3820183 _99546 _99547 x s f g q' (@lem3820023 _99546 _99547 x s f g)). Qed.
Lemma lem3820185 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s f g) : term278 _99546 _99547 x s f g.
Proof. exact (h1). Qed.
Lemma lem3820186 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s f g) : term116 _99546 _99547 f g.
Proof. exact (proj2 (@lem3820185 _99546 _99547 x s f g h1)). Qed.
Lemma lem3820187 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s f g) : term112 _99546 _99547 g.
Proof. exact (proj2 (@lem3820186 _99546 _99547 x s f g h1)). Qed.
Lemma lem3820188 {_99546 _99547 : Type'} (x' : _99546) (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s f g) : term218 _99546 _99547 g x'.
Proof. exact (@lem3820187 _99546 _99547 x s f g h1 x'). Qed.
Lemma lem3820189 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x' : _99546) : (term218 _99546 _99547 g x') = (term109 _99546 _99547 g x').
Proof. exact (eq_refl (term218 _99546 _99547 g x')). Qed.
Lemma lem3820190 {_99546 _99547 : Type'} (x' : _99546) (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s f g) : term109 _99546 _99547 g x'.
Proof. exact (EQ_MP (@lem3820189 _99546 _99547 g x') (@lem3820188 _99546 _99547 x' x s f g h1)). Qed.
Lemma lem3820191 {_99546 _99547 : Type'} (x' : _99546) (y : _99546) (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s f g) : term219 _99546 _99547 g x' y.
Proof. exact (@lem3820190 _99546 _99547 x' x s f g h1 y). Qed.
Lemma lem3820192 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x' : _99546) : (term219 _99546 _99547 g x' y) = (term105 _99546 _99547 y g x').
Proof. exact (eq_refl (term219 _99546 _99547 g x' y)). Qed.
Lemma lem3820193 {_99546 _99547 : Type'} (y : _99546) (x' : _99546) (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s f g) : term105 _99546 _99547 y g x'.
Proof. exact (EQ_MP (@lem3820192 _99546 _99547 y g x') (@lem3820191 _99546 _99547 x' y x s f g h1)). Qed.
Lemma lem3820194 {_99546 : Type'} (x' : _99546) (y : _99546) (h1 : term90 _99546 x' y) : term90 _99546 x' y.
Proof. exact (h1). Qed.
Lemma lem3820195 {_99546 _99547 : Type'} (x' : _99546) (y : _99546) (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term90 _99546 x' y) (h2 : term278 _99546 _99547 x s f g) : term104 _99546 _99547 y g x'.
Proof. exact (@lem3820193 _99546 _99547 y x' x s f g h2 (@lem3820194 _99546 x' y h1)). Qed.
Lemma lem3820196 {_99546 _99547 : Type'} (s : _99547) (x' : _99546) (y : _99546) (x : _99546) (s' : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term90 _99546 x' y) (h2 : term278 _99546 _99547 x s' f g) : term92 _99546 _99547 y g x' s.
Proof. exact (@lem3820195 _99546 _99547 x' y x s' f g h1 h2 s). Qed.
Lemma lem3820197 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x' : _99546) (s : _99547) : (term92 _99546 _99547 y g x' s) = ((term93 _99546 _99547 x' g y s) = (term93 _99546 _99547 y g x' s)).
Proof. exact (eq_refl (term92 _99546 _99547 y g x' s)). Qed.
Lemma lem3820198 {_99546 _99547 : Type'} (s : _99547) (x' : _99546) (y : _99546) (x : _99546) (s' : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term90 _99546 x' y) (h2 : term278 _99546 _99547 x s' f g) : (term93 _99546 _99547 x' g y s) = (term93 _99546 _99547 y g x' s).
Proof. exact (EQ_MP (@lem3820197 _99546 _99547 y g x' s) (@lem3820196 _99546 _99547 s x' y x s' f g h1 h2)). Qed.
Lemma lem3820204 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s f g) : term112 _99546 _99547 f.
Proof. exact (proj1 (@lem3820186 _99546 _99547 x s f g h1)). Qed.
Lemma lem3820205 {_99546 _99547 : Type'} (x' : _99546) (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s f g) : term218 _99546 _99547 f x'.
Proof. exact (@lem3820204 _99546 _99547 x s f g h1 x'). Qed.
Lemma lem3820206 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x' : _99546) : (term218 _99546 _99547 f x') = (term109 _99546 _99547 f x').
Proof. exact (eq_refl (term218 _99546 _99547 f x')). Qed.
Lemma lem3820207 {_99546 _99547 : Type'} (x' : _99546) (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s f g) : term109 _99546 _99547 f x'.
Proof. exact (EQ_MP (@lem3820206 _99546 _99547 f x') (@lem3820205 _99546 _99547 x' x s f g h1)). Qed.
Lemma lem3820208 {_99546 _99547 : Type'} (x' : _99546) (y : _99546) (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s f g) : term219 _99546 _99547 f x' y.
Proof. exact (@lem3820207 _99546 _99547 x' x s f g h1 y). Qed.
Lemma lem3820209 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x' : _99546) : (term219 _99546 _99547 f x' y) = (term105 _99546 _99547 y f x').
Proof. exact (eq_refl (term219 _99546 _99547 f x' y)). Qed.
Lemma lem3820210 {_99546 _99547 : Type'} (y : _99546) (x' : _99546) (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s f g) : term105 _99546 _99547 y f x'.
Proof. exact (EQ_MP (@lem3820209 _99546 _99547 y f x') (@lem3820208 _99546 _99547 x' y x s f g h1)). Qed.
Lemma lem3820211 {_99546 : Type'} (x' : _99546) (y : _99546) (h1 : term90 _99546 x' y) : term90 _99546 x' y.
Proof. exact (h1). Qed.
Lemma lem3820212 {_99546 _99547 : Type'} (x' : _99546) (y : _99546) (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term90 _99546 x' y) (h2 : term278 _99546 _99547 x s f g) : term104 _99546 _99547 y f x'.
Proof. exact (@lem3820210 _99546 _99547 y x' x s f g h2 (@lem3820211 _99546 x' y h1)). Qed.
Lemma lem3820213 {_99546 _99547 : Type'} (s : _99547) (x' : _99546) (y : _99546) (x : _99546) (s' : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term90 _99546 x' y) (h2 : term278 _99546 _99547 x s' f g) : term92 _99546 _99547 y f x' s.
Proof. exact (@lem3820212 _99546 _99547 x' y x s' f g h1 h2 s). Qed.
Lemma lem3820214 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x' : _99546) (s : _99547) : (term92 _99546 _99547 y f x' s) = ((term93 _99546 _99547 x' f y s) = (term93 _99546 _99547 y f x' s)).
Proof. exact (eq_refl (term92 _99546 _99547 y f x' s)). Qed.
Lemma lem3820215 {_99546 _99547 : Type'} (s : _99547) (x' : _99546) (y : _99546) (x : _99546) (s' : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term90 _99546 x' y) (h2 : term278 _99546 _99547 x s' f g) : (term93 _99546 _99547 x' f y s) = (term93 _99546 _99547 y f x' s).
Proof. exact (EQ_MP (@lem3820214 _99546 _99547 y f x' s) (@lem3820213 _99546 _99547 s x' y x s' f g h1 h2)). Qed.
Lemma lem3820221 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s f g) : term275 _99546 _99547 x s f g.
Proof. exact (proj1 (@lem3820185 _99546 _99547 x s f g h1)). Qed.
Lemma lem3820222 {_99546 _99547 : Type'} (x' : _99546) (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s f g) : term281 _99546 _99547 x s f g x'.
Proof. exact (@lem3820221 _99546 _99547 x s f g h1 x'). Qed.
Lemma lem3820223 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x' : _99546) : (term281 _99546 _99547 x s f g x') = (term271 _99546 _99547 x s f g x').
Proof. exact (eq_refl (term281 _99546 _99547 x s f g x')). Qed.
Lemma lem3820224 {_99546 _99547 : Type'} (x' : _99546) (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s f g) : term271 _99546 _99547 x s f g x'.
Proof. exact (EQ_MP (@lem3820223 _99546 _99547 x s f g x') (@lem3820222 _99546 _99547 x' x s f g h1)). Qed.
Lemma lem3820225 {_99546 : Type'} (x : _99546) (x' : _99546) (s : _99546 -> Prop) (h1 : term11 _99546 x x' s) : term11 _99546 x x' s.
Proof. exact (h1). Qed.
Lemma lem3820226 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (x' : _99546) (s : _99546 -> Prop) (h1 : term278 _99546 _99547 x s f g) (h2 : term11 _99546 x x' s) : (f x') = (g x').
Proof. exact (@lem3820224 _99546 _99547 x' x s f g h1 (@lem3820225 _99546 x x' s h2)). Qed.
Lemma lem3820239 {A B : Type'} (x : A) (f : type1411 A B) (s : A -> Prop) (b : B) : term31 A B x f s b.
Proof. exact (EQ_MP (@lem3817915 A B x f s b) (@lem3817908 A B x f s b)). Qed.
Lemma lem3820240 {_99546 _99547 : Type'} (x : _99546) (f : type1411 _99546 _99547) (s : _99546 -> Prop) (b : _99547) : term31 _99546 _99547 x f s b.
Proof. exact (@lem3820239 _99546 _99547 x f s b). Qed.
Lemma lem3820485 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term188 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem3820486 (p : Prop) (q : Prop) (p' : Prop) : term189 p q p'.
Proof. exact (fun q' : Prop => @lem3820485 p q p' q'). Qed.
Lemma lem3820487 (p : Prop) (q : Prop) : term190 p q.
Proof. exact (fun p' : Prop => @lem3820486 p q p'). Qed.
Lemma lem3820488 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (_44387 : _99546) (s : _99547) : term221 _99546 _99547 y f _44387 s.
Proof. exact (@lem3820487 (term90 _99546 _44387 y) ((term93 _99546 _99547 _44387 f y s) = (term93 _99546 _99547 y f _44387 s))). Qed.
Lemma lem3820489 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (_44387 : _99546) (s : _99547) (p' : Prop) : term222 _99546 _99547 y f _44387 s p'.
Proof. exact (@lem3820488 _99546 _99547 y f _44387 s p'). Qed.
Lemma lem3820490 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (_44387 : _99546) (s : _99547) (p' : Prop) : (term222 _99546 _99547 y f _44387 s p') = (term223 _99546 _99547 y f _44387 s p').
Proof. exact (eq_refl (term222 _99546 _99547 y f _44387 s p')). Qed.
Lemma lem3820491 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (_44387 : _99546) (s : _99547) (p' : Prop) : term223 _99546 _99547 y f _44387 s p'.
Proof. exact (EQ_MP (@lem3820490 _99546 _99547 y f _44387 s p') (@lem3820489 _99546 _99547 y f _44387 s p')). Qed.
Lemma lem3820492 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (_44387 : _99546) (s : _99547) (p' : Prop) (q' : Prop) : term224 _99546 _99547 y f _44387 s p' q'.
Proof. exact (@lem3820491 _99546 _99547 y f _44387 s p' q'). Qed.
Lemma lem3820493 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (_44387 : _99546) (s : _99547) (p' : Prop) (q' : Prop) : (term224 _99546 _99547 y f _44387 s p' q') = (term225 _99546 _99547 y f _44387 s p' q').
Proof. exact (eq_refl (term224 _99546 _99547 y f _44387 s p' q')). Qed.
Lemma lem3820494 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (_44387 : _99546) (s : _99547) (p' : Prop) (q' : Prop) : term225 _99546 _99547 y f _44387 s p' q'.
Proof. exact (EQ_MP (@lem3820493 _99546 _99547 y f _44387 s p' q') (@lem3820492 _99546 _99547 y f _44387 s p' q')). Qed.
Lemma lem3820497 {_99546 : Type'} (_44387 : _99546) (y : _99546) : (term90 _99546 _44387 y) = (term90 _99546 _44387 y).
Proof. exact (eq_refl (term90 _99546 _44387 y)). Qed.
Lemma lem3820498 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99547) (_44387 : _99546) (y : _99546) (q' : Prop) : term226 _99546 _99547 f s _44387 y q'.
Proof. exact (@lem3820494 _99546 _99547 y f _44387 s (term90 _99546 _44387 y) q'). Qed.
Lemma lem3820499 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99547) (_44387 : _99546) (y : _99546) (q' : Prop) : term227 _99546 _99547 f s _44387 y q'.
Proof. exact (@lem3820498 _99546 _99547 f s _44387 y q' (@lem3820497 _99546 _44387 y)). Qed.
Lemma lem3820500 {_99546 : Type'} (_44387 : _99546) (y : _99546) (h1 : term90 _99546 _44387 y) : term90 _99546 _44387 y.
Proof. exact (h1). Qed.
Lemma lem3820504 {_99546 : Type'} (_44387 : _99546) (y : _99546) (h1 : _44387 = y) : _44387 = y.
Proof. exact (h1). Qed.
Lemma lem3820505 {_99546 : Type'} (_44387 : _99546) (y : _99546) (h1 : _44387 = y) : y = _44387.
Proof. exact (SYM (@lem3820504 _99546 _44387 y h1)). Qed.
Lemma lem3820506 {_99546 : Type'} (y : _99546) (_44387 : _99546) (h1 : y = _44387) : y = _44387.
Proof. exact (h1). Qed.
Lemma lem3820507 {_99546 : Type'} (y : _99546) (_44387 : _99546) (h1 : y = _44387) : _44387 = y.
Proof. exact (SYM (@lem3820506 _99546 y _44387 h1)). Qed.
Lemma lem3820508 {_99546 : Type'} (y : _99546) (_44387 : _99546) : (_44387 = y) = (y = _44387).
Proof. exact (prop_ext (fun h1 : _44387 = y => @lem3820505 _99546 _44387 y h1) (fun h1 : y = _44387 => @lem3820507 _99546 y _44387 h1)). Qed.
Lemma lem3820509 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3820510 {_99546 : Type'} (y : _99546) (_44387 : _99546) : (term90 _99546 _44387 y) = (term90 _99546 y _44387).
Proof. exact (MK_COMB (@lem3820509) (@lem3820508 _99546 y _44387)). Qed.
Lemma lem3820511 {_99546 : Type'} (_44387 : _99546) (y : _99546) (h1 : term90 _99546 _44387 y) : term90 _99546 y _44387.
Proof. exact (EQ_MP (@lem3820510 _99546 y _44387) (@lem3820500 _99546 _44387 y h1)). Qed.
Lemma lem3820512 {_99546 : Type'} (y : _99546) (_44387 : _99546) : term228 _99546 y _44387.
Proof. exact (@lem82 (y = _44387)). Qed.
Lemma lem3820541 {_99546 _99547 : Type'} (y : _99546) (x' : _99546) (s : _99547) (x : _99546) (s' : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s' f g) : term96 _99546 _99547 y f x' s.
Proof. exact (fun h0 : term90 _99546 x' y => @lem3820215 _99546 _99547 s x' y x s' f g h0 h1). Qed.
Lemma lem3820542 {_99546 _99547 : Type'} (y : _99546) (x' : _99546) (s : _99547) (x : _99546) (s' : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s' f g) : term96 _99546 _99547 y f x' s.
Proof. exact (@lem3820541 _99546 _99547 y x' s x s' f g h1). Qed.
Lemma lem3820543 {_99546 _99547 : Type'} (_44387 : _99546) (y : _99546) (s : _99547) (x : _99546) (s' : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s' f g) : term96 _99546 _99547 _44387 f y s.
Proof. exact (@lem3820542 _99546 _99547 _44387 y s x s' f g h1). Qed.
Lemma lem3820545 {_99546 : Type'} (_44387 : _99546) (y : _99546) (h1 : term90 _99546 _44387 y) : (y = _44387) = False.
Proof. exact (@lem3820512 _99546 y _44387 (@lem3820511 _99546 _44387 y h1)). Qed.
Lemma lem3820546 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3820547 {_99546 : Type'} (_44387 : _99546) (y : _99546) (h1 : term90 _99546 _44387 y) : (term90 _99546 y _44387) = (~ False).
Proof. exact (MK_COMB (@lem3820546) (@lem3820545 _99546 _44387 y h1)). Qed.
Lemma lem3820549 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3820550 {_99546 : Type'} (_44387 : _99546) (y : _99546) (h1 : term90 _99546 _44387 y) : (term90 _99546 y _44387) = True.
Proof. exact (TRANS (@lem3820547 _99546 _44387 y h1) (@lem3820549)). Qed.
Lemma lem3820551 {_99546 : Type'} (_44387 : _99546) (y : _99546) (h1 : term90 _99546 _44387 y) : True = (term90 _99546 y _44387).
Proof. exact (SYM (@lem3820550 _99546 _44387 y h1)). Qed.
Lemma lem3820552 {_99546 : Type'} (_44387 : _99546) (y : _99546) (h1 : term90 _99546 _44387 y) : term90 _99546 y _44387.
Proof. exact (EQ_MP (@lem3820551 _99546 _44387 y h1) (@lem0)). Qed.
Lemma lem3820553 {_99546 _99547 : Type'} (s : _99547) (_44387 : _99546) (y : _99546) (x : _99546) (s' : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term90 _99546 _44387 y) (h2 : term278 _99546 _99547 x s' f g) : (term93 _99546 _99547 y f _44387 s) = (term93 _99546 _99547 _44387 f y s).
Proof. exact (@lem3820543 _99546 _99547 _44387 y s x s' f g h2 (@lem3820552 _99546 _44387 y h1)). Qed.
Lemma lem3820578 {_99546 _99547 : Type'} (_44387 : _99546) (f : type1411 _99546 _99547) (y : _99546) (s : _99547) : (term229 _99546 _99547 _44387 f y s) = (term229 _99546 _99547 _44387 f y s).
Proof. exact (eq_refl (term229 _99546 _99547 _44387 f y s)). Qed.
Lemma lem3820579 {_99546 _99547 : Type'} (s : _99547) (_44387 : _99546) (y : _99546) (x : _99546) (s' : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term90 _99546 _44387 y) (h2 : term278 _99546 _99547 x s' f g) : ((term93 _99546 _99547 _44387 f y s) = (term93 _99546 _99547 y f _44387 s)) = ((term93 _99546 _99547 _44387 f y s) = (term93 _99546 _99547 _44387 f y s)).
Proof. exact (MK_COMB (@lem3820578 _99546 _99547 _44387 f y s) (@lem3820553 _99546 _99547 s _44387 y x s' f g h1 h2)). Qed.
Lemma lem3820581 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3820582 {_99547 : Type'} (x : _99547) : (x = x) = True.
Proof. exact (@lem3820581 _99547 x). Qed.
Lemma lem3820583 {_99546 _99547 : Type'} (_44387 : _99546) (f : type1411 _99546 _99547) (y : _99546) (s : _99547) : ((term93 _99546 _99547 _44387 f y s) = (term93 _99546 _99547 _44387 f y s)) = True.
Proof. exact (@lem3820582 _99547 (term93 _99546 _99547 _44387 f y s)). Qed.
Lemma lem3820584 {_99546 _99547 : Type'} (s : _99547) (_44387 : _99546) (y : _99546) (x : _99546) (s' : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term90 _99546 _44387 y) (h2 : term278 _99546 _99547 x s' f g) : ((term93 _99546 _99547 _44387 f y s) = (term93 _99546 _99547 y f _44387 s)) = True.
Proof. exact (TRANS (@lem3820579 _99546 _99547 s _44387 y x s' f g h1 h2) (@lem3820583 _99546 _99547 _44387 f y s)). Qed.
Lemma lem3820585 {_99546 _99547 : Type'} (y : _99546) (_44387 : _99546) (s : _99547) (x : _99546) (s' : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s' f g) : term230 _99546 _99547 y f _44387 s.
Proof. exact (fun h0 : term90 _99546 _44387 y => @lem3820584 _99546 _99547 s _44387 y x s' f g h0 h1). Qed.
Lemma lem3820586 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99547) (_44387 : _99546) (y : _99546) : term231 _99546 _99547 f s _44387 y.
Proof. exact (@lem3820499 _99546 _99547 f s _44387 y True). Qed.
Lemma lem3820587 {_99546 _99547 : Type'} (s : _99547) (_44387 : _99546) (y : _99546) (x : _99546) (s' : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s' f g) : (term96 _99546 _99547 y f _44387 s) = (term232 _99546 _44387 y).
Proof. exact (@lem3820586 _99546 _99547 f s _44387 y (@lem3820585 _99546 _99547 y _44387 s x s' f g h1)). Qed.
Lemma lem3820589 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem3820590 {_99546 : Type'} (_44387 : _99546) (y : _99546) : (term232 _99546 _44387 y) = True.
Proof. exact (@lem3820589 (term90 _99546 _44387 y)). Qed.
Lemma lem3820591 {_99546 _99547 : Type'} (y : _99546) (_44387 : _99546) (s : _99547) (x : _99546) (s' : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s' f g) : (term96 _99546 _99547 y f _44387 s) = True.
Proof. exact (TRANS (@lem3820587 _99546 _99547 s _44387 y x s' f g h1) (@lem3820590 _99546 _44387 y)). Qed.
Lemma lem3820592 {_99546 _99547 : Type'} (y : _99546) (_44387 : _99546) (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s f g) : (term98 _99546 _99547 y f _44387) = (term210 _99547).
Proof. exact (fun_ext (fun s' : _99547 => @lem3820591 _99546 _99547 y _44387 s' x s f g h1)). Qed.
Lemma lem3820593 {_99547 : Type'} : (@all _99547) = (@all _99547).
Proof. exact (eq_refl (@all _99547)). Qed.
Lemma lem3820594 {_99546 _99547 : Type'} (y : _99546) (_44387 : _99546) (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s f g) : (term99 _99546 _99547 y f _44387) = (term212 _99547).
Proof. exact (MK_COMB (@lem3820593 _99547) (@lem3820592 _99546 _99547 y _44387 x s f g h1)). Qed.
Lemma lem3820596 {A : Type'} (t : Prop) : (term213 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3820597 {_99547 : Type'} (t : Prop) : (term213 _99547 t) = t.
Proof. exact (@lem3820596 _99547 t). Qed.
Lemma lem3820598 {_99547 : Type'} : (term212 _99547) = True.
Proof. exact (@lem3820597 _99547 True). Qed.
Lemma lem3820599 {_99546 _99547 : Type'} (y : _99546) (_44387 : _99546) (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s f g) : (term99 _99546 _99547 y f _44387) = True.
Proof. exact (TRANS (@lem3820594 _99546 _99547 y _44387 x s f g h1) (@lem3820598 _99547)). Qed.
Lemma lem3820600 {_99546 _99547 : Type'} (_44387 : _99546) (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s f g) : (term106 _99546 _99547 f _44387) = (term210 _99546).
Proof. exact (fun_ext (fun y : _99546 => @lem3820599 _99546 _99547 y _44387 x s f g h1)). Qed.
Lemma lem3820601 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3820602 {_99546 _99547 : Type'} (_44387 : _99546) (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s f g) : (term108 _99546 _99547 f _44387) = (term212 _99546).
Proof. exact (MK_COMB (@lem3820601 _99546) (@lem3820600 _99546 _99547 _44387 x s f g h1)). Qed.
Lemma lem3820604 {A : Type'} (t : Prop) : (term213 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3820605 {_99546 : Type'} (t : Prop) : (term213 _99546 t) = t.
Proof. exact (@lem3820604 _99546 t). Qed.
Lemma lem3820606 {_99546 : Type'} : (term212 _99546) = True.
Proof. exact (@lem3820605 _99546 True). Qed.
Lemma lem3820607 {_99546 _99547 : Type'} (_44387 : _99546) (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s f g) : (term108 _99546 _99547 f _44387) = True.
Proof. exact (TRANS (@lem3820602 _99546 _99547 _44387 x s f g h1) (@lem3820606 _99546)). Qed.
Lemma lem3820610 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s f g) : (term110 _99546 _99547 f) = (term210 _99546).
Proof. exact (fun_ext (fun _44387 : _99546 => @lem3820607 _99546 _99547 _44387 x s f g h1)). Qed.
Lemma lem3820611 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3820612 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s f g) : (term19 _99546 _99547 f) = (term212 _99546).
Proof. exact (MK_COMB (@lem3820611 _99546) (@lem3820610 _99546 _99547 x s f g h1)). Qed.
Lemma lem3820614 {A : Type'} (t : Prop) : (term213 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3820615 {_99546 : Type'} (t : Prop) : (term213 _99546 t) = t.
Proof. exact (@lem3820614 _99546 t). Qed.
Lemma lem3820616 {_99546 : Type'} : (term212 _99546) = True.
Proof. exact (@lem3820615 _99546 True). Qed.
Lemma lem3820617 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s f g) : (term19 _99546 _99547 f) = True.
Proof. exact (TRANS (@lem3820612 _99546 _99547 x s f g h1) (@lem3820616 _99546)). Qed.
Lemma lem3820618 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3820619 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s f g) : (term113 _99546 _99547 f) = (and True).
Proof. exact (MK_COMB (@lem3820618) (@lem3820617 _99546 _99547 x s f g h1)). Qed.
Lemma lem3820621 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (h1 : term165 _99546 _99547 x s) : (@FINITE _99546 s) = True.
Proof. exact (EQ_MP (@lem3819670 _99546 s) (@lem3819669 _99546 _99547 x s h1)). Qed.
Lemma lem3820622 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term278 _99546 _99547 x s f g) (h2 : term165 _99546 _99547 x s) : (term282 _99546 _99547 f s) = (True /\ True).
Proof. exact (MK_COMB (@lem3820619 _99546 _99547 x s f g h1) (@lem3820621 _99546 _99547 x s h2)). Qed.
Lemma lem3820624 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3820625 : (True /\ True) = True.
Proof. exact (@lem3820624 True). Qed.
Lemma lem3820626 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term278 _99546 _99547 x s f g) (h2 : term165 _99546 _99547 x s) : (term282 _99546 _99547 f s) = True.
Proof. exact (TRANS (@lem3820622 _99546 _99547 f g x s h1 h2) (@lem3820625)). Qed.
Lemma lem3820627 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term278 _99546 _99547 x s f g) (h2 : term165 _99546 _99547 x s) : True = (term282 _99546 _99547 f s).
Proof. exact (SYM (@lem3820626 _99546 _99547 f g x s h1 h2)). Qed.
Lemma lem3820628 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term278 _99546 _99547 x s f g) (h2 : term165 _99546 _99547 x s) : term282 _99546 _99547 f s.
Proof. exact (EQ_MP (@lem3820627 _99546 _99547 f g x s h1 h2) (@lem0)). Qed.
Lemma lem3820629 {_99546 _99547 : Type'} (b : _99547) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term278 _99546 _99547 x s f g) (h2 : term165 _99546 _99547 x s) : (term26 _99546 _99547 f x s b) = (term27 _99546 _99547 x f s b).
Proof. exact (@lem3820240 _99546 _99547 x f s b (@lem3820628 _99546 _99547 f g x s h1 h2)). Qed.
Lemma lem3820631 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term283 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem3820632 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term284 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem3820631 _2963 g t e g' t' e'). Qed.
Lemma lem3820633 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term285 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem3820632 _2963 g t e g' t'). Qed.
Lemma lem3820634 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term286 _2963 g t e.
Proof. exact (fun g' : Prop => @lem3820633 _2963 g t e g'). Qed.
Lemma lem3820635 {_99547 : Type'} (g : Prop) (t : _99547) (e : _99547) : term286 _99547 g t e.
Proof. exact (@lem3820634 _99547 g t e). Qed.
Lemma lem3820636 {_99546 _99547 : Type'} (x : _99546) (f : type1411 _99546 _99547) (s : _99546 -> Prop) (b : _99547) : term287 _99546 _99547 x f s b.
Proof. exact (@lem3820635 _99547 (@IN _99546 x s) (@ITSET _99547 _99546 f s b) (term288 _99546 _99547 x f s b)). Qed.
Lemma lem3820637 {_99546 _99547 : Type'} (x : _99546) (f : type1411 _99546 _99547) (s : _99546 -> Prop) (b : _99547) (g' : Prop) : term289 _99546 _99547 x f s b g'.
Proof. exact (@lem3820636 _99546 _99547 x f s b g'). Qed.
Lemma lem3820638 {_99546 _99547 : Type'} (x : _99546) (f : type1411 _99546 _99547) (s : _99546 -> Prop) (b : _99547) (g' : Prop) : (term289 _99546 _99547 x f s b g') = (term290 _99546 _99547 x f s b g').
Proof. exact (eq_refl (term289 _99546 _99547 x f s b g')). Qed.
Lemma lem3820639 {_99546 _99547 : Type'} (x : _99546) (f : type1411 _99546 _99547) (s : _99546 -> Prop) (b : _99547) (g' : Prop) : term290 _99546 _99547 x f s b g'.
Proof. exact (EQ_MP (@lem3820638 _99546 _99547 x f s b g') (@lem3820637 _99546 _99547 x f s b g')). Qed.
Lemma lem3820640 {_99546 _99547 : Type'} (x : _99546) (f : type1411 _99546 _99547) (s : _99546 -> Prop) (b : _99547) (g' : Prop) (t' : _99547) : term291 _99546 _99547 x f s b g' t'.
Proof. exact (@lem3820639 _99546 _99547 x f s b g' t'). Qed.
Lemma lem3820641 {_99546 _99547 : Type'} (x : _99546) (f : type1411 _99546 _99547) (s : _99546 -> Prop) (b : _99547) (g' : Prop) (t' : _99547) : (term291 _99546 _99547 x f s b g' t') = (term292 _99546 _99547 x f s b g' t').
Proof. exact (eq_refl (term291 _99546 _99547 x f s b g' t')). Qed.
Lemma lem3820642 {_99546 _99547 : Type'} (x : _99546) (f : type1411 _99546 _99547) (s : _99546 -> Prop) (b : _99547) (g' : Prop) (t' : _99547) : term292 _99546 _99547 x f s b g' t'.
Proof. exact (EQ_MP (@lem3820641 _99546 _99547 x f s b g' t') (@lem3820640 _99546 _99547 x f s b g' t')). Qed.
Lemma lem3820643 {_99546 _99547 : Type'} (x : _99546) (f : type1411 _99546 _99547) (s : _99546 -> Prop) (b : _99547) (g' : Prop) (t' : _99547) (e' : _99547) : term293 _99546 _99547 x f s b g' t' e'.
Proof. exact (@lem3820642 _99546 _99547 x f s b g' t' e'). Qed.
Lemma lem3820644 {_99546 _99547 : Type'} (x : _99546) (f : type1411 _99546 _99547) (s : _99546 -> Prop) (b : _99547) (g' : Prop) (t' : _99547) (e' : _99547) : (term293 _99546 _99547 x f s b g' t' e') = (term294 _99546 _99547 x f s b g' t' e').
Proof. exact (eq_refl (term293 _99546 _99547 x f s b g' t' e')). Qed.
Lemma lem3820645 {_99546 _99547 : Type'} (x : _99546) (f : type1411 _99546 _99547) (s : _99546 -> Prop) (b : _99547) (g' : Prop) (t' : _99547) (e' : _99547) : term294 _99546 _99547 x f s b g' t' e'.
Proof. exact (EQ_MP (@lem3820644 _99546 _99547 x f s b g' t' e') (@lem3820643 _99546 _99547 x f s b g' t' e')). Qed.
Lemma lem3820647 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (h1 : term165 _99546 _99547 x s) : (@IN _99546 x s) = False.
Proof. exact (@lem3819673 _99546 x s (@lem3819672 _99546 _99547 x s h1)). Qed.
Lemma lem3820648 {_99546 _99547 : Type'} (x : _99546) (f : type1411 _99546 _99547) (s : _99546 -> Prop) (b : _99547) (t' : _99547) (e' : _99547) : term295 _99546 _99547 x f s b t' e'.
Proof. exact (@lem3820645 _99546 _99547 x f s b False t' e'). Qed.
Lemma lem3820649 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (b : _99547) (t' : _99547) (e' : _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term165 _99546 _99547 x s) : term296 _99546 _99547 x f s b t' e'.
Proof. exact (@lem3820648 _99546 _99547 x f s b t' e' (@lem3820647 _99546 _99547 x s h1)). Qed.
Lemma lem3820656 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) (b : _99547) : (@ITSET _99547 _99546 f s b) = (@ITSET _99547 _99546 f s b).
Proof. exact (eq_refl (@ITSET _99547 _99546 f s b)). Qed.
Lemma lem3820657 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) (b : _99547) : term297 _99546 _99547 f s b.
Proof. exact (fun h0 : False => @lem3820656 _99546 _99547 f s b). Qed.
Lemma lem3820658 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (b : _99547) (e' : _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term165 _99546 _99547 x s) : term298 _99546 _99547 x f s b e'.
Proof. exact (@lem3820649 _99546 _99547 f b (@ITSET _99547 _99546 f s b) e' x s h1). Qed.
Lemma lem3820659 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (b : _99547) (e' : _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term165 _99546 _99547 x s) : term299 _99546 _99547 x f s b e'.
Proof. exact (@lem3820658 _99546 _99547 f b e' x s h1 (@lem3820657 _99546 _99547 f s b)). Qed.
Lemma lem3820666 {_99546 _99547 : Type'} (x' : _99546) (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s f g) : term271 _99546 _99547 x s f g x'.
Proof. exact (fun h0 : term11 _99546 x x' s => @lem3820226 _99546 _99547 f g x x' s h1 h0). Qed.
Lemma lem3820667 {_99546 _99547 : Type'} (x' : _99546) (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s f g) : term271 _99546 _99547 x s f g x'.
Proof. exact (@lem3820666 _99546 _99547 x' x s f g h1). Qed.
Lemma lem3820668 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s f g) : term300 _99546 _99547 s f g x.
Proof. exact (@lem3820667 _99546 _99547 x x s f g h1). Qed.
Lemma lem3820672 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3820673 {_99546 : Type'} (x : _99546) : (x = x) = True.
Proof. exact (@lem3820672 _99546 x). Qed.
Lemma lem3820674 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3820675 {_99546 : Type'} (x : _99546) : (term301 _99546 x) = (or True).
Proof. exact (MK_COMB (@lem3820674) (@lem3820673 _99546 x)). Qed.
Lemma lem3820677 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (h1 : term165 _99546 _99547 x s) : (@IN _99546 x s) = False.
Proof. exact (@lem3819673 _99546 x s (@lem3819672 _99546 _99547 x s h1)). Qed.
Lemma lem3820680 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (h1 : term165 _99546 _99547 x s) : (term302 _99546 x s) = (True \/ False).
Proof. exact (MK_COMB (@lem3820675 _99546 x) (@lem3820677 _99546 _99547 x s h1)). Qed.
Lemma lem3820682 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem3820683 : (True \/ False) = True.
Proof. exact (@lem3820682 False). Qed.
Lemma lem3820684 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (h1 : term165 _99546 _99547 x s) : (term302 _99546 x s) = True.
Proof. exact (TRANS (@lem3820680 _99546 _99547 x s h1) (@lem3820683)). Qed.
Lemma lem3820685 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (h1 : term165 _99546 _99547 x s) : True = (term302 _99546 x s).
Proof. exact (SYM (@lem3820684 _99546 _99547 x s h1)). Qed.
Lemma lem3820686 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (h1 : term165 _99546 _99547 x s) : term302 _99546 x s.
Proof. exact (EQ_MP (@lem3820685 _99546 _99547 x s h1) (@lem0)). Qed.
Lemma lem3820687 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term278 _99546 _99547 x s f g) (h2 : term165 _99546 _99547 x s) : (f x) = (g x).
Proof. exact (@lem3820668 _99546 _99547 x s f g h1 (@lem3820686 _99546 _99547 x s h2)). Qed.
Lemma lem3820691 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) (b : _99547) : (@ITSET _99547 _99546 f s b) = (@ITSET _99547 _99546 f s b).
Proof. exact (eq_refl (@ITSET _99547 _99546 f s b)). Qed.
Lemma lem3820692 {_99546 _99547 : Type'} (b : _99547) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term278 _99546 _99547 x s f g) (h2 : term165 _99546 _99547 x s) : (term288 _99546 _99547 x f s b) = (term303 _99546 _99547 g x f s b).
Proof. exact (MK_COMB (@lem3820687 _99546 _99547 f g x s h1 h2) (@lem3820691 _99546 _99547 f s b)). Qed.
Lemma lem3820696 {_99546 _99547 : Type'} (b : _99547) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term278 _99546 _99547 x s f g) (h2 : term165 _99546 _99547 x s) : term304 _99546 _99547 g x f s b.
Proof. exact (fun h0 : ~ False => @lem3820692 _99546 _99547 b f g x s h1 h2). Qed.
Lemma lem3820697 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (f : type1411 _99546 _99547) (b : _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term165 _99546 _99547 x s) : term305 _99546 _99547 g x f s b.
Proof. exact (@lem3820659 _99546 _99547 f b (term303 _99546 _99547 g x f s b) x s h1). Qed.
Lemma lem3820698 {_99546 _99547 : Type'} (b : _99547) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term278 _99546 _99547 x s f g) (h2 : term165 _99546 _99547 x s) : (term27 _99546 _99547 x f s b) = (term306 _99546 _99547 g x f s b).
Proof. exact (@lem3820697 _99546 _99547 g f b x s h2 (@lem3820696 _99546 _99547 b f g x s h1 h2)). Qed.
Lemma lem3820700 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem3820701 {_99547 : Type'} (t1 : _99547) (t2 : _99547) : (@COND _99547 False t1 t2) = t2.
Proof. exact (@lem3820700 _99547 t1 t2). Qed.
Lemma lem3820702 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) (f : type1411 _99546 _99547) (s : _99546 -> Prop) (b : _99547) : (term306 _99546 _99547 g x f s b) = (term303 _99546 _99547 g x f s b).
Proof. exact (@lem3820701 _99547 (@ITSET _99547 _99546 f s b) (term303 _99546 _99547 g x f s b)). Qed.
Lemma lem3820706 {_99546 _99547 : Type'} (b : _99547) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term278 _99546 _99547 x s f g) (h2 : term165 _99546 _99547 x s) : (term27 _99546 _99547 x f s b) = (term303 _99546 _99547 g x f s b).
Proof. exact (TRANS (@lem3820698 _99546 _99547 b f g x s h1 h2) (@lem3820702 _99546 _99547 g x f s b)). Qed.
Lemma lem3820707 {_99546 _99547 : Type'} (b : _99547) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term278 _99546 _99547 x s f g) (h2 : term165 _99546 _99547 x s) : (term26 _99546 _99547 f x s b) = (term303 _99546 _99547 g x f s b).
Proof. exact (TRANS (@lem3820629 _99546 _99547 b f g x s h1 h2) (@lem3820706 _99546 _99547 b f g x s h1 h2)). Qed.
Lemma lem3820708 {_99547 : Type'} : (@eq _99547) = (@eq _99547).
Proof. exact (eq_refl (@eq _99547)). Qed.
Lemma lem3820709 {_99546 _99547 : Type'} (b : _99547) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term278 _99546 _99547 x s f g) (h2 : term165 _99546 _99547 x s) : (term307 _99546 _99547 f x s b) = (term308 _99546 _99547 g x f s b).
Proof. exact (MK_COMB (@lem3820708 _99547) (@lem3820707 _99546 _99547 b f g x s h1 h2)). Qed.
Lemma lem3820714 {A B : Type'} (x : A) (f : type1411 A B) (s : A -> Prop) (b : B) : term31 A B x f s b.
Proof. exact (EQ_MP (@lem3817915 A B x f s b) (@lem3817908 A B x f s b)). Qed.
Lemma lem3820715 {_99546 _99547 : Type'} (x : _99546) (f : type1411 _99546 _99547) (s : _99546 -> Prop) (b : _99547) : term31 _99546 _99547 x f s b.
Proof. exact (@lem3820714 _99546 _99547 x f s b). Qed.
Lemma lem3820716 {_99546 _99547 : Type'} (x : _99546) (g : type1411 _99546 _99547) (s : _99546 -> Prop) (b : _99547) : term31 _99546 _99547 x g s b.
Proof. exact (@lem3820715 _99546 _99547 x g s b). Qed.
Lemma lem3820828 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term188 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem3820829 (p : Prop) (q : Prop) (p' : Prop) : term189 p q p'.
Proof. exact (fun q' : Prop => @lem3820828 p q p' q'). Qed.
Lemma lem3820830 (p : Prop) (q : Prop) : term190 p q.
Proof. exact (fun p' : Prop => @lem3820829 p q p'). Qed.
Lemma lem3820831 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (_44388 : _99546) (s : _99547) : term221 _99546 _99547 y g _44388 s.
Proof. exact (@lem3820830 (term90 _99546 _44388 y) ((term93 _99546 _99547 _44388 g y s) = (term93 _99546 _99547 y g _44388 s))). Qed.
Lemma lem3820832 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (_44388 : _99546) (s : _99547) (p' : Prop) : term222 _99546 _99547 y g _44388 s p'.
Proof. exact (@lem3820831 _99546 _99547 y g _44388 s p'). Qed.
Lemma lem3820833 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (_44388 : _99546) (s : _99547) (p' : Prop) : (term222 _99546 _99547 y g _44388 s p') = (term223 _99546 _99547 y g _44388 s p').
Proof. exact (eq_refl (term222 _99546 _99547 y g _44388 s p')). Qed.
Lemma lem3820834 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (_44388 : _99546) (s : _99547) (p' : Prop) : term223 _99546 _99547 y g _44388 s p'.
Proof. exact (EQ_MP (@lem3820833 _99546 _99547 y g _44388 s p') (@lem3820832 _99546 _99547 y g _44388 s p')). Qed.
Lemma lem3820835 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (_44388 : _99546) (s : _99547) (p' : Prop) (q' : Prop) : term224 _99546 _99547 y g _44388 s p' q'.
Proof. exact (@lem3820834 _99546 _99547 y g _44388 s p' q'). Qed.
Lemma lem3820836 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (_44388 : _99546) (s : _99547) (p' : Prop) (q' : Prop) : (term224 _99546 _99547 y g _44388 s p' q') = (term225 _99546 _99547 y g _44388 s p' q').
Proof. exact (eq_refl (term224 _99546 _99547 y g _44388 s p' q')). Qed.
Lemma lem3820837 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (_44388 : _99546) (s : _99547) (p' : Prop) (q' : Prop) : term225 _99546 _99547 y g _44388 s p' q'.
Proof. exact (EQ_MP (@lem3820836 _99546 _99547 y g _44388 s p' q') (@lem3820835 _99546 _99547 y g _44388 s p' q')). Qed.
Lemma lem3820840 {_99546 : Type'} (_44388 : _99546) (y : _99546) : (term90 _99546 _44388 y) = (term90 _99546 _44388 y).
Proof. exact (eq_refl (term90 _99546 _44388 y)). Qed.
Lemma lem3820841 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (s : _99547) (_44388 : _99546) (y : _99546) (q' : Prop) : term226 _99546 _99547 g s _44388 y q'.
Proof. exact (@lem3820837 _99546 _99547 y g _44388 s (term90 _99546 _44388 y) q'). Qed.
Lemma lem3820842 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (s : _99547) (_44388 : _99546) (y : _99546) (q' : Prop) : term227 _99546 _99547 g s _44388 y q'.
Proof. exact (@lem3820841 _99546 _99547 g s _44388 y q' (@lem3820840 _99546 _44388 y)). Qed.
Lemma lem3820843 {_99546 : Type'} (_44388 : _99546) (y : _99546) (h1 : term90 _99546 _44388 y) : term90 _99546 _44388 y.
Proof. exact (h1). Qed.
Lemma lem3820847 {_99546 : Type'} (_44388 : _99546) (y : _99546) (h1 : _44388 = y) : _44388 = y.
Proof. exact (h1). Qed.
Lemma lem3820848 {_99546 : Type'} (_44388 : _99546) (y : _99546) (h1 : _44388 = y) : y = _44388.
Proof. exact (SYM (@lem3820847 _99546 _44388 y h1)). Qed.
Lemma lem3820849 {_99546 : Type'} (y : _99546) (_44388 : _99546) (h1 : y = _44388) : y = _44388.
Proof. exact (h1). Qed.
Lemma lem3820850 {_99546 : Type'} (y : _99546) (_44388 : _99546) (h1 : y = _44388) : _44388 = y.
Proof. exact (SYM (@lem3820849 _99546 y _44388 h1)). Qed.
Lemma lem3820851 {_99546 : Type'} (y : _99546) (_44388 : _99546) : (_44388 = y) = (y = _44388).
Proof. exact (prop_ext (fun h1 : _44388 = y => @lem3820848 _99546 _44388 y h1) (fun h1 : y = _44388 => @lem3820850 _99546 y _44388 h1)). Qed.
Lemma lem3820852 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3820853 {_99546 : Type'} (y : _99546) (_44388 : _99546) : (term90 _99546 _44388 y) = (term90 _99546 y _44388).
Proof. exact (MK_COMB (@lem3820852) (@lem3820851 _99546 y _44388)). Qed.
Lemma lem3820854 {_99546 : Type'} (_44388 : _99546) (y : _99546) (h1 : term90 _99546 _44388 y) : term90 _99546 y _44388.
Proof. exact (EQ_MP (@lem3820853 _99546 y _44388) (@lem3820843 _99546 _44388 y h1)). Qed.
Lemma lem3820855 {_99546 : Type'} (y : _99546) (_44388 : _99546) : term228 _99546 y _44388.
Proof. exact (@lem82 (y = _44388)). Qed.
Lemma lem3820864 {_99546 _99547 : Type'} (y : _99546) (x' : _99546) (s : _99547) (x : _99546) (s' : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s' f g) : term96 _99546 _99547 y g x' s.
Proof. exact (fun h0 : term90 _99546 x' y => @lem3820198 _99546 _99547 s x' y x s' f g h0 h1). Qed.
Lemma lem3820865 {_99546 _99547 : Type'} (y : _99546) (x' : _99546) (s : _99547) (x : _99546) (s' : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s' f g) : term96 _99546 _99547 y g x' s.
Proof. exact (@lem3820864 _99546 _99547 y x' s x s' f g h1). Qed.
Lemma lem3820866 {_99546 _99547 : Type'} (_44388 : _99546) (y : _99546) (s : _99547) (x : _99546) (s' : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s' f g) : term96 _99546 _99547 _44388 g y s.
Proof. exact (@lem3820865 _99546 _99547 _44388 y s x s' f g h1). Qed.
Lemma lem3820868 {_99546 : Type'} (_44388 : _99546) (y : _99546) (h1 : term90 _99546 _44388 y) : (y = _44388) = False.
Proof. exact (@lem3820855 _99546 y _44388 (@lem3820854 _99546 _44388 y h1)). Qed.
Lemma lem3820869 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3820870 {_99546 : Type'} (_44388 : _99546) (y : _99546) (h1 : term90 _99546 _44388 y) : (term90 _99546 y _44388) = (~ False).
Proof. exact (MK_COMB (@lem3820869) (@lem3820868 _99546 _44388 y h1)). Qed.
Lemma lem3820872 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3820873 {_99546 : Type'} (_44388 : _99546) (y : _99546) (h1 : term90 _99546 _44388 y) : (term90 _99546 y _44388) = True.
Proof. exact (TRANS (@lem3820870 _99546 _44388 y h1) (@lem3820872)). Qed.
Lemma lem3820874 {_99546 : Type'} (_44388 : _99546) (y : _99546) (h1 : term90 _99546 _44388 y) : True = (term90 _99546 y _44388).
Proof. exact (SYM (@lem3820873 _99546 _44388 y h1)). Qed.
Lemma lem3820875 {_99546 : Type'} (_44388 : _99546) (y : _99546) (h1 : term90 _99546 _44388 y) : term90 _99546 y _44388.
Proof. exact (EQ_MP (@lem3820874 _99546 _44388 y h1) (@lem0)). Qed.
Lemma lem3820876 {_99546 _99547 : Type'} (s : _99547) (_44388 : _99546) (y : _99546) (x : _99546) (s' : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term90 _99546 _44388 y) (h2 : term278 _99546 _99547 x s' f g) : (term93 _99546 _99547 y g _44388 s) = (term93 _99546 _99547 _44388 g y s).
Proof. exact (@lem3820866 _99546 _99547 _44388 y s x s' f g h2 (@lem3820875 _99546 _44388 y h1)). Qed.
Lemma lem3820881 {_99546 _99547 : Type'} (_44388 : _99546) (g : type1411 _99546 _99547) (y : _99546) (s : _99547) : (term229 _99546 _99547 _44388 g y s) = (term229 _99546 _99547 _44388 g y s).
Proof. exact (eq_refl (term229 _99546 _99547 _44388 g y s)). Qed.
Lemma lem3820882 {_99546 _99547 : Type'} (s : _99547) (_44388 : _99546) (y : _99546) (x : _99546) (s' : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term90 _99546 _44388 y) (h2 : term278 _99546 _99547 x s' f g) : ((term93 _99546 _99547 _44388 g y s) = (term93 _99546 _99547 y g _44388 s)) = ((term93 _99546 _99547 _44388 g y s) = (term93 _99546 _99547 _44388 g y s)).
Proof. exact (MK_COMB (@lem3820881 _99546 _99547 _44388 g y s) (@lem3820876 _99546 _99547 s _44388 y x s' f g h1 h2)). Qed.
Lemma lem3820884 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3820885 {_99547 : Type'} (x : _99547) : (x = x) = True.
Proof. exact (@lem3820884 _99547 x). Qed.
Lemma lem3820886 {_99546 _99547 : Type'} (_44388 : _99546) (g : type1411 _99546 _99547) (y : _99546) (s : _99547) : ((term93 _99546 _99547 _44388 g y s) = (term93 _99546 _99547 _44388 g y s)) = True.
Proof. exact (@lem3820885 _99547 (term93 _99546 _99547 _44388 g y s)). Qed.
Lemma lem3820887 {_99546 _99547 : Type'} (s : _99547) (_44388 : _99546) (y : _99546) (x : _99546) (s' : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term90 _99546 _44388 y) (h2 : term278 _99546 _99547 x s' f g) : ((term93 _99546 _99547 _44388 g y s) = (term93 _99546 _99547 y g _44388 s)) = True.
Proof. exact (TRANS (@lem3820882 _99546 _99547 s _44388 y x s' f g h1 h2) (@lem3820886 _99546 _99547 _44388 g y s)). Qed.
Lemma lem3820888 {_99546 _99547 : Type'} (y : _99546) (_44388 : _99546) (s : _99547) (x : _99546) (s' : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s' f g) : term230 _99546 _99547 y g _44388 s.
Proof. exact (fun h0 : term90 _99546 _44388 y => @lem3820887 _99546 _99547 s _44388 y x s' f g h0 h1). Qed.
Lemma lem3820889 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (s : _99547) (_44388 : _99546) (y : _99546) : term231 _99546 _99547 g s _44388 y.
Proof. exact (@lem3820842 _99546 _99547 g s _44388 y True). Qed.
Lemma lem3820890 {_99546 _99547 : Type'} (s : _99547) (_44388 : _99546) (y : _99546) (x : _99546) (s' : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s' f g) : (term96 _99546 _99547 y g _44388 s) = (term232 _99546 _44388 y).
Proof. exact (@lem3820889 _99546 _99547 g s _44388 y (@lem3820888 _99546 _99547 y _44388 s x s' f g h1)). Qed.
Lemma lem3820892 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem3820893 {_99546 : Type'} (_44388 : _99546) (y : _99546) : (term232 _99546 _44388 y) = True.
Proof. exact (@lem3820892 (term90 _99546 _44388 y)). Qed.
Lemma lem3820894 {_99546 _99547 : Type'} (y : _99546) (_44388 : _99546) (s : _99547) (x : _99546) (s' : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s' f g) : (term96 _99546 _99547 y g _44388 s) = True.
Proof. exact (TRANS (@lem3820890 _99546 _99547 s _44388 y x s' f g h1) (@lem3820893 _99546 _44388 y)). Qed.
Lemma lem3820895 {_99546 _99547 : Type'} (y : _99546) (_44388 : _99546) (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s f g) : (term98 _99546 _99547 y g _44388) = (term210 _99547).
Proof. exact (fun_ext (fun s' : _99547 => @lem3820894 _99546 _99547 y _44388 s' x s f g h1)). Qed.
Lemma lem3820896 {_99547 : Type'} : (@all _99547) = (@all _99547).
Proof. exact (eq_refl (@all _99547)). Qed.
Lemma lem3820897 {_99546 _99547 : Type'} (y : _99546) (_44388 : _99546) (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s f g) : (term99 _99546 _99547 y g _44388) = (term212 _99547).
Proof. exact (MK_COMB (@lem3820896 _99547) (@lem3820895 _99546 _99547 y _44388 x s f g h1)). Qed.
Lemma lem3820899 {A : Type'} (t : Prop) : (term213 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3820900 {_99547 : Type'} (t : Prop) : (term213 _99547 t) = t.
Proof. exact (@lem3820899 _99547 t). Qed.
Lemma lem3820901 {_99547 : Type'} : (term212 _99547) = True.
Proof. exact (@lem3820900 _99547 True). Qed.
Lemma lem3820902 {_99546 _99547 : Type'} (y : _99546) (_44388 : _99546) (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s f g) : (term99 _99546 _99547 y g _44388) = True.
Proof. exact (TRANS (@lem3820897 _99546 _99547 y _44388 x s f g h1) (@lem3820901 _99547)). Qed.
Lemma lem3820903 {_99546 _99547 : Type'} (_44388 : _99546) (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s f g) : (term106 _99546 _99547 g _44388) = (term210 _99546).
Proof. exact (fun_ext (fun y : _99546 => @lem3820902 _99546 _99547 y _44388 x s f g h1)). Qed.
Lemma lem3820904 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3820905 {_99546 _99547 : Type'} (_44388 : _99546) (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s f g) : (term108 _99546 _99547 g _44388) = (term212 _99546).
Proof. exact (MK_COMB (@lem3820904 _99546) (@lem3820903 _99546 _99547 _44388 x s f g h1)). Qed.
Lemma lem3820907 {A : Type'} (t : Prop) : (term213 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3820908 {_99546 : Type'} (t : Prop) : (term213 _99546 t) = t.
Proof. exact (@lem3820907 _99546 t). Qed.
Lemma lem3820909 {_99546 : Type'} : (term212 _99546) = True.
Proof. exact (@lem3820908 _99546 True). Qed.
Lemma lem3820910 {_99546 _99547 : Type'} (_44388 : _99546) (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s f g) : (term108 _99546 _99547 g _44388) = True.
Proof. exact (TRANS (@lem3820905 _99546 _99547 _44388 x s f g h1) (@lem3820909 _99546)). Qed.
Lemma lem3820913 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s f g) : (term110 _99546 _99547 g) = (term210 _99546).
Proof. exact (fun_ext (fun _44388 : _99546 => @lem3820910 _99546 _99547 _44388 x s f g h1)). Qed.
Lemma lem3820914 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3820915 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s f g) : (term19 _99546 _99547 g) = (term212 _99546).
Proof. exact (MK_COMB (@lem3820914 _99546) (@lem3820913 _99546 _99547 x s f g h1)). Qed.
Lemma lem3820917 {A : Type'} (t : Prop) : (term213 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3820918 {_99546 : Type'} (t : Prop) : (term213 _99546 t) = t.
Proof. exact (@lem3820917 _99546 t). Qed.
Lemma lem3820919 {_99546 : Type'} : (term212 _99546) = True.
Proof. exact (@lem3820918 _99546 True). Qed.
Lemma lem3820920 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s f g) : (term19 _99546 _99547 g) = True.
Proof. exact (TRANS (@lem3820915 _99546 _99547 x s f g h1) (@lem3820919 _99546)). Qed.
Lemma lem3820921 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3820922 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s f g) : (term113 _99546 _99547 g) = (and True).
Proof. exact (MK_COMB (@lem3820921) (@lem3820920 _99546 _99547 x s f g h1)). Qed.
Lemma lem3820924 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (h1 : term165 _99546 _99547 x s) : (@FINITE _99546 s) = True.
Proof. exact (EQ_MP (@lem3819670 _99546 s) (@lem3819669 _99546 _99547 x s h1)). Qed.
Lemma lem3820925 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term278 _99546 _99547 x s f g) (h2 : term165 _99546 _99547 x s) : (term282 _99546 _99547 g s) = (True /\ True).
Proof. exact (MK_COMB (@lem3820922 _99546 _99547 x s f g h1) (@lem3820924 _99546 _99547 x s h2)). Qed.
Lemma lem3820927 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3820928 : (True /\ True) = True.
Proof. exact (@lem3820927 True). Qed.
Lemma lem3820929 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term278 _99546 _99547 x s f g) (h2 : term165 _99546 _99547 x s) : (term282 _99546 _99547 g s) = True.
Proof. exact (TRANS (@lem3820925 _99546 _99547 f g x s h1 h2) (@lem3820928)). Qed.
Lemma lem3820930 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term278 _99546 _99547 x s f g) (h2 : term165 _99546 _99547 x s) : True = (term282 _99546 _99547 g s).
Proof. exact (SYM (@lem3820929 _99546 _99547 f g x s h1 h2)). Qed.
Lemma lem3820931 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term278 _99546 _99547 x s f g) (h2 : term165 _99546 _99547 x s) : term282 _99546 _99547 g s.
Proof. exact (EQ_MP (@lem3820930 _99546 _99547 f g x s h1 h2) (@lem0)). Qed.
Lemma lem3820932 {_99546 _99547 : Type'} (b : _99547) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term278 _99546 _99547 x s f g) (h2 : term165 _99546 _99547 x s) : (term26 _99546 _99547 g x s b) = (term27 _99546 _99547 x g s b).
Proof. exact (@lem3820716 _99546 _99547 x g s b (@lem3820931 _99546 _99547 f g x s h1 h2)). Qed.
Lemma lem3820934 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term283 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem3820935 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term284 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem3820934 _2963 g t e g' t' e'). Qed.
Lemma lem3820936 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term285 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem3820935 _2963 g t e g' t'). Qed.
Lemma lem3820937 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term286 _2963 g t e.
Proof. exact (fun g' : Prop => @lem3820936 _2963 g t e g'). Qed.
Lemma lem3820938 {_99547 : Type'} (g : Prop) (t : _99547) (e : _99547) : term286 _99547 g t e.
Proof. exact (@lem3820937 _99547 g t e). Qed.
Lemma lem3820939 {_99546 _99547 : Type'} (x : _99546) (g : type1411 _99546 _99547) (s : _99546 -> Prop) (b : _99547) : term287 _99546 _99547 x g s b.
Proof. exact (@lem3820938 _99547 (@IN _99546 x s) (@ITSET _99547 _99546 g s b) (term288 _99546 _99547 x g s b)). Qed.
Lemma lem3820940 {_99546 _99547 : Type'} (x : _99546) (g : type1411 _99546 _99547) (s : _99546 -> Prop) (b : _99547) (g' : Prop) : term289 _99546 _99547 x g s b g'.
Proof. exact (@lem3820939 _99546 _99547 x g s b g'). Qed.
Lemma lem3820941 {_99546 _99547 : Type'} (x : _99546) (g : type1411 _99546 _99547) (s : _99546 -> Prop) (b : _99547) (g' : Prop) : (term289 _99546 _99547 x g s b g') = (term290 _99546 _99547 x g s b g').
Proof. exact (eq_refl (term289 _99546 _99547 x g s b g')). Qed.
Lemma lem3820942 {_99546 _99547 : Type'} (x : _99546) (g : type1411 _99546 _99547) (s : _99546 -> Prop) (b : _99547) (g' : Prop) : term290 _99546 _99547 x g s b g'.
Proof. exact (EQ_MP (@lem3820941 _99546 _99547 x g s b g') (@lem3820940 _99546 _99547 x g s b g')). Qed.
Lemma lem3820943 {_99546 _99547 : Type'} (x : _99546) (g : type1411 _99546 _99547) (s : _99546 -> Prop) (b : _99547) (g' : Prop) (t' : _99547) : term291 _99546 _99547 x g s b g' t'.
Proof. exact (@lem3820942 _99546 _99547 x g s b g' t'). Qed.
Lemma lem3820944 {_99546 _99547 : Type'} (x : _99546) (g : type1411 _99546 _99547) (s : _99546 -> Prop) (b : _99547) (g' : Prop) (t' : _99547) : (term291 _99546 _99547 x g s b g' t') = (term292 _99546 _99547 x g s b g' t').
Proof. exact (eq_refl (term291 _99546 _99547 x g s b g' t')). Qed.
Lemma lem3820945 {_99546 _99547 : Type'} (x : _99546) (g : type1411 _99546 _99547) (s : _99546 -> Prop) (b : _99547) (g' : Prop) (t' : _99547) : term292 _99546 _99547 x g s b g' t'.
Proof. exact (EQ_MP (@lem3820944 _99546 _99547 x g s b g' t') (@lem3820943 _99546 _99547 x g s b g' t')). Qed.
Lemma lem3820946 {_99546 _99547 : Type'} (x : _99546) (g : type1411 _99546 _99547) (s : _99546 -> Prop) (b : _99547) (g' : Prop) (t' : _99547) (e' : _99547) : term293 _99546 _99547 x g s b g' t' e'.
Proof. exact (@lem3820945 _99546 _99547 x g s b g' t' e'). Qed.
Lemma lem3820947 {_99546 _99547 : Type'} (x : _99546) (g : type1411 _99546 _99547) (s : _99546 -> Prop) (b : _99547) (g' : Prop) (t' : _99547) (e' : _99547) : (term293 _99546 _99547 x g s b g' t' e') = (term294 _99546 _99547 x g s b g' t' e').
Proof. exact (eq_refl (term293 _99546 _99547 x g s b g' t' e')). Qed.
Lemma lem3820948 {_99546 _99547 : Type'} (x : _99546) (g : type1411 _99546 _99547) (s : _99546 -> Prop) (b : _99547) (g' : Prop) (t' : _99547) (e' : _99547) : term294 _99546 _99547 x g s b g' t' e'.
Proof. exact (EQ_MP (@lem3820947 _99546 _99547 x g s b g' t' e') (@lem3820946 _99546 _99547 x g s b g' t' e')). Qed.
Lemma lem3820950 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (h1 : term165 _99546 _99547 x s) : (@IN _99546 x s) = False.
Proof. exact (@lem3819673 _99546 x s (@lem3819672 _99546 _99547 x s h1)). Qed.
Lemma lem3820951 {_99546 _99547 : Type'} (x : _99546) (g : type1411 _99546 _99547) (s : _99546 -> Prop) (b : _99547) (t' : _99547) (e' : _99547) : term295 _99546 _99547 x g s b t' e'.
Proof. exact (@lem3820948 _99546 _99547 x g s b False t' e'). Qed.
Lemma lem3820952 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (b : _99547) (t' : _99547) (e' : _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term165 _99546 _99547 x s) : term296 _99546 _99547 x g s b t' e'.
Proof. exact (@lem3820951 _99546 _99547 x g s b t' e' (@lem3820950 _99546 _99547 x s h1)). Qed.
Lemma lem3820960 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (s : _99546 -> Prop) (b : _99547) : (@ITSET _99547 _99546 g s b) = (@ITSET _99547 _99546 g s b).
Proof. exact (eq_refl (@ITSET _99547 _99546 g s b)). Qed.
Lemma lem3820961 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (s : _99546 -> Prop) (b : _99547) : term297 _99546 _99547 g s b.
Proof. exact (fun h0 : False => @lem3820960 _99546 _99547 g s b). Qed.
Lemma lem3820962 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (b : _99547) (e' : _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term165 _99546 _99547 x s) : term298 _99546 _99547 x g s b e'.
Proof. exact (@lem3820952 _99546 _99547 g b (@ITSET _99547 _99546 g s b) e' x s h1). Qed.
Lemma lem3820963 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (b : _99547) (e' : _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term165 _99546 _99547 x s) : term299 _99546 _99547 x g s b e'.
Proof. exact (@lem3820962 _99546 _99547 g b e' x s h1 (@lem3820961 _99546 _99547 g s b)). Qed.
Lemma lem3820973 {_99546 _99547 : Type'} (x : _99546) (g : type1411 _99546 _99547) (s : _99546 -> Prop) (b : _99547) : (term288 _99546 _99547 x g s b) = (term288 _99546 _99547 x g s b).
Proof. exact (eq_refl (term288 _99546 _99547 x g s b)). Qed.
Lemma lem3820974 {_99546 _99547 : Type'} (x : _99546) (g : type1411 _99546 _99547) (s : _99546 -> Prop) (b : _99547) : term309 _99546 _99547 x g s b.
Proof. exact (fun h0 : ~ False => @lem3820973 _99546 _99547 x g s b). Qed.
Lemma lem3820975 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (b : _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term165 _99546 _99547 x s) : term310 _99546 _99547 x g s b.
Proof. exact (@lem3820963 _99546 _99547 g b (term288 _99546 _99547 x g s b) x s h1). Qed.
Lemma lem3820976 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (b : _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term165 _99546 _99547 x s) : (term27 _99546 _99547 x g s b) = (term311 _99546 _99547 x g s b).
Proof. exact (@lem3820975 _99546 _99547 g b x s h1 (@lem3820974 _99546 _99547 x g s b)). Qed.
Lemma lem3820978 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem3820979 {_99547 : Type'} (t1 : _99547) (t2 : _99547) : (@COND _99547 False t1 t2) = t2.
Proof. exact (@lem3820978 _99547 t1 t2). Qed.
Lemma lem3820980 {_99546 _99547 : Type'} (x : _99546) (g : type1411 _99546 _99547) (s : _99546 -> Prop) (b : _99547) : (term311 _99546 _99547 x g s b) = (term288 _99546 _99547 x g s b).
Proof. exact (@lem3820979 _99547 (@ITSET _99547 _99546 g s b) (term288 _99546 _99547 x g s b)). Qed.
Lemma lem3820985 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (b : _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term165 _99546 _99547 x s) : (term27 _99546 _99547 x g s b) = (term288 _99546 _99547 x g s b).
Proof. exact (TRANS (@lem3820976 _99546 _99547 g b x s h1) (@lem3820980 _99546 _99547 x g s b)). Qed.
Lemma lem3820986 {_99546 _99547 : Type'} (b : _99547) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term278 _99546 _99547 x s f g) (h2 : term165 _99546 _99547 x s) : (term26 _99546 _99547 g x s b) = (term288 _99546 _99547 x g s b).
Proof. exact (TRANS (@lem3820932 _99546 _99547 b f g x s h1 h2) (@lem3820985 _99546 _99547 g b x s h2)). Qed.
Lemma lem3820987 {_99546 _99547 : Type'} (b : _99547) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term278 _99546 _99547 x s f g) (h2 : term165 _99546 _99547 x s) : ((term26 _99546 _99547 f x s b) = (term26 _99546 _99547 g x s b)) = ((term303 _99546 _99547 g x f s b) = (term288 _99546 _99547 x g s b)).
Proof. exact (MK_COMB (@lem3820709 _99546 _99547 b f g x s h1 h2) (@lem3820986 _99546 _99547 b f g x s h1 h2)). Qed.
Lemma lem3820997 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term278 _99546 _99547 x s f g) (h2 : term165 _99546 _99547 x s) : (term312 _99546 _99547 f g x s) = (term313 _99546 _99547 f x g s).
Proof. exact (fun_ext (fun b : _99547 => @lem3820987 _99546 _99547 b f g x s h1 h2)). Qed.
Lemma lem3821007 {_99547 : Type'} : (@all _99547) = (@all _99547).
Proof. exact (eq_refl (@all _99547)). Qed.
Lemma lem3821008 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term278 _99546 _99547 x s f g) (h2 : term165 _99546 _99547 x s) : (term256 _99546 _99547 f g x s) = (term314 _99546 _99547 f x g s).
Proof. exact (MK_COMB (@lem3821007 _99547) (@lem3820997 _99546 _99547 f g x s h1 h2)). Qed.
Lemma lem3821022 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term165 _99546 _99547 x s) : term315 _99546 _99547 f x g s.
Proof. exact (fun h0 : term278 _99546 _99547 x s f g => @lem3821008 _99546 _99547 f g x s h0 h1). Qed.
Lemma lem3821023 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : term316 _99546 _99547 f x g s.
Proof. exact (@lem3820184 _99546 _99547 x s f g (term314 _99546 _99547 f x g s)). Qed.
Lemma lem3821024 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term165 _99546 _99547 x s) : (term317 _99546 _99547 f g x s) = (term318 _99546 _99547 f x g s).
Proof. exact (@lem3821023 _99546 _99547 f x g s (@lem3821022 _99546 _99547 f g x s h1)). Qed.
Lemma lem3821436 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term165 _99546 _99547 x s) : (term319 _99546 _99547 f x s) = (term320 _99546 _99547 f x s).
Proof. exact (fun_ext (fun g : type1411 _99546 _99547 => @lem3821024 _99546 _99547 f g x s h1)). Qed.
Lemma lem3821848 {_99546 _99547 : Type'} : (@all (_99546 -> _99547 -> _99547)) = (@all (_99546 -> _99547 -> _99547)).
Proof. exact (eq_refl (@all (_99546 -> _99547 -> _99547))). Qed.
Lemma lem3821849 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term165 _99546 _99547 x s) : (term321 _99546 _99547 f x s) = (term322 _99546 _99547 f x s).
Proof. exact (MK_COMB (@lem3821848 _99546 _99547) (@lem3821436 _99546 _99547 f x s h1)). Qed.
Lemma lem3822265 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (h1 : term165 _99546 _99547 x s) : (term323 _99546 _99547 x s) = (term324 _99546 _99547 x s).
Proof. exact (fun_ext (fun f : type1411 _99546 _99547 => @lem3821849 _99546 _99547 f x s h1)). Qed.
Lemma lem3822681 {_99546 _99547 : Type'} : (@all (_99546 -> _99547 -> _99547)) = (@all (_99546 -> _99547 -> _99547)).
Proof. exact (eq_refl (@all (_99546 -> _99547 -> _99547))). Qed.
Lemma lem3822682 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (h1 : term165 _99546 _99547 x s) : (term169 _99546 _99547 x s) = (term325 _99546 _99547 x s).
Proof. exact (MK_COMB (@lem3822681 _99546 _99547) (@lem3822265 _99546 _99547 x s h1)). Qed.
Lemma lem3823102 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) : term326 _99546 _99547 x s.
Proof. exact (fun h0 : term165 _99546 _99547 x s => @lem3822682 _99546 _99547 x s h0). Qed.
Lemma lem3823103 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) : term327 _99546 _99547 x s.
Proof. exact (@lem3819666 _99546 _99547 x s (term325 _99546 _99547 x s)). Qed.
Lemma lem3823104 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) : (term171 _99546 _99547 x s) = (term328 _99546 _99547 x s).
Proof. exact (@lem3823103 _99546 _99547 x s (@lem3823102 _99546 _99547 x s)). Qed.
Lemma lem3824760 {_99546 _99547 : Type'} (x : _99546) : (term173 _99546 _99547 x) = (term329 _99546 _99547 x).
Proof. exact (fun_ext (fun s : _99546 -> Prop => @lem3823104 _99546 _99547 x s)). Qed.
Lemma lem3826416 {_99546 : Type'} : (@all (_99546 -> Prop)) = (@all (_99546 -> Prop)).
Proof. exact (eq_refl (@all (_99546 -> Prop))). Qed.
Lemma lem3826417 {_99546 _99547 : Type'} (x : _99546) : (term175 _99546 _99547 x) = (term330 _99546 _99547 x).
Proof. exact (MK_COMB (@lem3826416 _99546) (@lem3824760 _99546 _99547 x)). Qed.
Lemma lem3828077 {_99546 _99547 : Type'} : (term177 _99546 _99547) = (term331 _99546 _99547).
Proof. exact (fun_ext (fun x : _99546 => @lem3826417 _99546 _99547 x)). Qed.
Lemma lem3829737 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3829738 {_99546 _99547 : Type'} : (term179 _99546 _99547) = (term332 _99546 _99547).
Proof. exact (MK_COMB (@lem3829737 _99546) (@lem3828077 _99546 _99547)). Qed.
Lemma lem3831402 {_99546 _99547 : Type'} : (term181 _99546 _99547) = (term333 _99546 _99547).
Proof. exact (MK_COMB (@lem3819249 _99546 _99547) (@lem3829738 _99546 _99547)). Qed.
Lemma lem3831404 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3831405 {_99546 _99547 : Type'} : (term333 _99546 _99547) = (term332 _99546 _99547).
Proof. exact (@lem3831404 (term332 _99546 _99547)). Qed.
Lemma lem3833069 {_99546 _99547 : Type'} : (term181 _99546 _99547) = (term332 _99546 _99547).
Proof. exact (TRANS (@lem3831402 _99546 _99547) (@lem3831405 _99546 _99547)). Qed.
Lemma lem3833070 {_99546 _99547 : Type'} : (term332 _99546 _99547) = (term181 _99546 _99547).
Proof. exact (SYM (@lem3833069 _99546 _99547)). Qed.
Lemma lem3833071 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (h1 : term165 _99546 _99547 x s) : term165 _99546 _99547 x s.
Proof. exact (h1). Qed.
Lemma lem3833072 {_99546 : Type'} (x : _99546) (s : _99546 -> Prop) (h1 : term163 _99546 x s) : term163 _99546 x s.
Proof. exact (h1). Qed.
Lemma lem3833073 {_99546 _99547 : Type'} (s : _99546 -> Prop) (h1 : term150 _99546 _99547 s) : term150 _99546 _99547 s.
Proof. exact (h1). Qed.
Lemma lem3833074 {_99546 : Type'} (s : _99546 -> Prop) (h1 : @FINITE _99546 s) : @FINITE _99546 s.
Proof. exact (h1). Qed.
Lemma lem3833075 {_99546 : Type'} (x : _99546) (s : _99546 -> Prop) (h1 : term252 _99546 x s) : term252 _99546 x s.
Proof. exact (h1). Qed.
Lemma lem3833076 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s f g) : term278 _99546 _99547 x s f g.
Proof. exact (h1). Qed.
Lemma lem3833077 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : term116 _99546 _99547 f g.
Proof. exact (h1). Qed.
Lemma lem3833078 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term275 _99546 _99547 x s f g) : term275 _99546 _99547 x s f g.
Proof. exact (h1). Qed.
Lemma lem3833079 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (h1 : term112 _99546 _99547 g) : term112 _99546 _99547 g.
Proof. exact (h1). Qed.
Lemma lem3833080 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (h1 : term112 _99546 _99547 f) : term112 _99546 _99547 f.
Proof. exact (h1). Qed.
Lemma lem3833081 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) : (g x) = (g x).
Proof. exact (eq_refl (g x)). Qed.
Lemma lem3833297 {A : Type'} (P : Prop) (Q : A -> Prop) : (term3 A P Q) = (term4 A P Q).
Proof. exact (EQ_MP (@lem3817874 A P Q) (@lem3817873 A P Q)). Qed.
Lemma lem3833298 {_99547 : Type'} (P : Prop) (Q : _99547 -> Prop) : (term3 _99547 P Q) = (term4 _99547 P Q).
Proof. exact (@lem3833297 _99547 P Q). Qed.
Lemma lem3833299 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term334 _99546 _99547 f g s) = (term335 _99546 _99547 f g s).
Proof. exact (@lem3833298 _99547 (term118 _99546 _99547 s f g) (term77 _99546 _99547 f g s)). Qed.
Lemma lem3833300 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) (b : _99547) : (term78 _99546 _99547 f g s b) = ((@ITSET _99547 _99546 f s b) = (@ITSET _99547 _99546 g s b)).
Proof. exact (eq_refl (term78 _99546 _99547 f g s b)). Qed.
Lemma lem3833301 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term84 _99546 _99547 f g s) = (term77 _99546 _99547 f g s).
Proof. exact (fun_ext (fun b : _99547 => @lem3833300 _99546 _99547 f g s b)). Qed.
Lemma lem3833302 {_99547 : Type'} : (@all _99547) = (@all _99547).
Proof. exact (eq_refl (@all _99547)). Qed.
Lemma lem3833303 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term85 _99546 _99547 f g s) = (term86 _99546 _99547 f g s).
Proof. exact (MK_COMB (@lem3833302 _99547) (@lem3833301 _99546 _99547 f g s)). Qed.
Lemma lem3833304 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term119 _99546 _99547 s f g) = (term119 _99546 _99547 s f g).
Proof. exact (eq_refl (term119 _99546 _99547 s f g)). Qed.
Lemma lem3833305 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term334 _99546 _99547 f g s) = (term120 _99546 _99547 f g s).
Proof. exact (MK_COMB (@lem3833304 _99546 _99547 s f g) (@lem3833303 _99546 _99547 f g s)). Qed.
Lemma lem3833306 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3833307 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term336 _99546 _99547 f g s) = (term337 _99546 _99547 f g s).
Proof. exact (MK_COMB (@lem3833306) (@lem3833305 _99546 _99547 f g s)). Qed.
Lemma lem3833308 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) (b : _99547) : (term78 _99546 _99547 f g s b) = ((@ITSET _99547 _99546 f s b) = (@ITSET _99547 _99546 g s b)).
Proof. exact (eq_refl (term78 _99546 _99547 f g s b)). Qed.
Lemma lem3833309 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term119 _99546 _99547 s f g) = (term119 _99546 _99547 s f g).
Proof. exact (eq_refl (term119 _99546 _99547 s f g)). Qed.
Lemma lem3833310 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) (b : _99547) : (term338 _99546 _99547 f g s b) = (term339 _99546 _99547 f g s b).
Proof. exact (MK_COMB (@lem3833309 _99546 _99547 s f g) (@lem3833308 _99546 _99547 f g s b)). Qed.
Lemma lem3833311 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term340 _99546 _99547 f g s) = (term341 _99546 _99547 f g s).
Proof. exact (fun_ext (fun b : _99547 => @lem3833310 _99546 _99547 f g s b)). Qed.
Lemma lem3833312 {_99547 : Type'} : (@all _99547) = (@all _99547).
Proof. exact (eq_refl (@all _99547)). Qed.
Lemma lem3833313 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term335 _99546 _99547 f g s) = (term342 _99546 _99547 f g s).
Proof. exact (MK_COMB (@lem3833312 _99547) (@lem3833311 _99546 _99547 f g s)). Qed.
Lemma lem3833314 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : ((term334 _99546 _99547 f g s) = (term335 _99546 _99547 f g s)) = ((term120 _99546 _99547 f g s) = (term342 _99546 _99547 f g s)).
Proof. exact (MK_COMB (@lem3833307 _99546 _99547 f g s) (@lem3833313 _99546 _99547 f g s)). Qed.
Lemma lem3833315 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term120 _99546 _99547 f g s) = (term342 _99546 _99547 f g s).
Proof. exact (EQ_MP (@lem3833314 _99546 _99547 f g s) (@lem3833299 _99546 _99547 f g s)). Qed.
Lemma lem3833343 {A : Type'} (P : Prop) (Q : A -> Prop) : (term3 A P Q) = (term4 A P Q).
Proof. exact (EQ_MP (@lem3817874 A P Q) (@lem3817873 A P Q)). Qed.
Lemma lem3833344 {_99547 : Type'} (P : Prop) (Q : _99547 -> Prop) : (term3 _99547 P Q) = (term4 _99547 P Q).
Proof. exact (@lem3833343 _99547 P Q). Qed.
Lemma lem3833345 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term89 _99546 _99547 y f x) = (term88 _99546 _99547 y f x).
Proof. exact (@lem3833344 _99547 (term90 _99546 x y) (term91 _99546 _99547 y f x)). Qed.
Lemma lem3833346 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term92 _99546 _99547 y f x s) = ((term93 _99546 _99547 x f y s) = (term93 _99546 _99547 y f x s)).
Proof. exact (eq_refl (term92 _99546 _99547 y f x s)). Qed.
Lemma lem3833347 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term102 _99546 _99547 y f x) = (term91 _99546 _99547 y f x).
Proof. exact (fun_ext (fun s : _99547 => @lem3833346 _99546 _99547 y f x s)). Qed.
Lemma lem3833348 {_99547 : Type'} : (@all _99547) = (@all _99547).
Proof. exact (eq_refl (@all _99547)). Qed.
Lemma lem3833349 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term103 _99546 _99547 y f x) = (term104 _99546 _99547 y f x).
Proof. exact (MK_COMB (@lem3833348 _99547) (@lem3833347 _99546 _99547 y f x)). Qed.
Lemma lem3833350 {_99546 : Type'} (x : _99546) (y : _99546) : (term94 _99546 x y) = (term94 _99546 x y).
Proof. exact (eq_refl (term94 _99546 x y)). Qed.
Lemma lem3833351 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term89 _99546 _99547 y f x) = (term105 _99546 _99547 y f x).
Proof. exact (MK_COMB (@lem3833350 _99546 x y) (@lem3833349 _99546 _99547 y f x)). Qed.
Lemma lem3833352 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3833353 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term343 _99546 _99547 y f x) = (term344 _99546 _99547 y f x).
Proof. exact (MK_COMB (@lem3833352) (@lem3833351 _99546 _99547 y f x)). Qed.
Lemma lem3833354 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term92 _99546 _99547 y f x s) = ((term93 _99546 _99547 x f y s) = (term93 _99546 _99547 y f x s)).
Proof. exact (eq_refl (term92 _99546 _99547 y f x s)). Qed.
Lemma lem3833355 {_99546 : Type'} (x : _99546) (y : _99546) : (term94 _99546 x y) = (term94 _99546 x y).
Proof. exact (eq_refl (term94 _99546 x y)). Qed.
Lemma lem3833356 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term95 _99546 _99547 y f x s) = (term96 _99546 _99547 y f x s).
Proof. exact (MK_COMB (@lem3833355 _99546 x y) (@lem3833354 _99546 _99547 y f x s)). Qed.
Lemma lem3833357 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term97 _99546 _99547 y f x) = (term98 _99546 _99547 y f x).
Proof. exact (fun_ext (fun s : _99547 => @lem3833356 _99546 _99547 y f x s)). Qed.
Lemma lem3833358 {_99547 : Type'} : (@all _99547) = (@all _99547).
Proof. exact (eq_refl (@all _99547)). Qed.
Lemma lem3833359 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term88 _99546 _99547 y f x) = (term99 _99546 _99547 y f x).
Proof. exact (MK_COMB (@lem3833358 _99547) (@lem3833357 _99546 _99547 y f x)). Qed.
Lemma lem3833360 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : ((term89 _99546 _99547 y f x) = (term88 _99546 _99547 y f x)) = ((term105 _99546 _99547 y f x) = (term99 _99546 _99547 y f x)).
Proof. exact (MK_COMB (@lem3833353 _99546 _99547 y f x) (@lem3833359 _99546 _99547 y f x)). Qed.
Lemma lem3833361 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term105 _99546 _99547 y f x) = (term99 _99546 _99547 y f x).
Proof. exact (EQ_MP (@lem3833360 _99546 _99547 y f x) (@lem3833345 _99546 _99547 y f x)). Qed.
Lemma lem3833372 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (term107 _99546 _99547 f x) = (term106 _99546 _99547 f x).
Proof. exact (fun_ext (fun y : _99546 => @lem3833361 _99546 _99547 y f x)). Qed.
Lemma lem3833373 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3833374 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (term109 _99546 _99547 f x) = (term108 _99546 _99547 f x).
Proof. exact (MK_COMB (@lem3833373 _99546) (@lem3833372 _99546 _99547 f x)). Qed.
Lemma lem3833379 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term111 _99546 _99547 f) = (term110 _99546 _99547 f).
Proof. exact (fun_ext (fun x : _99546 => @lem3833374 _99546 _99547 f x)). Qed.
Lemma lem3833380 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3833381 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term112 _99546 _99547 f) = (term19 _99546 _99547 f).
Proof. exact (MK_COMB (@lem3833380 _99546) (@lem3833379 _99546 _99547 f)). Qed.
Lemma lem3833386 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3833387 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term114 _99546 _99547 f) = (term113 _99546 _99547 f).
Proof. exact (MK_COMB (@lem3833386) (@lem3833381 _99546 _99547 f)). Qed.
Lemma lem3833397 {A : Type'} (P : Prop) (Q : A -> Prop) : (term3 A P Q) = (term4 A P Q).
Proof. exact (EQ_MP (@lem3817874 A P Q) (@lem3817873 A P Q)). Qed.
Lemma lem3833398 {_99547 : Type'} (P : Prop) (Q : _99547 -> Prop) : (term3 _99547 P Q) = (term4 _99547 P Q).
Proof. exact (@lem3833397 _99547 P Q). Qed.
Lemma lem3833399 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term89 _99546 _99547 y g x) = (term88 _99546 _99547 y g x).
Proof. exact (@lem3833398 _99547 (term90 _99546 x y) (term91 _99546 _99547 y g x)). Qed.
Lemma lem3833400 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term92 _99546 _99547 y g x s) = ((term93 _99546 _99547 x g y s) = (term93 _99546 _99547 y g x s)).
Proof. exact (eq_refl (term92 _99546 _99547 y g x s)). Qed.
Lemma lem3833401 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term102 _99546 _99547 y g x) = (term91 _99546 _99547 y g x).
Proof. exact (fun_ext (fun s : _99547 => @lem3833400 _99546 _99547 y g x s)). Qed.
Lemma lem3833402 {_99547 : Type'} : (@all _99547) = (@all _99547).
Proof. exact (eq_refl (@all _99547)). Qed.
Lemma lem3833403 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term103 _99546 _99547 y g x) = (term104 _99546 _99547 y g x).
Proof. exact (MK_COMB (@lem3833402 _99547) (@lem3833401 _99546 _99547 y g x)). Qed.
Lemma lem3833404 {_99546 : Type'} (x : _99546) (y : _99546) : (term94 _99546 x y) = (term94 _99546 x y).
Proof. exact (eq_refl (term94 _99546 x y)). Qed.
Lemma lem3833405 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term89 _99546 _99547 y g x) = (term105 _99546 _99547 y g x).
Proof. exact (MK_COMB (@lem3833404 _99546 x y) (@lem3833403 _99546 _99547 y g x)). Qed.
Lemma lem3833406 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3833407 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term343 _99546 _99547 y g x) = (term344 _99546 _99547 y g x).
Proof. exact (MK_COMB (@lem3833406) (@lem3833405 _99546 _99547 y g x)). Qed.
Lemma lem3833408 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term92 _99546 _99547 y g x s) = ((term93 _99546 _99547 x g y s) = (term93 _99546 _99547 y g x s)).
Proof. exact (eq_refl (term92 _99546 _99547 y g x s)). Qed.
Lemma lem3833409 {_99546 : Type'} (x : _99546) (y : _99546) : (term94 _99546 x y) = (term94 _99546 x y).
Proof. exact (eq_refl (term94 _99546 x y)). Qed.
Lemma lem3833410 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term95 _99546 _99547 y g x s) = (term96 _99546 _99547 y g x s).
Proof. exact (MK_COMB (@lem3833409 _99546 x y) (@lem3833408 _99546 _99547 y g x s)). Qed.
Lemma lem3833411 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term97 _99546 _99547 y g x) = (term98 _99546 _99547 y g x).
Proof. exact (fun_ext (fun s : _99547 => @lem3833410 _99546 _99547 y g x s)). Qed.
Lemma lem3833412 {_99547 : Type'} : (@all _99547) = (@all _99547).
Proof. exact (eq_refl (@all _99547)). Qed.
Lemma lem3833413 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term88 _99546 _99547 y g x) = (term99 _99546 _99547 y g x).
Proof. exact (MK_COMB (@lem3833412 _99547) (@lem3833411 _99546 _99547 y g x)). Qed.
Lemma lem3833414 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : ((term89 _99546 _99547 y g x) = (term88 _99546 _99547 y g x)) = ((term105 _99546 _99547 y g x) = (term99 _99546 _99547 y g x)).
Proof. exact (MK_COMB (@lem3833407 _99546 _99547 y g x) (@lem3833413 _99546 _99547 y g x)). Qed.
Lemma lem3833415 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term105 _99546 _99547 y g x) = (term99 _99546 _99547 y g x).
Proof. exact (EQ_MP (@lem3833414 _99546 _99547 y g x) (@lem3833399 _99546 _99547 y g x)). Qed.
Lemma lem3833426 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) : (term107 _99546 _99547 g x) = (term106 _99546 _99547 g x).
Proof. exact (fun_ext (fun y : _99546 => @lem3833415 _99546 _99547 y g x)). Qed.
Lemma lem3833427 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3833428 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) : (term109 _99546 _99547 g x) = (term108 _99546 _99547 g x).
Proof. exact (MK_COMB (@lem3833427 _99546) (@lem3833426 _99546 _99547 g x)). Qed.
Lemma lem3833433 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) : (term111 _99546 _99547 g) = (term110 _99546 _99547 g).
Proof. exact (fun_ext (fun x : _99546 => @lem3833428 _99546 _99547 g x)). Qed.
Lemma lem3833434 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3833435 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) : (term112 _99546 _99547 g) = (term19 _99546 _99547 g).
Proof. exact (MK_COMB (@lem3833434 _99546) (@lem3833433 _99546 _99547 g)). Qed.
Lemma lem3833440 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term116 _99546 _99547 f g) = (term115 _99546 _99547 f g).
Proof. exact (MK_COMB (@lem3833387 _99546 _99547 f) (@lem3833435 _99546 _99547 g)). Qed.
Lemma lem3833443 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term117 _99546 _99547 s f g) = (term117 _99546 _99547 s f g).
Proof. exact (eq_refl (term117 _99546 _99547 s f g)). Qed.
Lemma lem3833444 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term118 _99546 _99547 s f g) = (term44 _99546 _99547 s f g).
Proof. exact (MK_COMB (@lem3833443 _99546 _99547 s f g) (@lem3833440 _99546 _99547 f g)). Qed.
Lemma lem3833447 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3833448 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term119 _99546 _99547 s f g) = (term79 _99546 _99547 s f g).
Proof. exact (MK_COMB (@lem3833447) (@lem3833444 _99546 _99547 s f g)). Qed.
Lemma lem3833451 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) (b : _99547) : ((@ITSET _99547 _99546 f s b) = (@ITSET _99547 _99546 g s b)) = ((@ITSET _99547 _99546 f s b) = (@ITSET _99547 _99546 g s b)).
Proof. exact (eq_refl ((@ITSET _99547 _99546 f s b) = (@ITSET _99547 _99546 g s b))). Qed.
Lemma lem3833452 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) (b : _99547) : (term339 _99546 _99547 f g s b) = (term65 _99546 _99547 f g s b).
Proof. exact (MK_COMB (@lem3833448 _99546 _99547 s f g) (@lem3833451 _99546 _99547 f g s b)). Qed.
Lemma lem3833455 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term341 _99546 _99547 f g s) = (term63 _99546 _99547 f g s).
Proof. exact (fun_ext (fun b : _99547 => @lem3833452 _99546 _99547 f g s b)). Qed.
Lemma lem3833456 {_99547 : Type'} : (@all _99547) = (@all _99547).
Proof. exact (eq_refl (@all _99547)). Qed.
Lemma lem3833457 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term342 _99546 _99547 f g s) = (term73 _99546 _99547 f g s).
Proof. exact (MK_COMB (@lem3833456 _99547) (@lem3833455 _99546 _99547 f g s)). Qed.
Lemma lem3833462 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term120 _99546 _99547 f g s) = (term73 _99546 _99547 f g s).
Proof. exact (TRANS (@lem3833315 _99546 _99547 f g s) (@lem3833457 _99546 _99547 f g s)). Qed.
Lemma lem3833463 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term128 _99546 _99547 f s) = (term345 _99546 _99547 f s).
Proof. exact (fun_ext (fun g : type1411 _99546 _99547 => @lem3833462 _99546 _99547 f g s)). Qed.
Lemma lem3833464 {_99546 _99547 : Type'} : (@all (_99546 -> _99547 -> _99547)) = (@all (_99546 -> _99547 -> _99547)).
Proof. exact (eq_refl (@all (_99546 -> _99547 -> _99547))). Qed.
Lemma lem3833465 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term136 _99546 _99547 f s) = (term346 _99546 _99547 f s).
Proof. exact (MK_COMB (@lem3833464 _99546 _99547) (@lem3833463 _99546 _99547 f s)). Qed.
Lemma lem3833470 {_99546 _99547 : Type'} (s : _99546 -> Prop) : (term142 _99546 _99547 s) = (term347 _99546 _99547 s).
Proof. exact (fun_ext (fun f : type1411 _99546 _99547 => @lem3833465 _99546 _99547 f s)). Qed.
Lemma lem3833471 {_99546 _99547 : Type'} : (@all (_99546 -> _99547 -> _99547)) = (@all (_99546 -> _99547 -> _99547)).
Proof. exact (eq_refl (@all (_99546 -> _99547 -> _99547))). Qed.
Lemma lem3833472 {_99546 _99547 : Type'} (s : _99546 -> Prop) : (term150 _99546 _99547 s) = (term348 _99546 _99547 s).
Proof. exact (MK_COMB (@lem3833471 _99546 _99547) (@lem3833470 _99546 _99547 s)). Qed.
Lemma lem3833477 {_99546 _99547 : Type'} (s : _99546 -> Prop) (h1 : term150 _99546 _99547 s) : term348 _99546 _99547 s.
Proof. exact (EQ_MP (@lem3833472 _99546 _99547 s) (@lem3833073 _99546 _99547 s h1)). Qed.
Lemma lem3833478 {_99546 _99547 : Type'} (s : _99546 -> Prop) (h1 : term348 _99546 _99547 s) : term348 _99546 _99547 s.
Proof. exact (h1). Qed.
Lemma lem3833479 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) (h1 : term348 _99546 _99547 s) : term349 _99546 _99547 s f.
Proof. exact (@lem3833478 _99546 _99547 s h1 f). Qed.
Lemma lem3833480 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term349 _99546 _99547 s f) = (term346 _99546 _99547 f s).
Proof. exact (eq_refl (term349 _99546 _99547 s f)). Qed.
Lemma lem3833481 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) (h1 : term348 _99546 _99547 s) : term346 _99546 _99547 f s.
Proof. exact (EQ_MP (@lem3833480 _99546 _99547 f s) (@lem3833479 _99546 _99547 f s h1)). Qed.
Lemma lem3833482 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) (h1 : term348 _99546 _99547 s) : term350 _99546 _99547 f s g.
Proof. exact (@lem3833481 _99546 _99547 f s h1 g). Qed.
Lemma lem3833483 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term350 _99546 _99547 f s g) = (term73 _99546 _99547 f g s).
Proof. exact (eq_refl (term350 _99546 _99547 f s g)). Qed.
Lemma lem3833484 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) (h1 : term348 _99546 _99547 s) : term73 _99546 _99547 f g s.
Proof. exact (EQ_MP (@lem3833483 _99546 _99547 f g s) (@lem3833482 _99546 _99547 f g s h1)). Qed.
Lemma lem3833485 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (b : _99547) (s : _99546 -> Prop) (h1 : term348 _99546 _99547 s) : term64 _99546 _99547 f g s b.
Proof. exact (@lem3833484 _99546 _99547 f g s h1 b). Qed.
Lemma lem3833486 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) (b : _99547) : (term64 _99546 _99547 f g s b) = (term65 _99546 _99547 f g s b).
Proof. exact (eq_refl (term64 _99546 _99547 f g s b)). Qed.
Lemma lem3833487 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (b : _99547) (s : _99546 -> Prop) (h1 : term348 _99546 _99547 s) : term65 _99546 _99547 f g s b.
Proof. exact (EQ_MP (@lem3833486 _99546 _99547 f g s b) (@lem3833485 _99546 _99547 f g b s h1)). Qed.
Lemma lem3833488 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term44 _99546 _99547 s f g) : term44 _99546 _99547 s f g.
Proof. exact (h1). Qed.
Lemma lem3833489 {_99546 _99547 : Type'} (b : _99547) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term348 _99546 _99547 s) (h2 : term44 _99546 _99547 s f g) : (@ITSET _99547 _99546 f s b) = (@ITSET _99547 _99546 g s b).
Proof. exact (@lem3833487 _99546 _99547 f g b s h1 (@lem3833488 _99546 _99547 s f g h2)). Qed.
Lemma lem3833490 {_99546 _99547 : Type'} (b : _99547) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term44 _99546 _99547 s f g) : term351 _99546 _99547 f g s b.
Proof. exact (fun h0 : term348 _99546 _99547 s => @lem3833489 _99546 _99547 b s f g h0 h1). Qed.
Lemma lem3833491 {_99546 _99547 : Type'} (s : _99546 -> Prop) (h1 : term348 _99546 _99547 s) : term348 _99546 _99547 s.
Proof. exact (h1). Qed.
Lemma lem3833492 {_99546 _99547 : Type'} (b : _99547) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term348 _99546 _99547 s) (h2 : term44 _99546 _99547 s f g) : (@ITSET _99547 _99546 f s b) = (@ITSET _99547 _99546 g s b).
Proof. exact (@lem3833490 _99546 _99547 b s f g h2 (@lem3833491 _99546 _99547 s h1)). Qed.
Lemma lem3833493 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (b : _99547) (s : _99546 -> Prop) (h1 : term348 _99546 _99547 s) : term65 _99546 _99547 f g s b.
Proof. exact (fun h0 : term44 _99546 _99547 s f g => @lem3833492 _99546 _99547 b s f g h1 h0). Qed.
Lemma lem3833494 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) (h1 : term348 _99546 _99547 s) : term73 _99546 _99547 f g s.
Proof. exact (fun b : _99547 => @lem3833493 _99546 _99547 f g b s h1). Qed.
Lemma lem3833495 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) (h1 : term348 _99546 _99547 s) : term346 _99546 _99547 f s.
Proof. exact (fun g : type1411 _99546 _99547 => @lem3833494 _99546 _99547 f g s h1). Qed.
Lemma lem3833496 {_99546 _99547 : Type'} (s : _99546 -> Prop) (h1 : term348 _99546 _99547 s) : term348 _99546 _99547 s.
Proof. exact (fun f : type1411 _99546 _99547 => @lem3833495 _99546 _99547 f s h1). Qed.
Lemma lem3833497 {_99546 _99547 : Type'} (s : _99546 -> Prop) : term352 _99546 _99547 s.
Proof. exact (fun h0 : term348 _99546 _99547 s => @lem3833496 _99546 _99547 s h0). Qed.
Lemma lem3833498 {_99546 _99547 : Type'} (s : _99546 -> Prop) (h1 : term150 _99546 _99547 s) : term348 _99546 _99547 s.
Proof. exact (@lem3833497 _99546 _99547 s (@lem3833477 _99546 _99547 s h1)). Qed.
Lemma lem3833499 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) (h1 : term150 _99546 _99547 s) : term349 _99546 _99547 s f.
Proof. exact (@lem3833498 _99546 _99547 s h1 f). Qed.
Lemma lem3833500 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term349 _99546 _99547 s f) = (term346 _99546 _99547 f s).
Proof. exact (eq_refl (term349 _99546 _99547 s f)). Qed.
Lemma lem3833501 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) (h1 : term150 _99546 _99547 s) : term346 _99546 _99547 f s.
Proof. exact (EQ_MP (@lem3833500 _99546 _99547 f s) (@lem3833499 _99546 _99547 f s h1)). Qed.
Lemma lem3833502 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) (h1 : term150 _99546 _99547 s) : term350 _99546 _99547 f s g.
Proof. exact (@lem3833501 _99546 _99547 f s h1 g). Qed.
Lemma lem3833503 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term350 _99546 _99547 f s g) = (term73 _99546 _99547 f g s).
Proof. exact (eq_refl (term350 _99546 _99547 f s g)). Qed.
Lemma lem3833504 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) (h1 : term150 _99546 _99547 s) : term73 _99546 _99547 f g s.
Proof. exact (EQ_MP (@lem3833503 _99546 _99547 f g s) (@lem3833502 _99546 _99547 f g s h1)). Qed.
Lemma lem3833505 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (b : _99547) (s : _99546 -> Prop) (h1 : term150 _99546 _99547 s) : term64 _99546 _99547 f g s b.
Proof. exact (@lem3833504 _99546 _99547 f g s h1 b). Qed.
Lemma lem3833506 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) (b : _99547) : (term64 _99546 _99547 f g s b) = (term65 _99546 _99547 f g s b).
Proof. exact (eq_refl (term64 _99546 _99547 f g s b)). Qed.
Lemma lem3833509 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (b : _99547) (s : _99546 -> Prop) (h1 : term150 _99546 _99547 s) : term65 _99546 _99547 f g s b.
Proof. exact (EQ_MP (@lem3833506 _99546 _99547 f g s b) (@lem3833505 _99546 _99547 f g b s h1)). Qed.
Lemma lem3833510 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (b : _99547) (s : _99546 -> Prop) (h1 : term150 _99546 _99547 s) : term65 _99546 _99547 f g s b.
Proof. exact (@lem3833509 _99546 _99547 f g b s h1). Qed.
Lemma lem3833512 (p : Prop) : p = (term353 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3833513 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term44 _99546 _99547 s f g) = (term354 _99546 _99547 s f g).
Proof. exact (@lem3833512 (term44 _99546 _99547 s f g)). Qed.
Lemma lem3833514 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term354 _99546 _99547 s f g) = (term44 _99546 _99547 s f g).
Proof. exact (SYM (@lem3833513 _99546 _99547 s f g)). Qed.
Lemma lem3833515 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term355 _99546 _99547 s f g) : term355 _99546 _99547 s f g.
Proof. exact (h1). Qed.
Lemma lem3833518 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term356 _99546 _99547 x s f g) : term356 _99546 _99547 x s f g.
Proof. exact (h1). Qed.
Lemma lem3833519 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : term357 _99546 _99547 x s f g.
Proof. exact (fun h0 : term356 _99546 _99547 x s f g => @lem3833518 _99546 _99547 x s f g h0). Qed.
Lemma lem3833520 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term357 _99546 _99547 x s f g) : term357 _99546 _99547 x s f g.
Proof. exact (h1). Qed.
Lemma lem3833521 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term356 _99546 _99547 x s f g) : term356 _99546 _99547 x s f g.
Proof. exact (h1). Qed.
Lemma lem3833522 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term356 _99546 _99547 x s f g) (h2 : term357 _99546 _99547 x s f g) : term356 _99546 _99547 x s f g.
Proof. exact (@lem3833520 _99546 _99547 x s f g h2 (@lem3833521 _99546 _99547 x s f g h1)). Qed.
Lemma lem3833523 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term356 _99546 _99547 x s f g) : term358 _99546 _99547 x s f g.
Proof. exact (fun h0 : term357 _99546 _99547 x s f g => @lem3833522 _99546 _99547 x s f g h1 h0). Qed.
Lemma lem3833524 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term357 _99546 _99547 x s f g) : term357 _99546 _99547 x s f g.
Proof. exact (h1). Qed.
Lemma lem3833525 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term356 _99546 _99547 x s f g) (h2 : term357 _99546 _99547 x s f g) : term356 _99546 _99547 x s f g.
Proof. exact (@lem3833523 _99546 _99547 x s f g h1 (@lem3833524 _99546 _99547 x s f g h2)). Qed.
Lemma lem3833526 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term357 _99546 _99547 x s f g) : term357 _99546 _99547 x s f g.
Proof. exact (fun h0 : term356 _99546 _99547 x s f g => @lem3833525 _99546 _99547 x s f g h0 h1). Qed.
Lemma lem3833527 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : term359 _99546 _99547 x s f g.
Proof. exact (fun h0 : term357 _99546 _99547 x s f g => @lem3833526 _99546 _99547 x s f g h0). Qed.
Lemma lem3833530 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : term357 _99546 _99547 x s f g.
Proof. exact (@lem3833527 _99546 _99547 x s f g (@lem3833519 _99546 _99547 x s f g)). Qed.
Lemma lem3833531 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : term357 _99546 _99547 x s f g.
Proof. exact (@lem3833530 _99546 _99547 x s f g). Qed.
Lemma lem3833649 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3833650 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term354 _99546 _99547 s f g) = (term360 _99546 _99547 s f g).
Proof. exact (@lem3833649 (term355 _99546 _99547 s f g)). Qed.
Lemma lem3833652 (t : Prop) : (term361 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3833653 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term360 _99546 _99547 s f g) = (term44 _99546 _99547 s f g).
Proof. exact (@lem3833652 (term44 _99546 _99547 s f g)). Qed.
Lemma lem3833656 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term354 _99546 _99547 s f g) = (term44 _99546 _99547 s f g).
Proof. exact (TRANS (@lem3833650 _99546 _99547 s f g) (@lem3833653 _99546 _99547 s f g)). Qed.
Lemma lem3833693 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) : (term362 _99546 _99547 g) = (term362 _99546 _99547 g).
Proof. exact (eq_refl (term362 _99546 _99547 g)). Qed.
Lemma lem3833694 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term363 _99546 _99547 s f g) = (term364 _99546 _99547 s f g).
Proof. exact (MK_COMB (@lem3833693 _99546 _99547 g) (@lem3833656 _99546 _99547 s f g)). Qed.
Lemma lem3833697 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term362 _99546 _99547 f) = (term362 _99546 _99547 f).
Proof. exact (eq_refl (term362 _99546 _99547 f)). Qed.
Lemma lem3833698 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term365 _99546 _99547 s f g) = (term366 _99546 _99547 s f g).
Proof. exact (MK_COMB (@lem3833697 _99546 _99547 f) (@lem3833694 _99546 _99547 s f g)). Qed.
Lemma lem3833701 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term367 _99546 _99547 x s f g) = (term367 _99546 _99547 x s f g).
Proof. exact (eq_refl (term367 _99546 _99547 x s f g)). Qed.
Lemma lem3833702 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term368 _99546 _99547 x s f g) = (term369 _99546 _99547 x s f g).
Proof. exact (MK_COMB (@lem3833701 _99546 _99547 x s f g) (@lem3833698 _99546 _99547 s f g)). Qed.
Lemma lem3833705 {_99546 : Type'} (s : _99546 -> Prop) : (term66 _99546 s) = (term66 _99546 s).
Proof. exact (eq_refl (term66 _99546 s)). Qed.
Lemma lem3833706 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term370 _99546 _99547 x s f g) = (term371 _99546 _99547 x s f g).
Proof. exact (MK_COMB (@lem3833705 _99546 s) (@lem3833702 _99546 _99547 x s f g)). Qed.
Lemma lem3833709 {_99546 : Type'} (x : _99546) (s : _99546 -> Prop) : (term372 _99546 x s) = (term372 _99546 x s).
Proof. exact (eq_refl (term372 _99546 x s)). Qed.
Lemma lem3833710 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term373 _99546 _99547 x s f g) = (term374 _99546 _99547 x s f g).
Proof. exact (MK_COMB (@lem3833709 _99546 x s) (@lem3833706 _99546 _99547 x s f g)). Qed.
Lemma lem3833713 {_99546 _99547 : Type'} (s : _99546 -> Prop) : (term375 _99546 _99547 s) = (term375 _99546 _99547 s).
Proof. exact (eq_refl (term375 _99546 _99547 s)). Qed.
Lemma lem3833714 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term356 _99546 _99547 x s f g) = (term376 _99546 _99547 x s f g).
Proof. exact (MK_COMB (@lem3833713 _99546 _99547 s) (@lem3833710 _99546 _99547 x s f g)). Qed.
Lemma lem3833717 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term377 _99546 _99547 s f g) = (term378 _99546 _99547 s f g).
Proof. exact (fun_ext (fun x : _99546 => @lem3833714 _99546 _99547 x s f g)). Qed.
Lemma lem3833718 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3833719 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term379 _99546 _99547 s f g) = (term380 _99546 _99547 s f g).
Proof. exact (MK_COMB (@lem3833718 _99546) (@lem3833717 _99546 _99547 s f g)). Qed.
Lemma lem3833724 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term381 _99546 _99547 f g) = (term382 _99546 _99547 f g).
Proof. exact (fun_ext (fun s : _99546 -> Prop => @lem3833719 _99546 _99547 s f g)). Qed.
Lemma lem3833725 {_99546 : Type'} : (@all (_99546 -> Prop)) = (@all (_99546 -> Prop)).
Proof. exact (eq_refl (@all (_99546 -> Prop))). Qed.
Lemma lem3833726 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term383 _99546 _99547 f g) = (term384 _99546 _99547 f g).
Proof. exact (MK_COMB (@lem3833725 _99546) (@lem3833724 _99546 _99547 f g)). Qed.
Lemma lem3833731 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) : (term385 _99546 _99547 g) = (term386 _99546 _99547 g).
Proof. exact (fun_ext (fun f : type1411 _99546 _99547 => @lem3833726 _99546 _99547 f g)). Qed.
Lemma lem3833732 {_99546 _99547 : Type'} : (@all (_99546 -> _99547 -> _99547)) = (@all (_99546 -> _99547 -> _99547)).
Proof. exact (eq_refl (@all (_99546 -> _99547 -> _99547))). Qed.
Lemma lem3833733 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) : (term387 _99546 _99547 g) = (term388 _99546 _99547 g).
Proof. exact (MK_COMB (@lem3833732 _99546 _99547) (@lem3833731 _99546 _99547 g)). Qed.
Lemma lem3833738 {_99546 _99547 : Type'} : (term389 _99546 _99547) = (term390 _99546 _99547).
Proof. exact (fun_ext (fun g : type1411 _99546 _99547 => @lem3833733 _99546 _99547 g)). Qed.
Lemma lem3833739 {_99546 _99547 : Type'} : (@all (_99546 -> _99547 -> _99547)) = (@all (_99546 -> _99547 -> _99547)).
Proof. exact (eq_refl (@all (_99546 -> _99547 -> _99547))). Qed.
Lemma lem3833748 {_99546 _99547 : Type'} : (term391 _99546 _99547) = (term392 _99546 _99547).
Proof. exact (MK_COMB (@lem3833739 _99546 _99547) (@lem3833738 _99546 _99547)). Qed.
Lemma lem3833755 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term96 _99546 _99547 y g x s) = (term96 _99546 _99547 y g x s).
Proof. exact (eq_refl (term96 _99546 _99547 y g x s)). Qed.
Lemma lem3833756 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term98 _99546 _99547 y g x) = (term98 _99546 _99547 y g x).
Proof. exact (fun_ext (fun s : _99547 => @lem3833755 _99546 _99547 y g x s)). Qed.
Lemma lem3833757 {_99547 : Type'} : (@all _99547) = (@all _99547).
Proof. exact (eq_refl (@all _99547)). Qed.
Lemma lem3833758 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term99 _99546 _99547 y g x) = (term99 _99546 _99547 y g x).
Proof. exact (MK_COMB (@lem3833757 _99547) (@lem3833756 _99546 _99547 y g x)). Qed.
Lemma lem3833759 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) : (term106 _99546 _99547 g x) = (term106 _99546 _99547 g x).
Proof. exact (fun_ext (fun y : _99546 => @lem3833758 _99546 _99547 y g x)). Qed.
Lemma lem3833760 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3833761 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) : (term108 _99546 _99547 g x) = (term108 _99546 _99547 g x).
Proof. exact (MK_COMB (@lem3833760 _99546) (@lem3833759 _99546 _99547 g x)). Qed.
Lemma lem3833762 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) : (term110 _99546 _99547 g) = (term110 _99546 _99547 g).
Proof. exact (fun_ext (fun x : _99546 => @lem3833761 _99546 _99547 g x)). Qed.
Lemma lem3833763 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3833764 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) : (term19 _99546 _99547 g) = (term19 _99546 _99547 g).
Proof. exact (MK_COMB (@lem3833763 _99546) (@lem3833762 _99546 _99547 g)). Qed.
Lemma lem3833771 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term96 _99546 _99547 y f x s) = (term96 _99546 _99547 y f x s).
Proof. exact (eq_refl (term96 _99546 _99547 y f x s)). Qed.
Lemma lem3833772 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term98 _99546 _99547 y f x) = (term98 _99546 _99547 y f x).
Proof. exact (fun_ext (fun s : _99547 => @lem3833771 _99546 _99547 y f x s)). Qed.
Lemma lem3833773 {_99547 : Type'} : (@all _99547) = (@all _99547).
Proof. exact (eq_refl (@all _99547)). Qed.
Lemma lem3833774 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term99 _99546 _99547 y f x) = (term99 _99546 _99547 y f x).
Proof. exact (MK_COMB (@lem3833773 _99547) (@lem3833772 _99546 _99547 y f x)). Qed.
Lemma lem3833775 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (term106 _99546 _99547 f x) = (term106 _99546 _99547 f x).
Proof. exact (fun_ext (fun y : _99546 => @lem3833774 _99546 _99547 y f x)). Qed.
Lemma lem3833776 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3833777 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (term108 _99546 _99547 f x) = (term108 _99546 _99547 f x).
Proof. exact (MK_COMB (@lem3833776 _99546) (@lem3833775 _99546 _99547 f x)). Qed.
Lemma lem3833778 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term110 _99546 _99547 f) = (term110 _99546 _99547 f).
Proof. exact (fun_ext (fun x : _99546 => @lem3833777 _99546 _99547 f x)). Qed.
Lemma lem3833779 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3833780 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term19 _99546 _99547 f) = (term19 _99546 _99547 f).
Proof. exact (MK_COMB (@lem3833779 _99546) (@lem3833778 _99546 _99547 f)). Qed.
Lemma lem3833781 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3833782 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term113 _99546 _99547 f) = (term113 _99546 _99547 f).
Proof. exact (MK_COMB (@lem3833781) (@lem3833780 _99546 _99547 f)). Qed.
Lemma lem3833783 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term115 _99546 _99547 f g) = (term115 _99546 _99547 f g).
Proof. exact (MK_COMB (@lem3833782 _99546 _99547 f) (@lem3833764 _99546 _99547 g)). Qed.
Lemma lem3833788 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term393 _99546 _99547 s f g x) = (term393 _99546 _99547 s f g x).
Proof. exact (eq_refl (term393 _99546 _99547 s f g x)). Qed.
Lemma lem3833789 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term394 _99546 _99547 s f g) = (term394 _99546 _99547 s f g).
Proof. exact (fun_ext (fun x : _99546 => @lem3833788 _99546 _99547 s f g x)). Qed.
Lemma lem3833790 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3833791 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term395 _99546 _99547 s f g) = (term395 _99546 _99547 s f g).
Proof. exact (MK_COMB (@lem3833790 _99546) (@lem3833789 _99546 _99547 s f g)). Qed.
Lemma lem3833792 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3833793 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term117 _99546 _99547 s f g) = (term117 _99546 _99547 s f g).
Proof. exact (MK_COMB (@lem3833792) (@lem3833791 _99546 _99547 s f g)). Qed.
Lemma lem3833794 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term44 _99546 _99547 s f g) = (term44 _99546 _99547 s f g).
Proof. exact (MK_COMB (@lem3833793 _99546 _99547 s f g) (@lem3833783 _99546 _99547 f g)). Qed.
Lemma lem3833795 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) : ((term93 _99546 _99547 x g y s) = (term93 _99546 _99547 y g x s)) = ((term93 _99546 _99547 x g y s) = (term93 _99546 _99547 y g x s)).
Proof. exact (eq_refl ((term93 _99546 _99547 x g y s) = (term93 _99546 _99547 y g x s))). Qed.
Lemma lem3833796 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term91 _99546 _99547 y g x) = (term91 _99546 _99547 y g x).
Proof. exact (fun_ext (fun s : _99547 => @lem3833795 _99546 _99547 y g x s)). Qed.
Lemma lem3833797 {_99547 : Type'} : (@all _99547) = (@all _99547).
Proof. exact (eq_refl (@all _99547)). Qed.
Lemma lem3833798 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term104 _99546 _99547 y g x) = (term104 _99546 _99547 y g x).
Proof. exact (MK_COMB (@lem3833797 _99547) (@lem3833796 _99546 _99547 y g x)). Qed.
Lemma lem3833803 {_99546 : Type'} (x : _99546) (y : _99546) : (term94 _99546 x y) = (term94 _99546 x y).
Proof. exact (eq_refl (term94 _99546 x y)). Qed.
Lemma lem3833804 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term105 _99546 _99547 y g x) = (term105 _99546 _99547 y g x).
Proof. exact (MK_COMB (@lem3833803 _99546 x y) (@lem3833798 _99546 _99547 y g x)). Qed.
Lemma lem3833805 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) : (term107 _99546 _99547 g x) = (term107 _99546 _99547 g x).
Proof. exact (fun_ext (fun y : _99546 => @lem3833804 _99546 _99547 y g x)). Qed.
Lemma lem3833806 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3833807 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) : (term109 _99546 _99547 g x) = (term109 _99546 _99547 g x).
Proof. exact (MK_COMB (@lem3833806 _99546) (@lem3833805 _99546 _99547 g x)). Qed.
Lemma lem3833808 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) : (term111 _99546 _99547 g) = (term111 _99546 _99547 g).
Proof. exact (fun_ext (fun x : _99546 => @lem3833807 _99546 _99547 g x)). Qed.
Lemma lem3833809 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3833810 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) : (term112 _99546 _99547 g) = (term112 _99546 _99547 g).
Proof. exact (MK_COMB (@lem3833809 _99546) (@lem3833808 _99546 _99547 g)). Qed.
Lemma lem3833811 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3833812 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) : (term362 _99546 _99547 g) = (term362 _99546 _99547 g).
Proof. exact (MK_COMB (@lem3833811) (@lem3833810 _99546 _99547 g)). Qed.
Lemma lem3833813 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term364 _99546 _99547 s f g) = (term364 _99546 _99547 s f g).
Proof. exact (MK_COMB (@lem3833812 _99546 _99547 g) (@lem3833794 _99546 _99547 s f g)). Qed.
Lemma lem3833814 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) (s : _99547) : ((term93 _99546 _99547 x f y s) = (term93 _99546 _99547 y f x s)) = ((term93 _99546 _99547 x f y s) = (term93 _99546 _99547 y f x s)).
Proof. exact (eq_refl ((term93 _99546 _99547 x f y s) = (term93 _99546 _99547 y f x s))). Qed.
Lemma lem3833815 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term91 _99546 _99547 y f x) = (term91 _99546 _99547 y f x).
Proof. exact (fun_ext (fun s : _99547 => @lem3833814 _99546 _99547 y f x s)). Qed.
Lemma lem3833816 {_99547 : Type'} : (@all _99547) = (@all _99547).
Proof. exact (eq_refl (@all _99547)). Qed.
Lemma lem3833817 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term104 _99546 _99547 y f x) = (term104 _99546 _99547 y f x).
Proof. exact (MK_COMB (@lem3833816 _99547) (@lem3833815 _99546 _99547 y f x)). Qed.
Lemma lem3833822 {_99546 : Type'} (x : _99546) (y : _99546) : (term94 _99546 x y) = (term94 _99546 x y).
Proof. exact (eq_refl (term94 _99546 x y)). Qed.
Lemma lem3833823 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term105 _99546 _99547 y f x) = (term105 _99546 _99547 y f x).
Proof. exact (MK_COMB (@lem3833822 _99546 x y) (@lem3833817 _99546 _99547 y f x)). Qed.
Lemma lem3833824 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (term107 _99546 _99547 f x) = (term107 _99546 _99547 f x).
Proof. exact (fun_ext (fun y : _99546 => @lem3833823 _99546 _99547 y f x)). Qed.
Lemma lem3833825 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3833826 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (term109 _99546 _99547 f x) = (term109 _99546 _99547 f x).
Proof. exact (MK_COMB (@lem3833825 _99546) (@lem3833824 _99546 _99547 f x)). Qed.
Lemma lem3833827 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term111 _99546 _99547 f) = (term111 _99546 _99547 f).
Proof. exact (fun_ext (fun x : _99546 => @lem3833826 _99546 _99547 f x)). Qed.
Lemma lem3833828 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3833829 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term112 _99546 _99547 f) = (term112 _99546 _99547 f).
Proof. exact (MK_COMB (@lem3833828 _99546) (@lem3833827 _99546 _99547 f)). Qed.
Lemma lem3833830 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3833831 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term362 _99546 _99547 f) = (term362 _99546 _99547 f).
Proof. exact (MK_COMB (@lem3833830) (@lem3833829 _99546 _99547 f)). Qed.
Lemma lem3833832 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term366 _99546 _99547 s f g) = (term366 _99546 _99547 s f g).
Proof. exact (MK_COMB (@lem3833831 _99546 _99547 f) (@lem3833813 _99546 _99547 s f g)). Qed.
Lemma lem3833841 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x' : _99546) : (term271 _99546 _99547 x s f g x') = (term271 _99546 _99547 x s f g x').
Proof. exact (eq_refl (term271 _99546 _99547 x s f g x')). Qed.
Lemma lem3833842 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term273 _99546 _99547 x s f g) = (term273 _99546 _99547 x s f g).
Proof. exact (fun_ext (fun x' : _99546 => @lem3833841 _99546 _99547 x s f g x')). Qed.
Lemma lem3833843 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3833844 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term275 _99546 _99547 x s f g) = (term275 _99546 _99547 x s f g).
Proof. exact (MK_COMB (@lem3833843 _99546) (@lem3833842 _99546 _99547 x s f g)). Qed.
Lemma lem3833845 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3833846 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term367 _99546 _99547 x s f g) = (term367 _99546 _99547 x s f g).
Proof. exact (MK_COMB (@lem3833845) (@lem3833844 _99546 _99547 x s f g)). Qed.
Lemma lem3833847 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term369 _99546 _99547 x s f g) = (term369 _99546 _99547 x s f g).
Proof. exact (MK_COMB (@lem3833846 _99546 _99547 x s f g) (@lem3833832 _99546 _99547 s f g)). Qed.
Lemma lem3833850 {_99546 : Type'} (s : _99546 -> Prop) : (term66 _99546 s) = (term66 _99546 s).
Proof. exact (eq_refl (term66 _99546 s)). Qed.
Lemma lem3833851 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term371 _99546 _99547 x s f g) = (term371 _99546 _99547 x s f g).
Proof. exact (MK_COMB (@lem3833850 _99546 s) (@lem3833847 _99546 _99547 x s f g)). Qed.
Lemma lem3833856 {_99546 : Type'} (x : _99546) (s : _99546 -> Prop) : (term372 _99546 x s) = (term372 _99546 x s).
Proof. exact (eq_refl (term372 _99546 x s)). Qed.
Lemma lem3833857 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term374 _99546 _99547 x s f g) = (term374 _99546 _99547 x s f g).
Proof. exact (MK_COMB (@lem3833856 _99546 x s) (@lem3833851 _99546 _99547 x s f g)). Qed.
Lemma lem3833858 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) (b : _99547) : ((@ITSET _99547 _99546 f s b) = (@ITSET _99547 _99546 g s b)) = ((@ITSET _99547 _99546 f s b) = (@ITSET _99547 _99546 g s b)).
Proof. exact (eq_refl ((@ITSET _99547 _99546 f s b) = (@ITSET _99547 _99546 g s b))). Qed.
Lemma lem3833859 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term77 _99546 _99547 f g s) = (term77 _99546 _99547 f g s).
Proof. exact (fun_ext (fun b : _99547 => @lem3833858 _99546 _99547 f g s b)). Qed.
Lemma lem3833860 {_99547 : Type'} : (@all _99547) = (@all _99547).
Proof. exact (eq_refl (@all _99547)). Qed.
Lemma lem3833861 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term86 _99546 _99547 f g s) = (term86 _99546 _99547 f g s).
Proof. exact (MK_COMB (@lem3833860 _99547) (@lem3833859 _99546 _99547 f g s)). Qed.
Lemma lem3833862 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) : ((term93 _99546 _99547 x g y s) = (term93 _99546 _99547 y g x s)) = ((term93 _99546 _99547 x g y s) = (term93 _99546 _99547 y g x s)).
Proof. exact (eq_refl ((term93 _99546 _99547 x g y s) = (term93 _99546 _99547 y g x s))). Qed.
Lemma lem3833863 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term91 _99546 _99547 y g x) = (term91 _99546 _99547 y g x).
Proof. exact (fun_ext (fun s : _99547 => @lem3833862 _99546 _99547 y g x s)). Qed.
Lemma lem3833864 {_99547 : Type'} : (@all _99547) = (@all _99547).
Proof. exact (eq_refl (@all _99547)). Qed.
Lemma lem3833865 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term104 _99546 _99547 y g x) = (term104 _99546 _99547 y g x).
Proof. exact (MK_COMB (@lem3833864 _99547) (@lem3833863 _99546 _99547 y g x)). Qed.
Lemma lem3833870 {_99546 : Type'} (x : _99546) (y : _99546) : (term94 _99546 x y) = (term94 _99546 x y).
Proof. exact (eq_refl (term94 _99546 x y)). Qed.
Lemma lem3833871 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term105 _99546 _99547 y g x) = (term105 _99546 _99547 y g x).
Proof. exact (MK_COMB (@lem3833870 _99546 x y) (@lem3833865 _99546 _99547 y g x)). Qed.
Lemma lem3833872 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) : (term107 _99546 _99547 g x) = (term107 _99546 _99547 g x).
Proof. exact (fun_ext (fun y : _99546 => @lem3833871 _99546 _99547 y g x)). Qed.
Lemma lem3833873 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3833874 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) : (term109 _99546 _99547 g x) = (term109 _99546 _99547 g x).
Proof. exact (MK_COMB (@lem3833873 _99546) (@lem3833872 _99546 _99547 g x)). Qed.
Lemma lem3833875 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) : (term111 _99546 _99547 g) = (term111 _99546 _99547 g).
Proof. exact (fun_ext (fun x : _99546 => @lem3833874 _99546 _99547 g x)). Qed.
Lemma lem3833876 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3833877 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) : (term112 _99546 _99547 g) = (term112 _99546 _99547 g).
Proof. exact (MK_COMB (@lem3833876 _99546) (@lem3833875 _99546 _99547 g)). Qed.
Lemma lem3833878 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) (s : _99547) : ((term93 _99546 _99547 x f y s) = (term93 _99546 _99547 y f x s)) = ((term93 _99546 _99547 x f y s) = (term93 _99546 _99547 y f x s)).
Proof. exact (eq_refl ((term93 _99546 _99547 x f y s) = (term93 _99546 _99547 y f x s))). Qed.
Lemma lem3833879 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term91 _99546 _99547 y f x) = (term91 _99546 _99547 y f x).
Proof. exact (fun_ext (fun s : _99547 => @lem3833878 _99546 _99547 y f x s)). Qed.
Lemma lem3833880 {_99547 : Type'} : (@all _99547) = (@all _99547).
Proof. exact (eq_refl (@all _99547)). Qed.
Lemma lem3833881 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term104 _99546 _99547 y f x) = (term104 _99546 _99547 y f x).
Proof. exact (MK_COMB (@lem3833880 _99547) (@lem3833879 _99546 _99547 y f x)). Qed.
Lemma lem3833886 {_99546 : Type'} (x : _99546) (y : _99546) : (term94 _99546 x y) = (term94 _99546 x y).
Proof. exact (eq_refl (term94 _99546 x y)). Qed.
Lemma lem3833887 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term105 _99546 _99547 y f x) = (term105 _99546 _99547 y f x).
Proof. exact (MK_COMB (@lem3833886 _99546 x y) (@lem3833881 _99546 _99547 y f x)). Qed.
Lemma lem3833888 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (term107 _99546 _99547 f x) = (term107 _99546 _99547 f x).
Proof. exact (fun_ext (fun y : _99546 => @lem3833887 _99546 _99547 y f x)). Qed.
Lemma lem3833889 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3833890 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (term109 _99546 _99547 f x) = (term109 _99546 _99547 f x).
Proof. exact (MK_COMB (@lem3833889 _99546) (@lem3833888 _99546 _99547 f x)). Qed.
Lemma lem3833891 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term111 _99546 _99547 f) = (term111 _99546 _99547 f).
Proof. exact (fun_ext (fun x : _99546 => @lem3833890 _99546 _99547 f x)). Qed.
Lemma lem3833892 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3833893 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term112 _99546 _99547 f) = (term112 _99546 _99547 f).
Proof. exact (MK_COMB (@lem3833892 _99546) (@lem3833891 _99546 _99547 f)). Qed.
Lemma lem3833894 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3833895 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term114 _99546 _99547 f) = (term114 _99546 _99547 f).
Proof. exact (MK_COMB (@lem3833894) (@lem3833893 _99546 _99547 f)). Qed.
Lemma lem3833896 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term116 _99546 _99547 f g) = (term116 _99546 _99547 f g).
Proof. exact (MK_COMB (@lem3833895 _99546 _99547 f) (@lem3833877 _99546 _99547 g)). Qed.
Lemma lem3833901 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term393 _99546 _99547 s f g x) = (term393 _99546 _99547 s f g x).
Proof. exact (eq_refl (term393 _99546 _99547 s f g x)). Qed.
Lemma lem3833902 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term394 _99546 _99547 s f g) = (term394 _99546 _99547 s f g).
Proof. exact (fun_ext (fun x : _99546 => @lem3833901 _99546 _99547 s f g x)). Qed.
Lemma lem3833903 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3833904 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term395 _99546 _99547 s f g) = (term395 _99546 _99547 s f g).
Proof. exact (MK_COMB (@lem3833903 _99546) (@lem3833902 _99546 _99547 s f g)). Qed.
Lemma lem3833905 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3833906 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term117 _99546 _99547 s f g) = (term117 _99546 _99547 s f g).
Proof. exact (MK_COMB (@lem3833905) (@lem3833904 _99546 _99547 s f g)). Qed.
Lemma lem3833907 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term118 _99546 _99547 s f g) = (term118 _99546 _99547 s f g).
Proof. exact (MK_COMB (@lem3833906 _99546 _99547 s f g) (@lem3833896 _99546 _99547 f g)). Qed.
Lemma lem3833908 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3833909 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term119 _99546 _99547 s f g) = (term119 _99546 _99547 s f g).
Proof. exact (MK_COMB (@lem3833908) (@lem3833907 _99546 _99547 s f g)). Qed.
Lemma lem3833910 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term120 _99546 _99547 f g s) = (term120 _99546 _99547 f g s).
Proof. exact (MK_COMB (@lem3833909 _99546 _99547 s f g) (@lem3833861 _99546 _99547 f g s)). Qed.
Lemma lem3833911 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term128 _99546 _99547 f s) = (term128 _99546 _99547 f s).
Proof. exact (fun_ext (fun g : type1411 _99546 _99547 => @lem3833910 _99546 _99547 f g s)). Qed.
Lemma lem3833912 {_99546 _99547 : Type'} : (@all (_99546 -> _99547 -> _99547)) = (@all (_99546 -> _99547 -> _99547)).
Proof. exact (eq_refl (@all (_99546 -> _99547 -> _99547))). Qed.
Lemma lem3833913 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term136 _99546 _99547 f s) = (term136 _99546 _99547 f s).
Proof. exact (MK_COMB (@lem3833912 _99546 _99547) (@lem3833911 _99546 _99547 f s)). Qed.
Lemma lem3833914 {_99546 _99547 : Type'} (s : _99546 -> Prop) : (term142 _99546 _99547 s) = (term142 _99546 _99547 s).
Proof. exact (fun_ext (fun f : type1411 _99546 _99547 => @lem3833913 _99546 _99547 f s)). Qed.
Lemma lem3833915 {_99546 _99547 : Type'} : (@all (_99546 -> _99547 -> _99547)) = (@all (_99546 -> _99547 -> _99547)).
Proof. exact (eq_refl (@all (_99546 -> _99547 -> _99547))). Qed.
Lemma lem3833916 {_99546 _99547 : Type'} (s : _99546 -> Prop) : (term150 _99546 _99547 s) = (term150 _99546 _99547 s).
Proof. exact (MK_COMB (@lem3833915 _99546 _99547) (@lem3833914 _99546 _99547 s)). Qed.
Lemma lem3833917 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3833918 {_99546 _99547 : Type'} (s : _99546 -> Prop) : (term375 _99546 _99547 s) = (term375 _99546 _99547 s).
Proof. exact (MK_COMB (@lem3833917) (@lem3833916 _99546 _99547 s)). Qed.
Lemma lem3833919 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term376 _99546 _99547 x s f g) = (term376 _99546 _99547 x s f g).
Proof. exact (MK_COMB (@lem3833918 _99546 _99547 s) (@lem3833857 _99546 _99547 x s f g)). Qed.
Lemma lem3833920 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term378 _99546 _99547 s f g) = (term378 _99546 _99547 s f g).
Proof. exact (fun_ext (fun x : _99546 => @lem3833919 _99546 _99547 x s f g)). Qed.
Lemma lem3833921 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3833922 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term380 _99546 _99547 s f g) = (term380 _99546 _99547 s f g).
Proof. exact (MK_COMB (@lem3833921 _99546) (@lem3833920 _99546 _99547 s f g)). Qed.
Lemma lem3833923 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term382 _99546 _99547 f g) = (term382 _99546 _99547 f g).
Proof. exact (fun_ext (fun s : _99546 -> Prop => @lem3833922 _99546 _99547 s f g)). Qed.
Lemma lem3833924 {_99546 : Type'} : (@all (_99546 -> Prop)) = (@all (_99546 -> Prop)).
Proof. exact (eq_refl (@all (_99546 -> Prop))). Qed.
Lemma lem3833925 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term384 _99546 _99547 f g) = (term384 _99546 _99547 f g).
Proof. exact (MK_COMB (@lem3833924 _99546) (@lem3833923 _99546 _99547 f g)). Qed.
Lemma lem3833926 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) : (term386 _99546 _99547 g) = (term386 _99546 _99547 g).
Proof. exact (fun_ext (fun f : type1411 _99546 _99547 => @lem3833925 _99546 _99547 f g)). Qed.
Lemma lem3833927 {_99546 _99547 : Type'} : (@all (_99546 -> _99547 -> _99547)) = (@all (_99546 -> _99547 -> _99547)).
Proof. exact (eq_refl (@all (_99546 -> _99547 -> _99547))). Qed.
Lemma lem3833928 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) : (term388 _99546 _99547 g) = (term388 _99546 _99547 g).
Proof. exact (MK_COMB (@lem3833927 _99546 _99547) (@lem3833926 _99546 _99547 g)). Qed.
Lemma lem3833929 {_99546 _99547 : Type'} : (term390 _99546 _99547) = (term390 _99546 _99547).
Proof. exact (fun_ext (fun g : type1411 _99546 _99547 => @lem3833928 _99546 _99547 g)). Qed.
Lemma lem3833930 {_99546 _99547 : Type'} : (@all (_99546 -> _99547 -> _99547)) = (@all (_99546 -> _99547 -> _99547)).
Proof. exact (eq_refl (@all (_99546 -> _99547 -> _99547))). Qed.
Lemma lem3833931 {_99546 _99547 : Type'} : (term392 _99546 _99547) = (term392 _99546 _99547).
Proof. exact (MK_COMB (@lem3833930 _99546 _99547) (@lem3833929 _99546 _99547)). Qed.
Lemma lem3834144 {_99546 _99547 : Type'} : (term391 _99546 _99547) = (term392 _99546 _99547).
Proof. exact (TRANS (@lem3833748 _99546 _99547) (@lem3833931 _99546 _99547)). Qed.
Lemma lem3834145 {_99546 _99547 : Type'} : (term392 _99546 _99547) = (term391 _99546 _99547).
Proof. exact (SYM (@lem3834144 _99546 _99547)). Qed.
Lemma lem3834146 {_99546 _99547 : Type'} (s : _99546 -> Prop) (h1 : term150 _99546 _99547 s) : term150 _99546 _99547 s.
Proof. exact (h1). Qed.
Lemma lem3834149 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term275 _99546 _99547 x s f g) : term275 _99546 _99547 x s f g.
Proof. exact (h1). Qed.
Lemma lem3834150 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (h1 : term112 _99546 _99547 f) : term112 _99546 _99547 f.
Proof. exact (h1). Qed.
Lemma lem3834151 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (h1 : term112 _99546 _99547 g) : term112 _99546 _99547 g.
Proof. exact (h1). Qed.
Lemma lem3834153 (p : Prop) : p = (term353 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3834154 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term44 _99546 _99547 s f g) = (term354 _99546 _99547 s f g).
Proof. exact (@lem3834153 (term44 _99546 _99547 s f g)). Qed.
Lemma lem3834155 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term354 _99546 _99547 s f g) = (term44 _99546 _99547 s f g).
Proof. exact (SYM (@lem3834154 _99546 _99547 s f g)). Qed.
Lemma lem3834156 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term355 _99546 _99547 s f g) : term355 _99546 _99547 s f g.
Proof. exact (h1). Qed.
Lemma lem3834163 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term396 _99546 _99547 s f g x) = (term397 _99546 _99547 s f g x).
Proof. exact (@lem17362 (@IN _99546 x s) ((f x) = (g x))). Qed.
Lemma lem3834164 {_99546 : Type'} (P : _99546 -> Prop) : (term398 _99546 P) = (term399 _99546 P).
Proof. exact (@lem18392 _99546 P). Qed.
Lemma lem3834165 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term400 _99546 _99547 s f g) = (term401 _99546 _99547 s f g).
Proof. exact (@lem3834164 _99546 (term394 _99546 _99547 s f g)). Qed.
Lemma lem3834166 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term402 _99546 _99547 s f g x) = (term393 _99546 _99547 s f g x).
Proof. exact (eq_refl (term402 _99546 _99547 s f g x)). Qed.
Lemma lem3834167 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3834168 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term403 _99546 _99547 s f g x) = (term396 _99546 _99547 s f g x).
Proof. exact (MK_COMB (@lem3834167) (@lem3834166 _99546 _99547 s f g x)). Qed.
Lemma lem3834169 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term403 _99546 _99547 s f g x) = (term397 _99546 _99547 s f g x).
Proof. exact (TRANS (@lem3834168 _99546 _99547 s f g x) (@lem3834163 _99546 _99547 s f g x)). Qed.
Lemma lem3834170 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term404 _99546 _99547 s f g) = (term405 _99546 _99547 s f g).
Proof. exact (fun_ext (fun x : _99546 => @lem3834169 _99546 _99547 s f g x)). Qed.
Lemma lem3834171 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3834172 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term401 _99546 _99547 s f g) = (term406 _99546 _99547 s f g).
Proof. exact (MK_COMB (@lem3834171 _99546) (@lem3834170 _99546 _99547 s f g)). Qed.
Lemma lem3834173 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term400 _99546 _99547 s f g) = (term406 _99546 _99547 s f g).
Proof. exact (TRANS (@lem3834165 _99546 _99547 s f g) (@lem3834172 _99546 _99547 s f g)). Qed.
Lemma lem3834176 {_99547 : Type'} (P : _99547 -> Prop) : (term398 _99547 P) = (term399 _99547 P).
Proof. exact (@lem18392 _99547 P). Qed.
Lemma lem3834177 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term407 _99546 _99547 y f x) = (term408 _99546 _99547 y f x).
Proof. exact (@lem3834176 _99547 (term91 _99546 _99547 y f x)). Qed.
Lemma lem3834178 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term92 _99546 _99547 y f x s) = ((term93 _99546 _99547 x f y s) = (term93 _99546 _99547 y f x s)).
Proof. exact (eq_refl (term92 _99546 _99547 y f x s)). Qed.
Lemma lem3834179 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3834181 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term409 _99546 _99547 y f x s) = (term410 _99546 _99547 y f x s).
Proof. exact (MK_COMB (@lem3834179) (@lem3834178 _99546 _99547 y f x s)). Qed.
Lemma lem3834182 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term411 _99546 _99547 y f x) = (term412 _99546 _99547 y f x).
Proof. exact (fun_ext (fun s : _99547 => @lem3834181 _99546 _99547 y f x s)). Qed.
Lemma lem3834183 {_99547 : Type'} : (@ex _99547) = (@ex _99547).
Proof. exact (eq_refl (@ex _99547)). Qed.
Lemma lem3834184 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term408 _99546 _99547 y f x) = (term413 _99546 _99547 y f x).
Proof. exact (MK_COMB (@lem3834183 _99547) (@lem3834182 _99546 _99547 y f x)). Qed.
Lemma lem3834185 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term407 _99546 _99547 y f x) = (term413 _99546 _99547 y f x).
Proof. exact (TRANS (@lem3834177 _99546 _99547 y f x) (@lem3834184 _99546 _99547 y f x)). Qed.
Lemma lem3834187 {_99546 : Type'} (x : _99546) (y : _99546) : (term414 _99546 x y) = (term414 _99546 x y).
Proof. exact (eq_refl (term414 _99546 x y)). Qed.
Lemma lem3834188 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term415 _99546 _99547 y f x) = (term416 _99546 _99547 y f x).
Proof. exact (MK_COMB (@lem3834187 _99546 x y) (@lem3834185 _99546 _99547 y f x)). Qed.
Lemma lem3834189 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term417 _99546 _99547 y f x) = (term415 _99546 _99547 y f x).
Proof. exact (@lem17362 (term90 _99546 x y) (term104 _99546 _99547 y f x)). Qed.
Lemma lem3834190 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term417 _99546 _99547 y f x) = (term416 _99546 _99547 y f x).
Proof. exact (TRANS (@lem3834189 _99546 _99547 y f x) (@lem3834188 _99546 _99547 y f x)). Qed.
Lemma lem3834191 {_99546 : Type'} (P : _99546 -> Prop) : (term398 _99546 P) = (term399 _99546 P).
Proof. exact (@lem18392 _99546 P). Qed.
Lemma lem3834192 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (term418 _99546 _99547 f x) = (term419 _99546 _99547 f x).
Proof. exact (@lem3834191 _99546 (term107 _99546 _99547 f x)). Qed.
Lemma lem3834193 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term219 _99546 _99547 f x y) = (term105 _99546 _99547 y f x).
Proof. exact (eq_refl (term219 _99546 _99547 f x y)). Qed.
Lemma lem3834194 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3834195 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term420 _99546 _99547 f x y) = (term417 _99546 _99547 y f x).
Proof. exact (MK_COMB (@lem3834194) (@lem3834193 _99546 _99547 y f x)). Qed.
Lemma lem3834196 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term420 _99546 _99547 f x y) = (term416 _99546 _99547 y f x).
Proof. exact (TRANS (@lem3834195 _99546 _99547 y f x) (@lem3834190 _99546 _99547 y f x)). Qed.
Lemma lem3834197 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (term421 _99546 _99547 f x) = (term422 _99546 _99547 f x).
Proof. exact (fun_ext (fun y : _99546 => @lem3834196 _99546 _99547 y f x)). Qed.
Lemma lem3834198 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3834199 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (term419 _99546 _99547 f x) = (term423 _99546 _99547 f x).
Proof. exact (MK_COMB (@lem3834198 _99546) (@lem3834197 _99546 _99547 f x)). Qed.
Lemma lem3834200 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (term418 _99546 _99547 f x) = (term423 _99546 _99547 f x).
Proof. exact (TRANS (@lem3834192 _99546 _99547 f x) (@lem3834199 _99546 _99547 f x)). Qed.
Lemma lem3834201 {_99546 : Type'} (P : _99546 -> Prop) : (term398 _99546 P) = (term399 _99546 P).
Proof. exact (@lem18392 _99546 P). Qed.
Lemma lem3834202 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term424 _99546 _99547 f) = (term425 _99546 _99547 f).
Proof. exact (@lem3834201 _99546 (term111 _99546 _99547 f)). Qed.
Lemma lem3834203 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (term218 _99546 _99547 f x) = (term109 _99546 _99547 f x).
Proof. exact (eq_refl (term218 _99546 _99547 f x)). Qed.
Lemma lem3834204 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3834205 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (term426 _99546 _99547 f x) = (term418 _99546 _99547 f x).
Proof. exact (MK_COMB (@lem3834204) (@lem3834203 _99546 _99547 f x)). Qed.
Lemma lem3834206 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (term426 _99546 _99547 f x) = (term423 _99546 _99547 f x).
Proof. exact (TRANS (@lem3834205 _99546 _99547 f x) (@lem3834200 _99546 _99547 f x)). Qed.
Lemma lem3834207 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term427 _99546 _99547 f) = (term428 _99546 _99547 f).
Proof. exact (fun_ext (fun x : _99546 => @lem3834206 _99546 _99547 f x)). Qed.
Lemma lem3834208 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3834209 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term425 _99546 _99547 f) = (term429 _99546 _99547 f).
Proof. exact (MK_COMB (@lem3834208 _99546) (@lem3834207 _99546 _99547 f)). Qed.
Lemma lem3834210 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term424 _99546 _99547 f) = (term429 _99546 _99547 f).
Proof. exact (TRANS (@lem3834202 _99546 _99547 f) (@lem3834209 _99546 _99547 f)). Qed.
Lemma lem3834213 {_99547 : Type'} (P : _99547 -> Prop) : (term398 _99547 P) = (term399 _99547 P).
Proof. exact (@lem18392 _99547 P). Qed.
Lemma lem3834214 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term407 _99546 _99547 y g x) = (term408 _99546 _99547 y g x).
Proof. exact (@lem3834213 _99547 (term91 _99546 _99547 y g x)). Qed.
Lemma lem3834215 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term92 _99546 _99547 y g x s) = ((term93 _99546 _99547 x g y s) = (term93 _99546 _99547 y g x s)).
Proof. exact (eq_refl (term92 _99546 _99547 y g x s)). Qed.
Lemma lem3834216 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3834218 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term409 _99546 _99547 y g x s) = (term410 _99546 _99547 y g x s).
Proof. exact (MK_COMB (@lem3834216) (@lem3834215 _99546 _99547 y g x s)). Qed.
Lemma lem3834219 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term411 _99546 _99547 y g x) = (term412 _99546 _99547 y g x).
Proof. exact (fun_ext (fun s : _99547 => @lem3834218 _99546 _99547 y g x s)). Qed.
Lemma lem3834220 {_99547 : Type'} : (@ex _99547) = (@ex _99547).
Proof. exact (eq_refl (@ex _99547)). Qed.
Lemma lem3834221 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term408 _99546 _99547 y g x) = (term413 _99546 _99547 y g x).
Proof. exact (MK_COMB (@lem3834220 _99547) (@lem3834219 _99546 _99547 y g x)). Qed.
Lemma lem3834222 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term407 _99546 _99547 y g x) = (term413 _99546 _99547 y g x).
Proof. exact (TRANS (@lem3834214 _99546 _99547 y g x) (@lem3834221 _99546 _99547 y g x)). Qed.
Lemma lem3834224 {_99546 : Type'} (x : _99546) (y : _99546) : (term414 _99546 x y) = (term414 _99546 x y).
Proof. exact (eq_refl (term414 _99546 x y)). Qed.
Lemma lem3834225 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term415 _99546 _99547 y g x) = (term416 _99546 _99547 y g x).
Proof. exact (MK_COMB (@lem3834224 _99546 x y) (@lem3834222 _99546 _99547 y g x)). Qed.
Lemma lem3834226 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term417 _99546 _99547 y g x) = (term415 _99546 _99547 y g x).
Proof. exact (@lem17362 (term90 _99546 x y) (term104 _99546 _99547 y g x)). Qed.
Lemma lem3834227 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term417 _99546 _99547 y g x) = (term416 _99546 _99547 y g x).
Proof. exact (TRANS (@lem3834226 _99546 _99547 y g x) (@lem3834225 _99546 _99547 y g x)). Qed.
Lemma lem3834228 {_99546 : Type'} (P : _99546 -> Prop) : (term398 _99546 P) = (term399 _99546 P).
Proof. exact (@lem18392 _99546 P). Qed.
Lemma lem3834229 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) : (term418 _99546 _99547 g x) = (term419 _99546 _99547 g x).
Proof. exact (@lem3834228 _99546 (term107 _99546 _99547 g x)). Qed.
Lemma lem3834230 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term219 _99546 _99547 g x y) = (term105 _99546 _99547 y g x).
Proof. exact (eq_refl (term219 _99546 _99547 g x y)). Qed.
Lemma lem3834231 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3834232 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term420 _99546 _99547 g x y) = (term417 _99546 _99547 y g x).
Proof. exact (MK_COMB (@lem3834231) (@lem3834230 _99546 _99547 y g x)). Qed.
Lemma lem3834233 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term420 _99546 _99547 g x y) = (term416 _99546 _99547 y g x).
Proof. exact (TRANS (@lem3834232 _99546 _99547 y g x) (@lem3834227 _99546 _99547 y g x)). Qed.
Lemma lem3834234 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) : (term421 _99546 _99547 g x) = (term422 _99546 _99547 g x).
Proof. exact (fun_ext (fun y : _99546 => @lem3834233 _99546 _99547 y g x)). Qed.
Lemma lem3834235 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3834236 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) : (term419 _99546 _99547 g x) = (term423 _99546 _99547 g x).
Proof. exact (MK_COMB (@lem3834235 _99546) (@lem3834234 _99546 _99547 g x)). Qed.
Lemma lem3834237 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) : (term418 _99546 _99547 g x) = (term423 _99546 _99547 g x).
Proof. exact (TRANS (@lem3834229 _99546 _99547 g x) (@lem3834236 _99546 _99547 g x)). Qed.
Lemma lem3834238 {_99546 : Type'} (P : _99546 -> Prop) : (term398 _99546 P) = (term399 _99546 P).
Proof. exact (@lem18392 _99546 P). Qed.
Lemma lem3834239 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) : (term424 _99546 _99547 g) = (term425 _99546 _99547 g).
Proof. exact (@lem3834238 _99546 (term111 _99546 _99547 g)). Qed.
Lemma lem3834240 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) : (term218 _99546 _99547 g x) = (term109 _99546 _99547 g x).
Proof. exact (eq_refl (term218 _99546 _99547 g x)). Qed.
Lemma lem3834241 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3834242 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) : (term426 _99546 _99547 g x) = (term418 _99546 _99547 g x).
Proof. exact (MK_COMB (@lem3834241) (@lem3834240 _99546 _99547 g x)). Qed.
Lemma lem3834243 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) : (term426 _99546 _99547 g x) = (term423 _99546 _99547 g x).
Proof. exact (TRANS (@lem3834242 _99546 _99547 g x) (@lem3834237 _99546 _99547 g x)). Qed.
Lemma lem3834244 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) : (term427 _99546 _99547 g) = (term428 _99546 _99547 g).
Proof. exact (fun_ext (fun x : _99546 => @lem3834243 _99546 _99547 g x)). Qed.
Lemma lem3834245 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3834246 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) : (term425 _99546 _99547 g) = (term429 _99546 _99547 g).
Proof. exact (MK_COMB (@lem3834245 _99546) (@lem3834244 _99546 _99547 g)). Qed.
Lemma lem3834247 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) : (term424 _99546 _99547 g) = (term429 _99546 _99547 g).
Proof. exact (TRANS (@lem3834239 _99546 _99547 g) (@lem3834246 _99546 _99547 g)). Qed.
Lemma lem3834248 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3834249 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term430 _99546 _99547 f) = (term431 _99546 _99547 f).
Proof. exact (MK_COMB (@lem3834248) (@lem3834210 _99546 _99547 f)). Qed.
Lemma lem3834250 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term432 _99546 _99547 f g) = (term433 _99546 _99547 f g).
Proof. exact (MK_COMB (@lem3834249 _99546 _99547 f) (@lem3834247 _99546 _99547 g)). Qed.
Lemma lem3834251 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term434 _99546 _99547 f g) = (term432 _99546 _99547 f g).
Proof. exact (@lem17045 (term112 _99546 _99547 f) (term112 _99546 _99547 g)). Qed.
Lemma lem3834252 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term434 _99546 _99547 f g) = (term433 _99546 _99547 f g).
Proof. exact (TRANS (@lem3834251 _99546 _99547 f g) (@lem3834250 _99546 _99547 f g)). Qed.
Lemma lem3834253 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3834254 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term435 _99546 _99547 s f g) = (term436 _99546 _99547 s f g).
Proof. exact (MK_COMB (@lem3834253) (@lem3834173 _99546 _99547 s f g)). Qed.
Lemma lem3834255 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term437 _99546 _99547 s f g) = (term438 _99546 _99547 s f g).
Proof. exact (MK_COMB (@lem3834254 _99546 _99547 s f g) (@lem3834252 _99546 _99547 f g)). Qed.
Lemma lem3834256 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term439 _99546 _99547 s f g) = (term437 _99546 _99547 s f g).
Proof. exact (@lem17045 (term395 _99546 _99547 s f g) (term116 _99546 _99547 f g)). Qed.
Lemma lem3834257 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term439 _99546 _99547 s f g) = (term438 _99546 _99547 s f g).
Proof. exact (TRANS (@lem3834256 _99546 _99547 s f g) (@lem3834255 _99546 _99547 s f g)). Qed.
Lemma lem3834258 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) (b : _99547) : ((@ITSET _99547 _99546 f s b) = (@ITSET _99547 _99546 g s b)) = ((@ITSET _99547 _99546 f s b) = (@ITSET _99547 _99546 g s b)).
Proof. exact (eq_refl ((@ITSET _99547 _99546 f s b) = (@ITSET _99547 _99546 g s b))). Qed.
Lemma lem3834259 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term77 _99546 _99547 f g s) = (term77 _99546 _99547 f g s).
Proof. exact (fun_ext (fun b : _99547 => @lem3834258 _99546 _99547 f g s b)). Qed.
Lemma lem3834260 {_99547 : Type'} : (@all _99547) = (@all _99547).
Proof. exact (eq_refl (@all _99547)). Qed.
Lemma lem3834261 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term86 _99546 _99547 f g s) = (term86 _99546 _99547 f g s).
Proof. exact (MK_COMB (@lem3834260 _99547) (@lem3834259 _99546 _99547 f g s)). Qed.
Lemma lem3834262 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3834263 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term440 _99546 _99547 s f g) = (term441 _99546 _99547 s f g).
Proof. exact (MK_COMB (@lem3834262) (@lem3834257 _99546 _99547 s f g)). Qed.
Lemma lem3834264 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term442 _99546 _99547 f g s) = (term443 _99546 _99547 f g s).
Proof. exact (MK_COMB (@lem3834263 _99546 _99547 s f g) (@lem3834261 _99546 _99547 f g s)). Qed.
Lemma lem3834265 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term120 _99546 _99547 f g s) = (term442 _99546 _99547 f g s).
Proof. exact (@lem17265 (term118 _99546 _99547 s f g) (term86 _99546 _99547 f g s)). Qed.
Lemma lem3834266 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term120 _99546 _99547 f g s) = (term443 _99546 _99547 f g s).
Proof. exact (TRANS (@lem3834265 _99546 _99547 f g s) (@lem3834264 _99546 _99547 f g s)). Qed.
Lemma lem3834267 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term128 _99546 _99547 f s) = (term444 _99546 _99547 f s).
Proof. exact (fun_ext (fun g : type1411 _99546 _99547 => @lem3834266 _99546 _99547 f g s)). Qed.
Lemma lem3834268 {_99546 _99547 : Type'} : (@all (_99546 -> _99547 -> _99547)) = (@all (_99546 -> _99547 -> _99547)).
Proof. exact (eq_refl (@all (_99546 -> _99547 -> _99547))). Qed.
Lemma lem3834269 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term136 _99546 _99547 f s) = (term445 _99546 _99547 f s).
Proof. exact (MK_COMB (@lem3834268 _99546 _99547) (@lem3834267 _99546 _99547 f s)). Qed.
Lemma lem3834270 {_99546 _99547 : Type'} (s : _99546 -> Prop) : (term142 _99546 _99547 s) = (term446 _99546 _99547 s).
Proof. exact (fun_ext (fun f : type1411 _99546 _99547 => @lem3834269 _99546 _99547 f s)). Qed.
Lemma lem3834271 {_99546 _99547 : Type'} : (@all (_99546 -> _99547 -> _99547)) = (@all (_99546 -> _99547 -> _99547)).
Proof. exact (eq_refl (@all (_99546 -> _99547 -> _99547))). Qed.
Lemma lem3834272 {_99546 _99547 : Type'} (s : _99546 -> Prop) : (term150 _99546 _99547 s) = (term447 _99546 _99547 s).
Proof. exact (MK_COMB (@lem3834271 _99546 _99547) (@lem3834270 _99546 _99547 s)). Qed.
Lemma lem3834491 {A : Type'} (P : Prop) (Q : A -> Prop) : (term448 A P Q) = (term449 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3834492 {_99547 : Type'} (P : Prop) (Q : _99547 -> Prop) : (term448 _99547 P Q) = (term449 _99547 P Q).
Proof. exact (@lem3834491 _99547 P Q). Qed.
Lemma lem3834493 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term450 _99546 _99547 y f x) = (term451 _99546 _99547 y f x).
Proof. exact (@lem3834492 _99547 (term90 _99546 x y) (term412 _99546 _99547 y f x)). Qed.
Lemma lem3834494 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term452 _99546 _99547 y f x s) = (term410 _99546 _99547 y f x s).
Proof. exact (eq_refl (term452 _99546 _99547 y f x s)). Qed.
Lemma lem3834495 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term453 _99546 _99547 y f x) = (term412 _99546 _99547 y f x).
Proof. exact (fun_ext (fun s : _99547 => @lem3834494 _99546 _99547 y f x s)). Qed.
Lemma lem3834496 {_99547 : Type'} : (@ex _99547) = (@ex _99547).
Proof. exact (eq_refl (@ex _99547)). Qed.
Lemma lem3834497 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term454 _99546 _99547 y f x) = (term413 _99546 _99547 y f x).
Proof. exact (MK_COMB (@lem3834496 _99547) (@lem3834495 _99546 _99547 y f x)). Qed.
Lemma lem3834498 {_99546 : Type'} (x : _99546) (y : _99546) : (term414 _99546 x y) = (term414 _99546 x y).
Proof. exact (eq_refl (term414 _99546 x y)). Qed.
Lemma lem3834499 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term450 _99546 _99547 y f x) = (term416 _99546 _99547 y f x).
Proof. exact (MK_COMB (@lem3834498 _99546 x y) (@lem3834497 _99546 _99547 y f x)). Qed.
Lemma lem3834500 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3834501 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term455 _99546 _99547 y f x) = (term456 _99546 _99547 y f x).
Proof. exact (MK_COMB (@lem3834500) (@lem3834499 _99546 _99547 y f x)). Qed.
Lemma lem3834502 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term452 _99546 _99547 y f x s) = (term410 _99546 _99547 y f x s).
Proof. exact (eq_refl (term452 _99546 _99547 y f x s)). Qed.
Lemma lem3834503 {_99546 : Type'} (x : _99546) (y : _99546) : (term414 _99546 x y) = (term414 _99546 x y).
Proof. exact (eq_refl (term414 _99546 x y)). Qed.
Lemma lem3834504 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term457 _99546 _99547 y f x s) = (term458 _99546 _99547 y f x s).
Proof. exact (MK_COMB (@lem3834503 _99546 x y) (@lem3834502 _99546 _99547 y f x s)). Qed.
Lemma lem3834505 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term459 _99546 _99547 y f x) = (term460 _99546 _99547 y f x).
Proof. exact (fun_ext (fun s : _99547 => @lem3834504 _99546 _99547 y f x s)). Qed.
Lemma lem3834506 {_99547 : Type'} : (@ex _99547) = (@ex _99547).
Proof. exact (eq_refl (@ex _99547)). Qed.
Lemma lem3834507 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term451 _99546 _99547 y f x) = (term461 _99546 _99547 y f x).
Proof. exact (MK_COMB (@lem3834506 _99547) (@lem3834505 _99546 _99547 y f x)). Qed.
Lemma lem3834508 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : ((term450 _99546 _99547 y f x) = (term451 _99546 _99547 y f x)) = ((term416 _99546 _99547 y f x) = (term461 _99546 _99547 y f x)).
Proof. exact (MK_COMB (@lem3834501 _99546 _99547 y f x) (@lem3834507 _99546 _99547 y f x)). Qed.
Lemma lem3834509 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term416 _99546 _99547 y f x) = (term461 _99546 _99547 y f x).
Proof. exact (EQ_MP (@lem3834508 _99546 _99547 y f x) (@lem3834493 _99546 _99547 y f x)). Qed.
Lemma lem3834510 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (term422 _99546 _99547 f x) = (term462 _99546 _99547 f x).
Proof. exact (fun_ext (fun y : _99546 => @lem3834509 _99546 _99547 y f x)). Qed.
Lemma lem3834511 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3834512 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (term423 _99546 _99547 f x) = (term463 _99546 _99547 f x).
Proof. exact (MK_COMB (@lem3834511 _99546) (@lem3834510 _99546 _99547 f x)). Qed.
Lemma lem3834513 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term428 _99546 _99547 f) = (term464 _99546 _99547 f).
Proof. exact (fun_ext (fun x : _99546 => @lem3834512 _99546 _99547 f x)). Qed.
Lemma lem3834514 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3834515 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term429 _99546 _99547 f) = (term465 _99546 _99547 f).
Proof. exact (MK_COMB (@lem3834514 _99546) (@lem3834513 _99546 _99547 f)). Qed.
Lemma lem3834516 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3834517 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term431 _99546 _99547 f) = (term466 _99546 _99547 f).
Proof. exact (MK_COMB (@lem3834516) (@lem3834515 _99546 _99547 f)). Qed.
Lemma lem3834519 {A : Type'} (P : Prop) (Q : A -> Prop) : (term448 A P Q) = (term449 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3834520 {_99547 : Type'} (P : Prop) (Q : _99547 -> Prop) : (term448 _99547 P Q) = (term449 _99547 P Q).
Proof. exact (@lem3834519 _99547 P Q). Qed.
Lemma lem3834521 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term450 _99546 _99547 y g x) = (term451 _99546 _99547 y g x).
Proof. exact (@lem3834520 _99547 (term90 _99546 x y) (term412 _99546 _99547 y g x)). Qed.
Lemma lem3834522 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term452 _99546 _99547 y g x s) = (term410 _99546 _99547 y g x s).
Proof. exact (eq_refl (term452 _99546 _99547 y g x s)). Qed.
Lemma lem3834523 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term453 _99546 _99547 y g x) = (term412 _99546 _99547 y g x).
Proof. exact (fun_ext (fun s : _99547 => @lem3834522 _99546 _99547 y g x s)). Qed.
Lemma lem3834524 {_99547 : Type'} : (@ex _99547) = (@ex _99547).
Proof. exact (eq_refl (@ex _99547)). Qed.
Lemma lem3834525 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term454 _99546 _99547 y g x) = (term413 _99546 _99547 y g x).
Proof. exact (MK_COMB (@lem3834524 _99547) (@lem3834523 _99546 _99547 y g x)). Qed.
Lemma lem3834526 {_99546 : Type'} (x : _99546) (y : _99546) : (term414 _99546 x y) = (term414 _99546 x y).
Proof. exact (eq_refl (term414 _99546 x y)). Qed.
Lemma lem3834527 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term450 _99546 _99547 y g x) = (term416 _99546 _99547 y g x).
Proof. exact (MK_COMB (@lem3834526 _99546 x y) (@lem3834525 _99546 _99547 y g x)). Qed.
Lemma lem3834528 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3834529 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term455 _99546 _99547 y g x) = (term456 _99546 _99547 y g x).
Proof. exact (MK_COMB (@lem3834528) (@lem3834527 _99546 _99547 y g x)). Qed.
Lemma lem3834530 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term452 _99546 _99547 y g x s) = (term410 _99546 _99547 y g x s).
Proof. exact (eq_refl (term452 _99546 _99547 y g x s)). Qed.
Lemma lem3834531 {_99546 : Type'} (x : _99546) (y : _99546) : (term414 _99546 x y) = (term414 _99546 x y).
Proof. exact (eq_refl (term414 _99546 x y)). Qed.
Lemma lem3834532 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term457 _99546 _99547 y g x s) = (term458 _99546 _99547 y g x s).
Proof. exact (MK_COMB (@lem3834531 _99546 x y) (@lem3834530 _99546 _99547 y g x s)). Qed.
Lemma lem3834533 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term459 _99546 _99547 y g x) = (term460 _99546 _99547 y g x).
Proof. exact (fun_ext (fun s : _99547 => @lem3834532 _99546 _99547 y g x s)). Qed.
Lemma lem3834534 {_99547 : Type'} : (@ex _99547) = (@ex _99547).
Proof. exact (eq_refl (@ex _99547)). Qed.
Lemma lem3834535 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term451 _99546 _99547 y g x) = (term461 _99546 _99547 y g x).
Proof. exact (MK_COMB (@lem3834534 _99547) (@lem3834533 _99546 _99547 y g x)). Qed.
Lemma lem3834536 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : ((term450 _99546 _99547 y g x) = (term451 _99546 _99547 y g x)) = ((term416 _99546 _99547 y g x) = (term461 _99546 _99547 y g x)).
Proof. exact (MK_COMB (@lem3834529 _99546 _99547 y g x) (@lem3834535 _99546 _99547 y g x)). Qed.
Lemma lem3834537 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term416 _99546 _99547 y g x) = (term461 _99546 _99547 y g x).
Proof. exact (EQ_MP (@lem3834536 _99546 _99547 y g x) (@lem3834521 _99546 _99547 y g x)). Qed.
Lemma lem3834538 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) : (term422 _99546 _99547 g x) = (term462 _99546 _99547 g x).
Proof. exact (fun_ext (fun y : _99546 => @lem3834537 _99546 _99547 y g x)). Qed.
Lemma lem3834539 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3834540 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) : (term423 _99546 _99547 g x) = (term463 _99546 _99547 g x).
Proof. exact (MK_COMB (@lem3834539 _99546) (@lem3834538 _99546 _99547 g x)). Qed.
Lemma lem3834541 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) : (term428 _99546 _99547 g) = (term464 _99546 _99547 g).
Proof. exact (fun_ext (fun x : _99546 => @lem3834540 _99546 _99547 g x)). Qed.
Lemma lem3834542 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3834543 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) : (term429 _99546 _99547 g) = (term465 _99546 _99547 g).
Proof. exact (MK_COMB (@lem3834542 _99546) (@lem3834541 _99546 _99547 g)). Qed.
Lemma lem3834544 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term433 _99546 _99547 f g) = (term467 _99546 _99547 f g).
Proof. exact (MK_COMB (@lem3834517 _99546 _99547 f) (@lem3834543 _99546 _99547 g)). Qed.
Lemma lem3834546 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term468 A P Q) = (term469 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3834547 {_99546 : Type'} (P : _99546 -> Prop) (Q : _99546 -> Prop) : (term468 _99546 P Q) = (term469 _99546 P Q).
Proof. exact (@lem3834546 _99546 P Q). Qed.
Lemma lem3834548 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term470 _99546 _99547 f g) = (term471 _99546 _99547 f g).
Proof. exact (@lem3834547 _99546 (term464 _99546 _99547 f) (term464 _99546 _99547 g)). Qed.
Lemma lem3834549 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (term472 _99546 _99547 f x) = (term463 _99546 _99547 f x).
Proof. exact (eq_refl (term472 _99546 _99547 f x)). Qed.
Lemma lem3834550 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term473 _99546 _99547 f) = (term464 _99546 _99547 f).
Proof. exact (fun_ext (fun x : _99546 => @lem3834549 _99546 _99547 f x)). Qed.
Lemma lem3834551 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3834552 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term474 _99546 _99547 f) = (term465 _99546 _99547 f).
Proof. exact (MK_COMB (@lem3834551 _99546) (@lem3834550 _99546 _99547 f)). Qed.
Lemma lem3834553 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3834554 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term475 _99546 _99547 f) = (term466 _99546 _99547 f).
Proof. exact (MK_COMB (@lem3834553) (@lem3834552 _99546 _99547 f)). Qed.
Lemma lem3834555 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) : (term472 _99546 _99547 g x) = (term463 _99546 _99547 g x).
Proof. exact (eq_refl (term472 _99546 _99547 g x)). Qed.
Lemma lem3834556 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) : (term473 _99546 _99547 g) = (term464 _99546 _99547 g).
Proof. exact (fun_ext (fun x : _99546 => @lem3834555 _99546 _99547 g x)). Qed.
Lemma lem3834557 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3834558 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) : (term474 _99546 _99547 g) = (term465 _99546 _99547 g).
Proof. exact (MK_COMB (@lem3834557 _99546) (@lem3834556 _99546 _99547 g)). Qed.
Lemma lem3834559 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term470 _99546 _99547 f g) = (term467 _99546 _99547 f g).
Proof. exact (MK_COMB (@lem3834554 _99546 _99547 f) (@lem3834558 _99546 _99547 g)). Qed.
Lemma lem3834560 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3834561 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term476 _99546 _99547 f g) = (term477 _99546 _99547 f g).
Proof. exact (MK_COMB (@lem3834560) (@lem3834559 _99546 _99547 f g)). Qed.
Lemma lem3834562 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (term472 _99546 _99547 f x) = (term463 _99546 _99547 f x).
Proof. exact (eq_refl (term472 _99546 _99547 f x)). Qed.
Lemma lem3834563 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3834564 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (term478 _99546 _99547 f x) = (term479 _99546 _99547 f x).
Proof. exact (MK_COMB (@lem3834563) (@lem3834562 _99546 _99547 f x)). Qed.
Lemma lem3834565 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) : (term472 _99546 _99547 g x) = (term463 _99546 _99547 g x).
Proof. exact (eq_refl (term472 _99546 _99547 g x)). Qed.
Lemma lem3834566 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term480 _99546 _99547 f g x) = (term481 _99546 _99547 f g x).
Proof. exact (MK_COMB (@lem3834564 _99546 _99547 f x) (@lem3834565 _99546 _99547 g x)). Qed.
Lemma lem3834567 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term482 _99546 _99547 f g) = (term483 _99546 _99547 f g).
Proof. exact (fun_ext (fun x : _99546 => @lem3834566 _99546 _99547 f g x)). Qed.
Lemma lem3834568 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3834569 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term471 _99546 _99547 f g) = (term484 _99546 _99547 f g).
Proof. exact (MK_COMB (@lem3834568 _99546) (@lem3834567 _99546 _99547 f g)). Qed.
Lemma lem3834570 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : ((term470 _99546 _99547 f g) = (term471 _99546 _99547 f g)) = ((term467 _99546 _99547 f g) = (term484 _99546 _99547 f g)).
Proof. exact (MK_COMB (@lem3834561 _99546 _99547 f g) (@lem3834569 _99546 _99547 f g)). Qed.
Lemma lem3834571 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term467 _99546 _99547 f g) = (term484 _99546 _99547 f g).
Proof. exact (EQ_MP (@lem3834570 _99546 _99547 f g) (@lem3834548 _99546 _99547 f g)). Qed.
Lemma lem3834573 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term468 A P Q) = (term469 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3834574 {_99546 : Type'} (P : _99546 -> Prop) (Q : _99546 -> Prop) : (term468 _99546 P Q) = (term469 _99546 P Q).
Proof. exact (@lem3834573 _99546 P Q). Qed.
Lemma lem3834575 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term485 _99546 _99547 f g x) = (term486 _99546 _99547 f g x).
Proof. exact (@lem3834574 _99546 (term462 _99546 _99547 f x) (term462 _99546 _99547 g x)). Qed.
Lemma lem3834576 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term487 _99546 _99547 f x y) = (term461 _99546 _99547 y f x).
Proof. exact (eq_refl (term487 _99546 _99547 f x y)). Qed.
Lemma lem3834577 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (term488 _99546 _99547 f x) = (term462 _99546 _99547 f x).
Proof. exact (fun_ext (fun y : _99546 => @lem3834576 _99546 _99547 y f x)). Qed.
Lemma lem3834578 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3834579 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (term489 _99546 _99547 f x) = (term463 _99546 _99547 f x).
Proof. exact (MK_COMB (@lem3834578 _99546) (@lem3834577 _99546 _99547 f x)). Qed.
Lemma lem3834580 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3834581 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (term490 _99546 _99547 f x) = (term479 _99546 _99547 f x).
Proof. exact (MK_COMB (@lem3834580) (@lem3834579 _99546 _99547 f x)). Qed.
Lemma lem3834582 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term487 _99546 _99547 g x y) = (term461 _99546 _99547 y g x).
Proof. exact (eq_refl (term487 _99546 _99547 g x y)). Qed.
Lemma lem3834583 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) : (term488 _99546 _99547 g x) = (term462 _99546 _99547 g x).
Proof. exact (fun_ext (fun y : _99546 => @lem3834582 _99546 _99547 y g x)). Qed.
Lemma lem3834584 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3834585 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) : (term489 _99546 _99547 g x) = (term463 _99546 _99547 g x).
Proof. exact (MK_COMB (@lem3834584 _99546) (@lem3834583 _99546 _99547 g x)). Qed.
Lemma lem3834586 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term485 _99546 _99547 f g x) = (term481 _99546 _99547 f g x).
Proof. exact (MK_COMB (@lem3834581 _99546 _99547 f x) (@lem3834585 _99546 _99547 g x)). Qed.
Lemma lem3834587 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3834588 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term491 _99546 _99547 f g x) = (term492 _99546 _99547 f g x).
Proof. exact (MK_COMB (@lem3834587) (@lem3834586 _99546 _99547 f g x)). Qed.
Lemma lem3834589 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term487 _99546 _99547 f x y) = (term461 _99546 _99547 y f x).
Proof. exact (eq_refl (term487 _99546 _99547 f x y)). Qed.
Lemma lem3834590 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3834591 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term493 _99546 _99547 f x y) = (term494 _99546 _99547 y f x).
Proof. exact (MK_COMB (@lem3834590) (@lem3834589 _99546 _99547 y f x)). Qed.
Lemma lem3834592 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term487 _99546 _99547 g x y) = (term461 _99546 _99547 y g x).
Proof. exact (eq_refl (term487 _99546 _99547 g x y)). Qed.
Lemma lem3834593 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term495 _99546 _99547 f g x y) = (term496 _99546 _99547 f y g x).
Proof. exact (MK_COMB (@lem3834591 _99546 _99547 y f x) (@lem3834592 _99546 _99547 y g x)). Qed.
Lemma lem3834594 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term497 _99546 _99547 f g x) = (term498 _99546 _99547 f g x).
Proof. exact (fun_ext (fun y : _99546 => @lem3834593 _99546 _99547 f y g x)). Qed.
Lemma lem3834595 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3834596 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term486 _99546 _99547 f g x) = (term499 _99546 _99547 f g x).
Proof. exact (MK_COMB (@lem3834595 _99546) (@lem3834594 _99546 _99547 f g x)). Qed.
Lemma lem3834597 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : ((term485 _99546 _99547 f g x) = (term486 _99546 _99547 f g x)) = ((term481 _99546 _99547 f g x) = (term499 _99546 _99547 f g x)).
Proof. exact (MK_COMB (@lem3834588 _99546 _99547 f g x) (@lem3834596 _99546 _99547 f g x)). Qed.
Lemma lem3834598 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term481 _99546 _99547 f g x) = (term499 _99546 _99547 f g x).
Proof. exact (EQ_MP (@lem3834597 _99546 _99547 f g x) (@lem3834575 _99546 _99547 f g x)). Qed.
Lemma lem3834600 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term468 A P Q) = (term469 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3834601 {_99547 : Type'} (P : _99547 -> Prop) (Q : _99547 -> Prop) : (term468 _99547 P Q) = (term469 _99547 P Q).
Proof. exact (@lem3834600 _99547 P Q). Qed.
Lemma lem3834602 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term500 _99546 _99547 f y g x) = (term501 _99546 _99547 f y g x).
Proof. exact (@lem3834601 _99547 (term460 _99546 _99547 y f x) (term460 _99546 _99547 y g x)). Qed.
Lemma lem3834603 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term502 _99546 _99547 y f x s) = (term458 _99546 _99547 y f x s).
Proof. exact (eq_refl (term502 _99546 _99547 y f x s)). Qed.
Lemma lem3834604 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term503 _99546 _99547 y f x) = (term460 _99546 _99547 y f x).
Proof. exact (fun_ext (fun s : _99547 => @lem3834603 _99546 _99547 y f x s)). Qed.
Lemma lem3834605 {_99547 : Type'} : (@ex _99547) = (@ex _99547).
Proof. exact (eq_refl (@ex _99547)). Qed.
Lemma lem3834606 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term504 _99546 _99547 y f x) = (term461 _99546 _99547 y f x).
Proof. exact (MK_COMB (@lem3834605 _99547) (@lem3834604 _99546 _99547 y f x)). Qed.
Lemma lem3834607 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3834608 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term505 _99546 _99547 y f x) = (term494 _99546 _99547 y f x).
Proof. exact (MK_COMB (@lem3834607) (@lem3834606 _99546 _99547 y f x)). Qed.
Lemma lem3834609 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term502 _99546 _99547 y g x s) = (term458 _99546 _99547 y g x s).
Proof. exact (eq_refl (term502 _99546 _99547 y g x s)). Qed.
Lemma lem3834610 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term503 _99546 _99547 y g x) = (term460 _99546 _99547 y g x).
Proof. exact (fun_ext (fun s : _99547 => @lem3834609 _99546 _99547 y g x s)). Qed.
Lemma lem3834611 {_99547 : Type'} : (@ex _99547) = (@ex _99547).
Proof. exact (eq_refl (@ex _99547)). Qed.
Lemma lem3834612 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term504 _99546 _99547 y g x) = (term461 _99546 _99547 y g x).
Proof. exact (MK_COMB (@lem3834611 _99547) (@lem3834610 _99546 _99547 y g x)). Qed.
Lemma lem3834613 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term500 _99546 _99547 f y g x) = (term496 _99546 _99547 f y g x).
Proof. exact (MK_COMB (@lem3834608 _99546 _99547 y f x) (@lem3834612 _99546 _99547 y g x)). Qed.
Lemma lem3834614 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3834615 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term506 _99546 _99547 f y g x) = (term507 _99546 _99547 f y g x).
Proof. exact (MK_COMB (@lem3834614) (@lem3834613 _99546 _99547 f y g x)). Qed.
Lemma lem3834616 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term502 _99546 _99547 y f x s) = (term458 _99546 _99547 y f x s).
Proof. exact (eq_refl (term502 _99546 _99547 y f x s)). Qed.
Lemma lem3834617 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3834618 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term508 _99546 _99547 y f x s) = (term509 _99546 _99547 y f x s).
Proof. exact (MK_COMB (@lem3834617) (@lem3834616 _99546 _99547 y f x s)). Qed.
Lemma lem3834619 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term502 _99546 _99547 y g x s) = (term458 _99546 _99547 y g x s).
Proof. exact (eq_refl (term502 _99546 _99547 y g x s)). Qed.
Lemma lem3834620 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term510 _99546 _99547 f y g x s) = (term511 _99546 _99547 f y g x s).
Proof. exact (MK_COMB (@lem3834618 _99546 _99547 y f x s) (@lem3834619 _99546 _99547 y g x s)). Qed.
Lemma lem3834621 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term512 _99546 _99547 f y g x) = (term513 _99546 _99547 f y g x).
Proof. exact (fun_ext (fun s : _99547 => @lem3834620 _99546 _99547 f y g x s)). Qed.
Lemma lem3834622 {_99547 : Type'} : (@ex _99547) = (@ex _99547).
Proof. exact (eq_refl (@ex _99547)). Qed.
Lemma lem3834623 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term501 _99546 _99547 f y g x) = (term514 _99546 _99547 f y g x).
Proof. exact (MK_COMB (@lem3834622 _99547) (@lem3834621 _99546 _99547 f y g x)). Qed.
Lemma lem3834624 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : ((term500 _99546 _99547 f y g x) = (term501 _99546 _99547 f y g x)) = ((term496 _99546 _99547 f y g x) = (term514 _99546 _99547 f y g x)).
Proof. exact (MK_COMB (@lem3834615 _99546 _99547 f y g x) (@lem3834623 _99546 _99547 f y g x)). Qed.
Lemma lem3834625 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term496 _99546 _99547 f y g x) = (term514 _99546 _99547 f y g x).
Proof. exact (EQ_MP (@lem3834624 _99546 _99547 f y g x) (@lem3834602 _99546 _99547 f y g x)). Qed.
Lemma lem3834626 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term498 _99546 _99547 f g x) = (term515 _99546 _99547 f g x).
Proof. exact (fun_ext (fun y : _99546 => @lem3834625 _99546 _99547 f y g x)). Qed.
Lemma lem3834627 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3834628 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term499 _99546 _99547 f g x) = (term516 _99546 _99547 f g x).
Proof. exact (MK_COMB (@lem3834627 _99546) (@lem3834626 _99546 _99547 f g x)). Qed.
Lemma lem3834629 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term481 _99546 _99547 f g x) = (term516 _99546 _99547 f g x).
Proof. exact (TRANS (@lem3834598 _99546 _99547 f g x) (@lem3834628 _99546 _99547 f g x)). Qed.
Lemma lem3834630 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term483 _99546 _99547 f g) = (term517 _99546 _99547 f g).
Proof. exact (fun_ext (fun x : _99546 => @lem3834629 _99546 _99547 f g x)). Qed.
Lemma lem3834631 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3834632 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term484 _99546 _99547 f g) = (term518 _99546 _99547 f g).
Proof. exact (MK_COMB (@lem3834631 _99546) (@lem3834630 _99546 _99547 f g)). Qed.
Lemma lem3834633 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term467 _99546 _99547 f g) = (term518 _99546 _99547 f g).
Proof. exact (TRANS (@lem3834571 _99546 _99547 f g) (@lem3834632 _99546 _99547 f g)). Qed.
Lemma lem3834634 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term433 _99546 _99547 f g) = (term518 _99546 _99547 f g).
Proof. exact (TRANS (@lem3834544 _99546 _99547 f g) (@lem3834633 _99546 _99547 f g)). Qed.
Lemma lem3834635 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term436 _99546 _99547 s f g) = (term436 _99546 _99547 s f g).
Proof. exact (eq_refl (term436 _99546 _99547 s f g)). Qed.
Lemma lem3834636 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term438 _99546 _99547 s f g) = (term519 _99546 _99547 s f g).
Proof. exact (MK_COMB (@lem3834635 _99546 _99547 s f g) (@lem3834634 _99546 _99547 f g)). Qed.
Lemma lem3834638 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term468 A P Q) = (term469 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3834639 {_99546 : Type'} (P : _99546 -> Prop) (Q : _99546 -> Prop) : (term468 _99546 P Q) = (term469 _99546 P Q).
Proof. exact (@lem3834638 _99546 P Q). Qed.
Lemma lem3834640 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term520 _99546 _99547 s f g) = (term521 _99546 _99547 s f g).
Proof. exact (@lem3834639 _99546 (term405 _99546 _99547 s f g) (term517 _99546 _99547 f g)). Qed.
Lemma lem3834641 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term522 _99546 _99547 s f g x) = (term397 _99546 _99547 s f g x).
Proof. exact (eq_refl (term522 _99546 _99547 s f g x)). Qed.
Lemma lem3834642 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term523 _99546 _99547 s f g) = (term405 _99546 _99547 s f g).
Proof. exact (fun_ext (fun x : _99546 => @lem3834641 _99546 _99547 s f g x)). Qed.
Lemma lem3834643 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3834644 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term524 _99546 _99547 s f g) = (term406 _99546 _99547 s f g).
Proof. exact (MK_COMB (@lem3834643 _99546) (@lem3834642 _99546 _99547 s f g)). Qed.
Lemma lem3834645 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3834646 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term525 _99546 _99547 s f g) = (term436 _99546 _99547 s f g).
Proof. exact (MK_COMB (@lem3834645) (@lem3834644 _99546 _99547 s f g)). Qed.
Lemma lem3834647 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term526 _99546 _99547 f g x) = (term516 _99546 _99547 f g x).
Proof. exact (eq_refl (term526 _99546 _99547 f g x)). Qed.
Lemma lem3834648 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term527 _99546 _99547 f g) = (term517 _99546 _99547 f g).
Proof. exact (fun_ext (fun x : _99546 => @lem3834647 _99546 _99547 f g x)). Qed.
Lemma lem3834649 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3834650 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term528 _99546 _99547 f g) = (term518 _99546 _99547 f g).
Proof. exact (MK_COMB (@lem3834649 _99546) (@lem3834648 _99546 _99547 f g)). Qed.
Lemma lem3834651 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term520 _99546 _99547 s f g) = (term519 _99546 _99547 s f g).
Proof. exact (MK_COMB (@lem3834646 _99546 _99547 s f g) (@lem3834650 _99546 _99547 f g)). Qed.
Lemma lem3834652 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3834653 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term529 _99546 _99547 s f g) = (term530 _99546 _99547 s f g).
Proof. exact (MK_COMB (@lem3834652) (@lem3834651 _99546 _99547 s f g)). Qed.
Lemma lem3834654 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term522 _99546 _99547 s f g x) = (term397 _99546 _99547 s f g x).
Proof. exact (eq_refl (term522 _99546 _99547 s f g x)). Qed.
Lemma lem3834655 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3834656 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term531 _99546 _99547 s f g x) = (term532 _99546 _99547 s f g x).
Proof. exact (MK_COMB (@lem3834655) (@lem3834654 _99546 _99547 s f g x)). Qed.
Lemma lem3834657 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term526 _99546 _99547 f g x) = (term516 _99546 _99547 f g x).
Proof. exact (eq_refl (term526 _99546 _99547 f g x)). Qed.
Lemma lem3834658 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term533 _99546 _99547 s f g x) = (term534 _99546 _99547 s f g x).
Proof. exact (MK_COMB (@lem3834656 _99546 _99547 s f g x) (@lem3834657 _99546 _99547 f g x)). Qed.
Lemma lem3834659 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term535 _99546 _99547 s f g) = (term536 _99546 _99547 s f g).
Proof. exact (fun_ext (fun x : _99546 => @lem3834658 _99546 _99547 s f g x)). Qed.
Lemma lem3834660 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3834661 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term521 _99546 _99547 s f g) = (term537 _99546 _99547 s f g).
Proof. exact (MK_COMB (@lem3834660 _99546) (@lem3834659 _99546 _99547 s f g)). Qed.
Lemma lem3834662 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : ((term520 _99546 _99547 s f g) = (term521 _99546 _99547 s f g)) = ((term519 _99546 _99547 s f g) = (term537 _99546 _99547 s f g)).
Proof. exact (MK_COMB (@lem3834653 _99546 _99547 s f g) (@lem3834661 _99546 _99547 s f g)). Qed.
Lemma lem3834663 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term519 _99546 _99547 s f g) = (term537 _99546 _99547 s f g).
Proof. exact (EQ_MP (@lem3834662 _99546 _99547 s f g) (@lem3834640 _99546 _99547 s f g)). Qed.
Lemma lem3834665 {A : Type'} (P : Prop) (Q : A -> Prop) : (term538 A P Q) = (term539 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3834666 {_99546 : Type'} (P : Prop) (Q : _99546 -> Prop) : (term538 _99546 P Q) = (term539 _99546 P Q).
Proof. exact (@lem3834665 _99546 P Q). Qed.
Lemma lem3834667 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term540 _99546 _99547 s f g x) = (term541 _99546 _99547 s f g x).
Proof. exact (@lem3834666 _99546 (term397 _99546 _99547 s f g x) (term515 _99546 _99547 f g x)). Qed.
Lemma lem3834668 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term542 _99546 _99547 f g x y) = (term514 _99546 _99547 f y g x).
Proof. exact (eq_refl (term542 _99546 _99547 f g x y)). Qed.
Lemma lem3834669 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term543 _99546 _99547 f g x) = (term515 _99546 _99547 f g x).
Proof. exact (fun_ext (fun y : _99546 => @lem3834668 _99546 _99547 f y g x)). Qed.
Lemma lem3834670 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3834671 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term544 _99546 _99547 f g x) = (term516 _99546 _99547 f g x).
Proof. exact (MK_COMB (@lem3834670 _99546) (@lem3834669 _99546 _99547 f g x)). Qed.
Lemma lem3834672 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term532 _99546 _99547 s f g x) = (term532 _99546 _99547 s f g x).
Proof. exact (eq_refl (term532 _99546 _99547 s f g x)). Qed.
Lemma lem3834673 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term540 _99546 _99547 s f g x) = (term534 _99546 _99547 s f g x).
Proof. exact (MK_COMB (@lem3834672 _99546 _99547 s f g x) (@lem3834671 _99546 _99547 f g x)). Qed.
Lemma lem3834674 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3834675 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term545 _99546 _99547 s f g x) = (term546 _99546 _99547 s f g x).
Proof. exact (MK_COMB (@lem3834674) (@lem3834673 _99546 _99547 s f g x)). Qed.
Lemma lem3834676 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term542 _99546 _99547 f g x y) = (term514 _99546 _99547 f y g x).
Proof. exact (eq_refl (term542 _99546 _99547 f g x y)). Qed.
Lemma lem3834677 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term532 _99546 _99547 s f g x) = (term532 _99546 _99547 s f g x).
Proof. exact (eq_refl (term532 _99546 _99547 s f g x)). Qed.
Lemma lem3834678 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term547 _99546 _99547 s f g x y) = (term548 _99546 _99547 s f y g x).
Proof. exact (MK_COMB (@lem3834677 _99546 _99547 s f g x) (@lem3834676 _99546 _99547 f y g x)). Qed.
Lemma lem3834679 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term549 _99546 _99547 s f g x) = (term550 _99546 _99547 s f g x).
Proof. exact (fun_ext (fun y : _99546 => @lem3834678 _99546 _99547 s f y g x)). Qed.
Lemma lem3834680 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3834681 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term541 _99546 _99547 s f g x) = (term551 _99546 _99547 s f g x).
Proof. exact (MK_COMB (@lem3834680 _99546) (@lem3834679 _99546 _99547 s f g x)). Qed.
Lemma lem3834682 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : ((term540 _99546 _99547 s f g x) = (term541 _99546 _99547 s f g x)) = ((term534 _99546 _99547 s f g x) = (term551 _99546 _99547 s f g x)).
Proof. exact (MK_COMB (@lem3834675 _99546 _99547 s f g x) (@lem3834681 _99546 _99547 s f g x)). Qed.
Lemma lem3834683 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term534 _99546 _99547 s f g x) = (term551 _99546 _99547 s f g x).
Proof. exact (EQ_MP (@lem3834682 _99546 _99547 s f g x) (@lem3834667 _99546 _99547 s f g x)). Qed.
Lemma lem3834685 {A : Type'} (P : Prop) (Q : A -> Prop) : (term538 A P Q) = (term539 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3834686 {_99547 : Type'} (P : Prop) (Q : _99547 -> Prop) : (term538 _99547 P Q) = (term539 _99547 P Q).
Proof. exact (@lem3834685 _99547 P Q). Qed.
Lemma lem3834687 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term552 _99546 _99547 s f y g x) = (term553 _99546 _99547 s f y g x).
Proof. exact (@lem3834686 _99547 (term397 _99546 _99547 s f g x) (term513 _99546 _99547 f y g x)). Qed.
Lemma lem3834688 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term554 _99546 _99547 f y g x s) = (term511 _99546 _99547 f y g x s).
Proof. exact (eq_refl (term554 _99546 _99547 f y g x s)). Qed.
Lemma lem3834689 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term555 _99546 _99547 f y g x) = (term513 _99546 _99547 f y g x).
Proof. exact (fun_ext (fun s : _99547 => @lem3834688 _99546 _99547 f y g x s)). Qed.
Lemma lem3834690 {_99547 : Type'} : (@ex _99547) = (@ex _99547).
Proof. exact (eq_refl (@ex _99547)). Qed.
Lemma lem3834691 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term556 _99546 _99547 f y g x) = (term514 _99546 _99547 f y g x).
Proof. exact (MK_COMB (@lem3834690 _99547) (@lem3834689 _99546 _99547 f y g x)). Qed.
Lemma lem3834692 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term532 _99546 _99547 s f g x) = (term532 _99546 _99547 s f g x).
Proof. exact (eq_refl (term532 _99546 _99547 s f g x)). Qed.
Lemma lem3834693 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term552 _99546 _99547 s f y g x) = (term548 _99546 _99547 s f y g x).
Proof. exact (MK_COMB (@lem3834692 _99546 _99547 s f g x) (@lem3834691 _99546 _99547 f y g x)). Qed.
Lemma lem3834694 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3834695 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term557 _99546 _99547 s f y g x) = (term558 _99546 _99547 s f y g x).
Proof. exact (MK_COMB (@lem3834694) (@lem3834693 _99546 _99547 s f y g x)). Qed.
Lemma lem3834696 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term554 _99546 _99547 f y g x s) = (term511 _99546 _99547 f y g x s).
Proof. exact (eq_refl (term554 _99546 _99547 f y g x s)). Qed.
Lemma lem3834697 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term532 _99546 _99547 s f g x) = (term532 _99546 _99547 s f g x).
Proof. exact (eq_refl (term532 _99546 _99547 s f g x)). Qed.
Lemma lem3834698 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s' : _99547) : (term559 _99546 _99547 s f y g x s') = (term560 _99546 _99547 s f y g x s').
Proof. exact (MK_COMB (@lem3834697 _99546 _99547 s f g x) (@lem3834696 _99546 _99547 f y g x s')). Qed.
Lemma lem3834699 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term561 _99546 _99547 s f y g x) = (term562 _99546 _99547 s f y g x).
Proof. exact (fun_ext (fun s' : _99547 => @lem3834698 _99546 _99547 s f y g x s')). Qed.
Lemma lem3834700 {_99547 : Type'} : (@ex _99547) = (@ex _99547).
Proof. exact (eq_refl (@ex _99547)). Qed.
Lemma lem3834701 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term553 _99546 _99547 s f y g x) = (term563 _99546 _99547 s f y g x).
Proof. exact (MK_COMB (@lem3834700 _99547) (@lem3834699 _99546 _99547 s f y g x)). Qed.
Lemma lem3834702 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : ((term552 _99546 _99547 s f y g x) = (term553 _99546 _99547 s f y g x)) = ((term548 _99546 _99547 s f y g x) = (term563 _99546 _99547 s f y g x)).
Proof. exact (MK_COMB (@lem3834695 _99546 _99547 s f y g x) (@lem3834701 _99546 _99547 s f y g x)). Qed.
Lemma lem3834703 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term548 _99546 _99547 s f y g x) = (term563 _99546 _99547 s f y g x).
Proof. exact (EQ_MP (@lem3834702 _99546 _99547 s f y g x) (@lem3834687 _99546 _99547 s f y g x)). Qed.
Lemma lem3834704 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term550 _99546 _99547 s f g x) = (term564 _99546 _99547 s f g x).
Proof. exact (fun_ext (fun y : _99546 => @lem3834703 _99546 _99547 s f y g x)). Qed.
Lemma lem3834705 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3834706 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term551 _99546 _99547 s f g x) = (term565 _99546 _99547 s f g x).
Proof. exact (MK_COMB (@lem3834705 _99546) (@lem3834704 _99546 _99547 s f g x)). Qed.
Lemma lem3834707 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term534 _99546 _99547 s f g x) = (term565 _99546 _99547 s f g x).
Proof. exact (TRANS (@lem3834683 _99546 _99547 s f g x) (@lem3834706 _99546 _99547 s f g x)). Qed.
Lemma lem3834708 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term536 _99546 _99547 s f g) = (term566 _99546 _99547 s f g).
Proof. exact (fun_ext (fun x : _99546 => @lem3834707 _99546 _99547 s f g x)). Qed.
Lemma lem3834709 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3834710 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term537 _99546 _99547 s f g) = (term567 _99546 _99547 s f g).
Proof. exact (MK_COMB (@lem3834709 _99546) (@lem3834708 _99546 _99547 s f g)). Qed.
Lemma lem3834711 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term519 _99546 _99547 s f g) = (term567 _99546 _99547 s f g).
Proof. exact (TRANS (@lem3834663 _99546 _99547 s f g) (@lem3834710 _99546 _99547 s f g)). Qed.
Lemma lem3834712 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term438 _99546 _99547 s f g) = (term567 _99546 _99547 s f g).
Proof. exact (TRANS (@lem3834636 _99546 _99547 s f g) (@lem3834711 _99546 _99547 s f g)). Qed.
Lemma lem3834713 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3834714 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term441 _99546 _99547 s f g) = (term568 _99546 _99547 s f g).
Proof. exact (MK_COMB (@lem3834713) (@lem3834712 _99546 _99547 s f g)). Qed.
Lemma lem3834715 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term86 _99546 _99547 f g s) = (term86 _99546 _99547 f g s).
Proof. exact (eq_refl (term86 _99546 _99547 f g s)). Qed.
Lemma lem3834716 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term443 _99546 _99547 f g s) = (term569 _99546 _99547 f g s).
Proof. exact (MK_COMB (@lem3834714 _99546 _99547 s f g) (@lem3834715 _99546 _99547 f g s)). Qed.
Lemma lem3834718 {A : Type'} (P : A -> Prop) (Q : Prop) : (term570 A P Q) = (term571 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3834719 {_99546 : Type'} (P : _99546 -> Prop) (Q : Prop) : (term570 _99546 P Q) = (term571 _99546 P Q).
Proof. exact (@lem3834718 _99546 P Q). Qed.
Lemma lem3834720 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term572 _99546 _99547 f g s) = (term573 _99546 _99547 f g s).
Proof. exact (@lem3834719 _99546 (term566 _99546 _99547 s f g) (term86 _99546 _99547 f g s)). Qed.
Lemma lem3834721 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term574 _99546 _99547 s f g x) = (term565 _99546 _99547 s f g x).
Proof. exact (eq_refl (term574 _99546 _99547 s f g x)). Qed.
Lemma lem3834722 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term575 _99546 _99547 s f g) = (term566 _99546 _99547 s f g).
Proof. exact (fun_ext (fun x : _99546 => @lem3834721 _99546 _99547 s f g x)). Qed.
Lemma lem3834723 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3834724 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term576 _99546 _99547 s f g) = (term567 _99546 _99547 s f g).
Proof. exact (MK_COMB (@lem3834723 _99546) (@lem3834722 _99546 _99547 s f g)). Qed.
Lemma lem3834725 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3834726 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term577 _99546 _99547 s f g) = (term568 _99546 _99547 s f g).
Proof. exact (MK_COMB (@lem3834725) (@lem3834724 _99546 _99547 s f g)). Qed.
Lemma lem3834727 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term86 _99546 _99547 f g s) = (term86 _99546 _99547 f g s).
Proof. exact (eq_refl (term86 _99546 _99547 f g s)). Qed.
Lemma lem3834728 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term572 _99546 _99547 f g s) = (term569 _99546 _99547 f g s).
Proof. exact (MK_COMB (@lem3834726 _99546 _99547 s f g) (@lem3834727 _99546 _99547 f g s)). Qed.
Lemma lem3834729 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3834730 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term578 _99546 _99547 f g s) = (term579 _99546 _99547 f g s).
Proof. exact (MK_COMB (@lem3834729) (@lem3834728 _99546 _99547 f g s)). Qed.
Lemma lem3834731 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term574 _99546 _99547 s f g x) = (term565 _99546 _99547 s f g x).
Proof. exact (eq_refl (term574 _99546 _99547 s f g x)). Qed.
Lemma lem3834732 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3834733 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term580 _99546 _99547 s f g x) = (term581 _99546 _99547 s f g x).
Proof. exact (MK_COMB (@lem3834732) (@lem3834731 _99546 _99547 s f g x)). Qed.
Lemma lem3834734 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term86 _99546 _99547 f g s) = (term86 _99546 _99547 f g s).
Proof. exact (eq_refl (term86 _99546 _99547 f g s)). Qed.
Lemma lem3834735 {_99546 _99547 : Type'} (x : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term582 _99546 _99547 x f g s) = (term583 _99546 _99547 x f g s).
Proof. exact (MK_COMB (@lem3834733 _99546 _99547 s f g x) (@lem3834734 _99546 _99547 f g s)). Qed.
Lemma lem3834736 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term584 _99546 _99547 f g s) = (term585 _99546 _99547 f g s).
Proof. exact (fun_ext (fun x : _99546 => @lem3834735 _99546 _99547 x f g s)). Qed.
Lemma lem3834737 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3834738 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term573 _99546 _99547 f g s) = (term586 _99546 _99547 f g s).
Proof. exact (MK_COMB (@lem3834737 _99546) (@lem3834736 _99546 _99547 f g s)). Qed.
Lemma lem3834739 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : ((term572 _99546 _99547 f g s) = (term573 _99546 _99547 f g s)) = ((term569 _99546 _99547 f g s) = (term586 _99546 _99547 f g s)).
Proof. exact (MK_COMB (@lem3834730 _99546 _99547 f g s) (@lem3834738 _99546 _99547 f g s)). Qed.
Lemma lem3834740 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term569 _99546 _99547 f g s) = (term586 _99546 _99547 f g s).
Proof. exact (EQ_MP (@lem3834739 _99546 _99547 f g s) (@lem3834720 _99546 _99547 f g s)). Qed.
Lemma lem3834742 {A : Type'} (P : A -> Prop) (Q : Prop) : (term570 A P Q) = (term571 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3834743 {_99546 : Type'} (P : _99546 -> Prop) (Q : Prop) : (term570 _99546 P Q) = (term571 _99546 P Q).
Proof. exact (@lem3834742 _99546 P Q). Qed.
Lemma lem3834744 {_99546 _99547 : Type'} (x : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term587 _99546 _99547 x f g s) = (term588 _99546 _99547 x f g s).
Proof. exact (@lem3834743 _99546 (term564 _99546 _99547 s f g x) (term86 _99546 _99547 f g s)). Qed.
Lemma lem3834745 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term589 _99546 _99547 s f g x y) = (term563 _99546 _99547 s f y g x).
Proof. exact (eq_refl (term589 _99546 _99547 s f g x y)). Qed.
Lemma lem3834746 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term590 _99546 _99547 s f g x) = (term564 _99546 _99547 s f g x).
Proof. exact (fun_ext (fun y : _99546 => @lem3834745 _99546 _99547 s f y g x)). Qed.
Lemma lem3834747 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3834748 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term591 _99546 _99547 s f g x) = (term565 _99546 _99547 s f g x).
Proof. exact (MK_COMB (@lem3834747 _99546) (@lem3834746 _99546 _99547 s f g x)). Qed.
Lemma lem3834749 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3834750 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term592 _99546 _99547 s f g x) = (term581 _99546 _99547 s f g x).
Proof. exact (MK_COMB (@lem3834749) (@lem3834748 _99546 _99547 s f g x)). Qed.
Lemma lem3834751 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term86 _99546 _99547 f g s) = (term86 _99546 _99547 f g s).
Proof. exact (eq_refl (term86 _99546 _99547 f g s)). Qed.
Lemma lem3834752 {_99546 _99547 : Type'} (x : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term587 _99546 _99547 x f g s) = (term583 _99546 _99547 x f g s).
Proof. exact (MK_COMB (@lem3834750 _99546 _99547 s f g x) (@lem3834751 _99546 _99547 f g s)). Qed.
Lemma lem3834753 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3834754 {_99546 _99547 : Type'} (x : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term593 _99546 _99547 x f g s) = (term594 _99546 _99547 x f g s).
Proof. exact (MK_COMB (@lem3834753) (@lem3834752 _99546 _99547 x f g s)). Qed.
Lemma lem3834755 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term589 _99546 _99547 s f g x y) = (term563 _99546 _99547 s f y g x).
Proof. exact (eq_refl (term589 _99546 _99547 s f g x y)). Qed.
Lemma lem3834756 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3834757 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term595 _99546 _99547 s f g x y) = (term596 _99546 _99547 s f y g x).
Proof. exact (MK_COMB (@lem3834756) (@lem3834755 _99546 _99547 s f y g x)). Qed.
Lemma lem3834758 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term86 _99546 _99547 f g s) = (term86 _99546 _99547 f g s).
Proof. exact (eq_refl (term86 _99546 _99547 f g s)). Qed.
Lemma lem3834759 {_99546 _99547 : Type'} (y : _99546) (x : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term597 _99546 _99547 x y f g s) = (term598 _99546 _99547 y x f g s).
Proof. exact (MK_COMB (@lem3834757 _99546 _99547 s f y g x) (@lem3834758 _99546 _99547 f g s)). Qed.
Lemma lem3834760 {_99546 _99547 : Type'} (x : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term599 _99546 _99547 x f g s) = (term600 _99546 _99547 x f g s).
Proof. exact (fun_ext (fun y : _99546 => @lem3834759 _99546 _99547 y x f g s)). Qed.
Lemma lem3834761 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3834762 {_99546 _99547 : Type'} (x : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term588 _99546 _99547 x f g s) = (term601 _99546 _99547 x f g s).
Proof. exact (MK_COMB (@lem3834761 _99546) (@lem3834760 _99546 _99547 x f g s)). Qed.
Lemma lem3834763 {_99546 _99547 : Type'} (x : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : ((term587 _99546 _99547 x f g s) = (term588 _99546 _99547 x f g s)) = ((term583 _99546 _99547 x f g s) = (term601 _99546 _99547 x f g s)).
Proof. exact (MK_COMB (@lem3834754 _99546 _99547 x f g s) (@lem3834762 _99546 _99547 x f g s)). Qed.
Lemma lem3834764 {_99546 _99547 : Type'} (x : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term583 _99546 _99547 x f g s) = (term601 _99546 _99547 x f g s).
Proof. exact (EQ_MP (@lem3834763 _99546 _99547 x f g s) (@lem3834744 _99546 _99547 x f g s)). Qed.
Lemma lem3834766 {A : Type'} (P : A -> Prop) (Q : Prop) : (term570 A P Q) = (term571 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3834767 {_99547 : Type'} (P : _99547 -> Prop) (Q : Prop) : (term570 _99547 P Q) = (term571 _99547 P Q).
Proof. exact (@lem3834766 _99547 P Q). Qed.
Lemma lem3834768 {_99546 _99547 : Type'} (y : _99546) (x : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term602 _99546 _99547 y x f g s) = (term603 _99546 _99547 y x f g s).
Proof. exact (@lem3834767 _99547 (term562 _99546 _99547 s f y g x) (term86 _99546 _99547 f g s)). Qed.
Lemma lem3834769 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s' : _99547) : (term604 _99546 _99547 s f y g x s') = (term560 _99546 _99547 s f y g x s').
Proof. exact (eq_refl (term604 _99546 _99547 s f y g x s')). Qed.
Lemma lem3834770 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term605 _99546 _99547 s f y g x) = (term562 _99546 _99547 s f y g x).
Proof. exact (fun_ext (fun s' : _99547 => @lem3834769 _99546 _99547 s f y g x s')). Qed.
Lemma lem3834771 {_99547 : Type'} : (@ex _99547) = (@ex _99547).
Proof. exact (eq_refl (@ex _99547)). Qed.
Lemma lem3834772 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term606 _99546 _99547 s f y g x) = (term563 _99546 _99547 s f y g x).
Proof. exact (MK_COMB (@lem3834771 _99547) (@lem3834770 _99546 _99547 s f y g x)). Qed.
Lemma lem3834773 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3834774 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term607 _99546 _99547 s f y g x) = (term596 _99546 _99547 s f y g x).
Proof. exact (MK_COMB (@lem3834773) (@lem3834772 _99546 _99547 s f y g x)). Qed.
Lemma lem3834775 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term86 _99546 _99547 f g s) = (term86 _99546 _99547 f g s).
Proof. exact (eq_refl (term86 _99546 _99547 f g s)). Qed.
Lemma lem3834776 {_99546 _99547 : Type'} (y : _99546) (x : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term602 _99546 _99547 y x f g s) = (term598 _99546 _99547 y x f g s).
Proof. exact (MK_COMB (@lem3834774 _99546 _99547 s f y g x) (@lem3834775 _99546 _99547 f g s)). Qed.
Lemma lem3834777 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3834778 {_99546 _99547 : Type'} (y : _99546) (x : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term608 _99546 _99547 y x f g s) = (term609 _99546 _99547 y x f g s).
Proof. exact (MK_COMB (@lem3834777) (@lem3834776 _99546 _99547 y x f g s)). Qed.
Lemma lem3834779 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s' : _99547) : (term604 _99546 _99547 s f y g x s') = (term560 _99546 _99547 s f y g x s').
Proof. exact (eq_refl (term604 _99546 _99547 s f y g x s')). Qed.
Lemma lem3834780 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3834781 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s' : _99547) : (term610 _99546 _99547 s f y g x s') = (term611 _99546 _99547 s f y g x s').
Proof. exact (MK_COMB (@lem3834780) (@lem3834779 _99546 _99547 s f y g x s')). Qed.
Lemma lem3834782 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term86 _99546 _99547 f g s) = (term86 _99546 _99547 f g s).
Proof. exact (eq_refl (term86 _99546 _99547 f g s)). Qed.
Lemma lem3834783 {_99546 _99547 : Type'} (y : _99546) (x : _99546) (s : _99547) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s' : _99546 -> Prop) : (term612 _99546 _99547 y x s f g s') = (term613 _99546 _99547 y x s f g s').
Proof. exact (MK_COMB (@lem3834781 _99546 _99547 s' f y g x s) (@lem3834782 _99546 _99547 f g s')). Qed.
Lemma lem3834784 {_99546 _99547 : Type'} (y : _99546) (x : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term614 _99546 _99547 y x f g s) = (term615 _99546 _99547 y x f g s).
Proof. exact (fun_ext (fun s' : _99547 => @lem3834783 _99546 _99547 y x s' f g s)). Qed.
Lemma lem3834785 {_99547 : Type'} : (@ex _99547) = (@ex _99547).
Proof. exact (eq_refl (@ex _99547)). Qed.
Lemma lem3834786 {_99546 _99547 : Type'} (y : _99546) (x : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term603 _99546 _99547 y x f g s) = (term616 _99546 _99547 y x f g s).
Proof. exact (MK_COMB (@lem3834785 _99547) (@lem3834784 _99546 _99547 y x f g s)). Qed.
Lemma lem3834787 {_99546 _99547 : Type'} (y : _99546) (x : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : ((term602 _99546 _99547 y x f g s) = (term603 _99546 _99547 y x f g s)) = ((term598 _99546 _99547 y x f g s) = (term616 _99546 _99547 y x f g s)).
Proof. exact (MK_COMB (@lem3834778 _99546 _99547 y x f g s) (@lem3834786 _99546 _99547 y x f g s)). Qed.
Lemma lem3834788 {_99546 _99547 : Type'} (y : _99546) (x : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term598 _99546 _99547 y x f g s) = (term616 _99546 _99547 y x f g s).
Proof. exact (EQ_MP (@lem3834787 _99546 _99547 y x f g s) (@lem3834768 _99546 _99547 y x f g s)). Qed.
Lemma lem3834789 {_99546 _99547 : Type'} (x : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term600 _99546 _99547 x f g s) = (term617 _99546 _99547 x f g s).
Proof. exact (fun_ext (fun y : _99546 => @lem3834788 _99546 _99547 y x f g s)). Qed.
Lemma lem3834790 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3834791 {_99546 _99547 : Type'} (x : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term601 _99546 _99547 x f g s) = (term618 _99546 _99547 x f g s).
Proof. exact (MK_COMB (@lem3834790 _99546) (@lem3834789 _99546 _99547 x f g s)). Qed.
Lemma lem3834792 {_99546 _99547 : Type'} (x : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term583 _99546 _99547 x f g s) = (term618 _99546 _99547 x f g s).
Proof. exact (TRANS (@lem3834764 _99546 _99547 x f g s) (@lem3834791 _99546 _99547 x f g s)). Qed.
Lemma lem3834793 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term585 _99546 _99547 f g s) = (term619 _99546 _99547 f g s).
Proof. exact (fun_ext (fun x : _99546 => @lem3834792 _99546 _99547 x f g s)). Qed.
Lemma lem3834794 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3834795 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term586 _99546 _99547 f g s) = (term620 _99546 _99547 f g s).
Proof. exact (MK_COMB (@lem3834794 _99546) (@lem3834793 _99546 _99547 f g s)). Qed.
Lemma lem3834796 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term569 _99546 _99547 f g s) = (term620 _99546 _99547 f g s).
Proof. exact (TRANS (@lem3834740 _99546 _99547 f g s) (@lem3834795 _99546 _99547 f g s)). Qed.
Lemma lem3834797 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term443 _99546 _99547 f g s) = (term620 _99546 _99547 f g s).
Proof. exact (TRANS (@lem3834716 _99546 _99547 f g s) (@lem3834796 _99546 _99547 f g s)). Qed.
Lemma lem3834798 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term444 _99546 _99547 f s) = (term621 _99546 _99547 f s).
Proof. exact (fun_ext (fun g : type1411 _99546 _99547 => @lem3834797 _99546 _99547 f g s)). Qed.
Lemma lem3834799 {_99546 _99547 : Type'} : (@all (_99546 -> _99547 -> _99547)) = (@all (_99546 -> _99547 -> _99547)).
Proof. exact (eq_refl (@all (_99546 -> _99547 -> _99547))). Qed.
Lemma lem3834800 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term445 _99546 _99547 f s) = (term622 _99546 _99547 f s).
Proof. exact (MK_COMB (@lem3834799 _99546 _99547) (@lem3834798 _99546 _99547 f s)). Qed.
Lemma lem3834802 {A B : Type'} (P : type1413 A B) : (term623 A B P) = (term624 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3834803 {_99546 _99547 : Type'} (P : type430 _99546 _99547) : (term625 _99546 _99547 P) = (term626 _99546 _99547 P).
Proof. exact (@lem3834802 (type1411 _99546 _99547) _99546 P). Qed.
Lemma lem3834804 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term627 _99546 _99547 f s) = (term628 _99546 _99547 f s).
Proof. exact (@lem3834803 _99546 _99547 (term629 _99546 _99547 f s)). Qed.
Lemma lem3834805 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term630 _99546 _99547 f s g) = (term619 _99546 _99547 f g s).
Proof. exact (eq_refl (term630 _99546 _99547 f s g)). Qed.
Lemma lem3834806 {_99546 : Type'} (x : _99546) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3834807 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) (x : _99546) : (term631 _99546 _99547 f s g x) = (term632 _99546 _99547 f g s x).
Proof. exact (MK_COMB (@lem3834805 _99546 _99547 f g s) (@lem3834806 _99546 x)). Qed.
Lemma lem3834808 {_99546 _99547 : Type'} (x : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term632 _99546 _99547 f g s x) = (term618 _99546 _99547 x f g s).
Proof. exact (eq_refl (term632 _99546 _99547 f g s x)). Qed.
Lemma lem3834809 {_99546 _99547 : Type'} (x : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term631 _99546 _99547 f s g x) = (term618 _99546 _99547 x f g s).
Proof. exact (TRANS (@lem3834807 _99546 _99547 f g s x) (@lem3834808 _99546 _99547 x f g s)). Qed.
Lemma lem3834810 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term633 _99546 _99547 f s g) = (term619 _99546 _99547 f g s).
Proof. exact (fun_ext (fun x : _99546 => @lem3834809 _99546 _99547 x f g s)). Qed.
Lemma lem3834811 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3834812 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term634 _99546 _99547 f s g) = (term620 _99546 _99547 f g s).
Proof. exact (MK_COMB (@lem3834811 _99546) (@lem3834810 _99546 _99547 f g s)). Qed.
Lemma lem3834813 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term635 _99546 _99547 f s) = (term621 _99546 _99547 f s).
Proof. exact (fun_ext (fun g : type1411 _99546 _99547 => @lem3834812 _99546 _99547 f g s)). Qed.
Lemma lem3834814 {_99546 _99547 : Type'} : (@all (_99546 -> _99547 -> _99547)) = (@all (_99546 -> _99547 -> _99547)).
Proof. exact (eq_refl (@all (_99546 -> _99547 -> _99547))). Qed.
Lemma lem3834815 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term627 _99546 _99547 f s) = (term622 _99546 _99547 f s).
Proof. exact (MK_COMB (@lem3834814 _99546 _99547) (@lem3834813 _99546 _99547 f s)). Qed.
Lemma lem3834816 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3834817 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term636 _99546 _99547 f s) = (term637 _99546 _99547 f s).
Proof. exact (MK_COMB (@lem3834816) (@lem3834815 _99546 _99547 f s)). Qed.
Lemma lem3834818 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term630 _99546 _99547 f s g) = (term619 _99546 _99547 f g s).
Proof. exact (eq_refl (term630 _99546 _99547 f s g)). Qed.
Lemma lem3834819 {_99546 _99547 : Type'} (x : type434 _99546 _99547) (g : type1411 _99546 _99547) : (x g) = (x g).
Proof. exact (eq_refl (x g)). Qed.
Lemma lem3834820 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) (x : type434 _99546 _99547) (g : type1411 _99546 _99547) : (term638 _99546 _99547 f s x g) = (term639 _99546 _99547 f s x g).
Proof. exact (MK_COMB (@lem3834818 _99546 _99547 f g s) (@lem3834819 _99546 _99547 x g)). Qed.
Lemma lem3834821 {_99546 _99547 : Type'} (x : type434 _99546 _99547) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term639 _99546 _99547 f s x g) = (term640 _99546 _99547 x f g s).
Proof. exact (eq_refl (term639 _99546 _99547 f s x g)). Qed.
Lemma lem3834822 {_99546 _99547 : Type'} (x : type434 _99546 _99547) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term638 _99546 _99547 f s x g) = (term640 _99546 _99547 x f g s).
Proof. exact (TRANS (@lem3834820 _99546 _99547 f s x g) (@lem3834821 _99546 _99547 x f g s)). Qed.
Lemma lem3834823 {_99546 _99547 : Type'} (x : type434 _99546 _99547) (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term641 _99546 _99547 f s x) = (term642 _99546 _99547 x f s).
Proof. exact (fun_ext (fun g : type1411 _99546 _99547 => @lem3834822 _99546 _99547 x f g s)). Qed.
Lemma lem3834824 {_99546 _99547 : Type'} : (@all (_99546 -> _99547 -> _99547)) = (@all (_99546 -> _99547 -> _99547)).
Proof. exact (eq_refl (@all (_99546 -> _99547 -> _99547))). Qed.
Lemma lem3834825 {_99546 _99547 : Type'} (x : type434 _99546 _99547) (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term643 _99546 _99547 f s x) = (term644 _99546 _99547 x f s).
Proof. exact (MK_COMB (@lem3834824 _99546 _99547) (@lem3834823 _99546 _99547 x f s)). Qed.
Lemma lem3834826 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term645 _99546 _99547 f s) = (term646 _99546 _99547 f s).
Proof. exact (fun_ext (fun x : type434 _99546 _99547 => @lem3834825 _99546 _99547 x f s)). Qed.
Lemma lem3834827 {_99546 _99547 : Type'} : (@ex ((_99546 -> _99547 -> _99547) -> _99546)) = (@ex ((_99546 -> _99547 -> _99547) -> _99546)).
Proof. exact (eq_refl (@ex ((_99546 -> _99547 -> _99547) -> _99546))). Qed.
Lemma lem3834828 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term628 _99546 _99547 f s) = (term647 _99546 _99547 f s).
Proof. exact (MK_COMB (@lem3834827 _99546 _99547) (@lem3834826 _99546 _99547 f s)). Qed.
Lemma lem3834829 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) : ((term627 _99546 _99547 f s) = (term628 _99546 _99547 f s)) = ((term622 _99546 _99547 f s) = (term647 _99546 _99547 f s)).
Proof. exact (MK_COMB (@lem3834817 _99546 _99547 f s) (@lem3834828 _99546 _99547 f s)). Qed.
Lemma lem3834830 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term622 _99546 _99547 f s) = (term647 _99546 _99547 f s).
Proof. exact (EQ_MP (@lem3834829 _99546 _99547 f s) (@lem3834804 _99546 _99547 f s)). Qed.
Lemma lem3834832 {A B : Type'} (P : type1413 A B) : (term623 A B P) = (term624 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3834833 {_99546 _99547 : Type'} (P : type430 _99546 _99547) : (term625 _99546 _99547 P) = (term626 _99546 _99547 P).
Proof. exact (@lem3834832 (type1411 _99546 _99547) _99546 P). Qed.
Lemma lem3834834 {_99546 _99547 : Type'} (x : type434 _99546 _99547) (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term648 _99546 _99547 x f s) = (term649 _99546 _99547 x f s).
Proof. exact (@lem3834833 _99546 _99547 (term650 _99546 _99547 x f s)). Qed.
Lemma lem3834835 {_99546 _99547 : Type'} (x : type434 _99546 _99547) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term651 _99546 _99547 x f s g) = (term652 _99546 _99547 x f g s).
Proof. exact (eq_refl (term651 _99546 _99547 x f s g)). Qed.
Lemma lem3834836 {_99546 : Type'} (y : _99546) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3834837 {_99546 _99547 : Type'} (x : type434 _99546 _99547) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) (y : _99546) : (term653 _99546 _99547 x f s g y) = (term654 _99546 _99547 x f g s y).
Proof. exact (MK_COMB (@lem3834835 _99546 _99547 x f g s) (@lem3834836 _99546 y)). Qed.
Lemma lem3834838 {_99546 _99547 : Type'} (y : _99546) (x : type434 _99546 _99547) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term654 _99546 _99547 x f g s y) = (term655 _99546 _99547 y x f g s).
Proof. exact (eq_refl (term654 _99546 _99547 x f g s y)). Qed.
Lemma lem3834839 {_99546 _99547 : Type'} (y : _99546) (x : type434 _99546 _99547) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term653 _99546 _99547 x f s g y) = (term655 _99546 _99547 y x f g s).
Proof. exact (TRANS (@lem3834837 _99546 _99547 x f g s y) (@lem3834838 _99546 _99547 y x f g s)). Qed.
Lemma lem3834840 {_99546 _99547 : Type'} (x : type434 _99546 _99547) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term656 _99546 _99547 x f s g) = (term652 _99546 _99547 x f g s).
Proof. exact (fun_ext (fun y : _99546 => @lem3834839 _99546 _99547 y x f g s)). Qed.
Lemma lem3834841 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3834842 {_99546 _99547 : Type'} (x : type434 _99546 _99547) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term657 _99546 _99547 x f s g) = (term640 _99546 _99547 x f g s).
Proof. exact (MK_COMB (@lem3834841 _99546) (@lem3834840 _99546 _99547 x f g s)). Qed.
Lemma lem3834843 {_99546 _99547 : Type'} (x : type434 _99546 _99547) (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term658 _99546 _99547 x f s) = (term642 _99546 _99547 x f s).
Proof. exact (fun_ext (fun g : type1411 _99546 _99547 => @lem3834842 _99546 _99547 x f g s)). Qed.
Lemma lem3834844 {_99546 _99547 : Type'} : (@all (_99546 -> _99547 -> _99547)) = (@all (_99546 -> _99547 -> _99547)).
Proof. exact (eq_refl (@all (_99546 -> _99547 -> _99547))). Qed.
Lemma lem3834845 {_99546 _99547 : Type'} (x : type434 _99546 _99547) (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term648 _99546 _99547 x f s) = (term644 _99546 _99547 x f s).
Proof. exact (MK_COMB (@lem3834844 _99546 _99547) (@lem3834843 _99546 _99547 x f s)). Qed.
Lemma lem3834846 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3834847 {_99546 _99547 : Type'} (x : type434 _99546 _99547) (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term659 _99546 _99547 x f s) = (term660 _99546 _99547 x f s).
Proof. exact (MK_COMB (@lem3834846) (@lem3834845 _99546 _99547 x f s)). Qed.
Lemma lem3834848 {_99546 _99547 : Type'} (x : type434 _99546 _99547) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term651 _99546 _99547 x f s g) = (term652 _99546 _99547 x f g s).
Proof. exact (eq_refl (term651 _99546 _99547 x f s g)). Qed.
Lemma lem3834849 {_99546 _99547 : Type'} (y : type434 _99546 _99547) (g : type1411 _99546 _99547) : (y g) = (y g).
Proof. exact (eq_refl (y g)). Qed.
Lemma lem3834850 {_99546 _99547 : Type'} (x : type434 _99546 _99547) (f : type1411 _99546 _99547) (s : _99546 -> Prop) (y : type434 _99546 _99547) (g : type1411 _99546 _99547) : (term661 _99546 _99547 x f s y g) = (term662 _99546 _99547 x f s y g).
Proof. exact (MK_COMB (@lem3834848 _99546 _99547 x f g s) (@lem3834849 _99546 _99547 y g)). Qed.
Lemma lem3834851 {_99546 _99547 : Type'} (y : type434 _99546 _99547) (x : type434 _99546 _99547) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term662 _99546 _99547 x f s y g) = (term663 _99546 _99547 y x f g s).
Proof. exact (eq_refl (term662 _99546 _99547 x f s y g)). Qed.
Lemma lem3834852 {_99546 _99547 : Type'} (y : type434 _99546 _99547) (x : type434 _99546 _99547) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term661 _99546 _99547 x f s y g) = (term663 _99546 _99547 y x f g s).
Proof. exact (TRANS (@lem3834850 _99546 _99547 x f s y g) (@lem3834851 _99546 _99547 y x f g s)). Qed.
Lemma lem3834853 {_99546 _99547 : Type'} (y : type434 _99546 _99547) (x : type434 _99546 _99547) (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term664 _99546 _99547 x f s y) = (term665 _99546 _99547 y x f s).
Proof. exact (fun_ext (fun g : type1411 _99546 _99547 => @lem3834852 _99546 _99547 y x f g s)). Qed.
Lemma lem3834854 {_99546 _99547 : Type'} : (@all (_99546 -> _99547 -> _99547)) = (@all (_99546 -> _99547 -> _99547)).
Proof. exact (eq_refl (@all (_99546 -> _99547 -> _99547))). Qed.
Lemma lem3834855 {_99546 _99547 : Type'} (y : type434 _99546 _99547) (x : type434 _99546 _99547) (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term666 _99546 _99547 x f s y) = (term667 _99546 _99547 y x f s).
Proof. exact (MK_COMB (@lem3834854 _99546 _99547) (@lem3834853 _99546 _99547 y x f s)). Qed.
Lemma lem3834856 {_99546 _99547 : Type'} (x : type434 _99546 _99547) (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term668 _99546 _99547 x f s) = (term669 _99546 _99547 x f s).
Proof. exact (fun_ext (fun y : type434 _99546 _99547 => @lem3834855 _99546 _99547 y x f s)). Qed.
Lemma lem3834857 {_99546 _99547 : Type'} : (@ex ((_99546 -> _99547 -> _99547) -> _99546)) = (@ex ((_99546 -> _99547 -> _99547) -> _99546)).
Proof. exact (eq_refl (@ex ((_99546 -> _99547 -> _99547) -> _99546))). Qed.
Lemma lem3834858 {_99546 _99547 : Type'} (x : type434 _99546 _99547) (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term649 _99546 _99547 x f s) = (term670 _99546 _99547 x f s).
Proof. exact (MK_COMB (@lem3834857 _99546 _99547) (@lem3834856 _99546 _99547 x f s)). Qed.
Lemma lem3834859 {_99546 _99547 : Type'} (x : type434 _99546 _99547) (f : type1411 _99546 _99547) (s : _99546 -> Prop) : ((term648 _99546 _99547 x f s) = (term649 _99546 _99547 x f s)) = ((term644 _99546 _99547 x f s) = (term670 _99546 _99547 x f s)).
Proof. exact (MK_COMB (@lem3834847 _99546 _99547 x f s) (@lem3834858 _99546 _99547 x f s)). Qed.
Lemma lem3834860 {_99546 _99547 : Type'} (x : type434 _99546 _99547) (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term644 _99546 _99547 x f s) = (term670 _99546 _99547 x f s).
Proof. exact (EQ_MP (@lem3834859 _99546 _99547 x f s) (@lem3834834 _99546 _99547 x f s)). Qed.
Lemma lem3834862 {A B : Type'} (P : type1413 A B) : (term623 A B P) = (term624 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3834863 {_99546 _99547 : Type'} (P : type433 _99546 _99547) : (term671 _99546 _99547 P) = (term672 _99546 _99547 P).
Proof. exact (@lem3834862 (type1411 _99546 _99547) _99547 P). Qed.
Lemma lem3834864 {_99546 _99547 : Type'} (y : type434 _99546 _99547) (x : type434 _99546 _99547) (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term673 _99546 _99547 y x f s) = (term674 _99546 _99547 y x f s).
Proof. exact (@lem3834863 _99546 _99547 (term675 _99546 _99547 y x f s)). Qed.
Lemma lem3834865 {_99546 _99547 : Type'} (y : type434 _99546 _99547) (x : type434 _99546 _99547) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term676 _99546 _99547 y x f s g) = (term677 _99546 _99547 y x f g s).
Proof. exact (eq_refl (term676 _99546 _99547 y x f s g)). Qed.
Lemma lem3834866 {_99547 : Type'} (s : _99547) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3834867 {_99546 _99547 : Type'} (y : type434 _99546 _99547) (x : type434 _99546 _99547) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) (s' : _99547) : (term678 _99546 _99547 y x f s g s') = (term679 _99546 _99547 y x f g s s').
Proof. exact (MK_COMB (@lem3834865 _99546 _99547 y x f g s) (@lem3834866 _99547 s')). Qed.
Lemma lem3834868 {_99546 _99547 : Type'} (y : type434 _99546 _99547) (x : type434 _99546 _99547) (s : _99547) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s' : _99546 -> Prop) : (term679 _99546 _99547 y x f g s' s) = (term680 _99546 _99547 y x s f g s').
Proof. exact (eq_refl (term679 _99546 _99547 y x f g s' s)). Qed.
Lemma lem3834869 {_99546 _99547 : Type'} (y : type434 _99546 _99547) (x : type434 _99546 _99547) (s : _99547) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s' : _99546 -> Prop) : (term678 _99546 _99547 y x f s' g s) = (term680 _99546 _99547 y x s f g s').
Proof. exact (TRANS (@lem3834867 _99546 _99547 y x f g s' s) (@lem3834868 _99546 _99547 y x s f g s')). Qed.
Lemma lem3834870 {_99546 _99547 : Type'} (y : type434 _99546 _99547) (x : type434 _99546 _99547) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term681 _99546 _99547 y x f s g) = (term677 _99546 _99547 y x f g s).
Proof. exact (fun_ext (fun s' : _99547 => @lem3834869 _99546 _99547 y x s' f g s)). Qed.
Lemma lem3834871 {_99547 : Type'} : (@ex _99547) = (@ex _99547).
Proof. exact (eq_refl (@ex _99547)). Qed.
Lemma lem3834872 {_99546 _99547 : Type'} (y : type434 _99546 _99547) (x : type434 _99546 _99547) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term682 _99546 _99547 y x f s g) = (term663 _99546 _99547 y x f g s).
Proof. exact (MK_COMB (@lem3834871 _99547) (@lem3834870 _99546 _99547 y x f g s)). Qed.
Lemma lem3834873 {_99546 _99547 : Type'} (y : type434 _99546 _99547) (x : type434 _99546 _99547) (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term683 _99546 _99547 y x f s) = (term665 _99546 _99547 y x f s).
Proof. exact (fun_ext (fun g : type1411 _99546 _99547 => @lem3834872 _99546 _99547 y x f g s)). Qed.
Lemma lem3834874 {_99546 _99547 : Type'} : (@all (_99546 -> _99547 -> _99547)) = (@all (_99546 -> _99547 -> _99547)).
Proof. exact (eq_refl (@all (_99546 -> _99547 -> _99547))). Qed.
Lemma lem3834875 {_99546 _99547 : Type'} (y : type434 _99546 _99547) (x : type434 _99546 _99547) (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term673 _99546 _99547 y x f s) = (term667 _99546 _99547 y x f s).
Proof. exact (MK_COMB (@lem3834874 _99546 _99547) (@lem3834873 _99546 _99547 y x f s)). Qed.
Lemma lem3834876 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3834877 {_99546 _99547 : Type'} (y : type434 _99546 _99547) (x : type434 _99546 _99547) (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term684 _99546 _99547 y x f s) = (term685 _99546 _99547 y x f s).
Proof. exact (MK_COMB (@lem3834876) (@lem3834875 _99546 _99547 y x f s)). Qed.
Lemma lem3834878 {_99546 _99547 : Type'} (y : type434 _99546 _99547) (x : type434 _99546 _99547) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : (term676 _99546 _99547 y x f s g) = (term677 _99546 _99547 y x f g s).
Proof. exact (eq_refl (term676 _99546 _99547 y x f s g)). Qed.
Lemma lem3834879 {_99546 _99547 : Type'} (s : type435 _99546 _99547) (g : type1411 _99546 _99547) : (s g) = (s g).
Proof. exact (eq_refl (s g)). Qed.
Lemma lem3834880 {_99546 _99547 : Type'} (y : type434 _99546 _99547) (x : type434 _99546 _99547) (f : type1411 _99546 _99547) (s : _99546 -> Prop) (s' : type435 _99546 _99547) (g : type1411 _99546 _99547) : (term686 _99546 _99547 y x f s s' g) = (term687 _99546 _99547 y x f s s' g).
Proof. exact (MK_COMB (@lem3834878 _99546 _99547 y x f g s) (@lem3834879 _99546 _99547 s' g)). Qed.
Lemma lem3834881 {_99546 _99547 : Type'} (y : type434 _99546 _99547) (x : type434 _99546 _99547) (s : type435 _99546 _99547) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s' : _99546 -> Prop) : (term687 _99546 _99547 y x f s' s g) = (term688 _99546 _99547 y x s f g s').
Proof. exact (eq_refl (term687 _99546 _99547 y x f s' s g)). Qed.
Lemma lem3834882 {_99546 _99547 : Type'} (y : type434 _99546 _99547) (x : type434 _99546 _99547) (s : type435 _99546 _99547) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s' : _99546 -> Prop) : (term686 _99546 _99547 y x f s' s g) = (term688 _99546 _99547 y x s f g s').
Proof. exact (TRANS (@lem3834880 _99546 _99547 y x f s' s g) (@lem3834881 _99546 _99547 y x s f g s')). Qed.
Lemma lem3834883 {_99546 _99547 : Type'} (y : type434 _99546 _99547) (x : type434 _99546 _99547) (s : type435 _99546 _99547) (f : type1411 _99546 _99547) (s' : _99546 -> Prop) : (term689 _99546 _99547 y x f s' s) = (term690 _99546 _99547 y x s f s').
Proof. exact (fun_ext (fun g : type1411 _99546 _99547 => @lem3834882 _99546 _99547 y x s f g s')). Qed.
Lemma lem3834884 {_99546 _99547 : Type'} : (@all (_99546 -> _99547 -> _99547)) = (@all (_99546 -> _99547 -> _99547)).
Proof. exact (eq_refl (@all (_99546 -> _99547 -> _99547))). Qed.
Lemma lem3834885 {_99546 _99547 : Type'} (y : type434 _99546 _99547) (x : type434 _99546 _99547) (s : type435 _99546 _99547) (f : type1411 _99546 _99547) (s' : _99546 -> Prop) : (term691 _99546 _99547 y x f s' s) = (term692 _99546 _99547 y x s f s').
Proof. exact (MK_COMB (@lem3834884 _99546 _99547) (@lem3834883 _99546 _99547 y x s f s')). Qed.
Lemma lem3834886 {_99546 _99547 : Type'} (y : type434 _99546 _99547) (x : type434 _99546 _99547) (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term693 _99546 _99547 y x f s) = (term694 _99546 _99547 y x f s).
Proof. exact (fun_ext (fun s' : type435 _99546 _99547 => @lem3834885 _99546 _99547 y x s' f s)). Qed.
Lemma lem3834887 {_99546 _99547 : Type'} : (@ex ((_99546 -> _99547 -> _99547) -> _99547)) = (@ex ((_99546 -> _99547 -> _99547) -> _99547)).
Proof. exact (eq_refl (@ex ((_99546 -> _99547 -> _99547) -> _99547))). Qed.
Lemma lem3834888 {_99546 _99547 : Type'} (y : type434 _99546 _99547) (x : type434 _99546 _99547) (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term674 _99546 _99547 y x f s) = (term695 _99546 _99547 y x f s).
Proof. exact (MK_COMB (@lem3834887 _99546 _99547) (@lem3834886 _99546 _99547 y x f s)). Qed.
Lemma lem3834889 {_99546 _99547 : Type'} (y : type434 _99546 _99547) (x : type434 _99546 _99547) (f : type1411 _99546 _99547) (s : _99546 -> Prop) : ((term673 _99546 _99547 y x f s) = (term674 _99546 _99547 y x f s)) = ((term667 _99546 _99547 y x f s) = (term695 _99546 _99547 y x f s)).
Proof. exact (MK_COMB (@lem3834877 _99546 _99547 y x f s) (@lem3834888 _99546 _99547 y x f s)). Qed.
Lemma lem3834890 {_99546 _99547 : Type'} (y : type434 _99546 _99547) (x : type434 _99546 _99547) (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term667 _99546 _99547 y x f s) = (term695 _99546 _99547 y x f s).
Proof. exact (EQ_MP (@lem3834889 _99546 _99547 y x f s) (@lem3834864 _99546 _99547 y x f s)). Qed.
Lemma lem3834891 {_99546 _99547 : Type'} (x : type434 _99546 _99547) (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term669 _99546 _99547 x f s) = (term696 _99546 _99547 x f s).
Proof. exact (fun_ext (fun y : type434 _99546 _99547 => @lem3834890 _99546 _99547 y x f s)). Qed.
Lemma lem3834892 {_99546 _99547 : Type'} : (@ex ((_99546 -> _99547 -> _99547) -> _99546)) = (@ex ((_99546 -> _99547 -> _99547) -> _99546)).
Proof. exact (eq_refl (@ex ((_99546 -> _99547 -> _99547) -> _99546))). Qed.
Lemma lem3834893 {_99546 _99547 : Type'} (x : type434 _99546 _99547) (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term670 _99546 _99547 x f s) = (term697 _99546 _99547 x f s).
Proof. exact (MK_COMB (@lem3834892 _99546 _99547) (@lem3834891 _99546 _99547 x f s)). Qed.
Lemma lem3834894 {_99546 _99547 : Type'} (x : type434 _99546 _99547) (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term644 _99546 _99547 x f s) = (term697 _99546 _99547 x f s).
Proof. exact (TRANS (@lem3834860 _99546 _99547 x f s) (@lem3834893 _99546 _99547 x f s)). Qed.
Lemma lem3834895 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term646 _99546 _99547 f s) = (term698 _99546 _99547 f s).
Proof. exact (fun_ext (fun x : type434 _99546 _99547 => @lem3834894 _99546 _99547 x f s)). Qed.
Lemma lem3834896 {_99546 _99547 : Type'} : (@ex ((_99546 -> _99547 -> _99547) -> _99546)) = (@ex ((_99546 -> _99547 -> _99547) -> _99546)).
Proof. exact (eq_refl (@ex ((_99546 -> _99547 -> _99547) -> _99546))). Qed.
Lemma lem3834897 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term647 _99546 _99547 f s) = (term699 _99546 _99547 f s).
Proof. exact (MK_COMB (@lem3834896 _99546 _99547) (@lem3834895 _99546 _99547 f s)). Qed.
Lemma lem3834898 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term622 _99546 _99547 f s) = (term699 _99546 _99547 f s).
Proof. exact (TRANS (@lem3834830 _99546 _99547 f s) (@lem3834897 _99546 _99547 f s)). Qed.
Lemma lem3834899 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term445 _99546 _99547 f s) = (term699 _99546 _99547 f s).
Proof. exact (TRANS (@lem3834800 _99546 _99547 f s) (@lem3834898 _99546 _99547 f s)). Qed.
Lemma lem3834900 {_99546 _99547 : Type'} (s : _99546 -> Prop) : (term446 _99546 _99547 s) = (term700 _99546 _99547 s).
Proof. exact (fun_ext (fun f : type1411 _99546 _99547 => @lem3834899 _99546 _99547 f s)). Qed.
Lemma lem3834901 {_99546 _99547 : Type'} : (@all (_99546 -> _99547 -> _99547)) = (@all (_99546 -> _99547 -> _99547)).
Proof. exact (eq_refl (@all (_99546 -> _99547 -> _99547))). Qed.
Lemma lem3834902 {_99546 _99547 : Type'} (s : _99546 -> Prop) : (term447 _99546 _99547 s) = (term701 _99546 _99547 s).
Proof. exact (MK_COMB (@lem3834901 _99546 _99547) (@lem3834900 _99546 _99547 s)). Qed.
Lemma lem3834904 {A B : Type'} (P : type1413 A B) : (term623 A B P) = (term624 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3834905 {_99546 _99547 : Type'} (P : type425 _99546 _99547) : (term702 _99546 _99547 P) = (term703 _99546 _99547 P).
Proof. exact (@lem3834904 (type1411 _99546 _99547) (type434 _99546 _99547) P). Qed.
Lemma lem3834906 {_99546 _99547 : Type'} (s : _99546 -> Prop) : (term704 _99546 _99547 s) = (term705 _99546 _99547 s).
Proof. exact (@lem3834905 _99546 _99547 (term706 _99546 _99547 s)). Qed.
Lemma lem3834907 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term707 _99546 _99547 s f) = (term698 _99546 _99547 f s).
Proof. exact (eq_refl (term707 _99546 _99547 s f)). Qed.
Lemma lem3834908 {_99546 _99547 : Type'} (x : type434 _99546 _99547) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3834909 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) (x : type434 _99546 _99547) : (term708 _99546 _99547 s f x) = (term709 _99546 _99547 f s x).
Proof. exact (MK_COMB (@lem3834907 _99546 _99547 f s) (@lem3834908 _99546 _99547 x)). Qed.
Lemma lem3834910 {_99546 _99547 : Type'} (x : type434 _99546 _99547) (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term709 _99546 _99547 f s x) = (term697 _99546 _99547 x f s).
Proof. exact (eq_refl (term709 _99546 _99547 f s x)). Qed.
Lemma lem3834911 {_99546 _99547 : Type'} (x : type434 _99546 _99547) (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term708 _99546 _99547 s f x) = (term697 _99546 _99547 x f s).
Proof. exact (TRANS (@lem3834909 _99546 _99547 f s x) (@lem3834910 _99546 _99547 x f s)). Qed.
Lemma lem3834912 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term710 _99546 _99547 s f) = (term698 _99546 _99547 f s).
Proof. exact (fun_ext (fun x : type434 _99546 _99547 => @lem3834911 _99546 _99547 x f s)). Qed.
Lemma lem3834913 {_99546 _99547 : Type'} : (@ex ((_99546 -> _99547 -> _99547) -> _99546)) = (@ex ((_99546 -> _99547 -> _99547) -> _99546)).
Proof. exact (eq_refl (@ex ((_99546 -> _99547 -> _99547) -> _99546))). Qed.
Lemma lem3834914 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term711 _99546 _99547 s f) = (term699 _99546 _99547 f s).
Proof. exact (MK_COMB (@lem3834913 _99546 _99547) (@lem3834912 _99546 _99547 f s)). Qed.
Lemma lem3834915 {_99546 _99547 : Type'} (s : _99546 -> Prop) : (term712 _99546 _99547 s) = (term700 _99546 _99547 s).
Proof. exact (fun_ext (fun f : type1411 _99546 _99547 => @lem3834914 _99546 _99547 f s)). Qed.
Lemma lem3834916 {_99546 _99547 : Type'} : (@all (_99546 -> _99547 -> _99547)) = (@all (_99546 -> _99547 -> _99547)).
Proof. exact (eq_refl (@all (_99546 -> _99547 -> _99547))). Qed.
Lemma lem3834917 {_99546 _99547 : Type'} (s : _99546 -> Prop) : (term704 _99546 _99547 s) = (term701 _99546 _99547 s).
Proof. exact (MK_COMB (@lem3834916 _99546 _99547) (@lem3834915 _99546 _99547 s)). Qed.
Lemma lem3834918 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3834919 {_99546 _99547 : Type'} (s : _99546 -> Prop) : (term713 _99546 _99547 s) = (term714 _99546 _99547 s).
Proof. exact (MK_COMB (@lem3834918) (@lem3834917 _99546 _99547 s)). Qed.
Lemma lem3834920 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term707 _99546 _99547 s f) = (term698 _99546 _99547 f s).
Proof. exact (eq_refl (term707 _99546 _99547 s f)). Qed.
Lemma lem3834921 {_99546 _99547 : Type'} (x : type427 _99546 _99547) (f : type1411 _99546 _99547) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem3834922 {_99546 _99547 : Type'} (s : _99546 -> Prop) (x : type427 _99546 _99547) (f : type1411 _99546 _99547) : (term715 _99546 _99547 s x f) = (term716 _99546 _99547 s x f).
Proof. exact (MK_COMB (@lem3834920 _99546 _99547 f s) (@lem3834921 _99546 _99547 x f)). Qed.
Lemma lem3834923 {_99546 _99547 : Type'} (x : type427 _99546 _99547) (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term716 _99546 _99547 s x f) = (term717 _99546 _99547 x f s).
Proof. exact (eq_refl (term716 _99546 _99547 s x f)). Qed.
Lemma lem3834924 {_99546 _99547 : Type'} (x : type427 _99546 _99547) (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term715 _99546 _99547 s x f) = (term717 _99546 _99547 x f s).
Proof. exact (TRANS (@lem3834922 _99546 _99547 s x f) (@lem3834923 _99546 _99547 x f s)). Qed.
Lemma lem3834925 {_99546 _99547 : Type'} (x : type427 _99546 _99547) (s : _99546 -> Prop) : (term718 _99546 _99547 s x) = (term719 _99546 _99547 x s).
Proof. exact (fun_ext (fun f : type1411 _99546 _99547 => @lem3834924 _99546 _99547 x f s)). Qed.
Lemma lem3834926 {_99546 _99547 : Type'} : (@all (_99546 -> _99547 -> _99547)) = (@all (_99546 -> _99547 -> _99547)).
Proof. exact (eq_refl (@all (_99546 -> _99547 -> _99547))). Qed.
Lemma lem3834927 {_99546 _99547 : Type'} (x : type427 _99546 _99547) (s : _99546 -> Prop) : (term720 _99546 _99547 s x) = (term721 _99546 _99547 x s).
Proof. exact (MK_COMB (@lem3834926 _99546 _99547) (@lem3834925 _99546 _99547 x s)). Qed.
Lemma lem3834928 {_99546 _99547 : Type'} (s : _99546 -> Prop) : (term722 _99546 _99547 s) = (term723 _99546 _99547 s).
Proof. exact (fun_ext (fun x : type427 _99546 _99547 => @lem3834927 _99546 _99547 x s)). Qed.
Lemma lem3834929 {_99546 _99547 : Type'} : (@ex ((_99546 -> _99547 -> _99547) -> (_99546 -> _99547 -> _99547) -> _99546)) = (@ex ((_99546 -> _99547 -> _99547) -> (_99546 -> _99547 -> _99547) -> _99546)).
Proof. exact (eq_refl (@ex ((_99546 -> _99547 -> _99547) -> (_99546 -> _99547 -> _99547) -> _99546))). Qed.
Lemma lem3834930 {_99546 _99547 : Type'} (s : _99546 -> Prop) : (term705 _99546 _99547 s) = (term724 _99546 _99547 s).
Proof. exact (MK_COMB (@lem3834929 _99546 _99547) (@lem3834928 _99546 _99547 s)). Qed.
Lemma lem3834931 {_99546 _99547 : Type'} (s : _99546 -> Prop) : ((term704 _99546 _99547 s) = (term705 _99546 _99547 s)) = ((term701 _99546 _99547 s) = (term724 _99546 _99547 s)).
Proof. exact (MK_COMB (@lem3834919 _99546 _99547 s) (@lem3834930 _99546 _99547 s)). Qed.
Lemma lem3834932 {_99546 _99547 : Type'} (s : _99546 -> Prop) : (term701 _99546 _99547 s) = (term724 _99546 _99547 s).
Proof. exact (EQ_MP (@lem3834931 _99546 _99547 s) (@lem3834906 _99546 _99547 s)). Qed.
Lemma lem3834934 {A B : Type'} (P : type1413 A B) : (term623 A B P) = (term624 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3834935 {_99546 _99547 : Type'} (P : type425 _99546 _99547) : (term702 _99546 _99547 P) = (term703 _99546 _99547 P).
Proof. exact (@lem3834934 (type1411 _99546 _99547) (type434 _99546 _99547) P). Qed.
Lemma lem3834936 {_99546 _99547 : Type'} (x : type427 _99546 _99547) (s : _99546 -> Prop) : (term725 _99546 _99547 x s) = (term726 _99546 _99547 x s).
Proof. exact (@lem3834935 _99546 _99547 (term727 _99546 _99547 x s)). Qed.
Lemma lem3834937 {_99546 _99547 : Type'} (x : type427 _99546 _99547) (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term728 _99546 _99547 x s f) = (term729 _99546 _99547 x f s).
Proof. exact (eq_refl (term728 _99546 _99547 x s f)). Qed.
Lemma lem3834938 {_99546 _99547 : Type'} (y : type434 _99546 _99547) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3834939 {_99546 _99547 : Type'} (x : type427 _99546 _99547) (f : type1411 _99546 _99547) (s : _99546 -> Prop) (y : type434 _99546 _99547) : (term730 _99546 _99547 x s f y) = (term731 _99546 _99547 x f s y).
Proof. exact (MK_COMB (@lem3834937 _99546 _99547 x f s) (@lem3834938 _99546 _99547 y)). Qed.
Lemma lem3834940 {_99546 _99547 : Type'} (y : type434 _99546 _99547) (x : type427 _99546 _99547) (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term731 _99546 _99547 x f s y) = (term732 _99546 _99547 y x f s).
Proof. exact (eq_refl (term731 _99546 _99547 x f s y)). Qed.
Lemma lem3834941 {_99546 _99547 : Type'} (y : type434 _99546 _99547) (x : type427 _99546 _99547) (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term730 _99546 _99547 x s f y) = (term732 _99546 _99547 y x f s).
Proof. exact (TRANS (@lem3834939 _99546 _99547 x f s y) (@lem3834940 _99546 _99547 y x f s)). Qed.
Lemma lem3834942 {_99546 _99547 : Type'} (x : type427 _99546 _99547) (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term733 _99546 _99547 x s f) = (term729 _99546 _99547 x f s).
Proof. exact (fun_ext (fun y : type434 _99546 _99547 => @lem3834941 _99546 _99547 y x f s)). Qed.
Lemma lem3834943 {_99546 _99547 : Type'} : (@ex ((_99546 -> _99547 -> _99547) -> _99546)) = (@ex ((_99546 -> _99547 -> _99547) -> _99546)).
Proof. exact (eq_refl (@ex ((_99546 -> _99547 -> _99547) -> _99546))). Qed.
Lemma lem3834944 {_99546 _99547 : Type'} (x : type427 _99546 _99547) (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term734 _99546 _99547 x s f) = (term717 _99546 _99547 x f s).
Proof. exact (MK_COMB (@lem3834943 _99546 _99547) (@lem3834942 _99546 _99547 x f s)). Qed.
Lemma lem3834945 {_99546 _99547 : Type'} (x : type427 _99546 _99547) (s : _99546 -> Prop) : (term735 _99546 _99547 x s) = (term719 _99546 _99547 x s).
Proof. exact (fun_ext (fun f : type1411 _99546 _99547 => @lem3834944 _99546 _99547 x f s)). Qed.
Lemma lem3834946 {_99546 _99547 : Type'} : (@all (_99546 -> _99547 -> _99547)) = (@all (_99546 -> _99547 -> _99547)).
Proof. exact (eq_refl (@all (_99546 -> _99547 -> _99547))). Qed.
Lemma lem3834947 {_99546 _99547 : Type'} (x : type427 _99546 _99547) (s : _99546 -> Prop) : (term725 _99546 _99547 x s) = (term721 _99546 _99547 x s).
Proof. exact (MK_COMB (@lem3834946 _99546 _99547) (@lem3834945 _99546 _99547 x s)). Qed.
Lemma lem3834948 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3834949 {_99546 _99547 : Type'} (x : type427 _99546 _99547) (s : _99546 -> Prop) : (term736 _99546 _99547 x s) = (term737 _99546 _99547 x s).
Proof. exact (MK_COMB (@lem3834948) (@lem3834947 _99546 _99547 x s)). Qed.
Lemma lem3834950 {_99546 _99547 : Type'} (x : type427 _99546 _99547) (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term728 _99546 _99547 x s f) = (term729 _99546 _99547 x f s).
Proof. exact (eq_refl (term728 _99546 _99547 x s f)). Qed.
Lemma lem3834951 {_99546 _99547 : Type'} (y : type427 _99546 _99547) (f : type1411 _99546 _99547) : (y f) = (y f).
Proof. exact (eq_refl (y f)). Qed.
Lemma lem3834952 {_99546 _99547 : Type'} (x : type427 _99546 _99547) (s : _99546 -> Prop) (y : type427 _99546 _99547) (f : type1411 _99546 _99547) : (term738 _99546 _99547 x s y f) = (term739 _99546 _99547 x s y f).
Proof. exact (MK_COMB (@lem3834950 _99546 _99547 x f s) (@lem3834951 _99546 _99547 y f)). Qed.
Lemma lem3834953 {_99546 _99547 : Type'} (y : type427 _99546 _99547) (x : type427 _99546 _99547) (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term739 _99546 _99547 x s y f) = (term740 _99546 _99547 y x f s).
Proof. exact (eq_refl (term739 _99546 _99547 x s y f)). Qed.
Lemma lem3834954 {_99546 _99547 : Type'} (y : type427 _99546 _99547) (x : type427 _99546 _99547) (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term738 _99546 _99547 x s y f) = (term740 _99546 _99547 y x f s).
Proof. exact (TRANS (@lem3834952 _99546 _99547 x s y f) (@lem3834953 _99546 _99547 y x f s)). Qed.
Lemma lem3834955 {_99546 _99547 : Type'} (y : type427 _99546 _99547) (x : type427 _99546 _99547) (s : _99546 -> Prop) : (term741 _99546 _99547 x s y) = (term742 _99546 _99547 y x s).
Proof. exact (fun_ext (fun f : type1411 _99546 _99547 => @lem3834954 _99546 _99547 y x f s)). Qed.
Lemma lem3834956 {_99546 _99547 : Type'} : (@all (_99546 -> _99547 -> _99547)) = (@all (_99546 -> _99547 -> _99547)).
Proof. exact (eq_refl (@all (_99546 -> _99547 -> _99547))). Qed.
Lemma lem3834957 {_99546 _99547 : Type'} (y : type427 _99546 _99547) (x : type427 _99546 _99547) (s : _99546 -> Prop) : (term743 _99546 _99547 x s y) = (term744 _99546 _99547 y x s).
Proof. exact (MK_COMB (@lem3834956 _99546 _99547) (@lem3834955 _99546 _99547 y x s)). Qed.
Lemma lem3834958 {_99546 _99547 : Type'} (x : type427 _99546 _99547) (s : _99546 -> Prop) : (term745 _99546 _99547 x s) = (term746 _99546 _99547 x s).
Proof. exact (fun_ext (fun y : type427 _99546 _99547 => @lem3834957 _99546 _99547 y x s)). Qed.
Lemma lem3834959 {_99546 _99547 : Type'} : (@ex ((_99546 -> _99547 -> _99547) -> (_99546 -> _99547 -> _99547) -> _99546)) = (@ex ((_99546 -> _99547 -> _99547) -> (_99546 -> _99547 -> _99547) -> _99546)).
Proof. exact (eq_refl (@ex ((_99546 -> _99547 -> _99547) -> (_99546 -> _99547 -> _99547) -> _99546))). Qed.
Lemma lem3834960 {_99546 _99547 : Type'} (x : type427 _99546 _99547) (s : _99546 -> Prop) : (term726 _99546 _99547 x s) = (term747 _99546 _99547 x s).
Proof. exact (MK_COMB (@lem3834959 _99546 _99547) (@lem3834958 _99546 _99547 x s)). Qed.
Lemma lem3834961 {_99546 _99547 : Type'} (x : type427 _99546 _99547) (s : _99546 -> Prop) : ((term725 _99546 _99547 x s) = (term726 _99546 _99547 x s)) = ((term721 _99546 _99547 x s) = (term747 _99546 _99547 x s)).
Proof. exact (MK_COMB (@lem3834949 _99546 _99547 x s) (@lem3834960 _99546 _99547 x s)). Qed.
Lemma lem3834962 {_99546 _99547 : Type'} (x : type427 _99546 _99547) (s : _99546 -> Prop) : (term721 _99546 _99547 x s) = (term747 _99546 _99547 x s).
Proof. exact (EQ_MP (@lem3834961 _99546 _99547 x s) (@lem3834936 _99546 _99547 x s)). Qed.
Lemma lem3834964 {A B : Type'} (P : type1413 A B) : (term623 A B P) = (term624 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3834965 {_99546 _99547 : Type'} (P : type426 _99546 _99547) : (term748 _99546 _99547 P) = (term749 _99546 _99547 P).
Proof. exact (@lem3834964 (type1411 _99546 _99547) (type435 _99546 _99547) P). Qed.
Lemma lem3834966 {_99546 _99547 : Type'} (y : type427 _99546 _99547) (x : type427 _99546 _99547) (s : _99546 -> Prop) : (term750 _99546 _99547 y x s) = (term751 _99546 _99547 y x s).
Proof. exact (@lem3834965 _99546 _99547 (term752 _99546 _99547 y x s)). Qed.
Lemma lem3834967 {_99546 _99547 : Type'} (y : type427 _99546 _99547) (x : type427 _99546 _99547) (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term753 _99546 _99547 y x s f) = (term754 _99546 _99547 y x f s).
Proof. exact (eq_refl (term753 _99546 _99547 y x s f)). Qed.
Lemma lem3834968 {_99546 _99547 : Type'} (s : type435 _99546 _99547) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3834969 {_99546 _99547 : Type'} (y : type427 _99546 _99547) (x : type427 _99546 _99547) (f : type1411 _99546 _99547) (s : _99546 -> Prop) (s' : type435 _99546 _99547) : (term755 _99546 _99547 y x s f s') = (term756 _99546 _99547 y x f s s').
Proof. exact (MK_COMB (@lem3834967 _99546 _99547 y x f s) (@lem3834968 _99546 _99547 s')). Qed.
Lemma lem3834970 {_99546 _99547 : Type'} (y : type427 _99546 _99547) (x : type427 _99546 _99547) (s : type435 _99546 _99547) (f : type1411 _99546 _99547) (s' : _99546 -> Prop) : (term756 _99546 _99547 y x f s' s) = (term757 _99546 _99547 y x s f s').
Proof. exact (eq_refl (term756 _99546 _99547 y x f s' s)). Qed.
Lemma lem3834971 {_99546 _99547 : Type'} (y : type427 _99546 _99547) (x : type427 _99546 _99547) (s : type435 _99546 _99547) (f : type1411 _99546 _99547) (s' : _99546 -> Prop) : (term755 _99546 _99547 y x s' f s) = (term757 _99546 _99547 y x s f s').
Proof. exact (TRANS (@lem3834969 _99546 _99547 y x f s' s) (@lem3834970 _99546 _99547 y x s f s')). Qed.
Lemma lem3834972 {_99546 _99547 : Type'} (y : type427 _99546 _99547) (x : type427 _99546 _99547) (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term758 _99546 _99547 y x s f) = (term754 _99546 _99547 y x f s).
Proof. exact (fun_ext (fun s' : type435 _99546 _99547 => @lem3834971 _99546 _99547 y x s' f s)). Qed.
Lemma lem3834973 {_99546 _99547 : Type'} : (@ex ((_99546 -> _99547 -> _99547) -> _99547)) = (@ex ((_99546 -> _99547 -> _99547) -> _99547)).
Proof. exact (eq_refl (@ex ((_99546 -> _99547 -> _99547) -> _99547))). Qed.
Lemma lem3834974 {_99546 _99547 : Type'} (y : type427 _99546 _99547) (x : type427 _99546 _99547) (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term759 _99546 _99547 y x s f) = (term740 _99546 _99547 y x f s).
Proof. exact (MK_COMB (@lem3834973 _99546 _99547) (@lem3834972 _99546 _99547 y x f s)). Qed.
Lemma lem3834975 {_99546 _99547 : Type'} (y : type427 _99546 _99547) (x : type427 _99546 _99547) (s : _99546 -> Prop) : (term760 _99546 _99547 y x s) = (term742 _99546 _99547 y x s).
Proof. exact (fun_ext (fun f : type1411 _99546 _99547 => @lem3834974 _99546 _99547 y x f s)). Qed.
Lemma lem3834976 {_99546 _99547 : Type'} : (@all (_99546 -> _99547 -> _99547)) = (@all (_99546 -> _99547 -> _99547)).
Proof. exact (eq_refl (@all (_99546 -> _99547 -> _99547))). Qed.
Lemma lem3834977 {_99546 _99547 : Type'} (y : type427 _99546 _99547) (x : type427 _99546 _99547) (s : _99546 -> Prop) : (term750 _99546 _99547 y x s) = (term744 _99546 _99547 y x s).
Proof. exact (MK_COMB (@lem3834976 _99546 _99547) (@lem3834975 _99546 _99547 y x s)). Qed.
Lemma lem3834978 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3834979 {_99546 _99547 : Type'} (y : type427 _99546 _99547) (x : type427 _99546 _99547) (s : _99546 -> Prop) : (term761 _99546 _99547 y x s) = (term762 _99546 _99547 y x s).
Proof. exact (MK_COMB (@lem3834978) (@lem3834977 _99546 _99547 y x s)). Qed.
Lemma lem3834980 {_99546 _99547 : Type'} (y : type427 _99546 _99547) (x : type427 _99546 _99547) (f : type1411 _99546 _99547) (s : _99546 -> Prop) : (term753 _99546 _99547 y x s f) = (term754 _99546 _99547 y x f s).
Proof. exact (eq_refl (term753 _99546 _99547 y x s f)). Qed.
Lemma lem3834981 {_99546 _99547 : Type'} (s : type428 _99546 _99547) (f : type1411 _99546 _99547) : (s f) = (s f).
Proof. exact (eq_refl (s f)). Qed.
Lemma lem3834982 {_99546 _99547 : Type'} (y : type427 _99546 _99547) (x : type427 _99546 _99547) (s : _99546 -> Prop) (s' : type428 _99546 _99547) (f : type1411 _99546 _99547) : (term763 _99546 _99547 y x s s' f) = (term764 _99546 _99547 y x s s' f).
Proof. exact (MK_COMB (@lem3834980 _99546 _99547 y x f s) (@lem3834981 _99546 _99547 s' f)). Qed.
Lemma lem3834983 {_99546 _99547 : Type'} (y : type427 _99546 _99547) (x : type427 _99546 _99547) (s : type428 _99546 _99547) (f : type1411 _99546 _99547) (s' : _99546 -> Prop) : (term764 _99546 _99547 y x s' s f) = (term765 _99546 _99547 y x s f s').
Proof. exact (eq_refl (term764 _99546 _99547 y x s' s f)). Qed.
Lemma lem3834984 {_99546 _99547 : Type'} (y : type427 _99546 _99547) (x : type427 _99546 _99547) (s : type428 _99546 _99547) (f : type1411 _99546 _99547) (s' : _99546 -> Prop) : (term763 _99546 _99547 y x s' s f) = (term765 _99546 _99547 y x s f s').
Proof. exact (TRANS (@lem3834982 _99546 _99547 y x s' s f) (@lem3834983 _99546 _99547 y x s f s')). Qed.
Lemma lem3834985 {_99546 _99547 : Type'} (y : type427 _99546 _99547) (x : type427 _99546 _99547) (s : type428 _99546 _99547) (s' : _99546 -> Prop) : (term766 _99546 _99547 y x s' s) = (term767 _99546 _99547 y x s s').
Proof. exact (fun_ext (fun f : type1411 _99546 _99547 => @lem3834984 _99546 _99547 y x s f s')). Qed.
Lemma lem3834986 {_99546 _99547 : Type'} : (@all (_99546 -> _99547 -> _99547)) = (@all (_99546 -> _99547 -> _99547)).
Proof. exact (eq_refl (@all (_99546 -> _99547 -> _99547))). Qed.
Lemma lem3834987 {_99546 _99547 : Type'} (y : type427 _99546 _99547) (x : type427 _99546 _99547) (s : type428 _99546 _99547) (s' : _99546 -> Prop) : (term768 _99546 _99547 y x s' s) = (term769 _99546 _99547 y x s s').
Proof. exact (MK_COMB (@lem3834986 _99546 _99547) (@lem3834985 _99546 _99547 y x s s')). Qed.
Lemma lem3834988 {_99546 _99547 : Type'} (y : type427 _99546 _99547) (x : type427 _99546 _99547) (s : _99546 -> Prop) : (term770 _99546 _99547 y x s) = (term771 _99546 _99547 y x s).
Proof. exact (fun_ext (fun s' : type428 _99546 _99547 => @lem3834987 _99546 _99547 y x s' s)). Qed.
Lemma lem3834989 {_99546 _99547 : Type'} : (@ex ((_99546 -> _99547 -> _99547) -> (_99546 -> _99547 -> _99547) -> _99547)) = (@ex ((_99546 -> _99547 -> _99547) -> (_99546 -> _99547 -> _99547) -> _99547)).
Proof. exact (eq_refl (@ex ((_99546 -> _99547 -> _99547) -> (_99546 -> _99547 -> _99547) -> _99547))). Qed.
Lemma lem3834990 {_99546 _99547 : Type'} (y : type427 _99546 _99547) (x : type427 _99546 _99547) (s : _99546 -> Prop) : (term751 _99546 _99547 y x s) = (term772 _99546 _99547 y x s).
Proof. exact (MK_COMB (@lem3834989 _99546 _99547) (@lem3834988 _99546 _99547 y x s)). Qed.
Lemma lem3834991 {_99546 _99547 : Type'} (y : type427 _99546 _99547) (x : type427 _99546 _99547) (s : _99546 -> Prop) : ((term750 _99546 _99547 y x s) = (term751 _99546 _99547 y x s)) = ((term744 _99546 _99547 y x s) = (term772 _99546 _99547 y x s)).
Proof. exact (MK_COMB (@lem3834979 _99546 _99547 y x s) (@lem3834990 _99546 _99547 y x s)). Qed.
Lemma lem3834992 {_99546 _99547 : Type'} (y : type427 _99546 _99547) (x : type427 _99546 _99547) (s : _99546 -> Prop) : (term744 _99546 _99547 y x s) = (term772 _99546 _99547 y x s).
Proof. exact (EQ_MP (@lem3834991 _99546 _99547 y x s) (@lem3834966 _99546 _99547 y x s)). Qed.
Lemma lem3834993 {_99546 _99547 : Type'} (x : type427 _99546 _99547) (s : _99546 -> Prop) : (term746 _99546 _99547 x s) = (term773 _99546 _99547 x s).
Proof. exact (fun_ext (fun y : type427 _99546 _99547 => @lem3834992 _99546 _99547 y x s)). Qed.
Lemma lem3834994 {_99546 _99547 : Type'} : (@ex ((_99546 -> _99547 -> _99547) -> (_99546 -> _99547 -> _99547) -> _99546)) = (@ex ((_99546 -> _99547 -> _99547) -> (_99546 -> _99547 -> _99547) -> _99546)).
Proof. exact (eq_refl (@ex ((_99546 -> _99547 -> _99547) -> (_99546 -> _99547 -> _99547) -> _99546))). Qed.
Lemma lem3834995 {_99546 _99547 : Type'} (x : type427 _99546 _99547) (s : _99546 -> Prop) : (term747 _99546 _99547 x s) = (term774 _99546 _99547 x s).
Proof. exact (MK_COMB (@lem3834994 _99546 _99547) (@lem3834993 _99546 _99547 x s)). Qed.
Lemma lem3834996 {_99546 _99547 : Type'} (x : type427 _99546 _99547) (s : _99546 -> Prop) : (term721 _99546 _99547 x s) = (term774 _99546 _99547 x s).
Proof. exact (TRANS (@lem3834962 _99546 _99547 x s) (@lem3834995 _99546 _99547 x s)). Qed.
Lemma lem3834997 {_99546 _99547 : Type'} (s : _99546 -> Prop) : (term723 _99546 _99547 s) = (term775 _99546 _99547 s).
Proof. exact (fun_ext (fun x : type427 _99546 _99547 => @lem3834996 _99546 _99547 x s)). Qed.
Lemma lem3834998 {_99546 _99547 : Type'} : (@ex ((_99546 -> _99547 -> _99547) -> (_99546 -> _99547 -> _99547) -> _99546)) = (@ex ((_99546 -> _99547 -> _99547) -> (_99546 -> _99547 -> _99547) -> _99546)).
Proof. exact (eq_refl (@ex ((_99546 -> _99547 -> _99547) -> (_99546 -> _99547 -> _99547) -> _99546))). Qed.
Lemma lem3834999 {_99546 _99547 : Type'} (s : _99546 -> Prop) : (term724 _99546 _99547 s) = (term776 _99546 _99547 s).
Proof. exact (MK_COMB (@lem3834998 _99546 _99547) (@lem3834997 _99546 _99547 s)). Qed.
Lemma lem3835000 {_99546 _99547 : Type'} (s : _99546 -> Prop) : (term701 _99546 _99547 s) = (term776 _99546 _99547 s).
Proof. exact (TRANS (@lem3834932 _99546 _99547 s) (@lem3834999 _99546 _99547 s)). Qed.
Lemma lem3835002 {_99546 _99547 : Type'} (s : _99546 -> Prop) : (term447 _99546 _99547 s) = (term776 _99546 _99547 s).
Proof. exact (TRANS (@lem3834902 _99546 _99547 s) (@lem3835000 _99546 _99547 s)). Qed.
Lemma lem3835003 {_99546 _99547 : Type'} (s : _99546 -> Prop) : (term150 _99546 _99547 s) = (term776 _99546 _99547 s).
Proof. exact (TRANS (@lem3834272 _99546 _99547 s) (@lem3835002 _99546 _99547 s)). Qed.
Lemma lem3835004 {_99546 _99547 : Type'} (s : _99546 -> Prop) (h1 : term150 _99546 _99547 s) : term776 _99546 _99547 s.
Proof. exact (EQ_MP (@lem3835003 _99546 _99547 s) (@lem3834146 _99546 _99547 s h1)). Qed.
Lemma lem3835023 {_99546 : Type'} (x : _99546) (x' : _99546) (s : _99546 -> Prop) : (term777 _99546 x x' s) = (term778 _99546 x x' s).
Proof. exact (@lem17160 (x' = x) (@IN _99546 x' s)). Qed.
Lemma lem3835024 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x' : _99546) : ((f x') = (g x')) = ((f x') = (g x')).
Proof. exact (eq_refl ((f x') = (g x'))). Qed.
Lemma lem3835025 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3835026 {_99546 : Type'} (x : _99546) (x' : _99546) (s : _99546 -> Prop) : (term779 _99546 x x' s) = (term780 _99546 x x' s).
Proof. exact (MK_COMB (@lem3835025) (@lem3835023 _99546 x x' s)). Qed.
Lemma lem3835027 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x' : _99546) : (term781 _99546 _99547 x s f g x') = (term782 _99546 _99547 x s f g x').
Proof. exact (MK_COMB (@lem3835026 _99546 x x' s) (@lem3835024 _99546 _99547 f g x')). Qed.
Lemma lem3835028 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x' : _99546) : (term271 _99546 _99547 x s f g x') = (term781 _99546 _99547 x s f g x').
Proof. exact (@lem17265 (term11 _99546 x x' s) ((f x') = (g x'))). Qed.
Lemma lem3835029 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x' : _99546) : (term271 _99546 _99547 x s f g x') = (term782 _99546 _99547 x s f g x').
Proof. exact (TRANS (@lem3835028 _99546 _99547 x s f g x') (@lem3835027 _99546 _99547 x s f g x')). Qed.
Lemma lem3835030 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term273 _99546 _99547 x s f g) = (term783 _99546 _99547 x s f g).
Proof. exact (fun_ext (fun x' : _99546 => @lem3835029 _99546 _99547 x s f g x')). Qed.
Lemma lem3835031 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3835084 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term275 _99546 _99547 x s f g) = (term784 _99546 _99547 x s f g).
Proof. exact (MK_COMB (@lem3835031 _99546) (@lem3835030 _99546 _99547 x s f g)). Qed.
Lemma lem3835085 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term275 _99546 _99547 x s f g) : term784 _99546 _99547 x s f g.
Proof. exact (EQ_MP (@lem3835084 _99546 _99547 x s f g) (@lem3834149 _99546 _99547 x s f g h1)). Qed.
Lemma lem3835088 {_99546 : Type'} (x : _99546) (y : _99546) : (term785 _99546 x y) = (x = y).
Proof. exact (@lem16933 (x = y)). Qed.
Lemma lem3835089 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) (s : _99547) : ((term93 _99546 _99547 x f y s) = (term93 _99546 _99547 y f x s)) = ((term93 _99546 _99547 x f y s) = (term93 _99546 _99547 y f x s)).
Proof. exact (eq_refl ((term93 _99546 _99547 x f y s) = (term93 _99546 _99547 y f x s))). Qed.
Lemma lem3835090 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term91 _99546 _99547 y f x) = (term91 _99546 _99547 y f x).
Proof. exact (fun_ext (fun s : _99547 => @lem3835089 _99546 _99547 y f x s)). Qed.
Lemma lem3835091 {_99547 : Type'} : (@all _99547) = (@all _99547).
Proof. exact (eq_refl (@all _99547)). Qed.
Lemma lem3835092 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term104 _99546 _99547 y f x) = (term104 _99546 _99547 y f x).
Proof. exact (MK_COMB (@lem3835091 _99547) (@lem3835090 _99546 _99547 y f x)). Qed.
Lemma lem3835093 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3835094 {_99546 : Type'} (x : _99546) (y : _99546) : (term786 _99546 x y) = (term787 _99546 x y).
Proof. exact (MK_COMB (@lem3835093) (@lem3835088 _99546 x y)). Qed.
Lemma lem3835095 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term788 _99546 _99547 y f x) = (term789 _99546 _99547 y f x).
Proof. exact (MK_COMB (@lem3835094 _99546 x y) (@lem3835092 _99546 _99547 y f x)). Qed.
Lemma lem3835096 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term105 _99546 _99547 y f x) = (term788 _99546 _99547 y f x).
Proof. exact (@lem17265 (term90 _99546 x y) (term104 _99546 _99547 y f x)). Qed.
Lemma lem3835097 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term105 _99546 _99547 y f x) = (term789 _99546 _99547 y f x).
Proof. exact (TRANS (@lem3835096 _99546 _99547 y f x) (@lem3835095 _99546 _99547 y f x)). Qed.
Lemma lem3835098 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (term107 _99546 _99547 f x) = (term790 _99546 _99547 f x).
Proof. exact (fun_ext (fun y : _99546 => @lem3835097 _99546 _99547 y f x)). Qed.
Lemma lem3835099 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3835100 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (term109 _99546 _99547 f x) = (term791 _99546 _99547 f x).
Proof. exact (MK_COMB (@lem3835099 _99546) (@lem3835098 _99546 _99547 f x)). Qed.
Lemma lem3835101 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term111 _99546 _99547 f) = (term792 _99546 _99547 f).
Proof. exact (fun_ext (fun x : _99546 => @lem3835100 _99546 _99547 f x)). Qed.
Lemma lem3835102 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3835163 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term112 _99546 _99547 f) = (term793 _99546 _99547 f).
Proof. exact (MK_COMB (@lem3835102 _99546) (@lem3835101 _99546 _99547 f)). Qed.
Lemma lem3835164 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (h1 : term112 _99546 _99547 f) : term793 _99546 _99547 f.
Proof. exact (EQ_MP (@lem3835163 _99546 _99547 f) (@lem3834150 _99546 _99547 f h1)). Qed.
Lemma lem3835167 {_99546 : Type'} (x : _99546) (y : _99546) : (term785 _99546 x y) = (x = y).
Proof. exact (@lem16933 (x = y)). Qed.
Lemma lem3835168 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) : ((term93 _99546 _99547 x g y s) = (term93 _99546 _99547 y g x s)) = ((term93 _99546 _99547 x g y s) = (term93 _99546 _99547 y g x s)).
Proof. exact (eq_refl ((term93 _99546 _99547 x g y s) = (term93 _99546 _99547 y g x s))). Qed.
Lemma lem3835169 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term91 _99546 _99547 y g x) = (term91 _99546 _99547 y g x).
Proof. exact (fun_ext (fun s : _99547 => @lem3835168 _99546 _99547 y g x s)). Qed.
Lemma lem3835170 {_99547 : Type'} : (@all _99547) = (@all _99547).
Proof. exact (eq_refl (@all _99547)). Qed.
Lemma lem3835171 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term104 _99546 _99547 y g x) = (term104 _99546 _99547 y g x).
Proof. exact (MK_COMB (@lem3835170 _99547) (@lem3835169 _99546 _99547 y g x)). Qed.
Lemma lem3835172 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3835173 {_99546 : Type'} (x : _99546) (y : _99546) : (term786 _99546 x y) = (term787 _99546 x y).
Proof. exact (MK_COMB (@lem3835172) (@lem3835167 _99546 x y)). Qed.
Lemma lem3835174 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term788 _99546 _99547 y g x) = (term789 _99546 _99547 y g x).
Proof. exact (MK_COMB (@lem3835173 _99546 x y) (@lem3835171 _99546 _99547 y g x)). Qed.
Lemma lem3835175 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term105 _99546 _99547 y g x) = (term788 _99546 _99547 y g x).
Proof. exact (@lem17265 (term90 _99546 x y) (term104 _99546 _99547 y g x)). Qed.
Lemma lem3835176 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term105 _99546 _99547 y g x) = (term789 _99546 _99547 y g x).
Proof. exact (TRANS (@lem3835175 _99546 _99547 y g x) (@lem3835174 _99546 _99547 y g x)). Qed.
Lemma lem3835177 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) : (term107 _99546 _99547 g x) = (term790 _99546 _99547 g x).
Proof. exact (fun_ext (fun y : _99546 => @lem3835176 _99546 _99547 y g x)). Qed.
Lemma lem3835178 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3835179 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) : (term109 _99546 _99547 g x) = (term791 _99546 _99547 g x).
Proof. exact (MK_COMB (@lem3835178 _99546) (@lem3835177 _99546 _99547 g x)). Qed.
Lemma lem3835180 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) : (term111 _99546 _99547 g) = (term792 _99546 _99547 g).
Proof. exact (fun_ext (fun x : _99546 => @lem3835179 _99546 _99547 g x)). Qed.
Lemma lem3835181 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3835242 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) : (term112 _99546 _99547 g) = (term793 _99546 _99547 g).
Proof. exact (MK_COMB (@lem3835181 _99546) (@lem3835180 _99546 _99547 g)). Qed.
Lemma lem3835243 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (h1 : term112 _99546 _99547 g) : term793 _99546 _99547 g.
Proof. exact (EQ_MP (@lem3835242 _99546 _99547 g) (@lem3834151 _99546 _99547 g h1)). Qed.
Lemma lem3835250 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term396 _99546 _99547 s f g x) = (term397 _99546 _99547 s f g x).
Proof. exact (@lem17362 (@IN _99546 x s) ((f x) = (g x))). Qed.
Lemma lem3835251 {_99546 : Type'} (P : _99546 -> Prop) : (term398 _99546 P) = (term399 _99546 P).
Proof. exact (@lem18392 _99546 P). Qed.
Lemma lem3835252 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term400 _99546 _99547 s f g) = (term401 _99546 _99547 s f g).
Proof. exact (@lem3835251 _99546 (term394 _99546 _99547 s f g)). Qed.
Lemma lem3835253 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term402 _99546 _99547 s f g x) = (term393 _99546 _99547 s f g x).
Proof. exact (eq_refl (term402 _99546 _99547 s f g x)). Qed.
Lemma lem3835254 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3835255 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term403 _99546 _99547 s f g x) = (term396 _99546 _99547 s f g x).
Proof. exact (MK_COMB (@lem3835254) (@lem3835253 _99546 _99547 s f g x)). Qed.
Lemma lem3835256 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term403 _99546 _99547 s f g x) = (term397 _99546 _99547 s f g x).
Proof. exact (TRANS (@lem3835255 _99546 _99547 s f g x) (@lem3835250 _99546 _99547 s f g x)). Qed.
Lemma lem3835257 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term404 _99546 _99547 s f g) = (term405 _99546 _99547 s f g).
Proof. exact (fun_ext (fun x : _99546 => @lem3835256 _99546 _99547 s f g x)). Qed.
Lemma lem3835258 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3835259 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term401 _99546 _99547 s f g) = (term406 _99546 _99547 s f g).
Proof. exact (MK_COMB (@lem3835258 _99546) (@lem3835257 _99546 _99547 s f g)). Qed.
Lemma lem3835260 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term400 _99546 _99547 s f g) = (term406 _99546 _99547 s f g).
Proof. exact (TRANS (@lem3835252 _99546 _99547 s f g) (@lem3835259 _99546 _99547 s f g)). Qed.
Lemma lem3835267 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term794 _99546 _99547 y f x s) = (term458 _99546 _99547 y f x s).
Proof. exact (@lem17362 (term90 _99546 x y) ((term93 _99546 _99547 x f y s) = (term93 _99546 _99547 y f x s))). Qed.
Lemma lem3835268 {_99547 : Type'} (P : _99547 -> Prop) : (term398 _99547 P) = (term399 _99547 P).
Proof. exact (@lem18392 _99547 P). Qed.
Lemma lem3835269 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term795 _99546 _99547 y f x) = (term796 _99546 _99547 y f x).
Proof. exact (@lem3835268 _99547 (term98 _99546 _99547 y f x)). Qed.
Lemma lem3835270 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term797 _99546 _99547 y f x s) = (term96 _99546 _99547 y f x s).
Proof. exact (eq_refl (term797 _99546 _99547 y f x s)). Qed.
Lemma lem3835271 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3835272 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term798 _99546 _99547 y f x s) = (term794 _99546 _99547 y f x s).
Proof. exact (MK_COMB (@lem3835271) (@lem3835270 _99546 _99547 y f x s)). Qed.
Lemma lem3835273 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term798 _99546 _99547 y f x s) = (term458 _99546 _99547 y f x s).
Proof. exact (TRANS (@lem3835272 _99546 _99547 y f x s) (@lem3835267 _99546 _99547 y f x s)). Qed.
Lemma lem3835274 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term799 _99546 _99547 y f x) = (term460 _99546 _99547 y f x).
Proof. exact (fun_ext (fun s : _99547 => @lem3835273 _99546 _99547 y f x s)). Qed.
Lemma lem3835275 {_99547 : Type'} : (@ex _99547) = (@ex _99547).
Proof. exact (eq_refl (@ex _99547)). Qed.
Lemma lem3835276 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term796 _99546 _99547 y f x) = (term461 _99546 _99547 y f x).
Proof. exact (MK_COMB (@lem3835275 _99547) (@lem3835274 _99546 _99547 y f x)). Qed.
Lemma lem3835277 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term795 _99546 _99547 y f x) = (term461 _99546 _99547 y f x).
Proof. exact (TRANS (@lem3835269 _99546 _99547 y f x) (@lem3835276 _99546 _99547 y f x)). Qed.
Lemma lem3835278 {_99546 : Type'} (P : _99546 -> Prop) : (term398 _99546 P) = (term399 _99546 P).
Proof. exact (@lem18392 _99546 P). Qed.
Lemma lem3835279 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (term800 _99546 _99547 f x) = (term801 _99546 _99547 f x).
Proof. exact (@lem3835278 _99546 (term106 _99546 _99547 f x)). Qed.
Lemma lem3835280 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term802 _99546 _99547 f x y) = (term99 _99546 _99547 y f x).
Proof. exact (eq_refl (term802 _99546 _99547 f x y)). Qed.
Lemma lem3835281 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3835282 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term803 _99546 _99547 f x y) = (term795 _99546 _99547 y f x).
Proof. exact (MK_COMB (@lem3835281) (@lem3835280 _99546 _99547 y f x)). Qed.
Lemma lem3835283 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term803 _99546 _99547 f x y) = (term461 _99546 _99547 y f x).
Proof. exact (TRANS (@lem3835282 _99546 _99547 y f x) (@lem3835277 _99546 _99547 y f x)). Qed.
Lemma lem3835284 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (term804 _99546 _99547 f x) = (term462 _99546 _99547 f x).
Proof. exact (fun_ext (fun y : _99546 => @lem3835283 _99546 _99547 y f x)). Qed.
Lemma lem3835285 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3835286 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (term801 _99546 _99547 f x) = (term463 _99546 _99547 f x).
Proof. exact (MK_COMB (@lem3835285 _99546) (@lem3835284 _99546 _99547 f x)). Qed.
Lemma lem3835287 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (term800 _99546 _99547 f x) = (term463 _99546 _99547 f x).
Proof. exact (TRANS (@lem3835279 _99546 _99547 f x) (@lem3835286 _99546 _99547 f x)). Qed.
Lemma lem3835288 {_99546 : Type'} (P : _99546 -> Prop) : (term398 _99546 P) = (term399 _99546 P).
Proof. exact (@lem18392 _99546 P). Qed.
Lemma lem3835289 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term805 _99546 _99547 f) = (term806 _99546 _99547 f).
Proof. exact (@lem3835288 _99546 (term110 _99546 _99547 f)). Qed.
Lemma lem3835290 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (term807 _99546 _99547 f x) = (term108 _99546 _99547 f x).
Proof. exact (eq_refl (term807 _99546 _99547 f x)). Qed.
Lemma lem3835291 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3835292 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (term808 _99546 _99547 f x) = (term800 _99546 _99547 f x).
Proof. exact (MK_COMB (@lem3835291) (@lem3835290 _99546 _99547 f x)). Qed.
Lemma lem3835293 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (term808 _99546 _99547 f x) = (term463 _99546 _99547 f x).
Proof. exact (TRANS (@lem3835292 _99546 _99547 f x) (@lem3835287 _99546 _99547 f x)). Qed.
Lemma lem3835294 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term809 _99546 _99547 f) = (term464 _99546 _99547 f).
Proof. exact (fun_ext (fun x : _99546 => @lem3835293 _99546 _99547 f x)). Qed.
Lemma lem3835295 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3835296 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term806 _99546 _99547 f) = (term465 _99546 _99547 f).
Proof. exact (MK_COMB (@lem3835295 _99546) (@lem3835294 _99546 _99547 f)). Qed.
Lemma lem3835297 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term805 _99546 _99547 f) = (term465 _99546 _99547 f).
Proof. exact (TRANS (@lem3835289 _99546 _99547 f) (@lem3835296 _99546 _99547 f)). Qed.
Lemma lem3835304 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term794 _99546 _99547 y g x s) = (term458 _99546 _99547 y g x s).
Proof. exact (@lem17362 (term90 _99546 x y) ((term93 _99546 _99547 x g y s) = (term93 _99546 _99547 y g x s))). Qed.
Lemma lem3835305 {_99547 : Type'} (P : _99547 -> Prop) : (term398 _99547 P) = (term399 _99547 P).
Proof. exact (@lem18392 _99547 P). Qed.
Lemma lem3835306 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term795 _99546 _99547 y g x) = (term796 _99546 _99547 y g x).
Proof. exact (@lem3835305 _99547 (term98 _99546 _99547 y g x)). Qed.
Lemma lem3835307 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term797 _99546 _99547 y g x s) = (term96 _99546 _99547 y g x s).
Proof. exact (eq_refl (term797 _99546 _99547 y g x s)). Qed.
Lemma lem3835308 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3835309 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term798 _99546 _99547 y g x s) = (term794 _99546 _99547 y g x s).
Proof. exact (MK_COMB (@lem3835308) (@lem3835307 _99546 _99547 y g x s)). Qed.
Lemma lem3835310 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term798 _99546 _99547 y g x s) = (term458 _99546 _99547 y g x s).
Proof. exact (TRANS (@lem3835309 _99546 _99547 y g x s) (@lem3835304 _99546 _99547 y g x s)). Qed.
Lemma lem3835311 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term799 _99546 _99547 y g x) = (term460 _99546 _99547 y g x).
Proof. exact (fun_ext (fun s : _99547 => @lem3835310 _99546 _99547 y g x s)). Qed.
Lemma lem3835312 {_99547 : Type'} : (@ex _99547) = (@ex _99547).
Proof. exact (eq_refl (@ex _99547)). Qed.
Lemma lem3835313 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term796 _99546 _99547 y g x) = (term461 _99546 _99547 y g x).
Proof. exact (MK_COMB (@lem3835312 _99547) (@lem3835311 _99546 _99547 y g x)). Qed.
Lemma lem3835314 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term795 _99546 _99547 y g x) = (term461 _99546 _99547 y g x).
Proof. exact (TRANS (@lem3835306 _99546 _99547 y g x) (@lem3835313 _99546 _99547 y g x)). Qed.
Lemma lem3835315 {_99546 : Type'} (P : _99546 -> Prop) : (term398 _99546 P) = (term399 _99546 P).
Proof. exact (@lem18392 _99546 P). Qed.
Lemma lem3835316 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) : (term800 _99546 _99547 g x) = (term801 _99546 _99547 g x).
Proof. exact (@lem3835315 _99546 (term106 _99546 _99547 g x)). Qed.
Lemma lem3835317 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term802 _99546 _99547 g x y) = (term99 _99546 _99547 y g x).
Proof. exact (eq_refl (term802 _99546 _99547 g x y)). Qed.
Lemma lem3835318 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3835319 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term803 _99546 _99547 g x y) = (term795 _99546 _99547 y g x).
Proof. exact (MK_COMB (@lem3835318) (@lem3835317 _99546 _99547 y g x)). Qed.
Lemma lem3835320 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term803 _99546 _99547 g x y) = (term461 _99546 _99547 y g x).
Proof. exact (TRANS (@lem3835319 _99546 _99547 y g x) (@lem3835314 _99546 _99547 y g x)). Qed.
Lemma lem3835321 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) : (term804 _99546 _99547 g x) = (term462 _99546 _99547 g x).
Proof. exact (fun_ext (fun y : _99546 => @lem3835320 _99546 _99547 y g x)). Qed.
Lemma lem3835322 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3835323 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) : (term801 _99546 _99547 g x) = (term463 _99546 _99547 g x).
Proof. exact (MK_COMB (@lem3835322 _99546) (@lem3835321 _99546 _99547 g x)). Qed.
Lemma lem3835324 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) : (term800 _99546 _99547 g x) = (term463 _99546 _99547 g x).
Proof. exact (TRANS (@lem3835316 _99546 _99547 g x) (@lem3835323 _99546 _99547 g x)). Qed.
Lemma lem3835325 {_99546 : Type'} (P : _99546 -> Prop) : (term398 _99546 P) = (term399 _99546 P).
Proof. exact (@lem18392 _99546 P). Qed.
Lemma lem3835326 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) : (term805 _99546 _99547 g) = (term806 _99546 _99547 g).
Proof. exact (@lem3835325 _99546 (term110 _99546 _99547 g)). Qed.
Lemma lem3835327 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) : (term807 _99546 _99547 g x) = (term108 _99546 _99547 g x).
Proof. exact (eq_refl (term807 _99546 _99547 g x)). Qed.
Lemma lem3835328 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3835329 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) : (term808 _99546 _99547 g x) = (term800 _99546 _99547 g x).
Proof. exact (MK_COMB (@lem3835328) (@lem3835327 _99546 _99547 g x)). Qed.
Lemma lem3835330 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) : (term808 _99546 _99547 g x) = (term463 _99546 _99547 g x).
Proof. exact (TRANS (@lem3835329 _99546 _99547 g x) (@lem3835324 _99546 _99547 g x)). Qed.
Lemma lem3835331 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) : (term809 _99546 _99547 g) = (term464 _99546 _99547 g).
Proof. exact (fun_ext (fun x : _99546 => @lem3835330 _99546 _99547 g x)). Qed.
Lemma lem3835332 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3835333 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) : (term806 _99546 _99547 g) = (term465 _99546 _99547 g).
Proof. exact (MK_COMB (@lem3835332 _99546) (@lem3835331 _99546 _99547 g)). Qed.
Lemma lem3835334 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) : (term805 _99546 _99547 g) = (term465 _99546 _99547 g).
Proof. exact (TRANS (@lem3835326 _99546 _99547 g) (@lem3835333 _99546 _99547 g)). Qed.
Lemma lem3835335 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3835336 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term810 _99546 _99547 f) = (term466 _99546 _99547 f).
Proof. exact (MK_COMB (@lem3835335) (@lem3835297 _99546 _99547 f)). Qed.
Lemma lem3835337 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term811 _99546 _99547 f g) = (term467 _99546 _99547 f g).
Proof. exact (MK_COMB (@lem3835336 _99546 _99547 f) (@lem3835334 _99546 _99547 g)). Qed.
Lemma lem3835338 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term812 _99546 _99547 f g) = (term811 _99546 _99547 f g).
Proof. exact (@lem17045 (term19 _99546 _99547 f) (term19 _99546 _99547 g)). Qed.
Lemma lem3835339 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term812 _99546 _99547 f g) = (term467 _99546 _99547 f g).
Proof. exact (TRANS (@lem3835338 _99546 _99547 f g) (@lem3835337 _99546 _99547 f g)). Qed.
Lemma lem3835340 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3835341 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term435 _99546 _99547 s f g) = (term436 _99546 _99547 s f g).
Proof. exact (MK_COMB (@lem3835340) (@lem3835260 _99546 _99547 s f g)). Qed.
Lemma lem3835342 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term813 _99546 _99547 s f g) = (term814 _99546 _99547 s f g).
Proof. exact (MK_COMB (@lem3835341 _99546 _99547 s f g) (@lem3835339 _99546 _99547 f g)). Qed.
Lemma lem3835343 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term355 _99546 _99547 s f g) = (term813 _99546 _99547 s f g).
Proof. exact (@lem17045 (term395 _99546 _99547 s f g) (term115 _99546 _99547 f g)). Qed.
Lemma lem3835344 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term355 _99546 _99547 s f g) = (term814 _99546 _99547 s f g).
Proof. exact (TRANS (@lem3835343 _99546 _99547 s f g) (@lem3835342 _99546 _99547 s f g)). Qed.
Lemma lem3835402 {A : Type'} (P : Prop) (Q : A -> Prop) : (term449 A P Q) = (term448 A P Q).
Proof. exact (EQ_MP (@lem18959 A P Q) (@lem18958 A P Q)). Qed.
Lemma lem3835403 {_99547 : Type'} (P : Prop) (Q : _99547 -> Prop) : (term449 _99547 P Q) = (term448 _99547 P Q).
Proof. exact (@lem3835402 _99547 P Q). Qed.
Lemma lem3835404 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term451 _99546 _99547 y f x) = (term450 _99546 _99547 y f x).
Proof. exact (@lem3835403 _99547 (term90 _99546 x y) (term412 _99546 _99547 y f x)). Qed.
Lemma lem3835405 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term452 _99546 _99547 y f x s) = (term410 _99546 _99547 y f x s).
Proof. exact (eq_refl (term452 _99546 _99547 y f x s)). Qed.
Lemma lem3835406 {_99546 : Type'} (x : _99546) (y : _99546) : (term414 _99546 x y) = (term414 _99546 x y).
Proof. exact (eq_refl (term414 _99546 x y)). Qed.
Lemma lem3835407 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term457 _99546 _99547 y f x s) = (term458 _99546 _99547 y f x s).
Proof. exact (MK_COMB (@lem3835406 _99546 x y) (@lem3835405 _99546 _99547 y f x s)). Qed.
Lemma lem3835408 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term459 _99546 _99547 y f x) = (term460 _99546 _99547 y f x).
Proof. exact (fun_ext (fun s : _99547 => @lem3835407 _99546 _99547 y f x s)). Qed.
Lemma lem3835409 {_99547 : Type'} : (@ex _99547) = (@ex _99547).
Proof. exact (eq_refl (@ex _99547)). Qed.
Lemma lem3835410 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term451 _99546 _99547 y f x) = (term461 _99546 _99547 y f x).
Proof. exact (MK_COMB (@lem3835409 _99547) (@lem3835408 _99546 _99547 y f x)). Qed.
Lemma lem3835411 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3835412 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term815 _99546 _99547 y f x) = (term816 _99546 _99547 y f x).
Proof. exact (MK_COMB (@lem3835411) (@lem3835410 _99546 _99547 y f x)). Qed.
Lemma lem3835413 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term452 _99546 _99547 y f x s) = (term410 _99546 _99547 y f x s).
Proof. exact (eq_refl (term452 _99546 _99547 y f x s)). Qed.
Lemma lem3835414 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term453 _99546 _99547 y f x) = (term412 _99546 _99547 y f x).
Proof. exact (fun_ext (fun s : _99547 => @lem3835413 _99546 _99547 y f x s)). Qed.
Lemma lem3835415 {_99547 : Type'} : (@ex _99547) = (@ex _99547).
Proof. exact (eq_refl (@ex _99547)). Qed.
Lemma lem3835416 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term454 _99546 _99547 y f x) = (term413 _99546 _99547 y f x).
Proof. exact (MK_COMB (@lem3835415 _99547) (@lem3835414 _99546 _99547 y f x)). Qed.
Lemma lem3835417 {_99546 : Type'} (x : _99546) (y : _99546) : (term414 _99546 x y) = (term414 _99546 x y).
Proof. exact (eq_refl (term414 _99546 x y)). Qed.
Lemma lem3835418 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term450 _99546 _99547 y f x) = (term416 _99546 _99547 y f x).
Proof. exact (MK_COMB (@lem3835417 _99546 x y) (@lem3835416 _99546 _99547 y f x)). Qed.
Lemma lem3835419 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : ((term451 _99546 _99547 y f x) = (term450 _99546 _99547 y f x)) = ((term461 _99546 _99547 y f x) = (term416 _99546 _99547 y f x)).
Proof. exact (MK_COMB (@lem3835412 _99546 _99547 y f x) (@lem3835418 _99546 _99547 y f x)). Qed.
Lemma lem3835420 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term461 _99546 _99547 y f x) = (term416 _99546 _99547 y f x).
Proof. exact (EQ_MP (@lem3835419 _99546 _99547 y f x) (@lem3835404 _99546 _99547 y f x)). Qed.
Lemma lem3835425 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (term462 _99546 _99547 f x) = (term422 _99546 _99547 f x).
Proof. exact (fun_ext (fun y : _99546 => @lem3835420 _99546 _99547 y f x)). Qed.
Lemma lem3835426 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3835427 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (term463 _99546 _99547 f x) = (term423 _99546 _99547 f x).
Proof. exact (MK_COMB (@lem3835426 _99546) (@lem3835425 _99546 _99547 f x)). Qed.
Lemma lem3835476 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term464 _99546 _99547 f) = (term428 _99546 _99547 f).
Proof. exact (fun_ext (fun x : _99546 => @lem3835427 _99546 _99547 f x)). Qed.
Lemma lem3835477 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3835478 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term465 _99546 _99547 f) = (term429 _99546 _99547 f).
Proof. exact (MK_COMB (@lem3835477 _99546) (@lem3835476 _99546 _99547 f)). Qed.
Lemma lem3835483 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3835484 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term466 _99546 _99547 f) = (term431 _99546 _99547 f).
Proof. exact (MK_COMB (@lem3835483) (@lem3835478 _99546 _99547 f)). Qed.
Lemma lem3835494 {A : Type'} (P : Prop) (Q : A -> Prop) : (term449 A P Q) = (term448 A P Q).
Proof. exact (EQ_MP (@lem18959 A P Q) (@lem18958 A P Q)). Qed.
Lemma lem3835495 {_99547 : Type'} (P : Prop) (Q : _99547 -> Prop) : (term449 _99547 P Q) = (term448 _99547 P Q).
Proof. exact (@lem3835494 _99547 P Q). Qed.
Lemma lem3835496 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term451 _99546 _99547 y g x) = (term450 _99546 _99547 y g x).
Proof. exact (@lem3835495 _99547 (term90 _99546 x y) (term412 _99546 _99547 y g x)). Qed.
Lemma lem3835497 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term452 _99546 _99547 y g x s) = (term410 _99546 _99547 y g x s).
Proof. exact (eq_refl (term452 _99546 _99547 y g x s)). Qed.
Lemma lem3835498 {_99546 : Type'} (x : _99546) (y : _99546) : (term414 _99546 x y) = (term414 _99546 x y).
Proof. exact (eq_refl (term414 _99546 x y)). Qed.
Lemma lem3835499 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term457 _99546 _99547 y g x s) = (term458 _99546 _99547 y g x s).
Proof. exact (MK_COMB (@lem3835498 _99546 x y) (@lem3835497 _99546 _99547 y g x s)). Qed.
Lemma lem3835500 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term459 _99546 _99547 y g x) = (term460 _99546 _99547 y g x).
Proof. exact (fun_ext (fun s : _99547 => @lem3835499 _99546 _99547 y g x s)). Qed.
Lemma lem3835501 {_99547 : Type'} : (@ex _99547) = (@ex _99547).
Proof. exact (eq_refl (@ex _99547)). Qed.
Lemma lem3835502 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term451 _99546 _99547 y g x) = (term461 _99546 _99547 y g x).
Proof. exact (MK_COMB (@lem3835501 _99547) (@lem3835500 _99546 _99547 y g x)). Qed.
Lemma lem3835503 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3835504 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term815 _99546 _99547 y g x) = (term816 _99546 _99547 y g x).
Proof. exact (MK_COMB (@lem3835503) (@lem3835502 _99546 _99547 y g x)). Qed.
Lemma lem3835505 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term452 _99546 _99547 y g x s) = (term410 _99546 _99547 y g x s).
Proof. exact (eq_refl (term452 _99546 _99547 y g x s)). Qed.
Lemma lem3835506 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term453 _99546 _99547 y g x) = (term412 _99546 _99547 y g x).
Proof. exact (fun_ext (fun s : _99547 => @lem3835505 _99546 _99547 y g x s)). Qed.
Lemma lem3835507 {_99547 : Type'} : (@ex _99547) = (@ex _99547).
Proof. exact (eq_refl (@ex _99547)). Qed.
Lemma lem3835508 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term454 _99546 _99547 y g x) = (term413 _99546 _99547 y g x).
Proof. exact (MK_COMB (@lem3835507 _99547) (@lem3835506 _99546 _99547 y g x)). Qed.
Lemma lem3835509 {_99546 : Type'} (x : _99546) (y : _99546) : (term414 _99546 x y) = (term414 _99546 x y).
Proof. exact (eq_refl (term414 _99546 x y)). Qed.
Lemma lem3835510 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term450 _99546 _99547 y g x) = (term416 _99546 _99547 y g x).
Proof. exact (MK_COMB (@lem3835509 _99546 x y) (@lem3835508 _99546 _99547 y g x)). Qed.
Lemma lem3835511 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : ((term451 _99546 _99547 y g x) = (term450 _99546 _99547 y g x)) = ((term461 _99546 _99547 y g x) = (term416 _99546 _99547 y g x)).
Proof. exact (MK_COMB (@lem3835504 _99546 _99547 y g x) (@lem3835510 _99546 _99547 y g x)). Qed.
Lemma lem3835512 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term461 _99546 _99547 y g x) = (term416 _99546 _99547 y g x).
Proof. exact (EQ_MP (@lem3835511 _99546 _99547 y g x) (@lem3835496 _99546 _99547 y g x)). Qed.
Lemma lem3835517 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) : (term462 _99546 _99547 g x) = (term422 _99546 _99547 g x).
Proof. exact (fun_ext (fun y : _99546 => @lem3835512 _99546 _99547 y g x)). Qed.
Lemma lem3835518 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3835519 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) : (term463 _99546 _99547 g x) = (term423 _99546 _99547 g x).
Proof. exact (MK_COMB (@lem3835518 _99546) (@lem3835517 _99546 _99547 g x)). Qed.
Lemma lem3835568 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) : (term464 _99546 _99547 g) = (term428 _99546 _99547 g).
Proof. exact (fun_ext (fun x : _99546 => @lem3835519 _99546 _99547 g x)). Qed.
Lemma lem3835569 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3835570 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) : (term465 _99546 _99547 g) = (term429 _99546 _99547 g).
Proof. exact (MK_COMB (@lem3835569 _99546) (@lem3835568 _99546 _99547 g)). Qed.
Lemma lem3835575 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term467 _99546 _99547 f g) = (term433 _99546 _99547 f g).
Proof. exact (MK_COMB (@lem3835484 _99546 _99547 f) (@lem3835570 _99546 _99547 g)). Qed.
Lemma lem3835576 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term436 _99546 _99547 s f g) = (term436 _99546 _99547 s f g).
Proof. exact (eq_refl (term436 _99546 _99547 s f g)). Qed.
Lemma lem3835577 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term814 _99546 _99547 s f g) = (term438 _99546 _99547 s f g).
Proof. exact (MK_COMB (@lem3835576 _99546 _99547 s f g) (@lem3835575 _99546 _99547 f g)). Qed.
Lemma lem3835579 {A : Type'} (P : Prop) (Q : A -> Prop) : (term448 A P Q) = (term449 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3835580 {_99547 : Type'} (P : Prop) (Q : _99547 -> Prop) : (term448 _99547 P Q) = (term449 _99547 P Q).
Proof. exact (@lem3835579 _99547 P Q). Qed.
Lemma lem3835581 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term450 _99546 _99547 y f x) = (term451 _99546 _99547 y f x).
Proof. exact (@lem3835580 _99547 (term90 _99546 x y) (term412 _99546 _99547 y f x)). Qed.
Lemma lem3835582 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term452 _99546 _99547 y f x s) = (term410 _99546 _99547 y f x s).
Proof. exact (eq_refl (term452 _99546 _99547 y f x s)). Qed.
Lemma lem3835583 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term453 _99546 _99547 y f x) = (term412 _99546 _99547 y f x).
Proof. exact (fun_ext (fun s : _99547 => @lem3835582 _99546 _99547 y f x s)). Qed.
Lemma lem3835584 {_99547 : Type'} : (@ex _99547) = (@ex _99547).
Proof. exact (eq_refl (@ex _99547)). Qed.
Lemma lem3835585 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term454 _99546 _99547 y f x) = (term413 _99546 _99547 y f x).
Proof. exact (MK_COMB (@lem3835584 _99547) (@lem3835583 _99546 _99547 y f x)). Qed.
Lemma lem3835586 {_99546 : Type'} (x : _99546) (y : _99546) : (term414 _99546 x y) = (term414 _99546 x y).
Proof. exact (eq_refl (term414 _99546 x y)). Qed.
Lemma lem3835587 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term450 _99546 _99547 y f x) = (term416 _99546 _99547 y f x).
Proof. exact (MK_COMB (@lem3835586 _99546 x y) (@lem3835585 _99546 _99547 y f x)). Qed.
Lemma lem3835588 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3835589 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term455 _99546 _99547 y f x) = (term456 _99546 _99547 y f x).
Proof. exact (MK_COMB (@lem3835588) (@lem3835587 _99546 _99547 y f x)). Qed.
Lemma lem3835590 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term452 _99546 _99547 y f x s) = (term410 _99546 _99547 y f x s).
Proof. exact (eq_refl (term452 _99546 _99547 y f x s)). Qed.
Lemma lem3835591 {_99546 : Type'} (x : _99546) (y : _99546) : (term414 _99546 x y) = (term414 _99546 x y).
Proof. exact (eq_refl (term414 _99546 x y)). Qed.
Lemma lem3835592 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term457 _99546 _99547 y f x s) = (term458 _99546 _99547 y f x s).
Proof. exact (MK_COMB (@lem3835591 _99546 x y) (@lem3835590 _99546 _99547 y f x s)). Qed.
Lemma lem3835593 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term459 _99546 _99547 y f x) = (term460 _99546 _99547 y f x).
Proof. exact (fun_ext (fun s : _99547 => @lem3835592 _99546 _99547 y f x s)). Qed.
Lemma lem3835594 {_99547 : Type'} : (@ex _99547) = (@ex _99547).
Proof. exact (eq_refl (@ex _99547)). Qed.
Lemma lem3835595 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term451 _99546 _99547 y f x) = (term461 _99546 _99547 y f x).
Proof. exact (MK_COMB (@lem3835594 _99547) (@lem3835593 _99546 _99547 y f x)). Qed.
Lemma lem3835596 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : ((term450 _99546 _99547 y f x) = (term451 _99546 _99547 y f x)) = ((term416 _99546 _99547 y f x) = (term461 _99546 _99547 y f x)).
Proof. exact (MK_COMB (@lem3835589 _99546 _99547 y f x) (@lem3835595 _99546 _99547 y f x)). Qed.
Lemma lem3835597 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term416 _99546 _99547 y f x) = (term461 _99546 _99547 y f x).
Proof. exact (EQ_MP (@lem3835596 _99546 _99547 y f x) (@lem3835581 _99546 _99547 y f x)). Qed.
Lemma lem3835598 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (term422 _99546 _99547 f x) = (term462 _99546 _99547 f x).
Proof. exact (fun_ext (fun y : _99546 => @lem3835597 _99546 _99547 y f x)). Qed.
Lemma lem3835599 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3835600 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (term423 _99546 _99547 f x) = (term463 _99546 _99547 f x).
Proof. exact (MK_COMB (@lem3835599 _99546) (@lem3835598 _99546 _99547 f x)). Qed.
Lemma lem3835601 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term428 _99546 _99547 f) = (term464 _99546 _99547 f).
Proof. exact (fun_ext (fun x : _99546 => @lem3835600 _99546 _99547 f x)). Qed.
Lemma lem3835602 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3835603 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term429 _99546 _99547 f) = (term465 _99546 _99547 f).
Proof. exact (MK_COMB (@lem3835602 _99546) (@lem3835601 _99546 _99547 f)). Qed.
Lemma lem3835604 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3835605 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term431 _99546 _99547 f) = (term466 _99546 _99547 f).
Proof. exact (MK_COMB (@lem3835604) (@lem3835603 _99546 _99547 f)). Qed.
Lemma lem3835607 {A : Type'} (P : Prop) (Q : A -> Prop) : (term448 A P Q) = (term449 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3835608 {_99547 : Type'} (P : Prop) (Q : _99547 -> Prop) : (term448 _99547 P Q) = (term449 _99547 P Q).
Proof. exact (@lem3835607 _99547 P Q). Qed.
Lemma lem3835609 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term450 _99546 _99547 y g x) = (term451 _99546 _99547 y g x).
Proof. exact (@lem3835608 _99547 (term90 _99546 x y) (term412 _99546 _99547 y g x)). Qed.
Lemma lem3835610 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term452 _99546 _99547 y g x s) = (term410 _99546 _99547 y g x s).
Proof. exact (eq_refl (term452 _99546 _99547 y g x s)). Qed.
Lemma lem3835611 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term453 _99546 _99547 y g x) = (term412 _99546 _99547 y g x).
Proof. exact (fun_ext (fun s : _99547 => @lem3835610 _99546 _99547 y g x s)). Qed.
Lemma lem3835612 {_99547 : Type'} : (@ex _99547) = (@ex _99547).
Proof. exact (eq_refl (@ex _99547)). Qed.
Lemma lem3835613 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term454 _99546 _99547 y g x) = (term413 _99546 _99547 y g x).
Proof. exact (MK_COMB (@lem3835612 _99547) (@lem3835611 _99546 _99547 y g x)). Qed.
Lemma lem3835614 {_99546 : Type'} (x : _99546) (y : _99546) : (term414 _99546 x y) = (term414 _99546 x y).
Proof. exact (eq_refl (term414 _99546 x y)). Qed.
Lemma lem3835615 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term450 _99546 _99547 y g x) = (term416 _99546 _99547 y g x).
Proof. exact (MK_COMB (@lem3835614 _99546 x y) (@lem3835613 _99546 _99547 y g x)). Qed.
Lemma lem3835616 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3835617 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term455 _99546 _99547 y g x) = (term456 _99546 _99547 y g x).
Proof. exact (MK_COMB (@lem3835616) (@lem3835615 _99546 _99547 y g x)). Qed.
Lemma lem3835618 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term452 _99546 _99547 y g x s) = (term410 _99546 _99547 y g x s).
Proof. exact (eq_refl (term452 _99546 _99547 y g x s)). Qed.
Lemma lem3835619 {_99546 : Type'} (x : _99546) (y : _99546) : (term414 _99546 x y) = (term414 _99546 x y).
Proof. exact (eq_refl (term414 _99546 x y)). Qed.
Lemma lem3835620 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term457 _99546 _99547 y g x s) = (term458 _99546 _99547 y g x s).
Proof. exact (MK_COMB (@lem3835619 _99546 x y) (@lem3835618 _99546 _99547 y g x s)). Qed.
Lemma lem3835621 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term459 _99546 _99547 y g x) = (term460 _99546 _99547 y g x).
Proof. exact (fun_ext (fun s : _99547 => @lem3835620 _99546 _99547 y g x s)). Qed.
Lemma lem3835622 {_99547 : Type'} : (@ex _99547) = (@ex _99547).
Proof. exact (eq_refl (@ex _99547)). Qed.
Lemma lem3835623 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term451 _99546 _99547 y g x) = (term461 _99546 _99547 y g x).
Proof. exact (MK_COMB (@lem3835622 _99547) (@lem3835621 _99546 _99547 y g x)). Qed.
Lemma lem3835624 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : ((term450 _99546 _99547 y g x) = (term451 _99546 _99547 y g x)) = ((term416 _99546 _99547 y g x) = (term461 _99546 _99547 y g x)).
Proof. exact (MK_COMB (@lem3835617 _99546 _99547 y g x) (@lem3835623 _99546 _99547 y g x)). Qed.
Lemma lem3835625 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term416 _99546 _99547 y g x) = (term461 _99546 _99547 y g x).
Proof. exact (EQ_MP (@lem3835624 _99546 _99547 y g x) (@lem3835609 _99546 _99547 y g x)). Qed.
Lemma lem3835626 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) : (term422 _99546 _99547 g x) = (term462 _99546 _99547 g x).
Proof. exact (fun_ext (fun y : _99546 => @lem3835625 _99546 _99547 y g x)). Qed.
Lemma lem3835627 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3835628 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) : (term423 _99546 _99547 g x) = (term463 _99546 _99547 g x).
Proof. exact (MK_COMB (@lem3835627 _99546) (@lem3835626 _99546 _99547 g x)). Qed.
Lemma lem3835629 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) : (term428 _99546 _99547 g) = (term464 _99546 _99547 g).
Proof. exact (fun_ext (fun x : _99546 => @lem3835628 _99546 _99547 g x)). Qed.
Lemma lem3835630 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3835631 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) : (term429 _99546 _99547 g) = (term465 _99546 _99547 g).
Proof. exact (MK_COMB (@lem3835630 _99546) (@lem3835629 _99546 _99547 g)). Qed.
Lemma lem3835632 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term433 _99546 _99547 f g) = (term467 _99546 _99547 f g).
Proof. exact (MK_COMB (@lem3835605 _99546 _99547 f) (@lem3835631 _99546 _99547 g)). Qed.
Lemma lem3835634 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term468 A P Q) = (term469 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3835635 {_99546 : Type'} (P : _99546 -> Prop) (Q : _99546 -> Prop) : (term468 _99546 P Q) = (term469 _99546 P Q).
Proof. exact (@lem3835634 _99546 P Q). Qed.
Lemma lem3835636 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term470 _99546 _99547 f g) = (term471 _99546 _99547 f g).
Proof. exact (@lem3835635 _99546 (term464 _99546 _99547 f) (term464 _99546 _99547 g)). Qed.
Lemma lem3835637 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (term472 _99546 _99547 f x) = (term463 _99546 _99547 f x).
Proof. exact (eq_refl (term472 _99546 _99547 f x)). Qed.
Lemma lem3835638 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term473 _99546 _99547 f) = (term464 _99546 _99547 f).
Proof. exact (fun_ext (fun x : _99546 => @lem3835637 _99546 _99547 f x)). Qed.
Lemma lem3835639 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3835640 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term474 _99546 _99547 f) = (term465 _99546 _99547 f).
Proof. exact (MK_COMB (@lem3835639 _99546) (@lem3835638 _99546 _99547 f)). Qed.
Lemma lem3835641 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3835642 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term475 _99546 _99547 f) = (term466 _99546 _99547 f).
Proof. exact (MK_COMB (@lem3835641) (@lem3835640 _99546 _99547 f)). Qed.
Lemma lem3835643 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) : (term472 _99546 _99547 g x) = (term463 _99546 _99547 g x).
Proof. exact (eq_refl (term472 _99546 _99547 g x)). Qed.
Lemma lem3835644 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) : (term473 _99546 _99547 g) = (term464 _99546 _99547 g).
Proof. exact (fun_ext (fun x : _99546 => @lem3835643 _99546 _99547 g x)). Qed.
Lemma lem3835645 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3835646 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) : (term474 _99546 _99547 g) = (term465 _99546 _99547 g).
Proof. exact (MK_COMB (@lem3835645 _99546) (@lem3835644 _99546 _99547 g)). Qed.
Lemma lem3835647 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term470 _99546 _99547 f g) = (term467 _99546 _99547 f g).
Proof. exact (MK_COMB (@lem3835642 _99546 _99547 f) (@lem3835646 _99546 _99547 g)). Qed.
Lemma lem3835648 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3835649 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term476 _99546 _99547 f g) = (term477 _99546 _99547 f g).
Proof. exact (MK_COMB (@lem3835648) (@lem3835647 _99546 _99547 f g)). Qed.
Lemma lem3835650 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (term472 _99546 _99547 f x) = (term463 _99546 _99547 f x).
Proof. exact (eq_refl (term472 _99546 _99547 f x)). Qed.
Lemma lem3835651 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3835652 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (term478 _99546 _99547 f x) = (term479 _99546 _99547 f x).
Proof. exact (MK_COMB (@lem3835651) (@lem3835650 _99546 _99547 f x)). Qed.
Lemma lem3835653 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) : (term472 _99546 _99547 g x) = (term463 _99546 _99547 g x).
Proof. exact (eq_refl (term472 _99546 _99547 g x)). Qed.
Lemma lem3835654 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term480 _99546 _99547 f g x) = (term481 _99546 _99547 f g x).
Proof. exact (MK_COMB (@lem3835652 _99546 _99547 f x) (@lem3835653 _99546 _99547 g x)). Qed.
Lemma lem3835655 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term482 _99546 _99547 f g) = (term483 _99546 _99547 f g).
Proof. exact (fun_ext (fun x : _99546 => @lem3835654 _99546 _99547 f g x)). Qed.
Lemma lem3835656 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3835657 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term471 _99546 _99547 f g) = (term484 _99546 _99547 f g).
Proof. exact (MK_COMB (@lem3835656 _99546) (@lem3835655 _99546 _99547 f g)). Qed.
Lemma lem3835658 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : ((term470 _99546 _99547 f g) = (term471 _99546 _99547 f g)) = ((term467 _99546 _99547 f g) = (term484 _99546 _99547 f g)).
Proof. exact (MK_COMB (@lem3835649 _99546 _99547 f g) (@lem3835657 _99546 _99547 f g)). Qed.
Lemma lem3835659 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term467 _99546 _99547 f g) = (term484 _99546 _99547 f g).
Proof. exact (EQ_MP (@lem3835658 _99546 _99547 f g) (@lem3835636 _99546 _99547 f g)). Qed.
Lemma lem3835661 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term468 A P Q) = (term469 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3835662 {_99546 : Type'} (P : _99546 -> Prop) (Q : _99546 -> Prop) : (term468 _99546 P Q) = (term469 _99546 P Q).
Proof. exact (@lem3835661 _99546 P Q). Qed.
Lemma lem3835663 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term485 _99546 _99547 f g x) = (term486 _99546 _99547 f g x).
Proof. exact (@lem3835662 _99546 (term462 _99546 _99547 f x) (term462 _99546 _99547 g x)). Qed.
Lemma lem3835664 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term487 _99546 _99547 f x y) = (term461 _99546 _99547 y f x).
Proof. exact (eq_refl (term487 _99546 _99547 f x y)). Qed.
Lemma lem3835665 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (term488 _99546 _99547 f x) = (term462 _99546 _99547 f x).
Proof. exact (fun_ext (fun y : _99546 => @lem3835664 _99546 _99547 y f x)). Qed.
Lemma lem3835666 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3835667 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (term489 _99546 _99547 f x) = (term463 _99546 _99547 f x).
Proof. exact (MK_COMB (@lem3835666 _99546) (@lem3835665 _99546 _99547 f x)). Qed.
Lemma lem3835668 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3835669 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (term490 _99546 _99547 f x) = (term479 _99546 _99547 f x).
Proof. exact (MK_COMB (@lem3835668) (@lem3835667 _99546 _99547 f x)). Qed.
Lemma lem3835670 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term487 _99546 _99547 g x y) = (term461 _99546 _99547 y g x).
Proof. exact (eq_refl (term487 _99546 _99547 g x y)). Qed.
Lemma lem3835671 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) : (term488 _99546 _99547 g x) = (term462 _99546 _99547 g x).
Proof. exact (fun_ext (fun y : _99546 => @lem3835670 _99546 _99547 y g x)). Qed.
Lemma lem3835672 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3835673 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) : (term489 _99546 _99547 g x) = (term463 _99546 _99547 g x).
Proof. exact (MK_COMB (@lem3835672 _99546) (@lem3835671 _99546 _99547 g x)). Qed.
Lemma lem3835674 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term485 _99546 _99547 f g x) = (term481 _99546 _99547 f g x).
Proof. exact (MK_COMB (@lem3835669 _99546 _99547 f x) (@lem3835673 _99546 _99547 g x)). Qed.
Lemma lem3835675 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3835676 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term491 _99546 _99547 f g x) = (term492 _99546 _99547 f g x).
Proof. exact (MK_COMB (@lem3835675) (@lem3835674 _99546 _99547 f g x)). Qed.
Lemma lem3835677 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term487 _99546 _99547 f x y) = (term461 _99546 _99547 y f x).
Proof. exact (eq_refl (term487 _99546 _99547 f x y)). Qed.
Lemma lem3835678 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3835679 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term493 _99546 _99547 f x y) = (term494 _99546 _99547 y f x).
Proof. exact (MK_COMB (@lem3835678) (@lem3835677 _99546 _99547 y f x)). Qed.
Lemma lem3835680 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term487 _99546 _99547 g x y) = (term461 _99546 _99547 y g x).
Proof. exact (eq_refl (term487 _99546 _99547 g x y)). Qed.
Lemma lem3835681 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term495 _99546 _99547 f g x y) = (term496 _99546 _99547 f y g x).
Proof. exact (MK_COMB (@lem3835679 _99546 _99547 y f x) (@lem3835680 _99546 _99547 y g x)). Qed.
Lemma lem3835682 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term497 _99546 _99547 f g x) = (term498 _99546 _99547 f g x).
Proof. exact (fun_ext (fun y : _99546 => @lem3835681 _99546 _99547 f y g x)). Qed.
Lemma lem3835683 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3835684 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term486 _99546 _99547 f g x) = (term499 _99546 _99547 f g x).
Proof. exact (MK_COMB (@lem3835683 _99546) (@lem3835682 _99546 _99547 f g x)). Qed.
Lemma lem3835685 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : ((term485 _99546 _99547 f g x) = (term486 _99546 _99547 f g x)) = ((term481 _99546 _99547 f g x) = (term499 _99546 _99547 f g x)).
Proof. exact (MK_COMB (@lem3835676 _99546 _99547 f g x) (@lem3835684 _99546 _99547 f g x)). Qed.
Lemma lem3835686 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term481 _99546 _99547 f g x) = (term499 _99546 _99547 f g x).
Proof. exact (EQ_MP (@lem3835685 _99546 _99547 f g x) (@lem3835663 _99546 _99547 f g x)). Qed.
Lemma lem3835688 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term468 A P Q) = (term469 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3835689 {_99547 : Type'} (P : _99547 -> Prop) (Q : _99547 -> Prop) : (term468 _99547 P Q) = (term469 _99547 P Q).
Proof. exact (@lem3835688 _99547 P Q). Qed.
Lemma lem3835690 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term500 _99546 _99547 f y g x) = (term501 _99546 _99547 f y g x).
Proof. exact (@lem3835689 _99547 (term460 _99546 _99547 y f x) (term460 _99546 _99547 y g x)). Qed.
Lemma lem3835691 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term502 _99546 _99547 y f x s) = (term458 _99546 _99547 y f x s).
Proof. exact (eq_refl (term502 _99546 _99547 y f x s)). Qed.
Lemma lem3835692 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term503 _99546 _99547 y f x) = (term460 _99546 _99547 y f x).
Proof. exact (fun_ext (fun s : _99547 => @lem3835691 _99546 _99547 y f x s)). Qed.
Lemma lem3835693 {_99547 : Type'} : (@ex _99547) = (@ex _99547).
Proof. exact (eq_refl (@ex _99547)). Qed.
Lemma lem3835694 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term504 _99546 _99547 y f x) = (term461 _99546 _99547 y f x).
Proof. exact (MK_COMB (@lem3835693 _99547) (@lem3835692 _99546 _99547 y f x)). Qed.
Lemma lem3835695 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3835696 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term505 _99546 _99547 y f x) = (term494 _99546 _99547 y f x).
Proof. exact (MK_COMB (@lem3835695) (@lem3835694 _99546 _99547 y f x)). Qed.
Lemma lem3835697 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term502 _99546 _99547 y g x s) = (term458 _99546 _99547 y g x s).
Proof. exact (eq_refl (term502 _99546 _99547 y g x s)). Qed.
Lemma lem3835698 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term503 _99546 _99547 y g x) = (term460 _99546 _99547 y g x).
Proof. exact (fun_ext (fun s : _99547 => @lem3835697 _99546 _99547 y g x s)). Qed.
Lemma lem3835699 {_99547 : Type'} : (@ex _99547) = (@ex _99547).
Proof. exact (eq_refl (@ex _99547)). Qed.
Lemma lem3835700 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term504 _99546 _99547 y g x) = (term461 _99546 _99547 y g x).
Proof. exact (MK_COMB (@lem3835699 _99547) (@lem3835698 _99546 _99547 y g x)). Qed.
Lemma lem3835701 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term500 _99546 _99547 f y g x) = (term496 _99546 _99547 f y g x).
Proof. exact (MK_COMB (@lem3835696 _99546 _99547 y f x) (@lem3835700 _99546 _99547 y g x)). Qed.
Lemma lem3835702 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3835703 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term506 _99546 _99547 f y g x) = (term507 _99546 _99547 f y g x).
Proof. exact (MK_COMB (@lem3835702) (@lem3835701 _99546 _99547 f y g x)). Qed.
Lemma lem3835704 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term502 _99546 _99547 y f x s) = (term458 _99546 _99547 y f x s).
Proof. exact (eq_refl (term502 _99546 _99547 y f x s)). Qed.
Lemma lem3835705 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3835706 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term508 _99546 _99547 y f x s) = (term509 _99546 _99547 y f x s).
Proof. exact (MK_COMB (@lem3835705) (@lem3835704 _99546 _99547 y f x s)). Qed.
Lemma lem3835707 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term502 _99546 _99547 y g x s) = (term458 _99546 _99547 y g x s).
Proof. exact (eq_refl (term502 _99546 _99547 y g x s)). Qed.
Lemma lem3835708 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term510 _99546 _99547 f y g x s) = (term511 _99546 _99547 f y g x s).
Proof. exact (MK_COMB (@lem3835706 _99546 _99547 y f x s) (@lem3835707 _99546 _99547 y g x s)). Qed.
Lemma lem3835709 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term512 _99546 _99547 f y g x) = (term513 _99546 _99547 f y g x).
Proof. exact (fun_ext (fun s : _99547 => @lem3835708 _99546 _99547 f y g x s)). Qed.
Lemma lem3835710 {_99547 : Type'} : (@ex _99547) = (@ex _99547).
Proof. exact (eq_refl (@ex _99547)). Qed.
Lemma lem3835711 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term501 _99546 _99547 f y g x) = (term514 _99546 _99547 f y g x).
Proof. exact (MK_COMB (@lem3835710 _99547) (@lem3835709 _99546 _99547 f y g x)). Qed.
Lemma lem3835712 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : ((term500 _99546 _99547 f y g x) = (term501 _99546 _99547 f y g x)) = ((term496 _99546 _99547 f y g x) = (term514 _99546 _99547 f y g x)).
Proof. exact (MK_COMB (@lem3835703 _99546 _99547 f y g x) (@lem3835711 _99546 _99547 f y g x)). Qed.
Lemma lem3835713 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term496 _99546 _99547 f y g x) = (term514 _99546 _99547 f y g x).
Proof. exact (EQ_MP (@lem3835712 _99546 _99547 f y g x) (@lem3835690 _99546 _99547 f y g x)). Qed.
Lemma lem3835714 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term498 _99546 _99547 f g x) = (term515 _99546 _99547 f g x).
Proof. exact (fun_ext (fun y : _99546 => @lem3835713 _99546 _99547 f y g x)). Qed.
Lemma lem3835715 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3835716 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term499 _99546 _99547 f g x) = (term516 _99546 _99547 f g x).
Proof. exact (MK_COMB (@lem3835715 _99546) (@lem3835714 _99546 _99547 f g x)). Qed.
Lemma lem3835717 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term481 _99546 _99547 f g x) = (term516 _99546 _99547 f g x).
Proof. exact (TRANS (@lem3835686 _99546 _99547 f g x) (@lem3835716 _99546 _99547 f g x)). Qed.
Lemma lem3835718 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term483 _99546 _99547 f g) = (term517 _99546 _99547 f g).
Proof. exact (fun_ext (fun x : _99546 => @lem3835717 _99546 _99547 f g x)). Qed.
Lemma lem3835719 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3835720 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term484 _99546 _99547 f g) = (term518 _99546 _99547 f g).
Proof. exact (MK_COMB (@lem3835719 _99546) (@lem3835718 _99546 _99547 f g)). Qed.
Lemma lem3835721 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term467 _99546 _99547 f g) = (term518 _99546 _99547 f g).
Proof. exact (TRANS (@lem3835659 _99546 _99547 f g) (@lem3835720 _99546 _99547 f g)). Qed.
Lemma lem3835722 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term433 _99546 _99547 f g) = (term518 _99546 _99547 f g).
Proof. exact (TRANS (@lem3835632 _99546 _99547 f g) (@lem3835721 _99546 _99547 f g)). Qed.
Lemma lem3835723 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term436 _99546 _99547 s f g) = (term436 _99546 _99547 s f g).
Proof. exact (eq_refl (term436 _99546 _99547 s f g)). Qed.
Lemma lem3835724 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term438 _99546 _99547 s f g) = (term519 _99546 _99547 s f g).
Proof. exact (MK_COMB (@lem3835723 _99546 _99547 s f g) (@lem3835722 _99546 _99547 f g)). Qed.
Lemma lem3835726 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term468 A P Q) = (term469 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3835727 {_99546 : Type'} (P : _99546 -> Prop) (Q : _99546 -> Prop) : (term468 _99546 P Q) = (term469 _99546 P Q).
Proof. exact (@lem3835726 _99546 P Q). Qed.
Lemma lem3835728 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term520 _99546 _99547 s f g) = (term521 _99546 _99547 s f g).
Proof. exact (@lem3835727 _99546 (term405 _99546 _99547 s f g) (term517 _99546 _99547 f g)). Qed.
Lemma lem3835729 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term522 _99546 _99547 s f g x) = (term397 _99546 _99547 s f g x).
Proof. exact (eq_refl (term522 _99546 _99547 s f g x)). Qed.
Lemma lem3835730 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term523 _99546 _99547 s f g) = (term405 _99546 _99547 s f g).
Proof. exact (fun_ext (fun x : _99546 => @lem3835729 _99546 _99547 s f g x)). Qed.
Lemma lem3835731 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3835732 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term524 _99546 _99547 s f g) = (term406 _99546 _99547 s f g).
Proof. exact (MK_COMB (@lem3835731 _99546) (@lem3835730 _99546 _99547 s f g)). Qed.
Lemma lem3835733 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3835734 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term525 _99546 _99547 s f g) = (term436 _99546 _99547 s f g).
Proof. exact (MK_COMB (@lem3835733) (@lem3835732 _99546 _99547 s f g)). Qed.
Lemma lem3835735 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term526 _99546 _99547 f g x) = (term516 _99546 _99547 f g x).
Proof. exact (eq_refl (term526 _99546 _99547 f g x)). Qed.
Lemma lem3835736 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term527 _99546 _99547 f g) = (term517 _99546 _99547 f g).
Proof. exact (fun_ext (fun x : _99546 => @lem3835735 _99546 _99547 f g x)). Qed.
Lemma lem3835737 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3835738 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term528 _99546 _99547 f g) = (term518 _99546 _99547 f g).
Proof. exact (MK_COMB (@lem3835737 _99546) (@lem3835736 _99546 _99547 f g)). Qed.
Lemma lem3835739 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term520 _99546 _99547 s f g) = (term519 _99546 _99547 s f g).
Proof. exact (MK_COMB (@lem3835734 _99546 _99547 s f g) (@lem3835738 _99546 _99547 f g)). Qed.
Lemma lem3835740 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3835741 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term529 _99546 _99547 s f g) = (term530 _99546 _99547 s f g).
Proof. exact (MK_COMB (@lem3835740) (@lem3835739 _99546 _99547 s f g)). Qed.
Lemma lem3835742 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term522 _99546 _99547 s f g x) = (term397 _99546 _99547 s f g x).
Proof. exact (eq_refl (term522 _99546 _99547 s f g x)). Qed.
Lemma lem3835743 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3835744 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term531 _99546 _99547 s f g x) = (term532 _99546 _99547 s f g x).
Proof. exact (MK_COMB (@lem3835743) (@lem3835742 _99546 _99547 s f g x)). Qed.
Lemma lem3835745 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term526 _99546 _99547 f g x) = (term516 _99546 _99547 f g x).
Proof. exact (eq_refl (term526 _99546 _99547 f g x)). Qed.
Lemma lem3835746 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term533 _99546 _99547 s f g x) = (term534 _99546 _99547 s f g x).
Proof. exact (MK_COMB (@lem3835744 _99546 _99547 s f g x) (@lem3835745 _99546 _99547 f g x)). Qed.
Lemma lem3835747 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term535 _99546 _99547 s f g) = (term536 _99546 _99547 s f g).
Proof. exact (fun_ext (fun x : _99546 => @lem3835746 _99546 _99547 s f g x)). Qed.
Lemma lem3835748 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3835749 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term521 _99546 _99547 s f g) = (term537 _99546 _99547 s f g).
Proof. exact (MK_COMB (@lem3835748 _99546) (@lem3835747 _99546 _99547 s f g)). Qed.
Lemma lem3835750 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : ((term520 _99546 _99547 s f g) = (term521 _99546 _99547 s f g)) = ((term519 _99546 _99547 s f g) = (term537 _99546 _99547 s f g)).
Proof. exact (MK_COMB (@lem3835741 _99546 _99547 s f g) (@lem3835749 _99546 _99547 s f g)). Qed.
Lemma lem3835751 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term519 _99546 _99547 s f g) = (term537 _99546 _99547 s f g).
Proof. exact (EQ_MP (@lem3835750 _99546 _99547 s f g) (@lem3835728 _99546 _99547 s f g)). Qed.
Lemma lem3835753 {A : Type'} (P : Prop) (Q : A -> Prop) : (term538 A P Q) = (term539 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3835754 {_99546 : Type'} (P : Prop) (Q : _99546 -> Prop) : (term538 _99546 P Q) = (term539 _99546 P Q).
Proof. exact (@lem3835753 _99546 P Q). Qed.
Lemma lem3835755 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term540 _99546 _99547 s f g x) = (term541 _99546 _99547 s f g x).
Proof. exact (@lem3835754 _99546 (term397 _99546 _99547 s f g x) (term515 _99546 _99547 f g x)). Qed.
Lemma lem3835756 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term542 _99546 _99547 f g x y) = (term514 _99546 _99547 f y g x).
Proof. exact (eq_refl (term542 _99546 _99547 f g x y)). Qed.
Lemma lem3835757 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term543 _99546 _99547 f g x) = (term515 _99546 _99547 f g x).
Proof. exact (fun_ext (fun y : _99546 => @lem3835756 _99546 _99547 f y g x)). Qed.
Lemma lem3835758 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3835759 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term544 _99546 _99547 f g x) = (term516 _99546 _99547 f g x).
Proof. exact (MK_COMB (@lem3835758 _99546) (@lem3835757 _99546 _99547 f g x)). Qed.
Lemma lem3835760 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term532 _99546 _99547 s f g x) = (term532 _99546 _99547 s f g x).
Proof. exact (eq_refl (term532 _99546 _99547 s f g x)). Qed.
Lemma lem3835761 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term540 _99546 _99547 s f g x) = (term534 _99546 _99547 s f g x).
Proof. exact (MK_COMB (@lem3835760 _99546 _99547 s f g x) (@lem3835759 _99546 _99547 f g x)). Qed.
Lemma lem3835762 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3835763 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term545 _99546 _99547 s f g x) = (term546 _99546 _99547 s f g x).
Proof. exact (MK_COMB (@lem3835762) (@lem3835761 _99546 _99547 s f g x)). Qed.
Lemma lem3835764 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term542 _99546 _99547 f g x y) = (term514 _99546 _99547 f y g x).
Proof. exact (eq_refl (term542 _99546 _99547 f g x y)). Qed.
Lemma lem3835765 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term532 _99546 _99547 s f g x) = (term532 _99546 _99547 s f g x).
Proof. exact (eq_refl (term532 _99546 _99547 s f g x)). Qed.
Lemma lem3835766 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term547 _99546 _99547 s f g x y) = (term548 _99546 _99547 s f y g x).
Proof. exact (MK_COMB (@lem3835765 _99546 _99547 s f g x) (@lem3835764 _99546 _99547 f y g x)). Qed.
Lemma lem3835767 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term549 _99546 _99547 s f g x) = (term550 _99546 _99547 s f g x).
Proof. exact (fun_ext (fun y : _99546 => @lem3835766 _99546 _99547 s f y g x)). Qed.
Lemma lem3835768 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3835769 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term541 _99546 _99547 s f g x) = (term551 _99546 _99547 s f g x).
Proof. exact (MK_COMB (@lem3835768 _99546) (@lem3835767 _99546 _99547 s f g x)). Qed.
Lemma lem3835770 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : ((term540 _99546 _99547 s f g x) = (term541 _99546 _99547 s f g x)) = ((term534 _99546 _99547 s f g x) = (term551 _99546 _99547 s f g x)).
Proof. exact (MK_COMB (@lem3835763 _99546 _99547 s f g x) (@lem3835769 _99546 _99547 s f g x)). Qed.
Lemma lem3835771 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term534 _99546 _99547 s f g x) = (term551 _99546 _99547 s f g x).
Proof. exact (EQ_MP (@lem3835770 _99546 _99547 s f g x) (@lem3835755 _99546 _99547 s f g x)). Qed.
Lemma lem3835773 {A : Type'} (P : Prop) (Q : A -> Prop) : (term538 A P Q) = (term539 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3835774 {_99547 : Type'} (P : Prop) (Q : _99547 -> Prop) : (term538 _99547 P Q) = (term539 _99547 P Q).
Proof. exact (@lem3835773 _99547 P Q). Qed.
Lemma lem3835775 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term552 _99546 _99547 s f y g x) = (term553 _99546 _99547 s f y g x).
Proof. exact (@lem3835774 _99547 (term397 _99546 _99547 s f g x) (term513 _99546 _99547 f y g x)). Qed.
Lemma lem3835776 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term554 _99546 _99547 f y g x s) = (term511 _99546 _99547 f y g x s).
Proof. exact (eq_refl (term554 _99546 _99547 f y g x s)). Qed.
Lemma lem3835777 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term555 _99546 _99547 f y g x) = (term513 _99546 _99547 f y g x).
Proof. exact (fun_ext (fun s : _99547 => @lem3835776 _99546 _99547 f y g x s)). Qed.
Lemma lem3835778 {_99547 : Type'} : (@ex _99547) = (@ex _99547).
Proof. exact (eq_refl (@ex _99547)). Qed.
Lemma lem3835779 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term556 _99546 _99547 f y g x) = (term514 _99546 _99547 f y g x).
Proof. exact (MK_COMB (@lem3835778 _99547) (@lem3835777 _99546 _99547 f y g x)). Qed.
Lemma lem3835780 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term532 _99546 _99547 s f g x) = (term532 _99546 _99547 s f g x).
Proof. exact (eq_refl (term532 _99546 _99547 s f g x)). Qed.
Lemma lem3835781 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term552 _99546 _99547 s f y g x) = (term548 _99546 _99547 s f y g x).
Proof. exact (MK_COMB (@lem3835780 _99546 _99547 s f g x) (@lem3835779 _99546 _99547 f y g x)). Qed.
Lemma lem3835782 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3835783 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term557 _99546 _99547 s f y g x) = (term558 _99546 _99547 s f y g x).
Proof. exact (MK_COMB (@lem3835782) (@lem3835781 _99546 _99547 s f y g x)). Qed.
Lemma lem3835784 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term554 _99546 _99547 f y g x s) = (term511 _99546 _99547 f y g x s).
Proof. exact (eq_refl (term554 _99546 _99547 f y g x s)). Qed.
Lemma lem3835785 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term532 _99546 _99547 s f g x) = (term532 _99546 _99547 s f g x).
Proof. exact (eq_refl (term532 _99546 _99547 s f g x)). Qed.
Lemma lem3835786 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s' : _99547) : (term559 _99546 _99547 s f y g x s') = (term560 _99546 _99547 s f y g x s').
Proof. exact (MK_COMB (@lem3835785 _99546 _99547 s f g x) (@lem3835784 _99546 _99547 f y g x s')). Qed.
Lemma lem3835787 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term561 _99546 _99547 s f y g x) = (term562 _99546 _99547 s f y g x).
Proof. exact (fun_ext (fun s' : _99547 => @lem3835786 _99546 _99547 s f y g x s')). Qed.
Lemma lem3835788 {_99547 : Type'} : (@ex _99547) = (@ex _99547).
Proof. exact (eq_refl (@ex _99547)). Qed.
Lemma lem3835789 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term553 _99546 _99547 s f y g x) = (term563 _99546 _99547 s f y g x).
Proof. exact (MK_COMB (@lem3835788 _99547) (@lem3835787 _99546 _99547 s f y g x)). Qed.
Lemma lem3835790 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : ((term552 _99546 _99547 s f y g x) = (term553 _99546 _99547 s f y g x)) = ((term548 _99546 _99547 s f y g x) = (term563 _99546 _99547 s f y g x)).
Proof. exact (MK_COMB (@lem3835783 _99546 _99547 s f y g x) (@lem3835789 _99546 _99547 s f y g x)). Qed.
Lemma lem3835791 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term548 _99546 _99547 s f y g x) = (term563 _99546 _99547 s f y g x).
Proof. exact (EQ_MP (@lem3835790 _99546 _99547 s f y g x) (@lem3835775 _99546 _99547 s f y g x)). Qed.
Lemma lem3835792 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term550 _99546 _99547 s f g x) = (term564 _99546 _99547 s f g x).
Proof. exact (fun_ext (fun y : _99546 => @lem3835791 _99546 _99547 s f y g x)). Qed.
Lemma lem3835793 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3835794 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term551 _99546 _99547 s f g x) = (term565 _99546 _99547 s f g x).
Proof. exact (MK_COMB (@lem3835793 _99546) (@lem3835792 _99546 _99547 s f g x)). Qed.
Lemma lem3835795 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : (term534 _99546 _99547 s f g x) = (term565 _99546 _99547 s f g x).
Proof. exact (TRANS (@lem3835771 _99546 _99547 s f g x) (@lem3835794 _99546 _99547 s f g x)). Qed.
Lemma lem3835796 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term536 _99546 _99547 s f g) = (term566 _99546 _99547 s f g).
Proof. exact (fun_ext (fun x : _99546 => @lem3835795 _99546 _99547 s f g x)). Qed.
Lemma lem3835797 {_99546 : Type'} : (@ex _99546) = (@ex _99546).
Proof. exact (eq_refl (@ex _99546)). Qed.
Lemma lem3835798 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term537 _99546 _99547 s f g) = (term567 _99546 _99547 s f g).
Proof. exact (MK_COMB (@lem3835797 _99546) (@lem3835796 _99546 _99547 s f g)). Qed.
Lemma lem3835799 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term519 _99546 _99547 s f g) = (term567 _99546 _99547 s f g).
Proof. exact (TRANS (@lem3835751 _99546 _99547 s f g) (@lem3835798 _99546 _99547 s f g)). Qed.
Lemma lem3835800 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term438 _99546 _99547 s f g) = (term567 _99546 _99547 s f g).
Proof. exact (TRANS (@lem3835724 _99546 _99547 s f g) (@lem3835799 _99546 _99547 s f g)). Qed.
Lemma lem3835801 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term814 _99546 _99547 s f g) = (term567 _99546 _99547 s f g).
Proof. exact (TRANS (@lem3835577 _99546 _99547 s f g) (@lem3835800 _99546 _99547 s f g)). Qed.
Lemma lem3835802 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term355 _99546 _99547 s f g) = (term567 _99546 _99547 s f g).
Proof. exact (TRANS (@lem3835344 _99546 _99547 s f g) (@lem3835801 _99546 _99547 s f g)). Qed.
Lemma lem3835803 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term355 _99546 _99547 s f g) : term567 _99546 _99547 s f g.
Proof. exact (EQ_MP (@lem3835802 _99546 _99547 s f g) (@lem3834156 _99546 _99547 s f g h1)). Qed.
Lemma lem3835804 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x' : _99546) (h1 : term565 _99546 _99547 s f g x') : term565 _99546 _99547 s f g x'.
Proof. exact (h1). Qed.
Lemma lem3835805 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x' : _99546) (h1 : term563 _99546 _99547 s f y g x') : term563 _99546 _99547 s f y g x'.
Proof. exact (h1). Qed.
Lemma lem3835806 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x' : _99546) (s' : _99547) (h1 : term560 _99546 _99547 s f y g x' s') : term560 _99546 _99547 s f y g x' s'.
Proof. exact (h1). Qed.
Lemma lem3835807 {_99546 _99547 : Type'} (x'' : type427 _99546 _99547) (s : _99546 -> Prop) (h1 : term774 _99546 _99547 x'' s) : term774 _99546 _99547 x'' s.
Proof. exact (h1). Qed.
Lemma lem3835808 {_99546 _99547 : Type'} (y' : type427 _99546 _99547) (x'' : type427 _99546 _99547) (s : _99546 -> Prop) (h1 : term772 _99546 _99547 y' x'' s) : term772 _99546 _99547 y' x'' s.
Proof. exact (h1). Qed.
Lemma lem3835839 {_99547 : Type'} : (@eq (_99547 -> _99547)) = (@eq (_99547 -> _99547)).
Proof. exact (eq_refl (@eq (_99547 -> _99547))). Qed.
Lemma lem3835844 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3835845 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (f x) = (@I (_99546 -> _99547 -> _99547) f x).
Proof. exact (@lem3835844 _99546 (_99547 -> _99547) f x). Qed.
Lemma lem3835847 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x' : _99546) : (f x') = (@I (_99546 -> _99547 -> _99547) f x').
Proof. exact (@lem3835845 _99546 _99547 f x'). Qed.
Lemma lem3835852 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3835853 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (f x) = (@I (_99546 -> _99547 -> _99547) f x).
Proof. exact (@lem3835852 _99546 (_99547 -> _99547) f x). Qed.
Lemma lem3835855 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x' : _99546) : (g x') = (@I (_99546 -> _99547 -> _99547) g x').
Proof. exact (@lem3835853 _99546 _99547 g x'). Qed.
Lemma lem3835856 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x' : _99546) : (term817 _99546 _99547 f x') = (term818 _99546 _99547 f x').
Proof. exact (MK_COMB (@lem3835839 _99547) (@lem3835847 _99546 _99547 f x')). Qed.
Lemma lem3835857 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x' : _99546) : ((f x') = (g x')) = ((@I (_99546 -> _99547 -> _99547) f x') = (@I (_99546 -> _99547 -> _99547) g x')).
Proof. exact (MK_COMB (@lem3835856 _99546 _99547 f x') (@lem3835855 _99546 _99547 g x')). Qed.
Lemma lem3835858 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3835865 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3835866 {_99546 : Type'} (f : type1364 _99546) (x : _99546) : (f x) = (@I (_99546 -> (_99546 -> Prop) -> Prop) f x).
Proof. exact (@lem3835865 _99546 (type686 _99546) f x). Qed.
Lemma lem3835867 {_99546 : Type'} (x' : _99546) : (@IN _99546 x') = (@I (_99546 -> (_99546 -> Prop) -> Prop) (@IN _99546) x').
Proof. exact (@lem3835866 _99546 (@IN _99546) x'). Qed.
Lemma lem3835868 {_99546 : Type'} (s : _99546 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3835869 {_99546 : Type'} (x' : _99546) (s : _99546 -> Prop) : (@IN _99546 x' s) = (@I (_99546 -> (_99546 -> Prop) -> Prop) (@IN _99546) x' s).
Proof. exact (MK_COMB (@lem3835867 _99546 x') (@lem3835868 _99546 s)). Qed.
Lemma lem3835871 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3835872 {_99546 : Type'} (f : type686 _99546) (x : _99546 -> Prop) : (f x) = (@I ((_99546 -> Prop) -> Prop) f x).
Proof. exact (@lem3835871 (_99546 -> Prop) Prop f x). Qed.
Lemma lem3835873 {_99546 : Type'} (x' : _99546) (s : _99546 -> Prop) : (@I (_99546 -> (_99546 -> Prop) -> Prop) (@IN _99546) x' s) = (term819 _99546 x' s).
Proof. exact (@lem3835872 _99546 (@I (_99546 -> (_99546 -> Prop) -> Prop) (@IN _99546) x') s). Qed.
Lemma lem3835875 {_99546 : Type'} (x' : _99546) (s : _99546 -> Prop) : (@IN _99546 x' s) = (term819 _99546 x' s).
Proof. exact (TRANS (@lem3835869 _99546 x' s) (@lem3835873 _99546 x' s)). Qed.
Lemma lem3835876 {_99546 : Type'} (x' : _99546) (s : _99546 -> Prop) : (term252 _99546 x' s) = (term820 _99546 x' s).
Proof. exact (MK_COMB (@lem3835858) (@lem3835875 _99546 x' s)). Qed.
Lemma lem3835885 {_99546 : Type'} (x' : _99546) (x : _99546) : (term414 _99546 x' x) = (term414 _99546 x' x).
Proof. exact (eq_refl (term414 _99546 x' x)). Qed.
Lemma lem3835886 {_99546 : Type'} (x : _99546) (x' : _99546) (s : _99546 -> Prop) : (term778 _99546 x x' s) = (term821 _99546 x x' s).
Proof. exact (MK_COMB (@lem3835885 _99546 x' x) (@lem3835876 _99546 x' s)). Qed.
Lemma lem3835887 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3835888 {_99546 : Type'} (x : _99546) (x' : _99546) (s : _99546 -> Prop) : (term780 _99546 x x' s) = (term822 _99546 x x' s).
Proof. exact (MK_COMB (@lem3835887) (@lem3835886 _99546 x x' s)). Qed.
Lemma lem3835889 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x' : _99546) : (term782 _99546 _99547 x s f g x') = (term823 _99546 _99547 x s f g x').
Proof. exact (MK_COMB (@lem3835888 _99546 x x' s) (@lem3835857 _99546 _99547 f g x')). Qed.
Lemma lem3835890 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term783 _99546 _99547 x s f g) = (term824 _99546 _99547 x s f g).
Proof. exact (fun_ext (fun x' : _99546 => @lem3835889 _99546 _99547 x s f g x')). Qed.
Lemma lem3835891 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3835892 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term784 _99546 _99547 x s f g) = (term825 _99546 _99547 x s f g).
Proof. exact (MK_COMB (@lem3835891 _99546) (@lem3835890 _99546 _99547 x s f g)). Qed.
Lemma lem3835893 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term275 _99546 _99547 x s f g) : term825 _99546 _99547 x s f g.
Proof. exact (EQ_MP (@lem3835892 _99546 _99547 x s f g) (@lem3835085 _99546 _99547 x s f g h1)). Qed.
Lemma lem3835894 {_99547 : Type'} : (@eq _99547) = (@eq _99547).
Proof. exact (eq_refl (@eq _99547)). Qed.
Lemma lem3835903 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3835904 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (f x) = (@I (_99546 -> _99547 -> _99547) f x).
Proof. exact (@lem3835903 _99546 (_99547 -> _99547) f x). Qed.
Lemma lem3835905 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (y : _99546) : (f y) = (@I (_99546 -> _99547 -> _99547) f y).
Proof. exact (@lem3835904 _99546 _99547 f y). Qed.
Lemma lem3835906 {_99547 : Type'} (s : _99547) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3835907 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (y : _99546) (s : _99547) : (f y s) = (@I (_99546 -> _99547 -> _99547) f y s).
Proof. exact (MK_COMB (@lem3835905 _99546 _99547 f y) (@lem3835906 _99547 s)). Qed.
Lemma lem3835909 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3835910 {_99547 : Type'} (f : _99547 -> _99547) (x : _99547) : (f x) = (@I (_99547 -> _99547) f x).
Proof. exact (@lem3835909 _99547 _99547 f x). Qed.
Lemma lem3835911 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (y : _99546) (s : _99547) : (@I (_99546 -> _99547 -> _99547) f y s) = (term826 _99546 _99547 f y s).
Proof. exact (@lem3835910 _99547 (@I (_99546 -> _99547 -> _99547) f y) s). Qed.
Lemma lem3835913 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (y : _99546) (s : _99547) : (f y s) = (term826 _99546 _99547 f y s).
Proof. exact (TRANS (@lem3835907 _99546 _99547 f y s) (@lem3835911 _99546 _99547 f y s)). Qed.
Lemma lem3835914 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem3835915 {_99546 _99547 : Type'} (x : _99546) (f : type1411 _99546 _99547) (y : _99546) (s : _99547) : (term93 _99546 _99547 x f y s) = (term827 _99546 _99547 x f y s).
Proof. exact (MK_COMB (@lem3835914 _99546 _99547 f x) (@lem3835913 _99546 _99547 f y s)). Qed.
Lemma lem3835917 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3835918 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (f x) = (@I (_99546 -> _99547 -> _99547) f x).
Proof. exact (@lem3835917 _99546 (_99547 -> _99547) f x). Qed.
Lemma lem3835919 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (y : _99546) (s : _99547) : (term826 _99546 _99547 f y s) = (term826 _99546 _99547 f y s).
Proof. exact (eq_refl (term826 _99546 _99547 f y s)). Qed.
Lemma lem3835920 {_99546 _99547 : Type'} (x : _99546) (f : type1411 _99546 _99547) (y : _99546) (s : _99547) : (term827 _99546 _99547 x f y s) = (term828 _99546 _99547 x f y s).
Proof. exact (MK_COMB (@lem3835918 _99546 _99547 f x) (@lem3835919 _99546 _99547 f y s)). Qed.
Lemma lem3835922 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3835923 {_99547 : Type'} (f : _99547 -> _99547) (x : _99547) : (f x) = (@I (_99547 -> _99547) f x).
Proof. exact (@lem3835922 _99547 _99547 f x). Qed.
Lemma lem3835924 {_99546 _99547 : Type'} (x : _99546) (f : type1411 _99546 _99547) (y : _99546) (s : _99547) : (term828 _99546 _99547 x f y s) = (term829 _99546 _99547 x f y s).
Proof. exact (@lem3835923 _99547 (@I (_99546 -> _99547 -> _99547) f x) (term826 _99546 _99547 f y s)). Qed.
Lemma lem3835925 {_99546 _99547 : Type'} (x : _99546) (f : type1411 _99546 _99547) (y : _99546) (s : _99547) : (term827 _99546 _99547 x f y s) = (term829 _99546 _99547 x f y s).
Proof. exact (TRANS (@lem3835920 _99546 _99547 x f y s) (@lem3835924 _99546 _99547 x f y s)). Qed.
Lemma lem3835926 {_99546 _99547 : Type'} (x : _99546) (f : type1411 _99546 _99547) (y : _99546) (s : _99547) : (term93 _99546 _99547 x f y s) = (term829 _99546 _99547 x f y s).
Proof. exact (TRANS (@lem3835915 _99546 _99547 x f y s) (@lem3835925 _99546 _99547 x f y s)). Qed.
Lemma lem3835935 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3835936 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (f x) = (@I (_99546 -> _99547 -> _99547) f x).
Proof. exact (@lem3835935 _99546 (_99547 -> _99547) f x). Qed.
Lemma lem3835937 {_99547 : Type'} (s : _99547) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3835938 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) (s : _99547) : (f x s) = (@I (_99546 -> _99547 -> _99547) f x s).
Proof. exact (MK_COMB (@lem3835936 _99546 _99547 f x) (@lem3835937 _99547 s)). Qed.
Lemma lem3835940 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3835941 {_99547 : Type'} (f : _99547 -> _99547) (x : _99547) : (f x) = (@I (_99547 -> _99547) f x).
Proof. exact (@lem3835940 _99547 _99547 f x). Qed.
Lemma lem3835942 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) (s : _99547) : (@I (_99546 -> _99547 -> _99547) f x s) = (term826 _99546 _99547 f x s).
Proof. exact (@lem3835941 _99547 (@I (_99546 -> _99547 -> _99547) f x) s). Qed.
Lemma lem3835944 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) (s : _99547) : (f x s) = (term826 _99546 _99547 f x s).
Proof. exact (TRANS (@lem3835938 _99546 _99547 f x s) (@lem3835942 _99546 _99547 f x s)). Qed.
Lemma lem3835945 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (y : _99546) : (f y) = (f y).
Proof. exact (eq_refl (f y)). Qed.
Lemma lem3835946 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term93 _99546 _99547 y f x s) = (term827 _99546 _99547 y f x s).
Proof. exact (MK_COMB (@lem3835945 _99546 _99547 f y) (@lem3835944 _99546 _99547 f x s)). Qed.
Lemma lem3835948 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3835949 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (f x) = (@I (_99546 -> _99547 -> _99547) f x).
Proof. exact (@lem3835948 _99546 (_99547 -> _99547) f x). Qed.
Lemma lem3835950 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (y : _99546) : (f y) = (@I (_99546 -> _99547 -> _99547) f y).
Proof. exact (@lem3835949 _99546 _99547 f y). Qed.
Lemma lem3835951 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term826 _99546 _99547 f x s) = (term826 _99546 _99547 f x s).
Proof. exact (eq_refl (term826 _99546 _99547 f x s)). Qed.
Lemma lem3835952 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term827 _99546 _99547 y f x s) = (term828 _99546 _99547 y f x s).
Proof. exact (MK_COMB (@lem3835950 _99546 _99547 f y) (@lem3835951 _99546 _99547 f x s)). Qed.
Lemma lem3835954 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3835955 {_99547 : Type'} (f : _99547 -> _99547) (x : _99547) : (f x) = (@I (_99547 -> _99547) f x).
Proof. exact (@lem3835954 _99547 _99547 f x). Qed.
Lemma lem3835956 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term828 _99546 _99547 y f x s) = (term829 _99546 _99547 y f x s).
Proof. exact (@lem3835955 _99547 (@I (_99546 -> _99547 -> _99547) f y) (term826 _99546 _99547 f x s)). Qed.
Lemma lem3835957 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term827 _99546 _99547 y f x s) = (term829 _99546 _99547 y f x s).
Proof. exact (TRANS (@lem3835952 _99546 _99547 y f x s) (@lem3835956 _99546 _99547 y f x s)). Qed.
Lemma lem3835958 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term93 _99546 _99547 y f x s) = (term829 _99546 _99547 y f x s).
Proof. exact (TRANS (@lem3835946 _99546 _99547 y f x s) (@lem3835957 _99546 _99547 y f x s)). Qed.
Lemma lem3835959 {_99546 _99547 : Type'} (x : _99546) (f : type1411 _99546 _99547) (y : _99546) (s : _99547) : (term229 _99546 _99547 x f y s) = (term830 _99546 _99547 x f y s).
Proof. exact (MK_COMB (@lem3835894 _99547) (@lem3835926 _99546 _99547 x f y s)). Qed.
Lemma lem3835960 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) (s : _99547) : ((term93 _99546 _99547 x f y s) = (term93 _99546 _99547 y f x s)) = ((term829 _99546 _99547 x f y s) = (term829 _99546 _99547 y f x s)).
Proof. exact (MK_COMB (@lem3835959 _99546 _99547 x f y s) (@lem3835958 _99546 _99547 y f x s)). Qed.
Lemma lem3835961 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term91 _99546 _99547 y f x) = (term831 _99546 _99547 y f x).
Proof. exact (fun_ext (fun s : _99547 => @lem3835960 _99546 _99547 y f x s)). Qed.
Lemma lem3835962 {_99547 : Type'} : (@all _99547) = (@all _99547).
Proof. exact (eq_refl (@all _99547)). Qed.
Lemma lem3835963 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term104 _99546 _99547 y f x) = (term832 _99546 _99547 y f x).
Proof. exact (MK_COMB (@lem3835962 _99547) (@lem3835961 _99546 _99547 y f x)). Qed.
Lemma lem3835970 {_99546 : Type'} (x : _99546) (y : _99546) : (term787 _99546 x y) = (term787 _99546 x y).
Proof. exact (eq_refl (term787 _99546 x y)). Qed.
Lemma lem3835971 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term789 _99546 _99547 y f x) = (term833 _99546 _99547 y f x).
Proof. exact (MK_COMB (@lem3835970 _99546 x y) (@lem3835963 _99546 _99547 y f x)). Qed.
Lemma lem3835972 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (term790 _99546 _99547 f x) = (term834 _99546 _99547 f x).
Proof. exact (fun_ext (fun y : _99546 => @lem3835971 _99546 _99547 y f x)). Qed.
Lemma lem3835973 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3835974 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (term791 _99546 _99547 f x) = (term835 _99546 _99547 f x).
Proof. exact (MK_COMB (@lem3835973 _99546) (@lem3835972 _99546 _99547 f x)). Qed.
Lemma lem3835975 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term792 _99546 _99547 f) = (term836 _99546 _99547 f).
Proof. exact (fun_ext (fun x : _99546 => @lem3835974 _99546 _99547 f x)). Qed.
Lemma lem3835976 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3835977 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term793 _99546 _99547 f) = (term837 _99546 _99547 f).
Proof. exact (MK_COMB (@lem3835976 _99546) (@lem3835975 _99546 _99547 f)). Qed.
Lemma lem3835978 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (h1 : term112 _99546 _99547 f) : term837 _99546 _99547 f.
Proof. exact (EQ_MP (@lem3835977 _99546 _99547 f) (@lem3835164 _99546 _99547 f h1)). Qed.
Lemma lem3835979 {_99547 : Type'} : (@eq _99547) = (@eq _99547).
Proof. exact (eq_refl (@eq _99547)). Qed.
Lemma lem3835988 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3835989 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (f x) = (@I (_99546 -> _99547 -> _99547) f x).
Proof. exact (@lem3835988 _99546 (_99547 -> _99547) f x). Qed.
Lemma lem3835990 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (y : _99546) : (g y) = (@I (_99546 -> _99547 -> _99547) g y).
Proof. exact (@lem3835989 _99546 _99547 g y). Qed.
Lemma lem3835991 {_99547 : Type'} (s : _99547) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3835992 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (y : _99546) (s : _99547) : (g y s) = (@I (_99546 -> _99547 -> _99547) g y s).
Proof. exact (MK_COMB (@lem3835990 _99546 _99547 g y) (@lem3835991 _99547 s)). Qed.
Lemma lem3835994 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3835995 {_99547 : Type'} (f : _99547 -> _99547) (x : _99547) : (f x) = (@I (_99547 -> _99547) f x).
Proof. exact (@lem3835994 _99547 _99547 f x). Qed.
Lemma lem3835996 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (y : _99546) (s : _99547) : (@I (_99546 -> _99547 -> _99547) g y s) = (term826 _99546 _99547 g y s).
Proof. exact (@lem3835995 _99547 (@I (_99546 -> _99547 -> _99547) g y) s). Qed.
Lemma lem3835998 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (y : _99546) (s : _99547) : (g y s) = (term826 _99546 _99547 g y s).
Proof. exact (TRANS (@lem3835992 _99546 _99547 g y s) (@lem3835996 _99546 _99547 g y s)). Qed.
Lemma lem3835999 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) : (g x) = (g x).
Proof. exact (eq_refl (g x)). Qed.
Lemma lem3836000 {_99546 _99547 : Type'} (x : _99546) (g : type1411 _99546 _99547) (y : _99546) (s : _99547) : (term93 _99546 _99547 x g y s) = (term827 _99546 _99547 x g y s).
Proof. exact (MK_COMB (@lem3835999 _99546 _99547 g x) (@lem3835998 _99546 _99547 g y s)). Qed.
Lemma lem3836002 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3836003 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (f x) = (@I (_99546 -> _99547 -> _99547) f x).
Proof. exact (@lem3836002 _99546 (_99547 -> _99547) f x). Qed.
Lemma lem3836004 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) : (g x) = (@I (_99546 -> _99547 -> _99547) g x).
Proof. exact (@lem3836003 _99546 _99547 g x). Qed.
Lemma lem3836005 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (y : _99546) (s : _99547) : (term826 _99546 _99547 g y s) = (term826 _99546 _99547 g y s).
Proof. exact (eq_refl (term826 _99546 _99547 g y s)). Qed.
Lemma lem3836006 {_99546 _99547 : Type'} (x : _99546) (g : type1411 _99546 _99547) (y : _99546) (s : _99547) : (term827 _99546 _99547 x g y s) = (term828 _99546 _99547 x g y s).
Proof. exact (MK_COMB (@lem3836004 _99546 _99547 g x) (@lem3836005 _99546 _99547 g y s)). Qed.
Lemma lem3836008 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3836009 {_99547 : Type'} (f : _99547 -> _99547) (x : _99547) : (f x) = (@I (_99547 -> _99547) f x).
Proof. exact (@lem3836008 _99547 _99547 f x). Qed.
Lemma lem3836010 {_99546 _99547 : Type'} (x : _99546) (g : type1411 _99546 _99547) (y : _99546) (s : _99547) : (term828 _99546 _99547 x g y s) = (term829 _99546 _99547 x g y s).
Proof. exact (@lem3836009 _99547 (@I (_99546 -> _99547 -> _99547) g x) (term826 _99546 _99547 g y s)). Qed.
Lemma lem3836011 {_99546 _99547 : Type'} (x : _99546) (g : type1411 _99546 _99547) (y : _99546) (s : _99547) : (term827 _99546 _99547 x g y s) = (term829 _99546 _99547 x g y s).
Proof. exact (TRANS (@lem3836006 _99546 _99547 x g y s) (@lem3836010 _99546 _99547 x g y s)). Qed.
Lemma lem3836012 {_99546 _99547 : Type'} (x : _99546) (g : type1411 _99546 _99547) (y : _99546) (s : _99547) : (term93 _99546 _99547 x g y s) = (term829 _99546 _99547 x g y s).
Proof. exact (TRANS (@lem3836000 _99546 _99547 x g y s) (@lem3836011 _99546 _99547 x g y s)). Qed.
Lemma lem3836021 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3836022 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (f x) = (@I (_99546 -> _99547 -> _99547) f x).
Proof. exact (@lem3836021 _99546 (_99547 -> _99547) f x). Qed.
Lemma lem3836023 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) : (g x) = (@I (_99546 -> _99547 -> _99547) g x).
Proof. exact (@lem3836022 _99546 _99547 g x). Qed.
Lemma lem3836024 {_99547 : Type'} (s : _99547) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3836025 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) (s : _99547) : (g x s) = (@I (_99546 -> _99547 -> _99547) g x s).
Proof. exact (MK_COMB (@lem3836023 _99546 _99547 g x) (@lem3836024 _99547 s)). Qed.
Lemma lem3836027 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3836028 {_99547 : Type'} (f : _99547 -> _99547) (x : _99547) : (f x) = (@I (_99547 -> _99547) f x).
Proof. exact (@lem3836027 _99547 _99547 f x). Qed.
Lemma lem3836029 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) (s : _99547) : (@I (_99546 -> _99547 -> _99547) g x s) = (term826 _99546 _99547 g x s).
Proof. exact (@lem3836028 _99547 (@I (_99546 -> _99547 -> _99547) g x) s). Qed.
Lemma lem3836031 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) (s : _99547) : (g x s) = (term826 _99546 _99547 g x s).
Proof. exact (TRANS (@lem3836025 _99546 _99547 g x s) (@lem3836029 _99546 _99547 g x s)). Qed.
Lemma lem3836032 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (y : _99546) : (g y) = (g y).
Proof. exact (eq_refl (g y)). Qed.
Lemma lem3836033 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term93 _99546 _99547 y g x s) = (term827 _99546 _99547 y g x s).
Proof. exact (MK_COMB (@lem3836032 _99546 _99547 g y) (@lem3836031 _99546 _99547 g x s)). Qed.
Lemma lem3836035 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3836036 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (f x) = (@I (_99546 -> _99547 -> _99547) f x).
Proof. exact (@lem3836035 _99546 (_99547 -> _99547) f x). Qed.
Lemma lem3836037 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (y : _99546) : (g y) = (@I (_99546 -> _99547 -> _99547) g y).
Proof. exact (@lem3836036 _99546 _99547 g y). Qed.
Lemma lem3836038 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term826 _99546 _99547 g x s) = (term826 _99546 _99547 g x s).
Proof. exact (eq_refl (term826 _99546 _99547 g x s)). Qed.
Lemma lem3836039 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term827 _99546 _99547 y g x s) = (term828 _99546 _99547 y g x s).
Proof. exact (MK_COMB (@lem3836037 _99546 _99547 g y) (@lem3836038 _99546 _99547 g x s)). Qed.
Lemma lem3836041 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3836042 {_99547 : Type'} (f : _99547 -> _99547) (x : _99547) : (f x) = (@I (_99547 -> _99547) f x).
Proof. exact (@lem3836041 _99547 _99547 f x). Qed.
Lemma lem3836043 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term828 _99546 _99547 y g x s) = (term829 _99546 _99547 y g x s).
Proof. exact (@lem3836042 _99547 (@I (_99546 -> _99547 -> _99547) g y) (term826 _99546 _99547 g x s)). Qed.
Lemma lem3836044 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term827 _99546 _99547 y g x s) = (term829 _99546 _99547 y g x s).
Proof. exact (TRANS (@lem3836039 _99546 _99547 y g x s) (@lem3836043 _99546 _99547 y g x s)). Qed.
Lemma lem3836045 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term93 _99546 _99547 y g x s) = (term829 _99546 _99547 y g x s).
Proof. exact (TRANS (@lem3836033 _99546 _99547 y g x s) (@lem3836044 _99546 _99547 y g x s)). Qed.
Lemma lem3836046 {_99546 _99547 : Type'} (x : _99546) (g : type1411 _99546 _99547) (y : _99546) (s : _99547) : (term229 _99546 _99547 x g y s) = (term830 _99546 _99547 x g y s).
Proof. exact (MK_COMB (@lem3835979 _99547) (@lem3836012 _99546 _99547 x g y s)). Qed.
Lemma lem3836047 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) : ((term93 _99546 _99547 x g y s) = (term93 _99546 _99547 y g x s)) = ((term829 _99546 _99547 x g y s) = (term829 _99546 _99547 y g x s)).
Proof. exact (MK_COMB (@lem3836046 _99546 _99547 x g y s) (@lem3836045 _99546 _99547 y g x s)). Qed.
Lemma lem3836048 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term91 _99546 _99547 y g x) = (term831 _99546 _99547 y g x).
Proof. exact (fun_ext (fun s : _99547 => @lem3836047 _99546 _99547 y g x s)). Qed.
Lemma lem3836049 {_99547 : Type'} : (@all _99547) = (@all _99547).
Proof. exact (eq_refl (@all _99547)). Qed.
Lemma lem3836050 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term104 _99546 _99547 y g x) = (term832 _99546 _99547 y g x).
Proof. exact (MK_COMB (@lem3836049 _99547) (@lem3836048 _99546 _99547 y g x)). Qed.
Lemma lem3836057 {_99546 : Type'} (x : _99546) (y : _99546) : (term787 _99546 x y) = (term787 _99546 x y).
Proof. exact (eq_refl (term787 _99546 x y)). Qed.
Lemma lem3836058 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term789 _99546 _99547 y g x) = (term833 _99546 _99547 y g x).
Proof. exact (MK_COMB (@lem3836057 _99546 x y) (@lem3836050 _99546 _99547 y g x)). Qed.
Lemma lem3836059 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) : (term790 _99546 _99547 g x) = (term834 _99546 _99547 g x).
Proof. exact (fun_ext (fun y : _99546 => @lem3836058 _99546 _99547 y g x)). Qed.
Lemma lem3836060 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3836061 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) : (term791 _99546 _99547 g x) = (term835 _99546 _99547 g x).
Proof. exact (MK_COMB (@lem3836060 _99546) (@lem3836059 _99546 _99547 g x)). Qed.
Lemma lem3836062 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) : (term792 _99546 _99547 g) = (term836 _99546 _99547 g).
Proof. exact (fun_ext (fun x : _99546 => @lem3836061 _99546 _99547 g x)). Qed.
Lemma lem3836063 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3836064 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) : (term793 _99546 _99547 g) = (term837 _99546 _99547 g).
Proof. exact (MK_COMB (@lem3836063 _99546) (@lem3836062 _99546 _99547 g)). Qed.
Lemma lem3836065 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (h1 : term112 _99546 _99547 g) : term837 _99546 _99547 g.
Proof. exact (EQ_MP (@lem3836064 _99546 _99547 g) (@lem3835243 _99546 _99547 g h1)). Qed.
Lemma lem3836066 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3836067 {_99547 : Type'} : (@eq _99547) = (@eq _99547).
Proof. exact (eq_refl (@eq _99547)). Qed.
Lemma lem3836076 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3836077 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (f x) = (@I (_99546 -> _99547 -> _99547) f x).
Proof. exact (@lem3836076 _99546 (_99547 -> _99547) f x). Qed.
Lemma lem3836078 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (y : _99546) : (g y) = (@I (_99546 -> _99547 -> _99547) g y).
Proof. exact (@lem3836077 _99546 _99547 g y). Qed.
Lemma lem3836079 {_99547 : Type'} (s' : _99547) : s' = s'.
Proof. exact (eq_refl s'). Qed.
Lemma lem3836080 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (y : _99546) (s' : _99547) : (g y s') = (@I (_99546 -> _99547 -> _99547) g y s').
Proof. exact (MK_COMB (@lem3836078 _99546 _99547 g y) (@lem3836079 _99547 s')). Qed.
Lemma lem3836082 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3836083 {_99547 : Type'} (f : _99547 -> _99547) (x : _99547) : (f x) = (@I (_99547 -> _99547) f x).
Proof. exact (@lem3836082 _99547 _99547 f x). Qed.
Lemma lem3836084 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (y : _99546) (s' : _99547) : (@I (_99546 -> _99547 -> _99547) g y s') = (term826 _99546 _99547 g y s').
Proof. exact (@lem3836083 _99547 (@I (_99546 -> _99547 -> _99547) g y) s'). Qed.
Lemma lem3836086 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (y : _99546) (s' : _99547) : (g y s') = (term826 _99546 _99547 g y s').
Proof. exact (TRANS (@lem3836080 _99546 _99547 g y s') (@lem3836084 _99546 _99547 g y s')). Qed.
Lemma lem3836087 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x' : _99546) : (g x') = (g x').
Proof. exact (eq_refl (g x')). Qed.
Lemma lem3836088 {_99546 _99547 : Type'} (x' : _99546) (g : type1411 _99546 _99547) (y : _99546) (s' : _99547) : (term93 _99546 _99547 x' g y s') = (term827 _99546 _99547 x' g y s').
Proof. exact (MK_COMB (@lem3836087 _99546 _99547 g x') (@lem3836086 _99546 _99547 g y s')). Qed.
Lemma lem3836090 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3836091 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (f x) = (@I (_99546 -> _99547 -> _99547) f x).
Proof. exact (@lem3836090 _99546 (_99547 -> _99547) f x). Qed.
Lemma lem3836092 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x' : _99546) : (g x') = (@I (_99546 -> _99547 -> _99547) g x').
Proof. exact (@lem3836091 _99546 _99547 g x'). Qed.
Lemma lem3836093 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (y : _99546) (s' : _99547) : (term826 _99546 _99547 g y s') = (term826 _99546 _99547 g y s').
Proof. exact (eq_refl (term826 _99546 _99547 g y s')). Qed.
Lemma lem3836094 {_99546 _99547 : Type'} (x' : _99546) (g : type1411 _99546 _99547) (y : _99546) (s' : _99547) : (term827 _99546 _99547 x' g y s') = (term828 _99546 _99547 x' g y s').
Proof. exact (MK_COMB (@lem3836092 _99546 _99547 g x') (@lem3836093 _99546 _99547 g y s')). Qed.
Lemma lem3836096 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3836097 {_99547 : Type'} (f : _99547 -> _99547) (x : _99547) : (f x) = (@I (_99547 -> _99547) f x).
Proof. exact (@lem3836096 _99547 _99547 f x). Qed.
Lemma lem3836098 {_99546 _99547 : Type'} (x' : _99546) (g : type1411 _99546 _99547) (y : _99546) (s' : _99547) : (term828 _99546 _99547 x' g y s') = (term829 _99546 _99547 x' g y s').
Proof. exact (@lem3836097 _99547 (@I (_99546 -> _99547 -> _99547) g x') (term826 _99546 _99547 g y s')). Qed.
Lemma lem3836099 {_99546 _99547 : Type'} (x' : _99546) (g : type1411 _99546 _99547) (y : _99546) (s' : _99547) : (term827 _99546 _99547 x' g y s') = (term829 _99546 _99547 x' g y s').
Proof. exact (TRANS (@lem3836094 _99546 _99547 x' g y s') (@lem3836098 _99546 _99547 x' g y s')). Qed.
Lemma lem3836100 {_99546 _99547 : Type'} (x' : _99546) (g : type1411 _99546 _99547) (y : _99546) (s' : _99547) : (term93 _99546 _99547 x' g y s') = (term829 _99546 _99547 x' g y s').
Proof. exact (TRANS (@lem3836088 _99546 _99547 x' g y s') (@lem3836099 _99546 _99547 x' g y s')). Qed.
Lemma lem3836109 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3836110 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (f x) = (@I (_99546 -> _99547 -> _99547) f x).
Proof. exact (@lem3836109 _99546 (_99547 -> _99547) f x). Qed.
Lemma lem3836111 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x' : _99546) : (g x') = (@I (_99546 -> _99547 -> _99547) g x').
Proof. exact (@lem3836110 _99546 _99547 g x'). Qed.
Lemma lem3836112 {_99547 : Type'} (s' : _99547) : s' = s'.
Proof. exact (eq_refl s'). Qed.
Lemma lem3836113 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x' : _99546) (s' : _99547) : (g x' s') = (@I (_99546 -> _99547 -> _99547) g x' s').
Proof. exact (MK_COMB (@lem3836111 _99546 _99547 g x') (@lem3836112 _99547 s')). Qed.
Lemma lem3836115 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3836116 {_99547 : Type'} (f : _99547 -> _99547) (x : _99547) : (f x) = (@I (_99547 -> _99547) f x).
Proof. exact (@lem3836115 _99547 _99547 f x). Qed.
Lemma lem3836117 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x' : _99546) (s' : _99547) : (@I (_99546 -> _99547 -> _99547) g x' s') = (term826 _99546 _99547 g x' s').
Proof. exact (@lem3836116 _99547 (@I (_99546 -> _99547 -> _99547) g x') s'). Qed.
Lemma lem3836119 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x' : _99546) (s' : _99547) : (g x' s') = (term826 _99546 _99547 g x' s').
Proof. exact (TRANS (@lem3836113 _99546 _99547 g x' s') (@lem3836117 _99546 _99547 g x' s')). Qed.
Lemma lem3836120 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (y : _99546) : (g y) = (g y).
Proof. exact (eq_refl (g y)). Qed.
Lemma lem3836121 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x' : _99546) (s' : _99547) : (term93 _99546 _99547 y g x' s') = (term827 _99546 _99547 y g x' s').
Proof. exact (MK_COMB (@lem3836120 _99546 _99547 g y) (@lem3836119 _99546 _99547 g x' s')). Qed.
Lemma lem3836123 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3836124 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (f x) = (@I (_99546 -> _99547 -> _99547) f x).
Proof. exact (@lem3836123 _99546 (_99547 -> _99547) f x). Qed.
Lemma lem3836125 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (y : _99546) : (g y) = (@I (_99546 -> _99547 -> _99547) g y).
Proof. exact (@lem3836124 _99546 _99547 g y). Qed.
Lemma lem3836126 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x' : _99546) (s' : _99547) : (term826 _99546 _99547 g x' s') = (term826 _99546 _99547 g x' s').
Proof. exact (eq_refl (term826 _99546 _99547 g x' s')). Qed.
Lemma lem3836127 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x' : _99546) (s' : _99547) : (term827 _99546 _99547 y g x' s') = (term828 _99546 _99547 y g x' s').
Proof. exact (MK_COMB (@lem3836125 _99546 _99547 g y) (@lem3836126 _99546 _99547 g x' s')). Qed.
Lemma lem3836129 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3836130 {_99547 : Type'} (f : _99547 -> _99547) (x : _99547) : (f x) = (@I (_99547 -> _99547) f x).
Proof. exact (@lem3836129 _99547 _99547 f x). Qed.
Lemma lem3836131 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x' : _99546) (s' : _99547) : (term828 _99546 _99547 y g x' s') = (term829 _99546 _99547 y g x' s').
Proof. exact (@lem3836130 _99547 (@I (_99546 -> _99547 -> _99547) g y) (term826 _99546 _99547 g x' s')). Qed.
Lemma lem3836132 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x' : _99546) (s' : _99547) : (term827 _99546 _99547 y g x' s') = (term829 _99546 _99547 y g x' s').
Proof. exact (TRANS (@lem3836127 _99546 _99547 y g x' s') (@lem3836131 _99546 _99547 y g x' s')). Qed.
Lemma lem3836133 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x' : _99546) (s' : _99547) : (term93 _99546 _99547 y g x' s') = (term829 _99546 _99547 y g x' s').
Proof. exact (TRANS (@lem3836121 _99546 _99547 y g x' s') (@lem3836132 _99546 _99547 y g x' s')). Qed.
Lemma lem3836134 {_99546 _99547 : Type'} (x' : _99546) (g : type1411 _99546 _99547) (y : _99546) (s' : _99547) : (term229 _99546 _99547 x' g y s') = (term830 _99546 _99547 x' g y s').
Proof. exact (MK_COMB (@lem3836067 _99547) (@lem3836100 _99546 _99547 x' g y s')). Qed.
Lemma lem3836135 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x' : _99546) (s' : _99547) : ((term93 _99546 _99547 x' g y s') = (term93 _99546 _99547 y g x' s')) = ((term829 _99546 _99547 x' g y s') = (term829 _99546 _99547 y g x' s')).
Proof. exact (MK_COMB (@lem3836134 _99546 _99547 x' g y s') (@lem3836133 _99546 _99547 y g x' s')). Qed.
Lemma lem3836136 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x' : _99546) (s' : _99547) : (term410 _99546 _99547 y g x' s') = (term838 _99546 _99547 y g x' s').
Proof. exact (MK_COMB (@lem3836066) (@lem3836135 _99546 _99547 y g x' s')). Qed.
Lemma lem3836145 {_99546 : Type'} (x' : _99546) (y : _99546) : (term414 _99546 x' y) = (term414 _99546 x' y).
Proof. exact (eq_refl (term414 _99546 x' y)). Qed.
Lemma lem3836146 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x' : _99546) (s' : _99547) : (term458 _99546 _99547 y g x' s') = (term839 _99546 _99547 y g x' s').
Proof. exact (MK_COMB (@lem3836145 _99546 x' y) (@lem3836136 _99546 _99547 y g x' s')). Qed.
Lemma lem3836147 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3836148 {_99547 : Type'} : (@eq _99547) = (@eq _99547).
Proof. exact (eq_refl (@eq _99547)). Qed.
Lemma lem3836157 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3836158 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (f x) = (@I (_99546 -> _99547 -> _99547) f x).
Proof. exact (@lem3836157 _99546 (_99547 -> _99547) f x). Qed.
Lemma lem3836159 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (y : _99546) : (f y) = (@I (_99546 -> _99547 -> _99547) f y).
Proof. exact (@lem3836158 _99546 _99547 f y). Qed.
Lemma lem3836160 {_99547 : Type'} (s' : _99547) : s' = s'.
Proof. exact (eq_refl s'). Qed.
Lemma lem3836161 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (y : _99546) (s' : _99547) : (f y s') = (@I (_99546 -> _99547 -> _99547) f y s').
Proof. exact (MK_COMB (@lem3836159 _99546 _99547 f y) (@lem3836160 _99547 s')). Qed.
Lemma lem3836163 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3836164 {_99547 : Type'} (f : _99547 -> _99547) (x : _99547) : (f x) = (@I (_99547 -> _99547) f x).
Proof. exact (@lem3836163 _99547 _99547 f x). Qed.
Lemma lem3836165 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (y : _99546) (s' : _99547) : (@I (_99546 -> _99547 -> _99547) f y s') = (term826 _99546 _99547 f y s').
Proof. exact (@lem3836164 _99547 (@I (_99546 -> _99547 -> _99547) f y) s'). Qed.
Lemma lem3836167 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (y : _99546) (s' : _99547) : (f y s') = (term826 _99546 _99547 f y s').
Proof. exact (TRANS (@lem3836161 _99546 _99547 f y s') (@lem3836165 _99546 _99547 f y s')). Qed.
Lemma lem3836168 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x' : _99546) : (f x') = (f x').
Proof. exact (eq_refl (f x')). Qed.
Lemma lem3836169 {_99546 _99547 : Type'} (x' : _99546) (f : type1411 _99546 _99547) (y : _99546) (s' : _99547) : (term93 _99546 _99547 x' f y s') = (term827 _99546 _99547 x' f y s').
Proof. exact (MK_COMB (@lem3836168 _99546 _99547 f x') (@lem3836167 _99546 _99547 f y s')). Qed.
Lemma lem3836171 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3836172 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (f x) = (@I (_99546 -> _99547 -> _99547) f x).
Proof. exact (@lem3836171 _99546 (_99547 -> _99547) f x). Qed.
Lemma lem3836173 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x' : _99546) : (f x') = (@I (_99546 -> _99547 -> _99547) f x').
Proof. exact (@lem3836172 _99546 _99547 f x'). Qed.
Lemma lem3836174 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (y : _99546) (s' : _99547) : (term826 _99546 _99547 f y s') = (term826 _99546 _99547 f y s').
Proof. exact (eq_refl (term826 _99546 _99547 f y s')). Qed.
Lemma lem3836175 {_99546 _99547 : Type'} (x' : _99546) (f : type1411 _99546 _99547) (y : _99546) (s' : _99547) : (term827 _99546 _99547 x' f y s') = (term828 _99546 _99547 x' f y s').
Proof. exact (MK_COMB (@lem3836173 _99546 _99547 f x') (@lem3836174 _99546 _99547 f y s')). Qed.
Lemma lem3836177 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3836178 {_99547 : Type'} (f : _99547 -> _99547) (x : _99547) : (f x) = (@I (_99547 -> _99547) f x).
Proof. exact (@lem3836177 _99547 _99547 f x). Qed.
Lemma lem3836179 {_99546 _99547 : Type'} (x' : _99546) (f : type1411 _99546 _99547) (y : _99546) (s' : _99547) : (term828 _99546 _99547 x' f y s') = (term829 _99546 _99547 x' f y s').
Proof. exact (@lem3836178 _99547 (@I (_99546 -> _99547 -> _99547) f x') (term826 _99546 _99547 f y s')). Qed.
Lemma lem3836180 {_99546 _99547 : Type'} (x' : _99546) (f : type1411 _99546 _99547) (y : _99546) (s' : _99547) : (term827 _99546 _99547 x' f y s') = (term829 _99546 _99547 x' f y s').
Proof. exact (TRANS (@lem3836175 _99546 _99547 x' f y s') (@lem3836179 _99546 _99547 x' f y s')). Qed.
Lemma lem3836181 {_99546 _99547 : Type'} (x' : _99546) (f : type1411 _99546 _99547) (y : _99546) (s' : _99547) : (term93 _99546 _99547 x' f y s') = (term829 _99546 _99547 x' f y s').
Proof. exact (TRANS (@lem3836169 _99546 _99547 x' f y s') (@lem3836180 _99546 _99547 x' f y s')). Qed.
Lemma lem3836190 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3836191 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (f x) = (@I (_99546 -> _99547 -> _99547) f x).
Proof. exact (@lem3836190 _99546 (_99547 -> _99547) f x). Qed.
Lemma lem3836192 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x' : _99546) : (f x') = (@I (_99546 -> _99547 -> _99547) f x').
Proof. exact (@lem3836191 _99546 _99547 f x'). Qed.
Lemma lem3836193 {_99547 : Type'} (s' : _99547) : s' = s'.
Proof. exact (eq_refl s'). Qed.
Lemma lem3836194 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x' : _99546) (s' : _99547) : (f x' s') = (@I (_99546 -> _99547 -> _99547) f x' s').
Proof. exact (MK_COMB (@lem3836192 _99546 _99547 f x') (@lem3836193 _99547 s')). Qed.
Lemma lem3836196 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3836197 {_99547 : Type'} (f : _99547 -> _99547) (x : _99547) : (f x) = (@I (_99547 -> _99547) f x).
Proof. exact (@lem3836196 _99547 _99547 f x). Qed.
Lemma lem3836198 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x' : _99546) (s' : _99547) : (@I (_99546 -> _99547 -> _99547) f x' s') = (term826 _99546 _99547 f x' s').
Proof. exact (@lem3836197 _99547 (@I (_99546 -> _99547 -> _99547) f x') s'). Qed.
Lemma lem3836200 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x' : _99546) (s' : _99547) : (f x' s') = (term826 _99546 _99547 f x' s').
Proof. exact (TRANS (@lem3836194 _99546 _99547 f x' s') (@lem3836198 _99546 _99547 f x' s')). Qed.
Lemma lem3836201 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (y : _99546) : (f y) = (f y).
Proof. exact (eq_refl (f y)). Qed.
Lemma lem3836202 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x' : _99546) (s' : _99547) : (term93 _99546 _99547 y f x' s') = (term827 _99546 _99547 y f x' s').
Proof. exact (MK_COMB (@lem3836201 _99546 _99547 f y) (@lem3836200 _99546 _99547 f x' s')). Qed.
Lemma lem3836204 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3836205 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (f x) = (@I (_99546 -> _99547 -> _99547) f x).
Proof. exact (@lem3836204 _99546 (_99547 -> _99547) f x). Qed.
Lemma lem3836206 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (y : _99546) : (f y) = (@I (_99546 -> _99547 -> _99547) f y).
Proof. exact (@lem3836205 _99546 _99547 f y). Qed.
Lemma lem3836207 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x' : _99546) (s' : _99547) : (term826 _99546 _99547 f x' s') = (term826 _99546 _99547 f x' s').
Proof. exact (eq_refl (term826 _99546 _99547 f x' s')). Qed.
Lemma lem3836208 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x' : _99546) (s' : _99547) : (term827 _99546 _99547 y f x' s') = (term828 _99546 _99547 y f x' s').
Proof. exact (MK_COMB (@lem3836206 _99546 _99547 f y) (@lem3836207 _99546 _99547 f x' s')). Qed.
Lemma lem3836210 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3836211 {_99547 : Type'} (f : _99547 -> _99547) (x : _99547) : (f x) = (@I (_99547 -> _99547) f x).
Proof. exact (@lem3836210 _99547 _99547 f x). Qed.
Lemma lem3836212 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x' : _99546) (s' : _99547) : (term828 _99546 _99547 y f x' s') = (term829 _99546 _99547 y f x' s').
Proof. exact (@lem3836211 _99547 (@I (_99546 -> _99547 -> _99547) f y) (term826 _99546 _99547 f x' s')). Qed.
Lemma lem3836213 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x' : _99546) (s' : _99547) : (term827 _99546 _99547 y f x' s') = (term829 _99546 _99547 y f x' s').
Proof. exact (TRANS (@lem3836208 _99546 _99547 y f x' s') (@lem3836212 _99546 _99547 y f x' s')). Qed.
Lemma lem3836214 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x' : _99546) (s' : _99547) : (term93 _99546 _99547 y f x' s') = (term829 _99546 _99547 y f x' s').
Proof. exact (TRANS (@lem3836202 _99546 _99547 y f x' s') (@lem3836213 _99546 _99547 y f x' s')). Qed.
Lemma lem3836215 {_99546 _99547 : Type'} (x' : _99546) (f : type1411 _99546 _99547) (y : _99546) (s' : _99547) : (term229 _99546 _99547 x' f y s') = (term830 _99546 _99547 x' f y s').
Proof. exact (MK_COMB (@lem3836148 _99547) (@lem3836181 _99546 _99547 x' f y s')). Qed.
Lemma lem3836216 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x' : _99546) (s' : _99547) : ((term93 _99546 _99547 x' f y s') = (term93 _99546 _99547 y f x' s')) = ((term829 _99546 _99547 x' f y s') = (term829 _99546 _99547 y f x' s')).
Proof. exact (MK_COMB (@lem3836215 _99546 _99547 x' f y s') (@lem3836214 _99546 _99547 y f x' s')). Qed.
Lemma lem3836217 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x' : _99546) (s' : _99547) : (term410 _99546 _99547 y f x' s') = (term838 _99546 _99547 y f x' s').
Proof. exact (MK_COMB (@lem3836147) (@lem3836216 _99546 _99547 y f x' s')). Qed.
Lemma lem3836226 {_99546 : Type'} (x' : _99546) (y : _99546) : (term414 _99546 x' y) = (term414 _99546 x' y).
Proof. exact (eq_refl (term414 _99546 x' y)). Qed.
Lemma lem3836227 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x' : _99546) (s' : _99547) : (term458 _99546 _99547 y f x' s') = (term839 _99546 _99547 y f x' s').
Proof. exact (MK_COMB (@lem3836226 _99546 x' y) (@lem3836217 _99546 _99547 y f x' s')). Qed.
Lemma lem3836228 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3836229 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x' : _99546) (s' : _99547) : (term509 _99546 _99547 y f x' s') = (term840 _99546 _99547 y f x' s').
Proof. exact (MK_COMB (@lem3836228) (@lem3836227 _99546 _99547 y f x' s')). Qed.
Lemma lem3836230 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x' : _99546) (s' : _99547) : (term511 _99546 _99547 f y g x' s') = (term841 _99546 _99547 f y g x' s').
Proof. exact (MK_COMB (@lem3836229 _99546 _99547 y f x' s') (@lem3836146 _99546 _99547 y g x' s')). Qed.
Lemma lem3836231 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3836232 {_99547 : Type'} : (@eq (_99547 -> _99547)) = (@eq (_99547 -> _99547)).
Proof. exact (eq_refl (@eq (_99547 -> _99547))). Qed.
Lemma lem3836237 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3836238 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (f x) = (@I (_99546 -> _99547 -> _99547) f x).
Proof. exact (@lem3836237 _99546 (_99547 -> _99547) f x). Qed.
Lemma lem3836240 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x' : _99546) : (f x') = (@I (_99546 -> _99547 -> _99547) f x').
Proof. exact (@lem3836238 _99546 _99547 f x'). Qed.
Lemma lem3836245 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3836246 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (f x) = (@I (_99546 -> _99547 -> _99547) f x).
Proof. exact (@lem3836245 _99546 (_99547 -> _99547) f x). Qed.
Lemma lem3836248 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x' : _99546) : (g x') = (@I (_99546 -> _99547 -> _99547) g x').
Proof. exact (@lem3836246 _99546 _99547 g x'). Qed.
Lemma lem3836249 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x' : _99546) : (term817 _99546 _99547 f x') = (term818 _99546 _99547 f x').
Proof. exact (MK_COMB (@lem3836232 _99547) (@lem3836240 _99546 _99547 f x')). Qed.
Lemma lem3836250 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x' : _99546) : ((f x') = (g x')) = ((@I (_99546 -> _99547 -> _99547) f x') = (@I (_99546 -> _99547 -> _99547) g x')).
Proof. exact (MK_COMB (@lem3836249 _99546 _99547 f x') (@lem3836248 _99546 _99547 g x')). Qed.
Lemma lem3836251 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x' : _99546) : (term842 _99546 _99547 f g x') = (term843 _99546 _99547 f g x').
Proof. exact (MK_COMB (@lem3836231) (@lem3836250 _99546 _99547 f g x')). Qed.
Lemma lem3836258 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3836259 {_99546 : Type'} (f : type1364 _99546) (x : _99546) : (f x) = (@I (_99546 -> (_99546 -> Prop) -> Prop) f x).
Proof. exact (@lem3836258 _99546 (type686 _99546) f x). Qed.
Lemma lem3836260 {_99546 : Type'} (x' : _99546) : (@IN _99546 x') = (@I (_99546 -> (_99546 -> Prop) -> Prop) (@IN _99546) x').
Proof. exact (@lem3836259 _99546 (@IN _99546) x'). Qed.
Lemma lem3836261 {_99546 : Type'} (s : _99546 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3836262 {_99546 : Type'} (x' : _99546) (s : _99546 -> Prop) : (@IN _99546 x' s) = (@I (_99546 -> (_99546 -> Prop) -> Prop) (@IN _99546) x' s).
Proof. exact (MK_COMB (@lem3836260 _99546 x') (@lem3836261 _99546 s)). Qed.
Lemma lem3836264 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3836265 {_99546 : Type'} (f : type686 _99546) (x : _99546 -> Prop) : (f x) = (@I ((_99546 -> Prop) -> Prop) f x).
Proof. exact (@lem3836264 (_99546 -> Prop) Prop f x). Qed.
Lemma lem3836266 {_99546 : Type'} (x' : _99546) (s : _99546 -> Prop) : (@I (_99546 -> (_99546 -> Prop) -> Prop) (@IN _99546) x' s) = (term819 _99546 x' s).
Proof. exact (@lem3836265 _99546 (@I (_99546 -> (_99546 -> Prop) -> Prop) (@IN _99546) x') s). Qed.
Lemma lem3836268 {_99546 : Type'} (x' : _99546) (s : _99546 -> Prop) : (@IN _99546 x' s) = (term819 _99546 x' s).
Proof. exact (TRANS (@lem3836262 _99546 x' s) (@lem3836266 _99546 x' s)). Qed.
Lemma lem3836269 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3836270 {_99546 : Type'} (x' : _99546) (s : _99546 -> Prop) : (term844 _99546 x' s) = (term845 _99546 x' s).
Proof. exact (MK_COMB (@lem3836269) (@lem3836268 _99546 x' s)). Qed.
Lemma lem3836271 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x' : _99546) : (term397 _99546 _99547 s f g x') = (term846 _99546 _99547 s f g x').
Proof. exact (MK_COMB (@lem3836270 _99546 x' s) (@lem3836251 _99546 _99547 f g x')). Qed.
Lemma lem3836272 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3836273 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x' : _99546) : (term532 _99546 _99547 s f g x') = (term847 _99546 _99547 s f g x').
Proof. exact (MK_COMB (@lem3836272) (@lem3836271 _99546 _99547 s f g x')). Qed.
Lemma lem3836274 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x' : _99546) (s' : _99547) : (term560 _99546 _99547 s f y g x' s') = (term848 _99546 _99547 s f y g x' s').
Proof. exact (MK_COMB (@lem3836273 _99546 _99547 s f g x') (@lem3836230 _99546 _99547 f y g x' s')). Qed.
Lemma lem3836275 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x' : _99546) (s' : _99547) (h1 : term560 _99546 _99547 s f y g x' s') : term848 _99546 _99547 s f y g x' s'.
Proof. exact (EQ_MP (@lem3836274 _99546 _99547 s f y g x' s') (@lem3835806 _99546 _99547 s f y g x' s' h1)). Qed.
Lemma lem3836857 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x' : _99546) (h1 : term846 _99546 _99547 s f g x') : term846 _99546 _99547 s f g x'.
Proof. exact (h1). Qed.
Lemma lem3836858 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x' : _99546) (s' : _99547) (h1 : term841 _99546 _99547 f y g x' s') : term841 _99546 _99547 f y g x' s'.
Proof. exact (h1). Qed.
Lemma lem3836861 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x' : _99546) (s' : _99547) (h1 : term839 _99546 _99547 y f x' s') : term839 _99546 _99547 y f x' s'.
Proof. exact (h1). Qed.
Lemma lem3836862 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x' : _99546) (s' : _99547) (h1 : term839 _99546 _99547 y g x' s') : term839 _99546 _99547 y g x' s'.
Proof. exact (h1). Qed.
Lemma lem3836892 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x' : _99546) : (term823 _99546 _99547 x s f g x') = (term849 _99546 _99547 x s f g x').
Proof. exact (@lem19699 (term90 _99546 x' x) (term820 _99546 x' s) ((@I (_99546 -> _99547 -> _99547) f x') = (@I (_99546 -> _99547 -> _99547) g x'))). Qed.
Lemma lem3836893 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term824 _99546 _99547 x s f g) = (term850 _99546 _99547 x s f g).
Proof. exact (fun_ext (fun x' : _99546 => @lem3836892 _99546 _99547 x s f g x')). Qed.
Lemma lem3836894 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3836896 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term825 _99546 _99547 x s f g) = (term851 _99546 _99547 x s f g).
Proof. exact (MK_COMB (@lem3836894 _99546) (@lem3836893 _99546 _99547 x s f g)). Qed.
Lemma lem3836897 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term275 _99546 _99547 x s f g) : term851 _99546 _99547 x s f g.
Proof. exact (EQ_MP (@lem3836896 _99546 _99547 x s f g) (@lem3835893 _99546 _99547 x s f g h1)). Qed.
Lemma lem3837196 {A : Type'} (P : Prop) (Q : A -> Prop) : (term852 A P Q) = (term853 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem3837197 {_99547 : Type'} (P : Prop) (Q : _99547 -> Prop) : (term852 _99547 P Q) = (term853 _99547 P Q).
Proof. exact (@lem3837196 _99547 P Q). Qed.
Lemma lem3837198 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term854 _99546 _99547 y f x) = (term855 _99546 _99547 y f x).
Proof. exact (@lem3837197 _99547 (x = y) (term831 _99546 _99547 y f x)). Qed.
Lemma lem3837199 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term856 _99546 _99547 y f x s) = ((term829 _99546 _99547 x f y s) = (term829 _99546 _99547 y f x s)).
Proof. exact (eq_refl (term856 _99546 _99547 y f x s)). Qed.
Lemma lem3837200 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term857 _99546 _99547 y f x) = (term831 _99546 _99547 y f x).
Proof. exact (fun_ext (fun s : _99547 => @lem3837199 _99546 _99547 y f x s)). Qed.
Lemma lem3837201 {_99547 : Type'} : (@all _99547) = (@all _99547).
Proof. exact (eq_refl (@all _99547)). Qed.
Lemma lem3837202 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term858 _99546 _99547 y f x) = (term832 _99546 _99547 y f x).
Proof. exact (MK_COMB (@lem3837201 _99547) (@lem3837200 _99546 _99547 y f x)). Qed.
Lemma lem3837203 {_99546 : Type'} (x : _99546) (y : _99546) : (term787 _99546 x y) = (term787 _99546 x y).
Proof. exact (eq_refl (term787 _99546 x y)). Qed.
Lemma lem3837204 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term854 _99546 _99547 y f x) = (term833 _99546 _99547 y f x).
Proof. exact (MK_COMB (@lem3837203 _99546 x y) (@lem3837202 _99546 _99547 y f x)). Qed.
Lemma lem3837205 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3837206 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term859 _99546 _99547 y f x) = (term860 _99546 _99547 y f x).
Proof. exact (MK_COMB (@lem3837205) (@lem3837204 _99546 _99547 y f x)). Qed.
Lemma lem3837207 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term856 _99546 _99547 y f x s) = ((term829 _99546 _99547 x f y s) = (term829 _99546 _99547 y f x s)).
Proof. exact (eq_refl (term856 _99546 _99547 y f x s)). Qed.
Lemma lem3837208 {_99546 : Type'} (x : _99546) (y : _99546) : (term787 _99546 x y) = (term787 _99546 x y).
Proof. exact (eq_refl (term787 _99546 x y)). Qed.
Lemma lem3837209 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term861 _99546 _99547 y f x s) = (term862 _99546 _99547 y f x s).
Proof. exact (MK_COMB (@lem3837208 _99546 x y) (@lem3837207 _99546 _99547 y f x s)). Qed.
Lemma lem3837210 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term863 _99546 _99547 y f x) = (term864 _99546 _99547 y f x).
Proof. exact (fun_ext (fun s : _99547 => @lem3837209 _99546 _99547 y f x s)). Qed.
Lemma lem3837211 {_99547 : Type'} : (@all _99547) = (@all _99547).
Proof. exact (eq_refl (@all _99547)). Qed.
Lemma lem3837212 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term855 _99546 _99547 y f x) = (term865 _99546 _99547 y f x).
Proof. exact (MK_COMB (@lem3837211 _99547) (@lem3837210 _99546 _99547 y f x)). Qed.
Lemma lem3837213 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : ((term854 _99546 _99547 y f x) = (term855 _99546 _99547 y f x)) = ((term833 _99546 _99547 y f x) = (term865 _99546 _99547 y f x)).
Proof. exact (MK_COMB (@lem3837206 _99546 _99547 y f x) (@lem3837212 _99546 _99547 y f x)). Qed.
Lemma lem3837214 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term833 _99546 _99547 y f x) = (term865 _99546 _99547 y f x).
Proof. exact (EQ_MP (@lem3837213 _99546 _99547 y f x) (@lem3837198 _99546 _99547 y f x)). Qed.
Lemma lem3837215 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (term834 _99546 _99547 f x) = (term866 _99546 _99547 f x).
Proof. exact (fun_ext (fun y : _99546 => @lem3837214 _99546 _99547 y f x)). Qed.
Lemma lem3837216 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3837217 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (term835 _99546 _99547 f x) = (term867 _99546 _99547 f x).
Proof. exact (MK_COMB (@lem3837216 _99546) (@lem3837215 _99546 _99547 f x)). Qed.
Lemma lem3837218 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term836 _99546 _99547 f) = (term868 _99546 _99547 f).
Proof. exact (fun_ext (fun x : _99546 => @lem3837217 _99546 _99547 f x)). Qed.
Lemma lem3837219 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3837220 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term837 _99546 _99547 f) = (term869 _99546 _99547 f).
Proof. exact (MK_COMB (@lem3837219 _99546) (@lem3837218 _99546 _99547 f)). Qed.
Lemma lem3837227 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term862 _99546 _99547 y f x s) = (term862 _99546 _99547 y f x s).
Proof. exact (eq_refl (term862 _99546 _99547 y f x s)). Qed.
Lemma lem3837228 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term864 _99546 _99547 y f x) = (term864 _99546 _99547 y f x).
Proof. exact (fun_ext (fun s : _99547 => @lem3837227 _99546 _99547 y f x s)). Qed.
Lemma lem3837229 {_99547 : Type'} : (@all _99547) = (@all _99547).
Proof. exact (eq_refl (@all _99547)). Qed.
Lemma lem3837230 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x : _99546) : (term865 _99546 _99547 y f x) = (term865 _99546 _99547 y f x).
Proof. exact (MK_COMB (@lem3837229 _99547) (@lem3837228 _99546 _99547 y f x)). Qed.
Lemma lem3837231 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (term866 _99546 _99547 f x) = (term866 _99546 _99547 f x).
Proof. exact (fun_ext (fun y : _99546 => @lem3837230 _99546 _99547 y f x)). Qed.
Lemma lem3837232 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3837233 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) : (term867 _99546 _99547 f x) = (term867 _99546 _99547 f x).
Proof. exact (MK_COMB (@lem3837232 _99546) (@lem3837231 _99546 _99547 f x)). Qed.
Lemma lem3837234 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term868 _99546 _99547 f) = (term868 _99546 _99547 f).
Proof. exact (fun_ext (fun x : _99546 => @lem3837233 _99546 _99547 f x)). Qed.
Lemma lem3837235 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3837236 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term869 _99546 _99547 f) = (term869 _99546 _99547 f).
Proof. exact (MK_COMB (@lem3837235 _99546) (@lem3837234 _99546 _99547 f)). Qed.
Lemma lem3837237 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) : (term837 _99546 _99547 f) = (term869 _99546 _99547 f).
Proof. exact (TRANS (@lem3837220 _99546 _99547 f) (@lem3837236 _99546 _99547 f)). Qed.
Lemma lem3837238 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (h1 : term112 _99546 _99547 f) : term869 _99546 _99547 f.
Proof. exact (EQ_MP (@lem3837237 _99546 _99547 f) (@lem3835978 _99546 _99547 f h1)). Qed.
Lemma lem3837537 {A : Type'} (P : Prop) (Q : A -> Prop) : (term852 A P Q) = (term853 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem3837538 {_99547 : Type'} (P : Prop) (Q : _99547 -> Prop) : (term852 _99547 P Q) = (term853 _99547 P Q).
Proof. exact (@lem3837537 _99547 P Q). Qed.
Lemma lem3837539 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term854 _99546 _99547 y g x) = (term855 _99546 _99547 y g x).
Proof. exact (@lem3837538 _99547 (x = y) (term831 _99546 _99547 y g x)). Qed.
Lemma lem3837540 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term856 _99546 _99547 y g x s) = ((term829 _99546 _99547 x g y s) = (term829 _99546 _99547 y g x s)).
Proof. exact (eq_refl (term856 _99546 _99547 y g x s)). Qed.
Lemma lem3837541 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term857 _99546 _99547 y g x) = (term831 _99546 _99547 y g x).
Proof. exact (fun_ext (fun s : _99547 => @lem3837540 _99546 _99547 y g x s)). Qed.
Lemma lem3837542 {_99547 : Type'} : (@all _99547) = (@all _99547).
Proof. exact (eq_refl (@all _99547)). Qed.
Lemma lem3837543 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term858 _99546 _99547 y g x) = (term832 _99546 _99547 y g x).
Proof. exact (MK_COMB (@lem3837542 _99547) (@lem3837541 _99546 _99547 y g x)). Qed.
Lemma lem3837544 {_99546 : Type'} (x : _99546) (y : _99546) : (term787 _99546 x y) = (term787 _99546 x y).
Proof. exact (eq_refl (term787 _99546 x y)). Qed.
Lemma lem3837545 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term854 _99546 _99547 y g x) = (term833 _99546 _99547 y g x).
Proof. exact (MK_COMB (@lem3837544 _99546 x y) (@lem3837543 _99546 _99547 y g x)). Qed.
Lemma lem3837546 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3837547 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term859 _99546 _99547 y g x) = (term860 _99546 _99547 y g x).
Proof. exact (MK_COMB (@lem3837546) (@lem3837545 _99546 _99547 y g x)). Qed.
Lemma lem3837548 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term856 _99546 _99547 y g x s) = ((term829 _99546 _99547 x g y s) = (term829 _99546 _99547 y g x s)).
Proof. exact (eq_refl (term856 _99546 _99547 y g x s)). Qed.
Lemma lem3837549 {_99546 : Type'} (x : _99546) (y : _99546) : (term787 _99546 x y) = (term787 _99546 x y).
Proof. exact (eq_refl (term787 _99546 x y)). Qed.
Lemma lem3837550 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term861 _99546 _99547 y g x s) = (term862 _99546 _99547 y g x s).
Proof. exact (MK_COMB (@lem3837549 _99546 x y) (@lem3837548 _99546 _99547 y g x s)). Qed.
Lemma lem3837551 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term863 _99546 _99547 y g x) = (term864 _99546 _99547 y g x).
Proof. exact (fun_ext (fun s : _99547 => @lem3837550 _99546 _99547 y g x s)). Qed.
Lemma lem3837552 {_99547 : Type'} : (@all _99547) = (@all _99547).
Proof. exact (eq_refl (@all _99547)). Qed.
Lemma lem3837553 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term855 _99546 _99547 y g x) = (term865 _99546 _99547 y g x).
Proof. exact (MK_COMB (@lem3837552 _99547) (@lem3837551 _99546 _99547 y g x)). Qed.
Lemma lem3837554 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : ((term854 _99546 _99547 y g x) = (term855 _99546 _99547 y g x)) = ((term833 _99546 _99547 y g x) = (term865 _99546 _99547 y g x)).
Proof. exact (MK_COMB (@lem3837547 _99546 _99547 y g x) (@lem3837553 _99546 _99547 y g x)). Qed.
Lemma lem3837555 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term833 _99546 _99547 y g x) = (term865 _99546 _99547 y g x).
Proof. exact (EQ_MP (@lem3837554 _99546 _99547 y g x) (@lem3837539 _99546 _99547 y g x)). Qed.
Lemma lem3837556 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) : (term834 _99546 _99547 g x) = (term866 _99546 _99547 g x).
Proof. exact (fun_ext (fun y : _99546 => @lem3837555 _99546 _99547 y g x)). Qed.
Lemma lem3837557 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3837558 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) : (term835 _99546 _99547 g x) = (term867 _99546 _99547 g x).
Proof. exact (MK_COMB (@lem3837557 _99546) (@lem3837556 _99546 _99547 g x)). Qed.
Lemma lem3837559 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) : (term836 _99546 _99547 g) = (term868 _99546 _99547 g).
Proof. exact (fun_ext (fun x : _99546 => @lem3837558 _99546 _99547 g x)). Qed.
Lemma lem3837560 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3837561 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) : (term837 _99546 _99547 g) = (term869 _99546 _99547 g).
Proof. exact (MK_COMB (@lem3837560 _99546) (@lem3837559 _99546 _99547 g)). Qed.
Lemma lem3837568 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) (s : _99547) : (term862 _99546 _99547 y g x s) = (term862 _99546 _99547 y g x s).
Proof. exact (eq_refl (term862 _99546 _99547 y g x s)). Qed.
Lemma lem3837569 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term864 _99546 _99547 y g x) = (term864 _99546 _99547 y g x).
Proof. exact (fun_ext (fun s : _99547 => @lem3837568 _99546 _99547 y g x s)). Qed.
Lemma lem3837570 {_99547 : Type'} : (@all _99547) = (@all _99547).
Proof. exact (eq_refl (@all _99547)). Qed.
Lemma lem3837571 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x : _99546) : (term865 _99546 _99547 y g x) = (term865 _99546 _99547 y g x).
Proof. exact (MK_COMB (@lem3837570 _99547) (@lem3837569 _99546 _99547 y g x)). Qed.
Lemma lem3837572 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) : (term866 _99546 _99547 g x) = (term866 _99546 _99547 g x).
Proof. exact (fun_ext (fun y : _99546 => @lem3837571 _99546 _99547 y g x)). Qed.
Lemma lem3837573 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3837574 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (x : _99546) : (term867 _99546 _99547 g x) = (term867 _99546 _99547 g x).
Proof. exact (MK_COMB (@lem3837573 _99546) (@lem3837572 _99546 _99547 g x)). Qed.
Lemma lem3837575 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) : (term868 _99546 _99547 g) = (term868 _99546 _99547 g).
Proof. exact (fun_ext (fun x : _99546 => @lem3837574 _99546 _99547 g x)). Qed.
Lemma lem3837576 {_99546 : Type'} : (@all _99546) = (@all _99546).
Proof. exact (eq_refl (@all _99546)). Qed.
Lemma lem3837577 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) : (term869 _99546 _99547 g) = (term869 _99546 _99547 g).
Proof. exact (MK_COMB (@lem3837576 _99546) (@lem3837575 _99546 _99547 g)). Qed.
Lemma lem3837578 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) : (term837 _99546 _99547 g) = (term869 _99546 _99547 g).
Proof. exact (TRANS (@lem3837561 _99546 _99547 g) (@lem3837577 _99546 _99547 g)). Qed.
Lemma lem3837579 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (h1 : term112 _99546 _99547 g) : term869 _99546 _99547 g.
Proof. exact (EQ_MP (@lem3837578 _99546 _99547 g) (@lem3836065 _99546 _99547 g h1)). Qed.
Lemma lem3837758 {_99546 _99547 : Type'} (_44389 : _99546) (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term275 _99546 _99547 x s f g) : term870 _99546 _99547 x s f g _44389.
Proof. exact (@lem3836897 _99546 _99547 x s f g h1 _44389). Qed.
Lemma lem3837759 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (_44389 : _99546) : (term870 _99546 _99547 x s f g _44389) = (term849 _99546 _99547 x s f g _44389).
Proof. exact (eq_refl (term870 _99546 _99547 x s f g _44389)). Qed.
Lemma lem3837760 {_99546 _99547 : Type'} (_44389 : _99546) (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term275 _99546 _99547 x s f g) : term849 _99546 _99547 x s f g _44389.
Proof. exact (EQ_MP (@lem3837759 _99546 _99547 x s f g _44389) (@lem3837758 _99546 _99547 _44389 x s f g h1)). Qed.
Lemma lem3837791 {_99546 _99547 : Type'} (_44400 : _99546) (f : type1411 _99546 _99547) (h1 : term112 _99546 _99547 f) : term871 _99546 _99547 f _44400.
Proof. exact (@lem3837238 _99546 _99547 f h1 _44400). Qed.
Lemma lem3837792 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (_44400 : _99546) : (term871 _99546 _99547 f _44400) = (term867 _99546 _99547 f _44400).
Proof. exact (eq_refl (term871 _99546 _99547 f _44400)). Qed.
Lemma lem3837793 {_99546 _99547 : Type'} (_44400 : _99546) (f : type1411 _99546 _99547) (h1 : term112 _99546 _99547 f) : term867 _99546 _99547 f _44400.
Proof. exact (EQ_MP (@lem3837792 _99546 _99547 f _44400) (@lem3837791 _99546 _99547 _44400 f h1)). Qed.
Lemma lem3837794 {_99546 _99547 : Type'} (_44400 : _99546) (_44401 : _99546) (f : type1411 _99546 _99547) (h1 : term112 _99546 _99547 f) : term872 _99546 _99547 f _44400 _44401.
Proof. exact (@lem3837793 _99546 _99547 _44400 f h1 _44401). Qed.
Lemma lem3837795 {_99546 _99547 : Type'} (_44401 : _99546) (f : type1411 _99546 _99547) (_44400 : _99546) : (term872 _99546 _99547 f _44400 _44401) = (term865 _99546 _99547 _44401 f _44400).
Proof. exact (eq_refl (term872 _99546 _99547 f _44400 _44401)). Qed.
Lemma lem3837796 {_99546 _99547 : Type'} (_44401 : _99546) (_44400 : _99546) (f : type1411 _99546 _99547) (h1 : term112 _99546 _99547 f) : term865 _99546 _99547 _44401 f _44400.
Proof. exact (EQ_MP (@lem3837795 _99546 _99547 _44401 f _44400) (@lem3837794 _99546 _99547 _44400 _44401 f h1)). Qed.
Lemma lem3837797 {_99546 _99547 : Type'} (_44401 : _99546) (_44400 : _99546) (_44402 : _99547) (f : type1411 _99546 _99547) (h1 : term112 _99546 _99547 f) : term873 _99546 _99547 _44401 f _44400 _44402.
Proof. exact (@lem3837796 _99546 _99547 _44401 _44400 f h1 _44402). Qed.
Lemma lem3837798 {_99546 _99547 : Type'} (_44401 : _99546) (f : type1411 _99546 _99547) (_44400 : _99546) (_44402 : _99547) : (term873 _99546 _99547 _44401 f _44400 _44402) = (term862 _99546 _99547 _44401 f _44400 _44402).
Proof. exact (eq_refl (term873 _99546 _99547 _44401 f _44400 _44402)). Qed.
Lemma lem3837830 {_99546 _99547 : Type'} (_44413 : _99546) (g : type1411 _99546 _99547) (h1 : term112 _99546 _99547 g) : term871 _99546 _99547 g _44413.
Proof. exact (@lem3837579 _99546 _99547 g h1 _44413). Qed.
Lemma lem3837831 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (_44413 : _99546) : (term871 _99546 _99547 g _44413) = (term867 _99546 _99547 g _44413).
Proof. exact (eq_refl (term871 _99546 _99547 g _44413)). Qed.
Lemma lem3837832 {_99546 _99547 : Type'} (_44413 : _99546) (g : type1411 _99546 _99547) (h1 : term112 _99546 _99547 g) : term867 _99546 _99547 g _44413.
Proof. exact (EQ_MP (@lem3837831 _99546 _99547 g _44413) (@lem3837830 _99546 _99547 _44413 g h1)). Qed.
Lemma lem3837833 {_99546 _99547 : Type'} (_44413 : _99546) (_44414 : _99546) (g : type1411 _99546 _99547) (h1 : term112 _99546 _99547 g) : term872 _99546 _99547 g _44413 _44414.
Proof. exact (@lem3837832 _99546 _99547 _44413 g h1 _44414). Qed.
Lemma lem3837834 {_99546 _99547 : Type'} (_44414 : _99546) (g : type1411 _99546 _99547) (_44413 : _99546) : (term872 _99546 _99547 g _44413 _44414) = (term865 _99546 _99547 _44414 g _44413).
Proof. exact (eq_refl (term872 _99546 _99547 g _44413 _44414)). Qed.
Lemma lem3837835 {_99546 _99547 : Type'} (_44414 : _99546) (_44413 : _99546) (g : type1411 _99546 _99547) (h1 : term112 _99546 _99547 g) : term865 _99546 _99547 _44414 g _44413.
Proof. exact (EQ_MP (@lem3837834 _99546 _99547 _44414 g _44413) (@lem3837833 _99546 _99547 _44413 _44414 g h1)). Qed.
Lemma lem3837836 {_99546 _99547 : Type'} (_44414 : _99546) (_44413 : _99546) (_44415 : _99547) (g : type1411 _99546 _99547) (h1 : term112 _99546 _99547 g) : term873 _99546 _99547 _44414 g _44413 _44415.
Proof. exact (@lem3837835 _99546 _99547 _44414 _44413 g h1 _44415). Qed.
Lemma lem3837837 {_99546 _99547 : Type'} (_44414 : _99546) (g : type1411 _99546 _99547) (_44413 : _99546) (_44415 : _99547) : (term873 _99546 _99547 _44414 g _44413 _44415) = (term862 _99546 _99547 _44414 g _44413 _44415).
Proof. exact (eq_refl (term873 _99546 _99547 _44414 g _44413 _44415)). Qed.
Lemma lem3837915 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x' : _99546) (h1 : term846 _99546 _99547 s f g x') : term843 _99546 _99547 f g x'.
Proof. exact (proj2 (@lem3836857 _99546 _99547 s f g x' h1)). Qed.
Lemma lem3838071 {_99546 _99547 : Type'} (_44389 : _99546) (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term275 _99546 _99547 x s f g) : term874 _99546 _99547 s f g _44389.
Proof. exact (proj2 (@lem3837760 _99546 _99547 _44389 x s f g h1)). Qed.
Lemma lem3838081 {_99546 _99547 : Type'} (_44401 : _99546) (_44400 : _99546) (_44402 : _99547) (f : type1411 _99546 _99547) (h1 : term112 _99546 _99547 f) : term862 _99546 _99547 _44401 f _44400 _44402.
Proof. exact (EQ_MP (@lem3837798 _99546 _99547 _44401 f _44400 _44402) (@lem3837797 _99546 _99547 _44401 _44400 _44402 f h1)). Qed.
Lemma lem3838091 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x' : _99546) (s' : _99547) (h1 : term839 _99546 _99547 y f x' s') : term838 _99546 _99547 y f x' s'.
Proof. exact (proj2 (@lem3836861 _99546 _99547 y f x' s' h1)). Qed.
Lemma lem3838263 {_99546 _99547 : Type'} (_44414 : _99546) (_44413 : _99546) (_44415 : _99547) (g : type1411 _99546 _99547) (h1 : term112 _99546 _99547 g) : term862 _99546 _99547 _44414 g _44413 _44415.
Proof. exact (EQ_MP (@lem3837837 _99546 _99547 _44414 g _44413 _44415) (@lem3837836 _99546 _99547 _44414 _44413 _44415 g h1)). Qed.
Lemma lem3838267 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x' : _99546) (s' : _99547) (h1 : term839 _99546 _99547 y g x' s') : term838 _99546 _99547 y g x' s'.
Proof. exact (proj2 (@lem3836862 _99546 _99547 y g x' s' h1)). Qed.
Lemma lem3838605 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x' : _99546) (h1 : term846 _99546 _99547 s f g x') : term819 _99546 x' s.
Proof. exact (proj1 (@lem3836857 _99546 _99547 s f g x' h1)). Qed.
Lemma lem3838606 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x' : _99546) (h1 : term846 _99546 _99547 s f g x') : term875 _99546 x' s.
Proof. exact (fun h0 : term820 _99546 x' s => @lem3838605 _99546 _99547 s f g x' h1). Qed.
Lemma lem3838608 (p : Prop) : (term876 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3838609 {_99546 : Type'} (x' : _99546) (s : _99546 -> Prop) : (term875 _99546 x' s) = (term819 _99546 x' s).
Proof. exact (@lem3838608 (term819 _99546 x' s)). Qed.
Lemma lem3838610 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x' : _99546) (h1 : term846 _99546 _99547 s f g x') : term819 _99546 x' s.
Proof. exact (EQ_MP (@lem3838609 _99546 x' s) (@lem3838606 _99546 _99547 s f g x' h1)). Qed.
Lemma lem3838616 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3838617 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (_44389 : _99546) (s : _99546 -> Prop) : (term874 _99546 _99547 s f g _44389) = (term877 _99546 _99547 f g _44389 s).
Proof. exact (@lem3838616 ((@I (_99546 -> _99547 -> _99547) f _44389) = (@I (_99546 -> _99547 -> _99547) g _44389)) (term820 _99546 _44389 s)). Qed.
Lemma lem3838625 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3838626 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (_44389 : _99546) (s : _99546 -> Prop) : (term878 _99546 _99547 s f g _44389) = (term879 _99546 _99547 f g _44389 s).
Proof. exact (MK_COMB (@lem3838625) (@lem3838617 _99546 _99547 f g _44389 s)). Qed.
Lemma lem3838634 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (_44389 : _99546) (s : _99546 -> Prop) : (term877 _99546 _99547 f g _44389 s) = (term877 _99546 _99547 f g _44389 s).
Proof. exact (eq_refl (term877 _99546 _99547 f g _44389 s)). Qed.
Lemma lem3838635 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (_44389 : _99546) (s : _99546 -> Prop) : ((term874 _99546 _99547 s f g _44389) = (term877 _99546 _99547 f g _44389 s)) = ((term877 _99546 _99547 f g _44389 s) = (term877 _99546 _99547 f g _44389 s)).
Proof. exact (MK_COMB (@lem3838626 _99546 _99547 f g _44389 s) (@lem3838634 _99546 _99547 f g _44389 s)). Qed.
Lemma lem3838637 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3838638 (x : Prop) : (x = x) = True.
Proof. exact (@lem3838637 Prop x). Qed.
Lemma lem3838639 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (_44389 : _99546) (s : _99546 -> Prop) : ((term877 _99546 _99547 f g _44389 s) = (term877 _99546 _99547 f g _44389 s)) = True.
Proof. exact (@lem3838638 (term877 _99546 _99547 f g _44389 s)). Qed.
Lemma lem3838640 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (_44389 : _99546) (s : _99546 -> Prop) : ((term874 _99546 _99547 s f g _44389) = (term877 _99546 _99547 f g _44389 s)) = True.
Proof. exact (TRANS (@lem3838635 _99546 _99547 f g _44389 s) (@lem3838639 _99546 _99547 f g _44389 s)). Qed.
Lemma lem3838641 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (_44389 : _99546) (s : _99546 -> Prop) : True = ((term874 _99546 _99547 s f g _44389) = (term877 _99546 _99547 f g _44389 s)).
Proof. exact (SYM (@lem3838640 _99546 _99547 f g _44389 s)). Qed.
Lemma lem3838642 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (_44389 : _99546) (s : _99546 -> Prop) : (term874 _99546 _99547 s f g _44389) = (term877 _99546 _99547 f g _44389 s).
Proof. exact (EQ_MP (@lem3838641 _99546 _99547 f g _44389 s) (@lem0)). Qed.
Lemma lem3838643 {_99546 _99547 : Type'} (_44389 : _99546) (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term275 _99546 _99547 x s f g) : term877 _99546 _99547 f g _44389 s.
Proof. exact (EQ_MP (@lem3838642 _99546 _99547 f g _44389 s) (@lem3838071 _99546 _99547 _44389 x s f g h1)). Qed.
Lemma lem3838645 (b : Prop) (a : Prop) : (a \/ b) = (term880 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3838646 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (_44389 : _99546) : (term877 _99546 _99547 f g _44389 s) = (term881 _99546 _99547 s f g _44389).
Proof. exact (@lem3838645 (term820 _99546 _44389 s) ((@I (_99546 -> _99547 -> _99547) f _44389) = (@I (_99546 -> _99547 -> _99547) g _44389))). Qed.
Lemma lem3838648 (a : Prop) : (term361 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3838649 {_99546 : Type'} (_44389 : _99546) (s : _99546 -> Prop) : (term882 _99546 _44389 s) = (term819 _99546 _44389 s).
Proof. exact (@lem3838648 (term819 _99546 _44389 s)). Qed.
Lemma lem3838650 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3838651 {_99546 : Type'} (_44389 : _99546) (s : _99546 -> Prop) : (term883 _99546 _44389 s) = (term884 _99546 _44389 s).
Proof. exact (MK_COMB (@lem3838650) (@lem3838649 _99546 _44389 s)). Qed.
Lemma lem3838652 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (_44389 : _99546) : ((@I (_99546 -> _99547 -> _99547) f _44389) = (@I (_99546 -> _99547 -> _99547) g _44389)) = ((@I (_99546 -> _99547 -> _99547) f _44389) = (@I (_99546 -> _99547 -> _99547) g _44389)).
Proof. exact (eq_refl ((@I (_99546 -> _99547 -> _99547) f _44389) = (@I (_99546 -> _99547 -> _99547) g _44389))). Qed.
Lemma lem3838653 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (_44389 : _99546) : (term881 _99546 _99547 s f g _44389) = (term885 _99546 _99547 s f g _44389).
Proof. exact (MK_COMB (@lem3838651 _99546 _44389 s) (@lem3838652 _99546 _99547 f g _44389)). Qed.
Lemma lem3838654 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (_44389 : _99546) : (term877 _99546 _99547 f g _44389 s) = (term885 _99546 _99547 s f g _44389).
Proof. exact (TRANS (@lem3838646 _99546 _99547 s f g _44389) (@lem3838653 _99546 _99547 s f g _44389)). Qed.
Lemma lem3838657 {_99546 _99547 : Type'} (_44389 : _99546) (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term275 _99546 _99547 x s f g) : term885 _99546 _99547 s f g _44389.
Proof. exact (EQ_MP (@lem3838654 _99546 _99547 s f g _44389) (@lem3838643 _99546 _99547 _44389 x s f g h1)). Qed.
Lemma lem3838658 {_99546 _99547 : Type'} (_44389 : _99546) (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term275 _99546 _99547 x s f g) : term885 _99546 _99547 s f g _44389.
Proof. exact (@lem3838657 _99546 _99547 _44389 x s f g h1). Qed.
Lemma lem3838659 {_99546 _99547 : Type'} (x' : _99546) (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term275 _99546 _99547 x s f g) : term885 _99546 _99547 s f g x'.
Proof. exact (@lem3838658 _99546 _99547 x' x s f g h1). Qed.
Lemma lem3838662 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x' : _99546) (h1 : term275 _99546 _99547 x s f g) (h2 : term846 _99546 _99547 s f g x') : (@I (_99546 -> _99547 -> _99547) f x') = (@I (_99546 -> _99547 -> _99547) g x').
Proof. exact (@lem3838659 _99546 _99547 x' x s f g h1 (@lem3838610 _99546 _99547 s f g x' h2)). Qed.
Lemma lem3838663 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x' : _99546) (h1 : term275 _99546 _99547 x s f g) (h2 : term846 _99546 _99547 s f g x') : term886 _99546 _99547 f g x'.
Proof. exact (fun h0 : term843 _99546 _99547 f g x' => @lem3838662 _99546 _99547 x s f g x' h1 h2). Qed.
Lemma lem3838665 (p : Prop) : (term876 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3838666 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x' : _99546) : (term886 _99546 _99547 f g x') = ((@I (_99546 -> _99547 -> _99547) f x') = (@I (_99546 -> _99547 -> _99547) g x')).
Proof. exact (@lem3838665 ((@I (_99546 -> _99547 -> _99547) f x') = (@I (_99546 -> _99547 -> _99547) g x'))). Qed.
Lemma lem3838667 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x' : _99546) (h1 : term275 _99546 _99547 x s f g) (h2 : term846 _99546 _99547 s f g x') : (@I (_99546 -> _99547 -> _99547) f x') = (@I (_99546 -> _99547 -> _99547) g x').
Proof. exact (EQ_MP (@lem3838666 _99546 _99547 f g x') (@lem3838663 _99546 _99547 x s f g x' h1 h2)). Qed.
Lemma lem3838670 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3838672 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x' : _99546) : (term843 _99546 _99547 f g x') = (term887 _99546 _99547 f g x').
Proof. exact (@lem3838670 ((@I (_99546 -> _99547 -> _99547) f x') = (@I (_99546 -> _99547 -> _99547) g x'))). Qed.
Lemma lem3838675 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x' : _99546) (h1 : term846 _99546 _99547 s f g x') : term887 _99546 _99547 f g x'.
Proof. exact (EQ_MP (@lem3838672 _99546 _99547 f g x') (@lem3837915 _99546 _99547 s f g x' h1)). Qed.
Lemma lem3838678 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x' : _99546) (h1 : term275 _99546 _99547 x s f g) (h2 : term846 _99546 _99547 s f g x') : False.
Proof. exact (@lem3838675 _99546 _99547 s f g x' h2 (@lem3838667 _99546 _99547 x s f g x' h1 h2)). Qed.
Lemma lem3838679 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x' : _99546) (h1 : term275 _99546 _99547 x s f g) (h2 : term846 _99546 _99547 s f g x') : term888.
Proof. exact (fun h0 : ~ False => @lem3838678 _99546 _99547 x s f g x' h1 h2). Qed.
Lemma lem3838681 (p : Prop) : (term876 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3838682 : term888 = False.
Proof. exact (@lem3838681 False). Qed.
Lemma lem3838683 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x' : _99546) (h1 : term275 _99546 _99547 x s f g) (h2 : term846 _99546 _99547 s f g x') : False.
Proof. exact (EQ_MP (@lem3838682) (@lem3838679 _99546 _99547 x s f g x' h1 h2)). Qed.
Lemma lem3838865 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x' : _99546) (s' : _99547) (h1 : term839 _99546 _99547 y f x' s') : term90 _99546 x' y.
Proof. exact (proj1 (@lem3836861 _99546 _99547 y f x' s' h1)). Qed.
Lemma lem3838866 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x' : _99546) (s' : _99547) (h1 : term839 _99546 _99547 y f x' s') : term889 _99546 x' y.
Proof. exact (fun h0 : x' = y => @lem3838865 _99546 _99547 y f x' s' h1). Qed.
Lemma lem3838868 (p : Prop) : (term890 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3838869 {_99546 : Type'} (x' : _99546) (y : _99546) : (term889 _99546 x' y) = (term90 _99546 x' y).
Proof. exact (@lem3838868 (x' = y)). Qed.
Lemma lem3838870 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x' : _99546) (s' : _99547) (h1 : term839 _99546 _99547 y f x' s') : term90 _99546 x' y.
Proof. exact (EQ_MP (@lem3838869 _99546 x' y) (@lem3838866 _99546 _99547 y f x' s' h1)). Qed.
Lemma lem3838885 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3838886 {_99546 _99547 : Type'} (_44401 : _99546) (f : type1411 _99546 _99547) (_44400 : _99546) (_44402 : _99547) : (term891 _99546 _99547 f _44402 _44400 _44401) = (term862 _99546 _99547 _44401 f _44400 _44402).
Proof. exact (@lem3838885 (_44400 = _44401) ((term829 _99546 _99547 _44400 f _44401 _44402) = (term829 _99546 _99547 _44401 f _44400 _44402))). Qed.
Lemma lem3838896 {_99546 _99547 : Type'} (_44401 : _99546) (f : type1411 _99546 _99547) (_44400 : _99546) (_44402 : _99547) : (term892 _99546 _99547 _44401 f _44400 _44402) = (term892 _99546 _99547 _44401 f _44400 _44402).
Proof. exact (eq_refl (term892 _99546 _99547 _44401 f _44400 _44402)). Qed.
Lemma lem3838897 {_99546 _99547 : Type'} (_44401 : _99546) (f : type1411 _99546 _99547) (_44400 : _99546) (_44402 : _99547) : ((term862 _99546 _99547 _44401 f _44400 _44402) = (term891 _99546 _99547 f _44402 _44400 _44401)) = ((term862 _99546 _99547 _44401 f _44400 _44402) = (term862 _99546 _99547 _44401 f _44400 _44402)).
Proof. exact (MK_COMB (@lem3838896 _99546 _99547 _44401 f _44400 _44402) (@lem3838886 _99546 _99547 _44401 f _44400 _44402)). Qed.
Lemma lem3838899 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3838900 (x : Prop) : (x = x) = True.
Proof. exact (@lem3838899 Prop x). Qed.
Lemma lem3838901 {_99546 _99547 : Type'} (_44401 : _99546) (f : type1411 _99546 _99547) (_44400 : _99546) (_44402 : _99547) : ((term862 _99546 _99547 _44401 f _44400 _44402) = (term862 _99546 _99547 _44401 f _44400 _44402)) = True.
Proof. exact (@lem3838900 (term862 _99546 _99547 _44401 f _44400 _44402)). Qed.
Lemma lem3838902 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (_44402 : _99547) (_44400 : _99546) (_44401 : _99546) : ((term862 _99546 _99547 _44401 f _44400 _44402) = (term891 _99546 _99547 f _44402 _44400 _44401)) = True.
Proof. exact (TRANS (@lem3838897 _99546 _99547 _44401 f _44400 _44402) (@lem3838901 _99546 _99547 _44401 f _44400 _44402)). Qed.
Lemma lem3838903 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (_44402 : _99547) (_44400 : _99546) (_44401 : _99546) : True = ((term862 _99546 _99547 _44401 f _44400 _44402) = (term891 _99546 _99547 f _44402 _44400 _44401)).
Proof. exact (SYM (@lem3838902 _99546 _99547 f _44402 _44400 _44401)). Qed.
Lemma lem3838904 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (_44402 : _99547) (_44400 : _99546) (_44401 : _99546) : (term862 _99546 _99547 _44401 f _44400 _44402) = (term891 _99546 _99547 f _44402 _44400 _44401).
Proof. exact (EQ_MP (@lem3838903 _99546 _99547 f _44402 _44400 _44401) (@lem0)). Qed.
Lemma lem3838905 {_99546 _99547 : Type'} (_44402 : _99547) (_44400 : _99546) (_44401 : _99546) (f : type1411 _99546 _99547) (h1 : term112 _99546 _99547 f) : term891 _99546 _99547 f _44402 _44400 _44401.
Proof. exact (EQ_MP (@lem3838904 _99546 _99547 f _44402 _44400 _44401) (@lem3838081 _99546 _99547 _44401 _44400 _44402 f h1)). Qed.
Lemma lem3838907 (b : Prop) (a : Prop) : (a \/ b) = (term880 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3838910 {_99546 _99547 : Type'} (_44401 : _99546) (f : type1411 _99546 _99547) (_44400 : _99546) (_44402 : _99547) : (term891 _99546 _99547 f _44402 _44400 _44401) = (term893 _99546 _99547 _44401 f _44400 _44402).
Proof. exact (@lem3838907 (_44400 = _44401) ((term829 _99546 _99547 _44400 f _44401 _44402) = (term829 _99546 _99547 _44401 f _44400 _44402))). Qed.
Lemma lem3838913 {_99546 _99547 : Type'} (_44401 : _99546) (_44400 : _99546) (_44402 : _99547) (f : type1411 _99546 _99547) (h1 : term112 _99546 _99547 f) : term893 _99546 _99547 _44401 f _44400 _44402.
Proof. exact (EQ_MP (@lem3838910 _99546 _99547 _44401 f _44400 _44402) (@lem3838905 _99546 _99547 _44402 _44400 _44401 f h1)). Qed.
Lemma lem3838914 {_99546 _99547 : Type'} (_44401 : _99546) (_44400 : _99546) (_44402 : _99547) (f : type1411 _99546 _99547) (h1 : term112 _99546 _99547 f) : term893 _99546 _99547 _44401 f _44400 _44402.
Proof. exact (@lem3838913 _99546 _99547 _44401 _44400 _44402 f h1). Qed.
Lemma lem3838915 {_99546 _99547 : Type'} (y : _99546) (x' : _99546) (_44402 : _99547) (f : type1411 _99546 _99547) (h1 : term112 _99546 _99547 f) : term893 _99546 _99547 y f x' _44402.
Proof. exact (@lem3838914 _99546 _99547 y x' _44402 f h1). Qed.
Lemma lem3838918 {_99546 _99547 : Type'} (_44402 : _99547) (y : _99546) (f : type1411 _99546 _99547) (x' : _99546) (s' : _99547) (h1 : term112 _99546 _99547 f) (h2 : term839 _99546 _99547 y f x' s') : (term829 _99546 _99547 x' f y _44402) = (term829 _99546 _99547 y f x' _44402).
Proof. exact (@lem3838915 _99546 _99547 y x' _44402 f h1 (@lem3838870 _99546 _99547 y f x' s' h2)). Qed.
Lemma lem3838919 {_99546 _99547 : Type'} (_44402 : _99547) (y : _99546) (f : type1411 _99546 _99547) (x' : _99546) (s' : _99547) (h1 : term112 _99546 _99547 f) (h2 : term839 _99546 _99547 y f x' s') : (term829 _99546 _99547 x' f y _44402) = (term829 _99546 _99547 y f x' _44402).
Proof. exact (@lem3838918 _99546 _99547 _44402 y f x' s' h1 h2). Qed.
Lemma lem3838920 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x' : _99546) (s' : _99547) (h1 : term112 _99546 _99547 f) (h2 : term839 _99546 _99547 y f x' s') : (term829 _99546 _99547 x' f y s') = (term829 _99546 _99547 y f x' s').
Proof. exact (@lem3838919 _99546 _99547 s' y f x' s' h1 h2). Qed.
Lemma lem3838921 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x' : _99546) (s' : _99547) (h1 : term112 _99546 _99547 f) (h2 : term839 _99546 _99547 y f x' s') : term894 _99546 _99547 y f x' s'.
Proof. exact (fun h0 : term838 _99546 _99547 y f x' s' => @lem3838920 _99546 _99547 y f x' s' h1 h2). Qed.
Lemma lem3838923 (p : Prop) : (term876 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3838924 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x' : _99546) (s' : _99547) : (term894 _99546 _99547 y f x' s') = ((term829 _99546 _99547 x' f y s') = (term829 _99546 _99547 y f x' s')).
Proof. exact (@lem3838923 ((term829 _99546 _99547 x' f y s') = (term829 _99546 _99547 y f x' s'))). Qed.
Lemma lem3838925 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x' : _99546) (s' : _99547) (h1 : term112 _99546 _99547 f) (h2 : term839 _99546 _99547 y f x' s') : (term829 _99546 _99547 x' f y s') = (term829 _99546 _99547 y f x' s').
Proof. exact (EQ_MP (@lem3838924 _99546 _99547 y f x' s') (@lem3838921 _99546 _99547 y f x' s' h1 h2)). Qed.
Lemma lem3838928 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3838930 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x' : _99546) (s' : _99547) : (term838 _99546 _99547 y f x' s') = (term895 _99546 _99547 y f x' s').
Proof. exact (@lem3838928 ((term829 _99546 _99547 x' f y s') = (term829 _99546 _99547 y f x' s'))). Qed.
Lemma lem3838933 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x' : _99546) (s' : _99547) (h1 : term839 _99546 _99547 y f x' s') : term895 _99546 _99547 y f x' s'.
Proof. exact (EQ_MP (@lem3838930 _99546 _99547 y f x' s') (@lem3838091 _99546 _99547 y f x' s' h1)). Qed.
Lemma lem3838936 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x' : _99546) (s' : _99547) (h1 : term112 _99546 _99547 f) (h2 : term839 _99546 _99547 y f x' s') : False.
Proof. exact (@lem3838933 _99546 _99547 y f x' s' h2 (@lem3838925 _99546 _99547 y f x' s' h1 h2)). Qed.
Lemma lem3838937 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x' : _99546) (s' : _99547) (h1 : term112 _99546 _99547 f) (h2 : term839 _99546 _99547 y f x' s') : term888.
Proof. exact (fun h0 : ~ False => @lem3838936 _99546 _99547 y f x' s' h1 h2). Qed.
Lemma lem3838939 (p : Prop) : (term876 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3838940 : term888 = False.
Proof. exact (@lem3838939 False). Qed.
Lemma lem3838941 {_99546 _99547 : Type'} (y : _99546) (f : type1411 _99546 _99547) (x' : _99546) (s' : _99547) (h1 : term112 _99546 _99547 f) (h2 : term839 _99546 _99547 y f x' s') : False.
Proof. exact (EQ_MP (@lem3838940) (@lem3838937 _99546 _99547 y f x' s' h1 h2)). Qed.
Lemma lem3839123 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x' : _99546) (s' : _99547) (h1 : term839 _99546 _99547 y g x' s') : term90 _99546 x' y.
Proof. exact (proj1 (@lem3836862 _99546 _99547 y g x' s' h1)). Qed.
Lemma lem3839124 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x' : _99546) (s' : _99547) (h1 : term839 _99546 _99547 y g x' s') : term889 _99546 x' y.
Proof. exact (fun h0 : x' = y => @lem3839123 _99546 _99547 y g x' s' h1). Qed.
Lemma lem3839126 (p : Prop) : (term890 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3839127 {_99546 : Type'} (x' : _99546) (y : _99546) : (term889 _99546 x' y) = (term90 _99546 x' y).
Proof. exact (@lem3839126 (x' = y)). Qed.
Lemma lem3839128 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x' : _99546) (s' : _99547) (h1 : term839 _99546 _99547 y g x' s') : term90 _99546 x' y.
Proof. exact (EQ_MP (@lem3839127 _99546 x' y) (@lem3839124 _99546 _99547 y g x' s' h1)). Qed.
Lemma lem3839143 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3839144 {_99546 _99547 : Type'} (_44414 : _99546) (g : type1411 _99546 _99547) (_44413 : _99546) (_44415 : _99547) : (term891 _99546 _99547 g _44415 _44413 _44414) = (term862 _99546 _99547 _44414 g _44413 _44415).
Proof. exact (@lem3839143 (_44413 = _44414) ((term829 _99546 _99547 _44413 g _44414 _44415) = (term829 _99546 _99547 _44414 g _44413 _44415))). Qed.
Lemma lem3839154 {_99546 _99547 : Type'} (_44414 : _99546) (g : type1411 _99546 _99547) (_44413 : _99546) (_44415 : _99547) : (term892 _99546 _99547 _44414 g _44413 _44415) = (term892 _99546 _99547 _44414 g _44413 _44415).
Proof. exact (eq_refl (term892 _99546 _99547 _44414 g _44413 _44415)). Qed.
Lemma lem3839155 {_99546 _99547 : Type'} (_44414 : _99546) (g : type1411 _99546 _99547) (_44413 : _99546) (_44415 : _99547) : ((term862 _99546 _99547 _44414 g _44413 _44415) = (term891 _99546 _99547 g _44415 _44413 _44414)) = ((term862 _99546 _99547 _44414 g _44413 _44415) = (term862 _99546 _99547 _44414 g _44413 _44415)).
Proof. exact (MK_COMB (@lem3839154 _99546 _99547 _44414 g _44413 _44415) (@lem3839144 _99546 _99547 _44414 g _44413 _44415)). Qed.
Lemma lem3839157 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3839158 (x : Prop) : (x = x) = True.
Proof. exact (@lem3839157 Prop x). Qed.
Lemma lem3839159 {_99546 _99547 : Type'} (_44414 : _99546) (g : type1411 _99546 _99547) (_44413 : _99546) (_44415 : _99547) : ((term862 _99546 _99547 _44414 g _44413 _44415) = (term862 _99546 _99547 _44414 g _44413 _44415)) = True.
Proof. exact (@lem3839158 (term862 _99546 _99547 _44414 g _44413 _44415)). Qed.
Lemma lem3839160 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (_44415 : _99547) (_44413 : _99546) (_44414 : _99546) : ((term862 _99546 _99547 _44414 g _44413 _44415) = (term891 _99546 _99547 g _44415 _44413 _44414)) = True.
Proof. exact (TRANS (@lem3839155 _99546 _99547 _44414 g _44413 _44415) (@lem3839159 _99546 _99547 _44414 g _44413 _44415)). Qed.
Lemma lem3839161 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (_44415 : _99547) (_44413 : _99546) (_44414 : _99546) : True = ((term862 _99546 _99547 _44414 g _44413 _44415) = (term891 _99546 _99547 g _44415 _44413 _44414)).
Proof. exact (SYM (@lem3839160 _99546 _99547 g _44415 _44413 _44414)). Qed.
Lemma lem3839162 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (_44415 : _99547) (_44413 : _99546) (_44414 : _99546) : (term862 _99546 _99547 _44414 g _44413 _44415) = (term891 _99546 _99547 g _44415 _44413 _44414).
Proof. exact (EQ_MP (@lem3839161 _99546 _99547 g _44415 _44413 _44414) (@lem0)). Qed.
Lemma lem3839163 {_99546 _99547 : Type'} (_44415 : _99547) (_44413 : _99546) (_44414 : _99546) (g : type1411 _99546 _99547) (h1 : term112 _99546 _99547 g) : term891 _99546 _99547 g _44415 _44413 _44414.
Proof. exact (EQ_MP (@lem3839162 _99546 _99547 g _44415 _44413 _44414) (@lem3838263 _99546 _99547 _44414 _44413 _44415 g h1)). Qed.
Lemma lem3839165 (b : Prop) (a : Prop) : (a \/ b) = (term880 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3839168 {_99546 _99547 : Type'} (_44414 : _99546) (g : type1411 _99546 _99547) (_44413 : _99546) (_44415 : _99547) : (term891 _99546 _99547 g _44415 _44413 _44414) = (term893 _99546 _99547 _44414 g _44413 _44415).
Proof. exact (@lem3839165 (_44413 = _44414) ((term829 _99546 _99547 _44413 g _44414 _44415) = (term829 _99546 _99547 _44414 g _44413 _44415))). Qed.
Lemma lem3839171 {_99546 _99547 : Type'} (_44414 : _99546) (_44413 : _99546) (_44415 : _99547) (g : type1411 _99546 _99547) (h1 : term112 _99546 _99547 g) : term893 _99546 _99547 _44414 g _44413 _44415.
Proof. exact (EQ_MP (@lem3839168 _99546 _99547 _44414 g _44413 _44415) (@lem3839163 _99546 _99547 _44415 _44413 _44414 g h1)). Qed.
Lemma lem3839172 {_99546 _99547 : Type'} (_44414 : _99546) (_44413 : _99546) (_44415 : _99547) (g : type1411 _99546 _99547) (h1 : term112 _99546 _99547 g) : term893 _99546 _99547 _44414 g _44413 _44415.
Proof. exact (@lem3839171 _99546 _99547 _44414 _44413 _44415 g h1). Qed.
Lemma lem3839173 {_99546 _99547 : Type'} (y : _99546) (x' : _99546) (_44415 : _99547) (g : type1411 _99546 _99547) (h1 : term112 _99546 _99547 g) : term893 _99546 _99547 y g x' _44415.
Proof. exact (@lem3839172 _99546 _99547 y x' _44415 g h1). Qed.
Lemma lem3839176 {_99546 _99547 : Type'} (_44415 : _99547) (y : _99546) (g : type1411 _99546 _99547) (x' : _99546) (s' : _99547) (h1 : term112 _99546 _99547 g) (h2 : term839 _99546 _99547 y g x' s') : (term829 _99546 _99547 x' g y _44415) = (term829 _99546 _99547 y g x' _44415).
Proof. exact (@lem3839173 _99546 _99547 y x' _44415 g h1 (@lem3839128 _99546 _99547 y g x' s' h2)). Qed.
Lemma lem3839177 {_99546 _99547 : Type'} (_44415 : _99547) (y : _99546) (g : type1411 _99546 _99547) (x' : _99546) (s' : _99547) (h1 : term112 _99546 _99547 g) (h2 : term839 _99546 _99547 y g x' s') : (term829 _99546 _99547 x' g y _44415) = (term829 _99546 _99547 y g x' _44415).
Proof. exact (@lem3839176 _99546 _99547 _44415 y g x' s' h1 h2). Qed.
Lemma lem3839178 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x' : _99546) (s' : _99547) (h1 : term112 _99546 _99547 g) (h2 : term839 _99546 _99547 y g x' s') : (term829 _99546 _99547 x' g y s') = (term829 _99546 _99547 y g x' s').
Proof. exact (@lem3839177 _99546 _99547 s' y g x' s' h1 h2). Qed.
Lemma lem3839179 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x' : _99546) (s' : _99547) (h1 : term112 _99546 _99547 g) (h2 : term839 _99546 _99547 y g x' s') : term894 _99546 _99547 y g x' s'.
Proof. exact (fun h0 : term838 _99546 _99547 y g x' s' => @lem3839178 _99546 _99547 y g x' s' h1 h2). Qed.
Lemma lem3839181 (p : Prop) : (term876 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3839182 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x' : _99546) (s' : _99547) : (term894 _99546 _99547 y g x' s') = ((term829 _99546 _99547 x' g y s') = (term829 _99546 _99547 y g x' s')).
Proof. exact (@lem3839181 ((term829 _99546 _99547 x' g y s') = (term829 _99546 _99547 y g x' s'))). Qed.
Lemma lem3839183 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x' : _99546) (s' : _99547) (h1 : term112 _99546 _99547 g) (h2 : term839 _99546 _99547 y g x' s') : (term829 _99546 _99547 x' g y s') = (term829 _99546 _99547 y g x' s').
Proof. exact (EQ_MP (@lem3839182 _99546 _99547 y g x' s') (@lem3839179 _99546 _99547 y g x' s' h1 h2)). Qed.
Lemma lem3839186 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3839188 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x' : _99546) (s' : _99547) : (term838 _99546 _99547 y g x' s') = (term895 _99546 _99547 y g x' s').
Proof. exact (@lem3839186 ((term829 _99546 _99547 x' g y s') = (term829 _99546 _99547 y g x' s'))). Qed.
Lemma lem3839191 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x' : _99546) (s' : _99547) (h1 : term839 _99546 _99547 y g x' s') : term895 _99546 _99547 y g x' s'.
Proof. exact (EQ_MP (@lem3839188 _99546 _99547 y g x' s') (@lem3838267 _99546 _99547 y g x' s' h1)). Qed.
Lemma lem3839194 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x' : _99546) (s' : _99547) (h1 : term112 _99546 _99547 g) (h2 : term839 _99546 _99547 y g x' s') : False.
Proof. exact (@lem3839191 _99546 _99547 y g x' s' h2 (@lem3839183 _99546 _99547 y g x' s' h1 h2)). Qed.
Lemma lem3839195 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x' : _99546) (s' : _99547) (h1 : term112 _99546 _99547 g) (h2 : term839 _99546 _99547 y g x' s') : term888.
Proof. exact (fun h0 : ~ False => @lem3839194 _99546 _99547 y g x' s' h1 h2). Qed.
Lemma lem3839197 (p : Prop) : (term876 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3839198 : term888 = False.
Proof. exact (@lem3839197 False). Qed.
Lemma lem3839199 {_99546 _99547 : Type'} (y : _99546) (g : type1411 _99546 _99547) (x' : _99546) (s' : _99547) (h1 : term112 _99546 _99547 g) (h2 : term839 _99546 _99547 y g x' s') : False.
Proof. exact (EQ_MP (@lem3839198) (@lem3839195 _99546 _99547 y g x' s' h1 h2)). Qed.
Lemma lem3839200 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x' : _99546) (s' : _99547) (h1 : term112 _99546 _99547 f) (h2 : term112 _99546 _99547 g) (h3 : term841 _99546 _99547 f y g x' s') : False.
Proof. exact (or_elim (@lem3836858 _99546 _99547 f y g x' s' h3) (fun h0 : term839 _99546 _99547 y f x' s' => @lem3838941 _99546 _99547 y f x' s' h1 h0) (fun h0 : term839 _99546 _99547 y g x' s' => @lem3839199 _99546 _99547 y g x' s' h2 h0)). Qed.
Lemma lem3839201 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x' : _99546) (s' : _99547) (h1 : term112 _99546 _99547 f) (h2 : term112 _99546 _99547 g) (h3 : term275 _99546 _99547 x s f g) (h4 : term560 _99546 _99547 s f y g x' s') : False.
Proof. exact (or_elim (@lem3836275 _99546 _99547 s f y g x' s' h4) (fun h0 : term846 _99546 _99547 s f g x' => @lem3838683 _99546 _99547 x s f g x' h3 h0) (fun h0 : term841 _99546 _99547 f y g x' s' => @lem3839200 _99546 _99547 f y g x' s' h1 h2 h0)). Qed.
Lemma lem3839202 {_99546 _99547 : Type'} (x : _99546) (y' : type427 _99546 _99547) (x'' : type427 _99546 _99547) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x' : _99546) (s' : _99547) (h1 : term112 _99546 _99547 f) (h2 : term112 _99546 _99547 g) (h3 : term275 _99546 _99547 x s f g) (h4 : term772 _99546 _99547 y' x'' s) (h5 : term560 _99546 _99547 s f y g x' s') : False.
Proof. exact (ex_elim (@lem3835808 _99546 _99547 y' x'' s h4) (fun s'' : type428 _99546 _99547 => fun h0 : term771 _99546 _99547 y' x'' s s'' => @lem3839201 _99546 _99547 x s f y g x' s' h1 h2 h3 h5)). Qed.
Lemma lem3839203 {_99546 _99547 : Type'} (x : _99546) (x'' : type427 _99546 _99547) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x' : _99546) (s' : _99547) (h1 : term112 _99546 _99547 f) (h2 : term112 _99546 _99547 g) (h3 : term275 _99546 _99547 x s f g) (h4 : term774 _99546 _99547 x'' s) (h5 : term560 _99546 _99547 s f y g x' s') : False.
Proof. exact (ex_elim (@lem3835807 _99546 _99547 x'' s h4) (fun y' : type427 _99546 _99547 => fun h0 : term773 _99546 _99547 x'' s y' => @lem3839202 _99546 _99547 x y' x'' s f y g x' s' h1 h2 h3 h0 h5)). Qed.
Lemma lem3839204 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x' : _99546) (s' : _99547) (h1 : term112 _99546 _99547 f) (h2 : term112 _99546 _99547 g) (h3 : term275 _99546 _99547 x s f g) (h4 : term150 _99546 _99547 s) (h5 : term560 _99546 _99547 s f y g x' s') : False.
Proof. exact (ex_elim (@lem3835004 _99546 _99547 s h4) (fun x'' : type427 _99546 _99547 => fun h0 : term775 _99546 _99547 s x'' => @lem3839203 _99546 _99547 x x'' s f y g x' s' h1 h2 h3 h0 h5)). Qed.
Lemma lem3839205 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (y : _99546) (g : type1411 _99546 _99547) (x' : _99546) (h1 : term112 _99546 _99547 f) (h2 : term112 _99546 _99547 g) (h3 : term275 _99546 _99547 x s f g) (h4 : term150 _99546 _99547 s) (h5 : term563 _99546 _99547 s f y g x') : False.
Proof. exact (ex_elim (@lem3835805 _99546 _99547 s f y g x' h5) (fun s' : _99547 => fun h0 : term562 _99546 _99547 s f y g x' s' => @lem3839204 _99546 _99547 x s f y g x' s' h1 h2 h3 h4 h0)). Qed.
Lemma lem3839206 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x' : _99546) (h1 : term112 _99546 _99547 f) (h2 : term112 _99546 _99547 g) (h3 : term275 _99546 _99547 x s f g) (h4 : term150 _99546 _99547 s) (h5 : term565 _99546 _99547 s f g x') : False.
Proof. exact (ex_elim (@lem3835804 _99546 _99547 s f g x' h5) (fun y : _99546 => fun h0 : term564 _99546 _99547 s f g x' y => @lem3839205 _99546 _99547 x s f y g x' h1 h2 h3 h4 h0)). Qed.
Lemma lem3839207 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term112 _99546 _99547 f) (h2 : term112 _99546 _99547 g) (h3 : term275 _99546 _99547 x s f g) (h4 : term150 _99546 _99547 s) (h5 : term355 _99546 _99547 s f g) : False.
Proof. exact (ex_elim (@lem3835803 _99546 _99547 s f g h5) (fun x' : _99546 => fun h0 : term566 _99546 _99547 s f g x' => @lem3839206 _99546 _99547 x s f g x' h1 h2 h3 h4 h0)). Qed.
Lemma lem3839208 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term112 _99546 _99547 f) (h2 : term112 _99546 _99547 g) (h3 : term275 _99546 _99547 x s f g) (h4 : term150 _99546 _99547 s) (h5 : term355 _99546 _99547 s f g) : (term355 _99546 _99547 s f g) = False.
Proof. exact (prop_ext (fun h6 : term355 _99546 _99547 s f g => @lem3839207 _99546 _99547 x s f g h1 h2 h3 h4 h5) (fun h6 : False => @lem3834156 _99546 _99547 s f g h5)). Qed.
Lemma lem3839209 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term112 _99546 _99547 f) (h2 : term112 _99546 _99547 g) (h3 : term275 _99546 _99547 x s f g) (h4 : term150 _99546 _99547 s) (h5 : term355 _99546 _99547 s f g) : False.
Proof. exact (EQ_MP (@lem3839208 _99546 _99547 x s f g h1 h2 h3 h4 h5) (@lem3834156 _99546 _99547 s f g h5)). Qed.
Lemma lem3839210 {_99546 _99547 : Type'} (x : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) (h1 : term112 _99546 _99547 f) (h2 : term112 _99546 _99547 g) (h3 : term275 _99546 _99547 x s f g) (h4 : term150 _99546 _99547 s) : term354 _99546 _99547 s f g.
Proof. exact (fun h0 : term355 _99546 _99547 s f g => @lem3839209 _99546 _99547 x s f g h1 h2 h3 h4 h0). Qed.
Lemma lem3839211 {_99546 _99547 : Type'} (x : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) (h1 : term112 _99546 _99547 f) (h2 : term112 _99546 _99547 g) (h3 : term275 _99546 _99547 x s f g) (h4 : term150 _99546 _99547 s) : term44 _99546 _99547 s f g.
Proof. exact (EQ_MP (@lem3834155 _99546 _99547 s f g) (@lem3839210 _99546 _99547 x f g s h1 h2 h3 h4)). Qed.
Lemma lem3839212 {_99546 _99547 : Type'} (x : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) (h1 : term112 _99546 _99547 f) (h2 : term275 _99546 _99547 x s f g) (h3 : term150 _99546 _99547 s) : term364 _99546 _99547 s f g.
Proof. exact (fun h0 : term112 _99546 _99547 g => @lem3839211 _99546 _99547 x f g s h1 h0 h2 h3). Qed.
Lemma lem3839213 {_99546 _99547 : Type'} (x : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) (h1 : term275 _99546 _99547 x s f g) (h2 : term150 _99546 _99547 s) : term366 _99546 _99547 s f g.
Proof. exact (fun h0 : term112 _99546 _99547 f => @lem3839212 _99546 _99547 x f g s h0 h1 h2). Qed.
Lemma lem3839214 {_99546 _99547 : Type'} (x : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) (h1 : term150 _99546 _99547 s) : term369 _99546 _99547 x s f g.
Proof. exact (fun h0 : term275 _99546 _99547 x s f g => @lem3839213 _99546 _99547 x f g s h0 h1). Qed.
Lemma lem3839215 {_99546 _99547 : Type'} (x : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) (h1 : term150 _99546 _99547 s) : term371 _99546 _99547 x s f g.
Proof. exact (fun h0 : @FINITE _99546 s => @lem3839214 _99546 _99547 x f g s h1). Qed.
Lemma lem3839216 {_99546 _99547 : Type'} (x : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) (h1 : term150 _99546 _99547 s) : term374 _99546 _99547 x s f g.
Proof. exact (fun h0 : term252 _99546 x s => @lem3839215 _99546 _99547 x f g s h1). Qed.
Lemma lem3839217 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : term376 _99546 _99547 x s f g.
Proof. exact (fun h0 : term150 _99546 _99547 s => @lem3839216 _99546 _99547 x f g s h0). Qed.
Lemma lem3839222 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : term380 _99546 _99547 s f g.
Proof. exact (fun x : _99546 => @lem3839217 _99546 _99547 x s f g). Qed.
Lemma lem3839227 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : term384 _99546 _99547 f g.
Proof. exact (fun s : _99546 -> Prop => @lem3839222 _99546 _99547 s f g). Qed.
Lemma lem3839232 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) : term388 _99546 _99547 g.
Proof. exact (fun f : type1411 _99546 _99547 => @lem3839227 _99546 _99547 f g). Qed.
Lemma lem3839237 {_99546 _99547 : Type'} : term392 _99546 _99547.
Proof. exact (fun g : type1411 _99546 _99547 => @lem3839232 _99546 _99547 g). Qed.
Lemma lem3839238 {_99546 _99547 : Type'} : term391 _99546 _99547.
Proof. exact (EQ_MP (@lem3834145 _99546 _99547) (@lem3839237 _99546 _99547)). Qed.
Lemma lem3839239 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) : term896 _99546 _99547 g.
Proof. exact (@lem3839238 _99546 _99547 g). Qed.
Lemma lem3839240 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) : (term896 _99546 _99547 g) = (term387 _99546 _99547 g).
Proof. exact (eq_refl (term896 _99546 _99547 g)). Qed.
Lemma lem3839241 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) : term387 _99546 _99547 g.
Proof. exact (EQ_MP (@lem3839240 _99546 _99547 g) (@lem3839239 _99546 _99547 g)). Qed.
Lemma lem3839242 {_99546 _99547 : Type'} (g : type1411 _99546 _99547) (f : type1411 _99546 _99547) : term897 _99546 _99547 g f.
Proof. exact (@lem3839241 _99546 _99547 g f). Qed.
Lemma lem3839243 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term897 _99546 _99547 g f) = (term383 _99546 _99547 f g).
Proof. exact (eq_refl (term897 _99546 _99547 g f)). Qed.
Lemma lem3839244 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : term383 _99546 _99547 f g.
Proof. exact (EQ_MP (@lem3839243 _99546 _99547 f g) (@lem3839242 _99546 _99547 g f)). Qed.
Lemma lem3839245 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) : term898 _99546 _99547 f g s.
Proof. exact (@lem3839244 _99546 _99547 f g s). Qed.
Lemma lem3839246 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term898 _99546 _99547 f g s) = (term379 _99546 _99547 s f g).
Proof. exact (eq_refl (term898 _99546 _99547 f g s)). Qed.
Lemma lem3839247 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : term379 _99546 _99547 s f g.
Proof. exact (EQ_MP (@lem3839246 _99546 _99547 s f g) (@lem3839245 _99546 _99547 f g s)). Qed.
Lemma lem3839248 {_99546 _99547 : Type'} (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) : term899 _99546 _99547 s f g x.
Proof. exact (@lem3839247 _99546 _99547 s f g x). Qed.
Lemma lem3839249 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : (term899 _99546 _99547 s f g x) = (term356 _99546 _99547 x s f g).
Proof. exact (eq_refl (term899 _99546 _99547 s f g x)). Qed.
Lemma lem3839250 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : term356 _99546 _99547 x s f g.
Proof. exact (EQ_MP (@lem3839249 _99546 _99547 x s f g) (@lem3839248 _99546 _99547 s f g x)). Qed.
Lemma lem3839252 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) : term356 _99546 _99547 x s f g.
Proof. exact (@lem3833531 _99546 _99547 x s f g (@lem3839250 _99546 _99547 x s f g)). Qed.
Lemma lem3839253 {_99546 _99547 : Type'} (x : _99546) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (s : _99546 -> Prop) (h1 : term150 _99546 _99547 s) : term373 _99546 _99547 x s f g.
Proof. exact (@lem3839252 _99546 _99547 x s f g (@lem3833073 _99546 _99547 s h1)). Qed.
Lemma lem3839254 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term150 _99546 _99547 s) (h2 : term252 _99546 x s) : term370 _99546 _99547 x s f g.
Proof. exact (@lem3839253 _99546 _99547 x f g s h1 (@lem3833075 _99546 x s h2)). Qed.
Lemma lem3839255 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term150 _99546 _99547 s) (h2 : @FINITE _99546 s) (h3 : term252 _99546 x s) : term368 _99546 _99547 x s f g.
Proof. exact (@lem3839254 _99546 _99547 f g x s h1 h3 (@lem3833074 _99546 s h2)). Qed.
Lemma lem3839256 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term275 _99546 _99547 x s f g) (h2 : term150 _99546 _99547 s) (h3 : @FINITE _99546 s) (h4 : term252 _99546 x s) : term365 _99546 _99547 s f g.
Proof. exact (@lem3839255 _99546 _99547 f g x s h2 h3 h4 (@lem3833078 _99546 _99547 x s f g h1)). Qed.
Lemma lem3839257 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term112 _99546 _99547 f) (h2 : term275 _99546 _99547 x s f g) (h3 : term150 _99546 _99547 s) (h4 : @FINITE _99546 s) (h5 : term252 _99546 x s) : term363 _99546 _99547 s f g.
Proof. exact (@lem3839256 _99546 _99547 f g x s h2 h3 h4 h5 (@lem3833080 _99546 _99547 f h1)). Qed.
Lemma lem3839258 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term112 _99546 _99547 f) (h2 : term112 _99546 _99547 g) (h3 : term275 _99546 _99547 x s f g) (h4 : term150 _99546 _99547 s) (h5 : @FINITE _99546 s) (h6 : term252 _99546 x s) : term354 _99546 _99547 s f g.
Proof. exact (@lem3839257 _99546 _99547 f g x s h1 h3 h4 h5 h6 (@lem3833079 _99546 _99547 g h2)). Qed.
Lemma lem3839259 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term112 _99546 _99547 f) (h2 : term112 _99546 _99547 g) (h3 : term275 _99546 _99547 x s f g) (h4 : term150 _99546 _99547 s) (h5 : @FINITE _99546 s) (h6 : term355 _99546 _99547 s f g) (h7 : term252 _99546 x s) : False.
Proof. exact (@lem3839258 _99546 _99547 f g x s h1 h2 h3 h4 h5 h7 (@lem3833515 _99546 _99547 s f g h6)). Qed.
Lemma lem3839260 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term112 _99546 _99547 f) (h2 : term112 _99546 _99547 g) (h3 : term275 _99546 _99547 x s f g) (h4 : term150 _99546 _99547 s) (h5 : @FINITE _99546 s) (h6 : term355 _99546 _99547 s f g) (h7 : term252 _99546 x s) : (term355 _99546 _99547 s f g) = False.
Proof. exact (prop_ext (fun h8 : term355 _99546 _99547 s f g => @lem3839259 _99546 _99547 f g x s h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem3833515 _99546 _99547 s f g h6)). Qed.
Lemma lem3839261 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term112 _99546 _99547 f) (h2 : term112 _99546 _99547 g) (h3 : term275 _99546 _99547 x s f g) (h4 : term150 _99546 _99547 s) (h5 : @FINITE _99546 s) (h6 : term355 _99546 _99547 s f g) (h7 : term252 _99546 x s) : False.
Proof. exact (EQ_MP (@lem3839260 _99546 _99547 f g x s h1 h2 h3 h4 h5 h6 h7) (@lem3833515 _99546 _99547 s f g h6)). Qed.
Lemma lem3839262 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term112 _99546 _99547 f) (h2 : term112 _99546 _99547 g) (h3 : term275 _99546 _99547 x s f g) (h4 : term150 _99546 _99547 s) (h5 : @FINITE _99546 s) (h6 : term252 _99546 x s) : term354 _99546 _99547 s f g.
Proof. exact (fun h0 : term355 _99546 _99547 s f g => @lem3839261 _99546 _99547 f g x s h1 h2 h3 h4 h5 h0 h6). Qed.
Lemma lem3839263 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term112 _99546 _99547 f) (h2 : term112 _99546 _99547 g) (h3 : term275 _99546 _99547 x s f g) (h4 : term150 _99546 _99547 s) (h5 : @FINITE _99546 s) (h6 : term252 _99546 x s) : term44 _99546 _99547 s f g.
Proof. exact (EQ_MP (@lem3833514 _99546 _99547 s f g) (@lem3839262 _99546 _99547 f g x s h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem3839264 {_99546 _99547 : Type'} (b : _99547) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term112 _99546 _99547 f) (h2 : term112 _99546 _99547 g) (h3 : term275 _99546 _99547 x s f g) (h4 : term150 _99546 _99547 s) (h5 : @FINITE _99546 s) (h6 : term252 _99546 x s) : (@ITSET _99547 _99546 f s b) = (@ITSET _99547 _99546 g s b).
Proof. exact (@lem3833510 _99546 _99547 f g b s h4 (@lem3839263 _99546 _99547 f g x s h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem3839265 {_99546 _99547 : Type'} (b : _99547) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term112 _99546 _99547 f) (h2 : term112 _99546 _99547 g) (h3 : term275 _99546 _99547 x s f g) (h4 : term150 _99546 _99547 s) (h5 : @FINITE _99546 s) (h6 : term252 _99546 x s) : (term303 _99546 _99547 g x f s b) = (term288 _99546 _99547 x g s b).
Proof. exact (MK_COMB (@lem3833081 _99546 _99547 g x) (@lem3839264 _99546 _99547 b f g x s h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem3839270 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term112 _99546 _99547 f) (h2 : term112 _99546 _99547 g) (h3 : term275 _99546 _99547 x s f g) (h4 : term150 _99546 _99547 s) (h5 : @FINITE _99546 s) (h6 : term252 _99546 x s) : term314 _99546 _99547 f x g s.
Proof. exact (fun b : _99547 => @lem3839265 _99546 _99547 b f g x s h1 h2 h3 h4 h5 h6). Qed.
Lemma lem3839271 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s f g) : term116 _99546 _99547 f g.
Proof. exact (proj2 (@lem3833076 _99546 _99547 x s f g h1)). Qed.
Lemma lem3839272 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term278 _99546 _99547 x s f g) : term275 _99546 _99547 x s f g.
Proof. exact (proj1 (@lem3833076 _99546 _99547 x s f g h1)). Qed.
Lemma lem3839273 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : term112 _99546 _99547 g.
Proof. exact (proj2 (@lem3833077 _99546 _99547 f g h1)). Qed.
Lemma lem3839274 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term116 _99546 _99547 f g) : term112 _99546 _99547 f.
Proof. exact (proj1 (@lem3833077 _99546 _99547 f g h1)). Qed.
Lemma lem3839275 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term112 _99546 _99547 f) (h2 : term112 _99546 _99547 g) (h3 : term275 _99546 _99547 x s f g) (h4 : term150 _99546 _99547 s) (h5 : @FINITE _99546 s) (h6 : term252 _99546 x s) : (term112 _99546 _99547 g) = (term314 _99546 _99547 f x g s).
Proof. exact (prop_ext (fun h7 : term112 _99546 _99547 g => @lem3839270 _99546 _99547 f g x s h1 h2 h3 h4 h5 h6) (fun h7 : term314 _99546 _99547 f x g s => @lem3833079 _99546 _99547 g h2)). Qed.
Lemma lem3839276 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term112 _99546 _99547 f) (h2 : term112 _99546 _99547 g) (h3 : term275 _99546 _99547 x s f g) (h4 : term150 _99546 _99547 s) (h5 : @FINITE _99546 s) (h6 : term252 _99546 x s) : term314 _99546 _99547 f x g s.
Proof. exact (EQ_MP (@lem3839275 _99546 _99547 f g x s h1 h2 h3 h4 h5 h6) (@lem3833079 _99546 _99547 g h2)). Qed.
Lemma lem3839277 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term112 _99546 _99547 f) (h2 : term112 _99546 _99547 g) (h3 : term275 _99546 _99547 x s f g) (h4 : term150 _99546 _99547 s) (h5 : @FINITE _99546 s) (h6 : term252 _99546 x s) : (term112 _99546 _99547 f) = (term314 _99546 _99547 f x g s).
Proof. exact (prop_ext (fun h7 : term112 _99546 _99547 f => @lem3839276 _99546 _99547 f g x s h1 h2 h3 h4 h5 h6) (fun h7 : term314 _99546 _99547 f x g s => @lem3833080 _99546 _99547 f h1)). Qed.
Lemma lem3839278 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term112 _99546 _99547 f) (h2 : term112 _99546 _99547 g) (h3 : term275 _99546 _99547 x s f g) (h4 : term150 _99546 _99547 s) (h5 : @FINITE _99546 s) (h6 : term252 _99546 x s) : term314 _99546 _99547 f x g s.
Proof. exact (EQ_MP (@lem3839277 _99546 _99547 f g x s h1 h2 h3 h4 h5 h6) (@lem3833080 _99546 _99547 f h1)). Qed.
Lemma lem3839279 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term112 _99546 _99547 f) (h2 : term275 _99546 _99547 x s f g) (h3 : term150 _99546 _99547 s) (h4 : @FINITE _99546 s) (h5 : term252 _99546 x s) (h6 : term116 _99546 _99547 f g) : (term112 _99546 _99547 g) = (term314 _99546 _99547 f x g s).
Proof. exact (prop_ext (fun h7 : term112 _99546 _99547 g => @lem3839278 _99546 _99547 f g x s h1 h7 h2 h3 h4 h5) (fun h7 : term314 _99546 _99547 f x g s => @lem3839273 _99546 _99547 f g h6)). Qed.
Lemma lem3839280 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term112 _99546 _99547 f) (h2 : term275 _99546 _99547 x s f g) (h3 : term150 _99546 _99547 s) (h4 : @FINITE _99546 s) (h5 : term252 _99546 x s) (h6 : term116 _99546 _99547 f g) : term314 _99546 _99547 f x g s.
Proof. exact (EQ_MP (@lem3839279 _99546 _99547 x s f g h1 h2 h3 h4 h5 h6) (@lem3839273 _99546 _99547 f g h6)). Qed.
Lemma lem3839281 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term275 _99546 _99547 x s f g) (h2 : term150 _99546 _99547 s) (h3 : @FINITE _99546 s) (h4 : term252 _99546 x s) (h5 : term116 _99546 _99547 f g) : (term112 _99546 _99547 f) = (term314 _99546 _99547 f x g s).
Proof. exact (prop_ext (fun h6 : term112 _99546 _99547 f => @lem3839280 _99546 _99547 x s f g h6 h1 h2 h3 h4 h5) (fun h6 : term314 _99546 _99547 f x g s => @lem3839274 _99546 _99547 f g h5)). Qed.
Lemma lem3839282 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term275 _99546 _99547 x s f g) (h2 : term150 _99546 _99547 s) (h3 : @FINITE _99546 s) (h4 : term252 _99546 x s) (h5 : term116 _99546 _99547 f g) : term314 _99546 _99547 f x g s.
Proof. exact (EQ_MP (@lem3839281 _99546 _99547 x s f g h1 h2 h3 h4 h5) (@lem3839274 _99546 _99547 f g h5)). Qed.
Lemma lem3839283 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term275 _99546 _99547 x s f g) (h2 : term150 _99546 _99547 s) (h3 : @FINITE _99546 s) (h4 : term252 _99546 x s) (h5 : term116 _99546 _99547 f g) : (term275 _99546 _99547 x s f g) = (term314 _99546 _99547 f x g s).
Proof. exact (prop_ext (fun h6 : term275 _99546 _99547 x s f g => @lem3839282 _99546 _99547 x s f g h1 h2 h3 h4 h5) (fun h6 : term314 _99546 _99547 f x g s => @lem3833078 _99546 _99547 x s f g h1)). Qed.
Lemma lem3839284 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term275 _99546 _99547 x s f g) (h2 : term150 _99546 _99547 s) (h3 : @FINITE _99546 s) (h4 : term252 _99546 x s) (h5 : term116 _99546 _99547 f g) : term314 _99546 _99547 f x g s.
Proof. exact (EQ_MP (@lem3839283 _99546 _99547 x s f g h1 h2 h3 h4 h5) (@lem3833078 _99546 _99547 x s f g h1)). Qed.
Lemma lem3839285 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term275 _99546 _99547 x s f g) (h2 : term150 _99546 _99547 s) (h3 : @FINITE _99546 s) (h4 : term252 _99546 x s) (h5 : term278 _99546 _99547 x s f g) : (term116 _99546 _99547 f g) = (term314 _99546 _99547 f x g s).
Proof. exact (prop_ext (fun h6 : term116 _99546 _99547 f g => @lem3839284 _99546 _99547 x s f g h1 h2 h3 h4 h6) (fun h6 : term314 _99546 _99547 f x g s => @lem3839271 _99546 _99547 x s f g h5)). Qed.
Lemma lem3839286 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term275 _99546 _99547 x s f g) (h2 : term150 _99546 _99547 s) (h3 : @FINITE _99546 s) (h4 : term252 _99546 x s) (h5 : term278 _99546 _99547 x s f g) : term314 _99546 _99547 f x g s.
Proof. exact (EQ_MP (@lem3839285 _99546 _99547 x s f g h1 h2 h3 h4 h5) (@lem3839271 _99546 _99547 x s f g h5)). Qed.
Lemma lem3839287 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term150 _99546 _99547 s) (h2 : @FINITE _99546 s) (h3 : term252 _99546 x s) (h4 : term278 _99546 _99547 x s f g) : (term275 _99546 _99547 x s f g) = (term314 _99546 _99547 f x g s).
Proof. exact (prop_ext (fun h5 : term275 _99546 _99547 x s f g => @lem3839286 _99546 _99547 x s f g h5 h1 h2 h3 h4) (fun h5 : term314 _99546 _99547 f x g s => @lem3839272 _99546 _99547 x s f g h4)). Qed.
Lemma lem3839288 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (h1 : term150 _99546 _99547 s) (h2 : @FINITE _99546 s) (h3 : term252 _99546 x s) (h4 : term278 _99546 _99547 x s f g) : term314 _99546 _99547 f x g s.
Proof. exact (EQ_MP (@lem3839287 _99546 _99547 x s f g h1 h2 h3 h4) (@lem3839272 _99546 _99547 x s f g h4)). Qed.
Lemma lem3839289 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (g : type1411 _99546 _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term150 _99546 _99547 s) (h2 : @FINITE _99546 s) (h3 : term252 _99546 x s) : term318 _99546 _99547 f x g s.
Proof. exact (fun h0 : term278 _99546 _99547 x s f g => @lem3839288 _99546 _99547 x s f g h1 h2 h3 h0). Qed.
Lemma lem3839294 {_99546 _99547 : Type'} (f : type1411 _99546 _99547) (x : _99546) (s : _99546 -> Prop) (h1 : term150 _99546 _99547 s) (h2 : @FINITE _99546 s) (h3 : term252 _99546 x s) : term322 _99546 _99547 f x s.
Proof. exact (fun g : type1411 _99546 _99547 => @lem3839289 _99546 _99547 f g x s h1 h2 h3). Qed.
Lemma lem3839299 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (h1 : term150 _99546 _99547 s) (h2 : @FINITE _99546 s) (h3 : term252 _99546 x s) : term325 _99546 _99547 x s.
Proof. exact (fun f : type1411 _99546 _99547 => @lem3839294 _99546 _99547 f x s h1 h2 h3). Qed.
Lemma lem3839300 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (h1 : term165 _99546 _99547 x s) : term163 _99546 x s.
Proof. exact (proj2 (@lem3833071 _99546 _99547 x s h1)). Qed.
Lemma lem3839301 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (h1 : term165 _99546 _99547 x s) : term150 _99546 _99547 s.
Proof. exact (proj1 (@lem3833071 _99546 _99547 x s h1)). Qed.
Lemma lem3839302 {_99546 : Type'} (x : _99546) (s : _99546 -> Prop) (h1 : term163 _99546 x s) : @FINITE _99546 s.
Proof. exact (proj2 (@lem3833072 _99546 x s h1)). Qed.
Lemma lem3839303 {_99546 : Type'} (x : _99546) (s : _99546 -> Prop) (h1 : term163 _99546 x s) : term252 _99546 x s.
Proof. exact (proj1 (@lem3833072 _99546 x s h1)). Qed.
Lemma lem3839304 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (h1 : term150 _99546 _99547 s) (h2 : @FINITE _99546 s) (h3 : term252 _99546 x s) : (@FINITE _99546 s) = (term325 _99546 _99547 x s).
Proof. exact (prop_ext (fun h4 : @FINITE _99546 s => @lem3839299 _99546 _99547 x s h1 h2 h3) (fun h4 : term325 _99546 _99547 x s => @lem3833074 _99546 s h2)). Qed.
Lemma lem3839305 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (h1 : term150 _99546 _99547 s) (h2 : @FINITE _99546 s) (h3 : term252 _99546 x s) : term325 _99546 _99547 x s.
Proof. exact (EQ_MP (@lem3839304 _99546 _99547 x s h1 h2 h3) (@lem3833074 _99546 s h2)). Qed.
Lemma lem3839306 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (h1 : term150 _99546 _99547 s) (h2 : @FINITE _99546 s) (h3 : term252 _99546 x s) : (term252 _99546 x s) = (term325 _99546 _99547 x s).
Proof. exact (prop_ext (fun h4 : term252 _99546 x s => @lem3839305 _99546 _99547 x s h1 h2 h3) (fun h4 : term325 _99546 _99547 x s => @lem3833075 _99546 x s h3)). Qed.
Lemma lem3839307 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (h1 : term150 _99546 _99547 s) (h2 : @FINITE _99546 s) (h3 : term252 _99546 x s) : term325 _99546 _99547 x s.
Proof. exact (EQ_MP (@lem3839306 _99546 _99547 x s h1 h2 h3) (@lem3833075 _99546 x s h3)). Qed.
Lemma lem3839308 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (h1 : term150 _99546 _99547 s) (h2 : term252 _99546 x s) (h3 : term163 _99546 x s) : (@FINITE _99546 s) = (term325 _99546 _99547 x s).
Proof. exact (prop_ext (fun h4 : @FINITE _99546 s => @lem3839307 _99546 _99547 x s h1 h4 h2) (fun h4 : term325 _99546 _99547 x s => @lem3839302 _99546 x s h3)). Qed.
Lemma lem3839309 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (h1 : term150 _99546 _99547 s) (h2 : term252 _99546 x s) (h3 : term163 _99546 x s) : term325 _99546 _99547 x s.
Proof. exact (EQ_MP (@lem3839308 _99546 _99547 x s h1 h2 h3) (@lem3839302 _99546 x s h3)). Qed.
Lemma lem3839310 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (h1 : term150 _99546 _99547 s) (h2 : term163 _99546 x s) : (term252 _99546 x s) = (term325 _99546 _99547 x s).
Proof. exact (prop_ext (fun h3 : term252 _99546 x s => @lem3839309 _99546 _99547 x s h1 h3 h2) (fun h3 : term325 _99546 _99547 x s => @lem3839303 _99546 x s h2)). Qed.
Lemma lem3839311 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (h1 : term150 _99546 _99547 s) (h2 : term163 _99546 x s) : term325 _99546 _99547 x s.
Proof. exact (EQ_MP (@lem3839310 _99546 _99547 x s h1 h2) (@lem3839303 _99546 x s h2)). Qed.
Lemma lem3839312 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (h1 : term150 _99546 _99547 s) (h2 : term163 _99546 x s) : (term150 _99546 _99547 s) = (term325 _99546 _99547 x s).
Proof. exact (prop_ext (fun h3 : term150 _99546 _99547 s => @lem3839311 _99546 _99547 x s h1 h2) (fun h3 : term325 _99546 _99547 x s => @lem3833073 _99546 _99547 s h1)). Qed.
Lemma lem3839313 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (h1 : term150 _99546 _99547 s) (h2 : term163 _99546 x s) : term325 _99546 _99547 x s.
Proof. exact (EQ_MP (@lem3839312 _99546 _99547 x s h1 h2) (@lem3833073 _99546 _99547 s h1)). Qed.
Lemma lem3839314 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (h1 : term150 _99546 _99547 s) (h2 : term165 _99546 _99547 x s) : (term163 _99546 x s) = (term325 _99546 _99547 x s).
Proof. exact (prop_ext (fun h3 : term163 _99546 x s => @lem3839313 _99546 _99547 x s h1 h3) (fun h3 : term325 _99546 _99547 x s => @lem3839300 _99546 _99547 x s h2)). Qed.
Lemma lem3839315 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (h1 : term150 _99546 _99547 s) (h2 : term165 _99546 _99547 x s) : term325 _99546 _99547 x s.
Proof. exact (EQ_MP (@lem3839314 _99546 _99547 x s h1 h2) (@lem3839300 _99546 _99547 x s h2)). Qed.
Lemma lem3839316 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (h1 : term165 _99546 _99547 x s) : (term150 _99546 _99547 s) = (term325 _99546 _99547 x s).
Proof. exact (prop_ext (fun h2 : term150 _99546 _99547 s => @lem3839315 _99546 _99547 x s h2 h1) (fun h2 : term325 _99546 _99547 x s => @lem3839301 _99546 _99547 x s h1)). Qed.
Lemma lem3839317 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) (h1 : term165 _99546 _99547 x s) : term325 _99546 _99547 x s.
Proof. exact (EQ_MP (@lem3839316 _99546 _99547 x s h1) (@lem3839301 _99546 _99547 x s h1)). Qed.
Lemma lem3839318 {_99546 _99547 : Type'} (x : _99546) (s : _99546 -> Prop) : term328 _99546 _99547 x s.
Proof. exact (fun h0 : term165 _99546 _99547 x s => @lem3839317 _99546 _99547 x s h0). Qed.
Lemma lem3839323 {_99546 _99547 : Type'} (x : _99546) : term330 _99546 _99547 x.
Proof. exact (fun s : _99546 -> Prop => @lem3839318 _99546 _99547 x s). Qed.
Lemma lem3839328 {_99546 _99547 : Type'} : term332 _99546 _99547.
Proof. exact (fun x : _99546 => @lem3839323 _99546 _99547 x). Qed.
Lemma lem3839329 {_99546 _99547 : Type'} : term181 _99546 _99547.
Proof. exact (EQ_MP (@lem3833070 _99546 _99547) (@lem3839328 _99546 _99547)). Qed.
Lemma lem3839330 {_99546 _99547 : Type'} : term153 _99546 _99547.
Proof. exact (@lem3818632 _99546 _99547 (@lem3839329 _99546 _99547)). Qed.
Lemma lem3839331 {_99546 _99547 : Type'} : term60 _99546 _99547.
Proof. exact (EQ_MP (@lem3818599 _99546 _99547) (@lem3839330 _99546 _99547)). Qed.
Lemma lem3839332 {_99546 _99547 : Type'} : term59 _99546 _99547.
Proof. exact (EQ_MP (@lem3817976 _99546 _99547) (@lem3839331 _99546 _99547)). Qed.
