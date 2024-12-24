Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARTESIAN_PRODUCT_SINGS_GEN_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import EXTENSION_spec.
Require Import EXTENSIONAL_spec.
Require Import FUN_EQ_THM_spec.
Require Import IN_SING_spec.
Require Import RESTRICTION_spec.
Require Import cartesian_product_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm20425_spec.
Require Import thm20611_spec.
Require Import thm20612_spec.
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
Require Import thm3184714_spec.
Require Import thm3184717_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Lemma lem4434838 {A B : Type'} (s : A -> Prop) : term0 A B s.
Proof. exact (@lem4386626 A B s). Qed.
Lemma lem4434839 {A B : Type'} (s : A -> Prop) : (term0 A B s) = (term1 A B s).
Proof. exact (eq_refl (term0 A B s)). Qed.
Lemma lem4434840 {A B : Type'} (s : A -> Prop) : term1 A B s.
Proof. exact (EQ_MP (@lem4434839 A B s) (@lem4434838 A B s)). Qed.
Lemma lem4434841 {A B : Type'} (s : A -> Prop) (f : A -> B) : term2 A B s f.
Proof. exact (@lem4434840 A B s f). Qed.
Lemma lem4434842 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term2 A B s f) = (term3 A B s f).
Proof. exact (eq_refl (term2 A B s f)). Qed.
Lemma lem4434843 {A B : Type'} (s : A -> Prop) (f : A -> B) : term3 A B s f.
Proof. exact (EQ_MP (@lem4434842 A B s f) (@lem4434841 A B s f)). Qed.
Lemma lem4434844 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : term4 A B s f x.
Proof. exact (@lem4434843 A B s f x). Qed.
Lemma lem4434845 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term4 A B s f x) = ((@RESTRICTION A B s f x) = (term5 A B s f x)).
Proof. exact (eq_refl (term4 A B s f x)). Qed.
Lemma lem4434847 {A B : Type'} (f : A -> B) : term6 A B f.
Proof. exact (@lem9220 A B f). Qed.
Lemma lem4434848 {A B : Type'} (f : A -> B) : (term6 A B f) = (term7 A B f).
Proof. exact (eq_refl (term6 A B f)). Qed.
Lemma lem4434849 {A B : Type'} (f : A -> B) : term7 A B f.
Proof. exact (EQ_MP (@lem4434848 A B f) (@lem4434847 A B f)). Qed.
Lemma lem4434850 {A B : Type'} (f : A -> B) (g : A -> B) : term8 A B f g.
Proof. exact (@lem4434849 A B f g). Qed.
Lemma lem4434851 {A B : Type'} (f : A -> B) (g : A -> B) : (term8 A B f g) = ((f = g) = (term9 A B f g)).
Proof. exact (eq_refl (term8 A B f g)). Qed.
Lemma lem4434853 {A : Type'} (x : A) : term10 A x.
Proof. exact (@lem3205876 A x). Qed.
Lemma lem4434854 {A : Type'} (x : A) : (term10 A x) = (term11 A x).
Proof. exact (eq_refl (term10 A x)). Qed.
Lemma lem4434855 {A : Type'} (x : A) : term11 A x.
Proof. exact (EQ_MP (@lem4434854 A x) (@lem4434853 A x)). Qed.
Lemma lem4434856 {A : Type'} (x : A) (y : A) : term12 A x y.
Proof. exact (@lem4434855 A x y). Qed.
Lemma lem4434857 {A : Type'} (x : A) (y : A) : (term12 A x y) = ((term13 A x y) = (x = y)).
Proof. exact (eq_refl (term12 A x y)). Qed.
Lemma lem4434869 {_83152 : Type'} : term14 _83152.
Proof. exact (EQ_MP (@lem3184717 _83152) (@lem3184714 _83152)). Qed.
Lemma lem4434870 {_83152 : Type'} (p : _83152 -> Prop) : term15 _83152 p.
Proof. exact (@lem4434869 _83152 p). Qed.
Lemma lem4434871 {_83152 : Type'} (p : _83152 -> Prop) : (term15 _83152 p) = (term16 _83152 p).
Proof. exact (eq_refl (term15 _83152 p)). Qed.
Lemma lem4434872 {_83152 : Type'} (p : _83152 -> Prop) : term16 _83152 p.
Proof. exact (EQ_MP (@lem4434871 _83152 p) (@lem4434870 _83152 p)). Qed.
Lemma lem4434873 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : term17 _83152 p x.
Proof. exact (@lem4434872 _83152 p x). Qed.
Lemma lem4434874 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term17 _83152 p x) = ((term18 _83152 p x) = (p x)).
Proof. exact (eq_refl (term17 _83152 p x)). Qed.
Lemma lem4434883 {_83095 : Type'} : term19 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem4434884 {_83095 : Type'} (p : _83095 -> Prop) : term20 _83095 p.
Proof. exact (@lem4434883 _83095 p). Qed.
Lemma lem4434885 {_83095 : Type'} (p : _83095 -> Prop) : (term20 _83095 p) = (term21 _83095 p).
Proof. exact (eq_refl (term20 _83095 p)). Qed.
Lemma lem4434886 {_83095 : Type'} (p : _83095 -> Prop) : term21 _83095 p.
Proof. exact (EQ_MP (@lem4434885 _83095 p) (@lem4434884 _83095 p)). Qed.
Lemma lem4434887 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term22 _83095 p x.
Proof. exact (@lem4434886 _83095 p x). Qed.
Lemma lem4434888 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term22 _83095 p x) = ((term23 _83095 x p) = (p x)).
Proof. exact (eq_refl (term22 _83095 p x)). Qed.
Lemma lem4434897 {A B : Type'} (s : A -> Prop) : term24 A B s.
Proof. exact (@lem4382798 A B s). Qed.
Lemma lem4434898 {A B : Type'} (s : A -> Prop) : (term24 A B s) = ((@EXTENSIONAL A B s) = (term25 A B s)).
Proof. exact (eq_refl (term24 A B s)). Qed.
Lemma lem4434900 {A : Type'} (s : A -> Prop) : term26 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem4434901 {A : Type'} (s : A -> Prop) : (term26 A s) = (term27 A s).
Proof. exact (eq_refl (term26 A s)). Qed.
Lemma lem4434902 {A : Type'} (s : A -> Prop) : term27 A s.
Proof. exact (EQ_MP (@lem4434901 A s) (@lem4434900 A s)). Qed.
Lemma lem4434903 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term28 A s t.
Proof. exact (@lem4434902 A s t). Qed.
Lemma lem4434904 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term28 A s t) = ((s = t) = (term29 A s t)).
Proof. exact (eq_refl (term28 A s t)). Qed.
Lemma lem4434906 {A : Type'} (x : A) : term10 A x.
Proof. exact (@lem3205876 A x). Qed.
Lemma lem4434907 {A : Type'} (x : A) : (term10 A x) = (term11 A x).
Proof. exact (eq_refl (term10 A x)). Qed.
Lemma lem4434908 {A : Type'} (x : A) : term11 A x.
Proof. exact (EQ_MP (@lem4434907 A x) (@lem4434906 A x)). Qed.
Lemma lem4434909 {A : Type'} (x : A) (y : A) : term12 A x y.
Proof. exact (@lem4434908 A x y). Qed.
Lemma lem4434910 {A : Type'} (x : A) (y : A) : (term12 A x y) = ((term13 A x y) = (x = y)).
Proof. exact (eq_refl (term12 A x y)). Qed.
Lemma lem4434912 {A K : Type'} (k : K -> Prop) : term30 A K k.
Proof. exact (@lem4399444 A K k). Qed.
Lemma lem4434913 {A K : Type'} (k : K -> Prop) : (term30 A K k) = (term31 A K k).
Proof. exact (eq_refl (term30 A K k)). Qed.
Lemma lem4434914 {A K : Type'} (k : K -> Prop) : term31 A K k.
Proof. exact (EQ_MP (@lem4434913 A K k) (@lem4434912 A K k)). Qed.
Lemma lem4434915 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term32 A K k s.
Proof. exact (@lem4434914 A K k s). Qed.
Lemma lem4434916 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term32 A K k s) = ((@cartesian_product A K k s) = (term33 A K k s)).
Proof. exact (eq_refl (term32 A K k s)). Qed.
Lemma lem4434929 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@cartesian_product A K k s) = (term33 A K k s).
Proof. exact (EQ_MP (@lem4434916 A K k s) (@lem4434915 A K k s)). Qed.
Lemma lem4434930 {_106515 _106516 : Type'} (k : _106515 -> Prop) (s : type1413 _106515 _106516) : (@cartesian_product _106516 _106515 k s) = (term34 _106515 _106516 k s).
Proof. exact (@lem4434929 _106516 _106515 k s). Qed.
Lemma lem4434931 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x : _106515 -> _106516) : (term35 _106515 _106516 k x) = (term36 _106515 _106516 k x).
Proof. exact (@lem4434930 _106515 _106516 k (term37 _106515 _106516 x)). Qed.
Lemma lem4434945 {A B : Type'} (f : A -> B) (y : A) : (term38 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4434946 {_106515 _106516 : Type'} (f : type1413 _106515 _106516) (y : _106515) : (term39 _106515 _106516 f y) = (f y).
Proof. exact (@lem4434945 _106515 (_106516 -> Prop) f y). Qed.
Lemma lem4434947 {_106515 _106516 : Type'} (x : _106515 -> _106516) (i : _106515) : (term40 _106515 _106516 x i) = (term41 _106515 _106516 x i).
Proof. exact (@lem4434946 _106515 _106516 (term37 _106515 _106516 x) i). Qed.
Lemma lem4434948 {_106515 _106516 : Type'} (x : _106515 -> _106516) (i : _106515) : (term41 _106515 _106516 x i) = (term42 _106515 _106516 x i).
Proof. exact (eq_refl (term41 _106515 _106516 x i)). Qed.
Lemma lem4434949 {_106515 _106516 : Type'} (x : _106515 -> _106516) : (term43 _106515 _106516 x) = (term37 _106515 _106516 x).
Proof. exact (fun_ext (fun i : _106515 => @lem4434948 _106515 _106516 x i)). Qed.
Lemma lem4434950 {_106515 : Type'} (i : _106515) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4434951 {_106515 _106516 : Type'} (x : _106515 -> _106516) (i : _106515) : (term40 _106515 _106516 x i) = (term41 _106515 _106516 x i).
Proof. exact (MK_COMB (@lem4434949 _106515 _106516 x) (@lem4434950 _106515 i)). Qed.
Lemma lem4434952 {_106516 : Type'} : (@eq (_106516 -> Prop)) = (@eq (_106516 -> Prop)).
Proof. exact (eq_refl (@eq (_106516 -> Prop))). Qed.
Lemma lem4434953 {_106515 _106516 : Type'} (x : _106515 -> _106516) (i : _106515) : (term44 _106515 _106516 x i) = (term45 _106515 _106516 x i).
Proof. exact (MK_COMB (@lem4434952 _106516) (@lem4434951 _106515 _106516 x i)). Qed.
Lemma lem4434954 {_106515 _106516 : Type'} (x : _106515 -> _106516) (i : _106515) : (term41 _106515 _106516 x i) = (term42 _106515 _106516 x i).
Proof. exact (eq_refl (term41 _106515 _106516 x i)). Qed.
Lemma lem4434955 {_106515 _106516 : Type'} (x : _106515 -> _106516) (i : _106515) : ((term40 _106515 _106516 x i) = (term41 _106515 _106516 x i)) = ((term41 _106515 _106516 x i) = (term42 _106515 _106516 x i)).
Proof. exact (MK_COMB (@lem4434953 _106515 _106516 x i) (@lem4434954 _106515 _106516 x i)). Qed.
Lemma lem4434956 {_106515 _106516 : Type'} (x : _106515 -> _106516) (i : _106515) : (term41 _106515 _106516 x i) = (term42 _106515 _106516 x i).
Proof. exact (EQ_MP (@lem4434955 _106515 _106516 x i) (@lem4434947 _106515 _106516 x i)). Qed.
Lemma lem4434957 {_106515 _106516 : Type'} (f : _106515 -> _106516) (i : _106515) : (term46 _106515 _106516 f i) = (term46 _106515 _106516 f i).
Proof. exact (eq_refl (term46 _106515 _106516 f i)). Qed.
Lemma lem4434958 {_106515 _106516 : Type'} (f : _106515 -> _106516) (x : _106515 -> _106516) (i : _106515) : (term47 _106515 _106516 f x i) = (term48 _106515 _106516 f x i).
Proof. exact (MK_COMB (@lem4434957 _106515 _106516 f i) (@lem4434956 _106515 _106516 x i)). Qed.
Lemma lem4434960 {A : Type'} (x : A) (y : A) : (term13 A x y) = (x = y).
Proof. exact (EQ_MP (@lem4434910 A x y) (@lem4434909 A x y)). Qed.
Lemma lem4434961 {_106516 : Type'} (x : _106516) (y : _106516) : (term13 _106516 x y) = (x = y).
Proof. exact (@lem4434960 _106516 x y). Qed.
Lemma lem4434962 {_106515 _106516 : Type'} (f : _106515 -> _106516) (x : _106515 -> _106516) (i : _106515) : (term48 _106515 _106516 f x i) = ((f i) = (x i)).
Proof. exact (@lem4434961 _106516 (f i) (x i)). Qed.
Lemma lem4434965 {_106515 _106516 : Type'} (f : _106515 -> _106516) (x : _106515 -> _106516) (i : _106515) : (term47 _106515 _106516 f x i) = ((f i) = (x i)).
Proof. exact (TRANS (@lem4434958 _106515 _106516 f x i) (@lem4434962 _106515 _106516 f x i)). Qed.
Lemma lem4434966 {_106515 : Type'} (i : _106515) (k : _106515 -> Prop) : (term49 _106515 i k) = (term49 _106515 i k).
Proof. exact (eq_refl (term49 _106515 i k)). Qed.
Lemma lem4434967 {_106515 _106516 : Type'} (k : _106515 -> Prop) (f : _106515 -> _106516) (x : _106515 -> _106516) (i : _106515) : (term50 _106515 _106516 k f x i) = (term51 _106515 _106516 k f x i).
Proof. exact (MK_COMB (@lem4434966 _106515 i k) (@lem4434965 _106515 _106516 f x i)). Qed.
Lemma lem4434970 {_106515 _106516 : Type'} (k : _106515 -> Prop) (f : _106515 -> _106516) (x : _106515 -> _106516) : (term52 _106515 _106516 k f x) = (term53 _106515 _106516 k f x).
Proof. exact (fun_ext (fun i : _106515 => @lem4434967 _106515 _106516 k f x i)). Qed.
Lemma lem4434971 {_106515 : Type'} : (@all _106515) = (@all _106515).
Proof. exact (eq_refl (@all _106515)). Qed.
Lemma lem4434972 {_106515 _106516 : Type'} (k : _106515 -> Prop) (f : _106515 -> _106516) (x : _106515 -> _106516) : (term54 _106515 _106516 k f x) = (term55 _106515 _106516 k f x).
Proof. exact (MK_COMB (@lem4434971 _106515) (@lem4434970 _106515 _106516 k f x)). Qed.
Lemma lem4434977 {_106515 _106516 : Type'} (k : _106515 -> Prop) (f : _106515 -> _106516) : (term56 _106515 _106516 k f) = (term56 _106515 _106516 k f).
Proof. exact (eq_refl (term56 _106515 _106516 k f)). Qed.
Lemma lem4434978 {_106515 _106516 : Type'} (k : _106515 -> Prop) (f : _106515 -> _106516) (x : _106515 -> _106516) : (term57 _106515 _106516 k f x) = (term58 _106515 _106516 k f x).
Proof. exact (MK_COMB (@lem4434977 _106515 _106516 k f) (@lem4434972 _106515 _106516 k f x)). Qed.
Lemma lem4434981 {_106515 _106516 : Type'} (GEN_PVAR_140 : _106515 -> _106516) : (@SETSPEC (_106515 -> _106516) GEN_PVAR_140) = (@SETSPEC (_106515 -> _106516) GEN_PVAR_140).
Proof. exact (eq_refl (@SETSPEC (_106515 -> _106516) GEN_PVAR_140)). Qed.
Lemma lem4434982 {_106515 _106516 : Type'} (GEN_PVAR_140 : _106515 -> _106516) (k : _106515 -> Prop) (f : _106515 -> _106516) (x : _106515 -> _106516) : (term59 _106515 _106516 GEN_PVAR_140 k f x) = (term60 _106515 _106516 GEN_PVAR_140 k f x).
Proof. exact (MK_COMB (@lem4434981 _106515 _106516 GEN_PVAR_140) (@lem4434978 _106515 _106516 k f x)). Qed.
Lemma lem4434983 {_106515 _106516 : Type'} (f : _106515 -> _106516) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4434984 {_106515 _106516 : Type'} (GEN_PVAR_140 : _106515 -> _106516) (k : _106515 -> Prop) (x : _106515 -> _106516) (f : _106515 -> _106516) : (term61 _106515 _106516 GEN_PVAR_140 k x f) = (term62 _106515 _106516 GEN_PVAR_140 k x f).
Proof. exact (MK_COMB (@lem4434982 _106515 _106516 GEN_PVAR_140 k f x) (@lem4434983 _106515 _106516 f)). Qed.
Lemma lem4434985 {_106515 _106516 : Type'} (GEN_PVAR_140 : _106515 -> _106516) (k : _106515 -> Prop) (x : _106515 -> _106516) : (term63 _106515 _106516 GEN_PVAR_140 k x) = (term64 _106515 _106516 GEN_PVAR_140 k x).
Proof. exact (fun_ext (fun f : _106515 -> _106516 => @lem4434984 _106515 _106516 GEN_PVAR_140 k x f)). Qed.
Lemma lem4434986 {_106515 _106516 : Type'} : (@ex (_106515 -> _106516)) = (@ex (_106515 -> _106516)).
Proof. exact (eq_refl (@ex (_106515 -> _106516))). Qed.
Lemma lem4434987 {_106515 _106516 : Type'} (GEN_PVAR_140 : _106515 -> _106516) (k : _106515 -> Prop) (x : _106515 -> _106516) : (term65 _106515 _106516 GEN_PVAR_140 k x) = (term66 _106515 _106516 GEN_PVAR_140 k x).
Proof. exact (MK_COMB (@lem4434986 _106515 _106516) (@lem4434985 _106515 _106516 GEN_PVAR_140 k x)). Qed.
Lemma lem4434992 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x : _106515 -> _106516) : (term67 _106515 _106516 k x) = (term68 _106515 _106516 k x).
Proof. exact (fun_ext (fun GEN_PVAR_140 : _106515 -> _106516 => @lem4434987 _106515 _106516 GEN_PVAR_140 k x)). Qed.
Lemma lem4434993 {_106515 _106516 : Type'} : (@GSPEC (_106515 -> _106516)) = (@GSPEC (_106515 -> _106516)).
Proof. exact (eq_refl (@GSPEC (_106515 -> _106516))). Qed.
Lemma lem4434994 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x : _106515 -> _106516) : (term36 _106515 _106516 k x) = (term69 _106515 _106516 k x).
Proof. exact (MK_COMB (@lem4434993 _106515 _106516) (@lem4434992 _106515 _106516 k x)). Qed.
Lemma lem4434995 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x : _106515 -> _106516) : (term35 _106515 _106516 k x) = (term69 _106515 _106516 k x).
Proof. exact (TRANS (@lem4434931 _106515 _106516 k x) (@lem4434994 _106515 _106516 k x)). Qed.
Lemma lem4434996 {_106515 _106516 : Type'} : (@eq ((_106515 -> _106516) -> Prop)) = (@eq ((_106515 -> _106516) -> Prop)).
Proof. exact (eq_refl (@eq ((_106515 -> _106516) -> Prop))). Qed.
Lemma lem4434997 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x : _106515 -> _106516) : (term70 _106515 _106516 k x) = (term71 _106515 _106516 k x).
Proof. exact (MK_COMB (@lem4434996 _106515 _106516) (@lem4434995 _106515 _106516 k x)). Qed.
Lemma lem4434998 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x : _106515 -> _106516) : (term72 _106515 _106516 k x) = (term72 _106515 _106516 k x).
Proof. exact (eq_refl (term72 _106515 _106516 k x)). Qed.
Lemma lem4434999 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x : _106515 -> _106516) : ((term35 _106515 _106516 k x) = (term72 _106515 _106516 k x)) = ((term69 _106515 _106516 k x) = (term72 _106515 _106516 k x)).
Proof. exact (MK_COMB (@lem4434997 _106515 _106516 k x) (@lem4434998 _106515 _106516 k x)). Qed.
Lemma lem4435002 {_106515 _106516 : Type'} (k : _106515 -> Prop) : (term73 _106515 _106516 k) = (term74 _106515 _106516 k).
Proof. exact (fun_ext (fun x : _106515 -> _106516 => @lem4434999 _106515 _106516 k x)). Qed.
Lemma lem4435003 {_106515 _106516 : Type'} : (@all (_106515 -> _106516)) = (@all (_106515 -> _106516)).
Proof. exact (eq_refl (@all (_106515 -> _106516))). Qed.
Lemma lem4435004 {_106515 _106516 : Type'} (k : _106515 -> Prop) : (term75 _106515 _106516 k) = (term76 _106515 _106516 k).
Proof. exact (MK_COMB (@lem4435003 _106515 _106516) (@lem4435002 _106515 _106516 k)). Qed.
Lemma lem4435009 {_106515 _106516 : Type'} : (term77 _106515 _106516) = (term78 _106515 _106516).
Proof. exact (fun_ext (fun k : _106515 -> Prop => @lem4435004 _106515 _106516 k)). Qed.
Lemma lem4435010 {_106515 : Type'} : (@all (_106515 -> Prop)) = (@all (_106515 -> Prop)).
Proof. exact (eq_refl (@all (_106515 -> Prop))). Qed.
Lemma lem4435011 {_106515 _106516 : Type'} : (term79 _106515 _106516) = (term80 _106515 _106516).
Proof. exact (MK_COMB (@lem4435010 _106515) (@lem4435009 _106515 _106516)). Qed.
Lemma lem4435016 {_106515 _106516 : Type'} : (term80 _106515 _106516) = (term79 _106515 _106516).
Proof. exact (SYM (@lem4435011 _106515 _106516)). Qed.
Lemma lem4435028 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term29 A s t).
Proof. exact (EQ_MP (@lem4434904 A s t) (@lem4434903 A s t)). Qed.
Lemma lem4435029 {_106515 _106516 : Type'} (s : type572 _106515 _106516) (t : type572 _106515 _106516) : (s = t) = (term81 _106515 _106516 s t).
Proof. exact (@lem4435028 (_106515 -> _106516) s t). Qed.
Lemma lem4435030 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x : _106515 -> _106516) : ((term69 _106515 _106516 k x) = (term72 _106515 _106516 k x)) = (term82 _106515 _106516 k x).
Proof. exact (@lem4435029 _106515 _106516 (term69 _106515 _106516 k x) (term72 _106515 _106516 k x)). Qed.
Lemma lem4435040 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term23 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem4434888 _83095 p x) (@lem4434887 _83095 p x)). Qed.
Lemma lem4435041 {_106515 _106516 : Type'} (p : type572 _106515 _106516) (x : _106515 -> _106516) : (term83 _106515 _106516 x p) = (p x).
Proof. exact (@lem4435040 (_106515 -> _106516) p x). Qed.
Lemma lem4435042 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x : _106515 -> _106516) (x' : _106515 -> _106516) : (term84 _106515 _106516 x' k x) = (term85 _106515 _106516 k x x').
Proof. exact (@lem4435041 _106515 _106516 (term86 _106515 _106516 k x) x'). Qed.
Lemma lem4435043 {_106515 _106516 : Type'} (k : _106515 -> Prop) (f : _106515 -> _106516) (x : _106515 -> _106516) : (term85 _106515 _106516 k x f) = (term58 _106515 _106516 k f x).
Proof. exact (eq_refl (term85 _106515 _106516 k x f)). Qed.
Lemma lem4435044 {_106515 _106516 : Type'} (GEN_PVAR_140 : _106515 -> _106516) : (@SETSPEC (_106515 -> _106516) GEN_PVAR_140) = (@SETSPEC (_106515 -> _106516) GEN_PVAR_140).
Proof. exact (eq_refl (@SETSPEC (_106515 -> _106516) GEN_PVAR_140)). Qed.
Lemma lem4435045 {_106515 _106516 : Type'} (GEN_PVAR_140 : _106515 -> _106516) (k : _106515 -> Prop) (f : _106515 -> _106516) (x : _106515 -> _106516) : (term87 _106515 _106516 GEN_PVAR_140 k x f) = (term60 _106515 _106516 GEN_PVAR_140 k f x).
Proof. exact (MK_COMB (@lem4435044 _106515 _106516 GEN_PVAR_140) (@lem4435043 _106515 _106516 k f x)). Qed.
Lemma lem4435046 {_106515 _106516 : Type'} (f : _106515 -> _106516) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4435047 {_106515 _106516 : Type'} (GEN_PVAR_140 : _106515 -> _106516) (k : _106515 -> Prop) (x : _106515 -> _106516) (f : _106515 -> _106516) : (term88 _106515 _106516 GEN_PVAR_140 k x f) = (term62 _106515 _106516 GEN_PVAR_140 k x f).
Proof. exact (MK_COMB (@lem4435045 _106515 _106516 GEN_PVAR_140 k f x) (@lem4435046 _106515 _106516 f)). Qed.
Lemma lem4435048 {_106515 _106516 : Type'} (GEN_PVAR_140 : _106515 -> _106516) (k : _106515 -> Prop) (x : _106515 -> _106516) : (term89 _106515 _106516 GEN_PVAR_140 k x) = (term64 _106515 _106516 GEN_PVAR_140 k x).
Proof. exact (fun_ext (fun f : _106515 -> _106516 => @lem4435047 _106515 _106516 GEN_PVAR_140 k x f)). Qed.
Lemma lem4435049 {_106515 _106516 : Type'} : (@ex (_106515 -> _106516)) = (@ex (_106515 -> _106516)).
Proof. exact (eq_refl (@ex (_106515 -> _106516))). Qed.
Lemma lem4435050 {_106515 _106516 : Type'} (GEN_PVAR_140 : _106515 -> _106516) (k : _106515 -> Prop) (x : _106515 -> _106516) : (term90 _106515 _106516 GEN_PVAR_140 k x) = (term66 _106515 _106516 GEN_PVAR_140 k x).
Proof. exact (MK_COMB (@lem4435049 _106515 _106516) (@lem4435048 _106515 _106516 GEN_PVAR_140 k x)). Qed.
Lemma lem4435051 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x : _106515 -> _106516) : (term91 _106515 _106516 k x) = (term68 _106515 _106516 k x).
Proof. exact (fun_ext (fun GEN_PVAR_140 : _106515 -> _106516 => @lem4435050 _106515 _106516 GEN_PVAR_140 k x)). Qed.
Lemma lem4435052 {_106515 _106516 : Type'} : (@GSPEC (_106515 -> _106516)) = (@GSPEC (_106515 -> _106516)).
Proof. exact (eq_refl (@GSPEC (_106515 -> _106516))). Qed.
Lemma lem4435053 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x : _106515 -> _106516) : (term92 _106515 _106516 k x) = (term69 _106515 _106516 k x).
Proof. exact (MK_COMB (@lem4435052 _106515 _106516) (@lem4435051 _106515 _106516 k x)). Qed.
Lemma lem4435054 {_106515 _106516 : Type'} (x' : _106515 -> _106516) : (@IN (_106515 -> _106516) x') = (@IN (_106515 -> _106516) x').
Proof. exact (eq_refl (@IN (_106515 -> _106516) x')). Qed.
Lemma lem4435055 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (k : _106515 -> Prop) (x : _106515 -> _106516) : (term84 _106515 _106516 x' k x) = (term93 _106515 _106516 x' k x).
Proof. exact (MK_COMB (@lem4435054 _106515 _106516 x') (@lem4435053 _106515 _106516 k x)). Qed.
Lemma lem4435056 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4435057 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (k : _106515 -> Prop) (x : _106515 -> _106516) : (term94 _106515 _106516 x' k x) = (term95 _106515 _106516 x' k x).
Proof. exact (MK_COMB (@lem4435056) (@lem4435055 _106515 _106516 x' k x)). Qed.
Lemma lem4435058 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term85 _106515 _106516 k x x') = (term58 _106515 _106516 k x' x).
Proof. exact (eq_refl (term85 _106515 _106516 k x x')). Qed.
Lemma lem4435059 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : ((term84 _106515 _106516 x' k x) = (term85 _106515 _106516 k x x')) = ((term93 _106515 _106516 x' k x) = (term58 _106515 _106516 k x' x)).
Proof. exact (MK_COMB (@lem4435057 _106515 _106516 x' k x) (@lem4435058 _106515 _106516 k x' x)). Qed.
Lemma lem4435060 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term93 _106515 _106516 x' k x) = (term58 _106515 _106516 k x' x).
Proof. exact (EQ_MP (@lem4435059 _106515 _106516 k x' x) (@lem4435042 _106515 _106516 k x x')). Qed.
Lemma lem4435064 {A B : Type'} (s : A -> Prop) : (@EXTENSIONAL A B s) = (term25 A B s).
Proof. exact (EQ_MP (@lem4434898 A B s) (@lem4434897 A B s)). Qed.
Lemma lem4435065 {_106515 _106516 : Type'} (s : _106515 -> Prop) : (@EXTENSIONAL _106515 _106516 s) = (term25 _106515 _106516 s).
Proof. exact (@lem4435064 _106515 _106516 s). Qed.
Lemma lem4435066 {_106515 _106516 : Type'} (k : _106515 -> Prop) : (@EXTENSIONAL _106515 _106516 k) = (term25 _106515 _106516 k).
Proof. exact (@lem4435065 _106515 _106516 k). Qed.
Lemma lem4435081 {_106515 _106516 : Type'} (x' : _106515 -> _106516) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem4435082 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) : (@EXTENSIONAL _106515 _106516 k x') = (term96 _106515 _106516 k x').
Proof. exact (MK_COMB (@lem4435066 _106515 _106516 k) (@lem4435081 _106515 _106516 x')). Qed.
Lemma lem4435084 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term18 _83152 p x) = (p x).
Proof. exact (EQ_MP (@lem4434874 _83152 p x) (@lem4434873 _83152 p x)). Qed.
Lemma lem4435085 {_106515 _106516 : Type'} (p : type572 _106515 _106516) (x : _106515 -> _106516) : (term97 _106515 _106516 p x) = (p x).
Proof. exact (@lem4435084 (_106515 -> _106516) p x). Qed.
Lemma lem4435086 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term98 _106515 _106516 k x') = (term99 _106515 _106516 k x').
Proof. exact (@lem4435085 _106515 _106516 (term100 _106515 _106516 k) x'). Qed.
Lemma lem4435087 {_106515 _106516 : Type'} (k : _106515 -> Prop) (f : _106515 -> _106516) : (term99 _106515 _106516 k f) = (term101 _106515 _106516 k f).
Proof. exact (eq_refl (term99 _106515 _106516 k f)). Qed.
Lemma lem4435088 {_106515 _106516 : Type'} (GEN_PVAR_139 : _106515 -> _106516) : (@SETSPEC (_106515 -> _106516) GEN_PVAR_139) = (@SETSPEC (_106515 -> _106516) GEN_PVAR_139).
Proof. exact (eq_refl (@SETSPEC (_106515 -> _106516) GEN_PVAR_139)). Qed.
Lemma lem4435089 {_106515 _106516 : Type'} (GEN_PVAR_139 : _106515 -> _106516) (k : _106515 -> Prop) (f : _106515 -> _106516) : (term102 _106515 _106516 GEN_PVAR_139 k f) = (term103 _106515 _106516 GEN_PVAR_139 k f).
Proof. exact (MK_COMB (@lem4435088 _106515 _106516 GEN_PVAR_139) (@lem4435087 _106515 _106516 k f)). Qed.
Lemma lem4435090 {_106515 _106516 : Type'} (f : _106515 -> _106516) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4435091 {_106515 _106516 : Type'} (GEN_PVAR_139 : _106515 -> _106516) (k : _106515 -> Prop) (f : _106515 -> _106516) : (term104 _106515 _106516 GEN_PVAR_139 k f) = (term105 _106515 _106516 GEN_PVAR_139 k f).
Proof. exact (MK_COMB (@lem4435089 _106515 _106516 GEN_PVAR_139 k f) (@lem4435090 _106515 _106516 f)). Qed.
Lemma lem4435092 {_106515 _106516 : Type'} (GEN_PVAR_139 : _106515 -> _106516) (k : _106515 -> Prop) : (term106 _106515 _106516 GEN_PVAR_139 k) = (term107 _106515 _106516 GEN_PVAR_139 k).
Proof. exact (fun_ext (fun f : _106515 -> _106516 => @lem4435091 _106515 _106516 GEN_PVAR_139 k f)). Qed.
Lemma lem4435093 {_106515 _106516 : Type'} : (@ex (_106515 -> _106516)) = (@ex (_106515 -> _106516)).
Proof. exact (eq_refl (@ex (_106515 -> _106516))). Qed.
Lemma lem4435094 {_106515 _106516 : Type'} (GEN_PVAR_139 : _106515 -> _106516) (k : _106515 -> Prop) : (term108 _106515 _106516 GEN_PVAR_139 k) = (term109 _106515 _106516 GEN_PVAR_139 k).
Proof. exact (MK_COMB (@lem4435093 _106515 _106516) (@lem4435092 _106515 _106516 GEN_PVAR_139 k)). Qed.
Lemma lem4435095 {_106515 _106516 : Type'} (k : _106515 -> Prop) : (term110 _106515 _106516 k) = (term111 _106515 _106516 k).
Proof. exact (fun_ext (fun GEN_PVAR_139 : _106515 -> _106516 => @lem4435094 _106515 _106516 GEN_PVAR_139 k)). Qed.
Lemma lem4435096 {_106515 _106516 : Type'} : (@GSPEC (_106515 -> _106516)) = (@GSPEC (_106515 -> _106516)).
Proof. exact (eq_refl (@GSPEC (_106515 -> _106516))). Qed.
Lemma lem4435097 {_106515 _106516 : Type'} (k : _106515 -> Prop) : (term112 _106515 _106516 k) = (term25 _106515 _106516 k).
Proof. exact (MK_COMB (@lem4435096 _106515 _106516) (@lem4435095 _106515 _106516 k)). Qed.
Lemma lem4435098 {_106515 _106516 : Type'} (x' : _106515 -> _106516) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem4435099 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term98 _106515 _106516 k x') = (term96 _106515 _106516 k x').
Proof. exact (MK_COMB (@lem4435097 _106515 _106516 k) (@lem4435098 _106515 _106516 x')). Qed.
Lemma lem4435100 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4435101 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term113 _106515 _106516 k x') = (term114 _106515 _106516 k x').
Proof. exact (MK_COMB (@lem4435100) (@lem4435099 _106515 _106516 k x')). Qed.
Lemma lem4435102 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term99 _106515 _106516 k x') = (term101 _106515 _106516 k x').
Proof. exact (eq_refl (term99 _106515 _106516 k x')). Qed.
Lemma lem4435103 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) : ((term98 _106515 _106516 k x') = (term99 _106515 _106516 k x')) = ((term96 _106515 _106516 k x') = (term101 _106515 _106516 k x')).
Proof. exact (MK_COMB (@lem4435101 _106515 _106516 k x') (@lem4435102 _106515 _106516 k x')). Qed.
Lemma lem4435104 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term96 _106515 _106516 k x') = (term101 _106515 _106516 k x').
Proof. exact (EQ_MP (@lem4435103 _106515 _106516 k x') (@lem4435086 _106515 _106516 k x')). Qed.
Lemma lem4435115 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) : (@EXTENSIONAL _106515 _106516 k x') = (term101 _106515 _106516 k x').
Proof. exact (TRANS (@lem4435082 _106515 _106516 k x') (@lem4435104 _106515 _106516 k x')). Qed.
Lemma lem4435116 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4435117 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term56 _106515 _106516 k x') = (term115 _106515 _106516 k x').
Proof. exact (MK_COMB (@lem4435116) (@lem4435115 _106515 _106516 k x')). Qed.
Lemma lem4435128 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term55 _106515 _106516 k x' x) = (term55 _106515 _106516 k x' x).
Proof. exact (eq_refl (term55 _106515 _106516 k x' x)). Qed.
Lemma lem4435129 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term58 _106515 _106516 k x' x) = (term116 _106515 _106516 k x' x).
Proof. exact (MK_COMB (@lem4435117 _106515 _106516 k x') (@lem4435128 _106515 _106516 k x' x)). Qed.
Lemma lem4435132 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term93 _106515 _106516 x' k x) = (term116 _106515 _106516 k x' x).
Proof. exact (TRANS (@lem4435060 _106515 _106516 k x' x) (@lem4435129 _106515 _106516 k x' x)). Qed.
Lemma lem4435133 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4435134 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term95 _106515 _106516 x' k x) = (term117 _106515 _106516 k x' x).
Proof. exact (MK_COMB (@lem4435133) (@lem4435132 _106515 _106516 k x' x)). Qed.
Lemma lem4435136 {A : Type'} (x : A) (y : A) : (term13 A x y) = (x = y).
Proof. exact (EQ_MP (@lem4434857 A x y) (@lem4434856 A x y)). Qed.
Lemma lem4435137 {_106515 _106516 : Type'} (x : _106515 -> _106516) (y : _106515 -> _106516) : (term118 _106515 _106516 x y) = (x = y).
Proof. exact (@lem4435136 (_106515 -> _106516) x y). Qed.
Lemma lem4435138 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (k : _106515 -> Prop) (x : _106515 -> _106516) : (term119 _106515 _106516 x' k x) = (x' = (@RESTRICTION _106515 _106516 k x)).
Proof. exact (@lem4435137 _106515 _106516 x' (@RESTRICTION _106515 _106516 k x)). Qed.
Lemma lem4435143 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (k : _106515 -> Prop) (x : _106515 -> _106516) : ((term93 _106515 _106516 x' k x) = (term119 _106515 _106516 x' k x)) = ((term116 _106515 _106516 k x' x) = (x' = (@RESTRICTION _106515 _106516 k x))).
Proof. exact (MK_COMB (@lem4435134 _106515 _106516 k x' x) (@lem4435138 _106515 _106516 x' k x)). Qed.
Lemma lem4435148 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x : _106515 -> _106516) : (term120 _106515 _106516 k x) = (term121 _106515 _106516 k x).
Proof. exact (fun_ext (fun x' : _106515 -> _106516 => @lem4435143 _106515 _106516 x' k x)). Qed.
Lemma lem4435149 {_106515 _106516 : Type'} : (@all (_106515 -> _106516)) = (@all (_106515 -> _106516)).
Proof. exact (eq_refl (@all (_106515 -> _106516))). Qed.
Lemma lem4435150 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x : _106515 -> _106516) : (term82 _106515 _106516 k x) = (term122 _106515 _106516 k x).
Proof. exact (MK_COMB (@lem4435149 _106515 _106516) (@lem4435148 _106515 _106516 k x)). Qed.
Lemma lem4435155 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x : _106515 -> _106516) : ((term69 _106515 _106516 k x) = (term72 _106515 _106516 k x)) = (term122 _106515 _106516 k x).
Proof. exact (TRANS (@lem4435030 _106515 _106516 k x) (@lem4435150 _106515 _106516 k x)). Qed.
Lemma lem4435156 {_106515 _106516 : Type'} (k : _106515 -> Prop) : (term74 _106515 _106516 k) = (term123 _106515 _106516 k).
Proof. exact (fun_ext (fun x : _106515 -> _106516 => @lem4435155 _106515 _106516 k x)). Qed.
Lemma lem4435157 {_106515 _106516 : Type'} : (@all (_106515 -> _106516)) = (@all (_106515 -> _106516)).
Proof. exact (eq_refl (@all (_106515 -> _106516))). Qed.
Lemma lem4435158 {_106515 _106516 : Type'} (k : _106515 -> Prop) : (term76 _106515 _106516 k) = (term124 _106515 _106516 k).
Proof. exact (MK_COMB (@lem4435157 _106515 _106516) (@lem4435156 _106515 _106516 k)). Qed.
Lemma lem4435163 {_106515 _106516 : Type'} : (term78 _106515 _106516) = (term125 _106515 _106516).
Proof. exact (fun_ext (fun k : _106515 -> Prop => @lem4435158 _106515 _106516 k)). Qed.
Lemma lem4435164 {_106515 : Type'} : (@all (_106515 -> Prop)) = (@all (_106515 -> Prop)).
Proof. exact (eq_refl (@all (_106515 -> Prop))). Qed.
Lemma lem4435165 {_106515 _106516 : Type'} : (term80 _106515 _106516) = (term126 _106515 _106516).
Proof. exact (MK_COMB (@lem4435164 _106515) (@lem4435163 _106515 _106516)). Qed.
Lemma lem4435170 {_106515 _106516 : Type'} : (term126 _106515 _106516) = (term80 _106515 _106516).
Proof. exact (SYM (@lem4435165 _106515 _106516)). Qed.
Lemma lem4435212 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term9 A B f g).
Proof. exact (EQ_MP (@lem4434851 A B f g) (@lem4434850 A B f g)). Qed.
Lemma lem4435213 {_106515 _106516 : Type'} (f : _106515 -> _106516) (g : _106515 -> _106516) : (f = g) = (term9 _106515 _106516 f g).
Proof. exact (@lem4435212 _106515 _106516 f g). Qed.
Lemma lem4435214 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (k : _106515 -> Prop) (x : _106515 -> _106516) : (x' = (@RESTRICTION _106515 _106516 k x)) = (term127 _106515 _106516 x' k x).
Proof. exact (@lem4435213 _106515 _106516 x' (@RESTRICTION _106515 _106516 k x)). Qed.
Lemma lem4435224 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (@RESTRICTION A B s f x) = (term5 A B s f x).
Proof. exact (EQ_MP (@lem4434845 A B s f x) (@lem4434844 A B s f x)). Qed.
Lemma lem4435225 {_106515 _106516 : Type'} (s : _106515 -> Prop) (f : _106515 -> _106516) (x : _106515) : (@RESTRICTION _106515 _106516 s f x) = (term5 _106515 _106516 s f x).
Proof. exact (@lem4435224 _106515 _106516 s f x). Qed.
Lemma lem4435226 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x : _106515 -> _106516) (x' : _106515) : (@RESTRICTION _106515 _106516 k x x') = (term5 _106515 _106516 k x x').
Proof. exact (@lem4435225 _106515 _106516 k x x'). Qed.
Lemma lem4435227 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (x : _106515) : (term128 _106515 _106516 x' x) = (term128 _106515 _106516 x' x).
Proof. exact (eq_refl (term128 _106515 _106516 x' x)). Qed.
Lemma lem4435228 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (k : _106515 -> Prop) (x : _106515 -> _106516) (x'' : _106515) : ((x' x'') = (@RESTRICTION _106515 _106516 k x x'')) = ((x' x'') = (term5 _106515 _106516 k x x'')).
Proof. exact (MK_COMB (@lem4435227 _106515 _106516 x' x'') (@lem4435226 _106515 _106516 k x x'')). Qed.
Lemma lem4435233 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (k : _106515 -> Prop) (x : _106515 -> _106516) : (term129 _106515 _106516 x' k x) = (term130 _106515 _106516 x' k x).
Proof. exact (fun_ext (fun x'' : _106515 => @lem4435228 _106515 _106516 x' k x x'')). Qed.
Lemma lem4435234 {_106515 : Type'} : (@all _106515) = (@all _106515).
Proof. exact (eq_refl (@all _106515)). Qed.
Lemma lem4435235 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (k : _106515 -> Prop) (x : _106515 -> _106516) : (term127 _106515 _106516 x' k x) = (term131 _106515 _106516 x' k x).
Proof. exact (MK_COMB (@lem4435234 _106515) (@lem4435233 _106515 _106516 x' k x)). Qed.
Lemma lem4435240 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (k : _106515 -> Prop) (x : _106515 -> _106516) : (x' = (@RESTRICTION _106515 _106516 k x)) = (term131 _106515 _106516 x' k x).
Proof. exact (TRANS (@lem4435214 _106515 _106516 x' k x) (@lem4435235 _106515 _106516 x' k x)). Qed.
Lemma lem4435241 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term117 _106515 _106516 k x' x) = (term117 _106515 _106516 k x' x).
Proof. exact (eq_refl (term117 _106515 _106516 k x' x)). Qed.
Lemma lem4435242 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (k : _106515 -> Prop) (x : _106515 -> _106516) : ((term116 _106515 _106516 k x' x) = (x' = (@RESTRICTION _106515 _106516 k x))) = ((term116 _106515 _106516 k x' x) = (term131 _106515 _106516 x' k x)).
Proof. exact (MK_COMB (@lem4435241 _106515 _106516 k x' x) (@lem4435240 _106515 _106516 x' k x)). Qed.
Lemma lem4435247 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x : _106515 -> _106516) : (term121 _106515 _106516 k x) = (term132 _106515 _106516 k x).
Proof. exact (fun_ext (fun x' : _106515 -> _106516 => @lem4435242 _106515 _106516 x' k x)). Qed.
Lemma lem4435248 {_106515 _106516 : Type'} : (@all (_106515 -> _106516)) = (@all (_106515 -> _106516)).
Proof. exact (eq_refl (@all (_106515 -> _106516))). Qed.
Lemma lem4435249 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x : _106515 -> _106516) : (term122 _106515 _106516 k x) = (term133 _106515 _106516 k x).
Proof. exact (MK_COMB (@lem4435248 _106515 _106516) (@lem4435247 _106515 _106516 k x)). Qed.
Lemma lem4435254 {_106515 _106516 : Type'} (k : _106515 -> Prop) : (term123 _106515 _106516 k) = (term134 _106515 _106516 k).
Proof. exact (fun_ext (fun x : _106515 -> _106516 => @lem4435249 _106515 _106516 k x)). Qed.
Lemma lem4435255 {_106515 _106516 : Type'} : (@all (_106515 -> _106516)) = (@all (_106515 -> _106516)).
Proof. exact (eq_refl (@all (_106515 -> _106516))). Qed.
Lemma lem4435256 {_106515 _106516 : Type'} (k : _106515 -> Prop) : (term124 _106515 _106516 k) = (term135 _106515 _106516 k).
Proof. exact (MK_COMB (@lem4435255 _106515 _106516) (@lem4435254 _106515 _106516 k)). Qed.
Lemma lem4435261 {_106515 _106516 : Type'} : (term125 _106515 _106516) = (term136 _106515 _106516).
Proof. exact (fun_ext (fun k : _106515 -> Prop => @lem4435256 _106515 _106516 k)). Qed.
Lemma lem4435262 {_106515 : Type'} : (@all (_106515 -> Prop)) = (@all (_106515 -> Prop)).
Proof. exact (eq_refl (@all (_106515 -> Prop))). Qed.
Lemma lem4435263 {_106515 _106516 : Type'} : (term126 _106515 _106516) = (term137 _106515 _106516).
Proof. exact (MK_COMB (@lem4435262 _106515) (@lem4435261 _106515 _106516)). Qed.
Lemma lem4435268 {_106515 _106516 : Type'} : (term137 _106515 _106516) = (term126 _106515 _106516).
Proof. exact (SYM (@lem4435263 _106515 _106516)). Qed.
Lemma lem4435270 (p : Prop) : p = (term138 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4435271 {_106515 _106516 : Type'} : (term137 _106515 _106516) = (term139 _106515 _106516).
Proof. exact (@lem4435270 (term137 _106515 _106516)). Qed.
Lemma lem4435272 {_106515 _106516 : Type'} : (term139 _106515 _106516) = (term137 _106515 _106516).
Proof. exact (SYM (@lem4435271 _106515 _106516)). Qed.
Lemma lem4435273 {_106515 _106516 : Type'} (h1 : term140 _106515 _106516) : term140 _106515 _106516.
Proof. exact (h1). Qed.
Lemma lem4435276 {_106515 _106516 : Type'} (h1 : term139 _106515 _106516) : term139 _106515 _106516.
Proof. exact (h1). Qed.
Lemma lem4435277 {_106515 _106516 : Type'} : term141 _106515 _106516.
Proof. exact (fun h0 : term139 _106515 _106516 => @lem4435276 _106515 _106516 h0). Qed.
Lemma lem4435278 {_106515 _106516 : Type'} (h1 : term141 _106515 _106516) : term141 _106515 _106516.
Proof. exact (h1). Qed.
Lemma lem4435279 {_106515 _106516 : Type'} (h1 : term139 _106515 _106516) : term139 _106515 _106516.
Proof. exact (h1). Qed.
Lemma lem4435280 {_106515 _106516 : Type'} (h1 : term139 _106515 _106516) (h2 : term141 _106515 _106516) : term139 _106515 _106516.
Proof. exact (@lem4435278 _106515 _106516 h2 (@lem4435279 _106515 _106516 h1)). Qed.
Lemma lem4435281 {_106515 _106516 : Type'} (h1 : term139 _106515 _106516) : term142 _106515 _106516.
Proof. exact (fun h0 : term141 _106515 _106516 => @lem4435280 _106515 _106516 h1 h0). Qed.
Lemma lem4435282 {_106515 _106516 : Type'} (h1 : term141 _106515 _106516) : term141 _106515 _106516.
Proof. exact (h1). Qed.
Lemma lem4435283 {_106515 _106516 : Type'} (h1 : term139 _106515 _106516) (h2 : term141 _106515 _106516) : term139 _106515 _106516.
Proof. exact (@lem4435281 _106515 _106516 h1 (@lem4435282 _106515 _106516 h2)). Qed.
Lemma lem4435284 {_106515 _106516 : Type'} (h1 : term141 _106515 _106516) : term141 _106515 _106516.
Proof. exact (fun h0 : term139 _106515 _106516 => @lem4435283 _106515 _106516 h0 h1). Qed.
Lemma lem4435285 {_106515 _106516 : Type'} : term143 _106515 _106516.
Proof. exact (fun h0 : term141 _106515 _106516 => @lem4435284 _106515 _106516 h0). Qed.
Lemma lem4435288 {_106515 _106516 : Type'} : term141 _106515 _106516.
Proof. exact (@lem4435285 _106515 _106516 (@lem4435277 _106515 _106516)). Qed.
Lemma lem4435289 {_106515 _106516 : Type'} : term141 _106515 _106516.
Proof. exact (@lem4435288 _106515 _106516). Qed.
Lemma lem4435291 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4435292 {_106515 _106516 : Type'} : (term139 _106515 _106516) = (term144 _106515 _106516).
Proof. exact (@lem4435291 (term140 _106515 _106516)). Qed.
Lemma lem4435294 (t : Prop) : (term145 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4435295 {_106515 _106516 : Type'} : (term144 _106515 _106516) = (term137 _106515 _106516).
Proof. exact (@lem4435294 (term137 _106515 _106516)). Qed.
Lemma lem4435330 {_106515 _106516 : Type'} : (term139 _106515 _106516) = (term137 _106515 _106516).
Proof. exact (TRANS (@lem4435292 _106515 _106516) (@lem4435295 _106515 _106516)). Qed.
Lemma lem4435334 {_106515 : Type'} (x : _106515) (k : _106515 -> Prop) (h1 : (@IN _106515 x k) = False) : (@IN _106515 x k) = False.
Proof. exact (h1). Qed.
Lemma lem4435335 {_106516 : Type'} : (@COND _106516) = (@COND _106516).
Proof. exact (eq_refl (@COND _106516)). Qed.
Lemma lem4435336 {_106515 _106516 : Type'} (x : _106515) (k : _106515 -> Prop) (h1 : (@IN _106515 x k) = False) : (term146 _106515 _106516 x k) = (@COND _106516 False).
Proof. exact (MK_COMB (@lem4435335 _106516) (@lem4435334 _106515 x k h1)). Qed.
Lemma lem4435337 {_106515 _106516 : Type'} (x : _106515 -> _106516) (x' : _106515) : (x x') = (x x').
Proof. exact (eq_refl (x x')). Qed.
Lemma lem4435338 {_106515 _106516 : Type'} (x : _106515 -> _106516) (x' : _106515) (k : _106515 -> Prop) (h1 : (@IN _106515 x' k) = False) : (term147 _106515 _106516 k x x') = (term148 _106515 _106516 x x').
Proof. exact (MK_COMB (@lem4435336 _106515 _106516 x' k h1) (@lem4435337 _106515 _106516 x x')). Qed.
Lemma lem4435339 {_106516 : Type'} : (@ARB _106516) = (@ARB _106516).
Proof. exact (eq_refl (@ARB _106516)). Qed.
Lemma lem4435340 {_106515 _106516 : Type'} (x : _106515 -> _106516) (x' : _106515) (k : _106515 -> Prop) (h1 : (@IN _106515 x' k) = False) : (term5 _106515 _106516 k x x') = (term149 _106515 _106516 x x').
Proof. exact (MK_COMB (@lem4435338 _106515 _106516 x x' k h1) (@lem4435339 _106516)). Qed.
Lemma lem4435342 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem4435343 {_106516 : Type'} (t1 : _106516) (t2 : _106516) : (@COND _106516 False t1 t2) = t2.
Proof. exact (@lem4435342 _106516 t1 t2). Qed.
Lemma lem4435344 {_106515 _106516 : Type'} (x : _106515 -> _106516) (x' : _106515) : (term149 _106515 _106516 x x') = (@ARB _106516).
Proof. exact (@lem4435343 _106516 (x x') (@ARB _106516)). Qed.
Lemma lem4435345 {_106515 _106516 : Type'} (x : _106515 -> _106516) (x' : _106515) (k : _106515 -> Prop) (h1 : (@IN _106515 x' k) = False) : (term5 _106515 _106516 k x x') = (@ARB _106516).
Proof. exact (TRANS (@lem4435340 _106515 _106516 x x' k h1) (@lem4435344 _106515 _106516 x x')). Qed.
Lemma lem4435346 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (x : _106515) : (term128 _106515 _106516 x' x) = (term128 _106515 _106516 x' x).
Proof. exact (eq_refl (term128 _106515 _106516 x' x)). Qed.
Lemma lem4435347 {_106515 _106516 : Type'} (x : _106515 -> _106516) (x' : _106515 -> _106516) (x'' : _106515) (k : _106515 -> Prop) (h1 : (@IN _106515 x'' k) = False) : ((x' x'') = (term5 _106515 _106516 k x x'')) = ((x' x'') = (@ARB _106516)).
Proof. exact (MK_COMB (@lem4435346 _106515 _106516 x' x'') (@lem4435345 _106515 _106516 x x'' k h1)). Qed.
Lemma lem4435350 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x : _106515 -> _106516) (x' : _106515 -> _106516) (x'' : _106515) : term150 _106515 _106516 k x x' x''.
Proof. exact (fun h0 : (@IN _106515 x'' k) = False => @lem4435347 _106515 _106516 x x' x'' k h0). Qed.
Lemma lem4435352 {_106515 : Type'} (x : _106515) (k : _106515 -> Prop) (h1 : (@IN _106515 x k) = True) : (@IN _106515 x k) = True.
Proof. exact (h1). Qed.
Lemma lem4435353 {_106516 : Type'} : (@COND _106516) = (@COND _106516).
Proof. exact (eq_refl (@COND _106516)). Qed.
Lemma lem4435354 {_106515 _106516 : Type'} (x : _106515) (k : _106515 -> Prop) (h1 : (@IN _106515 x k) = True) : (term146 _106515 _106516 x k) = (@COND _106516 True).
Proof. exact (MK_COMB (@lem4435353 _106516) (@lem4435352 _106515 x k h1)). Qed.
Lemma lem4435355 {_106515 _106516 : Type'} (x : _106515 -> _106516) (x' : _106515) : (x x') = (x x').
Proof. exact (eq_refl (x x')). Qed.
Lemma lem4435356 {_106515 _106516 : Type'} (x : _106515 -> _106516) (x' : _106515) (k : _106515 -> Prop) (h1 : (@IN _106515 x' k) = True) : (term147 _106515 _106516 k x x') = (term151 _106515 _106516 x x').
Proof. exact (MK_COMB (@lem4435354 _106515 _106516 x' k h1) (@lem4435355 _106515 _106516 x x')). Qed.
Lemma lem4435357 {_106516 : Type'} : (@ARB _106516) = (@ARB _106516).
Proof. exact (eq_refl (@ARB _106516)). Qed.
Lemma lem4435358 {_106515 _106516 : Type'} (x : _106515 -> _106516) (x' : _106515) (k : _106515 -> Prop) (h1 : (@IN _106515 x' k) = True) : (term5 _106515 _106516 k x x') = (term152 _106515 _106516 x x').
Proof. exact (MK_COMB (@lem4435356 _106515 _106516 x x' k h1) (@lem4435357 _106516)). Qed.
Lemma lem4435360 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem4435361 {_106516 : Type'} (t2 : _106516) (t1 : _106516) : (@COND _106516 True t1 t2) = t1.
Proof. exact (@lem4435360 _106516 t2 t1). Qed.
Lemma lem4435362 {_106515 _106516 : Type'} (x : _106515 -> _106516) (x' : _106515) : (term152 _106515 _106516 x x') = (x x').
Proof. exact (@lem4435361 _106516 (@ARB _106516) (x x')). Qed.
Lemma lem4435363 {_106515 _106516 : Type'} (x : _106515 -> _106516) (x' : _106515) (k : _106515 -> Prop) (h1 : (@IN _106515 x' k) = True) : (term5 _106515 _106516 k x x') = (x x').
Proof. exact (TRANS (@lem4435358 _106515 _106516 x x' k h1) (@lem4435362 _106515 _106516 x x')). Qed.
Lemma lem4435364 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (x : _106515) : (term128 _106515 _106516 x' x) = (term128 _106515 _106516 x' x).
Proof. exact (eq_refl (term128 _106515 _106516 x' x)). Qed.
Lemma lem4435365 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (x : _106515 -> _106516) (x'' : _106515) (k : _106515 -> Prop) (h1 : (@IN _106515 x'' k) = True) : ((x' x'') = (term5 _106515 _106516 k x x'')) = ((x' x'') = (x x'')).
Proof. exact (MK_COMB (@lem4435364 _106515 _106516 x' x'') (@lem4435363 _106515 _106516 x x'' k h1)). Qed.
Lemma lem4435368 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (x'' : _106515) : term153 _106515 _106516 k x' x x''.
Proof. exact (fun h0 : (@IN _106515 x'' k) = True => @lem4435365 _106515 _106516 x' x x'' k h0). Qed.
Lemma lem4435369 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (x'' : _106515) : term154 _106515 _106516 k x' x x''.
Proof. exact (conj (@lem4435350 _106515 _106516 k x x' x'') (@lem4435368 _106515 _106516 k x' x x'')). Qed.
Lemma lem4435371 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term155 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem4435372 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (x'' : _106515) : term156 _106515 _106516 x k x' x''.
Proof. exact (@lem4435371 ((x' x'') = (term5 _106515 _106516 k x x'')) ((x' x'') = (x x'')) (@IN _106515 x'' k) ((x' x'') = (@ARB _106516))). Qed.
Lemma lem4435405 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (x'' : _106515) : ((x' x'') = (term5 _106515 _106516 k x x'')) = (term157 _106515 _106516 x k x' x'').
Proof. exact (@lem4435372 _106515 _106516 x k x' x'' (@lem4435369 _106515 _106516 k x' x x'')). Qed.
Lemma lem4435406 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term130 _106515 _106516 x' k x) = (term158 _106515 _106516 x k x').
Proof. exact (fun_ext (fun x'' : _106515 => @lem4435405 _106515 _106516 x k x' x'')). Qed.
Lemma lem4435407 {_106515 : Type'} : (@all _106515) = (@all _106515).
Proof. exact (eq_refl (@all _106515)). Qed.
Lemma lem4435408 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term131 _106515 _106516 x' k x) = (term159 _106515 _106516 x k x').
Proof. exact (MK_COMB (@lem4435407 _106515) (@lem4435406 _106515 _106516 x k x')). Qed.
Lemma lem4435413 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (i : _106515) : (term51 _106515 _106516 k x' x i) = (term51 _106515 _106516 k x' x i).
Proof. exact (eq_refl (term51 _106515 _106516 k x' x i)). Qed.
Lemma lem4435414 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term53 _106515 _106516 k x' x) = (term53 _106515 _106516 k x' x).
Proof. exact (fun_ext (fun i : _106515 => @lem4435413 _106515 _106516 k x' x i)). Qed.
Lemma lem4435415 {_106515 : Type'} : (@all _106515) = (@all _106515).
Proof. exact (eq_refl (@all _106515)). Qed.
Lemma lem4435416 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term55 _106515 _106516 k x' x) = (term55 _106515 _106516 k x' x).
Proof. exact (MK_COMB (@lem4435415 _106515) (@lem4435414 _106515 _106516 k x' x)). Qed.
Lemma lem4435423 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515) : (term160 _106515 _106516 k x' x) = (term160 _106515 _106516 k x' x).
Proof. exact (eq_refl (term160 _106515 _106516 k x' x)). Qed.
Lemma lem4435424 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term161 _106515 _106516 k x') = (term161 _106515 _106516 k x').
Proof. exact (fun_ext (fun x : _106515 => @lem4435423 _106515 _106516 k x' x)). Qed.
Lemma lem4435425 {_106515 : Type'} : (@all _106515) = (@all _106515).
Proof. exact (eq_refl (@all _106515)). Qed.
Lemma lem4435426 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term101 _106515 _106516 k x') = (term101 _106515 _106516 k x').
Proof. exact (MK_COMB (@lem4435425 _106515) (@lem4435424 _106515 _106516 k x')). Qed.
Lemma lem4435427 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4435428 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term115 _106515 _106516 k x') = (term115 _106515 _106516 k x').
Proof. exact (MK_COMB (@lem4435427) (@lem4435426 _106515 _106516 k x')). Qed.
Lemma lem4435429 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term116 _106515 _106516 k x' x) = (term116 _106515 _106516 k x' x).
Proof. exact (MK_COMB (@lem4435428 _106515 _106516 k x') (@lem4435416 _106515 _106516 k x' x)). Qed.
Lemma lem4435430 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4435431 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term117 _106515 _106516 k x' x) = (term117 _106515 _106516 k x' x).
Proof. exact (MK_COMB (@lem4435430) (@lem4435429 _106515 _106516 k x' x)). Qed.
Lemma lem4435432 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : ((term116 _106515 _106516 k x' x) = (term131 _106515 _106516 x' k x)) = ((term116 _106515 _106516 k x' x) = (term159 _106515 _106516 x k x')).
Proof. exact (MK_COMB (@lem4435431 _106515 _106516 k x' x) (@lem4435408 _106515 _106516 x k x')). Qed.
Lemma lem4435433 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) : (term132 _106515 _106516 k x) = (term162 _106515 _106516 x k).
Proof. exact (fun_ext (fun x' : _106515 -> _106516 => @lem4435432 _106515 _106516 x k x')). Qed.
Lemma lem4435434 {_106515 _106516 : Type'} : (@all (_106515 -> _106516)) = (@all (_106515 -> _106516)).
Proof. exact (eq_refl (@all (_106515 -> _106516))). Qed.
Lemma lem4435435 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) : (term133 _106515 _106516 k x) = (term163 _106515 _106516 x k).
Proof. exact (MK_COMB (@lem4435434 _106515 _106516) (@lem4435433 _106515 _106516 x k)). Qed.
Lemma lem4435436 {_106515 _106516 : Type'} (k : _106515 -> Prop) : (term134 _106515 _106516 k) = (term164 _106515 _106516 k).
Proof. exact (fun_ext (fun x : _106515 -> _106516 => @lem4435435 _106515 _106516 x k)). Qed.
Lemma lem4435437 {_106515 _106516 : Type'} : (@all (_106515 -> _106516)) = (@all (_106515 -> _106516)).
Proof. exact (eq_refl (@all (_106515 -> _106516))). Qed.
Lemma lem4435438 {_106515 _106516 : Type'} (k : _106515 -> Prop) : (term135 _106515 _106516 k) = (term165 _106515 _106516 k).
Proof. exact (MK_COMB (@lem4435437 _106515 _106516) (@lem4435436 _106515 _106516 k)). Qed.
Lemma lem4435439 {_106515 _106516 : Type'} : (term136 _106515 _106516) = (term166 _106515 _106516).
Proof. exact (fun_ext (fun k : _106515 -> Prop => @lem4435438 _106515 _106516 k)). Qed.
Lemma lem4435440 {_106515 : Type'} : (@all (_106515 -> Prop)) = (@all (_106515 -> Prop)).
Proof. exact (eq_refl (@all (_106515 -> Prop))). Qed.
Lemma lem4435441 {_106515 _106516 : Type'} : (term137 _106515 _106516) = (term167 _106515 _106516).
Proof. exact (MK_COMB (@lem4435440 _106515) (@lem4435439 _106515 _106516)). Qed.
Lemma lem4435492 {_106515 _106516 : Type'} : (term139 _106515 _106516) = (term167 _106515 _106516).
Proof. exact (TRANS (@lem4435330 _106515 _106516) (@lem4435441 _106515 _106516)). Qed.
Lemma lem4435493 {_106515 _106516 : Type'} : (term167 _106515 _106516) = (term139 _106515 _106516).
Proof. exact (SYM (@lem4435492 _106515 _106516)). Qed.
Lemma lem4435495 (p : Prop) : p = (term138 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4435496 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : ((term116 _106515 _106516 k x' x) = (term159 _106515 _106516 x k x')) = (term168 _106515 _106516 x k x').
Proof. exact (@lem4435495 ((term116 _106515 _106516 k x' x) = (term159 _106515 _106516 x k x'))). Qed.
Lemma lem4435497 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term168 _106515 _106516 x k x') = ((term116 _106515 _106516 k x' x) = (term159 _106515 _106516 x k x')).
Proof. exact (SYM (@lem4435496 _106515 _106516 x k x')). Qed.
Lemma lem4435498 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (h1 : term169 _106515 _106516 x k x') : term169 _106515 _106516 x k x'.
Proof. exact (h1). Qed.
Lemma lem4435502 {_106515 : Type'} (x : _106515) (k : _106515 -> Prop) : (term170 _106515 x k) = (@IN _106515 x k).
Proof. exact (@lem16933 (@IN _106515 x k)). Qed.
Lemma lem4435504 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (x : _106515) : ((x' x) = (@ARB _106516)) = ((x' x) = (@ARB _106516)).
Proof. exact (eq_refl ((x' x) = (@ARB _106516))). Qed.
Lemma lem4435509 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515) : (term171 _106515 _106516 k x' x) = (term172 _106515 _106516 k x' x).
Proof. exact (@lem17362 (term173 _106515 x k) ((x' x) = (@ARB _106516))). Qed.
Lemma lem4435510 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4435511 {_106515 : Type'} (x : _106515) (k : _106515 -> Prop) : (term174 _106515 x k) = (term175 _106515 x k).
Proof. exact (MK_COMB (@lem4435510) (@lem4435502 _106515 x k)). Qed.
Lemma lem4435512 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515) : (term176 _106515 _106516 k x' x) = (term177 _106515 _106516 k x' x).
Proof. exact (MK_COMB (@lem4435511 _106515 x k) (@lem4435504 _106515 _106516 x' x)). Qed.
Lemma lem4435513 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515) : (term160 _106515 _106516 k x' x) = (term176 _106515 _106516 k x' x).
Proof. exact (@lem17265 (term173 _106515 x k) ((x' x) = (@ARB _106516))). Qed.
Lemma lem4435514 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515) : (term160 _106515 _106516 k x' x) = (term177 _106515 _106516 k x' x).
Proof. exact (TRANS (@lem4435513 _106515 _106516 k x' x) (@lem4435512 _106515 _106516 k x' x)). Qed.
Lemma lem4435515 {_106515 : Type'} (P : _106515 -> Prop) : (term178 _106515 P) = (term179 _106515 P).
Proof. exact (@lem18392 _106515 P). Qed.
Lemma lem4435516 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term180 _106515 _106516 k x') = (term181 _106515 _106516 k x').
Proof. exact (@lem4435515 _106515 (term161 _106515 _106516 k x')). Qed.
Lemma lem4435517 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515) : (term182 _106515 _106516 k x' x) = (term160 _106515 _106516 k x' x).
Proof. exact (eq_refl (term182 _106515 _106516 k x' x)). Qed.
Lemma lem4435518 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4435519 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515) : (term183 _106515 _106516 k x' x) = (term171 _106515 _106516 k x' x).
Proof. exact (MK_COMB (@lem4435518) (@lem4435517 _106515 _106516 k x' x)). Qed.
Lemma lem4435520 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515) : (term183 _106515 _106516 k x' x) = (term172 _106515 _106516 k x' x).
Proof. exact (TRANS (@lem4435519 _106515 _106516 k x' x) (@lem4435509 _106515 _106516 k x' x)). Qed.
Lemma lem4435521 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term184 _106515 _106516 k x') = (term185 _106515 _106516 k x').
Proof. exact (fun_ext (fun x : _106515 => @lem4435520 _106515 _106516 k x' x)). Qed.
Lemma lem4435522 {_106515 : Type'} : (@ex _106515) = (@ex _106515).
Proof. exact (eq_refl (@ex _106515)). Qed.
Lemma lem4435523 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term181 _106515 _106516 k x') = (term186 _106515 _106516 k x').
Proof. exact (MK_COMB (@lem4435522 _106515) (@lem4435521 _106515 _106516 k x')). Qed.
Lemma lem4435524 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term180 _106515 _106516 k x') = (term186 _106515 _106516 k x').
Proof. exact (TRANS (@lem4435516 _106515 _106516 k x') (@lem4435523 _106515 _106516 k x')). Qed.
Lemma lem4435525 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term161 _106515 _106516 k x') = (term187 _106515 _106516 k x').
Proof. exact (fun_ext (fun x : _106515 => @lem4435514 _106515 _106516 k x' x)). Qed.
Lemma lem4435526 {_106515 : Type'} : (@all _106515) = (@all _106515).
Proof. exact (eq_refl (@all _106515)). Qed.
Lemma lem4435527 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term101 _106515 _106516 k x') = (term188 _106515 _106516 k x').
Proof. exact (MK_COMB (@lem4435526 _106515) (@lem4435525 _106515 _106516 k x')). Qed.
Lemma lem4435536 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (i : _106515) : (term189 _106515 _106516 k x' x i) = (term190 _106515 _106516 k x' x i).
Proof. exact (@lem17362 (@IN _106515 i k) ((x' i) = (x i))). Qed.
Lemma lem4435541 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (i : _106515) : (term51 _106515 _106516 k x' x i) = (term191 _106515 _106516 k x' x i).
Proof. exact (@lem17265 (@IN _106515 i k) ((x' i) = (x i))). Qed.
Lemma lem4435542 {_106515 : Type'} (P : _106515 -> Prop) : (term178 _106515 P) = (term179 _106515 P).
Proof. exact (@lem18392 _106515 P). Qed.
Lemma lem4435543 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term192 _106515 _106516 k x' x) = (term193 _106515 _106516 k x' x).
Proof. exact (@lem4435542 _106515 (term53 _106515 _106516 k x' x)). Qed.
Lemma lem4435544 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (i : _106515) : (term194 _106515 _106516 k x' x i) = (term51 _106515 _106516 k x' x i).
Proof. exact (eq_refl (term194 _106515 _106516 k x' x i)). Qed.
Lemma lem4435545 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4435546 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (i : _106515) : (term195 _106515 _106516 k x' x i) = (term189 _106515 _106516 k x' x i).
Proof. exact (MK_COMB (@lem4435545) (@lem4435544 _106515 _106516 k x' x i)). Qed.
Lemma lem4435547 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (i : _106515) : (term195 _106515 _106516 k x' x i) = (term190 _106515 _106516 k x' x i).
Proof. exact (TRANS (@lem4435546 _106515 _106516 k x' x i) (@lem4435536 _106515 _106516 k x' x i)). Qed.
Lemma lem4435548 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term196 _106515 _106516 k x' x) = (term197 _106515 _106516 k x' x).
Proof. exact (fun_ext (fun i : _106515 => @lem4435547 _106515 _106516 k x' x i)). Qed.
Lemma lem4435549 {_106515 : Type'} : (@ex _106515) = (@ex _106515).
Proof. exact (eq_refl (@ex _106515)). Qed.
Lemma lem4435550 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term193 _106515 _106516 k x' x) = (term198 _106515 _106516 k x' x).
Proof. exact (MK_COMB (@lem4435549 _106515) (@lem4435548 _106515 _106516 k x' x)). Qed.
Lemma lem4435551 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term192 _106515 _106516 k x' x) = (term198 _106515 _106516 k x' x).
Proof. exact (TRANS (@lem4435543 _106515 _106516 k x' x) (@lem4435550 _106515 _106516 k x' x)). Qed.
Lemma lem4435552 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term53 _106515 _106516 k x' x) = (term199 _106515 _106516 k x' x).
Proof. exact (fun_ext (fun i : _106515 => @lem4435541 _106515 _106516 k x' x i)). Qed.
Lemma lem4435553 {_106515 : Type'} : (@all _106515) = (@all _106515).
Proof. exact (eq_refl (@all _106515)). Qed.
Lemma lem4435554 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term55 _106515 _106516 k x' x) = (term200 _106515 _106516 k x' x).
Proof. exact (MK_COMB (@lem4435553 _106515) (@lem4435552 _106515 _106516 k x' x)). Qed.
Lemma lem4435555 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4435556 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term201 _106515 _106516 k x') = (term202 _106515 _106516 k x').
Proof. exact (MK_COMB (@lem4435555) (@lem4435524 _106515 _106516 k x')). Qed.
Lemma lem4435557 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term203 _106515 _106516 k x' x) = (term204 _106515 _106516 k x' x).
Proof. exact (MK_COMB (@lem4435556 _106515 _106516 k x') (@lem4435551 _106515 _106516 k x' x)). Qed.
Lemma lem4435558 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term205 _106515 _106516 k x' x) = (term203 _106515 _106516 k x' x).
Proof. exact (@lem17045 (term101 _106515 _106516 k x') (term55 _106515 _106516 k x' x)). Qed.
Lemma lem4435559 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term205 _106515 _106516 k x' x) = (term204 _106515 _106516 k x' x).
Proof. exact (TRANS (@lem4435558 _106515 _106516 k x' x) (@lem4435557 _106515 _106516 k x' x)). Qed.
Lemma lem4435560 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4435561 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term115 _106515 _106516 k x') = (term206 _106515 _106516 k x').
Proof. exact (MK_COMB (@lem4435560) (@lem4435527 _106515 _106516 k x')). Qed.
Lemma lem4435562 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term116 _106515 _106516 k x' x) = (term207 _106515 _106516 k x' x).
Proof. exact (MK_COMB (@lem4435561 _106515 _106516 k x') (@lem4435554 _106515 _106516 k x' x)). Qed.
Lemma lem4435566 {_106515 : Type'} (x : _106515) (k : _106515 -> Prop) : (term170 _106515 x k) = (@IN _106515 x k).
Proof. exact (@lem16933 (@IN _106515 x k)). Qed.
Lemma lem4435567 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (x : _106515 -> _106516) (x'' : _106515) : (term208 _106515 _106516 x' x x'') = (term208 _106515 _106516 x' x x'').
Proof. exact (eq_refl (term208 _106515 _106516 x' x x'')). Qed.
Lemma lem4435569 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4435570 {_106515 : Type'} (x : _106515) (k : _106515 -> Prop) : (term209 _106515 x k) = (term210 _106515 x k).
Proof. exact (MK_COMB (@lem4435569) (@lem4435566 _106515 x k)). Qed.
Lemma lem4435571 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (x'' : _106515) : (term211 _106515 _106516 k x' x x'') = (term190 _106515 _106516 k x' x x'').
Proof. exact (MK_COMB (@lem4435570 _106515 x'' k) (@lem4435567 _106515 _106516 x' x x'')). Qed.
Lemma lem4435572 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (x'' : _106515) : (term212 _106515 _106516 k x' x x'') = (term211 _106515 _106516 k x' x x'').
Proof. exact (@lem17160 (term173 _106515 x'' k) ((x' x'') = (x x''))). Qed.
Lemma lem4435573 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (x'' : _106515) : (term212 _106515 _106516 k x' x x'') = (term190 _106515 _106516 k x' x x'').
Proof. exact (TRANS (@lem4435572 _106515 _106516 k x' x x'') (@lem4435571 _106515 _106516 k x' x x'')). Qed.
Lemma lem4435585 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515) : (term213 _106515 _106516 k x' x) = (term172 _106515 _106516 k x' x).
Proof. exact (@lem17160 (@IN _106515 x k) ((x' x) = (@ARB _106516))). Qed.
Lemma lem4435589 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4435590 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (x'' : _106515) : (term214 _106515 _106516 k x' x x'') = (term215 _106515 _106516 k x' x x'').
Proof. exact (MK_COMB (@lem4435589) (@lem4435573 _106515 _106516 k x' x x'')). Qed.
Lemma lem4435591 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (x'' : _106515) : (term216 _106515 _106516 x k x' x'') = (term217 _106515 _106516 x k x' x'').
Proof. exact (MK_COMB (@lem4435590 _106515 _106516 k x' x x'') (@lem4435585 _106515 _106516 k x' x'')). Qed.
Lemma lem4435592 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (x'' : _106515) : (term218 _106515 _106516 x k x' x'') = (term216 _106515 _106516 x k x' x'').
Proof. exact (@lem17045 (term191 _106515 _106516 k x' x x'') (term177 _106515 _106516 k x' x'')). Qed.
Lemma lem4435593 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (x'' : _106515) : (term218 _106515 _106516 x k x' x'') = (term217 _106515 _106516 x k x' x'').
Proof. exact (TRANS (@lem4435592 _106515 _106516 x k x' x'') (@lem4435591 _106515 _106516 x k x' x'')). Qed.
Lemma lem4435596 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (x'' : _106515) : (term157 _106515 _106516 x k x' x'') = (term157 _106515 _106516 x k x' x'').
Proof. exact (eq_refl (term157 _106515 _106516 x k x' x'')). Qed.
Lemma lem4435597 {_106515 : Type'} (P : _106515 -> Prop) : (term178 _106515 P) = (term179 _106515 P).
Proof. exact (@lem18392 _106515 P). Qed.
Lemma lem4435598 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term219 _106515 _106516 x k x') = (term220 _106515 _106516 x k x').
Proof. exact (@lem4435597 _106515 (term158 _106515 _106516 x k x')). Qed.
Lemma lem4435599 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (x'' : _106515) : (term221 _106515 _106516 x k x' x'') = (term157 _106515 _106516 x k x' x'').
Proof. exact (eq_refl (term221 _106515 _106516 x k x' x'')). Qed.
Lemma lem4435600 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4435601 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (x'' : _106515) : (term222 _106515 _106516 x k x' x'') = (term218 _106515 _106516 x k x' x'').
Proof. exact (MK_COMB (@lem4435600) (@lem4435599 _106515 _106516 x k x' x'')). Qed.
Lemma lem4435602 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (x'' : _106515) : (term222 _106515 _106516 x k x' x'') = (term217 _106515 _106516 x k x' x'').
Proof. exact (TRANS (@lem4435601 _106515 _106516 x k x' x'') (@lem4435593 _106515 _106516 x k x' x'')). Qed.
Lemma lem4435603 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term223 _106515 _106516 x k x') = (term224 _106515 _106516 x k x').
Proof. exact (fun_ext (fun x'' : _106515 => @lem4435602 _106515 _106516 x k x' x'')). Qed.
Lemma lem4435604 {_106515 : Type'} : (@ex _106515) = (@ex _106515).
Proof. exact (eq_refl (@ex _106515)). Qed.
Lemma lem4435605 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term220 _106515 _106516 x k x') = (term225 _106515 _106516 x k x').
Proof. exact (MK_COMB (@lem4435604 _106515) (@lem4435603 _106515 _106516 x k x')). Qed.
Lemma lem4435606 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term219 _106515 _106516 x k x') = (term225 _106515 _106516 x k x').
Proof. exact (TRANS (@lem4435598 _106515 _106516 x k x') (@lem4435605 _106515 _106516 x k x')). Qed.
Lemma lem4435607 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term158 _106515 _106516 x k x') = (term158 _106515 _106516 x k x').
Proof. exact (fun_ext (fun x'' : _106515 => @lem4435596 _106515 _106516 x k x' x'')). Qed.
Lemma lem4435608 {_106515 : Type'} : (@all _106515) = (@all _106515).
Proof. exact (eq_refl (@all _106515)). Qed.
Lemma lem4435609 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term159 _106515 _106516 x k x') = (term159 _106515 _106516 x k x').
Proof. exact (MK_COMB (@lem4435608 _106515) (@lem4435607 _106515 _106516 x k x')). Qed.
Lemma lem4435610 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4435611 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term226 _106515 _106516 k x' x) = (term227 _106515 _106516 k x' x).
Proof. exact (MK_COMB (@lem4435610) (@lem4435559 _106515 _106516 k x' x)). Qed.
Lemma lem4435612 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term228 _106515 _106516 x k x') = (term229 _106515 _106516 x k x').
Proof. exact (MK_COMB (@lem4435611 _106515 _106516 k x' x) (@lem4435609 _106515 _106516 x k x')). Qed.
Lemma lem4435613 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4435614 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term230 _106515 _106516 k x' x) = (term231 _106515 _106516 k x' x).
Proof. exact (MK_COMB (@lem4435613) (@lem4435562 _106515 _106516 k x' x)). Qed.
Lemma lem4435615 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term232 _106515 _106516 x k x') = (term233 _106515 _106516 x k x').
Proof. exact (MK_COMB (@lem4435614 _106515 _106516 k x' x) (@lem4435606 _106515 _106516 x k x')). Qed.
Lemma lem4435616 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4435617 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term234 _106515 _106516 x k x') = (term235 _106515 _106516 x k x').
Proof. exact (MK_COMB (@lem4435616) (@lem4435615 _106515 _106516 x k x')). Qed.
Lemma lem4435618 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term236 _106515 _106516 x k x') = (term237 _106515 _106516 x k x').
Proof. exact (MK_COMB (@lem4435617 _106515 _106516 x k x') (@lem4435612 _106515 _106516 x k x')). Qed.
Lemma lem4435619 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term169 _106515 _106516 x k x') = (term236 _106515 _106516 x k x').
Proof. exact (@lem17646 (term116 _106515 _106516 k x' x) (term159 _106515 _106516 x k x')). Qed.
Lemma lem4435620 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term169 _106515 _106516 x k x') = (term237 _106515 _106516 x k x').
Proof. exact (TRANS (@lem4435619 _106515 _106516 x k x') (@lem4435618 _106515 _106516 x k x')). Qed.
Lemma lem4435718 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term238 A P Q) = (term239 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem4435719 {_106515 : Type'} (P : _106515 -> Prop) (Q : _106515 -> Prop) : (term238 _106515 P Q) = (term239 _106515 P Q).
Proof. exact (@lem4435718 _106515 P Q). Qed.
Lemma lem4435720 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term240 _106515 _106516 x k x') = (term241 _106515 _106516 x k x').
Proof. exact (@lem4435719 _106515 (term197 _106515 _106516 k x' x) (term185 _106515 _106516 k x')). Qed.
Lemma lem4435721 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (x'' : _106515) : (term242 _106515 _106516 k x' x x'') = (term190 _106515 _106516 k x' x x'').
Proof. exact (eq_refl (term242 _106515 _106516 k x' x x'')). Qed.
Lemma lem4435722 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4435723 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (x'' : _106515) : (term243 _106515 _106516 k x' x x'') = (term215 _106515 _106516 k x' x x'').
Proof. exact (MK_COMB (@lem4435722) (@lem4435721 _106515 _106516 k x' x x'')). Qed.
Lemma lem4435724 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515) : (term244 _106515 _106516 k x' x) = (term172 _106515 _106516 k x' x).
Proof. exact (eq_refl (term244 _106515 _106516 k x' x)). Qed.
Lemma lem4435725 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (x'' : _106515) : (term245 _106515 _106516 x k x' x'') = (term217 _106515 _106516 x k x' x'').
Proof. exact (MK_COMB (@lem4435723 _106515 _106516 k x' x x'') (@lem4435724 _106515 _106516 k x' x'')). Qed.
Lemma lem4435726 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term246 _106515 _106516 x k x') = (term224 _106515 _106516 x k x').
Proof. exact (fun_ext (fun x'' : _106515 => @lem4435725 _106515 _106516 x k x' x'')). Qed.
Lemma lem4435727 {_106515 : Type'} : (@ex _106515) = (@ex _106515).
Proof. exact (eq_refl (@ex _106515)). Qed.
Lemma lem4435728 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term240 _106515 _106516 x k x') = (term225 _106515 _106516 x k x').
Proof. exact (MK_COMB (@lem4435727 _106515) (@lem4435726 _106515 _106516 x k x')). Qed.
Lemma lem4435729 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4435730 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term247 _106515 _106516 x k x') = (term248 _106515 _106516 x k x').
Proof. exact (MK_COMB (@lem4435729) (@lem4435728 _106515 _106516 x k x')). Qed.
Lemma lem4435731 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (x'' : _106515) : (term242 _106515 _106516 k x' x x'') = (term190 _106515 _106516 k x' x x'').
Proof. exact (eq_refl (term242 _106515 _106516 k x' x x'')). Qed.
Lemma lem4435732 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term249 _106515 _106516 k x' x) = (term197 _106515 _106516 k x' x).
Proof. exact (fun_ext (fun x'' : _106515 => @lem4435731 _106515 _106516 k x' x x'')). Qed.
Lemma lem4435733 {_106515 : Type'} : (@ex _106515) = (@ex _106515).
Proof. exact (eq_refl (@ex _106515)). Qed.
Lemma lem4435734 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term250 _106515 _106516 k x' x) = (term198 _106515 _106516 k x' x).
Proof. exact (MK_COMB (@lem4435733 _106515) (@lem4435732 _106515 _106516 k x' x)). Qed.
Lemma lem4435735 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4435736 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term251 _106515 _106516 k x' x) = (term252 _106515 _106516 k x' x).
Proof. exact (MK_COMB (@lem4435735) (@lem4435734 _106515 _106516 k x' x)). Qed.
Lemma lem4435737 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515) : (term244 _106515 _106516 k x' x) = (term172 _106515 _106516 k x' x).
Proof. exact (eq_refl (term244 _106515 _106516 k x' x)). Qed.
Lemma lem4435738 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term253 _106515 _106516 k x') = (term185 _106515 _106516 k x').
Proof. exact (fun_ext (fun x : _106515 => @lem4435737 _106515 _106516 k x' x)). Qed.
Lemma lem4435739 {_106515 : Type'} : (@ex _106515) = (@ex _106515).
Proof. exact (eq_refl (@ex _106515)). Qed.
Lemma lem4435740 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term254 _106515 _106516 k x') = (term186 _106515 _106516 k x').
Proof. exact (MK_COMB (@lem4435739 _106515) (@lem4435738 _106515 _106516 k x')). Qed.
Lemma lem4435741 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term241 _106515 _106516 x k x') = (term255 _106515 _106516 x k x').
Proof. exact (MK_COMB (@lem4435736 _106515 _106516 k x' x) (@lem4435740 _106515 _106516 k x')). Qed.
Lemma lem4435742 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : ((term240 _106515 _106516 x k x') = (term241 _106515 _106516 x k x')) = ((term225 _106515 _106516 x k x') = (term255 _106515 _106516 x k x')).
Proof. exact (MK_COMB (@lem4435730 _106515 _106516 x k x') (@lem4435741 _106515 _106516 x k x')). Qed.
Lemma lem4435743 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term225 _106515 _106516 x k x') = (term255 _106515 _106516 x k x').
Proof. exact (EQ_MP (@lem4435742 _106515 _106516 x k x') (@lem4435720 _106515 _106516 x k x')). Qed.
Lemma lem4435840 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term231 _106515 _106516 k x' x) = (term231 _106515 _106516 k x' x).
Proof. exact (eq_refl (term231 _106515 _106516 k x' x)). Qed.
Lemma lem4435841 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term233 _106515 _106516 x k x') = (term256 _106515 _106516 x k x').
Proof. exact (MK_COMB (@lem4435840 _106515 _106516 k x' x) (@lem4435743 _106515 _106516 x k x')). Qed.
Lemma lem4435842 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4435843 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term235 _106515 _106516 x k x') = (term257 _106515 _106516 x k x').
Proof. exact (MK_COMB (@lem4435842) (@lem4435841 _106515 _106516 x k x')). Qed.
Lemma lem4435941 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term258 A P Q) = (term259 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4435942 {_106515 : Type'} (P : _106515 -> Prop) (Q : _106515 -> Prop) : (term258 _106515 P Q) = (term259 _106515 P Q).
Proof. exact (@lem4435941 _106515 P Q). Qed.
Lemma lem4435943 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term260 _106515 _106516 x k x') = (term261 _106515 _106516 x k x').
Proof. exact (@lem4435942 _106515 (term199 _106515 _106516 k x' x) (term187 _106515 _106516 k x')). Qed.
Lemma lem4435944 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (x'' : _106515) : (term262 _106515 _106516 k x' x x'') = (term191 _106515 _106516 k x' x x'').
Proof. exact (eq_refl (term262 _106515 _106516 k x' x x'')). Qed.
Lemma lem4435945 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4435946 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (x'' : _106515) : (term263 _106515 _106516 k x' x x'') = (term264 _106515 _106516 k x' x x'').
Proof. exact (MK_COMB (@lem4435945) (@lem4435944 _106515 _106516 k x' x x'')). Qed.
Lemma lem4435947 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515) : (term265 _106515 _106516 k x' x) = (term177 _106515 _106516 k x' x).
Proof. exact (eq_refl (term265 _106515 _106516 k x' x)). Qed.
Lemma lem4435948 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (x'' : _106515) : (term266 _106515 _106516 x k x' x'') = (term157 _106515 _106516 x k x' x'').
Proof. exact (MK_COMB (@lem4435946 _106515 _106516 k x' x x'') (@lem4435947 _106515 _106516 k x' x'')). Qed.
Lemma lem4435949 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term267 _106515 _106516 x k x') = (term158 _106515 _106516 x k x').
Proof. exact (fun_ext (fun x'' : _106515 => @lem4435948 _106515 _106516 x k x' x'')). Qed.
Lemma lem4435950 {_106515 : Type'} : (@all _106515) = (@all _106515).
Proof. exact (eq_refl (@all _106515)). Qed.
Lemma lem4435951 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term260 _106515 _106516 x k x') = (term159 _106515 _106516 x k x').
Proof. exact (MK_COMB (@lem4435950 _106515) (@lem4435949 _106515 _106516 x k x')). Qed.
Lemma lem4435952 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4435953 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term268 _106515 _106516 x k x') = (term269 _106515 _106516 x k x').
Proof. exact (MK_COMB (@lem4435952) (@lem4435951 _106515 _106516 x k x')). Qed.
Lemma lem4435954 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (x'' : _106515) : (term262 _106515 _106516 k x' x x'') = (term191 _106515 _106516 k x' x x'').
Proof. exact (eq_refl (term262 _106515 _106516 k x' x x'')). Qed.
Lemma lem4435955 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term270 _106515 _106516 k x' x) = (term199 _106515 _106516 k x' x).
Proof. exact (fun_ext (fun x'' : _106515 => @lem4435954 _106515 _106516 k x' x x'')). Qed.
Lemma lem4435956 {_106515 : Type'} : (@all _106515) = (@all _106515).
Proof. exact (eq_refl (@all _106515)). Qed.
Lemma lem4435957 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term271 _106515 _106516 k x' x) = (term200 _106515 _106516 k x' x).
Proof. exact (MK_COMB (@lem4435956 _106515) (@lem4435955 _106515 _106516 k x' x)). Qed.
Lemma lem4435958 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4435959 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term272 _106515 _106516 k x' x) = (term273 _106515 _106516 k x' x).
Proof. exact (MK_COMB (@lem4435958) (@lem4435957 _106515 _106516 k x' x)). Qed.
Lemma lem4435960 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515) : (term265 _106515 _106516 k x' x) = (term177 _106515 _106516 k x' x).
Proof. exact (eq_refl (term265 _106515 _106516 k x' x)). Qed.
Lemma lem4435961 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term274 _106515 _106516 k x') = (term187 _106515 _106516 k x').
Proof. exact (fun_ext (fun x : _106515 => @lem4435960 _106515 _106516 k x' x)). Qed.
Lemma lem4435962 {_106515 : Type'} : (@all _106515) = (@all _106515).
Proof. exact (eq_refl (@all _106515)). Qed.
Lemma lem4435963 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term275 _106515 _106516 k x') = (term188 _106515 _106516 k x').
Proof. exact (MK_COMB (@lem4435962 _106515) (@lem4435961 _106515 _106516 k x')). Qed.
Lemma lem4435964 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term261 _106515 _106516 x k x') = (term276 _106515 _106516 x k x').
Proof. exact (MK_COMB (@lem4435959 _106515 _106516 k x' x) (@lem4435963 _106515 _106516 k x')). Qed.
Lemma lem4435965 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : ((term260 _106515 _106516 x k x') = (term261 _106515 _106516 x k x')) = ((term159 _106515 _106516 x k x') = (term276 _106515 _106516 x k x')).
Proof. exact (MK_COMB (@lem4435953 _106515 _106516 x k x') (@lem4435964 _106515 _106516 x k x')). Qed.
Lemma lem4435966 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term159 _106515 _106516 x k x') = (term276 _106515 _106516 x k x').
Proof. exact (EQ_MP (@lem4435965 _106515 _106516 x k x') (@lem4435943 _106515 _106516 x k x')). Qed.
Lemma lem4436063 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term227 _106515 _106516 k x' x) = (term227 _106515 _106516 k x' x).
Proof. exact (eq_refl (term227 _106515 _106516 k x' x)). Qed.
Lemma lem4436064 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term229 _106515 _106516 x k x') = (term277 _106515 _106516 x k x').
Proof. exact (MK_COMB (@lem4436063 _106515 _106516 k x' x) (@lem4435966 _106515 _106516 x k x')). Qed.
Lemma lem4436065 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term237 _106515 _106516 x k x') = (term278 _106515 _106516 x k x').
Proof. exact (MK_COMB (@lem4435843 _106515 _106516 x k x') (@lem4436064 _106515 _106516 x k x')). Qed.
Lemma lem4436067 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term239 A P Q) = (term238 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4436068 {_106515 : Type'} (P : _106515 -> Prop) (Q : _106515 -> Prop) : (term239 _106515 P Q) = (term238 _106515 P Q).
Proof. exact (@lem4436067 _106515 P Q). Qed.
Lemma lem4436069 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term241 _106515 _106516 x k x') = (term240 _106515 _106516 x k x').
Proof. exact (@lem4436068 _106515 (term197 _106515 _106516 k x' x) (term185 _106515 _106516 k x')). Qed.
Lemma lem4436070 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (x'' : _106515) : (term242 _106515 _106516 k x' x x'') = (term190 _106515 _106516 k x' x x'').
Proof. exact (eq_refl (term242 _106515 _106516 k x' x x'')). Qed.
Lemma lem4436071 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term249 _106515 _106516 k x' x) = (term197 _106515 _106516 k x' x).
Proof. exact (fun_ext (fun x'' : _106515 => @lem4436070 _106515 _106516 k x' x x'')). Qed.
Lemma lem4436072 {_106515 : Type'} : (@ex _106515) = (@ex _106515).
Proof. exact (eq_refl (@ex _106515)). Qed.
Lemma lem4436073 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term250 _106515 _106516 k x' x) = (term198 _106515 _106516 k x' x).
Proof. exact (MK_COMB (@lem4436072 _106515) (@lem4436071 _106515 _106516 k x' x)). Qed.
Lemma lem4436074 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4436075 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term251 _106515 _106516 k x' x) = (term252 _106515 _106516 k x' x).
Proof. exact (MK_COMB (@lem4436074) (@lem4436073 _106515 _106516 k x' x)). Qed.
Lemma lem4436076 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515) : (term244 _106515 _106516 k x' x) = (term172 _106515 _106516 k x' x).
Proof. exact (eq_refl (term244 _106515 _106516 k x' x)). Qed.
Lemma lem4436077 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term253 _106515 _106516 k x') = (term185 _106515 _106516 k x').
Proof. exact (fun_ext (fun x : _106515 => @lem4436076 _106515 _106516 k x' x)). Qed.
Lemma lem4436078 {_106515 : Type'} : (@ex _106515) = (@ex _106515).
Proof. exact (eq_refl (@ex _106515)). Qed.
Lemma lem4436079 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term254 _106515 _106516 k x') = (term186 _106515 _106516 k x').
Proof. exact (MK_COMB (@lem4436078 _106515) (@lem4436077 _106515 _106516 k x')). Qed.
Lemma lem4436080 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term241 _106515 _106516 x k x') = (term255 _106515 _106516 x k x').
Proof. exact (MK_COMB (@lem4436075 _106515 _106516 k x' x) (@lem4436079 _106515 _106516 k x')). Qed.
Lemma lem4436081 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4436082 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term279 _106515 _106516 x k x') = (term280 _106515 _106516 x k x').
Proof. exact (MK_COMB (@lem4436081) (@lem4436080 _106515 _106516 x k x')). Qed.
Lemma lem4436083 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (x'' : _106515) : (term242 _106515 _106516 k x' x x'') = (term190 _106515 _106516 k x' x x'').
Proof. exact (eq_refl (term242 _106515 _106516 k x' x x'')). Qed.
Lemma lem4436084 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4436085 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (x'' : _106515) : (term243 _106515 _106516 k x' x x'') = (term215 _106515 _106516 k x' x x'').
Proof. exact (MK_COMB (@lem4436084) (@lem4436083 _106515 _106516 k x' x x'')). Qed.
Lemma lem4436086 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515) : (term244 _106515 _106516 k x' x) = (term172 _106515 _106516 k x' x).
Proof. exact (eq_refl (term244 _106515 _106516 k x' x)). Qed.
Lemma lem4436087 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (x'' : _106515) : (term245 _106515 _106516 x k x' x'') = (term217 _106515 _106516 x k x' x'').
Proof. exact (MK_COMB (@lem4436085 _106515 _106516 k x' x x'') (@lem4436086 _106515 _106516 k x' x'')). Qed.
Lemma lem4436088 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term246 _106515 _106516 x k x') = (term224 _106515 _106516 x k x').
Proof. exact (fun_ext (fun x'' : _106515 => @lem4436087 _106515 _106516 x k x' x'')). Qed.
Lemma lem4436089 {_106515 : Type'} : (@ex _106515) = (@ex _106515).
Proof. exact (eq_refl (@ex _106515)). Qed.
Lemma lem4436090 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term240 _106515 _106516 x k x') = (term225 _106515 _106516 x k x').
Proof. exact (MK_COMB (@lem4436089 _106515) (@lem4436088 _106515 _106516 x k x')). Qed.
Lemma lem4436091 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : ((term241 _106515 _106516 x k x') = (term240 _106515 _106516 x k x')) = ((term255 _106515 _106516 x k x') = (term225 _106515 _106516 x k x')).
Proof. exact (MK_COMB (@lem4436082 _106515 _106516 x k x') (@lem4436090 _106515 _106516 x k x')). Qed.
Lemma lem4436092 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term255 _106515 _106516 x k x') = (term225 _106515 _106516 x k x').
Proof. exact (EQ_MP (@lem4436091 _106515 _106516 x k x') (@lem4436069 _106515 _106516 x k x')). Qed.
Lemma lem4436093 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term231 _106515 _106516 k x' x) = (term231 _106515 _106516 k x' x).
Proof. exact (eq_refl (term231 _106515 _106516 k x' x)). Qed.
Lemma lem4436094 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term256 _106515 _106516 x k x') = (term233 _106515 _106516 x k x').
Proof. exact (MK_COMB (@lem4436093 _106515 _106516 k x' x) (@lem4436092 _106515 _106516 x k x')). Qed.
Lemma lem4436096 {A : Type'} (P : Prop) (Q : A -> Prop) : (term281 A P Q) = (term282 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4436097 {_106515 : Type'} (P : Prop) (Q : _106515 -> Prop) : (term281 _106515 P Q) = (term282 _106515 P Q).
Proof. exact (@lem4436096 _106515 P Q). Qed.
Lemma lem4436098 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term283 _106515 _106516 x k x') = (term284 _106515 _106516 x k x').
Proof. exact (@lem4436097 _106515 (term207 _106515 _106516 k x' x) (term224 _106515 _106516 x k x')). Qed.
Lemma lem4436099 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (x'' : _106515) : (term285 _106515 _106516 x k x' x'') = (term217 _106515 _106516 x k x' x'').
Proof. exact (eq_refl (term285 _106515 _106516 x k x' x'')). Qed.
Lemma lem4436100 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term286 _106515 _106516 x k x') = (term224 _106515 _106516 x k x').
Proof. exact (fun_ext (fun x'' : _106515 => @lem4436099 _106515 _106516 x k x' x'')). Qed.
Lemma lem4436101 {_106515 : Type'} : (@ex _106515) = (@ex _106515).
Proof. exact (eq_refl (@ex _106515)). Qed.
Lemma lem4436102 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term287 _106515 _106516 x k x') = (term225 _106515 _106516 x k x').
Proof. exact (MK_COMB (@lem4436101 _106515) (@lem4436100 _106515 _106516 x k x')). Qed.
Lemma lem4436103 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term231 _106515 _106516 k x' x) = (term231 _106515 _106516 k x' x).
Proof. exact (eq_refl (term231 _106515 _106516 k x' x)). Qed.
Lemma lem4436104 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term283 _106515 _106516 x k x') = (term233 _106515 _106516 x k x').
Proof. exact (MK_COMB (@lem4436103 _106515 _106516 k x' x) (@lem4436102 _106515 _106516 x k x')). Qed.
Lemma lem4436105 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4436106 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term288 _106515 _106516 x k x') = (term289 _106515 _106516 x k x').
Proof. exact (MK_COMB (@lem4436105) (@lem4436104 _106515 _106516 x k x')). Qed.
Lemma lem4436107 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (x'' : _106515) : (term285 _106515 _106516 x k x' x'') = (term217 _106515 _106516 x k x' x'').
Proof. exact (eq_refl (term285 _106515 _106516 x k x' x'')). Qed.
Lemma lem4436108 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term231 _106515 _106516 k x' x) = (term231 _106515 _106516 k x' x).
Proof. exact (eq_refl (term231 _106515 _106516 k x' x)). Qed.
Lemma lem4436109 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (x'' : _106515) : (term290 _106515 _106516 x k x' x'') = (term291 _106515 _106516 x k x' x'').
Proof. exact (MK_COMB (@lem4436108 _106515 _106516 k x' x) (@lem4436107 _106515 _106516 x k x' x'')). Qed.
Lemma lem4436110 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term292 _106515 _106516 x k x') = (term293 _106515 _106516 x k x').
Proof. exact (fun_ext (fun x'' : _106515 => @lem4436109 _106515 _106516 x k x' x'')). Qed.
Lemma lem4436111 {_106515 : Type'} : (@ex _106515) = (@ex _106515).
Proof. exact (eq_refl (@ex _106515)). Qed.
Lemma lem4436112 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term284 _106515 _106516 x k x') = (term294 _106515 _106516 x k x').
Proof. exact (MK_COMB (@lem4436111 _106515) (@lem4436110 _106515 _106516 x k x')). Qed.
Lemma lem4436113 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : ((term283 _106515 _106516 x k x') = (term284 _106515 _106516 x k x')) = ((term233 _106515 _106516 x k x') = (term294 _106515 _106516 x k x')).
Proof. exact (MK_COMB (@lem4436106 _106515 _106516 x k x') (@lem4436112 _106515 _106516 x k x')). Qed.
Lemma lem4436114 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term233 _106515 _106516 x k x') = (term294 _106515 _106516 x k x').
Proof. exact (EQ_MP (@lem4436113 _106515 _106516 x k x') (@lem4436098 _106515 _106516 x k x')). Qed.
Lemma lem4436115 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term256 _106515 _106516 x k x') = (term294 _106515 _106516 x k x').
Proof. exact (TRANS (@lem4436094 _106515 _106516 x k x') (@lem4436114 _106515 _106516 x k x')). Qed.
Lemma lem4436116 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4436117 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term257 _106515 _106516 x k x') = (term295 _106515 _106516 x k x').
Proof. exact (MK_COMB (@lem4436116) (@lem4436115 _106515 _106516 x k x')). Qed.
Lemma lem4436119 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term239 A P Q) = (term238 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4436120 {_106515 : Type'} (P : _106515 -> Prop) (Q : _106515 -> Prop) : (term239 _106515 P Q) = (term238 _106515 P Q).
Proof. exact (@lem4436119 _106515 P Q). Qed.
Lemma lem4436121 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term296 _106515 _106516 k x' x) = (term297 _106515 _106516 k x' x).
Proof. exact (@lem4436120 _106515 (term185 _106515 _106516 k x') (term197 _106515 _106516 k x' x)). Qed.
Lemma lem4436122 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (i : _106515) : (term244 _106515 _106516 k x' i) = (term172 _106515 _106516 k x' i).
Proof. exact (eq_refl (term244 _106515 _106516 k x' i)). Qed.
Lemma lem4436123 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term253 _106515 _106516 k x') = (term185 _106515 _106516 k x').
Proof. exact (fun_ext (fun i : _106515 => @lem4436122 _106515 _106516 k x' i)). Qed.
Lemma lem4436124 {_106515 : Type'} : (@ex _106515) = (@ex _106515).
Proof. exact (eq_refl (@ex _106515)). Qed.
Lemma lem4436125 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term254 _106515 _106516 k x') = (term186 _106515 _106516 k x').
Proof. exact (MK_COMB (@lem4436124 _106515) (@lem4436123 _106515 _106516 k x')). Qed.
Lemma lem4436126 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4436127 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term298 _106515 _106516 k x') = (term202 _106515 _106516 k x').
Proof. exact (MK_COMB (@lem4436126) (@lem4436125 _106515 _106516 k x')). Qed.
Lemma lem4436128 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (i : _106515) : (term242 _106515 _106516 k x' x i) = (term190 _106515 _106516 k x' x i).
Proof. exact (eq_refl (term242 _106515 _106516 k x' x i)). Qed.
Lemma lem4436129 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term249 _106515 _106516 k x' x) = (term197 _106515 _106516 k x' x).
Proof. exact (fun_ext (fun i : _106515 => @lem4436128 _106515 _106516 k x' x i)). Qed.
Lemma lem4436130 {_106515 : Type'} : (@ex _106515) = (@ex _106515).
Proof. exact (eq_refl (@ex _106515)). Qed.
Lemma lem4436131 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term250 _106515 _106516 k x' x) = (term198 _106515 _106516 k x' x).
Proof. exact (MK_COMB (@lem4436130 _106515) (@lem4436129 _106515 _106516 k x' x)). Qed.
Lemma lem4436132 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term296 _106515 _106516 k x' x) = (term204 _106515 _106516 k x' x).
Proof. exact (MK_COMB (@lem4436127 _106515 _106516 k x') (@lem4436131 _106515 _106516 k x' x)). Qed.
Lemma lem4436133 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4436134 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term299 _106515 _106516 k x' x) = (term300 _106515 _106516 k x' x).
Proof. exact (MK_COMB (@lem4436133) (@lem4436132 _106515 _106516 k x' x)). Qed.
Lemma lem4436135 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (i : _106515) : (term244 _106515 _106516 k x' i) = (term172 _106515 _106516 k x' i).
Proof. exact (eq_refl (term244 _106515 _106516 k x' i)). Qed.
Lemma lem4436136 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4436137 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (i : _106515) : (term301 _106515 _106516 k x' i) = (term302 _106515 _106516 k x' i).
Proof. exact (MK_COMB (@lem4436136) (@lem4436135 _106515 _106516 k x' i)). Qed.
Lemma lem4436138 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (i : _106515) : (term242 _106515 _106516 k x' x i) = (term190 _106515 _106516 k x' x i).
Proof. exact (eq_refl (term242 _106515 _106516 k x' x i)). Qed.
Lemma lem4436139 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (i : _106515) : (term303 _106515 _106516 k x' x i) = (term304 _106515 _106516 k x' x i).
Proof. exact (MK_COMB (@lem4436137 _106515 _106516 k x' i) (@lem4436138 _106515 _106516 k x' x i)). Qed.
Lemma lem4436140 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term305 _106515 _106516 k x' x) = (term306 _106515 _106516 k x' x).
Proof. exact (fun_ext (fun i : _106515 => @lem4436139 _106515 _106516 k x' x i)). Qed.
Lemma lem4436141 {_106515 : Type'} : (@ex _106515) = (@ex _106515).
Proof. exact (eq_refl (@ex _106515)). Qed.
Lemma lem4436142 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term297 _106515 _106516 k x' x) = (term307 _106515 _106516 k x' x).
Proof. exact (MK_COMB (@lem4436141 _106515) (@lem4436140 _106515 _106516 k x' x)). Qed.
Lemma lem4436143 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : ((term296 _106515 _106516 k x' x) = (term297 _106515 _106516 k x' x)) = ((term204 _106515 _106516 k x' x) = (term307 _106515 _106516 k x' x)).
Proof. exact (MK_COMB (@lem4436134 _106515 _106516 k x' x) (@lem4436142 _106515 _106516 k x' x)). Qed.
Lemma lem4436144 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term204 _106515 _106516 k x' x) = (term307 _106515 _106516 k x' x).
Proof. exact (EQ_MP (@lem4436143 _106515 _106516 k x' x) (@lem4436121 _106515 _106516 k x' x)). Qed.
Lemma lem4436147 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term308 _106515 _106516 k x' x) = (term308 _106515 _106516 k x' x).
Proof. exact (eq_refl (term308 _106515 _106516 k x' x)). Qed.
Lemma lem4436148 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term308 _106515 _106516 k x' x) = ((term204 _106515 _106516 k x' x) = (term307 _106515 _106516 k x' x)).
Proof. exact (eq_refl (term308 _106515 _106516 k x' x)). Qed.
Lemma lem4436149 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term309 _106515 _106516 k x' x) = (term309 _106515 _106516 k x' x).
Proof. exact (eq_refl (term309 _106515 _106516 k x' x)). Qed.
Lemma lem4436150 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : ((term308 _106515 _106516 k x' x) = (term308 _106515 _106516 k x' x)) = ((term308 _106515 _106516 k x' x) = ((term204 _106515 _106516 k x' x) = (term307 _106515 _106516 k x' x))).
Proof. exact (MK_COMB (@lem4436149 _106515 _106516 k x' x) (@lem4436148 _106515 _106516 k x' x)). Qed.
Lemma lem4436151 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term308 _106515 _106516 k x' x) = ((term204 _106515 _106516 k x' x) = (term307 _106515 _106516 k x' x)).
Proof. exact (eq_refl (term308 _106515 _106516 k x' x)). Qed.
Lemma lem4436152 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4436153 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term309 _106515 _106516 k x' x) = (term310 _106515 _106516 k x' x).
Proof. exact (MK_COMB (@lem4436152) (@lem4436151 _106515 _106516 k x' x)). Qed.
Lemma lem4436154 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : ((term204 _106515 _106516 k x' x) = (term307 _106515 _106516 k x' x)) = ((term204 _106515 _106516 k x' x) = (term307 _106515 _106516 k x' x)).
Proof. exact (eq_refl ((term204 _106515 _106516 k x' x) = (term307 _106515 _106516 k x' x))). Qed.
Lemma lem4436155 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : ((term308 _106515 _106516 k x' x) = ((term204 _106515 _106516 k x' x) = (term307 _106515 _106516 k x' x))) = (((term204 _106515 _106516 k x' x) = (term307 _106515 _106516 k x' x)) = ((term204 _106515 _106516 k x' x) = (term307 _106515 _106516 k x' x))).
Proof. exact (MK_COMB (@lem4436153 _106515 _106516 k x' x) (@lem4436154 _106515 _106516 k x' x)). Qed.
Lemma lem4436156 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : ((term308 _106515 _106516 k x' x) = (term308 _106515 _106516 k x' x)) = (((term204 _106515 _106516 k x' x) = (term307 _106515 _106516 k x' x)) = ((term204 _106515 _106516 k x' x) = (term307 _106515 _106516 k x' x))).
Proof. exact (TRANS (@lem4436150 _106515 _106516 k x' x) (@lem4436155 _106515 _106516 k x' x)). Qed.
Lemma lem4436157 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : ((term204 _106515 _106516 k x' x) = (term307 _106515 _106516 k x' x)) = ((term204 _106515 _106516 k x' x) = (term307 _106515 _106516 k x' x)).
Proof. exact (EQ_MP (@lem4436156 _106515 _106516 k x' x) (@lem4436147 _106515 _106516 k x' x)). Qed.
Lemma lem4436158 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term204 _106515 _106516 k x' x) = (term307 _106515 _106516 k x' x).
Proof. exact (EQ_MP (@lem4436157 _106515 _106516 k x' x) (@lem4436144 _106515 _106516 k x' x)). Qed.
Lemma lem4436159 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4436160 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term227 _106515 _106516 k x' x) = (term311 _106515 _106516 k x' x).
Proof. exact (MK_COMB (@lem4436159) (@lem4436158 _106515 _106516 k x' x)). Qed.
Lemma lem4436161 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term276 _106515 _106516 x k x') = (term276 _106515 _106516 x k x').
Proof. exact (eq_refl (term276 _106515 _106516 x k x')). Qed.
Lemma lem4436162 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term277 _106515 _106516 x k x') = (term312 _106515 _106516 x k x').
Proof. exact (MK_COMB (@lem4436160 _106515 _106516 k x' x) (@lem4436161 _106515 _106516 x k x')). Qed.
Lemma lem4436164 {A : Type'} (P : A -> Prop) (Q : Prop) : (term313 A P Q) = (term314 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4436165 {_106515 : Type'} (P : _106515 -> Prop) (Q : Prop) : (term313 _106515 P Q) = (term314 _106515 P Q).
Proof. exact (@lem4436164 _106515 P Q). Qed.
Lemma lem4436166 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term315 _106515 _106516 x k x') = (term316 _106515 _106516 x k x').
Proof. exact (@lem4436165 _106515 (term306 _106515 _106516 k x' x) (term276 _106515 _106516 x k x')). Qed.
Lemma lem4436167 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (i : _106515) : (term317 _106515 _106516 k x' x i) = (term304 _106515 _106516 k x' x i).
Proof. exact (eq_refl (term317 _106515 _106516 k x' x i)). Qed.
Lemma lem4436168 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term318 _106515 _106516 k x' x) = (term306 _106515 _106516 k x' x).
Proof. exact (fun_ext (fun i : _106515 => @lem4436167 _106515 _106516 k x' x i)). Qed.
Lemma lem4436169 {_106515 : Type'} : (@ex _106515) = (@ex _106515).
Proof. exact (eq_refl (@ex _106515)). Qed.
Lemma lem4436170 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term319 _106515 _106516 k x' x) = (term307 _106515 _106516 k x' x).
Proof. exact (MK_COMB (@lem4436169 _106515) (@lem4436168 _106515 _106516 k x' x)). Qed.
Lemma lem4436171 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4436172 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term320 _106515 _106516 k x' x) = (term311 _106515 _106516 k x' x).
Proof. exact (MK_COMB (@lem4436171) (@lem4436170 _106515 _106516 k x' x)). Qed.
Lemma lem4436173 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term276 _106515 _106516 x k x') = (term276 _106515 _106516 x k x').
Proof. exact (eq_refl (term276 _106515 _106516 x k x')). Qed.
Lemma lem4436174 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term315 _106515 _106516 x k x') = (term312 _106515 _106516 x k x').
Proof. exact (MK_COMB (@lem4436172 _106515 _106516 k x' x) (@lem4436173 _106515 _106516 x k x')). Qed.
Lemma lem4436175 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4436176 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term321 _106515 _106516 x k x') = (term322 _106515 _106516 x k x').
Proof. exact (MK_COMB (@lem4436175) (@lem4436174 _106515 _106516 x k x')). Qed.
Lemma lem4436177 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (i : _106515) : (term317 _106515 _106516 k x' x i) = (term304 _106515 _106516 k x' x i).
Proof. exact (eq_refl (term317 _106515 _106516 k x' x i)). Qed.
Lemma lem4436178 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4436179 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (i : _106515) : (term323 _106515 _106516 k x' x i) = (term324 _106515 _106516 k x' x i).
Proof. exact (MK_COMB (@lem4436178) (@lem4436177 _106515 _106516 k x' x i)). Qed.
Lemma lem4436180 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term276 _106515 _106516 x k x') = (term276 _106515 _106516 x k x').
Proof. exact (eq_refl (term276 _106515 _106516 x k x')). Qed.
Lemma lem4436181 {_106515 _106516 : Type'} (i : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term325 _106515 _106516 i x k x') = (term326 _106515 _106516 i x k x').
Proof. exact (MK_COMB (@lem4436179 _106515 _106516 k x' x i) (@lem4436180 _106515 _106516 x k x')). Qed.
Lemma lem4436182 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term327 _106515 _106516 x k x') = (term328 _106515 _106516 x k x').
Proof. exact (fun_ext (fun i : _106515 => @lem4436181 _106515 _106516 i x k x')). Qed.
Lemma lem4436183 {_106515 : Type'} : (@ex _106515) = (@ex _106515).
Proof. exact (eq_refl (@ex _106515)). Qed.
Lemma lem4436184 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term316 _106515 _106516 x k x') = (term329 _106515 _106516 x k x').
Proof. exact (MK_COMB (@lem4436183 _106515) (@lem4436182 _106515 _106516 x k x')). Qed.
Lemma lem4436185 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : ((term315 _106515 _106516 x k x') = (term316 _106515 _106516 x k x')) = ((term312 _106515 _106516 x k x') = (term329 _106515 _106516 x k x')).
Proof. exact (MK_COMB (@lem4436176 _106515 _106516 x k x') (@lem4436184 _106515 _106516 x k x')). Qed.
Lemma lem4436186 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term312 _106515 _106516 x k x') = (term329 _106515 _106516 x k x').
Proof. exact (EQ_MP (@lem4436185 _106515 _106516 x k x') (@lem4436166 _106515 _106516 x k x')). Qed.
Lemma lem4436187 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term277 _106515 _106516 x k x') = (term329 _106515 _106516 x k x').
Proof. exact (TRANS (@lem4436162 _106515 _106516 x k x') (@lem4436186 _106515 _106516 x k x')). Qed.
Lemma lem4436188 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term278 _106515 _106516 x k x') = (term330 _106515 _106516 x k x').
Proof. exact (MK_COMB (@lem4436117 _106515 _106516 x k x') (@lem4436187 _106515 _106516 x k x')). Qed.
Lemma lem4436190 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term239 A P Q) = (term238 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4436191 {_106515 : Type'} (P : _106515 -> Prop) (Q : _106515 -> Prop) : (term239 _106515 P Q) = (term238 _106515 P Q).
Proof. exact (@lem4436190 _106515 P Q). Qed.
Lemma lem4436192 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term331 _106515 _106516 x k x') = (term332 _106515 _106516 x k x').
Proof. exact (@lem4436191 _106515 (term293 _106515 _106516 x k x') (term328 _106515 _106516 x k x')). Qed.
Lemma lem4436193 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (i : _106515) : (term333 _106515 _106516 x k x' i) = (term291 _106515 _106516 x k x' i).
Proof. exact (eq_refl (term333 _106515 _106516 x k x' i)). Qed.
Lemma lem4436194 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term334 _106515 _106516 x k x') = (term293 _106515 _106516 x k x').
Proof. exact (fun_ext (fun i : _106515 => @lem4436193 _106515 _106516 x k x' i)). Qed.
Lemma lem4436195 {_106515 : Type'} : (@ex _106515) = (@ex _106515).
Proof. exact (eq_refl (@ex _106515)). Qed.
Lemma lem4436196 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term335 _106515 _106516 x k x') = (term294 _106515 _106516 x k x').
Proof. exact (MK_COMB (@lem4436195 _106515) (@lem4436194 _106515 _106516 x k x')). Qed.
Lemma lem4436197 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4436198 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term336 _106515 _106516 x k x') = (term295 _106515 _106516 x k x').
Proof. exact (MK_COMB (@lem4436197) (@lem4436196 _106515 _106516 x k x')). Qed.
Lemma lem4436199 {_106515 _106516 : Type'} (i : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term337 _106515 _106516 x k x' i) = (term326 _106515 _106516 i x k x').
Proof. exact (eq_refl (term337 _106515 _106516 x k x' i)). Qed.
Lemma lem4436200 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term338 _106515 _106516 x k x') = (term328 _106515 _106516 x k x').
Proof. exact (fun_ext (fun i : _106515 => @lem4436199 _106515 _106516 i x k x')). Qed.
Lemma lem4436201 {_106515 : Type'} : (@ex _106515) = (@ex _106515).
Proof. exact (eq_refl (@ex _106515)). Qed.
Lemma lem4436202 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term339 _106515 _106516 x k x') = (term329 _106515 _106516 x k x').
Proof. exact (MK_COMB (@lem4436201 _106515) (@lem4436200 _106515 _106516 x k x')). Qed.
Lemma lem4436203 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term331 _106515 _106516 x k x') = (term330 _106515 _106516 x k x').
Proof. exact (MK_COMB (@lem4436198 _106515 _106516 x k x') (@lem4436202 _106515 _106516 x k x')). Qed.
Lemma lem4436204 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4436205 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term340 _106515 _106516 x k x') = (term341 _106515 _106516 x k x').
Proof. exact (MK_COMB (@lem4436204) (@lem4436203 _106515 _106516 x k x')). Qed.
Lemma lem4436206 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (i : _106515) : (term333 _106515 _106516 x k x' i) = (term291 _106515 _106516 x k x' i).
Proof. exact (eq_refl (term333 _106515 _106516 x k x' i)). Qed.
Lemma lem4436207 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4436208 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (i : _106515) : (term342 _106515 _106516 x k x' i) = (term343 _106515 _106516 x k x' i).
Proof. exact (MK_COMB (@lem4436207) (@lem4436206 _106515 _106516 x k x' i)). Qed.
Lemma lem4436209 {_106515 _106516 : Type'} (i : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term337 _106515 _106516 x k x' i) = (term326 _106515 _106516 i x k x').
Proof. exact (eq_refl (term337 _106515 _106516 x k x' i)). Qed.
Lemma lem4436210 {_106515 _106516 : Type'} (i : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term344 _106515 _106516 x k x' i) = (term345 _106515 _106516 i x k x').
Proof. exact (MK_COMB (@lem4436208 _106515 _106516 x k x' i) (@lem4436209 _106515 _106516 i x k x')). Qed.
Lemma lem4436211 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term346 _106515 _106516 x k x') = (term347 _106515 _106516 x k x').
Proof. exact (fun_ext (fun i : _106515 => @lem4436210 _106515 _106516 i x k x')). Qed.
Lemma lem4436212 {_106515 : Type'} : (@ex _106515) = (@ex _106515).
Proof. exact (eq_refl (@ex _106515)). Qed.
Lemma lem4436213 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term332 _106515 _106516 x k x') = (term348 _106515 _106516 x k x').
Proof. exact (MK_COMB (@lem4436212 _106515) (@lem4436211 _106515 _106516 x k x')). Qed.
Lemma lem4436214 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : ((term331 _106515 _106516 x k x') = (term332 _106515 _106516 x k x')) = ((term330 _106515 _106516 x k x') = (term348 _106515 _106516 x k x')).
Proof. exact (MK_COMB (@lem4436205 _106515 _106516 x k x') (@lem4436213 _106515 _106516 x k x')). Qed.
Lemma lem4436215 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term330 _106515 _106516 x k x') = (term348 _106515 _106516 x k x').
Proof. exact (EQ_MP (@lem4436214 _106515 _106516 x k x') (@lem4436192 _106515 _106516 x k x')). Qed.
Lemma lem4436218 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term349 _106515 _106516 x k x') = (term349 _106515 _106516 x k x').
Proof. exact (eq_refl (term349 _106515 _106516 x k x')). Qed.
Lemma lem4436219 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term349 _106515 _106516 x k x') = ((term330 _106515 _106516 x k x') = (term348 _106515 _106516 x k x')).
Proof. exact (eq_refl (term349 _106515 _106516 x k x')). Qed.
Lemma lem4436220 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term350 _106515 _106516 x k x') = (term350 _106515 _106516 x k x').
Proof. exact (eq_refl (term350 _106515 _106516 x k x')). Qed.
Lemma lem4436221 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : ((term349 _106515 _106516 x k x') = (term349 _106515 _106516 x k x')) = ((term349 _106515 _106516 x k x') = ((term330 _106515 _106516 x k x') = (term348 _106515 _106516 x k x'))).
Proof. exact (MK_COMB (@lem4436220 _106515 _106516 x k x') (@lem4436219 _106515 _106516 x k x')). Qed.
Lemma lem4436222 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term349 _106515 _106516 x k x') = ((term330 _106515 _106516 x k x') = (term348 _106515 _106516 x k x')).
Proof. exact (eq_refl (term349 _106515 _106516 x k x')). Qed.
Lemma lem4436223 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4436224 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term350 _106515 _106516 x k x') = (term351 _106515 _106516 x k x').
Proof. exact (MK_COMB (@lem4436223) (@lem4436222 _106515 _106516 x k x')). Qed.
Lemma lem4436225 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : ((term330 _106515 _106516 x k x') = (term348 _106515 _106516 x k x')) = ((term330 _106515 _106516 x k x') = (term348 _106515 _106516 x k x')).
Proof. exact (eq_refl ((term330 _106515 _106516 x k x') = (term348 _106515 _106516 x k x'))). Qed.
Lemma lem4436226 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : ((term349 _106515 _106516 x k x') = ((term330 _106515 _106516 x k x') = (term348 _106515 _106516 x k x'))) = (((term330 _106515 _106516 x k x') = (term348 _106515 _106516 x k x')) = ((term330 _106515 _106516 x k x') = (term348 _106515 _106516 x k x'))).
Proof. exact (MK_COMB (@lem4436224 _106515 _106516 x k x') (@lem4436225 _106515 _106516 x k x')). Qed.
Lemma lem4436227 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : ((term349 _106515 _106516 x k x') = (term349 _106515 _106516 x k x')) = (((term330 _106515 _106516 x k x') = (term348 _106515 _106516 x k x')) = ((term330 _106515 _106516 x k x') = (term348 _106515 _106516 x k x'))).
Proof. exact (TRANS (@lem4436221 _106515 _106516 x k x') (@lem4436226 _106515 _106516 x k x')). Qed.
Lemma lem4436228 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : ((term330 _106515 _106516 x k x') = (term348 _106515 _106516 x k x')) = ((term330 _106515 _106516 x k x') = (term348 _106515 _106516 x k x')).
Proof. exact (EQ_MP (@lem4436227 _106515 _106516 x k x') (@lem4436218 _106515 _106516 x k x')). Qed.
Lemma lem4436229 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term330 _106515 _106516 x k x') = (term348 _106515 _106516 x k x').
Proof. exact (EQ_MP (@lem4436228 _106515 _106516 x k x') (@lem4436215 _106515 _106516 x k x')). Qed.
Lemma lem4436230 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term278 _106515 _106516 x k x') = (term348 _106515 _106516 x k x').
Proof. exact (TRANS (@lem4436188 _106515 _106516 x k x') (@lem4436229 _106515 _106516 x k x')). Qed.
Lemma lem4436231 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term237 _106515 _106516 x k x') = (term348 _106515 _106516 x k x').
Proof. exact (TRANS (@lem4436065 _106515 _106516 x k x') (@lem4436230 _106515 _106516 x k x')). Qed.
Lemma lem4436232 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term169 _106515 _106516 x k x') = (term348 _106515 _106516 x k x').
Proof. exact (TRANS (@lem4435620 _106515 _106516 x k x') (@lem4436231 _106515 _106516 x k x')). Qed.
Lemma lem4436233 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (h1 : term169 _106515 _106516 x k x') : term348 _106515 _106516 x k x'.
Proof. exact (EQ_MP (@lem4436232 _106515 _106516 x k x') (@lem4435498 _106515 _106516 x k x' h1)). Qed.
Lemma lem4436234 {_106515 _106516 : Type'} (i : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (h1 : term345 _106515 _106516 i x k x') : term345 _106515 _106516 i x k x'.
Proof. exact (h1). Qed.
Lemma lem4436249 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515) : (term177 _106515 _106516 k x' x) = (term177 _106515 _106516 k x' x).
Proof. exact (eq_refl (term177 _106515 _106516 k x' x)). Qed.
Lemma lem4436250 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term187 _106515 _106516 k x') = (term187 _106515 _106516 k x').
Proof. exact (fun_ext (fun x : _106515 => @lem4436249 _106515 _106516 k x' x)). Qed.
Lemma lem4436251 {_106515 : Type'} : (@all _106515) = (@all _106515).
Proof. exact (eq_refl (@all _106515)). Qed.
Lemma lem4436252 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term188 _106515 _106516 k x') = (term188 _106515 _106516 k x').
Proof. exact (MK_COMB (@lem4436251 _106515) (@lem4436250 _106515 _106516 k x')). Qed.
Lemma lem4436271 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (x'' : _106515) : (term191 _106515 _106516 k x' x x'') = (term191 _106515 _106516 k x' x x'').
Proof. exact (eq_refl (term191 _106515 _106516 k x' x x'')). Qed.
Lemma lem4436272 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term199 _106515 _106516 k x' x) = (term199 _106515 _106516 k x' x).
Proof. exact (fun_ext (fun x'' : _106515 => @lem4436271 _106515 _106516 k x' x x'')). Qed.
Lemma lem4436273 {_106515 : Type'} : (@all _106515) = (@all _106515).
Proof. exact (eq_refl (@all _106515)). Qed.
Lemma lem4436274 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term200 _106515 _106516 k x' x) = (term200 _106515 _106516 k x' x).
Proof. exact (MK_COMB (@lem4436273 _106515) (@lem4436272 _106515 _106516 k x' x)). Qed.
Lemma lem4436275 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4436276 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term273 _106515 _106516 k x' x) = (term273 _106515 _106516 k x' x).
Proof. exact (MK_COMB (@lem4436275) (@lem4436274 _106515 _106516 k x' x)). Qed.
Lemma lem4436277 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term276 _106515 _106516 x k x') = (term276 _106515 _106516 x k x').
Proof. exact (MK_COMB (@lem4436276 _106515 _106516 k x' x) (@lem4436252 _106515 _106516 k x')). Qed.
Lemma lem4436320 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (i : _106515) : (term324 _106515 _106516 k x' x i) = (term324 _106515 _106516 k x' x i).
Proof. exact (eq_refl (term324 _106515 _106516 k x' x i)). Qed.
Lemma lem4436321 {_106515 _106516 : Type'} (i : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term326 _106515 _106516 i x k x') = (term326 _106515 _106516 i x k x').
Proof. exact (MK_COMB (@lem4436320 _106515 _106516 k x' x i) (@lem4436277 _106515 _106516 x k x')). Qed.
Lemma lem4436362 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (i : _106515) : (term217 _106515 _106516 x k x' i) = (term217 _106515 _106516 x k x' i).
Proof. exact (eq_refl (term217 _106515 _106516 x k x' i)). Qed.
Lemma lem4436381 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (i : _106515) : (term191 _106515 _106516 k x' x i) = (term191 _106515 _106516 k x' x i).
Proof. exact (eq_refl (term191 _106515 _106516 k x' x i)). Qed.
Lemma lem4436382 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term199 _106515 _106516 k x' x) = (term199 _106515 _106516 k x' x).
Proof. exact (fun_ext (fun i : _106515 => @lem4436381 _106515 _106516 k x' x i)). Qed.
Lemma lem4436383 {_106515 : Type'} : (@all _106515) = (@all _106515).
Proof. exact (eq_refl (@all _106515)). Qed.
Lemma lem4436384 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term200 _106515 _106516 k x' x) = (term200 _106515 _106516 k x' x).
Proof. exact (MK_COMB (@lem4436383 _106515) (@lem4436382 _106515 _106516 k x' x)). Qed.
Lemma lem4436399 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515) : (term177 _106515 _106516 k x' x) = (term177 _106515 _106516 k x' x).
Proof. exact (eq_refl (term177 _106515 _106516 k x' x)). Qed.
Lemma lem4436400 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term187 _106515 _106516 k x') = (term187 _106515 _106516 k x').
Proof. exact (fun_ext (fun x : _106515 => @lem4436399 _106515 _106516 k x' x)). Qed.
Lemma lem4436401 {_106515 : Type'} : (@all _106515) = (@all _106515).
Proof. exact (eq_refl (@all _106515)). Qed.
Lemma lem4436402 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term188 _106515 _106516 k x') = (term188 _106515 _106516 k x').
Proof. exact (MK_COMB (@lem4436401 _106515) (@lem4436400 _106515 _106516 k x')). Qed.
Lemma lem4436403 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4436404 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term206 _106515 _106516 k x') = (term206 _106515 _106516 k x').
Proof. exact (MK_COMB (@lem4436403) (@lem4436402 _106515 _106516 k x')). Qed.
Lemma lem4436405 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term207 _106515 _106516 k x' x) = (term207 _106515 _106516 k x' x).
Proof. exact (MK_COMB (@lem4436404 _106515 _106516 k x') (@lem4436384 _106515 _106516 k x' x)). Qed.
Lemma lem4436406 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4436407 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term231 _106515 _106516 k x' x) = (term231 _106515 _106516 k x' x).
Proof. exact (MK_COMB (@lem4436406) (@lem4436405 _106515 _106516 k x' x)). Qed.
Lemma lem4436408 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (i : _106515) : (term291 _106515 _106516 x k x' i) = (term291 _106515 _106516 x k x' i).
Proof. exact (MK_COMB (@lem4436407 _106515 _106516 k x' x) (@lem4436362 _106515 _106516 x k x' i)). Qed.
Lemma lem4436409 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4436410 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (i : _106515) : (term343 _106515 _106516 x k x' i) = (term343 _106515 _106516 x k x' i).
Proof. exact (MK_COMB (@lem4436409) (@lem4436408 _106515 _106516 x k x' i)). Qed.
Lemma lem4436411 {_106515 _106516 : Type'} (i : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term345 _106515 _106516 i x k x') = (term345 _106515 _106516 i x k x').
Proof. exact (MK_COMB (@lem4436410 _106515 _106516 x k x' i) (@lem4436321 _106515 _106516 i x k x')). Qed.
Lemma lem4436412 {_106515 _106516 : Type'} (i : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (h1 : term345 _106515 _106516 i x k x') : term345 _106515 _106516 i x k x'.
Proof. exact (EQ_MP (@lem4436411 _106515 _106516 i x k x') (@lem4436234 _106515 _106516 i x k x' h1)). Qed.
Lemma lem4436413 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (i : _106515) (h1 : term291 _106515 _106516 x k x' i) : term291 _106515 _106516 x k x' i.
Proof. exact (h1). Qed.
Lemma lem4436414 {_106515 _106516 : Type'} (i : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (h1 : term326 _106515 _106516 i x k x') : term326 _106515 _106516 i x k x'.
Proof. exact (h1). Qed.
Lemma lem4436415 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (i : _106515) (h1 : term291 _106515 _106516 x k x' i) : term217 _106515 _106516 x k x' i.
Proof. exact (proj2 (@lem4436413 _106515 _106516 x k x' i h1)). Qed.
Lemma lem4436416 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (i : _106515) (h1 : term291 _106515 _106516 x k x' i) : term207 _106515 _106516 k x' x.
Proof. exact (proj1 (@lem4436413 _106515 _106516 x k x' i h1)). Qed.
Lemma lem4436417 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (i : _106515) (h1 : term291 _106515 _106516 x k x' i) : term200 _106515 _106516 k x' x.
Proof. exact (proj2 (@lem4436416 _106515 _106516 x k x' i h1)). Qed.
Lemma lem4436418 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (i : _106515) (h1 : term291 _106515 _106516 x k x' i) : term188 _106515 _106516 k x'.
Proof. exact (proj1 (@lem4436416 _106515 _106516 x k x' i h1)). Qed.
Lemma lem4436419 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (i : _106515) (h1 : term190 _106515 _106516 k x' x i) : term190 _106515 _106516 k x' x i.
Proof. exact (h1). Qed.
Lemma lem4436420 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (i : _106515) (h1 : term172 _106515 _106516 k x' i) : term172 _106515 _106516 k x' i.
Proof. exact (h1). Qed.
Lemma lem4436425 {_106515 _106516 : Type'} (i : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (h1 : term326 _106515 _106516 i x k x') : term276 _106515 _106516 x k x'.
Proof. exact (proj2 (@lem4436414 _106515 _106516 i x k x' h1)). Qed.
Lemma lem4436426 {_106515 _106516 : Type'} (i : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (h1 : term326 _106515 _106516 i x k x') : term304 _106515 _106516 k x' x i.
Proof. exact (proj1 (@lem4436414 _106515 _106516 i x k x' h1)). Qed.
Lemma lem4436427 {_106515 _106516 : Type'} (i : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (h1 : term326 _106515 _106516 i x k x') : term188 _106515 _106516 k x'.
Proof. exact (proj2 (@lem4436425 _106515 _106516 i x k x' h1)). Qed.
Lemma lem4436428 {_106515 _106516 : Type'} (i : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (h1 : term326 _106515 _106516 i x k x') : term200 _106515 _106516 k x' x.
Proof. exact (proj1 (@lem4436425 _106515 _106516 i x k x' h1)). Qed.
Lemma lem4436429 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (i : _106515) (h1 : term172 _106515 _106516 k x' i) : term172 _106515 _106516 k x' i.
Proof. exact (h1). Qed.
Lemma lem4436430 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (i : _106515) (h1 : term190 _106515 _106516 k x' x i) : term190 _106515 _106516 k x' x i.
Proof. exact (h1). Qed.
Lemma lem4436455 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (i : _106515) : (term191 _106515 _106516 k x' x i) = (term191 _106515 _106516 k x' x i).
Proof. exact (eq_refl (term191 _106515 _106516 k x' x i)). Qed.
Lemma lem4436456 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term199 _106515 _106516 k x' x) = (term199 _106515 _106516 k x' x).
Proof. exact (fun_ext (fun i : _106515 => @lem4436455 _106515 _106516 k x' x i)). Qed.
Lemma lem4436457 {_106515 : Type'} : (@all _106515) = (@all _106515).
Proof. exact (eq_refl (@all _106515)). Qed.
Lemma lem4436459 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term200 _106515 _106516 k x' x) = (term200 _106515 _106516 k x' x).
Proof. exact (MK_COMB (@lem4436457 _106515) (@lem4436456 _106515 _106516 k x' x)). Qed.
Lemma lem4436460 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (i : _106515) (h1 : term291 _106515 _106516 x k x' i) : term200 _106515 _106516 k x' x.
Proof. exact (EQ_MP (@lem4436459 _106515 _106516 k x' x) (@lem4436417 _106515 _106516 x k x' i h1)). Qed.
Lemma lem4436476 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515) : (term177 _106515 _106516 k x' x) = (term177 _106515 _106516 k x' x).
Proof. exact (eq_refl (term177 _106515 _106516 k x' x)). Qed.
Lemma lem4436477 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term187 _106515 _106516 k x') = (term187 _106515 _106516 k x').
Proof. exact (fun_ext (fun x : _106515 => @lem4436476 _106515 _106516 k x' x)). Qed.
Lemma lem4436478 {_106515 : Type'} : (@all _106515) = (@all _106515).
Proof. exact (eq_refl (@all _106515)). Qed.
Lemma lem4436480 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term188 _106515 _106516 k x') = (term188 _106515 _106516 k x').
Proof. exact (MK_COMB (@lem4436478 _106515) (@lem4436477 _106515 _106516 k x')). Qed.
Lemma lem4436481 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (i : _106515) (h1 : term291 _106515 _106516 x k x' i) : term188 _106515 _106516 k x'.
Proof. exact (EQ_MP (@lem4436480 _106515 _106516 k x') (@lem4436418 _106515 _106516 x k x' i h1)). Qed.
Lemma lem4436523 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515) : (term177 _106515 _106516 k x' x) = (term177 _106515 _106516 k x' x).
Proof. exact (eq_refl (term177 _106515 _106516 k x' x)). Qed.
Lemma lem4436524 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term187 _106515 _106516 k x') = (term187 _106515 _106516 k x').
Proof. exact (fun_ext (fun x : _106515 => @lem4436523 _106515 _106516 k x' x)). Qed.
Lemma lem4436525 {_106515 : Type'} : (@all _106515) = (@all _106515).
Proof. exact (eq_refl (@all _106515)). Qed.
Lemma lem4436527 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term188 _106515 _106516 k x') = (term188 _106515 _106516 k x').
Proof. exact (MK_COMB (@lem4436525 _106515) (@lem4436524 _106515 _106516 k x')). Qed.
Lemma lem4436528 {_106515 _106516 : Type'} (i : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (h1 : term326 _106515 _106516 i x k x') : term188 _106515 _106516 k x'.
Proof. exact (EQ_MP (@lem4436527 _106515 _106516 k x') (@lem4436427 _106515 _106516 i x k x' h1)). Qed.
Lemma lem4436544 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (x'' : _106515) : (term191 _106515 _106516 k x' x x'') = (term191 _106515 _106516 k x' x x'').
Proof. exact (eq_refl (term191 _106515 _106516 k x' x x'')). Qed.
Lemma lem4436545 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term199 _106515 _106516 k x' x) = (term199 _106515 _106516 k x' x).
Proof. exact (fun_ext (fun x'' : _106515 => @lem4436544 _106515 _106516 k x' x x'')). Qed.
Lemma lem4436546 {_106515 : Type'} : (@all _106515) = (@all _106515).
Proof. exact (eq_refl (@all _106515)). Qed.
Lemma lem4436548 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) : (term200 _106515 _106516 k x' x) = (term200 _106515 _106516 k x' x).
Proof. exact (MK_COMB (@lem4436546 _106515) (@lem4436545 _106515 _106516 k x' x)). Qed.
Lemma lem4436549 {_106515 _106516 : Type'} (i : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (h1 : term326 _106515 _106516 i x k x') : term200 _106515 _106516 k x' x.
Proof. exact (EQ_MP (@lem4436548 _106515 _106516 k x' x) (@lem4436428 _106515 _106516 i x k x' h1)). Qed.
Lemma lem4436574 {_106515 _106516 : Type'} (_51031 : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (i : _106515) (h1 : term291 _106515 _106516 x k x' i) : term262 _106515 _106516 k x' x _51031.
Proof. exact (@lem4436460 _106515 _106516 x k x' i h1 _51031). Qed.
Lemma lem4436575 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (_51031 : _106515) : (term262 _106515 _106516 k x' x _51031) = (term191 _106515 _106516 k x' x _51031).
Proof. exact (eq_refl (term262 _106515 _106516 k x' x _51031)). Qed.
Lemma lem4436577 {_106515 _106516 : Type'} (_51032 : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (i : _106515) (h1 : term291 _106515 _106516 x k x' i) : term265 _106515 _106516 k x' _51032.
Proof. exact (@lem4436481 _106515 _106516 x k x' i h1 _51032). Qed.
Lemma lem4436578 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (_51032 : _106515) : (term265 _106515 _106516 k x' _51032) = (term177 _106515 _106516 k x' _51032).
Proof. exact (eq_refl (term265 _106515 _106516 k x' _51032)). Qed.
Lemma lem4436586 {_106515 _106516 : Type'} (_51035 : _106515) (i : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (h1 : term326 _106515 _106516 i x k x') : term265 _106515 _106516 k x' _51035.
Proof. exact (@lem4436528 _106515 _106516 i x k x' h1 _51035). Qed.
Lemma lem4436587 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (_51035 : _106515) : (term265 _106515 _106516 k x' _51035) = (term177 _106515 _106516 k x' _51035).
Proof. exact (eq_refl (term265 _106515 _106516 k x' _51035)). Qed.
Lemma lem4436589 {_106515 _106516 : Type'} (_51036 : _106515) (i : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (h1 : term326 _106515 _106516 i x k x') : term262 _106515 _106516 k x' x _51036.
Proof. exact (@lem4436549 _106515 _106516 i x k x' h1 _51036). Qed.
Lemma lem4436590 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (_51036 : _106515) : (term262 _106515 _106516 k x' x _51036) = (term191 _106515 _106516 k x' x _51036).
Proof. exact (eq_refl (term262 _106515 _106516 k x' x _51036)). Qed.
Lemma lem4436606 {_106515 _106516 : Type'} (_51031 : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (i : _106515) (h1 : term291 _106515 _106516 x k x' i) : term191 _106515 _106516 k x' x _51031.
Proof. exact (EQ_MP (@lem4436575 _106515 _106516 k x' x _51031) (@lem4436574 _106515 _106516 _51031 x k x' i h1)). Qed.
Lemma lem4436610 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (i : _106515) (h1 : term190 _106515 _106516 k x' x i) : term208 _106515 _106516 x' x i.
Proof. exact (proj2 (@lem4436419 _106515 _106516 k x' x i h1)). Qed.
Lemma lem4436616 {_106515 _106516 : Type'} (_51032 : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (i : _106515) (h1 : term291 _106515 _106516 x k x' i) : term177 _106515 _106516 k x' _51032.
Proof. exact (EQ_MP (@lem4436578 _106515 _106516 k x' _51032) (@lem4436577 _106515 _106516 _51032 x k x' i h1)). Qed.
Lemma lem4436626 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (i : _106515) (h1 : term172 _106515 _106516 k x' i) : term352 _106515 _106516 x' i.
Proof. exact (proj2 (@lem4436420 _106515 _106516 k x' i h1)). Qed.
Lemma lem4436638 {_106515 _106516 : Type'} (_51035 : _106515) (i : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (h1 : term326 _106515 _106516 i x k x') : term177 _106515 _106516 k x' _51035.
Proof. exact (EQ_MP (@lem4436587 _106515 _106516 k x' _51035) (@lem4436586 _106515 _106516 _51035 i x k x' h1)). Qed.
Lemma lem4436642 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (i : _106515) (h1 : term172 _106515 _106516 k x' i) : term352 _106515 _106516 x' i.
Proof. exact (proj2 (@lem4436429 _106515 _106516 k x' i h1)). Qed.
Lemma lem4436648 {_106515 _106516 : Type'} (_51036 : _106515) (i : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (h1 : term326 _106515 _106516 i x k x') : term191 _106515 _106516 k x' x _51036.
Proof. exact (EQ_MP (@lem4436590 _106515 _106516 k x' x _51036) (@lem4436589 _106515 _106516 _51036 i x k x' h1)). Qed.
Lemma lem4436658 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (i : _106515) (h1 : term190 _106515 _106516 k x' x i) : term208 _106515 _106516 x' x i.
Proof. exact (proj2 (@lem4436430 _106515 _106516 k x' x i h1)). Qed.
Lemma lem4436701 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (i : _106515) (h1 : term190 _106515 _106516 k x' x i) : @IN _106515 i k.
Proof. exact (proj1 (@lem4436419 _106515 _106516 k x' x i h1)). Qed.
Lemma lem4436702 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (i : _106515) (h1 : term190 _106515 _106516 k x' x i) : term353 _106515 i k.
Proof. exact (fun h0 : term173 _106515 i k => @lem4436701 _106515 _106516 k x' x i h1). Qed.
Lemma lem4436704 (p : Prop) : (term354 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4436705 {_106515 : Type'} (i : _106515) (k : _106515 -> Prop) : (term353 _106515 i k) = (@IN _106515 i k).
Proof. exact (@lem4436704 (@IN _106515 i k)). Qed.
Lemma lem4436706 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (i : _106515) (h1 : term190 _106515 _106516 k x' x i) : @IN _106515 i k.
Proof. exact (EQ_MP (@lem4436705 _106515 i k) (@lem4436702 _106515 _106516 k x' x i h1)). Qed.
Lemma lem4436712 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4436713 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (x : _106515 -> _106516) (_51031 : _106515) (k : _106515 -> Prop) : (term191 _106515 _106516 k x' x _51031) = (term355 _106515 _106516 x' x _51031 k).
Proof. exact (@lem4436712 ((x' _51031) = (x _51031)) (term173 _106515 _51031 k)). Qed.
Lemma lem4436721 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4436722 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (x : _106515 -> _106516) (_51031 : _106515) (k : _106515 -> Prop) : (term356 _106515 _106516 k x' x _51031) = (term357 _106515 _106516 x' x _51031 k).
Proof. exact (MK_COMB (@lem4436721) (@lem4436713 _106515 _106516 x' x _51031 k)). Qed.
Lemma lem4436730 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (x : _106515 -> _106516) (_51031 : _106515) (k : _106515 -> Prop) : (term355 _106515 _106516 x' x _51031 k) = (term355 _106515 _106516 x' x _51031 k).
Proof. exact (eq_refl (term355 _106515 _106516 x' x _51031 k)). Qed.
Lemma lem4436731 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (x : _106515 -> _106516) (_51031 : _106515) (k : _106515 -> Prop) : ((term191 _106515 _106516 k x' x _51031) = (term355 _106515 _106516 x' x _51031 k)) = ((term355 _106515 _106516 x' x _51031 k) = (term355 _106515 _106516 x' x _51031 k)).
Proof. exact (MK_COMB (@lem4436722 _106515 _106516 x' x _51031 k) (@lem4436730 _106515 _106516 x' x _51031 k)). Qed.
Lemma lem4436733 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4436734 (x : Prop) : (x = x) = True.
Proof. exact (@lem4436733 Prop x). Qed.
Lemma lem4436735 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (x : _106515 -> _106516) (_51031 : _106515) (k : _106515 -> Prop) : ((term355 _106515 _106516 x' x _51031 k) = (term355 _106515 _106516 x' x _51031 k)) = True.
Proof. exact (@lem4436734 (term355 _106515 _106516 x' x _51031 k)). Qed.
Lemma lem4436736 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (x : _106515 -> _106516) (_51031 : _106515) (k : _106515 -> Prop) : ((term191 _106515 _106516 k x' x _51031) = (term355 _106515 _106516 x' x _51031 k)) = True.
Proof. exact (TRANS (@lem4436731 _106515 _106516 x' x _51031 k) (@lem4436735 _106515 _106516 x' x _51031 k)). Qed.
Lemma lem4436737 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (x : _106515 -> _106516) (_51031 : _106515) (k : _106515 -> Prop) : True = ((term191 _106515 _106516 k x' x _51031) = (term355 _106515 _106516 x' x _51031 k)).
Proof. exact (SYM (@lem4436736 _106515 _106516 x' x _51031 k)). Qed.
Lemma lem4436738 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (x : _106515 -> _106516) (_51031 : _106515) (k : _106515 -> Prop) : (term191 _106515 _106516 k x' x _51031) = (term355 _106515 _106516 x' x _51031 k).
Proof. exact (EQ_MP (@lem4436737 _106515 _106516 x' x _51031 k) (@lem0)). Qed.
Lemma lem4436739 {_106515 _106516 : Type'} (_51031 : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (i : _106515) (h1 : term291 _106515 _106516 x k x' i) : term355 _106515 _106516 x' x _51031 k.
Proof. exact (EQ_MP (@lem4436738 _106515 _106516 x' x _51031 k) (@lem4436606 _106515 _106516 _51031 x k x' i h1)). Qed.
Lemma lem4436741 (b : Prop) (a : Prop) : (a \/ b) = (term358 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4436742 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (_51031 : _106515) : (term355 _106515 _106516 x' x _51031 k) = (term359 _106515 _106516 k x' x _51031).
Proof. exact (@lem4436741 (term173 _106515 _51031 k) ((x' _51031) = (x _51031))). Qed.
Lemma lem4436744 (a : Prop) : (term145 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4436745 {_106515 : Type'} (_51031 : _106515) (k : _106515 -> Prop) : (term170 _106515 _51031 k) = (@IN _106515 _51031 k).
Proof. exact (@lem4436744 (@IN _106515 _51031 k)). Qed.
Lemma lem4436746 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4436747 {_106515 : Type'} (_51031 : _106515) (k : _106515 -> Prop) : (term360 _106515 _51031 k) = (term49 _106515 _51031 k).
Proof. exact (MK_COMB (@lem4436746) (@lem4436745 _106515 _51031 k)). Qed.
Lemma lem4436748 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (x : _106515 -> _106516) (_51031 : _106515) : ((x' _51031) = (x _51031)) = ((x' _51031) = (x _51031)).
Proof. exact (eq_refl ((x' _51031) = (x _51031))). Qed.
Lemma lem4436749 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (_51031 : _106515) : (term359 _106515 _106516 k x' x _51031) = (term51 _106515 _106516 k x' x _51031).
Proof. exact (MK_COMB (@lem4436747 _106515 _51031 k) (@lem4436748 _106515 _106516 x' x _51031)). Qed.
Lemma lem4436750 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (_51031 : _106515) : (term355 _106515 _106516 x' x _51031 k) = (term51 _106515 _106516 k x' x _51031).
Proof. exact (TRANS (@lem4436742 _106515 _106516 k x' x _51031) (@lem4436749 _106515 _106516 k x' x _51031)). Qed.
Lemma lem4436753 {_106515 _106516 : Type'} (_51031 : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (i : _106515) (h1 : term291 _106515 _106516 x k x' i) : term51 _106515 _106516 k x' x _51031.
Proof. exact (EQ_MP (@lem4436750 _106515 _106516 k x' x _51031) (@lem4436739 _106515 _106516 _51031 x k x' i h1)). Qed.
Lemma lem4436754 {_106515 _106516 : Type'} (_51031 : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (i : _106515) (h1 : term291 _106515 _106516 x k x' i) : term51 _106515 _106516 k x' x _51031.
Proof. exact (@lem4436753 _106515 _106516 _51031 x k x' i h1). Qed.
Lemma lem4436755 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (i : _106515) (h1 : term291 _106515 _106516 x k x' i) : term51 _106515 _106516 k x' x i.
Proof. exact (@lem4436754 _106515 _106516 i x k x' i h1). Qed.
Lemma lem4436758 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (i : _106515) (h1 : term291 _106515 _106516 x k x' i) (h2 : term190 _106515 _106516 k x' x i) : (x' i) = (x i).
Proof. exact (@lem4436755 _106515 _106516 x k x' i h1 (@lem4436706 _106515 _106516 k x' x i h2)). Qed.
Lemma lem4436759 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (i : _106515) (h1 : term291 _106515 _106516 x k x' i) (h2 : term190 _106515 _106516 k x' x i) : term361 _106515 _106516 x' x i.
Proof. exact (fun h0 : term208 _106515 _106516 x' x i => @lem4436758 _106515 _106516 k x' x i h1 h2). Qed.
Lemma lem4436761 (p : Prop) : (term354 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4436762 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (x : _106515 -> _106516) (i : _106515) : (term361 _106515 _106516 x' x i) = ((x' i) = (x i)).
Proof. exact (@lem4436761 ((x' i) = (x i))). Qed.
Lemma lem4436763 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (i : _106515) (h1 : term291 _106515 _106516 x k x' i) (h2 : term190 _106515 _106516 k x' x i) : (x' i) = (x i).
Proof. exact (EQ_MP (@lem4436762 _106515 _106516 x' x i) (@lem4436759 _106515 _106516 k x' x i h1 h2)). Qed.
Lemma lem4436766 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4436768 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (x : _106515 -> _106516) (i : _106515) : (term208 _106515 _106516 x' x i) = (term362 _106515 _106516 x' x i).
Proof. exact (@lem4436766 ((x' i) = (x i))). Qed.
Lemma lem4436771 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (i : _106515) (h1 : term190 _106515 _106516 k x' x i) : term362 _106515 _106516 x' x i.
Proof. exact (EQ_MP (@lem4436768 _106515 _106516 x' x i) (@lem4436610 _106515 _106516 k x' x i h1)). Qed.
Lemma lem4436774 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (i : _106515) (h1 : term291 _106515 _106516 x k x' i) (h2 : term190 _106515 _106516 k x' x i) : False.
Proof. exact (@lem4436771 _106515 _106516 k x' x i h2 (@lem4436763 _106515 _106516 k x' x i h1 h2)). Qed.
Lemma lem4436775 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (i : _106515) (h1 : term291 _106515 _106516 x k x' i) (h2 : term190 _106515 _106516 k x' x i) : term363.
Proof. exact (fun h0 : ~ False => @lem4436774 _106515 _106516 k x' x i h1 h2). Qed.
Lemma lem4436777 (p : Prop) : (term354 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4436778 : term363 = False.
Proof. exact (@lem4436777 False). Qed.
Lemma lem4436779 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (i : _106515) (h1 : term291 _106515 _106516 x k x' i) (h2 : term190 _106515 _106516 k x' x i) : False.
Proof. exact (EQ_MP (@lem4436778) (@lem4436775 _106515 _106516 k x' x i h1 h2)). Qed.
Lemma lem4436822 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (i : _106515) (h1 : term172 _106515 _106516 k x' i) : term173 _106515 i k.
Proof. exact (proj1 (@lem4436420 _106515 _106516 k x' i h1)). Qed.
Lemma lem4436823 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (i : _106515) (h1 : term172 _106515 _106516 k x' i) : term364 _106515 i k.
Proof. exact (fun h0 : @IN _106515 i k => @lem4436822 _106515 _106516 k x' i h1). Qed.
Lemma lem4436825 (p : Prop) : (term365 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4436826 {_106515 : Type'} (i : _106515) (k : _106515 -> Prop) : (term364 _106515 i k) = (term173 _106515 i k).
Proof. exact (@lem4436825 (@IN _106515 i k)). Qed.
Lemma lem4436827 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (i : _106515) (h1 : term172 _106515 _106516 k x' i) : term173 _106515 i k.
Proof. exact (EQ_MP (@lem4436826 _106515 i k) (@lem4436823 _106515 _106516 k x' i h1)). Qed.
Lemma lem4436833 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4436834 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (_51032 : _106515) (k : _106515 -> Prop) : (term177 _106515 _106516 k x' _51032) = (term366 _106515 _106516 x' _51032 k).
Proof. exact (@lem4436833 ((x' _51032) = (@ARB _106516)) (@IN _106515 _51032 k)). Qed.
Lemma lem4436842 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4436843 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (_51032 : _106515) (k : _106515 -> Prop) : (term367 _106515 _106516 k x' _51032) = (term368 _106515 _106516 x' _51032 k).
Proof. exact (MK_COMB (@lem4436842) (@lem4436834 _106515 _106516 x' _51032 k)). Qed.
Lemma lem4436851 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (_51032 : _106515) (k : _106515 -> Prop) : (term366 _106515 _106516 x' _51032 k) = (term366 _106515 _106516 x' _51032 k).
Proof. exact (eq_refl (term366 _106515 _106516 x' _51032 k)). Qed.
Lemma lem4436852 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (_51032 : _106515) (k : _106515 -> Prop) : ((term177 _106515 _106516 k x' _51032) = (term366 _106515 _106516 x' _51032 k)) = ((term366 _106515 _106516 x' _51032 k) = (term366 _106515 _106516 x' _51032 k)).
Proof. exact (MK_COMB (@lem4436843 _106515 _106516 x' _51032 k) (@lem4436851 _106515 _106516 x' _51032 k)). Qed.
Lemma lem4436854 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4436855 (x : Prop) : (x = x) = True.
Proof. exact (@lem4436854 Prop x). Qed.
Lemma lem4436856 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (_51032 : _106515) (k : _106515 -> Prop) : ((term366 _106515 _106516 x' _51032 k) = (term366 _106515 _106516 x' _51032 k)) = True.
Proof. exact (@lem4436855 (term366 _106515 _106516 x' _51032 k)). Qed.
Lemma lem4436857 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (_51032 : _106515) (k : _106515 -> Prop) : ((term177 _106515 _106516 k x' _51032) = (term366 _106515 _106516 x' _51032 k)) = True.
Proof. exact (TRANS (@lem4436852 _106515 _106516 x' _51032 k) (@lem4436856 _106515 _106516 x' _51032 k)). Qed.
Lemma lem4436858 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (_51032 : _106515) (k : _106515 -> Prop) : True = ((term177 _106515 _106516 k x' _51032) = (term366 _106515 _106516 x' _51032 k)).
Proof. exact (SYM (@lem4436857 _106515 _106516 x' _51032 k)). Qed.
Lemma lem4436859 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (_51032 : _106515) (k : _106515 -> Prop) : (term177 _106515 _106516 k x' _51032) = (term366 _106515 _106516 x' _51032 k).
Proof. exact (EQ_MP (@lem4436858 _106515 _106516 x' _51032 k) (@lem0)). Qed.
Lemma lem4436860 {_106515 _106516 : Type'} (_51032 : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (i : _106515) (h1 : term291 _106515 _106516 x k x' i) : term366 _106515 _106516 x' _51032 k.
Proof. exact (EQ_MP (@lem4436859 _106515 _106516 x' _51032 k) (@lem4436616 _106515 _106516 _51032 x k x' i h1)). Qed.
Lemma lem4436862 (b : Prop) (a : Prop) : (a \/ b) = (term358 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4436865 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (_51032 : _106515) : (term366 _106515 _106516 x' _51032 k) = (term160 _106515 _106516 k x' _51032).
Proof. exact (@lem4436862 (@IN _106515 _51032 k) ((x' _51032) = (@ARB _106516))). Qed.
Lemma lem4436868 {_106515 _106516 : Type'} (_51032 : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (i : _106515) (h1 : term291 _106515 _106516 x k x' i) : term160 _106515 _106516 k x' _51032.
Proof. exact (EQ_MP (@lem4436865 _106515 _106516 k x' _51032) (@lem4436860 _106515 _106516 _51032 x k x' i h1)). Qed.
Lemma lem4436869 {_106515 _106516 : Type'} (_51032 : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (i : _106515) (h1 : term291 _106515 _106516 x k x' i) : term160 _106515 _106516 k x' _51032.
Proof. exact (@lem4436868 _106515 _106516 _51032 x k x' i h1). Qed.
Lemma lem4436870 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (i : _106515) (h1 : term291 _106515 _106516 x k x' i) : term160 _106515 _106516 k x' i.
Proof. exact (@lem4436869 _106515 _106516 i x k x' i h1). Qed.
Lemma lem4436873 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (i : _106515) (h1 : term172 _106515 _106516 k x' i) (h2 : term291 _106515 _106516 x k x' i) : (x' i) = (@ARB _106516).
Proof. exact (@lem4436870 _106515 _106516 x k x' i h2 (@lem4436827 _106515 _106516 k x' i h1)). Qed.
Lemma lem4436874 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (i : _106515) (h1 : term172 _106515 _106516 k x' i) (h2 : term291 _106515 _106516 x k x' i) : term369 _106515 _106516 x' i.
Proof. exact (fun h0 : term352 _106515 _106516 x' i => @lem4436873 _106515 _106516 x k x' i h1 h2). Qed.
Lemma lem4436876 (p : Prop) : (term354 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4436877 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (i : _106515) : (term369 _106515 _106516 x' i) = ((x' i) = (@ARB _106516)).
Proof. exact (@lem4436876 ((x' i) = (@ARB _106516))). Qed.
Lemma lem4436878 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (i : _106515) (h1 : term172 _106515 _106516 k x' i) (h2 : term291 _106515 _106516 x k x' i) : (x' i) = (@ARB _106516).
Proof. exact (EQ_MP (@lem4436877 _106515 _106516 x' i) (@lem4436874 _106515 _106516 x k x' i h1 h2)). Qed.
Lemma lem4436881 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4436883 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (i : _106515) : (term352 _106515 _106516 x' i) = (term370 _106515 _106516 x' i).
Proof. exact (@lem4436881 ((x' i) = (@ARB _106516))). Qed.
Lemma lem4436886 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (i : _106515) (h1 : term172 _106515 _106516 k x' i) : term370 _106515 _106516 x' i.
Proof. exact (EQ_MP (@lem4436883 _106515 _106516 x' i) (@lem4436626 _106515 _106516 k x' i h1)). Qed.
Lemma lem4436889 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (i : _106515) (h1 : term172 _106515 _106516 k x' i) (h2 : term291 _106515 _106516 x k x' i) : False.
Proof. exact (@lem4436886 _106515 _106516 k x' i h1 (@lem4436878 _106515 _106516 x k x' i h1 h2)). Qed.
Lemma lem4436890 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (i : _106515) (h1 : term172 _106515 _106516 k x' i) (h2 : term291 _106515 _106516 x k x' i) : term363.
Proof. exact (fun h0 : ~ False => @lem4436889 _106515 _106516 x k x' i h1 h2). Qed.
Lemma lem4436892 (p : Prop) : (term354 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4436893 : term363 = False.
Proof. exact (@lem4436892 False). Qed.
Lemma lem4436894 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (i : _106515) (h1 : term172 _106515 _106516 k x' i) (h2 : term291 _106515 _106516 x k x' i) : False.
Proof. exact (EQ_MP (@lem4436893) (@lem4436890 _106515 _106516 x k x' i h1 h2)). Qed.
Lemma lem4436937 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (i : _106515) (h1 : term172 _106515 _106516 k x' i) : term173 _106515 i k.
Proof. exact (proj1 (@lem4436429 _106515 _106516 k x' i h1)). Qed.
Lemma lem4436938 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (i : _106515) (h1 : term172 _106515 _106516 k x' i) : term364 _106515 i k.
Proof. exact (fun h0 : @IN _106515 i k => @lem4436937 _106515 _106516 k x' i h1). Qed.
Lemma lem4436940 (p : Prop) : (term365 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4436941 {_106515 : Type'} (i : _106515) (k : _106515 -> Prop) : (term364 _106515 i k) = (term173 _106515 i k).
Proof. exact (@lem4436940 (@IN _106515 i k)). Qed.
Lemma lem4436942 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (i : _106515) (h1 : term172 _106515 _106516 k x' i) : term173 _106515 i k.
Proof. exact (EQ_MP (@lem4436941 _106515 i k) (@lem4436938 _106515 _106516 k x' i h1)). Qed.
Lemma lem4436948 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4436949 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (_51035 : _106515) (k : _106515 -> Prop) : (term177 _106515 _106516 k x' _51035) = (term366 _106515 _106516 x' _51035 k).
Proof. exact (@lem4436948 ((x' _51035) = (@ARB _106516)) (@IN _106515 _51035 k)). Qed.
Lemma lem4436957 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4436958 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (_51035 : _106515) (k : _106515 -> Prop) : (term367 _106515 _106516 k x' _51035) = (term368 _106515 _106516 x' _51035 k).
Proof. exact (MK_COMB (@lem4436957) (@lem4436949 _106515 _106516 x' _51035 k)). Qed.
Lemma lem4436966 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (_51035 : _106515) (k : _106515 -> Prop) : (term366 _106515 _106516 x' _51035 k) = (term366 _106515 _106516 x' _51035 k).
Proof. exact (eq_refl (term366 _106515 _106516 x' _51035 k)). Qed.
Lemma lem4436967 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (_51035 : _106515) (k : _106515 -> Prop) : ((term177 _106515 _106516 k x' _51035) = (term366 _106515 _106516 x' _51035 k)) = ((term366 _106515 _106516 x' _51035 k) = (term366 _106515 _106516 x' _51035 k)).
Proof. exact (MK_COMB (@lem4436958 _106515 _106516 x' _51035 k) (@lem4436966 _106515 _106516 x' _51035 k)). Qed.
Lemma lem4436969 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4436970 (x : Prop) : (x = x) = True.
Proof. exact (@lem4436969 Prop x). Qed.
Lemma lem4436971 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (_51035 : _106515) (k : _106515 -> Prop) : ((term366 _106515 _106516 x' _51035 k) = (term366 _106515 _106516 x' _51035 k)) = True.
Proof. exact (@lem4436970 (term366 _106515 _106516 x' _51035 k)). Qed.
Lemma lem4436972 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (_51035 : _106515) (k : _106515 -> Prop) : ((term177 _106515 _106516 k x' _51035) = (term366 _106515 _106516 x' _51035 k)) = True.
Proof. exact (TRANS (@lem4436967 _106515 _106516 x' _51035 k) (@lem4436971 _106515 _106516 x' _51035 k)). Qed.
Lemma lem4436973 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (_51035 : _106515) (k : _106515 -> Prop) : True = ((term177 _106515 _106516 k x' _51035) = (term366 _106515 _106516 x' _51035 k)).
Proof. exact (SYM (@lem4436972 _106515 _106516 x' _51035 k)). Qed.
Lemma lem4436974 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (_51035 : _106515) (k : _106515 -> Prop) : (term177 _106515 _106516 k x' _51035) = (term366 _106515 _106516 x' _51035 k).
Proof. exact (EQ_MP (@lem4436973 _106515 _106516 x' _51035 k) (@lem0)). Qed.
Lemma lem4436975 {_106515 _106516 : Type'} (_51035 : _106515) (i : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (h1 : term326 _106515 _106516 i x k x') : term366 _106515 _106516 x' _51035 k.
Proof. exact (EQ_MP (@lem4436974 _106515 _106516 x' _51035 k) (@lem4436638 _106515 _106516 _51035 i x k x' h1)). Qed.
Lemma lem4436977 (b : Prop) (a : Prop) : (a \/ b) = (term358 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4436980 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (_51035 : _106515) : (term366 _106515 _106516 x' _51035 k) = (term160 _106515 _106516 k x' _51035).
Proof. exact (@lem4436977 (@IN _106515 _51035 k) ((x' _51035) = (@ARB _106516))). Qed.
Lemma lem4436983 {_106515 _106516 : Type'} (_51035 : _106515) (i : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (h1 : term326 _106515 _106516 i x k x') : term160 _106515 _106516 k x' _51035.
Proof. exact (EQ_MP (@lem4436980 _106515 _106516 k x' _51035) (@lem4436975 _106515 _106516 _51035 i x k x' h1)). Qed.
Lemma lem4436984 {_106515 _106516 : Type'} (_51035 : _106515) (i : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (h1 : term326 _106515 _106516 i x k x') : term160 _106515 _106516 k x' _51035.
Proof. exact (@lem4436983 _106515 _106516 _51035 i x k x' h1). Qed.
Lemma lem4436985 {_106515 _106516 : Type'} (i : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (h1 : term326 _106515 _106516 i x k x') : term160 _106515 _106516 k x' i.
Proof. exact (@lem4436984 _106515 _106516 i i x k x' h1). Qed.
Lemma lem4436988 {_106515 _106516 : Type'} (i : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (h1 : term172 _106515 _106516 k x' i) (h2 : term326 _106515 _106516 i x k x') : (x' i) = (@ARB _106516).
Proof. exact (@lem4436985 _106515 _106516 i x k x' h2 (@lem4436942 _106515 _106516 k x' i h1)). Qed.
Lemma lem4436989 {_106515 _106516 : Type'} (i : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (h1 : term172 _106515 _106516 k x' i) (h2 : term326 _106515 _106516 i x k x') : term369 _106515 _106516 x' i.
Proof. exact (fun h0 : term352 _106515 _106516 x' i => @lem4436988 _106515 _106516 i x k x' h1 h2). Qed.
Lemma lem4436991 (p : Prop) : (term354 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4436992 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (i : _106515) : (term369 _106515 _106516 x' i) = ((x' i) = (@ARB _106516)).
Proof. exact (@lem4436991 ((x' i) = (@ARB _106516))). Qed.
Lemma lem4436993 {_106515 _106516 : Type'} (i : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (h1 : term172 _106515 _106516 k x' i) (h2 : term326 _106515 _106516 i x k x') : (x' i) = (@ARB _106516).
Proof. exact (EQ_MP (@lem4436992 _106515 _106516 x' i) (@lem4436989 _106515 _106516 i x k x' h1 h2)). Qed.
Lemma lem4436996 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4436998 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (i : _106515) : (term352 _106515 _106516 x' i) = (term370 _106515 _106516 x' i).
Proof. exact (@lem4436996 ((x' i) = (@ARB _106516))). Qed.
Lemma lem4437001 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (i : _106515) (h1 : term172 _106515 _106516 k x' i) : term370 _106515 _106516 x' i.
Proof. exact (EQ_MP (@lem4436998 _106515 _106516 x' i) (@lem4436642 _106515 _106516 k x' i h1)). Qed.
Lemma lem4437004 {_106515 _106516 : Type'} (i : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (h1 : term172 _106515 _106516 k x' i) (h2 : term326 _106515 _106516 i x k x') : False.
Proof. exact (@lem4437001 _106515 _106516 k x' i h1 (@lem4436993 _106515 _106516 i x k x' h1 h2)). Qed.
Lemma lem4437005 {_106515 _106516 : Type'} (i : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (h1 : term172 _106515 _106516 k x' i) (h2 : term326 _106515 _106516 i x k x') : term363.
Proof. exact (fun h0 : ~ False => @lem4437004 _106515 _106516 i x k x' h1 h2). Qed.
Lemma lem4437007 (p : Prop) : (term354 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4437008 : term363 = False.
Proof. exact (@lem4437007 False). Qed.
Lemma lem4437009 {_106515 _106516 : Type'} (i : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (h1 : term172 _106515 _106516 k x' i) (h2 : term326 _106515 _106516 i x k x') : False.
Proof. exact (EQ_MP (@lem4437008) (@lem4437005 _106515 _106516 i x k x' h1 h2)). Qed.
Lemma lem4437052 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (i : _106515) (h1 : term190 _106515 _106516 k x' x i) : @IN _106515 i k.
Proof. exact (proj1 (@lem4436430 _106515 _106516 k x' x i h1)). Qed.
Lemma lem4437053 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (i : _106515) (h1 : term190 _106515 _106516 k x' x i) : term353 _106515 i k.
Proof. exact (fun h0 : term173 _106515 i k => @lem4437052 _106515 _106516 k x' x i h1). Qed.
Lemma lem4437055 (p : Prop) : (term354 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4437056 {_106515 : Type'} (i : _106515) (k : _106515 -> Prop) : (term353 _106515 i k) = (@IN _106515 i k).
Proof. exact (@lem4437055 (@IN _106515 i k)). Qed.
Lemma lem4437057 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (i : _106515) (h1 : term190 _106515 _106516 k x' x i) : @IN _106515 i k.
Proof. exact (EQ_MP (@lem4437056 _106515 i k) (@lem4437053 _106515 _106516 k x' x i h1)). Qed.
Lemma lem4437063 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4437064 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (x : _106515 -> _106516) (_51036 : _106515) (k : _106515 -> Prop) : (term191 _106515 _106516 k x' x _51036) = (term355 _106515 _106516 x' x _51036 k).
Proof. exact (@lem4437063 ((x' _51036) = (x _51036)) (term173 _106515 _51036 k)). Qed.
Lemma lem4437072 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4437073 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (x : _106515 -> _106516) (_51036 : _106515) (k : _106515 -> Prop) : (term356 _106515 _106516 k x' x _51036) = (term357 _106515 _106516 x' x _51036 k).
Proof. exact (MK_COMB (@lem4437072) (@lem4437064 _106515 _106516 x' x _51036 k)). Qed.
Lemma lem4437081 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (x : _106515 -> _106516) (_51036 : _106515) (k : _106515 -> Prop) : (term355 _106515 _106516 x' x _51036 k) = (term355 _106515 _106516 x' x _51036 k).
Proof. exact (eq_refl (term355 _106515 _106516 x' x _51036 k)). Qed.
Lemma lem4437082 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (x : _106515 -> _106516) (_51036 : _106515) (k : _106515 -> Prop) : ((term191 _106515 _106516 k x' x _51036) = (term355 _106515 _106516 x' x _51036 k)) = ((term355 _106515 _106516 x' x _51036 k) = (term355 _106515 _106516 x' x _51036 k)).
Proof. exact (MK_COMB (@lem4437073 _106515 _106516 x' x _51036 k) (@lem4437081 _106515 _106516 x' x _51036 k)). Qed.
Lemma lem4437084 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4437085 (x : Prop) : (x = x) = True.
Proof. exact (@lem4437084 Prop x). Qed.
Lemma lem4437086 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (x : _106515 -> _106516) (_51036 : _106515) (k : _106515 -> Prop) : ((term355 _106515 _106516 x' x _51036 k) = (term355 _106515 _106516 x' x _51036 k)) = True.
Proof. exact (@lem4437085 (term355 _106515 _106516 x' x _51036 k)). Qed.
Lemma lem4437087 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (x : _106515 -> _106516) (_51036 : _106515) (k : _106515 -> Prop) : ((term191 _106515 _106516 k x' x _51036) = (term355 _106515 _106516 x' x _51036 k)) = True.
Proof. exact (TRANS (@lem4437082 _106515 _106516 x' x _51036 k) (@lem4437086 _106515 _106516 x' x _51036 k)). Qed.
Lemma lem4437088 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (x : _106515 -> _106516) (_51036 : _106515) (k : _106515 -> Prop) : True = ((term191 _106515 _106516 k x' x _51036) = (term355 _106515 _106516 x' x _51036 k)).
Proof. exact (SYM (@lem4437087 _106515 _106516 x' x _51036 k)). Qed.
Lemma lem4437089 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (x : _106515 -> _106516) (_51036 : _106515) (k : _106515 -> Prop) : (term191 _106515 _106516 k x' x _51036) = (term355 _106515 _106516 x' x _51036 k).
Proof. exact (EQ_MP (@lem4437088 _106515 _106516 x' x _51036 k) (@lem0)). Qed.
Lemma lem4437090 {_106515 _106516 : Type'} (_51036 : _106515) (i : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (h1 : term326 _106515 _106516 i x k x') : term355 _106515 _106516 x' x _51036 k.
Proof. exact (EQ_MP (@lem4437089 _106515 _106516 x' x _51036 k) (@lem4436648 _106515 _106516 _51036 i x k x' h1)). Qed.
Lemma lem4437092 (b : Prop) (a : Prop) : (a \/ b) = (term358 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4437093 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (_51036 : _106515) : (term355 _106515 _106516 x' x _51036 k) = (term359 _106515 _106516 k x' x _51036).
Proof. exact (@lem4437092 (term173 _106515 _51036 k) ((x' _51036) = (x _51036))). Qed.
Lemma lem4437095 (a : Prop) : (term145 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4437096 {_106515 : Type'} (_51036 : _106515) (k : _106515 -> Prop) : (term170 _106515 _51036 k) = (@IN _106515 _51036 k).
Proof. exact (@lem4437095 (@IN _106515 _51036 k)). Qed.
Lemma lem4437097 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4437098 {_106515 : Type'} (_51036 : _106515) (k : _106515 -> Prop) : (term360 _106515 _51036 k) = (term49 _106515 _51036 k).
Proof. exact (MK_COMB (@lem4437097) (@lem4437096 _106515 _51036 k)). Qed.
Lemma lem4437099 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (x : _106515 -> _106516) (_51036 : _106515) : ((x' _51036) = (x _51036)) = ((x' _51036) = (x _51036)).
Proof. exact (eq_refl ((x' _51036) = (x _51036))). Qed.
Lemma lem4437100 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (_51036 : _106515) : (term359 _106515 _106516 k x' x _51036) = (term51 _106515 _106516 k x' x _51036).
Proof. exact (MK_COMB (@lem4437098 _106515 _51036 k) (@lem4437099 _106515 _106516 x' x _51036)). Qed.
Lemma lem4437101 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (_51036 : _106515) : (term355 _106515 _106516 x' x _51036 k) = (term51 _106515 _106516 k x' x _51036).
Proof. exact (TRANS (@lem4437093 _106515 _106516 k x' x _51036) (@lem4437100 _106515 _106516 k x' x _51036)). Qed.
Lemma lem4437104 {_106515 _106516 : Type'} (_51036 : _106515) (i : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (h1 : term326 _106515 _106516 i x k x') : term51 _106515 _106516 k x' x _51036.
Proof. exact (EQ_MP (@lem4437101 _106515 _106516 k x' x _51036) (@lem4437090 _106515 _106516 _51036 i x k x' h1)). Qed.
Lemma lem4437105 {_106515 _106516 : Type'} (_51036 : _106515) (i : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (h1 : term326 _106515 _106516 i x k x') : term51 _106515 _106516 k x' x _51036.
Proof. exact (@lem4437104 _106515 _106516 _51036 i x k x' h1). Qed.
Lemma lem4437106 {_106515 _106516 : Type'} (i : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (h1 : term326 _106515 _106516 i x k x') : term51 _106515 _106516 k x' x i.
Proof. exact (@lem4437105 _106515 _106516 i i x k x' h1). Qed.
Lemma lem4437109 {_106515 _106516 : Type'} (i : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (h1 : term190 _106515 _106516 k x' x i) (h2 : term326 _106515 _106516 i x k x') : (x' i) = (x i).
Proof. exact (@lem4437106 _106515 _106516 i x k x' h2 (@lem4437057 _106515 _106516 k x' x i h1)). Qed.
Lemma lem4437110 {_106515 _106516 : Type'} (i : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (h1 : term190 _106515 _106516 k x' x i) (h2 : term326 _106515 _106516 i x k x') : term361 _106515 _106516 x' x i.
Proof. exact (fun h0 : term208 _106515 _106516 x' x i => @lem4437109 _106515 _106516 i x k x' h1 h2). Qed.
Lemma lem4437112 (p : Prop) : (term354 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4437113 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (x : _106515 -> _106516) (i : _106515) : (term361 _106515 _106516 x' x i) = ((x' i) = (x i)).
Proof. exact (@lem4437112 ((x' i) = (x i))). Qed.
Lemma lem4437114 {_106515 _106516 : Type'} (i : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (h1 : term190 _106515 _106516 k x' x i) (h2 : term326 _106515 _106516 i x k x') : (x' i) = (x i).
Proof. exact (EQ_MP (@lem4437113 _106515 _106516 x' x i) (@lem4437110 _106515 _106516 i x k x' h1 h2)). Qed.
Lemma lem4437117 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4437119 {_106515 _106516 : Type'} (x' : _106515 -> _106516) (x : _106515 -> _106516) (i : _106515) : (term208 _106515 _106516 x' x i) = (term362 _106515 _106516 x' x i).
Proof. exact (@lem4437117 ((x' i) = (x i))). Qed.
Lemma lem4437122 {_106515 _106516 : Type'} (k : _106515 -> Prop) (x' : _106515 -> _106516) (x : _106515 -> _106516) (i : _106515) (h1 : term190 _106515 _106516 k x' x i) : term362 _106515 _106516 x' x i.
Proof. exact (EQ_MP (@lem4437119 _106515 _106516 x' x i) (@lem4436658 _106515 _106516 k x' x i h1)). Qed.
Lemma lem4437125 {_106515 _106516 : Type'} (i : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (h1 : term190 _106515 _106516 k x' x i) (h2 : term326 _106515 _106516 i x k x') : False.
Proof. exact (@lem4437122 _106515 _106516 k x' x i h1 (@lem4437114 _106515 _106516 i x k x' h1 h2)). Qed.
Lemma lem4437126 {_106515 _106516 : Type'} (i : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (h1 : term190 _106515 _106516 k x' x i) (h2 : term326 _106515 _106516 i x k x') : term363.
Proof. exact (fun h0 : ~ False => @lem4437125 _106515 _106516 i x k x' h1 h2). Qed.
Lemma lem4437128 (p : Prop) : (term354 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4437129 : term363 = False.
Proof. exact (@lem4437128 False). Qed.
Lemma lem4437130 {_106515 _106516 : Type'} (i : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (h1 : term190 _106515 _106516 k x' x i) (h2 : term326 _106515 _106516 i x k x') : False.
Proof. exact (EQ_MP (@lem4437129) (@lem4437126 _106515 _106516 i x k x' h1 h2)). Qed.
Lemma lem4437131 {_106515 _106516 : Type'} (i : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (h1 : term326 _106515 _106516 i x k x') : False.
Proof. exact (or_elim (@lem4436426 _106515 _106516 i x k x' h1) (fun h0 : term172 _106515 _106516 k x' i => @lem4437009 _106515 _106516 i x k x' h0 h1) (fun h0 : term190 _106515 _106516 k x' x i => @lem4437130 _106515 _106516 i x k x' h0 h1)). Qed.
Lemma lem4437132 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (i : _106515) (h1 : term291 _106515 _106516 x k x' i) : False.
Proof. exact (or_elim (@lem4436415 _106515 _106516 x k x' i h1) (fun h0 : term190 _106515 _106516 k x' x i => @lem4436779 _106515 _106516 k x' x i h1 h0) (fun h0 : term172 _106515 _106516 k x' i => @lem4436894 _106515 _106516 x k x' i h0 h1)). Qed.
Lemma lem4437133 {_106515 _106516 : Type'} (i : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (h1 : term345 _106515 _106516 i x k x') : False.
Proof. exact (or_elim (@lem4436412 _106515 _106516 i x k x' h1) (fun h0 : term291 _106515 _106516 x k x' i => @lem4437132 _106515 _106516 x k x' i h0) (fun h0 : term326 _106515 _106516 i x k x' => @lem4437131 _106515 _106516 i x k x' h0)). Qed.
Lemma lem4437134 {_106515 _106516 : Type'} (i : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (h1 : term345 _106515 _106516 i x k x') : (term345 _106515 _106516 i x k x') = False.
Proof. exact (prop_ext (fun h2 : term345 _106515 _106516 i x k x' => @lem4437133 _106515 _106516 i x k x' h1) (fun h2 : False => @lem4436412 _106515 _106516 i x k x' h1)). Qed.
Lemma lem4437135 {_106515 _106516 : Type'} (i : _106515) (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (h1 : term345 _106515 _106516 i x k x') : False.
Proof. exact (EQ_MP (@lem4437134 _106515 _106516 i x k x' h1) (@lem4436412 _106515 _106516 i x k x' h1)). Qed.
Lemma lem4437136 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (h1 : term169 _106515 _106516 x k x') : False.
Proof. exact (ex_elim (@lem4436233 _106515 _106516 x k x' h1) (fun i : _106515 => fun h0 : term347 _106515 _106516 x k x' i => @lem4437135 _106515 _106516 i x k x' h0)). Qed.
Lemma lem4437137 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (h1 : term169 _106515 _106516 x k x') : (term169 _106515 _106516 x k x') = False.
Proof. exact (prop_ext (fun h2 : term169 _106515 _106516 x k x' => @lem4437136 _106515 _106516 x k x' h1) (fun h2 : False => @lem4435498 _106515 _106516 x k x' h1)). Qed.
Lemma lem4437138 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) (h1 : term169 _106515 _106516 x k x') : False.
Proof. exact (EQ_MP (@lem4437137 _106515 _106516 x k x' h1) (@lem4435498 _106515 _106516 x k x' h1)). Qed.
Lemma lem4437139 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : term168 _106515 _106516 x k x'.
Proof. exact (fun h0 : term169 _106515 _106516 x k x' => @lem4437138 _106515 _106516 x k x' h0). Qed.
Lemma lem4437140 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) (x' : _106515 -> _106516) : (term116 _106515 _106516 k x' x) = (term159 _106515 _106516 x k x').
Proof. exact (EQ_MP (@lem4435497 _106515 _106516 x k x') (@lem4437139 _106515 _106516 x k x')). Qed.
Lemma lem4437145 {_106515 _106516 : Type'} (x : _106515 -> _106516) (k : _106515 -> Prop) : term163 _106515 _106516 x k.
Proof. exact (fun x' : _106515 -> _106516 => @lem4437140 _106515 _106516 x k x'). Qed.
Lemma lem4437150 {_106515 _106516 : Type'} (k : _106515 -> Prop) : term165 _106515 _106516 k.
Proof. exact (fun x : _106515 -> _106516 => @lem4437145 _106515 _106516 x k). Qed.
Lemma lem4437155 {_106515 _106516 : Type'} : term167 _106515 _106516.
Proof. exact (fun k : _106515 -> Prop => @lem4437150 _106515 _106516 k). Qed.
Lemma lem4437156 {_106515 _106516 : Type'} : term139 _106515 _106516.
Proof. exact (EQ_MP (@lem4435493 _106515 _106516) (@lem4437155 _106515 _106516)). Qed.
Lemma lem4437158 {_106515 _106516 : Type'} : term139 _106515 _106516.
Proof. exact (@lem4435289 _106515 _106516 (@lem4437156 _106515 _106516)). Qed.
Lemma lem4437159 {_106515 _106516 : Type'} (h1 : term140 _106515 _106516) : False.
Proof. exact (@lem4437158 _106515 _106516 (@lem4435273 _106515 _106516 h1)). Qed.
Lemma lem4437160 {_106515 _106516 : Type'} (h1 : term140 _106515 _106516) : (term140 _106515 _106516) = False.
Proof. exact (prop_ext (fun h2 : term140 _106515 _106516 => @lem4437159 _106515 _106516 h1) (fun h2 : False => @lem4435273 _106515 _106516 h1)). Qed.
Lemma lem4437161 {_106515 _106516 : Type'} (h1 : term140 _106515 _106516) : False.
Proof. exact (EQ_MP (@lem4437160 _106515 _106516 h1) (@lem4435273 _106515 _106516 h1)). Qed.
Lemma lem4437162 {_106515 _106516 : Type'} : term139 _106515 _106516.
Proof. exact (fun h0 : term140 _106515 _106516 => @lem4437161 _106515 _106516 h0). Qed.
Lemma lem4437163 {_106515 _106516 : Type'} : term137 _106515 _106516.
Proof. exact (EQ_MP (@lem4435272 _106515 _106516) (@lem4437162 _106515 _106516)). Qed.
Lemma lem4437164 {_106515 _106516 : Type'} : term126 _106515 _106516.
Proof. exact (EQ_MP (@lem4435268 _106515 _106516) (@lem4437163 _106515 _106516)). Qed.
Lemma lem4437165 {_106515 _106516 : Type'} : term80 _106515 _106516.
Proof. exact (EQ_MP (@lem4435170 _106515 _106516) (@lem4437164 _106515 _106516)). Qed.
Lemma lem4437166 {_106515 _106516 : Type'} : term79 _106515 _106516.
Proof. exact (EQ_MP (@lem4435016 _106515 _106516) (@lem4437165 _106515 _106516)). Qed.
