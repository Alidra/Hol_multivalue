Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INTER_CARTESIAN_PRODUCT_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import EXTENSION_spec.
Require Import IN_INTER_spec.
Require Import cartesian_product_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm18392_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19490_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Lemma lem4429939 {_83095 : Type'} : term0 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem4429940 {_83095 : Type'} (p : _83095 -> Prop) : term1 _83095 p.
Proof. exact (@lem4429939 _83095 p). Qed.
Lemma lem4429941 {_83095 : Type'} (p : _83095 -> Prop) : (term1 _83095 p) = (term2 _83095 p).
Proof. exact (eq_refl (term1 _83095 p)). Qed.
Lemma lem4429942 {_83095 : Type'} (p : _83095 -> Prop) : term2 _83095 p.
Proof. exact (EQ_MP (@lem4429941 _83095 p) (@lem4429940 _83095 p)). Qed.
Lemma lem4429943 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term3 _83095 p x.
Proof. exact (@lem4429942 _83095 p x). Qed.
Lemma lem4429944 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term3 _83095 p x) = ((term4 _83095 x p) = (p x)).
Proof. exact (eq_refl (term3 _83095 p x)). Qed.
Lemma lem4429953 {A : Type'} (s : A -> Prop) : term5 A s.
Proof. exact (@lem3205222 A s). Qed.
Lemma lem4429954 {A : Type'} (s : A -> Prop) : (term5 A s) = (term6 A s).
Proof. exact (eq_refl (term5 A s)). Qed.
Lemma lem4429955 {A : Type'} (s : A -> Prop) : term6 A s.
Proof. exact (EQ_MP (@lem4429954 A s) (@lem4429953 A s)). Qed.
Lemma lem4429956 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term7 A s t.
Proof. exact (@lem4429955 A s t). Qed.
Lemma lem4429957 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term7 A s t) = (term8 A s t).
Proof. exact (eq_refl (term7 A s t)). Qed.
Lemma lem4429958 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term8 A s t.
Proof. exact (EQ_MP (@lem4429957 A s t) (@lem4429956 A s t)). Qed.
Lemma lem4429959 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term9 A s t x.
Proof. exact (@lem4429958 A s t x). Qed.
Lemma lem4429960 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term9 A s t x) = ((term10 A x s t) = (term11 A s x t)).
Proof. exact (eq_refl (term9 A s t x)). Qed.
Lemma lem4429962 {A K : Type'} (k : K -> Prop) : term12 A K k.
Proof. exact (@lem4399444 A K k). Qed.
Lemma lem4429963 {A K : Type'} (k : K -> Prop) : (term12 A K k) = (term13 A K k).
Proof. exact (eq_refl (term12 A K k)). Qed.
Lemma lem4429964 {A K : Type'} (k : K -> Prop) : term13 A K k.
Proof. exact (EQ_MP (@lem4429963 A K k) (@lem4429962 A K k)). Qed.
Lemma lem4429965 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term14 A K k s.
Proof. exact (@lem4429964 A K k s). Qed.
Lemma lem4429966 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term14 A K k s) = ((@cartesian_product A K k s) = (term15 A K k s)).
Proof. exact (eq_refl (term14 A K k s)). Qed.
Lemma lem4429968 {A : Type'} (s : A -> Prop) : term16 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem4429969 {A : Type'} (s : A -> Prop) : (term16 A s) = (term17 A s).
Proof. exact (eq_refl (term16 A s)). Qed.
Lemma lem4429970 {A : Type'} (s : A -> Prop) : term17 A s.
Proof. exact (EQ_MP (@lem4429969 A s) (@lem4429968 A s)). Qed.
Lemma lem4429971 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term18 A s t.
Proof. exact (@lem4429970 A s t). Qed.
Lemma lem4429972 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term18 A s t) = ((s = t) = (term19 A s t)).
Proof. exact (eq_refl (term18 A s t)). Qed.
Lemma lem4429989 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term19 A s t).
Proof. exact (EQ_MP (@lem4429972 A s t) (@lem4429971 A s t)). Qed.
Lemma lem4429990 {A K : Type'} (s : type805 A K) (t : type805 A K) : (s = t) = (term20 A K s t).
Proof. exact (@lem4429989 (K -> A) s t). Qed.
Lemma lem4429991 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : ((term21 A K s k t) = (term22 A K k s t)) = (term23 A K k s t).
Proof. exact (@lem4429990 A K (term21 A K s k t) (term22 A K k s t)). Qed.
Lemma lem4430001 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term10 A x s t) = (term11 A s x t).
Proof. exact (EQ_MP (@lem4429960 A s x t) (@lem4429959 A s t x)). Qed.
Lemma lem4430002 {A K : Type'} (s : type805 A K) (x : K -> A) (t : type805 A K) : (term24 A K x s t) = (term25 A K s x t).
Proof. exact (@lem4430001 (K -> A) s x t). Qed.
Lemma lem4430003 {A K : Type'} (s : type1470 A K) (x : K -> A) (k : K -> Prop) (t : type1470 A K) : (term26 A K x s k t) = (term27 A K s x k t).
Proof. exact (@lem4430002 A K (@cartesian_product A K k s) x (@cartesian_product A K k t)). Qed.
Lemma lem4430007 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@cartesian_product A K k s) = (term15 A K k s).
Proof. exact (EQ_MP (@lem4429966 A K k s) (@lem4429965 A K k s)). Qed.
Lemma lem4430008 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@cartesian_product A K k s) = (term15 A K k s).
Proof. exact (@lem4430007 A K k s). Qed.
Lemma lem4430021 {A K : Type'} (x : K -> A) : (@IN (K -> A) x) = (@IN (K -> A) x).
Proof. exact (eq_refl (@IN (K -> A) x)). Qed.
Lemma lem4430022 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) : (term28 A K x k s) = (term29 A K x k s).
Proof. exact (MK_COMB (@lem4430021 A K x) (@lem4430008 A K k s)). Qed.
Lemma lem4430024 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term4 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem4429944 _83095 p x) (@lem4429943 _83095 p x)). Qed.
Lemma lem4430025 {A K : Type'} (p : type805 A K) (x : K -> A) : (term30 A K x p) = (p x).
Proof. exact (@lem4430024 (K -> A) p x). Qed.
Lemma lem4430026 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term31 A K x k s) = (term32 A K k s x).
Proof. exact (@lem4430025 A K (term33 A K k s) x). Qed.
Lemma lem4430027 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term32 A K k s f) = (term34 A K k f s).
Proof. exact (eq_refl (term32 A K k s f)). Qed.
Lemma lem4430028 {A K : Type'} (GEN_PVAR_140 : K -> A) : (@SETSPEC (K -> A) GEN_PVAR_140) = (@SETSPEC (K -> A) GEN_PVAR_140).
Proof. exact (eq_refl (@SETSPEC (K -> A) GEN_PVAR_140)). Qed.
Lemma lem4430029 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term35 A K GEN_PVAR_140 k s f) = (term36 A K GEN_PVAR_140 k f s).
Proof. exact (MK_COMB (@lem4430028 A K GEN_PVAR_140) (@lem4430027 A K k f s)). Qed.
Lemma lem4430030 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4430031 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term37 A K GEN_PVAR_140 k s f) = (term38 A K GEN_PVAR_140 k s f).
Proof. exact (MK_COMB (@lem4430029 A K GEN_PVAR_140 k f s) (@lem4430030 A K f)). Qed.
Lemma lem4430032 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (s : type1470 A K) : (term39 A K GEN_PVAR_140 k s) = (term40 A K GEN_PVAR_140 k s).
Proof. exact (fun_ext (fun f : K -> A => @lem4430031 A K GEN_PVAR_140 k s f)). Qed.
Lemma lem4430033 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4430034 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (s : type1470 A K) : (term41 A K GEN_PVAR_140 k s) = (term42 A K GEN_PVAR_140 k s).
Proof. exact (MK_COMB (@lem4430033 A K) (@lem4430032 A K GEN_PVAR_140 k s)). Qed.
Lemma lem4430035 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term43 A K k s) = (term44 A K k s).
Proof. exact (fun_ext (fun GEN_PVAR_140 : K -> A => @lem4430034 A K GEN_PVAR_140 k s)). Qed.
Lemma lem4430036 {A K : Type'} : (@GSPEC (K -> A)) = (@GSPEC (K -> A)).
Proof. exact (eq_refl (@GSPEC (K -> A))). Qed.
Lemma lem4430037 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term45 A K k s) = (term15 A K k s).
Proof. exact (MK_COMB (@lem4430036 A K) (@lem4430035 A K k s)). Qed.
Lemma lem4430038 {A K : Type'} (x : K -> A) : (@IN (K -> A) x) = (@IN (K -> A) x).
Proof. exact (eq_refl (@IN (K -> A) x)). Qed.
Lemma lem4430039 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) : (term31 A K x k s) = (term29 A K x k s).
Proof. exact (MK_COMB (@lem4430038 A K x) (@lem4430037 A K k s)). Qed.
Lemma lem4430040 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4430041 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) : (term46 A K x k s) = (term47 A K x k s).
Proof. exact (MK_COMB (@lem4430040) (@lem4430039 A K x k s)). Qed.
Lemma lem4430042 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term32 A K k s x) = (term34 A K k x s).
Proof. exact (eq_refl (term32 A K k s x)). Qed.
Lemma lem4430043 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : ((term31 A K x k s) = (term32 A K k s x)) = ((term29 A K x k s) = (term34 A K k x s)).
Proof. exact (MK_COMB (@lem4430041 A K x k s) (@lem4430042 A K k x s)). Qed.
Lemma lem4430044 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term29 A K x k s) = (term34 A K k x s).
Proof. exact (EQ_MP (@lem4430043 A K k x s) (@lem4430026 A K k s x)). Qed.
Lemma lem4430053 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term28 A K x k s) = (term34 A K k x s).
Proof. exact (TRANS (@lem4430022 A K x k s) (@lem4430044 A K k x s)). Qed.
Lemma lem4430054 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4430055 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term48 A K x k s) = (term49 A K k x s).
Proof. exact (MK_COMB (@lem4430054) (@lem4430053 A K k x s)). Qed.
Lemma lem4430057 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@cartesian_product A K k s) = (term15 A K k s).
Proof. exact (EQ_MP (@lem4429966 A K k s) (@lem4429965 A K k s)). Qed.
Lemma lem4430058 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@cartesian_product A K k s) = (term15 A K k s).
Proof. exact (@lem4430057 A K k s). Qed.
Lemma lem4430059 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (@cartesian_product A K k t) = (term15 A K k t).
Proof. exact (@lem4430058 A K k t). Qed.
Lemma lem4430072 {A K : Type'} (x : K -> A) : (@IN (K -> A) x) = (@IN (K -> A) x).
Proof. exact (eq_refl (@IN (K -> A) x)). Qed.
Lemma lem4430073 {A K : Type'} (x : K -> A) (k : K -> Prop) (t : type1470 A K) : (term28 A K x k t) = (term29 A K x k t).
Proof. exact (MK_COMB (@lem4430072 A K x) (@lem4430059 A K k t)). Qed.
Lemma lem4430075 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term4 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem4429944 _83095 p x) (@lem4429943 _83095 p x)). Qed.
Lemma lem4430076 {A K : Type'} (p : type805 A K) (x : K -> A) : (term30 A K x p) = (p x).
Proof. exact (@lem4430075 (K -> A) p x). Qed.
Lemma lem4430077 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term31 A K x k t) = (term32 A K k t x).
Proof. exact (@lem4430076 A K (term33 A K k t) x). Qed.
Lemma lem4430078 {A K : Type'} (k : K -> Prop) (f : K -> A) (t : type1470 A K) : (term32 A K k t f) = (term34 A K k f t).
Proof. exact (eq_refl (term32 A K k t f)). Qed.
Lemma lem4430079 {A K : Type'} (GEN_PVAR_140 : K -> A) : (@SETSPEC (K -> A) GEN_PVAR_140) = (@SETSPEC (K -> A) GEN_PVAR_140).
Proof. exact (eq_refl (@SETSPEC (K -> A) GEN_PVAR_140)). Qed.
Lemma lem4430080 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (f : K -> A) (t : type1470 A K) : (term35 A K GEN_PVAR_140 k t f) = (term36 A K GEN_PVAR_140 k f t).
Proof. exact (MK_COMB (@lem4430079 A K GEN_PVAR_140) (@lem4430078 A K k f t)). Qed.
Lemma lem4430081 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4430082 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (t : type1470 A K) (f : K -> A) : (term37 A K GEN_PVAR_140 k t f) = (term38 A K GEN_PVAR_140 k t f).
Proof. exact (MK_COMB (@lem4430080 A K GEN_PVAR_140 k f t) (@lem4430081 A K f)). Qed.
Lemma lem4430083 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (t : type1470 A K) : (term39 A K GEN_PVAR_140 k t) = (term40 A K GEN_PVAR_140 k t).
Proof. exact (fun_ext (fun f : K -> A => @lem4430082 A K GEN_PVAR_140 k t f)). Qed.
Lemma lem4430084 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4430085 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (t : type1470 A K) : (term41 A K GEN_PVAR_140 k t) = (term42 A K GEN_PVAR_140 k t).
Proof. exact (MK_COMB (@lem4430084 A K) (@lem4430083 A K GEN_PVAR_140 k t)). Qed.
Lemma lem4430086 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (term43 A K k t) = (term44 A K k t).
Proof. exact (fun_ext (fun GEN_PVAR_140 : K -> A => @lem4430085 A K GEN_PVAR_140 k t)). Qed.
Lemma lem4430087 {A K : Type'} : (@GSPEC (K -> A)) = (@GSPEC (K -> A)).
Proof. exact (eq_refl (@GSPEC (K -> A))). Qed.
Lemma lem4430088 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (term45 A K k t) = (term15 A K k t).
Proof. exact (MK_COMB (@lem4430087 A K) (@lem4430086 A K k t)). Qed.
Lemma lem4430089 {A K : Type'} (x : K -> A) : (@IN (K -> A) x) = (@IN (K -> A) x).
Proof. exact (eq_refl (@IN (K -> A) x)). Qed.
Lemma lem4430090 {A K : Type'} (x : K -> A) (k : K -> Prop) (t : type1470 A K) : (term31 A K x k t) = (term29 A K x k t).
Proof. exact (MK_COMB (@lem4430089 A K x) (@lem4430088 A K k t)). Qed.
Lemma lem4430091 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4430092 {A K : Type'} (x : K -> A) (k : K -> Prop) (t : type1470 A K) : (term46 A K x k t) = (term47 A K x k t).
Proof. exact (MK_COMB (@lem4430091) (@lem4430090 A K x k t)). Qed.
Lemma lem4430093 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) : (term32 A K k t x) = (term34 A K k x t).
Proof. exact (eq_refl (term32 A K k t x)). Qed.
Lemma lem4430094 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) : ((term31 A K x k t) = (term32 A K k t x)) = ((term29 A K x k t) = (term34 A K k x t)).
Proof. exact (MK_COMB (@lem4430092 A K x k t) (@lem4430093 A K k x t)). Qed.
Lemma lem4430095 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) : (term29 A K x k t) = (term34 A K k x t).
Proof. exact (EQ_MP (@lem4430094 A K k x t) (@lem4430077 A K k t x)). Qed.
Lemma lem4430104 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) : (term28 A K x k t) = (term34 A K k x t).
Proof. exact (TRANS (@lem4430073 A K x k t) (@lem4430095 A K k x t)). Qed.
Lemma lem4430105 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (t : type1470 A K) : (term27 A K s x k t) = (term50 A K s k x t).
Proof. exact (MK_COMB (@lem4430055 A K k x s) (@lem4430104 A K k x t)). Qed.
Lemma lem4430108 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (t : type1470 A K) : (term26 A K x s k t) = (term50 A K s k x t).
Proof. exact (TRANS (@lem4430003 A K s x k t) (@lem4430105 A K s k x t)). Qed.
Lemma lem4430109 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4430110 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (t : type1470 A K) : (term51 A K x s k t) = (term52 A K s k x t).
Proof. exact (MK_COMB (@lem4430109) (@lem4430108 A K s k x t)). Qed.
Lemma lem4430112 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@cartesian_product A K k s) = (term15 A K k s).
Proof. exact (EQ_MP (@lem4429966 A K k s) (@lem4429965 A K k s)). Qed.
Lemma lem4430113 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@cartesian_product A K k s) = (term15 A K k s).
Proof. exact (@lem4430112 A K k s). Qed.
Lemma lem4430114 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term22 A K k s t) = (term53 A K k s t).
Proof. exact (@lem4430113 A K k (term54 A K s t)). Qed.
Lemma lem4430128 {A B : Type'} (f : A -> B) (y : A) : (term55 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4430129 {A K : Type'} (f : type1470 A K) (y : K) : (term56 A K f y) = (f y).
Proof. exact (@lem4430128 K (A -> Prop) f y). Qed.
Lemma lem4430130 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term57 A K s t i) = (term58 A K s t i).
Proof. exact (@lem4430129 A K (term54 A K s t) i). Qed.
Lemma lem4430131 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term58 A K s t i) = (term59 A K s t i).
Proof. exact (eq_refl (term58 A K s t i)). Qed.
Lemma lem4430132 {A K : Type'} (s : type1470 A K) (t : type1470 A K) : (term60 A K s t) = (term54 A K s t).
Proof. exact (fun_ext (fun i : K => @lem4430131 A K s t i)). Qed.
Lemma lem4430133 {K : Type'} (i : K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4430134 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term57 A K s t i) = (term58 A K s t i).
Proof. exact (MK_COMB (@lem4430132 A K s t) (@lem4430133 K i)). Qed.
Lemma lem4430135 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4430136 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term61 A K s t i) = (term62 A K s t i).
Proof. exact (MK_COMB (@lem4430135 A) (@lem4430134 A K s t i)). Qed.
Lemma lem4430137 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term58 A K s t i) = (term59 A K s t i).
Proof. exact (eq_refl (term58 A K s t i)). Qed.
Lemma lem4430138 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : ((term57 A K s t i) = (term58 A K s t i)) = ((term58 A K s t i) = (term59 A K s t i)).
Proof. exact (MK_COMB (@lem4430136 A K s t i) (@lem4430137 A K s t i)). Qed.
Lemma lem4430139 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term58 A K s t i) = (term59 A K s t i).
Proof. exact (EQ_MP (@lem4430138 A K s t i) (@lem4430130 A K s t i)). Qed.
Lemma lem4430140 {A K : Type'} (f : K -> A) (i : K) : (term63 A K f i) = (term63 A K f i).
Proof. exact (eq_refl (term63 A K f i)). Qed.
Lemma lem4430141 {A K : Type'} (f : K -> A) (s : type1470 A K) (t : type1470 A K) (i : K) : (term64 A K f s t i) = (term65 A K f s t i).
Proof. exact (MK_COMB (@lem4430140 A K f i) (@lem4430139 A K s t i)). Qed.
Lemma lem4430143 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term10 A x s t) = (term11 A s x t).
Proof. exact (EQ_MP (@lem4429960 A s x t) (@lem4429959 A s t x)). Qed.
Lemma lem4430144 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term10 A x s t) = (term11 A s x t).
Proof. exact (@lem4430143 A s x t). Qed.
Lemma lem4430145 {A K : Type'} (s : type1470 A K) (f : K -> A) (t : type1470 A K) (i : K) : (term65 A K f s t i) = (term66 A K s f t i).
Proof. exact (@lem4430144 A (s i) (f i) (t i)). Qed.
Lemma lem4430148 {A K : Type'} (s : type1470 A K) (f : K -> A) (t : type1470 A K) (i : K) : (term64 A K f s t i) = (term66 A K s f t i).
Proof. exact (TRANS (@lem4430141 A K f s t i) (@lem4430145 A K s f t i)). Qed.
Lemma lem4430149 {K : Type'} (i : K) (k : K -> Prop) : (term67 K i k) = (term67 K i k).
Proof. exact (eq_refl (term67 K i k)). Qed.
Lemma lem4430150 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (t : type1470 A K) (i : K) : (term68 A K k f s t i) = (term69 A K k s f t i).
Proof. exact (MK_COMB (@lem4430149 K i k) (@lem4430148 A K s f t i)). Qed.
Lemma lem4430153 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (t : type1470 A K) : (term70 A K k f s t) = (term71 A K k s f t).
Proof. exact (fun_ext (fun i : K => @lem4430150 A K k s f t i)). Qed.
Lemma lem4430154 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4430155 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (t : type1470 A K) : (term72 A K k f s t) = (term73 A K k s f t).
Proof. exact (MK_COMB (@lem4430154 K) (@lem4430153 A K k s f t)). Qed.
Lemma lem4430160 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term74 A K k f) = (term74 A K k f).
Proof. exact (eq_refl (term74 A K k f)). Qed.
Lemma lem4430161 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (t : type1470 A K) : (term75 A K k f s t) = (term76 A K k s f t).
Proof. exact (MK_COMB (@lem4430160 A K k f) (@lem4430155 A K k s f t)). Qed.
Lemma lem4430164 {A K : Type'} (GEN_PVAR_140 : K -> A) : (@SETSPEC (K -> A) GEN_PVAR_140) = (@SETSPEC (K -> A) GEN_PVAR_140).
Proof. exact (eq_refl (@SETSPEC (K -> A) GEN_PVAR_140)). Qed.
Lemma lem4430165 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (s : type1470 A K) (f : K -> A) (t : type1470 A K) : (term77 A K GEN_PVAR_140 k f s t) = (term78 A K GEN_PVAR_140 k s f t).
Proof. exact (MK_COMB (@lem4430164 A K GEN_PVAR_140) (@lem4430161 A K k s f t)). Qed.
Lemma lem4430166 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4430167 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (f : K -> A) : (term79 A K GEN_PVAR_140 k s t f) = (term80 A K GEN_PVAR_140 k s t f).
Proof. exact (MK_COMB (@lem4430165 A K GEN_PVAR_140 k s f t) (@lem4430166 A K f)). Qed.
Lemma lem4430168 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term81 A K GEN_PVAR_140 k s t) = (term82 A K GEN_PVAR_140 k s t).
Proof. exact (fun_ext (fun f : K -> A => @lem4430167 A K GEN_PVAR_140 k s t f)). Qed.
Lemma lem4430169 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4430170 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term83 A K GEN_PVAR_140 k s t) = (term84 A K GEN_PVAR_140 k s t).
Proof. exact (MK_COMB (@lem4430169 A K) (@lem4430168 A K GEN_PVAR_140 k s t)). Qed.
Lemma lem4430175 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term85 A K k s t) = (term86 A K k s t).
Proof. exact (fun_ext (fun GEN_PVAR_140 : K -> A => @lem4430170 A K GEN_PVAR_140 k s t)). Qed.
Lemma lem4430176 {A K : Type'} : (@GSPEC (K -> A)) = (@GSPEC (K -> A)).
Proof. exact (eq_refl (@GSPEC (K -> A))). Qed.
Lemma lem4430177 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term53 A K k s t) = (term87 A K k s t).
Proof. exact (MK_COMB (@lem4430176 A K) (@lem4430175 A K k s t)). Qed.
Lemma lem4430178 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term22 A K k s t) = (term87 A K k s t).
Proof. exact (TRANS (@lem4430114 A K k s t) (@lem4430177 A K k s t)). Qed.
Lemma lem4430179 {A K : Type'} (x : K -> A) : (@IN (K -> A) x) = (@IN (K -> A) x).
Proof. exact (eq_refl (@IN (K -> A) x)). Qed.
Lemma lem4430180 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term88 A K x k s t) = (term89 A K x k s t).
Proof. exact (MK_COMB (@lem4430179 A K x) (@lem4430178 A K k s t)). Qed.
Lemma lem4430182 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term4 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem4429944 _83095 p x) (@lem4429943 _83095 p x)). Qed.
Lemma lem4430183 {A K : Type'} (p : type805 A K) (x : K -> A) : (term30 A K x p) = (p x).
Proof. exact (@lem4430182 (K -> A) p x). Qed.
Lemma lem4430184 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term90 A K x k s t) = (term91 A K k s t x).
Proof. exact (@lem4430183 A K (term92 A K k s t) x). Qed.
Lemma lem4430185 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (t : type1470 A K) : (term91 A K k s t f) = (term76 A K k s f t).
Proof. exact (eq_refl (term91 A K k s t f)). Qed.
Lemma lem4430186 {A K : Type'} (GEN_PVAR_140 : K -> A) : (@SETSPEC (K -> A) GEN_PVAR_140) = (@SETSPEC (K -> A) GEN_PVAR_140).
Proof. exact (eq_refl (@SETSPEC (K -> A) GEN_PVAR_140)). Qed.
Lemma lem4430187 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (s : type1470 A K) (f : K -> A) (t : type1470 A K) : (term93 A K GEN_PVAR_140 k s t f) = (term78 A K GEN_PVAR_140 k s f t).
Proof. exact (MK_COMB (@lem4430186 A K GEN_PVAR_140) (@lem4430185 A K k s f t)). Qed.
Lemma lem4430188 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4430189 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (f : K -> A) : (term94 A K GEN_PVAR_140 k s t f) = (term80 A K GEN_PVAR_140 k s t f).
Proof. exact (MK_COMB (@lem4430187 A K GEN_PVAR_140 k s f t) (@lem4430188 A K f)). Qed.
Lemma lem4430190 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term95 A K GEN_PVAR_140 k s t) = (term82 A K GEN_PVAR_140 k s t).
Proof. exact (fun_ext (fun f : K -> A => @lem4430189 A K GEN_PVAR_140 k s t f)). Qed.
Lemma lem4430191 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4430192 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term96 A K GEN_PVAR_140 k s t) = (term84 A K GEN_PVAR_140 k s t).
Proof. exact (MK_COMB (@lem4430191 A K) (@lem4430190 A K GEN_PVAR_140 k s t)). Qed.
Lemma lem4430193 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term97 A K k s t) = (term86 A K k s t).
Proof. exact (fun_ext (fun GEN_PVAR_140 : K -> A => @lem4430192 A K GEN_PVAR_140 k s t)). Qed.
Lemma lem4430194 {A K : Type'} : (@GSPEC (K -> A)) = (@GSPEC (K -> A)).
Proof. exact (eq_refl (@GSPEC (K -> A))). Qed.
Lemma lem4430195 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term98 A K k s t) = (term87 A K k s t).
Proof. exact (MK_COMB (@lem4430194 A K) (@lem4430193 A K k s t)). Qed.
Lemma lem4430196 {A K : Type'} (x : K -> A) : (@IN (K -> A) x) = (@IN (K -> A) x).
Proof. exact (eq_refl (@IN (K -> A) x)). Qed.
Lemma lem4430197 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term90 A K x k s t) = (term89 A K x k s t).
Proof. exact (MK_COMB (@lem4430196 A K x) (@lem4430195 A K k s t)). Qed.
Lemma lem4430198 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4430199 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term99 A K x k s t) = (term100 A K x k s t).
Proof. exact (MK_COMB (@lem4430198) (@lem4430197 A K x k s t)). Qed.
Lemma lem4430200 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (t : type1470 A K) : (term91 A K k s t x) = (term76 A K k s x t).
Proof. exact (eq_refl (term91 A K k s t x)). Qed.
Lemma lem4430201 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (t : type1470 A K) : ((term90 A K x k s t) = (term91 A K k s t x)) = ((term89 A K x k s t) = (term76 A K k s x t)).
Proof. exact (MK_COMB (@lem4430199 A K x k s t) (@lem4430200 A K k s x t)). Qed.
Lemma lem4430202 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (t : type1470 A K) : (term89 A K x k s t) = (term76 A K k s x t).
Proof. exact (EQ_MP (@lem4430201 A K k s x t) (@lem4430184 A K k s t x)). Qed.
Lemma lem4430213 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (t : type1470 A K) : (term88 A K x k s t) = (term76 A K k s x t).
Proof. exact (TRANS (@lem4430180 A K x k s t) (@lem4430202 A K k s x t)). Qed.
Lemma lem4430214 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (t : type1470 A K) : ((term26 A K x s k t) = (term88 A K x k s t)) = ((term50 A K s k x t) = (term76 A K k s x t)).
Proof. exact (MK_COMB (@lem4430110 A K s k x t) (@lem4430213 A K k s x t)). Qed.
Lemma lem4430219 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term101 A K k s t) = (term102 A K k s t).
Proof. exact (fun_ext (fun x : K -> A => @lem4430214 A K k s x t)). Qed.
Lemma lem4430220 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4430221 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term23 A K k s t) = (term103 A K k s t).
Proof. exact (MK_COMB (@lem4430220 A K) (@lem4430219 A K k s t)). Qed.
Lemma lem4430226 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : ((term21 A K s k t) = (term22 A K k s t)) = (term103 A K k s t).
Proof. exact (TRANS (@lem4429991 A K k s t) (@lem4430221 A K k s t)). Qed.
Lemma lem4430227 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term104 A K k s) = (term105 A K k s).
Proof. exact (fun_ext (fun t : type1470 A K => @lem4430226 A K k s t)). Qed.
Lemma lem4430228 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4430229 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term106 A K k s) = (term107 A K k s).
Proof. exact (MK_COMB (@lem4430228 A K) (@lem4430227 A K k s)). Qed.
Lemma lem4430234 {A K : Type'} (k : K -> Prop) : (term108 A K k) = (term109 A K k).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4430229 A K k s)). Qed.
Lemma lem4430235 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4430236 {A K : Type'} (k : K -> Prop) : (term110 A K k) = (term111 A K k).
Proof. exact (MK_COMB (@lem4430235 A K) (@lem4430234 A K k)). Qed.
Lemma lem4430241 {A K : Type'} : (term112 A K) = (term113 A K).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4430236 A K k)). Qed.
Lemma lem4430242 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4430243 {A K : Type'} : (term114 A K) = (term115 A K).
Proof. exact (MK_COMB (@lem4430242 K) (@lem4430241 A K)). Qed.
Lemma lem4430248 {A K : Type'} : (term115 A K) = (term114 A K).
Proof. exact (SYM (@lem4430243 A K)). Qed.
Lemma lem4430328 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4430329 {K : Type'} (P : K -> Prop) (x : K) : (@IN K x P) = (P x).
Proof. exact (@lem4430328 K P x). Qed.
Lemma lem4430330 {K : Type'} (k : K -> Prop) (i : K) : (@IN K i k) = (k i).
Proof. exact (@lem4430329 K k i). Qed.
Lemma lem4430331 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4430332 {K : Type'} (k : K -> Prop) (i : K) : (term67 K i k) = (term116 K k i).
Proof. exact (MK_COMB (@lem4430331) (@lem4430330 K k i)). Qed.
Lemma lem4430334 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4430335 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4430334 A P x). Qed.
Lemma lem4430336 {A K : Type'} (s : type1470 A K) (x : K -> A) (i : K) : (term117 A K x s i) = (term118 A K s x i).
Proof. exact (@lem4430335 A (s i) (x i)). Qed.
Lemma lem4430337 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (i : K) : (term119 A K k x s i) = (term120 A K k s x i).
Proof. exact (MK_COMB (@lem4430332 K k i) (@lem4430336 A K s x i)). Qed.
Lemma lem4430340 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term121 A K k x s) = (term122 A K k s x).
Proof. exact (fun_ext (fun i : K => @lem4430337 A K k s x i)). Qed.
Lemma lem4430341 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4430342 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term123 A K k x s) = (term124 A K k s x).
Proof. exact (MK_COMB (@lem4430341 K) (@lem4430340 A K k s x)). Qed.
Lemma lem4430347 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term74 A K k x) = (term74 A K k x).
Proof. exact (eq_refl (term74 A K k x)). Qed.
Lemma lem4430348 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term34 A K k x s) = (term125 A K k s x).
Proof. exact (MK_COMB (@lem4430347 A K k x) (@lem4430342 A K k s x)). Qed.
Lemma lem4430351 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4430352 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term49 A K k x s) = (term126 A K k s x).
Proof. exact (MK_COMB (@lem4430351) (@lem4430348 A K k s x)). Qed.
Lemma lem4430362 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4430363 {K : Type'} (P : K -> Prop) (x : K) : (@IN K x P) = (P x).
Proof. exact (@lem4430362 K P x). Qed.
Lemma lem4430364 {K : Type'} (k : K -> Prop) (i : K) : (@IN K i k) = (k i).
Proof. exact (@lem4430363 K k i). Qed.
Lemma lem4430365 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4430366 {K : Type'} (k : K -> Prop) (i : K) : (term67 K i k) = (term116 K k i).
Proof. exact (MK_COMB (@lem4430365) (@lem4430364 K k i)). Qed.
Lemma lem4430368 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4430369 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4430368 A P x). Qed.
Lemma lem4430370 {A K : Type'} (t : type1470 A K) (x : K -> A) (i : K) : (term117 A K x t i) = (term118 A K t x i).
Proof. exact (@lem4430369 A (t i) (x i)). Qed.
Lemma lem4430371 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) (i : K) : (term119 A K k x t i) = (term120 A K k t x i).
Proof. exact (MK_COMB (@lem4430366 K k i) (@lem4430370 A K t x i)). Qed.
Lemma lem4430374 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term121 A K k x t) = (term122 A K k t x).
Proof. exact (fun_ext (fun i : K => @lem4430371 A K k t x i)). Qed.
Lemma lem4430375 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4430376 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term123 A K k x t) = (term124 A K k t x).
Proof. exact (MK_COMB (@lem4430375 K) (@lem4430374 A K k t x)). Qed.
Lemma lem4430381 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term74 A K k x) = (term74 A K k x).
Proof. exact (eq_refl (term74 A K k x)). Qed.
Lemma lem4430382 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term34 A K k x t) = (term125 A K k t x).
Proof. exact (MK_COMB (@lem4430381 A K k x) (@lem4430376 A K k t x)). Qed.
Lemma lem4430385 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term50 A K s k x t) = (term127 A K s k t x).
Proof. exact (MK_COMB (@lem4430352 A K k s x) (@lem4430382 A K k t x)). Qed.
Lemma lem4430388 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4430389 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term52 A K s k x t) = (term128 A K s k t x).
Proof. exact (MK_COMB (@lem4430388) (@lem4430385 A K s k t x)). Qed.
Lemma lem4430399 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4430400 {K : Type'} (P : K -> Prop) (x : K) : (@IN K x P) = (P x).
Proof. exact (@lem4430399 K P x). Qed.
Lemma lem4430401 {K : Type'} (k : K -> Prop) (i : K) : (@IN K i k) = (k i).
Proof. exact (@lem4430400 K k i). Qed.
Lemma lem4430402 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4430403 {K : Type'} (k : K -> Prop) (i : K) : (term67 K i k) = (term116 K k i).
Proof. exact (MK_COMB (@lem4430402) (@lem4430401 K k i)). Qed.
Lemma lem4430407 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4430408 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4430407 A P x). Qed.
Lemma lem4430409 {A K : Type'} (s : type1470 A K) (x : K -> A) (i : K) : (term117 A K x s i) = (term118 A K s x i).
Proof. exact (@lem4430408 A (s i) (x i)). Qed.
Lemma lem4430410 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4430411 {A K : Type'} (s : type1470 A K) (x : K -> A) (i : K) : (term129 A K x s i) = (term130 A K s x i).
Proof. exact (MK_COMB (@lem4430410) (@lem4430409 A K s x i)). Qed.
Lemma lem4430413 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4430414 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4430413 A P x). Qed.
Lemma lem4430415 {A K : Type'} (t : type1470 A K) (x : K -> A) (i : K) : (term117 A K x t i) = (term118 A K t x i).
Proof. exact (@lem4430414 A (t i) (x i)). Qed.
Lemma lem4430416 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) : (term66 A K s x t i) = (term131 A K s t x i).
Proof. exact (MK_COMB (@lem4430411 A K s x i) (@lem4430415 A K t x i)). Qed.
Lemma lem4430419 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) : (term69 A K k s x t i) = (term132 A K k s t x i).
Proof. exact (MK_COMB (@lem4430403 K k i) (@lem4430416 A K s t x i)). Qed.
Lemma lem4430422 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term71 A K k s x t) = (term133 A K k s t x).
Proof. exact (fun_ext (fun i : K => @lem4430419 A K k s t x i)). Qed.
Lemma lem4430423 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4430424 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term73 A K k s x t) = (term134 A K k s t x).
Proof. exact (MK_COMB (@lem4430423 K) (@lem4430422 A K k s t x)). Qed.
Lemma lem4430429 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term74 A K k x) = (term74 A K k x).
Proof. exact (eq_refl (term74 A K k x)). Qed.
Lemma lem4430430 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term76 A K k s x t) = (term135 A K k s t x).
Proof. exact (MK_COMB (@lem4430429 A K k x) (@lem4430424 A K k s t x)). Qed.
Lemma lem4430433 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : ((term50 A K s k x t) = (term76 A K k s x t)) = ((term127 A K s k t x) = (term135 A K k s t x)).
Proof. exact (MK_COMB (@lem4430389 A K s k t x) (@lem4430430 A K k s t x)). Qed.
Lemma lem4430436 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term102 A K k s t) = (term136 A K k s t).
Proof. exact (fun_ext (fun x : K -> A => @lem4430433 A K k s t x)). Qed.
Lemma lem4430437 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4430438 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term103 A K k s t) = (term137 A K k s t).
Proof. exact (MK_COMB (@lem4430437 A K) (@lem4430436 A K k s t)). Qed.
Lemma lem4430443 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term105 A K k s) = (term138 A K k s).
Proof. exact (fun_ext (fun t : type1470 A K => @lem4430438 A K k s t)). Qed.
Lemma lem4430444 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4430445 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term107 A K k s) = (term139 A K k s).
Proof. exact (MK_COMB (@lem4430444 A K) (@lem4430443 A K k s)). Qed.
Lemma lem4430450 {A K : Type'} (k : K -> Prop) : (term109 A K k) = (term140 A K k).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4430445 A K k s)). Qed.
Lemma lem4430451 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4430452 {A K : Type'} (k : K -> Prop) : (term111 A K k) = (term141 A K k).
Proof. exact (MK_COMB (@lem4430451 A K) (@lem4430450 A K k)). Qed.
Lemma lem4430457 {A K : Type'} : (term113 A K) = (term142 A K).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4430452 A K k)). Qed.
Lemma lem4430458 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4430459 {A K : Type'} : (term115 A K) = (term143 A K).
Proof. exact (MK_COMB (@lem4430458 K) (@lem4430457 A K)). Qed.
Lemma lem4430464 {A K : Type'} : (term143 A K) = (term115 A K).
Proof. exact (SYM (@lem4430459 A K)). Qed.
Lemma lem4430466 (p : Prop) : p = (term144 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4430467 {A K : Type'} : (term143 A K) = (term145 A K).
Proof. exact (@lem4430466 (term143 A K)). Qed.
Lemma lem4430468 {A K : Type'} : (term145 A K) = (term143 A K).
Proof. exact (SYM (@lem4430467 A K)). Qed.
Lemma lem4430469 {A K : Type'} (h1 : term146 A K) : term146 A K.
Proof. exact (h1). Qed.
Lemma lem4430472 {A K : Type'} (h1 : term145 A K) : term145 A K.
Proof. exact (h1). Qed.
Lemma lem4430473 {A K : Type'} : term147 A K.
Proof. exact (fun h0 : term145 A K => @lem4430472 A K h0). Qed.
Lemma lem4430474 {A K : Type'} (h1 : term147 A K) : term147 A K.
Proof. exact (h1). Qed.
Lemma lem4430475 {A K : Type'} (h1 : term145 A K) : term145 A K.
Proof. exact (h1). Qed.
Lemma lem4430476 {A K : Type'} (h1 : term145 A K) (h2 : term147 A K) : term145 A K.
Proof. exact (@lem4430474 A K h2 (@lem4430475 A K h1)). Qed.
Lemma lem4430477 {A K : Type'} (h1 : term145 A K) : term148 A K.
Proof. exact (fun h0 : term147 A K => @lem4430476 A K h1 h0). Qed.
Lemma lem4430478 {A K : Type'} (h1 : term147 A K) : term147 A K.
Proof. exact (h1). Qed.
Lemma lem4430479 {A K : Type'} (h1 : term145 A K) (h2 : term147 A K) : term145 A K.
Proof. exact (@lem4430477 A K h1 (@lem4430478 A K h2)). Qed.
Lemma lem4430480 {A K : Type'} (h1 : term147 A K) : term147 A K.
Proof. exact (fun h0 : term145 A K => @lem4430479 A K h0 h1). Qed.
Lemma lem4430481 {A K : Type'} : term149 A K.
Proof. exact (fun h0 : term147 A K => @lem4430480 A K h0). Qed.
Lemma lem4430484 {A K : Type'} : term147 A K.
Proof. exact (@lem4430481 A K (@lem4430473 A K)). Qed.
Lemma lem4430485 {A K : Type'} : term147 A K.
Proof. exact (@lem4430484 A K). Qed.
Lemma lem4430487 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4430488 {A K : Type'} : (term145 A K) = (term150 A K).
Proof. exact (@lem4430487 (term146 A K)). Qed.
Lemma lem4430490 (t : Prop) : (term151 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4430491 {A K : Type'} : (term150 A K) = (term143 A K).
Proof. exact (@lem4430490 (term143 A K)). Qed.
Lemma lem4430540 {A K : Type'} : (term145 A K) = (term143 A K).
Proof. exact (TRANS (@lem4430488 A K) (@lem4430491 A K)). Qed.
Lemma lem4430549 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) : (term132 A K k s t x i) = (term132 A K k s t x i).
Proof. exact (eq_refl (term132 A K k s t x i)). Qed.
Lemma lem4430550 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term133 A K k s t x) = (term133 A K k s t x).
Proof. exact (fun_ext (fun i : K => @lem4430549 A K k s t x i)). Qed.
Lemma lem4430551 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4430552 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term134 A K k s t x) = (term134 A K k s t x).
Proof. exact (MK_COMB (@lem4430551 K) (@lem4430550 A K k s t x)). Qed.
Lemma lem4430555 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term74 A K k x) = (term74 A K k x).
Proof. exact (eq_refl (term74 A K k x)). Qed.
Lemma lem4430556 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term135 A K k s t x) = (term135 A K k s t x).
Proof. exact (MK_COMB (@lem4430555 A K k x) (@lem4430552 A K k s t x)). Qed.
Lemma lem4430561 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) (i : K) : (term120 A K k t x i) = (term120 A K k t x i).
Proof. exact (eq_refl (term120 A K k t x i)). Qed.
Lemma lem4430562 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term122 A K k t x) = (term122 A K k t x).
Proof. exact (fun_ext (fun i : K => @lem4430561 A K k t x i)). Qed.
Lemma lem4430563 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4430564 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term124 A K k t x) = (term124 A K k t x).
Proof. exact (MK_COMB (@lem4430563 K) (@lem4430562 A K k t x)). Qed.
Lemma lem4430567 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term74 A K k x) = (term74 A K k x).
Proof. exact (eq_refl (term74 A K k x)). Qed.
Lemma lem4430568 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term125 A K k t x) = (term125 A K k t x).
Proof. exact (MK_COMB (@lem4430567 A K k x) (@lem4430564 A K k t x)). Qed.
Lemma lem4430573 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (i : K) : (term120 A K k s x i) = (term120 A K k s x i).
Proof. exact (eq_refl (term120 A K k s x i)). Qed.
Lemma lem4430574 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term122 A K k s x) = (term122 A K k s x).
Proof. exact (fun_ext (fun i : K => @lem4430573 A K k s x i)). Qed.
Lemma lem4430575 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4430576 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term124 A K k s x) = (term124 A K k s x).
Proof. exact (MK_COMB (@lem4430575 K) (@lem4430574 A K k s x)). Qed.
Lemma lem4430579 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term74 A K k x) = (term74 A K k x).
Proof. exact (eq_refl (term74 A K k x)). Qed.
Lemma lem4430580 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term125 A K k s x) = (term125 A K k s x).
Proof. exact (MK_COMB (@lem4430579 A K k x) (@lem4430576 A K k s x)). Qed.
Lemma lem4430581 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4430582 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term126 A K k s x) = (term126 A K k s x).
Proof. exact (MK_COMB (@lem4430581) (@lem4430580 A K k s x)). Qed.
Lemma lem4430583 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term127 A K s k t x) = (term127 A K s k t x).
Proof. exact (MK_COMB (@lem4430582 A K k s x) (@lem4430568 A K k t x)). Qed.
Lemma lem4430584 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4430585 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term128 A K s k t x) = (term128 A K s k t x).
Proof. exact (MK_COMB (@lem4430584) (@lem4430583 A K s k t x)). Qed.
Lemma lem4430586 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : ((term127 A K s k t x) = (term135 A K k s t x)) = ((term127 A K s k t x) = (term135 A K k s t x)).
Proof. exact (MK_COMB (@lem4430585 A K s k t x) (@lem4430556 A K k s t x)). Qed.
Lemma lem4430587 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term136 A K k s t) = (term136 A K k s t).
Proof. exact (fun_ext (fun x : K -> A => @lem4430586 A K k s t x)). Qed.
Lemma lem4430588 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4430589 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term137 A K k s t) = (term137 A K k s t).
Proof. exact (MK_COMB (@lem4430588 A K) (@lem4430587 A K k s t)). Qed.
Lemma lem4430590 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term138 A K k s) = (term138 A K k s).
Proof. exact (fun_ext (fun t : type1470 A K => @lem4430589 A K k s t)). Qed.
Lemma lem4430591 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4430592 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term139 A K k s) = (term139 A K k s).
Proof. exact (MK_COMB (@lem4430591 A K) (@lem4430590 A K k s)). Qed.
Lemma lem4430593 {A K : Type'} (k : K -> Prop) : (term140 A K k) = (term140 A K k).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4430592 A K k s)). Qed.
Lemma lem4430594 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4430595 {A K : Type'} (k : K -> Prop) : (term141 A K k) = (term141 A K k).
Proof. exact (MK_COMB (@lem4430594 A K) (@lem4430593 A K k)). Qed.
Lemma lem4430596 {A K : Type'} : (term142 A K) = (term142 A K).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4430595 A K k)). Qed.
Lemma lem4430597 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4430598 {A K : Type'} : (term143 A K) = (term143 A K).
Proof. exact (MK_COMB (@lem4430597 K) (@lem4430596 A K)). Qed.
Lemma lem4430659 {A K : Type'} : (term145 A K) = (term143 A K).
Proof. exact (TRANS (@lem4430540 A K) (@lem4430598 A K)). Qed.
Lemma lem4430660 {A K : Type'} : (term143 A K) = (term145 A K).
Proof. exact (SYM (@lem4430659 A K)). Qed.
Lemma lem4430662 (p : Prop) : p = (term144 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4430663 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : ((term127 A K s k t x) = (term135 A K k s t x)) = (term152 A K k s t x).
Proof. exact (@lem4430662 ((term127 A K s k t x) = (term135 A K k s t x))). Qed.
Lemma lem4430664 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term152 A K k s t x) = ((term127 A K s k t x) = (term135 A K k s t x)).
Proof. exact (SYM (@lem4430663 A K k s t x)). Qed.
Lemma lem4430665 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term153 A K k s t x) : term153 A K k s t x.
Proof. exact (h1). Qed.
Lemma lem4430676 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (i : K) : (term154 A K k s x i) = (term155 A K k s x i).
Proof. exact (@lem17362 (k i) (term118 A K s x i)). Qed.
Lemma lem4430681 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (i : K) : (term120 A K k s x i) = (term156 A K k s x i).
Proof. exact (@lem17265 (k i) (term118 A K s x i)). Qed.
Lemma lem4430682 {K : Type'} (P : K -> Prop) : (term157 K P) = (term158 K P).
Proof. exact (@lem18392 K P). Qed.
Lemma lem4430683 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term159 A K k s x) = (term160 A K k s x).
Proof. exact (@lem4430682 K (term122 A K k s x)). Qed.
Lemma lem4430684 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (i : K) : (term161 A K k s x i) = (term120 A K k s x i).
Proof. exact (eq_refl (term161 A K k s x i)). Qed.
Lemma lem4430685 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4430686 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (i : K) : (term162 A K k s x i) = (term154 A K k s x i).
Proof. exact (MK_COMB (@lem4430685) (@lem4430684 A K k s x i)). Qed.
Lemma lem4430687 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (i : K) : (term162 A K k s x i) = (term155 A K k s x i).
Proof. exact (TRANS (@lem4430686 A K k s x i) (@lem4430676 A K k s x i)). Qed.
Lemma lem4430688 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term163 A K k s x) = (term164 A K k s x).
Proof. exact (fun_ext (fun i : K => @lem4430687 A K k s x i)). Qed.
Lemma lem4430689 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4430690 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term160 A K k s x) = (term165 A K k s x).
Proof. exact (MK_COMB (@lem4430689 K) (@lem4430688 A K k s x)). Qed.
Lemma lem4430691 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term159 A K k s x) = (term165 A K k s x).
Proof. exact (TRANS (@lem4430683 A K k s x) (@lem4430690 A K k s x)). Qed.
Lemma lem4430692 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term122 A K k s x) = (term166 A K k s x).
Proof. exact (fun_ext (fun i : K => @lem4430681 A K k s x i)). Qed.
Lemma lem4430693 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4430694 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term124 A K k s x) = (term167 A K k s x).
Proof. exact (MK_COMB (@lem4430693 K) (@lem4430692 A K k s x)). Qed.
Lemma lem4430696 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term168 A K k x) = (term168 A K k x).
Proof. exact (eq_refl (term168 A K k x)). Qed.
Lemma lem4430697 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term169 A K k s x) = (term170 A K k s x).
Proof. exact (MK_COMB (@lem4430696 A K k x) (@lem4430691 A K k s x)). Qed.
Lemma lem4430698 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term171 A K k s x) = (term169 A K k s x).
Proof. exact (@lem17045 (@EXTENSIONAL K A k x) (term124 A K k s x)). Qed.
Lemma lem4430699 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term171 A K k s x) = (term170 A K k s x).
Proof. exact (TRANS (@lem4430698 A K k s x) (@lem4430697 A K k s x)). Qed.
Lemma lem4430701 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term74 A K k x) = (term74 A K k x).
Proof. exact (eq_refl (term74 A K k x)). Qed.
Lemma lem4430702 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term125 A K k s x) = (term172 A K k s x).
Proof. exact (MK_COMB (@lem4430701 A K k x) (@lem4430694 A K k s x)). Qed.
Lemma lem4430713 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) (i : K) : (term154 A K k t x i) = (term155 A K k t x i).
Proof. exact (@lem17362 (k i) (term118 A K t x i)). Qed.
Lemma lem4430718 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) (i : K) : (term120 A K k t x i) = (term156 A K k t x i).
Proof. exact (@lem17265 (k i) (term118 A K t x i)). Qed.
Lemma lem4430719 {K : Type'} (P : K -> Prop) : (term157 K P) = (term158 K P).
Proof. exact (@lem18392 K P). Qed.
Lemma lem4430720 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term159 A K k t x) = (term160 A K k t x).
Proof. exact (@lem4430719 K (term122 A K k t x)). Qed.
Lemma lem4430721 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) (i : K) : (term161 A K k t x i) = (term120 A K k t x i).
Proof. exact (eq_refl (term161 A K k t x i)). Qed.
Lemma lem4430722 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4430723 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) (i : K) : (term162 A K k t x i) = (term154 A K k t x i).
Proof. exact (MK_COMB (@lem4430722) (@lem4430721 A K k t x i)). Qed.
Lemma lem4430724 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) (i : K) : (term162 A K k t x i) = (term155 A K k t x i).
Proof. exact (TRANS (@lem4430723 A K k t x i) (@lem4430713 A K k t x i)). Qed.
Lemma lem4430725 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term163 A K k t x) = (term164 A K k t x).
Proof. exact (fun_ext (fun i : K => @lem4430724 A K k t x i)). Qed.
Lemma lem4430726 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4430727 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term160 A K k t x) = (term165 A K k t x).
Proof. exact (MK_COMB (@lem4430726 K) (@lem4430725 A K k t x)). Qed.
Lemma lem4430728 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term159 A K k t x) = (term165 A K k t x).
Proof. exact (TRANS (@lem4430720 A K k t x) (@lem4430727 A K k t x)). Qed.
Lemma lem4430729 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term122 A K k t x) = (term166 A K k t x).
Proof. exact (fun_ext (fun i : K => @lem4430718 A K k t x i)). Qed.
Lemma lem4430730 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4430731 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term124 A K k t x) = (term167 A K k t x).
Proof. exact (MK_COMB (@lem4430730 K) (@lem4430729 A K k t x)). Qed.
Lemma lem4430733 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term168 A K k x) = (term168 A K k x).
Proof. exact (eq_refl (term168 A K k x)). Qed.
Lemma lem4430734 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term169 A K k t x) = (term170 A K k t x).
Proof. exact (MK_COMB (@lem4430733 A K k x) (@lem4430728 A K k t x)). Qed.
Lemma lem4430735 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term171 A K k t x) = (term169 A K k t x).
Proof. exact (@lem17045 (@EXTENSIONAL K A k x) (term124 A K k t x)). Qed.
Lemma lem4430736 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term171 A K k t x) = (term170 A K k t x).
Proof. exact (TRANS (@lem4430735 A K k t x) (@lem4430734 A K k t x)). Qed.
Lemma lem4430738 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term74 A K k x) = (term74 A K k x).
Proof. exact (eq_refl (term74 A K k x)). Qed.
Lemma lem4430739 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term125 A K k t x) = (term172 A K k t x).
Proof. exact (MK_COMB (@lem4430738 A K k x) (@lem4430731 A K k t x)). Qed.
Lemma lem4430740 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4430741 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term173 A K k s x) = (term174 A K k s x).
Proof. exact (MK_COMB (@lem4430740) (@lem4430699 A K k s x)). Qed.
Lemma lem4430742 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term175 A K s k t x) = (term176 A K s k t x).
Proof. exact (MK_COMB (@lem4430741 A K k s x) (@lem4430736 A K k t x)). Qed.
Lemma lem4430743 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term177 A K s k t x) = (term175 A K s k t x).
Proof. exact (@lem17045 (term125 A K k s x) (term125 A K k t x)). Qed.
Lemma lem4430744 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term177 A K s k t x) = (term176 A K s k t x).
Proof. exact (TRANS (@lem4430743 A K s k t x) (@lem4430742 A K s k t x)). Qed.
Lemma lem4430745 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4430746 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term126 A K k s x) = (term178 A K k s x).
Proof. exact (MK_COMB (@lem4430745) (@lem4430702 A K k s x)). Qed.
Lemma lem4430747 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term127 A K s k t x) = (term179 A K s k t x).
Proof. exact (MK_COMB (@lem4430746 A K k s x) (@lem4430739 A K k t x)). Qed.
Lemma lem4430760 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) : (term180 A K s t x i) = (term181 A K s t x i).
Proof. exact (@lem17045 (term118 A K s x i) (term118 A K t x i)). Qed.
Lemma lem4430765 {K : Type'} (k : K -> Prop) (i : K) : (term182 K k i) = (term182 K k i).
Proof. exact (eq_refl (term182 K k i)). Qed.
Lemma lem4430766 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) : (term183 A K k s t x i) = (term184 A K k s t x i).
Proof. exact (MK_COMB (@lem4430765 K k i) (@lem4430760 A K s t x i)). Qed.
Lemma lem4430767 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) : (term185 A K k s t x i) = (term183 A K k s t x i).
Proof. exact (@lem17362 (k i) (term131 A K s t x i)). Qed.
Lemma lem4430768 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) : (term185 A K k s t x i) = (term184 A K k s t x i).
Proof. exact (TRANS (@lem4430767 A K k s t x i) (@lem4430766 A K k s t x i)). Qed.
Lemma lem4430773 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) : (term132 A K k s t x i) = (term186 A K k s t x i).
Proof. exact (@lem17265 (k i) (term131 A K s t x i)). Qed.
Lemma lem4430774 {K : Type'} (P : K -> Prop) : (term157 K P) = (term158 K P).
Proof. exact (@lem18392 K P). Qed.
Lemma lem4430775 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term187 A K k s t x) = (term188 A K k s t x).
Proof. exact (@lem4430774 K (term133 A K k s t x)). Qed.
Lemma lem4430776 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) : (term189 A K k s t x i) = (term132 A K k s t x i).
Proof. exact (eq_refl (term189 A K k s t x i)). Qed.
Lemma lem4430777 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4430778 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) : (term190 A K k s t x i) = (term185 A K k s t x i).
Proof. exact (MK_COMB (@lem4430777) (@lem4430776 A K k s t x i)). Qed.
Lemma lem4430779 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) : (term190 A K k s t x i) = (term184 A K k s t x i).
Proof. exact (TRANS (@lem4430778 A K k s t x i) (@lem4430768 A K k s t x i)). Qed.
Lemma lem4430780 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term191 A K k s t x) = (term192 A K k s t x).
Proof. exact (fun_ext (fun i : K => @lem4430779 A K k s t x i)). Qed.
Lemma lem4430781 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4430782 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term188 A K k s t x) = (term193 A K k s t x).
Proof. exact (MK_COMB (@lem4430781 K) (@lem4430780 A K k s t x)). Qed.
Lemma lem4430783 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term187 A K k s t x) = (term193 A K k s t x).
Proof. exact (TRANS (@lem4430775 A K k s t x) (@lem4430782 A K k s t x)). Qed.
Lemma lem4430784 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term133 A K k s t x) = (term194 A K k s t x).
Proof. exact (fun_ext (fun i : K => @lem4430773 A K k s t x i)). Qed.
Lemma lem4430785 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4430786 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term134 A K k s t x) = (term195 A K k s t x).
Proof. exact (MK_COMB (@lem4430785 K) (@lem4430784 A K k s t x)). Qed.
Lemma lem4430788 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term168 A K k x) = (term168 A K k x).
Proof. exact (eq_refl (term168 A K k x)). Qed.
Lemma lem4430789 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term196 A K k s t x) = (term197 A K k s t x).
Proof. exact (MK_COMB (@lem4430788 A K k x) (@lem4430783 A K k s t x)). Qed.
Lemma lem4430790 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term198 A K k s t x) = (term196 A K k s t x).
Proof. exact (@lem17045 (@EXTENSIONAL K A k x) (term134 A K k s t x)). Qed.
Lemma lem4430791 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term198 A K k s t x) = (term197 A K k s t x).
Proof. exact (TRANS (@lem4430790 A K k s t x) (@lem4430789 A K k s t x)). Qed.
Lemma lem4430793 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term74 A K k x) = (term74 A K k x).
Proof. exact (eq_refl (term74 A K k x)). Qed.
Lemma lem4430794 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term135 A K k s t x) = (term199 A K k s t x).
Proof. exact (MK_COMB (@lem4430793 A K k x) (@lem4430786 A K k s t x)). Qed.
Lemma lem4430795 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4430796 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term200 A K s k t x) = (term201 A K s k t x).
Proof. exact (MK_COMB (@lem4430795) (@lem4430744 A K s k t x)). Qed.
Lemma lem4430797 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term202 A K k s t x) = (term203 A K k s t x).
Proof. exact (MK_COMB (@lem4430796 A K s k t x) (@lem4430794 A K k s t x)). Qed.
Lemma lem4430798 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4430799 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term204 A K s k t x) = (term205 A K s k t x).
Proof. exact (MK_COMB (@lem4430798) (@lem4430747 A K s k t x)). Qed.
Lemma lem4430800 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term206 A K k s t x) = (term207 A K k s t x).
Proof. exact (MK_COMB (@lem4430799 A K s k t x) (@lem4430791 A K k s t x)). Qed.
Lemma lem4430801 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4430802 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term208 A K k s t x) = (term209 A K k s t x).
Proof. exact (MK_COMB (@lem4430801) (@lem4430800 A K k s t x)). Qed.
Lemma lem4430803 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term210 A K k s t x) = (term211 A K k s t x).
Proof. exact (MK_COMB (@lem4430802 A K k s t x) (@lem4430797 A K k s t x)). Qed.
Lemma lem4430804 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term153 A K k s t x) = (term210 A K k s t x).
Proof. exact (@lem17646 (term127 A K s k t x) (term135 A K k s t x)). Qed.
Lemma lem4430805 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term153 A K k s t x) = (term211 A K k s t x).
Proof. exact (TRANS (@lem4430804 A K k s t x) (@lem4430803 A K k s t x)). Qed.
Lemma lem4431036 {A : Type'} (P : Prop) (Q : A -> Prop) : (term212 A P Q) = (term213 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4431037 {K : Type'} (P : Prop) (Q : K -> Prop) : (term212 K P Q) = (term213 K P Q).
Proof. exact (@lem4431036 K P Q). Qed.
Lemma lem4431038 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term214 A K k s t x) = (term215 A K k s t x).
Proof. exact (@lem4431037 K (term216 A K k x) (term192 A K k s t x)). Qed.
Lemma lem4431039 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) : (term217 A K k s t x i) = (term184 A K k s t x i).
Proof. exact (eq_refl (term217 A K k s t x i)). Qed.
Lemma lem4431040 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term218 A K k s t x) = (term192 A K k s t x).
Proof. exact (fun_ext (fun i : K => @lem4431039 A K k s t x i)). Qed.
Lemma lem4431041 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4431042 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term219 A K k s t x) = (term193 A K k s t x).
Proof. exact (MK_COMB (@lem4431041 K) (@lem4431040 A K k s t x)). Qed.
Lemma lem4431043 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term168 A K k x) = (term168 A K k x).
Proof. exact (eq_refl (term168 A K k x)). Qed.
Lemma lem4431044 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term214 A K k s t x) = (term197 A K k s t x).
Proof. exact (MK_COMB (@lem4431043 A K k x) (@lem4431042 A K k s t x)). Qed.
Lemma lem4431045 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4431046 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term220 A K k s t x) = (term221 A K k s t x).
Proof. exact (MK_COMB (@lem4431045) (@lem4431044 A K k s t x)). Qed.
Lemma lem4431047 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) : (term217 A K k s t x i) = (term184 A K k s t x i).
Proof. exact (eq_refl (term217 A K k s t x i)). Qed.
Lemma lem4431048 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term168 A K k x) = (term168 A K k x).
Proof. exact (eq_refl (term168 A K k x)). Qed.
Lemma lem4431049 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) : (term222 A K k s t x i) = (term223 A K k s t x i).
Proof. exact (MK_COMB (@lem4431048 A K k x) (@lem4431047 A K k s t x i)). Qed.
Lemma lem4431050 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term224 A K k s t x) = (term225 A K k s t x).
Proof. exact (fun_ext (fun i : K => @lem4431049 A K k s t x i)). Qed.
Lemma lem4431051 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4431052 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term215 A K k s t x) = (term226 A K k s t x).
Proof. exact (MK_COMB (@lem4431051 K) (@lem4431050 A K k s t x)). Qed.
Lemma lem4431053 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : ((term214 A K k s t x) = (term215 A K k s t x)) = ((term197 A K k s t x) = (term226 A K k s t x)).
Proof. exact (MK_COMB (@lem4431046 A K k s t x) (@lem4431052 A K k s t x)). Qed.
Lemma lem4431054 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term197 A K k s t x) = (term226 A K k s t x).
Proof. exact (EQ_MP (@lem4431053 A K k s t x) (@lem4431038 A K k s t x)). Qed.
Lemma lem4431055 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term205 A K s k t x) = (term205 A K s k t x).
Proof. exact (eq_refl (term205 A K s k t x)). Qed.
Lemma lem4431056 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term207 A K k s t x) = (term227 A K k s t x).
Proof. exact (MK_COMB (@lem4431055 A K s k t x) (@lem4431054 A K k s t x)). Qed.
Lemma lem4431058 {A : Type'} (P : Prop) (Q : A -> Prop) : (term228 A P Q) = (term229 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4431059 {K : Type'} (P : Prop) (Q : K -> Prop) : (term228 K P Q) = (term229 K P Q).
Proof. exact (@lem4431058 K P Q). Qed.
Lemma lem4431060 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term230 A K k s t x) = (term231 A K k s t x).
Proof. exact (@lem4431059 K (term179 A K s k t x) (term225 A K k s t x)). Qed.
Lemma lem4431061 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) : (term232 A K k s t x i) = (term223 A K k s t x i).
Proof. exact (eq_refl (term232 A K k s t x i)). Qed.
Lemma lem4431062 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term233 A K k s t x) = (term225 A K k s t x).
Proof. exact (fun_ext (fun i : K => @lem4431061 A K k s t x i)). Qed.
Lemma lem4431063 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4431064 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term234 A K k s t x) = (term226 A K k s t x).
Proof. exact (MK_COMB (@lem4431063 K) (@lem4431062 A K k s t x)). Qed.
Lemma lem4431065 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term205 A K s k t x) = (term205 A K s k t x).
Proof. exact (eq_refl (term205 A K s k t x)). Qed.
Lemma lem4431066 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term230 A K k s t x) = (term227 A K k s t x).
Proof. exact (MK_COMB (@lem4431065 A K s k t x) (@lem4431064 A K k s t x)). Qed.
Lemma lem4431067 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4431068 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term235 A K k s t x) = (term236 A K k s t x).
Proof. exact (MK_COMB (@lem4431067) (@lem4431066 A K k s t x)). Qed.
Lemma lem4431069 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) : (term232 A K k s t x i) = (term223 A K k s t x i).
Proof. exact (eq_refl (term232 A K k s t x i)). Qed.
Lemma lem4431070 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term205 A K s k t x) = (term205 A K s k t x).
Proof. exact (eq_refl (term205 A K s k t x)). Qed.
Lemma lem4431071 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) : (term237 A K k s t x i) = (term238 A K k s t x i).
Proof. exact (MK_COMB (@lem4431070 A K s k t x) (@lem4431069 A K k s t x i)). Qed.
Lemma lem4431072 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term239 A K k s t x) = (term240 A K k s t x).
Proof. exact (fun_ext (fun i : K => @lem4431071 A K k s t x i)). Qed.
Lemma lem4431073 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4431074 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term231 A K k s t x) = (term241 A K k s t x).
Proof. exact (MK_COMB (@lem4431073 K) (@lem4431072 A K k s t x)). Qed.
Lemma lem4431075 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : ((term230 A K k s t x) = (term231 A K k s t x)) = ((term227 A K k s t x) = (term241 A K k s t x)).
Proof. exact (MK_COMB (@lem4431068 A K k s t x) (@lem4431074 A K k s t x)). Qed.
Lemma lem4431076 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term227 A K k s t x) = (term241 A K k s t x).
Proof. exact (EQ_MP (@lem4431075 A K k s t x) (@lem4431060 A K k s t x)). Qed.
Lemma lem4431077 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term207 A K k s t x) = (term241 A K k s t x).
Proof. exact (TRANS (@lem4431056 A K k s t x) (@lem4431076 A K k s t x)). Qed.
Lemma lem4431078 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4431079 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term209 A K k s t x) = (term242 A K k s t x).
Proof. exact (MK_COMB (@lem4431078) (@lem4431077 A K k s t x)). Qed.
Lemma lem4431081 {A : Type'} (P : Prop) (Q : A -> Prop) : (term212 A P Q) = (term213 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4431082 {K : Type'} (P : Prop) (Q : K -> Prop) : (term212 K P Q) = (term213 K P Q).
Proof. exact (@lem4431081 K P Q). Qed.
Lemma lem4431083 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term243 A K k s x) = (term244 A K k s x).
Proof. exact (@lem4431082 K (term216 A K k x) (term164 A K k s x)). Qed.
Lemma lem4431084 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (i : K) : (term245 A K k s x i) = (term155 A K k s x i).
Proof. exact (eq_refl (term245 A K k s x i)). Qed.
Lemma lem4431085 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term246 A K k s x) = (term164 A K k s x).
Proof. exact (fun_ext (fun i : K => @lem4431084 A K k s x i)). Qed.
Lemma lem4431086 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4431087 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term247 A K k s x) = (term165 A K k s x).
Proof. exact (MK_COMB (@lem4431086 K) (@lem4431085 A K k s x)). Qed.
Lemma lem4431088 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term168 A K k x) = (term168 A K k x).
Proof. exact (eq_refl (term168 A K k x)). Qed.
Lemma lem4431089 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term243 A K k s x) = (term170 A K k s x).
Proof. exact (MK_COMB (@lem4431088 A K k x) (@lem4431087 A K k s x)). Qed.
Lemma lem4431090 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4431091 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term248 A K k s x) = (term249 A K k s x).
Proof. exact (MK_COMB (@lem4431090) (@lem4431089 A K k s x)). Qed.
Lemma lem4431092 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (i : K) : (term245 A K k s x i) = (term155 A K k s x i).
Proof. exact (eq_refl (term245 A K k s x i)). Qed.
Lemma lem4431093 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term168 A K k x) = (term168 A K k x).
Proof. exact (eq_refl (term168 A K k x)). Qed.
Lemma lem4431094 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (i : K) : (term250 A K k s x i) = (term251 A K k s x i).
Proof. exact (MK_COMB (@lem4431093 A K k x) (@lem4431092 A K k s x i)). Qed.
Lemma lem4431095 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term252 A K k s x) = (term253 A K k s x).
Proof. exact (fun_ext (fun i : K => @lem4431094 A K k s x i)). Qed.
Lemma lem4431096 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4431097 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term244 A K k s x) = (term254 A K k s x).
Proof. exact (MK_COMB (@lem4431096 K) (@lem4431095 A K k s x)). Qed.
Lemma lem4431098 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : ((term243 A K k s x) = (term244 A K k s x)) = ((term170 A K k s x) = (term254 A K k s x)).
Proof. exact (MK_COMB (@lem4431091 A K k s x) (@lem4431097 A K k s x)). Qed.
Lemma lem4431099 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term170 A K k s x) = (term254 A K k s x).
Proof. exact (EQ_MP (@lem4431098 A K k s x) (@lem4431083 A K k s x)). Qed.
Lemma lem4431100 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4431101 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term174 A K k s x) = (term255 A K k s x).
Proof. exact (MK_COMB (@lem4431100) (@lem4431099 A K k s x)). Qed.
Lemma lem4431103 {A : Type'} (P : Prop) (Q : A -> Prop) : (term212 A P Q) = (term213 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4431104 {K : Type'} (P : Prop) (Q : K -> Prop) : (term212 K P Q) = (term213 K P Q).
Proof. exact (@lem4431103 K P Q). Qed.
Lemma lem4431105 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term243 A K k t x) = (term244 A K k t x).
Proof. exact (@lem4431104 K (term216 A K k x) (term164 A K k t x)). Qed.
Lemma lem4431106 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) (i : K) : (term245 A K k t x i) = (term155 A K k t x i).
Proof. exact (eq_refl (term245 A K k t x i)). Qed.
Lemma lem4431107 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term246 A K k t x) = (term164 A K k t x).
Proof. exact (fun_ext (fun i : K => @lem4431106 A K k t x i)). Qed.
Lemma lem4431108 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4431109 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term247 A K k t x) = (term165 A K k t x).
Proof. exact (MK_COMB (@lem4431108 K) (@lem4431107 A K k t x)). Qed.
Lemma lem4431110 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term168 A K k x) = (term168 A K k x).
Proof. exact (eq_refl (term168 A K k x)). Qed.
Lemma lem4431111 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term243 A K k t x) = (term170 A K k t x).
Proof. exact (MK_COMB (@lem4431110 A K k x) (@lem4431109 A K k t x)). Qed.
Lemma lem4431112 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4431113 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term248 A K k t x) = (term249 A K k t x).
Proof. exact (MK_COMB (@lem4431112) (@lem4431111 A K k t x)). Qed.
Lemma lem4431114 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) (i : K) : (term245 A K k t x i) = (term155 A K k t x i).
Proof. exact (eq_refl (term245 A K k t x i)). Qed.
Lemma lem4431115 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term168 A K k x) = (term168 A K k x).
Proof. exact (eq_refl (term168 A K k x)). Qed.
Lemma lem4431116 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) (i : K) : (term250 A K k t x i) = (term251 A K k t x i).
Proof. exact (MK_COMB (@lem4431115 A K k x) (@lem4431114 A K k t x i)). Qed.
Lemma lem4431117 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term252 A K k t x) = (term253 A K k t x).
Proof. exact (fun_ext (fun i : K => @lem4431116 A K k t x i)). Qed.
Lemma lem4431118 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4431119 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term244 A K k t x) = (term254 A K k t x).
Proof. exact (MK_COMB (@lem4431118 K) (@lem4431117 A K k t x)). Qed.
Lemma lem4431120 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : ((term243 A K k t x) = (term244 A K k t x)) = ((term170 A K k t x) = (term254 A K k t x)).
Proof. exact (MK_COMB (@lem4431113 A K k t x) (@lem4431119 A K k t x)). Qed.
Lemma lem4431121 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term170 A K k t x) = (term254 A K k t x).
Proof. exact (EQ_MP (@lem4431120 A K k t x) (@lem4431105 A K k t x)). Qed.
Lemma lem4431122 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term176 A K s k t x) = (term256 A K s k t x).
Proof. exact (MK_COMB (@lem4431101 A K k s x) (@lem4431121 A K k t x)). Qed.
Lemma lem4431124 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term257 A P Q) = (term258 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4431125 {K : Type'} (P : K -> Prop) (Q : K -> Prop) : (term257 K P Q) = (term258 K P Q).
Proof. exact (@lem4431124 K P Q). Qed.
Lemma lem4431126 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term259 A K s k t x) = (term260 A K s k t x).
Proof. exact (@lem4431125 K (term253 A K k s x) (term253 A K k t x)). Qed.
Lemma lem4431127 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (i : K) : (term261 A K k s x i) = (term251 A K k s x i).
Proof. exact (eq_refl (term261 A K k s x i)). Qed.
Lemma lem4431128 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term262 A K k s x) = (term253 A K k s x).
Proof. exact (fun_ext (fun i : K => @lem4431127 A K k s x i)). Qed.
Lemma lem4431129 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4431130 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term263 A K k s x) = (term254 A K k s x).
Proof. exact (MK_COMB (@lem4431129 K) (@lem4431128 A K k s x)). Qed.
Lemma lem4431131 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4431132 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term264 A K k s x) = (term255 A K k s x).
Proof. exact (MK_COMB (@lem4431131) (@lem4431130 A K k s x)). Qed.
Lemma lem4431133 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) (i : K) : (term261 A K k t x i) = (term251 A K k t x i).
Proof. exact (eq_refl (term261 A K k t x i)). Qed.
Lemma lem4431134 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term262 A K k t x) = (term253 A K k t x).
Proof. exact (fun_ext (fun i : K => @lem4431133 A K k t x i)). Qed.
Lemma lem4431135 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4431136 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term263 A K k t x) = (term254 A K k t x).
Proof. exact (MK_COMB (@lem4431135 K) (@lem4431134 A K k t x)). Qed.
Lemma lem4431137 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term259 A K s k t x) = (term256 A K s k t x).
Proof. exact (MK_COMB (@lem4431132 A K k s x) (@lem4431136 A K k t x)). Qed.
Lemma lem4431138 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4431139 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term265 A K s k t x) = (term266 A K s k t x).
Proof. exact (MK_COMB (@lem4431138) (@lem4431137 A K s k t x)). Qed.
Lemma lem4431140 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (i : K) : (term261 A K k s x i) = (term251 A K k s x i).
Proof. exact (eq_refl (term261 A K k s x i)). Qed.
Lemma lem4431141 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4431142 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (i : K) : (term267 A K k s x i) = (term268 A K k s x i).
Proof. exact (MK_COMB (@lem4431141) (@lem4431140 A K k s x i)). Qed.
Lemma lem4431143 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) (i : K) : (term261 A K k t x i) = (term251 A K k t x i).
Proof. exact (eq_refl (term261 A K k t x i)). Qed.
Lemma lem4431144 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : K -> A) (i : K) : (term269 A K s k t x i) = (term270 A K s k t x i).
Proof. exact (MK_COMB (@lem4431142 A K k s x i) (@lem4431143 A K k t x i)). Qed.
Lemma lem4431145 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term271 A K s k t x) = (term272 A K s k t x).
Proof. exact (fun_ext (fun i : K => @lem4431144 A K s k t x i)). Qed.
Lemma lem4431146 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4431147 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term260 A K s k t x) = (term273 A K s k t x).
Proof. exact (MK_COMB (@lem4431146 K) (@lem4431145 A K s k t x)). Qed.
Lemma lem4431148 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : K -> A) : ((term259 A K s k t x) = (term260 A K s k t x)) = ((term256 A K s k t x) = (term273 A K s k t x)).
Proof. exact (MK_COMB (@lem4431139 A K s k t x) (@lem4431147 A K s k t x)). Qed.
Lemma lem4431149 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term256 A K s k t x) = (term273 A K s k t x).
Proof. exact (EQ_MP (@lem4431148 A K s k t x) (@lem4431126 A K s k t x)). Qed.
Lemma lem4431150 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term176 A K s k t x) = (term273 A K s k t x).
Proof. exact (TRANS (@lem4431122 A K s k t x) (@lem4431149 A K s k t x)). Qed.
Lemma lem4431151 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4431152 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term201 A K s k t x) = (term274 A K s k t x).
Proof. exact (MK_COMB (@lem4431151) (@lem4431150 A K s k t x)). Qed.
Lemma lem4431153 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term199 A K k s t x) = (term199 A K k s t x).
Proof. exact (eq_refl (term199 A K k s t x)). Qed.
Lemma lem4431154 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term203 A K k s t x) = (term275 A K k s t x).
Proof. exact (MK_COMB (@lem4431152 A K s k t x) (@lem4431153 A K k s t x)). Qed.
Lemma lem4431156 {A : Type'} (P : A -> Prop) (Q : Prop) : (term276 A P Q) = (term277 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4431157 {K : Type'} (P : K -> Prop) (Q : Prop) : (term276 K P Q) = (term277 K P Q).
Proof. exact (@lem4431156 K P Q). Qed.
Lemma lem4431158 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term278 A K k s t x) = (term279 A K k s t x).
Proof. exact (@lem4431157 K (term272 A K s k t x) (term199 A K k s t x)). Qed.
Lemma lem4431159 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : K -> A) (i : K) : (term280 A K s k t x i) = (term270 A K s k t x i).
Proof. exact (eq_refl (term280 A K s k t x i)). Qed.
Lemma lem4431160 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term281 A K s k t x) = (term272 A K s k t x).
Proof. exact (fun_ext (fun i : K => @lem4431159 A K s k t x i)). Qed.
Lemma lem4431161 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4431162 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term282 A K s k t x) = (term273 A K s k t x).
Proof. exact (MK_COMB (@lem4431161 K) (@lem4431160 A K s k t x)). Qed.
Lemma lem4431163 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4431164 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term283 A K s k t x) = (term274 A K s k t x).
Proof. exact (MK_COMB (@lem4431163) (@lem4431162 A K s k t x)). Qed.
Lemma lem4431165 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term199 A K k s t x) = (term199 A K k s t x).
Proof. exact (eq_refl (term199 A K k s t x)). Qed.
Lemma lem4431166 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term278 A K k s t x) = (term275 A K k s t x).
Proof. exact (MK_COMB (@lem4431164 A K s k t x) (@lem4431165 A K k s t x)). Qed.
Lemma lem4431167 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4431168 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term284 A K k s t x) = (term285 A K k s t x).
Proof. exact (MK_COMB (@lem4431167) (@lem4431166 A K k s t x)). Qed.
Lemma lem4431169 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : K -> A) (i : K) : (term280 A K s k t x i) = (term270 A K s k t x i).
Proof. exact (eq_refl (term280 A K s k t x i)). Qed.
Lemma lem4431170 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4431171 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : K -> A) (i : K) : (term286 A K s k t x i) = (term287 A K s k t x i).
Proof. exact (MK_COMB (@lem4431170) (@lem4431169 A K s k t x i)). Qed.
Lemma lem4431172 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term199 A K k s t x) = (term199 A K k s t x).
Proof. exact (eq_refl (term199 A K k s t x)). Qed.
Lemma lem4431173 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term288 A K i k s t x) = (term289 A K i k s t x).
Proof. exact (MK_COMB (@lem4431171 A K s k t x i) (@lem4431172 A K k s t x)). Qed.
Lemma lem4431174 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term290 A K k s t x) = (term291 A K k s t x).
Proof. exact (fun_ext (fun i : K => @lem4431173 A K i k s t x)). Qed.
Lemma lem4431175 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4431176 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term279 A K k s t x) = (term292 A K k s t x).
Proof. exact (MK_COMB (@lem4431175 K) (@lem4431174 A K k s t x)). Qed.
Lemma lem4431177 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : ((term278 A K k s t x) = (term279 A K k s t x)) = ((term275 A K k s t x) = (term292 A K k s t x)).
Proof. exact (MK_COMB (@lem4431168 A K k s t x) (@lem4431176 A K k s t x)). Qed.
Lemma lem4431178 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term275 A K k s t x) = (term292 A K k s t x).
Proof. exact (EQ_MP (@lem4431177 A K k s t x) (@lem4431158 A K k s t x)). Qed.
Lemma lem4431179 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term203 A K k s t x) = (term292 A K k s t x).
Proof. exact (TRANS (@lem4431154 A K k s t x) (@lem4431178 A K k s t x)). Qed.
Lemma lem4431180 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term211 A K k s t x) = (term293 A K k s t x).
Proof. exact (MK_COMB (@lem4431079 A K k s t x) (@lem4431179 A K k s t x)). Qed.
Lemma lem4431182 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term257 A P Q) = (term258 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4431183 {K : Type'} (P : K -> Prop) (Q : K -> Prop) : (term257 K P Q) = (term258 K P Q).
Proof. exact (@lem4431182 K P Q). Qed.
Lemma lem4431184 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term294 A K k s t x) = (term295 A K k s t x).
Proof. exact (@lem4431183 K (term240 A K k s t x) (term291 A K k s t x)). Qed.
Lemma lem4431185 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) : (term296 A K k s t x i) = (term238 A K k s t x i).
Proof. exact (eq_refl (term296 A K k s t x i)). Qed.
Lemma lem4431186 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term297 A K k s t x) = (term240 A K k s t x).
Proof. exact (fun_ext (fun i : K => @lem4431185 A K k s t x i)). Qed.
Lemma lem4431187 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4431188 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term298 A K k s t x) = (term241 A K k s t x).
Proof. exact (MK_COMB (@lem4431187 K) (@lem4431186 A K k s t x)). Qed.
Lemma lem4431189 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4431190 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term299 A K k s t x) = (term242 A K k s t x).
Proof. exact (MK_COMB (@lem4431189) (@lem4431188 A K k s t x)). Qed.
Lemma lem4431191 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term300 A K k s t x i) = (term289 A K i k s t x).
Proof. exact (eq_refl (term300 A K k s t x i)). Qed.
Lemma lem4431192 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term301 A K k s t x) = (term291 A K k s t x).
Proof. exact (fun_ext (fun i : K => @lem4431191 A K i k s t x)). Qed.
Lemma lem4431193 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4431194 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term302 A K k s t x) = (term292 A K k s t x).
Proof. exact (MK_COMB (@lem4431193 K) (@lem4431192 A K k s t x)). Qed.
Lemma lem4431195 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term294 A K k s t x) = (term293 A K k s t x).
Proof. exact (MK_COMB (@lem4431190 A K k s t x) (@lem4431194 A K k s t x)). Qed.
Lemma lem4431196 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4431197 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term303 A K k s t x) = (term304 A K k s t x).
Proof. exact (MK_COMB (@lem4431196) (@lem4431195 A K k s t x)). Qed.
Lemma lem4431198 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) : (term296 A K k s t x i) = (term238 A K k s t x i).
Proof. exact (eq_refl (term296 A K k s t x i)). Qed.
Lemma lem4431199 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4431200 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) : (term305 A K k s t x i) = (term306 A K k s t x i).
Proof. exact (MK_COMB (@lem4431199) (@lem4431198 A K k s t x i)). Qed.
Lemma lem4431201 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term300 A K k s t x i) = (term289 A K i k s t x).
Proof. exact (eq_refl (term300 A K k s t x i)). Qed.
Lemma lem4431202 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term307 A K k s t x i) = (term308 A K i k s t x).
Proof. exact (MK_COMB (@lem4431200 A K k s t x i) (@lem4431201 A K i k s t x)). Qed.
Lemma lem4431203 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term309 A K k s t x) = (term310 A K k s t x).
Proof. exact (fun_ext (fun i : K => @lem4431202 A K i k s t x)). Qed.
Lemma lem4431204 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4431205 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term295 A K k s t x) = (term311 A K k s t x).
Proof. exact (MK_COMB (@lem4431204 K) (@lem4431203 A K k s t x)). Qed.
Lemma lem4431206 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : ((term294 A K k s t x) = (term295 A K k s t x)) = ((term293 A K k s t x) = (term311 A K k s t x)).
Proof. exact (MK_COMB (@lem4431197 A K k s t x) (@lem4431205 A K k s t x)). Qed.
Lemma lem4431207 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term293 A K k s t x) = (term311 A K k s t x).
Proof. exact (EQ_MP (@lem4431206 A K k s t x) (@lem4431184 A K k s t x)). Qed.
Lemma lem4431209 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term211 A K k s t x) = (term311 A K k s t x).
Proof. exact (TRANS (@lem4431180 A K k s t x) (@lem4431207 A K k s t x)). Qed.
Lemma lem4431210 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term153 A K k s t x) = (term311 A K k s t x).
Proof. exact (TRANS (@lem4430805 A K k s t x) (@lem4431209 A K k s t x)). Qed.
Lemma lem4431211 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term153 A K k s t x) : term311 A K k s t x.
Proof. exact (EQ_MP (@lem4431210 A K k s t x) (@lem4430665 A K k s t x h1)). Qed.
Lemma lem4431212 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term308 A K i k s t x) : term308 A K i k s t x.
Proof. exact (h1). Qed.
Lemma lem4431219 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4431220 {A K : Type'} (f : K -> A) (x : K) : (f x) = (@I (K -> A) f x).
Proof. exact (@lem4431219 K A f x). Qed.
Lemma lem4431222 {A K : Type'} (x : K -> A) (i : K) : (x i) = (@I (K -> A) x i).
Proof. exact (@lem4431220 A K x i). Qed.
Lemma lem4431223 {A K : Type'} (t : type1470 A K) (i : K) : (t i) = (t i).
Proof. exact (eq_refl (t i)). Qed.
Lemma lem4431224 {A K : Type'} (t : type1470 A K) (x : K -> A) (i : K) : (term118 A K t x i) = (term312 A K t x i).
Proof. exact (MK_COMB (@lem4431223 A K t i) (@lem4431222 A K x i)). Qed.
Lemma lem4431231 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4431232 {A K : Type'} (f : K -> A) (x : K) : (f x) = (@I (K -> A) f x).
Proof. exact (@lem4431231 K A f x). Qed.
Lemma lem4431234 {A K : Type'} (x : K -> A) (i : K) : (x i) = (@I (K -> A) x i).
Proof. exact (@lem4431232 A K x i). Qed.
Lemma lem4431235 {A K : Type'} (s : type1470 A K) (i : K) : (s i) = (s i).
Proof. exact (eq_refl (s i)). Qed.
Lemma lem4431236 {A K : Type'} (s : type1470 A K) (x : K -> A) (i : K) : (term118 A K s x i) = (term312 A K s x i).
Proof. exact (MK_COMB (@lem4431235 A K s i) (@lem4431234 A K x i)). Qed.
Lemma lem4431237 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4431238 {A K : Type'} (s : type1470 A K) (x : K -> A) (i : K) : (term130 A K s x i) = (term313 A K s x i).
Proof. exact (MK_COMB (@lem4431237) (@lem4431236 A K s x i)). Qed.
Lemma lem4431239 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) : (term131 A K s t x i) = (term314 A K s t x i).
Proof. exact (MK_COMB (@lem4431238 A K s x i) (@lem4431224 A K t x i)). Qed.
Lemma lem4431240 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4431245 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4431246 {K : Type'} (f : K -> Prop) (x : K) : (f x) = (@I (K -> Prop) f x).
Proof. exact (@lem4431245 K Prop f x). Qed.
Lemma lem4431248 {K : Type'} (k : K -> Prop) (i : K) : (k i) = (@I (K -> Prop) k i).
Proof. exact (@lem4431246 K k i). Qed.
Lemma lem4431249 {K : Type'} (k : K -> Prop) (i : K) : (term315 K k i) = (term316 K k i).
Proof. exact (MK_COMB (@lem4431240) (@lem4431248 K k i)). Qed.
Lemma lem4431250 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4431251 {K : Type'} (k : K -> Prop) (i : K) : (term317 K k i) = (term318 K k i).
Proof. exact (MK_COMB (@lem4431250) (@lem4431249 K k i)). Qed.
Lemma lem4431252 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) : (term186 A K k s t x i) = (term319 A K k s t x i).
Proof. exact (MK_COMB (@lem4431251 K k i) (@lem4431239 A K s t x i)). Qed.
Lemma lem4431253 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term194 A K k s t x) = (term320 A K k s t x).
Proof. exact (fun_ext (fun i : K => @lem4431252 A K k s t x i)). Qed.
Lemma lem4431254 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4431255 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term195 A K k s t x) = (term321 A K k s t x).
Proof. exact (MK_COMB (@lem4431254 K) (@lem4431253 A K k s t x)). Qed.
Lemma lem4431262 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term74 A K k x) = (term74 A K k x).
Proof. exact (eq_refl (term74 A K k x)). Qed.
Lemma lem4431263 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term199 A K k s t x) = (term322 A K k s t x).
Proof. exact (MK_COMB (@lem4431262 A K k x) (@lem4431255 A K k s t x)). Qed.
Lemma lem4431264 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4431271 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4431272 {A K : Type'} (f : K -> A) (x : K) : (f x) = (@I (K -> A) f x).
Proof. exact (@lem4431271 K A f x). Qed.
Lemma lem4431274 {A K : Type'} (x : K -> A) (i : K) : (x i) = (@I (K -> A) x i).
Proof. exact (@lem4431272 A K x i). Qed.
Lemma lem4431275 {A K : Type'} (t : type1470 A K) (i : K) : (t i) = (t i).
Proof. exact (eq_refl (t i)). Qed.
Lemma lem4431276 {A K : Type'} (t : type1470 A K) (x : K -> A) (i : K) : (term118 A K t x i) = (term312 A K t x i).
Proof. exact (MK_COMB (@lem4431275 A K t i) (@lem4431274 A K x i)). Qed.
Lemma lem4431277 {A K : Type'} (t : type1470 A K) (x : K -> A) (i : K) : (term323 A K t x i) = (term324 A K t x i).
Proof. exact (MK_COMB (@lem4431264) (@lem4431276 A K t x i)). Qed.
Lemma lem4431282 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4431283 {K : Type'} (f : K -> Prop) (x : K) : (f x) = (@I (K -> Prop) f x).
Proof. exact (@lem4431282 K Prop f x). Qed.
Lemma lem4431285 {K : Type'} (k : K -> Prop) (i : K) : (k i) = (@I (K -> Prop) k i).
Proof. exact (@lem4431283 K k i). Qed.
Lemma lem4431286 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4431287 {K : Type'} (k : K -> Prop) (i : K) : (term182 K k i) = (term325 K k i).
Proof. exact (MK_COMB (@lem4431286) (@lem4431285 K k i)). Qed.
Lemma lem4431288 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) (i : K) : (term155 A K k t x i) = (term326 A K k t x i).
Proof. exact (MK_COMB (@lem4431287 K k i) (@lem4431277 A K t x i)). Qed.
Lemma lem4431297 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term168 A K k x) = (term168 A K k x).
Proof. exact (eq_refl (term168 A K k x)). Qed.
Lemma lem4431298 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) (i : K) : (term251 A K k t x i) = (term327 A K k t x i).
Proof. exact (MK_COMB (@lem4431297 A K k x) (@lem4431288 A K k t x i)). Qed.
Lemma lem4431299 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4431306 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4431307 {A K : Type'} (f : K -> A) (x : K) : (f x) = (@I (K -> A) f x).
Proof. exact (@lem4431306 K A f x). Qed.
Lemma lem4431309 {A K : Type'} (x : K -> A) (i : K) : (x i) = (@I (K -> A) x i).
Proof. exact (@lem4431307 A K x i). Qed.
Lemma lem4431310 {A K : Type'} (s : type1470 A K) (i : K) : (s i) = (s i).
Proof. exact (eq_refl (s i)). Qed.
Lemma lem4431311 {A K : Type'} (s : type1470 A K) (x : K -> A) (i : K) : (term118 A K s x i) = (term312 A K s x i).
Proof. exact (MK_COMB (@lem4431310 A K s i) (@lem4431309 A K x i)). Qed.
Lemma lem4431312 {A K : Type'} (s : type1470 A K) (x : K -> A) (i : K) : (term323 A K s x i) = (term324 A K s x i).
Proof. exact (MK_COMB (@lem4431299) (@lem4431311 A K s x i)). Qed.
Lemma lem4431317 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4431318 {K : Type'} (f : K -> Prop) (x : K) : (f x) = (@I (K -> Prop) f x).
Proof. exact (@lem4431317 K Prop f x). Qed.
Lemma lem4431320 {K : Type'} (k : K -> Prop) (i : K) : (k i) = (@I (K -> Prop) k i).
Proof. exact (@lem4431318 K k i). Qed.
Lemma lem4431321 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4431322 {K : Type'} (k : K -> Prop) (i : K) : (term182 K k i) = (term325 K k i).
Proof. exact (MK_COMB (@lem4431321) (@lem4431320 K k i)). Qed.
Lemma lem4431323 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (i : K) : (term155 A K k s x i) = (term326 A K k s x i).
Proof. exact (MK_COMB (@lem4431322 K k i) (@lem4431312 A K s x i)). Qed.
Lemma lem4431332 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term168 A K k x) = (term168 A K k x).
Proof. exact (eq_refl (term168 A K k x)). Qed.
Lemma lem4431333 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (i : K) : (term251 A K k s x i) = (term327 A K k s x i).
Proof. exact (MK_COMB (@lem4431332 A K k x) (@lem4431323 A K k s x i)). Qed.
Lemma lem4431334 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4431335 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (i : K) : (term268 A K k s x i) = (term328 A K k s x i).
Proof. exact (MK_COMB (@lem4431334) (@lem4431333 A K k s x i)). Qed.
Lemma lem4431336 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : K -> A) (i : K) : (term270 A K s k t x i) = (term329 A K s k t x i).
Proof. exact (MK_COMB (@lem4431335 A K k s x i) (@lem4431298 A K k t x i)). Qed.
Lemma lem4431337 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4431338 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : K -> A) (i : K) : (term287 A K s k t x i) = (term330 A K s k t x i).
Proof. exact (MK_COMB (@lem4431337) (@lem4431336 A K s k t x i)). Qed.
Lemma lem4431339 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term289 A K i k s t x) = (term331 A K i k s t x).
Proof. exact (MK_COMB (@lem4431338 A K s k t x i) (@lem4431263 A K k s t x)). Qed.
Lemma lem4431340 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4431347 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4431348 {A K : Type'} (f : K -> A) (x : K) : (f x) = (@I (K -> A) f x).
Proof. exact (@lem4431347 K A f x). Qed.
Lemma lem4431350 {A K : Type'} (x : K -> A) (i : K) : (x i) = (@I (K -> A) x i).
Proof. exact (@lem4431348 A K x i). Qed.
Lemma lem4431351 {A K : Type'} (t : type1470 A K) (i : K) : (t i) = (t i).
Proof. exact (eq_refl (t i)). Qed.
Lemma lem4431352 {A K : Type'} (t : type1470 A K) (x : K -> A) (i : K) : (term118 A K t x i) = (term312 A K t x i).
Proof. exact (MK_COMB (@lem4431351 A K t i) (@lem4431350 A K x i)). Qed.
Lemma lem4431353 {A K : Type'} (t : type1470 A K) (x : K -> A) (i : K) : (term323 A K t x i) = (term324 A K t x i).
Proof. exact (MK_COMB (@lem4431340) (@lem4431352 A K t x i)). Qed.
Lemma lem4431354 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4431361 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4431362 {A K : Type'} (f : K -> A) (x : K) : (f x) = (@I (K -> A) f x).
Proof. exact (@lem4431361 K A f x). Qed.
Lemma lem4431364 {A K : Type'} (x : K -> A) (i : K) : (x i) = (@I (K -> A) x i).
Proof. exact (@lem4431362 A K x i). Qed.
Lemma lem4431365 {A K : Type'} (s : type1470 A K) (i : K) : (s i) = (s i).
Proof. exact (eq_refl (s i)). Qed.
Lemma lem4431366 {A K : Type'} (s : type1470 A K) (x : K -> A) (i : K) : (term118 A K s x i) = (term312 A K s x i).
Proof. exact (MK_COMB (@lem4431365 A K s i) (@lem4431364 A K x i)). Qed.
Lemma lem4431367 {A K : Type'} (s : type1470 A K) (x : K -> A) (i : K) : (term323 A K s x i) = (term324 A K s x i).
Proof. exact (MK_COMB (@lem4431354) (@lem4431366 A K s x i)). Qed.
Lemma lem4431368 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4431369 {A K : Type'} (s : type1470 A K) (x : K -> A) (i : K) : (term332 A K s x i) = (term333 A K s x i).
Proof. exact (MK_COMB (@lem4431368) (@lem4431367 A K s x i)). Qed.
Lemma lem4431370 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) : (term181 A K s t x i) = (term334 A K s t x i).
Proof. exact (MK_COMB (@lem4431369 A K s x i) (@lem4431353 A K t x i)). Qed.
Lemma lem4431375 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4431376 {K : Type'} (f : K -> Prop) (x : K) : (f x) = (@I (K -> Prop) f x).
Proof. exact (@lem4431375 K Prop f x). Qed.
Lemma lem4431378 {K : Type'} (k : K -> Prop) (i : K) : (k i) = (@I (K -> Prop) k i).
Proof. exact (@lem4431376 K k i). Qed.
Lemma lem4431379 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4431380 {K : Type'} (k : K -> Prop) (i : K) : (term182 K k i) = (term325 K k i).
Proof. exact (MK_COMB (@lem4431379) (@lem4431378 K k i)). Qed.
Lemma lem4431381 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) : (term184 A K k s t x i) = (term335 A K k s t x i).
Proof. exact (MK_COMB (@lem4431380 K k i) (@lem4431370 A K s t x i)). Qed.
Lemma lem4431390 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term168 A K k x) = (term168 A K k x).
Proof. exact (eq_refl (term168 A K k x)). Qed.
Lemma lem4431391 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) : (term223 A K k s t x i) = (term336 A K k s t x i).
Proof. exact (MK_COMB (@lem4431390 A K k x) (@lem4431381 A K k s t x i)). Qed.
Lemma lem4431398 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4431399 {A K : Type'} (f : K -> A) (x : K) : (f x) = (@I (K -> A) f x).
Proof. exact (@lem4431398 K A f x). Qed.
Lemma lem4431401 {A K : Type'} (x : K -> A) (i : K) : (x i) = (@I (K -> A) x i).
Proof. exact (@lem4431399 A K x i). Qed.
Lemma lem4431402 {A K : Type'} (t : type1470 A K) (i : K) : (t i) = (t i).
Proof. exact (eq_refl (t i)). Qed.
Lemma lem4431403 {A K : Type'} (t : type1470 A K) (x : K -> A) (i : K) : (term118 A K t x i) = (term312 A K t x i).
Proof. exact (MK_COMB (@lem4431402 A K t i) (@lem4431401 A K x i)). Qed.
Lemma lem4431404 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4431409 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4431410 {K : Type'} (f : K -> Prop) (x : K) : (f x) = (@I (K -> Prop) f x).
Proof. exact (@lem4431409 K Prop f x). Qed.
Lemma lem4431412 {K : Type'} (k : K -> Prop) (i : K) : (k i) = (@I (K -> Prop) k i).
Proof. exact (@lem4431410 K k i). Qed.
Lemma lem4431413 {K : Type'} (k : K -> Prop) (i : K) : (term315 K k i) = (term316 K k i).
Proof. exact (MK_COMB (@lem4431404) (@lem4431412 K k i)). Qed.
Lemma lem4431414 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4431415 {K : Type'} (k : K -> Prop) (i : K) : (term317 K k i) = (term318 K k i).
Proof. exact (MK_COMB (@lem4431414) (@lem4431413 K k i)). Qed.
Lemma lem4431416 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) (i : K) : (term156 A K k t x i) = (term337 A K k t x i).
Proof. exact (MK_COMB (@lem4431415 K k i) (@lem4431403 A K t x i)). Qed.
Lemma lem4431417 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term166 A K k t x) = (term338 A K k t x).
Proof. exact (fun_ext (fun i : K => @lem4431416 A K k t x i)). Qed.
Lemma lem4431418 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4431419 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term167 A K k t x) = (term339 A K k t x).
Proof. exact (MK_COMB (@lem4431418 K) (@lem4431417 A K k t x)). Qed.
Lemma lem4431426 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term74 A K k x) = (term74 A K k x).
Proof. exact (eq_refl (term74 A K k x)). Qed.
Lemma lem4431427 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term172 A K k t x) = (term340 A K k t x).
Proof. exact (MK_COMB (@lem4431426 A K k x) (@lem4431419 A K k t x)). Qed.
Lemma lem4431434 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4431435 {A K : Type'} (f : K -> A) (x : K) : (f x) = (@I (K -> A) f x).
Proof. exact (@lem4431434 K A f x). Qed.
Lemma lem4431437 {A K : Type'} (x : K -> A) (i : K) : (x i) = (@I (K -> A) x i).
Proof. exact (@lem4431435 A K x i). Qed.
Lemma lem4431438 {A K : Type'} (s : type1470 A K) (i : K) : (s i) = (s i).
Proof. exact (eq_refl (s i)). Qed.
Lemma lem4431439 {A K : Type'} (s : type1470 A K) (x : K -> A) (i : K) : (term118 A K s x i) = (term312 A K s x i).
Proof. exact (MK_COMB (@lem4431438 A K s i) (@lem4431437 A K x i)). Qed.
Lemma lem4431440 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4431445 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4431446 {K : Type'} (f : K -> Prop) (x : K) : (f x) = (@I (K -> Prop) f x).
Proof. exact (@lem4431445 K Prop f x). Qed.
Lemma lem4431448 {K : Type'} (k : K -> Prop) (i : K) : (k i) = (@I (K -> Prop) k i).
Proof. exact (@lem4431446 K k i). Qed.
Lemma lem4431449 {K : Type'} (k : K -> Prop) (i : K) : (term315 K k i) = (term316 K k i).
Proof. exact (MK_COMB (@lem4431440) (@lem4431448 K k i)). Qed.
Lemma lem4431450 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4431451 {K : Type'} (k : K -> Prop) (i : K) : (term317 K k i) = (term318 K k i).
Proof. exact (MK_COMB (@lem4431450) (@lem4431449 K k i)). Qed.
Lemma lem4431452 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (i : K) : (term156 A K k s x i) = (term337 A K k s x i).
Proof. exact (MK_COMB (@lem4431451 K k i) (@lem4431439 A K s x i)). Qed.
Lemma lem4431453 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term166 A K k s x) = (term338 A K k s x).
Proof. exact (fun_ext (fun i : K => @lem4431452 A K k s x i)). Qed.
Lemma lem4431454 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4431455 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term167 A K k s x) = (term339 A K k s x).
Proof. exact (MK_COMB (@lem4431454 K) (@lem4431453 A K k s x)). Qed.
Lemma lem4431462 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term74 A K k x) = (term74 A K k x).
Proof. exact (eq_refl (term74 A K k x)). Qed.
Lemma lem4431463 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term172 A K k s x) = (term340 A K k s x).
Proof. exact (MK_COMB (@lem4431462 A K k x) (@lem4431455 A K k s x)). Qed.
Lemma lem4431464 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4431465 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term178 A K k s x) = (term341 A K k s x).
Proof. exact (MK_COMB (@lem4431464) (@lem4431463 A K k s x)). Qed.
Lemma lem4431466 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term179 A K s k t x) = (term342 A K s k t x).
Proof. exact (MK_COMB (@lem4431465 A K k s x) (@lem4431427 A K k t x)). Qed.
Lemma lem4431467 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4431468 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term205 A K s k t x) = (term343 A K s k t x).
Proof. exact (MK_COMB (@lem4431467) (@lem4431466 A K s k t x)). Qed.
Lemma lem4431469 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) : (term238 A K k s t x i) = (term344 A K k s t x i).
Proof. exact (MK_COMB (@lem4431468 A K s k t x) (@lem4431391 A K k s t x i)). Qed.
Lemma lem4431470 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4431471 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) : (term306 A K k s t x i) = (term345 A K k s t x i).
Proof. exact (MK_COMB (@lem4431470) (@lem4431469 A K k s t x i)). Qed.
Lemma lem4431472 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term308 A K i k s t x) = (term346 A K i k s t x).
Proof. exact (MK_COMB (@lem4431471 A K k s t x i) (@lem4431339 A K i k s t x)). Qed.
Lemma lem4431473 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term308 A K i k s t x) : term346 A K i k s t x.
Proof. exact (EQ_MP (@lem4431472 A K i k s t x) (@lem4431212 A K i k s t x h1)). Qed.
Lemma lem4431474 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term344 A K k s t x i) : term344 A K k s t x i.
Proof. exact (h1). Qed.
Lemma lem4431475 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term331 A K i k s t x) : term331 A K i k s t x.
Proof. exact (h1). Qed.
Lemma lem4431476 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term344 A K k s t x i) : term336 A K k s t x i.
Proof. exact (proj2 (@lem4431474 A K k s t x i h1)). Qed.
Lemma lem4431477 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term344 A K k s t x i) : term342 A K s k t x.
Proof. exact (proj1 (@lem4431474 A K k s t x i h1)). Qed.
Lemma lem4431478 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term344 A K k s t x i) : term340 A K k t x.
Proof. exact (proj2 (@lem4431477 A K k s t x i h1)). Qed.
Lemma lem4431479 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term344 A K k s t x i) : term340 A K k s x.
Proof. exact (proj1 (@lem4431477 A K k s t x i h1)). Qed.
Lemma lem4431480 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term344 A K k s t x i) : term339 A K k t x.
Proof. exact (proj2 (@lem4431478 A K k s t x i h1)). Qed.
Lemma lem4431482 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term344 A K k s t x i) : term339 A K k s x.
Proof. exact (proj2 (@lem4431479 A K k s t x i h1)). Qed.
Lemma lem4431485 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term335 A K k s t x i) : term335 A K k s t x i.
Proof. exact (h1). Qed.
Lemma lem4431486 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term335 A K k s t x i) : term334 A K s t x i.
Proof. exact (proj2 (@lem4431485 A K k s t x i h1)). Qed.
Lemma lem4431490 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term331 A K i k s t x) : term322 A K k s t x.
Proof. exact (proj2 (@lem4431475 A K i k s t x h1)). Qed.
Lemma lem4431491 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term331 A K i k s t x) : term329 A K s k t x i.
Proof. exact (proj1 (@lem4431475 A K i k s t x h1)). Qed.
Lemma lem4431492 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term331 A K i k s t x) : term321 A K k s t x.
Proof. exact (proj2 (@lem4431490 A K i k s t x h1)). Qed.
Lemma lem4431494 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (i : K) (h1 : term327 A K k s x i) : term327 A K k s x i.
Proof. exact (h1). Qed.
Lemma lem4431495 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term327 A K k t x i) : term327 A K k t x i.
Proof. exact (h1). Qed.
Lemma lem4431497 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (i : K) (h1 : term326 A K k s x i) : term326 A K k s x i.
Proof. exact (h1). Qed.
Lemma lem4431501 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term326 A K k t x i) : term326 A K k t x i.
Proof. exact (h1). Qed.
Lemma lem4431541 {A K : Type'} (k : K -> Prop) (x : K -> A) (h1 : term216 A K k x) : term216 A K k x.
Proof. exact (h1). Qed.
Lemma lem4431570 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (i : K) : (term337 A K k s x i) = (term337 A K k s x i).
Proof. exact (eq_refl (term337 A K k s x i)). Qed.
Lemma lem4431571 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term338 A K k s x) = (term338 A K k s x).
Proof. exact (fun_ext (fun i : K => @lem4431570 A K k s x i)). Qed.
Lemma lem4431572 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4431574 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term339 A K k s x) = (term339 A K k s x).
Proof. exact (MK_COMB (@lem4431572 K) (@lem4431571 A K k s x)). Qed.
Lemma lem4431575 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term344 A K k s t x i) : term339 A K k s x.
Proof. exact (EQ_MP (@lem4431574 A K k s x) (@lem4431482 A K k s t x i h1)). Qed.
Lemma lem4431583 {A K : Type'} (s : type1470 A K) (x : K -> A) (i : K) (h1 : term324 A K s x i) : term324 A K s x i.
Proof. exact (h1). Qed.
Lemma lem4431595 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) (i : K) : (term337 A K k t x i) = (term337 A K k t x i).
Proof. exact (eq_refl (term337 A K k t x i)). Qed.
Lemma lem4431596 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term338 A K k t x) = (term338 A K k t x).
Proof. exact (fun_ext (fun i : K => @lem4431595 A K k t x i)). Qed.
Lemma lem4431597 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4431599 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term339 A K k t x) = (term339 A K k t x).
Proof. exact (MK_COMB (@lem4431597 K) (@lem4431596 A K k t x)). Qed.
Lemma lem4431600 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term344 A K k s t x i) : term339 A K k t x.
Proof. exact (EQ_MP (@lem4431599 A K k t x) (@lem4431480 A K k s t x i h1)). Qed.
Lemma lem4431625 {A K : Type'} (t : type1470 A K) (x : K -> A) (i : K) (h1 : term324 A K t x i) : term324 A K t x i.
Proof. exact (h1). Qed.
Lemma lem4431656 {A K : Type'} (k : K -> Prop) (x : K -> A) (h1 : term216 A K k x) : term216 A K k x.
Proof. exact (h1). Qed.
Lemma lem4431678 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : K -> A) (i : K) : (term319 A K k s t x i) = (term347 A K s k t x i).
Proof. exact (@lem19490 (term312 A K s x i) (term316 K k i) (term312 A K t x i)). Qed.
Lemma lem4431679 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term320 A K k s t x) = (term348 A K s k t x).
Proof. exact (fun_ext (fun i : K => @lem4431678 A K s k t x i)). Qed.
Lemma lem4431680 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4431682 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term321 A K k s t x) = (term349 A K s k t x).
Proof. exact (MK_COMB (@lem4431680 K) (@lem4431679 A K s k t x)). Qed.
Lemma lem4431683 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term331 A K i k s t x) : term349 A K s k t x.
Proof. exact (EQ_MP (@lem4431682 A K s k t x) (@lem4431492 A K i k s t x h1)). Qed.
Lemma lem4431722 {A K : Type'} (k : K -> Prop) (x : K -> A) (h1 : term216 A K k x) : term216 A K k x.
Proof. exact (h1). Qed.
Lemma lem4431744 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : K -> A) (i : K) : (term319 A K k s t x i) = (term347 A K s k t x i).
Proof. exact (@lem19490 (term312 A K s x i) (term316 K k i) (term312 A K t x i)). Qed.
Lemma lem4431745 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term320 A K k s t x) = (term348 A K s k t x).
Proof. exact (fun_ext (fun i : K => @lem4431744 A K s k t x i)). Qed.
Lemma lem4431746 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4431748 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term321 A K k s t x) = (term349 A K s k t x).
Proof. exact (MK_COMB (@lem4431746 K) (@lem4431745 A K s k t x)). Qed.
Lemma lem4431749 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term331 A K i k s t x) : term349 A K s k t x.
Proof. exact (EQ_MP (@lem4431748 A K s k t x) (@lem4431492 A K i k s t x h1)). Qed.
Lemma lem4431767 {A K : Type'} (_50984 : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term344 A K k s t x i) : term350 A K k s x _50984.
Proof. exact (@lem4431575 A K k s t x i h1 _50984). Qed.
Lemma lem4431768 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (_50984 : K) : (term350 A K k s x _50984) = (term337 A K k s x _50984).
Proof. exact (eq_refl (term350 A K k s x _50984)). Qed.
Lemma lem4431770 {A K : Type'} (_50985 : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term344 A K k s t x i) : term350 A K k t x _50985.
Proof. exact (@lem4431600 A K k s t x i h1 _50985). Qed.
Lemma lem4431771 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) (_50985 : K) : (term350 A K k t x _50985) = (term337 A K k t x _50985).
Proof. exact (eq_refl (term350 A K k t x _50985)). Qed.
Lemma lem4431779 {A K : Type'} (_50988 : K) (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term331 A K i k s t x) : term351 A K s k t x _50988.
Proof. exact (@lem4431683 A K i k s t x h1 _50988). Qed.
Lemma lem4431780 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : K -> A) (_50988 : K) : (term351 A K s k t x _50988) = (term347 A K s k t x _50988).
Proof. exact (eq_refl (term351 A K s k t x _50988)). Qed.
Lemma lem4431781 {A K : Type'} (_50988 : K) (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term331 A K i k s t x) : term347 A K s k t x _50988.
Proof. exact (EQ_MP (@lem4431780 A K s k t x _50988) (@lem4431779 A K _50988 i k s t x h1)). Qed.
Lemma lem4431785 {A K : Type'} (_50990 : K) (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term331 A K i k s t x) : term351 A K s k t x _50990.
Proof. exact (@lem4431749 A K i k s t x h1 _50990). Qed.
Lemma lem4431786 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : K -> A) (_50990 : K) : (term351 A K s k t x _50990) = (term347 A K s k t x _50990).
Proof. exact (eq_refl (term351 A K s k t x _50990)). Qed.
Lemma lem4431787 {A K : Type'} (_50990 : K) (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term331 A K i k s t x) : term347 A K s k t x _50990.
Proof. exact (EQ_MP (@lem4431786 A K s k t x _50990) (@lem4431785 A K _50990 i k s t x h1)). Qed.
Lemma lem4431813 {A K : Type'} (k : K -> Prop) (x : K -> A) (h1 : term216 A K k x) : term216 A K k x.
Proof. exact (h1). Qed.
Lemma lem4431829 {A K : Type'} (_50984 : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term344 A K k s t x i) : term337 A K k s x _50984.
Proof. exact (EQ_MP (@lem4431768 A K k s x _50984) (@lem4431767 A K _50984 k s t x i h1)). Qed.
Lemma lem4431833 {A K : Type'} (s : type1470 A K) (x : K -> A) (i : K) (h1 : term324 A K s x i) : term324 A K s x i.
Proof. exact (h1). Qed.
Lemma lem4431841 {A K : Type'} (_50985 : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term344 A K k s t x i) : term337 A K k t x _50985.
Proof. exact (EQ_MP (@lem4431771 A K k t x _50985) (@lem4431770 A K _50985 k s t x i h1)). Qed.
Lemma lem4431853 {A K : Type'} (t : type1470 A K) (x : K -> A) (i : K) (h1 : term324 A K t x i) : term324 A K t x i.
Proof. exact (h1). Qed.
Lemma lem4431857 {A K : Type'} (k : K -> Prop) (x : K -> A) (h1 : term216 A K k x) : term216 A K k x.
Proof. exact (h1). Qed.
Lemma lem4431875 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (i : K) (h1 : term326 A K k s x i) : term324 A K s x i.
Proof. exact (proj2 (@lem4431497 A K k s x i h1)). Qed.
Lemma lem4431881 {A K : Type'} (_50988 : K) (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term331 A K i k s t x) : term337 A K k s x _50988.
Proof. exact (proj1 (@lem4431781 A K _50988 i k s t x h1)). Qed.
Lemma lem4431891 {A K : Type'} (k : K -> Prop) (x : K -> A) (h1 : term216 A K k x) : term216 A K k x.
Proof. exact (h1). Qed.
Lemma lem4431909 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term326 A K k t x i) : term324 A K t x i.
Proof. exact (proj2 (@lem4431501 A K k t x i h1)). Qed.
Lemma lem4431921 {A K : Type'} (_50990 : K) (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term331 A K i k s t x) : term337 A K k t x _50990.
Proof. exact (proj2 (@lem4431787 A K _50990 i k s t x h1)). Qed.
Lemma lem4431923 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term344 A K k s t x i) : @EXTENSIONAL K A k x.
Proof. exact (proj1 (@lem4431478 A K k s t x i h1)). Qed.
Lemma lem4431924 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term344 A K k s t x i) : term352 A K k x.
Proof. exact (fun h0 : term216 A K k x => @lem4431923 A K k s t x i h1). Qed.
Lemma lem4431926 (p : Prop) : (term353 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4431927 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term352 A K k x) = (@EXTENSIONAL K A k x).
Proof. exact (@lem4431926 (@EXTENSIONAL K A k x)). Qed.
Lemma lem4431928 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term344 A K k s t x i) : @EXTENSIONAL K A k x.
Proof. exact (EQ_MP (@lem4431927 A K k x) (@lem4431924 A K k s t x i h1)). Qed.
Lemma lem4431931 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4431933 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term216 A K k x) = (term354 A K k x).
Proof. exact (@lem4431931 (@EXTENSIONAL K A k x)). Qed.
Lemma lem4431936 {A K : Type'} (k : K -> Prop) (x : K -> A) (h1 : term216 A K k x) : term354 A K k x.
Proof. exact (EQ_MP (@lem4431933 A K k x) (@lem4431813 A K k x h1)). Qed.
Lemma lem4431939 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term216 A K k x) (h2 : term344 A K k s t x i) : False.
Proof. exact (@lem4431936 A K k x h1 (@lem4431928 A K k s t x i h2)). Qed.
Lemma lem4431940 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term216 A K k x) (h2 : term344 A K k s t x i) : term355.
Proof. exact (fun h0 : ~ False => @lem4431939 A K k s t x i h1 h2). Qed.
Lemma lem4431942 (p : Prop) : (term353 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4431943 : term355 = False.
Proof. exact (@lem4431942 False). Qed.
Lemma lem4431944 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term216 A K k x) (h2 : term344 A K k s t x i) : False.
Proof. exact (EQ_MP (@lem4431943) (@lem4431940 A K k s t x i h1 h2)). Qed.
Lemma lem4431946 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term335 A K k s t x i) : @I (K -> Prop) k i.
Proof. exact (proj1 (@lem4431485 A K k s t x i h1)). Qed.
Lemma lem4431947 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term335 A K k s t x i) : term356 K k i.
Proof. exact (fun h0 : term316 K k i => @lem4431946 A K k s t x i h1). Qed.
Lemma lem4431949 (p : Prop) : (term353 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4431950 {K : Type'} (k : K -> Prop) (i : K) : (term356 K k i) = (@I (K -> Prop) k i).
Proof. exact (@lem4431949 (@I (K -> Prop) k i)). Qed.
Lemma lem4431951 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term335 A K k s t x i) : @I (K -> Prop) k i.
Proof. exact (EQ_MP (@lem4431950 K k i) (@lem4431947 A K k s t x i h1)). Qed.
Lemma lem4431957 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4431958 {A K : Type'} (s : type1470 A K) (x : K -> A) (k : K -> Prop) (_50984 : K) : (term337 A K k s x _50984) = (term357 A K s x k _50984).
Proof. exact (@lem4431957 (term312 A K s x _50984) (term316 K k _50984)). Qed.
Lemma lem4431964 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4431965 {A K : Type'} (s : type1470 A K) (x : K -> A) (k : K -> Prop) (_50984 : K) : (term358 A K k s x _50984) = (term359 A K s x k _50984).
Proof. exact (MK_COMB (@lem4431964) (@lem4431958 A K s x k _50984)). Qed.
Lemma lem4431971 {A K : Type'} (s : type1470 A K) (x : K -> A) (k : K -> Prop) (_50984 : K) : (term357 A K s x k _50984) = (term357 A K s x k _50984).
Proof. exact (eq_refl (term357 A K s x k _50984)). Qed.
Lemma lem4431972 {A K : Type'} (s : type1470 A K) (x : K -> A) (k : K -> Prop) (_50984 : K) : ((term337 A K k s x _50984) = (term357 A K s x k _50984)) = ((term357 A K s x k _50984) = (term357 A K s x k _50984)).
Proof. exact (MK_COMB (@lem4431965 A K s x k _50984) (@lem4431971 A K s x k _50984)). Qed.
Lemma lem4431974 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4431975 (x : Prop) : (x = x) = True.
Proof. exact (@lem4431974 Prop x). Qed.
Lemma lem4431976 {A K : Type'} (s : type1470 A K) (x : K -> A) (k : K -> Prop) (_50984 : K) : ((term357 A K s x k _50984) = (term357 A K s x k _50984)) = True.
Proof. exact (@lem4431975 (term357 A K s x k _50984)). Qed.
Lemma lem4431977 {A K : Type'} (s : type1470 A K) (x : K -> A) (k : K -> Prop) (_50984 : K) : ((term337 A K k s x _50984) = (term357 A K s x k _50984)) = True.
Proof. exact (TRANS (@lem4431972 A K s x k _50984) (@lem4431976 A K s x k _50984)). Qed.
Lemma lem4431978 {A K : Type'} (s : type1470 A K) (x : K -> A) (k : K -> Prop) (_50984 : K) : True = ((term337 A K k s x _50984) = (term357 A K s x k _50984)).
Proof. exact (SYM (@lem4431977 A K s x k _50984)). Qed.
Lemma lem4431979 {A K : Type'} (s : type1470 A K) (x : K -> A) (k : K -> Prop) (_50984 : K) : (term337 A K k s x _50984) = (term357 A K s x k _50984).
Proof. exact (EQ_MP (@lem4431978 A K s x k _50984) (@lem0)). Qed.
Lemma lem4431980 {A K : Type'} (_50984 : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term344 A K k s t x i) : term357 A K s x k _50984.
Proof. exact (EQ_MP (@lem4431979 A K s x k _50984) (@lem4431829 A K _50984 k s t x i h1)). Qed.
Lemma lem4431982 (b : Prop) (a : Prop) : (a \/ b) = (term360 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4431983 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (_50984 : K) : (term357 A K s x k _50984) = (term361 A K k s x _50984).
Proof. exact (@lem4431982 (term316 K k _50984) (term312 A K s x _50984)). Qed.
Lemma lem4431985 (a : Prop) : (term151 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4431986 {K : Type'} (k : K -> Prop) (_50984 : K) : (term362 K k _50984) = (@I (K -> Prop) k _50984).
Proof. exact (@lem4431985 (@I (K -> Prop) k _50984)). Qed.
Lemma lem4431987 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4431988 {K : Type'} (k : K -> Prop) (_50984 : K) : (term363 K k _50984) = (term364 K k _50984).
Proof. exact (MK_COMB (@lem4431987) (@lem4431986 K k _50984)). Qed.
Lemma lem4431989 {A K : Type'} (s : type1470 A K) (x : K -> A) (_50984 : K) : (term312 A K s x _50984) = (term312 A K s x _50984).
Proof. exact (eq_refl (term312 A K s x _50984)). Qed.
Lemma lem4431990 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (_50984 : K) : (term361 A K k s x _50984) = (term365 A K k s x _50984).
Proof. exact (MK_COMB (@lem4431988 K k _50984) (@lem4431989 A K s x _50984)). Qed.
Lemma lem4431991 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (_50984 : K) : (term357 A K s x k _50984) = (term365 A K k s x _50984).
Proof. exact (TRANS (@lem4431983 A K k s x _50984) (@lem4431990 A K k s x _50984)). Qed.
Lemma lem4431994 {A K : Type'} (_50984 : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term344 A K k s t x i) : term365 A K k s x _50984.
Proof. exact (EQ_MP (@lem4431991 A K k s x _50984) (@lem4431980 A K _50984 k s t x i h1)). Qed.
Lemma lem4431995 {A K : Type'} (_50984 : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term344 A K k s t x i) : term365 A K k s x _50984.
Proof. exact (@lem4431994 A K _50984 k s t x i h1). Qed.
Lemma lem4431996 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term344 A K k s t x i) : term365 A K k s x i.
Proof. exact (@lem4431995 A K i k s t x i h1). Qed.
Lemma lem4431999 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term344 A K k s t x i) (h2 : term335 A K k s t x i) : term312 A K s x i.
Proof. exact (@lem4431996 A K k s t x i h1 (@lem4431951 A K k s t x i h2)). Qed.
Lemma lem4432000 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term344 A K k s t x i) (h2 : term335 A K k s t x i) : term366 A K s x i.
Proof. exact (fun h0 : term324 A K s x i => @lem4431999 A K k s t x i h1 h2). Qed.
Lemma lem4432002 (p : Prop) : (term353 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4432003 {A K : Type'} (s : type1470 A K) (x : K -> A) (i : K) : (term366 A K s x i) = (term312 A K s x i).
Proof. exact (@lem4432002 (term312 A K s x i)). Qed.
Lemma lem4432004 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term344 A K k s t x i) (h2 : term335 A K k s t x i) : term312 A K s x i.
Proof. exact (EQ_MP (@lem4432003 A K s x i) (@lem4432000 A K k s t x i h1 h2)). Qed.
Lemma lem4432007 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4432009 {A K : Type'} (s : type1470 A K) (x : K -> A) (i : K) : (term324 A K s x i) = (term367 A K s x i).
Proof. exact (@lem4432007 (term312 A K s x i)). Qed.
Lemma lem4432012 {A K : Type'} (s : type1470 A K) (x : K -> A) (i : K) (h1 : term324 A K s x i) : term367 A K s x i.
Proof. exact (EQ_MP (@lem4432009 A K s x i) (@lem4431833 A K s x i h1)). Qed.
Lemma lem4432015 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term324 A K s x i) (h2 : term344 A K k s t x i) (h3 : term335 A K k s t x i) : False.
Proof. exact (@lem4432012 A K s x i h1 (@lem4432004 A K k s t x i h2 h3)). Qed.
Lemma lem4432016 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term324 A K s x i) (h2 : term344 A K k s t x i) (h3 : term335 A K k s t x i) : term355.
Proof. exact (fun h0 : ~ False => @lem4432015 A K k s t x i h1 h2 h3). Qed.
Lemma lem4432018 (p : Prop) : (term353 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4432019 : term355 = False.
Proof. exact (@lem4432018 False). Qed.
Lemma lem4432020 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term324 A K s x i) (h2 : term344 A K k s t x i) (h3 : term335 A K k s t x i) : False.
Proof. exact (EQ_MP (@lem4432019) (@lem4432016 A K k s t x i h1 h2 h3)). Qed.
Lemma lem4432022 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term335 A K k s t x i) : @I (K -> Prop) k i.
Proof. exact (proj1 (@lem4431485 A K k s t x i h1)). Qed.
Lemma lem4432023 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term335 A K k s t x i) : term356 K k i.
Proof. exact (fun h0 : term316 K k i => @lem4432022 A K k s t x i h1). Qed.
Lemma lem4432025 (p : Prop) : (term353 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4432026 {K : Type'} (k : K -> Prop) (i : K) : (term356 K k i) = (@I (K -> Prop) k i).
Proof. exact (@lem4432025 (@I (K -> Prop) k i)). Qed.
Lemma lem4432027 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term335 A K k s t x i) : @I (K -> Prop) k i.
Proof. exact (EQ_MP (@lem4432026 K k i) (@lem4432023 A K k s t x i h1)). Qed.
Lemma lem4432033 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4432034 {A K : Type'} (t : type1470 A K) (x : K -> A) (k : K -> Prop) (_50985 : K) : (term337 A K k t x _50985) = (term357 A K t x k _50985).
Proof. exact (@lem4432033 (term312 A K t x _50985) (term316 K k _50985)). Qed.
Lemma lem4432040 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4432041 {A K : Type'} (t : type1470 A K) (x : K -> A) (k : K -> Prop) (_50985 : K) : (term358 A K k t x _50985) = (term359 A K t x k _50985).
Proof. exact (MK_COMB (@lem4432040) (@lem4432034 A K t x k _50985)). Qed.
Lemma lem4432047 {A K : Type'} (t : type1470 A K) (x : K -> A) (k : K -> Prop) (_50985 : K) : (term357 A K t x k _50985) = (term357 A K t x k _50985).
Proof. exact (eq_refl (term357 A K t x k _50985)). Qed.
Lemma lem4432048 {A K : Type'} (t : type1470 A K) (x : K -> A) (k : K -> Prop) (_50985 : K) : ((term337 A K k t x _50985) = (term357 A K t x k _50985)) = ((term357 A K t x k _50985) = (term357 A K t x k _50985)).
Proof. exact (MK_COMB (@lem4432041 A K t x k _50985) (@lem4432047 A K t x k _50985)). Qed.
Lemma lem4432050 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4432051 (x : Prop) : (x = x) = True.
Proof. exact (@lem4432050 Prop x). Qed.
Lemma lem4432052 {A K : Type'} (t : type1470 A K) (x : K -> A) (k : K -> Prop) (_50985 : K) : ((term357 A K t x k _50985) = (term357 A K t x k _50985)) = True.
Proof. exact (@lem4432051 (term357 A K t x k _50985)). Qed.
Lemma lem4432053 {A K : Type'} (t : type1470 A K) (x : K -> A) (k : K -> Prop) (_50985 : K) : ((term337 A K k t x _50985) = (term357 A K t x k _50985)) = True.
Proof. exact (TRANS (@lem4432048 A K t x k _50985) (@lem4432052 A K t x k _50985)). Qed.
Lemma lem4432054 {A K : Type'} (t : type1470 A K) (x : K -> A) (k : K -> Prop) (_50985 : K) : True = ((term337 A K k t x _50985) = (term357 A K t x k _50985)).
Proof. exact (SYM (@lem4432053 A K t x k _50985)). Qed.
Lemma lem4432055 {A K : Type'} (t : type1470 A K) (x : K -> A) (k : K -> Prop) (_50985 : K) : (term337 A K k t x _50985) = (term357 A K t x k _50985).
Proof. exact (EQ_MP (@lem4432054 A K t x k _50985) (@lem0)). Qed.
Lemma lem4432056 {A K : Type'} (_50985 : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term344 A K k s t x i) : term357 A K t x k _50985.
Proof. exact (EQ_MP (@lem4432055 A K t x k _50985) (@lem4431841 A K _50985 k s t x i h1)). Qed.
Lemma lem4432058 (b : Prop) (a : Prop) : (a \/ b) = (term360 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4432059 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) (_50985 : K) : (term357 A K t x k _50985) = (term361 A K k t x _50985).
Proof. exact (@lem4432058 (term316 K k _50985) (term312 A K t x _50985)). Qed.
Lemma lem4432061 (a : Prop) : (term151 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4432062 {K : Type'} (k : K -> Prop) (_50985 : K) : (term362 K k _50985) = (@I (K -> Prop) k _50985).
Proof. exact (@lem4432061 (@I (K -> Prop) k _50985)). Qed.
Lemma lem4432063 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4432064 {K : Type'} (k : K -> Prop) (_50985 : K) : (term363 K k _50985) = (term364 K k _50985).
Proof. exact (MK_COMB (@lem4432063) (@lem4432062 K k _50985)). Qed.
Lemma lem4432065 {A K : Type'} (t : type1470 A K) (x : K -> A) (_50985 : K) : (term312 A K t x _50985) = (term312 A K t x _50985).
Proof. exact (eq_refl (term312 A K t x _50985)). Qed.
Lemma lem4432066 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) (_50985 : K) : (term361 A K k t x _50985) = (term365 A K k t x _50985).
Proof. exact (MK_COMB (@lem4432064 K k _50985) (@lem4432065 A K t x _50985)). Qed.
Lemma lem4432067 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) (_50985 : K) : (term357 A K t x k _50985) = (term365 A K k t x _50985).
Proof. exact (TRANS (@lem4432059 A K k t x _50985) (@lem4432066 A K k t x _50985)). Qed.
Lemma lem4432070 {A K : Type'} (_50985 : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term344 A K k s t x i) : term365 A K k t x _50985.
Proof. exact (EQ_MP (@lem4432067 A K k t x _50985) (@lem4432056 A K _50985 k s t x i h1)). Qed.
Lemma lem4432071 {A K : Type'} (_50985 : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term344 A K k s t x i) : term365 A K k t x _50985.
Proof. exact (@lem4432070 A K _50985 k s t x i h1). Qed.
Lemma lem4432072 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term344 A K k s t x i) : term365 A K k t x i.
Proof. exact (@lem4432071 A K i k s t x i h1). Qed.
Lemma lem4432075 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term344 A K k s t x i) (h2 : term335 A K k s t x i) : term312 A K t x i.
Proof. exact (@lem4432072 A K k s t x i h1 (@lem4432027 A K k s t x i h2)). Qed.
Lemma lem4432076 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term344 A K k s t x i) (h2 : term335 A K k s t x i) : term366 A K t x i.
Proof. exact (fun h0 : term324 A K t x i => @lem4432075 A K k s t x i h1 h2). Qed.
Lemma lem4432078 (p : Prop) : (term353 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4432079 {A K : Type'} (t : type1470 A K) (x : K -> A) (i : K) : (term366 A K t x i) = (term312 A K t x i).
Proof. exact (@lem4432078 (term312 A K t x i)). Qed.
Lemma lem4432080 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term344 A K k s t x i) (h2 : term335 A K k s t x i) : term312 A K t x i.
Proof. exact (EQ_MP (@lem4432079 A K t x i) (@lem4432076 A K k s t x i h1 h2)). Qed.
Lemma lem4432083 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4432085 {A K : Type'} (t : type1470 A K) (x : K -> A) (i : K) : (term324 A K t x i) = (term367 A K t x i).
Proof. exact (@lem4432083 (term312 A K t x i)). Qed.
Lemma lem4432088 {A K : Type'} (t : type1470 A K) (x : K -> A) (i : K) (h1 : term324 A K t x i) : term367 A K t x i.
Proof. exact (EQ_MP (@lem4432085 A K t x i) (@lem4431853 A K t x i h1)). Qed.
Lemma lem4432091 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term324 A K t x i) (h2 : term344 A K k s t x i) (h3 : term335 A K k s t x i) : False.
Proof. exact (@lem4432088 A K t x i h1 (@lem4432080 A K k s t x i h2 h3)). Qed.
Lemma lem4432092 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term324 A K t x i) (h2 : term344 A K k s t x i) (h3 : term335 A K k s t x i) : term355.
Proof. exact (fun h0 : ~ False => @lem4432091 A K k s t x i h1 h2 h3). Qed.
Lemma lem4432094 (p : Prop) : (term353 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4432095 : term355 = False.
Proof. exact (@lem4432094 False). Qed.
Lemma lem4432096 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term324 A K t x i) (h2 : term344 A K k s t x i) (h3 : term335 A K k s t x i) : False.
Proof. exact (EQ_MP (@lem4432095) (@lem4432092 A K k s t x i h1 h2 h3)). Qed.
Lemma lem4432098 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term331 A K i k s t x) : @EXTENSIONAL K A k x.
Proof. exact (proj1 (@lem4431490 A K i k s t x h1)). Qed.
Lemma lem4432099 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term331 A K i k s t x) : term352 A K k x.
Proof. exact (fun h0 : term216 A K k x => @lem4432098 A K i k s t x h1). Qed.
Lemma lem4432101 (p : Prop) : (term353 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4432102 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term352 A K k x) = (@EXTENSIONAL K A k x).
Proof. exact (@lem4432101 (@EXTENSIONAL K A k x)). Qed.
Lemma lem4432103 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term331 A K i k s t x) : @EXTENSIONAL K A k x.
Proof. exact (EQ_MP (@lem4432102 A K k x) (@lem4432099 A K i k s t x h1)). Qed.
Lemma lem4432106 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4432108 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term216 A K k x) = (term354 A K k x).
Proof. exact (@lem4432106 (@EXTENSIONAL K A k x)). Qed.
Lemma lem4432111 {A K : Type'} (k : K -> Prop) (x : K -> A) (h1 : term216 A K k x) : term354 A K k x.
Proof. exact (EQ_MP (@lem4432108 A K k x) (@lem4431857 A K k x h1)). Qed.
Lemma lem4432114 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term216 A K k x) (h2 : term331 A K i k s t x) : False.
Proof. exact (@lem4432111 A K k x h1 (@lem4432103 A K i k s t x h2)). Qed.
Lemma lem4432115 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term216 A K k x) (h2 : term331 A K i k s t x) : term355.
Proof. exact (fun h0 : ~ False => @lem4432114 A K i k s t x h1 h2). Qed.
Lemma lem4432117 (p : Prop) : (term353 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4432118 : term355 = False.
Proof. exact (@lem4432117 False). Qed.
Lemma lem4432119 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term216 A K k x) (h2 : term331 A K i k s t x) : False.
Proof. exact (EQ_MP (@lem4432118) (@lem4432115 A K i k s t x h1 h2)). Qed.
Lemma lem4432121 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (i : K) (h1 : term326 A K k s x i) : @I (K -> Prop) k i.
Proof. exact (proj1 (@lem4431497 A K k s x i h1)). Qed.
Lemma lem4432122 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (i : K) (h1 : term326 A K k s x i) : term356 K k i.
Proof. exact (fun h0 : term316 K k i => @lem4432121 A K k s x i h1). Qed.
Lemma lem4432124 (p : Prop) : (term353 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4432125 {K : Type'} (k : K -> Prop) (i : K) : (term356 K k i) = (@I (K -> Prop) k i).
Proof. exact (@lem4432124 (@I (K -> Prop) k i)). Qed.
Lemma lem4432126 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (i : K) (h1 : term326 A K k s x i) : @I (K -> Prop) k i.
Proof. exact (EQ_MP (@lem4432125 K k i) (@lem4432122 A K k s x i h1)). Qed.
Lemma lem4432132 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4432133 {A K : Type'} (s : type1470 A K) (x : K -> A) (k : K -> Prop) (_50988 : K) : (term337 A K k s x _50988) = (term357 A K s x k _50988).
Proof. exact (@lem4432132 (term312 A K s x _50988) (term316 K k _50988)). Qed.
Lemma lem4432139 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4432140 {A K : Type'} (s : type1470 A K) (x : K -> A) (k : K -> Prop) (_50988 : K) : (term358 A K k s x _50988) = (term359 A K s x k _50988).
Proof. exact (MK_COMB (@lem4432139) (@lem4432133 A K s x k _50988)). Qed.
Lemma lem4432146 {A K : Type'} (s : type1470 A K) (x : K -> A) (k : K -> Prop) (_50988 : K) : (term357 A K s x k _50988) = (term357 A K s x k _50988).
Proof. exact (eq_refl (term357 A K s x k _50988)). Qed.
Lemma lem4432147 {A K : Type'} (s : type1470 A K) (x : K -> A) (k : K -> Prop) (_50988 : K) : ((term337 A K k s x _50988) = (term357 A K s x k _50988)) = ((term357 A K s x k _50988) = (term357 A K s x k _50988)).
Proof. exact (MK_COMB (@lem4432140 A K s x k _50988) (@lem4432146 A K s x k _50988)). Qed.
Lemma lem4432149 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4432150 (x : Prop) : (x = x) = True.
Proof. exact (@lem4432149 Prop x). Qed.
Lemma lem4432151 {A K : Type'} (s : type1470 A K) (x : K -> A) (k : K -> Prop) (_50988 : K) : ((term357 A K s x k _50988) = (term357 A K s x k _50988)) = True.
Proof. exact (@lem4432150 (term357 A K s x k _50988)). Qed.
Lemma lem4432152 {A K : Type'} (s : type1470 A K) (x : K -> A) (k : K -> Prop) (_50988 : K) : ((term337 A K k s x _50988) = (term357 A K s x k _50988)) = True.
Proof. exact (TRANS (@lem4432147 A K s x k _50988) (@lem4432151 A K s x k _50988)). Qed.
Lemma lem4432153 {A K : Type'} (s : type1470 A K) (x : K -> A) (k : K -> Prop) (_50988 : K) : True = ((term337 A K k s x _50988) = (term357 A K s x k _50988)).
Proof. exact (SYM (@lem4432152 A K s x k _50988)). Qed.
Lemma lem4432154 {A K : Type'} (s : type1470 A K) (x : K -> A) (k : K -> Prop) (_50988 : K) : (term337 A K k s x _50988) = (term357 A K s x k _50988).
Proof. exact (EQ_MP (@lem4432153 A K s x k _50988) (@lem0)). Qed.
Lemma lem4432155 {A K : Type'} (_50988 : K) (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term331 A K i k s t x) : term357 A K s x k _50988.
Proof. exact (EQ_MP (@lem4432154 A K s x k _50988) (@lem4431881 A K _50988 i k s t x h1)). Qed.
Lemma lem4432157 (b : Prop) (a : Prop) : (a \/ b) = (term360 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4432158 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (_50988 : K) : (term357 A K s x k _50988) = (term361 A K k s x _50988).
Proof. exact (@lem4432157 (term316 K k _50988) (term312 A K s x _50988)). Qed.
Lemma lem4432160 (a : Prop) : (term151 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4432161 {K : Type'} (k : K -> Prop) (_50988 : K) : (term362 K k _50988) = (@I (K -> Prop) k _50988).
Proof. exact (@lem4432160 (@I (K -> Prop) k _50988)). Qed.
Lemma lem4432162 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4432163 {K : Type'} (k : K -> Prop) (_50988 : K) : (term363 K k _50988) = (term364 K k _50988).
Proof. exact (MK_COMB (@lem4432162) (@lem4432161 K k _50988)). Qed.
Lemma lem4432164 {A K : Type'} (s : type1470 A K) (x : K -> A) (_50988 : K) : (term312 A K s x _50988) = (term312 A K s x _50988).
Proof. exact (eq_refl (term312 A K s x _50988)). Qed.
Lemma lem4432165 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (_50988 : K) : (term361 A K k s x _50988) = (term365 A K k s x _50988).
Proof. exact (MK_COMB (@lem4432163 K k _50988) (@lem4432164 A K s x _50988)). Qed.
Lemma lem4432166 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (_50988 : K) : (term357 A K s x k _50988) = (term365 A K k s x _50988).
Proof. exact (TRANS (@lem4432158 A K k s x _50988) (@lem4432165 A K k s x _50988)). Qed.
Lemma lem4432169 {A K : Type'} (_50988 : K) (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term331 A K i k s t x) : term365 A K k s x _50988.
Proof. exact (EQ_MP (@lem4432166 A K k s x _50988) (@lem4432155 A K _50988 i k s t x h1)). Qed.
Lemma lem4432170 {A K : Type'} (_50988 : K) (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term331 A K i k s t x) : term365 A K k s x _50988.
Proof. exact (@lem4432169 A K _50988 i k s t x h1). Qed.
Lemma lem4432171 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term331 A K i k s t x) : term365 A K k s x i.
Proof. exact (@lem4432170 A K i i k s t x h1). Qed.
Lemma lem4432174 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term326 A K k s x i) (h2 : term331 A K i k s t x) : term312 A K s x i.
Proof. exact (@lem4432171 A K i k s t x h2 (@lem4432126 A K k s x i h1)). Qed.
Lemma lem4432175 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term326 A K k s x i) (h2 : term331 A K i k s t x) : term366 A K s x i.
Proof. exact (fun h0 : term324 A K s x i => @lem4432174 A K i k s t x h1 h2). Qed.
Lemma lem4432177 (p : Prop) : (term353 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4432178 {A K : Type'} (s : type1470 A K) (x : K -> A) (i : K) : (term366 A K s x i) = (term312 A K s x i).
Proof. exact (@lem4432177 (term312 A K s x i)). Qed.
Lemma lem4432179 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term326 A K k s x i) (h2 : term331 A K i k s t x) : term312 A K s x i.
Proof. exact (EQ_MP (@lem4432178 A K s x i) (@lem4432175 A K i k s t x h1 h2)). Qed.
Lemma lem4432182 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4432184 {A K : Type'} (s : type1470 A K) (x : K -> A) (i : K) : (term324 A K s x i) = (term367 A K s x i).
Proof. exact (@lem4432182 (term312 A K s x i)). Qed.
Lemma lem4432187 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (i : K) (h1 : term326 A K k s x i) : term367 A K s x i.
Proof. exact (EQ_MP (@lem4432184 A K s x i) (@lem4431875 A K k s x i h1)). Qed.
Lemma lem4432190 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term326 A K k s x i) (h2 : term331 A K i k s t x) : False.
Proof. exact (@lem4432187 A K k s x i h1 (@lem4432179 A K i k s t x h1 h2)). Qed.
Lemma lem4432191 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term326 A K k s x i) (h2 : term331 A K i k s t x) : term355.
Proof. exact (fun h0 : ~ False => @lem4432190 A K i k s t x h1 h2). Qed.
Lemma lem4432193 (p : Prop) : (term353 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4432194 : term355 = False.
Proof. exact (@lem4432193 False). Qed.
Lemma lem4432195 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term326 A K k s x i) (h2 : term331 A K i k s t x) : False.
Proof. exact (EQ_MP (@lem4432194) (@lem4432191 A K i k s t x h1 h2)). Qed.
Lemma lem4432197 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term331 A K i k s t x) : @EXTENSIONAL K A k x.
Proof. exact (proj1 (@lem4431490 A K i k s t x h1)). Qed.
Lemma lem4432198 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term331 A K i k s t x) : term352 A K k x.
Proof. exact (fun h0 : term216 A K k x => @lem4432197 A K i k s t x h1). Qed.
Lemma lem4432200 (p : Prop) : (term353 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4432201 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term352 A K k x) = (@EXTENSIONAL K A k x).
Proof. exact (@lem4432200 (@EXTENSIONAL K A k x)). Qed.
Lemma lem4432202 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term331 A K i k s t x) : @EXTENSIONAL K A k x.
Proof. exact (EQ_MP (@lem4432201 A K k x) (@lem4432198 A K i k s t x h1)). Qed.
Lemma lem4432205 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4432207 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term216 A K k x) = (term354 A K k x).
Proof. exact (@lem4432205 (@EXTENSIONAL K A k x)). Qed.
Lemma lem4432210 {A K : Type'} (k : K -> Prop) (x : K -> A) (h1 : term216 A K k x) : term354 A K k x.
Proof. exact (EQ_MP (@lem4432207 A K k x) (@lem4431891 A K k x h1)). Qed.
Lemma lem4432213 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term216 A K k x) (h2 : term331 A K i k s t x) : False.
Proof. exact (@lem4432210 A K k x h1 (@lem4432202 A K i k s t x h2)). Qed.
Lemma lem4432214 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term216 A K k x) (h2 : term331 A K i k s t x) : term355.
Proof. exact (fun h0 : ~ False => @lem4432213 A K i k s t x h1 h2). Qed.
Lemma lem4432216 (p : Prop) : (term353 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4432217 : term355 = False.
Proof. exact (@lem4432216 False). Qed.
Lemma lem4432218 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term216 A K k x) (h2 : term331 A K i k s t x) : False.
Proof. exact (EQ_MP (@lem4432217) (@lem4432214 A K i k s t x h1 h2)). Qed.
Lemma lem4432220 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term326 A K k t x i) : @I (K -> Prop) k i.
Proof. exact (proj1 (@lem4431501 A K k t x i h1)). Qed.
Lemma lem4432221 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term326 A K k t x i) : term356 K k i.
Proof. exact (fun h0 : term316 K k i => @lem4432220 A K k t x i h1). Qed.
Lemma lem4432223 (p : Prop) : (term353 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4432224 {K : Type'} (k : K -> Prop) (i : K) : (term356 K k i) = (@I (K -> Prop) k i).
Proof. exact (@lem4432223 (@I (K -> Prop) k i)). Qed.
Lemma lem4432225 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term326 A K k t x i) : @I (K -> Prop) k i.
Proof. exact (EQ_MP (@lem4432224 K k i) (@lem4432221 A K k t x i h1)). Qed.
Lemma lem4432231 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4432232 {A K : Type'} (t : type1470 A K) (x : K -> A) (k : K -> Prop) (_50990 : K) : (term337 A K k t x _50990) = (term357 A K t x k _50990).
Proof. exact (@lem4432231 (term312 A K t x _50990) (term316 K k _50990)). Qed.
Lemma lem4432238 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4432239 {A K : Type'} (t : type1470 A K) (x : K -> A) (k : K -> Prop) (_50990 : K) : (term358 A K k t x _50990) = (term359 A K t x k _50990).
Proof. exact (MK_COMB (@lem4432238) (@lem4432232 A K t x k _50990)). Qed.
Lemma lem4432245 {A K : Type'} (t : type1470 A K) (x : K -> A) (k : K -> Prop) (_50990 : K) : (term357 A K t x k _50990) = (term357 A K t x k _50990).
Proof. exact (eq_refl (term357 A K t x k _50990)). Qed.
Lemma lem4432246 {A K : Type'} (t : type1470 A K) (x : K -> A) (k : K -> Prop) (_50990 : K) : ((term337 A K k t x _50990) = (term357 A K t x k _50990)) = ((term357 A K t x k _50990) = (term357 A K t x k _50990)).
Proof. exact (MK_COMB (@lem4432239 A K t x k _50990) (@lem4432245 A K t x k _50990)). Qed.
Lemma lem4432248 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4432249 (x : Prop) : (x = x) = True.
Proof. exact (@lem4432248 Prop x). Qed.
Lemma lem4432250 {A K : Type'} (t : type1470 A K) (x : K -> A) (k : K -> Prop) (_50990 : K) : ((term357 A K t x k _50990) = (term357 A K t x k _50990)) = True.
Proof. exact (@lem4432249 (term357 A K t x k _50990)). Qed.
Lemma lem4432251 {A K : Type'} (t : type1470 A K) (x : K -> A) (k : K -> Prop) (_50990 : K) : ((term337 A K k t x _50990) = (term357 A K t x k _50990)) = True.
Proof. exact (TRANS (@lem4432246 A K t x k _50990) (@lem4432250 A K t x k _50990)). Qed.
Lemma lem4432252 {A K : Type'} (t : type1470 A K) (x : K -> A) (k : K -> Prop) (_50990 : K) : True = ((term337 A K k t x _50990) = (term357 A K t x k _50990)).
Proof. exact (SYM (@lem4432251 A K t x k _50990)). Qed.
Lemma lem4432253 {A K : Type'} (t : type1470 A K) (x : K -> A) (k : K -> Prop) (_50990 : K) : (term337 A K k t x _50990) = (term357 A K t x k _50990).
Proof. exact (EQ_MP (@lem4432252 A K t x k _50990) (@lem0)). Qed.
Lemma lem4432254 {A K : Type'} (_50990 : K) (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term331 A K i k s t x) : term357 A K t x k _50990.
Proof. exact (EQ_MP (@lem4432253 A K t x k _50990) (@lem4431921 A K _50990 i k s t x h1)). Qed.
Lemma lem4432256 (b : Prop) (a : Prop) : (a \/ b) = (term360 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4432257 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) (_50990 : K) : (term357 A K t x k _50990) = (term361 A K k t x _50990).
Proof. exact (@lem4432256 (term316 K k _50990) (term312 A K t x _50990)). Qed.
Lemma lem4432259 (a : Prop) : (term151 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4432260 {K : Type'} (k : K -> Prop) (_50990 : K) : (term362 K k _50990) = (@I (K -> Prop) k _50990).
Proof. exact (@lem4432259 (@I (K -> Prop) k _50990)). Qed.
Lemma lem4432261 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4432262 {K : Type'} (k : K -> Prop) (_50990 : K) : (term363 K k _50990) = (term364 K k _50990).
Proof. exact (MK_COMB (@lem4432261) (@lem4432260 K k _50990)). Qed.
Lemma lem4432263 {A K : Type'} (t : type1470 A K) (x : K -> A) (_50990 : K) : (term312 A K t x _50990) = (term312 A K t x _50990).
Proof. exact (eq_refl (term312 A K t x _50990)). Qed.
Lemma lem4432264 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) (_50990 : K) : (term361 A K k t x _50990) = (term365 A K k t x _50990).
Proof. exact (MK_COMB (@lem4432262 K k _50990) (@lem4432263 A K t x _50990)). Qed.
Lemma lem4432265 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) (_50990 : K) : (term357 A K t x k _50990) = (term365 A K k t x _50990).
Proof. exact (TRANS (@lem4432257 A K k t x _50990) (@lem4432264 A K k t x _50990)). Qed.
Lemma lem4432268 {A K : Type'} (_50990 : K) (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term331 A K i k s t x) : term365 A K k t x _50990.
Proof. exact (EQ_MP (@lem4432265 A K k t x _50990) (@lem4432254 A K _50990 i k s t x h1)). Qed.
Lemma lem4432269 {A K : Type'} (_50990 : K) (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term331 A K i k s t x) : term365 A K k t x _50990.
Proof. exact (@lem4432268 A K _50990 i k s t x h1). Qed.
Lemma lem4432270 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term331 A K i k s t x) : term365 A K k t x i.
Proof. exact (@lem4432269 A K i i k s t x h1). Qed.
Lemma lem4432273 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term326 A K k t x i) (h2 : term331 A K i k s t x) : term312 A K t x i.
Proof. exact (@lem4432270 A K i k s t x h2 (@lem4432225 A K k t x i h1)). Qed.
Lemma lem4432274 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term326 A K k t x i) (h2 : term331 A K i k s t x) : term366 A K t x i.
Proof. exact (fun h0 : term324 A K t x i => @lem4432273 A K i k s t x h1 h2). Qed.
Lemma lem4432276 (p : Prop) : (term353 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4432277 {A K : Type'} (t : type1470 A K) (x : K -> A) (i : K) : (term366 A K t x i) = (term312 A K t x i).
Proof. exact (@lem4432276 (term312 A K t x i)). Qed.
Lemma lem4432278 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term326 A K k t x i) (h2 : term331 A K i k s t x) : term312 A K t x i.
Proof. exact (EQ_MP (@lem4432277 A K t x i) (@lem4432274 A K i k s t x h1 h2)). Qed.
Lemma lem4432281 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4432283 {A K : Type'} (t : type1470 A K) (x : K -> A) (i : K) : (term324 A K t x i) = (term367 A K t x i).
Proof. exact (@lem4432281 (term312 A K t x i)). Qed.
Lemma lem4432286 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term326 A K k t x i) : term367 A K t x i.
Proof. exact (EQ_MP (@lem4432283 A K t x i) (@lem4431909 A K k t x i h1)). Qed.
Lemma lem4432289 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term326 A K k t x i) (h2 : term331 A K i k s t x) : False.
Proof. exact (@lem4432286 A K k t x i h1 (@lem4432278 A K i k s t x h1 h2)). Qed.
Lemma lem4432290 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term326 A K k t x i) (h2 : term331 A K i k s t x) : term355.
Proof. exact (fun h0 : ~ False => @lem4432289 A K i k s t x h1 h2). Qed.
Lemma lem4432292 (p : Prop) : (term353 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4432293 : term355 = False.
Proof. exact (@lem4432292 False). Qed.
Lemma lem4432294 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term326 A K k t x i) (h2 : term331 A K i k s t x) : False.
Proof. exact (EQ_MP (@lem4432293) (@lem4432290 A K i k s t x h1 h2)). Qed.
Lemma lem4432295 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term216 A K k x) (h2 : term331 A K i k s t x) : (term216 A K k x) = False.
Proof. exact (prop_ext (fun h3 : term216 A K k x => @lem4432218 A K i k s t x h1 h2) (fun h3 : False => @lem4431891 A K k x h1)). Qed.
Lemma lem4432296 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term216 A K k x) (h2 : term331 A K i k s t x) : False.
Proof. exact (EQ_MP (@lem4432295 A K i k s t x h1 h2) (@lem4431891 A K k x h1)). Qed.
Lemma lem4432297 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term216 A K k x) (h2 : term331 A K i k s t x) : (term216 A K k x) = False.
Proof. exact (prop_ext (fun h3 : term216 A K k x => @lem4432119 A K i k s t x h1 h2) (fun h3 : False => @lem4431857 A K k x h1)). Qed.
Lemma lem4432298 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term216 A K k x) (h2 : term331 A K i k s t x) : False.
Proof. exact (EQ_MP (@lem4432297 A K i k s t x h1 h2) (@lem4431857 A K k x h1)). Qed.
Lemma lem4432299 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term324 A K t x i) (h2 : term344 A K k s t x i) (h3 : term335 A K k s t x i) : (term324 A K t x i) = False.
Proof. exact (prop_ext (fun h4 : term324 A K t x i => @lem4432096 A K k s t x i h1 h2 h3) (fun h4 : False => @lem4431853 A K t x i h1)). Qed.
Lemma lem4432300 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term324 A K t x i) (h2 : term344 A K k s t x i) (h3 : term335 A K k s t x i) : False.
Proof. exact (EQ_MP (@lem4432299 A K k s t x i h1 h2 h3) (@lem4431853 A K t x i h1)). Qed.
Lemma lem4432301 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term324 A K s x i) (h2 : term344 A K k s t x i) (h3 : term335 A K k s t x i) : (term324 A K s x i) = False.
Proof. exact (prop_ext (fun h4 : term324 A K s x i => @lem4432020 A K k s t x i h1 h2 h3) (fun h4 : False => @lem4431833 A K s x i h1)). Qed.
Lemma lem4432302 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term324 A K s x i) (h2 : term344 A K k s t x i) (h3 : term335 A K k s t x i) : False.
Proof. exact (EQ_MP (@lem4432301 A K k s t x i h1 h2 h3) (@lem4431833 A K s x i h1)). Qed.
Lemma lem4432303 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term216 A K k x) (h2 : term344 A K k s t x i) : (term216 A K k x) = False.
Proof. exact (prop_ext (fun h3 : term216 A K k x => @lem4431944 A K k s t x i h1 h2) (fun h3 : False => @lem4431813 A K k x h1)). Qed.
Lemma lem4432304 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term216 A K k x) (h2 : term344 A K k s t x i) : False.
Proof. exact (EQ_MP (@lem4432303 A K k s t x i h1 h2) (@lem4431813 A K k x h1)). Qed.
Lemma lem4432305 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term216 A K k x) (h2 : term331 A K i k s t x) : (term216 A K k x) = False.
Proof. exact (prop_ext (fun h3 : term216 A K k x => @lem4432296 A K i k s t x h1 h2) (fun h3 : False => @lem4431722 A K k x h1)). Qed.
Lemma lem4432306 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term216 A K k x) (h2 : term331 A K i k s t x) : False.
Proof. exact (EQ_MP (@lem4432305 A K i k s t x h1 h2) (@lem4431722 A K k x h1)). Qed.
Lemma lem4432307 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term216 A K k x) (h2 : term331 A K i k s t x) : (term216 A K k x) = False.
Proof. exact (prop_ext (fun h3 : term216 A K k x => @lem4432298 A K i k s t x h1 h2) (fun h3 : False => @lem4431656 A K k x h1)). Qed.
Lemma lem4432308 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term216 A K k x) (h2 : term331 A K i k s t x) : False.
Proof. exact (EQ_MP (@lem4432307 A K i k s t x h1 h2) (@lem4431656 A K k x h1)). Qed.
Lemma lem4432309 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term324 A K t x i) (h2 : term344 A K k s t x i) (h3 : term335 A K k s t x i) : (term324 A K t x i) = False.
Proof. exact (prop_ext (fun h4 : term324 A K t x i => @lem4432300 A K k s t x i h1 h2 h3) (fun h4 : False => @lem4431625 A K t x i h1)). Qed.
Lemma lem4432310 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term324 A K t x i) (h2 : term344 A K k s t x i) (h3 : term335 A K k s t x i) : False.
Proof. exact (EQ_MP (@lem4432309 A K k s t x i h1 h2 h3) (@lem4431625 A K t x i h1)). Qed.
Lemma lem4432311 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term324 A K s x i) (h2 : term344 A K k s t x i) (h3 : term335 A K k s t x i) : (term324 A K s x i) = False.
Proof. exact (prop_ext (fun h4 : term324 A K s x i => @lem4432302 A K k s t x i h1 h2 h3) (fun h4 : False => @lem4431583 A K s x i h1)). Qed.
Lemma lem4432312 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term324 A K s x i) (h2 : term344 A K k s t x i) (h3 : term335 A K k s t x i) : False.
Proof. exact (EQ_MP (@lem4432311 A K k s t x i h1 h2 h3) (@lem4431583 A K s x i h1)). Qed.
Lemma lem4432313 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term216 A K k x) (h2 : term344 A K k s t x i) : (term216 A K k x) = False.
Proof. exact (prop_ext (fun h3 : term216 A K k x => @lem4432304 A K k s t x i h1 h2) (fun h3 : False => @lem4431541 A K k x h1)). Qed.
Lemma lem4432314 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term216 A K k x) (h2 : term344 A K k s t x i) : False.
Proof. exact (EQ_MP (@lem4432313 A K k s t x i h1 h2) (@lem4431541 A K k x h1)). Qed.
Lemma lem4432315 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term216 A K k x) (h2 : term331 A K i k s t x) : (term216 A K k x) = False.
Proof. exact (prop_ext (fun h3 : term216 A K k x => @lem4432306 A K i k s t x h1 h2) (fun h3 : False => @lem4431722 A K k x h1)). Qed.
Lemma lem4432316 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term216 A K k x) (h2 : term331 A K i k s t x) : False.
Proof. exact (EQ_MP (@lem4432315 A K i k s t x h1 h2) (@lem4431722 A K k x h1)). Qed.
Lemma lem4432317 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term216 A K k x) (h2 : term331 A K i k s t x) : (term216 A K k x) = False.
Proof. exact (prop_ext (fun h3 : term216 A K k x => @lem4432308 A K i k s t x h1 h2) (fun h3 : False => @lem4431656 A K k x h1)). Qed.
Lemma lem4432318 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term216 A K k x) (h2 : term331 A K i k s t x) : False.
Proof. exact (EQ_MP (@lem4432317 A K i k s t x h1 h2) (@lem4431656 A K k x h1)). Qed.
Lemma lem4432319 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term324 A K t x i) (h2 : term344 A K k s t x i) (h3 : term335 A K k s t x i) : (term324 A K t x i) = False.
Proof. exact (prop_ext (fun h4 : term324 A K t x i => @lem4432310 A K k s t x i h1 h2 h3) (fun h4 : False => @lem4431625 A K t x i h1)). Qed.
Lemma lem4432320 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term324 A K t x i) (h2 : term344 A K k s t x i) (h3 : term335 A K k s t x i) : False.
Proof. exact (EQ_MP (@lem4432319 A K k s t x i h1 h2 h3) (@lem4431625 A K t x i h1)). Qed.
Lemma lem4432321 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term324 A K s x i) (h2 : term344 A K k s t x i) (h3 : term335 A K k s t x i) : (term324 A K s x i) = False.
Proof. exact (prop_ext (fun h4 : term324 A K s x i => @lem4432312 A K k s t x i h1 h2 h3) (fun h4 : False => @lem4431583 A K s x i h1)). Qed.
Lemma lem4432322 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term324 A K s x i) (h2 : term344 A K k s t x i) (h3 : term335 A K k s t x i) : False.
Proof. exact (EQ_MP (@lem4432321 A K k s t x i h1 h2 h3) (@lem4431583 A K s x i h1)). Qed.
Lemma lem4432323 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term216 A K k x) (h2 : term344 A K k s t x i) : (term216 A K k x) = False.
Proof. exact (prop_ext (fun h3 : term216 A K k x => @lem4432314 A K k s t x i h1 h2) (fun h3 : False => @lem4431541 A K k x h1)). Qed.
Lemma lem4432324 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term216 A K k x) (h2 : term344 A K k s t x i) : False.
Proof. exact (EQ_MP (@lem4432323 A K k s t x i h1 h2) (@lem4431541 A K k x h1)). Qed.
Lemma lem4432325 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term331 A K i k s t x) (h2 : term327 A K k t x i) : False.
Proof. exact (or_elim (@lem4431495 A K k t x i h2) (fun h0 : term216 A K k x => @lem4432316 A K i k s t x h0 h1) (fun h0 : term326 A K k t x i => @lem4432294 A K i k s t x h0 h1)). Qed.
Lemma lem4432326 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (x : K -> A) (i : K) (h1 : term331 A K i k s t x) (h2 : term327 A K k s x i) : False.
Proof. exact (or_elim (@lem4431494 A K k s x i h2) (fun h0 : term216 A K k x => @lem4432318 A K i k s t x h0 h1) (fun h0 : term326 A K k s x i => @lem4432195 A K i k s t x h0 h1)). Qed.
Lemma lem4432327 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term331 A K i k s t x) : False.
Proof. exact (or_elim (@lem4431491 A K i k s t x h1) (fun h0 : term327 A K k s x i => @lem4432326 A K t k s x i h1 h0) (fun h0 : term327 A K k t x i => @lem4432325 A K s k t x i h1 h0)). Qed.
Lemma lem4432328 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term344 A K k s t x i) (h2 : term335 A K k s t x i) : False.
Proof. exact (or_elim (@lem4431486 A K k s t x i h2) (fun h0 : term324 A K s x i => @lem4432322 A K k s t x i h0 h1 h2) (fun h0 : term324 A K t x i => @lem4432320 A K k s t x i h0 h1 h2)). Qed.
Lemma lem4432329 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (i : K) (h1 : term344 A K k s t x i) : False.
Proof. exact (or_elim (@lem4431476 A K k s t x i h1) (fun h0 : term216 A K k x => @lem4432324 A K k s t x i h0 h1) (fun h0 : term335 A K k s t x i => @lem4432328 A K k s t x i h1 h0)). Qed.
Lemma lem4432330 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term308 A K i k s t x) : False.
Proof. exact (or_elim (@lem4431473 A K i k s t x h1) (fun h0 : term344 A K k s t x i => @lem4432329 A K k s t x i h0) (fun h0 : term331 A K i k s t x => @lem4432327 A K i k s t x h0)). Qed.
Lemma lem4432331 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term153 A K k s t x) : False.
Proof. exact (ex_elim (@lem4431211 A K k s t x h1) (fun i : K => fun h0 : term310 A K k s t x i => @lem4432330 A K i k s t x h0)). Qed.
Lemma lem4432332 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term153 A K k s t x) : (term153 A K k s t x) = False.
Proof. exact (prop_ext (fun h2 : term153 A K k s t x => @lem4432331 A K k s t x h1) (fun h2 : False => @lem4430665 A K k s t x h1)). Qed.
Lemma lem4432333 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) (h1 : term153 A K k s t x) : False.
Proof. exact (EQ_MP (@lem4432332 A K k s t x h1) (@lem4430665 A K k s t x h1)). Qed.
Lemma lem4432334 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : term152 A K k s t x.
Proof. exact (fun h0 : term153 A K k s t x => @lem4432333 A K k s t x h0). Qed.
Lemma lem4432335 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (x : K -> A) : (term127 A K s k t x) = (term135 A K k s t x).
Proof. exact (EQ_MP (@lem4430664 A K k s t x) (@lem4432334 A K k s t x)). Qed.
Lemma lem4432340 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : term137 A K k s t.
Proof. exact (fun x : K -> A => @lem4432335 A K k s t x). Qed.
Lemma lem4432345 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term139 A K k s.
Proof. exact (fun t : type1470 A K => @lem4432340 A K k s t). Qed.
Lemma lem4432350 {A K : Type'} (k : K -> Prop) : term141 A K k.
Proof. exact (fun s : type1470 A K => @lem4432345 A K k s). Qed.
Lemma lem4432355 {A K : Type'} : term143 A K.
Proof. exact (fun k : K -> Prop => @lem4432350 A K k). Qed.
Lemma lem4432356 {A K : Type'} : term145 A K.
Proof. exact (EQ_MP (@lem4430660 A K) (@lem4432355 A K)). Qed.
Lemma lem4432358 {A K : Type'} : term145 A K.
Proof. exact (@lem4430485 A K (@lem4432356 A K)). Qed.
Lemma lem4432359 {A K : Type'} (h1 : term146 A K) : False.
Proof. exact (@lem4432358 A K (@lem4430469 A K h1)). Qed.
Lemma lem4432360 {A K : Type'} (h1 : term146 A K) : (term146 A K) = False.
Proof. exact (prop_ext (fun h2 : term146 A K => @lem4432359 A K h1) (fun h2 : False => @lem4430469 A K h1)). Qed.
Lemma lem4432361 {A K : Type'} (h1 : term146 A K) : False.
Proof. exact (EQ_MP (@lem4432360 A K h1) (@lem4430469 A K h1)). Qed.
Lemma lem4432362 {A K : Type'} : term145 A K.
Proof. exact (fun h0 : term146 A K => @lem4432361 A K h0). Qed.
Lemma lem4432363 {A K : Type'} : term143 A K.
Proof. exact (EQ_MP (@lem4430468 A K) (@lem4432362 A K)). Qed.
Lemma lem4432365 {A K : Type'} : term115 A K.
Proof. exact (EQ_MP (@lem4430464 A K) (@lem4432363 A K)). Qed.
Lemma lem4432366 {A K : Type'} : term114 A K.
Proof. exact (EQ_MP (@lem4430248 A K) (@lem4432365 A K)). Qed.
