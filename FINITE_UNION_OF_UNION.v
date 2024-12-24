Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_UNION_OF_UNION_term_abbrevs.
Require Import FINITE_EMPTY_spec.
Require Import FINITE_INSERT_spec.
Require Import FINITE_UNION_OF_UNIONS_spec.
Require Import FORALL_IN_INSERT_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import UNIONS_2_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1822_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem4887038 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem4887039 {A : Type'} (x : A) : (term0 A x) = (term1 A x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem4887040 {A : Type'} (x : A) : term1 A x.
Proof. exact (EQ_MP (@lem4887039 A x) (@lem4887038 A x)). Qed.
Lemma lem4887041 {A : Type'} (x : A) : term2 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem4887043 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = ((@FINITE _92140 (@EMPTY _92140)) = True).
Proof. exact (@lem7 (@FINITE _92140 (@EMPTY _92140))). Qed.
Lemma lem4887045 {A : Type'} (h1 : term3 A) : term3 A.
Proof. exact (h1). Qed.
Lemma lem4887046 {A : Type'} (P : type686 A) (h1 : term3 A) : term4 A P.
Proof. exact (@lem4887045 A h1 P). Qed.
Lemma lem4887047 {A : Type'} (P : type686 A) : (term4 A P) = (term5 A P).
Proof. exact (eq_refl (term4 A P)). Qed.
Lemma lem4887048 {A : Type'} (P : type686 A) (h1 : term3 A) : term5 A P.
Proof. exact (EQ_MP (@lem4887047 A P) (@lem4887046 A P h1)). Qed.
Lemma lem4887049 {A : Type'} (P : type686 A) (u : type686 A) (h1 : term3 A) : term6 A P u.
Proof. exact (@lem4887048 A P h1 u). Qed.
Lemma lem4887050 {A : Type'} (P : type686 A) (u : type686 A) : (term6 A P u) = (term7 A P u).
Proof. exact (eq_refl (term6 A P u)). Qed.
Lemma lem4887051 {A : Type'} (P : type686 A) (u : type686 A) (h1 : term3 A) : term7 A P u.
Proof. exact (EQ_MP (@lem4887050 A P u) (@lem4887049 A P u h1)). Qed.
Lemma lem4887052 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term8 A u P) : term8 A u P.
Proof. exact (h1). Qed.
Lemma lem4887053 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term3 A) (h2 : term8 A u P) : term9 A P u.
Proof. exact (@lem4887051 A P u h1 (@lem4887052 A u P h2)). Qed.
Lemma lem4887054 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term8 A u P) : term10 A P u.
Proof. exact (fun h0 : term3 A => @lem4887053 A u P h0 h1). Qed.
Lemma lem4887055 {A : Type'} (h1 : term3 A) : term3 A.
Proof. exact (h1). Qed.
Lemma lem4887056 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term3 A) (h2 : term8 A u P) : term9 A P u.
Proof. exact (@lem4887054 A u P h2 (@lem4887055 A h1)). Qed.
Lemma lem4887057 {A : Type'} (P : type686 A) (u : type686 A) (h1 : term3 A) : term7 A P u.
Proof. exact (fun h0 : term8 A u P => @lem4887056 A u P h1 h0). Qed.
Lemma lem4887058 {A : Type'} (P : type686 A) (h1 : term3 A) : term5 A P.
Proof. exact (fun u : type686 A => @lem4887057 A P u h1). Qed.
Lemma lem4887059 {A : Type'} (h1 : term3 A) : term3 A.
Proof. exact (fun P : type686 A => @lem4887058 A P h1). Qed.
Lemma lem4887060 {A : Type'} : term11 A.
Proof. exact (fun h0 : term3 A => @lem4887059 A h0). Qed.
Lemma lem4887061 {A : Type'} : term3 A.
Proof. exact (@lem4887060 A (@lem4887037 A)). Qed.
Lemma lem4887062 {A : Type'} (P : type686 A) : term4 A P.
Proof. exact (@lem4887061 A P). Qed.
Lemma lem4887063 {A : Type'} (P : type686 A) : (term4 A P) = (term5 A P).
Proof. exact (eq_refl (term4 A P)). Qed.
Lemma lem4887064 {A : Type'} (P : type686 A) : term5 A P.
Proof. exact (EQ_MP (@lem4887063 A P) (@lem4887062 A P)). Qed.
Lemma lem4887065 {A : Type'} (P : type686 A) (u : type686 A) : term6 A P u.
Proof. exact (@lem4887064 A P u). Qed.
Lemma lem4887066 {A : Type'} (P : type686 A) (u : type686 A) : (term6 A P u) = (term7 A P u).
Proof. exact (eq_refl (term6 A P u)). Qed.
Lemma lem4887068 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (h1 : (term12 _86827 s t) = (@UNION _86827 s t)) : (term12 _86827 s t) = (@UNION _86827 s t).
Proof. exact (h1). Qed.
Lemma lem4887069 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (h1 : (term12 _86827 s t) = (@UNION _86827 s t)) : (@UNION _86827 s t) = (term12 _86827 s t).
Proof. exact (SYM (@lem4887068 _86827 s t h1)). Qed.
Lemma lem4887070 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (h1 : (@UNION _86827 s t) = (term12 _86827 s t)) : (@UNION _86827 s t) = (term12 _86827 s t).
Proof. exact (h1). Qed.
Lemma lem4887071 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) (h1 : (@UNION _86827 s t) = (term12 _86827 s t)) : (term12 _86827 s t) = (@UNION _86827 s t).
Proof. exact (SYM (@lem4887070 _86827 s t h1)). Qed.
Lemma lem4887072 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) : ((term12 _86827 s t) = (@UNION _86827 s t)) = ((@UNION _86827 s t) = (term12 _86827 s t)).
Proof. exact (prop_ext (fun h1 : (term12 _86827 s t) = (@UNION _86827 s t) => @lem4887069 _86827 s t h1) (fun h1 : (@UNION _86827 s t) = (term12 _86827 s t) => @lem4887071 _86827 s t h1)). Qed.
Lemma lem4887074 {_112456 : Type'} (s : _112456 -> Prop) (P : type686 _112456) (t : _112456 -> Prop) (h1 : term13 _112456 s P t) : term13 _112456 s P t.
Proof. exact (h1). Qed.
Lemma lem4887075 {_112456 : Type'} (P : type686 _112456) (t : _112456 -> Prop) (h1 : @UNION_OF _112456 (@FINITE (_112456 -> Prop)) P t) : @UNION_OF _112456 (@FINITE (_112456 -> Prop)) P t.
Proof. exact (h1). Qed.
Lemma lem4887076 {_112456 : Type'} (P : type686 _112456) (s : _112456 -> Prop) (h1 : @UNION_OF _112456 (@FINITE (_112456 -> Prop)) P s) : @UNION_OF _112456 (@FINITE (_112456 -> Prop)) P s.
Proof. exact (h1). Qed.
Lemma lem4887078 {_86827 : Type'} (s : _86827 -> Prop) (t : _86827 -> Prop) : (@UNION _86827 s t) = (term12 _86827 s t).
Proof. exact (EQ_MP (@lem4887072 _86827 s t) (@lem3323992 _86827 s t)). Qed.
Lemma lem4887079 {_112456 : Type'} (s : _112456 -> Prop) (t : _112456 -> Prop) : (@UNION _112456 s t) = (term12 _112456 s t).
Proof. exact (@lem4887078 _112456 s t). Qed.
Lemma lem4887080 {_112456 : Type'} (P : type686 _112456) : (@UNION_OF _112456 (@FINITE (_112456 -> Prop)) P) = (@UNION_OF _112456 (@FINITE (_112456 -> Prop)) P).
Proof. exact (eq_refl (@UNION_OF _112456 (@FINITE (_112456 -> Prop)) P)). Qed.
Lemma lem4887081 {_112456 : Type'} (P : type686 _112456) (s : _112456 -> Prop) (t : _112456 -> Prop) : (term14 _112456 P s t) = (term15 _112456 P s t).
Proof. exact (MK_COMB (@lem4887080 _112456 P) (@lem4887079 _112456 s t)). Qed.
Lemma lem4887082 {_112456 : Type'} (P : type686 _112456) (s : _112456 -> Prop) (t : _112456 -> Prop) : (term15 _112456 P s t) = (term14 _112456 P s t).
Proof. exact (SYM (@lem4887081 _112456 P s t)). Qed.
Lemma lem4887084 {A : Type'} (P : type686 A) (u : type686 A) : term7 A P u.
Proof. exact (EQ_MP (@lem4887066 A P u) (@lem4887065 A P u)). Qed.
Lemma lem4887085 {_112456 : Type'} (P : type686 _112456) (u : type686 _112456) : term7 _112456 P u.
Proof. exact (@lem4887084 _112456 P u). Qed.
Lemma lem4887086 {_112456 : Type'} (P : type686 _112456) (s : _112456 -> Prop) (t : _112456 -> Prop) : term16 _112456 P s t.
Proof. exact (@lem4887085 _112456 P (term17 _112456 s t)). Qed.
Lemma lem4887087 {_83983 : Type'} (P : _83983 -> Prop) : term18 _83983 P.
Proof. exact (@lem3207453 _83983 P). Qed.
Lemma lem4887088 {_83983 : Type'} (P : _83983 -> Prop) : (term18 _83983 P) = (term19 _83983 P).
Proof. exact (eq_refl (term18 _83983 P)). Qed.
Lemma lem4887089 {_83983 : Type'} (P : _83983 -> Prop) : term19 _83983 P.
Proof. exact (EQ_MP (@lem4887088 _83983 P) (@lem4887087 _83983 P)). Qed.
Lemma lem4887090 {_83983 : Type'} (P : _83983 -> Prop) (a : _83983) : term20 _83983 P a.
Proof. exact (@lem4887089 _83983 P a). Qed.
Lemma lem4887091 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) : (term20 _83983 P a) = (term21 _83983 a P).
Proof. exact (eq_refl (term20 _83983 P a)). Qed.
Lemma lem4887092 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) : term21 _83983 a P.
Proof. exact (EQ_MP (@lem4887091 _83983 a P) (@lem4887090 _83983 P a)). Qed.
Lemma lem4887093 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) (s : _83983 -> Prop) : term22 _83983 a P s.
Proof. exact (@lem4887092 _83983 a P s). Qed.
Lemma lem4887094 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term22 _83983 a P s) = ((term23 _83983 a s P) = (term24 _83983 a s P)).
Proof. exact (eq_refl (term22 _83983 a P s)). Qed.
Lemma lem4887096 {A : Type'} (s : A -> Prop) : term25 A s.
Proof. exact (@lem3608316 A s). Qed.
Lemma lem4887097 {A : Type'} (s : A -> Prop) : (term25 A s) = (term26 A s).
Proof. exact (eq_refl (term25 A s)). Qed.
Lemma lem4887098 {A : Type'} (s : A -> Prop) : term26 A s.
Proof. exact (EQ_MP (@lem4887097 A s) (@lem4887096 A s)). Qed.
Lemma lem4887099 {A : Type'} (s : A -> Prop) (x : A) : term27 A s x.
Proof. exact (@lem4887098 A s x). Qed.
Lemma lem4887100 {A : Type'} (x : A) (s : A -> Prop) : (term27 A s x) = ((term28 A x s) = (@FINITE A s)).
Proof. exact (eq_refl (term27 A s x)). Qed.
Lemma lem4887102 {_112456 : Type'} (P : type686 _112456) (s : _112456 -> Prop) : (@UNION_OF _112456 (@FINITE (_112456 -> Prop)) P s) = ((@UNION_OF _112456 (@FINITE (_112456 -> Prop)) P s) = True).
Proof. exact (@lem7 (@UNION_OF _112456 (@FINITE (_112456 -> Prop)) P s)). Qed.
Lemma lem4887104 {_112456 : Type'} (P : type686 _112456) (t : _112456 -> Prop) : (@UNION_OF _112456 (@FINITE (_112456 -> Prop)) P t) = ((@UNION_OF _112456 (@FINITE (_112456 -> Prop)) P t) = True).
Proof. exact (@lem7 (@UNION_OF _112456 (@FINITE (_112456 -> Prop)) P t)). Qed.
Lemma lem4887109 {A : Type'} (x : A) (s : A -> Prop) : (term28 A x s) = (@FINITE A s).
Proof. exact (EQ_MP (@lem4887100 A x s) (@lem4887099 A s x)). Qed.
Lemma lem4887110 {_112456 : Type'} (x : _112456 -> Prop) (s : type686 _112456) : (term29 _112456 x s) = (@FINITE (_112456 -> Prop) s).
Proof. exact (@lem4887109 (_112456 -> Prop) x s). Qed.
Lemma lem4887111 {_112456 : Type'} (s : _112456 -> Prop) (t : _112456 -> Prop) : (term30 _112456 s t) = (term31 _112456 t).
Proof. exact (@lem4887110 _112456 s (@INSERT (_112456 -> Prop) t (@EMPTY (_112456 -> Prop)))). Qed.
Lemma lem4887113 {A : Type'} (x : A) (s : A -> Prop) : (term28 A x s) = (@FINITE A s).
Proof. exact (EQ_MP (@lem4887100 A x s) (@lem4887099 A s x)). Qed.
Lemma lem4887114 {_112456 : Type'} (x : _112456 -> Prop) (s : type686 _112456) : (term29 _112456 x s) = (@FINITE (_112456 -> Prop) s).
Proof. exact (@lem4887113 (_112456 -> Prop) x s). Qed.
Lemma lem4887115 {_112456 : Type'} (t : _112456 -> Prop) : (term31 _112456 t) = (@FINITE (_112456 -> Prop) (@EMPTY (_112456 -> Prop))).
Proof. exact (@lem4887114 _112456 t (@EMPTY (_112456 -> Prop))). Qed.
Lemma lem4887116 {_112456 : Type'} (s : _112456 -> Prop) (t : _112456 -> Prop) : (term30 _112456 s t) = (@FINITE (_112456 -> Prop) (@EMPTY (_112456 -> Prop))).
Proof. exact (TRANS (@lem4887111 _112456 s t) (@lem4887115 _112456 t)). Qed.
Lemma lem4887117 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4887118 {_112456 : Type'} (s : _112456 -> Prop) (t : _112456 -> Prop) : (term32 _112456 s t) = (term33 _112456).
Proof. exact (MK_COMB (@lem4887117) (@lem4887116 _112456 s t)). Qed.
Lemma lem4887120 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term23 _83983 a s P) = (term24 _83983 a s P).
Proof. exact (EQ_MP (@lem4887094 _83983 a s P) (@lem4887093 _83983 a P s)). Qed.
Lemma lem4887121 {_112456 : Type'} (a : _112456 -> Prop) (s : type686 _112456) (P : type686 _112456) : (term34 _112456 a s P) = (term35 _112456 a s P).
Proof. exact (@lem4887120 (_112456 -> Prop) a s P). Qed.
Lemma lem4887122 {_112456 : Type'} (s : _112456 -> Prop) (t : _112456 -> Prop) (P : type686 _112456) : (term36 _112456 s t P) = (term37 _112456 s t P).
Proof. exact (@lem4887121 _112456 s (@INSERT (_112456 -> Prop) t (@EMPTY (_112456 -> Prop))) (term38 _112456 P)). Qed.
Lemma lem4887123 {_112456 : Type'} (P : type686 _112456) (s' : _112456 -> Prop) : (term39 _112456 P s') = (@UNION_OF _112456 (@FINITE (_112456 -> Prop)) P s').
Proof. exact (eq_refl (term39 _112456 P s')). Qed.
Lemma lem4887124 {_112456 : Type'} (s' : _112456 -> Prop) (s : _112456 -> Prop) (t : _112456 -> Prop) : (term40 _112456 s' s t) = (term40 _112456 s' s t).
Proof. exact (eq_refl (term40 _112456 s' s t)). Qed.
Lemma lem4887125 {_112456 : Type'} (s : _112456 -> Prop) (t : _112456 -> Prop) (P : type686 _112456) (s' : _112456 -> Prop) : (term41 _112456 s t P s') = (term42 _112456 s t P s').
Proof. exact (MK_COMB (@lem4887124 _112456 s' s t) (@lem4887123 _112456 P s')). Qed.
Lemma lem4887126 {_112456 : Type'} (s : _112456 -> Prop) (t : _112456 -> Prop) (P : type686 _112456) : (term43 _112456 s t P) = (term44 _112456 s t P).
Proof. exact (fun_ext (fun s' : _112456 -> Prop => @lem4887125 _112456 s t P s')). Qed.
Lemma lem4887127 {_112456 : Type'} : (@all (_112456 -> Prop)) = (@all (_112456 -> Prop)).
Proof. exact (eq_refl (@all (_112456 -> Prop))). Qed.
Lemma lem4887128 {_112456 : Type'} (s : _112456 -> Prop) (t : _112456 -> Prop) (P : type686 _112456) : (term36 _112456 s t P) = (term45 _112456 s t P).
Proof. exact (MK_COMB (@lem4887127 _112456) (@lem4887126 _112456 s t P)). Qed.
Lemma lem4887129 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4887130 {_112456 : Type'} (s : _112456 -> Prop) (t : _112456 -> Prop) (P : type686 _112456) : (term46 _112456 s t P) = (term47 _112456 s t P).
Proof. exact (MK_COMB (@lem4887129) (@lem4887128 _112456 s t P)). Qed.
Lemma lem4887131 {_112456 : Type'} (P : type686 _112456) (s : _112456 -> Prop) : (term39 _112456 P s) = (@UNION_OF _112456 (@FINITE (_112456 -> Prop)) P s).
Proof. exact (eq_refl (term39 _112456 P s)). Qed.
Lemma lem4887132 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4887133 {_112456 : Type'} (P : type686 _112456) (s : _112456 -> Prop) : (term48 _112456 P s) = (term49 _112456 P s).
Proof. exact (MK_COMB (@lem4887132) (@lem4887131 _112456 P s)). Qed.
Lemma lem4887134 {_112456 : Type'} (P : type686 _112456) (s' : _112456 -> Prop) : (term39 _112456 P s') = (@UNION_OF _112456 (@FINITE (_112456 -> Prop)) P s').
Proof. exact (eq_refl (term39 _112456 P s')). Qed.
Lemma lem4887135 {_112456 : Type'} (s' : _112456 -> Prop) (t : _112456 -> Prop) : (term50 _112456 s' t) = (term50 _112456 s' t).
Proof. exact (eq_refl (term50 _112456 s' t)). Qed.
Lemma lem4887136 {_112456 : Type'} (t : _112456 -> Prop) (P : type686 _112456) (s' : _112456 -> Prop) : (term51 _112456 t P s') = (term52 _112456 t P s').
Proof. exact (MK_COMB (@lem4887135 _112456 s' t) (@lem4887134 _112456 P s')). Qed.
Lemma lem4887137 {_112456 : Type'} (t : _112456 -> Prop) (P : type686 _112456) : (term53 _112456 t P) = (term54 _112456 t P).
Proof. exact (fun_ext (fun s' : _112456 -> Prop => @lem4887136 _112456 t P s')). Qed.
Lemma lem4887138 {_112456 : Type'} : (@all (_112456 -> Prop)) = (@all (_112456 -> Prop)).
Proof. exact (eq_refl (@all (_112456 -> Prop))). Qed.
Lemma lem4887139 {_112456 : Type'} (t : _112456 -> Prop) (P : type686 _112456) : (term55 _112456 t P) = (term56 _112456 t P).
Proof. exact (MK_COMB (@lem4887138 _112456) (@lem4887137 _112456 t P)). Qed.
Lemma lem4887140 {_112456 : Type'} (s : _112456 -> Prop) (t : _112456 -> Prop) (P : type686 _112456) : (term37 _112456 s t P) = (term57 _112456 s t P).
Proof. exact (MK_COMB (@lem4887133 _112456 P s) (@lem4887139 _112456 t P)). Qed.
Lemma lem4887141 {_112456 : Type'} (s : _112456 -> Prop) (t : _112456 -> Prop) (P : type686 _112456) : ((term36 _112456 s t P) = (term37 _112456 s t P)) = ((term45 _112456 s t P) = (term57 _112456 s t P)).
Proof. exact (MK_COMB (@lem4887130 _112456 s t P) (@lem4887140 _112456 s t P)). Qed.
Lemma lem4887142 {_112456 : Type'} (s : _112456 -> Prop) (t : _112456 -> Prop) (P : type686 _112456) : (term45 _112456 s t P) = (term57 _112456 s t P).
Proof. exact (EQ_MP (@lem4887141 _112456 s t P) (@lem4887122 _112456 s t P)). Qed.
Lemma lem4887146 {_112456 : Type'} (P : type686 _112456) (s : _112456 -> Prop) (h1 : @UNION_OF _112456 (@FINITE (_112456 -> Prop)) P s) : (@UNION_OF _112456 (@FINITE (_112456 -> Prop)) P s) = True.
Proof. exact (EQ_MP (@lem4887102 _112456 P s) (@lem4887076 _112456 P s h1)). Qed.
Lemma lem4887147 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4887148 {_112456 : Type'} (P : type686 _112456) (s : _112456 -> Prop) (h1 : @UNION_OF _112456 (@FINITE (_112456 -> Prop)) P s) : (term49 _112456 P s) = (and True).
Proof. exact (MK_COMB (@lem4887147) (@lem4887146 _112456 P s h1)). Qed.
Lemma lem4887150 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term23 _83983 a s P) = (term24 _83983 a s P).
Proof. exact (EQ_MP (@lem4887094 _83983 a s P) (@lem4887093 _83983 a P s)). Qed.
Lemma lem4887151 {_112456 : Type'} (a : _112456 -> Prop) (s : type686 _112456) (P : type686 _112456) : (term34 _112456 a s P) = (term35 _112456 a s P).
Proof. exact (@lem4887150 (_112456 -> Prop) a s P). Qed.
Lemma lem4887152 {_112456 : Type'} (t : _112456 -> Prop) (P : type686 _112456) : (term55 _112456 t P) = (term58 _112456 t P).
Proof. exact (@lem4887151 _112456 t (@EMPTY (_112456 -> Prop)) (term38 _112456 P)). Qed.
Lemma lem4887153 {_112456 : Type'} (P : type686 _112456) (s' : _112456 -> Prop) : (term39 _112456 P s') = (@UNION_OF _112456 (@FINITE (_112456 -> Prop)) P s').
Proof. exact (eq_refl (term39 _112456 P s')). Qed.
Lemma lem4887154 {_112456 : Type'} (s' : _112456 -> Prop) (t : _112456 -> Prop) : (term50 _112456 s' t) = (term50 _112456 s' t).
Proof. exact (eq_refl (term50 _112456 s' t)). Qed.
Lemma lem4887155 {_112456 : Type'} (t : _112456 -> Prop) (P : type686 _112456) (s' : _112456 -> Prop) : (term51 _112456 t P s') = (term52 _112456 t P s').
Proof. exact (MK_COMB (@lem4887154 _112456 s' t) (@lem4887153 _112456 P s')). Qed.
Lemma lem4887156 {_112456 : Type'} (t : _112456 -> Prop) (P : type686 _112456) : (term53 _112456 t P) = (term54 _112456 t P).
Proof. exact (fun_ext (fun s' : _112456 -> Prop => @lem4887155 _112456 t P s')). Qed.
Lemma lem4887157 {_112456 : Type'} : (@all (_112456 -> Prop)) = (@all (_112456 -> Prop)).
Proof. exact (eq_refl (@all (_112456 -> Prop))). Qed.
Lemma lem4887158 {_112456 : Type'} (t : _112456 -> Prop) (P : type686 _112456) : (term55 _112456 t P) = (term56 _112456 t P).
Proof. exact (MK_COMB (@lem4887157 _112456) (@lem4887156 _112456 t P)). Qed.
Lemma lem4887159 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4887160 {_112456 : Type'} (t : _112456 -> Prop) (P : type686 _112456) : (term59 _112456 t P) = (term60 _112456 t P).
Proof. exact (MK_COMB (@lem4887159) (@lem4887158 _112456 t P)). Qed.
Lemma lem4887161 {_112456 : Type'} (P : type686 _112456) (t : _112456 -> Prop) : (term39 _112456 P t) = (@UNION_OF _112456 (@FINITE (_112456 -> Prop)) P t).
Proof. exact (eq_refl (term39 _112456 P t)). Qed.
Lemma lem4887162 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4887163 {_112456 : Type'} (P : type686 _112456) (t : _112456 -> Prop) : (term48 _112456 P t) = (term49 _112456 P t).
Proof. exact (MK_COMB (@lem4887162) (@lem4887161 _112456 P t)). Qed.
Lemma lem4887164 {_112456 : Type'} (P : type686 _112456) (s' : _112456 -> Prop) : (term39 _112456 P s') = (@UNION_OF _112456 (@FINITE (_112456 -> Prop)) P s').
Proof. exact (eq_refl (term39 _112456 P s')). Qed.
Lemma lem4887165 {_112456 : Type'} (s' : _112456 -> Prop) : (term61 _112456 s') = (term61 _112456 s').
Proof. exact (eq_refl (term61 _112456 s')). Qed.
Lemma lem4887166 {_112456 : Type'} (P : type686 _112456) (s' : _112456 -> Prop) : (term62 _112456 P s') = (term63 _112456 P s').
Proof. exact (MK_COMB (@lem4887165 _112456 s') (@lem4887164 _112456 P s')). Qed.
Lemma lem4887167 {_112456 : Type'} (P : type686 _112456) : (term64 _112456 P) = (term65 _112456 P).
Proof. exact (fun_ext (fun s' : _112456 -> Prop => @lem4887166 _112456 P s')). Qed.
Lemma lem4887168 {_112456 : Type'} : (@all (_112456 -> Prop)) = (@all (_112456 -> Prop)).
Proof. exact (eq_refl (@all (_112456 -> Prop))). Qed.
Lemma lem4887169 {_112456 : Type'} (P : type686 _112456) : (term66 _112456 P) = (term67 _112456 P).
Proof. exact (MK_COMB (@lem4887168 _112456) (@lem4887167 _112456 P)). Qed.
Lemma lem4887170 {_112456 : Type'} (t : _112456 -> Prop) (P : type686 _112456) : (term58 _112456 t P) = (term68 _112456 t P).
Proof. exact (MK_COMB (@lem4887163 _112456 P t) (@lem4887169 _112456 P)). Qed.
Lemma lem4887171 {_112456 : Type'} (t : _112456 -> Prop) (P : type686 _112456) : ((term55 _112456 t P) = (term58 _112456 t P)) = ((term56 _112456 t P) = (term68 _112456 t P)).
Proof. exact (MK_COMB (@lem4887160 _112456 t P) (@lem4887170 _112456 t P)). Qed.
Lemma lem4887172 {_112456 : Type'} (t : _112456 -> Prop) (P : type686 _112456) : (term56 _112456 t P) = (term68 _112456 t P).
Proof. exact (EQ_MP (@lem4887171 _112456 t P) (@lem4887152 _112456 t P)). Qed.
Lemma lem4887176 {_112456 : Type'} (P : type686 _112456) (t : _112456 -> Prop) (h1 : @UNION_OF _112456 (@FINITE (_112456 -> Prop)) P t) : (@UNION_OF _112456 (@FINITE (_112456 -> Prop)) P t) = True.
Proof. exact (EQ_MP (@lem4887104 _112456 P t) (@lem4887075 _112456 P t h1)). Qed.
Lemma lem4887177 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4887178 {_112456 : Type'} (P : type686 _112456) (t : _112456 -> Prop) (h1 : @UNION_OF _112456 (@FINITE (_112456 -> Prop)) P t) : (term49 _112456 P t) = (and True).
Proof. exact (MK_COMB (@lem4887177) (@lem4887176 _112456 P t h1)). Qed.
Lemma lem4887185 {_112456 : Type'} (P : type686 _112456) : (term67 _112456 P) = (term67 _112456 P).
Proof. exact (eq_refl (term67 _112456 P)). Qed.
Lemma lem4887186 {_112456 : Type'} (P : type686 _112456) (t : _112456 -> Prop) (h1 : @UNION_OF _112456 (@FINITE (_112456 -> Prop)) P t) : (term68 _112456 t P) = (term69 _112456 P).
Proof. exact (MK_COMB (@lem4887178 _112456 P t h1) (@lem4887185 _112456 P)). Qed.
Lemma lem4887188 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4887189 {_112456 : Type'} (P : type686 _112456) : (term69 _112456 P) = (term67 _112456 P).
Proof. exact (@lem4887188 (term67 _112456 P)). Qed.
Lemma lem4887196 {_112456 : Type'} (P : type686 _112456) (t : _112456 -> Prop) (h1 : @UNION_OF _112456 (@FINITE (_112456 -> Prop)) P t) : (term68 _112456 t P) = (term67 _112456 P).
Proof. exact (TRANS (@lem4887186 _112456 P t h1) (@lem4887189 _112456 P)). Qed.
Lemma lem4887197 {_112456 : Type'} (P : type686 _112456) (t : _112456 -> Prop) (h1 : @UNION_OF _112456 (@FINITE (_112456 -> Prop)) P t) : (term56 _112456 t P) = (term67 _112456 P).
Proof. exact (TRANS (@lem4887172 _112456 t P) (@lem4887196 _112456 P t h1)). Qed.
Lemma lem4887198 {_112456 : Type'} (s : _112456 -> Prop) (P : type686 _112456) (t : _112456 -> Prop) (h1 : @UNION_OF _112456 (@FINITE (_112456 -> Prop)) P s) (h2 : @UNION_OF _112456 (@FINITE (_112456 -> Prop)) P t) : (term57 _112456 s t P) = (term69 _112456 P).
Proof. exact (MK_COMB (@lem4887148 _112456 P s h1) (@lem4887197 _112456 P t h2)). Qed.
Lemma lem4887200 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4887201 {_112456 : Type'} (P : type686 _112456) : (term69 _112456 P) = (term67 _112456 P).
Proof. exact (@lem4887200 (term67 _112456 P)). Qed.
Lemma lem4887208 {_112456 : Type'} (s : _112456 -> Prop) (P : type686 _112456) (t : _112456 -> Prop) (h1 : @UNION_OF _112456 (@FINITE (_112456 -> Prop)) P s) (h2 : @UNION_OF _112456 (@FINITE (_112456 -> Prop)) P t) : (term57 _112456 s t P) = (term67 _112456 P).
Proof. exact (TRANS (@lem4887198 _112456 s P t h1 h2) (@lem4887201 _112456 P)). Qed.
Lemma lem4887209 {_112456 : Type'} (s : _112456 -> Prop) (P : type686 _112456) (t : _112456 -> Prop) (h1 : @UNION_OF _112456 (@FINITE (_112456 -> Prop)) P s) (h2 : @UNION_OF _112456 (@FINITE (_112456 -> Prop)) P t) : (term45 _112456 s t P) = (term67 _112456 P).
Proof. exact (TRANS (@lem4887142 _112456 s t P) (@lem4887208 _112456 s P t h1 h2)). Qed.
Lemma lem4887210 {_112456 : Type'} (s : _112456 -> Prop) (P : type686 _112456) (t : _112456 -> Prop) (h1 : @UNION_OF _112456 (@FINITE (_112456 -> Prop)) P s) (h2 : @UNION_OF _112456 (@FINITE (_112456 -> Prop)) P t) : (term70 _112456 s t P) = (term71 _112456 P).
Proof. exact (MK_COMB (@lem4887118 _112456 s t) (@lem4887209 _112456 s P t h1 h2)). Qed.
Lemma lem4887213 {_112456 : Type'} (s : _112456 -> Prop) (P : type686 _112456) (t : _112456 -> Prop) (h1 : @UNION_OF _112456 (@FINITE (_112456 -> Prop)) P s) (h2 : @UNION_OF _112456 (@FINITE (_112456 -> Prop)) P t) : (term71 _112456 P) = (term70 _112456 s t P).
Proof. exact (SYM (@lem4887210 _112456 s P t h1 h2)). Qed.
Lemma lem4887217 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = True.
Proof. exact (EQ_MP (@lem4887043 _92140) (@lem3596285 _92140)). Qed.
Lemma lem4887218 {_112456 : Type'} : (@FINITE (_112456 -> Prop) (@EMPTY (_112456 -> Prop))) = True.
Proof. exact (@lem4887217 (_112456 -> Prop)). Qed.
Lemma lem4887219 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4887220 {_112456 : Type'} : (term33 _112456) = (and True).
Proof. exact (MK_COMB (@lem4887219) (@lem4887218 _112456)). Qed.
Lemma lem4887228 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4887041 A x (@lem4887040 A x)). Qed.
Lemma lem4887229 {_112456 : Type'} (x : _112456 -> Prop) : (@IN (_112456 -> Prop) x (@EMPTY (_112456 -> Prop))) = False.
Proof. exact (@lem4887228 (_112456 -> Prop) x). Qed.
Lemma lem4887230 {_112456 : Type'} (s' : _112456 -> Prop) : (@IN (_112456 -> Prop) s' (@EMPTY (_112456 -> Prop))) = False.
Proof. exact (@lem4887229 _112456 s'). Qed.
Lemma lem4887231 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4887232 {_112456 : Type'} (s' : _112456 -> Prop) : (term61 _112456 s') = (imp False).
Proof. exact (MK_COMB (@lem4887231) (@lem4887230 _112456 s')). Qed.
Lemma lem4887233 {_112456 : Type'} (P : type686 _112456) (s' : _112456 -> Prop) : (@UNION_OF _112456 (@FINITE (_112456 -> Prop)) P s') = (@UNION_OF _112456 (@FINITE (_112456 -> Prop)) P s').
Proof. exact (eq_refl (@UNION_OF _112456 (@FINITE (_112456 -> Prop)) P s')). Qed.
Lemma lem4887234 {_112456 : Type'} (P : type686 _112456) (s' : _112456 -> Prop) : (term63 _112456 P s') = (term72 _112456 P s').
Proof. exact (MK_COMB (@lem4887232 _112456 s') (@lem4887233 _112456 P s')). Qed.
Lemma lem4887236 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem4887237 {_112456 : Type'} (P : type686 _112456) (s' : _112456 -> Prop) : (term72 _112456 P s') = True.
Proof. exact (@lem4887236 (@UNION_OF _112456 (@FINITE (_112456 -> Prop)) P s')). Qed.
Lemma lem4887238 {_112456 : Type'} (P : type686 _112456) (s' : _112456 -> Prop) : (term63 _112456 P s') = True.
Proof. exact (TRANS (@lem4887234 _112456 P s') (@lem4887237 _112456 P s')). Qed.
Lemma lem4887239 {_112456 : Type'} (P : type686 _112456) : (term65 _112456 P) = (term73 _112456).
Proof. exact (fun_ext (fun s' : _112456 -> Prop => @lem4887238 _112456 P s')). Qed.
Lemma lem4887240 {_112456 : Type'} : (@all (_112456 -> Prop)) = (@all (_112456 -> Prop)).
Proof. exact (eq_refl (@all (_112456 -> Prop))). Qed.
Lemma lem4887241 {_112456 : Type'} (P : type686 _112456) : (term67 _112456 P) = (term74 _112456).
Proof. exact (MK_COMB (@lem4887240 _112456) (@lem4887239 _112456 P)). Qed.
Lemma lem4887243 {A : Type'} (t : Prop) : (term75 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4887244 {_112456 : Type'} (t : Prop) : (term76 _112456 t) = t.
Proof. exact (@lem4887243 (_112456 -> Prop) t). Qed.
Lemma lem4887245 {_112456 : Type'} : (term74 _112456) = True.
Proof. exact (@lem4887244 _112456 True). Qed.
Lemma lem4887246 {_112456 : Type'} (P : type686 _112456) : (term67 _112456 P) = True.
Proof. exact (TRANS (@lem4887241 _112456 P) (@lem4887245 _112456)). Qed.
Lemma lem4887247 {_112456 : Type'} (P : type686 _112456) : (term71 _112456 P) = (True /\ True).
Proof. exact (MK_COMB (@lem4887220 _112456) (@lem4887246 _112456 P)). Qed.
Lemma lem4887249 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4887250 : (True /\ True) = True.
Proof. exact (@lem4887249 True). Qed.
Lemma lem4887251 {_112456 : Type'} (P : type686 _112456) : (term71 _112456 P) = True.
Proof. exact (TRANS (@lem4887247 _112456 P) (@lem4887250)). Qed.
Lemma lem4887252 {_112456 : Type'} (P : type686 _112456) : True = (term71 _112456 P).
Proof. exact (SYM (@lem4887251 _112456 P)). Qed.
Lemma lem4887253 {_112456 : Type'} (P : type686 _112456) : term71 _112456 P.
Proof. exact (EQ_MP (@lem4887252 _112456 P) (@lem0)). Qed.
Lemma lem4887254 {_112456 : Type'} (s : _112456 -> Prop) (P : type686 _112456) (t : _112456 -> Prop) (h1 : @UNION_OF _112456 (@FINITE (_112456 -> Prop)) P s) (h2 : @UNION_OF _112456 (@FINITE (_112456 -> Prop)) P t) : term70 _112456 s t P.
Proof. exact (EQ_MP (@lem4887213 _112456 s P t h1 h2) (@lem4887253 _112456 P)). Qed.
Lemma lem4887255 {_112456 : Type'} (s : _112456 -> Prop) (P : type686 _112456) (t : _112456 -> Prop) (h1 : @UNION_OF _112456 (@FINITE (_112456 -> Prop)) P s) (h2 : @UNION_OF _112456 (@FINITE (_112456 -> Prop)) P t) : term15 _112456 P s t.
Proof. exact (@lem4887086 _112456 P s t (@lem4887254 _112456 s P t h1 h2)). Qed.
Lemma lem4887256 {_112456 : Type'} (s : _112456 -> Prop) (P : type686 _112456) (t : _112456 -> Prop) (h1 : @UNION_OF _112456 (@FINITE (_112456 -> Prop)) P s) (h2 : @UNION_OF _112456 (@FINITE (_112456 -> Prop)) P t) : term14 _112456 P s t.
Proof. exact (EQ_MP (@lem4887082 _112456 P s t) (@lem4887255 _112456 s P t h1 h2)). Qed.
Lemma lem4887257 {_112456 : Type'} (s : _112456 -> Prop) (P : type686 _112456) (t : _112456 -> Prop) (h1 : term13 _112456 s P t) : @UNION_OF _112456 (@FINITE (_112456 -> Prop)) P t.
Proof. exact (proj2 (@lem4887074 _112456 s P t h1)). Qed.
Lemma lem4887258 {_112456 : Type'} (s : _112456 -> Prop) (P : type686 _112456) (t : _112456 -> Prop) (h1 : term13 _112456 s P t) : @UNION_OF _112456 (@FINITE (_112456 -> Prop)) P s.
Proof. exact (proj1 (@lem4887074 _112456 s P t h1)). Qed.
Lemma lem4887259 {_112456 : Type'} (s : _112456 -> Prop) (P : type686 _112456) (t : _112456 -> Prop) (h1 : @UNION_OF _112456 (@FINITE (_112456 -> Prop)) P s) (h2 : @UNION_OF _112456 (@FINITE (_112456 -> Prop)) P t) : (@UNION_OF _112456 (@FINITE (_112456 -> Prop)) P t) = (term14 _112456 P s t).
Proof. exact (prop_ext (fun h3 : @UNION_OF _112456 (@FINITE (_112456 -> Prop)) P t => @lem4887256 _112456 s P t h1 h2) (fun h3 : term14 _112456 P s t => @lem4887075 _112456 P t h2)). Qed.
Lemma lem4887260 {_112456 : Type'} (s : _112456 -> Prop) (P : type686 _112456) (t : _112456 -> Prop) (h1 : @UNION_OF _112456 (@FINITE (_112456 -> Prop)) P s) (h2 : @UNION_OF _112456 (@FINITE (_112456 -> Prop)) P t) : term14 _112456 P s t.
Proof. exact (EQ_MP (@lem4887259 _112456 s P t h1 h2) (@lem4887075 _112456 P t h2)). Qed.
Lemma lem4887261 {_112456 : Type'} (s : _112456 -> Prop) (P : type686 _112456) (t : _112456 -> Prop) (h1 : @UNION_OF _112456 (@FINITE (_112456 -> Prop)) P s) (h2 : @UNION_OF _112456 (@FINITE (_112456 -> Prop)) P t) : (@UNION_OF _112456 (@FINITE (_112456 -> Prop)) P s) = (term14 _112456 P s t).
Proof. exact (prop_ext (fun h3 : @UNION_OF _112456 (@FINITE (_112456 -> Prop)) P s => @lem4887260 _112456 s P t h1 h2) (fun h3 : term14 _112456 P s t => @lem4887076 _112456 P s h1)). Qed.
Lemma lem4887262 {_112456 : Type'} (s : _112456 -> Prop) (P : type686 _112456) (t : _112456 -> Prop) (h1 : @UNION_OF _112456 (@FINITE (_112456 -> Prop)) P s) (h2 : @UNION_OF _112456 (@FINITE (_112456 -> Prop)) P t) : term14 _112456 P s t.
Proof. exact (EQ_MP (@lem4887261 _112456 s P t h1 h2) (@lem4887076 _112456 P s h1)). Qed.
Lemma lem4887263 {_112456 : Type'} (t : _112456 -> Prop) (P : type686 _112456) (s : _112456 -> Prop) (h1 : term13 _112456 s P t) (h2 : @UNION_OF _112456 (@FINITE (_112456 -> Prop)) P s) : (@UNION_OF _112456 (@FINITE (_112456 -> Prop)) P t) = (term14 _112456 P s t).
Proof. exact (prop_ext (fun h3 : @UNION_OF _112456 (@FINITE (_112456 -> Prop)) P t => @lem4887262 _112456 s P t h2 h3) (fun h3 : term14 _112456 P s t => @lem4887257 _112456 s P t h1)). Qed.
Lemma lem4887264 {_112456 : Type'} (t : _112456 -> Prop) (P : type686 _112456) (s : _112456 -> Prop) (h1 : term13 _112456 s P t) (h2 : @UNION_OF _112456 (@FINITE (_112456 -> Prop)) P s) : term14 _112456 P s t.
Proof. exact (EQ_MP (@lem4887263 _112456 t P s h1 h2) (@lem4887257 _112456 s P t h1)). Qed.
Lemma lem4887265 {_112456 : Type'} (s : _112456 -> Prop) (P : type686 _112456) (t : _112456 -> Prop) (h1 : term13 _112456 s P t) : (@UNION_OF _112456 (@FINITE (_112456 -> Prop)) P s) = (term14 _112456 P s t).
Proof. exact (prop_ext (fun h2 : @UNION_OF _112456 (@FINITE (_112456 -> Prop)) P s => @lem4887264 _112456 t P s h1 h2) (fun h2 : term14 _112456 P s t => @lem4887258 _112456 s P t h1)). Qed.
Lemma lem4887266 {_112456 : Type'} (s : _112456 -> Prop) (P : type686 _112456) (t : _112456 -> Prop) (h1 : term13 _112456 s P t) : term14 _112456 P s t.
Proof. exact (EQ_MP (@lem4887265 _112456 s P t h1) (@lem4887258 _112456 s P t h1)). Qed.
Lemma lem4887267 {_112456 : Type'} (P : type686 _112456) (s : _112456 -> Prop) (t : _112456 -> Prop) : term77 _112456 P s t.
Proof. exact (fun h0 : term13 _112456 s P t => @lem4887266 _112456 s P t h0). Qed.
Lemma lem4887272 {_112456 : Type'} (P : type686 _112456) (s : _112456 -> Prop) : term78 _112456 P s.
Proof. exact (fun t : _112456 -> Prop => @lem4887267 _112456 P s t). Qed.
Lemma lem4887277 {_112456 : Type'} (P : type686 _112456) : term79 _112456 P.
Proof. exact (fun s : _112456 -> Prop => @lem4887272 _112456 P s). Qed.
Lemma lem4887282 {_112456 : Type'} : term80 _112456.
Proof. exact (fun P : type686 _112456 => @lem4887277 _112456 P). Qed.
