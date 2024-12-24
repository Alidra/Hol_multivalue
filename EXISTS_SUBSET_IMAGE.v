Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXISTS_SUBSET_IMAGE_term_abbrevs.
Require Import DISJ_ASSOC_spec.
Require Import SUBSET_IMAGE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm18394_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Lemma lem3645952 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3645953 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3645954 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3645953 t1) (@lem3645952 t1)). Qed.
Lemma lem3645955 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3645954 t1 t2). Qed.
Lemma lem3645956 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3645957 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3645956 t1 t2) (@lem3645955 t1 t2)). Qed.
Lemma lem3645958 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3645957 t1 t2 t3). Qed.
Lemma lem3645959 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3645960 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3645959 t1 t2 t3) (@lem3645958 t1 t2 t3)). Qed.
Lemma lem3645961 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3645960 t1 t2 t3)). Qed.
Lemma lem3645962 {A B : Type'} (f : A -> B) : term7 A B f.
Proof. exact (@lem3645951 A B f). Qed.
Lemma lem3645963 {A B : Type'} (f : A -> B) : (term7 A B f) = (term8 A B f).
Proof. exact (eq_refl (term7 A B f)). Qed.
Lemma lem3645964 {A B : Type'} (f : A -> B) : term8 A B f.
Proof. exact (EQ_MP (@lem3645963 A B f) (@lem3645962 A B f)). Qed.
Lemma lem3645965 {A B : Type'} (f : A -> B) (s : B -> Prop) : term9 A B f s.
Proof. exact (@lem3645964 A B f s). Qed.
Lemma lem3645966 {A B : Type'} (s : B -> Prop) (f : A -> B) : (term9 A B f s) = (term10 A B s f).
Proof. exact (eq_refl (term9 A B f s)). Qed.
Lemma lem3645967 {A B : Type'} (s : B -> Prop) (f : A -> B) : term10 A B s f.
Proof. exact (EQ_MP (@lem3645966 A B s f) (@lem3645965 A B f s)). Qed.
Lemma lem3645968 {A B : Type'} (s : B -> Prop) (f : A -> B) (t : A -> Prop) : term11 A B s f t.
Proof. exact (@lem3645967 A B s f t). Qed.
Lemma lem3645969 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term11 A B s f t) = ((term12 A B s f t) = (term13 A B t s f)).
Proof. exact (eq_refl (term11 A B s f t)). Qed.
Lemma lem3645992 {A B : Type'} (t : A -> Prop) (s : B -> Prop) (f : A -> B) : (term12 A B s f t) = (term13 A B t s f).
Proof. exact (EQ_MP (@lem3645969 A B t s f) (@lem3645968 A B s f t)). Qed.
Lemma lem3645993 {_93365 _93381 : Type'} (t : _93365 -> Prop) (s : _93381 -> Prop) (f : _93365 -> _93381) : (term12 _93365 _93381 s f t) = (term13 _93365 _93381 t s f).
Proof. exact (@lem3645992 _93365 _93381 t s f). Qed.
Lemma lem3645994 {_93365 _93381 : Type'} (s : _93365 -> Prop) (t : _93381 -> Prop) (f : _93365 -> _93381) : (term12 _93365 _93381 t f s) = (term13 _93365 _93381 s t f).
Proof. exact (@lem3645993 _93365 _93381 s t f). Qed.
Lemma lem3646003 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3646004 {_93365 _93381 : Type'} (s : _93365 -> Prop) (t : _93381 -> Prop) (f : _93365 -> _93381) : (term14 _93365 _93381 t f s) = (term15 _93365 _93381 s t f).
Proof. exact (MK_COMB (@lem3646003) (@lem3645994 _93365 _93381 s t f)). Qed.
Lemma lem3646005 {_93381 : Type'} (P : type686 _93381) (t : _93381 -> Prop) : (P t) = (P t).
Proof. exact (eq_refl (P t)). Qed.
Lemma lem3646006 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) (t : _93381 -> Prop) : (term16 _93365 _93381 f s P t) = (term17 _93365 _93381 s f P t).
Proof. exact (MK_COMB (@lem3646004 _93365 _93381 s t f) (@lem3646005 _93381 P t)). Qed.
Lemma lem3646009 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) : (term18 _93365 _93381 f s P) = (term19 _93365 _93381 s f P).
Proof. exact (fun_ext (fun t : _93381 -> Prop => @lem3646006 _93365 _93381 s f P t)). Qed.
Lemma lem3646010 {_93381 : Type'} : (@ex (_93381 -> Prop)) = (@ex (_93381 -> Prop)).
Proof. exact (eq_refl (@ex (_93381 -> Prop))). Qed.
Lemma lem3646011 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) : (term20 _93365 _93381 f s P) = (term21 _93365 _93381 s f P).
Proof. exact (MK_COMB (@lem3646010 _93381) (@lem3646009 _93365 _93381 s f P)). Qed.
Lemma lem3646016 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3646017 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) : (term22 _93365 _93381 f s P) = (term23 _93365 _93381 s f P).
Proof. exact (MK_COMB (@lem3646016) (@lem3646011 _93365 _93381 s f P)). Qed.
Lemma lem3646024 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term24 _93365 _93381 s P f) = (term24 _93365 _93381 s P f).
Proof. exact (eq_refl (term24 _93365 _93381 s P f)). Qed.
Lemma lem3646025 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : ((term20 _93365 _93381 f s P) = (term24 _93365 _93381 s P f)) = ((term21 _93365 _93381 s f P) = (term24 _93365 _93381 s P f)).
Proof. exact (MK_COMB (@lem3646017 _93365 _93381 s f P) (@lem3646024 _93365 _93381 s P f)). Qed.
Lemma lem3646028 {_93365 _93381 : Type'} (P : type686 _93381) (f : _93365 -> _93381) : (term25 _93365 _93381 P f) = (term26 _93365 _93381 P f).
Proof. exact (fun_ext (fun s : _93365 -> Prop => @lem3646025 _93365 _93381 s P f)). Qed.
Lemma lem3646029 {_93365 : Type'} : (@all (_93365 -> Prop)) = (@all (_93365 -> Prop)).
Proof. exact (eq_refl (@all (_93365 -> Prop))). Qed.
Lemma lem3646030 {_93365 _93381 : Type'} (P : type686 _93381) (f : _93365 -> _93381) : (term27 _93365 _93381 P f) = (term28 _93365 _93381 P f).
Proof. exact (MK_COMB (@lem3646029 _93365) (@lem3646028 _93365 _93381 P f)). Qed.
Lemma lem3646035 {_93365 _93381 : Type'} (P : type686 _93381) : (term29 _93365 _93381 P) = (term30 _93365 _93381 P).
Proof. exact (fun_ext (fun f : _93365 -> _93381 => @lem3646030 _93365 _93381 P f)). Qed.
Lemma lem3646036 {_93365 _93381 : Type'} : (@all (_93365 -> _93381)) = (@all (_93365 -> _93381)).
Proof. exact (eq_refl (@all (_93365 -> _93381))). Qed.
Lemma lem3646037 {_93365 _93381 : Type'} (P : type686 _93381) : (term31 _93365 _93381 P) = (term32 _93365 _93381 P).
Proof. exact (MK_COMB (@lem3646036 _93365 _93381) (@lem3646035 _93365 _93381 P)). Qed.
Lemma lem3646042 {_93365 _93381 : Type'} : (term33 _93365 _93381) = (term34 _93365 _93381).
Proof. exact (fun_ext (fun P : type686 _93381 => @lem3646037 _93365 _93381 P)). Qed.
Lemma lem3646043 {_93381 : Type'} : (@all ((_93381 -> Prop) -> Prop)) = (@all ((_93381 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_93381 -> Prop) -> Prop))). Qed.
Lemma lem3646044 {_93365 _93381 : Type'} : (term35 _93365 _93381) = (term36 _93365 _93381).
Proof. exact (MK_COMB (@lem3646043 _93381) (@lem3646042 _93365 _93381)). Qed.
Lemma lem3646049 {_93365 _93381 : Type'} : (term36 _93365 _93381) = (term35 _93365 _93381).
Proof. exact (SYM (@lem3646044 _93365 _93381)). Qed.
Lemma lem3646051 (p : Prop) : p = (term37 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3646052 {_93365 _93381 : Type'} : (term36 _93365 _93381) = (term38 _93365 _93381).
Proof. exact (@lem3646051 (term36 _93365 _93381)). Qed.
Lemma lem3646053 {_93365 _93381 : Type'} : (term38 _93365 _93381) = (term36 _93365 _93381).
Proof. exact (SYM (@lem3646052 _93365 _93381)). Qed.
Lemma lem3646054 {_93365 _93381 : Type'} (h1 : term39 _93365 _93381) : term39 _93365 _93381.
Proof. exact (h1). Qed.
Lemma lem3646057 {_93365 _93381 : Type'} (h1 : term38 _93365 _93381) : term38 _93365 _93381.
Proof. exact (h1). Qed.
Lemma lem3646058 {_93365 _93381 : Type'} : term40 _93365 _93381.
Proof. exact (fun h0 : term38 _93365 _93381 => @lem3646057 _93365 _93381 h0). Qed.
Lemma lem3646059 {_93365 _93381 : Type'} (h1 : term40 _93365 _93381) : term40 _93365 _93381.
Proof. exact (h1). Qed.
Lemma lem3646060 {_93365 _93381 : Type'} (h1 : term38 _93365 _93381) : term38 _93365 _93381.
Proof. exact (h1). Qed.
Lemma lem3646061 {_93365 _93381 : Type'} (h1 : term38 _93365 _93381) (h2 : term40 _93365 _93381) : term38 _93365 _93381.
Proof. exact (@lem3646059 _93365 _93381 h2 (@lem3646060 _93365 _93381 h1)). Qed.
Lemma lem3646062 {_93365 _93381 : Type'} (h1 : term38 _93365 _93381) : term41 _93365 _93381.
Proof. exact (fun h0 : term40 _93365 _93381 => @lem3646061 _93365 _93381 h1 h0). Qed.
Lemma lem3646063 {_93365 _93381 : Type'} (h1 : term40 _93365 _93381) : term40 _93365 _93381.
Proof. exact (h1). Qed.
Lemma lem3646064 {_93365 _93381 : Type'} (h1 : term38 _93365 _93381) (h2 : term40 _93365 _93381) : term38 _93365 _93381.
Proof. exact (@lem3646062 _93365 _93381 h1 (@lem3646063 _93365 _93381 h2)). Qed.
Lemma lem3646065 {_93365 _93381 : Type'} (h1 : term40 _93365 _93381) : term40 _93365 _93381.
Proof. exact (fun h0 : term38 _93365 _93381 => @lem3646064 _93365 _93381 h0 h1). Qed.
Lemma lem3646066 {_93365 _93381 : Type'} : term42 _93365 _93381.
Proof. exact (fun h0 : term40 _93365 _93381 => @lem3646065 _93365 _93381 h0). Qed.
Lemma lem3646069 {_93365 _93381 : Type'} : term40 _93365 _93381.
Proof. exact (@lem3646066 _93365 _93381 (@lem3646058 _93365 _93381)). Qed.
Lemma lem3646070 {_93365 _93381 : Type'} : term40 _93365 _93381.
Proof. exact (@lem3646069 _93365 _93381). Qed.
Lemma lem3646072 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3646073 {_93365 _93381 : Type'} : (term38 _93365 _93381) = (term43 _93365 _93381).
Proof. exact (@lem3646072 (term39 _93365 _93381)). Qed.
Lemma lem3646075 (t : Prop) : (term44 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3646076 {_93365 _93381 : Type'} : (term43 _93365 _93381) = (term36 _93365 _93381).
Proof. exact (@lem3646075 (term36 _93365 _93381)). Qed.
Lemma lem3646227 {_93365 _93381 : Type'} : (term38 _93365 _93381) = (term36 _93365 _93381).
Proof. exact (TRANS (@lem3646073 _93365 _93381) (@lem3646076 _93365 _93381)). Qed.
Lemma lem3646232 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (t : _93365 -> Prop) : (term45 _93365 _93381 s P f t) = (term45 _93365 _93381 s P f t).
Proof. exact (eq_refl (term45 _93365 _93381 s P f t)). Qed.
Lemma lem3646233 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term46 _93365 _93381 s P f) = (term46 _93365 _93381 s P f).
Proof. exact (fun_ext (fun t : _93365 -> Prop => @lem3646232 _93365 _93381 s P f t)). Qed.
Lemma lem3646234 {_93365 : Type'} : (@ex (_93365 -> Prop)) = (@ex (_93365 -> Prop)).
Proof. exact (eq_refl (@ex (_93365 -> Prop))). Qed.
Lemma lem3646235 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term24 _93365 _93381 s P f) = (term24 _93365 _93381 s P f).
Proof. exact (MK_COMB (@lem3646234 _93365) (@lem3646233 _93365 _93381 s P f)). Qed.
Lemma lem3646236 {_93381 : Type'} (P : type686 _93381) (t : _93381 -> Prop) : (P t) = (P t).
Proof. exact (eq_refl (P t)). Qed.
Lemma lem3646241 {_93365 _93381 : Type'} (s : _93365 -> Prop) (t : _93381 -> Prop) (f : _93365 -> _93381) (u : _93365 -> Prop) : (term47 _93365 _93381 s t f u) = (term47 _93365 _93381 s t f u).
Proof. exact (eq_refl (term47 _93365 _93381 s t f u)). Qed.
Lemma lem3646242 {_93365 _93381 : Type'} (s : _93365 -> Prop) (t : _93381 -> Prop) (f : _93365 -> _93381) : (term48 _93365 _93381 s t f) = (term48 _93365 _93381 s t f).
Proof. exact (fun_ext (fun u : _93365 -> Prop => @lem3646241 _93365 _93381 s t f u)). Qed.
Lemma lem3646243 {_93365 : Type'} : (@ex (_93365 -> Prop)) = (@ex (_93365 -> Prop)).
Proof. exact (eq_refl (@ex (_93365 -> Prop))). Qed.
Lemma lem3646244 {_93365 _93381 : Type'} (s : _93365 -> Prop) (t : _93381 -> Prop) (f : _93365 -> _93381) : (term13 _93365 _93381 s t f) = (term13 _93365 _93381 s t f).
Proof. exact (MK_COMB (@lem3646243 _93365) (@lem3646242 _93365 _93381 s t f)). Qed.
Lemma lem3646245 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3646246 {_93365 _93381 : Type'} (s : _93365 -> Prop) (t : _93381 -> Prop) (f : _93365 -> _93381) : (term15 _93365 _93381 s t f) = (term15 _93365 _93381 s t f).
Proof. exact (MK_COMB (@lem3646245) (@lem3646244 _93365 _93381 s t f)). Qed.
Lemma lem3646247 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) (t : _93381 -> Prop) : (term17 _93365 _93381 s f P t) = (term17 _93365 _93381 s f P t).
Proof. exact (MK_COMB (@lem3646246 _93365 _93381 s t f) (@lem3646236 _93381 P t)). Qed.
Lemma lem3646248 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) : (term19 _93365 _93381 s f P) = (term19 _93365 _93381 s f P).
Proof. exact (fun_ext (fun t : _93381 -> Prop => @lem3646247 _93365 _93381 s f P t)). Qed.
Lemma lem3646249 {_93381 : Type'} : (@ex (_93381 -> Prop)) = (@ex (_93381 -> Prop)).
Proof. exact (eq_refl (@ex (_93381 -> Prop))). Qed.
Lemma lem3646250 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) : (term21 _93365 _93381 s f P) = (term21 _93365 _93381 s f P).
Proof. exact (MK_COMB (@lem3646249 _93381) (@lem3646248 _93365 _93381 s f P)). Qed.
Lemma lem3646251 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3646252 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) : (term23 _93365 _93381 s f P) = (term23 _93365 _93381 s f P).
Proof. exact (MK_COMB (@lem3646251) (@lem3646250 _93365 _93381 s f P)). Qed.
Lemma lem3646253 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : ((term21 _93365 _93381 s f P) = (term24 _93365 _93381 s P f)) = ((term21 _93365 _93381 s f P) = (term24 _93365 _93381 s P f)).
Proof. exact (MK_COMB (@lem3646252 _93365 _93381 s f P) (@lem3646235 _93365 _93381 s P f)). Qed.
Lemma lem3646254 {_93365 _93381 : Type'} (P : type686 _93381) (f : _93365 -> _93381) : (term26 _93365 _93381 P f) = (term26 _93365 _93381 P f).
Proof. exact (fun_ext (fun s : _93365 -> Prop => @lem3646253 _93365 _93381 s P f)). Qed.
Lemma lem3646255 {_93365 : Type'} : (@all (_93365 -> Prop)) = (@all (_93365 -> Prop)).
Proof. exact (eq_refl (@all (_93365 -> Prop))). Qed.
Lemma lem3646256 {_93365 _93381 : Type'} (P : type686 _93381) (f : _93365 -> _93381) : (term28 _93365 _93381 P f) = (term28 _93365 _93381 P f).
Proof. exact (MK_COMB (@lem3646255 _93365) (@lem3646254 _93365 _93381 P f)). Qed.
Lemma lem3646257 {_93365 _93381 : Type'} (P : type686 _93381) : (term30 _93365 _93381 P) = (term30 _93365 _93381 P).
Proof. exact (fun_ext (fun f : _93365 -> _93381 => @lem3646256 _93365 _93381 P f)). Qed.
Lemma lem3646258 {_93365 _93381 : Type'} : (@all (_93365 -> _93381)) = (@all (_93365 -> _93381)).
Proof. exact (eq_refl (@all (_93365 -> _93381))). Qed.
Lemma lem3646259 {_93365 _93381 : Type'} (P : type686 _93381) : (term32 _93365 _93381 P) = (term32 _93365 _93381 P).
Proof. exact (MK_COMB (@lem3646258 _93365 _93381) (@lem3646257 _93365 _93381 P)). Qed.
Lemma lem3646260 {_93365 _93381 : Type'} : (term34 _93365 _93381) = (term34 _93365 _93381).
Proof. exact (fun_ext (fun P : type686 _93381 => @lem3646259 _93365 _93381 P)). Qed.
Lemma lem3646261 {_93381 : Type'} : (@all ((_93381 -> Prop) -> Prop)) = (@all ((_93381 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_93381 -> Prop) -> Prop))). Qed.
Lemma lem3646262 {_93365 _93381 : Type'} : (term36 _93365 _93381) = (term36 _93365 _93381).
Proof. exact (MK_COMB (@lem3646261 _93381) (@lem3646260 _93365 _93381)). Qed.
Lemma lem3646307 {_93365 _93381 : Type'} : (term38 _93365 _93381) = (term36 _93365 _93381).
Proof. exact (TRANS (@lem3646227 _93365 _93381) (@lem3646262 _93365 _93381)). Qed.
Lemma lem3646308 {_93365 _93381 : Type'} : (term36 _93365 _93381) = (term38 _93365 _93381).
Proof. exact (SYM (@lem3646307 _93365 _93381)). Qed.
Lemma lem3646310 (p : Prop) : p = (term37 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3646311 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : ((term21 _93365 _93381 s f P) = (term24 _93365 _93381 s P f)) = (term49 _93365 _93381 s P f).
Proof. exact (@lem3646310 ((term21 _93365 _93381 s f P) = (term24 _93365 _93381 s P f))). Qed.
Lemma lem3646312 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term49 _93365 _93381 s P f) = ((term21 _93365 _93381 s f P) = (term24 _93365 _93381 s P f)).
Proof. exact (SYM (@lem3646311 _93365 _93381 s P f)). Qed.
Lemma lem3646313 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (h1 : term50 _93365 _93381 s P f) : term50 _93365 _93381 s P f.
Proof. exact (h1). Qed.
Lemma lem3646322 {_93365 _93381 : Type'} (s : _93365 -> Prop) (t : _93381 -> Prop) (f : _93365 -> _93381) (u : _93365 -> Prop) : (term51 _93365 _93381 s t f u) = (term52 _93365 _93381 s t f u).
Proof. exact (@lem17045 (@SUBSET _93365 u s) (t = (@IMAGE _93365 _93381 f u))). Qed.
Lemma lem3646325 {_93365 _93381 : Type'} (s : _93365 -> Prop) (t : _93381 -> Prop) (f : _93365 -> _93381) (u : _93365 -> Prop) : (term47 _93365 _93381 s t f u) = (term47 _93365 _93381 s t f u).
Proof. exact (eq_refl (term47 _93365 _93381 s t f u)). Qed.
Lemma lem3646326 {_93365 : Type'} (P : type686 _93365) : (term53 _93365 P) = (term54 _93365 P).
Proof. exact (@lem18394 (_93365 -> Prop) P). Qed.
Lemma lem3646327 {_93365 _93381 : Type'} (s : _93365 -> Prop) (t : _93381 -> Prop) (f : _93365 -> _93381) : (term55 _93365 _93381 s t f) = (term56 _93365 _93381 s t f).
Proof. exact (@lem3646326 _93365 (term48 _93365 _93381 s t f)). Qed.
Lemma lem3646328 {_93365 _93381 : Type'} (s : _93365 -> Prop) (t : _93381 -> Prop) (f : _93365 -> _93381) (u : _93365 -> Prop) : (term57 _93365 _93381 s t f u) = (term47 _93365 _93381 s t f u).
Proof. exact (eq_refl (term57 _93365 _93381 s t f u)). Qed.
Lemma lem3646329 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3646330 {_93365 _93381 : Type'} (s : _93365 -> Prop) (t : _93381 -> Prop) (f : _93365 -> _93381) (u : _93365 -> Prop) : (term58 _93365 _93381 s t f u) = (term51 _93365 _93381 s t f u).
Proof. exact (MK_COMB (@lem3646329) (@lem3646328 _93365 _93381 s t f u)). Qed.
Lemma lem3646331 {_93365 _93381 : Type'} (s : _93365 -> Prop) (t : _93381 -> Prop) (f : _93365 -> _93381) (u : _93365 -> Prop) : (term58 _93365 _93381 s t f u) = (term52 _93365 _93381 s t f u).
Proof. exact (TRANS (@lem3646330 _93365 _93381 s t f u) (@lem3646322 _93365 _93381 s t f u)). Qed.
Lemma lem3646332 {_93365 _93381 : Type'} (s : _93365 -> Prop) (t : _93381 -> Prop) (f : _93365 -> _93381) : (term59 _93365 _93381 s t f) = (term60 _93365 _93381 s t f).
Proof. exact (fun_ext (fun u : _93365 -> Prop => @lem3646331 _93365 _93381 s t f u)). Qed.
Lemma lem3646333 {_93365 : Type'} : (@all (_93365 -> Prop)) = (@all (_93365 -> Prop)).
Proof. exact (eq_refl (@all (_93365 -> Prop))). Qed.
Lemma lem3646334 {_93365 _93381 : Type'} (s : _93365 -> Prop) (t : _93381 -> Prop) (f : _93365 -> _93381) : (term56 _93365 _93381 s t f) = (term61 _93365 _93381 s t f).
Proof. exact (MK_COMB (@lem3646333 _93365) (@lem3646332 _93365 _93381 s t f)). Qed.
Lemma lem3646335 {_93365 _93381 : Type'} (s : _93365 -> Prop) (t : _93381 -> Prop) (f : _93365 -> _93381) : (term55 _93365 _93381 s t f) = (term61 _93365 _93381 s t f).
Proof. exact (TRANS (@lem3646327 _93365 _93381 s t f) (@lem3646334 _93365 _93381 s t f)). Qed.
Lemma lem3646336 {_93365 _93381 : Type'} (s : _93365 -> Prop) (t : _93381 -> Prop) (f : _93365 -> _93381) : (term48 _93365 _93381 s t f) = (term48 _93365 _93381 s t f).
Proof. exact (fun_ext (fun u : _93365 -> Prop => @lem3646325 _93365 _93381 s t f u)). Qed.
Lemma lem3646337 {_93365 : Type'} : (@ex (_93365 -> Prop)) = (@ex (_93365 -> Prop)).
Proof. exact (eq_refl (@ex (_93365 -> Prop))). Qed.
Lemma lem3646338 {_93365 _93381 : Type'} (s : _93365 -> Prop) (t : _93381 -> Prop) (f : _93365 -> _93381) : (term13 _93365 _93381 s t f) = (term13 _93365 _93381 s t f).
Proof. exact (MK_COMB (@lem3646337 _93365) (@lem3646336 _93365 _93381 s t f)). Qed.
Lemma lem3646339 {_93381 : Type'} (P : type686 _93381) (t : _93381 -> Prop) : (term62 _93381 P t) = (term62 _93381 P t).
Proof. exact (eq_refl (term62 _93381 P t)). Qed.
Lemma lem3646340 {_93381 : Type'} (P : type686 _93381) (t : _93381 -> Prop) : (P t) = (P t).
Proof. exact (eq_refl (P t)). Qed.
Lemma lem3646341 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3646342 {_93365 _93381 : Type'} (s : _93365 -> Prop) (t : _93381 -> Prop) (f : _93365 -> _93381) : (term63 _93365 _93381 s t f) = (term64 _93365 _93381 s t f).
Proof. exact (MK_COMB (@lem3646341) (@lem3646335 _93365 _93381 s t f)). Qed.
Lemma lem3646343 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) (t : _93381 -> Prop) : (term65 _93365 _93381 s f P t) = (term66 _93365 _93381 s f P t).
Proof. exact (MK_COMB (@lem3646342 _93365 _93381 s t f) (@lem3646339 _93381 P t)). Qed.
Lemma lem3646344 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) (t : _93381 -> Prop) : (term67 _93365 _93381 s f P t) = (term65 _93365 _93381 s f P t).
Proof. exact (@lem17045 (term13 _93365 _93381 s t f) (P t)). Qed.
Lemma lem3646345 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) (t : _93381 -> Prop) : (term67 _93365 _93381 s f P t) = (term66 _93365 _93381 s f P t).
Proof. exact (TRANS (@lem3646344 _93365 _93381 s f P t) (@lem3646343 _93365 _93381 s f P t)). Qed.
Lemma lem3646346 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3646347 {_93365 _93381 : Type'} (s : _93365 -> Prop) (t : _93381 -> Prop) (f : _93365 -> _93381) : (term15 _93365 _93381 s t f) = (term15 _93365 _93381 s t f).
Proof. exact (MK_COMB (@lem3646346) (@lem3646338 _93365 _93381 s t f)). Qed.
Lemma lem3646348 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) (t : _93381 -> Prop) : (term17 _93365 _93381 s f P t) = (term17 _93365 _93381 s f P t).
Proof. exact (MK_COMB (@lem3646347 _93365 _93381 s t f) (@lem3646340 _93381 P t)). Qed.
Lemma lem3646349 {_93381 : Type'} (P : type686 _93381) : (term53 _93381 P) = (term54 _93381 P).
Proof. exact (@lem18394 (_93381 -> Prop) P). Qed.
Lemma lem3646350 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) : (term68 _93365 _93381 s f P) = (term69 _93365 _93381 s f P).
Proof. exact (@lem3646349 _93381 (term19 _93365 _93381 s f P)). Qed.
Lemma lem3646351 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) (t : _93381 -> Prop) : (term70 _93365 _93381 s f P t) = (term17 _93365 _93381 s f P t).
Proof. exact (eq_refl (term70 _93365 _93381 s f P t)). Qed.
Lemma lem3646352 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3646353 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) (t : _93381 -> Prop) : (term71 _93365 _93381 s f P t) = (term67 _93365 _93381 s f P t).
Proof. exact (MK_COMB (@lem3646352) (@lem3646351 _93365 _93381 s f P t)). Qed.
Lemma lem3646354 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) (t : _93381 -> Prop) : (term71 _93365 _93381 s f P t) = (term66 _93365 _93381 s f P t).
Proof. exact (TRANS (@lem3646353 _93365 _93381 s f P t) (@lem3646345 _93365 _93381 s f P t)). Qed.
Lemma lem3646355 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) : (term72 _93365 _93381 s f P) = (term73 _93365 _93381 s f P).
Proof. exact (fun_ext (fun t : _93381 -> Prop => @lem3646354 _93365 _93381 s f P t)). Qed.
Lemma lem3646356 {_93381 : Type'} : (@all (_93381 -> Prop)) = (@all (_93381 -> Prop)).
Proof. exact (eq_refl (@all (_93381 -> Prop))). Qed.
Lemma lem3646357 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) : (term69 _93365 _93381 s f P) = (term74 _93365 _93381 s f P).
Proof. exact (MK_COMB (@lem3646356 _93381) (@lem3646355 _93365 _93381 s f P)). Qed.
Lemma lem3646358 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) : (term68 _93365 _93381 s f P) = (term74 _93365 _93381 s f P).
Proof. exact (TRANS (@lem3646350 _93365 _93381 s f P) (@lem3646357 _93365 _93381 s f P)). Qed.
Lemma lem3646359 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) : (term19 _93365 _93381 s f P) = (term19 _93365 _93381 s f P).
Proof. exact (fun_ext (fun t : _93381 -> Prop => @lem3646348 _93365 _93381 s f P t)). Qed.
Lemma lem3646360 {_93381 : Type'} : (@ex (_93381 -> Prop)) = (@ex (_93381 -> Prop)).
Proof. exact (eq_refl (@ex (_93381 -> Prop))). Qed.
Lemma lem3646361 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) : (term21 _93365 _93381 s f P) = (term21 _93365 _93381 s f P).
Proof. exact (MK_COMB (@lem3646360 _93381) (@lem3646359 _93365 _93381 s f P)). Qed.
Lemma lem3646370 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (t : _93365 -> Prop) : (term75 _93365 _93381 s P f t) = (term76 _93365 _93381 s P f t).
Proof. exact (@lem17045 (@SUBSET _93365 t s) (term77 _93365 _93381 P f t)). Qed.
Lemma lem3646373 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (t : _93365 -> Prop) : (term45 _93365 _93381 s P f t) = (term45 _93365 _93381 s P f t).
Proof. exact (eq_refl (term45 _93365 _93381 s P f t)). Qed.
Lemma lem3646374 {_93365 : Type'} (P : type686 _93365) : (term53 _93365 P) = (term54 _93365 P).
Proof. exact (@lem18394 (_93365 -> Prop) P). Qed.
Lemma lem3646375 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term78 _93365 _93381 s P f) = (term79 _93365 _93381 s P f).
Proof. exact (@lem3646374 _93365 (term46 _93365 _93381 s P f)). Qed.
Lemma lem3646376 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (t : _93365 -> Prop) : (term80 _93365 _93381 s P f t) = (term45 _93365 _93381 s P f t).
Proof. exact (eq_refl (term80 _93365 _93381 s P f t)). Qed.
Lemma lem3646377 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3646378 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (t : _93365 -> Prop) : (term81 _93365 _93381 s P f t) = (term75 _93365 _93381 s P f t).
Proof. exact (MK_COMB (@lem3646377) (@lem3646376 _93365 _93381 s P f t)). Qed.
Lemma lem3646379 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (t : _93365 -> Prop) : (term81 _93365 _93381 s P f t) = (term76 _93365 _93381 s P f t).
Proof. exact (TRANS (@lem3646378 _93365 _93381 s P f t) (@lem3646370 _93365 _93381 s P f t)). Qed.
Lemma lem3646380 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term82 _93365 _93381 s P f) = (term83 _93365 _93381 s P f).
Proof. exact (fun_ext (fun t : _93365 -> Prop => @lem3646379 _93365 _93381 s P f t)). Qed.
Lemma lem3646381 {_93365 : Type'} : (@all (_93365 -> Prop)) = (@all (_93365 -> Prop)).
Proof. exact (eq_refl (@all (_93365 -> Prop))). Qed.
Lemma lem3646382 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term79 _93365 _93381 s P f) = (term84 _93365 _93381 s P f).
Proof. exact (MK_COMB (@lem3646381 _93365) (@lem3646380 _93365 _93381 s P f)). Qed.
Lemma lem3646383 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term78 _93365 _93381 s P f) = (term84 _93365 _93381 s P f).
Proof. exact (TRANS (@lem3646375 _93365 _93381 s P f) (@lem3646382 _93365 _93381 s P f)). Qed.
Lemma lem3646384 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term46 _93365 _93381 s P f) = (term46 _93365 _93381 s P f).
Proof. exact (fun_ext (fun t : _93365 -> Prop => @lem3646373 _93365 _93381 s P f t)). Qed.
Lemma lem3646385 {_93365 : Type'} : (@ex (_93365 -> Prop)) = (@ex (_93365 -> Prop)).
Proof. exact (eq_refl (@ex (_93365 -> Prop))). Qed.
Lemma lem3646386 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term24 _93365 _93381 s P f) = (term24 _93365 _93381 s P f).
Proof. exact (MK_COMB (@lem3646385 _93365) (@lem3646384 _93365 _93381 s P f)). Qed.
Lemma lem3646387 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3646388 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) : (term85 _93365 _93381 s f P) = (term86 _93365 _93381 s f P).
Proof. exact (MK_COMB (@lem3646387) (@lem3646358 _93365 _93381 s f P)). Qed.
Lemma lem3646389 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term87 _93365 _93381 s P f) = (term88 _93365 _93381 s P f).
Proof. exact (MK_COMB (@lem3646388 _93365 _93381 s f P) (@lem3646386 _93365 _93381 s P f)). Qed.
Lemma lem3646390 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3646391 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) : (term89 _93365 _93381 s f P) = (term89 _93365 _93381 s f P).
Proof. exact (MK_COMB (@lem3646390) (@lem3646361 _93365 _93381 s f P)). Qed.
Lemma lem3646392 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term90 _93365 _93381 s P f) = (term91 _93365 _93381 s P f).
Proof. exact (MK_COMB (@lem3646391 _93365 _93381 s f P) (@lem3646383 _93365 _93381 s P f)). Qed.
Lemma lem3646393 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3646394 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term92 _93365 _93381 s P f) = (term93 _93365 _93381 s P f).
Proof. exact (MK_COMB (@lem3646393) (@lem3646392 _93365 _93381 s P f)). Qed.
Lemma lem3646395 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term94 _93365 _93381 s P f) = (term95 _93365 _93381 s P f).
Proof. exact (MK_COMB (@lem3646394 _93365 _93381 s P f) (@lem3646389 _93365 _93381 s P f)). Qed.
Lemma lem3646396 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term50 _93365 _93381 s P f) = (term94 _93365 _93381 s P f).
Proof. exact (@lem17646 (term21 _93365 _93381 s f P) (term24 _93365 _93381 s P f)). Qed.
Lemma lem3646397 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term50 _93365 _93381 s P f) = (term95 _93365 _93381 s P f).
Proof. exact (TRANS (@lem3646396 _93365 _93381 s P f) (@lem3646395 _93365 _93381 s P f)). Qed.
Lemma lem3646672 {A : Type'} (P : A -> Prop) (Q : Prop) : (term96 A P Q) = (term97 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3646673 {_93365 : Type'} (P : type686 _93365) (Q : Prop) : (term98 _93365 P Q) = (term99 _93365 P Q).
Proof. exact (@lem3646672 (_93365 -> Prop) P Q). Qed.
Lemma lem3646674 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) (t : _93381 -> Prop) : (term100 _93365 _93381 s f P t) = (term101 _93365 _93381 s f P t).
Proof. exact (@lem3646673 _93365 (term48 _93365 _93381 s t f) (P t)). Qed.
Lemma lem3646675 {_93365 _93381 : Type'} (s : _93365 -> Prop) (t : _93381 -> Prop) (f : _93365 -> _93381) (u : _93365 -> Prop) : (term57 _93365 _93381 s t f u) = (term47 _93365 _93381 s t f u).
Proof. exact (eq_refl (term57 _93365 _93381 s t f u)). Qed.
Lemma lem3646676 {_93365 _93381 : Type'} (s : _93365 -> Prop) (t : _93381 -> Prop) (f : _93365 -> _93381) : (term102 _93365 _93381 s t f) = (term48 _93365 _93381 s t f).
Proof. exact (fun_ext (fun u : _93365 -> Prop => @lem3646675 _93365 _93381 s t f u)). Qed.
Lemma lem3646677 {_93365 : Type'} : (@ex (_93365 -> Prop)) = (@ex (_93365 -> Prop)).
Proof. exact (eq_refl (@ex (_93365 -> Prop))). Qed.
Lemma lem3646678 {_93365 _93381 : Type'} (s : _93365 -> Prop) (t : _93381 -> Prop) (f : _93365 -> _93381) : (term103 _93365 _93381 s t f) = (term13 _93365 _93381 s t f).
Proof. exact (MK_COMB (@lem3646677 _93365) (@lem3646676 _93365 _93381 s t f)). Qed.
Lemma lem3646679 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3646680 {_93365 _93381 : Type'} (s : _93365 -> Prop) (t : _93381 -> Prop) (f : _93365 -> _93381) : (term104 _93365 _93381 s t f) = (term15 _93365 _93381 s t f).
Proof. exact (MK_COMB (@lem3646679) (@lem3646678 _93365 _93381 s t f)). Qed.
Lemma lem3646681 {_93381 : Type'} (P : type686 _93381) (t : _93381 -> Prop) : (P t) = (P t).
Proof. exact (eq_refl (P t)). Qed.
Lemma lem3646682 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) (t : _93381 -> Prop) : (term100 _93365 _93381 s f P t) = (term17 _93365 _93381 s f P t).
Proof. exact (MK_COMB (@lem3646680 _93365 _93381 s t f) (@lem3646681 _93381 P t)). Qed.
Lemma lem3646683 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3646684 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) (t : _93381 -> Prop) : (term105 _93365 _93381 s f P t) = (term106 _93365 _93381 s f P t).
Proof. exact (MK_COMB (@lem3646683) (@lem3646682 _93365 _93381 s f P t)). Qed.
Lemma lem3646685 {_93365 _93381 : Type'} (s : _93365 -> Prop) (t : _93381 -> Prop) (f : _93365 -> _93381) (u : _93365 -> Prop) : (term57 _93365 _93381 s t f u) = (term47 _93365 _93381 s t f u).
Proof. exact (eq_refl (term57 _93365 _93381 s t f u)). Qed.
Lemma lem3646686 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3646687 {_93365 _93381 : Type'} (s : _93365 -> Prop) (t : _93381 -> Prop) (f : _93365 -> _93381) (u : _93365 -> Prop) : (term107 _93365 _93381 s t f u) = (term108 _93365 _93381 s t f u).
Proof. exact (MK_COMB (@lem3646686) (@lem3646685 _93365 _93381 s t f u)). Qed.
Lemma lem3646688 {_93381 : Type'} (P : type686 _93381) (t : _93381 -> Prop) : (P t) = (P t).
Proof. exact (eq_refl (P t)). Qed.
Lemma lem3646689 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (u : _93365 -> Prop) (P : type686 _93381) (t : _93381 -> Prop) : (term109 _93365 _93381 s f u P t) = (term110 _93365 _93381 s f u P t).
Proof. exact (MK_COMB (@lem3646687 _93365 _93381 s t f u) (@lem3646688 _93381 P t)). Qed.
Lemma lem3646690 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) (t : _93381 -> Prop) : (term111 _93365 _93381 s f P t) = (term112 _93365 _93381 s f P t).
Proof. exact (fun_ext (fun u : _93365 -> Prop => @lem3646689 _93365 _93381 s f u P t)). Qed.
Lemma lem3646691 {_93365 : Type'} : (@ex (_93365 -> Prop)) = (@ex (_93365 -> Prop)).
Proof. exact (eq_refl (@ex (_93365 -> Prop))). Qed.
Lemma lem3646692 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) (t : _93381 -> Prop) : (term101 _93365 _93381 s f P t) = (term113 _93365 _93381 s f P t).
Proof. exact (MK_COMB (@lem3646691 _93365) (@lem3646690 _93365 _93381 s f P t)). Qed.
Lemma lem3646693 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) (t : _93381 -> Prop) : ((term100 _93365 _93381 s f P t) = (term101 _93365 _93381 s f P t)) = ((term17 _93365 _93381 s f P t) = (term113 _93365 _93381 s f P t)).
Proof. exact (MK_COMB (@lem3646684 _93365 _93381 s f P t) (@lem3646692 _93365 _93381 s f P t)). Qed.
Lemma lem3646694 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) (t : _93381 -> Prop) : (term17 _93365 _93381 s f P t) = (term113 _93365 _93381 s f P t).
Proof. exact (EQ_MP (@lem3646693 _93365 _93381 s f P t) (@lem3646674 _93365 _93381 s f P t)). Qed.
Lemma lem3646695 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) : (term19 _93365 _93381 s f P) = (term114 _93365 _93381 s f P).
Proof. exact (fun_ext (fun t : _93381 -> Prop => @lem3646694 _93365 _93381 s f P t)). Qed.
Lemma lem3646696 {_93381 : Type'} : (@ex (_93381 -> Prop)) = (@ex (_93381 -> Prop)).
Proof. exact (eq_refl (@ex (_93381 -> Prop))). Qed.
Lemma lem3646697 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) : (term21 _93365 _93381 s f P) = (term115 _93365 _93381 s f P).
Proof. exact (MK_COMB (@lem3646696 _93381) (@lem3646695 _93365 _93381 s f P)). Qed.
Lemma lem3646698 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3646699 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) : (term89 _93365 _93381 s f P) = (term116 _93365 _93381 s f P).
Proof. exact (MK_COMB (@lem3646698) (@lem3646697 _93365 _93381 s f P)). Qed.
Lemma lem3646700 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term84 _93365 _93381 s P f) = (term84 _93365 _93381 s P f).
Proof. exact (eq_refl (term84 _93365 _93381 s P f)). Qed.
Lemma lem3646701 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term91 _93365 _93381 s P f) = (term117 _93365 _93381 s P f).
Proof. exact (MK_COMB (@lem3646699 _93365 _93381 s f P) (@lem3646700 _93365 _93381 s P f)). Qed.
Lemma lem3646703 {A : Type'} (P : A -> Prop) (Q : Prop) : (term96 A P Q) = (term97 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3646704 {_93381 : Type'} (P : type686 _93381) (Q : Prop) : (term98 _93381 P Q) = (term99 _93381 P Q).
Proof. exact (@lem3646703 (_93381 -> Prop) P Q). Qed.
Lemma lem3646705 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term118 _93365 _93381 s P f) = (term119 _93365 _93381 s P f).
Proof. exact (@lem3646704 _93381 (term114 _93365 _93381 s f P) (term84 _93365 _93381 s P f)). Qed.
Lemma lem3646706 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) (t : _93381 -> Prop) : (term120 _93365 _93381 s f P t) = (term113 _93365 _93381 s f P t).
Proof. exact (eq_refl (term120 _93365 _93381 s f P t)). Qed.
Lemma lem3646707 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) : (term121 _93365 _93381 s f P) = (term114 _93365 _93381 s f P).
Proof. exact (fun_ext (fun t : _93381 -> Prop => @lem3646706 _93365 _93381 s f P t)). Qed.
Lemma lem3646708 {_93381 : Type'} : (@ex (_93381 -> Prop)) = (@ex (_93381 -> Prop)).
Proof. exact (eq_refl (@ex (_93381 -> Prop))). Qed.
Lemma lem3646709 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) : (term122 _93365 _93381 s f P) = (term115 _93365 _93381 s f P).
Proof. exact (MK_COMB (@lem3646708 _93381) (@lem3646707 _93365 _93381 s f P)). Qed.
Lemma lem3646710 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3646711 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) : (term123 _93365 _93381 s f P) = (term116 _93365 _93381 s f P).
Proof. exact (MK_COMB (@lem3646710) (@lem3646709 _93365 _93381 s f P)). Qed.
Lemma lem3646712 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term84 _93365 _93381 s P f) = (term84 _93365 _93381 s P f).
Proof. exact (eq_refl (term84 _93365 _93381 s P f)). Qed.
Lemma lem3646713 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term118 _93365 _93381 s P f) = (term117 _93365 _93381 s P f).
Proof. exact (MK_COMB (@lem3646711 _93365 _93381 s f P) (@lem3646712 _93365 _93381 s P f)). Qed.
Lemma lem3646714 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3646715 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term124 _93365 _93381 s P f) = (term125 _93365 _93381 s P f).
Proof. exact (MK_COMB (@lem3646714) (@lem3646713 _93365 _93381 s P f)). Qed.
Lemma lem3646716 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) (t : _93381 -> Prop) : (term120 _93365 _93381 s f P t) = (term113 _93365 _93381 s f P t).
Proof. exact (eq_refl (term120 _93365 _93381 s f P t)). Qed.
Lemma lem3646717 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3646718 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) (t : _93381 -> Prop) : (term126 _93365 _93381 s f P t) = (term127 _93365 _93381 s f P t).
Proof. exact (MK_COMB (@lem3646717) (@lem3646716 _93365 _93381 s f P t)). Qed.
Lemma lem3646719 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term84 _93365 _93381 s P f) = (term84 _93365 _93381 s P f).
Proof. exact (eq_refl (term84 _93365 _93381 s P f)). Qed.
Lemma lem3646720 {_93365 _93381 : Type'} (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term128 _93365 _93381 t s P f) = (term129 _93365 _93381 t s P f).
Proof. exact (MK_COMB (@lem3646718 _93365 _93381 s f P t) (@lem3646719 _93365 _93381 s P f)). Qed.
Lemma lem3646721 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term130 _93365 _93381 s P f) = (term131 _93365 _93381 s P f).
Proof. exact (fun_ext (fun t : _93381 -> Prop => @lem3646720 _93365 _93381 t s P f)). Qed.
Lemma lem3646722 {_93381 : Type'} : (@ex (_93381 -> Prop)) = (@ex (_93381 -> Prop)).
Proof. exact (eq_refl (@ex (_93381 -> Prop))). Qed.
Lemma lem3646723 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term119 _93365 _93381 s P f) = (term132 _93365 _93381 s P f).
Proof. exact (MK_COMB (@lem3646722 _93381) (@lem3646721 _93365 _93381 s P f)). Qed.
Lemma lem3646724 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : ((term118 _93365 _93381 s P f) = (term119 _93365 _93381 s P f)) = ((term117 _93365 _93381 s P f) = (term132 _93365 _93381 s P f)).
Proof. exact (MK_COMB (@lem3646715 _93365 _93381 s P f) (@lem3646723 _93365 _93381 s P f)). Qed.
Lemma lem3646725 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term117 _93365 _93381 s P f) = (term132 _93365 _93381 s P f).
Proof. exact (EQ_MP (@lem3646724 _93365 _93381 s P f) (@lem3646705 _93365 _93381 s P f)). Qed.
Lemma lem3646727 {A : Type'} (P : A -> Prop) (Q : Prop) : (term96 A P Q) = (term97 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3646728 {_93365 : Type'} (P : type686 _93365) (Q : Prop) : (term98 _93365 P Q) = (term99 _93365 P Q).
Proof. exact (@lem3646727 (_93365 -> Prop) P Q). Qed.
Lemma lem3646729 {_93365 _93381 : Type'} (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term133 _93365 _93381 t s P f) = (term134 _93365 _93381 t s P f).
Proof. exact (@lem3646728 _93365 (term112 _93365 _93381 s f P t) (term84 _93365 _93381 s P f)). Qed.
Lemma lem3646730 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (u : _93365 -> Prop) (P : type686 _93381) (t : _93381 -> Prop) : (term135 _93365 _93381 s f P t u) = (term110 _93365 _93381 s f u P t).
Proof. exact (eq_refl (term135 _93365 _93381 s f P t u)). Qed.
Lemma lem3646731 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) (t : _93381 -> Prop) : (term136 _93365 _93381 s f P t) = (term112 _93365 _93381 s f P t).
Proof. exact (fun_ext (fun u : _93365 -> Prop => @lem3646730 _93365 _93381 s f u P t)). Qed.
Lemma lem3646732 {_93365 : Type'} : (@ex (_93365 -> Prop)) = (@ex (_93365 -> Prop)).
Proof. exact (eq_refl (@ex (_93365 -> Prop))). Qed.
Lemma lem3646733 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) (t : _93381 -> Prop) : (term137 _93365 _93381 s f P t) = (term113 _93365 _93381 s f P t).
Proof. exact (MK_COMB (@lem3646732 _93365) (@lem3646731 _93365 _93381 s f P t)). Qed.
Lemma lem3646734 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3646735 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) (t : _93381 -> Prop) : (term138 _93365 _93381 s f P t) = (term127 _93365 _93381 s f P t).
Proof. exact (MK_COMB (@lem3646734) (@lem3646733 _93365 _93381 s f P t)). Qed.
Lemma lem3646736 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term84 _93365 _93381 s P f) = (term84 _93365 _93381 s P f).
Proof. exact (eq_refl (term84 _93365 _93381 s P f)). Qed.
Lemma lem3646737 {_93365 _93381 : Type'} (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term133 _93365 _93381 t s P f) = (term129 _93365 _93381 t s P f).
Proof. exact (MK_COMB (@lem3646735 _93365 _93381 s f P t) (@lem3646736 _93365 _93381 s P f)). Qed.
Lemma lem3646738 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3646739 {_93365 _93381 : Type'} (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term139 _93365 _93381 t s P f) = (term140 _93365 _93381 t s P f).
Proof. exact (MK_COMB (@lem3646738) (@lem3646737 _93365 _93381 t s P f)). Qed.
Lemma lem3646740 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (u : _93365 -> Prop) (P : type686 _93381) (t : _93381 -> Prop) : (term135 _93365 _93381 s f P t u) = (term110 _93365 _93381 s f u P t).
Proof. exact (eq_refl (term135 _93365 _93381 s f P t u)). Qed.
Lemma lem3646741 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3646742 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (u : _93365 -> Prop) (P : type686 _93381) (t : _93381 -> Prop) : (term141 _93365 _93381 s f P t u) = (term142 _93365 _93381 s f u P t).
Proof. exact (MK_COMB (@lem3646741) (@lem3646740 _93365 _93381 s f u P t)). Qed.
Lemma lem3646743 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term84 _93365 _93381 s P f) = (term84 _93365 _93381 s P f).
Proof. exact (eq_refl (term84 _93365 _93381 s P f)). Qed.
Lemma lem3646744 {_93365 _93381 : Type'} (u : _93365 -> Prop) (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term143 _93365 _93381 t u s P f) = (term144 _93365 _93381 u t s P f).
Proof. exact (MK_COMB (@lem3646742 _93365 _93381 s f u P t) (@lem3646743 _93365 _93381 s P f)). Qed.
Lemma lem3646745 {_93365 _93381 : Type'} (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term145 _93365 _93381 t s P f) = (term146 _93365 _93381 t s P f).
Proof. exact (fun_ext (fun u : _93365 -> Prop => @lem3646744 _93365 _93381 u t s P f)). Qed.
Lemma lem3646746 {_93365 : Type'} : (@ex (_93365 -> Prop)) = (@ex (_93365 -> Prop)).
Proof. exact (eq_refl (@ex (_93365 -> Prop))). Qed.
Lemma lem3646747 {_93365 _93381 : Type'} (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term134 _93365 _93381 t s P f) = (term147 _93365 _93381 t s P f).
Proof. exact (MK_COMB (@lem3646746 _93365) (@lem3646745 _93365 _93381 t s P f)). Qed.
Lemma lem3646748 {_93365 _93381 : Type'} (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : ((term133 _93365 _93381 t s P f) = (term134 _93365 _93381 t s P f)) = ((term129 _93365 _93381 t s P f) = (term147 _93365 _93381 t s P f)).
Proof. exact (MK_COMB (@lem3646739 _93365 _93381 t s P f) (@lem3646747 _93365 _93381 t s P f)). Qed.
Lemma lem3646749 {_93365 _93381 : Type'} (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term129 _93365 _93381 t s P f) = (term147 _93365 _93381 t s P f).
Proof. exact (EQ_MP (@lem3646748 _93365 _93381 t s P f) (@lem3646729 _93365 _93381 t s P f)). Qed.
Lemma lem3646750 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term131 _93365 _93381 s P f) = (term148 _93365 _93381 s P f).
Proof. exact (fun_ext (fun t : _93381 -> Prop => @lem3646749 _93365 _93381 t s P f)). Qed.
Lemma lem3646751 {_93381 : Type'} : (@ex (_93381 -> Prop)) = (@ex (_93381 -> Prop)).
Proof. exact (eq_refl (@ex (_93381 -> Prop))). Qed.
Lemma lem3646752 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term132 _93365 _93381 s P f) = (term149 _93365 _93381 s P f).
Proof. exact (MK_COMB (@lem3646751 _93381) (@lem3646750 _93365 _93381 s P f)). Qed.
Lemma lem3646753 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term117 _93365 _93381 s P f) = (term149 _93365 _93381 s P f).
Proof. exact (TRANS (@lem3646725 _93365 _93381 s P f) (@lem3646752 _93365 _93381 s P f)). Qed.
Lemma lem3646754 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term91 _93365 _93381 s P f) = (term149 _93365 _93381 s P f).
Proof. exact (TRANS (@lem3646701 _93365 _93381 s P f) (@lem3646753 _93365 _93381 s P f)). Qed.
Lemma lem3646755 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3646756 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term93 _93365 _93381 s P f) = (term150 _93365 _93381 s P f).
Proof. exact (MK_COMB (@lem3646755) (@lem3646754 _93365 _93381 s P f)). Qed.
Lemma lem3646758 {A : Type'} (P : Prop) (Q : A -> Prop) : (term151 A P Q) = (term152 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3646759 {_93365 : Type'} (P : Prop) (Q : type686 _93365) : (term153 _93365 P Q) = (term154 _93365 P Q).
Proof. exact (@lem3646758 (_93365 -> Prop) P Q). Qed.
Lemma lem3646760 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term155 _93365 _93381 s P f) = (term156 _93365 _93381 s P f).
Proof. exact (@lem3646759 _93365 (term74 _93365 _93381 s f P) (term46 _93365 _93381 s P f)). Qed.
Lemma lem3646761 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (t : _93365 -> Prop) : (term80 _93365 _93381 s P f t) = (term45 _93365 _93381 s P f t).
Proof. exact (eq_refl (term80 _93365 _93381 s P f t)). Qed.
Lemma lem3646762 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term157 _93365 _93381 s P f) = (term46 _93365 _93381 s P f).
Proof. exact (fun_ext (fun t : _93365 -> Prop => @lem3646761 _93365 _93381 s P f t)). Qed.
Lemma lem3646763 {_93365 : Type'} : (@ex (_93365 -> Prop)) = (@ex (_93365 -> Prop)).
Proof. exact (eq_refl (@ex (_93365 -> Prop))). Qed.
Lemma lem3646764 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term158 _93365 _93381 s P f) = (term24 _93365 _93381 s P f).
Proof. exact (MK_COMB (@lem3646763 _93365) (@lem3646762 _93365 _93381 s P f)). Qed.
Lemma lem3646765 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) : (term86 _93365 _93381 s f P) = (term86 _93365 _93381 s f P).
Proof. exact (eq_refl (term86 _93365 _93381 s f P)). Qed.
Lemma lem3646766 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term155 _93365 _93381 s P f) = (term88 _93365 _93381 s P f).
Proof. exact (MK_COMB (@lem3646765 _93365 _93381 s f P) (@lem3646764 _93365 _93381 s P f)). Qed.
Lemma lem3646767 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3646768 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term159 _93365 _93381 s P f) = (term160 _93365 _93381 s P f).
Proof. exact (MK_COMB (@lem3646767) (@lem3646766 _93365 _93381 s P f)). Qed.
Lemma lem3646769 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (t : _93365 -> Prop) : (term80 _93365 _93381 s P f t) = (term45 _93365 _93381 s P f t).
Proof. exact (eq_refl (term80 _93365 _93381 s P f t)). Qed.
Lemma lem3646770 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) : (term86 _93365 _93381 s f P) = (term86 _93365 _93381 s f P).
Proof. exact (eq_refl (term86 _93365 _93381 s f P)). Qed.
Lemma lem3646771 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (t : _93365 -> Prop) : (term161 _93365 _93381 s P f t) = (term162 _93365 _93381 s P f t).
Proof. exact (MK_COMB (@lem3646770 _93365 _93381 s f P) (@lem3646769 _93365 _93381 s P f t)). Qed.
Lemma lem3646772 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term163 _93365 _93381 s P f) = (term164 _93365 _93381 s P f).
Proof. exact (fun_ext (fun t : _93365 -> Prop => @lem3646771 _93365 _93381 s P f t)). Qed.
Lemma lem3646773 {_93365 : Type'} : (@ex (_93365 -> Prop)) = (@ex (_93365 -> Prop)).
Proof. exact (eq_refl (@ex (_93365 -> Prop))). Qed.
Lemma lem3646774 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term156 _93365 _93381 s P f) = (term165 _93365 _93381 s P f).
Proof. exact (MK_COMB (@lem3646773 _93365) (@lem3646772 _93365 _93381 s P f)). Qed.
Lemma lem3646775 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : ((term155 _93365 _93381 s P f) = (term156 _93365 _93381 s P f)) = ((term88 _93365 _93381 s P f) = (term165 _93365 _93381 s P f)).
Proof. exact (MK_COMB (@lem3646768 _93365 _93381 s P f) (@lem3646774 _93365 _93381 s P f)). Qed.
Lemma lem3646776 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term88 _93365 _93381 s P f) = (term165 _93365 _93381 s P f).
Proof. exact (EQ_MP (@lem3646775 _93365 _93381 s P f) (@lem3646760 _93365 _93381 s P f)). Qed.
Lemma lem3646777 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term95 _93365 _93381 s P f) = (term166 _93365 _93381 s P f).
Proof. exact (MK_COMB (@lem3646756 _93365 _93381 s P f) (@lem3646776 _93365 _93381 s P f)). Qed.
Lemma lem3646781 {A : Type'} (P : A -> Prop) (Q : Prop) : (term167 A P Q) = (term168 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3646782 {_93381 : Type'} (P : type686 _93381) (Q : Prop) : (term169 _93381 P Q) = (term170 _93381 P Q).
Proof. exact (@lem3646781 (_93381 -> Prop) P Q). Qed.
Lemma lem3646783 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term171 _93365 _93381 s P f) = (term172 _93365 _93381 s P f).
Proof. exact (@lem3646782 _93381 (term148 _93365 _93381 s P f) (term165 _93365 _93381 s P f)). Qed.
Lemma lem3646784 {_93365 _93381 : Type'} (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term173 _93365 _93381 s P f t) = (term147 _93365 _93381 t s P f).
Proof. exact (eq_refl (term173 _93365 _93381 s P f t)). Qed.
Lemma lem3646785 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term174 _93365 _93381 s P f) = (term148 _93365 _93381 s P f).
Proof. exact (fun_ext (fun t : _93381 -> Prop => @lem3646784 _93365 _93381 t s P f)). Qed.
Lemma lem3646786 {_93381 : Type'} : (@ex (_93381 -> Prop)) = (@ex (_93381 -> Prop)).
Proof. exact (eq_refl (@ex (_93381 -> Prop))). Qed.
Lemma lem3646787 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term175 _93365 _93381 s P f) = (term149 _93365 _93381 s P f).
Proof. exact (MK_COMB (@lem3646786 _93381) (@lem3646785 _93365 _93381 s P f)). Qed.
Lemma lem3646788 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3646789 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term176 _93365 _93381 s P f) = (term150 _93365 _93381 s P f).
Proof. exact (MK_COMB (@lem3646788) (@lem3646787 _93365 _93381 s P f)). Qed.
Lemma lem3646790 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term165 _93365 _93381 s P f) = (term165 _93365 _93381 s P f).
Proof. exact (eq_refl (term165 _93365 _93381 s P f)). Qed.
Lemma lem3646791 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term171 _93365 _93381 s P f) = (term166 _93365 _93381 s P f).
Proof. exact (MK_COMB (@lem3646789 _93365 _93381 s P f) (@lem3646790 _93365 _93381 s P f)). Qed.
Lemma lem3646792 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3646793 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term177 _93365 _93381 s P f) = (term178 _93365 _93381 s P f).
Proof. exact (MK_COMB (@lem3646792) (@lem3646791 _93365 _93381 s P f)). Qed.
Lemma lem3646794 {_93365 _93381 : Type'} (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term173 _93365 _93381 s P f t) = (term147 _93365 _93381 t s P f).
Proof. exact (eq_refl (term173 _93365 _93381 s P f t)). Qed.
Lemma lem3646795 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3646796 {_93365 _93381 : Type'} (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term179 _93365 _93381 s P f t) = (term180 _93365 _93381 t s P f).
Proof. exact (MK_COMB (@lem3646795) (@lem3646794 _93365 _93381 t s P f)). Qed.
Lemma lem3646797 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term165 _93365 _93381 s P f) = (term165 _93365 _93381 s P f).
Proof. exact (eq_refl (term165 _93365 _93381 s P f)). Qed.
Lemma lem3646798 {_93365 _93381 : Type'} (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term181 _93365 _93381 t s P f) = (term182 _93365 _93381 t s P f).
Proof. exact (MK_COMB (@lem3646796 _93365 _93381 t s P f) (@lem3646797 _93365 _93381 s P f)). Qed.
Lemma lem3646799 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term183 _93365 _93381 s P f) = (term184 _93365 _93381 s P f).
Proof. exact (fun_ext (fun t : _93381 -> Prop => @lem3646798 _93365 _93381 t s P f)). Qed.
Lemma lem3646800 {_93381 : Type'} : (@ex (_93381 -> Prop)) = (@ex (_93381 -> Prop)).
Proof. exact (eq_refl (@ex (_93381 -> Prop))). Qed.
Lemma lem3646801 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term172 _93365 _93381 s P f) = (term185 _93365 _93381 s P f).
Proof. exact (MK_COMB (@lem3646800 _93381) (@lem3646799 _93365 _93381 s P f)). Qed.
Lemma lem3646802 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : ((term171 _93365 _93381 s P f) = (term172 _93365 _93381 s P f)) = ((term166 _93365 _93381 s P f) = (term185 _93365 _93381 s P f)).
Proof. exact (MK_COMB (@lem3646793 _93365 _93381 s P f) (@lem3646801 _93365 _93381 s P f)). Qed.
Lemma lem3646803 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term166 _93365 _93381 s P f) = (term185 _93365 _93381 s P f).
Proof. exact (EQ_MP (@lem3646802 _93365 _93381 s P f) (@lem3646783 _93365 _93381 s P f)). Qed.
Lemma lem3646805 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term186 A P Q) = (term187 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3646806 {_93365 : Type'} (P : type686 _93365) (Q : type686 _93365) : (term188 _93365 P Q) = (term189 _93365 P Q).
Proof. exact (@lem3646805 (_93365 -> Prop) P Q). Qed.
Lemma lem3646807 {_93365 _93381 : Type'} (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term190 _93365 _93381 t s P f) = (term191 _93365 _93381 t s P f).
Proof. exact (@lem3646806 _93365 (term146 _93365 _93381 t s P f) (term164 _93365 _93381 s P f)). Qed.
Lemma lem3646808 {_93365 _93381 : Type'} (u : _93365 -> Prop) (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term192 _93365 _93381 t s P f u) = (term144 _93365 _93381 u t s P f).
Proof. exact (eq_refl (term192 _93365 _93381 t s P f u)). Qed.
Lemma lem3646809 {_93365 _93381 : Type'} (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term193 _93365 _93381 t s P f) = (term146 _93365 _93381 t s P f).
Proof. exact (fun_ext (fun u : _93365 -> Prop => @lem3646808 _93365 _93381 u t s P f)). Qed.
Lemma lem3646810 {_93365 : Type'} : (@ex (_93365 -> Prop)) = (@ex (_93365 -> Prop)).
Proof. exact (eq_refl (@ex (_93365 -> Prop))). Qed.
Lemma lem3646811 {_93365 _93381 : Type'} (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term194 _93365 _93381 t s P f) = (term147 _93365 _93381 t s P f).
Proof. exact (MK_COMB (@lem3646810 _93365) (@lem3646809 _93365 _93381 t s P f)). Qed.
Lemma lem3646812 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3646813 {_93365 _93381 : Type'} (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term195 _93365 _93381 t s P f) = (term180 _93365 _93381 t s P f).
Proof. exact (MK_COMB (@lem3646812) (@lem3646811 _93365 _93381 t s P f)). Qed.
Lemma lem3646814 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (u : _93365 -> Prop) : (term196 _93365 _93381 s P f u) = (term162 _93365 _93381 s P f u).
Proof. exact (eq_refl (term196 _93365 _93381 s P f u)). Qed.
Lemma lem3646815 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term197 _93365 _93381 s P f) = (term164 _93365 _93381 s P f).
Proof. exact (fun_ext (fun u : _93365 -> Prop => @lem3646814 _93365 _93381 s P f u)). Qed.
Lemma lem3646816 {_93365 : Type'} : (@ex (_93365 -> Prop)) = (@ex (_93365 -> Prop)).
Proof. exact (eq_refl (@ex (_93365 -> Prop))). Qed.
Lemma lem3646817 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term198 _93365 _93381 s P f) = (term165 _93365 _93381 s P f).
Proof. exact (MK_COMB (@lem3646816 _93365) (@lem3646815 _93365 _93381 s P f)). Qed.
Lemma lem3646818 {_93365 _93381 : Type'} (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term190 _93365 _93381 t s P f) = (term182 _93365 _93381 t s P f).
Proof. exact (MK_COMB (@lem3646813 _93365 _93381 t s P f) (@lem3646817 _93365 _93381 s P f)). Qed.
Lemma lem3646819 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3646820 {_93365 _93381 : Type'} (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term199 _93365 _93381 t s P f) = (term200 _93365 _93381 t s P f).
Proof. exact (MK_COMB (@lem3646819) (@lem3646818 _93365 _93381 t s P f)). Qed.
Lemma lem3646821 {_93365 _93381 : Type'} (u : _93365 -> Prop) (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term192 _93365 _93381 t s P f u) = (term144 _93365 _93381 u t s P f).
Proof. exact (eq_refl (term192 _93365 _93381 t s P f u)). Qed.
Lemma lem3646822 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3646823 {_93365 _93381 : Type'} (u : _93365 -> Prop) (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term201 _93365 _93381 t s P f u) = (term202 _93365 _93381 u t s P f).
Proof. exact (MK_COMB (@lem3646822) (@lem3646821 _93365 _93381 u t s P f)). Qed.
Lemma lem3646824 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (u : _93365 -> Prop) : (term196 _93365 _93381 s P f u) = (term162 _93365 _93381 s P f u).
Proof. exact (eq_refl (term196 _93365 _93381 s P f u)). Qed.
Lemma lem3646825 {_93365 _93381 : Type'} (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (u : _93365 -> Prop) : (term203 _93365 _93381 t s P f u) = (term204 _93365 _93381 t s P f u).
Proof. exact (MK_COMB (@lem3646823 _93365 _93381 u t s P f) (@lem3646824 _93365 _93381 s P f u)). Qed.
Lemma lem3646826 {_93365 _93381 : Type'} (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term205 _93365 _93381 t s P f) = (term206 _93365 _93381 t s P f).
Proof. exact (fun_ext (fun u : _93365 -> Prop => @lem3646825 _93365 _93381 t s P f u)). Qed.
Lemma lem3646827 {_93365 : Type'} : (@ex (_93365 -> Prop)) = (@ex (_93365 -> Prop)).
Proof. exact (eq_refl (@ex (_93365 -> Prop))). Qed.
Lemma lem3646828 {_93365 _93381 : Type'} (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term191 _93365 _93381 t s P f) = (term207 _93365 _93381 t s P f).
Proof. exact (MK_COMB (@lem3646827 _93365) (@lem3646826 _93365 _93381 t s P f)). Qed.
Lemma lem3646829 {_93365 _93381 : Type'} (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : ((term190 _93365 _93381 t s P f) = (term191 _93365 _93381 t s P f)) = ((term182 _93365 _93381 t s P f) = (term207 _93365 _93381 t s P f)).
Proof. exact (MK_COMB (@lem3646820 _93365 _93381 t s P f) (@lem3646828 _93365 _93381 t s P f)). Qed.
Lemma lem3646830 {_93365 _93381 : Type'} (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term182 _93365 _93381 t s P f) = (term207 _93365 _93381 t s P f).
Proof. exact (EQ_MP (@lem3646829 _93365 _93381 t s P f) (@lem3646807 _93365 _93381 t s P f)). Qed.
Lemma lem3646833 {_93365 _93381 : Type'} (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term208 _93365 _93381 t s P f) = (term208 _93365 _93381 t s P f).
Proof. exact (eq_refl (term208 _93365 _93381 t s P f)). Qed.
Lemma lem3646834 {_93365 _93381 : Type'} (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term208 _93365 _93381 t s P f) = ((term182 _93365 _93381 t s P f) = (term207 _93365 _93381 t s P f)).
Proof. exact (eq_refl (term208 _93365 _93381 t s P f)). Qed.
Lemma lem3646835 {_93365 _93381 : Type'} (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term209 _93365 _93381 t s P f) = (term209 _93365 _93381 t s P f).
Proof. exact (eq_refl (term209 _93365 _93381 t s P f)). Qed.
Lemma lem3646836 {_93365 _93381 : Type'} (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : ((term208 _93365 _93381 t s P f) = (term208 _93365 _93381 t s P f)) = ((term208 _93365 _93381 t s P f) = ((term182 _93365 _93381 t s P f) = (term207 _93365 _93381 t s P f))).
Proof. exact (MK_COMB (@lem3646835 _93365 _93381 t s P f) (@lem3646834 _93365 _93381 t s P f)). Qed.
Lemma lem3646837 {_93365 _93381 : Type'} (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term208 _93365 _93381 t s P f) = ((term182 _93365 _93381 t s P f) = (term207 _93365 _93381 t s P f)).
Proof. exact (eq_refl (term208 _93365 _93381 t s P f)). Qed.
Lemma lem3646838 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3646839 {_93365 _93381 : Type'} (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term209 _93365 _93381 t s P f) = (term210 _93365 _93381 t s P f).
Proof. exact (MK_COMB (@lem3646838) (@lem3646837 _93365 _93381 t s P f)). Qed.
Lemma lem3646840 {_93365 _93381 : Type'} (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : ((term182 _93365 _93381 t s P f) = (term207 _93365 _93381 t s P f)) = ((term182 _93365 _93381 t s P f) = (term207 _93365 _93381 t s P f)).
Proof. exact (eq_refl ((term182 _93365 _93381 t s P f) = (term207 _93365 _93381 t s P f))). Qed.
Lemma lem3646841 {_93365 _93381 : Type'} (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : ((term208 _93365 _93381 t s P f) = ((term182 _93365 _93381 t s P f) = (term207 _93365 _93381 t s P f))) = (((term182 _93365 _93381 t s P f) = (term207 _93365 _93381 t s P f)) = ((term182 _93365 _93381 t s P f) = (term207 _93365 _93381 t s P f))).
Proof. exact (MK_COMB (@lem3646839 _93365 _93381 t s P f) (@lem3646840 _93365 _93381 t s P f)). Qed.
Lemma lem3646842 {_93365 _93381 : Type'} (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : ((term208 _93365 _93381 t s P f) = (term208 _93365 _93381 t s P f)) = (((term182 _93365 _93381 t s P f) = (term207 _93365 _93381 t s P f)) = ((term182 _93365 _93381 t s P f) = (term207 _93365 _93381 t s P f))).
Proof. exact (TRANS (@lem3646836 _93365 _93381 t s P f) (@lem3646841 _93365 _93381 t s P f)). Qed.
Lemma lem3646843 {_93365 _93381 : Type'} (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : ((term182 _93365 _93381 t s P f) = (term207 _93365 _93381 t s P f)) = ((term182 _93365 _93381 t s P f) = (term207 _93365 _93381 t s P f)).
Proof. exact (EQ_MP (@lem3646842 _93365 _93381 t s P f) (@lem3646833 _93365 _93381 t s P f)). Qed.
Lemma lem3646844 {_93365 _93381 : Type'} (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term182 _93365 _93381 t s P f) = (term207 _93365 _93381 t s P f).
Proof. exact (EQ_MP (@lem3646843 _93365 _93381 t s P f) (@lem3646830 _93365 _93381 t s P f)). Qed.
Lemma lem3646845 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term184 _93365 _93381 s P f) = (term211 _93365 _93381 s P f).
Proof. exact (fun_ext (fun t : _93381 -> Prop => @lem3646844 _93365 _93381 t s P f)). Qed.
Lemma lem3646846 {_93381 : Type'} : (@ex (_93381 -> Prop)) = (@ex (_93381 -> Prop)).
Proof. exact (eq_refl (@ex (_93381 -> Prop))). Qed.
Lemma lem3646847 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term185 _93365 _93381 s P f) = (term212 _93365 _93381 s P f).
Proof. exact (MK_COMB (@lem3646846 _93381) (@lem3646845 _93365 _93381 s P f)). Qed.
Lemma lem3646848 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term166 _93365 _93381 s P f) = (term212 _93365 _93381 s P f).
Proof. exact (TRANS (@lem3646803 _93365 _93381 s P f) (@lem3646847 _93365 _93381 s P f)). Qed.
Lemma lem3646850 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term95 _93365 _93381 s P f) = (term212 _93365 _93381 s P f).
Proof. exact (TRANS (@lem3646777 _93365 _93381 s P f) (@lem3646848 _93365 _93381 s P f)). Qed.
Lemma lem3646851 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term50 _93365 _93381 s P f) = (term212 _93365 _93381 s P f).
Proof. exact (TRANS (@lem3646397 _93365 _93381 s P f) (@lem3646850 _93365 _93381 s P f)). Qed.
Lemma lem3646852 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (h1 : term50 _93365 _93381 s P f) : term212 _93365 _93381 s P f.
Proof. exact (EQ_MP (@lem3646851 _93365 _93381 s P f) (@lem3646313 _93365 _93381 s P f h1)). Qed.
Lemma lem3646853 {_93365 _93381 : Type'} (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (h1 : term207 _93365 _93381 t s P f) : term207 _93365 _93381 t s P f.
Proof. exact (h1). Qed.
Lemma lem3646854 {_93365 _93381 : Type'} (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (u : _93365 -> Prop) (h1 : term204 _93365 _93381 t s P f u) : term204 _93365 _93381 t s P f u.
Proof. exact (h1). Qed.
Lemma lem3646869 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (u : _93365 -> Prop) : (term45 _93365 _93381 s P f u) = (term45 _93365 _93381 s P f u).
Proof. exact (eq_refl (term45 _93365 _93381 s P f u)). Qed.
Lemma lem3646874 {_93381 : Type'} (P : type686 _93381) (t : _93381 -> Prop) : (term62 _93381 P t) = (term62 _93381 P t).
Proof. exact (eq_refl (term62 _93381 P t)). Qed.
Lemma lem3646895 {_93365 _93381 : Type'} (s : _93365 -> Prop) (t : _93381 -> Prop) (f : _93365 -> _93381) (u : _93365 -> Prop) : (term52 _93365 _93381 s t f u) = (term52 _93365 _93381 s t f u).
Proof. exact (eq_refl (term52 _93365 _93381 s t f u)). Qed.
Lemma lem3646896 {_93365 _93381 : Type'} (s : _93365 -> Prop) (t : _93381 -> Prop) (f : _93365 -> _93381) : (term60 _93365 _93381 s t f) = (term60 _93365 _93381 s t f).
Proof. exact (fun_ext (fun u : _93365 -> Prop => @lem3646895 _93365 _93381 s t f u)). Qed.
Lemma lem3646897 {_93365 : Type'} : (@all (_93365 -> Prop)) = (@all (_93365 -> Prop)).
Proof. exact (eq_refl (@all (_93365 -> Prop))). Qed.
Lemma lem3646898 {_93365 _93381 : Type'} (s : _93365 -> Prop) (t : _93381 -> Prop) (f : _93365 -> _93381) : (term61 _93365 _93381 s t f) = (term61 _93365 _93381 s t f).
Proof. exact (MK_COMB (@lem3646897 _93365) (@lem3646896 _93365 _93381 s t f)). Qed.
Lemma lem3646899 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3646900 {_93365 _93381 : Type'} (s : _93365 -> Prop) (t : _93381 -> Prop) (f : _93365 -> _93381) : (term64 _93365 _93381 s t f) = (term64 _93365 _93381 s t f).
Proof. exact (MK_COMB (@lem3646899) (@lem3646898 _93365 _93381 s t f)). Qed.
Lemma lem3646901 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) (t : _93381 -> Prop) : (term66 _93365 _93381 s f P t) = (term66 _93365 _93381 s f P t).
Proof. exact (MK_COMB (@lem3646900 _93365 _93381 s t f) (@lem3646874 _93381 P t)). Qed.
Lemma lem3646902 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) : (term73 _93365 _93381 s f P) = (term73 _93365 _93381 s f P).
Proof. exact (fun_ext (fun t : _93381 -> Prop => @lem3646901 _93365 _93381 s f P t)). Qed.
Lemma lem3646903 {_93381 : Type'} : (@all (_93381 -> Prop)) = (@all (_93381 -> Prop)).
Proof. exact (eq_refl (@all (_93381 -> Prop))). Qed.
Lemma lem3646904 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) : (term74 _93365 _93381 s f P) = (term74 _93365 _93381 s f P).
Proof. exact (MK_COMB (@lem3646903 _93381) (@lem3646902 _93365 _93381 s f P)). Qed.
Lemma lem3646905 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3646906 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) : (term86 _93365 _93381 s f P) = (term86 _93365 _93381 s f P).
Proof. exact (MK_COMB (@lem3646905) (@lem3646904 _93365 _93381 s f P)). Qed.
Lemma lem3646907 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (u : _93365 -> Prop) : (term162 _93365 _93381 s P f u) = (term162 _93365 _93381 s P f u).
Proof. exact (MK_COMB (@lem3646906 _93365 _93381 s f P) (@lem3646869 _93365 _93381 s P f u)). Qed.
Lemma lem3646926 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (t : _93365 -> Prop) : (term76 _93365 _93381 s P f t) = (term76 _93365 _93381 s P f t).
Proof. exact (eq_refl (term76 _93365 _93381 s P f t)). Qed.
Lemma lem3646927 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term83 _93365 _93381 s P f) = (term83 _93365 _93381 s P f).
Proof. exact (fun_ext (fun t : _93365 -> Prop => @lem3646926 _93365 _93381 s P f t)). Qed.
Lemma lem3646928 {_93365 : Type'} : (@all (_93365 -> Prop)) = (@all (_93365 -> Prop)).
Proof. exact (eq_refl (@all (_93365 -> Prop))). Qed.
Lemma lem3646929 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term84 _93365 _93381 s P f) = (term84 _93365 _93381 s P f).
Proof. exact (MK_COMB (@lem3646928 _93365) (@lem3646927 _93365 _93381 s P f)). Qed.
Lemma lem3646954 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (u : _93365 -> Prop) (P : type686 _93381) (t : _93381 -> Prop) : (term142 _93365 _93381 s f u P t) = (term142 _93365 _93381 s f u P t).
Proof. exact (eq_refl (term142 _93365 _93381 s f u P t)). Qed.
Lemma lem3646955 {_93365 _93381 : Type'} (u : _93365 -> Prop) (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term144 _93365 _93381 u t s P f) = (term144 _93365 _93381 u t s P f).
Proof. exact (MK_COMB (@lem3646954 _93365 _93381 s f u P t) (@lem3646929 _93365 _93381 s P f)). Qed.
Lemma lem3646956 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3646957 {_93365 _93381 : Type'} (u : _93365 -> Prop) (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term202 _93365 _93381 u t s P f) = (term202 _93365 _93381 u t s P f).
Proof. exact (MK_COMB (@lem3646956) (@lem3646955 _93365 _93381 u t s P f)). Qed.
Lemma lem3646958 {_93365 _93381 : Type'} (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (u : _93365 -> Prop) : (term204 _93365 _93381 t s P f u) = (term204 _93365 _93381 t s P f u).
Proof. exact (MK_COMB (@lem3646957 _93365 _93381 u t s P f) (@lem3646907 _93365 _93381 s P f u)). Qed.
Lemma lem3646959 {_93365 _93381 : Type'} (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (u : _93365 -> Prop) (h1 : term204 _93365 _93381 t s P f u) : term204 _93365 _93381 t s P f u.
Proof. exact (EQ_MP (@lem3646958 _93365 _93381 t s P f u) (@lem3646854 _93365 _93381 t s P f u h1)). Qed.
Lemma lem3646960 {_93365 _93381 : Type'} (u : _93365 -> Prop) (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (h1 : term144 _93365 _93381 u t s P f) : term144 _93365 _93381 u t s P f.
Proof. exact (h1). Qed.
Lemma lem3646961 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (u : _93365 -> Prop) (h1 : term162 _93365 _93381 s P f u) : term162 _93365 _93381 s P f u.
Proof. exact (h1). Qed.
Lemma lem3646962 {_93365 _93381 : Type'} (u : _93365 -> Prop) (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (h1 : term144 _93365 _93381 u t s P f) : term84 _93365 _93381 s P f.
Proof. exact (proj2 (@lem3646960 _93365 _93381 u t s P f h1)). Qed.
Lemma lem3646963 {_93365 _93381 : Type'} (u : _93365 -> Prop) (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (h1 : term144 _93365 _93381 u t s P f) : term110 _93365 _93381 s f u P t.
Proof. exact (proj1 (@lem3646960 _93365 _93381 u t s P f h1)). Qed.
Lemma lem3646965 {_93365 _93381 : Type'} (u : _93365 -> Prop) (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (h1 : term144 _93365 _93381 u t s P f) : term47 _93365 _93381 s t f u.
Proof. exact (proj1 (@lem3646963 _93365 _93381 u t s P f h1)). Qed.
Lemma lem3646968 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (u : _93365 -> Prop) (h1 : term162 _93365 _93381 s P f u) : term45 _93365 _93381 s P f u.
Proof. exact (proj2 (@lem3646961 _93365 _93381 s P f u h1)). Qed.
Lemma lem3646969 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (u : _93365 -> Prop) (h1 : term162 _93365 _93381 s P f u) : term74 _93365 _93381 s f P.
Proof. exact (proj1 (@lem3646961 _93365 _93381 s P f u h1)). Qed.
Lemma lem3646979 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (t : _93365 -> Prop) : (term76 _93365 _93381 s P f t) = (term76 _93365 _93381 s P f t).
Proof. exact (eq_refl (term76 _93365 _93381 s P f t)). Qed.
Lemma lem3646980 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term83 _93365 _93381 s P f) = (term83 _93365 _93381 s P f).
Proof. exact (fun_ext (fun t : _93365 -> Prop => @lem3646979 _93365 _93381 s P f t)). Qed.
Lemma lem3646981 {_93365 : Type'} : (@all (_93365 -> Prop)) = (@all (_93365 -> Prop)).
Proof. exact (eq_refl (@all (_93365 -> Prop))). Qed.
Lemma lem3646983 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term84 _93365 _93381 s P f) = (term84 _93365 _93381 s P f).
Proof. exact (MK_COMB (@lem3646981 _93365) (@lem3646980 _93365 _93381 s P f)). Qed.
Lemma lem3646984 {_93365 _93381 : Type'} (u : _93365 -> Prop) (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (h1 : term144 _93365 _93381 u t s P f) : term84 _93365 _93381 s P f.
Proof. exact (EQ_MP (@lem3646983 _93365 _93381 s P f) (@lem3646962 _93365 _93381 u t s P f h1)). Qed.
Lemma lem3646998 {A : Type'} (P : A -> Prop) (Q : Prop) : (term213 A P Q) = (term214 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3646999 {_93365 : Type'} (P : type686 _93365) (Q : Prop) : (term215 _93365 P Q) = (term216 _93365 P Q).
Proof. exact (@lem3646998 (_93365 -> Prop) P Q). Qed.
Lemma lem3647000 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) (t : _93381 -> Prop) : (term217 _93365 _93381 s f P t) = (term218 _93365 _93381 s f P t).
Proof. exact (@lem3646999 _93365 (term60 _93365 _93381 s t f) (term62 _93381 P t)). Qed.
Lemma lem3647001 {_93365 _93381 : Type'} (s : _93365 -> Prop) (t : _93381 -> Prop) (f : _93365 -> _93381) (u : _93365 -> Prop) : (term219 _93365 _93381 s t f u) = (term52 _93365 _93381 s t f u).
Proof. exact (eq_refl (term219 _93365 _93381 s t f u)). Qed.
Lemma lem3647002 {_93365 _93381 : Type'} (s : _93365 -> Prop) (t : _93381 -> Prop) (f : _93365 -> _93381) : (term220 _93365 _93381 s t f) = (term60 _93365 _93381 s t f).
Proof. exact (fun_ext (fun u : _93365 -> Prop => @lem3647001 _93365 _93381 s t f u)). Qed.
Lemma lem3647003 {_93365 : Type'} : (@all (_93365 -> Prop)) = (@all (_93365 -> Prop)).
Proof. exact (eq_refl (@all (_93365 -> Prop))). Qed.
Lemma lem3647004 {_93365 _93381 : Type'} (s : _93365 -> Prop) (t : _93381 -> Prop) (f : _93365 -> _93381) : (term221 _93365 _93381 s t f) = (term61 _93365 _93381 s t f).
Proof. exact (MK_COMB (@lem3647003 _93365) (@lem3647002 _93365 _93381 s t f)). Qed.
Lemma lem3647005 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3647006 {_93365 _93381 : Type'} (s : _93365 -> Prop) (t : _93381 -> Prop) (f : _93365 -> _93381) : (term222 _93365 _93381 s t f) = (term64 _93365 _93381 s t f).
Proof. exact (MK_COMB (@lem3647005) (@lem3647004 _93365 _93381 s t f)). Qed.
Lemma lem3647007 {_93381 : Type'} (P : type686 _93381) (t : _93381 -> Prop) : (term62 _93381 P t) = (term62 _93381 P t).
Proof. exact (eq_refl (term62 _93381 P t)). Qed.
Lemma lem3647008 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) (t : _93381 -> Prop) : (term217 _93365 _93381 s f P t) = (term66 _93365 _93381 s f P t).
Proof. exact (MK_COMB (@lem3647006 _93365 _93381 s t f) (@lem3647007 _93381 P t)). Qed.
Lemma lem3647009 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3647010 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) (t : _93381 -> Prop) : (term223 _93365 _93381 s f P t) = (term224 _93365 _93381 s f P t).
Proof. exact (MK_COMB (@lem3647009) (@lem3647008 _93365 _93381 s f P t)). Qed.
Lemma lem3647011 {_93365 _93381 : Type'} (s : _93365 -> Prop) (t : _93381 -> Prop) (f : _93365 -> _93381) (u : _93365 -> Prop) : (term219 _93365 _93381 s t f u) = (term52 _93365 _93381 s t f u).
Proof. exact (eq_refl (term219 _93365 _93381 s t f u)). Qed.
Lemma lem3647012 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3647013 {_93365 _93381 : Type'} (s : _93365 -> Prop) (t : _93381 -> Prop) (f : _93365 -> _93381) (u : _93365 -> Prop) : (term225 _93365 _93381 s t f u) = (term226 _93365 _93381 s t f u).
Proof. exact (MK_COMB (@lem3647012) (@lem3647011 _93365 _93381 s t f u)). Qed.
Lemma lem3647014 {_93381 : Type'} (P : type686 _93381) (t : _93381 -> Prop) : (term62 _93381 P t) = (term62 _93381 P t).
Proof. exact (eq_refl (term62 _93381 P t)). Qed.
Lemma lem3647015 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (u : _93365 -> Prop) (P : type686 _93381) (t : _93381 -> Prop) : (term227 _93365 _93381 s f u P t) = (term228 _93365 _93381 s f u P t).
Proof. exact (MK_COMB (@lem3647013 _93365 _93381 s t f u) (@lem3647014 _93381 P t)). Qed.
Lemma lem3647016 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) (t : _93381 -> Prop) : (term229 _93365 _93381 s f P t) = (term230 _93365 _93381 s f P t).
Proof. exact (fun_ext (fun u : _93365 -> Prop => @lem3647015 _93365 _93381 s f u P t)). Qed.
Lemma lem3647017 {_93365 : Type'} : (@all (_93365 -> Prop)) = (@all (_93365 -> Prop)).
Proof. exact (eq_refl (@all (_93365 -> Prop))). Qed.
Lemma lem3647018 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) (t : _93381 -> Prop) : (term218 _93365 _93381 s f P t) = (term231 _93365 _93381 s f P t).
Proof. exact (MK_COMB (@lem3647017 _93365) (@lem3647016 _93365 _93381 s f P t)). Qed.
Lemma lem3647019 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) (t : _93381 -> Prop) : ((term217 _93365 _93381 s f P t) = (term218 _93365 _93381 s f P t)) = ((term66 _93365 _93381 s f P t) = (term231 _93365 _93381 s f P t)).
Proof. exact (MK_COMB (@lem3647010 _93365 _93381 s f P t) (@lem3647018 _93365 _93381 s f P t)). Qed.
Lemma lem3647020 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) (t : _93381 -> Prop) : (term66 _93365 _93381 s f P t) = (term231 _93365 _93381 s f P t).
Proof. exact (EQ_MP (@lem3647019 _93365 _93381 s f P t) (@lem3647000 _93365 _93381 s f P t)). Qed.
Lemma lem3647021 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) : (term73 _93365 _93381 s f P) = (term232 _93365 _93381 s f P).
Proof. exact (fun_ext (fun t : _93381 -> Prop => @lem3647020 _93365 _93381 s f P t)). Qed.
Lemma lem3647022 {_93381 : Type'} : (@all (_93381 -> Prop)) = (@all (_93381 -> Prop)).
Proof. exact (eq_refl (@all (_93381 -> Prop))). Qed.
Lemma lem3647023 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) : (term74 _93365 _93381 s f P) = (term233 _93365 _93381 s f P).
Proof. exact (MK_COMB (@lem3647022 _93381) (@lem3647021 _93365 _93381 s f P)). Qed.
Lemma lem3647036 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (u : _93365 -> Prop) (P : type686 _93381) (t : _93381 -> Prop) : (term228 _93365 _93381 s f u P t) = (term228 _93365 _93381 s f u P t).
Proof. exact (eq_refl (term228 _93365 _93381 s f u P t)). Qed.
Lemma lem3647037 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) (t : _93381 -> Prop) : (term230 _93365 _93381 s f P t) = (term230 _93365 _93381 s f P t).
Proof. exact (fun_ext (fun u : _93365 -> Prop => @lem3647036 _93365 _93381 s f u P t)). Qed.
Lemma lem3647038 {_93365 : Type'} : (@all (_93365 -> Prop)) = (@all (_93365 -> Prop)).
Proof. exact (eq_refl (@all (_93365 -> Prop))). Qed.
Lemma lem3647039 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) (t : _93381 -> Prop) : (term231 _93365 _93381 s f P t) = (term231 _93365 _93381 s f P t).
Proof. exact (MK_COMB (@lem3647038 _93365) (@lem3647037 _93365 _93381 s f P t)). Qed.
Lemma lem3647040 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) : (term232 _93365 _93381 s f P) = (term232 _93365 _93381 s f P).
Proof. exact (fun_ext (fun t : _93381 -> Prop => @lem3647039 _93365 _93381 s f P t)). Qed.
Lemma lem3647041 {_93381 : Type'} : (@all (_93381 -> Prop)) = (@all (_93381 -> Prop)).
Proof. exact (eq_refl (@all (_93381 -> Prop))). Qed.
Lemma lem3647042 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) : (term233 _93365 _93381 s f P) = (term233 _93365 _93381 s f P).
Proof. exact (MK_COMB (@lem3647041 _93381) (@lem3647040 _93365 _93381 s f P)). Qed.
Lemma lem3647043 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) : (term74 _93365 _93381 s f P) = (term233 _93365 _93381 s f P).
Proof. exact (TRANS (@lem3647023 _93365 _93381 s f P) (@lem3647042 _93365 _93381 s f P)). Qed.
Lemma lem3647044 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (u : _93365 -> Prop) (h1 : term162 _93365 _93381 s P f u) : term233 _93365 _93381 s f P.
Proof. exact (EQ_MP (@lem3647043 _93365 _93381 s f P) (@lem3646969 _93365 _93381 s P f u h1)). Qed.
Lemma lem3647053 {_93365 _93381 : Type'} (_40007 : _93365 -> Prop) (u : _93365 -> Prop) (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (h1 : term144 _93365 _93381 u t s P f) : term234 _93365 _93381 s P f _40007.
Proof. exact (@lem3646984 _93365 _93381 u t s P f h1 _40007). Qed.
Lemma lem3647054 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (_40007 : _93365 -> Prop) : (term234 _93365 _93381 s P f _40007) = (term76 _93365 _93381 s P f _40007).
Proof. exact (eq_refl (term234 _93365 _93381 s P f _40007)). Qed.
Lemma lem3647056 {_93365 _93381 : Type'} (_40008 : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (u : _93365 -> Prop) (h1 : term162 _93365 _93381 s P f u) : term235 _93365 _93381 s f P _40008.
Proof. exact (@lem3647044 _93365 _93381 s P f u h1 _40008). Qed.
Lemma lem3647057 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (P : type686 _93381) (_40008 : _93381 -> Prop) : (term235 _93365 _93381 s f P _40008) = (term231 _93365 _93381 s f P _40008).
Proof. exact (eq_refl (term235 _93365 _93381 s f P _40008)). Qed.
Lemma lem3647058 {_93365 _93381 : Type'} (_40008 : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (u : _93365 -> Prop) (h1 : term162 _93365 _93381 s P f u) : term231 _93365 _93381 s f P _40008.
Proof. exact (EQ_MP (@lem3647057 _93365 _93381 s f P _40008) (@lem3647056 _93365 _93381 _40008 s P f u h1)). Qed.
Lemma lem3647059 {_93365 _93381 : Type'} (_40008 : _93381 -> Prop) (_40009 : _93365 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (u : _93365 -> Prop) (h1 : term162 _93365 _93381 s P f u) : term236 _93365 _93381 s f P _40008 _40009.
Proof. exact (@lem3647058 _93365 _93381 _40008 s P f u h1 _40009). Qed.
Lemma lem3647060 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (_40009 : _93365 -> Prop) (P : type686 _93381) (_40008 : _93381 -> Prop) : (term236 _93365 _93381 s f P _40008 _40009) = (term228 _93365 _93381 s f _40009 P _40008).
Proof. exact (eq_refl (term236 _93365 _93381 s f P _40008 _40009)). Qed.
Lemma lem3647061 {_93365 _93381 : Type'} (_40009 : _93365 -> Prop) (_40008 : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (u : _93365 -> Prop) (h1 : term162 _93365 _93381 s P f u) : term228 _93365 _93381 s f _40009 P _40008.
Proof. exact (EQ_MP (@lem3647060 _93365 _93381 s f _40009 P _40008) (@lem3647059 _93365 _93381 _40008 _40009 s P f u h1)). Qed.
Lemma lem3647069 {_93365 _93381 : Type'} (u : _93365 -> Prop) (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (h1 : term144 _93365 _93381 u t s P f) : P t.
Proof. exact (proj2 (@lem3646963 _93365 _93381 u t s P f h1)). Qed.
Lemma lem3647073 {_93365 _93381 : Type'} (u : _93365 -> Prop) (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (h1 : term144 _93365 _93381 u t s P f) : t = (@IMAGE _93365 _93381 f u).
Proof. exact (proj2 (@lem3646965 _93365 _93381 u t s P f h1)). Qed.
Lemma lem3647084 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (_40009 : _93365 -> Prop) (P : type686 _93381) (_40008 : _93381 -> Prop) : (term228 _93365 _93381 s f _40009 P _40008) = (term237 _93365 _93381 s f _40009 P _40008).
Proof. exact (@lem3645961 (term238 _93365 _40009 s) (term239 _93365 _93381 _40008 f _40009) (term62 _93381 P _40008)). Qed.
Lemma lem3647085 {_93365 _93381 : Type'} (_40009 : _93365 -> Prop) (_40008 : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (u : _93365 -> Prop) (h1 : term162 _93365 _93381 s P f u) : term237 _93365 _93381 s f _40009 P _40008.
Proof. exact (EQ_MP (@lem3647084 _93365 _93381 s f _40009 P _40008) (@lem3647061 _93365 _93381 _40009 _40008 s P f u h1)). Qed.
Lemma lem3647117 {_93365 _93381 : Type'} (_40007 : _93365 -> Prop) (u : _93365 -> Prop) (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (h1 : term144 _93365 _93381 u t s P f) : term76 _93365 _93381 s P f _40007.
Proof. exact (EQ_MP (@lem3647054 _93365 _93381 s P f _40007) (@lem3647053 _93365 _93381 _40007 u t s P f h1)). Qed.
Lemma lem3647118 {_93381 : Type'} (P : type686 _93381) : (term240 _93381 P) = (term240 _93381 P).
Proof. exact (eq_refl (term240 _93381 P)). Qed.
Lemma lem3647119 {_93365 _93381 : Type'} (u : _93365 -> Prop) (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (h1 : term144 _93365 _93381 u t s P f) : (term241 _93381 P t) = (term242 _93365 _93381 P f u).
Proof. exact (MK_COMB (@lem3647118 _93381 P) (@lem3647073 _93365 _93381 u t s P f h1)). Qed.
Lemma lem3647120 {_93365 _93381 : Type'} (P : type686 _93381) (f : _93365 -> _93381) (u : _93365 -> Prop) : (term242 _93365 _93381 P f u) = (term77 _93365 _93381 P f u).
Proof. exact (eq_refl (term242 _93365 _93381 P f u)). Qed.
Lemma lem3647121 {_93381 : Type'} (P : type686 _93381) (t : _93381 -> Prop) : (term243 _93381 P t) = (term243 _93381 P t).
Proof. exact (eq_refl (term243 _93381 P t)). Qed.
Lemma lem3647122 {_93365 _93381 : Type'} (t : _93381 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (u : _93365 -> Prop) : ((term241 _93381 P t) = (term242 _93365 _93381 P f u)) = ((term241 _93381 P t) = (term77 _93365 _93381 P f u)).
Proof. exact (MK_COMB (@lem3647121 _93381 P t) (@lem3647120 _93365 _93381 P f u)). Qed.
Lemma lem3647123 {_93381 : Type'} (P : type686 _93381) (t : _93381 -> Prop) : (term241 _93381 P t) = (P t).
Proof. exact (eq_refl (term241 _93381 P t)). Qed.
Lemma lem3647124 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3647125 {_93381 : Type'} (P : type686 _93381) (t : _93381 -> Prop) : (term243 _93381 P t) = (term244 _93381 P t).
Proof. exact (MK_COMB (@lem3647124) (@lem3647123 _93381 P t)). Qed.
Lemma lem3647126 {_93365 _93381 : Type'} (P : type686 _93381) (f : _93365 -> _93381) (u : _93365 -> Prop) : (term77 _93365 _93381 P f u) = (term77 _93365 _93381 P f u).
Proof. exact (eq_refl (term77 _93365 _93381 P f u)). Qed.
Lemma lem3647127 {_93365 _93381 : Type'} (t : _93381 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (u : _93365 -> Prop) : ((term241 _93381 P t) = (term77 _93365 _93381 P f u)) = ((P t) = (term77 _93365 _93381 P f u)).
Proof. exact (MK_COMB (@lem3647125 _93381 P t) (@lem3647126 _93365 _93381 P f u)). Qed.
Lemma lem3647128 {_93365 _93381 : Type'} (t : _93381 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (u : _93365 -> Prop) : ((term241 _93381 P t) = (term242 _93365 _93381 P f u)) = ((P t) = (term77 _93365 _93381 P f u)).
Proof. exact (TRANS (@lem3647122 _93365 _93381 t P f u) (@lem3647127 _93365 _93381 t P f u)). Qed.
Lemma lem3647129 {_93365 _93381 : Type'} (u : _93365 -> Prop) (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (h1 : term144 _93365 _93381 u t s P f) : (P t) = (term77 _93365 _93381 P f u).
Proof. exact (EQ_MP (@lem3647128 _93365 _93381 t P f u) (@lem3647119 _93365 _93381 u t s P f h1)). Qed.
Lemma lem3647146 {_93365 _93381 : Type'} (u : _93365 -> Prop) (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (h1 : term144 _93365 _93381 u t s P f) : @SUBSET _93365 u s.
Proof. exact (proj1 (@lem3646965 _93365 _93381 u t s P f h1)). Qed.
Lemma lem3647147 {_93365 _93381 : Type'} (u : _93365 -> Prop) (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (h1 : term144 _93365 _93381 u t s P f) : term245 _93365 u s.
Proof. exact (fun h0 : term238 _93365 u s => @lem3647146 _93365 _93381 u t s P f h1). Qed.
Lemma lem3647149 (p : Prop) : (term246 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3647150 {_93365 : Type'} (u : _93365 -> Prop) (s : _93365 -> Prop) : (term245 _93365 u s) = (@SUBSET _93365 u s).
Proof. exact (@lem3647149 (@SUBSET _93365 u s)). Qed.
Lemma lem3647151 {_93365 _93381 : Type'} (u : _93365 -> Prop) (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (h1 : term144 _93365 _93381 u t s P f) : @SUBSET _93365 u s.
Proof. exact (EQ_MP (@lem3647150 _93365 u s) (@lem3647147 _93365 _93381 u t s P f h1)). Qed.
Lemma lem3647153 {_93365 _93381 : Type'} (u : _93365 -> Prop) (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (h1 : term144 _93365 _93381 u t s P f) : term77 _93365 _93381 P f u.
Proof. exact (EQ_MP (@lem3647129 _93365 _93381 u t s P f h1) (@lem3647069 _93365 _93381 u t s P f h1)). Qed.
Lemma lem3647154 {_93365 _93381 : Type'} (u : _93365 -> Prop) (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (h1 : term144 _93365 _93381 u t s P f) : term247 _93365 _93381 P f u.
Proof. exact (fun h0 : term248 _93365 _93381 P f u => @lem3647153 _93365 _93381 u t s P f h1). Qed.
Lemma lem3647156 (p : Prop) : (term246 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3647157 {_93365 _93381 : Type'} (P : type686 _93381) (f : _93365 -> _93381) (u : _93365 -> Prop) : (term247 _93365 _93381 P f u) = (term77 _93365 _93381 P f u).
Proof. exact (@lem3647156 (term77 _93365 _93381 P f u)). Qed.
Lemma lem3647158 {_93365 _93381 : Type'} (u : _93365 -> Prop) (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (h1 : term144 _93365 _93381 u t s P f) : term77 _93365 _93381 P f u.
Proof. exact (EQ_MP (@lem3647157 _93365 _93381 P f u) (@lem3647154 _93365 _93381 u t s P f h1)). Qed.
Lemma lem3647160 (a : Prop) (b : Prop) : (term249 a b) = (term250 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3647161 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (_40007 : _93365 -> Prop) : (term76 _93365 _93381 s P f _40007) = (term75 _93365 _93381 s P f _40007).
Proof. exact (@lem3647160 (@SUBSET _93365 _40007 s) (term77 _93365 _93381 P f _40007)). Qed.
Lemma lem3647163 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3647164 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (_40007 : _93365 -> Prop) : (term75 _93365 _93381 s P f _40007) = (term251 _93365 _93381 s P f _40007).
Proof. exact (@lem3647163 (term45 _93365 _93381 s P f _40007)). Qed.
Lemma lem3647165 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (_40007 : _93365 -> Prop) : (term76 _93365 _93381 s P f _40007) = (term251 _93365 _93381 s P f _40007).
Proof. exact (TRANS (@lem3647161 _93365 _93381 s P f _40007) (@lem3647164 _93365 _93381 s P f _40007)). Qed.
Lemma lem3647167 {_93365 _93381 : Type'} (u : _93365 -> Prop) (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (h1 : term144 _93365 _93381 u t s P f) : term45 _93365 _93381 s P f u.
Proof. exact (conj (@lem3647151 _93365 _93381 u t s P f h1) (@lem3647158 _93365 _93381 u t s P f h1)). Qed.
Lemma lem3647169 {_93365 _93381 : Type'} (_40007 : _93365 -> Prop) (u : _93365 -> Prop) (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (h1 : term144 _93365 _93381 u t s P f) : term251 _93365 _93381 s P f _40007.
Proof. exact (EQ_MP (@lem3647165 _93365 _93381 s P f _40007) (@lem3647117 _93365 _93381 _40007 u t s P f h1)). Qed.
Lemma lem3647170 {_93365 _93381 : Type'} (_40007 : _93365 -> Prop) (u : _93365 -> Prop) (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (h1 : term144 _93365 _93381 u t s P f) : term251 _93365 _93381 s P f _40007.
Proof. exact (@lem3647169 _93365 _93381 _40007 u t s P f h1). Qed.
Lemma lem3647171 {_93365 _93381 : Type'} (u : _93365 -> Prop) (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (h1 : term144 _93365 _93381 u t s P f) : term251 _93365 _93381 s P f u.
Proof. exact (@lem3647170 _93365 _93381 u u t s P f h1). Qed.
Lemma lem3647174 {_93365 _93381 : Type'} (u : _93365 -> Prop) (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (h1 : term144 _93365 _93381 u t s P f) : False.
Proof. exact (@lem3647171 _93365 _93381 u t s P f h1 (@lem3647167 _93365 _93381 u t s P f h1)). Qed.
Lemma lem3647175 {_93365 _93381 : Type'} (u : _93365 -> Prop) (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (h1 : term144 _93365 _93381 u t s P f) : term252.
Proof. exact (fun h0 : ~ False => @lem3647174 _93365 _93381 u t s P f h1). Qed.
Lemma lem3647177 (p : Prop) : (term246 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3647178 : term252 = False.
Proof. exact (@lem3647177 False). Qed.
Lemma lem3647233 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (u : _93365 -> Prop) (h1 : term162 _93365 _93381 s P f u) : @SUBSET _93365 u s.
Proof. exact (proj1 (@lem3646968 _93365 _93381 s P f u h1)). Qed.
Lemma lem3647234 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (u : _93365 -> Prop) (h1 : term162 _93365 _93381 s P f u) : term245 _93365 u s.
Proof. exact (fun h0 : term238 _93365 u s => @lem3647233 _93365 _93381 s P f u h1). Qed.
Lemma lem3647236 (p : Prop) : (term246 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3647237 {_93365 : Type'} (u : _93365 -> Prop) (s : _93365 -> Prop) : (term245 _93365 u s) = (@SUBSET _93365 u s).
Proof. exact (@lem3647236 (@SUBSET _93365 u s)). Qed.
Lemma lem3647238 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (u : _93365 -> Prop) (h1 : term162 _93365 _93381 s P f u) : @SUBSET _93365 u s.
Proof. exact (EQ_MP (@lem3647237 _93365 u s) (@lem3647234 _93365 _93381 s P f u h1)). Qed.
Lemma lem3647240 {_93381 : Type'} (x : _93381 -> Prop) : x = x.
Proof. exact (@lem21386 (_93381 -> Prop) x). Qed.
Lemma lem3647241 {_93381 : Type'} (x : _93381 -> Prop) : x = x.
Proof. exact (@lem3647240 _93381 x). Qed.
Lemma lem3647242 {_93365 _93381 : Type'} (f : _93365 -> _93381) (u : _93365 -> Prop) : (@IMAGE _93365 _93381 f u) = (@IMAGE _93365 _93381 f u).
Proof. exact (@lem3647241 _93381 (@IMAGE _93365 _93381 f u)). Qed.
Lemma lem3647243 {_93365 _93381 : Type'} (f : _93365 -> _93381) (u : _93365 -> Prop) : term253 _93365 _93381 f u.
Proof. exact (fun h0 : term254 _93365 _93381 f u => @lem3647242 _93365 _93381 f u). Qed.
Lemma lem3647245 (p : Prop) : (term246 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3647246 {_93365 _93381 : Type'} (f : _93365 -> _93381) (u : _93365 -> Prop) : (term253 _93365 _93381 f u) = ((@IMAGE _93365 _93381 f u) = (@IMAGE _93365 _93381 f u)).
Proof. exact (@lem3647245 ((@IMAGE _93365 _93381 f u) = (@IMAGE _93365 _93381 f u))). Qed.
Lemma lem3647247 {_93365 _93381 : Type'} (f : _93365 -> _93381) (u : _93365 -> Prop) : (@IMAGE _93365 _93381 f u) = (@IMAGE _93365 _93381 f u).
Proof. exact (EQ_MP (@lem3647246 _93365 _93381 f u) (@lem3647243 _93365 _93381 f u)). Qed.
Lemma lem3647249 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (u : _93365 -> Prop) (h1 : term162 _93365 _93381 s P f u) : term77 _93365 _93381 P f u.
Proof. exact (proj2 (@lem3646968 _93365 _93381 s P f u h1)). Qed.
Lemma lem3647250 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (u : _93365 -> Prop) (h1 : term162 _93365 _93381 s P f u) : term247 _93365 _93381 P f u.
Proof. exact (fun h0 : term248 _93365 _93381 P f u => @lem3647249 _93365 _93381 s P f u h1). Qed.
Lemma lem3647252 (p : Prop) : (term246 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3647253 {_93365 _93381 : Type'} (P : type686 _93381) (f : _93365 -> _93381) (u : _93365 -> Prop) : (term247 _93365 _93381 P f u) = (term77 _93365 _93381 P f u).
Proof. exact (@lem3647252 (term77 _93365 _93381 P f u)). Qed.
Lemma lem3647254 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (u : _93365 -> Prop) (h1 : term162 _93365 _93381 s P f u) : term77 _93365 _93381 P f u.
Proof. exact (EQ_MP (@lem3647253 _93365 _93381 P f u) (@lem3647250 _93365 _93381 s P f u h1)). Qed.
Lemma lem3647256 (a : Prop) (b : Prop) : (term249 a b) = (term250 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3647257 {_93365 _93381 : Type'} (f : _93365 -> _93381) (_40009 : _93365 -> Prop) (P : type686 _93381) (_40008 : _93381 -> Prop) : (term255 _93365 _93381 f _40009 P _40008) = (term256 _93365 _93381 f _40009 P _40008).
Proof. exact (@lem3647256 (_40008 = (@IMAGE _93365 _93381 f _40009)) (P _40008)). Qed.
Lemma lem3647258 {_93365 : Type'} (_40009 : _93365 -> Prop) (s : _93365 -> Prop) : (term257 _93365 _40009 s) = (term257 _93365 _40009 s).
Proof. exact (eq_refl (term257 _93365 _40009 s)). Qed.
Lemma lem3647259 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (_40009 : _93365 -> Prop) (P : type686 _93381) (_40008 : _93381 -> Prop) : (term237 _93365 _93381 s f _40009 P _40008) = (term258 _93365 _93381 s f _40009 P _40008).
Proof. exact (MK_COMB (@lem3647258 _93365 _40009 s) (@lem3647257 _93365 _93381 f _40009 P _40008)). Qed.
Lemma lem3647261 (a : Prop) (b : Prop) : (term249 a b) = (term250 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3647262 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (_40009 : _93365 -> Prop) (P : type686 _93381) (_40008 : _93381 -> Prop) : (term258 _93365 _93381 s f _40009 P _40008) = (term259 _93365 _93381 s f _40009 P _40008).
Proof. exact (@lem3647261 (@SUBSET _93365 _40009 s) (term260 _93365 _93381 f _40009 P _40008)). Qed.
Lemma lem3647263 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (_40009 : _93365 -> Prop) (P : type686 _93381) (_40008 : _93381 -> Prop) : (term237 _93365 _93381 s f _40009 P _40008) = (term259 _93365 _93381 s f _40009 P _40008).
Proof. exact (TRANS (@lem3647259 _93365 _93381 s f _40009 P _40008) (@lem3647262 _93365 _93381 s f _40009 P _40008)). Qed.
Lemma lem3647265 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3647266 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (_40009 : _93365 -> Prop) (P : type686 _93381) (_40008 : _93381 -> Prop) : (term259 _93365 _93381 s f _40009 P _40008) = (term261 _93365 _93381 s f _40009 P _40008).
Proof. exact (@lem3647265 (term262 _93365 _93381 s f _40009 P _40008)). Qed.
Lemma lem3647267 {_93365 _93381 : Type'} (s : _93365 -> Prop) (f : _93365 -> _93381) (_40009 : _93365 -> Prop) (P : type686 _93381) (_40008 : _93381 -> Prop) : (term237 _93365 _93381 s f _40009 P _40008) = (term261 _93365 _93381 s f _40009 P _40008).
Proof. exact (TRANS (@lem3647263 _93365 _93381 s f _40009 P _40008) (@lem3647266 _93365 _93381 s f _40009 P _40008)). Qed.
Lemma lem3647269 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (u : _93365 -> Prop) (h1 : term162 _93365 _93381 s P f u) : term263 _93365 _93381 P f u.
Proof. exact (conj (@lem3647247 _93365 _93381 f u) (@lem3647254 _93365 _93381 s P f u h1)). Qed.
Lemma lem3647270 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (u : _93365 -> Prop) (h1 : term162 _93365 _93381 s P f u) : term264 _93365 _93381 s P f u.
Proof. exact (conj (@lem3647238 _93365 _93381 s P f u h1) (@lem3647269 _93365 _93381 s P f u h1)). Qed.
Lemma lem3647272 {_93365 _93381 : Type'} (_40009 : _93365 -> Prop) (_40008 : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (u : _93365 -> Prop) (h1 : term162 _93365 _93381 s P f u) : term261 _93365 _93381 s f _40009 P _40008.
Proof. exact (EQ_MP (@lem3647267 _93365 _93381 s f _40009 P _40008) (@lem3647085 _93365 _93381 _40009 _40008 s P f u h1)). Qed.
Lemma lem3647273 {_93365 _93381 : Type'} (_40009 : _93365 -> Prop) (_40008 : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (u : _93365 -> Prop) (h1 : term162 _93365 _93381 s P f u) : term261 _93365 _93381 s f _40009 P _40008.
Proof. exact (@lem3647272 _93365 _93381 _40009 _40008 s P f u h1). Qed.
Lemma lem3647274 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (u : _93365 -> Prop) (h1 : term162 _93365 _93381 s P f u) : term265 _93365 _93381 s P f u.
Proof. exact (@lem3647273 _93365 _93381 u (@IMAGE _93365 _93381 f u) s P f u h1). Qed.
Lemma lem3647277 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (u : _93365 -> Prop) (h1 : term162 _93365 _93381 s P f u) : False.
Proof. exact (@lem3647274 _93365 _93381 s P f u h1 (@lem3647270 _93365 _93381 s P f u h1)). Qed.
Lemma lem3647278 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (u : _93365 -> Prop) (h1 : term162 _93365 _93381 s P f u) : term252.
Proof. exact (fun h0 : ~ False => @lem3647277 _93365 _93381 s P f u h1). Qed.
Lemma lem3647280 (p : Prop) : (term246 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3647281 : term252 = False.
Proof. exact (@lem3647280 False). Qed.
Lemma lem3647282 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (u : _93365 -> Prop) (h1 : term162 _93365 _93381 s P f u) : False.
Proof. exact (EQ_MP (@lem3647281) (@lem3647278 _93365 _93381 s P f u h1)). Qed.
Lemma lem3647283 {_93365 _93381 : Type'} (u : _93365 -> Prop) (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (h1 : term144 _93365 _93381 u t s P f) : False.
Proof. exact (EQ_MP (@lem3647178) (@lem3647175 _93365 _93381 u t s P f h1)). Qed.
Lemma lem3647284 {_93365 _93381 : Type'} (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (u : _93365 -> Prop) (h1 : term204 _93365 _93381 t s P f u) : False.
Proof. exact (or_elim (@lem3646959 _93365 _93381 t s P f u h1) (fun h0 : term144 _93365 _93381 u t s P f => @lem3647283 _93365 _93381 u t s P f h0) (fun h0 : term162 _93365 _93381 s P f u => @lem3647282 _93365 _93381 s P f u h0)). Qed.
Lemma lem3647285 {_93365 _93381 : Type'} (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (u : _93365 -> Prop) (h1 : term204 _93365 _93381 t s P f u) : (term204 _93365 _93381 t s P f u) = False.
Proof. exact (prop_ext (fun h2 : term204 _93365 _93381 t s P f u => @lem3647284 _93365 _93381 t s P f u h1) (fun h2 : False => @lem3646959 _93365 _93381 t s P f u h1)). Qed.
Lemma lem3647286 {_93365 _93381 : Type'} (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (u : _93365 -> Prop) (h1 : term204 _93365 _93381 t s P f u) : False.
Proof. exact (EQ_MP (@lem3647285 _93365 _93381 t s P f u h1) (@lem3646959 _93365 _93381 t s P f u h1)). Qed.
Lemma lem3647287 {_93365 _93381 : Type'} (t : _93381 -> Prop) (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (h1 : term207 _93365 _93381 t s P f) : False.
Proof. exact (ex_elim (@lem3646853 _93365 _93381 t s P f h1) (fun u : _93365 -> Prop => fun h0 : term206 _93365 _93381 t s P f u => @lem3647286 _93365 _93381 t s P f u h0)). Qed.
Lemma lem3647288 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (h1 : term50 _93365 _93381 s P f) : False.
Proof. exact (ex_elim (@lem3646852 _93365 _93381 s P f h1) (fun t : _93381 -> Prop => fun h0 : term211 _93365 _93381 s P f t => @lem3647287 _93365 _93381 t s P f h0)). Qed.
Lemma lem3647289 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (h1 : term50 _93365 _93381 s P f) : (term50 _93365 _93381 s P f) = False.
Proof. exact (prop_ext (fun h2 : term50 _93365 _93381 s P f => @lem3647288 _93365 _93381 s P f h1) (fun h2 : False => @lem3646313 _93365 _93381 s P f h1)). Qed.
Lemma lem3647290 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) (h1 : term50 _93365 _93381 s P f) : False.
Proof. exact (EQ_MP (@lem3647289 _93365 _93381 s P f h1) (@lem3646313 _93365 _93381 s P f h1)). Qed.
Lemma lem3647291 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : term49 _93365 _93381 s P f.
Proof. exact (fun h0 : term50 _93365 _93381 s P f => @lem3647290 _93365 _93381 s P f h0). Qed.
Lemma lem3647292 {_93365 _93381 : Type'} (s : _93365 -> Prop) (P : type686 _93381) (f : _93365 -> _93381) : (term21 _93365 _93381 s f P) = (term24 _93365 _93381 s P f).
Proof. exact (EQ_MP (@lem3646312 _93365 _93381 s P f) (@lem3647291 _93365 _93381 s P f)). Qed.
Lemma lem3647297 {_93365 _93381 : Type'} (P : type686 _93381) (f : _93365 -> _93381) : term28 _93365 _93381 P f.
Proof. exact (fun s : _93365 -> Prop => @lem3647292 _93365 _93381 s P f). Qed.
Lemma lem3647302 {_93365 _93381 : Type'} (P : type686 _93381) : term32 _93365 _93381 P.
Proof. exact (fun f : _93365 -> _93381 => @lem3647297 _93365 _93381 P f). Qed.
Lemma lem3647307 {_93365 _93381 : Type'} : term36 _93365 _93381.
Proof. exact (fun P : type686 _93381 => @lem3647302 _93365 _93381 P). Qed.
Lemma lem3647308 {_93365 _93381 : Type'} : term38 _93365 _93381.
Proof. exact (EQ_MP (@lem3646308 _93365 _93381) (@lem3647307 _93365 _93381)). Qed.
Lemma lem3647310 {_93365 _93381 : Type'} : term38 _93365 _93381.
Proof. exact (@lem3646070 _93365 _93381 (@lem3647308 _93365 _93381)). Qed.
Lemma lem3647311 {_93365 _93381 : Type'} (h1 : term39 _93365 _93381) : False.
Proof. exact (@lem3647310 _93365 _93381 (@lem3646054 _93365 _93381 h1)). Qed.
Lemma lem3647312 {_93365 _93381 : Type'} (h1 : term39 _93365 _93381) : (term39 _93365 _93381) = False.
Proof. exact (prop_ext (fun h2 : term39 _93365 _93381 => @lem3647311 _93365 _93381 h1) (fun h2 : False => @lem3646054 _93365 _93381 h1)). Qed.
Lemma lem3647313 {_93365 _93381 : Type'} (h1 : term39 _93365 _93381) : False.
Proof. exact (EQ_MP (@lem3647312 _93365 _93381 h1) (@lem3646054 _93365 _93381 h1)). Qed.
Lemma lem3647314 {_93365 _93381 : Type'} : term38 _93365 _93381.
Proof. exact (fun h0 : term39 _93365 _93381 => @lem3647313 _93365 _93381 h0). Qed.
Lemma lem3647315 {_93365 _93381 : Type'} : term36 _93365 _93381.
Proof. exact (EQ_MP (@lem3646053 _93365 _93381) (@lem3647314 _93365 _93381)). Qed.
Lemma lem3647316 {_93365 _93381 : Type'} : term35 _93365 _93381.
Proof. exact (EQ_MP (@lem3646049 _93365 _93381) (@lem3647315 _93365 _93381)). Qed.
