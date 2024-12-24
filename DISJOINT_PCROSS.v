Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DISJOINT_PCROSS_term_abbrevs.
Require Import DISJOINT_spec.
Require Import INTER_PCROSS_spec.
Require Import PCROSS_EQ_EMPTY_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem8057214 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) : term0 _141954 _141955 _141956 s.
Proof. exact (@lem8005884 _141954 _141955 _141956 s). Qed.
Lemma lem8057215 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) : (term0 _141954 _141955 _141956 s) = (term1 _141954 _141955 _141956 s).
Proof. exact (eq_refl (term0 _141954 _141955 _141956 s)). Qed.
Lemma lem8057216 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) : term1 _141954 _141955 _141956 s.
Proof. exact (EQ_MP (@lem8057215 _141954 _141955 _141956 s) (@lem8057214 _141954 _141955 _141956 s)). Qed.
Lemma lem8057217 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : term2 _141954 _141955 _141956 s t.
Proof. exact (@lem8057216 _141954 _141955 _141956 s t). Qed.
Lemma lem8057218 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : (term2 _141954 _141955 _141956 s t) = (((@PCROSS _141954 _141955 _141956 s t) = (@EMPTY (cart _141954 (finite_sum _141955 _141956)))) = (term3 _141954 _141955 _141956 s t)).
Proof. exact (eq_refl (term2 _141954 _141955 _141956 s t)). Qed.
Lemma lem8057220 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) : term4 _142693 _142694 _142695 s.
Proof. exact (@lem8039577 _142693 _142694 _142695 s). Qed.
Lemma lem8057221 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) : (term4 _142693 _142694 _142695 s) = (term5 _142693 _142694 _142695 s).
Proof. exact (eq_refl (term4 _142693 _142694 _142695 s)). Qed.
Lemma lem8057222 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) : term5 _142693 _142694 _142695 s.
Proof. exact (EQ_MP (@lem8057221 _142693 _142694 _142695 s) (@lem8057220 _142693 _142694 _142695 s)). Qed.
Lemma lem8057223 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) (s' : type24 _142693 _142694) : term6 _142693 _142694 _142695 s s'.
Proof. exact (@lem8057222 _142693 _142694 _142695 s s'). Qed.
Lemma lem8057224 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) (s' : type24 _142693 _142694) : (term6 _142693 _142694 _142695 s s') = (term7 _142693 _142694 _142695 s s').
Proof. exact (eq_refl (term6 _142693 _142694 _142695 s s')). Qed.
Lemma lem8057225 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) (s' : type24 _142693 _142694) : term7 _142693 _142694 _142695 s s'.
Proof. exact (EQ_MP (@lem8057224 _142693 _142694 _142695 s s') (@lem8057223 _142693 _142694 _142695 s s')). Qed.
Lemma lem8057226 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) : term8 _142693 _142694 _142695 s s' t.
Proof. exact (@lem8057225 _142693 _142694 _142695 s s' t). Qed.
Lemma lem8057227 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) : (term8 _142693 _142694 _142695 s s' t) = (term9 _142693 _142694 _142695 s s' t).
Proof. exact (eq_refl (term8 _142693 _142694 _142695 s s' t)). Qed.
Lemma lem8057228 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) : term9 _142693 _142694 _142695 s s' t.
Proof. exact (EQ_MP (@lem8057227 _142693 _142694 _142695 s s' t) (@lem8057226 _142693 _142694 _142695 s s' t)). Qed.
Lemma lem8057229 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (t' : type24 _142693 _142695) : term10 _142693 _142694 _142695 s s' t t'.
Proof. exact (@lem8057228 _142693 _142694 _142695 s s' t t'). Qed.
Lemma lem8057230 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (t' : type24 _142693 _142695) : (term10 _142693 _142694 _142695 s s' t t') = ((term11 _142693 _142694 _142695 s t s' t') = (term12 _142693 _142694 _142695 s s' t t')).
Proof. exact (eq_refl (term10 _142693 _142694 _142695 s s' t t')). Qed.
Lemma lem8057232 {A : Type'} (s : A -> Prop) : term13 A s.
Proof. exact (@lem3196110 A s). Qed.
Lemma lem8057233 {A : Type'} (s : A -> Prop) : (term13 A s) = (term14 A s).
Proof. exact (eq_refl (term13 A s)). Qed.
Lemma lem8057234 {A : Type'} (s : A -> Prop) : term14 A s.
Proof. exact (EQ_MP (@lem8057233 A s) (@lem8057232 A s)). Qed.
Lemma lem8057235 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term15 A s t.
Proof. exact (@lem8057234 A s t). Qed.
Lemma lem8057236 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term15 A s t) = ((@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A))).
Proof. exact (eq_refl (term15 A s t)). Qed.
Lemma lem8057257 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (EQ_MP (@lem8057236 A s t) (@lem8057235 A s t)). Qed.
Lemma lem8057258 {A M N : Type'} (s : type16 A M N) (t : type16 A M N) : (@DISJOINT (cart A (finite_sum M N)) s t) = ((@INTER (cart A (finite_sum M N)) s t) = (@EMPTY (cart A (finite_sum M N)))).
Proof. exact (@lem8057257 (type2 A M N) s t). Qed.
Lemma lem8057259 {A M N : Type'} (s : type24 A M) (t : type24 A N) (s' : type24 A M) (t' : type24 A N) : (term16 A M N s t s' t') = ((term11 A M N s t s' t') = (@EMPTY (cart A (finite_sum M N)))).
Proof. exact (@lem8057258 A M N (@PCROSS A M N s t) (@PCROSS A M N s' t')). Qed.
Lemma lem8057263 {_142693 _142694 _142695 : Type'} (s : type24 _142693 _142694) (s' : type24 _142693 _142694) (t : type24 _142693 _142695) (t' : type24 _142693 _142695) : (term11 _142693 _142694 _142695 s t s' t') = (term12 _142693 _142694 _142695 s s' t t').
Proof. exact (EQ_MP (@lem8057230 _142693 _142694 _142695 s s' t t') (@lem8057229 _142693 _142694 _142695 s s' t t')). Qed.
Lemma lem8057264 {A M N : Type'} (s : type24 A M) (s' : type24 A M) (t : type24 A N) (t' : type24 A N) : (term11 A M N s t s' t') = (term12 A M N s s' t t').
Proof. exact (@lem8057263 A M N s s' t t'). Qed.
Lemma lem8057265 {A M N : Type'} : (@eq ((cart A (finite_sum M N)) -> Prop)) = (@eq ((cart A (finite_sum M N)) -> Prop)).
Proof. exact (eq_refl (@eq ((cart A (finite_sum M N)) -> Prop))). Qed.
Lemma lem8057266 {A M N : Type'} (s : type24 A M) (s' : type24 A M) (t : type24 A N) (t' : type24 A N) : (term17 A M N s t s' t') = (term18 A M N s s' t t').
Proof. exact (MK_COMB (@lem8057265 A M N) (@lem8057264 A M N s s' t t')). Qed.
Lemma lem8057267 {A M N : Type'} : (@EMPTY (cart A (finite_sum M N))) = (@EMPTY (cart A (finite_sum M N))).
Proof. exact (eq_refl (@EMPTY (cart A (finite_sum M N)))). Qed.
Lemma lem8057268 {A M N : Type'} (s : type24 A M) (s' : type24 A M) (t : type24 A N) (t' : type24 A N) : ((term11 A M N s t s' t') = (@EMPTY (cart A (finite_sum M N)))) = ((term12 A M N s s' t t') = (@EMPTY (cart A (finite_sum M N)))).
Proof. exact (MK_COMB (@lem8057266 A M N s s' t t') (@lem8057267 A M N)). Qed.
Lemma lem8057270 {_141954 _141955 _141956 : Type'} (s : type24 _141954 _141955) (t : type24 _141954 _141956) : ((@PCROSS _141954 _141955 _141956 s t) = (@EMPTY (cart _141954 (finite_sum _141955 _141956)))) = (term3 _141954 _141955 _141956 s t).
Proof. exact (EQ_MP (@lem8057218 _141954 _141955 _141956 s t) (@lem8057217 _141954 _141955 _141956 s t)). Qed.
Lemma lem8057271 {A M N : Type'} (s : type24 A M) (t : type24 A N) : ((@PCROSS A M N s t) = (@EMPTY (cart A (finite_sum M N)))) = (term3 A M N s t).
Proof. exact (@lem8057270 A M N s t). Qed.
Lemma lem8057272 {A M N : Type'} (s : type24 A M) (s' : type24 A M) (t : type24 A N) (t' : type24 A N) : ((term12 A M N s s' t t') = (@EMPTY (cart A (finite_sum M N)))) = (term19 A M N s s' t t').
Proof. exact (@lem8057271 A M N (@INTER (cart A M) s s') (@INTER (cart A N) t t')). Qed.
Lemma lem8057279 {A M N : Type'} (s : type24 A M) (s' : type24 A M) (t : type24 A N) (t' : type24 A N) : ((term11 A M N s t s' t') = (@EMPTY (cart A (finite_sum M N)))) = (term19 A M N s s' t t').
Proof. exact (TRANS (@lem8057268 A M N s s' t t') (@lem8057272 A M N s s' t t')). Qed.
Lemma lem8057280 {A M N : Type'} (s : type24 A M) (s' : type24 A M) (t : type24 A N) (t' : type24 A N) : (term16 A M N s t s' t') = (term19 A M N s s' t t').
Proof. exact (TRANS (@lem8057259 A M N s t s' t') (@lem8057279 A M N s s' t t')). Qed.
Lemma lem8057281 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8057282 {A M N : Type'} (s : type24 A M) (s' : type24 A M) (t : type24 A N) (t' : type24 A N) : (term20 A M N s t s' t') = (term21 A M N s s' t t').
Proof. exact (MK_COMB (@lem8057281) (@lem8057280 A M N s s' t t')). Qed.
Lemma lem8057286 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (EQ_MP (@lem8057236 A s t) (@lem8057235 A s t)). Qed.
Lemma lem8057287 {A M : Type'} (s : type24 A M) (t : type24 A M) : (@DISJOINT (cart A M) s t) = ((@INTER (cart A M) s t) = (@EMPTY (cart A M))).
Proof. exact (@lem8057286 (cart A M) s t). Qed.
Lemma lem8057288 {A M : Type'} (s : type24 A M) (s' : type24 A M) : (@DISJOINT (cart A M) s s') = ((@INTER (cart A M) s s') = (@EMPTY (cart A M))).
Proof. exact (@lem8057287 A M s s'). Qed.
Lemma lem8057291 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8057292 {A M : Type'} (s : type24 A M) (s' : type24 A M) : (term22 A M s s') = (term23 A M s s').
Proof. exact (MK_COMB (@lem8057291) (@lem8057288 A M s s')). Qed.
Lemma lem8057294 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (EQ_MP (@lem8057236 A s t) (@lem8057235 A s t)). Qed.
Lemma lem8057295 {A N : Type'} (s : type24 A N) (t : type24 A N) : (@DISJOINT (cart A N) s t) = ((@INTER (cart A N) s t) = (@EMPTY (cart A N))).
Proof. exact (@lem8057294 (cart A N) s t). Qed.
Lemma lem8057296 {A N : Type'} (t : type24 A N) (t' : type24 A N) : (@DISJOINT (cart A N) t t') = ((@INTER (cart A N) t t') = (@EMPTY (cart A N))).
Proof. exact (@lem8057295 A N t t'). Qed.
Lemma lem8057299 {A M N : Type'} (s : type24 A M) (s' : type24 A M) (t : type24 A N) (t' : type24 A N) : (term24 A M N s s' t t') = (term19 A M N s s' t t').
Proof. exact (MK_COMB (@lem8057292 A M s s') (@lem8057296 A N t t')). Qed.
Lemma lem8057302 {A M N : Type'} (s : type24 A M) (s' : type24 A M) (t : type24 A N) (t' : type24 A N) : ((term16 A M N s t s' t') = (term24 A M N s s' t t')) = ((term19 A M N s s' t t') = (term19 A M N s s' t t')).
Proof. exact (MK_COMB (@lem8057282 A M N s s' t t') (@lem8057299 A M N s s' t t')). Qed.
Lemma lem8057304 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem8057305 (x : Prop) : (x = x) = True.
Proof. exact (@lem8057304 Prop x). Qed.
Lemma lem8057306 {A M N : Type'} (s : type24 A M) (s' : type24 A M) (t : type24 A N) (t' : type24 A N) : ((term19 A M N s s' t t') = (term19 A M N s s' t t')) = True.
Proof. exact (@lem8057305 (term19 A M N s s' t t')). Qed.
Lemma lem8057307 {A M N : Type'} (s : type24 A M) (s' : type24 A M) (t : type24 A N) (t' : type24 A N) : ((term16 A M N s t s' t') = (term24 A M N s s' t t')) = True.
Proof. exact (TRANS (@lem8057302 A M N s s' t t') (@lem8057306 A M N s s' t t')). Qed.
Lemma lem8057308 {A M N : Type'} (s : type24 A M) (s' : type24 A M) (t : type24 A N) : (term25 A M N s s' t) = (term26 A N).
Proof. exact (fun_ext (fun t' : type24 A N => @lem8057307 A M N s s' t t')). Qed.
Lemma lem8057309 {A N : Type'} : (@all ((cart A N) -> Prop)) = (@all ((cart A N) -> Prop)).
Proof. exact (eq_refl (@all ((cart A N) -> Prop))). Qed.
Lemma lem8057310 {A M N : Type'} (s : type24 A M) (s' : type24 A M) (t : type24 A N) : (term27 A M N s s' t) = (term28 A N).
Proof. exact (MK_COMB (@lem8057309 A N) (@lem8057308 A M N s s' t)). Qed.
Lemma lem8057312 {A : Type'} (t : Prop) : (term29 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8057313 {A N : Type'} (t : Prop) : (term30 A N t) = t.
Proof. exact (@lem8057312 (type24 A N) t). Qed.
Lemma lem8057314 {A N : Type'} : (term28 A N) = True.
Proof. exact (@lem8057313 A N True). Qed.
Lemma lem8057315 {A M N : Type'} (s : type24 A M) (s' : type24 A M) (t : type24 A N) : (term27 A M N s s' t) = True.
Proof. exact (TRANS (@lem8057310 A M N s s' t) (@lem8057314 A N)). Qed.
Lemma lem8057316 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term31 A M N s t) = (term26 A M).
Proof. exact (fun_ext (fun s' : type24 A M => @lem8057315 A M N s s' t)). Qed.
Lemma lem8057317 {A M : Type'} : (@all ((cart A M) -> Prop)) = (@all ((cart A M) -> Prop)).
Proof. exact (eq_refl (@all ((cart A M) -> Prop))). Qed.
Lemma lem8057318 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term32 A M N s t) = (term28 A M).
Proof. exact (MK_COMB (@lem8057317 A M) (@lem8057316 A M N s t)). Qed.
Lemma lem8057320 {A : Type'} (t : Prop) : (term29 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8057321 {A M : Type'} (t : Prop) : (term30 A M t) = t.
Proof. exact (@lem8057320 (type24 A M) t). Qed.
Lemma lem8057322 {A M : Type'} : (term28 A M) = True.
Proof. exact (@lem8057321 A M True). Qed.
Lemma lem8057323 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term32 A M N s t) = True.
Proof. exact (TRANS (@lem8057318 A M N s t) (@lem8057322 A M)). Qed.
Lemma lem8057324 {A M N : Type'} (s : type24 A M) : (term33 A M N s) = (term26 A N).
Proof. exact (fun_ext (fun t : type24 A N => @lem8057323 A M N s t)). Qed.
Lemma lem8057325 {A N : Type'} : (@all ((cart A N) -> Prop)) = (@all ((cart A N) -> Prop)).
Proof. exact (eq_refl (@all ((cart A N) -> Prop))). Qed.
Lemma lem8057326 {A M N : Type'} (s : type24 A M) : (term34 A M N s) = (term28 A N).
Proof. exact (MK_COMB (@lem8057325 A N) (@lem8057324 A M N s)). Qed.
Lemma lem8057328 {A : Type'} (t : Prop) : (term29 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8057329 {A N : Type'} (t : Prop) : (term30 A N t) = t.
Proof. exact (@lem8057328 (type24 A N) t). Qed.
Lemma lem8057330 {A N : Type'} : (term28 A N) = True.
Proof. exact (@lem8057329 A N True). Qed.
Lemma lem8057331 {A M N : Type'} (s : type24 A M) : (term34 A M N s) = True.
Proof. exact (TRANS (@lem8057326 A M N s) (@lem8057330 A N)). Qed.
Lemma lem8057332 {A M N : Type'} : (term35 A M N) = (term26 A M).
Proof. exact (fun_ext (fun s : type24 A M => @lem8057331 A M N s)). Qed.
Lemma lem8057333 {A M : Type'} : (@all ((cart A M) -> Prop)) = (@all ((cart A M) -> Prop)).
Proof. exact (eq_refl (@all ((cart A M) -> Prop))). Qed.
Lemma lem8057334 {A M N : Type'} : (term36 A M N) = (term28 A M).
Proof. exact (MK_COMB (@lem8057333 A M) (@lem8057332 A M N)). Qed.
Lemma lem8057336 {A : Type'} (t : Prop) : (term29 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8057337 {A M : Type'} (t : Prop) : (term30 A M t) = t.
Proof. exact (@lem8057336 (type24 A M) t). Qed.
Lemma lem8057338 {A M : Type'} : (term28 A M) = True.
Proof. exact (@lem8057337 A M True). Qed.
Lemma lem8057339 {A M N : Type'} : (term36 A M N) = True.
Proof. exact (TRANS (@lem8057334 A M N) (@lem8057338 A M)). Qed.
Lemma lem8057340 {A M N : Type'} : True = (term36 A M N).
Proof. exact (SYM (@lem8057339 A M N)). Qed.
Lemma lem8057341 {A M N : Type'} : term36 A M N.
Proof. exact (EQ_MP (@lem8057340 A M N) (@lem0)). Qed.
