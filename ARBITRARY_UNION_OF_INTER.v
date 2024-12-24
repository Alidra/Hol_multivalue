Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ARBITRARY_UNION_OF_INTER_term_abbrevs.
Require Import ARBITRARY_UNION_OF_INC_spec.
Require Import ARBITRARY_UNION_OF_INTER_EQ_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem4871096 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4871097 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem4871098 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem4871097 t1) (@lem4871096 t1)). Qed.
Lemma lem4871099 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem4871098 t1 t2). Qed.
Lemma lem4871100 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem4871101 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem4871100 t1 t2) (@lem4871099 t1 t2)). Qed.
Lemma lem4871102 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem4871101 t1 t2 t3). Qed.
Lemma lem4871103 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem4871104 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem4871103 t1 t2 t3) (@lem4871102 t1 t2 t3)). Qed.
Lemma lem4871105 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem4871104 t1 t2 t3)). Qed.
Lemma lem4871106 {A : Type'} (P : type686 A) : term7 A P.
Proof. exact (@lem4871095 A P). Qed.
Lemma lem4871107 {A : Type'} (P : type686 A) : (term7 A P) = ((term8 A P) = (term9 A P)).
Proof. exact (eq_refl (term7 A P)). Qed.
Lemma lem4871128 {A : Type'} (P : type686 A) : (term8 A P) = (term9 A P).
Proof. exact (EQ_MP (@lem4871107 A P) (@lem4871106 A P)). Qed.
Lemma lem4871129 {A : Type'} (P : type686 A) : (term8 A P) = (term9 A P).
Proof. exact (@lem4871128 A P). Qed.
Lemma lem4871142 {A : Type'} (P : type686 A) : (term10 A P) = (term10 A P).
Proof. exact (eq_refl (term10 A P)). Qed.
Lemma lem4871143 {A : Type'} (P : type686 A) : (term11 A P) = (term12 A P).
Proof. exact (MK_COMB (@lem4871142 A P) (@lem4871129 A P)). Qed.
Lemma lem4871146 {A : Type'} : (term13 A) = (term14 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4871143 A P)). Qed.
Lemma lem4871147 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4871148 {A : Type'} : (term15 A) = (term16 A).
Proof. exact (MK_COMB (@lem4871147 A) (@lem4871146 A)). Qed.
Lemma lem4871153 {A : Type'} : (term16 A) = (term15 A).
Proof. exact (SYM (@lem4871148 A)). Qed.
Lemma lem4871155 (p : Prop) : p = (term17 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4871156 {A : Type'} : (term16 A) = (term18 A).
Proof. exact (@lem4871155 (term16 A)). Qed.
Lemma lem4871157 {A : Type'} : (term18 A) = (term16 A).
Proof. exact (SYM (@lem4871156 A)). Qed.
Lemma lem4871158 {A : Type'} (h1 : term19 A) : term19 A.
Proof. exact (h1). Qed.
Lemma lem4871159 {A : Type'} : term20 A.
Proof. exact (@lem4858424 A). Qed.
Lemma lem4871163 {A : Type'} (h1 : term21 A) : term21 A.
Proof. exact (h1). Qed.
Lemma lem4871164 {A : Type'} : term22 A.
Proof. exact (fun h0 : term21 A => @lem4871163 A h0). Qed.
Lemma lem4871165 {A : Type'} (h1 : term22 A) : term22 A.
Proof. exact (h1). Qed.
Lemma lem4871166 {A : Type'} (h1 : term21 A) : term21 A.
Proof. exact (h1). Qed.
Lemma lem4871167 {A : Type'} (h1 : term21 A) (h2 : term22 A) : term21 A.
Proof. exact (@lem4871165 A h2 (@lem4871166 A h1)). Qed.
Lemma lem4871168 {A : Type'} (h1 : term21 A) : term23 A.
Proof. exact (fun h0 : term22 A => @lem4871167 A h1 h0). Qed.
Lemma lem4871169 {A : Type'} (h1 : term22 A) : term22 A.
Proof. exact (h1). Qed.
Lemma lem4871170 {A : Type'} (h1 : term21 A) (h2 : term22 A) : term21 A.
Proof. exact (@lem4871168 A h1 (@lem4871169 A h2)). Qed.
Lemma lem4871171 {A : Type'} (h1 : term22 A) : term22 A.
Proof. exact (fun h0 : term21 A => @lem4871170 A h0 h1). Qed.
Lemma lem4871172 {A : Type'} : term24 A.
Proof. exact (fun h0 : term22 A => @lem4871171 A h0). Qed.
Lemma lem4871175 {A : Type'} : term22 A.
Proof. exact (@lem4871172 A (@lem4871164 A)). Qed.
Lemma lem4871176 {A : Type'} : term22 A.
Proof. exact (@lem4871175 A). Qed.
Lemma lem4871210 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4871211 {A : Type'} : (term25 A) = (term26 A).
Proof. exact (@lem4871210 (term20 A)). Qed.
Lemma lem4871222 {A : Type'} : (term27 A) = (term27 A).
Proof. exact (eq_refl (term27 A)). Qed.
Lemma lem4871229 {A : Type'} : (term21 A) = (term28 A).
Proof. exact (MK_COMB (@lem4871222 A) (@lem4871211 A)). Qed.
Lemma lem4871234 {A : Type'} (P : type686 A) (s : A -> Prop) : (term29 A P s) = (term29 A P s).
Proof. exact (eq_refl (term29 A P s)). Qed.
Lemma lem4871235 {A : Type'} (P : type686 A) : (term30 A P) = (term30 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4871234 A P s)). Qed.
Lemma lem4871236 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4871237 {A : Type'} (P : type686 A) : (term31 A P) = (term31 A P).
Proof. exact (MK_COMB (@lem4871236 A) (@lem4871235 A P)). Qed.
Lemma lem4871238 {A : Type'} : (term32 A) = (term32 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4871237 A P)). Qed.
Lemma lem4871239 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4871240 {A : Type'} : (term20 A) = (term20 A).
Proof. exact (MK_COMB (@lem4871239 A) (@lem4871238 A)). Qed.
Lemma lem4871241 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4871242 {A : Type'} : (term26 A) = (term26 A).
Proof. exact (MK_COMB (@lem4871241) (@lem4871240 A)). Qed.
Lemma lem4871251 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term33 A P s t) = (term33 A P s t).
Proof. exact (eq_refl (term33 A P s t)). Qed.
Lemma lem4871252 {A : Type'} (P : type686 A) (s : A -> Prop) : (term34 A P s) = (term34 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4871251 A P s t)). Qed.
Lemma lem4871253 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4871254 {A : Type'} (P : type686 A) (s : A -> Prop) : (term35 A P s) = (term35 A P s).
Proof. exact (MK_COMB (@lem4871253 A) (@lem4871252 A P s)). Qed.
Lemma lem4871255 {A : Type'} (P : type686 A) : (term36 A P) = (term36 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4871254 A P s)). Qed.
Lemma lem4871256 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4871257 {A : Type'} (P : type686 A) : (term9 A P) = (term9 A P).
Proof. exact (MK_COMB (@lem4871256 A) (@lem4871255 A P)). Qed.
Lemma lem4871266 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term37 A P s t) = (term37 A P s t).
Proof. exact (eq_refl (term37 A P s t)). Qed.
Lemma lem4871267 {A : Type'} (P : type686 A) (s : A -> Prop) : (term38 A P s) = (term38 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4871266 A P s t)). Qed.
Lemma lem4871268 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4871269 {A : Type'} (P : type686 A) (s : A -> Prop) : (term39 A P s) = (term39 A P s).
Proof. exact (MK_COMB (@lem4871268 A) (@lem4871267 A P s)). Qed.
Lemma lem4871270 {A : Type'} (P : type686 A) : (term40 A P) = (term40 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4871269 A P s)). Qed.
Lemma lem4871271 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4871272 {A : Type'} (P : type686 A) : (term41 A P) = (term41 A P).
Proof. exact (MK_COMB (@lem4871271 A) (@lem4871270 A P)). Qed.
Lemma lem4871273 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4871274 {A : Type'} (P : type686 A) : (term10 A P) = (term10 A P).
Proof. exact (MK_COMB (@lem4871273) (@lem4871272 A P)). Qed.
Lemma lem4871275 {A : Type'} (P : type686 A) : (term12 A P) = (term12 A P).
Proof. exact (MK_COMB (@lem4871274 A P) (@lem4871257 A P)). Qed.
Lemma lem4871276 {A : Type'} : (term14 A) = (term14 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4871275 A P)). Qed.
Lemma lem4871277 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4871278 {A : Type'} : (term16 A) = (term16 A).
Proof. exact (MK_COMB (@lem4871277 A) (@lem4871276 A)). Qed.
Lemma lem4871279 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4871280 {A : Type'} : (term19 A) = (term19 A).
Proof. exact (MK_COMB (@lem4871279) (@lem4871278 A)). Qed.
Lemma lem4871281 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4871282 {A : Type'} : (term27 A) = (term27 A).
Proof. exact (MK_COMB (@lem4871281) (@lem4871280 A)). Qed.
Lemma lem4871283 {A : Type'} : (term28 A) = (term28 A).
Proof. exact (MK_COMB (@lem4871282 A) (@lem4871242 A)). Qed.
Lemma lem4871342 {A : Type'} : (term21 A) = (term28 A).
Proof. exact (TRANS (@lem4871229 A) (@lem4871283 A)). Qed.
Lemma lem4871343 {A : Type'} : (term28 A) = (term21 A).
Proof. exact (SYM (@lem4871342 A)). Qed.
Lemma lem4871344 {A : Type'} (h1 : term19 A) : term19 A.
Proof. exact (h1). Qed.
Lemma lem4871345 {A : Type'} (h1 : term20 A) : term20 A.
Proof. exact (h1). Qed.
Lemma lem4871352 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term42 A s P t) = (term43 A s P t).
Proof. exact (@lem17045 (P s) (P t)). Qed.
Lemma lem4871353 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term44 A P s t) = (term44 A P s t).
Proof. exact (eq_refl (term44 A P s t)). Qed.
Lemma lem4871354 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4871355 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term45 A s P t) = (term46 A s P t).
Proof. exact (MK_COMB (@lem4871354) (@lem4871352 A s P t)). Qed.
Lemma lem4871356 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term47 A P s t) = (term48 A P s t).
Proof. exact (MK_COMB (@lem4871355 A s P t) (@lem4871353 A P s t)). Qed.
Lemma lem4871357 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term37 A P s t) = (term47 A P s t).
Proof. exact (@lem17265 (term49 A s P t) (term44 A P s t)). Qed.
Lemma lem4871358 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term37 A P s t) = (term48 A P s t).
Proof. exact (TRANS (@lem4871357 A P s t) (@lem4871356 A P s t)). Qed.
Lemma lem4871359 {A : Type'} (P : type686 A) (s : A -> Prop) : (term38 A P s) = (term50 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4871358 A P s t)). Qed.
Lemma lem4871360 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4871361 {A : Type'} (P : type686 A) (s : A -> Prop) : (term39 A P s) = (term51 A P s).
Proof. exact (MK_COMB (@lem4871360 A) (@lem4871359 A P s)). Qed.
Lemma lem4871362 {A : Type'} (P : type686 A) : (term40 A P) = (term52 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4871361 A P s)). Qed.
Lemma lem4871363 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4871364 {A : Type'} (P : type686 A) : (term41 A P) = (term53 A P).
Proof. exact (MK_COMB (@lem4871363 A) (@lem4871362 A P)). Qed.
Lemma lem4871375 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term54 A P s t) = (term55 A P s t).
Proof. exact (@lem17362 (term49 A s P t) (term56 A P s t)). Qed.
Lemma lem4871376 {A : Type'} (P : type686 A) : (term57 A P) = (term58 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem4871377 {A : Type'} (P : type686 A) (s : A -> Prop) : (term59 A P s) = (term60 A P s).
Proof. exact (@lem4871376 A (term34 A P s)). Qed.
Lemma lem4871378 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term61 A P s t) = (term33 A P s t).
Proof. exact (eq_refl (term61 A P s t)). Qed.
Lemma lem4871379 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4871380 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term62 A P s t) = (term54 A P s t).
Proof. exact (MK_COMB (@lem4871379) (@lem4871378 A P s t)). Qed.
Lemma lem4871381 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term62 A P s t) = (term55 A P s t).
Proof. exact (TRANS (@lem4871380 A P s t) (@lem4871375 A P s t)). Qed.
Lemma lem4871382 {A : Type'} (P : type686 A) (s : A -> Prop) : (term63 A P s) = (term64 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4871381 A P s t)). Qed.
Lemma lem4871383 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4871384 {A : Type'} (P : type686 A) (s : A -> Prop) : (term60 A P s) = (term65 A P s).
Proof. exact (MK_COMB (@lem4871383 A) (@lem4871382 A P s)). Qed.
Lemma lem4871385 {A : Type'} (P : type686 A) (s : A -> Prop) : (term59 A P s) = (term65 A P s).
Proof. exact (TRANS (@lem4871377 A P s) (@lem4871384 A P s)). Qed.
Lemma lem4871386 {A : Type'} (P : type686 A) : (term57 A P) = (term58 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem4871387 {A : Type'} (P : type686 A) : (term66 A P) = (term67 A P).
Proof. exact (@lem4871386 A (term36 A P)). Qed.
Lemma lem4871388 {A : Type'} (P : type686 A) (s : A -> Prop) : (term68 A P s) = (term35 A P s).
Proof. exact (eq_refl (term68 A P s)). Qed.
Lemma lem4871389 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4871390 {A : Type'} (P : type686 A) (s : A -> Prop) : (term69 A P s) = (term59 A P s).
Proof. exact (MK_COMB (@lem4871389) (@lem4871388 A P s)). Qed.
Lemma lem4871391 {A : Type'} (P : type686 A) (s : A -> Prop) : (term69 A P s) = (term65 A P s).
Proof. exact (TRANS (@lem4871390 A P s) (@lem4871385 A P s)). Qed.
Lemma lem4871392 {A : Type'} (P : type686 A) : (term70 A P) = (term71 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4871391 A P s)). Qed.
Lemma lem4871393 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4871394 {A : Type'} (P : type686 A) : (term67 A P) = (term72 A P).
Proof. exact (MK_COMB (@lem4871393 A) (@lem4871392 A P)). Qed.
Lemma lem4871395 {A : Type'} (P : type686 A) : (term66 A P) = (term72 A P).
Proof. exact (TRANS (@lem4871387 A P) (@lem4871394 A P)). Qed.
Lemma lem4871396 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4871397 {A : Type'} (P : type686 A) : (term73 A P) = (term74 A P).
Proof. exact (MK_COMB (@lem4871396) (@lem4871364 A P)). Qed.
Lemma lem4871398 {A : Type'} (P : type686 A) : (term75 A P) = (term76 A P).
Proof. exact (MK_COMB (@lem4871397 A P) (@lem4871395 A P)). Qed.
Lemma lem4871399 {A : Type'} (P : type686 A) : (term77 A P) = (term75 A P).
Proof. exact (@lem17362 (term41 A P) (term9 A P)). Qed.
Lemma lem4871400 {A : Type'} (P : type686 A) : (term77 A P) = (term76 A P).
Proof. exact (TRANS (@lem4871399 A P) (@lem4871398 A P)). Qed.
Lemma lem4871401 {A : Type'} (P : type180 A) : (term78 A P) = (term79 A P).
Proof. exact (@lem18392 (type686 A) P). Qed.
Lemma lem4871402 {A : Type'} : (term19 A) = (term80 A).
Proof. exact (@lem4871401 A (term14 A)). Qed.
Lemma lem4871403 {A : Type'} (P : type686 A) : (term81 A P) = (term12 A P).
Proof. exact (eq_refl (term81 A P)). Qed.
Lemma lem4871404 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4871405 {A : Type'} (P : type686 A) : (term82 A P) = (term77 A P).
Proof. exact (MK_COMB (@lem4871404) (@lem4871403 A P)). Qed.
Lemma lem4871406 {A : Type'} (P : type686 A) : (term82 A P) = (term76 A P).
Proof. exact (TRANS (@lem4871405 A P) (@lem4871400 A P)). Qed.
Lemma lem4871407 {A : Type'} : (term83 A) = (term84 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4871406 A P)). Qed.
Lemma lem4871408 {A : Type'} : (@ex ((A -> Prop) -> Prop)) = (@ex ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> Prop))). Qed.
Lemma lem4871409 {A : Type'} : (term80 A) = (term85 A).
Proof. exact (MK_COMB (@lem4871408 A) (@lem4871407 A)). Qed.
Lemma lem4871410 {A : Type'} : (term19 A) = (term85 A).
Proof. exact (TRANS (@lem4871402 A) (@lem4871409 A)). Qed.
Lemma lem4871565 {A : Type'} (P : Prop) (Q : A -> Prop) : (term86 A P Q) = (term87 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4871566 {A : Type'} (P : Prop) (Q : type686 A) : (term88 A P Q) = (term89 A P Q).
Proof. exact (@lem4871565 (A -> Prop) P Q). Qed.
Lemma lem4871567 {A : Type'} (P : type686 A) : (term90 A P) = (term91 A P).
Proof. exact (@lem4871566 A (term53 A P) (term71 A P)). Qed.
Lemma lem4871568 {A : Type'} (P : type686 A) (s : A -> Prop) : (term92 A P s) = (term65 A P s).
Proof. exact (eq_refl (term92 A P s)). Qed.
Lemma lem4871569 {A : Type'} (P : type686 A) : (term93 A P) = (term71 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4871568 A P s)). Qed.
Lemma lem4871570 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4871571 {A : Type'} (P : type686 A) : (term94 A P) = (term72 A P).
Proof. exact (MK_COMB (@lem4871570 A) (@lem4871569 A P)). Qed.
Lemma lem4871572 {A : Type'} (P : type686 A) : (term74 A P) = (term74 A P).
Proof. exact (eq_refl (term74 A P)). Qed.
Lemma lem4871573 {A : Type'} (P : type686 A) : (term90 A P) = (term76 A P).
Proof. exact (MK_COMB (@lem4871572 A P) (@lem4871571 A P)). Qed.
Lemma lem4871574 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4871575 {A : Type'} (P : type686 A) : (term95 A P) = (term96 A P).
Proof. exact (MK_COMB (@lem4871574) (@lem4871573 A P)). Qed.
Lemma lem4871576 {A : Type'} (P : type686 A) (s : A -> Prop) : (term92 A P s) = (term65 A P s).
Proof. exact (eq_refl (term92 A P s)). Qed.
Lemma lem4871577 {A : Type'} (P : type686 A) : (term74 A P) = (term74 A P).
Proof. exact (eq_refl (term74 A P)). Qed.
Lemma lem4871578 {A : Type'} (P : type686 A) (s : A -> Prop) : (term97 A P s) = (term98 A P s).
Proof. exact (MK_COMB (@lem4871577 A P) (@lem4871576 A P s)). Qed.
Lemma lem4871579 {A : Type'} (P : type686 A) : (term99 A P) = (term100 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4871578 A P s)). Qed.
Lemma lem4871580 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4871581 {A : Type'} (P : type686 A) : (term91 A P) = (term101 A P).
Proof. exact (MK_COMB (@lem4871580 A) (@lem4871579 A P)). Qed.
Lemma lem4871582 {A : Type'} (P : type686 A) : ((term90 A P) = (term91 A P)) = ((term76 A P) = (term101 A P)).
Proof. exact (MK_COMB (@lem4871575 A P) (@lem4871581 A P)). Qed.
Lemma lem4871583 {A : Type'} (P : type686 A) : (term76 A P) = (term101 A P).
Proof. exact (EQ_MP (@lem4871582 A P) (@lem4871567 A P)). Qed.
Lemma lem4871585 {A : Type'} (P : Prop) (Q : A -> Prop) : (term86 A P Q) = (term87 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4871586 {A : Type'} (P : Prop) (Q : type686 A) : (term88 A P Q) = (term89 A P Q).
Proof. exact (@lem4871585 (A -> Prop) P Q). Qed.
Lemma lem4871587 {A : Type'} (P : type686 A) (s : A -> Prop) : (term102 A P s) = (term103 A P s).
Proof. exact (@lem4871586 A (term53 A P) (term64 A P s)). Qed.
Lemma lem4871588 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term104 A P s t) = (term55 A P s t).
Proof. exact (eq_refl (term104 A P s t)). Qed.
Lemma lem4871589 {A : Type'} (P : type686 A) (s : A -> Prop) : (term105 A P s) = (term64 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4871588 A P s t)). Qed.
Lemma lem4871590 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4871591 {A : Type'} (P : type686 A) (s : A -> Prop) : (term106 A P s) = (term65 A P s).
Proof. exact (MK_COMB (@lem4871590 A) (@lem4871589 A P s)). Qed.
Lemma lem4871592 {A : Type'} (P : type686 A) : (term74 A P) = (term74 A P).
Proof. exact (eq_refl (term74 A P)). Qed.
Lemma lem4871593 {A : Type'} (P : type686 A) (s : A -> Prop) : (term102 A P s) = (term98 A P s).
Proof. exact (MK_COMB (@lem4871592 A P) (@lem4871591 A P s)). Qed.
Lemma lem4871594 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4871595 {A : Type'} (P : type686 A) (s : A -> Prop) : (term107 A P s) = (term108 A P s).
Proof. exact (MK_COMB (@lem4871594) (@lem4871593 A P s)). Qed.
Lemma lem4871596 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term104 A P s t) = (term55 A P s t).
Proof. exact (eq_refl (term104 A P s t)). Qed.
Lemma lem4871597 {A : Type'} (P : type686 A) : (term74 A P) = (term74 A P).
Proof. exact (eq_refl (term74 A P)). Qed.
Lemma lem4871598 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term109 A P s t) = (term110 A P s t).
Proof. exact (MK_COMB (@lem4871597 A P) (@lem4871596 A P s t)). Qed.
Lemma lem4871599 {A : Type'} (P : type686 A) (s : A -> Prop) : (term111 A P s) = (term112 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4871598 A P s t)). Qed.
Lemma lem4871600 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4871601 {A : Type'} (P : type686 A) (s : A -> Prop) : (term103 A P s) = (term113 A P s).
Proof. exact (MK_COMB (@lem4871600 A) (@lem4871599 A P s)). Qed.
Lemma lem4871602 {A : Type'} (P : type686 A) (s : A -> Prop) : ((term102 A P s) = (term103 A P s)) = ((term98 A P s) = (term113 A P s)).
Proof. exact (MK_COMB (@lem4871595 A P s) (@lem4871601 A P s)). Qed.
Lemma lem4871603 {A : Type'} (P : type686 A) (s : A -> Prop) : (term98 A P s) = (term113 A P s).
Proof. exact (EQ_MP (@lem4871602 A P s) (@lem4871587 A P s)). Qed.
Lemma lem4871604 {A : Type'} (P : type686 A) : (term100 A P) = (term114 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4871603 A P s)). Qed.
Lemma lem4871605 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4871606 {A : Type'} (P : type686 A) : (term101 A P) = (term115 A P).
Proof. exact (MK_COMB (@lem4871605 A) (@lem4871604 A P)). Qed.
Lemma lem4871607 {A : Type'} (P : type686 A) : (term76 A P) = (term115 A P).
Proof. exact (TRANS (@lem4871583 A P) (@lem4871606 A P)). Qed.
Lemma lem4871608 {A : Type'} : (term84 A) = (term116 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4871607 A P)). Qed.
Lemma lem4871609 {A : Type'} : (@ex ((A -> Prop) -> Prop)) = (@ex ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> Prop))). Qed.
Lemma lem4871611 {A : Type'} : (term85 A) = (term117 A).
Proof. exact (MK_COMB (@lem4871609 A) (@lem4871608 A)). Qed.
Lemma lem4871612 {A : Type'} : (term19 A) = (term117 A).
Proof. exact (TRANS (@lem4871410 A) (@lem4871611 A)). Qed.
Lemma lem4871613 {A : Type'} (h1 : term19 A) : term117 A.
Proof. exact (EQ_MP (@lem4871612 A) (@lem4871344 A h1)). Qed.
Lemma lem4871620 {A : Type'} (P : type686 A) (s : A -> Prop) : (term29 A P s) = (term118 A P s).
Proof. exact (@lem17265 (P s) (@UNION_OF A (@ARBITRARY A) P s)). Qed.
Lemma lem4871621 {A : Type'} (P : type686 A) : (term30 A P) = (term119 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4871620 A P s)). Qed.
Lemma lem4871622 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4871623 {A : Type'} (P : type686 A) : (term31 A P) = (term120 A P).
Proof. exact (MK_COMB (@lem4871622 A) (@lem4871621 A P)). Qed.
Lemma lem4871624 {A : Type'} : (term32 A) = (term121 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4871623 A P)). Qed.
Lemma lem4871625 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4871682 {A : Type'} : (term20 A) = (term122 A).
Proof. exact (MK_COMB (@lem4871625 A) (@lem4871624 A)). Qed.
Lemma lem4871683 {A : Type'} (h1 : term20 A) : term122 A.
Proof. exact (EQ_MP (@lem4871682 A) (@lem4871345 A h1)). Qed.
Lemma lem4871684 {A : Type'} (P : type686 A) (h1 : term115 A P) : term115 A P.
Proof. exact (h1). Qed.
Lemma lem4871685 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term113 A P s) : term113 A P s.
Proof. exact (h1). Qed.
Lemma lem4871686 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term110 A P s t.
Proof. exact (h1). Qed.
Lemma lem4871695 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4871696 {A : Type'} (f : type74 A) (x : type180 A) : (f x) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4871695 (type180 A) (type174 A) f x). Qed.
Lemma lem4871697 {A : Type'} : (@UNION_OF A (@ARBITRARY A)) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@ARBITRARY A)).
Proof. exact (@lem4871696 A (@UNION_OF A) (@ARBITRARY A)). Qed.
Lemma lem4871698 {A : Type'} (P : type686 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem4871699 {A : Type'} (P : type686 A) : (@UNION_OF A (@ARBITRARY A) P) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@ARBITRARY A) P).
Proof. exact (MK_COMB (@lem4871697 A) (@lem4871698 A P)). Qed.
Lemma lem4871701 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4871702 {A : Type'} (f : type174 A) (x : type686 A) : (f x) = (@I (((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4871701 (type686 A) (type686 A) f x). Qed.
Lemma lem4871703 {A : Type'} (P : type686 A) : (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@ARBITRARY A) P) = (term123 A P).
Proof. exact (@lem4871702 A (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@ARBITRARY A)) P). Qed.
Lemma lem4871704 {A : Type'} (P : type686 A) : (@UNION_OF A (@ARBITRARY A) P) = (term123 A P).
Proof. exact (TRANS (@lem4871699 A P) (@lem4871703 A P)). Qed.
Lemma lem4871705 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4871706 {A : Type'} (P : type686 A) (s : A -> Prop) : (@UNION_OF A (@ARBITRARY A) P s) = (term124 A P s).
Proof. exact (MK_COMB (@lem4871704 A P) (@lem4871705 A s)). Qed.
Lemma lem4871708 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4871709 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4871708 (A -> Prop) Prop f x). Qed.
Lemma lem4871710 {A : Type'} (P : type686 A) (s : A -> Prop) : (term124 A P s) = (term125 A P s).
Proof. exact (@lem4871709 A (term123 A P) s). Qed.
Lemma lem4871712 {A : Type'} (P : type686 A) (s : A -> Prop) : (@UNION_OF A (@ARBITRARY A) P s) = (term125 A P s).
Proof. exact (TRANS (@lem4871706 A P s) (@lem4871710 A P s)). Qed.
Lemma lem4871713 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4871718 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4871719 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4871718 (A -> Prop) Prop f x). Qed.
Lemma lem4871721 {A : Type'} (P : type686 A) (s : A -> Prop) : (P s) = (@I ((A -> Prop) -> Prop) P s).
Proof. exact (@lem4871719 A P s). Qed.
Lemma lem4871722 {A : Type'} (P : type686 A) (s : A -> Prop) : (term126 A P s) = (term127 A P s).
Proof. exact (MK_COMB (@lem4871713) (@lem4871721 A P s)). Qed.
Lemma lem4871723 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4871724 {A : Type'} (P : type686 A) (s : A -> Prop) : (term128 A P s) = (term129 A P s).
Proof. exact (MK_COMB (@lem4871723) (@lem4871722 A P s)). Qed.
Lemma lem4871725 {A : Type'} (P : type686 A) (s : A -> Prop) : (term118 A P s) = (term130 A P s).
Proof. exact (MK_COMB (@lem4871724 A P s) (@lem4871712 A P s)). Qed.
Lemma lem4871726 {A : Type'} (P : type686 A) : (term119 A P) = (term131 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4871725 A P s)). Qed.
Lemma lem4871727 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4871728 {A : Type'} (P : type686 A) : (term120 A P) = (term132 A P).
Proof. exact (MK_COMB (@lem4871727 A) (@lem4871726 A P)). Qed.
Lemma lem4871729 {A : Type'} : (term121 A) = (term133 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4871728 A P)). Qed.
Lemma lem4871730 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4871731 {A : Type'} : (term122 A) = (term134 A).
Proof. exact (MK_COMB (@lem4871730 A) (@lem4871729 A)). Qed.
Lemma lem4871732 {A : Type'} (h1 : term20 A) : term134 A.
Proof. exact (EQ_MP (@lem4871731 A) (@lem4871683 A h1)). Qed.
Lemma lem4871733 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4871743 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4871744 {A : Type'} (f : type636 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem4871743 (A -> Prop) (type672 A) f x). Qed.
Lemma lem4871745 {A : Type'} (s : A -> Prop) : (@INTER A s) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@INTER A) s).
Proof. exact (@lem4871744 A (@INTER A) s). Qed.
Lemma lem4871746 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4871747 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@INTER A s t) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@INTER A) s t).
Proof. exact (MK_COMB (@lem4871745 A s) (@lem4871746 A t)). Qed.
Lemma lem4871749 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4871750 {A : Type'} (f : type672 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem4871749 (A -> Prop) (A -> Prop) f x). Qed.
Lemma lem4871751 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@INTER A) s t) = (term135 A s t).
Proof. exact (@lem4871750 A (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@INTER A) s) t). Qed.
Lemma lem4871753 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@INTER A s t) = (term135 A s t).
Proof. exact (TRANS (@lem4871747 A s t) (@lem4871751 A s t)). Qed.
Lemma lem4871755 {A : Type'} (P : type686 A) : (@UNION_OF A (@ARBITRARY A) P) = (@UNION_OF A (@ARBITRARY A) P).
Proof. exact (eq_refl (@UNION_OF A (@ARBITRARY A) P)). Qed.
Lemma lem4871756 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term56 A P s t) = (term136 A P s t).
Proof. exact (MK_COMB (@lem4871755 A P) (@lem4871753 A s t)). Qed.
Lemma lem4871758 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4871759 {A : Type'} (f : type74 A) (x : type180 A) : (f x) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4871758 (type180 A) (type174 A) f x). Qed.
Lemma lem4871760 {A : Type'} : (@UNION_OF A (@ARBITRARY A)) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@ARBITRARY A)).
Proof. exact (@lem4871759 A (@UNION_OF A) (@ARBITRARY A)). Qed.
Lemma lem4871761 {A : Type'} (P : type686 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem4871762 {A : Type'} (P : type686 A) : (@UNION_OF A (@ARBITRARY A) P) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@ARBITRARY A) P).
Proof. exact (MK_COMB (@lem4871760 A) (@lem4871761 A P)). Qed.
Lemma lem4871764 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4871765 {A : Type'} (f : type174 A) (x : type686 A) : (f x) = (@I (((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4871764 (type686 A) (type686 A) f x). Qed.
Lemma lem4871766 {A : Type'} (P : type686 A) : (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@ARBITRARY A) P) = (term123 A P).
Proof. exact (@lem4871765 A (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@UNION_OF A) (@ARBITRARY A)) P). Qed.
Lemma lem4871767 {A : Type'} (P : type686 A) : (@UNION_OF A (@ARBITRARY A) P) = (term123 A P).
Proof. exact (TRANS (@lem4871762 A P) (@lem4871766 A P)). Qed.
Lemma lem4871768 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term135 A s t) = (term135 A s t).
Proof. exact (eq_refl (term135 A s t)). Qed.
Lemma lem4871769 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term136 A P s t) = (term137 A P s t).
Proof. exact (MK_COMB (@lem4871767 A P) (@lem4871768 A s t)). Qed.
Lemma lem4871771 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4871772 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4871771 (A -> Prop) Prop f x). Qed.
Lemma lem4871773 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term137 A P s t) = (term138 A P s t).
Proof. exact (@lem4871772 A (term123 A P) (term135 A s t)). Qed.
Lemma lem4871774 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term136 A P s t) = (term138 A P s t).
Proof. exact (TRANS (@lem4871769 A P s t) (@lem4871773 A P s t)). Qed.
Lemma lem4871775 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term56 A P s t) = (term138 A P s t).
Proof. exact (TRANS (@lem4871756 A P s t) (@lem4871774 A P s t)). Qed.
Lemma lem4871776 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term139 A P s t) = (term140 A P s t).
Proof. exact (MK_COMB (@lem4871733) (@lem4871775 A P s t)). Qed.
Lemma lem4871781 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4871782 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4871781 (A -> Prop) Prop f x). Qed.
Lemma lem4871784 {A : Type'} (P : type686 A) (t : A -> Prop) : (P t) = (@I ((A -> Prop) -> Prop) P t).
Proof. exact (@lem4871782 A P t). Qed.
Lemma lem4871789 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4871790 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4871789 (A -> Prop) Prop f x). Qed.
Lemma lem4871792 {A : Type'} (P : type686 A) (s : A -> Prop) : (P s) = (@I ((A -> Prop) -> Prop) P s).
Proof. exact (@lem4871790 A P s). Qed.
Lemma lem4871793 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4871794 {A : Type'} (P : type686 A) (s : A -> Prop) : (term141 A P s) = (term142 A P s).
Proof. exact (MK_COMB (@lem4871793) (@lem4871792 A P s)). Qed.
Lemma lem4871795 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term49 A s P t) = (term143 A s P t).
Proof. exact (MK_COMB (@lem4871794 A P s) (@lem4871784 A P t)). Qed.
Lemma lem4871796 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4871797 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term144 A s P t) = (term145 A s P t).
Proof. exact (MK_COMB (@lem4871796) (@lem4871795 A s P t)). Qed.
Lemma lem4871798 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term55 A P s t) = (term146 A P s t).
Proof. exact (MK_COMB (@lem4871797 A s P t) (@lem4871776 A P s t)). Qed.
Lemma lem4871799 {A : Type'} (P : type686 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem4871806 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4871807 {A : Type'} (f : type636 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem4871806 (A -> Prop) (type672 A) f x). Qed.
Lemma lem4871808 {A : Type'} (s : A -> Prop) : (@INTER A s) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@INTER A) s).
Proof. exact (@lem4871807 A (@INTER A) s). Qed.
Lemma lem4871809 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4871810 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@INTER A s t) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@INTER A) s t).
Proof. exact (MK_COMB (@lem4871808 A s) (@lem4871809 A t)). Qed.
Lemma lem4871812 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4871813 {A : Type'} (f : type672 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem4871812 (A -> Prop) (A -> Prop) f x). Qed.
Lemma lem4871814 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@INTER A) s t) = (term135 A s t).
Proof. exact (@lem4871813 A (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@INTER A) s) t). Qed.
Lemma lem4871816 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@INTER A s t) = (term135 A s t).
Proof. exact (TRANS (@lem4871810 A s t) (@lem4871814 A s t)). Qed.
Lemma lem4871817 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term44 A P s t) = (term147 A P s t).
Proof. exact (MK_COMB (@lem4871799 A P) (@lem4871816 A s t)). Qed.
Lemma lem4871819 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4871820 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4871819 (A -> Prop) Prop f x). Qed.
Lemma lem4871821 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term147 A P s t) = (term148 A P s t).
Proof. exact (@lem4871820 A P (term135 A s t)). Qed.
Lemma lem4871822 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term44 A P s t) = (term148 A P s t).
Proof. exact (TRANS (@lem4871817 A P s t) (@lem4871821 A P s t)). Qed.
Lemma lem4871823 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4871828 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4871829 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4871828 (A -> Prop) Prop f x). Qed.
Lemma lem4871831 {A : Type'} (P : type686 A) (t : A -> Prop) : (P t) = (@I ((A -> Prop) -> Prop) P t).
Proof. exact (@lem4871829 A P t). Qed.
Lemma lem4871832 {A : Type'} (P : type686 A) (t : A -> Prop) : (term126 A P t) = (term127 A P t).
Proof. exact (MK_COMB (@lem4871823) (@lem4871831 A P t)). Qed.
Lemma lem4871833 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4871838 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4871839 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4871838 (A -> Prop) Prop f x). Qed.
Lemma lem4871841 {A : Type'} (P : type686 A) (s : A -> Prop) : (P s) = (@I ((A -> Prop) -> Prop) P s).
Proof. exact (@lem4871839 A P s). Qed.
Lemma lem4871842 {A : Type'} (P : type686 A) (s : A -> Prop) : (term126 A P s) = (term127 A P s).
Proof. exact (MK_COMB (@lem4871833) (@lem4871841 A P s)). Qed.
Lemma lem4871843 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4871844 {A : Type'} (P : type686 A) (s : A -> Prop) : (term128 A P s) = (term129 A P s).
Proof. exact (MK_COMB (@lem4871843) (@lem4871842 A P s)). Qed.
Lemma lem4871845 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term43 A s P t) = (term149 A s P t).
Proof. exact (MK_COMB (@lem4871844 A P s) (@lem4871832 A P t)). Qed.
Lemma lem4871846 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4871847 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term46 A s P t) = (term150 A s P t).
Proof. exact (MK_COMB (@lem4871846) (@lem4871845 A s P t)). Qed.
Lemma lem4871848 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term48 A P s t) = (term151 A P s t).
Proof. exact (MK_COMB (@lem4871847 A s P t) (@lem4871822 A P s t)). Qed.
Lemma lem4871849 {A : Type'} (P : type686 A) (s : A -> Prop) : (term50 A P s) = (term152 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4871848 A P s t)). Qed.
Lemma lem4871850 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4871851 {A : Type'} (P : type686 A) (s : A -> Prop) : (term51 A P s) = (term153 A P s).
Proof. exact (MK_COMB (@lem4871850 A) (@lem4871849 A P s)). Qed.
Lemma lem4871852 {A : Type'} (P : type686 A) : (term52 A P) = (term154 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4871851 A P s)). Qed.
Lemma lem4871853 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4871854 {A : Type'} (P : type686 A) : (term53 A P) = (term155 A P).
Proof. exact (MK_COMB (@lem4871853 A) (@lem4871852 A P)). Qed.
Lemma lem4871855 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4871856 {A : Type'} (P : type686 A) : (term74 A P) = (term156 A P).
Proof. exact (MK_COMB (@lem4871855) (@lem4871854 A P)). Qed.
Lemma lem4871857 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term110 A P s t) = (term157 A P s t).
Proof. exact (MK_COMB (@lem4871856 A P) (@lem4871798 A P s t)). Qed.
Lemma lem4871858 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term157 A P s t.
Proof. exact (EQ_MP (@lem4871857 A P s t) (@lem4871686 A P s t h1)). Qed.
Lemma lem4871859 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term146 A P s t.
Proof. exact (proj2 (@lem4871858 A P s t h1)). Qed.
Lemma lem4871860 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term155 A P.
Proof. exact (proj1 (@lem4871858 A P s t h1)). Qed.
Lemma lem4871862 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term143 A s P t.
Proof. exact (proj1 (@lem4871859 A P s t h1)). Qed.
Lemma lem4871872 {A : Type'} (P : type686 A) (s : A -> Prop) : (term130 A P s) = (term130 A P s).
Proof. exact (eq_refl (term130 A P s)). Qed.
Lemma lem4871873 {A : Type'} (P : type686 A) : (term131 A P) = (term131 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4871872 A P s)). Qed.
Lemma lem4871874 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4871875 {A : Type'} (P : type686 A) : (term132 A P) = (term132 A P).
Proof. exact (MK_COMB (@lem4871874 A) (@lem4871873 A P)). Qed.
Lemma lem4871876 {A : Type'} : (term133 A) = (term133 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4871875 A P)). Qed.
Lemma lem4871877 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4871879 {A : Type'} : (term134 A) = (term134 A).
Proof. exact (MK_COMB (@lem4871877 A) (@lem4871876 A)). Qed.
Lemma lem4871880 {A : Type'} (h1 : term20 A) : term134 A.
Proof. exact (EQ_MP (@lem4871879 A) (@lem4871732 A h1)). Qed.
Lemma lem4871894 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term151 A P s t) = (term151 A P s t).
Proof. exact (eq_refl (term151 A P s t)). Qed.
Lemma lem4871895 {A : Type'} (P : type686 A) (s : A -> Prop) : (term152 A P s) = (term152 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4871894 A P s t)). Qed.
Lemma lem4871896 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4871897 {A : Type'} (P : type686 A) (s : A -> Prop) : (term153 A P s) = (term153 A P s).
Proof. exact (MK_COMB (@lem4871896 A) (@lem4871895 A P s)). Qed.
Lemma lem4871898 {A : Type'} (P : type686 A) : (term154 A P) = (term154 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4871897 A P s)). Qed.
Lemma lem4871899 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4871901 {A : Type'} (P : type686 A) : (term155 A P) = (term155 A P).
Proof. exact (MK_COMB (@lem4871899 A) (@lem4871898 A P)). Qed.
Lemma lem4871902 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term155 A P.
Proof. exact (EQ_MP (@lem4871901 A P) (@lem4871860 A P s t h1)). Qed.
Lemma lem4871915 {A : Type'} (_60263 : type686 A) (h1 : term20 A) : term158 A _60263.
Proof. exact (@lem4871880 A h1 _60263). Qed.
Lemma lem4871916 {A : Type'} (_60263 : type686 A) : (term158 A _60263) = (term132 A _60263).
Proof. exact (eq_refl (term158 A _60263)). Qed.
Lemma lem4871917 {A : Type'} (_60263 : type686 A) (h1 : term20 A) : term132 A _60263.
Proof. exact (EQ_MP (@lem4871916 A _60263) (@lem4871915 A _60263 h1)). Qed.
Lemma lem4871918 {A : Type'} (_60263 : type686 A) (_60264 : A -> Prop) (h1 : term20 A) : term159 A _60263 _60264.
Proof. exact (@lem4871917 A _60263 h1 _60264). Qed.
Lemma lem4871919 {A : Type'} (_60263 : type686 A) (_60264 : A -> Prop) : (term159 A _60263 _60264) = (term130 A _60263 _60264).
Proof. exact (eq_refl (term159 A _60263 _60264)). Qed.
Lemma lem4871921 {A : Type'} (_60265 : A -> Prop) (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term160 A P _60265.
Proof. exact (@lem4871902 A P s t h1 _60265). Qed.
Lemma lem4871922 {A : Type'} (P : type686 A) (_60265 : A -> Prop) : (term160 A P _60265) = (term153 A P _60265).
Proof. exact (eq_refl (term160 A P _60265)). Qed.
Lemma lem4871923 {A : Type'} (_60265 : A -> Prop) (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term153 A P _60265.
Proof. exact (EQ_MP (@lem4871922 A P _60265) (@lem4871921 A _60265 P s t h1)). Qed.
Lemma lem4871924 {A : Type'} (_60265 : A -> Prop) (_60266 : A -> Prop) (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term161 A P _60265 _60266.
Proof. exact (@lem4871923 A _60265 P s t h1 _60266). Qed.
Lemma lem4871925 {A : Type'} (P : type686 A) (_60265 : A -> Prop) (_60266 : A -> Prop) : (term161 A P _60265 _60266) = (term151 A P _60265 _60266).
Proof. exact (eq_refl (term161 A P _60265 _60266)). Qed.
Lemma lem4871926 {A : Type'} (_60265 : A -> Prop) (_60266 : A -> Prop) (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term151 A P _60265 _60266.
Proof. exact (EQ_MP (@lem4871925 A P _60265 _60266) (@lem4871924 A _60265 _60266 P s t h1)). Qed.
Lemma lem4871932 {A : Type'} (_60263 : type686 A) (_60264 : A -> Prop) (h1 : term20 A) : term130 A _60263 _60264.
Proof. exact (EQ_MP (@lem4871919 A _60263 _60264) (@lem4871918 A _60263 _60264 h1)). Qed.
Lemma lem4871943 {A : Type'} (P : type686 A) (_60265 : A -> Prop) (_60266 : A -> Prop) : (term151 A P _60265 _60266) = (term162 A P _60265 _60266).
Proof. exact (@lem4871105 (term127 A P _60265) (term127 A P _60266) (term148 A P _60265 _60266)). Qed.
Lemma lem4871944 {A : Type'} (_60265 : A -> Prop) (_60266 : A -> Prop) (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term162 A P _60265 _60266.
Proof. exact (EQ_MP (@lem4871943 A P _60265 _60266) (@lem4871926 A _60265 _60266 P s t h1)). Qed.
Lemma lem4871946 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term140 A P s t.
Proof. exact (proj2 (@lem4871859 A P s t h1)). Qed.
Lemma lem4871952 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : @I ((A -> Prop) -> Prop) P s.
Proof. exact (proj1 (@lem4871862 A P s t h1)). Qed.
Lemma lem4871953 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term163 A P s.
Proof. exact (fun h0 : term127 A P s => @lem4871952 A P s t h1). Qed.
Lemma lem4871955 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4871956 {A : Type'} (P : type686 A) (s : A -> Prop) : (term163 A P s) = (@I ((A -> Prop) -> Prop) P s).
Proof. exact (@lem4871955 (@I ((A -> Prop) -> Prop) P s)). Qed.
Lemma lem4871957 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : @I ((A -> Prop) -> Prop) P s.
Proof. exact (EQ_MP (@lem4871956 A P s) (@lem4871953 A P s t h1)). Qed.
Lemma lem4871959 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : @I ((A -> Prop) -> Prop) P t.
Proof. exact (proj2 (@lem4871862 A P s t h1)). Qed.
Lemma lem4871960 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term163 A P t.
Proof. exact (fun h0 : term127 A P t => @lem4871959 A P s t h1). Qed.
Lemma lem4871962 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4871963 {A : Type'} (P : type686 A) (t : A -> Prop) : (term163 A P t) = (@I ((A -> Prop) -> Prop) P t).
Proof. exact (@lem4871962 (@I ((A -> Prop) -> Prop) P t)). Qed.
Lemma lem4871964 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : @I ((A -> Prop) -> Prop) P t.
Proof. exact (EQ_MP (@lem4871963 A P t) (@lem4871960 A P s t h1)). Qed.
Lemma lem4871980 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4871981 {A : Type'} (_60265 : A -> Prop) (P : type686 A) (_60266 : A -> Prop) : (term165 A P _60265 _60266) = (term166 A _60265 P _60266).
Proof. exact (@lem4871980 (term148 A P _60265 _60266) (term127 A P _60266)). Qed.
Lemma lem4871987 {A : Type'} (P : type686 A) (_60265 : A -> Prop) : (term129 A P _60265) = (term129 A P _60265).
Proof. exact (eq_refl (term129 A P _60265)). Qed.
Lemma lem4871988 {A : Type'} (_60265 : A -> Prop) (P : type686 A) (_60266 : A -> Prop) : (term162 A P _60265 _60266) = (term167 A _60265 P _60266).
Proof. exact (MK_COMB (@lem4871987 A P _60265) (@lem4871981 A _60265 P _60266)). Qed.
Lemma lem4871992 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4871993 {A : Type'} (_60265 : A -> Prop) (P : type686 A) (_60266 : A -> Prop) : (term167 A _60265 P _60266) = (term168 A _60265 P _60266).
Proof. exact (@lem4871992 (term148 A P _60265 _60266) (term127 A P _60265) (term127 A P _60266)). Qed.
Lemma lem4872009 {A : Type'} (_60265 : A -> Prop) (P : type686 A) (_60266 : A -> Prop) : (term162 A P _60265 _60266) = (term168 A _60265 P _60266).
Proof. exact (TRANS (@lem4871988 A _60265 P _60266) (@lem4871993 A _60265 P _60266)). Qed.
Lemma lem4872010 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4872011 {A : Type'} (_60265 : A -> Prop) (P : type686 A) (_60266 : A -> Prop) : (term169 A P _60265 _60266) = (term170 A _60265 P _60266).
Proof. exact (MK_COMB (@lem4872010) (@lem4872009 A _60265 P _60266)). Qed.
Lemma lem4872027 {A : Type'} (_60265 : A -> Prop) (P : type686 A) (_60266 : A -> Prop) : (term168 A _60265 P _60266) = (term168 A _60265 P _60266).
Proof. exact (eq_refl (term168 A _60265 P _60266)). Qed.
Lemma lem4872028 {A : Type'} (_60265 : A -> Prop) (P : type686 A) (_60266 : A -> Prop) : ((term162 A P _60265 _60266) = (term168 A _60265 P _60266)) = ((term168 A _60265 P _60266) = (term168 A _60265 P _60266)).
Proof. exact (MK_COMB (@lem4872011 A _60265 P _60266) (@lem4872027 A _60265 P _60266)). Qed.
Lemma lem4872030 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4872031 (x : Prop) : (x = x) = True.
Proof. exact (@lem4872030 Prop x). Qed.
Lemma lem4872032 {A : Type'} (_60265 : A -> Prop) (P : type686 A) (_60266 : A -> Prop) : ((term168 A _60265 P _60266) = (term168 A _60265 P _60266)) = True.
Proof. exact (@lem4872031 (term168 A _60265 P _60266)). Qed.
Lemma lem4872033 {A : Type'} (_60265 : A -> Prop) (P : type686 A) (_60266 : A -> Prop) : ((term162 A P _60265 _60266) = (term168 A _60265 P _60266)) = True.
Proof. exact (TRANS (@lem4872028 A _60265 P _60266) (@lem4872032 A _60265 P _60266)). Qed.
Lemma lem4872034 {A : Type'} (_60265 : A -> Prop) (P : type686 A) (_60266 : A -> Prop) : True = ((term162 A P _60265 _60266) = (term168 A _60265 P _60266)).
Proof. exact (SYM (@lem4872033 A _60265 P _60266)). Qed.
Lemma lem4872035 {A : Type'} (_60265 : A -> Prop) (P : type686 A) (_60266 : A -> Prop) : (term162 A P _60265 _60266) = (term168 A _60265 P _60266).
Proof. exact (EQ_MP (@lem4872034 A _60265 P _60266) (@lem0)). Qed.
Lemma lem4872036 {A : Type'} (_60265 : A -> Prop) (_60266 : A -> Prop) (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term168 A _60265 P _60266.
Proof. exact (EQ_MP (@lem4872035 A _60265 P _60266) (@lem4871944 A _60265 _60266 P s t h1)). Qed.
Lemma lem4872038 (b : Prop) (a : Prop) : (a \/ b) = (term171 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4872039 {A : Type'} (P : type686 A) (_60265 : A -> Prop) (_60266 : A -> Prop) : (term168 A _60265 P _60266) = (term172 A P _60265 _60266).
Proof. exact (@lem4872038 (term149 A _60265 P _60266) (term148 A P _60265 _60266)). Qed.
Lemma lem4872041 (a : Prop) (b : Prop) : (term173 a b) = (term174 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4872042 {A : Type'} (_60265 : A -> Prop) (P : type686 A) (_60266 : A -> Prop) : (term175 A _60265 P _60266) = (term176 A _60265 P _60266).
Proof. exact (@lem4872041 (term127 A P _60265) (term127 A P _60266)). Qed.
Lemma lem4872044 (a : Prop) : (term177 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4872045 {A : Type'} (P : type686 A) (_60265 : A -> Prop) : (term178 A P _60265) = (@I ((A -> Prop) -> Prop) P _60265).
Proof. exact (@lem4872044 (@I ((A -> Prop) -> Prop) P _60265)). Qed.
Lemma lem4872046 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4872047 {A : Type'} (P : type686 A) (_60265 : A -> Prop) : (term179 A P _60265) = (term142 A P _60265).
Proof. exact (MK_COMB (@lem4872046) (@lem4872045 A P _60265)). Qed.
Lemma lem4872049 (a : Prop) : (term177 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4872050 {A : Type'} (P : type686 A) (_60266 : A -> Prop) : (term178 A P _60266) = (@I ((A -> Prop) -> Prop) P _60266).
Proof. exact (@lem4872049 (@I ((A -> Prop) -> Prop) P _60266)). Qed.
Lemma lem4872051 {A : Type'} (_60265 : A -> Prop) (P : type686 A) (_60266 : A -> Prop) : (term176 A _60265 P _60266) = (term143 A _60265 P _60266).
Proof. exact (MK_COMB (@lem4872047 A P _60265) (@lem4872050 A P _60266)). Qed.
Lemma lem4872052 {A : Type'} (_60265 : A -> Prop) (P : type686 A) (_60266 : A -> Prop) : (term175 A _60265 P _60266) = (term143 A _60265 P _60266).
Proof. exact (TRANS (@lem4872042 A _60265 P _60266) (@lem4872051 A _60265 P _60266)). Qed.
Lemma lem4872053 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4872054 {A : Type'} (_60265 : A -> Prop) (P : type686 A) (_60266 : A -> Prop) : (term180 A _60265 P _60266) = (term181 A _60265 P _60266).
Proof. exact (MK_COMB (@lem4872053) (@lem4872052 A _60265 P _60266)). Qed.
Lemma lem4872055 {A : Type'} (P : type686 A) (_60265 : A -> Prop) (_60266 : A -> Prop) : (term148 A P _60265 _60266) = (term148 A P _60265 _60266).
Proof. exact (eq_refl (term148 A P _60265 _60266)). Qed.
Lemma lem4872056 {A : Type'} (P : type686 A) (_60265 : A -> Prop) (_60266 : A -> Prop) : (term172 A P _60265 _60266) = (term182 A P _60265 _60266).
Proof. exact (MK_COMB (@lem4872054 A _60265 P _60266) (@lem4872055 A P _60265 _60266)). Qed.
Lemma lem4872057 {A : Type'} (P : type686 A) (_60265 : A -> Prop) (_60266 : A -> Prop) : (term168 A _60265 P _60266) = (term182 A P _60265 _60266).
Proof. exact (TRANS (@lem4872039 A P _60265 _60266) (@lem4872056 A P _60265 _60266)). Qed.
Lemma lem4872059 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term143 A s P t.
Proof. exact (conj (@lem4871957 A P s t h1) (@lem4871964 A P s t h1)). Qed.
Lemma lem4872061 {A : Type'} (_60265 : A -> Prop) (_60266 : A -> Prop) (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term182 A P _60265 _60266.
Proof. exact (EQ_MP (@lem4872057 A P _60265 _60266) (@lem4872036 A _60265 _60266 P s t h1)). Qed.
Lemma lem4872062 {A : Type'} (_60265 : A -> Prop) (_60266 : A -> Prop) (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term182 A P _60265 _60266.
Proof. exact (@lem4872061 A _60265 _60266 P s t h1). Qed.
Lemma lem4872063 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term182 A P s t.
Proof. exact (@lem4872062 A s t P s t h1). Qed.
Lemma lem4872066 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term148 A P s t.
Proof. exact (@lem4872063 A P s t h1 (@lem4872059 A P s t h1)). Qed.
Lemma lem4872067 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term183 A P s t.
Proof. exact (fun h0 : term184 A P s t => @lem4872066 A P s t h1). Qed.
Lemma lem4872069 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4872070 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term183 A P s t) = (term148 A P s t).
Proof. exact (@lem4872069 (term148 A P s t)). Qed.
Lemma lem4872071 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term148 A P s t.
Proof. exact (EQ_MP (@lem4872070 A P s t) (@lem4872067 A P s t h1)). Qed.
Lemma lem4872077 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4872078 {A : Type'} (_60263 : type686 A) (_60264 : A -> Prop) : (term130 A _60263 _60264) = (term185 A _60263 _60264).
Proof. exact (@lem4872077 (term125 A _60263 _60264) (term127 A _60263 _60264)). Qed.
Lemma lem4872084 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4872085 {A : Type'} (_60263 : type686 A) (_60264 : A -> Prop) : (term186 A _60263 _60264) = (term187 A _60263 _60264).
Proof. exact (MK_COMB (@lem4872084) (@lem4872078 A _60263 _60264)). Qed.
Lemma lem4872091 {A : Type'} (_60263 : type686 A) (_60264 : A -> Prop) : (term185 A _60263 _60264) = (term185 A _60263 _60264).
Proof. exact (eq_refl (term185 A _60263 _60264)). Qed.
Lemma lem4872092 {A : Type'} (_60263 : type686 A) (_60264 : A -> Prop) : ((term130 A _60263 _60264) = (term185 A _60263 _60264)) = ((term185 A _60263 _60264) = (term185 A _60263 _60264)).
Proof. exact (MK_COMB (@lem4872085 A _60263 _60264) (@lem4872091 A _60263 _60264)). Qed.
Lemma lem4872094 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4872095 (x : Prop) : (x = x) = True.
Proof. exact (@lem4872094 Prop x). Qed.
Lemma lem4872096 {A : Type'} (_60263 : type686 A) (_60264 : A -> Prop) : ((term185 A _60263 _60264) = (term185 A _60263 _60264)) = True.
Proof. exact (@lem4872095 (term185 A _60263 _60264)). Qed.
Lemma lem4872097 {A : Type'} (_60263 : type686 A) (_60264 : A -> Prop) : ((term130 A _60263 _60264) = (term185 A _60263 _60264)) = True.
Proof. exact (TRANS (@lem4872092 A _60263 _60264) (@lem4872096 A _60263 _60264)). Qed.
Lemma lem4872098 {A : Type'} (_60263 : type686 A) (_60264 : A -> Prop) : True = ((term130 A _60263 _60264) = (term185 A _60263 _60264)).
Proof. exact (SYM (@lem4872097 A _60263 _60264)). Qed.
Lemma lem4872099 {A : Type'} (_60263 : type686 A) (_60264 : A -> Prop) : (term130 A _60263 _60264) = (term185 A _60263 _60264).
Proof. exact (EQ_MP (@lem4872098 A _60263 _60264) (@lem0)). Qed.
Lemma lem4872100 {A : Type'} (_60263 : type686 A) (_60264 : A -> Prop) (h1 : term20 A) : term185 A _60263 _60264.
Proof. exact (EQ_MP (@lem4872099 A _60263 _60264) (@lem4871932 A _60263 _60264 h1)). Qed.
Lemma lem4872102 (b : Prop) (a : Prop) : (a \/ b) = (term171 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4872103 {A : Type'} (_60263 : type686 A) (_60264 : A -> Prop) : (term185 A _60263 _60264) = (term188 A _60263 _60264).
Proof. exact (@lem4872102 (term127 A _60263 _60264) (term125 A _60263 _60264)). Qed.
Lemma lem4872105 (a : Prop) : (term177 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4872106 {A : Type'} (_60263 : type686 A) (_60264 : A -> Prop) : (term178 A _60263 _60264) = (@I ((A -> Prop) -> Prop) _60263 _60264).
Proof. exact (@lem4872105 (@I ((A -> Prop) -> Prop) _60263 _60264)). Qed.
Lemma lem4872107 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4872108 {A : Type'} (_60263 : type686 A) (_60264 : A -> Prop) : (term189 A _60263 _60264) = (term190 A _60263 _60264).
Proof. exact (MK_COMB (@lem4872107) (@lem4872106 A _60263 _60264)). Qed.
Lemma lem4872109 {A : Type'} (_60263 : type686 A) (_60264 : A -> Prop) : (term125 A _60263 _60264) = (term125 A _60263 _60264).
Proof. exact (eq_refl (term125 A _60263 _60264)). Qed.
Lemma lem4872110 {A : Type'} (_60263 : type686 A) (_60264 : A -> Prop) : (term188 A _60263 _60264) = (term191 A _60263 _60264).
Proof. exact (MK_COMB (@lem4872108 A _60263 _60264) (@lem4872109 A _60263 _60264)). Qed.
Lemma lem4872111 {A : Type'} (_60263 : type686 A) (_60264 : A -> Prop) : (term185 A _60263 _60264) = (term191 A _60263 _60264).
Proof. exact (TRANS (@lem4872103 A _60263 _60264) (@lem4872110 A _60263 _60264)). Qed.
Lemma lem4872114 {A : Type'} (_60263 : type686 A) (_60264 : A -> Prop) (h1 : term20 A) : term191 A _60263 _60264.
Proof. exact (EQ_MP (@lem4872111 A _60263 _60264) (@lem4872100 A _60263 _60264 h1)). Qed.
Lemma lem4872115 {A : Type'} (_60263 : type686 A) (_60264 : A -> Prop) (h1 : term20 A) : term191 A _60263 _60264.
Proof. exact (@lem4872114 A _60263 _60264 h1). Qed.
Lemma lem4872116 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term20 A) : term192 A P s t.
Proof. exact (@lem4872115 A P (term135 A s t) h1). Qed.
Lemma lem4872119 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term20 A) (h2 : term110 A P s t) : term138 A P s t.
Proof. exact (@lem4872116 A P s t h1 (@lem4872071 A P s t h2)). Qed.
Lemma lem4872120 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term20 A) (h2 : term110 A P s t) : term193 A P s t.
Proof. exact (fun h0 : term140 A P s t => @lem4872119 A P s t h1 h2). Qed.
Lemma lem4872122 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4872123 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term193 A P s t) = (term138 A P s t).
Proof. exact (@lem4872122 (term138 A P s t)). Qed.
Lemma lem4872124 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term20 A) (h2 : term110 A P s t) : term138 A P s t.
Proof. exact (EQ_MP (@lem4872123 A P s t) (@lem4872120 A P s t h1 h2)). Qed.
Lemma lem4872127 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4872129 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term140 A P s t) = (term194 A P s t).
Proof. exact (@lem4872127 (term138 A P s t)). Qed.
Lemma lem4872132 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term194 A P s t.
Proof. exact (EQ_MP (@lem4872129 A P s t) (@lem4871946 A P s t h1)). Qed.
Lemma lem4872135 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term20 A) (h2 : term110 A P s t) : False.
Proof. exact (@lem4872132 A P s t h2 (@lem4872124 A P s t h1 h2)). Qed.
Lemma lem4872136 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term20 A) (h2 : term110 A P s t) : term195.
Proof. exact (fun h0 : ~ False => @lem4872135 A P s t h1 h2). Qed.
Lemma lem4872138 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4872139 : term195 = False.
Proof. exact (@lem4872138 False). Qed.
Lemma lem4872140 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term20 A) (h2 : term110 A P s t) : False.
Proof. exact (EQ_MP (@lem4872139) (@lem4872136 A P s t h1 h2)). Qed.
Lemma lem4872141 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term20 A) (h2 : term113 A P s) : False.
Proof. exact (ex_elim (@lem4871685 A P s h2) (fun t : A -> Prop => fun h0 : term112 A P s t => @lem4872140 A P s t h1 h0)). Qed.
Lemma lem4872142 {A : Type'} (P : type686 A) (h1 : term20 A) (h2 : term115 A P) : False.
Proof. exact (ex_elim (@lem4871684 A P h2) (fun s : A -> Prop => fun h0 : term114 A P s => @lem4872141 A P s h1 h0)). Qed.
Lemma lem4872143 {A : Type'} (h1 : term20 A) (h2 : term19 A) : False.
Proof. exact (ex_elim (@lem4871613 A h2) (fun P : type686 A => fun h0 : term116 A P => @lem4872142 A P h1 h0)). Qed.
Lemma lem4872144 {A : Type'} (h1 : term19 A) : term25 A.
Proof. exact (fun h0 : term20 A => @lem4872143 A h0 h1). Qed.
Lemma lem4872145 {A : Type'} : (term25 A) = (term26 A).
Proof. exact (@lem69 (term20 A)). Qed.
Lemma lem4872146 {A : Type'} (h1 : term19 A) : term26 A.
Proof. exact (EQ_MP (@lem4872145 A) (@lem4872144 A h1)). Qed.
Lemma lem4872147 {A : Type'} : term28 A.
Proof. exact (fun h0 : term19 A => @lem4872146 A h0). Qed.
Lemma lem4872148 {A : Type'} : term21 A.
Proof. exact (EQ_MP (@lem4871343 A) (@lem4872147 A)). Qed.
Lemma lem4872150 {A : Type'} : term21 A.
Proof. exact (@lem4871176 A (@lem4872148 A)). Qed.
Lemma lem4872151 {A : Type'} (h1 : term19 A) : term25 A.
Proof. exact (@lem4872150 A (@lem4871158 A h1)). Qed.
Lemma lem4872152 {A : Type'} (h1 : term19 A) : False.
Proof. exact (@lem4872151 A h1 (@lem4871159 A)). Qed.
Lemma lem4872153 {A : Type'} (h1 : term19 A) : (term19 A) = False.
Proof. exact (prop_ext (fun h2 : term19 A => @lem4872152 A h1) (fun h2 : False => @lem4871158 A h1)). Qed.
Lemma lem4872154 {A : Type'} (h1 : term19 A) : False.
Proof. exact (EQ_MP (@lem4872153 A h1) (@lem4871158 A h1)). Qed.
Lemma lem4872155 {A : Type'} : term18 A.
Proof. exact (fun h0 : term19 A => @lem4872154 A h0). Qed.
Lemma lem4872156 {A : Type'} : term16 A.
Proof. exact (EQ_MP (@lem4871157 A) (@lem4872155 A)). Qed.
Lemma lem4872157 {A : Type'} : term15 A.
Proof. exact (EQ_MP (@lem4871153 A) (@lem4872156 A)). Qed.
