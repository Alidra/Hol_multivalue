Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FORALL_SUBSET_IMAGE_INJ_term_abbrevs.
Require Import CONJ_ASSOC_spec.
Require Import EXISTS_SUBSET_IMAGE_INJ_spec.
Require Import NOT_IMP_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Lemma lem3655230 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term0 t1 t2 t3) = (term1 t1 t2 t3)) : (term0 t1 t2 t3) = (term1 t1 t2 t3).
Proof. exact (h1). Qed.
Lemma lem3655231 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term0 t1 t2 t3) = (term1 t1 t2 t3)) : (term1 t1 t2 t3) = (term0 t1 t2 t3).
Proof. exact (SYM (@lem3655230 t1 t2 t3 h1)). Qed.
Lemma lem3655232 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term1 t1 t2 t3) = (term0 t1 t2 t3)) : (term1 t1 t2 t3) = (term0 t1 t2 t3).
Proof. exact (h1). Qed.
Lemma lem3655233 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term1 t1 t2 t3) = (term0 t1 t2 t3)) : (term0 t1 t2 t3) = (term1 t1 t2 t3).
Proof. exact (SYM (@lem3655232 t1 t2 t3 h1)). Qed.
Lemma lem3655234 (t1 : Prop) (t2 : Prop) (t3 : Prop) : ((term0 t1 t2 t3) = (term1 t1 t2 t3)) = ((term1 t1 t2 t3) = (term0 t1 t2 t3)).
Proof. exact (prop_ext (fun h1 : (term0 t1 t2 t3) = (term1 t1 t2 t3) => @lem3655231 t1 t2 t3 h1) (fun h1 : (term1 t1 t2 t3) = (term0 t1 t2 t3) => @lem3655233 t1 t2 t3 h1)). Qed.
Lemma lem3655235 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (fun_ext (fun t3 : Prop => @lem3655234 t1 t2 t3)). Qed.
Lemma lem3655236 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem3655237 (t1 : Prop) (t2 : Prop) : (term4 t1 t2) = (term5 t1 t2).
Proof. exact (MK_COMB (@lem3655236) (@lem3655235 t1 t2)). Qed.
Lemma lem3655238 (t1 : Prop) : (term6 t1) = (term7 t1).
Proof. exact (fun_ext (fun t2 : Prop => @lem3655237 t1 t2)). Qed.
Lemma lem3655239 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem3655240 (t1 : Prop) : (term8 t1) = (term9 t1).
Proof. exact (MK_COMB (@lem3655239) (@lem3655238 t1)). Qed.
Lemma lem3655241 : term10 = term11.
Proof. exact (fun_ext (fun t1 : Prop => @lem3655240 t1)). Qed.
Lemma lem3655242 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem3655243 : term12 = term13.
Proof. exact (MK_COMB (@lem3655242) (@lem3655241)). Qed.
Lemma lem3655244 : term13.
Proof. exact (EQ_MP (@lem3655243) (@lem512)). Qed.
Lemma lem3655245 (t1 : Prop) : term14 t1.
Proof. exact (@lem3655244 t1). Qed.
Lemma lem3655246 (t1 : Prop) : (term14 t1) = (term9 t1).
Proof. exact (eq_refl (term14 t1)). Qed.
Lemma lem3655247 (t1 : Prop) : term9 t1.
Proof. exact (EQ_MP (@lem3655246 t1) (@lem3655245 t1)). Qed.
Lemma lem3655248 (t1 : Prop) (t2 : Prop) : term15 t1 t2.
Proof. exact (@lem3655247 t1 t2). Qed.
Lemma lem3655249 (t1 : Prop) (t2 : Prop) : (term15 t1 t2) = (term5 t1 t2).
Proof. exact (eq_refl (term15 t1 t2)). Qed.
Lemma lem3655250 (t1 : Prop) (t2 : Prop) : term5 t1 t2.
Proof. exact (EQ_MP (@lem3655249 t1 t2) (@lem3655248 t1 t2)). Qed.
Lemma lem3655251 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term16 t1 t2 t3.
Proof. exact (@lem3655250 t1 t2 t3). Qed.
Lemma lem3655252 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term16 t1 t2 t3) = ((term1 t1 t2 t3) = (term0 t1 t2 t3)).
Proof. exact (eq_refl (term16 t1 t2 t3)). Qed.
Lemma lem3655254 {_93490 _93497 : Type'} (P : type686 _93497) : term17 _93490 _93497 P.
Proof. exact (@lem3655226 _93490 _93497 P). Qed.
Lemma lem3655255 {_93490 _93497 : Type'} (P : type686 _93497) : (term17 _93490 _93497 P) = (term18 _93490 _93497 P).
Proof. exact (eq_refl (term17 _93490 _93497 P)). Qed.
Lemma lem3655256 {_93490 _93497 : Type'} (P : type686 _93497) : term18 _93490 _93497 P.
Proof. exact (EQ_MP (@lem3655255 _93490 _93497 P) (@lem3655254 _93490 _93497 P)). Qed.
Lemma lem3655257 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) : term19 _93490 _93497 P f.
Proof. exact (@lem3655256 _93490 _93497 P f). Qed.
Lemma lem3655258 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) : (term19 _93490 _93497 P f) = (term20 _93490 _93497 P f).
Proof. exact (eq_refl (term19 _93490 _93497 P f)). Qed.
Lemma lem3655259 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) : term20 _93490 _93497 P f.
Proof. exact (EQ_MP (@lem3655258 _93490 _93497 P f) (@lem3655257 _93490 _93497 P f)). Qed.
Lemma lem3655260 {_93490 _93497 : Type'} (P : type686 _93497) (f : _93490 -> _93497) (s : _93490 -> Prop) : term21 _93490 _93497 P f s.
Proof. exact (@lem3655259 _93490 _93497 P f s). Qed.
Lemma lem3655261 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term21 _93490 _93497 P f s) = ((term22 _93490 _93497 f s P) = (term23 _93490 _93497 s P f)).
Proof. exact (eq_refl (term21 _93490 _93497 P f s)). Qed.
Lemma lem3655263 (t1 : Prop) : term24 t1.
Proof. exact (@lem10299 t1). Qed.
Lemma lem3655264 (t1 : Prop) : (term24 t1) = (term25 t1).
Proof. exact (eq_refl (term24 t1)). Qed.
Lemma lem3655265 (t1 : Prop) : term25 t1.
Proof. exact (EQ_MP (@lem3655264 t1) (@lem3655263 t1)). Qed.
Lemma lem3655266 (t1 : Prop) (t2 : Prop) : term26 t1 t2.
Proof. exact (@lem3655265 t1 t2). Qed.
Lemma lem3655267 (t1 : Prop) (t2 : Prop) : (term26 t1 t2) = ((term27 t1 t2) = (term28 t1 t2)).
Proof. exact (eq_refl (term26 t1 t2)). Qed.
Lemma lem3655280 (p : Prop) : p = (term29 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3655281 {_93512 : Type'} (p : _93512 -> Prop) : ((term30 _93512 p) = (term31 _93512 p)) = (term32 _93512 p).
Proof. exact (@lem3655280 ((term30 _93512 p) = (term31 _93512 p))). Qed.
Lemma lem3655282 {_93512 : Type'} (p : _93512 -> Prop) : (term32 _93512 p) = ((term30 _93512 p) = (term31 _93512 p)).
Proof. exact (SYM (@lem3655281 _93512 p)). Qed.
Lemma lem3655283 {_93512 : Type'} (p : _93512 -> Prop) (h1 : term33 _93512 p) : term33 _93512 p.
Proof. exact (h1). Qed.
Lemma lem3655286 {_93512 : Type'} (p : _93512 -> Prop) (h1 : term32 _93512 p) : term32 _93512 p.
Proof. exact (h1). Qed.
Lemma lem3655287 {_93512 : Type'} (p : _93512 -> Prop) : term34 _93512 p.
Proof. exact (fun h0 : term32 _93512 p => @lem3655286 _93512 p h0). Qed.
Lemma lem3655288 {_93512 : Type'} (p : _93512 -> Prop) (h1 : term34 _93512 p) : term34 _93512 p.
Proof. exact (h1). Qed.
Lemma lem3655289 {_93512 : Type'} (p : _93512 -> Prop) (h1 : term32 _93512 p) : term32 _93512 p.
Proof. exact (h1). Qed.
Lemma lem3655290 {_93512 : Type'} (p : _93512 -> Prop) (h1 : term32 _93512 p) (h2 : term34 _93512 p) : term32 _93512 p.
Proof. exact (@lem3655288 _93512 p h2 (@lem3655289 _93512 p h1)). Qed.
Lemma lem3655291 {_93512 : Type'} (p : _93512 -> Prop) (h1 : term32 _93512 p) : term35 _93512 p.
Proof. exact (fun h0 : term34 _93512 p => @lem3655290 _93512 p h1 h0). Qed.
Lemma lem3655292 {_93512 : Type'} (p : _93512 -> Prop) (h1 : term34 _93512 p) : term34 _93512 p.
Proof. exact (h1). Qed.
Lemma lem3655293 {_93512 : Type'} (p : _93512 -> Prop) (h1 : term32 _93512 p) (h2 : term34 _93512 p) : term32 _93512 p.
Proof. exact (@lem3655291 _93512 p h1 (@lem3655292 _93512 p h2)). Qed.
Lemma lem3655294 {_93512 : Type'} (p : _93512 -> Prop) (h1 : term34 _93512 p) : term34 _93512 p.
Proof. exact (fun h0 : term32 _93512 p => @lem3655293 _93512 p h0 h1). Qed.
Lemma lem3655295 {_93512 : Type'} (p : _93512 -> Prop) : term36 _93512 p.
Proof. exact (fun h0 : term34 _93512 p => @lem3655294 _93512 p h0). Qed.
Lemma lem3655298 {_93512 : Type'} (p : _93512 -> Prop) : term34 _93512 p.
Proof. exact (@lem3655295 _93512 p (@lem3655287 _93512 p)). Qed.
Lemma lem3655299 {_93512 : Type'} (p : _93512 -> Prop) : term34 _93512 p.
Proof. exact (@lem3655298 _93512 p). Qed.
Lemma lem3655305 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3655306 {_93512 : Type'} (p : _93512 -> Prop) : (term32 _93512 p) = (term37 _93512 p).
Proof. exact (@lem3655305 (term33 _93512 p)). Qed.
Lemma lem3655308 (t : Prop) : (term38 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3655309 {_93512 : Type'} (p : _93512 -> Prop) : (term37 _93512 p) = ((term30 _93512 p) = (term31 _93512 p)).
Proof. exact (@lem3655308 ((term30 _93512 p) = (term31 _93512 p))). Qed.
Lemma lem3655310 {_93512 : Type'} (p : _93512 -> Prop) : (term32 _93512 p) = ((term30 _93512 p) = (term31 _93512 p)).
Proof. exact (TRANS (@lem3655306 _93512 p) (@lem3655309 _93512 p)). Qed.
Lemma lem3655319 {_93512 : Type'} : (term39 _93512) = (term40 _93512).
Proof. exact (fun_ext (fun p : _93512 -> Prop => @lem3655310 _93512 p)). Qed.
Lemma lem3655320 {_93512 : Type'} : (@all (_93512 -> Prop)) = (@all (_93512 -> Prop)).
Proof. exact (eq_refl (@all (_93512 -> Prop))). Qed.
Lemma lem3655329 {_93512 : Type'} : (term41 _93512) = (term42 _93512).
Proof. exact (MK_COMB (@lem3655320 _93512) (@lem3655319 _93512)). Qed.
Lemma lem3655332 {_93512 : Type'} (p : _93512 -> Prop) (t : _93512) : (term43 _93512 p t) = (term43 _93512 p t).
Proof. exact (eq_refl (term43 _93512 p t)). Qed.
Lemma lem3655333 {_93512 : Type'} (p : _93512 -> Prop) : (term44 _93512 p) = (term44 _93512 p).
Proof. exact (fun_ext (fun t : _93512 => @lem3655332 _93512 p t)). Qed.
Lemma lem3655334 {_93512 : Type'} : (@ex _93512) = (@ex _93512).
Proof. exact (eq_refl (@ex _93512)). Qed.
Lemma lem3655335 {_93512 : Type'} (p : _93512 -> Prop) : (term45 _93512 p) = (term45 _93512 p).
Proof. exact (MK_COMB (@lem3655334 _93512) (@lem3655333 _93512 p)). Qed.
Lemma lem3655336 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3655337 {_93512 : Type'} (p : _93512 -> Prop) : (term31 _93512 p) = (term31 _93512 p).
Proof. exact (MK_COMB (@lem3655336) (@lem3655335 _93512 p)). Qed.
Lemma lem3655338 {_93512 : Type'} (p : _93512 -> Prop) (t : _93512) : (p t) = (p t).
Proof. exact (eq_refl (p t)). Qed.
Lemma lem3655339 {_93512 : Type'} (p : _93512 -> Prop) : (term46 _93512 p) = (term46 _93512 p).
Proof. exact (fun_ext (fun t : _93512 => @lem3655338 _93512 p t)). Qed.
Lemma lem3655340 {_93512 : Type'} : (@all _93512) = (@all _93512).
Proof. exact (eq_refl (@all _93512)). Qed.
Lemma lem3655341 {_93512 : Type'} (p : _93512 -> Prop) : (term30 _93512 p) = (term30 _93512 p).
Proof. exact (MK_COMB (@lem3655340 _93512) (@lem3655339 _93512 p)). Qed.
Lemma lem3655342 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3655343 {_93512 : Type'} (p : _93512 -> Prop) : (term47 _93512 p) = (term47 _93512 p).
Proof. exact (MK_COMB (@lem3655342) (@lem3655341 _93512 p)). Qed.
Lemma lem3655344 {_93512 : Type'} (p : _93512 -> Prop) : ((term30 _93512 p) = (term31 _93512 p)) = ((term30 _93512 p) = (term31 _93512 p)).
Proof. exact (MK_COMB (@lem3655343 _93512 p) (@lem3655337 _93512 p)). Qed.
Lemma lem3655345 {_93512 : Type'} : (term40 _93512) = (term40 _93512).
Proof. exact (fun_ext (fun p : _93512 -> Prop => @lem3655344 _93512 p)). Qed.
Lemma lem3655346 {_93512 : Type'} : (@all (_93512 -> Prop)) = (@all (_93512 -> Prop)).
Proof. exact (eq_refl (@all (_93512 -> Prop))). Qed.
Lemma lem3655347 {_93512 : Type'} : (term42 _93512) = (term42 _93512).
Proof. exact (MK_COMB (@lem3655346 _93512) (@lem3655345 _93512)). Qed.
Lemma lem3655368 {_93512 : Type'} : (term41 _93512) = (term42 _93512).
Proof. exact (TRANS (@lem3655329 _93512) (@lem3655347 _93512)). Qed.
Lemma lem3655369 {_93512 : Type'} : (term42 _93512) = (term41 _93512).
Proof. exact (SYM (@lem3655368 _93512)). Qed.
Lemma lem3655371 (p : Prop) : p = (term29 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3655372 {_93512 : Type'} (p : _93512 -> Prop) : ((term30 _93512 p) = (term31 _93512 p)) = (term32 _93512 p).
Proof. exact (@lem3655371 ((term30 _93512 p) = (term31 _93512 p))). Qed.
Lemma lem3655373 {_93512 : Type'} (p : _93512 -> Prop) : (term32 _93512 p) = ((term30 _93512 p) = (term31 _93512 p)).
Proof. exact (SYM (@lem3655372 _93512 p)). Qed.
Lemma lem3655374 {_93512 : Type'} (p : _93512 -> Prop) (h1 : term33 _93512 p) : term33 _93512 p.
Proof. exact (h1). Qed.
Lemma lem3655376 {_93512 : Type'} (p : _93512 -> Prop) (t : _93512) : (p t) = (p t).
Proof. exact (eq_refl (p t)). Qed.
Lemma lem3655377 {_93512 : Type'} (P : _93512 -> Prop) : (term48 _93512 P) = (term45 _93512 P).
Proof. exact (@lem18392 _93512 P). Qed.
Lemma lem3655378 {_93512 : Type'} (p : _93512 -> Prop) : (term49 _93512 p) = (term50 _93512 p).
Proof. exact (@lem3655377 _93512 (term46 _93512 p)). Qed.
Lemma lem3655379 {_93512 : Type'} (p : _93512 -> Prop) (t : _93512) : (term51 _93512 p t) = (p t).
Proof. exact (eq_refl (term51 _93512 p t)). Qed.
Lemma lem3655380 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3655382 {_93512 : Type'} (p : _93512 -> Prop) (t : _93512) : (term52 _93512 p t) = (term43 _93512 p t).
Proof. exact (MK_COMB (@lem3655380) (@lem3655379 _93512 p t)). Qed.
Lemma lem3655383 {_93512 : Type'} (p : _93512 -> Prop) : (term53 _93512 p) = (term44 _93512 p).
Proof. exact (fun_ext (fun t : _93512 => @lem3655382 _93512 p t)). Qed.
Lemma lem3655384 {_93512 : Type'} : (@ex _93512) = (@ex _93512).
Proof. exact (eq_refl (@ex _93512)). Qed.
Lemma lem3655385 {_93512 : Type'} (p : _93512 -> Prop) : (term50 _93512 p) = (term45 _93512 p).
Proof. exact (MK_COMB (@lem3655384 _93512) (@lem3655383 _93512 p)). Qed.
Lemma lem3655386 {_93512 : Type'} (p : _93512 -> Prop) : (term49 _93512 p) = (term45 _93512 p).
Proof. exact (TRANS (@lem3655378 _93512 p) (@lem3655385 _93512 p)). Qed.
Lemma lem3655387 {_93512 : Type'} (p : _93512 -> Prop) : (term46 _93512 p) = (term46 _93512 p).
Proof. exact (fun_ext (fun t : _93512 => @lem3655376 _93512 p t)). Qed.
Lemma lem3655388 {_93512 : Type'} : (@all _93512) = (@all _93512).
Proof. exact (eq_refl (@all _93512)). Qed.
Lemma lem3655389 {_93512 : Type'} (p : _93512 -> Prop) : (term30 _93512 p) = (term30 _93512 p).
Proof. exact (MK_COMB (@lem3655388 _93512) (@lem3655387 _93512 p)). Qed.
Lemma lem3655390 {_93512 : Type'} (p : _93512 -> Prop) (t : _93512) : (term43 _93512 p t) = (term43 _93512 p t).
Proof. exact (eq_refl (term43 _93512 p t)). Qed.
Lemma lem3655393 {_93512 : Type'} (p : _93512 -> Prop) (t : _93512) : (term54 _93512 p t) = (p t).
Proof. exact (@lem16933 (p t)). Qed.
Lemma lem3655394 {_93512 : Type'} (P : _93512 -> Prop) : (term55 _93512 P) = (term56 _93512 P).
Proof. exact (@lem18394 _93512 P). Qed.
Lemma lem3655395 {_93512 : Type'} (p : _93512 -> Prop) : (term31 _93512 p) = (term57 _93512 p).
Proof. exact (@lem3655394 _93512 (term44 _93512 p)). Qed.
Lemma lem3655396 {_93512 : Type'} (p : _93512 -> Prop) (t : _93512) : (term58 _93512 p t) = (term43 _93512 p t).
Proof. exact (eq_refl (term58 _93512 p t)). Qed.
Lemma lem3655397 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3655398 {_93512 : Type'} (p : _93512 -> Prop) (t : _93512) : (term59 _93512 p t) = (term54 _93512 p t).
Proof. exact (MK_COMB (@lem3655397) (@lem3655396 _93512 p t)). Qed.
Lemma lem3655399 {_93512 : Type'} (p : _93512 -> Prop) (t : _93512) : (term59 _93512 p t) = (p t).
Proof. exact (TRANS (@lem3655398 _93512 p t) (@lem3655393 _93512 p t)). Qed.
Lemma lem3655400 {_93512 : Type'} (p : _93512 -> Prop) : (term60 _93512 p) = (term46 _93512 p).
Proof. exact (fun_ext (fun t : _93512 => @lem3655399 _93512 p t)). Qed.
Lemma lem3655401 {_93512 : Type'} : (@all _93512) = (@all _93512).
Proof. exact (eq_refl (@all _93512)). Qed.
Lemma lem3655402 {_93512 : Type'} (p : _93512 -> Prop) : (term57 _93512 p) = (term30 _93512 p).
Proof. exact (MK_COMB (@lem3655401 _93512) (@lem3655400 _93512 p)). Qed.
Lemma lem3655403 {_93512 : Type'} (p : _93512 -> Prop) : (term31 _93512 p) = (term30 _93512 p).
Proof. exact (TRANS (@lem3655395 _93512 p) (@lem3655402 _93512 p)). Qed.
Lemma lem3655404 {_93512 : Type'} (p : _93512 -> Prop) : (term44 _93512 p) = (term44 _93512 p).
Proof. exact (fun_ext (fun t : _93512 => @lem3655390 _93512 p t)). Qed.
Lemma lem3655405 {_93512 : Type'} : (@ex _93512) = (@ex _93512).
Proof. exact (eq_refl (@ex _93512)). Qed.
Lemma lem3655406 {_93512 : Type'} (p : _93512 -> Prop) : (term45 _93512 p) = (term45 _93512 p).
Proof. exact (MK_COMB (@lem3655405 _93512) (@lem3655404 _93512 p)). Qed.
Lemma lem3655407 {_93512 : Type'} (p : _93512 -> Prop) : (term61 _93512 p) = (term45 _93512 p).
Proof. exact (@lem16933 (term45 _93512 p)). Qed.
Lemma lem3655408 {_93512 : Type'} (p : _93512 -> Prop) : (term61 _93512 p) = (term45 _93512 p).
Proof. exact (TRANS (@lem3655407 _93512 p) (@lem3655406 _93512 p)). Qed.
Lemma lem3655409 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3655410 {_93512 : Type'} (p : _93512 -> Prop) : (term62 _93512 p) = (term63 _93512 p).
Proof. exact (MK_COMB (@lem3655409) (@lem3655386 _93512 p)). Qed.
Lemma lem3655411 {_93512 : Type'} (p : _93512 -> Prop) : (term64 _93512 p) = (term65 _93512 p).
Proof. exact (MK_COMB (@lem3655410 _93512 p) (@lem3655403 _93512 p)). Qed.
Lemma lem3655412 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3655413 {_93512 : Type'} (p : _93512 -> Prop) : (term66 _93512 p) = (term66 _93512 p).
Proof. exact (MK_COMB (@lem3655412) (@lem3655389 _93512 p)). Qed.
Lemma lem3655414 {_93512 : Type'} (p : _93512 -> Prop) : (term67 _93512 p) = (term68 _93512 p).
Proof. exact (MK_COMB (@lem3655413 _93512 p) (@lem3655408 _93512 p)). Qed.
Lemma lem3655415 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3655416 {_93512 : Type'} (p : _93512 -> Prop) : (term69 _93512 p) = (term70 _93512 p).
Proof. exact (MK_COMB (@lem3655415) (@lem3655414 _93512 p)). Qed.
Lemma lem3655417 {_93512 : Type'} (p : _93512 -> Prop) : (term71 _93512 p) = (term72 _93512 p).
Proof. exact (MK_COMB (@lem3655416 _93512 p) (@lem3655411 _93512 p)). Qed.
Lemma lem3655418 {_93512 : Type'} (p : _93512 -> Prop) : (term33 _93512 p) = (term71 _93512 p).
Proof. exact (@lem17646 (term30 _93512 p) (term31 _93512 p)). Qed.
Lemma lem3655419 {_93512 : Type'} (p : _93512 -> Prop) : (term33 _93512 p) = (term72 _93512 p).
Proof. exact (TRANS (@lem3655418 _93512 p) (@lem3655417 _93512 p)). Qed.
Lemma lem3655438 {A : Type'} (P : Prop) (Q : A -> Prop) : (term73 A P Q) = (term74 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3655439 {_93512 : Type'} (P : Prop) (Q : _93512 -> Prop) : (term73 _93512 P Q) = (term74 _93512 P Q).
Proof. exact (@lem3655438 _93512 P Q). Qed.
Lemma lem3655440 {_93512 : Type'} (p : _93512 -> Prop) : (term75 _93512 p) = (term76 _93512 p).
Proof. exact (@lem3655439 _93512 (term30 _93512 p) (term44 _93512 p)). Qed.
Lemma lem3655441 {_93512 : Type'} (p : _93512 -> Prop) (t : _93512) : (term58 _93512 p t) = (term43 _93512 p t).
Proof. exact (eq_refl (term58 _93512 p t)). Qed.
Lemma lem3655442 {_93512 : Type'} (p : _93512 -> Prop) : (term77 _93512 p) = (term44 _93512 p).
Proof. exact (fun_ext (fun t : _93512 => @lem3655441 _93512 p t)). Qed.
Lemma lem3655443 {_93512 : Type'} : (@ex _93512) = (@ex _93512).
Proof. exact (eq_refl (@ex _93512)). Qed.
Lemma lem3655444 {_93512 : Type'} (p : _93512 -> Prop) : (term78 _93512 p) = (term45 _93512 p).
Proof. exact (MK_COMB (@lem3655443 _93512) (@lem3655442 _93512 p)). Qed.
Lemma lem3655445 {_93512 : Type'} (p : _93512 -> Prop) : (term66 _93512 p) = (term66 _93512 p).
Proof. exact (eq_refl (term66 _93512 p)). Qed.
Lemma lem3655446 {_93512 : Type'} (p : _93512 -> Prop) : (term75 _93512 p) = (term68 _93512 p).
Proof. exact (MK_COMB (@lem3655445 _93512 p) (@lem3655444 _93512 p)). Qed.
Lemma lem3655447 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3655448 {_93512 : Type'} (p : _93512 -> Prop) : (term79 _93512 p) = (term80 _93512 p).
Proof. exact (MK_COMB (@lem3655447) (@lem3655446 _93512 p)). Qed.
Lemma lem3655449 {_93512 : Type'} (p : _93512 -> Prop) (t : _93512) : (term58 _93512 p t) = (term43 _93512 p t).
Proof. exact (eq_refl (term58 _93512 p t)). Qed.
Lemma lem3655450 {_93512 : Type'} (p : _93512 -> Prop) : (term66 _93512 p) = (term66 _93512 p).
Proof. exact (eq_refl (term66 _93512 p)). Qed.
Lemma lem3655451 {_93512 : Type'} (p : _93512 -> Prop) (t : _93512) : (term81 _93512 p t) = (term82 _93512 p t).
Proof. exact (MK_COMB (@lem3655450 _93512 p) (@lem3655449 _93512 p t)). Qed.
Lemma lem3655452 {_93512 : Type'} (p : _93512 -> Prop) : (term83 _93512 p) = (term84 _93512 p).
Proof. exact (fun_ext (fun t : _93512 => @lem3655451 _93512 p t)). Qed.
Lemma lem3655453 {_93512 : Type'} : (@ex _93512) = (@ex _93512).
Proof. exact (eq_refl (@ex _93512)). Qed.
Lemma lem3655454 {_93512 : Type'} (p : _93512 -> Prop) : (term76 _93512 p) = (term85 _93512 p).
Proof. exact (MK_COMB (@lem3655453 _93512) (@lem3655452 _93512 p)). Qed.
Lemma lem3655455 {_93512 : Type'} (p : _93512 -> Prop) : ((term75 _93512 p) = (term76 _93512 p)) = ((term68 _93512 p) = (term85 _93512 p)).
Proof. exact (MK_COMB (@lem3655448 _93512 p) (@lem3655454 _93512 p)). Qed.
Lemma lem3655456 {_93512 : Type'} (p : _93512 -> Prop) : (term68 _93512 p) = (term85 _93512 p).
Proof. exact (EQ_MP (@lem3655455 _93512 p) (@lem3655440 _93512 p)). Qed.
Lemma lem3655457 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3655458 {_93512 : Type'} (p : _93512 -> Prop) : (term70 _93512 p) = (term86 _93512 p).
Proof. exact (MK_COMB (@lem3655457) (@lem3655456 _93512 p)). Qed.
Lemma lem3655460 {A : Type'} (P : A -> Prop) (Q : Prop) : (term87 A P Q) = (term88 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3655461 {_93512 : Type'} (P : _93512 -> Prop) (Q : Prop) : (term87 _93512 P Q) = (term88 _93512 P Q).
Proof. exact (@lem3655460 _93512 P Q). Qed.
Lemma lem3655462 {_93512 : Type'} (p : _93512 -> Prop) : (term89 _93512 p) = (term90 _93512 p).
Proof. exact (@lem3655461 _93512 (term44 _93512 p) (term30 _93512 p)). Qed.
Lemma lem3655463 {_93512 : Type'} (p : _93512 -> Prop) (t : _93512) : (term58 _93512 p t) = (term43 _93512 p t).
Proof. exact (eq_refl (term58 _93512 p t)). Qed.
Lemma lem3655464 {_93512 : Type'} (p : _93512 -> Prop) : (term77 _93512 p) = (term44 _93512 p).
Proof. exact (fun_ext (fun t : _93512 => @lem3655463 _93512 p t)). Qed.
Lemma lem3655465 {_93512 : Type'} : (@ex _93512) = (@ex _93512).
Proof. exact (eq_refl (@ex _93512)). Qed.
Lemma lem3655466 {_93512 : Type'} (p : _93512 -> Prop) : (term78 _93512 p) = (term45 _93512 p).
Proof. exact (MK_COMB (@lem3655465 _93512) (@lem3655464 _93512 p)). Qed.
Lemma lem3655467 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3655468 {_93512 : Type'} (p : _93512 -> Prop) : (term91 _93512 p) = (term63 _93512 p).
Proof. exact (MK_COMB (@lem3655467) (@lem3655466 _93512 p)). Qed.
Lemma lem3655469 {_93512 : Type'} (p : _93512 -> Prop) : (term30 _93512 p) = (term30 _93512 p).
Proof. exact (eq_refl (term30 _93512 p)). Qed.
Lemma lem3655470 {_93512 : Type'} (p : _93512 -> Prop) : (term89 _93512 p) = (term65 _93512 p).
Proof. exact (MK_COMB (@lem3655468 _93512 p) (@lem3655469 _93512 p)). Qed.
Lemma lem3655471 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3655472 {_93512 : Type'} (p : _93512 -> Prop) : (term92 _93512 p) = (term93 _93512 p).
Proof. exact (MK_COMB (@lem3655471) (@lem3655470 _93512 p)). Qed.
Lemma lem3655473 {_93512 : Type'} (p : _93512 -> Prop) (t : _93512) : (term58 _93512 p t) = (term43 _93512 p t).
Proof. exact (eq_refl (term58 _93512 p t)). Qed.
Lemma lem3655474 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3655475 {_93512 : Type'} (p : _93512 -> Prop) (t : _93512) : (term94 _93512 p t) = (term95 _93512 p t).
Proof. exact (MK_COMB (@lem3655474) (@lem3655473 _93512 p t)). Qed.
Lemma lem3655476 {_93512 : Type'} (p : _93512 -> Prop) : (term30 _93512 p) = (term30 _93512 p).
Proof. exact (eq_refl (term30 _93512 p)). Qed.
Lemma lem3655477 {_93512 : Type'} (t : _93512) (p : _93512 -> Prop) : (term96 _93512 t p) = (term97 _93512 t p).
Proof. exact (MK_COMB (@lem3655475 _93512 p t) (@lem3655476 _93512 p)). Qed.
Lemma lem3655478 {_93512 : Type'} (p : _93512 -> Prop) : (term98 _93512 p) = (term99 _93512 p).
Proof. exact (fun_ext (fun t : _93512 => @lem3655477 _93512 t p)). Qed.
Lemma lem3655479 {_93512 : Type'} : (@ex _93512) = (@ex _93512).
Proof. exact (eq_refl (@ex _93512)). Qed.
Lemma lem3655480 {_93512 : Type'} (p : _93512 -> Prop) : (term90 _93512 p) = (term100 _93512 p).
Proof. exact (MK_COMB (@lem3655479 _93512) (@lem3655478 _93512 p)). Qed.
Lemma lem3655481 {_93512 : Type'} (p : _93512 -> Prop) : ((term89 _93512 p) = (term90 _93512 p)) = ((term65 _93512 p) = (term100 _93512 p)).
Proof. exact (MK_COMB (@lem3655472 _93512 p) (@lem3655480 _93512 p)). Qed.
Lemma lem3655482 {_93512 : Type'} (p : _93512 -> Prop) : (term65 _93512 p) = (term100 _93512 p).
Proof. exact (EQ_MP (@lem3655481 _93512 p) (@lem3655462 _93512 p)). Qed.
Lemma lem3655483 {_93512 : Type'} (p : _93512 -> Prop) : (term72 _93512 p) = (term101 _93512 p).
Proof. exact (MK_COMB (@lem3655458 _93512 p) (@lem3655482 _93512 p)). Qed.
Lemma lem3655485 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term102 A P Q) = (term103 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3655486 {_93512 : Type'} (P : _93512 -> Prop) (Q : _93512 -> Prop) : (term102 _93512 P Q) = (term103 _93512 P Q).
Proof. exact (@lem3655485 _93512 P Q). Qed.
Lemma lem3655487 {_93512 : Type'} (p : _93512 -> Prop) : (term104 _93512 p) = (term105 _93512 p).
Proof. exact (@lem3655486 _93512 (term84 _93512 p) (term99 _93512 p)). Qed.
Lemma lem3655488 {_93512 : Type'} (p : _93512 -> Prop) (t : _93512) : (term106 _93512 p t) = (term82 _93512 p t).
Proof. exact (eq_refl (term106 _93512 p t)). Qed.
Lemma lem3655489 {_93512 : Type'} (p : _93512 -> Prop) : (term107 _93512 p) = (term84 _93512 p).
Proof. exact (fun_ext (fun t : _93512 => @lem3655488 _93512 p t)). Qed.
Lemma lem3655490 {_93512 : Type'} : (@ex _93512) = (@ex _93512).
Proof. exact (eq_refl (@ex _93512)). Qed.
Lemma lem3655491 {_93512 : Type'} (p : _93512 -> Prop) : (term108 _93512 p) = (term85 _93512 p).
Proof. exact (MK_COMB (@lem3655490 _93512) (@lem3655489 _93512 p)). Qed.
Lemma lem3655492 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3655493 {_93512 : Type'} (p : _93512 -> Prop) : (term109 _93512 p) = (term86 _93512 p).
Proof. exact (MK_COMB (@lem3655492) (@lem3655491 _93512 p)). Qed.
Lemma lem3655494 {_93512 : Type'} (t : _93512) (p : _93512 -> Prop) : (term110 _93512 p t) = (term97 _93512 t p).
Proof. exact (eq_refl (term110 _93512 p t)). Qed.
Lemma lem3655495 {_93512 : Type'} (p : _93512 -> Prop) : (term111 _93512 p) = (term99 _93512 p).
Proof. exact (fun_ext (fun t : _93512 => @lem3655494 _93512 t p)). Qed.
Lemma lem3655496 {_93512 : Type'} : (@ex _93512) = (@ex _93512).
Proof. exact (eq_refl (@ex _93512)). Qed.
Lemma lem3655497 {_93512 : Type'} (p : _93512 -> Prop) : (term112 _93512 p) = (term100 _93512 p).
Proof. exact (MK_COMB (@lem3655496 _93512) (@lem3655495 _93512 p)). Qed.
Lemma lem3655498 {_93512 : Type'} (p : _93512 -> Prop) : (term104 _93512 p) = (term101 _93512 p).
Proof. exact (MK_COMB (@lem3655493 _93512 p) (@lem3655497 _93512 p)). Qed.
Lemma lem3655499 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3655500 {_93512 : Type'} (p : _93512 -> Prop) : (term113 _93512 p) = (term114 _93512 p).
Proof. exact (MK_COMB (@lem3655499) (@lem3655498 _93512 p)). Qed.
Lemma lem3655501 {_93512 : Type'} (p : _93512 -> Prop) (t : _93512) : (term106 _93512 p t) = (term82 _93512 p t).
Proof. exact (eq_refl (term106 _93512 p t)). Qed.
Lemma lem3655502 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3655503 {_93512 : Type'} (p : _93512 -> Prop) (t : _93512) : (term115 _93512 p t) = (term116 _93512 p t).
Proof. exact (MK_COMB (@lem3655502) (@lem3655501 _93512 p t)). Qed.
Lemma lem3655504 {_93512 : Type'} (t : _93512) (p : _93512 -> Prop) : (term110 _93512 p t) = (term97 _93512 t p).
Proof. exact (eq_refl (term110 _93512 p t)). Qed.
Lemma lem3655505 {_93512 : Type'} (t : _93512) (p : _93512 -> Prop) : (term117 _93512 p t) = (term118 _93512 t p).
Proof. exact (MK_COMB (@lem3655503 _93512 p t) (@lem3655504 _93512 t p)). Qed.
Lemma lem3655506 {_93512 : Type'} (p : _93512 -> Prop) : (term119 _93512 p) = (term120 _93512 p).
Proof. exact (fun_ext (fun t : _93512 => @lem3655505 _93512 t p)). Qed.
Lemma lem3655507 {_93512 : Type'} : (@ex _93512) = (@ex _93512).
Proof. exact (eq_refl (@ex _93512)). Qed.
Lemma lem3655508 {_93512 : Type'} (p : _93512 -> Prop) : (term105 _93512 p) = (term121 _93512 p).
Proof. exact (MK_COMB (@lem3655507 _93512) (@lem3655506 _93512 p)). Qed.
Lemma lem3655509 {_93512 : Type'} (p : _93512 -> Prop) : ((term104 _93512 p) = (term105 _93512 p)) = ((term101 _93512 p) = (term121 _93512 p)).
Proof. exact (MK_COMB (@lem3655500 _93512 p) (@lem3655508 _93512 p)). Qed.
Lemma lem3655510 {_93512 : Type'} (p : _93512 -> Prop) : (term101 _93512 p) = (term121 _93512 p).
Proof. exact (EQ_MP (@lem3655509 _93512 p) (@lem3655487 _93512 p)). Qed.
Lemma lem3655512 {_93512 : Type'} (p : _93512 -> Prop) : (term72 _93512 p) = (term121 _93512 p).
Proof. exact (TRANS (@lem3655483 _93512 p) (@lem3655510 _93512 p)). Qed.
Lemma lem3655513 {_93512 : Type'} (p : _93512 -> Prop) : (term33 _93512 p) = (term121 _93512 p).
Proof. exact (TRANS (@lem3655419 _93512 p) (@lem3655512 _93512 p)). Qed.
Lemma lem3655514 {_93512 : Type'} (p : _93512 -> Prop) (h1 : term33 _93512 p) : term121 _93512 p.
Proof. exact (EQ_MP (@lem3655513 _93512 p) (@lem3655374 _93512 p h1)). Qed.
Lemma lem3655515 {_93512 : Type'} (t : _93512) (p : _93512 -> Prop) (h1 : term118 _93512 t p) : term118 _93512 t p.
Proof. exact (h1). Qed.
Lemma lem3655518 {_93512 : Type'} (p : _93512 -> Prop) (t : _93512) : (p t) = (p t).
Proof. exact (eq_refl (p t)). Qed.
Lemma lem3655519 {_93512 : Type'} (p : _93512 -> Prop) : (term46 _93512 p) = (term46 _93512 p).
Proof. exact (fun_ext (fun t : _93512 => @lem3655518 _93512 p t)). Qed.
Lemma lem3655520 {_93512 : Type'} : (@all _93512) = (@all _93512).
Proof. exact (eq_refl (@all _93512)). Qed.
Lemma lem3655521 {_93512 : Type'} (p : _93512 -> Prop) : (term30 _93512 p) = (term30 _93512 p).
Proof. exact (MK_COMB (@lem3655520 _93512) (@lem3655519 _93512 p)). Qed.
Lemma lem3655528 {_93512 : Type'} (p : _93512 -> Prop) (t : _93512) : (term95 _93512 p t) = (term95 _93512 p t).
Proof. exact (eq_refl (term95 _93512 p t)). Qed.
Lemma lem3655529 {_93512 : Type'} (t : _93512) (p : _93512 -> Prop) : (term97 _93512 t p) = (term97 _93512 t p).
Proof. exact (MK_COMB (@lem3655528 _93512 p t) (@lem3655521 _93512 p)). Qed.
Lemma lem3655534 {_93512 : Type'} (p : _93512 -> Prop) (t : _93512) : (term43 _93512 p t) = (term43 _93512 p t).
Proof. exact (eq_refl (term43 _93512 p t)). Qed.
Lemma lem3655537 {_93512 : Type'} (p : _93512 -> Prop) (t : _93512) : (p t) = (p t).
Proof. exact (eq_refl (p t)). Qed.
Lemma lem3655538 {_93512 : Type'} (p : _93512 -> Prop) : (term46 _93512 p) = (term46 _93512 p).
Proof. exact (fun_ext (fun t : _93512 => @lem3655537 _93512 p t)). Qed.
Lemma lem3655539 {_93512 : Type'} : (@all _93512) = (@all _93512).
Proof. exact (eq_refl (@all _93512)). Qed.
Lemma lem3655540 {_93512 : Type'} (p : _93512 -> Prop) : (term30 _93512 p) = (term30 _93512 p).
Proof. exact (MK_COMB (@lem3655539 _93512) (@lem3655538 _93512 p)). Qed.
Lemma lem3655541 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3655542 {_93512 : Type'} (p : _93512 -> Prop) : (term66 _93512 p) = (term66 _93512 p).
Proof. exact (MK_COMB (@lem3655541) (@lem3655540 _93512 p)). Qed.
Lemma lem3655543 {_93512 : Type'} (p : _93512 -> Prop) (t : _93512) : (term82 _93512 p t) = (term82 _93512 p t).
Proof. exact (MK_COMB (@lem3655542 _93512 p) (@lem3655534 _93512 p t)). Qed.
Lemma lem3655544 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3655545 {_93512 : Type'} (p : _93512 -> Prop) (t : _93512) : (term116 _93512 p t) = (term116 _93512 p t).
Proof. exact (MK_COMB (@lem3655544) (@lem3655543 _93512 p t)). Qed.
Lemma lem3655546 {_93512 : Type'} (t : _93512) (p : _93512 -> Prop) : (term118 _93512 t p) = (term118 _93512 t p).
Proof. exact (MK_COMB (@lem3655545 _93512 p t) (@lem3655529 _93512 t p)). Qed.
Lemma lem3655547 {_93512 : Type'} (t : _93512) (p : _93512 -> Prop) (h1 : term118 _93512 t p) : term118 _93512 t p.
Proof. exact (EQ_MP (@lem3655546 _93512 t p) (@lem3655515 _93512 t p h1)). Qed.
Lemma lem3655548 {_93512 : Type'} (p : _93512 -> Prop) (t : _93512) (h1 : term82 _93512 p t) : term82 _93512 p t.
Proof. exact (h1). Qed.
Lemma lem3655549 {_93512 : Type'} (t : _93512) (p : _93512 -> Prop) (h1 : term97 _93512 t p) : term97 _93512 t p.
Proof. exact (h1). Qed.
Lemma lem3655551 {_93512 : Type'} (p : _93512 -> Prop) (t : _93512) (h1 : term82 _93512 p t) : term30 _93512 p.
Proof. exact (proj1 (@lem3655548 _93512 p t h1)). Qed.
Lemma lem3655552 {_93512 : Type'} (t : _93512) (p : _93512 -> Prop) (h1 : term97 _93512 t p) : term30 _93512 p.
Proof. exact (proj2 (@lem3655549 _93512 t p h1)). Qed.
Lemma lem3655555 {_93512 : Type'} (p : _93512 -> Prop) (t : _93512) : (p t) = (p t).
Proof. exact (eq_refl (p t)). Qed.
Lemma lem3655556 {_93512 : Type'} (p : _93512 -> Prop) : (term46 _93512 p) = (term46 _93512 p).
Proof. exact (fun_ext (fun t : _93512 => @lem3655555 _93512 p t)). Qed.
Lemma lem3655557 {_93512 : Type'} : (@all _93512) = (@all _93512).
Proof. exact (eq_refl (@all _93512)). Qed.
Lemma lem3655559 {_93512 : Type'} (p : _93512 -> Prop) : (term30 _93512 p) = (term30 _93512 p).
Proof. exact (MK_COMB (@lem3655557 _93512) (@lem3655556 _93512 p)). Qed.
Lemma lem3655560 {_93512 : Type'} (p : _93512 -> Prop) (t : _93512) (h1 : term82 _93512 p t) : term30 _93512 p.
Proof. exact (EQ_MP (@lem3655559 _93512 p) (@lem3655551 _93512 p t h1)). Qed.
Lemma lem3655570 {_93512 : Type'} (p : _93512 -> Prop) (t : _93512) : (p t) = (p t).
Proof. exact (eq_refl (p t)). Qed.
Lemma lem3655571 {_93512 : Type'} (p : _93512 -> Prop) : (term46 _93512 p) = (term46 _93512 p).
Proof. exact (fun_ext (fun t : _93512 => @lem3655570 _93512 p t)). Qed.
Lemma lem3655572 {_93512 : Type'} : (@all _93512) = (@all _93512).
Proof. exact (eq_refl (@all _93512)). Qed.
Lemma lem3655574 {_93512 : Type'} (p : _93512 -> Prop) : (term30 _93512 p) = (term30 _93512 p).
Proof. exact (MK_COMB (@lem3655572 _93512) (@lem3655571 _93512 p)). Qed.
Lemma lem3655575 {_93512 : Type'} (t : _93512) (p : _93512 -> Prop) (h1 : term97 _93512 t p) : term30 _93512 p.
Proof. exact (EQ_MP (@lem3655574 _93512 p) (@lem3655552 _93512 t p h1)). Qed.
Lemma lem3655576 {_93512 : Type'} (_40122 : _93512) (p : _93512 -> Prop) (t : _93512) (h1 : term82 _93512 p t) : term51 _93512 p _40122.
Proof. exact (@lem3655560 _93512 p t h1 _40122). Qed.
Lemma lem3655577 {_93512 : Type'} (p : _93512 -> Prop) (_40122 : _93512) : (term51 _93512 p _40122) = (p _40122).
Proof. exact (eq_refl (term51 _93512 p _40122)). Qed.
Lemma lem3655579 {_93512 : Type'} (_40123 : _93512) (t : _93512) (p : _93512 -> Prop) (h1 : term97 _93512 t p) : term51 _93512 p _40123.
Proof. exact (@lem3655575 _93512 t p h1 _40123). Qed.
Lemma lem3655580 {_93512 : Type'} (p : _93512 -> Prop) (_40123 : _93512) : (term51 _93512 p _40123) = (p _40123).
Proof. exact (eq_refl (term51 _93512 p _40123)). Qed.
Lemma lem3655585 {_93512 : Type'} (p : _93512 -> Prop) (t : _93512) (h1 : term82 _93512 p t) : term43 _93512 p t.
Proof. exact (proj2 (@lem3655548 _93512 p t h1)). Qed.
Lemma lem3655587 {_93512 : Type'} (t : _93512) (p : _93512 -> Prop) (h1 : term97 _93512 t p) : term43 _93512 p t.
Proof. exact (proj1 (@lem3655549 _93512 t p h1)). Qed.
Lemma lem3655591 {_93512 : Type'} (_40122 : _93512) (p : _93512 -> Prop) (t : _93512) (h1 : term82 _93512 p t) : p _40122.
Proof. exact (EQ_MP (@lem3655577 _93512 p _40122) (@lem3655576 _93512 _40122 p t h1)). Qed.
Lemma lem3655592 {_93512 : Type'} (_40122 : _93512) (p : _93512 -> Prop) (t : _93512) (h1 : term82 _93512 p t) : p _40122.
Proof. exact (@lem3655591 _93512 _40122 p t h1). Qed.
Lemma lem3655593 {_93512 : Type'} (p : _93512 -> Prop) (t : _93512) (h1 : term82 _93512 p t) : p t.
Proof. exact (@lem3655592 _93512 t p t h1). Qed.
Lemma lem3655594 {_93512 : Type'} (p : _93512 -> Prop) (t : _93512) (h1 : term82 _93512 p t) : term122 _93512 p t.
Proof. exact (fun h0 : term43 _93512 p t => @lem3655593 _93512 p t h1). Qed.
Lemma lem3655596 (p : Prop) : (term123 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3655597 {_93512 : Type'} (p : _93512 -> Prop) (t : _93512) : (term122 _93512 p t) = (p t).
Proof. exact (@lem3655596 (p t)). Qed.
Lemma lem3655598 {_93512 : Type'} (p : _93512 -> Prop) (t : _93512) (h1 : term82 _93512 p t) : p t.
Proof. exact (EQ_MP (@lem3655597 _93512 p t) (@lem3655594 _93512 p t h1)). Qed.
Lemma lem3655601 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3655603 {_93512 : Type'} (p : _93512 -> Prop) (t : _93512) : (term43 _93512 p t) = (term124 _93512 p t).
Proof. exact (@lem3655601 (p t)). Qed.
Lemma lem3655606 {_93512 : Type'} (p : _93512 -> Prop) (t : _93512) (h1 : term82 _93512 p t) : term124 _93512 p t.
Proof. exact (EQ_MP (@lem3655603 _93512 p t) (@lem3655585 _93512 p t h1)). Qed.
Lemma lem3655609 {_93512 : Type'} (p : _93512 -> Prop) (t : _93512) (h1 : term82 _93512 p t) : False.
Proof. exact (@lem3655606 _93512 p t h1 (@lem3655598 _93512 p t h1)). Qed.
Lemma lem3655610 {_93512 : Type'} (p : _93512 -> Prop) (t : _93512) (h1 : term82 _93512 p t) : term125.
Proof. exact (fun h0 : ~ False => @lem3655609 _93512 p t h1). Qed.
Lemma lem3655612 (p : Prop) : (term123 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3655613 : term125 = False.
Proof. exact (@lem3655612 False). Qed.
Lemma lem3655614 {_93512 : Type'} (p : _93512 -> Prop) (t : _93512) (h1 : term82 _93512 p t) : False.
Proof. exact (EQ_MP (@lem3655613) (@lem3655610 _93512 p t h1)). Qed.
Lemma lem3655616 {_93512 : Type'} (_40123 : _93512) (t : _93512) (p : _93512 -> Prop) (h1 : term97 _93512 t p) : p _40123.
Proof. exact (EQ_MP (@lem3655580 _93512 p _40123) (@lem3655579 _93512 _40123 t p h1)). Qed.
Lemma lem3655617 {_93512 : Type'} (_40123 : _93512) (t : _93512) (p : _93512 -> Prop) (h1 : term97 _93512 t p) : p _40123.
Proof. exact (@lem3655616 _93512 _40123 t p h1). Qed.
Lemma lem3655618 {_93512 : Type'} (t : _93512) (p : _93512 -> Prop) (h1 : term97 _93512 t p) : p t.
Proof. exact (@lem3655617 _93512 t t p h1). Qed.
Lemma lem3655619 {_93512 : Type'} (t : _93512) (p : _93512 -> Prop) (h1 : term97 _93512 t p) : term122 _93512 p t.
Proof. exact (fun h0 : term43 _93512 p t => @lem3655618 _93512 t p h1). Qed.
Lemma lem3655621 (p : Prop) : (term123 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3655622 {_93512 : Type'} (p : _93512 -> Prop) (t : _93512) : (term122 _93512 p t) = (p t).
Proof. exact (@lem3655621 (p t)). Qed.
Lemma lem3655623 {_93512 : Type'} (t : _93512) (p : _93512 -> Prop) (h1 : term97 _93512 t p) : p t.
Proof. exact (EQ_MP (@lem3655622 _93512 p t) (@lem3655619 _93512 t p h1)). Qed.
Lemma lem3655626 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3655628 {_93512 : Type'} (p : _93512 -> Prop) (t : _93512) : (term43 _93512 p t) = (term124 _93512 p t).
Proof. exact (@lem3655626 (p t)). Qed.
Lemma lem3655631 {_93512 : Type'} (t : _93512) (p : _93512 -> Prop) (h1 : term97 _93512 t p) : term124 _93512 p t.
Proof. exact (EQ_MP (@lem3655628 _93512 p t) (@lem3655587 _93512 t p h1)). Qed.
Lemma lem3655634 {_93512 : Type'} (t : _93512) (p : _93512 -> Prop) (h1 : term97 _93512 t p) : False.
Proof. exact (@lem3655631 _93512 t p h1 (@lem3655623 _93512 t p h1)). Qed.
Lemma lem3655635 {_93512 : Type'} (t : _93512) (p : _93512 -> Prop) (h1 : term97 _93512 t p) : term125.
Proof. exact (fun h0 : ~ False => @lem3655634 _93512 t p h1). Qed.
Lemma lem3655637 (p : Prop) : (term123 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3655638 : term125 = False.
Proof. exact (@lem3655637 False). Qed.
Lemma lem3655639 {_93512 : Type'} (t : _93512) (p : _93512 -> Prop) (h1 : term97 _93512 t p) : False.
Proof. exact (EQ_MP (@lem3655638) (@lem3655635 _93512 t p h1)). Qed.
Lemma lem3655640 {_93512 : Type'} (t : _93512) (p : _93512 -> Prop) (h1 : term118 _93512 t p) : False.
Proof. exact (or_elim (@lem3655547 _93512 t p h1) (fun h0 : term82 _93512 p t => @lem3655614 _93512 p t h0) (fun h0 : term97 _93512 t p => @lem3655639 _93512 t p h0)). Qed.
Lemma lem3655641 {_93512 : Type'} (t : _93512) (p : _93512 -> Prop) (h1 : term118 _93512 t p) : (term118 _93512 t p) = False.
Proof. exact (prop_ext (fun h2 : term118 _93512 t p => @lem3655640 _93512 t p h1) (fun h2 : False => @lem3655547 _93512 t p h1)). Qed.
Lemma lem3655642 {_93512 : Type'} (t : _93512) (p : _93512 -> Prop) (h1 : term118 _93512 t p) : False.
Proof. exact (EQ_MP (@lem3655641 _93512 t p h1) (@lem3655547 _93512 t p h1)). Qed.
Lemma lem3655643 {_93512 : Type'} (p : _93512 -> Prop) (h1 : term33 _93512 p) : False.
Proof. exact (ex_elim (@lem3655514 _93512 p h1) (fun t : _93512 => fun h0 : term120 _93512 p t => @lem3655642 _93512 t p h0)). Qed.
Lemma lem3655644 {_93512 : Type'} (p : _93512 -> Prop) (h1 : term33 _93512 p) : (term33 _93512 p) = False.
Proof. exact (prop_ext (fun h2 : term33 _93512 p => @lem3655643 _93512 p h1) (fun h2 : False => @lem3655374 _93512 p h1)). Qed.
Lemma lem3655645 {_93512 : Type'} (p : _93512 -> Prop) (h1 : term33 _93512 p) : False.
Proof. exact (EQ_MP (@lem3655644 _93512 p h1) (@lem3655374 _93512 p h1)). Qed.
Lemma lem3655646 {_93512 : Type'} (p : _93512 -> Prop) : term32 _93512 p.
Proof. exact (fun h0 : term33 _93512 p => @lem3655645 _93512 p h0). Qed.
Lemma lem3655647 {_93512 : Type'} (p : _93512 -> Prop) : (term30 _93512 p) = (term31 _93512 p).
Proof. exact (EQ_MP (@lem3655373 _93512 p) (@lem3655646 _93512 p)). Qed.
Lemma lem3655652 {_93512 : Type'} : term42 _93512.
Proof. exact (fun p : _93512 -> Prop => @lem3655647 _93512 p). Qed.
Lemma lem3655653 {_93512 : Type'} : term41 _93512.
Proof. exact (EQ_MP (@lem3655369 _93512) (@lem3655652 _93512)). Qed.
Lemma lem3655654 {_93512 : Type'} (p : _93512 -> Prop) : term126 _93512 p.
Proof. exact (@lem3655653 _93512 p). Qed.
Lemma lem3655655 {_93512 : Type'} (p : _93512 -> Prop) : (term126 _93512 p) = (term32 _93512 p).
Proof. exact (eq_refl (term126 _93512 p)). Qed.
Lemma lem3655656 {_93512 : Type'} (p : _93512 -> Prop) : term32 _93512 p.
Proof. exact (EQ_MP (@lem3655655 _93512 p) (@lem3655654 _93512 p)). Qed.
Lemma lem3655658 {_93512 : Type'} (p : _93512 -> Prop) : term32 _93512 p.
Proof. exact (@lem3655299 _93512 p (@lem3655656 _93512 p)). Qed.
Lemma lem3655659 {_93512 : Type'} (p : _93512 -> Prop) (h1 : term33 _93512 p) : False.
Proof. exact (@lem3655658 _93512 p (@lem3655283 _93512 p h1)). Qed.
Lemma lem3655660 {_93512 : Type'} (p : _93512 -> Prop) (h1 : term33 _93512 p) : (term33 _93512 p) = False.
Proof. exact (prop_ext (fun h2 : term33 _93512 p => @lem3655659 _93512 p h1) (fun h2 : False => @lem3655283 _93512 p h1)). Qed.
Lemma lem3655661 {_93512 : Type'} (p : _93512 -> Prop) (h1 : term33 _93512 p) : False.
Proof. exact (EQ_MP (@lem3655660 _93512 p h1) (@lem3655283 _93512 p h1)). Qed.
Lemma lem3655662 {_93512 : Type'} (p : _93512 -> Prop) : term32 _93512 p.
Proof. exact (fun h0 : term33 _93512 p => @lem3655661 _93512 p h0). Qed.
Lemma lem3655671 {_93512 : Type'} (p : _93512 -> Prop) : (term30 _93512 p) = (term31 _93512 p).
Proof. exact (EQ_MP (@lem3655282 _93512 p) (@lem3655662 _93512 p)). Qed.
Lemma lem3655672 {_93585 : Type'} (p : type686 _93585) : (term127 _93585 p) = (term128 _93585 p).
Proof. exact (@lem3655671 (_93585 -> Prop) p). Qed.
Lemma lem3655673 {_93578 _93585 : Type'} (f : _93578 -> _93585) (s : _93578 -> Prop) (P : type686 _93585) : (term129 _93578 _93585 f s P) = (term130 _93578 _93585 f s P).
Proof. exact (@lem3655672 _93585 (term131 _93578 _93585 f s P)). Qed.
Lemma lem3655674 {_93578 _93585 : Type'} (f : _93578 -> _93585) (s : _93578 -> Prop) (P : type686 _93585) (t : _93585 -> Prop) : (term132 _93578 _93585 f s P t) = (term133 _93578 _93585 f s P t).
Proof. exact (eq_refl (term132 _93578 _93585 f s P t)). Qed.
Lemma lem3655675 {_93578 _93585 : Type'} (f : _93578 -> _93585) (s : _93578 -> Prop) (P : type686 _93585) : (term134 _93578 _93585 f s P) = (term131 _93578 _93585 f s P).
Proof. exact (fun_ext (fun t : _93585 -> Prop => @lem3655674 _93578 _93585 f s P t)). Qed.
Lemma lem3655676 {_93585 : Type'} : (@all (_93585 -> Prop)) = (@all (_93585 -> Prop)).
Proof. exact (eq_refl (@all (_93585 -> Prop))). Qed.
Lemma lem3655677 {_93578 _93585 : Type'} (f : _93578 -> _93585) (s : _93578 -> Prop) (P : type686 _93585) : (term129 _93578 _93585 f s P) = (term135 _93578 _93585 f s P).
Proof. exact (MK_COMB (@lem3655676 _93585) (@lem3655675 _93578 _93585 f s P)). Qed.
Lemma lem3655678 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3655679 {_93578 _93585 : Type'} (f : _93578 -> _93585) (s : _93578 -> Prop) (P : type686 _93585) : (term136 _93578 _93585 f s P) = (term137 _93578 _93585 f s P).
Proof. exact (MK_COMB (@lem3655678) (@lem3655677 _93578 _93585 f s P)). Qed.
Lemma lem3655680 {_93578 _93585 : Type'} (f : _93578 -> _93585) (s : _93578 -> Prop) (P : type686 _93585) (t : _93585 -> Prop) : (term132 _93578 _93585 f s P t) = (term133 _93578 _93585 f s P t).
Proof. exact (eq_refl (term132 _93578 _93585 f s P t)). Qed.
Lemma lem3655681 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3655682 {_93578 _93585 : Type'} (f : _93578 -> _93585) (s : _93578 -> Prop) (P : type686 _93585) (t : _93585 -> Prop) : (term138 _93578 _93585 f s P t) = (term139 _93578 _93585 f s P t).
Proof. exact (MK_COMB (@lem3655681) (@lem3655680 _93578 _93585 f s P t)). Qed.
Lemma lem3655683 {_93578 _93585 : Type'} (f : _93578 -> _93585) (s : _93578 -> Prop) (P : type686 _93585) : (term140 _93578 _93585 f s P) = (term141 _93578 _93585 f s P).
Proof. exact (fun_ext (fun t : _93585 -> Prop => @lem3655682 _93578 _93585 f s P t)). Qed.
Lemma lem3655684 {_93585 : Type'} : (@ex (_93585 -> Prop)) = (@ex (_93585 -> Prop)).
Proof. exact (eq_refl (@ex (_93585 -> Prop))). Qed.
Lemma lem3655685 {_93578 _93585 : Type'} (f : _93578 -> _93585) (s : _93578 -> Prop) (P : type686 _93585) : (term142 _93578 _93585 f s P) = (term143 _93578 _93585 f s P).
Proof. exact (MK_COMB (@lem3655684 _93585) (@lem3655683 _93578 _93585 f s P)). Qed.
Lemma lem3655686 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3655687 {_93578 _93585 : Type'} (f : _93578 -> _93585) (s : _93578 -> Prop) (P : type686 _93585) : (term130 _93578 _93585 f s P) = (term144 _93578 _93585 f s P).
Proof. exact (MK_COMB (@lem3655686) (@lem3655685 _93578 _93585 f s P)). Qed.
Lemma lem3655688 {_93578 _93585 : Type'} (f : _93578 -> _93585) (s : _93578 -> Prop) (P : type686 _93585) : ((term129 _93578 _93585 f s P) = (term130 _93578 _93585 f s P)) = ((term135 _93578 _93585 f s P) = (term144 _93578 _93585 f s P)).
Proof. exact (MK_COMB (@lem3655679 _93578 _93585 f s P) (@lem3655687 _93578 _93585 f s P)). Qed.
Lemma lem3655689 {_93578 _93585 : Type'} (f : _93578 -> _93585) (s : _93578 -> Prop) (P : type686 _93585) : (term135 _93578 _93585 f s P) = (term144 _93578 _93585 f s P).
Proof. exact (EQ_MP (@lem3655688 _93578 _93585 f s P) (@lem3655673 _93578 _93585 f s P)). Qed.
Lemma lem3655690 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3655691 {_93578 _93585 : Type'} (f : _93578 -> _93585) (s : _93578 -> Prop) (P : type686 _93585) : (term137 _93578 _93585 f s P) = (term145 _93578 _93585 f s P).
Proof. exact (MK_COMB (@lem3655690) (@lem3655689 _93578 _93585 f s P)). Qed.
Lemma lem3655697 {_93512 : Type'} (p : _93512 -> Prop) : (term30 _93512 p) = (term31 _93512 p).
Proof. exact (EQ_MP (@lem3655282 _93512 p) (@lem3655662 _93512 p)). Qed.
Lemma lem3655698 {_93578 : Type'} (p : type686 _93578) : (term127 _93578 p) = (term128 _93578 p).
Proof. exact (@lem3655697 (_93578 -> Prop) p). Qed.
Lemma lem3655699 {_93578 _93585 : Type'} (s : _93578 -> Prop) (P : type686 _93585) (f : _93578 -> _93585) : (term146 _93578 _93585 s P f) = (term147 _93578 _93585 s P f).
Proof. exact (@lem3655698 _93578 (term148 _93578 _93585 s P f)). Qed.
Lemma lem3655700 {_93578 _93585 : Type'} (s : _93578 -> Prop) (P : type686 _93585) (f : _93578 -> _93585) (t : _93578 -> Prop) : (term149 _93578 _93585 s P f t) = (term150 _93578 _93585 s P f t).
Proof. exact (eq_refl (term149 _93578 _93585 s P f t)). Qed.
Lemma lem3655701 {_93578 _93585 : Type'} (s : _93578 -> Prop) (P : type686 _93585) (f : _93578 -> _93585) : (term151 _93578 _93585 s P f) = (term148 _93578 _93585 s P f).
Proof. exact (fun_ext (fun t : _93578 -> Prop => @lem3655700 _93578 _93585 s P f t)). Qed.
Lemma lem3655702 {_93578 : Type'} : (@all (_93578 -> Prop)) = (@all (_93578 -> Prop)).
Proof. exact (eq_refl (@all (_93578 -> Prop))). Qed.
Lemma lem3655703 {_93578 _93585 : Type'} (s : _93578 -> Prop) (P : type686 _93585) (f : _93578 -> _93585) : (term146 _93578 _93585 s P f) = (term152 _93578 _93585 s P f).
Proof. exact (MK_COMB (@lem3655702 _93578) (@lem3655701 _93578 _93585 s P f)). Qed.
Lemma lem3655704 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3655705 {_93578 _93585 : Type'} (s : _93578 -> Prop) (P : type686 _93585) (f : _93578 -> _93585) : (term153 _93578 _93585 s P f) = (term154 _93578 _93585 s P f).
Proof. exact (MK_COMB (@lem3655704) (@lem3655703 _93578 _93585 s P f)). Qed.
Lemma lem3655706 {_93578 _93585 : Type'} (s : _93578 -> Prop) (P : type686 _93585) (f : _93578 -> _93585) (t : _93578 -> Prop) : (term149 _93578 _93585 s P f t) = (term150 _93578 _93585 s P f t).
Proof. exact (eq_refl (term149 _93578 _93585 s P f t)). Qed.
Lemma lem3655707 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3655708 {_93578 _93585 : Type'} (s : _93578 -> Prop) (P : type686 _93585) (f : _93578 -> _93585) (t : _93578 -> Prop) : (term155 _93578 _93585 s P f t) = (term156 _93578 _93585 s P f t).
Proof. exact (MK_COMB (@lem3655707) (@lem3655706 _93578 _93585 s P f t)). Qed.
Lemma lem3655709 {_93578 _93585 : Type'} (s : _93578 -> Prop) (P : type686 _93585) (f : _93578 -> _93585) : (term157 _93578 _93585 s P f) = (term158 _93578 _93585 s P f).
Proof. exact (fun_ext (fun t : _93578 -> Prop => @lem3655708 _93578 _93585 s P f t)). Qed.
Lemma lem3655710 {_93578 : Type'} : (@ex (_93578 -> Prop)) = (@ex (_93578 -> Prop)).
Proof. exact (eq_refl (@ex (_93578 -> Prop))). Qed.
Lemma lem3655711 {_93578 _93585 : Type'} (s : _93578 -> Prop) (P : type686 _93585) (f : _93578 -> _93585) : (term159 _93578 _93585 s P f) = (term160 _93578 _93585 s P f).
Proof. exact (MK_COMB (@lem3655710 _93578) (@lem3655709 _93578 _93585 s P f)). Qed.
Lemma lem3655712 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3655713 {_93578 _93585 : Type'} (s : _93578 -> Prop) (P : type686 _93585) (f : _93578 -> _93585) : (term147 _93578 _93585 s P f) = (term161 _93578 _93585 s P f).
Proof. exact (MK_COMB (@lem3655712) (@lem3655711 _93578 _93585 s P f)). Qed.
Lemma lem3655714 {_93578 _93585 : Type'} (s : _93578 -> Prop) (P : type686 _93585) (f : _93578 -> _93585) : ((term146 _93578 _93585 s P f) = (term147 _93578 _93585 s P f)) = ((term152 _93578 _93585 s P f) = (term161 _93578 _93585 s P f)).
Proof. exact (MK_COMB (@lem3655705 _93578 _93585 s P f) (@lem3655713 _93578 _93585 s P f)). Qed.
Lemma lem3655715 {_93578 _93585 : Type'} (s : _93578 -> Prop) (P : type686 _93585) (f : _93578 -> _93585) : (term152 _93578 _93585 s P f) = (term161 _93578 _93585 s P f).
Proof. exact (EQ_MP (@lem3655714 _93578 _93585 s P f) (@lem3655699 _93578 _93585 s P f)). Qed.
Lemma lem3655716 {_93578 _93585 : Type'} (s : _93578 -> Prop) (P : type686 _93585) (f : _93578 -> _93585) : ((term135 _93578 _93585 f s P) = (term152 _93578 _93585 s P f)) = ((term144 _93578 _93585 f s P) = (term161 _93578 _93585 s P f)).
Proof. exact (MK_COMB (@lem3655691 _93578 _93585 f s P) (@lem3655715 _93578 _93585 s P f)). Qed.
Lemma lem3655717 {_93578 _93585 : Type'} (s : _93578 -> Prop) (P : type686 _93585) (f : _93578 -> _93585) : ((term144 _93578 _93585 f s P) = (term161 _93578 _93585 s P f)) = ((term135 _93578 _93585 f s P) = (term152 _93578 _93585 s P f)).
Proof. exact (SYM (@lem3655716 _93578 _93585 s P f)). Qed.
Lemma lem3655725 (t1 : Prop) (t2 : Prop) : (term27 t1 t2) = (term28 t1 t2).
Proof. exact (EQ_MP (@lem3655267 t1 t2) (@lem3655266 t1 t2)). Qed.
Lemma lem3655726 {_93578 _93585 : Type'} (f : _93578 -> _93585) (s : _93578 -> Prop) (P : type686 _93585) (t : _93585 -> Prop) : (term139 _93578 _93585 f s P t) = (term162 _93578 _93585 f s P t).
Proof. exact (@lem3655725 (term163 _93578 _93585 t f s) (P t)). Qed.
Lemma lem3655729 {_93578 _93585 : Type'} (f : _93578 -> _93585) (s : _93578 -> Prop) (P : type686 _93585) : (term141 _93578 _93585 f s P) = (term164 _93578 _93585 f s P).
Proof. exact (fun_ext (fun t : _93585 -> Prop => @lem3655726 _93578 _93585 f s P t)). Qed.
Lemma lem3655730 {_93585 : Type'} : (@ex (_93585 -> Prop)) = (@ex (_93585 -> Prop)).
Proof. exact (eq_refl (@ex (_93585 -> Prop))). Qed.
Lemma lem3655731 {_93578 _93585 : Type'} (f : _93578 -> _93585) (s : _93578 -> Prop) (P : type686 _93585) : (term143 _93578 _93585 f s P) = (term165 _93578 _93585 f s P).
Proof. exact (MK_COMB (@lem3655730 _93585) (@lem3655729 _93578 _93585 f s P)). Qed.
Lemma lem3655733 {_93490 _93497 : Type'} (s : _93490 -> Prop) (P : type686 _93497) (f : _93490 -> _93497) : (term22 _93490 _93497 f s P) = (term23 _93490 _93497 s P f).
Proof. exact (EQ_MP (@lem3655261 _93490 _93497 s P f) (@lem3655260 _93490 _93497 P f s)). Qed.
Lemma lem3655734 {_93578 _93585 : Type'} (s : _93578 -> Prop) (P : type686 _93585) (f : _93578 -> _93585) : (term22 _93578 _93585 f s P) = (term23 _93578 _93585 s P f).
Proof. exact (@lem3655733 _93578 _93585 s P f). Qed.
Lemma lem3655735 {_93578 _93585 : Type'} (s : _93578 -> Prop) (P : type686 _93585) (f : _93578 -> _93585) : (term166 _93578 _93585 f s P) = (term167 _93578 _93585 s P f).
Proof. exact (@lem3655734 _93578 _93585 s (term168 _93585 P) f). Qed.
Lemma lem3655736 {_93585 : Type'} (P : type686 _93585) (t : _93585 -> Prop) : (term169 _93585 P t) = (term170 _93585 P t).
Proof. exact (eq_refl (term169 _93585 P t)). Qed.
Lemma lem3655737 {_93578 _93585 : Type'} (t : _93585 -> Prop) (f : _93578 -> _93585) (s : _93578 -> Prop) : (term171 _93578 _93585 t f s) = (term171 _93578 _93585 t f s).
Proof. exact (eq_refl (term171 _93578 _93585 t f s)). Qed.
Lemma lem3655738 {_93578 _93585 : Type'} (f : _93578 -> _93585) (s : _93578 -> Prop) (P : type686 _93585) (t : _93585 -> Prop) : (term172 _93578 _93585 f s P t) = (term162 _93578 _93585 f s P t).
Proof. exact (MK_COMB (@lem3655737 _93578 _93585 t f s) (@lem3655736 _93585 P t)). Qed.
Lemma lem3655739 {_93578 _93585 : Type'} (f : _93578 -> _93585) (s : _93578 -> Prop) (P : type686 _93585) : (term173 _93578 _93585 f s P) = (term164 _93578 _93585 f s P).
Proof. exact (fun_ext (fun t : _93585 -> Prop => @lem3655738 _93578 _93585 f s P t)). Qed.
Lemma lem3655740 {_93585 : Type'} : (@ex (_93585 -> Prop)) = (@ex (_93585 -> Prop)).
Proof. exact (eq_refl (@ex (_93585 -> Prop))). Qed.
Lemma lem3655741 {_93578 _93585 : Type'} (f : _93578 -> _93585) (s : _93578 -> Prop) (P : type686 _93585) : (term166 _93578 _93585 f s P) = (term165 _93578 _93585 f s P).
Proof. exact (MK_COMB (@lem3655740 _93585) (@lem3655739 _93578 _93585 f s P)). Qed.
Lemma lem3655742 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3655743 {_93578 _93585 : Type'} (f : _93578 -> _93585) (s : _93578 -> Prop) (P : type686 _93585) : (term174 _93578 _93585 f s P) = (term175 _93578 _93585 f s P).
Proof. exact (MK_COMB (@lem3655742) (@lem3655741 _93578 _93585 f s P)). Qed.
Lemma lem3655744 {_93578 _93585 : Type'} (P : type686 _93585) (f : _93578 -> _93585) (t : _93578 -> Prop) : (term176 _93578 _93585 P f t) = (term177 _93578 _93585 P f t).
Proof. exact (eq_refl (term176 _93578 _93585 P f t)). Qed.
Lemma lem3655745 {_93578 _93585 : Type'} (t : _93578 -> Prop) (f : _93578 -> _93585) : (term178 _93578 _93585 t f) = (term178 _93578 _93585 t f).
Proof. exact (eq_refl (term178 _93578 _93585 t f)). Qed.
Lemma lem3655746 {_93578 _93585 : Type'} (P : type686 _93585) (f : _93578 -> _93585) (t : _93578 -> Prop) : (term179 _93578 _93585 P f t) = (term180 _93578 _93585 P f t).
Proof. exact (MK_COMB (@lem3655745 _93578 _93585 t f) (@lem3655744 _93578 _93585 P f t)). Qed.
Lemma lem3655747 {_93578 : Type'} (t : _93578 -> Prop) (s : _93578 -> Prop) : (term181 _93578 t s) = (term181 _93578 t s).
Proof. exact (eq_refl (term181 _93578 t s)). Qed.
Lemma lem3655748 {_93578 _93585 : Type'} (s : _93578 -> Prop) (P : type686 _93585) (f : _93578 -> _93585) (t : _93578 -> Prop) : (term182 _93578 _93585 s P f t) = (term183 _93578 _93585 s P f t).
Proof. exact (MK_COMB (@lem3655747 _93578 t s) (@lem3655746 _93578 _93585 P f t)). Qed.
Lemma lem3655749 {_93578 _93585 : Type'} (s : _93578 -> Prop) (P : type686 _93585) (f : _93578 -> _93585) : (term184 _93578 _93585 s P f) = (term185 _93578 _93585 s P f).
Proof. exact (fun_ext (fun t : _93578 -> Prop => @lem3655748 _93578 _93585 s P f t)). Qed.
Lemma lem3655750 {_93578 : Type'} : (@ex (_93578 -> Prop)) = (@ex (_93578 -> Prop)).
Proof. exact (eq_refl (@ex (_93578 -> Prop))). Qed.
Lemma lem3655751 {_93578 _93585 : Type'} (s : _93578 -> Prop) (P : type686 _93585) (f : _93578 -> _93585) : (term167 _93578 _93585 s P f) = (term186 _93578 _93585 s P f).
Proof. exact (MK_COMB (@lem3655750 _93578) (@lem3655749 _93578 _93585 s P f)). Qed.
Lemma lem3655752 {_93578 _93585 : Type'} (s : _93578 -> Prop) (P : type686 _93585) (f : _93578 -> _93585) : ((term166 _93578 _93585 f s P) = (term167 _93578 _93585 s P f)) = ((term165 _93578 _93585 f s P) = (term186 _93578 _93585 s P f)).
Proof. exact (MK_COMB (@lem3655743 _93578 _93585 f s P) (@lem3655751 _93578 _93585 s P f)). Qed.
Lemma lem3655753 {_93578 _93585 : Type'} (s : _93578 -> Prop) (P : type686 _93585) (f : _93578 -> _93585) : (term165 _93578 _93585 f s P) = (term186 _93578 _93585 s P f).
Proof. exact (EQ_MP (@lem3655752 _93578 _93585 s P f) (@lem3655735 _93578 _93585 s P f)). Qed.
Lemma lem3655780 {_93578 _93585 : Type'} (s : _93578 -> Prop) (P : type686 _93585) (f : _93578 -> _93585) : (term143 _93578 _93585 f s P) = (term186 _93578 _93585 s P f).
Proof. exact (TRANS (@lem3655731 _93578 _93585 f s P) (@lem3655753 _93578 _93585 s P f)). Qed.
Lemma lem3655781 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3655782 {_93578 _93585 : Type'} (s : _93578 -> Prop) (P : type686 _93585) (f : _93578 -> _93585) : (term144 _93578 _93585 f s P) = (term187 _93578 _93585 s P f).
Proof. exact (MK_COMB (@lem3655781) (@lem3655780 _93578 _93585 s P f)). Qed.
Lemma lem3655783 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3655784 {_93578 _93585 : Type'} (s : _93578 -> Prop) (P : type686 _93585) (f : _93578 -> _93585) : (term145 _93578 _93585 f s P) = (term188 _93578 _93585 s P f).
Proof. exact (MK_COMB (@lem3655783) (@lem3655782 _93578 _93585 s P f)). Qed.
Lemma lem3655790 (t1 : Prop) (t2 : Prop) : (term27 t1 t2) = (term28 t1 t2).
Proof. exact (EQ_MP (@lem3655267 t1 t2) (@lem3655266 t1 t2)). Qed.
Lemma lem3655791 {_93578 _93585 : Type'} (s : _93578 -> Prop) (P : type686 _93585) (f : _93578 -> _93585) (t : _93578 -> Prop) : (term156 _93578 _93585 s P f t) = (term189 _93578 _93585 s P f t).
Proof. exact (@lem3655790 (term190 _93578 _93585 s t f) (term191 _93578 _93585 P f t)). Qed.
Lemma lem3655793 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term1 t1 t2 t3) = (term0 t1 t2 t3).
Proof. exact (EQ_MP (@lem3655252 t1 t2 t3) (@lem3655251 t1 t2 t3)). Qed.
Lemma lem3655794 {_93578 _93585 : Type'} (s : _93578 -> Prop) (P : type686 _93585) (f : _93578 -> _93585) (t : _93578 -> Prop) : (term189 _93578 _93585 s P f t) = (term183 _93578 _93585 s P f t).
Proof. exact (@lem3655793 (@SUBSET _93578 t s) (term192 _93578 _93585 t f) (term177 _93578 _93585 P f t)). Qed.
Lemma lem3655797 {_93578 _93585 : Type'} (s : _93578 -> Prop) (P : type686 _93585) (f : _93578 -> _93585) (t : _93578 -> Prop) : (term156 _93578 _93585 s P f t) = (term183 _93578 _93585 s P f t).
Proof. exact (TRANS (@lem3655791 _93578 _93585 s P f t) (@lem3655794 _93578 _93585 s P f t)). Qed.
Lemma lem3655818 {_93578 _93585 : Type'} (s : _93578 -> Prop) (P : type686 _93585) (f : _93578 -> _93585) : (term158 _93578 _93585 s P f) = (term185 _93578 _93585 s P f).
Proof. exact (fun_ext (fun t : _93578 -> Prop => @lem3655797 _93578 _93585 s P f t)). Qed.
Lemma lem3655819 {_93578 : Type'} : (@ex (_93578 -> Prop)) = (@ex (_93578 -> Prop)).
Proof. exact (eq_refl (@ex (_93578 -> Prop))). Qed.
Lemma lem3655820 {_93578 _93585 : Type'} (s : _93578 -> Prop) (P : type686 _93585) (f : _93578 -> _93585) : (term160 _93578 _93585 s P f) = (term186 _93578 _93585 s P f).
Proof. exact (MK_COMB (@lem3655819 _93578) (@lem3655818 _93578 _93585 s P f)). Qed.
Lemma lem3655825 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3655826 {_93578 _93585 : Type'} (s : _93578 -> Prop) (P : type686 _93585) (f : _93578 -> _93585) : (term161 _93578 _93585 s P f) = (term187 _93578 _93585 s P f).
Proof. exact (MK_COMB (@lem3655825) (@lem3655820 _93578 _93585 s P f)). Qed.
Lemma lem3655827 {_93578 _93585 : Type'} (s : _93578 -> Prop) (P : type686 _93585) (f : _93578 -> _93585) : ((term144 _93578 _93585 f s P) = (term161 _93578 _93585 s P f)) = ((term187 _93578 _93585 s P f) = (term187 _93578 _93585 s P f)).
Proof. exact (MK_COMB (@lem3655784 _93578 _93585 s P f) (@lem3655826 _93578 _93585 s P f)). Qed.
Lemma lem3655829 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3655830 (x : Prop) : (x = x) = True.
Proof. exact (@lem3655829 Prop x). Qed.
Lemma lem3655831 {_93578 _93585 : Type'} (s : _93578 -> Prop) (P : type686 _93585) (f : _93578 -> _93585) : ((term187 _93578 _93585 s P f) = (term187 _93578 _93585 s P f)) = True.
Proof. exact (@lem3655830 (term187 _93578 _93585 s P f)). Qed.
Lemma lem3655832 {_93578 _93585 : Type'} (s : _93578 -> Prop) (P : type686 _93585) (f : _93578 -> _93585) : ((term144 _93578 _93585 f s P) = (term161 _93578 _93585 s P f)) = True.
Proof. exact (TRANS (@lem3655827 _93578 _93585 s P f) (@lem3655831 _93578 _93585 s P f)). Qed.
Lemma lem3655833 {_93578 _93585 : Type'} (s : _93578 -> Prop) (P : type686 _93585) (f : _93578 -> _93585) : True = ((term144 _93578 _93585 f s P) = (term161 _93578 _93585 s P f)).
Proof. exact (SYM (@lem3655832 _93578 _93585 s P f)). Qed.
Lemma lem3655834 {_93578 _93585 : Type'} (s : _93578 -> Prop) (P : type686 _93585) (f : _93578 -> _93585) : (term144 _93578 _93585 f s P) = (term161 _93578 _93585 s P f).
Proof. exact (EQ_MP (@lem3655833 _93578 _93585 s P f) (@lem0)). Qed.
Lemma lem3655835 {_93578 _93585 : Type'} (s : _93578 -> Prop) (P : type686 _93585) (f : _93578 -> _93585) : (term135 _93578 _93585 f s P) = (term152 _93578 _93585 s P f).
Proof. exact (EQ_MP (@lem3655717 _93578 _93585 s P f) (@lem3655834 _93578 _93585 s P f)). Qed.
Lemma lem3655840 {_93578 _93585 : Type'} (P : type686 _93585) (f : _93578 -> _93585) : term193 _93578 _93585 P f.
Proof. exact (fun s : _93578 -> Prop => @lem3655835 _93578 _93585 s P f). Qed.
Lemma lem3655845 {_93578 _93585 : Type'} (P : type686 _93585) : term194 _93578 _93585 P.
Proof. exact (fun f : _93578 -> _93585 => @lem3655840 _93578 _93585 P f). Qed.
Lemma lem3655850 {_93578 _93585 : Type'} : term195 _93578 _93585.
Proof. exact (fun P : type686 _93585 => @lem3655845 _93578 _93585 P). Qed.
