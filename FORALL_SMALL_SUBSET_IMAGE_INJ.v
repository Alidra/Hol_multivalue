Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FORALL_SMALL_SUBSET_IMAGE_INJ_term_abbrevs.
Require Import CONJ_ASSOC_spec.
Require Import EXISTS_SMALL_SUBSET_IMAGE_INJ_spec.
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
Lemma lem4067243 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term0 t1 t2 t3) = (term1 t1 t2 t3)) : (term0 t1 t2 t3) = (term1 t1 t2 t3).
Proof. exact (h1). Qed.
Lemma lem4067244 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term0 t1 t2 t3) = (term1 t1 t2 t3)) : (term1 t1 t2 t3) = (term0 t1 t2 t3).
Proof. exact (SYM (@lem4067243 t1 t2 t3 h1)). Qed.
Lemma lem4067245 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term1 t1 t2 t3) = (term0 t1 t2 t3)) : (term1 t1 t2 t3) = (term0 t1 t2 t3).
Proof. exact (h1). Qed.
Lemma lem4067246 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term1 t1 t2 t3) = (term0 t1 t2 t3)) : (term0 t1 t2 t3) = (term1 t1 t2 t3).
Proof. exact (SYM (@lem4067245 t1 t2 t3 h1)). Qed.
Lemma lem4067247 (t1 : Prop) (t2 : Prop) (t3 : Prop) : ((term0 t1 t2 t3) = (term1 t1 t2 t3)) = ((term1 t1 t2 t3) = (term0 t1 t2 t3)).
Proof. exact (prop_ext (fun h1 : (term0 t1 t2 t3) = (term1 t1 t2 t3) => @lem4067244 t1 t2 t3 h1) (fun h1 : (term1 t1 t2 t3) = (term0 t1 t2 t3) => @lem4067246 t1 t2 t3 h1)). Qed.
Lemma lem4067248 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (fun_ext (fun t3 : Prop => @lem4067247 t1 t2 t3)). Qed.
Lemma lem4067249 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem4067250 (t1 : Prop) (t2 : Prop) : (term4 t1 t2) = (term5 t1 t2).
Proof. exact (MK_COMB (@lem4067249) (@lem4067248 t1 t2)). Qed.
Lemma lem4067251 (t1 : Prop) : (term6 t1) = (term7 t1).
Proof. exact (fun_ext (fun t2 : Prop => @lem4067250 t1 t2)). Qed.
Lemma lem4067252 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem4067253 (t1 : Prop) : (term8 t1) = (term9 t1).
Proof. exact (MK_COMB (@lem4067252) (@lem4067251 t1)). Qed.
Lemma lem4067254 : term10 = term11.
Proof. exact (fun_ext (fun t1 : Prop => @lem4067253 t1)). Qed.
Lemma lem4067255 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem4067256 : term12 = term13.
Proof. exact (MK_COMB (@lem4067255) (@lem4067254)). Qed.
Lemma lem4067257 : term13.
Proof. exact (EQ_MP (@lem4067256) (@lem512)). Qed.
Lemma lem4067258 (t1 : Prop) : term14 t1.
Proof. exact (@lem4067257 t1). Qed.
Lemma lem4067259 (t1 : Prop) : (term14 t1) = (term9 t1).
Proof. exact (eq_refl (term14 t1)). Qed.
Lemma lem4067260 (t1 : Prop) : term9 t1.
Proof. exact (EQ_MP (@lem4067259 t1) (@lem4067258 t1)). Qed.
Lemma lem4067261 (t1 : Prop) (t2 : Prop) : term15 t1 t2.
Proof. exact (@lem4067260 t1 t2). Qed.
Lemma lem4067262 (t1 : Prop) (t2 : Prop) : (term15 t1 t2) = (term5 t1 t2).
Proof. exact (eq_refl (term15 t1 t2)). Qed.
Lemma lem4067263 (t1 : Prop) (t2 : Prop) : term5 t1 t2.
Proof. exact (EQ_MP (@lem4067262 t1 t2) (@lem4067261 t1 t2)). Qed.
Lemma lem4067264 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term16 t1 t2 t3.
Proof. exact (@lem4067263 t1 t2 t3). Qed.
Lemma lem4067265 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term16 t1 t2 t3) = ((term1 t1 t2 t3) = (term0 t1 t2 t3)).
Proof. exact (eq_refl (term16 t1 t2 t3)). Qed.
Lemma lem4067267 {_102126 _102133 : Type'} (P : type686 _102133) : term17 _102126 _102133 P.
Proof. exact (@lem4067239 _102126 _102133 P). Qed.
Lemma lem4067268 {_102126 _102133 : Type'} (P : type686 _102133) : (term17 _102126 _102133 P) = (term18 _102126 _102133 P).
Proof. exact (eq_refl (term17 _102126 _102133 P)). Qed.
Lemma lem4067269 {_102126 _102133 : Type'} (P : type686 _102133) : term18 _102126 _102133 P.
Proof. exact (EQ_MP (@lem4067268 _102126 _102133 P) (@lem4067267 _102126 _102133 P)). Qed.
Lemma lem4067270 {_102126 _102133 : Type'} (P : type686 _102133) (f : _102126 -> _102133) : term19 _102126 _102133 P f.
Proof. exact (@lem4067269 _102126 _102133 P f). Qed.
Lemma lem4067271 {_102126 _102133 : Type'} (P : type686 _102133) (f : _102126 -> _102133) : (term19 _102126 _102133 P f) = (term20 _102126 _102133 P f).
Proof. exact (eq_refl (term19 _102126 _102133 P f)). Qed.
Lemma lem4067272 {_102126 _102133 : Type'} (P : type686 _102133) (f : _102126 -> _102133) : term20 _102126 _102133 P f.
Proof. exact (EQ_MP (@lem4067271 _102126 _102133 P f) (@lem4067270 _102126 _102133 P f)). Qed.
Lemma lem4067273 {_102126 _102133 : Type'} (P : type686 _102133) (f : _102126 -> _102133) (s : _102126 -> Prop) : term21 _102126 _102133 P f s.
Proof. exact (@lem4067272 _102126 _102133 P f s). Qed.
Lemma lem4067274 {_102126 _102133 : Type'} (s : _102126 -> Prop) (P : type686 _102133) (f : _102126 -> _102133) : (term21 _102126 _102133 P f s) = (term22 _102126 _102133 s P f).
Proof. exact (eq_refl (term21 _102126 _102133 P f s)). Qed.
Lemma lem4067275 {_102126 _102133 : Type'} (s : _102126 -> Prop) (P : type686 _102133) (f : _102126 -> _102133) : term22 _102126 _102133 s P f.
Proof. exact (EQ_MP (@lem4067274 _102126 _102133 s P f) (@lem4067273 _102126 _102133 P f s)). Qed.
Lemma lem4067276 {_102126 _102133 : Type'} (s : _102126 -> Prop) (P : type686 _102133) (f : _102126 -> _102133) (n : nat) : term23 _102126 _102133 s P f n.
Proof. exact (@lem4067275 _102126 _102133 s P f n). Qed.
Lemma lem4067277 {_102126 _102133 : Type'} (n : nat) (s : _102126 -> Prop) (P : type686 _102133) (f : _102126 -> _102133) : (term23 _102126 _102133 s P f n) = ((term24 _102126 _102133 n f s P) = (term25 _102126 _102133 n s P f)).
Proof. exact (eq_refl (term23 _102126 _102133 s P f n)). Qed.
Lemma lem4067279 (t1 : Prop) : term26 t1.
Proof. exact (@lem10299 t1). Qed.
Lemma lem4067280 (t1 : Prop) : (term26 t1) = (term27 t1).
Proof. exact (eq_refl (term26 t1)). Qed.
Lemma lem4067281 (t1 : Prop) : term27 t1.
Proof. exact (EQ_MP (@lem4067280 t1) (@lem4067279 t1)). Qed.
Lemma lem4067282 (t1 : Prop) (t2 : Prop) : term28 t1 t2.
Proof. exact (@lem4067281 t1 t2). Qed.
Lemma lem4067283 (t1 : Prop) (t2 : Prop) : (term28 t1 t2) = ((term29 t1 t2) = (term30 t1 t2)).
Proof. exact (eq_refl (term28 t1 t2)). Qed.
Lemma lem4067296 (p : Prop) : p = (term31 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4067297 {_102148 : Type'} (p : _102148 -> Prop) : ((term32 _102148 p) = (term33 _102148 p)) = (term34 _102148 p).
Proof. exact (@lem4067296 ((term32 _102148 p) = (term33 _102148 p))). Qed.
Lemma lem4067298 {_102148 : Type'} (p : _102148 -> Prop) : (term34 _102148 p) = ((term32 _102148 p) = (term33 _102148 p)).
Proof. exact (SYM (@lem4067297 _102148 p)). Qed.
Lemma lem4067299 {_102148 : Type'} (p : _102148 -> Prop) (h1 : term35 _102148 p) : term35 _102148 p.
Proof. exact (h1). Qed.
Lemma lem4067302 {_102148 : Type'} (p : _102148 -> Prop) (h1 : term34 _102148 p) : term34 _102148 p.
Proof. exact (h1). Qed.
Lemma lem4067303 {_102148 : Type'} (p : _102148 -> Prop) : term36 _102148 p.
Proof. exact (fun h0 : term34 _102148 p => @lem4067302 _102148 p h0). Qed.
Lemma lem4067304 {_102148 : Type'} (p : _102148 -> Prop) (h1 : term36 _102148 p) : term36 _102148 p.
Proof. exact (h1). Qed.
Lemma lem4067305 {_102148 : Type'} (p : _102148 -> Prop) (h1 : term34 _102148 p) : term34 _102148 p.
Proof. exact (h1). Qed.
Lemma lem4067306 {_102148 : Type'} (p : _102148 -> Prop) (h1 : term34 _102148 p) (h2 : term36 _102148 p) : term34 _102148 p.
Proof. exact (@lem4067304 _102148 p h2 (@lem4067305 _102148 p h1)). Qed.
Lemma lem4067307 {_102148 : Type'} (p : _102148 -> Prop) (h1 : term34 _102148 p) : term37 _102148 p.
Proof. exact (fun h0 : term36 _102148 p => @lem4067306 _102148 p h1 h0). Qed.
Lemma lem4067308 {_102148 : Type'} (p : _102148 -> Prop) (h1 : term36 _102148 p) : term36 _102148 p.
Proof. exact (h1). Qed.
Lemma lem4067309 {_102148 : Type'} (p : _102148 -> Prop) (h1 : term34 _102148 p) (h2 : term36 _102148 p) : term34 _102148 p.
Proof. exact (@lem4067307 _102148 p h1 (@lem4067308 _102148 p h2)). Qed.
Lemma lem4067310 {_102148 : Type'} (p : _102148 -> Prop) (h1 : term36 _102148 p) : term36 _102148 p.
Proof. exact (fun h0 : term34 _102148 p => @lem4067309 _102148 p h0 h1). Qed.
Lemma lem4067311 {_102148 : Type'} (p : _102148 -> Prop) : term38 _102148 p.
Proof. exact (fun h0 : term36 _102148 p => @lem4067310 _102148 p h0). Qed.
Lemma lem4067314 {_102148 : Type'} (p : _102148 -> Prop) : term36 _102148 p.
Proof. exact (@lem4067311 _102148 p (@lem4067303 _102148 p)). Qed.
Lemma lem4067315 {_102148 : Type'} (p : _102148 -> Prop) : term36 _102148 p.
Proof. exact (@lem4067314 _102148 p). Qed.
Lemma lem4067321 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4067322 {_102148 : Type'} (p : _102148 -> Prop) : (term34 _102148 p) = (term39 _102148 p).
Proof. exact (@lem4067321 (term35 _102148 p)). Qed.
Lemma lem4067324 (t : Prop) : (term40 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4067325 {_102148 : Type'} (p : _102148 -> Prop) : (term39 _102148 p) = ((term32 _102148 p) = (term33 _102148 p)).
Proof. exact (@lem4067324 ((term32 _102148 p) = (term33 _102148 p))). Qed.
Lemma lem4067326 {_102148 : Type'} (p : _102148 -> Prop) : (term34 _102148 p) = ((term32 _102148 p) = (term33 _102148 p)).
Proof. exact (TRANS (@lem4067322 _102148 p) (@lem4067325 _102148 p)). Qed.
Lemma lem4067335 {_102148 : Type'} : (term41 _102148) = (term42 _102148).
Proof. exact (fun_ext (fun p : _102148 -> Prop => @lem4067326 _102148 p)). Qed.
Lemma lem4067336 {_102148 : Type'} : (@all (_102148 -> Prop)) = (@all (_102148 -> Prop)).
Proof. exact (eq_refl (@all (_102148 -> Prop))). Qed.
Lemma lem4067345 {_102148 : Type'} : (term43 _102148) = (term44 _102148).
Proof. exact (MK_COMB (@lem4067336 _102148) (@lem4067335 _102148)). Qed.
Lemma lem4067348 {_102148 : Type'} (p : _102148 -> Prop) (t : _102148) : (term45 _102148 p t) = (term45 _102148 p t).
Proof. exact (eq_refl (term45 _102148 p t)). Qed.
Lemma lem4067349 {_102148 : Type'} (p : _102148 -> Prop) : (term46 _102148 p) = (term46 _102148 p).
Proof. exact (fun_ext (fun t : _102148 => @lem4067348 _102148 p t)). Qed.
Lemma lem4067350 {_102148 : Type'} : (@ex _102148) = (@ex _102148).
Proof. exact (eq_refl (@ex _102148)). Qed.
Lemma lem4067351 {_102148 : Type'} (p : _102148 -> Prop) : (term47 _102148 p) = (term47 _102148 p).
Proof. exact (MK_COMB (@lem4067350 _102148) (@lem4067349 _102148 p)). Qed.
Lemma lem4067352 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4067353 {_102148 : Type'} (p : _102148 -> Prop) : (term33 _102148 p) = (term33 _102148 p).
Proof. exact (MK_COMB (@lem4067352) (@lem4067351 _102148 p)). Qed.
Lemma lem4067354 {_102148 : Type'} (p : _102148 -> Prop) (t : _102148) : (p t) = (p t).
Proof. exact (eq_refl (p t)). Qed.
Lemma lem4067355 {_102148 : Type'} (p : _102148 -> Prop) : (term48 _102148 p) = (term48 _102148 p).
Proof. exact (fun_ext (fun t : _102148 => @lem4067354 _102148 p t)). Qed.
Lemma lem4067356 {_102148 : Type'} : (@all _102148) = (@all _102148).
Proof. exact (eq_refl (@all _102148)). Qed.
Lemma lem4067357 {_102148 : Type'} (p : _102148 -> Prop) : (term32 _102148 p) = (term32 _102148 p).
Proof. exact (MK_COMB (@lem4067356 _102148) (@lem4067355 _102148 p)). Qed.
Lemma lem4067358 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4067359 {_102148 : Type'} (p : _102148 -> Prop) : (term49 _102148 p) = (term49 _102148 p).
Proof. exact (MK_COMB (@lem4067358) (@lem4067357 _102148 p)). Qed.
Lemma lem4067360 {_102148 : Type'} (p : _102148 -> Prop) : ((term32 _102148 p) = (term33 _102148 p)) = ((term32 _102148 p) = (term33 _102148 p)).
Proof. exact (MK_COMB (@lem4067359 _102148 p) (@lem4067353 _102148 p)). Qed.
Lemma lem4067361 {_102148 : Type'} : (term42 _102148) = (term42 _102148).
Proof. exact (fun_ext (fun p : _102148 -> Prop => @lem4067360 _102148 p)). Qed.
Lemma lem4067362 {_102148 : Type'} : (@all (_102148 -> Prop)) = (@all (_102148 -> Prop)).
Proof. exact (eq_refl (@all (_102148 -> Prop))). Qed.
Lemma lem4067363 {_102148 : Type'} : (term44 _102148) = (term44 _102148).
Proof. exact (MK_COMB (@lem4067362 _102148) (@lem4067361 _102148)). Qed.
Lemma lem4067384 {_102148 : Type'} : (term43 _102148) = (term44 _102148).
Proof. exact (TRANS (@lem4067345 _102148) (@lem4067363 _102148)). Qed.
Lemma lem4067385 {_102148 : Type'} : (term44 _102148) = (term43 _102148).
Proof. exact (SYM (@lem4067384 _102148)). Qed.
Lemma lem4067387 (p : Prop) : p = (term31 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4067388 {_102148 : Type'} (p : _102148 -> Prop) : ((term32 _102148 p) = (term33 _102148 p)) = (term34 _102148 p).
Proof. exact (@lem4067387 ((term32 _102148 p) = (term33 _102148 p))). Qed.
Lemma lem4067389 {_102148 : Type'} (p : _102148 -> Prop) : (term34 _102148 p) = ((term32 _102148 p) = (term33 _102148 p)).
Proof. exact (SYM (@lem4067388 _102148 p)). Qed.
Lemma lem4067390 {_102148 : Type'} (p : _102148 -> Prop) (h1 : term35 _102148 p) : term35 _102148 p.
Proof. exact (h1). Qed.
Lemma lem4067392 {_102148 : Type'} (p : _102148 -> Prop) (t : _102148) : (p t) = (p t).
Proof. exact (eq_refl (p t)). Qed.
Lemma lem4067393 {_102148 : Type'} (P : _102148 -> Prop) : (term50 _102148 P) = (term47 _102148 P).
Proof. exact (@lem18392 _102148 P). Qed.
Lemma lem4067394 {_102148 : Type'} (p : _102148 -> Prop) : (term51 _102148 p) = (term52 _102148 p).
Proof. exact (@lem4067393 _102148 (term48 _102148 p)). Qed.
Lemma lem4067395 {_102148 : Type'} (p : _102148 -> Prop) (t : _102148) : (term53 _102148 p t) = (p t).
Proof. exact (eq_refl (term53 _102148 p t)). Qed.
Lemma lem4067396 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4067398 {_102148 : Type'} (p : _102148 -> Prop) (t : _102148) : (term54 _102148 p t) = (term45 _102148 p t).
Proof. exact (MK_COMB (@lem4067396) (@lem4067395 _102148 p t)). Qed.
Lemma lem4067399 {_102148 : Type'} (p : _102148 -> Prop) : (term55 _102148 p) = (term46 _102148 p).
Proof. exact (fun_ext (fun t : _102148 => @lem4067398 _102148 p t)). Qed.
Lemma lem4067400 {_102148 : Type'} : (@ex _102148) = (@ex _102148).
Proof. exact (eq_refl (@ex _102148)). Qed.
Lemma lem4067401 {_102148 : Type'} (p : _102148 -> Prop) : (term52 _102148 p) = (term47 _102148 p).
Proof. exact (MK_COMB (@lem4067400 _102148) (@lem4067399 _102148 p)). Qed.
Lemma lem4067402 {_102148 : Type'} (p : _102148 -> Prop) : (term51 _102148 p) = (term47 _102148 p).
Proof. exact (TRANS (@lem4067394 _102148 p) (@lem4067401 _102148 p)). Qed.
Lemma lem4067403 {_102148 : Type'} (p : _102148 -> Prop) : (term48 _102148 p) = (term48 _102148 p).
Proof. exact (fun_ext (fun t : _102148 => @lem4067392 _102148 p t)). Qed.
Lemma lem4067404 {_102148 : Type'} : (@all _102148) = (@all _102148).
Proof. exact (eq_refl (@all _102148)). Qed.
Lemma lem4067405 {_102148 : Type'} (p : _102148 -> Prop) : (term32 _102148 p) = (term32 _102148 p).
Proof. exact (MK_COMB (@lem4067404 _102148) (@lem4067403 _102148 p)). Qed.
Lemma lem4067406 {_102148 : Type'} (p : _102148 -> Prop) (t : _102148) : (term45 _102148 p t) = (term45 _102148 p t).
Proof. exact (eq_refl (term45 _102148 p t)). Qed.
Lemma lem4067409 {_102148 : Type'} (p : _102148 -> Prop) (t : _102148) : (term56 _102148 p t) = (p t).
Proof. exact (@lem16933 (p t)). Qed.
Lemma lem4067410 {_102148 : Type'} (P : _102148 -> Prop) : (term57 _102148 P) = (term58 _102148 P).
Proof. exact (@lem18394 _102148 P). Qed.
Lemma lem4067411 {_102148 : Type'} (p : _102148 -> Prop) : (term33 _102148 p) = (term59 _102148 p).
Proof. exact (@lem4067410 _102148 (term46 _102148 p)). Qed.
Lemma lem4067412 {_102148 : Type'} (p : _102148 -> Prop) (t : _102148) : (term60 _102148 p t) = (term45 _102148 p t).
Proof. exact (eq_refl (term60 _102148 p t)). Qed.
Lemma lem4067413 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4067414 {_102148 : Type'} (p : _102148 -> Prop) (t : _102148) : (term61 _102148 p t) = (term56 _102148 p t).
Proof. exact (MK_COMB (@lem4067413) (@lem4067412 _102148 p t)). Qed.
Lemma lem4067415 {_102148 : Type'} (p : _102148 -> Prop) (t : _102148) : (term61 _102148 p t) = (p t).
Proof. exact (TRANS (@lem4067414 _102148 p t) (@lem4067409 _102148 p t)). Qed.
Lemma lem4067416 {_102148 : Type'} (p : _102148 -> Prop) : (term62 _102148 p) = (term48 _102148 p).
Proof. exact (fun_ext (fun t : _102148 => @lem4067415 _102148 p t)). Qed.
Lemma lem4067417 {_102148 : Type'} : (@all _102148) = (@all _102148).
Proof. exact (eq_refl (@all _102148)). Qed.
Lemma lem4067418 {_102148 : Type'} (p : _102148 -> Prop) : (term59 _102148 p) = (term32 _102148 p).
Proof. exact (MK_COMB (@lem4067417 _102148) (@lem4067416 _102148 p)). Qed.
Lemma lem4067419 {_102148 : Type'} (p : _102148 -> Prop) : (term33 _102148 p) = (term32 _102148 p).
Proof. exact (TRANS (@lem4067411 _102148 p) (@lem4067418 _102148 p)). Qed.
Lemma lem4067420 {_102148 : Type'} (p : _102148 -> Prop) : (term46 _102148 p) = (term46 _102148 p).
Proof. exact (fun_ext (fun t : _102148 => @lem4067406 _102148 p t)). Qed.
Lemma lem4067421 {_102148 : Type'} : (@ex _102148) = (@ex _102148).
Proof. exact (eq_refl (@ex _102148)). Qed.
Lemma lem4067422 {_102148 : Type'} (p : _102148 -> Prop) : (term47 _102148 p) = (term47 _102148 p).
Proof. exact (MK_COMB (@lem4067421 _102148) (@lem4067420 _102148 p)). Qed.
Lemma lem4067423 {_102148 : Type'} (p : _102148 -> Prop) : (term63 _102148 p) = (term47 _102148 p).
Proof. exact (@lem16933 (term47 _102148 p)). Qed.
Lemma lem4067424 {_102148 : Type'} (p : _102148 -> Prop) : (term63 _102148 p) = (term47 _102148 p).
Proof. exact (TRANS (@lem4067423 _102148 p) (@lem4067422 _102148 p)). Qed.
Lemma lem4067425 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4067426 {_102148 : Type'} (p : _102148 -> Prop) : (term64 _102148 p) = (term65 _102148 p).
Proof. exact (MK_COMB (@lem4067425) (@lem4067402 _102148 p)). Qed.
Lemma lem4067427 {_102148 : Type'} (p : _102148 -> Prop) : (term66 _102148 p) = (term67 _102148 p).
Proof. exact (MK_COMB (@lem4067426 _102148 p) (@lem4067419 _102148 p)). Qed.
Lemma lem4067428 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4067429 {_102148 : Type'} (p : _102148 -> Prop) : (term68 _102148 p) = (term68 _102148 p).
Proof. exact (MK_COMB (@lem4067428) (@lem4067405 _102148 p)). Qed.
Lemma lem4067430 {_102148 : Type'} (p : _102148 -> Prop) : (term69 _102148 p) = (term70 _102148 p).
Proof. exact (MK_COMB (@lem4067429 _102148 p) (@lem4067424 _102148 p)). Qed.
Lemma lem4067431 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4067432 {_102148 : Type'} (p : _102148 -> Prop) : (term71 _102148 p) = (term72 _102148 p).
Proof. exact (MK_COMB (@lem4067431) (@lem4067430 _102148 p)). Qed.
Lemma lem4067433 {_102148 : Type'} (p : _102148 -> Prop) : (term73 _102148 p) = (term74 _102148 p).
Proof. exact (MK_COMB (@lem4067432 _102148 p) (@lem4067427 _102148 p)). Qed.
Lemma lem4067434 {_102148 : Type'} (p : _102148 -> Prop) : (term35 _102148 p) = (term73 _102148 p).
Proof. exact (@lem17646 (term32 _102148 p) (term33 _102148 p)). Qed.
Lemma lem4067435 {_102148 : Type'} (p : _102148 -> Prop) : (term35 _102148 p) = (term74 _102148 p).
Proof. exact (TRANS (@lem4067434 _102148 p) (@lem4067433 _102148 p)). Qed.
Lemma lem4067454 {A : Type'} (P : Prop) (Q : A -> Prop) : (term75 A P Q) = (term76 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4067455 {_102148 : Type'} (P : Prop) (Q : _102148 -> Prop) : (term75 _102148 P Q) = (term76 _102148 P Q).
Proof. exact (@lem4067454 _102148 P Q). Qed.
Lemma lem4067456 {_102148 : Type'} (p : _102148 -> Prop) : (term77 _102148 p) = (term78 _102148 p).
Proof. exact (@lem4067455 _102148 (term32 _102148 p) (term46 _102148 p)). Qed.
Lemma lem4067457 {_102148 : Type'} (p : _102148 -> Prop) (t : _102148) : (term60 _102148 p t) = (term45 _102148 p t).
Proof. exact (eq_refl (term60 _102148 p t)). Qed.
Lemma lem4067458 {_102148 : Type'} (p : _102148 -> Prop) : (term79 _102148 p) = (term46 _102148 p).
Proof. exact (fun_ext (fun t : _102148 => @lem4067457 _102148 p t)). Qed.
Lemma lem4067459 {_102148 : Type'} : (@ex _102148) = (@ex _102148).
Proof. exact (eq_refl (@ex _102148)). Qed.
Lemma lem4067460 {_102148 : Type'} (p : _102148 -> Prop) : (term80 _102148 p) = (term47 _102148 p).
Proof. exact (MK_COMB (@lem4067459 _102148) (@lem4067458 _102148 p)). Qed.
Lemma lem4067461 {_102148 : Type'} (p : _102148 -> Prop) : (term68 _102148 p) = (term68 _102148 p).
Proof. exact (eq_refl (term68 _102148 p)). Qed.
Lemma lem4067462 {_102148 : Type'} (p : _102148 -> Prop) : (term77 _102148 p) = (term70 _102148 p).
Proof. exact (MK_COMB (@lem4067461 _102148 p) (@lem4067460 _102148 p)). Qed.
Lemma lem4067463 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4067464 {_102148 : Type'} (p : _102148 -> Prop) : (term81 _102148 p) = (term82 _102148 p).
Proof. exact (MK_COMB (@lem4067463) (@lem4067462 _102148 p)). Qed.
Lemma lem4067465 {_102148 : Type'} (p : _102148 -> Prop) (t : _102148) : (term60 _102148 p t) = (term45 _102148 p t).
Proof. exact (eq_refl (term60 _102148 p t)). Qed.
Lemma lem4067466 {_102148 : Type'} (p : _102148 -> Prop) : (term68 _102148 p) = (term68 _102148 p).
Proof. exact (eq_refl (term68 _102148 p)). Qed.
Lemma lem4067467 {_102148 : Type'} (p : _102148 -> Prop) (t : _102148) : (term83 _102148 p t) = (term84 _102148 p t).
Proof. exact (MK_COMB (@lem4067466 _102148 p) (@lem4067465 _102148 p t)). Qed.
Lemma lem4067468 {_102148 : Type'} (p : _102148 -> Prop) : (term85 _102148 p) = (term86 _102148 p).
Proof. exact (fun_ext (fun t : _102148 => @lem4067467 _102148 p t)). Qed.
Lemma lem4067469 {_102148 : Type'} : (@ex _102148) = (@ex _102148).
Proof. exact (eq_refl (@ex _102148)). Qed.
Lemma lem4067470 {_102148 : Type'} (p : _102148 -> Prop) : (term78 _102148 p) = (term87 _102148 p).
Proof. exact (MK_COMB (@lem4067469 _102148) (@lem4067468 _102148 p)). Qed.
Lemma lem4067471 {_102148 : Type'} (p : _102148 -> Prop) : ((term77 _102148 p) = (term78 _102148 p)) = ((term70 _102148 p) = (term87 _102148 p)).
Proof. exact (MK_COMB (@lem4067464 _102148 p) (@lem4067470 _102148 p)). Qed.
Lemma lem4067472 {_102148 : Type'} (p : _102148 -> Prop) : (term70 _102148 p) = (term87 _102148 p).
Proof. exact (EQ_MP (@lem4067471 _102148 p) (@lem4067456 _102148 p)). Qed.
Lemma lem4067473 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4067474 {_102148 : Type'} (p : _102148 -> Prop) : (term72 _102148 p) = (term88 _102148 p).
Proof. exact (MK_COMB (@lem4067473) (@lem4067472 _102148 p)). Qed.
Lemma lem4067476 {A : Type'} (P : A -> Prop) (Q : Prop) : (term89 A P Q) = (term90 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4067477 {_102148 : Type'} (P : _102148 -> Prop) (Q : Prop) : (term89 _102148 P Q) = (term90 _102148 P Q).
Proof. exact (@lem4067476 _102148 P Q). Qed.
Lemma lem4067478 {_102148 : Type'} (p : _102148 -> Prop) : (term91 _102148 p) = (term92 _102148 p).
Proof. exact (@lem4067477 _102148 (term46 _102148 p) (term32 _102148 p)). Qed.
Lemma lem4067479 {_102148 : Type'} (p : _102148 -> Prop) (t : _102148) : (term60 _102148 p t) = (term45 _102148 p t).
Proof. exact (eq_refl (term60 _102148 p t)). Qed.
Lemma lem4067480 {_102148 : Type'} (p : _102148 -> Prop) : (term79 _102148 p) = (term46 _102148 p).
Proof. exact (fun_ext (fun t : _102148 => @lem4067479 _102148 p t)). Qed.
Lemma lem4067481 {_102148 : Type'} : (@ex _102148) = (@ex _102148).
Proof. exact (eq_refl (@ex _102148)). Qed.
Lemma lem4067482 {_102148 : Type'} (p : _102148 -> Prop) : (term80 _102148 p) = (term47 _102148 p).
Proof. exact (MK_COMB (@lem4067481 _102148) (@lem4067480 _102148 p)). Qed.
Lemma lem4067483 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4067484 {_102148 : Type'} (p : _102148 -> Prop) : (term93 _102148 p) = (term65 _102148 p).
Proof. exact (MK_COMB (@lem4067483) (@lem4067482 _102148 p)). Qed.
Lemma lem4067485 {_102148 : Type'} (p : _102148 -> Prop) : (term32 _102148 p) = (term32 _102148 p).
Proof. exact (eq_refl (term32 _102148 p)). Qed.
Lemma lem4067486 {_102148 : Type'} (p : _102148 -> Prop) : (term91 _102148 p) = (term67 _102148 p).
Proof. exact (MK_COMB (@lem4067484 _102148 p) (@lem4067485 _102148 p)). Qed.
Lemma lem4067487 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4067488 {_102148 : Type'} (p : _102148 -> Prop) : (term94 _102148 p) = (term95 _102148 p).
Proof. exact (MK_COMB (@lem4067487) (@lem4067486 _102148 p)). Qed.
Lemma lem4067489 {_102148 : Type'} (p : _102148 -> Prop) (t : _102148) : (term60 _102148 p t) = (term45 _102148 p t).
Proof. exact (eq_refl (term60 _102148 p t)). Qed.
Lemma lem4067490 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4067491 {_102148 : Type'} (p : _102148 -> Prop) (t : _102148) : (term96 _102148 p t) = (term97 _102148 p t).
Proof. exact (MK_COMB (@lem4067490) (@lem4067489 _102148 p t)). Qed.
Lemma lem4067492 {_102148 : Type'} (p : _102148 -> Prop) : (term32 _102148 p) = (term32 _102148 p).
Proof. exact (eq_refl (term32 _102148 p)). Qed.
Lemma lem4067493 {_102148 : Type'} (t : _102148) (p : _102148 -> Prop) : (term98 _102148 t p) = (term99 _102148 t p).
Proof. exact (MK_COMB (@lem4067491 _102148 p t) (@lem4067492 _102148 p)). Qed.
Lemma lem4067494 {_102148 : Type'} (p : _102148 -> Prop) : (term100 _102148 p) = (term101 _102148 p).
Proof. exact (fun_ext (fun t : _102148 => @lem4067493 _102148 t p)). Qed.
Lemma lem4067495 {_102148 : Type'} : (@ex _102148) = (@ex _102148).
Proof. exact (eq_refl (@ex _102148)). Qed.
Lemma lem4067496 {_102148 : Type'} (p : _102148 -> Prop) : (term92 _102148 p) = (term102 _102148 p).
Proof. exact (MK_COMB (@lem4067495 _102148) (@lem4067494 _102148 p)). Qed.
Lemma lem4067497 {_102148 : Type'} (p : _102148 -> Prop) : ((term91 _102148 p) = (term92 _102148 p)) = ((term67 _102148 p) = (term102 _102148 p)).
Proof. exact (MK_COMB (@lem4067488 _102148 p) (@lem4067496 _102148 p)). Qed.
Lemma lem4067498 {_102148 : Type'} (p : _102148 -> Prop) : (term67 _102148 p) = (term102 _102148 p).
Proof. exact (EQ_MP (@lem4067497 _102148 p) (@lem4067478 _102148 p)). Qed.
Lemma lem4067499 {_102148 : Type'} (p : _102148 -> Prop) : (term74 _102148 p) = (term103 _102148 p).
Proof. exact (MK_COMB (@lem4067474 _102148 p) (@lem4067498 _102148 p)). Qed.
Lemma lem4067501 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term104 A P Q) = (term105 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4067502 {_102148 : Type'} (P : _102148 -> Prop) (Q : _102148 -> Prop) : (term104 _102148 P Q) = (term105 _102148 P Q).
Proof. exact (@lem4067501 _102148 P Q). Qed.
Lemma lem4067503 {_102148 : Type'} (p : _102148 -> Prop) : (term106 _102148 p) = (term107 _102148 p).
Proof. exact (@lem4067502 _102148 (term86 _102148 p) (term101 _102148 p)). Qed.
Lemma lem4067504 {_102148 : Type'} (p : _102148 -> Prop) (t : _102148) : (term108 _102148 p t) = (term84 _102148 p t).
Proof. exact (eq_refl (term108 _102148 p t)). Qed.
Lemma lem4067505 {_102148 : Type'} (p : _102148 -> Prop) : (term109 _102148 p) = (term86 _102148 p).
Proof. exact (fun_ext (fun t : _102148 => @lem4067504 _102148 p t)). Qed.
Lemma lem4067506 {_102148 : Type'} : (@ex _102148) = (@ex _102148).
Proof. exact (eq_refl (@ex _102148)). Qed.
Lemma lem4067507 {_102148 : Type'} (p : _102148 -> Prop) : (term110 _102148 p) = (term87 _102148 p).
Proof. exact (MK_COMB (@lem4067506 _102148) (@lem4067505 _102148 p)). Qed.
Lemma lem4067508 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4067509 {_102148 : Type'} (p : _102148 -> Prop) : (term111 _102148 p) = (term88 _102148 p).
Proof. exact (MK_COMB (@lem4067508) (@lem4067507 _102148 p)). Qed.
Lemma lem4067510 {_102148 : Type'} (t : _102148) (p : _102148 -> Prop) : (term112 _102148 p t) = (term99 _102148 t p).
Proof. exact (eq_refl (term112 _102148 p t)). Qed.
Lemma lem4067511 {_102148 : Type'} (p : _102148 -> Prop) : (term113 _102148 p) = (term101 _102148 p).
Proof. exact (fun_ext (fun t : _102148 => @lem4067510 _102148 t p)). Qed.
Lemma lem4067512 {_102148 : Type'} : (@ex _102148) = (@ex _102148).
Proof. exact (eq_refl (@ex _102148)). Qed.
Lemma lem4067513 {_102148 : Type'} (p : _102148 -> Prop) : (term114 _102148 p) = (term102 _102148 p).
Proof. exact (MK_COMB (@lem4067512 _102148) (@lem4067511 _102148 p)). Qed.
Lemma lem4067514 {_102148 : Type'} (p : _102148 -> Prop) : (term106 _102148 p) = (term103 _102148 p).
Proof. exact (MK_COMB (@lem4067509 _102148 p) (@lem4067513 _102148 p)). Qed.
Lemma lem4067515 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4067516 {_102148 : Type'} (p : _102148 -> Prop) : (term115 _102148 p) = (term116 _102148 p).
Proof. exact (MK_COMB (@lem4067515) (@lem4067514 _102148 p)). Qed.
Lemma lem4067517 {_102148 : Type'} (p : _102148 -> Prop) (t : _102148) : (term108 _102148 p t) = (term84 _102148 p t).
Proof. exact (eq_refl (term108 _102148 p t)). Qed.
Lemma lem4067518 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4067519 {_102148 : Type'} (p : _102148 -> Prop) (t : _102148) : (term117 _102148 p t) = (term118 _102148 p t).
Proof. exact (MK_COMB (@lem4067518) (@lem4067517 _102148 p t)). Qed.
Lemma lem4067520 {_102148 : Type'} (t : _102148) (p : _102148 -> Prop) : (term112 _102148 p t) = (term99 _102148 t p).
Proof. exact (eq_refl (term112 _102148 p t)). Qed.
Lemma lem4067521 {_102148 : Type'} (t : _102148) (p : _102148 -> Prop) : (term119 _102148 p t) = (term120 _102148 t p).
Proof. exact (MK_COMB (@lem4067519 _102148 p t) (@lem4067520 _102148 t p)). Qed.
Lemma lem4067522 {_102148 : Type'} (p : _102148 -> Prop) : (term121 _102148 p) = (term122 _102148 p).
Proof. exact (fun_ext (fun t : _102148 => @lem4067521 _102148 t p)). Qed.
Lemma lem4067523 {_102148 : Type'} : (@ex _102148) = (@ex _102148).
Proof. exact (eq_refl (@ex _102148)). Qed.
Lemma lem4067524 {_102148 : Type'} (p : _102148 -> Prop) : (term107 _102148 p) = (term123 _102148 p).
Proof. exact (MK_COMB (@lem4067523 _102148) (@lem4067522 _102148 p)). Qed.
Lemma lem4067525 {_102148 : Type'} (p : _102148 -> Prop) : ((term106 _102148 p) = (term107 _102148 p)) = ((term103 _102148 p) = (term123 _102148 p)).
Proof. exact (MK_COMB (@lem4067516 _102148 p) (@lem4067524 _102148 p)). Qed.
Lemma lem4067526 {_102148 : Type'} (p : _102148 -> Prop) : (term103 _102148 p) = (term123 _102148 p).
Proof. exact (EQ_MP (@lem4067525 _102148 p) (@lem4067503 _102148 p)). Qed.
Lemma lem4067528 {_102148 : Type'} (p : _102148 -> Prop) : (term74 _102148 p) = (term123 _102148 p).
Proof. exact (TRANS (@lem4067499 _102148 p) (@lem4067526 _102148 p)). Qed.
Lemma lem4067529 {_102148 : Type'} (p : _102148 -> Prop) : (term35 _102148 p) = (term123 _102148 p).
Proof. exact (TRANS (@lem4067435 _102148 p) (@lem4067528 _102148 p)). Qed.
Lemma lem4067530 {_102148 : Type'} (p : _102148 -> Prop) (h1 : term35 _102148 p) : term123 _102148 p.
Proof. exact (EQ_MP (@lem4067529 _102148 p) (@lem4067390 _102148 p h1)). Qed.
Lemma lem4067531 {_102148 : Type'} (t : _102148) (p : _102148 -> Prop) (h1 : term120 _102148 t p) : term120 _102148 t p.
Proof. exact (h1). Qed.
Lemma lem4067534 {_102148 : Type'} (p : _102148 -> Prop) (t : _102148) : (p t) = (p t).
Proof. exact (eq_refl (p t)). Qed.
Lemma lem4067535 {_102148 : Type'} (p : _102148 -> Prop) : (term48 _102148 p) = (term48 _102148 p).
Proof. exact (fun_ext (fun t : _102148 => @lem4067534 _102148 p t)). Qed.
Lemma lem4067536 {_102148 : Type'} : (@all _102148) = (@all _102148).
Proof. exact (eq_refl (@all _102148)). Qed.
Lemma lem4067537 {_102148 : Type'} (p : _102148 -> Prop) : (term32 _102148 p) = (term32 _102148 p).
Proof. exact (MK_COMB (@lem4067536 _102148) (@lem4067535 _102148 p)). Qed.
Lemma lem4067544 {_102148 : Type'} (p : _102148 -> Prop) (t : _102148) : (term97 _102148 p t) = (term97 _102148 p t).
Proof. exact (eq_refl (term97 _102148 p t)). Qed.
Lemma lem4067545 {_102148 : Type'} (t : _102148) (p : _102148 -> Prop) : (term99 _102148 t p) = (term99 _102148 t p).
Proof. exact (MK_COMB (@lem4067544 _102148 p t) (@lem4067537 _102148 p)). Qed.
Lemma lem4067550 {_102148 : Type'} (p : _102148 -> Prop) (t : _102148) : (term45 _102148 p t) = (term45 _102148 p t).
Proof. exact (eq_refl (term45 _102148 p t)). Qed.
Lemma lem4067553 {_102148 : Type'} (p : _102148 -> Prop) (t : _102148) : (p t) = (p t).
Proof. exact (eq_refl (p t)). Qed.
Lemma lem4067554 {_102148 : Type'} (p : _102148 -> Prop) : (term48 _102148 p) = (term48 _102148 p).
Proof. exact (fun_ext (fun t : _102148 => @lem4067553 _102148 p t)). Qed.
Lemma lem4067555 {_102148 : Type'} : (@all _102148) = (@all _102148).
Proof. exact (eq_refl (@all _102148)). Qed.
Lemma lem4067556 {_102148 : Type'} (p : _102148 -> Prop) : (term32 _102148 p) = (term32 _102148 p).
Proof. exact (MK_COMB (@lem4067555 _102148) (@lem4067554 _102148 p)). Qed.
Lemma lem4067557 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4067558 {_102148 : Type'} (p : _102148 -> Prop) : (term68 _102148 p) = (term68 _102148 p).
Proof. exact (MK_COMB (@lem4067557) (@lem4067556 _102148 p)). Qed.
Lemma lem4067559 {_102148 : Type'} (p : _102148 -> Prop) (t : _102148) : (term84 _102148 p t) = (term84 _102148 p t).
Proof. exact (MK_COMB (@lem4067558 _102148 p) (@lem4067550 _102148 p t)). Qed.
Lemma lem4067560 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4067561 {_102148 : Type'} (p : _102148 -> Prop) (t : _102148) : (term118 _102148 p t) = (term118 _102148 p t).
Proof. exact (MK_COMB (@lem4067560) (@lem4067559 _102148 p t)). Qed.
Lemma lem4067562 {_102148 : Type'} (t : _102148) (p : _102148 -> Prop) : (term120 _102148 t p) = (term120 _102148 t p).
Proof. exact (MK_COMB (@lem4067561 _102148 p t) (@lem4067545 _102148 t p)). Qed.
Lemma lem4067563 {_102148 : Type'} (t : _102148) (p : _102148 -> Prop) (h1 : term120 _102148 t p) : term120 _102148 t p.
Proof. exact (EQ_MP (@lem4067562 _102148 t p) (@lem4067531 _102148 t p h1)). Qed.
Lemma lem4067564 {_102148 : Type'} (p : _102148 -> Prop) (t : _102148) (h1 : term84 _102148 p t) : term84 _102148 p t.
Proof. exact (h1). Qed.
Lemma lem4067565 {_102148 : Type'} (t : _102148) (p : _102148 -> Prop) (h1 : term99 _102148 t p) : term99 _102148 t p.
Proof. exact (h1). Qed.
Lemma lem4067567 {_102148 : Type'} (p : _102148 -> Prop) (t : _102148) (h1 : term84 _102148 p t) : term32 _102148 p.
Proof. exact (proj1 (@lem4067564 _102148 p t h1)). Qed.
Lemma lem4067568 {_102148 : Type'} (t : _102148) (p : _102148 -> Prop) (h1 : term99 _102148 t p) : term32 _102148 p.
Proof. exact (proj2 (@lem4067565 _102148 t p h1)). Qed.
Lemma lem4067571 {_102148 : Type'} (p : _102148 -> Prop) (t : _102148) : (p t) = (p t).
Proof. exact (eq_refl (p t)). Qed.
Lemma lem4067572 {_102148 : Type'} (p : _102148 -> Prop) : (term48 _102148 p) = (term48 _102148 p).
Proof. exact (fun_ext (fun t : _102148 => @lem4067571 _102148 p t)). Qed.
Lemma lem4067573 {_102148 : Type'} : (@all _102148) = (@all _102148).
Proof. exact (eq_refl (@all _102148)). Qed.
Lemma lem4067575 {_102148 : Type'} (p : _102148 -> Prop) : (term32 _102148 p) = (term32 _102148 p).
Proof. exact (MK_COMB (@lem4067573 _102148) (@lem4067572 _102148 p)). Qed.
Lemma lem4067576 {_102148 : Type'} (p : _102148 -> Prop) (t : _102148) (h1 : term84 _102148 p t) : term32 _102148 p.
Proof. exact (EQ_MP (@lem4067575 _102148 p) (@lem4067567 _102148 p t h1)). Qed.
Lemma lem4067586 {_102148 : Type'} (p : _102148 -> Prop) (t : _102148) : (p t) = (p t).
Proof. exact (eq_refl (p t)). Qed.
Lemma lem4067587 {_102148 : Type'} (p : _102148 -> Prop) : (term48 _102148 p) = (term48 _102148 p).
Proof. exact (fun_ext (fun t : _102148 => @lem4067586 _102148 p t)). Qed.
Lemma lem4067588 {_102148 : Type'} : (@all _102148) = (@all _102148).
Proof. exact (eq_refl (@all _102148)). Qed.
Lemma lem4067590 {_102148 : Type'} (p : _102148 -> Prop) : (term32 _102148 p) = (term32 _102148 p).
Proof. exact (MK_COMB (@lem4067588 _102148) (@lem4067587 _102148 p)). Qed.
Lemma lem4067591 {_102148 : Type'} (t : _102148) (p : _102148 -> Prop) (h1 : term99 _102148 t p) : term32 _102148 p.
Proof. exact (EQ_MP (@lem4067590 _102148 p) (@lem4067568 _102148 t p h1)). Qed.
Lemma lem4067592 {_102148 : Type'} (_47773 : _102148) (p : _102148 -> Prop) (t : _102148) (h1 : term84 _102148 p t) : term53 _102148 p _47773.
Proof. exact (@lem4067576 _102148 p t h1 _47773). Qed.
Lemma lem4067593 {_102148 : Type'} (p : _102148 -> Prop) (_47773 : _102148) : (term53 _102148 p _47773) = (p _47773).
Proof. exact (eq_refl (term53 _102148 p _47773)). Qed.
Lemma lem4067595 {_102148 : Type'} (_47774 : _102148) (t : _102148) (p : _102148 -> Prop) (h1 : term99 _102148 t p) : term53 _102148 p _47774.
Proof. exact (@lem4067591 _102148 t p h1 _47774). Qed.
Lemma lem4067596 {_102148 : Type'} (p : _102148 -> Prop) (_47774 : _102148) : (term53 _102148 p _47774) = (p _47774).
Proof. exact (eq_refl (term53 _102148 p _47774)). Qed.
Lemma lem4067601 {_102148 : Type'} (p : _102148 -> Prop) (t : _102148) (h1 : term84 _102148 p t) : term45 _102148 p t.
Proof. exact (proj2 (@lem4067564 _102148 p t h1)). Qed.
Lemma lem4067603 {_102148 : Type'} (t : _102148) (p : _102148 -> Prop) (h1 : term99 _102148 t p) : term45 _102148 p t.
Proof. exact (proj1 (@lem4067565 _102148 t p h1)). Qed.
Lemma lem4067607 {_102148 : Type'} (_47773 : _102148) (p : _102148 -> Prop) (t : _102148) (h1 : term84 _102148 p t) : p _47773.
Proof. exact (EQ_MP (@lem4067593 _102148 p _47773) (@lem4067592 _102148 _47773 p t h1)). Qed.
Lemma lem4067608 {_102148 : Type'} (_47773 : _102148) (p : _102148 -> Prop) (t : _102148) (h1 : term84 _102148 p t) : p _47773.
Proof. exact (@lem4067607 _102148 _47773 p t h1). Qed.
Lemma lem4067609 {_102148 : Type'} (p : _102148 -> Prop) (t : _102148) (h1 : term84 _102148 p t) : p t.
Proof. exact (@lem4067608 _102148 t p t h1). Qed.
Lemma lem4067610 {_102148 : Type'} (p : _102148 -> Prop) (t : _102148) (h1 : term84 _102148 p t) : term124 _102148 p t.
Proof. exact (fun h0 : term45 _102148 p t => @lem4067609 _102148 p t h1). Qed.
Lemma lem4067612 (p : Prop) : (term125 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4067613 {_102148 : Type'} (p : _102148 -> Prop) (t : _102148) : (term124 _102148 p t) = (p t).
Proof. exact (@lem4067612 (p t)). Qed.
Lemma lem4067614 {_102148 : Type'} (p : _102148 -> Prop) (t : _102148) (h1 : term84 _102148 p t) : p t.
Proof. exact (EQ_MP (@lem4067613 _102148 p t) (@lem4067610 _102148 p t h1)). Qed.
Lemma lem4067617 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4067619 {_102148 : Type'} (p : _102148 -> Prop) (t : _102148) : (term45 _102148 p t) = (term126 _102148 p t).
Proof. exact (@lem4067617 (p t)). Qed.
Lemma lem4067622 {_102148 : Type'} (p : _102148 -> Prop) (t : _102148) (h1 : term84 _102148 p t) : term126 _102148 p t.
Proof. exact (EQ_MP (@lem4067619 _102148 p t) (@lem4067601 _102148 p t h1)). Qed.
Lemma lem4067625 {_102148 : Type'} (p : _102148 -> Prop) (t : _102148) (h1 : term84 _102148 p t) : False.
Proof. exact (@lem4067622 _102148 p t h1 (@lem4067614 _102148 p t h1)). Qed.
Lemma lem4067626 {_102148 : Type'} (p : _102148 -> Prop) (t : _102148) (h1 : term84 _102148 p t) : term127.
Proof. exact (fun h0 : ~ False => @lem4067625 _102148 p t h1). Qed.
Lemma lem4067628 (p : Prop) : (term125 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4067629 : term127 = False.
Proof. exact (@lem4067628 False). Qed.
Lemma lem4067630 {_102148 : Type'} (p : _102148 -> Prop) (t : _102148) (h1 : term84 _102148 p t) : False.
Proof. exact (EQ_MP (@lem4067629) (@lem4067626 _102148 p t h1)). Qed.
Lemma lem4067632 {_102148 : Type'} (_47774 : _102148) (t : _102148) (p : _102148 -> Prop) (h1 : term99 _102148 t p) : p _47774.
Proof. exact (EQ_MP (@lem4067596 _102148 p _47774) (@lem4067595 _102148 _47774 t p h1)). Qed.
Lemma lem4067633 {_102148 : Type'} (_47774 : _102148) (t : _102148) (p : _102148 -> Prop) (h1 : term99 _102148 t p) : p _47774.
Proof. exact (@lem4067632 _102148 _47774 t p h1). Qed.
Lemma lem4067634 {_102148 : Type'} (t : _102148) (p : _102148 -> Prop) (h1 : term99 _102148 t p) : p t.
Proof. exact (@lem4067633 _102148 t t p h1). Qed.
Lemma lem4067635 {_102148 : Type'} (t : _102148) (p : _102148 -> Prop) (h1 : term99 _102148 t p) : term124 _102148 p t.
Proof. exact (fun h0 : term45 _102148 p t => @lem4067634 _102148 t p h1). Qed.
Lemma lem4067637 (p : Prop) : (term125 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4067638 {_102148 : Type'} (p : _102148 -> Prop) (t : _102148) : (term124 _102148 p t) = (p t).
Proof. exact (@lem4067637 (p t)). Qed.
Lemma lem4067639 {_102148 : Type'} (t : _102148) (p : _102148 -> Prop) (h1 : term99 _102148 t p) : p t.
Proof. exact (EQ_MP (@lem4067638 _102148 p t) (@lem4067635 _102148 t p h1)). Qed.
Lemma lem4067642 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4067644 {_102148 : Type'} (p : _102148 -> Prop) (t : _102148) : (term45 _102148 p t) = (term126 _102148 p t).
Proof. exact (@lem4067642 (p t)). Qed.
Lemma lem4067647 {_102148 : Type'} (t : _102148) (p : _102148 -> Prop) (h1 : term99 _102148 t p) : term126 _102148 p t.
Proof. exact (EQ_MP (@lem4067644 _102148 p t) (@lem4067603 _102148 t p h1)). Qed.
Lemma lem4067650 {_102148 : Type'} (t : _102148) (p : _102148 -> Prop) (h1 : term99 _102148 t p) : False.
Proof. exact (@lem4067647 _102148 t p h1 (@lem4067639 _102148 t p h1)). Qed.
Lemma lem4067651 {_102148 : Type'} (t : _102148) (p : _102148 -> Prop) (h1 : term99 _102148 t p) : term127.
Proof. exact (fun h0 : ~ False => @lem4067650 _102148 t p h1). Qed.
Lemma lem4067653 (p : Prop) : (term125 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4067654 : term127 = False.
Proof. exact (@lem4067653 False). Qed.
Lemma lem4067655 {_102148 : Type'} (t : _102148) (p : _102148 -> Prop) (h1 : term99 _102148 t p) : False.
Proof. exact (EQ_MP (@lem4067654) (@lem4067651 _102148 t p h1)). Qed.
Lemma lem4067656 {_102148 : Type'} (t : _102148) (p : _102148 -> Prop) (h1 : term120 _102148 t p) : False.
Proof. exact (or_elim (@lem4067563 _102148 t p h1) (fun h0 : term84 _102148 p t => @lem4067630 _102148 p t h0) (fun h0 : term99 _102148 t p => @lem4067655 _102148 t p h0)). Qed.
Lemma lem4067657 {_102148 : Type'} (t : _102148) (p : _102148 -> Prop) (h1 : term120 _102148 t p) : (term120 _102148 t p) = False.
Proof. exact (prop_ext (fun h2 : term120 _102148 t p => @lem4067656 _102148 t p h1) (fun h2 : False => @lem4067563 _102148 t p h1)). Qed.
Lemma lem4067658 {_102148 : Type'} (t : _102148) (p : _102148 -> Prop) (h1 : term120 _102148 t p) : False.
Proof. exact (EQ_MP (@lem4067657 _102148 t p h1) (@lem4067563 _102148 t p h1)). Qed.
Lemma lem4067659 {_102148 : Type'} (p : _102148 -> Prop) (h1 : term35 _102148 p) : False.
Proof. exact (ex_elim (@lem4067530 _102148 p h1) (fun t : _102148 => fun h0 : term122 _102148 p t => @lem4067658 _102148 t p h0)). Qed.
Lemma lem4067660 {_102148 : Type'} (p : _102148 -> Prop) (h1 : term35 _102148 p) : (term35 _102148 p) = False.
Proof. exact (prop_ext (fun h2 : term35 _102148 p => @lem4067659 _102148 p h1) (fun h2 : False => @lem4067390 _102148 p h1)). Qed.
Lemma lem4067661 {_102148 : Type'} (p : _102148 -> Prop) (h1 : term35 _102148 p) : False.
Proof. exact (EQ_MP (@lem4067660 _102148 p h1) (@lem4067390 _102148 p h1)). Qed.
Lemma lem4067662 {_102148 : Type'} (p : _102148 -> Prop) : term34 _102148 p.
Proof. exact (fun h0 : term35 _102148 p => @lem4067661 _102148 p h0). Qed.
Lemma lem4067663 {_102148 : Type'} (p : _102148 -> Prop) : (term32 _102148 p) = (term33 _102148 p).
Proof. exact (EQ_MP (@lem4067389 _102148 p) (@lem4067662 _102148 p)). Qed.
Lemma lem4067668 {_102148 : Type'} : term44 _102148.
Proof. exact (fun p : _102148 -> Prop => @lem4067663 _102148 p). Qed.
Lemma lem4067669 {_102148 : Type'} : term43 _102148.
Proof. exact (EQ_MP (@lem4067385 _102148) (@lem4067668 _102148)). Qed.
Lemma lem4067670 {_102148 : Type'} (p : _102148 -> Prop) : term128 _102148 p.
Proof. exact (@lem4067669 _102148 p). Qed.
Lemma lem4067671 {_102148 : Type'} (p : _102148 -> Prop) : (term128 _102148 p) = (term34 _102148 p).
Proof. exact (eq_refl (term128 _102148 p)). Qed.
Lemma lem4067672 {_102148 : Type'} (p : _102148 -> Prop) : term34 _102148 p.
Proof. exact (EQ_MP (@lem4067671 _102148 p) (@lem4067670 _102148 p)). Qed.
Lemma lem4067674 {_102148 : Type'} (p : _102148 -> Prop) : term34 _102148 p.
Proof. exact (@lem4067315 _102148 p (@lem4067672 _102148 p)). Qed.
Lemma lem4067675 {_102148 : Type'} (p : _102148 -> Prop) (h1 : term35 _102148 p) : False.
Proof. exact (@lem4067674 _102148 p (@lem4067299 _102148 p h1)). Qed.
Lemma lem4067676 {_102148 : Type'} (p : _102148 -> Prop) (h1 : term35 _102148 p) : (term35 _102148 p) = False.
Proof. exact (prop_ext (fun h2 : term35 _102148 p => @lem4067675 _102148 p h1) (fun h2 : False => @lem4067299 _102148 p h1)). Qed.
Lemma lem4067677 {_102148 : Type'} (p : _102148 -> Prop) (h1 : term35 _102148 p) : False.
Proof. exact (EQ_MP (@lem4067676 _102148 p h1) (@lem4067299 _102148 p h1)). Qed.
Lemma lem4067678 {_102148 : Type'} (p : _102148 -> Prop) : term34 _102148 p.
Proof. exact (fun h0 : term35 _102148 p => @lem4067677 _102148 p h0). Qed.
Lemma lem4067687 {_102148 : Type'} (p : _102148 -> Prop) : (term32 _102148 p) = (term33 _102148 p).
Proof. exact (EQ_MP (@lem4067298 _102148 p) (@lem4067678 _102148 p)). Qed.
Lemma lem4067688 {_102247 : Type'} (p : type686 _102247) : (term129 _102247 p) = (term130 _102247 p).
Proof. exact (@lem4067687 (_102247 -> Prop) p). Qed.
Lemma lem4067689 {_102240 _102247 : Type'} (n : nat) (f : _102240 -> _102247) (s : _102240 -> Prop) (P : type686 _102247) : (term131 _102240 _102247 n f s P) = (term132 _102240 _102247 n f s P).
Proof. exact (@lem4067688 _102247 (term133 _102240 _102247 n f s P)). Qed.
Lemma lem4067690 {_102240 _102247 : Type'} (n : nat) (f : _102240 -> _102247) (s : _102240 -> Prop) (P : type686 _102247) (t : _102247 -> Prop) : (term134 _102240 _102247 n f s P t) = (term135 _102240 _102247 n f s P t).
Proof. exact (eq_refl (term134 _102240 _102247 n f s P t)). Qed.
Lemma lem4067691 {_102240 _102247 : Type'} (n : nat) (f : _102240 -> _102247) (s : _102240 -> Prop) (P : type686 _102247) : (term136 _102240 _102247 n f s P) = (term133 _102240 _102247 n f s P).
Proof. exact (fun_ext (fun t : _102247 -> Prop => @lem4067690 _102240 _102247 n f s P t)). Qed.
Lemma lem4067692 {_102247 : Type'} : (@all (_102247 -> Prop)) = (@all (_102247 -> Prop)).
Proof. exact (eq_refl (@all (_102247 -> Prop))). Qed.
Lemma lem4067693 {_102240 _102247 : Type'} (n : nat) (f : _102240 -> _102247) (s : _102240 -> Prop) (P : type686 _102247) : (term131 _102240 _102247 n f s P) = (term137 _102240 _102247 n f s P).
Proof. exact (MK_COMB (@lem4067692 _102247) (@lem4067691 _102240 _102247 n f s P)). Qed.
Lemma lem4067694 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4067695 {_102240 _102247 : Type'} (n : nat) (f : _102240 -> _102247) (s : _102240 -> Prop) (P : type686 _102247) : (term138 _102240 _102247 n f s P) = (term139 _102240 _102247 n f s P).
Proof. exact (MK_COMB (@lem4067694) (@lem4067693 _102240 _102247 n f s P)). Qed.
Lemma lem4067696 {_102240 _102247 : Type'} (n : nat) (f : _102240 -> _102247) (s : _102240 -> Prop) (P : type686 _102247) (t : _102247 -> Prop) : (term134 _102240 _102247 n f s P t) = (term135 _102240 _102247 n f s P t).
Proof. exact (eq_refl (term134 _102240 _102247 n f s P t)). Qed.
Lemma lem4067697 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4067698 {_102240 _102247 : Type'} (n : nat) (f : _102240 -> _102247) (s : _102240 -> Prop) (P : type686 _102247) (t : _102247 -> Prop) : (term140 _102240 _102247 n f s P t) = (term141 _102240 _102247 n f s P t).
Proof. exact (MK_COMB (@lem4067697) (@lem4067696 _102240 _102247 n f s P t)). Qed.
Lemma lem4067699 {_102240 _102247 : Type'} (n : nat) (f : _102240 -> _102247) (s : _102240 -> Prop) (P : type686 _102247) : (term142 _102240 _102247 n f s P) = (term143 _102240 _102247 n f s P).
Proof. exact (fun_ext (fun t : _102247 -> Prop => @lem4067698 _102240 _102247 n f s P t)). Qed.
Lemma lem4067700 {_102247 : Type'} : (@ex (_102247 -> Prop)) = (@ex (_102247 -> Prop)).
Proof. exact (eq_refl (@ex (_102247 -> Prop))). Qed.
Lemma lem4067701 {_102240 _102247 : Type'} (n : nat) (f : _102240 -> _102247) (s : _102240 -> Prop) (P : type686 _102247) : (term144 _102240 _102247 n f s P) = (term145 _102240 _102247 n f s P).
Proof. exact (MK_COMB (@lem4067700 _102247) (@lem4067699 _102240 _102247 n f s P)). Qed.
Lemma lem4067702 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4067703 {_102240 _102247 : Type'} (n : nat) (f : _102240 -> _102247) (s : _102240 -> Prop) (P : type686 _102247) : (term132 _102240 _102247 n f s P) = (term146 _102240 _102247 n f s P).
Proof. exact (MK_COMB (@lem4067702) (@lem4067701 _102240 _102247 n f s P)). Qed.
Lemma lem4067704 {_102240 _102247 : Type'} (n : nat) (f : _102240 -> _102247) (s : _102240 -> Prop) (P : type686 _102247) : ((term131 _102240 _102247 n f s P) = (term132 _102240 _102247 n f s P)) = ((term137 _102240 _102247 n f s P) = (term146 _102240 _102247 n f s P)).
Proof. exact (MK_COMB (@lem4067695 _102240 _102247 n f s P) (@lem4067703 _102240 _102247 n f s P)). Qed.
Lemma lem4067705 {_102240 _102247 : Type'} (n : nat) (f : _102240 -> _102247) (s : _102240 -> Prop) (P : type686 _102247) : (term137 _102240 _102247 n f s P) = (term146 _102240 _102247 n f s P).
Proof. exact (EQ_MP (@lem4067704 _102240 _102247 n f s P) (@lem4067689 _102240 _102247 n f s P)). Qed.
Lemma lem4067706 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4067707 {_102240 _102247 : Type'} (n : nat) (f : _102240 -> _102247) (s : _102240 -> Prop) (P : type686 _102247) : (term139 _102240 _102247 n f s P) = (term147 _102240 _102247 n f s P).
Proof. exact (MK_COMB (@lem4067706) (@lem4067705 _102240 _102247 n f s P)). Qed.
Lemma lem4067713 {_102148 : Type'} (p : _102148 -> Prop) : (term32 _102148 p) = (term33 _102148 p).
Proof. exact (EQ_MP (@lem4067298 _102148 p) (@lem4067678 _102148 p)). Qed.
Lemma lem4067714 {_102240 : Type'} (p : type686 _102240) : (term129 _102240 p) = (term130 _102240 p).
Proof. exact (@lem4067713 (_102240 -> Prop) p). Qed.
Lemma lem4067715 {_102240 _102247 : Type'} (n : nat) (s : _102240 -> Prop) (P : type686 _102247) (f : _102240 -> _102247) : (term148 _102240 _102247 n s P f) = (term149 _102240 _102247 n s P f).
Proof. exact (@lem4067714 _102240 (term150 _102240 _102247 n s P f)). Qed.
Lemma lem4067716 {_102240 _102247 : Type'} (n : nat) (s : _102240 -> Prop) (P : type686 _102247) (f : _102240 -> _102247) (t : _102240 -> Prop) : (term151 _102240 _102247 n s P f t) = (term152 _102240 _102247 n s P f t).
Proof. exact (eq_refl (term151 _102240 _102247 n s P f t)). Qed.
Lemma lem4067717 {_102240 _102247 : Type'} (n : nat) (s : _102240 -> Prop) (P : type686 _102247) (f : _102240 -> _102247) : (term153 _102240 _102247 n s P f) = (term150 _102240 _102247 n s P f).
Proof. exact (fun_ext (fun t : _102240 -> Prop => @lem4067716 _102240 _102247 n s P f t)). Qed.
Lemma lem4067718 {_102240 : Type'} : (@all (_102240 -> Prop)) = (@all (_102240 -> Prop)).
Proof. exact (eq_refl (@all (_102240 -> Prop))). Qed.
Lemma lem4067719 {_102240 _102247 : Type'} (n : nat) (s : _102240 -> Prop) (P : type686 _102247) (f : _102240 -> _102247) : (term148 _102240 _102247 n s P f) = (term154 _102240 _102247 n s P f).
Proof. exact (MK_COMB (@lem4067718 _102240) (@lem4067717 _102240 _102247 n s P f)). Qed.
Lemma lem4067720 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4067721 {_102240 _102247 : Type'} (n : nat) (s : _102240 -> Prop) (P : type686 _102247) (f : _102240 -> _102247) : (term155 _102240 _102247 n s P f) = (term156 _102240 _102247 n s P f).
Proof. exact (MK_COMB (@lem4067720) (@lem4067719 _102240 _102247 n s P f)). Qed.
Lemma lem4067722 {_102240 _102247 : Type'} (n : nat) (s : _102240 -> Prop) (P : type686 _102247) (f : _102240 -> _102247) (t : _102240 -> Prop) : (term151 _102240 _102247 n s P f t) = (term152 _102240 _102247 n s P f t).
Proof. exact (eq_refl (term151 _102240 _102247 n s P f t)). Qed.
Lemma lem4067723 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4067724 {_102240 _102247 : Type'} (n : nat) (s : _102240 -> Prop) (P : type686 _102247) (f : _102240 -> _102247) (t : _102240 -> Prop) : (term157 _102240 _102247 n s P f t) = (term158 _102240 _102247 n s P f t).
Proof. exact (MK_COMB (@lem4067723) (@lem4067722 _102240 _102247 n s P f t)). Qed.
Lemma lem4067725 {_102240 _102247 : Type'} (n : nat) (s : _102240 -> Prop) (P : type686 _102247) (f : _102240 -> _102247) : (term159 _102240 _102247 n s P f) = (term160 _102240 _102247 n s P f).
Proof. exact (fun_ext (fun t : _102240 -> Prop => @lem4067724 _102240 _102247 n s P f t)). Qed.
Lemma lem4067726 {_102240 : Type'} : (@ex (_102240 -> Prop)) = (@ex (_102240 -> Prop)).
Proof. exact (eq_refl (@ex (_102240 -> Prop))). Qed.
Lemma lem4067727 {_102240 _102247 : Type'} (n : nat) (s : _102240 -> Prop) (P : type686 _102247) (f : _102240 -> _102247) : (term161 _102240 _102247 n s P f) = (term162 _102240 _102247 n s P f).
Proof. exact (MK_COMB (@lem4067726 _102240) (@lem4067725 _102240 _102247 n s P f)). Qed.
Lemma lem4067728 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4067729 {_102240 _102247 : Type'} (n : nat) (s : _102240 -> Prop) (P : type686 _102247) (f : _102240 -> _102247) : (term149 _102240 _102247 n s P f) = (term163 _102240 _102247 n s P f).
Proof. exact (MK_COMB (@lem4067728) (@lem4067727 _102240 _102247 n s P f)). Qed.
Lemma lem4067730 {_102240 _102247 : Type'} (n : nat) (s : _102240 -> Prop) (P : type686 _102247) (f : _102240 -> _102247) : ((term148 _102240 _102247 n s P f) = (term149 _102240 _102247 n s P f)) = ((term154 _102240 _102247 n s P f) = (term163 _102240 _102247 n s P f)).
Proof. exact (MK_COMB (@lem4067721 _102240 _102247 n s P f) (@lem4067729 _102240 _102247 n s P f)). Qed.
Lemma lem4067731 {_102240 _102247 : Type'} (n : nat) (s : _102240 -> Prop) (P : type686 _102247) (f : _102240 -> _102247) : (term154 _102240 _102247 n s P f) = (term163 _102240 _102247 n s P f).
Proof. exact (EQ_MP (@lem4067730 _102240 _102247 n s P f) (@lem4067715 _102240 _102247 n s P f)). Qed.
Lemma lem4067732 {_102240 _102247 : Type'} (n : nat) (s : _102240 -> Prop) (P : type686 _102247) (f : _102240 -> _102247) : ((term137 _102240 _102247 n f s P) = (term154 _102240 _102247 n s P f)) = ((term146 _102240 _102247 n f s P) = (term163 _102240 _102247 n s P f)).
Proof. exact (MK_COMB (@lem4067707 _102240 _102247 n f s P) (@lem4067731 _102240 _102247 n s P f)). Qed.
Lemma lem4067733 {_102240 _102247 : Type'} (n : nat) (s : _102240 -> Prop) (P : type686 _102247) (f : _102240 -> _102247) : ((term146 _102240 _102247 n f s P) = (term163 _102240 _102247 n s P f)) = ((term137 _102240 _102247 n f s P) = (term154 _102240 _102247 n s P f)).
Proof. exact (SYM (@lem4067732 _102240 _102247 n s P f)). Qed.
Lemma lem4067741 (t1 : Prop) (t2 : Prop) : (term29 t1 t2) = (term30 t1 t2).
Proof. exact (EQ_MP (@lem4067283 t1 t2) (@lem4067282 t1 t2)). Qed.
Lemma lem4067742 {_102240 _102247 : Type'} (n : nat) (f : _102240 -> _102247) (s : _102240 -> Prop) (P : type686 _102247) (t : _102247 -> Prop) : (term141 _102240 _102247 n f s P t) = (term164 _102240 _102247 n f s P t).
Proof. exact (@lem4067741 (term165 _102240 _102247 n t f s) (P t)). Qed.
Lemma lem4067744 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term1 t1 t2 t3) = (term0 t1 t2 t3).
Proof. exact (EQ_MP (@lem4067265 t1 t2 t3) (@lem4067264 t1 t2 t3)). Qed.
Lemma lem4067745 {_102240 _102247 : Type'} (n : nat) (f : _102240 -> _102247) (s : _102240 -> Prop) (P : type686 _102247) (t : _102247 -> Prop) : (term164 _102240 _102247 n f s P t) = (term166 _102240 _102247 n f s P t).
Proof. exact (@lem4067744 (@FINITE _102247 t) (term167 _102240 _102247 n t f s) (term168 _102247 P t)). Qed.
Lemma lem4067748 {_102240 _102247 : Type'} (n : nat) (f : _102240 -> _102247) (s : _102240 -> Prop) (P : type686 _102247) (t : _102247 -> Prop) : (term141 _102240 _102247 n f s P t) = (term166 _102240 _102247 n f s P t).
Proof. exact (TRANS (@lem4067742 _102240 _102247 n f s P t) (@lem4067745 _102240 _102247 n f s P t)). Qed.
Lemma lem4067750 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term1 t1 t2 t3) = (term0 t1 t2 t3).
Proof. exact (EQ_MP (@lem4067265 t1 t2 t3) (@lem4067264 t1 t2 t3)). Qed.
Lemma lem4067751 {_102240 _102247 : Type'} (n : nat) (f : _102240 -> _102247) (s : _102240 -> Prop) (P : type686 _102247) (t : _102247 -> Prop) : (term169 _102240 _102247 n f s P t) = (term170 _102240 _102247 n f s P t).
Proof. exact (@lem4067750 (term171 _102247 t n) (term172 _102240 _102247 t f s) (term168 _102247 P t)). Qed.
Lemma lem4067756 {_102247 : Type'} (t : _102247 -> Prop) : (term173 _102247 t) = (term173 _102247 t).
Proof. exact (eq_refl (term173 _102247 t)). Qed.
Lemma lem4067757 {_102240 _102247 : Type'} (n : nat) (f : _102240 -> _102247) (s : _102240 -> Prop) (P : type686 _102247) (t : _102247 -> Prop) : (term166 _102240 _102247 n f s P t) = (term174 _102240 _102247 n f s P t).
Proof. exact (MK_COMB (@lem4067756 _102247 t) (@lem4067751 _102240 _102247 n f s P t)). Qed.
Lemma lem4067760 {_102240 _102247 : Type'} (n : nat) (f : _102240 -> _102247) (s : _102240 -> Prop) (P : type686 _102247) (t : _102247 -> Prop) : (term141 _102240 _102247 n f s P t) = (term174 _102240 _102247 n f s P t).
Proof. exact (TRANS (@lem4067748 _102240 _102247 n f s P t) (@lem4067757 _102240 _102247 n f s P t)). Qed.
Lemma lem4067761 {_102240 _102247 : Type'} (n : nat) (f : _102240 -> _102247) (s : _102240 -> Prop) (P : type686 _102247) : (term143 _102240 _102247 n f s P) = (term175 _102240 _102247 n f s P).
Proof. exact (fun_ext (fun t : _102247 -> Prop => @lem4067760 _102240 _102247 n f s P t)). Qed.
Lemma lem4067762 {_102247 : Type'} : (@ex (_102247 -> Prop)) = (@ex (_102247 -> Prop)).
Proof. exact (eq_refl (@ex (_102247 -> Prop))). Qed.
Lemma lem4067763 {_102240 _102247 : Type'} (n : nat) (f : _102240 -> _102247) (s : _102240 -> Prop) (P : type686 _102247) : (term145 _102240 _102247 n f s P) = (term176 _102240 _102247 n f s P).
Proof. exact (MK_COMB (@lem4067762 _102247) (@lem4067761 _102240 _102247 n f s P)). Qed.
Lemma lem4067765 {_102126 _102133 : Type'} (n : nat) (s : _102126 -> Prop) (P : type686 _102133) (f : _102126 -> _102133) : (term24 _102126 _102133 n f s P) = (term25 _102126 _102133 n s P f).
Proof. exact (EQ_MP (@lem4067277 _102126 _102133 n s P f) (@lem4067276 _102126 _102133 s P f n)). Qed.
Lemma lem4067766 {_102240 _102247 : Type'} (n : nat) (s : _102240 -> Prop) (P : type686 _102247) (f : _102240 -> _102247) : (term24 _102240 _102247 n f s P) = (term25 _102240 _102247 n s P f).
Proof. exact (@lem4067765 _102240 _102247 n s P f). Qed.
Lemma lem4067767 {_102240 _102247 : Type'} (n : nat) (s : _102240 -> Prop) (P : type686 _102247) (f : _102240 -> _102247) : (term177 _102240 _102247 n f s P) = (term178 _102240 _102247 n s P f).
Proof. exact (@lem4067766 _102240 _102247 n s (term179 _102247 P) f). Qed.
Lemma lem4067768 {_102247 : Type'} (P : type686 _102247) (t : _102247 -> Prop) : (term180 _102247 P t) = (term168 _102247 P t).
Proof. exact (eq_refl (term180 _102247 P t)). Qed.
Lemma lem4067769 {_102240 _102247 : Type'} (t : _102247 -> Prop) (f : _102240 -> _102247) (s : _102240 -> Prop) : (term181 _102240 _102247 t f s) = (term181 _102240 _102247 t f s).
Proof. exact (eq_refl (term181 _102240 _102247 t f s)). Qed.
Lemma lem4067770 {_102240 _102247 : Type'} (f : _102240 -> _102247) (s : _102240 -> Prop) (P : type686 _102247) (t : _102247 -> Prop) : (term182 _102240 _102247 f s P t) = (term183 _102240 _102247 f s P t).
Proof. exact (MK_COMB (@lem4067769 _102240 _102247 t f s) (@lem4067768 _102247 P t)). Qed.
Lemma lem4067771 {_102247 : Type'} (t : _102247 -> Prop) (n : nat) : (term184 _102247 t n) = (term184 _102247 t n).
Proof. exact (eq_refl (term184 _102247 t n)). Qed.
Lemma lem4067772 {_102240 _102247 : Type'} (n : nat) (f : _102240 -> _102247) (s : _102240 -> Prop) (P : type686 _102247) (t : _102247 -> Prop) : (term185 _102240 _102247 n f s P t) = (term170 _102240 _102247 n f s P t).
Proof. exact (MK_COMB (@lem4067771 _102247 t n) (@lem4067770 _102240 _102247 f s P t)). Qed.
Lemma lem4067773 {_102247 : Type'} (t : _102247 -> Prop) : (term173 _102247 t) = (term173 _102247 t).
Proof. exact (eq_refl (term173 _102247 t)). Qed.
Lemma lem4067774 {_102240 _102247 : Type'} (n : nat) (f : _102240 -> _102247) (s : _102240 -> Prop) (P : type686 _102247) (t : _102247 -> Prop) : (term186 _102240 _102247 n f s P t) = (term174 _102240 _102247 n f s P t).
Proof. exact (MK_COMB (@lem4067773 _102247 t) (@lem4067772 _102240 _102247 n f s P t)). Qed.
Lemma lem4067775 {_102240 _102247 : Type'} (n : nat) (f : _102240 -> _102247) (s : _102240 -> Prop) (P : type686 _102247) : (term187 _102240 _102247 n f s P) = (term175 _102240 _102247 n f s P).
Proof. exact (fun_ext (fun t : _102247 -> Prop => @lem4067774 _102240 _102247 n f s P t)). Qed.
Lemma lem4067776 {_102247 : Type'} : (@ex (_102247 -> Prop)) = (@ex (_102247 -> Prop)).
Proof. exact (eq_refl (@ex (_102247 -> Prop))). Qed.
Lemma lem4067777 {_102240 _102247 : Type'} (n : nat) (f : _102240 -> _102247) (s : _102240 -> Prop) (P : type686 _102247) : (term177 _102240 _102247 n f s P) = (term176 _102240 _102247 n f s P).
Proof. exact (MK_COMB (@lem4067776 _102247) (@lem4067775 _102240 _102247 n f s P)). Qed.
Lemma lem4067778 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4067779 {_102240 _102247 : Type'} (n : nat) (f : _102240 -> _102247) (s : _102240 -> Prop) (P : type686 _102247) : (term188 _102240 _102247 n f s P) = (term189 _102240 _102247 n f s P).
Proof. exact (MK_COMB (@lem4067778) (@lem4067777 _102240 _102247 n f s P)). Qed.
Lemma lem4067780 {_102240 _102247 : Type'} (P : type686 _102247) (f : _102240 -> _102247) (t : _102240 -> Prop) : (term190 _102240 _102247 P f t) = (term191 _102240 _102247 P f t).
Proof. exact (eq_refl (term190 _102240 _102247 P f t)). Qed.
Lemma lem4067781 {_102240 _102247 : Type'} (t : _102240 -> Prop) (f : _102240 -> _102247) : (term192 _102240 _102247 t f) = (term192 _102240 _102247 t f).
Proof. exact (eq_refl (term192 _102240 _102247 t f)). Qed.
Lemma lem4067782 {_102240 _102247 : Type'} (P : type686 _102247) (f : _102240 -> _102247) (t : _102240 -> Prop) : (term193 _102240 _102247 P f t) = (term194 _102240 _102247 P f t).
Proof. exact (MK_COMB (@lem4067781 _102240 _102247 t f) (@lem4067780 _102240 _102247 P f t)). Qed.
Lemma lem4067783 {_102240 : Type'} (t : _102240 -> Prop) (s : _102240 -> Prop) : (term195 _102240 t s) = (term195 _102240 t s).
Proof. exact (eq_refl (term195 _102240 t s)). Qed.
Lemma lem4067784 {_102240 _102247 : Type'} (s : _102240 -> Prop) (P : type686 _102247) (f : _102240 -> _102247) (t : _102240 -> Prop) : (term196 _102240 _102247 s P f t) = (term197 _102240 _102247 s P f t).
Proof. exact (MK_COMB (@lem4067783 _102240 t s) (@lem4067782 _102240 _102247 P f t)). Qed.
Lemma lem4067785 {_102240 : Type'} (t : _102240 -> Prop) (n : nat) : (term184 _102240 t n) = (term184 _102240 t n).
Proof. exact (eq_refl (term184 _102240 t n)). Qed.
Lemma lem4067786 {_102240 _102247 : Type'} (n : nat) (s : _102240 -> Prop) (P : type686 _102247) (f : _102240 -> _102247) (t : _102240 -> Prop) : (term198 _102240 _102247 n s P f t) = (term199 _102240 _102247 n s P f t).
Proof. exact (MK_COMB (@lem4067785 _102240 t n) (@lem4067784 _102240 _102247 s P f t)). Qed.
Lemma lem4067787 {_102240 : Type'} (t : _102240 -> Prop) : (term173 _102240 t) = (term173 _102240 t).
Proof. exact (eq_refl (term173 _102240 t)). Qed.
Lemma lem4067788 {_102240 _102247 : Type'} (n : nat) (s : _102240 -> Prop) (P : type686 _102247) (f : _102240 -> _102247) (t : _102240 -> Prop) : (term200 _102240 _102247 n s P f t) = (term201 _102240 _102247 n s P f t).
Proof. exact (MK_COMB (@lem4067787 _102240 t) (@lem4067786 _102240 _102247 n s P f t)). Qed.
Lemma lem4067789 {_102240 _102247 : Type'} (n : nat) (s : _102240 -> Prop) (P : type686 _102247) (f : _102240 -> _102247) : (term202 _102240 _102247 n s P f) = (term203 _102240 _102247 n s P f).
Proof. exact (fun_ext (fun t : _102240 -> Prop => @lem4067788 _102240 _102247 n s P f t)). Qed.
Lemma lem4067790 {_102240 : Type'} : (@ex (_102240 -> Prop)) = (@ex (_102240 -> Prop)).
Proof. exact (eq_refl (@ex (_102240 -> Prop))). Qed.
Lemma lem4067791 {_102240 _102247 : Type'} (n : nat) (s : _102240 -> Prop) (P : type686 _102247) (f : _102240 -> _102247) : (term178 _102240 _102247 n s P f) = (term204 _102240 _102247 n s P f).
Proof. exact (MK_COMB (@lem4067790 _102240) (@lem4067789 _102240 _102247 n s P f)). Qed.
Lemma lem4067792 {_102240 _102247 : Type'} (n : nat) (s : _102240 -> Prop) (P : type686 _102247) (f : _102240 -> _102247) : ((term177 _102240 _102247 n f s P) = (term178 _102240 _102247 n s P f)) = ((term176 _102240 _102247 n f s P) = (term204 _102240 _102247 n s P f)).
Proof. exact (MK_COMB (@lem4067779 _102240 _102247 n f s P) (@lem4067791 _102240 _102247 n s P f)). Qed.
Lemma lem4067793 {_102240 _102247 : Type'} (n : nat) (s : _102240 -> Prop) (P : type686 _102247) (f : _102240 -> _102247) : (term176 _102240 _102247 n f s P) = (term204 _102240 _102247 n s P f).
Proof. exact (EQ_MP (@lem4067792 _102240 _102247 n s P f) (@lem4067767 _102240 _102247 n s P f)). Qed.
Lemma lem4067824 {_102240 _102247 : Type'} (n : nat) (s : _102240 -> Prop) (P : type686 _102247) (f : _102240 -> _102247) : (term145 _102240 _102247 n f s P) = (term204 _102240 _102247 n s P f).
Proof. exact (TRANS (@lem4067763 _102240 _102247 n f s P) (@lem4067793 _102240 _102247 n s P f)). Qed.
Lemma lem4067825 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4067826 {_102240 _102247 : Type'} (n : nat) (s : _102240 -> Prop) (P : type686 _102247) (f : _102240 -> _102247) : (term146 _102240 _102247 n f s P) = (term205 _102240 _102247 n s P f).
Proof. exact (MK_COMB (@lem4067825) (@lem4067824 _102240 _102247 n s P f)). Qed.
Lemma lem4067827 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4067828 {_102240 _102247 : Type'} (n : nat) (s : _102240 -> Prop) (P : type686 _102247) (f : _102240 -> _102247) : (term147 _102240 _102247 n f s P) = (term206 _102240 _102247 n s P f).
Proof. exact (MK_COMB (@lem4067827) (@lem4067826 _102240 _102247 n s P f)). Qed.
Lemma lem4067834 (t1 : Prop) (t2 : Prop) : (term29 t1 t2) = (term30 t1 t2).
Proof. exact (EQ_MP (@lem4067283 t1 t2) (@lem4067282 t1 t2)). Qed.
Lemma lem4067835 {_102240 _102247 : Type'} (n : nat) (s : _102240 -> Prop) (P : type686 _102247) (f : _102240 -> _102247) (t : _102240 -> Prop) : (term158 _102240 _102247 n s P f t) = (term207 _102240 _102247 n s P f t).
Proof. exact (@lem4067834 (term208 _102240 _102247 n s t f) (term209 _102240 _102247 P f t)). Qed.
Lemma lem4067837 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term1 t1 t2 t3) = (term0 t1 t2 t3).
Proof. exact (EQ_MP (@lem4067265 t1 t2 t3) (@lem4067264 t1 t2 t3)). Qed.
Lemma lem4067838 {_102240 _102247 : Type'} (n : nat) (s : _102240 -> Prop) (P : type686 _102247) (f : _102240 -> _102247) (t : _102240 -> Prop) : (term207 _102240 _102247 n s P f t) = (term210 _102240 _102247 n s P f t).
Proof. exact (@lem4067837 (@FINITE _102240 t) (term211 _102240 _102247 n s t f) (term191 _102240 _102247 P f t)). Qed.
Lemma lem4067841 {_102240 _102247 : Type'} (n : nat) (s : _102240 -> Prop) (P : type686 _102247) (f : _102240 -> _102247) (t : _102240 -> Prop) : (term158 _102240 _102247 n s P f t) = (term210 _102240 _102247 n s P f t).
Proof. exact (TRANS (@lem4067835 _102240 _102247 n s P f t) (@lem4067838 _102240 _102247 n s P f t)). Qed.
Lemma lem4067843 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term1 t1 t2 t3) = (term0 t1 t2 t3).
Proof. exact (EQ_MP (@lem4067265 t1 t2 t3) (@lem4067264 t1 t2 t3)). Qed.
Lemma lem4067844 {_102240 _102247 : Type'} (n : nat) (s : _102240 -> Prop) (P : type686 _102247) (f : _102240 -> _102247) (t : _102240 -> Prop) : (term212 _102240 _102247 n s P f t) = (term213 _102240 _102247 n s P f t).
Proof. exact (@lem4067843 (term171 _102240 t n) (term214 _102240 _102247 s t f) (term191 _102240 _102247 P f t)). Qed.
Lemma lem4067848 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term1 t1 t2 t3) = (term0 t1 t2 t3).
Proof. exact (EQ_MP (@lem4067265 t1 t2 t3) (@lem4067264 t1 t2 t3)). Qed.
Lemma lem4067849 {_102240 _102247 : Type'} (s : _102240 -> Prop) (P : type686 _102247) (f : _102240 -> _102247) (t : _102240 -> Prop) : (term215 _102240 _102247 s P f t) = (term197 _102240 _102247 s P f t).
Proof. exact (@lem4067848 (@SUBSET _102240 t s) (term216 _102240 _102247 t f) (term191 _102240 _102247 P f t)). Qed.
Lemma lem4067872 {_102240 : Type'} (t : _102240 -> Prop) (n : nat) : (term184 _102240 t n) = (term184 _102240 t n).
Proof. exact (eq_refl (term184 _102240 t n)). Qed.
Lemma lem4067873 {_102240 _102247 : Type'} (n : nat) (s : _102240 -> Prop) (P : type686 _102247) (f : _102240 -> _102247) (t : _102240 -> Prop) : (term213 _102240 _102247 n s P f t) = (term199 _102240 _102247 n s P f t).
Proof. exact (MK_COMB (@lem4067872 _102240 t n) (@lem4067849 _102240 _102247 s P f t)). Qed.
Lemma lem4067876 {_102240 _102247 : Type'} (n : nat) (s : _102240 -> Prop) (P : type686 _102247) (f : _102240 -> _102247) (t : _102240 -> Prop) : (term212 _102240 _102247 n s P f t) = (term199 _102240 _102247 n s P f t).
Proof. exact (TRANS (@lem4067844 _102240 _102247 n s P f t) (@lem4067873 _102240 _102247 n s P f t)). Qed.
Lemma lem4067877 {_102240 : Type'} (t : _102240 -> Prop) : (term173 _102240 t) = (term173 _102240 t).
Proof. exact (eq_refl (term173 _102240 t)). Qed.
Lemma lem4067878 {_102240 _102247 : Type'} (n : nat) (s : _102240 -> Prop) (P : type686 _102247) (f : _102240 -> _102247) (t : _102240 -> Prop) : (term210 _102240 _102247 n s P f t) = (term201 _102240 _102247 n s P f t).
Proof. exact (MK_COMB (@lem4067877 _102240 t) (@lem4067876 _102240 _102247 n s P f t)). Qed.
Lemma lem4067881 {_102240 _102247 : Type'} (n : nat) (s : _102240 -> Prop) (P : type686 _102247) (f : _102240 -> _102247) (t : _102240 -> Prop) : (term158 _102240 _102247 n s P f t) = (term201 _102240 _102247 n s P f t).
Proof. exact (TRANS (@lem4067841 _102240 _102247 n s P f t) (@lem4067878 _102240 _102247 n s P f t)). Qed.
Lemma lem4067882 {_102240 _102247 : Type'} (n : nat) (s : _102240 -> Prop) (P : type686 _102247) (f : _102240 -> _102247) : (term160 _102240 _102247 n s P f) = (term203 _102240 _102247 n s P f).
Proof. exact (fun_ext (fun t : _102240 -> Prop => @lem4067881 _102240 _102247 n s P f t)). Qed.
Lemma lem4067883 {_102240 : Type'} : (@ex (_102240 -> Prop)) = (@ex (_102240 -> Prop)).
Proof. exact (eq_refl (@ex (_102240 -> Prop))). Qed.
Lemma lem4067884 {_102240 _102247 : Type'} (n : nat) (s : _102240 -> Prop) (P : type686 _102247) (f : _102240 -> _102247) : (term162 _102240 _102247 n s P f) = (term204 _102240 _102247 n s P f).
Proof. exact (MK_COMB (@lem4067883 _102240) (@lem4067882 _102240 _102247 n s P f)). Qed.
Lemma lem4067889 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4067890 {_102240 _102247 : Type'} (n : nat) (s : _102240 -> Prop) (P : type686 _102247) (f : _102240 -> _102247) : (term163 _102240 _102247 n s P f) = (term205 _102240 _102247 n s P f).
Proof. exact (MK_COMB (@lem4067889) (@lem4067884 _102240 _102247 n s P f)). Qed.
Lemma lem4067891 {_102240 _102247 : Type'} (n : nat) (s : _102240 -> Prop) (P : type686 _102247) (f : _102240 -> _102247) : ((term146 _102240 _102247 n f s P) = (term163 _102240 _102247 n s P f)) = ((term205 _102240 _102247 n s P f) = (term205 _102240 _102247 n s P f)).
Proof. exact (MK_COMB (@lem4067828 _102240 _102247 n s P f) (@lem4067890 _102240 _102247 n s P f)). Qed.
Lemma lem4067893 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4067894 (x : Prop) : (x = x) = True.
Proof. exact (@lem4067893 Prop x). Qed.
Lemma lem4067895 {_102240 _102247 : Type'} (n : nat) (s : _102240 -> Prop) (P : type686 _102247) (f : _102240 -> _102247) : ((term205 _102240 _102247 n s P f) = (term205 _102240 _102247 n s P f)) = True.
Proof. exact (@lem4067894 (term205 _102240 _102247 n s P f)). Qed.
Lemma lem4067896 {_102240 _102247 : Type'} (n : nat) (s : _102240 -> Prop) (P : type686 _102247) (f : _102240 -> _102247) : ((term146 _102240 _102247 n f s P) = (term163 _102240 _102247 n s P f)) = True.
Proof. exact (TRANS (@lem4067891 _102240 _102247 n s P f) (@lem4067895 _102240 _102247 n s P f)). Qed.
Lemma lem4067897 {_102240 _102247 : Type'} (n : nat) (s : _102240 -> Prop) (P : type686 _102247) (f : _102240 -> _102247) : True = ((term146 _102240 _102247 n f s P) = (term163 _102240 _102247 n s P f)).
Proof. exact (SYM (@lem4067896 _102240 _102247 n s P f)). Qed.
Lemma lem4067898 {_102240 _102247 : Type'} (n : nat) (s : _102240 -> Prop) (P : type686 _102247) (f : _102240 -> _102247) : (term146 _102240 _102247 n f s P) = (term163 _102240 _102247 n s P f).
Proof. exact (EQ_MP (@lem4067897 _102240 _102247 n s P f) (@lem0)). Qed.
Lemma lem4067899 {_102240 _102247 : Type'} (n : nat) (s : _102240 -> Prop) (P : type686 _102247) (f : _102240 -> _102247) : (term137 _102240 _102247 n f s P) = (term154 _102240 _102247 n s P f).
Proof. exact (EQ_MP (@lem4067733 _102240 _102247 n s P f) (@lem4067898 _102240 _102247 n s P f)). Qed.
Lemma lem4067904 {_102240 _102247 : Type'} (s : _102240 -> Prop) (P : type686 _102247) (f : _102240 -> _102247) : term217 _102240 _102247 s P f.
Proof. exact (fun n : nat => @lem4067899 _102240 _102247 n s P f). Qed.
Lemma lem4067909 {_102240 _102247 : Type'} (P : type686 _102247) (f : _102240 -> _102247) : term218 _102240 _102247 P f.
Proof. exact (fun s : _102240 -> Prop => @lem4067904 _102240 _102247 s P f). Qed.
Lemma lem4067914 {_102240 _102247 : Type'} (P : type686 _102247) : term219 _102240 _102247 P.
Proof. exact (fun f : _102240 -> _102247 => @lem4067909 _102240 _102247 P f). Qed.
Lemma lem4067919 {_102240 _102247 : Type'} : term220 _102240 _102247.
Proof. exact (fun P : type686 _102247 => @lem4067914 _102240 _102247 P). Qed.
