Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MOD_MULT_ADD_term_abbrevs.
Require Import ADD_AC_spec.
Require Import ADD_ASSOC_spec.
Require Import ADD_CLAUSES_spec.
Require Import BOOL_CASES_AX_spec.
Require Import DIVISION_spec.
Require Import EQ_ADD_LCANCEL_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import MOD_UNIQ_spec.
Require Import MULT_AC_spec.
Require Import MULT_CLAUSES_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import RIGHT_ADD_DISTRIB_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1844_spec.
Require Import thm1845_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem206232 (m : nat) (n : nat) (p : nat) (h1 : (term0 m n p) = (term1 m n p)) : (term0 m n p) = (term1 m n p).
Proof. exact (h1). Qed.
Lemma lem206233 (m : nat) (n : nat) (p : nat) (h1 : (term0 m n p) = (term1 m n p)) : (term1 m n p) = (term0 m n p).
Proof. exact (SYM (@lem206232 m n p h1)). Qed.
Lemma lem206234 (m : nat) (n : nat) (p : nat) (h1 : (term1 m n p) = (term0 m n p)) : (term1 m n p) = (term0 m n p).
Proof. exact (h1). Qed.
Lemma lem206235 (m : nat) (n : nat) (p : nat) (h1 : (term1 m n p) = (term0 m n p)) : (term0 m n p) = (term1 m n p).
Proof. exact (SYM (@lem206234 m n p h1)). Qed.
Lemma lem206236 (m : nat) (n : nat) (p : nat) : ((term0 m n p) = (term1 m n p)) = ((term1 m n p) = (term0 m n p)).
Proof. exact (prop_ext (fun h1 : (term0 m n p) = (term1 m n p) => @lem206233 m n p h1) (fun h1 : (term1 m n p) = (term0 m n p) => @lem206235 m n p h1)). Qed.
Lemma lem206237 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (fun_ext (fun p : nat => @lem206236 m n p)). Qed.
Lemma lem206238 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem206239 (m : nat) (n : nat) : (term4 m n) = (term5 m n).
Proof. exact (MK_COMB (@lem206238) (@lem206237 m n)). Qed.
Lemma lem206240 (m : nat) : (term6 m) = (term7 m).
Proof. exact (fun_ext (fun n : nat => @lem206239 m n)). Qed.
Lemma lem206241 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem206242 (m : nat) : (term8 m) = (term9 m).
Proof. exact (MK_COMB (@lem206241) (@lem206240 m)). Qed.
Lemma lem206243 : term10 = term11.
Proof. exact (fun_ext (fun m : nat => @lem206242 m)). Qed.
Lemma lem206244 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem206245 : term12 = term13.
Proof. exact (MK_COMB (@lem206244) (@lem206243)). Qed.
Lemma lem206246 : term13.
Proof. exact (EQ_MP (@lem206245) (@lem77960)). Qed.
Lemma lem206247 (h1 : term14) : term14.
Proof. exact (h1). Qed.
Lemma lem206248 (m : nat) (h1 : term14) : term15 m.
Proof. exact (@lem206247 h1 m). Qed.
Lemma lem206249 (m : nat) : (term15 m) = (term16 m).
Proof. exact (eq_refl (term15 m)). Qed.
Lemma lem206250 (m : nat) (h1 : term14) : term16 m.
Proof. exact (EQ_MP (@lem206249 m) (@lem206248 m h1)). Qed.
Lemma lem206251 (m : nat) (n : nat) (h1 : term14) : term17 m n.
Proof. exact (@lem206250 m h1 n). Qed.
Lemma lem206252 (m : nat) (n : nat) : (term17 m n) = (term18 m n).
Proof. exact (eq_refl (term17 m n)). Qed.
Lemma lem206253 (m : nat) (n : nat) (h1 : term14) : term18 m n.
Proof. exact (EQ_MP (@lem206252 m n) (@lem206251 m n h1)). Qed.
Lemma lem206254 (m : nat) (n : nat) (q : nat) (h1 : term14) : term19 m n q.
Proof. exact (@lem206253 m n h1 q). Qed.
Lemma lem206255 (q : nat) (m : nat) (n : nat) : (term19 m n q) = (term20 q m n).
Proof. exact (eq_refl (term19 m n q)). Qed.
Lemma lem206256 (q : nat) (m : nat) (n : nat) (h1 : term14) : term20 q m n.
Proof. exact (EQ_MP (@lem206255 q m n) (@lem206254 m n q h1)). Qed.
Lemma lem206257 (q : nat) (m : nat) (n : nat) (r : nat) (h1 : term14) : term21 q m n r.
Proof. exact (@lem206256 q m n h1 r). Qed.
Lemma lem206258 (q : nat) (m : nat) (n : nat) (r : nat) : (term21 q m n r) = (term22 q m n r).
Proof. exact (eq_refl (term21 q m n r)). Qed.
Lemma lem206259 (q : nat) (m : nat) (n : nat) (r : nat) (h1 : term14) : term22 q m n r.
Proof. exact (EQ_MP (@lem206258 q m n r) (@lem206257 q m n r h1)). Qed.
Lemma lem206260 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term23 m q r n) : term23 m q r n.
Proof. exact (h1). Qed.
Lemma lem206261 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term14) (h2 : term23 m q r n) : (Nat.modulo m n) = r.
Proof. exact (@lem206259 q m n r h1 (@lem206260 m q r n h2)). Qed.
Lemma lem206262 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term23 m q r n) : term24 m n r.
Proof. exact (fun h0 : term14 => @lem206261 m q r n h0 h1). Qed.
Lemma lem206263 (m : nat) (r : nat) (n : nat) (h1 : term25 m r n) : term25 m r n.
Proof. exact (h1). Qed.
Lemma lem206264 (m : nat) (r : nat) (n : nat) (h1 : term25 m r n) : term24 m n r.
Proof. exact (ex_elim (@lem206263 m r n h1) (fun q : nat => fun h0 : term26 m r n q => @lem206262 m q r n h0)). Qed.
Lemma lem206265 (h1 : term14) : term14.
Proof. exact (h1). Qed.
Lemma lem206266 (m : nat) (r : nat) (n : nat) (h1 : term14) (h2 : term25 m r n) : (Nat.modulo m n) = r.
Proof. exact (@lem206264 m r n h2 (@lem206265 h1)). Qed.
Lemma lem206267 (m : nat) (n : nat) (r : nat) (h1 : term14) : term27 m n r.
Proof. exact (fun h0 : term25 m r n => @lem206266 m r n h1 h0). Qed.
Lemma lem206268 (m : nat) (n : nat) (h1 : term14) : term28 m n.
Proof. exact (fun r : nat => @lem206267 m n r h1). Qed.
Lemma lem206269 (m : nat) (h1 : term14) : term29 m.
Proof. exact (fun n : nat => @lem206268 m n h1). Qed.
Lemma lem206270 (h1 : term14) : term30.
Proof. exact (fun m : nat => @lem206269 m h1). Qed.
Lemma lem206271 : term31.
Proof. exact (fun h0 : term14 => @lem206270 h0). Qed.
Lemma lem206272 : term30.
Proof. exact (@lem206271 (@lem169705)). Qed.
Lemma lem206273 (m : nat) : term32 m.
Proof. exact (@lem206272 m). Qed.
Lemma lem206274 (m : nat) : (term32 m) = (term29 m).
Proof. exact (eq_refl (term32 m)). Qed.
Lemma lem206275 (m : nat) : term29 m.
Proof. exact (EQ_MP (@lem206274 m) (@lem206273 m)). Qed.
Lemma lem206276 (m : nat) (n : nat) : term33 m n.
Proof. exact (@lem206275 m n). Qed.
Lemma lem206277 (m : nat) (n : nat) : (term33 m n) = (term28 m n).
Proof. exact (eq_refl (term33 m n)). Qed.
Lemma lem206278 (m : nat) (n : nat) : term28 m n.
Proof. exact (EQ_MP (@lem206277 m n) (@lem206276 m n)). Qed.
Lemma lem206279 (m : nat) (n : nat) (r : nat) : term34 m n r.
Proof. exact (@lem206278 m n r). Qed.
Lemma lem206280 (m : nat) (n : nat) (r : nat) : (term34 m n r) = (term27 m n r).
Proof. exact (eq_refl (term34 m n r)). Qed.
Lemma lem206282 (n : nat) : term35 n.
Proof. exact (@lem9784 (n = (NUMERAL 0))). Qed.
Lemma lem206283 (n : nat) : (term35 n) = (term36 n).
Proof. exact (eq_refl (term35 n)). Qed.
Lemma lem206284 (n : nat) : term36 n.
Proof. exact (EQ_MP (@lem206283 n) (@lem206282 n)). Qed.
Lemma lem206286 (n : nat) (h1 : term37 n) : term37 n.
Proof. exact (h1). Qed.
Lemma lem206305 (p : Prop) : term38 p.
Proof. exact (@lem9851 p). Qed.
Lemma lem206306 (p : Prop) : (term38 p) = (term39 p).
Proof. exact (eq_refl (term38 p)). Qed.
Lemma lem206307 (p : Prop) : term39 p.
Proof. exact (EQ_MP (@lem206306 p) (@lem206305 p)). Qed.
Lemma lem206308 (p : Prop) (h1 : p = True) : p = True.
Proof. exact (h1). Qed.
Lemma lem206309 (p : Prop) (h1 : p = False) : p = False.
Proof. exact (h1). Qed.
Lemma lem206320 (q : Prop) : (term40 q) = (term40 q).
Proof. exact (eq_refl (term40 q)). Qed.
Lemma lem206321 (q : Prop) (p : Prop) (h1 : p = True) : (term41 q p) = (term42 q).
Proof. exact (MK_COMB (@lem206320 q) (@lem206308 p h1)). Qed.
Lemma lem206322 (q : Prop) : (term42 q) = (term43 q).
Proof. exact (eq_refl (term42 q)). Qed.
Lemma lem206323 (q : Prop) (p : Prop) : (term44 q p) = (term44 q p).
Proof. exact (eq_refl (term44 q p)). Qed.
Lemma lem206324 (p : Prop) (q : Prop) : ((term41 q p) = (term42 q)) = ((term41 q p) = (term43 q)).
Proof. exact (MK_COMB (@lem206323 q p) (@lem206322 q)). Qed.
Lemma lem206325 (p : Prop) (q : Prop) : (term41 q p) = (term45 p q).
Proof. exact (eq_refl (term41 q p)). Qed.
Lemma lem206326 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem206327 (p : Prop) (q : Prop) : (term44 q p) = (term46 p q).
Proof. exact (MK_COMB (@lem206326) (@lem206325 p q)). Qed.
Lemma lem206328 (q : Prop) : (term43 q) = (term43 q).
Proof. exact (eq_refl (term43 q)). Qed.
Lemma lem206329 (p : Prop) (q : Prop) : ((term41 q p) = (term43 q)) = ((term45 p q) = (term43 q)).
Proof. exact (MK_COMB (@lem206327 p q) (@lem206328 q)). Qed.
Lemma lem206330 (p : Prop) (q : Prop) : ((term41 q p) = (term42 q)) = ((term45 p q) = (term43 q)).
Proof. exact (TRANS (@lem206324 p q) (@lem206329 p q)). Qed.
Lemma lem206331 (q : Prop) (p : Prop) (h1 : p = True) : (term45 p q) = (term43 q).
Proof. exact (EQ_MP (@lem206330 p q) (@lem206321 q p h1)). Qed.
Lemma lem206332 (q : Prop) (p : Prop) (h1 : p = True) : (term43 q) = (term45 p q).
Proof. exact (SYM (@lem206331 q p h1)). Qed.
Lemma lem206333 (q : Prop) : (term40 q) = (term40 q).
Proof. exact (eq_refl (term40 q)). Qed.
Lemma lem206334 (q : Prop) (p : Prop) (h1 : p = False) : (term41 q p) = (term47 q).
Proof. exact (MK_COMB (@lem206333 q) (@lem206309 p h1)). Qed.
Lemma lem206335 (q : Prop) : (term47 q) = (term48 q).
Proof. exact (eq_refl (term47 q)). Qed.
Lemma lem206336 (q : Prop) (p : Prop) : (term44 q p) = (term44 q p).
Proof. exact (eq_refl (term44 q p)). Qed.
Lemma lem206337 (p : Prop) (q : Prop) : ((term41 q p) = (term47 q)) = ((term41 q p) = (term48 q)).
Proof. exact (MK_COMB (@lem206336 q p) (@lem206335 q)). Qed.
Lemma lem206338 (p : Prop) (q : Prop) : (term41 q p) = (term45 p q).
Proof. exact (eq_refl (term41 q p)). Qed.
Lemma lem206339 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem206340 (p : Prop) (q : Prop) : (term44 q p) = (term46 p q).
Proof. exact (MK_COMB (@lem206339) (@lem206338 p q)). Qed.
Lemma lem206341 (q : Prop) : (term48 q) = (term48 q).
Proof. exact (eq_refl (term48 q)). Qed.
Lemma lem206342 (p : Prop) (q : Prop) : ((term41 q p) = (term48 q)) = ((term45 p q) = (term48 q)).
Proof. exact (MK_COMB (@lem206340 p q) (@lem206341 q)). Qed.
Lemma lem206343 (p : Prop) (q : Prop) : ((term41 q p) = (term47 q)) = ((term45 p q) = (term48 q)).
Proof. exact (TRANS (@lem206337 p q) (@lem206342 p q)). Qed.
Lemma lem206344 (q : Prop) (p : Prop) (h1 : p = False) : (term45 p q) = (term48 q).
Proof. exact (EQ_MP (@lem206343 p q) (@lem206334 q p h1)). Qed.
Lemma lem206345 (q : Prop) (p : Prop) (h1 : p = False) : (term48 q) = (term45 p q).
Proof. exact (SYM (@lem206344 q p h1)). Qed.
Lemma lem206349 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem206350 (q : Prop) : (term49 q) = (True -> q).
Proof. exact (@lem206349 (True -> q)). Qed.
Lemma lem206352 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem206353 (q : Prop) : (True -> q) = q.
Proof. exact (@lem206352 q). Qed.
Lemma lem206354 (q : Prop) : (term49 q) = q.
Proof. exact (TRANS (@lem206350 q) (@lem206353 q)). Qed.
Lemma lem206355 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem206356 (q : Prop) : (term50 q) = (imp q).
Proof. exact (MK_COMB (@lem206355) (@lem206354 q)). Qed.
Lemma lem206358 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem206359 (q : Prop) : (True /\ q) = q.
Proof. exact (@lem206358 q). Qed.
Lemma lem206360 (q : Prop) : (term43 q) = (q -> q).
Proof. exact (MK_COMB (@lem206356 q) (@lem206359 q)). Qed.
Lemma lem206362 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem206363 (q : Prop) : (q -> q) = True.
Proof. exact (@lem206362 q). Qed.
Lemma lem206364 (q : Prop) : (term43 q) = True.
Proof. exact (TRANS (@lem206360 q) (@lem206363 q)). Qed.
Lemma lem206365 (q : Prop) : True = (term43 q).
Proof. exact (SYM (@lem206364 q)). Qed.
Lemma lem206366 (q : Prop) : term43 q.
Proof. exact (EQ_MP (@lem206365 q) (@lem0)). Qed.
Lemma lem206370 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem206371 (q : Prop) : (term51 q) = False.
Proof. exact (@lem206370 (False -> q)). Qed.
Lemma lem206372 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem206373 (q : Prop) : (term52 q) = (imp False).
Proof. exact (MK_COMB (@lem206372) (@lem206371 q)). Qed.
Lemma lem206375 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem206376 (q : Prop) : (False /\ q) = False.
Proof. exact (@lem206375 q). Qed.
Lemma lem206377 (q : Prop) : (term48 q) = (False -> False).
Proof. exact (MK_COMB (@lem206373 q) (@lem206376 q)). Qed.
Lemma lem206379 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem206380 : (False -> False) = True.
Proof. exact (@lem206379 False). Qed.
Lemma lem206381 (q : Prop) : (term48 q) = True.
Proof. exact (TRANS (@lem206377 q) (@lem206380)). Qed.
Lemma lem206382 (q : Prop) : True = (term48 q).
Proof. exact (SYM (@lem206381 q)). Qed.
Lemma lem206383 (q : Prop) : term48 q.
Proof. exact (EQ_MP (@lem206382 q) (@lem0)). Qed.
Lemma lem206384 (q : Prop) (p : Prop) (h1 : p = False) : term45 p q.
Proof. exact (EQ_MP (@lem206345 q p h1) (@lem206383 q)). Qed.
Lemma lem206385 (q : Prop) (p : Prop) (h1 : p = True) : term45 p q.
Proof. exact (EQ_MP (@lem206332 q p h1) (@lem206366 q)). Qed.
Lemma lem206388 (p : Prop) (q : Prop) : term45 p q.
Proof. exact (or_elim (@lem206307 p) (fun h0 : p = True => @lem206385 q p h0) (fun h0 : p = False => @lem206384 q p h0)). Qed.
Lemma lem206389 (p : Prop) (q : Prop) (h1 : term45 p q) : term45 p q.
Proof. exact (h1). Qed.
Lemma lem206390 (q : Prop) (p : Prop) (h1 : term53 q p) : term53 q p.
Proof. exact (h1). Qed.
Lemma lem206391 (p : Prop) (q : Prop) (h1 : term53 q p) (h2 : term45 p q) : p /\ q.
Proof. exact (@lem206389 p q h2 (@lem206390 q p h1)). Qed.
Lemma lem206392 (q : Prop) (p : Prop) (h1 : term53 q p) : term54 p q.
Proof. exact (fun h0 : term45 p q => @lem206391 p q h1 h0). Qed.
Lemma lem206393 (p : Prop) (q : Prop) (h1 : term45 p q) : term45 p q.
Proof. exact (h1). Qed.
Lemma lem206394 (p : Prop) (q : Prop) (h1 : term53 q p) (h2 : term45 p q) : p /\ q.
Proof. exact (@lem206392 q p h1 (@lem206393 p q h2)). Qed.
Lemma lem206395 (p : Prop) (q : Prop) (h1 : term45 p q) : term45 p q.
Proof. exact (fun h0 : term53 q p => @lem206394 p q h0 h1). Qed.
Lemma lem206396 (p : Prop) (q : Prop) : term55 p q.
Proof. exact (fun h0 : term45 p q => @lem206395 p q h0). Qed.
Lemma lem206399 (p : Prop) (q : Prop) : term45 p q.
Proof. exact (@lem206396 p q (@lem206388 p q)). Qed.
Lemma lem206400 : term56.
Proof. exact (@lem206399 term57 term58). Qed.
Lemma lem206404 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term59 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem206405 (p : Prop) (q : Prop) (p' : Prop) : term60 p q p'.
Proof. exact (fun q' : Prop => @lem206404 p q p' q'). Qed.
Lemma lem206406 (p : Prop) (q : Prop) : term61 p q.
Proof. exact (fun p' : Prop => @lem206405 p q p'). Qed.
Lemma lem206407 : term62.
Proof. exact (@lem206406 term57 term58). Qed.
Lemma lem206408 (p' : Prop) : term63 p'.
Proof. exact (@lem206407 p'). Qed.
Lemma lem206409 (p' : Prop) : (term63 p') = (term64 p').
Proof. exact (eq_refl (term63 p')). Qed.
Lemma lem206410 (p' : Prop) : term64 p'.
Proof. exact (EQ_MP (@lem206409 p') (@lem206408 p')). Qed.
Lemma lem206411 (p' : Prop) (q' : Prop) : term65 p' q'.
Proof. exact (@lem206410 p' q'). Qed.
Lemma lem206412 (p' : Prop) (q' : Prop) : (term65 p' q') = (term66 p' q').
Proof. exact (eq_refl (term65 p' q')). Qed.
Lemma lem206413 (p' : Prop) (q' : Prop) : term66 p' q'.
Proof. exact (EQ_MP (@lem206412 p' q') (@lem206411 p' q')). Qed.
Lemma lem206429 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem206430 (p : nat) (m : nat) (n : nat) : (term67 m n p) = (term68 p m n).
Proof. exact (@lem206429 p (Nat.mul m n)). Qed.
Lemma lem206436 : Nat.modulo = Nat.modulo.
Proof. exact (eq_refl Nat.modulo). Qed.
Lemma lem206437 (p : nat) (m : nat) (n : nat) : (term69 m n p) = (term70 p m n).
Proof. exact (MK_COMB (@lem206436) (@lem206430 p m n)). Qed.
Lemma lem206443 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem206444 (p : nat) (m : nat) (n : nat) : (term71 m p n) = (term72 p m n).
Proof. exact (MK_COMB (@lem206437 p m n) (@lem206443 n)). Qed.
Lemma lem206450 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem206451 (p : nat) (m : nat) (n : nat) : (term73 m p n) = (term74 p m n).
Proof. exact (MK_COMB (@lem206450) (@lem206444 p m n)). Qed.
Lemma lem206457 (p : nat) (n : nat) : (Nat.modulo p n) = (Nat.modulo p n).
Proof. exact (eq_refl (Nat.modulo p n)). Qed.
Lemma lem206458 (m : nat) (p : nat) (n : nat) : ((term71 m p n) = (Nat.modulo p n)) = ((term72 p m n) = (Nat.modulo p n)).
Proof. exact (MK_COMB (@lem206451 p m n) (@lem206457 p n)). Qed.
Lemma lem206466 (m : nat) (n : nat) : (term75 m n) = (term76 m n).
Proof. exact (fun_ext (fun p : nat => @lem206458 m p n)). Qed.
Lemma lem206474 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem206475 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (MK_COMB (@lem206474) (@lem206466 m n)). Qed.
Lemma lem206487 (m : nat) : (term79 m) = (term80 m).
Proof. exact (fun_ext (fun n : nat => @lem206475 m n)). Qed.
Lemma lem206499 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem206500 (m : nat) : (term81 m) = (term82 m).
Proof. exact (MK_COMB (@lem206499) (@lem206487 m)). Qed.
Lemma lem206516 : term83 = term84.
Proof. exact (fun_ext (fun m : nat => @lem206500 m)). Qed.
Lemma lem206532 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem206533 : term57 = term85.
Proof. exact (MK_COMB (@lem206532) (@lem206516)). Qed.
Lemma lem206553 (q' : Prop) : term86 q'.
Proof. exact (@lem206413 term85 q'). Qed.
Lemma lem206554 (q' : Prop) : term87 q'.
Proof. exact (@lem206553 q' (@lem206533)). Qed.
Lemma lem206555 (h1 : term85) : term85.
Proof. exact (h1). Qed.
Lemma lem206556 (m : nat) (h1 : term85) : term88 m.
Proof. exact (@lem206555 h1 m). Qed.
Lemma lem206557 (m : nat) : (term88 m) = (term82 m).
Proof. exact (eq_refl (term88 m)). Qed.
Lemma lem206558 (m : nat) (h1 : term85) : term82 m.
Proof. exact (EQ_MP (@lem206557 m) (@lem206556 m h1)). Qed.
Lemma lem206559 (m : nat) (n : nat) (h1 : term85) : term89 m n.
Proof. exact (@lem206558 m h1 n). Qed.
Lemma lem206560 (m : nat) (n : nat) : (term89 m n) = (term78 m n).
Proof. exact (eq_refl (term89 m n)). Qed.
Lemma lem206561 (m : nat) (n : nat) (h1 : term85) : term78 m n.
Proof. exact (EQ_MP (@lem206560 m n) (@lem206559 m n h1)). Qed.
Lemma lem206562 (m : nat) (n : nat) (p : nat) (h1 : term85) : term90 m n p.
Proof. exact (@lem206561 m n h1 p). Qed.
Lemma lem206563 (m : nat) (p : nat) (n : nat) : (term90 m n p) = ((term72 p m n) = (Nat.modulo p n)).
Proof. exact (eq_refl (term90 m n p)). Qed.
Lemma lem206582 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem206583 (p : nat) (n : nat) (m : nat) : (term67 n m p) = (term68 p n m).
Proof. exact (@lem206582 p (Nat.mul n m)). Qed.
Lemma lem206588 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (proj1 (@lem83517 n m (@el nat))). Qed.
Lemma lem206589 (m : nat) (n : nat) : (Nat.mul n m) = (Nat.mul m n).
Proof. exact (@lem206588 m n). Qed.
Lemma lem206592 (p : nat) : (Nat.add p) = (Nat.add p).
Proof. exact (eq_refl (Nat.add p)). Qed.
Lemma lem206593 (p : nat) (m : nat) (n : nat) : (term68 p n m) = (term68 p m n).
Proof. exact (MK_COMB (@lem206592 p) (@lem206589 m n)). Qed.
Lemma lem206599 (p : nat) (m : nat) (n : nat) : (term67 n m p) = (term68 p m n).
Proof. exact (TRANS (@lem206583 p n m) (@lem206593 p m n)). Qed.
Lemma lem206600 : Nat.modulo = Nat.modulo.
Proof. exact (eq_refl Nat.modulo). Qed.
Lemma lem206601 (p : nat) (m : nat) (n : nat) : (term69 n m p) = (term70 p m n).
Proof. exact (MK_COMB (@lem206600) (@lem206599 p m n)). Qed.
Lemma lem206607 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem206608 (p : nat) (m : nat) (n : nat) : (term91 m p n) = (term72 p m n).
Proof. exact (MK_COMB (@lem206601 p m n) (@lem206607 n)). Qed.
Lemma lem206610 (m : nat) (p : nat) (n : nat) (h1 : term85) : (term72 p m n) = (Nat.modulo p n).
Proof. exact (EQ_MP (@lem206563 m p n) (@lem206562 m n p h1)). Qed.
Lemma lem206611 (m : nat) (p : nat) (n : nat) (h1 : term85) : (term91 m p n) = (Nat.modulo p n).
Proof. exact (TRANS (@lem206608 p m n) (@lem206610 m p n h1)). Qed.
Lemma lem206612 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem206613 (m : nat) (p : nat) (n : nat) (h1 : term85) : (term92 m p n) = (term93 p n).
Proof. exact (MK_COMB (@lem206612) (@lem206611 m p n h1)). Qed.
Lemma lem206614 (p : nat) (n : nat) : (Nat.modulo p n) = (Nat.modulo p n).
Proof. exact (eq_refl (Nat.modulo p n)). Qed.
Lemma lem206615 (m : nat) (p : nat) (n : nat) (h1 : term85) : ((term91 m p n) = (Nat.modulo p n)) = ((Nat.modulo p n) = (Nat.modulo p n)).
Proof. exact (MK_COMB (@lem206613 m p n h1) (@lem206614 p n)). Qed.
Lemma lem206617 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem206618 (x : nat) : (x = x) = True.
Proof. exact (@lem206617 nat x). Qed.
Lemma lem206619 (p : nat) (n : nat) : ((Nat.modulo p n) = (Nat.modulo p n)) = True.
Proof. exact (@lem206618 (Nat.modulo p n)). Qed.
Lemma lem206620 (m : nat) (p : nat) (n : nat) (h1 : term85) : ((term91 m p n) = (Nat.modulo p n)) = True.
Proof. exact (TRANS (@lem206615 m p n h1) (@lem206619 p n)). Qed.
Lemma lem206621 (m : nat) (n : nat) (h1 : term85) : (term94 m n) = term95.
Proof. exact (fun_ext (fun p : nat => @lem206620 m p n h1)). Qed.
Lemma lem206622 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem206623 (m : nat) (n : nat) (h1 : term85) : (term96 m n) = term97.
Proof. exact (MK_COMB (@lem206622) (@lem206621 m n h1)). Qed.
Lemma lem206625 {A : Type'} (t : Prop) : (term98 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem206626 (t : Prop) : (term99 t) = t.
Proof. exact (@lem206625 nat t). Qed.
Lemma lem206627 : term97 = True.
Proof. exact (@lem206626 True). Qed.
Lemma lem206628 (m : nat) (n : nat) (h1 : term85) : (term96 m n) = True.
Proof. exact (TRANS (@lem206623 m n h1) (@lem206627)). Qed.
Lemma lem206629 (m : nat) (h1 : term85) : (term100 m) = term95.
Proof. exact (fun_ext (fun n : nat => @lem206628 m n h1)). Qed.
Lemma lem206630 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem206631 (m : nat) (h1 : term85) : (term101 m) = term97.
Proof. exact (MK_COMB (@lem206630) (@lem206629 m h1)). Qed.
Lemma lem206633 {A : Type'} (t : Prop) : (term98 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem206634 (t : Prop) : (term99 t) = t.
Proof. exact (@lem206633 nat t). Qed.
Lemma lem206635 : term97 = True.
Proof. exact (@lem206634 True). Qed.
Lemma lem206636 (m : nat) (h1 : term85) : (term101 m) = True.
Proof. exact (TRANS (@lem206631 m h1) (@lem206635)). Qed.
Lemma lem206637 (h1 : term85) : term102 = term95.
Proof. exact (fun_ext (fun m : nat => @lem206636 m h1)). Qed.
Lemma lem206638 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem206639 (h1 : term85) : term103 = term97.
Proof. exact (MK_COMB (@lem206638) (@lem206637 h1)). Qed.
Lemma lem206641 {A : Type'} (t : Prop) : (term98 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem206642 (t : Prop) : (term99 t) = t.
Proof. exact (@lem206641 nat t). Qed.
Lemma lem206643 : term97 = True.
Proof. exact (@lem206642 True). Qed.
Lemma lem206644 (h1 : term85) : term103 = True.
Proof. exact (TRANS (@lem206639 h1) (@lem206643)). Qed.
Lemma lem206645 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem206646 (h1 : term85) : term104 = (and True).
Proof. exact (MK_COMB (@lem206645) (@lem206644 h1)). Qed.
Lemma lem206664 (m : nat) (p : nat) (n : nat) (h1 : term85) : (term72 p m n) = (Nat.modulo p n).
Proof. exact (EQ_MP (@lem206563 m p n) (@lem206562 m n p h1)). Qed.
Lemma lem206665 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem206666 (m : nat) (p : nat) (n : nat) (h1 : term85) : (term74 p m n) = (term93 p n).
Proof. exact (MK_COMB (@lem206665) (@lem206664 m p n h1)). Qed.
Lemma lem206667 (p : nat) (n : nat) : (Nat.modulo p n) = (Nat.modulo p n).
Proof. exact (eq_refl (Nat.modulo p n)). Qed.
Lemma lem206668 (m : nat) (p : nat) (n : nat) (h1 : term85) : ((term72 p m n) = (Nat.modulo p n)) = ((Nat.modulo p n) = (Nat.modulo p n)).
Proof. exact (MK_COMB (@lem206666 m p n h1) (@lem206667 p n)). Qed.
Lemma lem206670 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem206671 (x : nat) : (x = x) = True.
Proof. exact (@lem206670 nat x). Qed.
Lemma lem206672 (p : nat) (n : nat) : ((Nat.modulo p n) = (Nat.modulo p n)) = True.
Proof. exact (@lem206671 (Nat.modulo p n)). Qed.
Lemma lem206673 (m : nat) (p : nat) (n : nat) (h1 : term85) : ((term72 p m n) = (Nat.modulo p n)) = True.
Proof. exact (TRANS (@lem206668 m p n h1) (@lem206672 p n)). Qed.
Lemma lem206674 (m : nat) (n : nat) (h1 : term85) : (term76 m n) = term95.
Proof. exact (fun_ext (fun p : nat => @lem206673 m p n h1)). Qed.
Lemma lem206675 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem206676 (m : nat) (n : nat) (h1 : term85) : (term78 m n) = term97.
Proof. exact (MK_COMB (@lem206675) (@lem206674 m n h1)). Qed.
Lemma lem206678 {A : Type'} (t : Prop) : (term98 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem206679 (t : Prop) : (term99 t) = t.
Proof. exact (@lem206678 nat t). Qed.
Lemma lem206680 : term97 = True.
Proof. exact (@lem206679 True). Qed.
Lemma lem206681 (m : nat) (n : nat) (h1 : term85) : (term78 m n) = True.
Proof. exact (TRANS (@lem206676 m n h1) (@lem206680)). Qed.
Lemma lem206682 (m : nat) (h1 : term85) : (term80 m) = term95.
Proof. exact (fun_ext (fun n : nat => @lem206681 m n h1)). Qed.
Lemma lem206683 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem206684 (m : nat) (h1 : term85) : (term82 m) = term97.
Proof. exact (MK_COMB (@lem206683) (@lem206682 m h1)). Qed.
Lemma lem206686 {A : Type'} (t : Prop) : (term98 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem206687 (t : Prop) : (term99 t) = t.
Proof. exact (@lem206686 nat t). Qed.
Lemma lem206688 : term97 = True.
Proof. exact (@lem206687 True). Qed.
Lemma lem206689 (m : nat) (h1 : term85) : (term82 m) = True.
Proof. exact (TRANS (@lem206684 m h1) (@lem206688)). Qed.
Lemma lem206690 (h1 : term85) : term84 = term95.
Proof. exact (fun_ext (fun m : nat => @lem206689 m h1)). Qed.
Lemma lem206691 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem206692 (h1 : term85) : term85 = term97.
Proof. exact (MK_COMB (@lem206691) (@lem206690 h1)). Qed.
Lemma lem206694 {A : Type'} (t : Prop) : (term98 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem206695 (t : Prop) : (term99 t) = t.
Proof. exact (@lem206694 nat t). Qed.
Lemma lem206696 : term97 = True.
Proof. exact (@lem206695 True). Qed.
Lemma lem206697 (h1 : term85) : term85 = True.
Proof. exact (TRANS (@lem206692 h1) (@lem206696)). Qed.
Lemma lem206698 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem206699 (h1 : term85) : term105 = (and True).
Proof. exact (MK_COMB (@lem206698) (@lem206697 h1)). Qed.
Lemma lem206720 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (proj1 (@lem83517 n m (@el nat))). Qed.
Lemma lem206721 (m : nat) (n : nat) : (Nat.mul n m) = (Nat.mul m n).
Proof. exact (@lem206720 m n). Qed.
Lemma lem206724 (p : nat) : (Nat.add p) = (Nat.add p).
Proof. exact (eq_refl (Nat.add p)). Qed.
Lemma lem206725 (p : nat) (m : nat) (n : nat) : (term68 p n m) = (term68 p m n).
Proof. exact (MK_COMB (@lem206724 p) (@lem206721 m n)). Qed.
Lemma lem206731 : Nat.modulo = Nat.modulo.
Proof. exact (eq_refl Nat.modulo). Qed.
Lemma lem206732 (p : nat) (m : nat) (n : nat) : (term70 p n m) = (term70 p m n).
Proof. exact (MK_COMB (@lem206731) (@lem206725 p m n)). Qed.
Lemma lem206738 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem206739 (p : nat) (m : nat) (n : nat) : (term106 p m n) = (term72 p m n).
Proof. exact (MK_COMB (@lem206732 p m n) (@lem206738 n)). Qed.
Lemma lem206741 (m : nat) (p : nat) (n : nat) (h1 : term85) : (term72 p m n) = (Nat.modulo p n).
Proof. exact (EQ_MP (@lem206563 m p n) (@lem206562 m n p h1)). Qed.
Lemma lem206742 (m : nat) (p : nat) (n : nat) (h1 : term85) : (term106 p m n) = (Nat.modulo p n).
Proof. exact (TRANS (@lem206739 p m n) (@lem206741 m p n h1)). Qed.
Lemma lem206743 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem206744 (m : nat) (p : nat) (n : nat) (h1 : term85) : (term107 p m n) = (term93 p n).
Proof. exact (MK_COMB (@lem206743) (@lem206742 m p n h1)). Qed.
Lemma lem206745 (p : nat) (n : nat) : (Nat.modulo p n) = (Nat.modulo p n).
Proof. exact (eq_refl (Nat.modulo p n)). Qed.
Lemma lem206746 (m : nat) (p : nat) (n : nat) (h1 : term85) : ((term106 p m n) = (Nat.modulo p n)) = ((Nat.modulo p n) = (Nat.modulo p n)).
Proof. exact (MK_COMB (@lem206744 m p n h1) (@lem206745 p n)). Qed.
Lemma lem206748 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem206749 (x : nat) : (x = x) = True.
Proof. exact (@lem206748 nat x). Qed.
Lemma lem206750 (p : nat) (n : nat) : ((Nat.modulo p n) = (Nat.modulo p n)) = True.
Proof. exact (@lem206749 (Nat.modulo p n)). Qed.
Lemma lem206751 (m : nat) (p : nat) (n : nat) (h1 : term85) : ((term106 p m n) = (Nat.modulo p n)) = True.
Proof. exact (TRANS (@lem206746 m p n h1) (@lem206750 p n)). Qed.
Lemma lem206752 (m : nat) (n : nat) (h1 : term85) : (term108 m n) = term95.
Proof. exact (fun_ext (fun p : nat => @lem206751 m p n h1)). Qed.
Lemma lem206753 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem206754 (m : nat) (n : nat) (h1 : term85) : (term109 m n) = term97.
Proof. exact (MK_COMB (@lem206753) (@lem206752 m n h1)). Qed.
Lemma lem206756 {A : Type'} (t : Prop) : (term98 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem206757 (t : Prop) : (term99 t) = t.
Proof. exact (@lem206756 nat t). Qed.
Lemma lem206758 : term97 = True.
Proof. exact (@lem206757 True). Qed.
Lemma lem206759 (m : nat) (n : nat) (h1 : term85) : (term109 m n) = True.
Proof. exact (TRANS (@lem206754 m n h1) (@lem206758)). Qed.
Lemma lem206760 (m : nat) (h1 : term85) : (term110 m) = term95.
Proof. exact (fun_ext (fun n : nat => @lem206759 m n h1)). Qed.
Lemma lem206761 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem206762 (m : nat) (h1 : term85) : (term111 m) = term97.
Proof. exact (MK_COMB (@lem206761) (@lem206760 m h1)). Qed.
Lemma lem206764 {A : Type'} (t : Prop) : (term98 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem206765 (t : Prop) : (term99 t) = t.
Proof. exact (@lem206764 nat t). Qed.
Lemma lem206766 : term97 = True.
Proof. exact (@lem206765 True). Qed.
Lemma lem206767 (m : nat) (h1 : term85) : (term111 m) = True.
Proof. exact (TRANS (@lem206762 m h1) (@lem206766)). Qed.
Lemma lem206768 (h1 : term85) : term112 = term95.
Proof. exact (fun_ext (fun m : nat => @lem206767 m h1)). Qed.
Lemma lem206769 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem206770 (h1 : term85) : term113 = term97.
Proof. exact (MK_COMB (@lem206769) (@lem206768 h1)). Qed.
Lemma lem206772 {A : Type'} (t : Prop) : (term98 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem206773 (t : Prop) : (term99 t) = t.
Proof. exact (@lem206772 nat t). Qed.
Lemma lem206774 : term97 = True.
Proof. exact (@lem206773 True). Qed.
Lemma lem206775 (h1 : term85) : term113 = True.
Proof. exact (TRANS (@lem206770 h1) (@lem206774)). Qed.
Lemma lem206776 (h1 : term85) : term114 = (True /\ True).
Proof. exact (MK_COMB (@lem206699 h1) (@lem206775 h1)). Qed.
Lemma lem206778 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem206779 : (True /\ True) = True.
Proof. exact (@lem206778 True). Qed.
Lemma lem206780 (h1 : term85) : term114 = True.
Proof. exact (TRANS (@lem206776 h1) (@lem206779)). Qed.
Lemma lem206781 (h1 : term85) : term58 = (True /\ True).
Proof. exact (MK_COMB (@lem206646 h1) (@lem206780 h1)). Qed.
Lemma lem206783 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem206784 : (True /\ True) = True.
Proof. exact (@lem206783 True). Qed.
Lemma lem206785 (h1 : term85) : term58 = True.
Proof. exact (TRANS (@lem206781 h1) (@lem206784)). Qed.
Lemma lem206786 : term115.
Proof. exact (fun h0 : term85 => @lem206785 h0). Qed.
Lemma lem206787 : term116.
Proof. exact (@lem206554 True). Qed.
Lemma lem206788 : term117 = term118.
Proof. exact (@lem206787 (@lem206786)). Qed.
Lemma lem206790 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem206791 : term118 = True.
Proof. exact (@lem206790 term85). Qed.
Lemma lem206792 : term117 = True.
Proof. exact (TRANS (@lem206788) (@lem206791)). Qed.
Lemma lem206793 : True = term117.
Proof. exact (SYM (@lem206792)). Qed.
Lemma lem206794 : term117.
Proof. exact (EQ_MP (@lem206793) (@lem0)). Qed.
Lemma lem206815 : term119.
Proof. exact (proj1 (@lem77629)). Qed.
Lemma lem206816 (n : nat) : term120 n.
Proof. exact (@lem206815 n). Qed.
Lemma lem206817 (n : nat) : (term120 n) = ((term121 n) = n).
Proof. exact (eq_refl (term120 n)). Qed.
Lemma lem206819 : term122.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem206845 : term123.
Proof. exact (proj1 (@lem206819)). Qed.
Lemma lem206846 (m : nat) : term124 m.
Proof. exact (@lem206845 m). Qed.
Lemma lem206847 (m : nat) : (term124 m) = ((term125 m) = (NUMERAL 0)).
Proof. exact (eq_refl (term124 m)). Qed.
Lemma lem206856 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem206857 (m : nat) : (Nat.mul m) = (Nat.mul m).
Proof. exact (eq_refl (Nat.mul m)). Qed.
Lemma lem206858 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.mul m n) = (term125 m).
Proof. exact (MK_COMB (@lem206857 m) (@lem206856 n h1)). Qed.
Lemma lem206860 (m : nat) : (term125 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem206847 m) (@lem206846 m)). Qed.
Lemma lem206861 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.mul m n) = (NUMERAL 0).
Proof. exact (TRANS (@lem206858 m n h1) (@lem206860 m)). Qed.
Lemma lem206862 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem206863 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term126 m n) = term127.
Proof. exact (MK_COMB (@lem206862) (@lem206861 m n h1)). Qed.
Lemma lem206864 (p : nat) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem206865 (m : nat) (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term67 m n p) = (term121 p).
Proof. exact (MK_COMB (@lem206863 m n h1) (@lem206864 p)). Qed.
Lemma lem206867 (n : nat) : (term121 n) = n.
Proof. exact (EQ_MP (@lem206817 n) (@lem206816 n)). Qed.
Lemma lem206868 (p : nat) : (term121 p) = p.
Proof. exact (@lem206867 p). Qed.
Lemma lem206869 (m : nat) (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term67 m n p) = p.
Proof. exact (TRANS (@lem206865 m p n h1) (@lem206868 p)). Qed.
Lemma lem206870 : Nat.modulo = Nat.modulo.
Proof. exact (eq_refl Nat.modulo). Qed.
Lemma lem206871 (m : nat) (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term69 m n p) = (Nat.modulo p).
Proof. exact (MK_COMB (@lem206870) (@lem206869 m p n h1)). Qed.
Lemma lem206873 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem206874 (m : nat) (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term71 m p n) = (term128 p).
Proof. exact (MK_COMB (@lem206871 m p n h1) (@lem206873 n h1)). Qed.
Lemma lem206875 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem206876 (m : nat) (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term73 m p n) = (term129 p).
Proof. exact (MK_COMB (@lem206875) (@lem206874 m p n h1)). Qed.
Lemma lem206878 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem206879 (p : nat) : (Nat.modulo p) = (Nat.modulo p).
Proof. exact (eq_refl (Nat.modulo p)). Qed.
Lemma lem206880 (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.modulo p n) = (term128 p).
Proof. exact (MK_COMB (@lem206879 p) (@lem206878 n h1)). Qed.
Lemma lem206881 (m : nat) (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : ((term71 m p n) = (Nat.modulo p n)) = ((term128 p) = (term128 p)).
Proof. exact (MK_COMB (@lem206876 m p n h1) (@lem206880 p n h1)). Qed.
Lemma lem206883 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem206884 (x : nat) : (x = x) = True.
Proof. exact (@lem206883 nat x). Qed.
Lemma lem206885 (p : nat) : ((term128 p) = (term128 p)) = True.
Proof. exact (@lem206884 (term128 p)). Qed.
Lemma lem206886 (m : nat) (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : ((term71 m p n) = (Nat.modulo p n)) = True.
Proof. exact (TRANS (@lem206881 m p n h1) (@lem206885 p)). Qed.
Lemma lem206887 (m : nat) (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : True = ((term71 m p n) = (Nat.modulo p n)).
Proof. exact (SYM (@lem206886 m p n h1)). Qed.
Lemma lem206888 (m : nat) (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term71 m p n) = (Nat.modulo p n).
Proof. exact (EQ_MP (@lem206887 m p n h1) (@lem0)). Qed.
Lemma lem206965 (m : nat) (n : nat) (r : nat) : term27 m n r.
Proof. exact (EQ_MP (@lem206280 m n r) (@lem206279 m n r)). Qed.
Lemma lem206966 (m : nat) (p : nat) (n : nat) : term130 m p n.
Proof. exact (@lem206965 (term67 m n p) n (Nat.modulo p n)). Qed.
Lemma lem206967 (m : nat) : term131 m.
Proof. exact (@lem157261 m). Qed.
Lemma lem206968 (m : nat) : (term131 m) = (term132 m).
Proof. exact (eq_refl (term131 m)). Qed.
Lemma lem206969 (m : nat) : term132 m.
Proof. exact (EQ_MP (@lem206968 m) (@lem206967 m)). Qed.
Lemma lem206970 (m : nat) (n : nat) : term133 m n.
Proof. exact (@lem206969 m n). Qed.
Lemma lem206971 (m : nat) (n : nat) : (term133 m n) = (term134 m n).
Proof. exact (eq_refl (term133 m n)). Qed.
Lemma lem206972 (m : nat) (n : nat) : term134 m n.
Proof. exact (EQ_MP (@lem206971 m n) (@lem206970 m n)). Qed.
Lemma lem206973 (n : nat) (h1 : term37 n) : term37 n.
Proof. exact (h1). Qed.
Lemma lem206974 (m : nat) (n : nat) (h1 : term37 n) : term135 m n.
Proof. exact (@lem206972 m n (@lem206973 n h1)). Qed.
Lemma lem206975 (m : nat) (n : nat) (h1 : term37 n) : term136 m n.
Proof. exact (proj2 (@lem206974 m n h1)). Qed.
Lemma lem206976 (m : nat) (n : nat) : (term136 m n) = ((term136 m n) = True).
Proof. exact (@lem7 (term136 m n)). Qed.
Lemma lem206977 (m : nat) (n : nat) (h1 : term37 n) : (term136 m n) = True.
Proof. exact (EQ_MP (@lem206976 m n) (@lem206975 m n h1)). Qed.
Lemma lem206983 (m : nat) (n : nat) (h1 : term37 n) : m = (term137 m n).
Proof. exact (proj1 (@lem206974 m n h1)). Qed.
Lemma lem206988 (m : nat) (n : nat) : term138 m n.
Proof. exact (fun h0 : term37 n => @lem206983 m n h0). Qed.
Lemma lem206989 (n : nat) (h1 : term37 n) : term37 n.
Proof. exact (h1). Qed.
Lemma lem206990 (m : nat) (n : nat) (h1 : term37 n) : m = (term137 m n).
Proof. exact (@lem206988 m n (@lem206989 n h1)). Qed.
Lemma lem206991 (m : nat) (n : nat) : (m = (term137 m n)) = ((m = (term137 m n)) = True).
Proof. exact (@lem7 (m = (term137 m n))). Qed.
Lemma lem206992 (m : nat) (n : nat) (h1 : term37 n) : (m = (term137 m n)) = True.
Proof. exact (EQ_MP (@lem206991 m n) (@lem206990 m n h1)). Qed.
Lemma lem206994 (m : nat) : term139 m.
Proof. exact (@lem79639 m). Qed.
Lemma lem206995 (m : nat) : (term139 m) = (term140 m).
Proof. exact (eq_refl (term139 m)). Qed.
Lemma lem206996 (m : nat) : term140 m.
Proof. exact (EQ_MP (@lem206995 m) (@lem206994 m)). Qed.
Lemma lem206997 (m : nat) (n : nat) : term141 m n.
Proof. exact (@lem206996 m n). Qed.
Lemma lem206998 (m : nat) (n : nat) : (term141 m n) = (term142 m n).
Proof. exact (eq_refl (term141 m n)). Qed.
Lemma lem206999 (m : nat) (n : nat) : term142 m n.
Proof. exact (EQ_MP (@lem206998 m n) (@lem206997 m n)). Qed.
Lemma lem207000 (m : nat) (n : nat) (p : nat) : term143 m n p.
Proof. exact (@lem206999 m n p). Qed.
Lemma lem207001 (m : nat) (n : nat) (p : nat) : (term143 m n p) = (((Nat.add m n) = (Nat.add m p)) = (n = p)).
Proof. exact (eq_refl (term143 m n p)). Qed.
Lemma lem207003 (m : nat) : term144 m.
Proof. exact (@lem206246 m). Qed.
Lemma lem207004 (m : nat) : (term144 m) = (term9 m).
Proof. exact (eq_refl (term144 m)). Qed.
Lemma lem207005 (m : nat) : term9 m.
Proof. exact (EQ_MP (@lem207004 m) (@lem207003 m)). Qed.
Lemma lem207006 (m : nat) (n : nat) : term145 m n.
Proof. exact (@lem207005 m n). Qed.
Lemma lem207007 (m : nat) (n : nat) : (term145 m n) = (term5 m n).
Proof. exact (eq_refl (term145 m n)). Qed.
Lemma lem207008 (m : nat) (n : nat) : term5 m n.
Proof. exact (EQ_MP (@lem207007 m n) (@lem207006 m n)). Qed.
Lemma lem207009 (m : nat) (n : nat) (p : nat) : term146 m n p.
Proof. exact (@lem207008 m n p). Qed.
Lemma lem207010 (m : nat) (n : nat) (p : nat) : (term146 m n p) = ((term1 m n p) = (term0 m n p)).
Proof. exact (eq_refl (term146 m n p)). Qed.
Lemma lem207012 (m : nat) : term147 m.
Proof. exact (@lem82128 m). Qed.
Lemma lem207013 (m : nat) : (term147 m) = (term148 m).
Proof. exact (eq_refl (term147 m)). Qed.
Lemma lem207014 (m : nat) : term148 m.
Proof. exact (EQ_MP (@lem207013 m) (@lem207012 m)). Qed.
Lemma lem207015 (m : nat) (n : nat) : term149 m n.
Proof. exact (@lem207014 m n). Qed.
Lemma lem207016 (m : nat) (n : nat) : (term149 m n) = (term150 m n).
Proof. exact (eq_refl (term149 m n)). Qed.
Lemma lem207017 (m : nat) (n : nat) : term150 m n.
Proof. exact (EQ_MP (@lem207016 m n) (@lem207015 m n)). Qed.
Lemma lem207018 (m : nat) (n : nat) (p : nat) : term151 m n p.
Proof. exact (@lem207017 m n p). Qed.
Lemma lem207019 (m : nat) (n : nat) (p : nat) : (term151 m n p) = ((term152 m n p) = (term153 m n p)).
Proof. exact (eq_refl (term151 m n p)). Qed.
Lemma lem207021 (n : nat) : term154 n.
Proof. exact (@lem82 (n = (NUMERAL 0))). Qed.
Lemma lem207077 (m : nat) (n : nat) (p : nat) : (term152 m n p) = (term153 m n p).
Proof. exact (EQ_MP (@lem207019 m n p) (@lem207018 m n p)). Qed.
Lemma lem207078 (m : nat) (p : nat) (n : nat) : (term155 m p n) = (term156 m p n).
Proof. exact (@lem207077 m (Nat.div p n) n). Qed.
Lemma lem207113 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem207114 (m : nat) (p : nat) (n : nat) : (term157 m p n) = (term158 m p n).
Proof. exact (MK_COMB (@lem207113) (@lem207078 m p n)). Qed.
Lemma lem207163 (p : nat) (n : nat) : (Nat.modulo p n) = (Nat.modulo p n).
Proof. exact (eq_refl (Nat.modulo p n)). Qed.
Lemma lem207164 (m : nat) (p : nat) (n : nat) : (term159 m p n) = (term160 m p n).
Proof. exact (MK_COMB (@lem207114 m p n) (@lem207163 p n)). Qed.
Lemma lem207166 (m : nat) (n : nat) (p : nat) : (term1 m n p) = (term0 m n p).
Proof. exact (EQ_MP (@lem207010 m n p) (@lem207009 m n p)). Qed.
Lemma lem207167 (m : nat) (p : nat) (n : nat) : (term160 m p n) = (term161 m p n).
Proof. exact (@lem207166 (Nat.mul m n) (term162 p n) (Nat.modulo p n)). Qed.
Lemma lem207218 (m : nat) (p : nat) (n : nat) : (term159 m p n) = (term161 m p n).
Proof. exact (TRANS (@lem207164 m p n) (@lem207167 m p n)). Qed.
Lemma lem207219 (m : nat) (n : nat) (p : nat) : (term163 m n p) = (term163 m n p).
Proof. exact (eq_refl (term163 m n p)). Qed.
Lemma lem207220 (m : nat) (p : nat) (n : nat) : ((term67 m n p) = (term159 m p n)) = ((term67 m n p) = (term161 m p n)).
Proof. exact (MK_COMB (@lem207219 m n p) (@lem207218 m p n)). Qed.
Lemma lem207222 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem207001 m n p) (@lem207000 m n p)). Qed.
Lemma lem207223 (m : nat) (p : nat) (n : nat) : ((term67 m n p) = (term161 m p n)) = (p = (term137 p n)).
Proof. exact (@lem207222 (Nat.mul m n) p (term137 p n)). Qed.
Lemma lem207227 (m : nat) (n : nat) : term164 m n.
Proof. exact (fun h0 : term37 n => @lem206992 m n h0). Qed.
Lemma lem207228 (p : nat) (n : nat) : term164 p n.
Proof. exact (@lem207227 p n). Qed.
Lemma lem207234 (n : nat) (h1 : term37 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem207021 n (@lem206286 n h1)). Qed.
Lemma lem207237 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem207238 (n : nat) (h1 : term37 n) : (term37 n) = (~ False).
Proof. exact (MK_COMB (@lem207237) (@lem207234 n h1)). Qed.
Lemma lem207240 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem207243 (n : nat) (h1 : term37 n) : (term37 n) = True.
Proof. exact (TRANS (@lem207238 n h1) (@lem207240)). Qed.
Lemma lem207244 (n : nat) (h1 : term37 n) : True = (term37 n).
Proof. exact (SYM (@lem207243 n h1)). Qed.
Lemma lem207245 (n : nat) (h1 : term37 n) : term37 n.
Proof. exact (EQ_MP (@lem207244 n h1) (@lem0)). Qed.
Lemma lem207246 (p : nat) (n : nat) (h1 : term37 n) : (p = (term137 p n)) = True.
Proof. exact (@lem207228 p n (@lem207245 n h1)). Qed.
Lemma lem207249 (m : nat) (p : nat) (n : nat) (h1 : term37 n) : ((term67 m n p) = (term161 m p n)) = True.
Proof. exact (TRANS (@lem207223 m p n) (@lem207246 p n h1)). Qed.
Lemma lem207250 (m : nat) (p : nat) (n : nat) (h1 : term37 n) : ((term67 m n p) = (term159 m p n)) = True.
Proof. exact (TRANS (@lem207220 m p n) (@lem207249 m p n h1)). Qed.
Lemma lem207251 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem207252 (m : nat) (p : nat) (n : nat) (h1 : term37 n) : (term165 m p n) = (and True).
Proof. exact (MK_COMB (@lem207251) (@lem207250 m p n h1)). Qed.
Lemma lem207260 (m : nat) (n : nat) : term166 m n.
Proof. exact (fun h0 : term37 n => @lem206977 m n h0). Qed.
Lemma lem207261 (p : nat) (n : nat) : term166 p n.
Proof. exact (@lem207260 p n). Qed.
Lemma lem207267 (n : nat) (h1 : term37 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem207021 n (@lem206286 n h1)). Qed.
Lemma lem207270 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem207271 (n : nat) (h1 : term37 n) : (term37 n) = (~ False).
Proof. exact (MK_COMB (@lem207270) (@lem207267 n h1)). Qed.
Lemma lem207273 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem207276 (n : nat) (h1 : term37 n) : (term37 n) = True.
Proof. exact (TRANS (@lem207271 n h1) (@lem207273)). Qed.
Lemma lem207277 (n : nat) (h1 : term37 n) : True = (term37 n).
Proof. exact (SYM (@lem207276 n h1)). Qed.
Lemma lem207278 (n : nat) (h1 : term37 n) : term37 n.
Proof. exact (EQ_MP (@lem207277 n h1) (@lem0)). Qed.
Lemma lem207279 (p : nat) (n : nat) (h1 : term37 n) : (term136 p n) = True.
Proof. exact (@lem207261 p n (@lem207278 n h1)). Qed.
Lemma lem207282 (m : nat) (p : nat) (n : nat) (h1 : term37 n) : (term167 m p n) = (True /\ True).
Proof. exact (MK_COMB (@lem207252 m p n h1) (@lem207279 p n h1)). Qed.
Lemma lem207284 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem207285 : (True /\ True) = True.
Proof. exact (@lem207284 True). Qed.
Lemma lem207288 (m : nat) (p : nat) (n : nat) (h1 : term37 n) : (term167 m p n) = True.
Proof. exact (TRANS (@lem207282 m p n h1) (@lem207285)). Qed.
Lemma lem207289 (m : nat) (p : nat) (n : nat) (h1 : term37 n) : True = (term167 m p n).
Proof. exact (SYM (@lem207288 m p n h1)). Qed.
Lemma lem207290 (m : nat) (p : nat) (n : nat) (h1 : term37 n) : term167 m p n.
Proof. exact (EQ_MP (@lem207289 m p n h1) (@lem0)). Qed.
Lemma lem207291 (m : nat) (p : nat) (n : nat) (h1 : term37 n) : term168 m p n.
Proof. exact (ex_intro (term169 m p n) (term170 m p n) (@lem207290 m p n h1)). Qed.
Lemma lem207293 (m : nat) (p : nat) (n : nat) (h1 : term37 n) : (term71 m p n) = (Nat.modulo p n).
Proof. exact (@lem206966 m p n (@lem207291 m p n h1)). Qed.
Lemma lem207294 (m : nat) (p : nat) (n : nat) : (term71 m p n) = (Nat.modulo p n).
Proof. exact (or_elim (@lem206284 n) (fun h0 : n = (NUMERAL 0) => @lem206888 m p n h0) (fun h0 : term37 n => @lem207293 m p n h0)). Qed.
Lemma lem207299 (m : nat) (n : nat) : term77 m n.
Proof. exact (fun p : nat => @lem207294 m p n). Qed.
Lemma lem207304 (m : nat) : term81 m.
Proof. exact (fun n : nat => @lem207299 m n). Qed.
Lemma lem207309 : term57.
Proof. exact (fun m : nat => @lem207304 m). Qed.
Lemma lem207310 : term171.
Proof. exact (conj (@lem206794) (@lem207309)). Qed.
Lemma lem207311 : term172.
Proof. exact (@lem206400 (@lem207310)). Qed.
