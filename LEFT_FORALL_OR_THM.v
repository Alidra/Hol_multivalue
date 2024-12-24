Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LEFT_FORALL_OR_THM_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import DE_MORGAN_THM_spec.
Require Import LEFT_EXISTS_AND_THM_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_FORALL_THM_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem11204 {A : Type'} (P : A -> Prop) : term0 A P.
Proof. exact (@lem5682 A P). Qed.
Lemma lem11205 {A : Type'} (P : A -> Prop) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem11206 {A : Type'} (P : A -> Prop) : term1 A P.
Proof. exact (EQ_MP (@lem11205 A P) (@lem11204 A P)). Qed.
Lemma lem11207 {A : Type'} (P : A -> Prop) (Q : Prop) : term2 A P Q.
Proof. exact (@lem11206 A P Q). Qed.
Lemma lem11208 {A : Type'} (P : A -> Prop) (Q : Prop) : (term2 A P Q) = ((term3 A P Q) = (term4 A P Q)).
Proof. exact (eq_refl (term2 A P Q)). Qed.
Lemma lem11210 (t1 : Prop) : term5 t1.
Proof. exact (@lem10089 t1). Qed.
Lemma lem11211 (t1 : Prop) : (term5 t1) = (term6 t1).
Proof. exact (eq_refl (term5 t1)). Qed.
Lemma lem11212 (t1 : Prop) : term6 t1.
Proof. exact (EQ_MP (@lem11211 t1) (@lem11210 t1)). Qed.
Lemma lem11213 (t1 : Prop) (t2 : Prop) : term7 t1 t2.
Proof. exact (@lem11212 t1 t2). Qed.
Lemma lem11214 (t1 : Prop) (t2 : Prop) : (term7 t1 t2) = (term8 t1 t2).
Proof. exact (eq_refl (term7 t1 t2)). Qed.
Lemma lem11215 (t1 : Prop) (t2 : Prop) : term8 t1 t2.
Proof. exact (EQ_MP (@lem11214 t1 t2) (@lem11213 t1 t2)). Qed.
Lemma lem11218 {A : Type'} (P : A -> Prop) : term9 A P.
Proof. exact (@lem10884 A P). Qed.
Lemma lem11219 {A : Type'} (P : A -> Prop) : (term9 A P) = ((term10 A P) = (term11 A P)).
Proof. exact (eq_refl (term9 A P)). Qed.
Lemma lem11229 (a : Prop) : term12 a.
Proof. exact (@lem9851 a). Qed.
Lemma lem11230 (a : Prop) : (term12 a) = (term13 a).
Proof. exact (eq_refl (term12 a)). Qed.
Lemma lem11231 (a : Prop) : term13 a.
Proof. exact (EQ_MP (@lem11230 a) (@lem11229 a)). Qed.
Lemma lem11232 (a : Prop) (h1 : a = True) : a = True.
Proof. exact (h1). Qed.
Lemma lem11233 (a : Prop) (h1 : a = False) : a = False.
Proof. exact (h1). Qed.
Lemma lem11242 (b : Prop) : (term14 b) = (term14 b).
Proof. exact (eq_refl (term14 b)). Qed.
Lemma lem11243 (b : Prop) (a : Prop) (h1 : a = True) : (term15 b a) = (term16 b).
Proof. exact (MK_COMB (@lem11242 b) (@lem11232 a h1)). Qed.
Lemma lem11244 (b : Prop) : (term16 b) = ((True = b) = ((~ True) = (~ b))).
Proof. exact (eq_refl (term16 b)). Qed.
Lemma lem11245 (b : Prop) (a : Prop) : (term17 b a) = (term17 b a).
Proof. exact (eq_refl (term17 b a)). Qed.
Lemma lem11246 (a : Prop) (b : Prop) : ((term15 b a) = (term16 b)) = ((term15 b a) = ((True = b) = ((~ True) = (~ b)))).
Proof. exact (MK_COMB (@lem11245 b a) (@lem11244 b)). Qed.
Lemma lem11247 (a : Prop) (b : Prop) : (term15 b a) = ((a = b) = ((~ a) = (~ b))).
Proof. exact (eq_refl (term15 b a)). Qed.
Lemma lem11248 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem11249 (a : Prop) (b : Prop) : (term17 b a) = (term18 a b).
Proof. exact (MK_COMB (@lem11248) (@lem11247 a b)). Qed.
Lemma lem11250 (b : Prop) : ((True = b) = ((~ True) = (~ b))) = ((True = b) = ((~ True) = (~ b))).
Proof. exact (eq_refl ((True = b) = ((~ True) = (~ b)))). Qed.
Lemma lem11251 (a : Prop) (b : Prop) : ((term15 b a) = ((True = b) = ((~ True) = (~ b)))) = (((a = b) = ((~ a) = (~ b))) = ((True = b) = ((~ True) = (~ b)))).
Proof. exact (MK_COMB (@lem11249 a b) (@lem11250 b)). Qed.
Lemma lem11252 (a : Prop) (b : Prop) : ((term15 b a) = (term16 b)) = (((a = b) = ((~ a) = (~ b))) = ((True = b) = ((~ True) = (~ b)))).
Proof. exact (TRANS (@lem11246 a b) (@lem11251 a b)). Qed.
Lemma lem11253 (b : Prop) (a : Prop) (h1 : a = True) : ((a = b) = ((~ a) = (~ b))) = ((True = b) = ((~ True) = (~ b))).
Proof. exact (EQ_MP (@lem11252 a b) (@lem11243 b a h1)). Qed.
Lemma lem11254 (b : Prop) (a : Prop) (h1 : a = True) : ((True = b) = ((~ True) = (~ b))) = ((a = b) = ((~ a) = (~ b))).
Proof. exact (SYM (@lem11253 b a h1)). Qed.
Lemma lem11255 (b : Prop) : (term14 b) = (term14 b).
Proof. exact (eq_refl (term14 b)). Qed.
Lemma lem11256 (b : Prop) (a : Prop) (h1 : a = False) : (term15 b a) = (term19 b).
Proof. exact (MK_COMB (@lem11255 b) (@lem11233 a h1)). Qed.
Lemma lem11257 (b : Prop) : (term19 b) = ((False = b) = ((~ False) = (~ b))).
Proof. exact (eq_refl (term19 b)). Qed.
Lemma lem11258 (b : Prop) (a : Prop) : (term17 b a) = (term17 b a).
Proof. exact (eq_refl (term17 b a)). Qed.
Lemma lem11259 (a : Prop) (b : Prop) : ((term15 b a) = (term19 b)) = ((term15 b a) = ((False = b) = ((~ False) = (~ b)))).
Proof. exact (MK_COMB (@lem11258 b a) (@lem11257 b)). Qed.
Lemma lem11260 (a : Prop) (b : Prop) : (term15 b a) = ((a = b) = ((~ a) = (~ b))).
Proof. exact (eq_refl (term15 b a)). Qed.
Lemma lem11261 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem11262 (a : Prop) (b : Prop) : (term17 b a) = (term18 a b).
Proof. exact (MK_COMB (@lem11261) (@lem11260 a b)). Qed.
Lemma lem11263 (b : Prop) : ((False = b) = ((~ False) = (~ b))) = ((False = b) = ((~ False) = (~ b))).
Proof. exact (eq_refl ((False = b) = ((~ False) = (~ b)))). Qed.
Lemma lem11264 (a : Prop) (b : Prop) : ((term15 b a) = ((False = b) = ((~ False) = (~ b)))) = (((a = b) = ((~ a) = (~ b))) = ((False = b) = ((~ False) = (~ b)))).
Proof. exact (MK_COMB (@lem11262 a b) (@lem11263 b)). Qed.
Lemma lem11265 (a : Prop) (b : Prop) : ((term15 b a) = (term19 b)) = (((a = b) = ((~ a) = (~ b))) = ((False = b) = ((~ False) = (~ b)))).
Proof. exact (TRANS (@lem11259 a b) (@lem11264 a b)). Qed.
Lemma lem11266 (b : Prop) (a : Prop) (h1 : a = False) : ((a = b) = ((~ a) = (~ b))) = ((False = b) = ((~ False) = (~ b))).
Proof. exact (EQ_MP (@lem11265 a b) (@lem11256 b a h1)). Qed.
Lemma lem11267 (b : Prop) (a : Prop) (h1 : a = False) : ((False = b) = ((~ False) = (~ b))) = ((a = b) = ((~ a) = (~ b))).
Proof. exact (SYM (@lem11266 b a h1)). Qed.
Lemma lem11271 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem11272 (b : Prop) : (True = b) = b.
Proof. exact (@lem11271 b). Qed.
Lemma lem11273 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem11274 (b : Prop) : (term20 b) = (@eq Prop b).
Proof. exact (MK_COMB (@lem11273) (@lem11272 b)). Qed.
Lemma lem11278 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem11279 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem11280 : term21 = (@eq Prop False).
Proof. exact (MK_COMB (@lem11279) (@lem11278)). Qed.
Lemma lem11281 (b : Prop) : (~ b) = (~ b).
Proof. exact (eq_refl (~ b)). Qed.
Lemma lem11282 (b : Prop) : ((~ True) = (~ b)) = (False = (~ b)).
Proof. exact (MK_COMB (@lem11280) (@lem11281 b)). Qed.
Lemma lem11284 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem11285 (b : Prop) : (False = (~ b)) = (term22 b).
Proof. exact (@lem11284 (~ b)). Qed.
Lemma lem11286 (b : Prop) : ((~ True) = (~ b)) = (term22 b).
Proof. exact (TRANS (@lem11282 b) (@lem11285 b)). Qed.
Lemma lem11287 (b : Prop) : ((True = b) = ((~ True) = (~ b))) = (b = (term22 b)).
Proof. exact (MK_COMB (@lem11274 b) (@lem11286 b)). Qed.
Lemma lem11290 (b : Prop) : (b = (term22 b)) = ((True = b) = ((~ True) = (~ b))).
Proof. exact (SYM (@lem11287 b)). Qed.
Lemma lem11299 (t : Prop) : (term22 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem11300 (b : Prop) : (term22 b) = b.
Proof. exact (@lem11299 b). Qed.
Lemma lem11301 (b : Prop) : (@eq Prop b) = (@eq Prop b).
Proof. exact (eq_refl (@eq Prop b)). Qed.
Lemma lem11302 (b : Prop) : (b = (term22 b)) = (b = b).
Proof. exact (MK_COMB (@lem11301 b) (@lem11300 b)). Qed.
Lemma lem11304 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem11305 (x : Prop) : (x = x) = True.
Proof. exact (@lem11304 Prop x). Qed.
Lemma lem11306 (b : Prop) : (b = b) = True.
Proof. exact (@lem11305 b). Qed.
Lemma lem11307 (b : Prop) : (b = (term22 b)) = True.
Proof. exact (TRANS (@lem11302 b) (@lem11306 b)). Qed.
Lemma lem11308 (b : Prop) : True = (b = (term22 b)).
Proof. exact (SYM (@lem11307 b)). Qed.
Lemma lem11309 (b : Prop) : b = (term22 b).
Proof. exact (EQ_MP (@lem11308 b) (@lem0)). Qed.
Lemma lem11310 (b : Prop) : (True = b) = ((~ True) = (~ b)).
Proof. exact (EQ_MP (@lem11290 b) (@lem11309 b)). Qed.
Lemma lem11314 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem11315 (b : Prop) : (False = b) = (~ b).
Proof. exact (@lem11314 b). Qed.
Lemma lem11316 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem11317 (b : Prop) : (term23 b) = (term24 b).
Proof. exact (MK_COMB (@lem11316) (@lem11315 b)). Qed.
Lemma lem11321 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem11322 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem11323 : term25 = (@eq Prop True).
Proof. exact (MK_COMB (@lem11322) (@lem11321)). Qed.
Lemma lem11324 (b : Prop) : (~ b) = (~ b).
Proof. exact (eq_refl (~ b)). Qed.
Lemma lem11325 (b : Prop) : ((~ False) = (~ b)) = (True = (~ b)).
Proof. exact (MK_COMB (@lem11323) (@lem11324 b)). Qed.
Lemma lem11327 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem11328 (b : Prop) : (True = (~ b)) = (~ b).
Proof. exact (@lem11327 (~ b)). Qed.
Lemma lem11329 (b : Prop) : ((~ False) = (~ b)) = (~ b).
Proof. exact (TRANS (@lem11325 b) (@lem11328 b)). Qed.
Lemma lem11330 (b : Prop) : ((False = b) = ((~ False) = (~ b))) = ((~ b) = (~ b)).
Proof. exact (MK_COMB (@lem11317 b) (@lem11329 b)). Qed.
Lemma lem11332 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem11333 (x : Prop) : (x = x) = True.
Proof. exact (@lem11332 Prop x). Qed.
Lemma lem11334 (b : Prop) : ((~ b) = (~ b)) = True.
Proof. exact (@lem11333 (~ b)). Qed.
Lemma lem11335 (b : Prop) : ((False = b) = ((~ False) = (~ b))) = True.
Proof. exact (TRANS (@lem11330 b) (@lem11334 b)). Qed.
Lemma lem11336 (b : Prop) : True = ((False = b) = ((~ False) = (~ b))).
Proof. exact (SYM (@lem11335 b)). Qed.
Lemma lem11337 (b : Prop) : (False = b) = ((~ False) = (~ b)).
Proof. exact (EQ_MP (@lem11336 b) (@lem0)). Qed.
Lemma lem11338 (b : Prop) (a : Prop) (h1 : a = False) : (a = b) = ((~ a) = (~ b)).
Proof. exact (EQ_MP (@lem11267 b a h1) (@lem11337 b)). Qed.
Lemma lem11339 (b : Prop) (a : Prop) (h1 : a = True) : (a = b) = ((~ a) = (~ b)).
Proof. exact (EQ_MP (@lem11254 b a h1) (@lem11310 b)). Qed.
Lemma lem11346 (a : Prop) (b : Prop) : (a = b) = ((~ a) = (~ b)).
Proof. exact (or_elim (@lem11231 a) (fun h0 : a = True => @lem11339 b a h0) (fun h0 : a = False => @lem11338 b a h0)). Qed.
Lemma lem11347 {A : Type'} (P : A -> Prop) (Q : Prop) : ((term26 A P Q) = (term27 A P Q)) = ((term28 A P Q) = (term29 A P Q)).
Proof. exact (@lem11346 (term26 A P Q) (term27 A P Q)). Qed.
Lemma lem11348 {A : Type'} (P : A -> Prop) (Q : Prop) : ((term28 A P Q) = (term29 A P Q)) = ((term26 A P Q) = (term27 A P Q)).
Proof. exact (SYM (@lem11347 A P Q)). Qed.
Lemma lem11352 {A : Type'} (P : A -> Prop) : (term10 A P) = (term11 A P).
Proof. exact (EQ_MP (@lem11219 A P) (@lem11218 A P)). Qed.
Lemma lem11353 {A : Type'} (P : A -> Prop) : (term10 A P) = (term11 A P).
Proof. exact (@lem11352 A P). Qed.
Lemma lem11354 {A : Type'} (P : A -> Prop) (Q : Prop) : (term30 A P Q) = (term31 A P Q).
Proof. exact (@lem11353 A (term32 A P Q)). Qed.
Lemma lem11355 {A : Type'} (P : A -> Prop) (x : A) (Q : Prop) : (term33 A P Q x) = (term34 A P x Q).
Proof. exact (eq_refl (term33 A P Q x)). Qed.
Lemma lem11356 {A : Type'} (P : A -> Prop) (Q : Prop) : (term35 A P Q) = (term32 A P Q).
Proof. exact (fun_ext (fun x : A => @lem11355 A P x Q)). Qed.
Lemma lem11357 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem11358 {A : Type'} (P : A -> Prop) (Q : Prop) : (term36 A P Q) = (term26 A P Q).
Proof. exact (MK_COMB (@lem11357 A) (@lem11356 A P Q)). Qed.
Lemma lem11359 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem11360 {A : Type'} (P : A -> Prop) (Q : Prop) : (term30 A P Q) = (term28 A P Q).
Proof. exact (MK_COMB (@lem11359) (@lem11358 A P Q)). Qed.
Lemma lem11361 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem11362 {A : Type'} (P : A -> Prop) (Q : Prop) : (term37 A P Q) = (term38 A P Q).
Proof. exact (MK_COMB (@lem11361) (@lem11360 A P Q)). Qed.
Lemma lem11363 {A : Type'} (P : A -> Prop) (x : A) (Q : Prop) : (term33 A P Q x) = (term34 A P x Q).
Proof. exact (eq_refl (term33 A P Q x)). Qed.
Lemma lem11364 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem11365 {A : Type'} (P : A -> Prop) (x : A) (Q : Prop) : (term39 A P Q x) = (term40 A P x Q).
Proof. exact (MK_COMB (@lem11364) (@lem11363 A P x Q)). Qed.
Lemma lem11366 {A : Type'} (P : A -> Prop) (Q : Prop) : (term41 A P Q) = (term42 A P Q).
Proof. exact (fun_ext (fun x : A => @lem11365 A P x Q)). Qed.
Lemma lem11367 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem11368 {A : Type'} (P : A -> Prop) (Q : Prop) : (term31 A P Q) = (term43 A P Q).
Proof. exact (MK_COMB (@lem11367 A) (@lem11366 A P Q)). Qed.
Lemma lem11369 {A : Type'} (P : A -> Prop) (Q : Prop) : ((term30 A P Q) = (term31 A P Q)) = ((term28 A P Q) = (term43 A P Q)).
Proof. exact (MK_COMB (@lem11362 A P Q) (@lem11368 A P Q)). Qed.
Lemma lem11370 {A : Type'} (P : A -> Prop) (Q : Prop) : (term28 A P Q) = (term43 A P Q).
Proof. exact (EQ_MP (@lem11369 A P Q) (@lem11354 A P Q)). Qed.
Lemma lem11376 (t1 : Prop) (t2 : Prop) : (term44 t1 t2) = (term45 t1 t2).
Proof. exact (proj2 (@lem11215 t1 t2)). Qed.
Lemma lem11377 {A : Type'} (P : A -> Prop) (x : A) (Q : Prop) : (term40 A P x Q) = (term46 A P x Q).
Proof. exact (@lem11376 (P x) Q). Qed.
Lemma lem11380 {A : Type'} (P : A -> Prop) (Q : Prop) : (term42 A P Q) = (term47 A P Q).
Proof. exact (fun_ext (fun x : A => @lem11377 A P x Q)). Qed.
Lemma lem11381 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem11382 {A : Type'} (P : A -> Prop) (Q : Prop) : (term43 A P Q) = (term48 A P Q).
Proof. exact (MK_COMB (@lem11381 A) (@lem11380 A P Q)). Qed.
Lemma lem11384 {A : Type'} (P : A -> Prop) (Q : Prop) : (term3 A P Q) = (term4 A P Q).
Proof. exact (EQ_MP (@lem11208 A P Q) (@lem11207 A P Q)). Qed.
Lemma lem11385 {A : Type'} (P : A -> Prop) (Q : Prop) : (term3 A P Q) = (term4 A P Q).
Proof. exact (@lem11384 A P Q). Qed.
Lemma lem11386 {A : Type'} (P : A -> Prop) (Q : Prop) : (term49 A P Q) = (term50 A P Q).
Proof. exact (@lem11385 A (term51 A P) (~ Q)). Qed.
Lemma lem11387 {A : Type'} (P : A -> Prop) (x : A) : (term52 A P x) = (term53 A P x).
Proof. exact (eq_refl (term52 A P x)). Qed.
Lemma lem11388 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem11389 {A : Type'} (P : A -> Prop) (x : A) : (term54 A P x) = (term55 A P x).
Proof. exact (MK_COMB (@lem11388) (@lem11387 A P x)). Qed.
Lemma lem11390 (Q : Prop) : (~ Q) = (~ Q).
Proof. exact (eq_refl (~ Q)). Qed.
Lemma lem11391 {A : Type'} (P : A -> Prop) (x : A) (Q : Prop) : (term56 A P x Q) = (term46 A P x Q).
Proof. exact (MK_COMB (@lem11389 A P x) (@lem11390 Q)). Qed.
Lemma lem11392 {A : Type'} (P : A -> Prop) (Q : Prop) : (term57 A P Q) = (term47 A P Q).
Proof. exact (fun_ext (fun x : A => @lem11391 A P x Q)). Qed.
Lemma lem11393 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem11394 {A : Type'} (P : A -> Prop) (Q : Prop) : (term49 A P Q) = (term48 A P Q).
Proof. exact (MK_COMB (@lem11393 A) (@lem11392 A P Q)). Qed.
Lemma lem11395 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem11396 {A : Type'} (P : A -> Prop) (Q : Prop) : (term58 A P Q) = (term59 A P Q).
Proof. exact (MK_COMB (@lem11395) (@lem11394 A P Q)). Qed.
Lemma lem11397 {A : Type'} (P : A -> Prop) (x : A) : (term52 A P x) = (term53 A P x).
Proof. exact (eq_refl (term52 A P x)). Qed.
Lemma lem11398 {A : Type'} (P : A -> Prop) : (term60 A P) = (term51 A P).
Proof. exact (fun_ext (fun x : A => @lem11397 A P x)). Qed.
Lemma lem11399 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem11400 {A : Type'} (P : A -> Prop) : (term61 A P) = (term11 A P).
Proof. exact (MK_COMB (@lem11399 A) (@lem11398 A P)). Qed.
Lemma lem11401 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem11402 {A : Type'} (P : A -> Prop) : (term62 A P) = (term63 A P).
Proof. exact (MK_COMB (@lem11401) (@lem11400 A P)). Qed.
Lemma lem11403 (Q : Prop) : (~ Q) = (~ Q).
Proof. exact (eq_refl (~ Q)). Qed.
Lemma lem11404 {A : Type'} (P : A -> Prop) (Q : Prop) : (term50 A P Q) = (term64 A P Q).
Proof. exact (MK_COMB (@lem11402 A P) (@lem11403 Q)). Qed.
Lemma lem11405 {A : Type'} (P : A -> Prop) (Q : Prop) : ((term49 A P Q) = (term50 A P Q)) = ((term48 A P Q) = (term64 A P Q)).
Proof. exact (MK_COMB (@lem11396 A P Q) (@lem11404 A P Q)). Qed.
Lemma lem11406 {A : Type'} (P : A -> Prop) (Q : Prop) : (term48 A P Q) = (term64 A P Q).
Proof. exact (EQ_MP (@lem11405 A P Q) (@lem11386 A P Q)). Qed.
Lemma lem11413 {A : Type'} (P : A -> Prop) (Q : Prop) : (term43 A P Q) = (term64 A P Q).
Proof. exact (TRANS (@lem11382 A P Q) (@lem11406 A P Q)). Qed.
Lemma lem11414 {A : Type'} (P : A -> Prop) (Q : Prop) : (term28 A P Q) = (term64 A P Q).
Proof. exact (TRANS (@lem11370 A P Q) (@lem11413 A P Q)). Qed.
Lemma lem11415 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem11416 {A : Type'} (P : A -> Prop) (Q : Prop) : (term38 A P Q) = (term65 A P Q).
Proof. exact (MK_COMB (@lem11415) (@lem11414 A P Q)). Qed.
Lemma lem11418 (t1 : Prop) (t2 : Prop) : (term44 t1 t2) = (term45 t1 t2).
Proof. exact (proj2 (@lem11215 t1 t2)). Qed.
Lemma lem11419 {A : Type'} (P : A -> Prop) (Q : Prop) : (term29 A P Q) = (term66 A P Q).
Proof. exact (@lem11418 (term67 A P) Q). Qed.
Lemma lem11423 {A : Type'} (P : A -> Prop) : (term10 A P) = (term11 A P).
Proof. exact (EQ_MP (@lem11219 A P) (@lem11218 A P)). Qed.
Lemma lem11424 {A : Type'} (P : A -> Prop) : (term10 A P) = (term11 A P).
Proof. exact (@lem11423 A P). Qed.
Lemma lem11429 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem11430 {A : Type'} (P : A -> Prop) : (term68 A P) = (term63 A P).
Proof. exact (MK_COMB (@lem11429) (@lem11424 A P)). Qed.
Lemma lem11431 (Q : Prop) : (~ Q) = (~ Q).
Proof. exact (eq_refl (~ Q)). Qed.
Lemma lem11432 {A : Type'} (P : A -> Prop) (Q : Prop) : (term66 A P Q) = (term64 A P Q).
Proof. exact (MK_COMB (@lem11430 A P) (@lem11431 Q)). Qed.
Lemma lem11435 {A : Type'} (P : A -> Prop) (Q : Prop) : (term29 A P Q) = (term64 A P Q).
Proof. exact (TRANS (@lem11419 A P Q) (@lem11432 A P Q)). Qed.
Lemma lem11436 {A : Type'} (P : A -> Prop) (Q : Prop) : ((term28 A P Q) = (term29 A P Q)) = ((term64 A P Q) = (term64 A P Q)).
Proof. exact (MK_COMB (@lem11416 A P Q) (@lem11435 A P Q)). Qed.
Lemma lem11438 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem11439 (x : Prop) : (x = x) = True.
Proof. exact (@lem11438 Prop x). Qed.
Lemma lem11440 {A : Type'} (P : A -> Prop) (Q : Prop) : ((term64 A P Q) = (term64 A P Q)) = True.
Proof. exact (@lem11439 (term64 A P Q)). Qed.
Lemma lem11441 {A : Type'} (P : A -> Prop) (Q : Prop) : ((term28 A P Q) = (term29 A P Q)) = True.
Proof. exact (TRANS (@lem11436 A P Q) (@lem11440 A P Q)). Qed.
Lemma lem11442 {A : Type'} (P : A -> Prop) (Q : Prop) : True = ((term28 A P Q) = (term29 A P Q)).
Proof. exact (SYM (@lem11441 A P Q)). Qed.
Lemma lem11443 {A : Type'} (P : A -> Prop) (Q : Prop) : (term28 A P Q) = (term29 A P Q).
Proof. exact (EQ_MP (@lem11442 A P Q) (@lem0)). Qed.
Lemma lem11444 {A : Type'} (P : A -> Prop) (Q : Prop) : (term26 A P Q) = (term27 A P Q).
Proof. exact (EQ_MP (@lem11348 A P Q) (@lem11443 A P Q)). Qed.
Lemma lem11449 {A : Type'} (P : A -> Prop) : term69 A P.
Proof. exact (fun Q : Prop => @lem11444 A P Q). Qed.
Lemma lem11454 {A : Type'} : term70 A.
Proof. exact (fun P : A -> Prop => @lem11449 A P). Qed.
