Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUBSET_UNION_ABSORPTION_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm17930_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19699_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211719_spec.
Require Import thm3211720_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3234207 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3234208 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (@lem3234207 A s t). Qed.
Lemma lem3234215 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3234216 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1 A s t) = (term2 A s t).
Proof. exact (MK_COMB (@lem3234215) (@lem3234208 A s t)). Qed.
Lemma lem3234220 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term3 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3234221 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term3 A s t).
Proof. exact (@lem3234220 A s t). Qed.
Lemma lem3234222 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((@UNION A s t) = t) = (term4 A s t).
Proof. exact (@lem3234221 A (@UNION A s t) t). Qed.
Lemma lem3234231 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((@SUBSET A s t) = ((@UNION A s t) = t)) = ((term0 A s t) = (term4 A s t)).
Proof. exact (MK_COMB (@lem3234216 A s t) (@lem3234222 A s t)). Qed.
Lemma lem3234236 {A : Type'} (s : A -> Prop) : (term5 A s) = (term6 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3234231 A s t)). Qed.
Lemma lem3234237 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3234238 {A : Type'} (s : A -> Prop) : (term7 A s) = (term8 A s).
Proof. exact (MK_COMB (@lem3234237 A) (@lem3234236 A s)). Qed.
Lemma lem3234243 {A : Type'} : (term9 A) = (term10 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3234238 A s)). Qed.
Lemma lem3234244 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3234245 {A : Type'} : (term11 A) = (term12 A).
Proof. exact (MK_COMB (@lem3234244 A) (@lem3234243 A)). Qed.
Lemma lem3234250 {A : Type'} : (term12 A) = (term11 A).
Proof. exact (SYM (@lem3234245 A)). Qed.
Lemma lem3234268 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3234269 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3234268 A P x). Qed.
Lemma lem3234270 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3234269 A s x). Qed.
Lemma lem3234271 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3234272 {A : Type'} (s : A -> Prop) (x : A) : (term13 A x s) = (term14 A s x).
Proof. exact (MK_COMB (@lem3234271) (@lem3234270 A s x)). Qed.
Lemma lem3234274 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3234275 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3234274 A P x). Qed.
Lemma lem3234276 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3234275 A t x). Qed.
Lemma lem3234277 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term15 A s x t) = (term16 A s t x).
Proof. exact (MK_COMB (@lem3234272 A s x) (@lem3234276 A t x)). Qed.
Lemma lem3234280 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term17 A s t) = (term18 A s t).
Proof. exact (fun_ext (fun x : A => @lem3234277 A s t x)). Qed.
Lemma lem3234281 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3234282 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term0 A s t) = (term19 A s t).
Proof. exact (MK_COMB (@lem3234281 A) (@lem3234280 A s t)). Qed.
Lemma lem3234287 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3234288 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term2 A s t) = (term20 A s t).
Proof. exact (MK_COMB (@lem3234287) (@lem3234282 A s t)). Qed.
Lemma lem3234296 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term21 A x s t) = (term22 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3234297 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term21 A x s t) = (term22 A s x t).
Proof. exact (@lem3234296 A s x t). Qed.
Lemma lem3234301 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3234302 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3234301 A P x). Qed.
Lemma lem3234303 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3234302 A s x). Qed.
Lemma lem3234304 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3234305 {A : Type'} (s : A -> Prop) (x : A) : (term23 A x s) = (term24 A s x).
Proof. exact (MK_COMB (@lem3234304) (@lem3234303 A s x)). Qed.
Lemma lem3234307 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3234308 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3234307 A P x). Qed.
Lemma lem3234309 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3234308 A t x). Qed.
Lemma lem3234310 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term22 A s x t) = (term25 A s t x).
Proof. exact (MK_COMB (@lem3234305 A s x) (@lem3234309 A t x)). Qed.
Lemma lem3234313 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term21 A x s t) = (term25 A s t x).
Proof. exact (TRANS (@lem3234297 A s x t) (@lem3234310 A s t x)). Qed.
Lemma lem3234314 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3234315 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term26 A x s t) = (term27 A s t x).
Proof. exact (MK_COMB (@lem3234314) (@lem3234313 A s t x)). Qed.
Lemma lem3234317 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3234318 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3234317 A P x). Qed.
Lemma lem3234319 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3234318 A t x). Qed.
Lemma lem3234320 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((term21 A x s t) = (@IN A x t)) = ((term25 A s t x) = (t x)).
Proof. exact (MK_COMB (@lem3234315 A s t x) (@lem3234319 A t x)). Qed.
Lemma lem3234323 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term28 A s t) = (term29 A s t).
Proof. exact (fun_ext (fun x : A => @lem3234320 A s t x)). Qed.
Lemma lem3234324 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3234325 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term4 A s t) = (term30 A s t).
Proof. exact (MK_COMB (@lem3234324 A) (@lem3234323 A s t)). Qed.
Lemma lem3234330 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term0 A s t) = (term4 A s t)) = ((term19 A s t) = (term30 A s t)).
Proof. exact (MK_COMB (@lem3234288 A s t) (@lem3234325 A s t)). Qed.
Lemma lem3234333 {A : Type'} (s : A -> Prop) : (term6 A s) = (term31 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3234330 A s t)). Qed.
Lemma lem3234334 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3234335 {A : Type'} (s : A -> Prop) : (term8 A s) = (term32 A s).
Proof. exact (MK_COMB (@lem3234334 A) (@lem3234333 A s)). Qed.
Lemma lem3234340 {A : Type'} : (term10 A) = (term33 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3234335 A s)). Qed.
Lemma lem3234341 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3234342 {A : Type'} : (term12 A) = (term34 A).
Proof. exact (MK_COMB (@lem3234341 A) (@lem3234340 A)). Qed.
Lemma lem3234347 {A : Type'} : (term34 A) = (term12 A).
Proof. exact (SYM (@lem3234342 A)). Qed.
Lemma lem3234349 (p : Prop) : p = (term35 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3234350 {A : Type'} : (term34 A) = (term36 A).
Proof. exact (@lem3234349 (term34 A)). Qed.
Lemma lem3234351 {A : Type'} : (term36 A) = (term34 A).
Proof. exact (SYM (@lem3234350 A)). Qed.
Lemma lem3234352 {A : Type'} (h1 : term37 A) : term37 A.
Proof. exact (h1). Qed.
Lemma lem3234355 {A : Type'} (h1 : term36 A) : term36 A.
Proof. exact (h1). Qed.
Lemma lem3234356 {A : Type'} : term38 A.
Proof. exact (fun h0 : term36 A => @lem3234355 A h0). Qed.
Lemma lem3234357 {A : Type'} (h1 : term38 A) : term38 A.
Proof. exact (h1). Qed.
Lemma lem3234358 {A : Type'} (h1 : term36 A) : term36 A.
Proof. exact (h1). Qed.
Lemma lem3234359 {A : Type'} (h1 : term36 A) (h2 : term38 A) : term36 A.
Proof. exact (@lem3234357 A h2 (@lem3234358 A h1)). Qed.
Lemma lem3234360 {A : Type'} (h1 : term36 A) : term39 A.
Proof. exact (fun h0 : term38 A => @lem3234359 A h1 h0). Qed.
Lemma lem3234361 {A : Type'} (h1 : term38 A) : term38 A.
Proof. exact (h1). Qed.
Lemma lem3234362 {A : Type'} (h1 : term36 A) (h2 : term38 A) : term36 A.
Proof. exact (@lem3234360 A h1 (@lem3234361 A h2)). Qed.
Lemma lem3234363 {A : Type'} (h1 : term38 A) : term38 A.
Proof. exact (fun h0 : term36 A => @lem3234362 A h0 h1). Qed.
Lemma lem3234364 {A : Type'} : term40 A.
Proof. exact (fun h0 : term38 A => @lem3234363 A h0). Qed.
Lemma lem3234367 {A : Type'} : term38 A.
Proof. exact (@lem3234364 A (@lem3234356 A)). Qed.
Lemma lem3234368 {A : Type'} : term38 A.
Proof. exact (@lem3234367 A). Qed.
Lemma lem3234370 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3234371 {A : Type'} : (term36 A) = (term41 A).
Proof. exact (@lem3234370 (term37 A)). Qed.
Lemma lem3234373 (t : Prop) : (term42 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3234374 {A : Type'} : (term41 A) = (term34 A).
Proof. exact (@lem3234373 (term34 A)). Qed.
Lemma lem3234399 {A : Type'} : (term36 A) = (term34 A).
Proof. exact (TRANS (@lem3234371 A) (@lem3234374 A)). Qed.
Lemma lem3234408 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((term25 A s t x) = (t x)) = ((term25 A s t x) = (t x)).
Proof. exact (eq_refl ((term25 A s t x) = (t x))). Qed.
Lemma lem3234409 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term29 A s t) = (term29 A s t).
Proof. exact (fun_ext (fun x : A => @lem3234408 A s t x)). Qed.
Lemma lem3234410 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3234411 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term30 A s t) = (term30 A s t).
Proof. exact (MK_COMB (@lem3234410 A) (@lem3234409 A s t)). Qed.
Lemma lem3234416 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term16 A s t x) = (term16 A s t x).
Proof. exact (eq_refl (term16 A s t x)). Qed.
Lemma lem3234417 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term18 A s t) = (term18 A s t).
Proof. exact (fun_ext (fun x : A => @lem3234416 A s t x)). Qed.
Lemma lem3234418 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3234419 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term19 A s t) = (term19 A s t).
Proof. exact (MK_COMB (@lem3234418 A) (@lem3234417 A s t)). Qed.
Lemma lem3234420 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3234421 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term20 A s t) = (term20 A s t).
Proof. exact (MK_COMB (@lem3234420) (@lem3234419 A s t)). Qed.
Lemma lem3234422 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term19 A s t) = (term30 A s t)) = ((term19 A s t) = (term30 A s t)).
Proof. exact (MK_COMB (@lem3234421 A s t) (@lem3234411 A s t)). Qed.
Lemma lem3234423 {A : Type'} (s : A -> Prop) : (term31 A s) = (term31 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3234422 A s t)). Qed.
Lemma lem3234424 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3234425 {A : Type'} (s : A -> Prop) : (term32 A s) = (term32 A s).
Proof. exact (MK_COMB (@lem3234424 A) (@lem3234423 A s)). Qed.
Lemma lem3234426 {A : Type'} : (term33 A) = (term33 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3234425 A s)). Qed.
Lemma lem3234427 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3234428 {A : Type'} : (term34 A) = (term34 A).
Proof. exact (MK_COMB (@lem3234427 A) (@lem3234426 A)). Qed.
Lemma lem3234459 {A : Type'} : (term36 A) = (term34 A).
Proof. exact (TRANS (@lem3234399 A) (@lem3234428 A)). Qed.
Lemma lem3234460 {A : Type'} : (term34 A) = (term36 A).
Proof. exact (SYM (@lem3234459 A)). Qed.
Lemma lem3234462 (p : Prop) : p = (term35 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3234463 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term19 A s t) = (term30 A s t)) = (term43 A s t).
Proof. exact (@lem3234462 ((term19 A s t) = (term30 A s t))). Qed.
Lemma lem3234464 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term43 A s t) = ((term19 A s t) = (term30 A s t)).
Proof. exact (SYM (@lem3234463 A s t)). Qed.
Lemma lem3234465 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term44 A s t) : term44 A s t.
Proof. exact (h1). Qed.
Lemma lem3234474 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term45 A s t x) = (term46 A s t x).
Proof. exact (@lem17362 (s x) (t x)). Qed.
Lemma lem3234479 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term16 A s t x) = (term47 A s t x).
Proof. exact (@lem17265 (s x) (t x)). Qed.
Lemma lem3234480 {A : Type'} (P : A -> Prop) : (term48 A P) = (term49 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3234481 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term50 A s t) = (term51 A s t).
Proof. exact (@lem3234480 A (term18 A s t)). Qed.
Lemma lem3234482 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term52 A s t x) = (term16 A s t x).
Proof. exact (eq_refl (term52 A s t x)). Qed.
Lemma lem3234483 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3234484 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term53 A s t x) = (term45 A s t x).
Proof. exact (MK_COMB (@lem3234483) (@lem3234482 A s t x)). Qed.
Lemma lem3234485 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term53 A s t x) = (term46 A s t x).
Proof. exact (TRANS (@lem3234484 A s t x) (@lem3234474 A s t x)). Qed.
Lemma lem3234486 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term54 A s t) = (term55 A s t).
Proof. exact (fun_ext (fun x : A => @lem3234485 A s t x)). Qed.
Lemma lem3234487 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3234488 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term51 A s t) = (term56 A s t).
Proof. exact (MK_COMB (@lem3234487 A) (@lem3234486 A s t)). Qed.
Lemma lem3234489 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term50 A s t) = (term56 A s t).
Proof. exact (TRANS (@lem3234481 A s t) (@lem3234488 A s t)). Qed.
Lemma lem3234490 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term18 A s t) = (term57 A s t).
Proof. exact (fun_ext (fun x : A => @lem3234479 A s t x)). Qed.
Lemma lem3234491 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3234492 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term19 A s t) = (term58 A s t).
Proof. exact (MK_COMB (@lem3234491 A) (@lem3234490 A s t)). Qed.
Lemma lem3234501 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term59 A s t x) = (term60 A s t x).
Proof. exact (@lem17160 (s x) (t x)). Qed.
Lemma lem3234505 {A : Type'} (t : A -> Prop) (x : A) : (term61 A t x) = (term61 A t x).
Proof. exact (eq_refl (term61 A t x)). Qed.
Lemma lem3234506 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3234507 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3234508 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term62 A s t x) = (term63 A s t x).
Proof. exact (MK_COMB (@lem3234507) (@lem3234501 A s t x)). Qed.
Lemma lem3234509 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term64 A s t x) = (term65 A s t x).
Proof. exact (MK_COMB (@lem3234508 A s t x) (@lem3234505 A t x)). Qed.
Lemma lem3234514 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term66 A s t x) = (term66 A s t x).
Proof. exact (eq_refl (term66 A s t x)). Qed.
Lemma lem3234515 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term67 A s t x) = (term68 A s t x).
Proof. exact (MK_COMB (@lem3234514 A s t x) (@lem3234509 A s t x)). Qed.
Lemma lem3234516 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term69 A s t x) = (term67 A s t x).
Proof. exact (@lem17930 (term25 A s t x) (t x)). Qed.
Lemma lem3234517 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term69 A s t x) = (term68 A s t x).
Proof. exact (TRANS (@lem3234516 A s t x) (@lem3234515 A s t x)). Qed.
Lemma lem3234518 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3234519 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term62 A s t x) = (term63 A s t x).
Proof. exact (MK_COMB (@lem3234518) (@lem3234501 A s t x)). Qed.
Lemma lem3234520 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term70 A s t x) = (term71 A s t x).
Proof. exact (MK_COMB (@lem3234519 A s t x) (@lem3234506 A t x)). Qed.
Lemma lem3234525 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term72 A s t x) = (term72 A s t x).
Proof. exact (eq_refl (term72 A s t x)). Qed.
Lemma lem3234526 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term73 A s t x) = (term74 A s t x).
Proof. exact (MK_COMB (@lem3234525 A s t x) (@lem3234520 A s t x)). Qed.
Lemma lem3234527 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((term25 A s t x) = (t x)) = (term73 A s t x).
Proof. exact (@lem17784 (term25 A s t x) (t x)). Qed.
Lemma lem3234528 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((term25 A s t x) = (t x)) = (term74 A s t x).
Proof. exact (TRANS (@lem3234527 A s t x) (@lem3234526 A s t x)). Qed.
Lemma lem3234529 {A : Type'} (P : A -> Prop) : (term48 A P) = (term49 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3234530 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term75 A s t) = (term76 A s t).
Proof. exact (@lem3234529 A (term29 A s t)). Qed.
Lemma lem3234531 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term77 A s t x) = ((term25 A s t x) = (t x)).
Proof. exact (eq_refl (term77 A s t x)). Qed.
Lemma lem3234532 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3234533 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term78 A s t x) = (term69 A s t x).
Proof. exact (MK_COMB (@lem3234532) (@lem3234531 A s t x)). Qed.
Lemma lem3234534 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term78 A s t x) = (term68 A s t x).
Proof. exact (TRANS (@lem3234533 A s t x) (@lem3234517 A s t x)). Qed.
Lemma lem3234535 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term79 A s t) = (term80 A s t).
Proof. exact (fun_ext (fun x : A => @lem3234534 A s t x)). Qed.
Lemma lem3234536 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3234537 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term76 A s t) = (term81 A s t).
Proof. exact (MK_COMB (@lem3234536 A) (@lem3234535 A s t)). Qed.
Lemma lem3234538 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term75 A s t) = (term81 A s t).
Proof. exact (TRANS (@lem3234530 A s t) (@lem3234537 A s t)). Qed.
Lemma lem3234539 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term29 A s t) = (term82 A s t).
Proof. exact (fun_ext (fun x : A => @lem3234528 A s t x)). Qed.
Lemma lem3234540 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3234541 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term30 A s t) = (term83 A s t).
Proof. exact (MK_COMB (@lem3234540 A) (@lem3234539 A s t)). Qed.
Lemma lem3234542 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3234543 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term84 A s t) = (term85 A s t).
Proof. exact (MK_COMB (@lem3234542) (@lem3234489 A s t)). Qed.
Lemma lem3234544 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term86 A s t) = (term87 A s t).
Proof. exact (MK_COMB (@lem3234543 A s t) (@lem3234541 A s t)). Qed.
Lemma lem3234545 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3234546 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term88 A s t) = (term89 A s t).
Proof. exact (MK_COMB (@lem3234545) (@lem3234492 A s t)). Qed.
Lemma lem3234547 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term90 A s t) = (term91 A s t).
Proof. exact (MK_COMB (@lem3234546 A s t) (@lem3234538 A s t)). Qed.
Lemma lem3234548 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3234549 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term92 A s t) = (term93 A s t).
Proof. exact (MK_COMB (@lem3234548) (@lem3234547 A s t)). Qed.
Lemma lem3234550 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term94 A s t) = (term95 A s t).
Proof. exact (MK_COMB (@lem3234549 A s t) (@lem3234544 A s t)). Qed.
Lemma lem3234551 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term44 A s t) = (term94 A s t).
Proof. exact (@lem17646 (term19 A s t) (term30 A s t)). Qed.
Lemma lem3234552 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term44 A s t) = (term95 A s t).
Proof. exact (TRANS (@lem3234551 A s t) (@lem3234550 A s t)). Qed.
Lemma lem3234662 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term96 A P Q) = (term97 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3234663 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term96 A P Q) = (term97 A P Q).
Proof. exact (@lem3234662 A P Q). Qed.
Lemma lem3234664 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term98 A s t) = (term99 A s t).
Proof. exact (@lem3234663 A (term100 A s t) (term101 A s t)). Qed.
Lemma lem3234665 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term102 A s t x) = (term103 A s t x).
Proof. exact (eq_refl (term102 A s t x)). Qed.
Lemma lem3234666 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3234667 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term104 A s t x) = (term72 A s t x).
Proof. exact (MK_COMB (@lem3234666) (@lem3234665 A s t x)). Qed.
Lemma lem3234668 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term105 A s t x) = (term71 A s t x).
Proof. exact (eq_refl (term105 A s t x)). Qed.
Lemma lem3234669 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term106 A s t x) = (term74 A s t x).
Proof. exact (MK_COMB (@lem3234667 A s t x) (@lem3234668 A s t x)). Qed.
Lemma lem3234670 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term107 A s t) = (term82 A s t).
Proof. exact (fun_ext (fun x : A => @lem3234669 A s t x)). Qed.
Lemma lem3234671 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3234672 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term98 A s t) = (term83 A s t).
Proof. exact (MK_COMB (@lem3234671 A) (@lem3234670 A s t)). Qed.
Lemma lem3234673 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3234674 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term108 A s t) = (term109 A s t).
Proof. exact (MK_COMB (@lem3234673) (@lem3234672 A s t)). Qed.
Lemma lem3234675 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term102 A s t x) = (term103 A s t x).
Proof. exact (eq_refl (term102 A s t x)). Qed.
Lemma lem3234676 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term110 A s t) = (term100 A s t).
Proof. exact (fun_ext (fun x : A => @lem3234675 A s t x)). Qed.
Lemma lem3234677 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3234678 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term111 A s t) = (term112 A s t).
Proof. exact (MK_COMB (@lem3234677 A) (@lem3234676 A s t)). Qed.
Lemma lem3234679 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3234680 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term113 A s t) = (term114 A s t).
Proof. exact (MK_COMB (@lem3234679) (@lem3234678 A s t)). Qed.
Lemma lem3234681 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term105 A s t x) = (term71 A s t x).
Proof. exact (eq_refl (term105 A s t x)). Qed.
Lemma lem3234682 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term115 A s t) = (term101 A s t).
Proof. exact (fun_ext (fun x : A => @lem3234681 A s t x)). Qed.
Lemma lem3234683 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3234684 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term116 A s t) = (term117 A s t).
Proof. exact (MK_COMB (@lem3234683 A) (@lem3234682 A s t)). Qed.
Lemma lem3234685 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term99 A s t) = (term118 A s t).
Proof. exact (MK_COMB (@lem3234680 A s t) (@lem3234684 A s t)). Qed.
Lemma lem3234686 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term98 A s t) = (term99 A s t)) = ((term83 A s t) = (term118 A s t)).
Proof. exact (MK_COMB (@lem3234674 A s t) (@lem3234685 A s t)). Qed.
Lemma lem3234687 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term83 A s t) = (term118 A s t).
Proof. exact (EQ_MP (@lem3234686 A s t) (@lem3234664 A s t)). Qed.
Lemma lem3234768 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term85 A s t) = (term85 A s t).
Proof. exact (eq_refl (term85 A s t)). Qed.
Lemma lem3234769 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term87 A s t) = (term119 A s t).
Proof. exact (MK_COMB (@lem3234768 A s t) (@lem3234687 A s t)). Qed.
Lemma lem3234770 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term93 A s t) = (term93 A s t).
Proof. exact (eq_refl (term93 A s t)). Qed.
Lemma lem3234771 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term95 A s t) = (term120 A s t).
Proof. exact (MK_COMB (@lem3234770 A s t) (@lem3234769 A s t)). Qed.
Lemma lem3234773 {A : Type'} (P : Prop) (Q : A -> Prop) : (term121 A P Q) = (term122 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3234774 {A : Type'} (P : Prop) (Q : A -> Prop) : (term121 A P Q) = (term122 A P Q).
Proof. exact (@lem3234773 A P Q). Qed.
Lemma lem3234775 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term123 A s t) = (term124 A s t).
Proof. exact (@lem3234774 A (term58 A s t) (term80 A s t)). Qed.
Lemma lem3234776 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term125 A s t x) = (term68 A s t x).
Proof. exact (eq_refl (term125 A s t x)). Qed.
Lemma lem3234777 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term126 A s t) = (term80 A s t).
Proof. exact (fun_ext (fun x : A => @lem3234776 A s t x)). Qed.
Lemma lem3234778 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3234779 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term127 A s t) = (term81 A s t).
Proof. exact (MK_COMB (@lem3234778 A) (@lem3234777 A s t)). Qed.
Lemma lem3234780 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term89 A s t) = (term89 A s t).
Proof. exact (eq_refl (term89 A s t)). Qed.
Lemma lem3234781 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term123 A s t) = (term91 A s t).
Proof. exact (MK_COMB (@lem3234780 A s t) (@lem3234779 A s t)). Qed.
Lemma lem3234782 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3234783 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term128 A s t) = (term129 A s t).
Proof. exact (MK_COMB (@lem3234782) (@lem3234781 A s t)). Qed.
Lemma lem3234784 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term125 A s t x) = (term68 A s t x).
Proof. exact (eq_refl (term125 A s t x)). Qed.
Lemma lem3234785 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term89 A s t) = (term89 A s t).
Proof. exact (eq_refl (term89 A s t)). Qed.
Lemma lem3234786 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term130 A s t x) = (term131 A s t x).
Proof. exact (MK_COMB (@lem3234785 A s t) (@lem3234784 A s t x)). Qed.
Lemma lem3234787 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term132 A s t) = (term133 A s t).
Proof. exact (fun_ext (fun x : A => @lem3234786 A s t x)). Qed.
Lemma lem3234788 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3234789 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term124 A s t) = (term134 A s t).
Proof. exact (MK_COMB (@lem3234788 A) (@lem3234787 A s t)). Qed.
Lemma lem3234790 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term123 A s t) = (term124 A s t)) = ((term91 A s t) = (term134 A s t)).
Proof. exact (MK_COMB (@lem3234783 A s t) (@lem3234789 A s t)). Qed.
Lemma lem3234791 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term91 A s t) = (term134 A s t).
Proof. exact (EQ_MP (@lem3234790 A s t) (@lem3234775 A s t)). Qed.
Lemma lem3234792 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3234793 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term93 A s t) = (term135 A s t).
Proof. exact (MK_COMB (@lem3234792) (@lem3234791 A s t)). Qed.
Lemma lem3234795 {A : Type'} (P : A -> Prop) (Q : Prop) : (term136 A P Q) = (term137 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3234796 {A : Type'} (P : A -> Prop) (Q : Prop) : (term136 A P Q) = (term137 A P Q).
Proof. exact (@lem3234795 A P Q). Qed.
Lemma lem3234797 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term138 A s t) = (term139 A s t).
Proof. exact (@lem3234796 A (term55 A s t) (term118 A s t)). Qed.
Lemma lem3234798 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term140 A s t x) = (term46 A s t x).
Proof. exact (eq_refl (term140 A s t x)). Qed.
Lemma lem3234799 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term141 A s t) = (term55 A s t).
Proof. exact (fun_ext (fun x : A => @lem3234798 A s t x)). Qed.
Lemma lem3234800 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3234801 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term142 A s t) = (term56 A s t).
Proof. exact (MK_COMB (@lem3234800 A) (@lem3234799 A s t)). Qed.
Lemma lem3234802 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3234803 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term143 A s t) = (term85 A s t).
Proof. exact (MK_COMB (@lem3234802) (@lem3234801 A s t)). Qed.
Lemma lem3234804 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term118 A s t) = (term118 A s t).
Proof. exact (eq_refl (term118 A s t)). Qed.
Lemma lem3234805 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term138 A s t) = (term119 A s t).
Proof. exact (MK_COMB (@lem3234803 A s t) (@lem3234804 A s t)). Qed.
Lemma lem3234806 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3234807 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term144 A s t) = (term145 A s t).
Proof. exact (MK_COMB (@lem3234806) (@lem3234805 A s t)). Qed.
Lemma lem3234808 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term140 A s t x) = (term46 A s t x).
Proof. exact (eq_refl (term140 A s t x)). Qed.
Lemma lem3234809 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3234810 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term146 A s t x) = (term147 A s t x).
Proof. exact (MK_COMB (@lem3234809) (@lem3234808 A s t x)). Qed.
Lemma lem3234811 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term118 A s t) = (term118 A s t).
Proof. exact (eq_refl (term118 A s t)). Qed.
Lemma lem3234812 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term148 A x s t) = (term149 A x s t).
Proof. exact (MK_COMB (@lem3234810 A s t x) (@lem3234811 A s t)). Qed.
Lemma lem3234813 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term150 A s t) = (term151 A s t).
Proof. exact (fun_ext (fun x : A => @lem3234812 A x s t)). Qed.
Lemma lem3234814 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3234815 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term139 A s t) = (term152 A s t).
Proof. exact (MK_COMB (@lem3234814 A) (@lem3234813 A s t)). Qed.
Lemma lem3234816 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term138 A s t) = (term139 A s t)) = ((term119 A s t) = (term152 A s t)).
Proof. exact (MK_COMB (@lem3234807 A s t) (@lem3234815 A s t)). Qed.
Lemma lem3234817 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term119 A s t) = (term152 A s t).
Proof. exact (EQ_MP (@lem3234816 A s t) (@lem3234797 A s t)). Qed.
Lemma lem3234818 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term120 A s t) = (term153 A s t).
Proof. exact (MK_COMB (@lem3234793 A s t) (@lem3234817 A s t)). Qed.
Lemma lem3234820 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term154 A P Q) = (term155 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3234821 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term154 A P Q) = (term155 A P Q).
Proof. exact (@lem3234820 A P Q). Qed.
Lemma lem3234822 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term156 A s t) = (term157 A s t).
Proof. exact (@lem3234821 A (term133 A s t) (term151 A s t)). Qed.
Lemma lem3234823 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term158 A s t x) = (term131 A s t x).
Proof. exact (eq_refl (term158 A s t x)). Qed.
Lemma lem3234824 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term159 A s t) = (term133 A s t).
Proof. exact (fun_ext (fun x : A => @lem3234823 A s t x)). Qed.
Lemma lem3234825 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3234826 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term160 A s t) = (term134 A s t).
Proof. exact (MK_COMB (@lem3234825 A) (@lem3234824 A s t)). Qed.
Lemma lem3234827 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3234828 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term161 A s t) = (term135 A s t).
Proof. exact (MK_COMB (@lem3234827) (@lem3234826 A s t)). Qed.
Lemma lem3234829 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term162 A s t x) = (term149 A x s t).
Proof. exact (eq_refl (term162 A s t x)). Qed.
Lemma lem3234830 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term163 A s t) = (term151 A s t).
Proof. exact (fun_ext (fun x : A => @lem3234829 A x s t)). Qed.
Lemma lem3234831 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3234832 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term164 A s t) = (term152 A s t).
Proof. exact (MK_COMB (@lem3234831 A) (@lem3234830 A s t)). Qed.
Lemma lem3234833 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term156 A s t) = (term153 A s t).
Proof. exact (MK_COMB (@lem3234828 A s t) (@lem3234832 A s t)). Qed.
Lemma lem3234834 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3234835 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term165 A s t) = (term166 A s t).
Proof. exact (MK_COMB (@lem3234834) (@lem3234833 A s t)). Qed.
Lemma lem3234836 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term158 A s t x) = (term131 A s t x).
Proof. exact (eq_refl (term158 A s t x)). Qed.
Lemma lem3234837 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3234838 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term167 A s t x) = (term168 A s t x).
Proof. exact (MK_COMB (@lem3234837) (@lem3234836 A s t x)). Qed.
Lemma lem3234839 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term162 A s t x) = (term149 A x s t).
Proof. exact (eq_refl (term162 A s t x)). Qed.
Lemma lem3234840 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term169 A s t x) = (term170 A x s t).
Proof. exact (MK_COMB (@lem3234838 A s t x) (@lem3234839 A x s t)). Qed.
Lemma lem3234841 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term171 A s t) = (term172 A s t).
Proof. exact (fun_ext (fun x : A => @lem3234840 A x s t)). Qed.
Lemma lem3234842 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3234843 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term157 A s t) = (term173 A s t).
Proof. exact (MK_COMB (@lem3234842 A) (@lem3234841 A s t)). Qed.
Lemma lem3234844 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term156 A s t) = (term157 A s t)) = ((term153 A s t) = (term173 A s t)).
Proof. exact (MK_COMB (@lem3234835 A s t) (@lem3234843 A s t)). Qed.
Lemma lem3234845 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term153 A s t) = (term173 A s t).
Proof. exact (EQ_MP (@lem3234844 A s t) (@lem3234822 A s t)). Qed.
Lemma lem3234846 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term120 A s t) = (term173 A s t).
Proof. exact (TRANS (@lem3234818 A s t) (@lem3234845 A s t)). Qed.
Lemma lem3234847 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term95 A s t) = (term173 A s t).
Proof. exact (TRANS (@lem3234771 A s t) (@lem3234846 A s t)). Qed.
Lemma lem3234848 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term44 A s t) = (term173 A s t).
Proof. exact (TRANS (@lem3234552 A s t) (@lem3234847 A s t)). Qed.
Lemma lem3234849 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term44 A s t) : term173 A s t.
Proof. exact (EQ_MP (@lem3234848 A s t) (@lem3234465 A s t h1)). Qed.
Lemma lem3234850 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term170 A x s t) : term170 A x s t.
Proof. exact (h1). Qed.
Lemma lem3234869 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term71 A s t x) = (term71 A s t x).
Proof. exact (eq_refl (term71 A s t x)). Qed.
Lemma lem3234870 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term101 A s t) = (term101 A s t).
Proof. exact (fun_ext (fun x : A => @lem3234869 A s t x)). Qed.
Lemma lem3234871 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3234872 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term117 A s t) = (term117 A s t).
Proof. exact (MK_COMB (@lem3234871 A) (@lem3234870 A s t)). Qed.
Lemma lem3234889 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term103 A s t x) = (term103 A s t x).
Proof. exact (eq_refl (term103 A s t x)). Qed.
Lemma lem3234890 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term100 A s t) = (term100 A s t).
Proof. exact (fun_ext (fun x : A => @lem3234889 A s t x)). Qed.
Lemma lem3234891 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3234892 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term112 A s t) = (term112 A s t).
Proof. exact (MK_COMB (@lem3234891 A) (@lem3234890 A s t)). Qed.
Lemma lem3234893 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3234894 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term114 A s t) = (term114 A s t).
Proof. exact (MK_COMB (@lem3234893) (@lem3234892 A s t)). Qed.
Lemma lem3234895 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term118 A s t) = (term118 A s t).
Proof. exact (MK_COMB (@lem3234894 A s t) (@lem3234872 A s t)). Qed.
Lemma lem3234908 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term147 A s t x) = (term147 A s t x).
Proof. exact (eq_refl (term147 A s t x)). Qed.
Lemma lem3234909 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term149 A x s t) = (term149 A x s t).
Proof. exact (MK_COMB (@lem3234908 A s t x) (@lem3234895 A s t)). Qed.
Lemma lem3234948 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term68 A s t x) = (term68 A s t x).
Proof. exact (eq_refl (term68 A s t x)). Qed.
Lemma lem3234959 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term47 A s t x) = (term47 A s t x).
Proof. exact (eq_refl (term47 A s t x)). Qed.
Lemma lem3234960 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term57 A s t) = (term57 A s t).
Proof. exact (fun_ext (fun x : A => @lem3234959 A s t x)). Qed.
Lemma lem3234961 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3234962 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term58 A s t) = (term58 A s t).
Proof. exact (MK_COMB (@lem3234961 A) (@lem3234960 A s t)). Qed.
Lemma lem3234963 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3234964 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term89 A s t) = (term89 A s t).
Proof. exact (MK_COMB (@lem3234963) (@lem3234962 A s t)). Qed.
Lemma lem3234965 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term131 A s t x) = (term131 A s t x).
Proof. exact (MK_COMB (@lem3234964 A s t) (@lem3234948 A s t x)). Qed.
Lemma lem3234966 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3234967 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term168 A s t x) = (term168 A s t x).
Proof. exact (MK_COMB (@lem3234966) (@lem3234965 A s t x)). Qed.
Lemma lem3234968 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term170 A x s t) = (term170 A x s t).
Proof. exact (MK_COMB (@lem3234967 A s t x) (@lem3234909 A x s t)). Qed.
Lemma lem3234969 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term170 A x s t) : term170 A x s t.
Proof. exact (EQ_MP (@lem3234968 A x s t) (@lem3234850 A x s t h1)). Qed.
Lemma lem3234970 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term131 A s t x) : term131 A s t x.
Proof. exact (h1). Qed.
Lemma lem3234971 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term149 A x s t) : term149 A x s t.
Proof. exact (h1). Qed.
Lemma lem3234972 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term131 A s t x) : term68 A s t x.
Proof. exact (proj2 (@lem3234970 A s t x h1)). Qed.
Lemma lem3234973 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term131 A s t x) : term58 A s t.
Proof. exact (proj1 (@lem3234970 A s t x h1)). Qed.
Lemma lem3234974 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term131 A s t x) : term65 A s t x.
Proof. exact (proj2 (@lem3234972 A s t x h1)). Qed.
Lemma lem3234975 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term131 A s t x) : term174 A s t x.
Proof. exact (proj1 (@lem3234972 A s t x h1)). Qed.
Lemma lem3234976 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term60 A s t x) : term60 A s t x.
Proof. exact (h1). Qed.
Lemma lem3234980 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term25 A s t x) : term25 A s t x.
Proof. exact (h1). Qed.
Lemma lem3234984 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term25 A s t x) : term25 A s t x.
Proof. exact (h1). Qed.
Lemma lem3234988 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term149 A x s t) : term118 A s t.
Proof. exact (proj2 (@lem3234971 A x s t h1)). Qed.
Lemma lem3234989 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term149 A x s t) : term46 A s t x.
Proof. exact (proj1 (@lem3234971 A x s t h1)). Qed.
Lemma lem3234990 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term149 A x s t) : term117 A s t.
Proof. exact (proj2 (@lem3234988 A x s t h1)). Qed.
Lemma lem3235018 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3235043 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3235068 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3235076 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term47 A s t x) = (term47 A s t x).
Proof. exact (eq_refl (term47 A s t x)). Qed.
Lemma lem3235077 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term57 A s t) = (term57 A s t).
Proof. exact (fun_ext (fun x : A => @lem3235076 A s t x)). Qed.
Lemma lem3235078 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3235080 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term58 A s t) = (term58 A s t).
Proof. exact (MK_COMB (@lem3235078 A) (@lem3235077 A s t)). Qed.
Lemma lem3235081 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term131 A s t x) : term58 A s t.
Proof. exact (EQ_MP (@lem3235080 A s t) (@lem3234973 A s t x h1)). Qed.
Lemma lem3235085 {A : Type'} (t : A -> Prop) (x : A) (h1 : term61 A t x) : term61 A t x.
Proof. exact (h1). Qed.
Lemma lem3235089 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3235106 {A : Type'} (t : A -> Prop) (x : A) (h1 : term61 A t x) : term61 A t x.
Proof. exact (h1). Qed.
Lemma lem3235110 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3235127 {A : Type'} (t : A -> Prop) (x : A) (h1 : term61 A t x) : term61 A t x.
Proof. exact (h1). Qed.
Lemma lem3235131 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3235168 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term71 A s t x) = (term175 A s t x).
Proof. exact (@lem19699 (term61 A s x) (term61 A t x) (t x)). Qed.
Lemma lem3235169 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term101 A s t) = (term176 A s t).
Proof. exact (fun_ext (fun x : A => @lem3235168 A s t x)). Qed.
Lemma lem3235170 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3235172 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term117 A s t) = (term177 A s t).
Proof. exact (MK_COMB (@lem3235170 A) (@lem3235169 A s t)). Qed.
Lemma lem3235173 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term149 A x s t) : term177 A s t.
Proof. exact (EQ_MP (@lem3235172 A s t) (@lem3234990 A x s t h1)). Qed.
Lemma lem3235191 {A : Type'} (_33200 : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term131 A s t x) : term178 A s t _33200.
Proof. exact (@lem3235081 A s t x h1 _33200). Qed.
Lemma lem3235192 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33200 : A) : (term178 A s t _33200) = (term47 A s t _33200).
Proof. exact (eq_refl (term178 A s t _33200)). Qed.
Lemma lem3235203 {A : Type'} (_33204 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term149 A x s t) : term179 A s t _33204.
Proof. exact (@lem3235173 A x s t h1 _33204). Qed.
Lemma lem3235204 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33204 : A) : (term179 A s t _33204) = (term175 A s t _33204).
Proof. exact (eq_refl (term179 A s t _33204)). Qed.
Lemma lem3235205 {A : Type'} (_33204 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term149 A x s t) : term175 A s t _33204.
Proof. exact (EQ_MP (@lem3235204 A s t _33204) (@lem3235203 A _33204 x s t h1)). Qed.
Lemma lem3235215 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term60 A s t x) : term61 A s x.
Proof. exact (proj1 (@lem3234976 A s t x h1)). Qed.
Lemma lem3235219 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3235229 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term60 A s t x) : term61 A t x.
Proof. exact (proj2 (@lem3234976 A s t x h1)). Qed.
Lemma lem3235231 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3235241 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term60 A s t x) : term61 A t x.
Proof. exact (proj2 (@lem3234976 A s t x h1)). Qed.
Lemma lem3235243 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3235249 {A : Type'} (_33200 : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term131 A s t x) : term47 A s t _33200.
Proof. exact (EQ_MP (@lem3235192 A s t _33200) (@lem3235191 A _33200 s t x h1)). Qed.
Lemma lem3235251 {A : Type'} (t : A -> Prop) (x : A) (h1 : term61 A t x) : term61 A t x.
Proof. exact (h1). Qed.
Lemma lem3235253 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3235261 {A : Type'} (t : A -> Prop) (x : A) (h1 : term61 A t x) : term61 A t x.
Proof. exact (h1). Qed.
Lemma lem3235263 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3235271 {A : Type'} (t : A -> Prop) (x : A) (h1 : term61 A t x) : term61 A t x.
Proof. exact (h1). Qed.
Lemma lem3235273 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3235289 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term149 A x s t) : term61 A t x.
Proof. exact (proj2 (@lem3234989 A x s t h1)). Qed.
Lemma lem3235295 {A : Type'} (_33204 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term149 A x s t) : term47 A s t _33204.
Proof. exact (proj1 (@lem3235205 A _33204 x s t h1)). Qed.
Lemma lem3235303 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3235304 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : term180 A s x.
Proof. exact (fun h0 : term61 A s x => @lem3235303 A s x h1). Qed.
Lemma lem3235306 (p : Prop) : (term181 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3235307 {A : Type'} (s : A -> Prop) (x : A) : (term180 A s x) = (s x).
Proof. exact (@lem3235306 (s x)). Qed.
Lemma lem3235308 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem3235307 A s x) (@lem3235304 A s x h1)). Qed.
Lemma lem3235311 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3235313 {A : Type'} (s : A -> Prop) (x : A) : (term61 A s x) = (term182 A s x).
Proof. exact (@lem3235311 (s x)). Qed.
Lemma lem3235316 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term60 A s t x) : term182 A s x.
Proof. exact (EQ_MP (@lem3235313 A s x) (@lem3235215 A s t x h1)). Qed.
Lemma lem3235319 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : s x) (h2 : term60 A s t x) : False.
Proof. exact (@lem3235316 A s t x h2 (@lem3235308 A s x h1)). Qed.
Lemma lem3235320 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : s x) (h2 : term60 A s t x) : term183.
Proof. exact (fun h0 : ~ False => @lem3235319 A s t x h1 h2). Qed.
Lemma lem3235322 (p : Prop) : (term181 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3235323 : term183 = False.
Proof. exact (@lem3235322 False). Qed.
Lemma lem3235324 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : s x) (h2 : term60 A s t x) : False.
Proof. exact (EQ_MP (@lem3235323) (@lem3235320 A s t x h1 h2)). Qed.
Lemma lem3235326 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3235327 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : term180 A t x.
Proof. exact (fun h0 : term61 A t x => @lem3235326 A t x h1). Qed.
Lemma lem3235329 (p : Prop) : (term181 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3235330 {A : Type'} (t : A -> Prop) (x : A) : (term180 A t x) = (t x).
Proof. exact (@lem3235329 (t x)). Qed.
Lemma lem3235331 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem3235330 A t x) (@lem3235327 A t x h1)). Qed.
Lemma lem3235334 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3235336 {A : Type'} (t : A -> Prop) (x : A) : (term61 A t x) = (term182 A t x).
Proof. exact (@lem3235334 (t x)). Qed.
Lemma lem3235339 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term60 A s t x) : term182 A t x.
Proof. exact (EQ_MP (@lem3235336 A t x) (@lem3235229 A s t x h1)). Qed.
Lemma lem3235342 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term60 A s t x) : False.
Proof. exact (@lem3235339 A s t x h2 (@lem3235331 A t x h1)). Qed.
Lemma lem3235343 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term60 A s t x) : term183.
Proof. exact (fun h0 : ~ False => @lem3235342 A s t x h1 h2). Qed.
Lemma lem3235345 (p : Prop) : (term181 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3235346 : term183 = False.
Proof. exact (@lem3235345 False). Qed.
Lemma lem3235347 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term60 A s t x) : False.
Proof. exact (EQ_MP (@lem3235346) (@lem3235343 A s t x h1 h2)). Qed.
Lemma lem3235349 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3235350 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : term180 A t x.
Proof. exact (fun h0 : term61 A t x => @lem3235349 A t x h1). Qed.
Lemma lem3235352 (p : Prop) : (term181 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3235353 {A : Type'} (t : A -> Prop) (x : A) : (term180 A t x) = (t x).
Proof. exact (@lem3235352 (t x)). Qed.
Lemma lem3235354 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem3235353 A t x) (@lem3235350 A t x h1)). Qed.
Lemma lem3235357 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3235359 {A : Type'} (t : A -> Prop) (x : A) : (term61 A t x) = (term182 A t x).
Proof. exact (@lem3235357 (t x)). Qed.
Lemma lem3235362 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term60 A s t x) : term182 A t x.
Proof. exact (EQ_MP (@lem3235359 A t x) (@lem3235241 A s t x h1)). Qed.
Lemma lem3235365 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term60 A s t x) : False.
Proof. exact (@lem3235362 A s t x h2 (@lem3235354 A t x h1)). Qed.
Lemma lem3235366 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term60 A s t x) : term183.
Proof. exact (fun h0 : ~ False => @lem3235365 A s t x h1 h2). Qed.
Lemma lem3235368 (p : Prop) : (term181 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3235369 : term183 = False.
Proof. exact (@lem3235368 False). Qed.
Lemma lem3235370 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term60 A s t x) : False.
Proof. exact (EQ_MP (@lem3235369) (@lem3235366 A s t x h1 h2)). Qed.
Lemma lem3235372 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3235373 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : term180 A s x.
Proof. exact (fun h0 : term61 A s x => @lem3235372 A s x h1). Qed.
Lemma lem3235375 (p : Prop) : (term181 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3235376 {A : Type'} (s : A -> Prop) (x : A) : (term180 A s x) = (s x).
Proof. exact (@lem3235375 (s x)). Qed.
Lemma lem3235377 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem3235376 A s x) (@lem3235373 A s x h1)). Qed.
Lemma lem3235383 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3235384 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33200 : A) : (term47 A s t _33200) = (term184 A t s _33200).
Proof. exact (@lem3235383 (t _33200) (term61 A s _33200)). Qed.
Lemma lem3235390 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3235391 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33200 : A) : (term185 A s t _33200) = (term186 A t s _33200).
Proof. exact (MK_COMB (@lem3235390) (@lem3235384 A t s _33200)). Qed.
Lemma lem3235397 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33200 : A) : (term184 A t s _33200) = (term184 A t s _33200).
Proof. exact (eq_refl (term184 A t s _33200)). Qed.
Lemma lem3235398 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33200 : A) : ((term47 A s t _33200) = (term184 A t s _33200)) = ((term184 A t s _33200) = (term184 A t s _33200)).
Proof. exact (MK_COMB (@lem3235391 A t s _33200) (@lem3235397 A t s _33200)). Qed.
Lemma lem3235400 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3235401 (x : Prop) : (x = x) = True.
Proof. exact (@lem3235400 Prop x). Qed.
Lemma lem3235402 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33200 : A) : ((term184 A t s _33200) = (term184 A t s _33200)) = True.
Proof. exact (@lem3235401 (term184 A t s _33200)). Qed.
Lemma lem3235403 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33200 : A) : ((term47 A s t _33200) = (term184 A t s _33200)) = True.
Proof. exact (TRANS (@lem3235398 A t s _33200) (@lem3235402 A t s _33200)). Qed.
Lemma lem3235404 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33200 : A) : True = ((term47 A s t _33200) = (term184 A t s _33200)).
Proof. exact (SYM (@lem3235403 A t s _33200)). Qed.
Lemma lem3235405 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33200 : A) : (term47 A s t _33200) = (term184 A t s _33200).
Proof. exact (EQ_MP (@lem3235404 A t s _33200) (@lem0)). Qed.
Lemma lem3235406 {A : Type'} (_33200 : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term131 A s t x) : term184 A t s _33200.
Proof. exact (EQ_MP (@lem3235405 A t s _33200) (@lem3235249 A _33200 s t x h1)). Qed.
Lemma lem3235408 (b : Prop) (a : Prop) : (a \/ b) = (term187 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3235409 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33200 : A) : (term184 A t s _33200) = (term188 A s t _33200).
Proof. exact (@lem3235408 (term61 A s _33200) (t _33200)). Qed.
Lemma lem3235411 (a : Prop) : (term42 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3235412 {A : Type'} (s : A -> Prop) (_33200 : A) : (term189 A s _33200) = (s _33200).
Proof. exact (@lem3235411 (s _33200)). Qed.
Lemma lem3235413 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3235414 {A : Type'} (s : A -> Prop) (_33200 : A) : (term190 A s _33200) = (term14 A s _33200).
Proof. exact (MK_COMB (@lem3235413) (@lem3235412 A s _33200)). Qed.
Lemma lem3235415 {A : Type'} (t : A -> Prop) (_33200 : A) : (t _33200) = (t _33200).
Proof. exact (eq_refl (t _33200)). Qed.
Lemma lem3235416 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33200 : A) : (term188 A s t _33200) = (term16 A s t _33200).
Proof. exact (MK_COMB (@lem3235414 A s _33200) (@lem3235415 A t _33200)). Qed.
Lemma lem3235417 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33200 : A) : (term184 A t s _33200) = (term16 A s t _33200).
Proof. exact (TRANS (@lem3235409 A s t _33200) (@lem3235416 A s t _33200)). Qed.
Lemma lem3235420 {A : Type'} (_33200 : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term131 A s t x) : term16 A s t _33200.
Proof. exact (EQ_MP (@lem3235417 A s t _33200) (@lem3235406 A _33200 s t x h1)). Qed.
Lemma lem3235421 {A : Type'} (_33200 : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term131 A s t x) : term16 A s t _33200.
Proof. exact (@lem3235420 A _33200 s t x h1). Qed.
Lemma lem3235422 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term131 A s t x) : term16 A s t x.
Proof. exact (@lem3235421 A x s t x h1). Qed.
Lemma lem3235425 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : s x) (h2 : term131 A s t x) : t x.
Proof. exact (@lem3235422 A s t x h2 (@lem3235377 A s x h1)). Qed.
Lemma lem3235426 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : s x) (h2 : term131 A s t x) : term180 A t x.
Proof. exact (fun h0 : term61 A t x => @lem3235425 A s t x h1 h2). Qed.
Lemma lem3235428 (p : Prop) : (term181 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3235429 {A : Type'} (t : A -> Prop) (x : A) : (term180 A t x) = (t x).
Proof. exact (@lem3235428 (t x)). Qed.
Lemma lem3235430 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : s x) (h2 : term131 A s t x) : t x.
Proof. exact (EQ_MP (@lem3235429 A t x) (@lem3235426 A s t x h1 h2)). Qed.
Lemma lem3235433 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3235435 {A : Type'} (t : A -> Prop) (x : A) : (term61 A t x) = (term182 A t x).
Proof. exact (@lem3235433 (t x)). Qed.
Lemma lem3235438 {A : Type'} (t : A -> Prop) (x : A) (h1 : term61 A t x) : term182 A t x.
Proof. exact (EQ_MP (@lem3235435 A t x) (@lem3235251 A t x h1)). Qed.
Lemma lem3235441 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : s x) (h3 : term131 A s t x) : False.
Proof. exact (@lem3235438 A t x h1 (@lem3235430 A s t x h2 h3)). Qed.
Lemma lem3235442 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : s x) (h3 : term131 A s t x) : term183.
Proof. exact (fun h0 : ~ False => @lem3235441 A s t x h1 h2 h3). Qed.
Lemma lem3235444 (p : Prop) : (term181 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3235445 : term183 = False.
Proof. exact (@lem3235444 False). Qed.
Lemma lem3235446 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : s x) (h3 : term131 A s t x) : False.
Proof. exact (EQ_MP (@lem3235445) (@lem3235442 A s t x h1 h2 h3)). Qed.
Lemma lem3235448 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3235449 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : term180 A t x.
Proof. exact (fun h0 : term61 A t x => @lem3235448 A t x h1). Qed.
Lemma lem3235451 (p : Prop) : (term181 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3235452 {A : Type'} (t : A -> Prop) (x : A) : (term180 A t x) = (t x).
Proof. exact (@lem3235451 (t x)). Qed.
Lemma lem3235453 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem3235452 A t x) (@lem3235449 A t x h1)). Qed.
Lemma lem3235456 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3235458 {A : Type'} (t : A -> Prop) (x : A) : (term61 A t x) = (term182 A t x).
Proof. exact (@lem3235456 (t x)). Qed.
Lemma lem3235461 {A : Type'} (t : A -> Prop) (x : A) (h1 : term61 A t x) : term182 A t x.
Proof. exact (EQ_MP (@lem3235458 A t x) (@lem3235261 A t x h1)). Qed.
Lemma lem3235464 {A : Type'} (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : t x) : False.
Proof. exact (@lem3235461 A t x h1 (@lem3235453 A t x h2)). Qed.
Lemma lem3235465 {A : Type'} (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : t x) : term183.
Proof. exact (fun h0 : ~ False => @lem3235464 A t x h1 h2). Qed.
Lemma lem3235467 (p : Prop) : (term181 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3235468 : term183 = False.
Proof. exact (@lem3235467 False). Qed.
Lemma lem3235469 {A : Type'} (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3235468) (@lem3235465 A t x h1 h2)). Qed.
Lemma lem3235471 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3235472 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : term180 A t x.
Proof. exact (fun h0 : term61 A t x => @lem3235471 A t x h1). Qed.
Lemma lem3235474 (p : Prop) : (term181 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3235475 {A : Type'} (t : A -> Prop) (x : A) : (term180 A t x) = (t x).
Proof. exact (@lem3235474 (t x)). Qed.
Lemma lem3235476 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem3235475 A t x) (@lem3235472 A t x h1)). Qed.
Lemma lem3235479 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3235481 {A : Type'} (t : A -> Prop) (x : A) : (term61 A t x) = (term182 A t x).
Proof. exact (@lem3235479 (t x)). Qed.
Lemma lem3235484 {A : Type'} (t : A -> Prop) (x : A) (h1 : term61 A t x) : term182 A t x.
Proof. exact (EQ_MP (@lem3235481 A t x) (@lem3235271 A t x h1)). Qed.
Lemma lem3235487 {A : Type'} (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : t x) : False.
Proof. exact (@lem3235484 A t x h1 (@lem3235476 A t x h2)). Qed.
Lemma lem3235488 {A : Type'} (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : t x) : term183.
Proof. exact (fun h0 : ~ False => @lem3235487 A t x h1 h2). Qed.
Lemma lem3235490 (p : Prop) : (term181 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3235491 : term183 = False.
Proof. exact (@lem3235490 False). Qed.
Lemma lem3235492 {A : Type'} (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3235491) (@lem3235488 A t x h1 h2)). Qed.
Lemma lem3235494 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term149 A x s t) : s x.
Proof. exact (proj1 (@lem3234989 A x s t h1)). Qed.
Lemma lem3235495 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term149 A x s t) : term180 A s x.
Proof. exact (fun h0 : term61 A s x => @lem3235494 A x s t h1). Qed.
Lemma lem3235497 (p : Prop) : (term181 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3235498 {A : Type'} (s : A -> Prop) (x : A) : (term180 A s x) = (s x).
Proof. exact (@lem3235497 (s x)). Qed.
Lemma lem3235499 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term149 A x s t) : s x.
Proof. exact (EQ_MP (@lem3235498 A s x) (@lem3235495 A x s t h1)). Qed.
Lemma lem3235505 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3235506 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33204 : A) : (term47 A s t _33204) = (term184 A t s _33204).
Proof. exact (@lem3235505 (t _33204) (term61 A s _33204)). Qed.
Lemma lem3235512 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3235513 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33204 : A) : (term185 A s t _33204) = (term186 A t s _33204).
Proof. exact (MK_COMB (@lem3235512) (@lem3235506 A t s _33204)). Qed.
Lemma lem3235519 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33204 : A) : (term184 A t s _33204) = (term184 A t s _33204).
Proof. exact (eq_refl (term184 A t s _33204)). Qed.
Lemma lem3235520 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33204 : A) : ((term47 A s t _33204) = (term184 A t s _33204)) = ((term184 A t s _33204) = (term184 A t s _33204)).
Proof. exact (MK_COMB (@lem3235513 A t s _33204) (@lem3235519 A t s _33204)). Qed.
Lemma lem3235522 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3235523 (x : Prop) : (x = x) = True.
Proof. exact (@lem3235522 Prop x). Qed.
Lemma lem3235524 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33204 : A) : ((term184 A t s _33204) = (term184 A t s _33204)) = True.
Proof. exact (@lem3235523 (term184 A t s _33204)). Qed.
Lemma lem3235525 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33204 : A) : ((term47 A s t _33204) = (term184 A t s _33204)) = True.
Proof. exact (TRANS (@lem3235520 A t s _33204) (@lem3235524 A t s _33204)). Qed.
Lemma lem3235526 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33204 : A) : True = ((term47 A s t _33204) = (term184 A t s _33204)).
Proof. exact (SYM (@lem3235525 A t s _33204)). Qed.
Lemma lem3235527 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33204 : A) : (term47 A s t _33204) = (term184 A t s _33204).
Proof. exact (EQ_MP (@lem3235526 A t s _33204) (@lem0)). Qed.
Lemma lem3235528 {A : Type'} (_33204 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term149 A x s t) : term184 A t s _33204.
Proof. exact (EQ_MP (@lem3235527 A t s _33204) (@lem3235295 A _33204 x s t h1)). Qed.
Lemma lem3235530 (b : Prop) (a : Prop) : (a \/ b) = (term187 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3235531 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33204 : A) : (term184 A t s _33204) = (term188 A s t _33204).
Proof. exact (@lem3235530 (term61 A s _33204) (t _33204)). Qed.
Lemma lem3235533 (a : Prop) : (term42 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3235534 {A : Type'} (s : A -> Prop) (_33204 : A) : (term189 A s _33204) = (s _33204).
Proof. exact (@lem3235533 (s _33204)). Qed.
Lemma lem3235535 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3235536 {A : Type'} (s : A -> Prop) (_33204 : A) : (term190 A s _33204) = (term14 A s _33204).
Proof. exact (MK_COMB (@lem3235535) (@lem3235534 A s _33204)). Qed.
Lemma lem3235537 {A : Type'} (t : A -> Prop) (_33204 : A) : (t _33204) = (t _33204).
Proof. exact (eq_refl (t _33204)). Qed.
Lemma lem3235538 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33204 : A) : (term188 A s t _33204) = (term16 A s t _33204).
Proof. exact (MK_COMB (@lem3235536 A s _33204) (@lem3235537 A t _33204)). Qed.
Lemma lem3235539 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33204 : A) : (term184 A t s _33204) = (term16 A s t _33204).
Proof. exact (TRANS (@lem3235531 A s t _33204) (@lem3235538 A s t _33204)). Qed.
Lemma lem3235542 {A : Type'} (_33204 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term149 A x s t) : term16 A s t _33204.
Proof. exact (EQ_MP (@lem3235539 A s t _33204) (@lem3235528 A _33204 x s t h1)). Qed.
Lemma lem3235543 {A : Type'} (_33204 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term149 A x s t) : term16 A s t _33204.
Proof. exact (@lem3235542 A _33204 x s t h1). Qed.
Lemma lem3235544 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term149 A x s t) : term16 A s t x.
Proof. exact (@lem3235543 A x x s t h1). Qed.
Lemma lem3235547 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term149 A x s t) : t x.
Proof. exact (@lem3235544 A x s t h1 (@lem3235499 A x s t h1)). Qed.
Lemma lem3235548 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term149 A x s t) : term180 A t x.
Proof. exact (fun h0 : term61 A t x => @lem3235547 A x s t h1). Qed.
Lemma lem3235550 (p : Prop) : (term181 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3235551 {A : Type'} (t : A -> Prop) (x : A) : (term180 A t x) = (t x).
Proof. exact (@lem3235550 (t x)). Qed.
Lemma lem3235552 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term149 A x s t) : t x.
Proof. exact (EQ_MP (@lem3235551 A t x) (@lem3235548 A x s t h1)). Qed.
Lemma lem3235555 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3235557 {A : Type'} (t : A -> Prop) (x : A) : (term61 A t x) = (term182 A t x).
Proof. exact (@lem3235555 (t x)). Qed.
Lemma lem3235560 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term149 A x s t) : term182 A t x.
Proof. exact (EQ_MP (@lem3235557 A t x) (@lem3235289 A x s t h1)). Qed.
Lemma lem3235563 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term149 A x s t) : False.
Proof. exact (@lem3235560 A x s t h1 (@lem3235552 A x s t h1)). Qed.
Lemma lem3235564 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term149 A x s t) : term183.
Proof. exact (fun h0 : ~ False => @lem3235563 A x s t h1). Qed.
Lemma lem3235566 (p : Prop) : (term181 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3235567 : term183 = False.
Proof. exact (@lem3235566 False). Qed.
Lemma lem3235568 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term149 A x s t) : False.
Proof. exact (EQ_MP (@lem3235567) (@lem3235564 A x s t h1)). Qed.
Lemma lem3235569 {A : Type'} (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3235492 A t x h1 h2) (fun h3 : False => @lem3235273 A t x h2)). Qed.
Lemma lem3235570 {A : Type'} (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3235569 A t x h1 h2) (@lem3235273 A t x h2)). Qed.
Lemma lem3235571 {A : Type'} (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : t x) : (term61 A t x) = False.
Proof. exact (prop_ext (fun h3 : term61 A t x => @lem3235570 A t x h1 h2) (fun h3 : False => @lem3235271 A t x h1)). Qed.
Lemma lem3235572 {A : Type'} (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3235571 A t x h1 h2) (@lem3235271 A t x h1)). Qed.
Lemma lem3235573 {A : Type'} (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3235469 A t x h1 h2) (fun h3 : False => @lem3235263 A t x h2)). Qed.
Lemma lem3235574 {A : Type'} (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3235573 A t x h1 h2) (@lem3235263 A t x h2)). Qed.
Lemma lem3235575 {A : Type'} (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : t x) : (term61 A t x) = False.
Proof. exact (prop_ext (fun h3 : term61 A t x => @lem3235574 A t x h1 h2) (fun h3 : False => @lem3235261 A t x h1)). Qed.
Lemma lem3235576 {A : Type'} (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3235575 A t x h1 h2) (@lem3235261 A t x h1)). Qed.
Lemma lem3235577 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : s x) (h3 : term131 A s t x) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem3235446 A s t x h1 h2 h3) (fun h4 : False => @lem3235253 A s x h2)). Qed.
Lemma lem3235578 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : s x) (h3 : term131 A s t x) : False.
Proof. exact (EQ_MP (@lem3235577 A s t x h1 h2 h3) (@lem3235253 A s x h2)). Qed.
Lemma lem3235579 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : s x) (h3 : term131 A s t x) : (term61 A t x) = False.
Proof. exact (prop_ext (fun h4 : term61 A t x => @lem3235578 A s t x h1 h2 h3) (fun h4 : False => @lem3235251 A t x h1)). Qed.
Lemma lem3235580 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : s x) (h3 : term131 A s t x) : False.
Proof. exact (EQ_MP (@lem3235579 A s t x h1 h2 h3) (@lem3235251 A t x h1)). Qed.
Lemma lem3235581 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term60 A s t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3235370 A s t x h1 h2) (fun h3 : False => @lem3235243 A t x h1)). Qed.
Lemma lem3235582 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term60 A s t x) : False.
Proof. exact (EQ_MP (@lem3235581 A s t x h1 h2) (@lem3235243 A t x h1)). Qed.
Lemma lem3235583 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term60 A s t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3235347 A s t x h1 h2) (fun h3 : False => @lem3235231 A t x h1)). Qed.
Lemma lem3235584 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term60 A s t x) : False.
Proof. exact (EQ_MP (@lem3235583 A s t x h1 h2) (@lem3235231 A t x h1)). Qed.
Lemma lem3235585 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : s x) (h2 : term60 A s t x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3235324 A s t x h1 h2) (fun h3 : False => @lem3235219 A s x h1)). Qed.
Lemma lem3235586 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : s x) (h2 : term60 A s t x) : False.
Proof. exact (EQ_MP (@lem3235585 A s t x h1 h2) (@lem3235219 A s x h1)). Qed.
Lemma lem3235587 {A : Type'} (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3235572 A t x h1 h2) (fun h3 : False => @lem3235131 A t x h2)). Qed.
Lemma lem3235588 {A : Type'} (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3235587 A t x h1 h2) (@lem3235131 A t x h2)). Qed.
Lemma lem3235589 {A : Type'} (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : t x) : (term61 A t x) = False.
Proof. exact (prop_ext (fun h3 : term61 A t x => @lem3235588 A t x h1 h2) (fun h3 : False => @lem3235127 A t x h1)). Qed.
Lemma lem3235590 {A : Type'} (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3235589 A t x h1 h2) (@lem3235127 A t x h1)). Qed.
Lemma lem3235591 {A : Type'} (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3235576 A t x h1 h2) (fun h3 : False => @lem3235110 A t x h2)). Qed.
Lemma lem3235592 {A : Type'} (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3235591 A t x h1 h2) (@lem3235110 A t x h2)). Qed.
Lemma lem3235593 {A : Type'} (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : t x) : (term61 A t x) = False.
Proof. exact (prop_ext (fun h3 : term61 A t x => @lem3235592 A t x h1 h2) (fun h3 : False => @lem3235106 A t x h1)). Qed.
Lemma lem3235594 {A : Type'} (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3235593 A t x h1 h2) (@lem3235106 A t x h1)). Qed.
Lemma lem3235595 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : s x) (h3 : term131 A s t x) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem3235580 A s t x h1 h2 h3) (fun h4 : False => @lem3235089 A s x h2)). Qed.
Lemma lem3235596 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : s x) (h3 : term131 A s t x) : False.
Proof. exact (EQ_MP (@lem3235595 A s t x h1 h2 h3) (@lem3235089 A s x h2)). Qed.
Lemma lem3235597 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : s x) (h3 : term131 A s t x) : (term61 A t x) = False.
Proof. exact (prop_ext (fun h4 : term61 A t x => @lem3235596 A s t x h1 h2 h3) (fun h4 : False => @lem3235085 A t x h1)). Qed.
Lemma lem3235598 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : s x) (h3 : term131 A s t x) : False.
Proof. exact (EQ_MP (@lem3235597 A s t x h1 h2 h3) (@lem3235085 A t x h1)). Qed.
Lemma lem3235599 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term60 A s t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3235582 A s t x h1 h2) (fun h3 : False => @lem3235068 A t x h1)). Qed.
Lemma lem3235600 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term60 A s t x) : False.
Proof. exact (EQ_MP (@lem3235599 A s t x h1 h2) (@lem3235068 A t x h1)). Qed.
Lemma lem3235601 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term60 A s t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3235584 A s t x h1 h2) (fun h3 : False => @lem3235043 A t x h1)). Qed.
Lemma lem3235602 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term60 A s t x) : False.
Proof. exact (EQ_MP (@lem3235601 A s t x h1 h2) (@lem3235043 A t x h1)). Qed.
Lemma lem3235603 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : s x) (h2 : term60 A s t x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3235586 A s t x h1 h2) (fun h3 : False => @lem3235018 A s x h1)). Qed.
Lemma lem3235604 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : s x) (h2 : term60 A s t x) : False.
Proof. exact (EQ_MP (@lem3235603 A s t x h1 h2) (@lem3235018 A s x h1)). Qed.
Lemma lem3235605 {A : Type'} (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3235590 A t x h1 h2) (fun h3 : False => @lem3235131 A t x h2)). Qed.
Lemma lem3235606 {A : Type'} (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3235605 A t x h1 h2) (@lem3235131 A t x h2)). Qed.
Lemma lem3235607 {A : Type'} (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : t x) : (term61 A t x) = False.
Proof. exact (prop_ext (fun h3 : term61 A t x => @lem3235606 A t x h1 h2) (fun h3 : False => @lem3235127 A t x h1)). Qed.
Lemma lem3235608 {A : Type'} (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3235607 A t x h1 h2) (@lem3235127 A t x h1)). Qed.
Lemma lem3235609 {A : Type'} (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3235594 A t x h1 h2) (fun h3 : False => @lem3235110 A t x h2)). Qed.
Lemma lem3235610 {A : Type'} (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3235609 A t x h1 h2) (@lem3235110 A t x h2)). Qed.
Lemma lem3235611 {A : Type'} (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : t x) : (term61 A t x) = False.
Proof. exact (prop_ext (fun h3 : term61 A t x => @lem3235610 A t x h1 h2) (fun h3 : False => @lem3235106 A t x h1)). Qed.
Lemma lem3235612 {A : Type'} (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3235611 A t x h1 h2) (@lem3235106 A t x h1)). Qed.
Lemma lem3235613 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : s x) (h3 : term131 A s t x) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem3235598 A s t x h1 h2 h3) (fun h4 : False => @lem3235089 A s x h2)). Qed.
Lemma lem3235614 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : s x) (h3 : term131 A s t x) : False.
Proof. exact (EQ_MP (@lem3235613 A s t x h1 h2 h3) (@lem3235089 A s x h2)). Qed.
Lemma lem3235615 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : s x) (h3 : term131 A s t x) : (term61 A t x) = False.
Proof. exact (prop_ext (fun h4 : term61 A t x => @lem3235614 A s t x h1 h2 h3) (fun h4 : False => @lem3235085 A t x h1)). Qed.
Lemma lem3235616 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : s x) (h3 : term131 A s t x) : False.
Proof. exact (EQ_MP (@lem3235615 A s t x h1 h2 h3) (@lem3235085 A t x h1)). Qed.
Lemma lem3235617 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term60 A s t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3235600 A s t x h1 h2) (fun h3 : False => @lem3235068 A t x h1)). Qed.
Lemma lem3235618 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term60 A s t x) : False.
Proof. exact (EQ_MP (@lem3235617 A s t x h1 h2) (@lem3235068 A t x h1)). Qed.
Lemma lem3235619 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term60 A s t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3235602 A s t x h1 h2) (fun h3 : False => @lem3235043 A t x h1)). Qed.
Lemma lem3235620 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term60 A s t x) : False.
Proof. exact (EQ_MP (@lem3235619 A s t x h1 h2) (@lem3235043 A t x h1)). Qed.
Lemma lem3235621 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : s x) (h2 : term60 A s t x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3235604 A s t x h1 h2) (fun h3 : False => @lem3235018 A s x h1)). Qed.
Lemma lem3235622 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : s x) (h2 : term60 A s t x) : False.
Proof. exact (EQ_MP (@lem3235621 A s t x h1 h2) (@lem3235018 A s x h1)). Qed.
Lemma lem3235623 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : term131 A s t x) (h3 : term25 A s t x) : False.
Proof. exact (or_elim (@lem3234984 A s t x h3) (fun h0 : s x => @lem3235616 A s t x h1 h0 h2) (fun h0 : t x => @lem3235612 A t x h1 h0)). Qed.
Lemma lem3235624 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term61 A t x) (h2 : term131 A s t x) : False.
Proof. exact (or_elim (@lem3234975 A s t x h2) (fun h0 : term25 A s t x => @lem3235623 A s t x h1 h2 h0) (fun h0 : t x => @lem3235608 A t x h1 h0)). Qed.
Lemma lem3235625 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term60 A s t x) (h2 : term25 A s t x) : False.
Proof. exact (or_elim (@lem3234980 A s t x h2) (fun h0 : s x => @lem3235622 A s t x h0 h1) (fun h0 : t x => @lem3235620 A s t x h0 h1)). Qed.
Lemma lem3235626 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term131 A s t x) (h2 : term60 A s t x) : False.
Proof. exact (or_elim (@lem3234975 A s t x h1) (fun h0 : term25 A s t x => @lem3235625 A s t x h2 h0) (fun h0 : t x => @lem3235618 A s t x h0 h2)). Qed.
Lemma lem3235627 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term131 A s t x) : False.
Proof. exact (or_elim (@lem3234974 A s t x h1) (fun h0 : term60 A s t x => @lem3235626 A s t x h1 h0) (fun h0 : term61 A t x => @lem3235624 A s t x h0 h1)). Qed.
Lemma lem3235628 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term170 A x s t) : False.
Proof. exact (or_elim (@lem3234969 A x s t h1) (fun h0 : term131 A s t x => @lem3235627 A s t x h0) (fun h0 : term149 A x s t => @lem3235568 A x s t h0)). Qed.
Lemma lem3235629 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term170 A x s t) : (term170 A x s t) = False.
Proof. exact (prop_ext (fun h2 : term170 A x s t => @lem3235628 A x s t h1) (fun h2 : False => @lem3234969 A x s t h1)). Qed.
Lemma lem3235630 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term170 A x s t) : False.
Proof. exact (EQ_MP (@lem3235629 A x s t h1) (@lem3234969 A x s t h1)). Qed.
Lemma lem3235631 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term44 A s t) : False.
Proof. exact (ex_elim (@lem3234849 A s t h1) (fun x : A => fun h0 : term172 A s t x => @lem3235630 A x s t h0)). Qed.
Lemma lem3235632 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term44 A s t) : (term44 A s t) = False.
Proof. exact (prop_ext (fun h2 : term44 A s t => @lem3235631 A s t h1) (fun h2 : False => @lem3234465 A s t h1)). Qed.
Lemma lem3235633 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term44 A s t) : False.
Proof. exact (EQ_MP (@lem3235632 A s t h1) (@lem3234465 A s t h1)). Qed.
Lemma lem3235634 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term43 A s t.
Proof. exact (fun h0 : term44 A s t => @lem3235633 A s t h0). Qed.
Lemma lem3235635 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term19 A s t) = (term30 A s t).
Proof. exact (EQ_MP (@lem3234464 A s t) (@lem3235634 A s t)). Qed.
Lemma lem3235640 {A : Type'} (s : A -> Prop) : term32 A s.
Proof. exact (fun t : A -> Prop => @lem3235635 A s t). Qed.
Lemma lem3235645 {A : Type'} : term34 A.
Proof. exact (fun s : A -> Prop => @lem3235640 A s). Qed.
Lemma lem3235646 {A : Type'} : term36 A.
Proof. exact (EQ_MP (@lem3234460 A) (@lem3235645 A)). Qed.
Lemma lem3235648 {A : Type'} : term36 A.
Proof. exact (@lem3234368 A (@lem3235646 A)). Qed.
Lemma lem3235649 {A : Type'} (h1 : term37 A) : False.
Proof. exact (@lem3235648 A (@lem3234352 A h1)). Qed.
Lemma lem3235650 {A : Type'} (h1 : term37 A) : (term37 A) = False.
Proof. exact (prop_ext (fun h2 : term37 A => @lem3235649 A h1) (fun h2 : False => @lem3234352 A h1)). Qed.
Lemma lem3235651 {A : Type'} (h1 : term37 A) : False.
Proof. exact (EQ_MP (@lem3235650 A h1) (@lem3234352 A h1)). Qed.
Lemma lem3235652 {A : Type'} : term36 A.
Proof. exact (fun h0 : term37 A => @lem3235651 A h0). Qed.
Lemma lem3235653 {A : Type'} : term34 A.
Proof. exact (EQ_MP (@lem3234351 A) (@lem3235652 A)). Qed.
Lemma lem3235654 {A : Type'} : term12 A.
Proof. exact (EQ_MP (@lem3234347 A) (@lem3235653 A)). Qed.
Lemma lem3235655 {A : Type'} : term11 A.
Proof. exact (EQ_MP (@lem3234250 A) (@lem3235654 A)). Qed.
