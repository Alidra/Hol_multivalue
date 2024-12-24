Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HAS_SUP_UBOUND_term_abbrevs.
Require Import DISJ_ASSOC_spec.
Require Import has_sup_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1339240_spec.
Require Import thm16474_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
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
Lemma lem5292279 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5292280 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem5292281 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem5292280 t1) (@lem5292279 t1)). Qed.
Lemma lem5292282 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem5292281 t1 t2). Qed.
Lemma lem5292283 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem5292284 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem5292283 t1 t2) (@lem5292282 t1 t2)). Qed.
Lemma lem5292285 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem5292284 t1 t2 t3). Qed.
Lemma lem5292286 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem5292287 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem5292286 t1 t2 t3) (@lem5292285 t1 t2 t3)). Qed.
Lemma lem5292288 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem5292287 t1 t2 t3)). Qed.
Lemma lem5292289 (s : real -> Prop) : term7 s.
Proof. exact (@lem5291214 s). Qed.
Lemma lem5292290 (s : real -> Prop) : (term7 s) = (term8 s).
Proof. exact (eq_refl (term7 s)). Qed.
Lemma lem5292291 (s : real -> Prop) : term8 s.
Proof. exact (EQ_MP (@lem5292290 s) (@lem5292289 s)). Qed.
Lemma lem5292292 (s : real -> Prop) (b : real) : term9 s b.
Proof. exact (@lem5292291 s b). Qed.
Lemma lem5292293 (s : real -> Prop) (b : real) : (term9 s b) = ((has_sup s b) = (term10 s b)).
Proof. exact (eq_refl (term9 s b)). Qed.
Lemma lem5292300 (s : real -> Prop) (b : real) : (has_sup s b) = (term10 s b).
Proof. exact (EQ_MP (@lem5292293 s b) (@lem5292292 s b)). Qed.
Lemma lem5292313 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5292314 (s : real -> Prop) (b : real) : (term11 s b) = (term12 s b).
Proof. exact (MK_COMB (@lem5292313) (@lem5292300 s b)). Qed.
Lemma lem5292315 (x : real) (s : real -> Prop) : (@IN real x s) = (@IN real x s).
Proof. exact (eq_refl (@IN real x s)). Qed.
Lemma lem5292316 (b : real) (x : real) (s : real -> Prop) : (term13 b x s) = (term14 b x s).
Proof. exact (MK_COMB (@lem5292314 s b) (@lem5292315 x s)). Qed.
Lemma lem5292319 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5292320 (b : real) (x : real) (s : real -> Prop) : (term15 b x s) = (term16 b x s).
Proof. exact (MK_COMB (@lem5292319) (@lem5292316 b x s)). Qed.
Lemma lem5292321 (x : real) (b : real) : (real_le x b) = (real_le x b).
Proof. exact (eq_refl (real_le x b)). Qed.
Lemma lem5292322 (s : real -> Prop) (x : real) (b : real) : (term17 s x b) = (term18 s x b).
Proof. exact (MK_COMB (@lem5292320 b x s) (@lem5292321 x b)). Qed.
Lemma lem5292325 (s : real -> Prop) (x : real) (b : real) : (term18 s x b) = (term17 s x b).
Proof. exact (SYM (@lem5292322 s x b)). Qed.
Lemma lem5292327 (p : Prop) : p = (term19 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5292328 (s : real -> Prop) (x : real) (b : real) : (term18 s x b) = (term20 s x b).
Proof. exact (@lem5292327 (term18 s x b)). Qed.
Lemma lem5292329 (s : real -> Prop) (x : real) (b : real) : (term20 s x b) = (term18 s x b).
Proof. exact (SYM (@lem5292328 s x b)). Qed.
Lemma lem5292330 (s : real -> Prop) (x : real) (b : real) (h1 : term21 s x b) : term21 s x b.
Proof. exact (h1). Qed.
Lemma lem5292333 (s : real -> Prop) (x : real) (b : real) (h1 : term22 s x b) : term22 s x b.
Proof. exact (h1). Qed.
Lemma lem5292334 (s : real -> Prop) (x : real) (b : real) : term23 s x b.
Proof. exact (fun h0 : term22 s x b => @lem5292333 s x b h0). Qed.
Lemma lem5292335 (s : real -> Prop) (x : real) (b : real) (h1 : term23 s x b) : term23 s x b.
Proof. exact (h1). Qed.
Lemma lem5292336 (s : real -> Prop) (x : real) (b : real) (h1 : term22 s x b) : term22 s x b.
Proof. exact (h1). Qed.
Lemma lem5292337 (s : real -> Prop) (x : real) (b : real) (h1 : term22 s x b) (h2 : term23 s x b) : term22 s x b.
Proof. exact (@lem5292335 s x b h2 (@lem5292336 s x b h1)). Qed.
Lemma lem5292338 (s : real -> Prop) (x : real) (b : real) (h1 : term22 s x b) : term24 s x b.
Proof. exact (fun h0 : term23 s x b => @lem5292337 s x b h1 h0). Qed.
Lemma lem5292339 (s : real -> Prop) (x : real) (b : real) (h1 : term23 s x b) : term23 s x b.
Proof. exact (h1). Qed.
Lemma lem5292340 (s : real -> Prop) (x : real) (b : real) (h1 : term22 s x b) (h2 : term23 s x b) : term22 s x b.
Proof. exact (@lem5292338 s x b h1 (@lem5292339 s x b h2)). Qed.
Lemma lem5292341 (s : real -> Prop) (x : real) (b : real) (h1 : term23 s x b) : term23 s x b.
Proof. exact (fun h0 : term22 s x b => @lem5292340 s x b h0 h1). Qed.
Lemma lem5292342 (s : real -> Prop) (x : real) (b : real) : term25 s x b.
Proof. exact (fun h0 : term23 s x b => @lem5292341 s x b h0). Qed.
Lemma lem5292345 (s : real -> Prop) (x : real) (b : real) : term23 s x b.
Proof. exact (@lem5292342 s x b (@lem5292334 s x b)). Qed.
Lemma lem5292375 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5292376 : term26 = term27.
Proof. exact (@lem5292375 term28). Qed.
Lemma lem5292381 (s : real -> Prop) (x : real) (b : real) : (term29 s x b) = (term29 s x b).
Proof. exact (eq_refl (term29 s x b)). Qed.
Lemma lem5292382 (s : real -> Prop) (x : real) (b : real) : (term22 s x b) = (term30 s x b).
Proof. exact (MK_COMB (@lem5292381 s x b) (@lem5292376)). Qed.
Lemma lem5292385 (x : real) (b : real) : (term31 x b) = (term32 x b).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5292382 s x b)). Qed.
Lemma lem5292386 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5292387 (x : real) (b : real) : (term33 x b) = (term34 x b).
Proof. exact (MK_COMB (@lem5292386) (@lem5292385 x b)). Qed.
Lemma lem5292392 (b : real) : (term35 b) = (term36 b).
Proof. exact (fun_ext (fun x : real => @lem5292387 x b)). Qed.
Lemma lem5292393 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5292394 (b : real) : (term37 b) = (term38 b).
Proof. exact (MK_COMB (@lem5292393) (@lem5292392 b)). Qed.
Lemma lem5292399 : term39 = term40.
Proof. exact (fun_ext (fun b : real => @lem5292394 b)). Qed.
Lemma lem5292400 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5292409 : term41 = term42.
Proof. exact (MK_COMB (@lem5292400) (@lem5292399)). Qed.
Lemma lem5292410 (x : real) : (real_le x x) = (real_le x x).
Proof. exact (eq_refl (real_le x x)). Qed.
Lemma lem5292411 : term43 = term43.
Proof. exact (fun_ext (fun x : real => @lem5292410 x)). Qed.
Lemma lem5292412 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5292413 : term28 = term28.
Proof. exact (MK_COMB (@lem5292412) (@lem5292411)). Qed.
Lemma lem5292414 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5292415 : term27 = term27.
Proof. exact (MK_COMB (@lem5292414) (@lem5292413)). Qed.
Lemma lem5292416 (x : real) (b : real) : (real_le x b) = (real_le x b).
Proof. exact (eq_refl (real_le x b)). Qed.
Lemma lem5292417 (x : real) (s : real -> Prop) : (@IN real x s) = (@IN real x s).
Proof. exact (eq_refl (@IN real x s)). Qed.
Lemma lem5292418 (b : real) (c : real) : (real_le b c) = (real_le b c).
Proof. exact (eq_refl (real_le b c)). Qed.
Lemma lem5292423 (s : real -> Prop) (x : real) (c : real) : (term44 s x c) = (term44 s x c).
Proof. exact (eq_refl (term44 s x c)). Qed.
Lemma lem5292424 (s : real -> Prop) (c : real) : (term45 s c) = (term45 s c).
Proof. exact (fun_ext (fun x : real => @lem5292423 s x c)). Qed.
Lemma lem5292425 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5292426 (s : real -> Prop) (c : real) : (term46 s c) = (term46 s c).
Proof. exact (MK_COMB (@lem5292425) (@lem5292424 s c)). Qed.
Lemma lem5292427 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5292428 (s : real -> Prop) (c : real) : (term47 s c) = (term47 s c).
Proof. exact (MK_COMB (@lem5292427) (@lem5292426 s c)). Qed.
Lemma lem5292429 (s : real -> Prop) (b : real) (c : real) : ((term46 s c) = (real_le b c)) = ((term46 s c) = (real_le b c)).
Proof. exact (MK_COMB (@lem5292428 s c) (@lem5292418 b c)). Qed.
Lemma lem5292430 (s : real -> Prop) (b : real) : (term48 s b) = (term48 s b).
Proof. exact (fun_ext (fun c : real => @lem5292429 s b c)). Qed.
Lemma lem5292431 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5292432 (s : real -> Prop) (b : real) : (term10 s b) = (term10 s b).
Proof. exact (MK_COMB (@lem5292431) (@lem5292430 s b)). Qed.
Lemma lem5292433 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5292434 (s : real -> Prop) (b : real) : (term12 s b) = (term12 s b).
Proof. exact (MK_COMB (@lem5292433) (@lem5292432 s b)). Qed.
Lemma lem5292435 (b : real) (x : real) (s : real -> Prop) : (term14 b x s) = (term14 b x s).
Proof. exact (MK_COMB (@lem5292434 s b) (@lem5292417 x s)). Qed.
Lemma lem5292436 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5292437 (b : real) (x : real) (s : real -> Prop) : (term16 b x s) = (term16 b x s).
Proof. exact (MK_COMB (@lem5292436) (@lem5292435 b x s)). Qed.
Lemma lem5292438 (s : real -> Prop) (x : real) (b : real) : (term18 s x b) = (term18 s x b).
Proof. exact (MK_COMB (@lem5292437 b x s) (@lem5292416 x b)). Qed.
Lemma lem5292439 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5292440 (s : real -> Prop) (x : real) (b : real) : (term21 s x b) = (term21 s x b).
Proof. exact (MK_COMB (@lem5292439) (@lem5292438 s x b)). Qed.
Lemma lem5292441 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5292442 (s : real -> Prop) (x : real) (b : real) : (term29 s x b) = (term29 s x b).
Proof. exact (MK_COMB (@lem5292441) (@lem5292440 s x b)). Qed.
Lemma lem5292443 (s : real -> Prop) (x : real) (b : real) : (term30 s x b) = (term30 s x b).
Proof. exact (MK_COMB (@lem5292442 s x b) (@lem5292415)). Qed.
Lemma lem5292444 (x : real) (b : real) : (term32 x b) = (term32 x b).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5292443 s x b)). Qed.
Lemma lem5292445 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5292446 (x : real) (b : real) : (term34 x b) = (term34 x b).
Proof. exact (MK_COMB (@lem5292445) (@lem5292444 x b)). Qed.
Lemma lem5292447 (b : real) : (term36 b) = (term36 b).
Proof. exact (fun_ext (fun x : real => @lem5292446 x b)). Qed.
Lemma lem5292448 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5292449 (b : real) : (term38 b) = (term38 b).
Proof. exact (MK_COMB (@lem5292448) (@lem5292447 b)). Qed.
Lemma lem5292450 : term40 = term40.
Proof. exact (fun_ext (fun b : real => @lem5292449 b)). Qed.
Lemma lem5292451 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5292452 : term42 = term42.
Proof. exact (MK_COMB (@lem5292451) (@lem5292450)). Qed.
Lemma lem5292499 : term41 = term42.
Proof. exact (TRANS (@lem5292409) (@lem5292452)). Qed.
Lemma lem5292500 : term42 = term41.
Proof. exact (SYM (@lem5292499)). Qed.
Lemma lem5292501 (s : real -> Prop) (x : real) (b : real) (h1 : term21 s x b) : term21 s x b.
Proof. exact (h1). Qed.
Lemma lem5292502 (h1 : term28) : term28.
Proof. exact (h1). Qed.
Lemma lem5292511 (s : real -> Prop) (x : real) (c : real) : (term49 s x c) = (term50 s x c).
Proof. exact (@lem17362 (@IN real x s) (real_le x c)). Qed.
Lemma lem5292516 (s : real -> Prop) (x : real) (c : real) : (term44 s x c) = (term51 s x c).
Proof. exact (@lem17265 (@IN real x s) (real_le x c)). Qed.
Lemma lem5292517 (P : real -> Prop) : (term52 P) = (term53 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5292518 (s : real -> Prop) (c : real) : (term54 s c) = (term55 s c).
Proof. exact (@lem5292517 (term45 s c)). Qed.
Lemma lem5292519 (s : real -> Prop) (x : real) (c : real) : (term56 s c x) = (term44 s x c).
Proof. exact (eq_refl (term56 s c x)). Qed.
Lemma lem5292520 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5292521 (s : real -> Prop) (x : real) (c : real) : (term57 s c x) = (term49 s x c).
Proof. exact (MK_COMB (@lem5292520) (@lem5292519 s x c)). Qed.
Lemma lem5292522 (s : real -> Prop) (x : real) (c : real) : (term57 s c x) = (term50 s x c).
Proof. exact (TRANS (@lem5292521 s x c) (@lem5292511 s x c)). Qed.
Lemma lem5292523 (s : real -> Prop) (c : real) : (term58 s c) = (term59 s c).
Proof. exact (fun_ext (fun x : real => @lem5292522 s x c)). Qed.
Lemma lem5292524 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5292525 (s : real -> Prop) (c : real) : (term55 s c) = (term60 s c).
Proof. exact (MK_COMB (@lem5292524) (@lem5292523 s c)). Qed.
Lemma lem5292526 (s : real -> Prop) (c : real) : (term54 s c) = (term60 s c).
Proof. exact (TRANS (@lem5292518 s c) (@lem5292525 s c)). Qed.
Lemma lem5292527 (s : real -> Prop) (c : real) : (term45 s c) = (term61 s c).
Proof. exact (fun_ext (fun x : real => @lem5292516 s x c)). Qed.
Lemma lem5292528 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5292529 (s : real -> Prop) (c : real) : (term46 s c) = (term62 s c).
Proof. exact (MK_COMB (@lem5292528) (@lem5292527 s c)). Qed.
Lemma lem5292530 (b : real) (c : real) : (term63 b c) = (term63 b c).
Proof. exact (eq_refl (term63 b c)). Qed.
Lemma lem5292531 (b : real) (c : real) : (real_le b c) = (real_le b c).
Proof. exact (eq_refl (real_le b c)). Qed.
Lemma lem5292532 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5292533 (s : real -> Prop) (c : real) : (term64 s c) = (term65 s c).
Proof. exact (MK_COMB (@lem5292532) (@lem5292526 s c)). Qed.
Lemma lem5292534 (s : real -> Prop) (b : real) (c : real) : (term66 s b c) = (term67 s b c).
Proof. exact (MK_COMB (@lem5292533 s c) (@lem5292531 b c)). Qed.
Lemma lem5292535 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5292536 (s : real -> Prop) (c : real) : (term68 s c) = (term69 s c).
Proof. exact (MK_COMB (@lem5292535) (@lem5292529 s c)). Qed.
Lemma lem5292537 (s : real -> Prop) (b : real) (c : real) : (term70 s b c) = (term71 s b c).
Proof. exact (MK_COMB (@lem5292536 s c) (@lem5292530 b c)). Qed.
Lemma lem5292538 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5292539 (s : real -> Prop) (b : real) (c : real) : (term72 s b c) = (term73 s b c).
Proof. exact (MK_COMB (@lem5292538) (@lem5292537 s b c)). Qed.
Lemma lem5292540 (s : real -> Prop) (b : real) (c : real) : (term74 s b c) = (term75 s b c).
Proof. exact (MK_COMB (@lem5292539 s b c) (@lem5292534 s b c)). Qed.
Lemma lem5292541 (s : real -> Prop) (b : real) (c : real) : ((term46 s c) = (real_le b c)) = (term74 s b c).
Proof. exact (@lem17784 (term46 s c) (real_le b c)). Qed.
Lemma lem5292542 (s : real -> Prop) (b : real) (c : real) : ((term46 s c) = (real_le b c)) = (term75 s b c).
Proof. exact (TRANS (@lem5292541 s b c) (@lem5292540 s b c)). Qed.
Lemma lem5292543 (s : real -> Prop) (b : real) : (term48 s b) = (term76 s b).
Proof. exact (fun_ext (fun c : real => @lem5292542 s b c)). Qed.
Lemma lem5292544 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5292545 (s : real -> Prop) (b : real) : (term10 s b) = (term77 s b).
Proof. exact (MK_COMB (@lem5292544) (@lem5292543 s b)). Qed.
Lemma lem5292546 (x : real) (s : real -> Prop) : (@IN real x s) = (@IN real x s).
Proof. exact (eq_refl (@IN real x s)). Qed.
Lemma lem5292547 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5292548 (s : real -> Prop) (b : real) : (term12 s b) = (term78 s b).
Proof. exact (MK_COMB (@lem5292547) (@lem5292545 s b)). Qed.
Lemma lem5292549 (b : real) (x : real) (s : real -> Prop) : (term14 b x s) = (term79 b x s).
Proof. exact (MK_COMB (@lem5292548 s b) (@lem5292546 x s)). Qed.
Lemma lem5292550 (x : real) (b : real) : (term63 x b) = (term63 x b).
Proof. exact (eq_refl (term63 x b)). Qed.
Lemma lem5292551 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5292552 (b : real) (x : real) (s : real -> Prop) : (term80 b x s) = (term81 b x s).
Proof. exact (MK_COMB (@lem5292551) (@lem5292549 b x s)). Qed.
Lemma lem5292553 (s : real -> Prop) (x : real) (b : real) : (term82 s x b) = (term83 s x b).
Proof. exact (MK_COMB (@lem5292552 b x s) (@lem5292550 x b)). Qed.
Lemma lem5292554 (s : real -> Prop) (x : real) (b : real) : (term21 s x b) = (term82 s x b).
Proof. exact (@lem17362 (term14 b x s) (real_le x b)). Qed.
Lemma lem5292555 (s : real -> Prop) (x : real) (b : real) : (term21 s x b) = (term83 s x b).
Proof. exact (TRANS (@lem5292554 s x b) (@lem5292553 s x b)). Qed.
Lemma lem5292557 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term84 A P Q) = (term85 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5292558 (P : real -> Prop) (Q : real -> Prop) : (term86 P Q) = (term87 P Q).
Proof. exact (@lem5292557 real P Q). Qed.
Lemma lem5292559 (s : real -> Prop) (b : real) : (term88 s b) = (term89 s b).
Proof. exact (@lem5292558 (term90 s b) (term91 s b)). Qed.
Lemma lem5292560 (s : real -> Prop) (b : real) (c : real) : (term92 s b c) = (term71 s b c).
Proof. exact (eq_refl (term92 s b c)). Qed.
Lemma lem5292561 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5292562 (s : real -> Prop) (b : real) (c : real) : (term93 s b c) = (term73 s b c).
Proof. exact (MK_COMB (@lem5292561) (@lem5292560 s b c)). Qed.
Lemma lem5292563 (s : real -> Prop) (b : real) (c : real) : (term94 s b c) = (term67 s b c).
Proof. exact (eq_refl (term94 s b c)). Qed.
Lemma lem5292564 (s : real -> Prop) (b : real) (c : real) : (term95 s b c) = (term75 s b c).
Proof. exact (MK_COMB (@lem5292562 s b c) (@lem5292563 s b c)). Qed.
Lemma lem5292565 (s : real -> Prop) (b : real) : (term96 s b) = (term76 s b).
Proof. exact (fun_ext (fun c : real => @lem5292564 s b c)). Qed.
Lemma lem5292566 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5292567 (s : real -> Prop) (b : real) : (term88 s b) = (term77 s b).
Proof. exact (MK_COMB (@lem5292566) (@lem5292565 s b)). Qed.
Lemma lem5292568 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5292569 (s : real -> Prop) (b : real) : (term97 s b) = (term98 s b).
Proof. exact (MK_COMB (@lem5292568) (@lem5292567 s b)). Qed.
Lemma lem5292570 (s : real -> Prop) (b : real) (c : real) : (term92 s b c) = (term71 s b c).
Proof. exact (eq_refl (term92 s b c)). Qed.
Lemma lem5292571 (s : real -> Prop) (b : real) : (term99 s b) = (term90 s b).
Proof. exact (fun_ext (fun c : real => @lem5292570 s b c)). Qed.
Lemma lem5292572 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5292573 (s : real -> Prop) (b : real) : (term100 s b) = (term101 s b).
Proof. exact (MK_COMB (@lem5292572) (@lem5292571 s b)). Qed.
Lemma lem5292574 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5292575 (s : real -> Prop) (b : real) : (term102 s b) = (term103 s b).
Proof. exact (MK_COMB (@lem5292574) (@lem5292573 s b)). Qed.
Lemma lem5292576 (s : real -> Prop) (b : real) (c : real) : (term94 s b c) = (term67 s b c).
Proof. exact (eq_refl (term94 s b c)). Qed.
Lemma lem5292577 (s : real -> Prop) (b : real) : (term104 s b) = (term91 s b).
Proof. exact (fun_ext (fun c : real => @lem5292576 s b c)). Qed.
Lemma lem5292578 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5292579 (s : real -> Prop) (b : real) : (term105 s b) = (term106 s b).
Proof. exact (MK_COMB (@lem5292578) (@lem5292577 s b)). Qed.
Lemma lem5292580 (s : real -> Prop) (b : real) : (term89 s b) = (term107 s b).
Proof. exact (MK_COMB (@lem5292575 s b) (@lem5292579 s b)). Qed.
Lemma lem5292581 (s : real -> Prop) (b : real) : ((term88 s b) = (term89 s b)) = ((term77 s b) = (term107 s b)).
Proof. exact (MK_COMB (@lem5292569 s b) (@lem5292580 s b)). Qed.
Lemma lem5292582 (s : real -> Prop) (b : real) : (term77 s b) = (term107 s b).
Proof. exact (EQ_MP (@lem5292581 s b) (@lem5292559 s b)). Qed.
Lemma lem5292775 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5292776 (s : real -> Prop) (b : real) : (term78 s b) = (term108 s b).
Proof. exact (MK_COMB (@lem5292775) (@lem5292582 s b)). Qed.
Lemma lem5292777 (x : real) (s : real -> Prop) : (@IN real x s) = (@IN real x s).
Proof. exact (eq_refl (@IN real x s)). Qed.
Lemma lem5292778 (b : real) (x : real) (s : real -> Prop) : (term79 b x s) = (term109 b x s).
Proof. exact (MK_COMB (@lem5292776 s b) (@lem5292777 x s)). Qed.
Lemma lem5292779 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5292780 (b : real) (x : real) (s : real -> Prop) : (term81 b x s) = (term110 b x s).
Proof. exact (MK_COMB (@lem5292779) (@lem5292778 b x s)). Qed.
Lemma lem5292781 (x : real) (b : real) : (term63 x b) = (term63 x b).
Proof. exact (eq_refl (term63 x b)). Qed.
Lemma lem5292782 (s : real -> Prop) (x : real) (b : real) : (term83 s x b) = (term111 s x b).
Proof. exact (MK_COMB (@lem5292780 b x s) (@lem5292781 x b)). Qed.
Lemma lem5292784 {A : Type'} (P : A -> Prop) (Q : Prop) : (term112 A P Q) = (term113 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5292785 (P : real -> Prop) (Q : Prop) : (term114 P Q) = (term115 P Q).
Proof. exact (@lem5292784 real P Q). Qed.
Lemma lem5292786 (s : real -> Prop) (b : real) (c : real) : (term116 s b c) = (term117 s b c).
Proof. exact (@lem5292785 (term59 s c) (real_le b c)). Qed.
Lemma lem5292787 (s : real -> Prop) (x : real) (c : real) : (term118 s c x) = (term50 s x c).
Proof. exact (eq_refl (term118 s c x)). Qed.
Lemma lem5292788 (s : real -> Prop) (c : real) : (term119 s c) = (term59 s c).
Proof. exact (fun_ext (fun x : real => @lem5292787 s x c)). Qed.
Lemma lem5292789 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5292790 (s : real -> Prop) (c : real) : (term120 s c) = (term60 s c).
Proof. exact (MK_COMB (@lem5292789) (@lem5292788 s c)). Qed.
Lemma lem5292791 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5292792 (s : real -> Prop) (c : real) : (term121 s c) = (term65 s c).
Proof. exact (MK_COMB (@lem5292791) (@lem5292790 s c)). Qed.
Lemma lem5292793 (b : real) (c : real) : (real_le b c) = (real_le b c).
Proof. exact (eq_refl (real_le b c)). Qed.
Lemma lem5292794 (s : real -> Prop) (b : real) (c : real) : (term116 s b c) = (term67 s b c).
Proof. exact (MK_COMB (@lem5292792 s c) (@lem5292793 b c)). Qed.
Lemma lem5292795 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5292796 (s : real -> Prop) (b : real) (c : real) : (term122 s b c) = (term123 s b c).
Proof. exact (MK_COMB (@lem5292795) (@lem5292794 s b c)). Qed.
Lemma lem5292797 (s : real -> Prop) (x : real) (c : real) : (term118 s c x) = (term50 s x c).
Proof. exact (eq_refl (term118 s c x)). Qed.
Lemma lem5292798 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5292799 (s : real -> Prop) (x : real) (c : real) : (term124 s c x) = (term125 s x c).
Proof. exact (MK_COMB (@lem5292798) (@lem5292797 s x c)). Qed.
Lemma lem5292800 (b : real) (c : real) : (real_le b c) = (real_le b c).
Proof. exact (eq_refl (real_le b c)). Qed.
Lemma lem5292801 (s : real -> Prop) (x : real) (b : real) (c : real) : (term126 s x b c) = (term127 s x b c).
Proof. exact (MK_COMB (@lem5292799 s x c) (@lem5292800 b c)). Qed.
Lemma lem5292802 (s : real -> Prop) (b : real) (c : real) : (term128 s b c) = (term129 s b c).
Proof. exact (fun_ext (fun x : real => @lem5292801 s x b c)). Qed.
Lemma lem5292803 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5292804 (s : real -> Prop) (b : real) (c : real) : (term117 s b c) = (term130 s b c).
Proof. exact (MK_COMB (@lem5292803) (@lem5292802 s b c)). Qed.
Lemma lem5292805 (s : real -> Prop) (b : real) (c : real) : ((term116 s b c) = (term117 s b c)) = ((term67 s b c) = (term130 s b c)).
Proof. exact (MK_COMB (@lem5292796 s b c) (@lem5292804 s b c)). Qed.
Lemma lem5292806 (s : real -> Prop) (b : real) (c : real) : (term67 s b c) = (term130 s b c).
Proof. exact (EQ_MP (@lem5292805 s b c) (@lem5292786 s b c)). Qed.
Lemma lem5292807 (s : real -> Prop) (b : real) : (term91 s b) = (term131 s b).
Proof. exact (fun_ext (fun c : real => @lem5292806 s b c)). Qed.
Lemma lem5292808 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5292809 (s : real -> Prop) (b : real) : (term106 s b) = (term132 s b).
Proof. exact (MK_COMB (@lem5292808) (@lem5292807 s b)). Qed.
Lemma lem5292811 {A B : Type'} (P : type1413 A B) : (term133 A B P) = (term134 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5292812 (P : type1626) : (term135 P) = (term136 P).
Proof. exact (@lem5292811 real real P). Qed.
Lemma lem5292813 (s : real -> Prop) (b : real) : (term137 s b) = (term138 s b).
Proof. exact (@lem5292812 (term139 s b)). Qed.
Lemma lem5292814 (s : real -> Prop) (b : real) (c : real) : (term140 s b c) = (term129 s b c).
Proof. exact (eq_refl (term140 s b c)). Qed.
Lemma lem5292815 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5292816 (s : real -> Prop) (b : real) (c : real) (x : real) : (term141 s b c x) = (term142 s b c x).
Proof. exact (MK_COMB (@lem5292814 s b c) (@lem5292815 x)). Qed.
Lemma lem5292817 (s : real -> Prop) (x : real) (b : real) (c : real) : (term142 s b c x) = (term127 s x b c).
Proof. exact (eq_refl (term142 s b c x)). Qed.
Lemma lem5292818 (s : real -> Prop) (x : real) (b : real) (c : real) : (term141 s b c x) = (term127 s x b c).
Proof. exact (TRANS (@lem5292816 s b c x) (@lem5292817 s x b c)). Qed.
Lemma lem5292819 (s : real -> Prop) (b : real) (c : real) : (term143 s b c) = (term129 s b c).
Proof. exact (fun_ext (fun x : real => @lem5292818 s x b c)). Qed.
Lemma lem5292820 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5292821 (s : real -> Prop) (b : real) (c : real) : (term144 s b c) = (term130 s b c).
Proof. exact (MK_COMB (@lem5292820) (@lem5292819 s b c)). Qed.
Lemma lem5292822 (s : real -> Prop) (b : real) : (term145 s b) = (term131 s b).
Proof. exact (fun_ext (fun c : real => @lem5292821 s b c)). Qed.
Lemma lem5292823 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5292824 (s : real -> Prop) (b : real) : (term137 s b) = (term132 s b).
Proof. exact (MK_COMB (@lem5292823) (@lem5292822 s b)). Qed.
Lemma lem5292825 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5292826 (s : real -> Prop) (b : real) : (term146 s b) = (term147 s b).
Proof. exact (MK_COMB (@lem5292825) (@lem5292824 s b)). Qed.
Lemma lem5292827 (s : real -> Prop) (b : real) (c : real) : (term140 s b c) = (term129 s b c).
Proof. exact (eq_refl (term140 s b c)). Qed.
Lemma lem5292828 (x : real -> real) (c : real) : (x c) = (x c).
Proof. exact (eq_refl (x c)). Qed.
Lemma lem5292829 (s : real -> Prop) (b : real) (x : real -> real) (c : real) : (term148 s b x c) = (term149 s b x c).
Proof. exact (MK_COMB (@lem5292827 s b c) (@lem5292828 x c)). Qed.
Lemma lem5292830 (s : real -> Prop) (x : real -> real) (b : real) (c : real) : (term149 s b x c) = (term150 s x b c).
Proof. exact (eq_refl (term149 s b x c)). Qed.
Lemma lem5292831 (s : real -> Prop) (x : real -> real) (b : real) (c : real) : (term148 s b x c) = (term150 s x b c).
Proof. exact (TRANS (@lem5292829 s b x c) (@lem5292830 s x b c)). Qed.
Lemma lem5292832 (s : real -> Prop) (x : real -> real) (b : real) : (term151 s b x) = (term152 s x b).
Proof. exact (fun_ext (fun c : real => @lem5292831 s x b c)). Qed.
Lemma lem5292833 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5292834 (s : real -> Prop) (x : real -> real) (b : real) : (term153 s b x) = (term154 s x b).
Proof. exact (MK_COMB (@lem5292833) (@lem5292832 s x b)). Qed.
Lemma lem5292835 (s : real -> Prop) (b : real) : (term155 s b) = (term156 s b).
Proof. exact (fun_ext (fun x : real -> real => @lem5292834 s x b)). Qed.
Lemma lem5292836 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5292837 (s : real -> Prop) (b : real) : (term138 s b) = (term157 s b).
Proof. exact (MK_COMB (@lem5292836) (@lem5292835 s b)). Qed.
Lemma lem5292838 (s : real -> Prop) (b : real) : ((term137 s b) = (term138 s b)) = ((term132 s b) = (term157 s b)).
Proof. exact (MK_COMB (@lem5292826 s b) (@lem5292837 s b)). Qed.
Lemma lem5292839 (s : real -> Prop) (b : real) : (term132 s b) = (term157 s b).
Proof. exact (EQ_MP (@lem5292838 s b) (@lem5292813 s b)). Qed.
Lemma lem5292840 (s : real -> Prop) (b : real) : (term106 s b) = (term157 s b).
Proof. exact (TRANS (@lem5292809 s b) (@lem5292839 s b)). Qed.
Lemma lem5292841 (s : real -> Prop) (b : real) : (term103 s b) = (term103 s b).
Proof. exact (eq_refl (term103 s b)). Qed.
Lemma lem5292842 (s : real -> Prop) (b : real) : (term107 s b) = (term158 s b).
Proof. exact (MK_COMB (@lem5292841 s b) (@lem5292840 s b)). Qed.
Lemma lem5292844 {A : Type'} (P : Prop) (Q : A -> Prop) : (term159 A P Q) = (term160 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5292845 (P : Prop) (Q : type1028) : (term161 P Q) = (term162 P Q).
Proof. exact (@lem5292844 (real -> real) P Q). Qed.
Lemma lem5292846 (s : real -> Prop) (b : real) : (term163 s b) = (term164 s b).
Proof. exact (@lem5292845 (term101 s b) (term156 s b)). Qed.
Lemma lem5292847 (s : real -> Prop) (x : real -> real) (b : real) : (term165 s b x) = (term154 s x b).
Proof. exact (eq_refl (term165 s b x)). Qed.
Lemma lem5292848 (s : real -> Prop) (b : real) : (term166 s b) = (term156 s b).
Proof. exact (fun_ext (fun x : real -> real => @lem5292847 s x b)). Qed.
Lemma lem5292849 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5292850 (s : real -> Prop) (b : real) : (term167 s b) = (term157 s b).
Proof. exact (MK_COMB (@lem5292849) (@lem5292848 s b)). Qed.
Lemma lem5292851 (s : real -> Prop) (b : real) : (term103 s b) = (term103 s b).
Proof. exact (eq_refl (term103 s b)). Qed.
Lemma lem5292852 (s : real -> Prop) (b : real) : (term163 s b) = (term158 s b).
Proof. exact (MK_COMB (@lem5292851 s b) (@lem5292850 s b)). Qed.
Lemma lem5292853 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5292854 (s : real -> Prop) (b : real) : (term168 s b) = (term169 s b).
Proof. exact (MK_COMB (@lem5292853) (@lem5292852 s b)). Qed.
Lemma lem5292855 (s : real -> Prop) (x : real -> real) (b : real) : (term165 s b x) = (term154 s x b).
Proof. exact (eq_refl (term165 s b x)). Qed.
Lemma lem5292856 (s : real -> Prop) (b : real) : (term103 s b) = (term103 s b).
Proof. exact (eq_refl (term103 s b)). Qed.
Lemma lem5292857 (s : real -> Prop) (x : real -> real) (b : real) : (term170 s b x) = (term171 s x b).
Proof. exact (MK_COMB (@lem5292856 s b) (@lem5292855 s x b)). Qed.
Lemma lem5292858 (s : real -> Prop) (b : real) : (term172 s b) = (term173 s b).
Proof. exact (fun_ext (fun x : real -> real => @lem5292857 s x b)). Qed.
Lemma lem5292859 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5292860 (s : real -> Prop) (b : real) : (term164 s b) = (term174 s b).
Proof. exact (MK_COMB (@lem5292859) (@lem5292858 s b)). Qed.
Lemma lem5292861 (s : real -> Prop) (b : real) : ((term163 s b) = (term164 s b)) = ((term158 s b) = (term174 s b)).
Proof. exact (MK_COMB (@lem5292854 s b) (@lem5292860 s b)). Qed.
Lemma lem5292862 (s : real -> Prop) (b : real) : (term158 s b) = (term174 s b).
Proof. exact (EQ_MP (@lem5292861 s b) (@lem5292846 s b)). Qed.
Lemma lem5292863 (s : real -> Prop) (b : real) : (term107 s b) = (term174 s b).
Proof. exact (TRANS (@lem5292842 s b) (@lem5292862 s b)). Qed.
Lemma lem5292864 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5292865 (s : real -> Prop) (b : real) : (term108 s b) = (term175 s b).
Proof. exact (MK_COMB (@lem5292864) (@lem5292863 s b)). Qed.
Lemma lem5292866 (x : real) (s : real -> Prop) : (@IN real x s) = (@IN real x s).
Proof. exact (eq_refl (@IN real x s)). Qed.
Lemma lem5292867 (b : real) (x : real) (s : real -> Prop) : (term109 b x s) = (term176 b x s).
Proof. exact (MK_COMB (@lem5292865 s b) (@lem5292866 x s)). Qed.
Lemma lem5292869 {A : Type'} (P : A -> Prop) (Q : Prop) : (term177 A P Q) = (term178 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5292870 (P : type1028) (Q : Prop) : (term179 P Q) = (term180 P Q).
Proof. exact (@lem5292869 (real -> real) P Q). Qed.
Lemma lem5292871 (b : real) (x : real) (s : real -> Prop) : (term181 b x s) = (term182 b x s).
Proof. exact (@lem5292870 (term173 s b) (@IN real x s)). Qed.
Lemma lem5292872 (s : real -> Prop) (x : real -> real) (b : real) : (term183 s b x) = (term171 s x b).
Proof. exact (eq_refl (term183 s b x)). Qed.
Lemma lem5292873 (s : real -> Prop) (b : real) : (term184 s b) = (term173 s b).
Proof. exact (fun_ext (fun x : real -> real => @lem5292872 s x b)). Qed.
Lemma lem5292874 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5292875 (s : real -> Prop) (b : real) : (term185 s b) = (term174 s b).
Proof. exact (MK_COMB (@lem5292874) (@lem5292873 s b)). Qed.
Lemma lem5292876 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5292877 (s : real -> Prop) (b : real) : (term186 s b) = (term175 s b).
Proof. exact (MK_COMB (@lem5292876) (@lem5292875 s b)). Qed.
Lemma lem5292878 (x : real) (s : real -> Prop) : (@IN real x s) = (@IN real x s).
Proof. exact (eq_refl (@IN real x s)). Qed.
Lemma lem5292879 (b : real) (x : real) (s : real -> Prop) : (term181 b x s) = (term176 b x s).
Proof. exact (MK_COMB (@lem5292877 s b) (@lem5292878 x s)). Qed.
Lemma lem5292880 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5292881 (b : real) (x : real) (s : real -> Prop) : (term187 b x s) = (term188 b x s).
Proof. exact (MK_COMB (@lem5292880) (@lem5292879 b x s)). Qed.
Lemma lem5292882 (s : real -> Prop) (x : real -> real) (b : real) : (term183 s b x) = (term171 s x b).
Proof. exact (eq_refl (term183 s b x)). Qed.
Lemma lem5292883 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5292884 (s : real -> Prop) (x : real -> real) (b : real) : (term189 s b x) = (term190 s x b).
Proof. exact (MK_COMB (@lem5292883) (@lem5292882 s x b)). Qed.
Lemma lem5292885 (x : real) (s : real -> Prop) : (@IN real x s) = (@IN real x s).
Proof. exact (eq_refl (@IN real x s)). Qed.
Lemma lem5292886 (x : real -> real) (b : real) (x' : real) (s : real -> Prop) : (term191 b x x' s) = (term192 x b x' s).
Proof. exact (MK_COMB (@lem5292884 s x b) (@lem5292885 x' s)). Qed.
Lemma lem5292887 (b : real) (x : real) (s : real -> Prop) : (term193 b x s) = (term194 b x s).
Proof. exact (fun_ext (fun x' : real -> real => @lem5292886 x' b x s)). Qed.
Lemma lem5292888 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5292889 (b : real) (x : real) (s : real -> Prop) : (term182 b x s) = (term195 b x s).
Proof. exact (MK_COMB (@lem5292888) (@lem5292887 b x s)). Qed.
Lemma lem5292890 (b : real) (x : real) (s : real -> Prop) : ((term181 b x s) = (term182 b x s)) = ((term176 b x s) = (term195 b x s)).
Proof. exact (MK_COMB (@lem5292881 b x s) (@lem5292889 b x s)). Qed.
Lemma lem5292891 (b : real) (x : real) (s : real -> Prop) : (term176 b x s) = (term195 b x s).
Proof. exact (EQ_MP (@lem5292890 b x s) (@lem5292871 b x s)). Qed.
Lemma lem5292892 (b : real) (x : real) (s : real -> Prop) : (term109 b x s) = (term195 b x s).
Proof. exact (TRANS (@lem5292867 b x s) (@lem5292891 b x s)). Qed.
Lemma lem5292893 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5292894 (b : real) (x : real) (s : real -> Prop) : (term110 b x s) = (term196 b x s).
Proof. exact (MK_COMB (@lem5292893) (@lem5292892 b x s)). Qed.
Lemma lem5292895 (x : real) (b : real) : (term63 x b) = (term63 x b).
Proof. exact (eq_refl (term63 x b)). Qed.
Lemma lem5292896 (s : real -> Prop) (x : real) (b : real) : (term111 s x b) = (term197 s x b).
Proof. exact (MK_COMB (@lem5292894 b x s) (@lem5292895 x b)). Qed.
Lemma lem5292898 {A : Type'} (P : A -> Prop) (Q : Prop) : (term177 A P Q) = (term178 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5292899 (P : type1028) (Q : Prop) : (term179 P Q) = (term180 P Q).
Proof. exact (@lem5292898 (real -> real) P Q). Qed.
Lemma lem5292900 (s : real -> Prop) (x : real) (b : real) : (term198 s x b) = (term199 s x b).
Proof. exact (@lem5292899 (term194 b x s) (term63 x b)). Qed.
Lemma lem5292901 (x : real -> real) (b : real) (x' : real) (s : real -> Prop) : (term200 b x' s x) = (term192 x b x' s).
Proof. exact (eq_refl (term200 b x' s x)). Qed.
Lemma lem5292902 (b : real) (x : real) (s : real -> Prop) : (term201 b x s) = (term194 b x s).
Proof. exact (fun_ext (fun x' : real -> real => @lem5292901 x' b x s)). Qed.
Lemma lem5292903 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5292904 (b : real) (x : real) (s : real -> Prop) : (term202 b x s) = (term195 b x s).
Proof. exact (MK_COMB (@lem5292903) (@lem5292902 b x s)). Qed.
Lemma lem5292905 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5292906 (b : real) (x : real) (s : real -> Prop) : (term203 b x s) = (term196 b x s).
Proof. exact (MK_COMB (@lem5292905) (@lem5292904 b x s)). Qed.
Lemma lem5292907 (x : real) (b : real) : (term63 x b) = (term63 x b).
Proof. exact (eq_refl (term63 x b)). Qed.
Lemma lem5292908 (s : real -> Prop) (x : real) (b : real) : (term198 s x b) = (term197 s x b).
Proof. exact (MK_COMB (@lem5292906 b x s) (@lem5292907 x b)). Qed.
Lemma lem5292909 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5292910 (s : real -> Prop) (x : real) (b : real) : (term204 s x b) = (term205 s x b).
Proof. exact (MK_COMB (@lem5292909) (@lem5292908 s x b)). Qed.
Lemma lem5292911 (x : real -> real) (b : real) (x' : real) (s : real -> Prop) : (term200 b x' s x) = (term192 x b x' s).
Proof. exact (eq_refl (term200 b x' s x)). Qed.
Lemma lem5292912 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5292913 (x : real -> real) (b : real) (x' : real) (s : real -> Prop) : (term206 b x' s x) = (term207 x b x' s).
Proof. exact (MK_COMB (@lem5292912) (@lem5292911 x b x' s)). Qed.
Lemma lem5292914 (x : real) (b : real) : (term63 x b) = (term63 x b).
Proof. exact (eq_refl (term63 x b)). Qed.
Lemma lem5292915 (x : real -> real) (s : real -> Prop) (x' : real) (b : real) : (term208 s x x' b) = (term209 x s x' b).
Proof. exact (MK_COMB (@lem5292913 x b x' s) (@lem5292914 x' b)). Qed.
Lemma lem5292916 (s : real -> Prop) (x : real) (b : real) : (term210 s x b) = (term211 s x b).
Proof. exact (fun_ext (fun x' : real -> real => @lem5292915 x' s x b)). Qed.
Lemma lem5292917 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5292918 (s : real -> Prop) (x : real) (b : real) : (term199 s x b) = (term212 s x b).
Proof. exact (MK_COMB (@lem5292917) (@lem5292916 s x b)). Qed.
Lemma lem5292919 (s : real -> Prop) (x : real) (b : real) : ((term198 s x b) = (term199 s x b)) = ((term197 s x b) = (term212 s x b)).
Proof. exact (MK_COMB (@lem5292910 s x b) (@lem5292918 s x b)). Qed.
Lemma lem5292920 (s : real -> Prop) (x : real) (b : real) : (term197 s x b) = (term212 s x b).
Proof. exact (EQ_MP (@lem5292919 s x b) (@lem5292900 s x b)). Qed.
Lemma lem5292921 (s : real -> Prop) (x : real) (b : real) : (term111 s x b) = (term212 s x b).
Proof. exact (TRANS (@lem5292896 s x b) (@lem5292920 s x b)). Qed.
Lemma lem5292922 (s : real -> Prop) (x : real) (b : real) : (term83 s x b) = (term212 s x b).
Proof. exact (TRANS (@lem5292782 s x b) (@lem5292921 s x b)). Qed.
Lemma lem5292923 (s : real -> Prop) (x : real) (b : real) : (term21 s x b) = (term212 s x b).
Proof. exact (TRANS (@lem5292555 s x b) (@lem5292922 s x b)). Qed.
Lemma lem5292924 (s : real -> Prop) (x : real) (b : real) (h1 : term21 s x b) : term212 s x b.
Proof. exact (EQ_MP (@lem5292923 s x b) (@lem5292501 s x b h1)). Qed.
Lemma lem5292925 (x : real) : (real_le x x) = (real_le x x).
Proof. exact (eq_refl (real_le x x)). Qed.
Lemma lem5292926 : term43 = term43.
Proof. exact (fun_ext (fun x : real => @lem5292925 x)). Qed.
Lemma lem5292927 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5292936 : term28 = term28.
Proof. exact (MK_COMB (@lem5292927) (@lem5292926)). Qed.
Lemma lem5292937 (h1 : term28) : term28.
Proof. exact (EQ_MP (@lem5292936) (@lem5292502 h1)). Qed.
Lemma lem5292938 (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (h1 : term209 x' s x b) : term209 x' s x b.
Proof. exact (h1). Qed.
Lemma lem5292943 (x : real) : (real_le x x) = (real_le x x).
Proof. exact (eq_refl (real_le x x)). Qed.
Lemma lem5292944 : term43 = term43.
Proof. exact (fun_ext (fun x : real => @lem5292943 x)). Qed.
Lemma lem5292945 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5292946 : term28 = term28.
Proof. exact (MK_COMB (@lem5292945) (@lem5292944)). Qed.
Lemma lem5292947 (h1 : term28) : term28.
Proof. exact (EQ_MP (@lem5292946) (@lem5292937 h1)). Qed.
Lemma lem5292954 (x : real) (b : real) : (term63 x b) = (term63 x b).
Proof. exact (eq_refl (term63 x b)). Qed.
Lemma lem5292959 (x : real) (s : real -> Prop) : (@IN real x s) = (@IN real x s).
Proof. exact (eq_refl (@IN real x s)). Qed.
Lemma lem5292986 (s : real -> Prop) (x' : real -> real) (b : real) (c : real) : (term150 s x' b c) = (term150 s x' b c).
Proof. exact (eq_refl (term150 s x' b c)). Qed.
Lemma lem5292987 (s : real -> Prop) (x' : real -> real) (b : real) : (term152 s x' b) = (term152 s x' b).
Proof. exact (fun_ext (fun c : real => @lem5292986 s x' b c)). Qed.
Lemma lem5292988 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5292989 (s : real -> Prop) (x' : real -> real) (b : real) : (term154 s x' b) = (term154 s x' b).
Proof. exact (MK_COMB (@lem5292988) (@lem5292987 s x' b)). Qed.
Lemma lem5292996 (b : real) (c : real) : (term63 b c) = (term63 b c).
Proof. exact (eq_refl (term63 b c)). Qed.
Lemma lem5293011 (s : real -> Prop) (x : real) (c : real) : (term51 s x c) = (term51 s x c).
Proof. exact (eq_refl (term51 s x c)). Qed.
Lemma lem5293012 (s : real -> Prop) (c : real) : (term61 s c) = (term61 s c).
Proof. exact (fun_ext (fun x : real => @lem5293011 s x c)). Qed.
Lemma lem5293013 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5293014 (s : real -> Prop) (c : real) : (term62 s c) = (term62 s c).
Proof. exact (MK_COMB (@lem5293013) (@lem5293012 s c)). Qed.
Lemma lem5293015 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5293016 (s : real -> Prop) (c : real) : (term69 s c) = (term69 s c).
Proof. exact (MK_COMB (@lem5293015) (@lem5293014 s c)). Qed.
Lemma lem5293017 (s : real -> Prop) (b : real) (c : real) : (term71 s b c) = (term71 s b c).
Proof. exact (MK_COMB (@lem5293016 s c) (@lem5292996 b c)). Qed.
Lemma lem5293018 (s : real -> Prop) (b : real) : (term90 s b) = (term90 s b).
Proof. exact (fun_ext (fun c : real => @lem5293017 s b c)). Qed.
Lemma lem5293019 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5293020 (s : real -> Prop) (b : real) : (term101 s b) = (term101 s b).
Proof. exact (MK_COMB (@lem5293019) (@lem5293018 s b)). Qed.
Lemma lem5293021 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5293022 (s : real -> Prop) (b : real) : (term103 s b) = (term103 s b).
Proof. exact (MK_COMB (@lem5293021) (@lem5293020 s b)). Qed.
Lemma lem5293023 (s : real -> Prop) (x' : real -> real) (b : real) : (term171 s x' b) = (term171 s x' b).
Proof. exact (MK_COMB (@lem5293022 s b) (@lem5292989 s x' b)). Qed.
Lemma lem5293024 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5293025 (s : real -> Prop) (x' : real -> real) (b : real) : (term190 s x' b) = (term190 s x' b).
Proof. exact (MK_COMB (@lem5293024) (@lem5293023 s x' b)). Qed.
Lemma lem5293026 (x' : real -> real) (b : real) (x : real) (s : real -> Prop) : (term192 x' b x s) = (term192 x' b x s).
Proof. exact (MK_COMB (@lem5293025 s x' b) (@lem5292959 x s)). Qed.
Lemma lem5293027 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5293028 (x' : real -> real) (b : real) (x : real) (s : real -> Prop) : (term207 x' b x s) = (term207 x' b x s).
Proof. exact (MK_COMB (@lem5293027) (@lem5293026 x' b x s)). Qed.
Lemma lem5293029 (x' : real -> real) (s : real -> Prop) (x : real) (b : real) : (term209 x' s x b) = (term209 x' s x b).
Proof. exact (MK_COMB (@lem5293028 x' b x s) (@lem5292954 x b)). Qed.
Lemma lem5293030 (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (h1 : term209 x' s x b) : term209 x' s x b.
Proof. exact (EQ_MP (@lem5293029 x' s x b) (@lem5292938 x' s x b h1)). Qed.
Lemma lem5293032 (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (h1 : term209 x' s x b) : term192 x' b x s.
Proof. exact (proj1 (@lem5293030 x' s x b h1)). Qed.
Lemma lem5293034 (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (h1 : term209 x' s x b) : term171 s x' b.
Proof. exact (proj1 (@lem5293032 x' s x b h1)). Qed.
Lemma lem5293036 (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (h1 : term209 x' s x b) : term101 s b.
Proof. exact (proj1 (@lem5293034 x' s x b h1)). Qed.
Lemma lem5293038 (x : real) : (real_le x x) = (real_le x x).
Proof. exact (eq_refl (real_le x x)). Qed.
Lemma lem5293039 : term43 = term43.
Proof. exact (fun_ext (fun x : real => @lem5293038 x)). Qed.
Lemma lem5293040 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5293042 : term28 = term28.
Proof. exact (MK_COMB (@lem5293040) (@lem5293039)). Qed.
Lemma lem5293043 (h1 : term28) : term28.
Proof. exact (EQ_MP (@lem5293042) (@lem5292947 h1)). Qed.
Lemma lem5293053 {A : Type'} (P : A -> Prop) (Q : Prop) : (term213 A P Q) = (term214 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem5293054 (P : real -> Prop) (Q : Prop) : (term215 P Q) = (term216 P Q).
Proof. exact (@lem5293053 real P Q). Qed.
Lemma lem5293055 (s : real -> Prop) (b : real) (c : real) : (term217 s b c) = (term218 s b c).
Proof. exact (@lem5293054 (term61 s c) (term63 b c)). Qed.
Lemma lem5293056 (s : real -> Prop) (x : real) (c : real) : (term219 s c x) = (term51 s x c).
Proof. exact (eq_refl (term219 s c x)). Qed.
Lemma lem5293057 (s : real -> Prop) (c : real) : (term220 s c) = (term61 s c).
Proof. exact (fun_ext (fun x : real => @lem5293056 s x c)). Qed.
Lemma lem5293058 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5293059 (s : real -> Prop) (c : real) : (term221 s c) = (term62 s c).
Proof. exact (MK_COMB (@lem5293058) (@lem5293057 s c)). Qed.
Lemma lem5293060 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5293061 (s : real -> Prop) (c : real) : (term222 s c) = (term69 s c).
Proof. exact (MK_COMB (@lem5293060) (@lem5293059 s c)). Qed.
Lemma lem5293062 (b : real) (c : real) : (term63 b c) = (term63 b c).
Proof. exact (eq_refl (term63 b c)). Qed.
Lemma lem5293063 (s : real -> Prop) (b : real) (c : real) : (term217 s b c) = (term71 s b c).
Proof. exact (MK_COMB (@lem5293061 s c) (@lem5293062 b c)). Qed.
Lemma lem5293064 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5293065 (s : real -> Prop) (b : real) (c : real) : (term223 s b c) = (term224 s b c).
Proof. exact (MK_COMB (@lem5293064) (@lem5293063 s b c)). Qed.
Lemma lem5293066 (s : real -> Prop) (x : real) (c : real) : (term219 s c x) = (term51 s x c).
Proof. exact (eq_refl (term219 s c x)). Qed.
Lemma lem5293067 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5293068 (s : real -> Prop) (x : real) (c : real) : (term225 s c x) = (term226 s x c).
Proof. exact (MK_COMB (@lem5293067) (@lem5293066 s x c)). Qed.
Lemma lem5293069 (b : real) (c : real) : (term63 b c) = (term63 b c).
Proof. exact (eq_refl (term63 b c)). Qed.
Lemma lem5293070 (s : real -> Prop) (x : real) (b : real) (c : real) : (term227 s x b c) = (term228 s x b c).
Proof. exact (MK_COMB (@lem5293068 s x c) (@lem5293069 b c)). Qed.
Lemma lem5293071 (s : real -> Prop) (b : real) (c : real) : (term229 s b c) = (term230 s b c).
Proof. exact (fun_ext (fun x : real => @lem5293070 s x b c)). Qed.
Lemma lem5293072 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5293073 (s : real -> Prop) (b : real) (c : real) : (term218 s b c) = (term231 s b c).
Proof. exact (MK_COMB (@lem5293072) (@lem5293071 s b c)). Qed.
Lemma lem5293074 (s : real -> Prop) (b : real) (c : real) : ((term217 s b c) = (term218 s b c)) = ((term71 s b c) = (term231 s b c)).
Proof. exact (MK_COMB (@lem5293065 s b c) (@lem5293073 s b c)). Qed.
Lemma lem5293075 (s : real -> Prop) (b : real) (c : real) : (term71 s b c) = (term231 s b c).
Proof. exact (EQ_MP (@lem5293074 s b c) (@lem5293055 s b c)). Qed.
Lemma lem5293076 (s : real -> Prop) (b : real) : (term90 s b) = (term232 s b).
Proof. exact (fun_ext (fun c : real => @lem5293075 s b c)). Qed.
Lemma lem5293077 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5293078 (s : real -> Prop) (b : real) : (term101 s b) = (term233 s b).
Proof. exact (MK_COMB (@lem5293077) (@lem5293076 s b)). Qed.
Lemma lem5293091 (s : real -> Prop) (x : real) (b : real) (c : real) : (term228 s x b c) = (term228 s x b c).
Proof. exact (eq_refl (term228 s x b c)). Qed.
Lemma lem5293092 (s : real -> Prop) (b : real) (c : real) : (term230 s b c) = (term230 s b c).
Proof. exact (fun_ext (fun x : real => @lem5293091 s x b c)). Qed.
Lemma lem5293093 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5293094 (s : real -> Prop) (b : real) (c : real) : (term231 s b c) = (term231 s b c).
Proof. exact (MK_COMB (@lem5293093) (@lem5293092 s b c)). Qed.
Lemma lem5293095 (s : real -> Prop) (b : real) : (term232 s b) = (term232 s b).
Proof. exact (fun_ext (fun c : real => @lem5293094 s b c)). Qed.
Lemma lem5293096 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5293097 (s : real -> Prop) (b : real) : (term233 s b) = (term233 s b).
Proof. exact (MK_COMB (@lem5293096) (@lem5293095 s b)). Qed.
Lemma lem5293098 (s : real -> Prop) (b : real) : (term101 s b) = (term233 s b).
Proof. exact (TRANS (@lem5293078 s b) (@lem5293097 s b)). Qed.
Lemma lem5293099 (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (h1 : term209 x' s x b) : term233 s b.
Proof. exact (EQ_MP (@lem5293098 s b) (@lem5293036 x' s x b h1)). Qed.
Lemma lem5293123 (_69282 : real) (h1 : term28) : term234 _69282.
Proof. exact (@lem5293043 h1 _69282). Qed.
Lemma lem5293124 (_69282 : real) : (term234 _69282) = (real_le _69282 _69282).
Proof. exact (eq_refl (term234 _69282)). Qed.
Lemma lem5293126 (_69283 : real) (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (h1 : term209 x' s x b) : term235 s b _69283.
Proof. exact (@lem5293099 x' s x b h1 _69283). Qed.
Lemma lem5293127 (s : real -> Prop) (b : real) (_69283 : real) : (term235 s b _69283) = (term231 s b _69283).
Proof. exact (eq_refl (term235 s b _69283)). Qed.
Lemma lem5293128 (_69283 : real) (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (h1 : term209 x' s x b) : term231 s b _69283.
Proof. exact (EQ_MP (@lem5293127 s b _69283) (@lem5293126 _69283 x' s x b h1)). Qed.
Lemma lem5293129 (_69283 : real) (_69284 : real) (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (h1 : term209 x' s x b) : term236 s b _69283 _69284.
Proof. exact (@lem5293128 _69283 x' s x b h1 _69284). Qed.
Lemma lem5293130 (s : real -> Prop) (_69284 : real) (b : real) (_69283 : real) : (term236 s b _69283 _69284) = (term228 s _69284 b _69283).
Proof. exact (eq_refl (term236 s b _69283 _69284)). Qed.
Lemma lem5293131 (_69284 : real) (_69283 : real) (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (h1 : term209 x' s x b) : term228 s _69284 b _69283.
Proof. exact (EQ_MP (@lem5293130 s _69284 b _69283) (@lem5293129 _69283 _69284 x' s x b h1)). Qed.
Lemma lem5293140 (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (h1 : term209 x' s x b) : term63 x b.
Proof. exact (proj2 (@lem5293030 x' s x b h1)). Qed.
Lemma lem5293153 (s : real -> Prop) (_69284 : real) (b : real) (_69283 : real) : (term228 s _69284 b _69283) = (term237 s _69284 b _69283).
Proof. exact (@lem5292288 (term238 _69284 s) (real_le _69284 _69283) (term63 b _69283)). Qed.
Lemma lem5293154 (_69284 : real) (_69283 : real) (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (h1 : term209 x' s x b) : term237 s _69284 b _69283.
Proof. exact (EQ_MP (@lem5293153 s _69284 b _69283) (@lem5293131 _69284 _69283 x' s x b h1)). Qed.
Lemma lem5293168 (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (h1 : term209 x' s x b) : @IN real x s.
Proof. exact (proj2 (@lem5293032 x' s x b h1)). Qed.
Lemma lem5293169 (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (h1 : term209 x' s x b) : term239 x s.
Proof. exact (fun h0 : term238 x s => @lem5293168 x' s x b h1). Qed.
Lemma lem5293171 (p : Prop) : (term240 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5293172 (x : real) (s : real -> Prop) : (term239 x s) = (@IN real x s).
Proof. exact (@lem5293171 (@IN real x s)). Qed.
Lemma lem5293173 (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (h1 : term209 x' s x b) : @IN real x s.
Proof. exact (EQ_MP (@lem5293172 x s) (@lem5293169 x' s x b h1)). Qed.
Lemma lem5293175 (_69282 : real) (h1 : term28) : real_le _69282 _69282.
Proof. exact (EQ_MP (@lem5293124 _69282) (@lem5293123 _69282 h1)). Qed.
Lemma lem5293176 (b : real) (h1 : term28) : real_le b b.
Proof. exact (@lem5293175 b h1). Qed.
Lemma lem5293177 (b : real) (h1 : term28) : term241 b.
Proof. exact (fun h0 : term242 b => @lem5293176 b h1). Qed.
Lemma lem5293179 (p : Prop) : (term240 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5293180 (b : real) : (term241 b) = (real_le b b).
Proof. exact (@lem5293179 (real_le b b)). Qed.
Lemma lem5293181 (b : real) (h1 : term28) : real_le b b.
Proof. exact (EQ_MP (@lem5293180 b) (@lem5293177 b h1)). Qed.
Lemma lem5293187 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5293188 (_69284 : real) (s : real -> Prop) (b : real) (_69283 : real) : (term237 s _69284 b _69283) = (term243 _69284 s b _69283).
Proof. exact (@lem5293187 (real_le _69284 _69283) (term238 _69284 s) (term63 b _69283)). Qed.
Lemma lem5293204 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5293205 (_69284 : real) (s : real -> Prop) (b : real) (_69283 : real) : (term244 s _69284 b _69283) = (term245 _69284 s b _69283).
Proof. exact (MK_COMB (@lem5293204) (@lem5293188 _69284 s b _69283)). Qed.
Lemma lem5293221 (_69284 : real) (s : real -> Prop) (b : real) (_69283 : real) : (term243 _69284 s b _69283) = (term243 _69284 s b _69283).
Proof. exact (eq_refl (term243 _69284 s b _69283)). Qed.
Lemma lem5293222 (_69284 : real) (s : real -> Prop) (b : real) (_69283 : real) : ((term237 s _69284 b _69283) = (term243 _69284 s b _69283)) = ((term243 _69284 s b _69283) = (term243 _69284 s b _69283)).
Proof. exact (MK_COMB (@lem5293205 _69284 s b _69283) (@lem5293221 _69284 s b _69283)). Qed.
Lemma lem5293224 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5293225 (x : Prop) : (x = x) = True.
Proof. exact (@lem5293224 Prop x). Qed.
Lemma lem5293226 (_69284 : real) (s : real -> Prop) (b : real) (_69283 : real) : ((term243 _69284 s b _69283) = (term243 _69284 s b _69283)) = True.
Proof. exact (@lem5293225 (term243 _69284 s b _69283)). Qed.
Lemma lem5293227 (_69284 : real) (s : real -> Prop) (b : real) (_69283 : real) : ((term237 s _69284 b _69283) = (term243 _69284 s b _69283)) = True.
Proof. exact (TRANS (@lem5293222 _69284 s b _69283) (@lem5293226 _69284 s b _69283)). Qed.
Lemma lem5293228 (_69284 : real) (s : real -> Prop) (b : real) (_69283 : real) : True = ((term237 s _69284 b _69283) = (term243 _69284 s b _69283)).
Proof. exact (SYM (@lem5293227 _69284 s b _69283)). Qed.
Lemma lem5293229 (_69284 : real) (s : real -> Prop) (b : real) (_69283 : real) : (term237 s _69284 b _69283) = (term243 _69284 s b _69283).
Proof. exact (EQ_MP (@lem5293228 _69284 s b _69283) (@lem0)). Qed.
Lemma lem5293230 (_69284 : real) (_69283 : real) (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (h1 : term209 x' s x b) : term243 _69284 s b _69283.
Proof. exact (EQ_MP (@lem5293229 _69284 s b _69283) (@lem5293154 _69284 _69283 x' s x b h1)). Qed.
Lemma lem5293232 (b : Prop) (a : Prop) : (a \/ b) = (term246 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5293233 (s : real -> Prop) (b : real) (_69284 : real) (_69283 : real) : (term243 _69284 s b _69283) = (term247 s b _69284 _69283).
Proof. exact (@lem5293232 (term248 _69284 s b _69283) (real_le _69284 _69283)). Qed.
Lemma lem5293235 (a : Prop) (b : Prop) : (term249 a b) = (term250 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5293236 (_69284 : real) (s : real -> Prop) (b : real) (_69283 : real) : (term251 _69284 s b _69283) = (term252 _69284 s b _69283).
Proof. exact (@lem5293235 (term238 _69284 s) (term63 b _69283)). Qed.
Lemma lem5293238 (a : Prop) : (term253 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5293239 (_69284 : real) (s : real -> Prop) : (term254 _69284 s) = (@IN real _69284 s).
Proof. exact (@lem5293238 (@IN real _69284 s)). Qed.
Lemma lem5293240 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5293241 (_69284 : real) (s : real -> Prop) : (term255 _69284 s) = (term256 _69284 s).
Proof. exact (MK_COMB (@lem5293240) (@lem5293239 _69284 s)). Qed.
Lemma lem5293243 (a : Prop) : (term253 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5293244 (b : real) (_69283 : real) : (term257 b _69283) = (real_le b _69283).
Proof. exact (@lem5293243 (real_le b _69283)). Qed.
Lemma lem5293245 (_69284 : real) (s : real -> Prop) (b : real) (_69283 : real) : (term252 _69284 s b _69283) = (term258 _69284 s b _69283).
Proof. exact (MK_COMB (@lem5293241 _69284 s) (@lem5293244 b _69283)). Qed.
Lemma lem5293246 (_69284 : real) (s : real -> Prop) (b : real) (_69283 : real) : (term251 _69284 s b _69283) = (term258 _69284 s b _69283).
Proof. exact (TRANS (@lem5293236 _69284 s b _69283) (@lem5293245 _69284 s b _69283)). Qed.
Lemma lem5293247 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5293248 (_69284 : real) (s : real -> Prop) (b : real) (_69283 : real) : (term259 _69284 s b _69283) = (term260 _69284 s b _69283).
Proof. exact (MK_COMB (@lem5293247) (@lem5293246 _69284 s b _69283)). Qed.
Lemma lem5293249 (_69284 : real) (_69283 : real) : (real_le _69284 _69283) = (real_le _69284 _69283).
Proof. exact (eq_refl (real_le _69284 _69283)). Qed.
Lemma lem5293250 (s : real -> Prop) (b : real) (_69284 : real) (_69283 : real) : (term247 s b _69284 _69283) = (term261 s b _69284 _69283).
Proof. exact (MK_COMB (@lem5293248 _69284 s b _69283) (@lem5293249 _69284 _69283)). Qed.
Lemma lem5293251 (s : real -> Prop) (b : real) (_69284 : real) (_69283 : real) : (term243 _69284 s b _69283) = (term261 s b _69284 _69283).
Proof. exact (TRANS (@lem5293233 s b _69284 _69283) (@lem5293250 s b _69284 _69283)). Qed.
Lemma lem5293253 (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (h1 : term28) (h2 : term209 x' s x b) : term262 x s b.
Proof. exact (conj (@lem5293173 x' s x b h2) (@lem5293181 b h1)). Qed.
Lemma lem5293255 (_69284 : real) (_69283 : real) (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (h1 : term209 x' s x b) : term261 s b _69284 _69283.
Proof. exact (EQ_MP (@lem5293251 s b _69284 _69283) (@lem5293230 _69284 _69283 x' s x b h1)). Qed.
Lemma lem5293256 (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (h1 : term209 x' s x b) : term263 s x b.
Proof. exact (@lem5293255 x b x' s x b h1). Qed.
Lemma lem5293259 (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (h1 : term28) (h2 : term209 x' s x b) : real_le x b.
Proof. exact (@lem5293256 x' s x b h2 (@lem5293253 x' s x b h1 h2)). Qed.
Lemma lem5293260 (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (h1 : term28) (h2 : term209 x' s x b) : term264 x b.
Proof. exact (fun h0 : term63 x b => @lem5293259 x' s x b h1 h2). Qed.
Lemma lem5293262 (p : Prop) : (term240 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5293263 (x : real) (b : real) : (term264 x b) = (real_le x b).
Proof. exact (@lem5293262 (real_le x b)). Qed.
Lemma lem5293264 (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (h1 : term28) (h2 : term209 x' s x b) : real_le x b.
Proof. exact (EQ_MP (@lem5293263 x b) (@lem5293260 x' s x b h1 h2)). Qed.
Lemma lem5293267 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5293269 (x : real) (b : real) : (term63 x b) = (term265 x b).
Proof. exact (@lem5293267 (real_le x b)). Qed.
Lemma lem5293272 (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (h1 : term209 x' s x b) : term265 x b.
Proof. exact (EQ_MP (@lem5293269 x b) (@lem5293140 x' s x b h1)). Qed.
Lemma lem5293275 (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (h1 : term28) (h2 : term209 x' s x b) : False.
Proof. exact (@lem5293272 x' s x b h2 (@lem5293264 x' s x b h1 h2)). Qed.
Lemma lem5293276 (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (h1 : term28) (h2 : term209 x' s x b) : term266.
Proof. exact (fun h0 : ~ False => @lem5293275 x' s x b h1 h2). Qed.
Lemma lem5293278 (p : Prop) : (term240 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5293279 : term266 = False.
Proof. exact (@lem5293278 False). Qed.
Lemma lem5293280 (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (h1 : term28) (h2 : term209 x' s x b) : False.
Proof. exact (EQ_MP (@lem5293279) (@lem5293276 x' s x b h1 h2)). Qed.
Lemma lem5293281 (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (h1 : term28) (h2 : term209 x' s x b) : term28 = False.
Proof. exact (prop_ext (fun h3 : term28 => @lem5293280 x' s x b h1 h2) (fun h3 : False => @lem5293043 h1)). Qed.
Lemma lem5293282 (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (h1 : term28) (h2 : term209 x' s x b) : False.
Proof. exact (EQ_MP (@lem5293281 x' s x b h1 h2) (@lem5293043 h1)). Qed.
Lemma lem5293283 (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (h1 : term28) (h2 : term209 x' s x b) : (term209 x' s x b) = False.
Proof. exact (prop_ext (fun h3 : term209 x' s x b => @lem5293282 x' s x b h1 h2) (fun h3 : False => @lem5293030 x' s x b h2)). Qed.
Lemma lem5293284 (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (h1 : term28) (h2 : term209 x' s x b) : False.
Proof. exact (EQ_MP (@lem5293283 x' s x b h1 h2) (@lem5293030 x' s x b h2)). Qed.
Lemma lem5293285 (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (h1 : term28) (h2 : term209 x' s x b) : term28 = False.
Proof. exact (prop_ext (fun h3 : term28 => @lem5293284 x' s x b h1 h2) (fun h3 : False => @lem5292947 h1)). Qed.
Lemma lem5293286 (x' : real -> real) (s : real -> Prop) (x : real) (b : real) (h1 : term28) (h2 : term209 x' s x b) : False.
Proof. exact (EQ_MP (@lem5293285 x' s x b h1 h2) (@lem5292947 h1)). Qed.
Lemma lem5293287 (s : real -> Prop) (x : real) (b : real) (h1 : term28) (h2 : term21 s x b) : False.
Proof. exact (ex_elim (@lem5292924 s x b h2) (fun x' : real -> real => fun h0 : term211 s x b x' => @lem5293286 x' s x b h1 h0)). Qed.
Lemma lem5293288 (s : real -> Prop) (x : real) (b : real) (h1 : term28) (h2 : term21 s x b) : term28 = False.
Proof. exact (prop_ext (fun h3 : term28 => @lem5293287 s x b h1 h2) (fun h3 : False => @lem5292937 h1)). Qed.
Lemma lem5293289 (s : real -> Prop) (x : real) (b : real) (h1 : term28) (h2 : term21 s x b) : False.
Proof. exact (EQ_MP (@lem5293288 s x b h1 h2) (@lem5292937 h1)). Qed.
Lemma lem5293290 (s : real -> Prop) (x : real) (b : real) (h1 : term21 s x b) : term26.
Proof. exact (fun h0 : term28 => @lem5293289 s x b h0 h1). Qed.
Lemma lem5293291 : term26 = term27.
Proof. exact (@lem69 term28). Qed.
Lemma lem5293292 (s : real -> Prop) (x : real) (b : real) (h1 : term21 s x b) : term27.
Proof. exact (EQ_MP (@lem5293291) (@lem5293290 s x b h1)). Qed.
Lemma lem5293293 (s : real -> Prop) (x : real) (b : real) : term30 s x b.
Proof. exact (fun h0 : term21 s x b => @lem5293292 s x b h0). Qed.
Lemma lem5293298 (x : real) (b : real) : term34 x b.
Proof. exact (fun s : real -> Prop => @lem5293293 s x b). Qed.
Lemma lem5293303 (b : real) : term38 b.
Proof. exact (fun x : real => @lem5293298 x b). Qed.
Lemma lem5293308 : term42.
Proof. exact (fun b : real => @lem5293303 b). Qed.
Lemma lem5293309 : term41.
Proof. exact (EQ_MP (@lem5292500) (@lem5293308)). Qed.
Lemma lem5293310 (b : real) : term267 b.
Proof. exact (@lem5293309 b). Qed.
Lemma lem5293311 (b : real) : (term267 b) = (term37 b).
Proof. exact (eq_refl (term267 b)). Qed.
Lemma lem5293312 (b : real) : term37 b.
Proof. exact (EQ_MP (@lem5293311 b) (@lem5293310 b)). Qed.
Lemma lem5293313 (b : real) (x : real) : term268 b x.
Proof. exact (@lem5293312 b x). Qed.
Lemma lem5293314 (x : real) (b : real) : (term268 b x) = (term33 x b).
Proof. exact (eq_refl (term268 b x)). Qed.
Lemma lem5293315 (x : real) (b : real) : term33 x b.
Proof. exact (EQ_MP (@lem5293314 x b) (@lem5293313 b x)). Qed.
Lemma lem5293316 (x : real) (b : real) (s : real -> Prop) : term269 x b s.
Proof. exact (@lem5293315 x b s). Qed.
Lemma lem5293317 (s : real -> Prop) (x : real) (b : real) : (term269 x b s) = (term22 s x b).
Proof. exact (eq_refl (term269 x b s)). Qed.
Lemma lem5293318 (s : real -> Prop) (x : real) (b : real) : term22 s x b.
Proof. exact (EQ_MP (@lem5293317 s x b) (@lem5293316 x b s)). Qed.
Lemma lem5293320 (s : real -> Prop) (x : real) (b : real) : term22 s x b.
Proof. exact (@lem5292345 s x b (@lem5293318 s x b)). Qed.
Lemma lem5293321 (s : real -> Prop) (x : real) (b : real) (h1 : term21 s x b) : term26.
Proof. exact (@lem5293320 s x b (@lem5292330 s x b h1)). Qed.
Lemma lem5293322 (s : real -> Prop) (x : real) (b : real) (h1 : term21 s x b) : False.
Proof. exact (@lem5293321 s x b h1 (@lem1339240)). Qed.
Lemma lem5293323 (s : real -> Prop) (x : real) (b : real) (h1 : term21 s x b) : (term21 s x b) = False.
Proof. exact (prop_ext (fun h2 : term21 s x b => @lem5293322 s x b h1) (fun h2 : False => @lem5292330 s x b h1)). Qed.
Lemma lem5293324 (s : real -> Prop) (x : real) (b : real) (h1 : term21 s x b) : False.
Proof. exact (EQ_MP (@lem5293323 s x b h1) (@lem5292330 s x b h1)). Qed.
Lemma lem5293325 (s : real -> Prop) (x : real) (b : real) : term20 s x b.
Proof. exact (fun h0 : term21 s x b => @lem5293324 s x b h0). Qed.
Lemma lem5293326 (s : real -> Prop) (x : real) (b : real) : term18 s x b.
Proof. exact (EQ_MP (@lem5292329 s x b) (@lem5293325 s x b)). Qed.
Lemma lem5293327 (s : real -> Prop) (x : real) (b : real) : term17 s x b.
Proof. exact (EQ_MP (@lem5292325 s x b) (@lem5293326 s x b)). Qed.
Lemma lem5293332 (s : real -> Prop) (b : real) : term270 s b.
Proof. exact (fun x : real => @lem5293327 s x b). Qed.
Lemma lem5293337 (s : real -> Prop) : term271 s.
Proof. exact (fun b : real => @lem5293332 s b). Qed.
Lemma lem5293342 : term272.
Proof. exact (fun s : real -> Prop => @lem5293337 s). Qed.
