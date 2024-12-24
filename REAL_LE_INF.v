Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LE_INF_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import INF_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm19030_spec.
Require Import thm19031_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem5236202 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5236203 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem5236204 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem5236203 t1) (@lem5236202 t1)). Qed.
Lemma lem5236205 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem5236204 t1 t2). Qed.
Lemma lem5236206 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem5236207 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem5236206 t1 t2) (@lem5236205 t1 t2)). Qed.
Lemma lem5236208 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem5236207 t1 t2 t3). Qed.
Lemma lem5236209 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem5236210 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem5236209 t1 t2 t3) (@lem5236208 t1 t2 t3)). Qed.
Lemma lem5236211 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem5236210 t1 t2 t3)). Qed.
Lemma lem5236213 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5236214 (s : real -> Prop) : (term8 s) = (term9 s).
Proof. exact (@lem5236213 (term8 s)). Qed.
Lemma lem5236215 (s : real -> Prop) : (term9 s) = (term8 s).
Proof. exact (SYM (@lem5236214 s)). Qed.
Lemma lem5236216 (s : real -> Prop) (h1 : term10 s) : term10 s.
Proof. exact (h1). Qed.
Lemma lem5236219 (s : real -> Prop) (h1 : term11 s) : term11 s.
Proof. exact (h1). Qed.
Lemma lem5236220 (s : real -> Prop) : term12 s.
Proof. exact (fun h0 : term11 s => @lem5236219 s h0). Qed.
Lemma lem5236221 (s : real -> Prop) (h1 : term12 s) : term12 s.
Proof. exact (h1). Qed.
Lemma lem5236222 (s : real -> Prop) (h1 : term11 s) : term11 s.
Proof. exact (h1). Qed.
Lemma lem5236223 (s : real -> Prop) (h1 : term11 s) (h2 : term12 s) : term11 s.
Proof. exact (@lem5236221 s h2 (@lem5236222 s h1)). Qed.
Lemma lem5236224 (s : real -> Prop) (h1 : term11 s) : term13 s.
Proof. exact (fun h0 : term12 s => @lem5236223 s h1 h0). Qed.
Lemma lem5236225 (s : real -> Prop) (h1 : term12 s) : term12 s.
Proof. exact (h1). Qed.
Lemma lem5236226 (s : real -> Prop) (h1 : term11 s) (h2 : term12 s) : term11 s.
Proof. exact (@lem5236224 s h1 (@lem5236225 s h2)). Qed.
Lemma lem5236227 (s : real -> Prop) (h1 : term12 s) : term12 s.
Proof. exact (fun h0 : term11 s => @lem5236226 s h0 h1). Qed.
Lemma lem5236228 (s : real -> Prop) : term14 s.
Proof. exact (fun h0 : term12 s => @lem5236227 s h0). Qed.
Lemma lem5236231 (s : real -> Prop) : term12 s.
Proof. exact (@lem5236228 s (@lem5236220 s)). Qed.
Lemma lem5236253 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5236254 : term15 = term16.
Proof. exact (@lem5236253 term17). Qed.
Lemma lem5236293 (s : real -> Prop) : (term18 s) = (term18 s).
Proof. exact (eq_refl (term18 s)). Qed.
Lemma lem5236294 (s : real -> Prop) : (term11 s) = (term19 s).
Proof. exact (MK_COMB (@lem5236293 s) (@lem5236254)). Qed.
Lemma lem5236297 : term20 = term21.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5236294 s)). Qed.
Lemma lem5236298 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5236307 : term22 = term23.
Proof. exact (MK_COMB (@lem5236298) (@lem5236297)). Qed.
Lemma lem5236308 (b : real) (s : real -> Prop) : (term24 b s) = (term24 b s).
Proof. exact (eq_refl (term24 b s)). Qed.
Lemma lem5236313 (s : real -> Prop) (b : real) (x : real) : (term25 s b x) = (term25 s b x).
Proof. exact (eq_refl (term25 s b x)). Qed.
Lemma lem5236314 (s : real -> Prop) (b : real) : (term26 s b) = (term26 s b).
Proof. exact (fun_ext (fun x : real => @lem5236313 s b x)). Qed.
Lemma lem5236315 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5236316 (s : real -> Prop) (b : real) : (term27 s b) = (term27 s b).
Proof. exact (MK_COMB (@lem5236315) (@lem5236314 s b)). Qed.
Lemma lem5236317 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5236318 (s : real -> Prop) (b : real) : (term28 s b) = (term28 s b).
Proof. exact (MK_COMB (@lem5236317) (@lem5236316 s b)). Qed.
Lemma lem5236319 (b : real) (s : real -> Prop) : (term29 b s) = (term29 b s).
Proof. exact (MK_COMB (@lem5236318 s b) (@lem5236308 b s)). Qed.
Lemma lem5236320 (s : real -> Prop) : (term30 s) = (term30 s).
Proof. exact (fun_ext (fun b : real => @lem5236319 b s)). Qed.
Lemma lem5236321 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5236322 (s : real -> Prop) : (term31 s) = (term31 s).
Proof. exact (MK_COMB (@lem5236321) (@lem5236320 s)). Qed.
Lemma lem5236327 (s : real -> Prop) (x : real) : (term32 s x) = (term32 s x).
Proof. exact (eq_refl (term32 s x)). Qed.
Lemma lem5236328 (s : real -> Prop) : (term33 s) = (term33 s).
Proof. exact (fun_ext (fun x : real => @lem5236327 s x)). Qed.
Lemma lem5236329 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5236330 (s : real -> Prop) : (term34 s) = (term34 s).
Proof. exact (MK_COMB (@lem5236329) (@lem5236328 s)). Qed.
Lemma lem5236331 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5236332 (s : real -> Prop) : (term35 s) = (term35 s).
Proof. exact (MK_COMB (@lem5236331) (@lem5236330 s)). Qed.
Lemma lem5236333 (s : real -> Prop) : (term36 s) = (term36 s).
Proof. exact (MK_COMB (@lem5236332 s) (@lem5236322 s)). Qed.
Lemma lem5236338 (s : real -> Prop) (b : real) (x : real) : (term25 s b x) = (term25 s b x).
Proof. exact (eq_refl (term25 s b x)). Qed.
Lemma lem5236339 (s : real -> Prop) (b : real) : (term26 s b) = (term26 s b).
Proof. exact (fun_ext (fun x : real => @lem5236338 s b x)). Qed.
Lemma lem5236340 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5236341 (s : real -> Prop) (b : real) : (term27 s b) = (term27 s b).
Proof. exact (MK_COMB (@lem5236340) (@lem5236339 s b)). Qed.
Lemma lem5236342 (s : real -> Prop) : (term37 s) = (term37 s).
Proof. exact (fun_ext (fun b : real => @lem5236341 s b)). Qed.
Lemma lem5236343 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5236344 (s : real -> Prop) : (term38 s) = (term38 s).
Proof. exact (MK_COMB (@lem5236343) (@lem5236342 s)). Qed.
Lemma lem5236349 (s : real -> Prop) : (term39 s) = (term39 s).
Proof. exact (eq_refl (term39 s)). Qed.
Lemma lem5236350 (s : real -> Prop) : (term40 s) = (term40 s).
Proof. exact (MK_COMB (@lem5236349 s) (@lem5236344 s)). Qed.
Lemma lem5236351 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5236352 (s : real -> Prop) : (term41 s) = (term41 s).
Proof. exact (MK_COMB (@lem5236351) (@lem5236350 s)). Qed.
Lemma lem5236353 (s : real -> Prop) : (term42 s) = (term42 s).
Proof. exact (MK_COMB (@lem5236352 s) (@lem5236333 s)). Qed.
Lemma lem5236354 : term43 = term43.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5236353 s)). Qed.
Lemma lem5236355 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5236356 : term17 = term17.
Proof. exact (MK_COMB (@lem5236355) (@lem5236354)). Qed.
Lemma lem5236357 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5236358 : term16 = term16.
Proof. exact (MK_COMB (@lem5236357) (@lem5236356)). Qed.
Lemma lem5236359 (b : real) (s : real -> Prop) : (term24 b s) = (term24 b s).
Proof. exact (eq_refl (term24 b s)). Qed.
Lemma lem5236364 (s : real -> Prop) (b : real) (x : real) : (term25 s b x) = (term25 s b x).
Proof. exact (eq_refl (term25 s b x)). Qed.
Lemma lem5236365 (s : real -> Prop) (b : real) : (term26 s b) = (term26 s b).
Proof. exact (fun_ext (fun x : real => @lem5236364 s b x)). Qed.
Lemma lem5236366 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5236367 (s : real -> Prop) (b : real) : (term27 s b) = (term27 s b).
Proof. exact (MK_COMB (@lem5236366) (@lem5236365 s b)). Qed.
Lemma lem5236372 (s : real -> Prop) : (term39 s) = (term39 s).
Proof. exact (eq_refl (term39 s)). Qed.
Lemma lem5236373 (s : real -> Prop) (b : real) : (term44 s b) = (term44 s b).
Proof. exact (MK_COMB (@lem5236372 s) (@lem5236367 s b)). Qed.
Lemma lem5236374 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5236375 (s : real -> Prop) (b : real) : (term45 s b) = (term45 s b).
Proof. exact (MK_COMB (@lem5236374) (@lem5236373 s b)). Qed.
Lemma lem5236376 (b : real) (s : real -> Prop) : (term46 b s) = (term46 b s).
Proof. exact (MK_COMB (@lem5236375 s b) (@lem5236359 b s)). Qed.
Lemma lem5236377 (s : real -> Prop) : (term47 s) = (term47 s).
Proof. exact (fun_ext (fun b : real => @lem5236376 b s)). Qed.
Lemma lem5236378 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5236379 (s : real -> Prop) : (term8 s) = (term8 s).
Proof. exact (MK_COMB (@lem5236378) (@lem5236377 s)). Qed.
Lemma lem5236380 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5236381 (s : real -> Prop) : (term10 s) = (term10 s).
Proof. exact (MK_COMB (@lem5236380) (@lem5236379 s)). Qed.
Lemma lem5236382 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5236383 (s : real -> Prop) : (term18 s) = (term18 s).
Proof. exact (MK_COMB (@lem5236382) (@lem5236381 s)). Qed.
Lemma lem5236384 (s : real -> Prop) : (term19 s) = (term19 s).
Proof. exact (MK_COMB (@lem5236383 s) (@lem5236358)). Qed.
Lemma lem5236385 : term21 = term21.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5236384 s)). Qed.
Lemma lem5236386 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5236387 : term23 = term23.
Proof. exact (MK_COMB (@lem5236386) (@lem5236385)). Qed.
Lemma lem5236466 : term22 = term23.
Proof. exact (TRANS (@lem5236307) (@lem5236387)). Qed.
Lemma lem5236467 : term23 = term22.
Proof. exact (SYM (@lem5236466)). Qed.
Lemma lem5236468 (s : real -> Prop) (h1 : term10 s) : term10 s.
Proof. exact (h1). Qed.
Lemma lem5236469 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem5236477 (s : real -> Prop) (b : real) (x : real) : (term25 s b x) = (term48 s b x).
Proof. exact (@lem17265 (@IN real x s) (real_le b x)). Qed.
Lemma lem5236478 (s : real -> Prop) (b : real) : (term26 s b) = (term49 s b).
Proof. exact (fun_ext (fun x : real => @lem5236477 s b x)). Qed.
Lemma lem5236479 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5236480 (s : real -> Prop) (b : real) : (term27 s b) = (term50 s b).
Proof. exact (MK_COMB (@lem5236479) (@lem5236478 s b)). Qed.
Lemma lem5236482 (s : real -> Prop) : (term39 s) = (term39 s).
Proof. exact (eq_refl (term39 s)). Qed.
Lemma lem5236483 (s : real -> Prop) (b : real) : (term44 s b) = (term51 s b).
Proof. exact (MK_COMB (@lem5236482 s) (@lem5236480 s b)). Qed.
Lemma lem5236484 (b : real) (s : real -> Prop) : (term52 b s) = (term52 b s).
Proof. exact (eq_refl (term52 b s)). Qed.
Lemma lem5236485 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5236486 (s : real -> Prop) (b : real) : (term53 s b) = (term54 s b).
Proof. exact (MK_COMB (@lem5236485) (@lem5236483 s b)). Qed.
Lemma lem5236487 (b : real) (s : real -> Prop) : (term55 b s) = (term56 b s).
Proof. exact (MK_COMB (@lem5236486 s b) (@lem5236484 b s)). Qed.
Lemma lem5236488 (b : real) (s : real -> Prop) : (term57 b s) = (term55 b s).
Proof. exact (@lem17362 (term44 s b) (term24 b s)). Qed.
Lemma lem5236489 (b : real) (s : real -> Prop) : (term57 b s) = (term56 b s).
Proof. exact (TRANS (@lem5236488 b s) (@lem5236487 b s)). Qed.
Lemma lem5236490 (P : real -> Prop) : (term58 P) = (term59 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5236491 (s : real -> Prop) : (term10 s) = (term60 s).
Proof. exact (@lem5236490 (term47 s)). Qed.
Lemma lem5236492 (b : real) (s : real -> Prop) : (term61 s b) = (term46 b s).
Proof. exact (eq_refl (term61 s b)). Qed.
Lemma lem5236493 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5236494 (b : real) (s : real -> Prop) : (term62 s b) = (term57 b s).
Proof. exact (MK_COMB (@lem5236493) (@lem5236492 b s)). Qed.
Lemma lem5236495 (b : real) (s : real -> Prop) : (term62 s b) = (term56 b s).
Proof. exact (TRANS (@lem5236494 b s) (@lem5236489 b s)). Qed.
Lemma lem5236496 (s : real -> Prop) : (term63 s) = (term64 s).
Proof. exact (fun_ext (fun b : real => @lem5236495 b s)). Qed.
Lemma lem5236497 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5236498 (s : real -> Prop) : (term60 s) = (term65 s).
Proof. exact (MK_COMB (@lem5236497) (@lem5236496 s)). Qed.
Lemma lem5236599 (s : real -> Prop) : (term10 s) = (term65 s).
Proof. exact (TRANS (@lem5236491 s) (@lem5236498 s)). Qed.
Lemma lem5236600 (s : real -> Prop) (h1 : term10 s) : term65 s.
Proof. exact (EQ_MP (@lem5236599 s) (@lem5236468 s h1)). Qed.
Lemma lem5236603 (s : real -> Prop) : (term66 s) = (s = (@EMPTY real)).
Proof. exact (@lem16933 (s = (@EMPTY real))). Qed.
Lemma lem5236610 (s : real -> Prop) (b : real) (x : real) : (term67 s b x) = (term68 s b x).
Proof. exact (@lem17362 (@IN real x s) (real_le b x)). Qed.
Lemma lem5236611 (P : real -> Prop) : (term58 P) = (term59 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5236612 (s : real -> Prop) (b : real) : (term69 s b) = (term70 s b).
Proof. exact (@lem5236611 (term26 s b)). Qed.
Lemma lem5236613 (s : real -> Prop) (b : real) (x : real) : (term71 s b x) = (term25 s b x).
Proof. exact (eq_refl (term71 s b x)). Qed.
Lemma lem5236614 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5236615 (s : real -> Prop) (b : real) (x : real) : (term72 s b x) = (term67 s b x).
Proof. exact (MK_COMB (@lem5236614) (@lem5236613 s b x)). Qed.
Lemma lem5236616 (s : real -> Prop) (b : real) (x : real) : (term72 s b x) = (term68 s b x).
Proof. exact (TRANS (@lem5236615 s b x) (@lem5236610 s b x)). Qed.
Lemma lem5236617 (s : real -> Prop) (b : real) : (term73 s b) = (term74 s b).
Proof. exact (fun_ext (fun x : real => @lem5236616 s b x)). Qed.
Lemma lem5236618 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5236619 (s : real -> Prop) (b : real) : (term70 s b) = (term75 s b).
Proof. exact (MK_COMB (@lem5236618) (@lem5236617 s b)). Qed.
Lemma lem5236620 (s : real -> Prop) (b : real) : (term69 s b) = (term75 s b).
Proof. exact (TRANS (@lem5236612 s b) (@lem5236619 s b)). Qed.
Lemma lem5236621 (P : real -> Prop) : (term76 P) = (term77 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5236622 (s : real -> Prop) : (term78 s) = (term79 s).
Proof. exact (@lem5236621 (term37 s)). Qed.
Lemma lem5236623 (s : real -> Prop) (b : real) : (term80 s b) = (term27 s b).
Proof. exact (eq_refl (term80 s b)). Qed.
Lemma lem5236624 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5236625 (s : real -> Prop) (b : real) : (term81 s b) = (term69 s b).
Proof. exact (MK_COMB (@lem5236624) (@lem5236623 s b)). Qed.
Lemma lem5236626 (s : real -> Prop) (b : real) : (term81 s b) = (term75 s b).
Proof. exact (TRANS (@lem5236625 s b) (@lem5236620 s b)). Qed.
Lemma lem5236627 (s : real -> Prop) : (term82 s) = (term83 s).
Proof. exact (fun_ext (fun b : real => @lem5236626 s b)). Qed.
Lemma lem5236628 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5236629 (s : real -> Prop) : (term79 s) = (term84 s).
Proof. exact (MK_COMB (@lem5236628) (@lem5236627 s)). Qed.
Lemma lem5236630 (s : real -> Prop) : (term78 s) = (term84 s).
Proof. exact (TRANS (@lem5236622 s) (@lem5236629 s)). Qed.
Lemma lem5236631 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5236632 (s : real -> Prop) : (term85 s) = (term86 s).
Proof. exact (MK_COMB (@lem5236631) (@lem5236603 s)). Qed.
Lemma lem5236633 (s : real -> Prop) : (term87 s) = (term88 s).
Proof. exact (MK_COMB (@lem5236632 s) (@lem5236630 s)). Qed.
Lemma lem5236634 (s : real -> Prop) : (term89 s) = (term87 s).
Proof. exact (@lem17045 (term90 s) (term38 s)). Qed.
Lemma lem5236635 (s : real -> Prop) : (term89 s) = (term88 s).
Proof. exact (TRANS (@lem5236634 s) (@lem5236633 s)). Qed.
Lemma lem5236642 (s : real -> Prop) (x : real) : (term32 s x) = (term91 s x).
Proof. exact (@lem17265 (@IN real x s) (term92 s x)). Qed.
Lemma lem5236643 (s : real -> Prop) : (term33 s) = (term93 s).
Proof. exact (fun_ext (fun x : real => @lem5236642 s x)). Qed.
Lemma lem5236644 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5236645 (s : real -> Prop) : (term34 s) = (term94 s).
Proof. exact (MK_COMB (@lem5236644) (@lem5236643 s)). Qed.
Lemma lem5236652 (s : real -> Prop) (b : real) (x : real) : (term67 s b x) = (term68 s b x).
Proof. exact (@lem17362 (@IN real x s) (real_le b x)). Qed.
Lemma lem5236653 (P : real -> Prop) : (term58 P) = (term59 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5236654 (s : real -> Prop) (b : real) : (term69 s b) = (term70 s b).
Proof. exact (@lem5236653 (term26 s b)). Qed.
Lemma lem5236655 (s : real -> Prop) (b : real) (x : real) : (term71 s b x) = (term25 s b x).
Proof. exact (eq_refl (term71 s b x)). Qed.
Lemma lem5236656 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5236657 (s : real -> Prop) (b : real) (x : real) : (term72 s b x) = (term67 s b x).
Proof. exact (MK_COMB (@lem5236656) (@lem5236655 s b x)). Qed.
Lemma lem5236658 (s : real -> Prop) (b : real) (x : real) : (term72 s b x) = (term68 s b x).
Proof. exact (TRANS (@lem5236657 s b x) (@lem5236652 s b x)). Qed.
Lemma lem5236659 (s : real -> Prop) (b : real) : (term73 s b) = (term74 s b).
Proof. exact (fun_ext (fun x : real => @lem5236658 s b x)). Qed.
Lemma lem5236660 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5236661 (s : real -> Prop) (b : real) : (term70 s b) = (term75 s b).
Proof. exact (MK_COMB (@lem5236660) (@lem5236659 s b)). Qed.
Lemma lem5236662 (s : real -> Prop) (b : real) : (term69 s b) = (term75 s b).
Proof. exact (TRANS (@lem5236654 s b) (@lem5236661 s b)). Qed.
Lemma lem5236663 (b : real) (s : real -> Prop) : (term24 b s) = (term24 b s).
Proof. exact (eq_refl (term24 b s)). Qed.
Lemma lem5236664 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5236665 (s : real -> Prop) (b : real) : (term95 s b) = (term96 s b).
Proof. exact (MK_COMB (@lem5236664) (@lem5236662 s b)). Qed.
Lemma lem5236666 (b : real) (s : real -> Prop) : (term97 b s) = (term98 b s).
Proof. exact (MK_COMB (@lem5236665 s b) (@lem5236663 b s)). Qed.
Lemma lem5236667 (b : real) (s : real -> Prop) : (term29 b s) = (term97 b s).
Proof. exact (@lem17265 (term27 s b) (term24 b s)). Qed.
Lemma lem5236668 (b : real) (s : real -> Prop) : (term29 b s) = (term98 b s).
Proof. exact (TRANS (@lem5236667 b s) (@lem5236666 b s)). Qed.
Lemma lem5236669 (s : real -> Prop) : (term30 s) = (term99 s).
Proof. exact (fun_ext (fun b : real => @lem5236668 b s)). Qed.
Lemma lem5236670 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5236671 (s : real -> Prop) : (term31 s) = (term100 s).
Proof. exact (MK_COMB (@lem5236670) (@lem5236669 s)). Qed.
Lemma lem5236672 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5236673 (s : real -> Prop) : (term35 s) = (term101 s).
Proof. exact (MK_COMB (@lem5236672) (@lem5236645 s)). Qed.
Lemma lem5236674 (s : real -> Prop) : (term36 s) = (term102 s).
Proof. exact (MK_COMB (@lem5236673 s) (@lem5236671 s)). Qed.
Lemma lem5236675 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5236676 (s : real -> Prop) : (term103 s) = (term104 s).
Proof. exact (MK_COMB (@lem5236675) (@lem5236635 s)). Qed.
Lemma lem5236677 (s : real -> Prop) : (term105 s) = (term106 s).
Proof. exact (MK_COMB (@lem5236676 s) (@lem5236674 s)). Qed.
Lemma lem5236678 (s : real -> Prop) : (term42 s) = (term105 s).
Proof. exact (@lem17265 (term40 s) (term36 s)). Qed.
Lemma lem5236679 (s : real -> Prop) : (term42 s) = (term106 s).
Proof. exact (TRANS (@lem5236678 s) (@lem5236677 s)). Qed.
Lemma lem5236680 : term43 = term107.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5236679 s)). Qed.
Lemma lem5236681 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5236682 : term17 = term108.
Proof. exact (MK_COMB (@lem5236681) (@lem5236680)). Qed.
Lemma lem5236929 {A B : Type'} (P : type1413 A B) : (term109 A B P) = (term110 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5236930 (P : type1626) : (term111 P) = (term112 P).
Proof. exact (@lem5236929 real real P). Qed.
Lemma lem5236931 (s : real -> Prop) : (term113 s) = (term114 s).
Proof. exact (@lem5236930 (term115 s)). Qed.
Lemma lem5236932 (s : real -> Prop) (b : real) : (term116 s b) = (term74 s b).
Proof. exact (eq_refl (term116 s b)). Qed.
Lemma lem5236933 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5236934 (s : real -> Prop) (b : real) (x : real) : (term117 s b x) = (term118 s b x).
Proof. exact (MK_COMB (@lem5236932 s b) (@lem5236933 x)). Qed.
Lemma lem5236935 (s : real -> Prop) (b : real) (x : real) : (term118 s b x) = (term68 s b x).
Proof. exact (eq_refl (term118 s b x)). Qed.
Lemma lem5236936 (s : real -> Prop) (b : real) (x : real) : (term117 s b x) = (term68 s b x).
Proof. exact (TRANS (@lem5236934 s b x) (@lem5236935 s b x)). Qed.
Lemma lem5236937 (s : real -> Prop) (b : real) : (term119 s b) = (term74 s b).
Proof. exact (fun_ext (fun x : real => @lem5236936 s b x)). Qed.
Lemma lem5236938 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5236939 (s : real -> Prop) (b : real) : (term120 s b) = (term75 s b).
Proof. exact (MK_COMB (@lem5236938) (@lem5236937 s b)). Qed.
Lemma lem5236940 (s : real -> Prop) : (term121 s) = (term83 s).
Proof. exact (fun_ext (fun b : real => @lem5236939 s b)). Qed.
Lemma lem5236941 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5236942 (s : real -> Prop) : (term113 s) = (term84 s).
Proof. exact (MK_COMB (@lem5236941) (@lem5236940 s)). Qed.
Lemma lem5236943 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5236944 (s : real -> Prop) : (term122 s) = (term123 s).
Proof. exact (MK_COMB (@lem5236943) (@lem5236942 s)). Qed.
Lemma lem5236945 (s : real -> Prop) (b : real) : (term116 s b) = (term74 s b).
Proof. exact (eq_refl (term116 s b)). Qed.
Lemma lem5236946 (x : real -> real) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem5236947 (s : real -> Prop) (x : real -> real) (b : real) : (term124 s x b) = (term125 s x b).
Proof. exact (MK_COMB (@lem5236945 s b) (@lem5236946 x b)). Qed.
Lemma lem5236948 (s : real -> Prop) (x : real -> real) (b : real) : (term125 s x b) = (term126 s x b).
Proof. exact (eq_refl (term125 s x b)). Qed.
Lemma lem5236949 (s : real -> Prop) (x : real -> real) (b : real) : (term124 s x b) = (term126 s x b).
Proof. exact (TRANS (@lem5236947 s x b) (@lem5236948 s x b)). Qed.
Lemma lem5236950 (s : real -> Prop) (x : real -> real) : (term127 s x) = (term128 s x).
Proof. exact (fun_ext (fun b : real => @lem5236949 s x b)). Qed.
Lemma lem5236951 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5236952 (s : real -> Prop) (x : real -> real) : (term129 s x) = (term130 s x).
Proof. exact (MK_COMB (@lem5236951) (@lem5236950 s x)). Qed.
Lemma lem5236953 (s : real -> Prop) : (term131 s) = (term132 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5236952 s x)). Qed.
Lemma lem5236954 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5236955 (s : real -> Prop) : (term114 s) = (term133 s).
Proof. exact (MK_COMB (@lem5236954) (@lem5236953 s)). Qed.
Lemma lem5236956 (s : real -> Prop) : ((term113 s) = (term114 s)) = ((term84 s) = (term133 s)).
Proof. exact (MK_COMB (@lem5236944 s) (@lem5236955 s)). Qed.
Lemma lem5236957 (s : real -> Prop) : (term84 s) = (term133 s).
Proof. exact (EQ_MP (@lem5236956 s) (@lem5236931 s)). Qed.
Lemma lem5236958 (s : real -> Prop) : (term86 s) = (term86 s).
Proof. exact (eq_refl (term86 s)). Qed.
Lemma lem5236959 (s : real -> Prop) : (term88 s) = (term134 s).
Proof. exact (MK_COMB (@lem5236958 s) (@lem5236957 s)). Qed.
Lemma lem5236961 {A : Type'} (P : Prop) (Q : A -> Prop) : (term135 A P Q) = (term136 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5236962 (P : Prop) (Q : type1028) : (term137 P Q) = (term138 P Q).
Proof. exact (@lem5236961 (real -> real) P Q). Qed.
Lemma lem5236963 (s : real -> Prop) : (term139 s) = (term140 s).
Proof. exact (@lem5236962 (s = (@EMPTY real)) (term132 s)). Qed.
Lemma lem5236964 (s : real -> Prop) (x : real -> real) : (term141 s x) = (term130 s x).
Proof. exact (eq_refl (term141 s x)). Qed.
Lemma lem5236965 (s : real -> Prop) : (term142 s) = (term132 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5236964 s x)). Qed.
Lemma lem5236966 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5236967 (s : real -> Prop) : (term143 s) = (term133 s).
Proof. exact (MK_COMB (@lem5236966) (@lem5236965 s)). Qed.
Lemma lem5236968 (s : real -> Prop) : (term86 s) = (term86 s).
Proof. exact (eq_refl (term86 s)). Qed.
Lemma lem5236969 (s : real -> Prop) : (term139 s) = (term134 s).
Proof. exact (MK_COMB (@lem5236968 s) (@lem5236967 s)). Qed.
Lemma lem5236970 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5236971 (s : real -> Prop) : (term144 s) = (term145 s).
Proof. exact (MK_COMB (@lem5236970) (@lem5236969 s)). Qed.
Lemma lem5236972 (s : real -> Prop) (x : real -> real) : (term141 s x) = (term130 s x).
Proof. exact (eq_refl (term141 s x)). Qed.
Lemma lem5236973 (s : real -> Prop) : (term86 s) = (term86 s).
Proof. exact (eq_refl (term86 s)). Qed.
Lemma lem5236974 (s : real -> Prop) (x : real -> real) : (term146 s x) = (term147 s x).
Proof. exact (MK_COMB (@lem5236973 s) (@lem5236972 s x)). Qed.
Lemma lem5236975 (s : real -> Prop) : (term148 s) = (term149 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5236974 s x)). Qed.
Lemma lem5236976 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5236977 (s : real -> Prop) : (term140 s) = (term150 s).
Proof. exact (MK_COMB (@lem5236976) (@lem5236975 s)). Qed.
Lemma lem5236978 (s : real -> Prop) : ((term139 s) = (term140 s)) = ((term134 s) = (term150 s)).
Proof. exact (MK_COMB (@lem5236971 s) (@lem5236977 s)). Qed.
Lemma lem5236979 (s : real -> Prop) : (term134 s) = (term150 s).
Proof. exact (EQ_MP (@lem5236978 s) (@lem5236963 s)). Qed.
Lemma lem5236980 (s : real -> Prop) : (term88 s) = (term150 s).
Proof. exact (TRANS (@lem5236959 s) (@lem5236979 s)). Qed.
Lemma lem5236981 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5236982 (s : real -> Prop) : (term104 s) = (term151 s).
Proof. exact (MK_COMB (@lem5236981) (@lem5236980 s)). Qed.
Lemma lem5236984 {A : Type'} (P : A -> Prop) (Q : Prop) : (term152 A P Q) = (term153 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5236985 (P : real -> Prop) (Q : Prop) : (term154 P Q) = (term155 P Q).
Proof. exact (@lem5236984 real P Q). Qed.
Lemma lem5236986 (b : real) (s : real -> Prop) : (term156 b s) = (term157 b s).
Proof. exact (@lem5236985 (term74 s b) (term24 b s)). Qed.
Lemma lem5236987 (s : real -> Prop) (b : real) (x : real) : (term118 s b x) = (term68 s b x).
Proof. exact (eq_refl (term118 s b x)). Qed.
Lemma lem5236988 (s : real -> Prop) (b : real) : (term158 s b) = (term74 s b).
Proof. exact (fun_ext (fun x : real => @lem5236987 s b x)). Qed.
Lemma lem5236989 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5236990 (s : real -> Prop) (b : real) : (term159 s b) = (term75 s b).
Proof. exact (MK_COMB (@lem5236989) (@lem5236988 s b)). Qed.
Lemma lem5236991 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5236992 (s : real -> Prop) (b : real) : (term160 s b) = (term96 s b).
Proof. exact (MK_COMB (@lem5236991) (@lem5236990 s b)). Qed.
Lemma lem5236993 (b : real) (s : real -> Prop) : (term24 b s) = (term24 b s).
Proof. exact (eq_refl (term24 b s)). Qed.
Lemma lem5236994 (b : real) (s : real -> Prop) : (term156 b s) = (term98 b s).
Proof. exact (MK_COMB (@lem5236992 s b) (@lem5236993 b s)). Qed.
Lemma lem5236995 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5236996 (b : real) (s : real -> Prop) : (term161 b s) = (term162 b s).
Proof. exact (MK_COMB (@lem5236995) (@lem5236994 b s)). Qed.
Lemma lem5236997 (s : real -> Prop) (b : real) (x : real) : (term118 s b x) = (term68 s b x).
Proof. exact (eq_refl (term118 s b x)). Qed.
Lemma lem5236998 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5236999 (s : real -> Prop) (b : real) (x : real) : (term163 s b x) = (term164 s b x).
Proof. exact (MK_COMB (@lem5236998) (@lem5236997 s b x)). Qed.
Lemma lem5237000 (b : real) (s : real -> Prop) : (term24 b s) = (term24 b s).
Proof. exact (eq_refl (term24 b s)). Qed.
Lemma lem5237001 (x : real) (b : real) (s : real -> Prop) : (term165 x b s) = (term166 x b s).
Proof. exact (MK_COMB (@lem5236999 s b x) (@lem5237000 b s)). Qed.
Lemma lem5237002 (b : real) (s : real -> Prop) : (term167 b s) = (term168 b s).
Proof. exact (fun_ext (fun x : real => @lem5237001 x b s)). Qed.
Lemma lem5237003 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5237004 (b : real) (s : real -> Prop) : (term157 b s) = (term169 b s).
Proof. exact (MK_COMB (@lem5237003) (@lem5237002 b s)). Qed.
Lemma lem5237005 (b : real) (s : real -> Prop) : ((term156 b s) = (term157 b s)) = ((term98 b s) = (term169 b s)).
Proof. exact (MK_COMB (@lem5236996 b s) (@lem5237004 b s)). Qed.
Lemma lem5237006 (b : real) (s : real -> Prop) : (term98 b s) = (term169 b s).
Proof. exact (EQ_MP (@lem5237005 b s) (@lem5236986 b s)). Qed.
Lemma lem5237007 (s : real -> Prop) : (term99 s) = (term170 s).
Proof. exact (fun_ext (fun b : real => @lem5237006 b s)). Qed.
Lemma lem5237008 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5237009 (s : real -> Prop) : (term100 s) = (term171 s).
Proof. exact (MK_COMB (@lem5237008) (@lem5237007 s)). Qed.
Lemma lem5237011 {A B : Type'} (P : type1413 A B) : (term109 A B P) = (term110 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5237012 (P : type1626) : (term111 P) = (term112 P).
Proof. exact (@lem5237011 real real P). Qed.
Lemma lem5237013 (s : real -> Prop) : (term172 s) = (term173 s).
Proof. exact (@lem5237012 (term174 s)). Qed.
Lemma lem5237014 (b : real) (s : real -> Prop) : (term175 s b) = (term168 b s).
Proof. exact (eq_refl (term175 s b)). Qed.
Lemma lem5237015 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5237016 (b : real) (s : real -> Prop) (x : real) : (term176 s b x) = (term177 b s x).
Proof. exact (MK_COMB (@lem5237014 b s) (@lem5237015 x)). Qed.
Lemma lem5237017 (x : real) (b : real) (s : real -> Prop) : (term177 b s x) = (term166 x b s).
Proof. exact (eq_refl (term177 b s x)). Qed.
Lemma lem5237018 (x : real) (b : real) (s : real -> Prop) : (term176 s b x) = (term166 x b s).
Proof. exact (TRANS (@lem5237016 b s x) (@lem5237017 x b s)). Qed.
Lemma lem5237019 (b : real) (s : real -> Prop) : (term178 s b) = (term168 b s).
Proof. exact (fun_ext (fun x : real => @lem5237018 x b s)). Qed.
Lemma lem5237020 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5237021 (b : real) (s : real -> Prop) : (term179 s b) = (term169 b s).
Proof. exact (MK_COMB (@lem5237020) (@lem5237019 b s)). Qed.
Lemma lem5237022 (s : real -> Prop) : (term180 s) = (term170 s).
Proof. exact (fun_ext (fun b : real => @lem5237021 b s)). Qed.
Lemma lem5237023 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5237024 (s : real -> Prop) : (term172 s) = (term171 s).
Proof. exact (MK_COMB (@lem5237023) (@lem5237022 s)). Qed.
Lemma lem5237025 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5237026 (s : real -> Prop) : (term181 s) = (term182 s).
Proof. exact (MK_COMB (@lem5237025) (@lem5237024 s)). Qed.
Lemma lem5237027 (b : real) (s : real -> Prop) : (term175 s b) = (term168 b s).
Proof. exact (eq_refl (term175 s b)). Qed.
Lemma lem5237028 (x : real -> real) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem5237029 (s : real -> Prop) (x : real -> real) (b : real) : (term183 s x b) = (term184 s x b).
Proof. exact (MK_COMB (@lem5237027 b s) (@lem5237028 x b)). Qed.
Lemma lem5237030 (x : real -> real) (b : real) (s : real -> Prop) : (term184 s x b) = (term185 x b s).
Proof. exact (eq_refl (term184 s x b)). Qed.
Lemma lem5237031 (x : real -> real) (b : real) (s : real -> Prop) : (term183 s x b) = (term185 x b s).
Proof. exact (TRANS (@lem5237029 s x b) (@lem5237030 x b s)). Qed.
Lemma lem5237032 (x : real -> real) (s : real -> Prop) : (term186 s x) = (term187 x s).
Proof. exact (fun_ext (fun b : real => @lem5237031 x b s)). Qed.
Lemma lem5237033 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5237034 (x : real -> real) (s : real -> Prop) : (term188 s x) = (term189 x s).
Proof. exact (MK_COMB (@lem5237033) (@lem5237032 x s)). Qed.
Lemma lem5237035 (s : real -> Prop) : (term190 s) = (term191 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5237034 x s)). Qed.
Lemma lem5237036 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5237037 (s : real -> Prop) : (term173 s) = (term192 s).
Proof. exact (MK_COMB (@lem5237036) (@lem5237035 s)). Qed.
Lemma lem5237038 (s : real -> Prop) : ((term172 s) = (term173 s)) = ((term171 s) = (term192 s)).
Proof. exact (MK_COMB (@lem5237026 s) (@lem5237037 s)). Qed.
Lemma lem5237039 (s : real -> Prop) : (term171 s) = (term192 s).
Proof. exact (EQ_MP (@lem5237038 s) (@lem5237013 s)). Qed.
Lemma lem5237040 (s : real -> Prop) : (term100 s) = (term192 s).
Proof. exact (TRANS (@lem5237009 s) (@lem5237039 s)). Qed.
Lemma lem5237041 (s : real -> Prop) : (term101 s) = (term101 s).
Proof. exact (eq_refl (term101 s)). Qed.
Lemma lem5237042 (s : real -> Prop) : (term102 s) = (term193 s).
Proof. exact (MK_COMB (@lem5237041 s) (@lem5237040 s)). Qed.
Lemma lem5237044 {A : Type'} (P : Prop) (Q : A -> Prop) : (term194 A P Q) = (term195 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5237045 (P : Prop) (Q : type1028) : (term196 P Q) = (term197 P Q).
Proof. exact (@lem5237044 (real -> real) P Q). Qed.
Lemma lem5237046 (s : real -> Prop) : (term198 s) = (term199 s).
Proof. exact (@lem5237045 (term94 s) (term191 s)). Qed.
Lemma lem5237047 (x : real -> real) (s : real -> Prop) : (term200 s x) = (term189 x s).
Proof. exact (eq_refl (term200 s x)). Qed.
Lemma lem5237048 (s : real -> Prop) : (term201 s) = (term191 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5237047 x s)). Qed.
Lemma lem5237049 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5237050 (s : real -> Prop) : (term202 s) = (term192 s).
Proof. exact (MK_COMB (@lem5237049) (@lem5237048 s)). Qed.
Lemma lem5237051 (s : real -> Prop) : (term101 s) = (term101 s).
Proof. exact (eq_refl (term101 s)). Qed.
Lemma lem5237052 (s : real -> Prop) : (term198 s) = (term193 s).
Proof. exact (MK_COMB (@lem5237051 s) (@lem5237050 s)). Qed.
Lemma lem5237053 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5237054 (s : real -> Prop) : (term203 s) = (term204 s).
Proof. exact (MK_COMB (@lem5237053) (@lem5237052 s)). Qed.
Lemma lem5237055 (x : real -> real) (s : real -> Prop) : (term200 s x) = (term189 x s).
Proof. exact (eq_refl (term200 s x)). Qed.
Lemma lem5237056 (s : real -> Prop) : (term101 s) = (term101 s).
Proof. exact (eq_refl (term101 s)). Qed.
Lemma lem5237057 (x : real -> real) (s : real -> Prop) : (term205 s x) = (term206 x s).
Proof. exact (MK_COMB (@lem5237056 s) (@lem5237055 x s)). Qed.
Lemma lem5237058 (s : real -> Prop) : (term207 s) = (term208 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5237057 x s)). Qed.
Lemma lem5237059 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5237060 (s : real -> Prop) : (term199 s) = (term209 s).
Proof. exact (MK_COMB (@lem5237059) (@lem5237058 s)). Qed.
Lemma lem5237061 (s : real -> Prop) : ((term198 s) = (term199 s)) = ((term193 s) = (term209 s)).
Proof. exact (MK_COMB (@lem5237054 s) (@lem5237060 s)). Qed.
Lemma lem5237062 (s : real -> Prop) : (term193 s) = (term209 s).
Proof. exact (EQ_MP (@lem5237061 s) (@lem5237046 s)). Qed.
Lemma lem5237063 (s : real -> Prop) : (term102 s) = (term209 s).
Proof. exact (TRANS (@lem5237042 s) (@lem5237062 s)). Qed.
Lemma lem5237064 (s : real -> Prop) : (term106 s) = (term210 s).
Proof. exact (MK_COMB (@lem5236982 s) (@lem5237063 s)). Qed.
Lemma lem5237066 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term211 A P Q) = (term212 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5237067 (P : type1028) (Q : type1028) : (term213 P Q) = (term214 P Q).
Proof. exact (@lem5237066 (real -> real) P Q). Qed.
Lemma lem5237068 (s : real -> Prop) : (term215 s) = (term216 s).
Proof. exact (@lem5237067 (term149 s) (term208 s)). Qed.
Lemma lem5237069 (s : real -> Prop) (x : real -> real) : (term217 s x) = (term147 s x).
Proof. exact (eq_refl (term217 s x)). Qed.
Lemma lem5237070 (s : real -> Prop) : (term218 s) = (term149 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5237069 s x)). Qed.
Lemma lem5237071 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5237072 (s : real -> Prop) : (term219 s) = (term150 s).
Proof. exact (MK_COMB (@lem5237071) (@lem5237070 s)). Qed.
Lemma lem5237073 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5237074 (s : real -> Prop) : (term220 s) = (term151 s).
Proof. exact (MK_COMB (@lem5237073) (@lem5237072 s)). Qed.
Lemma lem5237075 (x : real -> real) (s : real -> Prop) : (term221 s x) = (term206 x s).
Proof. exact (eq_refl (term221 s x)). Qed.
Lemma lem5237076 (s : real -> Prop) : (term222 s) = (term208 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5237075 x s)). Qed.
Lemma lem5237077 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5237078 (s : real -> Prop) : (term223 s) = (term209 s).
Proof. exact (MK_COMB (@lem5237077) (@lem5237076 s)). Qed.
Lemma lem5237079 (s : real -> Prop) : (term215 s) = (term210 s).
Proof. exact (MK_COMB (@lem5237074 s) (@lem5237078 s)). Qed.
Lemma lem5237080 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5237081 (s : real -> Prop) : (term224 s) = (term225 s).
Proof. exact (MK_COMB (@lem5237080) (@lem5237079 s)). Qed.
Lemma lem5237082 (s : real -> Prop) (x : real -> real) : (term217 s x) = (term147 s x).
Proof. exact (eq_refl (term217 s x)). Qed.
Lemma lem5237083 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5237084 (s : real -> Prop) (x : real -> real) : (term226 s x) = (term227 s x).
Proof. exact (MK_COMB (@lem5237083) (@lem5237082 s x)). Qed.
Lemma lem5237085 (x : real -> real) (s : real -> Prop) : (term221 s x) = (term206 x s).
Proof. exact (eq_refl (term221 s x)). Qed.
Lemma lem5237086 (x : real -> real) (s : real -> Prop) : (term228 s x) = (term229 x s).
Proof. exact (MK_COMB (@lem5237084 s x) (@lem5237085 x s)). Qed.
Lemma lem5237087 (s : real -> Prop) : (term230 s) = (term231 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5237086 x s)). Qed.
Lemma lem5237088 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5237089 (s : real -> Prop) : (term216 s) = (term232 s).
Proof. exact (MK_COMB (@lem5237088) (@lem5237087 s)). Qed.
Lemma lem5237090 (s : real -> Prop) : ((term215 s) = (term216 s)) = ((term210 s) = (term232 s)).
Proof. exact (MK_COMB (@lem5237081 s) (@lem5237089 s)). Qed.
Lemma lem5237091 (s : real -> Prop) : (term210 s) = (term232 s).
Proof. exact (EQ_MP (@lem5237090 s) (@lem5237068 s)). Qed.
Lemma lem5237092 (s : real -> Prop) : (term106 s) = (term232 s).
Proof. exact (TRANS (@lem5237064 s) (@lem5237091 s)). Qed.
Lemma lem5237093 : term107 = term233.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5237092 s)). Qed.
Lemma lem5237094 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5237095 : term108 = term234.
Proof. exact (MK_COMB (@lem5237094) (@lem5237093)). Qed.
Lemma lem5237097 {A B : Type'} (P : type1413 A B) : (term109 A B P) = (term110 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5237098 (P : type1017) : (term235 P) = (term236 P).
Proof. exact (@lem5237097 (real -> Prop) (real -> real) P). Qed.
Lemma lem5237099 : term237 = term238.
Proof. exact (@lem5237098 term239). Qed.
Lemma lem5237100 (s : real -> Prop) : (term240 s) = (term231 s).
Proof. exact (eq_refl (term240 s)). Qed.
Lemma lem5237101 (x : real -> real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5237102 (s : real -> Prop) (x : real -> real) : (term241 s x) = (term242 s x).
Proof. exact (MK_COMB (@lem5237100 s) (@lem5237101 x)). Qed.
Lemma lem5237103 (x : real -> real) (s : real -> Prop) : (term242 s x) = (term229 x s).
Proof. exact (eq_refl (term242 s x)). Qed.
Lemma lem5237104 (x : real -> real) (s : real -> Prop) : (term241 s x) = (term229 x s).
Proof. exact (TRANS (@lem5237102 s x) (@lem5237103 x s)). Qed.
Lemma lem5237105 (s : real -> Prop) : (term243 s) = (term231 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5237104 x s)). Qed.
Lemma lem5237106 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5237107 (s : real -> Prop) : (term244 s) = (term232 s).
Proof. exact (MK_COMB (@lem5237106) (@lem5237105 s)). Qed.
Lemma lem5237108 : term245 = term233.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5237107 s)). Qed.
Lemma lem5237109 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5237110 : term237 = term234.
Proof. exact (MK_COMB (@lem5237109) (@lem5237108)). Qed.
Lemma lem5237111 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5237112 : term246 = term247.
Proof. exact (MK_COMB (@lem5237111) (@lem5237110)). Qed.
Lemma lem5237113 (s : real -> Prop) : (term240 s) = (term231 s).
Proof. exact (eq_refl (term240 s)). Qed.
Lemma lem5237114 (x : type1021) (s : real -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem5237115 (x : type1021) (s : real -> Prop) : (term248 x s) = (term249 x s).
Proof. exact (MK_COMB (@lem5237113 s) (@lem5237114 x s)). Qed.
Lemma lem5237116 (x : type1021) (s : real -> Prop) : (term249 x s) = (term250 x s).
Proof. exact (eq_refl (term249 x s)). Qed.
Lemma lem5237117 (x : type1021) (s : real -> Prop) : (term248 x s) = (term250 x s).
Proof. exact (TRANS (@lem5237115 x s) (@lem5237116 x s)). Qed.
Lemma lem5237118 (x : type1021) : (term251 x) = (term252 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5237117 x s)). Qed.
Lemma lem5237119 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5237120 (x : type1021) : (term253 x) = (term254 x).
Proof. exact (MK_COMB (@lem5237119) (@lem5237118 x)). Qed.
Lemma lem5237121 : term255 = term256.
Proof. exact (fun_ext (fun x : type1021 => @lem5237120 x)). Qed.
Lemma lem5237122 : (@ex ((real -> Prop) -> real -> real)) = (@ex ((real -> Prop) -> real -> real)).
Proof. exact (eq_refl (@ex ((real -> Prop) -> real -> real))). Qed.
Lemma lem5237123 : term238 = term257.
Proof. exact (MK_COMB (@lem5237122) (@lem5237121)). Qed.
Lemma lem5237124 : (term237 = term238) = (term234 = term257).
Proof. exact (MK_COMB (@lem5237112) (@lem5237123)). Qed.
Lemma lem5237125 : term234 = term257.
Proof. exact (EQ_MP (@lem5237124) (@lem5237099)). Qed.
Lemma lem5237127 : term108 = term257.
Proof. exact (TRANS (@lem5237095) (@lem5237125)). Qed.
Lemma lem5237128 : term17 = term257.
Proof. exact (TRANS (@lem5236682) (@lem5237127)). Qed.
Lemma lem5237129 (h1 : term17) : term257.
Proof. exact (EQ_MP (@lem5237128) (@lem5236469 h1)). Qed.
Lemma lem5237130 (x : type1021) (h1 : term254 x) : term254 x.
Proof. exact (h1). Qed.
Lemma lem5237131 (b : real) (s : real -> Prop) (h1 : term56 b s) : term56 b s.
Proof. exact (h1). Qed.
Lemma lem5237164 (x : type1021) (b : real) (s : real -> Prop) : (term258 x b s) = (term258 x b s).
Proof. exact (eq_refl (term258 x b s)). Qed.
Lemma lem5237165 (x : type1021) (s : real -> Prop) : (term259 x s) = (term259 x s).
Proof. exact (fun_ext (fun b : real => @lem5237164 x b s)). Qed.
Lemma lem5237166 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5237167 (x : type1021) (s : real -> Prop) : (term260 x s) = (term260 x s).
Proof. exact (MK_COMB (@lem5237166) (@lem5237165 x s)). Qed.
Lemma lem5237184 (s : real -> Prop) (x : real) : (term91 s x) = (term91 s x).
Proof. exact (eq_refl (term91 s x)). Qed.
Lemma lem5237185 (s : real -> Prop) : (term93 s) = (term93 s).
Proof. exact (fun_ext (fun x : real => @lem5237184 s x)). Qed.
Lemma lem5237186 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5237187 (s : real -> Prop) : (term94 s) = (term94 s).
Proof. exact (MK_COMB (@lem5237186) (@lem5237185 s)). Qed.
Lemma lem5237188 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5237189 (s : real -> Prop) : (term101 s) = (term101 s).
Proof. exact (MK_COMB (@lem5237188) (@lem5237187 s)). Qed.
Lemma lem5237190 (x : type1021) (s : real -> Prop) : (term261 x s) = (term261 x s).
Proof. exact (MK_COMB (@lem5237189 s) (@lem5237167 x s)). Qed.
Lemma lem5237213 (x : type1021) (s : real -> Prop) (b : real) : (term262 x s b) = (term262 x s b).
Proof. exact (eq_refl (term262 x s b)). Qed.
Lemma lem5237214 (x : type1021) (s : real -> Prop) : (term263 x s) = (term263 x s).
Proof. exact (fun_ext (fun b : real => @lem5237213 x s b)). Qed.
Lemma lem5237215 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5237216 (x : type1021) (s : real -> Prop) : (term264 x s) = (term264 x s).
Proof. exact (MK_COMB (@lem5237215) (@lem5237214 x s)). Qed.
Lemma lem5237223 (s : real -> Prop) : (term86 s) = (term86 s).
Proof. exact (eq_refl (term86 s)). Qed.
Lemma lem5237224 (x : type1021) (s : real -> Prop) : (term265 x s) = (term265 x s).
Proof. exact (MK_COMB (@lem5237223 s) (@lem5237216 x s)). Qed.
Lemma lem5237225 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5237226 (x : type1021) (s : real -> Prop) : (term266 x s) = (term266 x s).
Proof. exact (MK_COMB (@lem5237225) (@lem5237224 x s)). Qed.
Lemma lem5237227 (x : type1021) (s : real -> Prop) : (term250 x s) = (term250 x s).
Proof. exact (MK_COMB (@lem5237226 x s) (@lem5237190 x s)). Qed.
Lemma lem5237228 (x : type1021) : (term252 x) = (term252 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5237227 x s)). Qed.
Lemma lem5237229 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5237230 (x : type1021) : (term254 x) = (term254 x).
Proof. exact (MK_COMB (@lem5237229) (@lem5237228 x)). Qed.
Lemma lem5237231 (x : type1021) (h1 : term254 x) : term254 x.
Proof. exact (EQ_MP (@lem5237230 x) (@lem5237130 x h1)). Qed.
Lemma lem5237240 (b : real) (s : real -> Prop) : (term52 b s) = (term52 b s).
Proof. exact (eq_refl (term52 b s)). Qed.
Lemma lem5237255 (s : real -> Prop) (b : real) (x : real) : (term48 s b x) = (term48 s b x).
Proof. exact (eq_refl (term48 s b x)). Qed.
Lemma lem5237256 (s : real -> Prop) (b : real) : (term49 s b) = (term49 s b).
Proof. exact (fun_ext (fun x : real => @lem5237255 s b x)). Qed.
Lemma lem5237257 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5237258 (s : real -> Prop) (b : real) : (term50 s b) = (term50 s b).
Proof. exact (MK_COMB (@lem5237257) (@lem5237256 s b)). Qed.
Lemma lem5237267 (s : real -> Prop) : (term39 s) = (term39 s).
Proof. exact (eq_refl (term39 s)). Qed.
Lemma lem5237268 (s : real -> Prop) (b : real) : (term51 s b) = (term51 s b).
Proof. exact (MK_COMB (@lem5237267 s) (@lem5237258 s b)). Qed.
Lemma lem5237269 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5237270 (s : real -> Prop) (b : real) : (term54 s b) = (term54 s b).
Proof. exact (MK_COMB (@lem5237269) (@lem5237268 s b)). Qed.
Lemma lem5237271 (b : real) (s : real -> Prop) : (term56 b s) = (term56 b s).
Proof. exact (MK_COMB (@lem5237270 s b) (@lem5237240 b s)). Qed.
Lemma lem5237272 (b : real) (s : real -> Prop) (h1 : term56 b s) : term56 b s.
Proof. exact (EQ_MP (@lem5237271 b s) (@lem5237131 b s h1)). Qed.
Lemma lem5237274 (b : real) (s : real -> Prop) (h1 : term56 b s) : term51 s b.
Proof. exact (proj1 (@lem5237272 b s h1)). Qed.
Lemma lem5237275 (b : real) (s : real -> Prop) (h1 : term56 b s) : term50 s b.
Proof. exact (proj2 (@lem5237274 b s h1)). Qed.
Lemma lem5237278 {A : Type'} (P : Prop) (Q : A -> Prop) : (term267 A P Q) = (term268 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5237279 (P : Prop) (Q : real -> Prop) : (term269 P Q) = (term270 P Q).
Proof. exact (@lem5237278 real P Q). Qed.
Lemma lem5237280 (x : type1021) (s : real -> Prop) : (term271 x s) = (term272 x s).
Proof. exact (@lem5237279 (s = (@EMPTY real)) (term263 x s)). Qed.
Lemma lem5237281 (x : type1021) (s : real -> Prop) (b : real) : (term273 x s b) = (term262 x s b).
Proof. exact (eq_refl (term273 x s b)). Qed.
Lemma lem5237282 (x : type1021) (s : real -> Prop) : (term274 x s) = (term263 x s).
Proof. exact (fun_ext (fun b : real => @lem5237281 x s b)). Qed.
Lemma lem5237283 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5237284 (x : type1021) (s : real -> Prop) : (term275 x s) = (term264 x s).
Proof. exact (MK_COMB (@lem5237283) (@lem5237282 x s)). Qed.
Lemma lem5237285 (s : real -> Prop) : (term86 s) = (term86 s).
Proof. exact (eq_refl (term86 s)). Qed.
Lemma lem5237286 (x : type1021) (s : real -> Prop) : (term271 x s) = (term265 x s).
Proof. exact (MK_COMB (@lem5237285 s) (@lem5237284 x s)). Qed.
Lemma lem5237287 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5237288 (x : type1021) (s : real -> Prop) : (term276 x s) = (term277 x s).
Proof. exact (MK_COMB (@lem5237287) (@lem5237286 x s)). Qed.
Lemma lem5237289 (x : type1021) (s : real -> Prop) (b : real) : (term273 x s b) = (term262 x s b).
Proof. exact (eq_refl (term273 x s b)). Qed.
Lemma lem5237290 (s : real -> Prop) : (term86 s) = (term86 s).
Proof. exact (eq_refl (term86 s)). Qed.
Lemma lem5237291 (x : type1021) (s : real -> Prop) (b : real) : (term278 x s b) = (term279 x s b).
Proof. exact (MK_COMB (@lem5237290 s) (@lem5237289 x s b)). Qed.
Lemma lem5237292 (x : type1021) (s : real -> Prop) : (term280 x s) = (term281 x s).
Proof. exact (fun_ext (fun b : real => @lem5237291 x s b)). Qed.
Lemma lem5237293 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5237294 (x : type1021) (s : real -> Prop) : (term272 x s) = (term282 x s).
Proof. exact (MK_COMB (@lem5237293) (@lem5237292 x s)). Qed.
Lemma lem5237295 (x : type1021) (s : real -> Prop) : ((term271 x s) = (term272 x s)) = ((term265 x s) = (term282 x s)).
Proof. exact (MK_COMB (@lem5237288 x s) (@lem5237294 x s)). Qed.
Lemma lem5237296 (x : type1021) (s : real -> Prop) : (term265 x s) = (term282 x s).
Proof. exact (EQ_MP (@lem5237295 x s) (@lem5237280 x s)). Qed.
Lemma lem5237297 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5237298 (x : type1021) (s : real -> Prop) : (term266 x s) = (term283 x s).
Proof. exact (MK_COMB (@lem5237297) (@lem5237296 x s)). Qed.
Lemma lem5237300 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term284 A P Q) = (term285 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem5237301 (P : real -> Prop) (Q : real -> Prop) : (term286 P Q) = (term287 P Q).
Proof. exact (@lem5237300 real P Q). Qed.
Lemma lem5237302 (x : type1021) (s : real -> Prop) : (term288 x s) = (term289 x s).
Proof. exact (@lem5237301 (term93 s) (term259 x s)). Qed.
Lemma lem5237303 (s : real -> Prop) (b : real) : (term290 s b) = (term91 s b).
Proof. exact (eq_refl (term290 s b)). Qed.
Lemma lem5237304 (s : real -> Prop) : (term291 s) = (term93 s).
Proof. exact (fun_ext (fun b : real => @lem5237303 s b)). Qed.
Lemma lem5237305 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5237306 (s : real -> Prop) : (term292 s) = (term94 s).
Proof. exact (MK_COMB (@lem5237305) (@lem5237304 s)). Qed.
Lemma lem5237307 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5237308 (s : real -> Prop) : (term293 s) = (term101 s).
Proof. exact (MK_COMB (@lem5237307) (@lem5237306 s)). Qed.
Lemma lem5237309 (x : type1021) (b : real) (s : real -> Prop) : (term294 x s b) = (term258 x b s).
Proof. exact (eq_refl (term294 x s b)). Qed.
Lemma lem5237310 (x : type1021) (s : real -> Prop) : (term295 x s) = (term259 x s).
Proof. exact (fun_ext (fun b : real => @lem5237309 x b s)). Qed.
Lemma lem5237311 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5237312 (x : type1021) (s : real -> Prop) : (term296 x s) = (term260 x s).
Proof. exact (MK_COMB (@lem5237311) (@lem5237310 x s)). Qed.
Lemma lem5237313 (x : type1021) (s : real -> Prop) : (term288 x s) = (term261 x s).
Proof. exact (MK_COMB (@lem5237308 s) (@lem5237312 x s)). Qed.
Lemma lem5237314 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5237315 (x : type1021) (s : real -> Prop) : (term297 x s) = (term298 x s).
Proof. exact (MK_COMB (@lem5237314) (@lem5237313 x s)). Qed.
Lemma lem5237316 (s : real -> Prop) (b : real) : (term290 s b) = (term91 s b).
Proof. exact (eq_refl (term290 s b)). Qed.
Lemma lem5237317 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5237318 (s : real -> Prop) (b : real) : (term299 s b) = (term300 s b).
Proof. exact (MK_COMB (@lem5237317) (@lem5237316 s b)). Qed.
Lemma lem5237319 (x : type1021) (b : real) (s : real -> Prop) : (term294 x s b) = (term258 x b s).
Proof. exact (eq_refl (term294 x s b)). Qed.
Lemma lem5237320 (x : type1021) (b : real) (s : real -> Prop) : (term301 x s b) = (term302 x b s).
Proof. exact (MK_COMB (@lem5237318 s b) (@lem5237319 x b s)). Qed.
Lemma lem5237321 (x : type1021) (s : real -> Prop) : (term303 x s) = (term304 x s).
Proof. exact (fun_ext (fun b : real => @lem5237320 x b s)). Qed.
Lemma lem5237322 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5237323 (x : type1021) (s : real -> Prop) : (term289 x s) = (term305 x s).
Proof. exact (MK_COMB (@lem5237322) (@lem5237321 x s)). Qed.
Lemma lem5237324 (x : type1021) (s : real -> Prop) : ((term288 x s) = (term289 x s)) = ((term261 x s) = (term305 x s)).
Proof. exact (MK_COMB (@lem5237315 x s) (@lem5237323 x s)). Qed.
Lemma lem5237325 (x : type1021) (s : real -> Prop) : (term261 x s) = (term305 x s).
Proof. exact (EQ_MP (@lem5237324 x s) (@lem5237302 x s)). Qed.
Lemma lem5237328 (x : type1021) (s : real -> Prop) : (term306 x s) = (term306 x s).
Proof. exact (eq_refl (term306 x s)). Qed.
Lemma lem5237329 (x : type1021) (s : real -> Prop) : (term306 x s) = ((term261 x s) = (term305 x s)).
Proof. exact (eq_refl (term306 x s)). Qed.
Lemma lem5237330 (x : type1021) (s : real -> Prop) : (term307 x s) = (term307 x s).
Proof. exact (eq_refl (term307 x s)). Qed.
Lemma lem5237331 (x : type1021) (s : real -> Prop) : ((term306 x s) = (term306 x s)) = ((term306 x s) = ((term261 x s) = (term305 x s))).
Proof. exact (MK_COMB (@lem5237330 x s) (@lem5237329 x s)). Qed.
Lemma lem5237332 (x : type1021) (s : real -> Prop) : (term306 x s) = ((term261 x s) = (term305 x s)).
Proof. exact (eq_refl (term306 x s)). Qed.
Lemma lem5237333 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5237334 (x : type1021) (s : real -> Prop) : (term307 x s) = (term308 x s).
Proof. exact (MK_COMB (@lem5237333) (@lem5237332 x s)). Qed.
Lemma lem5237335 (x : type1021) (s : real -> Prop) : ((term261 x s) = (term305 x s)) = ((term261 x s) = (term305 x s)).
Proof. exact (eq_refl ((term261 x s) = (term305 x s))). Qed.
Lemma lem5237336 (x : type1021) (s : real -> Prop) : ((term306 x s) = ((term261 x s) = (term305 x s))) = (((term261 x s) = (term305 x s)) = ((term261 x s) = (term305 x s))).
Proof. exact (MK_COMB (@lem5237334 x s) (@lem5237335 x s)). Qed.
Lemma lem5237337 (x : type1021) (s : real -> Prop) : ((term306 x s) = (term306 x s)) = (((term261 x s) = (term305 x s)) = ((term261 x s) = (term305 x s))).
Proof. exact (TRANS (@lem5237331 x s) (@lem5237336 x s)). Qed.
Lemma lem5237338 (x : type1021) (s : real -> Prop) : ((term261 x s) = (term305 x s)) = ((term261 x s) = (term305 x s)).
Proof. exact (EQ_MP (@lem5237337 x s) (@lem5237328 x s)). Qed.
Lemma lem5237339 (x : type1021) (s : real -> Prop) : (term261 x s) = (term305 x s).
Proof. exact (EQ_MP (@lem5237338 x s) (@lem5237325 x s)). Qed.
Lemma lem5237340 (x : type1021) (s : real -> Prop) : (term250 x s) = (term309 x s).
Proof. exact (MK_COMB (@lem5237298 x s) (@lem5237339 x s)). Qed.
Lemma lem5237342 {A : Type'} (P : A -> Prop) (Q : Prop) : (term310 A P Q) = (term311 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem5237343 (P : real -> Prop) (Q : Prop) : (term312 P Q) = (term313 P Q).
Proof. exact (@lem5237342 real P Q). Qed.
Lemma lem5237344 (x : type1021) (s : real -> Prop) : (term314 x s) = (term315 x s).
Proof. exact (@lem5237343 (term281 x s) (term305 x s)). Qed.
Lemma lem5237345 (x : type1021) (s : real -> Prop) (b : real) : (term316 x s b) = (term279 x s b).
Proof. exact (eq_refl (term316 x s b)). Qed.
Lemma lem5237346 (x : type1021) (s : real -> Prop) : (term317 x s) = (term281 x s).
Proof. exact (fun_ext (fun b : real => @lem5237345 x s b)). Qed.
Lemma lem5237347 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5237348 (x : type1021) (s : real -> Prop) : (term318 x s) = (term282 x s).
Proof. exact (MK_COMB (@lem5237347) (@lem5237346 x s)). Qed.
Lemma lem5237349 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5237350 (x : type1021) (s : real -> Prop) : (term319 x s) = (term283 x s).
Proof. exact (MK_COMB (@lem5237349) (@lem5237348 x s)). Qed.
Lemma lem5237351 (x : type1021) (s : real -> Prop) : (term305 x s) = (term305 x s).
Proof. exact (eq_refl (term305 x s)). Qed.
Lemma lem5237352 (x : type1021) (s : real -> Prop) : (term314 x s) = (term309 x s).
Proof. exact (MK_COMB (@lem5237350 x s) (@lem5237351 x s)). Qed.
Lemma lem5237353 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5237354 (x : type1021) (s : real -> Prop) : (term320 x s) = (term321 x s).
Proof. exact (MK_COMB (@lem5237353) (@lem5237352 x s)). Qed.
Lemma lem5237355 (x : type1021) (s : real -> Prop) (b : real) : (term316 x s b) = (term279 x s b).
Proof. exact (eq_refl (term316 x s b)). Qed.
Lemma lem5237356 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5237357 (x : type1021) (s : real -> Prop) (b : real) : (term322 x s b) = (term323 x s b).
Proof. exact (MK_COMB (@lem5237356) (@lem5237355 x s b)). Qed.
Lemma lem5237358 (x : type1021) (s : real -> Prop) : (term305 x s) = (term305 x s).
Proof. exact (eq_refl (term305 x s)). Qed.
Lemma lem5237359 (b : real) (x : type1021) (s : real -> Prop) : (term324 b x s) = (term325 b x s).
Proof. exact (MK_COMB (@lem5237357 x s b) (@lem5237358 x s)). Qed.
Lemma lem5237360 (x : type1021) (s : real -> Prop) : (term326 x s) = (term327 x s).
Proof. exact (fun_ext (fun b : real => @lem5237359 b x s)). Qed.
Lemma lem5237361 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5237362 (x : type1021) (s : real -> Prop) : (term315 x s) = (term328 x s).
Proof. exact (MK_COMB (@lem5237361) (@lem5237360 x s)). Qed.
Lemma lem5237363 (x : type1021) (s : real -> Prop) : ((term314 x s) = (term315 x s)) = ((term309 x s) = (term328 x s)).
Proof. exact (MK_COMB (@lem5237354 x s) (@lem5237362 x s)). Qed.
Lemma lem5237364 (x : type1021) (s : real -> Prop) : (term309 x s) = (term328 x s).
Proof. exact (EQ_MP (@lem5237363 x s) (@lem5237344 x s)). Qed.
Lemma lem5237366 {A : Type'} (P : Prop) (Q : A -> Prop) : (term267 A P Q) = (term268 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5237367 (P : Prop) (Q : real -> Prop) : (term269 P Q) = (term270 P Q).
Proof. exact (@lem5237366 real P Q). Qed.
Lemma lem5237368 (b : real) (x : type1021) (s : real -> Prop) : (term329 b x s) = (term330 b x s).
Proof. exact (@lem5237367 (term279 x s b) (term304 x s)). Qed.
Lemma lem5237369 (x : type1021) (b : real) (s : real -> Prop) : (term331 x s b) = (term302 x b s).
Proof. exact (eq_refl (term331 x s b)). Qed.
Lemma lem5237370 (x : type1021) (s : real -> Prop) : (term332 x s) = (term304 x s).
Proof. exact (fun_ext (fun b : real => @lem5237369 x b s)). Qed.
Lemma lem5237371 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5237372 (x : type1021) (s : real -> Prop) : (term333 x s) = (term305 x s).
Proof. exact (MK_COMB (@lem5237371) (@lem5237370 x s)). Qed.
Lemma lem5237373 (x : type1021) (s : real -> Prop) (b : real) : (term323 x s b) = (term323 x s b).
Proof. exact (eq_refl (term323 x s b)). Qed.
Lemma lem5237374 (b : real) (x : type1021) (s : real -> Prop) : (term329 b x s) = (term325 b x s).
Proof. exact (MK_COMB (@lem5237373 x s b) (@lem5237372 x s)). Qed.
Lemma lem5237375 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5237376 (b : real) (x : type1021) (s : real -> Prop) : (term334 b x s) = (term335 b x s).
Proof. exact (MK_COMB (@lem5237375) (@lem5237374 b x s)). Qed.
Lemma lem5237377 (x : type1021) (b' : real) (s : real -> Prop) : (term331 x s b') = (term302 x b' s).
Proof. exact (eq_refl (term331 x s b')). Qed.
Lemma lem5237378 (x : type1021) (s : real -> Prop) (b : real) : (term323 x s b) = (term323 x s b).
Proof. exact (eq_refl (term323 x s b)). Qed.
Lemma lem5237379 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term336 b x s b') = (term337 b x b' s).
Proof. exact (MK_COMB (@lem5237378 x s b) (@lem5237377 x b' s)). Qed.
Lemma lem5237380 (b : real) (x : type1021) (s : real -> Prop) : (term338 b x s) = (term339 b x s).
Proof. exact (fun_ext (fun b' : real => @lem5237379 b x b' s)). Qed.
Lemma lem5237381 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5237382 (b : real) (x : type1021) (s : real -> Prop) : (term330 b x s) = (term340 b x s).
Proof. exact (MK_COMB (@lem5237381) (@lem5237380 b x s)). Qed.
Lemma lem5237383 (b : real) (x : type1021) (s : real -> Prop) : ((term329 b x s) = (term330 b x s)) = ((term325 b x s) = (term340 b x s)).
Proof. exact (MK_COMB (@lem5237376 b x s) (@lem5237382 b x s)). Qed.
Lemma lem5237384 (b : real) (x : type1021) (s : real -> Prop) : (term325 b x s) = (term340 b x s).
Proof. exact (EQ_MP (@lem5237383 b x s) (@lem5237368 b x s)). Qed.
Lemma lem5237385 (x : type1021) (s : real -> Prop) : (term327 x s) = (term341 x s).
Proof. exact (fun_ext (fun b : real => @lem5237384 b x s)). Qed.
Lemma lem5237386 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5237387 (x : type1021) (s : real -> Prop) : (term328 x s) = (term342 x s).
Proof. exact (MK_COMB (@lem5237386) (@lem5237385 x s)). Qed.
Lemma lem5237388 (x : type1021) (s : real -> Prop) : (term309 x s) = (term342 x s).
Proof. exact (TRANS (@lem5237364 x s) (@lem5237387 x s)). Qed.
Lemma lem5237389 (x : type1021) (s : real -> Prop) : (term250 x s) = (term342 x s).
Proof. exact (TRANS (@lem5237340 x s) (@lem5237388 x s)). Qed.
Lemma lem5237390 (x : type1021) : (term252 x) = (term343 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5237389 x s)). Qed.
Lemma lem5237391 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5237392 (x : type1021) : (term254 x) = (term344 x).
Proof. exact (MK_COMB (@lem5237391) (@lem5237390 x)). Qed.
Lemma lem5237409 (x : type1021) (b' : real) (s : real -> Prop) : (term258 x b' s) = (term345 x b' s).
Proof. exact (@lem19699 (term346 x b' s) (term347 x s b') (term24 b' s)). Qed.
Lemma lem5237418 (s : real -> Prop) (b' : real) : (term300 s b') = (term300 s b').
Proof. exact (eq_refl (term300 s b')). Qed.
Lemma lem5237419 (x : type1021) (b' : real) (s : real -> Prop) : (term302 x b' s) = (term348 x b' s).
Proof. exact (MK_COMB (@lem5237418 s b') (@lem5237409 x b' s)). Qed.
Lemma lem5237436 (x : type1021) (s : real -> Prop) (b : real) : (term279 x s b) = (term349 x s b).
Proof. exact (@lem19490 (term346 x b s) (s = (@EMPTY real)) (term347 x s b)). Qed.
Lemma lem5237437 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5237438 (x : type1021) (s : real -> Prop) (b : real) : (term323 x s b) = (term350 x s b).
Proof. exact (MK_COMB (@lem5237437) (@lem5237436 x s b)). Qed.
Lemma lem5237439 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term337 b x b' s) = (term351 b x b' s).
Proof. exact (MK_COMB (@lem5237438 x s b) (@lem5237419 x b' s)). Qed.
Lemma lem5237440 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term351 b x b' s) = (term352 b x b' s).
Proof. exact (@lem19490 (term91 s b') (term349 x s b) (term345 x b' s)). Qed.
Lemma lem5237441 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term353 b x b' s) = (term354 b x b' s).
Proof. exact (@lem19490 (term355 x b' s) (term349 x s b) (term356 x b' s)). Qed.
Lemma lem5237448 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term357 b x b' s) = (term358 b x b' s).
Proof. exact (@lem19699 (term359 x b s) (term360 x s b) (term356 x b' s)). Qed.
Lemma lem5237455 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term361 b x b' s) = (term362 b x b' s).
Proof. exact (@lem19699 (term359 x b s) (term360 x s b) (term355 x b' s)). Qed.
Lemma lem5237456 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5237457 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term363 b x b' s) = (term364 b x b' s).
Proof. exact (MK_COMB (@lem5237456) (@lem5237455 b x b' s)). Qed.
Lemma lem5237458 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term354 b x b' s) = (term365 b x b' s).
Proof. exact (MK_COMB (@lem5237457 b x b' s) (@lem5237448 b x b' s)). Qed.
Lemma lem5237459 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term353 b x b' s) = (term365 b x b' s).
Proof. exact (TRANS (@lem5237441 b x b' s) (@lem5237458 b x b' s)). Qed.
Lemma lem5237466 (x : type1021) (b : real) (s : real -> Prop) (b' : real) : (term366 x b s b') = (term367 x b s b').
Proof. exact (@lem19699 (term359 x b s) (term360 x s b) (term91 s b')). Qed.
Lemma lem5237467 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5237468 (x : type1021) (b : real) (s : real -> Prop) (b' : real) : (term368 x b s b') = (term369 x b s b').
Proof. exact (MK_COMB (@lem5237467) (@lem5237466 x b s b')). Qed.
Lemma lem5237469 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term352 b x b' s) = (term370 b x b' s).
Proof. exact (MK_COMB (@lem5237468 x b s b') (@lem5237459 b x b' s)). Qed.
Lemma lem5237470 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term351 b x b' s) = (term370 b x b' s).
Proof. exact (TRANS (@lem5237440 b x b' s) (@lem5237469 b x b' s)). Qed.
Lemma lem5237471 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term337 b x b' s) = (term370 b x b' s).
Proof. exact (TRANS (@lem5237439 b x b' s) (@lem5237470 b x b' s)). Qed.
Lemma lem5237472 (b : real) (x : type1021) (s : real -> Prop) : (term339 b x s) = (term371 b x s).
Proof. exact (fun_ext (fun b' : real => @lem5237471 b x b' s)). Qed.
Lemma lem5237473 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5237474 (b : real) (x : type1021) (s : real -> Prop) : (term340 b x s) = (term372 b x s).
Proof. exact (MK_COMB (@lem5237473) (@lem5237472 b x s)). Qed.
Lemma lem5237475 (x : type1021) (s : real -> Prop) : (term341 x s) = (term373 x s).
Proof. exact (fun_ext (fun b : real => @lem5237474 b x s)). Qed.
Lemma lem5237476 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5237477 (x : type1021) (s : real -> Prop) : (term342 x s) = (term374 x s).
Proof. exact (MK_COMB (@lem5237476) (@lem5237475 x s)). Qed.
Lemma lem5237478 (x : type1021) : (term343 x) = (term375 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5237477 x s)). Qed.
Lemma lem5237479 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5237480 (x : type1021) : (term344 x) = (term376 x).
Proof. exact (MK_COMB (@lem5237479) (@lem5237478 x)). Qed.
Lemma lem5237481 (x : type1021) : (term254 x) = (term376 x).
Proof. exact (TRANS (@lem5237392 x) (@lem5237480 x)). Qed.
Lemma lem5237482 (x : type1021) (h1 : term254 x) : term376 x.
Proof. exact (EQ_MP (@lem5237481 x) (@lem5237231 x h1)). Qed.
Lemma lem5237498 (s : real -> Prop) (b : real) (x : real) : (term48 s b x) = (term48 s b x).
Proof. exact (eq_refl (term48 s b x)). Qed.
Lemma lem5237499 (s : real -> Prop) (b : real) : (term49 s b) = (term49 s b).
Proof. exact (fun_ext (fun x : real => @lem5237498 s b x)). Qed.
Lemma lem5237500 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5237502 (s : real -> Prop) (b : real) : (term50 s b) = (term50 s b).
Proof. exact (MK_COMB (@lem5237500) (@lem5237499 s b)). Qed.
Lemma lem5237503 (b : real) (s : real -> Prop) (h1 : term56 b s) : term50 s b.
Proof. exact (EQ_MP (@lem5237502 s b) (@lem5237275 b s h1)). Qed.
Lemma lem5237504 (_68643 : real -> Prop) (x : type1021) (h1 : term254 x) : term377 x _68643.
Proof. exact (@lem5237482 x h1 _68643). Qed.
Lemma lem5237505 (x : type1021) (_68643 : real -> Prop) : (term377 x _68643) = (term374 x _68643).
Proof. exact (eq_refl (term377 x _68643)). Qed.
Lemma lem5237506 (_68643 : real -> Prop) (x : type1021) (h1 : term254 x) : term374 x _68643.
Proof. exact (EQ_MP (@lem5237505 x _68643) (@lem5237504 _68643 x h1)). Qed.
Lemma lem5237507 (_68643 : real -> Prop) (_68644 : real) (x : type1021) (h1 : term254 x) : term378 x _68643 _68644.
Proof. exact (@lem5237506 _68643 x h1 _68644). Qed.
Lemma lem5237508 (_68644 : real) (x : type1021) (_68643 : real -> Prop) : (term378 x _68643 _68644) = (term372 _68644 x _68643).
Proof. exact (eq_refl (term378 x _68643 _68644)). Qed.
Lemma lem5237509 (_68644 : real) (_68643 : real -> Prop) (x : type1021) (h1 : term254 x) : term372 _68644 x _68643.
Proof. exact (EQ_MP (@lem5237508 _68644 x _68643) (@lem5237507 _68643 _68644 x h1)). Qed.
Lemma lem5237510 (_68644 : real) (_68643 : real -> Prop) (_68645 : real) (x : type1021) (h1 : term254 x) : term379 _68644 x _68643 _68645.
Proof. exact (@lem5237509 _68644 _68643 x h1 _68645). Qed.
Lemma lem5237511 (_68644 : real) (x : type1021) (_68645 : real) (_68643 : real -> Prop) : (term379 _68644 x _68643 _68645) = (term370 _68644 x _68645 _68643).
Proof. exact (eq_refl (term379 _68644 x _68643 _68645)). Qed.
Lemma lem5237512 (_68644 : real) (_68645 : real) (_68643 : real -> Prop) (x : type1021) (h1 : term254 x) : term370 _68644 x _68645 _68643.
Proof. exact (EQ_MP (@lem5237511 _68644 x _68645 _68643) (@lem5237510 _68644 _68643 _68645 x h1)). Qed.
Lemma lem5237513 (_68646 : real) (b : real) (s : real -> Prop) (h1 : term56 b s) : term380 s b _68646.
Proof. exact (@lem5237503 b s h1 _68646). Qed.
Lemma lem5237514 (s : real -> Prop) (b : real) (_68646 : real) : (term380 s b _68646) = (term48 s b _68646).
Proof. exact (eq_refl (term380 s b _68646)). Qed.
Lemma lem5237516 (_68644 : real) (_68645 : real) (_68643 : real -> Prop) (x : type1021) (h1 : term254 x) : term365 _68644 x _68645 _68643.
Proof. exact (proj2 (@lem5237512 _68644 _68645 _68643 x h1)). Qed.
Lemma lem5237518 (_68644 : real) (_68645 : real) (_68643 : real -> Prop) (x : type1021) (h1 : term254 x) : term358 _68644 x _68645 _68643.
Proof. exact (proj2 (@lem5237516 _68644 _68645 _68643 x h1)). Qed.
Lemma lem5237519 (_68644 : real) (_68645 : real) (_68643 : real -> Prop) (x : type1021) (h1 : term254 x) : term362 _68644 x _68645 _68643.
Proof. exact (proj1 (@lem5237516 _68644 _68645 _68643 x h1)). Qed.
Lemma lem5237520 (_68644 : real) (_68645 : real) (_68643 : real -> Prop) (x : type1021) (h1 : term254 x) : term381 _68644 x _68645 _68643.
Proof. exact (proj2 (@lem5237518 _68644 _68645 _68643 x h1)). Qed.
Lemma lem5237522 (_68644 : real) (_68645 : real) (_68643 : real -> Prop) (x : type1021) (h1 : term254 x) : term382 _68644 x _68645 _68643.
Proof. exact (proj2 (@lem5237519 _68644 _68645 _68643 x h1)). Qed.
Lemma lem5237523 (_68644 : real) (_68645 : real) (_68643 : real -> Prop) (x : type1021) (h1 : term254 x) : term383 _68644 x _68645 _68643.
Proof. exact (proj1 (@lem5237519 _68644 _68645 _68643 x h1)). Qed.
Lemma lem5237529 (b : real) (s : real -> Prop) (h1 : term56 b s) : term90 s.
Proof. exact (proj1 (@lem5237274 b s h1)). Qed.
Lemma lem5237535 (_68646 : real) (b : real) (s : real -> Prop) (h1 : term56 b s) : term48 s b _68646.
Proof. exact (EQ_MP (@lem5237514 s b _68646) (@lem5237513 _68646 b s h1)). Qed.
Lemma lem5237566 (_68644 : real) (x : type1021) (_68645 : real) (_68643 : real -> Prop) : (term381 _68644 x _68645 _68643) = (term384 _68644 x _68645 _68643).
Proof. exact (@lem5236211 (_68643 = (@EMPTY real)) (term347 x _68643 _68644) (term356 x _68645 _68643)). Qed.
Lemma lem5237567 (_68644 : real) (_68645 : real) (_68643 : real -> Prop) (x : type1021) (h1 : term254 x) : term384 _68644 x _68645 _68643.
Proof. exact (EQ_MP (@lem5237566 _68644 x _68645 _68643) (@lem5237520 _68644 _68645 _68643 x h1)). Qed.
Lemma lem5237582 (_68644 : real) (x : type1021) (_68645 : real) (_68643 : real -> Prop) : (term383 _68644 x _68645 _68643) = (term385 _68644 x _68645 _68643).
Proof. exact (@lem5236211 (_68643 = (@EMPTY real)) (term346 x _68644 _68643) (term355 x _68645 _68643)). Qed.
Lemma lem5237583 (_68644 : real) (_68645 : real) (_68643 : real -> Prop) (x : type1021) (h1 : term254 x) : term385 _68644 x _68645 _68643.
Proof. exact (EQ_MP (@lem5237582 _68644 x _68645 _68643) (@lem5237523 _68644 _68645 _68643 x h1)). Qed.
Lemma lem5237598 (_68644 : real) (x : type1021) (_68645 : real) (_68643 : real -> Prop) : (term382 _68644 x _68645 _68643) = (term386 _68644 x _68645 _68643).
Proof. exact (@lem5236211 (_68643 = (@EMPTY real)) (term347 x _68643 _68644) (term355 x _68645 _68643)). Qed.
Lemma lem5237599 (_68644 : real) (_68645 : real) (_68643 : real -> Prop) (x : type1021) (h1 : term254 x) : term386 _68644 x _68645 _68643.
Proof. exact (EQ_MP (@lem5237598 _68644 x _68645 _68643) (@lem5237522 _68644 _68645 _68643 x h1)). Qed.
Lemma lem5237699 (s : real -> Prop) (h1 : term90 s) : term90 s.
Proof. exact (h1). Qed.
Lemma lem5237700 (s : real -> Prop) (h1 : term90 s) : term387 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5237699 s h1). Qed.
Lemma lem5237702 (p : Prop) : (term388 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5237703 (s : real -> Prop) : (term387 s) = (term90 s).
Proof. exact (@lem5237702 (s = (@EMPTY real))). Qed.
Lemma lem5237704 (s : real -> Prop) (h1 : term90 s) : term90 s.
Proof. exact (EQ_MP (@lem5237703 s) (@lem5237700 s h1)). Qed.
Lemma lem5237707 (x : type1021) (b : real) (s : real -> Prop) (h1 : term389 x b s) : term389 x b s.
Proof. exact (h1). Qed.
Lemma lem5237708 (x : type1021) (b : real) (s : real -> Prop) (h1 : term389 x b s) : term390 x b s.
Proof. exact (fun h0 : term346 x b s => @lem5237707 x b s h1). Qed.
Lemma lem5237710 (p : Prop) : (term388 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5237711 (x : type1021) (b : real) (s : real -> Prop) : (term390 x b s) = (term389 x b s).
Proof. exact (@lem5237710 (term346 x b s)). Qed.
Lemma lem5237712 (x : type1021) (b : real) (s : real -> Prop) (h1 : term389 x b s) : term389 x b s.
Proof. exact (EQ_MP (@lem5237711 x b s) (@lem5237708 x b s h1)). Qed.
Lemma lem5237714 (b : real) (s : real -> Prop) (h1 : term56 b s) : term52 b s.
Proof. exact (proj2 (@lem5237272 b s h1)). Qed.
Lemma lem5237715 (b : real) (s : real -> Prop) (h1 : term56 b s) : term391 b s.
Proof. exact (fun h0 : term24 b s => @lem5237714 b s h1). Qed.
Lemma lem5237717 (p : Prop) : (term388 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5237718 (b : real) (s : real -> Prop) : (term391 b s) = (term52 b s).
Proof. exact (@lem5237717 (term24 b s)). Qed.
Lemma lem5237719 (b : real) (s : real -> Prop) (h1 : term56 b s) : term52 b s.
Proof. exact (EQ_MP (@lem5237718 b s) (@lem5237715 b s h1)). Qed.
Lemma lem5237752 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5237753 (x : type1021) (_68644 : real) (_68645 : real) (_68643 : real -> Prop) : (term392 x _68644 _68645 _68643) = (term393 x _68644 _68645 _68643).
Proof. exact (@lem5237752 (_68643 = (@EMPTY real)) (term346 x _68645 _68643) (term394 x _68644 _68645 _68643)). Qed.
Lemma lem5237769 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5237770 (_68644 : real) (x : type1021) (_68645 : real) (_68643 : real -> Prop) : (term395 x _68644 _68645 _68643) = (term396 _68644 x _68645 _68643).
Proof. exact (@lem5237769 (term346 x _68644 _68643) (term346 x _68645 _68643) (term24 _68645 _68643)). Qed.
Lemma lem5237786 (_68643 : real -> Prop) : (term86 _68643) = (term86 _68643).
Proof. exact (eq_refl (term86 _68643)). Qed.
Lemma lem5237787 (_68644 : real) (x : type1021) (_68645 : real) (_68643 : real -> Prop) : (term393 x _68644 _68645 _68643) = (term385 _68644 x _68645 _68643).
Proof. exact (MK_COMB (@lem5237786 _68643) (@lem5237770 _68644 x _68645 _68643)). Qed.
Lemma lem5237798 (_68644 : real) (x : type1021) (_68645 : real) (_68643 : real -> Prop) : (term392 x _68644 _68645 _68643) = (term385 _68644 x _68645 _68643).
Proof. exact (TRANS (@lem5237753 x _68644 _68645 _68643) (@lem5237787 _68644 x _68645 _68643)). Qed.
Lemma lem5237799 (_68644 : real) (x : type1021) (_68645 : real) (_68643 : real -> Prop) : (term397 _68644 x _68645 _68643) = (term397 _68644 x _68645 _68643).
Proof. exact (eq_refl (term397 _68644 x _68645 _68643)). Qed.
Lemma lem5237800 (_68644 : real) (x : type1021) (_68645 : real) (_68643 : real -> Prop) : ((term385 _68644 x _68645 _68643) = (term392 x _68644 _68645 _68643)) = ((term385 _68644 x _68645 _68643) = (term385 _68644 x _68645 _68643)).
Proof. exact (MK_COMB (@lem5237799 _68644 x _68645 _68643) (@lem5237798 _68644 x _68645 _68643)). Qed.
Lemma lem5237802 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5237803 (x : Prop) : (x = x) = True.
Proof. exact (@lem5237802 Prop x). Qed.
Lemma lem5237804 (_68644 : real) (x : type1021) (_68645 : real) (_68643 : real -> Prop) : ((term385 _68644 x _68645 _68643) = (term385 _68644 x _68645 _68643)) = True.
Proof. exact (@lem5237803 (term385 _68644 x _68645 _68643)). Qed.
Lemma lem5237805 (x : type1021) (_68644 : real) (_68645 : real) (_68643 : real -> Prop) : ((term385 _68644 x _68645 _68643) = (term392 x _68644 _68645 _68643)) = True.
Proof. exact (TRANS (@lem5237800 _68644 x _68645 _68643) (@lem5237804 _68644 x _68645 _68643)). Qed.
Lemma lem5237806 (x : type1021) (_68644 : real) (_68645 : real) (_68643 : real -> Prop) : True = ((term385 _68644 x _68645 _68643) = (term392 x _68644 _68645 _68643)).
Proof. exact (SYM (@lem5237805 x _68644 _68645 _68643)). Qed.
Lemma lem5237807 (x : type1021) (_68644 : real) (_68645 : real) (_68643 : real -> Prop) : (term385 _68644 x _68645 _68643) = (term392 x _68644 _68645 _68643).
Proof. exact (EQ_MP (@lem5237806 x _68644 _68645 _68643) (@lem0)). Qed.
Lemma lem5237808 (_68644 : real) (_68645 : real) (_68643 : real -> Prop) (x : type1021) (h1 : term254 x) : term392 x _68644 _68645 _68643.
Proof. exact (EQ_MP (@lem5237807 x _68644 _68645 _68643) (@lem5237583 _68644 _68645 _68643 x h1)). Qed.
Lemma lem5237810 (b : Prop) (a : Prop) : (a \/ b) = (term398 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5237811 (_68644 : real) (x : type1021) (_68645 : real) (_68643 : real -> Prop) : (term392 x _68644 _68645 _68643) = (term399 _68644 x _68645 _68643).
Proof. exact (@lem5237810 (term400 x _68644 _68645 _68643) (term346 x _68645 _68643)). Qed.
Lemma lem5237813 (a : Prop) (b : Prop) : (term401 a b) = (term402 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5237814 (x : type1021) (_68644 : real) (_68645 : real) (_68643 : real -> Prop) : (term403 x _68644 _68645 _68643) = (term404 x _68644 _68645 _68643).
Proof. exact (@lem5237813 (_68643 = (@EMPTY real)) (term394 x _68644 _68645 _68643)). Qed.
Lemma lem5237816 (a : Prop) (b : Prop) : (term401 a b) = (term402 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5237817 (x : type1021) (_68644 : real) (_68645 : real) (_68643 : real -> Prop) : (term405 x _68644 _68645 _68643) = (term406 x _68644 _68645 _68643).
Proof. exact (@lem5237816 (term346 x _68644 _68643) (term24 _68645 _68643)). Qed.
Lemma lem5237818 (_68643 : real -> Prop) : (term39 _68643) = (term39 _68643).
Proof. exact (eq_refl (term39 _68643)). Qed.
Lemma lem5237819 (x : type1021) (_68644 : real) (_68645 : real) (_68643 : real -> Prop) : (term404 x _68644 _68645 _68643) = (term407 x _68644 _68645 _68643).
Proof. exact (MK_COMB (@lem5237818 _68643) (@lem5237817 x _68644 _68645 _68643)). Qed.
Lemma lem5237820 (x : type1021) (_68644 : real) (_68645 : real) (_68643 : real -> Prop) : (term403 x _68644 _68645 _68643) = (term407 x _68644 _68645 _68643).
Proof. exact (TRANS (@lem5237814 x _68644 _68645 _68643) (@lem5237819 x _68644 _68645 _68643)). Qed.
Lemma lem5237821 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5237822 (x : type1021) (_68644 : real) (_68645 : real) (_68643 : real -> Prop) : (term408 x _68644 _68645 _68643) = (term409 x _68644 _68645 _68643).
Proof. exact (MK_COMB (@lem5237821) (@lem5237820 x _68644 _68645 _68643)). Qed.
Lemma lem5237823 (x : type1021) (_68645 : real) (_68643 : real -> Prop) : (term346 x _68645 _68643) = (term346 x _68645 _68643).
Proof. exact (eq_refl (term346 x _68645 _68643)). Qed.
Lemma lem5237824 (_68644 : real) (x : type1021) (_68645 : real) (_68643 : real -> Prop) : (term399 _68644 x _68645 _68643) = (term410 _68644 x _68645 _68643).
Proof. exact (MK_COMB (@lem5237822 x _68644 _68645 _68643) (@lem5237823 x _68645 _68643)). Qed.
Lemma lem5237825 (_68644 : real) (x : type1021) (_68645 : real) (_68643 : real -> Prop) : (term392 x _68644 _68645 _68643) = (term410 _68644 x _68645 _68643).
Proof. exact (TRANS (@lem5237811 _68644 x _68645 _68643) (@lem5237824 _68644 x _68645 _68643)). Qed.
Lemma lem5237827 (x : type1021) (b : real) (s : real -> Prop) (h1 : term389 x b s) (h2 : term56 b s) : term411 x b s.
Proof. exact (conj (@lem5237712 x b s h1) (@lem5237719 b s h2)). Qed.
Lemma lem5237828 (x : type1021) (b : real) (s : real -> Prop) (h1 : term90 s) (h2 : term389 x b s) (h3 : term56 b s) : term412 x b s.
Proof. exact (conj (@lem5237704 s h1) (@lem5237827 x b s h2 h3)). Qed.
Lemma lem5237830 (_68644 : real) (_68645 : real) (_68643 : real -> Prop) (x : type1021) (h1 : term254 x) : term410 _68644 x _68645 _68643.
Proof. exact (EQ_MP (@lem5237825 _68644 x _68645 _68643) (@lem5237808 _68644 _68645 _68643 x h1)). Qed.
Lemma lem5237831 (b : real) (s : real -> Prop) (x : type1021) (h1 : term254 x) : term413 x b s.
Proof. exact (@lem5237830 b b s x h1). Qed.
Lemma lem5237834 (x : type1021) (b : real) (s : real -> Prop) (h1 : term254 x) (h2 : term90 s) (h3 : term389 x b s) (h4 : term56 b s) : term346 x b s.
Proof. exact (@lem5237831 b s x h1 (@lem5237828 x b s h2 h3 h4)). Qed.
Lemma lem5237835 (x : type1021) (b : real) (s : real -> Prop) (h1 : term254 x) (h2 : term90 s) (h3 : term56 b s) : term414 x b s.
Proof. exact (fun h0 : term389 x b s => @lem5237834 x b s h1 h2 h0 h3). Qed.
Lemma lem5237837 (p : Prop) : (term415 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5237838 (x : type1021) (b : real) (s : real -> Prop) : (term414 x b s) = (term346 x b s).
Proof. exact (@lem5237837 (term346 x b s)). Qed.
Lemma lem5237839 (x : type1021) (b : real) (s : real -> Prop) (h1 : term254 x) (h2 : term90 s) (h3 : term56 b s) : term346 x b s.
Proof. exact (EQ_MP (@lem5237838 x b s) (@lem5237835 x b s h1 h2 h3)). Qed.
Lemma lem5237845 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5237846 (b : real) (_68646 : real) (s : real -> Prop) : (term48 s b _68646) = (term416 b _68646 s).
Proof. exact (@lem5237845 (real_le b _68646) (term417 _68646 s)). Qed.
Lemma lem5237852 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5237853 (b : real) (_68646 : real) (s : real -> Prop) : (term418 s b _68646) = (term419 b _68646 s).
Proof. exact (MK_COMB (@lem5237852) (@lem5237846 b _68646 s)). Qed.
Lemma lem5237859 (b : real) (_68646 : real) (s : real -> Prop) : (term416 b _68646 s) = (term416 b _68646 s).
Proof. exact (eq_refl (term416 b _68646 s)). Qed.
Lemma lem5237860 (b : real) (_68646 : real) (s : real -> Prop) : ((term48 s b _68646) = (term416 b _68646 s)) = ((term416 b _68646 s) = (term416 b _68646 s)).
Proof. exact (MK_COMB (@lem5237853 b _68646 s) (@lem5237859 b _68646 s)). Qed.
Lemma lem5237862 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5237863 (x : Prop) : (x = x) = True.
Proof. exact (@lem5237862 Prop x). Qed.
Lemma lem5237864 (b : real) (_68646 : real) (s : real -> Prop) : ((term416 b _68646 s) = (term416 b _68646 s)) = True.
Proof. exact (@lem5237863 (term416 b _68646 s)). Qed.
Lemma lem5237865 (b : real) (_68646 : real) (s : real -> Prop) : ((term48 s b _68646) = (term416 b _68646 s)) = True.
Proof. exact (TRANS (@lem5237860 b _68646 s) (@lem5237864 b _68646 s)). Qed.
Lemma lem5237866 (b : real) (_68646 : real) (s : real -> Prop) : True = ((term48 s b _68646) = (term416 b _68646 s)).
Proof. exact (SYM (@lem5237865 b _68646 s)). Qed.
Lemma lem5237867 (b : real) (_68646 : real) (s : real -> Prop) : (term48 s b _68646) = (term416 b _68646 s).
Proof. exact (EQ_MP (@lem5237866 b _68646 s) (@lem0)). Qed.
Lemma lem5237868 (_68646 : real) (b : real) (s : real -> Prop) (h1 : term56 b s) : term416 b _68646 s.
Proof. exact (EQ_MP (@lem5237867 b _68646 s) (@lem5237535 _68646 b s h1)). Qed.
Lemma lem5237870 (b : Prop) (a : Prop) : (a \/ b) = (term398 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5237871 (s : real -> Prop) (b : real) (_68646 : real) : (term416 b _68646 s) = (term420 s b _68646).
Proof. exact (@lem5237870 (term417 _68646 s) (real_le b _68646)). Qed.
Lemma lem5237873 (a : Prop) : (term421 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5237874 (_68646 : real) (s : real -> Prop) : (term422 _68646 s) = (@IN real _68646 s).
Proof. exact (@lem5237873 (@IN real _68646 s)). Qed.
Lemma lem5237875 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5237876 (_68646 : real) (s : real -> Prop) : (term423 _68646 s) = (term424 _68646 s).
Proof. exact (MK_COMB (@lem5237875) (@lem5237874 _68646 s)). Qed.
Lemma lem5237877 (b : real) (_68646 : real) : (real_le b _68646) = (real_le b _68646).
Proof. exact (eq_refl (real_le b _68646)). Qed.
Lemma lem5237878 (s : real -> Prop) (b : real) (_68646 : real) : (term420 s b _68646) = (term25 s b _68646).
Proof. exact (MK_COMB (@lem5237876 _68646 s) (@lem5237877 b _68646)). Qed.
Lemma lem5237879 (s : real -> Prop) (b : real) (_68646 : real) : (term416 b _68646 s) = (term25 s b _68646).
Proof. exact (TRANS (@lem5237871 s b _68646) (@lem5237878 s b _68646)). Qed.
Lemma lem5237882 (_68646 : real) (b : real) (s : real -> Prop) (h1 : term56 b s) : term25 s b _68646.
Proof. exact (EQ_MP (@lem5237879 s b _68646) (@lem5237868 _68646 b s h1)). Qed.
Lemma lem5237883 (x : type1021) (b : real) (s : real -> Prop) (h1 : term56 b s) : term425 x s b.
Proof. exact (@lem5237882 (x s b) b s h1). Qed.
Lemma lem5237886 (x : type1021) (b : real) (s : real -> Prop) (h1 : term254 x) (h2 : term90 s) (h3 : term56 b s) : term426 x s b.
Proof. exact (@lem5237883 x b s h3 (@lem5237839 x b s h1 h2 h3)). Qed.
Lemma lem5237887 (x : type1021) (b : real) (s : real -> Prop) (h1 : term254 x) (h2 : term90 s) (h3 : term56 b s) : term427 x s b.
Proof. exact (fun h0 : term347 x s b => @lem5237886 x b s h1 h2 h3). Qed.
Lemma lem5237889 (p : Prop) : (term415 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5237890 (x : type1021) (s : real -> Prop) (b : real) : (term427 x s b) = (term426 x s b).
Proof. exact (@lem5237889 (term426 x s b)). Qed.
Lemma lem5237891 (x : type1021) (b : real) (s : real -> Prop) (h1 : term254 x) (h2 : term90 s) (h3 : term56 b s) : term426 x s b.
Proof. exact (EQ_MP (@lem5237890 x s b) (@lem5237887 x b s h1 h2 h3)). Qed.
Lemma lem5237894 (s : real -> Prop) (h1 : term90 s) : term90 s.
Proof. exact (h1). Qed.
Lemma lem5237895 (s : real -> Prop) (h1 : term90 s) : term387 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5237894 s h1). Qed.
Lemma lem5237897 (p : Prop) : (term388 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5237898 (s : real -> Prop) : (term387 s) = (term90 s).
Proof. exact (@lem5237897 (s = (@EMPTY real))). Qed.
Lemma lem5237899 (s : real -> Prop) (h1 : term90 s) : term90 s.
Proof. exact (EQ_MP (@lem5237898 s) (@lem5237895 s h1)). Qed.
Lemma lem5237902 (s : real -> Prop) (h1 : term90 s) : term90 s.
Proof. exact (h1). Qed.
Lemma lem5237903 (s : real -> Prop) (h1 : term90 s) : term387 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5237902 s h1). Qed.
Lemma lem5237905 (p : Prop) : (term388 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5237906 (s : real -> Prop) : (term387 s) = (term90 s).
Proof. exact (@lem5237905 (s = (@EMPTY real))). Qed.
Lemma lem5237907 (s : real -> Prop) (h1 : term90 s) : term90 s.
Proof. exact (EQ_MP (@lem5237906 s) (@lem5237903 s h1)). Qed.
Lemma lem5237910 (x : type1021) (b : real) (s : real -> Prop) (h1 : term389 x b s) : term389 x b s.
Proof. exact (h1). Qed.
Lemma lem5237911 (x : type1021) (b : real) (s : real -> Prop) (h1 : term389 x b s) : term390 x b s.
Proof. exact (fun h0 : term346 x b s => @lem5237910 x b s h1). Qed.
Lemma lem5237913 (p : Prop) : (term388 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5237914 (x : type1021) (b : real) (s : real -> Prop) : (term390 x b s) = (term389 x b s).
Proof. exact (@lem5237913 (term346 x b s)). Qed.
Lemma lem5237915 (x : type1021) (b : real) (s : real -> Prop) (h1 : term389 x b s) : term389 x b s.
Proof. exact (EQ_MP (@lem5237914 x b s) (@lem5237911 x b s h1)). Qed.
Lemma lem5237917 (b : real) (s : real -> Prop) (h1 : term56 b s) : term52 b s.
Proof. exact (proj2 (@lem5237272 b s h1)). Qed.
Lemma lem5237918 (b : real) (s : real -> Prop) (h1 : term56 b s) : term391 b s.
Proof. exact (fun h0 : term24 b s => @lem5237917 b s h1). Qed.
Lemma lem5237920 (p : Prop) : (term388 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5237921 (b : real) (s : real -> Prop) : (term391 b s) = (term52 b s).
Proof. exact (@lem5237920 (term24 b s)). Qed.
Lemma lem5237922 (b : real) (s : real -> Prop) (h1 : term56 b s) : term52 b s.
Proof. exact (EQ_MP (@lem5237921 b s) (@lem5237918 b s h1)). Qed.
Lemma lem5237923 (x : type1021) (b : real) (s : real -> Prop) (h1 : term389 x b s) (h2 : term56 b s) : term411 x b s.
Proof. exact (conj (@lem5237915 x b s h1) (@lem5237922 b s h2)). Qed.
Lemma lem5237924 (x : type1021) (b : real) (s : real -> Prop) (h1 : term90 s) (h2 : term389 x b s) (h3 : term56 b s) : term412 x b s.
Proof. exact (conj (@lem5237907 s h1) (@lem5237923 x b s h2 h3)). Qed.
Lemma lem5237926 (_68644 : real) (_68645 : real) (_68643 : real -> Prop) (x : type1021) (h1 : term254 x) : term410 _68644 x _68645 _68643.
Proof. exact (EQ_MP (@lem5237825 _68644 x _68645 _68643) (@lem5237808 _68644 _68645 _68643 x h1)). Qed.
Lemma lem5237927 (b : real) (s : real -> Prop) (x : type1021) (h1 : term254 x) : term413 x b s.
Proof. exact (@lem5237926 b b s x h1). Qed.
Lemma lem5237930 (x : type1021) (b : real) (s : real -> Prop) (h1 : term254 x) (h2 : term90 s) (h3 : term389 x b s) (h4 : term56 b s) : term346 x b s.
Proof. exact (@lem5237927 b s x h1 (@lem5237924 x b s h2 h3 h4)). Qed.
Lemma lem5237931 (x : type1021) (b : real) (s : real -> Prop) (h1 : term254 x) (h2 : term90 s) (h3 : term56 b s) : term414 x b s.
Proof. exact (fun h0 : term389 x b s => @lem5237930 x b s h1 h2 h0 h3). Qed.
Lemma lem5237933 (p : Prop) : (term415 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5237934 (x : type1021) (b : real) (s : real -> Prop) : (term414 x b s) = (term346 x b s).
Proof. exact (@lem5237933 (term346 x b s)). Qed.
Lemma lem5237935 (x : type1021) (b : real) (s : real -> Prop) (h1 : term254 x) (h2 : term90 s) (h3 : term56 b s) : term346 x b s.
Proof. exact (EQ_MP (@lem5237934 x b s) (@lem5237931 x b s h1 h2 h3)). Qed.
Lemma lem5237937 (_68646 : real) (b : real) (s : real -> Prop) (h1 : term56 b s) : term25 s b _68646.
Proof. exact (EQ_MP (@lem5237879 s b _68646) (@lem5237868 _68646 b s h1)). Qed.
Lemma lem5237938 (x : type1021) (b : real) (s : real -> Prop) (h1 : term56 b s) : term425 x s b.
Proof. exact (@lem5237937 (x s b) b s h1). Qed.
Lemma lem5237941 (x : type1021) (b : real) (s : real -> Prop) (h1 : term254 x) (h2 : term90 s) (h3 : term56 b s) : term426 x s b.
Proof. exact (@lem5237938 x b s h3 (@lem5237935 x b s h1 h2 h3)). Qed.
Lemma lem5237942 (x : type1021) (b : real) (s : real -> Prop) (h1 : term254 x) (h2 : term90 s) (h3 : term56 b s) : term427 x s b.
Proof. exact (fun h0 : term347 x s b => @lem5237941 x b s h1 h2 h3). Qed.
Lemma lem5237944 (p : Prop) : (term415 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5237945 (x : type1021) (s : real -> Prop) (b : real) : (term427 x s b) = (term426 x s b).
Proof. exact (@lem5237944 (term426 x s b)). Qed.
Lemma lem5237946 (x : type1021) (b : real) (s : real -> Prop) (h1 : term254 x) (h2 : term90 s) (h3 : term56 b s) : term426 x s b.
Proof. exact (EQ_MP (@lem5237945 x s b) (@lem5237942 x b s h1 h2 h3)). Qed.
Lemma lem5237948 (b : real) (s : real -> Prop) (h1 : term56 b s) : term52 b s.
Proof. exact (proj2 (@lem5237272 b s h1)). Qed.
Lemma lem5237949 (b : real) (s : real -> Prop) (h1 : term56 b s) : term391 b s.
Proof. exact (fun h0 : term24 b s => @lem5237948 b s h1). Qed.
Lemma lem5237951 (p : Prop) : (term388 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5237952 (b : real) (s : real -> Prop) : (term391 b s) = (term52 b s).
Proof. exact (@lem5237951 (term24 b s)). Qed.
Lemma lem5237953 (b : real) (s : real -> Prop) (h1 : term56 b s) : term52 b s.
Proof. exact (EQ_MP (@lem5237952 b s) (@lem5237949 b s h1)). Qed.
Lemma lem5237981 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5237982 (x : type1021) (_68643 : real -> Prop) (_68645 : real) : (term356 x _68645 _68643) = (term428 x _68643 _68645).
Proof. exact (@lem5237981 (term24 _68645 _68643) (term347 x _68643 _68645)). Qed.
Lemma lem5237988 (x : type1021) (_68643 : real -> Prop) (_68644 : real) : (term429 x _68643 _68644) = (term429 x _68643 _68644).
Proof. exact (eq_refl (term429 x _68643 _68644)). Qed.
Lemma lem5237989 (_68644 : real) (x : type1021) (_68643 : real -> Prop) (_68645 : real) : (term430 _68644 x _68645 _68643) = (term431 _68644 x _68643 _68645).
Proof. exact (MK_COMB (@lem5237988 x _68643 _68644) (@lem5237982 x _68643 _68645)). Qed.
Lemma lem5237993 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5237994 (_68644 : real) (x : type1021) (_68643 : real -> Prop) (_68645 : real) : (term431 _68644 x _68643 _68645) = (term432 _68644 x _68643 _68645).
Proof. exact (@lem5237993 (term24 _68645 _68643) (term347 x _68643 _68644) (term347 x _68643 _68645)). Qed.
Lemma lem5238010 (_68644 : real) (x : type1021) (_68643 : real -> Prop) (_68645 : real) : (term430 _68644 x _68645 _68643) = (term432 _68644 x _68643 _68645).
Proof. exact (TRANS (@lem5237989 _68644 x _68643 _68645) (@lem5237994 _68644 x _68643 _68645)). Qed.
Lemma lem5238011 (_68643 : real -> Prop) : (term86 _68643) = (term86 _68643).
Proof. exact (eq_refl (term86 _68643)). Qed.
Lemma lem5238012 (_68644 : real) (x : type1021) (_68643 : real -> Prop) (_68645 : real) : (term384 _68644 x _68645 _68643) = (term433 _68644 x _68643 _68645).
Proof. exact (MK_COMB (@lem5238011 _68643) (@lem5238010 _68644 x _68643 _68645)). Qed.
Lemma lem5238023 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5238024 (_68644 : real) (x : type1021) (_68643 : real -> Prop) (_68645 : real) : (term434 _68644 x _68645 _68643) = (term435 _68644 x _68643 _68645).
Proof. exact (MK_COMB (@lem5238023) (@lem5238012 _68644 x _68643 _68645)). Qed.
Lemma lem5238028 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5238029 (x : type1021) (_68644 : real) (_68645 : real) (_68643 : real -> Prop) : (term436 x _68644 _68645 _68643) = (term437 x _68644 _68645 _68643).
Proof. exact (@lem5238028 (_68643 = (@EMPTY real)) (term347 x _68643 _68645) (term438 x _68644 _68645 _68643)). Qed.
Lemma lem5238045 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5238046 (_68644 : real) (x : type1021) (_68645 : real) (_68643 : real -> Prop) : (term439 x _68644 _68645 _68643) = (term430 _68644 x _68645 _68643).
Proof. exact (@lem5238045 (term347 x _68643 _68644) (term347 x _68643 _68645) (term24 _68645 _68643)). Qed.
Lemma lem5238060 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5238061 (x : type1021) (_68643 : real -> Prop) (_68645 : real) : (term356 x _68645 _68643) = (term428 x _68643 _68645).
Proof. exact (@lem5238060 (term24 _68645 _68643) (term347 x _68643 _68645)). Qed.
Lemma lem5238067 (x : type1021) (_68643 : real -> Prop) (_68644 : real) : (term429 x _68643 _68644) = (term429 x _68643 _68644).
Proof. exact (eq_refl (term429 x _68643 _68644)). Qed.
Lemma lem5238068 (_68644 : real) (x : type1021) (_68643 : real -> Prop) (_68645 : real) : (term430 _68644 x _68645 _68643) = (term431 _68644 x _68643 _68645).
Proof. exact (MK_COMB (@lem5238067 x _68643 _68644) (@lem5238061 x _68643 _68645)). Qed.
Lemma lem5238072 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5238073 (_68644 : real) (x : type1021) (_68643 : real -> Prop) (_68645 : real) : (term431 _68644 x _68643 _68645) = (term432 _68644 x _68643 _68645).
Proof. exact (@lem5238072 (term24 _68645 _68643) (term347 x _68643 _68644) (term347 x _68643 _68645)). Qed.
Lemma lem5238089 (_68644 : real) (x : type1021) (_68643 : real -> Prop) (_68645 : real) : (term430 _68644 x _68645 _68643) = (term432 _68644 x _68643 _68645).
Proof. exact (TRANS (@lem5238068 _68644 x _68643 _68645) (@lem5238073 _68644 x _68643 _68645)). Qed.
Lemma lem5238090 (_68644 : real) (x : type1021) (_68643 : real -> Prop) (_68645 : real) : (term439 x _68644 _68645 _68643) = (term432 _68644 x _68643 _68645).
Proof. exact (TRANS (@lem5238046 _68644 x _68645 _68643) (@lem5238089 _68644 x _68643 _68645)). Qed.
Lemma lem5238091 (_68643 : real -> Prop) : (term86 _68643) = (term86 _68643).
Proof. exact (eq_refl (term86 _68643)). Qed.
Lemma lem5238092 (_68644 : real) (x : type1021) (_68643 : real -> Prop) (_68645 : real) : (term437 x _68644 _68645 _68643) = (term433 _68644 x _68643 _68645).
Proof. exact (MK_COMB (@lem5238091 _68643) (@lem5238090 _68644 x _68643 _68645)). Qed.
Lemma lem5238103 (_68644 : real) (x : type1021) (_68643 : real -> Prop) (_68645 : real) : (term436 x _68644 _68645 _68643) = (term433 _68644 x _68643 _68645).
Proof. exact (TRANS (@lem5238029 x _68644 _68645 _68643) (@lem5238092 _68644 x _68643 _68645)). Qed.
Lemma lem5238104 (_68644 : real) (x : type1021) (_68643 : real -> Prop) (_68645 : real) : ((term384 _68644 x _68645 _68643) = (term436 x _68644 _68645 _68643)) = ((term433 _68644 x _68643 _68645) = (term433 _68644 x _68643 _68645)).
Proof. exact (MK_COMB (@lem5238024 _68644 x _68643 _68645) (@lem5238103 _68644 x _68643 _68645)). Qed.
Lemma lem5238106 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5238107 (x : Prop) : (x = x) = True.
Proof. exact (@lem5238106 Prop x). Qed.
Lemma lem5238108 (_68644 : real) (x : type1021) (_68643 : real -> Prop) (_68645 : real) : ((term433 _68644 x _68643 _68645) = (term433 _68644 x _68643 _68645)) = True.
Proof. exact (@lem5238107 (term433 _68644 x _68643 _68645)). Qed.
Lemma lem5238109 (x : type1021) (_68644 : real) (_68645 : real) (_68643 : real -> Prop) : ((term384 _68644 x _68645 _68643) = (term436 x _68644 _68645 _68643)) = True.
Proof. exact (TRANS (@lem5238104 _68644 x _68643 _68645) (@lem5238108 _68644 x _68643 _68645)). Qed.
Lemma lem5238110 (x : type1021) (_68644 : real) (_68645 : real) (_68643 : real -> Prop) : True = ((term384 _68644 x _68645 _68643) = (term436 x _68644 _68645 _68643)).
Proof. exact (SYM (@lem5238109 x _68644 _68645 _68643)). Qed.
Lemma lem5238111 (x : type1021) (_68644 : real) (_68645 : real) (_68643 : real -> Prop) : (term384 _68644 x _68645 _68643) = (term436 x _68644 _68645 _68643).
Proof. exact (EQ_MP (@lem5238110 x _68644 _68645 _68643) (@lem0)). Qed.
Lemma lem5238112 (_68644 : real) (_68645 : real) (_68643 : real -> Prop) (x : type1021) (h1 : term254 x) : term436 x _68644 _68645 _68643.
Proof. exact (EQ_MP (@lem5238111 x _68644 _68645 _68643) (@lem5237567 _68644 _68645 _68643 x h1)). Qed.
Lemma lem5238114 (b : Prop) (a : Prop) : (a \/ b) = (term398 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5238115 (_68644 : real) (x : type1021) (_68643 : real -> Prop) (_68645 : real) : (term436 x _68644 _68645 _68643) = (term440 _68644 x _68643 _68645).
Proof. exact (@lem5238114 (term441 x _68644 _68645 _68643) (term347 x _68643 _68645)). Qed.
Lemma lem5238117 (a : Prop) (b : Prop) : (term401 a b) = (term402 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5238118 (x : type1021) (_68644 : real) (_68645 : real) (_68643 : real -> Prop) : (term442 x _68644 _68645 _68643) = (term443 x _68644 _68645 _68643).
Proof. exact (@lem5238117 (_68643 = (@EMPTY real)) (term438 x _68644 _68645 _68643)). Qed.
Lemma lem5238120 (a : Prop) (b : Prop) : (term401 a b) = (term402 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5238121 (x : type1021) (_68644 : real) (_68645 : real) (_68643 : real -> Prop) : (term444 x _68644 _68645 _68643) = (term445 x _68644 _68645 _68643).
Proof. exact (@lem5238120 (term347 x _68643 _68644) (term24 _68645 _68643)). Qed.
Lemma lem5238123 (a : Prop) : (term421 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5238124 (x : type1021) (_68643 : real -> Prop) (_68644 : real) : (term446 x _68643 _68644) = (term426 x _68643 _68644).
Proof. exact (@lem5238123 (term426 x _68643 _68644)). Qed.
Lemma lem5238125 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5238126 (x : type1021) (_68643 : real -> Prop) (_68644 : real) : (term447 x _68643 _68644) = (term448 x _68643 _68644).
Proof. exact (MK_COMB (@lem5238125) (@lem5238124 x _68643 _68644)). Qed.
Lemma lem5238127 (_68645 : real) (_68643 : real -> Prop) : (term52 _68645 _68643) = (term52 _68645 _68643).
Proof. exact (eq_refl (term52 _68645 _68643)). Qed.
Lemma lem5238128 (x : type1021) (_68644 : real) (_68645 : real) (_68643 : real -> Prop) : (term445 x _68644 _68645 _68643) = (term449 x _68644 _68645 _68643).
Proof. exact (MK_COMB (@lem5238126 x _68643 _68644) (@lem5238127 _68645 _68643)). Qed.
Lemma lem5238129 (x : type1021) (_68644 : real) (_68645 : real) (_68643 : real -> Prop) : (term444 x _68644 _68645 _68643) = (term449 x _68644 _68645 _68643).
Proof. exact (TRANS (@lem5238121 x _68644 _68645 _68643) (@lem5238128 x _68644 _68645 _68643)). Qed.
Lemma lem5238130 (_68643 : real -> Prop) : (term39 _68643) = (term39 _68643).
Proof. exact (eq_refl (term39 _68643)). Qed.
Lemma lem5238131 (x : type1021) (_68644 : real) (_68645 : real) (_68643 : real -> Prop) : (term443 x _68644 _68645 _68643) = (term450 x _68644 _68645 _68643).
Proof. exact (MK_COMB (@lem5238130 _68643) (@lem5238129 x _68644 _68645 _68643)). Qed.
Lemma lem5238132 (x : type1021) (_68644 : real) (_68645 : real) (_68643 : real -> Prop) : (term442 x _68644 _68645 _68643) = (term450 x _68644 _68645 _68643).
Proof. exact (TRANS (@lem5238118 x _68644 _68645 _68643) (@lem5238131 x _68644 _68645 _68643)). Qed.
Lemma lem5238133 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5238134 (x : type1021) (_68644 : real) (_68645 : real) (_68643 : real -> Prop) : (term451 x _68644 _68645 _68643) = (term452 x _68644 _68645 _68643).
Proof. exact (MK_COMB (@lem5238133) (@lem5238132 x _68644 _68645 _68643)). Qed.
Lemma lem5238135 (x : type1021) (_68643 : real -> Prop) (_68645 : real) : (term347 x _68643 _68645) = (term347 x _68643 _68645).
Proof. exact (eq_refl (term347 x _68643 _68645)). Qed.
Lemma lem5238136 (_68644 : real) (x : type1021) (_68643 : real -> Prop) (_68645 : real) : (term440 _68644 x _68643 _68645) = (term453 _68644 x _68643 _68645).
Proof. exact (MK_COMB (@lem5238134 x _68644 _68645 _68643) (@lem5238135 x _68643 _68645)). Qed.
Lemma lem5238137 (_68644 : real) (x : type1021) (_68643 : real -> Prop) (_68645 : real) : (term436 x _68644 _68645 _68643) = (term453 _68644 x _68643 _68645).
Proof. exact (TRANS (@lem5238115 _68644 x _68643 _68645) (@lem5238136 _68644 x _68643 _68645)). Qed.
Lemma lem5238139 (x : type1021) (b : real) (s : real -> Prop) (h1 : term254 x) (h2 : term90 s) (h3 : term56 b s) : term454 x b s.
Proof. exact (conj (@lem5237946 x b s h1 h2 h3) (@lem5237953 b s h3)). Qed.
Lemma lem5238140 (x : type1021) (b : real) (s : real -> Prop) (h1 : term254 x) (h2 : term90 s) (h3 : term56 b s) : term455 x b s.
Proof. exact (conj (@lem5237899 s h2) (@lem5238139 x b s h1 h2 h3)). Qed.
Lemma lem5238142 (_68644 : real) (_68643 : real -> Prop) (_68645 : real) (x : type1021) (h1 : term254 x) : term453 _68644 x _68643 _68645.
Proof. exact (EQ_MP (@lem5238137 _68644 x _68643 _68645) (@lem5238112 _68644 _68645 _68643 x h1)). Qed.
Lemma lem5238143 (s : real -> Prop) (b : real) (x : type1021) (h1 : term254 x) : term456 x s b.
Proof. exact (@lem5238142 b s b x h1). Qed.
Lemma lem5238146 (x : type1021) (b : real) (s : real -> Prop) (h1 : term254 x) (h2 : term90 s) (h3 : term56 b s) : term347 x s b.
Proof. exact (@lem5238143 s b x h1 (@lem5238140 x b s h1 h2 h3)). Qed.
Lemma lem5238147 (x : type1021) (b : real) (s : real -> Prop) (h1 : term254 x) (h2 : term90 s) (h3 : term56 b s) : term457 x s b.
Proof. exact (fun h0 : term426 x s b => @lem5238146 x b s h1 h2 h3). Qed.
Lemma lem5238149 (p : Prop) : (term388 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5238150 (x : type1021) (s : real -> Prop) (b : real) : (term457 x s b) = (term347 x s b).
Proof. exact (@lem5238149 (term426 x s b)). Qed.
Lemma lem5238151 (x : type1021) (b : real) (s : real -> Prop) (h1 : term254 x) (h2 : term90 s) (h3 : term56 b s) : term347 x s b.
Proof. exact (EQ_MP (@lem5238150 x s b) (@lem5238147 x b s h1 h2 h3)). Qed.
Lemma lem5238153 (b : Prop) (a : Prop) : (a \/ b) = (term398 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5238156 (b : real) (_68646 : real) (s : real -> Prop) : (term48 s b _68646) = (term458 b _68646 s).
Proof. exact (@lem5238153 (real_le b _68646) (term417 _68646 s)). Qed.
Lemma lem5238159 (_68646 : real) (b : real) (s : real -> Prop) (h1 : term56 b s) : term458 b _68646 s.
Proof. exact (EQ_MP (@lem5238156 b _68646 s) (@lem5237535 _68646 b s h1)). Qed.
Lemma lem5238160 (x : type1021) (b : real) (s : real -> Prop) (h1 : term56 b s) : term459 x b s.
Proof. exact (@lem5238159 (x s b) b s h1). Qed.
Lemma lem5238163 (x : type1021) (b : real) (s : real -> Prop) (h1 : term254 x) (h2 : term90 s) (h3 : term56 b s) : term389 x b s.
Proof. exact (@lem5238160 x b s h3 (@lem5238151 x b s h1 h2 h3)). Qed.
Lemma lem5238164 (x : type1021) (b : real) (s : real -> Prop) (h1 : term254 x) (h2 : term90 s) (h3 : term56 b s) : term390 x b s.
Proof. exact (fun h0 : term346 x b s => @lem5238163 x b s h1 h2 h3). Qed.
Lemma lem5238166 (p : Prop) : (term388 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5238167 (x : type1021) (b : real) (s : real -> Prop) : (term390 x b s) = (term389 x b s).
Proof. exact (@lem5238166 (term346 x b s)). Qed.
Lemma lem5238168 (x : type1021) (b : real) (s : real -> Prop) (h1 : term254 x) (h2 : term90 s) (h3 : term56 b s) : term389 x b s.
Proof. exact (EQ_MP (@lem5238167 x b s) (@lem5238164 x b s h1 h2 h3)). Qed.
Lemma lem5238170 (b : real) (s : real -> Prop) (h1 : term56 b s) : term52 b s.
Proof. exact (proj2 (@lem5237272 b s h1)). Qed.
Lemma lem5238171 (b : real) (s : real -> Prop) (h1 : term56 b s) : term391 b s.
Proof. exact (fun h0 : term24 b s => @lem5238170 b s h1). Qed.
Lemma lem5238173 (p : Prop) : (term388 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5238174 (b : real) (s : real -> Prop) : (term391 b s) = (term52 b s).
Proof. exact (@lem5238173 (term24 b s)). Qed.
Lemma lem5238175 (b : real) (s : real -> Prop) (h1 : term56 b s) : term52 b s.
Proof. exact (EQ_MP (@lem5238174 b s) (@lem5238171 b s h1)). Qed.
Lemma lem5238177 (b : Prop) (a : Prop) : (a \/ b) = (term398 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5238178 (_68644 : real) (x : type1021) (_68645 : real) (_68643 : real -> Prop) : (term386 _68644 x _68645 _68643) = (term460 _68644 x _68645 _68643).
Proof. exact (@lem5238177 (term461 _68644 x _68645 _68643) (_68643 = (@EMPTY real))). Qed.
Lemma lem5238180 (a : Prop) (b : Prop) : (term401 a b) = (term402 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5238181 (_68644 : real) (x : type1021) (_68645 : real) (_68643 : real -> Prop) : (term462 _68644 x _68645 _68643) = (term463 _68644 x _68645 _68643).
Proof. exact (@lem5238180 (term347 x _68643 _68644) (term355 x _68645 _68643)). Qed.
Lemma lem5238183 (a : Prop) : (term421 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5238184 (x : type1021) (_68643 : real -> Prop) (_68644 : real) : (term446 x _68643 _68644) = (term426 x _68643 _68644).
Proof. exact (@lem5238183 (term426 x _68643 _68644)). Qed.
Lemma lem5238185 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5238186 (x : type1021) (_68643 : real -> Prop) (_68644 : real) : (term447 x _68643 _68644) = (term448 x _68643 _68644).
Proof. exact (MK_COMB (@lem5238185) (@lem5238184 x _68643 _68644)). Qed.
Lemma lem5238188 (a : Prop) (b : Prop) : (term401 a b) = (term402 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5238189 (x : type1021) (_68645 : real) (_68643 : real -> Prop) : (term464 x _68645 _68643) = (term411 x _68645 _68643).
Proof. exact (@lem5238188 (term346 x _68645 _68643) (term24 _68645 _68643)). Qed.
Lemma lem5238190 (_68644 : real) (x : type1021) (_68645 : real) (_68643 : real -> Prop) : (term463 _68644 x _68645 _68643) = (term465 _68644 x _68645 _68643).
Proof. exact (MK_COMB (@lem5238186 x _68643 _68644) (@lem5238189 x _68645 _68643)). Qed.
Lemma lem5238191 (_68644 : real) (x : type1021) (_68645 : real) (_68643 : real -> Prop) : (term462 _68644 x _68645 _68643) = (term465 _68644 x _68645 _68643).
Proof. exact (TRANS (@lem5238181 _68644 x _68645 _68643) (@lem5238190 _68644 x _68645 _68643)). Qed.
Lemma lem5238192 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5238193 (_68644 : real) (x : type1021) (_68645 : real) (_68643 : real -> Prop) : (term466 _68644 x _68645 _68643) = (term467 _68644 x _68645 _68643).
Proof. exact (MK_COMB (@lem5238192) (@lem5238191 _68644 x _68645 _68643)). Qed.
Lemma lem5238194 (_68643 : real -> Prop) : (_68643 = (@EMPTY real)) = (_68643 = (@EMPTY real)).
Proof. exact (eq_refl (_68643 = (@EMPTY real))). Qed.
Lemma lem5238195 (_68644 : real) (x : type1021) (_68645 : real) (_68643 : real -> Prop) : (term460 _68644 x _68645 _68643) = (term468 _68644 x _68645 _68643).
Proof. exact (MK_COMB (@lem5238193 _68644 x _68645 _68643) (@lem5238194 _68643)). Qed.
Lemma lem5238196 (_68644 : real) (x : type1021) (_68645 : real) (_68643 : real -> Prop) : (term386 _68644 x _68645 _68643) = (term468 _68644 x _68645 _68643).
Proof. exact (TRANS (@lem5238178 _68644 x _68645 _68643) (@lem5238195 _68644 x _68645 _68643)). Qed.
Lemma lem5238198 (x : type1021) (b : real) (s : real -> Prop) (h1 : term254 x) (h2 : term90 s) (h3 : term56 b s) : term411 x b s.
Proof. exact (conj (@lem5238168 x b s h1 h2 h3) (@lem5238175 b s h3)). Qed.
Lemma lem5238199 (x : type1021) (b : real) (s : real -> Prop) (h1 : term254 x) (h2 : term90 s) (h3 : term56 b s) : term469 x b s.
Proof. exact (conj (@lem5237891 x b s h1 h2 h3) (@lem5238198 x b s h1 h2 h3)). Qed.
Lemma lem5238201 (_68644 : real) (_68645 : real) (_68643 : real -> Prop) (x : type1021) (h1 : term254 x) : term468 _68644 x _68645 _68643.
Proof. exact (EQ_MP (@lem5238196 _68644 x _68645 _68643) (@lem5237599 _68644 _68645 _68643 x h1)). Qed.
Lemma lem5238202 (b : real) (s : real -> Prop) (x : type1021) (h1 : term254 x) : term470 x b s.
Proof. exact (@lem5238201 b b s x h1). Qed.
Lemma lem5238205 (x : type1021) (b : real) (s : real -> Prop) (h1 : term254 x) (h2 : term90 s) (h3 : term56 b s) : s = (@EMPTY real).
Proof. exact (@lem5238202 b s x h1 (@lem5238199 x b s h1 h2 h3)). Qed.
Lemma lem5238206 (x : type1021) (b : real) (s : real -> Prop) (h1 : term254 x) (h2 : term56 b s) : term471 s.
Proof. exact (fun h0 : term90 s => @lem5238205 x b s h1 h0 h2). Qed.
Lemma lem5238208 (p : Prop) : (term415 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5238209 (s : real -> Prop) : (term471 s) = (s = (@EMPTY real)).
Proof. exact (@lem5238208 (s = (@EMPTY real))). Qed.
Lemma lem5238210 (x : type1021) (b : real) (s : real -> Prop) (h1 : term254 x) (h2 : term56 b s) : s = (@EMPTY real).
Proof. exact (EQ_MP (@lem5238209 s) (@lem5238206 x b s h1 h2)). Qed.
Lemma lem5238213 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5238215 (s : real -> Prop) : (term90 s) = (term472 s).
Proof. exact (@lem5238213 (s = (@EMPTY real))). Qed.
Lemma lem5238218 (b : real) (s : real -> Prop) (h1 : term56 b s) : term472 s.
Proof. exact (EQ_MP (@lem5238215 s) (@lem5237529 b s h1)). Qed.
Lemma lem5238221 (x : type1021) (b : real) (s : real -> Prop) (h1 : term254 x) (h2 : term56 b s) : False.
Proof. exact (@lem5238218 b s h2 (@lem5238210 x b s h1 h2)). Qed.
Lemma lem5238222 (x : type1021) (b : real) (s : real -> Prop) (h1 : term254 x) (h2 : term56 b s) : term473.
Proof. exact (fun h0 : ~ False => @lem5238221 x b s h1 h2). Qed.
Lemma lem5238224 (p : Prop) : (term415 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5238225 : term473 = False.
Proof. exact (@lem5238224 False). Qed.
Lemma lem5238226 (x : type1021) (b : real) (s : real -> Prop) (h1 : term254 x) (h2 : term56 b s) : False.
Proof. exact (EQ_MP (@lem5238225) (@lem5238222 x b s h1 h2)). Qed.
Lemma lem5238227 (x : type1021) (b : real) (s : real -> Prop) (h1 : term254 x) (h2 : term56 b s) : (term56 b s) = False.
Proof. exact (prop_ext (fun h3 : term56 b s => @lem5238226 x b s h1 h2) (fun h3 : False => @lem5237272 b s h2)). Qed.
Lemma lem5238228 (x : type1021) (b : real) (s : real -> Prop) (h1 : term254 x) (h2 : term56 b s) : False.
Proof. exact (EQ_MP (@lem5238227 x b s h1 h2) (@lem5237272 b s h2)). Qed.
Lemma lem5238229 (x : type1021) (b : real) (s : real -> Prop) (h1 : term254 x) (h2 : term56 b s) : (term254 x) = False.
Proof. exact (prop_ext (fun h3 : term254 x => @lem5238228 x b s h1 h2) (fun h3 : False => @lem5237231 x h1)). Qed.
Lemma lem5238230 (x : type1021) (b : real) (s : real -> Prop) (h1 : term254 x) (h2 : term56 b s) : False.
Proof. exact (EQ_MP (@lem5238229 x b s h1 h2) (@lem5237231 x h1)). Qed.
Lemma lem5238231 (x : type1021) (s : real -> Prop) (h1 : term254 x) (h2 : term10 s) : False.
Proof. exact (ex_elim (@lem5236600 s h2) (fun b : real => fun h0 : term64 s b => @lem5238230 x b s h1 h0)). Qed.
Lemma lem5238232 (s : real -> Prop) (h1 : term17) (h2 : term10 s) : False.
Proof. exact (ex_elim (@lem5237129 h1) (fun x : type1021 => fun h0 : term256 x => @lem5238231 x s h0 h2)). Qed.
Lemma lem5238233 (s : real -> Prop) (h1 : term10 s) : term15.
Proof. exact (fun h0 : term17 => @lem5238232 s h0 h1). Qed.
Lemma lem5238234 : term15 = term16.
Proof. exact (@lem69 term17). Qed.
Lemma lem5238235 (s : real -> Prop) (h1 : term10 s) : term16.
Proof. exact (EQ_MP (@lem5238234) (@lem5238233 s h1)). Qed.
Lemma lem5238236 (s : real -> Prop) : term19 s.
Proof. exact (fun h0 : term10 s => @lem5238235 s h0). Qed.
Lemma lem5238241 : term23.
Proof. exact (fun s : real -> Prop => @lem5238236 s). Qed.
Lemma lem5238242 : term22.
Proof. exact (EQ_MP (@lem5236467) (@lem5238241)). Qed.
Lemma lem5238243 (s : real -> Prop) : term474 s.
Proof. exact (@lem5238242 s). Qed.
Lemma lem5238244 (s : real -> Prop) : (term474 s) = (term11 s).
Proof. exact (eq_refl (term474 s)). Qed.
Lemma lem5238245 (s : real -> Prop) : term11 s.
Proof. exact (EQ_MP (@lem5238244 s) (@lem5238243 s)). Qed.
Lemma lem5238247 (s : real -> Prop) : term11 s.
Proof. exact (@lem5236231 s (@lem5238245 s)). Qed.
Lemma lem5238248 (s : real -> Prop) (h1 : term10 s) : term15.
Proof. exact (@lem5238247 s (@lem5236216 s h1)). Qed.
Lemma lem5238249 (s : real -> Prop) (h1 : term10 s) : False.
Proof. exact (@lem5238248 s h1 (@lem5214027)). Qed.
Lemma lem5238250 (s : real -> Prop) (h1 : term10 s) : (term10 s) = False.
Proof. exact (prop_ext (fun h2 : term10 s => @lem5238249 s h1) (fun h2 : False => @lem5236216 s h1)). Qed.
Lemma lem5238251 (s : real -> Prop) (h1 : term10 s) : False.
Proof. exact (EQ_MP (@lem5238250 s h1) (@lem5236216 s h1)). Qed.
Lemma lem5238252 (s : real -> Prop) : term9 s.
Proof. exact (fun h0 : term10 s => @lem5238251 s h0). Qed.
Lemma lem5238253 (s : real -> Prop) : term8 s.
Proof. exact (EQ_MP (@lem5236215 s) (@lem5238252 s)). Qed.
