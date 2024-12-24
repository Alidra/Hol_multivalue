Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HAS_SUP_APPROACH_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import HAS_SUP_SUP_spec.
Require Import SUP_APPROACH_spec.
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
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
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
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem5308186 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5308187 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem5308188 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem5308187 t1) (@lem5308186 t1)). Qed.
Lemma lem5308189 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem5308188 t1 t2). Qed.
Lemma lem5308190 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem5308191 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem5308190 t1 t2) (@lem5308189 t1 t2)). Qed.
Lemma lem5308192 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem5308191 t1 t2 t3). Qed.
Lemma lem5308193 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem5308194 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem5308193 t1 t2 t3) (@lem5308192 t1 t2 t3)). Qed.
Lemma lem5308195 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem5308194 t1 t2 t3)). Qed.
Lemma lem5308196 (s : real -> Prop) : term7 s.
Proof. exact (@lem5297166 s). Qed.
Lemma lem5308197 (s : real -> Prop) : (term7 s) = (term8 s).
Proof. exact (eq_refl (term7 s)). Qed.
Lemma lem5308198 (s : real -> Prop) : term8 s.
Proof. exact (EQ_MP (@lem5308197 s) (@lem5308196 s)). Qed.
Lemma lem5308199 (s : real -> Prop) (l : real) : term9 s l.
Proof. exact (@lem5308198 s l). Qed.
Lemma lem5308200 (s : real -> Prop) (l : real) : (term9 s l) = ((has_sup s l) = (term10 s l)).
Proof. exact (eq_refl (term9 s l)). Qed.
Lemma lem5308219 (s : real -> Prop) (l : real) : (has_sup s l) = (term10 s l).
Proof. exact (EQ_MP (@lem5308200 s l) (@lem5308199 s l)). Qed.
Lemma lem5308238 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5308239 (s : real -> Prop) (l : real) : (term11 s l) = (term12 s l).
Proof. exact (MK_COMB (@lem5308238) (@lem5308219 s l)). Qed.
Lemma lem5308240 (c : real) (l : real) : (real_lt c l) = (real_lt c l).
Proof. exact (eq_refl (real_lt c l)). Qed.
Lemma lem5308241 (s : real -> Prop) (c : real) (l : real) : (term13 s c l) = (term14 s c l).
Proof. exact (MK_COMB (@lem5308239 s l) (@lem5308240 c l)). Qed.
Lemma lem5308244 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5308245 (s : real -> Prop) (c : real) (l : real) : (term15 s c l) = (term16 s c l).
Proof. exact (MK_COMB (@lem5308244) (@lem5308241 s c l)). Qed.
Lemma lem5308252 (s : real -> Prop) (c : real) : (term17 s c) = (term17 s c).
Proof. exact (eq_refl (term17 s c)). Qed.
Lemma lem5308253 (l : real) (s : real -> Prop) (c : real) : (term18 l s c) = (term19 l s c).
Proof. exact (MK_COMB (@lem5308245 s c l) (@lem5308252 s c)). Qed.
Lemma lem5308256 (l : real) (s : real -> Prop) : (term20 l s) = (term21 l s).
Proof. exact (fun_ext (fun c : real => @lem5308253 l s c)). Qed.
Lemma lem5308257 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5308258 (l : real) (s : real -> Prop) : (term22 l s) = (term23 l s).
Proof. exact (MK_COMB (@lem5308257) (@lem5308256 l s)). Qed.
Lemma lem5308263 (s : real -> Prop) : (term24 s) = (term25 s).
Proof. exact (fun_ext (fun l : real => @lem5308258 l s)). Qed.
Lemma lem5308264 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5308265 (s : real -> Prop) : (term26 s) = (term27 s).
Proof. exact (MK_COMB (@lem5308264) (@lem5308263 s)). Qed.
Lemma lem5308270 : term28 = term29.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5308265 s)). Qed.
Lemma lem5308271 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5308272 : term30 = term31.
Proof. exact (MK_COMB (@lem5308271) (@lem5308270)). Qed.
Lemma lem5308277 : term31 = term30.
Proof. exact (SYM (@lem5308272)). Qed.
Lemma lem5308279 (p : Prop) : p = (term32 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5308280 : term31 = term33.
Proof. exact (@lem5308279 term31). Qed.
Lemma lem5308281 : term33 = term31.
Proof. exact (SYM (@lem5308280)). Qed.
Lemma lem5308282 (h1 : term34) : term34.
Proof. exact (h1). Qed.
Lemma lem5308285 (h1 : term35) : term35.
Proof. exact (h1). Qed.
Lemma lem5308286 : term36.
Proof. exact (fun h0 : term35 => @lem5308285 h0). Qed.
Lemma lem5308287 (h1 : term36) : term36.
Proof. exact (h1). Qed.
Lemma lem5308288 (h1 : term35) : term35.
Proof. exact (h1). Qed.
Lemma lem5308289 (h1 : term35) (h2 : term36) : term35.
Proof. exact (@lem5308287 h2 (@lem5308288 h1)). Qed.
Lemma lem5308290 (h1 : term35) : term37.
Proof. exact (fun h0 : term36 => @lem5308289 h1 h0). Qed.
Lemma lem5308291 (h1 : term36) : term36.
Proof. exact (h1). Qed.
Lemma lem5308292 (h1 : term35) (h2 : term36) : term35.
Proof. exact (@lem5308290 h1 (@lem5308291 h2)). Qed.
Lemma lem5308293 (h1 : term36) : term36.
Proof. exact (fun h0 : term35 => @lem5308292 h0 h1). Qed.
Lemma lem5308294 : term38.
Proof. exact (fun h0 : term36 => @lem5308293 h0). Qed.
Lemma lem5308297 : term36.
Proof. exact (@lem5308294 (@lem5308286)). Qed.
Lemma lem5308381 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5308382 : term39 = term40.
Proof. exact (@lem5308381 term41). Qed.
Lemma lem5308457 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem5308464 : term35 = term43.
Proof. exact (MK_COMB (@lem5308457) (@lem5308382)). Qed.
Lemma lem5308469 (s : real -> Prop) (c : real) (x : real) : (term44 s c x) = (term44 s c x).
Proof. exact (eq_refl (term44 s c x)). Qed.
Lemma lem5308470 (s : real -> Prop) (c : real) : (term45 s c) = (term45 s c).
Proof. exact (fun_ext (fun x : real => @lem5308469 s c x)). Qed.
Lemma lem5308471 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5308472 (s : real -> Prop) (c : real) : (term17 s c) = (term17 s c).
Proof. exact (MK_COMB (@lem5308471) (@lem5308470 s c)). Qed.
Lemma lem5308473 (c : real) (s : real -> Prop) : (term46 c s) = (term46 c s).
Proof. exact (eq_refl (term46 c s)). Qed.
Lemma lem5308478 (s : real -> Prop) (x : real) (b : real) : (term47 s x b) = (term47 s x b).
Proof. exact (eq_refl (term47 s x b)). Qed.
Lemma lem5308479 (s : real -> Prop) (b : real) : (term48 s b) = (term48 s b).
Proof. exact (fun_ext (fun x : real => @lem5308478 s x b)). Qed.
Lemma lem5308480 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5308481 (s : real -> Prop) (b : real) : (term49 s b) = (term49 s b).
Proof. exact (MK_COMB (@lem5308480) (@lem5308479 s b)). Qed.
Lemma lem5308482 (s : real -> Prop) : (term50 s) = (term50 s).
Proof. exact (fun_ext (fun b : real => @lem5308481 s b)). Qed.
Lemma lem5308483 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5308484 (s : real -> Prop) : (term51 s) = (term51 s).
Proof. exact (MK_COMB (@lem5308483) (@lem5308482 s)). Qed.
Lemma lem5308485 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5308486 (s : real -> Prop) : (term52 s) = (term52 s).
Proof. exact (MK_COMB (@lem5308485) (@lem5308484 s)). Qed.
Lemma lem5308487 (c : real) (s : real -> Prop) : (term53 c s) = (term53 c s).
Proof. exact (MK_COMB (@lem5308486 s) (@lem5308473 c s)). Qed.
Lemma lem5308492 (s : real -> Prop) : (term54 s) = (term54 s).
Proof. exact (eq_refl (term54 s)). Qed.
Lemma lem5308493 (c : real) (s : real -> Prop) : (term55 c s) = (term55 c s).
Proof. exact (MK_COMB (@lem5308492 s) (@lem5308487 c s)). Qed.
Lemma lem5308494 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5308495 (c : real) (s : real -> Prop) : (term56 c s) = (term56 c s).
Proof. exact (MK_COMB (@lem5308494) (@lem5308493 c s)). Qed.
Lemma lem5308496 (s : real -> Prop) (c : real) : (term57 s c) = (term57 s c).
Proof. exact (MK_COMB (@lem5308495 c s) (@lem5308472 s c)). Qed.
Lemma lem5308497 (s : real -> Prop) : (term58 s) = (term58 s).
Proof. exact (fun_ext (fun c : real => @lem5308496 s c)). Qed.
Lemma lem5308498 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5308499 (s : real -> Prop) : (term59 s) = (term59 s).
Proof. exact (MK_COMB (@lem5308498) (@lem5308497 s)). Qed.
Lemma lem5308500 : term60 = term60.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5308499 s)). Qed.
Lemma lem5308501 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5308502 : term41 = term41.
Proof. exact (MK_COMB (@lem5308501) (@lem5308500)). Qed.
Lemma lem5308503 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5308504 : term40 = term40.
Proof. exact (MK_COMB (@lem5308503) (@lem5308502)). Qed.
Lemma lem5308509 (s : real -> Prop) (c : real) (x : real) : (term44 s c x) = (term44 s c x).
Proof. exact (eq_refl (term44 s c x)). Qed.
Lemma lem5308510 (s : real -> Prop) (c : real) : (term45 s c) = (term45 s c).
Proof. exact (fun_ext (fun x : real => @lem5308509 s c x)). Qed.
Lemma lem5308511 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5308512 (s : real -> Prop) (c : real) : (term17 s c) = (term17 s c).
Proof. exact (MK_COMB (@lem5308511) (@lem5308510 s c)). Qed.
Lemma lem5308513 (c : real) (l : real) : (real_lt c l) = (real_lt c l).
Proof. exact (eq_refl (real_lt c l)). Qed.
Lemma lem5308514 (s : real -> Prop) (l : real) : ((sup s) = l) = ((sup s) = l).
Proof. exact (eq_refl ((sup s) = l)). Qed.
Lemma lem5308519 (s : real -> Prop) (x : real) (b : real) : (term47 s x b) = (term47 s x b).
Proof. exact (eq_refl (term47 s x b)). Qed.
Lemma lem5308520 (s : real -> Prop) (b : real) : (term48 s b) = (term48 s b).
Proof. exact (fun_ext (fun x : real => @lem5308519 s x b)). Qed.
Lemma lem5308521 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5308522 (s : real -> Prop) (b : real) : (term49 s b) = (term49 s b).
Proof. exact (MK_COMB (@lem5308521) (@lem5308520 s b)). Qed.
Lemma lem5308523 (s : real -> Prop) : (term50 s) = (term50 s).
Proof. exact (fun_ext (fun b : real => @lem5308522 s b)). Qed.
Lemma lem5308524 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5308525 (s : real -> Prop) : (term51 s) = (term51 s).
Proof. exact (MK_COMB (@lem5308524) (@lem5308523 s)). Qed.
Lemma lem5308526 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5308527 (s : real -> Prop) : (term52 s) = (term52 s).
Proof. exact (MK_COMB (@lem5308526) (@lem5308525 s)). Qed.
Lemma lem5308528 (s : real -> Prop) (l : real) : (term61 s l) = (term61 s l).
Proof. exact (MK_COMB (@lem5308527 s) (@lem5308514 s l)). Qed.
Lemma lem5308533 (s : real -> Prop) : (term54 s) = (term54 s).
Proof. exact (eq_refl (term54 s)). Qed.
Lemma lem5308534 (s : real -> Prop) (l : real) : (term10 s l) = (term10 s l).
Proof. exact (MK_COMB (@lem5308533 s) (@lem5308528 s l)). Qed.
Lemma lem5308535 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5308536 (s : real -> Prop) (l : real) : (term12 s l) = (term12 s l).
Proof. exact (MK_COMB (@lem5308535) (@lem5308534 s l)). Qed.
Lemma lem5308537 (s : real -> Prop) (c : real) (l : real) : (term14 s c l) = (term14 s c l).
Proof. exact (MK_COMB (@lem5308536 s l) (@lem5308513 c l)). Qed.
Lemma lem5308538 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5308539 (s : real -> Prop) (c : real) (l : real) : (term16 s c l) = (term16 s c l).
Proof. exact (MK_COMB (@lem5308538) (@lem5308537 s c l)). Qed.
Lemma lem5308540 (l : real) (s : real -> Prop) (c : real) : (term19 l s c) = (term19 l s c).
Proof. exact (MK_COMB (@lem5308539 s c l) (@lem5308512 s c)). Qed.
Lemma lem5308541 (l : real) (s : real -> Prop) : (term21 l s) = (term21 l s).
Proof. exact (fun_ext (fun c : real => @lem5308540 l s c)). Qed.
Lemma lem5308542 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5308543 (l : real) (s : real -> Prop) : (term23 l s) = (term23 l s).
Proof. exact (MK_COMB (@lem5308542) (@lem5308541 l s)). Qed.
Lemma lem5308544 (s : real -> Prop) : (term25 s) = (term25 s).
Proof. exact (fun_ext (fun l : real => @lem5308543 l s)). Qed.
Lemma lem5308545 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5308546 (s : real -> Prop) : (term27 s) = (term27 s).
Proof. exact (MK_COMB (@lem5308545) (@lem5308544 s)). Qed.
Lemma lem5308547 : term29 = term29.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5308546 s)). Qed.
Lemma lem5308548 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5308549 : term31 = term31.
Proof. exact (MK_COMB (@lem5308548) (@lem5308547)). Qed.
Lemma lem5308550 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5308551 : term34 = term34.
Proof. exact (MK_COMB (@lem5308550) (@lem5308549)). Qed.
Lemma lem5308552 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5308553 : term42 = term42.
Proof. exact (MK_COMB (@lem5308552) (@lem5308551)). Qed.
Lemma lem5308554 : term43 = term43.
Proof. exact (MK_COMB (@lem5308553) (@lem5308504)). Qed.
Lemma lem5308647 : term35 = term43.
Proof. exact (TRANS (@lem5308464) (@lem5308554)). Qed.
Lemma lem5308648 : term43 = term35.
Proof. exact (SYM (@lem5308647)). Qed.
Lemma lem5308649 (h1 : term34) : term34.
Proof. exact (h1). Qed.
Lemma lem5308650 (h1 : term41) : term41.
Proof. exact (h1). Qed.
Lemma lem5308658 (s : real -> Prop) (x : real) (b : real) : (term47 s x b) = (term62 s x b).
Proof. exact (@lem17265 (@IN real x s) (real_le x b)). Qed.
Lemma lem5308659 (s : real -> Prop) (b : real) : (term48 s b) = (term63 s b).
Proof. exact (fun_ext (fun x : real => @lem5308658 s x b)). Qed.
Lemma lem5308660 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5308661 (s : real -> Prop) (b : real) : (term49 s b) = (term64 s b).
Proof. exact (MK_COMB (@lem5308660) (@lem5308659 s b)). Qed.
Lemma lem5308662 (s : real -> Prop) : (term50 s) = (term65 s).
Proof. exact (fun_ext (fun b : real => @lem5308661 s b)). Qed.
Lemma lem5308663 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5308664 (s : real -> Prop) : (term51 s) = (term66 s).
Proof. exact (MK_COMB (@lem5308663) (@lem5308662 s)). Qed.
Lemma lem5308665 (s : real -> Prop) (l : real) : ((sup s) = l) = ((sup s) = l).
Proof. exact (eq_refl ((sup s) = l)). Qed.
Lemma lem5308666 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5308667 (s : real -> Prop) : (term52 s) = (term67 s).
Proof. exact (MK_COMB (@lem5308666) (@lem5308664 s)). Qed.
Lemma lem5308668 (s : real -> Prop) (l : real) : (term61 s l) = (term68 s l).
Proof. exact (MK_COMB (@lem5308667 s) (@lem5308665 s l)). Qed.
Lemma lem5308670 (s : real -> Prop) : (term54 s) = (term54 s).
Proof. exact (eq_refl (term54 s)). Qed.
Lemma lem5308671 (s : real -> Prop) (l : real) : (term10 s l) = (term69 s l).
Proof. exact (MK_COMB (@lem5308670 s) (@lem5308668 s l)). Qed.
Lemma lem5308672 (c : real) (l : real) : (real_lt c l) = (real_lt c l).
Proof. exact (eq_refl (real_lt c l)). Qed.
Lemma lem5308673 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5308674 (s : real -> Prop) (l : real) : (term12 s l) = (term70 s l).
Proof. exact (MK_COMB (@lem5308673) (@lem5308671 s l)). Qed.
Lemma lem5308675 (s : real -> Prop) (c : real) (l : real) : (term14 s c l) = (term71 s c l).
Proof. exact (MK_COMB (@lem5308674 s l) (@lem5308672 c l)). Qed.
Lemma lem5308682 (s : real -> Prop) (c : real) (x : real) : (term72 s c x) = (term73 s c x).
Proof. exact (@lem17045 (@IN real x s) (real_lt c x)). Qed.
Lemma lem5308683 (P : real -> Prop) : (term74 P) = (term75 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5308684 (s : real -> Prop) (c : real) : (term76 s c) = (term77 s c).
Proof. exact (@lem5308683 (term45 s c)). Qed.
Lemma lem5308685 (s : real -> Prop) (c : real) (x : real) : (term78 s c x) = (term44 s c x).
Proof. exact (eq_refl (term78 s c x)). Qed.
Lemma lem5308686 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5308687 (s : real -> Prop) (c : real) (x : real) : (term79 s c x) = (term72 s c x).
Proof. exact (MK_COMB (@lem5308686) (@lem5308685 s c x)). Qed.
Lemma lem5308688 (s : real -> Prop) (c : real) (x : real) : (term79 s c x) = (term73 s c x).
Proof. exact (TRANS (@lem5308687 s c x) (@lem5308682 s c x)). Qed.
Lemma lem5308689 (s : real -> Prop) (c : real) : (term80 s c) = (term81 s c).
Proof. exact (fun_ext (fun x : real => @lem5308688 s c x)). Qed.
Lemma lem5308690 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5308691 (s : real -> Prop) (c : real) : (term77 s c) = (term82 s c).
Proof. exact (MK_COMB (@lem5308690) (@lem5308689 s c)). Qed.
Lemma lem5308692 (s : real -> Prop) (c : real) : (term76 s c) = (term82 s c).
Proof. exact (TRANS (@lem5308684 s c) (@lem5308691 s c)). Qed.
Lemma lem5308693 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5308694 (s : real -> Prop) (c : real) (l : real) : (term83 s c l) = (term84 s c l).
Proof. exact (MK_COMB (@lem5308693) (@lem5308675 s c l)). Qed.
Lemma lem5308695 (l : real) (s : real -> Prop) (c : real) : (term85 l s c) = (term86 l s c).
Proof. exact (MK_COMB (@lem5308694 s c l) (@lem5308692 s c)). Qed.
Lemma lem5308696 (l : real) (s : real -> Prop) (c : real) : (term87 l s c) = (term85 l s c).
Proof. exact (@lem17362 (term14 s c l) (term17 s c)). Qed.
Lemma lem5308697 (l : real) (s : real -> Prop) (c : real) : (term87 l s c) = (term86 l s c).
Proof. exact (TRANS (@lem5308696 l s c) (@lem5308695 l s c)). Qed.
Lemma lem5308698 (P : real -> Prop) : (term88 P) = (term89 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5308699 (l : real) (s : real -> Prop) : (term90 l s) = (term91 l s).
Proof. exact (@lem5308698 (term21 l s)). Qed.
Lemma lem5308700 (l : real) (s : real -> Prop) (c : real) : (term92 l s c) = (term19 l s c).
Proof. exact (eq_refl (term92 l s c)). Qed.
Lemma lem5308701 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5308702 (l : real) (s : real -> Prop) (c : real) : (term93 l s c) = (term87 l s c).
Proof. exact (MK_COMB (@lem5308701) (@lem5308700 l s c)). Qed.
Lemma lem5308703 (l : real) (s : real -> Prop) (c : real) : (term93 l s c) = (term86 l s c).
Proof. exact (TRANS (@lem5308702 l s c) (@lem5308697 l s c)). Qed.
Lemma lem5308704 (l : real) (s : real -> Prop) : (term94 l s) = (term95 l s).
Proof. exact (fun_ext (fun c : real => @lem5308703 l s c)). Qed.
Lemma lem5308705 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5308706 (l : real) (s : real -> Prop) : (term91 l s) = (term96 l s).
Proof. exact (MK_COMB (@lem5308705) (@lem5308704 l s)). Qed.
Lemma lem5308707 (l : real) (s : real -> Prop) : (term90 l s) = (term96 l s).
Proof. exact (TRANS (@lem5308699 l s) (@lem5308706 l s)). Qed.
Lemma lem5308708 (P : real -> Prop) : (term88 P) = (term89 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5308709 (s : real -> Prop) : (term97 s) = (term98 s).
Proof. exact (@lem5308708 (term25 s)). Qed.
Lemma lem5308710 (l : real) (s : real -> Prop) : (term99 s l) = (term23 l s).
Proof. exact (eq_refl (term99 s l)). Qed.
Lemma lem5308711 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5308712 (l : real) (s : real -> Prop) : (term100 s l) = (term90 l s).
Proof. exact (MK_COMB (@lem5308711) (@lem5308710 l s)). Qed.
Lemma lem5308713 (l : real) (s : real -> Prop) : (term100 s l) = (term96 l s).
Proof. exact (TRANS (@lem5308712 l s) (@lem5308707 l s)). Qed.
Lemma lem5308714 (s : real -> Prop) : (term101 s) = (term102 s).
Proof. exact (fun_ext (fun l : real => @lem5308713 l s)). Qed.
Lemma lem5308715 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5308716 (s : real -> Prop) : (term98 s) = (term103 s).
Proof. exact (MK_COMB (@lem5308715) (@lem5308714 s)). Qed.
Lemma lem5308717 (s : real -> Prop) : (term97 s) = (term103 s).
Proof. exact (TRANS (@lem5308709 s) (@lem5308716 s)). Qed.
Lemma lem5308718 (P : type1022) : (term104 P) = (term105 P).
Proof. exact (@lem18392 (real -> Prop) P). Qed.
Lemma lem5308719 : term34 = term106.
Proof. exact (@lem5308718 term29). Qed.
Lemma lem5308720 (s : real -> Prop) : (term107 s) = (term27 s).
Proof. exact (eq_refl (term107 s)). Qed.
Lemma lem5308721 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5308722 (s : real -> Prop) : (term108 s) = (term97 s).
Proof. exact (MK_COMB (@lem5308721) (@lem5308720 s)). Qed.
Lemma lem5308723 (s : real -> Prop) : (term108 s) = (term103 s).
Proof. exact (TRANS (@lem5308722 s) (@lem5308717 s)). Qed.
Lemma lem5308724 : term109 = term110.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5308723 s)). Qed.
Lemma lem5308725 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5308726 : term106 = term111.
Proof. exact (MK_COMB (@lem5308725) (@lem5308724)). Qed.
Lemma lem5308727 : term34 = term111.
Proof. exact (TRANS (@lem5308719) (@lem5308726)). Qed.
Lemma lem5308886 {A : Type'} (P : A -> Prop) (Q : Prop) : (term112 A P Q) = (term113 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5308887 (P : real -> Prop) (Q : Prop) : (term114 P Q) = (term115 P Q).
Proof. exact (@lem5308886 real P Q). Qed.
Lemma lem5308888 (s : real -> Prop) (l : real) : (term116 s l) = (term117 s l).
Proof. exact (@lem5308887 (term65 s) ((sup s) = l)). Qed.
Lemma lem5308889 (s : real -> Prop) (b : real) : (term118 s b) = (term64 s b).
Proof. exact (eq_refl (term118 s b)). Qed.
Lemma lem5308890 (s : real -> Prop) : (term119 s) = (term65 s).
Proof. exact (fun_ext (fun b : real => @lem5308889 s b)). Qed.
Lemma lem5308891 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5308892 (s : real -> Prop) : (term120 s) = (term66 s).
Proof. exact (MK_COMB (@lem5308891) (@lem5308890 s)). Qed.
Lemma lem5308893 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5308894 (s : real -> Prop) : (term121 s) = (term67 s).
Proof. exact (MK_COMB (@lem5308893) (@lem5308892 s)). Qed.
Lemma lem5308895 (s : real -> Prop) (l : real) : ((sup s) = l) = ((sup s) = l).
Proof. exact (eq_refl ((sup s) = l)). Qed.
Lemma lem5308896 (s : real -> Prop) (l : real) : (term116 s l) = (term68 s l).
Proof. exact (MK_COMB (@lem5308894 s) (@lem5308895 s l)). Qed.
Lemma lem5308897 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5308898 (s : real -> Prop) (l : real) : (term122 s l) = (term123 s l).
Proof. exact (MK_COMB (@lem5308897) (@lem5308896 s l)). Qed.
Lemma lem5308899 (s : real -> Prop) (b : real) : (term118 s b) = (term64 s b).
Proof. exact (eq_refl (term118 s b)). Qed.
Lemma lem5308900 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5308901 (s : real -> Prop) (b : real) : (term124 s b) = (term125 s b).
Proof. exact (MK_COMB (@lem5308900) (@lem5308899 s b)). Qed.
Lemma lem5308902 (s : real -> Prop) (l : real) : ((sup s) = l) = ((sup s) = l).
Proof. exact (eq_refl ((sup s) = l)). Qed.
Lemma lem5308903 (b : real) (s : real -> Prop) (l : real) : (term126 b s l) = (term127 b s l).
Proof. exact (MK_COMB (@lem5308901 s b) (@lem5308902 s l)). Qed.
Lemma lem5308904 (s : real -> Prop) (l : real) : (term128 s l) = (term129 s l).
Proof. exact (fun_ext (fun b : real => @lem5308903 b s l)). Qed.
Lemma lem5308905 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5308906 (s : real -> Prop) (l : real) : (term117 s l) = (term130 s l).
Proof. exact (MK_COMB (@lem5308905) (@lem5308904 s l)). Qed.
Lemma lem5308907 (s : real -> Prop) (l : real) : ((term116 s l) = (term117 s l)) = ((term68 s l) = (term130 s l)).
Proof. exact (MK_COMB (@lem5308898 s l) (@lem5308906 s l)). Qed.
Lemma lem5308908 (s : real -> Prop) (l : real) : (term68 s l) = (term130 s l).
Proof. exact (EQ_MP (@lem5308907 s l) (@lem5308888 s l)). Qed.
Lemma lem5308909 (s : real -> Prop) : (term54 s) = (term54 s).
Proof. exact (eq_refl (term54 s)). Qed.
Lemma lem5308910 (s : real -> Prop) (l : real) : (term69 s l) = (term131 s l).
Proof. exact (MK_COMB (@lem5308909 s) (@lem5308908 s l)). Qed.
Lemma lem5308912 {A : Type'} (P : Prop) (Q : A -> Prop) : (term132 A P Q) = (term133 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5308913 (P : Prop) (Q : real -> Prop) : (term134 P Q) = (term135 P Q).
Proof. exact (@lem5308912 real P Q). Qed.
Lemma lem5308914 (s : real -> Prop) (l : real) : (term136 s l) = (term137 s l).
Proof. exact (@lem5308913 (term138 s) (term129 s l)). Qed.
Lemma lem5308915 (b : real) (s : real -> Prop) (l : real) : (term139 s l b) = (term127 b s l).
Proof. exact (eq_refl (term139 s l b)). Qed.
Lemma lem5308916 (s : real -> Prop) (l : real) : (term140 s l) = (term129 s l).
Proof. exact (fun_ext (fun b : real => @lem5308915 b s l)). Qed.
Lemma lem5308917 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5308918 (s : real -> Prop) (l : real) : (term141 s l) = (term130 s l).
Proof. exact (MK_COMB (@lem5308917) (@lem5308916 s l)). Qed.
Lemma lem5308919 (s : real -> Prop) : (term54 s) = (term54 s).
Proof. exact (eq_refl (term54 s)). Qed.
Lemma lem5308920 (s : real -> Prop) (l : real) : (term136 s l) = (term131 s l).
Proof. exact (MK_COMB (@lem5308919 s) (@lem5308918 s l)). Qed.
Lemma lem5308921 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5308922 (s : real -> Prop) (l : real) : (term142 s l) = (term143 s l).
Proof. exact (MK_COMB (@lem5308921) (@lem5308920 s l)). Qed.
Lemma lem5308923 (b : real) (s : real -> Prop) (l : real) : (term139 s l b) = (term127 b s l).
Proof. exact (eq_refl (term139 s l b)). Qed.
Lemma lem5308924 (s : real -> Prop) : (term54 s) = (term54 s).
Proof. exact (eq_refl (term54 s)). Qed.
Lemma lem5308925 (b : real) (s : real -> Prop) (l : real) : (term144 s l b) = (term145 b s l).
Proof. exact (MK_COMB (@lem5308924 s) (@lem5308923 b s l)). Qed.
Lemma lem5308926 (s : real -> Prop) (l : real) : (term146 s l) = (term147 s l).
Proof. exact (fun_ext (fun b : real => @lem5308925 b s l)). Qed.
Lemma lem5308927 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5308928 (s : real -> Prop) (l : real) : (term137 s l) = (term148 s l).
Proof. exact (MK_COMB (@lem5308927) (@lem5308926 s l)). Qed.
Lemma lem5308929 (s : real -> Prop) (l : real) : ((term136 s l) = (term137 s l)) = ((term131 s l) = (term148 s l)).
Proof. exact (MK_COMB (@lem5308922 s l) (@lem5308928 s l)). Qed.
Lemma lem5308930 (s : real -> Prop) (l : real) : (term131 s l) = (term148 s l).
Proof. exact (EQ_MP (@lem5308929 s l) (@lem5308914 s l)). Qed.
Lemma lem5308931 (s : real -> Prop) (l : real) : (term69 s l) = (term148 s l).
Proof. exact (TRANS (@lem5308910 s l) (@lem5308930 s l)). Qed.
Lemma lem5308932 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5308933 (s : real -> Prop) (l : real) : (term70 s l) = (term149 s l).
Proof. exact (MK_COMB (@lem5308932) (@lem5308931 s l)). Qed.
Lemma lem5308934 (c : real) (l : real) : (real_lt c l) = (real_lt c l).
Proof. exact (eq_refl (real_lt c l)). Qed.
Lemma lem5308935 (s : real -> Prop) (c : real) (l : real) : (term71 s c l) = (term150 s c l).
Proof. exact (MK_COMB (@lem5308933 s l) (@lem5308934 c l)). Qed.
Lemma lem5308937 {A : Type'} (P : A -> Prop) (Q : Prop) : (term112 A P Q) = (term113 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5308938 (P : real -> Prop) (Q : Prop) : (term114 P Q) = (term115 P Q).
Proof. exact (@lem5308937 real P Q). Qed.
Lemma lem5308939 (s : real -> Prop) (c : real) (l : real) : (term151 s c l) = (term152 s c l).
Proof. exact (@lem5308938 (term147 s l) (real_lt c l)). Qed.
Lemma lem5308940 (b : real) (s : real -> Prop) (l : real) : (term153 s l b) = (term145 b s l).
Proof. exact (eq_refl (term153 s l b)). Qed.
Lemma lem5308941 (s : real -> Prop) (l : real) : (term154 s l) = (term147 s l).
Proof. exact (fun_ext (fun b : real => @lem5308940 b s l)). Qed.
Lemma lem5308942 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5308943 (s : real -> Prop) (l : real) : (term155 s l) = (term148 s l).
Proof. exact (MK_COMB (@lem5308942) (@lem5308941 s l)). Qed.
Lemma lem5308944 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5308945 (s : real -> Prop) (l : real) : (term156 s l) = (term149 s l).
Proof. exact (MK_COMB (@lem5308944) (@lem5308943 s l)). Qed.
Lemma lem5308946 (c : real) (l : real) : (real_lt c l) = (real_lt c l).
Proof. exact (eq_refl (real_lt c l)). Qed.
Lemma lem5308947 (s : real -> Prop) (c : real) (l : real) : (term151 s c l) = (term150 s c l).
Proof. exact (MK_COMB (@lem5308945 s l) (@lem5308946 c l)). Qed.
Lemma lem5308948 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5308949 (s : real -> Prop) (c : real) (l : real) : (term157 s c l) = (term158 s c l).
Proof. exact (MK_COMB (@lem5308948) (@lem5308947 s c l)). Qed.
Lemma lem5308950 (b : real) (s : real -> Prop) (l : real) : (term153 s l b) = (term145 b s l).
Proof. exact (eq_refl (term153 s l b)). Qed.
Lemma lem5308951 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5308952 (b : real) (s : real -> Prop) (l : real) : (term159 s l b) = (term160 b s l).
Proof. exact (MK_COMB (@lem5308951) (@lem5308950 b s l)). Qed.
Lemma lem5308953 (c : real) (l : real) : (real_lt c l) = (real_lt c l).
Proof. exact (eq_refl (real_lt c l)). Qed.
Lemma lem5308954 (b : real) (s : real -> Prop) (c : real) (l : real) : (term161 s b c l) = (term162 b s c l).
Proof. exact (MK_COMB (@lem5308952 b s l) (@lem5308953 c l)). Qed.
Lemma lem5308955 (s : real -> Prop) (c : real) (l : real) : (term163 s c l) = (term164 s c l).
Proof. exact (fun_ext (fun b : real => @lem5308954 b s c l)). Qed.
Lemma lem5308956 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5308957 (s : real -> Prop) (c : real) (l : real) : (term152 s c l) = (term165 s c l).
Proof. exact (MK_COMB (@lem5308956) (@lem5308955 s c l)). Qed.
Lemma lem5308958 (s : real -> Prop) (c : real) (l : real) : ((term151 s c l) = (term152 s c l)) = ((term150 s c l) = (term165 s c l)).
Proof. exact (MK_COMB (@lem5308949 s c l) (@lem5308957 s c l)). Qed.
Lemma lem5308959 (s : real -> Prop) (c : real) (l : real) : (term150 s c l) = (term165 s c l).
Proof. exact (EQ_MP (@lem5308958 s c l) (@lem5308939 s c l)). Qed.
Lemma lem5308960 (s : real -> Prop) (c : real) (l : real) : (term71 s c l) = (term165 s c l).
Proof. exact (TRANS (@lem5308935 s c l) (@lem5308959 s c l)). Qed.
Lemma lem5308961 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5308962 (s : real -> Prop) (c : real) (l : real) : (term84 s c l) = (term166 s c l).
Proof. exact (MK_COMB (@lem5308961) (@lem5308960 s c l)). Qed.
Lemma lem5308963 (s : real -> Prop) (c : real) : (term82 s c) = (term82 s c).
Proof. exact (eq_refl (term82 s c)). Qed.
Lemma lem5308964 (l : real) (s : real -> Prop) (c : real) : (term86 l s c) = (term167 l s c).
Proof. exact (MK_COMB (@lem5308962 s c l) (@lem5308963 s c)). Qed.
Lemma lem5308966 {A : Type'} (P : A -> Prop) (Q : Prop) : (term112 A P Q) = (term113 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5308967 (P : real -> Prop) (Q : Prop) : (term114 P Q) = (term115 P Q).
Proof. exact (@lem5308966 real P Q). Qed.
Lemma lem5308968 (l : real) (s : real -> Prop) (c : real) : (term168 l s c) = (term169 l s c).
Proof. exact (@lem5308967 (term164 s c l) (term82 s c)). Qed.
Lemma lem5308969 (b : real) (s : real -> Prop) (c : real) (l : real) : (term170 s c l b) = (term162 b s c l).
Proof. exact (eq_refl (term170 s c l b)). Qed.
Lemma lem5308970 (s : real -> Prop) (c : real) (l : real) : (term171 s c l) = (term164 s c l).
Proof. exact (fun_ext (fun b : real => @lem5308969 b s c l)). Qed.
Lemma lem5308971 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5308972 (s : real -> Prop) (c : real) (l : real) : (term172 s c l) = (term165 s c l).
Proof. exact (MK_COMB (@lem5308971) (@lem5308970 s c l)). Qed.
Lemma lem5308973 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5308974 (s : real -> Prop) (c : real) (l : real) : (term173 s c l) = (term166 s c l).
Proof. exact (MK_COMB (@lem5308973) (@lem5308972 s c l)). Qed.
Lemma lem5308975 (s : real -> Prop) (c : real) : (term82 s c) = (term82 s c).
Proof. exact (eq_refl (term82 s c)). Qed.
Lemma lem5308976 (l : real) (s : real -> Prop) (c : real) : (term168 l s c) = (term167 l s c).
Proof. exact (MK_COMB (@lem5308974 s c l) (@lem5308975 s c)). Qed.
Lemma lem5308977 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5308978 (l : real) (s : real -> Prop) (c : real) : (term174 l s c) = (term175 l s c).
Proof. exact (MK_COMB (@lem5308977) (@lem5308976 l s c)). Qed.
Lemma lem5308979 (b : real) (s : real -> Prop) (c : real) (l : real) : (term170 s c l b) = (term162 b s c l).
Proof. exact (eq_refl (term170 s c l b)). Qed.
Lemma lem5308980 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5308981 (b : real) (s : real -> Prop) (c : real) (l : real) : (term176 s c l b) = (term177 b s c l).
Proof. exact (MK_COMB (@lem5308980) (@lem5308979 b s c l)). Qed.
Lemma lem5308982 (s : real -> Prop) (c : real) : (term82 s c) = (term82 s c).
Proof. exact (eq_refl (term82 s c)). Qed.
Lemma lem5308983 (b : real) (l : real) (s : real -> Prop) (c : real) : (term178 l b s c) = (term179 b l s c).
Proof. exact (MK_COMB (@lem5308981 b s c l) (@lem5308982 s c)). Qed.
Lemma lem5308984 (l : real) (s : real -> Prop) (c : real) : (term180 l s c) = (term181 l s c).
Proof. exact (fun_ext (fun b : real => @lem5308983 b l s c)). Qed.
Lemma lem5308985 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5308986 (l : real) (s : real -> Prop) (c : real) : (term169 l s c) = (term182 l s c).
Proof. exact (MK_COMB (@lem5308985) (@lem5308984 l s c)). Qed.
Lemma lem5308987 (l : real) (s : real -> Prop) (c : real) : ((term168 l s c) = (term169 l s c)) = ((term167 l s c) = (term182 l s c)).
Proof. exact (MK_COMB (@lem5308978 l s c) (@lem5308986 l s c)). Qed.
Lemma lem5308988 (l : real) (s : real -> Prop) (c : real) : (term167 l s c) = (term182 l s c).
Proof. exact (EQ_MP (@lem5308987 l s c) (@lem5308968 l s c)). Qed.
Lemma lem5308989 (l : real) (s : real -> Prop) (c : real) : (term86 l s c) = (term182 l s c).
Proof. exact (TRANS (@lem5308964 l s c) (@lem5308988 l s c)). Qed.
Lemma lem5308990 (l : real) (s : real -> Prop) : (term95 l s) = (term183 l s).
Proof. exact (fun_ext (fun c : real => @lem5308989 l s c)). Qed.
Lemma lem5308991 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5308992 (l : real) (s : real -> Prop) : (term96 l s) = (term184 l s).
Proof. exact (MK_COMB (@lem5308991) (@lem5308990 l s)). Qed.
Lemma lem5308993 (s : real -> Prop) : (term102 s) = (term185 s).
Proof. exact (fun_ext (fun l : real => @lem5308992 l s)). Qed.
Lemma lem5308994 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5308995 (s : real -> Prop) : (term103 s) = (term186 s).
Proof. exact (MK_COMB (@lem5308994) (@lem5308993 s)). Qed.
Lemma lem5308996 : term110 = term187.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5308995 s)). Qed.
Lemma lem5308997 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5308999 : term111 = term188.
Proof. exact (MK_COMB (@lem5308997) (@lem5308996)). Qed.
Lemma lem5309000 : term34 = term188.
Proof. exact (TRANS (@lem5308727) (@lem5308999)). Qed.
Lemma lem5309001 (h1 : term34) : term188.
Proof. exact (EQ_MP (@lem5309000) (@lem5308649 h1)). Qed.
Lemma lem5309004 (s : real -> Prop) : (term189 s) = (s = (@EMPTY real)).
Proof. exact (@lem16933 (s = (@EMPTY real))). Qed.
Lemma lem5309011 (s : real -> Prop) (x : real) (b : real) : (term190 s x b) = (term191 s x b).
Proof. exact (@lem17362 (@IN real x s) (real_le x b)). Qed.
Lemma lem5309012 (P : real -> Prop) : (term88 P) = (term89 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5309013 (s : real -> Prop) (b : real) : (term192 s b) = (term193 s b).
Proof. exact (@lem5309012 (term48 s b)). Qed.
Lemma lem5309014 (s : real -> Prop) (x : real) (b : real) : (term194 s b x) = (term47 s x b).
Proof. exact (eq_refl (term194 s b x)). Qed.
Lemma lem5309015 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5309016 (s : real -> Prop) (x : real) (b : real) : (term195 s b x) = (term190 s x b).
Proof. exact (MK_COMB (@lem5309015) (@lem5309014 s x b)). Qed.
Lemma lem5309017 (s : real -> Prop) (x : real) (b : real) : (term195 s b x) = (term191 s x b).
Proof. exact (TRANS (@lem5309016 s x b) (@lem5309011 s x b)). Qed.
Lemma lem5309018 (s : real -> Prop) (b : real) : (term196 s b) = (term197 s b).
Proof. exact (fun_ext (fun x : real => @lem5309017 s x b)). Qed.
Lemma lem5309019 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5309020 (s : real -> Prop) (b : real) : (term193 s b) = (term198 s b).
Proof. exact (MK_COMB (@lem5309019) (@lem5309018 s b)). Qed.
Lemma lem5309021 (s : real -> Prop) (b : real) : (term192 s b) = (term198 s b).
Proof. exact (TRANS (@lem5309013 s b) (@lem5309020 s b)). Qed.
Lemma lem5309022 (P : real -> Prop) : (term74 P) = (term75 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5309023 (s : real -> Prop) : (term199 s) = (term200 s).
Proof. exact (@lem5309022 (term50 s)). Qed.
Lemma lem5309024 (s : real -> Prop) (b : real) : (term201 s b) = (term49 s b).
Proof. exact (eq_refl (term201 s b)). Qed.
Lemma lem5309025 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5309026 (s : real -> Prop) (b : real) : (term202 s b) = (term192 s b).
Proof. exact (MK_COMB (@lem5309025) (@lem5309024 s b)). Qed.
Lemma lem5309027 (s : real -> Prop) (b : real) : (term202 s b) = (term198 s b).
Proof. exact (TRANS (@lem5309026 s b) (@lem5309021 s b)). Qed.
Lemma lem5309028 (s : real -> Prop) : (term203 s) = (term204 s).
Proof. exact (fun_ext (fun b : real => @lem5309027 s b)). Qed.
Lemma lem5309029 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5309030 (s : real -> Prop) : (term200 s) = (term205 s).
Proof. exact (MK_COMB (@lem5309029) (@lem5309028 s)). Qed.
Lemma lem5309031 (s : real -> Prop) : (term199 s) = (term205 s).
Proof. exact (TRANS (@lem5309023 s) (@lem5309030 s)). Qed.
Lemma lem5309032 (c : real) (s : real -> Prop) : (term206 c s) = (term206 c s).
Proof. exact (eq_refl (term206 c s)). Qed.
Lemma lem5309033 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5309034 (s : real -> Prop) : (term207 s) = (term208 s).
Proof. exact (MK_COMB (@lem5309033) (@lem5309031 s)). Qed.
Lemma lem5309035 (c : real) (s : real -> Prop) : (term209 c s) = (term210 c s).
Proof. exact (MK_COMB (@lem5309034 s) (@lem5309032 c s)). Qed.
Lemma lem5309036 (c : real) (s : real -> Prop) : (term211 c s) = (term209 c s).
Proof. exact (@lem17045 (term51 s) (term46 c s)). Qed.
Lemma lem5309037 (c : real) (s : real -> Prop) : (term211 c s) = (term210 c s).
Proof. exact (TRANS (@lem5309036 c s) (@lem5309035 c s)). Qed.
Lemma lem5309038 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5309039 (s : real -> Prop) : (term212 s) = (term213 s).
Proof. exact (MK_COMB (@lem5309038) (@lem5309004 s)). Qed.
Lemma lem5309040 (c : real) (s : real -> Prop) : (term214 c s) = (term215 c s).
Proof. exact (MK_COMB (@lem5309039 s) (@lem5309037 c s)). Qed.
Lemma lem5309041 (c : real) (s : real -> Prop) : (term216 c s) = (term214 c s).
Proof. exact (@lem17045 (term138 s) (term53 c s)). Qed.
Lemma lem5309042 (c : real) (s : real -> Prop) : (term216 c s) = (term215 c s).
Proof. exact (TRANS (@lem5309041 c s) (@lem5309040 c s)). Qed.
Lemma lem5309047 (s : real -> Prop) (c : real) (x : real) : (term44 s c x) = (term44 s c x).
Proof. exact (eq_refl (term44 s c x)). Qed.
Lemma lem5309048 (s : real -> Prop) (c : real) : (term45 s c) = (term45 s c).
Proof. exact (fun_ext (fun x : real => @lem5309047 s c x)). Qed.
Lemma lem5309049 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5309050 (s : real -> Prop) (c : real) : (term17 s c) = (term17 s c).
Proof. exact (MK_COMB (@lem5309049) (@lem5309048 s c)). Qed.
Lemma lem5309051 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5309052 (c : real) (s : real -> Prop) : (term217 c s) = (term218 c s).
Proof. exact (MK_COMB (@lem5309051) (@lem5309042 c s)). Qed.
Lemma lem5309053 (s : real -> Prop) (c : real) : (term219 s c) = (term220 s c).
Proof. exact (MK_COMB (@lem5309052 c s) (@lem5309050 s c)). Qed.
Lemma lem5309054 (s : real -> Prop) (c : real) : (term57 s c) = (term219 s c).
Proof. exact (@lem17265 (term55 c s) (term17 s c)). Qed.
Lemma lem5309055 (s : real -> Prop) (c : real) : (term57 s c) = (term220 s c).
Proof. exact (TRANS (@lem5309054 s c) (@lem5309053 s c)). Qed.
Lemma lem5309056 (s : real -> Prop) : (term58 s) = (term221 s).
Proof. exact (fun_ext (fun c : real => @lem5309055 s c)). Qed.
Lemma lem5309057 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5309058 (s : real -> Prop) : (term59 s) = (term222 s).
Proof. exact (MK_COMB (@lem5309057) (@lem5309056 s)). Qed.
Lemma lem5309059 : term60 = term223.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5309058 s)). Qed.
Lemma lem5309060 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5309061 : term41 = term224.
Proof. exact (MK_COMB (@lem5309060) (@lem5309059)). Qed.
Lemma lem5309216 {A B : Type'} (P : type1413 A B) : (term225 A B P) = (term226 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5309217 (P : type1626) : (term227 P) = (term228 P).
Proof. exact (@lem5309216 real real P). Qed.
Lemma lem5309218 (s : real -> Prop) : (term229 s) = (term230 s).
Proof. exact (@lem5309217 (term231 s)). Qed.
Lemma lem5309219 (s : real -> Prop) (b : real) : (term232 s b) = (term197 s b).
Proof. exact (eq_refl (term232 s b)). Qed.
Lemma lem5309220 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5309221 (s : real -> Prop) (b : real) (x : real) : (term233 s b x) = (term234 s b x).
Proof. exact (MK_COMB (@lem5309219 s b) (@lem5309220 x)). Qed.
Lemma lem5309222 (s : real -> Prop) (x : real) (b : real) : (term234 s b x) = (term191 s x b).
Proof. exact (eq_refl (term234 s b x)). Qed.
Lemma lem5309223 (s : real -> Prop) (x : real) (b : real) : (term233 s b x) = (term191 s x b).
Proof. exact (TRANS (@lem5309221 s b x) (@lem5309222 s x b)). Qed.
Lemma lem5309224 (s : real -> Prop) (b : real) : (term235 s b) = (term197 s b).
Proof. exact (fun_ext (fun x : real => @lem5309223 s x b)). Qed.
Lemma lem5309225 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5309226 (s : real -> Prop) (b : real) : (term236 s b) = (term198 s b).
Proof. exact (MK_COMB (@lem5309225) (@lem5309224 s b)). Qed.
Lemma lem5309227 (s : real -> Prop) : (term237 s) = (term204 s).
Proof. exact (fun_ext (fun b : real => @lem5309226 s b)). Qed.
Lemma lem5309228 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5309229 (s : real -> Prop) : (term229 s) = (term205 s).
Proof. exact (MK_COMB (@lem5309228) (@lem5309227 s)). Qed.
Lemma lem5309230 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5309231 (s : real -> Prop) : (term238 s) = (term239 s).
Proof. exact (MK_COMB (@lem5309230) (@lem5309229 s)). Qed.
Lemma lem5309232 (s : real -> Prop) (b : real) : (term232 s b) = (term197 s b).
Proof. exact (eq_refl (term232 s b)). Qed.
Lemma lem5309233 (x : real -> real) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem5309234 (s : real -> Prop) (x : real -> real) (b : real) : (term240 s x b) = (term241 s x b).
Proof. exact (MK_COMB (@lem5309232 s b) (@lem5309233 x b)). Qed.
Lemma lem5309235 (s : real -> Prop) (x : real -> real) (b : real) : (term241 s x b) = (term242 s x b).
Proof. exact (eq_refl (term241 s x b)). Qed.
Lemma lem5309236 (s : real -> Prop) (x : real -> real) (b : real) : (term240 s x b) = (term242 s x b).
Proof. exact (TRANS (@lem5309234 s x b) (@lem5309235 s x b)). Qed.
Lemma lem5309237 (s : real -> Prop) (x : real -> real) : (term243 s x) = (term244 s x).
Proof. exact (fun_ext (fun b : real => @lem5309236 s x b)). Qed.
Lemma lem5309238 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5309239 (s : real -> Prop) (x : real -> real) : (term245 s x) = (term246 s x).
Proof. exact (MK_COMB (@lem5309238) (@lem5309237 s x)). Qed.
Lemma lem5309240 (s : real -> Prop) : (term247 s) = (term248 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5309239 s x)). Qed.
Lemma lem5309241 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5309242 (s : real -> Prop) : (term230 s) = (term249 s).
Proof. exact (MK_COMB (@lem5309241) (@lem5309240 s)). Qed.
Lemma lem5309243 (s : real -> Prop) : ((term229 s) = (term230 s)) = ((term205 s) = (term249 s)).
Proof. exact (MK_COMB (@lem5309231 s) (@lem5309242 s)). Qed.
Lemma lem5309244 (s : real -> Prop) : (term205 s) = (term249 s).
Proof. exact (EQ_MP (@lem5309243 s) (@lem5309218 s)). Qed.
Lemma lem5309245 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5309246 (s : real -> Prop) : (term208 s) = (term250 s).
Proof. exact (MK_COMB (@lem5309245) (@lem5309244 s)). Qed.
Lemma lem5309247 (c : real) (s : real -> Prop) : (term206 c s) = (term206 c s).
Proof. exact (eq_refl (term206 c s)). Qed.
Lemma lem5309248 (c : real) (s : real -> Prop) : (term210 c s) = (term251 c s).
Proof. exact (MK_COMB (@lem5309246 s) (@lem5309247 c s)). Qed.
Lemma lem5309250 {A : Type'} (P : A -> Prop) (Q : Prop) : (term252 A P Q) = (term253 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5309251 (P : type1028) (Q : Prop) : (term254 P Q) = (term255 P Q).
Proof. exact (@lem5309250 (real -> real) P Q). Qed.
Lemma lem5309252 (c : real) (s : real -> Prop) : (term256 c s) = (term257 c s).
Proof. exact (@lem5309251 (term248 s) (term206 c s)). Qed.
Lemma lem5309253 (s : real -> Prop) (x : real -> real) : (term258 s x) = (term246 s x).
Proof. exact (eq_refl (term258 s x)). Qed.
Lemma lem5309254 (s : real -> Prop) : (term259 s) = (term248 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5309253 s x)). Qed.
Lemma lem5309255 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5309256 (s : real -> Prop) : (term260 s) = (term249 s).
Proof. exact (MK_COMB (@lem5309255) (@lem5309254 s)). Qed.
Lemma lem5309257 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5309258 (s : real -> Prop) : (term261 s) = (term250 s).
Proof. exact (MK_COMB (@lem5309257) (@lem5309256 s)). Qed.
Lemma lem5309259 (c : real) (s : real -> Prop) : (term206 c s) = (term206 c s).
Proof. exact (eq_refl (term206 c s)). Qed.
Lemma lem5309260 (c : real) (s : real -> Prop) : (term256 c s) = (term251 c s).
Proof. exact (MK_COMB (@lem5309258 s) (@lem5309259 c s)). Qed.
Lemma lem5309261 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5309262 (c : real) (s : real -> Prop) : (term262 c s) = (term263 c s).
Proof. exact (MK_COMB (@lem5309261) (@lem5309260 c s)). Qed.
Lemma lem5309263 (s : real -> Prop) (x : real -> real) : (term258 s x) = (term246 s x).
Proof. exact (eq_refl (term258 s x)). Qed.
Lemma lem5309264 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5309265 (s : real -> Prop) (x : real -> real) : (term264 s x) = (term265 s x).
Proof. exact (MK_COMB (@lem5309264) (@lem5309263 s x)). Qed.
Lemma lem5309266 (c : real) (s : real -> Prop) : (term206 c s) = (term206 c s).
Proof. exact (eq_refl (term206 c s)). Qed.
Lemma lem5309267 (x : real -> real) (c : real) (s : real -> Prop) : (term266 x c s) = (term267 x c s).
Proof. exact (MK_COMB (@lem5309265 s x) (@lem5309266 c s)). Qed.
Lemma lem5309268 (c : real) (s : real -> Prop) : (term268 c s) = (term269 c s).
Proof. exact (fun_ext (fun x : real -> real => @lem5309267 x c s)). Qed.
Lemma lem5309269 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5309270 (c : real) (s : real -> Prop) : (term257 c s) = (term270 c s).
Proof. exact (MK_COMB (@lem5309269) (@lem5309268 c s)). Qed.
Lemma lem5309271 (c : real) (s : real -> Prop) : ((term256 c s) = (term257 c s)) = ((term251 c s) = (term270 c s)).
Proof. exact (MK_COMB (@lem5309262 c s) (@lem5309270 c s)). Qed.
Lemma lem5309272 (c : real) (s : real -> Prop) : (term251 c s) = (term270 c s).
Proof. exact (EQ_MP (@lem5309271 c s) (@lem5309252 c s)). Qed.
Lemma lem5309273 (c : real) (s : real -> Prop) : (term210 c s) = (term270 c s).
Proof. exact (TRANS (@lem5309248 c s) (@lem5309272 c s)). Qed.
Lemma lem5309274 (s : real -> Prop) : (term213 s) = (term213 s).
Proof. exact (eq_refl (term213 s)). Qed.
Lemma lem5309275 (c : real) (s : real -> Prop) : (term215 c s) = (term271 c s).
Proof. exact (MK_COMB (@lem5309274 s) (@lem5309273 c s)). Qed.
Lemma lem5309277 {A : Type'} (P : Prop) (Q : A -> Prop) : (term272 A P Q) = (term273 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5309278 (P : Prop) (Q : type1028) : (term274 P Q) = (term275 P Q).
Proof. exact (@lem5309277 (real -> real) P Q). Qed.
Lemma lem5309279 (c : real) (s : real -> Prop) : (term276 c s) = (term277 c s).
Proof. exact (@lem5309278 (s = (@EMPTY real)) (term269 c s)). Qed.
Lemma lem5309280 (x : real -> real) (c : real) (s : real -> Prop) : (term278 c s x) = (term267 x c s).
Proof. exact (eq_refl (term278 c s x)). Qed.
Lemma lem5309281 (c : real) (s : real -> Prop) : (term279 c s) = (term269 c s).
Proof. exact (fun_ext (fun x : real -> real => @lem5309280 x c s)). Qed.
Lemma lem5309282 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5309283 (c : real) (s : real -> Prop) : (term280 c s) = (term270 c s).
Proof. exact (MK_COMB (@lem5309282) (@lem5309281 c s)). Qed.
Lemma lem5309284 (s : real -> Prop) : (term213 s) = (term213 s).
Proof. exact (eq_refl (term213 s)). Qed.
Lemma lem5309285 (c : real) (s : real -> Prop) : (term276 c s) = (term271 c s).
Proof. exact (MK_COMB (@lem5309284 s) (@lem5309283 c s)). Qed.
Lemma lem5309286 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5309287 (c : real) (s : real -> Prop) : (term281 c s) = (term282 c s).
Proof. exact (MK_COMB (@lem5309286) (@lem5309285 c s)). Qed.
Lemma lem5309288 (x : real -> real) (c : real) (s : real -> Prop) : (term278 c s x) = (term267 x c s).
Proof. exact (eq_refl (term278 c s x)). Qed.
Lemma lem5309289 (s : real -> Prop) : (term213 s) = (term213 s).
Proof. exact (eq_refl (term213 s)). Qed.
Lemma lem5309290 (x : real -> real) (c : real) (s : real -> Prop) : (term283 c s x) = (term284 x c s).
Proof. exact (MK_COMB (@lem5309289 s) (@lem5309288 x c s)). Qed.
Lemma lem5309291 (c : real) (s : real -> Prop) : (term285 c s) = (term286 c s).
Proof. exact (fun_ext (fun x : real -> real => @lem5309290 x c s)). Qed.
Lemma lem5309292 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5309293 (c : real) (s : real -> Prop) : (term277 c s) = (term287 c s).
Proof. exact (MK_COMB (@lem5309292) (@lem5309291 c s)). Qed.
Lemma lem5309294 (c : real) (s : real -> Prop) : ((term276 c s) = (term277 c s)) = ((term271 c s) = (term287 c s)).
Proof. exact (MK_COMB (@lem5309287 c s) (@lem5309293 c s)). Qed.
Lemma lem5309295 (c : real) (s : real -> Prop) : (term271 c s) = (term287 c s).
Proof. exact (EQ_MP (@lem5309294 c s) (@lem5309279 c s)). Qed.
Lemma lem5309296 (c : real) (s : real -> Prop) : (term215 c s) = (term287 c s).
Proof. exact (TRANS (@lem5309275 c s) (@lem5309295 c s)). Qed.
Lemma lem5309297 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5309298 (c : real) (s : real -> Prop) : (term218 c s) = (term288 c s).
Proof. exact (MK_COMB (@lem5309297) (@lem5309296 c s)). Qed.
Lemma lem5309299 (s : real -> Prop) (c : real) : (term17 s c) = (term17 s c).
Proof. exact (eq_refl (term17 s c)). Qed.
Lemma lem5309300 (s : real -> Prop) (c : real) : (term220 s c) = (term289 s c).
Proof. exact (MK_COMB (@lem5309298 c s) (@lem5309299 s c)). Qed.
Lemma lem5309304 {A : Type'} (P : A -> Prop) (Q : Prop) : (term252 A P Q) = (term253 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5309305 (P : type1028) (Q : Prop) : (term254 P Q) = (term255 P Q).
Proof. exact (@lem5309304 (real -> real) P Q). Qed.
Lemma lem5309306 (s : real -> Prop) (c : real) : (term290 s c) = (term291 s c).
Proof. exact (@lem5309305 (term286 c s) (term17 s c)). Qed.
Lemma lem5309307 (x : real -> real) (c : real) (s : real -> Prop) : (term292 c s x) = (term284 x c s).
Proof. exact (eq_refl (term292 c s x)). Qed.
Lemma lem5309308 (c : real) (s : real -> Prop) : (term293 c s) = (term286 c s).
Proof. exact (fun_ext (fun x : real -> real => @lem5309307 x c s)). Qed.
Lemma lem5309309 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5309310 (c : real) (s : real -> Prop) : (term294 c s) = (term287 c s).
Proof. exact (MK_COMB (@lem5309309) (@lem5309308 c s)). Qed.
Lemma lem5309311 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5309312 (c : real) (s : real -> Prop) : (term295 c s) = (term288 c s).
Proof. exact (MK_COMB (@lem5309311) (@lem5309310 c s)). Qed.
Lemma lem5309313 (s : real -> Prop) (c : real) : (term17 s c) = (term17 s c).
Proof. exact (eq_refl (term17 s c)). Qed.
Lemma lem5309314 (s : real -> Prop) (c : real) : (term290 s c) = (term289 s c).
Proof. exact (MK_COMB (@lem5309312 c s) (@lem5309313 s c)). Qed.
Lemma lem5309315 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5309316 (s : real -> Prop) (c : real) : (term296 s c) = (term297 s c).
Proof. exact (MK_COMB (@lem5309315) (@lem5309314 s c)). Qed.
Lemma lem5309317 (x : real -> real) (c : real) (s : real -> Prop) : (term292 c s x) = (term284 x c s).
Proof. exact (eq_refl (term292 c s x)). Qed.
Lemma lem5309318 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5309319 (x : real -> real) (c : real) (s : real -> Prop) : (term298 c s x) = (term299 x c s).
Proof. exact (MK_COMB (@lem5309318) (@lem5309317 x c s)). Qed.
Lemma lem5309320 (s : real -> Prop) (c : real) : (term17 s c) = (term17 s c).
Proof. exact (eq_refl (term17 s c)). Qed.
Lemma lem5309321 (x : real -> real) (s : real -> Prop) (c : real) : (term300 x s c) = (term301 x s c).
Proof. exact (MK_COMB (@lem5309319 x c s) (@lem5309320 s c)). Qed.
Lemma lem5309322 (s : real -> Prop) (c : real) : (term302 s c) = (term303 s c).
Proof. exact (fun_ext (fun x : real -> real => @lem5309321 x s c)). Qed.
Lemma lem5309323 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5309324 (s : real -> Prop) (c : real) : (term291 s c) = (term304 s c).
Proof. exact (MK_COMB (@lem5309323) (@lem5309322 s c)). Qed.
Lemma lem5309325 (s : real -> Prop) (c : real) : ((term290 s c) = (term291 s c)) = ((term289 s c) = (term304 s c)).
Proof. exact (MK_COMB (@lem5309316 s c) (@lem5309324 s c)). Qed.
Lemma lem5309326 (s : real -> Prop) (c : real) : (term289 s c) = (term304 s c).
Proof. exact (EQ_MP (@lem5309325 s c) (@lem5309306 s c)). Qed.
Lemma lem5309328 {A : Type'} (P : Prop) (Q : A -> Prop) : (term272 A P Q) = (term273 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5309329 (P : Prop) (Q : real -> Prop) : (term305 P Q) = (term306 P Q).
Proof. exact (@lem5309328 real P Q). Qed.
Lemma lem5309330 (x : real -> real) (s : real -> Prop) (c : real) : (term307 x s c) = (term308 x s c).
Proof. exact (@lem5309329 (term284 x c s) (term45 s c)). Qed.
Lemma lem5309331 (s : real -> Prop) (c : real) (x : real) : (term78 s c x) = (term44 s c x).
Proof. exact (eq_refl (term78 s c x)). Qed.
Lemma lem5309332 (s : real -> Prop) (c : real) : (term309 s c) = (term45 s c).
Proof. exact (fun_ext (fun x : real => @lem5309331 s c x)). Qed.
Lemma lem5309333 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5309334 (s : real -> Prop) (c : real) : (term310 s c) = (term17 s c).
Proof. exact (MK_COMB (@lem5309333) (@lem5309332 s c)). Qed.
Lemma lem5309335 (x : real -> real) (c : real) (s : real -> Prop) : (term299 x c s) = (term299 x c s).
Proof. exact (eq_refl (term299 x c s)). Qed.
Lemma lem5309336 (x : real -> real) (s : real -> Prop) (c : real) : (term307 x s c) = (term301 x s c).
Proof. exact (MK_COMB (@lem5309335 x c s) (@lem5309334 s c)). Qed.
Lemma lem5309337 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5309338 (x : real -> real) (s : real -> Prop) (c : real) : (term311 x s c) = (term312 x s c).
Proof. exact (MK_COMB (@lem5309337) (@lem5309336 x s c)). Qed.
Lemma lem5309339 (s : real -> Prop) (c : real) (x : real) : (term78 s c x) = (term44 s c x).
Proof. exact (eq_refl (term78 s c x)). Qed.
Lemma lem5309340 (x : real -> real) (c : real) (s : real -> Prop) : (term299 x c s) = (term299 x c s).
Proof. exact (eq_refl (term299 x c s)). Qed.
Lemma lem5309341 (x : real -> real) (s : real -> Prop) (c : real) (x' : real) : (term313 x s c x') = (term314 x s c x').
Proof. exact (MK_COMB (@lem5309340 x c s) (@lem5309339 s c x')). Qed.
Lemma lem5309342 (x : real -> real) (s : real -> Prop) (c : real) : (term315 x s c) = (term316 x s c).
Proof. exact (fun_ext (fun x' : real => @lem5309341 x s c x')). Qed.
Lemma lem5309343 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5309344 (x : real -> real) (s : real -> Prop) (c : real) : (term308 x s c) = (term317 x s c).
Proof. exact (MK_COMB (@lem5309343) (@lem5309342 x s c)). Qed.
Lemma lem5309345 (x : real -> real) (s : real -> Prop) (c : real) : ((term307 x s c) = (term308 x s c)) = ((term301 x s c) = (term317 x s c)).
Proof. exact (MK_COMB (@lem5309338 x s c) (@lem5309344 x s c)). Qed.
Lemma lem5309346 (x : real -> real) (s : real -> Prop) (c : real) : (term301 x s c) = (term317 x s c).
Proof. exact (EQ_MP (@lem5309345 x s c) (@lem5309330 x s c)). Qed.
Lemma lem5309347 (s : real -> Prop) (c : real) : (term303 s c) = (term318 s c).
Proof. exact (fun_ext (fun x : real -> real => @lem5309346 x s c)). Qed.
Lemma lem5309348 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5309349 (s : real -> Prop) (c : real) : (term304 s c) = (term319 s c).
Proof. exact (MK_COMB (@lem5309348) (@lem5309347 s c)). Qed.
Lemma lem5309350 (s : real -> Prop) (c : real) : (term289 s c) = (term319 s c).
Proof. exact (TRANS (@lem5309326 s c) (@lem5309349 s c)). Qed.
Lemma lem5309351 (s : real -> Prop) (c : real) : (term220 s c) = (term319 s c).
Proof. exact (TRANS (@lem5309300 s c) (@lem5309350 s c)). Qed.
Lemma lem5309352 (s : real -> Prop) : (term221 s) = (term320 s).
Proof. exact (fun_ext (fun c : real => @lem5309351 s c)). Qed.
Lemma lem5309353 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5309354 (s : real -> Prop) : (term222 s) = (term321 s).
Proof. exact (MK_COMB (@lem5309353) (@lem5309352 s)). Qed.
Lemma lem5309356 {A B : Type'} (P : type1413 A B) : (term225 A B P) = (term226 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5309357 (P : type1618) : (term322 P) = (term323 P).
Proof. exact (@lem5309356 real (real -> real) P). Qed.
Lemma lem5309358 (s : real -> Prop) : (term324 s) = (term325 s).
Proof. exact (@lem5309357 (term326 s)). Qed.
Lemma lem5309359 (s : real -> Prop) (c : real) : (term327 s c) = (term318 s c).
Proof. exact (eq_refl (term327 s c)). Qed.
Lemma lem5309360 (x : real -> real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5309361 (s : real -> Prop) (c : real) (x : real -> real) : (term328 s c x) = (term329 s c x).
Proof. exact (MK_COMB (@lem5309359 s c) (@lem5309360 x)). Qed.
Lemma lem5309362 (x : real -> real) (s : real -> Prop) (c : real) : (term329 s c x) = (term317 x s c).
Proof. exact (eq_refl (term329 s c x)). Qed.
Lemma lem5309363 (x : real -> real) (s : real -> Prop) (c : real) : (term328 s c x) = (term317 x s c).
Proof. exact (TRANS (@lem5309361 s c x) (@lem5309362 x s c)). Qed.
Lemma lem5309364 (s : real -> Prop) (c : real) : (term330 s c) = (term318 s c).
Proof. exact (fun_ext (fun x : real -> real => @lem5309363 x s c)). Qed.
Lemma lem5309365 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5309366 (s : real -> Prop) (c : real) : (term331 s c) = (term319 s c).
Proof. exact (MK_COMB (@lem5309365) (@lem5309364 s c)). Qed.
Lemma lem5309367 (s : real -> Prop) : (term332 s) = (term320 s).
Proof. exact (fun_ext (fun c : real => @lem5309366 s c)). Qed.
Lemma lem5309368 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5309369 (s : real -> Prop) : (term324 s) = (term321 s).
Proof. exact (MK_COMB (@lem5309368) (@lem5309367 s)). Qed.
Lemma lem5309370 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5309371 (s : real -> Prop) : (term333 s) = (term334 s).
Proof. exact (MK_COMB (@lem5309370) (@lem5309369 s)). Qed.
Lemma lem5309372 (s : real -> Prop) (c : real) : (term327 s c) = (term318 s c).
Proof. exact (eq_refl (term327 s c)). Qed.
Lemma lem5309373 (x : type1627) (c : real) : (x c) = (x c).
Proof. exact (eq_refl (x c)). Qed.
Lemma lem5309374 (s : real -> Prop) (x : type1627) (c : real) : (term335 s x c) = (term336 s x c).
Proof. exact (MK_COMB (@lem5309372 s c) (@lem5309373 x c)). Qed.
Lemma lem5309375 (x : type1627) (s : real -> Prop) (c : real) : (term336 s x c) = (term337 x s c).
Proof. exact (eq_refl (term336 s x c)). Qed.
Lemma lem5309376 (x : type1627) (s : real -> Prop) (c : real) : (term335 s x c) = (term337 x s c).
Proof. exact (TRANS (@lem5309374 s x c) (@lem5309375 x s c)). Qed.
Lemma lem5309377 (x : type1627) (s : real -> Prop) : (term338 s x) = (term339 x s).
Proof. exact (fun_ext (fun c : real => @lem5309376 x s c)). Qed.
Lemma lem5309378 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5309379 (x : type1627) (s : real -> Prop) : (term340 s x) = (term341 x s).
Proof. exact (MK_COMB (@lem5309378) (@lem5309377 x s)). Qed.
Lemma lem5309380 (s : real -> Prop) : (term342 s) = (term343 s).
Proof. exact (fun_ext (fun x : type1627 => @lem5309379 x s)). Qed.
Lemma lem5309381 : (@ex (real -> real -> real)) = (@ex (real -> real -> real)).
Proof. exact (eq_refl (@ex (real -> real -> real))). Qed.
Lemma lem5309382 (s : real -> Prop) : (term325 s) = (term344 s).
Proof. exact (MK_COMB (@lem5309381) (@lem5309380 s)). Qed.
Lemma lem5309383 (s : real -> Prop) : ((term324 s) = (term325 s)) = ((term321 s) = (term344 s)).
Proof. exact (MK_COMB (@lem5309371 s) (@lem5309382 s)). Qed.
Lemma lem5309384 (s : real -> Prop) : (term321 s) = (term344 s).
Proof. exact (EQ_MP (@lem5309383 s) (@lem5309358 s)). Qed.
Lemma lem5309386 {A B : Type'} (P : type1413 A B) : (term225 A B P) = (term226 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5309387 (P : type1626) : (term227 P) = (term228 P).
Proof. exact (@lem5309386 real real P). Qed.
Lemma lem5309388 (x : type1627) (s : real -> Prop) : (term345 x s) = (term346 x s).
Proof. exact (@lem5309387 (term347 x s)). Qed.
Lemma lem5309389 (x : type1627) (s : real -> Prop) (c : real) : (term348 x s c) = (term349 x s c).
Proof. exact (eq_refl (term348 x s c)). Qed.
Lemma lem5309390 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5309391 (x : type1627) (s : real -> Prop) (c : real) (x' : real) : (term350 x s c x') = (term351 x s c x').
Proof. exact (MK_COMB (@lem5309389 x s c) (@lem5309390 x')). Qed.
Lemma lem5309392 (x : type1627) (s : real -> Prop) (c : real) (x' : real) : (term351 x s c x') = (term352 x s c x').
Proof. exact (eq_refl (term351 x s c x')). Qed.
Lemma lem5309393 (x : type1627) (s : real -> Prop) (c : real) (x' : real) : (term350 x s c x') = (term352 x s c x').
Proof. exact (TRANS (@lem5309391 x s c x') (@lem5309392 x s c x')). Qed.
Lemma lem5309394 (x : type1627) (s : real -> Prop) (c : real) : (term353 x s c) = (term349 x s c).
Proof. exact (fun_ext (fun x' : real => @lem5309393 x s c x')). Qed.
Lemma lem5309395 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5309396 (x : type1627) (s : real -> Prop) (c : real) : (term354 x s c) = (term337 x s c).
Proof. exact (MK_COMB (@lem5309395) (@lem5309394 x s c)). Qed.
Lemma lem5309397 (x : type1627) (s : real -> Prop) : (term355 x s) = (term339 x s).
Proof. exact (fun_ext (fun c : real => @lem5309396 x s c)). Qed.
Lemma lem5309398 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5309399 (x : type1627) (s : real -> Prop) : (term345 x s) = (term341 x s).
Proof. exact (MK_COMB (@lem5309398) (@lem5309397 x s)). Qed.
Lemma lem5309400 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5309401 (x : type1627) (s : real -> Prop) : (term356 x s) = (term357 x s).
Proof. exact (MK_COMB (@lem5309400) (@lem5309399 x s)). Qed.
Lemma lem5309402 (x : type1627) (s : real -> Prop) (c : real) : (term348 x s c) = (term349 x s c).
Proof. exact (eq_refl (term348 x s c)). Qed.
Lemma lem5309403 (x : real -> real) (c : real) : (x c) = (x c).
Proof. exact (eq_refl (x c)). Qed.
Lemma lem5309404 (x : type1627) (s : real -> Prop) (x' : real -> real) (c : real) : (term358 x s x' c) = (term359 x s x' c).
Proof. exact (MK_COMB (@lem5309402 x s c) (@lem5309403 x' c)). Qed.
Lemma lem5309405 (x : type1627) (s : real -> Prop) (x' : real -> real) (c : real) : (term359 x s x' c) = (term360 x s x' c).
Proof. exact (eq_refl (term359 x s x' c)). Qed.
Lemma lem5309406 (x : type1627) (s : real -> Prop) (x' : real -> real) (c : real) : (term358 x s x' c) = (term360 x s x' c).
Proof. exact (TRANS (@lem5309404 x s x' c) (@lem5309405 x s x' c)). Qed.
Lemma lem5309407 (x : type1627) (s : real -> Prop) (x' : real -> real) : (term361 x s x') = (term362 x s x').
Proof. exact (fun_ext (fun c : real => @lem5309406 x s x' c)). Qed.
Lemma lem5309408 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5309409 (x : type1627) (s : real -> Prop) (x' : real -> real) : (term363 x s x') = (term364 x s x').
Proof. exact (MK_COMB (@lem5309408) (@lem5309407 x s x')). Qed.
Lemma lem5309410 (x : type1627) (s : real -> Prop) : (term365 x s) = (term366 x s).
Proof. exact (fun_ext (fun x' : real -> real => @lem5309409 x s x')). Qed.
Lemma lem5309411 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5309412 (x : type1627) (s : real -> Prop) : (term346 x s) = (term367 x s).
Proof. exact (MK_COMB (@lem5309411) (@lem5309410 x s)). Qed.
Lemma lem5309413 (x : type1627) (s : real -> Prop) : ((term345 x s) = (term346 x s)) = ((term341 x s) = (term367 x s)).
Proof. exact (MK_COMB (@lem5309401 x s) (@lem5309412 x s)). Qed.
Lemma lem5309414 (x : type1627) (s : real -> Prop) : (term341 x s) = (term367 x s).
Proof. exact (EQ_MP (@lem5309413 x s) (@lem5309388 x s)). Qed.
Lemma lem5309415 (s : real -> Prop) : (term343 s) = (term368 s).
Proof. exact (fun_ext (fun x : type1627 => @lem5309414 x s)). Qed.
Lemma lem5309416 : (@ex (real -> real -> real)) = (@ex (real -> real -> real)).
Proof. exact (eq_refl (@ex (real -> real -> real))). Qed.
Lemma lem5309417 (s : real -> Prop) : (term344 s) = (term369 s).
Proof. exact (MK_COMB (@lem5309416) (@lem5309415 s)). Qed.
Lemma lem5309418 (s : real -> Prop) : (term321 s) = (term369 s).
Proof. exact (TRANS (@lem5309384 s) (@lem5309417 s)). Qed.
Lemma lem5309419 (s : real -> Prop) : (term222 s) = (term369 s).
Proof. exact (TRANS (@lem5309354 s) (@lem5309418 s)). Qed.
Lemma lem5309420 : term223 = term370.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5309419 s)). Qed.
Lemma lem5309421 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5309422 : term224 = term371.
Proof. exact (MK_COMB (@lem5309421) (@lem5309420)). Qed.
Lemma lem5309424 {A B : Type'} (P : type1413 A B) : (term225 A B P) = (term226 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5309425 (P : type1016) : (term372 P) = (term373 P).
Proof. exact (@lem5309424 (real -> Prop) type1627 P). Qed.
Lemma lem5309426 : term374 = term375.
Proof. exact (@lem5309425 term376). Qed.
Lemma lem5309427 (s : real -> Prop) : (term377 s) = (term368 s).
Proof. exact (eq_refl (term377 s)). Qed.
Lemma lem5309428 (x : type1627) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5309429 (s : real -> Prop) (x : type1627) : (term378 s x) = (term379 s x).
Proof. exact (MK_COMB (@lem5309427 s) (@lem5309428 x)). Qed.
Lemma lem5309430 (x : type1627) (s : real -> Prop) : (term379 s x) = (term367 x s).
Proof. exact (eq_refl (term379 s x)). Qed.
Lemma lem5309431 (x : type1627) (s : real -> Prop) : (term378 s x) = (term367 x s).
Proof. exact (TRANS (@lem5309429 s x) (@lem5309430 x s)). Qed.
Lemma lem5309432 (s : real -> Prop) : (term380 s) = (term368 s).
Proof. exact (fun_ext (fun x : type1627 => @lem5309431 x s)). Qed.
Lemma lem5309433 : (@ex (real -> real -> real)) = (@ex (real -> real -> real)).
Proof. exact (eq_refl (@ex (real -> real -> real))). Qed.
Lemma lem5309434 (s : real -> Prop) : (term381 s) = (term369 s).
Proof. exact (MK_COMB (@lem5309433) (@lem5309432 s)). Qed.
Lemma lem5309435 : term382 = term370.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5309434 s)). Qed.
Lemma lem5309436 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5309437 : term374 = term371.
Proof. exact (MK_COMB (@lem5309436) (@lem5309435)). Qed.
Lemma lem5309438 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5309439 : term383 = term384.
Proof. exact (MK_COMB (@lem5309438) (@lem5309437)). Qed.
Lemma lem5309440 (s : real -> Prop) : (term377 s) = (term368 s).
Proof. exact (eq_refl (term377 s)). Qed.
Lemma lem5309441 (x : type1019) (s : real -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem5309442 (x : type1019) (s : real -> Prop) : (term385 x s) = (term386 x s).
Proof. exact (MK_COMB (@lem5309440 s) (@lem5309441 x s)). Qed.
Lemma lem5309443 (x : type1019) (s : real -> Prop) : (term386 x s) = (term387 x s).
Proof. exact (eq_refl (term386 x s)). Qed.
Lemma lem5309444 (x : type1019) (s : real -> Prop) : (term385 x s) = (term387 x s).
Proof. exact (TRANS (@lem5309442 x s) (@lem5309443 x s)). Qed.
Lemma lem5309445 (x : type1019) : (term388 x) = (term389 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5309444 x s)). Qed.
Lemma lem5309446 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5309447 (x : type1019) : (term390 x) = (term391 x).
Proof. exact (MK_COMB (@lem5309446) (@lem5309445 x)). Qed.
Lemma lem5309448 : term392 = term393.
Proof. exact (fun_ext (fun x : type1019 => @lem5309447 x)). Qed.
Lemma lem5309449 : (@ex ((real -> Prop) -> real -> real -> real)) = (@ex ((real -> Prop) -> real -> real -> real)).
Proof. exact (eq_refl (@ex ((real -> Prop) -> real -> real -> real))). Qed.
Lemma lem5309450 : term375 = term394.
Proof. exact (MK_COMB (@lem5309449) (@lem5309448)). Qed.
Lemma lem5309451 : (term374 = term375) = (term371 = term394).
Proof. exact (MK_COMB (@lem5309439) (@lem5309450)). Qed.
Lemma lem5309452 : term371 = term394.
Proof. exact (EQ_MP (@lem5309451) (@lem5309426)). Qed.
Lemma lem5309454 {A B : Type'} (P : type1413 A B) : (term225 A B P) = (term226 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5309455 (P : type1017) : (term395 P) = (term396 P).
Proof. exact (@lem5309454 (real -> Prop) (real -> real) P). Qed.
Lemma lem5309456 (x : type1019) : (term397 x) = (term398 x).
Proof. exact (@lem5309455 (term399 x)). Qed.
Lemma lem5309457 (x : type1019) (s : real -> Prop) : (term400 x s) = (term401 x s).
Proof. exact (eq_refl (term400 x s)). Qed.
Lemma lem5309458 (x : real -> real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5309459 (x : type1019) (s : real -> Prop) (x' : real -> real) : (term402 x s x') = (term403 x s x').
Proof. exact (MK_COMB (@lem5309457 x s) (@lem5309458 x')). Qed.
Lemma lem5309460 (x : type1019) (s : real -> Prop) (x' : real -> real) : (term403 x s x') = (term404 x s x').
Proof. exact (eq_refl (term403 x s x')). Qed.
Lemma lem5309461 (x : type1019) (s : real -> Prop) (x' : real -> real) : (term402 x s x') = (term404 x s x').
Proof. exact (TRANS (@lem5309459 x s x') (@lem5309460 x s x')). Qed.
Lemma lem5309462 (x : type1019) (s : real -> Prop) : (term405 x s) = (term401 x s).
Proof. exact (fun_ext (fun x' : real -> real => @lem5309461 x s x')). Qed.
Lemma lem5309463 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5309464 (x : type1019) (s : real -> Prop) : (term406 x s) = (term387 x s).
Proof. exact (MK_COMB (@lem5309463) (@lem5309462 x s)). Qed.
Lemma lem5309465 (x : type1019) : (term407 x) = (term389 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5309464 x s)). Qed.
Lemma lem5309466 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5309467 (x : type1019) : (term397 x) = (term391 x).
Proof. exact (MK_COMB (@lem5309466) (@lem5309465 x)). Qed.
Lemma lem5309468 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5309469 (x : type1019) : (term408 x) = (term409 x).
Proof. exact (MK_COMB (@lem5309468) (@lem5309467 x)). Qed.
Lemma lem5309470 (x : type1019) (s : real -> Prop) : (term400 x s) = (term401 x s).
Proof. exact (eq_refl (term400 x s)). Qed.
Lemma lem5309471 (x : type1021) (s : real -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem5309472 (x : type1019) (x' : type1021) (s : real -> Prop) : (term410 x x' s) = (term411 x x' s).
Proof. exact (MK_COMB (@lem5309470 x s) (@lem5309471 x' s)). Qed.
Lemma lem5309473 (x : type1019) (x' : type1021) (s : real -> Prop) : (term411 x x' s) = (term412 x x' s).
Proof. exact (eq_refl (term411 x x' s)). Qed.
Lemma lem5309474 (x : type1019) (x' : type1021) (s : real -> Prop) : (term410 x x' s) = (term412 x x' s).
Proof. exact (TRANS (@lem5309472 x x' s) (@lem5309473 x x' s)). Qed.
Lemma lem5309475 (x : type1019) (x' : type1021) : (term413 x x') = (term414 x x').
Proof. exact (fun_ext (fun s : real -> Prop => @lem5309474 x x' s)). Qed.
Lemma lem5309476 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5309477 (x : type1019) (x' : type1021) : (term415 x x') = (term416 x x').
Proof. exact (MK_COMB (@lem5309476) (@lem5309475 x x')). Qed.
Lemma lem5309478 (x : type1019) : (term417 x) = (term418 x).
Proof. exact (fun_ext (fun x' : type1021 => @lem5309477 x x')). Qed.
Lemma lem5309479 : (@ex ((real -> Prop) -> real -> real)) = (@ex ((real -> Prop) -> real -> real)).
Proof. exact (eq_refl (@ex ((real -> Prop) -> real -> real))). Qed.
Lemma lem5309480 (x : type1019) : (term398 x) = (term419 x).
Proof. exact (MK_COMB (@lem5309479) (@lem5309478 x)). Qed.
Lemma lem5309481 (x : type1019) : ((term397 x) = (term398 x)) = ((term391 x) = (term419 x)).
Proof. exact (MK_COMB (@lem5309469 x) (@lem5309480 x)). Qed.
Lemma lem5309482 (x : type1019) : (term391 x) = (term419 x).
Proof. exact (EQ_MP (@lem5309481 x) (@lem5309456 x)). Qed.
Lemma lem5309483 : term393 = term420.
Proof. exact (fun_ext (fun x : type1019 => @lem5309482 x)). Qed.
Lemma lem5309484 : (@ex ((real -> Prop) -> real -> real -> real)) = (@ex ((real -> Prop) -> real -> real -> real)).
Proof. exact (eq_refl (@ex ((real -> Prop) -> real -> real -> real))). Qed.
Lemma lem5309485 : term394 = term421.
Proof. exact (MK_COMB (@lem5309484) (@lem5309483)). Qed.
Lemma lem5309486 : term371 = term421.
Proof. exact (TRANS (@lem5309452) (@lem5309485)). Qed.
Lemma lem5309488 : term224 = term421.
Proof. exact (TRANS (@lem5309422) (@lem5309486)). Qed.
Lemma lem5309489 : term41 = term421.
Proof. exact (TRANS (@lem5309061) (@lem5309488)). Qed.
Lemma lem5309490 (h1 : term41) : term421.
Proof. exact (EQ_MP (@lem5309489) (@lem5308650 h1)). Qed.
Lemma lem5309491 (x : type1019) (h1 : term419 x) : term419 x.
Proof. exact (h1). Qed.
Lemma lem5309492 (x : type1019) (x' : type1021) (h1 : term416 x x') : term416 x x'.
Proof. exact (h1). Qed.
Lemma lem5309493 (s : real -> Prop) (h1 : term186 s) : term186 s.
Proof. exact (h1). Qed.
Lemma lem5309494 (l : real) (s : real -> Prop) (h1 : term184 l s) : term184 l s.
Proof. exact (h1). Qed.
Lemma lem5309495 (l : real) (s : real -> Prop) (c : real) (h1 : term182 l s c) : term182 l s c.
Proof. exact (h1). Qed.
Lemma lem5309496 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term179 b l s c.
Proof. exact (h1). Qed.
Lemma lem5309517 (x' : type1021) (s : real -> Prop) (c : real) : (term422 x' s c) = (term422 x' s c).
Proof. exact (eq_refl (term422 x' s c)). Qed.
Lemma lem5309526 (c : real) (s : real -> Prop) : (term206 c s) = (term206 c s).
Proof. exact (eq_refl (term206 c s)). Qed.
Lemma lem5309553 (x : type1019) (s : real -> Prop) (c : real) (b : real) : (term423 x s c b) = (term423 x s c b).
Proof. exact (eq_refl (term423 x s c b)). Qed.
Lemma lem5309554 (x : type1019) (s : real -> Prop) (c : real) : (term424 x s c) = (term424 x s c).
Proof. exact (fun_ext (fun b : real => @lem5309553 x s c b)). Qed.
Lemma lem5309555 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5309556 (x : type1019) (s : real -> Prop) (c : real) : (term425 x s c) = (term425 x s c).
Proof. exact (MK_COMB (@lem5309555) (@lem5309554 x s c)). Qed.
Lemma lem5309557 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5309558 (x : type1019) (s : real -> Prop) (c : real) : (term426 x s c) = (term426 x s c).
Proof. exact (MK_COMB (@lem5309557) (@lem5309556 x s c)). Qed.
Lemma lem5309559 (x : type1019) (c : real) (s : real -> Prop) : (term427 x c s) = (term427 x c s).
Proof. exact (MK_COMB (@lem5309558 x s c) (@lem5309526 c s)). Qed.
Lemma lem5309566 (s : real -> Prop) : (term213 s) = (term213 s).
Proof. exact (eq_refl (term213 s)). Qed.
Lemma lem5309567 (x : type1019) (c : real) (s : real -> Prop) : (term428 x c s) = (term428 x c s).
Proof. exact (MK_COMB (@lem5309566 s) (@lem5309559 x c s)). Qed.
Lemma lem5309568 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5309569 (x : type1019) (c : real) (s : real -> Prop) : (term429 x c s) = (term429 x c s).
Proof. exact (MK_COMB (@lem5309568) (@lem5309567 x c s)). Qed.
Lemma lem5309570 (x : type1019) (x' : type1021) (s : real -> Prop) (c : real) : (term430 x x' s c) = (term430 x x' s c).
Proof. exact (MK_COMB (@lem5309569 x c s) (@lem5309517 x' s c)). Qed.
Lemma lem5309571 (x : type1019) (x' : type1021) (s : real -> Prop) : (term431 x x' s) = (term431 x x' s).
Proof. exact (fun_ext (fun c : real => @lem5309570 x x' s c)). Qed.
Lemma lem5309572 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5309573 (x : type1019) (x' : type1021) (s : real -> Prop) : (term412 x x' s) = (term412 x x' s).
Proof. exact (MK_COMB (@lem5309572) (@lem5309571 x x' s)). Qed.
Lemma lem5309574 (x : type1019) (x' : type1021) : (term414 x x') = (term414 x x').
Proof. exact (fun_ext (fun s : real -> Prop => @lem5309573 x x' s)). Qed.
Lemma lem5309575 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5309576 (x : type1019) (x' : type1021) : (term416 x x') = (term416 x x').
Proof. exact (MK_COMB (@lem5309575) (@lem5309574 x x')). Qed.
Lemma lem5309577 (x : type1019) (x' : type1021) (h1 : term416 x x') : term416 x x'.
Proof. exact (EQ_MP (@lem5309576 x x') (@lem5309492 x x' h1)). Qed.
Lemma lem5309594 (s : real -> Prop) (c : real) (x : real) : (term73 s c x) = (term73 s c x).
Proof. exact (eq_refl (term73 s c x)). Qed.
Lemma lem5309595 (s : real -> Prop) (c : real) : (term81 s c) = (term81 s c).
Proof. exact (fun_ext (fun x : real => @lem5309594 s c x)). Qed.
Lemma lem5309596 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5309597 (s : real -> Prop) (c : real) : (term82 s c) = (term82 s c).
Proof. exact (MK_COMB (@lem5309596) (@lem5309595 s c)). Qed.
Lemma lem5309602 (c : real) (l : real) : (real_lt c l) = (real_lt c l).
Proof. exact (eq_refl (real_lt c l)). Qed.
Lemma lem5309609 (s : real -> Prop) (l : real) : ((sup s) = l) = ((sup s) = l).
Proof. exact (eq_refl ((sup s) = l)). Qed.
Lemma lem5309624 (s : real -> Prop) (x : real) (b : real) : (term62 s x b) = (term62 s x b).
Proof. exact (eq_refl (term62 s x b)). Qed.
Lemma lem5309625 (s : real -> Prop) (b : real) : (term63 s b) = (term63 s b).
Proof. exact (fun_ext (fun x : real => @lem5309624 s x b)). Qed.
Lemma lem5309626 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5309627 (s : real -> Prop) (b : real) : (term64 s b) = (term64 s b).
Proof. exact (MK_COMB (@lem5309626) (@lem5309625 s b)). Qed.
Lemma lem5309628 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5309629 (s : real -> Prop) (b : real) : (term125 s b) = (term125 s b).
Proof. exact (MK_COMB (@lem5309628) (@lem5309627 s b)). Qed.
Lemma lem5309630 (b : real) (s : real -> Prop) (l : real) : (term127 b s l) = (term127 b s l).
Proof. exact (MK_COMB (@lem5309629 s b) (@lem5309609 s l)). Qed.
Lemma lem5309639 (s : real -> Prop) : (term54 s) = (term54 s).
Proof. exact (eq_refl (term54 s)). Qed.
Lemma lem5309640 (b : real) (s : real -> Prop) (l : real) : (term145 b s l) = (term145 b s l).
Proof. exact (MK_COMB (@lem5309639 s) (@lem5309630 b s l)). Qed.
Lemma lem5309641 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5309642 (b : real) (s : real -> Prop) (l : real) : (term160 b s l) = (term160 b s l).
Proof. exact (MK_COMB (@lem5309641) (@lem5309640 b s l)). Qed.
Lemma lem5309643 (b : real) (s : real -> Prop) (c : real) (l : real) : (term162 b s c l) = (term162 b s c l).
Proof. exact (MK_COMB (@lem5309642 b s l) (@lem5309602 c l)). Qed.
Lemma lem5309644 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5309645 (b : real) (s : real -> Prop) (c : real) (l : real) : (term177 b s c l) = (term177 b s c l).
Proof. exact (MK_COMB (@lem5309644) (@lem5309643 b s c l)). Qed.
Lemma lem5309646 (b : real) (l : real) (s : real -> Prop) (c : real) : (term179 b l s c) = (term179 b l s c).
Proof. exact (MK_COMB (@lem5309645 b s c l) (@lem5309597 s c)). Qed.
Lemma lem5309647 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term179 b l s c.
Proof. exact (EQ_MP (@lem5309646 b l s c) (@lem5309496 b l s c h1)). Qed.
Lemma lem5309648 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term82 s c.
Proof. exact (proj2 (@lem5309647 b l s c h1)). Qed.
Lemma lem5309649 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term162 b s c l.
Proof. exact (proj1 (@lem5309647 b l s c h1)). Qed.
Lemma lem5309651 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term145 b s l.
Proof. exact (proj1 (@lem5309649 b l s c h1)). Qed.
Lemma lem5309652 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term127 b s l.
Proof. exact (proj2 (@lem5309651 b l s c h1)). Qed.
Lemma lem5309655 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term64 s b.
Proof. exact (proj1 (@lem5309652 b l s c h1)). Qed.
Lemma lem5309657 {A : Type'} (P : A -> Prop) (Q : Prop) : (term432 A P Q) = (term433 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem5309658 (P : real -> Prop) (Q : Prop) : (term434 P Q) = (term435 P Q).
Proof. exact (@lem5309657 real P Q). Qed.
Lemma lem5309659 (x : type1019) (c : real) (s : real -> Prop) : (term436 x c s) = (term437 x c s).
Proof. exact (@lem5309658 (term424 x s c) (term206 c s)). Qed.
Lemma lem5309660 (x : type1019) (s : real -> Prop) (c : real) (b : real) : (term438 x s c b) = (term423 x s c b).
Proof. exact (eq_refl (term438 x s c b)). Qed.
Lemma lem5309661 (x : type1019) (s : real -> Prop) (c : real) : (term439 x s c) = (term424 x s c).
Proof. exact (fun_ext (fun b : real => @lem5309660 x s c b)). Qed.
Lemma lem5309662 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5309663 (x : type1019) (s : real -> Prop) (c : real) : (term440 x s c) = (term425 x s c).
Proof. exact (MK_COMB (@lem5309662) (@lem5309661 x s c)). Qed.
Lemma lem5309664 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5309665 (x : type1019) (s : real -> Prop) (c : real) : (term441 x s c) = (term426 x s c).
Proof. exact (MK_COMB (@lem5309664) (@lem5309663 x s c)). Qed.
Lemma lem5309666 (c : real) (s : real -> Prop) : (term206 c s) = (term206 c s).
Proof. exact (eq_refl (term206 c s)). Qed.
Lemma lem5309667 (x : type1019) (c : real) (s : real -> Prop) : (term436 x c s) = (term427 x c s).
Proof. exact (MK_COMB (@lem5309665 x s c) (@lem5309666 c s)). Qed.
Lemma lem5309668 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5309669 (x : type1019) (c : real) (s : real -> Prop) : (term442 x c s) = (term443 x c s).
Proof. exact (MK_COMB (@lem5309668) (@lem5309667 x c s)). Qed.
Lemma lem5309670 (x : type1019) (s : real -> Prop) (c : real) (b : real) : (term438 x s c b) = (term423 x s c b).
Proof. exact (eq_refl (term438 x s c b)). Qed.
Lemma lem5309671 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5309672 (x : type1019) (s : real -> Prop) (c : real) (b : real) : (term444 x s c b) = (term445 x s c b).
Proof. exact (MK_COMB (@lem5309671) (@lem5309670 x s c b)). Qed.
Lemma lem5309673 (c : real) (s : real -> Prop) : (term206 c s) = (term206 c s).
Proof. exact (eq_refl (term206 c s)). Qed.
Lemma lem5309674 (x : type1019) (b : real) (c : real) (s : real -> Prop) : (term446 x b c s) = (term447 x b c s).
Proof. exact (MK_COMB (@lem5309672 x s c b) (@lem5309673 c s)). Qed.
Lemma lem5309675 (x : type1019) (c : real) (s : real -> Prop) : (term448 x c s) = (term449 x c s).
Proof. exact (fun_ext (fun b : real => @lem5309674 x b c s)). Qed.
Lemma lem5309676 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5309677 (x : type1019) (c : real) (s : real -> Prop) : (term437 x c s) = (term450 x c s).
Proof. exact (MK_COMB (@lem5309676) (@lem5309675 x c s)). Qed.
Lemma lem5309678 (x : type1019) (c : real) (s : real -> Prop) : ((term436 x c s) = (term437 x c s)) = ((term427 x c s) = (term450 x c s)).
Proof. exact (MK_COMB (@lem5309669 x c s) (@lem5309677 x c s)). Qed.
Lemma lem5309679 (x : type1019) (c : real) (s : real -> Prop) : (term427 x c s) = (term450 x c s).
Proof. exact (EQ_MP (@lem5309678 x c s) (@lem5309659 x c s)). Qed.
Lemma lem5309680 (s : real -> Prop) : (term213 s) = (term213 s).
Proof. exact (eq_refl (term213 s)). Qed.
Lemma lem5309681 (x : type1019) (c : real) (s : real -> Prop) : (term428 x c s) = (term451 x c s).
Proof. exact (MK_COMB (@lem5309680 s) (@lem5309679 x c s)). Qed.
Lemma lem5309683 {A : Type'} (P : Prop) (Q : A -> Prop) : (term452 A P Q) = (term453 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5309684 (P : Prop) (Q : real -> Prop) : (term454 P Q) = (term455 P Q).
Proof. exact (@lem5309683 real P Q). Qed.
Lemma lem5309685 (x : type1019) (c : real) (s : real -> Prop) : (term456 x c s) = (term457 x c s).
Proof. exact (@lem5309684 (s = (@EMPTY real)) (term449 x c s)). Qed.
Lemma lem5309686 (x : type1019) (b : real) (c : real) (s : real -> Prop) : (term458 x c s b) = (term447 x b c s).
Proof. exact (eq_refl (term458 x c s b)). Qed.
Lemma lem5309687 (x : type1019) (c : real) (s : real -> Prop) : (term459 x c s) = (term449 x c s).
Proof. exact (fun_ext (fun b : real => @lem5309686 x b c s)). Qed.
Lemma lem5309688 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5309689 (x : type1019) (c : real) (s : real -> Prop) : (term460 x c s) = (term450 x c s).
Proof. exact (MK_COMB (@lem5309688) (@lem5309687 x c s)). Qed.
Lemma lem5309690 (s : real -> Prop) : (term213 s) = (term213 s).
Proof. exact (eq_refl (term213 s)). Qed.
Lemma lem5309691 (x : type1019) (c : real) (s : real -> Prop) : (term456 x c s) = (term451 x c s).
Proof. exact (MK_COMB (@lem5309690 s) (@lem5309689 x c s)). Qed.
Lemma lem5309692 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5309693 (x : type1019) (c : real) (s : real -> Prop) : (term461 x c s) = (term462 x c s).
Proof. exact (MK_COMB (@lem5309692) (@lem5309691 x c s)). Qed.
Lemma lem5309694 (x : type1019) (b : real) (c : real) (s : real -> Prop) : (term458 x c s b) = (term447 x b c s).
Proof. exact (eq_refl (term458 x c s b)). Qed.
Lemma lem5309695 (s : real -> Prop) : (term213 s) = (term213 s).
Proof. exact (eq_refl (term213 s)). Qed.
Lemma lem5309696 (x : type1019) (b : real) (c : real) (s : real -> Prop) : (term463 x c s b) = (term464 x b c s).
Proof. exact (MK_COMB (@lem5309695 s) (@lem5309694 x b c s)). Qed.
Lemma lem5309697 (x : type1019) (c : real) (s : real -> Prop) : (term465 x c s) = (term466 x c s).
Proof. exact (fun_ext (fun b : real => @lem5309696 x b c s)). Qed.
Lemma lem5309698 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5309699 (x : type1019) (c : real) (s : real -> Prop) : (term457 x c s) = (term467 x c s).
Proof. exact (MK_COMB (@lem5309698) (@lem5309697 x c s)). Qed.
Lemma lem5309700 (x : type1019) (c : real) (s : real -> Prop) : ((term456 x c s) = (term457 x c s)) = ((term451 x c s) = (term467 x c s)).
Proof. exact (MK_COMB (@lem5309693 x c s) (@lem5309699 x c s)). Qed.
Lemma lem5309701 (x : type1019) (c : real) (s : real -> Prop) : (term451 x c s) = (term467 x c s).
Proof. exact (EQ_MP (@lem5309700 x c s) (@lem5309685 x c s)). Qed.
Lemma lem5309702 (x : type1019) (c : real) (s : real -> Prop) : (term428 x c s) = (term467 x c s).
Proof. exact (TRANS (@lem5309681 x c s) (@lem5309701 x c s)). Qed.
Lemma lem5309703 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5309704 (x : type1019) (c : real) (s : real -> Prop) : (term429 x c s) = (term468 x c s).
Proof. exact (MK_COMB (@lem5309703) (@lem5309702 x c s)). Qed.
Lemma lem5309705 (x' : type1021) (s : real -> Prop) (c : real) : (term422 x' s c) = (term422 x' s c).
Proof. exact (eq_refl (term422 x' s c)). Qed.
Lemma lem5309706 (x : type1019) (x' : type1021) (s : real -> Prop) (c : real) : (term430 x x' s c) = (term469 x x' s c).
Proof. exact (MK_COMB (@lem5309704 x c s) (@lem5309705 x' s c)). Qed.
Lemma lem5309708 {A : Type'} (P : A -> Prop) (Q : Prop) : (term432 A P Q) = (term433 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem5309709 (P : real -> Prop) (Q : Prop) : (term434 P Q) = (term435 P Q).
Proof. exact (@lem5309708 real P Q). Qed.
Lemma lem5309710 (x : type1019) (x' : type1021) (s : real -> Prop) (c : real) : (term470 x x' s c) = (term471 x x' s c).
Proof. exact (@lem5309709 (term466 x c s) (term422 x' s c)). Qed.
Lemma lem5309711 (x : type1019) (b : real) (c : real) (s : real -> Prop) : (term472 x c s b) = (term464 x b c s).
Proof. exact (eq_refl (term472 x c s b)). Qed.
Lemma lem5309712 (x : type1019) (c : real) (s : real -> Prop) : (term473 x c s) = (term466 x c s).
Proof. exact (fun_ext (fun b : real => @lem5309711 x b c s)). Qed.
Lemma lem5309713 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5309714 (x : type1019) (c : real) (s : real -> Prop) : (term474 x c s) = (term467 x c s).
Proof. exact (MK_COMB (@lem5309713) (@lem5309712 x c s)). Qed.
Lemma lem5309715 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5309716 (x : type1019) (c : real) (s : real -> Prop) : (term475 x c s) = (term468 x c s).
Proof. exact (MK_COMB (@lem5309715) (@lem5309714 x c s)). Qed.
Lemma lem5309717 (x' : type1021) (s : real -> Prop) (c : real) : (term422 x' s c) = (term422 x' s c).
Proof. exact (eq_refl (term422 x' s c)). Qed.
Lemma lem5309718 (x : type1019) (x' : type1021) (s : real -> Prop) (c : real) : (term470 x x' s c) = (term469 x x' s c).
Proof. exact (MK_COMB (@lem5309716 x c s) (@lem5309717 x' s c)). Qed.
Lemma lem5309719 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5309720 (x : type1019) (x' : type1021) (s : real -> Prop) (c : real) : (term476 x x' s c) = (term477 x x' s c).
Proof. exact (MK_COMB (@lem5309719) (@lem5309718 x x' s c)). Qed.
Lemma lem5309721 (x : type1019) (b : real) (c : real) (s : real -> Prop) : (term472 x c s b) = (term464 x b c s).
Proof. exact (eq_refl (term472 x c s b)). Qed.
Lemma lem5309722 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5309723 (x : type1019) (b : real) (c : real) (s : real -> Prop) : (term478 x c s b) = (term479 x b c s).
Proof. exact (MK_COMB (@lem5309722) (@lem5309721 x b c s)). Qed.
Lemma lem5309724 (x' : type1021) (s : real -> Prop) (c : real) : (term422 x' s c) = (term422 x' s c).
Proof. exact (eq_refl (term422 x' s c)). Qed.
Lemma lem5309725 (x : type1019) (b : real) (x' : type1021) (s : real -> Prop) (c : real) : (term480 x b x' s c) = (term481 x b x' s c).
Proof. exact (MK_COMB (@lem5309723 x b c s) (@lem5309724 x' s c)). Qed.
Lemma lem5309726 (x : type1019) (x' : type1021) (s : real -> Prop) (c : real) : (term482 x x' s c) = (term483 x x' s c).
Proof. exact (fun_ext (fun b : real => @lem5309725 x b x' s c)). Qed.
Lemma lem5309727 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5309728 (x : type1019) (x' : type1021) (s : real -> Prop) (c : real) : (term471 x x' s c) = (term484 x x' s c).
Proof. exact (MK_COMB (@lem5309727) (@lem5309726 x x' s c)). Qed.
Lemma lem5309729 (x : type1019) (x' : type1021) (s : real -> Prop) (c : real) : ((term470 x x' s c) = (term471 x x' s c)) = ((term469 x x' s c) = (term484 x x' s c)).
Proof. exact (MK_COMB (@lem5309720 x x' s c) (@lem5309728 x x' s c)). Qed.
Lemma lem5309730 (x : type1019) (x' : type1021) (s : real -> Prop) (c : real) : (term469 x x' s c) = (term484 x x' s c).
Proof. exact (EQ_MP (@lem5309729 x x' s c) (@lem5309710 x x' s c)). Qed.
Lemma lem5309731 (x : type1019) (x' : type1021) (s : real -> Prop) (c : real) : (term430 x x' s c) = (term484 x x' s c).
Proof. exact (TRANS (@lem5309706 x x' s c) (@lem5309730 x x' s c)). Qed.
Lemma lem5309732 (x : type1019) (x' : type1021) (s : real -> Prop) : (term431 x x' s) = (term485 x x' s).
Proof. exact (fun_ext (fun c : real => @lem5309731 x x' s c)). Qed.
Lemma lem5309733 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5309734 (x : type1019) (x' : type1021) (s : real -> Prop) : (term412 x x' s) = (term486 x x' s).
Proof. exact (MK_COMB (@lem5309733) (@lem5309732 x x' s)). Qed.
Lemma lem5309735 (x : type1019) (x' : type1021) : (term414 x x') = (term487 x x').
Proof. exact (fun_ext (fun s : real -> Prop => @lem5309734 x x' s)). Qed.
Lemma lem5309736 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5309737 (x : type1019) (x' : type1021) : (term416 x x') = (term488 x x').
Proof. exact (MK_COMB (@lem5309736) (@lem5309735 x x')). Qed.
Lemma lem5309742 (x' : type1021) (s : real -> Prop) (c : real) : (term422 x' s c) = (term422 x' s c).
Proof. exact (eq_refl (term422 x' s c)). Qed.
Lemma lem5309759 (x : type1019) (b : real) (c : real) (s : real -> Prop) : (term447 x b c s) = (term489 x b c s).
Proof. exact (@lem19699 (term490 x c b s) (term491 x s c b) (term206 c s)). Qed.
Lemma lem5309762 (s : real -> Prop) : (term213 s) = (term213 s).
Proof. exact (eq_refl (term213 s)). Qed.
Lemma lem5309763 (x : type1019) (b : real) (c : real) (s : real -> Prop) : (term464 x b c s) = (term492 x b c s).
Proof. exact (MK_COMB (@lem5309762 s) (@lem5309759 x b c s)). Qed.
Lemma lem5309770 (x : type1019) (b : real) (c : real) (s : real -> Prop) : (term492 x b c s) = (term493 x b c s).
Proof. exact (@lem19490 (term494 x b c s) (s = (@EMPTY real)) (term495 x b c s)). Qed.
Lemma lem5309771 (x : type1019) (b : real) (c : real) (s : real -> Prop) : (term464 x b c s) = (term493 x b c s).
Proof. exact (TRANS (@lem5309763 x b c s) (@lem5309770 x b c s)). Qed.
Lemma lem5309772 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5309773 (x : type1019) (b : real) (c : real) (s : real -> Prop) : (term479 x b c s) = (term496 x b c s).
Proof. exact (MK_COMB (@lem5309772) (@lem5309771 x b c s)). Qed.
Lemma lem5309774 (x : type1019) (b : real) (x' : type1021) (s : real -> Prop) (c : real) : (term481 x b x' s c) = (term497 x b x' s c).
Proof. exact (MK_COMB (@lem5309773 x b c s) (@lem5309742 x' s c)). Qed.
Lemma lem5309775 (x : type1019) (b : real) (x' : type1021) (s : real -> Prop) (c : real) : (term497 x b x' s c) = (term498 x b x' s c).
Proof. exact (@lem19490 (term499 x' c s) (term493 x b c s) (term500 x' s c)). Qed.
Lemma lem5309782 (x : type1019) (b : real) (x' : type1021) (s : real -> Prop) (c : real) : (term501 x b x' s c) = (term502 x b x' s c).
Proof. exact (@lem19699 (term503 x b c s) (term504 x b c s) (term500 x' s c)). Qed.
Lemma lem5309789 (x : type1019) (b : real) (x' : type1021) (c : real) (s : real -> Prop) : (term505 x b x' c s) = (term506 x b x' c s).
Proof. exact (@lem19699 (term503 x b c s) (term504 x b c s) (term499 x' c s)). Qed.
Lemma lem5309790 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5309791 (x : type1019) (b : real) (x' : type1021) (c : real) (s : real -> Prop) : (term507 x b x' c s) = (term508 x b x' c s).
Proof. exact (MK_COMB (@lem5309790) (@lem5309789 x b x' c s)). Qed.
Lemma lem5309792 (x : type1019) (b : real) (x' : type1021) (s : real -> Prop) (c : real) : (term498 x b x' s c) = (term509 x b x' s c).
Proof. exact (MK_COMB (@lem5309791 x b x' c s) (@lem5309782 x b x' s c)). Qed.
Lemma lem5309793 (x : type1019) (b : real) (x' : type1021) (s : real -> Prop) (c : real) : (term497 x b x' s c) = (term509 x b x' s c).
Proof. exact (TRANS (@lem5309775 x b x' s c) (@lem5309792 x b x' s c)). Qed.
Lemma lem5309794 (x : type1019) (b : real) (x' : type1021) (s : real -> Prop) (c : real) : (term481 x b x' s c) = (term509 x b x' s c).
Proof. exact (TRANS (@lem5309774 x b x' s c) (@lem5309793 x b x' s c)). Qed.
Lemma lem5309795 (x : type1019) (x' : type1021) (s : real -> Prop) (c : real) : (term483 x x' s c) = (term510 x x' s c).
Proof. exact (fun_ext (fun b : real => @lem5309794 x b x' s c)). Qed.
Lemma lem5309796 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5309797 (x : type1019) (x' : type1021) (s : real -> Prop) (c : real) : (term484 x x' s c) = (term511 x x' s c).
Proof. exact (MK_COMB (@lem5309796) (@lem5309795 x x' s c)). Qed.
Lemma lem5309798 (x : type1019) (x' : type1021) (s : real -> Prop) : (term485 x x' s) = (term512 x x' s).
Proof. exact (fun_ext (fun c : real => @lem5309797 x x' s c)). Qed.
Lemma lem5309799 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5309800 (x : type1019) (x' : type1021) (s : real -> Prop) : (term486 x x' s) = (term513 x x' s).
Proof. exact (MK_COMB (@lem5309799) (@lem5309798 x x' s)). Qed.
Lemma lem5309801 (x : type1019) (x' : type1021) : (term487 x x') = (term514 x x').
Proof. exact (fun_ext (fun s : real -> Prop => @lem5309800 x x' s)). Qed.
Lemma lem5309802 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5309803 (x : type1019) (x' : type1021) : (term488 x x') = (term515 x x').
Proof. exact (MK_COMB (@lem5309802) (@lem5309801 x x')). Qed.
Lemma lem5309804 (x : type1019) (x' : type1021) : (term416 x x') = (term515 x x').
Proof. exact (TRANS (@lem5309737 x x') (@lem5309803 x x')). Qed.
Lemma lem5309805 (x : type1019) (x' : type1021) (h1 : term416 x x') : term515 x x'.
Proof. exact (EQ_MP (@lem5309804 x x') (@lem5309577 x x' h1)). Qed.
Lemma lem5309813 (s : real -> Prop) (c : real) (x : real) : (term73 s c x) = (term73 s c x).
Proof. exact (eq_refl (term73 s c x)). Qed.
Lemma lem5309814 (s : real -> Prop) (c : real) : (term81 s c) = (term81 s c).
Proof. exact (fun_ext (fun x : real => @lem5309813 s c x)). Qed.
Lemma lem5309815 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5309817 (s : real -> Prop) (c : real) : (term82 s c) = (term82 s c).
Proof. exact (MK_COMB (@lem5309815) (@lem5309814 s c)). Qed.
Lemma lem5309818 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term82 s c.
Proof. exact (EQ_MP (@lem5309817 s c) (@lem5309648 b l s c h1)). Qed.
Lemma lem5309834 (s : real -> Prop) (x : real) (b : real) : (term62 s x b) = (term62 s x b).
Proof. exact (eq_refl (term62 s x b)). Qed.
Lemma lem5309835 (s : real -> Prop) (b : real) : (term63 s b) = (term63 s b).
Proof. exact (fun_ext (fun x : real => @lem5309834 s x b)). Qed.
Lemma lem5309836 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5309838 (s : real -> Prop) (b : real) : (term64 s b) = (term64 s b).
Proof. exact (MK_COMB (@lem5309836) (@lem5309835 s b)). Qed.
Lemma lem5309839 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term64 s b.
Proof. exact (EQ_MP (@lem5309838 s b) (@lem5309655 b l s c h1)). Qed.
Lemma lem5309844 (_69627 : real -> Prop) (x : type1019) (x' : type1021) (h1 : term416 x x') : term516 x x' _69627.
Proof. exact (@lem5309805 x x' h1 _69627). Qed.
Lemma lem5309845 (x : type1019) (x' : type1021) (_69627 : real -> Prop) : (term516 x x' _69627) = (term513 x x' _69627).
Proof. exact (eq_refl (term516 x x' _69627)). Qed.
Lemma lem5309846 (_69627 : real -> Prop) (x : type1019) (x' : type1021) (h1 : term416 x x') : term513 x x' _69627.
Proof. exact (EQ_MP (@lem5309845 x x' _69627) (@lem5309844 _69627 x x' h1)). Qed.
Lemma lem5309847 (_69627 : real -> Prop) (_69628 : real) (x : type1019) (x' : type1021) (h1 : term416 x x') : term517 x x' _69627 _69628.
Proof. exact (@lem5309846 _69627 x x' h1 _69628). Qed.
Lemma lem5309848 (x : type1019) (x' : type1021) (_69627 : real -> Prop) (_69628 : real) : (term517 x x' _69627 _69628) = (term511 x x' _69627 _69628).
Proof. exact (eq_refl (term517 x x' _69627 _69628)). Qed.
Lemma lem5309849 (_69627 : real -> Prop) (_69628 : real) (x : type1019) (x' : type1021) (h1 : term416 x x') : term511 x x' _69627 _69628.
Proof. exact (EQ_MP (@lem5309848 x x' _69627 _69628) (@lem5309847 _69627 _69628 x x' h1)). Qed.
Lemma lem5309850 (_69627 : real -> Prop) (_69628 : real) (_69629 : real) (x : type1019) (x' : type1021) (h1 : term416 x x') : term518 x x' _69627 _69628 _69629.
Proof. exact (@lem5309849 _69627 _69628 x x' h1 _69629). Qed.
Lemma lem5309851 (x : type1019) (_69629 : real) (x' : type1021) (_69627 : real -> Prop) (_69628 : real) : (term518 x x' _69627 _69628 _69629) = (term509 x _69629 x' _69627 _69628).
Proof. exact (eq_refl (term518 x x' _69627 _69628 _69629)). Qed.
Lemma lem5309852 (_69629 : real) (_69627 : real -> Prop) (_69628 : real) (x : type1019) (x' : type1021) (h1 : term416 x x') : term509 x _69629 x' _69627 _69628.
Proof. exact (EQ_MP (@lem5309851 x _69629 x' _69627 _69628) (@lem5309850 _69627 _69628 _69629 x x' h1)). Qed.
Lemma lem5309853 (_69630 : real) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term519 s c _69630.
Proof. exact (@lem5309818 b l s c h1 _69630). Qed.
Lemma lem5309854 (s : real -> Prop) (c : real) (_69630 : real) : (term519 s c _69630) = (term73 s c _69630).
Proof. exact (eq_refl (term519 s c _69630)). Qed.
Lemma lem5309856 (_69631 : real) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term520 s b _69631.
Proof. exact (@lem5309839 b l s c h1 _69631). Qed.
Lemma lem5309857 (s : real -> Prop) (_69631 : real) (b : real) : (term520 s b _69631) = (term62 s _69631 b).
Proof. exact (eq_refl (term520 s b _69631)). Qed.
Lemma lem5309859 (_69629 : real) (_69627 : real -> Prop) (_69628 : real) (x : type1019) (x' : type1021) (h1 : term416 x x') : term502 x _69629 x' _69627 _69628.
Proof. exact (proj2 (@lem5309852 _69629 _69627 _69628 x x' h1)). Qed.
Lemma lem5309860 (_69629 : real) (_69628 : real) (_69627 : real -> Prop) (x : type1019) (x' : type1021) (h1 : term416 x x') : term506 x _69629 x' _69628 _69627.
Proof. exact (proj1 (@lem5309852 _69629 _69627 _69628 x x' h1)). Qed.
Lemma lem5309861 (_69629 : real) (_69627 : real -> Prop) (_69628 : real) (x : type1019) (x' : type1021) (h1 : term416 x x') : term521 x _69629 x' _69627 _69628.
Proof. exact (proj2 (@lem5309859 _69629 _69627 _69628 x x' h1)). Qed.
Lemma lem5309862 (_69629 : real) (_69627 : real -> Prop) (_69628 : real) (x : type1019) (x' : type1021) (h1 : term416 x x') : term522 x _69629 x' _69627 _69628.
Proof. exact (proj1 (@lem5309859 _69629 _69627 _69628 x x' h1)). Qed.
Lemma lem5309863 (_69629 : real) (_69628 : real) (_69627 : real -> Prop) (x : type1019) (x' : type1021) (h1 : term416 x x') : term523 x _69629 x' _69628 _69627.
Proof. exact (proj2 (@lem5309860 _69629 _69628 _69627 x x' h1)). Qed.
Lemma lem5309864 (_69629 : real) (_69628 : real) (_69627 : real -> Prop) (x : type1019) (x' : type1021) (h1 : term416 x x') : term524 x _69629 x' _69628 _69627.
Proof. exact (proj1 (@lem5309860 _69629 _69628 _69627 x x' h1)). Qed.
Lemma lem5309872 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : real_lt c l.
Proof. exact (proj2 (@lem5309649 b l s c h1)). Qed.
Lemma lem5309882 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : (sup s) = l.
Proof. exact (proj2 (@lem5309652 b l s c h1)). Qed.
Lemma lem5309886 (x : type1019) (_69629 : real) (x' : type1021) (_69627 : real -> Prop) (_69628 : real) : (term522 x _69629 x' _69627 _69628) = (term525 x _69629 x' _69627 _69628).
Proof. exact (@lem5308195 (_69627 = (@EMPTY real)) (term494 x _69629 _69628 _69627) (term500 x' _69627 _69628)). Qed.
Lemma lem5309893 (x : type1019) (_69629 : real) (x' : type1021) (_69627 : real -> Prop) (_69628 : real) : (term526 x _69629 x' _69627 _69628) = (term527 x _69629 x' _69627 _69628).
Proof. exact (@lem5308195 (term490 x _69628 _69629 _69627) (term206 _69628 _69627) (term500 x' _69627 _69628)). Qed.
Lemma lem5309894 (_69627 : real -> Prop) : (term213 _69627) = (term213 _69627).
Proof. exact (eq_refl (term213 _69627)). Qed.
Lemma lem5309897 (x : type1019) (_69629 : real) (x' : type1021) (_69627 : real -> Prop) (_69628 : real) : (term525 x _69629 x' _69627 _69628) = (term528 x _69629 x' _69627 _69628).
Proof. exact (MK_COMB (@lem5309894 _69627) (@lem5309893 x _69629 x' _69627 _69628)). Qed.
Lemma lem5309899 (x : type1019) (_69629 : real) (x' : type1021) (_69627 : real -> Prop) (_69628 : real) : (term522 x _69629 x' _69627 _69628) = (term528 x _69629 x' _69627 _69628).
Proof. exact (TRANS (@lem5309886 x _69629 x' _69627 _69628) (@lem5309897 x _69629 x' _69627 _69628)). Qed.
Lemma lem5309904 (x : type1019) (_69629 : real) (x' : type1021) (_69627 : real -> Prop) (_69628 : real) : (term521 x _69629 x' _69627 _69628) = (term529 x _69629 x' _69627 _69628).
Proof. exact (@lem5308195 (_69627 = (@EMPTY real)) (term495 x _69629 _69628 _69627) (term500 x' _69627 _69628)). Qed.
Lemma lem5309911 (x : type1019) (_69629 : real) (x' : type1021) (_69627 : real -> Prop) (_69628 : real) : (term530 x _69629 x' _69627 _69628) = (term531 x _69629 x' _69627 _69628).
Proof. exact (@lem5308195 (term491 x _69627 _69628 _69629) (term206 _69628 _69627) (term500 x' _69627 _69628)). Qed.
Lemma lem5309912 (_69627 : real -> Prop) : (term213 _69627) = (term213 _69627).
Proof. exact (eq_refl (term213 _69627)). Qed.
Lemma lem5309915 (x : type1019) (_69629 : real) (x' : type1021) (_69627 : real -> Prop) (_69628 : real) : (term529 x _69629 x' _69627 _69628) = (term532 x _69629 x' _69627 _69628).
Proof. exact (MK_COMB (@lem5309912 _69627) (@lem5309911 x _69629 x' _69627 _69628)). Qed.
Lemma lem5309917 (x : type1019) (_69629 : real) (x' : type1021) (_69627 : real -> Prop) (_69628 : real) : (term521 x _69629 x' _69627 _69628) = (term532 x _69629 x' _69627 _69628).
Proof. exact (TRANS (@lem5309904 x _69629 x' _69627 _69628) (@lem5309915 x _69629 x' _69627 _69628)). Qed.
Lemma lem5309922 (x : type1019) (_69629 : real) (x' : type1021) (_69628 : real) (_69627 : real -> Prop) : (term524 x _69629 x' _69628 _69627) = (term533 x _69629 x' _69628 _69627).
Proof. exact (@lem5308195 (_69627 = (@EMPTY real)) (term494 x _69629 _69628 _69627) (term499 x' _69628 _69627)). Qed.
Lemma lem5309929 (x : type1019) (_69629 : real) (x' : type1021) (_69628 : real) (_69627 : real -> Prop) : (term534 x _69629 x' _69628 _69627) = (term535 x _69629 x' _69628 _69627).
Proof. exact (@lem5308195 (term490 x _69628 _69629 _69627) (term206 _69628 _69627) (term499 x' _69628 _69627)). Qed.
Lemma lem5309930 (_69627 : real -> Prop) : (term213 _69627) = (term213 _69627).
Proof. exact (eq_refl (term213 _69627)). Qed.
Lemma lem5309933 (x : type1019) (_69629 : real) (x' : type1021) (_69628 : real) (_69627 : real -> Prop) : (term533 x _69629 x' _69628 _69627) = (term536 x _69629 x' _69628 _69627).
Proof. exact (MK_COMB (@lem5309930 _69627) (@lem5309929 x _69629 x' _69628 _69627)). Qed.
Lemma lem5309935 (x : type1019) (_69629 : real) (x' : type1021) (_69628 : real) (_69627 : real -> Prop) : (term524 x _69629 x' _69628 _69627) = (term536 x _69629 x' _69628 _69627).
Proof. exact (TRANS (@lem5309922 x _69629 x' _69628 _69627) (@lem5309933 x _69629 x' _69628 _69627)). Qed.
Lemma lem5309940 (x : type1019) (_69629 : real) (x' : type1021) (_69628 : real) (_69627 : real -> Prop) : (term523 x _69629 x' _69628 _69627) = (term537 x _69629 x' _69628 _69627).
Proof. exact (@lem5308195 (_69627 = (@EMPTY real)) (term495 x _69629 _69628 _69627) (term499 x' _69628 _69627)). Qed.
Lemma lem5309947 (x : type1019) (_69629 : real) (x' : type1021) (_69628 : real) (_69627 : real -> Prop) : (term538 x _69629 x' _69628 _69627) = (term539 x _69629 x' _69628 _69627).
Proof. exact (@lem5308195 (term491 x _69627 _69628 _69629) (term206 _69628 _69627) (term499 x' _69628 _69627)). Qed.
Lemma lem5309948 (_69627 : real -> Prop) : (term213 _69627) = (term213 _69627).
Proof. exact (eq_refl (term213 _69627)). Qed.
Lemma lem5309951 (x : type1019) (_69629 : real) (x' : type1021) (_69628 : real) (_69627 : real -> Prop) : (term537 x _69629 x' _69628 _69627) = (term540 x _69629 x' _69628 _69627).
Proof. exact (MK_COMB (@lem5309948 _69627) (@lem5309947 x _69629 x' _69628 _69627)). Qed.
Lemma lem5309953 (x : type1019) (_69629 : real) (x' : type1021) (_69628 : real) (_69627 : real -> Prop) : (term523 x _69629 x' _69628 _69627) = (term540 x _69629 x' _69628 _69627).
Proof. exact (TRANS (@lem5309940 x _69629 x' _69628 _69627) (@lem5309951 x _69629 x' _69628 _69627)). Qed.
Lemma lem5309955 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : l = (sup s).
Proof. exact (SYM (@lem5309882 b l s c h1)). Qed.
Lemma lem5309983 (_69630 : real) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term73 s c _69630.
Proof. exact (EQ_MP (@lem5309854 s c _69630) (@lem5309853 _69630 b l s c h1)). Qed.
Lemma lem5309984 (c : real) : (term541 c) = (term541 c).
Proof. exact (eq_refl (term541 c)). Qed.
Lemma lem5309985 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : (term542 c l) = (term543 c s).
Proof. exact (MK_COMB (@lem5309984 c) (@lem5309955 b l s c h1)). Qed.
Lemma lem5309986 (c : real) (s : real -> Prop) : (term543 c s) = (term46 c s).
Proof. exact (eq_refl (term543 c s)). Qed.
Lemma lem5309987 (c : real) (l : real) : (term544 c l) = (term544 c l).
Proof. exact (eq_refl (term544 c l)). Qed.
Lemma lem5309988 (l : real) (c : real) (s : real -> Prop) : ((term542 c l) = (term543 c s)) = ((term542 c l) = (term46 c s)).
Proof. exact (MK_COMB (@lem5309987 c l) (@lem5309986 c s)). Qed.
Lemma lem5309989 (c : real) (l : real) : (term542 c l) = (real_lt c l).
Proof. exact (eq_refl (term542 c l)). Qed.
Lemma lem5309990 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5309991 (c : real) (l : real) : (term544 c l) = (term545 c l).
Proof. exact (MK_COMB (@lem5309990) (@lem5309989 c l)). Qed.
Lemma lem5309992 (c : real) (s : real -> Prop) : (term46 c s) = (term46 c s).
Proof. exact (eq_refl (term46 c s)). Qed.
Lemma lem5309993 (l : real) (c : real) (s : real -> Prop) : ((term542 c l) = (term46 c s)) = ((real_lt c l) = (term46 c s)).
Proof. exact (MK_COMB (@lem5309991 c l) (@lem5309992 c s)). Qed.
Lemma lem5309994 (l : real) (c : real) (s : real -> Prop) : ((term542 c l) = (term543 c s)) = ((real_lt c l) = (term46 c s)).
Proof. exact (TRANS (@lem5309988 l c s) (@lem5309993 l c s)). Qed.
Lemma lem5309995 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : (real_lt c l) = (term46 c s).
Proof. exact (EQ_MP (@lem5309994 l c s) (@lem5309985 b l s c h1)). Qed.
Lemma lem5310024 (_69631 : real) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term62 s _69631 b.
Proof. exact (EQ_MP (@lem5309857 s _69631 b) (@lem5309856 _69631 b l s c h1)). Qed.
Lemma lem5310038 (_69629 : real) (_69627 : real -> Prop) (_69628 : real) (x : type1019) (x' : type1021) (h1 : term416 x x') : term528 x _69629 x' _69627 _69628.
Proof. exact (EQ_MP (@lem5309899 x _69629 x' _69627 _69628) (@lem5309862 _69629 _69627 _69628 x x' h1)). Qed.
Lemma lem5310052 (_69629 : real) (_69627 : real -> Prop) (_69628 : real) (x : type1019) (x' : type1021) (h1 : term416 x x') : term532 x _69629 x' _69627 _69628.
Proof. exact (EQ_MP (@lem5309917 x _69629 x' _69627 _69628) (@lem5309861 _69629 _69627 _69628 x x' h1)). Qed.
Lemma lem5310066 (_69629 : real) (_69628 : real) (_69627 : real -> Prop) (x : type1019) (x' : type1021) (h1 : term416 x x') : term536 x _69629 x' _69628 _69627.
Proof. exact (EQ_MP (@lem5309935 x _69629 x' _69628 _69627) (@lem5309864 _69629 _69628 _69627 x x' h1)). Qed.
Lemma lem5310080 (_69629 : real) (_69628 : real) (_69627 : real -> Prop) (x : type1019) (x' : type1021) (h1 : term416 x x') : term540 x _69629 x' _69628 _69627.
Proof. exact (EQ_MP (@lem5309953 x _69629 x' _69628 _69627) (@lem5309863 _69629 _69628 _69627 x x' h1)). Qed.
Lemma lem5310188 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term138 s.
Proof. exact (proj1 (@lem5309651 b l s c h1)). Qed.
Lemma lem5310189 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term546 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5310188 b l s c h1). Qed.
Lemma lem5310191 (p : Prop) : (term547 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5310192 (s : real -> Prop) : (term546 s) = (term138 s).
Proof. exact (@lem5310191 (s = (@EMPTY real))). Qed.
Lemma lem5310193 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term138 s.
Proof. exact (EQ_MP (@lem5310192 s) (@lem5310189 b l s c h1)). Qed.
Lemma lem5310195 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term138 s.
Proof. exact (proj1 (@lem5309651 b l s c h1)). Qed.
Lemma lem5310196 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term546 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5310195 b l s c h1). Qed.
Lemma lem5310198 (p : Prop) : (term547 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5310199 (s : real -> Prop) : (term546 s) = (term138 s).
Proof. exact (@lem5310198 (s = (@EMPTY real))). Qed.
Lemma lem5310200 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term138 s.
Proof. exact (EQ_MP (@lem5310199 s) (@lem5310196 b l s c h1)). Qed.
Lemma lem5310202 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term46 c s.
Proof. exact (EQ_MP (@lem5309995 b l s c h1) (@lem5309872 b l s c h1)). Qed.
Lemma lem5310203 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term548 c s.
Proof. exact (fun h0 : term206 c s => @lem5310202 b l s c h1). Qed.
Lemma lem5310205 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5310206 (c : real) (s : real -> Prop) : (term548 c s) = (term46 c s).
Proof. exact (@lem5310205 (term46 c s)). Qed.
Lemma lem5310207 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term46 c s.
Proof. exact (EQ_MP (@lem5310206 c s) (@lem5310203 b l s c h1)). Qed.
Lemma lem5310210 (x' : type1021) (c : real) (s : real -> Prop) (h1 : term550 x' c s) : term550 x' c s.
Proof. exact (h1). Qed.
Lemma lem5310211 (x' : type1021) (c : real) (s : real -> Prop) (h1 : term550 x' c s) : term551 x' c s.
Proof. exact (fun h0 : term499 x' c s => @lem5310210 x' c s h1). Qed.
Lemma lem5310213 (p : Prop) : (term547 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5310214 (x' : type1021) (c : real) (s : real -> Prop) : (term551 x' c s) = (term550 x' c s).
Proof. exact (@lem5310213 (term499 x' c s)). Qed.
Lemma lem5310215 (x' : type1021) (c : real) (s : real -> Prop) (h1 : term550 x' c s) : term550 x' c s.
Proof. exact (EQ_MP (@lem5310214 x' c s) (@lem5310211 x' c s h1)). Qed.
Lemma lem5310243 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5310244 (x' : type1021) (_69628 : real) (_69627 : real -> Prop) : (term552 x' _69628 _69627) = (term553 x' _69628 _69627).
Proof. exact (@lem5310243 (term499 x' _69628 _69627) (term206 _69628 _69627)). Qed.
Lemma lem5310250 (x : type1019) (_69628 : real) (_69629 : real) (_69627 : real -> Prop) : (term554 x _69628 _69629 _69627) = (term554 x _69628 _69629 _69627).
Proof. exact (eq_refl (term554 x _69628 _69629 _69627)). Qed.
Lemma lem5310251 (x : type1019) (_69629 : real) (x' : type1021) (_69628 : real) (_69627 : real -> Prop) : (term535 x _69629 x' _69628 _69627) = (term555 x _69629 x' _69628 _69627).
Proof. exact (MK_COMB (@lem5310250 x _69628 _69629 _69627) (@lem5310244 x' _69628 _69627)). Qed.
Lemma lem5310262 (_69627 : real -> Prop) : (term213 _69627) = (term213 _69627).
Proof. exact (eq_refl (term213 _69627)). Qed.
Lemma lem5310263 (x : type1019) (_69629 : real) (x' : type1021) (_69628 : real) (_69627 : real -> Prop) : (term536 x _69629 x' _69628 _69627) = (term556 x _69629 x' _69628 _69627).
Proof. exact (MK_COMB (@lem5310262 _69627) (@lem5310251 x _69629 x' _69628 _69627)). Qed.
Lemma lem5310274 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5310275 (x : type1019) (_69629 : real) (x' : type1021) (_69628 : real) (_69627 : real -> Prop) : (term557 x _69629 x' _69628 _69627) = (term558 x _69629 x' _69628 _69627).
Proof. exact (MK_COMB (@lem5310274) (@lem5310263 x _69629 x' _69628 _69627)). Qed.
Lemma lem5310279 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5310280 (x : type1019) (_69629 : real) (x' : type1021) (_69628 : real) (_69627 : real -> Prop) : (term559 x _69629 x' _69628 _69627) = (term536 x _69629 x' _69628 _69627).
Proof. exact (@lem5310279 (_69627 = (@EMPTY real)) (term490 x _69628 _69629 _69627) (term552 x' _69628 _69627)). Qed.
Lemma lem5310306 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5310307 (x' : type1021) (_69628 : real) (_69627 : real -> Prop) : (term552 x' _69628 _69627) = (term553 x' _69628 _69627).
Proof. exact (@lem5310306 (term499 x' _69628 _69627) (term206 _69628 _69627)). Qed.
Lemma lem5310313 (x : type1019) (_69628 : real) (_69629 : real) (_69627 : real -> Prop) : (term554 x _69628 _69629 _69627) = (term554 x _69628 _69629 _69627).
Proof. exact (eq_refl (term554 x _69628 _69629 _69627)). Qed.
Lemma lem5310314 (x : type1019) (_69629 : real) (x' : type1021) (_69628 : real) (_69627 : real -> Prop) : (term535 x _69629 x' _69628 _69627) = (term555 x _69629 x' _69628 _69627).
Proof. exact (MK_COMB (@lem5310313 x _69628 _69629 _69627) (@lem5310307 x' _69628 _69627)). Qed.
Lemma lem5310325 (_69627 : real -> Prop) : (term213 _69627) = (term213 _69627).
Proof. exact (eq_refl (term213 _69627)). Qed.
Lemma lem5310326 (x : type1019) (_69629 : real) (x' : type1021) (_69628 : real) (_69627 : real -> Prop) : (term536 x _69629 x' _69628 _69627) = (term556 x _69629 x' _69628 _69627).
Proof. exact (MK_COMB (@lem5310325 _69627) (@lem5310314 x _69629 x' _69628 _69627)). Qed.
Lemma lem5310337 (x : type1019) (_69629 : real) (x' : type1021) (_69628 : real) (_69627 : real -> Prop) : (term559 x _69629 x' _69628 _69627) = (term556 x _69629 x' _69628 _69627).
Proof. exact (TRANS (@lem5310280 x _69629 x' _69628 _69627) (@lem5310326 x _69629 x' _69628 _69627)). Qed.
Lemma lem5310338 (x : type1019) (_69629 : real) (x' : type1021) (_69628 : real) (_69627 : real -> Prop) : ((term536 x _69629 x' _69628 _69627) = (term559 x _69629 x' _69628 _69627)) = ((term556 x _69629 x' _69628 _69627) = (term556 x _69629 x' _69628 _69627)).
Proof. exact (MK_COMB (@lem5310275 x _69629 x' _69628 _69627) (@lem5310337 x _69629 x' _69628 _69627)). Qed.
Lemma lem5310340 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5310341 (x : Prop) : (x = x) = True.
Proof. exact (@lem5310340 Prop x). Qed.
Lemma lem5310342 (x : type1019) (_69629 : real) (x' : type1021) (_69628 : real) (_69627 : real -> Prop) : ((term556 x _69629 x' _69628 _69627) = (term556 x _69629 x' _69628 _69627)) = True.
Proof. exact (@lem5310341 (term556 x _69629 x' _69628 _69627)). Qed.
Lemma lem5310343 (x : type1019) (_69629 : real) (x' : type1021) (_69628 : real) (_69627 : real -> Prop) : ((term536 x _69629 x' _69628 _69627) = (term559 x _69629 x' _69628 _69627)) = True.
Proof. exact (TRANS (@lem5310338 x _69629 x' _69628 _69627) (@lem5310342 x _69629 x' _69628 _69627)). Qed.
Lemma lem5310344 (x : type1019) (_69629 : real) (x' : type1021) (_69628 : real) (_69627 : real -> Prop) : True = ((term536 x _69629 x' _69628 _69627) = (term559 x _69629 x' _69628 _69627)).
Proof. exact (SYM (@lem5310343 x _69629 x' _69628 _69627)). Qed.
Lemma lem5310345 (x : type1019) (_69629 : real) (x' : type1021) (_69628 : real) (_69627 : real -> Prop) : (term536 x _69629 x' _69628 _69627) = (term559 x _69629 x' _69628 _69627).
Proof. exact (EQ_MP (@lem5310344 x _69629 x' _69628 _69627) (@lem0)). Qed.
Lemma lem5310346 (_69629 : real) (_69628 : real) (_69627 : real -> Prop) (x : type1019) (x' : type1021) (h1 : term416 x x') : term559 x _69629 x' _69628 _69627.
Proof. exact (EQ_MP (@lem5310345 x _69629 x' _69628 _69627) (@lem5310066 _69629 _69628 _69627 x x' h1)). Qed.
Lemma lem5310348 (b : Prop) (a : Prop) : (a \/ b) = (term560 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5310349 (x' : type1021) (x : type1019) (_69628 : real) (_69629 : real) (_69627 : real -> Prop) : (term559 x _69629 x' _69628 _69627) = (term561 x' x _69628 _69629 _69627).
Proof. exact (@lem5310348 (term562 x' _69628 _69627) (term490 x _69628 _69629 _69627)). Qed.
Lemma lem5310351 (a : Prop) (b : Prop) : (term563 a b) = (term564 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5310352 (x' : type1021) (_69628 : real) (_69627 : real -> Prop) : (term565 x' _69628 _69627) = (term566 x' _69628 _69627).
Proof. exact (@lem5310351 (_69627 = (@EMPTY real)) (term552 x' _69628 _69627)). Qed.
Lemma lem5310354 (a : Prop) (b : Prop) : (term563 a b) = (term564 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5310355 (x' : type1021) (_69628 : real) (_69627 : real -> Prop) : (term567 x' _69628 _69627) = (term568 x' _69628 _69627).
Proof. exact (@lem5310354 (term206 _69628 _69627) (term499 x' _69628 _69627)). Qed.
Lemma lem5310357 (a : Prop) : (term569 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5310358 (_69628 : real) (_69627 : real -> Prop) : (term570 _69628 _69627) = (term46 _69628 _69627).
Proof. exact (@lem5310357 (term46 _69628 _69627)). Qed.
Lemma lem5310359 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5310360 (_69628 : real) (_69627 : real -> Prop) : (term571 _69628 _69627) = (term572 _69628 _69627).
Proof. exact (MK_COMB (@lem5310359) (@lem5310358 _69628 _69627)). Qed.
Lemma lem5310361 (x' : type1021) (_69628 : real) (_69627 : real -> Prop) : (term550 x' _69628 _69627) = (term550 x' _69628 _69627).
Proof. exact (eq_refl (term550 x' _69628 _69627)). Qed.
Lemma lem5310362 (x' : type1021) (_69628 : real) (_69627 : real -> Prop) : (term568 x' _69628 _69627) = (term573 x' _69628 _69627).
Proof. exact (MK_COMB (@lem5310360 _69628 _69627) (@lem5310361 x' _69628 _69627)). Qed.
Lemma lem5310363 (x' : type1021) (_69628 : real) (_69627 : real -> Prop) : (term567 x' _69628 _69627) = (term573 x' _69628 _69627).
Proof. exact (TRANS (@lem5310355 x' _69628 _69627) (@lem5310362 x' _69628 _69627)). Qed.
Lemma lem5310364 (_69627 : real -> Prop) : (term54 _69627) = (term54 _69627).
Proof. exact (eq_refl (term54 _69627)). Qed.
Lemma lem5310365 (x' : type1021) (_69628 : real) (_69627 : real -> Prop) : (term566 x' _69628 _69627) = (term574 x' _69628 _69627).
Proof. exact (MK_COMB (@lem5310364 _69627) (@lem5310363 x' _69628 _69627)). Qed.
Lemma lem5310366 (x' : type1021) (_69628 : real) (_69627 : real -> Prop) : (term565 x' _69628 _69627) = (term574 x' _69628 _69627).
Proof. exact (TRANS (@lem5310352 x' _69628 _69627) (@lem5310365 x' _69628 _69627)). Qed.
Lemma lem5310367 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5310368 (x' : type1021) (_69628 : real) (_69627 : real -> Prop) : (term575 x' _69628 _69627) = (term576 x' _69628 _69627).
Proof. exact (MK_COMB (@lem5310367) (@lem5310366 x' _69628 _69627)). Qed.
Lemma lem5310369 (x : type1019) (_69628 : real) (_69629 : real) (_69627 : real -> Prop) : (term490 x _69628 _69629 _69627) = (term490 x _69628 _69629 _69627).
Proof. exact (eq_refl (term490 x _69628 _69629 _69627)). Qed.
Lemma lem5310370 (x' : type1021) (x : type1019) (_69628 : real) (_69629 : real) (_69627 : real -> Prop) : (term561 x' x _69628 _69629 _69627) = (term577 x' x _69628 _69629 _69627).
Proof. exact (MK_COMB (@lem5310368 x' _69628 _69627) (@lem5310369 x _69628 _69629 _69627)). Qed.
Lemma lem5310371 (x' : type1021) (x : type1019) (_69628 : real) (_69629 : real) (_69627 : real -> Prop) : (term559 x _69629 x' _69628 _69627) = (term577 x' x _69628 _69629 _69627).
Proof. exact (TRANS (@lem5310349 x' x _69628 _69629 _69627) (@lem5310370 x' x _69628 _69629 _69627)). Qed.
Lemma lem5310373 (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term550 x' c s) (h2 : term179 b l s c) : term573 x' c s.
Proof. exact (conj (@lem5310207 b l s c h2) (@lem5310215 x' c s h1)). Qed.
Lemma lem5310374 (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term550 x' c s) (h2 : term179 b l s c) : term574 x' c s.
Proof. exact (conj (@lem5310200 b l s c h2) (@lem5310373 x' b l s c h1 h2)). Qed.
Lemma lem5310376 (_69628 : real) (_69629 : real) (_69627 : real -> Prop) (x : type1019) (x' : type1021) (h1 : term416 x x') : term577 x' x _69628 _69629 _69627.
Proof. exact (EQ_MP (@lem5310371 x' x _69628 _69629 _69627) (@lem5310346 _69629 _69628 _69627 x x' h1)). Qed.
Lemma lem5310377 (c : real) (_69629 : real) (s : real -> Prop) (x : type1019) (x' : type1021) (h1 : term416 x x') : term577 x' x c _69629 s.
Proof. exact (@lem5310376 c _69629 s x x' h1). Qed.
Lemma lem5310380 (_69629 : real) (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term550 x' c s) (h3 : term179 b l s c) : term490 x c _69629 s.
Proof. exact (@lem5310377 c _69629 s x x' h1 (@lem5310374 x' b l s c h2 h3)). Qed.
Lemma lem5310381 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term550 x' c s) (h3 : term179 b l s c) : term490 x c b s.
Proof. exact (@lem5310380 b x x' b l s c h1 h2 h3). Qed.
Lemma lem5310382 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term550 x' c s) (h3 : term179 b l s c) : term578 x c b s.
Proof. exact (fun h0 : term579 x c b s => @lem5310381 x x' b l s c h1 h2 h3). Qed.
Lemma lem5310384 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5310385 (x : type1019) (c : real) (b : real) (s : real -> Prop) : (term578 x c b s) = (term490 x c b s).
Proof. exact (@lem5310384 (term490 x c b s)). Qed.
Lemma lem5310386 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term550 x' c s) (h3 : term179 b l s c) : term490 x c b s.
Proof. exact (EQ_MP (@lem5310385 x c b s) (@lem5310382 x x' b l s c h1 h2 h3)). Qed.
Lemma lem5310392 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5310393 (b : real) (_69631 : real) (s : real -> Prop) : (term62 s _69631 b) = (term580 b _69631 s).
Proof. exact (@lem5310392 (real_le _69631 b) (term581 _69631 s)). Qed.
Lemma lem5310399 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5310400 (b : real) (_69631 : real) (s : real -> Prop) : (term582 s _69631 b) = (term583 b _69631 s).
Proof. exact (MK_COMB (@lem5310399) (@lem5310393 b _69631 s)). Qed.
Lemma lem5310406 (b : real) (_69631 : real) (s : real -> Prop) : (term580 b _69631 s) = (term580 b _69631 s).
Proof. exact (eq_refl (term580 b _69631 s)). Qed.
Lemma lem5310407 (b : real) (_69631 : real) (s : real -> Prop) : ((term62 s _69631 b) = (term580 b _69631 s)) = ((term580 b _69631 s) = (term580 b _69631 s)).
Proof. exact (MK_COMB (@lem5310400 b _69631 s) (@lem5310406 b _69631 s)). Qed.
Lemma lem5310409 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5310410 (x : Prop) : (x = x) = True.
Proof. exact (@lem5310409 Prop x). Qed.
Lemma lem5310411 (b : real) (_69631 : real) (s : real -> Prop) : ((term580 b _69631 s) = (term580 b _69631 s)) = True.
Proof. exact (@lem5310410 (term580 b _69631 s)). Qed.
Lemma lem5310412 (b : real) (_69631 : real) (s : real -> Prop) : ((term62 s _69631 b) = (term580 b _69631 s)) = True.
Proof. exact (TRANS (@lem5310407 b _69631 s) (@lem5310411 b _69631 s)). Qed.
Lemma lem5310413 (b : real) (_69631 : real) (s : real -> Prop) : True = ((term62 s _69631 b) = (term580 b _69631 s)).
Proof. exact (SYM (@lem5310412 b _69631 s)). Qed.
Lemma lem5310414 (b : real) (_69631 : real) (s : real -> Prop) : (term62 s _69631 b) = (term580 b _69631 s).
Proof. exact (EQ_MP (@lem5310413 b _69631 s) (@lem0)). Qed.
Lemma lem5310415 (_69631 : real) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term580 b _69631 s.
Proof. exact (EQ_MP (@lem5310414 b _69631 s) (@lem5310024 _69631 b l s c h1)). Qed.
Lemma lem5310417 (b : Prop) (a : Prop) : (a \/ b) = (term560 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5310418 (s : real -> Prop) (_69631 : real) (b : real) : (term580 b _69631 s) = (term584 s _69631 b).
Proof. exact (@lem5310417 (term581 _69631 s) (real_le _69631 b)). Qed.
Lemma lem5310420 (a : Prop) : (term569 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5310421 (_69631 : real) (s : real -> Prop) : (term585 _69631 s) = (@IN real _69631 s).
Proof. exact (@lem5310420 (@IN real _69631 s)). Qed.
Lemma lem5310422 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5310423 (_69631 : real) (s : real -> Prop) : (term586 _69631 s) = (term587 _69631 s).
Proof. exact (MK_COMB (@lem5310422) (@lem5310421 _69631 s)). Qed.
Lemma lem5310424 (_69631 : real) (b : real) : (real_le _69631 b) = (real_le _69631 b).
Proof. exact (eq_refl (real_le _69631 b)). Qed.
Lemma lem5310425 (s : real -> Prop) (_69631 : real) (b : real) : (term584 s _69631 b) = (term47 s _69631 b).
Proof. exact (MK_COMB (@lem5310423 _69631 s) (@lem5310424 _69631 b)). Qed.
Lemma lem5310426 (s : real -> Prop) (_69631 : real) (b : real) : (term580 b _69631 s) = (term47 s _69631 b).
Proof. exact (TRANS (@lem5310418 s _69631 b) (@lem5310425 s _69631 b)). Qed.
Lemma lem5310429 (_69631 : real) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term47 s _69631 b.
Proof. exact (EQ_MP (@lem5310426 s _69631 b) (@lem5310415 _69631 b l s c h1)). Qed.
Lemma lem5310430 (x : type1019) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term588 x s c b.
Proof. exact (@lem5310429 (x s c b) b l s c h1). Qed.
Lemma lem5310433 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term550 x' c s) (h3 : term179 b l s c) : term589 x s c b.
Proof. exact (@lem5310430 x b l s c h3 (@lem5310386 x x' b l s c h1 h2 h3)). Qed.
Lemma lem5310434 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term550 x' c s) (h3 : term179 b l s c) : term590 x s c b.
Proof. exact (fun h0 : term491 x s c b => @lem5310433 x x' b l s c h1 h2 h3). Qed.
Lemma lem5310436 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5310437 (x : type1019) (s : real -> Prop) (c : real) (b : real) : (term590 x s c b) = (term589 x s c b).
Proof. exact (@lem5310436 (term589 x s c b)). Qed.
Lemma lem5310438 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term550 x' c s) (h3 : term179 b l s c) : term589 x s c b.
Proof. exact (EQ_MP (@lem5310437 x s c b) (@lem5310434 x x' b l s c h1 h2 h3)). Qed.
Lemma lem5310440 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term46 c s.
Proof. exact (EQ_MP (@lem5309995 b l s c h1) (@lem5309872 b l s c h1)). Qed.
Lemma lem5310441 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term548 c s.
Proof. exact (fun h0 : term206 c s => @lem5310440 b l s c h1). Qed.
Lemma lem5310443 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5310444 (c : real) (s : real -> Prop) : (term548 c s) = (term46 c s).
Proof. exact (@lem5310443 (term46 c s)). Qed.
Lemma lem5310445 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term46 c s.
Proof. exact (EQ_MP (@lem5310444 c s) (@lem5310441 b l s c h1)). Qed.
Lemma lem5310473 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5310474 (x' : type1021) (_69628 : real) (_69627 : real -> Prop) : (term552 x' _69628 _69627) = (term553 x' _69628 _69627).
Proof. exact (@lem5310473 (term499 x' _69628 _69627) (term206 _69628 _69627)). Qed.
Lemma lem5310480 (x : type1019) (_69627 : real -> Prop) (_69628 : real) (_69629 : real) : (term591 x _69627 _69628 _69629) = (term591 x _69627 _69628 _69629).
Proof. exact (eq_refl (term591 x _69627 _69628 _69629)). Qed.
Lemma lem5310481 (x : type1019) (_69629 : real) (x' : type1021) (_69628 : real) (_69627 : real -> Prop) : (term539 x _69629 x' _69628 _69627) = (term592 x _69629 x' _69628 _69627).
Proof. exact (MK_COMB (@lem5310480 x _69627 _69628 _69629) (@lem5310474 x' _69628 _69627)). Qed.
Lemma lem5310485 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5310486 (x' : type1021) (x : type1019) (_69629 : real) (_69628 : real) (_69627 : real -> Prop) : (term592 x _69629 x' _69628 _69627) = (term593 x' x _69629 _69628 _69627).
Proof. exact (@lem5310485 (term499 x' _69628 _69627) (term491 x _69627 _69628 _69629) (term206 _69628 _69627)). Qed.
Lemma lem5310502 (x' : type1021) (x : type1019) (_69629 : real) (_69628 : real) (_69627 : real -> Prop) : (term539 x _69629 x' _69628 _69627) = (term593 x' x _69629 _69628 _69627).
Proof. exact (TRANS (@lem5310481 x _69629 x' _69628 _69627) (@lem5310486 x' x _69629 _69628 _69627)). Qed.
Lemma lem5310503 (_69627 : real -> Prop) : (term213 _69627) = (term213 _69627).
Proof. exact (eq_refl (term213 _69627)). Qed.
Lemma lem5310504 (x' : type1021) (x : type1019) (_69629 : real) (_69628 : real) (_69627 : real -> Prop) : (term540 x _69629 x' _69628 _69627) = (term594 x' x _69629 _69628 _69627).
Proof. exact (MK_COMB (@lem5310503 _69627) (@lem5310502 x' x _69629 _69628 _69627)). Qed.
Lemma lem5310515 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5310516 (x' : type1021) (x : type1019) (_69629 : real) (_69628 : real) (_69627 : real -> Prop) : (term595 x _69629 x' _69628 _69627) = (term596 x' x _69629 _69628 _69627).
Proof. exact (MK_COMB (@lem5310515) (@lem5310504 x' x _69629 _69628 _69627)). Qed.
Lemma lem5310520 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5310521 (x' : type1021) (x : type1019) (_69629 : real) (_69628 : real) (_69627 : real -> Prop) : (term597 x' x _69629 _69628 _69627) = (term594 x' x _69629 _69628 _69627).
Proof. exact (@lem5310520 (_69627 = (@EMPTY real)) (term499 x' _69628 _69627) (term495 x _69629 _69628 _69627)). Qed.
Lemma lem5310549 (x' : type1021) (x : type1019) (_69629 : real) (_69628 : real) (_69627 : real -> Prop) : ((term540 x _69629 x' _69628 _69627) = (term597 x' x _69629 _69628 _69627)) = ((term594 x' x _69629 _69628 _69627) = (term594 x' x _69629 _69628 _69627)).
Proof. exact (MK_COMB (@lem5310516 x' x _69629 _69628 _69627) (@lem5310521 x' x _69629 _69628 _69627)). Qed.
Lemma lem5310551 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5310552 (x : Prop) : (x = x) = True.
Proof. exact (@lem5310551 Prop x). Qed.
Lemma lem5310553 (x' : type1021) (x : type1019) (_69629 : real) (_69628 : real) (_69627 : real -> Prop) : ((term594 x' x _69629 _69628 _69627) = (term594 x' x _69629 _69628 _69627)) = True.
Proof. exact (@lem5310552 (term594 x' x _69629 _69628 _69627)). Qed.
Lemma lem5310554 (x' : type1021) (x : type1019) (_69629 : real) (_69628 : real) (_69627 : real -> Prop) : ((term540 x _69629 x' _69628 _69627) = (term597 x' x _69629 _69628 _69627)) = True.
Proof. exact (TRANS (@lem5310549 x' x _69629 _69628 _69627) (@lem5310553 x' x _69629 _69628 _69627)). Qed.
Lemma lem5310555 (x' : type1021) (x : type1019) (_69629 : real) (_69628 : real) (_69627 : real -> Prop) : True = ((term540 x _69629 x' _69628 _69627) = (term597 x' x _69629 _69628 _69627)).
Proof. exact (SYM (@lem5310554 x' x _69629 _69628 _69627)). Qed.
Lemma lem5310556 (x' : type1021) (x : type1019) (_69629 : real) (_69628 : real) (_69627 : real -> Prop) : (term540 x _69629 x' _69628 _69627) = (term597 x' x _69629 _69628 _69627).
Proof. exact (EQ_MP (@lem5310555 x' x _69629 _69628 _69627) (@lem0)). Qed.
Lemma lem5310557 (_69629 : real) (_69628 : real) (_69627 : real -> Prop) (x : type1019) (x' : type1021) (h1 : term416 x x') : term597 x' x _69629 _69628 _69627.
Proof. exact (EQ_MP (@lem5310556 x' x _69629 _69628 _69627) (@lem5310080 _69629 _69628 _69627 x x' h1)). Qed.
Lemma lem5310559 (b : Prop) (a : Prop) : (a \/ b) = (term560 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5310560 (x : type1019) (_69629 : real) (x' : type1021) (_69628 : real) (_69627 : real -> Prop) : (term597 x' x _69629 _69628 _69627) = (term598 x _69629 x' _69628 _69627).
Proof. exact (@lem5310559 (term504 x _69629 _69628 _69627) (term499 x' _69628 _69627)). Qed.
Lemma lem5310562 (a : Prop) (b : Prop) : (term563 a b) = (term564 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5310563 (x : type1019) (_69629 : real) (_69628 : real) (_69627 : real -> Prop) : (term599 x _69629 _69628 _69627) = (term600 x _69629 _69628 _69627).
Proof. exact (@lem5310562 (_69627 = (@EMPTY real)) (term495 x _69629 _69628 _69627)). Qed.
Lemma lem5310565 (a : Prop) (b : Prop) : (term563 a b) = (term564 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5310566 (x : type1019) (_69629 : real) (_69628 : real) (_69627 : real -> Prop) : (term601 x _69629 _69628 _69627) = (term602 x _69629 _69628 _69627).
Proof. exact (@lem5310565 (term491 x _69627 _69628 _69629) (term206 _69628 _69627)). Qed.
Lemma lem5310568 (a : Prop) : (term569 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5310569 (x : type1019) (_69627 : real -> Prop) (_69628 : real) (_69629 : real) : (term603 x _69627 _69628 _69629) = (term589 x _69627 _69628 _69629).
Proof. exact (@lem5310568 (term589 x _69627 _69628 _69629)). Qed.
Lemma lem5310570 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5310571 (x : type1019) (_69627 : real -> Prop) (_69628 : real) (_69629 : real) : (term604 x _69627 _69628 _69629) = (term605 x _69627 _69628 _69629).
Proof. exact (MK_COMB (@lem5310570) (@lem5310569 x _69627 _69628 _69629)). Qed.
Lemma lem5310573 (a : Prop) : (term569 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5310574 (_69628 : real) (_69627 : real -> Prop) : (term570 _69628 _69627) = (term46 _69628 _69627).
Proof. exact (@lem5310573 (term46 _69628 _69627)). Qed.
Lemma lem5310575 (x : type1019) (_69629 : real) (_69628 : real) (_69627 : real -> Prop) : (term602 x _69629 _69628 _69627) = (term606 x _69629 _69628 _69627).
Proof. exact (MK_COMB (@lem5310571 x _69627 _69628 _69629) (@lem5310574 _69628 _69627)). Qed.
Lemma lem5310576 (x : type1019) (_69629 : real) (_69628 : real) (_69627 : real -> Prop) : (term601 x _69629 _69628 _69627) = (term606 x _69629 _69628 _69627).
Proof. exact (TRANS (@lem5310566 x _69629 _69628 _69627) (@lem5310575 x _69629 _69628 _69627)). Qed.
Lemma lem5310577 (_69627 : real -> Prop) : (term54 _69627) = (term54 _69627).
Proof. exact (eq_refl (term54 _69627)). Qed.
Lemma lem5310578 (x : type1019) (_69629 : real) (_69628 : real) (_69627 : real -> Prop) : (term600 x _69629 _69628 _69627) = (term607 x _69629 _69628 _69627).
Proof. exact (MK_COMB (@lem5310577 _69627) (@lem5310576 x _69629 _69628 _69627)). Qed.
Lemma lem5310579 (x : type1019) (_69629 : real) (_69628 : real) (_69627 : real -> Prop) : (term599 x _69629 _69628 _69627) = (term607 x _69629 _69628 _69627).
Proof. exact (TRANS (@lem5310563 x _69629 _69628 _69627) (@lem5310578 x _69629 _69628 _69627)). Qed.
Lemma lem5310580 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5310581 (x : type1019) (_69629 : real) (_69628 : real) (_69627 : real -> Prop) : (term608 x _69629 _69628 _69627) = (term609 x _69629 _69628 _69627).
Proof. exact (MK_COMB (@lem5310580) (@lem5310579 x _69629 _69628 _69627)). Qed.
Lemma lem5310582 (x' : type1021) (_69628 : real) (_69627 : real -> Prop) : (term499 x' _69628 _69627) = (term499 x' _69628 _69627).
Proof. exact (eq_refl (term499 x' _69628 _69627)). Qed.
Lemma lem5310583 (x : type1019) (_69629 : real) (x' : type1021) (_69628 : real) (_69627 : real -> Prop) : (term598 x _69629 x' _69628 _69627) = (term610 x _69629 x' _69628 _69627).
Proof. exact (MK_COMB (@lem5310581 x _69629 _69628 _69627) (@lem5310582 x' _69628 _69627)). Qed.
Lemma lem5310584 (x : type1019) (_69629 : real) (x' : type1021) (_69628 : real) (_69627 : real -> Prop) : (term597 x' x _69629 _69628 _69627) = (term610 x _69629 x' _69628 _69627).
Proof. exact (TRANS (@lem5310560 x _69629 x' _69628 _69627) (@lem5310583 x _69629 x' _69628 _69627)). Qed.
Lemma lem5310586 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term550 x' c s) (h3 : term179 b l s c) : term606 x b c s.
Proof. exact (conj (@lem5310438 x x' b l s c h1 h2 h3) (@lem5310445 b l s c h3)). Qed.
Lemma lem5310587 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term550 x' c s) (h3 : term179 b l s c) : term607 x b c s.
Proof. exact (conj (@lem5310193 b l s c h3) (@lem5310586 x x' b l s c h1 h2 h3)). Qed.
Lemma lem5310589 (_69629 : real) (_69628 : real) (_69627 : real -> Prop) (x : type1019) (x' : type1021) (h1 : term416 x x') : term610 x _69629 x' _69628 _69627.
Proof. exact (EQ_MP (@lem5310584 x _69629 x' _69628 _69627) (@lem5310557 _69629 _69628 _69627 x x' h1)). Qed.
Lemma lem5310590 (b : real) (c : real) (s : real -> Prop) (x : type1019) (x' : type1021) (h1 : term416 x x') : term610 x b x' c s.
Proof. exact (@lem5310589 b c s x x' h1). Qed.
Lemma lem5310593 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term550 x' c s) (h3 : term179 b l s c) : term499 x' c s.
Proof. exact (@lem5310590 b c s x x' h1 (@lem5310587 x x' b l s c h1 h2 h3)). Qed.
Lemma lem5310594 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term179 b l s c) : term611 x' c s.
Proof. exact (fun h0 : term550 x' c s => @lem5310593 x x' b l s c h1 h0 h2). Qed.
Lemma lem5310596 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5310597 (x' : type1021) (c : real) (s : real -> Prop) : (term611 x' c s) = (term499 x' c s).
Proof. exact (@lem5310596 (term499 x' c s)). Qed.
Lemma lem5310598 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term179 b l s c) : term499 x' c s.
Proof. exact (EQ_MP (@lem5310597 x' c s) (@lem5310594 x x' b l s c h1 h2)). Qed.
Lemma lem5310600 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term138 s.
Proof. exact (proj1 (@lem5309651 b l s c h1)). Qed.
Lemma lem5310601 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term546 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5310600 b l s c h1). Qed.
Lemma lem5310603 (p : Prop) : (term547 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5310604 (s : real -> Prop) : (term546 s) = (term138 s).
Proof. exact (@lem5310603 (s = (@EMPTY real))). Qed.
Lemma lem5310605 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term138 s.
Proof. exact (EQ_MP (@lem5310604 s) (@lem5310601 b l s c h1)). Qed.
Lemma lem5310607 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term138 s.
Proof. exact (proj1 (@lem5309651 b l s c h1)). Qed.
Lemma lem5310608 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term546 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5310607 b l s c h1). Qed.
Lemma lem5310610 (p : Prop) : (term547 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5310611 (s : real -> Prop) : (term546 s) = (term138 s).
Proof. exact (@lem5310610 (s = (@EMPTY real))). Qed.
Lemma lem5310612 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term138 s.
Proof. exact (EQ_MP (@lem5310611 s) (@lem5310608 b l s c h1)). Qed.
Lemma lem5310614 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term46 c s.
Proof. exact (EQ_MP (@lem5309995 b l s c h1) (@lem5309872 b l s c h1)). Qed.
Lemma lem5310615 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term548 c s.
Proof. exact (fun h0 : term206 c s => @lem5310614 b l s c h1). Qed.
Lemma lem5310617 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5310618 (c : real) (s : real -> Prop) : (term548 c s) = (term46 c s).
Proof. exact (@lem5310617 (term46 c s)). Qed.
Lemma lem5310619 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term46 c s.
Proof. exact (EQ_MP (@lem5310618 c s) (@lem5310615 b l s c h1)). Qed.
Lemma lem5310622 (x' : type1021) (s : real -> Prop) (c : real) (h1 : term612 x' s c) : term612 x' s c.
Proof. exact (h1). Qed.
Lemma lem5310623 (x' : type1021) (s : real -> Prop) (c : real) (h1 : term612 x' s c) : term613 x' s c.
Proof. exact (fun h0 : term500 x' s c => @lem5310622 x' s c h1). Qed.
Lemma lem5310625 (p : Prop) : (term547 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5310626 (x' : type1021) (s : real -> Prop) (c : real) : (term613 x' s c) = (term612 x' s c).
Proof. exact (@lem5310625 (term500 x' s c)). Qed.
Lemma lem5310627 (x' : type1021) (s : real -> Prop) (c : real) (h1 : term612 x' s c) : term612 x' s c.
Proof. exact (EQ_MP (@lem5310626 x' s c) (@lem5310623 x' s c h1)). Qed.
Lemma lem5310655 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5310656 (x' : type1021) (_69628 : real) (_69627 : real -> Prop) : (term614 x' _69627 _69628) = (term615 x' _69628 _69627).
Proof. exact (@lem5310655 (term500 x' _69627 _69628) (term206 _69628 _69627)). Qed.
Lemma lem5310662 (x : type1019) (_69628 : real) (_69629 : real) (_69627 : real -> Prop) : (term554 x _69628 _69629 _69627) = (term554 x _69628 _69629 _69627).
Proof. exact (eq_refl (term554 x _69628 _69629 _69627)). Qed.
Lemma lem5310663 (x : type1019) (_69629 : real) (x' : type1021) (_69628 : real) (_69627 : real -> Prop) : (term527 x _69629 x' _69627 _69628) = (term616 x _69629 x' _69628 _69627).
Proof. exact (MK_COMB (@lem5310662 x _69628 _69629 _69627) (@lem5310656 x' _69628 _69627)). Qed.
Lemma lem5310674 (_69627 : real -> Prop) : (term213 _69627) = (term213 _69627).
Proof. exact (eq_refl (term213 _69627)). Qed.
Lemma lem5310675 (x : type1019) (_69629 : real) (x' : type1021) (_69628 : real) (_69627 : real -> Prop) : (term528 x _69629 x' _69627 _69628) = (term617 x _69629 x' _69628 _69627).
Proof. exact (MK_COMB (@lem5310674 _69627) (@lem5310663 x _69629 x' _69628 _69627)). Qed.
Lemma lem5310686 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5310687 (x : type1019) (_69629 : real) (x' : type1021) (_69628 : real) (_69627 : real -> Prop) : (term618 x _69629 x' _69627 _69628) = (term619 x _69629 x' _69628 _69627).
Proof. exact (MK_COMB (@lem5310686) (@lem5310675 x _69629 x' _69628 _69627)). Qed.
Lemma lem5310691 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5310692 (x : type1019) (_69629 : real) (x' : type1021) (_69627 : real -> Prop) (_69628 : real) : (term620 x _69629 x' _69627 _69628) = (term528 x _69629 x' _69627 _69628).
Proof. exact (@lem5310691 (_69627 = (@EMPTY real)) (term490 x _69628 _69629 _69627) (term614 x' _69627 _69628)). Qed.
Lemma lem5310718 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5310719 (x' : type1021) (_69628 : real) (_69627 : real -> Prop) : (term614 x' _69627 _69628) = (term615 x' _69628 _69627).
Proof. exact (@lem5310718 (term500 x' _69627 _69628) (term206 _69628 _69627)). Qed.
Lemma lem5310725 (x : type1019) (_69628 : real) (_69629 : real) (_69627 : real -> Prop) : (term554 x _69628 _69629 _69627) = (term554 x _69628 _69629 _69627).
Proof. exact (eq_refl (term554 x _69628 _69629 _69627)). Qed.
Lemma lem5310726 (x : type1019) (_69629 : real) (x' : type1021) (_69628 : real) (_69627 : real -> Prop) : (term527 x _69629 x' _69627 _69628) = (term616 x _69629 x' _69628 _69627).
Proof. exact (MK_COMB (@lem5310725 x _69628 _69629 _69627) (@lem5310719 x' _69628 _69627)). Qed.
Lemma lem5310737 (_69627 : real -> Prop) : (term213 _69627) = (term213 _69627).
Proof. exact (eq_refl (term213 _69627)). Qed.
Lemma lem5310738 (x : type1019) (_69629 : real) (x' : type1021) (_69628 : real) (_69627 : real -> Prop) : (term528 x _69629 x' _69627 _69628) = (term617 x _69629 x' _69628 _69627).
Proof. exact (MK_COMB (@lem5310737 _69627) (@lem5310726 x _69629 x' _69628 _69627)). Qed.
Lemma lem5310749 (x : type1019) (_69629 : real) (x' : type1021) (_69628 : real) (_69627 : real -> Prop) : (term620 x _69629 x' _69627 _69628) = (term617 x _69629 x' _69628 _69627).
Proof. exact (TRANS (@lem5310692 x _69629 x' _69627 _69628) (@lem5310738 x _69629 x' _69628 _69627)). Qed.
Lemma lem5310750 (x : type1019) (_69629 : real) (x' : type1021) (_69628 : real) (_69627 : real -> Prop) : ((term528 x _69629 x' _69627 _69628) = (term620 x _69629 x' _69627 _69628)) = ((term617 x _69629 x' _69628 _69627) = (term617 x _69629 x' _69628 _69627)).
Proof. exact (MK_COMB (@lem5310687 x _69629 x' _69628 _69627) (@lem5310749 x _69629 x' _69628 _69627)). Qed.
Lemma lem5310752 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5310753 (x : Prop) : (x = x) = True.
Proof. exact (@lem5310752 Prop x). Qed.
Lemma lem5310754 (x : type1019) (_69629 : real) (x' : type1021) (_69628 : real) (_69627 : real -> Prop) : ((term617 x _69629 x' _69628 _69627) = (term617 x _69629 x' _69628 _69627)) = True.
Proof. exact (@lem5310753 (term617 x _69629 x' _69628 _69627)). Qed.
Lemma lem5310755 (x : type1019) (_69629 : real) (x' : type1021) (_69627 : real -> Prop) (_69628 : real) : ((term528 x _69629 x' _69627 _69628) = (term620 x _69629 x' _69627 _69628)) = True.
Proof. exact (TRANS (@lem5310750 x _69629 x' _69628 _69627) (@lem5310754 x _69629 x' _69628 _69627)). Qed.
Lemma lem5310756 (x : type1019) (_69629 : real) (x' : type1021) (_69627 : real -> Prop) (_69628 : real) : True = ((term528 x _69629 x' _69627 _69628) = (term620 x _69629 x' _69627 _69628)).
Proof. exact (SYM (@lem5310755 x _69629 x' _69627 _69628)). Qed.
Lemma lem5310757 (x : type1019) (_69629 : real) (x' : type1021) (_69627 : real -> Prop) (_69628 : real) : (term528 x _69629 x' _69627 _69628) = (term620 x _69629 x' _69627 _69628).
Proof. exact (EQ_MP (@lem5310756 x _69629 x' _69627 _69628) (@lem0)). Qed.
Lemma lem5310758 (_69629 : real) (_69627 : real -> Prop) (_69628 : real) (x : type1019) (x' : type1021) (h1 : term416 x x') : term620 x _69629 x' _69627 _69628.
Proof. exact (EQ_MP (@lem5310757 x _69629 x' _69627 _69628) (@lem5310038 _69629 _69627 _69628 x x' h1)). Qed.
Lemma lem5310760 (b : Prop) (a : Prop) : (a \/ b) = (term560 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5310761 (x' : type1021) (x : type1019) (_69628 : real) (_69629 : real) (_69627 : real -> Prop) : (term620 x _69629 x' _69627 _69628) = (term621 x' x _69628 _69629 _69627).
Proof. exact (@lem5310760 (term622 x' _69627 _69628) (term490 x _69628 _69629 _69627)). Qed.
Lemma lem5310763 (a : Prop) (b : Prop) : (term563 a b) = (term564 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5310764 (x' : type1021) (_69627 : real -> Prop) (_69628 : real) : (term623 x' _69627 _69628) = (term624 x' _69627 _69628).
Proof. exact (@lem5310763 (_69627 = (@EMPTY real)) (term614 x' _69627 _69628)). Qed.
Lemma lem5310766 (a : Prop) (b : Prop) : (term563 a b) = (term564 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5310767 (x' : type1021) (_69627 : real -> Prop) (_69628 : real) : (term625 x' _69627 _69628) = (term626 x' _69627 _69628).
Proof. exact (@lem5310766 (term206 _69628 _69627) (term500 x' _69627 _69628)). Qed.
Lemma lem5310769 (a : Prop) : (term569 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5310770 (_69628 : real) (_69627 : real -> Prop) : (term570 _69628 _69627) = (term46 _69628 _69627).
Proof. exact (@lem5310769 (term46 _69628 _69627)). Qed.
Lemma lem5310771 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5310772 (_69628 : real) (_69627 : real -> Prop) : (term571 _69628 _69627) = (term572 _69628 _69627).
Proof. exact (MK_COMB (@lem5310771) (@lem5310770 _69628 _69627)). Qed.
Lemma lem5310773 (x' : type1021) (_69627 : real -> Prop) (_69628 : real) : (term612 x' _69627 _69628) = (term612 x' _69627 _69628).
Proof. exact (eq_refl (term612 x' _69627 _69628)). Qed.
Lemma lem5310774 (x' : type1021) (_69627 : real -> Prop) (_69628 : real) : (term626 x' _69627 _69628) = (term627 x' _69627 _69628).
Proof. exact (MK_COMB (@lem5310772 _69628 _69627) (@lem5310773 x' _69627 _69628)). Qed.
Lemma lem5310775 (x' : type1021) (_69627 : real -> Prop) (_69628 : real) : (term625 x' _69627 _69628) = (term627 x' _69627 _69628).
Proof. exact (TRANS (@lem5310767 x' _69627 _69628) (@lem5310774 x' _69627 _69628)). Qed.
Lemma lem5310776 (_69627 : real -> Prop) : (term54 _69627) = (term54 _69627).
Proof. exact (eq_refl (term54 _69627)). Qed.
Lemma lem5310777 (x' : type1021) (_69627 : real -> Prop) (_69628 : real) : (term624 x' _69627 _69628) = (term628 x' _69627 _69628).
Proof. exact (MK_COMB (@lem5310776 _69627) (@lem5310775 x' _69627 _69628)). Qed.
Lemma lem5310778 (x' : type1021) (_69627 : real -> Prop) (_69628 : real) : (term623 x' _69627 _69628) = (term628 x' _69627 _69628).
Proof. exact (TRANS (@lem5310764 x' _69627 _69628) (@lem5310777 x' _69627 _69628)). Qed.
Lemma lem5310779 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5310780 (x' : type1021) (_69627 : real -> Prop) (_69628 : real) : (term629 x' _69627 _69628) = (term630 x' _69627 _69628).
Proof. exact (MK_COMB (@lem5310779) (@lem5310778 x' _69627 _69628)). Qed.
Lemma lem5310781 (x : type1019) (_69628 : real) (_69629 : real) (_69627 : real -> Prop) : (term490 x _69628 _69629 _69627) = (term490 x _69628 _69629 _69627).
Proof. exact (eq_refl (term490 x _69628 _69629 _69627)). Qed.
Lemma lem5310782 (x' : type1021) (x : type1019) (_69628 : real) (_69629 : real) (_69627 : real -> Prop) : (term621 x' x _69628 _69629 _69627) = (term631 x' x _69628 _69629 _69627).
Proof. exact (MK_COMB (@lem5310780 x' _69627 _69628) (@lem5310781 x _69628 _69629 _69627)). Qed.
Lemma lem5310783 (x' : type1021) (x : type1019) (_69628 : real) (_69629 : real) (_69627 : real -> Prop) : (term620 x _69629 x' _69627 _69628) = (term631 x' x _69628 _69629 _69627).
Proof. exact (TRANS (@lem5310761 x' x _69628 _69629 _69627) (@lem5310782 x' x _69628 _69629 _69627)). Qed.
Lemma lem5310785 (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term612 x' s c) (h2 : term179 b l s c) : term627 x' s c.
Proof. exact (conj (@lem5310619 b l s c h2) (@lem5310627 x' s c h1)). Qed.
Lemma lem5310786 (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term612 x' s c) (h2 : term179 b l s c) : term628 x' s c.
Proof. exact (conj (@lem5310612 b l s c h2) (@lem5310785 x' b l s c h1 h2)). Qed.
Lemma lem5310788 (_69628 : real) (_69629 : real) (_69627 : real -> Prop) (x : type1019) (x' : type1021) (h1 : term416 x x') : term631 x' x _69628 _69629 _69627.
Proof. exact (EQ_MP (@lem5310783 x' x _69628 _69629 _69627) (@lem5310758 _69629 _69627 _69628 x x' h1)). Qed.
Lemma lem5310789 (c : real) (_69629 : real) (s : real -> Prop) (x : type1019) (x' : type1021) (h1 : term416 x x') : term631 x' x c _69629 s.
Proof. exact (@lem5310788 c _69629 s x x' h1). Qed.
Lemma lem5310792 (_69629 : real) (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term612 x' s c) (h3 : term179 b l s c) : term490 x c _69629 s.
Proof. exact (@lem5310789 c _69629 s x x' h1 (@lem5310786 x' b l s c h2 h3)). Qed.
Lemma lem5310793 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term612 x' s c) (h3 : term179 b l s c) : term490 x c b s.
Proof. exact (@lem5310792 b x x' b l s c h1 h2 h3). Qed.
Lemma lem5310794 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term612 x' s c) (h3 : term179 b l s c) : term578 x c b s.
Proof. exact (fun h0 : term579 x c b s => @lem5310793 x x' b l s c h1 h2 h3). Qed.
Lemma lem5310796 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5310797 (x : type1019) (c : real) (b : real) (s : real -> Prop) : (term578 x c b s) = (term490 x c b s).
Proof. exact (@lem5310796 (term490 x c b s)). Qed.
Lemma lem5310798 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term612 x' s c) (h3 : term179 b l s c) : term490 x c b s.
Proof. exact (EQ_MP (@lem5310797 x c b s) (@lem5310794 x x' b l s c h1 h2 h3)). Qed.
Lemma lem5310800 (_69631 : real) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term47 s _69631 b.
Proof. exact (EQ_MP (@lem5310426 s _69631 b) (@lem5310415 _69631 b l s c h1)). Qed.
Lemma lem5310801 (x : type1019) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term588 x s c b.
Proof. exact (@lem5310800 (x s c b) b l s c h1). Qed.
Lemma lem5310804 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term612 x' s c) (h3 : term179 b l s c) : term589 x s c b.
Proof. exact (@lem5310801 x b l s c h3 (@lem5310798 x x' b l s c h1 h2 h3)). Qed.
Lemma lem5310805 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term612 x' s c) (h3 : term179 b l s c) : term590 x s c b.
Proof. exact (fun h0 : term491 x s c b => @lem5310804 x x' b l s c h1 h2 h3). Qed.
Lemma lem5310807 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5310808 (x : type1019) (s : real -> Prop) (c : real) (b : real) : (term590 x s c b) = (term589 x s c b).
Proof. exact (@lem5310807 (term589 x s c b)). Qed.
Lemma lem5310809 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term612 x' s c) (h3 : term179 b l s c) : term589 x s c b.
Proof. exact (EQ_MP (@lem5310808 x s c b) (@lem5310805 x x' b l s c h1 h2 h3)). Qed.
Lemma lem5310811 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term46 c s.
Proof. exact (EQ_MP (@lem5309995 b l s c h1) (@lem5309872 b l s c h1)). Qed.
Lemma lem5310812 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term548 c s.
Proof. exact (fun h0 : term206 c s => @lem5310811 b l s c h1). Qed.
Lemma lem5310814 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5310815 (c : real) (s : real -> Prop) : (term548 c s) = (term46 c s).
Proof. exact (@lem5310814 (term46 c s)). Qed.
Lemma lem5310816 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term46 c s.
Proof. exact (EQ_MP (@lem5310815 c s) (@lem5310812 b l s c h1)). Qed.
Lemma lem5310844 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5310845 (x' : type1021) (_69628 : real) (_69627 : real -> Prop) : (term614 x' _69627 _69628) = (term615 x' _69628 _69627).
Proof. exact (@lem5310844 (term500 x' _69627 _69628) (term206 _69628 _69627)). Qed.
Lemma lem5310851 (x : type1019) (_69627 : real -> Prop) (_69628 : real) (_69629 : real) : (term591 x _69627 _69628 _69629) = (term591 x _69627 _69628 _69629).
Proof. exact (eq_refl (term591 x _69627 _69628 _69629)). Qed.
Lemma lem5310852 (x : type1019) (_69629 : real) (x' : type1021) (_69628 : real) (_69627 : real -> Prop) : (term531 x _69629 x' _69627 _69628) = (term632 x _69629 x' _69628 _69627).
Proof. exact (MK_COMB (@lem5310851 x _69627 _69628 _69629) (@lem5310845 x' _69628 _69627)). Qed.
Lemma lem5310856 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5310857 (x' : type1021) (x : type1019) (_69629 : real) (_69628 : real) (_69627 : real -> Prop) : (term632 x _69629 x' _69628 _69627) = (term633 x' x _69629 _69628 _69627).
Proof. exact (@lem5310856 (term500 x' _69627 _69628) (term491 x _69627 _69628 _69629) (term206 _69628 _69627)). Qed.
Lemma lem5310873 (x' : type1021) (x : type1019) (_69629 : real) (_69628 : real) (_69627 : real -> Prop) : (term531 x _69629 x' _69627 _69628) = (term633 x' x _69629 _69628 _69627).
Proof. exact (TRANS (@lem5310852 x _69629 x' _69628 _69627) (@lem5310857 x' x _69629 _69628 _69627)). Qed.
Lemma lem5310874 (_69627 : real -> Prop) : (term213 _69627) = (term213 _69627).
Proof. exact (eq_refl (term213 _69627)). Qed.
Lemma lem5310875 (x' : type1021) (x : type1019) (_69629 : real) (_69628 : real) (_69627 : real -> Prop) : (term532 x _69629 x' _69627 _69628) = (term634 x' x _69629 _69628 _69627).
Proof. exact (MK_COMB (@lem5310874 _69627) (@lem5310873 x' x _69629 _69628 _69627)). Qed.
Lemma lem5310886 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5310887 (x' : type1021) (x : type1019) (_69629 : real) (_69628 : real) (_69627 : real -> Prop) : (term635 x _69629 x' _69627 _69628) = (term636 x' x _69629 _69628 _69627).
Proof. exact (MK_COMB (@lem5310886) (@lem5310875 x' x _69629 _69628 _69627)). Qed.
Lemma lem5310891 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5310892 (x' : type1021) (x : type1019) (_69629 : real) (_69628 : real) (_69627 : real -> Prop) : (term637 x' x _69629 _69628 _69627) = (term634 x' x _69629 _69628 _69627).
Proof. exact (@lem5310891 (_69627 = (@EMPTY real)) (term500 x' _69627 _69628) (term495 x _69629 _69628 _69627)). Qed.
Lemma lem5310920 (x' : type1021) (x : type1019) (_69629 : real) (_69628 : real) (_69627 : real -> Prop) : ((term532 x _69629 x' _69627 _69628) = (term637 x' x _69629 _69628 _69627)) = ((term634 x' x _69629 _69628 _69627) = (term634 x' x _69629 _69628 _69627)).
Proof. exact (MK_COMB (@lem5310887 x' x _69629 _69628 _69627) (@lem5310892 x' x _69629 _69628 _69627)). Qed.
Lemma lem5310922 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5310923 (x : Prop) : (x = x) = True.
Proof. exact (@lem5310922 Prop x). Qed.
Lemma lem5310924 (x' : type1021) (x : type1019) (_69629 : real) (_69628 : real) (_69627 : real -> Prop) : ((term634 x' x _69629 _69628 _69627) = (term634 x' x _69629 _69628 _69627)) = True.
Proof. exact (@lem5310923 (term634 x' x _69629 _69628 _69627)). Qed.
Lemma lem5310925 (x' : type1021) (x : type1019) (_69629 : real) (_69628 : real) (_69627 : real -> Prop) : ((term532 x _69629 x' _69627 _69628) = (term637 x' x _69629 _69628 _69627)) = True.
Proof. exact (TRANS (@lem5310920 x' x _69629 _69628 _69627) (@lem5310924 x' x _69629 _69628 _69627)). Qed.
Lemma lem5310926 (x' : type1021) (x : type1019) (_69629 : real) (_69628 : real) (_69627 : real -> Prop) : True = ((term532 x _69629 x' _69627 _69628) = (term637 x' x _69629 _69628 _69627)).
Proof. exact (SYM (@lem5310925 x' x _69629 _69628 _69627)). Qed.
Lemma lem5310927 (x' : type1021) (x : type1019) (_69629 : real) (_69628 : real) (_69627 : real -> Prop) : (term532 x _69629 x' _69627 _69628) = (term637 x' x _69629 _69628 _69627).
Proof. exact (EQ_MP (@lem5310926 x' x _69629 _69628 _69627) (@lem0)). Qed.
Lemma lem5310928 (_69629 : real) (_69628 : real) (_69627 : real -> Prop) (x : type1019) (x' : type1021) (h1 : term416 x x') : term637 x' x _69629 _69628 _69627.
Proof. exact (EQ_MP (@lem5310927 x' x _69629 _69628 _69627) (@lem5310052 _69629 _69627 _69628 x x' h1)). Qed.
Lemma lem5310930 (b : Prop) (a : Prop) : (a \/ b) = (term560 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5310931 (x : type1019) (_69629 : real) (x' : type1021) (_69627 : real -> Prop) (_69628 : real) : (term637 x' x _69629 _69628 _69627) = (term638 x _69629 x' _69627 _69628).
Proof. exact (@lem5310930 (term504 x _69629 _69628 _69627) (term500 x' _69627 _69628)). Qed.
Lemma lem5310933 (a : Prop) (b : Prop) : (term563 a b) = (term564 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5310934 (x : type1019) (_69629 : real) (_69628 : real) (_69627 : real -> Prop) : (term599 x _69629 _69628 _69627) = (term600 x _69629 _69628 _69627).
Proof. exact (@lem5310933 (_69627 = (@EMPTY real)) (term495 x _69629 _69628 _69627)). Qed.
Lemma lem5310936 (a : Prop) (b : Prop) : (term563 a b) = (term564 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5310937 (x : type1019) (_69629 : real) (_69628 : real) (_69627 : real -> Prop) : (term601 x _69629 _69628 _69627) = (term602 x _69629 _69628 _69627).
Proof. exact (@lem5310936 (term491 x _69627 _69628 _69629) (term206 _69628 _69627)). Qed.
Lemma lem5310939 (a : Prop) : (term569 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5310940 (x : type1019) (_69627 : real -> Prop) (_69628 : real) (_69629 : real) : (term603 x _69627 _69628 _69629) = (term589 x _69627 _69628 _69629).
Proof. exact (@lem5310939 (term589 x _69627 _69628 _69629)). Qed.
Lemma lem5310941 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5310942 (x : type1019) (_69627 : real -> Prop) (_69628 : real) (_69629 : real) : (term604 x _69627 _69628 _69629) = (term605 x _69627 _69628 _69629).
Proof. exact (MK_COMB (@lem5310941) (@lem5310940 x _69627 _69628 _69629)). Qed.
Lemma lem5310944 (a : Prop) : (term569 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5310945 (_69628 : real) (_69627 : real -> Prop) : (term570 _69628 _69627) = (term46 _69628 _69627).
Proof. exact (@lem5310944 (term46 _69628 _69627)). Qed.
Lemma lem5310946 (x : type1019) (_69629 : real) (_69628 : real) (_69627 : real -> Prop) : (term602 x _69629 _69628 _69627) = (term606 x _69629 _69628 _69627).
Proof. exact (MK_COMB (@lem5310942 x _69627 _69628 _69629) (@lem5310945 _69628 _69627)). Qed.
Lemma lem5310947 (x : type1019) (_69629 : real) (_69628 : real) (_69627 : real -> Prop) : (term601 x _69629 _69628 _69627) = (term606 x _69629 _69628 _69627).
Proof. exact (TRANS (@lem5310937 x _69629 _69628 _69627) (@lem5310946 x _69629 _69628 _69627)). Qed.
Lemma lem5310948 (_69627 : real -> Prop) : (term54 _69627) = (term54 _69627).
Proof. exact (eq_refl (term54 _69627)). Qed.
Lemma lem5310949 (x : type1019) (_69629 : real) (_69628 : real) (_69627 : real -> Prop) : (term600 x _69629 _69628 _69627) = (term607 x _69629 _69628 _69627).
Proof. exact (MK_COMB (@lem5310948 _69627) (@lem5310947 x _69629 _69628 _69627)). Qed.
Lemma lem5310950 (x : type1019) (_69629 : real) (_69628 : real) (_69627 : real -> Prop) : (term599 x _69629 _69628 _69627) = (term607 x _69629 _69628 _69627).
Proof. exact (TRANS (@lem5310934 x _69629 _69628 _69627) (@lem5310949 x _69629 _69628 _69627)). Qed.
Lemma lem5310951 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5310952 (x : type1019) (_69629 : real) (_69628 : real) (_69627 : real -> Prop) : (term608 x _69629 _69628 _69627) = (term609 x _69629 _69628 _69627).
Proof. exact (MK_COMB (@lem5310951) (@lem5310950 x _69629 _69628 _69627)). Qed.
Lemma lem5310953 (x' : type1021) (_69627 : real -> Prop) (_69628 : real) : (term500 x' _69627 _69628) = (term500 x' _69627 _69628).
Proof. exact (eq_refl (term500 x' _69627 _69628)). Qed.
Lemma lem5310954 (x : type1019) (_69629 : real) (x' : type1021) (_69627 : real -> Prop) (_69628 : real) : (term638 x _69629 x' _69627 _69628) = (term639 x _69629 x' _69627 _69628).
Proof. exact (MK_COMB (@lem5310952 x _69629 _69628 _69627) (@lem5310953 x' _69627 _69628)). Qed.
Lemma lem5310955 (x : type1019) (_69629 : real) (x' : type1021) (_69627 : real -> Prop) (_69628 : real) : (term637 x' x _69629 _69628 _69627) = (term639 x _69629 x' _69627 _69628).
Proof. exact (TRANS (@lem5310931 x _69629 x' _69627 _69628) (@lem5310954 x _69629 x' _69627 _69628)). Qed.
Lemma lem5310957 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term612 x' s c) (h3 : term179 b l s c) : term606 x b c s.
Proof. exact (conj (@lem5310809 x x' b l s c h1 h2 h3) (@lem5310816 b l s c h3)). Qed.
Lemma lem5310958 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term612 x' s c) (h3 : term179 b l s c) : term607 x b c s.
Proof. exact (conj (@lem5310605 b l s c h3) (@lem5310957 x x' b l s c h1 h2 h3)). Qed.
Lemma lem5310960 (_69629 : real) (_69627 : real -> Prop) (_69628 : real) (x : type1019) (x' : type1021) (h1 : term416 x x') : term639 x _69629 x' _69627 _69628.
Proof. exact (EQ_MP (@lem5310955 x _69629 x' _69627 _69628) (@lem5310928 _69629 _69628 _69627 x x' h1)). Qed.
Lemma lem5310961 (b : real) (s : real -> Prop) (c : real) (x : type1019) (x' : type1021) (h1 : term416 x x') : term639 x b x' s c.
Proof. exact (@lem5310960 b s c x x' h1). Qed.
Lemma lem5310964 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term612 x' s c) (h3 : term179 b l s c) : term500 x' s c.
Proof. exact (@lem5310961 b s c x x' h1 (@lem5310958 x x' b l s c h1 h2 h3)). Qed.
Lemma lem5310965 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term179 b l s c) : term640 x' s c.
Proof. exact (fun h0 : term612 x' s c => @lem5310964 x x' b l s c h1 h0 h2). Qed.
Lemma lem5310967 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5310968 (x' : type1021) (s : real -> Prop) (c : real) : (term640 x' s c) = (term500 x' s c).
Proof. exact (@lem5310967 (term500 x' s c)). Qed.
Lemma lem5310969 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term179 b l s c) : term500 x' s c.
Proof. exact (EQ_MP (@lem5310968 x' s c) (@lem5310965 x x' b l s c h1 h2)). Qed.
Lemma lem5310971 (a : Prop) (b : Prop) : (term641 a b) = (term642 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem5310972 (s : real -> Prop) (c : real) (_69630 : real) : (term73 s c _69630) = (term72 s c _69630).
Proof. exact (@lem5310971 (@IN real _69630 s) (real_lt c _69630)). Qed.
Lemma lem5310974 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5310975 (s : real -> Prop) (c : real) (_69630 : real) : (term72 s c _69630) = (term643 s c _69630).
Proof. exact (@lem5310974 (term44 s c _69630)). Qed.
Lemma lem5310976 (s : real -> Prop) (c : real) (_69630 : real) : (term73 s c _69630) = (term643 s c _69630).
Proof. exact (TRANS (@lem5310972 s c _69630) (@lem5310975 s c _69630)). Qed.
Lemma lem5310978 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term179 b l s c) : term422 x' s c.
Proof. exact (conj (@lem5310598 x x' b l s c h1 h2) (@lem5310969 x x' b l s c h1 h2)). Qed.
Lemma lem5310980 (_69630 : real) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term643 s c _69630.
Proof. exact (EQ_MP (@lem5310976 s c _69630) (@lem5309983 _69630 b l s c h1)). Qed.
Lemma lem5310981 (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term644 x' s c.
Proof. exact (@lem5310980 (x' s c) b l s c h1). Qed.
Lemma lem5310984 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term179 b l s c) : False.
Proof. exact (@lem5310981 x' b l s c h2 (@lem5310978 x x' b l s c h1 h2)). Qed.
Lemma lem5310985 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term179 b l s c) : term645.
Proof. exact (fun h0 : ~ False => @lem5310984 x x' b l s c h1 h2). Qed.
Lemma lem5310987 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5310988 : term645 = False.
Proof. exact (@lem5310987 False). Qed.
Lemma lem5310990 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term179 b l s c) : False.
Proof. exact (EQ_MP (@lem5310988) (@lem5310985 x x' b l s c h1 h2)). Qed.
Lemma lem5310991 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term179 b l s c) : (term179 b l s c) = False.
Proof. exact (prop_ext (fun h3 : term179 b l s c => @lem5310990 x x' b l s c h1 h2) (fun h3 : False => @lem5309647 b l s c h2)). Qed.
Lemma lem5310992 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term179 b l s c) : False.
Proof. exact (EQ_MP (@lem5310991 x x' b l s c h1 h2) (@lem5309647 b l s c h2)). Qed.
Lemma lem5310993 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term179 b l s c) : (term416 x x') = False.
Proof. exact (prop_ext (fun h3 : term416 x x' => @lem5310992 x x' b l s c h1 h2) (fun h3 : False => @lem5309577 x x' h1)). Qed.
Lemma lem5310994 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term179 b l s c) : False.
Proof. exact (EQ_MP (@lem5310993 x x' b l s c h1 h2) (@lem5309577 x x' h1)). Qed.
Lemma lem5310995 (x : type1019) (x' : type1021) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term182 l s c) : False.
Proof. exact (ex_elim (@lem5309495 l s c h2) (fun b : real => fun h0 : term181 l s c b => @lem5310994 x x' b l s c h1 h0)). Qed.
Lemma lem5310996 (x : type1019) (x' : type1021) (l : real) (s : real -> Prop) (h1 : term416 x x') (h2 : term184 l s) : False.
Proof. exact (ex_elim (@lem5309494 l s h2) (fun c : real => fun h0 : term183 l s c => @lem5310995 x x' l s c h1 h0)). Qed.
Lemma lem5310997 (x : type1019) (x' : type1021) (s : real -> Prop) (h1 : term416 x x') (h2 : term186 s) : False.
Proof. exact (ex_elim (@lem5309493 s h2) (fun l : real => fun h0 : term185 s l => @lem5310996 x x' l s h1 h0)). Qed.
Lemma lem5310998 (x : type1019) (x' : type1021) (h1 : term416 x x') (h2 : term34) : False.
Proof. exact (ex_elim (@lem5309001 h2) (fun s : real -> Prop => fun h0 : term187 s => @lem5310997 x x' s h1 h0)). Qed.
Lemma lem5310999 (x : type1019) (h1 : term419 x) (h2 : term34) : False.
Proof. exact (ex_elim (@lem5309491 x h1) (fun x' : type1021 => fun h0 : term418 x x' => @lem5310998 x x' h0 h2)). Qed.
Lemma lem5311000 (h1 : term41) (h2 : term34) : False.
Proof. exact (ex_elim (@lem5309490 h1) (fun x : type1019 => fun h0 : term420 x => @lem5310999 x h0 h2)). Qed.
Lemma lem5311001 (h1 : term34) : term39.
Proof. exact (fun h0 : term41 => @lem5311000 h0 h1). Qed.
Lemma lem5311002 : term39 = term40.
Proof. exact (@lem69 term41). Qed.
Lemma lem5311003 (h1 : term34) : term40.
Proof. exact (EQ_MP (@lem5311002) (@lem5311001 h1)). Qed.
Lemma lem5311004 : term43.
Proof. exact (fun h0 : term34 => @lem5311003 h0). Qed.
Lemma lem5311005 : term35.
Proof. exact (EQ_MP (@lem5308648) (@lem5311004)). Qed.
Lemma lem5311007 : term35.
Proof. exact (@lem5308297 (@lem5311005)). Qed.
Lemma lem5311008 (h1 : term34) : term39.
Proof. exact (@lem5311007 (@lem5308282 h1)). Qed.
Lemma lem5311009 (h1 : term34) : False.
Proof. exact (@lem5311008 h1 (@lem5200089)). Qed.
Lemma lem5311010 (h1 : term34) : term34 = False.
Proof. exact (prop_ext (fun h2 : term34 => @lem5311009 h1) (fun h2 : False => @lem5308282 h1)). Qed.
Lemma lem5311011 (h1 : term34) : False.
Proof. exact (EQ_MP (@lem5311010 h1) (@lem5308282 h1)). Qed.
Lemma lem5311012 : term33.
Proof. exact (fun h0 : term34 => @lem5311011 h0). Qed.
Lemma lem5311013 : term31.
Proof. exact (EQ_MP (@lem5308281) (@lem5311012)). Qed.
Lemma lem5311014 : term30.
Proof. exact (EQ_MP (@lem5308277) (@lem5311013)). Qed.
