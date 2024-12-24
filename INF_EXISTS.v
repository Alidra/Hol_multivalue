Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INF_EXISTS_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import HAS_INF_INF_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
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
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm19018_spec.
Require Import thm19019_spec.
Require Import thm19024_spec.
Require Import thm19025_spec.
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
Require Import thm21386_spec.
Require Import thm69_spec.
Lemma lem5297178 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5297179 : term1 = term2.
Proof. exact (@lem5297178 term1). Qed.
Lemma lem5297180 : term2 = term1.
Proof. exact (SYM (@lem5297179)). Qed.
Lemma lem5297181 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem5297184 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem5297185 : term5.
Proof. exact (fun h0 : term4 => @lem5297184 h0). Qed.
Lemma lem5297186 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem5297187 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem5297188 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem5297186 h2 (@lem5297187 h1)). Qed.
Lemma lem5297189 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem5297188 h1 h0). Qed.
Lemma lem5297190 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem5297191 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem5297189 h1 (@lem5297190 h2)). Qed.
Lemma lem5297192 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem5297191 h0 h1). Qed.
Lemma lem5297193 : term7.
Proof. exact (fun h0 : term5 => @lem5297192 h0). Qed.
Lemma lem5297196 : term5.
Proof. exact (@lem5297193 (@lem5297185)). Qed.
Lemma lem5297220 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5297221 : term8 = term9.
Proof. exact (@lem5297220 term10). Qed.
Lemma lem5297244 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem5297251 : term4 = term12.
Proof. exact (MK_COMB (@lem5297244) (@lem5297221)). Qed.
Lemma lem5297252 (s : real -> Prop) (l : real) : ((inf s) = l) = ((inf s) = l).
Proof. exact (eq_refl ((inf s) = l)). Qed.
Lemma lem5297257 (s : real -> Prop) (b : real) (x : real) : (term13 s b x) = (term13 s b x).
Proof. exact (eq_refl (term13 s b x)). Qed.
Lemma lem5297258 (s : real -> Prop) (b : real) : (term14 s b) = (term14 s b).
Proof. exact (fun_ext (fun x : real => @lem5297257 s b x)). Qed.
Lemma lem5297259 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5297260 (s : real -> Prop) (b : real) : (term15 s b) = (term15 s b).
Proof. exact (MK_COMB (@lem5297259) (@lem5297258 s b)). Qed.
Lemma lem5297261 (s : real -> Prop) : (term16 s) = (term16 s).
Proof. exact (fun_ext (fun b : real => @lem5297260 s b)). Qed.
Lemma lem5297262 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5297263 (s : real -> Prop) : (term17 s) = (term17 s).
Proof. exact (MK_COMB (@lem5297262) (@lem5297261 s)). Qed.
Lemma lem5297264 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5297265 (s : real -> Prop) : (term18 s) = (term18 s).
Proof. exact (MK_COMB (@lem5297264) (@lem5297263 s)). Qed.
Lemma lem5297266 (s : real -> Prop) (l : real) : (term19 s l) = (term19 s l).
Proof. exact (MK_COMB (@lem5297265 s) (@lem5297252 s l)). Qed.
Lemma lem5297271 (s : real -> Prop) : (term20 s) = (term20 s).
Proof. exact (eq_refl (term20 s)). Qed.
Lemma lem5297272 (s : real -> Prop) (l : real) : (term21 s l) = (term21 s l).
Proof. exact (MK_COMB (@lem5297271 s) (@lem5297266 s l)). Qed.
Lemma lem5297275 (s : real -> Prop) (l : real) : (term22 s l) = (term22 s l).
Proof. exact (eq_refl (term22 s l)). Qed.
Lemma lem5297276 (s : real -> Prop) (l : real) : ((has_inf s l) = (term21 s l)) = ((has_inf s l) = (term21 s l)).
Proof. exact (MK_COMB (@lem5297275 s l) (@lem5297272 s l)). Qed.
Lemma lem5297277 (s : real -> Prop) : (term23 s) = (term23 s).
Proof. exact (fun_ext (fun l : real => @lem5297276 s l)). Qed.
Lemma lem5297278 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5297279 (s : real -> Prop) : (term24 s) = (term24 s).
Proof. exact (MK_COMB (@lem5297278) (@lem5297277 s)). Qed.
Lemma lem5297280 : term25 = term25.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5297279 s)). Qed.
Lemma lem5297281 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5297282 : term10 = term10.
Proof. exact (MK_COMB (@lem5297281) (@lem5297280)). Qed.
Lemma lem5297283 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5297284 : term9 = term9.
Proof. exact (MK_COMB (@lem5297283) (@lem5297282)). Qed.
Lemma lem5297289 (s : real -> Prop) (b : real) (x : real) : (term13 s b x) = (term13 s b x).
Proof. exact (eq_refl (term13 s b x)). Qed.
Lemma lem5297290 (s : real -> Prop) (b : real) : (term14 s b) = (term14 s b).
Proof. exact (fun_ext (fun x : real => @lem5297289 s b x)). Qed.
Lemma lem5297291 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5297292 (s : real -> Prop) (b : real) : (term15 s b) = (term15 s b).
Proof. exact (MK_COMB (@lem5297291) (@lem5297290 s b)). Qed.
Lemma lem5297293 (s : real -> Prop) : (term16 s) = (term16 s).
Proof. exact (fun_ext (fun b : real => @lem5297292 s b)). Qed.
Lemma lem5297294 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5297295 (s : real -> Prop) : (term17 s) = (term17 s).
Proof. exact (MK_COMB (@lem5297294) (@lem5297293 s)). Qed.
Lemma lem5297300 (s : real -> Prop) : (term20 s) = (term20 s).
Proof. exact (eq_refl (term20 s)). Qed.
Lemma lem5297301 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (MK_COMB (@lem5297300 s) (@lem5297295 s)). Qed.
Lemma lem5297302 (s : real -> Prop) (l : real) : (has_inf s l) = (has_inf s l).
Proof. exact (eq_refl (has_inf s l)). Qed.
Lemma lem5297303 (s : real -> Prop) : (term27 s) = (term27 s).
Proof. exact (fun_ext (fun l : real => @lem5297302 s l)). Qed.
Lemma lem5297304 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5297305 (s : real -> Prop) : (term28 s) = (term28 s).
Proof. exact (MK_COMB (@lem5297304) (@lem5297303 s)). Qed.
Lemma lem5297306 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5297307 (s : real -> Prop) : (term29 s) = (term29 s).
Proof. exact (MK_COMB (@lem5297306) (@lem5297305 s)). Qed.
Lemma lem5297308 (s : real -> Prop) : ((term28 s) = (term26 s)) = ((term28 s) = (term26 s)).
Proof. exact (MK_COMB (@lem5297307 s) (@lem5297301 s)). Qed.
Lemma lem5297309 : term30 = term30.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5297308 s)). Qed.
Lemma lem5297310 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5297311 : term1 = term1.
Proof. exact (MK_COMB (@lem5297310) (@lem5297309)). Qed.
Lemma lem5297312 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5297313 : term3 = term3.
Proof. exact (MK_COMB (@lem5297312) (@lem5297311)). Qed.
Lemma lem5297314 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5297315 : term11 = term11.
Proof. exact (MK_COMB (@lem5297314) (@lem5297313)). Qed.
Lemma lem5297316 : term12 = term12.
Proof. exact (MK_COMB (@lem5297315) (@lem5297284)). Qed.
Lemma lem5297379 : term4 = term12.
Proof. exact (TRANS (@lem5297251) (@lem5297316)). Qed.
Lemma lem5297380 : term12 = term4.
Proof. exact (SYM (@lem5297379)). Qed.
Lemma lem5297381 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem5297382 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem5297384 (s : real -> Prop) (l : real) : (has_inf s l) = (has_inf s l).
Proof. exact (eq_refl (has_inf s l)). Qed.
Lemma lem5297385 (P : real -> Prop) : (term31 P) = (term32 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5297386 (s : real -> Prop) : (term33 s) = (term34 s).
Proof. exact (@lem5297385 (term27 s)). Qed.
Lemma lem5297387 (s : real -> Prop) (l : real) : (term35 s l) = (has_inf s l).
Proof. exact (eq_refl (term35 s l)). Qed.
Lemma lem5297388 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5297390 (s : real -> Prop) (l : real) : (term36 s l) = (term37 s l).
Proof. exact (MK_COMB (@lem5297388) (@lem5297387 s l)). Qed.
Lemma lem5297391 (s : real -> Prop) : (term38 s) = (term39 s).
Proof. exact (fun_ext (fun l : real => @lem5297390 s l)). Qed.
Lemma lem5297392 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5297393 (s : real -> Prop) : (term34 s) = (term40 s).
Proof. exact (MK_COMB (@lem5297392) (@lem5297391 s)). Qed.
Lemma lem5297394 (s : real -> Prop) : (term33 s) = (term40 s).
Proof. exact (TRANS (@lem5297386 s) (@lem5297393 s)). Qed.
Lemma lem5297395 (s : real -> Prop) : (term27 s) = (term27 s).
Proof. exact (fun_ext (fun l : real => @lem5297384 s l)). Qed.
Lemma lem5297396 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5297397 (s : real -> Prop) : (term28 s) = (term28 s).
Proof. exact (MK_COMB (@lem5297396) (@lem5297395 s)). Qed.
Lemma lem5297401 (s : real -> Prop) : (term41 s) = (s = (@EMPTY real)).
Proof. exact (@lem16933 (s = (@EMPTY real))). Qed.
Lemma lem5297410 (s : real -> Prop) (b : real) (x : real) : (term42 s b x) = (term43 s b x).
Proof. exact (@lem17362 (@IN real x s) (real_le b x)). Qed.
Lemma lem5297415 (s : real -> Prop) (b : real) (x : real) : (term13 s b x) = (term44 s b x).
Proof. exact (@lem17265 (@IN real x s) (real_le b x)). Qed.
Lemma lem5297416 (P : real -> Prop) : (term45 P) = (term46 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5297417 (s : real -> Prop) (b : real) : (term47 s b) = (term48 s b).
Proof. exact (@lem5297416 (term14 s b)). Qed.
Lemma lem5297418 (s : real -> Prop) (b : real) (x : real) : (term49 s b x) = (term13 s b x).
Proof. exact (eq_refl (term49 s b x)). Qed.
Lemma lem5297419 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5297420 (s : real -> Prop) (b : real) (x : real) : (term50 s b x) = (term42 s b x).
Proof. exact (MK_COMB (@lem5297419) (@lem5297418 s b x)). Qed.
Lemma lem5297421 (s : real -> Prop) (b : real) (x : real) : (term50 s b x) = (term43 s b x).
Proof. exact (TRANS (@lem5297420 s b x) (@lem5297410 s b x)). Qed.
Lemma lem5297422 (s : real -> Prop) (b : real) : (term51 s b) = (term52 s b).
Proof. exact (fun_ext (fun x : real => @lem5297421 s b x)). Qed.
Lemma lem5297423 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5297424 (s : real -> Prop) (b : real) : (term48 s b) = (term53 s b).
Proof. exact (MK_COMB (@lem5297423) (@lem5297422 s b)). Qed.
Lemma lem5297425 (s : real -> Prop) (b : real) : (term47 s b) = (term53 s b).
Proof. exact (TRANS (@lem5297417 s b) (@lem5297424 s b)). Qed.
Lemma lem5297426 (s : real -> Prop) (b : real) : (term14 s b) = (term54 s b).
Proof. exact (fun_ext (fun x : real => @lem5297415 s b x)). Qed.
Lemma lem5297427 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5297428 (s : real -> Prop) (b : real) : (term15 s b) = (term55 s b).
Proof. exact (MK_COMB (@lem5297427) (@lem5297426 s b)). Qed.
Lemma lem5297429 (P : real -> Prop) : (term31 P) = (term32 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5297430 (s : real -> Prop) : (term56 s) = (term57 s).
Proof. exact (@lem5297429 (term16 s)). Qed.
Lemma lem5297431 (s : real -> Prop) (b : real) : (term58 s b) = (term15 s b).
Proof. exact (eq_refl (term58 s b)). Qed.
Lemma lem5297432 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5297433 (s : real -> Prop) (b : real) : (term59 s b) = (term47 s b).
Proof. exact (MK_COMB (@lem5297432) (@lem5297431 s b)). Qed.
Lemma lem5297434 (s : real -> Prop) (b : real) : (term59 s b) = (term53 s b).
Proof. exact (TRANS (@lem5297433 s b) (@lem5297425 s b)). Qed.
Lemma lem5297435 (s : real -> Prop) : (term60 s) = (term61 s).
Proof. exact (fun_ext (fun b : real => @lem5297434 s b)). Qed.
Lemma lem5297436 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5297437 (s : real -> Prop) : (term57 s) = (term62 s).
Proof. exact (MK_COMB (@lem5297436) (@lem5297435 s)). Qed.
Lemma lem5297438 (s : real -> Prop) : (term56 s) = (term62 s).
Proof. exact (TRANS (@lem5297430 s) (@lem5297437 s)). Qed.
Lemma lem5297439 (s : real -> Prop) : (term16 s) = (term63 s).
Proof. exact (fun_ext (fun b : real => @lem5297428 s b)). Qed.
Lemma lem5297440 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5297441 (s : real -> Prop) : (term17 s) = (term64 s).
Proof. exact (MK_COMB (@lem5297440) (@lem5297439 s)). Qed.
Lemma lem5297442 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5297443 (s : real -> Prop) : (term65 s) = (term66 s).
Proof. exact (MK_COMB (@lem5297442) (@lem5297401 s)). Qed.
Lemma lem5297444 (s : real -> Prop) : (term67 s) = (term68 s).
Proof. exact (MK_COMB (@lem5297443 s) (@lem5297438 s)). Qed.
Lemma lem5297445 (s : real -> Prop) : (term69 s) = (term67 s).
Proof. exact (@lem17045 (term70 s) (term17 s)). Qed.
Lemma lem5297446 (s : real -> Prop) : (term69 s) = (term68 s).
Proof. exact (TRANS (@lem5297445 s) (@lem5297444 s)). Qed.
Lemma lem5297448 (s : real -> Prop) : (term20 s) = (term20 s).
Proof. exact (eq_refl (term20 s)). Qed.
Lemma lem5297449 (s : real -> Prop) : (term26 s) = (term71 s).
Proof. exact (MK_COMB (@lem5297448 s) (@lem5297441 s)). Qed.
Lemma lem5297450 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5297451 (s : real -> Prop) : (term72 s) = (term73 s).
Proof. exact (MK_COMB (@lem5297450) (@lem5297394 s)). Qed.
Lemma lem5297452 (s : real -> Prop) : (term74 s) = (term75 s).
Proof. exact (MK_COMB (@lem5297451 s) (@lem5297449 s)). Qed.
Lemma lem5297453 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5297454 (s : real -> Prop) : (term76 s) = (term76 s).
Proof. exact (MK_COMB (@lem5297453) (@lem5297397 s)). Qed.
Lemma lem5297455 (s : real -> Prop) : (term77 s) = (term78 s).
Proof. exact (MK_COMB (@lem5297454 s) (@lem5297446 s)). Qed.
Lemma lem5297456 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5297457 (s : real -> Prop) : (term79 s) = (term80 s).
Proof. exact (MK_COMB (@lem5297456) (@lem5297455 s)). Qed.
Lemma lem5297458 (s : real -> Prop) : (term81 s) = (term82 s).
Proof. exact (MK_COMB (@lem5297457 s) (@lem5297452 s)). Qed.
Lemma lem5297459 (s : real -> Prop) : (term83 s) = (term81 s).
Proof. exact (@lem17646 (term28 s) (term26 s)). Qed.
Lemma lem5297460 (s : real -> Prop) : (term83 s) = (term82 s).
Proof. exact (TRANS (@lem5297459 s) (@lem5297458 s)). Qed.
Lemma lem5297461 (P : type1022) : (term84 P) = (term85 P).
Proof. exact (@lem18392 (real -> Prop) P). Qed.
Lemma lem5297462 : term3 = term86.
Proof. exact (@lem5297461 term30). Qed.
Lemma lem5297463 (s : real -> Prop) : (term87 s) = ((term28 s) = (term26 s)).
Proof. exact (eq_refl (term87 s)). Qed.
Lemma lem5297464 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5297465 (s : real -> Prop) : (term88 s) = (term83 s).
Proof. exact (MK_COMB (@lem5297464) (@lem5297463 s)). Qed.
Lemma lem5297466 (s : real -> Prop) : (term88 s) = (term82 s).
Proof. exact (TRANS (@lem5297465 s) (@lem5297460 s)). Qed.
Lemma lem5297467 : term89 = term90.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5297466 s)). Qed.
Lemma lem5297468 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5297469 : term86 = term91.
Proof. exact (MK_COMB (@lem5297468) (@lem5297467)). Qed.
Lemma lem5297470 : term3 = term91.
Proof. exact (TRANS (@lem5297462) (@lem5297469)). Qed.
Lemma lem5297472 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term92 A P Q) = (term93 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem5297473 (P : type1022) (Q : type1022) : (term94 P Q) = (term95 P Q).
Proof. exact (@lem5297472 (real -> Prop) P Q). Qed.
Lemma lem5297474 : term96 = term97.
Proof. exact (@lem5297473 term98 term99). Qed.
Lemma lem5297475 (s : real -> Prop) : (term100 s) = (term78 s).
Proof. exact (eq_refl (term100 s)). Qed.
Lemma lem5297476 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5297477 (s : real -> Prop) : (term101 s) = (term80 s).
Proof. exact (MK_COMB (@lem5297476) (@lem5297475 s)). Qed.
Lemma lem5297478 (s : real -> Prop) : (term102 s) = (term75 s).
Proof. exact (eq_refl (term102 s)). Qed.
Lemma lem5297479 (s : real -> Prop) : (term103 s) = (term82 s).
Proof. exact (MK_COMB (@lem5297477 s) (@lem5297478 s)). Qed.
Lemma lem5297480 : term104 = term90.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5297479 s)). Qed.
Lemma lem5297481 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5297482 : term96 = term91.
Proof. exact (MK_COMB (@lem5297481) (@lem5297480)). Qed.
Lemma lem5297483 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5297484 : term105 = term106.
Proof. exact (MK_COMB (@lem5297483) (@lem5297482)). Qed.
Lemma lem5297485 (s : real -> Prop) : (term100 s) = (term78 s).
Proof. exact (eq_refl (term100 s)). Qed.
Lemma lem5297486 : term107 = term98.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5297485 s)). Qed.
Lemma lem5297487 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5297488 : term108 = term109.
Proof. exact (MK_COMB (@lem5297487) (@lem5297486)). Qed.
Lemma lem5297489 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5297490 : term110 = term111.
Proof. exact (MK_COMB (@lem5297489) (@lem5297488)). Qed.
Lemma lem5297491 (s : real -> Prop) : (term102 s) = (term75 s).
Proof. exact (eq_refl (term102 s)). Qed.
Lemma lem5297492 : term112 = term99.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5297491 s)). Qed.
Lemma lem5297493 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5297494 : term113 = term114.
Proof. exact (MK_COMB (@lem5297493) (@lem5297492)). Qed.
Lemma lem5297495 : term97 = term115.
Proof. exact (MK_COMB (@lem5297490) (@lem5297494)). Qed.
Lemma lem5297496 : (term96 = term97) = (term91 = term115).
Proof. exact (MK_COMB (@lem5297484) (@lem5297495)). Qed.
Lemma lem5297497 : term91 = term115.
Proof. exact (EQ_MP (@lem5297496) (@lem5297474)). Qed.
Lemma lem5297707 {A B : Type'} (P : type1413 A B) : (term116 A B P) = (term117 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5297708 (P : type1626) : (term118 P) = (term119 P).
Proof. exact (@lem5297707 real real P). Qed.
Lemma lem5297709 (s : real -> Prop) : (term120 s) = (term121 s).
Proof. exact (@lem5297708 (term122 s)). Qed.
Lemma lem5297710 (s : real -> Prop) (b : real) : (term123 s b) = (term52 s b).
Proof. exact (eq_refl (term123 s b)). Qed.
Lemma lem5297711 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5297712 (s : real -> Prop) (b : real) (x : real) : (term124 s b x) = (term125 s b x).
Proof. exact (MK_COMB (@lem5297710 s b) (@lem5297711 x)). Qed.
Lemma lem5297713 (s : real -> Prop) (b : real) (x : real) : (term125 s b x) = (term43 s b x).
Proof. exact (eq_refl (term125 s b x)). Qed.
Lemma lem5297714 (s : real -> Prop) (b : real) (x : real) : (term124 s b x) = (term43 s b x).
Proof. exact (TRANS (@lem5297712 s b x) (@lem5297713 s b x)). Qed.
Lemma lem5297715 (s : real -> Prop) (b : real) : (term126 s b) = (term52 s b).
Proof. exact (fun_ext (fun x : real => @lem5297714 s b x)). Qed.
Lemma lem5297716 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5297717 (s : real -> Prop) (b : real) : (term127 s b) = (term53 s b).
Proof. exact (MK_COMB (@lem5297716) (@lem5297715 s b)). Qed.
Lemma lem5297718 (s : real -> Prop) : (term128 s) = (term61 s).
Proof. exact (fun_ext (fun b : real => @lem5297717 s b)). Qed.
Lemma lem5297719 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5297720 (s : real -> Prop) : (term120 s) = (term62 s).
Proof. exact (MK_COMB (@lem5297719) (@lem5297718 s)). Qed.
Lemma lem5297721 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5297722 (s : real -> Prop) : (term129 s) = (term130 s).
Proof. exact (MK_COMB (@lem5297721) (@lem5297720 s)). Qed.
Lemma lem5297723 (s : real -> Prop) (b : real) : (term123 s b) = (term52 s b).
Proof. exact (eq_refl (term123 s b)). Qed.
Lemma lem5297724 (x : real -> real) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem5297725 (s : real -> Prop) (x : real -> real) (b : real) : (term131 s x b) = (term132 s x b).
Proof. exact (MK_COMB (@lem5297723 s b) (@lem5297724 x b)). Qed.
Lemma lem5297726 (s : real -> Prop) (x : real -> real) (b : real) : (term132 s x b) = (term133 s x b).
Proof. exact (eq_refl (term132 s x b)). Qed.
Lemma lem5297727 (s : real -> Prop) (x : real -> real) (b : real) : (term131 s x b) = (term133 s x b).
Proof. exact (TRANS (@lem5297725 s x b) (@lem5297726 s x b)). Qed.
Lemma lem5297728 (s : real -> Prop) (x : real -> real) : (term134 s x) = (term135 s x).
Proof. exact (fun_ext (fun b : real => @lem5297727 s x b)). Qed.
Lemma lem5297729 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5297730 (s : real -> Prop) (x : real -> real) : (term136 s x) = (term137 s x).
Proof. exact (MK_COMB (@lem5297729) (@lem5297728 s x)). Qed.
Lemma lem5297731 (s : real -> Prop) : (term138 s) = (term139 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5297730 s x)). Qed.
Lemma lem5297732 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5297733 (s : real -> Prop) : (term121 s) = (term140 s).
Proof. exact (MK_COMB (@lem5297732) (@lem5297731 s)). Qed.
Lemma lem5297734 (s : real -> Prop) : ((term120 s) = (term121 s)) = ((term62 s) = (term140 s)).
Proof. exact (MK_COMB (@lem5297722 s) (@lem5297733 s)). Qed.
Lemma lem5297735 (s : real -> Prop) : (term62 s) = (term140 s).
Proof. exact (EQ_MP (@lem5297734 s) (@lem5297709 s)). Qed.
Lemma lem5297736 (s : real -> Prop) : (term66 s) = (term66 s).
Proof. exact (eq_refl (term66 s)). Qed.
Lemma lem5297737 (s : real -> Prop) : (term68 s) = (term141 s).
Proof. exact (MK_COMB (@lem5297736 s) (@lem5297735 s)). Qed.
Lemma lem5297739 {A : Type'} (P : Prop) (Q : A -> Prop) : (term142 A P Q) = (term143 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5297740 (P : Prop) (Q : type1028) : (term144 P Q) = (term145 P Q).
Proof. exact (@lem5297739 (real -> real) P Q). Qed.
Lemma lem5297741 (s : real -> Prop) : (term146 s) = (term147 s).
Proof. exact (@lem5297740 (s = (@EMPTY real)) (term139 s)). Qed.
Lemma lem5297742 (s : real -> Prop) (x : real -> real) : (term148 s x) = (term137 s x).
Proof. exact (eq_refl (term148 s x)). Qed.
Lemma lem5297743 (s : real -> Prop) : (term149 s) = (term139 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5297742 s x)). Qed.
Lemma lem5297744 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5297745 (s : real -> Prop) : (term150 s) = (term140 s).
Proof. exact (MK_COMB (@lem5297744) (@lem5297743 s)). Qed.
Lemma lem5297746 (s : real -> Prop) : (term66 s) = (term66 s).
Proof. exact (eq_refl (term66 s)). Qed.
Lemma lem5297747 (s : real -> Prop) : (term146 s) = (term141 s).
Proof. exact (MK_COMB (@lem5297746 s) (@lem5297745 s)). Qed.
Lemma lem5297748 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5297749 (s : real -> Prop) : (term151 s) = (term152 s).
Proof. exact (MK_COMB (@lem5297748) (@lem5297747 s)). Qed.
Lemma lem5297750 (s : real -> Prop) (x : real -> real) : (term148 s x) = (term137 s x).
Proof. exact (eq_refl (term148 s x)). Qed.
Lemma lem5297751 (s : real -> Prop) : (term66 s) = (term66 s).
Proof. exact (eq_refl (term66 s)). Qed.
Lemma lem5297752 (s : real -> Prop) (x : real -> real) : (term153 s x) = (term154 s x).
Proof. exact (MK_COMB (@lem5297751 s) (@lem5297750 s x)). Qed.
Lemma lem5297753 (s : real -> Prop) : (term155 s) = (term156 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5297752 s x)). Qed.
Lemma lem5297754 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5297755 (s : real -> Prop) : (term147 s) = (term157 s).
Proof. exact (MK_COMB (@lem5297754) (@lem5297753 s)). Qed.
Lemma lem5297756 (s : real -> Prop) : ((term146 s) = (term147 s)) = ((term141 s) = (term157 s)).
Proof. exact (MK_COMB (@lem5297749 s) (@lem5297755 s)). Qed.
Lemma lem5297757 (s : real -> Prop) : (term141 s) = (term157 s).
Proof. exact (EQ_MP (@lem5297756 s) (@lem5297741 s)). Qed.
Lemma lem5297758 (s : real -> Prop) : (term68 s) = (term157 s).
Proof. exact (TRANS (@lem5297737 s) (@lem5297757 s)). Qed.
Lemma lem5297759 (s : real -> Prop) : (term76 s) = (term76 s).
Proof. exact (eq_refl (term76 s)). Qed.
Lemma lem5297760 (s : real -> Prop) : (term78 s) = (term158 s).
Proof. exact (MK_COMB (@lem5297759 s) (@lem5297758 s)). Qed.
Lemma lem5297762 {A : Type'} (P : A -> Prop) (Q : Prop) : (term159 A P Q) = (term160 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5297763 (P : real -> Prop) (Q : Prop) : (term161 P Q) = (term162 P Q).
Proof. exact (@lem5297762 real P Q). Qed.
Lemma lem5297764 (s : real -> Prop) : (term163 s) = (term164 s).
Proof. exact (@lem5297763 (term27 s) (term157 s)). Qed.
Lemma lem5297765 (s : real -> Prop) (l : real) : (term35 s l) = (has_inf s l).
Proof. exact (eq_refl (term35 s l)). Qed.
Lemma lem5297766 (s : real -> Prop) : (term165 s) = (term27 s).
Proof. exact (fun_ext (fun l : real => @lem5297765 s l)). Qed.
Lemma lem5297767 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5297768 (s : real -> Prop) : (term166 s) = (term28 s).
Proof. exact (MK_COMB (@lem5297767) (@lem5297766 s)). Qed.
Lemma lem5297769 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5297770 (s : real -> Prop) : (term167 s) = (term76 s).
Proof. exact (MK_COMB (@lem5297769) (@lem5297768 s)). Qed.
Lemma lem5297771 (s : real -> Prop) : (term157 s) = (term157 s).
Proof. exact (eq_refl (term157 s)). Qed.
Lemma lem5297772 (s : real -> Prop) : (term163 s) = (term158 s).
Proof. exact (MK_COMB (@lem5297770 s) (@lem5297771 s)). Qed.
Lemma lem5297773 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5297774 (s : real -> Prop) : (term168 s) = (term169 s).
Proof. exact (MK_COMB (@lem5297773) (@lem5297772 s)). Qed.
Lemma lem5297775 (s : real -> Prop) (l : real) : (term35 s l) = (has_inf s l).
Proof. exact (eq_refl (term35 s l)). Qed.
Lemma lem5297776 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5297777 (s : real -> Prop) (l : real) : (term170 s l) = (term171 s l).
Proof. exact (MK_COMB (@lem5297776) (@lem5297775 s l)). Qed.
Lemma lem5297778 (s : real -> Prop) : (term157 s) = (term157 s).
Proof. exact (eq_refl (term157 s)). Qed.
Lemma lem5297779 (l : real) (s : real -> Prop) : (term172 l s) = (term173 l s).
Proof. exact (MK_COMB (@lem5297777 s l) (@lem5297778 s)). Qed.
Lemma lem5297780 (s : real -> Prop) : (term174 s) = (term175 s).
Proof. exact (fun_ext (fun l : real => @lem5297779 l s)). Qed.
Lemma lem5297781 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5297782 (s : real -> Prop) : (term164 s) = (term176 s).
Proof. exact (MK_COMB (@lem5297781) (@lem5297780 s)). Qed.
Lemma lem5297783 (s : real -> Prop) : ((term163 s) = (term164 s)) = ((term158 s) = (term176 s)).
Proof. exact (MK_COMB (@lem5297774 s) (@lem5297782 s)). Qed.
Lemma lem5297784 (s : real -> Prop) : (term158 s) = (term176 s).
Proof. exact (EQ_MP (@lem5297783 s) (@lem5297764 s)). Qed.
Lemma lem5297786 {A : Type'} (P : Prop) (Q : A -> Prop) : (term177 A P Q) = (term178 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5297787 (P : Prop) (Q : type1028) : (term179 P Q) = (term180 P Q).
Proof. exact (@lem5297786 (real -> real) P Q). Qed.
Lemma lem5297788 (l : real) (s : real -> Prop) : (term181 l s) = (term182 l s).
Proof. exact (@lem5297787 (has_inf s l) (term156 s)). Qed.
Lemma lem5297789 (s : real -> Prop) (x : real -> real) : (term183 s x) = (term154 s x).
Proof. exact (eq_refl (term183 s x)). Qed.
Lemma lem5297790 (s : real -> Prop) : (term184 s) = (term156 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5297789 s x)). Qed.
Lemma lem5297791 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5297792 (s : real -> Prop) : (term185 s) = (term157 s).
Proof. exact (MK_COMB (@lem5297791) (@lem5297790 s)). Qed.
Lemma lem5297793 (s : real -> Prop) (l : real) : (term171 s l) = (term171 s l).
Proof. exact (eq_refl (term171 s l)). Qed.
Lemma lem5297794 (l : real) (s : real -> Prop) : (term181 l s) = (term173 l s).
Proof. exact (MK_COMB (@lem5297793 s l) (@lem5297792 s)). Qed.
Lemma lem5297795 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5297796 (l : real) (s : real -> Prop) : (term186 l s) = (term187 l s).
Proof. exact (MK_COMB (@lem5297795) (@lem5297794 l s)). Qed.
Lemma lem5297797 (s : real -> Prop) (x : real -> real) : (term183 s x) = (term154 s x).
Proof. exact (eq_refl (term183 s x)). Qed.
Lemma lem5297798 (s : real -> Prop) (l : real) : (term171 s l) = (term171 s l).
Proof. exact (eq_refl (term171 s l)). Qed.
Lemma lem5297799 (l : real) (s : real -> Prop) (x : real -> real) : (term188 l s x) = (term189 l s x).
Proof. exact (MK_COMB (@lem5297798 s l) (@lem5297797 s x)). Qed.
Lemma lem5297800 (l : real) (s : real -> Prop) : (term190 l s) = (term191 l s).
Proof. exact (fun_ext (fun x : real -> real => @lem5297799 l s x)). Qed.
Lemma lem5297801 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5297802 (l : real) (s : real -> Prop) : (term182 l s) = (term192 l s).
Proof. exact (MK_COMB (@lem5297801) (@lem5297800 l s)). Qed.
Lemma lem5297803 (l : real) (s : real -> Prop) : ((term181 l s) = (term182 l s)) = ((term173 l s) = (term192 l s)).
Proof. exact (MK_COMB (@lem5297796 l s) (@lem5297802 l s)). Qed.
Lemma lem5297804 (l : real) (s : real -> Prop) : (term173 l s) = (term192 l s).
Proof. exact (EQ_MP (@lem5297803 l s) (@lem5297788 l s)). Qed.
Lemma lem5297805 (s : real -> Prop) : (term175 s) = (term193 s).
Proof. exact (fun_ext (fun l : real => @lem5297804 l s)). Qed.
Lemma lem5297806 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5297807 (s : real -> Prop) : (term176 s) = (term194 s).
Proof. exact (MK_COMB (@lem5297806) (@lem5297805 s)). Qed.
Lemma lem5297808 (s : real -> Prop) : (term158 s) = (term194 s).
Proof. exact (TRANS (@lem5297784 s) (@lem5297807 s)). Qed.
Lemma lem5297809 (s : real -> Prop) : (term78 s) = (term194 s).
Proof. exact (TRANS (@lem5297760 s) (@lem5297808 s)). Qed.
Lemma lem5297810 : term98 = term195.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5297809 s)). Qed.
Lemma lem5297811 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5297812 : term109 = term196.
Proof. exact (MK_COMB (@lem5297811) (@lem5297810)). Qed.
Lemma lem5297813 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5297814 : term111 = term197.
Proof. exact (MK_COMB (@lem5297813) (@lem5297812)). Qed.
Lemma lem5297816 {A : Type'} (P : Prop) (Q : A -> Prop) : (term177 A P Q) = (term178 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5297817 (P : Prop) (Q : real -> Prop) : (term198 P Q) = (term199 P Q).
Proof. exact (@lem5297816 real P Q). Qed.
Lemma lem5297818 (s : real -> Prop) : (term200 s) = (term201 s).
Proof. exact (@lem5297817 (term70 s) (term63 s)). Qed.
Lemma lem5297819 (s : real -> Prop) (b : real) : (term202 s b) = (term55 s b).
Proof. exact (eq_refl (term202 s b)). Qed.
Lemma lem5297820 (s : real -> Prop) : (term203 s) = (term63 s).
Proof. exact (fun_ext (fun b : real => @lem5297819 s b)). Qed.
Lemma lem5297821 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5297822 (s : real -> Prop) : (term204 s) = (term64 s).
Proof. exact (MK_COMB (@lem5297821) (@lem5297820 s)). Qed.
Lemma lem5297823 (s : real -> Prop) : (term20 s) = (term20 s).
Proof. exact (eq_refl (term20 s)). Qed.
Lemma lem5297824 (s : real -> Prop) : (term200 s) = (term71 s).
Proof. exact (MK_COMB (@lem5297823 s) (@lem5297822 s)). Qed.
Lemma lem5297825 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5297826 (s : real -> Prop) : (term205 s) = (term206 s).
Proof. exact (MK_COMB (@lem5297825) (@lem5297824 s)). Qed.
Lemma lem5297827 (s : real -> Prop) (b : real) : (term202 s b) = (term55 s b).
Proof. exact (eq_refl (term202 s b)). Qed.
Lemma lem5297828 (s : real -> Prop) : (term20 s) = (term20 s).
Proof. exact (eq_refl (term20 s)). Qed.
Lemma lem5297829 (s : real -> Prop) (b : real) : (term207 s b) = (term208 s b).
Proof. exact (MK_COMB (@lem5297828 s) (@lem5297827 s b)). Qed.
Lemma lem5297830 (s : real -> Prop) : (term209 s) = (term210 s).
Proof. exact (fun_ext (fun b : real => @lem5297829 s b)). Qed.
Lemma lem5297831 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5297832 (s : real -> Prop) : (term201 s) = (term211 s).
Proof. exact (MK_COMB (@lem5297831) (@lem5297830 s)). Qed.
Lemma lem5297833 (s : real -> Prop) : ((term200 s) = (term201 s)) = ((term71 s) = (term211 s)).
Proof. exact (MK_COMB (@lem5297826 s) (@lem5297832 s)). Qed.
Lemma lem5297834 (s : real -> Prop) : (term71 s) = (term211 s).
Proof. exact (EQ_MP (@lem5297833 s) (@lem5297818 s)). Qed.
Lemma lem5297835 (s : real -> Prop) : (term73 s) = (term73 s).
Proof. exact (eq_refl (term73 s)). Qed.
Lemma lem5297836 (s : real -> Prop) : (term75 s) = (term212 s).
Proof. exact (MK_COMB (@lem5297835 s) (@lem5297834 s)). Qed.
Lemma lem5297838 {A : Type'} (P : Prop) (Q : A -> Prop) : (term177 A P Q) = (term178 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5297839 (P : Prop) (Q : real -> Prop) : (term198 P Q) = (term199 P Q).
Proof. exact (@lem5297838 real P Q). Qed.
Lemma lem5297840 (s : real -> Prop) : (term213 s) = (term214 s).
Proof. exact (@lem5297839 (term40 s) (term210 s)). Qed.
Lemma lem5297841 (s : real -> Prop) (b : real) : (term215 s b) = (term208 s b).
Proof. exact (eq_refl (term215 s b)). Qed.
Lemma lem5297842 (s : real -> Prop) : (term216 s) = (term210 s).
Proof. exact (fun_ext (fun b : real => @lem5297841 s b)). Qed.
Lemma lem5297843 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5297844 (s : real -> Prop) : (term217 s) = (term211 s).
Proof. exact (MK_COMB (@lem5297843) (@lem5297842 s)). Qed.
Lemma lem5297845 (s : real -> Prop) : (term73 s) = (term73 s).
Proof. exact (eq_refl (term73 s)). Qed.
Lemma lem5297846 (s : real -> Prop) : (term213 s) = (term212 s).
Proof. exact (MK_COMB (@lem5297845 s) (@lem5297844 s)). Qed.
Lemma lem5297847 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5297848 (s : real -> Prop) : (term218 s) = (term219 s).
Proof. exact (MK_COMB (@lem5297847) (@lem5297846 s)). Qed.
Lemma lem5297849 (s : real -> Prop) (b : real) : (term215 s b) = (term208 s b).
Proof. exact (eq_refl (term215 s b)). Qed.
Lemma lem5297850 (s : real -> Prop) : (term73 s) = (term73 s).
Proof. exact (eq_refl (term73 s)). Qed.
Lemma lem5297851 (s : real -> Prop) (b : real) : (term220 s b) = (term221 s b).
Proof. exact (MK_COMB (@lem5297850 s) (@lem5297849 s b)). Qed.
Lemma lem5297852 (s : real -> Prop) : (term222 s) = (term223 s).
Proof. exact (fun_ext (fun b : real => @lem5297851 s b)). Qed.
Lemma lem5297853 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5297854 (s : real -> Prop) : (term214 s) = (term224 s).
Proof. exact (MK_COMB (@lem5297853) (@lem5297852 s)). Qed.
Lemma lem5297855 (s : real -> Prop) : ((term213 s) = (term214 s)) = ((term212 s) = (term224 s)).
Proof. exact (MK_COMB (@lem5297848 s) (@lem5297854 s)). Qed.
Lemma lem5297856 (s : real -> Prop) : (term212 s) = (term224 s).
Proof. exact (EQ_MP (@lem5297855 s) (@lem5297840 s)). Qed.
Lemma lem5297857 (s : real -> Prop) : (term75 s) = (term224 s).
Proof. exact (TRANS (@lem5297836 s) (@lem5297856 s)). Qed.
Lemma lem5297858 : term99 = term225.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5297857 s)). Qed.
Lemma lem5297859 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5297860 : term114 = term226.
Proof. exact (MK_COMB (@lem5297859) (@lem5297858)). Qed.
Lemma lem5297861 : term115 = term227.
Proof. exact (MK_COMB (@lem5297814) (@lem5297860)). Qed.
Lemma lem5297863 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term93 A P Q) = (term92 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5297864 (P : type1022) (Q : type1022) : (term95 P Q) = (term94 P Q).
Proof. exact (@lem5297863 (real -> Prop) P Q). Qed.
Lemma lem5297865 : term228 = term229.
Proof. exact (@lem5297864 term195 term225). Qed.
Lemma lem5297866 (s : real -> Prop) : (term230 s) = (term194 s).
Proof. exact (eq_refl (term230 s)). Qed.
Lemma lem5297867 : term231 = term195.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5297866 s)). Qed.
Lemma lem5297868 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5297869 : term232 = term196.
Proof. exact (MK_COMB (@lem5297868) (@lem5297867)). Qed.
Lemma lem5297870 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5297871 : term233 = term197.
Proof. exact (MK_COMB (@lem5297870) (@lem5297869)). Qed.
Lemma lem5297872 (s : real -> Prop) : (term234 s) = (term224 s).
Proof. exact (eq_refl (term234 s)). Qed.
Lemma lem5297873 : term235 = term225.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5297872 s)). Qed.
Lemma lem5297874 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5297875 : term236 = term226.
Proof. exact (MK_COMB (@lem5297874) (@lem5297873)). Qed.
Lemma lem5297876 : term228 = term227.
Proof. exact (MK_COMB (@lem5297871) (@lem5297875)). Qed.
Lemma lem5297877 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5297878 : term237 = term238.
Proof. exact (MK_COMB (@lem5297877) (@lem5297876)). Qed.
Lemma lem5297879 (s : real -> Prop) : (term230 s) = (term194 s).
Proof. exact (eq_refl (term230 s)). Qed.
Lemma lem5297880 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5297881 (s : real -> Prop) : (term239 s) = (term240 s).
Proof. exact (MK_COMB (@lem5297880) (@lem5297879 s)). Qed.
Lemma lem5297882 (s : real -> Prop) : (term234 s) = (term224 s).
Proof. exact (eq_refl (term234 s)). Qed.
Lemma lem5297883 (s : real -> Prop) : (term241 s) = (term242 s).
Proof. exact (MK_COMB (@lem5297881 s) (@lem5297882 s)). Qed.
Lemma lem5297884 : term243 = term244.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5297883 s)). Qed.
Lemma lem5297885 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5297886 : term229 = term245.
Proof. exact (MK_COMB (@lem5297885) (@lem5297884)). Qed.
Lemma lem5297887 : (term228 = term229) = (term227 = term245).
Proof. exact (MK_COMB (@lem5297878) (@lem5297886)). Qed.
Lemma lem5297888 : term227 = term245.
Proof. exact (EQ_MP (@lem5297887) (@lem5297865)). Qed.
Lemma lem5297890 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term93 A P Q) = (term92 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5297891 (P : real -> Prop) (Q : real -> Prop) : (term246 P Q) = (term247 P Q).
Proof. exact (@lem5297890 real P Q). Qed.
Lemma lem5297892 (s : real -> Prop) : (term248 s) = (term249 s).
Proof. exact (@lem5297891 (term193 s) (term223 s)). Qed.
Lemma lem5297893 (l : real) (s : real -> Prop) : (term250 s l) = (term192 l s).
Proof. exact (eq_refl (term250 s l)). Qed.
Lemma lem5297894 (s : real -> Prop) : (term251 s) = (term193 s).
Proof. exact (fun_ext (fun l : real => @lem5297893 l s)). Qed.
Lemma lem5297895 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5297896 (s : real -> Prop) : (term252 s) = (term194 s).
Proof. exact (MK_COMB (@lem5297895) (@lem5297894 s)). Qed.
Lemma lem5297897 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5297898 (s : real -> Prop) : (term253 s) = (term240 s).
Proof. exact (MK_COMB (@lem5297897) (@lem5297896 s)). Qed.
Lemma lem5297899 (s : real -> Prop) (l : real) : (term254 s l) = (term221 s l).
Proof. exact (eq_refl (term254 s l)). Qed.
Lemma lem5297900 (s : real -> Prop) : (term255 s) = (term223 s).
Proof. exact (fun_ext (fun l : real => @lem5297899 s l)). Qed.
Lemma lem5297901 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5297902 (s : real -> Prop) : (term256 s) = (term224 s).
Proof. exact (MK_COMB (@lem5297901) (@lem5297900 s)). Qed.
Lemma lem5297903 (s : real -> Prop) : (term248 s) = (term242 s).
Proof. exact (MK_COMB (@lem5297898 s) (@lem5297902 s)). Qed.
Lemma lem5297904 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5297905 (s : real -> Prop) : (term257 s) = (term258 s).
Proof. exact (MK_COMB (@lem5297904) (@lem5297903 s)). Qed.
Lemma lem5297906 (l : real) (s : real -> Prop) : (term250 s l) = (term192 l s).
Proof. exact (eq_refl (term250 s l)). Qed.
Lemma lem5297907 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5297908 (l : real) (s : real -> Prop) : (term259 s l) = (term260 l s).
Proof. exact (MK_COMB (@lem5297907) (@lem5297906 l s)). Qed.
Lemma lem5297909 (s : real -> Prop) (l : real) : (term254 s l) = (term221 s l).
Proof. exact (eq_refl (term254 s l)). Qed.
Lemma lem5297910 (s : real -> Prop) (l : real) : (term261 s l) = (term262 s l).
Proof. exact (MK_COMB (@lem5297908 l s) (@lem5297909 s l)). Qed.
Lemma lem5297911 (s : real -> Prop) : (term263 s) = (term264 s).
Proof. exact (fun_ext (fun l : real => @lem5297910 s l)). Qed.
Lemma lem5297912 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5297913 (s : real -> Prop) : (term249 s) = (term265 s).
Proof. exact (MK_COMB (@lem5297912) (@lem5297911 s)). Qed.
Lemma lem5297914 (s : real -> Prop) : ((term248 s) = (term249 s)) = ((term242 s) = (term265 s)).
Proof. exact (MK_COMB (@lem5297905 s) (@lem5297913 s)). Qed.
Lemma lem5297915 (s : real -> Prop) : (term242 s) = (term265 s).
Proof. exact (EQ_MP (@lem5297914 s) (@lem5297892 s)). Qed.
Lemma lem5297918 (s : real -> Prop) : (term266 s) = (term266 s).
Proof. exact (eq_refl (term266 s)). Qed.
Lemma lem5297919 (s : real -> Prop) : (term266 s) = ((term242 s) = (term265 s)).
Proof. exact (eq_refl (term266 s)). Qed.
Lemma lem5297920 (s : real -> Prop) : (term267 s) = (term267 s).
Proof. exact (eq_refl (term267 s)). Qed.
Lemma lem5297921 (s : real -> Prop) : ((term266 s) = (term266 s)) = ((term266 s) = ((term242 s) = (term265 s))).
Proof. exact (MK_COMB (@lem5297920 s) (@lem5297919 s)). Qed.
Lemma lem5297922 (s : real -> Prop) : (term266 s) = ((term242 s) = (term265 s)).
Proof. exact (eq_refl (term266 s)). Qed.
Lemma lem5297923 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5297924 (s : real -> Prop) : (term267 s) = (term268 s).
Proof. exact (MK_COMB (@lem5297923) (@lem5297922 s)). Qed.
Lemma lem5297925 (s : real -> Prop) : ((term242 s) = (term265 s)) = ((term242 s) = (term265 s)).
Proof. exact (eq_refl ((term242 s) = (term265 s))). Qed.
Lemma lem5297926 (s : real -> Prop) : ((term266 s) = ((term242 s) = (term265 s))) = (((term242 s) = (term265 s)) = ((term242 s) = (term265 s))).
Proof. exact (MK_COMB (@lem5297924 s) (@lem5297925 s)). Qed.
Lemma lem5297927 (s : real -> Prop) : ((term266 s) = (term266 s)) = (((term242 s) = (term265 s)) = ((term242 s) = (term265 s))).
Proof. exact (TRANS (@lem5297921 s) (@lem5297926 s)). Qed.
Lemma lem5297928 (s : real -> Prop) : ((term242 s) = (term265 s)) = ((term242 s) = (term265 s)).
Proof. exact (EQ_MP (@lem5297927 s) (@lem5297918 s)). Qed.
Lemma lem5297929 (s : real -> Prop) : (term242 s) = (term265 s).
Proof. exact (EQ_MP (@lem5297928 s) (@lem5297915 s)). Qed.
Lemma lem5297931 {A : Type'} (P : A -> Prop) (Q : Prop) : (term269 A P Q) = (term270 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5297932 (P : type1028) (Q : Prop) : (term271 P Q) = (term272 P Q).
Proof. exact (@lem5297931 (real -> real) P Q). Qed.
Lemma lem5297933 (s : real -> Prop) (l : real) : (term273 s l) = (term274 s l).
Proof. exact (@lem5297932 (term191 l s) (term221 s l)). Qed.
Lemma lem5297934 (l : real) (s : real -> Prop) (x : real -> real) : (term275 l s x) = (term189 l s x).
Proof. exact (eq_refl (term275 l s x)). Qed.
Lemma lem5297935 (l : real) (s : real -> Prop) : (term276 l s) = (term191 l s).
Proof. exact (fun_ext (fun x : real -> real => @lem5297934 l s x)). Qed.
Lemma lem5297936 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5297937 (l : real) (s : real -> Prop) : (term277 l s) = (term192 l s).
Proof. exact (MK_COMB (@lem5297936) (@lem5297935 l s)). Qed.
Lemma lem5297938 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5297939 (l : real) (s : real -> Prop) : (term278 l s) = (term260 l s).
Proof. exact (MK_COMB (@lem5297938) (@lem5297937 l s)). Qed.
Lemma lem5297940 (s : real -> Prop) (l : real) : (term221 s l) = (term221 s l).
Proof. exact (eq_refl (term221 s l)). Qed.
Lemma lem5297941 (s : real -> Prop) (l : real) : (term273 s l) = (term262 s l).
Proof. exact (MK_COMB (@lem5297939 l s) (@lem5297940 s l)). Qed.
Lemma lem5297942 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5297943 (s : real -> Prop) (l : real) : (term279 s l) = (term280 s l).
Proof. exact (MK_COMB (@lem5297942) (@lem5297941 s l)). Qed.
Lemma lem5297944 (l : real) (s : real -> Prop) (x : real -> real) : (term275 l s x) = (term189 l s x).
Proof. exact (eq_refl (term275 l s x)). Qed.
Lemma lem5297945 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5297946 (l : real) (s : real -> Prop) (x : real -> real) : (term281 l s x) = (term282 l s x).
Proof. exact (MK_COMB (@lem5297945) (@lem5297944 l s x)). Qed.
Lemma lem5297947 (s : real -> Prop) (l : real) : (term221 s l) = (term221 s l).
Proof. exact (eq_refl (term221 s l)). Qed.
Lemma lem5297948 (x : real -> real) (s : real -> Prop) (l : real) : (term283 x s l) = (term284 x s l).
Proof. exact (MK_COMB (@lem5297946 l s x) (@lem5297947 s l)). Qed.
Lemma lem5297949 (s : real -> Prop) (l : real) : (term285 s l) = (term286 s l).
Proof. exact (fun_ext (fun x : real -> real => @lem5297948 x s l)). Qed.
Lemma lem5297950 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5297951 (s : real -> Prop) (l : real) : (term274 s l) = (term287 s l).
Proof. exact (MK_COMB (@lem5297950) (@lem5297949 s l)). Qed.
Lemma lem5297952 (s : real -> Prop) (l : real) : ((term273 s l) = (term274 s l)) = ((term262 s l) = (term287 s l)).
Proof. exact (MK_COMB (@lem5297943 s l) (@lem5297951 s l)). Qed.
Lemma lem5297953 (s : real -> Prop) (l : real) : (term262 s l) = (term287 s l).
Proof. exact (EQ_MP (@lem5297952 s l) (@lem5297933 s l)). Qed.
Lemma lem5297954 (s : real -> Prop) : (term264 s) = (term288 s).
Proof. exact (fun_ext (fun l : real => @lem5297953 s l)). Qed.
Lemma lem5297955 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5297956 (s : real -> Prop) : (term265 s) = (term289 s).
Proof. exact (MK_COMB (@lem5297955) (@lem5297954 s)). Qed.
Lemma lem5297957 (s : real -> Prop) : (term242 s) = (term289 s).
Proof. exact (TRANS (@lem5297929 s) (@lem5297956 s)). Qed.
Lemma lem5297958 : term244 = term290.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5297957 s)). Qed.
Lemma lem5297959 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5297960 : term245 = term291.
Proof. exact (MK_COMB (@lem5297959) (@lem5297958)). Qed.
Lemma lem5297961 : term227 = term291.
Proof. exact (TRANS (@lem5297888) (@lem5297960)). Qed.
Lemma lem5297962 : term115 = term291.
Proof. exact (TRANS (@lem5297861) (@lem5297961)). Qed.
Lemma lem5297963 : term91 = term291.
Proof. exact (TRANS (@lem5297497) (@lem5297962)). Qed.
Lemma lem5297964 : term3 = term291.
Proof. exact (TRANS (@lem5297470) (@lem5297963)). Qed.
Lemma lem5297965 (h1 : term3) : term291.
Proof. exact (EQ_MP (@lem5297964) (@lem5297381 h1)). Qed.
Lemma lem5297971 (s : real -> Prop) : (term41 s) = (s = (@EMPTY real)).
Proof. exact (@lem16933 (s = (@EMPTY real))). Qed.
Lemma lem5297980 (s : real -> Prop) (b : real) (x : real) : (term42 s b x) = (term43 s b x).
Proof. exact (@lem17362 (@IN real x s) (real_le b x)). Qed.
Lemma lem5297985 (s : real -> Prop) (b : real) (x : real) : (term13 s b x) = (term44 s b x).
Proof. exact (@lem17265 (@IN real x s) (real_le b x)). Qed.
Lemma lem5297986 (P : real -> Prop) : (term45 P) = (term46 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5297987 (s : real -> Prop) (b : real) : (term47 s b) = (term48 s b).
Proof. exact (@lem5297986 (term14 s b)). Qed.
Lemma lem5297988 (s : real -> Prop) (b : real) (x : real) : (term49 s b x) = (term13 s b x).
Proof. exact (eq_refl (term49 s b x)). Qed.
Lemma lem5297989 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5297990 (s : real -> Prop) (b : real) (x : real) : (term50 s b x) = (term42 s b x).
Proof. exact (MK_COMB (@lem5297989) (@lem5297988 s b x)). Qed.
Lemma lem5297991 (s : real -> Prop) (b : real) (x : real) : (term50 s b x) = (term43 s b x).
Proof. exact (TRANS (@lem5297990 s b x) (@lem5297980 s b x)). Qed.
Lemma lem5297992 (s : real -> Prop) (b : real) : (term51 s b) = (term52 s b).
Proof. exact (fun_ext (fun x : real => @lem5297991 s b x)). Qed.
Lemma lem5297993 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5297994 (s : real -> Prop) (b : real) : (term48 s b) = (term53 s b).
Proof. exact (MK_COMB (@lem5297993) (@lem5297992 s b)). Qed.
Lemma lem5297995 (s : real -> Prop) (b : real) : (term47 s b) = (term53 s b).
Proof. exact (TRANS (@lem5297987 s b) (@lem5297994 s b)). Qed.
Lemma lem5297996 (s : real -> Prop) (b : real) : (term14 s b) = (term54 s b).
Proof. exact (fun_ext (fun x : real => @lem5297985 s b x)). Qed.
Lemma lem5297997 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5297998 (s : real -> Prop) (b : real) : (term15 s b) = (term55 s b).
Proof. exact (MK_COMB (@lem5297997) (@lem5297996 s b)). Qed.
Lemma lem5297999 (P : real -> Prop) : (term31 P) = (term32 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5298000 (s : real -> Prop) : (term56 s) = (term57 s).
Proof. exact (@lem5297999 (term16 s)). Qed.
Lemma lem5298001 (s : real -> Prop) (b : real) : (term58 s b) = (term15 s b).
Proof. exact (eq_refl (term58 s b)). Qed.
Lemma lem5298002 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5298003 (s : real -> Prop) (b : real) : (term59 s b) = (term47 s b).
Proof. exact (MK_COMB (@lem5298002) (@lem5298001 s b)). Qed.
Lemma lem5298004 (s : real -> Prop) (b : real) : (term59 s b) = (term53 s b).
Proof. exact (TRANS (@lem5298003 s b) (@lem5297995 s b)). Qed.
Lemma lem5298005 (s : real -> Prop) : (term60 s) = (term61 s).
Proof. exact (fun_ext (fun b : real => @lem5298004 s b)). Qed.
Lemma lem5298006 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5298007 (s : real -> Prop) : (term57 s) = (term62 s).
Proof. exact (MK_COMB (@lem5298006) (@lem5298005 s)). Qed.
Lemma lem5298008 (s : real -> Prop) : (term56 s) = (term62 s).
Proof. exact (TRANS (@lem5298000 s) (@lem5298007 s)). Qed.
Lemma lem5298009 (s : real -> Prop) : (term16 s) = (term63 s).
Proof. exact (fun_ext (fun b : real => @lem5297998 s b)). Qed.
Lemma lem5298010 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5298011 (s : real -> Prop) : (term17 s) = (term64 s).
Proof. exact (MK_COMB (@lem5298010) (@lem5298009 s)). Qed.
Lemma lem5298012 (s : real -> Prop) (l : real) : (term292 s l) = (term292 s l).
Proof. exact (eq_refl (term292 s l)). Qed.
Lemma lem5298013 (s : real -> Prop) (l : real) : ((inf s) = l) = ((inf s) = l).
Proof. exact (eq_refl ((inf s) = l)). Qed.
Lemma lem5298014 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5298015 (s : real -> Prop) : (term293 s) = (term294 s).
Proof. exact (MK_COMB (@lem5298014) (@lem5298008 s)). Qed.
Lemma lem5298016 (s : real -> Prop) (l : real) : (term295 s l) = (term296 s l).
Proof. exact (MK_COMB (@lem5298015 s) (@lem5298012 s l)). Qed.
Lemma lem5298017 (s : real -> Prop) (l : real) : (term297 s l) = (term295 s l).
Proof. exact (@lem17045 (term17 s) ((inf s) = l)). Qed.
Lemma lem5298018 (s : real -> Prop) (l : real) : (term297 s l) = (term296 s l).
Proof. exact (TRANS (@lem5298017 s l) (@lem5298016 s l)). Qed.
Lemma lem5298019 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5298020 (s : real -> Prop) : (term18 s) = (term298 s).
Proof. exact (MK_COMB (@lem5298019) (@lem5298011 s)). Qed.
Lemma lem5298021 (s : real -> Prop) (l : real) : (term19 s l) = (term299 s l).
Proof. exact (MK_COMB (@lem5298020 s) (@lem5298013 s l)). Qed.
Lemma lem5298022 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5298023 (s : real -> Prop) : (term65 s) = (term66 s).
Proof. exact (MK_COMB (@lem5298022) (@lem5297971 s)). Qed.
Lemma lem5298024 (s : real -> Prop) (l : real) : (term300 s l) = (term301 s l).
Proof. exact (MK_COMB (@lem5298023 s) (@lem5298018 s l)). Qed.
Lemma lem5298025 (s : real -> Prop) (l : real) : (term302 s l) = (term300 s l).
Proof. exact (@lem17045 (term70 s) (term19 s l)). Qed.
Lemma lem5298026 (s : real -> Prop) (l : real) : (term302 s l) = (term301 s l).
Proof. exact (TRANS (@lem5298025 s l) (@lem5298024 s l)). Qed.
Lemma lem5298028 (s : real -> Prop) : (term20 s) = (term20 s).
Proof. exact (eq_refl (term20 s)). Qed.
Lemma lem5298029 (s : real -> Prop) (l : real) : (term21 s l) = (term303 s l).
Proof. exact (MK_COMB (@lem5298028 s) (@lem5298021 s l)). Qed.
Lemma lem5298031 (s : real -> Prop) (l : real) : (term304 s l) = (term304 s l).
Proof. exact (eq_refl (term304 s l)). Qed.
Lemma lem5298032 (s : real -> Prop) (l : real) : (term305 s l) = (term306 s l).
Proof. exact (MK_COMB (@lem5298031 s l) (@lem5298029 s l)). Qed.
Lemma lem5298034 (s : real -> Prop) (l : real) : (term307 s l) = (term307 s l).
Proof. exact (eq_refl (term307 s l)). Qed.
Lemma lem5298035 (s : real -> Prop) (l : real) : (term308 s l) = (term309 s l).
Proof. exact (MK_COMB (@lem5298034 s l) (@lem5298026 s l)). Qed.
Lemma lem5298036 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5298037 (s : real -> Prop) (l : real) : (term310 s l) = (term311 s l).
Proof. exact (MK_COMB (@lem5298036) (@lem5298035 s l)). Qed.
Lemma lem5298038 (s : real -> Prop) (l : real) : (term312 s l) = (term313 s l).
Proof. exact (MK_COMB (@lem5298037 s l) (@lem5298032 s l)). Qed.
Lemma lem5298039 (s : real -> Prop) (l : real) : ((has_inf s l) = (term21 s l)) = (term312 s l).
Proof. exact (@lem17784 (has_inf s l) (term21 s l)). Qed.
Lemma lem5298040 (s : real -> Prop) (l : real) : ((has_inf s l) = (term21 s l)) = (term313 s l).
Proof. exact (TRANS (@lem5298039 s l) (@lem5298038 s l)). Qed.
Lemma lem5298041 (s : real -> Prop) : (term23 s) = (term314 s).
Proof. exact (fun_ext (fun l : real => @lem5298040 s l)). Qed.
Lemma lem5298042 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5298043 (s : real -> Prop) : (term24 s) = (term315 s).
Proof. exact (MK_COMB (@lem5298042) (@lem5298041 s)). Qed.
Lemma lem5298044 : term25 = term316.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5298043 s)). Qed.
Lemma lem5298045 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5298046 : term10 = term317.
Proof. exact (MK_COMB (@lem5298045) (@lem5298044)). Qed.
Lemma lem5298052 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term318 A P Q) = (term319 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5298053 (P : real -> Prop) (Q : real -> Prop) : (term320 P Q) = (term321 P Q).
Proof. exact (@lem5298052 real P Q). Qed.
Lemma lem5298054 (s : real -> Prop) : (term322 s) = (term323 s).
Proof. exact (@lem5298053 (term324 s) (term325 s)). Qed.
Lemma lem5298055 (s : real -> Prop) (l : real) : (term326 s l) = (term309 s l).
Proof. exact (eq_refl (term326 s l)). Qed.
Lemma lem5298056 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5298057 (s : real -> Prop) (l : real) : (term327 s l) = (term311 s l).
Proof. exact (MK_COMB (@lem5298056) (@lem5298055 s l)). Qed.
Lemma lem5298058 (s : real -> Prop) (l : real) : (term328 s l) = (term306 s l).
Proof. exact (eq_refl (term328 s l)). Qed.
Lemma lem5298059 (s : real -> Prop) (l : real) : (term329 s l) = (term313 s l).
Proof. exact (MK_COMB (@lem5298057 s l) (@lem5298058 s l)). Qed.
Lemma lem5298060 (s : real -> Prop) : (term330 s) = (term314 s).
Proof. exact (fun_ext (fun l : real => @lem5298059 s l)). Qed.
Lemma lem5298061 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5298062 (s : real -> Prop) : (term322 s) = (term315 s).
Proof. exact (MK_COMB (@lem5298061) (@lem5298060 s)). Qed.
Lemma lem5298063 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5298064 (s : real -> Prop) : (term331 s) = (term332 s).
Proof. exact (MK_COMB (@lem5298063) (@lem5298062 s)). Qed.
Lemma lem5298065 (s : real -> Prop) (l : real) : (term326 s l) = (term309 s l).
Proof. exact (eq_refl (term326 s l)). Qed.
Lemma lem5298066 (s : real -> Prop) : (term333 s) = (term324 s).
Proof. exact (fun_ext (fun l : real => @lem5298065 s l)). Qed.
Lemma lem5298067 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5298068 (s : real -> Prop) : (term334 s) = (term335 s).
Proof. exact (MK_COMB (@lem5298067) (@lem5298066 s)). Qed.
Lemma lem5298069 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5298070 (s : real -> Prop) : (term336 s) = (term337 s).
Proof. exact (MK_COMB (@lem5298069) (@lem5298068 s)). Qed.
Lemma lem5298071 (s : real -> Prop) (l : real) : (term328 s l) = (term306 s l).
Proof. exact (eq_refl (term328 s l)). Qed.
Lemma lem5298072 (s : real -> Prop) : (term338 s) = (term325 s).
Proof. exact (fun_ext (fun l : real => @lem5298071 s l)). Qed.
Lemma lem5298073 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5298074 (s : real -> Prop) : (term339 s) = (term340 s).
Proof. exact (MK_COMB (@lem5298073) (@lem5298072 s)). Qed.
Lemma lem5298075 (s : real -> Prop) : (term323 s) = (term341 s).
Proof. exact (MK_COMB (@lem5298070 s) (@lem5298074 s)). Qed.
Lemma lem5298076 (s : real -> Prop) : ((term322 s) = (term323 s)) = ((term315 s) = (term341 s)).
Proof. exact (MK_COMB (@lem5298064 s) (@lem5298075 s)). Qed.
Lemma lem5298077 (s : real -> Prop) : (term315 s) = (term341 s).
Proof. exact (EQ_MP (@lem5298076 s) (@lem5298054 s)). Qed.
Lemma lem5298278 : term316 = term342.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5298077 s)). Qed.
Lemma lem5298279 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5298280 : term317 = term343.
Proof. exact (MK_COMB (@lem5298279) (@lem5298278)). Qed.
Lemma lem5298282 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term318 A P Q) = (term319 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5298283 (P : type1022) (Q : type1022) : (term344 P Q) = (term345 P Q).
Proof. exact (@lem5298282 (real -> Prop) P Q). Qed.
Lemma lem5298284 : term346 = term347.
Proof. exact (@lem5298283 term348 term349). Qed.
Lemma lem5298285 (s : real -> Prop) : (term350 s) = (term335 s).
Proof. exact (eq_refl (term350 s)). Qed.
Lemma lem5298286 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5298287 (s : real -> Prop) : (term351 s) = (term337 s).
Proof. exact (MK_COMB (@lem5298286) (@lem5298285 s)). Qed.
Lemma lem5298288 (s : real -> Prop) : (term352 s) = (term340 s).
Proof. exact (eq_refl (term352 s)). Qed.
Lemma lem5298289 (s : real -> Prop) : (term353 s) = (term341 s).
Proof. exact (MK_COMB (@lem5298287 s) (@lem5298288 s)). Qed.
Lemma lem5298290 : term354 = term342.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5298289 s)). Qed.
Lemma lem5298291 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5298292 : term346 = term343.
Proof. exact (MK_COMB (@lem5298291) (@lem5298290)). Qed.
Lemma lem5298293 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5298294 : term355 = term356.
Proof. exact (MK_COMB (@lem5298293) (@lem5298292)). Qed.
Lemma lem5298295 (s : real -> Prop) : (term350 s) = (term335 s).
Proof. exact (eq_refl (term350 s)). Qed.
Lemma lem5298296 : term357 = term348.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5298295 s)). Qed.
Lemma lem5298297 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5298298 : term358 = term359.
Proof. exact (MK_COMB (@lem5298297) (@lem5298296)). Qed.
Lemma lem5298299 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5298300 : term360 = term361.
Proof. exact (MK_COMB (@lem5298299) (@lem5298298)). Qed.
Lemma lem5298301 (s : real -> Prop) : (term352 s) = (term340 s).
Proof. exact (eq_refl (term352 s)). Qed.
Lemma lem5298302 : term362 = term349.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5298301 s)). Qed.
Lemma lem5298303 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5298304 : term363 = term364.
Proof. exact (MK_COMB (@lem5298303) (@lem5298302)). Qed.
Lemma lem5298305 : term347 = term365.
Proof. exact (MK_COMB (@lem5298300) (@lem5298304)). Qed.
Lemma lem5298306 : (term346 = term347) = (term343 = term365).
Proof. exact (MK_COMB (@lem5298294) (@lem5298305)). Qed.
Lemma lem5298307 : term343 = term365.
Proof. exact (EQ_MP (@lem5298306) (@lem5298284)). Qed.
Lemma lem5298516 : term317 = term365.
Proof. exact (TRANS (@lem5298280) (@lem5298307)). Qed.
Lemma lem5298518 {A B : Type'} (P : type1413 A B) : (term116 A B P) = (term117 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5298519 (P : type1626) : (term118 P) = (term119 P).
Proof. exact (@lem5298518 real real P). Qed.
Lemma lem5298520 (s : real -> Prop) : (term120 s) = (term121 s).
Proof. exact (@lem5298519 (term122 s)). Qed.
Lemma lem5298521 (s : real -> Prop) (b : real) : (term123 s b) = (term52 s b).
Proof. exact (eq_refl (term123 s b)). Qed.
Lemma lem5298522 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5298523 (s : real -> Prop) (b : real) (x : real) : (term124 s b x) = (term125 s b x).
Proof. exact (MK_COMB (@lem5298521 s b) (@lem5298522 x)). Qed.
Lemma lem5298524 (s : real -> Prop) (b : real) (x : real) : (term125 s b x) = (term43 s b x).
Proof. exact (eq_refl (term125 s b x)). Qed.
Lemma lem5298525 (s : real -> Prop) (b : real) (x : real) : (term124 s b x) = (term43 s b x).
Proof. exact (TRANS (@lem5298523 s b x) (@lem5298524 s b x)). Qed.
Lemma lem5298526 (s : real -> Prop) (b : real) : (term126 s b) = (term52 s b).
Proof. exact (fun_ext (fun x : real => @lem5298525 s b x)). Qed.
Lemma lem5298527 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5298528 (s : real -> Prop) (b : real) : (term127 s b) = (term53 s b).
Proof. exact (MK_COMB (@lem5298527) (@lem5298526 s b)). Qed.
Lemma lem5298529 (s : real -> Prop) : (term128 s) = (term61 s).
Proof. exact (fun_ext (fun b : real => @lem5298528 s b)). Qed.
Lemma lem5298530 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5298531 (s : real -> Prop) : (term120 s) = (term62 s).
Proof. exact (MK_COMB (@lem5298530) (@lem5298529 s)). Qed.
Lemma lem5298532 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5298533 (s : real -> Prop) : (term129 s) = (term130 s).
Proof. exact (MK_COMB (@lem5298532) (@lem5298531 s)). Qed.
Lemma lem5298534 (s : real -> Prop) (b : real) : (term123 s b) = (term52 s b).
Proof. exact (eq_refl (term123 s b)). Qed.
Lemma lem5298535 (x : real -> real) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem5298536 (s : real -> Prop) (x : real -> real) (b : real) : (term131 s x b) = (term132 s x b).
Proof. exact (MK_COMB (@lem5298534 s b) (@lem5298535 x b)). Qed.
Lemma lem5298537 (s : real -> Prop) (x : real -> real) (b : real) : (term132 s x b) = (term133 s x b).
Proof. exact (eq_refl (term132 s x b)). Qed.
Lemma lem5298538 (s : real -> Prop) (x : real -> real) (b : real) : (term131 s x b) = (term133 s x b).
Proof. exact (TRANS (@lem5298536 s x b) (@lem5298537 s x b)). Qed.
Lemma lem5298539 (s : real -> Prop) (x : real -> real) : (term134 s x) = (term135 s x).
Proof. exact (fun_ext (fun b : real => @lem5298538 s x b)). Qed.
Lemma lem5298540 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5298541 (s : real -> Prop) (x : real -> real) : (term136 s x) = (term137 s x).
Proof. exact (MK_COMB (@lem5298540) (@lem5298539 s x)). Qed.
Lemma lem5298542 (s : real -> Prop) : (term138 s) = (term139 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5298541 s x)). Qed.
Lemma lem5298543 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5298544 (s : real -> Prop) : (term121 s) = (term140 s).
Proof. exact (MK_COMB (@lem5298543) (@lem5298542 s)). Qed.
Lemma lem5298545 (s : real -> Prop) : ((term120 s) = (term121 s)) = ((term62 s) = (term140 s)).
Proof. exact (MK_COMB (@lem5298533 s) (@lem5298544 s)). Qed.
Lemma lem5298546 (s : real -> Prop) : (term62 s) = (term140 s).
Proof. exact (EQ_MP (@lem5298545 s) (@lem5298520 s)). Qed.
Lemma lem5298547 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5298548 (s : real -> Prop) : (term294 s) = (term366 s).
Proof. exact (MK_COMB (@lem5298547) (@lem5298546 s)). Qed.
Lemma lem5298549 (s : real -> Prop) (l : real) : (term292 s l) = (term292 s l).
Proof. exact (eq_refl (term292 s l)). Qed.
Lemma lem5298550 (s : real -> Prop) (l : real) : (term296 s l) = (term367 s l).
Proof. exact (MK_COMB (@lem5298548 s) (@lem5298549 s l)). Qed.
Lemma lem5298552 {A : Type'} (P : A -> Prop) (Q : Prop) : (term269 A P Q) = (term270 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5298553 (P : type1028) (Q : Prop) : (term271 P Q) = (term272 P Q).
Proof. exact (@lem5298552 (real -> real) P Q). Qed.
Lemma lem5298554 (s : real -> Prop) (l : real) : (term368 s l) = (term369 s l).
Proof. exact (@lem5298553 (term139 s) (term292 s l)). Qed.
Lemma lem5298555 (s : real -> Prop) (x : real -> real) : (term148 s x) = (term137 s x).
Proof. exact (eq_refl (term148 s x)). Qed.
Lemma lem5298556 (s : real -> Prop) : (term149 s) = (term139 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5298555 s x)). Qed.
Lemma lem5298557 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5298558 (s : real -> Prop) : (term150 s) = (term140 s).
Proof. exact (MK_COMB (@lem5298557) (@lem5298556 s)). Qed.
Lemma lem5298559 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5298560 (s : real -> Prop) : (term370 s) = (term366 s).
Proof. exact (MK_COMB (@lem5298559) (@lem5298558 s)). Qed.
Lemma lem5298561 (s : real -> Prop) (l : real) : (term292 s l) = (term292 s l).
Proof. exact (eq_refl (term292 s l)). Qed.
Lemma lem5298562 (s : real -> Prop) (l : real) : (term368 s l) = (term367 s l).
Proof. exact (MK_COMB (@lem5298560 s) (@lem5298561 s l)). Qed.
Lemma lem5298563 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5298564 (s : real -> Prop) (l : real) : (term371 s l) = (term372 s l).
Proof. exact (MK_COMB (@lem5298563) (@lem5298562 s l)). Qed.
Lemma lem5298565 (s : real -> Prop) (x : real -> real) : (term148 s x) = (term137 s x).
Proof. exact (eq_refl (term148 s x)). Qed.
Lemma lem5298566 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5298567 (s : real -> Prop) (x : real -> real) : (term373 s x) = (term374 s x).
Proof. exact (MK_COMB (@lem5298566) (@lem5298565 s x)). Qed.
Lemma lem5298568 (s : real -> Prop) (l : real) : (term292 s l) = (term292 s l).
Proof. exact (eq_refl (term292 s l)). Qed.
Lemma lem5298569 (x : real -> real) (s : real -> Prop) (l : real) : (term375 x s l) = (term376 x s l).
Proof. exact (MK_COMB (@lem5298567 s x) (@lem5298568 s l)). Qed.
Lemma lem5298570 (s : real -> Prop) (l : real) : (term377 s l) = (term378 s l).
Proof. exact (fun_ext (fun x : real -> real => @lem5298569 x s l)). Qed.
Lemma lem5298571 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5298572 (s : real -> Prop) (l : real) : (term369 s l) = (term379 s l).
Proof. exact (MK_COMB (@lem5298571) (@lem5298570 s l)). Qed.
Lemma lem5298573 (s : real -> Prop) (l : real) : ((term368 s l) = (term369 s l)) = ((term367 s l) = (term379 s l)).
Proof. exact (MK_COMB (@lem5298564 s l) (@lem5298572 s l)). Qed.
Lemma lem5298574 (s : real -> Prop) (l : real) : (term367 s l) = (term379 s l).
Proof. exact (EQ_MP (@lem5298573 s l) (@lem5298554 s l)). Qed.
Lemma lem5298575 (s : real -> Prop) (l : real) : (term296 s l) = (term379 s l).
Proof. exact (TRANS (@lem5298550 s l) (@lem5298574 s l)). Qed.
Lemma lem5298576 (s : real -> Prop) : (term66 s) = (term66 s).
Proof. exact (eq_refl (term66 s)). Qed.
Lemma lem5298577 (s : real -> Prop) (l : real) : (term301 s l) = (term380 s l).
Proof. exact (MK_COMB (@lem5298576 s) (@lem5298575 s l)). Qed.
Lemma lem5298579 {A : Type'} (P : Prop) (Q : A -> Prop) : (term142 A P Q) = (term143 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5298580 (P : Prop) (Q : type1028) : (term144 P Q) = (term145 P Q).
Proof. exact (@lem5298579 (real -> real) P Q). Qed.
Lemma lem5298581 (s : real -> Prop) (l : real) : (term381 s l) = (term382 s l).
Proof. exact (@lem5298580 (s = (@EMPTY real)) (term378 s l)). Qed.
Lemma lem5298582 (x : real -> real) (s : real -> Prop) (l : real) : (term383 s l x) = (term376 x s l).
Proof. exact (eq_refl (term383 s l x)). Qed.
Lemma lem5298583 (s : real -> Prop) (l : real) : (term384 s l) = (term378 s l).
Proof. exact (fun_ext (fun x : real -> real => @lem5298582 x s l)). Qed.
Lemma lem5298584 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5298585 (s : real -> Prop) (l : real) : (term385 s l) = (term379 s l).
Proof. exact (MK_COMB (@lem5298584) (@lem5298583 s l)). Qed.
Lemma lem5298586 (s : real -> Prop) : (term66 s) = (term66 s).
Proof. exact (eq_refl (term66 s)). Qed.
Lemma lem5298587 (s : real -> Prop) (l : real) : (term381 s l) = (term380 s l).
Proof. exact (MK_COMB (@lem5298586 s) (@lem5298585 s l)). Qed.
Lemma lem5298588 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5298589 (s : real -> Prop) (l : real) : (term386 s l) = (term387 s l).
Proof. exact (MK_COMB (@lem5298588) (@lem5298587 s l)). Qed.
Lemma lem5298590 (x : real -> real) (s : real -> Prop) (l : real) : (term383 s l x) = (term376 x s l).
Proof. exact (eq_refl (term383 s l x)). Qed.
Lemma lem5298591 (s : real -> Prop) : (term66 s) = (term66 s).
Proof. exact (eq_refl (term66 s)). Qed.
Lemma lem5298592 (x : real -> real) (s : real -> Prop) (l : real) : (term388 s l x) = (term389 x s l).
Proof. exact (MK_COMB (@lem5298591 s) (@lem5298590 x s l)). Qed.
Lemma lem5298593 (s : real -> Prop) (l : real) : (term390 s l) = (term391 s l).
Proof. exact (fun_ext (fun x : real -> real => @lem5298592 x s l)). Qed.
Lemma lem5298594 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5298595 (s : real -> Prop) (l : real) : (term382 s l) = (term392 s l).
Proof. exact (MK_COMB (@lem5298594) (@lem5298593 s l)). Qed.
Lemma lem5298596 (s : real -> Prop) (l : real) : ((term381 s l) = (term382 s l)) = ((term380 s l) = (term392 s l)).
Proof. exact (MK_COMB (@lem5298589 s l) (@lem5298595 s l)). Qed.
Lemma lem5298597 (s : real -> Prop) (l : real) : (term380 s l) = (term392 s l).
Proof. exact (EQ_MP (@lem5298596 s l) (@lem5298581 s l)). Qed.
Lemma lem5298598 (s : real -> Prop) (l : real) : (term301 s l) = (term392 s l).
Proof. exact (TRANS (@lem5298577 s l) (@lem5298597 s l)). Qed.
Lemma lem5298599 (s : real -> Prop) (l : real) : (term307 s l) = (term307 s l).
Proof. exact (eq_refl (term307 s l)). Qed.
Lemma lem5298600 (s : real -> Prop) (l : real) : (term309 s l) = (term393 s l).
Proof. exact (MK_COMB (@lem5298599 s l) (@lem5298598 s l)). Qed.
Lemma lem5298602 {A : Type'} (P : Prop) (Q : A -> Prop) : (term142 A P Q) = (term143 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5298603 (P : Prop) (Q : type1028) : (term144 P Q) = (term145 P Q).
Proof. exact (@lem5298602 (real -> real) P Q). Qed.
Lemma lem5298604 (s : real -> Prop) (l : real) : (term394 s l) = (term395 s l).
Proof. exact (@lem5298603 (has_inf s l) (term391 s l)). Qed.
Lemma lem5298605 (x : real -> real) (s : real -> Prop) (l : real) : (term396 s l x) = (term389 x s l).
Proof. exact (eq_refl (term396 s l x)). Qed.
Lemma lem5298606 (s : real -> Prop) (l : real) : (term397 s l) = (term391 s l).
Proof. exact (fun_ext (fun x : real -> real => @lem5298605 x s l)). Qed.
Lemma lem5298607 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5298608 (s : real -> Prop) (l : real) : (term398 s l) = (term392 s l).
Proof. exact (MK_COMB (@lem5298607) (@lem5298606 s l)). Qed.
Lemma lem5298609 (s : real -> Prop) (l : real) : (term307 s l) = (term307 s l).
Proof. exact (eq_refl (term307 s l)). Qed.
Lemma lem5298610 (s : real -> Prop) (l : real) : (term394 s l) = (term393 s l).
Proof. exact (MK_COMB (@lem5298609 s l) (@lem5298608 s l)). Qed.
Lemma lem5298611 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5298612 (s : real -> Prop) (l : real) : (term399 s l) = (term400 s l).
Proof. exact (MK_COMB (@lem5298611) (@lem5298610 s l)). Qed.
Lemma lem5298613 (x : real -> real) (s : real -> Prop) (l : real) : (term396 s l x) = (term389 x s l).
Proof. exact (eq_refl (term396 s l x)). Qed.
Lemma lem5298614 (s : real -> Prop) (l : real) : (term307 s l) = (term307 s l).
Proof. exact (eq_refl (term307 s l)). Qed.
Lemma lem5298615 (x : real -> real) (s : real -> Prop) (l : real) : (term401 s l x) = (term402 x s l).
Proof. exact (MK_COMB (@lem5298614 s l) (@lem5298613 x s l)). Qed.
Lemma lem5298616 (s : real -> Prop) (l : real) : (term403 s l) = (term404 s l).
Proof. exact (fun_ext (fun x : real -> real => @lem5298615 x s l)). Qed.
Lemma lem5298617 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5298618 (s : real -> Prop) (l : real) : (term395 s l) = (term405 s l).
Proof. exact (MK_COMB (@lem5298617) (@lem5298616 s l)). Qed.
Lemma lem5298619 (s : real -> Prop) (l : real) : ((term394 s l) = (term395 s l)) = ((term393 s l) = (term405 s l)).
Proof. exact (MK_COMB (@lem5298612 s l) (@lem5298618 s l)). Qed.
Lemma lem5298620 (s : real -> Prop) (l : real) : (term393 s l) = (term405 s l).
Proof. exact (EQ_MP (@lem5298619 s l) (@lem5298604 s l)). Qed.
Lemma lem5298621 (s : real -> Prop) (l : real) : (term309 s l) = (term405 s l).
Proof. exact (TRANS (@lem5298600 s l) (@lem5298620 s l)). Qed.
Lemma lem5298622 (s : real -> Prop) : (term324 s) = (term406 s).
Proof. exact (fun_ext (fun l : real => @lem5298621 s l)). Qed.
Lemma lem5298623 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5298624 (s : real -> Prop) : (term335 s) = (term407 s).
Proof. exact (MK_COMB (@lem5298623) (@lem5298622 s)). Qed.
Lemma lem5298626 {A B : Type'} (P : type1413 A B) : (term116 A B P) = (term117 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5298627 (P : type1618) : (term408 P) = (term409 P).
Proof. exact (@lem5298626 real (real -> real) P). Qed.
Lemma lem5298628 (s : real -> Prop) : (term410 s) = (term411 s).
Proof. exact (@lem5298627 (term412 s)). Qed.
Lemma lem5298629 (s : real -> Prop) (l : real) : (term413 s l) = (term404 s l).
Proof. exact (eq_refl (term413 s l)). Qed.
Lemma lem5298630 (x : real -> real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5298631 (s : real -> Prop) (l : real) (x : real -> real) : (term414 s l x) = (term415 s l x).
Proof. exact (MK_COMB (@lem5298629 s l) (@lem5298630 x)). Qed.
Lemma lem5298632 (x : real -> real) (s : real -> Prop) (l : real) : (term415 s l x) = (term402 x s l).
Proof. exact (eq_refl (term415 s l x)). Qed.
Lemma lem5298633 (x : real -> real) (s : real -> Prop) (l : real) : (term414 s l x) = (term402 x s l).
Proof. exact (TRANS (@lem5298631 s l x) (@lem5298632 x s l)). Qed.
Lemma lem5298634 (s : real -> Prop) (l : real) : (term416 s l) = (term404 s l).
Proof. exact (fun_ext (fun x : real -> real => @lem5298633 x s l)). Qed.
Lemma lem5298635 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5298636 (s : real -> Prop) (l : real) : (term417 s l) = (term405 s l).
Proof. exact (MK_COMB (@lem5298635) (@lem5298634 s l)). Qed.
Lemma lem5298637 (s : real -> Prop) : (term418 s) = (term406 s).
Proof. exact (fun_ext (fun l : real => @lem5298636 s l)). Qed.
Lemma lem5298638 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5298639 (s : real -> Prop) : (term410 s) = (term407 s).
Proof. exact (MK_COMB (@lem5298638) (@lem5298637 s)). Qed.
Lemma lem5298640 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5298641 (s : real -> Prop) : (term419 s) = (term420 s).
Proof. exact (MK_COMB (@lem5298640) (@lem5298639 s)). Qed.
Lemma lem5298642 (s : real -> Prop) (l : real) : (term413 s l) = (term404 s l).
Proof. exact (eq_refl (term413 s l)). Qed.
Lemma lem5298643 (x : type1627) (l : real) : (x l) = (x l).
Proof. exact (eq_refl (x l)). Qed.
Lemma lem5298644 (s : real -> Prop) (x : type1627) (l : real) : (term421 s x l) = (term422 s x l).
Proof. exact (MK_COMB (@lem5298642 s l) (@lem5298643 x l)). Qed.
Lemma lem5298645 (x : type1627) (s : real -> Prop) (l : real) : (term422 s x l) = (term423 x s l).
Proof. exact (eq_refl (term422 s x l)). Qed.
Lemma lem5298646 (x : type1627) (s : real -> Prop) (l : real) : (term421 s x l) = (term423 x s l).
Proof. exact (TRANS (@lem5298644 s x l) (@lem5298645 x s l)). Qed.
Lemma lem5298647 (x : type1627) (s : real -> Prop) : (term424 s x) = (term425 x s).
Proof. exact (fun_ext (fun l : real => @lem5298646 x s l)). Qed.
Lemma lem5298648 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5298649 (x : type1627) (s : real -> Prop) : (term426 s x) = (term427 x s).
Proof. exact (MK_COMB (@lem5298648) (@lem5298647 x s)). Qed.
Lemma lem5298650 (s : real -> Prop) : (term428 s) = (term429 s).
Proof. exact (fun_ext (fun x : type1627 => @lem5298649 x s)). Qed.
Lemma lem5298651 : (@ex (real -> real -> real)) = (@ex (real -> real -> real)).
Proof. exact (eq_refl (@ex (real -> real -> real))). Qed.
Lemma lem5298652 (s : real -> Prop) : (term411 s) = (term430 s).
Proof. exact (MK_COMB (@lem5298651) (@lem5298650 s)). Qed.
Lemma lem5298653 (s : real -> Prop) : ((term410 s) = (term411 s)) = ((term407 s) = (term430 s)).
Proof. exact (MK_COMB (@lem5298641 s) (@lem5298652 s)). Qed.
Lemma lem5298654 (s : real -> Prop) : (term407 s) = (term430 s).
Proof. exact (EQ_MP (@lem5298653 s) (@lem5298628 s)). Qed.
Lemma lem5298655 (s : real -> Prop) : (term335 s) = (term430 s).
Proof. exact (TRANS (@lem5298624 s) (@lem5298654 s)). Qed.
Lemma lem5298656 : term348 = term431.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5298655 s)). Qed.
Lemma lem5298657 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5298658 : term359 = term432.
Proof. exact (MK_COMB (@lem5298657) (@lem5298656)). Qed.
Lemma lem5298660 {A B : Type'} (P : type1413 A B) : (term116 A B P) = (term117 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5298661 (P : type1016) : (term433 P) = (term434 P).
Proof. exact (@lem5298660 (real -> Prop) type1627 P). Qed.
Lemma lem5298662 : term435 = term436.
Proof. exact (@lem5298661 term437). Qed.
Lemma lem5298663 (s : real -> Prop) : (term438 s) = (term429 s).
Proof. exact (eq_refl (term438 s)). Qed.
Lemma lem5298664 (x : type1627) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5298665 (s : real -> Prop) (x : type1627) : (term439 s x) = (term440 s x).
Proof. exact (MK_COMB (@lem5298663 s) (@lem5298664 x)). Qed.
Lemma lem5298666 (x : type1627) (s : real -> Prop) : (term440 s x) = (term427 x s).
Proof. exact (eq_refl (term440 s x)). Qed.
Lemma lem5298667 (x : type1627) (s : real -> Prop) : (term439 s x) = (term427 x s).
Proof. exact (TRANS (@lem5298665 s x) (@lem5298666 x s)). Qed.
Lemma lem5298668 (s : real -> Prop) : (term441 s) = (term429 s).
Proof. exact (fun_ext (fun x : type1627 => @lem5298667 x s)). Qed.
Lemma lem5298669 : (@ex (real -> real -> real)) = (@ex (real -> real -> real)).
Proof. exact (eq_refl (@ex (real -> real -> real))). Qed.
Lemma lem5298670 (s : real -> Prop) : (term442 s) = (term430 s).
Proof. exact (MK_COMB (@lem5298669) (@lem5298668 s)). Qed.
Lemma lem5298671 : term443 = term431.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5298670 s)). Qed.
Lemma lem5298672 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5298673 : term435 = term432.
Proof. exact (MK_COMB (@lem5298672) (@lem5298671)). Qed.
Lemma lem5298674 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5298675 : term444 = term445.
Proof. exact (MK_COMB (@lem5298674) (@lem5298673)). Qed.
Lemma lem5298676 (s : real -> Prop) : (term438 s) = (term429 s).
Proof. exact (eq_refl (term438 s)). Qed.
Lemma lem5298677 (x : type1019) (s : real -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem5298678 (x : type1019) (s : real -> Prop) : (term446 x s) = (term447 x s).
Proof. exact (MK_COMB (@lem5298676 s) (@lem5298677 x s)). Qed.
Lemma lem5298679 (x : type1019) (s : real -> Prop) : (term447 x s) = (term448 x s).
Proof. exact (eq_refl (term447 x s)). Qed.
Lemma lem5298680 (x : type1019) (s : real -> Prop) : (term446 x s) = (term448 x s).
Proof. exact (TRANS (@lem5298678 x s) (@lem5298679 x s)). Qed.
Lemma lem5298681 (x : type1019) : (term449 x) = (term450 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5298680 x s)). Qed.
Lemma lem5298682 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5298683 (x : type1019) : (term451 x) = (term452 x).
Proof. exact (MK_COMB (@lem5298682) (@lem5298681 x)). Qed.
Lemma lem5298684 : term453 = term454.
Proof. exact (fun_ext (fun x : type1019 => @lem5298683 x)). Qed.
Lemma lem5298685 : (@ex ((real -> Prop) -> real -> real -> real)) = (@ex ((real -> Prop) -> real -> real -> real)).
Proof. exact (eq_refl (@ex ((real -> Prop) -> real -> real -> real))). Qed.
Lemma lem5298686 : term436 = term455.
Proof. exact (MK_COMB (@lem5298685) (@lem5298684)). Qed.
Lemma lem5298687 : (term435 = term436) = (term432 = term455).
Proof. exact (MK_COMB (@lem5298675) (@lem5298686)). Qed.
Lemma lem5298688 : term432 = term455.
Proof. exact (EQ_MP (@lem5298687) (@lem5298662)). Qed.
Lemma lem5298689 : term359 = term455.
Proof. exact (TRANS (@lem5298658) (@lem5298688)). Qed.
Lemma lem5298690 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5298691 : term361 = term456.
Proof. exact (MK_COMB (@lem5298690) (@lem5298689)). Qed.
Lemma lem5298693 {A : Type'} (P : A -> Prop) (Q : Prop) : (term159 A P Q) = (term160 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5298694 (P : real -> Prop) (Q : Prop) : (term161 P Q) = (term162 P Q).
Proof. exact (@lem5298693 real P Q). Qed.
Lemma lem5298695 (s : real -> Prop) (l : real) : (term457 s l) = (term458 s l).
Proof. exact (@lem5298694 (term63 s) ((inf s) = l)). Qed.
Lemma lem5298696 (s : real -> Prop) (b : real) : (term202 s b) = (term55 s b).
Proof. exact (eq_refl (term202 s b)). Qed.
Lemma lem5298697 (s : real -> Prop) : (term203 s) = (term63 s).
Proof. exact (fun_ext (fun b : real => @lem5298696 s b)). Qed.
Lemma lem5298698 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5298699 (s : real -> Prop) : (term204 s) = (term64 s).
Proof. exact (MK_COMB (@lem5298698) (@lem5298697 s)). Qed.
Lemma lem5298700 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5298701 (s : real -> Prop) : (term459 s) = (term298 s).
Proof. exact (MK_COMB (@lem5298700) (@lem5298699 s)). Qed.
Lemma lem5298702 (s : real -> Prop) (l : real) : ((inf s) = l) = ((inf s) = l).
Proof. exact (eq_refl ((inf s) = l)). Qed.
Lemma lem5298703 (s : real -> Prop) (l : real) : (term457 s l) = (term299 s l).
Proof. exact (MK_COMB (@lem5298701 s) (@lem5298702 s l)). Qed.
Lemma lem5298704 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5298705 (s : real -> Prop) (l : real) : (term460 s l) = (term461 s l).
Proof. exact (MK_COMB (@lem5298704) (@lem5298703 s l)). Qed.
Lemma lem5298706 (s : real -> Prop) (b : real) : (term202 s b) = (term55 s b).
Proof. exact (eq_refl (term202 s b)). Qed.
Lemma lem5298707 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5298708 (s : real -> Prop) (b : real) : (term462 s b) = (term463 s b).
Proof. exact (MK_COMB (@lem5298707) (@lem5298706 s b)). Qed.
Lemma lem5298709 (s : real -> Prop) (l : real) : ((inf s) = l) = ((inf s) = l).
Proof. exact (eq_refl ((inf s) = l)). Qed.
Lemma lem5298710 (b : real) (s : real -> Prop) (l : real) : (term464 b s l) = (term465 b s l).
Proof. exact (MK_COMB (@lem5298708 s b) (@lem5298709 s l)). Qed.
Lemma lem5298711 (s : real -> Prop) (l : real) : (term466 s l) = (term467 s l).
Proof. exact (fun_ext (fun b : real => @lem5298710 b s l)). Qed.
Lemma lem5298712 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5298713 (s : real -> Prop) (l : real) : (term458 s l) = (term468 s l).
Proof. exact (MK_COMB (@lem5298712) (@lem5298711 s l)). Qed.
Lemma lem5298714 (s : real -> Prop) (l : real) : ((term457 s l) = (term458 s l)) = ((term299 s l) = (term468 s l)).
Proof. exact (MK_COMB (@lem5298705 s l) (@lem5298713 s l)). Qed.
Lemma lem5298715 (s : real -> Prop) (l : real) : (term299 s l) = (term468 s l).
Proof. exact (EQ_MP (@lem5298714 s l) (@lem5298695 s l)). Qed.
Lemma lem5298716 (s : real -> Prop) : (term20 s) = (term20 s).
Proof. exact (eq_refl (term20 s)). Qed.
Lemma lem5298717 (s : real -> Prop) (l : real) : (term303 s l) = (term469 s l).
Proof. exact (MK_COMB (@lem5298716 s) (@lem5298715 s l)). Qed.
Lemma lem5298719 {A : Type'} (P : Prop) (Q : A -> Prop) : (term177 A P Q) = (term178 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5298720 (P : Prop) (Q : real -> Prop) : (term198 P Q) = (term199 P Q).
Proof. exact (@lem5298719 real P Q). Qed.
Lemma lem5298721 (s : real -> Prop) (l : real) : (term470 s l) = (term471 s l).
Proof. exact (@lem5298720 (term70 s) (term467 s l)). Qed.
Lemma lem5298722 (b : real) (s : real -> Prop) (l : real) : (term472 s l b) = (term465 b s l).
Proof. exact (eq_refl (term472 s l b)). Qed.
Lemma lem5298723 (s : real -> Prop) (l : real) : (term473 s l) = (term467 s l).
Proof. exact (fun_ext (fun b : real => @lem5298722 b s l)). Qed.
Lemma lem5298724 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5298725 (s : real -> Prop) (l : real) : (term474 s l) = (term468 s l).
Proof. exact (MK_COMB (@lem5298724) (@lem5298723 s l)). Qed.
Lemma lem5298726 (s : real -> Prop) : (term20 s) = (term20 s).
Proof. exact (eq_refl (term20 s)). Qed.
Lemma lem5298727 (s : real -> Prop) (l : real) : (term470 s l) = (term469 s l).
Proof. exact (MK_COMB (@lem5298726 s) (@lem5298725 s l)). Qed.
Lemma lem5298728 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5298729 (s : real -> Prop) (l : real) : (term475 s l) = (term476 s l).
Proof. exact (MK_COMB (@lem5298728) (@lem5298727 s l)). Qed.
Lemma lem5298730 (b : real) (s : real -> Prop) (l : real) : (term472 s l b) = (term465 b s l).
Proof. exact (eq_refl (term472 s l b)). Qed.
Lemma lem5298731 (s : real -> Prop) : (term20 s) = (term20 s).
Proof. exact (eq_refl (term20 s)). Qed.
Lemma lem5298732 (b : real) (s : real -> Prop) (l : real) : (term477 s l b) = (term478 b s l).
Proof. exact (MK_COMB (@lem5298731 s) (@lem5298730 b s l)). Qed.
Lemma lem5298733 (s : real -> Prop) (l : real) : (term479 s l) = (term480 s l).
Proof. exact (fun_ext (fun b : real => @lem5298732 b s l)). Qed.
Lemma lem5298734 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5298735 (s : real -> Prop) (l : real) : (term471 s l) = (term481 s l).
Proof. exact (MK_COMB (@lem5298734) (@lem5298733 s l)). Qed.
Lemma lem5298736 (s : real -> Prop) (l : real) : ((term470 s l) = (term471 s l)) = ((term469 s l) = (term481 s l)).
Proof. exact (MK_COMB (@lem5298729 s l) (@lem5298735 s l)). Qed.
Lemma lem5298737 (s : real -> Prop) (l : real) : (term469 s l) = (term481 s l).
Proof. exact (EQ_MP (@lem5298736 s l) (@lem5298721 s l)). Qed.
Lemma lem5298738 (s : real -> Prop) (l : real) : (term303 s l) = (term481 s l).
Proof. exact (TRANS (@lem5298717 s l) (@lem5298737 s l)). Qed.
Lemma lem5298739 (s : real -> Prop) (l : real) : (term304 s l) = (term304 s l).
Proof. exact (eq_refl (term304 s l)). Qed.
Lemma lem5298740 (s : real -> Prop) (l : real) : (term306 s l) = (term482 s l).
Proof. exact (MK_COMB (@lem5298739 s l) (@lem5298738 s l)). Qed.
Lemma lem5298742 {A : Type'} (P : Prop) (Q : A -> Prop) : (term142 A P Q) = (term143 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5298743 (P : Prop) (Q : real -> Prop) : (term483 P Q) = (term484 P Q).
Proof. exact (@lem5298742 real P Q). Qed.
Lemma lem5298744 (s : real -> Prop) (l : real) : (term485 s l) = (term486 s l).
Proof. exact (@lem5298743 (term37 s l) (term480 s l)). Qed.
Lemma lem5298745 (b : real) (s : real -> Prop) (l : real) : (term487 s l b) = (term478 b s l).
Proof. exact (eq_refl (term487 s l b)). Qed.
Lemma lem5298746 (s : real -> Prop) (l : real) : (term488 s l) = (term480 s l).
Proof. exact (fun_ext (fun b : real => @lem5298745 b s l)). Qed.
Lemma lem5298747 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5298748 (s : real -> Prop) (l : real) : (term489 s l) = (term481 s l).
Proof. exact (MK_COMB (@lem5298747) (@lem5298746 s l)). Qed.
Lemma lem5298749 (s : real -> Prop) (l : real) : (term304 s l) = (term304 s l).
Proof. exact (eq_refl (term304 s l)). Qed.
Lemma lem5298750 (s : real -> Prop) (l : real) : (term485 s l) = (term482 s l).
Proof. exact (MK_COMB (@lem5298749 s l) (@lem5298748 s l)). Qed.
Lemma lem5298751 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5298752 (s : real -> Prop) (l : real) : (term490 s l) = (term491 s l).
Proof. exact (MK_COMB (@lem5298751) (@lem5298750 s l)). Qed.
Lemma lem5298753 (b : real) (s : real -> Prop) (l : real) : (term487 s l b) = (term478 b s l).
Proof. exact (eq_refl (term487 s l b)). Qed.
Lemma lem5298754 (s : real -> Prop) (l : real) : (term304 s l) = (term304 s l).
Proof. exact (eq_refl (term304 s l)). Qed.
Lemma lem5298755 (b : real) (s : real -> Prop) (l : real) : (term492 s l b) = (term493 b s l).
Proof. exact (MK_COMB (@lem5298754 s l) (@lem5298753 b s l)). Qed.
Lemma lem5298756 (s : real -> Prop) (l : real) : (term494 s l) = (term495 s l).
Proof. exact (fun_ext (fun b : real => @lem5298755 b s l)). Qed.
Lemma lem5298757 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5298758 (s : real -> Prop) (l : real) : (term486 s l) = (term496 s l).
Proof. exact (MK_COMB (@lem5298757) (@lem5298756 s l)). Qed.
Lemma lem5298759 (s : real -> Prop) (l : real) : ((term485 s l) = (term486 s l)) = ((term482 s l) = (term496 s l)).
Proof. exact (MK_COMB (@lem5298752 s l) (@lem5298758 s l)). Qed.
Lemma lem5298760 (s : real -> Prop) (l : real) : (term482 s l) = (term496 s l).
Proof. exact (EQ_MP (@lem5298759 s l) (@lem5298744 s l)). Qed.
Lemma lem5298761 (s : real -> Prop) (l : real) : (term306 s l) = (term496 s l).
Proof. exact (TRANS (@lem5298740 s l) (@lem5298760 s l)). Qed.
Lemma lem5298762 (s : real -> Prop) : (term325 s) = (term497 s).
Proof. exact (fun_ext (fun l : real => @lem5298761 s l)). Qed.
Lemma lem5298763 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5298764 (s : real -> Prop) : (term340 s) = (term498 s).
Proof. exact (MK_COMB (@lem5298763) (@lem5298762 s)). Qed.
Lemma lem5298766 {A B : Type'} (P : type1413 A B) : (term116 A B P) = (term117 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5298767 (P : type1626) : (term118 P) = (term119 P).
Proof. exact (@lem5298766 real real P). Qed.
Lemma lem5298768 (s : real -> Prop) : (term499 s) = (term500 s).
Proof. exact (@lem5298767 (term501 s)). Qed.
Lemma lem5298769 (s : real -> Prop) (l : real) : (term502 s l) = (term495 s l).
Proof. exact (eq_refl (term502 s l)). Qed.
Lemma lem5298770 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem5298771 (s : real -> Prop) (l : real) (b : real) : (term503 s l b) = (term504 s l b).
Proof. exact (MK_COMB (@lem5298769 s l) (@lem5298770 b)). Qed.
Lemma lem5298772 (b : real) (s : real -> Prop) (l : real) : (term504 s l b) = (term493 b s l).
Proof. exact (eq_refl (term504 s l b)). Qed.
Lemma lem5298773 (b : real) (s : real -> Prop) (l : real) : (term503 s l b) = (term493 b s l).
Proof. exact (TRANS (@lem5298771 s l b) (@lem5298772 b s l)). Qed.
Lemma lem5298774 (s : real -> Prop) (l : real) : (term505 s l) = (term495 s l).
Proof. exact (fun_ext (fun b : real => @lem5298773 b s l)). Qed.
Lemma lem5298775 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5298776 (s : real -> Prop) (l : real) : (term506 s l) = (term496 s l).
Proof. exact (MK_COMB (@lem5298775) (@lem5298774 s l)). Qed.
Lemma lem5298777 (s : real -> Prop) : (term507 s) = (term497 s).
Proof. exact (fun_ext (fun l : real => @lem5298776 s l)). Qed.
Lemma lem5298778 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5298779 (s : real -> Prop) : (term499 s) = (term498 s).
Proof. exact (MK_COMB (@lem5298778) (@lem5298777 s)). Qed.
Lemma lem5298780 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5298781 (s : real -> Prop) : (term508 s) = (term509 s).
Proof. exact (MK_COMB (@lem5298780) (@lem5298779 s)). Qed.
Lemma lem5298782 (s : real -> Prop) (l : real) : (term502 s l) = (term495 s l).
Proof. exact (eq_refl (term502 s l)). Qed.
Lemma lem5298783 (b : real -> real) (l : real) : (b l) = (b l).
Proof. exact (eq_refl (b l)). Qed.
Lemma lem5298784 (s : real -> Prop) (b : real -> real) (l : real) : (term510 s b l) = (term511 s b l).
Proof. exact (MK_COMB (@lem5298782 s l) (@lem5298783 b l)). Qed.
Lemma lem5298785 (b : real -> real) (s : real -> Prop) (l : real) : (term511 s b l) = (term512 b s l).
Proof. exact (eq_refl (term511 s b l)). Qed.
Lemma lem5298786 (b : real -> real) (s : real -> Prop) (l : real) : (term510 s b l) = (term512 b s l).
Proof. exact (TRANS (@lem5298784 s b l) (@lem5298785 b s l)). Qed.
Lemma lem5298787 (b : real -> real) (s : real -> Prop) : (term513 s b) = (term514 b s).
Proof. exact (fun_ext (fun l : real => @lem5298786 b s l)). Qed.
Lemma lem5298788 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5298789 (b : real -> real) (s : real -> Prop) : (term515 s b) = (term516 b s).
Proof. exact (MK_COMB (@lem5298788) (@lem5298787 b s)). Qed.
Lemma lem5298790 (s : real -> Prop) : (term517 s) = (term518 s).
Proof. exact (fun_ext (fun b : real -> real => @lem5298789 b s)). Qed.
Lemma lem5298791 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5298792 (s : real -> Prop) : (term500 s) = (term519 s).
Proof. exact (MK_COMB (@lem5298791) (@lem5298790 s)). Qed.
Lemma lem5298793 (s : real -> Prop) : ((term499 s) = (term500 s)) = ((term498 s) = (term519 s)).
Proof. exact (MK_COMB (@lem5298781 s) (@lem5298792 s)). Qed.
Lemma lem5298794 (s : real -> Prop) : (term498 s) = (term519 s).
Proof. exact (EQ_MP (@lem5298793 s) (@lem5298768 s)). Qed.
Lemma lem5298795 (s : real -> Prop) : (term340 s) = (term519 s).
Proof. exact (TRANS (@lem5298764 s) (@lem5298794 s)). Qed.
Lemma lem5298796 : term349 = term520.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5298795 s)). Qed.
Lemma lem5298797 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5298798 : term364 = term521.
Proof. exact (MK_COMB (@lem5298797) (@lem5298796)). Qed.
Lemma lem5298800 {A B : Type'} (P : type1413 A B) : (term116 A B P) = (term117 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5298801 (P : type1017) : (term522 P) = (term523 P).
Proof. exact (@lem5298800 (real -> Prop) (real -> real) P). Qed.
Lemma lem5298802 : term524 = term525.
Proof. exact (@lem5298801 term526). Qed.
Lemma lem5298803 (s : real -> Prop) : (term527 s) = (term518 s).
Proof. exact (eq_refl (term527 s)). Qed.
Lemma lem5298804 (b : real -> real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem5298805 (s : real -> Prop) (b : real -> real) : (term528 s b) = (term529 s b).
Proof. exact (MK_COMB (@lem5298803 s) (@lem5298804 b)). Qed.
Lemma lem5298806 (b : real -> real) (s : real -> Prop) : (term529 s b) = (term516 b s).
Proof. exact (eq_refl (term529 s b)). Qed.
Lemma lem5298807 (b : real -> real) (s : real -> Prop) : (term528 s b) = (term516 b s).
Proof. exact (TRANS (@lem5298805 s b) (@lem5298806 b s)). Qed.
Lemma lem5298808 (s : real -> Prop) : (term530 s) = (term518 s).
Proof. exact (fun_ext (fun b : real -> real => @lem5298807 b s)). Qed.
Lemma lem5298809 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5298810 (s : real -> Prop) : (term531 s) = (term519 s).
Proof. exact (MK_COMB (@lem5298809) (@lem5298808 s)). Qed.
Lemma lem5298811 : term532 = term520.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5298810 s)). Qed.
Lemma lem5298812 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5298813 : term524 = term521.
Proof. exact (MK_COMB (@lem5298812) (@lem5298811)). Qed.
Lemma lem5298814 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5298815 : term533 = term534.
Proof. exact (MK_COMB (@lem5298814) (@lem5298813)). Qed.
Lemma lem5298816 (s : real -> Prop) : (term527 s) = (term518 s).
Proof. exact (eq_refl (term527 s)). Qed.
Lemma lem5298817 (b : type1021) (s : real -> Prop) : (b s) = (b s).
Proof. exact (eq_refl (b s)). Qed.
Lemma lem5298818 (b : type1021) (s : real -> Prop) : (term535 b s) = (term536 b s).
Proof. exact (MK_COMB (@lem5298816 s) (@lem5298817 b s)). Qed.
Lemma lem5298819 (b : type1021) (s : real -> Prop) : (term536 b s) = (term537 b s).
Proof. exact (eq_refl (term536 b s)). Qed.
Lemma lem5298820 (b : type1021) (s : real -> Prop) : (term535 b s) = (term537 b s).
Proof. exact (TRANS (@lem5298818 b s) (@lem5298819 b s)). Qed.
Lemma lem5298821 (b : type1021) : (term538 b) = (term539 b).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5298820 b s)). Qed.
Lemma lem5298822 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5298823 (b : type1021) : (term540 b) = (term541 b).
Proof. exact (MK_COMB (@lem5298822) (@lem5298821 b)). Qed.
Lemma lem5298824 : term542 = term543.
Proof. exact (fun_ext (fun b : type1021 => @lem5298823 b)). Qed.
Lemma lem5298825 : (@ex ((real -> Prop) -> real -> real)) = (@ex ((real -> Prop) -> real -> real)).
Proof. exact (eq_refl (@ex ((real -> Prop) -> real -> real))). Qed.
Lemma lem5298826 : term525 = term544.
Proof. exact (MK_COMB (@lem5298825) (@lem5298824)). Qed.
Lemma lem5298827 : (term524 = term525) = (term521 = term544).
Proof. exact (MK_COMB (@lem5298815) (@lem5298826)). Qed.
Lemma lem5298828 : term521 = term544.
Proof. exact (EQ_MP (@lem5298827) (@lem5298802)). Qed.
Lemma lem5298829 : term364 = term544.
Proof. exact (TRANS (@lem5298798) (@lem5298828)). Qed.
Lemma lem5298830 : term365 = term545.
Proof. exact (MK_COMB (@lem5298691) (@lem5298829)). Qed.
Lemma lem5298832 {A : Type'} (P : A -> Prop) (Q : Prop) : (term159 A P Q) = (term160 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5298833 (P : type255) (Q : Prop) : (term546 P Q) = (term547 P Q).
Proof. exact (@lem5298832 type1019 P Q). Qed.
Lemma lem5298834 : term548 = term549.
Proof. exact (@lem5298833 term454 term544). Qed.
Lemma lem5298835 (x : type1019) : (term550 x) = (term452 x).
Proof. exact (eq_refl (term550 x)). Qed.
Lemma lem5298836 : term551 = term454.
Proof. exact (fun_ext (fun x : type1019 => @lem5298835 x)). Qed.
Lemma lem5298837 : (@ex ((real -> Prop) -> real -> real -> real)) = (@ex ((real -> Prop) -> real -> real -> real)).
Proof. exact (eq_refl (@ex ((real -> Prop) -> real -> real -> real))). Qed.
Lemma lem5298838 : term552 = term455.
Proof. exact (MK_COMB (@lem5298837) (@lem5298836)). Qed.
Lemma lem5298839 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5298840 : term553 = term456.
Proof. exact (MK_COMB (@lem5298839) (@lem5298838)). Qed.
Lemma lem5298841 : term544 = term544.
Proof. exact (eq_refl term544). Qed.
Lemma lem5298842 : term548 = term545.
Proof. exact (MK_COMB (@lem5298840) (@lem5298841)). Qed.
Lemma lem5298843 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5298844 : term554 = term555.
Proof. exact (MK_COMB (@lem5298843) (@lem5298842)). Qed.
Lemma lem5298845 (x : type1019) : (term550 x) = (term452 x).
Proof. exact (eq_refl (term550 x)). Qed.
Lemma lem5298846 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5298847 (x : type1019) : (term556 x) = (term557 x).
Proof. exact (MK_COMB (@lem5298846) (@lem5298845 x)). Qed.
Lemma lem5298848 : term544 = term544.
Proof. exact (eq_refl term544). Qed.
Lemma lem5298849 (x : type1019) : (term558 x) = (term559 x).
Proof. exact (MK_COMB (@lem5298847 x) (@lem5298848)). Qed.
Lemma lem5298850 : term560 = term561.
Proof. exact (fun_ext (fun x : type1019 => @lem5298849 x)). Qed.
Lemma lem5298851 : (@ex ((real -> Prop) -> real -> real -> real)) = (@ex ((real -> Prop) -> real -> real -> real)).
Proof. exact (eq_refl (@ex ((real -> Prop) -> real -> real -> real))). Qed.
Lemma lem5298852 : term549 = term562.
Proof. exact (MK_COMB (@lem5298851) (@lem5298850)). Qed.
Lemma lem5298853 : (term548 = term549) = (term545 = term562).
Proof. exact (MK_COMB (@lem5298844) (@lem5298852)). Qed.
Lemma lem5298854 : term545 = term562.
Proof. exact (EQ_MP (@lem5298853) (@lem5298834)). Qed.
Lemma lem5298856 {A : Type'} (P : Prop) (Q : A -> Prop) : (term177 A P Q) = (term178 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5298857 (P : Prop) (Q : type256) : (term563 P Q) = (term564 P Q).
Proof. exact (@lem5298856 type1021 P Q). Qed.
Lemma lem5298858 (x : type1019) : (term565 x) = (term566 x).
Proof. exact (@lem5298857 (term452 x) term543). Qed.
Lemma lem5298859 (b : type1021) : (term567 b) = (term541 b).
Proof. exact (eq_refl (term567 b)). Qed.
Lemma lem5298860 : term568 = term543.
Proof. exact (fun_ext (fun b : type1021 => @lem5298859 b)). Qed.
Lemma lem5298861 : (@ex ((real -> Prop) -> real -> real)) = (@ex ((real -> Prop) -> real -> real)).
Proof. exact (eq_refl (@ex ((real -> Prop) -> real -> real))). Qed.
Lemma lem5298862 : term569 = term544.
Proof. exact (MK_COMB (@lem5298861) (@lem5298860)). Qed.
Lemma lem5298863 (x : type1019) : (term557 x) = (term557 x).
Proof. exact (eq_refl (term557 x)). Qed.
Lemma lem5298864 (x : type1019) : (term565 x) = (term559 x).
Proof. exact (MK_COMB (@lem5298863 x) (@lem5298862)). Qed.
Lemma lem5298865 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5298866 (x : type1019) : (term570 x) = (term571 x).
Proof. exact (MK_COMB (@lem5298865) (@lem5298864 x)). Qed.
Lemma lem5298867 (b : type1021) : (term567 b) = (term541 b).
Proof. exact (eq_refl (term567 b)). Qed.
Lemma lem5298868 (x : type1019) : (term557 x) = (term557 x).
Proof. exact (eq_refl (term557 x)). Qed.
Lemma lem5298869 (x : type1019) (b : type1021) : (term572 x b) = (term573 x b).
Proof. exact (MK_COMB (@lem5298868 x) (@lem5298867 b)). Qed.
Lemma lem5298870 (x : type1019) : (term574 x) = (term575 x).
Proof. exact (fun_ext (fun b : type1021 => @lem5298869 x b)). Qed.
Lemma lem5298871 : (@ex ((real -> Prop) -> real -> real)) = (@ex ((real -> Prop) -> real -> real)).
Proof. exact (eq_refl (@ex ((real -> Prop) -> real -> real))). Qed.
Lemma lem5298872 (x : type1019) : (term566 x) = (term576 x).
Proof. exact (MK_COMB (@lem5298871) (@lem5298870 x)). Qed.
Lemma lem5298873 (x : type1019) : ((term565 x) = (term566 x)) = ((term559 x) = (term576 x)).
Proof. exact (MK_COMB (@lem5298866 x) (@lem5298872 x)). Qed.
Lemma lem5298874 (x : type1019) : (term559 x) = (term576 x).
Proof. exact (EQ_MP (@lem5298873 x) (@lem5298858 x)). Qed.
Lemma lem5298875 : term561 = term577.
Proof. exact (fun_ext (fun x : type1019 => @lem5298874 x)). Qed.
Lemma lem5298876 : (@ex ((real -> Prop) -> real -> real -> real)) = (@ex ((real -> Prop) -> real -> real -> real)).
Proof. exact (eq_refl (@ex ((real -> Prop) -> real -> real -> real))). Qed.
Lemma lem5298877 : term562 = term578.
Proof. exact (MK_COMB (@lem5298876) (@lem5298875)). Qed.
Lemma lem5298878 : term545 = term578.
Proof. exact (TRANS (@lem5298854) (@lem5298877)). Qed.
Lemma lem5298879 : term365 = term578.
Proof. exact (TRANS (@lem5298830) (@lem5298878)). Qed.
Lemma lem5298880 : term317 = term578.
Proof. exact (TRANS (@lem5298516) (@lem5298879)). Qed.
Lemma lem5298881 : term10 = term578.
Proof. exact (TRANS (@lem5298046) (@lem5298880)). Qed.
Lemma lem5298882 (h1 : term10) : term578.
Proof. exact (EQ_MP (@lem5298881) (@lem5297382 h1)). Qed.
Lemma lem5298883 (x : type1019) (h1 : term576 x) : term576 x.
Proof. exact (h1). Qed.
Lemma lem5298884 (x : type1019) (b : type1021) (h1 : term573 x b) : term573 x b.
Proof. exact (h1). Qed.
Lemma lem5298885 (s : real -> Prop) (h1 : term289 s) : term289 s.
Proof. exact (h1). Qed.
Lemma lem5298886 (s : real -> Prop) (l : real) (h1 : term287 s l) : term287 s l.
Proof. exact (h1). Qed.
Lemma lem5298887 (x' : real -> real) (s : real -> Prop) (l : real) (h1 : term284 x' s l) : term284 x' s l.
Proof. exact (h1). Qed.
Lemma lem5298894 (s : real -> Prop) (l : real) : ((inf s) = l) = ((inf s) = l).
Proof. exact (eq_refl ((inf s) = l)). Qed.
Lemma lem5298913 (b : type1021) (s : real -> Prop) (l : real) (x : real) : (term579 b s l x) = (term579 b s l x).
Proof. exact (eq_refl (term579 b s l x)). Qed.
Lemma lem5298914 (b : type1021) (s : real -> Prop) (l : real) : (term580 b s l) = (term580 b s l).
Proof. exact (fun_ext (fun x : real => @lem5298913 b s l x)). Qed.
Lemma lem5298915 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5298916 (b : type1021) (s : real -> Prop) (l : real) : (term581 b s l) = (term581 b s l).
Proof. exact (MK_COMB (@lem5298915) (@lem5298914 b s l)). Qed.
Lemma lem5298917 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5298918 (b : type1021) (s : real -> Prop) (l : real) : (term582 b s l) = (term582 b s l).
Proof. exact (MK_COMB (@lem5298917) (@lem5298916 b s l)). Qed.
Lemma lem5298919 (b : type1021) (s : real -> Prop) (l : real) : (term583 b s l) = (term583 b s l).
Proof. exact (MK_COMB (@lem5298918 b s l) (@lem5298894 s l)). Qed.
Lemma lem5298928 (s : real -> Prop) : (term20 s) = (term20 s).
Proof. exact (eq_refl (term20 s)). Qed.
Lemma lem5298929 (b : type1021) (s : real -> Prop) (l : real) : (term584 b s l) = (term584 b s l).
Proof. exact (MK_COMB (@lem5298928 s) (@lem5298919 b s l)). Qed.
Lemma lem5298938 (s : real -> Prop) (l : real) : (term304 s l) = (term304 s l).
Proof. exact (eq_refl (term304 s l)). Qed.
Lemma lem5298939 (b : type1021) (s : real -> Prop) (l : real) : (term585 b s l) = (term585 b s l).
Proof. exact (MK_COMB (@lem5298938 s l) (@lem5298929 b s l)). Qed.
Lemma lem5298940 (b : type1021) (s : real -> Prop) : (term586 b s) = (term586 b s).
Proof. exact (fun_ext (fun l : real => @lem5298939 b s l)). Qed.
Lemma lem5298941 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5298942 (b : type1021) (s : real -> Prop) : (term537 b s) = (term537 b s).
Proof. exact (MK_COMB (@lem5298941) (@lem5298940 b s)). Qed.
Lemma lem5298943 (b : type1021) : (term539 b) = (term539 b).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5298942 b s)). Qed.
Lemma lem5298944 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5298945 (b : type1021) : (term541 b) = (term541 b).
Proof. exact (MK_COMB (@lem5298944) (@lem5298943 b)). Qed.
Lemma lem5298954 (s : real -> Prop) (l : real) : (term292 s l) = (term292 s l).
Proof. exact (eq_refl (term292 s l)). Qed.
Lemma lem5298981 (x : type1019) (s : real -> Prop) (l : real) (b : real) : (term587 x s l b) = (term587 x s l b).
Proof. exact (eq_refl (term587 x s l b)). Qed.
Lemma lem5298982 (x : type1019) (s : real -> Prop) (l : real) : (term588 x s l) = (term588 x s l).
Proof. exact (fun_ext (fun b : real => @lem5298981 x s l b)). Qed.
Lemma lem5298983 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5298984 (x : type1019) (s : real -> Prop) (l : real) : (term589 x s l) = (term589 x s l).
Proof. exact (MK_COMB (@lem5298983) (@lem5298982 x s l)). Qed.
Lemma lem5298985 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5298986 (x : type1019) (s : real -> Prop) (l : real) : (term590 x s l) = (term590 x s l).
Proof. exact (MK_COMB (@lem5298985) (@lem5298984 x s l)). Qed.
Lemma lem5298987 (x : type1019) (s : real -> Prop) (l : real) : (term591 x s l) = (term591 x s l).
Proof. exact (MK_COMB (@lem5298986 x s l) (@lem5298954 s l)). Qed.
Lemma lem5298994 (s : real -> Prop) : (term66 s) = (term66 s).
Proof. exact (eq_refl (term66 s)). Qed.
Lemma lem5298995 (x : type1019) (s : real -> Prop) (l : real) : (term592 x s l) = (term592 x s l).
Proof. exact (MK_COMB (@lem5298994 s) (@lem5298987 x s l)). Qed.
Lemma lem5299002 (s : real -> Prop) (l : real) : (term307 s l) = (term307 s l).
Proof. exact (eq_refl (term307 s l)). Qed.
Lemma lem5299003 (x : type1019) (s : real -> Prop) (l : real) : (term593 x s l) = (term593 x s l).
Proof. exact (MK_COMB (@lem5299002 s l) (@lem5298995 x s l)). Qed.
Lemma lem5299004 (x : type1019) (s : real -> Prop) : (term594 x s) = (term594 x s).
Proof. exact (fun_ext (fun l : real => @lem5299003 x s l)). Qed.
Lemma lem5299005 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5299006 (x : type1019) (s : real -> Prop) : (term448 x s) = (term448 x s).
Proof. exact (MK_COMB (@lem5299005) (@lem5299004 x s)). Qed.
Lemma lem5299007 (x : type1019) : (term450 x) = (term450 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5299006 x s)). Qed.
Lemma lem5299008 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5299009 (x : type1019) : (term452 x) = (term452 x).
Proof. exact (MK_COMB (@lem5299008) (@lem5299007 x)). Qed.
Lemma lem5299010 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5299011 (x : type1019) : (term557 x) = (term557 x).
Proof. exact (MK_COMB (@lem5299010) (@lem5299009 x)). Qed.
Lemma lem5299012 (x : type1019) (b : type1021) : (term573 x b) = (term573 x b).
Proof. exact (MK_COMB (@lem5299011 x) (@lem5298945 b)). Qed.
Lemma lem5299013 (x : type1019) (b : type1021) (h1 : term573 x b) : term573 x b.
Proof. exact (EQ_MP (@lem5299012 x b) (@lem5298884 x b h1)). Qed.
Lemma lem5299028 (s : real -> Prop) (l : real) (x : real) : (term44 s l x) = (term44 s l x).
Proof. exact (eq_refl (term44 s l x)). Qed.
Lemma lem5299029 (s : real -> Prop) (l : real) : (term54 s l) = (term54 s l).
Proof. exact (fun_ext (fun x : real => @lem5299028 s l x)). Qed.
Lemma lem5299030 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5299031 (s : real -> Prop) (l : real) : (term55 s l) = (term55 s l).
Proof. exact (MK_COMB (@lem5299030) (@lem5299029 s l)). Qed.
Lemma lem5299040 (s : real -> Prop) : (term20 s) = (term20 s).
Proof. exact (eq_refl (term20 s)). Qed.
Lemma lem5299041 (s : real -> Prop) (l : real) : (term208 s l) = (term208 s l).
Proof. exact (MK_COMB (@lem5299040 s) (@lem5299031 s l)). Qed.
Lemma lem5299048 (s : real -> Prop) (l : real) : (term37 s l) = (term37 s l).
Proof. exact (eq_refl (term37 s l)). Qed.
Lemma lem5299049 (s : real -> Prop) : (term39 s) = (term39 s).
Proof. exact (fun_ext (fun l : real => @lem5299048 s l)). Qed.
Lemma lem5299050 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5299051 (s : real -> Prop) : (term40 s) = (term40 s).
Proof. exact (MK_COMB (@lem5299050) (@lem5299049 s)). Qed.
Lemma lem5299052 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5299053 (s : real -> Prop) : (term73 s) = (term73 s).
Proof. exact (MK_COMB (@lem5299052) (@lem5299051 s)). Qed.
Lemma lem5299054 (s : real -> Prop) (l : real) : (term221 s l) = (term221 s l).
Proof. exact (MK_COMB (@lem5299053 s) (@lem5299041 s l)). Qed.
Lemma lem5299073 (s : real -> Prop) (x' : real -> real) (b : real) : (term133 s x' b) = (term133 s x' b).
Proof. exact (eq_refl (term133 s x' b)). Qed.
Lemma lem5299074 (s : real -> Prop) (x' : real -> real) : (term135 s x') = (term135 s x').
Proof. exact (fun_ext (fun b : real => @lem5299073 s x' b)). Qed.
Lemma lem5299075 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5299076 (s : real -> Prop) (x' : real -> real) : (term137 s x') = (term137 s x').
Proof. exact (MK_COMB (@lem5299075) (@lem5299074 s x')). Qed.
Lemma lem5299083 (s : real -> Prop) : (term66 s) = (term66 s).
Proof. exact (eq_refl (term66 s)). Qed.
Lemma lem5299084 (s : real -> Prop) (x' : real -> real) : (term154 s x') = (term154 s x').
Proof. exact (MK_COMB (@lem5299083 s) (@lem5299076 s x')). Qed.
Lemma lem5299091 (s : real -> Prop) (l : real) : (term171 s l) = (term171 s l).
Proof. exact (eq_refl (term171 s l)). Qed.
Lemma lem5299092 (l : real) (s : real -> Prop) (x' : real -> real) : (term189 l s x') = (term189 l s x').
Proof. exact (MK_COMB (@lem5299091 s l) (@lem5299084 s x')). Qed.
Lemma lem5299093 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5299094 (l : real) (s : real -> Prop) (x' : real -> real) : (term282 l s x') = (term282 l s x').
Proof. exact (MK_COMB (@lem5299093) (@lem5299092 l s x')). Qed.
Lemma lem5299095 (x' : real -> real) (s : real -> Prop) (l : real) : (term284 x' s l) = (term284 x' s l).
Proof. exact (MK_COMB (@lem5299094 l s x') (@lem5299054 s l)). Qed.
Lemma lem5299096 (x' : real -> real) (s : real -> Prop) (l : real) (h1 : term284 x' s l) : term284 x' s l.
Proof. exact (EQ_MP (@lem5299095 x' s l) (@lem5298887 x' s l h1)). Qed.
Lemma lem5299097 (x : type1019) (b : type1021) (h1 : term573 x b) : term541 b.
Proof. exact (proj2 (@lem5299013 x b h1)). Qed.
Lemma lem5299098 (x : type1019) (b : type1021) (h1 : term573 x b) : term452 x.
Proof. exact (proj1 (@lem5299013 x b h1)). Qed.
Lemma lem5299099 (l : real) (s : real -> Prop) (x' : real -> real) (h1 : term189 l s x') : term189 l s x'.
Proof. exact (h1). Qed.
Lemma lem5299100 (s : real -> Prop) (l : real) (h1 : term221 s l) : term221 s l.
Proof. exact (h1). Qed.
Lemma lem5299101 (l : real) (s : real -> Prop) (x' : real -> real) (h1 : term189 l s x') : term154 s x'.
Proof. exact (proj2 (@lem5299099 l s x' h1)). Qed.
Lemma lem5299104 (s : real -> Prop) (x' : real -> real) (h1 : term137 s x') : term137 s x'.
Proof. exact (h1). Qed.
Lemma lem5299105 (s : real -> Prop) (l : real) (h1 : term221 s l) : term208 s l.
Proof. exact (proj2 (@lem5299100 s l h1)). Qed.
Lemma lem5299106 (s : real -> Prop) (l : real) (h1 : term221 s l) : term40 s.
Proof. exact (proj1 (@lem5299100 s l h1)). Qed.
Lemma lem5299107 (s : real -> Prop) (l : real) (h1 : term221 s l) : term55 s l.
Proof. exact (proj2 (@lem5299105 s l h1)). Qed.
Lemma lem5299238 {A : Type'} (P : A -> Prop) (Q : Prop) : (term595 A P Q) = (term596 A P Q).
Proof. exact (EQ_MP (@lem19025 A P Q) (@lem19024 A P Q)). Qed.
Lemma lem5299239 (P : real -> Prop) (Q : Prop) : (term597 P Q) = (term598 P Q).
Proof. exact (@lem5299238 real P Q). Qed.
Lemma lem5299240 (b : type1021) (s : real -> Prop) (l : real) : (term599 b s l) = (term600 b s l).
Proof. exact (@lem5299239 (term580 b s l) ((inf s) = l)). Qed.
Lemma lem5299241 (b : type1021) (s : real -> Prop) (l : real) (x : real) : (term601 b s l x) = (term579 b s l x).
Proof. exact (eq_refl (term601 b s l x)). Qed.
Lemma lem5299242 (b : type1021) (s : real -> Prop) (l : real) : (term602 b s l) = (term580 b s l).
Proof. exact (fun_ext (fun x : real => @lem5299241 b s l x)). Qed.
Lemma lem5299243 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5299244 (b : type1021) (s : real -> Prop) (l : real) : (term603 b s l) = (term581 b s l).
Proof. exact (MK_COMB (@lem5299243) (@lem5299242 b s l)). Qed.
Lemma lem5299245 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5299246 (b : type1021) (s : real -> Prop) (l : real) : (term604 b s l) = (term582 b s l).
Proof. exact (MK_COMB (@lem5299245) (@lem5299244 b s l)). Qed.
Lemma lem5299247 (s : real -> Prop) (l : real) : ((inf s) = l) = ((inf s) = l).
Proof. exact (eq_refl ((inf s) = l)). Qed.
Lemma lem5299248 (b : type1021) (s : real -> Prop) (l : real) : (term599 b s l) = (term583 b s l).
Proof. exact (MK_COMB (@lem5299246 b s l) (@lem5299247 s l)). Qed.
Lemma lem5299249 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5299250 (b : type1021) (s : real -> Prop) (l : real) : (term605 b s l) = (term606 b s l).
Proof. exact (MK_COMB (@lem5299249) (@lem5299248 b s l)). Qed.
Lemma lem5299251 (b : type1021) (s : real -> Prop) (l : real) (x : real) : (term601 b s l x) = (term579 b s l x).
Proof. exact (eq_refl (term601 b s l x)). Qed.
Lemma lem5299252 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5299253 (b : type1021) (s : real -> Prop) (l : real) (x : real) : (term607 b s l x) = (term608 b s l x).
Proof. exact (MK_COMB (@lem5299252) (@lem5299251 b s l x)). Qed.
Lemma lem5299254 (s : real -> Prop) (l : real) : ((inf s) = l) = ((inf s) = l).
Proof. exact (eq_refl ((inf s) = l)). Qed.
Lemma lem5299255 (b : type1021) (x : real) (s : real -> Prop) (l : real) : (term609 b x s l) = (term610 b x s l).
Proof. exact (MK_COMB (@lem5299253 b s l x) (@lem5299254 s l)). Qed.
Lemma lem5299256 (b : type1021) (s : real -> Prop) (l : real) : (term611 b s l) = (term612 b s l).
Proof. exact (fun_ext (fun x : real => @lem5299255 b x s l)). Qed.
Lemma lem5299257 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5299258 (b : type1021) (s : real -> Prop) (l : real) : (term600 b s l) = (term613 b s l).
Proof. exact (MK_COMB (@lem5299257) (@lem5299256 b s l)). Qed.
Lemma lem5299259 (b : type1021) (s : real -> Prop) (l : real) : ((term599 b s l) = (term600 b s l)) = ((term583 b s l) = (term613 b s l)).
Proof. exact (MK_COMB (@lem5299250 b s l) (@lem5299258 b s l)). Qed.
Lemma lem5299260 (b : type1021) (s : real -> Prop) (l : real) : (term583 b s l) = (term613 b s l).
Proof. exact (EQ_MP (@lem5299259 b s l) (@lem5299240 b s l)). Qed.
Lemma lem5299261 (s : real -> Prop) : (term20 s) = (term20 s).
Proof. exact (eq_refl (term20 s)). Qed.
Lemma lem5299262 (b : type1021) (s : real -> Prop) (l : real) : (term584 b s l) = (term614 b s l).
Proof. exact (MK_COMB (@lem5299261 s) (@lem5299260 b s l)). Qed.
Lemma lem5299264 {A : Type'} (P : Prop) (Q : A -> Prop) : (term615 A P Q) = (term616 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem5299265 (P : Prop) (Q : real -> Prop) : (term617 P Q) = (term618 P Q).
Proof. exact (@lem5299264 real P Q). Qed.
Lemma lem5299266 (b : type1021) (s : real -> Prop) (l : real) : (term619 b s l) = (term620 b s l).
Proof. exact (@lem5299265 (term70 s) (term612 b s l)). Qed.
Lemma lem5299267 (b : type1021) (x : real) (s : real -> Prop) (l : real) : (term621 b s l x) = (term610 b x s l).
Proof. exact (eq_refl (term621 b s l x)). Qed.
Lemma lem5299268 (b : type1021) (s : real -> Prop) (l : real) : (term622 b s l) = (term612 b s l).
Proof. exact (fun_ext (fun x : real => @lem5299267 b x s l)). Qed.
Lemma lem5299269 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5299270 (b : type1021) (s : real -> Prop) (l : real) : (term623 b s l) = (term613 b s l).
Proof. exact (MK_COMB (@lem5299269) (@lem5299268 b s l)). Qed.
Lemma lem5299271 (s : real -> Prop) : (term20 s) = (term20 s).
Proof. exact (eq_refl (term20 s)). Qed.
Lemma lem5299272 (b : type1021) (s : real -> Prop) (l : real) : (term619 b s l) = (term614 b s l).
Proof. exact (MK_COMB (@lem5299271 s) (@lem5299270 b s l)). Qed.
Lemma lem5299273 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5299274 (b : type1021) (s : real -> Prop) (l : real) : (term624 b s l) = (term625 b s l).
Proof. exact (MK_COMB (@lem5299273) (@lem5299272 b s l)). Qed.
Lemma lem5299275 (b : type1021) (x : real) (s : real -> Prop) (l : real) : (term621 b s l x) = (term610 b x s l).
Proof. exact (eq_refl (term621 b s l x)). Qed.
Lemma lem5299276 (s : real -> Prop) : (term20 s) = (term20 s).
Proof. exact (eq_refl (term20 s)). Qed.
Lemma lem5299277 (b : type1021) (x : real) (s : real -> Prop) (l : real) : (term626 b s l x) = (term627 b x s l).
Proof. exact (MK_COMB (@lem5299276 s) (@lem5299275 b x s l)). Qed.
Lemma lem5299278 (b : type1021) (s : real -> Prop) (l : real) : (term628 b s l) = (term629 b s l).
Proof. exact (fun_ext (fun x : real => @lem5299277 b x s l)). Qed.
Lemma lem5299279 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5299280 (b : type1021) (s : real -> Prop) (l : real) : (term620 b s l) = (term630 b s l).
Proof. exact (MK_COMB (@lem5299279) (@lem5299278 b s l)). Qed.
Lemma lem5299281 (b : type1021) (s : real -> Prop) (l : real) : ((term619 b s l) = (term620 b s l)) = ((term614 b s l) = (term630 b s l)).
Proof. exact (MK_COMB (@lem5299274 b s l) (@lem5299280 b s l)). Qed.
Lemma lem5299282 (b : type1021) (s : real -> Prop) (l : real) : (term614 b s l) = (term630 b s l).
Proof. exact (EQ_MP (@lem5299281 b s l) (@lem5299266 b s l)). Qed.
Lemma lem5299283 (b : type1021) (s : real -> Prop) (l : real) : (term584 b s l) = (term630 b s l).
Proof. exact (TRANS (@lem5299262 b s l) (@lem5299282 b s l)). Qed.
Lemma lem5299284 (s : real -> Prop) (l : real) : (term304 s l) = (term304 s l).
Proof. exact (eq_refl (term304 s l)). Qed.
Lemma lem5299285 (b : type1021) (s : real -> Prop) (l : real) : (term585 b s l) = (term631 b s l).
Proof. exact (MK_COMB (@lem5299284 s l) (@lem5299283 b s l)). Qed.
Lemma lem5299287 {A : Type'} (P : Prop) (Q : A -> Prop) : (term632 A P Q) = (term633 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5299288 (P : Prop) (Q : real -> Prop) : (term634 P Q) = (term635 P Q).
Proof. exact (@lem5299287 real P Q). Qed.
Lemma lem5299289 (b : type1021) (s : real -> Prop) (l : real) : (term636 b s l) = (term637 b s l).
Proof. exact (@lem5299288 (term37 s l) (term629 b s l)). Qed.
Lemma lem5299290 (b : type1021) (x : real) (s : real -> Prop) (l : real) : (term638 b s l x) = (term627 b x s l).
Proof. exact (eq_refl (term638 b s l x)). Qed.
Lemma lem5299291 (b : type1021) (s : real -> Prop) (l : real) : (term639 b s l) = (term629 b s l).
Proof. exact (fun_ext (fun x : real => @lem5299290 b x s l)). Qed.
Lemma lem5299292 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5299293 (b : type1021) (s : real -> Prop) (l : real) : (term640 b s l) = (term630 b s l).
Proof. exact (MK_COMB (@lem5299292) (@lem5299291 b s l)). Qed.
Lemma lem5299294 (s : real -> Prop) (l : real) : (term304 s l) = (term304 s l).
Proof. exact (eq_refl (term304 s l)). Qed.
Lemma lem5299295 (b : type1021) (s : real -> Prop) (l : real) : (term636 b s l) = (term631 b s l).
Proof. exact (MK_COMB (@lem5299294 s l) (@lem5299293 b s l)). Qed.
Lemma lem5299296 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5299297 (b : type1021) (s : real -> Prop) (l : real) : (term641 b s l) = (term642 b s l).
Proof. exact (MK_COMB (@lem5299296) (@lem5299295 b s l)). Qed.
Lemma lem5299298 (b : type1021) (x : real) (s : real -> Prop) (l : real) : (term638 b s l x) = (term627 b x s l).
Proof. exact (eq_refl (term638 b s l x)). Qed.
Lemma lem5299299 (s : real -> Prop) (l : real) : (term304 s l) = (term304 s l).
Proof. exact (eq_refl (term304 s l)). Qed.
Lemma lem5299300 (b : type1021) (x : real) (s : real -> Prop) (l : real) : (term643 b s l x) = (term644 b x s l).
Proof. exact (MK_COMB (@lem5299299 s l) (@lem5299298 b x s l)). Qed.
Lemma lem5299301 (b : type1021) (s : real -> Prop) (l : real) : (term645 b s l) = (term646 b s l).
Proof. exact (fun_ext (fun x : real => @lem5299300 b x s l)). Qed.
Lemma lem5299302 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5299303 (b : type1021) (s : real -> Prop) (l : real) : (term637 b s l) = (term647 b s l).
Proof. exact (MK_COMB (@lem5299302) (@lem5299301 b s l)). Qed.
Lemma lem5299304 (b : type1021) (s : real -> Prop) (l : real) : ((term636 b s l) = (term637 b s l)) = ((term631 b s l) = (term647 b s l)).
Proof. exact (MK_COMB (@lem5299297 b s l) (@lem5299303 b s l)). Qed.
Lemma lem5299305 (b : type1021) (s : real -> Prop) (l : real) : (term631 b s l) = (term647 b s l).
Proof. exact (EQ_MP (@lem5299304 b s l) (@lem5299289 b s l)). Qed.
Lemma lem5299306 (b : type1021) (s : real -> Prop) (l : real) : (term585 b s l) = (term647 b s l).
Proof. exact (TRANS (@lem5299285 b s l) (@lem5299305 b s l)). Qed.
Lemma lem5299307 (b : type1021) (s : real -> Prop) : (term586 b s) = (term648 b s).
Proof. exact (fun_ext (fun l : real => @lem5299306 b s l)). Qed.
Lemma lem5299308 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5299309 (b : type1021) (s : real -> Prop) : (term537 b s) = (term649 b s).
Proof. exact (MK_COMB (@lem5299308) (@lem5299307 b s)). Qed.
Lemma lem5299310 (b : type1021) : (term539 b) = (term650 b).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5299309 b s)). Qed.
Lemma lem5299311 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5299312 (b : type1021) : (term541 b) = (term651 b).
Proof. exact (MK_COMB (@lem5299311) (@lem5299310 b)). Qed.
Lemma lem5299332 (b : type1021) (x : real) (s : real -> Prop) (l : real) : (term644 b x s l) = (term652 b x s l).
Proof. exact (@lem19490 (term70 s) (term37 s l) (term610 b x s l)). Qed.
Lemma lem5299339 (b : type1021) (x : real) (s : real -> Prop) (l : real) : (term653 b x s l) = (term654 b x s l).
Proof. exact (@lem19490 (term579 b s l x) (term37 s l) ((inf s) = l)). Qed.
Lemma lem5299342 (l : real) (s : real -> Prop) : (term655 l s) = (term655 l s).
Proof. exact (eq_refl (term655 l s)). Qed.
Lemma lem5299343 (b : type1021) (x : real) (s : real -> Prop) (l : real) : (term652 b x s l) = (term656 b x s l).
Proof. exact (MK_COMB (@lem5299342 l s) (@lem5299339 b x s l)). Qed.
Lemma lem5299345 (b : type1021) (x : real) (s : real -> Prop) (l : real) : (term644 b x s l) = (term656 b x s l).
Proof. exact (TRANS (@lem5299332 b x s l) (@lem5299343 b x s l)). Qed.
Lemma lem5299346 (b : type1021) (s : real -> Prop) (l : real) : (term646 b s l) = (term657 b s l).
Proof. exact (fun_ext (fun x : real => @lem5299345 b x s l)). Qed.
Lemma lem5299347 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5299348 (b : type1021) (s : real -> Prop) (l : real) : (term647 b s l) = (term658 b s l).
Proof. exact (MK_COMB (@lem5299347) (@lem5299346 b s l)). Qed.
Lemma lem5299349 (b : type1021) (s : real -> Prop) : (term648 b s) = (term659 b s).
Proof. exact (fun_ext (fun l : real => @lem5299348 b s l)). Qed.
Lemma lem5299350 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5299351 (b : type1021) (s : real -> Prop) : (term649 b s) = (term660 b s).
Proof. exact (MK_COMB (@lem5299350) (@lem5299349 b s)). Qed.
Lemma lem5299352 (b : type1021) : (term650 b) = (term661 b).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5299351 b s)). Qed.
Lemma lem5299353 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5299354 (b : type1021) : (term651 b) = (term662 b).
Proof. exact (MK_COMB (@lem5299353) (@lem5299352 b)). Qed.
Lemma lem5299355 (b : type1021) : (term541 b) = (term662 b).
Proof. exact (TRANS (@lem5299312 b) (@lem5299354 b)). Qed.
Lemma lem5299356 (x : type1019) (b : type1021) (h1 : term573 x b) : term662 b.
Proof. exact (EQ_MP (@lem5299355 b) (@lem5299097 x b h1)). Qed.
Lemma lem5299364 (s : real -> Prop) (h1 : s = (@EMPTY real)) : s = (@EMPTY real).
Proof. exact (h1). Qed.
Lemma lem5299494 {A : Type'} (P : A -> Prop) (Q : Prop) : (term595 A P Q) = (term596 A P Q).
Proof. exact (EQ_MP (@lem19025 A P Q) (@lem19024 A P Q)). Qed.
Lemma lem5299495 (P : real -> Prop) (Q : Prop) : (term597 P Q) = (term598 P Q).
Proof. exact (@lem5299494 real P Q). Qed.
Lemma lem5299496 (b : type1021) (s : real -> Prop) (l : real) : (term599 b s l) = (term600 b s l).
Proof. exact (@lem5299495 (term580 b s l) ((inf s) = l)). Qed.
Lemma lem5299497 (b : type1021) (s : real -> Prop) (l : real) (x : real) : (term601 b s l x) = (term579 b s l x).
Proof. exact (eq_refl (term601 b s l x)). Qed.
Lemma lem5299498 (b : type1021) (s : real -> Prop) (l : real) : (term602 b s l) = (term580 b s l).
Proof. exact (fun_ext (fun x : real => @lem5299497 b s l x)). Qed.
Lemma lem5299499 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5299500 (b : type1021) (s : real -> Prop) (l : real) : (term603 b s l) = (term581 b s l).
Proof. exact (MK_COMB (@lem5299499) (@lem5299498 b s l)). Qed.
Lemma lem5299501 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5299502 (b : type1021) (s : real -> Prop) (l : real) : (term604 b s l) = (term582 b s l).
Proof. exact (MK_COMB (@lem5299501) (@lem5299500 b s l)). Qed.
Lemma lem5299503 (s : real -> Prop) (l : real) : ((inf s) = l) = ((inf s) = l).
Proof. exact (eq_refl ((inf s) = l)). Qed.
Lemma lem5299504 (b : type1021) (s : real -> Prop) (l : real) : (term599 b s l) = (term583 b s l).
Proof. exact (MK_COMB (@lem5299502 b s l) (@lem5299503 s l)). Qed.
Lemma lem5299505 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5299506 (b : type1021) (s : real -> Prop) (l : real) : (term605 b s l) = (term606 b s l).
Proof. exact (MK_COMB (@lem5299505) (@lem5299504 b s l)). Qed.
Lemma lem5299507 (b : type1021) (s : real -> Prop) (l : real) (x : real) : (term601 b s l x) = (term579 b s l x).
Proof. exact (eq_refl (term601 b s l x)). Qed.
Lemma lem5299508 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5299509 (b : type1021) (s : real -> Prop) (l : real) (x : real) : (term607 b s l x) = (term608 b s l x).
Proof. exact (MK_COMB (@lem5299508) (@lem5299507 b s l x)). Qed.
Lemma lem5299510 (s : real -> Prop) (l : real) : ((inf s) = l) = ((inf s) = l).
Proof. exact (eq_refl ((inf s) = l)). Qed.
Lemma lem5299511 (b : type1021) (x : real) (s : real -> Prop) (l : real) : (term609 b x s l) = (term610 b x s l).
Proof. exact (MK_COMB (@lem5299509 b s l x) (@lem5299510 s l)). Qed.
Lemma lem5299512 (b : type1021) (s : real -> Prop) (l : real) : (term611 b s l) = (term612 b s l).
Proof. exact (fun_ext (fun x : real => @lem5299511 b x s l)). Qed.
Lemma lem5299513 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5299514 (b : type1021) (s : real -> Prop) (l : real) : (term600 b s l) = (term613 b s l).
Proof. exact (MK_COMB (@lem5299513) (@lem5299512 b s l)). Qed.
Lemma lem5299515 (b : type1021) (s : real -> Prop) (l : real) : ((term599 b s l) = (term600 b s l)) = ((term583 b s l) = (term613 b s l)).
Proof. exact (MK_COMB (@lem5299506 b s l) (@lem5299514 b s l)). Qed.
Lemma lem5299516 (b : type1021) (s : real -> Prop) (l : real) : (term583 b s l) = (term613 b s l).
Proof. exact (EQ_MP (@lem5299515 b s l) (@lem5299496 b s l)). Qed.
Lemma lem5299517 (s : real -> Prop) : (term20 s) = (term20 s).
Proof. exact (eq_refl (term20 s)). Qed.
Lemma lem5299518 (b : type1021) (s : real -> Prop) (l : real) : (term584 b s l) = (term614 b s l).
Proof. exact (MK_COMB (@lem5299517 s) (@lem5299516 b s l)). Qed.
Lemma lem5299520 {A : Type'} (P : Prop) (Q : A -> Prop) : (term615 A P Q) = (term616 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem5299521 (P : Prop) (Q : real -> Prop) : (term617 P Q) = (term618 P Q).
Proof. exact (@lem5299520 real P Q). Qed.
Lemma lem5299522 (b : type1021) (s : real -> Prop) (l : real) : (term619 b s l) = (term620 b s l).
Proof. exact (@lem5299521 (term70 s) (term612 b s l)). Qed.
Lemma lem5299523 (b : type1021) (x : real) (s : real -> Prop) (l : real) : (term621 b s l x) = (term610 b x s l).
Proof. exact (eq_refl (term621 b s l x)). Qed.
Lemma lem5299524 (b : type1021) (s : real -> Prop) (l : real) : (term622 b s l) = (term612 b s l).
Proof. exact (fun_ext (fun x : real => @lem5299523 b x s l)). Qed.
Lemma lem5299525 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5299526 (b : type1021) (s : real -> Prop) (l : real) : (term623 b s l) = (term613 b s l).
Proof. exact (MK_COMB (@lem5299525) (@lem5299524 b s l)). Qed.
Lemma lem5299527 (s : real -> Prop) : (term20 s) = (term20 s).
Proof. exact (eq_refl (term20 s)). Qed.
Lemma lem5299528 (b : type1021) (s : real -> Prop) (l : real) : (term619 b s l) = (term614 b s l).
Proof. exact (MK_COMB (@lem5299527 s) (@lem5299526 b s l)). Qed.
Lemma lem5299529 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5299530 (b : type1021) (s : real -> Prop) (l : real) : (term624 b s l) = (term625 b s l).
Proof. exact (MK_COMB (@lem5299529) (@lem5299528 b s l)). Qed.
Lemma lem5299531 (b : type1021) (x : real) (s : real -> Prop) (l : real) : (term621 b s l x) = (term610 b x s l).
Proof. exact (eq_refl (term621 b s l x)). Qed.
Lemma lem5299532 (s : real -> Prop) : (term20 s) = (term20 s).
Proof. exact (eq_refl (term20 s)). Qed.
Lemma lem5299533 (b : type1021) (x : real) (s : real -> Prop) (l : real) : (term626 b s l x) = (term627 b x s l).
Proof. exact (MK_COMB (@lem5299532 s) (@lem5299531 b x s l)). Qed.
Lemma lem5299534 (b : type1021) (s : real -> Prop) (l : real) : (term628 b s l) = (term629 b s l).
Proof. exact (fun_ext (fun x : real => @lem5299533 b x s l)). Qed.
Lemma lem5299535 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5299536 (b : type1021) (s : real -> Prop) (l : real) : (term620 b s l) = (term630 b s l).
Proof. exact (MK_COMB (@lem5299535) (@lem5299534 b s l)). Qed.
Lemma lem5299537 (b : type1021) (s : real -> Prop) (l : real) : ((term619 b s l) = (term620 b s l)) = ((term614 b s l) = (term630 b s l)).
Proof. exact (MK_COMB (@lem5299530 b s l) (@lem5299536 b s l)). Qed.
Lemma lem5299538 (b : type1021) (s : real -> Prop) (l : real) : (term614 b s l) = (term630 b s l).
Proof. exact (EQ_MP (@lem5299537 b s l) (@lem5299522 b s l)). Qed.
Lemma lem5299539 (b : type1021) (s : real -> Prop) (l : real) : (term584 b s l) = (term630 b s l).
Proof. exact (TRANS (@lem5299518 b s l) (@lem5299538 b s l)). Qed.
Lemma lem5299540 (s : real -> Prop) (l : real) : (term304 s l) = (term304 s l).
Proof. exact (eq_refl (term304 s l)). Qed.
Lemma lem5299541 (b : type1021) (s : real -> Prop) (l : real) : (term585 b s l) = (term631 b s l).
Proof. exact (MK_COMB (@lem5299540 s l) (@lem5299539 b s l)). Qed.
Lemma lem5299543 {A : Type'} (P : Prop) (Q : A -> Prop) : (term632 A P Q) = (term633 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5299544 (P : Prop) (Q : real -> Prop) : (term634 P Q) = (term635 P Q).
Proof. exact (@lem5299543 real P Q). Qed.
Lemma lem5299545 (b : type1021) (s : real -> Prop) (l : real) : (term636 b s l) = (term637 b s l).
Proof. exact (@lem5299544 (term37 s l) (term629 b s l)). Qed.
Lemma lem5299546 (b : type1021) (x : real) (s : real -> Prop) (l : real) : (term638 b s l x) = (term627 b x s l).
Proof. exact (eq_refl (term638 b s l x)). Qed.
Lemma lem5299547 (b : type1021) (s : real -> Prop) (l : real) : (term639 b s l) = (term629 b s l).
Proof. exact (fun_ext (fun x : real => @lem5299546 b x s l)). Qed.
Lemma lem5299548 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5299549 (b : type1021) (s : real -> Prop) (l : real) : (term640 b s l) = (term630 b s l).
Proof. exact (MK_COMB (@lem5299548) (@lem5299547 b s l)). Qed.
Lemma lem5299550 (s : real -> Prop) (l : real) : (term304 s l) = (term304 s l).
Proof. exact (eq_refl (term304 s l)). Qed.
Lemma lem5299551 (b : type1021) (s : real -> Prop) (l : real) : (term636 b s l) = (term631 b s l).
Proof. exact (MK_COMB (@lem5299550 s l) (@lem5299549 b s l)). Qed.
Lemma lem5299552 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5299553 (b : type1021) (s : real -> Prop) (l : real) : (term641 b s l) = (term642 b s l).
Proof. exact (MK_COMB (@lem5299552) (@lem5299551 b s l)). Qed.
Lemma lem5299554 (b : type1021) (x : real) (s : real -> Prop) (l : real) : (term638 b s l x) = (term627 b x s l).
Proof. exact (eq_refl (term638 b s l x)). Qed.
Lemma lem5299555 (s : real -> Prop) (l : real) : (term304 s l) = (term304 s l).
Proof. exact (eq_refl (term304 s l)). Qed.
Lemma lem5299556 (b : type1021) (x : real) (s : real -> Prop) (l : real) : (term643 b s l x) = (term644 b x s l).
Proof. exact (MK_COMB (@lem5299555 s l) (@lem5299554 b x s l)). Qed.
Lemma lem5299557 (b : type1021) (s : real -> Prop) (l : real) : (term645 b s l) = (term646 b s l).
Proof. exact (fun_ext (fun x : real => @lem5299556 b x s l)). Qed.
Lemma lem5299558 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5299559 (b : type1021) (s : real -> Prop) (l : real) : (term637 b s l) = (term647 b s l).
Proof. exact (MK_COMB (@lem5299558) (@lem5299557 b s l)). Qed.
Lemma lem5299560 (b : type1021) (s : real -> Prop) (l : real) : ((term636 b s l) = (term637 b s l)) = ((term631 b s l) = (term647 b s l)).
Proof. exact (MK_COMB (@lem5299553 b s l) (@lem5299559 b s l)). Qed.
Lemma lem5299561 (b : type1021) (s : real -> Prop) (l : real) : (term631 b s l) = (term647 b s l).
Proof. exact (EQ_MP (@lem5299560 b s l) (@lem5299545 b s l)). Qed.
Lemma lem5299562 (b : type1021) (s : real -> Prop) (l : real) : (term585 b s l) = (term647 b s l).
Proof. exact (TRANS (@lem5299541 b s l) (@lem5299561 b s l)). Qed.
Lemma lem5299563 (b : type1021) (s : real -> Prop) : (term586 b s) = (term648 b s).
Proof. exact (fun_ext (fun l : real => @lem5299562 b s l)). Qed.
Lemma lem5299564 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5299565 (b : type1021) (s : real -> Prop) : (term537 b s) = (term649 b s).
Proof. exact (MK_COMB (@lem5299564) (@lem5299563 b s)). Qed.
Lemma lem5299566 (b : type1021) : (term539 b) = (term650 b).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5299565 b s)). Qed.
Lemma lem5299567 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5299568 (b : type1021) : (term541 b) = (term651 b).
Proof. exact (MK_COMB (@lem5299567) (@lem5299566 b)). Qed.
Lemma lem5299588 (b : type1021) (x : real) (s : real -> Prop) (l : real) : (term644 b x s l) = (term652 b x s l).
Proof. exact (@lem19490 (term70 s) (term37 s l) (term610 b x s l)). Qed.
Lemma lem5299595 (b : type1021) (x : real) (s : real -> Prop) (l : real) : (term653 b x s l) = (term654 b x s l).
Proof. exact (@lem19490 (term579 b s l x) (term37 s l) ((inf s) = l)). Qed.
Lemma lem5299598 (l : real) (s : real -> Prop) : (term655 l s) = (term655 l s).
Proof. exact (eq_refl (term655 l s)). Qed.
Lemma lem5299599 (b : type1021) (x : real) (s : real -> Prop) (l : real) : (term652 b x s l) = (term656 b x s l).
Proof. exact (MK_COMB (@lem5299598 l s) (@lem5299595 b x s l)). Qed.
Lemma lem5299601 (b : type1021) (x : real) (s : real -> Prop) (l : real) : (term644 b x s l) = (term656 b x s l).
Proof. exact (TRANS (@lem5299588 b x s l) (@lem5299599 b x s l)). Qed.
Lemma lem5299602 (b : type1021) (s : real -> Prop) (l : real) : (term646 b s l) = (term657 b s l).
Proof. exact (fun_ext (fun x : real => @lem5299601 b x s l)). Qed.
Lemma lem5299603 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5299604 (b : type1021) (s : real -> Prop) (l : real) : (term647 b s l) = (term658 b s l).
Proof. exact (MK_COMB (@lem5299603) (@lem5299602 b s l)). Qed.
Lemma lem5299605 (b : type1021) (s : real -> Prop) : (term648 b s) = (term659 b s).
Proof. exact (fun_ext (fun l : real => @lem5299604 b s l)). Qed.
Lemma lem5299606 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5299607 (b : type1021) (s : real -> Prop) : (term649 b s) = (term660 b s).
Proof. exact (MK_COMB (@lem5299606) (@lem5299605 b s)). Qed.
Lemma lem5299608 (b : type1021) : (term650 b) = (term661 b).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5299607 b s)). Qed.
Lemma lem5299609 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5299610 (b : type1021) : (term651 b) = (term662 b).
Proof. exact (MK_COMB (@lem5299609) (@lem5299608 b)). Qed.
Lemma lem5299611 (b : type1021) : (term541 b) = (term662 b).
Proof. exact (TRANS (@lem5299568 b) (@lem5299610 b)). Qed.
Lemma lem5299612 (x : type1019) (b : type1021) (h1 : term573 x b) : term662 b.
Proof. exact (EQ_MP (@lem5299611 b) (@lem5299097 x b h1)). Qed.
Lemma lem5299622 (s : real -> Prop) (x' : real -> real) (b : real) : (term133 s x' b) = (term133 s x' b).
Proof. exact (eq_refl (term133 s x' b)). Qed.
Lemma lem5299623 (s : real -> Prop) (x' : real -> real) : (term135 s x') = (term135 s x').
Proof. exact (fun_ext (fun b : real => @lem5299622 s x' b)). Qed.
Lemma lem5299624 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5299626 (s : real -> Prop) (x' : real -> real) : (term137 s x') = (term137 s x').
Proof. exact (MK_COMB (@lem5299624) (@lem5299623 s x')). Qed.
Lemma lem5299627 (s : real -> Prop) (x' : real -> real) (h1 : term137 s x') : term137 s x'.
Proof. exact (EQ_MP (@lem5299626 s x') (@lem5299104 s x' h1)). Qed.
Lemma lem5299629 {A : Type'} (P : A -> Prop) (Q : Prop) : (term663 A P Q) = (term664 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem5299630 (P : real -> Prop) (Q : Prop) : (term665 P Q) = (term666 P Q).
Proof. exact (@lem5299629 real P Q). Qed.
Lemma lem5299631 (x : type1019) (s : real -> Prop) (l : real) : (term667 x s l) = (term668 x s l).
Proof. exact (@lem5299630 (term588 x s l) (term292 s l)). Qed.
Lemma lem5299632 (x : type1019) (s : real -> Prop) (l : real) (b : real) : (term669 x s l b) = (term587 x s l b).
Proof. exact (eq_refl (term669 x s l b)). Qed.
Lemma lem5299633 (x : type1019) (s : real -> Prop) (l : real) : (term670 x s l) = (term588 x s l).
Proof. exact (fun_ext (fun b : real => @lem5299632 x s l b)). Qed.
Lemma lem5299634 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5299635 (x : type1019) (s : real -> Prop) (l : real) : (term671 x s l) = (term589 x s l).
Proof. exact (MK_COMB (@lem5299634) (@lem5299633 x s l)). Qed.
Lemma lem5299636 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5299637 (x : type1019) (s : real -> Prop) (l : real) : (term672 x s l) = (term590 x s l).
Proof. exact (MK_COMB (@lem5299636) (@lem5299635 x s l)). Qed.
Lemma lem5299638 (s : real -> Prop) (l : real) : (term292 s l) = (term292 s l).
Proof. exact (eq_refl (term292 s l)). Qed.
Lemma lem5299639 (x : type1019) (s : real -> Prop) (l : real) : (term667 x s l) = (term591 x s l).
Proof. exact (MK_COMB (@lem5299637 x s l) (@lem5299638 s l)). Qed.
Lemma lem5299640 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5299641 (x : type1019) (s : real -> Prop) (l : real) : (term673 x s l) = (term674 x s l).
Proof. exact (MK_COMB (@lem5299640) (@lem5299639 x s l)). Qed.
Lemma lem5299642 (x : type1019) (s : real -> Prop) (l : real) (b : real) : (term669 x s l b) = (term587 x s l b).
Proof. exact (eq_refl (term669 x s l b)). Qed.
Lemma lem5299643 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5299644 (x : type1019) (s : real -> Prop) (l : real) (b : real) : (term675 x s l b) = (term676 x s l b).
Proof. exact (MK_COMB (@lem5299643) (@lem5299642 x s l b)). Qed.
Lemma lem5299645 (s : real -> Prop) (l : real) : (term292 s l) = (term292 s l).
Proof. exact (eq_refl (term292 s l)). Qed.
Lemma lem5299646 (x : type1019) (b : real) (s : real -> Prop) (l : real) : (term677 x b s l) = (term678 x b s l).
Proof. exact (MK_COMB (@lem5299644 x s l b) (@lem5299645 s l)). Qed.
Lemma lem5299647 (x : type1019) (s : real -> Prop) (l : real) : (term679 x s l) = (term680 x s l).
Proof. exact (fun_ext (fun b : real => @lem5299646 x b s l)). Qed.
Lemma lem5299648 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5299649 (x : type1019) (s : real -> Prop) (l : real) : (term668 x s l) = (term681 x s l).
Proof. exact (MK_COMB (@lem5299648) (@lem5299647 x s l)). Qed.
Lemma lem5299650 (x : type1019) (s : real -> Prop) (l : real) : ((term667 x s l) = (term668 x s l)) = ((term591 x s l) = (term681 x s l)).
Proof. exact (MK_COMB (@lem5299641 x s l) (@lem5299649 x s l)). Qed.
Lemma lem5299651 (x : type1019) (s : real -> Prop) (l : real) : (term591 x s l) = (term681 x s l).
Proof. exact (EQ_MP (@lem5299650 x s l) (@lem5299631 x s l)). Qed.
Lemma lem5299652 (s : real -> Prop) : (term66 s) = (term66 s).
Proof. exact (eq_refl (term66 s)). Qed.
Lemma lem5299653 (x : type1019) (s : real -> Prop) (l : real) : (term592 x s l) = (term682 x s l).
Proof. exact (MK_COMB (@lem5299652 s) (@lem5299651 x s l)). Qed.
Lemma lem5299655 {A : Type'} (P : Prop) (Q : A -> Prop) : (term632 A P Q) = (term633 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5299656 (P : Prop) (Q : real -> Prop) : (term634 P Q) = (term635 P Q).
Proof. exact (@lem5299655 real P Q). Qed.
Lemma lem5299657 (x : type1019) (s : real -> Prop) (l : real) : (term683 x s l) = (term684 x s l).
Proof. exact (@lem5299656 (s = (@EMPTY real)) (term680 x s l)). Qed.
Lemma lem5299658 (x : type1019) (b : real) (s : real -> Prop) (l : real) : (term685 x s l b) = (term678 x b s l).
Proof. exact (eq_refl (term685 x s l b)). Qed.
Lemma lem5299659 (x : type1019) (s : real -> Prop) (l : real) : (term686 x s l) = (term680 x s l).
Proof. exact (fun_ext (fun b : real => @lem5299658 x b s l)). Qed.
Lemma lem5299660 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5299661 (x : type1019) (s : real -> Prop) (l : real) : (term687 x s l) = (term681 x s l).
Proof. exact (MK_COMB (@lem5299660) (@lem5299659 x s l)). Qed.
Lemma lem5299662 (s : real -> Prop) : (term66 s) = (term66 s).
Proof. exact (eq_refl (term66 s)). Qed.
Lemma lem5299663 (x : type1019) (s : real -> Prop) (l : real) : (term683 x s l) = (term682 x s l).
Proof. exact (MK_COMB (@lem5299662 s) (@lem5299661 x s l)). Qed.
Lemma lem5299664 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5299665 (x : type1019) (s : real -> Prop) (l : real) : (term688 x s l) = (term689 x s l).
Proof. exact (MK_COMB (@lem5299664) (@lem5299663 x s l)). Qed.
Lemma lem5299666 (x : type1019) (b : real) (s : real -> Prop) (l : real) : (term685 x s l b) = (term678 x b s l).
Proof. exact (eq_refl (term685 x s l b)). Qed.
Lemma lem5299667 (s : real -> Prop) : (term66 s) = (term66 s).
Proof. exact (eq_refl (term66 s)). Qed.
Lemma lem5299668 (x : type1019) (b : real) (s : real -> Prop) (l : real) : (term690 x s l b) = (term691 x b s l).
Proof. exact (MK_COMB (@lem5299667 s) (@lem5299666 x b s l)). Qed.
Lemma lem5299669 (x : type1019) (s : real -> Prop) (l : real) : (term692 x s l) = (term693 x s l).
Proof. exact (fun_ext (fun b : real => @lem5299668 x b s l)). Qed.
Lemma lem5299670 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5299671 (x : type1019) (s : real -> Prop) (l : real) : (term684 x s l) = (term694 x s l).
Proof. exact (MK_COMB (@lem5299670) (@lem5299669 x s l)). Qed.
Lemma lem5299672 (x : type1019) (s : real -> Prop) (l : real) : ((term683 x s l) = (term684 x s l)) = ((term682 x s l) = (term694 x s l)).
Proof. exact (MK_COMB (@lem5299665 x s l) (@lem5299671 x s l)). Qed.
Lemma lem5299673 (x : type1019) (s : real -> Prop) (l : real) : (term682 x s l) = (term694 x s l).
Proof. exact (EQ_MP (@lem5299672 x s l) (@lem5299657 x s l)). Qed.
Lemma lem5299674 (x : type1019) (s : real -> Prop) (l : real) : (term592 x s l) = (term694 x s l).
Proof. exact (TRANS (@lem5299653 x s l) (@lem5299673 x s l)). Qed.
Lemma lem5299675 (s : real -> Prop) (l : real) : (term307 s l) = (term307 s l).
Proof. exact (eq_refl (term307 s l)). Qed.
Lemma lem5299676 (x : type1019) (s : real -> Prop) (l : real) : (term593 x s l) = (term695 x s l).
Proof. exact (MK_COMB (@lem5299675 s l) (@lem5299674 x s l)). Qed.
Lemma lem5299678 {A : Type'} (P : Prop) (Q : A -> Prop) : (term632 A P Q) = (term633 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5299679 (P : Prop) (Q : real -> Prop) : (term634 P Q) = (term635 P Q).
Proof. exact (@lem5299678 real P Q). Qed.
Lemma lem5299680 (x : type1019) (s : real -> Prop) (l : real) : (term696 x s l) = (term697 x s l).
Proof. exact (@lem5299679 (has_inf s l) (term693 x s l)). Qed.
Lemma lem5299681 (x : type1019) (b : real) (s : real -> Prop) (l : real) : (term698 x s l b) = (term691 x b s l).
Proof. exact (eq_refl (term698 x s l b)). Qed.
Lemma lem5299682 (x : type1019) (s : real -> Prop) (l : real) : (term699 x s l) = (term693 x s l).
Proof. exact (fun_ext (fun b : real => @lem5299681 x b s l)). Qed.
Lemma lem5299683 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5299684 (x : type1019) (s : real -> Prop) (l : real) : (term700 x s l) = (term694 x s l).
Proof. exact (MK_COMB (@lem5299683) (@lem5299682 x s l)). Qed.
Lemma lem5299685 (s : real -> Prop) (l : real) : (term307 s l) = (term307 s l).
Proof. exact (eq_refl (term307 s l)). Qed.
Lemma lem5299686 (x : type1019) (s : real -> Prop) (l : real) : (term696 x s l) = (term695 x s l).
Proof. exact (MK_COMB (@lem5299685 s l) (@lem5299684 x s l)). Qed.
Lemma lem5299687 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5299688 (x : type1019) (s : real -> Prop) (l : real) : (term701 x s l) = (term702 x s l).
Proof. exact (MK_COMB (@lem5299687) (@lem5299686 x s l)). Qed.
Lemma lem5299689 (x : type1019) (b : real) (s : real -> Prop) (l : real) : (term698 x s l b) = (term691 x b s l).
Proof. exact (eq_refl (term698 x s l b)). Qed.
Lemma lem5299690 (s : real -> Prop) (l : real) : (term307 s l) = (term307 s l).
Proof. exact (eq_refl (term307 s l)). Qed.
Lemma lem5299691 (x : type1019) (b : real) (s : real -> Prop) (l : real) : (term703 x s l b) = (term704 x b s l).
Proof. exact (MK_COMB (@lem5299690 s l) (@lem5299689 x b s l)). Qed.
Lemma lem5299692 (x : type1019) (s : real -> Prop) (l : real) : (term705 x s l) = (term706 x s l).
Proof. exact (fun_ext (fun b : real => @lem5299691 x b s l)). Qed.
Lemma lem5299693 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5299694 (x : type1019) (s : real -> Prop) (l : real) : (term697 x s l) = (term707 x s l).
Proof. exact (MK_COMB (@lem5299693) (@lem5299692 x s l)). Qed.
Lemma lem5299695 (x : type1019) (s : real -> Prop) (l : real) : ((term696 x s l) = (term697 x s l)) = ((term695 x s l) = (term707 x s l)).
Proof. exact (MK_COMB (@lem5299688 x s l) (@lem5299694 x s l)). Qed.
Lemma lem5299696 (x : type1019) (s : real -> Prop) (l : real) : (term695 x s l) = (term707 x s l).
Proof. exact (EQ_MP (@lem5299695 x s l) (@lem5299680 x s l)). Qed.
Lemma lem5299697 (x : type1019) (s : real -> Prop) (l : real) : (term593 x s l) = (term707 x s l).
Proof. exact (TRANS (@lem5299676 x s l) (@lem5299696 x s l)). Qed.
Lemma lem5299698 (x : type1019) (s : real -> Prop) : (term594 x s) = (term708 x s).
Proof. exact (fun_ext (fun l : real => @lem5299697 x s l)). Qed.
Lemma lem5299699 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5299700 (x : type1019) (s : real -> Prop) : (term448 x s) = (term709 x s).
Proof. exact (MK_COMB (@lem5299699) (@lem5299698 x s)). Qed.
Lemma lem5299701 (x : type1019) : (term450 x) = (term710 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5299700 x s)). Qed.
Lemma lem5299702 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5299703 (x : type1019) : (term452 x) = (term711 x).
Proof. exact (MK_COMB (@lem5299702) (@lem5299701 x)). Qed.
Lemma lem5299720 (x : type1019) (b : real) (s : real -> Prop) (l : real) : (term678 x b s l) = (term712 x b s l).
Proof. exact (@lem19699 (term713 x l b s) (term714 x s l b) (term292 s l)). Qed.
Lemma lem5299723 (s : real -> Prop) : (term66 s) = (term66 s).
Proof. exact (eq_refl (term66 s)). Qed.
Lemma lem5299724 (x : type1019) (b : real) (s : real -> Prop) (l : real) : (term691 x b s l) = (term715 x b s l).
Proof. exact (MK_COMB (@lem5299723 s) (@lem5299720 x b s l)). Qed.
Lemma lem5299731 (x : type1019) (b : real) (s : real -> Prop) (l : real) : (term715 x b s l) = (term716 x b s l).
Proof. exact (@lem19490 (term717 x b s l) (s = (@EMPTY real)) (term718 x b s l)). Qed.
Lemma lem5299732 (x : type1019) (b : real) (s : real -> Prop) (l : real) : (term691 x b s l) = (term716 x b s l).
Proof. exact (TRANS (@lem5299724 x b s l) (@lem5299731 x b s l)). Qed.
Lemma lem5299735 (s : real -> Prop) (l : real) : (term307 s l) = (term307 s l).
Proof. exact (eq_refl (term307 s l)). Qed.
Lemma lem5299736 (x : type1019) (b : real) (s : real -> Prop) (l : real) : (term704 x b s l) = (term719 x b s l).
Proof. exact (MK_COMB (@lem5299735 s l) (@lem5299732 x b s l)). Qed.
Lemma lem5299743 (x : type1019) (b : real) (s : real -> Prop) (l : real) : (term719 x b s l) = (term720 x b s l).
Proof. exact (@lem19490 (term721 x b s l) (has_inf s l) (term722 x b s l)). Qed.
Lemma lem5299744 (x : type1019) (b : real) (s : real -> Prop) (l : real) : (term704 x b s l) = (term720 x b s l).
Proof. exact (TRANS (@lem5299736 x b s l) (@lem5299743 x b s l)). Qed.
Lemma lem5299745 (x : type1019) (s : real -> Prop) (l : real) : (term706 x s l) = (term723 x s l).
Proof. exact (fun_ext (fun b : real => @lem5299744 x b s l)). Qed.
Lemma lem5299746 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5299747 (x : type1019) (s : real -> Prop) (l : real) : (term707 x s l) = (term724 x s l).
Proof. exact (MK_COMB (@lem5299746) (@lem5299745 x s l)). Qed.
Lemma lem5299748 (x : type1019) (s : real -> Prop) : (term708 x s) = (term725 x s).
Proof. exact (fun_ext (fun l : real => @lem5299747 x s l)). Qed.
Lemma lem5299749 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5299750 (x : type1019) (s : real -> Prop) : (term709 x s) = (term726 x s).
Proof. exact (MK_COMB (@lem5299749) (@lem5299748 x s)). Qed.
Lemma lem5299751 (x : type1019) : (term710 x) = (term727 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5299750 x s)). Qed.
Lemma lem5299752 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5299753 (x : type1019) : (term711 x) = (term728 x).
Proof. exact (MK_COMB (@lem5299752) (@lem5299751 x)). Qed.
Lemma lem5299754 (x : type1019) : (term452 x) = (term728 x).
Proof. exact (TRANS (@lem5299703 x) (@lem5299753 x)). Qed.
Lemma lem5299755 (x : type1019) (b : type1021) (h1 : term573 x b) : term728 x.
Proof. exact (EQ_MP (@lem5299754 x) (@lem5299098 x b h1)). Qed.
Lemma lem5299877 (s : real -> Prop) (l : real) : (term37 s l) = (term37 s l).
Proof. exact (eq_refl (term37 s l)). Qed.
Lemma lem5299878 (s : real -> Prop) : (term39 s) = (term39 s).
Proof. exact (fun_ext (fun l : real => @lem5299877 s l)). Qed.
Lemma lem5299879 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5299881 (s : real -> Prop) : (term40 s) = (term40 s).
Proof. exact (MK_COMB (@lem5299879) (@lem5299878 s)). Qed.
Lemma lem5299882 (s : real -> Prop) (l : real) (h1 : term221 s l) : term40 s.
Proof. exact (EQ_MP (@lem5299881 s) (@lem5299106 s l h1)). Qed.
Lemma lem5299894 (s : real -> Prop) (l : real) (x : real) : (term44 s l x) = (term44 s l x).
Proof. exact (eq_refl (term44 s l x)). Qed.
Lemma lem5299895 (s : real -> Prop) (l : real) : (term54 s l) = (term54 s l).
Proof. exact (fun_ext (fun x : real => @lem5299894 s l x)). Qed.
Lemma lem5299896 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5299898 (s : real -> Prop) (l : real) : (term55 s l) = (term55 s l).
Proof. exact (MK_COMB (@lem5299896) (@lem5299895 s l)). Qed.
Lemma lem5299899 (s : real -> Prop) (l : real) (h1 : term221 s l) : term55 s l.
Proof. exact (EQ_MP (@lem5299898 s l) (@lem5299107 s l h1)). Qed.
Lemma lem5299909 (_69363 : real -> Prop) (x : type1019) (b : type1021) (h1 : term573 x b) : term729 b _69363.
Proof. exact (@lem5299356 x b h1 _69363). Qed.
Lemma lem5299910 (b : type1021) (_69363 : real -> Prop) : (term729 b _69363) = (term660 b _69363).
Proof. exact (eq_refl (term729 b _69363)). Qed.
Lemma lem5299911 (_69363 : real -> Prop) (x : type1019) (b : type1021) (h1 : term573 x b) : term660 b _69363.
Proof. exact (EQ_MP (@lem5299910 b _69363) (@lem5299909 _69363 x b h1)). Qed.
Lemma lem5299912 (_69363 : real -> Prop) (_69364 : real) (x : type1019) (b : type1021) (h1 : term573 x b) : term730 b _69363 _69364.
Proof. exact (@lem5299911 _69363 x b h1 _69364). Qed.
Lemma lem5299913 (b : type1021) (_69363 : real -> Prop) (_69364 : real) : (term730 b _69363 _69364) = (term658 b _69363 _69364).
Proof. exact (eq_refl (term730 b _69363 _69364)). Qed.
Lemma lem5299914 (_69363 : real -> Prop) (_69364 : real) (x : type1019) (b : type1021) (h1 : term573 x b) : term658 b _69363 _69364.
Proof. exact (EQ_MP (@lem5299913 b _69363 _69364) (@lem5299912 _69363 _69364 x b h1)). Qed.
Lemma lem5299915 (_69363 : real -> Prop) (_69364 : real) (_69365 : real) (x : type1019) (b : type1021) (h1 : term573 x b) : term731 b _69363 _69364 _69365.
Proof. exact (@lem5299914 _69363 _69364 x b h1 _69365). Qed.
Lemma lem5299916 (b : type1021) (_69365 : real) (_69363 : real -> Prop) (_69364 : real) : (term731 b _69363 _69364 _69365) = (term656 b _69365 _69363 _69364).
Proof. exact (eq_refl (term731 b _69363 _69364 _69365)). Qed.
Lemma lem5299917 (_69365 : real) (_69363 : real -> Prop) (_69364 : real) (x : type1019) (b : type1021) (h1 : term573 x b) : term656 b _69365 _69363 _69364.
Proof. exact (EQ_MP (@lem5299916 b _69365 _69363 _69364) (@lem5299915 _69363 _69364 _69365 x b h1)). Qed.
Lemma lem5299927 (_69369 : real -> Prop) (x : type1019) (b : type1021) (h1 : term573 x b) : term729 b _69369.
Proof. exact (@lem5299612 x b h1 _69369). Qed.
Lemma lem5299928 (b : type1021) (_69369 : real -> Prop) : (term729 b _69369) = (term660 b _69369).
Proof. exact (eq_refl (term729 b _69369)). Qed.
Lemma lem5299929 (_69369 : real -> Prop) (x : type1019) (b : type1021) (h1 : term573 x b) : term660 b _69369.
Proof. exact (EQ_MP (@lem5299928 b _69369) (@lem5299927 _69369 x b h1)). Qed.
Lemma lem5299930 (_69369 : real -> Prop) (_69370 : real) (x : type1019) (b : type1021) (h1 : term573 x b) : term730 b _69369 _69370.
Proof. exact (@lem5299929 _69369 x b h1 _69370). Qed.
Lemma lem5299931 (b : type1021) (_69369 : real -> Prop) (_69370 : real) : (term730 b _69369 _69370) = (term658 b _69369 _69370).
Proof. exact (eq_refl (term730 b _69369 _69370)). Qed.
Lemma lem5299932 (_69369 : real -> Prop) (_69370 : real) (x : type1019) (b : type1021) (h1 : term573 x b) : term658 b _69369 _69370.
Proof. exact (EQ_MP (@lem5299931 b _69369 _69370) (@lem5299930 _69369 _69370 x b h1)). Qed.
Lemma lem5299933 (_69369 : real -> Prop) (_69370 : real) (_69371 : real) (x : type1019) (b : type1021) (h1 : term573 x b) : term731 b _69369 _69370 _69371.
Proof. exact (@lem5299932 _69369 _69370 x b h1 _69371). Qed.
Lemma lem5299934 (b : type1021) (_69371 : real) (_69369 : real -> Prop) (_69370 : real) : (term731 b _69369 _69370 _69371) = (term656 b _69371 _69369 _69370).
Proof. exact (eq_refl (term731 b _69369 _69370 _69371)). Qed.
Lemma lem5299935 (_69371 : real) (_69369 : real -> Prop) (_69370 : real) (x : type1019) (b : type1021) (h1 : term573 x b) : term656 b _69371 _69369 _69370.
Proof. exact (EQ_MP (@lem5299934 b _69371 _69369 _69370) (@lem5299933 _69369 _69370 _69371 x b h1)). Qed.
Lemma lem5299936 (_69372 : real) (s : real -> Prop) (x' : real -> real) (h1 : term137 s x') : term732 s x' _69372.
Proof. exact (@lem5299627 s x' h1 _69372). Qed.
Lemma lem5299937 (s : real -> Prop) (x' : real -> real) (_69372 : real) : (term732 s x' _69372) = (term133 s x' _69372).
Proof. exact (eq_refl (term732 s x' _69372)). Qed.
Lemma lem5299938 (_69372 : real) (s : real -> Prop) (x' : real -> real) (h1 : term137 s x') : term133 s x' _69372.
Proof. exact (EQ_MP (@lem5299937 s x' _69372) (@lem5299936 _69372 s x' h1)). Qed.
Lemma lem5299939 (_69373 : real -> Prop) (x : type1019) (b : type1021) (h1 : term573 x b) : term733 x _69373.
Proof. exact (@lem5299755 x b h1 _69373). Qed.
Lemma lem5299940 (x : type1019) (_69373 : real -> Prop) : (term733 x _69373) = (term726 x _69373).
Proof. exact (eq_refl (term733 x _69373)). Qed.
Lemma lem5299941 (_69373 : real -> Prop) (x : type1019) (b : type1021) (h1 : term573 x b) : term726 x _69373.
Proof. exact (EQ_MP (@lem5299940 x _69373) (@lem5299939 _69373 x b h1)). Qed.
Lemma lem5299942 (_69373 : real -> Prop) (_69374 : real) (x : type1019) (b : type1021) (h1 : term573 x b) : term734 x _69373 _69374.
Proof. exact (@lem5299941 _69373 x b h1 _69374). Qed.
Lemma lem5299943 (x : type1019) (_69373 : real -> Prop) (_69374 : real) : (term734 x _69373 _69374) = (term724 x _69373 _69374).
Proof. exact (eq_refl (term734 x _69373 _69374)). Qed.
Lemma lem5299944 (_69373 : real -> Prop) (_69374 : real) (x : type1019) (b : type1021) (h1 : term573 x b) : term724 x _69373 _69374.
Proof. exact (EQ_MP (@lem5299943 x _69373 _69374) (@lem5299942 _69373 _69374 x b h1)). Qed.
Lemma lem5299945 (_69373 : real -> Prop) (_69374 : real) (_69375 : real) (x : type1019) (b : type1021) (h1 : term573 x b) : term735 x _69373 _69374 _69375.
Proof. exact (@lem5299944 _69373 _69374 x b h1 _69375). Qed.
Lemma lem5299946 (x : type1019) (_69375 : real) (_69373 : real -> Prop) (_69374 : real) : (term735 x _69373 _69374 _69375) = (term720 x _69375 _69373 _69374).
Proof. exact (eq_refl (term735 x _69373 _69374 _69375)). Qed.
Lemma lem5299947 (_69375 : real) (_69373 : real -> Prop) (_69374 : real) (x : type1019) (b : type1021) (h1 : term573 x b) : term720 x _69375 _69373 _69374.
Proof. exact (EQ_MP (@lem5299946 x _69375 _69373 _69374) (@lem5299945 _69373 _69374 _69375 x b h1)). Qed.
Lemma lem5299957 (_69379 : real) (s : real -> Prop) (l : real) (h1 : term221 s l) : term736 s _69379.
Proof. exact (@lem5299882 s l h1 _69379). Qed.
Lemma lem5299958 (s : real -> Prop) (_69379 : real) : (term736 s _69379) = (term37 s _69379).
Proof. exact (eq_refl (term736 s _69379)). Qed.
Lemma lem5299960 (_69380 : real) (s : real -> Prop) (l : real) (h1 : term221 s l) : term737 s l _69380.
Proof. exact (@lem5299899 s l h1 _69380). Qed.
Lemma lem5299961 (s : real -> Prop) (l : real) (_69380 : real) : (term737 s l _69380) = (term44 s l _69380).
Proof. exact (eq_refl (term737 s l _69380)). Qed.
Lemma lem5299971 (_69371 : real) (_69369 : real -> Prop) (_69370 : real) (x : type1019) (b : type1021) (h1 : term573 x b) : term654 b _69371 _69369 _69370.
Proof. exact (proj2 (@lem5299935 _69371 _69369 _69370 x b h1)). Qed.
Lemma lem5299984 (l : real) (s : real -> Prop) (x' : real -> real) (h1 : term189 l s x') : has_inf s l.
Proof. exact (proj1 (@lem5299099 l s x' h1)). Qed.
Lemma lem5299986 (s : real -> Prop) (h1 : s = (@EMPTY real)) : s = (@EMPTY real).
Proof. exact (h1). Qed.
Lemma lem5300042 (_69372 : real) (s : real -> Prop) (x' : real -> real) (h1 : term137 s x') : term738 x' _69372.
Proof. exact (proj2 (@lem5299938 _69372 s x' h1)). Qed.
Lemma lem5300058 (_69369 : real -> Prop) (_69370 : real) (_69371 : real) (x : type1019) (b : type1021) (h1 : term573 x b) : term739 b _69369 _69370 _69371.
Proof. exact (proj1 (@lem5299971 _69371 _69369 _69370 x b h1)). Qed.
Lemma lem5300096 (s : real -> Prop) (l : real) (h1 : term221 s l) : term70 s.
Proof. exact (proj1 (@lem5299105 s l h1)). Qed.
Lemma lem5300102 (_69380 : real) (s : real -> Prop) (l : real) (h1 : term221 s l) : term44 s l _69380.
Proof. exact (EQ_MP (@lem5299961 s l _69380) (@lem5299960 _69380 s l h1)). Qed.
Lemma lem5300138 (_69375 : real) (_69373 : real -> Prop) (_69374 : real) (x : type1019) (b : type1021) (h1 : term573 x b) : term740 x _69375 _69373 _69374.
Proof. exact (proj1 (@lem5299947 _69375 _69373 _69374 x b h1)). Qed.
Lemma lem5300152 (_69375 : real) (_69373 : real -> Prop) (_69374 : real) (x : type1019) (b : type1021) (h1 : term573 x b) : term741 x _69375 _69373 _69374.
Proof. exact (proj2 (@lem5299947 _69375 _69373 _69374 x b h1)). Qed.
Lemma lem5300167 (l : real) : (term742 l) = (term742 l).
Proof. exact (eq_refl (term742 l)). Qed.
Lemma lem5300168 (l : real) (s : real -> Prop) (h1 : s = (@EMPTY real)) : (term743 l s) = (term744 l).
Proof. exact (MK_COMB (@lem5300167 l) (@lem5299986 s h1)). Qed.
Lemma lem5300169 (l : real) : (term744 l) = (has_inf (@EMPTY real) l).
Proof. exact (eq_refl (term744 l)). Qed.
Lemma lem5300170 (l : real) (s : real -> Prop) : (term745 l s) = (term745 l s).
Proof. exact (eq_refl (term745 l s)). Qed.
Lemma lem5300171 (s : real -> Prop) (l : real) : ((term743 l s) = (term744 l)) = ((term743 l s) = (has_inf (@EMPTY real) l)).
Proof. exact (MK_COMB (@lem5300170 l s) (@lem5300169 l)). Qed.
Lemma lem5300172 (s : real -> Prop) (l : real) : (term743 l s) = (has_inf s l).
Proof. exact (eq_refl (term743 l s)). Qed.
Lemma lem5300173 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5300174 (s : real -> Prop) (l : real) : (term745 l s) = (term22 s l).
Proof. exact (MK_COMB (@lem5300173) (@lem5300172 s l)). Qed.
Lemma lem5300175 (l : real) : (has_inf (@EMPTY real) l) = (has_inf (@EMPTY real) l).
Proof. exact (eq_refl (has_inf (@EMPTY real) l)). Qed.
Lemma lem5300176 (s : real -> Prop) (l : real) : ((term743 l s) = (has_inf (@EMPTY real) l)) = ((has_inf s l) = (has_inf (@EMPTY real) l)).
Proof. exact (MK_COMB (@lem5300174 s l) (@lem5300175 l)). Qed.
Lemma lem5300177 (s : real -> Prop) (l : real) : ((term743 l s) = (term744 l)) = ((has_inf s l) = (has_inf (@EMPTY real) l)).
Proof. exact (TRANS (@lem5300171 s l) (@lem5300176 s l)). Qed.
Lemma lem5300178 (l : real) (s : real -> Prop) (h1 : s = (@EMPTY real)) : (has_inf s l) = (has_inf (@EMPTY real) l).
Proof. exact (EQ_MP (@lem5300177 s l) (@lem5300168 l s h1)). Qed.
Lemma lem5300193 (_69364 : real) (_69363 : real -> Prop) (x : type1019) (b : type1021) (h1 : term573 x b) : term746 _69364 _69363.
Proof. exact (proj1 (@lem5299917 (@el real) _69363 _69364 x b h1)). Qed.
Lemma lem5300357 (l : real) (x' : real -> real) (s : real -> Prop) (h1 : term189 l s x') (h2 : s = (@EMPTY real)) : has_inf (@EMPTY real) l.
Proof. exact (EQ_MP (@lem5300178 l s h2) (@lem5299984 l s x' h1)). Qed.
Lemma lem5300358 (l : real) (x' : real -> real) (s : real -> Prop) (h1 : term189 l s x') (h2 : s = (@EMPTY real)) : term747 l.
Proof. exact (fun h0 : term748 l => @lem5300357 l x' s h1 h2). Qed.
Lemma lem5300360 (p : Prop) : (term749 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5300361 (l : real) : (term747 l) = (has_inf (@EMPTY real) l).
Proof. exact (@lem5300360 (has_inf (@EMPTY real) l)). Qed.
Lemma lem5300362 (l : real) (x' : real -> real) (s : real -> Prop) (h1 : term189 l s x') (h2 : s = (@EMPTY real)) : has_inf (@EMPTY real) l.
Proof. exact (EQ_MP (@lem5300361 l) (@lem5300358 l x' s h1 h2)). Qed.
Lemma lem5300364 (x : real -> Prop) : x = x.
Proof. exact (@lem21386 (real -> Prop) x). Qed.
Lemma lem5300365 : (@EMPTY real) = (@EMPTY real).
Proof. exact (@lem5300364 (@EMPTY real)). Qed.
Lemma lem5300366 : term750.
Proof. exact (fun h0 : term751 => @lem5300365). Qed.
Lemma lem5300368 (p : Prop) : (term749 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5300369 : term750 = ((@EMPTY real) = (@EMPTY real)).
Proof. exact (@lem5300368 ((@EMPTY real) = (@EMPTY real))). Qed.
Lemma lem5300370 : (@EMPTY real) = (@EMPTY real).
Proof. exact (EQ_MP (@lem5300369) (@lem5300366)). Qed.
Lemma lem5300372 (a : Prop) (b : Prop) : (term752 a b) = (term753 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem5300373 (_69364 : real) (_69363 : real -> Prop) : (term746 _69364 _69363) = (term754 _69364 _69363).
Proof. exact (@lem5300372 (has_inf _69363 _69364) (_69363 = (@EMPTY real))). Qed.
Lemma lem5300375 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5300376 (_69364 : real) (_69363 : real -> Prop) : (term754 _69364 _69363) = (term755 _69364 _69363).
Proof. exact (@lem5300375 (term756 _69364 _69363)). Qed.
Lemma lem5300377 (_69364 : real) (_69363 : real -> Prop) : (term746 _69364 _69363) = (term755 _69364 _69363).
Proof. exact (TRANS (@lem5300373 _69364 _69363) (@lem5300376 _69364 _69363)). Qed.
Lemma lem5300379 (l : real) (x' : real -> real) (s : real -> Prop) (h1 : term189 l s x') (h2 : s = (@EMPTY real)) : term757 l.
Proof. exact (conj (@lem5300362 l x' s h1 h2) (@lem5300370)). Qed.
Lemma lem5300381 (_69364 : real) (_69363 : real -> Prop) (x : type1019) (b : type1021) (h1 : term573 x b) : term755 _69364 _69363.
Proof. exact (EQ_MP (@lem5300377 _69364 _69363) (@lem5300193 _69364 _69363 x b h1)). Qed.
Lemma lem5300382 (l : real) (x : type1019) (b : type1021) (h1 : term573 x b) : term758 l.
Proof. exact (@lem5300381 l (@EMPTY real) x b h1). Qed.
Lemma lem5300385 (x : type1019) (b : type1021) (l : real) (x' : real -> real) (s : real -> Prop) (h1 : term573 x b) (h2 : term189 l s x') (h3 : s = (@EMPTY real)) : False.
Proof. exact (@lem5300382 l x b h1 (@lem5300379 l x' s h2 h3)). Qed.
Lemma lem5300386 (x : type1019) (b : type1021) (l : real) (x' : real -> real) (s : real -> Prop) (h1 : term573 x b) (h2 : term189 l s x') (h3 : s = (@EMPTY real)) : term759.
Proof. exact (fun h0 : ~ False => @lem5300385 x b l x' s h1 h2 h3). Qed.
Lemma lem5300388 (p : Prop) : (term749 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5300389 : term759 = False.
Proof. exact (@lem5300388 False). Qed.
Lemma lem5300506 (l : real) (s : real -> Prop) (x' : real -> real) (h1 : term189 l s x') : has_inf s l.
Proof. exact (proj1 (@lem5299099 l s x' h1)). Qed.
Lemma lem5300507 (l : real) (s : real -> Prop) (x' : real -> real) (h1 : term189 l s x') : term760 s l.
Proof. exact (fun h0 : term37 s l => @lem5300506 l s x' h1). Qed.
Lemma lem5300509 (p : Prop) : (term749 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5300510 (s : real -> Prop) (l : real) : (term760 s l) = (has_inf s l).
Proof. exact (@lem5300509 (has_inf s l)). Qed.
Lemma lem5300511 (l : real) (s : real -> Prop) (x' : real -> real) (h1 : term189 l s x') : has_inf s l.
Proof. exact (EQ_MP (@lem5300510 s l) (@lem5300507 l s x' h1)). Qed.
Lemma lem5300513 (_69372 : real) (s : real -> Prop) (x' : real -> real) (h1 : term137 s x') : term761 x' _69372 s.
Proof. exact (proj1 (@lem5299938 _69372 s x' h1)). Qed.
Lemma lem5300514 (b : type1021) (l : real) (s : real -> Prop) (x' : real -> real) (h1 : term137 s x') : term762 x' b l s.
Proof. exact (@lem5300513 (b s l) s x' h1). Qed.
Lemma lem5300515 (b : type1021) (l : real) (s : real -> Prop) (x' : real -> real) (h1 : term137 s x') : term763 x' b l s.
Proof. exact (fun h0 : term764 x' b l s => @lem5300514 b l s x' h1). Qed.
Lemma lem5300517 (p : Prop) : (term749 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5300518 (x' : real -> real) (b : type1021) (l : real) (s : real -> Prop) : (term763 x' b l s) = (term762 x' b l s).
Proof. exact (@lem5300517 (term762 x' b l s)). Qed.
Lemma lem5300519 (b : type1021) (l : real) (s : real -> Prop) (x' : real -> real) (h1 : term137 s x') : term762 x' b l s.
Proof. exact (EQ_MP (@lem5300518 x' b l s) (@lem5300515 b l s x' h1)). Qed.
Lemma lem5300525 (q : Prop) (p : Prop) (r : Prop) : (term765 p q r) = (term765 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5300526 (b : type1021) (_69369 : real -> Prop) (_69370 : real) (_69371 : real) : (term739 b _69369 _69370 _69371) = (term766 b _69369 _69370 _69371).
Proof. exact (@lem5300525 (term767 _69371 _69369) (term37 _69369 _69370) (term768 b _69369 _69370 _69371)). Qed.
Lemma lem5300540 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5300541 (b : type1021) (_69371 : real) (_69369 : real -> Prop) (_69370 : real) : (term769 b _69369 _69370 _69371) = (term770 b _69371 _69369 _69370).
Proof. exact (@lem5300540 (term768 b _69369 _69370 _69371) (term37 _69369 _69370)). Qed.
Lemma lem5300547 (_69371 : real) (_69369 : real -> Prop) : (term771 _69371 _69369) = (term771 _69371 _69369).
Proof. exact (eq_refl (term771 _69371 _69369)). Qed.
Lemma lem5300548 (b : type1021) (_69371 : real) (_69369 : real -> Prop) (_69370 : real) : (term766 b _69369 _69370 _69371) = (term772 b _69371 _69369 _69370).
Proof. exact (MK_COMB (@lem5300547 _69371 _69369) (@lem5300541 b _69371 _69369 _69370)). Qed.
Lemma lem5300552 (q : Prop) (p : Prop) (r : Prop) : (term765 p q r) = (term765 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5300553 (b : type1021) (_69371 : real) (_69369 : real -> Prop) (_69370 : real) : (term772 b _69371 _69369 _69370) = (term773 b _69371 _69369 _69370).
Proof. exact (@lem5300552 (term768 b _69369 _69370 _69371) (term767 _69371 _69369) (term37 _69369 _69370)). Qed.
Lemma lem5300569 (b : type1021) (_69371 : real) (_69369 : real -> Prop) (_69370 : real) : (term766 b _69369 _69370 _69371) = (term773 b _69371 _69369 _69370).
Proof. exact (TRANS (@lem5300548 b _69371 _69369 _69370) (@lem5300553 b _69371 _69369 _69370)). Qed.
Lemma lem5300570 (b : type1021) (_69371 : real) (_69369 : real -> Prop) (_69370 : real) : (term739 b _69369 _69370 _69371) = (term773 b _69371 _69369 _69370).
Proof. exact (TRANS (@lem5300526 b _69369 _69370 _69371) (@lem5300569 b _69371 _69369 _69370)). Qed.
Lemma lem5300571 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5300572 (b : type1021) (_69371 : real) (_69369 : real -> Prop) (_69370 : real) : (term774 b _69369 _69370 _69371) = (term775 b _69371 _69369 _69370).
Proof. exact (MK_COMB (@lem5300571) (@lem5300570 b _69371 _69369 _69370)). Qed.
Lemma lem5300586 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5300587 (_69371 : real) (_69369 : real -> Prop) (_69370 : real) : (term776 _69370 _69371 _69369) = (term777 _69371 _69369 _69370).
Proof. exact (@lem5300586 (term767 _69371 _69369) (term37 _69369 _69370)). Qed.
Lemma lem5300593 (b : type1021) (_69369 : real -> Prop) (_69370 : real) (_69371 : real) : (term778 b _69369 _69370 _69371) = (term778 b _69369 _69370 _69371).
Proof. exact (eq_refl (term778 b _69369 _69370 _69371)). Qed.
Lemma lem5300594 (b : type1021) (_69371 : real) (_69369 : real -> Prop) (_69370 : real) : (term779 b _69370 _69371 _69369) = (term773 b _69371 _69369 _69370).
Proof. exact (MK_COMB (@lem5300593 b _69369 _69370 _69371) (@lem5300587 _69371 _69369 _69370)). Qed.
Lemma lem5300605 (b : type1021) (_69371 : real) (_69369 : real -> Prop) (_69370 : real) : ((term739 b _69369 _69370 _69371) = (term779 b _69370 _69371 _69369)) = ((term773 b _69371 _69369 _69370) = (term773 b _69371 _69369 _69370)).
Proof. exact (MK_COMB (@lem5300572 b _69371 _69369 _69370) (@lem5300594 b _69371 _69369 _69370)). Qed.
Lemma lem5300607 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5300608 (x : Prop) : (x = x) = True.
Proof. exact (@lem5300607 Prop x). Qed.
Lemma lem5300609 (b : type1021) (_69371 : real) (_69369 : real -> Prop) (_69370 : real) : ((term773 b _69371 _69369 _69370) = (term773 b _69371 _69369 _69370)) = True.
Proof. exact (@lem5300608 (term773 b _69371 _69369 _69370)). Qed.
Lemma lem5300610 (b : type1021) (_69370 : real) (_69371 : real) (_69369 : real -> Prop) : ((term739 b _69369 _69370 _69371) = (term779 b _69370 _69371 _69369)) = True.
Proof. exact (TRANS (@lem5300605 b _69371 _69369 _69370) (@lem5300609 b _69371 _69369 _69370)). Qed.
Lemma lem5300611 (b : type1021) (_69370 : real) (_69371 : real) (_69369 : real -> Prop) : True = ((term739 b _69369 _69370 _69371) = (term779 b _69370 _69371 _69369)).
Proof. exact (SYM (@lem5300610 b _69370 _69371 _69369)). Qed.
Lemma lem5300612 (b : type1021) (_69370 : real) (_69371 : real) (_69369 : real -> Prop) : (term739 b _69369 _69370 _69371) = (term779 b _69370 _69371 _69369).
Proof. exact (EQ_MP (@lem5300611 b _69370 _69371 _69369) (@lem0)). Qed.
Lemma lem5300613 (_69370 : real) (_69371 : real) (_69369 : real -> Prop) (x : type1019) (b : type1021) (h1 : term573 x b) : term779 b _69370 _69371 _69369.
Proof. exact (EQ_MP (@lem5300612 b _69370 _69371 _69369) (@lem5300058 _69369 _69370 _69371 x b h1)). Qed.
Lemma lem5300615 (b : Prop) (a : Prop) : (a \/ b) = (term780 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5300616 (b : type1021) (_69369 : real -> Prop) (_69370 : real) (_69371 : real) : (term779 b _69370 _69371 _69369) = (term781 b _69369 _69370 _69371).
Proof. exact (@lem5300615 (term776 _69370 _69371 _69369) (term768 b _69369 _69370 _69371)). Qed.
Lemma lem5300618 (a : Prop) (b : Prop) : (term782 a b) = (term783 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5300619 (_69370 : real) (_69371 : real) (_69369 : real -> Prop) : (term784 _69370 _69371 _69369) = (term785 _69370 _69371 _69369).
Proof. exact (@lem5300618 (term37 _69369 _69370) (term767 _69371 _69369)). Qed.
Lemma lem5300621 (a : Prop) : (term786 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5300622 (_69369 : real -> Prop) (_69370 : real) : (term787 _69369 _69370) = (has_inf _69369 _69370).
Proof. exact (@lem5300621 (has_inf _69369 _69370)). Qed.
Lemma lem5300623 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5300624 (_69369 : real -> Prop) (_69370 : real) : (term788 _69369 _69370) = (term171 _69369 _69370).
Proof. exact (MK_COMB (@lem5300623) (@lem5300622 _69369 _69370)). Qed.
Lemma lem5300626 (a : Prop) : (term786 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5300627 (_69371 : real) (_69369 : real -> Prop) : (term789 _69371 _69369) = (@IN real _69371 _69369).
Proof. exact (@lem5300626 (@IN real _69371 _69369)). Qed.
Lemma lem5300628 (_69370 : real) (_69371 : real) (_69369 : real -> Prop) : (term785 _69370 _69371 _69369) = (term790 _69370 _69371 _69369).
Proof. exact (MK_COMB (@lem5300624 _69369 _69370) (@lem5300627 _69371 _69369)). Qed.
Lemma lem5300629 (_69370 : real) (_69371 : real) (_69369 : real -> Prop) : (term784 _69370 _69371 _69369) = (term790 _69370 _69371 _69369).
Proof. exact (TRANS (@lem5300619 _69370 _69371 _69369) (@lem5300628 _69370 _69371 _69369)). Qed.
Lemma lem5300630 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5300631 (_69370 : real) (_69371 : real) (_69369 : real -> Prop) : (term791 _69370 _69371 _69369) = (term792 _69370 _69371 _69369).
Proof. exact (MK_COMB (@lem5300630) (@lem5300629 _69370 _69371 _69369)). Qed.
Lemma lem5300632 (b : type1021) (_69369 : real -> Prop) (_69370 : real) (_69371 : real) : (term768 b _69369 _69370 _69371) = (term768 b _69369 _69370 _69371).
Proof. exact (eq_refl (term768 b _69369 _69370 _69371)). Qed.
Lemma lem5300633 (b : type1021) (_69369 : real -> Prop) (_69370 : real) (_69371 : real) : (term781 b _69369 _69370 _69371) = (term793 b _69369 _69370 _69371).
Proof. exact (MK_COMB (@lem5300631 _69370 _69371 _69369) (@lem5300632 b _69369 _69370 _69371)). Qed.
Lemma lem5300634 (b : type1021) (_69369 : real -> Prop) (_69370 : real) (_69371 : real) : (term779 b _69370 _69371 _69369) = (term793 b _69369 _69370 _69371).
Proof. exact (TRANS (@lem5300616 b _69369 _69370 _69371) (@lem5300633 b _69369 _69370 _69371)). Qed.
Lemma lem5300636 (b : type1021) (l : real) (s : real -> Prop) (x' : real -> real) (h1 : term137 s x') (h2 : term189 l s x') : term794 x' b l s.
Proof. exact (conj (@lem5300511 l s x' h2) (@lem5300519 b l s x' h1)). Qed.
Lemma lem5300638 (_69369 : real -> Prop) (_69370 : real) (_69371 : real) (x : type1019) (b : type1021) (h1 : term573 x b) : term793 b _69369 _69370 _69371.
Proof. exact (EQ_MP (@lem5300634 b _69369 _69370 _69371) (@lem5300613 _69370 _69371 _69369 x b h1)). Qed.
Lemma lem5300639 (x' : real -> real) (s : real -> Prop) (l : real) (x : type1019) (b : type1021) (h1 : term573 x b) : term795 x' b s l.
Proof. exact (@lem5300638 s l (term796 x' b s l) x b h1). Qed.
Lemma lem5300642 (x : type1019) (b : type1021) (l : real) (s : real -> Prop) (x' : real -> real) (h1 : term137 s x') (h2 : term573 x b) (h3 : term189 l s x') : term797 x' b s l.
Proof. exact (@lem5300639 x' s l x b h2 (@lem5300636 b l s x' h1 h3)). Qed.
Lemma lem5300643 (x : type1019) (b : type1021) (l : real) (s : real -> Prop) (x' : real -> real) (h1 : term137 s x') (h2 : term573 x b) (h3 : term189 l s x') : term798 x' b s l.
Proof. exact (fun h0 : term799 x' b s l => @lem5300642 x b l s x' h1 h2 h3). Qed.
Lemma lem5300645 (p : Prop) : (term749 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5300646 (x' : real -> real) (b : type1021) (s : real -> Prop) (l : real) : (term798 x' b s l) = (term797 x' b s l).
Proof. exact (@lem5300645 (term797 x' b s l)). Qed.
Lemma lem5300647 (x : type1019) (b : type1021) (l : real) (s : real -> Prop) (x' : real -> real) (h1 : term137 s x') (h2 : term573 x b) (h3 : term189 l s x') : term797 x' b s l.
Proof. exact (EQ_MP (@lem5300646 x' b s l) (@lem5300643 x b l s x' h1 h2 h3)). Qed.
Lemma lem5300650 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5300652 (x' : real -> real) (_69372 : real) : (term738 x' _69372) = (term800 x' _69372).
Proof. exact (@lem5300650 (term801 x' _69372)). Qed.
Lemma lem5300655 (_69372 : real) (s : real -> Prop) (x' : real -> real) (h1 : term137 s x') : term800 x' _69372.
Proof. exact (EQ_MP (@lem5300652 x' _69372) (@lem5300042 _69372 s x' h1)). Qed.
Lemma lem5300656 (b : type1021) (l : real) (s : real -> Prop) (x' : real -> real) (h1 : term137 s x') : term802 x' b s l.
Proof. exact (@lem5300655 (b s l) s x' h1). Qed.
Lemma lem5300659 (x : type1019) (b : type1021) (l : real) (s : real -> Prop) (x' : real -> real) (h1 : term137 s x') (h2 : term573 x b) (h3 : term189 l s x') : False.
Proof. exact (@lem5300656 b l s x' h1 (@lem5300647 x b l s x' h1 h2 h3)). Qed.
Lemma lem5300660 (x : type1019) (b : type1021) (l : real) (s : real -> Prop) (x' : real -> real) (h1 : term137 s x') (h2 : term573 x b) (h3 : term189 l s x') : term759.
Proof. exact (fun h0 : ~ False => @lem5300659 x b l s x' h1 h2 h3). Qed.
Lemma lem5300662 (p : Prop) : (term749 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5300663 : term759 = False.
Proof. exact (@lem5300662 False). Qed.
Lemma lem5300664 (x : type1019) (b : type1021) (l : real) (s : real -> Prop) (x' : real -> real) (h1 : term137 s x') (h2 : term573 x b) (h3 : term189 l s x') : False.
Proof. exact (EQ_MP (@lem5300663) (@lem5300660 x b l s x' h1 h2 h3)). Qed.
Lemma lem5300772 (_69379 : real) (s : real -> Prop) (l : real) (h1 : term221 s l) : term37 s _69379.
Proof. exact (EQ_MP (@lem5299958 s _69379) (@lem5299957 _69379 s l h1)). Qed.
Lemma lem5300773 (s : real -> Prop) (l : real) (h1 : term221 s l) : term803 s.
Proof. exact (@lem5300772 (inf s) s l h1). Qed.
Lemma lem5300774 (s : real -> Prop) (l : real) (h1 : term221 s l) : term804 s.
Proof. exact (fun h0 : term805 s => @lem5300773 s l h1). Qed.
Lemma lem5300776 (p : Prop) : (term806 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5300777 (s : real -> Prop) : (term804 s) = (term803 s).
Proof. exact (@lem5300776 (term805 s)). Qed.
Lemma lem5300778 (s : real -> Prop) (l : real) (h1 : term221 s l) : term803 s.
Proof. exact (EQ_MP (@lem5300777 s) (@lem5300774 s l h1)). Qed.
Lemma lem5300780 (_69379 : real) (s : real -> Prop) (l : real) (h1 : term221 s l) : term37 s _69379.
Proof. exact (EQ_MP (@lem5299958 s _69379) (@lem5299957 _69379 s l h1)). Qed.
Lemma lem5300781 (s : real -> Prop) (l : real) (h1 : term221 s l) : term803 s.
Proof. exact (@lem5300780 (inf s) s l h1). Qed.
Lemma lem5300782 (s : real -> Prop) (l : real) (h1 : term221 s l) : term804 s.
Proof. exact (fun h0 : term805 s => @lem5300781 s l h1). Qed.
Lemma lem5300784 (p : Prop) : (term806 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5300785 (s : real -> Prop) : (term804 s) = (term803 s).
Proof. exact (@lem5300784 (term805 s)). Qed.
Lemma lem5300786 (s : real -> Prop) (l : real) (h1 : term221 s l) : term803 s.
Proof. exact (EQ_MP (@lem5300785 s) (@lem5300782 s l h1)). Qed.
Lemma lem5300789 (s : real -> Prop) (h1 : term70 s) : term70 s.
Proof. exact (h1). Qed.
Lemma lem5300790 (s : real -> Prop) (h1 : term70 s) : term807 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5300789 s h1). Qed.
Lemma lem5300792 (p : Prop) : (term806 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5300793 (s : real -> Prop) : (term807 s) = (term70 s).
Proof. exact (@lem5300792 (s = (@EMPTY real))). Qed.
Lemma lem5300794 (s : real -> Prop) (h1 : term70 s) : term70 s.
Proof. exact (EQ_MP (@lem5300793 s) (@lem5300790 s h1)). Qed.
Lemma lem5300796 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem5300797 (s : real -> Prop) : (inf s) = (inf s).
Proof. exact (@lem5300796 (inf s)). Qed.
Lemma lem5300798 (s : real -> Prop) : term808 s.
Proof. exact (fun h0 : term809 s => @lem5300797 s). Qed.
Lemma lem5300800 (p : Prop) : (term749 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5300801 (s : real -> Prop) : (term808 s) = ((inf s) = (inf s)).
Proof. exact (@lem5300800 ((inf s) = (inf s))). Qed.
Lemma lem5300802 (s : real -> Prop) : (inf s) = (inf s).
Proof. exact (EQ_MP (@lem5300801 s) (@lem5300798 s)). Qed.
Lemma lem5300808 (q : Prop) (p : Prop) (r : Prop) : (term765 p q r) = (term765 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5300809 (x : type1019) (_69375 : real) (_69373 : real -> Prop) (_69374 : real) : (term740 x _69375 _69373 _69374) = (term810 x _69375 _69373 _69374).
Proof. exact (@lem5300808 (_69373 = (@EMPTY real)) (has_inf _69373 _69374) (term717 x _69375 _69373 _69374)). Qed.
Lemma lem5300825 (q : Prop) (p : Prop) (r : Prop) : (term765 p q r) = (term765 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5300826 (x : type1019) (_69375 : real) (_69373 : real -> Prop) (_69374 : real) : (term811 x _69375 _69373 _69374) = (term812 x _69375 _69373 _69374).
Proof. exact (@lem5300825 (term713 x _69374 _69375 _69373) (has_inf _69373 _69374) (term292 _69373 _69374)). Qed.
Lemma lem5300844 (_69373 : real -> Prop) : (term66 _69373) = (term66 _69373).
Proof. exact (eq_refl (term66 _69373)). Qed.
Lemma lem5300845 (x : type1019) (_69375 : real) (_69373 : real -> Prop) (_69374 : real) : (term810 x _69375 _69373 _69374) = (term813 x _69375 _69373 _69374).
Proof. exact (MK_COMB (@lem5300844 _69373) (@lem5300826 x _69375 _69373 _69374)). Qed.
Lemma lem5300856 (x : type1019) (_69375 : real) (_69373 : real -> Prop) (_69374 : real) : (term740 x _69375 _69373 _69374) = (term813 x _69375 _69373 _69374).
Proof. exact (TRANS (@lem5300809 x _69375 _69373 _69374) (@lem5300845 x _69375 _69373 _69374)). Qed.
Lemma lem5300857 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5300858 (x : type1019) (_69375 : real) (_69373 : real -> Prop) (_69374 : real) : (term814 x _69375 _69373 _69374) = (term815 x _69375 _69373 _69374).
Proof. exact (MK_COMB (@lem5300857) (@lem5300856 x _69375 _69373 _69374)). Qed.
Lemma lem5300872 (q : Prop) (p : Prop) (r : Prop) : (term765 p q r) = (term765 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5300873 (_69373 : real -> Prop) (_69374 : real) : (term816 _69373 _69374) = (term817 _69373 _69374).
Proof. exact (@lem5300872 (_69373 = (@EMPTY real)) (has_inf _69373 _69374) (term292 _69373 _69374)). Qed.
Lemma lem5300893 (x : type1019) (_69374 : real) (_69375 : real) (_69373 : real -> Prop) : (term818 x _69374 _69375 _69373) = (term818 x _69374 _69375 _69373).
Proof. exact (eq_refl (term818 x _69374 _69375 _69373)). Qed.
Lemma lem5300894 (x : type1019) (_69375 : real) (_69373 : real -> Prop) (_69374 : real) : (term819 x _69375 _69373 _69374) = (term820 x _69375 _69373 _69374).
Proof. exact (MK_COMB (@lem5300893 x _69374 _69375 _69373) (@lem5300873 _69373 _69374)). Qed.
Lemma lem5300898 (q : Prop) (p : Prop) (r : Prop) : (term765 p q r) = (term765 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5300899 (x : type1019) (_69375 : real) (_69373 : real -> Prop) (_69374 : real) : (term820 x _69375 _69373 _69374) = (term813 x _69375 _69373 _69374).
Proof. exact (@lem5300898 (_69373 = (@EMPTY real)) (term713 x _69374 _69375 _69373) (term821 _69373 _69374)). Qed.
Lemma lem5300929 (x : type1019) (_69375 : real) (_69373 : real -> Prop) (_69374 : real) : (term819 x _69375 _69373 _69374) = (term813 x _69375 _69373 _69374).
Proof. exact (TRANS (@lem5300894 x _69375 _69373 _69374) (@lem5300899 x _69375 _69373 _69374)). Qed.
Lemma lem5300930 (x : type1019) (_69375 : real) (_69373 : real -> Prop) (_69374 : real) : ((term740 x _69375 _69373 _69374) = (term819 x _69375 _69373 _69374)) = ((term813 x _69375 _69373 _69374) = (term813 x _69375 _69373 _69374)).
Proof. exact (MK_COMB (@lem5300858 x _69375 _69373 _69374) (@lem5300929 x _69375 _69373 _69374)). Qed.
Lemma lem5300932 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5300933 (x : Prop) : (x = x) = True.
Proof. exact (@lem5300932 Prop x). Qed.
Lemma lem5300934 (x : type1019) (_69375 : real) (_69373 : real -> Prop) (_69374 : real) : ((term813 x _69375 _69373 _69374) = (term813 x _69375 _69373 _69374)) = True.
Proof. exact (@lem5300933 (term813 x _69375 _69373 _69374)). Qed.
Lemma lem5300935 (x : type1019) (_69375 : real) (_69373 : real -> Prop) (_69374 : real) : ((term740 x _69375 _69373 _69374) = (term819 x _69375 _69373 _69374)) = True.
Proof. exact (TRANS (@lem5300930 x _69375 _69373 _69374) (@lem5300934 x _69375 _69373 _69374)). Qed.
Lemma lem5300936 (x : type1019) (_69375 : real) (_69373 : real -> Prop) (_69374 : real) : True = ((term740 x _69375 _69373 _69374) = (term819 x _69375 _69373 _69374)).
Proof. exact (SYM (@lem5300935 x _69375 _69373 _69374)). Qed.
Lemma lem5300937 (x : type1019) (_69375 : real) (_69373 : real -> Prop) (_69374 : real) : (term740 x _69375 _69373 _69374) = (term819 x _69375 _69373 _69374).
Proof. exact (EQ_MP (@lem5300936 x _69375 _69373 _69374) (@lem0)). Qed.
Lemma lem5300938 (_69375 : real) (_69373 : real -> Prop) (_69374 : real) (x : type1019) (b : type1021) (h1 : term573 x b) : term819 x _69375 _69373 _69374.
Proof. exact (EQ_MP (@lem5300937 x _69375 _69373 _69374) (@lem5300138 _69375 _69373 _69374 x b h1)). Qed.
Lemma lem5300940 (b : Prop) (a : Prop) : (a \/ b) = (term780 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5300941 (x : type1019) (_69374 : real) (_69375 : real) (_69373 : real -> Prop) : (term819 x _69375 _69373 _69374) = (term822 x _69374 _69375 _69373).
Proof. exact (@lem5300940 (term816 _69373 _69374) (term713 x _69374 _69375 _69373)). Qed.
Lemma lem5300943 (a : Prop) (b : Prop) : (term782 a b) = (term783 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5300944 (_69373 : real -> Prop) (_69374 : real) : (term823 _69373 _69374) = (term824 _69373 _69374).
Proof. exact (@lem5300943 (has_inf _69373 _69374) (term825 _69373 _69374)). Qed.
Lemma lem5300946 (a : Prop) (b : Prop) : (term782 a b) = (term783 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5300947 (_69373 : real -> Prop) (_69374 : real) : (term826 _69373 _69374) = (term827 _69373 _69374).
Proof. exact (@lem5300946 (_69373 = (@EMPTY real)) (term292 _69373 _69374)). Qed.
Lemma lem5300949 (a : Prop) : (term786 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5300950 (_69373 : real -> Prop) (_69374 : real) : (term828 _69373 _69374) = ((inf _69373) = _69374).
Proof. exact (@lem5300949 ((inf _69373) = _69374)). Qed.
Lemma lem5300951 (_69373 : real -> Prop) : (term20 _69373) = (term20 _69373).
Proof. exact (eq_refl (term20 _69373)). Qed.
Lemma lem5300952 (_69373 : real -> Prop) (_69374 : real) : (term827 _69373 _69374) = (term829 _69373 _69374).
Proof. exact (MK_COMB (@lem5300951 _69373) (@lem5300950 _69373 _69374)). Qed.
Lemma lem5300953 (_69373 : real -> Prop) (_69374 : real) : (term826 _69373 _69374) = (term829 _69373 _69374).
Proof. exact (TRANS (@lem5300947 _69373 _69374) (@lem5300952 _69373 _69374)). Qed.
Lemma lem5300954 (_69373 : real -> Prop) (_69374 : real) : (term830 _69373 _69374) = (term830 _69373 _69374).
Proof. exact (eq_refl (term830 _69373 _69374)). Qed.
Lemma lem5300955 (_69373 : real -> Prop) (_69374 : real) : (term824 _69373 _69374) = (term831 _69373 _69374).
Proof. exact (MK_COMB (@lem5300954 _69373 _69374) (@lem5300953 _69373 _69374)). Qed.
Lemma lem5300956 (_69373 : real -> Prop) (_69374 : real) : (term823 _69373 _69374) = (term831 _69373 _69374).
Proof. exact (TRANS (@lem5300944 _69373 _69374) (@lem5300955 _69373 _69374)). Qed.
Lemma lem5300957 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5300958 (_69373 : real -> Prop) (_69374 : real) : (term832 _69373 _69374) = (term833 _69373 _69374).
Proof. exact (MK_COMB (@lem5300957) (@lem5300956 _69373 _69374)). Qed.
Lemma lem5300959 (x : type1019) (_69374 : real) (_69375 : real) (_69373 : real -> Prop) : (term713 x _69374 _69375 _69373) = (term713 x _69374 _69375 _69373).
Proof. exact (eq_refl (term713 x _69374 _69375 _69373)). Qed.
Lemma lem5300960 (x : type1019) (_69374 : real) (_69375 : real) (_69373 : real -> Prop) : (term822 x _69374 _69375 _69373) = (term834 x _69374 _69375 _69373).
Proof. exact (MK_COMB (@lem5300958 _69373 _69374) (@lem5300959 x _69374 _69375 _69373)). Qed.
Lemma lem5300961 (x : type1019) (_69374 : real) (_69375 : real) (_69373 : real -> Prop) : (term819 x _69375 _69373 _69374) = (term834 x _69374 _69375 _69373).
Proof. exact (TRANS (@lem5300941 x _69374 _69375 _69373) (@lem5300960 x _69374 _69375 _69373)). Qed.
Lemma lem5300963 (s : real -> Prop) (h1 : term70 s) : term835 s.
Proof. exact (conj (@lem5300794 s h1) (@lem5300802 s)). Qed.
Lemma lem5300964 (s : real -> Prop) (l : real) (h1 : term70 s) (h2 : term221 s l) : term836 s.
Proof. exact (conj (@lem5300786 s l h2) (@lem5300963 s h1)). Qed.
Lemma lem5300966 (_69374 : real) (_69375 : real) (_69373 : real -> Prop) (x : type1019) (b : type1021) (h1 : term573 x b) : term834 x _69374 _69375 _69373.
Proof. exact (EQ_MP (@lem5300961 x _69374 _69375 _69373) (@lem5300938 _69375 _69373 _69374 x b h1)). Qed.
Lemma lem5300967 (_69375 : real) (s : real -> Prop) (x : type1019) (b : type1021) (h1 : term573 x b) : term837 x _69375 s.
Proof. exact (@lem5300966 (inf s) _69375 s x b h1). Qed.
Lemma lem5300970 (_69375 : real) (x : type1019) (b : type1021) (s : real -> Prop) (l : real) (h1 : term70 s) (h2 : term573 x b) (h3 : term221 s l) : term838 x _69375 s.
Proof. exact (@lem5300967 _69375 s x b h2 (@lem5300964 s l h1 h3)). Qed.
Lemma lem5300971 (x : type1019) (b : type1021) (s : real -> Prop) (l : real) (h1 : term70 s) (h2 : term573 x b) (h3 : term221 s l) : term838 x l s.
Proof. exact (@lem5300970 l x b s l h1 h2 h3). Qed.
Lemma lem5300972 (x : type1019) (b : type1021) (s : real -> Prop) (l : real) (h1 : term70 s) (h2 : term573 x b) (h3 : term221 s l) : term839 x l s.
Proof. exact (fun h0 : term840 x l s => @lem5300971 x b s l h1 h2 h3). Qed.
Lemma lem5300974 (p : Prop) : (term749 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5300975 (x : type1019) (l : real) (s : real -> Prop) : (term839 x l s) = (term838 x l s).
Proof. exact (@lem5300974 (term838 x l s)). Qed.
Lemma lem5300976 (x : type1019) (b : type1021) (s : real -> Prop) (l : real) (h1 : term70 s) (h2 : term573 x b) (h3 : term221 s l) : term838 x l s.
Proof. exact (EQ_MP (@lem5300975 x l s) (@lem5300972 x b s l h1 h2 h3)). Qed.
Lemma lem5300982 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5300983 (l : real) (_69380 : real) (s : real -> Prop) : (term44 s l _69380) = (term841 l _69380 s).
Proof. exact (@lem5300982 (real_le l _69380) (term767 _69380 s)). Qed.
Lemma lem5300989 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5300990 (l : real) (_69380 : real) (s : real -> Prop) : (term842 s l _69380) = (term843 l _69380 s).
Proof. exact (MK_COMB (@lem5300989) (@lem5300983 l _69380 s)). Qed.
Lemma lem5300996 (l : real) (_69380 : real) (s : real -> Prop) : (term841 l _69380 s) = (term841 l _69380 s).
Proof. exact (eq_refl (term841 l _69380 s)). Qed.
Lemma lem5300997 (l : real) (_69380 : real) (s : real -> Prop) : ((term44 s l _69380) = (term841 l _69380 s)) = ((term841 l _69380 s) = (term841 l _69380 s)).
Proof. exact (MK_COMB (@lem5300990 l _69380 s) (@lem5300996 l _69380 s)). Qed.
Lemma lem5300999 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5301000 (x : Prop) : (x = x) = True.
Proof. exact (@lem5300999 Prop x). Qed.
Lemma lem5301001 (l : real) (_69380 : real) (s : real -> Prop) : ((term841 l _69380 s) = (term841 l _69380 s)) = True.
Proof. exact (@lem5301000 (term841 l _69380 s)). Qed.
Lemma lem5301002 (l : real) (_69380 : real) (s : real -> Prop) : ((term44 s l _69380) = (term841 l _69380 s)) = True.
Proof. exact (TRANS (@lem5300997 l _69380 s) (@lem5301001 l _69380 s)). Qed.
Lemma lem5301003 (l : real) (_69380 : real) (s : real -> Prop) : True = ((term44 s l _69380) = (term841 l _69380 s)).
Proof. exact (SYM (@lem5301002 l _69380 s)). Qed.
Lemma lem5301004 (l : real) (_69380 : real) (s : real -> Prop) : (term44 s l _69380) = (term841 l _69380 s).
Proof. exact (EQ_MP (@lem5301003 l _69380 s) (@lem0)). Qed.
Lemma lem5301005 (_69380 : real) (s : real -> Prop) (l : real) (h1 : term221 s l) : term841 l _69380 s.
Proof. exact (EQ_MP (@lem5301004 l _69380 s) (@lem5300102 _69380 s l h1)). Qed.
Lemma lem5301007 (b : Prop) (a : Prop) : (a \/ b) = (term780 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5301008 (s : real -> Prop) (l : real) (_69380 : real) : (term841 l _69380 s) = (term844 s l _69380).
Proof. exact (@lem5301007 (term767 _69380 s) (real_le l _69380)). Qed.
Lemma lem5301010 (a : Prop) : (term786 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5301011 (_69380 : real) (s : real -> Prop) : (term789 _69380 s) = (@IN real _69380 s).
Proof. exact (@lem5301010 (@IN real _69380 s)). Qed.
Lemma lem5301012 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5301013 (_69380 : real) (s : real -> Prop) : (term845 _69380 s) = (term846 _69380 s).
Proof. exact (MK_COMB (@lem5301012) (@lem5301011 _69380 s)). Qed.
Lemma lem5301014 (l : real) (_69380 : real) : (real_le l _69380) = (real_le l _69380).
Proof. exact (eq_refl (real_le l _69380)). Qed.
Lemma lem5301015 (s : real -> Prop) (l : real) (_69380 : real) : (term844 s l _69380) = (term13 s l _69380).
Proof. exact (MK_COMB (@lem5301013 _69380 s) (@lem5301014 l _69380)). Qed.
Lemma lem5301016 (s : real -> Prop) (l : real) (_69380 : real) : (term841 l _69380 s) = (term13 s l _69380).
Proof. exact (TRANS (@lem5301008 s l _69380) (@lem5301015 s l _69380)). Qed.
Lemma lem5301019 (_69380 : real) (s : real -> Prop) (l : real) (h1 : term221 s l) : term13 s l _69380.
Proof. exact (EQ_MP (@lem5301016 s l _69380) (@lem5301005 _69380 s l h1)). Qed.
Lemma lem5301020 (x : type1019) (s : real -> Prop) (l : real) (h1 : term221 s l) : term847 x s l.
Proof. exact (@lem5301019 (term848 x s l) s l h1). Qed.
Lemma lem5301023 (x : type1019) (b : type1021) (s : real -> Prop) (l : real) (h1 : term70 s) (h2 : term573 x b) (h3 : term221 s l) : term849 x s l.
Proof. exact (@lem5301020 x s l h3 (@lem5300976 x b s l h1 h2 h3)). Qed.
Lemma lem5301024 (x : type1019) (b : type1021) (s : real -> Prop) (l : real) (h1 : term70 s) (h2 : term573 x b) (h3 : term221 s l) : term850 x s l.
Proof. exact (fun h0 : term851 x s l => @lem5301023 x b s l h1 h2 h3). Qed.
Lemma lem5301026 (p : Prop) : (term749 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5301027 (x : type1019) (s : real -> Prop) (l : real) : (term850 x s l) = (term849 x s l).
Proof. exact (@lem5301026 (term849 x s l)). Qed.
Lemma lem5301028 (x : type1019) (b : type1021) (s : real -> Prop) (l : real) (h1 : term70 s) (h2 : term573 x b) (h3 : term221 s l) : term849 x s l.
Proof. exact (EQ_MP (@lem5301027 x s l) (@lem5301024 x b s l h1 h2 h3)). Qed.
Lemma lem5301030 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem5301031 (s : real -> Prop) : (inf s) = (inf s).
Proof. exact (@lem5301030 (inf s)). Qed.
Lemma lem5301032 (s : real -> Prop) : term808 s.
Proof. exact (fun h0 : term809 s => @lem5301031 s). Qed.
Lemma lem5301034 (p : Prop) : (term749 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5301035 (s : real -> Prop) : (term808 s) = ((inf s) = (inf s)).
Proof. exact (@lem5301034 ((inf s) = (inf s))). Qed.
Lemma lem5301036 (s : real -> Prop) : (inf s) = (inf s).
Proof. exact (EQ_MP (@lem5301035 s) (@lem5301032 s)). Qed.
Lemma lem5301042 (q : Prop) (p : Prop) (r : Prop) : (term765 p q r) = (term765 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5301043 (x : type1019) (_69375 : real) (_69373 : real -> Prop) (_69374 : real) : (term741 x _69375 _69373 _69374) = (term852 x _69375 _69373 _69374).
Proof. exact (@lem5301042 (_69373 = (@EMPTY real)) (has_inf _69373 _69374) (term718 x _69375 _69373 _69374)). Qed.
Lemma lem5301069 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5301070 (x : type1019) (_69373 : real -> Prop) (_69374 : real) (_69375 : real) : (term718 x _69375 _69373 _69374) = (term853 x _69373 _69374 _69375).
Proof. exact (@lem5301069 (term292 _69373 _69374) (term714 x _69373 _69374 _69375)). Qed.
Lemma lem5301078 (_69373 : real -> Prop) (_69374 : real) : (term307 _69373 _69374) = (term307 _69373 _69374).
Proof. exact (eq_refl (term307 _69373 _69374)). Qed.
Lemma lem5301079 (x : type1019) (_69373 : real -> Prop) (_69374 : real) (_69375 : real) : (term854 x _69375 _69373 _69374) = (term855 x _69373 _69374 _69375).
Proof. exact (MK_COMB (@lem5301078 _69373 _69374) (@lem5301070 x _69373 _69374 _69375)). Qed.
Lemma lem5301090 (_69373 : real -> Prop) : (term66 _69373) = (term66 _69373).
Proof. exact (eq_refl (term66 _69373)). Qed.
Lemma lem5301091 (x : type1019) (_69373 : real -> Prop) (_69374 : real) (_69375 : real) : (term852 x _69375 _69373 _69374) = (term856 x _69373 _69374 _69375).
Proof. exact (MK_COMB (@lem5301090 _69373) (@lem5301079 x _69373 _69374 _69375)). Qed.
Lemma lem5301102 (x : type1019) (_69373 : real -> Prop) (_69374 : real) (_69375 : real) : (term741 x _69375 _69373 _69374) = (term856 x _69373 _69374 _69375).
Proof. exact (TRANS (@lem5301043 x _69375 _69373 _69374) (@lem5301091 x _69373 _69374 _69375)). Qed.
Lemma lem5301103 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5301104 (x : type1019) (_69373 : real -> Prop) (_69374 : real) (_69375 : real) : (term857 x _69375 _69373 _69374) = (term858 x _69373 _69374 _69375).
Proof. exact (MK_COMB (@lem5301103) (@lem5301102 x _69373 _69374 _69375)). Qed.
Lemma lem5301130 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5301131 (x : type1019) (_69373 : real -> Prop) (_69374 : real) (_69375 : real) : (term718 x _69375 _69373 _69374) = (term853 x _69373 _69374 _69375).
Proof. exact (@lem5301130 (term292 _69373 _69374) (term714 x _69373 _69374 _69375)). Qed.
Lemma lem5301139 (_69373 : real -> Prop) (_69374 : real) : (term307 _69373 _69374) = (term307 _69373 _69374).
Proof. exact (eq_refl (term307 _69373 _69374)). Qed.
Lemma lem5301140 (x : type1019) (_69373 : real -> Prop) (_69374 : real) (_69375 : real) : (term854 x _69375 _69373 _69374) = (term855 x _69373 _69374 _69375).
Proof. exact (MK_COMB (@lem5301139 _69373 _69374) (@lem5301131 x _69373 _69374 _69375)). Qed.
Lemma lem5301151 (_69373 : real -> Prop) : (term66 _69373) = (term66 _69373).
Proof. exact (eq_refl (term66 _69373)). Qed.
Lemma lem5301152 (x : type1019) (_69373 : real -> Prop) (_69374 : real) (_69375 : real) : (term852 x _69375 _69373 _69374) = (term856 x _69373 _69374 _69375).
Proof. exact (MK_COMB (@lem5301151 _69373) (@lem5301140 x _69373 _69374 _69375)). Qed.
Lemma lem5301163 (x : type1019) (_69373 : real -> Prop) (_69374 : real) (_69375 : real) : ((term741 x _69375 _69373 _69374) = (term852 x _69375 _69373 _69374)) = ((term856 x _69373 _69374 _69375) = (term856 x _69373 _69374 _69375)).
Proof. exact (MK_COMB (@lem5301104 x _69373 _69374 _69375) (@lem5301152 x _69373 _69374 _69375)). Qed.
Lemma lem5301165 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5301166 (x : Prop) : (x = x) = True.
Proof. exact (@lem5301165 Prop x). Qed.
Lemma lem5301167 (x : type1019) (_69373 : real -> Prop) (_69374 : real) (_69375 : real) : ((term856 x _69373 _69374 _69375) = (term856 x _69373 _69374 _69375)) = True.
Proof. exact (@lem5301166 (term856 x _69373 _69374 _69375)). Qed.
Lemma lem5301168 (x : type1019) (_69375 : real) (_69373 : real -> Prop) (_69374 : real) : ((term741 x _69375 _69373 _69374) = (term852 x _69375 _69373 _69374)) = True.
Proof. exact (TRANS (@lem5301163 x _69373 _69374 _69375) (@lem5301167 x _69373 _69374 _69375)). Qed.
Lemma lem5301169 (x : type1019) (_69375 : real) (_69373 : real -> Prop) (_69374 : real) : True = ((term741 x _69375 _69373 _69374) = (term852 x _69375 _69373 _69374)).
Proof. exact (SYM (@lem5301168 x _69375 _69373 _69374)). Qed.
Lemma lem5301170 (x : type1019) (_69375 : real) (_69373 : real -> Prop) (_69374 : real) : (term741 x _69375 _69373 _69374) = (term852 x _69375 _69373 _69374).
Proof. exact (EQ_MP (@lem5301169 x _69375 _69373 _69374) (@lem0)). Qed.
Lemma lem5301171 (_69375 : real) (_69373 : real -> Prop) (_69374 : real) (x : type1019) (b : type1021) (h1 : term573 x b) : term852 x _69375 _69373 _69374.
Proof. exact (EQ_MP (@lem5301170 x _69375 _69373 _69374) (@lem5300152 _69375 _69373 _69374 x b h1)). Qed.
Lemma lem5301173 (b : Prop) (a : Prop) : (a \/ b) = (term780 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5301174 (x : type1019) (_69375 : real) (_69374 : real) (_69373 : real -> Prop) : (term852 x _69375 _69373 _69374) = (term859 x _69375 _69374 _69373).
Proof. exact (@lem5301173 (term854 x _69375 _69373 _69374) (_69373 = (@EMPTY real))). Qed.
Lemma lem5301176 (a : Prop) (b : Prop) : (term782 a b) = (term783 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5301177 (x : type1019) (_69375 : real) (_69373 : real -> Prop) (_69374 : real) : (term860 x _69375 _69373 _69374) = (term861 x _69375 _69373 _69374).
Proof. exact (@lem5301176 (has_inf _69373 _69374) (term718 x _69375 _69373 _69374)). Qed.
Lemma lem5301179 (a : Prop) (b : Prop) : (term782 a b) = (term783 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5301180 (x : type1019) (_69375 : real) (_69373 : real -> Prop) (_69374 : real) : (term862 x _69375 _69373 _69374) = (term863 x _69375 _69373 _69374).
Proof. exact (@lem5301179 (term714 x _69373 _69374 _69375) (term292 _69373 _69374)). Qed.
Lemma lem5301182 (a : Prop) : (term786 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5301183 (x : type1019) (_69373 : real -> Prop) (_69374 : real) (_69375 : real) : (term864 x _69373 _69374 _69375) = (term865 x _69373 _69374 _69375).
Proof. exact (@lem5301182 (term865 x _69373 _69374 _69375)). Qed.
Lemma lem5301184 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5301185 (x : type1019) (_69373 : real -> Prop) (_69374 : real) (_69375 : real) : (term866 x _69373 _69374 _69375) = (term867 x _69373 _69374 _69375).
Proof. exact (MK_COMB (@lem5301184) (@lem5301183 x _69373 _69374 _69375)). Qed.
Lemma lem5301187 (a : Prop) : (term786 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5301188 (_69373 : real -> Prop) (_69374 : real) : (term828 _69373 _69374) = ((inf _69373) = _69374).
Proof. exact (@lem5301187 ((inf _69373) = _69374)). Qed.
Lemma lem5301189 (x : type1019) (_69375 : real) (_69373 : real -> Prop) (_69374 : real) : (term863 x _69375 _69373 _69374) = (term868 x _69375 _69373 _69374).
Proof. exact (MK_COMB (@lem5301185 x _69373 _69374 _69375) (@lem5301188 _69373 _69374)). Qed.
Lemma lem5301190 (x : type1019) (_69375 : real) (_69373 : real -> Prop) (_69374 : real) : (term862 x _69375 _69373 _69374) = (term868 x _69375 _69373 _69374).
Proof. exact (TRANS (@lem5301180 x _69375 _69373 _69374) (@lem5301189 x _69375 _69373 _69374)). Qed.
Lemma lem5301191 (_69373 : real -> Prop) (_69374 : real) : (term830 _69373 _69374) = (term830 _69373 _69374).
Proof. exact (eq_refl (term830 _69373 _69374)). Qed.
Lemma lem5301192 (x : type1019) (_69375 : real) (_69373 : real -> Prop) (_69374 : real) : (term861 x _69375 _69373 _69374) = (term869 x _69375 _69373 _69374).
Proof. exact (MK_COMB (@lem5301191 _69373 _69374) (@lem5301190 x _69375 _69373 _69374)). Qed.
Lemma lem5301193 (x : type1019) (_69375 : real) (_69373 : real -> Prop) (_69374 : real) : (term860 x _69375 _69373 _69374) = (term869 x _69375 _69373 _69374).
Proof. exact (TRANS (@lem5301177 x _69375 _69373 _69374) (@lem5301192 x _69375 _69373 _69374)). Qed.
Lemma lem5301194 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5301195 (x : type1019) (_69375 : real) (_69373 : real -> Prop) (_69374 : real) : (term870 x _69375 _69373 _69374) = (term871 x _69375 _69373 _69374).
Proof. exact (MK_COMB (@lem5301194) (@lem5301193 x _69375 _69373 _69374)). Qed.
Lemma lem5301196 (_69373 : real -> Prop) : (_69373 = (@EMPTY real)) = (_69373 = (@EMPTY real)).
Proof. exact (eq_refl (_69373 = (@EMPTY real))). Qed.
Lemma lem5301197 (x : type1019) (_69375 : real) (_69374 : real) (_69373 : real -> Prop) : (term859 x _69375 _69374 _69373) = (term872 x _69375 _69374 _69373).
Proof. exact (MK_COMB (@lem5301195 x _69375 _69373 _69374) (@lem5301196 _69373)). Qed.
Lemma lem5301198 (x : type1019) (_69375 : real) (_69374 : real) (_69373 : real -> Prop) : (term852 x _69375 _69373 _69374) = (term872 x _69375 _69374 _69373).
Proof. exact (TRANS (@lem5301174 x _69375 _69374 _69373) (@lem5301197 x _69375 _69374 _69373)). Qed.
Lemma lem5301200 (x : type1019) (b : type1021) (s : real -> Prop) (l : real) (h1 : term70 s) (h2 : term573 x b) (h3 : term221 s l) : term873 x l s.
Proof. exact (conj (@lem5301028 x b s l h1 h2 h3) (@lem5301036 s)). Qed.
Lemma lem5301201 (x : type1019) (b : type1021) (s : real -> Prop) (l : real) (h1 : term70 s) (h2 : term573 x b) (h3 : term221 s l) : term874 x l s.
Proof. exact (conj (@lem5300778 s l h3) (@lem5301200 x b s l h1 h2 h3)). Qed.
Lemma lem5301203 (_69375 : real) (_69374 : real) (_69373 : real -> Prop) (x : type1019) (b : type1021) (h1 : term573 x b) : term872 x _69375 _69374 _69373.
Proof. exact (EQ_MP (@lem5301198 x _69375 _69374 _69373) (@lem5301171 _69375 _69373 _69374 x b h1)). Qed.
Lemma lem5301204 (l : real) (s : real -> Prop) (x : type1019) (b : type1021) (h1 : term573 x b) : term875 x l s.
Proof. exact (@lem5301203 l (inf s) s x b h1). Qed.
Lemma lem5301207 (x : type1019) (b : type1021) (s : real -> Prop) (l : real) (h1 : term70 s) (h2 : term573 x b) (h3 : term221 s l) : s = (@EMPTY real).
Proof. exact (@lem5301204 l s x b h2 (@lem5301201 x b s l h1 h2 h3)). Qed.
Lemma lem5301208 (x : type1019) (b : type1021) (s : real -> Prop) (l : real) (h1 : term573 x b) (h2 : term221 s l) : term876 s.
Proof. exact (fun h0 : term70 s => @lem5301207 x b s l h0 h1 h2). Qed.
Lemma lem5301210 (p : Prop) : (term749 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5301211 (s : real -> Prop) : (term876 s) = (s = (@EMPTY real)).
Proof. exact (@lem5301210 (s = (@EMPTY real))). Qed.
Lemma lem5301212 (x : type1019) (b : type1021) (s : real -> Prop) (l : real) (h1 : term573 x b) (h2 : term221 s l) : s = (@EMPTY real).
Proof. exact (EQ_MP (@lem5301211 s) (@lem5301208 x b s l h1 h2)). Qed.
Lemma lem5301215 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5301217 (s : real -> Prop) : (term70 s) = (term877 s).
Proof. exact (@lem5301215 (s = (@EMPTY real))). Qed.
Lemma lem5301220 (s : real -> Prop) (l : real) (h1 : term221 s l) : term877 s.
Proof. exact (EQ_MP (@lem5301217 s) (@lem5300096 s l h1)). Qed.
Lemma lem5301223 (x : type1019) (b : type1021) (s : real -> Prop) (l : real) (h1 : term573 x b) (h2 : term221 s l) : False.
Proof. exact (@lem5301220 s l h2 (@lem5301212 x b s l h1 h2)). Qed.
Lemma lem5301224 (x : type1019) (b : type1021) (s : real -> Prop) (l : real) (h1 : term573 x b) (h2 : term221 s l) : term759.
Proof. exact (fun h0 : ~ False => @lem5301223 x b s l h1 h2). Qed.
Lemma lem5301226 (p : Prop) : (term749 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5301227 : term759 = False.
Proof. exact (@lem5301226 False). Qed.
Lemma lem5301228 (x : type1019) (b : type1021) (s : real -> Prop) (l : real) (h1 : term573 x b) (h2 : term221 s l) : False.
Proof. exact (EQ_MP (@lem5301227) (@lem5301224 x b s l h1 h2)). Qed.
Lemma lem5301229 (x : type1019) (b : type1021) (l : real) (x' : real -> real) (s : real -> Prop) (h1 : term573 x b) (h2 : term189 l s x') (h3 : s = (@EMPTY real)) : False.
Proof. exact (EQ_MP (@lem5300389) (@lem5300386 x b l x' s h1 h2 h3)). Qed.
Lemma lem5301230 (x : type1019) (b : type1021) (l : real) (x' : real -> real) (s : real -> Prop) (h1 : term573 x b) (h2 : term189 l s x') (h3 : s = (@EMPTY real)) : (s = (@EMPTY real)) = False.
Proof. exact (prop_ext (fun h4 : s = (@EMPTY real) => @lem5301229 x b l x' s h1 h2 h3) (fun h4 : False => @lem5299986 s h3)). Qed.
Lemma lem5301231 (x : type1019) (b : type1021) (l : real) (x' : real -> real) (s : real -> Prop) (h1 : term573 x b) (h2 : term189 l s x') (h3 : s = (@EMPTY real)) : False.
Proof. exact (EQ_MP (@lem5301230 x b l x' s h1 h2 h3) (@lem5299986 s h3)). Qed.
Lemma lem5301232 (x : type1019) (b : type1021) (l : real) (x' : real -> real) (s : real -> Prop) (h1 : term573 x b) (h2 : term189 l s x') (h3 : s = (@EMPTY real)) : (s = (@EMPTY real)) = False.
Proof. exact (prop_ext (fun h4 : s = (@EMPTY real) => @lem5301231 x b l x' s h1 h2 h3) (fun h4 : False => @lem5299364 s h3)). Qed.
Lemma lem5301233 (x : type1019) (b : type1021) (l : real) (x' : real -> real) (s : real -> Prop) (h1 : term573 x b) (h2 : term189 l s x') (h3 : s = (@EMPTY real)) : False.
Proof. exact (EQ_MP (@lem5301232 x b l x' s h1 h2 h3) (@lem5299364 s h3)). Qed.
Lemma lem5301234 (x : type1019) (b : type1021) (l : real) (s : real -> Prop) (x' : real -> real) (h1 : term137 s x') (h2 : term573 x b) (h3 : term189 l s x') : (term137 s x') = False.
Proof. exact (prop_ext (fun h4 : term137 s x' => @lem5300664 x b l s x' h1 h2 h3) (fun h4 : False => @lem5299627 s x' h1)). Qed.
Lemma lem5301235 (x : type1019) (b : type1021) (l : real) (s : real -> Prop) (x' : real -> real) (h1 : term137 s x') (h2 : term573 x b) (h3 : term189 l s x') : False.
Proof. exact (EQ_MP (@lem5301234 x b l s x' h1 h2 h3) (@lem5299627 s x' h1)). Qed.
Lemma lem5301236 (x : type1019) (b : type1021) (l : real) (x' : real -> real) (s : real -> Prop) (h1 : term573 x b) (h2 : term189 l s x') (h3 : s = (@EMPTY real)) : (s = (@EMPTY real)) = False.
Proof. exact (prop_ext (fun h4 : s = (@EMPTY real) => @lem5301233 x b l x' s h1 h2 h3) (fun h4 : False => @lem5299364 s h3)). Qed.
Lemma lem5301237 (x : type1019) (b : type1021) (l : real) (x' : real -> real) (s : real -> Prop) (h1 : term573 x b) (h2 : term189 l s x') (h3 : s = (@EMPTY real)) : False.
Proof. exact (EQ_MP (@lem5301236 x b l x' s h1 h2 h3) (@lem5299364 s h3)). Qed.
Lemma lem5301238 (x : type1019) (b : type1021) (l : real) (s : real -> Prop) (x' : real -> real) (h1 : term573 x b) (h2 : term189 l s x') : False.
Proof. exact (or_elim (@lem5299101 l s x' h2) (fun h0 : s = (@EMPTY real) => @lem5301237 x b l x' s h1 h2 h0) (fun h0 : term137 s x' => @lem5301235 x b l s x' h0 h1 h2)). Qed.
Lemma lem5301239 (x : type1019) (b : type1021) (x' : real -> real) (s : real -> Prop) (l : real) (h1 : term573 x b) (h2 : term284 x' s l) : False.
Proof. exact (or_elim (@lem5299096 x' s l h2) (fun h0 : term189 l s x' => @lem5301238 x b l s x' h1 h0) (fun h0 : term221 s l => @lem5301228 x b s l h1 h0)). Qed.
Lemma lem5301240 (x : type1019) (b : type1021) (x' : real -> real) (s : real -> Prop) (l : real) (h1 : term573 x b) (h2 : term284 x' s l) : (term284 x' s l) = False.
Proof. exact (prop_ext (fun h3 : term284 x' s l => @lem5301239 x b x' s l h1 h2) (fun h3 : False => @lem5299096 x' s l h2)). Qed.
Lemma lem5301241 (x : type1019) (b : type1021) (x' : real -> real) (s : real -> Prop) (l : real) (h1 : term573 x b) (h2 : term284 x' s l) : False.
Proof. exact (EQ_MP (@lem5301240 x b x' s l h1 h2) (@lem5299096 x' s l h2)). Qed.
Lemma lem5301242 (x : type1019) (b : type1021) (x' : real -> real) (s : real -> Prop) (l : real) (h1 : term573 x b) (h2 : term284 x' s l) : (term573 x b) = False.
Proof. exact (prop_ext (fun h3 : term573 x b => @lem5301241 x b x' s l h1 h2) (fun h3 : False => @lem5299013 x b h1)). Qed.
Lemma lem5301243 (x : type1019) (b : type1021) (x' : real -> real) (s : real -> Prop) (l : real) (h1 : term573 x b) (h2 : term284 x' s l) : False.
Proof. exact (EQ_MP (@lem5301242 x b x' s l h1 h2) (@lem5299013 x b h1)). Qed.
Lemma lem5301244 (s : real -> Prop) (l : real) (x : type1019) (b : type1021) (h1 : term287 s l) (h2 : term573 x b) : False.
Proof. exact (ex_elim (@lem5298886 s l h1) (fun x' : real -> real => fun h0 : term286 s l x' => @lem5301243 x b x' s l h2 h0)). Qed.
Lemma lem5301245 (s : real -> Prop) (x : type1019) (b : type1021) (h1 : term289 s) (h2 : term573 x b) : False.
Proof. exact (ex_elim (@lem5298885 s h1) (fun l : real => fun h0 : term288 s l => @lem5301244 s l x b h0 h2)). Qed.
Lemma lem5301246 (x : type1019) (b : type1021) (h1 : term3) (h2 : term573 x b) : False.
Proof. exact (ex_elim (@lem5297965 h1) (fun s : real -> Prop => fun h0 : term290 s => @lem5301245 s x b h0 h2)). Qed.
Lemma lem5301247 (x : type1019) (h1 : term576 x) (h2 : term3) : False.
Proof. exact (ex_elim (@lem5298883 x h1) (fun b : type1021 => fun h0 : term575 x b => @lem5301246 x b h2 h0)). Qed.
Lemma lem5301248 (h1 : term10) (h2 : term3) : False.
Proof. exact (ex_elim (@lem5298882 h1) (fun x : type1019 => fun h0 : term577 x => @lem5301247 x h0 h2)). Qed.
Lemma lem5301249 (h1 : term3) : term8.
Proof. exact (fun h0 : term10 => @lem5301248 h0 h1). Qed.
Lemma lem5301250 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem5301251 (h1 : term3) : term9.
Proof. exact (EQ_MP (@lem5301250) (@lem5301249 h1)). Qed.
Lemma lem5301252 : term12.
Proof. exact (fun h0 : term3 => @lem5301251 h0). Qed.
Lemma lem5301253 : term4.
Proof. exact (EQ_MP (@lem5297380) (@lem5301252)). Qed.
Lemma lem5301255 : term4.
Proof. exact (@lem5297196 (@lem5301253)). Qed.
Lemma lem5301256 (h1 : term3) : term8.
Proof. exact (@lem5301255 (@lem5297181 h1)). Qed.
Lemma lem5301257 (h1 : term3) : False.
Proof. exact (@lem5301256 h1 (@lem5295254)). Qed.
Lemma lem5301258 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem5301257 h1) (fun h2 : False => @lem5297181 h1)). Qed.
Lemma lem5301259 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem5301258 h1) (@lem5297181 h1)). Qed.
Lemma lem5301260 : term2.
Proof. exact (fun h0 : term3 => @lem5301259 h0). Qed.
Lemma lem5301261 : term1.
Proof. exact (EQ_MP (@lem5297180) (@lem5301260)). Qed.
