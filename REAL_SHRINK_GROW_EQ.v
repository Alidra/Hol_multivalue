Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_SHRINK_GROW_EQ_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import REAL_SHRINK_GALOIS_spec.
Require Import REAL_SHRINK_RANGE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm69_spec.
Lemma lem2257158 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem2257159 : term1 = term2.
Proof. exact (@lem2257158 term1). Qed.
Lemma lem2257160 : term2 = term1.
Proof. exact (SYM (@lem2257159)). Qed.
Lemma lem2257161 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem2257164 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem2257165 : term5.
Proof. exact (fun h0 : term4 => @lem2257164 h0). Qed.
Lemma lem2257166 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem2257167 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem2257168 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem2257166 h2 (@lem2257167 h1)). Qed.
Lemma lem2257169 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem2257168 h1 h0). Qed.
Lemma lem2257170 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem2257171 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem2257169 h1 (@lem2257170 h2)). Qed.
Lemma lem2257172 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem2257171 h0 h1). Qed.
Lemma lem2257173 : term7.
Proof. exact (fun h0 : term5 => @lem2257172 h0). Qed.
Lemma lem2257176 : term5.
Proof. exact (@lem2257173 (@lem2257165)). Qed.
Lemma lem2257190 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem2257191 : term8 = term9.
Proof. exact (@lem2257190 term10). Qed.
Lemma lem2257202 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem2257203 : term12 = term13.
Proof. exact (MK_COMB (@lem2257202) (@lem2257191)). Qed.
Lemma lem2257206 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2257213 : term4 = term15.
Proof. exact (MK_COMB (@lem2257206) (@lem2257203)). Qed.
Lemma lem2257222 (y : real) (x : real) : (((term16 x) = y) = (term17 y x)) = (((term16 x) = y) = (term17 y x)).
Proof. exact (eq_refl (((term16 x) = y) = (term17 y x))). Qed.
Lemma lem2257223 (x : real) : (term18 x) = (term18 x).
Proof. exact (fun_ext (fun y : real => @lem2257222 y x)). Qed.
Lemma lem2257224 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2257225 (x : real) : (term19 x) = (term19 x).
Proof. exact (MK_COMB (@lem2257224) (@lem2257223 x)). Qed.
Lemma lem2257226 : term20 = term20.
Proof. exact (fun_ext (fun x : real => @lem2257225 x)). Qed.
Lemma lem2257227 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2257228 : term10 = term10.
Proof. exact (MK_COMB (@lem2257227) (@lem2257226)). Qed.
Lemma lem2257229 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2257230 : term9 = term9.
Proof. exact (MK_COMB (@lem2257229) (@lem2257228)). Qed.
Lemma lem2257231 (x : real) : (term21 x) = (term21 x).
Proof. exact (eq_refl (term21 x)). Qed.
Lemma lem2257232 : term22 = term22.
Proof. exact (fun_ext (fun x : real => @lem2257231 x)). Qed.
Lemma lem2257233 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2257234 : term23 = term23.
Proof. exact (MK_COMB (@lem2257233) (@lem2257232)). Qed.
Lemma lem2257235 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2257236 : term11 = term11.
Proof. exact (MK_COMB (@lem2257235) (@lem2257234)). Qed.
Lemma lem2257237 : term13 = term13.
Proof. exact (MK_COMB (@lem2257236) (@lem2257230)). Qed.
Lemma lem2257242 (x : real) : (((term24 x) = x) = (term25 x)) = (((term24 x) = x) = (term25 x)).
Proof. exact (eq_refl (((term24 x) = x) = (term25 x))). Qed.
Lemma lem2257243 : term26 = term26.
Proof. exact (fun_ext (fun x : real => @lem2257242 x)). Qed.
Lemma lem2257244 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2257245 : term1 = term1.
Proof. exact (MK_COMB (@lem2257244) (@lem2257243)). Qed.
Lemma lem2257246 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2257247 : term3 = term3.
Proof. exact (MK_COMB (@lem2257246) (@lem2257245)). Qed.
Lemma lem2257248 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2257249 : term14 = term14.
Proof. exact (MK_COMB (@lem2257248) (@lem2257247)). Qed.
Lemma lem2257250 : term15 = term15.
Proof. exact (MK_COMB (@lem2257249) (@lem2257237)). Qed.
Lemma lem2257283 : term4 = term15.
Proof. exact (TRANS (@lem2257213) (@lem2257250)). Qed.
Lemma lem2257284 : term15 = term4.
Proof. exact (SYM (@lem2257283)). Qed.
Lemma lem2257285 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem2257287 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem2257302 (x : real) : (term27 x) = (term28 x).
Proof. exact (@lem17646 ((term24 x) = x) (term25 x)). Qed.
Lemma lem2257303 (P : real -> Prop) : (term29 P) = (term30 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem2257304 : term3 = term31.
Proof. exact (@lem2257303 term26). Qed.
Lemma lem2257305 (x : real) : (term32 x) = (((term24 x) = x) = (term25 x)).
Proof. exact (eq_refl (term32 x)). Qed.
Lemma lem2257306 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2257307 (x : real) : (term33 x) = (term27 x).
Proof. exact (MK_COMB (@lem2257306) (@lem2257305 x)). Qed.
Lemma lem2257308 (x : real) : (term33 x) = (term28 x).
Proof. exact (TRANS (@lem2257307 x) (@lem2257302 x)). Qed.
Lemma lem2257309 : term34 = term35.
Proof. exact (fun_ext (fun x : real => @lem2257308 x)). Qed.
Lemma lem2257310 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem2257311 : term31 = term36.
Proof. exact (MK_COMB (@lem2257310) (@lem2257309)). Qed.
Lemma lem2257312 : term3 = term36.
Proof. exact (TRANS (@lem2257304) (@lem2257311)). Qed.
Lemma lem2257314 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term37 A P Q) = (term38 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem2257315 (P : real -> Prop) (Q : real -> Prop) : (term39 P Q) = (term40 P Q).
Proof. exact (@lem2257314 real P Q). Qed.
Lemma lem2257316 : term41 = term42.
Proof. exact (@lem2257315 term43 term44). Qed.
Lemma lem2257317 (x : real) : (term45 x) = (term46 x).
Proof. exact (eq_refl (term45 x)). Qed.
Lemma lem2257318 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2257319 (x : real) : (term47 x) = (term48 x).
Proof. exact (MK_COMB (@lem2257318) (@lem2257317 x)). Qed.
Lemma lem2257320 (x : real) : (term49 x) = (term50 x).
Proof. exact (eq_refl (term49 x)). Qed.
Lemma lem2257321 (x : real) : (term51 x) = (term28 x).
Proof. exact (MK_COMB (@lem2257319 x) (@lem2257320 x)). Qed.
Lemma lem2257322 : term52 = term35.
Proof. exact (fun_ext (fun x : real => @lem2257321 x)). Qed.
Lemma lem2257323 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem2257324 : term41 = term36.
Proof. exact (MK_COMB (@lem2257323) (@lem2257322)). Qed.
Lemma lem2257325 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2257326 : term53 = term54.
Proof. exact (MK_COMB (@lem2257325) (@lem2257324)). Qed.
Lemma lem2257327 (x : real) : (term45 x) = (term46 x).
Proof. exact (eq_refl (term45 x)). Qed.
Lemma lem2257328 : term55 = term43.
Proof. exact (fun_ext (fun x : real => @lem2257327 x)). Qed.
Lemma lem2257329 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem2257330 : term56 = term57.
Proof. exact (MK_COMB (@lem2257329) (@lem2257328)). Qed.
Lemma lem2257331 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2257332 : term58 = term59.
Proof. exact (MK_COMB (@lem2257331) (@lem2257330)). Qed.
Lemma lem2257333 (x : real) : (term49 x) = (term50 x).
Proof. exact (eq_refl (term49 x)). Qed.
Lemma lem2257334 : term60 = term44.
Proof. exact (fun_ext (fun x : real => @lem2257333 x)). Qed.
Lemma lem2257335 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem2257336 : term61 = term62.
Proof. exact (MK_COMB (@lem2257335) (@lem2257334)). Qed.
Lemma lem2257337 : term42 = term63.
Proof. exact (MK_COMB (@lem2257332) (@lem2257336)). Qed.
Lemma lem2257338 : (term41 = term42) = (term36 = term63).
Proof. exact (MK_COMB (@lem2257326) (@lem2257337)). Qed.
Lemma lem2257339 : term36 = term63.
Proof. exact (EQ_MP (@lem2257338) (@lem2257316)). Qed.
Lemma lem2257437 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term38 A P Q) = (term37 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem2257438 (P : real -> Prop) (Q : real -> Prop) : (term40 P Q) = (term39 P Q).
Proof. exact (@lem2257437 real P Q). Qed.
Lemma lem2257439 : term42 = term41.
Proof. exact (@lem2257438 term43 term44). Qed.
Lemma lem2257440 (x : real) : (term45 x) = (term46 x).
Proof. exact (eq_refl (term45 x)). Qed.
Lemma lem2257441 : term55 = term43.
Proof. exact (fun_ext (fun x : real => @lem2257440 x)). Qed.
Lemma lem2257442 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem2257443 : term56 = term57.
Proof. exact (MK_COMB (@lem2257442) (@lem2257441)). Qed.
Lemma lem2257444 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2257445 : term58 = term59.
Proof. exact (MK_COMB (@lem2257444) (@lem2257443)). Qed.
Lemma lem2257446 (x : real) : (term49 x) = (term50 x).
Proof. exact (eq_refl (term49 x)). Qed.
Lemma lem2257447 : term60 = term44.
Proof. exact (fun_ext (fun x : real => @lem2257446 x)). Qed.
Lemma lem2257448 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem2257449 : term61 = term62.
Proof. exact (MK_COMB (@lem2257448) (@lem2257447)). Qed.
Lemma lem2257450 : term42 = term63.
Proof. exact (MK_COMB (@lem2257445) (@lem2257449)). Qed.
Lemma lem2257451 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2257452 : term64 = term65.
Proof. exact (MK_COMB (@lem2257451) (@lem2257450)). Qed.
Lemma lem2257453 (x : real) : (term45 x) = (term46 x).
Proof. exact (eq_refl (term45 x)). Qed.
Lemma lem2257454 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2257455 (x : real) : (term47 x) = (term48 x).
Proof. exact (MK_COMB (@lem2257454) (@lem2257453 x)). Qed.
Lemma lem2257456 (x : real) : (term49 x) = (term50 x).
Proof. exact (eq_refl (term49 x)). Qed.
Lemma lem2257457 (x : real) : (term51 x) = (term28 x).
Proof. exact (MK_COMB (@lem2257455 x) (@lem2257456 x)). Qed.
Lemma lem2257458 : term52 = term35.
Proof. exact (fun_ext (fun x : real => @lem2257457 x)). Qed.
Lemma lem2257459 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem2257460 : term41 = term36.
Proof. exact (MK_COMB (@lem2257459) (@lem2257458)). Qed.
Lemma lem2257461 : (term42 = term41) = (term63 = term36).
Proof. exact (MK_COMB (@lem2257452) (@lem2257460)). Qed.
Lemma lem2257462 : term63 = term36.
Proof. exact (EQ_MP (@lem2257461) (@lem2257439)). Qed.
Lemma lem2257463 : term36 = term36.
Proof. exact (TRANS (@lem2257339) (@lem2257462)). Qed.
Lemma lem2257464 : term3 = term36.
Proof. exact (TRANS (@lem2257312) (@lem2257463)). Qed.
Lemma lem2257465 (h1 : term3) : term36.
Proof. exact (EQ_MP (@lem2257464) (@lem2257285 h1)). Qed.
Lemma lem2257489 (y : real) (x : real) : (term66 y x) = (term67 y x).
Proof. exact (@lem17045 (term25 y) ((term68 y) = x)). Qed.
Lemma lem2257495 (y : real) (x : real) : (term69 y x) = (term69 y x).
Proof. exact (eq_refl (term69 y x)). Qed.
Lemma lem2257497 (x : real) (y : real) : (term70 x y) = (term70 x y).
Proof. exact (eq_refl (term70 x y)). Qed.
Lemma lem2257498 (y : real) (x : real) : (term71 y x) = (term72 y x).
Proof. exact (MK_COMB (@lem2257497 x y) (@lem2257489 y x)). Qed.
Lemma lem2257499 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2257500 (y : real) (x : real) : (term73 y x) = (term74 y x).
Proof. exact (MK_COMB (@lem2257499) (@lem2257498 y x)). Qed.
Lemma lem2257501 (y : real) (x : real) : (term75 y x) = (term76 y x).
Proof. exact (MK_COMB (@lem2257500 y x) (@lem2257495 y x)). Qed.
Lemma lem2257502 (y : real) (x : real) : (((term16 x) = y) = (term17 y x)) = (term75 y x).
Proof. exact (@lem17784 ((term16 x) = y) (term17 y x)). Qed.
Lemma lem2257503 (y : real) (x : real) : (((term16 x) = y) = (term17 y x)) = (term76 y x).
Proof. exact (TRANS (@lem2257502 y x) (@lem2257501 y x)). Qed.
Lemma lem2257504 (x : real) : (term18 x) = (term77 x).
Proof. exact (fun_ext (fun y : real => @lem2257503 y x)). Qed.
Lemma lem2257505 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2257506 (x : real) : (term19 x) = (term78 x).
Proof. exact (MK_COMB (@lem2257505) (@lem2257504 x)). Qed.
Lemma lem2257507 : term20 = term79.
Proof. exact (fun_ext (fun x : real => @lem2257506 x)). Qed.
Lemma lem2257508 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2257509 : term10 = term80.
Proof. exact (MK_COMB (@lem2257508) (@lem2257507)). Qed.
Lemma lem2257515 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term81 A P Q) = (term82 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem2257516 (P : real -> Prop) (Q : real -> Prop) : (term83 P Q) = (term84 P Q).
Proof. exact (@lem2257515 real P Q). Qed.
Lemma lem2257517 (x : real) : (term85 x) = (term86 x).
Proof. exact (@lem2257516 (term87 x) (term88 x)). Qed.
Lemma lem2257518 (y : real) (x : real) : (term89 x y) = (term72 y x).
Proof. exact (eq_refl (term89 x y)). Qed.
Lemma lem2257519 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2257520 (y : real) (x : real) : (term90 x y) = (term74 y x).
Proof. exact (MK_COMB (@lem2257519) (@lem2257518 y x)). Qed.
Lemma lem2257521 (y : real) (x : real) : (term91 x y) = (term69 y x).
Proof. exact (eq_refl (term91 x y)). Qed.
Lemma lem2257522 (y : real) (x : real) : (term92 x y) = (term76 y x).
Proof. exact (MK_COMB (@lem2257520 y x) (@lem2257521 y x)). Qed.
Lemma lem2257523 (x : real) : (term93 x) = (term77 x).
Proof. exact (fun_ext (fun y : real => @lem2257522 y x)). Qed.
Lemma lem2257524 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2257525 (x : real) : (term85 x) = (term78 x).
Proof. exact (MK_COMB (@lem2257524) (@lem2257523 x)). Qed.
Lemma lem2257526 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2257527 (x : real) : (term94 x) = (term95 x).
Proof. exact (MK_COMB (@lem2257526) (@lem2257525 x)). Qed.
Lemma lem2257528 (y : real) (x : real) : (term89 x y) = (term72 y x).
Proof. exact (eq_refl (term89 x y)). Qed.
Lemma lem2257529 (x : real) : (term96 x) = (term87 x).
Proof. exact (fun_ext (fun y : real => @lem2257528 y x)). Qed.
Lemma lem2257530 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2257531 (x : real) : (term97 x) = (term98 x).
Proof. exact (MK_COMB (@lem2257530) (@lem2257529 x)). Qed.
Lemma lem2257532 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2257533 (x : real) : (term99 x) = (term100 x).
Proof. exact (MK_COMB (@lem2257532) (@lem2257531 x)). Qed.
Lemma lem2257534 (y : real) (x : real) : (term91 x y) = (term69 y x).
Proof. exact (eq_refl (term91 x y)). Qed.
Lemma lem2257535 (x : real) : (term101 x) = (term88 x).
Proof. exact (fun_ext (fun y : real => @lem2257534 y x)). Qed.
Lemma lem2257536 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2257537 (x : real) : (term102 x) = (term103 x).
Proof. exact (MK_COMB (@lem2257536) (@lem2257535 x)). Qed.
Lemma lem2257538 (x : real) : (term86 x) = (term104 x).
Proof. exact (MK_COMB (@lem2257533 x) (@lem2257537 x)). Qed.
Lemma lem2257539 (x : real) : ((term85 x) = (term86 x)) = ((term78 x) = (term104 x)).
Proof. exact (MK_COMB (@lem2257527 x) (@lem2257538 x)). Qed.
Lemma lem2257540 (x : real) : (term78 x) = (term104 x).
Proof. exact (EQ_MP (@lem2257539 x) (@lem2257517 x)). Qed.
Lemma lem2257637 : term79 = term105.
Proof. exact (fun_ext (fun x : real => @lem2257540 x)). Qed.
Lemma lem2257638 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2257639 : term80 = term106.
Proof. exact (MK_COMB (@lem2257638) (@lem2257637)). Qed.
Lemma lem2257641 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term81 A P Q) = (term82 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem2257642 (P : real -> Prop) (Q : real -> Prop) : (term83 P Q) = (term84 P Q).
Proof. exact (@lem2257641 real P Q). Qed.
Lemma lem2257643 : term107 = term108.
Proof. exact (@lem2257642 term109 term110). Qed.
Lemma lem2257644 (x : real) : (term111 x) = (term98 x).
Proof. exact (eq_refl (term111 x)). Qed.
Lemma lem2257645 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2257646 (x : real) : (term112 x) = (term100 x).
Proof. exact (MK_COMB (@lem2257645) (@lem2257644 x)). Qed.
Lemma lem2257647 (x : real) : (term113 x) = (term103 x).
Proof. exact (eq_refl (term113 x)). Qed.
Lemma lem2257648 (x : real) : (term114 x) = (term104 x).
Proof. exact (MK_COMB (@lem2257646 x) (@lem2257647 x)). Qed.
Lemma lem2257649 : term115 = term105.
Proof. exact (fun_ext (fun x : real => @lem2257648 x)). Qed.
Lemma lem2257650 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2257651 : term107 = term106.
Proof. exact (MK_COMB (@lem2257650) (@lem2257649)). Qed.
Lemma lem2257652 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2257653 : term116 = term117.
Proof. exact (MK_COMB (@lem2257652) (@lem2257651)). Qed.
Lemma lem2257654 (x : real) : (term111 x) = (term98 x).
Proof. exact (eq_refl (term111 x)). Qed.
Lemma lem2257655 : term118 = term109.
Proof. exact (fun_ext (fun x : real => @lem2257654 x)). Qed.
Lemma lem2257656 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2257657 : term119 = term120.
Proof. exact (MK_COMB (@lem2257656) (@lem2257655)). Qed.
Lemma lem2257658 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2257659 : term121 = term122.
Proof. exact (MK_COMB (@lem2257658) (@lem2257657)). Qed.
Lemma lem2257660 (x : real) : (term113 x) = (term103 x).
Proof. exact (eq_refl (term113 x)). Qed.
Lemma lem2257661 : term123 = term110.
Proof. exact (fun_ext (fun x : real => @lem2257660 x)). Qed.
Lemma lem2257662 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2257663 : term124 = term125.
Proof. exact (MK_COMB (@lem2257662) (@lem2257661)). Qed.
Lemma lem2257664 : term108 = term126.
Proof. exact (MK_COMB (@lem2257659) (@lem2257663)). Qed.
Lemma lem2257665 : (term107 = term108) = (term106 = term126).
Proof. exact (MK_COMB (@lem2257653) (@lem2257664)). Qed.
Lemma lem2257666 : term106 = term126.
Proof. exact (EQ_MP (@lem2257665) (@lem2257643)). Qed.
Lemma lem2257773 : term80 = term126.
Proof. exact (TRANS (@lem2257639) (@lem2257666)). Qed.
Lemma lem2257774 : term10 = term126.
Proof. exact (TRANS (@lem2257509) (@lem2257773)). Qed.
Lemma lem2257775 (h1 : term10) : term126.
Proof. exact (EQ_MP (@lem2257774) (@lem2257287 h1)). Qed.
Lemma lem2257872 (y : real) (x : real) : (term69 y x) = (term69 y x).
Proof. exact (eq_refl (term69 y x)). Qed.
Lemma lem2257873 (x : real) : (term88 x) = (term88 x).
Proof. exact (fun_ext (fun y : real => @lem2257872 y x)). Qed.
Lemma lem2257874 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2257875 (x : real) : (term103 x) = (term103 x).
Proof. exact (MK_COMB (@lem2257874) (@lem2257873 x)). Qed.
Lemma lem2257876 : term110 = term110.
Proof. exact (fun_ext (fun x : real => @lem2257875 x)). Qed.
Lemma lem2257877 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2257878 : term125 = term125.
Proof. exact (MK_COMB (@lem2257877) (@lem2257876)). Qed.
Lemma lem2257943 (y : real) (x : real) : (term72 y x) = (term72 y x).
Proof. exact (eq_refl (term72 y x)). Qed.
Lemma lem2257944 (x : real) : (term87 x) = (term87 x).
Proof. exact (fun_ext (fun y : real => @lem2257943 y x)). Qed.
Lemma lem2257945 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2257946 (x : real) : (term98 x) = (term98 x).
Proof. exact (MK_COMB (@lem2257945) (@lem2257944 x)). Qed.
Lemma lem2257947 : term109 = term109.
Proof. exact (fun_ext (fun x : real => @lem2257946 x)). Qed.
Lemma lem2257948 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2257949 : term120 = term120.
Proof. exact (MK_COMB (@lem2257948) (@lem2257947)). Qed.
Lemma lem2257950 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2257951 : term122 = term122.
Proof. exact (MK_COMB (@lem2257950) (@lem2257949)). Qed.
Lemma lem2257952 : term126 = term126.
Proof. exact (MK_COMB (@lem2257951) (@lem2257878)). Qed.
Lemma lem2257953 (h1 : term10) : term126.
Proof. exact (EQ_MP (@lem2257952) (@lem2257775 h1)). Qed.
Lemma lem2258099 (x : real) (h1 : term28 x) : term28 x.
Proof. exact (h1). Qed.
Lemma lem2258100 (h1 : term10) : term125.
Proof. exact (proj2 (@lem2257953 h1)). Qed.
Lemma lem2258101 (h1 : term10) : term120.
Proof. exact (proj1 (@lem2257953 h1)). Qed.
Lemma lem2258102 (x : real) (h1 : term46 x) : term46 x.
Proof. exact (h1). Qed.
Lemma lem2258103 (x : real) (h1 : term50 x) : term50 x.
Proof. exact (h1). Qed.
Lemma lem2258154 (y : real) (x : real) : (term69 y x) = (term127 y x).
Proof. exact (@lem19490 (term25 y) (term128 x y) ((term68 y) = x)). Qed.
Lemma lem2258155 (x : real) : (term88 x) = (term129 x).
Proof. exact (fun_ext (fun y : real => @lem2258154 y x)). Qed.
Lemma lem2258156 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2258157 (x : real) : (term103 x) = (term130 x).
Proof. exact (MK_COMB (@lem2258156) (@lem2258155 x)). Qed.
Lemma lem2258158 : term110 = term131.
Proof. exact (fun_ext (fun x : real => @lem2258157 x)). Qed.
Lemma lem2258159 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2258161 : term125 = term132.
Proof. exact (MK_COMB (@lem2258159) (@lem2258158)). Qed.
Lemma lem2258162 (h1 : term10) : term132.
Proof. exact (EQ_MP (@lem2258161) (@lem2258100 h1)). Qed.
Lemma lem2258191 (y : real) (x : real) : (term72 y x) = (term72 y x).
Proof. exact (eq_refl (term72 y x)). Qed.
Lemma lem2258192 (x : real) : (term87 x) = (term87 x).
Proof. exact (fun_ext (fun y : real => @lem2258191 y x)). Qed.
Lemma lem2258193 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2258194 (x : real) : (term98 x) = (term98 x).
Proof. exact (MK_COMB (@lem2258193) (@lem2258192 x)). Qed.
Lemma lem2258195 : term109 = term109.
Proof. exact (fun_ext (fun x : real => @lem2258194 x)). Qed.
Lemma lem2258196 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2258198 : term120 = term120.
Proof. exact (MK_COMB (@lem2258196) (@lem2258195)). Qed.
Lemma lem2258199 (h1 : term10) : term120.
Proof. exact (EQ_MP (@lem2258198) (@lem2258101 h1)). Qed.
Lemma lem2258243 (_28533 : real) (h1 : term10) : term133 _28533.
Proof. exact (@lem2258162 h1 _28533). Qed.
Lemma lem2258244 (_28533 : real) : (term133 _28533) = (term130 _28533).
Proof. exact (eq_refl (term133 _28533)). Qed.
Lemma lem2258245 (_28533 : real) (h1 : term10) : term130 _28533.
Proof. exact (EQ_MP (@lem2258244 _28533) (@lem2258243 _28533 h1)). Qed.
Lemma lem2258246 (_28533 : real) (_28534 : real) (h1 : term10) : term134 _28533 _28534.
Proof. exact (@lem2258245 _28533 h1 _28534). Qed.
Lemma lem2258247 (_28534 : real) (_28533 : real) : (term134 _28533 _28534) = (term127 _28534 _28533).
Proof. exact (eq_refl (term134 _28533 _28534)). Qed.
Lemma lem2258248 (_28534 : real) (_28533 : real) (h1 : term10) : term127 _28534 _28533.
Proof. exact (EQ_MP (@lem2258247 _28534 _28533) (@lem2258246 _28533 _28534 h1)). Qed.
Lemma lem2258252 (_28536 : real) (h1 : term10) : term111 _28536.
Proof. exact (@lem2258199 h1 _28536). Qed.
Lemma lem2258253 (_28536 : real) : (term111 _28536) = (term98 _28536).
Proof. exact (eq_refl (term111 _28536)). Qed.
Lemma lem2258254 (_28536 : real) (h1 : term10) : term98 _28536.
Proof. exact (EQ_MP (@lem2258253 _28536) (@lem2258252 _28536 h1)). Qed.
Lemma lem2258255 (_28536 : real) (_28537 : real) (h1 : term10) : term89 _28536 _28537.
Proof. exact (@lem2258254 _28536 h1 _28537). Qed.
Lemma lem2258256 (_28537 : real) (_28536 : real) : (term89 _28536 _28537) = (term72 _28537 _28536).
Proof. exact (eq_refl (term89 _28536 _28537)). Qed.
Lemma lem2258283 (x : real) (h1 : term46 x) : term135 x.
Proof. exact (proj2 (@lem2258102 x h1)). Qed.
Lemma lem2258289 (_28533 : real) (_28534 : real) (h1 : term10) : term136 _28533 _28534.
Proof. exact (proj1 (@lem2258248 _28534 _28533 h1)). Qed.
Lemma lem2258307 (_28537 : real) (_28536 : real) (h1 : term10) : term72 _28537 _28536.
Proof. exact (EQ_MP (@lem2258256 _28537 _28536) (@lem2258255 _28536 _28537 h1)). Qed.
Lemma lem2258309 (x : real) (h1 : term50 x) : term137 x.
Proof. exact (proj1 (@lem2258103 x h1)). Qed.
Lemma lem2258425 (x : real) (h1 : term46 x) : (term24 x) = x.
Proof. exact (proj1 (@lem2258102 x h1)). Qed.
Lemma lem2258426 (x : real) (h1 : term46 x) : term138 x.
Proof. exact (fun h0 : term137 x => @lem2258425 x h1). Qed.
Lemma lem2258428 (p : Prop) : (term139 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2258429 (x : real) : (term138 x) = ((term24 x) = x).
Proof. exact (@lem2258428 ((term24 x) = x)). Qed.
Lemma lem2258430 (x : real) (h1 : term46 x) : (term24 x) = x.
Proof. exact (EQ_MP (@lem2258429 x) (@lem2258426 x h1)). Qed.
Lemma lem2258436 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem2258437 (_28533 : real) (_28534 : real) : (term136 _28533 _28534) = (term140 _28533 _28534).
Proof. exact (@lem2258436 (term25 _28534) (term128 _28533 _28534)). Qed.
Lemma lem2258445 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2258446 (_28533 : real) (_28534 : real) : (term141 _28533 _28534) = (term142 _28533 _28534).
Proof. exact (MK_COMB (@lem2258445) (@lem2258437 _28533 _28534)). Qed.
Lemma lem2258454 (_28533 : real) (_28534 : real) : (term140 _28533 _28534) = (term140 _28533 _28534).
Proof. exact (eq_refl (term140 _28533 _28534)). Qed.
Lemma lem2258455 (_28533 : real) (_28534 : real) : ((term136 _28533 _28534) = (term140 _28533 _28534)) = ((term140 _28533 _28534) = (term140 _28533 _28534)).
Proof. exact (MK_COMB (@lem2258446 _28533 _28534) (@lem2258454 _28533 _28534)). Qed.
Lemma lem2258457 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem2258458 (x : Prop) : (x = x) = True.
Proof. exact (@lem2258457 Prop x). Qed.
Lemma lem2258459 (_28533 : real) (_28534 : real) : ((term140 _28533 _28534) = (term140 _28533 _28534)) = True.
Proof. exact (@lem2258458 (term140 _28533 _28534)). Qed.
Lemma lem2258460 (_28533 : real) (_28534 : real) : ((term136 _28533 _28534) = (term140 _28533 _28534)) = True.
Proof. exact (TRANS (@lem2258455 _28533 _28534) (@lem2258459 _28533 _28534)). Qed.
Lemma lem2258461 (_28533 : real) (_28534 : real) : True = ((term136 _28533 _28534) = (term140 _28533 _28534)).
Proof. exact (SYM (@lem2258460 _28533 _28534)). Qed.
Lemma lem2258462 (_28533 : real) (_28534 : real) : (term136 _28533 _28534) = (term140 _28533 _28534).
Proof. exact (EQ_MP (@lem2258461 _28533 _28534) (@lem0)). Qed.
Lemma lem2258463 (_28533 : real) (_28534 : real) (h1 : term10) : term140 _28533 _28534.
Proof. exact (EQ_MP (@lem2258462 _28533 _28534) (@lem2258289 _28533 _28534 h1)). Qed.
Lemma lem2258465 (b : Prop) (a : Prop) : (a \/ b) = (term143 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem2258466 (_28533 : real) (_28534 : real) : (term140 _28533 _28534) = (term144 _28533 _28534).
Proof. exact (@lem2258465 (term128 _28533 _28534) (term25 _28534)). Qed.
Lemma lem2258468 (a : Prop) : (term145 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem2258469 (_28533 : real) (_28534 : real) : (term146 _28533 _28534) = ((term16 _28533) = _28534).
Proof. exact (@lem2258468 ((term16 _28533) = _28534)). Qed.
Lemma lem2258470 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2258471 (_28533 : real) (_28534 : real) : (term147 _28533 _28534) = (term148 _28533 _28534).
Proof. exact (MK_COMB (@lem2258470) (@lem2258469 _28533 _28534)). Qed.
Lemma lem2258472 (_28534 : real) : (term25 _28534) = (term25 _28534).
Proof. exact (eq_refl (term25 _28534)). Qed.
Lemma lem2258473 (_28533 : real) (_28534 : real) : (term144 _28533 _28534) = (term149 _28533 _28534).
Proof. exact (MK_COMB (@lem2258471 _28533 _28534) (@lem2258472 _28534)). Qed.
Lemma lem2258474 (_28533 : real) (_28534 : real) : (term140 _28533 _28534) = (term149 _28533 _28534).
Proof. exact (TRANS (@lem2258466 _28533 _28534) (@lem2258473 _28533 _28534)). Qed.
Lemma lem2258477 (_28533 : real) (_28534 : real) (h1 : term10) : term149 _28533 _28534.
Proof. exact (EQ_MP (@lem2258474 _28533 _28534) (@lem2258463 _28533 _28534 h1)). Qed.
Lemma lem2258478 (x : real) (h1 : term10) : term150 x.
Proof. exact (@lem2258477 (term68 x) x h1). Qed.
Lemma lem2258481 (x : real) (h1 : term10) (h2 : term46 x) : term25 x.
Proof. exact (@lem2258478 x h1 (@lem2258430 x h2)). Qed.
Lemma lem2258482 (x : real) (h1 : term10) (h2 : term46 x) : term151 x.
Proof. exact (fun h0 : term135 x => @lem2258481 x h1 h2). Qed.
Lemma lem2258484 (p : Prop) : (term139 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2258485 (x : real) : (term151 x) = (term25 x).
Proof. exact (@lem2258484 (term25 x)). Qed.
Lemma lem2258486 (x : real) (h1 : term10) (h2 : term46 x) : term25 x.
Proof. exact (EQ_MP (@lem2258485 x) (@lem2258482 x h1 h2)). Qed.
Lemma lem2258489 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem2258491 (x : real) : (term135 x) = (term152 x).
Proof. exact (@lem2258489 (term25 x)). Qed.
Lemma lem2258494 (x : real) (h1 : term46 x) : term152 x.
Proof. exact (EQ_MP (@lem2258491 x) (@lem2258283 x h1)). Qed.
Lemma lem2258497 (x : real) (h1 : term10) (h2 : term46 x) : False.
Proof. exact (@lem2258494 x h2 (@lem2258486 x h1 h2)). Qed.
Lemma lem2258498 (x : real) (h1 : term10) (h2 : term46 x) : term153.
Proof. exact (fun h0 : ~ False => @lem2258497 x h1 h2). Qed.
Lemma lem2258500 (p : Prop) : (term139 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2258501 : term153 = False.
Proof. exact (@lem2258500 False). Qed.
Lemma lem2258502 (x : real) (h1 : term10) (h2 : term46 x) : False.
Proof. exact (EQ_MP (@lem2258501) (@lem2258498 x h1 h2)). Qed.
Lemma lem2258604 (x : real) (h1 : term50 x) : term25 x.
Proof. exact (proj2 (@lem2258103 x h1)). Qed.
Lemma lem2258605 (x : real) (h1 : term50 x) : term151 x.
Proof. exact (fun h0 : term135 x => @lem2258604 x h1). Qed.
Lemma lem2258607 (p : Prop) : (term139 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2258608 (x : real) : (term151 x) = (term25 x).
Proof. exact (@lem2258607 (term25 x)). Qed.
Lemma lem2258609 (x : real) (h1 : term50 x) : term25 x.
Proof. exact (EQ_MP (@lem2258608 x) (@lem2258605 x h1)). Qed.
Lemma lem2258611 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem2258612 (x : real) : (term68 x) = (term68 x).
Proof. exact (@lem2258611 (term68 x)). Qed.
Lemma lem2258613 (x : real) : term154 x.
Proof. exact (fun h0 : term155 x => @lem2258612 x). Qed.
Lemma lem2258615 (p : Prop) : (term139 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2258616 (x : real) : (term154 x) = ((term68 x) = (term68 x)).
Proof. exact (@lem2258615 ((term68 x) = (term68 x))). Qed.
Lemma lem2258617 (x : real) : (term68 x) = (term68 x).
Proof. exact (EQ_MP (@lem2258616 x) (@lem2258613 x)). Qed.
Lemma lem2258619 (b : Prop) (a : Prop) : (a \/ b) = (term143 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem2258620 (_28536 : real) (_28537 : real) : (term72 _28537 _28536) = (term156 _28536 _28537).
Proof. exact (@lem2258619 (term67 _28537 _28536) ((term16 _28536) = _28537)). Qed.
Lemma lem2258622 (a : Prop) (b : Prop) : (term157 a b) = (term158 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem2258623 (_28537 : real) (_28536 : real) : (term159 _28537 _28536) = (term160 _28537 _28536).
Proof. exact (@lem2258622 (term135 _28537) (term161 _28537 _28536)). Qed.
Lemma lem2258625 (a : Prop) : (term145 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem2258626 (_28537 : real) : (term162 _28537) = (term25 _28537).
Proof. exact (@lem2258625 (term25 _28537)). Qed.
Lemma lem2258627 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2258628 (_28537 : real) : (term163 _28537) = (term164 _28537).
Proof. exact (MK_COMB (@lem2258627) (@lem2258626 _28537)). Qed.
Lemma lem2258630 (a : Prop) : (term145 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem2258631 (_28537 : real) (_28536 : real) : (term165 _28537 _28536) = ((term68 _28537) = _28536).
Proof. exact (@lem2258630 ((term68 _28537) = _28536)). Qed.
Lemma lem2258632 (_28537 : real) (_28536 : real) : (term160 _28537 _28536) = (term17 _28537 _28536).
Proof. exact (MK_COMB (@lem2258628 _28537) (@lem2258631 _28537 _28536)). Qed.
Lemma lem2258633 (_28537 : real) (_28536 : real) : (term159 _28537 _28536) = (term17 _28537 _28536).
Proof. exact (TRANS (@lem2258623 _28537 _28536) (@lem2258632 _28537 _28536)). Qed.
Lemma lem2258634 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2258635 (_28537 : real) (_28536 : real) : (term166 _28537 _28536) = (term167 _28537 _28536).
Proof. exact (MK_COMB (@lem2258634) (@lem2258633 _28537 _28536)). Qed.
Lemma lem2258636 (_28536 : real) (_28537 : real) : ((term16 _28536) = _28537) = ((term16 _28536) = _28537).
Proof. exact (eq_refl ((term16 _28536) = _28537)). Qed.
Lemma lem2258637 (_28536 : real) (_28537 : real) : (term156 _28536 _28537) = (term168 _28536 _28537).
Proof. exact (MK_COMB (@lem2258635 _28537 _28536) (@lem2258636 _28536 _28537)). Qed.
Lemma lem2258638 (_28536 : real) (_28537 : real) : (term72 _28537 _28536) = (term168 _28536 _28537).
Proof. exact (TRANS (@lem2258620 _28536 _28537) (@lem2258637 _28536 _28537)). Qed.
Lemma lem2258640 (x : real) (h1 : term50 x) : term169 x.
Proof. exact (conj (@lem2258609 x h1) (@lem2258617 x)). Qed.
Lemma lem2258642 (_28536 : real) (_28537 : real) (h1 : term10) : term168 _28536 _28537.
Proof. exact (EQ_MP (@lem2258638 _28536 _28537) (@lem2258307 _28537 _28536 h1)). Qed.
Lemma lem2258643 (x : real) (h1 : term10) : term170 x.
Proof. exact (@lem2258642 (term68 x) x h1). Qed.
Lemma lem2258646 (x : real) (h1 : term10) (h2 : term50 x) : (term24 x) = x.
Proof. exact (@lem2258643 x h1 (@lem2258640 x h2)). Qed.
Lemma lem2258647 (x : real) (h1 : term10) (h2 : term50 x) : term138 x.
Proof. exact (fun h0 : term137 x => @lem2258646 x h1 h2). Qed.
Lemma lem2258649 (p : Prop) : (term139 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2258650 (x : real) : (term138 x) = ((term24 x) = x).
Proof. exact (@lem2258649 ((term24 x) = x)). Qed.
Lemma lem2258651 (x : real) (h1 : term10) (h2 : term50 x) : (term24 x) = x.
Proof. exact (EQ_MP (@lem2258650 x) (@lem2258647 x h1 h2)). Qed.
Lemma lem2258654 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem2258656 (x : real) : (term137 x) = (term171 x).
Proof. exact (@lem2258654 ((term24 x) = x)). Qed.
Lemma lem2258659 (x : real) (h1 : term50 x) : term171 x.
Proof. exact (EQ_MP (@lem2258656 x) (@lem2258309 x h1)). Qed.
Lemma lem2258662 (x : real) (h1 : term10) (h2 : term50 x) : False.
Proof. exact (@lem2258659 x h2 (@lem2258651 x h1 h2)). Qed.
Lemma lem2258663 (x : real) (h1 : term10) (h2 : term50 x) : term153.
Proof. exact (fun h0 : ~ False => @lem2258662 x h1 h2). Qed.
Lemma lem2258665 (p : Prop) : (term139 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2258666 : term153 = False.
Proof. exact (@lem2258665 False). Qed.
Lemma lem2258667 (x : real) (h1 : term10) (h2 : term50 x) : False.
Proof. exact (EQ_MP (@lem2258666) (@lem2258663 x h1 h2)). Qed.
Lemma lem2258668 (x : real) (h1 : term10) (h2 : term28 x) : False.
Proof. exact (or_elim (@lem2258099 x h2) (fun h0 : term46 x => @lem2258502 x h1 h0) (fun h0 : term50 x => @lem2258667 x h1 h0)). Qed.
Lemma lem2258669 (x : real) (h1 : term10) (h2 : term28 x) : (term28 x) = False.
Proof. exact (prop_ext (fun h3 : term28 x => @lem2258668 x h1 h2) (fun h3 : False => @lem2258099 x h2)). Qed.
Lemma lem2258670 (x : real) (h1 : term10) (h2 : term28 x) : False.
Proof. exact (EQ_MP (@lem2258669 x h1 h2) (@lem2258099 x h2)). Qed.
Lemma lem2258671 (h1 : term10) (h2 : term3) : False.
Proof. exact (ex_elim (@lem2257465 h2) (fun x : real => fun h0 : term35 x => @lem2258670 x h1 h0)). Qed.
Lemma lem2258672 (h1 : term3) : term8.
Proof. exact (fun h0 : term10 => @lem2258671 h0 h1). Qed.
Lemma lem2258673 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem2258674 (h1 : term3) : term9.
Proof. exact (EQ_MP (@lem2258673) (@lem2258672 h1)). Qed.
Lemma lem2258675 (h1 : term3) : term13.
Proof. exact (fun h0 : term23 => @lem2258674 h1). Qed.
Lemma lem2258676 : term15.
Proof. exact (fun h0 : term3 => @lem2258675 h0). Qed.
Lemma lem2258677 : term4.
Proof. exact (EQ_MP (@lem2257284) (@lem2258676)). Qed.
Lemma lem2258679 : term4.
Proof. exact (@lem2257176 (@lem2258677)). Qed.
Lemma lem2258680 (h1 : term3) : term12.
Proof. exact (@lem2258679 (@lem2257161 h1)). Qed.
Lemma lem2258681 (h1 : term3) : term8.
Proof. exact (@lem2258680 h1 (@lem2004769)). Qed.
Lemma lem2258682 (h1 : term3) : False.
Proof. exact (@lem2258681 h1 (@lem2256133)). Qed.
Lemma lem2258683 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem2258682 h1) (fun h2 : False => @lem2257161 h1)). Qed.
Lemma lem2258684 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem2258683 h1) (@lem2257161 h1)). Qed.
Lemma lem2258685 : term2.
Proof. exact (fun h0 : term3 => @lem2258684 h0). Qed.
Lemma lem2258686 : term1.
Proof. exact (EQ_MP (@lem2257160) (@lem2258685)). Qed.
