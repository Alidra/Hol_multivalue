Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ABS_BOUND_term_abbrevs.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1482704_spec.
Require Import thm1483436_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483460_spec.
Require Import thm1483476_spec.
Require Import thm1483480_spec.
Require Import thm1483484_spec.
Require Import thm1483488_spec.
Require Import thm1483508_spec.
Require Import thm1483519_spec.
Require Import thm1483521_spec.
Require Import thm1483531_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem1539173 (y : real) (x : real) (d : real) : (term0 y x d) = (term1 y x d).
Proof. exact (@lem17362 (term2 x y d) (term3 y x d)). Qed.
Lemma lem1539174 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1539175 (y : real) (x : real) : (term6 y x) = (term7 y x).
Proof. exact (@lem1539174 (term8 y x)). Qed.
Lemma lem1539176 (y : real) (x : real) (d : real) : (term9 y x d) = (term10 y x d).
Proof. exact (eq_refl (term9 y x d)). Qed.
Lemma lem1539177 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1539178 (y : real) (x : real) (d : real) : (term11 y x d) = (term0 y x d).
Proof. exact (MK_COMB (@lem1539177) (@lem1539176 y x d)). Qed.
Lemma lem1539179 (y : real) (x : real) (d : real) : (term11 y x d) = (term1 y x d).
Proof. exact (TRANS (@lem1539178 y x d) (@lem1539173 y x d)). Qed.
Lemma lem1539180 (y : real) (x : real) : (term12 y x) = (term13 y x).
Proof. exact (fun_ext (fun d : real => @lem1539179 y x d)). Qed.
Lemma lem1539181 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1539182 (y : real) (x : real) : (term7 y x) = (term14 y x).
Proof. exact (MK_COMB (@lem1539181) (@lem1539180 y x)). Qed.
Lemma lem1539183 (y : real) (x : real) : (term6 y x) = (term14 y x).
Proof. exact (TRANS (@lem1539175 y x) (@lem1539182 y x)). Qed.
Lemma lem1539184 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1539185 (x : real) : (term15 x) = (term16 x).
Proof. exact (@lem1539184 (term17 x)). Qed.
Lemma lem1539186 (y : real) (x : real) : (term18 x y) = (term19 y x).
Proof. exact (eq_refl (term18 x y)). Qed.
Lemma lem1539187 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1539188 (y : real) (x : real) : (term20 x y) = (term6 y x).
Proof. exact (MK_COMB (@lem1539187) (@lem1539186 y x)). Qed.
Lemma lem1539189 (y : real) (x : real) : (term20 x y) = (term14 y x).
Proof. exact (TRANS (@lem1539188 y x) (@lem1539183 y x)). Qed.
Lemma lem1539190 (x : real) : (term21 x) = (term22 x).
Proof. exact (fun_ext (fun y : real => @lem1539189 y x)). Qed.
Lemma lem1539191 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1539192 (x : real) : (term16 x) = (term23 x).
Proof. exact (MK_COMB (@lem1539191) (@lem1539190 x)). Qed.
Lemma lem1539193 (x : real) : (term15 x) = (term23 x).
Proof. exact (TRANS (@lem1539185 x) (@lem1539192 x)). Qed.
Lemma lem1539194 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1539195 : term24 = term25.
Proof. exact (@lem1539194 term26). Qed.
Lemma lem1539196 (x : real) : (term27 x) = (term28 x).
Proof. exact (eq_refl (term27 x)). Qed.
Lemma lem1539197 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1539198 (x : real) : (term29 x) = (term15 x).
Proof. exact (MK_COMB (@lem1539197) (@lem1539196 x)). Qed.
Lemma lem1539199 (x : real) : (term29 x) = (term23 x).
Proof. exact (TRANS (@lem1539198 x) (@lem1539193 x)). Qed.
Lemma lem1539200 : term30 = term31.
Proof. exact (fun_ext (fun x : real => @lem1539199 x)). Qed.
Lemma lem1539201 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1539202 : term25 = term32.
Proof. exact (MK_COMB (@lem1539201) (@lem1539200)). Qed.
Lemma lem1539204 : term24 = term32.
Proof. exact (TRANS (@lem1539195) (@lem1539202)). Qed.
Lemma lem1539211 (y : real) (x : real) (d : real) : (term1 y x d) = (term1 y x d).
Proof. exact (eq_refl (term1 y x d)). Qed.
Lemma lem1539212 (y : real) (x : real) : (term13 y x) = (term13 y x).
Proof. exact (fun_ext (fun d : real => @lem1539211 y x d)). Qed.
Lemma lem1539213 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1539214 (y : real) (x : real) : (term14 y x) = (term14 y x).
Proof. exact (MK_COMB (@lem1539213) (@lem1539212 y x)). Qed.
Lemma lem1539215 (x : real) : (term22 x) = (term22 x).
Proof. exact (fun_ext (fun y : real => @lem1539214 y x)). Qed.
Lemma lem1539216 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1539217 (x : real) : (term23 x) = (term23 x).
Proof. exact (MK_COMB (@lem1539216) (@lem1539215 x)). Qed.
Lemma lem1539218 : term31 = term31.
Proof. exact (fun_ext (fun x : real => @lem1539217 x)). Qed.
Lemma lem1539219 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1539220 : term32 = term32.
Proof. exact (MK_COMB (@lem1539219) (@lem1539218)). Qed.
Lemma lem1539221 : term24 = term32.
Proof. exact (TRANS (@lem1539204) (@lem1539220)). Qed.
Lemma lem1539222 (d : real) (x : real) (y : real) : (term2 x y d) = (term33 d x y).
Proof. exact (@lem1483521 d (term34 x y)). Qed.
Lemma lem1539235 (d : real) (x : real) (y : real) : (term35 d x y) = (term36 d x y).
Proof. exact (@lem1483519 d (term34 x y)). Qed.
Lemma lem1539236 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1539237 (d : real) (x : real) (y : real) : (term37 d x y) = (term38 d x y).
Proof. exact (MK_COMB (@lem1539236) (@lem1539235 d x y)). Qed.
Lemma lem1539238 : term39 = term39.
Proof. exact (eq_refl term39). Qed.
Lemma lem1539239 (d : real) (x : real) (y : real) : (term33 d x y) = (term40 d x y).
Proof. exact (MK_COMB (@lem1539237 d x y) (@lem1539238)). Qed.
Lemma lem1539240 (d : real) (x : real) (y : real) : (term2 x y d) = (term40 d x y).
Proof. exact (TRANS (@lem1539222 d x y) (@lem1539239 d x y)). Qed.
Lemma lem1539241 (y : real) (x : real) (d : real) : (term41 y x d) = (term42 y x d).
Proof. exact (@lem1483531 y (real_add x d)). Qed.
Lemma lem1539248 (d : real) (x : real) : (real_add x d) = (real_add d x).
Proof. exact (@lem1483488 d x). Qed.
Lemma lem1539251 (y : real) : (real_sub y) = (real_sub y).
Proof. exact (eq_refl (real_sub y)). Qed.
Lemma lem1539252 (y : real) (d : real) (x : real) : (term43 y x d) = (term43 y d x).
Proof. exact (MK_COMB (@lem1539251 y) (@lem1539248 d x)). Qed.
Lemma lem1539253 (y : real) (d : real) (x : real) : (term43 y d x) = (term44 y d x).
Proof. exact (@lem1483519 y (real_add d x)). Qed.
Lemma lem1539260 (d : real) (x : real) : (term45 d x) = (term46 d x).
Proof. exact (@lem1483508 d term47 x). Qed.
Lemma lem1539261 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1539262 (y : real) (d : real) (x : real) : (term44 y d x) = (term48 y d x).
Proof. exact (MK_COMB (@lem1539261 y) (@lem1539260 d x)). Qed.
Lemma lem1539263 (d : real) (y : real) (x : real) : (term48 y d x) = (term49 d y x).
Proof. exact (@lem1483484 (term50 d) y (term50 x)). Qed.
Lemma lem1539264 (x : real) (y : real) : (term51 y x) = (term52 x y).
Proof. exact (@lem1483488 (term50 x) y). Qed.
Lemma lem1539265 (d : real) : (term53 d) = (term53 d).
Proof. exact (eq_refl (term53 d)). Qed.
Lemma lem1539266 (d : real) (x : real) (y : real) : (term49 d y x) = (term54 d x y).
Proof. exact (MK_COMB (@lem1539265 d) (@lem1539264 x y)). Qed.
Lemma lem1539267 (d : real) (x : real) (y : real) : (term48 y d x) = (term54 d x y).
Proof. exact (TRANS (@lem1539263 d y x) (@lem1539266 d x y)). Qed.
Lemma lem1539268 (d : real) (x : real) (y : real) : (term44 y d x) = (term54 d x y).
Proof. exact (TRANS (@lem1539262 y d x) (@lem1539267 d x y)). Qed.
Lemma lem1539269 (d : real) (x : real) (y : real) : (term43 y d x) = (term54 d x y).
Proof. exact (TRANS (@lem1539253 y d x) (@lem1539268 d x y)). Qed.
Lemma lem1539270 (d : real) (x : real) (y : real) : (term43 y x d) = (term54 d x y).
Proof. exact (TRANS (@lem1539252 y d x) (@lem1539269 d x y)). Qed.
Lemma lem1539271 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1539272 (d : real) (x : real) (y : real) : (term55 y x d) = (term56 d x y).
Proof. exact (MK_COMB (@lem1539271) (@lem1539270 d x y)). Qed.
Lemma lem1539273 : term39 = term39.
Proof. exact (eq_refl term39). Qed.
Lemma lem1539274 (d : real) (x : real) (y : real) : (term42 y x d) = (term57 d x y).
Proof. exact (MK_COMB (@lem1539272 d x y) (@lem1539273)). Qed.
Lemma lem1539275 (d : real) (x : real) (y : real) : (term41 y x d) = (term57 d x y).
Proof. exact (TRANS (@lem1539241 y x d) (@lem1539274 d x y)). Qed.
Lemma lem1539276 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1539277 (d : real) (x : real) (y : real) : (term58 x y d) = (term59 d x y).
Proof. exact (MK_COMB (@lem1539276) (@lem1539240 d x y)). Qed.
Lemma lem1539278 (d : real) (x : real) (y : real) : (term1 y x d) = (term60 d x y).
Proof. exact (MK_COMB (@lem1539277 d x y) (@lem1539275 d x y)). Qed.
Lemma lem1539279 (x : real) (y : real) : (term13 y x) = (term61 x y).
Proof. exact (fun_ext (fun d : real => @lem1539278 d x y)). Qed.
Lemma lem1539280 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1539281 (x : real) (y : real) : (term14 y x) = (term62 x y).
Proof. exact (MK_COMB (@lem1539280) (@lem1539279 x y)). Qed.
Lemma lem1539282 (x : real) : (term22 x) = (term63 x).
Proof. exact (fun_ext (fun y : real => @lem1539281 x y)). Qed.
Lemma lem1539283 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1539284 (x : real) : (term23 x) = (term64 x).
Proof. exact (MK_COMB (@lem1539283) (@lem1539282 x)). Qed.
Lemma lem1539285 : term31 = term65.
Proof. exact (fun_ext (fun x : real => @lem1539284 x)). Qed.
Lemma lem1539286 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1539287 : term32 = term66.
Proof. exact (MK_COMB (@lem1539286) (@lem1539285)). Qed.
Lemma lem1539350 : term24 = term66.
Proof. exact (TRANS (@lem1539221) (@lem1539287)). Qed.
Lemma lem1539357 (d : real) (x : real) (y : real) : (term60 d x y) = (term60 d x y).
Proof. exact (eq_refl (term60 d x y)). Qed.
Lemma lem1539358 (x : real) (y : real) : (term61 x y) = (term61 x y).
Proof. exact (fun_ext (fun d : real => @lem1539357 d x y)). Qed.
Lemma lem1539359 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1539360 (x : real) (y : real) : (term62 x y) = (term62 x y).
Proof. exact (MK_COMB (@lem1539359) (@lem1539358 x y)). Qed.
Lemma lem1539361 (x : real) : (term63 x) = (term63 x).
Proof. exact (fun_ext (fun y : real => @lem1539360 x y)). Qed.
Lemma lem1539362 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1539363 (x : real) : (term64 x) = (term64 x).
Proof. exact (MK_COMB (@lem1539362) (@lem1539361 x)). Qed.
Lemma lem1539364 : term65 = term65.
Proof. exact (fun_ext (fun x : real => @lem1539363 x)). Qed.
Lemma lem1539365 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1539366 : term66 = term66.
Proof. exact (MK_COMB (@lem1539365) (@lem1539364)). Qed.
Lemma lem1539367 : term24 = term66.
Proof. exact (TRANS (@lem1539350) (@lem1539366)). Qed.
Lemma lem1539369 (a : real) (x : real) (r : real) : (term67 a x r) = (term68 a x r).
Proof. exact (proj1 (@lem1482704 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1539370 (d : real) (x : real) (y : real) : (term40 d x y) = (term69 d x y).
Proof. exact (@lem1539369 d (real_sub x y) term39). Qed.
Lemma lem1539383 (x : real) (y : real) : (real_sub x y) = (term51 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1539386 : term70 = term70.
Proof. exact (eq_refl term70). Qed.
Lemma lem1539387 (x : real) (y : real) : (term71 x y) = (term72 x y).
Proof. exact (MK_COMB (@lem1539386) (@lem1539383 x y)). Qed.
Lemma lem1539388 (x : real) (y : real) : (term72 x y) = (term51 x y).
Proof. exact (@lem1483460 (term51 x y)). Qed.
Lemma lem1539389 (x : real) (y : real) : (term71 x y) = (term51 x y).
Proof. exact (TRANS (@lem1539387 x y) (@lem1539388 x y)). Qed.
Lemma lem1539392 (d : real) : (real_add d) = (real_add d).
Proof. exact (eq_refl (real_add d)). Qed.
Lemma lem1539395 (d : real) (x : real) (y : real) : (term73 d x y) = (term74 d x y).
Proof. exact (MK_COMB (@lem1539392 d) (@lem1539389 x y)). Qed.
Lemma lem1539396 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1539397 (d : real) (x : real) (y : real) : (term75 d x y) = (term76 d x y).
Proof. exact (MK_COMB (@lem1539396) (@lem1539395 d x y)). Qed.
Lemma lem1539398 : term39 = term39.
Proof. exact (eq_refl term39). Qed.
Lemma lem1539399 (d : real) (x : real) (y : real) : (term77 d x y) = (term78 d x y).
Proof. exact (MK_COMB (@lem1539397 d x y) (@lem1539398)). Qed.
Lemma lem1539412 (x : real) (y : real) : (real_sub x y) = (term51 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1539415 : term79 = term79.
Proof. exact (eq_refl term79). Qed.
Lemma lem1539416 (x : real) (y : real) : (term80 x y) = (term81 x y).
Proof. exact (MK_COMB (@lem1539415) (@lem1539412 x y)). Qed.
Lemma lem1539417 (x : real) (y : real) : (term81 x y) = (term82 x y).
Proof. exact (@lem1483508 x term47 (term50 y)). Qed.
Lemma lem1539418 (y : real) : (term83 y) = (term84 y).
Proof. exact (@lem1483476 term47 term47 y). Qed.
Lemma lem1539420 (m : nat) (n : nat) : (term85 m n) = (term86 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1539421 : term87 = term88.
Proof. exact (@lem1539420 term89 term89). Qed.
Lemma lem1539422 : (term90 = (BIT1 0)) = (term91 = term89).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1539423 : term91 = term89.
Proof. exact (EQ_MP (@lem1539422) (@lem940073)). Qed.
Lemma lem1539424 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1539425 : term88 = term92.
Proof. exact (MK_COMB (@lem1539424) (@lem1539423)). Qed.
Lemma lem1539426 : term87 = term92.
Proof. exact (TRANS (@lem1539421) (@lem1539425)). Qed.
Lemma lem1539427 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1539428 : term93 = term70.
Proof. exact (MK_COMB (@lem1539427) (@lem1539426)). Qed.
Lemma lem1539429 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1539430 (y : real) : (term84 y) = (term94 y).
Proof. exact (MK_COMB (@lem1539428) (@lem1539429 y)). Qed.
Lemma lem1539431 (y : real) : (term83 y) = (term94 y).
Proof. exact (TRANS (@lem1539418 y) (@lem1539430 y)). Qed.
Lemma lem1539432 (y : real) : (term94 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1539433 (y : real) : (term83 y) = y.
Proof. exact (TRANS (@lem1539431 y) (@lem1539432 y)). Qed.
Lemma lem1539436 (x : real) : (term53 x) = (term53 x).
Proof. exact (eq_refl (term53 x)). Qed.
Lemma lem1539437 (x : real) (y : real) : (term82 x y) = (term52 x y).
Proof. exact (MK_COMB (@lem1539436 x) (@lem1539433 y)). Qed.
Lemma lem1539438 (x : real) (y : real) : (term81 x y) = (term52 x y).
Proof. exact (TRANS (@lem1539417 x y) (@lem1539437 x y)). Qed.
Lemma lem1539439 (x : real) (y : real) : (term80 x y) = (term52 x y).
Proof. exact (TRANS (@lem1539416 x y) (@lem1539438 x y)). Qed.
Lemma lem1539442 (d : real) : (real_add d) = (real_add d).
Proof. exact (eq_refl (real_add d)). Qed.
Lemma lem1539445 (d : real) (x : real) (y : real) : (term95 d x y) = (term96 d x y).
Proof. exact (MK_COMB (@lem1539442 d) (@lem1539439 x y)). Qed.
Lemma lem1539446 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1539447 (d : real) (x : real) (y : real) : (term97 d x y) = (term98 d x y).
Proof. exact (MK_COMB (@lem1539446) (@lem1539445 d x y)). Qed.
Lemma lem1539448 : term39 = term39.
Proof. exact (eq_refl term39). Qed.
Lemma lem1539449 (d : real) (x : real) (y : real) : (term99 d x y) = (term100 d x y).
Proof. exact (MK_COMB (@lem1539447 d x y) (@lem1539448)). Qed.
Lemma lem1539450 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1539451 (d : real) (x : real) (y : real) : (term101 d x y) = (term102 d x y).
Proof. exact (MK_COMB (@lem1539450) (@lem1539449 d x y)). Qed.
Lemma lem1539452 (d : real) (x : real) (y : real) : (term69 d x y) = (term103 d x y).
Proof. exact (MK_COMB (@lem1539451 d x y) (@lem1539399 d x y)). Qed.
Lemma lem1539453 (d : real) (x : real) (y : real) : (term40 d x y) = (term103 d x y).
Proof. exact (TRANS (@lem1539370 d x y) (@lem1539452 d x y)). Qed.
Lemma lem1539454 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1539455 (d : real) (x : real) (y : real) : (term59 d x y) = (term104 d x y).
Proof. exact (MK_COMB (@lem1539454) (@lem1539453 d x y)). Qed.
Lemma lem1539456 (d : real) (x : real) (y : real) : (term57 d x y) = (term57 d x y).
Proof. exact (eq_refl (term57 d x y)). Qed.
Lemma lem1539459 (d : real) (x : real) (y : real) : (term60 d x y) = (term105 d x y).
Proof. exact (MK_COMB (@lem1539455 d x y) (@lem1539456 d x y)). Qed.
Lemma lem1539460 (d : real) (x : real) (y : real) (h1 : term105 d x y) : term105 d x y.
Proof. exact (h1). Qed.
Lemma lem1539461 (d : real) (x : real) (y : real) (h1 : term105 d x y) : term57 d x y.
Proof. exact (proj2 (@lem1539460 d x y h1)). Qed.
Lemma lem1539462 (d : real) (x : real) (y : real) (h1 : term105 d x y) : term103 d x y.
Proof. exact (proj1 (@lem1539460 d x y h1)). Qed.
Lemma lem1539463 (d : real) (x : real) (y : real) (h1 : term105 d x y) : term78 d x y.
Proof. exact (proj2 (@lem1539462 d x y h1)). Qed.
Lemma lem1539466 (n : nat) (m : nat) : (term106 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1539467 : term107 = term108.
Proof. exact (@lem1539466 (NUMERAL 0) term89). Qed.
Lemma lem1539468 : term109 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1539469 (h1 : term109 = (BIT1 0)) : term108 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1539470 : (term109 = (BIT1 0)) = (term108 = True).
Proof. exact (prop_ext (fun h1 : term109 = (BIT1 0) => @lem1539469 h1) (fun h1 : term108 = True => @lem1539468)). Qed.
Lemma lem1539471 : term108 = True.
Proof. exact (EQ_MP (@lem1539470) (@lem1539468)). Qed.
Lemma lem1539472 : term107 = True.
Proof. exact (TRANS (@lem1539467) (@lem1539471)). Qed.
Lemma lem1539473 : True = term107.
Proof. exact (SYM (@lem1539472)). Qed.
Lemma lem1539474 : term107.
Proof. exact (EQ_MP (@lem1539473) (@lem0)). Qed.
Lemma lem1539475 (d : real) (x : real) (y : real) (h1 : term105 d x y) : term110 d x y.
Proof. exact (conj (@lem1539474) (@lem1539461 d x y h1)). Qed.
Lemma lem1539477 (x : real) (y : real) : term111 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1539478 (d : real) (x : real) (y : real) : term112 d x y.
Proof. exact (@lem1539477 term92 (term54 d x y)). Qed.
Lemma lem1539479 (d : real) (x : real) (y : real) (h1 : term105 d x y) : term113 d x y.
Proof. exact (@lem1539478 d x y (@lem1539475 d x y h1)). Qed.
Lemma lem1539480 (d : real) (x : real) (y : real) : (term114 d x y) = (term54 d x y).
Proof. exact (@lem1483460 (term54 d x y)). Qed.
Lemma lem1539481 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1539482 (d : real) (x : real) (y : real) : (term115 d x y) = (term56 d x y).
Proof. exact (MK_COMB (@lem1539481) (@lem1539480 d x y)). Qed.
Lemma lem1539483 : term39 = term39.
Proof. exact (eq_refl term39). Qed.
Lemma lem1539484 (d : real) (x : real) (y : real) : (term113 d x y) = (term57 d x y).
Proof. exact (MK_COMB (@lem1539482 d x y) (@lem1539483)). Qed.
Lemma lem1539485 (d : real) (x : real) (y : real) (h1 : term105 d x y) : term57 d x y.
Proof. exact (EQ_MP (@lem1539484 d x y) (@lem1539479 d x y h1)). Qed.
Lemma lem1539487 (n : nat) (m : nat) : (term106 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1539488 : term107 = term108.
Proof. exact (@lem1539487 (NUMERAL 0) term89). Qed.
Lemma lem1539489 : term109 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1539490 (h1 : term109 = (BIT1 0)) : term108 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1539491 : (term109 = (BIT1 0)) = (term108 = True).
Proof. exact (prop_ext (fun h1 : term109 = (BIT1 0) => @lem1539490 h1) (fun h1 : term108 = True => @lem1539489)). Qed.
Lemma lem1539492 : term108 = True.
Proof. exact (EQ_MP (@lem1539491) (@lem1539489)). Qed.
Lemma lem1539493 : term107 = True.
Proof. exact (TRANS (@lem1539488) (@lem1539492)). Qed.
Lemma lem1539494 : True = term107.
Proof. exact (SYM (@lem1539493)). Qed.
Lemma lem1539495 : term107.
Proof. exact (EQ_MP (@lem1539494) (@lem0)). Qed.
Lemma lem1539496 (d : real) (x : real) (y : real) (h1 : term105 d x y) : term116 d x y.
Proof. exact (conj (@lem1539495) (@lem1539463 d x y h1)). Qed.
Lemma lem1539498 (x : real) (y : real) : term117 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1539499 (d : real) (x : real) (y : real) : term118 d x y.
Proof. exact (@lem1539498 term92 (term74 d x y)). Qed.
Lemma lem1539500 (d : real) (x : real) (y : real) (h1 : term105 d x y) : term119 d x y.
Proof. exact (@lem1539499 d x y (@lem1539496 d x y h1)). Qed.
Lemma lem1539501 (d : real) (x : real) (y : real) : (term120 d x y) = (term74 d x y).
Proof. exact (@lem1483460 (term74 d x y)). Qed.
Lemma lem1539502 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1539503 (d : real) (x : real) (y : real) : (term121 d x y) = (term76 d x y).
Proof. exact (MK_COMB (@lem1539502) (@lem1539501 d x y)). Qed.
Lemma lem1539504 : term39 = term39.
Proof. exact (eq_refl term39). Qed.
Lemma lem1539505 (d : real) (x : real) (y : real) : (term119 d x y) = (term78 d x y).
Proof. exact (MK_COMB (@lem1539503 d x y) (@lem1539504)). Qed.
Lemma lem1539506 (d : real) (x : real) (y : real) (h1 : term105 d x y) : term78 d x y.
Proof. exact (EQ_MP (@lem1539505 d x y) (@lem1539500 d x y h1)). Qed.
Lemma lem1539507 (d : real) (x : real) (y : real) (h1 : term105 d x y) : term122 d x y.
Proof. exact (conj (@lem1539506 d x y h1) (@lem1539485 d x y h1)). Qed.
Lemma lem1539509 (x : real) (y : real) : term123 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1539510 (d : real) (x : real) (y : real) : term124 d x y.
Proof. exact (@lem1539509 (term74 d x y) (term54 d x y)). Qed.
Lemma lem1539511 (d : real) (x : real) (y : real) (h1 : term105 d x y) : term125 d x y.
Proof. exact (@lem1539510 d x y (@lem1539507 d x y h1)). Qed.
Lemma lem1539512 (d : real) (x : real) (y : real) : (term126 d x y) = (term127 d x y).
Proof. exact (@lem1483480 d (term50 d) (term51 x y) (term52 x y)). Qed.
Lemma lem1539513 (d : real) : (term128 d) = (term129 d).
Proof. exact (@lem1483442 term47 d). Qed.
Lemma lem1539515 (m : nat) : (term130 m) = term39.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1539516 : term131 = term39.
Proof. exact (@lem1539515 term89). Qed.
Lemma lem1539517 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1539518 : term132 = term133.
Proof. exact (MK_COMB (@lem1539517) (@lem1539516)). Qed.
Lemma lem1539519 (d : real) : d = d.
Proof. exact (eq_refl d). Qed.
Lemma lem1539520 (d : real) : (term129 d) = (term134 d).
Proof. exact (MK_COMB (@lem1539518) (@lem1539519 d)). Qed.
Lemma lem1539521 (d : real) : (term128 d) = (term134 d).
Proof. exact (TRANS (@lem1539513 d) (@lem1539520 d)). Qed.
Lemma lem1539522 (d : real) : (term134 d) = term39.
Proof. exact (@lem1483446 d). Qed.
Lemma lem1539523 (d : real) : (term128 d) = term39.
Proof. exact (TRANS (@lem1539521 d) (@lem1539522 d)). Qed.
Lemma lem1539524 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1539525 (d : real) : (term135 d) = term136.
Proof. exact (MK_COMB (@lem1539524) (@lem1539523 d)). Qed.
Lemma lem1539526 (x : real) (y : real) : (term137 x y) = (term138 x y).
Proof. exact (@lem1483480 x (term50 x) (term50 y) y). Qed.
Lemma lem1539527 (x : real) : (term128 x) = (term129 x).
Proof. exact (@lem1483442 term47 x). Qed.
Lemma lem1539529 (m : nat) : (term130 m) = term39.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1539530 : term131 = term39.
Proof. exact (@lem1539529 term89). Qed.
Lemma lem1539531 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1539532 : term132 = term133.
Proof. exact (MK_COMB (@lem1539531) (@lem1539530)). Qed.
Lemma lem1539533 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1539534 (x : real) : (term129 x) = (term134 x).
Proof. exact (MK_COMB (@lem1539532) (@lem1539533 x)). Qed.
Lemma lem1539535 (x : real) : (term128 x) = (term134 x).
Proof. exact (TRANS (@lem1539527 x) (@lem1539534 x)). Qed.
Lemma lem1539536 (x : real) : (term134 x) = term39.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1539537 (x : real) : (term128 x) = term39.
Proof. exact (TRANS (@lem1539535 x) (@lem1539536 x)). Qed.
Lemma lem1539538 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1539539 (x : real) : (term135 x) = term136.
Proof. exact (MK_COMB (@lem1539538) (@lem1539537 x)). Qed.
Lemma lem1539540 (y : real) : (term139 y) = (term129 y).
Proof. exact (@lem1483440 term47 y). Qed.
Lemma lem1539542 (m : nat) : (term130 m) = term39.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1539543 : term131 = term39.
Proof. exact (@lem1539542 term89). Qed.
Lemma lem1539544 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1539545 : term132 = term133.
Proof. exact (MK_COMB (@lem1539544) (@lem1539543)). Qed.
Lemma lem1539546 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1539547 (y : real) : (term129 y) = (term134 y).
Proof. exact (MK_COMB (@lem1539545) (@lem1539546 y)). Qed.
Lemma lem1539548 (y : real) : (term139 y) = (term134 y).
Proof. exact (TRANS (@lem1539540 y) (@lem1539547 y)). Qed.
Lemma lem1539549 (y : real) : (term134 y) = term39.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1539550 (y : real) : (term139 y) = term39.
Proof. exact (TRANS (@lem1539548 y) (@lem1539549 y)). Qed.
Lemma lem1539551 (x : real) (y : real) : (term138 x y) = term140.
Proof. exact (MK_COMB (@lem1539539 x) (@lem1539550 y)). Qed.
Lemma lem1539552 (x : real) (y : real) : (term137 x y) = term140.
Proof. exact (TRANS (@lem1539526 x y) (@lem1539551 x y)). Qed.
Lemma lem1539553 : term140 = term39.
Proof. exact (@lem1483448 term39). Qed.
Lemma lem1539554 (x : real) (y : real) : (term137 x y) = term39.
Proof. exact (TRANS (@lem1539552 x y) (@lem1539553)). Qed.
Lemma lem1539555 (d : real) (x : real) (y : real) : (term127 d x y) = term140.
Proof. exact (MK_COMB (@lem1539525 d) (@lem1539554 x y)). Qed.
Lemma lem1539556 (d : real) (x : real) (y : real) : (term126 d x y) = term140.
Proof. exact (TRANS (@lem1539512 d x y) (@lem1539555 d x y)). Qed.
Lemma lem1539557 : term140 = term39.
Proof. exact (@lem1483448 term39). Qed.
Lemma lem1539558 (d : real) (x : real) (y : real) : (term126 d x y) = term39.
Proof. exact (TRANS (@lem1539556 d x y) (@lem1539557)). Qed.
Lemma lem1539559 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1539560 (d : real) (x : real) (y : real) : (term141 d x y) = term142.
Proof. exact (MK_COMB (@lem1539559) (@lem1539558 d x y)). Qed.
Lemma lem1539561 : term39 = term39.
Proof. exact (eq_refl term39). Qed.
Lemma lem1539562 (d : real) (x : real) (y : real) : (term125 d x y) = term143.
Proof. exact (MK_COMB (@lem1539560 d x y) (@lem1539561)). Qed.
Lemma lem1539563 (d : real) (x : real) (y : real) (h1 : term105 d x y) : term143.
Proof. exact (EQ_MP (@lem1539562 d x y) (@lem1539511 d x y h1)). Qed.
Lemma lem1539565 (n : nat) (m : nat) : (term106 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1539566 : term143 = term144.
Proof. exact (@lem1539565 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1539567 : term144 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1539568 : term143 = False.
Proof. exact (TRANS (@lem1539566) (@lem1539567)). Qed.
Lemma lem1539569 (d : real) (x : real) (y : real) (h1 : term105 d x y) : False.
Proof. exact (EQ_MP (@lem1539568) (@lem1539563 d x y h1)). Qed.
Lemma lem1539570 (d : real) (x : real) (y : real) (h1 : term60 d x y) : term60 d x y.
Proof. exact (h1). Qed.
Lemma lem1539571 (d : real) (x : real) (y : real) (h1 : term60 d x y) : term105 d x y.
Proof. exact (EQ_MP (@lem1539459 d x y) (@lem1539570 d x y h1)). Qed.
Lemma lem1539572 (d : real) (x : real) (y : real) (h1 : term60 d x y) : (term105 d x y) = False.
Proof. exact (prop_ext (fun h2 : term105 d x y => @lem1539569 d x y h2) (fun h2 : False => @lem1539571 d x y h1)). Qed.
Lemma lem1539573 (d : real) (x : real) (y : real) (h1 : term60 d x y) : False.
Proof. exact (EQ_MP (@lem1539572 d x y h1) (@lem1539571 d x y h1)). Qed.
Lemma lem1539574 (x : real) (y : real) (h1 : term62 x y) : term62 x y.
Proof. exact (h1). Qed.
Lemma lem1539575 (x : real) (y : real) (h1 : term62 x y) : False.
Proof. exact (ex_elim (@lem1539574 x y h1) (fun d : real => fun h0 : term61 x y d => @lem1539573 d x y h0)). Qed.
Lemma lem1539576 (x : real) (h1 : term64 x) : term64 x.
Proof. exact (h1). Qed.
Lemma lem1539577 (x : real) (h1 : term64 x) : False.
Proof. exact (ex_elim (@lem1539576 x h1) (fun y : real => fun h0 : term63 x y => @lem1539575 x y h0)). Qed.
Lemma lem1539578 (h1 : term66) : term66.
Proof. exact (h1). Qed.
Lemma lem1539579 (h1 : term66) : False.
Proof. exact (ex_elim (@lem1539578 h1) (fun x : real => fun h0 : term65 x => @lem1539577 x h0)). Qed.
Lemma lem1539580 (h1 : term24) : term24.
Proof. exact (h1). Qed.
Lemma lem1539581 (h1 : term24) : term66.
Proof. exact (EQ_MP (@lem1539367) (@lem1539580 h1)). Qed.
Lemma lem1539582 (h1 : term24) : term66 = False.
Proof. exact (prop_ext (fun h2 : term66 => @lem1539579 h2) (fun h2 : False => @lem1539581 h1)). Qed.
Lemma lem1539583 (h1 : term24) : False.
Proof. exact (EQ_MP (@lem1539582 h1) (@lem1539581 h1)). Qed.
Lemma lem1539584 : term145.
Proof. exact (fun h0 : term24 => @lem1539583 h0). Qed.
Lemma lem1539585 : term146.
Proof. exact (@lem1386578 term147). Qed.
Lemma lem1539586 : term147.
Proof. exact (@lem1539585 (@lem1539584)). Qed.
