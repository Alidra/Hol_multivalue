Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NOT_INT_REM_2_term_abbrevs.
Require Import AND_FORALL_THM_spec.
Require Import INT_REM_2_CASES_spec.
Require Import MONO_FORALL_spec.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1365105_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1366971_spec.
Require Import thm1366974_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367763_spec.
Require Import thm1367770_spec.
Require Import thm1367771_spec.
Require Import thm1386578_spec.
Require Import thm1393126_spec.
Require Import thm1396750_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm19158_spec.
Require Import thm19367_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980026_spec.
Require Import thm1980255_spec.
Require Import thm1980259_spec.
Require Import thm1980260_spec.
Require Import thm1980265_spec.
Require Import thm1980266_spec.
Require Import thm1980277_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982733_spec.
Require Import thm1982753_spec.
Require Import thm1982757_spec.
Require Import thm1982759_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988293_spec.
Require Import thm1988330_spec.
Require Import thm1988332_spec.
Require Import thm1988336_spec.
Require Import thm2318497_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318574_spec.
Require Import thm2318575_spec.
Require Import thm2318604_spec.
Require Import thm7_spec.
Require Import thm706885_spec.
Require Import thm912739_spec.
Require Import thm912803_spec.
Require Import thm940073_spec.
Require Import thm996237_spec.
Require Import thm996238_spec.
Lemma lem2716253 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (h1). Qed.
Lemma lem2716254 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term1 A P Q) : term1 A P Q.
Proof. exact (h1). Qed.
Lemma lem2716255 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term1 A P Q) (h2 : term0 A P Q) : term2 A P Q.
Proof. exact (@lem2716253 A P Q h2 (@lem2716254 A P Q h1)). Qed.
Lemma lem2716256 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term1 A P Q) : term3 A P Q.
Proof. exact (fun h0 : term0 A P Q => @lem2716255 A P Q h1 h0). Qed.
Lemma lem2716257 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (h1). Qed.
Lemma lem2716258 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term1 A P Q) (h2 : term0 A P Q) : term2 A P Q.
Proof. exact (@lem2716256 A P Q h1 (@lem2716257 A P Q h2)). Qed.
Lemma lem2716259 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (fun h0 : term1 A P Q => @lem2716258 A P Q h0 h1). Qed.
Lemma lem2716260 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term4 A P Q.
Proof. exact (fun h0 : term0 A P Q => @lem2716259 A P Q h0). Qed.
Lemma lem2716262 {A : Type'} (P : A -> Prop) : term5 A P.
Proof. exact (@lem5146 A P). Qed.
Lemma lem2716263 {A : Type'} (P : A -> Prop) : (term5 A P) = (term6 A P).
Proof. exact (eq_refl (term5 A P)). Qed.
Lemma lem2716264 {A : Type'} (P : A -> Prop) : term6 A P.
Proof. exact (EQ_MP (@lem2716263 A P) (@lem2716262 A P)). Qed.
Lemma lem2716265 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term7 A P Q.
Proof. exact (@lem2716264 A P Q). Qed.
Lemma lem2716266 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term7 A P Q) = ((term8 A P Q) = (term9 A P Q)).
Proof. exact (eq_refl (term7 A P Q)). Qed.
Lemma lem2716269 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term8 A P Q) = (term9 A P Q).
Proof. exact (EQ_MP (@lem2716266 A P Q) (@lem2716265 A P Q)). Qed.
Lemma lem2716270 (P : int -> Prop) (Q : int -> Prop) : (term10 P Q) = (term11 P Q).
Proof. exact (@lem2716269 int P Q). Qed.
Lemma lem2716271 : term12 = term13.
Proof. exact (@lem2716270 term14 term15). Qed.
Lemma lem2716272 (n : int) : (term16 n) = ((term17 n) = ((term18 n) = term19)).
Proof. exact (eq_refl (term16 n)). Qed.
Lemma lem2716273 : term20 = term14.
Proof. exact (fun_ext (fun n : int => @lem2716272 n)). Qed.
Lemma lem2716274 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2716275 : term21 = term22.
Proof. exact (MK_COMB (@lem2716274) (@lem2716273)). Qed.
Lemma lem2716276 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2716277 : term23 = term24.
Proof. exact (MK_COMB (@lem2716276) (@lem2716275)). Qed.
Lemma lem2716278 (n : int) : (term25 n) = ((term26 n) = ((term18 n) = term27)).
Proof. exact (eq_refl (term25 n)). Qed.
Lemma lem2716279 : term28 = term15.
Proof. exact (fun_ext (fun n : int => @lem2716278 n)). Qed.
Lemma lem2716280 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2716281 : term29 = term30.
Proof. exact (MK_COMB (@lem2716280) (@lem2716279)). Qed.
Lemma lem2716282 : term12 = term31.
Proof. exact (MK_COMB (@lem2716277) (@lem2716281)). Qed.
Lemma lem2716283 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2716284 : term32 = term33.
Proof. exact (MK_COMB (@lem2716283) (@lem2716282)). Qed.
Lemma lem2716285 (n : int) : (term16 n) = ((term17 n) = ((term18 n) = term19)).
Proof. exact (eq_refl (term16 n)). Qed.
Lemma lem2716286 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2716287 (n : int) : (term34 n) = (term35 n).
Proof. exact (MK_COMB (@lem2716286) (@lem2716285 n)). Qed.
Lemma lem2716288 (n : int) : (term25 n) = ((term26 n) = ((term18 n) = term27)).
Proof. exact (eq_refl (term25 n)). Qed.
Lemma lem2716289 (n : int) : (term36 n) = (term37 n).
Proof. exact (MK_COMB (@lem2716287 n) (@lem2716288 n)). Qed.
Lemma lem2716290 : term38 = term39.
Proof. exact (fun_ext (fun n : int => @lem2716289 n)). Qed.
Lemma lem2716291 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2716292 : term13 = term40.
Proof. exact (MK_COMB (@lem2716291) (@lem2716290)). Qed.
Lemma lem2716293 : (term12 = term13) = (term31 = term40).
Proof. exact (MK_COMB (@lem2716284) (@lem2716292)). Qed.
Lemma lem2716294 : term31 = term40.
Proof. exact (EQ_MP (@lem2716293) (@lem2716271)). Qed.
Lemma lem2716313 : term40 = term31.
Proof. exact (SYM (@lem2716294)). Qed.
Lemma lem2716315 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term0 A P Q.
Proof. exact (@lem2716260 A P Q (@lem7363 A P Q)). Qed.
Lemma lem2716316 (P : int -> Prop) (Q : int -> Prop) : term41 P Q.
Proof. exact (@lem2716315 int P Q). Qed.
Lemma lem2716317 : term42.
Proof. exact (@lem2716316 term43 term39). Qed.
Lemma lem2716318 (n : int) : (term44 n) = (term45 n).
Proof. exact (eq_refl (term44 n)). Qed.
Lemma lem2716319 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2716320 (n : int) : (term46 n) = (term47 n).
Proof. exact (MK_COMB (@lem2716319) (@lem2716318 n)). Qed.
Lemma lem2716321 (n : int) : (term48 n) = (term37 n).
Proof. exact (eq_refl (term48 n)). Qed.
Lemma lem2716322 (n : int) : (term49 n) = (term50 n).
Proof. exact (MK_COMB (@lem2716320 n) (@lem2716321 n)). Qed.
Lemma lem2716323 : term51 = term52.
Proof. exact (fun_ext (fun n : int => @lem2716322 n)). Qed.
Lemma lem2716324 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2716325 : term53 = term54.
Proof. exact (MK_COMB (@lem2716324) (@lem2716323)). Qed.
Lemma lem2716326 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2716327 : term55 = term56.
Proof. exact (MK_COMB (@lem2716326) (@lem2716325)). Qed.
Lemma lem2716328 (n : int) : (term44 n) = (term45 n).
Proof. exact (eq_refl (term44 n)). Qed.
Lemma lem2716329 : term57 = term43.
Proof. exact (fun_ext (fun n : int => @lem2716328 n)). Qed.
Lemma lem2716330 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2716331 : term58 = term59.
Proof. exact (MK_COMB (@lem2716330) (@lem2716329)). Qed.
Lemma lem2716332 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2716333 : term60 = term61.
Proof. exact (MK_COMB (@lem2716332) (@lem2716331)). Qed.
Lemma lem2716334 (n : int) : (term48 n) = (term37 n).
Proof. exact (eq_refl (term48 n)). Qed.
Lemma lem2716335 : term62 = term39.
Proof. exact (fun_ext (fun n : int => @lem2716334 n)). Qed.
Lemma lem2716336 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2716337 : term63 = term40.
Proof. exact (MK_COMB (@lem2716336) (@lem2716335)). Qed.
Lemma lem2716338 : term64 = term65.
Proof. exact (MK_COMB (@lem2716333) (@lem2716337)). Qed.
Lemma lem2716339 : term42 = term66.
Proof. exact (MK_COMB (@lem2716327) (@lem2716338)). Qed.
Lemma lem2716340 : term66.
Proof. exact (EQ_MP (@lem2716339) (@lem2716317)). Qed.
Lemma lem2716341 : term67 = term54.
Proof. exact (@lem2318604 term54). Qed.
Lemma lem2716365 (n : int) : (term68 n) = ((term18 n) = term27).
Proof. exact (@lem16933 ((term18 n) = term27)). Qed.
Lemma lem2716367 (n : int) : ((term18 n) = term19) = ((term18 n) = term19).
Proof. exact (eq_refl ((term18 n) = term19)). Qed.
Lemma lem2716368 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2716369 (n : int) : (term69 n) = (term70 n).
Proof. exact (MK_COMB (@lem2716368) (@lem2716365 n)). Qed.
Lemma lem2716370 (n : int) : (term71 n) = (term72 n).
Proof. exact (MK_COMB (@lem2716369 n) (@lem2716367 n)). Qed.
Lemma lem2716375 (n : int) : (term73 n) = (term73 n).
Proof. exact (eq_refl (term73 n)). Qed.
Lemma lem2716376 (n : int) : (term74 n) = (term75 n).
Proof. exact (MK_COMB (@lem2716375 n) (@lem2716370 n)). Qed.
Lemma lem2716377 (n : int) : (term76 n) = (term74 n).
Proof. exact (@lem17646 (term17 n) ((term18 n) = term19)). Qed.
Lemma lem2716378 (n : int) : (term76 n) = (term75 n).
Proof. exact (TRANS (@lem2716377 n) (@lem2716376 n)). Qed.
Lemma lem2716382 (n : int) : (term77 n) = ((term18 n) = term19).
Proof. exact (@lem16933 ((term18 n) = term19)). Qed.
Lemma lem2716384 (n : int) : ((term18 n) = term27) = ((term18 n) = term27).
Proof. exact (eq_refl ((term18 n) = term27)). Qed.
Lemma lem2716385 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2716386 (n : int) : (term78 n) = (term79 n).
Proof. exact (MK_COMB (@lem2716385) (@lem2716382 n)). Qed.
Lemma lem2716387 (n : int) : (term80 n) = (term81 n).
Proof. exact (MK_COMB (@lem2716386 n) (@lem2716384 n)). Qed.
Lemma lem2716392 (n : int) : (term82 n) = (term82 n).
Proof. exact (eq_refl (term82 n)). Qed.
Lemma lem2716393 (n : int) : (term83 n) = (term84 n).
Proof. exact (MK_COMB (@lem2716392 n) (@lem2716387 n)). Qed.
Lemma lem2716394 (n : int) : (term85 n) = (term83 n).
Proof. exact (@lem17646 (term26 n) ((term18 n) = term27)). Qed.
Lemma lem2716395 (n : int) : (term85 n) = (term84 n).
Proof. exact (TRANS (@lem2716394 n) (@lem2716393 n)). Qed.
Lemma lem2716396 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2716397 (n : int) : (term86 n) = (term87 n).
Proof. exact (MK_COMB (@lem2716396) (@lem2716378 n)). Qed.
Lemma lem2716398 (n : int) : (term88 n) = (term89 n).
Proof. exact (MK_COMB (@lem2716397 n) (@lem2716395 n)). Qed.
Lemma lem2716399 (n : int) : (term90 n) = (term88 n).
Proof. exact (@lem17045 ((term17 n) = ((term18 n) = term19)) ((term26 n) = ((term18 n) = term27))). Qed.
Lemma lem2716400 (n : int) : (term90 n) = (term89 n).
Proof. exact (TRANS (@lem2716399 n) (@lem2716398 n)). Qed.
Lemma lem2716402 (n : int) : (term91 n) = (term91 n).
Proof. exact (eq_refl (term91 n)). Qed.
Lemma lem2716403 (n : int) : (term92 n) = (term93 n).
Proof. exact (MK_COMB (@lem2716402 n) (@lem2716400 n)). Qed.
Lemma lem2716404 (n : int) : (term94 n) = (term92 n).
Proof. exact (@lem17362 (term45 n) (term37 n)). Qed.
Lemma lem2716405 (n : int) : (term94 n) = (term93 n).
Proof. exact (TRANS (@lem2716404 n) (@lem2716403 n)). Qed.
Lemma lem2716406 (P : int -> Prop) : (term95 P) = (term96 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2716407 : term97 = term98.
Proof. exact (@lem2716406 term52). Qed.
Lemma lem2716408 (n : int) : (term99 n) = (term50 n).
Proof. exact (eq_refl (term99 n)). Qed.
Lemma lem2716409 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2716410 (n : int) : (term100 n) = (term94 n).
Proof. exact (MK_COMB (@lem2716409) (@lem2716408 n)). Qed.
Lemma lem2716411 (n : int) : (term100 n) = (term93 n).
Proof. exact (TRANS (@lem2716410 n) (@lem2716405 n)). Qed.
Lemma lem2716412 : term101 = term102.
Proof. exact (fun_ext (fun n : int => @lem2716411 n)). Qed.
Lemma lem2716413 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2716414 : term98 = term103.
Proof. exact (MK_COMB (@lem2716413) (@lem2716412)). Qed.
Lemma lem2716416 : term97 = term103.
Proof. exact (TRANS (@lem2716407) (@lem2716414)). Qed.
Lemma lem2716461 (n : int) : (term93 n) = (term93 n).
Proof. exact (eq_refl (term93 n)). Qed.
Lemma lem2716462 : term102 = term102.
Proof. exact (fun_ext (fun n : int => @lem2716461 n)). Qed.
Lemma lem2716463 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2716464 : term103 = term103.
Proof. exact (MK_COMB (@lem2716463) (@lem2716462)). Qed.
Lemma lem2716465 : term97 = term103.
Proof. exact (TRANS (@lem2716416) (@lem2716464)). Qed.
Lemma lem2716468 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem2716469 (n : int) : ((term18 n) = term27) = ((term104 n) = term105).
Proof. exact (@lem2716468 (term18 n) term27). Qed.
Lemma lem2716473 (n : nat) : (term106 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2716474 : term105 = term107.
Proof. exact (@lem2716473 (NUMERAL 0)). Qed.
Lemma lem2716475 (n : int) : (term108 n) = (term108 n).
Proof. exact (eq_refl (term108 n)). Qed.
Lemma lem2716476 (n : int) : ((term104 n) = term105) = ((term104 n) = term107).
Proof. exact (MK_COMB (@lem2716475 n) (@lem2716474)). Qed.
Lemma lem2716478 (n : int) : ((term18 n) = term27) = ((term104 n) = term107).
Proof. exact (TRANS (@lem2716469 n) (@lem2716476 n)). Qed.
Lemma lem2716481 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem2716482 (n : int) : ((term18 n) = term19) = ((term104 n) = term109).
Proof. exact (@lem2716481 (term18 n) term19). Qed.
Lemma lem2716486 (n : nat) : (term106 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2716487 : term109 = term110.
Proof. exact (@lem2716486 term111). Qed.
Lemma lem2716488 (n : int) : (term108 n) = (term108 n).
Proof. exact (eq_refl (term108 n)). Qed.
Lemma lem2716489 (n : int) : ((term104 n) = term109) = ((term104 n) = term110).
Proof. exact (MK_COMB (@lem2716488 n) (@lem2716487)). Qed.
Lemma lem2716491 (n : int) : ((term18 n) = term19) = ((term104 n) = term110).
Proof. exact (TRANS (@lem2716482 n) (@lem2716489 n)). Qed.
Lemma lem2716492 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2716493 (n : int) : (term112 n) = (term113 n).
Proof. exact (MK_COMB (@lem2716492) (@lem2716478 n)). Qed.
Lemma lem2716494 (n : int) : (term45 n) = (term114 n).
Proof. exact (MK_COMB (@lem2716493 n) (@lem2716491 n)). Qed.
Lemma lem2716496 (y : int) (x : int) : (term115 x y) = (term116 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem2716497 (n : int) : (term17 n) = (term117 n).
Proof. exact (@lem2716496 term27 (term18 n)). Qed.
Lemma lem2716499 (x : int) (y : int) : (int_le x y) = (term118 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2716500 (n : int) : (term119 n) = (term120 n).
Proof. exact (@lem2716499 (term121 n) term27). Qed.
Lemma lem2716502 (x : int) (y : int) : (term122 x y) = (term123 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2716503 (n : int) : (term124 n) = (term125 n).
Proof. exact (@lem2716502 (term18 n) term19). Qed.
Lemma lem2716505 (n : nat) : (term106 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2716506 : term109 = term110.
Proof. exact (@lem2716505 term111). Qed.
Lemma lem2716507 (n : int) : (term126 n) = (term126 n).
Proof. exact (eq_refl (term126 n)). Qed.
Lemma lem2716508 (n : int) : (term125 n) = (term127 n).
Proof. exact (MK_COMB (@lem2716507 n) (@lem2716506)). Qed.
Lemma lem2716509 (n : int) : (term124 n) = (term127 n).
Proof. exact (TRANS (@lem2716503 n) (@lem2716508 n)). Qed.
Lemma lem2716510 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2716511 (n : int) : (term128 n) = (term129 n).
Proof. exact (MK_COMB (@lem2716510) (@lem2716509 n)). Qed.
Lemma lem2716513 (n : nat) : (term106 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2716514 : term105 = term107.
Proof. exact (@lem2716513 (NUMERAL 0)). Qed.
Lemma lem2716515 (n : int) : (term120 n) = (term130 n).
Proof. exact (MK_COMB (@lem2716511 n) (@lem2716514)). Qed.
Lemma lem2716516 (n : int) : (term119 n) = (term130 n).
Proof. exact (TRANS (@lem2716500 n) (@lem2716515 n)). Qed.
Lemma lem2716517 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2716518 (n : int) : (term131 n) = (term132 n).
Proof. exact (MK_COMB (@lem2716517) (@lem2716516 n)). Qed.
Lemma lem2716520 (x : int) (y : int) : (int_le x y) = (term118 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2716521 (n : int) : (term133 n) = (term134 n).
Proof. exact (@lem2716520 term135 (term18 n)). Qed.
Lemma lem2716523 (x : int) (y : int) : (term122 x y) = (term123 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2716524 : term136 = term137.
Proof. exact (@lem2716523 term27 term19). Qed.
Lemma lem2716526 (n : nat) : (term106 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2716527 : term105 = term107.
Proof. exact (@lem2716526 (NUMERAL 0)). Qed.
Lemma lem2716528 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2716529 : term138 = term139.
Proof. exact (MK_COMB (@lem2716528) (@lem2716527)). Qed.
Lemma lem2716531 (n : nat) : (term106 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2716532 : term109 = term110.
Proof. exact (@lem2716531 term111). Qed.
Lemma lem2716533 : term137 = term140.
Proof. exact (MK_COMB (@lem2716529) (@lem2716532)). Qed.
Lemma lem2716534 : term136 = term140.
Proof. exact (TRANS (@lem2716524) (@lem2716533)). Qed.
Lemma lem2716535 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2716536 : term141 = term142.
Proof. exact (MK_COMB (@lem2716535) (@lem2716534)). Qed.
Lemma lem2716537 (n : int) : (term104 n) = (term104 n).
Proof. exact (eq_refl (term104 n)). Qed.
Lemma lem2716538 (n : int) : (term134 n) = (term143 n).
Proof. exact (MK_COMB (@lem2716536) (@lem2716537 n)). Qed.
Lemma lem2716539 (n : int) : (term133 n) = (term143 n).
Proof. exact (TRANS (@lem2716521 n) (@lem2716538 n)). Qed.
Lemma lem2716540 (n : int) : (term117 n) = (term144 n).
Proof. exact (MK_COMB (@lem2716518 n) (@lem2716539 n)). Qed.
Lemma lem2716541 (n : int) : (term17 n) = (term144 n).
Proof. exact (TRANS (@lem2716497 n) (@lem2716540 n)). Qed.
Lemma lem2716543 (y : int) (x : int) : (term115 x y) = (term116 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem2716544 (n : int) : (term26 n) = (term145 n).
Proof. exact (@lem2716543 term19 (term18 n)). Qed.
Lemma lem2716546 (x : int) (y : int) : (int_le x y) = (term118 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2716547 (n : int) : (term146 n) = (term147 n).
Proof. exact (@lem2716546 (term121 n) term19). Qed.
Lemma lem2716549 (x : int) (y : int) : (term122 x y) = (term123 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2716550 (n : int) : (term124 n) = (term125 n).
Proof. exact (@lem2716549 (term18 n) term19). Qed.
Lemma lem2716552 (n : nat) : (term106 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2716553 : term109 = term110.
Proof. exact (@lem2716552 term111). Qed.
Lemma lem2716554 (n : int) : (term126 n) = (term126 n).
Proof. exact (eq_refl (term126 n)). Qed.
Lemma lem2716555 (n : int) : (term125 n) = (term127 n).
Proof. exact (MK_COMB (@lem2716554 n) (@lem2716553)). Qed.
Lemma lem2716556 (n : int) : (term124 n) = (term127 n).
Proof. exact (TRANS (@lem2716550 n) (@lem2716555 n)). Qed.
Lemma lem2716557 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2716558 (n : int) : (term128 n) = (term129 n).
Proof. exact (MK_COMB (@lem2716557) (@lem2716556 n)). Qed.
Lemma lem2716560 (n : nat) : (term106 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2716561 : term109 = term110.
Proof. exact (@lem2716560 term111). Qed.
Lemma lem2716562 (n : int) : (term147 n) = (term148 n).
Proof. exact (MK_COMB (@lem2716558 n) (@lem2716561)). Qed.
Lemma lem2716563 (n : int) : (term146 n) = (term148 n).
Proof. exact (TRANS (@lem2716547 n) (@lem2716562 n)). Qed.
Lemma lem2716564 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2716565 (n : int) : (term149 n) = (term150 n).
Proof. exact (MK_COMB (@lem2716564) (@lem2716563 n)). Qed.
Lemma lem2716567 (x : int) (y : int) : (int_le x y) = (term118 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2716568 (n : int) : (term151 n) = (term152 n).
Proof. exact (@lem2716567 term153 (term18 n)). Qed.
Lemma lem2716570 (x : int) (y : int) : (term122 x y) = (term123 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2716571 : term154 = term155.
Proof. exact (@lem2716570 term19 term19). Qed.
Lemma lem2716573 (n : nat) : (term106 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2716574 : term109 = term110.
Proof. exact (@lem2716573 term111). Qed.
Lemma lem2716575 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2716576 : term156 = term157.
Proof. exact (MK_COMB (@lem2716575) (@lem2716574)). Qed.
Lemma lem2716578 (n : nat) : (term106 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2716579 : term109 = term110.
Proof. exact (@lem2716578 term111). Qed.
Lemma lem2716580 : term155 = term158.
Proof. exact (MK_COMB (@lem2716576) (@lem2716579)). Qed.
Lemma lem2716581 : term154 = term158.
Proof. exact (TRANS (@lem2716571) (@lem2716580)). Qed.
Lemma lem2716582 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2716583 : term159 = term160.
Proof. exact (MK_COMB (@lem2716582) (@lem2716581)). Qed.
Lemma lem2716584 (n : int) : (term104 n) = (term104 n).
Proof. exact (eq_refl (term104 n)). Qed.
Lemma lem2716585 (n : int) : (term152 n) = (term161 n).
Proof. exact (MK_COMB (@lem2716583) (@lem2716584 n)). Qed.
Lemma lem2716586 (n : int) : (term151 n) = (term161 n).
Proof. exact (TRANS (@lem2716568 n) (@lem2716585 n)). Qed.
Lemma lem2716587 (n : int) : (term145 n) = (term162 n).
Proof. exact (MK_COMB (@lem2716565 n) (@lem2716586 n)). Qed.
Lemma lem2716588 (n : int) : (term26 n) = (term162 n).
Proof. exact (TRANS (@lem2716544 n) (@lem2716587 n)). Qed.
Lemma lem2716589 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2716590 (n : int) : (term163 n) = (term164 n).
Proof. exact (MK_COMB (@lem2716589) (@lem2716541 n)). Qed.
Lemma lem2716591 (n : int) : (term165 n) = (term166 n).
Proof. exact (MK_COMB (@lem2716590 n) (@lem2716588 n)). Qed.
Lemma lem2716594 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem2716595 (n : int) : ((term18 n) = term27) = ((term104 n) = term105).
Proof. exact (@lem2716594 (term18 n) term27). Qed.
Lemma lem2716599 (n : nat) : (term106 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2716600 : term105 = term107.
Proof. exact (@lem2716599 (NUMERAL 0)). Qed.
Lemma lem2716601 (n : int) : (term108 n) = (term108 n).
Proof. exact (eq_refl (term108 n)). Qed.
Lemma lem2716602 (n : int) : ((term104 n) = term105) = ((term104 n) = term107).
Proof. exact (MK_COMB (@lem2716601 n) (@lem2716600)). Qed.
Lemma lem2716604 (n : int) : ((term18 n) = term27) = ((term104 n) = term107).
Proof. exact (TRANS (@lem2716595 n) (@lem2716602 n)). Qed.
Lemma lem2716607 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem2716608 (n : int) : ((term18 n) = term19) = ((term104 n) = term109).
Proof. exact (@lem2716607 (term18 n) term19). Qed.
Lemma lem2716612 (n : nat) : (term106 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2716613 : term109 = term110.
Proof. exact (@lem2716612 term111). Qed.
Lemma lem2716614 (n : int) : (term108 n) = (term108 n).
Proof. exact (eq_refl (term108 n)). Qed.
Lemma lem2716615 (n : int) : ((term104 n) = term109) = ((term104 n) = term110).
Proof. exact (MK_COMB (@lem2716614 n) (@lem2716613)). Qed.
Lemma lem2716617 (n : int) : ((term18 n) = term19) = ((term104 n) = term110).
Proof. exact (TRANS (@lem2716608 n) (@lem2716615 n)). Qed.
Lemma lem2716618 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2716619 (n : int) : (term70 n) = (term167 n).
Proof. exact (MK_COMB (@lem2716618) (@lem2716604 n)). Qed.
Lemma lem2716620 (n : int) : (term72 n) = (term168 n).
Proof. exact (MK_COMB (@lem2716619 n) (@lem2716617 n)). Qed.
Lemma lem2716621 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2716622 (n : int) : (term73 n) = (term169 n).
Proof. exact (MK_COMB (@lem2716621) (@lem2716591 n)). Qed.
Lemma lem2716623 (n : int) : (term75 n) = (term170 n).
Proof. exact (MK_COMB (@lem2716622 n) (@lem2716620 n)). Qed.
Lemma lem2716625 (y : int) (x : int) : (term115 x y) = (term116 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem2716626 (n : int) : (term26 n) = (term145 n).
Proof. exact (@lem2716625 term19 (term18 n)). Qed.
Lemma lem2716628 (x : int) (y : int) : (int_le x y) = (term118 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2716629 (n : int) : (term146 n) = (term147 n).
Proof. exact (@lem2716628 (term121 n) term19). Qed.
Lemma lem2716631 (x : int) (y : int) : (term122 x y) = (term123 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2716632 (n : int) : (term124 n) = (term125 n).
Proof. exact (@lem2716631 (term18 n) term19). Qed.
Lemma lem2716634 (n : nat) : (term106 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2716635 : term109 = term110.
Proof. exact (@lem2716634 term111). Qed.
Lemma lem2716636 (n : int) : (term126 n) = (term126 n).
Proof. exact (eq_refl (term126 n)). Qed.
Lemma lem2716637 (n : int) : (term125 n) = (term127 n).
Proof. exact (MK_COMB (@lem2716636 n) (@lem2716635)). Qed.
Lemma lem2716638 (n : int) : (term124 n) = (term127 n).
Proof. exact (TRANS (@lem2716632 n) (@lem2716637 n)). Qed.
Lemma lem2716639 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2716640 (n : int) : (term128 n) = (term129 n).
Proof. exact (MK_COMB (@lem2716639) (@lem2716638 n)). Qed.
Lemma lem2716642 (n : nat) : (term106 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2716643 : term109 = term110.
Proof. exact (@lem2716642 term111). Qed.
Lemma lem2716644 (n : int) : (term147 n) = (term148 n).
Proof. exact (MK_COMB (@lem2716640 n) (@lem2716643)). Qed.
Lemma lem2716645 (n : int) : (term146 n) = (term148 n).
Proof. exact (TRANS (@lem2716629 n) (@lem2716644 n)). Qed.
Lemma lem2716646 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2716647 (n : int) : (term149 n) = (term150 n).
Proof. exact (MK_COMB (@lem2716646) (@lem2716645 n)). Qed.
Lemma lem2716649 (x : int) (y : int) : (int_le x y) = (term118 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2716650 (n : int) : (term151 n) = (term152 n).
Proof. exact (@lem2716649 term153 (term18 n)). Qed.
Lemma lem2716652 (x : int) (y : int) : (term122 x y) = (term123 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2716653 : term154 = term155.
Proof. exact (@lem2716652 term19 term19). Qed.
Lemma lem2716655 (n : nat) : (term106 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2716656 : term109 = term110.
Proof. exact (@lem2716655 term111). Qed.
Lemma lem2716657 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2716658 : term156 = term157.
Proof. exact (MK_COMB (@lem2716657) (@lem2716656)). Qed.
Lemma lem2716660 (n : nat) : (term106 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2716661 : term109 = term110.
Proof. exact (@lem2716660 term111). Qed.
Lemma lem2716662 : term155 = term158.
Proof. exact (MK_COMB (@lem2716658) (@lem2716661)). Qed.
Lemma lem2716663 : term154 = term158.
Proof. exact (TRANS (@lem2716653) (@lem2716662)). Qed.
Lemma lem2716664 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2716665 : term159 = term160.
Proof. exact (MK_COMB (@lem2716664) (@lem2716663)). Qed.
Lemma lem2716666 (n : int) : (term104 n) = (term104 n).
Proof. exact (eq_refl (term104 n)). Qed.
Lemma lem2716667 (n : int) : (term152 n) = (term161 n).
Proof. exact (MK_COMB (@lem2716665) (@lem2716666 n)). Qed.
Lemma lem2716668 (n : int) : (term151 n) = (term161 n).
Proof. exact (TRANS (@lem2716650 n) (@lem2716667 n)). Qed.
Lemma lem2716669 (n : int) : (term145 n) = (term162 n).
Proof. exact (MK_COMB (@lem2716647 n) (@lem2716668 n)). Qed.
Lemma lem2716670 (n : int) : (term26 n) = (term162 n).
Proof. exact (TRANS (@lem2716626 n) (@lem2716669 n)). Qed.
Lemma lem2716672 (y : int) (x : int) : (term115 x y) = (term116 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem2716673 (n : int) : (term17 n) = (term117 n).
Proof. exact (@lem2716672 term27 (term18 n)). Qed.
Lemma lem2716675 (x : int) (y : int) : (int_le x y) = (term118 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2716676 (n : int) : (term119 n) = (term120 n).
Proof. exact (@lem2716675 (term121 n) term27). Qed.
Lemma lem2716678 (x : int) (y : int) : (term122 x y) = (term123 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2716679 (n : int) : (term124 n) = (term125 n).
Proof. exact (@lem2716678 (term18 n) term19). Qed.
Lemma lem2716681 (n : nat) : (term106 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2716682 : term109 = term110.
Proof. exact (@lem2716681 term111). Qed.
Lemma lem2716683 (n : int) : (term126 n) = (term126 n).
Proof. exact (eq_refl (term126 n)). Qed.
Lemma lem2716684 (n : int) : (term125 n) = (term127 n).
Proof. exact (MK_COMB (@lem2716683 n) (@lem2716682)). Qed.
Lemma lem2716685 (n : int) : (term124 n) = (term127 n).
Proof. exact (TRANS (@lem2716679 n) (@lem2716684 n)). Qed.
Lemma lem2716686 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2716687 (n : int) : (term128 n) = (term129 n).
Proof. exact (MK_COMB (@lem2716686) (@lem2716685 n)). Qed.
Lemma lem2716689 (n : nat) : (term106 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2716690 : term105 = term107.
Proof. exact (@lem2716689 (NUMERAL 0)). Qed.
Lemma lem2716691 (n : int) : (term120 n) = (term130 n).
Proof. exact (MK_COMB (@lem2716687 n) (@lem2716690)). Qed.
Lemma lem2716692 (n : int) : (term119 n) = (term130 n).
Proof. exact (TRANS (@lem2716676 n) (@lem2716691 n)). Qed.
Lemma lem2716693 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2716694 (n : int) : (term131 n) = (term132 n).
Proof. exact (MK_COMB (@lem2716693) (@lem2716692 n)). Qed.
Lemma lem2716696 (x : int) (y : int) : (int_le x y) = (term118 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2716697 (n : int) : (term133 n) = (term134 n).
Proof. exact (@lem2716696 term135 (term18 n)). Qed.
Lemma lem2716699 (x : int) (y : int) : (term122 x y) = (term123 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2716700 : term136 = term137.
Proof. exact (@lem2716699 term27 term19). Qed.
Lemma lem2716702 (n : nat) : (term106 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2716703 : term105 = term107.
Proof. exact (@lem2716702 (NUMERAL 0)). Qed.
Lemma lem2716704 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2716705 : term138 = term139.
Proof. exact (MK_COMB (@lem2716704) (@lem2716703)). Qed.
Lemma lem2716707 (n : nat) : (term106 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2716708 : term109 = term110.
Proof. exact (@lem2716707 term111). Qed.
Lemma lem2716709 : term137 = term140.
Proof. exact (MK_COMB (@lem2716705) (@lem2716708)). Qed.
Lemma lem2716710 : term136 = term140.
Proof. exact (TRANS (@lem2716700) (@lem2716709)). Qed.
Lemma lem2716711 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2716712 : term141 = term142.
Proof. exact (MK_COMB (@lem2716711) (@lem2716710)). Qed.
Lemma lem2716713 (n : int) : (term104 n) = (term104 n).
Proof. exact (eq_refl (term104 n)). Qed.
Lemma lem2716714 (n : int) : (term134 n) = (term143 n).
Proof. exact (MK_COMB (@lem2716712) (@lem2716713 n)). Qed.
Lemma lem2716715 (n : int) : (term133 n) = (term143 n).
Proof. exact (TRANS (@lem2716697 n) (@lem2716714 n)). Qed.
Lemma lem2716716 (n : int) : (term117 n) = (term144 n).
Proof. exact (MK_COMB (@lem2716694 n) (@lem2716715 n)). Qed.
Lemma lem2716717 (n : int) : (term17 n) = (term144 n).
Proof. exact (TRANS (@lem2716673 n) (@lem2716716 n)). Qed.
Lemma lem2716718 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2716719 (n : int) : (term171 n) = (term172 n).
Proof. exact (MK_COMB (@lem2716718) (@lem2716670 n)). Qed.
Lemma lem2716720 (n : int) : (term173 n) = (term174 n).
Proof. exact (MK_COMB (@lem2716719 n) (@lem2716717 n)). Qed.
Lemma lem2716723 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem2716724 (n : int) : ((term18 n) = term19) = ((term104 n) = term109).
Proof. exact (@lem2716723 (term18 n) term19). Qed.
Lemma lem2716728 (n : nat) : (term106 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2716729 : term109 = term110.
Proof. exact (@lem2716728 term111). Qed.
Lemma lem2716730 (n : int) : (term108 n) = (term108 n).
Proof. exact (eq_refl (term108 n)). Qed.
Lemma lem2716731 (n : int) : ((term104 n) = term109) = ((term104 n) = term110).
Proof. exact (MK_COMB (@lem2716730 n) (@lem2716729)). Qed.
Lemma lem2716733 (n : int) : ((term18 n) = term19) = ((term104 n) = term110).
Proof. exact (TRANS (@lem2716724 n) (@lem2716731 n)). Qed.
Lemma lem2716736 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem2716737 (n : int) : ((term18 n) = term27) = ((term104 n) = term105).
Proof. exact (@lem2716736 (term18 n) term27). Qed.
Lemma lem2716741 (n : nat) : (term106 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2716742 : term105 = term107.
Proof. exact (@lem2716741 (NUMERAL 0)). Qed.
Lemma lem2716743 (n : int) : (term108 n) = (term108 n).
Proof. exact (eq_refl (term108 n)). Qed.
Lemma lem2716744 (n : int) : ((term104 n) = term105) = ((term104 n) = term107).
Proof. exact (MK_COMB (@lem2716743 n) (@lem2716742)). Qed.
Lemma lem2716746 (n : int) : ((term18 n) = term27) = ((term104 n) = term107).
Proof. exact (TRANS (@lem2716737 n) (@lem2716744 n)). Qed.
Lemma lem2716747 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2716748 (n : int) : (term79 n) = (term175 n).
Proof. exact (MK_COMB (@lem2716747) (@lem2716733 n)). Qed.
Lemma lem2716749 (n : int) : (term81 n) = (term176 n).
Proof. exact (MK_COMB (@lem2716748 n) (@lem2716746 n)). Qed.
Lemma lem2716750 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2716751 (n : int) : (term82 n) = (term177 n).
Proof. exact (MK_COMB (@lem2716750) (@lem2716720 n)). Qed.
Lemma lem2716752 (n : int) : (term84 n) = (term178 n).
Proof. exact (MK_COMB (@lem2716751 n) (@lem2716749 n)). Qed.
Lemma lem2716753 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2716754 (n : int) : (term87 n) = (term179 n).
Proof. exact (MK_COMB (@lem2716753) (@lem2716623 n)). Qed.
Lemma lem2716755 (n : int) : (term89 n) = (term180 n).
Proof. exact (MK_COMB (@lem2716754 n) (@lem2716752 n)). Qed.
Lemma lem2716756 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2716757 (n : int) : (term91 n) = (term181 n).
Proof. exact (MK_COMB (@lem2716756) (@lem2716494 n)). Qed.
Lemma lem2716758 (n : int) : (term93 n) = (term182 n).
Proof. exact (MK_COMB (@lem2716757 n) (@lem2716755 n)). Qed.
Lemma lem2716759 : term102 = term183.
Proof. exact (fun_ext (fun n : int => @lem2716758 n)). Qed.
Lemma lem2716760 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2716761 : term103 = term184.
Proof. exact (MK_COMB (@lem2716760) (@lem2716759)). Qed.
Lemma lem2716762 : term97 = term184.
Proof. exact (TRANS (@lem2716465) (@lem2716761)). Qed.
Lemma lem2716766 (t : Prop) : (term185 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem2716842 : term186 = term184.
Proof. exact (@lem2716766 term184). Qed.
Lemma lem2716895 (n : int) : (term182 n) = (term182 n).
Proof. exact (eq_refl (term182 n)). Qed.
Lemma lem2716896 : term183 = term183.
Proof. exact (fun_ext (fun n : int => @lem2716895 n)). Qed.
Lemma lem2716897 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2716898 : term184 = term184.
Proof. exact (MK_COMB (@lem2716897) (@lem2716896)). Qed.
Lemma lem2716899 : term186 = term184.
Proof. exact (TRANS (@lem2716842) (@lem2716898)). Qed.
Lemma lem2716952 (n : int) : (term182 n) = (term182 n).
Proof. exact (eq_refl (term182 n)). Qed.
Lemma lem2716953 : term183 = term183.
Proof. exact (fun_ext (fun n : int => @lem2716952 n)). Qed.
Lemma lem2716954 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2716955 : term184 = term184.
Proof. exact (MK_COMB (@lem2716954) (@lem2716953)). Qed.
Lemma lem2716956 : term186 = term184.
Proof. exact (TRANS (@lem2716899) (@lem2716955)). Qed.
Lemma lem2716957 (n : int) : ((term104 n) = term107) = ((term187 n) = term107).
Proof. exact (@lem1988293 (term104 n) term107). Qed.
Lemma lem2716963 (n : int) : (term187 n) = (term188 n).
Proof. exact (@lem1982792 (term104 n) term107). Qed.
Lemma lem2716965 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2716966 : term107 = term190.
Proof. exact (@lem2716965 (NUMERAL 0)). Qed.
Lemma lem2716968 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2716969 : term193 = term194.
Proof. exact (@lem2716968 term111). Qed.
Lemma lem2716970 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2716971 : term195 = term196.
Proof. exact (MK_COMB (@lem2716970) (@lem2716969)). Qed.
Lemma lem2716972 : term197 = term198.
Proof. exact (MK_COMB (@lem2716971) (@lem2716966)). Qed.
Lemma lem2716973 : term198 = term199.
Proof. exact (@lem1981613 term193 term107 term110 term110). Qed.
Lemma lem2716975 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2716976 : term202 = term203.
Proof. exact (@lem2716975 term111 term111). Qed.
Lemma lem2716977 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2716978 : term205 = term111.
Proof. exact (EQ_MP (@lem2716977) (@lem940073)). Qed.
Lemma lem2716979 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2716980 : term203 = term110.
Proof. exact (MK_COMB (@lem2716979) (@lem2716978)). Qed.
Lemma lem2716981 : term202 = term110.
Proof. exact (TRANS (@lem2716976) (@lem2716980)). Qed.
Lemma lem2716983 (x : nat) : (term206 x) = term107.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2716984 : term197 = term107.
Proof. exact (@lem2716983 term111). Qed.
Lemma lem2716985 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2716986 : term207 = term208.
Proof. exact (MK_COMB (@lem2716985) (@lem2716984)). Qed.
Lemma lem2716987 : term199 = term190.
Proof. exact (MK_COMB (@lem2716986) (@lem2716981)). Qed.
Lemma lem2716988 : term198 = term190.
Proof. exact (TRANS (@lem2716973) (@lem2716987)). Qed.
Lemma lem2716989 : term197 = term190.
Proof. exact (TRANS (@lem2716972) (@lem2716988)). Qed.
Lemma lem2716991 (x : real) : (term209 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2716992 : term190 = term107.
Proof. exact (@lem2716991 term107). Qed.
Lemma lem2716993 : term197 = term107.
Proof. exact (TRANS (@lem2716989) (@lem2716992)). Qed.
Lemma lem2716994 (n : int) : (term126 n) = (term126 n).
Proof. exact (eq_refl (term126 n)). Qed.
Lemma lem2716995 (n : int) : (term188 n) = (term210 n).
Proof. exact (MK_COMB (@lem2716994 n) (@lem2716993)). Qed.
Lemma lem2716996 (n : int) : (term210 n) = (term104 n).
Proof. exact (@lem1982723 (term104 n)). Qed.
Lemma lem2716997 (n : int) : (term188 n) = (term104 n).
Proof. exact (TRANS (@lem2716995 n) (@lem2716996 n)). Qed.
Lemma lem2716999 (n : int) : (term187 n) = (term104 n).
Proof. exact (TRANS (@lem2716963 n) (@lem2716997 n)). Qed.
Lemma lem2717000 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2717001 (n : int) : (term211 n) = (term108 n).
Proof. exact (MK_COMB (@lem2717000) (@lem2716999 n)). Qed.
Lemma lem2717002 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2717003 (n : int) : ((term187 n) = term107) = ((term104 n) = term107).
Proof. exact (MK_COMB (@lem2717001 n) (@lem2717002)). Qed.
Lemma lem2717004 (n : int) : ((term104 n) = term107) = ((term104 n) = term107).
Proof. exact (TRANS (@lem2716957 n) (@lem2717003 n)). Qed.
Lemma lem2717005 (n : int) : ((term104 n) = term110) = ((term212 n) = term107).
Proof. exact (@lem1988293 (term104 n) term110). Qed.
Lemma lem2717011 (n : int) : (term212 n) = (term213 n).
Proof. exact (@lem1982792 (term104 n) term110). Qed.
Lemma lem2717013 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2717014 : term110 = term214.
Proof. exact (@lem2717013 term111). Qed.
Lemma lem2717016 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2717017 : term193 = term194.
Proof. exact (@lem2717016 term111). Qed.
Lemma lem2717018 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2717019 : term195 = term196.
Proof. exact (MK_COMB (@lem2717018) (@lem2717017)). Qed.
Lemma lem2717020 : term215 = term216.
Proof. exact (MK_COMB (@lem2717019) (@lem2717014)). Qed.
Lemma lem2717021 : term216 = term217.
Proof. exact (@lem1981613 term193 term110 term110 term110). Qed.
Lemma lem2717023 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2717024 : term202 = term203.
Proof. exact (@lem2717023 term111 term111). Qed.
Lemma lem2717025 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2717026 : term205 = term111.
Proof. exact (EQ_MP (@lem2717025) (@lem940073)). Qed.
Lemma lem2717027 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2717028 : term203 = term110.
Proof. exact (MK_COMB (@lem2717027) (@lem2717026)). Qed.
Lemma lem2717029 : term202 = term110.
Proof. exact (TRANS (@lem2717024) (@lem2717028)). Qed.
Lemma lem2717031 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2717032 : term215 = term220.
Proof. exact (@lem2717031 term111 term111). Qed.
Lemma lem2717033 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2717034 : term205 = term111.
Proof. exact (EQ_MP (@lem2717033) (@lem940073)). Qed.
Lemma lem2717035 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2717036 : term203 = term110.
Proof. exact (MK_COMB (@lem2717035) (@lem2717034)). Qed.
Lemma lem2717037 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2717038 : term220 = term193.
Proof. exact (MK_COMB (@lem2717037) (@lem2717036)). Qed.
Lemma lem2717039 : term215 = term193.
Proof. exact (TRANS (@lem2717032) (@lem2717038)). Qed.
Lemma lem2717040 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2717041 : term221 = term222.
Proof. exact (MK_COMB (@lem2717040) (@lem2717039)). Qed.
Lemma lem2717042 : term217 = term194.
Proof. exact (MK_COMB (@lem2717041) (@lem2717029)). Qed.
Lemma lem2717043 : term216 = term194.
Proof. exact (TRANS (@lem2717021) (@lem2717042)). Qed.
Lemma lem2717044 : term215 = term194.
Proof. exact (TRANS (@lem2717020) (@lem2717043)). Qed.
Lemma lem2717046 (x : real) : (term209 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2717047 : term194 = term193.
Proof. exact (@lem2717046 term193). Qed.
Lemma lem2717048 : term215 = term193.
Proof. exact (TRANS (@lem2717044) (@lem2717047)). Qed.
Lemma lem2717049 (n : int) : (term126 n) = (term126 n).
Proof. exact (eq_refl (term126 n)). Qed.
Lemma lem2717052 (n : int) : (term213 n) = (term223 n).
Proof. exact (MK_COMB (@lem2717049 n) (@lem2717048)). Qed.
Lemma lem2717054 (n : int) : (term212 n) = (term223 n).
Proof. exact (TRANS (@lem2717011 n) (@lem2717052 n)). Qed.
Lemma lem2717055 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2717056 (n : int) : (term224 n) = (term225 n).
Proof. exact (MK_COMB (@lem2717055) (@lem2717054 n)). Qed.
Lemma lem2717057 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2717058 (n : int) : ((term212 n) = term107) = ((term223 n) = term107).
Proof. exact (MK_COMB (@lem2717056 n) (@lem2717057)). Qed.
Lemma lem2717059 (n : int) : ((term104 n) = term110) = ((term223 n) = term107).
Proof. exact (TRANS (@lem2717005 n) (@lem2717058 n)). Qed.
Lemma lem2717060 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2717061 (n : int) : (term113 n) = (term113 n).
Proof. exact (MK_COMB (@lem2717060) (@lem2717004 n)). Qed.
Lemma lem2717062 (n : int) : (term114 n) = (term226 n).
Proof. exact (MK_COMB (@lem2717061 n) (@lem2717059 n)). Qed.
Lemma lem2717063 (n : int) : (term130 n) = (term227 n).
Proof. exact (@lem1988287 term107 (term127 n)). Qed.
Lemma lem2717075 (n : int) : (term228 n) = (term229 n).
Proof. exact (@lem1982792 term107 (term127 n)). Qed.
Lemma lem2717076 (n : int) : (term230 n) = (term231 n).
Proof. exact (@lem1982781 (term104 n) term193 term110). Qed.
Lemma lem2717078 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2717079 : term110 = term214.
Proof. exact (@lem2717078 term111). Qed.
Lemma lem2717081 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2717082 : term193 = term194.
Proof. exact (@lem2717081 term111). Qed.
Lemma lem2717083 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2717084 : term195 = term196.
Proof. exact (MK_COMB (@lem2717083) (@lem2717082)). Qed.
Lemma lem2717085 : term215 = term216.
Proof. exact (MK_COMB (@lem2717084) (@lem2717079)). Qed.
Lemma lem2717086 : term216 = term217.
Proof. exact (@lem1981613 term193 term110 term110 term110). Qed.
Lemma lem2717088 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2717089 : term202 = term203.
Proof. exact (@lem2717088 term111 term111). Qed.
Lemma lem2717090 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2717091 : term205 = term111.
Proof. exact (EQ_MP (@lem2717090) (@lem940073)). Qed.
Lemma lem2717092 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2717093 : term203 = term110.
Proof. exact (MK_COMB (@lem2717092) (@lem2717091)). Qed.
Lemma lem2717094 : term202 = term110.
Proof. exact (TRANS (@lem2717089) (@lem2717093)). Qed.
Lemma lem2717096 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2717097 : term215 = term220.
Proof. exact (@lem2717096 term111 term111). Qed.
Lemma lem2717098 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2717099 : term205 = term111.
Proof. exact (EQ_MP (@lem2717098) (@lem940073)). Qed.
Lemma lem2717100 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2717101 : term203 = term110.
Proof. exact (MK_COMB (@lem2717100) (@lem2717099)). Qed.
Lemma lem2717102 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2717103 : term220 = term193.
Proof. exact (MK_COMB (@lem2717102) (@lem2717101)). Qed.
Lemma lem2717104 : term215 = term193.
Proof. exact (TRANS (@lem2717097) (@lem2717103)). Qed.
Lemma lem2717105 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2717106 : term221 = term222.
Proof. exact (MK_COMB (@lem2717105) (@lem2717104)). Qed.
Lemma lem2717107 : term217 = term194.
Proof. exact (MK_COMB (@lem2717106) (@lem2717094)). Qed.
Lemma lem2717108 : term216 = term194.
Proof. exact (TRANS (@lem2717086) (@lem2717107)). Qed.
Lemma lem2717109 : term215 = term194.
Proof. exact (TRANS (@lem2717085) (@lem2717108)). Qed.
Lemma lem2717111 (x : real) : (term209 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2717112 : term194 = term193.
Proof. exact (@lem2717111 term193). Qed.
Lemma lem2717113 : term215 = term193.
Proof. exact (TRANS (@lem2717109) (@lem2717112)). Qed.
Lemma lem2717116 (n : int) : (term232 n) = (term232 n).
Proof. exact (eq_refl (term232 n)). Qed.
Lemma lem2717117 (n : int) : (term231 n) = (term233 n).
Proof. exact (MK_COMB (@lem2717116 n) (@lem2717113)). Qed.
Lemma lem2717118 (n : int) : (term230 n) = (term233 n).
Proof. exact (TRANS (@lem2717076 n) (@lem2717117 n)). Qed.
Lemma lem2717119 : term139 = term139.
Proof. exact (eq_refl term139). Qed.
Lemma lem2717120 (n : int) : (term229 n) = (term234 n).
Proof. exact (MK_COMB (@lem2717119) (@lem2717118 n)). Qed.
Lemma lem2717121 (n : int) : (term234 n) = (term233 n).
Proof. exact (@lem1982721 (term233 n)). Qed.
Lemma lem2717122 (n : int) : (term229 n) = (term233 n).
Proof. exact (TRANS (@lem2717120 n) (@lem2717121 n)). Qed.
Lemma lem2717124 (n : int) : (term228 n) = (term233 n).
Proof. exact (TRANS (@lem2717075 n) (@lem2717122 n)). Qed.
Lemma lem2717125 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2717126 (n : int) : (term235 n) = (term236 n).
Proof. exact (MK_COMB (@lem2717125) (@lem2717124 n)). Qed.
Lemma lem2717127 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2717128 (n : int) : (term227 n) = (term237 n).
Proof. exact (MK_COMB (@lem2717126 n) (@lem2717127)). Qed.
Lemma lem2717129 (n : int) : (term130 n) = (term237 n).
Proof. exact (TRANS (@lem2717063 n) (@lem2717128 n)). Qed.
Lemma lem2717130 (n : int) : (term143 n) = (term238 n).
Proof. exact (@lem1988287 (term104 n) term140). Qed.
Lemma lem2717137 : term140 = term110.
Proof. exact (@lem1982721 term110). Qed.
Lemma lem2717140 (n : int) : (term239 n) = (term239 n).
Proof. exact (eq_refl (term239 n)). Qed.
Lemma lem2717141 (n : int) : (term240 n) = (term212 n).
Proof. exact (MK_COMB (@lem2717140 n) (@lem2717137)). Qed.
Lemma lem2717142 (n : int) : (term212 n) = (term213 n).
Proof. exact (@lem1982792 (term104 n) term110). Qed.
Lemma lem2717144 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2717145 : term110 = term214.
Proof. exact (@lem2717144 term111). Qed.
Lemma lem2717147 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2717148 : term193 = term194.
Proof. exact (@lem2717147 term111). Qed.
Lemma lem2717149 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2717150 : term195 = term196.
Proof. exact (MK_COMB (@lem2717149) (@lem2717148)). Qed.
Lemma lem2717151 : term215 = term216.
Proof. exact (MK_COMB (@lem2717150) (@lem2717145)). Qed.
Lemma lem2717152 : term216 = term217.
Proof. exact (@lem1981613 term193 term110 term110 term110). Qed.
Lemma lem2717154 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2717155 : term202 = term203.
Proof. exact (@lem2717154 term111 term111). Qed.
Lemma lem2717156 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2717157 : term205 = term111.
Proof. exact (EQ_MP (@lem2717156) (@lem940073)). Qed.
Lemma lem2717158 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2717159 : term203 = term110.
Proof. exact (MK_COMB (@lem2717158) (@lem2717157)). Qed.
Lemma lem2717160 : term202 = term110.
Proof. exact (TRANS (@lem2717155) (@lem2717159)). Qed.
Lemma lem2717162 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2717163 : term215 = term220.
Proof. exact (@lem2717162 term111 term111). Qed.
Lemma lem2717164 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2717165 : term205 = term111.
Proof. exact (EQ_MP (@lem2717164) (@lem940073)). Qed.
Lemma lem2717166 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2717167 : term203 = term110.
Proof. exact (MK_COMB (@lem2717166) (@lem2717165)). Qed.
Lemma lem2717168 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2717169 : term220 = term193.
Proof. exact (MK_COMB (@lem2717168) (@lem2717167)). Qed.
Lemma lem2717170 : term215 = term193.
Proof. exact (TRANS (@lem2717163) (@lem2717169)). Qed.
Lemma lem2717171 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2717172 : term221 = term222.
Proof. exact (MK_COMB (@lem2717171) (@lem2717170)). Qed.
Lemma lem2717173 : term217 = term194.
Proof. exact (MK_COMB (@lem2717172) (@lem2717160)). Qed.
Lemma lem2717174 : term216 = term194.
Proof. exact (TRANS (@lem2717152) (@lem2717173)). Qed.
Lemma lem2717175 : term215 = term194.
Proof. exact (TRANS (@lem2717151) (@lem2717174)). Qed.
Lemma lem2717177 (x : real) : (term209 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2717178 : term194 = term193.
Proof. exact (@lem2717177 term193). Qed.
Lemma lem2717179 : term215 = term193.
Proof. exact (TRANS (@lem2717175) (@lem2717178)). Qed.
Lemma lem2717180 (n : int) : (term126 n) = (term126 n).
Proof. exact (eq_refl (term126 n)). Qed.
Lemma lem2717183 (n : int) : (term213 n) = (term223 n).
Proof. exact (MK_COMB (@lem2717180 n) (@lem2717179)). Qed.
Lemma lem2717184 (n : int) : (term212 n) = (term223 n).
Proof. exact (TRANS (@lem2717142 n) (@lem2717183 n)). Qed.
Lemma lem2717185 (n : int) : (term240 n) = (term223 n).
Proof. exact (TRANS (@lem2717141 n) (@lem2717184 n)). Qed.
Lemma lem2717186 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2717187 (n : int) : (term241 n) = (term242 n).
Proof. exact (MK_COMB (@lem2717186) (@lem2717185 n)). Qed.
Lemma lem2717188 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2717189 (n : int) : (term238 n) = (term243 n).
Proof. exact (MK_COMB (@lem2717187 n) (@lem2717188)). Qed.
Lemma lem2717190 (n : int) : (term143 n) = (term243 n).
Proof. exact (TRANS (@lem2717130 n) (@lem2717189 n)). Qed.
Lemma lem2717191 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2717192 (n : int) : (term132 n) = (term244 n).
Proof. exact (MK_COMB (@lem2717191) (@lem2717129 n)). Qed.
Lemma lem2717193 (n : int) : (term144 n) = (term245 n).
Proof. exact (MK_COMB (@lem2717192 n) (@lem2717190 n)). Qed.
Lemma lem2717194 (n : int) : (term148 n) = (term246 n).
Proof. exact (@lem1988287 term110 (term127 n)). Qed.
Lemma lem2717206 (n : int) : (term247 n) = (term248 n).
Proof. exact (@lem1982792 term110 (term127 n)). Qed.
Lemma lem2717207 (n : int) : (term230 n) = (term231 n).
Proof. exact (@lem1982781 (term104 n) term193 term110). Qed.
Lemma lem2717209 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2717210 : term110 = term214.
Proof. exact (@lem2717209 term111). Qed.
Lemma lem2717212 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2717213 : term193 = term194.
Proof. exact (@lem2717212 term111). Qed.
Lemma lem2717214 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2717215 : term195 = term196.
Proof. exact (MK_COMB (@lem2717214) (@lem2717213)). Qed.
Lemma lem2717216 : term215 = term216.
Proof. exact (MK_COMB (@lem2717215) (@lem2717210)). Qed.
Lemma lem2717217 : term216 = term217.
Proof. exact (@lem1981613 term193 term110 term110 term110). Qed.
Lemma lem2717219 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2717220 : term202 = term203.
Proof. exact (@lem2717219 term111 term111). Qed.
Lemma lem2717221 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2717222 : term205 = term111.
Proof. exact (EQ_MP (@lem2717221) (@lem940073)). Qed.
Lemma lem2717223 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2717224 : term203 = term110.
Proof. exact (MK_COMB (@lem2717223) (@lem2717222)). Qed.
Lemma lem2717225 : term202 = term110.
Proof. exact (TRANS (@lem2717220) (@lem2717224)). Qed.
Lemma lem2717227 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2717228 : term215 = term220.
Proof. exact (@lem2717227 term111 term111). Qed.
Lemma lem2717229 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2717230 : term205 = term111.
Proof. exact (EQ_MP (@lem2717229) (@lem940073)). Qed.
Lemma lem2717231 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2717232 : term203 = term110.
Proof. exact (MK_COMB (@lem2717231) (@lem2717230)). Qed.
Lemma lem2717233 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2717234 : term220 = term193.
Proof. exact (MK_COMB (@lem2717233) (@lem2717232)). Qed.
Lemma lem2717235 : term215 = term193.
Proof. exact (TRANS (@lem2717228) (@lem2717234)). Qed.
Lemma lem2717236 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2717237 : term221 = term222.
Proof. exact (MK_COMB (@lem2717236) (@lem2717235)). Qed.
Lemma lem2717238 : term217 = term194.
Proof. exact (MK_COMB (@lem2717237) (@lem2717225)). Qed.
Lemma lem2717239 : term216 = term194.
Proof. exact (TRANS (@lem2717217) (@lem2717238)). Qed.
Lemma lem2717240 : term215 = term194.
Proof. exact (TRANS (@lem2717216) (@lem2717239)). Qed.
Lemma lem2717242 (x : real) : (term209 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2717243 : term194 = term193.
Proof. exact (@lem2717242 term193). Qed.
Lemma lem2717244 : term215 = term193.
Proof. exact (TRANS (@lem2717240) (@lem2717243)). Qed.
Lemma lem2717247 (n : int) : (term232 n) = (term232 n).
Proof. exact (eq_refl (term232 n)). Qed.
Lemma lem2717248 (n : int) : (term231 n) = (term233 n).
Proof. exact (MK_COMB (@lem2717247 n) (@lem2717244)). Qed.
Lemma lem2717249 (n : int) : (term230 n) = (term233 n).
Proof. exact (TRANS (@lem2717207 n) (@lem2717248 n)). Qed.
Lemma lem2717250 : term157 = term157.
Proof. exact (eq_refl term157). Qed.
Lemma lem2717251 (n : int) : (term248 n) = (term249 n).
Proof. exact (MK_COMB (@lem2717250) (@lem2717249 n)). Qed.
Lemma lem2717252 (n : int) : (term249 n) = (term250 n).
Proof. exact (@lem1982757 (term251 n) term110 term193). Qed.
Lemma lem2717254 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2717255 : term193 = term194.
Proof. exact (@lem2717254 term111). Qed.
Lemma lem2717257 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2717258 : term110 = term214.
Proof. exact (@lem2717257 term111). Qed.
Lemma lem2717259 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2717260 : term157 = term252.
Proof. exact (MK_COMB (@lem2717259) (@lem2717258)). Qed.
Lemma lem2717261 : term253 = term254.
Proof. exact (MK_COMB (@lem2717260) (@lem2717255)). Qed.
Lemma lem2717262 : term255.
Proof. exact (@lem1981473 term110 term110 term193 term110 term107 term110). Qed.
Lemma lem2717264 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2717265 : term257 = term258.
Proof. exact (@lem2717264 (NUMERAL 0) term111). Qed.
Lemma lem2717266 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2717267 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2717268 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2717267 h1) (fun h1 : term258 = True => @lem2717266)). Qed.
Lemma lem2717269 : term258 = True.
Proof. exact (EQ_MP (@lem2717268) (@lem2717266)). Qed.
Lemma lem2717270 : term257 = True.
Proof. exact (TRANS (@lem2717265) (@lem2717269)). Qed.
Lemma lem2717271 : True = term257.
Proof. exact (SYM (@lem2717270)). Qed.
Lemma lem2717272 : term257.
Proof. exact (EQ_MP (@lem2717271) (@lem0)). Qed.
Lemma lem2717273 : term260.
Proof. exact (@lem2717262 (@lem2717272)). Qed.
Lemma lem2717275 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2717276 : term257 = term258.
Proof. exact (@lem2717275 (NUMERAL 0) term111). Qed.
Lemma lem2717277 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2717278 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2717279 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2717278 h1) (fun h1 : term258 = True => @lem2717277)). Qed.
Lemma lem2717280 : term258 = True.
Proof. exact (EQ_MP (@lem2717279) (@lem2717277)). Qed.
Lemma lem2717281 : term257 = True.
Proof. exact (TRANS (@lem2717276) (@lem2717280)). Qed.
Lemma lem2717282 : True = term257.
Proof. exact (SYM (@lem2717281)). Qed.
Lemma lem2717283 : term257.
Proof. exact (EQ_MP (@lem2717282) (@lem0)). Qed.
Lemma lem2717284 : term261.
Proof. exact (@lem2717273 (@lem2717283)). Qed.
Lemma lem2717286 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2717287 : term257 = term258.
Proof. exact (@lem2717286 (NUMERAL 0) term111). Qed.
Lemma lem2717288 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2717289 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2717290 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2717289 h1) (fun h1 : term258 = True => @lem2717288)). Qed.
Lemma lem2717291 : term258 = True.
Proof. exact (EQ_MP (@lem2717290) (@lem2717288)). Qed.
Lemma lem2717292 : term257 = True.
Proof. exact (TRANS (@lem2717287) (@lem2717291)). Qed.
Lemma lem2717293 : True = term257.
Proof. exact (SYM (@lem2717292)). Qed.
Lemma lem2717294 : term257.
Proof. exact (EQ_MP (@lem2717293) (@lem0)). Qed.
Lemma lem2717295 : term262.
Proof. exact (@lem2717284 (@lem2717294)). Qed.
Lemma lem2717297 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2717298 : term215 = term220.
Proof. exact (@lem2717297 term111 term111). Qed.
Lemma lem2717299 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2717300 : term205 = term111.
Proof. exact (EQ_MP (@lem2717299) (@lem940073)). Qed.
Lemma lem2717301 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2717302 : term203 = term110.
Proof. exact (MK_COMB (@lem2717301) (@lem2717300)). Qed.
Lemma lem2717303 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2717304 : term220 = term193.
Proof. exact (MK_COMB (@lem2717303) (@lem2717302)). Qed.
Lemma lem2717305 : term215 = term193.
Proof. exact (TRANS (@lem2717298) (@lem2717304)). Qed.
Lemma lem2717307 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2717308 : term202 = term203.
Proof. exact (@lem2717307 term111 term111). Qed.
Lemma lem2717309 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2717310 : term205 = term111.
Proof. exact (EQ_MP (@lem2717309) (@lem940073)). Qed.
Lemma lem2717311 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2717312 : term203 = term110.
Proof. exact (MK_COMB (@lem2717311) (@lem2717310)). Qed.
Lemma lem2717313 : term202 = term110.
Proof. exact (TRANS (@lem2717308) (@lem2717312)). Qed.
Lemma lem2717314 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2717315 : term263 = term157.
Proof. exact (MK_COMB (@lem2717314) (@lem2717313)). Qed.
Lemma lem2717316 : term264 = term253.
Proof. exact (MK_COMB (@lem2717315) (@lem2717305)). Qed.
Lemma lem2717318 (m : nat) : (term265 m) = term107.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem2717319 : term253 = term107.
Proof. exact (@lem2717318 term111). Qed.
Lemma lem2717320 : term264 = term107.
Proof. exact (TRANS (@lem2717316) (@lem2717319)). Qed.
Lemma lem2717321 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2717322 : term266 = term267.
Proof. exact (MK_COMB (@lem2717321) (@lem2717320)). Qed.
Lemma lem2717323 : term110 = term110.
Proof. exact (eq_refl term110). Qed.
Lemma lem2717324 : term268 = term269.
Proof. exact (MK_COMB (@lem2717322) (@lem2717323)). Qed.
Lemma lem2717326 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2717327 : term269 = term107.
Proof. exact (@lem2717326 term111). Qed.
Lemma lem2717328 : term268 = term107.
Proof. exact (TRANS (@lem2717324) (@lem2717327)). Qed.
Lemma lem2717330 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2717331 : term202 = term203.
Proof. exact (@lem2717330 term111 term111). Qed.
Lemma lem2717332 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2717333 : term205 = term111.
Proof. exact (EQ_MP (@lem2717332) (@lem940073)). Qed.
Lemma lem2717334 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2717335 : term203 = term110.
Proof. exact (MK_COMB (@lem2717334) (@lem2717333)). Qed.
Lemma lem2717336 : term202 = term110.
Proof. exact (TRANS (@lem2717331) (@lem2717335)). Qed.
Lemma lem2717337 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2717338 : term271 = term269.
Proof. exact (MK_COMB (@lem2717337) (@lem2717336)). Qed.
Lemma lem2717340 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2717341 : term269 = term107.
Proof. exact (@lem2717340 term111). Qed.
Lemma lem2717342 : term271 = term107.
Proof. exact (TRANS (@lem2717338) (@lem2717341)). Qed.
Lemma lem2717343 : term107 = term271.
Proof. exact (SYM (@lem2717342)). Qed.
Lemma lem2717344 : term268 = term271.
Proof. exact (TRANS (@lem2717328) (@lem2717343)). Qed.
Lemma lem2717345 : term254 = term190.
Proof. exact (@lem2717295 (@lem2717344)). Qed.
Lemma lem2717346 : term253 = term190.
Proof. exact (TRANS (@lem2717261) (@lem2717345)). Qed.
Lemma lem2717348 (x : real) : (term209 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2717349 : term190 = term107.
Proof. exact (@lem2717348 term107). Qed.
Lemma lem2717350 : term253 = term107.
Proof. exact (TRANS (@lem2717346) (@lem2717349)). Qed.
Lemma lem2717351 (n : int) : (term232 n) = (term232 n).
Proof. exact (eq_refl (term232 n)). Qed.
Lemma lem2717352 (n : int) : (term250 n) = (term272 n).
Proof. exact (MK_COMB (@lem2717351 n) (@lem2717350)). Qed.
Lemma lem2717353 (n : int) : (term249 n) = (term272 n).
Proof. exact (TRANS (@lem2717252 n) (@lem2717352 n)). Qed.
Lemma lem2717354 (n : int) : (term272 n) = (term251 n).
Proof. exact (@lem1982723 (term251 n)). Qed.
Lemma lem2717355 (n : int) : (term249 n) = (term251 n).
Proof. exact (TRANS (@lem2717353 n) (@lem2717354 n)). Qed.
Lemma lem2717356 (n : int) : (term248 n) = (term251 n).
Proof. exact (TRANS (@lem2717251 n) (@lem2717355 n)). Qed.
Lemma lem2717358 (n : int) : (term247 n) = (term251 n).
Proof. exact (TRANS (@lem2717206 n) (@lem2717356 n)). Qed.
Lemma lem2717359 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2717360 (n : int) : (term273 n) = (term274 n).
Proof. exact (MK_COMB (@lem2717359) (@lem2717358 n)). Qed.
Lemma lem2717361 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2717362 (n : int) : (term246 n) = (term275 n).
Proof. exact (MK_COMB (@lem2717360 n) (@lem2717361)). Qed.
Lemma lem2717363 (n : int) : (term148 n) = (term275 n).
Proof. exact (TRANS (@lem2717194 n) (@lem2717362 n)). Qed.
Lemma lem2717364 (n : int) : (term161 n) = (term276 n).
Proof. exact (@lem1988287 (term104 n) term158). Qed.
Lemma lem2717371 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2717372 : term110 = term214.
Proof. exact (@lem2717371 term111). Qed.
Lemma lem2717374 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2717375 : term110 = term214.
Proof. exact (@lem2717374 term111). Qed.
Lemma lem2717376 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2717377 : term157 = term252.
Proof. exact (MK_COMB (@lem2717376) (@lem2717375)). Qed.
Lemma lem2717378 : term158 = term277.
Proof. exact (MK_COMB (@lem2717377) (@lem2717372)). Qed.
Lemma lem2717379 : term278.
Proof. exact (@lem1981473 term110 term110 term110 term110 term279 term110). Qed.
Lemma lem2717381 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2717382 : term257 = term258.
Proof. exact (@lem2717381 (NUMERAL 0) term111). Qed.
Lemma lem2717383 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2717384 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2717385 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2717384 h1) (fun h1 : term258 = True => @lem2717383)). Qed.
Lemma lem2717386 : term258 = True.
Proof. exact (EQ_MP (@lem2717385) (@lem2717383)). Qed.
Lemma lem2717387 : term257 = True.
Proof. exact (TRANS (@lem2717382) (@lem2717386)). Qed.
Lemma lem2717388 : True = term257.
Proof. exact (SYM (@lem2717387)). Qed.
Lemma lem2717389 : term257.
Proof. exact (EQ_MP (@lem2717388) (@lem0)). Qed.
Lemma lem2717390 : term280.
Proof. exact (@lem2717379 (@lem2717389)). Qed.
Lemma lem2717392 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2717393 : term257 = term258.
Proof. exact (@lem2717392 (NUMERAL 0) term111). Qed.
Lemma lem2717394 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2717395 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2717396 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2717395 h1) (fun h1 : term258 = True => @lem2717394)). Qed.
Lemma lem2717397 : term258 = True.
Proof. exact (EQ_MP (@lem2717396) (@lem2717394)). Qed.
Lemma lem2717398 : term257 = True.
Proof. exact (TRANS (@lem2717393) (@lem2717397)). Qed.
Lemma lem2717399 : True = term257.
Proof. exact (SYM (@lem2717398)). Qed.
Lemma lem2717400 : term257.
Proof. exact (EQ_MP (@lem2717399) (@lem0)). Qed.
Lemma lem2717401 : term281.
Proof. exact (@lem2717390 (@lem2717400)). Qed.
Lemma lem2717403 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2717404 : term257 = term258.
Proof. exact (@lem2717403 (NUMERAL 0) term111). Qed.
Lemma lem2717405 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2717406 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2717407 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2717406 h1) (fun h1 : term258 = True => @lem2717405)). Qed.
Lemma lem2717408 : term258 = True.
Proof. exact (EQ_MP (@lem2717407) (@lem2717405)). Qed.
Lemma lem2717409 : term257 = True.
Proof. exact (TRANS (@lem2717404) (@lem2717408)). Qed.
Lemma lem2717410 : True = term257.
Proof. exact (SYM (@lem2717409)). Qed.
Lemma lem2717411 : term257.
Proof. exact (EQ_MP (@lem2717410) (@lem0)). Qed.
Lemma lem2717412 : term282.
Proof. exact (@lem2717401 (@lem2717411)). Qed.
Lemma lem2717414 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2717415 : term202 = term203.
Proof. exact (@lem2717414 term111 term111). Qed.
Lemma lem2717416 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2717417 : term205 = term111.
Proof. exact (EQ_MP (@lem2717416) (@lem940073)). Qed.
Lemma lem2717418 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2717419 : term203 = term110.
Proof. exact (MK_COMB (@lem2717418) (@lem2717417)). Qed.
Lemma lem2717420 : term202 = term110.
Proof. exact (TRANS (@lem2717415) (@lem2717419)). Qed.
Lemma lem2717422 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2717423 : term202 = term203.
Proof. exact (@lem2717422 term111 term111). Qed.
Lemma lem2717424 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2717425 : term205 = term111.
Proof. exact (EQ_MP (@lem2717424) (@lem940073)). Qed.
Lemma lem2717426 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2717427 : term203 = term110.
Proof. exact (MK_COMB (@lem2717426) (@lem2717425)). Qed.
Lemma lem2717428 : term202 = term110.
Proof. exact (TRANS (@lem2717423) (@lem2717427)). Qed.
Lemma lem2717429 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2717430 : term263 = term157.
Proof. exact (MK_COMB (@lem2717429) (@lem2717428)). Qed.
Lemma lem2717431 : term283 = term158.
Proof. exact (MK_COMB (@lem2717430) (@lem2717420)). Qed.
Lemma lem2717432 : term158 = term284.
Proof. exact (@lem1367770 term111 term111). Qed.
Lemma lem2717433 : term285 = term286.
Proof. exact (@lem706885). Qed.
Lemma lem2717434 : (term285 = term286) = (term287 = term288).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term286). Qed.
Lemma lem2717435 : term287 = term288.
Proof. exact (EQ_MP (@lem2717434) (@lem2717433)). Qed.
Lemma lem2717436 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2717437 : term284 = term279.
Proof. exact (MK_COMB (@lem2717436) (@lem2717435)). Qed.
Lemma lem2717438 : term158 = term279.
Proof. exact (TRANS (@lem2717432) (@lem2717437)). Qed.
Lemma lem2717439 : term283 = term279.
Proof. exact (TRANS (@lem2717431) (@lem2717438)). Qed.
Lemma lem2717440 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2717441 : term289 = term290.
Proof. exact (MK_COMB (@lem2717440) (@lem2717439)). Qed.
Lemma lem2717442 : term110 = term110.
Proof. exact (eq_refl term110). Qed.
Lemma lem2717443 : term291 = term292.
Proof. exact (MK_COMB (@lem2717441) (@lem2717442)). Qed.
Lemma lem2717445 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2717446 : term292 = term293.
Proof. exact (@lem2717445 term288 term111). Qed.
Lemma lem2717447 : term294 = term286.
Proof. exact (@lem996237 term286). Qed.
Lemma lem2717448 : (term294 = term286) = (term295 = term288).
Proof. exact (@lem1007663 term286 (BIT1 0) term286). Qed.
Lemma lem2717449 : term295 = term288.
Proof. exact (EQ_MP (@lem2717448) (@lem2717447)). Qed.
Lemma lem2717450 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2717451 : term293 = term279.
Proof. exact (MK_COMB (@lem2717450) (@lem2717449)). Qed.
Lemma lem2717452 : term292 = term279.
Proof. exact (TRANS (@lem2717446) (@lem2717451)). Qed.
Lemma lem2717453 : term291 = term279.
Proof. exact (TRANS (@lem2717443) (@lem2717452)). Qed.
Lemma lem2717455 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2717456 : term202 = term203.
Proof. exact (@lem2717455 term111 term111). Qed.
Lemma lem2717457 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2717458 : term205 = term111.
Proof. exact (EQ_MP (@lem2717457) (@lem940073)). Qed.
Lemma lem2717459 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2717460 : term203 = term110.
Proof. exact (MK_COMB (@lem2717459) (@lem2717458)). Qed.
Lemma lem2717461 : term202 = term110.
Proof. exact (TRANS (@lem2717456) (@lem2717460)). Qed.
Lemma lem2717462 : term290 = term290.
Proof. exact (eq_refl term290). Qed.
Lemma lem2717463 : term296 = term292.
Proof. exact (MK_COMB (@lem2717462) (@lem2717461)). Qed.
Lemma lem2717465 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2717466 : term292 = term293.
Proof. exact (@lem2717465 term288 term111). Qed.
Lemma lem2717467 : term294 = term286.
Proof. exact (@lem996237 term286). Qed.
Lemma lem2717468 : (term294 = term286) = (term295 = term288).
Proof. exact (@lem1007663 term286 (BIT1 0) term286). Qed.
Lemma lem2717469 : term295 = term288.
Proof. exact (EQ_MP (@lem2717468) (@lem2717467)). Qed.
Lemma lem2717470 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2717471 : term293 = term279.
Proof. exact (MK_COMB (@lem2717470) (@lem2717469)). Qed.
Lemma lem2717472 : term292 = term279.
Proof. exact (TRANS (@lem2717466) (@lem2717471)). Qed.
Lemma lem2717473 : term296 = term279.
Proof. exact (TRANS (@lem2717463) (@lem2717472)). Qed.
Lemma lem2717474 : term279 = term296.
Proof. exact (SYM (@lem2717473)). Qed.
Lemma lem2717475 : term291 = term296.
Proof. exact (TRANS (@lem2717453) (@lem2717474)). Qed.
Lemma lem2717476 : term277 = term297.
Proof. exact (@lem2717412 (@lem2717475)). Qed.
Lemma lem2717477 : term158 = term297.
Proof. exact (TRANS (@lem2717378) (@lem2717476)). Qed.
Lemma lem2717479 (x : real) : (term209 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2717480 : term297 = term279.
Proof. exact (@lem2717479 term279). Qed.
Lemma lem2717482 : term158 = term279.
Proof. exact (TRANS (@lem2717477) (@lem2717480)). Qed.
Lemma lem2717485 (n : int) : (term239 n) = (term239 n).
Proof. exact (eq_refl (term239 n)). Qed.
Lemma lem2717486 (n : int) : (term298 n) = (term299 n).
Proof. exact (MK_COMB (@lem2717485 n) (@lem2717482)). Qed.
Lemma lem2717487 (n : int) : (term299 n) = (term300 n).
Proof. exact (@lem1982792 (term104 n) term279). Qed.
Lemma lem2717489 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2717490 : term279 = term297.
Proof. exact (@lem2717489 term288). Qed.
Lemma lem2717492 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2717493 : term193 = term194.
Proof. exact (@lem2717492 term111). Qed.
Lemma lem2717494 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2717495 : term195 = term196.
Proof. exact (MK_COMB (@lem2717494) (@lem2717493)). Qed.
Lemma lem2717496 : term301 = term302.
Proof. exact (MK_COMB (@lem2717495) (@lem2717490)). Qed.
Lemma lem2717497 : term302 = term303.
Proof. exact (@lem1981613 term193 term279 term110 term110). Qed.
Lemma lem2717499 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2717500 : term202 = term203.
Proof. exact (@lem2717499 term111 term111). Qed.
Lemma lem2717501 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2717502 : term205 = term111.
Proof. exact (EQ_MP (@lem2717501) (@lem940073)). Qed.
Lemma lem2717503 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2717504 : term203 = term110.
Proof. exact (MK_COMB (@lem2717503) (@lem2717502)). Qed.
Lemma lem2717505 : term202 = term110.
Proof. exact (TRANS (@lem2717500) (@lem2717504)). Qed.
Lemma lem2717507 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2717508 : term301 = term304.
Proof. exact (@lem2717507 term111 term288). Qed.
Lemma lem2717509 : term305 = term286.
Proof. exact (@lem996238 term286). Qed.
Lemma lem2717510 : (term305 = term286) = (term306 = term288).
Proof. exact (@lem1007663 (BIT1 0) term286 term286). Qed.
Lemma lem2717511 : term306 = term288.
Proof. exact (EQ_MP (@lem2717510) (@lem2717509)). Qed.
Lemma lem2717512 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2717513 : term307 = term279.
Proof. exact (MK_COMB (@lem2717512) (@lem2717511)). Qed.
Lemma lem2717514 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2717515 : term304 = term308.
Proof. exact (MK_COMB (@lem2717514) (@lem2717513)). Qed.
Lemma lem2717516 : term301 = term308.
Proof. exact (TRANS (@lem2717508) (@lem2717515)). Qed.
Lemma lem2717517 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2717518 : term309 = term310.
Proof. exact (MK_COMB (@lem2717517) (@lem2717516)). Qed.
Lemma lem2717519 : term303 = term311.
Proof. exact (MK_COMB (@lem2717518) (@lem2717505)). Qed.
Lemma lem2717520 : term302 = term311.
Proof. exact (TRANS (@lem2717497) (@lem2717519)). Qed.
Lemma lem2717521 : term301 = term311.
Proof. exact (TRANS (@lem2717496) (@lem2717520)). Qed.
Lemma lem2717523 (x : real) : (term209 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2717524 : term311 = term308.
Proof. exact (@lem2717523 term308). Qed.
Lemma lem2717525 : term301 = term308.
Proof. exact (TRANS (@lem2717521) (@lem2717524)). Qed.
Lemma lem2717526 (n : int) : (term126 n) = (term126 n).
Proof. exact (eq_refl (term126 n)). Qed.
Lemma lem2717529 (n : int) : (term300 n) = (term312 n).
Proof. exact (MK_COMB (@lem2717526 n) (@lem2717525)). Qed.
Lemma lem2717530 (n : int) : (term299 n) = (term312 n).
Proof. exact (TRANS (@lem2717487 n) (@lem2717529 n)). Qed.
Lemma lem2717531 (n : int) : (term298 n) = (term312 n).
Proof. exact (TRANS (@lem2717486 n) (@lem2717530 n)). Qed.
Lemma lem2717532 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2717533 (n : int) : (term313 n) = (term314 n).
Proof. exact (MK_COMB (@lem2717532) (@lem2717531 n)). Qed.
Lemma lem2717534 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2717535 (n : int) : (term276 n) = (term315 n).
Proof. exact (MK_COMB (@lem2717533 n) (@lem2717534)). Qed.
Lemma lem2717536 (n : int) : (term161 n) = (term315 n).
Proof. exact (TRANS (@lem2717364 n) (@lem2717535 n)). Qed.
Lemma lem2717537 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2717538 (n : int) : (term150 n) = (term316 n).
Proof. exact (MK_COMB (@lem2717537) (@lem2717363 n)). Qed.
Lemma lem2717539 (n : int) : (term162 n) = (term317 n).
Proof. exact (MK_COMB (@lem2717538 n) (@lem2717536 n)). Qed.
Lemma lem2717540 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2717541 (n : int) : (term164 n) = (term318 n).
Proof. exact (MK_COMB (@lem2717540) (@lem2717193 n)). Qed.
Lemma lem2717542 (n : int) : (term166 n) = (term319 n).
Proof. exact (MK_COMB (@lem2717541 n) (@lem2717539 n)). Qed.
Lemma lem2717543 (n : int) : ((term104 n) = term107) = ((term187 n) = term107).
Proof. exact (@lem1988293 (term104 n) term107). Qed.
Lemma lem2717549 (n : int) : (term187 n) = (term188 n).
Proof. exact (@lem1982792 (term104 n) term107). Qed.
Lemma lem2717551 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2717552 : term107 = term190.
Proof. exact (@lem2717551 (NUMERAL 0)). Qed.
Lemma lem2717554 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2717555 : term193 = term194.
Proof. exact (@lem2717554 term111). Qed.
Lemma lem2717556 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2717557 : term195 = term196.
Proof. exact (MK_COMB (@lem2717556) (@lem2717555)). Qed.
Lemma lem2717558 : term197 = term198.
Proof. exact (MK_COMB (@lem2717557) (@lem2717552)). Qed.
Lemma lem2717559 : term198 = term199.
Proof. exact (@lem1981613 term193 term107 term110 term110). Qed.
Lemma lem2717561 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2717562 : term202 = term203.
Proof. exact (@lem2717561 term111 term111). Qed.
Lemma lem2717563 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2717564 : term205 = term111.
Proof. exact (EQ_MP (@lem2717563) (@lem940073)). Qed.
Lemma lem2717565 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2717566 : term203 = term110.
Proof. exact (MK_COMB (@lem2717565) (@lem2717564)). Qed.
Lemma lem2717567 : term202 = term110.
Proof. exact (TRANS (@lem2717562) (@lem2717566)). Qed.
Lemma lem2717569 (x : nat) : (term206 x) = term107.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2717570 : term197 = term107.
Proof. exact (@lem2717569 term111). Qed.
Lemma lem2717571 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2717572 : term207 = term208.
Proof. exact (MK_COMB (@lem2717571) (@lem2717570)). Qed.
Lemma lem2717573 : term199 = term190.
Proof. exact (MK_COMB (@lem2717572) (@lem2717567)). Qed.
Lemma lem2717574 : term198 = term190.
Proof. exact (TRANS (@lem2717559) (@lem2717573)). Qed.
Lemma lem2717575 : term197 = term190.
Proof. exact (TRANS (@lem2717558) (@lem2717574)). Qed.
Lemma lem2717577 (x : real) : (term209 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2717578 : term190 = term107.
Proof. exact (@lem2717577 term107). Qed.
Lemma lem2717579 : term197 = term107.
Proof. exact (TRANS (@lem2717575) (@lem2717578)). Qed.
Lemma lem2717580 (n : int) : (term126 n) = (term126 n).
Proof. exact (eq_refl (term126 n)). Qed.
Lemma lem2717581 (n : int) : (term188 n) = (term210 n).
Proof. exact (MK_COMB (@lem2717580 n) (@lem2717579)). Qed.
Lemma lem2717582 (n : int) : (term210 n) = (term104 n).
Proof. exact (@lem1982723 (term104 n)). Qed.
Lemma lem2717583 (n : int) : (term188 n) = (term104 n).
Proof. exact (TRANS (@lem2717581 n) (@lem2717582 n)). Qed.
Lemma lem2717585 (n : int) : (term187 n) = (term104 n).
Proof. exact (TRANS (@lem2717549 n) (@lem2717583 n)). Qed.
Lemma lem2717586 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2717587 (n : int) : (term211 n) = (term108 n).
Proof. exact (MK_COMB (@lem2717586) (@lem2717585 n)). Qed.
Lemma lem2717588 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2717589 (n : int) : ((term187 n) = term107) = ((term104 n) = term107).
Proof. exact (MK_COMB (@lem2717587 n) (@lem2717588)). Qed.
Lemma lem2717590 (n : int) : ((term104 n) = term107) = ((term104 n) = term107).
Proof. exact (TRANS (@lem2717543 n) (@lem2717589 n)). Qed.
Lemma lem2717591 (n : int) : ((term104 n) = term110) = ((term212 n) = term107).
Proof. exact (@lem1988293 (term104 n) term110). Qed.
Lemma lem2717597 (n : int) : (term212 n) = (term213 n).
Proof. exact (@lem1982792 (term104 n) term110). Qed.
Lemma lem2717599 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2717600 : term110 = term214.
Proof. exact (@lem2717599 term111). Qed.
Lemma lem2717602 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2717603 : term193 = term194.
Proof. exact (@lem2717602 term111). Qed.
Lemma lem2717604 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2717605 : term195 = term196.
Proof. exact (MK_COMB (@lem2717604) (@lem2717603)). Qed.
Lemma lem2717606 : term215 = term216.
Proof. exact (MK_COMB (@lem2717605) (@lem2717600)). Qed.
Lemma lem2717607 : term216 = term217.
Proof. exact (@lem1981613 term193 term110 term110 term110). Qed.
Lemma lem2717609 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2717610 : term202 = term203.
Proof. exact (@lem2717609 term111 term111). Qed.
Lemma lem2717611 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2717612 : term205 = term111.
Proof. exact (EQ_MP (@lem2717611) (@lem940073)). Qed.
Lemma lem2717613 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2717614 : term203 = term110.
Proof. exact (MK_COMB (@lem2717613) (@lem2717612)). Qed.
Lemma lem2717615 : term202 = term110.
Proof. exact (TRANS (@lem2717610) (@lem2717614)). Qed.
Lemma lem2717617 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2717618 : term215 = term220.
Proof. exact (@lem2717617 term111 term111). Qed.
Lemma lem2717619 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2717620 : term205 = term111.
Proof. exact (EQ_MP (@lem2717619) (@lem940073)). Qed.
Lemma lem2717621 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2717622 : term203 = term110.
Proof. exact (MK_COMB (@lem2717621) (@lem2717620)). Qed.
Lemma lem2717623 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2717624 : term220 = term193.
Proof. exact (MK_COMB (@lem2717623) (@lem2717622)). Qed.
Lemma lem2717625 : term215 = term193.
Proof. exact (TRANS (@lem2717618) (@lem2717624)). Qed.
Lemma lem2717626 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2717627 : term221 = term222.
Proof. exact (MK_COMB (@lem2717626) (@lem2717625)). Qed.
Lemma lem2717628 : term217 = term194.
Proof. exact (MK_COMB (@lem2717627) (@lem2717615)). Qed.
Lemma lem2717629 : term216 = term194.
Proof. exact (TRANS (@lem2717607) (@lem2717628)). Qed.
Lemma lem2717630 : term215 = term194.
Proof. exact (TRANS (@lem2717606) (@lem2717629)). Qed.
Lemma lem2717632 (x : real) : (term209 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2717633 : term194 = term193.
Proof. exact (@lem2717632 term193). Qed.
Lemma lem2717634 : term215 = term193.
Proof. exact (TRANS (@lem2717630) (@lem2717633)). Qed.
Lemma lem2717635 (n : int) : (term126 n) = (term126 n).
Proof. exact (eq_refl (term126 n)). Qed.
Lemma lem2717638 (n : int) : (term213 n) = (term223 n).
Proof. exact (MK_COMB (@lem2717635 n) (@lem2717634)). Qed.
Lemma lem2717640 (n : int) : (term212 n) = (term223 n).
Proof. exact (TRANS (@lem2717597 n) (@lem2717638 n)). Qed.
Lemma lem2717641 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2717642 (n : int) : (term224 n) = (term225 n).
Proof. exact (MK_COMB (@lem2717641) (@lem2717640 n)). Qed.
Lemma lem2717643 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2717644 (n : int) : ((term212 n) = term107) = ((term223 n) = term107).
Proof. exact (MK_COMB (@lem2717642 n) (@lem2717643)). Qed.
Lemma lem2717645 (n : int) : ((term104 n) = term110) = ((term223 n) = term107).
Proof. exact (TRANS (@lem2717591 n) (@lem2717644 n)). Qed.
Lemma lem2717646 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2717647 (n : int) : (term167 n) = (term167 n).
Proof. exact (MK_COMB (@lem2717646) (@lem2717590 n)). Qed.
Lemma lem2717648 (n : int) : (term168 n) = (term320 n).
Proof. exact (MK_COMB (@lem2717647 n) (@lem2717645 n)). Qed.
Lemma lem2717649 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2717650 (n : int) : (term169 n) = (term321 n).
Proof. exact (MK_COMB (@lem2717649) (@lem2717542 n)). Qed.
Lemma lem2717651 (n : int) : (term170 n) = (term322 n).
Proof. exact (MK_COMB (@lem2717650 n) (@lem2717648 n)). Qed.
Lemma lem2717652 (n : int) : (term148 n) = (term246 n).
Proof. exact (@lem1988287 term110 (term127 n)). Qed.
Lemma lem2717664 (n : int) : (term247 n) = (term248 n).
Proof. exact (@lem1982792 term110 (term127 n)). Qed.
Lemma lem2717665 (n : int) : (term230 n) = (term231 n).
Proof. exact (@lem1982781 (term104 n) term193 term110). Qed.
Lemma lem2717667 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2717668 : term110 = term214.
Proof. exact (@lem2717667 term111). Qed.
Lemma lem2717670 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2717671 : term193 = term194.
Proof. exact (@lem2717670 term111). Qed.
Lemma lem2717672 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2717673 : term195 = term196.
Proof. exact (MK_COMB (@lem2717672) (@lem2717671)). Qed.
Lemma lem2717674 : term215 = term216.
Proof. exact (MK_COMB (@lem2717673) (@lem2717668)). Qed.
Lemma lem2717675 : term216 = term217.
Proof. exact (@lem1981613 term193 term110 term110 term110). Qed.
Lemma lem2717677 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2717678 : term202 = term203.
Proof. exact (@lem2717677 term111 term111). Qed.
Lemma lem2717679 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2717680 : term205 = term111.
Proof. exact (EQ_MP (@lem2717679) (@lem940073)). Qed.
Lemma lem2717681 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2717682 : term203 = term110.
Proof. exact (MK_COMB (@lem2717681) (@lem2717680)). Qed.
Lemma lem2717683 : term202 = term110.
Proof. exact (TRANS (@lem2717678) (@lem2717682)). Qed.
Lemma lem2717685 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2717686 : term215 = term220.
Proof. exact (@lem2717685 term111 term111). Qed.
Lemma lem2717687 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2717688 : term205 = term111.
Proof. exact (EQ_MP (@lem2717687) (@lem940073)). Qed.
Lemma lem2717689 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2717690 : term203 = term110.
Proof. exact (MK_COMB (@lem2717689) (@lem2717688)). Qed.
Lemma lem2717691 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2717692 : term220 = term193.
Proof. exact (MK_COMB (@lem2717691) (@lem2717690)). Qed.
Lemma lem2717693 : term215 = term193.
Proof. exact (TRANS (@lem2717686) (@lem2717692)). Qed.
Lemma lem2717694 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2717695 : term221 = term222.
Proof. exact (MK_COMB (@lem2717694) (@lem2717693)). Qed.
Lemma lem2717696 : term217 = term194.
Proof. exact (MK_COMB (@lem2717695) (@lem2717683)). Qed.
Lemma lem2717697 : term216 = term194.
Proof. exact (TRANS (@lem2717675) (@lem2717696)). Qed.
Lemma lem2717698 : term215 = term194.
Proof. exact (TRANS (@lem2717674) (@lem2717697)). Qed.
Lemma lem2717700 (x : real) : (term209 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2717701 : term194 = term193.
Proof. exact (@lem2717700 term193). Qed.
Lemma lem2717702 : term215 = term193.
Proof. exact (TRANS (@lem2717698) (@lem2717701)). Qed.
Lemma lem2717705 (n : int) : (term232 n) = (term232 n).
Proof. exact (eq_refl (term232 n)). Qed.
Lemma lem2717706 (n : int) : (term231 n) = (term233 n).
Proof. exact (MK_COMB (@lem2717705 n) (@lem2717702)). Qed.
Lemma lem2717707 (n : int) : (term230 n) = (term233 n).
Proof. exact (TRANS (@lem2717665 n) (@lem2717706 n)). Qed.
Lemma lem2717708 : term157 = term157.
Proof. exact (eq_refl term157). Qed.
Lemma lem2717709 (n : int) : (term248 n) = (term249 n).
Proof. exact (MK_COMB (@lem2717708) (@lem2717707 n)). Qed.
Lemma lem2717710 (n : int) : (term249 n) = (term250 n).
Proof. exact (@lem1982757 (term251 n) term110 term193). Qed.
Lemma lem2717712 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2717713 : term193 = term194.
Proof. exact (@lem2717712 term111). Qed.
Lemma lem2717715 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2717716 : term110 = term214.
Proof. exact (@lem2717715 term111). Qed.
Lemma lem2717717 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2717718 : term157 = term252.
Proof. exact (MK_COMB (@lem2717717) (@lem2717716)). Qed.
Lemma lem2717719 : term253 = term254.
Proof. exact (MK_COMB (@lem2717718) (@lem2717713)). Qed.
Lemma lem2717720 : term255.
Proof. exact (@lem1981473 term110 term110 term193 term110 term107 term110). Qed.
Lemma lem2717722 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2717723 : term257 = term258.
Proof. exact (@lem2717722 (NUMERAL 0) term111). Qed.
Lemma lem2717724 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2717725 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2717726 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2717725 h1) (fun h1 : term258 = True => @lem2717724)). Qed.
Lemma lem2717727 : term258 = True.
Proof. exact (EQ_MP (@lem2717726) (@lem2717724)). Qed.
Lemma lem2717728 : term257 = True.
Proof. exact (TRANS (@lem2717723) (@lem2717727)). Qed.
Lemma lem2717729 : True = term257.
Proof. exact (SYM (@lem2717728)). Qed.
Lemma lem2717730 : term257.
Proof. exact (EQ_MP (@lem2717729) (@lem0)). Qed.
Lemma lem2717731 : term260.
Proof. exact (@lem2717720 (@lem2717730)). Qed.
Lemma lem2717733 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2717734 : term257 = term258.
Proof. exact (@lem2717733 (NUMERAL 0) term111). Qed.
Lemma lem2717735 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2717736 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2717737 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2717736 h1) (fun h1 : term258 = True => @lem2717735)). Qed.
Lemma lem2717738 : term258 = True.
Proof. exact (EQ_MP (@lem2717737) (@lem2717735)). Qed.
Lemma lem2717739 : term257 = True.
Proof. exact (TRANS (@lem2717734) (@lem2717738)). Qed.
Lemma lem2717740 : True = term257.
Proof. exact (SYM (@lem2717739)). Qed.
Lemma lem2717741 : term257.
Proof. exact (EQ_MP (@lem2717740) (@lem0)). Qed.
Lemma lem2717742 : term261.
Proof. exact (@lem2717731 (@lem2717741)). Qed.
Lemma lem2717744 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2717745 : term257 = term258.
Proof. exact (@lem2717744 (NUMERAL 0) term111). Qed.
Lemma lem2717746 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2717747 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2717748 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2717747 h1) (fun h1 : term258 = True => @lem2717746)). Qed.
Lemma lem2717749 : term258 = True.
Proof. exact (EQ_MP (@lem2717748) (@lem2717746)). Qed.
Lemma lem2717750 : term257 = True.
Proof. exact (TRANS (@lem2717745) (@lem2717749)). Qed.
Lemma lem2717751 : True = term257.
Proof. exact (SYM (@lem2717750)). Qed.
Lemma lem2717752 : term257.
Proof. exact (EQ_MP (@lem2717751) (@lem0)). Qed.
Lemma lem2717753 : term262.
Proof. exact (@lem2717742 (@lem2717752)). Qed.
Lemma lem2717755 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2717756 : term215 = term220.
Proof. exact (@lem2717755 term111 term111). Qed.
Lemma lem2717757 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2717758 : term205 = term111.
Proof. exact (EQ_MP (@lem2717757) (@lem940073)). Qed.
Lemma lem2717759 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2717760 : term203 = term110.
Proof. exact (MK_COMB (@lem2717759) (@lem2717758)). Qed.
Lemma lem2717761 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2717762 : term220 = term193.
Proof. exact (MK_COMB (@lem2717761) (@lem2717760)). Qed.
Lemma lem2717763 : term215 = term193.
Proof. exact (TRANS (@lem2717756) (@lem2717762)). Qed.
Lemma lem2717765 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2717766 : term202 = term203.
Proof. exact (@lem2717765 term111 term111). Qed.
Lemma lem2717767 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2717768 : term205 = term111.
Proof. exact (EQ_MP (@lem2717767) (@lem940073)). Qed.
Lemma lem2717769 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2717770 : term203 = term110.
Proof. exact (MK_COMB (@lem2717769) (@lem2717768)). Qed.
Lemma lem2717771 : term202 = term110.
Proof. exact (TRANS (@lem2717766) (@lem2717770)). Qed.
Lemma lem2717772 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2717773 : term263 = term157.
Proof. exact (MK_COMB (@lem2717772) (@lem2717771)). Qed.
Lemma lem2717774 : term264 = term253.
Proof. exact (MK_COMB (@lem2717773) (@lem2717763)). Qed.
Lemma lem2717776 (m : nat) : (term265 m) = term107.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem2717777 : term253 = term107.
Proof. exact (@lem2717776 term111). Qed.
Lemma lem2717778 : term264 = term107.
Proof. exact (TRANS (@lem2717774) (@lem2717777)). Qed.
Lemma lem2717779 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2717780 : term266 = term267.
Proof. exact (MK_COMB (@lem2717779) (@lem2717778)). Qed.
Lemma lem2717781 : term110 = term110.
Proof. exact (eq_refl term110). Qed.
Lemma lem2717782 : term268 = term269.
Proof. exact (MK_COMB (@lem2717780) (@lem2717781)). Qed.
Lemma lem2717784 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2717785 : term269 = term107.
Proof. exact (@lem2717784 term111). Qed.
Lemma lem2717786 : term268 = term107.
Proof. exact (TRANS (@lem2717782) (@lem2717785)). Qed.
Lemma lem2717788 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2717789 : term202 = term203.
Proof. exact (@lem2717788 term111 term111). Qed.
Lemma lem2717790 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2717791 : term205 = term111.
Proof. exact (EQ_MP (@lem2717790) (@lem940073)). Qed.
Lemma lem2717792 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2717793 : term203 = term110.
Proof. exact (MK_COMB (@lem2717792) (@lem2717791)). Qed.
Lemma lem2717794 : term202 = term110.
Proof. exact (TRANS (@lem2717789) (@lem2717793)). Qed.
Lemma lem2717795 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2717796 : term271 = term269.
Proof. exact (MK_COMB (@lem2717795) (@lem2717794)). Qed.
Lemma lem2717798 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2717799 : term269 = term107.
Proof. exact (@lem2717798 term111). Qed.
Lemma lem2717800 : term271 = term107.
Proof. exact (TRANS (@lem2717796) (@lem2717799)). Qed.
Lemma lem2717801 : term107 = term271.
Proof. exact (SYM (@lem2717800)). Qed.
Lemma lem2717802 : term268 = term271.
Proof. exact (TRANS (@lem2717786) (@lem2717801)). Qed.
Lemma lem2717803 : term254 = term190.
Proof. exact (@lem2717753 (@lem2717802)). Qed.
Lemma lem2717804 : term253 = term190.
Proof. exact (TRANS (@lem2717719) (@lem2717803)). Qed.
Lemma lem2717806 (x : real) : (term209 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2717807 : term190 = term107.
Proof. exact (@lem2717806 term107). Qed.
Lemma lem2717808 : term253 = term107.
Proof. exact (TRANS (@lem2717804) (@lem2717807)). Qed.
Lemma lem2717809 (n : int) : (term232 n) = (term232 n).
Proof. exact (eq_refl (term232 n)). Qed.
Lemma lem2717810 (n : int) : (term250 n) = (term272 n).
Proof. exact (MK_COMB (@lem2717809 n) (@lem2717808)). Qed.
Lemma lem2717811 (n : int) : (term249 n) = (term272 n).
Proof. exact (TRANS (@lem2717710 n) (@lem2717810 n)). Qed.
Lemma lem2717812 (n : int) : (term272 n) = (term251 n).
Proof. exact (@lem1982723 (term251 n)). Qed.
Lemma lem2717813 (n : int) : (term249 n) = (term251 n).
Proof. exact (TRANS (@lem2717811 n) (@lem2717812 n)). Qed.
Lemma lem2717814 (n : int) : (term248 n) = (term251 n).
Proof. exact (TRANS (@lem2717709 n) (@lem2717813 n)). Qed.
Lemma lem2717816 (n : int) : (term247 n) = (term251 n).
Proof. exact (TRANS (@lem2717664 n) (@lem2717814 n)). Qed.
Lemma lem2717817 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2717818 (n : int) : (term273 n) = (term274 n).
Proof. exact (MK_COMB (@lem2717817) (@lem2717816 n)). Qed.
Lemma lem2717819 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2717820 (n : int) : (term246 n) = (term275 n).
Proof. exact (MK_COMB (@lem2717818 n) (@lem2717819)). Qed.
Lemma lem2717821 (n : int) : (term148 n) = (term275 n).
Proof. exact (TRANS (@lem2717652 n) (@lem2717820 n)). Qed.
Lemma lem2717822 (n : int) : (term161 n) = (term276 n).
Proof. exact (@lem1988287 (term104 n) term158). Qed.
Lemma lem2717829 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2717830 : term110 = term214.
Proof. exact (@lem2717829 term111). Qed.
Lemma lem2717832 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2717833 : term110 = term214.
Proof. exact (@lem2717832 term111). Qed.
Lemma lem2717834 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2717835 : term157 = term252.
Proof. exact (MK_COMB (@lem2717834) (@lem2717833)). Qed.
Lemma lem2717836 : term158 = term277.
Proof. exact (MK_COMB (@lem2717835) (@lem2717830)). Qed.
Lemma lem2717837 : term278.
Proof. exact (@lem1981473 term110 term110 term110 term110 term279 term110). Qed.
Lemma lem2717839 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2717840 : term257 = term258.
Proof. exact (@lem2717839 (NUMERAL 0) term111). Qed.
Lemma lem2717841 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2717842 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2717843 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2717842 h1) (fun h1 : term258 = True => @lem2717841)). Qed.
Lemma lem2717844 : term258 = True.
Proof. exact (EQ_MP (@lem2717843) (@lem2717841)). Qed.
Lemma lem2717845 : term257 = True.
Proof. exact (TRANS (@lem2717840) (@lem2717844)). Qed.
Lemma lem2717846 : True = term257.
Proof. exact (SYM (@lem2717845)). Qed.
Lemma lem2717847 : term257.
Proof. exact (EQ_MP (@lem2717846) (@lem0)). Qed.
Lemma lem2717848 : term280.
Proof. exact (@lem2717837 (@lem2717847)). Qed.
Lemma lem2717850 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2717851 : term257 = term258.
Proof. exact (@lem2717850 (NUMERAL 0) term111). Qed.
Lemma lem2717852 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2717853 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2717854 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2717853 h1) (fun h1 : term258 = True => @lem2717852)). Qed.
Lemma lem2717855 : term258 = True.
Proof. exact (EQ_MP (@lem2717854) (@lem2717852)). Qed.
Lemma lem2717856 : term257 = True.
Proof. exact (TRANS (@lem2717851) (@lem2717855)). Qed.
Lemma lem2717857 : True = term257.
Proof. exact (SYM (@lem2717856)). Qed.
Lemma lem2717858 : term257.
Proof. exact (EQ_MP (@lem2717857) (@lem0)). Qed.
Lemma lem2717859 : term281.
Proof. exact (@lem2717848 (@lem2717858)). Qed.
Lemma lem2717861 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2717862 : term257 = term258.
Proof. exact (@lem2717861 (NUMERAL 0) term111). Qed.
Lemma lem2717863 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2717864 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2717865 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2717864 h1) (fun h1 : term258 = True => @lem2717863)). Qed.
Lemma lem2717866 : term258 = True.
Proof. exact (EQ_MP (@lem2717865) (@lem2717863)). Qed.
Lemma lem2717867 : term257 = True.
Proof. exact (TRANS (@lem2717862) (@lem2717866)). Qed.
Lemma lem2717868 : True = term257.
Proof. exact (SYM (@lem2717867)). Qed.
Lemma lem2717869 : term257.
Proof. exact (EQ_MP (@lem2717868) (@lem0)). Qed.
Lemma lem2717870 : term282.
Proof. exact (@lem2717859 (@lem2717869)). Qed.
Lemma lem2717872 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2717873 : term202 = term203.
Proof. exact (@lem2717872 term111 term111). Qed.
Lemma lem2717874 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2717875 : term205 = term111.
Proof. exact (EQ_MP (@lem2717874) (@lem940073)). Qed.
Lemma lem2717876 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2717877 : term203 = term110.
Proof. exact (MK_COMB (@lem2717876) (@lem2717875)). Qed.
Lemma lem2717878 : term202 = term110.
Proof. exact (TRANS (@lem2717873) (@lem2717877)). Qed.
Lemma lem2717880 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2717881 : term202 = term203.
Proof. exact (@lem2717880 term111 term111). Qed.
Lemma lem2717882 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2717883 : term205 = term111.
Proof. exact (EQ_MP (@lem2717882) (@lem940073)). Qed.
Lemma lem2717884 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2717885 : term203 = term110.
Proof. exact (MK_COMB (@lem2717884) (@lem2717883)). Qed.
Lemma lem2717886 : term202 = term110.
Proof. exact (TRANS (@lem2717881) (@lem2717885)). Qed.
Lemma lem2717887 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2717888 : term263 = term157.
Proof. exact (MK_COMB (@lem2717887) (@lem2717886)). Qed.
Lemma lem2717889 : term283 = term158.
Proof. exact (MK_COMB (@lem2717888) (@lem2717878)). Qed.
Lemma lem2717890 : term158 = term284.
Proof. exact (@lem1367770 term111 term111). Qed.
Lemma lem2717891 : term285 = term286.
Proof. exact (@lem706885). Qed.
Lemma lem2717892 : (term285 = term286) = (term287 = term288).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term286). Qed.
Lemma lem2717893 : term287 = term288.
Proof. exact (EQ_MP (@lem2717892) (@lem2717891)). Qed.
Lemma lem2717894 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2717895 : term284 = term279.
Proof. exact (MK_COMB (@lem2717894) (@lem2717893)). Qed.
Lemma lem2717896 : term158 = term279.
Proof. exact (TRANS (@lem2717890) (@lem2717895)). Qed.
Lemma lem2717897 : term283 = term279.
Proof. exact (TRANS (@lem2717889) (@lem2717896)). Qed.
Lemma lem2717898 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2717899 : term289 = term290.
Proof. exact (MK_COMB (@lem2717898) (@lem2717897)). Qed.
Lemma lem2717900 : term110 = term110.
Proof. exact (eq_refl term110). Qed.
Lemma lem2717901 : term291 = term292.
Proof. exact (MK_COMB (@lem2717899) (@lem2717900)). Qed.
Lemma lem2717903 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2717904 : term292 = term293.
Proof. exact (@lem2717903 term288 term111). Qed.
Lemma lem2717905 : term294 = term286.
Proof. exact (@lem996237 term286). Qed.
Lemma lem2717906 : (term294 = term286) = (term295 = term288).
Proof. exact (@lem1007663 term286 (BIT1 0) term286). Qed.
Lemma lem2717907 : term295 = term288.
Proof. exact (EQ_MP (@lem2717906) (@lem2717905)). Qed.
Lemma lem2717908 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2717909 : term293 = term279.
Proof. exact (MK_COMB (@lem2717908) (@lem2717907)). Qed.
Lemma lem2717910 : term292 = term279.
Proof. exact (TRANS (@lem2717904) (@lem2717909)). Qed.
Lemma lem2717911 : term291 = term279.
Proof. exact (TRANS (@lem2717901) (@lem2717910)). Qed.
Lemma lem2717913 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2717914 : term202 = term203.
Proof. exact (@lem2717913 term111 term111). Qed.
Lemma lem2717915 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2717916 : term205 = term111.
Proof. exact (EQ_MP (@lem2717915) (@lem940073)). Qed.
Lemma lem2717917 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2717918 : term203 = term110.
Proof. exact (MK_COMB (@lem2717917) (@lem2717916)). Qed.
Lemma lem2717919 : term202 = term110.
Proof. exact (TRANS (@lem2717914) (@lem2717918)). Qed.
Lemma lem2717920 : term290 = term290.
Proof. exact (eq_refl term290). Qed.
Lemma lem2717921 : term296 = term292.
Proof. exact (MK_COMB (@lem2717920) (@lem2717919)). Qed.
Lemma lem2717923 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2717924 : term292 = term293.
Proof. exact (@lem2717923 term288 term111). Qed.
Lemma lem2717925 : term294 = term286.
Proof. exact (@lem996237 term286). Qed.
Lemma lem2717926 : (term294 = term286) = (term295 = term288).
Proof. exact (@lem1007663 term286 (BIT1 0) term286). Qed.
Lemma lem2717927 : term295 = term288.
Proof. exact (EQ_MP (@lem2717926) (@lem2717925)). Qed.
Lemma lem2717928 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2717929 : term293 = term279.
Proof. exact (MK_COMB (@lem2717928) (@lem2717927)). Qed.
Lemma lem2717930 : term292 = term279.
Proof. exact (TRANS (@lem2717924) (@lem2717929)). Qed.
Lemma lem2717931 : term296 = term279.
Proof. exact (TRANS (@lem2717921) (@lem2717930)). Qed.
Lemma lem2717932 : term279 = term296.
Proof. exact (SYM (@lem2717931)). Qed.
Lemma lem2717933 : term291 = term296.
Proof. exact (TRANS (@lem2717911) (@lem2717932)). Qed.
Lemma lem2717934 : term277 = term297.
Proof. exact (@lem2717870 (@lem2717933)). Qed.
Lemma lem2717935 : term158 = term297.
Proof. exact (TRANS (@lem2717836) (@lem2717934)). Qed.
Lemma lem2717937 (x : real) : (term209 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2717938 : term297 = term279.
Proof. exact (@lem2717937 term279). Qed.
Lemma lem2717940 : term158 = term279.
Proof. exact (TRANS (@lem2717935) (@lem2717938)). Qed.
Lemma lem2717943 (n : int) : (term239 n) = (term239 n).
Proof. exact (eq_refl (term239 n)). Qed.
Lemma lem2717944 (n : int) : (term298 n) = (term299 n).
Proof. exact (MK_COMB (@lem2717943 n) (@lem2717940)). Qed.
Lemma lem2717945 (n : int) : (term299 n) = (term300 n).
Proof. exact (@lem1982792 (term104 n) term279). Qed.
Lemma lem2717947 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2717948 : term279 = term297.
Proof. exact (@lem2717947 term288). Qed.
Lemma lem2717950 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2717951 : term193 = term194.
Proof. exact (@lem2717950 term111). Qed.
Lemma lem2717952 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2717953 : term195 = term196.
Proof. exact (MK_COMB (@lem2717952) (@lem2717951)). Qed.
Lemma lem2717954 : term301 = term302.
Proof. exact (MK_COMB (@lem2717953) (@lem2717948)). Qed.
Lemma lem2717955 : term302 = term303.
Proof. exact (@lem1981613 term193 term279 term110 term110). Qed.
Lemma lem2717957 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2717958 : term202 = term203.
Proof. exact (@lem2717957 term111 term111). Qed.
Lemma lem2717959 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2717960 : term205 = term111.
Proof. exact (EQ_MP (@lem2717959) (@lem940073)). Qed.
Lemma lem2717961 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2717962 : term203 = term110.
Proof. exact (MK_COMB (@lem2717961) (@lem2717960)). Qed.
Lemma lem2717963 : term202 = term110.
Proof. exact (TRANS (@lem2717958) (@lem2717962)). Qed.
Lemma lem2717965 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2717966 : term301 = term304.
Proof. exact (@lem2717965 term111 term288). Qed.
Lemma lem2717967 : term305 = term286.
Proof. exact (@lem996238 term286). Qed.
Lemma lem2717968 : (term305 = term286) = (term306 = term288).
Proof. exact (@lem1007663 (BIT1 0) term286 term286). Qed.
Lemma lem2717969 : term306 = term288.
Proof. exact (EQ_MP (@lem2717968) (@lem2717967)). Qed.
Lemma lem2717970 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2717971 : term307 = term279.
Proof. exact (MK_COMB (@lem2717970) (@lem2717969)). Qed.
Lemma lem2717972 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2717973 : term304 = term308.
Proof. exact (MK_COMB (@lem2717972) (@lem2717971)). Qed.
Lemma lem2717974 : term301 = term308.
Proof. exact (TRANS (@lem2717966) (@lem2717973)). Qed.
Lemma lem2717975 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2717976 : term309 = term310.
Proof. exact (MK_COMB (@lem2717975) (@lem2717974)). Qed.
Lemma lem2717977 : term303 = term311.
Proof. exact (MK_COMB (@lem2717976) (@lem2717963)). Qed.
Lemma lem2717978 : term302 = term311.
Proof. exact (TRANS (@lem2717955) (@lem2717977)). Qed.
Lemma lem2717979 : term301 = term311.
Proof. exact (TRANS (@lem2717954) (@lem2717978)). Qed.
Lemma lem2717981 (x : real) : (term209 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2717982 : term311 = term308.
Proof. exact (@lem2717981 term308). Qed.
Lemma lem2717983 : term301 = term308.
Proof. exact (TRANS (@lem2717979) (@lem2717982)). Qed.
Lemma lem2717984 (n : int) : (term126 n) = (term126 n).
Proof. exact (eq_refl (term126 n)). Qed.
Lemma lem2717987 (n : int) : (term300 n) = (term312 n).
Proof. exact (MK_COMB (@lem2717984 n) (@lem2717983)). Qed.
Lemma lem2717988 (n : int) : (term299 n) = (term312 n).
Proof. exact (TRANS (@lem2717945 n) (@lem2717987 n)). Qed.
Lemma lem2717989 (n : int) : (term298 n) = (term312 n).
Proof. exact (TRANS (@lem2717944 n) (@lem2717988 n)). Qed.
Lemma lem2717990 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2717991 (n : int) : (term313 n) = (term314 n).
Proof. exact (MK_COMB (@lem2717990) (@lem2717989 n)). Qed.
Lemma lem2717992 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2717993 (n : int) : (term276 n) = (term315 n).
Proof. exact (MK_COMB (@lem2717991 n) (@lem2717992)). Qed.
Lemma lem2717994 (n : int) : (term161 n) = (term315 n).
Proof. exact (TRANS (@lem2717822 n) (@lem2717993 n)). Qed.
Lemma lem2717995 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2717996 (n : int) : (term150 n) = (term316 n).
Proof. exact (MK_COMB (@lem2717995) (@lem2717821 n)). Qed.
Lemma lem2717997 (n : int) : (term162 n) = (term317 n).
Proof. exact (MK_COMB (@lem2717996 n) (@lem2717994 n)). Qed.
Lemma lem2717998 (n : int) : (term130 n) = (term227 n).
Proof. exact (@lem1988287 term107 (term127 n)). Qed.
Lemma lem2718010 (n : int) : (term228 n) = (term229 n).
Proof. exact (@lem1982792 term107 (term127 n)). Qed.
Lemma lem2718011 (n : int) : (term230 n) = (term231 n).
Proof. exact (@lem1982781 (term104 n) term193 term110). Qed.
Lemma lem2718013 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2718014 : term110 = term214.
Proof. exact (@lem2718013 term111). Qed.
Lemma lem2718016 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2718017 : term193 = term194.
Proof. exact (@lem2718016 term111). Qed.
Lemma lem2718018 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2718019 : term195 = term196.
Proof. exact (MK_COMB (@lem2718018) (@lem2718017)). Qed.
Lemma lem2718020 : term215 = term216.
Proof. exact (MK_COMB (@lem2718019) (@lem2718014)). Qed.
Lemma lem2718021 : term216 = term217.
Proof. exact (@lem1981613 term193 term110 term110 term110). Qed.
Lemma lem2718023 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2718024 : term202 = term203.
Proof. exact (@lem2718023 term111 term111). Qed.
Lemma lem2718025 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2718026 : term205 = term111.
Proof. exact (EQ_MP (@lem2718025) (@lem940073)). Qed.
Lemma lem2718027 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2718028 : term203 = term110.
Proof. exact (MK_COMB (@lem2718027) (@lem2718026)). Qed.
Lemma lem2718029 : term202 = term110.
Proof. exact (TRANS (@lem2718024) (@lem2718028)). Qed.
Lemma lem2718031 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2718032 : term215 = term220.
Proof. exact (@lem2718031 term111 term111). Qed.
Lemma lem2718033 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2718034 : term205 = term111.
Proof. exact (EQ_MP (@lem2718033) (@lem940073)). Qed.
Lemma lem2718035 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2718036 : term203 = term110.
Proof. exact (MK_COMB (@lem2718035) (@lem2718034)). Qed.
Lemma lem2718037 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2718038 : term220 = term193.
Proof. exact (MK_COMB (@lem2718037) (@lem2718036)). Qed.
Lemma lem2718039 : term215 = term193.
Proof. exact (TRANS (@lem2718032) (@lem2718038)). Qed.
Lemma lem2718040 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2718041 : term221 = term222.
Proof. exact (MK_COMB (@lem2718040) (@lem2718039)). Qed.
Lemma lem2718042 : term217 = term194.
Proof. exact (MK_COMB (@lem2718041) (@lem2718029)). Qed.
Lemma lem2718043 : term216 = term194.
Proof. exact (TRANS (@lem2718021) (@lem2718042)). Qed.
Lemma lem2718044 : term215 = term194.
Proof. exact (TRANS (@lem2718020) (@lem2718043)). Qed.
Lemma lem2718046 (x : real) : (term209 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2718047 : term194 = term193.
Proof. exact (@lem2718046 term193). Qed.
Lemma lem2718048 : term215 = term193.
Proof. exact (TRANS (@lem2718044) (@lem2718047)). Qed.
Lemma lem2718051 (n : int) : (term232 n) = (term232 n).
Proof. exact (eq_refl (term232 n)). Qed.
Lemma lem2718052 (n : int) : (term231 n) = (term233 n).
Proof. exact (MK_COMB (@lem2718051 n) (@lem2718048)). Qed.
Lemma lem2718053 (n : int) : (term230 n) = (term233 n).
Proof. exact (TRANS (@lem2718011 n) (@lem2718052 n)). Qed.
Lemma lem2718054 : term139 = term139.
Proof. exact (eq_refl term139). Qed.
Lemma lem2718055 (n : int) : (term229 n) = (term234 n).
Proof. exact (MK_COMB (@lem2718054) (@lem2718053 n)). Qed.
Lemma lem2718056 (n : int) : (term234 n) = (term233 n).
Proof. exact (@lem1982721 (term233 n)). Qed.
Lemma lem2718057 (n : int) : (term229 n) = (term233 n).
Proof. exact (TRANS (@lem2718055 n) (@lem2718056 n)). Qed.
Lemma lem2718059 (n : int) : (term228 n) = (term233 n).
Proof. exact (TRANS (@lem2718010 n) (@lem2718057 n)). Qed.
Lemma lem2718060 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2718061 (n : int) : (term235 n) = (term236 n).
Proof. exact (MK_COMB (@lem2718060) (@lem2718059 n)). Qed.
Lemma lem2718062 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2718063 (n : int) : (term227 n) = (term237 n).
Proof. exact (MK_COMB (@lem2718061 n) (@lem2718062)). Qed.
Lemma lem2718064 (n : int) : (term130 n) = (term237 n).
Proof. exact (TRANS (@lem2717998 n) (@lem2718063 n)). Qed.
Lemma lem2718065 (n : int) : (term143 n) = (term238 n).
Proof. exact (@lem1988287 (term104 n) term140). Qed.
Lemma lem2718072 : term140 = term110.
Proof. exact (@lem1982721 term110). Qed.
Lemma lem2718075 (n : int) : (term239 n) = (term239 n).
Proof. exact (eq_refl (term239 n)). Qed.
Lemma lem2718076 (n : int) : (term240 n) = (term212 n).
Proof. exact (MK_COMB (@lem2718075 n) (@lem2718072)). Qed.
Lemma lem2718077 (n : int) : (term212 n) = (term213 n).
Proof. exact (@lem1982792 (term104 n) term110). Qed.
Lemma lem2718079 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2718080 : term110 = term214.
Proof. exact (@lem2718079 term111). Qed.
Lemma lem2718082 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2718083 : term193 = term194.
Proof. exact (@lem2718082 term111). Qed.
Lemma lem2718084 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2718085 : term195 = term196.
Proof. exact (MK_COMB (@lem2718084) (@lem2718083)). Qed.
Lemma lem2718086 : term215 = term216.
Proof. exact (MK_COMB (@lem2718085) (@lem2718080)). Qed.
Lemma lem2718087 : term216 = term217.
Proof. exact (@lem1981613 term193 term110 term110 term110). Qed.
Lemma lem2718089 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2718090 : term202 = term203.
Proof. exact (@lem2718089 term111 term111). Qed.
Lemma lem2718091 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2718092 : term205 = term111.
Proof. exact (EQ_MP (@lem2718091) (@lem940073)). Qed.
Lemma lem2718093 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2718094 : term203 = term110.
Proof. exact (MK_COMB (@lem2718093) (@lem2718092)). Qed.
Lemma lem2718095 : term202 = term110.
Proof. exact (TRANS (@lem2718090) (@lem2718094)). Qed.
Lemma lem2718097 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2718098 : term215 = term220.
Proof. exact (@lem2718097 term111 term111). Qed.
Lemma lem2718099 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2718100 : term205 = term111.
Proof. exact (EQ_MP (@lem2718099) (@lem940073)). Qed.
Lemma lem2718101 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2718102 : term203 = term110.
Proof. exact (MK_COMB (@lem2718101) (@lem2718100)). Qed.
Lemma lem2718103 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2718104 : term220 = term193.
Proof. exact (MK_COMB (@lem2718103) (@lem2718102)). Qed.
Lemma lem2718105 : term215 = term193.
Proof. exact (TRANS (@lem2718098) (@lem2718104)). Qed.
Lemma lem2718106 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2718107 : term221 = term222.
Proof. exact (MK_COMB (@lem2718106) (@lem2718105)). Qed.
Lemma lem2718108 : term217 = term194.
Proof. exact (MK_COMB (@lem2718107) (@lem2718095)). Qed.
Lemma lem2718109 : term216 = term194.
Proof. exact (TRANS (@lem2718087) (@lem2718108)). Qed.
Lemma lem2718110 : term215 = term194.
Proof. exact (TRANS (@lem2718086) (@lem2718109)). Qed.
Lemma lem2718112 (x : real) : (term209 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2718113 : term194 = term193.
Proof. exact (@lem2718112 term193). Qed.
Lemma lem2718114 : term215 = term193.
Proof. exact (TRANS (@lem2718110) (@lem2718113)). Qed.
Lemma lem2718115 (n : int) : (term126 n) = (term126 n).
Proof. exact (eq_refl (term126 n)). Qed.
Lemma lem2718118 (n : int) : (term213 n) = (term223 n).
Proof. exact (MK_COMB (@lem2718115 n) (@lem2718114)). Qed.
Lemma lem2718119 (n : int) : (term212 n) = (term223 n).
Proof. exact (TRANS (@lem2718077 n) (@lem2718118 n)). Qed.
Lemma lem2718120 (n : int) : (term240 n) = (term223 n).
Proof. exact (TRANS (@lem2718076 n) (@lem2718119 n)). Qed.
Lemma lem2718121 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2718122 (n : int) : (term241 n) = (term242 n).
Proof. exact (MK_COMB (@lem2718121) (@lem2718120 n)). Qed.
Lemma lem2718123 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2718124 (n : int) : (term238 n) = (term243 n).
Proof. exact (MK_COMB (@lem2718122 n) (@lem2718123)). Qed.
Lemma lem2718125 (n : int) : (term143 n) = (term243 n).
Proof. exact (TRANS (@lem2718065 n) (@lem2718124 n)). Qed.
Lemma lem2718126 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2718127 (n : int) : (term132 n) = (term244 n).
Proof. exact (MK_COMB (@lem2718126) (@lem2718064 n)). Qed.
Lemma lem2718128 (n : int) : (term144 n) = (term245 n).
Proof. exact (MK_COMB (@lem2718127 n) (@lem2718125 n)). Qed.
Lemma lem2718129 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2718130 (n : int) : (term172 n) = (term323 n).
Proof. exact (MK_COMB (@lem2718129) (@lem2717997 n)). Qed.
Lemma lem2718131 (n : int) : (term174 n) = (term324 n).
Proof. exact (MK_COMB (@lem2718130 n) (@lem2718128 n)). Qed.
Lemma lem2718132 (n : int) : ((term104 n) = term110) = ((term212 n) = term107).
Proof. exact (@lem1988293 (term104 n) term110). Qed.
Lemma lem2718138 (n : int) : (term212 n) = (term213 n).
Proof. exact (@lem1982792 (term104 n) term110). Qed.
Lemma lem2718140 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2718141 : term110 = term214.
Proof. exact (@lem2718140 term111). Qed.
Lemma lem2718143 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2718144 : term193 = term194.
Proof. exact (@lem2718143 term111). Qed.
Lemma lem2718145 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2718146 : term195 = term196.
Proof. exact (MK_COMB (@lem2718145) (@lem2718144)). Qed.
Lemma lem2718147 : term215 = term216.
Proof. exact (MK_COMB (@lem2718146) (@lem2718141)). Qed.
Lemma lem2718148 : term216 = term217.
Proof. exact (@lem1981613 term193 term110 term110 term110). Qed.
Lemma lem2718150 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2718151 : term202 = term203.
Proof. exact (@lem2718150 term111 term111). Qed.
Lemma lem2718152 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2718153 : term205 = term111.
Proof. exact (EQ_MP (@lem2718152) (@lem940073)). Qed.
Lemma lem2718154 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2718155 : term203 = term110.
Proof. exact (MK_COMB (@lem2718154) (@lem2718153)). Qed.
Lemma lem2718156 : term202 = term110.
Proof. exact (TRANS (@lem2718151) (@lem2718155)). Qed.
Lemma lem2718158 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2718159 : term215 = term220.
Proof. exact (@lem2718158 term111 term111). Qed.
Lemma lem2718160 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2718161 : term205 = term111.
Proof. exact (EQ_MP (@lem2718160) (@lem940073)). Qed.
Lemma lem2718162 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2718163 : term203 = term110.
Proof. exact (MK_COMB (@lem2718162) (@lem2718161)). Qed.
Lemma lem2718164 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2718165 : term220 = term193.
Proof. exact (MK_COMB (@lem2718164) (@lem2718163)). Qed.
Lemma lem2718166 : term215 = term193.
Proof. exact (TRANS (@lem2718159) (@lem2718165)). Qed.
Lemma lem2718167 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2718168 : term221 = term222.
Proof. exact (MK_COMB (@lem2718167) (@lem2718166)). Qed.
Lemma lem2718169 : term217 = term194.
Proof. exact (MK_COMB (@lem2718168) (@lem2718156)). Qed.
Lemma lem2718170 : term216 = term194.
Proof. exact (TRANS (@lem2718148) (@lem2718169)). Qed.
Lemma lem2718171 : term215 = term194.
Proof. exact (TRANS (@lem2718147) (@lem2718170)). Qed.
Lemma lem2718173 (x : real) : (term209 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2718174 : term194 = term193.
Proof. exact (@lem2718173 term193). Qed.
Lemma lem2718175 : term215 = term193.
Proof. exact (TRANS (@lem2718171) (@lem2718174)). Qed.
Lemma lem2718176 (n : int) : (term126 n) = (term126 n).
Proof. exact (eq_refl (term126 n)). Qed.
Lemma lem2718179 (n : int) : (term213 n) = (term223 n).
Proof. exact (MK_COMB (@lem2718176 n) (@lem2718175)). Qed.
Lemma lem2718181 (n : int) : (term212 n) = (term223 n).
Proof. exact (TRANS (@lem2718138 n) (@lem2718179 n)). Qed.
Lemma lem2718182 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2718183 (n : int) : (term224 n) = (term225 n).
Proof. exact (MK_COMB (@lem2718182) (@lem2718181 n)). Qed.
Lemma lem2718184 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2718185 (n : int) : ((term212 n) = term107) = ((term223 n) = term107).
Proof. exact (MK_COMB (@lem2718183 n) (@lem2718184)). Qed.
Lemma lem2718186 (n : int) : ((term104 n) = term110) = ((term223 n) = term107).
Proof. exact (TRANS (@lem2718132 n) (@lem2718185 n)). Qed.
Lemma lem2718187 (n : int) : ((term104 n) = term107) = ((term187 n) = term107).
Proof. exact (@lem1988293 (term104 n) term107). Qed.
Lemma lem2718193 (n : int) : (term187 n) = (term188 n).
Proof. exact (@lem1982792 (term104 n) term107). Qed.
Lemma lem2718195 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2718196 : term107 = term190.
Proof. exact (@lem2718195 (NUMERAL 0)). Qed.
Lemma lem2718198 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2718199 : term193 = term194.
Proof. exact (@lem2718198 term111). Qed.
Lemma lem2718200 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2718201 : term195 = term196.
Proof. exact (MK_COMB (@lem2718200) (@lem2718199)). Qed.
Lemma lem2718202 : term197 = term198.
Proof. exact (MK_COMB (@lem2718201) (@lem2718196)). Qed.
Lemma lem2718203 : term198 = term199.
Proof. exact (@lem1981613 term193 term107 term110 term110). Qed.
Lemma lem2718205 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2718206 : term202 = term203.
Proof. exact (@lem2718205 term111 term111). Qed.
Lemma lem2718207 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2718208 : term205 = term111.
Proof. exact (EQ_MP (@lem2718207) (@lem940073)). Qed.
Lemma lem2718209 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2718210 : term203 = term110.
Proof. exact (MK_COMB (@lem2718209) (@lem2718208)). Qed.
Lemma lem2718211 : term202 = term110.
Proof. exact (TRANS (@lem2718206) (@lem2718210)). Qed.
Lemma lem2718213 (x : nat) : (term206 x) = term107.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2718214 : term197 = term107.
Proof. exact (@lem2718213 term111). Qed.
Lemma lem2718215 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2718216 : term207 = term208.
Proof. exact (MK_COMB (@lem2718215) (@lem2718214)). Qed.
Lemma lem2718217 : term199 = term190.
Proof. exact (MK_COMB (@lem2718216) (@lem2718211)). Qed.
Lemma lem2718218 : term198 = term190.
Proof. exact (TRANS (@lem2718203) (@lem2718217)). Qed.
Lemma lem2718219 : term197 = term190.
Proof. exact (TRANS (@lem2718202) (@lem2718218)). Qed.
Lemma lem2718221 (x : real) : (term209 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2718222 : term190 = term107.
Proof. exact (@lem2718221 term107). Qed.
Lemma lem2718223 : term197 = term107.
Proof. exact (TRANS (@lem2718219) (@lem2718222)). Qed.
Lemma lem2718224 (n : int) : (term126 n) = (term126 n).
Proof. exact (eq_refl (term126 n)). Qed.
Lemma lem2718225 (n : int) : (term188 n) = (term210 n).
Proof. exact (MK_COMB (@lem2718224 n) (@lem2718223)). Qed.
Lemma lem2718226 (n : int) : (term210 n) = (term104 n).
Proof. exact (@lem1982723 (term104 n)). Qed.
Lemma lem2718227 (n : int) : (term188 n) = (term104 n).
Proof. exact (TRANS (@lem2718225 n) (@lem2718226 n)). Qed.
Lemma lem2718229 (n : int) : (term187 n) = (term104 n).
Proof. exact (TRANS (@lem2718193 n) (@lem2718227 n)). Qed.
Lemma lem2718230 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2718231 (n : int) : (term211 n) = (term108 n).
Proof. exact (MK_COMB (@lem2718230) (@lem2718229 n)). Qed.
Lemma lem2718232 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2718233 (n : int) : ((term187 n) = term107) = ((term104 n) = term107).
Proof. exact (MK_COMB (@lem2718231 n) (@lem2718232)). Qed.
Lemma lem2718234 (n : int) : ((term104 n) = term107) = ((term104 n) = term107).
Proof. exact (TRANS (@lem2718187 n) (@lem2718233 n)). Qed.
Lemma lem2718235 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2718236 (n : int) : (term175 n) = (term325 n).
Proof. exact (MK_COMB (@lem2718235) (@lem2718186 n)). Qed.
Lemma lem2718237 (n : int) : (term176 n) = (term326 n).
Proof. exact (MK_COMB (@lem2718236 n) (@lem2718234 n)). Qed.
Lemma lem2718238 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2718239 (n : int) : (term177 n) = (term327 n).
Proof. exact (MK_COMB (@lem2718238) (@lem2718131 n)). Qed.
Lemma lem2718240 (n : int) : (term178 n) = (term328 n).
Proof. exact (MK_COMB (@lem2718239 n) (@lem2718237 n)). Qed.
Lemma lem2718241 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2718242 (n : int) : (term179 n) = (term329 n).
Proof. exact (MK_COMB (@lem2718241) (@lem2717651 n)). Qed.
Lemma lem2718243 (n : int) : (term180 n) = (term330 n).
Proof. exact (MK_COMB (@lem2718242 n) (@lem2718240 n)). Qed.
Lemma lem2718244 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2718245 (n : int) : (term181 n) = (term331 n).
Proof. exact (MK_COMB (@lem2718244) (@lem2717062 n)). Qed.
Lemma lem2718246 (n : int) : (term182 n) = (term332 n).
Proof. exact (MK_COMB (@lem2718245 n) (@lem2718243 n)). Qed.
Lemma lem2718247 : term183 = term333.
Proof. exact (fun_ext (fun n : int => @lem2718246 n)). Qed.
Lemma lem2718248 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2718249 : term184 = term334.
Proof. exact (MK_COMB (@lem2718248) (@lem2718247)). Qed.
Lemma lem2718304 : term186 = term334.
Proof. exact (TRANS (@lem2716956) (@lem2718249)). Qed.
Lemma lem2718311 (n : int) : (term326 n) = (term326 n).
Proof. exact (eq_refl (term326 n)). Qed.
Lemma lem2718325 (n : int) : (term324 n) = (term335 n).
Proof. exact (@lem19158 (term237 n) (term317 n) (term243 n)). Qed.
Lemma lem2718332 (n : int) : (term336 n) = (term337 n).
Proof. exact (@lem19367 (term275 n) (term315 n) (term243 n)). Qed.
Lemma lem2718339 (n : int) : (term338 n) = (term339 n).
Proof. exact (@lem19367 (term275 n) (term315 n) (term237 n)). Qed.
Lemma lem2718340 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2718341 (n : int) : (term340 n) = (term341 n).
Proof. exact (MK_COMB (@lem2718340) (@lem2718339 n)). Qed.
Lemma lem2718342 (n : int) : (term335 n) = (term342 n).
Proof. exact (MK_COMB (@lem2718341 n) (@lem2718332 n)). Qed.
Lemma lem2718344 (n : int) : (term324 n) = (term342 n).
Proof. exact (TRANS (@lem2718325 n) (@lem2718342 n)). Qed.
Lemma lem2718345 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2718346 (n : int) : (term327 n) = (term343 n).
Proof. exact (MK_COMB (@lem2718345) (@lem2718344 n)). Qed.
Lemma lem2718347 (n : int) : (term328 n) = (term344 n).
Proof. exact (MK_COMB (@lem2718346 n) (@lem2718311 n)). Qed.
Lemma lem2718354 (n : int) : (term320 n) = (term320 n).
Proof. exact (eq_refl (term320 n)). Qed.
Lemma lem2718368 (n : int) : (term319 n) = (term345 n).
Proof. exact (@lem19158 (term275 n) (term245 n) (term315 n)). Qed.
Lemma lem2718375 (n : int) : (term346 n) = (term347 n).
Proof. exact (@lem19367 (term237 n) (term243 n) (term315 n)). Qed.
Lemma lem2718382 (n : int) : (term348 n) = (term349 n).
Proof. exact (@lem19367 (term237 n) (term243 n) (term275 n)). Qed.
Lemma lem2718383 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2718384 (n : int) : (term350 n) = (term351 n).
Proof. exact (MK_COMB (@lem2718383) (@lem2718382 n)). Qed.
Lemma lem2718385 (n : int) : (term345 n) = (term352 n).
Proof. exact (MK_COMB (@lem2718384 n) (@lem2718375 n)). Qed.
Lemma lem2718387 (n : int) : (term319 n) = (term352 n).
Proof. exact (TRANS (@lem2718368 n) (@lem2718385 n)). Qed.
Lemma lem2718388 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2718389 (n : int) : (term321 n) = (term353 n).
Proof. exact (MK_COMB (@lem2718388) (@lem2718387 n)). Qed.
Lemma lem2718390 (n : int) : (term322 n) = (term354 n).
Proof. exact (MK_COMB (@lem2718389 n) (@lem2718354 n)). Qed.
Lemma lem2718391 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2718392 (n : int) : (term329 n) = (term355 n).
Proof. exact (MK_COMB (@lem2718391) (@lem2718390 n)). Qed.
Lemma lem2718393 (n : int) : (term330 n) = (term356 n).
Proof. exact (MK_COMB (@lem2718392 n) (@lem2718347 n)). Qed.
Lemma lem2718400 (n : int) : (term331 n) = (term331 n).
Proof. exact (eq_refl (term331 n)). Qed.
Lemma lem2718401 (n : int) : (term332 n) = (term357 n).
Proof. exact (MK_COMB (@lem2718400 n) (@lem2718393 n)). Qed.
Lemma lem2718402 (n : int) : (term357 n) = (term358 n).
Proof. exact (@lem19158 (term354 n) (term226 n) (term344 n)). Qed.
Lemma lem2718403 (n : int) : (term359 n) = (term360 n).
Proof. exact (@lem19158 (term342 n) (term226 n) (term326 n)). Qed.
Lemma lem2718410 (n : int) : (term361 n) = (term362 n).
Proof. exact (@lem19367 ((term104 n) = term107) ((term223 n) = term107) (term326 n)). Qed.
Lemma lem2718411 (n : int) : (term363 n) = (term364 n).
Proof. exact (@lem19158 (term339 n) (term226 n) (term337 n)). Qed.
Lemma lem2718412 (n : int) : (term365 n) = (term366 n).
Proof. exact (@lem19158 (term367 n) (term226 n) (term368 n)). Qed.
Lemma lem2718419 (n : int) : (term369 n) = (term370 n).
Proof. exact (@lem19367 ((term104 n) = term107) ((term223 n) = term107) (term368 n)). Qed.
Lemma lem2718426 (n : int) : (term371 n) = (term372 n).
Proof. exact (@lem19367 ((term104 n) = term107) ((term223 n) = term107) (term367 n)). Qed.
Lemma lem2718427 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2718428 (n : int) : (term373 n) = (term374 n).
Proof. exact (MK_COMB (@lem2718427) (@lem2718426 n)). Qed.
Lemma lem2718429 (n : int) : (term366 n) = (term375 n).
Proof. exact (MK_COMB (@lem2718428 n) (@lem2718419 n)). Qed.
Lemma lem2718430 (n : int) : (term365 n) = (term375 n).
Proof. exact (TRANS (@lem2718412 n) (@lem2718429 n)). Qed.
Lemma lem2718431 (n : int) : (term376 n) = (term377 n).
Proof. exact (@lem19158 (term378 n) (term226 n) (term379 n)). Qed.
Lemma lem2718438 (n : int) : (term380 n) = (term381 n).
Proof. exact (@lem19367 ((term104 n) = term107) ((term223 n) = term107) (term379 n)). Qed.
Lemma lem2718445 (n : int) : (term382 n) = (term383 n).
Proof. exact (@lem19367 ((term104 n) = term107) ((term223 n) = term107) (term378 n)). Qed.
Lemma lem2718446 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2718447 (n : int) : (term384 n) = (term385 n).
Proof. exact (MK_COMB (@lem2718446) (@lem2718445 n)). Qed.
Lemma lem2718448 (n : int) : (term377 n) = (term386 n).
Proof. exact (MK_COMB (@lem2718447 n) (@lem2718438 n)). Qed.
Lemma lem2718449 (n : int) : (term376 n) = (term386 n).
Proof. exact (TRANS (@lem2718431 n) (@lem2718448 n)). Qed.
Lemma lem2718450 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2718451 (n : int) : (term387 n) = (term388 n).
Proof. exact (MK_COMB (@lem2718450) (@lem2718449 n)). Qed.
Lemma lem2718452 (n : int) : (term364 n) = (term389 n).
Proof. exact (MK_COMB (@lem2718451 n) (@lem2718430 n)). Qed.
Lemma lem2718453 (n : int) : (term363 n) = (term389 n).
Proof. exact (TRANS (@lem2718411 n) (@lem2718452 n)). Qed.
Lemma lem2718454 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2718455 (n : int) : (term390 n) = (term391 n).
Proof. exact (MK_COMB (@lem2718454) (@lem2718453 n)). Qed.
Lemma lem2718456 (n : int) : (term360 n) = (term392 n).
Proof. exact (MK_COMB (@lem2718455 n) (@lem2718410 n)). Qed.
Lemma lem2718457 (n : int) : (term359 n) = (term392 n).
Proof. exact (TRANS (@lem2718403 n) (@lem2718456 n)). Qed.
Lemma lem2718458 (n : int) : (term393 n) = (term394 n).
Proof. exact (@lem19158 (term352 n) (term226 n) (term320 n)). Qed.
Lemma lem2718465 (n : int) : (term395 n) = (term396 n).
Proof. exact (@lem19367 ((term104 n) = term107) ((term223 n) = term107) (term320 n)). Qed.
Lemma lem2718466 (n : int) : (term397 n) = (term398 n).
Proof. exact (@lem19158 (term349 n) (term226 n) (term347 n)). Qed.
Lemma lem2718467 (n : int) : (term399 n) = (term400 n).
Proof. exact (@lem19158 (term401 n) (term226 n) (term402 n)). Qed.
Lemma lem2718474 (n : int) : (term403 n) = (term404 n).
Proof. exact (@lem19367 ((term104 n) = term107) ((term223 n) = term107) (term402 n)). Qed.
Lemma lem2718481 (n : int) : (term405 n) = (term406 n).
Proof. exact (@lem19367 ((term104 n) = term107) ((term223 n) = term107) (term401 n)). Qed.
Lemma lem2718482 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2718483 (n : int) : (term407 n) = (term408 n).
Proof. exact (MK_COMB (@lem2718482) (@lem2718481 n)). Qed.
Lemma lem2718484 (n : int) : (term400 n) = (term409 n).
Proof. exact (MK_COMB (@lem2718483 n) (@lem2718474 n)). Qed.
Lemma lem2718485 (n : int) : (term399 n) = (term409 n).
Proof. exact (TRANS (@lem2718467 n) (@lem2718484 n)). Qed.
Lemma lem2718486 (n : int) : (term410 n) = (term411 n).
Proof. exact (@lem19158 (term412 n) (term226 n) (term413 n)). Qed.
Lemma lem2718493 (n : int) : (term414 n) = (term415 n).
Proof. exact (@lem19367 ((term104 n) = term107) ((term223 n) = term107) (term413 n)). Qed.
Lemma lem2718500 (n : int) : (term416 n) = (term417 n).
Proof. exact (@lem19367 ((term104 n) = term107) ((term223 n) = term107) (term412 n)). Qed.
Lemma lem2718501 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2718502 (n : int) : (term418 n) = (term419 n).
Proof. exact (MK_COMB (@lem2718501) (@lem2718500 n)). Qed.
Lemma lem2718503 (n : int) : (term411 n) = (term420 n).
Proof. exact (MK_COMB (@lem2718502 n) (@lem2718493 n)). Qed.
Lemma lem2718504 (n : int) : (term410 n) = (term420 n).
Proof. exact (TRANS (@lem2718486 n) (@lem2718503 n)). Qed.
Lemma lem2718505 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2718506 (n : int) : (term421 n) = (term422 n).
Proof. exact (MK_COMB (@lem2718505) (@lem2718504 n)). Qed.
Lemma lem2718507 (n : int) : (term398 n) = (term423 n).
Proof. exact (MK_COMB (@lem2718506 n) (@lem2718485 n)). Qed.
Lemma lem2718508 (n : int) : (term397 n) = (term423 n).
Proof. exact (TRANS (@lem2718466 n) (@lem2718507 n)). Qed.
Lemma lem2718509 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2718510 (n : int) : (term424 n) = (term425 n).
Proof. exact (MK_COMB (@lem2718509) (@lem2718508 n)). Qed.
Lemma lem2718511 (n : int) : (term394 n) = (term426 n).
Proof. exact (MK_COMB (@lem2718510 n) (@lem2718465 n)). Qed.
Lemma lem2718512 (n : int) : (term393 n) = (term426 n).
Proof. exact (TRANS (@lem2718458 n) (@lem2718511 n)). Qed.
Lemma lem2718513 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2718514 (n : int) : (term427 n) = (term428 n).
Proof. exact (MK_COMB (@lem2718513) (@lem2718512 n)). Qed.
Lemma lem2718515 (n : int) : (term358 n) = (term429 n).
Proof. exact (MK_COMB (@lem2718514 n) (@lem2718457 n)). Qed.
Lemma lem2718516 (n : int) : (term357 n) = (term429 n).
Proof. exact (TRANS (@lem2718402 n) (@lem2718515 n)). Qed.
Lemma lem2718517 (n : int) : (term332 n) = (term429 n).
Proof. exact (TRANS (@lem2718401 n) (@lem2718516 n)). Qed.
Lemma lem2718518 : term333 = term430.
Proof. exact (fun_ext (fun n : int => @lem2718517 n)). Qed.
Lemma lem2718519 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2718520 : term334 = term431.
Proof. exact (MK_COMB (@lem2718519) (@lem2718518)). Qed.
Lemma lem2718521 : term186 = term431.
Proof. exact (TRANS (@lem2718304) (@lem2718520)). Qed.
Lemma lem2718639 (n : int) (h1 : term429 n) : term429 n.
Proof. exact (h1). Qed.
Lemma lem2718640 (n : int) (h1 : term426 n) : term426 n.
Proof. exact (h1). Qed.
Lemma lem2718641 (n : int) (h1 : term423 n) : term423 n.
Proof. exact (h1). Qed.
Lemma lem2718642 (n : int) (h1 : term420 n) : term420 n.
Proof. exact (h1). Qed.
Lemma lem2718643 (n : int) (h1 : term417 n) : term417 n.
Proof. exact (h1). Qed.
Lemma lem2718644 (n : int) (h1 : term432 n) : term432 n.
Proof. exact (h1). Qed.
Lemma lem2718645 (n : int) (h1 : term432 n) : term412 n.
Proof. exact (proj2 (@lem2718644 n h1)). Qed.
Lemma lem2718646 (n : int) (h1 : term432 n) : (term104 n) = term107.
Proof. exact (proj1 (@lem2718644 n h1)). Qed.
Lemma lem2718648 (n : int) (h1 : term432 n) : term237 n.
Proof. exact (proj1 (@lem2718645 n h1)). Qed.
Lemma lem2718650 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2718651 : term433 = term257.
Proof. exact (@lem2718650 term107 term110). Qed.
Lemma lem2718653 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2718654 : term110 = term214.
Proof. exact (@lem2718653 term111). Qed.
Lemma lem2718656 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2718657 : term107 = term190.
Proof. exact (@lem2718656 (NUMERAL 0)). Qed.
Lemma lem2718658 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2718659 : term434 = term435.
Proof. exact (MK_COMB (@lem2718658) (@lem2718657)). Qed.
Lemma lem2718660 : term257 = term436.
Proof. exact (MK_COMB (@lem2718659) (@lem2718654)). Qed.
Lemma lem2718661 : term437.
Proof. exact (@lem1980255 term107 term110 term110 term110). Qed.
Lemma lem2718663 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2718664 : term257 = term258.
Proof. exact (@lem2718663 (NUMERAL 0) term111). Qed.
Lemma lem2718665 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2718666 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2718667 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2718666 h1) (fun h1 : term258 = True => @lem2718665)). Qed.
Lemma lem2718668 : term258 = True.
Proof. exact (EQ_MP (@lem2718667) (@lem2718665)). Qed.
Lemma lem2718669 : term257 = True.
Proof. exact (TRANS (@lem2718664) (@lem2718668)). Qed.
Lemma lem2718670 : True = term257.
Proof. exact (SYM (@lem2718669)). Qed.
Lemma lem2718671 : term257.
Proof. exact (EQ_MP (@lem2718670) (@lem0)). Qed.
Lemma lem2718672 : term438.
Proof. exact (@lem2718661 (@lem2718671)). Qed.
Lemma lem2718674 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2718675 : term257 = term258.
Proof. exact (@lem2718674 (NUMERAL 0) term111). Qed.
Lemma lem2718676 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2718677 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2718678 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2718677 h1) (fun h1 : term258 = True => @lem2718676)). Qed.
Lemma lem2718679 : term258 = True.
Proof. exact (EQ_MP (@lem2718678) (@lem2718676)). Qed.
Lemma lem2718680 : term257 = True.
Proof. exact (TRANS (@lem2718675) (@lem2718679)). Qed.
Lemma lem2718681 : True = term257.
Proof. exact (SYM (@lem2718680)). Qed.
Lemma lem2718682 : term257.
Proof. exact (EQ_MP (@lem2718681) (@lem0)). Qed.
Lemma lem2718683 : term436 = term439.
Proof. exact (@lem2718672 (@lem2718682)). Qed.
Lemma lem2718685 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2718686 : term202 = term203.
Proof. exact (@lem2718685 term111 term111). Qed.
Lemma lem2718687 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2718688 : term205 = term111.
Proof. exact (EQ_MP (@lem2718687) (@lem940073)). Qed.
Lemma lem2718689 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2718690 : term203 = term110.
Proof. exact (MK_COMB (@lem2718689) (@lem2718688)). Qed.
Lemma lem2718691 : term202 = term110.
Proof. exact (TRANS (@lem2718686) (@lem2718690)). Qed.
Lemma lem2718693 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2718694 : term269 = term107.
Proof. exact (@lem2718693 term111). Qed.
Lemma lem2718695 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2718696 : term440 = term434.
Proof. exact (MK_COMB (@lem2718695) (@lem2718694)). Qed.
Lemma lem2718697 : term439 = term257.
Proof. exact (MK_COMB (@lem2718696) (@lem2718691)). Qed.
Lemma lem2718699 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2718700 : term257 = term258.
Proof. exact (@lem2718699 (NUMERAL 0) term111). Qed.
Lemma lem2718701 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2718702 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2718703 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2718702 h1) (fun h1 : term258 = True => @lem2718701)). Qed.
Lemma lem2718704 : term258 = True.
Proof. exact (EQ_MP (@lem2718703) (@lem2718701)). Qed.
Lemma lem2718705 : term257 = True.
Proof. exact (TRANS (@lem2718700) (@lem2718704)). Qed.
Lemma lem2718706 : term439 = True.
Proof. exact (TRANS (@lem2718697) (@lem2718705)). Qed.
Lemma lem2718707 : term436 = True.
Proof. exact (TRANS (@lem2718683) (@lem2718706)). Qed.
Lemma lem2718708 : term257 = True.
Proof. exact (TRANS (@lem2718660) (@lem2718707)). Qed.
Lemma lem2718709 : term433 = True.
Proof. exact (TRANS (@lem2718651) (@lem2718708)). Qed.
Lemma lem2718710 : True = term433.
Proof. exact (SYM (@lem2718709)). Qed.
Lemma lem2718711 : term433.
Proof. exact (EQ_MP (@lem2718710) (@lem0)). Qed.
Lemma lem2718712 (n : int) (h1 : term432 n) : term441 n.
Proof. exact (conj (@lem2718711) (@lem2718648 n h1)). Qed.
Lemma lem2718714 (x : real) (y : real) : term442 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2718715 (n : int) : term443 n.
Proof. exact (@lem2718714 term110 (term233 n)). Qed.
Lemma lem2718716 (n : int) (h1 : term432 n) : term444 n.
Proof. exact (@lem2718715 n (@lem2718712 n h1)). Qed.
Lemma lem2718717 (n : int) : (term445 n) = (term233 n).
Proof. exact (@lem1982733 (term233 n)). Qed.
Lemma lem2718718 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2718719 (n : int) : (term446 n) = (term236 n).
Proof. exact (MK_COMB (@lem2718718) (@lem2718717 n)). Qed.
Lemma lem2718720 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2718721 (n : int) : (term444 n) = (term237 n).
Proof. exact (MK_COMB (@lem2718719 n) (@lem2718720)). Qed.
Lemma lem2718722 (n : int) (h1 : term432 n) : term237 n.
Proof. exact (EQ_MP (@lem2718721 n) (@lem2718716 n h1)). Qed.
Lemma lem2718724 (y : real) : term447 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2718725 (n : int) : term448 n.
Proof. exact (@lem2718724 (term104 n)). Qed.
Lemma lem2718726 (n : int) (h1 : term432 n) : term449 n.
Proof. exact (@lem2718725 n (@lem2718646 n h1)). Qed.
Lemma lem2718727 (n : int) (h1 : term432 n) : term450 n.
Proof. exact (@lem2718726 n h1 term110). Qed.
Lemma lem2718728 (n : int) : (term450 n) = ((term451 n) = term107).
Proof. exact (eq_refl (term450 n)). Qed.
Lemma lem2718729 (n : int) (h1 : term432 n) : (term451 n) = term107.
Proof. exact (EQ_MP (@lem2718728 n) (@lem2718727 n h1)). Qed.
Lemma lem2718730 (n : int) : (term451 n) = (term104 n).
Proof. exact (@lem1982733 (term104 n)). Qed.
Lemma lem2718731 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2718732 (n : int) : (term452 n) = (term108 n).
Proof. exact (MK_COMB (@lem2718731) (@lem2718730 n)). Qed.
Lemma lem2718733 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2718734 (n : int) : ((term451 n) = term107) = ((term104 n) = term107).
Proof. exact (MK_COMB (@lem2718732 n) (@lem2718733)). Qed.
Lemma lem2718735 (n : int) (h1 : term432 n) : (term104 n) = term107.
Proof. exact (EQ_MP (@lem2718734 n) (@lem2718729 n h1)). Qed.
Lemma lem2718736 (n : int) (h1 : term432 n) : term453 n.
Proof. exact (conj (@lem2718735 n h1) (@lem2718722 n h1)). Qed.
Lemma lem2718738 (x : real) (y : real) : term454 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2718739 (n : int) : term455 n.
Proof. exact (@lem2718738 (term104 n) (term233 n)). Qed.
Lemma lem2718740 (n : int) (h1 : term432 n) : term456 n.
Proof. exact (@lem2718739 n (@lem2718736 n h1)). Qed.
Lemma lem2718741 (n : int) : (term457 n) = (term458 n).
Proof. exact (@lem1982763 (term104 n) (term251 n) term193). Qed.
Lemma lem2718742 (n : int) : (term459 n) = (term460 n).
Proof. exact (@lem1982715 term193 (term104 n)). Qed.
Lemma lem2718744 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2718745 : term110 = term214.
Proof. exact (@lem2718744 term111). Qed.
Lemma lem2718747 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2718748 : term193 = term194.
Proof. exact (@lem2718747 term111). Qed.
Lemma lem2718749 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2718750 : term461 = term462.
Proof. exact (MK_COMB (@lem2718749) (@lem2718748)). Qed.
Lemma lem2718751 : term463 = term464.
Proof. exact (MK_COMB (@lem2718750) (@lem2718745)). Qed.
Lemma lem2718752 : term465.
Proof. exact (@lem1981473 term193 term110 term110 term110 term107 term110). Qed.
Lemma lem2718754 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2718755 : term257 = term258.
Proof. exact (@lem2718754 (NUMERAL 0) term111). Qed.
Lemma lem2718756 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2718757 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2718758 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2718757 h1) (fun h1 : term258 = True => @lem2718756)). Qed.
Lemma lem2718759 : term258 = True.
Proof. exact (EQ_MP (@lem2718758) (@lem2718756)). Qed.
Lemma lem2718760 : term257 = True.
Proof. exact (TRANS (@lem2718755) (@lem2718759)). Qed.
Lemma lem2718761 : True = term257.
Proof. exact (SYM (@lem2718760)). Qed.
Lemma lem2718762 : term257.
Proof. exact (EQ_MP (@lem2718761) (@lem0)). Qed.
Lemma lem2718763 : term466.
Proof. exact (@lem2718752 (@lem2718762)). Qed.
Lemma lem2718765 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2718766 : term257 = term258.
Proof. exact (@lem2718765 (NUMERAL 0) term111). Qed.
Lemma lem2718767 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2718768 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2718769 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2718768 h1) (fun h1 : term258 = True => @lem2718767)). Qed.
Lemma lem2718770 : term258 = True.
Proof. exact (EQ_MP (@lem2718769) (@lem2718767)). Qed.
Lemma lem2718771 : term257 = True.
Proof. exact (TRANS (@lem2718766) (@lem2718770)). Qed.
Lemma lem2718772 : True = term257.
Proof. exact (SYM (@lem2718771)). Qed.
Lemma lem2718773 : term257.
Proof. exact (EQ_MP (@lem2718772) (@lem0)). Qed.
Lemma lem2718774 : term467.
Proof. exact (@lem2718763 (@lem2718773)). Qed.
Lemma lem2718776 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2718777 : term257 = term258.
Proof. exact (@lem2718776 (NUMERAL 0) term111). Qed.
Lemma lem2718778 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2718779 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2718780 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2718779 h1) (fun h1 : term258 = True => @lem2718778)). Qed.
Lemma lem2718781 : term258 = True.
Proof. exact (EQ_MP (@lem2718780) (@lem2718778)). Qed.
Lemma lem2718782 : term257 = True.
Proof. exact (TRANS (@lem2718777) (@lem2718781)). Qed.
Lemma lem2718783 : True = term257.
Proof. exact (SYM (@lem2718782)). Qed.
Lemma lem2718784 : term257.
Proof. exact (EQ_MP (@lem2718783) (@lem0)). Qed.
Lemma lem2718785 : term468.
Proof. exact (@lem2718774 (@lem2718784)). Qed.
Lemma lem2718787 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2718788 : term202 = term203.
Proof. exact (@lem2718787 term111 term111). Qed.
Lemma lem2718789 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2718790 : term205 = term111.
Proof. exact (EQ_MP (@lem2718789) (@lem940073)). Qed.
Lemma lem2718791 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2718792 : term203 = term110.
Proof. exact (MK_COMB (@lem2718791) (@lem2718790)). Qed.
Lemma lem2718793 : term202 = term110.
Proof. exact (TRANS (@lem2718788) (@lem2718792)). Qed.
Lemma lem2718795 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2718796 : term215 = term220.
Proof. exact (@lem2718795 term111 term111). Qed.
Lemma lem2718797 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2718798 : term205 = term111.
Proof. exact (EQ_MP (@lem2718797) (@lem940073)). Qed.
Lemma lem2718799 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2718800 : term203 = term110.
Proof. exact (MK_COMB (@lem2718799) (@lem2718798)). Qed.
Lemma lem2718801 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2718802 : term220 = term193.
Proof. exact (MK_COMB (@lem2718801) (@lem2718800)). Qed.
Lemma lem2718803 : term215 = term193.
Proof. exact (TRANS (@lem2718796) (@lem2718802)). Qed.
Lemma lem2718804 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2718805 : term469 = term461.
Proof. exact (MK_COMB (@lem2718804) (@lem2718803)). Qed.
Lemma lem2718806 : term470 = term463.
Proof. exact (MK_COMB (@lem2718805) (@lem2718793)). Qed.
Lemma lem2718808 (m : nat) : (term471 m) = term107.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2718809 : term463 = term107.
Proof. exact (@lem2718808 term111). Qed.
Lemma lem2718810 : term470 = term107.
Proof. exact (TRANS (@lem2718806) (@lem2718809)). Qed.
Lemma lem2718811 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2718812 : term472 = term267.
Proof. exact (MK_COMB (@lem2718811) (@lem2718810)). Qed.
Lemma lem2718813 : term110 = term110.
Proof. exact (eq_refl term110). Qed.
Lemma lem2718814 : term473 = term269.
Proof. exact (MK_COMB (@lem2718812) (@lem2718813)). Qed.
Lemma lem2718816 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2718817 : term269 = term107.
Proof. exact (@lem2718816 term111). Qed.
Lemma lem2718818 : term473 = term107.
Proof. exact (TRANS (@lem2718814) (@lem2718817)). Qed.
Lemma lem2718820 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2718821 : term202 = term203.
Proof. exact (@lem2718820 term111 term111). Qed.
Lemma lem2718822 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2718823 : term205 = term111.
Proof. exact (EQ_MP (@lem2718822) (@lem940073)). Qed.
Lemma lem2718824 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2718825 : term203 = term110.
Proof. exact (MK_COMB (@lem2718824) (@lem2718823)). Qed.
Lemma lem2718826 : term202 = term110.
Proof. exact (TRANS (@lem2718821) (@lem2718825)). Qed.
Lemma lem2718827 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2718828 : term271 = term269.
Proof. exact (MK_COMB (@lem2718827) (@lem2718826)). Qed.
Lemma lem2718830 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2718831 : term269 = term107.
Proof. exact (@lem2718830 term111). Qed.
Lemma lem2718832 : term271 = term107.
Proof. exact (TRANS (@lem2718828) (@lem2718831)). Qed.
Lemma lem2718833 : term107 = term271.
Proof. exact (SYM (@lem2718832)). Qed.
Lemma lem2718834 : term473 = term271.
Proof. exact (TRANS (@lem2718818) (@lem2718833)). Qed.
Lemma lem2718835 : term464 = term190.
Proof. exact (@lem2718785 (@lem2718834)). Qed.
Lemma lem2718836 : term463 = term190.
Proof. exact (TRANS (@lem2718751) (@lem2718835)). Qed.
Lemma lem2718838 (x : real) : (term209 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2718839 : term190 = term107.
Proof. exact (@lem2718838 term107). Qed.
Lemma lem2718840 : term463 = term107.
Proof. exact (TRANS (@lem2718836) (@lem2718839)). Qed.
Lemma lem2718841 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2718842 : term474 = term267.
Proof. exact (MK_COMB (@lem2718841) (@lem2718840)). Qed.
Lemma lem2718843 (n : int) : (term104 n) = (term104 n).
Proof. exact (eq_refl (term104 n)). Qed.
Lemma lem2718844 (n : int) : (term460 n) = (term475 n).
Proof. exact (MK_COMB (@lem2718842) (@lem2718843 n)). Qed.
Lemma lem2718845 (n : int) : (term459 n) = (term475 n).
Proof. exact (TRANS (@lem2718742 n) (@lem2718844 n)). Qed.
Lemma lem2718846 (n : int) : (term475 n) = term107.
Proof. exact (@lem1982719 (term104 n)). Qed.
Lemma lem2718847 (n : int) : (term459 n) = term107.
Proof. exact (TRANS (@lem2718845 n) (@lem2718846 n)). Qed.
Lemma lem2718848 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2718849 (n : int) : (term476 n) = term139.
Proof. exact (MK_COMB (@lem2718848) (@lem2718847 n)). Qed.
Lemma lem2718850 : term193 = term193.
Proof. exact (eq_refl term193). Qed.
Lemma lem2718851 (n : int) : (term458 n) = term477.
Proof. exact (MK_COMB (@lem2718849 n) (@lem2718850)). Qed.
Lemma lem2718852 (n : int) : (term457 n) = term477.
Proof. exact (TRANS (@lem2718741 n) (@lem2718851 n)). Qed.
Lemma lem2718853 : term477 = term193.
Proof. exact (@lem1982721 term193). Qed.
Lemma lem2718854 (n : int) : (term457 n) = term193.
Proof. exact (TRANS (@lem2718852 n) (@lem2718853)). Qed.
Lemma lem2718855 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2718856 (n : int) : (term478 n) = term479.
Proof. exact (MK_COMB (@lem2718855) (@lem2718854 n)). Qed.
Lemma lem2718857 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2718858 (n : int) : (term456 n) = term480.
Proof. exact (MK_COMB (@lem2718856 n) (@lem2718857)). Qed.
Lemma lem2718859 (n : int) (h1 : term432 n) : term480.
Proof. exact (EQ_MP (@lem2718858 n) (@lem2718740 n h1)). Qed.
Lemma lem2718861 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2718862 : term480 = term481.
Proof. exact (@lem2718861 term107 term193). Qed.
Lemma lem2718864 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2718865 : term193 = term194.
Proof. exact (@lem2718864 term111). Qed.
Lemma lem2718867 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2718868 : term107 = term190.
Proof. exact (@lem2718867 (NUMERAL 0)). Qed.
Lemma lem2718869 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2718870 : term482 = term483.
Proof. exact (MK_COMB (@lem2718869) (@lem2718868)). Qed.
Lemma lem2718871 : term481 = term484.
Proof. exact (MK_COMB (@lem2718870) (@lem2718865)). Qed.
Lemma lem2718872 : term485.
Proof. exact (@lem1980026 term107 term110 term193 term110). Qed.
Lemma lem2718874 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2718875 : term257 = term258.
Proof. exact (@lem2718874 (NUMERAL 0) term111). Qed.
Lemma lem2718876 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2718877 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2718878 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2718877 h1) (fun h1 : term258 = True => @lem2718876)). Qed.
Lemma lem2718879 : term258 = True.
Proof. exact (EQ_MP (@lem2718878) (@lem2718876)). Qed.
Lemma lem2718880 : term257 = True.
Proof. exact (TRANS (@lem2718875) (@lem2718879)). Qed.
Lemma lem2718881 : True = term257.
Proof. exact (SYM (@lem2718880)). Qed.
Lemma lem2718882 : term257.
Proof. exact (EQ_MP (@lem2718881) (@lem0)). Qed.
Lemma lem2718883 : term486.
Proof. exact (@lem2718872 (@lem2718882)). Qed.
Lemma lem2718885 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2718886 : term257 = term258.
Proof. exact (@lem2718885 (NUMERAL 0) term111). Qed.
Lemma lem2718887 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2718888 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2718889 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2718888 h1) (fun h1 : term258 = True => @lem2718887)). Qed.
Lemma lem2718890 : term258 = True.
Proof. exact (EQ_MP (@lem2718889) (@lem2718887)). Qed.
Lemma lem2718891 : term257 = True.
Proof. exact (TRANS (@lem2718886) (@lem2718890)). Qed.
Lemma lem2718892 : True = term257.
Proof. exact (SYM (@lem2718891)). Qed.
Lemma lem2718893 : term257.
Proof. exact (EQ_MP (@lem2718892) (@lem0)). Qed.
Lemma lem2718894 : term484 = term487.
Proof. exact (@lem2718883 (@lem2718893)). Qed.
Lemma lem2718896 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2718897 : term215 = term220.
Proof. exact (@lem2718896 term111 term111). Qed.
Lemma lem2718898 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2718899 : term205 = term111.
Proof. exact (EQ_MP (@lem2718898) (@lem940073)). Qed.
Lemma lem2718900 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2718901 : term203 = term110.
Proof. exact (MK_COMB (@lem2718900) (@lem2718899)). Qed.
Lemma lem2718902 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2718903 : term220 = term193.
Proof. exact (MK_COMB (@lem2718902) (@lem2718901)). Qed.
Lemma lem2718904 : term215 = term193.
Proof. exact (TRANS (@lem2718897) (@lem2718903)). Qed.
Lemma lem2718906 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2718907 : term269 = term107.
Proof. exact (@lem2718906 term111). Qed.
Lemma lem2718908 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2718909 : term488 = term482.
Proof. exact (MK_COMB (@lem2718908) (@lem2718907)). Qed.
Lemma lem2718910 : term487 = term481.
Proof. exact (MK_COMB (@lem2718909) (@lem2718904)). Qed.
Lemma lem2718912 (m : nat) (n : nat) : (term489 m n) = (term490 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2718913 : term481 = term491.
Proof. exact (@lem2718912 (NUMERAL 0) term111). Qed.
Lemma lem2718914 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2718915 (h1 : term259 = (BIT1 0)) : (term111 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2718916 : (term259 = (BIT1 0)) = ((term111 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2718915 h1) (fun h1 : (term111 = (NUMERAL 0)) = False => @lem2718914)). Qed.
Lemma lem2718917 : (term111 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2718916) (@lem2718914)). Qed.
Lemma lem2718918 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2718919 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2718920 : term492 = (and True).
Proof. exact (MK_COMB (@lem2718919) (@lem2718918)). Qed.
Lemma lem2718921 : term491 = (True /\ False).
Proof. exact (MK_COMB (@lem2718920) (@lem2718917)). Qed.
Lemma lem2718923 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2718924 : term491 = False.
Proof. exact (TRANS (@lem2718921) (@lem2718923)). Qed.
Lemma lem2718925 : term481 = False.
Proof. exact (TRANS (@lem2718913) (@lem2718924)). Qed.
Lemma lem2718926 : term487 = False.
Proof. exact (TRANS (@lem2718910) (@lem2718925)). Qed.
Lemma lem2718927 : term484 = False.
Proof. exact (TRANS (@lem2718894) (@lem2718926)). Qed.
Lemma lem2718928 : term481 = False.
Proof. exact (TRANS (@lem2718871) (@lem2718927)). Qed.
Lemma lem2718929 : term480 = False.
Proof. exact (TRANS (@lem2718862) (@lem2718928)). Qed.
Lemma lem2718930 (n : int) (h1 : term432 n) : False.
Proof. exact (EQ_MP (@lem2718929) (@lem2718859 n h1)). Qed.
Lemma lem2718931 (n : int) (h1 : term493 n) : term493 n.
Proof. exact (h1). Qed.
Lemma lem2718932 (n : int) (h1 : term493 n) : term412 n.
Proof. exact (proj2 (@lem2718931 n h1)). Qed.
Lemma lem2718933 (n : int) (h1 : term493 n) : (term223 n) = term107.
Proof. exact (proj1 (@lem2718931 n h1)). Qed.
Lemma lem2718934 (n : int) (h1 : term493 n) : term275 n.
Proof. exact (proj2 (@lem2718932 n h1)). Qed.
Lemma lem2718937 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2718938 : term433 = term257.
Proof. exact (@lem2718937 term107 term110). Qed.
Lemma lem2718940 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2718941 : term110 = term214.
Proof. exact (@lem2718940 term111). Qed.
Lemma lem2718943 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2718944 : term107 = term190.
Proof. exact (@lem2718943 (NUMERAL 0)). Qed.
Lemma lem2718945 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2718946 : term434 = term435.
Proof. exact (MK_COMB (@lem2718945) (@lem2718944)). Qed.
Lemma lem2718947 : term257 = term436.
Proof. exact (MK_COMB (@lem2718946) (@lem2718941)). Qed.
Lemma lem2718948 : term437.
Proof. exact (@lem1980255 term107 term110 term110 term110). Qed.
Lemma lem2718950 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2718951 : term257 = term258.
Proof. exact (@lem2718950 (NUMERAL 0) term111). Qed.
Lemma lem2718952 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2718953 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2718954 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2718953 h1) (fun h1 : term258 = True => @lem2718952)). Qed.
Lemma lem2718955 : term258 = True.
Proof. exact (EQ_MP (@lem2718954) (@lem2718952)). Qed.
Lemma lem2718956 : term257 = True.
Proof. exact (TRANS (@lem2718951) (@lem2718955)). Qed.
Lemma lem2718957 : True = term257.
Proof. exact (SYM (@lem2718956)). Qed.
Lemma lem2718958 : term257.
Proof. exact (EQ_MP (@lem2718957) (@lem0)). Qed.
Lemma lem2718959 : term438.
Proof. exact (@lem2718948 (@lem2718958)). Qed.
Lemma lem2718961 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2718962 : term257 = term258.
Proof. exact (@lem2718961 (NUMERAL 0) term111). Qed.
Lemma lem2718963 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2718964 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2718965 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2718964 h1) (fun h1 : term258 = True => @lem2718963)). Qed.
Lemma lem2718966 : term258 = True.
Proof. exact (EQ_MP (@lem2718965) (@lem2718963)). Qed.
Lemma lem2718967 : term257 = True.
Proof. exact (TRANS (@lem2718962) (@lem2718966)). Qed.
Lemma lem2718968 : True = term257.
Proof. exact (SYM (@lem2718967)). Qed.
Lemma lem2718969 : term257.
Proof. exact (EQ_MP (@lem2718968) (@lem0)). Qed.
Lemma lem2718970 : term436 = term439.
Proof. exact (@lem2718959 (@lem2718969)). Qed.
Lemma lem2718972 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2718973 : term202 = term203.
Proof. exact (@lem2718972 term111 term111). Qed.
Lemma lem2718974 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2718975 : term205 = term111.
Proof. exact (EQ_MP (@lem2718974) (@lem940073)). Qed.
Lemma lem2718976 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2718977 : term203 = term110.
Proof. exact (MK_COMB (@lem2718976) (@lem2718975)). Qed.
Lemma lem2718978 : term202 = term110.
Proof. exact (TRANS (@lem2718973) (@lem2718977)). Qed.
Lemma lem2718980 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2718981 : term269 = term107.
Proof. exact (@lem2718980 term111). Qed.
Lemma lem2718982 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2718983 : term440 = term434.
Proof. exact (MK_COMB (@lem2718982) (@lem2718981)). Qed.
Lemma lem2718984 : term439 = term257.
Proof. exact (MK_COMB (@lem2718983) (@lem2718978)). Qed.
Lemma lem2718986 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2718987 : term257 = term258.
Proof. exact (@lem2718986 (NUMERAL 0) term111). Qed.
Lemma lem2718988 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2718989 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2718990 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2718989 h1) (fun h1 : term258 = True => @lem2718988)). Qed.
Lemma lem2718991 : term258 = True.
Proof. exact (EQ_MP (@lem2718990) (@lem2718988)). Qed.
Lemma lem2718992 : term257 = True.
Proof. exact (TRANS (@lem2718987) (@lem2718991)). Qed.
Lemma lem2718993 : term439 = True.
Proof. exact (TRANS (@lem2718984) (@lem2718992)). Qed.
Lemma lem2718994 : term436 = True.
Proof. exact (TRANS (@lem2718970) (@lem2718993)). Qed.
Lemma lem2718995 : term257 = True.
Proof. exact (TRANS (@lem2718947) (@lem2718994)). Qed.
Lemma lem2718996 : term433 = True.
Proof. exact (TRANS (@lem2718938) (@lem2718995)). Qed.
Lemma lem2718997 : True = term433.
Proof. exact (SYM (@lem2718996)). Qed.
Lemma lem2718998 : term433.
Proof. exact (EQ_MP (@lem2718997) (@lem0)). Qed.
Lemma lem2718999 (n : int) (h1 : term493 n) : term494 n.
Proof. exact (conj (@lem2718998) (@lem2718934 n h1)). Qed.
Lemma lem2719001 (x : real) (y : real) : term442 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2719002 (n : int) : term495 n.
Proof. exact (@lem2719001 term110 (term251 n)). Qed.
Lemma lem2719003 (n : int) (h1 : term493 n) : term496 n.
Proof. exact (@lem2719002 n (@lem2718999 n h1)). Qed.
Lemma lem2719004 (n : int) : (term497 n) = (term251 n).
Proof. exact (@lem1982733 (term251 n)). Qed.
Lemma lem2719005 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2719006 (n : int) : (term498 n) = (term274 n).
Proof. exact (MK_COMB (@lem2719005) (@lem2719004 n)). Qed.
Lemma lem2719007 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2719008 (n : int) : (term496 n) = (term275 n).
Proof. exact (MK_COMB (@lem2719006 n) (@lem2719007)). Qed.
Lemma lem2719009 (n : int) (h1 : term493 n) : term275 n.
Proof. exact (EQ_MP (@lem2719008 n) (@lem2719003 n h1)). Qed.
Lemma lem2719011 (y : real) : term447 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2719012 (n : int) : term499 n.
Proof. exact (@lem2719011 (term223 n)). Qed.
Lemma lem2719013 (n : int) (h1 : term493 n) : term500 n.
Proof. exact (@lem2719012 n (@lem2718933 n h1)). Qed.
Lemma lem2719014 (n : int) (h1 : term493 n) : term501 n.
Proof. exact (@lem2719013 n h1 term110). Qed.
Lemma lem2719015 (n : int) : (term501 n) = ((term502 n) = term107).
Proof. exact (eq_refl (term501 n)). Qed.
Lemma lem2719016 (n : int) (h1 : term493 n) : (term502 n) = term107.
Proof. exact (EQ_MP (@lem2719015 n) (@lem2719014 n h1)). Qed.
Lemma lem2719017 (n : int) : (term502 n) = (term223 n).
Proof. exact (@lem1982733 (term223 n)). Qed.
Lemma lem2719018 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2719019 (n : int) : (term503 n) = (term225 n).
Proof. exact (MK_COMB (@lem2719018) (@lem2719017 n)). Qed.
Lemma lem2719020 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2719021 (n : int) : ((term502 n) = term107) = ((term223 n) = term107).
Proof. exact (MK_COMB (@lem2719019 n) (@lem2719020)). Qed.
Lemma lem2719022 (n : int) (h1 : term493 n) : (term223 n) = term107.
Proof. exact (EQ_MP (@lem2719021 n) (@lem2719016 n h1)). Qed.
Lemma lem2719023 (n : int) (h1 : term493 n) : term504 n.
Proof. exact (conj (@lem2719022 n h1) (@lem2719009 n h1)). Qed.
Lemma lem2719025 (x : real) (y : real) : term454 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2719026 (n : int) : term505 n.
Proof. exact (@lem2719025 (term223 n) (term251 n)). Qed.
Lemma lem2719027 (n : int) (h1 : term493 n) : term506 n.
Proof. exact (@lem2719026 n (@lem2719023 n h1)). Qed.
Lemma lem2719028 (n : int) : (term507 n) = (term458 n).
Proof. exact (@lem1982759 (term104 n) (term251 n) term193). Qed.
Lemma lem2719029 (n : int) : (term459 n) = (term460 n).
Proof. exact (@lem1982715 term193 (term104 n)). Qed.
Lemma lem2719031 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2719032 : term110 = term214.
Proof. exact (@lem2719031 term111). Qed.
Lemma lem2719034 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2719035 : term193 = term194.
Proof. exact (@lem2719034 term111). Qed.
Lemma lem2719036 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2719037 : term461 = term462.
Proof. exact (MK_COMB (@lem2719036) (@lem2719035)). Qed.
Lemma lem2719038 : term463 = term464.
Proof. exact (MK_COMB (@lem2719037) (@lem2719032)). Qed.
Lemma lem2719039 : term465.
Proof. exact (@lem1981473 term193 term110 term110 term110 term107 term110). Qed.
Lemma lem2719041 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2719042 : term257 = term258.
Proof. exact (@lem2719041 (NUMERAL 0) term111). Qed.
Lemma lem2719043 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2719044 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2719045 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2719044 h1) (fun h1 : term258 = True => @lem2719043)). Qed.
Lemma lem2719046 : term258 = True.
Proof. exact (EQ_MP (@lem2719045) (@lem2719043)). Qed.
Lemma lem2719047 : term257 = True.
Proof. exact (TRANS (@lem2719042) (@lem2719046)). Qed.
Lemma lem2719048 : True = term257.
Proof. exact (SYM (@lem2719047)). Qed.
Lemma lem2719049 : term257.
Proof. exact (EQ_MP (@lem2719048) (@lem0)). Qed.
Lemma lem2719050 : term466.
Proof. exact (@lem2719039 (@lem2719049)). Qed.
Lemma lem2719052 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2719053 : term257 = term258.
Proof. exact (@lem2719052 (NUMERAL 0) term111). Qed.
Lemma lem2719054 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2719055 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2719056 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2719055 h1) (fun h1 : term258 = True => @lem2719054)). Qed.
Lemma lem2719057 : term258 = True.
Proof. exact (EQ_MP (@lem2719056) (@lem2719054)). Qed.
Lemma lem2719058 : term257 = True.
Proof. exact (TRANS (@lem2719053) (@lem2719057)). Qed.
Lemma lem2719059 : True = term257.
Proof. exact (SYM (@lem2719058)). Qed.
Lemma lem2719060 : term257.
Proof. exact (EQ_MP (@lem2719059) (@lem0)). Qed.
Lemma lem2719061 : term467.
Proof. exact (@lem2719050 (@lem2719060)). Qed.
Lemma lem2719063 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2719064 : term257 = term258.
Proof. exact (@lem2719063 (NUMERAL 0) term111). Qed.
Lemma lem2719065 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2719066 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2719067 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2719066 h1) (fun h1 : term258 = True => @lem2719065)). Qed.
Lemma lem2719068 : term258 = True.
Proof. exact (EQ_MP (@lem2719067) (@lem2719065)). Qed.
Lemma lem2719069 : term257 = True.
Proof. exact (TRANS (@lem2719064) (@lem2719068)). Qed.
Lemma lem2719070 : True = term257.
Proof. exact (SYM (@lem2719069)). Qed.
Lemma lem2719071 : term257.
Proof. exact (EQ_MP (@lem2719070) (@lem0)). Qed.
Lemma lem2719072 : term468.
Proof. exact (@lem2719061 (@lem2719071)). Qed.
Lemma lem2719074 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2719075 : term202 = term203.
Proof. exact (@lem2719074 term111 term111). Qed.
Lemma lem2719076 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2719077 : term205 = term111.
Proof. exact (EQ_MP (@lem2719076) (@lem940073)). Qed.
Lemma lem2719078 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2719079 : term203 = term110.
Proof. exact (MK_COMB (@lem2719078) (@lem2719077)). Qed.
Lemma lem2719080 : term202 = term110.
Proof. exact (TRANS (@lem2719075) (@lem2719079)). Qed.
Lemma lem2719082 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2719083 : term215 = term220.
Proof. exact (@lem2719082 term111 term111). Qed.
Lemma lem2719084 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2719085 : term205 = term111.
Proof. exact (EQ_MP (@lem2719084) (@lem940073)). Qed.
Lemma lem2719086 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2719087 : term203 = term110.
Proof. exact (MK_COMB (@lem2719086) (@lem2719085)). Qed.
Lemma lem2719088 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2719089 : term220 = term193.
Proof. exact (MK_COMB (@lem2719088) (@lem2719087)). Qed.
Lemma lem2719090 : term215 = term193.
Proof. exact (TRANS (@lem2719083) (@lem2719089)). Qed.
Lemma lem2719091 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2719092 : term469 = term461.
Proof. exact (MK_COMB (@lem2719091) (@lem2719090)). Qed.
Lemma lem2719093 : term470 = term463.
Proof. exact (MK_COMB (@lem2719092) (@lem2719080)). Qed.
Lemma lem2719095 (m : nat) : (term471 m) = term107.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2719096 : term463 = term107.
Proof. exact (@lem2719095 term111). Qed.
Lemma lem2719097 : term470 = term107.
Proof. exact (TRANS (@lem2719093) (@lem2719096)). Qed.
Lemma lem2719098 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2719099 : term472 = term267.
Proof. exact (MK_COMB (@lem2719098) (@lem2719097)). Qed.
Lemma lem2719100 : term110 = term110.
Proof. exact (eq_refl term110). Qed.
Lemma lem2719101 : term473 = term269.
Proof. exact (MK_COMB (@lem2719099) (@lem2719100)). Qed.
Lemma lem2719103 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2719104 : term269 = term107.
Proof. exact (@lem2719103 term111). Qed.
Lemma lem2719105 : term473 = term107.
Proof. exact (TRANS (@lem2719101) (@lem2719104)). Qed.
Lemma lem2719107 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2719108 : term202 = term203.
Proof. exact (@lem2719107 term111 term111). Qed.
Lemma lem2719109 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2719110 : term205 = term111.
Proof. exact (EQ_MP (@lem2719109) (@lem940073)). Qed.
Lemma lem2719111 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2719112 : term203 = term110.
Proof. exact (MK_COMB (@lem2719111) (@lem2719110)). Qed.
Lemma lem2719113 : term202 = term110.
Proof. exact (TRANS (@lem2719108) (@lem2719112)). Qed.
Lemma lem2719114 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2719115 : term271 = term269.
Proof. exact (MK_COMB (@lem2719114) (@lem2719113)). Qed.
Lemma lem2719117 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2719118 : term269 = term107.
Proof. exact (@lem2719117 term111). Qed.
Lemma lem2719119 : term271 = term107.
Proof. exact (TRANS (@lem2719115) (@lem2719118)). Qed.
Lemma lem2719120 : term107 = term271.
Proof. exact (SYM (@lem2719119)). Qed.
Lemma lem2719121 : term473 = term271.
Proof. exact (TRANS (@lem2719105) (@lem2719120)). Qed.
Lemma lem2719122 : term464 = term190.
Proof. exact (@lem2719072 (@lem2719121)). Qed.
Lemma lem2719123 : term463 = term190.
Proof. exact (TRANS (@lem2719038) (@lem2719122)). Qed.
Lemma lem2719125 (x : real) : (term209 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2719126 : term190 = term107.
Proof. exact (@lem2719125 term107). Qed.
Lemma lem2719127 : term463 = term107.
Proof. exact (TRANS (@lem2719123) (@lem2719126)). Qed.
Lemma lem2719128 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2719129 : term474 = term267.
Proof. exact (MK_COMB (@lem2719128) (@lem2719127)). Qed.
Lemma lem2719130 (n : int) : (term104 n) = (term104 n).
Proof. exact (eq_refl (term104 n)). Qed.
Lemma lem2719131 (n : int) : (term460 n) = (term475 n).
Proof. exact (MK_COMB (@lem2719129) (@lem2719130 n)). Qed.
Lemma lem2719132 (n : int) : (term459 n) = (term475 n).
Proof. exact (TRANS (@lem2719029 n) (@lem2719131 n)). Qed.
Lemma lem2719133 (n : int) : (term475 n) = term107.
Proof. exact (@lem1982719 (term104 n)). Qed.
Lemma lem2719134 (n : int) : (term459 n) = term107.
Proof. exact (TRANS (@lem2719132 n) (@lem2719133 n)). Qed.
Lemma lem2719135 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2719136 (n : int) : (term476 n) = term139.
Proof. exact (MK_COMB (@lem2719135) (@lem2719134 n)). Qed.
Lemma lem2719137 : term193 = term193.
Proof. exact (eq_refl term193). Qed.
Lemma lem2719138 (n : int) : (term458 n) = term477.
Proof. exact (MK_COMB (@lem2719136 n) (@lem2719137)). Qed.
Lemma lem2719139 (n : int) : (term507 n) = term477.
Proof. exact (TRANS (@lem2719028 n) (@lem2719138 n)). Qed.
Lemma lem2719140 : term477 = term193.
Proof. exact (@lem1982721 term193). Qed.
Lemma lem2719141 (n : int) : (term507 n) = term193.
Proof. exact (TRANS (@lem2719139 n) (@lem2719140)). Qed.
Lemma lem2719142 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2719143 (n : int) : (term508 n) = term479.
Proof. exact (MK_COMB (@lem2719142) (@lem2719141 n)). Qed.
Lemma lem2719144 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2719145 (n : int) : (term506 n) = term480.
Proof. exact (MK_COMB (@lem2719143 n) (@lem2719144)). Qed.
Lemma lem2719146 (n : int) (h1 : term493 n) : term480.
Proof. exact (EQ_MP (@lem2719145 n) (@lem2719027 n h1)). Qed.
Lemma lem2719148 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2719149 : term480 = term481.
Proof. exact (@lem2719148 term107 term193). Qed.
Lemma lem2719151 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2719152 : term193 = term194.
Proof. exact (@lem2719151 term111). Qed.
Lemma lem2719154 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2719155 : term107 = term190.
Proof. exact (@lem2719154 (NUMERAL 0)). Qed.
Lemma lem2719156 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2719157 : term482 = term483.
Proof. exact (MK_COMB (@lem2719156) (@lem2719155)). Qed.
Lemma lem2719158 : term481 = term484.
Proof. exact (MK_COMB (@lem2719157) (@lem2719152)). Qed.
Lemma lem2719159 : term485.
Proof. exact (@lem1980026 term107 term110 term193 term110). Qed.
Lemma lem2719161 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2719162 : term257 = term258.
Proof. exact (@lem2719161 (NUMERAL 0) term111). Qed.
Lemma lem2719163 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2719164 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2719165 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2719164 h1) (fun h1 : term258 = True => @lem2719163)). Qed.
Lemma lem2719166 : term258 = True.
Proof. exact (EQ_MP (@lem2719165) (@lem2719163)). Qed.
Lemma lem2719167 : term257 = True.
Proof. exact (TRANS (@lem2719162) (@lem2719166)). Qed.
Lemma lem2719168 : True = term257.
Proof. exact (SYM (@lem2719167)). Qed.
Lemma lem2719169 : term257.
Proof. exact (EQ_MP (@lem2719168) (@lem0)). Qed.
Lemma lem2719170 : term486.
Proof. exact (@lem2719159 (@lem2719169)). Qed.
Lemma lem2719172 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2719173 : term257 = term258.
Proof. exact (@lem2719172 (NUMERAL 0) term111). Qed.
Lemma lem2719174 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2719175 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2719176 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2719175 h1) (fun h1 : term258 = True => @lem2719174)). Qed.
Lemma lem2719177 : term258 = True.
Proof. exact (EQ_MP (@lem2719176) (@lem2719174)). Qed.
Lemma lem2719178 : term257 = True.
Proof. exact (TRANS (@lem2719173) (@lem2719177)). Qed.
Lemma lem2719179 : True = term257.
Proof. exact (SYM (@lem2719178)). Qed.
Lemma lem2719180 : term257.
Proof. exact (EQ_MP (@lem2719179) (@lem0)). Qed.
Lemma lem2719181 : term484 = term487.
Proof. exact (@lem2719170 (@lem2719180)). Qed.
Lemma lem2719183 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2719184 : term215 = term220.
Proof. exact (@lem2719183 term111 term111). Qed.
Lemma lem2719185 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2719186 : term205 = term111.
Proof. exact (EQ_MP (@lem2719185) (@lem940073)). Qed.
Lemma lem2719187 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2719188 : term203 = term110.
Proof. exact (MK_COMB (@lem2719187) (@lem2719186)). Qed.
Lemma lem2719189 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2719190 : term220 = term193.
Proof. exact (MK_COMB (@lem2719189) (@lem2719188)). Qed.
Lemma lem2719191 : term215 = term193.
Proof. exact (TRANS (@lem2719184) (@lem2719190)). Qed.
Lemma lem2719193 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2719194 : term269 = term107.
Proof. exact (@lem2719193 term111). Qed.
Lemma lem2719195 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2719196 : term488 = term482.
Proof. exact (MK_COMB (@lem2719195) (@lem2719194)). Qed.
Lemma lem2719197 : term487 = term481.
Proof. exact (MK_COMB (@lem2719196) (@lem2719191)). Qed.
Lemma lem2719199 (m : nat) (n : nat) : (term489 m n) = (term490 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2719200 : term481 = term491.
Proof. exact (@lem2719199 (NUMERAL 0) term111). Qed.
Lemma lem2719201 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2719202 (h1 : term259 = (BIT1 0)) : (term111 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2719203 : (term259 = (BIT1 0)) = ((term111 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2719202 h1) (fun h1 : (term111 = (NUMERAL 0)) = False => @lem2719201)). Qed.
Lemma lem2719204 : (term111 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2719203) (@lem2719201)). Qed.
Lemma lem2719205 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2719206 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2719207 : term492 = (and True).
Proof. exact (MK_COMB (@lem2719206) (@lem2719205)). Qed.
Lemma lem2719208 : term491 = (True /\ False).
Proof. exact (MK_COMB (@lem2719207) (@lem2719204)). Qed.
Lemma lem2719210 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2719211 : term491 = False.
Proof. exact (TRANS (@lem2719208) (@lem2719210)). Qed.
Lemma lem2719212 : term481 = False.
Proof. exact (TRANS (@lem2719200) (@lem2719211)). Qed.
Lemma lem2719213 : term487 = False.
Proof. exact (TRANS (@lem2719197) (@lem2719212)). Qed.
Lemma lem2719214 : term484 = False.
Proof. exact (TRANS (@lem2719181) (@lem2719213)). Qed.
Lemma lem2719215 : term481 = False.
Proof. exact (TRANS (@lem2719158) (@lem2719214)). Qed.
Lemma lem2719216 : term480 = False.
Proof. exact (TRANS (@lem2719149) (@lem2719215)). Qed.
Lemma lem2719217 (n : int) (h1 : term493 n) : False.
Proof. exact (EQ_MP (@lem2719216) (@lem2719146 n h1)). Qed.
Lemma lem2719218 (n : int) (h1 : term417 n) : False.
Proof. exact (or_elim (@lem2718643 n h1) (fun h0 : term432 n => @lem2718930 n h0) (fun h0 : term493 n => @lem2719217 n h0)). Qed.
Lemma lem2719219 (n : int) (h1 : term415 n) : term415 n.
Proof. exact (h1). Qed.
Lemma lem2719220 (n : int) (h1 : term509 n) : term509 n.
Proof. exact (h1). Qed.
Lemma lem2719221 (n : int) (h1 : term509 n) : term413 n.
Proof. exact (proj2 (@lem2719220 n h1)). Qed.
Lemma lem2719222 (n : int) (h1 : term509 n) : (term104 n) = term107.
Proof. exact (proj1 (@lem2719220 n h1)). Qed.
Lemma lem2719224 (n : int) (h1 : term509 n) : term243 n.
Proof. exact (proj1 (@lem2719221 n h1)). Qed.
Lemma lem2719226 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2719227 : term433 = term257.
Proof. exact (@lem2719226 term107 term110). Qed.
Lemma lem2719229 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2719230 : term110 = term214.
Proof. exact (@lem2719229 term111). Qed.
Lemma lem2719232 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2719233 : term107 = term190.
Proof. exact (@lem2719232 (NUMERAL 0)). Qed.
Lemma lem2719234 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2719235 : term434 = term435.
Proof. exact (MK_COMB (@lem2719234) (@lem2719233)). Qed.
Lemma lem2719236 : term257 = term436.
Proof. exact (MK_COMB (@lem2719235) (@lem2719230)). Qed.
Lemma lem2719237 : term437.
Proof. exact (@lem1980255 term107 term110 term110 term110). Qed.
Lemma lem2719239 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2719240 : term257 = term258.
Proof. exact (@lem2719239 (NUMERAL 0) term111). Qed.
Lemma lem2719241 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2719242 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2719243 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2719242 h1) (fun h1 : term258 = True => @lem2719241)). Qed.
Lemma lem2719244 : term258 = True.
Proof. exact (EQ_MP (@lem2719243) (@lem2719241)). Qed.
Lemma lem2719245 : term257 = True.
Proof. exact (TRANS (@lem2719240) (@lem2719244)). Qed.
Lemma lem2719246 : True = term257.
Proof. exact (SYM (@lem2719245)). Qed.
Lemma lem2719247 : term257.
Proof. exact (EQ_MP (@lem2719246) (@lem0)). Qed.
Lemma lem2719248 : term438.
Proof. exact (@lem2719237 (@lem2719247)). Qed.
Lemma lem2719250 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2719251 : term257 = term258.
Proof. exact (@lem2719250 (NUMERAL 0) term111). Qed.
Lemma lem2719252 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2719253 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2719254 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2719253 h1) (fun h1 : term258 = True => @lem2719252)). Qed.
Lemma lem2719255 : term258 = True.
Proof. exact (EQ_MP (@lem2719254) (@lem2719252)). Qed.
Lemma lem2719256 : term257 = True.
Proof. exact (TRANS (@lem2719251) (@lem2719255)). Qed.
Lemma lem2719257 : True = term257.
Proof. exact (SYM (@lem2719256)). Qed.
Lemma lem2719258 : term257.
Proof. exact (EQ_MP (@lem2719257) (@lem0)). Qed.
Lemma lem2719259 : term436 = term439.
Proof. exact (@lem2719248 (@lem2719258)). Qed.
Lemma lem2719261 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2719262 : term202 = term203.
Proof. exact (@lem2719261 term111 term111). Qed.
Lemma lem2719263 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2719264 : term205 = term111.
Proof. exact (EQ_MP (@lem2719263) (@lem940073)). Qed.
Lemma lem2719265 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2719266 : term203 = term110.
Proof. exact (MK_COMB (@lem2719265) (@lem2719264)). Qed.
Lemma lem2719267 : term202 = term110.
Proof. exact (TRANS (@lem2719262) (@lem2719266)). Qed.
Lemma lem2719269 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2719270 : term269 = term107.
Proof. exact (@lem2719269 term111). Qed.
Lemma lem2719271 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2719272 : term440 = term434.
Proof. exact (MK_COMB (@lem2719271) (@lem2719270)). Qed.
Lemma lem2719273 : term439 = term257.
Proof. exact (MK_COMB (@lem2719272) (@lem2719267)). Qed.
Lemma lem2719275 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2719276 : term257 = term258.
Proof. exact (@lem2719275 (NUMERAL 0) term111). Qed.
Lemma lem2719277 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2719278 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2719279 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2719278 h1) (fun h1 : term258 = True => @lem2719277)). Qed.
Lemma lem2719280 : term258 = True.
Proof. exact (EQ_MP (@lem2719279) (@lem2719277)). Qed.
Lemma lem2719281 : term257 = True.
Proof. exact (TRANS (@lem2719276) (@lem2719280)). Qed.
Lemma lem2719282 : term439 = True.
Proof. exact (TRANS (@lem2719273) (@lem2719281)). Qed.
Lemma lem2719283 : term436 = True.
Proof. exact (TRANS (@lem2719259) (@lem2719282)). Qed.
Lemma lem2719284 : term257 = True.
Proof. exact (TRANS (@lem2719236) (@lem2719283)). Qed.
Lemma lem2719285 : term433 = True.
Proof. exact (TRANS (@lem2719227) (@lem2719284)). Qed.
Lemma lem2719286 : True = term433.
Proof. exact (SYM (@lem2719285)). Qed.
Lemma lem2719287 : term433.
Proof. exact (EQ_MP (@lem2719286) (@lem0)). Qed.
Lemma lem2719288 (n : int) (h1 : term509 n) : term510 n.
Proof. exact (conj (@lem2719287) (@lem2719224 n h1)). Qed.
Lemma lem2719290 (x : real) (y : real) : term442 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2719291 (n : int) : term511 n.
Proof. exact (@lem2719290 term110 (term223 n)). Qed.
Lemma lem2719292 (n : int) (h1 : term509 n) : term512 n.
Proof. exact (@lem2719291 n (@lem2719288 n h1)). Qed.
Lemma lem2719293 (n : int) : (term502 n) = (term223 n).
Proof. exact (@lem1982733 (term223 n)). Qed.
Lemma lem2719294 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2719295 (n : int) : (term513 n) = (term242 n).
Proof. exact (MK_COMB (@lem2719294) (@lem2719293 n)). Qed.
Lemma lem2719296 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2719297 (n : int) : (term512 n) = (term243 n).
Proof. exact (MK_COMB (@lem2719295 n) (@lem2719296)). Qed.
Lemma lem2719298 (n : int) (h1 : term509 n) : term243 n.
Proof. exact (EQ_MP (@lem2719297 n) (@lem2719292 n h1)). Qed.
Lemma lem2719300 (y : real) : term447 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2719301 (n : int) : term448 n.
Proof. exact (@lem2719300 (term104 n)). Qed.
Lemma lem2719302 (n : int) (h1 : term509 n) : term449 n.
Proof. exact (@lem2719301 n (@lem2719222 n h1)). Qed.
Lemma lem2719303 (n : int) (h1 : term509 n) : term514 n.
Proof. exact (@lem2719302 n h1 term193). Qed.
Lemma lem2719304 (n : int) : (term514 n) = ((term251 n) = term107).
Proof. exact (eq_refl (term514 n)). Qed.
Lemma lem2719311 (n : int) (h1 : term509 n) : (term251 n) = term107.
Proof. exact (EQ_MP (@lem2719304 n) (@lem2719303 n h1)). Qed.
Lemma lem2719312 (n : int) (h1 : term509 n) : term515 n.
Proof. exact (conj (@lem2719311 n h1) (@lem2719298 n h1)). Qed.
Lemma lem2719314 (x : real) (y : real) : term454 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2719315 (n : int) : term516 n.
Proof. exact (@lem2719314 (term251 n) (term223 n)). Qed.
Lemma lem2719316 (n : int) (h1 : term509 n) : term517 n.
Proof. exact (@lem2719315 n (@lem2719312 n h1)). Qed.
Lemma lem2719317 (n : int) : (term518 n) = (term519 n).
Proof. exact (@lem1982763 (term251 n) (term104 n) term193). Qed.
Lemma lem2719318 (n : int) : (term520 n) = (term460 n).
Proof. exact (@lem1982713 term193 (term104 n)). Qed.
Lemma lem2719320 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2719321 : term110 = term214.
Proof. exact (@lem2719320 term111). Qed.
Lemma lem2719323 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2719324 : term193 = term194.
Proof. exact (@lem2719323 term111). Qed.
Lemma lem2719325 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2719326 : term461 = term462.
Proof. exact (MK_COMB (@lem2719325) (@lem2719324)). Qed.
Lemma lem2719327 : term463 = term464.
Proof. exact (MK_COMB (@lem2719326) (@lem2719321)). Qed.
Lemma lem2719328 : term465.
Proof. exact (@lem1981473 term193 term110 term110 term110 term107 term110). Qed.
Lemma lem2719330 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2719331 : term257 = term258.
Proof. exact (@lem2719330 (NUMERAL 0) term111). Qed.
Lemma lem2719332 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2719333 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2719334 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2719333 h1) (fun h1 : term258 = True => @lem2719332)). Qed.
Lemma lem2719335 : term258 = True.
Proof. exact (EQ_MP (@lem2719334) (@lem2719332)). Qed.
Lemma lem2719336 : term257 = True.
Proof. exact (TRANS (@lem2719331) (@lem2719335)). Qed.
Lemma lem2719337 : True = term257.
Proof. exact (SYM (@lem2719336)). Qed.
Lemma lem2719338 : term257.
Proof. exact (EQ_MP (@lem2719337) (@lem0)). Qed.
Lemma lem2719339 : term466.
Proof. exact (@lem2719328 (@lem2719338)). Qed.
Lemma lem2719341 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2719342 : term257 = term258.
Proof. exact (@lem2719341 (NUMERAL 0) term111). Qed.
Lemma lem2719343 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2719344 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2719345 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2719344 h1) (fun h1 : term258 = True => @lem2719343)). Qed.
Lemma lem2719346 : term258 = True.
Proof. exact (EQ_MP (@lem2719345) (@lem2719343)). Qed.
Lemma lem2719347 : term257 = True.
Proof. exact (TRANS (@lem2719342) (@lem2719346)). Qed.
Lemma lem2719348 : True = term257.
Proof. exact (SYM (@lem2719347)). Qed.
Lemma lem2719349 : term257.
Proof. exact (EQ_MP (@lem2719348) (@lem0)). Qed.
Lemma lem2719350 : term467.
Proof. exact (@lem2719339 (@lem2719349)). Qed.
Lemma lem2719352 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2719353 : term257 = term258.
Proof. exact (@lem2719352 (NUMERAL 0) term111). Qed.
Lemma lem2719354 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2719355 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2719356 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2719355 h1) (fun h1 : term258 = True => @lem2719354)). Qed.
Lemma lem2719357 : term258 = True.
Proof. exact (EQ_MP (@lem2719356) (@lem2719354)). Qed.
Lemma lem2719358 : term257 = True.
Proof. exact (TRANS (@lem2719353) (@lem2719357)). Qed.
Lemma lem2719359 : True = term257.
Proof. exact (SYM (@lem2719358)). Qed.
Lemma lem2719360 : term257.
Proof. exact (EQ_MP (@lem2719359) (@lem0)). Qed.
Lemma lem2719361 : term468.
Proof. exact (@lem2719350 (@lem2719360)). Qed.
Lemma lem2719363 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2719364 : term202 = term203.
Proof. exact (@lem2719363 term111 term111). Qed.
Lemma lem2719365 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2719366 : term205 = term111.
Proof. exact (EQ_MP (@lem2719365) (@lem940073)). Qed.
Lemma lem2719367 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2719368 : term203 = term110.
Proof. exact (MK_COMB (@lem2719367) (@lem2719366)). Qed.
Lemma lem2719369 : term202 = term110.
Proof. exact (TRANS (@lem2719364) (@lem2719368)). Qed.
Lemma lem2719371 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2719372 : term215 = term220.
Proof. exact (@lem2719371 term111 term111). Qed.
Lemma lem2719373 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2719374 : term205 = term111.
Proof. exact (EQ_MP (@lem2719373) (@lem940073)). Qed.
Lemma lem2719375 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2719376 : term203 = term110.
Proof. exact (MK_COMB (@lem2719375) (@lem2719374)). Qed.
Lemma lem2719377 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2719378 : term220 = term193.
Proof. exact (MK_COMB (@lem2719377) (@lem2719376)). Qed.
Lemma lem2719379 : term215 = term193.
Proof. exact (TRANS (@lem2719372) (@lem2719378)). Qed.
Lemma lem2719380 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2719381 : term469 = term461.
Proof. exact (MK_COMB (@lem2719380) (@lem2719379)). Qed.
Lemma lem2719382 : term470 = term463.
Proof. exact (MK_COMB (@lem2719381) (@lem2719369)). Qed.
Lemma lem2719384 (m : nat) : (term471 m) = term107.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2719385 : term463 = term107.
Proof. exact (@lem2719384 term111). Qed.
Lemma lem2719386 : term470 = term107.
Proof. exact (TRANS (@lem2719382) (@lem2719385)). Qed.
Lemma lem2719387 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2719388 : term472 = term267.
Proof. exact (MK_COMB (@lem2719387) (@lem2719386)). Qed.
Lemma lem2719389 : term110 = term110.
Proof. exact (eq_refl term110). Qed.
Lemma lem2719390 : term473 = term269.
Proof. exact (MK_COMB (@lem2719388) (@lem2719389)). Qed.
Lemma lem2719392 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2719393 : term269 = term107.
Proof. exact (@lem2719392 term111). Qed.
Lemma lem2719394 : term473 = term107.
Proof. exact (TRANS (@lem2719390) (@lem2719393)). Qed.
Lemma lem2719396 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2719397 : term202 = term203.
Proof. exact (@lem2719396 term111 term111). Qed.
Lemma lem2719398 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2719399 : term205 = term111.
Proof. exact (EQ_MP (@lem2719398) (@lem940073)). Qed.
Lemma lem2719400 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2719401 : term203 = term110.
Proof. exact (MK_COMB (@lem2719400) (@lem2719399)). Qed.
Lemma lem2719402 : term202 = term110.
Proof. exact (TRANS (@lem2719397) (@lem2719401)). Qed.
Lemma lem2719403 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2719404 : term271 = term269.
Proof. exact (MK_COMB (@lem2719403) (@lem2719402)). Qed.
Lemma lem2719406 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2719407 : term269 = term107.
Proof. exact (@lem2719406 term111). Qed.
Lemma lem2719408 : term271 = term107.
Proof. exact (TRANS (@lem2719404) (@lem2719407)). Qed.
Lemma lem2719409 : term107 = term271.
Proof. exact (SYM (@lem2719408)). Qed.
Lemma lem2719410 : term473 = term271.
Proof. exact (TRANS (@lem2719394) (@lem2719409)). Qed.
Lemma lem2719411 : term464 = term190.
Proof. exact (@lem2719361 (@lem2719410)). Qed.
Lemma lem2719412 : term463 = term190.
Proof. exact (TRANS (@lem2719327) (@lem2719411)). Qed.
Lemma lem2719414 (x : real) : (term209 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2719415 : term190 = term107.
Proof. exact (@lem2719414 term107). Qed.
Lemma lem2719416 : term463 = term107.
Proof. exact (TRANS (@lem2719412) (@lem2719415)). Qed.
Lemma lem2719417 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2719418 : term474 = term267.
Proof. exact (MK_COMB (@lem2719417) (@lem2719416)). Qed.
Lemma lem2719419 (n : int) : (term104 n) = (term104 n).
Proof. exact (eq_refl (term104 n)). Qed.
Lemma lem2719420 (n : int) : (term460 n) = (term475 n).
Proof. exact (MK_COMB (@lem2719418) (@lem2719419 n)). Qed.
Lemma lem2719421 (n : int) : (term520 n) = (term475 n).
Proof. exact (TRANS (@lem2719318 n) (@lem2719420 n)). Qed.
Lemma lem2719422 (n : int) : (term475 n) = term107.
Proof. exact (@lem1982719 (term104 n)). Qed.
Lemma lem2719423 (n : int) : (term520 n) = term107.
Proof. exact (TRANS (@lem2719421 n) (@lem2719422 n)). Qed.
Lemma lem2719424 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2719425 (n : int) : (term521 n) = term139.
Proof. exact (MK_COMB (@lem2719424) (@lem2719423 n)). Qed.
Lemma lem2719426 : term193 = term193.
Proof. exact (eq_refl term193). Qed.
Lemma lem2719427 (n : int) : (term519 n) = term477.
Proof. exact (MK_COMB (@lem2719425 n) (@lem2719426)). Qed.
Lemma lem2719428 (n : int) : (term518 n) = term477.
Proof. exact (TRANS (@lem2719317 n) (@lem2719427 n)). Qed.
Lemma lem2719429 : term477 = term193.
Proof. exact (@lem1982721 term193). Qed.
Lemma lem2719430 (n : int) : (term518 n) = term193.
Proof. exact (TRANS (@lem2719428 n) (@lem2719429)). Qed.
Lemma lem2719431 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2719432 (n : int) : (term522 n) = term479.
Proof. exact (MK_COMB (@lem2719431) (@lem2719430 n)). Qed.
Lemma lem2719433 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2719434 (n : int) : (term517 n) = term480.
Proof. exact (MK_COMB (@lem2719432 n) (@lem2719433)). Qed.
Lemma lem2719435 (n : int) (h1 : term509 n) : term480.
Proof. exact (EQ_MP (@lem2719434 n) (@lem2719316 n h1)). Qed.
Lemma lem2719437 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2719438 : term480 = term481.
Proof. exact (@lem2719437 term107 term193). Qed.
Lemma lem2719440 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2719441 : term193 = term194.
Proof. exact (@lem2719440 term111). Qed.
Lemma lem2719443 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2719444 : term107 = term190.
Proof. exact (@lem2719443 (NUMERAL 0)). Qed.
Lemma lem2719445 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2719446 : term482 = term483.
Proof. exact (MK_COMB (@lem2719445) (@lem2719444)). Qed.
Lemma lem2719447 : term481 = term484.
Proof. exact (MK_COMB (@lem2719446) (@lem2719441)). Qed.
Lemma lem2719448 : term485.
Proof. exact (@lem1980026 term107 term110 term193 term110). Qed.
Lemma lem2719450 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2719451 : term257 = term258.
Proof. exact (@lem2719450 (NUMERAL 0) term111). Qed.
Lemma lem2719452 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2719453 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2719454 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2719453 h1) (fun h1 : term258 = True => @lem2719452)). Qed.
Lemma lem2719455 : term258 = True.
Proof. exact (EQ_MP (@lem2719454) (@lem2719452)). Qed.
Lemma lem2719456 : term257 = True.
Proof. exact (TRANS (@lem2719451) (@lem2719455)). Qed.
Lemma lem2719457 : True = term257.
Proof. exact (SYM (@lem2719456)). Qed.
Lemma lem2719458 : term257.
Proof. exact (EQ_MP (@lem2719457) (@lem0)). Qed.
Lemma lem2719459 : term486.
Proof. exact (@lem2719448 (@lem2719458)). Qed.
Lemma lem2719461 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2719462 : term257 = term258.
Proof. exact (@lem2719461 (NUMERAL 0) term111). Qed.
Lemma lem2719463 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2719464 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2719465 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2719464 h1) (fun h1 : term258 = True => @lem2719463)). Qed.
Lemma lem2719466 : term258 = True.
Proof. exact (EQ_MP (@lem2719465) (@lem2719463)). Qed.
Lemma lem2719467 : term257 = True.
Proof. exact (TRANS (@lem2719462) (@lem2719466)). Qed.
Lemma lem2719468 : True = term257.
Proof. exact (SYM (@lem2719467)). Qed.
Lemma lem2719469 : term257.
Proof. exact (EQ_MP (@lem2719468) (@lem0)). Qed.
Lemma lem2719470 : term484 = term487.
Proof. exact (@lem2719459 (@lem2719469)). Qed.
Lemma lem2719472 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2719473 : term215 = term220.
Proof. exact (@lem2719472 term111 term111). Qed.
Lemma lem2719474 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2719475 : term205 = term111.
Proof. exact (EQ_MP (@lem2719474) (@lem940073)). Qed.
Lemma lem2719476 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2719477 : term203 = term110.
Proof. exact (MK_COMB (@lem2719476) (@lem2719475)). Qed.
Lemma lem2719478 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2719479 : term220 = term193.
Proof. exact (MK_COMB (@lem2719478) (@lem2719477)). Qed.
Lemma lem2719480 : term215 = term193.
Proof. exact (TRANS (@lem2719473) (@lem2719479)). Qed.
Lemma lem2719482 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2719483 : term269 = term107.
Proof. exact (@lem2719482 term111). Qed.
Lemma lem2719484 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2719485 : term488 = term482.
Proof. exact (MK_COMB (@lem2719484) (@lem2719483)). Qed.
Lemma lem2719486 : term487 = term481.
Proof. exact (MK_COMB (@lem2719485) (@lem2719480)). Qed.
Lemma lem2719488 (m : nat) (n : nat) : (term489 m n) = (term490 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2719489 : term481 = term491.
Proof. exact (@lem2719488 (NUMERAL 0) term111). Qed.
Lemma lem2719490 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2719491 (h1 : term259 = (BIT1 0)) : (term111 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2719492 : (term259 = (BIT1 0)) = ((term111 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2719491 h1) (fun h1 : (term111 = (NUMERAL 0)) = False => @lem2719490)). Qed.
Lemma lem2719493 : (term111 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2719492) (@lem2719490)). Qed.
Lemma lem2719494 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2719495 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2719496 : term492 = (and True).
Proof. exact (MK_COMB (@lem2719495) (@lem2719494)). Qed.
Lemma lem2719497 : term491 = (True /\ False).
Proof. exact (MK_COMB (@lem2719496) (@lem2719493)). Qed.
Lemma lem2719499 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2719500 : term491 = False.
Proof. exact (TRANS (@lem2719497) (@lem2719499)). Qed.
Lemma lem2719501 : term481 = False.
Proof. exact (TRANS (@lem2719489) (@lem2719500)). Qed.
Lemma lem2719502 : term487 = False.
Proof. exact (TRANS (@lem2719486) (@lem2719501)). Qed.
Lemma lem2719503 : term484 = False.
Proof. exact (TRANS (@lem2719470) (@lem2719502)). Qed.
Lemma lem2719504 : term481 = False.
Proof. exact (TRANS (@lem2719447) (@lem2719503)). Qed.
Lemma lem2719505 : term480 = False.
Proof. exact (TRANS (@lem2719438) (@lem2719504)). Qed.
Lemma lem2719506 (n : int) (h1 : term509 n) : False.
Proof. exact (EQ_MP (@lem2719505) (@lem2719435 n h1)). Qed.
Lemma lem2719507 (n : int) (h1 : term523 n) : term523 n.
Proof. exact (h1). Qed.
Lemma lem2719508 (n : int) (h1 : term523 n) : term413 n.
Proof. exact (proj2 (@lem2719507 n h1)). Qed.
Lemma lem2719509 (n : int) (h1 : term523 n) : (term223 n) = term107.
Proof. exact (proj1 (@lem2719507 n h1)). Qed.
Lemma lem2719510 (n : int) (h1 : term523 n) : term275 n.
Proof. exact (proj2 (@lem2719508 n h1)). Qed.
Lemma lem2719513 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2719514 : term433 = term257.
Proof. exact (@lem2719513 term107 term110). Qed.
Lemma lem2719516 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2719517 : term110 = term214.
Proof. exact (@lem2719516 term111). Qed.
Lemma lem2719519 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2719520 : term107 = term190.
Proof. exact (@lem2719519 (NUMERAL 0)). Qed.
Lemma lem2719521 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2719522 : term434 = term435.
Proof. exact (MK_COMB (@lem2719521) (@lem2719520)). Qed.
Lemma lem2719523 : term257 = term436.
Proof. exact (MK_COMB (@lem2719522) (@lem2719517)). Qed.
Lemma lem2719524 : term437.
Proof. exact (@lem1980255 term107 term110 term110 term110). Qed.
Lemma lem2719526 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2719527 : term257 = term258.
Proof. exact (@lem2719526 (NUMERAL 0) term111). Qed.
Lemma lem2719528 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2719529 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2719530 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2719529 h1) (fun h1 : term258 = True => @lem2719528)). Qed.
Lemma lem2719531 : term258 = True.
Proof. exact (EQ_MP (@lem2719530) (@lem2719528)). Qed.
Lemma lem2719532 : term257 = True.
Proof. exact (TRANS (@lem2719527) (@lem2719531)). Qed.
Lemma lem2719533 : True = term257.
Proof. exact (SYM (@lem2719532)). Qed.
Lemma lem2719534 : term257.
Proof. exact (EQ_MP (@lem2719533) (@lem0)). Qed.
Lemma lem2719535 : term438.
Proof. exact (@lem2719524 (@lem2719534)). Qed.
Lemma lem2719537 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2719538 : term257 = term258.
Proof. exact (@lem2719537 (NUMERAL 0) term111). Qed.
Lemma lem2719539 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2719540 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2719541 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2719540 h1) (fun h1 : term258 = True => @lem2719539)). Qed.
Lemma lem2719542 : term258 = True.
Proof. exact (EQ_MP (@lem2719541) (@lem2719539)). Qed.
Lemma lem2719543 : term257 = True.
Proof. exact (TRANS (@lem2719538) (@lem2719542)). Qed.
Lemma lem2719544 : True = term257.
Proof. exact (SYM (@lem2719543)). Qed.
Lemma lem2719545 : term257.
Proof. exact (EQ_MP (@lem2719544) (@lem0)). Qed.
Lemma lem2719546 : term436 = term439.
Proof. exact (@lem2719535 (@lem2719545)). Qed.
Lemma lem2719548 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2719549 : term202 = term203.
Proof. exact (@lem2719548 term111 term111). Qed.
Lemma lem2719550 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2719551 : term205 = term111.
Proof. exact (EQ_MP (@lem2719550) (@lem940073)). Qed.
Lemma lem2719552 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2719553 : term203 = term110.
Proof. exact (MK_COMB (@lem2719552) (@lem2719551)). Qed.
Lemma lem2719554 : term202 = term110.
Proof. exact (TRANS (@lem2719549) (@lem2719553)). Qed.
Lemma lem2719556 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2719557 : term269 = term107.
Proof. exact (@lem2719556 term111). Qed.
Lemma lem2719558 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2719559 : term440 = term434.
Proof. exact (MK_COMB (@lem2719558) (@lem2719557)). Qed.
Lemma lem2719560 : term439 = term257.
Proof. exact (MK_COMB (@lem2719559) (@lem2719554)). Qed.
Lemma lem2719562 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2719563 : term257 = term258.
Proof. exact (@lem2719562 (NUMERAL 0) term111). Qed.
Lemma lem2719564 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2719565 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2719566 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2719565 h1) (fun h1 : term258 = True => @lem2719564)). Qed.
Lemma lem2719567 : term258 = True.
Proof. exact (EQ_MP (@lem2719566) (@lem2719564)). Qed.
Lemma lem2719568 : term257 = True.
Proof. exact (TRANS (@lem2719563) (@lem2719567)). Qed.
Lemma lem2719569 : term439 = True.
Proof. exact (TRANS (@lem2719560) (@lem2719568)). Qed.
Lemma lem2719570 : term436 = True.
Proof. exact (TRANS (@lem2719546) (@lem2719569)). Qed.
Lemma lem2719571 : term257 = True.
Proof. exact (TRANS (@lem2719523) (@lem2719570)). Qed.
Lemma lem2719572 : term433 = True.
Proof. exact (TRANS (@lem2719514) (@lem2719571)). Qed.
Lemma lem2719573 : True = term433.
Proof. exact (SYM (@lem2719572)). Qed.
Lemma lem2719574 : term433.
Proof. exact (EQ_MP (@lem2719573) (@lem0)). Qed.
Lemma lem2719575 (n : int) (h1 : term523 n) : term494 n.
Proof. exact (conj (@lem2719574) (@lem2719510 n h1)). Qed.
Lemma lem2719577 (x : real) (y : real) : term442 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2719578 (n : int) : term495 n.
Proof. exact (@lem2719577 term110 (term251 n)). Qed.
Lemma lem2719579 (n : int) (h1 : term523 n) : term496 n.
Proof. exact (@lem2719578 n (@lem2719575 n h1)). Qed.
Lemma lem2719580 (n : int) : (term497 n) = (term251 n).
Proof. exact (@lem1982733 (term251 n)). Qed.
Lemma lem2719581 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2719582 (n : int) : (term498 n) = (term274 n).
Proof. exact (MK_COMB (@lem2719581) (@lem2719580 n)). Qed.
Lemma lem2719583 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2719584 (n : int) : (term496 n) = (term275 n).
Proof. exact (MK_COMB (@lem2719582 n) (@lem2719583)). Qed.
Lemma lem2719585 (n : int) (h1 : term523 n) : term275 n.
Proof. exact (EQ_MP (@lem2719584 n) (@lem2719579 n h1)). Qed.
Lemma lem2719587 (y : real) : term447 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2719588 (n : int) : term499 n.
Proof. exact (@lem2719587 (term223 n)). Qed.
Lemma lem2719589 (n : int) (h1 : term523 n) : term500 n.
Proof. exact (@lem2719588 n (@lem2719509 n h1)). Qed.
Lemma lem2719590 (n : int) (h1 : term523 n) : term501 n.
Proof. exact (@lem2719589 n h1 term110). Qed.
Lemma lem2719591 (n : int) : (term501 n) = ((term502 n) = term107).
Proof. exact (eq_refl (term501 n)). Qed.
Lemma lem2719592 (n : int) (h1 : term523 n) : (term502 n) = term107.
Proof. exact (EQ_MP (@lem2719591 n) (@lem2719590 n h1)). Qed.
Lemma lem2719593 (n : int) : (term502 n) = (term223 n).
Proof. exact (@lem1982733 (term223 n)). Qed.
Lemma lem2719594 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2719595 (n : int) : (term503 n) = (term225 n).
Proof. exact (MK_COMB (@lem2719594) (@lem2719593 n)). Qed.
Lemma lem2719596 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2719597 (n : int) : ((term502 n) = term107) = ((term223 n) = term107).
Proof. exact (MK_COMB (@lem2719595 n) (@lem2719596)). Qed.
Lemma lem2719598 (n : int) (h1 : term523 n) : (term223 n) = term107.
Proof. exact (EQ_MP (@lem2719597 n) (@lem2719592 n h1)). Qed.
Lemma lem2719599 (n : int) (h1 : term523 n) : term504 n.
Proof. exact (conj (@lem2719598 n h1) (@lem2719585 n h1)). Qed.
Lemma lem2719601 (x : real) (y : real) : term454 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2719602 (n : int) : term505 n.
Proof. exact (@lem2719601 (term223 n) (term251 n)). Qed.
Lemma lem2719603 (n : int) (h1 : term523 n) : term506 n.
Proof. exact (@lem2719602 n (@lem2719599 n h1)). Qed.
Lemma lem2719604 (n : int) : (term507 n) = (term458 n).
Proof. exact (@lem1982759 (term104 n) (term251 n) term193). Qed.
Lemma lem2719605 (n : int) : (term459 n) = (term460 n).
Proof. exact (@lem1982715 term193 (term104 n)). Qed.
Lemma lem2719607 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2719608 : term110 = term214.
Proof. exact (@lem2719607 term111). Qed.
Lemma lem2719610 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2719611 : term193 = term194.
Proof. exact (@lem2719610 term111). Qed.
Lemma lem2719612 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2719613 : term461 = term462.
Proof. exact (MK_COMB (@lem2719612) (@lem2719611)). Qed.
Lemma lem2719614 : term463 = term464.
Proof. exact (MK_COMB (@lem2719613) (@lem2719608)). Qed.
Lemma lem2719615 : term465.
Proof. exact (@lem1981473 term193 term110 term110 term110 term107 term110). Qed.
Lemma lem2719617 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2719618 : term257 = term258.
Proof. exact (@lem2719617 (NUMERAL 0) term111). Qed.
Lemma lem2719619 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2719620 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2719621 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2719620 h1) (fun h1 : term258 = True => @lem2719619)). Qed.
Lemma lem2719622 : term258 = True.
Proof. exact (EQ_MP (@lem2719621) (@lem2719619)). Qed.
Lemma lem2719623 : term257 = True.
Proof. exact (TRANS (@lem2719618) (@lem2719622)). Qed.
Lemma lem2719624 : True = term257.
Proof. exact (SYM (@lem2719623)). Qed.
Lemma lem2719625 : term257.
Proof. exact (EQ_MP (@lem2719624) (@lem0)). Qed.
Lemma lem2719626 : term466.
Proof. exact (@lem2719615 (@lem2719625)). Qed.
Lemma lem2719628 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2719629 : term257 = term258.
Proof. exact (@lem2719628 (NUMERAL 0) term111). Qed.
Lemma lem2719630 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2719631 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2719632 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2719631 h1) (fun h1 : term258 = True => @lem2719630)). Qed.
Lemma lem2719633 : term258 = True.
Proof. exact (EQ_MP (@lem2719632) (@lem2719630)). Qed.
Lemma lem2719634 : term257 = True.
Proof. exact (TRANS (@lem2719629) (@lem2719633)). Qed.
Lemma lem2719635 : True = term257.
Proof. exact (SYM (@lem2719634)). Qed.
Lemma lem2719636 : term257.
Proof. exact (EQ_MP (@lem2719635) (@lem0)). Qed.
Lemma lem2719637 : term467.
Proof. exact (@lem2719626 (@lem2719636)). Qed.
Lemma lem2719639 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2719640 : term257 = term258.
Proof. exact (@lem2719639 (NUMERAL 0) term111). Qed.
Lemma lem2719641 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2719642 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2719643 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2719642 h1) (fun h1 : term258 = True => @lem2719641)). Qed.
Lemma lem2719644 : term258 = True.
Proof. exact (EQ_MP (@lem2719643) (@lem2719641)). Qed.
Lemma lem2719645 : term257 = True.
Proof. exact (TRANS (@lem2719640) (@lem2719644)). Qed.
Lemma lem2719646 : True = term257.
Proof. exact (SYM (@lem2719645)). Qed.
Lemma lem2719647 : term257.
Proof. exact (EQ_MP (@lem2719646) (@lem0)). Qed.
Lemma lem2719648 : term468.
Proof. exact (@lem2719637 (@lem2719647)). Qed.
Lemma lem2719650 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2719651 : term202 = term203.
Proof. exact (@lem2719650 term111 term111). Qed.
Lemma lem2719652 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2719653 : term205 = term111.
Proof. exact (EQ_MP (@lem2719652) (@lem940073)). Qed.
Lemma lem2719654 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2719655 : term203 = term110.
Proof. exact (MK_COMB (@lem2719654) (@lem2719653)). Qed.
Lemma lem2719656 : term202 = term110.
Proof. exact (TRANS (@lem2719651) (@lem2719655)). Qed.
Lemma lem2719658 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2719659 : term215 = term220.
Proof. exact (@lem2719658 term111 term111). Qed.
Lemma lem2719660 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2719661 : term205 = term111.
Proof. exact (EQ_MP (@lem2719660) (@lem940073)). Qed.
Lemma lem2719662 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2719663 : term203 = term110.
Proof. exact (MK_COMB (@lem2719662) (@lem2719661)). Qed.
Lemma lem2719664 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2719665 : term220 = term193.
Proof. exact (MK_COMB (@lem2719664) (@lem2719663)). Qed.
Lemma lem2719666 : term215 = term193.
Proof. exact (TRANS (@lem2719659) (@lem2719665)). Qed.
Lemma lem2719667 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2719668 : term469 = term461.
Proof. exact (MK_COMB (@lem2719667) (@lem2719666)). Qed.
Lemma lem2719669 : term470 = term463.
Proof. exact (MK_COMB (@lem2719668) (@lem2719656)). Qed.
Lemma lem2719671 (m : nat) : (term471 m) = term107.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2719672 : term463 = term107.
Proof. exact (@lem2719671 term111). Qed.
Lemma lem2719673 : term470 = term107.
Proof. exact (TRANS (@lem2719669) (@lem2719672)). Qed.
Lemma lem2719674 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2719675 : term472 = term267.
Proof. exact (MK_COMB (@lem2719674) (@lem2719673)). Qed.
Lemma lem2719676 : term110 = term110.
Proof. exact (eq_refl term110). Qed.
Lemma lem2719677 : term473 = term269.
Proof. exact (MK_COMB (@lem2719675) (@lem2719676)). Qed.
Lemma lem2719679 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2719680 : term269 = term107.
Proof. exact (@lem2719679 term111). Qed.
Lemma lem2719681 : term473 = term107.
Proof. exact (TRANS (@lem2719677) (@lem2719680)). Qed.
Lemma lem2719683 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2719684 : term202 = term203.
Proof. exact (@lem2719683 term111 term111). Qed.
Lemma lem2719685 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2719686 : term205 = term111.
Proof. exact (EQ_MP (@lem2719685) (@lem940073)). Qed.
Lemma lem2719687 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2719688 : term203 = term110.
Proof. exact (MK_COMB (@lem2719687) (@lem2719686)). Qed.
Lemma lem2719689 : term202 = term110.
Proof. exact (TRANS (@lem2719684) (@lem2719688)). Qed.
Lemma lem2719690 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2719691 : term271 = term269.
Proof. exact (MK_COMB (@lem2719690) (@lem2719689)). Qed.
Lemma lem2719693 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2719694 : term269 = term107.
Proof. exact (@lem2719693 term111). Qed.
Lemma lem2719695 : term271 = term107.
Proof. exact (TRANS (@lem2719691) (@lem2719694)). Qed.
Lemma lem2719696 : term107 = term271.
Proof. exact (SYM (@lem2719695)). Qed.
Lemma lem2719697 : term473 = term271.
Proof. exact (TRANS (@lem2719681) (@lem2719696)). Qed.
Lemma lem2719698 : term464 = term190.
Proof. exact (@lem2719648 (@lem2719697)). Qed.
Lemma lem2719699 : term463 = term190.
Proof. exact (TRANS (@lem2719614) (@lem2719698)). Qed.
Lemma lem2719701 (x : real) : (term209 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2719702 : term190 = term107.
Proof. exact (@lem2719701 term107). Qed.
Lemma lem2719703 : term463 = term107.
Proof. exact (TRANS (@lem2719699) (@lem2719702)). Qed.
Lemma lem2719704 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2719705 : term474 = term267.
Proof. exact (MK_COMB (@lem2719704) (@lem2719703)). Qed.
Lemma lem2719706 (n : int) : (term104 n) = (term104 n).
Proof. exact (eq_refl (term104 n)). Qed.
Lemma lem2719707 (n : int) : (term460 n) = (term475 n).
Proof. exact (MK_COMB (@lem2719705) (@lem2719706 n)). Qed.
Lemma lem2719708 (n : int) : (term459 n) = (term475 n).
Proof. exact (TRANS (@lem2719605 n) (@lem2719707 n)). Qed.
Lemma lem2719709 (n : int) : (term475 n) = term107.
Proof. exact (@lem1982719 (term104 n)). Qed.
Lemma lem2719710 (n : int) : (term459 n) = term107.
Proof. exact (TRANS (@lem2719708 n) (@lem2719709 n)). Qed.
Lemma lem2719711 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2719712 (n : int) : (term476 n) = term139.
Proof. exact (MK_COMB (@lem2719711) (@lem2719710 n)). Qed.
Lemma lem2719713 : term193 = term193.
Proof. exact (eq_refl term193). Qed.
Lemma lem2719714 (n : int) : (term458 n) = term477.
Proof. exact (MK_COMB (@lem2719712 n) (@lem2719713)). Qed.
Lemma lem2719715 (n : int) : (term507 n) = term477.
Proof. exact (TRANS (@lem2719604 n) (@lem2719714 n)). Qed.
Lemma lem2719716 : term477 = term193.
Proof. exact (@lem1982721 term193). Qed.
Lemma lem2719717 (n : int) : (term507 n) = term193.
Proof. exact (TRANS (@lem2719715 n) (@lem2719716)). Qed.
Lemma lem2719718 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2719719 (n : int) : (term508 n) = term479.
Proof. exact (MK_COMB (@lem2719718) (@lem2719717 n)). Qed.
Lemma lem2719720 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2719721 (n : int) : (term506 n) = term480.
Proof. exact (MK_COMB (@lem2719719 n) (@lem2719720)). Qed.
Lemma lem2719722 (n : int) (h1 : term523 n) : term480.
Proof. exact (EQ_MP (@lem2719721 n) (@lem2719603 n h1)). Qed.
Lemma lem2719724 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2719725 : term480 = term481.
Proof. exact (@lem2719724 term107 term193). Qed.
Lemma lem2719727 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2719728 : term193 = term194.
Proof. exact (@lem2719727 term111). Qed.
Lemma lem2719730 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2719731 : term107 = term190.
Proof. exact (@lem2719730 (NUMERAL 0)). Qed.
Lemma lem2719732 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2719733 : term482 = term483.
Proof. exact (MK_COMB (@lem2719732) (@lem2719731)). Qed.
Lemma lem2719734 : term481 = term484.
Proof. exact (MK_COMB (@lem2719733) (@lem2719728)). Qed.
Lemma lem2719735 : term485.
Proof. exact (@lem1980026 term107 term110 term193 term110). Qed.
Lemma lem2719737 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2719738 : term257 = term258.
Proof. exact (@lem2719737 (NUMERAL 0) term111). Qed.
Lemma lem2719739 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2719740 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2719741 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2719740 h1) (fun h1 : term258 = True => @lem2719739)). Qed.
Lemma lem2719742 : term258 = True.
Proof. exact (EQ_MP (@lem2719741) (@lem2719739)). Qed.
Lemma lem2719743 : term257 = True.
Proof. exact (TRANS (@lem2719738) (@lem2719742)). Qed.
Lemma lem2719744 : True = term257.
Proof. exact (SYM (@lem2719743)). Qed.
Lemma lem2719745 : term257.
Proof. exact (EQ_MP (@lem2719744) (@lem0)). Qed.
Lemma lem2719746 : term486.
Proof. exact (@lem2719735 (@lem2719745)). Qed.
Lemma lem2719748 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2719749 : term257 = term258.
Proof. exact (@lem2719748 (NUMERAL 0) term111). Qed.
Lemma lem2719750 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2719751 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2719752 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2719751 h1) (fun h1 : term258 = True => @lem2719750)). Qed.
Lemma lem2719753 : term258 = True.
Proof. exact (EQ_MP (@lem2719752) (@lem2719750)). Qed.
Lemma lem2719754 : term257 = True.
Proof. exact (TRANS (@lem2719749) (@lem2719753)). Qed.
Lemma lem2719755 : True = term257.
Proof. exact (SYM (@lem2719754)). Qed.
Lemma lem2719756 : term257.
Proof. exact (EQ_MP (@lem2719755) (@lem0)). Qed.
Lemma lem2719757 : term484 = term487.
Proof. exact (@lem2719746 (@lem2719756)). Qed.
Lemma lem2719759 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2719760 : term215 = term220.
Proof. exact (@lem2719759 term111 term111). Qed.
Lemma lem2719761 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2719762 : term205 = term111.
Proof. exact (EQ_MP (@lem2719761) (@lem940073)). Qed.
Lemma lem2719763 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2719764 : term203 = term110.
Proof. exact (MK_COMB (@lem2719763) (@lem2719762)). Qed.
Lemma lem2719765 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2719766 : term220 = term193.
Proof. exact (MK_COMB (@lem2719765) (@lem2719764)). Qed.
Lemma lem2719767 : term215 = term193.
Proof. exact (TRANS (@lem2719760) (@lem2719766)). Qed.
Lemma lem2719769 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2719770 : term269 = term107.
Proof. exact (@lem2719769 term111). Qed.
Lemma lem2719771 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2719772 : term488 = term482.
Proof. exact (MK_COMB (@lem2719771) (@lem2719770)). Qed.
Lemma lem2719773 : term487 = term481.
Proof. exact (MK_COMB (@lem2719772) (@lem2719767)). Qed.
Lemma lem2719775 (m : nat) (n : nat) : (term489 m n) = (term490 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2719776 : term481 = term491.
Proof. exact (@lem2719775 (NUMERAL 0) term111). Qed.
Lemma lem2719777 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2719778 (h1 : term259 = (BIT1 0)) : (term111 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2719779 : (term259 = (BIT1 0)) = ((term111 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2719778 h1) (fun h1 : (term111 = (NUMERAL 0)) = False => @lem2719777)). Qed.
Lemma lem2719780 : (term111 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2719779) (@lem2719777)). Qed.
Lemma lem2719781 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2719782 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2719783 : term492 = (and True).
Proof. exact (MK_COMB (@lem2719782) (@lem2719781)). Qed.
Lemma lem2719784 : term491 = (True /\ False).
Proof. exact (MK_COMB (@lem2719783) (@lem2719780)). Qed.
Lemma lem2719786 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2719787 : term491 = False.
Proof. exact (TRANS (@lem2719784) (@lem2719786)). Qed.
Lemma lem2719788 : term481 = False.
Proof. exact (TRANS (@lem2719776) (@lem2719787)). Qed.
Lemma lem2719789 : term487 = False.
Proof. exact (TRANS (@lem2719773) (@lem2719788)). Qed.
Lemma lem2719790 : term484 = False.
Proof. exact (TRANS (@lem2719757) (@lem2719789)). Qed.
Lemma lem2719791 : term481 = False.
Proof. exact (TRANS (@lem2719734) (@lem2719790)). Qed.
Lemma lem2719792 : term480 = False.
Proof. exact (TRANS (@lem2719725) (@lem2719791)). Qed.
Lemma lem2719793 (n : int) (h1 : term523 n) : False.
Proof. exact (EQ_MP (@lem2719792) (@lem2719722 n h1)). Qed.
Lemma lem2719794 (n : int) (h1 : term415 n) : False.
Proof. exact (or_elim (@lem2719219 n h1) (fun h0 : term509 n => @lem2719506 n h0) (fun h0 : term523 n => @lem2719793 n h0)). Qed.
Lemma lem2719795 (n : int) (h1 : term420 n) : False.
Proof. exact (or_elim (@lem2718642 n h1) (fun h0 : term417 n => @lem2719218 n h0) (fun h0 : term415 n => @lem2719794 n h0)). Qed.
Lemma lem2719796 (n : int) (h1 : term409 n) : term409 n.
Proof. exact (h1). Qed.
Lemma lem2719797 (n : int) (h1 : term406 n) : term406 n.
Proof. exact (h1). Qed.
Lemma lem2719798 (n : int) (h1 : term524 n) : term524 n.
Proof. exact (h1). Qed.
Lemma lem2719799 (n : int) (h1 : term524 n) : term401 n.
Proof. exact (proj2 (@lem2719798 n h1)). Qed.
Lemma lem2719800 (n : int) (h1 : term524 n) : (term104 n) = term107.
Proof. exact (proj1 (@lem2719798 n h1)). Qed.
Lemma lem2719801 (n : int) (h1 : term524 n) : term315 n.
Proof. exact (proj2 (@lem2719799 n h1)). Qed.
Lemma lem2719804 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2719805 : term433 = term257.
Proof. exact (@lem2719804 term107 term110). Qed.
Lemma lem2719807 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2719808 : term110 = term214.
Proof. exact (@lem2719807 term111). Qed.
Lemma lem2719810 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2719811 : term107 = term190.
Proof. exact (@lem2719810 (NUMERAL 0)). Qed.
Lemma lem2719812 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2719813 : term434 = term435.
Proof. exact (MK_COMB (@lem2719812) (@lem2719811)). Qed.
Lemma lem2719814 : term257 = term436.
Proof. exact (MK_COMB (@lem2719813) (@lem2719808)). Qed.
Lemma lem2719815 : term437.
Proof. exact (@lem1980255 term107 term110 term110 term110). Qed.
Lemma lem2719817 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2719818 : term257 = term258.
Proof. exact (@lem2719817 (NUMERAL 0) term111). Qed.
Lemma lem2719819 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2719820 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2719821 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2719820 h1) (fun h1 : term258 = True => @lem2719819)). Qed.
Lemma lem2719822 : term258 = True.
Proof. exact (EQ_MP (@lem2719821) (@lem2719819)). Qed.
Lemma lem2719823 : term257 = True.
Proof. exact (TRANS (@lem2719818) (@lem2719822)). Qed.
Lemma lem2719824 : True = term257.
Proof. exact (SYM (@lem2719823)). Qed.
Lemma lem2719825 : term257.
Proof. exact (EQ_MP (@lem2719824) (@lem0)). Qed.
Lemma lem2719826 : term438.
Proof. exact (@lem2719815 (@lem2719825)). Qed.
Lemma lem2719828 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2719829 : term257 = term258.
Proof. exact (@lem2719828 (NUMERAL 0) term111). Qed.
Lemma lem2719830 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2719831 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2719832 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2719831 h1) (fun h1 : term258 = True => @lem2719830)). Qed.
Lemma lem2719833 : term258 = True.
Proof. exact (EQ_MP (@lem2719832) (@lem2719830)). Qed.
Lemma lem2719834 : term257 = True.
Proof. exact (TRANS (@lem2719829) (@lem2719833)). Qed.
Lemma lem2719835 : True = term257.
Proof. exact (SYM (@lem2719834)). Qed.
Lemma lem2719836 : term257.
Proof. exact (EQ_MP (@lem2719835) (@lem0)). Qed.
Lemma lem2719837 : term436 = term439.
Proof. exact (@lem2719826 (@lem2719836)). Qed.
Lemma lem2719839 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2719840 : term202 = term203.
Proof. exact (@lem2719839 term111 term111). Qed.
Lemma lem2719841 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2719842 : term205 = term111.
Proof. exact (EQ_MP (@lem2719841) (@lem940073)). Qed.
Lemma lem2719843 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2719844 : term203 = term110.
Proof. exact (MK_COMB (@lem2719843) (@lem2719842)). Qed.
Lemma lem2719845 : term202 = term110.
Proof. exact (TRANS (@lem2719840) (@lem2719844)). Qed.
Lemma lem2719847 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2719848 : term269 = term107.
Proof. exact (@lem2719847 term111). Qed.
Lemma lem2719849 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2719850 : term440 = term434.
Proof. exact (MK_COMB (@lem2719849) (@lem2719848)). Qed.
Lemma lem2719851 : term439 = term257.
Proof. exact (MK_COMB (@lem2719850) (@lem2719845)). Qed.
Lemma lem2719853 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2719854 : term257 = term258.
Proof. exact (@lem2719853 (NUMERAL 0) term111). Qed.
Lemma lem2719855 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2719856 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2719857 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2719856 h1) (fun h1 : term258 = True => @lem2719855)). Qed.
Lemma lem2719858 : term258 = True.
Proof. exact (EQ_MP (@lem2719857) (@lem2719855)). Qed.
Lemma lem2719859 : term257 = True.
Proof. exact (TRANS (@lem2719854) (@lem2719858)). Qed.
Lemma lem2719860 : term439 = True.
Proof. exact (TRANS (@lem2719851) (@lem2719859)). Qed.
Lemma lem2719861 : term436 = True.
Proof. exact (TRANS (@lem2719837) (@lem2719860)). Qed.
Lemma lem2719862 : term257 = True.
Proof. exact (TRANS (@lem2719814) (@lem2719861)). Qed.
Lemma lem2719863 : term433 = True.
Proof. exact (TRANS (@lem2719805) (@lem2719862)). Qed.
Lemma lem2719864 : True = term433.
Proof. exact (SYM (@lem2719863)). Qed.
Lemma lem2719865 : term433.
Proof. exact (EQ_MP (@lem2719864) (@lem0)). Qed.
Lemma lem2719866 (n : int) (h1 : term524 n) : term525 n.
Proof. exact (conj (@lem2719865) (@lem2719801 n h1)). Qed.
Lemma lem2719868 (x : real) (y : real) : term442 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2719869 (n : int) : term526 n.
Proof. exact (@lem2719868 term110 (term312 n)). Qed.
Lemma lem2719870 (n : int) (h1 : term524 n) : term527 n.
Proof. exact (@lem2719869 n (@lem2719866 n h1)). Qed.
Lemma lem2719871 (n : int) : (term528 n) = (term312 n).
Proof. exact (@lem1982733 (term312 n)). Qed.
Lemma lem2719872 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2719873 (n : int) : (term529 n) = (term314 n).
Proof. exact (MK_COMB (@lem2719872) (@lem2719871 n)). Qed.
Lemma lem2719874 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2719875 (n : int) : (term527 n) = (term315 n).
Proof. exact (MK_COMB (@lem2719873 n) (@lem2719874)). Qed.
Lemma lem2719876 (n : int) (h1 : term524 n) : term315 n.
Proof. exact (EQ_MP (@lem2719875 n) (@lem2719870 n h1)). Qed.
Lemma lem2719878 (y : real) : term447 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2719879 (n : int) : term448 n.
Proof. exact (@lem2719878 (term104 n)). Qed.
Lemma lem2719880 (n : int) (h1 : term524 n) : term449 n.
Proof. exact (@lem2719879 n (@lem2719800 n h1)). Qed.
Lemma lem2719881 (n : int) (h1 : term524 n) : term514 n.
Proof. exact (@lem2719880 n h1 term193). Qed.
Lemma lem2719882 (n : int) : (term514 n) = ((term251 n) = term107).
Proof. exact (eq_refl (term514 n)). Qed.
Lemma lem2719889 (n : int) (h1 : term524 n) : (term251 n) = term107.
Proof. exact (EQ_MP (@lem2719882 n) (@lem2719881 n h1)). Qed.
Lemma lem2719890 (n : int) (h1 : term524 n) : term530 n.
Proof. exact (conj (@lem2719889 n h1) (@lem2719876 n h1)). Qed.
Lemma lem2719892 (x : real) (y : real) : term454 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2719893 (n : int) : term531 n.
Proof. exact (@lem2719892 (term251 n) (term312 n)). Qed.
Lemma lem2719894 (n : int) (h1 : term524 n) : term532 n.
Proof. exact (@lem2719893 n (@lem2719890 n h1)). Qed.
Lemma lem2719895 (n : int) : (term533 n) = (term534 n).
Proof. exact (@lem1982763 (term251 n) (term104 n) term308). Qed.
Lemma lem2719896 (n : int) : (term520 n) = (term460 n).
Proof. exact (@lem1982713 term193 (term104 n)). Qed.
Lemma lem2719898 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2719899 : term110 = term214.
Proof. exact (@lem2719898 term111). Qed.
Lemma lem2719901 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2719902 : term193 = term194.
Proof. exact (@lem2719901 term111). Qed.
Lemma lem2719903 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2719904 : term461 = term462.
Proof. exact (MK_COMB (@lem2719903) (@lem2719902)). Qed.
Lemma lem2719905 : term463 = term464.
Proof. exact (MK_COMB (@lem2719904) (@lem2719899)). Qed.
Lemma lem2719906 : term465.
Proof. exact (@lem1981473 term193 term110 term110 term110 term107 term110). Qed.
Lemma lem2719908 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2719909 : term257 = term258.
Proof. exact (@lem2719908 (NUMERAL 0) term111). Qed.
Lemma lem2719910 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2719911 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2719912 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2719911 h1) (fun h1 : term258 = True => @lem2719910)). Qed.
Lemma lem2719913 : term258 = True.
Proof. exact (EQ_MP (@lem2719912) (@lem2719910)). Qed.
Lemma lem2719914 : term257 = True.
Proof. exact (TRANS (@lem2719909) (@lem2719913)). Qed.
Lemma lem2719915 : True = term257.
Proof. exact (SYM (@lem2719914)). Qed.
Lemma lem2719916 : term257.
Proof. exact (EQ_MP (@lem2719915) (@lem0)). Qed.
Lemma lem2719917 : term466.
Proof. exact (@lem2719906 (@lem2719916)). Qed.
Lemma lem2719919 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2719920 : term257 = term258.
Proof. exact (@lem2719919 (NUMERAL 0) term111). Qed.
Lemma lem2719921 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2719922 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2719923 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2719922 h1) (fun h1 : term258 = True => @lem2719921)). Qed.
Lemma lem2719924 : term258 = True.
Proof. exact (EQ_MP (@lem2719923) (@lem2719921)). Qed.
Lemma lem2719925 : term257 = True.
Proof. exact (TRANS (@lem2719920) (@lem2719924)). Qed.
Lemma lem2719926 : True = term257.
Proof. exact (SYM (@lem2719925)). Qed.
Lemma lem2719927 : term257.
Proof. exact (EQ_MP (@lem2719926) (@lem0)). Qed.
Lemma lem2719928 : term467.
Proof. exact (@lem2719917 (@lem2719927)). Qed.
Lemma lem2719930 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2719931 : term257 = term258.
Proof. exact (@lem2719930 (NUMERAL 0) term111). Qed.
Lemma lem2719932 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2719933 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2719934 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2719933 h1) (fun h1 : term258 = True => @lem2719932)). Qed.
Lemma lem2719935 : term258 = True.
Proof. exact (EQ_MP (@lem2719934) (@lem2719932)). Qed.
Lemma lem2719936 : term257 = True.
Proof. exact (TRANS (@lem2719931) (@lem2719935)). Qed.
Lemma lem2719937 : True = term257.
Proof. exact (SYM (@lem2719936)). Qed.
Lemma lem2719938 : term257.
Proof. exact (EQ_MP (@lem2719937) (@lem0)). Qed.
Lemma lem2719939 : term468.
Proof. exact (@lem2719928 (@lem2719938)). Qed.
Lemma lem2719941 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2719942 : term202 = term203.
Proof. exact (@lem2719941 term111 term111). Qed.
Lemma lem2719943 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2719944 : term205 = term111.
Proof. exact (EQ_MP (@lem2719943) (@lem940073)). Qed.
Lemma lem2719945 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2719946 : term203 = term110.
Proof. exact (MK_COMB (@lem2719945) (@lem2719944)). Qed.
Lemma lem2719947 : term202 = term110.
Proof. exact (TRANS (@lem2719942) (@lem2719946)). Qed.
Lemma lem2719949 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2719950 : term215 = term220.
Proof. exact (@lem2719949 term111 term111). Qed.
Lemma lem2719951 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2719952 : term205 = term111.
Proof. exact (EQ_MP (@lem2719951) (@lem940073)). Qed.
Lemma lem2719953 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2719954 : term203 = term110.
Proof. exact (MK_COMB (@lem2719953) (@lem2719952)). Qed.
Lemma lem2719955 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2719956 : term220 = term193.
Proof. exact (MK_COMB (@lem2719955) (@lem2719954)). Qed.
Lemma lem2719957 : term215 = term193.
Proof. exact (TRANS (@lem2719950) (@lem2719956)). Qed.
Lemma lem2719958 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2719959 : term469 = term461.
Proof. exact (MK_COMB (@lem2719958) (@lem2719957)). Qed.
Lemma lem2719960 : term470 = term463.
Proof. exact (MK_COMB (@lem2719959) (@lem2719947)). Qed.
Lemma lem2719962 (m : nat) : (term471 m) = term107.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2719963 : term463 = term107.
Proof. exact (@lem2719962 term111). Qed.
Lemma lem2719964 : term470 = term107.
Proof. exact (TRANS (@lem2719960) (@lem2719963)). Qed.
Lemma lem2719965 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2719966 : term472 = term267.
Proof. exact (MK_COMB (@lem2719965) (@lem2719964)). Qed.
Lemma lem2719967 : term110 = term110.
Proof. exact (eq_refl term110). Qed.
Lemma lem2719968 : term473 = term269.
Proof. exact (MK_COMB (@lem2719966) (@lem2719967)). Qed.
Lemma lem2719970 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2719971 : term269 = term107.
Proof. exact (@lem2719970 term111). Qed.
Lemma lem2719972 : term473 = term107.
Proof. exact (TRANS (@lem2719968) (@lem2719971)). Qed.
Lemma lem2719974 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2719975 : term202 = term203.
Proof. exact (@lem2719974 term111 term111). Qed.
Lemma lem2719976 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2719977 : term205 = term111.
Proof. exact (EQ_MP (@lem2719976) (@lem940073)). Qed.
Lemma lem2719978 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2719979 : term203 = term110.
Proof. exact (MK_COMB (@lem2719978) (@lem2719977)). Qed.
Lemma lem2719980 : term202 = term110.
Proof. exact (TRANS (@lem2719975) (@lem2719979)). Qed.
Lemma lem2719981 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2719982 : term271 = term269.
Proof. exact (MK_COMB (@lem2719981) (@lem2719980)). Qed.
Lemma lem2719984 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2719985 : term269 = term107.
Proof. exact (@lem2719984 term111). Qed.
Lemma lem2719986 : term271 = term107.
Proof. exact (TRANS (@lem2719982) (@lem2719985)). Qed.
Lemma lem2719987 : term107 = term271.
Proof. exact (SYM (@lem2719986)). Qed.
Lemma lem2719988 : term473 = term271.
Proof. exact (TRANS (@lem2719972) (@lem2719987)). Qed.
Lemma lem2719989 : term464 = term190.
Proof. exact (@lem2719939 (@lem2719988)). Qed.
Lemma lem2719990 : term463 = term190.
Proof. exact (TRANS (@lem2719905) (@lem2719989)). Qed.
Lemma lem2719992 (x : real) : (term209 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2719993 : term190 = term107.
Proof. exact (@lem2719992 term107). Qed.
Lemma lem2719994 : term463 = term107.
Proof. exact (TRANS (@lem2719990) (@lem2719993)). Qed.
Lemma lem2719995 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2719996 : term474 = term267.
Proof. exact (MK_COMB (@lem2719995) (@lem2719994)). Qed.
Lemma lem2719997 (n : int) : (term104 n) = (term104 n).
Proof. exact (eq_refl (term104 n)). Qed.
Lemma lem2719998 (n : int) : (term460 n) = (term475 n).
Proof. exact (MK_COMB (@lem2719996) (@lem2719997 n)). Qed.
Lemma lem2719999 (n : int) : (term520 n) = (term475 n).
Proof. exact (TRANS (@lem2719896 n) (@lem2719998 n)). Qed.
Lemma lem2720000 (n : int) : (term475 n) = term107.
Proof. exact (@lem1982719 (term104 n)). Qed.
Lemma lem2720001 (n : int) : (term520 n) = term107.
Proof. exact (TRANS (@lem2719999 n) (@lem2720000 n)). Qed.
Lemma lem2720002 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2720003 (n : int) : (term521 n) = term139.
Proof. exact (MK_COMB (@lem2720002) (@lem2720001 n)). Qed.
Lemma lem2720004 : term308 = term308.
Proof. exact (eq_refl term308). Qed.
Lemma lem2720005 (n : int) : (term534 n) = term535.
Proof. exact (MK_COMB (@lem2720003 n) (@lem2720004)). Qed.
Lemma lem2720006 (n : int) : (term533 n) = term535.
Proof. exact (TRANS (@lem2719895 n) (@lem2720005 n)). Qed.
Lemma lem2720007 : term535 = term308.
Proof. exact (@lem1982721 term308). Qed.
Lemma lem2720008 (n : int) : (term533 n) = term308.
Proof. exact (TRANS (@lem2720006 n) (@lem2720007)). Qed.
Lemma lem2720009 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2720010 (n : int) : (term536 n) = term537.
Proof. exact (MK_COMB (@lem2720009) (@lem2720008 n)). Qed.
Lemma lem2720011 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2720012 (n : int) : (term532 n) = term538.
Proof. exact (MK_COMB (@lem2720010 n) (@lem2720011)). Qed.
Lemma lem2720013 (n : int) (h1 : term524 n) : term538.
Proof. exact (EQ_MP (@lem2720012 n) (@lem2719894 n h1)). Qed.
Lemma lem2720015 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2720016 : term538 = term539.
Proof. exact (@lem2720015 term107 term308). Qed.
Lemma lem2720018 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2720019 : term308 = term311.
Proof. exact (@lem2720018 term288). Qed.
Lemma lem2720021 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2720022 : term107 = term190.
Proof. exact (@lem2720021 (NUMERAL 0)). Qed.
Lemma lem2720023 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2720024 : term482 = term483.
Proof. exact (MK_COMB (@lem2720023) (@lem2720022)). Qed.
Lemma lem2720025 : term539 = term540.
Proof. exact (MK_COMB (@lem2720024) (@lem2720019)). Qed.
Lemma lem2720026 : term541.
Proof. exact (@lem1980026 term107 term110 term308 term110). Qed.
Lemma lem2720028 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2720029 : term257 = term258.
Proof. exact (@lem2720028 (NUMERAL 0) term111). Qed.
Lemma lem2720030 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2720031 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2720032 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2720031 h1) (fun h1 : term258 = True => @lem2720030)). Qed.
Lemma lem2720033 : term258 = True.
Proof. exact (EQ_MP (@lem2720032) (@lem2720030)). Qed.
Lemma lem2720034 : term257 = True.
Proof. exact (TRANS (@lem2720029) (@lem2720033)). Qed.
Lemma lem2720035 : True = term257.
Proof. exact (SYM (@lem2720034)). Qed.
Lemma lem2720036 : term257.
Proof. exact (EQ_MP (@lem2720035) (@lem0)). Qed.
Lemma lem2720037 : term542.
Proof. exact (@lem2720026 (@lem2720036)). Qed.
Lemma lem2720039 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2720040 : term257 = term258.
Proof. exact (@lem2720039 (NUMERAL 0) term111). Qed.
Lemma lem2720041 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2720042 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2720043 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2720042 h1) (fun h1 : term258 = True => @lem2720041)). Qed.
Lemma lem2720044 : term258 = True.
Proof. exact (EQ_MP (@lem2720043) (@lem2720041)). Qed.
Lemma lem2720045 : term257 = True.
Proof. exact (TRANS (@lem2720040) (@lem2720044)). Qed.
Lemma lem2720046 : True = term257.
Proof. exact (SYM (@lem2720045)). Qed.
Lemma lem2720047 : term257.
Proof. exact (EQ_MP (@lem2720046) (@lem0)). Qed.
Lemma lem2720048 : term540 = term543.
Proof. exact (@lem2720037 (@lem2720047)). Qed.
Lemma lem2720050 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2720051 : term544 = term545.
Proof. exact (@lem2720050 term288 term111). Qed.
Lemma lem2720052 : term294 = term286.
Proof. exact (@lem996237 term286). Qed.
Lemma lem2720053 : (term294 = term286) = (term295 = term288).
Proof. exact (@lem1007663 term286 (BIT1 0) term286). Qed.
Lemma lem2720054 : term295 = term288.
Proof. exact (EQ_MP (@lem2720053) (@lem2720052)). Qed.
Lemma lem2720055 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2720056 : term293 = term279.
Proof. exact (MK_COMB (@lem2720055) (@lem2720054)). Qed.
Lemma lem2720057 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2720058 : term545 = term308.
Proof. exact (MK_COMB (@lem2720057) (@lem2720056)). Qed.
Lemma lem2720059 : term544 = term308.
Proof. exact (TRANS (@lem2720051) (@lem2720058)). Qed.
Lemma lem2720061 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2720062 : term269 = term107.
Proof. exact (@lem2720061 term111). Qed.
Lemma lem2720063 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2720064 : term488 = term482.
Proof. exact (MK_COMB (@lem2720063) (@lem2720062)). Qed.
Lemma lem2720065 : term543 = term539.
Proof. exact (MK_COMB (@lem2720064) (@lem2720059)). Qed.
Lemma lem2720067 (m : nat) (n : nat) : (term489 m n) = (term490 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2720068 : term539 = term546.
Proof. exact (@lem2720067 (NUMERAL 0) term288). Qed.
Lemma lem2720069 : term547 = term286.
Proof. exact (@lem912803). Qed.
Lemma lem2720070 (h1 : term547 = term286) : (term288 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term286 h1). Qed.
Lemma lem2720071 : (term547 = term286) = ((term288 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term547 = term286 => @lem2720070 h1) (fun h1 : (term288 = (NUMERAL 0)) = False => @lem2720069)). Qed.
Lemma lem2720072 : (term288 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2720071) (@lem2720069)). Qed.
Lemma lem2720073 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2720074 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2720075 : term492 = (and True).
Proof. exact (MK_COMB (@lem2720074) (@lem2720073)). Qed.
Lemma lem2720076 : term546 = (True /\ False).
Proof. exact (MK_COMB (@lem2720075) (@lem2720072)). Qed.
Lemma lem2720078 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2720079 : term546 = False.
Proof. exact (TRANS (@lem2720076) (@lem2720078)). Qed.
Lemma lem2720080 : term539 = False.
Proof. exact (TRANS (@lem2720068) (@lem2720079)). Qed.
Lemma lem2720081 : term543 = False.
Proof. exact (TRANS (@lem2720065) (@lem2720080)). Qed.
Lemma lem2720082 : term540 = False.
Proof. exact (TRANS (@lem2720048) (@lem2720081)). Qed.
Lemma lem2720083 : term539 = False.
Proof. exact (TRANS (@lem2720025) (@lem2720082)). Qed.
Lemma lem2720084 : term538 = False.
Proof. exact (TRANS (@lem2720016) (@lem2720083)). Qed.
Lemma lem2720085 (n : int) (h1 : term524 n) : False.
Proof. exact (EQ_MP (@lem2720084) (@lem2720013 n h1)). Qed.
Lemma lem2720086 (n : int) (h1 : term548 n) : term548 n.
Proof. exact (h1). Qed.
Lemma lem2720087 (n : int) (h1 : term548 n) : term401 n.
Proof. exact (proj2 (@lem2720086 n h1)). Qed.
Lemma lem2720088 (n : int) (h1 : term548 n) : (term223 n) = term107.
Proof. exact (proj1 (@lem2720086 n h1)). Qed.
Lemma lem2720089 (n : int) (h1 : term548 n) : term315 n.
Proof. exact (proj2 (@lem2720087 n h1)). Qed.
Lemma lem2720092 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2720093 : term433 = term257.
Proof. exact (@lem2720092 term107 term110). Qed.
Lemma lem2720095 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2720096 : term110 = term214.
Proof. exact (@lem2720095 term111). Qed.
Lemma lem2720098 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2720099 : term107 = term190.
Proof. exact (@lem2720098 (NUMERAL 0)). Qed.
Lemma lem2720100 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2720101 : term434 = term435.
Proof. exact (MK_COMB (@lem2720100) (@lem2720099)). Qed.
Lemma lem2720102 : term257 = term436.
Proof. exact (MK_COMB (@lem2720101) (@lem2720096)). Qed.
Lemma lem2720103 : term437.
Proof. exact (@lem1980255 term107 term110 term110 term110). Qed.
Lemma lem2720105 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2720106 : term257 = term258.
Proof. exact (@lem2720105 (NUMERAL 0) term111). Qed.
Lemma lem2720107 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2720108 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2720109 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2720108 h1) (fun h1 : term258 = True => @lem2720107)). Qed.
Lemma lem2720110 : term258 = True.
Proof. exact (EQ_MP (@lem2720109) (@lem2720107)). Qed.
Lemma lem2720111 : term257 = True.
Proof. exact (TRANS (@lem2720106) (@lem2720110)). Qed.
Lemma lem2720112 : True = term257.
Proof. exact (SYM (@lem2720111)). Qed.
Lemma lem2720113 : term257.
Proof. exact (EQ_MP (@lem2720112) (@lem0)). Qed.
Lemma lem2720114 : term438.
Proof. exact (@lem2720103 (@lem2720113)). Qed.
Lemma lem2720116 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2720117 : term257 = term258.
Proof. exact (@lem2720116 (NUMERAL 0) term111). Qed.
Lemma lem2720118 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2720119 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2720120 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2720119 h1) (fun h1 : term258 = True => @lem2720118)). Qed.
Lemma lem2720121 : term258 = True.
Proof. exact (EQ_MP (@lem2720120) (@lem2720118)). Qed.
Lemma lem2720122 : term257 = True.
Proof. exact (TRANS (@lem2720117) (@lem2720121)). Qed.
Lemma lem2720123 : True = term257.
Proof. exact (SYM (@lem2720122)). Qed.
Lemma lem2720124 : term257.
Proof. exact (EQ_MP (@lem2720123) (@lem0)). Qed.
Lemma lem2720125 : term436 = term439.
Proof. exact (@lem2720114 (@lem2720124)). Qed.
Lemma lem2720127 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2720128 : term202 = term203.
Proof. exact (@lem2720127 term111 term111). Qed.
Lemma lem2720129 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2720130 : term205 = term111.
Proof. exact (EQ_MP (@lem2720129) (@lem940073)). Qed.
Lemma lem2720131 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2720132 : term203 = term110.
Proof. exact (MK_COMB (@lem2720131) (@lem2720130)). Qed.
Lemma lem2720133 : term202 = term110.
Proof. exact (TRANS (@lem2720128) (@lem2720132)). Qed.
Lemma lem2720135 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2720136 : term269 = term107.
Proof. exact (@lem2720135 term111). Qed.
Lemma lem2720137 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2720138 : term440 = term434.
Proof. exact (MK_COMB (@lem2720137) (@lem2720136)). Qed.
Lemma lem2720139 : term439 = term257.
Proof. exact (MK_COMB (@lem2720138) (@lem2720133)). Qed.
Lemma lem2720141 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2720142 : term257 = term258.
Proof. exact (@lem2720141 (NUMERAL 0) term111). Qed.
Lemma lem2720143 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2720144 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2720145 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2720144 h1) (fun h1 : term258 = True => @lem2720143)). Qed.
Lemma lem2720146 : term258 = True.
Proof. exact (EQ_MP (@lem2720145) (@lem2720143)). Qed.
Lemma lem2720147 : term257 = True.
Proof. exact (TRANS (@lem2720142) (@lem2720146)). Qed.
Lemma lem2720148 : term439 = True.
Proof. exact (TRANS (@lem2720139) (@lem2720147)). Qed.
Lemma lem2720149 : term436 = True.
Proof. exact (TRANS (@lem2720125) (@lem2720148)). Qed.
Lemma lem2720150 : term257 = True.
Proof. exact (TRANS (@lem2720102) (@lem2720149)). Qed.
Lemma lem2720151 : term433 = True.
Proof. exact (TRANS (@lem2720093) (@lem2720150)). Qed.
Lemma lem2720152 : True = term433.
Proof. exact (SYM (@lem2720151)). Qed.
Lemma lem2720153 : term433.
Proof. exact (EQ_MP (@lem2720152) (@lem0)). Qed.
Lemma lem2720154 (n : int) (h1 : term548 n) : term525 n.
Proof. exact (conj (@lem2720153) (@lem2720089 n h1)). Qed.
Lemma lem2720156 (x : real) (y : real) : term442 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2720157 (n : int) : term526 n.
Proof. exact (@lem2720156 term110 (term312 n)). Qed.
Lemma lem2720158 (n : int) (h1 : term548 n) : term527 n.
Proof. exact (@lem2720157 n (@lem2720154 n h1)). Qed.
Lemma lem2720159 (n : int) : (term528 n) = (term312 n).
Proof. exact (@lem1982733 (term312 n)). Qed.
Lemma lem2720160 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2720161 (n : int) : (term529 n) = (term314 n).
Proof. exact (MK_COMB (@lem2720160) (@lem2720159 n)). Qed.
Lemma lem2720162 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2720163 (n : int) : (term527 n) = (term315 n).
Proof. exact (MK_COMB (@lem2720161 n) (@lem2720162)). Qed.
Lemma lem2720164 (n : int) (h1 : term548 n) : term315 n.
Proof. exact (EQ_MP (@lem2720163 n) (@lem2720158 n h1)). Qed.
Lemma lem2720166 (y : real) : term447 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2720167 (n : int) : term499 n.
Proof. exact (@lem2720166 (term223 n)). Qed.
Lemma lem2720168 (n : int) (h1 : term548 n) : term500 n.
Proof. exact (@lem2720167 n (@lem2720088 n h1)). Qed.
Lemma lem2720169 (n : int) (h1 : term548 n) : term549 n.
Proof. exact (@lem2720168 n h1 term193). Qed.
Lemma lem2720170 (n : int) : (term549 n) = ((term550 n) = term107).
Proof. exact (eq_refl (term549 n)). Qed.
Lemma lem2720171 (n : int) (h1 : term548 n) : (term550 n) = term107.
Proof. exact (EQ_MP (@lem2720170 n) (@lem2720169 n h1)). Qed.
Lemma lem2720172 (n : int) : (term550 n) = (term551 n).
Proof. exact (@lem1982781 (term104 n) term193 term193). Qed.
Lemma lem2720174 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2720175 : term193 = term194.
Proof. exact (@lem2720174 term111). Qed.
Lemma lem2720177 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2720178 : term193 = term194.
Proof. exact (@lem2720177 term111). Qed.
Lemma lem2720179 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2720180 : term195 = term196.
Proof. exact (MK_COMB (@lem2720179) (@lem2720178)). Qed.
Lemma lem2720181 : term552 = term553.
Proof. exact (MK_COMB (@lem2720180) (@lem2720175)). Qed.
Lemma lem2720182 : term553 = term554.
Proof. exact (@lem1981613 term193 term193 term110 term110). Qed.
Lemma lem2720184 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2720185 : term202 = term203.
Proof. exact (@lem2720184 term111 term111). Qed.
Lemma lem2720186 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2720187 : term205 = term111.
Proof. exact (EQ_MP (@lem2720186) (@lem940073)). Qed.
Lemma lem2720188 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2720189 : term203 = term110.
Proof. exact (MK_COMB (@lem2720188) (@lem2720187)). Qed.
Lemma lem2720190 : term202 = term110.
Proof. exact (TRANS (@lem2720185) (@lem2720189)). Qed.
Lemma lem2720192 (m : nat) (n : nat) : (term555 m n) = (term201 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2720193 : term552 = term203.
Proof. exact (@lem2720192 term111 term111). Qed.
Lemma lem2720194 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2720195 : term205 = term111.
Proof. exact (EQ_MP (@lem2720194) (@lem940073)). Qed.
Lemma lem2720196 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2720197 : term203 = term110.
Proof. exact (MK_COMB (@lem2720196) (@lem2720195)). Qed.
Lemma lem2720198 : term552 = term110.
Proof. exact (TRANS (@lem2720193) (@lem2720197)). Qed.
Lemma lem2720199 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2720200 : term556 = term557.
Proof. exact (MK_COMB (@lem2720199) (@lem2720198)). Qed.
Lemma lem2720201 : term554 = term214.
Proof. exact (MK_COMB (@lem2720200) (@lem2720190)). Qed.
Lemma lem2720202 : term553 = term214.
Proof. exact (TRANS (@lem2720182) (@lem2720201)). Qed.
Lemma lem2720203 : term552 = term214.
Proof. exact (TRANS (@lem2720181) (@lem2720202)). Qed.
Lemma lem2720205 (x : real) : (term209 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2720206 : term214 = term110.
Proof. exact (@lem2720205 term110). Qed.
Lemma lem2720207 : term552 = term110.
Proof. exact (TRANS (@lem2720203) (@lem2720206)). Qed.
Lemma lem2720210 (n : int) : (term232 n) = (term232 n).
Proof. exact (eq_refl (term232 n)). Qed.
Lemma lem2720211 (n : int) : (term551 n) = (term558 n).
Proof. exact (MK_COMB (@lem2720210 n) (@lem2720207)). Qed.
Lemma lem2720212 (n : int) : (term550 n) = (term558 n).
Proof. exact (TRANS (@lem2720172 n) (@lem2720211 n)). Qed.
Lemma lem2720213 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2720214 (n : int) : (term559 n) = (term560 n).
Proof. exact (MK_COMB (@lem2720213) (@lem2720212 n)). Qed.
Lemma lem2720215 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2720216 (n : int) : ((term550 n) = term107) = ((term558 n) = term107).
Proof. exact (MK_COMB (@lem2720214 n) (@lem2720215)). Qed.
Lemma lem2720217 (n : int) (h1 : term548 n) : (term558 n) = term107.
Proof. exact (EQ_MP (@lem2720216 n) (@lem2720171 n h1)). Qed.
Lemma lem2720218 (n : int) (h1 : term548 n) : term561 n.
Proof. exact (conj (@lem2720217 n h1) (@lem2720164 n h1)). Qed.
Lemma lem2720220 (x : real) (y : real) : term454 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2720221 (n : int) : term562 n.
Proof. exact (@lem2720220 (term558 n) (term312 n)). Qed.
Lemma lem2720222 (n : int) (h1 : term548 n) : term563 n.
Proof. exact (@lem2720221 n (@lem2720218 n h1)). Qed.
Lemma lem2720223 (n : int) : (term564 n) = (term565 n).
Proof. exact (@lem1982753 (term251 n) (term104 n) term110 term308). Qed.
Lemma lem2720224 (n : int) : (term520 n) = (term460 n).
Proof. exact (@lem1982713 term193 (term104 n)). Qed.
Lemma lem2720226 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2720227 : term110 = term214.
Proof. exact (@lem2720226 term111). Qed.
Lemma lem2720229 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2720230 : term193 = term194.
Proof. exact (@lem2720229 term111). Qed.
Lemma lem2720231 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2720232 : term461 = term462.
Proof. exact (MK_COMB (@lem2720231) (@lem2720230)). Qed.
Lemma lem2720233 : term463 = term464.
Proof. exact (MK_COMB (@lem2720232) (@lem2720227)). Qed.
Lemma lem2720234 : term465.
Proof. exact (@lem1981473 term193 term110 term110 term110 term107 term110). Qed.
Lemma lem2720236 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2720237 : term257 = term258.
Proof. exact (@lem2720236 (NUMERAL 0) term111). Qed.
Lemma lem2720238 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2720239 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2720240 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2720239 h1) (fun h1 : term258 = True => @lem2720238)). Qed.
Lemma lem2720241 : term258 = True.
Proof. exact (EQ_MP (@lem2720240) (@lem2720238)). Qed.
Lemma lem2720242 : term257 = True.
Proof. exact (TRANS (@lem2720237) (@lem2720241)). Qed.
Lemma lem2720243 : True = term257.
Proof. exact (SYM (@lem2720242)). Qed.
Lemma lem2720244 : term257.
Proof. exact (EQ_MP (@lem2720243) (@lem0)). Qed.
Lemma lem2720245 : term466.
Proof. exact (@lem2720234 (@lem2720244)). Qed.
Lemma lem2720247 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2720248 : term257 = term258.
Proof. exact (@lem2720247 (NUMERAL 0) term111). Qed.
Lemma lem2720249 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2720250 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2720251 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2720250 h1) (fun h1 : term258 = True => @lem2720249)). Qed.
Lemma lem2720252 : term258 = True.
Proof. exact (EQ_MP (@lem2720251) (@lem2720249)). Qed.
Lemma lem2720253 : term257 = True.
Proof. exact (TRANS (@lem2720248) (@lem2720252)). Qed.
Lemma lem2720254 : True = term257.
Proof. exact (SYM (@lem2720253)). Qed.
Lemma lem2720255 : term257.
Proof. exact (EQ_MP (@lem2720254) (@lem0)). Qed.
Lemma lem2720256 : term467.
Proof. exact (@lem2720245 (@lem2720255)). Qed.
Lemma lem2720258 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2720259 : term257 = term258.
Proof. exact (@lem2720258 (NUMERAL 0) term111). Qed.
Lemma lem2720260 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2720261 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2720262 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2720261 h1) (fun h1 : term258 = True => @lem2720260)). Qed.
Lemma lem2720263 : term258 = True.
Proof. exact (EQ_MP (@lem2720262) (@lem2720260)). Qed.
Lemma lem2720264 : term257 = True.
Proof. exact (TRANS (@lem2720259) (@lem2720263)). Qed.
Lemma lem2720265 : True = term257.
Proof. exact (SYM (@lem2720264)). Qed.
Lemma lem2720266 : term257.
Proof. exact (EQ_MP (@lem2720265) (@lem0)). Qed.
Lemma lem2720267 : term468.
Proof. exact (@lem2720256 (@lem2720266)). Qed.
Lemma lem2720269 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2720270 : term202 = term203.
Proof. exact (@lem2720269 term111 term111). Qed.
Lemma lem2720271 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2720272 : term205 = term111.
Proof. exact (EQ_MP (@lem2720271) (@lem940073)). Qed.
Lemma lem2720273 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2720274 : term203 = term110.
Proof. exact (MK_COMB (@lem2720273) (@lem2720272)). Qed.
Lemma lem2720275 : term202 = term110.
Proof. exact (TRANS (@lem2720270) (@lem2720274)). Qed.
Lemma lem2720277 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2720278 : term215 = term220.
Proof. exact (@lem2720277 term111 term111). Qed.
Lemma lem2720279 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2720280 : term205 = term111.
Proof. exact (EQ_MP (@lem2720279) (@lem940073)). Qed.
Lemma lem2720281 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2720282 : term203 = term110.
Proof. exact (MK_COMB (@lem2720281) (@lem2720280)). Qed.
Lemma lem2720283 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2720284 : term220 = term193.
Proof. exact (MK_COMB (@lem2720283) (@lem2720282)). Qed.
Lemma lem2720285 : term215 = term193.
Proof. exact (TRANS (@lem2720278) (@lem2720284)). Qed.
Lemma lem2720286 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2720287 : term469 = term461.
Proof. exact (MK_COMB (@lem2720286) (@lem2720285)). Qed.
Lemma lem2720288 : term470 = term463.
Proof. exact (MK_COMB (@lem2720287) (@lem2720275)). Qed.
Lemma lem2720290 (m : nat) : (term471 m) = term107.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2720291 : term463 = term107.
Proof. exact (@lem2720290 term111). Qed.
Lemma lem2720292 : term470 = term107.
Proof. exact (TRANS (@lem2720288) (@lem2720291)). Qed.
Lemma lem2720293 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2720294 : term472 = term267.
Proof. exact (MK_COMB (@lem2720293) (@lem2720292)). Qed.
Lemma lem2720295 : term110 = term110.
Proof. exact (eq_refl term110). Qed.
Lemma lem2720296 : term473 = term269.
Proof. exact (MK_COMB (@lem2720294) (@lem2720295)). Qed.
Lemma lem2720298 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2720299 : term269 = term107.
Proof. exact (@lem2720298 term111). Qed.
Lemma lem2720300 : term473 = term107.
Proof. exact (TRANS (@lem2720296) (@lem2720299)). Qed.
Lemma lem2720302 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2720303 : term202 = term203.
Proof. exact (@lem2720302 term111 term111). Qed.
Lemma lem2720304 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2720305 : term205 = term111.
Proof. exact (EQ_MP (@lem2720304) (@lem940073)). Qed.
Lemma lem2720306 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2720307 : term203 = term110.
Proof. exact (MK_COMB (@lem2720306) (@lem2720305)). Qed.
Lemma lem2720308 : term202 = term110.
Proof. exact (TRANS (@lem2720303) (@lem2720307)). Qed.
Lemma lem2720309 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2720310 : term271 = term269.
Proof. exact (MK_COMB (@lem2720309) (@lem2720308)). Qed.
Lemma lem2720312 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2720313 : term269 = term107.
Proof. exact (@lem2720312 term111). Qed.
Lemma lem2720314 : term271 = term107.
Proof. exact (TRANS (@lem2720310) (@lem2720313)). Qed.
Lemma lem2720315 : term107 = term271.
Proof. exact (SYM (@lem2720314)). Qed.
Lemma lem2720316 : term473 = term271.
Proof. exact (TRANS (@lem2720300) (@lem2720315)). Qed.
Lemma lem2720317 : term464 = term190.
Proof. exact (@lem2720267 (@lem2720316)). Qed.
Lemma lem2720318 : term463 = term190.
Proof. exact (TRANS (@lem2720233) (@lem2720317)). Qed.
Lemma lem2720320 (x : real) : (term209 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2720321 : term190 = term107.
Proof. exact (@lem2720320 term107). Qed.
Lemma lem2720322 : term463 = term107.
Proof. exact (TRANS (@lem2720318) (@lem2720321)). Qed.
Lemma lem2720323 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2720324 : term474 = term267.
Proof. exact (MK_COMB (@lem2720323) (@lem2720322)). Qed.
Lemma lem2720325 (n : int) : (term104 n) = (term104 n).
Proof. exact (eq_refl (term104 n)). Qed.
Lemma lem2720326 (n : int) : (term460 n) = (term475 n).
Proof. exact (MK_COMB (@lem2720324) (@lem2720325 n)). Qed.
Lemma lem2720327 (n : int) : (term520 n) = (term475 n).
Proof. exact (TRANS (@lem2720224 n) (@lem2720326 n)). Qed.
Lemma lem2720328 (n : int) : (term475 n) = term107.
Proof. exact (@lem1982719 (term104 n)). Qed.
Lemma lem2720329 (n : int) : (term520 n) = term107.
Proof. exact (TRANS (@lem2720327 n) (@lem2720328 n)). Qed.
Lemma lem2720330 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2720331 (n : int) : (term521 n) = term139.
Proof. exact (MK_COMB (@lem2720330) (@lem2720329 n)). Qed.
Lemma lem2720333 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2720334 : term308 = term311.
Proof. exact (@lem2720333 term288). Qed.
Lemma lem2720336 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2720337 : term110 = term214.
Proof. exact (@lem2720336 term111). Qed.
Lemma lem2720338 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2720339 : term157 = term252.
Proof. exact (MK_COMB (@lem2720338) (@lem2720337)). Qed.
Lemma lem2720340 : term566 = term567.
Proof. exact (MK_COMB (@lem2720339) (@lem2720334)). Qed.
Lemma lem2720341 : term568.
Proof. exact (@lem1981473 term110 term110 term308 term110 term193 term110). Qed.
Lemma lem2720343 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2720344 : term257 = term258.
Proof. exact (@lem2720343 (NUMERAL 0) term111). Qed.
Lemma lem2720345 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2720346 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2720347 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2720346 h1) (fun h1 : term258 = True => @lem2720345)). Qed.
Lemma lem2720348 : term258 = True.
Proof. exact (EQ_MP (@lem2720347) (@lem2720345)). Qed.
Lemma lem2720349 : term257 = True.
Proof. exact (TRANS (@lem2720344) (@lem2720348)). Qed.
Lemma lem2720350 : True = term257.
Proof. exact (SYM (@lem2720349)). Qed.
Lemma lem2720351 : term257.
Proof. exact (EQ_MP (@lem2720350) (@lem0)). Qed.
Lemma lem2720352 : term569.
Proof. exact (@lem2720341 (@lem2720351)). Qed.
Lemma lem2720354 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2720355 : term257 = term258.
Proof. exact (@lem2720354 (NUMERAL 0) term111). Qed.
Lemma lem2720356 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2720357 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2720358 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2720357 h1) (fun h1 : term258 = True => @lem2720356)). Qed.
Lemma lem2720359 : term258 = True.
Proof. exact (EQ_MP (@lem2720358) (@lem2720356)). Qed.
Lemma lem2720360 : term257 = True.
Proof. exact (TRANS (@lem2720355) (@lem2720359)). Qed.
Lemma lem2720361 : True = term257.
Proof. exact (SYM (@lem2720360)). Qed.
Lemma lem2720362 : term257.
Proof. exact (EQ_MP (@lem2720361) (@lem0)). Qed.
Lemma lem2720363 : term570.
Proof. exact (@lem2720352 (@lem2720362)). Qed.
Lemma lem2720365 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2720366 : term257 = term258.
Proof. exact (@lem2720365 (NUMERAL 0) term111). Qed.
Lemma lem2720367 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2720368 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2720369 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2720368 h1) (fun h1 : term258 = True => @lem2720367)). Qed.
Lemma lem2720370 : term258 = True.
Proof. exact (EQ_MP (@lem2720369) (@lem2720367)). Qed.
Lemma lem2720371 : term257 = True.
Proof. exact (TRANS (@lem2720366) (@lem2720370)). Qed.
Lemma lem2720372 : True = term257.
Proof. exact (SYM (@lem2720371)). Qed.
Lemma lem2720373 : term257.
Proof. exact (EQ_MP (@lem2720372) (@lem0)). Qed.
Lemma lem2720374 : term571.
Proof. exact (@lem2720363 (@lem2720373)). Qed.
Lemma lem2720376 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2720377 : term544 = term545.
Proof. exact (@lem2720376 term288 term111). Qed.
Lemma lem2720378 : term294 = term286.
Proof. exact (@lem996237 term286). Qed.
Lemma lem2720379 : (term294 = term286) = (term295 = term288).
Proof. exact (@lem1007663 term286 (BIT1 0) term286). Qed.
Lemma lem2720380 : term295 = term288.
Proof. exact (EQ_MP (@lem2720379) (@lem2720378)). Qed.
Lemma lem2720381 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2720382 : term293 = term279.
Proof. exact (MK_COMB (@lem2720381) (@lem2720380)). Qed.
Lemma lem2720383 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2720384 : term545 = term308.
Proof. exact (MK_COMB (@lem2720383) (@lem2720382)). Qed.
Lemma lem2720385 : term544 = term308.
Proof. exact (TRANS (@lem2720377) (@lem2720384)). Qed.
Lemma lem2720387 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2720388 : term202 = term203.
Proof. exact (@lem2720387 term111 term111). Qed.
Lemma lem2720389 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2720390 : term205 = term111.
Proof. exact (EQ_MP (@lem2720389) (@lem940073)). Qed.
Lemma lem2720391 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2720392 : term203 = term110.
Proof. exact (MK_COMB (@lem2720391) (@lem2720390)). Qed.
Lemma lem2720393 : term202 = term110.
Proof. exact (TRANS (@lem2720388) (@lem2720392)). Qed.
Lemma lem2720394 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2720395 : term263 = term157.
Proof. exact (MK_COMB (@lem2720394) (@lem2720393)). Qed.
Lemma lem2720396 : term572 = term566.
Proof. exact (MK_COMB (@lem2720395) (@lem2720385)). Qed.
Lemma lem2720399 : term573 = term193.
Proof. exact (@lem1367771 term111 term111). Qed.
Lemma lem2720400 : term285 = term286.
Proof. exact (@lem706885). Qed.
Lemma lem2720401 : (term285 = term286) = (term287 = term288).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term286). Qed.
Lemma lem2720402 : term287 = term288.
Proof. exact (EQ_MP (@lem2720401) (@lem2720400)). Qed.
Lemma lem2720403 : term288 = term287.
Proof. exact (SYM (@lem2720402)). Qed.
Lemma lem2720404 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2720405 : term279 = term284.
Proof. exact (MK_COMB (@lem2720404) (@lem2720403)). Qed.
Lemma lem2720406 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2720407 : term308 = term574.
Proof. exact (MK_COMB (@lem2720406) (@lem2720405)). Qed.
Lemma lem2720408 : term157 = term157.
Proof. exact (eq_refl term157). Qed.
Lemma lem2720409 : term566 = term573.
Proof. exact (MK_COMB (@lem2720408) (@lem2720407)). Qed.
Lemma lem2720410 : term566 = term193.
Proof. exact (TRANS (@lem2720409) (@lem2720399)). Qed.
Lemma lem2720411 : term572 = term193.
Proof. exact (TRANS (@lem2720396) (@lem2720410)). Qed.
Lemma lem2720412 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2720413 : term575 = term195.
Proof. exact (MK_COMB (@lem2720412) (@lem2720411)). Qed.
Lemma lem2720414 : term110 = term110.
Proof. exact (eq_refl term110). Qed.
Lemma lem2720415 : term576 = term215.
Proof. exact (MK_COMB (@lem2720413) (@lem2720414)). Qed.
Lemma lem2720417 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2720418 : term215 = term220.
Proof. exact (@lem2720417 term111 term111). Qed.
Lemma lem2720419 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2720420 : term205 = term111.
Proof. exact (EQ_MP (@lem2720419) (@lem940073)). Qed.
Lemma lem2720421 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2720422 : term203 = term110.
Proof. exact (MK_COMB (@lem2720421) (@lem2720420)). Qed.
Lemma lem2720423 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2720424 : term220 = term193.
Proof. exact (MK_COMB (@lem2720423) (@lem2720422)). Qed.
Lemma lem2720425 : term215 = term193.
Proof. exact (TRANS (@lem2720418) (@lem2720424)). Qed.
Lemma lem2720426 : term576 = term193.
Proof. exact (TRANS (@lem2720415) (@lem2720425)). Qed.
Lemma lem2720428 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2720429 : term202 = term203.
Proof. exact (@lem2720428 term111 term111). Qed.
Lemma lem2720430 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2720431 : term205 = term111.
Proof. exact (EQ_MP (@lem2720430) (@lem940073)). Qed.
Lemma lem2720432 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2720433 : term203 = term110.
Proof. exact (MK_COMB (@lem2720432) (@lem2720431)). Qed.
Lemma lem2720434 : term202 = term110.
Proof. exact (TRANS (@lem2720429) (@lem2720433)). Qed.
Lemma lem2720435 : term195 = term195.
Proof. exact (eq_refl term195). Qed.
Lemma lem2720436 : term577 = term215.
Proof. exact (MK_COMB (@lem2720435) (@lem2720434)). Qed.
Lemma lem2720438 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2720439 : term215 = term220.
Proof. exact (@lem2720438 term111 term111). Qed.
Lemma lem2720440 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2720441 : term205 = term111.
Proof. exact (EQ_MP (@lem2720440) (@lem940073)). Qed.
Lemma lem2720442 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2720443 : term203 = term110.
Proof. exact (MK_COMB (@lem2720442) (@lem2720441)). Qed.
Lemma lem2720444 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2720445 : term220 = term193.
Proof. exact (MK_COMB (@lem2720444) (@lem2720443)). Qed.
Lemma lem2720446 : term215 = term193.
Proof. exact (TRANS (@lem2720439) (@lem2720445)). Qed.
Lemma lem2720447 : term577 = term193.
Proof. exact (TRANS (@lem2720436) (@lem2720446)). Qed.
Lemma lem2720448 : term193 = term577.
Proof. exact (SYM (@lem2720447)). Qed.
Lemma lem2720449 : term576 = term577.
Proof. exact (TRANS (@lem2720426) (@lem2720448)). Qed.
Lemma lem2720450 : term567 = term194.
Proof. exact (@lem2720374 (@lem2720449)). Qed.
Lemma lem2720451 : term566 = term194.
Proof. exact (TRANS (@lem2720340) (@lem2720450)). Qed.
Lemma lem2720453 (x : real) : (term209 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2720454 : term194 = term193.
Proof. exact (@lem2720453 term193). Qed.
Lemma lem2720455 : term566 = term193.
Proof. exact (TRANS (@lem2720451) (@lem2720454)). Qed.
Lemma lem2720456 (n : int) : (term565 n) = term477.
Proof. exact (MK_COMB (@lem2720331 n) (@lem2720455)). Qed.
Lemma lem2720457 (n : int) : (term564 n) = term477.
Proof. exact (TRANS (@lem2720223 n) (@lem2720456 n)). Qed.
Lemma lem2720458 : term477 = term193.
Proof. exact (@lem1982721 term193). Qed.
Lemma lem2720459 (n : int) : (term564 n) = term193.
Proof. exact (TRANS (@lem2720457 n) (@lem2720458)). Qed.
Lemma lem2720460 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2720461 (n : int) : (term578 n) = term479.
Proof. exact (MK_COMB (@lem2720460) (@lem2720459 n)). Qed.
Lemma lem2720462 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2720463 (n : int) : (term563 n) = term480.
Proof. exact (MK_COMB (@lem2720461 n) (@lem2720462)). Qed.
Lemma lem2720464 (n : int) (h1 : term548 n) : term480.
Proof. exact (EQ_MP (@lem2720463 n) (@lem2720222 n h1)). Qed.
Lemma lem2720466 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2720467 : term480 = term481.
Proof. exact (@lem2720466 term107 term193). Qed.
Lemma lem2720469 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2720470 : term193 = term194.
Proof. exact (@lem2720469 term111). Qed.
Lemma lem2720472 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2720473 : term107 = term190.
Proof. exact (@lem2720472 (NUMERAL 0)). Qed.
Lemma lem2720474 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2720475 : term482 = term483.
Proof. exact (MK_COMB (@lem2720474) (@lem2720473)). Qed.
Lemma lem2720476 : term481 = term484.
Proof. exact (MK_COMB (@lem2720475) (@lem2720470)). Qed.
Lemma lem2720477 : term485.
Proof. exact (@lem1980026 term107 term110 term193 term110). Qed.
Lemma lem2720479 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2720480 : term257 = term258.
Proof. exact (@lem2720479 (NUMERAL 0) term111). Qed.
Lemma lem2720481 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2720482 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2720483 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2720482 h1) (fun h1 : term258 = True => @lem2720481)). Qed.
Lemma lem2720484 : term258 = True.
Proof. exact (EQ_MP (@lem2720483) (@lem2720481)). Qed.
Lemma lem2720485 : term257 = True.
Proof. exact (TRANS (@lem2720480) (@lem2720484)). Qed.
Lemma lem2720486 : True = term257.
Proof. exact (SYM (@lem2720485)). Qed.
Lemma lem2720487 : term257.
Proof. exact (EQ_MP (@lem2720486) (@lem0)). Qed.
Lemma lem2720488 : term486.
Proof. exact (@lem2720477 (@lem2720487)). Qed.
Lemma lem2720490 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2720491 : term257 = term258.
Proof. exact (@lem2720490 (NUMERAL 0) term111). Qed.
Lemma lem2720492 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2720493 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2720494 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2720493 h1) (fun h1 : term258 = True => @lem2720492)). Qed.
Lemma lem2720495 : term258 = True.
Proof. exact (EQ_MP (@lem2720494) (@lem2720492)). Qed.
Lemma lem2720496 : term257 = True.
Proof. exact (TRANS (@lem2720491) (@lem2720495)). Qed.
Lemma lem2720497 : True = term257.
Proof. exact (SYM (@lem2720496)). Qed.
Lemma lem2720498 : term257.
Proof. exact (EQ_MP (@lem2720497) (@lem0)). Qed.
Lemma lem2720499 : term484 = term487.
Proof. exact (@lem2720488 (@lem2720498)). Qed.
Lemma lem2720501 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2720502 : term215 = term220.
Proof. exact (@lem2720501 term111 term111). Qed.
Lemma lem2720503 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2720504 : term205 = term111.
Proof. exact (EQ_MP (@lem2720503) (@lem940073)). Qed.
Lemma lem2720505 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2720506 : term203 = term110.
Proof. exact (MK_COMB (@lem2720505) (@lem2720504)). Qed.
Lemma lem2720507 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2720508 : term220 = term193.
Proof. exact (MK_COMB (@lem2720507) (@lem2720506)). Qed.
Lemma lem2720509 : term215 = term193.
Proof. exact (TRANS (@lem2720502) (@lem2720508)). Qed.
Lemma lem2720511 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2720512 : term269 = term107.
Proof. exact (@lem2720511 term111). Qed.
Lemma lem2720513 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2720514 : term488 = term482.
Proof. exact (MK_COMB (@lem2720513) (@lem2720512)). Qed.
Lemma lem2720515 : term487 = term481.
Proof. exact (MK_COMB (@lem2720514) (@lem2720509)). Qed.
Lemma lem2720517 (m : nat) (n : nat) : (term489 m n) = (term490 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2720518 : term481 = term491.
Proof. exact (@lem2720517 (NUMERAL 0) term111). Qed.
Lemma lem2720519 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2720520 (h1 : term259 = (BIT1 0)) : (term111 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2720521 : (term259 = (BIT1 0)) = ((term111 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2720520 h1) (fun h1 : (term111 = (NUMERAL 0)) = False => @lem2720519)). Qed.
Lemma lem2720522 : (term111 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2720521) (@lem2720519)). Qed.
Lemma lem2720523 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2720524 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2720525 : term492 = (and True).
Proof. exact (MK_COMB (@lem2720524) (@lem2720523)). Qed.
Lemma lem2720526 : term491 = (True /\ False).
Proof. exact (MK_COMB (@lem2720525) (@lem2720522)). Qed.
Lemma lem2720528 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2720529 : term491 = False.
Proof. exact (TRANS (@lem2720526) (@lem2720528)). Qed.
Lemma lem2720530 : term481 = False.
Proof. exact (TRANS (@lem2720518) (@lem2720529)). Qed.
Lemma lem2720531 : term487 = False.
Proof. exact (TRANS (@lem2720515) (@lem2720530)). Qed.
Lemma lem2720532 : term484 = False.
Proof. exact (TRANS (@lem2720499) (@lem2720531)). Qed.
Lemma lem2720533 : term481 = False.
Proof. exact (TRANS (@lem2720476) (@lem2720532)). Qed.
Lemma lem2720534 : term480 = False.
Proof. exact (TRANS (@lem2720467) (@lem2720533)). Qed.
Lemma lem2720535 (n : int) (h1 : term548 n) : False.
Proof. exact (EQ_MP (@lem2720534) (@lem2720464 n h1)). Qed.
Lemma lem2720536 (n : int) (h1 : term406 n) : False.
Proof. exact (or_elim (@lem2719797 n h1) (fun h0 : term524 n => @lem2720085 n h0) (fun h0 : term548 n => @lem2720535 n h0)). Qed.
Lemma lem2720537 (n : int) (h1 : term404 n) : term404 n.
Proof. exact (h1). Qed.
Lemma lem2720538 (n : int) (h1 : term579 n) : term579 n.
Proof. exact (h1). Qed.
Lemma lem2720539 (n : int) (h1 : term579 n) : term402 n.
Proof. exact (proj2 (@lem2720538 n h1)). Qed.
Lemma lem2720540 (n : int) (h1 : term579 n) : (term104 n) = term107.
Proof. exact (proj1 (@lem2720538 n h1)). Qed.
Lemma lem2720541 (n : int) (h1 : term579 n) : term315 n.
Proof. exact (proj2 (@lem2720539 n h1)). Qed.
Lemma lem2720544 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2720545 : term433 = term257.
Proof. exact (@lem2720544 term107 term110). Qed.
Lemma lem2720547 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2720548 : term110 = term214.
Proof. exact (@lem2720547 term111). Qed.
Lemma lem2720550 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2720551 : term107 = term190.
Proof. exact (@lem2720550 (NUMERAL 0)). Qed.
Lemma lem2720552 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2720553 : term434 = term435.
Proof. exact (MK_COMB (@lem2720552) (@lem2720551)). Qed.
Lemma lem2720554 : term257 = term436.
Proof. exact (MK_COMB (@lem2720553) (@lem2720548)). Qed.
Lemma lem2720555 : term437.
Proof. exact (@lem1980255 term107 term110 term110 term110). Qed.
Lemma lem2720557 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2720558 : term257 = term258.
Proof. exact (@lem2720557 (NUMERAL 0) term111). Qed.
Lemma lem2720559 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2720560 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2720561 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2720560 h1) (fun h1 : term258 = True => @lem2720559)). Qed.
Lemma lem2720562 : term258 = True.
Proof. exact (EQ_MP (@lem2720561) (@lem2720559)). Qed.
Lemma lem2720563 : term257 = True.
Proof. exact (TRANS (@lem2720558) (@lem2720562)). Qed.
Lemma lem2720564 : True = term257.
Proof. exact (SYM (@lem2720563)). Qed.
Lemma lem2720565 : term257.
Proof. exact (EQ_MP (@lem2720564) (@lem0)). Qed.
Lemma lem2720566 : term438.
Proof. exact (@lem2720555 (@lem2720565)). Qed.
Lemma lem2720568 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2720569 : term257 = term258.
Proof. exact (@lem2720568 (NUMERAL 0) term111). Qed.
Lemma lem2720570 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2720571 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2720572 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2720571 h1) (fun h1 : term258 = True => @lem2720570)). Qed.
Lemma lem2720573 : term258 = True.
Proof. exact (EQ_MP (@lem2720572) (@lem2720570)). Qed.
Lemma lem2720574 : term257 = True.
Proof. exact (TRANS (@lem2720569) (@lem2720573)). Qed.
Lemma lem2720575 : True = term257.
Proof. exact (SYM (@lem2720574)). Qed.
Lemma lem2720576 : term257.
Proof. exact (EQ_MP (@lem2720575) (@lem0)). Qed.
Lemma lem2720577 : term436 = term439.
Proof. exact (@lem2720566 (@lem2720576)). Qed.
Lemma lem2720579 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2720580 : term202 = term203.
Proof. exact (@lem2720579 term111 term111). Qed.
Lemma lem2720581 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2720582 : term205 = term111.
Proof. exact (EQ_MP (@lem2720581) (@lem940073)). Qed.
Lemma lem2720583 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2720584 : term203 = term110.
Proof. exact (MK_COMB (@lem2720583) (@lem2720582)). Qed.
Lemma lem2720585 : term202 = term110.
Proof. exact (TRANS (@lem2720580) (@lem2720584)). Qed.
Lemma lem2720587 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2720588 : term269 = term107.
Proof. exact (@lem2720587 term111). Qed.
Lemma lem2720589 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2720590 : term440 = term434.
Proof. exact (MK_COMB (@lem2720589) (@lem2720588)). Qed.
Lemma lem2720591 : term439 = term257.
Proof. exact (MK_COMB (@lem2720590) (@lem2720585)). Qed.
Lemma lem2720593 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2720594 : term257 = term258.
Proof. exact (@lem2720593 (NUMERAL 0) term111). Qed.
Lemma lem2720595 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2720596 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2720597 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2720596 h1) (fun h1 : term258 = True => @lem2720595)). Qed.
Lemma lem2720598 : term258 = True.
Proof. exact (EQ_MP (@lem2720597) (@lem2720595)). Qed.
Lemma lem2720599 : term257 = True.
Proof. exact (TRANS (@lem2720594) (@lem2720598)). Qed.
Lemma lem2720600 : term439 = True.
Proof. exact (TRANS (@lem2720591) (@lem2720599)). Qed.
Lemma lem2720601 : term436 = True.
Proof. exact (TRANS (@lem2720577) (@lem2720600)). Qed.
Lemma lem2720602 : term257 = True.
Proof. exact (TRANS (@lem2720554) (@lem2720601)). Qed.
Lemma lem2720603 : term433 = True.
Proof. exact (TRANS (@lem2720545) (@lem2720602)). Qed.
Lemma lem2720604 : True = term433.
Proof. exact (SYM (@lem2720603)). Qed.
Lemma lem2720605 : term433.
Proof. exact (EQ_MP (@lem2720604) (@lem0)). Qed.
Lemma lem2720606 (n : int) (h1 : term579 n) : term525 n.
Proof. exact (conj (@lem2720605) (@lem2720541 n h1)). Qed.
Lemma lem2720608 (x : real) (y : real) : term442 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2720609 (n : int) : term526 n.
Proof. exact (@lem2720608 term110 (term312 n)). Qed.
Lemma lem2720610 (n : int) (h1 : term579 n) : term527 n.
Proof. exact (@lem2720609 n (@lem2720606 n h1)). Qed.
Lemma lem2720611 (n : int) : (term528 n) = (term312 n).
Proof. exact (@lem1982733 (term312 n)). Qed.
Lemma lem2720612 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2720613 (n : int) : (term529 n) = (term314 n).
Proof. exact (MK_COMB (@lem2720612) (@lem2720611 n)). Qed.
Lemma lem2720614 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2720615 (n : int) : (term527 n) = (term315 n).
Proof. exact (MK_COMB (@lem2720613 n) (@lem2720614)). Qed.
Lemma lem2720616 (n : int) (h1 : term579 n) : term315 n.
Proof. exact (EQ_MP (@lem2720615 n) (@lem2720610 n h1)). Qed.
Lemma lem2720618 (y : real) : term447 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2720619 (n : int) : term448 n.
Proof. exact (@lem2720618 (term104 n)). Qed.
Lemma lem2720620 (n : int) (h1 : term579 n) : term449 n.
Proof. exact (@lem2720619 n (@lem2720540 n h1)). Qed.
Lemma lem2720621 (n : int) (h1 : term579 n) : term514 n.
Proof. exact (@lem2720620 n h1 term193). Qed.
Lemma lem2720622 (n : int) : (term514 n) = ((term251 n) = term107).
Proof. exact (eq_refl (term514 n)). Qed.
Lemma lem2720629 (n : int) (h1 : term579 n) : (term251 n) = term107.
Proof. exact (EQ_MP (@lem2720622 n) (@lem2720621 n h1)). Qed.
Lemma lem2720630 (n : int) (h1 : term579 n) : term530 n.
Proof. exact (conj (@lem2720629 n h1) (@lem2720616 n h1)). Qed.
Lemma lem2720632 (x : real) (y : real) : term454 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2720633 (n : int) : term531 n.
Proof. exact (@lem2720632 (term251 n) (term312 n)). Qed.
Lemma lem2720634 (n : int) (h1 : term579 n) : term532 n.
Proof. exact (@lem2720633 n (@lem2720630 n h1)). Qed.
Lemma lem2720635 (n : int) : (term533 n) = (term534 n).
Proof. exact (@lem1982763 (term251 n) (term104 n) term308). Qed.
Lemma lem2720636 (n : int) : (term520 n) = (term460 n).
Proof. exact (@lem1982713 term193 (term104 n)). Qed.
Lemma lem2720638 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2720639 : term110 = term214.
Proof. exact (@lem2720638 term111). Qed.
Lemma lem2720641 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2720642 : term193 = term194.
Proof. exact (@lem2720641 term111). Qed.
Lemma lem2720643 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2720644 : term461 = term462.
Proof. exact (MK_COMB (@lem2720643) (@lem2720642)). Qed.
Lemma lem2720645 : term463 = term464.
Proof. exact (MK_COMB (@lem2720644) (@lem2720639)). Qed.
Lemma lem2720646 : term465.
Proof. exact (@lem1981473 term193 term110 term110 term110 term107 term110). Qed.
Lemma lem2720648 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2720649 : term257 = term258.
Proof. exact (@lem2720648 (NUMERAL 0) term111). Qed.
Lemma lem2720650 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2720651 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2720652 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2720651 h1) (fun h1 : term258 = True => @lem2720650)). Qed.
Lemma lem2720653 : term258 = True.
Proof. exact (EQ_MP (@lem2720652) (@lem2720650)). Qed.
Lemma lem2720654 : term257 = True.
Proof. exact (TRANS (@lem2720649) (@lem2720653)). Qed.
Lemma lem2720655 : True = term257.
Proof. exact (SYM (@lem2720654)). Qed.
Lemma lem2720656 : term257.
Proof. exact (EQ_MP (@lem2720655) (@lem0)). Qed.
Lemma lem2720657 : term466.
Proof. exact (@lem2720646 (@lem2720656)). Qed.
Lemma lem2720659 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2720660 : term257 = term258.
Proof. exact (@lem2720659 (NUMERAL 0) term111). Qed.
Lemma lem2720661 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2720662 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2720663 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2720662 h1) (fun h1 : term258 = True => @lem2720661)). Qed.
Lemma lem2720664 : term258 = True.
Proof. exact (EQ_MP (@lem2720663) (@lem2720661)). Qed.
Lemma lem2720665 : term257 = True.
Proof. exact (TRANS (@lem2720660) (@lem2720664)). Qed.
Lemma lem2720666 : True = term257.
Proof. exact (SYM (@lem2720665)). Qed.
Lemma lem2720667 : term257.
Proof. exact (EQ_MP (@lem2720666) (@lem0)). Qed.
Lemma lem2720668 : term467.
Proof. exact (@lem2720657 (@lem2720667)). Qed.
Lemma lem2720670 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2720671 : term257 = term258.
Proof. exact (@lem2720670 (NUMERAL 0) term111). Qed.
Lemma lem2720672 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2720673 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2720674 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2720673 h1) (fun h1 : term258 = True => @lem2720672)). Qed.
Lemma lem2720675 : term258 = True.
Proof. exact (EQ_MP (@lem2720674) (@lem2720672)). Qed.
Lemma lem2720676 : term257 = True.
Proof. exact (TRANS (@lem2720671) (@lem2720675)). Qed.
Lemma lem2720677 : True = term257.
Proof. exact (SYM (@lem2720676)). Qed.
Lemma lem2720678 : term257.
Proof. exact (EQ_MP (@lem2720677) (@lem0)). Qed.
Lemma lem2720679 : term468.
Proof. exact (@lem2720668 (@lem2720678)). Qed.
Lemma lem2720681 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2720682 : term202 = term203.
Proof. exact (@lem2720681 term111 term111). Qed.
Lemma lem2720683 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2720684 : term205 = term111.
Proof. exact (EQ_MP (@lem2720683) (@lem940073)). Qed.
Lemma lem2720685 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2720686 : term203 = term110.
Proof. exact (MK_COMB (@lem2720685) (@lem2720684)). Qed.
Lemma lem2720687 : term202 = term110.
Proof. exact (TRANS (@lem2720682) (@lem2720686)). Qed.
Lemma lem2720689 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2720690 : term215 = term220.
Proof. exact (@lem2720689 term111 term111). Qed.
Lemma lem2720691 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2720692 : term205 = term111.
Proof. exact (EQ_MP (@lem2720691) (@lem940073)). Qed.
Lemma lem2720693 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2720694 : term203 = term110.
Proof. exact (MK_COMB (@lem2720693) (@lem2720692)). Qed.
Lemma lem2720695 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2720696 : term220 = term193.
Proof. exact (MK_COMB (@lem2720695) (@lem2720694)). Qed.
Lemma lem2720697 : term215 = term193.
Proof. exact (TRANS (@lem2720690) (@lem2720696)). Qed.
Lemma lem2720698 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2720699 : term469 = term461.
Proof. exact (MK_COMB (@lem2720698) (@lem2720697)). Qed.
Lemma lem2720700 : term470 = term463.
Proof. exact (MK_COMB (@lem2720699) (@lem2720687)). Qed.
Lemma lem2720702 (m : nat) : (term471 m) = term107.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2720703 : term463 = term107.
Proof. exact (@lem2720702 term111). Qed.
Lemma lem2720704 : term470 = term107.
Proof. exact (TRANS (@lem2720700) (@lem2720703)). Qed.
Lemma lem2720705 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2720706 : term472 = term267.
Proof. exact (MK_COMB (@lem2720705) (@lem2720704)). Qed.
Lemma lem2720707 : term110 = term110.
Proof. exact (eq_refl term110). Qed.
Lemma lem2720708 : term473 = term269.
Proof. exact (MK_COMB (@lem2720706) (@lem2720707)). Qed.
Lemma lem2720710 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2720711 : term269 = term107.
Proof. exact (@lem2720710 term111). Qed.
Lemma lem2720712 : term473 = term107.
Proof. exact (TRANS (@lem2720708) (@lem2720711)). Qed.
Lemma lem2720714 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2720715 : term202 = term203.
Proof. exact (@lem2720714 term111 term111). Qed.
Lemma lem2720716 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2720717 : term205 = term111.
Proof. exact (EQ_MP (@lem2720716) (@lem940073)). Qed.
Lemma lem2720718 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2720719 : term203 = term110.
Proof. exact (MK_COMB (@lem2720718) (@lem2720717)). Qed.
Lemma lem2720720 : term202 = term110.
Proof. exact (TRANS (@lem2720715) (@lem2720719)). Qed.
Lemma lem2720721 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2720722 : term271 = term269.
Proof. exact (MK_COMB (@lem2720721) (@lem2720720)). Qed.
Lemma lem2720724 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2720725 : term269 = term107.
Proof. exact (@lem2720724 term111). Qed.
Lemma lem2720726 : term271 = term107.
Proof. exact (TRANS (@lem2720722) (@lem2720725)). Qed.
Lemma lem2720727 : term107 = term271.
Proof. exact (SYM (@lem2720726)). Qed.
Lemma lem2720728 : term473 = term271.
Proof. exact (TRANS (@lem2720712) (@lem2720727)). Qed.
Lemma lem2720729 : term464 = term190.
Proof. exact (@lem2720679 (@lem2720728)). Qed.
Lemma lem2720730 : term463 = term190.
Proof. exact (TRANS (@lem2720645) (@lem2720729)). Qed.
Lemma lem2720732 (x : real) : (term209 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2720733 : term190 = term107.
Proof. exact (@lem2720732 term107). Qed.
Lemma lem2720734 : term463 = term107.
Proof. exact (TRANS (@lem2720730) (@lem2720733)). Qed.
Lemma lem2720735 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2720736 : term474 = term267.
Proof. exact (MK_COMB (@lem2720735) (@lem2720734)). Qed.
Lemma lem2720737 (n : int) : (term104 n) = (term104 n).
Proof. exact (eq_refl (term104 n)). Qed.
Lemma lem2720738 (n : int) : (term460 n) = (term475 n).
Proof. exact (MK_COMB (@lem2720736) (@lem2720737 n)). Qed.
Lemma lem2720739 (n : int) : (term520 n) = (term475 n).
Proof. exact (TRANS (@lem2720636 n) (@lem2720738 n)). Qed.
Lemma lem2720740 (n : int) : (term475 n) = term107.
Proof. exact (@lem1982719 (term104 n)). Qed.
Lemma lem2720741 (n : int) : (term520 n) = term107.
Proof. exact (TRANS (@lem2720739 n) (@lem2720740 n)). Qed.
Lemma lem2720742 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2720743 (n : int) : (term521 n) = term139.
Proof. exact (MK_COMB (@lem2720742) (@lem2720741 n)). Qed.
Lemma lem2720744 : term308 = term308.
Proof. exact (eq_refl term308). Qed.
Lemma lem2720745 (n : int) : (term534 n) = term535.
Proof. exact (MK_COMB (@lem2720743 n) (@lem2720744)). Qed.
Lemma lem2720746 (n : int) : (term533 n) = term535.
Proof. exact (TRANS (@lem2720635 n) (@lem2720745 n)). Qed.
Lemma lem2720747 : term535 = term308.
Proof. exact (@lem1982721 term308). Qed.
Lemma lem2720748 (n : int) : (term533 n) = term308.
Proof. exact (TRANS (@lem2720746 n) (@lem2720747)). Qed.
Lemma lem2720749 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2720750 (n : int) : (term536 n) = term537.
Proof. exact (MK_COMB (@lem2720749) (@lem2720748 n)). Qed.
Lemma lem2720751 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2720752 (n : int) : (term532 n) = term538.
Proof. exact (MK_COMB (@lem2720750 n) (@lem2720751)). Qed.
Lemma lem2720753 (n : int) (h1 : term579 n) : term538.
Proof. exact (EQ_MP (@lem2720752 n) (@lem2720634 n h1)). Qed.
Lemma lem2720755 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2720756 : term538 = term539.
Proof. exact (@lem2720755 term107 term308). Qed.
Lemma lem2720758 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2720759 : term308 = term311.
Proof. exact (@lem2720758 term288). Qed.
Lemma lem2720761 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2720762 : term107 = term190.
Proof. exact (@lem2720761 (NUMERAL 0)). Qed.
Lemma lem2720763 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2720764 : term482 = term483.
Proof. exact (MK_COMB (@lem2720763) (@lem2720762)). Qed.
Lemma lem2720765 : term539 = term540.
Proof. exact (MK_COMB (@lem2720764) (@lem2720759)). Qed.
Lemma lem2720766 : term541.
Proof. exact (@lem1980026 term107 term110 term308 term110). Qed.
Lemma lem2720768 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2720769 : term257 = term258.
Proof. exact (@lem2720768 (NUMERAL 0) term111). Qed.
Lemma lem2720770 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2720771 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2720772 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2720771 h1) (fun h1 : term258 = True => @lem2720770)). Qed.
Lemma lem2720773 : term258 = True.
Proof. exact (EQ_MP (@lem2720772) (@lem2720770)). Qed.
Lemma lem2720774 : term257 = True.
Proof. exact (TRANS (@lem2720769) (@lem2720773)). Qed.
Lemma lem2720775 : True = term257.
Proof. exact (SYM (@lem2720774)). Qed.
Lemma lem2720776 : term257.
Proof. exact (EQ_MP (@lem2720775) (@lem0)). Qed.
Lemma lem2720777 : term542.
Proof. exact (@lem2720766 (@lem2720776)). Qed.
Lemma lem2720779 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2720780 : term257 = term258.
Proof. exact (@lem2720779 (NUMERAL 0) term111). Qed.
Lemma lem2720781 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2720782 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2720783 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2720782 h1) (fun h1 : term258 = True => @lem2720781)). Qed.
Lemma lem2720784 : term258 = True.
Proof. exact (EQ_MP (@lem2720783) (@lem2720781)). Qed.
Lemma lem2720785 : term257 = True.
Proof. exact (TRANS (@lem2720780) (@lem2720784)). Qed.
Lemma lem2720786 : True = term257.
Proof. exact (SYM (@lem2720785)). Qed.
Lemma lem2720787 : term257.
Proof. exact (EQ_MP (@lem2720786) (@lem0)). Qed.
Lemma lem2720788 : term540 = term543.
Proof. exact (@lem2720777 (@lem2720787)). Qed.
Lemma lem2720790 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2720791 : term544 = term545.
Proof. exact (@lem2720790 term288 term111). Qed.
Lemma lem2720792 : term294 = term286.
Proof. exact (@lem996237 term286). Qed.
Lemma lem2720793 : (term294 = term286) = (term295 = term288).
Proof. exact (@lem1007663 term286 (BIT1 0) term286). Qed.
Lemma lem2720794 : term295 = term288.
Proof. exact (EQ_MP (@lem2720793) (@lem2720792)). Qed.
Lemma lem2720795 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2720796 : term293 = term279.
Proof. exact (MK_COMB (@lem2720795) (@lem2720794)). Qed.
Lemma lem2720797 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2720798 : term545 = term308.
Proof. exact (MK_COMB (@lem2720797) (@lem2720796)). Qed.
Lemma lem2720799 : term544 = term308.
Proof. exact (TRANS (@lem2720791) (@lem2720798)). Qed.
Lemma lem2720801 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2720802 : term269 = term107.
Proof. exact (@lem2720801 term111). Qed.
Lemma lem2720803 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2720804 : term488 = term482.
Proof. exact (MK_COMB (@lem2720803) (@lem2720802)). Qed.
Lemma lem2720805 : term543 = term539.
Proof. exact (MK_COMB (@lem2720804) (@lem2720799)). Qed.
Lemma lem2720807 (m : nat) (n : nat) : (term489 m n) = (term490 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2720808 : term539 = term546.
Proof. exact (@lem2720807 (NUMERAL 0) term288). Qed.
Lemma lem2720809 : term547 = term286.
Proof. exact (@lem912803). Qed.
Lemma lem2720810 (h1 : term547 = term286) : (term288 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term286 h1). Qed.
Lemma lem2720811 : (term547 = term286) = ((term288 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term547 = term286 => @lem2720810 h1) (fun h1 : (term288 = (NUMERAL 0)) = False => @lem2720809)). Qed.
Lemma lem2720812 : (term288 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2720811) (@lem2720809)). Qed.
Lemma lem2720813 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2720814 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2720815 : term492 = (and True).
Proof. exact (MK_COMB (@lem2720814) (@lem2720813)). Qed.
Lemma lem2720816 : term546 = (True /\ False).
Proof. exact (MK_COMB (@lem2720815) (@lem2720812)). Qed.
Lemma lem2720818 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2720819 : term546 = False.
Proof. exact (TRANS (@lem2720816) (@lem2720818)). Qed.
Lemma lem2720820 : term539 = False.
Proof. exact (TRANS (@lem2720808) (@lem2720819)). Qed.
Lemma lem2720821 : term543 = False.
Proof. exact (TRANS (@lem2720805) (@lem2720820)). Qed.
Lemma lem2720822 : term540 = False.
Proof. exact (TRANS (@lem2720788) (@lem2720821)). Qed.
Lemma lem2720823 : term539 = False.
Proof. exact (TRANS (@lem2720765) (@lem2720822)). Qed.
Lemma lem2720824 : term538 = False.
Proof. exact (TRANS (@lem2720756) (@lem2720823)). Qed.
Lemma lem2720825 (n : int) (h1 : term579 n) : False.
Proof. exact (EQ_MP (@lem2720824) (@lem2720753 n h1)). Qed.
Lemma lem2720826 (n : int) (h1 : term580 n) : term580 n.
Proof. exact (h1). Qed.
Lemma lem2720827 (n : int) (h1 : term580 n) : term402 n.
Proof. exact (proj2 (@lem2720826 n h1)). Qed.
Lemma lem2720828 (n : int) (h1 : term580 n) : (term223 n) = term107.
Proof. exact (proj1 (@lem2720826 n h1)). Qed.
Lemma lem2720829 (n : int) (h1 : term580 n) : term315 n.
Proof. exact (proj2 (@lem2720827 n h1)). Qed.
Lemma lem2720832 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2720833 : term433 = term257.
Proof. exact (@lem2720832 term107 term110). Qed.
Lemma lem2720835 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2720836 : term110 = term214.
Proof. exact (@lem2720835 term111). Qed.
Lemma lem2720838 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2720839 : term107 = term190.
Proof. exact (@lem2720838 (NUMERAL 0)). Qed.
Lemma lem2720840 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2720841 : term434 = term435.
Proof. exact (MK_COMB (@lem2720840) (@lem2720839)). Qed.
Lemma lem2720842 : term257 = term436.
Proof. exact (MK_COMB (@lem2720841) (@lem2720836)). Qed.
Lemma lem2720843 : term437.
Proof. exact (@lem1980255 term107 term110 term110 term110). Qed.
Lemma lem2720845 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2720846 : term257 = term258.
Proof. exact (@lem2720845 (NUMERAL 0) term111). Qed.
Lemma lem2720847 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2720848 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2720849 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2720848 h1) (fun h1 : term258 = True => @lem2720847)). Qed.
Lemma lem2720850 : term258 = True.
Proof. exact (EQ_MP (@lem2720849) (@lem2720847)). Qed.
Lemma lem2720851 : term257 = True.
Proof. exact (TRANS (@lem2720846) (@lem2720850)). Qed.
Lemma lem2720852 : True = term257.
Proof. exact (SYM (@lem2720851)). Qed.
Lemma lem2720853 : term257.
Proof. exact (EQ_MP (@lem2720852) (@lem0)). Qed.
Lemma lem2720854 : term438.
Proof. exact (@lem2720843 (@lem2720853)). Qed.
Lemma lem2720856 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2720857 : term257 = term258.
Proof. exact (@lem2720856 (NUMERAL 0) term111). Qed.
Lemma lem2720858 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2720859 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2720860 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2720859 h1) (fun h1 : term258 = True => @lem2720858)). Qed.
Lemma lem2720861 : term258 = True.
Proof. exact (EQ_MP (@lem2720860) (@lem2720858)). Qed.
Lemma lem2720862 : term257 = True.
Proof. exact (TRANS (@lem2720857) (@lem2720861)). Qed.
Lemma lem2720863 : True = term257.
Proof. exact (SYM (@lem2720862)). Qed.
Lemma lem2720864 : term257.
Proof. exact (EQ_MP (@lem2720863) (@lem0)). Qed.
Lemma lem2720865 : term436 = term439.
Proof. exact (@lem2720854 (@lem2720864)). Qed.
Lemma lem2720867 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2720868 : term202 = term203.
Proof. exact (@lem2720867 term111 term111). Qed.
Lemma lem2720869 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2720870 : term205 = term111.
Proof. exact (EQ_MP (@lem2720869) (@lem940073)). Qed.
Lemma lem2720871 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2720872 : term203 = term110.
Proof. exact (MK_COMB (@lem2720871) (@lem2720870)). Qed.
Lemma lem2720873 : term202 = term110.
Proof. exact (TRANS (@lem2720868) (@lem2720872)). Qed.
Lemma lem2720875 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2720876 : term269 = term107.
Proof. exact (@lem2720875 term111). Qed.
Lemma lem2720877 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2720878 : term440 = term434.
Proof. exact (MK_COMB (@lem2720877) (@lem2720876)). Qed.
Lemma lem2720879 : term439 = term257.
Proof. exact (MK_COMB (@lem2720878) (@lem2720873)). Qed.
Lemma lem2720881 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2720882 : term257 = term258.
Proof. exact (@lem2720881 (NUMERAL 0) term111). Qed.
Lemma lem2720883 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2720884 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2720885 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2720884 h1) (fun h1 : term258 = True => @lem2720883)). Qed.
Lemma lem2720886 : term258 = True.
Proof. exact (EQ_MP (@lem2720885) (@lem2720883)). Qed.
Lemma lem2720887 : term257 = True.
Proof. exact (TRANS (@lem2720882) (@lem2720886)). Qed.
Lemma lem2720888 : term439 = True.
Proof. exact (TRANS (@lem2720879) (@lem2720887)). Qed.
Lemma lem2720889 : term436 = True.
Proof. exact (TRANS (@lem2720865) (@lem2720888)). Qed.
Lemma lem2720890 : term257 = True.
Proof. exact (TRANS (@lem2720842) (@lem2720889)). Qed.
Lemma lem2720891 : term433 = True.
Proof. exact (TRANS (@lem2720833) (@lem2720890)). Qed.
Lemma lem2720892 : True = term433.
Proof. exact (SYM (@lem2720891)). Qed.
Lemma lem2720893 : term433.
Proof. exact (EQ_MP (@lem2720892) (@lem0)). Qed.
Lemma lem2720894 (n : int) (h1 : term580 n) : term525 n.
Proof. exact (conj (@lem2720893) (@lem2720829 n h1)). Qed.
Lemma lem2720896 (x : real) (y : real) : term442 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2720897 (n : int) : term526 n.
Proof. exact (@lem2720896 term110 (term312 n)). Qed.
Lemma lem2720898 (n : int) (h1 : term580 n) : term527 n.
Proof. exact (@lem2720897 n (@lem2720894 n h1)). Qed.
Lemma lem2720899 (n : int) : (term528 n) = (term312 n).
Proof. exact (@lem1982733 (term312 n)). Qed.
Lemma lem2720900 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2720901 (n : int) : (term529 n) = (term314 n).
Proof. exact (MK_COMB (@lem2720900) (@lem2720899 n)). Qed.
Lemma lem2720902 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2720903 (n : int) : (term527 n) = (term315 n).
Proof. exact (MK_COMB (@lem2720901 n) (@lem2720902)). Qed.
Lemma lem2720904 (n : int) (h1 : term580 n) : term315 n.
Proof. exact (EQ_MP (@lem2720903 n) (@lem2720898 n h1)). Qed.
Lemma lem2720906 (y : real) : term447 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2720907 (n : int) : term499 n.
Proof. exact (@lem2720906 (term223 n)). Qed.
Lemma lem2720908 (n : int) (h1 : term580 n) : term500 n.
Proof. exact (@lem2720907 n (@lem2720828 n h1)). Qed.
Lemma lem2720909 (n : int) (h1 : term580 n) : term549 n.
Proof. exact (@lem2720908 n h1 term193). Qed.
Lemma lem2720910 (n : int) : (term549 n) = ((term550 n) = term107).
Proof. exact (eq_refl (term549 n)). Qed.
Lemma lem2720911 (n : int) (h1 : term580 n) : (term550 n) = term107.
Proof. exact (EQ_MP (@lem2720910 n) (@lem2720909 n h1)). Qed.
Lemma lem2720912 (n : int) : (term550 n) = (term551 n).
Proof. exact (@lem1982781 (term104 n) term193 term193). Qed.
Lemma lem2720914 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2720915 : term193 = term194.
Proof. exact (@lem2720914 term111). Qed.
Lemma lem2720917 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2720918 : term193 = term194.
Proof. exact (@lem2720917 term111). Qed.
Lemma lem2720919 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2720920 : term195 = term196.
Proof. exact (MK_COMB (@lem2720919) (@lem2720918)). Qed.
Lemma lem2720921 : term552 = term553.
Proof. exact (MK_COMB (@lem2720920) (@lem2720915)). Qed.
Lemma lem2720922 : term553 = term554.
Proof. exact (@lem1981613 term193 term193 term110 term110). Qed.
Lemma lem2720924 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2720925 : term202 = term203.
Proof. exact (@lem2720924 term111 term111). Qed.
Lemma lem2720926 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2720927 : term205 = term111.
Proof. exact (EQ_MP (@lem2720926) (@lem940073)). Qed.
Lemma lem2720928 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2720929 : term203 = term110.
Proof. exact (MK_COMB (@lem2720928) (@lem2720927)). Qed.
Lemma lem2720930 : term202 = term110.
Proof. exact (TRANS (@lem2720925) (@lem2720929)). Qed.
Lemma lem2720932 (m : nat) (n : nat) : (term555 m n) = (term201 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2720933 : term552 = term203.
Proof. exact (@lem2720932 term111 term111). Qed.
Lemma lem2720934 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2720935 : term205 = term111.
Proof. exact (EQ_MP (@lem2720934) (@lem940073)). Qed.
Lemma lem2720936 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2720937 : term203 = term110.
Proof. exact (MK_COMB (@lem2720936) (@lem2720935)). Qed.
Lemma lem2720938 : term552 = term110.
Proof. exact (TRANS (@lem2720933) (@lem2720937)). Qed.
Lemma lem2720939 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2720940 : term556 = term557.
Proof. exact (MK_COMB (@lem2720939) (@lem2720938)). Qed.
Lemma lem2720941 : term554 = term214.
Proof. exact (MK_COMB (@lem2720940) (@lem2720930)). Qed.
Lemma lem2720942 : term553 = term214.
Proof. exact (TRANS (@lem2720922) (@lem2720941)). Qed.
Lemma lem2720943 : term552 = term214.
Proof. exact (TRANS (@lem2720921) (@lem2720942)). Qed.
Lemma lem2720945 (x : real) : (term209 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2720946 : term214 = term110.
Proof. exact (@lem2720945 term110). Qed.
Lemma lem2720947 : term552 = term110.
Proof. exact (TRANS (@lem2720943) (@lem2720946)). Qed.
Lemma lem2720950 (n : int) : (term232 n) = (term232 n).
Proof. exact (eq_refl (term232 n)). Qed.
Lemma lem2720951 (n : int) : (term551 n) = (term558 n).
Proof. exact (MK_COMB (@lem2720950 n) (@lem2720947)). Qed.
Lemma lem2720952 (n : int) : (term550 n) = (term558 n).
Proof. exact (TRANS (@lem2720912 n) (@lem2720951 n)). Qed.
Lemma lem2720953 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2720954 (n : int) : (term559 n) = (term560 n).
Proof. exact (MK_COMB (@lem2720953) (@lem2720952 n)). Qed.
Lemma lem2720955 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2720956 (n : int) : ((term550 n) = term107) = ((term558 n) = term107).
Proof. exact (MK_COMB (@lem2720954 n) (@lem2720955)). Qed.
Lemma lem2720957 (n : int) (h1 : term580 n) : (term558 n) = term107.
Proof. exact (EQ_MP (@lem2720956 n) (@lem2720911 n h1)). Qed.
Lemma lem2720958 (n : int) (h1 : term580 n) : term561 n.
Proof. exact (conj (@lem2720957 n h1) (@lem2720904 n h1)). Qed.
Lemma lem2720960 (x : real) (y : real) : term454 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2720961 (n : int) : term562 n.
Proof. exact (@lem2720960 (term558 n) (term312 n)). Qed.
Lemma lem2720962 (n : int) (h1 : term580 n) : term563 n.
Proof. exact (@lem2720961 n (@lem2720958 n h1)). Qed.
Lemma lem2720963 (n : int) : (term564 n) = (term565 n).
Proof. exact (@lem1982753 (term251 n) (term104 n) term110 term308). Qed.
Lemma lem2720964 (n : int) : (term520 n) = (term460 n).
Proof. exact (@lem1982713 term193 (term104 n)). Qed.
Lemma lem2720966 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2720967 : term110 = term214.
Proof. exact (@lem2720966 term111). Qed.
Lemma lem2720969 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2720970 : term193 = term194.
Proof. exact (@lem2720969 term111). Qed.
Lemma lem2720971 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2720972 : term461 = term462.
Proof. exact (MK_COMB (@lem2720971) (@lem2720970)). Qed.
Lemma lem2720973 : term463 = term464.
Proof. exact (MK_COMB (@lem2720972) (@lem2720967)). Qed.
Lemma lem2720974 : term465.
Proof. exact (@lem1981473 term193 term110 term110 term110 term107 term110). Qed.
Lemma lem2720976 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2720977 : term257 = term258.
Proof. exact (@lem2720976 (NUMERAL 0) term111). Qed.
Lemma lem2720978 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2720979 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2720980 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2720979 h1) (fun h1 : term258 = True => @lem2720978)). Qed.
Lemma lem2720981 : term258 = True.
Proof. exact (EQ_MP (@lem2720980) (@lem2720978)). Qed.
Lemma lem2720982 : term257 = True.
Proof. exact (TRANS (@lem2720977) (@lem2720981)). Qed.
Lemma lem2720983 : True = term257.
Proof. exact (SYM (@lem2720982)). Qed.
Lemma lem2720984 : term257.
Proof. exact (EQ_MP (@lem2720983) (@lem0)). Qed.
Lemma lem2720985 : term466.
Proof. exact (@lem2720974 (@lem2720984)). Qed.
Lemma lem2720987 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2720988 : term257 = term258.
Proof. exact (@lem2720987 (NUMERAL 0) term111). Qed.
Lemma lem2720989 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2720990 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2720991 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2720990 h1) (fun h1 : term258 = True => @lem2720989)). Qed.
Lemma lem2720992 : term258 = True.
Proof. exact (EQ_MP (@lem2720991) (@lem2720989)). Qed.
Lemma lem2720993 : term257 = True.
Proof. exact (TRANS (@lem2720988) (@lem2720992)). Qed.
Lemma lem2720994 : True = term257.
Proof. exact (SYM (@lem2720993)). Qed.
Lemma lem2720995 : term257.
Proof. exact (EQ_MP (@lem2720994) (@lem0)). Qed.
Lemma lem2720996 : term467.
Proof. exact (@lem2720985 (@lem2720995)). Qed.
Lemma lem2720998 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2720999 : term257 = term258.
Proof. exact (@lem2720998 (NUMERAL 0) term111). Qed.
Lemma lem2721000 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2721001 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2721002 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2721001 h1) (fun h1 : term258 = True => @lem2721000)). Qed.
Lemma lem2721003 : term258 = True.
Proof. exact (EQ_MP (@lem2721002) (@lem2721000)). Qed.
Lemma lem2721004 : term257 = True.
Proof. exact (TRANS (@lem2720999) (@lem2721003)). Qed.
Lemma lem2721005 : True = term257.
Proof. exact (SYM (@lem2721004)). Qed.
Lemma lem2721006 : term257.
Proof. exact (EQ_MP (@lem2721005) (@lem0)). Qed.
Lemma lem2721007 : term468.
Proof. exact (@lem2720996 (@lem2721006)). Qed.
Lemma lem2721009 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2721010 : term202 = term203.
Proof. exact (@lem2721009 term111 term111). Qed.
Lemma lem2721011 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2721012 : term205 = term111.
Proof. exact (EQ_MP (@lem2721011) (@lem940073)). Qed.
Lemma lem2721013 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2721014 : term203 = term110.
Proof. exact (MK_COMB (@lem2721013) (@lem2721012)). Qed.
Lemma lem2721015 : term202 = term110.
Proof. exact (TRANS (@lem2721010) (@lem2721014)). Qed.
Lemma lem2721017 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2721018 : term215 = term220.
Proof. exact (@lem2721017 term111 term111). Qed.
Lemma lem2721019 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2721020 : term205 = term111.
Proof. exact (EQ_MP (@lem2721019) (@lem940073)). Qed.
Lemma lem2721021 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2721022 : term203 = term110.
Proof. exact (MK_COMB (@lem2721021) (@lem2721020)). Qed.
Lemma lem2721023 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2721024 : term220 = term193.
Proof. exact (MK_COMB (@lem2721023) (@lem2721022)). Qed.
Lemma lem2721025 : term215 = term193.
Proof. exact (TRANS (@lem2721018) (@lem2721024)). Qed.
Lemma lem2721026 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2721027 : term469 = term461.
Proof. exact (MK_COMB (@lem2721026) (@lem2721025)). Qed.
Lemma lem2721028 : term470 = term463.
Proof. exact (MK_COMB (@lem2721027) (@lem2721015)). Qed.
Lemma lem2721030 (m : nat) : (term471 m) = term107.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2721031 : term463 = term107.
Proof. exact (@lem2721030 term111). Qed.
Lemma lem2721032 : term470 = term107.
Proof. exact (TRANS (@lem2721028) (@lem2721031)). Qed.
Lemma lem2721033 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2721034 : term472 = term267.
Proof. exact (MK_COMB (@lem2721033) (@lem2721032)). Qed.
Lemma lem2721035 : term110 = term110.
Proof. exact (eq_refl term110). Qed.
Lemma lem2721036 : term473 = term269.
Proof. exact (MK_COMB (@lem2721034) (@lem2721035)). Qed.
Lemma lem2721038 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2721039 : term269 = term107.
Proof. exact (@lem2721038 term111). Qed.
Lemma lem2721040 : term473 = term107.
Proof. exact (TRANS (@lem2721036) (@lem2721039)). Qed.
Lemma lem2721042 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2721043 : term202 = term203.
Proof. exact (@lem2721042 term111 term111). Qed.
Lemma lem2721044 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2721045 : term205 = term111.
Proof. exact (EQ_MP (@lem2721044) (@lem940073)). Qed.
Lemma lem2721046 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2721047 : term203 = term110.
Proof. exact (MK_COMB (@lem2721046) (@lem2721045)). Qed.
Lemma lem2721048 : term202 = term110.
Proof. exact (TRANS (@lem2721043) (@lem2721047)). Qed.
Lemma lem2721049 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2721050 : term271 = term269.
Proof. exact (MK_COMB (@lem2721049) (@lem2721048)). Qed.
Lemma lem2721052 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2721053 : term269 = term107.
Proof. exact (@lem2721052 term111). Qed.
Lemma lem2721054 : term271 = term107.
Proof. exact (TRANS (@lem2721050) (@lem2721053)). Qed.
Lemma lem2721055 : term107 = term271.
Proof. exact (SYM (@lem2721054)). Qed.
Lemma lem2721056 : term473 = term271.
Proof. exact (TRANS (@lem2721040) (@lem2721055)). Qed.
Lemma lem2721057 : term464 = term190.
Proof. exact (@lem2721007 (@lem2721056)). Qed.
Lemma lem2721058 : term463 = term190.
Proof. exact (TRANS (@lem2720973) (@lem2721057)). Qed.
Lemma lem2721060 (x : real) : (term209 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2721061 : term190 = term107.
Proof. exact (@lem2721060 term107). Qed.
Lemma lem2721062 : term463 = term107.
Proof. exact (TRANS (@lem2721058) (@lem2721061)). Qed.
Lemma lem2721063 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2721064 : term474 = term267.
Proof. exact (MK_COMB (@lem2721063) (@lem2721062)). Qed.
Lemma lem2721065 (n : int) : (term104 n) = (term104 n).
Proof. exact (eq_refl (term104 n)). Qed.
Lemma lem2721066 (n : int) : (term460 n) = (term475 n).
Proof. exact (MK_COMB (@lem2721064) (@lem2721065 n)). Qed.
Lemma lem2721067 (n : int) : (term520 n) = (term475 n).
Proof. exact (TRANS (@lem2720964 n) (@lem2721066 n)). Qed.
Lemma lem2721068 (n : int) : (term475 n) = term107.
Proof. exact (@lem1982719 (term104 n)). Qed.
Lemma lem2721069 (n : int) : (term520 n) = term107.
Proof. exact (TRANS (@lem2721067 n) (@lem2721068 n)). Qed.
Lemma lem2721070 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2721071 (n : int) : (term521 n) = term139.
Proof. exact (MK_COMB (@lem2721070) (@lem2721069 n)). Qed.
Lemma lem2721073 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2721074 : term308 = term311.
Proof. exact (@lem2721073 term288). Qed.
Lemma lem2721076 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2721077 : term110 = term214.
Proof. exact (@lem2721076 term111). Qed.
Lemma lem2721078 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2721079 : term157 = term252.
Proof. exact (MK_COMB (@lem2721078) (@lem2721077)). Qed.
Lemma lem2721080 : term566 = term567.
Proof. exact (MK_COMB (@lem2721079) (@lem2721074)). Qed.
Lemma lem2721081 : term568.
Proof. exact (@lem1981473 term110 term110 term308 term110 term193 term110). Qed.
Lemma lem2721083 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2721084 : term257 = term258.
Proof. exact (@lem2721083 (NUMERAL 0) term111). Qed.
Lemma lem2721085 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2721086 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2721087 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2721086 h1) (fun h1 : term258 = True => @lem2721085)). Qed.
Lemma lem2721088 : term258 = True.
Proof. exact (EQ_MP (@lem2721087) (@lem2721085)). Qed.
Lemma lem2721089 : term257 = True.
Proof. exact (TRANS (@lem2721084) (@lem2721088)). Qed.
Lemma lem2721090 : True = term257.
Proof. exact (SYM (@lem2721089)). Qed.
Lemma lem2721091 : term257.
Proof. exact (EQ_MP (@lem2721090) (@lem0)). Qed.
Lemma lem2721092 : term569.
Proof. exact (@lem2721081 (@lem2721091)). Qed.
Lemma lem2721094 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2721095 : term257 = term258.
Proof. exact (@lem2721094 (NUMERAL 0) term111). Qed.
Lemma lem2721096 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2721097 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2721098 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2721097 h1) (fun h1 : term258 = True => @lem2721096)). Qed.
Lemma lem2721099 : term258 = True.
Proof. exact (EQ_MP (@lem2721098) (@lem2721096)). Qed.
Lemma lem2721100 : term257 = True.
Proof. exact (TRANS (@lem2721095) (@lem2721099)). Qed.
Lemma lem2721101 : True = term257.
Proof. exact (SYM (@lem2721100)). Qed.
Lemma lem2721102 : term257.
Proof. exact (EQ_MP (@lem2721101) (@lem0)). Qed.
Lemma lem2721103 : term570.
Proof. exact (@lem2721092 (@lem2721102)). Qed.
Lemma lem2721105 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2721106 : term257 = term258.
Proof. exact (@lem2721105 (NUMERAL 0) term111). Qed.
Lemma lem2721107 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2721108 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2721109 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2721108 h1) (fun h1 : term258 = True => @lem2721107)). Qed.
Lemma lem2721110 : term258 = True.
Proof. exact (EQ_MP (@lem2721109) (@lem2721107)). Qed.
Lemma lem2721111 : term257 = True.
Proof. exact (TRANS (@lem2721106) (@lem2721110)). Qed.
Lemma lem2721112 : True = term257.
Proof. exact (SYM (@lem2721111)). Qed.
Lemma lem2721113 : term257.
Proof. exact (EQ_MP (@lem2721112) (@lem0)). Qed.
Lemma lem2721114 : term571.
Proof. exact (@lem2721103 (@lem2721113)). Qed.
Lemma lem2721116 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2721117 : term544 = term545.
Proof. exact (@lem2721116 term288 term111). Qed.
Lemma lem2721118 : term294 = term286.
Proof. exact (@lem996237 term286). Qed.
Lemma lem2721119 : (term294 = term286) = (term295 = term288).
Proof. exact (@lem1007663 term286 (BIT1 0) term286). Qed.
Lemma lem2721120 : term295 = term288.
Proof. exact (EQ_MP (@lem2721119) (@lem2721118)). Qed.
Lemma lem2721121 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2721122 : term293 = term279.
Proof. exact (MK_COMB (@lem2721121) (@lem2721120)). Qed.
Lemma lem2721123 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2721124 : term545 = term308.
Proof. exact (MK_COMB (@lem2721123) (@lem2721122)). Qed.
Lemma lem2721125 : term544 = term308.
Proof. exact (TRANS (@lem2721117) (@lem2721124)). Qed.
Lemma lem2721127 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2721128 : term202 = term203.
Proof. exact (@lem2721127 term111 term111). Qed.
Lemma lem2721129 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2721130 : term205 = term111.
Proof. exact (EQ_MP (@lem2721129) (@lem940073)). Qed.
Lemma lem2721131 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2721132 : term203 = term110.
Proof. exact (MK_COMB (@lem2721131) (@lem2721130)). Qed.
Lemma lem2721133 : term202 = term110.
Proof. exact (TRANS (@lem2721128) (@lem2721132)). Qed.
Lemma lem2721134 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2721135 : term263 = term157.
Proof. exact (MK_COMB (@lem2721134) (@lem2721133)). Qed.
Lemma lem2721136 : term572 = term566.
Proof. exact (MK_COMB (@lem2721135) (@lem2721125)). Qed.
Lemma lem2721139 : term573 = term193.
Proof. exact (@lem1367771 term111 term111). Qed.
Lemma lem2721140 : term285 = term286.
Proof. exact (@lem706885). Qed.
Lemma lem2721141 : (term285 = term286) = (term287 = term288).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term286). Qed.
Lemma lem2721142 : term287 = term288.
Proof. exact (EQ_MP (@lem2721141) (@lem2721140)). Qed.
Lemma lem2721143 : term288 = term287.
Proof. exact (SYM (@lem2721142)). Qed.
Lemma lem2721144 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2721145 : term279 = term284.
Proof. exact (MK_COMB (@lem2721144) (@lem2721143)). Qed.
Lemma lem2721146 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2721147 : term308 = term574.
Proof. exact (MK_COMB (@lem2721146) (@lem2721145)). Qed.
Lemma lem2721148 : term157 = term157.
Proof. exact (eq_refl term157). Qed.
Lemma lem2721149 : term566 = term573.
Proof. exact (MK_COMB (@lem2721148) (@lem2721147)). Qed.
Lemma lem2721150 : term566 = term193.
Proof. exact (TRANS (@lem2721149) (@lem2721139)). Qed.
Lemma lem2721151 : term572 = term193.
Proof. exact (TRANS (@lem2721136) (@lem2721150)). Qed.
Lemma lem2721152 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2721153 : term575 = term195.
Proof. exact (MK_COMB (@lem2721152) (@lem2721151)). Qed.
Lemma lem2721154 : term110 = term110.
Proof. exact (eq_refl term110). Qed.
Lemma lem2721155 : term576 = term215.
Proof. exact (MK_COMB (@lem2721153) (@lem2721154)). Qed.
Lemma lem2721157 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2721158 : term215 = term220.
Proof. exact (@lem2721157 term111 term111). Qed.
Lemma lem2721159 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2721160 : term205 = term111.
Proof. exact (EQ_MP (@lem2721159) (@lem940073)). Qed.
Lemma lem2721161 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2721162 : term203 = term110.
Proof. exact (MK_COMB (@lem2721161) (@lem2721160)). Qed.
Lemma lem2721163 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2721164 : term220 = term193.
Proof. exact (MK_COMB (@lem2721163) (@lem2721162)). Qed.
Lemma lem2721165 : term215 = term193.
Proof. exact (TRANS (@lem2721158) (@lem2721164)). Qed.
Lemma lem2721166 : term576 = term193.
Proof. exact (TRANS (@lem2721155) (@lem2721165)). Qed.
Lemma lem2721168 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2721169 : term202 = term203.
Proof. exact (@lem2721168 term111 term111). Qed.
Lemma lem2721170 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2721171 : term205 = term111.
Proof. exact (EQ_MP (@lem2721170) (@lem940073)). Qed.
Lemma lem2721172 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2721173 : term203 = term110.
Proof. exact (MK_COMB (@lem2721172) (@lem2721171)). Qed.
Lemma lem2721174 : term202 = term110.
Proof. exact (TRANS (@lem2721169) (@lem2721173)). Qed.
Lemma lem2721175 : term195 = term195.
Proof. exact (eq_refl term195). Qed.
Lemma lem2721176 : term577 = term215.
Proof. exact (MK_COMB (@lem2721175) (@lem2721174)). Qed.
Lemma lem2721178 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2721179 : term215 = term220.
Proof. exact (@lem2721178 term111 term111). Qed.
Lemma lem2721180 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2721181 : term205 = term111.
Proof. exact (EQ_MP (@lem2721180) (@lem940073)). Qed.
Lemma lem2721182 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2721183 : term203 = term110.
Proof. exact (MK_COMB (@lem2721182) (@lem2721181)). Qed.
Lemma lem2721184 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2721185 : term220 = term193.
Proof. exact (MK_COMB (@lem2721184) (@lem2721183)). Qed.
Lemma lem2721186 : term215 = term193.
Proof. exact (TRANS (@lem2721179) (@lem2721185)). Qed.
Lemma lem2721187 : term577 = term193.
Proof. exact (TRANS (@lem2721176) (@lem2721186)). Qed.
Lemma lem2721188 : term193 = term577.
Proof. exact (SYM (@lem2721187)). Qed.
Lemma lem2721189 : term576 = term577.
Proof. exact (TRANS (@lem2721166) (@lem2721188)). Qed.
Lemma lem2721190 : term567 = term194.
Proof. exact (@lem2721114 (@lem2721189)). Qed.
Lemma lem2721191 : term566 = term194.
Proof. exact (TRANS (@lem2721080) (@lem2721190)). Qed.
Lemma lem2721193 (x : real) : (term209 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2721194 : term194 = term193.
Proof. exact (@lem2721193 term193). Qed.
Lemma lem2721195 : term566 = term193.
Proof. exact (TRANS (@lem2721191) (@lem2721194)). Qed.
Lemma lem2721196 (n : int) : (term565 n) = term477.
Proof. exact (MK_COMB (@lem2721071 n) (@lem2721195)). Qed.
Lemma lem2721197 (n : int) : (term564 n) = term477.
Proof. exact (TRANS (@lem2720963 n) (@lem2721196 n)). Qed.
Lemma lem2721198 : term477 = term193.
Proof. exact (@lem1982721 term193). Qed.
Lemma lem2721199 (n : int) : (term564 n) = term193.
Proof. exact (TRANS (@lem2721197 n) (@lem2721198)). Qed.
Lemma lem2721200 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2721201 (n : int) : (term578 n) = term479.
Proof. exact (MK_COMB (@lem2721200) (@lem2721199 n)). Qed.
Lemma lem2721202 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2721203 (n : int) : (term563 n) = term480.
Proof. exact (MK_COMB (@lem2721201 n) (@lem2721202)). Qed.
Lemma lem2721204 (n : int) (h1 : term580 n) : term480.
Proof. exact (EQ_MP (@lem2721203 n) (@lem2720962 n h1)). Qed.
Lemma lem2721206 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2721207 : term480 = term481.
Proof. exact (@lem2721206 term107 term193). Qed.
Lemma lem2721209 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2721210 : term193 = term194.
Proof. exact (@lem2721209 term111). Qed.
Lemma lem2721212 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2721213 : term107 = term190.
Proof. exact (@lem2721212 (NUMERAL 0)). Qed.
Lemma lem2721214 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2721215 : term482 = term483.
Proof. exact (MK_COMB (@lem2721214) (@lem2721213)). Qed.
Lemma lem2721216 : term481 = term484.
Proof. exact (MK_COMB (@lem2721215) (@lem2721210)). Qed.
Lemma lem2721217 : term485.
Proof. exact (@lem1980026 term107 term110 term193 term110). Qed.
Lemma lem2721219 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2721220 : term257 = term258.
Proof. exact (@lem2721219 (NUMERAL 0) term111). Qed.
Lemma lem2721221 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2721222 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2721223 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2721222 h1) (fun h1 : term258 = True => @lem2721221)). Qed.
Lemma lem2721224 : term258 = True.
Proof. exact (EQ_MP (@lem2721223) (@lem2721221)). Qed.
Lemma lem2721225 : term257 = True.
Proof. exact (TRANS (@lem2721220) (@lem2721224)). Qed.
Lemma lem2721226 : True = term257.
Proof. exact (SYM (@lem2721225)). Qed.
Lemma lem2721227 : term257.
Proof. exact (EQ_MP (@lem2721226) (@lem0)). Qed.
Lemma lem2721228 : term486.
Proof. exact (@lem2721217 (@lem2721227)). Qed.
Lemma lem2721230 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2721231 : term257 = term258.
Proof. exact (@lem2721230 (NUMERAL 0) term111). Qed.
Lemma lem2721232 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2721233 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2721234 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2721233 h1) (fun h1 : term258 = True => @lem2721232)). Qed.
Lemma lem2721235 : term258 = True.
Proof. exact (EQ_MP (@lem2721234) (@lem2721232)). Qed.
Lemma lem2721236 : term257 = True.
Proof. exact (TRANS (@lem2721231) (@lem2721235)). Qed.
Lemma lem2721237 : True = term257.
Proof. exact (SYM (@lem2721236)). Qed.
Lemma lem2721238 : term257.
Proof. exact (EQ_MP (@lem2721237) (@lem0)). Qed.
Lemma lem2721239 : term484 = term487.
Proof. exact (@lem2721228 (@lem2721238)). Qed.
Lemma lem2721241 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2721242 : term215 = term220.
Proof. exact (@lem2721241 term111 term111). Qed.
Lemma lem2721243 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2721244 : term205 = term111.
Proof. exact (EQ_MP (@lem2721243) (@lem940073)). Qed.
Lemma lem2721245 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2721246 : term203 = term110.
Proof. exact (MK_COMB (@lem2721245) (@lem2721244)). Qed.
Lemma lem2721247 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2721248 : term220 = term193.
Proof. exact (MK_COMB (@lem2721247) (@lem2721246)). Qed.
Lemma lem2721249 : term215 = term193.
Proof. exact (TRANS (@lem2721242) (@lem2721248)). Qed.
Lemma lem2721251 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2721252 : term269 = term107.
Proof. exact (@lem2721251 term111). Qed.
Lemma lem2721253 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2721254 : term488 = term482.
Proof. exact (MK_COMB (@lem2721253) (@lem2721252)). Qed.
Lemma lem2721255 : term487 = term481.
Proof. exact (MK_COMB (@lem2721254) (@lem2721249)). Qed.
Lemma lem2721257 (m : nat) (n : nat) : (term489 m n) = (term490 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2721258 : term481 = term491.
Proof. exact (@lem2721257 (NUMERAL 0) term111). Qed.
Lemma lem2721259 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2721260 (h1 : term259 = (BIT1 0)) : (term111 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2721261 : (term259 = (BIT1 0)) = ((term111 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2721260 h1) (fun h1 : (term111 = (NUMERAL 0)) = False => @lem2721259)). Qed.
Lemma lem2721262 : (term111 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2721261) (@lem2721259)). Qed.
Lemma lem2721263 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2721264 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2721265 : term492 = (and True).
Proof. exact (MK_COMB (@lem2721264) (@lem2721263)). Qed.
Lemma lem2721266 : term491 = (True /\ False).
Proof. exact (MK_COMB (@lem2721265) (@lem2721262)). Qed.
Lemma lem2721268 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2721269 : term491 = False.
Proof. exact (TRANS (@lem2721266) (@lem2721268)). Qed.
Lemma lem2721270 : term481 = False.
Proof. exact (TRANS (@lem2721258) (@lem2721269)). Qed.
Lemma lem2721271 : term487 = False.
Proof. exact (TRANS (@lem2721255) (@lem2721270)). Qed.
Lemma lem2721272 : term484 = False.
Proof. exact (TRANS (@lem2721239) (@lem2721271)). Qed.
Lemma lem2721273 : term481 = False.
Proof. exact (TRANS (@lem2721216) (@lem2721272)). Qed.
Lemma lem2721274 : term480 = False.
Proof. exact (TRANS (@lem2721207) (@lem2721273)). Qed.
Lemma lem2721275 (n : int) (h1 : term580 n) : False.
Proof. exact (EQ_MP (@lem2721274) (@lem2721204 n h1)). Qed.
Lemma lem2721276 (n : int) (h1 : term404 n) : False.
Proof. exact (or_elim (@lem2720537 n h1) (fun h0 : term579 n => @lem2720825 n h0) (fun h0 : term580 n => @lem2721275 n h0)). Qed.
Lemma lem2721277 (n : int) (h1 : term409 n) : False.
Proof. exact (or_elim (@lem2719796 n h1) (fun h0 : term406 n => @lem2720536 n h0) (fun h0 : term404 n => @lem2721276 n h0)). Qed.
Lemma lem2721278 (n : int) (h1 : term423 n) : False.
Proof. exact (or_elim (@lem2718641 n h1) (fun h0 : term420 n => @lem2719795 n h0) (fun h0 : term409 n => @lem2721277 n h0)). Qed.
Lemma lem2721279 (n : int) (h1 : term396 n) : term396 n.
Proof. exact (h1). Qed.
Lemma lem2721280 (n : int) (h1 : term581 n) : term581 n.
Proof. exact (h1). Qed.
Lemma lem2721281 (n : int) (h1 : term581 n) : term320 n.
Proof. exact (proj2 (@lem2721280 n h1)). Qed.
Lemma lem2721283 (n : int) (h1 : term581 n) : (term223 n) = term107.
Proof. exact (proj2 (@lem2721281 n h1)). Qed.
Lemma lem2721284 (n : int) (h1 : term581 n) : (term104 n) = term107.
Proof. exact (proj1 (@lem2721281 n h1)). Qed.
Lemma lem2721286 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2721287 : term433 = term257.
Proof. exact (@lem2721286 term107 term110). Qed.
Lemma lem2721289 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2721290 : term110 = term214.
Proof. exact (@lem2721289 term111). Qed.
Lemma lem2721292 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2721293 : term107 = term190.
Proof. exact (@lem2721292 (NUMERAL 0)). Qed.
Lemma lem2721294 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2721295 : term434 = term435.
Proof. exact (MK_COMB (@lem2721294) (@lem2721293)). Qed.
Lemma lem2721296 : term257 = term436.
Proof. exact (MK_COMB (@lem2721295) (@lem2721290)). Qed.
Lemma lem2721297 : term437.
Proof. exact (@lem1980255 term107 term110 term110 term110). Qed.
Lemma lem2721299 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2721300 : term257 = term258.
Proof. exact (@lem2721299 (NUMERAL 0) term111). Qed.
Lemma lem2721301 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2721302 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2721303 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2721302 h1) (fun h1 : term258 = True => @lem2721301)). Qed.
Lemma lem2721304 : term258 = True.
Proof. exact (EQ_MP (@lem2721303) (@lem2721301)). Qed.
Lemma lem2721305 : term257 = True.
Proof. exact (TRANS (@lem2721300) (@lem2721304)). Qed.
Lemma lem2721306 : True = term257.
Proof. exact (SYM (@lem2721305)). Qed.
Lemma lem2721307 : term257.
Proof. exact (EQ_MP (@lem2721306) (@lem0)). Qed.
Lemma lem2721308 : term438.
Proof. exact (@lem2721297 (@lem2721307)). Qed.
Lemma lem2721310 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2721311 : term257 = term258.
Proof. exact (@lem2721310 (NUMERAL 0) term111). Qed.
Lemma lem2721312 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2721313 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2721314 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2721313 h1) (fun h1 : term258 = True => @lem2721312)). Qed.
Lemma lem2721315 : term258 = True.
Proof. exact (EQ_MP (@lem2721314) (@lem2721312)). Qed.
Lemma lem2721316 : term257 = True.
Proof. exact (TRANS (@lem2721311) (@lem2721315)). Qed.
Lemma lem2721317 : True = term257.
Proof. exact (SYM (@lem2721316)). Qed.
Lemma lem2721318 : term257.
Proof. exact (EQ_MP (@lem2721317) (@lem0)). Qed.
Lemma lem2721319 : term436 = term439.
Proof. exact (@lem2721308 (@lem2721318)). Qed.
Lemma lem2721321 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2721322 : term202 = term203.
Proof. exact (@lem2721321 term111 term111). Qed.
Lemma lem2721323 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2721324 : term205 = term111.
Proof. exact (EQ_MP (@lem2721323) (@lem940073)). Qed.
Lemma lem2721325 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2721326 : term203 = term110.
Proof. exact (MK_COMB (@lem2721325) (@lem2721324)). Qed.
Lemma lem2721327 : term202 = term110.
Proof. exact (TRANS (@lem2721322) (@lem2721326)). Qed.
Lemma lem2721329 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2721330 : term269 = term107.
Proof. exact (@lem2721329 term111). Qed.
Lemma lem2721331 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2721332 : term440 = term434.
Proof. exact (MK_COMB (@lem2721331) (@lem2721330)). Qed.
Lemma lem2721333 : term439 = term257.
Proof. exact (MK_COMB (@lem2721332) (@lem2721327)). Qed.
Lemma lem2721335 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2721336 : term257 = term258.
Proof. exact (@lem2721335 (NUMERAL 0) term111). Qed.
Lemma lem2721337 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2721338 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2721339 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2721338 h1) (fun h1 : term258 = True => @lem2721337)). Qed.
Lemma lem2721340 : term258 = True.
Proof. exact (EQ_MP (@lem2721339) (@lem2721337)). Qed.
Lemma lem2721341 : term257 = True.
Proof. exact (TRANS (@lem2721336) (@lem2721340)). Qed.
Lemma lem2721342 : term439 = True.
Proof. exact (TRANS (@lem2721333) (@lem2721341)). Qed.
Lemma lem2721343 : term436 = True.
Proof. exact (TRANS (@lem2721319) (@lem2721342)). Qed.
Lemma lem2721344 : term257 = True.
Proof. exact (TRANS (@lem2721296) (@lem2721343)). Qed.
Lemma lem2721345 : term433 = True.
Proof. exact (TRANS (@lem2721287) (@lem2721344)). Qed.
Lemma lem2721346 : True = term433.
Proof. exact (SYM (@lem2721345)). Qed.
Lemma lem2721347 : term433.
Proof. exact (EQ_MP (@lem2721346) (@lem0)). Qed.
Lemma lem2721348 (n : int) (h1 : term581 n) : term582 n.
Proof. exact (conj (@lem2721347) (@lem2721284 n h1)). Qed.
Lemma lem2721350 (x : real) (y : real) : term583 x y.
Proof. exact (proj1 (@lem1988330 x y)). Qed.
Lemma lem2721351 (n : int) : term584 n.
Proof. exact (@lem2721350 term110 (term104 n)). Qed.
Lemma lem2721352 (n : int) (h1 : term581 n) : (term451 n) = term107.
Proof. exact (@lem2721351 n (@lem2721348 n h1)). Qed.
Lemma lem2721353 (n : int) : (term451 n) = (term104 n).
Proof. exact (@lem1982733 (term104 n)). Qed.
Lemma lem2721354 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2721355 (n : int) : (term452 n) = (term108 n).
Proof. exact (MK_COMB (@lem2721354) (@lem2721353 n)). Qed.
Lemma lem2721356 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2721357 (n : int) : ((term451 n) = term107) = ((term104 n) = term107).
Proof. exact (MK_COMB (@lem2721355 n) (@lem2721356)). Qed.
Lemma lem2721358 (n : int) (h1 : term581 n) : (term104 n) = term107.
Proof. exact (EQ_MP (@lem2721357 n) (@lem2721352 n h1)). Qed.
Lemma lem2721360 (y : real) : term447 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2721361 (n : int) : term499 n.
Proof. exact (@lem2721360 (term223 n)). Qed.
Lemma lem2721362 (n : int) (h1 : term581 n) : term500 n.
Proof. exact (@lem2721361 n (@lem2721283 n h1)). Qed.
Lemma lem2721363 (n : int) (h1 : term581 n) : term549 n.
Proof. exact (@lem2721362 n h1 term193). Qed.
Lemma lem2721364 (n : int) : (term549 n) = ((term550 n) = term107).
Proof. exact (eq_refl (term549 n)). Qed.
Lemma lem2721365 (n : int) (h1 : term581 n) : (term550 n) = term107.
Proof. exact (EQ_MP (@lem2721364 n) (@lem2721363 n h1)). Qed.
Lemma lem2721366 (n : int) : (term550 n) = (term551 n).
Proof. exact (@lem1982781 (term104 n) term193 term193). Qed.
Lemma lem2721368 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2721369 : term193 = term194.
Proof. exact (@lem2721368 term111). Qed.
Lemma lem2721371 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2721372 : term193 = term194.
Proof. exact (@lem2721371 term111). Qed.
Lemma lem2721373 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2721374 : term195 = term196.
Proof. exact (MK_COMB (@lem2721373) (@lem2721372)). Qed.
Lemma lem2721375 : term552 = term553.
Proof. exact (MK_COMB (@lem2721374) (@lem2721369)). Qed.
Lemma lem2721376 : term553 = term554.
Proof. exact (@lem1981613 term193 term193 term110 term110). Qed.
Lemma lem2721378 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2721379 : term202 = term203.
Proof. exact (@lem2721378 term111 term111). Qed.
Lemma lem2721380 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2721381 : term205 = term111.
Proof. exact (EQ_MP (@lem2721380) (@lem940073)). Qed.
Lemma lem2721382 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2721383 : term203 = term110.
Proof. exact (MK_COMB (@lem2721382) (@lem2721381)). Qed.
Lemma lem2721384 : term202 = term110.
Proof. exact (TRANS (@lem2721379) (@lem2721383)). Qed.
Lemma lem2721386 (m : nat) (n : nat) : (term555 m n) = (term201 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2721387 : term552 = term203.
Proof. exact (@lem2721386 term111 term111). Qed.
Lemma lem2721388 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2721389 : term205 = term111.
Proof. exact (EQ_MP (@lem2721388) (@lem940073)). Qed.
Lemma lem2721390 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2721391 : term203 = term110.
Proof. exact (MK_COMB (@lem2721390) (@lem2721389)). Qed.
Lemma lem2721392 : term552 = term110.
Proof. exact (TRANS (@lem2721387) (@lem2721391)). Qed.
Lemma lem2721393 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2721394 : term556 = term557.
Proof. exact (MK_COMB (@lem2721393) (@lem2721392)). Qed.
Lemma lem2721395 : term554 = term214.
Proof. exact (MK_COMB (@lem2721394) (@lem2721384)). Qed.
Lemma lem2721396 : term553 = term214.
Proof. exact (TRANS (@lem2721376) (@lem2721395)). Qed.
Lemma lem2721397 : term552 = term214.
Proof. exact (TRANS (@lem2721375) (@lem2721396)). Qed.
Lemma lem2721399 (x : real) : (term209 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2721400 : term214 = term110.
Proof. exact (@lem2721399 term110). Qed.
Lemma lem2721401 : term552 = term110.
Proof. exact (TRANS (@lem2721397) (@lem2721400)). Qed.
Lemma lem2721404 (n : int) : (term232 n) = (term232 n).
Proof. exact (eq_refl (term232 n)). Qed.
Lemma lem2721405 (n : int) : (term551 n) = (term558 n).
Proof. exact (MK_COMB (@lem2721404 n) (@lem2721401)). Qed.
Lemma lem2721406 (n : int) : (term550 n) = (term558 n).
Proof. exact (TRANS (@lem2721366 n) (@lem2721405 n)). Qed.
Lemma lem2721407 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2721408 (n : int) : (term559 n) = (term560 n).
Proof. exact (MK_COMB (@lem2721407) (@lem2721406 n)). Qed.
Lemma lem2721409 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2721410 (n : int) : ((term550 n) = term107) = ((term558 n) = term107).
Proof. exact (MK_COMB (@lem2721408 n) (@lem2721409)). Qed.
Lemma lem2721411 (n : int) (h1 : term581 n) : (term558 n) = term107.
Proof. exact (EQ_MP (@lem2721410 n) (@lem2721365 n h1)). Qed.
Lemma lem2721412 (n : int) (h1 : term581 n) : term585 n.
Proof. exact (conj (@lem2721411 n h1) (@lem2721358 n h1)). Qed.
Lemma lem2721414 (x : real) (y : real) : term586 x y.
Proof. exact (proj1 (@lem1393126 x y)). Qed.
Lemma lem2721415 (n : int) : term587 n.
Proof. exact (@lem2721414 (term558 n) (term104 n)). Qed.
Lemma lem2721416 (n : int) (h1 : term581 n) : (term588 n) = term107.
Proof. exact (@lem2721415 n (@lem2721412 n h1)). Qed.
Lemma lem2721417 (n : int) : (term588 n) = (term589 n).
Proof. exact (@lem1982759 (term251 n) (term104 n) term110). Qed.
Lemma lem2721418 (n : int) : (term520 n) = (term460 n).
Proof. exact (@lem1982713 term193 (term104 n)). Qed.
Lemma lem2721420 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2721421 : term110 = term214.
Proof. exact (@lem2721420 term111). Qed.
Lemma lem2721423 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2721424 : term193 = term194.
Proof. exact (@lem2721423 term111). Qed.
Lemma lem2721425 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2721426 : term461 = term462.
Proof. exact (MK_COMB (@lem2721425) (@lem2721424)). Qed.
Lemma lem2721427 : term463 = term464.
Proof. exact (MK_COMB (@lem2721426) (@lem2721421)). Qed.
Lemma lem2721428 : term465.
Proof. exact (@lem1981473 term193 term110 term110 term110 term107 term110). Qed.
Lemma lem2721430 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2721431 : term257 = term258.
Proof. exact (@lem2721430 (NUMERAL 0) term111). Qed.
Lemma lem2721432 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2721433 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2721434 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2721433 h1) (fun h1 : term258 = True => @lem2721432)). Qed.
Lemma lem2721435 : term258 = True.
Proof. exact (EQ_MP (@lem2721434) (@lem2721432)). Qed.
Lemma lem2721436 : term257 = True.
Proof. exact (TRANS (@lem2721431) (@lem2721435)). Qed.
Lemma lem2721437 : True = term257.
Proof. exact (SYM (@lem2721436)). Qed.
Lemma lem2721438 : term257.
Proof. exact (EQ_MP (@lem2721437) (@lem0)). Qed.
Lemma lem2721439 : term466.
Proof. exact (@lem2721428 (@lem2721438)). Qed.
Lemma lem2721441 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2721442 : term257 = term258.
Proof. exact (@lem2721441 (NUMERAL 0) term111). Qed.
Lemma lem2721443 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2721444 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2721445 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2721444 h1) (fun h1 : term258 = True => @lem2721443)). Qed.
Lemma lem2721446 : term258 = True.
Proof. exact (EQ_MP (@lem2721445) (@lem2721443)). Qed.
Lemma lem2721447 : term257 = True.
Proof. exact (TRANS (@lem2721442) (@lem2721446)). Qed.
Lemma lem2721448 : True = term257.
Proof. exact (SYM (@lem2721447)). Qed.
Lemma lem2721449 : term257.
Proof. exact (EQ_MP (@lem2721448) (@lem0)). Qed.
Lemma lem2721450 : term467.
Proof. exact (@lem2721439 (@lem2721449)). Qed.
Lemma lem2721452 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2721453 : term257 = term258.
Proof. exact (@lem2721452 (NUMERAL 0) term111). Qed.
Lemma lem2721454 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2721455 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2721456 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2721455 h1) (fun h1 : term258 = True => @lem2721454)). Qed.
Lemma lem2721457 : term258 = True.
Proof. exact (EQ_MP (@lem2721456) (@lem2721454)). Qed.
Lemma lem2721458 : term257 = True.
Proof. exact (TRANS (@lem2721453) (@lem2721457)). Qed.
Lemma lem2721459 : True = term257.
Proof. exact (SYM (@lem2721458)). Qed.
Lemma lem2721460 : term257.
Proof. exact (EQ_MP (@lem2721459) (@lem0)). Qed.
Lemma lem2721461 : term468.
Proof. exact (@lem2721450 (@lem2721460)). Qed.
Lemma lem2721463 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2721464 : term202 = term203.
Proof. exact (@lem2721463 term111 term111). Qed.
Lemma lem2721465 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2721466 : term205 = term111.
Proof. exact (EQ_MP (@lem2721465) (@lem940073)). Qed.
Lemma lem2721467 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2721468 : term203 = term110.
Proof. exact (MK_COMB (@lem2721467) (@lem2721466)). Qed.
Lemma lem2721469 : term202 = term110.
Proof. exact (TRANS (@lem2721464) (@lem2721468)). Qed.
Lemma lem2721471 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2721472 : term215 = term220.
Proof. exact (@lem2721471 term111 term111). Qed.
Lemma lem2721473 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2721474 : term205 = term111.
Proof. exact (EQ_MP (@lem2721473) (@lem940073)). Qed.
Lemma lem2721475 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2721476 : term203 = term110.
Proof. exact (MK_COMB (@lem2721475) (@lem2721474)). Qed.
Lemma lem2721477 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2721478 : term220 = term193.
Proof. exact (MK_COMB (@lem2721477) (@lem2721476)). Qed.
Lemma lem2721479 : term215 = term193.
Proof. exact (TRANS (@lem2721472) (@lem2721478)). Qed.
Lemma lem2721480 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2721481 : term469 = term461.
Proof. exact (MK_COMB (@lem2721480) (@lem2721479)). Qed.
Lemma lem2721482 : term470 = term463.
Proof. exact (MK_COMB (@lem2721481) (@lem2721469)). Qed.
Lemma lem2721484 (m : nat) : (term471 m) = term107.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2721485 : term463 = term107.
Proof. exact (@lem2721484 term111). Qed.
Lemma lem2721486 : term470 = term107.
Proof. exact (TRANS (@lem2721482) (@lem2721485)). Qed.
Lemma lem2721487 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2721488 : term472 = term267.
Proof. exact (MK_COMB (@lem2721487) (@lem2721486)). Qed.
Lemma lem2721489 : term110 = term110.
Proof. exact (eq_refl term110). Qed.
Lemma lem2721490 : term473 = term269.
Proof. exact (MK_COMB (@lem2721488) (@lem2721489)). Qed.
Lemma lem2721492 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2721493 : term269 = term107.
Proof. exact (@lem2721492 term111). Qed.
Lemma lem2721494 : term473 = term107.
Proof. exact (TRANS (@lem2721490) (@lem2721493)). Qed.
Lemma lem2721496 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2721497 : term202 = term203.
Proof. exact (@lem2721496 term111 term111). Qed.
Lemma lem2721498 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2721499 : term205 = term111.
Proof. exact (EQ_MP (@lem2721498) (@lem940073)). Qed.
Lemma lem2721500 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2721501 : term203 = term110.
Proof. exact (MK_COMB (@lem2721500) (@lem2721499)). Qed.
Lemma lem2721502 : term202 = term110.
Proof. exact (TRANS (@lem2721497) (@lem2721501)). Qed.
Lemma lem2721503 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2721504 : term271 = term269.
Proof. exact (MK_COMB (@lem2721503) (@lem2721502)). Qed.
Lemma lem2721506 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2721507 : term269 = term107.
Proof. exact (@lem2721506 term111). Qed.
Lemma lem2721508 : term271 = term107.
Proof. exact (TRANS (@lem2721504) (@lem2721507)). Qed.
Lemma lem2721509 : term107 = term271.
Proof. exact (SYM (@lem2721508)). Qed.
Lemma lem2721510 : term473 = term271.
Proof. exact (TRANS (@lem2721494) (@lem2721509)). Qed.
Lemma lem2721511 : term464 = term190.
Proof. exact (@lem2721461 (@lem2721510)). Qed.
Lemma lem2721512 : term463 = term190.
Proof. exact (TRANS (@lem2721427) (@lem2721511)). Qed.
Lemma lem2721514 (x : real) : (term209 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2721515 : term190 = term107.
Proof. exact (@lem2721514 term107). Qed.
Lemma lem2721516 : term463 = term107.
Proof. exact (TRANS (@lem2721512) (@lem2721515)). Qed.
Lemma lem2721517 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2721518 : term474 = term267.
Proof. exact (MK_COMB (@lem2721517) (@lem2721516)). Qed.
Lemma lem2721519 (n : int) : (term104 n) = (term104 n).
Proof. exact (eq_refl (term104 n)). Qed.
Lemma lem2721520 (n : int) : (term460 n) = (term475 n).
Proof. exact (MK_COMB (@lem2721518) (@lem2721519 n)). Qed.
Lemma lem2721521 (n : int) : (term520 n) = (term475 n).
Proof. exact (TRANS (@lem2721418 n) (@lem2721520 n)). Qed.
Lemma lem2721522 (n : int) : (term475 n) = term107.
Proof. exact (@lem1982719 (term104 n)). Qed.
Lemma lem2721523 (n : int) : (term520 n) = term107.
Proof. exact (TRANS (@lem2721521 n) (@lem2721522 n)). Qed.
Lemma lem2721524 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2721525 (n : int) : (term521 n) = term139.
Proof. exact (MK_COMB (@lem2721524) (@lem2721523 n)). Qed.
Lemma lem2721526 : term110 = term110.
Proof. exact (eq_refl term110). Qed.
Lemma lem2721527 (n : int) : (term589 n) = term140.
Proof. exact (MK_COMB (@lem2721525 n) (@lem2721526)). Qed.
Lemma lem2721528 (n : int) : (term588 n) = term140.
Proof. exact (TRANS (@lem2721417 n) (@lem2721527 n)). Qed.
Lemma lem2721529 : term140 = term110.
Proof. exact (@lem1982721 term110). Qed.
Lemma lem2721530 (n : int) : (term588 n) = term110.
Proof. exact (TRANS (@lem2721528 n) (@lem2721529)). Qed.
Lemma lem2721531 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2721532 (n : int) : (term590 n) = term591.
Proof. exact (MK_COMB (@lem2721531) (@lem2721530 n)). Qed.
Lemma lem2721533 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2721534 (n : int) : ((term588 n) = term107) = (term110 = term107).
Proof. exact (MK_COMB (@lem2721532 n) (@lem2721533)). Qed.
Lemma lem2721535 (n : int) (h1 : term581 n) : term110 = term107.
Proof. exact (EQ_MP (@lem2721534 n) (@lem2721416 n h1)). Qed.
Lemma lem2721537 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2721538 : term107 = term190.
Proof. exact (@lem2721537 (NUMERAL 0)). Qed.
Lemma lem2721540 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2721541 : term110 = term214.
Proof. exact (@lem2721540 term111). Qed.
Lemma lem2721542 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2721543 : term591 = term592.
Proof. exact (MK_COMB (@lem2721542) (@lem2721541)). Qed.
Lemma lem2721544 : (term110 = term107) = (term214 = term190).
Proof. exact (MK_COMB (@lem2721543) (@lem2721538)). Qed.
Lemma lem2721545 : term593.
Proof. exact (@lem1980277 term110 term110 term107 term110). Qed.
Lemma lem2721547 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2721548 : term257 = term258.
Proof. exact (@lem2721547 (NUMERAL 0) term111). Qed.
Lemma lem2721549 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2721550 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2721551 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2721550 h1) (fun h1 : term258 = True => @lem2721549)). Qed.
Lemma lem2721552 : term258 = True.
Proof. exact (EQ_MP (@lem2721551) (@lem2721549)). Qed.
Lemma lem2721553 : term257 = True.
Proof. exact (TRANS (@lem2721548) (@lem2721552)). Qed.
Lemma lem2721554 : True = term257.
Proof. exact (SYM (@lem2721553)). Qed.
Lemma lem2721555 : term257.
Proof. exact (EQ_MP (@lem2721554) (@lem0)). Qed.
Lemma lem2721556 : term594.
Proof. exact (@lem2721545 (@lem2721555)). Qed.
Lemma lem2721558 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2721559 : term257 = term258.
Proof. exact (@lem2721558 (NUMERAL 0) term111). Qed.
Lemma lem2721560 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2721561 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2721562 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2721561 h1) (fun h1 : term258 = True => @lem2721560)). Qed.
Lemma lem2721563 : term258 = True.
Proof. exact (EQ_MP (@lem2721562) (@lem2721560)). Qed.
Lemma lem2721564 : term257 = True.
Proof. exact (TRANS (@lem2721559) (@lem2721563)). Qed.
Lemma lem2721565 : True = term257.
Proof. exact (SYM (@lem2721564)). Qed.
Lemma lem2721566 : term257.
Proof. exact (EQ_MP (@lem2721565) (@lem0)). Qed.
Lemma lem2721567 : (term214 = term190) = (term202 = term269).
Proof. exact (@lem2721556 (@lem2721566)). Qed.
Lemma lem2721569 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2721570 : term269 = term107.
Proof. exact (@lem2721569 term111). Qed.
Lemma lem2721572 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2721573 : term202 = term203.
Proof. exact (@lem2721572 term111 term111). Qed.
Lemma lem2721574 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2721575 : term205 = term111.
Proof. exact (EQ_MP (@lem2721574) (@lem940073)). Qed.
Lemma lem2721576 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2721577 : term203 = term110.
Proof. exact (MK_COMB (@lem2721576) (@lem2721575)). Qed.
Lemma lem2721578 : term202 = term110.
Proof. exact (TRANS (@lem2721573) (@lem2721577)). Qed.
Lemma lem2721579 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2721580 : term595 = term591.
Proof. exact (MK_COMB (@lem2721579) (@lem2721578)). Qed.
Lemma lem2721581 : (term202 = term269) = (term110 = term107).
Proof. exact (MK_COMB (@lem2721580) (@lem2721570)). Qed.
Lemma lem2721583 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = (m = n).
Proof. exact (proj1 (@lem1366971 m n)). Qed.
Lemma lem2721584 : (term110 = term107) = (term111 = (NUMERAL 0)).
Proof. exact (@lem2721583 term111 (NUMERAL 0)). Qed.
Lemma lem2721585 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2721586 (h1 : term259 = (BIT1 0)) : (term111 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2721587 : (term259 = (BIT1 0)) = ((term111 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2721586 h1) (fun h1 : (term111 = (NUMERAL 0)) = False => @lem2721585)). Qed.
Lemma lem2721588 : (term111 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2721587) (@lem2721585)). Qed.
Lemma lem2721589 : (term110 = term107) = False.
Proof. exact (TRANS (@lem2721584) (@lem2721588)). Qed.
Lemma lem2721590 : (term202 = term269) = False.
Proof. exact (TRANS (@lem2721581) (@lem2721589)). Qed.
Lemma lem2721591 : (term214 = term190) = False.
Proof. exact (TRANS (@lem2721567) (@lem2721590)). Qed.
Lemma lem2721592 : (term110 = term107) = False.
Proof. exact (TRANS (@lem2721544) (@lem2721591)). Qed.
Lemma lem2721593 (n : int) (h1 : term581 n) : False.
Proof. exact (EQ_MP (@lem2721592) (@lem2721535 n h1)). Qed.
Lemma lem2721594 (n : int) (h1 : term596 n) : term596 n.
Proof. exact (h1). Qed.
Lemma lem2721595 (n : int) (h1 : term596 n) : term320 n.
Proof. exact (proj2 (@lem2721594 n h1)). Qed.
Lemma lem2721597 (n : int) (h1 : term596 n) : (term223 n) = term107.
Proof. exact (proj2 (@lem2721595 n h1)). Qed.
Lemma lem2721598 (n : int) (h1 : term596 n) : (term104 n) = term107.
Proof. exact (proj1 (@lem2721595 n h1)). Qed.
Lemma lem2721600 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2721601 : term433 = term257.
Proof. exact (@lem2721600 term107 term110). Qed.
Lemma lem2721603 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2721604 : term110 = term214.
Proof. exact (@lem2721603 term111). Qed.
Lemma lem2721606 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2721607 : term107 = term190.
Proof. exact (@lem2721606 (NUMERAL 0)). Qed.
Lemma lem2721608 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2721609 : term434 = term435.
Proof. exact (MK_COMB (@lem2721608) (@lem2721607)). Qed.
Lemma lem2721610 : term257 = term436.
Proof. exact (MK_COMB (@lem2721609) (@lem2721604)). Qed.
Lemma lem2721611 : term437.
Proof. exact (@lem1980255 term107 term110 term110 term110). Qed.
Lemma lem2721613 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2721614 : term257 = term258.
Proof. exact (@lem2721613 (NUMERAL 0) term111). Qed.
Lemma lem2721615 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2721616 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2721617 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2721616 h1) (fun h1 : term258 = True => @lem2721615)). Qed.
Lemma lem2721618 : term258 = True.
Proof. exact (EQ_MP (@lem2721617) (@lem2721615)). Qed.
Lemma lem2721619 : term257 = True.
Proof. exact (TRANS (@lem2721614) (@lem2721618)). Qed.
Lemma lem2721620 : True = term257.
Proof. exact (SYM (@lem2721619)). Qed.
Lemma lem2721621 : term257.
Proof. exact (EQ_MP (@lem2721620) (@lem0)). Qed.
Lemma lem2721622 : term438.
Proof. exact (@lem2721611 (@lem2721621)). Qed.
Lemma lem2721624 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2721625 : term257 = term258.
Proof. exact (@lem2721624 (NUMERAL 0) term111). Qed.
Lemma lem2721626 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2721627 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2721628 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2721627 h1) (fun h1 : term258 = True => @lem2721626)). Qed.
Lemma lem2721629 : term258 = True.
Proof. exact (EQ_MP (@lem2721628) (@lem2721626)). Qed.
Lemma lem2721630 : term257 = True.
Proof. exact (TRANS (@lem2721625) (@lem2721629)). Qed.
Lemma lem2721631 : True = term257.
Proof. exact (SYM (@lem2721630)). Qed.
Lemma lem2721632 : term257.
Proof. exact (EQ_MP (@lem2721631) (@lem0)). Qed.
Lemma lem2721633 : term436 = term439.
Proof. exact (@lem2721622 (@lem2721632)). Qed.
Lemma lem2721635 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2721636 : term202 = term203.
Proof. exact (@lem2721635 term111 term111). Qed.
Lemma lem2721637 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2721638 : term205 = term111.
Proof. exact (EQ_MP (@lem2721637) (@lem940073)). Qed.
Lemma lem2721639 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2721640 : term203 = term110.
Proof. exact (MK_COMB (@lem2721639) (@lem2721638)). Qed.
Lemma lem2721641 : term202 = term110.
Proof. exact (TRANS (@lem2721636) (@lem2721640)). Qed.
Lemma lem2721643 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2721644 : term269 = term107.
Proof. exact (@lem2721643 term111). Qed.
Lemma lem2721645 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2721646 : term440 = term434.
Proof. exact (MK_COMB (@lem2721645) (@lem2721644)). Qed.
Lemma lem2721647 : term439 = term257.
Proof. exact (MK_COMB (@lem2721646) (@lem2721641)). Qed.
Lemma lem2721649 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2721650 : term257 = term258.
Proof. exact (@lem2721649 (NUMERAL 0) term111). Qed.
Lemma lem2721651 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2721652 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2721653 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2721652 h1) (fun h1 : term258 = True => @lem2721651)). Qed.
Lemma lem2721654 : term258 = True.
Proof. exact (EQ_MP (@lem2721653) (@lem2721651)). Qed.
Lemma lem2721655 : term257 = True.
Proof. exact (TRANS (@lem2721650) (@lem2721654)). Qed.
Lemma lem2721656 : term439 = True.
Proof. exact (TRANS (@lem2721647) (@lem2721655)). Qed.
Lemma lem2721657 : term436 = True.
Proof. exact (TRANS (@lem2721633) (@lem2721656)). Qed.
Lemma lem2721658 : term257 = True.
Proof. exact (TRANS (@lem2721610) (@lem2721657)). Qed.
Lemma lem2721659 : term433 = True.
Proof. exact (TRANS (@lem2721601) (@lem2721658)). Qed.
Lemma lem2721660 : True = term433.
Proof. exact (SYM (@lem2721659)). Qed.
Lemma lem2721661 : term433.
Proof. exact (EQ_MP (@lem2721660) (@lem0)). Qed.
Lemma lem2721662 (n : int) (h1 : term596 n) : term582 n.
Proof. exact (conj (@lem2721661) (@lem2721598 n h1)). Qed.
Lemma lem2721664 (x : real) (y : real) : term583 x y.
Proof. exact (proj1 (@lem1988330 x y)). Qed.
Lemma lem2721665 (n : int) : term584 n.
Proof. exact (@lem2721664 term110 (term104 n)). Qed.
Lemma lem2721666 (n : int) (h1 : term596 n) : (term451 n) = term107.
Proof. exact (@lem2721665 n (@lem2721662 n h1)). Qed.
Lemma lem2721667 (n : int) : (term451 n) = (term104 n).
Proof. exact (@lem1982733 (term104 n)). Qed.
Lemma lem2721668 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2721669 (n : int) : (term452 n) = (term108 n).
Proof. exact (MK_COMB (@lem2721668) (@lem2721667 n)). Qed.
Lemma lem2721670 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2721671 (n : int) : ((term451 n) = term107) = ((term104 n) = term107).
Proof. exact (MK_COMB (@lem2721669 n) (@lem2721670)). Qed.
Lemma lem2721672 (n : int) (h1 : term596 n) : (term104 n) = term107.
Proof. exact (EQ_MP (@lem2721671 n) (@lem2721666 n h1)). Qed.
Lemma lem2721674 (y : real) : term447 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2721675 (n : int) : term499 n.
Proof. exact (@lem2721674 (term223 n)). Qed.
Lemma lem2721676 (n : int) (h1 : term596 n) : term500 n.
Proof. exact (@lem2721675 n (@lem2721597 n h1)). Qed.
Lemma lem2721677 (n : int) (h1 : term596 n) : term549 n.
Proof. exact (@lem2721676 n h1 term193). Qed.
Lemma lem2721678 (n : int) : (term549 n) = ((term550 n) = term107).
Proof. exact (eq_refl (term549 n)). Qed.
Lemma lem2721679 (n : int) (h1 : term596 n) : (term550 n) = term107.
Proof. exact (EQ_MP (@lem2721678 n) (@lem2721677 n h1)). Qed.
Lemma lem2721680 (n : int) : (term550 n) = (term551 n).
Proof. exact (@lem1982781 (term104 n) term193 term193). Qed.
Lemma lem2721682 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2721683 : term193 = term194.
Proof. exact (@lem2721682 term111). Qed.
Lemma lem2721685 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2721686 : term193 = term194.
Proof. exact (@lem2721685 term111). Qed.
Lemma lem2721687 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2721688 : term195 = term196.
Proof. exact (MK_COMB (@lem2721687) (@lem2721686)). Qed.
Lemma lem2721689 : term552 = term553.
Proof. exact (MK_COMB (@lem2721688) (@lem2721683)). Qed.
Lemma lem2721690 : term553 = term554.
Proof. exact (@lem1981613 term193 term193 term110 term110). Qed.
Lemma lem2721692 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2721693 : term202 = term203.
Proof. exact (@lem2721692 term111 term111). Qed.
Lemma lem2721694 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2721695 : term205 = term111.
Proof. exact (EQ_MP (@lem2721694) (@lem940073)). Qed.
Lemma lem2721696 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2721697 : term203 = term110.
Proof. exact (MK_COMB (@lem2721696) (@lem2721695)). Qed.
Lemma lem2721698 : term202 = term110.
Proof. exact (TRANS (@lem2721693) (@lem2721697)). Qed.
Lemma lem2721700 (m : nat) (n : nat) : (term555 m n) = (term201 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2721701 : term552 = term203.
Proof. exact (@lem2721700 term111 term111). Qed.
Lemma lem2721702 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2721703 : term205 = term111.
Proof. exact (EQ_MP (@lem2721702) (@lem940073)). Qed.
Lemma lem2721704 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2721705 : term203 = term110.
Proof. exact (MK_COMB (@lem2721704) (@lem2721703)). Qed.
Lemma lem2721706 : term552 = term110.
Proof. exact (TRANS (@lem2721701) (@lem2721705)). Qed.
Lemma lem2721707 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2721708 : term556 = term557.
Proof. exact (MK_COMB (@lem2721707) (@lem2721706)). Qed.
Lemma lem2721709 : term554 = term214.
Proof. exact (MK_COMB (@lem2721708) (@lem2721698)). Qed.
Lemma lem2721710 : term553 = term214.
Proof. exact (TRANS (@lem2721690) (@lem2721709)). Qed.
Lemma lem2721711 : term552 = term214.
Proof. exact (TRANS (@lem2721689) (@lem2721710)). Qed.
Lemma lem2721713 (x : real) : (term209 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2721714 : term214 = term110.
Proof. exact (@lem2721713 term110). Qed.
Lemma lem2721715 : term552 = term110.
Proof. exact (TRANS (@lem2721711) (@lem2721714)). Qed.
Lemma lem2721718 (n : int) : (term232 n) = (term232 n).
Proof. exact (eq_refl (term232 n)). Qed.
Lemma lem2721719 (n : int) : (term551 n) = (term558 n).
Proof. exact (MK_COMB (@lem2721718 n) (@lem2721715)). Qed.
Lemma lem2721720 (n : int) : (term550 n) = (term558 n).
Proof. exact (TRANS (@lem2721680 n) (@lem2721719 n)). Qed.
Lemma lem2721721 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2721722 (n : int) : (term559 n) = (term560 n).
Proof. exact (MK_COMB (@lem2721721) (@lem2721720 n)). Qed.
Lemma lem2721723 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2721724 (n : int) : ((term550 n) = term107) = ((term558 n) = term107).
Proof. exact (MK_COMB (@lem2721722 n) (@lem2721723)). Qed.
Lemma lem2721725 (n : int) (h1 : term596 n) : (term558 n) = term107.
Proof. exact (EQ_MP (@lem2721724 n) (@lem2721679 n h1)). Qed.
Lemma lem2721726 (n : int) (h1 : term596 n) : term585 n.
Proof. exact (conj (@lem2721725 n h1) (@lem2721672 n h1)). Qed.
Lemma lem2721728 (x : real) (y : real) : term586 x y.
Proof. exact (proj1 (@lem1393126 x y)). Qed.
Lemma lem2721729 (n : int) : term587 n.
Proof. exact (@lem2721728 (term558 n) (term104 n)). Qed.
Lemma lem2721730 (n : int) (h1 : term596 n) : (term588 n) = term107.
Proof. exact (@lem2721729 n (@lem2721726 n h1)). Qed.
Lemma lem2721731 (n : int) : (term588 n) = (term589 n).
Proof. exact (@lem1982759 (term251 n) (term104 n) term110). Qed.
Lemma lem2721732 (n : int) : (term520 n) = (term460 n).
Proof. exact (@lem1982713 term193 (term104 n)). Qed.
Lemma lem2721734 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2721735 : term110 = term214.
Proof. exact (@lem2721734 term111). Qed.
Lemma lem2721737 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2721738 : term193 = term194.
Proof. exact (@lem2721737 term111). Qed.
Lemma lem2721739 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2721740 : term461 = term462.
Proof. exact (MK_COMB (@lem2721739) (@lem2721738)). Qed.
Lemma lem2721741 : term463 = term464.
Proof. exact (MK_COMB (@lem2721740) (@lem2721735)). Qed.
Lemma lem2721742 : term465.
Proof. exact (@lem1981473 term193 term110 term110 term110 term107 term110). Qed.
Lemma lem2721744 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2721745 : term257 = term258.
Proof. exact (@lem2721744 (NUMERAL 0) term111). Qed.
Lemma lem2721746 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2721747 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2721748 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2721747 h1) (fun h1 : term258 = True => @lem2721746)). Qed.
Lemma lem2721749 : term258 = True.
Proof. exact (EQ_MP (@lem2721748) (@lem2721746)). Qed.
Lemma lem2721750 : term257 = True.
Proof. exact (TRANS (@lem2721745) (@lem2721749)). Qed.
Lemma lem2721751 : True = term257.
Proof. exact (SYM (@lem2721750)). Qed.
Lemma lem2721752 : term257.
Proof. exact (EQ_MP (@lem2721751) (@lem0)). Qed.
Lemma lem2721753 : term466.
Proof. exact (@lem2721742 (@lem2721752)). Qed.
Lemma lem2721755 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2721756 : term257 = term258.
Proof. exact (@lem2721755 (NUMERAL 0) term111). Qed.
Lemma lem2721757 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2721758 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2721759 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2721758 h1) (fun h1 : term258 = True => @lem2721757)). Qed.
Lemma lem2721760 : term258 = True.
Proof. exact (EQ_MP (@lem2721759) (@lem2721757)). Qed.
Lemma lem2721761 : term257 = True.
Proof. exact (TRANS (@lem2721756) (@lem2721760)). Qed.
Lemma lem2721762 : True = term257.
Proof. exact (SYM (@lem2721761)). Qed.
Lemma lem2721763 : term257.
Proof. exact (EQ_MP (@lem2721762) (@lem0)). Qed.
Lemma lem2721764 : term467.
Proof. exact (@lem2721753 (@lem2721763)). Qed.
Lemma lem2721766 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2721767 : term257 = term258.
Proof. exact (@lem2721766 (NUMERAL 0) term111). Qed.
Lemma lem2721768 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2721769 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2721770 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2721769 h1) (fun h1 : term258 = True => @lem2721768)). Qed.
Lemma lem2721771 : term258 = True.
Proof. exact (EQ_MP (@lem2721770) (@lem2721768)). Qed.
Lemma lem2721772 : term257 = True.
Proof. exact (TRANS (@lem2721767) (@lem2721771)). Qed.
Lemma lem2721773 : True = term257.
Proof. exact (SYM (@lem2721772)). Qed.
Lemma lem2721774 : term257.
Proof. exact (EQ_MP (@lem2721773) (@lem0)). Qed.
Lemma lem2721775 : term468.
Proof. exact (@lem2721764 (@lem2721774)). Qed.
Lemma lem2721777 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2721778 : term202 = term203.
Proof. exact (@lem2721777 term111 term111). Qed.
Lemma lem2721779 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2721780 : term205 = term111.
Proof. exact (EQ_MP (@lem2721779) (@lem940073)). Qed.
Lemma lem2721781 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2721782 : term203 = term110.
Proof. exact (MK_COMB (@lem2721781) (@lem2721780)). Qed.
Lemma lem2721783 : term202 = term110.
Proof. exact (TRANS (@lem2721778) (@lem2721782)). Qed.
Lemma lem2721785 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2721786 : term215 = term220.
Proof. exact (@lem2721785 term111 term111). Qed.
Lemma lem2721787 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2721788 : term205 = term111.
Proof. exact (EQ_MP (@lem2721787) (@lem940073)). Qed.
Lemma lem2721789 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2721790 : term203 = term110.
Proof. exact (MK_COMB (@lem2721789) (@lem2721788)). Qed.
Lemma lem2721791 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2721792 : term220 = term193.
Proof. exact (MK_COMB (@lem2721791) (@lem2721790)). Qed.
Lemma lem2721793 : term215 = term193.
Proof. exact (TRANS (@lem2721786) (@lem2721792)). Qed.
Lemma lem2721794 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2721795 : term469 = term461.
Proof. exact (MK_COMB (@lem2721794) (@lem2721793)). Qed.
Lemma lem2721796 : term470 = term463.
Proof. exact (MK_COMB (@lem2721795) (@lem2721783)). Qed.
Lemma lem2721798 (m : nat) : (term471 m) = term107.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2721799 : term463 = term107.
Proof. exact (@lem2721798 term111). Qed.
Lemma lem2721800 : term470 = term107.
Proof. exact (TRANS (@lem2721796) (@lem2721799)). Qed.
Lemma lem2721801 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2721802 : term472 = term267.
Proof. exact (MK_COMB (@lem2721801) (@lem2721800)). Qed.
Lemma lem2721803 : term110 = term110.
Proof. exact (eq_refl term110). Qed.
Lemma lem2721804 : term473 = term269.
Proof. exact (MK_COMB (@lem2721802) (@lem2721803)). Qed.
Lemma lem2721806 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2721807 : term269 = term107.
Proof. exact (@lem2721806 term111). Qed.
Lemma lem2721808 : term473 = term107.
Proof. exact (TRANS (@lem2721804) (@lem2721807)). Qed.
Lemma lem2721810 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2721811 : term202 = term203.
Proof. exact (@lem2721810 term111 term111). Qed.
Lemma lem2721812 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2721813 : term205 = term111.
Proof. exact (EQ_MP (@lem2721812) (@lem940073)). Qed.
Lemma lem2721814 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2721815 : term203 = term110.
Proof. exact (MK_COMB (@lem2721814) (@lem2721813)). Qed.
Lemma lem2721816 : term202 = term110.
Proof. exact (TRANS (@lem2721811) (@lem2721815)). Qed.
Lemma lem2721817 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2721818 : term271 = term269.
Proof. exact (MK_COMB (@lem2721817) (@lem2721816)). Qed.
Lemma lem2721820 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2721821 : term269 = term107.
Proof. exact (@lem2721820 term111). Qed.
Lemma lem2721822 : term271 = term107.
Proof. exact (TRANS (@lem2721818) (@lem2721821)). Qed.
Lemma lem2721823 : term107 = term271.
Proof. exact (SYM (@lem2721822)). Qed.
Lemma lem2721824 : term473 = term271.
Proof. exact (TRANS (@lem2721808) (@lem2721823)). Qed.
Lemma lem2721825 : term464 = term190.
Proof. exact (@lem2721775 (@lem2721824)). Qed.
Lemma lem2721826 : term463 = term190.
Proof. exact (TRANS (@lem2721741) (@lem2721825)). Qed.
Lemma lem2721828 (x : real) : (term209 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2721829 : term190 = term107.
Proof. exact (@lem2721828 term107). Qed.
Lemma lem2721830 : term463 = term107.
Proof. exact (TRANS (@lem2721826) (@lem2721829)). Qed.
Lemma lem2721831 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2721832 : term474 = term267.
Proof. exact (MK_COMB (@lem2721831) (@lem2721830)). Qed.
Lemma lem2721833 (n : int) : (term104 n) = (term104 n).
Proof. exact (eq_refl (term104 n)). Qed.
Lemma lem2721834 (n : int) : (term460 n) = (term475 n).
Proof. exact (MK_COMB (@lem2721832) (@lem2721833 n)). Qed.
Lemma lem2721835 (n : int) : (term520 n) = (term475 n).
Proof. exact (TRANS (@lem2721732 n) (@lem2721834 n)). Qed.
Lemma lem2721836 (n : int) : (term475 n) = term107.
Proof. exact (@lem1982719 (term104 n)). Qed.
Lemma lem2721837 (n : int) : (term520 n) = term107.
Proof. exact (TRANS (@lem2721835 n) (@lem2721836 n)). Qed.
Lemma lem2721838 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2721839 (n : int) : (term521 n) = term139.
Proof. exact (MK_COMB (@lem2721838) (@lem2721837 n)). Qed.
Lemma lem2721840 : term110 = term110.
Proof. exact (eq_refl term110). Qed.
Lemma lem2721841 (n : int) : (term589 n) = term140.
Proof. exact (MK_COMB (@lem2721839 n) (@lem2721840)). Qed.
Lemma lem2721842 (n : int) : (term588 n) = term140.
Proof. exact (TRANS (@lem2721731 n) (@lem2721841 n)). Qed.
Lemma lem2721843 : term140 = term110.
Proof. exact (@lem1982721 term110). Qed.
Lemma lem2721844 (n : int) : (term588 n) = term110.
Proof. exact (TRANS (@lem2721842 n) (@lem2721843)). Qed.
Lemma lem2721845 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2721846 (n : int) : (term590 n) = term591.
Proof. exact (MK_COMB (@lem2721845) (@lem2721844 n)). Qed.
Lemma lem2721847 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2721848 (n : int) : ((term588 n) = term107) = (term110 = term107).
Proof. exact (MK_COMB (@lem2721846 n) (@lem2721847)). Qed.
Lemma lem2721849 (n : int) (h1 : term596 n) : term110 = term107.
Proof. exact (EQ_MP (@lem2721848 n) (@lem2721730 n h1)). Qed.
Lemma lem2721851 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2721852 : term107 = term190.
Proof. exact (@lem2721851 (NUMERAL 0)). Qed.
Lemma lem2721854 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2721855 : term110 = term214.
Proof. exact (@lem2721854 term111). Qed.
Lemma lem2721856 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2721857 : term591 = term592.
Proof. exact (MK_COMB (@lem2721856) (@lem2721855)). Qed.
Lemma lem2721858 : (term110 = term107) = (term214 = term190).
Proof. exact (MK_COMB (@lem2721857) (@lem2721852)). Qed.
Lemma lem2721859 : term593.
Proof. exact (@lem1980277 term110 term110 term107 term110). Qed.
Lemma lem2721861 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2721862 : term257 = term258.
Proof. exact (@lem2721861 (NUMERAL 0) term111). Qed.
Lemma lem2721863 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2721864 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2721865 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2721864 h1) (fun h1 : term258 = True => @lem2721863)). Qed.
Lemma lem2721866 : term258 = True.
Proof. exact (EQ_MP (@lem2721865) (@lem2721863)). Qed.
Lemma lem2721867 : term257 = True.
Proof. exact (TRANS (@lem2721862) (@lem2721866)). Qed.
Lemma lem2721868 : True = term257.
Proof. exact (SYM (@lem2721867)). Qed.
Lemma lem2721869 : term257.
Proof. exact (EQ_MP (@lem2721868) (@lem0)). Qed.
Lemma lem2721870 : term594.
Proof. exact (@lem2721859 (@lem2721869)). Qed.
Lemma lem2721872 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2721873 : term257 = term258.
Proof. exact (@lem2721872 (NUMERAL 0) term111). Qed.
Lemma lem2721874 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2721875 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2721876 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2721875 h1) (fun h1 : term258 = True => @lem2721874)). Qed.
Lemma lem2721877 : term258 = True.
Proof. exact (EQ_MP (@lem2721876) (@lem2721874)). Qed.
Lemma lem2721878 : term257 = True.
Proof. exact (TRANS (@lem2721873) (@lem2721877)). Qed.
Lemma lem2721879 : True = term257.
Proof. exact (SYM (@lem2721878)). Qed.
Lemma lem2721880 : term257.
Proof. exact (EQ_MP (@lem2721879) (@lem0)). Qed.
Lemma lem2721881 : (term214 = term190) = (term202 = term269).
Proof. exact (@lem2721870 (@lem2721880)). Qed.
Lemma lem2721883 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2721884 : term269 = term107.
Proof. exact (@lem2721883 term111). Qed.
Lemma lem2721886 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2721887 : term202 = term203.
Proof. exact (@lem2721886 term111 term111). Qed.
Lemma lem2721888 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2721889 : term205 = term111.
Proof. exact (EQ_MP (@lem2721888) (@lem940073)). Qed.
Lemma lem2721890 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2721891 : term203 = term110.
Proof. exact (MK_COMB (@lem2721890) (@lem2721889)). Qed.
Lemma lem2721892 : term202 = term110.
Proof. exact (TRANS (@lem2721887) (@lem2721891)). Qed.
Lemma lem2721893 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2721894 : term595 = term591.
Proof. exact (MK_COMB (@lem2721893) (@lem2721892)). Qed.
Lemma lem2721895 : (term202 = term269) = (term110 = term107).
Proof. exact (MK_COMB (@lem2721894) (@lem2721884)). Qed.
Lemma lem2721897 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = (m = n).
Proof. exact (proj1 (@lem1366971 m n)). Qed.
Lemma lem2721898 : (term110 = term107) = (term111 = (NUMERAL 0)).
Proof. exact (@lem2721897 term111 (NUMERAL 0)). Qed.
Lemma lem2721899 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2721900 (h1 : term259 = (BIT1 0)) : (term111 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2721901 : (term259 = (BIT1 0)) = ((term111 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2721900 h1) (fun h1 : (term111 = (NUMERAL 0)) = False => @lem2721899)). Qed.
Lemma lem2721902 : (term111 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2721901) (@lem2721899)). Qed.
Lemma lem2721903 : (term110 = term107) = False.
Proof. exact (TRANS (@lem2721898) (@lem2721902)). Qed.
Lemma lem2721904 : (term202 = term269) = False.
Proof. exact (TRANS (@lem2721895) (@lem2721903)). Qed.
Lemma lem2721905 : (term214 = term190) = False.
Proof. exact (TRANS (@lem2721881) (@lem2721904)). Qed.
Lemma lem2721906 : (term110 = term107) = False.
Proof. exact (TRANS (@lem2721858) (@lem2721905)). Qed.
Lemma lem2721907 (n : int) (h1 : term596 n) : False.
Proof. exact (EQ_MP (@lem2721906) (@lem2721849 n h1)). Qed.
Lemma lem2721908 (n : int) (h1 : term396 n) : False.
Proof. exact (or_elim (@lem2721279 n h1) (fun h0 : term581 n => @lem2721593 n h0) (fun h0 : term596 n => @lem2721907 n h0)). Qed.
Lemma lem2721909 (n : int) (h1 : term426 n) : False.
Proof. exact (or_elim (@lem2718640 n h1) (fun h0 : term423 n => @lem2721278 n h0) (fun h0 : term396 n => @lem2721908 n h0)). Qed.
Lemma lem2721910 (n : int) (h1 : term392 n) : term392 n.
Proof. exact (h1). Qed.
Lemma lem2721911 (n : int) (h1 : term389 n) : term389 n.
Proof. exact (h1). Qed.
Lemma lem2721912 (n : int) (h1 : term386 n) : term386 n.
Proof. exact (h1). Qed.
Lemma lem2721913 (n : int) (h1 : term383 n) : term383 n.
Proof. exact (h1). Qed.
Lemma lem2721914 (n : int) (h1 : term597 n) : term597 n.
Proof. exact (h1). Qed.
Lemma lem2721915 (n : int) (h1 : term597 n) : term378 n.
Proof. exact (proj2 (@lem2721914 n h1)). Qed.
Lemma lem2721916 (n : int) (h1 : term597 n) : (term104 n) = term107.
Proof. exact (proj1 (@lem2721914 n h1)). Qed.
Lemma lem2721917 (n : int) (h1 : term597 n) : term237 n.
Proof. exact (proj2 (@lem2721915 n h1)). Qed.
Lemma lem2721920 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2721921 : term433 = term257.
Proof. exact (@lem2721920 term107 term110). Qed.
Lemma lem2721923 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2721924 : term110 = term214.
Proof. exact (@lem2721923 term111). Qed.
Lemma lem2721926 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2721927 : term107 = term190.
Proof. exact (@lem2721926 (NUMERAL 0)). Qed.
Lemma lem2721928 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2721929 : term434 = term435.
Proof. exact (MK_COMB (@lem2721928) (@lem2721927)). Qed.
Lemma lem2721930 : term257 = term436.
Proof. exact (MK_COMB (@lem2721929) (@lem2721924)). Qed.
Lemma lem2721931 : term437.
Proof. exact (@lem1980255 term107 term110 term110 term110). Qed.
Lemma lem2721933 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2721934 : term257 = term258.
Proof. exact (@lem2721933 (NUMERAL 0) term111). Qed.
Lemma lem2721935 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2721936 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2721937 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2721936 h1) (fun h1 : term258 = True => @lem2721935)). Qed.
Lemma lem2721938 : term258 = True.
Proof. exact (EQ_MP (@lem2721937) (@lem2721935)). Qed.
Lemma lem2721939 : term257 = True.
Proof. exact (TRANS (@lem2721934) (@lem2721938)). Qed.
Lemma lem2721940 : True = term257.
Proof. exact (SYM (@lem2721939)). Qed.
Lemma lem2721941 : term257.
Proof. exact (EQ_MP (@lem2721940) (@lem0)). Qed.
Lemma lem2721942 : term438.
Proof. exact (@lem2721931 (@lem2721941)). Qed.
Lemma lem2721944 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2721945 : term257 = term258.
Proof. exact (@lem2721944 (NUMERAL 0) term111). Qed.
Lemma lem2721946 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2721947 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2721948 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2721947 h1) (fun h1 : term258 = True => @lem2721946)). Qed.
Lemma lem2721949 : term258 = True.
Proof. exact (EQ_MP (@lem2721948) (@lem2721946)). Qed.
Lemma lem2721950 : term257 = True.
Proof. exact (TRANS (@lem2721945) (@lem2721949)). Qed.
Lemma lem2721951 : True = term257.
Proof. exact (SYM (@lem2721950)). Qed.
Lemma lem2721952 : term257.
Proof. exact (EQ_MP (@lem2721951) (@lem0)). Qed.
Lemma lem2721953 : term436 = term439.
Proof. exact (@lem2721942 (@lem2721952)). Qed.
Lemma lem2721955 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2721956 : term202 = term203.
Proof. exact (@lem2721955 term111 term111). Qed.
Lemma lem2721957 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2721958 : term205 = term111.
Proof. exact (EQ_MP (@lem2721957) (@lem940073)). Qed.
Lemma lem2721959 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2721960 : term203 = term110.
Proof. exact (MK_COMB (@lem2721959) (@lem2721958)). Qed.
Lemma lem2721961 : term202 = term110.
Proof. exact (TRANS (@lem2721956) (@lem2721960)). Qed.
Lemma lem2721963 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2721964 : term269 = term107.
Proof. exact (@lem2721963 term111). Qed.
Lemma lem2721965 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2721966 : term440 = term434.
Proof. exact (MK_COMB (@lem2721965) (@lem2721964)). Qed.
Lemma lem2721967 : term439 = term257.
Proof. exact (MK_COMB (@lem2721966) (@lem2721961)). Qed.
Lemma lem2721969 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2721970 : term257 = term258.
Proof. exact (@lem2721969 (NUMERAL 0) term111). Qed.
Lemma lem2721971 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2721972 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2721973 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2721972 h1) (fun h1 : term258 = True => @lem2721971)). Qed.
Lemma lem2721974 : term258 = True.
Proof. exact (EQ_MP (@lem2721973) (@lem2721971)). Qed.
Lemma lem2721975 : term257 = True.
Proof. exact (TRANS (@lem2721970) (@lem2721974)). Qed.
Lemma lem2721976 : term439 = True.
Proof. exact (TRANS (@lem2721967) (@lem2721975)). Qed.
Lemma lem2721977 : term436 = True.
Proof. exact (TRANS (@lem2721953) (@lem2721976)). Qed.
Lemma lem2721978 : term257 = True.
Proof. exact (TRANS (@lem2721930) (@lem2721977)). Qed.
Lemma lem2721979 : term433 = True.
Proof. exact (TRANS (@lem2721921) (@lem2721978)). Qed.
Lemma lem2721980 : True = term433.
Proof. exact (SYM (@lem2721979)). Qed.
Lemma lem2721981 : term433.
Proof. exact (EQ_MP (@lem2721980) (@lem0)). Qed.
Lemma lem2721982 (n : int) (h1 : term597 n) : term441 n.
Proof. exact (conj (@lem2721981) (@lem2721917 n h1)). Qed.
Lemma lem2721984 (x : real) (y : real) : term442 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2721985 (n : int) : term443 n.
Proof. exact (@lem2721984 term110 (term233 n)). Qed.
Lemma lem2721986 (n : int) (h1 : term597 n) : term444 n.
Proof. exact (@lem2721985 n (@lem2721982 n h1)). Qed.
Lemma lem2721987 (n : int) : (term445 n) = (term233 n).
Proof. exact (@lem1982733 (term233 n)). Qed.
Lemma lem2721988 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2721989 (n : int) : (term446 n) = (term236 n).
Proof. exact (MK_COMB (@lem2721988) (@lem2721987 n)). Qed.
Lemma lem2721990 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2721991 (n : int) : (term444 n) = (term237 n).
Proof. exact (MK_COMB (@lem2721989 n) (@lem2721990)). Qed.
Lemma lem2721992 (n : int) (h1 : term597 n) : term237 n.
Proof. exact (EQ_MP (@lem2721991 n) (@lem2721986 n h1)). Qed.
Lemma lem2721994 (y : real) : term447 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2721995 (n : int) : term448 n.
Proof. exact (@lem2721994 (term104 n)). Qed.
Lemma lem2721996 (n : int) (h1 : term597 n) : term449 n.
Proof. exact (@lem2721995 n (@lem2721916 n h1)). Qed.
Lemma lem2721997 (n : int) (h1 : term597 n) : term450 n.
Proof. exact (@lem2721996 n h1 term110). Qed.
Lemma lem2721998 (n : int) : (term450 n) = ((term451 n) = term107).
Proof. exact (eq_refl (term450 n)). Qed.
Lemma lem2721999 (n : int) (h1 : term597 n) : (term451 n) = term107.
Proof. exact (EQ_MP (@lem2721998 n) (@lem2721997 n h1)). Qed.
Lemma lem2722000 (n : int) : (term451 n) = (term104 n).
Proof. exact (@lem1982733 (term104 n)). Qed.
Lemma lem2722001 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2722002 (n : int) : (term452 n) = (term108 n).
Proof. exact (MK_COMB (@lem2722001) (@lem2722000 n)). Qed.
Lemma lem2722003 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2722004 (n : int) : ((term451 n) = term107) = ((term104 n) = term107).
Proof. exact (MK_COMB (@lem2722002 n) (@lem2722003)). Qed.
Lemma lem2722005 (n : int) (h1 : term597 n) : (term104 n) = term107.
Proof. exact (EQ_MP (@lem2722004 n) (@lem2721999 n h1)). Qed.
Lemma lem2722006 (n : int) (h1 : term597 n) : term453 n.
Proof. exact (conj (@lem2722005 n h1) (@lem2721992 n h1)). Qed.
Lemma lem2722008 (x : real) (y : real) : term454 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2722009 (n : int) : term455 n.
Proof. exact (@lem2722008 (term104 n) (term233 n)). Qed.
Lemma lem2722010 (n : int) (h1 : term597 n) : term456 n.
Proof. exact (@lem2722009 n (@lem2722006 n h1)). Qed.
Lemma lem2722011 (n : int) : (term457 n) = (term458 n).
Proof. exact (@lem1982763 (term104 n) (term251 n) term193). Qed.
Lemma lem2722012 (n : int) : (term459 n) = (term460 n).
Proof. exact (@lem1982715 term193 (term104 n)). Qed.
Lemma lem2722014 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2722015 : term110 = term214.
Proof. exact (@lem2722014 term111). Qed.
Lemma lem2722017 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2722018 : term193 = term194.
Proof. exact (@lem2722017 term111). Qed.
Lemma lem2722019 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2722020 : term461 = term462.
Proof. exact (MK_COMB (@lem2722019) (@lem2722018)). Qed.
Lemma lem2722021 : term463 = term464.
Proof. exact (MK_COMB (@lem2722020) (@lem2722015)). Qed.
Lemma lem2722022 : term465.
Proof. exact (@lem1981473 term193 term110 term110 term110 term107 term110). Qed.
Lemma lem2722024 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2722025 : term257 = term258.
Proof. exact (@lem2722024 (NUMERAL 0) term111). Qed.
Lemma lem2722026 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2722027 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2722028 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2722027 h1) (fun h1 : term258 = True => @lem2722026)). Qed.
Lemma lem2722029 : term258 = True.
Proof. exact (EQ_MP (@lem2722028) (@lem2722026)). Qed.
Lemma lem2722030 : term257 = True.
Proof. exact (TRANS (@lem2722025) (@lem2722029)). Qed.
Lemma lem2722031 : True = term257.
Proof. exact (SYM (@lem2722030)). Qed.
Lemma lem2722032 : term257.
Proof. exact (EQ_MP (@lem2722031) (@lem0)). Qed.
Lemma lem2722033 : term466.
Proof. exact (@lem2722022 (@lem2722032)). Qed.
Lemma lem2722035 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2722036 : term257 = term258.
Proof. exact (@lem2722035 (NUMERAL 0) term111). Qed.
Lemma lem2722037 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2722038 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2722039 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2722038 h1) (fun h1 : term258 = True => @lem2722037)). Qed.
Lemma lem2722040 : term258 = True.
Proof. exact (EQ_MP (@lem2722039) (@lem2722037)). Qed.
Lemma lem2722041 : term257 = True.
Proof. exact (TRANS (@lem2722036) (@lem2722040)). Qed.
Lemma lem2722042 : True = term257.
Proof. exact (SYM (@lem2722041)). Qed.
Lemma lem2722043 : term257.
Proof. exact (EQ_MP (@lem2722042) (@lem0)). Qed.
Lemma lem2722044 : term467.
Proof. exact (@lem2722033 (@lem2722043)). Qed.
Lemma lem2722046 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2722047 : term257 = term258.
Proof. exact (@lem2722046 (NUMERAL 0) term111). Qed.
Lemma lem2722048 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2722049 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2722050 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2722049 h1) (fun h1 : term258 = True => @lem2722048)). Qed.
Lemma lem2722051 : term258 = True.
Proof. exact (EQ_MP (@lem2722050) (@lem2722048)). Qed.
Lemma lem2722052 : term257 = True.
Proof. exact (TRANS (@lem2722047) (@lem2722051)). Qed.
Lemma lem2722053 : True = term257.
Proof. exact (SYM (@lem2722052)). Qed.
Lemma lem2722054 : term257.
Proof. exact (EQ_MP (@lem2722053) (@lem0)). Qed.
Lemma lem2722055 : term468.
Proof. exact (@lem2722044 (@lem2722054)). Qed.
Lemma lem2722057 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2722058 : term202 = term203.
Proof. exact (@lem2722057 term111 term111). Qed.
Lemma lem2722059 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2722060 : term205 = term111.
Proof. exact (EQ_MP (@lem2722059) (@lem940073)). Qed.
Lemma lem2722061 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2722062 : term203 = term110.
Proof. exact (MK_COMB (@lem2722061) (@lem2722060)). Qed.
Lemma lem2722063 : term202 = term110.
Proof. exact (TRANS (@lem2722058) (@lem2722062)). Qed.
Lemma lem2722065 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2722066 : term215 = term220.
Proof. exact (@lem2722065 term111 term111). Qed.
Lemma lem2722067 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2722068 : term205 = term111.
Proof. exact (EQ_MP (@lem2722067) (@lem940073)). Qed.
Lemma lem2722069 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2722070 : term203 = term110.
Proof. exact (MK_COMB (@lem2722069) (@lem2722068)). Qed.
Lemma lem2722071 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2722072 : term220 = term193.
Proof. exact (MK_COMB (@lem2722071) (@lem2722070)). Qed.
Lemma lem2722073 : term215 = term193.
Proof. exact (TRANS (@lem2722066) (@lem2722072)). Qed.
Lemma lem2722074 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2722075 : term469 = term461.
Proof. exact (MK_COMB (@lem2722074) (@lem2722073)). Qed.
Lemma lem2722076 : term470 = term463.
Proof. exact (MK_COMB (@lem2722075) (@lem2722063)). Qed.
Lemma lem2722078 (m : nat) : (term471 m) = term107.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2722079 : term463 = term107.
Proof. exact (@lem2722078 term111). Qed.
Lemma lem2722080 : term470 = term107.
Proof. exact (TRANS (@lem2722076) (@lem2722079)). Qed.
Lemma lem2722081 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2722082 : term472 = term267.
Proof. exact (MK_COMB (@lem2722081) (@lem2722080)). Qed.
Lemma lem2722083 : term110 = term110.
Proof. exact (eq_refl term110). Qed.
Lemma lem2722084 : term473 = term269.
Proof. exact (MK_COMB (@lem2722082) (@lem2722083)). Qed.
Lemma lem2722086 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2722087 : term269 = term107.
Proof. exact (@lem2722086 term111). Qed.
Lemma lem2722088 : term473 = term107.
Proof. exact (TRANS (@lem2722084) (@lem2722087)). Qed.
Lemma lem2722090 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2722091 : term202 = term203.
Proof. exact (@lem2722090 term111 term111). Qed.
Lemma lem2722092 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2722093 : term205 = term111.
Proof. exact (EQ_MP (@lem2722092) (@lem940073)). Qed.
Lemma lem2722094 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2722095 : term203 = term110.
Proof. exact (MK_COMB (@lem2722094) (@lem2722093)). Qed.
Lemma lem2722096 : term202 = term110.
Proof. exact (TRANS (@lem2722091) (@lem2722095)). Qed.
Lemma lem2722097 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2722098 : term271 = term269.
Proof. exact (MK_COMB (@lem2722097) (@lem2722096)). Qed.
Lemma lem2722100 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2722101 : term269 = term107.
Proof. exact (@lem2722100 term111). Qed.
Lemma lem2722102 : term271 = term107.
Proof. exact (TRANS (@lem2722098) (@lem2722101)). Qed.
Lemma lem2722103 : term107 = term271.
Proof. exact (SYM (@lem2722102)). Qed.
Lemma lem2722104 : term473 = term271.
Proof. exact (TRANS (@lem2722088) (@lem2722103)). Qed.
Lemma lem2722105 : term464 = term190.
Proof. exact (@lem2722055 (@lem2722104)). Qed.
Lemma lem2722106 : term463 = term190.
Proof. exact (TRANS (@lem2722021) (@lem2722105)). Qed.
Lemma lem2722108 (x : real) : (term209 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2722109 : term190 = term107.
Proof. exact (@lem2722108 term107). Qed.
Lemma lem2722110 : term463 = term107.
Proof. exact (TRANS (@lem2722106) (@lem2722109)). Qed.
Lemma lem2722111 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2722112 : term474 = term267.
Proof. exact (MK_COMB (@lem2722111) (@lem2722110)). Qed.
Lemma lem2722113 (n : int) : (term104 n) = (term104 n).
Proof. exact (eq_refl (term104 n)). Qed.
Lemma lem2722114 (n : int) : (term460 n) = (term475 n).
Proof. exact (MK_COMB (@lem2722112) (@lem2722113 n)). Qed.
Lemma lem2722115 (n : int) : (term459 n) = (term475 n).
Proof. exact (TRANS (@lem2722012 n) (@lem2722114 n)). Qed.
Lemma lem2722116 (n : int) : (term475 n) = term107.
Proof. exact (@lem1982719 (term104 n)). Qed.
Lemma lem2722117 (n : int) : (term459 n) = term107.
Proof. exact (TRANS (@lem2722115 n) (@lem2722116 n)). Qed.
Lemma lem2722118 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2722119 (n : int) : (term476 n) = term139.
Proof. exact (MK_COMB (@lem2722118) (@lem2722117 n)). Qed.
Lemma lem2722120 : term193 = term193.
Proof. exact (eq_refl term193). Qed.
Lemma lem2722121 (n : int) : (term458 n) = term477.
Proof. exact (MK_COMB (@lem2722119 n) (@lem2722120)). Qed.
Lemma lem2722122 (n : int) : (term457 n) = term477.
Proof. exact (TRANS (@lem2722011 n) (@lem2722121 n)). Qed.
Lemma lem2722123 : term477 = term193.
Proof. exact (@lem1982721 term193). Qed.
Lemma lem2722124 (n : int) : (term457 n) = term193.
Proof. exact (TRANS (@lem2722122 n) (@lem2722123)). Qed.
Lemma lem2722125 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2722126 (n : int) : (term478 n) = term479.
Proof. exact (MK_COMB (@lem2722125) (@lem2722124 n)). Qed.
Lemma lem2722127 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2722128 (n : int) : (term456 n) = term480.
Proof. exact (MK_COMB (@lem2722126 n) (@lem2722127)). Qed.
Lemma lem2722129 (n : int) (h1 : term597 n) : term480.
Proof. exact (EQ_MP (@lem2722128 n) (@lem2722010 n h1)). Qed.
Lemma lem2722131 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2722132 : term480 = term481.
Proof. exact (@lem2722131 term107 term193). Qed.
Lemma lem2722134 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2722135 : term193 = term194.
Proof. exact (@lem2722134 term111). Qed.
Lemma lem2722137 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2722138 : term107 = term190.
Proof. exact (@lem2722137 (NUMERAL 0)). Qed.
Lemma lem2722139 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2722140 : term482 = term483.
Proof. exact (MK_COMB (@lem2722139) (@lem2722138)). Qed.
Lemma lem2722141 : term481 = term484.
Proof. exact (MK_COMB (@lem2722140) (@lem2722135)). Qed.
Lemma lem2722142 : term485.
Proof. exact (@lem1980026 term107 term110 term193 term110). Qed.
Lemma lem2722144 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2722145 : term257 = term258.
Proof. exact (@lem2722144 (NUMERAL 0) term111). Qed.
Lemma lem2722146 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2722147 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2722148 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2722147 h1) (fun h1 : term258 = True => @lem2722146)). Qed.
Lemma lem2722149 : term258 = True.
Proof. exact (EQ_MP (@lem2722148) (@lem2722146)). Qed.
Lemma lem2722150 : term257 = True.
Proof. exact (TRANS (@lem2722145) (@lem2722149)). Qed.
Lemma lem2722151 : True = term257.
Proof. exact (SYM (@lem2722150)). Qed.
Lemma lem2722152 : term257.
Proof. exact (EQ_MP (@lem2722151) (@lem0)). Qed.
Lemma lem2722153 : term486.
Proof. exact (@lem2722142 (@lem2722152)). Qed.
Lemma lem2722155 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2722156 : term257 = term258.
Proof. exact (@lem2722155 (NUMERAL 0) term111). Qed.
Lemma lem2722157 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2722158 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2722159 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2722158 h1) (fun h1 : term258 = True => @lem2722157)). Qed.
Lemma lem2722160 : term258 = True.
Proof. exact (EQ_MP (@lem2722159) (@lem2722157)). Qed.
Lemma lem2722161 : term257 = True.
Proof. exact (TRANS (@lem2722156) (@lem2722160)). Qed.
Lemma lem2722162 : True = term257.
Proof. exact (SYM (@lem2722161)). Qed.
Lemma lem2722163 : term257.
Proof. exact (EQ_MP (@lem2722162) (@lem0)). Qed.
Lemma lem2722164 : term484 = term487.
Proof. exact (@lem2722153 (@lem2722163)). Qed.
Lemma lem2722166 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2722167 : term215 = term220.
Proof. exact (@lem2722166 term111 term111). Qed.
Lemma lem2722168 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2722169 : term205 = term111.
Proof. exact (EQ_MP (@lem2722168) (@lem940073)). Qed.
Lemma lem2722170 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2722171 : term203 = term110.
Proof. exact (MK_COMB (@lem2722170) (@lem2722169)). Qed.
Lemma lem2722172 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2722173 : term220 = term193.
Proof. exact (MK_COMB (@lem2722172) (@lem2722171)). Qed.
Lemma lem2722174 : term215 = term193.
Proof. exact (TRANS (@lem2722167) (@lem2722173)). Qed.
Lemma lem2722176 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2722177 : term269 = term107.
Proof. exact (@lem2722176 term111). Qed.
Lemma lem2722178 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2722179 : term488 = term482.
Proof. exact (MK_COMB (@lem2722178) (@lem2722177)). Qed.
Lemma lem2722180 : term487 = term481.
Proof. exact (MK_COMB (@lem2722179) (@lem2722174)). Qed.
Lemma lem2722182 (m : nat) (n : nat) : (term489 m n) = (term490 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2722183 : term481 = term491.
Proof. exact (@lem2722182 (NUMERAL 0) term111). Qed.
Lemma lem2722184 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2722185 (h1 : term259 = (BIT1 0)) : (term111 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2722186 : (term259 = (BIT1 0)) = ((term111 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2722185 h1) (fun h1 : (term111 = (NUMERAL 0)) = False => @lem2722184)). Qed.
Lemma lem2722187 : (term111 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2722186) (@lem2722184)). Qed.
Lemma lem2722188 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2722189 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2722190 : term492 = (and True).
Proof. exact (MK_COMB (@lem2722189) (@lem2722188)). Qed.
Lemma lem2722191 : term491 = (True /\ False).
Proof. exact (MK_COMB (@lem2722190) (@lem2722187)). Qed.
Lemma lem2722193 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2722194 : term491 = False.
Proof. exact (TRANS (@lem2722191) (@lem2722193)). Qed.
Lemma lem2722195 : term481 = False.
Proof. exact (TRANS (@lem2722183) (@lem2722194)). Qed.
Lemma lem2722196 : term487 = False.
Proof. exact (TRANS (@lem2722180) (@lem2722195)). Qed.
Lemma lem2722197 : term484 = False.
Proof. exact (TRANS (@lem2722164) (@lem2722196)). Qed.
Lemma lem2722198 : term481 = False.
Proof. exact (TRANS (@lem2722141) (@lem2722197)). Qed.
Lemma lem2722199 : term480 = False.
Proof. exact (TRANS (@lem2722132) (@lem2722198)). Qed.
Lemma lem2722200 (n : int) (h1 : term597 n) : False.
Proof. exact (EQ_MP (@lem2722199) (@lem2722129 n h1)). Qed.
Lemma lem2722201 (n : int) (h1 : term598 n) : term598 n.
Proof. exact (h1). Qed.
Lemma lem2722202 (n : int) (h1 : term598 n) : term378 n.
Proof. exact (proj2 (@lem2722201 n h1)). Qed.
Lemma lem2722203 (n : int) (h1 : term598 n) : (term223 n) = term107.
Proof. exact (proj1 (@lem2722201 n h1)). Qed.
Lemma lem2722204 (n : int) (h1 : term598 n) : term237 n.
Proof. exact (proj2 (@lem2722202 n h1)). Qed.
Lemma lem2722207 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2722208 : term433 = term257.
Proof. exact (@lem2722207 term107 term110). Qed.
Lemma lem2722210 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2722211 : term110 = term214.
Proof. exact (@lem2722210 term111). Qed.
Lemma lem2722213 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2722214 : term107 = term190.
Proof. exact (@lem2722213 (NUMERAL 0)). Qed.
Lemma lem2722215 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2722216 : term434 = term435.
Proof. exact (MK_COMB (@lem2722215) (@lem2722214)). Qed.
Lemma lem2722217 : term257 = term436.
Proof. exact (MK_COMB (@lem2722216) (@lem2722211)). Qed.
Lemma lem2722218 : term437.
Proof. exact (@lem1980255 term107 term110 term110 term110). Qed.
Lemma lem2722220 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2722221 : term257 = term258.
Proof. exact (@lem2722220 (NUMERAL 0) term111). Qed.
Lemma lem2722222 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2722223 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2722224 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2722223 h1) (fun h1 : term258 = True => @lem2722222)). Qed.
Lemma lem2722225 : term258 = True.
Proof. exact (EQ_MP (@lem2722224) (@lem2722222)). Qed.
Lemma lem2722226 : term257 = True.
Proof. exact (TRANS (@lem2722221) (@lem2722225)). Qed.
Lemma lem2722227 : True = term257.
Proof. exact (SYM (@lem2722226)). Qed.
Lemma lem2722228 : term257.
Proof. exact (EQ_MP (@lem2722227) (@lem0)). Qed.
Lemma lem2722229 : term438.
Proof. exact (@lem2722218 (@lem2722228)). Qed.
Lemma lem2722231 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2722232 : term257 = term258.
Proof. exact (@lem2722231 (NUMERAL 0) term111). Qed.
Lemma lem2722233 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2722234 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2722235 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2722234 h1) (fun h1 : term258 = True => @lem2722233)). Qed.
Lemma lem2722236 : term258 = True.
Proof. exact (EQ_MP (@lem2722235) (@lem2722233)). Qed.
Lemma lem2722237 : term257 = True.
Proof. exact (TRANS (@lem2722232) (@lem2722236)). Qed.
Lemma lem2722238 : True = term257.
Proof. exact (SYM (@lem2722237)). Qed.
Lemma lem2722239 : term257.
Proof. exact (EQ_MP (@lem2722238) (@lem0)). Qed.
Lemma lem2722240 : term436 = term439.
Proof. exact (@lem2722229 (@lem2722239)). Qed.
Lemma lem2722242 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2722243 : term202 = term203.
Proof. exact (@lem2722242 term111 term111). Qed.
Lemma lem2722244 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2722245 : term205 = term111.
Proof. exact (EQ_MP (@lem2722244) (@lem940073)). Qed.
Lemma lem2722246 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2722247 : term203 = term110.
Proof. exact (MK_COMB (@lem2722246) (@lem2722245)). Qed.
Lemma lem2722248 : term202 = term110.
Proof. exact (TRANS (@lem2722243) (@lem2722247)). Qed.
Lemma lem2722250 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2722251 : term269 = term107.
Proof. exact (@lem2722250 term111). Qed.
Lemma lem2722252 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2722253 : term440 = term434.
Proof. exact (MK_COMB (@lem2722252) (@lem2722251)). Qed.
Lemma lem2722254 : term439 = term257.
Proof. exact (MK_COMB (@lem2722253) (@lem2722248)). Qed.
Lemma lem2722256 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2722257 : term257 = term258.
Proof. exact (@lem2722256 (NUMERAL 0) term111). Qed.
Lemma lem2722258 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2722259 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2722260 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2722259 h1) (fun h1 : term258 = True => @lem2722258)). Qed.
Lemma lem2722261 : term258 = True.
Proof. exact (EQ_MP (@lem2722260) (@lem2722258)). Qed.
Lemma lem2722262 : term257 = True.
Proof. exact (TRANS (@lem2722257) (@lem2722261)). Qed.
Lemma lem2722263 : term439 = True.
Proof. exact (TRANS (@lem2722254) (@lem2722262)). Qed.
Lemma lem2722264 : term436 = True.
Proof. exact (TRANS (@lem2722240) (@lem2722263)). Qed.
Lemma lem2722265 : term257 = True.
Proof. exact (TRANS (@lem2722217) (@lem2722264)). Qed.
Lemma lem2722266 : term433 = True.
Proof. exact (TRANS (@lem2722208) (@lem2722265)). Qed.
Lemma lem2722267 : True = term433.
Proof. exact (SYM (@lem2722266)). Qed.
Lemma lem2722268 : term433.
Proof. exact (EQ_MP (@lem2722267) (@lem0)). Qed.
Lemma lem2722269 (n : int) (h1 : term598 n) : term441 n.
Proof. exact (conj (@lem2722268) (@lem2722204 n h1)). Qed.
Lemma lem2722271 (x : real) (y : real) : term442 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2722272 (n : int) : term443 n.
Proof. exact (@lem2722271 term110 (term233 n)). Qed.
Lemma lem2722273 (n : int) (h1 : term598 n) : term444 n.
Proof. exact (@lem2722272 n (@lem2722269 n h1)). Qed.
Lemma lem2722274 (n : int) : (term445 n) = (term233 n).
Proof. exact (@lem1982733 (term233 n)). Qed.
Lemma lem2722275 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2722276 (n : int) : (term446 n) = (term236 n).
Proof. exact (MK_COMB (@lem2722275) (@lem2722274 n)). Qed.
Lemma lem2722277 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2722278 (n : int) : (term444 n) = (term237 n).
Proof. exact (MK_COMB (@lem2722276 n) (@lem2722277)). Qed.
Lemma lem2722279 (n : int) (h1 : term598 n) : term237 n.
Proof. exact (EQ_MP (@lem2722278 n) (@lem2722273 n h1)). Qed.
Lemma lem2722281 (y : real) : term447 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2722282 (n : int) : term499 n.
Proof. exact (@lem2722281 (term223 n)). Qed.
Lemma lem2722283 (n : int) (h1 : term598 n) : term500 n.
Proof. exact (@lem2722282 n (@lem2722203 n h1)). Qed.
Lemma lem2722284 (n : int) (h1 : term598 n) : term501 n.
Proof. exact (@lem2722283 n h1 term110). Qed.
Lemma lem2722285 (n : int) : (term501 n) = ((term502 n) = term107).
Proof. exact (eq_refl (term501 n)). Qed.
Lemma lem2722286 (n : int) (h1 : term598 n) : (term502 n) = term107.
Proof. exact (EQ_MP (@lem2722285 n) (@lem2722284 n h1)). Qed.
Lemma lem2722287 (n : int) : (term502 n) = (term223 n).
Proof. exact (@lem1982733 (term223 n)). Qed.
Lemma lem2722288 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2722289 (n : int) : (term503 n) = (term225 n).
Proof. exact (MK_COMB (@lem2722288) (@lem2722287 n)). Qed.
Lemma lem2722290 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2722291 (n : int) : ((term502 n) = term107) = ((term223 n) = term107).
Proof. exact (MK_COMB (@lem2722289 n) (@lem2722290)). Qed.
Lemma lem2722292 (n : int) (h1 : term598 n) : (term223 n) = term107.
Proof. exact (EQ_MP (@lem2722291 n) (@lem2722286 n h1)). Qed.
Lemma lem2722293 (n : int) (h1 : term598 n) : term599 n.
Proof. exact (conj (@lem2722292 n h1) (@lem2722279 n h1)). Qed.
Lemma lem2722295 (x : real) (y : real) : term454 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2722296 (n : int) : term600 n.
Proof. exact (@lem2722295 (term223 n) (term233 n)). Qed.
Lemma lem2722297 (n : int) (h1 : term598 n) : term601 n.
Proof. exact (@lem2722296 n (@lem2722293 n h1)). Qed.
Lemma lem2722298 (n : int) : (term602 n) = (term603 n).
Proof. exact (@lem1982753 (term104 n) (term251 n) term193 term193). Qed.
Lemma lem2722299 (n : int) : (term459 n) = (term460 n).
Proof. exact (@lem1982715 term193 (term104 n)). Qed.
Lemma lem2722301 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2722302 : term110 = term214.
Proof. exact (@lem2722301 term111). Qed.
Lemma lem2722304 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2722305 : term193 = term194.
Proof. exact (@lem2722304 term111). Qed.
Lemma lem2722306 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2722307 : term461 = term462.
Proof. exact (MK_COMB (@lem2722306) (@lem2722305)). Qed.
Lemma lem2722308 : term463 = term464.
Proof. exact (MK_COMB (@lem2722307) (@lem2722302)). Qed.
Lemma lem2722309 : term465.
Proof. exact (@lem1981473 term193 term110 term110 term110 term107 term110). Qed.
Lemma lem2722311 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2722312 : term257 = term258.
Proof. exact (@lem2722311 (NUMERAL 0) term111). Qed.
Lemma lem2722313 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2722314 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2722315 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2722314 h1) (fun h1 : term258 = True => @lem2722313)). Qed.
Lemma lem2722316 : term258 = True.
Proof. exact (EQ_MP (@lem2722315) (@lem2722313)). Qed.
Lemma lem2722317 : term257 = True.
Proof. exact (TRANS (@lem2722312) (@lem2722316)). Qed.
Lemma lem2722318 : True = term257.
Proof. exact (SYM (@lem2722317)). Qed.
Lemma lem2722319 : term257.
Proof. exact (EQ_MP (@lem2722318) (@lem0)). Qed.
Lemma lem2722320 : term466.
Proof. exact (@lem2722309 (@lem2722319)). Qed.
Lemma lem2722322 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2722323 : term257 = term258.
Proof. exact (@lem2722322 (NUMERAL 0) term111). Qed.
Lemma lem2722324 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2722325 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2722326 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2722325 h1) (fun h1 : term258 = True => @lem2722324)). Qed.
Lemma lem2722327 : term258 = True.
Proof. exact (EQ_MP (@lem2722326) (@lem2722324)). Qed.
Lemma lem2722328 : term257 = True.
Proof. exact (TRANS (@lem2722323) (@lem2722327)). Qed.
Lemma lem2722329 : True = term257.
Proof. exact (SYM (@lem2722328)). Qed.
Lemma lem2722330 : term257.
Proof. exact (EQ_MP (@lem2722329) (@lem0)). Qed.
Lemma lem2722331 : term467.
Proof. exact (@lem2722320 (@lem2722330)). Qed.
Lemma lem2722333 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2722334 : term257 = term258.
Proof. exact (@lem2722333 (NUMERAL 0) term111). Qed.
Lemma lem2722335 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2722336 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2722337 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2722336 h1) (fun h1 : term258 = True => @lem2722335)). Qed.
Lemma lem2722338 : term258 = True.
Proof. exact (EQ_MP (@lem2722337) (@lem2722335)). Qed.
Lemma lem2722339 : term257 = True.
Proof. exact (TRANS (@lem2722334) (@lem2722338)). Qed.
Lemma lem2722340 : True = term257.
Proof. exact (SYM (@lem2722339)). Qed.
Lemma lem2722341 : term257.
Proof. exact (EQ_MP (@lem2722340) (@lem0)). Qed.
Lemma lem2722342 : term468.
Proof. exact (@lem2722331 (@lem2722341)). Qed.
Lemma lem2722344 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2722345 : term202 = term203.
Proof. exact (@lem2722344 term111 term111). Qed.
Lemma lem2722346 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2722347 : term205 = term111.
Proof. exact (EQ_MP (@lem2722346) (@lem940073)). Qed.
Lemma lem2722348 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2722349 : term203 = term110.
Proof. exact (MK_COMB (@lem2722348) (@lem2722347)). Qed.
Lemma lem2722350 : term202 = term110.
Proof. exact (TRANS (@lem2722345) (@lem2722349)). Qed.
Lemma lem2722352 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2722353 : term215 = term220.
Proof. exact (@lem2722352 term111 term111). Qed.
Lemma lem2722354 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2722355 : term205 = term111.
Proof. exact (EQ_MP (@lem2722354) (@lem940073)). Qed.
Lemma lem2722356 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2722357 : term203 = term110.
Proof. exact (MK_COMB (@lem2722356) (@lem2722355)). Qed.
Lemma lem2722358 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2722359 : term220 = term193.
Proof. exact (MK_COMB (@lem2722358) (@lem2722357)). Qed.
Lemma lem2722360 : term215 = term193.
Proof. exact (TRANS (@lem2722353) (@lem2722359)). Qed.
Lemma lem2722361 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2722362 : term469 = term461.
Proof. exact (MK_COMB (@lem2722361) (@lem2722360)). Qed.
Lemma lem2722363 : term470 = term463.
Proof. exact (MK_COMB (@lem2722362) (@lem2722350)). Qed.
Lemma lem2722365 (m : nat) : (term471 m) = term107.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2722366 : term463 = term107.
Proof. exact (@lem2722365 term111). Qed.
Lemma lem2722367 : term470 = term107.
Proof. exact (TRANS (@lem2722363) (@lem2722366)). Qed.
Lemma lem2722368 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2722369 : term472 = term267.
Proof. exact (MK_COMB (@lem2722368) (@lem2722367)). Qed.
Lemma lem2722370 : term110 = term110.
Proof. exact (eq_refl term110). Qed.
Lemma lem2722371 : term473 = term269.
Proof. exact (MK_COMB (@lem2722369) (@lem2722370)). Qed.
Lemma lem2722373 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2722374 : term269 = term107.
Proof. exact (@lem2722373 term111). Qed.
Lemma lem2722375 : term473 = term107.
Proof. exact (TRANS (@lem2722371) (@lem2722374)). Qed.
Lemma lem2722377 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2722378 : term202 = term203.
Proof. exact (@lem2722377 term111 term111). Qed.
Lemma lem2722379 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2722380 : term205 = term111.
Proof. exact (EQ_MP (@lem2722379) (@lem940073)). Qed.
Lemma lem2722381 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2722382 : term203 = term110.
Proof. exact (MK_COMB (@lem2722381) (@lem2722380)). Qed.
Lemma lem2722383 : term202 = term110.
Proof. exact (TRANS (@lem2722378) (@lem2722382)). Qed.
Lemma lem2722384 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2722385 : term271 = term269.
Proof. exact (MK_COMB (@lem2722384) (@lem2722383)). Qed.
Lemma lem2722387 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2722388 : term269 = term107.
Proof. exact (@lem2722387 term111). Qed.
Lemma lem2722389 : term271 = term107.
Proof. exact (TRANS (@lem2722385) (@lem2722388)). Qed.
Lemma lem2722390 : term107 = term271.
Proof. exact (SYM (@lem2722389)). Qed.
Lemma lem2722391 : term473 = term271.
Proof. exact (TRANS (@lem2722375) (@lem2722390)). Qed.
Lemma lem2722392 : term464 = term190.
Proof. exact (@lem2722342 (@lem2722391)). Qed.
Lemma lem2722393 : term463 = term190.
Proof. exact (TRANS (@lem2722308) (@lem2722392)). Qed.
Lemma lem2722395 (x : real) : (term209 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2722396 : term190 = term107.
Proof. exact (@lem2722395 term107). Qed.
Lemma lem2722397 : term463 = term107.
Proof. exact (TRANS (@lem2722393) (@lem2722396)). Qed.
Lemma lem2722398 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2722399 : term474 = term267.
Proof. exact (MK_COMB (@lem2722398) (@lem2722397)). Qed.
Lemma lem2722400 (n : int) : (term104 n) = (term104 n).
Proof. exact (eq_refl (term104 n)). Qed.
Lemma lem2722401 (n : int) : (term460 n) = (term475 n).
Proof. exact (MK_COMB (@lem2722399) (@lem2722400 n)). Qed.
Lemma lem2722402 (n : int) : (term459 n) = (term475 n).
Proof. exact (TRANS (@lem2722299 n) (@lem2722401 n)). Qed.
Lemma lem2722403 (n : int) : (term475 n) = term107.
Proof. exact (@lem1982719 (term104 n)). Qed.
Lemma lem2722404 (n : int) : (term459 n) = term107.
Proof. exact (TRANS (@lem2722402 n) (@lem2722403 n)). Qed.
Lemma lem2722405 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2722406 (n : int) : (term476 n) = term139.
Proof. exact (MK_COMB (@lem2722405) (@lem2722404 n)). Qed.
Lemma lem2722408 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2722409 : term193 = term194.
Proof. exact (@lem2722408 term111). Qed.
Lemma lem2722411 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2722412 : term193 = term194.
Proof. exact (@lem2722411 term111). Qed.
Lemma lem2722413 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2722414 : term461 = term462.
Proof. exact (MK_COMB (@lem2722413) (@lem2722412)). Qed.
Lemma lem2722415 : term604 = term605.
Proof. exact (MK_COMB (@lem2722414) (@lem2722409)). Qed.
Lemma lem2722416 : term606.
Proof. exact (@lem1981473 term193 term110 term193 term110 term308 term110). Qed.
Lemma lem2722418 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2722419 : term257 = term258.
Proof. exact (@lem2722418 (NUMERAL 0) term111). Qed.
Lemma lem2722420 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2722421 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2722422 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2722421 h1) (fun h1 : term258 = True => @lem2722420)). Qed.
Lemma lem2722423 : term258 = True.
Proof. exact (EQ_MP (@lem2722422) (@lem2722420)). Qed.
Lemma lem2722424 : term257 = True.
Proof. exact (TRANS (@lem2722419) (@lem2722423)). Qed.
Lemma lem2722425 : True = term257.
Proof. exact (SYM (@lem2722424)). Qed.
Lemma lem2722426 : term257.
Proof. exact (EQ_MP (@lem2722425) (@lem0)). Qed.
Lemma lem2722427 : term607.
Proof. exact (@lem2722416 (@lem2722426)). Qed.
Lemma lem2722429 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2722430 : term257 = term258.
Proof. exact (@lem2722429 (NUMERAL 0) term111). Qed.
Lemma lem2722431 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2722432 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2722433 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2722432 h1) (fun h1 : term258 = True => @lem2722431)). Qed.
Lemma lem2722434 : term258 = True.
Proof. exact (EQ_MP (@lem2722433) (@lem2722431)). Qed.
Lemma lem2722435 : term257 = True.
Proof. exact (TRANS (@lem2722430) (@lem2722434)). Qed.
Lemma lem2722436 : True = term257.
Proof. exact (SYM (@lem2722435)). Qed.
Lemma lem2722437 : term257.
Proof. exact (EQ_MP (@lem2722436) (@lem0)). Qed.
Lemma lem2722438 : term608.
Proof. exact (@lem2722427 (@lem2722437)). Qed.
Lemma lem2722440 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2722441 : term257 = term258.
Proof. exact (@lem2722440 (NUMERAL 0) term111). Qed.
Lemma lem2722442 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2722443 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2722444 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2722443 h1) (fun h1 : term258 = True => @lem2722442)). Qed.
Lemma lem2722445 : term258 = True.
Proof. exact (EQ_MP (@lem2722444) (@lem2722442)). Qed.
Lemma lem2722446 : term257 = True.
Proof. exact (TRANS (@lem2722441) (@lem2722445)). Qed.
Lemma lem2722447 : True = term257.
Proof. exact (SYM (@lem2722446)). Qed.
Lemma lem2722448 : term257.
Proof. exact (EQ_MP (@lem2722447) (@lem0)). Qed.
Lemma lem2722449 : term609.
Proof. exact (@lem2722438 (@lem2722448)). Qed.
Lemma lem2722451 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2722452 : term215 = term220.
Proof. exact (@lem2722451 term111 term111). Qed.
Lemma lem2722453 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2722454 : term205 = term111.
Proof. exact (EQ_MP (@lem2722453) (@lem940073)). Qed.
Lemma lem2722455 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2722456 : term203 = term110.
Proof. exact (MK_COMB (@lem2722455) (@lem2722454)). Qed.
Lemma lem2722457 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2722458 : term220 = term193.
Proof. exact (MK_COMB (@lem2722457) (@lem2722456)). Qed.
Lemma lem2722459 : term215 = term193.
Proof. exact (TRANS (@lem2722452) (@lem2722458)). Qed.
Lemma lem2722461 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2722462 : term215 = term220.
Proof. exact (@lem2722461 term111 term111). Qed.
Lemma lem2722463 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2722464 : term205 = term111.
Proof. exact (EQ_MP (@lem2722463) (@lem940073)). Qed.
Lemma lem2722465 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2722466 : term203 = term110.
Proof. exact (MK_COMB (@lem2722465) (@lem2722464)). Qed.
Lemma lem2722467 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2722468 : term220 = term193.
Proof. exact (MK_COMB (@lem2722467) (@lem2722466)). Qed.
Lemma lem2722469 : term215 = term193.
Proof. exact (TRANS (@lem2722462) (@lem2722468)). Qed.
Lemma lem2722470 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2722471 : term469 = term461.
Proof. exact (MK_COMB (@lem2722470) (@lem2722469)). Qed.
Lemma lem2722472 : term610 = term604.
Proof. exact (MK_COMB (@lem2722471) (@lem2722459)). Qed.
Lemma lem2722473 : term604 = term574.
Proof. exact (@lem1367763 term111 term111). Qed.
Lemma lem2722474 : term285 = term286.
Proof. exact (@lem706885). Qed.
Lemma lem2722475 : (term285 = term286) = (term287 = term288).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term286). Qed.
Lemma lem2722476 : term287 = term288.
Proof. exact (EQ_MP (@lem2722475) (@lem2722474)). Qed.
Lemma lem2722477 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2722478 : term284 = term279.
Proof. exact (MK_COMB (@lem2722477) (@lem2722476)). Qed.
Lemma lem2722479 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2722480 : term574 = term308.
Proof. exact (MK_COMB (@lem2722479) (@lem2722478)). Qed.
Lemma lem2722481 : term604 = term308.
Proof. exact (TRANS (@lem2722473) (@lem2722480)). Qed.
Lemma lem2722482 : term610 = term308.
Proof. exact (TRANS (@lem2722472) (@lem2722481)). Qed.
Lemma lem2722483 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2722484 : term611 = term612.
Proof. exact (MK_COMB (@lem2722483) (@lem2722482)). Qed.
Lemma lem2722485 : term110 = term110.
Proof. exact (eq_refl term110). Qed.
Lemma lem2722486 : term613 = term544.
Proof. exact (MK_COMB (@lem2722484) (@lem2722485)). Qed.
Lemma lem2722488 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2722489 : term544 = term545.
Proof. exact (@lem2722488 term288 term111). Qed.
Lemma lem2722490 : term294 = term286.
Proof. exact (@lem996237 term286). Qed.
Lemma lem2722491 : (term294 = term286) = (term295 = term288).
Proof. exact (@lem1007663 term286 (BIT1 0) term286). Qed.
Lemma lem2722492 : term295 = term288.
Proof. exact (EQ_MP (@lem2722491) (@lem2722490)). Qed.
Lemma lem2722493 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2722494 : term293 = term279.
Proof. exact (MK_COMB (@lem2722493) (@lem2722492)). Qed.
Lemma lem2722495 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2722496 : term545 = term308.
Proof. exact (MK_COMB (@lem2722495) (@lem2722494)). Qed.
Lemma lem2722497 : term544 = term308.
Proof. exact (TRANS (@lem2722489) (@lem2722496)). Qed.
Lemma lem2722498 : term613 = term308.
Proof. exact (TRANS (@lem2722486) (@lem2722497)). Qed.
Lemma lem2722500 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2722501 : term202 = term203.
Proof. exact (@lem2722500 term111 term111). Qed.
Lemma lem2722502 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2722503 : term205 = term111.
Proof. exact (EQ_MP (@lem2722502) (@lem940073)). Qed.
Lemma lem2722504 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2722505 : term203 = term110.
Proof. exact (MK_COMB (@lem2722504) (@lem2722503)). Qed.
Lemma lem2722506 : term202 = term110.
Proof. exact (TRANS (@lem2722501) (@lem2722505)). Qed.
Lemma lem2722507 : term612 = term612.
Proof. exact (eq_refl term612). Qed.
Lemma lem2722508 : term614 = term544.
Proof. exact (MK_COMB (@lem2722507) (@lem2722506)). Qed.
Lemma lem2722510 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2722511 : term544 = term545.
Proof. exact (@lem2722510 term288 term111). Qed.
Lemma lem2722512 : term294 = term286.
Proof. exact (@lem996237 term286). Qed.
Lemma lem2722513 : (term294 = term286) = (term295 = term288).
Proof. exact (@lem1007663 term286 (BIT1 0) term286). Qed.
Lemma lem2722514 : term295 = term288.
Proof. exact (EQ_MP (@lem2722513) (@lem2722512)). Qed.
Lemma lem2722515 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2722516 : term293 = term279.
Proof. exact (MK_COMB (@lem2722515) (@lem2722514)). Qed.
Lemma lem2722517 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2722518 : term545 = term308.
Proof. exact (MK_COMB (@lem2722517) (@lem2722516)). Qed.
Lemma lem2722519 : term544 = term308.
Proof. exact (TRANS (@lem2722511) (@lem2722518)). Qed.
Lemma lem2722520 : term614 = term308.
Proof. exact (TRANS (@lem2722508) (@lem2722519)). Qed.
Lemma lem2722521 : term308 = term614.
Proof. exact (SYM (@lem2722520)). Qed.
Lemma lem2722522 : term613 = term614.
Proof. exact (TRANS (@lem2722498) (@lem2722521)). Qed.
Lemma lem2722523 : term605 = term311.
Proof. exact (@lem2722449 (@lem2722522)). Qed.
Lemma lem2722524 : term604 = term311.
Proof. exact (TRANS (@lem2722415) (@lem2722523)). Qed.
Lemma lem2722526 (x : real) : (term209 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2722527 : term311 = term308.
Proof. exact (@lem2722526 term308). Qed.
Lemma lem2722528 : term604 = term308.
Proof. exact (TRANS (@lem2722524) (@lem2722527)). Qed.
Lemma lem2722529 (n : int) : (term603 n) = term535.
Proof. exact (MK_COMB (@lem2722406 n) (@lem2722528)). Qed.
Lemma lem2722530 (n : int) : (term602 n) = term535.
Proof. exact (TRANS (@lem2722298 n) (@lem2722529 n)). Qed.
Lemma lem2722531 : term535 = term308.
Proof. exact (@lem1982721 term308). Qed.
Lemma lem2722532 (n : int) : (term602 n) = term308.
Proof. exact (TRANS (@lem2722530 n) (@lem2722531)). Qed.
Lemma lem2722533 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2722534 (n : int) : (term615 n) = term537.
Proof. exact (MK_COMB (@lem2722533) (@lem2722532 n)). Qed.
Lemma lem2722535 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2722536 (n : int) : (term601 n) = term538.
Proof. exact (MK_COMB (@lem2722534 n) (@lem2722535)). Qed.
Lemma lem2722537 (n : int) (h1 : term598 n) : term538.
Proof. exact (EQ_MP (@lem2722536 n) (@lem2722297 n h1)). Qed.
Lemma lem2722539 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2722540 : term538 = term539.
Proof. exact (@lem2722539 term107 term308). Qed.
Lemma lem2722542 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2722543 : term308 = term311.
Proof. exact (@lem2722542 term288). Qed.
Lemma lem2722545 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2722546 : term107 = term190.
Proof. exact (@lem2722545 (NUMERAL 0)). Qed.
Lemma lem2722547 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2722548 : term482 = term483.
Proof. exact (MK_COMB (@lem2722547) (@lem2722546)). Qed.
Lemma lem2722549 : term539 = term540.
Proof. exact (MK_COMB (@lem2722548) (@lem2722543)). Qed.
Lemma lem2722550 : term541.
Proof. exact (@lem1980026 term107 term110 term308 term110). Qed.
Lemma lem2722552 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2722553 : term257 = term258.
Proof. exact (@lem2722552 (NUMERAL 0) term111). Qed.
Lemma lem2722554 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2722555 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2722556 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2722555 h1) (fun h1 : term258 = True => @lem2722554)). Qed.
Lemma lem2722557 : term258 = True.
Proof. exact (EQ_MP (@lem2722556) (@lem2722554)). Qed.
Lemma lem2722558 : term257 = True.
Proof. exact (TRANS (@lem2722553) (@lem2722557)). Qed.
Lemma lem2722559 : True = term257.
Proof. exact (SYM (@lem2722558)). Qed.
Lemma lem2722560 : term257.
Proof. exact (EQ_MP (@lem2722559) (@lem0)). Qed.
Lemma lem2722561 : term542.
Proof. exact (@lem2722550 (@lem2722560)). Qed.
Lemma lem2722563 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2722564 : term257 = term258.
Proof. exact (@lem2722563 (NUMERAL 0) term111). Qed.
Lemma lem2722565 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2722566 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2722567 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2722566 h1) (fun h1 : term258 = True => @lem2722565)). Qed.
Lemma lem2722568 : term258 = True.
Proof. exact (EQ_MP (@lem2722567) (@lem2722565)). Qed.
Lemma lem2722569 : term257 = True.
Proof. exact (TRANS (@lem2722564) (@lem2722568)). Qed.
Lemma lem2722570 : True = term257.
Proof. exact (SYM (@lem2722569)). Qed.
Lemma lem2722571 : term257.
Proof. exact (EQ_MP (@lem2722570) (@lem0)). Qed.
Lemma lem2722572 : term540 = term543.
Proof. exact (@lem2722561 (@lem2722571)). Qed.
Lemma lem2722574 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2722575 : term544 = term545.
Proof. exact (@lem2722574 term288 term111). Qed.
Lemma lem2722576 : term294 = term286.
Proof. exact (@lem996237 term286). Qed.
Lemma lem2722577 : (term294 = term286) = (term295 = term288).
Proof. exact (@lem1007663 term286 (BIT1 0) term286). Qed.
Lemma lem2722578 : term295 = term288.
Proof. exact (EQ_MP (@lem2722577) (@lem2722576)). Qed.
Lemma lem2722579 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2722580 : term293 = term279.
Proof. exact (MK_COMB (@lem2722579) (@lem2722578)). Qed.
Lemma lem2722581 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2722582 : term545 = term308.
Proof. exact (MK_COMB (@lem2722581) (@lem2722580)). Qed.
Lemma lem2722583 : term544 = term308.
Proof. exact (TRANS (@lem2722575) (@lem2722582)). Qed.
Lemma lem2722585 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2722586 : term269 = term107.
Proof. exact (@lem2722585 term111). Qed.
Lemma lem2722587 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2722588 : term488 = term482.
Proof. exact (MK_COMB (@lem2722587) (@lem2722586)). Qed.
Lemma lem2722589 : term543 = term539.
Proof. exact (MK_COMB (@lem2722588) (@lem2722583)). Qed.
Lemma lem2722591 (m : nat) (n : nat) : (term489 m n) = (term490 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2722592 : term539 = term546.
Proof. exact (@lem2722591 (NUMERAL 0) term288). Qed.
Lemma lem2722593 : term547 = term286.
Proof. exact (@lem912803). Qed.
Lemma lem2722594 (h1 : term547 = term286) : (term288 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term286 h1). Qed.
Lemma lem2722595 : (term547 = term286) = ((term288 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term547 = term286 => @lem2722594 h1) (fun h1 : (term288 = (NUMERAL 0)) = False => @lem2722593)). Qed.
Lemma lem2722596 : (term288 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2722595) (@lem2722593)). Qed.
Lemma lem2722597 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2722598 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2722599 : term492 = (and True).
Proof. exact (MK_COMB (@lem2722598) (@lem2722597)). Qed.
Lemma lem2722600 : term546 = (True /\ False).
Proof. exact (MK_COMB (@lem2722599) (@lem2722596)). Qed.
Lemma lem2722602 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2722603 : term546 = False.
Proof. exact (TRANS (@lem2722600) (@lem2722602)). Qed.
Lemma lem2722604 : term539 = False.
Proof. exact (TRANS (@lem2722592) (@lem2722603)). Qed.
Lemma lem2722605 : term543 = False.
Proof. exact (TRANS (@lem2722589) (@lem2722604)). Qed.
Lemma lem2722606 : term540 = False.
Proof. exact (TRANS (@lem2722572) (@lem2722605)). Qed.
Lemma lem2722607 : term539 = False.
Proof. exact (TRANS (@lem2722549) (@lem2722606)). Qed.
Lemma lem2722608 : term538 = False.
Proof. exact (TRANS (@lem2722540) (@lem2722607)). Qed.
Lemma lem2722609 (n : int) (h1 : term598 n) : False.
Proof. exact (EQ_MP (@lem2722608) (@lem2722537 n h1)). Qed.
Lemma lem2722610 (n : int) (h1 : term383 n) : False.
Proof. exact (or_elim (@lem2721913 n h1) (fun h0 : term597 n => @lem2722200 n h0) (fun h0 : term598 n => @lem2722609 n h0)). Qed.
Lemma lem2722611 (n : int) (h1 : term381 n) : term381 n.
Proof. exact (h1). Qed.
Lemma lem2722612 (n : int) (h1 : term616 n) : term616 n.
Proof. exact (h1). Qed.
Lemma lem2722613 (n : int) (h1 : term616 n) : term379 n.
Proof. exact (proj2 (@lem2722612 n h1)). Qed.
Lemma lem2722614 (n : int) (h1 : term616 n) : (term104 n) = term107.
Proof. exact (proj1 (@lem2722612 n h1)). Qed.
Lemma lem2722615 (n : int) (h1 : term616 n) : term237 n.
Proof. exact (proj2 (@lem2722613 n h1)). Qed.
Lemma lem2722618 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2722619 : term433 = term257.
Proof. exact (@lem2722618 term107 term110). Qed.
Lemma lem2722621 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2722622 : term110 = term214.
Proof. exact (@lem2722621 term111). Qed.
Lemma lem2722624 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2722625 : term107 = term190.
Proof. exact (@lem2722624 (NUMERAL 0)). Qed.
Lemma lem2722626 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2722627 : term434 = term435.
Proof. exact (MK_COMB (@lem2722626) (@lem2722625)). Qed.
Lemma lem2722628 : term257 = term436.
Proof. exact (MK_COMB (@lem2722627) (@lem2722622)). Qed.
Lemma lem2722629 : term437.
Proof. exact (@lem1980255 term107 term110 term110 term110). Qed.
Lemma lem2722631 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2722632 : term257 = term258.
Proof. exact (@lem2722631 (NUMERAL 0) term111). Qed.
Lemma lem2722633 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2722634 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2722635 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2722634 h1) (fun h1 : term258 = True => @lem2722633)). Qed.
Lemma lem2722636 : term258 = True.
Proof. exact (EQ_MP (@lem2722635) (@lem2722633)). Qed.
Lemma lem2722637 : term257 = True.
Proof. exact (TRANS (@lem2722632) (@lem2722636)). Qed.
Lemma lem2722638 : True = term257.
Proof. exact (SYM (@lem2722637)). Qed.
Lemma lem2722639 : term257.
Proof. exact (EQ_MP (@lem2722638) (@lem0)). Qed.
Lemma lem2722640 : term438.
Proof. exact (@lem2722629 (@lem2722639)). Qed.
Lemma lem2722642 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2722643 : term257 = term258.
Proof. exact (@lem2722642 (NUMERAL 0) term111). Qed.
Lemma lem2722644 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2722645 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2722646 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2722645 h1) (fun h1 : term258 = True => @lem2722644)). Qed.
Lemma lem2722647 : term258 = True.
Proof. exact (EQ_MP (@lem2722646) (@lem2722644)). Qed.
Lemma lem2722648 : term257 = True.
Proof. exact (TRANS (@lem2722643) (@lem2722647)). Qed.
Lemma lem2722649 : True = term257.
Proof. exact (SYM (@lem2722648)). Qed.
Lemma lem2722650 : term257.
Proof. exact (EQ_MP (@lem2722649) (@lem0)). Qed.
Lemma lem2722651 : term436 = term439.
Proof. exact (@lem2722640 (@lem2722650)). Qed.
Lemma lem2722653 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2722654 : term202 = term203.
Proof. exact (@lem2722653 term111 term111). Qed.
Lemma lem2722655 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2722656 : term205 = term111.
Proof. exact (EQ_MP (@lem2722655) (@lem940073)). Qed.
Lemma lem2722657 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2722658 : term203 = term110.
Proof. exact (MK_COMB (@lem2722657) (@lem2722656)). Qed.
Lemma lem2722659 : term202 = term110.
Proof. exact (TRANS (@lem2722654) (@lem2722658)). Qed.
Lemma lem2722661 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2722662 : term269 = term107.
Proof. exact (@lem2722661 term111). Qed.
Lemma lem2722663 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2722664 : term440 = term434.
Proof. exact (MK_COMB (@lem2722663) (@lem2722662)). Qed.
Lemma lem2722665 : term439 = term257.
Proof. exact (MK_COMB (@lem2722664) (@lem2722659)). Qed.
Lemma lem2722667 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2722668 : term257 = term258.
Proof. exact (@lem2722667 (NUMERAL 0) term111). Qed.
Lemma lem2722669 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2722670 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2722671 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2722670 h1) (fun h1 : term258 = True => @lem2722669)). Qed.
Lemma lem2722672 : term258 = True.
Proof. exact (EQ_MP (@lem2722671) (@lem2722669)). Qed.
Lemma lem2722673 : term257 = True.
Proof. exact (TRANS (@lem2722668) (@lem2722672)). Qed.
Lemma lem2722674 : term439 = True.
Proof. exact (TRANS (@lem2722665) (@lem2722673)). Qed.
Lemma lem2722675 : term436 = True.
Proof. exact (TRANS (@lem2722651) (@lem2722674)). Qed.
Lemma lem2722676 : term257 = True.
Proof. exact (TRANS (@lem2722628) (@lem2722675)). Qed.
Lemma lem2722677 : term433 = True.
Proof. exact (TRANS (@lem2722619) (@lem2722676)). Qed.
Lemma lem2722678 : True = term433.
Proof. exact (SYM (@lem2722677)). Qed.
Lemma lem2722679 : term433.
Proof. exact (EQ_MP (@lem2722678) (@lem0)). Qed.
Lemma lem2722680 (n : int) (h1 : term616 n) : term441 n.
Proof. exact (conj (@lem2722679) (@lem2722615 n h1)). Qed.
Lemma lem2722682 (x : real) (y : real) : term442 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2722683 (n : int) : term443 n.
Proof. exact (@lem2722682 term110 (term233 n)). Qed.
Lemma lem2722684 (n : int) (h1 : term616 n) : term444 n.
Proof. exact (@lem2722683 n (@lem2722680 n h1)). Qed.
Lemma lem2722685 (n : int) : (term445 n) = (term233 n).
Proof. exact (@lem1982733 (term233 n)). Qed.
Lemma lem2722686 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2722687 (n : int) : (term446 n) = (term236 n).
Proof. exact (MK_COMB (@lem2722686) (@lem2722685 n)). Qed.
Lemma lem2722688 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2722689 (n : int) : (term444 n) = (term237 n).
Proof. exact (MK_COMB (@lem2722687 n) (@lem2722688)). Qed.
Lemma lem2722690 (n : int) (h1 : term616 n) : term237 n.
Proof. exact (EQ_MP (@lem2722689 n) (@lem2722684 n h1)). Qed.
Lemma lem2722692 (y : real) : term447 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2722693 (n : int) : term448 n.
Proof. exact (@lem2722692 (term104 n)). Qed.
Lemma lem2722694 (n : int) (h1 : term616 n) : term449 n.
Proof. exact (@lem2722693 n (@lem2722614 n h1)). Qed.
Lemma lem2722695 (n : int) (h1 : term616 n) : term450 n.
Proof. exact (@lem2722694 n h1 term110). Qed.
Lemma lem2722696 (n : int) : (term450 n) = ((term451 n) = term107).
Proof. exact (eq_refl (term450 n)). Qed.
Lemma lem2722697 (n : int) (h1 : term616 n) : (term451 n) = term107.
Proof. exact (EQ_MP (@lem2722696 n) (@lem2722695 n h1)). Qed.
Lemma lem2722698 (n : int) : (term451 n) = (term104 n).
Proof. exact (@lem1982733 (term104 n)). Qed.
Lemma lem2722699 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2722700 (n : int) : (term452 n) = (term108 n).
Proof. exact (MK_COMB (@lem2722699) (@lem2722698 n)). Qed.
Lemma lem2722701 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2722702 (n : int) : ((term451 n) = term107) = ((term104 n) = term107).
Proof. exact (MK_COMB (@lem2722700 n) (@lem2722701)). Qed.
Lemma lem2722703 (n : int) (h1 : term616 n) : (term104 n) = term107.
Proof. exact (EQ_MP (@lem2722702 n) (@lem2722697 n h1)). Qed.
Lemma lem2722704 (n : int) (h1 : term616 n) : term453 n.
Proof. exact (conj (@lem2722703 n h1) (@lem2722690 n h1)). Qed.
Lemma lem2722706 (x : real) (y : real) : term454 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2722707 (n : int) : term455 n.
Proof. exact (@lem2722706 (term104 n) (term233 n)). Qed.
Lemma lem2722708 (n : int) (h1 : term616 n) : term456 n.
Proof. exact (@lem2722707 n (@lem2722704 n h1)). Qed.
Lemma lem2722709 (n : int) : (term457 n) = (term458 n).
Proof. exact (@lem1982763 (term104 n) (term251 n) term193). Qed.
Lemma lem2722710 (n : int) : (term459 n) = (term460 n).
Proof. exact (@lem1982715 term193 (term104 n)). Qed.
Lemma lem2722712 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2722713 : term110 = term214.
Proof. exact (@lem2722712 term111). Qed.
Lemma lem2722715 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2722716 : term193 = term194.
Proof. exact (@lem2722715 term111). Qed.
Lemma lem2722717 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2722718 : term461 = term462.
Proof. exact (MK_COMB (@lem2722717) (@lem2722716)). Qed.
Lemma lem2722719 : term463 = term464.
Proof. exact (MK_COMB (@lem2722718) (@lem2722713)). Qed.
Lemma lem2722720 : term465.
Proof. exact (@lem1981473 term193 term110 term110 term110 term107 term110). Qed.
Lemma lem2722722 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2722723 : term257 = term258.
Proof. exact (@lem2722722 (NUMERAL 0) term111). Qed.
Lemma lem2722724 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2722725 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2722726 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2722725 h1) (fun h1 : term258 = True => @lem2722724)). Qed.
Lemma lem2722727 : term258 = True.
Proof. exact (EQ_MP (@lem2722726) (@lem2722724)). Qed.
Lemma lem2722728 : term257 = True.
Proof. exact (TRANS (@lem2722723) (@lem2722727)). Qed.
Lemma lem2722729 : True = term257.
Proof. exact (SYM (@lem2722728)). Qed.
Lemma lem2722730 : term257.
Proof. exact (EQ_MP (@lem2722729) (@lem0)). Qed.
Lemma lem2722731 : term466.
Proof. exact (@lem2722720 (@lem2722730)). Qed.
Lemma lem2722733 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2722734 : term257 = term258.
Proof. exact (@lem2722733 (NUMERAL 0) term111). Qed.
Lemma lem2722735 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2722736 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2722737 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2722736 h1) (fun h1 : term258 = True => @lem2722735)). Qed.
Lemma lem2722738 : term258 = True.
Proof. exact (EQ_MP (@lem2722737) (@lem2722735)). Qed.
Lemma lem2722739 : term257 = True.
Proof. exact (TRANS (@lem2722734) (@lem2722738)). Qed.
Lemma lem2722740 : True = term257.
Proof. exact (SYM (@lem2722739)). Qed.
Lemma lem2722741 : term257.
Proof. exact (EQ_MP (@lem2722740) (@lem0)). Qed.
Lemma lem2722742 : term467.
Proof. exact (@lem2722731 (@lem2722741)). Qed.
Lemma lem2722744 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2722745 : term257 = term258.
Proof. exact (@lem2722744 (NUMERAL 0) term111). Qed.
Lemma lem2722746 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2722747 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2722748 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2722747 h1) (fun h1 : term258 = True => @lem2722746)). Qed.
Lemma lem2722749 : term258 = True.
Proof. exact (EQ_MP (@lem2722748) (@lem2722746)). Qed.
Lemma lem2722750 : term257 = True.
Proof. exact (TRANS (@lem2722745) (@lem2722749)). Qed.
Lemma lem2722751 : True = term257.
Proof. exact (SYM (@lem2722750)). Qed.
Lemma lem2722752 : term257.
Proof. exact (EQ_MP (@lem2722751) (@lem0)). Qed.
Lemma lem2722753 : term468.
Proof. exact (@lem2722742 (@lem2722752)). Qed.
Lemma lem2722755 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2722756 : term202 = term203.
Proof. exact (@lem2722755 term111 term111). Qed.
Lemma lem2722757 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2722758 : term205 = term111.
Proof. exact (EQ_MP (@lem2722757) (@lem940073)). Qed.
Lemma lem2722759 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2722760 : term203 = term110.
Proof. exact (MK_COMB (@lem2722759) (@lem2722758)). Qed.
Lemma lem2722761 : term202 = term110.
Proof. exact (TRANS (@lem2722756) (@lem2722760)). Qed.
Lemma lem2722763 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2722764 : term215 = term220.
Proof. exact (@lem2722763 term111 term111). Qed.
Lemma lem2722765 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2722766 : term205 = term111.
Proof. exact (EQ_MP (@lem2722765) (@lem940073)). Qed.
Lemma lem2722767 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2722768 : term203 = term110.
Proof. exact (MK_COMB (@lem2722767) (@lem2722766)). Qed.
Lemma lem2722769 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2722770 : term220 = term193.
Proof. exact (MK_COMB (@lem2722769) (@lem2722768)). Qed.
Lemma lem2722771 : term215 = term193.
Proof. exact (TRANS (@lem2722764) (@lem2722770)). Qed.
Lemma lem2722772 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2722773 : term469 = term461.
Proof. exact (MK_COMB (@lem2722772) (@lem2722771)). Qed.
Lemma lem2722774 : term470 = term463.
Proof. exact (MK_COMB (@lem2722773) (@lem2722761)). Qed.
Lemma lem2722776 (m : nat) : (term471 m) = term107.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2722777 : term463 = term107.
Proof. exact (@lem2722776 term111). Qed.
Lemma lem2722778 : term470 = term107.
Proof. exact (TRANS (@lem2722774) (@lem2722777)). Qed.
Lemma lem2722779 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2722780 : term472 = term267.
Proof. exact (MK_COMB (@lem2722779) (@lem2722778)). Qed.
Lemma lem2722781 : term110 = term110.
Proof. exact (eq_refl term110). Qed.
Lemma lem2722782 : term473 = term269.
Proof. exact (MK_COMB (@lem2722780) (@lem2722781)). Qed.
Lemma lem2722784 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2722785 : term269 = term107.
Proof. exact (@lem2722784 term111). Qed.
Lemma lem2722786 : term473 = term107.
Proof. exact (TRANS (@lem2722782) (@lem2722785)). Qed.
Lemma lem2722788 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2722789 : term202 = term203.
Proof. exact (@lem2722788 term111 term111). Qed.
Lemma lem2722790 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2722791 : term205 = term111.
Proof. exact (EQ_MP (@lem2722790) (@lem940073)). Qed.
Lemma lem2722792 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2722793 : term203 = term110.
Proof. exact (MK_COMB (@lem2722792) (@lem2722791)). Qed.
Lemma lem2722794 : term202 = term110.
Proof. exact (TRANS (@lem2722789) (@lem2722793)). Qed.
Lemma lem2722795 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2722796 : term271 = term269.
Proof. exact (MK_COMB (@lem2722795) (@lem2722794)). Qed.
Lemma lem2722798 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2722799 : term269 = term107.
Proof. exact (@lem2722798 term111). Qed.
Lemma lem2722800 : term271 = term107.
Proof. exact (TRANS (@lem2722796) (@lem2722799)). Qed.
Lemma lem2722801 : term107 = term271.
Proof. exact (SYM (@lem2722800)). Qed.
Lemma lem2722802 : term473 = term271.
Proof. exact (TRANS (@lem2722786) (@lem2722801)). Qed.
Lemma lem2722803 : term464 = term190.
Proof. exact (@lem2722753 (@lem2722802)). Qed.
Lemma lem2722804 : term463 = term190.
Proof. exact (TRANS (@lem2722719) (@lem2722803)). Qed.
Lemma lem2722806 (x : real) : (term209 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2722807 : term190 = term107.
Proof. exact (@lem2722806 term107). Qed.
Lemma lem2722808 : term463 = term107.
Proof. exact (TRANS (@lem2722804) (@lem2722807)). Qed.
Lemma lem2722809 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2722810 : term474 = term267.
Proof. exact (MK_COMB (@lem2722809) (@lem2722808)). Qed.
Lemma lem2722811 (n : int) : (term104 n) = (term104 n).
Proof. exact (eq_refl (term104 n)). Qed.
Lemma lem2722812 (n : int) : (term460 n) = (term475 n).
Proof. exact (MK_COMB (@lem2722810) (@lem2722811 n)). Qed.
Lemma lem2722813 (n : int) : (term459 n) = (term475 n).
Proof. exact (TRANS (@lem2722710 n) (@lem2722812 n)). Qed.
Lemma lem2722814 (n : int) : (term475 n) = term107.
Proof. exact (@lem1982719 (term104 n)). Qed.
Lemma lem2722815 (n : int) : (term459 n) = term107.
Proof. exact (TRANS (@lem2722813 n) (@lem2722814 n)). Qed.
Lemma lem2722816 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2722817 (n : int) : (term476 n) = term139.
Proof. exact (MK_COMB (@lem2722816) (@lem2722815 n)). Qed.
Lemma lem2722818 : term193 = term193.
Proof. exact (eq_refl term193). Qed.
Lemma lem2722819 (n : int) : (term458 n) = term477.
Proof. exact (MK_COMB (@lem2722817 n) (@lem2722818)). Qed.
Lemma lem2722820 (n : int) : (term457 n) = term477.
Proof. exact (TRANS (@lem2722709 n) (@lem2722819 n)). Qed.
Lemma lem2722821 : term477 = term193.
Proof. exact (@lem1982721 term193). Qed.
Lemma lem2722822 (n : int) : (term457 n) = term193.
Proof. exact (TRANS (@lem2722820 n) (@lem2722821)). Qed.
Lemma lem2722823 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2722824 (n : int) : (term478 n) = term479.
Proof. exact (MK_COMB (@lem2722823) (@lem2722822 n)). Qed.
Lemma lem2722825 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2722826 (n : int) : (term456 n) = term480.
Proof. exact (MK_COMB (@lem2722824 n) (@lem2722825)). Qed.
Lemma lem2722827 (n : int) (h1 : term616 n) : term480.
Proof. exact (EQ_MP (@lem2722826 n) (@lem2722708 n h1)). Qed.
Lemma lem2722829 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2722830 : term480 = term481.
Proof. exact (@lem2722829 term107 term193). Qed.
Lemma lem2722832 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2722833 : term193 = term194.
Proof. exact (@lem2722832 term111). Qed.
Lemma lem2722835 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2722836 : term107 = term190.
Proof. exact (@lem2722835 (NUMERAL 0)). Qed.
Lemma lem2722837 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2722838 : term482 = term483.
Proof. exact (MK_COMB (@lem2722837) (@lem2722836)). Qed.
Lemma lem2722839 : term481 = term484.
Proof. exact (MK_COMB (@lem2722838) (@lem2722833)). Qed.
Lemma lem2722840 : term485.
Proof. exact (@lem1980026 term107 term110 term193 term110). Qed.
Lemma lem2722842 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2722843 : term257 = term258.
Proof. exact (@lem2722842 (NUMERAL 0) term111). Qed.
Lemma lem2722844 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2722845 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2722846 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2722845 h1) (fun h1 : term258 = True => @lem2722844)). Qed.
Lemma lem2722847 : term258 = True.
Proof. exact (EQ_MP (@lem2722846) (@lem2722844)). Qed.
Lemma lem2722848 : term257 = True.
Proof. exact (TRANS (@lem2722843) (@lem2722847)). Qed.
Lemma lem2722849 : True = term257.
Proof. exact (SYM (@lem2722848)). Qed.
Lemma lem2722850 : term257.
Proof. exact (EQ_MP (@lem2722849) (@lem0)). Qed.
Lemma lem2722851 : term486.
Proof. exact (@lem2722840 (@lem2722850)). Qed.
Lemma lem2722853 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2722854 : term257 = term258.
Proof. exact (@lem2722853 (NUMERAL 0) term111). Qed.
Lemma lem2722855 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2722856 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2722857 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2722856 h1) (fun h1 : term258 = True => @lem2722855)). Qed.
Lemma lem2722858 : term258 = True.
Proof. exact (EQ_MP (@lem2722857) (@lem2722855)). Qed.
Lemma lem2722859 : term257 = True.
Proof. exact (TRANS (@lem2722854) (@lem2722858)). Qed.
Lemma lem2722860 : True = term257.
Proof. exact (SYM (@lem2722859)). Qed.
Lemma lem2722861 : term257.
Proof. exact (EQ_MP (@lem2722860) (@lem0)). Qed.
Lemma lem2722862 : term484 = term487.
Proof. exact (@lem2722851 (@lem2722861)). Qed.
Lemma lem2722864 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2722865 : term215 = term220.
Proof. exact (@lem2722864 term111 term111). Qed.
Lemma lem2722866 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2722867 : term205 = term111.
Proof. exact (EQ_MP (@lem2722866) (@lem940073)). Qed.
Lemma lem2722868 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2722869 : term203 = term110.
Proof. exact (MK_COMB (@lem2722868) (@lem2722867)). Qed.
Lemma lem2722870 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2722871 : term220 = term193.
Proof. exact (MK_COMB (@lem2722870) (@lem2722869)). Qed.
Lemma lem2722872 : term215 = term193.
Proof. exact (TRANS (@lem2722865) (@lem2722871)). Qed.
Lemma lem2722874 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2722875 : term269 = term107.
Proof. exact (@lem2722874 term111). Qed.
Lemma lem2722876 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2722877 : term488 = term482.
Proof. exact (MK_COMB (@lem2722876) (@lem2722875)). Qed.
Lemma lem2722878 : term487 = term481.
Proof. exact (MK_COMB (@lem2722877) (@lem2722872)). Qed.
Lemma lem2722880 (m : nat) (n : nat) : (term489 m n) = (term490 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2722881 : term481 = term491.
Proof. exact (@lem2722880 (NUMERAL 0) term111). Qed.
Lemma lem2722882 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2722883 (h1 : term259 = (BIT1 0)) : (term111 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2722884 : (term259 = (BIT1 0)) = ((term111 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2722883 h1) (fun h1 : (term111 = (NUMERAL 0)) = False => @lem2722882)). Qed.
Lemma lem2722885 : (term111 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2722884) (@lem2722882)). Qed.
Lemma lem2722886 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2722887 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2722888 : term492 = (and True).
Proof. exact (MK_COMB (@lem2722887) (@lem2722886)). Qed.
Lemma lem2722889 : term491 = (True /\ False).
Proof. exact (MK_COMB (@lem2722888) (@lem2722885)). Qed.
Lemma lem2722891 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2722892 : term491 = False.
Proof. exact (TRANS (@lem2722889) (@lem2722891)). Qed.
Lemma lem2722893 : term481 = False.
Proof. exact (TRANS (@lem2722881) (@lem2722892)). Qed.
Lemma lem2722894 : term487 = False.
Proof. exact (TRANS (@lem2722878) (@lem2722893)). Qed.
Lemma lem2722895 : term484 = False.
Proof. exact (TRANS (@lem2722862) (@lem2722894)). Qed.
Lemma lem2722896 : term481 = False.
Proof. exact (TRANS (@lem2722839) (@lem2722895)). Qed.
Lemma lem2722897 : term480 = False.
Proof. exact (TRANS (@lem2722830) (@lem2722896)). Qed.
Lemma lem2722898 (n : int) (h1 : term616 n) : False.
Proof. exact (EQ_MP (@lem2722897) (@lem2722827 n h1)). Qed.
Lemma lem2722899 (n : int) (h1 : term617 n) : term617 n.
Proof. exact (h1). Qed.
Lemma lem2722900 (n : int) (h1 : term617 n) : term379 n.
Proof. exact (proj2 (@lem2722899 n h1)). Qed.
Lemma lem2722901 (n : int) (h1 : term617 n) : (term223 n) = term107.
Proof. exact (proj1 (@lem2722899 n h1)). Qed.
Lemma lem2722902 (n : int) (h1 : term617 n) : term237 n.
Proof. exact (proj2 (@lem2722900 n h1)). Qed.
Lemma lem2722905 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2722906 : term433 = term257.
Proof. exact (@lem2722905 term107 term110). Qed.
Lemma lem2722908 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2722909 : term110 = term214.
Proof. exact (@lem2722908 term111). Qed.
Lemma lem2722911 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2722912 : term107 = term190.
Proof. exact (@lem2722911 (NUMERAL 0)). Qed.
Lemma lem2722913 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2722914 : term434 = term435.
Proof. exact (MK_COMB (@lem2722913) (@lem2722912)). Qed.
Lemma lem2722915 : term257 = term436.
Proof. exact (MK_COMB (@lem2722914) (@lem2722909)). Qed.
Lemma lem2722916 : term437.
Proof. exact (@lem1980255 term107 term110 term110 term110). Qed.
Lemma lem2722918 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2722919 : term257 = term258.
Proof. exact (@lem2722918 (NUMERAL 0) term111). Qed.
Lemma lem2722920 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2722921 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2722922 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2722921 h1) (fun h1 : term258 = True => @lem2722920)). Qed.
Lemma lem2722923 : term258 = True.
Proof. exact (EQ_MP (@lem2722922) (@lem2722920)). Qed.
Lemma lem2722924 : term257 = True.
Proof. exact (TRANS (@lem2722919) (@lem2722923)). Qed.
Lemma lem2722925 : True = term257.
Proof. exact (SYM (@lem2722924)). Qed.
Lemma lem2722926 : term257.
Proof. exact (EQ_MP (@lem2722925) (@lem0)). Qed.
Lemma lem2722927 : term438.
Proof. exact (@lem2722916 (@lem2722926)). Qed.
Lemma lem2722929 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2722930 : term257 = term258.
Proof. exact (@lem2722929 (NUMERAL 0) term111). Qed.
Lemma lem2722931 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2722932 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2722933 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2722932 h1) (fun h1 : term258 = True => @lem2722931)). Qed.
Lemma lem2722934 : term258 = True.
Proof. exact (EQ_MP (@lem2722933) (@lem2722931)). Qed.
Lemma lem2722935 : term257 = True.
Proof. exact (TRANS (@lem2722930) (@lem2722934)). Qed.
Lemma lem2722936 : True = term257.
Proof. exact (SYM (@lem2722935)). Qed.
Lemma lem2722937 : term257.
Proof. exact (EQ_MP (@lem2722936) (@lem0)). Qed.
Lemma lem2722938 : term436 = term439.
Proof. exact (@lem2722927 (@lem2722937)). Qed.
Lemma lem2722940 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2722941 : term202 = term203.
Proof. exact (@lem2722940 term111 term111). Qed.
Lemma lem2722942 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2722943 : term205 = term111.
Proof. exact (EQ_MP (@lem2722942) (@lem940073)). Qed.
Lemma lem2722944 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2722945 : term203 = term110.
Proof. exact (MK_COMB (@lem2722944) (@lem2722943)). Qed.
Lemma lem2722946 : term202 = term110.
Proof. exact (TRANS (@lem2722941) (@lem2722945)). Qed.
Lemma lem2722948 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2722949 : term269 = term107.
Proof. exact (@lem2722948 term111). Qed.
Lemma lem2722950 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2722951 : term440 = term434.
Proof. exact (MK_COMB (@lem2722950) (@lem2722949)). Qed.
Lemma lem2722952 : term439 = term257.
Proof. exact (MK_COMB (@lem2722951) (@lem2722946)). Qed.
Lemma lem2722954 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2722955 : term257 = term258.
Proof. exact (@lem2722954 (NUMERAL 0) term111). Qed.
Lemma lem2722956 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2722957 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2722958 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2722957 h1) (fun h1 : term258 = True => @lem2722956)). Qed.
Lemma lem2722959 : term258 = True.
Proof. exact (EQ_MP (@lem2722958) (@lem2722956)). Qed.
Lemma lem2722960 : term257 = True.
Proof. exact (TRANS (@lem2722955) (@lem2722959)). Qed.
Lemma lem2722961 : term439 = True.
Proof. exact (TRANS (@lem2722952) (@lem2722960)). Qed.
Lemma lem2722962 : term436 = True.
Proof. exact (TRANS (@lem2722938) (@lem2722961)). Qed.
Lemma lem2722963 : term257 = True.
Proof. exact (TRANS (@lem2722915) (@lem2722962)). Qed.
Lemma lem2722964 : term433 = True.
Proof. exact (TRANS (@lem2722906) (@lem2722963)). Qed.
Lemma lem2722965 : True = term433.
Proof. exact (SYM (@lem2722964)). Qed.
Lemma lem2722966 : term433.
Proof. exact (EQ_MP (@lem2722965) (@lem0)). Qed.
Lemma lem2722967 (n : int) (h1 : term617 n) : term441 n.
Proof. exact (conj (@lem2722966) (@lem2722902 n h1)). Qed.
Lemma lem2722969 (x : real) (y : real) : term442 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2722970 (n : int) : term443 n.
Proof. exact (@lem2722969 term110 (term233 n)). Qed.
Lemma lem2722971 (n : int) (h1 : term617 n) : term444 n.
Proof. exact (@lem2722970 n (@lem2722967 n h1)). Qed.
Lemma lem2722972 (n : int) : (term445 n) = (term233 n).
Proof. exact (@lem1982733 (term233 n)). Qed.
Lemma lem2722973 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2722974 (n : int) : (term446 n) = (term236 n).
Proof. exact (MK_COMB (@lem2722973) (@lem2722972 n)). Qed.
Lemma lem2722975 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2722976 (n : int) : (term444 n) = (term237 n).
Proof. exact (MK_COMB (@lem2722974 n) (@lem2722975)). Qed.
Lemma lem2722977 (n : int) (h1 : term617 n) : term237 n.
Proof. exact (EQ_MP (@lem2722976 n) (@lem2722971 n h1)). Qed.
Lemma lem2722979 (y : real) : term447 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2722980 (n : int) : term499 n.
Proof. exact (@lem2722979 (term223 n)). Qed.
Lemma lem2722981 (n : int) (h1 : term617 n) : term500 n.
Proof. exact (@lem2722980 n (@lem2722901 n h1)). Qed.
Lemma lem2722982 (n : int) (h1 : term617 n) : term501 n.
Proof. exact (@lem2722981 n h1 term110). Qed.
Lemma lem2722983 (n : int) : (term501 n) = ((term502 n) = term107).
Proof. exact (eq_refl (term501 n)). Qed.
Lemma lem2722984 (n : int) (h1 : term617 n) : (term502 n) = term107.
Proof. exact (EQ_MP (@lem2722983 n) (@lem2722982 n h1)). Qed.
Lemma lem2722985 (n : int) : (term502 n) = (term223 n).
Proof. exact (@lem1982733 (term223 n)). Qed.
Lemma lem2722986 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2722987 (n : int) : (term503 n) = (term225 n).
Proof. exact (MK_COMB (@lem2722986) (@lem2722985 n)). Qed.
Lemma lem2722988 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2722989 (n : int) : ((term502 n) = term107) = ((term223 n) = term107).
Proof. exact (MK_COMB (@lem2722987 n) (@lem2722988)). Qed.
Lemma lem2722990 (n : int) (h1 : term617 n) : (term223 n) = term107.
Proof. exact (EQ_MP (@lem2722989 n) (@lem2722984 n h1)). Qed.
Lemma lem2722991 (n : int) (h1 : term617 n) : term599 n.
Proof. exact (conj (@lem2722990 n h1) (@lem2722977 n h1)). Qed.
Lemma lem2722993 (x : real) (y : real) : term454 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2722994 (n : int) : term600 n.
Proof. exact (@lem2722993 (term223 n) (term233 n)). Qed.
Lemma lem2722995 (n : int) (h1 : term617 n) : term601 n.
Proof. exact (@lem2722994 n (@lem2722991 n h1)). Qed.
Lemma lem2722996 (n : int) : (term602 n) = (term603 n).
Proof. exact (@lem1982753 (term104 n) (term251 n) term193 term193). Qed.
Lemma lem2722997 (n : int) : (term459 n) = (term460 n).
Proof. exact (@lem1982715 term193 (term104 n)). Qed.
Lemma lem2722999 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2723000 : term110 = term214.
Proof. exact (@lem2722999 term111). Qed.
Lemma lem2723002 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2723003 : term193 = term194.
Proof. exact (@lem2723002 term111). Qed.
Lemma lem2723004 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2723005 : term461 = term462.
Proof. exact (MK_COMB (@lem2723004) (@lem2723003)). Qed.
Lemma lem2723006 : term463 = term464.
Proof. exact (MK_COMB (@lem2723005) (@lem2723000)). Qed.
Lemma lem2723007 : term465.
Proof. exact (@lem1981473 term193 term110 term110 term110 term107 term110). Qed.
Lemma lem2723009 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2723010 : term257 = term258.
Proof. exact (@lem2723009 (NUMERAL 0) term111). Qed.
Lemma lem2723011 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2723012 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2723013 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2723012 h1) (fun h1 : term258 = True => @lem2723011)). Qed.
Lemma lem2723014 : term258 = True.
Proof. exact (EQ_MP (@lem2723013) (@lem2723011)). Qed.
Lemma lem2723015 : term257 = True.
Proof. exact (TRANS (@lem2723010) (@lem2723014)). Qed.
Lemma lem2723016 : True = term257.
Proof. exact (SYM (@lem2723015)). Qed.
Lemma lem2723017 : term257.
Proof. exact (EQ_MP (@lem2723016) (@lem0)). Qed.
Lemma lem2723018 : term466.
Proof. exact (@lem2723007 (@lem2723017)). Qed.
Lemma lem2723020 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2723021 : term257 = term258.
Proof. exact (@lem2723020 (NUMERAL 0) term111). Qed.
Lemma lem2723022 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2723023 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2723024 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2723023 h1) (fun h1 : term258 = True => @lem2723022)). Qed.
Lemma lem2723025 : term258 = True.
Proof. exact (EQ_MP (@lem2723024) (@lem2723022)). Qed.
Lemma lem2723026 : term257 = True.
Proof. exact (TRANS (@lem2723021) (@lem2723025)). Qed.
Lemma lem2723027 : True = term257.
Proof. exact (SYM (@lem2723026)). Qed.
Lemma lem2723028 : term257.
Proof. exact (EQ_MP (@lem2723027) (@lem0)). Qed.
Lemma lem2723029 : term467.
Proof. exact (@lem2723018 (@lem2723028)). Qed.
Lemma lem2723031 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2723032 : term257 = term258.
Proof. exact (@lem2723031 (NUMERAL 0) term111). Qed.
Lemma lem2723033 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2723034 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2723035 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2723034 h1) (fun h1 : term258 = True => @lem2723033)). Qed.
Lemma lem2723036 : term258 = True.
Proof. exact (EQ_MP (@lem2723035) (@lem2723033)). Qed.
Lemma lem2723037 : term257 = True.
Proof. exact (TRANS (@lem2723032) (@lem2723036)). Qed.
Lemma lem2723038 : True = term257.
Proof. exact (SYM (@lem2723037)). Qed.
Lemma lem2723039 : term257.
Proof. exact (EQ_MP (@lem2723038) (@lem0)). Qed.
Lemma lem2723040 : term468.
Proof. exact (@lem2723029 (@lem2723039)). Qed.
Lemma lem2723042 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2723043 : term202 = term203.
Proof. exact (@lem2723042 term111 term111). Qed.
Lemma lem2723044 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2723045 : term205 = term111.
Proof. exact (EQ_MP (@lem2723044) (@lem940073)). Qed.
Lemma lem2723046 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2723047 : term203 = term110.
Proof. exact (MK_COMB (@lem2723046) (@lem2723045)). Qed.
Lemma lem2723048 : term202 = term110.
Proof. exact (TRANS (@lem2723043) (@lem2723047)). Qed.
Lemma lem2723050 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2723051 : term215 = term220.
Proof. exact (@lem2723050 term111 term111). Qed.
Lemma lem2723052 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2723053 : term205 = term111.
Proof. exact (EQ_MP (@lem2723052) (@lem940073)). Qed.
Lemma lem2723054 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2723055 : term203 = term110.
Proof. exact (MK_COMB (@lem2723054) (@lem2723053)). Qed.
Lemma lem2723056 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2723057 : term220 = term193.
Proof. exact (MK_COMB (@lem2723056) (@lem2723055)). Qed.
Lemma lem2723058 : term215 = term193.
Proof. exact (TRANS (@lem2723051) (@lem2723057)). Qed.
Lemma lem2723059 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2723060 : term469 = term461.
Proof. exact (MK_COMB (@lem2723059) (@lem2723058)). Qed.
Lemma lem2723061 : term470 = term463.
Proof. exact (MK_COMB (@lem2723060) (@lem2723048)). Qed.
Lemma lem2723063 (m : nat) : (term471 m) = term107.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2723064 : term463 = term107.
Proof. exact (@lem2723063 term111). Qed.
Lemma lem2723065 : term470 = term107.
Proof. exact (TRANS (@lem2723061) (@lem2723064)). Qed.
Lemma lem2723066 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2723067 : term472 = term267.
Proof. exact (MK_COMB (@lem2723066) (@lem2723065)). Qed.
Lemma lem2723068 : term110 = term110.
Proof. exact (eq_refl term110). Qed.
Lemma lem2723069 : term473 = term269.
Proof. exact (MK_COMB (@lem2723067) (@lem2723068)). Qed.
Lemma lem2723071 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2723072 : term269 = term107.
Proof. exact (@lem2723071 term111). Qed.
Lemma lem2723073 : term473 = term107.
Proof. exact (TRANS (@lem2723069) (@lem2723072)). Qed.
Lemma lem2723075 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2723076 : term202 = term203.
Proof. exact (@lem2723075 term111 term111). Qed.
Lemma lem2723077 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2723078 : term205 = term111.
Proof. exact (EQ_MP (@lem2723077) (@lem940073)). Qed.
Lemma lem2723079 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2723080 : term203 = term110.
Proof. exact (MK_COMB (@lem2723079) (@lem2723078)). Qed.
Lemma lem2723081 : term202 = term110.
Proof. exact (TRANS (@lem2723076) (@lem2723080)). Qed.
Lemma lem2723082 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2723083 : term271 = term269.
Proof. exact (MK_COMB (@lem2723082) (@lem2723081)). Qed.
Lemma lem2723085 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2723086 : term269 = term107.
Proof. exact (@lem2723085 term111). Qed.
Lemma lem2723087 : term271 = term107.
Proof. exact (TRANS (@lem2723083) (@lem2723086)). Qed.
Lemma lem2723088 : term107 = term271.
Proof. exact (SYM (@lem2723087)). Qed.
Lemma lem2723089 : term473 = term271.
Proof. exact (TRANS (@lem2723073) (@lem2723088)). Qed.
Lemma lem2723090 : term464 = term190.
Proof. exact (@lem2723040 (@lem2723089)). Qed.
Lemma lem2723091 : term463 = term190.
Proof. exact (TRANS (@lem2723006) (@lem2723090)). Qed.
Lemma lem2723093 (x : real) : (term209 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2723094 : term190 = term107.
Proof. exact (@lem2723093 term107). Qed.
Lemma lem2723095 : term463 = term107.
Proof. exact (TRANS (@lem2723091) (@lem2723094)). Qed.
Lemma lem2723096 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2723097 : term474 = term267.
Proof. exact (MK_COMB (@lem2723096) (@lem2723095)). Qed.
Lemma lem2723098 (n : int) : (term104 n) = (term104 n).
Proof. exact (eq_refl (term104 n)). Qed.
Lemma lem2723099 (n : int) : (term460 n) = (term475 n).
Proof. exact (MK_COMB (@lem2723097) (@lem2723098 n)). Qed.
Lemma lem2723100 (n : int) : (term459 n) = (term475 n).
Proof. exact (TRANS (@lem2722997 n) (@lem2723099 n)). Qed.
Lemma lem2723101 (n : int) : (term475 n) = term107.
Proof. exact (@lem1982719 (term104 n)). Qed.
Lemma lem2723102 (n : int) : (term459 n) = term107.
Proof. exact (TRANS (@lem2723100 n) (@lem2723101 n)). Qed.
Lemma lem2723103 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2723104 (n : int) : (term476 n) = term139.
Proof. exact (MK_COMB (@lem2723103) (@lem2723102 n)). Qed.
Lemma lem2723106 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2723107 : term193 = term194.
Proof. exact (@lem2723106 term111). Qed.
Lemma lem2723109 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2723110 : term193 = term194.
Proof. exact (@lem2723109 term111). Qed.
Lemma lem2723111 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2723112 : term461 = term462.
Proof. exact (MK_COMB (@lem2723111) (@lem2723110)). Qed.
Lemma lem2723113 : term604 = term605.
Proof. exact (MK_COMB (@lem2723112) (@lem2723107)). Qed.
Lemma lem2723114 : term606.
Proof. exact (@lem1981473 term193 term110 term193 term110 term308 term110). Qed.
Lemma lem2723116 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2723117 : term257 = term258.
Proof. exact (@lem2723116 (NUMERAL 0) term111). Qed.
Lemma lem2723118 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2723119 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2723120 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2723119 h1) (fun h1 : term258 = True => @lem2723118)). Qed.
Lemma lem2723121 : term258 = True.
Proof. exact (EQ_MP (@lem2723120) (@lem2723118)). Qed.
Lemma lem2723122 : term257 = True.
Proof. exact (TRANS (@lem2723117) (@lem2723121)). Qed.
Lemma lem2723123 : True = term257.
Proof. exact (SYM (@lem2723122)). Qed.
Lemma lem2723124 : term257.
Proof. exact (EQ_MP (@lem2723123) (@lem0)). Qed.
Lemma lem2723125 : term607.
Proof. exact (@lem2723114 (@lem2723124)). Qed.
Lemma lem2723127 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2723128 : term257 = term258.
Proof. exact (@lem2723127 (NUMERAL 0) term111). Qed.
Lemma lem2723129 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2723130 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2723131 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2723130 h1) (fun h1 : term258 = True => @lem2723129)). Qed.
Lemma lem2723132 : term258 = True.
Proof. exact (EQ_MP (@lem2723131) (@lem2723129)). Qed.
Lemma lem2723133 : term257 = True.
Proof. exact (TRANS (@lem2723128) (@lem2723132)). Qed.
Lemma lem2723134 : True = term257.
Proof. exact (SYM (@lem2723133)). Qed.
Lemma lem2723135 : term257.
Proof. exact (EQ_MP (@lem2723134) (@lem0)). Qed.
Lemma lem2723136 : term608.
Proof. exact (@lem2723125 (@lem2723135)). Qed.
Lemma lem2723138 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2723139 : term257 = term258.
Proof. exact (@lem2723138 (NUMERAL 0) term111). Qed.
Lemma lem2723140 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2723141 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2723142 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2723141 h1) (fun h1 : term258 = True => @lem2723140)). Qed.
Lemma lem2723143 : term258 = True.
Proof. exact (EQ_MP (@lem2723142) (@lem2723140)). Qed.
Lemma lem2723144 : term257 = True.
Proof. exact (TRANS (@lem2723139) (@lem2723143)). Qed.
Lemma lem2723145 : True = term257.
Proof. exact (SYM (@lem2723144)). Qed.
Lemma lem2723146 : term257.
Proof. exact (EQ_MP (@lem2723145) (@lem0)). Qed.
Lemma lem2723147 : term609.
Proof. exact (@lem2723136 (@lem2723146)). Qed.
Lemma lem2723149 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2723150 : term215 = term220.
Proof. exact (@lem2723149 term111 term111). Qed.
Lemma lem2723151 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2723152 : term205 = term111.
Proof. exact (EQ_MP (@lem2723151) (@lem940073)). Qed.
Lemma lem2723153 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2723154 : term203 = term110.
Proof. exact (MK_COMB (@lem2723153) (@lem2723152)). Qed.
Lemma lem2723155 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2723156 : term220 = term193.
Proof. exact (MK_COMB (@lem2723155) (@lem2723154)). Qed.
Lemma lem2723157 : term215 = term193.
Proof. exact (TRANS (@lem2723150) (@lem2723156)). Qed.
Lemma lem2723159 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2723160 : term215 = term220.
Proof. exact (@lem2723159 term111 term111). Qed.
Lemma lem2723161 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2723162 : term205 = term111.
Proof. exact (EQ_MP (@lem2723161) (@lem940073)). Qed.
Lemma lem2723163 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2723164 : term203 = term110.
Proof. exact (MK_COMB (@lem2723163) (@lem2723162)). Qed.
Lemma lem2723165 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2723166 : term220 = term193.
Proof. exact (MK_COMB (@lem2723165) (@lem2723164)). Qed.
Lemma lem2723167 : term215 = term193.
Proof. exact (TRANS (@lem2723160) (@lem2723166)). Qed.
Lemma lem2723168 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2723169 : term469 = term461.
Proof. exact (MK_COMB (@lem2723168) (@lem2723167)). Qed.
Lemma lem2723170 : term610 = term604.
Proof. exact (MK_COMB (@lem2723169) (@lem2723157)). Qed.
Lemma lem2723171 : term604 = term574.
Proof. exact (@lem1367763 term111 term111). Qed.
Lemma lem2723172 : term285 = term286.
Proof. exact (@lem706885). Qed.
Lemma lem2723173 : (term285 = term286) = (term287 = term288).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term286). Qed.
Lemma lem2723174 : term287 = term288.
Proof. exact (EQ_MP (@lem2723173) (@lem2723172)). Qed.
Lemma lem2723175 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2723176 : term284 = term279.
Proof. exact (MK_COMB (@lem2723175) (@lem2723174)). Qed.
Lemma lem2723177 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2723178 : term574 = term308.
Proof. exact (MK_COMB (@lem2723177) (@lem2723176)). Qed.
Lemma lem2723179 : term604 = term308.
Proof. exact (TRANS (@lem2723171) (@lem2723178)). Qed.
Lemma lem2723180 : term610 = term308.
Proof. exact (TRANS (@lem2723170) (@lem2723179)). Qed.
Lemma lem2723181 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2723182 : term611 = term612.
Proof. exact (MK_COMB (@lem2723181) (@lem2723180)). Qed.
Lemma lem2723183 : term110 = term110.
Proof. exact (eq_refl term110). Qed.
Lemma lem2723184 : term613 = term544.
Proof. exact (MK_COMB (@lem2723182) (@lem2723183)). Qed.
Lemma lem2723186 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2723187 : term544 = term545.
Proof. exact (@lem2723186 term288 term111). Qed.
Lemma lem2723188 : term294 = term286.
Proof. exact (@lem996237 term286). Qed.
Lemma lem2723189 : (term294 = term286) = (term295 = term288).
Proof. exact (@lem1007663 term286 (BIT1 0) term286). Qed.
Lemma lem2723190 : term295 = term288.
Proof. exact (EQ_MP (@lem2723189) (@lem2723188)). Qed.
Lemma lem2723191 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2723192 : term293 = term279.
Proof. exact (MK_COMB (@lem2723191) (@lem2723190)). Qed.
Lemma lem2723193 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2723194 : term545 = term308.
Proof. exact (MK_COMB (@lem2723193) (@lem2723192)). Qed.
Lemma lem2723195 : term544 = term308.
Proof. exact (TRANS (@lem2723187) (@lem2723194)). Qed.
Lemma lem2723196 : term613 = term308.
Proof. exact (TRANS (@lem2723184) (@lem2723195)). Qed.
Lemma lem2723198 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2723199 : term202 = term203.
Proof. exact (@lem2723198 term111 term111). Qed.
Lemma lem2723200 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2723201 : term205 = term111.
Proof. exact (EQ_MP (@lem2723200) (@lem940073)). Qed.
Lemma lem2723202 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2723203 : term203 = term110.
Proof. exact (MK_COMB (@lem2723202) (@lem2723201)). Qed.
Lemma lem2723204 : term202 = term110.
Proof. exact (TRANS (@lem2723199) (@lem2723203)). Qed.
Lemma lem2723205 : term612 = term612.
Proof. exact (eq_refl term612). Qed.
Lemma lem2723206 : term614 = term544.
Proof. exact (MK_COMB (@lem2723205) (@lem2723204)). Qed.
Lemma lem2723208 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2723209 : term544 = term545.
Proof. exact (@lem2723208 term288 term111). Qed.
Lemma lem2723210 : term294 = term286.
Proof. exact (@lem996237 term286). Qed.
Lemma lem2723211 : (term294 = term286) = (term295 = term288).
Proof. exact (@lem1007663 term286 (BIT1 0) term286). Qed.
Lemma lem2723212 : term295 = term288.
Proof. exact (EQ_MP (@lem2723211) (@lem2723210)). Qed.
Lemma lem2723213 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2723214 : term293 = term279.
Proof. exact (MK_COMB (@lem2723213) (@lem2723212)). Qed.
Lemma lem2723215 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2723216 : term545 = term308.
Proof. exact (MK_COMB (@lem2723215) (@lem2723214)). Qed.
Lemma lem2723217 : term544 = term308.
Proof. exact (TRANS (@lem2723209) (@lem2723216)). Qed.
Lemma lem2723218 : term614 = term308.
Proof. exact (TRANS (@lem2723206) (@lem2723217)). Qed.
Lemma lem2723219 : term308 = term614.
Proof. exact (SYM (@lem2723218)). Qed.
Lemma lem2723220 : term613 = term614.
Proof. exact (TRANS (@lem2723196) (@lem2723219)). Qed.
Lemma lem2723221 : term605 = term311.
Proof. exact (@lem2723147 (@lem2723220)). Qed.
Lemma lem2723222 : term604 = term311.
Proof. exact (TRANS (@lem2723113) (@lem2723221)). Qed.
Lemma lem2723224 (x : real) : (term209 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2723225 : term311 = term308.
Proof. exact (@lem2723224 term308). Qed.
Lemma lem2723226 : term604 = term308.
Proof. exact (TRANS (@lem2723222) (@lem2723225)). Qed.
Lemma lem2723227 (n : int) : (term603 n) = term535.
Proof. exact (MK_COMB (@lem2723104 n) (@lem2723226)). Qed.
Lemma lem2723228 (n : int) : (term602 n) = term535.
Proof. exact (TRANS (@lem2722996 n) (@lem2723227 n)). Qed.
Lemma lem2723229 : term535 = term308.
Proof. exact (@lem1982721 term308). Qed.
Lemma lem2723230 (n : int) : (term602 n) = term308.
Proof. exact (TRANS (@lem2723228 n) (@lem2723229)). Qed.
Lemma lem2723231 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2723232 (n : int) : (term615 n) = term537.
Proof. exact (MK_COMB (@lem2723231) (@lem2723230 n)). Qed.
Lemma lem2723233 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2723234 (n : int) : (term601 n) = term538.
Proof. exact (MK_COMB (@lem2723232 n) (@lem2723233)). Qed.
Lemma lem2723235 (n : int) (h1 : term617 n) : term538.
Proof. exact (EQ_MP (@lem2723234 n) (@lem2722995 n h1)). Qed.
Lemma lem2723237 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2723238 : term538 = term539.
Proof. exact (@lem2723237 term107 term308). Qed.
Lemma lem2723240 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2723241 : term308 = term311.
Proof. exact (@lem2723240 term288). Qed.
Lemma lem2723243 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2723244 : term107 = term190.
Proof. exact (@lem2723243 (NUMERAL 0)). Qed.
Lemma lem2723245 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2723246 : term482 = term483.
Proof. exact (MK_COMB (@lem2723245) (@lem2723244)). Qed.
Lemma lem2723247 : term539 = term540.
Proof. exact (MK_COMB (@lem2723246) (@lem2723241)). Qed.
Lemma lem2723248 : term541.
Proof. exact (@lem1980026 term107 term110 term308 term110). Qed.
Lemma lem2723250 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2723251 : term257 = term258.
Proof. exact (@lem2723250 (NUMERAL 0) term111). Qed.
Lemma lem2723252 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2723253 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2723254 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2723253 h1) (fun h1 : term258 = True => @lem2723252)). Qed.
Lemma lem2723255 : term258 = True.
Proof. exact (EQ_MP (@lem2723254) (@lem2723252)). Qed.
Lemma lem2723256 : term257 = True.
Proof. exact (TRANS (@lem2723251) (@lem2723255)). Qed.
Lemma lem2723257 : True = term257.
Proof. exact (SYM (@lem2723256)). Qed.
Lemma lem2723258 : term257.
Proof. exact (EQ_MP (@lem2723257) (@lem0)). Qed.
Lemma lem2723259 : term542.
Proof. exact (@lem2723248 (@lem2723258)). Qed.
Lemma lem2723261 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2723262 : term257 = term258.
Proof. exact (@lem2723261 (NUMERAL 0) term111). Qed.
Lemma lem2723263 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2723264 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2723265 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2723264 h1) (fun h1 : term258 = True => @lem2723263)). Qed.
Lemma lem2723266 : term258 = True.
Proof. exact (EQ_MP (@lem2723265) (@lem2723263)). Qed.
Lemma lem2723267 : term257 = True.
Proof. exact (TRANS (@lem2723262) (@lem2723266)). Qed.
Lemma lem2723268 : True = term257.
Proof. exact (SYM (@lem2723267)). Qed.
Lemma lem2723269 : term257.
Proof. exact (EQ_MP (@lem2723268) (@lem0)). Qed.
Lemma lem2723270 : term540 = term543.
Proof. exact (@lem2723259 (@lem2723269)). Qed.
Lemma lem2723272 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2723273 : term544 = term545.
Proof. exact (@lem2723272 term288 term111). Qed.
Lemma lem2723274 : term294 = term286.
Proof. exact (@lem996237 term286). Qed.
Lemma lem2723275 : (term294 = term286) = (term295 = term288).
Proof. exact (@lem1007663 term286 (BIT1 0) term286). Qed.
Lemma lem2723276 : term295 = term288.
Proof. exact (EQ_MP (@lem2723275) (@lem2723274)). Qed.
Lemma lem2723277 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2723278 : term293 = term279.
Proof. exact (MK_COMB (@lem2723277) (@lem2723276)). Qed.
Lemma lem2723279 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2723280 : term545 = term308.
Proof. exact (MK_COMB (@lem2723279) (@lem2723278)). Qed.
Lemma lem2723281 : term544 = term308.
Proof. exact (TRANS (@lem2723273) (@lem2723280)). Qed.
Lemma lem2723283 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2723284 : term269 = term107.
Proof. exact (@lem2723283 term111). Qed.
Lemma lem2723285 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2723286 : term488 = term482.
Proof. exact (MK_COMB (@lem2723285) (@lem2723284)). Qed.
Lemma lem2723287 : term543 = term539.
Proof. exact (MK_COMB (@lem2723286) (@lem2723281)). Qed.
Lemma lem2723289 (m : nat) (n : nat) : (term489 m n) = (term490 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2723290 : term539 = term546.
Proof. exact (@lem2723289 (NUMERAL 0) term288). Qed.
Lemma lem2723291 : term547 = term286.
Proof. exact (@lem912803). Qed.
Lemma lem2723292 (h1 : term547 = term286) : (term288 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term286 h1). Qed.
Lemma lem2723293 : (term547 = term286) = ((term288 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term547 = term286 => @lem2723292 h1) (fun h1 : (term288 = (NUMERAL 0)) = False => @lem2723291)). Qed.
Lemma lem2723294 : (term288 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2723293) (@lem2723291)). Qed.
Lemma lem2723295 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2723296 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2723297 : term492 = (and True).
Proof. exact (MK_COMB (@lem2723296) (@lem2723295)). Qed.
Lemma lem2723298 : term546 = (True /\ False).
Proof. exact (MK_COMB (@lem2723297) (@lem2723294)). Qed.
Lemma lem2723300 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2723301 : term546 = False.
Proof. exact (TRANS (@lem2723298) (@lem2723300)). Qed.
Lemma lem2723302 : term539 = False.
Proof. exact (TRANS (@lem2723290) (@lem2723301)). Qed.
Lemma lem2723303 : term543 = False.
Proof. exact (TRANS (@lem2723287) (@lem2723302)). Qed.
Lemma lem2723304 : term540 = False.
Proof. exact (TRANS (@lem2723270) (@lem2723303)). Qed.
Lemma lem2723305 : term539 = False.
Proof. exact (TRANS (@lem2723247) (@lem2723304)). Qed.
Lemma lem2723306 : term538 = False.
Proof. exact (TRANS (@lem2723238) (@lem2723305)). Qed.
Lemma lem2723307 (n : int) (h1 : term617 n) : False.
Proof. exact (EQ_MP (@lem2723306) (@lem2723235 n h1)). Qed.
Lemma lem2723308 (n : int) (h1 : term381 n) : False.
Proof. exact (or_elim (@lem2722611 n h1) (fun h0 : term616 n => @lem2722898 n h0) (fun h0 : term617 n => @lem2723307 n h0)). Qed.
Lemma lem2723309 (n : int) (h1 : term386 n) : False.
Proof. exact (or_elim (@lem2721912 n h1) (fun h0 : term383 n => @lem2722610 n h0) (fun h0 : term381 n => @lem2723308 n h0)). Qed.
Lemma lem2723310 (n : int) (h1 : term375 n) : term375 n.
Proof. exact (h1). Qed.
Lemma lem2723311 (n : int) (h1 : term372 n) : term372 n.
Proof. exact (h1). Qed.
Lemma lem2723312 (n : int) (h1 : term618 n) : term618 n.
Proof. exact (h1). Qed.
Lemma lem2723313 (n : int) (h1 : term618 n) : term367 n.
Proof. exact (proj2 (@lem2723312 n h1)). Qed.
Lemma lem2723314 (n : int) (h1 : term618 n) : (term104 n) = term107.
Proof. exact (proj1 (@lem2723312 n h1)). Qed.
Lemma lem2723315 (n : int) (h1 : term618 n) : term243 n.
Proof. exact (proj2 (@lem2723313 n h1)). Qed.
Lemma lem2723318 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2723319 : term433 = term257.
Proof. exact (@lem2723318 term107 term110). Qed.
Lemma lem2723321 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2723322 : term110 = term214.
Proof. exact (@lem2723321 term111). Qed.
Lemma lem2723324 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2723325 : term107 = term190.
Proof. exact (@lem2723324 (NUMERAL 0)). Qed.
Lemma lem2723326 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2723327 : term434 = term435.
Proof. exact (MK_COMB (@lem2723326) (@lem2723325)). Qed.
Lemma lem2723328 : term257 = term436.
Proof. exact (MK_COMB (@lem2723327) (@lem2723322)). Qed.
Lemma lem2723329 : term437.
Proof. exact (@lem1980255 term107 term110 term110 term110). Qed.
Lemma lem2723331 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2723332 : term257 = term258.
Proof. exact (@lem2723331 (NUMERAL 0) term111). Qed.
Lemma lem2723333 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2723334 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2723335 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2723334 h1) (fun h1 : term258 = True => @lem2723333)). Qed.
Lemma lem2723336 : term258 = True.
Proof. exact (EQ_MP (@lem2723335) (@lem2723333)). Qed.
Lemma lem2723337 : term257 = True.
Proof. exact (TRANS (@lem2723332) (@lem2723336)). Qed.
Lemma lem2723338 : True = term257.
Proof. exact (SYM (@lem2723337)). Qed.
Lemma lem2723339 : term257.
Proof. exact (EQ_MP (@lem2723338) (@lem0)). Qed.
Lemma lem2723340 : term438.
Proof. exact (@lem2723329 (@lem2723339)). Qed.
Lemma lem2723342 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2723343 : term257 = term258.
Proof. exact (@lem2723342 (NUMERAL 0) term111). Qed.
Lemma lem2723344 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2723345 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2723346 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2723345 h1) (fun h1 : term258 = True => @lem2723344)). Qed.
Lemma lem2723347 : term258 = True.
Proof. exact (EQ_MP (@lem2723346) (@lem2723344)). Qed.
Lemma lem2723348 : term257 = True.
Proof. exact (TRANS (@lem2723343) (@lem2723347)). Qed.
Lemma lem2723349 : True = term257.
Proof. exact (SYM (@lem2723348)). Qed.
Lemma lem2723350 : term257.
Proof. exact (EQ_MP (@lem2723349) (@lem0)). Qed.
Lemma lem2723351 : term436 = term439.
Proof. exact (@lem2723340 (@lem2723350)). Qed.
Lemma lem2723353 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2723354 : term202 = term203.
Proof. exact (@lem2723353 term111 term111). Qed.
Lemma lem2723355 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2723356 : term205 = term111.
Proof. exact (EQ_MP (@lem2723355) (@lem940073)). Qed.
Lemma lem2723357 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2723358 : term203 = term110.
Proof. exact (MK_COMB (@lem2723357) (@lem2723356)). Qed.
Lemma lem2723359 : term202 = term110.
Proof. exact (TRANS (@lem2723354) (@lem2723358)). Qed.
Lemma lem2723361 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2723362 : term269 = term107.
Proof. exact (@lem2723361 term111). Qed.
Lemma lem2723363 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2723364 : term440 = term434.
Proof. exact (MK_COMB (@lem2723363) (@lem2723362)). Qed.
Lemma lem2723365 : term439 = term257.
Proof. exact (MK_COMB (@lem2723364) (@lem2723359)). Qed.
Lemma lem2723367 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2723368 : term257 = term258.
Proof. exact (@lem2723367 (NUMERAL 0) term111). Qed.
Lemma lem2723369 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2723370 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2723371 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2723370 h1) (fun h1 : term258 = True => @lem2723369)). Qed.
Lemma lem2723372 : term258 = True.
Proof. exact (EQ_MP (@lem2723371) (@lem2723369)). Qed.
Lemma lem2723373 : term257 = True.
Proof. exact (TRANS (@lem2723368) (@lem2723372)). Qed.
Lemma lem2723374 : term439 = True.
Proof. exact (TRANS (@lem2723365) (@lem2723373)). Qed.
Lemma lem2723375 : term436 = True.
Proof. exact (TRANS (@lem2723351) (@lem2723374)). Qed.
Lemma lem2723376 : term257 = True.
Proof. exact (TRANS (@lem2723328) (@lem2723375)). Qed.
Lemma lem2723377 : term433 = True.
Proof. exact (TRANS (@lem2723319) (@lem2723376)). Qed.
Lemma lem2723378 : True = term433.
Proof. exact (SYM (@lem2723377)). Qed.
Lemma lem2723379 : term433.
Proof. exact (EQ_MP (@lem2723378) (@lem0)). Qed.
Lemma lem2723380 (n : int) (h1 : term618 n) : term510 n.
Proof. exact (conj (@lem2723379) (@lem2723315 n h1)). Qed.
Lemma lem2723382 (x : real) (y : real) : term442 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2723383 (n : int) : term511 n.
Proof. exact (@lem2723382 term110 (term223 n)). Qed.
Lemma lem2723384 (n : int) (h1 : term618 n) : term512 n.
Proof. exact (@lem2723383 n (@lem2723380 n h1)). Qed.
Lemma lem2723385 (n : int) : (term502 n) = (term223 n).
Proof. exact (@lem1982733 (term223 n)). Qed.
Lemma lem2723386 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2723387 (n : int) : (term513 n) = (term242 n).
Proof. exact (MK_COMB (@lem2723386) (@lem2723385 n)). Qed.
Lemma lem2723388 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2723389 (n : int) : (term512 n) = (term243 n).
Proof. exact (MK_COMB (@lem2723387 n) (@lem2723388)). Qed.
Lemma lem2723390 (n : int) (h1 : term618 n) : term243 n.
Proof. exact (EQ_MP (@lem2723389 n) (@lem2723384 n h1)). Qed.
Lemma lem2723392 (y : real) : term447 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2723393 (n : int) : term448 n.
Proof. exact (@lem2723392 (term104 n)). Qed.
Lemma lem2723394 (n : int) (h1 : term618 n) : term449 n.
Proof. exact (@lem2723393 n (@lem2723314 n h1)). Qed.
Lemma lem2723395 (n : int) (h1 : term618 n) : term514 n.
Proof. exact (@lem2723394 n h1 term193). Qed.
Lemma lem2723396 (n : int) : (term514 n) = ((term251 n) = term107).
Proof. exact (eq_refl (term514 n)). Qed.
Lemma lem2723403 (n : int) (h1 : term618 n) : (term251 n) = term107.
Proof. exact (EQ_MP (@lem2723396 n) (@lem2723395 n h1)). Qed.
Lemma lem2723404 (n : int) (h1 : term618 n) : term515 n.
Proof. exact (conj (@lem2723403 n h1) (@lem2723390 n h1)). Qed.
Lemma lem2723406 (x : real) (y : real) : term454 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2723407 (n : int) : term516 n.
Proof. exact (@lem2723406 (term251 n) (term223 n)). Qed.
Lemma lem2723408 (n : int) (h1 : term618 n) : term517 n.
Proof. exact (@lem2723407 n (@lem2723404 n h1)). Qed.
Lemma lem2723409 (n : int) : (term518 n) = (term519 n).
Proof. exact (@lem1982763 (term251 n) (term104 n) term193). Qed.
Lemma lem2723410 (n : int) : (term520 n) = (term460 n).
Proof. exact (@lem1982713 term193 (term104 n)). Qed.
Lemma lem2723412 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2723413 : term110 = term214.
Proof. exact (@lem2723412 term111). Qed.
Lemma lem2723415 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2723416 : term193 = term194.
Proof. exact (@lem2723415 term111). Qed.
Lemma lem2723417 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2723418 : term461 = term462.
Proof. exact (MK_COMB (@lem2723417) (@lem2723416)). Qed.
Lemma lem2723419 : term463 = term464.
Proof. exact (MK_COMB (@lem2723418) (@lem2723413)). Qed.
Lemma lem2723420 : term465.
Proof. exact (@lem1981473 term193 term110 term110 term110 term107 term110). Qed.
Lemma lem2723422 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2723423 : term257 = term258.
Proof. exact (@lem2723422 (NUMERAL 0) term111). Qed.
Lemma lem2723424 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2723425 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2723426 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2723425 h1) (fun h1 : term258 = True => @lem2723424)). Qed.
Lemma lem2723427 : term258 = True.
Proof. exact (EQ_MP (@lem2723426) (@lem2723424)). Qed.
Lemma lem2723428 : term257 = True.
Proof. exact (TRANS (@lem2723423) (@lem2723427)). Qed.
Lemma lem2723429 : True = term257.
Proof. exact (SYM (@lem2723428)). Qed.
Lemma lem2723430 : term257.
Proof. exact (EQ_MP (@lem2723429) (@lem0)). Qed.
Lemma lem2723431 : term466.
Proof. exact (@lem2723420 (@lem2723430)). Qed.
Lemma lem2723433 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2723434 : term257 = term258.
Proof. exact (@lem2723433 (NUMERAL 0) term111). Qed.
Lemma lem2723435 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2723436 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2723437 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2723436 h1) (fun h1 : term258 = True => @lem2723435)). Qed.
Lemma lem2723438 : term258 = True.
Proof. exact (EQ_MP (@lem2723437) (@lem2723435)). Qed.
Lemma lem2723439 : term257 = True.
Proof. exact (TRANS (@lem2723434) (@lem2723438)). Qed.
Lemma lem2723440 : True = term257.
Proof. exact (SYM (@lem2723439)). Qed.
Lemma lem2723441 : term257.
Proof. exact (EQ_MP (@lem2723440) (@lem0)). Qed.
Lemma lem2723442 : term467.
Proof. exact (@lem2723431 (@lem2723441)). Qed.
Lemma lem2723444 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2723445 : term257 = term258.
Proof. exact (@lem2723444 (NUMERAL 0) term111). Qed.
Lemma lem2723446 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2723447 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2723448 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2723447 h1) (fun h1 : term258 = True => @lem2723446)). Qed.
Lemma lem2723449 : term258 = True.
Proof. exact (EQ_MP (@lem2723448) (@lem2723446)). Qed.
Lemma lem2723450 : term257 = True.
Proof. exact (TRANS (@lem2723445) (@lem2723449)). Qed.
Lemma lem2723451 : True = term257.
Proof. exact (SYM (@lem2723450)). Qed.
Lemma lem2723452 : term257.
Proof. exact (EQ_MP (@lem2723451) (@lem0)). Qed.
Lemma lem2723453 : term468.
Proof. exact (@lem2723442 (@lem2723452)). Qed.
Lemma lem2723455 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2723456 : term202 = term203.
Proof. exact (@lem2723455 term111 term111). Qed.
Lemma lem2723457 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2723458 : term205 = term111.
Proof. exact (EQ_MP (@lem2723457) (@lem940073)). Qed.
Lemma lem2723459 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2723460 : term203 = term110.
Proof. exact (MK_COMB (@lem2723459) (@lem2723458)). Qed.
Lemma lem2723461 : term202 = term110.
Proof. exact (TRANS (@lem2723456) (@lem2723460)). Qed.
Lemma lem2723463 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2723464 : term215 = term220.
Proof. exact (@lem2723463 term111 term111). Qed.
Lemma lem2723465 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2723466 : term205 = term111.
Proof. exact (EQ_MP (@lem2723465) (@lem940073)). Qed.
Lemma lem2723467 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2723468 : term203 = term110.
Proof. exact (MK_COMB (@lem2723467) (@lem2723466)). Qed.
Lemma lem2723469 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2723470 : term220 = term193.
Proof. exact (MK_COMB (@lem2723469) (@lem2723468)). Qed.
Lemma lem2723471 : term215 = term193.
Proof. exact (TRANS (@lem2723464) (@lem2723470)). Qed.
Lemma lem2723472 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2723473 : term469 = term461.
Proof. exact (MK_COMB (@lem2723472) (@lem2723471)). Qed.
Lemma lem2723474 : term470 = term463.
Proof. exact (MK_COMB (@lem2723473) (@lem2723461)). Qed.
Lemma lem2723476 (m : nat) : (term471 m) = term107.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2723477 : term463 = term107.
Proof. exact (@lem2723476 term111). Qed.
Lemma lem2723478 : term470 = term107.
Proof. exact (TRANS (@lem2723474) (@lem2723477)). Qed.
Lemma lem2723479 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2723480 : term472 = term267.
Proof. exact (MK_COMB (@lem2723479) (@lem2723478)). Qed.
Lemma lem2723481 : term110 = term110.
Proof. exact (eq_refl term110). Qed.
Lemma lem2723482 : term473 = term269.
Proof. exact (MK_COMB (@lem2723480) (@lem2723481)). Qed.
Lemma lem2723484 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2723485 : term269 = term107.
Proof. exact (@lem2723484 term111). Qed.
Lemma lem2723486 : term473 = term107.
Proof. exact (TRANS (@lem2723482) (@lem2723485)). Qed.
Lemma lem2723488 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2723489 : term202 = term203.
Proof. exact (@lem2723488 term111 term111). Qed.
Lemma lem2723490 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2723491 : term205 = term111.
Proof. exact (EQ_MP (@lem2723490) (@lem940073)). Qed.
Lemma lem2723492 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2723493 : term203 = term110.
Proof. exact (MK_COMB (@lem2723492) (@lem2723491)). Qed.
Lemma lem2723494 : term202 = term110.
Proof. exact (TRANS (@lem2723489) (@lem2723493)). Qed.
Lemma lem2723495 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2723496 : term271 = term269.
Proof. exact (MK_COMB (@lem2723495) (@lem2723494)). Qed.
Lemma lem2723498 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2723499 : term269 = term107.
Proof. exact (@lem2723498 term111). Qed.
Lemma lem2723500 : term271 = term107.
Proof. exact (TRANS (@lem2723496) (@lem2723499)). Qed.
Lemma lem2723501 : term107 = term271.
Proof. exact (SYM (@lem2723500)). Qed.
Lemma lem2723502 : term473 = term271.
Proof. exact (TRANS (@lem2723486) (@lem2723501)). Qed.
Lemma lem2723503 : term464 = term190.
Proof. exact (@lem2723453 (@lem2723502)). Qed.
Lemma lem2723504 : term463 = term190.
Proof. exact (TRANS (@lem2723419) (@lem2723503)). Qed.
Lemma lem2723506 (x : real) : (term209 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2723507 : term190 = term107.
Proof. exact (@lem2723506 term107). Qed.
Lemma lem2723508 : term463 = term107.
Proof. exact (TRANS (@lem2723504) (@lem2723507)). Qed.
Lemma lem2723509 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2723510 : term474 = term267.
Proof. exact (MK_COMB (@lem2723509) (@lem2723508)). Qed.
Lemma lem2723511 (n : int) : (term104 n) = (term104 n).
Proof. exact (eq_refl (term104 n)). Qed.
Lemma lem2723512 (n : int) : (term460 n) = (term475 n).
Proof. exact (MK_COMB (@lem2723510) (@lem2723511 n)). Qed.
Lemma lem2723513 (n : int) : (term520 n) = (term475 n).
Proof. exact (TRANS (@lem2723410 n) (@lem2723512 n)). Qed.
Lemma lem2723514 (n : int) : (term475 n) = term107.
Proof. exact (@lem1982719 (term104 n)). Qed.
Lemma lem2723515 (n : int) : (term520 n) = term107.
Proof. exact (TRANS (@lem2723513 n) (@lem2723514 n)). Qed.
Lemma lem2723516 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2723517 (n : int) : (term521 n) = term139.
Proof. exact (MK_COMB (@lem2723516) (@lem2723515 n)). Qed.
Lemma lem2723518 : term193 = term193.
Proof. exact (eq_refl term193). Qed.
Lemma lem2723519 (n : int) : (term519 n) = term477.
Proof. exact (MK_COMB (@lem2723517 n) (@lem2723518)). Qed.
Lemma lem2723520 (n : int) : (term518 n) = term477.
Proof. exact (TRANS (@lem2723409 n) (@lem2723519 n)). Qed.
Lemma lem2723521 : term477 = term193.
Proof. exact (@lem1982721 term193). Qed.
Lemma lem2723522 (n : int) : (term518 n) = term193.
Proof. exact (TRANS (@lem2723520 n) (@lem2723521)). Qed.
Lemma lem2723523 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2723524 (n : int) : (term522 n) = term479.
Proof. exact (MK_COMB (@lem2723523) (@lem2723522 n)). Qed.
Lemma lem2723525 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2723526 (n : int) : (term517 n) = term480.
Proof. exact (MK_COMB (@lem2723524 n) (@lem2723525)). Qed.
Lemma lem2723527 (n : int) (h1 : term618 n) : term480.
Proof. exact (EQ_MP (@lem2723526 n) (@lem2723408 n h1)). Qed.
Lemma lem2723529 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2723530 : term480 = term481.
Proof. exact (@lem2723529 term107 term193). Qed.
Lemma lem2723532 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2723533 : term193 = term194.
Proof. exact (@lem2723532 term111). Qed.
Lemma lem2723535 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2723536 : term107 = term190.
Proof. exact (@lem2723535 (NUMERAL 0)). Qed.
Lemma lem2723537 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2723538 : term482 = term483.
Proof. exact (MK_COMB (@lem2723537) (@lem2723536)). Qed.
Lemma lem2723539 : term481 = term484.
Proof. exact (MK_COMB (@lem2723538) (@lem2723533)). Qed.
Lemma lem2723540 : term485.
Proof. exact (@lem1980026 term107 term110 term193 term110). Qed.
Lemma lem2723542 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2723543 : term257 = term258.
Proof. exact (@lem2723542 (NUMERAL 0) term111). Qed.
Lemma lem2723544 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2723545 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2723546 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2723545 h1) (fun h1 : term258 = True => @lem2723544)). Qed.
Lemma lem2723547 : term258 = True.
Proof. exact (EQ_MP (@lem2723546) (@lem2723544)). Qed.
Lemma lem2723548 : term257 = True.
Proof. exact (TRANS (@lem2723543) (@lem2723547)). Qed.
Lemma lem2723549 : True = term257.
Proof. exact (SYM (@lem2723548)). Qed.
Lemma lem2723550 : term257.
Proof. exact (EQ_MP (@lem2723549) (@lem0)). Qed.
Lemma lem2723551 : term486.
Proof. exact (@lem2723540 (@lem2723550)). Qed.
Lemma lem2723553 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2723554 : term257 = term258.
Proof. exact (@lem2723553 (NUMERAL 0) term111). Qed.
Lemma lem2723555 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2723556 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2723557 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2723556 h1) (fun h1 : term258 = True => @lem2723555)). Qed.
Lemma lem2723558 : term258 = True.
Proof. exact (EQ_MP (@lem2723557) (@lem2723555)). Qed.
Lemma lem2723559 : term257 = True.
Proof. exact (TRANS (@lem2723554) (@lem2723558)). Qed.
Lemma lem2723560 : True = term257.
Proof. exact (SYM (@lem2723559)). Qed.
Lemma lem2723561 : term257.
Proof. exact (EQ_MP (@lem2723560) (@lem0)). Qed.
Lemma lem2723562 : term484 = term487.
Proof. exact (@lem2723551 (@lem2723561)). Qed.
Lemma lem2723564 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2723565 : term215 = term220.
Proof. exact (@lem2723564 term111 term111). Qed.
Lemma lem2723566 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2723567 : term205 = term111.
Proof. exact (EQ_MP (@lem2723566) (@lem940073)). Qed.
Lemma lem2723568 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2723569 : term203 = term110.
Proof. exact (MK_COMB (@lem2723568) (@lem2723567)). Qed.
Lemma lem2723570 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2723571 : term220 = term193.
Proof. exact (MK_COMB (@lem2723570) (@lem2723569)). Qed.
Lemma lem2723572 : term215 = term193.
Proof. exact (TRANS (@lem2723565) (@lem2723571)). Qed.
Lemma lem2723574 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2723575 : term269 = term107.
Proof. exact (@lem2723574 term111). Qed.
Lemma lem2723576 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2723577 : term488 = term482.
Proof. exact (MK_COMB (@lem2723576) (@lem2723575)). Qed.
Lemma lem2723578 : term487 = term481.
Proof. exact (MK_COMB (@lem2723577) (@lem2723572)). Qed.
Lemma lem2723580 (m : nat) (n : nat) : (term489 m n) = (term490 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2723581 : term481 = term491.
Proof. exact (@lem2723580 (NUMERAL 0) term111). Qed.
Lemma lem2723582 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2723583 (h1 : term259 = (BIT1 0)) : (term111 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2723584 : (term259 = (BIT1 0)) = ((term111 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2723583 h1) (fun h1 : (term111 = (NUMERAL 0)) = False => @lem2723582)). Qed.
Lemma lem2723585 : (term111 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2723584) (@lem2723582)). Qed.
Lemma lem2723586 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2723587 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2723588 : term492 = (and True).
Proof. exact (MK_COMB (@lem2723587) (@lem2723586)). Qed.
Lemma lem2723589 : term491 = (True /\ False).
Proof. exact (MK_COMB (@lem2723588) (@lem2723585)). Qed.
Lemma lem2723591 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2723592 : term491 = False.
Proof. exact (TRANS (@lem2723589) (@lem2723591)). Qed.
Lemma lem2723593 : term481 = False.
Proof. exact (TRANS (@lem2723581) (@lem2723592)). Qed.
Lemma lem2723594 : term487 = False.
Proof. exact (TRANS (@lem2723578) (@lem2723593)). Qed.
Lemma lem2723595 : term484 = False.
Proof. exact (TRANS (@lem2723562) (@lem2723594)). Qed.
Lemma lem2723596 : term481 = False.
Proof. exact (TRANS (@lem2723539) (@lem2723595)). Qed.
Lemma lem2723597 : term480 = False.
Proof. exact (TRANS (@lem2723530) (@lem2723596)). Qed.
Lemma lem2723598 (n : int) (h1 : term618 n) : False.
Proof. exact (EQ_MP (@lem2723597) (@lem2723527 n h1)). Qed.
Lemma lem2723599 (n : int) (h1 : term619 n) : term619 n.
Proof. exact (h1). Qed.
Lemma lem2723600 (n : int) (h1 : term619 n) : term367 n.
Proof. exact (proj2 (@lem2723599 n h1)). Qed.
Lemma lem2723601 (n : int) (h1 : term619 n) : (term223 n) = term107.
Proof. exact (proj1 (@lem2723599 n h1)). Qed.
Lemma lem2723603 (n : int) (h1 : term619 n) : term275 n.
Proof. exact (proj1 (@lem2723600 n h1)). Qed.
Lemma lem2723605 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2723606 : term433 = term257.
Proof. exact (@lem2723605 term107 term110). Qed.
Lemma lem2723608 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2723609 : term110 = term214.
Proof. exact (@lem2723608 term111). Qed.
Lemma lem2723611 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2723612 : term107 = term190.
Proof. exact (@lem2723611 (NUMERAL 0)). Qed.
Lemma lem2723613 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2723614 : term434 = term435.
Proof. exact (MK_COMB (@lem2723613) (@lem2723612)). Qed.
Lemma lem2723615 : term257 = term436.
Proof. exact (MK_COMB (@lem2723614) (@lem2723609)). Qed.
Lemma lem2723616 : term437.
Proof. exact (@lem1980255 term107 term110 term110 term110). Qed.
Lemma lem2723618 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2723619 : term257 = term258.
Proof. exact (@lem2723618 (NUMERAL 0) term111). Qed.
Lemma lem2723620 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2723621 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2723622 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2723621 h1) (fun h1 : term258 = True => @lem2723620)). Qed.
Lemma lem2723623 : term258 = True.
Proof. exact (EQ_MP (@lem2723622) (@lem2723620)). Qed.
Lemma lem2723624 : term257 = True.
Proof. exact (TRANS (@lem2723619) (@lem2723623)). Qed.
Lemma lem2723625 : True = term257.
Proof. exact (SYM (@lem2723624)). Qed.
Lemma lem2723626 : term257.
Proof. exact (EQ_MP (@lem2723625) (@lem0)). Qed.
Lemma lem2723627 : term438.
Proof. exact (@lem2723616 (@lem2723626)). Qed.
Lemma lem2723629 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2723630 : term257 = term258.
Proof. exact (@lem2723629 (NUMERAL 0) term111). Qed.
Lemma lem2723631 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2723632 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2723633 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2723632 h1) (fun h1 : term258 = True => @lem2723631)). Qed.
Lemma lem2723634 : term258 = True.
Proof. exact (EQ_MP (@lem2723633) (@lem2723631)). Qed.
Lemma lem2723635 : term257 = True.
Proof. exact (TRANS (@lem2723630) (@lem2723634)). Qed.
Lemma lem2723636 : True = term257.
Proof. exact (SYM (@lem2723635)). Qed.
Lemma lem2723637 : term257.
Proof. exact (EQ_MP (@lem2723636) (@lem0)). Qed.
Lemma lem2723638 : term436 = term439.
Proof. exact (@lem2723627 (@lem2723637)). Qed.
Lemma lem2723640 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2723641 : term202 = term203.
Proof. exact (@lem2723640 term111 term111). Qed.
Lemma lem2723642 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2723643 : term205 = term111.
Proof. exact (EQ_MP (@lem2723642) (@lem940073)). Qed.
Lemma lem2723644 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2723645 : term203 = term110.
Proof. exact (MK_COMB (@lem2723644) (@lem2723643)). Qed.
Lemma lem2723646 : term202 = term110.
Proof. exact (TRANS (@lem2723641) (@lem2723645)). Qed.
Lemma lem2723648 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2723649 : term269 = term107.
Proof. exact (@lem2723648 term111). Qed.
Lemma lem2723650 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2723651 : term440 = term434.
Proof. exact (MK_COMB (@lem2723650) (@lem2723649)). Qed.
Lemma lem2723652 : term439 = term257.
Proof. exact (MK_COMB (@lem2723651) (@lem2723646)). Qed.
Lemma lem2723654 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2723655 : term257 = term258.
Proof. exact (@lem2723654 (NUMERAL 0) term111). Qed.
Lemma lem2723656 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2723657 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2723658 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2723657 h1) (fun h1 : term258 = True => @lem2723656)). Qed.
Lemma lem2723659 : term258 = True.
Proof. exact (EQ_MP (@lem2723658) (@lem2723656)). Qed.
Lemma lem2723660 : term257 = True.
Proof. exact (TRANS (@lem2723655) (@lem2723659)). Qed.
Lemma lem2723661 : term439 = True.
Proof. exact (TRANS (@lem2723652) (@lem2723660)). Qed.
Lemma lem2723662 : term436 = True.
Proof. exact (TRANS (@lem2723638) (@lem2723661)). Qed.
Lemma lem2723663 : term257 = True.
Proof. exact (TRANS (@lem2723615) (@lem2723662)). Qed.
Lemma lem2723664 : term433 = True.
Proof. exact (TRANS (@lem2723606) (@lem2723663)). Qed.
Lemma lem2723665 : True = term433.
Proof. exact (SYM (@lem2723664)). Qed.
Lemma lem2723666 : term433.
Proof. exact (EQ_MP (@lem2723665) (@lem0)). Qed.
Lemma lem2723667 (n : int) (h1 : term619 n) : term494 n.
Proof. exact (conj (@lem2723666) (@lem2723603 n h1)). Qed.
Lemma lem2723669 (x : real) (y : real) : term442 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2723670 (n : int) : term495 n.
Proof. exact (@lem2723669 term110 (term251 n)). Qed.
Lemma lem2723671 (n : int) (h1 : term619 n) : term496 n.
Proof. exact (@lem2723670 n (@lem2723667 n h1)). Qed.
Lemma lem2723672 (n : int) : (term497 n) = (term251 n).
Proof. exact (@lem1982733 (term251 n)). Qed.
Lemma lem2723673 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2723674 (n : int) : (term498 n) = (term274 n).
Proof. exact (MK_COMB (@lem2723673) (@lem2723672 n)). Qed.
Lemma lem2723675 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2723676 (n : int) : (term496 n) = (term275 n).
Proof. exact (MK_COMB (@lem2723674 n) (@lem2723675)). Qed.
Lemma lem2723677 (n : int) (h1 : term619 n) : term275 n.
Proof. exact (EQ_MP (@lem2723676 n) (@lem2723671 n h1)). Qed.
Lemma lem2723679 (y : real) : term447 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2723680 (n : int) : term499 n.
Proof. exact (@lem2723679 (term223 n)). Qed.
Lemma lem2723681 (n : int) (h1 : term619 n) : term500 n.
Proof. exact (@lem2723680 n (@lem2723601 n h1)). Qed.
Lemma lem2723682 (n : int) (h1 : term619 n) : term501 n.
Proof. exact (@lem2723681 n h1 term110). Qed.
Lemma lem2723683 (n : int) : (term501 n) = ((term502 n) = term107).
Proof. exact (eq_refl (term501 n)). Qed.
Lemma lem2723684 (n : int) (h1 : term619 n) : (term502 n) = term107.
Proof. exact (EQ_MP (@lem2723683 n) (@lem2723682 n h1)). Qed.
Lemma lem2723685 (n : int) : (term502 n) = (term223 n).
Proof. exact (@lem1982733 (term223 n)). Qed.
Lemma lem2723686 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2723687 (n : int) : (term503 n) = (term225 n).
Proof. exact (MK_COMB (@lem2723686) (@lem2723685 n)). Qed.
Lemma lem2723688 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2723689 (n : int) : ((term502 n) = term107) = ((term223 n) = term107).
Proof. exact (MK_COMB (@lem2723687 n) (@lem2723688)). Qed.
Lemma lem2723690 (n : int) (h1 : term619 n) : (term223 n) = term107.
Proof. exact (EQ_MP (@lem2723689 n) (@lem2723684 n h1)). Qed.
Lemma lem2723691 (n : int) (h1 : term619 n) : term504 n.
Proof. exact (conj (@lem2723690 n h1) (@lem2723677 n h1)). Qed.
Lemma lem2723693 (x : real) (y : real) : term454 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2723694 (n : int) : term505 n.
Proof. exact (@lem2723693 (term223 n) (term251 n)). Qed.
Lemma lem2723695 (n : int) (h1 : term619 n) : term506 n.
Proof. exact (@lem2723694 n (@lem2723691 n h1)). Qed.
Lemma lem2723696 (n : int) : (term507 n) = (term458 n).
Proof. exact (@lem1982759 (term104 n) (term251 n) term193). Qed.
Lemma lem2723697 (n : int) : (term459 n) = (term460 n).
Proof. exact (@lem1982715 term193 (term104 n)). Qed.
Lemma lem2723699 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2723700 : term110 = term214.
Proof. exact (@lem2723699 term111). Qed.
Lemma lem2723702 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2723703 : term193 = term194.
Proof. exact (@lem2723702 term111). Qed.
Lemma lem2723704 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2723705 : term461 = term462.
Proof. exact (MK_COMB (@lem2723704) (@lem2723703)). Qed.
Lemma lem2723706 : term463 = term464.
Proof. exact (MK_COMB (@lem2723705) (@lem2723700)). Qed.
Lemma lem2723707 : term465.
Proof. exact (@lem1981473 term193 term110 term110 term110 term107 term110). Qed.
Lemma lem2723709 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2723710 : term257 = term258.
Proof. exact (@lem2723709 (NUMERAL 0) term111). Qed.
Lemma lem2723711 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2723712 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2723713 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2723712 h1) (fun h1 : term258 = True => @lem2723711)). Qed.
Lemma lem2723714 : term258 = True.
Proof. exact (EQ_MP (@lem2723713) (@lem2723711)). Qed.
Lemma lem2723715 : term257 = True.
Proof. exact (TRANS (@lem2723710) (@lem2723714)). Qed.
Lemma lem2723716 : True = term257.
Proof. exact (SYM (@lem2723715)). Qed.
Lemma lem2723717 : term257.
Proof. exact (EQ_MP (@lem2723716) (@lem0)). Qed.
Lemma lem2723718 : term466.
Proof. exact (@lem2723707 (@lem2723717)). Qed.
Lemma lem2723720 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2723721 : term257 = term258.
Proof. exact (@lem2723720 (NUMERAL 0) term111). Qed.
Lemma lem2723722 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2723723 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2723724 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2723723 h1) (fun h1 : term258 = True => @lem2723722)). Qed.
Lemma lem2723725 : term258 = True.
Proof. exact (EQ_MP (@lem2723724) (@lem2723722)). Qed.
Lemma lem2723726 : term257 = True.
Proof. exact (TRANS (@lem2723721) (@lem2723725)). Qed.
Lemma lem2723727 : True = term257.
Proof. exact (SYM (@lem2723726)). Qed.
Lemma lem2723728 : term257.
Proof. exact (EQ_MP (@lem2723727) (@lem0)). Qed.
Lemma lem2723729 : term467.
Proof. exact (@lem2723718 (@lem2723728)). Qed.
Lemma lem2723731 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2723732 : term257 = term258.
Proof. exact (@lem2723731 (NUMERAL 0) term111). Qed.
Lemma lem2723733 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2723734 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2723735 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2723734 h1) (fun h1 : term258 = True => @lem2723733)). Qed.
Lemma lem2723736 : term258 = True.
Proof. exact (EQ_MP (@lem2723735) (@lem2723733)). Qed.
Lemma lem2723737 : term257 = True.
Proof. exact (TRANS (@lem2723732) (@lem2723736)). Qed.
Lemma lem2723738 : True = term257.
Proof. exact (SYM (@lem2723737)). Qed.
Lemma lem2723739 : term257.
Proof. exact (EQ_MP (@lem2723738) (@lem0)). Qed.
Lemma lem2723740 : term468.
Proof. exact (@lem2723729 (@lem2723739)). Qed.
Lemma lem2723742 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2723743 : term202 = term203.
Proof. exact (@lem2723742 term111 term111). Qed.
Lemma lem2723744 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2723745 : term205 = term111.
Proof. exact (EQ_MP (@lem2723744) (@lem940073)). Qed.
Lemma lem2723746 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2723747 : term203 = term110.
Proof. exact (MK_COMB (@lem2723746) (@lem2723745)). Qed.
Lemma lem2723748 : term202 = term110.
Proof. exact (TRANS (@lem2723743) (@lem2723747)). Qed.
Lemma lem2723750 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2723751 : term215 = term220.
Proof. exact (@lem2723750 term111 term111). Qed.
Lemma lem2723752 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2723753 : term205 = term111.
Proof. exact (EQ_MP (@lem2723752) (@lem940073)). Qed.
Lemma lem2723754 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2723755 : term203 = term110.
Proof. exact (MK_COMB (@lem2723754) (@lem2723753)). Qed.
Lemma lem2723756 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2723757 : term220 = term193.
Proof. exact (MK_COMB (@lem2723756) (@lem2723755)). Qed.
Lemma lem2723758 : term215 = term193.
Proof. exact (TRANS (@lem2723751) (@lem2723757)). Qed.
Lemma lem2723759 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2723760 : term469 = term461.
Proof. exact (MK_COMB (@lem2723759) (@lem2723758)). Qed.
Lemma lem2723761 : term470 = term463.
Proof. exact (MK_COMB (@lem2723760) (@lem2723748)). Qed.
Lemma lem2723763 (m : nat) : (term471 m) = term107.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2723764 : term463 = term107.
Proof. exact (@lem2723763 term111). Qed.
Lemma lem2723765 : term470 = term107.
Proof. exact (TRANS (@lem2723761) (@lem2723764)). Qed.
Lemma lem2723766 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2723767 : term472 = term267.
Proof. exact (MK_COMB (@lem2723766) (@lem2723765)). Qed.
Lemma lem2723768 : term110 = term110.
Proof. exact (eq_refl term110). Qed.
Lemma lem2723769 : term473 = term269.
Proof. exact (MK_COMB (@lem2723767) (@lem2723768)). Qed.
Lemma lem2723771 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2723772 : term269 = term107.
Proof. exact (@lem2723771 term111). Qed.
Lemma lem2723773 : term473 = term107.
Proof. exact (TRANS (@lem2723769) (@lem2723772)). Qed.
Lemma lem2723775 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2723776 : term202 = term203.
Proof. exact (@lem2723775 term111 term111). Qed.
Lemma lem2723777 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2723778 : term205 = term111.
Proof. exact (EQ_MP (@lem2723777) (@lem940073)). Qed.
Lemma lem2723779 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2723780 : term203 = term110.
Proof. exact (MK_COMB (@lem2723779) (@lem2723778)). Qed.
Lemma lem2723781 : term202 = term110.
Proof. exact (TRANS (@lem2723776) (@lem2723780)). Qed.
Lemma lem2723782 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2723783 : term271 = term269.
Proof. exact (MK_COMB (@lem2723782) (@lem2723781)). Qed.
Lemma lem2723785 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2723786 : term269 = term107.
Proof. exact (@lem2723785 term111). Qed.
Lemma lem2723787 : term271 = term107.
Proof. exact (TRANS (@lem2723783) (@lem2723786)). Qed.
Lemma lem2723788 : term107 = term271.
Proof. exact (SYM (@lem2723787)). Qed.
Lemma lem2723789 : term473 = term271.
Proof. exact (TRANS (@lem2723773) (@lem2723788)). Qed.
Lemma lem2723790 : term464 = term190.
Proof. exact (@lem2723740 (@lem2723789)). Qed.
Lemma lem2723791 : term463 = term190.
Proof. exact (TRANS (@lem2723706) (@lem2723790)). Qed.
Lemma lem2723793 (x : real) : (term209 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2723794 : term190 = term107.
Proof. exact (@lem2723793 term107). Qed.
Lemma lem2723795 : term463 = term107.
Proof. exact (TRANS (@lem2723791) (@lem2723794)). Qed.
Lemma lem2723796 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2723797 : term474 = term267.
Proof. exact (MK_COMB (@lem2723796) (@lem2723795)). Qed.
Lemma lem2723798 (n : int) : (term104 n) = (term104 n).
Proof. exact (eq_refl (term104 n)). Qed.
Lemma lem2723799 (n : int) : (term460 n) = (term475 n).
Proof. exact (MK_COMB (@lem2723797) (@lem2723798 n)). Qed.
Lemma lem2723800 (n : int) : (term459 n) = (term475 n).
Proof. exact (TRANS (@lem2723697 n) (@lem2723799 n)). Qed.
Lemma lem2723801 (n : int) : (term475 n) = term107.
Proof. exact (@lem1982719 (term104 n)). Qed.
Lemma lem2723802 (n : int) : (term459 n) = term107.
Proof. exact (TRANS (@lem2723800 n) (@lem2723801 n)). Qed.
Lemma lem2723803 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2723804 (n : int) : (term476 n) = term139.
Proof. exact (MK_COMB (@lem2723803) (@lem2723802 n)). Qed.
Lemma lem2723805 : term193 = term193.
Proof. exact (eq_refl term193). Qed.
Lemma lem2723806 (n : int) : (term458 n) = term477.
Proof. exact (MK_COMB (@lem2723804 n) (@lem2723805)). Qed.
Lemma lem2723807 (n : int) : (term507 n) = term477.
Proof. exact (TRANS (@lem2723696 n) (@lem2723806 n)). Qed.
Lemma lem2723808 : term477 = term193.
Proof. exact (@lem1982721 term193). Qed.
Lemma lem2723809 (n : int) : (term507 n) = term193.
Proof. exact (TRANS (@lem2723807 n) (@lem2723808)). Qed.
Lemma lem2723810 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2723811 (n : int) : (term508 n) = term479.
Proof. exact (MK_COMB (@lem2723810) (@lem2723809 n)). Qed.
Lemma lem2723812 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2723813 (n : int) : (term506 n) = term480.
Proof. exact (MK_COMB (@lem2723811 n) (@lem2723812)). Qed.
Lemma lem2723814 (n : int) (h1 : term619 n) : term480.
Proof. exact (EQ_MP (@lem2723813 n) (@lem2723695 n h1)). Qed.
Lemma lem2723816 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2723817 : term480 = term481.
Proof. exact (@lem2723816 term107 term193). Qed.
Lemma lem2723819 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2723820 : term193 = term194.
Proof. exact (@lem2723819 term111). Qed.
Lemma lem2723822 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2723823 : term107 = term190.
Proof. exact (@lem2723822 (NUMERAL 0)). Qed.
Lemma lem2723824 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2723825 : term482 = term483.
Proof. exact (MK_COMB (@lem2723824) (@lem2723823)). Qed.
Lemma lem2723826 : term481 = term484.
Proof. exact (MK_COMB (@lem2723825) (@lem2723820)). Qed.
Lemma lem2723827 : term485.
Proof. exact (@lem1980026 term107 term110 term193 term110). Qed.
Lemma lem2723829 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2723830 : term257 = term258.
Proof. exact (@lem2723829 (NUMERAL 0) term111). Qed.
Lemma lem2723831 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2723832 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2723833 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2723832 h1) (fun h1 : term258 = True => @lem2723831)). Qed.
Lemma lem2723834 : term258 = True.
Proof. exact (EQ_MP (@lem2723833) (@lem2723831)). Qed.
Lemma lem2723835 : term257 = True.
Proof. exact (TRANS (@lem2723830) (@lem2723834)). Qed.
Lemma lem2723836 : True = term257.
Proof. exact (SYM (@lem2723835)). Qed.
Lemma lem2723837 : term257.
Proof. exact (EQ_MP (@lem2723836) (@lem0)). Qed.
Lemma lem2723838 : term486.
Proof. exact (@lem2723827 (@lem2723837)). Qed.
Lemma lem2723840 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2723841 : term257 = term258.
Proof. exact (@lem2723840 (NUMERAL 0) term111). Qed.
Lemma lem2723842 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2723843 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2723844 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2723843 h1) (fun h1 : term258 = True => @lem2723842)). Qed.
Lemma lem2723845 : term258 = True.
Proof. exact (EQ_MP (@lem2723844) (@lem2723842)). Qed.
Lemma lem2723846 : term257 = True.
Proof. exact (TRANS (@lem2723841) (@lem2723845)). Qed.
Lemma lem2723847 : True = term257.
Proof. exact (SYM (@lem2723846)). Qed.
Lemma lem2723848 : term257.
Proof. exact (EQ_MP (@lem2723847) (@lem0)). Qed.
Lemma lem2723849 : term484 = term487.
Proof. exact (@lem2723838 (@lem2723848)). Qed.
Lemma lem2723851 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2723852 : term215 = term220.
Proof. exact (@lem2723851 term111 term111). Qed.
Lemma lem2723853 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2723854 : term205 = term111.
Proof. exact (EQ_MP (@lem2723853) (@lem940073)). Qed.
Lemma lem2723855 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2723856 : term203 = term110.
Proof. exact (MK_COMB (@lem2723855) (@lem2723854)). Qed.
Lemma lem2723857 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2723858 : term220 = term193.
Proof. exact (MK_COMB (@lem2723857) (@lem2723856)). Qed.
Lemma lem2723859 : term215 = term193.
Proof. exact (TRANS (@lem2723852) (@lem2723858)). Qed.
Lemma lem2723861 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2723862 : term269 = term107.
Proof. exact (@lem2723861 term111). Qed.
Lemma lem2723863 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2723864 : term488 = term482.
Proof. exact (MK_COMB (@lem2723863) (@lem2723862)). Qed.
Lemma lem2723865 : term487 = term481.
Proof. exact (MK_COMB (@lem2723864) (@lem2723859)). Qed.
Lemma lem2723867 (m : nat) (n : nat) : (term489 m n) = (term490 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2723868 : term481 = term491.
Proof. exact (@lem2723867 (NUMERAL 0) term111). Qed.
Lemma lem2723869 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2723870 (h1 : term259 = (BIT1 0)) : (term111 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2723871 : (term259 = (BIT1 0)) = ((term111 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2723870 h1) (fun h1 : (term111 = (NUMERAL 0)) = False => @lem2723869)). Qed.
Lemma lem2723872 : (term111 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2723871) (@lem2723869)). Qed.
Lemma lem2723873 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2723874 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2723875 : term492 = (and True).
Proof. exact (MK_COMB (@lem2723874) (@lem2723873)). Qed.
Lemma lem2723876 : term491 = (True /\ False).
Proof. exact (MK_COMB (@lem2723875) (@lem2723872)). Qed.
Lemma lem2723878 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2723879 : term491 = False.
Proof. exact (TRANS (@lem2723876) (@lem2723878)). Qed.
Lemma lem2723880 : term481 = False.
Proof. exact (TRANS (@lem2723868) (@lem2723879)). Qed.
Lemma lem2723881 : term487 = False.
Proof. exact (TRANS (@lem2723865) (@lem2723880)). Qed.
Lemma lem2723882 : term484 = False.
Proof. exact (TRANS (@lem2723849) (@lem2723881)). Qed.
Lemma lem2723883 : term481 = False.
Proof. exact (TRANS (@lem2723826) (@lem2723882)). Qed.
Lemma lem2723884 : term480 = False.
Proof. exact (TRANS (@lem2723817) (@lem2723883)). Qed.
Lemma lem2723885 (n : int) (h1 : term619 n) : False.
Proof. exact (EQ_MP (@lem2723884) (@lem2723814 n h1)). Qed.
Lemma lem2723886 (n : int) (h1 : term372 n) : False.
Proof. exact (or_elim (@lem2723311 n h1) (fun h0 : term618 n => @lem2723598 n h0) (fun h0 : term619 n => @lem2723885 n h0)). Qed.
Lemma lem2723887 (n : int) (h1 : term370 n) : term370 n.
Proof. exact (h1). Qed.
Lemma lem2723888 (n : int) (h1 : term620 n) : term620 n.
Proof. exact (h1). Qed.
Lemma lem2723889 (n : int) (h1 : term620 n) : term368 n.
Proof. exact (proj2 (@lem2723888 n h1)). Qed.
Lemma lem2723890 (n : int) (h1 : term620 n) : (term104 n) = term107.
Proof. exact (proj1 (@lem2723888 n h1)). Qed.
Lemma lem2723891 (n : int) (h1 : term620 n) : term243 n.
Proof. exact (proj2 (@lem2723889 n h1)). Qed.
Lemma lem2723894 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2723895 : term433 = term257.
Proof. exact (@lem2723894 term107 term110). Qed.
Lemma lem2723897 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2723898 : term110 = term214.
Proof. exact (@lem2723897 term111). Qed.
Lemma lem2723900 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2723901 : term107 = term190.
Proof. exact (@lem2723900 (NUMERAL 0)). Qed.
Lemma lem2723902 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2723903 : term434 = term435.
Proof. exact (MK_COMB (@lem2723902) (@lem2723901)). Qed.
Lemma lem2723904 : term257 = term436.
Proof. exact (MK_COMB (@lem2723903) (@lem2723898)). Qed.
Lemma lem2723905 : term437.
Proof. exact (@lem1980255 term107 term110 term110 term110). Qed.
Lemma lem2723907 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2723908 : term257 = term258.
Proof. exact (@lem2723907 (NUMERAL 0) term111). Qed.
Lemma lem2723909 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2723910 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2723911 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2723910 h1) (fun h1 : term258 = True => @lem2723909)). Qed.
Lemma lem2723912 : term258 = True.
Proof. exact (EQ_MP (@lem2723911) (@lem2723909)). Qed.
Lemma lem2723913 : term257 = True.
Proof. exact (TRANS (@lem2723908) (@lem2723912)). Qed.
Lemma lem2723914 : True = term257.
Proof. exact (SYM (@lem2723913)). Qed.
Lemma lem2723915 : term257.
Proof. exact (EQ_MP (@lem2723914) (@lem0)). Qed.
Lemma lem2723916 : term438.
Proof. exact (@lem2723905 (@lem2723915)). Qed.
Lemma lem2723918 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2723919 : term257 = term258.
Proof. exact (@lem2723918 (NUMERAL 0) term111). Qed.
Lemma lem2723920 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2723921 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2723922 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2723921 h1) (fun h1 : term258 = True => @lem2723920)). Qed.
Lemma lem2723923 : term258 = True.
Proof. exact (EQ_MP (@lem2723922) (@lem2723920)). Qed.
Lemma lem2723924 : term257 = True.
Proof. exact (TRANS (@lem2723919) (@lem2723923)). Qed.
Lemma lem2723925 : True = term257.
Proof. exact (SYM (@lem2723924)). Qed.
Lemma lem2723926 : term257.
Proof. exact (EQ_MP (@lem2723925) (@lem0)). Qed.
Lemma lem2723927 : term436 = term439.
Proof. exact (@lem2723916 (@lem2723926)). Qed.
Lemma lem2723929 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2723930 : term202 = term203.
Proof. exact (@lem2723929 term111 term111). Qed.
Lemma lem2723931 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2723932 : term205 = term111.
Proof. exact (EQ_MP (@lem2723931) (@lem940073)). Qed.
Lemma lem2723933 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2723934 : term203 = term110.
Proof. exact (MK_COMB (@lem2723933) (@lem2723932)). Qed.
Lemma lem2723935 : term202 = term110.
Proof. exact (TRANS (@lem2723930) (@lem2723934)). Qed.
Lemma lem2723937 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2723938 : term269 = term107.
Proof. exact (@lem2723937 term111). Qed.
Lemma lem2723939 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2723940 : term440 = term434.
Proof. exact (MK_COMB (@lem2723939) (@lem2723938)). Qed.
Lemma lem2723941 : term439 = term257.
Proof. exact (MK_COMB (@lem2723940) (@lem2723935)). Qed.
Lemma lem2723943 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2723944 : term257 = term258.
Proof. exact (@lem2723943 (NUMERAL 0) term111). Qed.
Lemma lem2723945 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2723946 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2723947 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2723946 h1) (fun h1 : term258 = True => @lem2723945)). Qed.
Lemma lem2723948 : term258 = True.
Proof. exact (EQ_MP (@lem2723947) (@lem2723945)). Qed.
Lemma lem2723949 : term257 = True.
Proof. exact (TRANS (@lem2723944) (@lem2723948)). Qed.
Lemma lem2723950 : term439 = True.
Proof. exact (TRANS (@lem2723941) (@lem2723949)). Qed.
Lemma lem2723951 : term436 = True.
Proof. exact (TRANS (@lem2723927) (@lem2723950)). Qed.
Lemma lem2723952 : term257 = True.
Proof. exact (TRANS (@lem2723904) (@lem2723951)). Qed.
Lemma lem2723953 : term433 = True.
Proof. exact (TRANS (@lem2723895) (@lem2723952)). Qed.
Lemma lem2723954 : True = term433.
Proof. exact (SYM (@lem2723953)). Qed.
Lemma lem2723955 : term433.
Proof. exact (EQ_MP (@lem2723954) (@lem0)). Qed.
Lemma lem2723956 (n : int) (h1 : term620 n) : term510 n.
Proof. exact (conj (@lem2723955) (@lem2723891 n h1)). Qed.
Lemma lem2723958 (x : real) (y : real) : term442 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2723959 (n : int) : term511 n.
Proof. exact (@lem2723958 term110 (term223 n)). Qed.
Lemma lem2723960 (n : int) (h1 : term620 n) : term512 n.
Proof. exact (@lem2723959 n (@lem2723956 n h1)). Qed.
Lemma lem2723961 (n : int) : (term502 n) = (term223 n).
Proof. exact (@lem1982733 (term223 n)). Qed.
Lemma lem2723962 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2723963 (n : int) : (term513 n) = (term242 n).
Proof. exact (MK_COMB (@lem2723962) (@lem2723961 n)). Qed.
Lemma lem2723964 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2723965 (n : int) : (term512 n) = (term243 n).
Proof. exact (MK_COMB (@lem2723963 n) (@lem2723964)). Qed.
Lemma lem2723966 (n : int) (h1 : term620 n) : term243 n.
Proof. exact (EQ_MP (@lem2723965 n) (@lem2723960 n h1)). Qed.
Lemma lem2723968 (y : real) : term447 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2723969 (n : int) : term448 n.
Proof. exact (@lem2723968 (term104 n)). Qed.
Lemma lem2723970 (n : int) (h1 : term620 n) : term449 n.
Proof. exact (@lem2723969 n (@lem2723890 n h1)). Qed.
Lemma lem2723971 (n : int) (h1 : term620 n) : term514 n.
Proof. exact (@lem2723970 n h1 term193). Qed.
Lemma lem2723972 (n : int) : (term514 n) = ((term251 n) = term107).
Proof. exact (eq_refl (term514 n)). Qed.
Lemma lem2723979 (n : int) (h1 : term620 n) : (term251 n) = term107.
Proof. exact (EQ_MP (@lem2723972 n) (@lem2723971 n h1)). Qed.
Lemma lem2723980 (n : int) (h1 : term620 n) : term515 n.
Proof. exact (conj (@lem2723979 n h1) (@lem2723966 n h1)). Qed.
Lemma lem2723982 (x : real) (y : real) : term454 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2723983 (n : int) : term516 n.
Proof. exact (@lem2723982 (term251 n) (term223 n)). Qed.
Lemma lem2723984 (n : int) (h1 : term620 n) : term517 n.
Proof. exact (@lem2723983 n (@lem2723980 n h1)). Qed.
Lemma lem2723985 (n : int) : (term518 n) = (term519 n).
Proof. exact (@lem1982763 (term251 n) (term104 n) term193). Qed.
Lemma lem2723986 (n : int) : (term520 n) = (term460 n).
Proof. exact (@lem1982713 term193 (term104 n)). Qed.
Lemma lem2723988 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2723989 : term110 = term214.
Proof. exact (@lem2723988 term111). Qed.
Lemma lem2723991 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2723992 : term193 = term194.
Proof. exact (@lem2723991 term111). Qed.
Lemma lem2723993 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2723994 : term461 = term462.
Proof. exact (MK_COMB (@lem2723993) (@lem2723992)). Qed.
Lemma lem2723995 : term463 = term464.
Proof. exact (MK_COMB (@lem2723994) (@lem2723989)). Qed.
Lemma lem2723996 : term465.
Proof. exact (@lem1981473 term193 term110 term110 term110 term107 term110). Qed.
Lemma lem2723998 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2723999 : term257 = term258.
Proof. exact (@lem2723998 (NUMERAL 0) term111). Qed.
Lemma lem2724000 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2724001 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2724002 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2724001 h1) (fun h1 : term258 = True => @lem2724000)). Qed.
Lemma lem2724003 : term258 = True.
Proof. exact (EQ_MP (@lem2724002) (@lem2724000)). Qed.
Lemma lem2724004 : term257 = True.
Proof. exact (TRANS (@lem2723999) (@lem2724003)). Qed.
Lemma lem2724005 : True = term257.
Proof. exact (SYM (@lem2724004)). Qed.
Lemma lem2724006 : term257.
Proof. exact (EQ_MP (@lem2724005) (@lem0)). Qed.
Lemma lem2724007 : term466.
Proof. exact (@lem2723996 (@lem2724006)). Qed.
Lemma lem2724009 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2724010 : term257 = term258.
Proof. exact (@lem2724009 (NUMERAL 0) term111). Qed.
Lemma lem2724011 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2724012 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2724013 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2724012 h1) (fun h1 : term258 = True => @lem2724011)). Qed.
Lemma lem2724014 : term258 = True.
Proof. exact (EQ_MP (@lem2724013) (@lem2724011)). Qed.
Lemma lem2724015 : term257 = True.
Proof. exact (TRANS (@lem2724010) (@lem2724014)). Qed.
Lemma lem2724016 : True = term257.
Proof. exact (SYM (@lem2724015)). Qed.
Lemma lem2724017 : term257.
Proof. exact (EQ_MP (@lem2724016) (@lem0)). Qed.
Lemma lem2724018 : term467.
Proof. exact (@lem2724007 (@lem2724017)). Qed.
Lemma lem2724020 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2724021 : term257 = term258.
Proof. exact (@lem2724020 (NUMERAL 0) term111). Qed.
Lemma lem2724022 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2724023 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2724024 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2724023 h1) (fun h1 : term258 = True => @lem2724022)). Qed.
Lemma lem2724025 : term258 = True.
Proof. exact (EQ_MP (@lem2724024) (@lem2724022)). Qed.
Lemma lem2724026 : term257 = True.
Proof. exact (TRANS (@lem2724021) (@lem2724025)). Qed.
Lemma lem2724027 : True = term257.
Proof. exact (SYM (@lem2724026)). Qed.
Lemma lem2724028 : term257.
Proof. exact (EQ_MP (@lem2724027) (@lem0)). Qed.
Lemma lem2724029 : term468.
Proof. exact (@lem2724018 (@lem2724028)). Qed.
Lemma lem2724031 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2724032 : term202 = term203.
Proof. exact (@lem2724031 term111 term111). Qed.
Lemma lem2724033 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2724034 : term205 = term111.
Proof. exact (EQ_MP (@lem2724033) (@lem940073)). Qed.
Lemma lem2724035 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2724036 : term203 = term110.
Proof. exact (MK_COMB (@lem2724035) (@lem2724034)). Qed.
Lemma lem2724037 : term202 = term110.
Proof. exact (TRANS (@lem2724032) (@lem2724036)). Qed.
Lemma lem2724039 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2724040 : term215 = term220.
Proof. exact (@lem2724039 term111 term111). Qed.
Lemma lem2724041 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2724042 : term205 = term111.
Proof. exact (EQ_MP (@lem2724041) (@lem940073)). Qed.
Lemma lem2724043 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2724044 : term203 = term110.
Proof. exact (MK_COMB (@lem2724043) (@lem2724042)). Qed.
Lemma lem2724045 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2724046 : term220 = term193.
Proof. exact (MK_COMB (@lem2724045) (@lem2724044)). Qed.
Lemma lem2724047 : term215 = term193.
Proof. exact (TRANS (@lem2724040) (@lem2724046)). Qed.
Lemma lem2724048 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2724049 : term469 = term461.
Proof. exact (MK_COMB (@lem2724048) (@lem2724047)). Qed.
Lemma lem2724050 : term470 = term463.
Proof. exact (MK_COMB (@lem2724049) (@lem2724037)). Qed.
Lemma lem2724052 (m : nat) : (term471 m) = term107.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2724053 : term463 = term107.
Proof. exact (@lem2724052 term111). Qed.
Lemma lem2724054 : term470 = term107.
Proof. exact (TRANS (@lem2724050) (@lem2724053)). Qed.
Lemma lem2724055 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2724056 : term472 = term267.
Proof. exact (MK_COMB (@lem2724055) (@lem2724054)). Qed.
Lemma lem2724057 : term110 = term110.
Proof. exact (eq_refl term110). Qed.
Lemma lem2724058 : term473 = term269.
Proof. exact (MK_COMB (@lem2724056) (@lem2724057)). Qed.
Lemma lem2724060 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2724061 : term269 = term107.
Proof. exact (@lem2724060 term111). Qed.
Lemma lem2724062 : term473 = term107.
Proof. exact (TRANS (@lem2724058) (@lem2724061)). Qed.
Lemma lem2724064 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2724065 : term202 = term203.
Proof. exact (@lem2724064 term111 term111). Qed.
Lemma lem2724066 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2724067 : term205 = term111.
Proof. exact (EQ_MP (@lem2724066) (@lem940073)). Qed.
Lemma lem2724068 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2724069 : term203 = term110.
Proof. exact (MK_COMB (@lem2724068) (@lem2724067)). Qed.
Lemma lem2724070 : term202 = term110.
Proof. exact (TRANS (@lem2724065) (@lem2724069)). Qed.
Lemma lem2724071 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2724072 : term271 = term269.
Proof. exact (MK_COMB (@lem2724071) (@lem2724070)). Qed.
Lemma lem2724074 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2724075 : term269 = term107.
Proof. exact (@lem2724074 term111). Qed.
Lemma lem2724076 : term271 = term107.
Proof. exact (TRANS (@lem2724072) (@lem2724075)). Qed.
Lemma lem2724077 : term107 = term271.
Proof. exact (SYM (@lem2724076)). Qed.
Lemma lem2724078 : term473 = term271.
Proof. exact (TRANS (@lem2724062) (@lem2724077)). Qed.
Lemma lem2724079 : term464 = term190.
Proof. exact (@lem2724029 (@lem2724078)). Qed.
Lemma lem2724080 : term463 = term190.
Proof. exact (TRANS (@lem2723995) (@lem2724079)). Qed.
Lemma lem2724082 (x : real) : (term209 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2724083 : term190 = term107.
Proof. exact (@lem2724082 term107). Qed.
Lemma lem2724084 : term463 = term107.
Proof. exact (TRANS (@lem2724080) (@lem2724083)). Qed.
Lemma lem2724085 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2724086 : term474 = term267.
Proof. exact (MK_COMB (@lem2724085) (@lem2724084)). Qed.
Lemma lem2724087 (n : int) : (term104 n) = (term104 n).
Proof. exact (eq_refl (term104 n)). Qed.
Lemma lem2724088 (n : int) : (term460 n) = (term475 n).
Proof. exact (MK_COMB (@lem2724086) (@lem2724087 n)). Qed.
Lemma lem2724089 (n : int) : (term520 n) = (term475 n).
Proof. exact (TRANS (@lem2723986 n) (@lem2724088 n)). Qed.
Lemma lem2724090 (n : int) : (term475 n) = term107.
Proof. exact (@lem1982719 (term104 n)). Qed.
Lemma lem2724091 (n : int) : (term520 n) = term107.
Proof. exact (TRANS (@lem2724089 n) (@lem2724090 n)). Qed.
Lemma lem2724092 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2724093 (n : int) : (term521 n) = term139.
Proof. exact (MK_COMB (@lem2724092) (@lem2724091 n)). Qed.
Lemma lem2724094 : term193 = term193.
Proof. exact (eq_refl term193). Qed.
Lemma lem2724095 (n : int) : (term519 n) = term477.
Proof. exact (MK_COMB (@lem2724093 n) (@lem2724094)). Qed.
Lemma lem2724096 (n : int) : (term518 n) = term477.
Proof. exact (TRANS (@lem2723985 n) (@lem2724095 n)). Qed.
Lemma lem2724097 : term477 = term193.
Proof. exact (@lem1982721 term193). Qed.
Lemma lem2724098 (n : int) : (term518 n) = term193.
Proof. exact (TRANS (@lem2724096 n) (@lem2724097)). Qed.
Lemma lem2724099 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2724100 (n : int) : (term522 n) = term479.
Proof. exact (MK_COMB (@lem2724099) (@lem2724098 n)). Qed.
Lemma lem2724101 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2724102 (n : int) : (term517 n) = term480.
Proof. exact (MK_COMB (@lem2724100 n) (@lem2724101)). Qed.
Lemma lem2724103 (n : int) (h1 : term620 n) : term480.
Proof. exact (EQ_MP (@lem2724102 n) (@lem2723984 n h1)). Qed.
Lemma lem2724105 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2724106 : term480 = term481.
Proof. exact (@lem2724105 term107 term193). Qed.
Lemma lem2724108 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2724109 : term193 = term194.
Proof. exact (@lem2724108 term111). Qed.
Lemma lem2724111 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2724112 : term107 = term190.
Proof. exact (@lem2724111 (NUMERAL 0)). Qed.
Lemma lem2724113 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2724114 : term482 = term483.
Proof. exact (MK_COMB (@lem2724113) (@lem2724112)). Qed.
Lemma lem2724115 : term481 = term484.
Proof. exact (MK_COMB (@lem2724114) (@lem2724109)). Qed.
Lemma lem2724116 : term485.
Proof. exact (@lem1980026 term107 term110 term193 term110). Qed.
Lemma lem2724118 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2724119 : term257 = term258.
Proof. exact (@lem2724118 (NUMERAL 0) term111). Qed.
Lemma lem2724120 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2724121 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2724122 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2724121 h1) (fun h1 : term258 = True => @lem2724120)). Qed.
Lemma lem2724123 : term258 = True.
Proof. exact (EQ_MP (@lem2724122) (@lem2724120)). Qed.
Lemma lem2724124 : term257 = True.
Proof. exact (TRANS (@lem2724119) (@lem2724123)). Qed.
Lemma lem2724125 : True = term257.
Proof. exact (SYM (@lem2724124)). Qed.
Lemma lem2724126 : term257.
Proof. exact (EQ_MP (@lem2724125) (@lem0)). Qed.
Lemma lem2724127 : term486.
Proof. exact (@lem2724116 (@lem2724126)). Qed.
Lemma lem2724129 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2724130 : term257 = term258.
Proof. exact (@lem2724129 (NUMERAL 0) term111). Qed.
Lemma lem2724131 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2724132 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2724133 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2724132 h1) (fun h1 : term258 = True => @lem2724131)). Qed.
Lemma lem2724134 : term258 = True.
Proof. exact (EQ_MP (@lem2724133) (@lem2724131)). Qed.
Lemma lem2724135 : term257 = True.
Proof. exact (TRANS (@lem2724130) (@lem2724134)). Qed.
Lemma lem2724136 : True = term257.
Proof. exact (SYM (@lem2724135)). Qed.
Lemma lem2724137 : term257.
Proof. exact (EQ_MP (@lem2724136) (@lem0)). Qed.
Lemma lem2724138 : term484 = term487.
Proof. exact (@lem2724127 (@lem2724137)). Qed.
Lemma lem2724140 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2724141 : term215 = term220.
Proof. exact (@lem2724140 term111 term111). Qed.
Lemma lem2724142 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2724143 : term205 = term111.
Proof. exact (EQ_MP (@lem2724142) (@lem940073)). Qed.
Lemma lem2724144 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2724145 : term203 = term110.
Proof. exact (MK_COMB (@lem2724144) (@lem2724143)). Qed.
Lemma lem2724146 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2724147 : term220 = term193.
Proof. exact (MK_COMB (@lem2724146) (@lem2724145)). Qed.
Lemma lem2724148 : term215 = term193.
Proof. exact (TRANS (@lem2724141) (@lem2724147)). Qed.
Lemma lem2724150 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2724151 : term269 = term107.
Proof. exact (@lem2724150 term111). Qed.
Lemma lem2724152 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2724153 : term488 = term482.
Proof. exact (MK_COMB (@lem2724152) (@lem2724151)). Qed.
Lemma lem2724154 : term487 = term481.
Proof. exact (MK_COMB (@lem2724153) (@lem2724148)). Qed.
Lemma lem2724156 (m : nat) (n : nat) : (term489 m n) = (term490 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2724157 : term481 = term491.
Proof. exact (@lem2724156 (NUMERAL 0) term111). Qed.
Lemma lem2724158 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2724159 (h1 : term259 = (BIT1 0)) : (term111 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2724160 : (term259 = (BIT1 0)) = ((term111 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2724159 h1) (fun h1 : (term111 = (NUMERAL 0)) = False => @lem2724158)). Qed.
Lemma lem2724161 : (term111 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2724160) (@lem2724158)). Qed.
Lemma lem2724162 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2724163 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2724164 : term492 = (and True).
Proof. exact (MK_COMB (@lem2724163) (@lem2724162)). Qed.
Lemma lem2724165 : term491 = (True /\ False).
Proof. exact (MK_COMB (@lem2724164) (@lem2724161)). Qed.
Lemma lem2724167 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2724168 : term491 = False.
Proof. exact (TRANS (@lem2724165) (@lem2724167)). Qed.
Lemma lem2724169 : term481 = False.
Proof. exact (TRANS (@lem2724157) (@lem2724168)). Qed.
Lemma lem2724170 : term487 = False.
Proof. exact (TRANS (@lem2724154) (@lem2724169)). Qed.
Lemma lem2724171 : term484 = False.
Proof. exact (TRANS (@lem2724138) (@lem2724170)). Qed.
Lemma lem2724172 : term481 = False.
Proof. exact (TRANS (@lem2724115) (@lem2724171)). Qed.
Lemma lem2724173 : term480 = False.
Proof. exact (TRANS (@lem2724106) (@lem2724172)). Qed.
Lemma lem2724174 (n : int) (h1 : term620 n) : False.
Proof. exact (EQ_MP (@lem2724173) (@lem2724103 n h1)). Qed.
Lemma lem2724175 (n : int) (h1 : term621 n) : term621 n.
Proof. exact (h1). Qed.
Lemma lem2724176 (n : int) (h1 : term621 n) : term368 n.
Proof. exact (proj2 (@lem2724175 n h1)). Qed.
Lemma lem2724177 (n : int) (h1 : term621 n) : (term223 n) = term107.
Proof. exact (proj1 (@lem2724175 n h1)). Qed.
Lemma lem2724179 (n : int) (h1 : term621 n) : term315 n.
Proof. exact (proj1 (@lem2724176 n h1)). Qed.
Lemma lem2724181 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2724182 : term433 = term257.
Proof. exact (@lem2724181 term107 term110). Qed.
Lemma lem2724184 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2724185 : term110 = term214.
Proof. exact (@lem2724184 term111). Qed.
Lemma lem2724187 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2724188 : term107 = term190.
Proof. exact (@lem2724187 (NUMERAL 0)). Qed.
Lemma lem2724189 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2724190 : term434 = term435.
Proof. exact (MK_COMB (@lem2724189) (@lem2724188)). Qed.
Lemma lem2724191 : term257 = term436.
Proof. exact (MK_COMB (@lem2724190) (@lem2724185)). Qed.
Lemma lem2724192 : term437.
Proof. exact (@lem1980255 term107 term110 term110 term110). Qed.
Lemma lem2724194 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2724195 : term257 = term258.
Proof. exact (@lem2724194 (NUMERAL 0) term111). Qed.
Lemma lem2724196 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2724197 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2724198 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2724197 h1) (fun h1 : term258 = True => @lem2724196)). Qed.
Lemma lem2724199 : term258 = True.
Proof. exact (EQ_MP (@lem2724198) (@lem2724196)). Qed.
Lemma lem2724200 : term257 = True.
Proof. exact (TRANS (@lem2724195) (@lem2724199)). Qed.
Lemma lem2724201 : True = term257.
Proof. exact (SYM (@lem2724200)). Qed.
Lemma lem2724202 : term257.
Proof. exact (EQ_MP (@lem2724201) (@lem0)). Qed.
Lemma lem2724203 : term438.
Proof. exact (@lem2724192 (@lem2724202)). Qed.
Lemma lem2724205 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2724206 : term257 = term258.
Proof. exact (@lem2724205 (NUMERAL 0) term111). Qed.
Lemma lem2724207 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2724208 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2724209 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2724208 h1) (fun h1 : term258 = True => @lem2724207)). Qed.
Lemma lem2724210 : term258 = True.
Proof. exact (EQ_MP (@lem2724209) (@lem2724207)). Qed.
Lemma lem2724211 : term257 = True.
Proof. exact (TRANS (@lem2724206) (@lem2724210)). Qed.
Lemma lem2724212 : True = term257.
Proof. exact (SYM (@lem2724211)). Qed.
Lemma lem2724213 : term257.
Proof. exact (EQ_MP (@lem2724212) (@lem0)). Qed.
Lemma lem2724214 : term436 = term439.
Proof. exact (@lem2724203 (@lem2724213)). Qed.
Lemma lem2724216 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2724217 : term202 = term203.
Proof. exact (@lem2724216 term111 term111). Qed.
Lemma lem2724218 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2724219 : term205 = term111.
Proof. exact (EQ_MP (@lem2724218) (@lem940073)). Qed.
Lemma lem2724220 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2724221 : term203 = term110.
Proof. exact (MK_COMB (@lem2724220) (@lem2724219)). Qed.
Lemma lem2724222 : term202 = term110.
Proof. exact (TRANS (@lem2724217) (@lem2724221)). Qed.
Lemma lem2724224 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2724225 : term269 = term107.
Proof. exact (@lem2724224 term111). Qed.
Lemma lem2724226 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2724227 : term440 = term434.
Proof. exact (MK_COMB (@lem2724226) (@lem2724225)). Qed.
Lemma lem2724228 : term439 = term257.
Proof. exact (MK_COMB (@lem2724227) (@lem2724222)). Qed.
Lemma lem2724230 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2724231 : term257 = term258.
Proof. exact (@lem2724230 (NUMERAL 0) term111). Qed.
Lemma lem2724232 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2724233 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2724234 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2724233 h1) (fun h1 : term258 = True => @lem2724232)). Qed.
Lemma lem2724235 : term258 = True.
Proof. exact (EQ_MP (@lem2724234) (@lem2724232)). Qed.
Lemma lem2724236 : term257 = True.
Proof. exact (TRANS (@lem2724231) (@lem2724235)). Qed.
Lemma lem2724237 : term439 = True.
Proof. exact (TRANS (@lem2724228) (@lem2724236)). Qed.
Lemma lem2724238 : term436 = True.
Proof. exact (TRANS (@lem2724214) (@lem2724237)). Qed.
Lemma lem2724239 : term257 = True.
Proof. exact (TRANS (@lem2724191) (@lem2724238)). Qed.
Lemma lem2724240 : term433 = True.
Proof. exact (TRANS (@lem2724182) (@lem2724239)). Qed.
Lemma lem2724241 : True = term433.
Proof. exact (SYM (@lem2724240)). Qed.
Lemma lem2724242 : term433.
Proof. exact (EQ_MP (@lem2724241) (@lem0)). Qed.
Lemma lem2724243 (n : int) (h1 : term621 n) : term525 n.
Proof. exact (conj (@lem2724242) (@lem2724179 n h1)). Qed.
Lemma lem2724245 (x : real) (y : real) : term442 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2724246 (n : int) : term526 n.
Proof. exact (@lem2724245 term110 (term312 n)). Qed.
Lemma lem2724247 (n : int) (h1 : term621 n) : term527 n.
Proof. exact (@lem2724246 n (@lem2724243 n h1)). Qed.
Lemma lem2724248 (n : int) : (term528 n) = (term312 n).
Proof. exact (@lem1982733 (term312 n)). Qed.
Lemma lem2724249 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2724250 (n : int) : (term529 n) = (term314 n).
Proof. exact (MK_COMB (@lem2724249) (@lem2724248 n)). Qed.
Lemma lem2724251 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2724252 (n : int) : (term527 n) = (term315 n).
Proof. exact (MK_COMB (@lem2724250 n) (@lem2724251)). Qed.
Lemma lem2724253 (n : int) (h1 : term621 n) : term315 n.
Proof. exact (EQ_MP (@lem2724252 n) (@lem2724247 n h1)). Qed.
Lemma lem2724255 (y : real) : term447 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2724256 (n : int) : term499 n.
Proof. exact (@lem2724255 (term223 n)). Qed.
Lemma lem2724257 (n : int) (h1 : term621 n) : term500 n.
Proof. exact (@lem2724256 n (@lem2724177 n h1)). Qed.
Lemma lem2724258 (n : int) (h1 : term621 n) : term549 n.
Proof. exact (@lem2724257 n h1 term193). Qed.
Lemma lem2724259 (n : int) : (term549 n) = ((term550 n) = term107).
Proof. exact (eq_refl (term549 n)). Qed.
Lemma lem2724260 (n : int) (h1 : term621 n) : (term550 n) = term107.
Proof. exact (EQ_MP (@lem2724259 n) (@lem2724258 n h1)). Qed.
Lemma lem2724261 (n : int) : (term550 n) = (term551 n).
Proof. exact (@lem1982781 (term104 n) term193 term193). Qed.
Lemma lem2724263 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2724264 : term193 = term194.
Proof. exact (@lem2724263 term111). Qed.
Lemma lem2724266 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2724267 : term193 = term194.
Proof. exact (@lem2724266 term111). Qed.
Lemma lem2724268 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2724269 : term195 = term196.
Proof. exact (MK_COMB (@lem2724268) (@lem2724267)). Qed.
Lemma lem2724270 : term552 = term553.
Proof. exact (MK_COMB (@lem2724269) (@lem2724264)). Qed.
Lemma lem2724271 : term553 = term554.
Proof. exact (@lem1981613 term193 term193 term110 term110). Qed.
Lemma lem2724273 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2724274 : term202 = term203.
Proof. exact (@lem2724273 term111 term111). Qed.
Lemma lem2724275 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2724276 : term205 = term111.
Proof. exact (EQ_MP (@lem2724275) (@lem940073)). Qed.
Lemma lem2724277 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2724278 : term203 = term110.
Proof. exact (MK_COMB (@lem2724277) (@lem2724276)). Qed.
Lemma lem2724279 : term202 = term110.
Proof. exact (TRANS (@lem2724274) (@lem2724278)). Qed.
Lemma lem2724281 (m : nat) (n : nat) : (term555 m n) = (term201 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem2724282 : term552 = term203.
Proof. exact (@lem2724281 term111 term111). Qed.
Lemma lem2724283 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2724284 : term205 = term111.
Proof. exact (EQ_MP (@lem2724283) (@lem940073)). Qed.
Lemma lem2724285 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2724286 : term203 = term110.
Proof. exact (MK_COMB (@lem2724285) (@lem2724284)). Qed.
Lemma lem2724287 : term552 = term110.
Proof. exact (TRANS (@lem2724282) (@lem2724286)). Qed.
Lemma lem2724288 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2724289 : term556 = term557.
Proof. exact (MK_COMB (@lem2724288) (@lem2724287)). Qed.
Lemma lem2724290 : term554 = term214.
Proof. exact (MK_COMB (@lem2724289) (@lem2724279)). Qed.
Lemma lem2724291 : term553 = term214.
Proof. exact (TRANS (@lem2724271) (@lem2724290)). Qed.
Lemma lem2724292 : term552 = term214.
Proof. exact (TRANS (@lem2724270) (@lem2724291)). Qed.
Lemma lem2724294 (x : real) : (term209 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2724295 : term214 = term110.
Proof. exact (@lem2724294 term110). Qed.
Lemma lem2724296 : term552 = term110.
Proof. exact (TRANS (@lem2724292) (@lem2724295)). Qed.
Lemma lem2724299 (n : int) : (term232 n) = (term232 n).
Proof. exact (eq_refl (term232 n)). Qed.
Lemma lem2724300 (n : int) : (term551 n) = (term558 n).
Proof. exact (MK_COMB (@lem2724299 n) (@lem2724296)). Qed.
Lemma lem2724301 (n : int) : (term550 n) = (term558 n).
Proof. exact (TRANS (@lem2724261 n) (@lem2724300 n)). Qed.
Lemma lem2724302 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2724303 (n : int) : (term559 n) = (term560 n).
Proof. exact (MK_COMB (@lem2724302) (@lem2724301 n)). Qed.
Lemma lem2724304 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2724305 (n : int) : ((term550 n) = term107) = ((term558 n) = term107).
Proof. exact (MK_COMB (@lem2724303 n) (@lem2724304)). Qed.
Lemma lem2724306 (n : int) (h1 : term621 n) : (term558 n) = term107.
Proof. exact (EQ_MP (@lem2724305 n) (@lem2724260 n h1)). Qed.
Lemma lem2724307 (n : int) (h1 : term621 n) : term561 n.
Proof. exact (conj (@lem2724306 n h1) (@lem2724253 n h1)). Qed.
Lemma lem2724309 (x : real) (y : real) : term454 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem2724310 (n : int) : term562 n.
Proof. exact (@lem2724309 (term558 n) (term312 n)). Qed.
Lemma lem2724311 (n : int) (h1 : term621 n) : term563 n.
Proof. exact (@lem2724310 n (@lem2724307 n h1)). Qed.
Lemma lem2724312 (n : int) : (term564 n) = (term565 n).
Proof. exact (@lem1982753 (term251 n) (term104 n) term110 term308). Qed.
Lemma lem2724313 (n : int) : (term520 n) = (term460 n).
Proof. exact (@lem1982713 term193 (term104 n)). Qed.
Lemma lem2724315 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2724316 : term110 = term214.
Proof. exact (@lem2724315 term111). Qed.
Lemma lem2724318 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2724319 : term193 = term194.
Proof. exact (@lem2724318 term111). Qed.
Lemma lem2724320 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2724321 : term461 = term462.
Proof. exact (MK_COMB (@lem2724320) (@lem2724319)). Qed.
Lemma lem2724322 : term463 = term464.
Proof. exact (MK_COMB (@lem2724321) (@lem2724316)). Qed.
Lemma lem2724323 : term465.
Proof. exact (@lem1981473 term193 term110 term110 term110 term107 term110). Qed.
Lemma lem2724325 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2724326 : term257 = term258.
Proof. exact (@lem2724325 (NUMERAL 0) term111). Qed.
Lemma lem2724327 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2724328 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2724329 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2724328 h1) (fun h1 : term258 = True => @lem2724327)). Qed.
Lemma lem2724330 : term258 = True.
Proof. exact (EQ_MP (@lem2724329) (@lem2724327)). Qed.
Lemma lem2724331 : term257 = True.
Proof. exact (TRANS (@lem2724326) (@lem2724330)). Qed.
Lemma lem2724332 : True = term257.
Proof. exact (SYM (@lem2724331)). Qed.
Lemma lem2724333 : term257.
Proof. exact (EQ_MP (@lem2724332) (@lem0)). Qed.
Lemma lem2724334 : term466.
Proof. exact (@lem2724323 (@lem2724333)). Qed.
Lemma lem2724336 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2724337 : term257 = term258.
Proof. exact (@lem2724336 (NUMERAL 0) term111). Qed.
Lemma lem2724338 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2724339 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2724340 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2724339 h1) (fun h1 : term258 = True => @lem2724338)). Qed.
Lemma lem2724341 : term258 = True.
Proof. exact (EQ_MP (@lem2724340) (@lem2724338)). Qed.
Lemma lem2724342 : term257 = True.
Proof. exact (TRANS (@lem2724337) (@lem2724341)). Qed.
Lemma lem2724343 : True = term257.
Proof. exact (SYM (@lem2724342)). Qed.
Lemma lem2724344 : term257.
Proof. exact (EQ_MP (@lem2724343) (@lem0)). Qed.
Lemma lem2724345 : term467.
Proof. exact (@lem2724334 (@lem2724344)). Qed.
Lemma lem2724347 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2724348 : term257 = term258.
Proof. exact (@lem2724347 (NUMERAL 0) term111). Qed.
Lemma lem2724349 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2724350 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2724351 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2724350 h1) (fun h1 : term258 = True => @lem2724349)). Qed.
Lemma lem2724352 : term258 = True.
Proof. exact (EQ_MP (@lem2724351) (@lem2724349)). Qed.
Lemma lem2724353 : term257 = True.
Proof. exact (TRANS (@lem2724348) (@lem2724352)). Qed.
Lemma lem2724354 : True = term257.
Proof. exact (SYM (@lem2724353)). Qed.
Lemma lem2724355 : term257.
Proof. exact (EQ_MP (@lem2724354) (@lem0)). Qed.
Lemma lem2724356 : term468.
Proof. exact (@lem2724345 (@lem2724355)). Qed.
Lemma lem2724358 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2724359 : term202 = term203.
Proof. exact (@lem2724358 term111 term111). Qed.
Lemma lem2724360 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2724361 : term205 = term111.
Proof. exact (EQ_MP (@lem2724360) (@lem940073)). Qed.
Lemma lem2724362 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2724363 : term203 = term110.
Proof. exact (MK_COMB (@lem2724362) (@lem2724361)). Qed.
Lemma lem2724364 : term202 = term110.
Proof. exact (TRANS (@lem2724359) (@lem2724363)). Qed.
Lemma lem2724366 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2724367 : term215 = term220.
Proof. exact (@lem2724366 term111 term111). Qed.
Lemma lem2724368 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2724369 : term205 = term111.
Proof. exact (EQ_MP (@lem2724368) (@lem940073)). Qed.
Lemma lem2724370 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2724371 : term203 = term110.
Proof. exact (MK_COMB (@lem2724370) (@lem2724369)). Qed.
Lemma lem2724372 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2724373 : term220 = term193.
Proof. exact (MK_COMB (@lem2724372) (@lem2724371)). Qed.
Lemma lem2724374 : term215 = term193.
Proof. exact (TRANS (@lem2724367) (@lem2724373)). Qed.
Lemma lem2724375 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2724376 : term469 = term461.
Proof. exact (MK_COMB (@lem2724375) (@lem2724374)). Qed.
Lemma lem2724377 : term470 = term463.
Proof. exact (MK_COMB (@lem2724376) (@lem2724364)). Qed.
Lemma lem2724379 (m : nat) : (term471 m) = term107.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2724380 : term463 = term107.
Proof. exact (@lem2724379 term111). Qed.
Lemma lem2724381 : term470 = term107.
Proof. exact (TRANS (@lem2724377) (@lem2724380)). Qed.
Lemma lem2724382 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2724383 : term472 = term267.
Proof. exact (MK_COMB (@lem2724382) (@lem2724381)). Qed.
Lemma lem2724384 : term110 = term110.
Proof. exact (eq_refl term110). Qed.
Lemma lem2724385 : term473 = term269.
Proof. exact (MK_COMB (@lem2724383) (@lem2724384)). Qed.
Lemma lem2724387 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2724388 : term269 = term107.
Proof. exact (@lem2724387 term111). Qed.
Lemma lem2724389 : term473 = term107.
Proof. exact (TRANS (@lem2724385) (@lem2724388)). Qed.
Lemma lem2724391 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2724392 : term202 = term203.
Proof. exact (@lem2724391 term111 term111). Qed.
Lemma lem2724393 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2724394 : term205 = term111.
Proof. exact (EQ_MP (@lem2724393) (@lem940073)). Qed.
Lemma lem2724395 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2724396 : term203 = term110.
Proof. exact (MK_COMB (@lem2724395) (@lem2724394)). Qed.
Lemma lem2724397 : term202 = term110.
Proof. exact (TRANS (@lem2724392) (@lem2724396)). Qed.
Lemma lem2724398 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2724399 : term271 = term269.
Proof. exact (MK_COMB (@lem2724398) (@lem2724397)). Qed.
Lemma lem2724401 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2724402 : term269 = term107.
Proof. exact (@lem2724401 term111). Qed.
Lemma lem2724403 : term271 = term107.
Proof. exact (TRANS (@lem2724399) (@lem2724402)). Qed.
Lemma lem2724404 : term107 = term271.
Proof. exact (SYM (@lem2724403)). Qed.
Lemma lem2724405 : term473 = term271.
Proof. exact (TRANS (@lem2724389) (@lem2724404)). Qed.
Lemma lem2724406 : term464 = term190.
Proof. exact (@lem2724356 (@lem2724405)). Qed.
Lemma lem2724407 : term463 = term190.
Proof. exact (TRANS (@lem2724322) (@lem2724406)). Qed.
Lemma lem2724409 (x : real) : (term209 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2724410 : term190 = term107.
Proof. exact (@lem2724409 term107). Qed.
Lemma lem2724411 : term463 = term107.
Proof. exact (TRANS (@lem2724407) (@lem2724410)). Qed.
Lemma lem2724412 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2724413 : term474 = term267.
Proof. exact (MK_COMB (@lem2724412) (@lem2724411)). Qed.
Lemma lem2724414 (n : int) : (term104 n) = (term104 n).
Proof. exact (eq_refl (term104 n)). Qed.
Lemma lem2724415 (n : int) : (term460 n) = (term475 n).
Proof. exact (MK_COMB (@lem2724413) (@lem2724414 n)). Qed.
Lemma lem2724416 (n : int) : (term520 n) = (term475 n).
Proof. exact (TRANS (@lem2724313 n) (@lem2724415 n)). Qed.
Lemma lem2724417 (n : int) : (term475 n) = term107.
Proof. exact (@lem1982719 (term104 n)). Qed.
Lemma lem2724418 (n : int) : (term520 n) = term107.
Proof. exact (TRANS (@lem2724416 n) (@lem2724417 n)). Qed.
Lemma lem2724419 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2724420 (n : int) : (term521 n) = term139.
Proof. exact (MK_COMB (@lem2724419) (@lem2724418 n)). Qed.
Lemma lem2724422 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2724423 : term308 = term311.
Proof. exact (@lem2724422 term288). Qed.
Lemma lem2724425 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2724426 : term110 = term214.
Proof. exact (@lem2724425 term111). Qed.
Lemma lem2724427 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2724428 : term157 = term252.
Proof. exact (MK_COMB (@lem2724427) (@lem2724426)). Qed.
Lemma lem2724429 : term566 = term567.
Proof. exact (MK_COMB (@lem2724428) (@lem2724423)). Qed.
Lemma lem2724430 : term568.
Proof. exact (@lem1981473 term110 term110 term308 term110 term193 term110). Qed.
Lemma lem2724432 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2724433 : term257 = term258.
Proof. exact (@lem2724432 (NUMERAL 0) term111). Qed.
Lemma lem2724434 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2724435 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2724436 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2724435 h1) (fun h1 : term258 = True => @lem2724434)). Qed.
Lemma lem2724437 : term258 = True.
Proof. exact (EQ_MP (@lem2724436) (@lem2724434)). Qed.
Lemma lem2724438 : term257 = True.
Proof. exact (TRANS (@lem2724433) (@lem2724437)). Qed.
Lemma lem2724439 : True = term257.
Proof. exact (SYM (@lem2724438)). Qed.
Lemma lem2724440 : term257.
Proof. exact (EQ_MP (@lem2724439) (@lem0)). Qed.
Lemma lem2724441 : term569.
Proof. exact (@lem2724430 (@lem2724440)). Qed.
Lemma lem2724443 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2724444 : term257 = term258.
Proof. exact (@lem2724443 (NUMERAL 0) term111). Qed.
Lemma lem2724445 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2724446 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2724447 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2724446 h1) (fun h1 : term258 = True => @lem2724445)). Qed.
Lemma lem2724448 : term258 = True.
Proof. exact (EQ_MP (@lem2724447) (@lem2724445)). Qed.
Lemma lem2724449 : term257 = True.
Proof. exact (TRANS (@lem2724444) (@lem2724448)). Qed.
Lemma lem2724450 : True = term257.
Proof. exact (SYM (@lem2724449)). Qed.
Lemma lem2724451 : term257.
Proof. exact (EQ_MP (@lem2724450) (@lem0)). Qed.
Lemma lem2724452 : term570.
Proof. exact (@lem2724441 (@lem2724451)). Qed.
Lemma lem2724454 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2724455 : term257 = term258.
Proof. exact (@lem2724454 (NUMERAL 0) term111). Qed.
Lemma lem2724456 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2724457 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2724458 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2724457 h1) (fun h1 : term258 = True => @lem2724456)). Qed.
Lemma lem2724459 : term258 = True.
Proof. exact (EQ_MP (@lem2724458) (@lem2724456)). Qed.
Lemma lem2724460 : term257 = True.
Proof. exact (TRANS (@lem2724455) (@lem2724459)). Qed.
Lemma lem2724461 : True = term257.
Proof. exact (SYM (@lem2724460)). Qed.
Lemma lem2724462 : term257.
Proof. exact (EQ_MP (@lem2724461) (@lem0)). Qed.
Lemma lem2724463 : term571.
Proof. exact (@lem2724452 (@lem2724462)). Qed.
Lemma lem2724465 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2724466 : term544 = term545.
Proof. exact (@lem2724465 term288 term111). Qed.
Lemma lem2724467 : term294 = term286.
Proof. exact (@lem996237 term286). Qed.
Lemma lem2724468 : (term294 = term286) = (term295 = term288).
Proof. exact (@lem1007663 term286 (BIT1 0) term286). Qed.
Lemma lem2724469 : term295 = term288.
Proof. exact (EQ_MP (@lem2724468) (@lem2724467)). Qed.
Lemma lem2724470 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2724471 : term293 = term279.
Proof. exact (MK_COMB (@lem2724470) (@lem2724469)). Qed.
Lemma lem2724472 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2724473 : term545 = term308.
Proof. exact (MK_COMB (@lem2724472) (@lem2724471)). Qed.
Lemma lem2724474 : term544 = term308.
Proof. exact (TRANS (@lem2724466) (@lem2724473)). Qed.
Lemma lem2724476 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2724477 : term202 = term203.
Proof. exact (@lem2724476 term111 term111). Qed.
Lemma lem2724478 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2724479 : term205 = term111.
Proof. exact (EQ_MP (@lem2724478) (@lem940073)). Qed.
Lemma lem2724480 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2724481 : term203 = term110.
Proof. exact (MK_COMB (@lem2724480) (@lem2724479)). Qed.
Lemma lem2724482 : term202 = term110.
Proof. exact (TRANS (@lem2724477) (@lem2724481)). Qed.
Lemma lem2724483 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2724484 : term263 = term157.
Proof. exact (MK_COMB (@lem2724483) (@lem2724482)). Qed.
Lemma lem2724485 : term572 = term566.
Proof. exact (MK_COMB (@lem2724484) (@lem2724474)). Qed.
Lemma lem2724488 : term573 = term193.
Proof. exact (@lem1367771 term111 term111). Qed.
Lemma lem2724489 : term285 = term286.
Proof. exact (@lem706885). Qed.
Lemma lem2724490 : (term285 = term286) = (term287 = term288).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term286). Qed.
Lemma lem2724491 : term287 = term288.
Proof. exact (EQ_MP (@lem2724490) (@lem2724489)). Qed.
Lemma lem2724492 : term288 = term287.
Proof. exact (SYM (@lem2724491)). Qed.
Lemma lem2724493 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2724494 : term279 = term284.
Proof. exact (MK_COMB (@lem2724493) (@lem2724492)). Qed.
Lemma lem2724495 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2724496 : term308 = term574.
Proof. exact (MK_COMB (@lem2724495) (@lem2724494)). Qed.
Lemma lem2724497 : term157 = term157.
Proof. exact (eq_refl term157). Qed.
Lemma lem2724498 : term566 = term573.
Proof. exact (MK_COMB (@lem2724497) (@lem2724496)). Qed.
Lemma lem2724499 : term566 = term193.
Proof. exact (TRANS (@lem2724498) (@lem2724488)). Qed.
Lemma lem2724500 : term572 = term193.
Proof. exact (TRANS (@lem2724485) (@lem2724499)). Qed.
Lemma lem2724501 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2724502 : term575 = term195.
Proof. exact (MK_COMB (@lem2724501) (@lem2724500)). Qed.
Lemma lem2724503 : term110 = term110.
Proof. exact (eq_refl term110). Qed.
Lemma lem2724504 : term576 = term215.
Proof. exact (MK_COMB (@lem2724502) (@lem2724503)). Qed.
Lemma lem2724506 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2724507 : term215 = term220.
Proof. exact (@lem2724506 term111 term111). Qed.
Lemma lem2724508 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2724509 : term205 = term111.
Proof. exact (EQ_MP (@lem2724508) (@lem940073)). Qed.
Lemma lem2724510 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2724511 : term203 = term110.
Proof. exact (MK_COMB (@lem2724510) (@lem2724509)). Qed.
Lemma lem2724512 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2724513 : term220 = term193.
Proof. exact (MK_COMB (@lem2724512) (@lem2724511)). Qed.
Lemma lem2724514 : term215 = term193.
Proof. exact (TRANS (@lem2724507) (@lem2724513)). Qed.
Lemma lem2724515 : term576 = term193.
Proof. exact (TRANS (@lem2724504) (@lem2724514)). Qed.
Lemma lem2724517 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2724518 : term202 = term203.
Proof. exact (@lem2724517 term111 term111). Qed.
Lemma lem2724519 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2724520 : term205 = term111.
Proof. exact (EQ_MP (@lem2724519) (@lem940073)). Qed.
Lemma lem2724521 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2724522 : term203 = term110.
Proof. exact (MK_COMB (@lem2724521) (@lem2724520)). Qed.
Lemma lem2724523 : term202 = term110.
Proof. exact (TRANS (@lem2724518) (@lem2724522)). Qed.
Lemma lem2724524 : term195 = term195.
Proof. exact (eq_refl term195). Qed.
Lemma lem2724525 : term577 = term215.
Proof. exact (MK_COMB (@lem2724524) (@lem2724523)). Qed.
Lemma lem2724527 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2724528 : term215 = term220.
Proof. exact (@lem2724527 term111 term111). Qed.
Lemma lem2724529 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2724530 : term205 = term111.
Proof. exact (EQ_MP (@lem2724529) (@lem940073)). Qed.
Lemma lem2724531 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2724532 : term203 = term110.
Proof. exact (MK_COMB (@lem2724531) (@lem2724530)). Qed.
Lemma lem2724533 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2724534 : term220 = term193.
Proof. exact (MK_COMB (@lem2724533) (@lem2724532)). Qed.
Lemma lem2724535 : term215 = term193.
Proof. exact (TRANS (@lem2724528) (@lem2724534)). Qed.
Lemma lem2724536 : term577 = term193.
Proof. exact (TRANS (@lem2724525) (@lem2724535)). Qed.
Lemma lem2724537 : term193 = term577.
Proof. exact (SYM (@lem2724536)). Qed.
Lemma lem2724538 : term576 = term577.
Proof. exact (TRANS (@lem2724515) (@lem2724537)). Qed.
Lemma lem2724539 : term567 = term194.
Proof. exact (@lem2724463 (@lem2724538)). Qed.
Lemma lem2724540 : term566 = term194.
Proof. exact (TRANS (@lem2724429) (@lem2724539)). Qed.
Lemma lem2724542 (x : real) : (term209 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2724543 : term194 = term193.
Proof. exact (@lem2724542 term193). Qed.
Lemma lem2724544 : term566 = term193.
Proof. exact (TRANS (@lem2724540) (@lem2724543)). Qed.
Lemma lem2724545 (n : int) : (term565 n) = term477.
Proof. exact (MK_COMB (@lem2724420 n) (@lem2724544)). Qed.
Lemma lem2724546 (n : int) : (term564 n) = term477.
Proof. exact (TRANS (@lem2724312 n) (@lem2724545 n)). Qed.
Lemma lem2724547 : term477 = term193.
Proof. exact (@lem1982721 term193). Qed.
Lemma lem2724548 (n : int) : (term564 n) = term193.
Proof. exact (TRANS (@lem2724546 n) (@lem2724547)). Qed.
Lemma lem2724549 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2724550 (n : int) : (term578 n) = term479.
Proof. exact (MK_COMB (@lem2724549) (@lem2724548 n)). Qed.
Lemma lem2724551 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2724552 (n : int) : (term563 n) = term480.
Proof. exact (MK_COMB (@lem2724550 n) (@lem2724551)). Qed.
Lemma lem2724553 (n : int) (h1 : term621 n) : term480.
Proof. exact (EQ_MP (@lem2724552 n) (@lem2724311 n h1)). Qed.
Lemma lem2724555 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2724556 : term480 = term481.
Proof. exact (@lem2724555 term107 term193). Qed.
Lemma lem2724558 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2724559 : term193 = term194.
Proof. exact (@lem2724558 term111). Qed.
Lemma lem2724561 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2724562 : term107 = term190.
Proof. exact (@lem2724561 (NUMERAL 0)). Qed.
Lemma lem2724563 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2724564 : term482 = term483.
Proof. exact (MK_COMB (@lem2724563) (@lem2724562)). Qed.
Lemma lem2724565 : term481 = term484.
Proof. exact (MK_COMB (@lem2724564) (@lem2724559)). Qed.
Lemma lem2724566 : term485.
Proof. exact (@lem1980026 term107 term110 term193 term110). Qed.
Lemma lem2724568 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2724569 : term257 = term258.
Proof. exact (@lem2724568 (NUMERAL 0) term111). Qed.
Lemma lem2724570 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2724571 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2724572 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2724571 h1) (fun h1 : term258 = True => @lem2724570)). Qed.
Lemma lem2724573 : term258 = True.
Proof. exact (EQ_MP (@lem2724572) (@lem2724570)). Qed.
Lemma lem2724574 : term257 = True.
Proof. exact (TRANS (@lem2724569) (@lem2724573)). Qed.
Lemma lem2724575 : True = term257.
Proof. exact (SYM (@lem2724574)). Qed.
Lemma lem2724576 : term257.
Proof. exact (EQ_MP (@lem2724575) (@lem0)). Qed.
Lemma lem2724577 : term486.
Proof. exact (@lem2724566 (@lem2724576)). Qed.
Lemma lem2724579 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2724580 : term257 = term258.
Proof. exact (@lem2724579 (NUMERAL 0) term111). Qed.
Lemma lem2724581 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2724582 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2724583 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2724582 h1) (fun h1 : term258 = True => @lem2724581)). Qed.
Lemma lem2724584 : term258 = True.
Proof. exact (EQ_MP (@lem2724583) (@lem2724581)). Qed.
Lemma lem2724585 : term257 = True.
Proof. exact (TRANS (@lem2724580) (@lem2724584)). Qed.
Lemma lem2724586 : True = term257.
Proof. exact (SYM (@lem2724585)). Qed.
Lemma lem2724587 : term257.
Proof. exact (EQ_MP (@lem2724586) (@lem0)). Qed.
Lemma lem2724588 : term484 = term487.
Proof. exact (@lem2724577 (@lem2724587)). Qed.
Lemma lem2724590 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2724591 : term215 = term220.
Proof. exact (@lem2724590 term111 term111). Qed.
Lemma lem2724592 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2724593 : term205 = term111.
Proof. exact (EQ_MP (@lem2724592) (@lem940073)). Qed.
Lemma lem2724594 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2724595 : term203 = term110.
Proof. exact (MK_COMB (@lem2724594) (@lem2724593)). Qed.
Lemma lem2724596 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2724597 : term220 = term193.
Proof. exact (MK_COMB (@lem2724596) (@lem2724595)). Qed.
Lemma lem2724598 : term215 = term193.
Proof. exact (TRANS (@lem2724591) (@lem2724597)). Qed.
Lemma lem2724600 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2724601 : term269 = term107.
Proof. exact (@lem2724600 term111). Qed.
Lemma lem2724602 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2724603 : term488 = term482.
Proof. exact (MK_COMB (@lem2724602) (@lem2724601)). Qed.
Lemma lem2724604 : term487 = term481.
Proof. exact (MK_COMB (@lem2724603) (@lem2724598)). Qed.
Lemma lem2724606 (m : nat) (n : nat) : (term489 m n) = (term490 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2724607 : term481 = term491.
Proof. exact (@lem2724606 (NUMERAL 0) term111). Qed.
Lemma lem2724608 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2724609 (h1 : term259 = (BIT1 0)) : (term111 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2724610 : (term259 = (BIT1 0)) = ((term111 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2724609 h1) (fun h1 : (term111 = (NUMERAL 0)) = False => @lem2724608)). Qed.
Lemma lem2724611 : (term111 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2724610) (@lem2724608)). Qed.
Lemma lem2724612 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2724613 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2724614 : term492 = (and True).
Proof. exact (MK_COMB (@lem2724613) (@lem2724612)). Qed.
Lemma lem2724615 : term491 = (True /\ False).
Proof. exact (MK_COMB (@lem2724614) (@lem2724611)). Qed.
Lemma lem2724617 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2724618 : term491 = False.
Proof. exact (TRANS (@lem2724615) (@lem2724617)). Qed.
Lemma lem2724619 : term481 = False.
Proof. exact (TRANS (@lem2724607) (@lem2724618)). Qed.
Lemma lem2724620 : term487 = False.
Proof. exact (TRANS (@lem2724604) (@lem2724619)). Qed.
Lemma lem2724621 : term484 = False.
Proof. exact (TRANS (@lem2724588) (@lem2724620)). Qed.
Lemma lem2724622 : term481 = False.
Proof. exact (TRANS (@lem2724565) (@lem2724621)). Qed.
Lemma lem2724623 : term480 = False.
Proof. exact (TRANS (@lem2724556) (@lem2724622)). Qed.
Lemma lem2724624 (n : int) (h1 : term621 n) : False.
Proof. exact (EQ_MP (@lem2724623) (@lem2724553 n h1)). Qed.
Lemma lem2724625 (n : int) (h1 : term370 n) : False.
Proof. exact (or_elim (@lem2723887 n h1) (fun h0 : term620 n => @lem2724174 n h0) (fun h0 : term621 n => @lem2724624 n h0)). Qed.
Lemma lem2724626 (n : int) (h1 : term375 n) : False.
Proof. exact (or_elim (@lem2723310 n h1) (fun h0 : term372 n => @lem2723886 n h0) (fun h0 : term370 n => @lem2724625 n h0)). Qed.
Lemma lem2724627 (n : int) (h1 : term389 n) : False.
Proof. exact (or_elim (@lem2721911 n h1) (fun h0 : term386 n => @lem2723309 n h0) (fun h0 : term375 n => @lem2724626 n h0)). Qed.
Lemma lem2724628 (n : int) (h1 : term362 n) : term362 n.
Proof. exact (h1). Qed.
Lemma lem2724629 (n : int) (h1 : term622 n) : term622 n.
Proof. exact (h1). Qed.
Lemma lem2724630 (n : int) (h1 : term622 n) : term326 n.
Proof. exact (proj2 (@lem2724629 n h1)). Qed.
Lemma lem2724632 (n : int) (h1 : term622 n) : (term104 n) = term107.
Proof. exact (proj2 (@lem2724630 n h1)). Qed.
Lemma lem2724633 (n : int) (h1 : term622 n) : (term223 n) = term107.
Proof. exact (proj1 (@lem2724630 n h1)). Qed.
Lemma lem2724635 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2724636 : term433 = term257.
Proof. exact (@lem2724635 term107 term110). Qed.
Lemma lem2724638 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2724639 : term110 = term214.
Proof. exact (@lem2724638 term111). Qed.
Lemma lem2724641 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2724642 : term107 = term190.
Proof. exact (@lem2724641 (NUMERAL 0)). Qed.
Lemma lem2724643 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2724644 : term434 = term435.
Proof. exact (MK_COMB (@lem2724643) (@lem2724642)). Qed.
Lemma lem2724645 : term257 = term436.
Proof. exact (MK_COMB (@lem2724644) (@lem2724639)). Qed.
Lemma lem2724646 : term437.
Proof. exact (@lem1980255 term107 term110 term110 term110). Qed.
Lemma lem2724648 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2724649 : term257 = term258.
Proof. exact (@lem2724648 (NUMERAL 0) term111). Qed.
Lemma lem2724650 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2724651 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2724652 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2724651 h1) (fun h1 : term258 = True => @lem2724650)). Qed.
Lemma lem2724653 : term258 = True.
Proof. exact (EQ_MP (@lem2724652) (@lem2724650)). Qed.
Lemma lem2724654 : term257 = True.
Proof. exact (TRANS (@lem2724649) (@lem2724653)). Qed.
Lemma lem2724655 : True = term257.
Proof. exact (SYM (@lem2724654)). Qed.
Lemma lem2724656 : term257.
Proof. exact (EQ_MP (@lem2724655) (@lem0)). Qed.
Lemma lem2724657 : term438.
Proof. exact (@lem2724646 (@lem2724656)). Qed.
Lemma lem2724659 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2724660 : term257 = term258.
Proof. exact (@lem2724659 (NUMERAL 0) term111). Qed.
Lemma lem2724661 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2724662 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2724663 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2724662 h1) (fun h1 : term258 = True => @lem2724661)). Qed.
Lemma lem2724664 : term258 = True.
Proof. exact (EQ_MP (@lem2724663) (@lem2724661)). Qed.
Lemma lem2724665 : term257 = True.
Proof. exact (TRANS (@lem2724660) (@lem2724664)). Qed.
Lemma lem2724666 : True = term257.
Proof. exact (SYM (@lem2724665)). Qed.
Lemma lem2724667 : term257.
Proof. exact (EQ_MP (@lem2724666) (@lem0)). Qed.
Lemma lem2724668 : term436 = term439.
Proof. exact (@lem2724657 (@lem2724667)). Qed.
Lemma lem2724670 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2724671 : term202 = term203.
Proof. exact (@lem2724670 term111 term111). Qed.
Lemma lem2724672 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2724673 : term205 = term111.
Proof. exact (EQ_MP (@lem2724672) (@lem940073)). Qed.
Lemma lem2724674 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2724675 : term203 = term110.
Proof. exact (MK_COMB (@lem2724674) (@lem2724673)). Qed.
Lemma lem2724676 : term202 = term110.
Proof. exact (TRANS (@lem2724671) (@lem2724675)). Qed.
Lemma lem2724678 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2724679 : term269 = term107.
Proof. exact (@lem2724678 term111). Qed.
Lemma lem2724680 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2724681 : term440 = term434.
Proof. exact (MK_COMB (@lem2724680) (@lem2724679)). Qed.
Lemma lem2724682 : term439 = term257.
Proof. exact (MK_COMB (@lem2724681) (@lem2724676)). Qed.
Lemma lem2724684 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2724685 : term257 = term258.
Proof. exact (@lem2724684 (NUMERAL 0) term111). Qed.
Lemma lem2724686 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2724687 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2724688 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2724687 h1) (fun h1 : term258 = True => @lem2724686)). Qed.
Lemma lem2724689 : term258 = True.
Proof. exact (EQ_MP (@lem2724688) (@lem2724686)). Qed.
Lemma lem2724690 : term257 = True.
Proof. exact (TRANS (@lem2724685) (@lem2724689)). Qed.
Lemma lem2724691 : term439 = True.
Proof. exact (TRANS (@lem2724682) (@lem2724690)). Qed.
Lemma lem2724692 : term436 = True.
Proof. exact (TRANS (@lem2724668) (@lem2724691)). Qed.
Lemma lem2724693 : term257 = True.
Proof. exact (TRANS (@lem2724645) (@lem2724692)). Qed.
Lemma lem2724694 : term433 = True.
Proof. exact (TRANS (@lem2724636) (@lem2724693)). Qed.
Lemma lem2724695 : True = term433.
Proof. exact (SYM (@lem2724694)). Qed.
Lemma lem2724696 : term433.
Proof. exact (EQ_MP (@lem2724695) (@lem0)). Qed.
Lemma lem2724697 (n : int) (h1 : term622 n) : term623 n.
Proof. exact (conj (@lem2724696) (@lem2724633 n h1)). Qed.
Lemma lem2724699 (x : real) (y : real) : term583 x y.
Proof. exact (proj1 (@lem1988330 x y)). Qed.
Lemma lem2724700 (n : int) : term624 n.
Proof. exact (@lem2724699 term110 (term223 n)). Qed.
Lemma lem2724701 (n : int) (h1 : term622 n) : (term502 n) = term107.
Proof. exact (@lem2724700 n (@lem2724697 n h1)). Qed.
Lemma lem2724702 (n : int) : (term502 n) = (term223 n).
Proof. exact (@lem1982733 (term223 n)). Qed.
Lemma lem2724703 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2724704 (n : int) : (term503 n) = (term225 n).
Proof. exact (MK_COMB (@lem2724703) (@lem2724702 n)). Qed.
Lemma lem2724705 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2724706 (n : int) : ((term502 n) = term107) = ((term223 n) = term107).
Proof. exact (MK_COMB (@lem2724704 n) (@lem2724705)). Qed.
Lemma lem2724707 (n : int) (h1 : term622 n) : (term223 n) = term107.
Proof. exact (EQ_MP (@lem2724706 n) (@lem2724701 n h1)). Qed.
Lemma lem2724709 (y : real) : term447 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2724710 (n : int) : term448 n.
Proof. exact (@lem2724709 (term104 n)). Qed.
Lemma lem2724711 (n : int) (h1 : term622 n) : term449 n.
Proof. exact (@lem2724710 n (@lem2724632 n h1)). Qed.
Lemma lem2724712 (n : int) (h1 : term622 n) : term514 n.
Proof. exact (@lem2724711 n h1 term193). Qed.
Lemma lem2724713 (n : int) : (term514 n) = ((term251 n) = term107).
Proof. exact (eq_refl (term514 n)). Qed.
Lemma lem2724720 (n : int) (h1 : term622 n) : (term251 n) = term107.
Proof. exact (EQ_MP (@lem2724713 n) (@lem2724712 n h1)). Qed.
Lemma lem2724721 (n : int) (h1 : term622 n) : term625 n.
Proof. exact (conj (@lem2724720 n h1) (@lem2724707 n h1)). Qed.
Lemma lem2724723 (x : real) (y : real) : term586 x y.
Proof. exact (proj1 (@lem1393126 x y)). Qed.
Lemma lem2724724 (n : int) : term626 n.
Proof. exact (@lem2724723 (term251 n) (term223 n)). Qed.
Lemma lem2724725 (n : int) (h1 : term622 n) : (term518 n) = term107.
Proof. exact (@lem2724724 n (@lem2724721 n h1)). Qed.
Lemma lem2724726 (n : int) : (term518 n) = (term519 n).
Proof. exact (@lem1982763 (term251 n) (term104 n) term193). Qed.
Lemma lem2724727 (n : int) : (term520 n) = (term460 n).
Proof. exact (@lem1982713 term193 (term104 n)). Qed.
Lemma lem2724729 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2724730 : term110 = term214.
Proof. exact (@lem2724729 term111). Qed.
Lemma lem2724732 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2724733 : term193 = term194.
Proof. exact (@lem2724732 term111). Qed.
Lemma lem2724734 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2724735 : term461 = term462.
Proof. exact (MK_COMB (@lem2724734) (@lem2724733)). Qed.
Lemma lem2724736 : term463 = term464.
Proof. exact (MK_COMB (@lem2724735) (@lem2724730)). Qed.
Lemma lem2724737 : term465.
Proof. exact (@lem1981473 term193 term110 term110 term110 term107 term110). Qed.
Lemma lem2724739 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2724740 : term257 = term258.
Proof. exact (@lem2724739 (NUMERAL 0) term111). Qed.
Lemma lem2724741 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2724742 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2724743 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2724742 h1) (fun h1 : term258 = True => @lem2724741)). Qed.
Lemma lem2724744 : term258 = True.
Proof. exact (EQ_MP (@lem2724743) (@lem2724741)). Qed.
Lemma lem2724745 : term257 = True.
Proof. exact (TRANS (@lem2724740) (@lem2724744)). Qed.
Lemma lem2724746 : True = term257.
Proof. exact (SYM (@lem2724745)). Qed.
Lemma lem2724747 : term257.
Proof. exact (EQ_MP (@lem2724746) (@lem0)). Qed.
Lemma lem2724748 : term466.
Proof. exact (@lem2724737 (@lem2724747)). Qed.
Lemma lem2724750 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2724751 : term257 = term258.
Proof. exact (@lem2724750 (NUMERAL 0) term111). Qed.
Lemma lem2724752 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2724753 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2724754 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2724753 h1) (fun h1 : term258 = True => @lem2724752)). Qed.
Lemma lem2724755 : term258 = True.
Proof. exact (EQ_MP (@lem2724754) (@lem2724752)). Qed.
Lemma lem2724756 : term257 = True.
Proof. exact (TRANS (@lem2724751) (@lem2724755)). Qed.
Lemma lem2724757 : True = term257.
Proof. exact (SYM (@lem2724756)). Qed.
Lemma lem2724758 : term257.
Proof. exact (EQ_MP (@lem2724757) (@lem0)). Qed.
Lemma lem2724759 : term467.
Proof. exact (@lem2724748 (@lem2724758)). Qed.
Lemma lem2724761 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2724762 : term257 = term258.
Proof. exact (@lem2724761 (NUMERAL 0) term111). Qed.
Lemma lem2724763 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2724764 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2724765 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2724764 h1) (fun h1 : term258 = True => @lem2724763)). Qed.
Lemma lem2724766 : term258 = True.
Proof. exact (EQ_MP (@lem2724765) (@lem2724763)). Qed.
Lemma lem2724767 : term257 = True.
Proof. exact (TRANS (@lem2724762) (@lem2724766)). Qed.
Lemma lem2724768 : True = term257.
Proof. exact (SYM (@lem2724767)). Qed.
Lemma lem2724769 : term257.
Proof. exact (EQ_MP (@lem2724768) (@lem0)). Qed.
Lemma lem2724770 : term468.
Proof. exact (@lem2724759 (@lem2724769)). Qed.
Lemma lem2724772 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2724773 : term202 = term203.
Proof. exact (@lem2724772 term111 term111). Qed.
Lemma lem2724774 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2724775 : term205 = term111.
Proof. exact (EQ_MP (@lem2724774) (@lem940073)). Qed.
Lemma lem2724776 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2724777 : term203 = term110.
Proof. exact (MK_COMB (@lem2724776) (@lem2724775)). Qed.
Lemma lem2724778 : term202 = term110.
Proof. exact (TRANS (@lem2724773) (@lem2724777)). Qed.
Lemma lem2724780 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2724781 : term215 = term220.
Proof. exact (@lem2724780 term111 term111). Qed.
Lemma lem2724782 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2724783 : term205 = term111.
Proof. exact (EQ_MP (@lem2724782) (@lem940073)). Qed.
Lemma lem2724784 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2724785 : term203 = term110.
Proof. exact (MK_COMB (@lem2724784) (@lem2724783)). Qed.
Lemma lem2724786 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2724787 : term220 = term193.
Proof. exact (MK_COMB (@lem2724786) (@lem2724785)). Qed.
Lemma lem2724788 : term215 = term193.
Proof. exact (TRANS (@lem2724781) (@lem2724787)). Qed.
Lemma lem2724789 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2724790 : term469 = term461.
Proof. exact (MK_COMB (@lem2724789) (@lem2724788)). Qed.
Lemma lem2724791 : term470 = term463.
Proof. exact (MK_COMB (@lem2724790) (@lem2724778)). Qed.
Lemma lem2724793 (m : nat) : (term471 m) = term107.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2724794 : term463 = term107.
Proof. exact (@lem2724793 term111). Qed.
Lemma lem2724795 : term470 = term107.
Proof. exact (TRANS (@lem2724791) (@lem2724794)). Qed.
Lemma lem2724796 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2724797 : term472 = term267.
Proof. exact (MK_COMB (@lem2724796) (@lem2724795)). Qed.
Lemma lem2724798 : term110 = term110.
Proof. exact (eq_refl term110). Qed.
Lemma lem2724799 : term473 = term269.
Proof. exact (MK_COMB (@lem2724797) (@lem2724798)). Qed.
Lemma lem2724801 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2724802 : term269 = term107.
Proof. exact (@lem2724801 term111). Qed.
Lemma lem2724803 : term473 = term107.
Proof. exact (TRANS (@lem2724799) (@lem2724802)). Qed.
Lemma lem2724805 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2724806 : term202 = term203.
Proof. exact (@lem2724805 term111 term111). Qed.
Lemma lem2724807 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2724808 : term205 = term111.
Proof. exact (EQ_MP (@lem2724807) (@lem940073)). Qed.
Lemma lem2724809 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2724810 : term203 = term110.
Proof. exact (MK_COMB (@lem2724809) (@lem2724808)). Qed.
Lemma lem2724811 : term202 = term110.
Proof. exact (TRANS (@lem2724806) (@lem2724810)). Qed.
Lemma lem2724812 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2724813 : term271 = term269.
Proof. exact (MK_COMB (@lem2724812) (@lem2724811)). Qed.
Lemma lem2724815 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2724816 : term269 = term107.
Proof. exact (@lem2724815 term111). Qed.
Lemma lem2724817 : term271 = term107.
Proof. exact (TRANS (@lem2724813) (@lem2724816)). Qed.
Lemma lem2724818 : term107 = term271.
Proof. exact (SYM (@lem2724817)). Qed.
Lemma lem2724819 : term473 = term271.
Proof. exact (TRANS (@lem2724803) (@lem2724818)). Qed.
Lemma lem2724820 : term464 = term190.
Proof. exact (@lem2724770 (@lem2724819)). Qed.
Lemma lem2724821 : term463 = term190.
Proof. exact (TRANS (@lem2724736) (@lem2724820)). Qed.
Lemma lem2724823 (x : real) : (term209 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2724824 : term190 = term107.
Proof. exact (@lem2724823 term107). Qed.
Lemma lem2724825 : term463 = term107.
Proof. exact (TRANS (@lem2724821) (@lem2724824)). Qed.
Lemma lem2724826 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2724827 : term474 = term267.
Proof. exact (MK_COMB (@lem2724826) (@lem2724825)). Qed.
Lemma lem2724828 (n : int) : (term104 n) = (term104 n).
Proof. exact (eq_refl (term104 n)). Qed.
Lemma lem2724829 (n : int) : (term460 n) = (term475 n).
Proof. exact (MK_COMB (@lem2724827) (@lem2724828 n)). Qed.
Lemma lem2724830 (n : int) : (term520 n) = (term475 n).
Proof. exact (TRANS (@lem2724727 n) (@lem2724829 n)). Qed.
Lemma lem2724831 (n : int) : (term475 n) = term107.
Proof. exact (@lem1982719 (term104 n)). Qed.
Lemma lem2724832 (n : int) : (term520 n) = term107.
Proof. exact (TRANS (@lem2724830 n) (@lem2724831 n)). Qed.
Lemma lem2724833 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2724834 (n : int) : (term521 n) = term139.
Proof. exact (MK_COMB (@lem2724833) (@lem2724832 n)). Qed.
Lemma lem2724835 : term193 = term193.
Proof. exact (eq_refl term193). Qed.
Lemma lem2724836 (n : int) : (term519 n) = term477.
Proof. exact (MK_COMB (@lem2724834 n) (@lem2724835)). Qed.
Lemma lem2724837 (n : int) : (term518 n) = term477.
Proof. exact (TRANS (@lem2724726 n) (@lem2724836 n)). Qed.
Lemma lem2724838 : term477 = term193.
Proof. exact (@lem1982721 term193). Qed.
Lemma lem2724839 (n : int) : (term518 n) = term193.
Proof. exact (TRANS (@lem2724837 n) (@lem2724838)). Qed.
Lemma lem2724840 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2724841 (n : int) : (term627 n) = term628.
Proof. exact (MK_COMB (@lem2724840) (@lem2724839 n)). Qed.
Lemma lem2724842 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2724843 (n : int) : ((term518 n) = term107) = (term193 = term107).
Proof. exact (MK_COMB (@lem2724841 n) (@lem2724842)). Qed.
Lemma lem2724844 (n : int) (h1 : term622 n) : term193 = term107.
Proof. exact (EQ_MP (@lem2724843 n) (@lem2724725 n h1)). Qed.
Lemma lem2724846 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2724847 : term107 = term190.
Proof. exact (@lem2724846 (NUMERAL 0)). Qed.
Lemma lem2724849 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2724850 : term193 = term194.
Proof. exact (@lem2724849 term111). Qed.
Lemma lem2724851 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2724852 : term628 = term629.
Proof. exact (MK_COMB (@lem2724851) (@lem2724850)). Qed.
Lemma lem2724853 : (term193 = term107) = (term194 = term190).
Proof. exact (MK_COMB (@lem2724852) (@lem2724847)). Qed.
Lemma lem2724854 : term630.
Proof. exact (@lem1980277 term193 term110 term107 term110). Qed.
Lemma lem2724856 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2724857 : term257 = term258.
Proof. exact (@lem2724856 (NUMERAL 0) term111). Qed.
Lemma lem2724858 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2724859 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2724860 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2724859 h1) (fun h1 : term258 = True => @lem2724858)). Qed.
Lemma lem2724861 : term258 = True.
Proof. exact (EQ_MP (@lem2724860) (@lem2724858)). Qed.
Lemma lem2724862 : term257 = True.
Proof. exact (TRANS (@lem2724857) (@lem2724861)). Qed.
Lemma lem2724863 : True = term257.
Proof. exact (SYM (@lem2724862)). Qed.
Lemma lem2724864 : term257.
Proof. exact (EQ_MP (@lem2724863) (@lem0)). Qed.
Lemma lem2724865 : term631.
Proof. exact (@lem2724854 (@lem2724864)). Qed.
Lemma lem2724867 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2724868 : term257 = term258.
Proof. exact (@lem2724867 (NUMERAL 0) term111). Qed.
Lemma lem2724869 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2724870 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2724871 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2724870 h1) (fun h1 : term258 = True => @lem2724869)). Qed.
Lemma lem2724872 : term258 = True.
Proof. exact (EQ_MP (@lem2724871) (@lem2724869)). Qed.
Lemma lem2724873 : term257 = True.
Proof. exact (TRANS (@lem2724868) (@lem2724872)). Qed.
Lemma lem2724874 : True = term257.
Proof. exact (SYM (@lem2724873)). Qed.
Lemma lem2724875 : term257.
Proof. exact (EQ_MP (@lem2724874) (@lem0)). Qed.
Lemma lem2724876 : (term194 = term190) = (term215 = term269).
Proof. exact (@lem2724865 (@lem2724875)). Qed.
Lemma lem2724878 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2724879 : term269 = term107.
Proof. exact (@lem2724878 term111). Qed.
Lemma lem2724881 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2724882 : term215 = term220.
Proof. exact (@lem2724881 term111 term111). Qed.
Lemma lem2724883 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2724884 : term205 = term111.
Proof. exact (EQ_MP (@lem2724883) (@lem940073)). Qed.
Lemma lem2724885 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2724886 : term203 = term110.
Proof. exact (MK_COMB (@lem2724885) (@lem2724884)). Qed.
Lemma lem2724887 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2724888 : term220 = term193.
Proof. exact (MK_COMB (@lem2724887) (@lem2724886)). Qed.
Lemma lem2724889 : term215 = term193.
Proof. exact (TRANS (@lem2724882) (@lem2724888)). Qed.
Lemma lem2724890 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2724891 : term632 = term628.
Proof. exact (MK_COMB (@lem2724890) (@lem2724889)). Qed.
Lemma lem2724892 : (term215 = term269) = (term193 = term107).
Proof. exact (MK_COMB (@lem2724891) (@lem2724879)). Qed.
Lemma lem2724894 (m : nat) (n : nat) : ((term191 m) = (real_of_num n)) = (term490 m n).
Proof. exact (proj1 (@lem1366974 m n)). Qed.
Lemma lem2724895 : (term193 = term107) = term633.
Proof. exact (@lem2724894 term111 (NUMERAL 0)). Qed.
Lemma lem2724896 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2724897 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2724898 (h1 : term259 = (BIT1 0)) : (term111 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2724899 : (term259 = (BIT1 0)) = ((term111 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2724898 h1) (fun h1 : (term111 = (NUMERAL 0)) = False => @lem2724897)). Qed.
Lemma lem2724900 : (term111 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2724899) (@lem2724897)). Qed.
Lemma lem2724901 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2724902 : term634 = (and False).
Proof. exact (MK_COMB (@lem2724901) (@lem2724900)). Qed.
Lemma lem2724903 : term633 = (False /\ True).
Proof. exact (MK_COMB (@lem2724902) (@lem2724896)). Qed.
Lemma lem2724905 : (False /\ True) = False.
Proof. exact (proj1 (@lem1365105)). Qed.
Lemma lem2724906 : term633 = False.
Proof. exact (TRANS (@lem2724903) (@lem2724905)). Qed.
Lemma lem2724907 : (term193 = term107) = False.
Proof. exact (TRANS (@lem2724895) (@lem2724906)). Qed.
Lemma lem2724908 : (term215 = term269) = False.
Proof. exact (TRANS (@lem2724892) (@lem2724907)). Qed.
Lemma lem2724909 : (term194 = term190) = False.
Proof. exact (TRANS (@lem2724876) (@lem2724908)). Qed.
Lemma lem2724910 : (term193 = term107) = False.
Proof. exact (TRANS (@lem2724853) (@lem2724909)). Qed.
Lemma lem2724911 (n : int) (h1 : term622 n) : False.
Proof. exact (EQ_MP (@lem2724910) (@lem2724844 n h1)). Qed.
Lemma lem2724912 (n : int) (h1 : term635 n) : term635 n.
Proof. exact (h1). Qed.
Lemma lem2724913 (n : int) (h1 : term635 n) : term326 n.
Proof. exact (proj2 (@lem2724912 n h1)). Qed.
Lemma lem2724915 (n : int) (h1 : term635 n) : (term104 n) = term107.
Proof. exact (proj2 (@lem2724913 n h1)). Qed.
Lemma lem2724916 (n : int) (h1 : term635 n) : (term223 n) = term107.
Proof. exact (proj1 (@lem2724913 n h1)). Qed.
Lemma lem2724918 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2724919 : term433 = term257.
Proof. exact (@lem2724918 term107 term110). Qed.
Lemma lem2724921 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2724922 : term110 = term214.
Proof. exact (@lem2724921 term111). Qed.
Lemma lem2724924 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2724925 : term107 = term190.
Proof. exact (@lem2724924 (NUMERAL 0)). Qed.
Lemma lem2724926 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2724927 : term434 = term435.
Proof. exact (MK_COMB (@lem2724926) (@lem2724925)). Qed.
Lemma lem2724928 : term257 = term436.
Proof. exact (MK_COMB (@lem2724927) (@lem2724922)). Qed.
Lemma lem2724929 : term437.
Proof. exact (@lem1980255 term107 term110 term110 term110). Qed.
Lemma lem2724931 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2724932 : term257 = term258.
Proof. exact (@lem2724931 (NUMERAL 0) term111). Qed.
Lemma lem2724933 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2724934 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2724935 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2724934 h1) (fun h1 : term258 = True => @lem2724933)). Qed.
Lemma lem2724936 : term258 = True.
Proof. exact (EQ_MP (@lem2724935) (@lem2724933)). Qed.
Lemma lem2724937 : term257 = True.
Proof. exact (TRANS (@lem2724932) (@lem2724936)). Qed.
Lemma lem2724938 : True = term257.
Proof. exact (SYM (@lem2724937)). Qed.
Lemma lem2724939 : term257.
Proof. exact (EQ_MP (@lem2724938) (@lem0)). Qed.
Lemma lem2724940 : term438.
Proof. exact (@lem2724929 (@lem2724939)). Qed.
Lemma lem2724942 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2724943 : term257 = term258.
Proof. exact (@lem2724942 (NUMERAL 0) term111). Qed.
Lemma lem2724944 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2724945 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2724946 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2724945 h1) (fun h1 : term258 = True => @lem2724944)). Qed.
Lemma lem2724947 : term258 = True.
Proof. exact (EQ_MP (@lem2724946) (@lem2724944)). Qed.
Lemma lem2724948 : term257 = True.
Proof. exact (TRANS (@lem2724943) (@lem2724947)). Qed.
Lemma lem2724949 : True = term257.
Proof. exact (SYM (@lem2724948)). Qed.
Lemma lem2724950 : term257.
Proof. exact (EQ_MP (@lem2724949) (@lem0)). Qed.
Lemma lem2724951 : term436 = term439.
Proof. exact (@lem2724940 (@lem2724950)). Qed.
Lemma lem2724953 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2724954 : term202 = term203.
Proof. exact (@lem2724953 term111 term111). Qed.
Lemma lem2724955 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2724956 : term205 = term111.
Proof. exact (EQ_MP (@lem2724955) (@lem940073)). Qed.
Lemma lem2724957 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2724958 : term203 = term110.
Proof. exact (MK_COMB (@lem2724957) (@lem2724956)). Qed.
Lemma lem2724959 : term202 = term110.
Proof. exact (TRANS (@lem2724954) (@lem2724958)). Qed.
Lemma lem2724961 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2724962 : term269 = term107.
Proof. exact (@lem2724961 term111). Qed.
Lemma lem2724963 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2724964 : term440 = term434.
Proof. exact (MK_COMB (@lem2724963) (@lem2724962)). Qed.
Lemma lem2724965 : term439 = term257.
Proof. exact (MK_COMB (@lem2724964) (@lem2724959)). Qed.
Lemma lem2724967 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2724968 : term257 = term258.
Proof. exact (@lem2724967 (NUMERAL 0) term111). Qed.
Lemma lem2724969 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2724970 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2724971 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2724970 h1) (fun h1 : term258 = True => @lem2724969)). Qed.
Lemma lem2724972 : term258 = True.
Proof. exact (EQ_MP (@lem2724971) (@lem2724969)). Qed.
Lemma lem2724973 : term257 = True.
Proof. exact (TRANS (@lem2724968) (@lem2724972)). Qed.
Lemma lem2724974 : term439 = True.
Proof. exact (TRANS (@lem2724965) (@lem2724973)). Qed.
Lemma lem2724975 : term436 = True.
Proof. exact (TRANS (@lem2724951) (@lem2724974)). Qed.
Lemma lem2724976 : term257 = True.
Proof. exact (TRANS (@lem2724928) (@lem2724975)). Qed.
Lemma lem2724977 : term433 = True.
Proof. exact (TRANS (@lem2724919) (@lem2724976)). Qed.
Lemma lem2724978 : True = term433.
Proof. exact (SYM (@lem2724977)). Qed.
Lemma lem2724979 : term433.
Proof. exact (EQ_MP (@lem2724978) (@lem0)). Qed.
Lemma lem2724980 (n : int) (h1 : term635 n) : term623 n.
Proof. exact (conj (@lem2724979) (@lem2724916 n h1)). Qed.
Lemma lem2724982 (x : real) (y : real) : term583 x y.
Proof. exact (proj1 (@lem1988330 x y)). Qed.
Lemma lem2724983 (n : int) : term624 n.
Proof. exact (@lem2724982 term110 (term223 n)). Qed.
Lemma lem2724984 (n : int) (h1 : term635 n) : (term502 n) = term107.
Proof. exact (@lem2724983 n (@lem2724980 n h1)). Qed.
Lemma lem2724985 (n : int) : (term502 n) = (term223 n).
Proof. exact (@lem1982733 (term223 n)). Qed.
Lemma lem2724986 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2724987 (n : int) : (term503 n) = (term225 n).
Proof. exact (MK_COMB (@lem2724986) (@lem2724985 n)). Qed.
Lemma lem2724988 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2724989 (n : int) : ((term502 n) = term107) = ((term223 n) = term107).
Proof. exact (MK_COMB (@lem2724987 n) (@lem2724988)). Qed.
Lemma lem2724990 (n : int) (h1 : term635 n) : (term223 n) = term107.
Proof. exact (EQ_MP (@lem2724989 n) (@lem2724984 n h1)). Qed.
Lemma lem2724992 (y : real) : term447 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem2724993 (n : int) : term448 n.
Proof. exact (@lem2724992 (term104 n)). Qed.
Lemma lem2724994 (n : int) (h1 : term635 n) : term449 n.
Proof. exact (@lem2724993 n (@lem2724915 n h1)). Qed.
Lemma lem2724995 (n : int) (h1 : term635 n) : term514 n.
Proof. exact (@lem2724994 n h1 term193). Qed.
Lemma lem2724996 (n : int) : (term514 n) = ((term251 n) = term107).
Proof. exact (eq_refl (term514 n)). Qed.
Lemma lem2725003 (n : int) (h1 : term635 n) : (term251 n) = term107.
Proof. exact (EQ_MP (@lem2724996 n) (@lem2724995 n h1)). Qed.
Lemma lem2725004 (n : int) (h1 : term635 n) : term625 n.
Proof. exact (conj (@lem2725003 n h1) (@lem2724990 n h1)). Qed.
Lemma lem2725006 (x : real) (y : real) : term586 x y.
Proof. exact (proj1 (@lem1393126 x y)). Qed.
Lemma lem2725007 (n : int) : term626 n.
Proof. exact (@lem2725006 (term251 n) (term223 n)). Qed.
Lemma lem2725008 (n : int) (h1 : term635 n) : (term518 n) = term107.
Proof. exact (@lem2725007 n (@lem2725004 n h1)). Qed.
Lemma lem2725009 (n : int) : (term518 n) = (term519 n).
Proof. exact (@lem1982763 (term251 n) (term104 n) term193). Qed.
Lemma lem2725010 (n : int) : (term520 n) = (term460 n).
Proof. exact (@lem1982713 term193 (term104 n)). Qed.
Lemma lem2725012 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2725013 : term110 = term214.
Proof. exact (@lem2725012 term111). Qed.
Lemma lem2725015 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2725016 : term193 = term194.
Proof. exact (@lem2725015 term111). Qed.
Lemma lem2725017 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2725018 : term461 = term462.
Proof. exact (MK_COMB (@lem2725017) (@lem2725016)). Qed.
Lemma lem2725019 : term463 = term464.
Proof. exact (MK_COMB (@lem2725018) (@lem2725013)). Qed.
Lemma lem2725020 : term465.
Proof. exact (@lem1981473 term193 term110 term110 term110 term107 term110). Qed.
Lemma lem2725022 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2725023 : term257 = term258.
Proof. exact (@lem2725022 (NUMERAL 0) term111). Qed.
Lemma lem2725024 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2725025 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2725026 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2725025 h1) (fun h1 : term258 = True => @lem2725024)). Qed.
Lemma lem2725027 : term258 = True.
Proof. exact (EQ_MP (@lem2725026) (@lem2725024)). Qed.
Lemma lem2725028 : term257 = True.
Proof. exact (TRANS (@lem2725023) (@lem2725027)). Qed.
Lemma lem2725029 : True = term257.
Proof. exact (SYM (@lem2725028)). Qed.
Lemma lem2725030 : term257.
Proof. exact (EQ_MP (@lem2725029) (@lem0)). Qed.
Lemma lem2725031 : term466.
Proof. exact (@lem2725020 (@lem2725030)). Qed.
Lemma lem2725033 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2725034 : term257 = term258.
Proof. exact (@lem2725033 (NUMERAL 0) term111). Qed.
Lemma lem2725035 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2725036 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2725037 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2725036 h1) (fun h1 : term258 = True => @lem2725035)). Qed.
Lemma lem2725038 : term258 = True.
Proof. exact (EQ_MP (@lem2725037) (@lem2725035)). Qed.
Lemma lem2725039 : term257 = True.
Proof. exact (TRANS (@lem2725034) (@lem2725038)). Qed.
Lemma lem2725040 : True = term257.
Proof. exact (SYM (@lem2725039)). Qed.
Lemma lem2725041 : term257.
Proof. exact (EQ_MP (@lem2725040) (@lem0)). Qed.
Lemma lem2725042 : term467.
Proof. exact (@lem2725031 (@lem2725041)). Qed.
Lemma lem2725044 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2725045 : term257 = term258.
Proof. exact (@lem2725044 (NUMERAL 0) term111). Qed.
Lemma lem2725046 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2725047 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2725048 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2725047 h1) (fun h1 : term258 = True => @lem2725046)). Qed.
Lemma lem2725049 : term258 = True.
Proof. exact (EQ_MP (@lem2725048) (@lem2725046)). Qed.
Lemma lem2725050 : term257 = True.
Proof. exact (TRANS (@lem2725045) (@lem2725049)). Qed.
Lemma lem2725051 : True = term257.
Proof. exact (SYM (@lem2725050)). Qed.
Lemma lem2725052 : term257.
Proof. exact (EQ_MP (@lem2725051) (@lem0)). Qed.
Lemma lem2725053 : term468.
Proof. exact (@lem2725042 (@lem2725052)). Qed.
Lemma lem2725055 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2725056 : term202 = term203.
Proof. exact (@lem2725055 term111 term111). Qed.
Lemma lem2725057 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2725058 : term205 = term111.
Proof. exact (EQ_MP (@lem2725057) (@lem940073)). Qed.
Lemma lem2725059 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2725060 : term203 = term110.
Proof. exact (MK_COMB (@lem2725059) (@lem2725058)). Qed.
Lemma lem2725061 : term202 = term110.
Proof. exact (TRANS (@lem2725056) (@lem2725060)). Qed.
Lemma lem2725063 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2725064 : term215 = term220.
Proof. exact (@lem2725063 term111 term111). Qed.
Lemma lem2725065 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2725066 : term205 = term111.
Proof. exact (EQ_MP (@lem2725065) (@lem940073)). Qed.
Lemma lem2725067 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2725068 : term203 = term110.
Proof. exact (MK_COMB (@lem2725067) (@lem2725066)). Qed.
Lemma lem2725069 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2725070 : term220 = term193.
Proof. exact (MK_COMB (@lem2725069) (@lem2725068)). Qed.
Lemma lem2725071 : term215 = term193.
Proof. exact (TRANS (@lem2725064) (@lem2725070)). Qed.
Lemma lem2725072 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2725073 : term469 = term461.
Proof. exact (MK_COMB (@lem2725072) (@lem2725071)). Qed.
Lemma lem2725074 : term470 = term463.
Proof. exact (MK_COMB (@lem2725073) (@lem2725061)). Qed.
Lemma lem2725076 (m : nat) : (term471 m) = term107.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2725077 : term463 = term107.
Proof. exact (@lem2725076 term111). Qed.
Lemma lem2725078 : term470 = term107.
Proof. exact (TRANS (@lem2725074) (@lem2725077)). Qed.
Lemma lem2725079 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2725080 : term472 = term267.
Proof. exact (MK_COMB (@lem2725079) (@lem2725078)). Qed.
Lemma lem2725081 : term110 = term110.
Proof. exact (eq_refl term110). Qed.
Lemma lem2725082 : term473 = term269.
Proof. exact (MK_COMB (@lem2725080) (@lem2725081)). Qed.
Lemma lem2725084 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2725085 : term269 = term107.
Proof. exact (@lem2725084 term111). Qed.
Lemma lem2725086 : term473 = term107.
Proof. exact (TRANS (@lem2725082) (@lem2725085)). Qed.
Lemma lem2725088 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2725089 : term202 = term203.
Proof. exact (@lem2725088 term111 term111). Qed.
Lemma lem2725090 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2725091 : term205 = term111.
Proof. exact (EQ_MP (@lem2725090) (@lem940073)). Qed.
Lemma lem2725092 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2725093 : term203 = term110.
Proof. exact (MK_COMB (@lem2725092) (@lem2725091)). Qed.
Lemma lem2725094 : term202 = term110.
Proof. exact (TRANS (@lem2725089) (@lem2725093)). Qed.
Lemma lem2725095 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2725096 : term271 = term269.
Proof. exact (MK_COMB (@lem2725095) (@lem2725094)). Qed.
Lemma lem2725098 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2725099 : term269 = term107.
Proof. exact (@lem2725098 term111). Qed.
Lemma lem2725100 : term271 = term107.
Proof. exact (TRANS (@lem2725096) (@lem2725099)). Qed.
Lemma lem2725101 : term107 = term271.
Proof. exact (SYM (@lem2725100)). Qed.
Lemma lem2725102 : term473 = term271.
Proof. exact (TRANS (@lem2725086) (@lem2725101)). Qed.
Lemma lem2725103 : term464 = term190.
Proof. exact (@lem2725053 (@lem2725102)). Qed.
Lemma lem2725104 : term463 = term190.
Proof. exact (TRANS (@lem2725019) (@lem2725103)). Qed.
Lemma lem2725106 (x : real) : (term209 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2725107 : term190 = term107.
Proof. exact (@lem2725106 term107). Qed.
Lemma lem2725108 : term463 = term107.
Proof. exact (TRANS (@lem2725104) (@lem2725107)). Qed.
Lemma lem2725109 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2725110 : term474 = term267.
Proof. exact (MK_COMB (@lem2725109) (@lem2725108)). Qed.
Lemma lem2725111 (n : int) : (term104 n) = (term104 n).
Proof. exact (eq_refl (term104 n)). Qed.
Lemma lem2725112 (n : int) : (term460 n) = (term475 n).
Proof. exact (MK_COMB (@lem2725110) (@lem2725111 n)). Qed.
Lemma lem2725113 (n : int) : (term520 n) = (term475 n).
Proof. exact (TRANS (@lem2725010 n) (@lem2725112 n)). Qed.
Lemma lem2725114 (n : int) : (term475 n) = term107.
Proof. exact (@lem1982719 (term104 n)). Qed.
Lemma lem2725115 (n : int) : (term520 n) = term107.
Proof. exact (TRANS (@lem2725113 n) (@lem2725114 n)). Qed.
Lemma lem2725116 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2725117 (n : int) : (term521 n) = term139.
Proof. exact (MK_COMB (@lem2725116) (@lem2725115 n)). Qed.
Lemma lem2725118 : term193 = term193.
Proof. exact (eq_refl term193). Qed.
Lemma lem2725119 (n : int) : (term519 n) = term477.
Proof. exact (MK_COMB (@lem2725117 n) (@lem2725118)). Qed.
Lemma lem2725120 (n : int) : (term518 n) = term477.
Proof. exact (TRANS (@lem2725009 n) (@lem2725119 n)). Qed.
Lemma lem2725121 : term477 = term193.
Proof. exact (@lem1982721 term193). Qed.
Lemma lem2725122 (n : int) : (term518 n) = term193.
Proof. exact (TRANS (@lem2725120 n) (@lem2725121)). Qed.
Lemma lem2725123 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2725124 (n : int) : (term627 n) = term628.
Proof. exact (MK_COMB (@lem2725123) (@lem2725122 n)). Qed.
Lemma lem2725125 : term107 = term107.
Proof. exact (eq_refl term107). Qed.
Lemma lem2725126 (n : int) : ((term518 n) = term107) = (term193 = term107).
Proof. exact (MK_COMB (@lem2725124 n) (@lem2725125)). Qed.
Lemma lem2725127 (n : int) (h1 : term635 n) : term193 = term107.
Proof. exact (EQ_MP (@lem2725126 n) (@lem2725008 n h1)). Qed.
Lemma lem2725129 (x : nat) : (real_of_num x) = (term189 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2725130 : term107 = term190.
Proof. exact (@lem2725129 (NUMERAL 0)). Qed.
Lemma lem2725132 (x : nat) : (term191 x) = (term192 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2725133 : term193 = term194.
Proof. exact (@lem2725132 term111). Qed.
Lemma lem2725134 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2725135 : term628 = term629.
Proof. exact (MK_COMB (@lem2725134) (@lem2725133)). Qed.
Lemma lem2725136 : (term193 = term107) = (term194 = term190).
Proof. exact (MK_COMB (@lem2725135) (@lem2725130)). Qed.
Lemma lem2725137 : term630.
Proof. exact (@lem1980277 term193 term110 term107 term110). Qed.
Lemma lem2725139 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2725140 : term257 = term258.
Proof. exact (@lem2725139 (NUMERAL 0) term111). Qed.
Lemma lem2725141 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2725142 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2725143 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2725142 h1) (fun h1 : term258 = True => @lem2725141)). Qed.
Lemma lem2725144 : term258 = True.
Proof. exact (EQ_MP (@lem2725143) (@lem2725141)). Qed.
Lemma lem2725145 : term257 = True.
Proof. exact (TRANS (@lem2725140) (@lem2725144)). Qed.
Lemma lem2725146 : True = term257.
Proof. exact (SYM (@lem2725145)). Qed.
Lemma lem2725147 : term257.
Proof. exact (EQ_MP (@lem2725146) (@lem0)). Qed.
Lemma lem2725148 : term631.
Proof. exact (@lem2725137 (@lem2725147)). Qed.
Lemma lem2725150 (m : nat) (n : nat) : (term256 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2725151 : term257 = term258.
Proof. exact (@lem2725150 (NUMERAL 0) term111). Qed.
Lemma lem2725152 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2725153 (h1 : term259 = (BIT1 0)) : term258 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2725154 : (term259 = (BIT1 0)) = (term258 = True).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2725153 h1) (fun h1 : term258 = True => @lem2725152)). Qed.
Lemma lem2725155 : term258 = True.
Proof. exact (EQ_MP (@lem2725154) (@lem2725152)). Qed.
Lemma lem2725156 : term257 = True.
Proof. exact (TRANS (@lem2725151) (@lem2725155)). Qed.
Lemma lem2725157 : True = term257.
Proof. exact (SYM (@lem2725156)). Qed.
Lemma lem2725158 : term257.
Proof. exact (EQ_MP (@lem2725157) (@lem0)). Qed.
Lemma lem2725159 : (term194 = term190) = (term215 = term269).
Proof. exact (@lem2725148 (@lem2725158)). Qed.
Lemma lem2725161 (x : nat) : (term270 x) = term107.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2725162 : term269 = term107.
Proof. exact (@lem2725161 term111). Qed.
Lemma lem2725164 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2725165 : term215 = term220.
Proof. exact (@lem2725164 term111 term111). Qed.
Lemma lem2725166 : (term204 = (BIT1 0)) = (term205 = term111).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2725167 : term205 = term111.
Proof. exact (EQ_MP (@lem2725166) (@lem940073)). Qed.
Lemma lem2725168 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2725169 : term203 = term110.
Proof. exact (MK_COMB (@lem2725168) (@lem2725167)). Qed.
Lemma lem2725170 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2725171 : term220 = term193.
Proof. exact (MK_COMB (@lem2725170) (@lem2725169)). Qed.
Lemma lem2725172 : term215 = term193.
Proof. exact (TRANS (@lem2725165) (@lem2725171)). Qed.
Lemma lem2725173 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2725174 : term632 = term628.
Proof. exact (MK_COMB (@lem2725173) (@lem2725172)). Qed.
Lemma lem2725175 : (term215 = term269) = (term193 = term107).
Proof. exact (MK_COMB (@lem2725174) (@lem2725162)). Qed.
Lemma lem2725177 (m : nat) (n : nat) : ((term191 m) = (real_of_num n)) = (term490 m n).
Proof. exact (proj1 (@lem1366974 m n)). Qed.
Lemma lem2725178 : (term193 = term107) = term633.
Proof. exact (@lem2725177 term111 (NUMERAL 0)). Qed.
Lemma lem2725179 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2725180 : term259 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2725181 (h1 : term259 = (BIT1 0)) : (term111 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2725182 : (term259 = (BIT1 0)) = ((term111 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term259 = (BIT1 0) => @lem2725181 h1) (fun h1 : (term111 = (NUMERAL 0)) = False => @lem2725180)). Qed.
Lemma lem2725183 : (term111 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2725182) (@lem2725180)). Qed.
Lemma lem2725184 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2725185 : term634 = (and False).
Proof. exact (MK_COMB (@lem2725184) (@lem2725183)). Qed.
Lemma lem2725186 : term633 = (False /\ True).
Proof. exact (MK_COMB (@lem2725185) (@lem2725179)). Qed.
Lemma lem2725188 : (False /\ True) = False.
Proof. exact (proj1 (@lem1365105)). Qed.
Lemma lem2725189 : term633 = False.
Proof. exact (TRANS (@lem2725186) (@lem2725188)). Qed.
Lemma lem2725190 : (term193 = term107) = False.
Proof. exact (TRANS (@lem2725178) (@lem2725189)). Qed.
Lemma lem2725191 : (term215 = term269) = False.
Proof. exact (TRANS (@lem2725175) (@lem2725190)). Qed.
Lemma lem2725192 : (term194 = term190) = False.
Proof. exact (TRANS (@lem2725159) (@lem2725191)). Qed.
Lemma lem2725193 : (term193 = term107) = False.
Proof. exact (TRANS (@lem2725136) (@lem2725192)). Qed.
Lemma lem2725194 (n : int) (h1 : term635 n) : False.
Proof. exact (EQ_MP (@lem2725193) (@lem2725127 n h1)). Qed.
Lemma lem2725195 (n : int) (h1 : term362 n) : False.
Proof. exact (or_elim (@lem2724628 n h1) (fun h0 : term622 n => @lem2724911 n h0) (fun h0 : term635 n => @lem2725194 n h0)). Qed.
Lemma lem2725196 (n : int) (h1 : term392 n) : False.
Proof. exact (or_elim (@lem2721910 n h1) (fun h0 : term389 n => @lem2724627 n h0) (fun h0 : term362 n => @lem2725195 n h0)). Qed.
Lemma lem2725197 (n : int) (h1 : term429 n) : False.
Proof. exact (or_elim (@lem2718639 n h1) (fun h0 : term426 n => @lem2721909 n h0) (fun h0 : term392 n => @lem2725196 n h0)). Qed.
Lemma lem2725199 (n : int) (h1 : term429 n) : term429 n.
Proof. exact (h1). Qed.
Lemma lem2725200 (n : int) (h1 : term429 n) : (term429 n) = False.
Proof. exact (prop_ext (fun h2 : term429 n => @lem2725197 n h1) (fun h2 : False => @lem2725199 n h1)). Qed.
Lemma lem2725201 (n : int) (h1 : term429 n) : False.
Proof. exact (EQ_MP (@lem2725200 n h1) (@lem2725199 n h1)). Qed.
Lemma lem2725202 (h1 : term431) : term431.
Proof. exact (h1). Qed.
Lemma lem2725203 (h1 : term431) : False.
Proof. exact (ex_elim (@lem2725202 h1) (fun n : int => fun h0 : term430 n => @lem2725201 n h0)). Qed.
Lemma lem2725204 (h1 : term186) : term186.
Proof. exact (h1). Qed.
Lemma lem2725205 (h1 : term186) : term431.
Proof. exact (EQ_MP (@lem2718521) (@lem2725204 h1)). Qed.
Lemma lem2725206 (h1 : term186) : term431 = False.
Proof. exact (prop_ext (fun h2 : term431 => @lem2725203 h2) (fun h2 : False => @lem2725205 h1)). Qed.
Lemma lem2725207 (h1 : term186) : False.
Proof. exact (EQ_MP (@lem2725206 h1) (@lem2725205 h1)). Qed.
Lemma lem2725208 : term636.
Proof. exact (fun h0 : term186 => @lem2725207 h0). Qed.
Lemma lem2725209 : term637.
Proof. exact (@lem1386578 term638). Qed.
Lemma lem2725212 : term638.
Proof. exact (@lem2725209 (@lem2725208)). Qed.
Lemma lem2725213 : term184 = term97.
Proof. exact (SYM (@lem2716762)). Qed.
Lemma lem2725214 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2725215 : term638 = term67.
Proof. exact (MK_COMB (@lem2725214) (@lem2725213)). Qed.
Lemma lem2725216 : term67.
Proof. exact (EQ_MP (@lem2725215) (@lem2725212)). Qed.
Lemma lem2725217 : term54.
Proof. exact (EQ_MP (@lem2716341) (@lem2725216)). Qed.
Lemma lem2725218 : term54 = (term54 = True).
Proof. exact (@lem7 term54). Qed.
Lemma lem2725219 : term54 = True.
Proof. exact (EQ_MP (@lem2725218) (@lem2725217)). Qed.
Lemma lem2725220 : True = term54.
Proof. exact (SYM (@lem2725219)). Qed.
Lemma lem2725221 : term54.
Proof. exact (EQ_MP (@lem2725220) (@lem0)). Qed.
Lemma lem2725222 : term65.
Proof. exact (@lem2716340 (@lem2725221)). Qed.
Lemma lem2725223 : term40.
Proof. exact (@lem2725222 (@lem2716252)). Qed.
Lemma lem2725224 : term31.
Proof. exact (EQ_MP (@lem2716313) (@lem2725223)). Qed.
