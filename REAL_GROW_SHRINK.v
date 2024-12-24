Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_GROW_SHRINK_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import REAL_SHRINK_GALOIS_spec.
Require Import REAL_SHRINK_RANGE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm69_spec.
Lemma lem2256145 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem2256146 : term1 = term2.
Proof. exact (@lem2256145 term1). Qed.
Lemma lem2256147 : term2 = term1.
Proof. exact (SYM (@lem2256146)). Qed.
Lemma lem2256148 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem2256151 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem2256152 : term5.
Proof. exact (fun h0 : term4 => @lem2256151 h0). Qed.
Lemma lem2256153 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem2256154 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem2256155 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem2256153 h2 (@lem2256154 h1)). Qed.
Lemma lem2256156 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem2256155 h1 h0). Qed.
Lemma lem2256157 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem2256158 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem2256156 h1 (@lem2256157 h2)). Qed.
Lemma lem2256159 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem2256158 h0 h1). Qed.
Lemma lem2256160 : term7.
Proof. exact (fun h0 : term5 => @lem2256159 h0). Qed.
Lemma lem2256163 : term5.
Proof. exact (@lem2256160 (@lem2256152)). Qed.
Lemma lem2256177 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem2256178 : term8 = term9.
Proof. exact (@lem2256177 term10). Qed.
Lemma lem2256189 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem2256190 : term12 = term13.
Proof. exact (MK_COMB (@lem2256189) (@lem2256178)). Qed.
Lemma lem2256193 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2256200 : term4 = term15.
Proof. exact (MK_COMB (@lem2256193) (@lem2256190)). Qed.
Lemma lem2256209 (y : real) (x : real) : (((term16 x) = y) = (term17 y x)) = (((term16 x) = y) = (term17 y x)).
Proof. exact (eq_refl (((term16 x) = y) = (term17 y x))). Qed.
Lemma lem2256210 (x : real) : (term18 x) = (term18 x).
Proof. exact (fun_ext (fun y : real => @lem2256209 y x)). Qed.
Lemma lem2256211 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2256212 (x : real) : (term19 x) = (term19 x).
Proof. exact (MK_COMB (@lem2256211) (@lem2256210 x)). Qed.
Lemma lem2256213 : term20 = term20.
Proof. exact (fun_ext (fun x : real => @lem2256212 x)). Qed.
Lemma lem2256214 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2256215 : term10 = term10.
Proof. exact (MK_COMB (@lem2256214) (@lem2256213)). Qed.
Lemma lem2256216 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2256217 : term9 = term9.
Proof. exact (MK_COMB (@lem2256216) (@lem2256215)). Qed.
Lemma lem2256218 (x : real) : (term21 x) = (term21 x).
Proof. exact (eq_refl (term21 x)). Qed.
Lemma lem2256219 : term22 = term22.
Proof. exact (fun_ext (fun x : real => @lem2256218 x)). Qed.
Lemma lem2256220 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2256221 : term23 = term23.
Proof. exact (MK_COMB (@lem2256220) (@lem2256219)). Qed.
Lemma lem2256222 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2256223 : term11 = term11.
Proof. exact (MK_COMB (@lem2256222) (@lem2256221)). Qed.
Lemma lem2256224 : term13 = term13.
Proof. exact (MK_COMB (@lem2256223) (@lem2256217)). Qed.
Lemma lem2256225 (x : real) : ((term24 x) = x) = ((term24 x) = x).
Proof. exact (eq_refl ((term24 x) = x)). Qed.
Lemma lem2256226 : term25 = term25.
Proof. exact (fun_ext (fun x : real => @lem2256225 x)). Qed.
Lemma lem2256227 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2256228 : term1 = term1.
Proof. exact (MK_COMB (@lem2256227) (@lem2256226)). Qed.
Lemma lem2256229 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2256230 : term3 = term3.
Proof. exact (MK_COMB (@lem2256229) (@lem2256228)). Qed.
Lemma lem2256231 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2256232 : term14 = term14.
Proof. exact (MK_COMB (@lem2256231) (@lem2256230)). Qed.
Lemma lem2256233 : term15 = term15.
Proof. exact (MK_COMB (@lem2256232) (@lem2256224)). Qed.
Lemma lem2256266 : term4 = term15.
Proof. exact (TRANS (@lem2256200) (@lem2256233)). Qed.
Lemma lem2256267 : term15 = term4.
Proof. exact (SYM (@lem2256266)). Qed.
Lemma lem2256268 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem2256270 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem2256272 (P : real -> Prop) : (term26 P) = (term27 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem2256273 : term3 = term28.
Proof. exact (@lem2256272 term25). Qed.
Lemma lem2256274 (x : real) : (term29 x) = ((term24 x) = x).
Proof. exact (eq_refl (term29 x)). Qed.
Lemma lem2256275 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2256277 (x : real) : (term30 x) = (term31 x).
Proof. exact (MK_COMB (@lem2256275) (@lem2256274 x)). Qed.
Lemma lem2256278 : term32 = term33.
Proof. exact (fun_ext (fun x : real => @lem2256277 x)). Qed.
Lemma lem2256279 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem2256280 : term28 = term34.
Proof. exact (MK_COMB (@lem2256279) (@lem2256278)). Qed.
Lemma lem2256289 : term3 = term34.
Proof. exact (TRANS (@lem2256273) (@lem2256280)). Qed.
Lemma lem2256290 (h1 : term3) : term34.
Proof. exact (EQ_MP (@lem2256289) (@lem2256268 h1)). Qed.
Lemma lem2256314 (y : real) (x : real) : (term35 y x) = (term36 y x).
Proof. exact (@lem17045 (term37 y) ((term38 y) = x)). Qed.
Lemma lem2256320 (y : real) (x : real) : (term39 y x) = (term39 y x).
Proof. exact (eq_refl (term39 y x)). Qed.
Lemma lem2256322 (x : real) (y : real) : (term40 x y) = (term40 x y).
Proof. exact (eq_refl (term40 x y)). Qed.
Lemma lem2256323 (y : real) (x : real) : (term41 y x) = (term42 y x).
Proof. exact (MK_COMB (@lem2256322 x y) (@lem2256314 y x)). Qed.
Lemma lem2256324 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2256325 (y : real) (x : real) : (term43 y x) = (term44 y x).
Proof. exact (MK_COMB (@lem2256324) (@lem2256323 y x)). Qed.
Lemma lem2256326 (y : real) (x : real) : (term45 y x) = (term46 y x).
Proof. exact (MK_COMB (@lem2256325 y x) (@lem2256320 y x)). Qed.
Lemma lem2256327 (y : real) (x : real) : (((term16 x) = y) = (term17 y x)) = (term45 y x).
Proof. exact (@lem17784 ((term16 x) = y) (term17 y x)). Qed.
Lemma lem2256328 (y : real) (x : real) : (((term16 x) = y) = (term17 y x)) = (term46 y x).
Proof. exact (TRANS (@lem2256327 y x) (@lem2256326 y x)). Qed.
Lemma lem2256329 (x : real) : (term18 x) = (term47 x).
Proof. exact (fun_ext (fun y : real => @lem2256328 y x)). Qed.
Lemma lem2256330 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2256331 (x : real) : (term19 x) = (term48 x).
Proof. exact (MK_COMB (@lem2256330) (@lem2256329 x)). Qed.
Lemma lem2256332 : term20 = term49.
Proof. exact (fun_ext (fun x : real => @lem2256331 x)). Qed.
Lemma lem2256333 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2256334 : term10 = term50.
Proof. exact (MK_COMB (@lem2256333) (@lem2256332)). Qed.
Lemma lem2256340 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term51 A P Q) = (term52 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem2256341 (P : real -> Prop) (Q : real -> Prop) : (term53 P Q) = (term54 P Q).
Proof. exact (@lem2256340 real P Q). Qed.
Lemma lem2256342 (x : real) : (term55 x) = (term56 x).
Proof. exact (@lem2256341 (term57 x) (term58 x)). Qed.
Lemma lem2256343 (y : real) (x : real) : (term59 x y) = (term42 y x).
Proof. exact (eq_refl (term59 x y)). Qed.
Lemma lem2256344 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2256345 (y : real) (x : real) : (term60 x y) = (term44 y x).
Proof. exact (MK_COMB (@lem2256344) (@lem2256343 y x)). Qed.
Lemma lem2256346 (y : real) (x : real) : (term61 x y) = (term39 y x).
Proof. exact (eq_refl (term61 x y)). Qed.
Lemma lem2256347 (y : real) (x : real) : (term62 x y) = (term46 y x).
Proof. exact (MK_COMB (@lem2256345 y x) (@lem2256346 y x)). Qed.
Lemma lem2256348 (x : real) : (term63 x) = (term47 x).
Proof. exact (fun_ext (fun y : real => @lem2256347 y x)). Qed.
Lemma lem2256349 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2256350 (x : real) : (term55 x) = (term48 x).
Proof. exact (MK_COMB (@lem2256349) (@lem2256348 x)). Qed.
Lemma lem2256351 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2256352 (x : real) : (term64 x) = (term65 x).
Proof. exact (MK_COMB (@lem2256351) (@lem2256350 x)). Qed.
Lemma lem2256353 (y : real) (x : real) : (term59 x y) = (term42 y x).
Proof. exact (eq_refl (term59 x y)). Qed.
Lemma lem2256354 (x : real) : (term66 x) = (term57 x).
Proof. exact (fun_ext (fun y : real => @lem2256353 y x)). Qed.
Lemma lem2256355 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2256356 (x : real) : (term67 x) = (term68 x).
Proof. exact (MK_COMB (@lem2256355) (@lem2256354 x)). Qed.
Lemma lem2256357 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2256358 (x : real) : (term69 x) = (term70 x).
Proof. exact (MK_COMB (@lem2256357) (@lem2256356 x)). Qed.
Lemma lem2256359 (y : real) (x : real) : (term61 x y) = (term39 y x).
Proof. exact (eq_refl (term61 x y)). Qed.
Lemma lem2256360 (x : real) : (term71 x) = (term58 x).
Proof. exact (fun_ext (fun y : real => @lem2256359 y x)). Qed.
Lemma lem2256361 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2256362 (x : real) : (term72 x) = (term73 x).
Proof. exact (MK_COMB (@lem2256361) (@lem2256360 x)). Qed.
Lemma lem2256363 (x : real) : (term56 x) = (term74 x).
Proof. exact (MK_COMB (@lem2256358 x) (@lem2256362 x)). Qed.
Lemma lem2256364 (x : real) : ((term55 x) = (term56 x)) = ((term48 x) = (term74 x)).
Proof. exact (MK_COMB (@lem2256352 x) (@lem2256363 x)). Qed.
Lemma lem2256365 (x : real) : (term48 x) = (term74 x).
Proof. exact (EQ_MP (@lem2256364 x) (@lem2256342 x)). Qed.
Lemma lem2256462 : term49 = term75.
Proof. exact (fun_ext (fun x : real => @lem2256365 x)). Qed.
Lemma lem2256463 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2256464 : term50 = term76.
Proof. exact (MK_COMB (@lem2256463) (@lem2256462)). Qed.
Lemma lem2256466 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term51 A P Q) = (term52 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem2256467 (P : real -> Prop) (Q : real -> Prop) : (term53 P Q) = (term54 P Q).
Proof. exact (@lem2256466 real P Q). Qed.
Lemma lem2256468 : term77 = term78.
Proof. exact (@lem2256467 term79 term80). Qed.
Lemma lem2256469 (x : real) : (term81 x) = (term68 x).
Proof. exact (eq_refl (term81 x)). Qed.
Lemma lem2256470 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2256471 (x : real) : (term82 x) = (term70 x).
Proof. exact (MK_COMB (@lem2256470) (@lem2256469 x)). Qed.
Lemma lem2256472 (x : real) : (term83 x) = (term73 x).
Proof. exact (eq_refl (term83 x)). Qed.
Lemma lem2256473 (x : real) : (term84 x) = (term74 x).
Proof. exact (MK_COMB (@lem2256471 x) (@lem2256472 x)). Qed.
Lemma lem2256474 : term85 = term75.
Proof. exact (fun_ext (fun x : real => @lem2256473 x)). Qed.
Lemma lem2256475 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2256476 : term77 = term76.
Proof. exact (MK_COMB (@lem2256475) (@lem2256474)). Qed.
Lemma lem2256477 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2256478 : term86 = term87.
Proof. exact (MK_COMB (@lem2256477) (@lem2256476)). Qed.
Lemma lem2256479 (x : real) : (term81 x) = (term68 x).
Proof. exact (eq_refl (term81 x)). Qed.
Lemma lem2256480 : term88 = term79.
Proof. exact (fun_ext (fun x : real => @lem2256479 x)). Qed.
Lemma lem2256481 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2256482 : term89 = term90.
Proof. exact (MK_COMB (@lem2256481) (@lem2256480)). Qed.
Lemma lem2256483 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2256484 : term91 = term92.
Proof. exact (MK_COMB (@lem2256483) (@lem2256482)). Qed.
Lemma lem2256485 (x : real) : (term83 x) = (term73 x).
Proof. exact (eq_refl (term83 x)). Qed.
Lemma lem2256486 : term93 = term80.
Proof. exact (fun_ext (fun x : real => @lem2256485 x)). Qed.
Lemma lem2256487 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2256488 : term94 = term95.
Proof. exact (MK_COMB (@lem2256487) (@lem2256486)). Qed.
Lemma lem2256489 : term78 = term96.
Proof. exact (MK_COMB (@lem2256484) (@lem2256488)). Qed.
Lemma lem2256490 : (term77 = term78) = (term76 = term96).
Proof. exact (MK_COMB (@lem2256478) (@lem2256489)). Qed.
Lemma lem2256491 : term76 = term96.
Proof. exact (EQ_MP (@lem2256490) (@lem2256468)). Qed.
Lemma lem2256598 : term50 = term96.
Proof. exact (TRANS (@lem2256464) (@lem2256491)). Qed.
Lemma lem2256599 : term10 = term96.
Proof. exact (TRANS (@lem2256334) (@lem2256598)). Qed.
Lemma lem2256600 (h1 : term10) : term96.
Proof. exact (EQ_MP (@lem2256599) (@lem2256270 h1)). Qed.
Lemma lem2256697 (y : real) (x : real) : (term39 y x) = (term39 y x).
Proof. exact (eq_refl (term39 y x)). Qed.
Lemma lem2256698 (x : real) : (term58 x) = (term58 x).
Proof. exact (fun_ext (fun y : real => @lem2256697 y x)). Qed.
Lemma lem2256699 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2256700 (x : real) : (term73 x) = (term73 x).
Proof. exact (MK_COMB (@lem2256699) (@lem2256698 x)). Qed.
Lemma lem2256701 : term80 = term80.
Proof. exact (fun_ext (fun x : real => @lem2256700 x)). Qed.
Lemma lem2256702 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2256703 : term95 = term95.
Proof. exact (MK_COMB (@lem2256702) (@lem2256701)). Qed.
Lemma lem2256768 (y : real) (x : real) : (term42 y x) = (term42 y x).
Proof. exact (eq_refl (term42 y x)). Qed.
Lemma lem2256769 (x : real) : (term57 x) = (term57 x).
Proof. exact (fun_ext (fun y : real => @lem2256768 y x)). Qed.
Lemma lem2256770 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2256771 (x : real) : (term68 x) = (term68 x).
Proof. exact (MK_COMB (@lem2256770) (@lem2256769 x)). Qed.
Lemma lem2256772 : term79 = term79.
Proof. exact (fun_ext (fun x : real => @lem2256771 x)). Qed.
Lemma lem2256773 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2256774 : term90 = term90.
Proof. exact (MK_COMB (@lem2256773) (@lem2256772)). Qed.
Lemma lem2256775 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2256776 : term92 = term92.
Proof. exact (MK_COMB (@lem2256775) (@lem2256774)). Qed.
Lemma lem2256777 : term96 = term96.
Proof. exact (MK_COMB (@lem2256776) (@lem2256703)). Qed.
Lemma lem2256778 (h1 : term10) : term96.
Proof. exact (EQ_MP (@lem2256777) (@lem2256600 h1)). Qed.
Lemma lem2256834 (x : real) (h1 : term31 x) : term31 x.
Proof. exact (h1). Qed.
Lemma lem2256835 (h1 : term10) : term95.
Proof. exact (proj2 (@lem2256778 h1)). Qed.
Lemma lem2256847 (x : real) (h1 : term31 x) : term31 x.
Proof. exact (h1). Qed.
Lemma lem2256887 (y : real) (x : real) : (term39 y x) = (term97 y x).
Proof. exact (@lem19490 (term37 y) (term98 x y) ((term38 y) = x)). Qed.
Lemma lem2256888 (x : real) : (term58 x) = (term99 x).
Proof. exact (fun_ext (fun y : real => @lem2256887 y x)). Qed.
Lemma lem2256889 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2256890 (x : real) : (term73 x) = (term100 x).
Proof. exact (MK_COMB (@lem2256889) (@lem2256888 x)). Qed.
Lemma lem2256891 : term80 = term101.
Proof. exact (fun_ext (fun x : real => @lem2256890 x)). Qed.
Lemma lem2256892 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2256894 : term95 = term102.
Proof. exact (MK_COMB (@lem2256892) (@lem2256891)). Qed.
Lemma lem2256895 (h1 : term10) : term102.
Proof. exact (EQ_MP (@lem2256894) (@lem2256835 h1)). Qed.
Lemma lem2256905 (_28504 : real) (h1 : term10) : term103 _28504.
Proof. exact (@lem2256895 h1 _28504). Qed.
Lemma lem2256906 (_28504 : real) : (term103 _28504) = (term100 _28504).
Proof. exact (eq_refl (term103 _28504)). Qed.
Lemma lem2256907 (_28504 : real) (h1 : term10) : term100 _28504.
Proof. exact (EQ_MP (@lem2256906 _28504) (@lem2256905 _28504 h1)). Qed.
Lemma lem2256908 (_28504 : real) (_28505 : real) (h1 : term10) : term104 _28504 _28505.
Proof. exact (@lem2256907 _28504 h1 _28505). Qed.
Lemma lem2256909 (_28505 : real) (_28504 : real) : (term104 _28504 _28505) = (term97 _28505 _28504).
Proof. exact (eq_refl (term104 _28504 _28505)). Qed.
Lemma lem2256910 (_28505 : real) (_28504 : real) (h1 : term10) : term97 _28505 _28504.
Proof. exact (EQ_MP (@lem2256909 _28505 _28504) (@lem2256908 _28504 _28505 h1)). Qed.
Lemma lem2256916 (x : real) (h1 : term31 x) : term31 x.
Proof. exact (h1). Qed.
Lemma lem2256938 (_28505 : real) (_28504 : real) (h1 : term10) : term105 _28505 _28504.
Proof. exact (proj2 (@lem2256910 _28505 _28504 h1)). Qed.
Lemma lem2257040 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem2257041 (x : real) : (term16 x) = (term16 x).
Proof. exact (@lem2257040 (term16 x)). Qed.
Lemma lem2257042 (x : real) : term106 x.
Proof. exact (fun h0 : term107 x => @lem2257041 x). Qed.
Lemma lem2257044 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2257045 (x : real) : (term106 x) = ((term16 x) = (term16 x)).
Proof. exact (@lem2257044 ((term16 x) = (term16 x))). Qed.
Lemma lem2257046 (x : real) : (term16 x) = (term16 x).
Proof. exact (EQ_MP (@lem2257045 x) (@lem2257042 x)). Qed.
Lemma lem2257052 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem2257053 (_28504 : real) (_28505 : real) : (term105 _28505 _28504) = (term109 _28504 _28505).
Proof. exact (@lem2257052 ((term38 _28505) = _28504) (term98 _28504 _28505)). Qed.
Lemma lem2257063 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2257064 (_28504 : real) (_28505 : real) : (term110 _28505 _28504) = (term111 _28504 _28505).
Proof. exact (MK_COMB (@lem2257063) (@lem2257053 _28504 _28505)). Qed.
Lemma lem2257074 (_28504 : real) (_28505 : real) : (term109 _28504 _28505) = (term109 _28504 _28505).
Proof. exact (eq_refl (term109 _28504 _28505)). Qed.
Lemma lem2257075 (_28504 : real) (_28505 : real) : ((term105 _28505 _28504) = (term109 _28504 _28505)) = ((term109 _28504 _28505) = (term109 _28504 _28505)).
Proof. exact (MK_COMB (@lem2257064 _28504 _28505) (@lem2257074 _28504 _28505)). Qed.
Lemma lem2257077 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem2257078 (x : Prop) : (x = x) = True.
Proof. exact (@lem2257077 Prop x). Qed.
Lemma lem2257079 (_28504 : real) (_28505 : real) : ((term109 _28504 _28505) = (term109 _28504 _28505)) = True.
Proof. exact (@lem2257078 (term109 _28504 _28505)). Qed.
Lemma lem2257080 (_28504 : real) (_28505 : real) : ((term105 _28505 _28504) = (term109 _28504 _28505)) = True.
Proof. exact (TRANS (@lem2257075 _28504 _28505) (@lem2257079 _28504 _28505)). Qed.
Lemma lem2257081 (_28504 : real) (_28505 : real) : True = ((term105 _28505 _28504) = (term109 _28504 _28505)).
Proof. exact (SYM (@lem2257080 _28504 _28505)). Qed.
Lemma lem2257082 (_28504 : real) (_28505 : real) : (term105 _28505 _28504) = (term109 _28504 _28505).
Proof. exact (EQ_MP (@lem2257081 _28504 _28505) (@lem0)). Qed.
Lemma lem2257083 (_28504 : real) (_28505 : real) (h1 : term10) : term109 _28504 _28505.
Proof. exact (EQ_MP (@lem2257082 _28504 _28505) (@lem2256938 _28505 _28504 h1)). Qed.
Lemma lem2257085 (b : Prop) (a : Prop) : (a \/ b) = (term112 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem2257086 (_28505 : real) (_28504 : real) : (term109 _28504 _28505) = (term113 _28505 _28504).
Proof. exact (@lem2257085 (term98 _28504 _28505) ((term38 _28505) = _28504)). Qed.
Lemma lem2257088 (a : Prop) : (term114 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem2257089 (_28504 : real) (_28505 : real) : (term115 _28504 _28505) = ((term16 _28504) = _28505).
Proof. exact (@lem2257088 ((term16 _28504) = _28505)). Qed.
Lemma lem2257090 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2257091 (_28504 : real) (_28505 : real) : (term116 _28504 _28505) = (term117 _28504 _28505).
Proof. exact (MK_COMB (@lem2257090) (@lem2257089 _28504 _28505)). Qed.
Lemma lem2257092 (_28505 : real) (_28504 : real) : ((term38 _28505) = _28504) = ((term38 _28505) = _28504).
Proof. exact (eq_refl ((term38 _28505) = _28504)). Qed.
Lemma lem2257093 (_28505 : real) (_28504 : real) : (term113 _28505 _28504) = (term118 _28505 _28504).
Proof. exact (MK_COMB (@lem2257091 _28504 _28505) (@lem2257092 _28505 _28504)). Qed.
Lemma lem2257094 (_28505 : real) (_28504 : real) : (term109 _28504 _28505) = (term118 _28505 _28504).
Proof. exact (TRANS (@lem2257086 _28505 _28504) (@lem2257093 _28505 _28504)). Qed.
Lemma lem2257097 (_28505 : real) (_28504 : real) (h1 : term10) : term118 _28505 _28504.
Proof. exact (EQ_MP (@lem2257094 _28505 _28504) (@lem2257083 _28504 _28505 h1)). Qed.
Lemma lem2257098 (x : real) (h1 : term10) : term119 x.
Proof. exact (@lem2257097 (term16 x) x h1). Qed.
Lemma lem2257101 (x : real) (h1 : term10) : (term24 x) = x.
Proof. exact (@lem2257098 x h1 (@lem2257046 x)). Qed.
Lemma lem2257102 (x : real) (h1 : term10) : term120 x.
Proof. exact (fun h0 : term31 x => @lem2257101 x h1). Qed.
Lemma lem2257104 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2257105 (x : real) : (term120 x) = ((term24 x) = x).
Proof. exact (@lem2257104 ((term24 x) = x)). Qed.
Lemma lem2257106 (x : real) (h1 : term10) : (term24 x) = x.
Proof. exact (EQ_MP (@lem2257105 x) (@lem2257102 x h1)). Qed.
Lemma lem2257109 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem2257111 (x : real) : (term31 x) = (term121 x).
Proof. exact (@lem2257109 ((term24 x) = x)). Qed.
Lemma lem2257114 (x : real) (h1 : term31 x) : term121 x.
Proof. exact (EQ_MP (@lem2257111 x) (@lem2256916 x h1)). Qed.
Lemma lem2257117 (x : real) (h1 : term10) (h2 : term31 x) : False.
Proof. exact (@lem2257114 x h2 (@lem2257106 x h1)). Qed.
Lemma lem2257118 (x : real) (h1 : term10) (h2 : term31 x) : term122.
Proof. exact (fun h0 : ~ False => @lem2257117 x h1 h2). Qed.
Lemma lem2257120 (p : Prop) : (term108 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2257121 : term122 = False.
Proof. exact (@lem2257120 False). Qed.
Lemma lem2257122 (x : real) (h1 : term10) (h2 : term31 x) : False.
Proof. exact (EQ_MP (@lem2257121) (@lem2257118 x h1 h2)). Qed.
Lemma lem2257123 (x : real) (h1 : term10) (h2 : term31 x) : (term31 x) = False.
Proof. exact (prop_ext (fun h3 : term31 x => @lem2257122 x h1 h2) (fun h3 : False => @lem2256916 x h2)). Qed.
Lemma lem2257124 (x : real) (h1 : term10) (h2 : term31 x) : False.
Proof. exact (EQ_MP (@lem2257123 x h1 h2) (@lem2256916 x h2)). Qed.
Lemma lem2257125 (x : real) (h1 : term10) (h2 : term31 x) : (term31 x) = False.
Proof. exact (prop_ext (fun h3 : term31 x => @lem2257124 x h1 h2) (fun h3 : False => @lem2256847 x h2)). Qed.
Lemma lem2257126 (x : real) (h1 : term10) (h2 : term31 x) : False.
Proof. exact (EQ_MP (@lem2257125 x h1 h2) (@lem2256847 x h2)). Qed.
Lemma lem2257127 (x : real) (h1 : term10) (h2 : term31 x) : (term31 x) = False.
Proof. exact (prop_ext (fun h3 : term31 x => @lem2257126 x h1 h2) (fun h3 : False => @lem2256847 x h2)). Qed.
Lemma lem2257128 (x : real) (h1 : term10) (h2 : term31 x) : False.
Proof. exact (EQ_MP (@lem2257127 x h1 h2) (@lem2256847 x h2)). Qed.
Lemma lem2257129 (x : real) (h1 : term10) (h2 : term31 x) : (term31 x) = False.
Proof. exact (prop_ext (fun h3 : term31 x => @lem2257128 x h1 h2) (fun h3 : False => @lem2256834 x h2)). Qed.
Lemma lem2257130 (x : real) (h1 : term10) (h2 : term31 x) : False.
Proof. exact (EQ_MP (@lem2257129 x h1 h2) (@lem2256834 x h2)). Qed.
Lemma lem2257131 (h1 : term10) (h2 : term3) : False.
Proof. exact (ex_elim (@lem2256290 h2) (fun x : real => fun h0 : term33 x => @lem2257130 x h1 h0)). Qed.
Lemma lem2257132 (h1 : term3) : term8.
Proof. exact (fun h0 : term10 => @lem2257131 h0 h1). Qed.
Lemma lem2257133 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem2257134 (h1 : term3) : term9.
Proof. exact (EQ_MP (@lem2257133) (@lem2257132 h1)). Qed.
Lemma lem2257135 (h1 : term3) : term13.
Proof. exact (fun h0 : term23 => @lem2257134 h1). Qed.
Lemma lem2257136 : term15.
Proof. exact (fun h0 : term3 => @lem2257135 h0). Qed.
Lemma lem2257137 : term4.
Proof. exact (EQ_MP (@lem2256267) (@lem2257136)). Qed.
Lemma lem2257139 : term4.
Proof. exact (@lem2256163 (@lem2257137)). Qed.
Lemma lem2257140 (h1 : term3) : term12.
Proof. exact (@lem2257139 (@lem2256148 h1)). Qed.
Lemma lem2257141 (h1 : term3) : term8.
Proof. exact (@lem2257140 h1 (@lem2004769)). Qed.
Lemma lem2257142 (h1 : term3) : False.
Proof. exact (@lem2257141 h1 (@lem2256133)). Qed.
Lemma lem2257143 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem2257142 h1) (fun h2 : False => @lem2256148 h1)). Qed.
Lemma lem2257144 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem2257143 h1) (@lem2256148 h1)). Qed.
Lemma lem2257145 : term2.
Proof. exact (fun h0 : term3 => @lem2257144 h0). Qed.
Lemma lem2257146 : term1.
Proof. exact (EQ_MP (@lem2256147) (@lem2257145)). Qed.
