Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LE_INV_EQ_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import REAL_INV_EQ_0_spec.
Require Import REAL_LE_LT_spec.
Require Import REAL_LT_INV_EQ_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
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
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm69_spec.
Lemma lem1590222 (x : real) : term0 x.
Proof. exact (@lem1590037 x). Qed.
Lemma lem1590223 (x : real) : (term0 x) = ((term1 x) = (term2 x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1590225 (x : real) : term3 x.
Proof. exact (@lem1376325 x). Qed.
Lemma lem1590226 (x : real) : (term3 x) = (term4 x).
Proof. exact (eq_refl (term3 x)). Qed.
Lemma lem1590227 (x : real) : term4 x.
Proof. exact (EQ_MP (@lem1590226 x) (@lem1590225 x)). Qed.
Lemma lem1590228 (x : real) (y : real) : term5 x y.
Proof. exact (@lem1590227 x y). Qed.
Lemma lem1590229 (x : real) (y : real) : (term5 x y) = ((real_le x y) = (term6 x y)).
Proof. exact (eq_refl (term5 x y)). Qed.
Lemma lem1590238 (x : real) (y : real) : (real_le x y) = (term6 x y).
Proof. exact (EQ_MP (@lem1590229 x y) (@lem1590228 x y)). Qed.
Lemma lem1590239 (x : real) : (term7 x) = (term8 x).
Proof. exact (@lem1590238 term9 (real_inv x)). Qed.
Lemma lem1590243 (x : real) : (term1 x) = (term2 x).
Proof. exact (EQ_MP (@lem1590223 x) (@lem1590222 x)). Qed.
Lemma lem1590244 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1590245 (x : real) : (term10 x) = (term11 x).
Proof. exact (MK_COMB (@lem1590244) (@lem1590243 x)). Qed.
Lemma lem1590248 (x : real) : (term9 = (real_inv x)) = (term9 = (real_inv x)).
Proof. exact (eq_refl (term9 = (real_inv x))). Qed.
Lemma lem1590249 (x : real) : (term8 x) = (term12 x).
Proof. exact (MK_COMB (@lem1590245 x) (@lem1590248 x)). Qed.
Lemma lem1590252 (x : real) : (term7 x) = (term12 x).
Proof. exact (TRANS (@lem1590239 x) (@lem1590249 x)). Qed.
Lemma lem1590253 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1590254 (x : real) : (term13 x) = (term14 x).
Proof. exact (MK_COMB (@lem1590253) (@lem1590252 x)). Qed.
Lemma lem1590256 (x : real) (y : real) : (real_le x y) = (term6 x y).
Proof. exact (EQ_MP (@lem1590229 x y) (@lem1590228 x y)). Qed.
Lemma lem1590257 (x : real) : (term15 x) = (term16 x).
Proof. exact (@lem1590256 term9 x). Qed.
Lemma lem1590262 (x : real) : ((term7 x) = (term15 x)) = ((term12 x) = (term16 x)).
Proof. exact (MK_COMB (@lem1590254 x) (@lem1590257 x)). Qed.
Lemma lem1590265 : term17 = term18.
Proof. exact (fun_ext (fun x : real => @lem1590262 x)). Qed.
Lemma lem1590266 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1590267 : term19 = term20.
Proof. exact (MK_COMB (@lem1590266) (@lem1590265)). Qed.
Lemma lem1590272 : term20 = term19.
Proof. exact (SYM (@lem1590267)). Qed.
Lemma lem1590274 (p : Prop) : p = (term21 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1590275 : term20 = term22.
Proof. exact (@lem1590274 term20). Qed.
Lemma lem1590276 : term22 = term20.
Proof. exact (SYM (@lem1590275)). Qed.
Lemma lem1590277 (h1 : term23) : term23.
Proof. exact (h1). Qed.
Lemma lem1590280 (h1 : term24) : term24.
Proof. exact (h1). Qed.
Lemma lem1590281 : term25.
Proof. exact (fun h0 : term24 => @lem1590280 h0). Qed.
Lemma lem1590282 (h1 : term25) : term25.
Proof. exact (h1). Qed.
Lemma lem1590283 (h1 : term24) : term24.
Proof. exact (h1). Qed.
Lemma lem1590284 (h1 : term24) (h2 : term25) : term24.
Proof. exact (@lem1590282 h2 (@lem1590283 h1)). Qed.
Lemma lem1590285 (h1 : term24) : term26.
Proof. exact (fun h0 : term25 => @lem1590284 h1 h0). Qed.
Lemma lem1590286 (h1 : term25) : term25.
Proof. exact (h1). Qed.
Lemma lem1590287 (h1 : term24) (h2 : term25) : term24.
Proof. exact (@lem1590285 h1 (@lem1590286 h2)). Qed.
Lemma lem1590288 (h1 : term25) : term25.
Proof. exact (fun h0 : term24 => @lem1590287 h0 h1). Qed.
Lemma lem1590289 : term27.
Proof. exact (fun h0 : term25 => @lem1590288 h0). Qed.
Lemma lem1590292 : term25.
Proof. exact (@lem1590289 (@lem1590281)). Qed.
Lemma lem1590304 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1590305 : term28 = term29.
Proof. exact (@lem1590304 term30). Qed.
Lemma lem1590310 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem1590317 : term24 = term32.
Proof. exact (MK_COMB (@lem1590310) (@lem1590305)). Qed.
Lemma lem1590322 (x : real) : (((real_inv x) = term9) = (x = term9)) = (((real_inv x) = term9) = (x = term9)).
Proof. exact (eq_refl (((real_inv x) = term9) = (x = term9))). Qed.
Lemma lem1590323 : term33 = term33.
Proof. exact (fun_ext (fun x : real => @lem1590322 x)). Qed.
Lemma lem1590324 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1590325 : term30 = term30.
Proof. exact (MK_COMB (@lem1590324) (@lem1590323)). Qed.
Lemma lem1590326 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1590327 : term29 = term29.
Proof. exact (MK_COMB (@lem1590326) (@lem1590325)). Qed.
Lemma lem1590340 (x : real) : ((term12 x) = (term16 x)) = ((term12 x) = (term16 x)).
Proof. exact (eq_refl ((term12 x) = (term16 x))). Qed.
Lemma lem1590341 : term18 = term18.
Proof. exact (fun_ext (fun x : real => @lem1590340 x)). Qed.
Lemma lem1590342 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1590343 : term20 = term20.
Proof. exact (MK_COMB (@lem1590342) (@lem1590341)). Qed.
Lemma lem1590344 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1590345 : term23 = term23.
Proof. exact (MK_COMB (@lem1590344) (@lem1590343)). Qed.
Lemma lem1590346 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1590347 : term31 = term31.
Proof. exact (MK_COMB (@lem1590346) (@lem1590345)). Qed.
Lemma lem1590348 : term32 = term32.
Proof. exact (MK_COMB (@lem1590347) (@lem1590327)). Qed.
Lemma lem1590369 : term24 = term32.
Proof. exact (TRANS (@lem1590317) (@lem1590348)). Qed.
Lemma lem1590370 : term32 = term24.
Proof. exact (SYM (@lem1590369)). Qed.
Lemma lem1590371 (h1 : term23) : term23.
Proof. exact (h1). Qed.
Lemma lem1590372 (h1 : term30) : term30.
Proof. exact (h1). Qed.
Lemma lem1590381 (x : real) : (term34 x) = (term35 x).
Proof. exact (@lem17160 (term2 x) (term9 = (real_inv x))). Qed.
Lemma lem1590393 (x : real) : (term36 x) = (term37 x).
Proof. exact (@lem17160 (term2 x) (term9 = x)). Qed.
Lemma lem1590396 (x : real) : (term16 x) = (term16 x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1590397 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1590398 (x : real) : (term38 x) = (term39 x).
Proof. exact (MK_COMB (@lem1590397) (@lem1590381 x)). Qed.
Lemma lem1590399 (x : real) : (term40 x) = (term41 x).
Proof. exact (MK_COMB (@lem1590398 x) (@lem1590396 x)). Qed.
Lemma lem1590401 (x : real) : (term42 x) = (term42 x).
Proof. exact (eq_refl (term42 x)). Qed.
Lemma lem1590402 (x : real) : (term43 x) = (term44 x).
Proof. exact (MK_COMB (@lem1590401 x) (@lem1590393 x)). Qed.
Lemma lem1590403 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1590404 (x : real) : (term45 x) = (term46 x).
Proof. exact (MK_COMB (@lem1590403) (@lem1590402 x)). Qed.
Lemma lem1590405 (x : real) : (term47 x) = (term48 x).
Proof. exact (MK_COMB (@lem1590404 x) (@lem1590399 x)). Qed.
Lemma lem1590406 (x : real) : (term49 x) = (term47 x).
Proof. exact (@lem17646 (term12 x) (term16 x)). Qed.
Lemma lem1590407 (x : real) : (term49 x) = (term48 x).
Proof. exact (TRANS (@lem1590406 x) (@lem1590405 x)). Qed.
Lemma lem1590408 (P : real -> Prop) : (term50 P) = (term51 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1590409 : term23 = term52.
Proof. exact (@lem1590408 term18). Qed.
Lemma lem1590410 (x : real) : (term53 x) = ((term12 x) = (term16 x)).
Proof. exact (eq_refl (term53 x)). Qed.
Lemma lem1590411 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1590412 (x : real) : (term54 x) = (term49 x).
Proof. exact (MK_COMB (@lem1590411) (@lem1590410 x)). Qed.
Lemma lem1590413 (x : real) : (term54 x) = (term48 x).
Proof. exact (TRANS (@lem1590412 x) (@lem1590407 x)). Qed.
Lemma lem1590414 : term55 = term56.
Proof. exact (fun_ext (fun x : real => @lem1590413 x)). Qed.
Lemma lem1590415 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1590416 : term52 = term57.
Proof. exact (MK_COMB (@lem1590415) (@lem1590414)). Qed.
Lemma lem1590417 : term23 = term57.
Proof. exact (TRANS (@lem1590409) (@lem1590416)). Qed.
Lemma lem1590419 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term58 A P Q) = (term59 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1590420 (P : real -> Prop) (Q : real -> Prop) : (term60 P Q) = (term61 P Q).
Proof. exact (@lem1590419 real P Q). Qed.
Lemma lem1590421 : term62 = term63.
Proof. exact (@lem1590420 term64 term65). Qed.
Lemma lem1590422 (x : real) : (term66 x) = (term44 x).
Proof. exact (eq_refl (term66 x)). Qed.
Lemma lem1590423 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1590424 (x : real) : (term67 x) = (term46 x).
Proof. exact (MK_COMB (@lem1590423) (@lem1590422 x)). Qed.
Lemma lem1590425 (x : real) : (term68 x) = (term41 x).
Proof. exact (eq_refl (term68 x)). Qed.
Lemma lem1590426 (x : real) : (term69 x) = (term48 x).
Proof. exact (MK_COMB (@lem1590424 x) (@lem1590425 x)). Qed.
Lemma lem1590427 : term70 = term56.
Proof. exact (fun_ext (fun x : real => @lem1590426 x)). Qed.
Lemma lem1590428 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1590429 : term62 = term57.
Proof. exact (MK_COMB (@lem1590428) (@lem1590427)). Qed.
Lemma lem1590430 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1590431 : term71 = term72.
Proof. exact (MK_COMB (@lem1590430) (@lem1590429)). Qed.
Lemma lem1590432 (x : real) : (term66 x) = (term44 x).
Proof. exact (eq_refl (term66 x)). Qed.
Lemma lem1590433 : term73 = term64.
Proof. exact (fun_ext (fun x : real => @lem1590432 x)). Qed.
Lemma lem1590434 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1590435 : term74 = term75.
Proof. exact (MK_COMB (@lem1590434) (@lem1590433)). Qed.
Lemma lem1590436 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1590437 : term76 = term77.
Proof. exact (MK_COMB (@lem1590436) (@lem1590435)). Qed.
Lemma lem1590438 (x : real) : (term68 x) = (term41 x).
Proof. exact (eq_refl (term68 x)). Qed.
Lemma lem1590439 : term78 = term65.
Proof. exact (fun_ext (fun x : real => @lem1590438 x)). Qed.
Lemma lem1590440 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1590441 : term79 = term80.
Proof. exact (MK_COMB (@lem1590440) (@lem1590439)). Qed.
Lemma lem1590442 : term63 = term81.
Proof. exact (MK_COMB (@lem1590437) (@lem1590441)). Qed.
Lemma lem1590443 : (term62 = term63) = (term57 = term81).
Proof. exact (MK_COMB (@lem1590431) (@lem1590442)). Qed.
Lemma lem1590444 : term57 = term81.
Proof. exact (EQ_MP (@lem1590443) (@lem1590421)). Qed.
Lemma lem1590542 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term59 A P Q) = (term58 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1590543 (P : real -> Prop) (Q : real -> Prop) : (term61 P Q) = (term60 P Q).
Proof. exact (@lem1590542 real P Q). Qed.
Lemma lem1590544 : term63 = term62.
Proof. exact (@lem1590543 term64 term65). Qed.
Lemma lem1590545 (x : real) : (term66 x) = (term44 x).
Proof. exact (eq_refl (term66 x)). Qed.
Lemma lem1590546 : term73 = term64.
Proof. exact (fun_ext (fun x : real => @lem1590545 x)). Qed.
Lemma lem1590547 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1590548 : term74 = term75.
Proof. exact (MK_COMB (@lem1590547) (@lem1590546)). Qed.
Lemma lem1590549 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1590550 : term76 = term77.
Proof. exact (MK_COMB (@lem1590549) (@lem1590548)). Qed.
Lemma lem1590551 (x : real) : (term68 x) = (term41 x).
Proof. exact (eq_refl (term68 x)). Qed.
Lemma lem1590552 : term78 = term65.
Proof. exact (fun_ext (fun x : real => @lem1590551 x)). Qed.
Lemma lem1590553 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1590554 : term79 = term80.
Proof. exact (MK_COMB (@lem1590553) (@lem1590552)). Qed.
Lemma lem1590555 : term63 = term81.
Proof. exact (MK_COMB (@lem1590550) (@lem1590554)). Qed.
Lemma lem1590556 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1590557 : term82 = term83.
Proof. exact (MK_COMB (@lem1590556) (@lem1590555)). Qed.
Lemma lem1590558 (x : real) : (term66 x) = (term44 x).
Proof. exact (eq_refl (term66 x)). Qed.
Lemma lem1590559 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1590560 (x : real) : (term67 x) = (term46 x).
Proof. exact (MK_COMB (@lem1590559) (@lem1590558 x)). Qed.
Lemma lem1590561 (x : real) : (term68 x) = (term41 x).
Proof. exact (eq_refl (term68 x)). Qed.
Lemma lem1590562 (x : real) : (term69 x) = (term48 x).
Proof. exact (MK_COMB (@lem1590560 x) (@lem1590561 x)). Qed.
Lemma lem1590563 : term70 = term56.
Proof. exact (fun_ext (fun x : real => @lem1590562 x)). Qed.
Lemma lem1590564 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1590565 : term62 = term57.
Proof. exact (MK_COMB (@lem1590564) (@lem1590563)). Qed.
Lemma lem1590566 : (term63 = term62) = (term81 = term57).
Proof. exact (MK_COMB (@lem1590557) (@lem1590565)). Qed.
Lemma lem1590567 : term81 = term57.
Proof. exact (EQ_MP (@lem1590566) (@lem1590544)). Qed.
Lemma lem1590568 : term57 = term57.
Proof. exact (TRANS (@lem1590444) (@lem1590567)). Qed.
Lemma lem1590569 : term23 = term57.
Proof. exact (TRANS (@lem1590417) (@lem1590568)). Qed.
Lemma lem1590570 (h1 : term23) : term57.
Proof. exact (EQ_MP (@lem1590569) (@lem1590371 h1)). Qed.
Lemma lem1590585 (x : real) : (((real_inv x) = term9) = (x = term9)) = (term84 x).
Proof. exact (@lem17784 ((real_inv x) = term9) (x = term9)). Qed.
Lemma lem1590586 : term33 = term85.
Proof. exact (fun_ext (fun x : real => @lem1590585 x)). Qed.
Lemma lem1590587 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1590588 : term30 = term86.
Proof. exact (MK_COMB (@lem1590587) (@lem1590586)). Qed.
Lemma lem1590590 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term87 A P Q) = (term88 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1590591 (P : real -> Prop) (Q : real -> Prop) : (term89 P Q) = (term90 P Q).
Proof. exact (@lem1590590 real P Q). Qed.
Lemma lem1590592 : term91 = term92.
Proof. exact (@lem1590591 term93 term94). Qed.
Lemma lem1590593 (x : real) : (term95 x) = (term96 x).
Proof. exact (eq_refl (term95 x)). Qed.
Lemma lem1590594 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1590595 (x : real) : (term97 x) = (term98 x).
Proof. exact (MK_COMB (@lem1590594) (@lem1590593 x)). Qed.
Lemma lem1590596 (x : real) : (term99 x) = (term100 x).
Proof. exact (eq_refl (term99 x)). Qed.
Lemma lem1590597 (x : real) : (term101 x) = (term84 x).
Proof. exact (MK_COMB (@lem1590595 x) (@lem1590596 x)). Qed.
Lemma lem1590598 : term102 = term85.
Proof. exact (fun_ext (fun x : real => @lem1590597 x)). Qed.
Lemma lem1590599 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1590600 : term91 = term86.
Proof. exact (MK_COMB (@lem1590599) (@lem1590598)). Qed.
Lemma lem1590601 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1590602 : term103 = term104.
Proof. exact (MK_COMB (@lem1590601) (@lem1590600)). Qed.
Lemma lem1590603 (x : real) : (term95 x) = (term96 x).
Proof. exact (eq_refl (term95 x)). Qed.
Lemma lem1590604 : term105 = term93.
Proof. exact (fun_ext (fun x : real => @lem1590603 x)). Qed.
Lemma lem1590605 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1590606 : term106 = term107.
Proof. exact (MK_COMB (@lem1590605) (@lem1590604)). Qed.
Lemma lem1590607 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1590608 : term108 = term109.
Proof. exact (MK_COMB (@lem1590607) (@lem1590606)). Qed.
Lemma lem1590609 (x : real) : (term99 x) = (term100 x).
Proof. exact (eq_refl (term99 x)). Qed.
Lemma lem1590610 : term110 = term94.
Proof. exact (fun_ext (fun x : real => @lem1590609 x)). Qed.
Lemma lem1590611 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1590612 : term111 = term112.
Proof. exact (MK_COMB (@lem1590611) (@lem1590610)). Qed.
Lemma lem1590613 : term92 = term113.
Proof. exact (MK_COMB (@lem1590608) (@lem1590612)). Qed.
Lemma lem1590614 : (term91 = term92) = (term86 = term113).
Proof. exact (MK_COMB (@lem1590602) (@lem1590613)). Qed.
Lemma lem1590713 : term86 = term113.
Proof. exact (EQ_MP (@lem1590614) (@lem1590592)). Qed.
Lemma lem1590714 : term30 = term113.
Proof. exact (TRANS (@lem1590588) (@lem1590713)). Qed.
Lemma lem1590715 (h1 : term30) : term113.
Proof. exact (EQ_MP (@lem1590714) (@lem1590372 h1)). Qed.
Lemma lem1590741 (x : real) : (term100 x) = (term100 x).
Proof. exact (eq_refl (term100 x)). Qed.
Lemma lem1590742 : term94 = term94.
Proof. exact (fun_ext (fun x : real => @lem1590741 x)). Qed.
Lemma lem1590743 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1590744 : term112 = term112.
Proof. exact (MK_COMB (@lem1590743) (@lem1590742)). Qed.
Lemma lem1590769 (x : real) : (term96 x) = (term96 x).
Proof. exact (eq_refl (term96 x)). Qed.
Lemma lem1590770 : term93 = term93.
Proof. exact (fun_ext (fun x : real => @lem1590769 x)). Qed.
Lemma lem1590771 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1590772 : term107 = term107.
Proof. exact (MK_COMB (@lem1590771) (@lem1590770)). Qed.
Lemma lem1590773 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1590774 : term109 = term109.
Proof. exact (MK_COMB (@lem1590773) (@lem1590772)). Qed.
Lemma lem1590775 : term113 = term113.
Proof. exact (MK_COMB (@lem1590774) (@lem1590744)). Qed.
Lemma lem1590776 (h1 : term30) : term113.
Proof. exact (EQ_MP (@lem1590775) (@lem1590715 h1)). Qed.
Lemma lem1590882 (x : real) (h1 : term48 x) : term48 x.
Proof. exact (h1). Qed.
Lemma lem1590883 (h1 : term30) : term112.
Proof. exact (proj2 (@lem1590776 h1)). Qed.
Lemma lem1590884 (h1 : term30) : term107.
Proof. exact (proj1 (@lem1590776 h1)). Qed.
Lemma lem1590885 (x : real) (h1 : term44 x) : term44 x.
Proof. exact (h1). Qed.
Lemma lem1590886 (x : real) (h1 : term41 x) : term41 x.
Proof. exact (h1). Qed.
Lemma lem1590887 (x : real) (h1 : term44 x) : term37 x.
Proof. exact (proj2 (@lem1590885 x h1)). Qed.
Lemma lem1590888 (x : real) (h1 : term44 x) : term12 x.
Proof. exact (proj1 (@lem1590885 x h1)). Qed.
Lemma lem1590893 (x : real) (h1 : term41 x) : term16 x.
Proof. exact (proj2 (@lem1590886 x h1)). Qed.
Lemma lem1590894 (x : real) (h1 : term41 x) : term35 x.
Proof. exact (proj1 (@lem1590886 x h1)). Qed.
Lemma lem1590936 (x : real) (h1 : term2 x) : term2 x.
Proof. exact (h1). Qed.
Lemma lem1590957 (x : real) : (term100 x) = (term100 x).
Proof. exact (eq_refl (term100 x)). Qed.
Lemma lem1590958 : term94 = term94.
Proof. exact (fun_ext (fun x : real => @lem1590957 x)). Qed.
Lemma lem1590959 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1590961 : term112 = term112.
Proof. exact (MK_COMB (@lem1590959) (@lem1590958)). Qed.
Lemma lem1590962 (h1 : term30) : term112.
Proof. exact (EQ_MP (@lem1590961) (@lem1590883 h1)). Qed.
Lemma lem1590974 (x : real) (h1 : term9 = (real_inv x)) : term9 = (real_inv x).
Proof. exact (h1). Qed.
Lemma lem1591012 (x : real) (h1 : term2 x) : term2 x.
Proof. exact (h1). Qed.
Lemma lem1591020 (x : real) : (term96 x) = (term96 x).
Proof. exact (eq_refl (term96 x)). Qed.
Lemma lem1591021 : term93 = term93.
Proof. exact (fun_ext (fun x : real => @lem1591020 x)). Qed.
Lemma lem1591022 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1591024 : term107 = term107.
Proof. exact (MK_COMB (@lem1591022) (@lem1591021)). Qed.
Lemma lem1591025 (h1 : term30) : term107.
Proof. exact (EQ_MP (@lem1591024) (@lem1590884 h1)). Qed.
Lemma lem1591050 (x : real) (h1 : term9 = x) : term9 = x.
Proof. exact (h1). Qed.
Lemma lem1591060 (_25102 : real) (h1 : term30) : term99 _25102.
Proof. exact (@lem1590962 h1 _25102). Qed.
Lemma lem1591061 (_25102 : real) : (term99 _25102) = (term100 _25102).
Proof. exact (eq_refl (term99 _25102)). Qed.
Lemma lem1591069 (_25105 : real) (h1 : term30) : term95 _25105.
Proof. exact (@lem1591025 h1 _25105). Qed.
Lemma lem1591070 (_25105 : real) : (term95 _25105) = (term96 _25105).
Proof. exact (eq_refl (term95 _25105)). Qed.
Lemma lem1591088 (x : real) (h1 : term44 x) : term114 x.
Proof. exact (proj1 (@lem1590887 x h1)). Qed.
Lemma lem1591092 (x : real) (h1 : term2 x) : term2 x.
Proof. exact (h1). Qed.
Lemma lem1591104 (_25102 : real) (h1 : term30) : term100 _25102.
Proof. exact (EQ_MP (@lem1591061 _25102) (@lem1591060 _25102 h1)). Qed.
Lemma lem1591108 (x : real) (h1 : term44 x) : term115 x.
Proof. exact (proj2 (@lem1590887 x h1)). Qed.
Lemma lem1591110 (x : real) (h1 : term9 = (real_inv x)) : term9 = (real_inv x).
Proof. exact (h1). Qed.
Lemma lem1591124 (x : real) (h1 : term41 x) : term114 x.
Proof. exact (proj1 (@lem1590894 x h1)). Qed.
Lemma lem1591128 (x : real) (h1 : term2 x) : term2 x.
Proof. exact (h1). Qed.
Lemma lem1591144 (x : real) (h1 : term41 x) : term116 x.
Proof. exact (proj2 (@lem1590894 x h1)). Qed.
Lemma lem1591146 (x : real) (h1 : term9 = x) : term9 = x.
Proof. exact (h1). Qed.
Lemma lem1591147 (x : real) (h1 : term9 = x) : x = term9.
Proof. exact (SYM (@lem1591146 x h1)). Qed.
Lemma lem1591175 (_25105 : real) (h1 : term30) : term96 _25105.
Proof. exact (EQ_MP (@lem1591070 _25105) (@lem1591069 _25105 h1)). Qed.
Lemma lem1591203 : term117 = term117.
Proof. exact (eq_refl term117). Qed.
Lemma lem1591204 (x : real) (h1 : term9 = x) : (term118 x) = term119.
Proof. exact (MK_COMB (@lem1591203) (@lem1591147 x h1)). Qed.
Lemma lem1591205 : term119 = term120.
Proof. exact (eq_refl term119). Qed.
Lemma lem1591206 (x : real) : (term121 x) = (term121 x).
Proof. exact (eq_refl (term121 x)). Qed.
Lemma lem1591207 (x : real) : ((term118 x) = term119) = ((term118 x) = term120).
Proof. exact (MK_COMB (@lem1591206 x) (@lem1591205)). Qed.
Lemma lem1591208 (x : real) : (term118 x) = (term116 x).
Proof. exact (eq_refl (term118 x)). Qed.
Lemma lem1591209 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1591210 (x : real) : (term121 x) = (term122 x).
Proof. exact (MK_COMB (@lem1591209) (@lem1591208 x)). Qed.
Lemma lem1591211 : term120 = term120.
Proof. exact (eq_refl term120). Qed.
Lemma lem1591212 (x : real) : ((term118 x) = term120) = ((term116 x) = term120).
Proof. exact (MK_COMB (@lem1591210 x) (@lem1591211)). Qed.
Lemma lem1591213 (x : real) : ((term118 x) = term119) = ((term116 x) = term120).
Proof. exact (TRANS (@lem1591207 x) (@lem1591212 x)). Qed.
Lemma lem1591214 (x : real) (h1 : term9 = x) : (term116 x) = term120.
Proof. exact (EQ_MP (@lem1591213 x) (@lem1591204 x h1)). Qed.
Lemma lem1591215 (x : real) (h1 : term41 x) (h2 : term9 = x) : term120.
Proof. exact (EQ_MP (@lem1591214 x h2) (@lem1591144 x h1)). Qed.
Lemma lem1591264 (x : real) (h1 : term2 x) : term2 x.
Proof. exact (h1). Qed.
Lemma lem1591265 (x : real) (h1 : term2 x) : term123 x.
Proof. exact (fun h0 : term114 x => @lem1591264 x h1). Qed.
Lemma lem1591267 (p : Prop) : (term124 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1591268 (x : real) : (term123 x) = (term2 x).
Proof. exact (@lem1591267 (term2 x)). Qed.
Lemma lem1591269 (x : real) (h1 : term2 x) : term2 x.
Proof. exact (EQ_MP (@lem1591268 x) (@lem1591265 x h1)). Qed.
Lemma lem1591272 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1591274 (x : real) : (term114 x) = (term125 x).
Proof. exact (@lem1591272 (term2 x)). Qed.
Lemma lem1591277 (x : real) (h1 : term44 x) : term125 x.
Proof. exact (EQ_MP (@lem1591274 x) (@lem1591088 x h1)). Qed.
Lemma lem1591280 (x : real) (h1 : term44 x) (h2 : term2 x) : False.
Proof. exact (@lem1591277 x h1 (@lem1591269 x h2)). Qed.
Lemma lem1591281 (x : real) (h1 : term44 x) (h2 : term2 x) : term126.
Proof. exact (fun h0 : ~ False => @lem1591280 x h1 h2). Qed.
Lemma lem1591283 (p : Prop) : (term124 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1591284 : term126 = False.
Proof. exact (@lem1591283 False). Qed.
Lemma lem1591285 (x : real) (h1 : term44 x) (h2 : term2 x) : False.
Proof. exact (EQ_MP (@lem1591284) (@lem1591281 x h1 h2)). Qed.
Lemma lem1591330 (x : real) (y : real) (z : real) : term127 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem1591334 (x : real) (h1 : term9 = (real_inv x)) : term9 = (real_inv x).
Proof. exact (h1). Qed.
Lemma lem1591335 (x : real) (h1 : term9 = (real_inv x)) : term128 x.
Proof. exact (fun h0 : term116 x => @lem1591334 x h1). Qed.
Lemma lem1591337 (p : Prop) : (term124 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1591338 (x : real) : (term128 x) = (term9 = (real_inv x)).
Proof. exact (@lem1591337 (term9 = (real_inv x))). Qed.
Lemma lem1591339 (x : real) (h1 : term9 = (real_inv x)) : term9 = (real_inv x).
Proof. exact (EQ_MP (@lem1591338 x) (@lem1591335 x h1)). Qed.
Lemma lem1591341 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1591342 : term9 = term9.
Proof. exact (@lem1591341 term9). Qed.
Lemma lem1591343 : term129.
Proof. exact (fun h0 : term130 => @lem1591342). Qed.
Lemma lem1591345 (p : Prop) : (term124 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1591346 : term129 = (term9 = term9).
Proof. exact (@lem1591345 (term9 = term9)). Qed.
Lemma lem1591347 : term9 = term9.
Proof. exact (EQ_MP (@lem1591346) (@lem1591343)). Qed.
Lemma lem1591365 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1591366 (y : real) (x : real) (z : real) : (term131 x y z) = (term132 y x z).
Proof. exact (@lem1591365 (y = z) (term133 x z)). Qed.
Lemma lem1591376 (x : real) (y : real) : (term134 x y) = (term134 x y).
Proof. exact (eq_refl (term134 x y)). Qed.
Lemma lem1591377 (y : real) (x : real) (z : real) : (term127 x y z) = (term135 y x z).
Proof. exact (MK_COMB (@lem1591376 x y) (@lem1591366 y x z)). Qed.
Lemma lem1591381 (q : Prop) (p : Prop) (r : Prop) : (term136 p q r) = (term136 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1591382 (y : real) (x : real) (z : real) : (term135 y x z) = (term137 y x z).
Proof. exact (@lem1591381 (y = z) (term133 x y) (term133 x z)). Qed.
Lemma lem1591404 (y : real) (x : real) (z : real) : (term127 x y z) = (term137 y x z).
Proof. exact (TRANS (@lem1591377 y x z) (@lem1591382 y x z)). Qed.
Lemma lem1591405 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1591406 (y : real) (x : real) (z : real) : (term138 x y z) = (term139 y x z).
Proof. exact (MK_COMB (@lem1591405) (@lem1591404 y x z)). Qed.
Lemma lem1591428 (y : real) (x : real) (z : real) : (term137 y x z) = (term137 y x z).
Proof. exact (eq_refl (term137 y x z)). Qed.
Lemma lem1591429 (y : real) (x : real) (z : real) : ((term127 x y z) = (term137 y x z)) = ((term137 y x z) = (term137 y x z)).
Proof. exact (MK_COMB (@lem1591406 y x z) (@lem1591428 y x z)). Qed.
Lemma lem1591431 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1591432 (x : Prop) : (x = x) = True.
Proof. exact (@lem1591431 Prop x). Qed.
Lemma lem1591433 (y : real) (x : real) (z : real) : ((term137 y x z) = (term137 y x z)) = True.
Proof. exact (@lem1591432 (term137 y x z)). Qed.
Lemma lem1591434 (y : real) (x : real) (z : real) : ((term127 x y z) = (term137 y x z)) = True.
Proof. exact (TRANS (@lem1591429 y x z) (@lem1591433 y x z)). Qed.
Lemma lem1591435 (y : real) (x : real) (z : real) : True = ((term127 x y z) = (term137 y x z)).
Proof. exact (SYM (@lem1591434 y x z)). Qed.
Lemma lem1591436 (y : real) (x : real) (z : real) : (term127 x y z) = (term137 y x z).
Proof. exact (EQ_MP (@lem1591435 y x z) (@lem0)). Qed.
Lemma lem1591437 (y : real) (x : real) (z : real) : term137 y x z.
Proof. exact (EQ_MP (@lem1591436 y x z) (@lem1591330 x y z)). Qed.
Lemma lem1591439 (b : Prop) (a : Prop) : (a \/ b) = (term140 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1591440 (x : real) (y : real) (z : real) : (term137 y x z) = (term141 x y z).
Proof. exact (@lem1591439 (term142 y x z) (y = z)). Qed.
Lemma lem1591442 (a : Prop) (b : Prop) : (term143 a b) = (term144 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1591443 (y : real) (x : real) (z : real) : (term145 y x z) = (term146 y x z).
Proof. exact (@lem1591442 (term133 x y) (term133 x z)). Qed.
Lemma lem1591445 (a : Prop) : (term147 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1591446 (x : real) (y : real) : (term148 x y) = (x = y).
Proof. exact (@lem1591445 (x = y)). Qed.
Lemma lem1591447 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1591448 (x : real) (y : real) : (term149 x y) = (term150 x y).
Proof. exact (MK_COMB (@lem1591447) (@lem1591446 x y)). Qed.
Lemma lem1591450 (a : Prop) : (term147 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1591451 (x : real) (z : real) : (term148 x z) = (x = z).
Proof. exact (@lem1591450 (x = z)). Qed.
Lemma lem1591452 (y : real) (x : real) (z : real) : (term146 y x z) = (term151 y x z).
Proof. exact (MK_COMB (@lem1591448 x y) (@lem1591451 x z)). Qed.
Lemma lem1591453 (y : real) (x : real) (z : real) : (term145 y x z) = (term151 y x z).
Proof. exact (TRANS (@lem1591443 y x z) (@lem1591452 y x z)). Qed.
Lemma lem1591454 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1591455 (y : real) (x : real) (z : real) : (term152 y x z) = (term153 y x z).
Proof. exact (MK_COMB (@lem1591454) (@lem1591453 y x z)). Qed.
Lemma lem1591456 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1591457 (x : real) (y : real) (z : real) : (term141 x y z) = (term154 x y z).
Proof. exact (MK_COMB (@lem1591455 y x z) (@lem1591456 y z)). Qed.
Lemma lem1591458 (x : real) (y : real) (z : real) : (term137 y x z) = (term154 x y z).
Proof. exact (TRANS (@lem1591440 x y z) (@lem1591457 x y z)). Qed.
Lemma lem1591460 (x : real) (h1 : term9 = (real_inv x)) : term155 x.
Proof. exact (conj (@lem1591339 x h1) (@lem1591347)). Qed.
Lemma lem1591462 (x : real) (y : real) (z : real) : term154 x y z.
Proof. exact (EQ_MP (@lem1591458 x y z) (@lem1591437 y x z)). Qed.
Lemma lem1591463 (x : real) : term156 x.
Proof. exact (@lem1591462 term9 (real_inv x) term9). Qed.
Lemma lem1591466 (x : real) (h1 : term9 = (real_inv x)) : (real_inv x) = term9.
Proof. exact (@lem1591463 x (@lem1591460 x h1)). Qed.
Lemma lem1591467 (x : real) (h1 : term9 = (real_inv x)) : term157 x.
Proof. exact (fun h0 : term158 x => @lem1591466 x h1). Qed.
Lemma lem1591469 (p : Prop) : (term124 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1591470 (x : real) : (term157 x) = ((real_inv x) = term9).
Proof. exact (@lem1591469 ((real_inv x) = term9)). Qed.
Lemma lem1591471 (x : real) (h1 : term9 = (real_inv x)) : (real_inv x) = term9.
Proof. exact (EQ_MP (@lem1591470 x) (@lem1591467 x h1)). Qed.
Lemma lem1591477 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1591478 (_25102 : real) : (term100 _25102) = (term159 _25102).
Proof. exact (@lem1591477 (_25102 = term9) (term158 _25102)). Qed.
Lemma lem1591488 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1591489 (_25102 : real) : (term160 _25102) = (term161 _25102).
Proof. exact (MK_COMB (@lem1591488) (@lem1591478 _25102)). Qed.
Lemma lem1591499 (_25102 : real) : (term159 _25102) = (term159 _25102).
Proof. exact (eq_refl (term159 _25102)). Qed.
Lemma lem1591500 (_25102 : real) : ((term100 _25102) = (term159 _25102)) = ((term159 _25102) = (term159 _25102)).
Proof. exact (MK_COMB (@lem1591489 _25102) (@lem1591499 _25102)). Qed.
Lemma lem1591502 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1591503 (x : Prop) : (x = x) = True.
Proof. exact (@lem1591502 Prop x). Qed.
Lemma lem1591504 (_25102 : real) : ((term159 _25102) = (term159 _25102)) = True.
Proof. exact (@lem1591503 (term159 _25102)). Qed.
Lemma lem1591505 (_25102 : real) : ((term100 _25102) = (term159 _25102)) = True.
Proof. exact (TRANS (@lem1591500 _25102) (@lem1591504 _25102)). Qed.
Lemma lem1591506 (_25102 : real) : True = ((term100 _25102) = (term159 _25102)).
Proof. exact (SYM (@lem1591505 _25102)). Qed.
Lemma lem1591507 (_25102 : real) : (term100 _25102) = (term159 _25102).
Proof. exact (EQ_MP (@lem1591506 _25102) (@lem0)). Qed.
Lemma lem1591508 (_25102 : real) (h1 : term30) : term159 _25102.
Proof. exact (EQ_MP (@lem1591507 _25102) (@lem1591104 _25102 h1)). Qed.
Lemma lem1591510 (b : Prop) (a : Prop) : (a \/ b) = (term140 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1591511 (_25102 : real) : (term159 _25102) = (term162 _25102).
Proof. exact (@lem1591510 (term158 _25102) (_25102 = term9)). Qed.
Lemma lem1591513 (a : Prop) : (term147 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1591514 (_25102 : real) : (term163 _25102) = ((real_inv _25102) = term9).
Proof. exact (@lem1591513 ((real_inv _25102) = term9)). Qed.
Lemma lem1591515 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1591516 (_25102 : real) : (term164 _25102) = (term165 _25102).
Proof. exact (MK_COMB (@lem1591515) (@lem1591514 _25102)). Qed.
Lemma lem1591517 (_25102 : real) : (_25102 = term9) = (_25102 = term9).
Proof. exact (eq_refl (_25102 = term9)). Qed.
Lemma lem1591518 (_25102 : real) : (term162 _25102) = (term166 _25102).
Proof. exact (MK_COMB (@lem1591516 _25102) (@lem1591517 _25102)). Qed.
Lemma lem1591519 (_25102 : real) : (term159 _25102) = (term166 _25102).
Proof. exact (TRANS (@lem1591511 _25102) (@lem1591518 _25102)). Qed.
Lemma lem1591522 (_25102 : real) (h1 : term30) : term166 _25102.
Proof. exact (EQ_MP (@lem1591519 _25102) (@lem1591508 _25102 h1)). Qed.
Lemma lem1591523 (x : real) (h1 : term30) : term166 x.
Proof. exact (@lem1591522 x h1). Qed.
Lemma lem1591526 (x : real) (h1 : term30) (h2 : term9 = (real_inv x)) : x = term9.
Proof. exact (@lem1591523 x h1 (@lem1591471 x h2)). Qed.
Lemma lem1591527 (x : real) (h1 : term30) (h2 : term9 = (real_inv x)) : term167 x.
Proof. exact (fun h0 : term168 x => @lem1591526 x h1 h2). Qed.
Lemma lem1591529 (p : Prop) : (term124 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1591530 (x : real) : (term167 x) = (x = term9).
Proof. exact (@lem1591529 (x = term9)). Qed.
Lemma lem1591531 (x : real) (h1 : term30) (h2 : term9 = (real_inv x)) : x = term9.
Proof. exact (EQ_MP (@lem1591530 x) (@lem1591527 x h1 h2)). Qed.
Lemma lem1591533 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1591534 (x : real) : term169 x.
Proof. exact (fun h0 : term170 x => @lem1591533 x). Qed.
Lemma lem1591536 (p : Prop) : (term124 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1591537 (x : real) : (term169 x) = (x = x).
Proof. exact (@lem1591536 (x = x)). Qed.
Lemma lem1591538 (x : real) : x = x.
Proof. exact (EQ_MP (@lem1591537 x) (@lem1591534 x)). Qed.
Lemma lem1591539 (x : real) (h1 : term30) (h2 : term9 = (real_inv x)) : term171 x.
Proof. exact (conj (@lem1591531 x h1 h2) (@lem1591538 x)). Qed.
Lemma lem1591541 (x : real) (y : real) (z : real) : term154 x y z.
Proof. exact (EQ_MP (@lem1591458 x y z) (@lem1591437 y x z)). Qed.
Lemma lem1591542 (x : real) : term172 x.
Proof. exact (@lem1591541 x term9 x). Qed.
Lemma lem1591545 (x : real) (h1 : term30) (h2 : term9 = (real_inv x)) : term9 = x.
Proof. exact (@lem1591542 x (@lem1591539 x h1 h2)). Qed.
Lemma lem1591546 (x : real) (h1 : term30) (h2 : term9 = (real_inv x)) : term173 x.
Proof. exact (fun h0 : term115 x => @lem1591545 x h1 h2). Qed.
Lemma lem1591548 (p : Prop) : (term124 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1591549 (x : real) : (term173 x) = (term9 = x).
Proof. exact (@lem1591548 (term9 = x)). Qed.
Lemma lem1591550 (x : real) (h1 : term30) (h2 : term9 = (real_inv x)) : term9 = x.
Proof. exact (EQ_MP (@lem1591549 x) (@lem1591546 x h1 h2)). Qed.
Lemma lem1591553 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1591555 (x : real) : (term115 x) = (term174 x).
Proof. exact (@lem1591553 (term9 = x)). Qed.
Lemma lem1591558 (x : real) (h1 : term44 x) : term174 x.
Proof. exact (EQ_MP (@lem1591555 x) (@lem1591108 x h1)). Qed.
Lemma lem1591561 (x : real) (h1 : term30) (h2 : term44 x) (h3 : term9 = (real_inv x)) : False.
Proof. exact (@lem1591558 x h2 (@lem1591550 x h1 h3)). Qed.
Lemma lem1591562 (x : real) (h1 : term30) (h2 : term44 x) (h3 : term9 = (real_inv x)) : term126.
Proof. exact (fun h0 : ~ False => @lem1591561 x h1 h2 h3). Qed.
Lemma lem1591564 (p : Prop) : (term124 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1591565 : term126 = False.
Proof. exact (@lem1591564 False). Qed.
Lemma lem1591566 (x : real) (h1 : term30) (h2 : term44 x) (h3 : term9 = (real_inv x)) : False.
Proof. exact (EQ_MP (@lem1591565) (@lem1591562 x h1 h2 h3)). Qed.
Lemma lem1591615 (x : real) (h1 : term2 x) : term2 x.
Proof. exact (h1). Qed.
Lemma lem1591616 (x : real) (h1 : term2 x) : term123 x.
Proof. exact (fun h0 : term114 x => @lem1591615 x h1). Qed.
Lemma lem1591618 (p : Prop) : (term124 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1591619 (x : real) : (term123 x) = (term2 x).
Proof. exact (@lem1591618 (term2 x)). Qed.
Lemma lem1591620 (x : real) (h1 : term2 x) : term2 x.
Proof. exact (EQ_MP (@lem1591619 x) (@lem1591616 x h1)). Qed.
Lemma lem1591623 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1591625 (x : real) : (term114 x) = (term125 x).
Proof. exact (@lem1591623 (term2 x)). Qed.
Lemma lem1591628 (x : real) (h1 : term41 x) : term125 x.
Proof. exact (EQ_MP (@lem1591625 x) (@lem1591124 x h1)). Qed.
Lemma lem1591631 (x : real) (h1 : term41 x) (h2 : term2 x) : False.
Proof. exact (@lem1591628 x h1 (@lem1591620 x h2)). Qed.
Lemma lem1591632 (x : real) (h1 : term41 x) (h2 : term2 x) : term126.
Proof. exact (fun h0 : ~ False => @lem1591631 x h1 h2). Qed.
Lemma lem1591634 (p : Prop) : (term124 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1591635 : term126 = False.
Proof. exact (@lem1591634 False). Qed.
Lemma lem1591636 (x : real) (h1 : term41 x) (h2 : term2 x) : False.
Proof. exact (EQ_MP (@lem1591635) (@lem1591632 x h1 h2)). Qed.
Lemma lem1591681 (x : real) (y : real) (z : real) : term127 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem1591685 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1591686 : term9 = term9.
Proof. exact (@lem1591685 term9). Qed.
Lemma lem1591687 : term129.
Proof. exact (fun h0 : term130 => @lem1591686). Qed.
Lemma lem1591689 (p : Prop) : (term124 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1591690 : term129 = (term9 = term9).
Proof. exact (@lem1591689 (term9 = term9)). Qed.
Lemma lem1591691 : term9 = term9.
Proof. exact (EQ_MP (@lem1591690) (@lem1591687)). Qed.
Lemma lem1591693 (b : Prop) (a : Prop) : (a \/ b) = (term140 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1591694 (_25105 : real) : (term96 _25105) = (term175 _25105).
Proof. exact (@lem1591693 (term168 _25105) ((real_inv _25105) = term9)). Qed.
Lemma lem1591696 (a : Prop) : (term147 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1591697 (_25105 : real) : (term176 _25105) = (_25105 = term9).
Proof. exact (@lem1591696 (_25105 = term9)). Qed.
Lemma lem1591698 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1591699 (_25105 : real) : (term177 _25105) = (term178 _25105).
Proof. exact (MK_COMB (@lem1591698) (@lem1591697 _25105)). Qed.
Lemma lem1591700 (_25105 : real) : ((real_inv _25105) = term9) = ((real_inv _25105) = term9).
Proof. exact (eq_refl ((real_inv _25105) = term9)). Qed.
Lemma lem1591701 (_25105 : real) : (term175 _25105) = (term179 _25105).
Proof. exact (MK_COMB (@lem1591699 _25105) (@lem1591700 _25105)). Qed.
Lemma lem1591702 (_25105 : real) : (term96 _25105) = (term179 _25105).
Proof. exact (TRANS (@lem1591694 _25105) (@lem1591701 _25105)). Qed.
Lemma lem1591705 (_25105 : real) (h1 : term30) : term179 _25105.
Proof. exact (EQ_MP (@lem1591702 _25105) (@lem1591175 _25105 h1)). Qed.
Lemma lem1591706 (h1 : term30) : term180.
Proof. exact (@lem1591705 term9 h1). Qed.
Lemma lem1591709 (h1 : term30) : term181 = term9.
Proof. exact (@lem1591706 h1 (@lem1591691)). Qed.
Lemma lem1591710 (h1 : term30) : term182.
Proof. exact (fun h0 : term183 => @lem1591709 h1). Qed.
Lemma lem1591712 (p : Prop) : (term124 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1591713 : term182 = (term181 = term9).
Proof. exact (@lem1591712 (term181 = term9)). Qed.
Lemma lem1591714 (h1 : term30) : term181 = term9.
Proof. exact (EQ_MP (@lem1591713) (@lem1591710 h1)). Qed.
Lemma lem1591716 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1591717 : term181 = term181.
Proof. exact (@lem1591716 term181). Qed.
Lemma lem1591718 : term184.
Proof. exact (fun h0 : term185 => @lem1591717). Qed.
Lemma lem1591720 (p : Prop) : (term124 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1591721 : term184 = (term181 = term181).
Proof. exact (@lem1591720 (term181 = term181)). Qed.
Lemma lem1591722 : term181 = term181.
Proof. exact (EQ_MP (@lem1591721) (@lem1591718)). Qed.
Lemma lem1591740 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1591741 (y : real) (x : real) (z : real) : (term131 x y z) = (term132 y x z).
Proof. exact (@lem1591740 (y = z) (term133 x z)). Qed.
Lemma lem1591751 (x : real) (y : real) : (term134 x y) = (term134 x y).
Proof. exact (eq_refl (term134 x y)). Qed.
Lemma lem1591752 (y : real) (x : real) (z : real) : (term127 x y z) = (term135 y x z).
Proof. exact (MK_COMB (@lem1591751 x y) (@lem1591741 y x z)). Qed.
Lemma lem1591756 (q : Prop) (p : Prop) (r : Prop) : (term136 p q r) = (term136 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1591757 (y : real) (x : real) (z : real) : (term135 y x z) = (term137 y x z).
Proof. exact (@lem1591756 (y = z) (term133 x y) (term133 x z)). Qed.
Lemma lem1591779 (y : real) (x : real) (z : real) : (term127 x y z) = (term137 y x z).
Proof. exact (TRANS (@lem1591752 y x z) (@lem1591757 y x z)). Qed.
Lemma lem1591780 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1591781 (y : real) (x : real) (z : real) : (term138 x y z) = (term139 y x z).
Proof. exact (MK_COMB (@lem1591780) (@lem1591779 y x z)). Qed.
Lemma lem1591803 (y : real) (x : real) (z : real) : (term137 y x z) = (term137 y x z).
Proof. exact (eq_refl (term137 y x z)). Qed.
Lemma lem1591804 (y : real) (x : real) (z : real) : ((term127 x y z) = (term137 y x z)) = ((term137 y x z) = (term137 y x z)).
Proof. exact (MK_COMB (@lem1591781 y x z) (@lem1591803 y x z)). Qed.
Lemma lem1591806 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1591807 (x : Prop) : (x = x) = True.
Proof. exact (@lem1591806 Prop x). Qed.
Lemma lem1591808 (y : real) (x : real) (z : real) : ((term137 y x z) = (term137 y x z)) = True.
Proof. exact (@lem1591807 (term137 y x z)). Qed.
Lemma lem1591809 (y : real) (x : real) (z : real) : ((term127 x y z) = (term137 y x z)) = True.
Proof. exact (TRANS (@lem1591804 y x z) (@lem1591808 y x z)). Qed.
Lemma lem1591810 (y : real) (x : real) (z : real) : True = ((term127 x y z) = (term137 y x z)).
Proof. exact (SYM (@lem1591809 y x z)). Qed.
Lemma lem1591811 (y : real) (x : real) (z : real) : (term127 x y z) = (term137 y x z).
Proof. exact (EQ_MP (@lem1591810 y x z) (@lem0)). Qed.
Lemma lem1591812 (y : real) (x : real) (z : real) : term137 y x z.
Proof. exact (EQ_MP (@lem1591811 y x z) (@lem1591681 x y z)). Qed.
Lemma lem1591814 (b : Prop) (a : Prop) : (a \/ b) = (term140 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1591815 (x : real) (y : real) (z : real) : (term137 y x z) = (term141 x y z).
Proof. exact (@lem1591814 (term142 y x z) (y = z)). Qed.
Lemma lem1591817 (a : Prop) (b : Prop) : (term143 a b) = (term144 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1591818 (y : real) (x : real) (z : real) : (term145 y x z) = (term146 y x z).
Proof. exact (@lem1591817 (term133 x y) (term133 x z)). Qed.
Lemma lem1591820 (a : Prop) : (term147 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1591821 (x : real) (y : real) : (term148 x y) = (x = y).
Proof. exact (@lem1591820 (x = y)). Qed.
Lemma lem1591822 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1591823 (x : real) (y : real) : (term149 x y) = (term150 x y).
Proof. exact (MK_COMB (@lem1591822) (@lem1591821 x y)). Qed.
Lemma lem1591825 (a : Prop) : (term147 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1591826 (x : real) (z : real) : (term148 x z) = (x = z).
Proof. exact (@lem1591825 (x = z)). Qed.
Lemma lem1591827 (y : real) (x : real) (z : real) : (term146 y x z) = (term151 y x z).
Proof. exact (MK_COMB (@lem1591823 x y) (@lem1591826 x z)). Qed.
Lemma lem1591828 (y : real) (x : real) (z : real) : (term145 y x z) = (term151 y x z).
Proof. exact (TRANS (@lem1591818 y x z) (@lem1591827 y x z)). Qed.
Lemma lem1591829 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1591830 (y : real) (x : real) (z : real) : (term152 y x z) = (term153 y x z).
Proof. exact (MK_COMB (@lem1591829) (@lem1591828 y x z)). Qed.
Lemma lem1591831 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1591832 (x : real) (y : real) (z : real) : (term141 x y z) = (term154 x y z).
Proof. exact (MK_COMB (@lem1591830 y x z) (@lem1591831 y z)). Qed.
Lemma lem1591833 (x : real) (y : real) (z : real) : (term137 y x z) = (term154 x y z).
Proof. exact (TRANS (@lem1591815 x y z) (@lem1591832 x y z)). Qed.
Lemma lem1591835 (h1 : term30) : term186.
Proof. exact (conj (@lem1591714 h1) (@lem1591722)). Qed.
Lemma lem1591837 (x : real) (y : real) (z : real) : term154 x y z.
Proof. exact (EQ_MP (@lem1591833 x y z) (@lem1591812 y x z)). Qed.
Lemma lem1591838 : term187.
Proof. exact (@lem1591837 term181 term9 term181). Qed.
Lemma lem1591841 (h1 : term30) : term9 = term181.
Proof. exact (@lem1591838 (@lem1591835 h1)). Qed.
Lemma lem1591842 (h1 : term30) : term188.
Proof. exact (fun h0 : term120 => @lem1591841 h1). Qed.
Lemma lem1591844 (p : Prop) : (term124 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1591845 : term188 = (term9 = term181).
Proof. exact (@lem1591844 (term9 = term181)). Qed.
Lemma lem1591846 (h1 : term30) : term9 = term181.
Proof. exact (EQ_MP (@lem1591845) (@lem1591842 h1)). Qed.
Lemma lem1591849 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1591851 : term120 = term189.
Proof. exact (@lem1591849 (term9 = term181)). Qed.
Lemma lem1591854 (x : real) (h1 : term41 x) (h2 : term9 = x) : term189.
Proof. exact (EQ_MP (@lem1591851) (@lem1591215 x h1 h2)). Qed.
Lemma lem1591857 (x : real) (h1 : term30) (h2 : term41 x) (h3 : term9 = x) : False.
Proof. exact (@lem1591854 x h2 h3 (@lem1591846 h1)). Qed.
Lemma lem1591858 (x : real) (h1 : term30) (h2 : term41 x) (h3 : term9 = x) : term126.
Proof. exact (fun h0 : ~ False => @lem1591857 x h1 h2 h3). Qed.
Lemma lem1591860 (p : Prop) : (term124 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1591861 : term126 = False.
Proof. exact (@lem1591860 False). Qed.
Lemma lem1591863 (x : real) (h1 : term30) (h2 : term41 x) (h3 : term9 = x) : False.
Proof. exact (EQ_MP (@lem1591861) (@lem1591858 x h1 h2 h3)). Qed.
Lemma lem1591864 (x : real) (h1 : term30) (h2 : term41 x) (h3 : term9 = x) : (term9 = x) = False.
Proof. exact (prop_ext (fun h4 : term9 = x => @lem1591863 x h1 h2 h3) (fun h4 : False => @lem1591146 x h3)). Qed.
Lemma lem1591865 (x : real) (h1 : term30) (h2 : term41 x) (h3 : term9 = x) : False.
Proof. exact (EQ_MP (@lem1591864 x h1 h2 h3) (@lem1591146 x h3)). Qed.
Lemma lem1591866 (x : real) (h1 : term41 x) (h2 : term2 x) : (term2 x) = False.
Proof. exact (prop_ext (fun h3 : term2 x => @lem1591636 x h1 h2) (fun h3 : False => @lem1591128 x h2)). Qed.
Lemma lem1591867 (x : real) (h1 : term41 x) (h2 : term2 x) : False.
Proof. exact (EQ_MP (@lem1591866 x h1 h2) (@lem1591128 x h2)). Qed.
Lemma lem1591868 (x : real) (h1 : term30) (h2 : term44 x) (h3 : term9 = (real_inv x)) : (term9 = (real_inv x)) = False.
Proof. exact (prop_ext (fun h4 : term9 = (real_inv x) => @lem1591566 x h1 h2 h3) (fun h4 : False => @lem1591110 x h3)). Qed.
Lemma lem1591869 (x : real) (h1 : term30) (h2 : term44 x) (h3 : term9 = (real_inv x)) : False.
Proof. exact (EQ_MP (@lem1591868 x h1 h2 h3) (@lem1591110 x h3)). Qed.
Lemma lem1591870 (x : real) (h1 : term44 x) (h2 : term2 x) : (term2 x) = False.
Proof. exact (prop_ext (fun h3 : term2 x => @lem1591285 x h1 h2) (fun h3 : False => @lem1591092 x h2)). Qed.
Lemma lem1591871 (x : real) (h1 : term44 x) (h2 : term2 x) : False.
Proof. exact (EQ_MP (@lem1591870 x h1 h2) (@lem1591092 x h2)). Qed.
Lemma lem1591872 (x : real) (h1 : term30) (h2 : term41 x) (h3 : term9 = x) : (term9 = x) = False.
Proof. exact (prop_ext (fun h4 : term9 = x => @lem1591865 x h1 h2 h3) (fun h4 : False => @lem1591050 x h3)). Qed.
Lemma lem1591873 (x : real) (h1 : term30) (h2 : term41 x) (h3 : term9 = x) : False.
Proof. exact (EQ_MP (@lem1591872 x h1 h2 h3) (@lem1591050 x h3)). Qed.
Lemma lem1591874 (x : real) (h1 : term41 x) (h2 : term2 x) : (term2 x) = False.
Proof. exact (prop_ext (fun h3 : term2 x => @lem1591867 x h1 h2) (fun h3 : False => @lem1591012 x h2)). Qed.
Lemma lem1591875 (x : real) (h1 : term41 x) (h2 : term2 x) : False.
Proof. exact (EQ_MP (@lem1591874 x h1 h2) (@lem1591012 x h2)). Qed.
Lemma lem1591876 (x : real) (h1 : term30) (h2 : term44 x) (h3 : term9 = (real_inv x)) : (term9 = (real_inv x)) = False.
Proof. exact (prop_ext (fun h4 : term9 = (real_inv x) => @lem1591869 x h1 h2 h3) (fun h4 : False => @lem1590974 x h3)). Qed.
Lemma lem1591877 (x : real) (h1 : term30) (h2 : term44 x) (h3 : term9 = (real_inv x)) : False.
Proof. exact (EQ_MP (@lem1591876 x h1 h2 h3) (@lem1590974 x h3)). Qed.
Lemma lem1591878 (x : real) (h1 : term44 x) (h2 : term2 x) : (term2 x) = False.
Proof. exact (prop_ext (fun h3 : term2 x => @lem1591871 x h1 h2) (fun h3 : False => @lem1590936 x h2)). Qed.
Lemma lem1591879 (x : real) (h1 : term44 x) (h2 : term2 x) : False.
Proof. exact (EQ_MP (@lem1591878 x h1 h2) (@lem1590936 x h2)). Qed.
Lemma lem1591880 (x : real) (h1 : term30) (h2 : term41 x) (h3 : term9 = x) : (term9 = x) = False.
Proof. exact (prop_ext (fun h4 : term9 = x => @lem1591873 x h1 h2 h3) (fun h4 : False => @lem1591050 x h3)). Qed.
Lemma lem1591881 (x : real) (h1 : term30) (h2 : term41 x) (h3 : term9 = x) : False.
Proof. exact (EQ_MP (@lem1591880 x h1 h2 h3) (@lem1591050 x h3)). Qed.
Lemma lem1591882 (x : real) (h1 : term41 x) (h2 : term2 x) : (term2 x) = False.
Proof. exact (prop_ext (fun h3 : term2 x => @lem1591875 x h1 h2) (fun h3 : False => @lem1591012 x h2)). Qed.
Lemma lem1591883 (x : real) (h1 : term41 x) (h2 : term2 x) : False.
Proof. exact (EQ_MP (@lem1591882 x h1 h2) (@lem1591012 x h2)). Qed.
Lemma lem1591884 (x : real) (h1 : term30) (h2 : term44 x) (h3 : term9 = (real_inv x)) : (term9 = (real_inv x)) = False.
Proof. exact (prop_ext (fun h4 : term9 = (real_inv x) => @lem1591877 x h1 h2 h3) (fun h4 : False => @lem1590974 x h3)). Qed.
Lemma lem1591885 (x : real) (h1 : term30) (h2 : term44 x) (h3 : term9 = (real_inv x)) : False.
Proof. exact (EQ_MP (@lem1591884 x h1 h2 h3) (@lem1590974 x h3)). Qed.
Lemma lem1591886 (x : real) (h1 : term44 x) (h2 : term2 x) : (term2 x) = False.
Proof. exact (prop_ext (fun h3 : term2 x => @lem1591879 x h1 h2) (fun h3 : False => @lem1590936 x h2)). Qed.
Lemma lem1591887 (x : real) (h1 : term44 x) (h2 : term2 x) : False.
Proof. exact (EQ_MP (@lem1591886 x h1 h2) (@lem1590936 x h2)). Qed.
Lemma lem1591888 (x : real) (h1 : term30) (h2 : term41 x) : False.
Proof. exact (or_elim (@lem1590893 x h2) (fun h0 : term2 x => @lem1591883 x h2 h0) (fun h0 : term9 = x => @lem1591881 x h1 h2 h0)). Qed.
Lemma lem1591889 (x : real) (h1 : term30) (h2 : term44 x) : False.
Proof. exact (or_elim (@lem1590888 x h2) (fun h0 : term2 x => @lem1591887 x h2 h0) (fun h0 : term9 = (real_inv x) => @lem1591885 x h1 h2 h0)). Qed.
Lemma lem1591890 (x : real) (h1 : term30) (h2 : term48 x) : False.
Proof. exact (or_elim (@lem1590882 x h2) (fun h0 : term44 x => @lem1591889 x h1 h0) (fun h0 : term41 x => @lem1591888 x h1 h0)). Qed.
Lemma lem1591891 (x : real) (h1 : term30) (h2 : term48 x) : (term48 x) = False.
Proof. exact (prop_ext (fun h3 : term48 x => @lem1591890 x h1 h2) (fun h3 : False => @lem1590882 x h2)). Qed.
Lemma lem1591892 (x : real) (h1 : term30) (h2 : term48 x) : False.
Proof. exact (EQ_MP (@lem1591891 x h1 h2) (@lem1590882 x h2)). Qed.
Lemma lem1591893 (h1 : term30) (h2 : term23) : False.
Proof. exact (ex_elim (@lem1590570 h2) (fun x : real => fun h0 : term56 x => @lem1591892 x h1 h0)). Qed.
Lemma lem1591894 (h1 : term23) : term28.
Proof. exact (fun h0 : term30 => @lem1591893 h0 h1). Qed.
Lemma lem1591895 : term28 = term29.
Proof. exact (@lem69 term30). Qed.
Lemma lem1591896 (h1 : term23) : term29.
Proof. exact (EQ_MP (@lem1591895) (@lem1591894 h1)). Qed.
Lemma lem1591897 : term32.
Proof. exact (fun h0 : term23 => @lem1591896 h0). Qed.
Lemma lem1591898 : term24.
Proof. exact (EQ_MP (@lem1590370) (@lem1591897)). Qed.
Lemma lem1591900 : term24.
Proof. exact (@lem1590292 (@lem1591898)). Qed.
Lemma lem1591901 (h1 : term23) : term28.
Proof. exact (@lem1591900 (@lem1590277 h1)). Qed.
Lemma lem1591902 (h1 : term23) : False.
Proof. exact (@lem1591901 h1 (@lem1588944)). Qed.
Lemma lem1591903 (h1 : term23) : term23 = False.
Proof. exact (prop_ext (fun h2 : term23 => @lem1591902 h1) (fun h2 : False => @lem1590277 h1)). Qed.
Lemma lem1591904 (h1 : term23) : False.
Proof. exact (EQ_MP (@lem1591903 h1) (@lem1590277 h1)). Qed.
Lemma lem1591905 : term22.
Proof. exact (fun h0 : term23 => @lem1591904 h0). Qed.
Lemma lem1591906 : term20.
Proof. exact (EQ_MP (@lem1590276) (@lem1591905)). Qed.
Lemma lem1591907 : term19.
Proof. exact (EQ_MP (@lem1590272) (@lem1591906)). Qed.
