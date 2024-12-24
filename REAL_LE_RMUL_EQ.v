Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LE_RMUL_EQ_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import REAL_LE_RCANCEL_IMP_spec.
Require Import REAL_LE_RMUL_spec.
Require Import REAL_LT_IMP_LE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18946_spec.
Require Import thm18947_spec.
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
Lemma lem1599120 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1599121 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1599122 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1599121 t1) (@lem1599120 t1)). Qed.
Lemma lem1599123 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1599122 t1 t2). Qed.
Lemma lem1599124 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1599125 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1599124 t1 t2) (@lem1599123 t1 t2)). Qed.
Lemma lem1599126 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1599125 t1 t2 t3). Qed.
Lemma lem1599127 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1599128 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1599127 t1 t2 t3) (@lem1599126 t1 t2 t3)). Qed.
Lemma lem1599129 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1599128 t1 t2 t3)). Qed.
Lemma lem1599131 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1599132 : term8 = term9.
Proof. exact (@lem1599131 term8). Qed.
Lemma lem1599133 : term9 = term8.
Proof. exact (SYM (@lem1599132)). Qed.
Lemma lem1599134 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1599137 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1599138 : term12.
Proof. exact (fun h0 : term11 => @lem1599137 h0). Qed.
Lemma lem1599139 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1599140 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1599141 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem1599139 h2 (@lem1599140 h1)). Qed.
Lemma lem1599142 (h1 : term11) : term13.
Proof. exact (fun h0 : term12 => @lem1599141 h1 h0). Qed.
Lemma lem1599143 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1599144 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem1599142 h1 (@lem1599143 h2)). Qed.
Lemma lem1599145 (h1 : term12) : term12.
Proof. exact (fun h0 : term11 => @lem1599144 h0 h1). Qed.
Lemma lem1599146 : term14.
Proof. exact (fun h0 : term12 => @lem1599145 h0). Qed.
Lemma lem1599149 : term12.
Proof. exact (@lem1599146 (@lem1599138)). Qed.
Lemma lem1599197 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1599198 : term15 = term16.
Proof. exact (@lem1599197 term17). Qed.
Lemma lem1599215 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem1599216 : term19 = term20.
Proof. exact (MK_COMB (@lem1599215) (@lem1599198)). Qed.
Lemma lem1599219 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem1599220 : term22 = term23.
Proof. exact (MK_COMB (@lem1599219) (@lem1599216)). Qed.
Lemma lem1599223 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1599230 : term11 = term25.
Proof. exact (MK_COMB (@lem1599223) (@lem1599220)). Qed.
Lemma lem1599239 (x : real) (y : real) (z : real) : (term26 x y z) = (term26 x y z).
Proof. exact (eq_refl (term26 x y z)). Qed.
Lemma lem1599240 (x : real) (y : real) : (term27 x y) = (term27 x y).
Proof. exact (fun_ext (fun z : real => @lem1599239 x y z)). Qed.
Lemma lem1599241 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1599242 (x : real) (y : real) : (term28 x y) = (term28 x y).
Proof. exact (MK_COMB (@lem1599241) (@lem1599240 x y)). Qed.
Lemma lem1599243 (x : real) : (term29 x) = (term29 x).
Proof. exact (fun_ext (fun y : real => @lem1599242 x y)). Qed.
Lemma lem1599244 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1599245 (x : real) : (term30 x) = (term30 x).
Proof. exact (MK_COMB (@lem1599244) (@lem1599243 x)). Qed.
Lemma lem1599246 : term31 = term31.
Proof. exact (fun_ext (fun x : real => @lem1599245 x)). Qed.
Lemma lem1599247 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1599248 : term17 = term17.
Proof. exact (MK_COMB (@lem1599247) (@lem1599246)). Qed.
Lemma lem1599249 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1599250 : term16 = term16.
Proof. exact (MK_COMB (@lem1599249) (@lem1599248)). Qed.
Lemma lem1599259 (z : real) (x : real) (y : real) : (term32 z x y) = (term32 z x y).
Proof. exact (eq_refl (term32 z x y)). Qed.
Lemma lem1599260 (x : real) (y : real) : (term33 x y) = (term33 x y).
Proof. exact (fun_ext (fun z : real => @lem1599259 z x y)). Qed.
Lemma lem1599261 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1599262 (x : real) (y : real) : (term34 x y) = (term34 x y).
Proof. exact (MK_COMB (@lem1599261) (@lem1599260 x y)). Qed.
Lemma lem1599263 (x : real) : (term35 x) = (term35 x).
Proof. exact (fun_ext (fun y : real => @lem1599262 x y)). Qed.
Lemma lem1599264 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1599265 (x : real) : (term36 x) = (term36 x).
Proof. exact (MK_COMB (@lem1599264) (@lem1599263 x)). Qed.
Lemma lem1599266 : term37 = term37.
Proof. exact (fun_ext (fun x : real => @lem1599265 x)). Qed.
Lemma lem1599267 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1599268 : term38 = term38.
Proof. exact (MK_COMB (@lem1599267) (@lem1599266)). Qed.
Lemma lem1599269 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1599270 : term18 = term18.
Proof. exact (MK_COMB (@lem1599269) (@lem1599268)). Qed.
Lemma lem1599271 : term20 = term20.
Proof. exact (MK_COMB (@lem1599270) (@lem1599250)). Qed.
Lemma lem1599276 (x : real) (y : real) : (term39 x y) = (term39 x y).
Proof. exact (eq_refl (term39 x y)). Qed.
Lemma lem1599277 (x : real) : (term40 x) = (term40 x).
Proof. exact (fun_ext (fun y : real => @lem1599276 x y)). Qed.
Lemma lem1599278 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1599279 (x : real) : (term41 x) = (term41 x).
Proof. exact (MK_COMB (@lem1599278) (@lem1599277 x)). Qed.
Lemma lem1599280 : term42 = term42.
Proof. exact (fun_ext (fun x : real => @lem1599279 x)). Qed.
Lemma lem1599281 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1599282 : term43 = term43.
Proof. exact (MK_COMB (@lem1599281) (@lem1599280)). Qed.
Lemma lem1599283 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1599284 : term21 = term21.
Proof. exact (MK_COMB (@lem1599283) (@lem1599282)). Qed.
Lemma lem1599285 : term23 = term23.
Proof. exact (MK_COMB (@lem1599284) (@lem1599271)). Qed.
Lemma lem1599294 (z : real) (x : real) (y : real) : (term44 z x y) = (term44 z x y).
Proof. exact (eq_refl (term44 z x y)). Qed.
Lemma lem1599295 (x : real) (y : real) : (term45 x y) = (term45 x y).
Proof. exact (fun_ext (fun z : real => @lem1599294 z x y)). Qed.
Lemma lem1599296 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1599297 (x : real) (y : real) : (term46 x y) = (term46 x y).
Proof. exact (MK_COMB (@lem1599296) (@lem1599295 x y)). Qed.
Lemma lem1599298 (x : real) : (term47 x) = (term47 x).
Proof. exact (fun_ext (fun y : real => @lem1599297 x y)). Qed.
Lemma lem1599299 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1599300 (x : real) : (term48 x) = (term48 x).
Proof. exact (MK_COMB (@lem1599299) (@lem1599298 x)). Qed.
Lemma lem1599301 : term49 = term49.
Proof. exact (fun_ext (fun x : real => @lem1599300 x)). Qed.
Lemma lem1599302 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1599303 : term8 = term8.
Proof. exact (MK_COMB (@lem1599302) (@lem1599301)). Qed.
Lemma lem1599304 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1599305 : term10 = term10.
Proof. exact (MK_COMB (@lem1599304) (@lem1599303)). Qed.
Lemma lem1599306 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1599307 : term24 = term24.
Proof. exact (MK_COMB (@lem1599306) (@lem1599305)). Qed.
Lemma lem1599308 : term25 = term25.
Proof. exact (MK_COMB (@lem1599307) (@lem1599285)). Qed.
Lemma lem1599395 : term11 = term25.
Proof. exact (TRANS (@lem1599230) (@lem1599308)). Qed.
Lemma lem1599396 : term25 = term11.
Proof. exact (SYM (@lem1599395)). Qed.
Lemma lem1599397 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1599398 (h1 : term43) : term43.
Proof. exact (h1). Qed.
Lemma lem1599399 (h1 : term38) : term38.
Proof. exact (h1). Qed.
Lemma lem1599400 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem1599416 (z : real) (x : real) (y : real) : (term50 z x y) = (term51 z x y).
Proof. exact (@lem17646 (term52 x y z) (real_le x y)). Qed.
Lemma lem1599418 (z : real) : (term53 z) = (term53 z).
Proof. exact (eq_refl (term53 z)). Qed.
Lemma lem1599419 (z : real) (x : real) (y : real) : (term54 z x y) = (term55 z x y).
Proof. exact (MK_COMB (@lem1599418 z) (@lem1599416 z x y)). Qed.
Lemma lem1599420 (z : real) (x : real) (y : real) : (term56 z x y) = (term54 z x y).
Proof. exact (@lem17362 (term57 z) ((term52 x y z) = (real_le x y))). Qed.
Lemma lem1599421 (z : real) (x : real) (y : real) : (term56 z x y) = (term55 z x y).
Proof. exact (TRANS (@lem1599420 z x y) (@lem1599419 z x y)). Qed.
Lemma lem1599422 (P : real -> Prop) : (term58 P) = (term59 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1599423 (x : real) (y : real) : (term60 x y) = (term61 x y).
Proof. exact (@lem1599422 (term45 x y)). Qed.
Lemma lem1599424 (z : real) (x : real) (y : real) : (term62 x y z) = (term44 z x y).
Proof. exact (eq_refl (term62 x y z)). Qed.
Lemma lem1599425 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1599426 (z : real) (x : real) (y : real) : (term63 x y z) = (term56 z x y).
Proof. exact (MK_COMB (@lem1599425) (@lem1599424 z x y)). Qed.
Lemma lem1599427 (z : real) (x : real) (y : real) : (term63 x y z) = (term55 z x y).
Proof. exact (TRANS (@lem1599426 z x y) (@lem1599421 z x y)). Qed.
Lemma lem1599428 (x : real) (y : real) : (term64 x y) = (term65 x y).
Proof. exact (fun_ext (fun z : real => @lem1599427 z x y)). Qed.
Lemma lem1599429 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1599430 (x : real) (y : real) : (term61 x y) = (term66 x y).
Proof. exact (MK_COMB (@lem1599429) (@lem1599428 x y)). Qed.
Lemma lem1599431 (x : real) (y : real) : (term60 x y) = (term66 x y).
Proof. exact (TRANS (@lem1599423 x y) (@lem1599430 x y)). Qed.
Lemma lem1599432 (P : real -> Prop) : (term58 P) = (term59 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1599433 (x : real) : (term67 x) = (term68 x).
Proof. exact (@lem1599432 (term47 x)). Qed.
Lemma lem1599434 (x : real) (y : real) : (term69 x y) = (term46 x y).
Proof. exact (eq_refl (term69 x y)). Qed.
Lemma lem1599435 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1599436 (x : real) (y : real) : (term70 x y) = (term60 x y).
Proof. exact (MK_COMB (@lem1599435) (@lem1599434 x y)). Qed.
Lemma lem1599437 (x : real) (y : real) : (term70 x y) = (term66 x y).
Proof. exact (TRANS (@lem1599436 x y) (@lem1599431 x y)). Qed.
Lemma lem1599438 (x : real) : (term71 x) = (term72 x).
Proof. exact (fun_ext (fun y : real => @lem1599437 x y)). Qed.
Lemma lem1599439 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1599440 (x : real) : (term68 x) = (term73 x).
Proof. exact (MK_COMB (@lem1599439) (@lem1599438 x)). Qed.
Lemma lem1599441 (x : real) : (term67 x) = (term73 x).
Proof. exact (TRANS (@lem1599433 x) (@lem1599440 x)). Qed.
Lemma lem1599442 (P : real -> Prop) : (term58 P) = (term59 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1599443 : term10 = term74.
Proof. exact (@lem1599442 term49). Qed.
Lemma lem1599444 (x : real) : (term75 x) = (term48 x).
Proof. exact (eq_refl (term75 x)). Qed.
Lemma lem1599445 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1599446 (x : real) : (term76 x) = (term67 x).
Proof. exact (MK_COMB (@lem1599445) (@lem1599444 x)). Qed.
Lemma lem1599447 (x : real) : (term76 x) = (term73 x).
Proof. exact (TRANS (@lem1599446 x) (@lem1599441 x)). Qed.
Lemma lem1599448 : term77 = term78.
Proof. exact (fun_ext (fun x : real => @lem1599447 x)). Qed.
Lemma lem1599449 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1599450 : term74 = term79.
Proof. exact (MK_COMB (@lem1599449) (@lem1599448)). Qed.
Lemma lem1599511 : term10 = term79.
Proof. exact (TRANS (@lem1599443) (@lem1599450)). Qed.
Lemma lem1599512 (h1 : term10) : term79.
Proof. exact (EQ_MP (@lem1599511) (@lem1599397 h1)). Qed.
Lemma lem1599519 (x : real) (y : real) : (term39 x y) = (term80 x y).
Proof. exact (@lem17265 (real_lt x y) (real_le x y)). Qed.
Lemma lem1599520 (x : real) : (term40 x) = (term81 x).
Proof. exact (fun_ext (fun y : real => @lem1599519 x y)). Qed.
Lemma lem1599521 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1599522 (x : real) : (term41 x) = (term82 x).
Proof. exact (MK_COMB (@lem1599521) (@lem1599520 x)). Qed.
Lemma lem1599523 : term42 = term83.
Proof. exact (fun_ext (fun x : real => @lem1599522 x)). Qed.
Lemma lem1599524 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1599581 : term43 = term84.
Proof. exact (MK_COMB (@lem1599524) (@lem1599523)). Qed.
Lemma lem1599582 (h1 : term43) : term84.
Proof. exact (EQ_MP (@lem1599581) (@lem1599398 h1)). Qed.
Lemma lem1599589 (x : real) (y : real) (z : real) : (term85 x y z) = (term86 x y z).
Proof. exact (@lem17045 (term57 z) (term52 x y z)). Qed.
Lemma lem1599590 (x : real) (y : real) : (real_le x y) = (real_le x y).
Proof. exact (eq_refl (real_le x y)). Qed.
Lemma lem1599591 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1599592 (x : real) (y : real) (z : real) : (term87 x y z) = (term88 x y z).
Proof. exact (MK_COMB (@lem1599591) (@lem1599589 x y z)). Qed.
Lemma lem1599593 (z : real) (x : real) (y : real) : (term89 z x y) = (term90 z x y).
Proof. exact (MK_COMB (@lem1599592 x y z) (@lem1599590 x y)). Qed.
Lemma lem1599594 (z : real) (x : real) (y : real) : (term32 z x y) = (term89 z x y).
Proof. exact (@lem17265 (term91 x y z) (real_le x y)). Qed.
Lemma lem1599595 (z : real) (x : real) (y : real) : (term32 z x y) = (term90 z x y).
Proof. exact (TRANS (@lem1599594 z x y) (@lem1599593 z x y)). Qed.
Lemma lem1599596 (x : real) (y : real) : (term33 x y) = (term92 x y).
Proof. exact (fun_ext (fun z : real => @lem1599595 z x y)). Qed.
Lemma lem1599597 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1599598 (x : real) (y : real) : (term34 x y) = (term93 x y).
Proof. exact (MK_COMB (@lem1599597) (@lem1599596 x y)). Qed.
Lemma lem1599599 (x : real) : (term35 x) = (term94 x).
Proof. exact (fun_ext (fun y : real => @lem1599598 x y)). Qed.
Lemma lem1599600 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1599601 (x : real) : (term36 x) = (term95 x).
Proof. exact (MK_COMB (@lem1599600) (@lem1599599 x)). Qed.
Lemma lem1599602 : term37 = term96.
Proof. exact (fun_ext (fun x : real => @lem1599601 x)). Qed.
Lemma lem1599603 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1599604 : term38 = term97.
Proof. exact (MK_COMB (@lem1599603) (@lem1599602)). Qed.
Lemma lem1599634 {A : Type'} (P : A -> Prop) (Q : Prop) : (term98 A P Q) = (term99 A P Q).
Proof. exact (EQ_MP (@lem18947 A P Q) (@lem18946 A P Q)). Qed.
Lemma lem1599635 (P : real -> Prop) (Q : Prop) : (term100 P Q) = (term101 P Q).
Proof. exact (@lem1599634 real P Q). Qed.
Lemma lem1599636 (x : real) (y : real) : (term102 x y) = (term103 x y).
Proof. exact (@lem1599635 (term104 x y) (real_le x y)). Qed.
Lemma lem1599637 (x : real) (y : real) (z : real) : (term105 x y z) = (term86 x y z).
Proof. exact (eq_refl (term105 x y z)). Qed.
Lemma lem1599638 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1599639 (x : real) (y : real) (z : real) : (term106 x y z) = (term88 x y z).
Proof. exact (MK_COMB (@lem1599638) (@lem1599637 x y z)). Qed.
Lemma lem1599640 (x : real) (y : real) : (real_le x y) = (real_le x y).
Proof. exact (eq_refl (real_le x y)). Qed.
Lemma lem1599641 (z : real) (x : real) (y : real) : (term107 z x y) = (term90 z x y).
Proof. exact (MK_COMB (@lem1599639 x y z) (@lem1599640 x y)). Qed.
Lemma lem1599642 (x : real) (y : real) : (term108 x y) = (term92 x y).
Proof. exact (fun_ext (fun z : real => @lem1599641 z x y)). Qed.
Lemma lem1599643 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1599644 (x : real) (y : real) : (term102 x y) = (term93 x y).
Proof. exact (MK_COMB (@lem1599643) (@lem1599642 x y)). Qed.
Lemma lem1599645 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1599646 (x : real) (y : real) : (term109 x y) = (term110 x y).
Proof. exact (MK_COMB (@lem1599645) (@lem1599644 x y)). Qed.
Lemma lem1599647 (x : real) (y : real) (z : real) : (term105 x y z) = (term86 x y z).
Proof. exact (eq_refl (term105 x y z)). Qed.
Lemma lem1599648 (x : real) (y : real) : (term111 x y) = (term104 x y).
Proof. exact (fun_ext (fun z : real => @lem1599647 x y z)). Qed.
Lemma lem1599649 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1599650 (x : real) (y : real) : (term112 x y) = (term113 x y).
Proof. exact (MK_COMB (@lem1599649) (@lem1599648 x y)). Qed.
Lemma lem1599651 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1599652 (x : real) (y : real) : (term114 x y) = (term115 x y).
Proof. exact (MK_COMB (@lem1599651) (@lem1599650 x y)). Qed.
Lemma lem1599653 (x : real) (y : real) : (real_le x y) = (real_le x y).
Proof. exact (eq_refl (real_le x y)). Qed.
Lemma lem1599654 (x : real) (y : real) : (term103 x y) = (term116 x y).
Proof. exact (MK_COMB (@lem1599652 x y) (@lem1599653 x y)). Qed.
Lemma lem1599655 (x : real) (y : real) : ((term102 x y) = (term103 x y)) = ((term93 x y) = (term116 x y)).
Proof. exact (MK_COMB (@lem1599646 x y) (@lem1599654 x y)). Qed.
Lemma lem1599656 (x : real) (y : real) : (term93 x y) = (term116 x y).
Proof. exact (EQ_MP (@lem1599655 x y) (@lem1599636 x y)). Qed.
Lemma lem1599705 (x : real) : (term94 x) = (term117 x).
Proof. exact (fun_ext (fun y : real => @lem1599656 x y)). Qed.
Lemma lem1599706 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1599707 (x : real) : (term95 x) = (term118 x).
Proof. exact (MK_COMB (@lem1599706) (@lem1599705 x)). Qed.
Lemma lem1599756 : term96 = term119.
Proof. exact (fun_ext (fun x : real => @lem1599707 x)). Qed.
Lemma lem1599757 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1599764 : term97 = term120.
Proof. exact (MK_COMB (@lem1599757) (@lem1599756)). Qed.
Lemma lem1599765 : term38 = term120.
Proof. exact (TRANS (@lem1599604) (@lem1599764)). Qed.
Lemma lem1599766 (h1 : term38) : term120.
Proof. exact (EQ_MP (@lem1599765) (@lem1599399 h1)). Qed.
Lemma lem1599773 (x : real) (y : real) (z : real) : (term121 x y z) = (term122 x y z).
Proof. exact (@lem17045 (real_le x y) (term123 z)). Qed.
Lemma lem1599774 (x : real) (y : real) (z : real) : (term52 x y z) = (term52 x y z).
Proof. exact (eq_refl (term52 x y z)). Qed.
Lemma lem1599775 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1599776 (x : real) (y : real) (z : real) : (term124 x y z) = (term125 x y z).
Proof. exact (MK_COMB (@lem1599775) (@lem1599773 x y z)). Qed.
Lemma lem1599777 (x : real) (y : real) (z : real) : (term126 x y z) = (term127 x y z).
Proof. exact (MK_COMB (@lem1599776 x y z) (@lem1599774 x y z)). Qed.
Lemma lem1599778 (x : real) (y : real) (z : real) : (term26 x y z) = (term126 x y z).
Proof. exact (@lem17265 (term128 x y z) (term52 x y z)). Qed.
Lemma lem1599779 (x : real) (y : real) (z : real) : (term26 x y z) = (term127 x y z).
Proof. exact (TRANS (@lem1599778 x y z) (@lem1599777 x y z)). Qed.
Lemma lem1599780 (x : real) (y : real) : (term27 x y) = (term129 x y).
Proof. exact (fun_ext (fun z : real => @lem1599779 x y z)). Qed.
Lemma lem1599781 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1599782 (x : real) (y : real) : (term28 x y) = (term130 x y).
Proof. exact (MK_COMB (@lem1599781) (@lem1599780 x y)). Qed.
Lemma lem1599783 (x : real) : (term29 x) = (term131 x).
Proof. exact (fun_ext (fun y : real => @lem1599782 x y)). Qed.
Lemma lem1599784 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1599785 (x : real) : (term30 x) = (term132 x).
Proof. exact (MK_COMB (@lem1599784) (@lem1599783 x)). Qed.
Lemma lem1599786 : term31 = term133.
Proof. exact (fun_ext (fun x : real => @lem1599785 x)). Qed.
Lemma lem1599787 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1599848 : term17 = term134.
Proof. exact (MK_COMB (@lem1599787) (@lem1599786)). Qed.
Lemma lem1599849 (h1 : term17) : term134.
Proof. exact (EQ_MP (@lem1599848) (@lem1599400 h1)). Qed.
Lemma lem1599850 (x : real) (h1 : term73 x) : term73 x.
Proof. exact (h1). Qed.
Lemma lem1599851 (x : real) (y : real) (h1 : term66 x y) : term66 x y.
Proof. exact (h1). Qed.
Lemma lem1599867 (x : real) (y : real) : (term80 x y) = (term80 x y).
Proof. exact (eq_refl (term80 x y)). Qed.
Lemma lem1599868 (x : real) : (term81 x) = (term81 x).
Proof. exact (fun_ext (fun y : real => @lem1599867 x y)). Qed.
Lemma lem1599869 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1599870 (x : real) : (term82 x) = (term82 x).
Proof. exact (MK_COMB (@lem1599869) (@lem1599868 x)). Qed.
Lemma lem1599871 : term83 = term83.
Proof. exact (fun_ext (fun x : real => @lem1599870 x)). Qed.
Lemma lem1599872 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1599873 : term84 = term84.
Proof. exact (MK_COMB (@lem1599872) (@lem1599871)). Qed.
Lemma lem1599874 (h1 : term43) : term84.
Proof. exact (EQ_MP (@lem1599873) (@lem1599582 h1)). Qed.
Lemma lem1599879 (x : real) (y : real) : (real_le x y) = (real_le x y).
Proof. exact (eq_refl (real_le x y)). Qed.
Lemma lem1599908 (x : real) (y : real) (z : real) : (term86 x y z) = (term86 x y z).
Proof. exact (eq_refl (term86 x y z)). Qed.
Lemma lem1599909 (x : real) (y : real) : (term104 x y) = (term104 x y).
Proof. exact (fun_ext (fun z : real => @lem1599908 x y z)). Qed.
Lemma lem1599910 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1599911 (x : real) (y : real) : (term113 x y) = (term113 x y).
Proof. exact (MK_COMB (@lem1599910) (@lem1599909 x y)). Qed.
Lemma lem1599912 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1599913 (x : real) (y : real) : (term115 x y) = (term115 x y).
Proof. exact (MK_COMB (@lem1599912) (@lem1599911 x y)). Qed.
Lemma lem1599914 (x : real) (y : real) : (term116 x y) = (term116 x y).
Proof. exact (MK_COMB (@lem1599913 x y) (@lem1599879 x y)). Qed.
Lemma lem1599915 (x : real) : (term117 x) = (term117 x).
Proof. exact (fun_ext (fun y : real => @lem1599914 x y)). Qed.
Lemma lem1599916 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1599917 (x : real) : (term118 x) = (term118 x).
Proof. exact (MK_COMB (@lem1599916) (@lem1599915 x)). Qed.
Lemma lem1599918 : term119 = term119.
Proof. exact (fun_ext (fun x : real => @lem1599917 x)). Qed.
Lemma lem1599919 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1599920 : term120 = term120.
Proof. exact (MK_COMB (@lem1599919) (@lem1599918)). Qed.
Lemma lem1599921 (h1 : term38) : term120.
Proof. exact (EQ_MP (@lem1599920) (@lem1599766 h1)). Qed.
Lemma lem1599958 (x : real) (y : real) (z : real) : (term127 x y z) = (term127 x y z).
Proof. exact (eq_refl (term127 x y z)). Qed.
Lemma lem1599959 (x : real) (y : real) : (term129 x y) = (term129 x y).
Proof. exact (fun_ext (fun z : real => @lem1599958 x y z)). Qed.
Lemma lem1599960 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1599961 (x : real) (y : real) : (term130 x y) = (term130 x y).
Proof. exact (MK_COMB (@lem1599960) (@lem1599959 x y)). Qed.
Lemma lem1599962 (x : real) : (term131 x) = (term131 x).
Proof. exact (fun_ext (fun y : real => @lem1599961 x y)). Qed.
Lemma lem1599963 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1599964 (x : real) : (term132 x) = (term132 x).
Proof. exact (MK_COMB (@lem1599963) (@lem1599962 x)). Qed.
Lemma lem1599965 : term133 = term133.
Proof. exact (fun_ext (fun x : real => @lem1599964 x)). Qed.
Lemma lem1599966 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1599967 : term134 = term134.
Proof. exact (MK_COMB (@lem1599966) (@lem1599965)). Qed.
Lemma lem1599968 (h1 : term17) : term134.
Proof. exact (EQ_MP (@lem1599967) (@lem1599849 h1)). Qed.
Lemma lem1600030 (z : real) (x : real) (y : real) (h1 : term55 z x y) : term55 z x y.
Proof. exact (h1). Qed.
Lemma lem1600031 (z : real) (x : real) (y : real) (h1 : term55 z x y) : term51 z x y.
Proof. exact (proj2 (@lem1600030 z x y h1)). Qed.
Lemma lem1600033 (z : real) (x : real) (y : real) (h1 : term135 z x y) : term135 z x y.
Proof. exact (h1). Qed.
Lemma lem1600034 (z : real) (x : real) (y : real) (h1 : term136 z x y) : term136 z x y.
Proof. exact (h1). Qed.
Lemma lem1600056 {A : Type'} (P : A -> Prop) (Q : Prop) : (term99 A P Q) = (term98 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem1600057 (P : real -> Prop) (Q : Prop) : (term101 P Q) = (term100 P Q).
Proof. exact (@lem1600056 real P Q). Qed.
Lemma lem1600058 (x : real) (y : real) : (term103 x y) = (term102 x y).
Proof. exact (@lem1600057 (term104 x y) (real_le x y)). Qed.
Lemma lem1600059 (x : real) (y : real) (z : real) : (term105 x y z) = (term86 x y z).
Proof. exact (eq_refl (term105 x y z)). Qed.
Lemma lem1600060 (x : real) (y : real) : (term111 x y) = (term104 x y).
Proof. exact (fun_ext (fun z : real => @lem1600059 x y z)). Qed.
Lemma lem1600061 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1600062 (x : real) (y : real) : (term112 x y) = (term113 x y).
Proof. exact (MK_COMB (@lem1600061) (@lem1600060 x y)). Qed.
Lemma lem1600063 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1600064 (x : real) (y : real) : (term114 x y) = (term115 x y).
Proof. exact (MK_COMB (@lem1600063) (@lem1600062 x y)). Qed.
Lemma lem1600065 (x : real) (y : real) : (real_le x y) = (real_le x y).
Proof. exact (eq_refl (real_le x y)). Qed.
Lemma lem1600066 (x : real) (y : real) : (term103 x y) = (term116 x y).
Proof. exact (MK_COMB (@lem1600064 x y) (@lem1600065 x y)). Qed.
Lemma lem1600067 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1600068 (x : real) (y : real) : (term137 x y) = (term138 x y).
Proof. exact (MK_COMB (@lem1600067) (@lem1600066 x y)). Qed.
Lemma lem1600069 (x : real) (y : real) (z : real) : (term105 x y z) = (term86 x y z).
Proof. exact (eq_refl (term105 x y z)). Qed.
Lemma lem1600070 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1600071 (x : real) (y : real) (z : real) : (term106 x y z) = (term88 x y z).
Proof. exact (MK_COMB (@lem1600070) (@lem1600069 x y z)). Qed.
Lemma lem1600072 (x : real) (y : real) : (real_le x y) = (real_le x y).
Proof. exact (eq_refl (real_le x y)). Qed.
Lemma lem1600073 (z : real) (x : real) (y : real) : (term107 z x y) = (term90 z x y).
Proof. exact (MK_COMB (@lem1600071 x y z) (@lem1600072 x y)). Qed.
Lemma lem1600074 (x : real) (y : real) : (term108 x y) = (term92 x y).
Proof. exact (fun_ext (fun z : real => @lem1600073 z x y)). Qed.
Lemma lem1600075 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1600076 (x : real) (y : real) : (term102 x y) = (term93 x y).
Proof. exact (MK_COMB (@lem1600075) (@lem1600074 x y)). Qed.
Lemma lem1600077 (x : real) (y : real) : ((term103 x y) = (term102 x y)) = ((term116 x y) = (term93 x y)).
Proof. exact (MK_COMB (@lem1600068 x y) (@lem1600076 x y)). Qed.
Lemma lem1600078 (x : real) (y : real) : (term116 x y) = (term93 x y).
Proof. exact (EQ_MP (@lem1600077 x y) (@lem1600058 x y)). Qed.
Lemma lem1600079 (x : real) : (term117 x) = (term94 x).
Proof. exact (fun_ext (fun y : real => @lem1600078 x y)). Qed.
Lemma lem1600080 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1600081 (x : real) : (term118 x) = (term95 x).
Proof. exact (MK_COMB (@lem1600080) (@lem1600079 x)). Qed.
Lemma lem1600082 : term119 = term96.
Proof. exact (fun_ext (fun x : real => @lem1600081 x)). Qed.
Lemma lem1600083 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1600084 : term120 = term97.
Proof. exact (MK_COMB (@lem1600083) (@lem1600082)). Qed.
Lemma lem1600097 (z : real) (x : real) (y : real) : (term90 z x y) = (term90 z x y).
Proof. exact (eq_refl (term90 z x y)). Qed.
Lemma lem1600098 (x : real) (y : real) : (term92 x y) = (term92 x y).
Proof. exact (fun_ext (fun z : real => @lem1600097 z x y)). Qed.
Lemma lem1600099 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1600100 (x : real) (y : real) : (term93 x y) = (term93 x y).
Proof. exact (MK_COMB (@lem1600099) (@lem1600098 x y)). Qed.
Lemma lem1600101 (x : real) : (term94 x) = (term94 x).
Proof. exact (fun_ext (fun y : real => @lem1600100 x y)). Qed.
Lemma lem1600102 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1600103 (x : real) : (term95 x) = (term95 x).
Proof. exact (MK_COMB (@lem1600102) (@lem1600101 x)). Qed.
Lemma lem1600104 : term96 = term96.
Proof. exact (fun_ext (fun x : real => @lem1600103 x)). Qed.
Lemma lem1600105 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1600106 : term97 = term97.
Proof. exact (MK_COMB (@lem1600105) (@lem1600104)). Qed.
Lemma lem1600107 : term120 = term97.
Proof. exact (TRANS (@lem1600084) (@lem1600106)). Qed.
Lemma lem1600108 (h1 : term38) : term97.
Proof. exact (EQ_MP (@lem1600107) (@lem1599921 h1)). Qed.
Lemma lem1600153 (x : real) (y : real) : (term80 x y) = (term80 x y).
Proof. exact (eq_refl (term80 x y)). Qed.
Lemma lem1600154 (x : real) : (term81 x) = (term81 x).
Proof. exact (fun_ext (fun y : real => @lem1600153 x y)). Qed.
Lemma lem1600155 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1600156 (x : real) : (term82 x) = (term82 x).
Proof. exact (MK_COMB (@lem1600155) (@lem1600154 x)). Qed.
Lemma lem1600157 : term83 = term83.
Proof. exact (fun_ext (fun x : real => @lem1600156 x)). Qed.
Lemma lem1600158 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1600160 : term84 = term84.
Proof. exact (MK_COMB (@lem1600158) (@lem1600157)). Qed.
Lemma lem1600161 (h1 : term43) : term84.
Proof. exact (EQ_MP (@lem1600160) (@lem1599874 h1)). Qed.
Lemma lem1600229 (x : real) (y : real) (z : real) : (term127 x y z) = (term127 x y z).
Proof. exact (eq_refl (term127 x y z)). Qed.
Lemma lem1600230 (x : real) (y : real) : (term129 x y) = (term129 x y).
Proof. exact (fun_ext (fun z : real => @lem1600229 x y z)). Qed.
Lemma lem1600231 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1600232 (x : real) (y : real) : (term130 x y) = (term130 x y).
Proof. exact (MK_COMB (@lem1600231) (@lem1600230 x y)). Qed.
Lemma lem1600233 (x : real) : (term131 x) = (term131 x).
Proof. exact (fun_ext (fun y : real => @lem1600232 x y)). Qed.
Lemma lem1600234 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1600235 (x : real) : (term132 x) = (term132 x).
Proof. exact (MK_COMB (@lem1600234) (@lem1600233 x)). Qed.
Lemma lem1600236 : term133 = term133.
Proof. exact (fun_ext (fun x : real => @lem1600235 x)). Qed.
Lemma lem1600237 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1600239 : term134 = term134.
Proof. exact (MK_COMB (@lem1600237) (@lem1600236)). Qed.
Lemma lem1600240 (h1 : term17) : term134.
Proof. exact (EQ_MP (@lem1600239) (@lem1599968 h1)). Qed.
Lemma lem1600259 (_25237 : real) (h1 : term38) : term139 _25237.
Proof. exact (@lem1600108 h1 _25237). Qed.
Lemma lem1600260 (_25237 : real) : (term139 _25237) = (term95 _25237).
Proof. exact (eq_refl (term139 _25237)). Qed.
Lemma lem1600261 (_25237 : real) (h1 : term38) : term95 _25237.
Proof. exact (EQ_MP (@lem1600260 _25237) (@lem1600259 _25237 h1)). Qed.
Lemma lem1600262 (_25237 : real) (_25238 : real) (h1 : term38) : term140 _25237 _25238.
Proof. exact (@lem1600261 _25237 h1 _25238). Qed.
Lemma lem1600263 (_25237 : real) (_25238 : real) : (term140 _25237 _25238) = (term93 _25237 _25238).
Proof. exact (eq_refl (term140 _25237 _25238)). Qed.
Lemma lem1600264 (_25237 : real) (_25238 : real) (h1 : term38) : term93 _25237 _25238.
Proof. exact (EQ_MP (@lem1600263 _25237 _25238) (@lem1600262 _25237 _25238 h1)). Qed.
Lemma lem1600265 (_25237 : real) (_25238 : real) (_25239 : real) (h1 : term38) : term141 _25237 _25238 _25239.
Proof. exact (@lem1600264 _25237 _25238 h1 _25239). Qed.
Lemma lem1600266 (_25239 : real) (_25237 : real) (_25238 : real) : (term141 _25237 _25238 _25239) = (term90 _25239 _25237 _25238).
Proof. exact (eq_refl (term141 _25237 _25238 _25239)). Qed.
Lemma lem1600267 (_25239 : real) (_25237 : real) (_25238 : real) (h1 : term38) : term90 _25239 _25237 _25238.
Proof. exact (EQ_MP (@lem1600266 _25239 _25237 _25238) (@lem1600265 _25237 _25238 _25239 h1)). Qed.
Lemma lem1600277 (_25243 : real) (h1 : term43) : term142 _25243.
Proof. exact (@lem1600161 h1 _25243). Qed.
Lemma lem1600278 (_25243 : real) : (term142 _25243) = (term82 _25243).
Proof. exact (eq_refl (term142 _25243)). Qed.
Lemma lem1600279 (_25243 : real) (h1 : term43) : term82 _25243.
Proof. exact (EQ_MP (@lem1600278 _25243) (@lem1600277 _25243 h1)). Qed.
Lemma lem1600280 (_25243 : real) (_25244 : real) (h1 : term43) : term143 _25243 _25244.
Proof. exact (@lem1600279 _25243 h1 _25244). Qed.
Lemma lem1600281 (_25243 : real) (_25244 : real) : (term143 _25243 _25244) = (term80 _25243 _25244).
Proof. exact (eq_refl (term143 _25243 _25244)). Qed.
Lemma lem1600292 (_25248 : real) (h1 : term17) : term144 _25248.
Proof. exact (@lem1600240 h1 _25248). Qed.
Lemma lem1600293 (_25248 : real) : (term144 _25248) = (term132 _25248).
Proof. exact (eq_refl (term144 _25248)). Qed.
Lemma lem1600294 (_25248 : real) (h1 : term17) : term132 _25248.
Proof. exact (EQ_MP (@lem1600293 _25248) (@lem1600292 _25248 h1)). Qed.
Lemma lem1600295 (_25248 : real) (_25249 : real) (h1 : term17) : term145 _25248 _25249.
Proof. exact (@lem1600294 _25248 h1 _25249). Qed.
Lemma lem1600296 (_25248 : real) (_25249 : real) : (term145 _25248 _25249) = (term130 _25248 _25249).
Proof. exact (eq_refl (term145 _25248 _25249)). Qed.
Lemma lem1600297 (_25248 : real) (_25249 : real) (h1 : term17) : term130 _25248 _25249.
Proof. exact (EQ_MP (@lem1600296 _25248 _25249) (@lem1600295 _25248 _25249 h1)). Qed.
Lemma lem1600298 (_25248 : real) (_25249 : real) (_25250 : real) (h1 : term17) : term146 _25248 _25249 _25250.
Proof. exact (@lem1600297 _25248 _25249 h1 _25250). Qed.
Lemma lem1600299 (_25248 : real) (_25249 : real) (_25250 : real) : (term146 _25248 _25249 _25250) = (term127 _25248 _25249 _25250).
Proof. exact (eq_refl (term146 _25248 _25249 _25250)). Qed.
Lemma lem1600300 (_25248 : real) (_25249 : real) (_25250 : real) (h1 : term17) : term127 _25248 _25249 _25250.
Proof. exact (EQ_MP (@lem1600299 _25248 _25249 _25250) (@lem1600298 _25248 _25249 _25250 h1)). Qed.
Lemma lem1600317 (_25239 : real) (_25237 : real) (_25238 : real) : (term90 _25239 _25237 _25238) = (term147 _25239 _25237 _25238).
Proof. exact (@lem1599129 (term148 _25239) (term149 _25237 _25238 _25239) (real_le _25237 _25238)). Qed.
Lemma lem1600318 (_25239 : real) (_25237 : real) (_25238 : real) (h1 : term38) : term147 _25239 _25237 _25238.
Proof. exact (EQ_MP (@lem1600317 _25239 _25237 _25238) (@lem1600267 _25239 _25237 _25238 h1)). Qed.
Lemma lem1600336 (z : real) (x : real) (y : real) (h1 : term135 z x y) : term150 x y.
Proof. exact (proj2 (@lem1600033 z x y h1)). Qed.
Lemma lem1600342 (_25243 : real) (_25244 : real) (h1 : term43) : term80 _25243 _25244.
Proof. exact (EQ_MP (@lem1600281 _25243 _25244) (@lem1600280 _25243 _25244 h1)). Qed.
Lemma lem1600365 (_25248 : real) (_25249 : real) (_25250 : real) : (term127 _25248 _25249 _25250) = (term151 _25248 _25249 _25250).
Proof. exact (@lem1599129 (term150 _25248 _25249) (term152 _25250) (term52 _25248 _25249 _25250)). Qed.
Lemma lem1600366 (_25248 : real) (_25249 : real) (_25250 : real) (h1 : term17) : term151 _25248 _25249 _25250.
Proof. exact (EQ_MP (@lem1600365 _25248 _25249 _25250) (@lem1600300 _25248 _25249 _25250 h1)). Qed.
Lemma lem1600370 (z : real) (x : real) (y : real) (h1 : term136 z x y) : term149 x y z.
Proof. exact (proj1 (@lem1600034 z x y h1)). Qed.
Lemma lem1600374 (z : real) (x : real) (y : real) (h1 : term55 z x y) : term57 z.
Proof. exact (proj1 (@lem1600030 z x y h1)). Qed.
Lemma lem1600375 (z : real) (x : real) (y : real) (h1 : term55 z x y) : term153 z.
Proof. exact (fun h0 : term148 z => @lem1600374 z x y h1). Qed.
Lemma lem1600377 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1600378 (z : real) : (term153 z) = (term57 z).
Proof. exact (@lem1600377 (term57 z)). Qed.
Lemma lem1600379 (z : real) (x : real) (y : real) (h1 : term55 z x y) : term57 z.
Proof. exact (EQ_MP (@lem1600378 z) (@lem1600375 z x y h1)). Qed.
Lemma lem1600381 (z : real) (x : real) (y : real) (h1 : term135 z x y) : term52 x y z.
Proof. exact (proj1 (@lem1600033 z x y h1)). Qed.
Lemma lem1600382 (z : real) (x : real) (y : real) (h1 : term135 z x y) : term155 x y z.
Proof. exact (fun h0 : term149 x y z => @lem1600381 z x y h1). Qed.
Lemma lem1600384 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1600385 (x : real) (y : real) (z : real) : (term155 x y z) = (term52 x y z).
Proof. exact (@lem1600384 (term52 x y z)). Qed.
Lemma lem1600386 (z : real) (x : real) (y : real) (h1 : term135 z x y) : term52 x y z.
Proof. exact (EQ_MP (@lem1600385 x y z) (@lem1600382 z x y h1)). Qed.
Lemma lem1600392 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1600393 (_25239 : real) (_25237 : real) (_25238 : real) : (term147 _25239 _25237 _25238) = (term156 _25239 _25237 _25238).
Proof. exact (@lem1600392 (term149 _25237 _25238 _25239) (term148 _25239) (real_le _25237 _25238)). Qed.
Lemma lem1600407 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1600408 (_25237 : real) (_25238 : real) (_25239 : real) : (term157 _25239 _25237 _25238) = (term158 _25237 _25238 _25239).
Proof. exact (@lem1600407 (real_le _25237 _25238) (term148 _25239)). Qed.
Lemma lem1600414 (_25237 : real) (_25238 : real) (_25239 : real) : (term159 _25237 _25238 _25239) = (term159 _25237 _25238 _25239).
Proof. exact (eq_refl (term159 _25237 _25238 _25239)). Qed.
Lemma lem1600415 (_25237 : real) (_25238 : real) (_25239 : real) : (term156 _25239 _25237 _25238) = (term160 _25237 _25238 _25239).
Proof. exact (MK_COMB (@lem1600414 _25237 _25238 _25239) (@lem1600408 _25237 _25238 _25239)). Qed.
Lemma lem1600419 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1600420 (_25237 : real) (_25238 : real) (_25239 : real) : (term160 _25237 _25238 _25239) = (term161 _25237 _25238 _25239).
Proof. exact (@lem1600419 (real_le _25237 _25238) (term149 _25237 _25238 _25239) (term148 _25239)). Qed.
Lemma lem1600436 (_25237 : real) (_25238 : real) (_25239 : real) : (term156 _25239 _25237 _25238) = (term161 _25237 _25238 _25239).
Proof. exact (TRANS (@lem1600415 _25237 _25238 _25239) (@lem1600420 _25237 _25238 _25239)). Qed.
Lemma lem1600437 (_25237 : real) (_25238 : real) (_25239 : real) : (term147 _25239 _25237 _25238) = (term161 _25237 _25238 _25239).
Proof. exact (TRANS (@lem1600393 _25239 _25237 _25238) (@lem1600436 _25237 _25238 _25239)). Qed.
Lemma lem1600438 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1600439 (_25237 : real) (_25238 : real) (_25239 : real) : (term162 _25239 _25237 _25238) = (term163 _25237 _25238 _25239).
Proof. exact (MK_COMB (@lem1600438) (@lem1600437 _25237 _25238 _25239)). Qed.
Lemma lem1600453 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1600454 (_25237 : real) (_25238 : real) (_25239 : real) : (term86 _25237 _25238 _25239) = (term164 _25237 _25238 _25239).
Proof. exact (@lem1600453 (term149 _25237 _25238 _25239) (term148 _25239)). Qed.
Lemma lem1600460 (_25237 : real) (_25238 : real) : (term165 _25237 _25238) = (term165 _25237 _25238).
Proof. exact (eq_refl (term165 _25237 _25238)). Qed.
Lemma lem1600461 (_25237 : real) (_25238 : real) (_25239 : real) : (term166 _25237 _25238 _25239) = (term161 _25237 _25238 _25239).
Proof. exact (MK_COMB (@lem1600460 _25237 _25238) (@lem1600454 _25237 _25238 _25239)). Qed.
Lemma lem1600472 (_25237 : real) (_25238 : real) (_25239 : real) : ((term147 _25239 _25237 _25238) = (term166 _25237 _25238 _25239)) = ((term161 _25237 _25238 _25239) = (term161 _25237 _25238 _25239)).
Proof. exact (MK_COMB (@lem1600439 _25237 _25238 _25239) (@lem1600461 _25237 _25238 _25239)). Qed.
Lemma lem1600474 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1600475 (x : Prop) : (x = x) = True.
Proof. exact (@lem1600474 Prop x). Qed.
Lemma lem1600476 (_25237 : real) (_25238 : real) (_25239 : real) : ((term161 _25237 _25238 _25239) = (term161 _25237 _25238 _25239)) = True.
Proof. exact (@lem1600475 (term161 _25237 _25238 _25239)). Qed.
Lemma lem1600477 (_25237 : real) (_25238 : real) (_25239 : real) : ((term147 _25239 _25237 _25238) = (term166 _25237 _25238 _25239)) = True.
Proof. exact (TRANS (@lem1600472 _25237 _25238 _25239) (@lem1600476 _25237 _25238 _25239)). Qed.
Lemma lem1600478 (_25237 : real) (_25238 : real) (_25239 : real) : True = ((term147 _25239 _25237 _25238) = (term166 _25237 _25238 _25239)).
Proof. exact (SYM (@lem1600477 _25237 _25238 _25239)). Qed.
Lemma lem1600479 (_25237 : real) (_25238 : real) (_25239 : real) : (term147 _25239 _25237 _25238) = (term166 _25237 _25238 _25239).
Proof. exact (EQ_MP (@lem1600478 _25237 _25238 _25239) (@lem0)). Qed.
Lemma lem1600480 (_25237 : real) (_25238 : real) (_25239 : real) (h1 : term38) : term166 _25237 _25238 _25239.
Proof. exact (EQ_MP (@lem1600479 _25237 _25238 _25239) (@lem1600318 _25239 _25237 _25238 h1)). Qed.
Lemma lem1600482 (b : Prop) (a : Prop) : (a \/ b) = (term167 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1600483 (_25239 : real) (_25237 : real) (_25238 : real) : (term166 _25237 _25238 _25239) = (term168 _25239 _25237 _25238).
Proof. exact (@lem1600482 (term86 _25237 _25238 _25239) (real_le _25237 _25238)). Qed.
Lemma lem1600485 (a : Prop) (b : Prop) : (term169 a b) = (term170 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1600486 (_25237 : real) (_25238 : real) (_25239 : real) : (term171 _25237 _25238 _25239) = (term172 _25237 _25238 _25239).
Proof. exact (@lem1600485 (term148 _25239) (term149 _25237 _25238 _25239)). Qed.
Lemma lem1600488 (a : Prop) : (term173 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1600489 (_25239 : real) : (term174 _25239) = (term57 _25239).
Proof. exact (@lem1600488 (term57 _25239)). Qed.
Lemma lem1600490 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1600491 (_25239 : real) : (term175 _25239) = (term53 _25239).
Proof. exact (MK_COMB (@lem1600490) (@lem1600489 _25239)). Qed.
Lemma lem1600493 (a : Prop) : (term173 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1600494 (_25237 : real) (_25238 : real) (_25239 : real) : (term176 _25237 _25238 _25239) = (term52 _25237 _25238 _25239).
Proof. exact (@lem1600493 (term52 _25237 _25238 _25239)). Qed.
Lemma lem1600495 (_25237 : real) (_25238 : real) (_25239 : real) : (term172 _25237 _25238 _25239) = (term91 _25237 _25238 _25239).
Proof. exact (MK_COMB (@lem1600491 _25239) (@lem1600494 _25237 _25238 _25239)). Qed.
Lemma lem1600496 (_25237 : real) (_25238 : real) (_25239 : real) : (term171 _25237 _25238 _25239) = (term91 _25237 _25238 _25239).
Proof. exact (TRANS (@lem1600486 _25237 _25238 _25239) (@lem1600495 _25237 _25238 _25239)). Qed.
Lemma lem1600497 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1600498 (_25237 : real) (_25238 : real) (_25239 : real) : (term177 _25237 _25238 _25239) = (term178 _25237 _25238 _25239).
Proof. exact (MK_COMB (@lem1600497) (@lem1600496 _25237 _25238 _25239)). Qed.
Lemma lem1600499 (_25237 : real) (_25238 : real) : (real_le _25237 _25238) = (real_le _25237 _25238).
Proof. exact (eq_refl (real_le _25237 _25238)). Qed.
Lemma lem1600500 (_25239 : real) (_25237 : real) (_25238 : real) : (term168 _25239 _25237 _25238) = (term32 _25239 _25237 _25238).
Proof. exact (MK_COMB (@lem1600498 _25237 _25238 _25239) (@lem1600499 _25237 _25238)). Qed.
Lemma lem1600501 (_25239 : real) (_25237 : real) (_25238 : real) : (term166 _25237 _25238 _25239) = (term32 _25239 _25237 _25238).
Proof. exact (TRANS (@lem1600483 _25239 _25237 _25238) (@lem1600500 _25239 _25237 _25238)). Qed.
Lemma lem1600503 (z : real) (x : real) (y : real) (h1 : term135 z x y) (h2 : term55 z x y) : term91 x y z.
Proof. exact (conj (@lem1600379 z x y h2) (@lem1600386 z x y h1)). Qed.
Lemma lem1600505 (_25239 : real) (_25237 : real) (_25238 : real) (h1 : term38) : term32 _25239 _25237 _25238.
Proof. exact (EQ_MP (@lem1600501 _25239 _25237 _25238) (@lem1600480 _25237 _25238 _25239 h1)). Qed.
Lemma lem1600506 (z : real) (x : real) (y : real) (h1 : term38) : term32 z x y.
Proof. exact (@lem1600505 z x y h1). Qed.
Lemma lem1600509 (z : real) (x : real) (y : real) (h1 : term38) (h2 : term135 z x y) (h3 : term55 z x y) : real_le x y.
Proof. exact (@lem1600506 z x y h1 (@lem1600503 z x y h2 h3)). Qed.
Lemma lem1600510 (z : real) (x : real) (y : real) (h1 : term38) (h2 : term135 z x y) (h3 : term55 z x y) : term179 x y.
Proof. exact (fun h0 : term150 x y => @lem1600509 z x y h1 h2 h3). Qed.
Lemma lem1600512 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1600513 (x : real) (y : real) : (term179 x y) = (real_le x y).
Proof. exact (@lem1600512 (real_le x y)). Qed.
Lemma lem1600514 (z : real) (x : real) (y : real) (h1 : term38) (h2 : term135 z x y) (h3 : term55 z x y) : real_le x y.
Proof. exact (EQ_MP (@lem1600513 x y) (@lem1600510 z x y h1 h2 h3)). Qed.
Lemma lem1600517 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1600519 (x : real) (y : real) : (term150 x y) = (term180 x y).
Proof. exact (@lem1600517 (real_le x y)). Qed.
Lemma lem1600522 (z : real) (x : real) (y : real) (h1 : term135 z x y) : term180 x y.
Proof. exact (EQ_MP (@lem1600519 x y) (@lem1600336 z x y h1)). Qed.
Lemma lem1600525 (z : real) (x : real) (y : real) (h1 : term38) (h2 : term135 z x y) (h3 : term55 z x y) : False.
Proof. exact (@lem1600522 z x y h2 (@lem1600514 z x y h1 h2 h3)). Qed.
Lemma lem1600526 (z : real) (x : real) (y : real) (h1 : term38) (h2 : term135 z x y) (h3 : term55 z x y) : term181.
Proof. exact (fun h0 : ~ False => @lem1600525 z x y h1 h2 h3). Qed.
Lemma lem1600528 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1600529 : term181 = False.
Proof. exact (@lem1600528 False). Qed.
Lemma lem1600530 (z : real) (x : real) (y : real) (h1 : term38) (h2 : term135 z x y) (h3 : term55 z x y) : False.
Proof. exact (EQ_MP (@lem1600529) (@lem1600526 z x y h1 h2 h3)). Qed.
Lemma lem1600532 (z : real) (x : real) (y : real) (h1 : term136 z x y) : real_le x y.
Proof. exact (proj2 (@lem1600034 z x y h1)). Qed.
Lemma lem1600533 (z : real) (x : real) (y : real) (h1 : term136 z x y) : term179 x y.
Proof. exact (fun h0 : term150 x y => @lem1600532 z x y h1). Qed.
Lemma lem1600535 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1600536 (x : real) (y : real) : (term179 x y) = (real_le x y).
Proof. exact (@lem1600535 (real_le x y)). Qed.
Lemma lem1600537 (z : real) (x : real) (y : real) (h1 : term136 z x y) : real_le x y.
Proof. exact (EQ_MP (@lem1600536 x y) (@lem1600533 z x y h1)). Qed.
Lemma lem1600539 (z : real) (x : real) (y : real) (h1 : term55 z x y) : term57 z.
Proof. exact (proj1 (@lem1600030 z x y h1)). Qed.
Lemma lem1600540 (z : real) (x : real) (y : real) (h1 : term55 z x y) : term153 z.
Proof. exact (fun h0 : term148 z => @lem1600539 z x y h1). Qed.
Lemma lem1600542 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1600543 (z : real) : (term153 z) = (term57 z).
Proof. exact (@lem1600542 (term57 z)). Qed.
Lemma lem1600544 (z : real) (x : real) (y : real) (h1 : term55 z x y) : term57 z.
Proof. exact (EQ_MP (@lem1600543 z) (@lem1600540 z x y h1)). Qed.
Lemma lem1600550 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1600551 (_25243 : real) (_25244 : real) : (term80 _25243 _25244) = (term182 _25243 _25244).
Proof. exact (@lem1600550 (real_le _25243 _25244) (term183 _25243 _25244)). Qed.
Lemma lem1600557 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1600558 (_25243 : real) (_25244 : real) : (term184 _25243 _25244) = (term185 _25243 _25244).
Proof. exact (MK_COMB (@lem1600557) (@lem1600551 _25243 _25244)). Qed.
Lemma lem1600564 (_25243 : real) (_25244 : real) : (term182 _25243 _25244) = (term182 _25243 _25244).
Proof. exact (eq_refl (term182 _25243 _25244)). Qed.
Lemma lem1600565 (_25243 : real) (_25244 : real) : ((term80 _25243 _25244) = (term182 _25243 _25244)) = ((term182 _25243 _25244) = (term182 _25243 _25244)).
Proof. exact (MK_COMB (@lem1600558 _25243 _25244) (@lem1600564 _25243 _25244)). Qed.
Lemma lem1600567 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1600568 (x : Prop) : (x = x) = True.
Proof. exact (@lem1600567 Prop x). Qed.
Lemma lem1600569 (_25243 : real) (_25244 : real) : ((term182 _25243 _25244) = (term182 _25243 _25244)) = True.
Proof. exact (@lem1600568 (term182 _25243 _25244)). Qed.
Lemma lem1600570 (_25243 : real) (_25244 : real) : ((term80 _25243 _25244) = (term182 _25243 _25244)) = True.
Proof. exact (TRANS (@lem1600565 _25243 _25244) (@lem1600569 _25243 _25244)). Qed.
Lemma lem1600571 (_25243 : real) (_25244 : real) : True = ((term80 _25243 _25244) = (term182 _25243 _25244)).
Proof. exact (SYM (@lem1600570 _25243 _25244)). Qed.
Lemma lem1600572 (_25243 : real) (_25244 : real) : (term80 _25243 _25244) = (term182 _25243 _25244).
Proof. exact (EQ_MP (@lem1600571 _25243 _25244) (@lem0)). Qed.
Lemma lem1600573 (_25243 : real) (_25244 : real) (h1 : term43) : term182 _25243 _25244.
Proof. exact (EQ_MP (@lem1600572 _25243 _25244) (@lem1600342 _25243 _25244 h1)). Qed.
Lemma lem1600575 (b : Prop) (a : Prop) : (a \/ b) = (term167 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1600576 (_25243 : real) (_25244 : real) : (term182 _25243 _25244) = (term186 _25243 _25244).
Proof. exact (@lem1600575 (term183 _25243 _25244) (real_le _25243 _25244)). Qed.
Lemma lem1600578 (a : Prop) : (term173 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1600579 (_25243 : real) (_25244 : real) : (term187 _25243 _25244) = (real_lt _25243 _25244).
Proof. exact (@lem1600578 (real_lt _25243 _25244)). Qed.
Lemma lem1600580 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1600581 (_25243 : real) (_25244 : real) : (term188 _25243 _25244) = (term189 _25243 _25244).
Proof. exact (MK_COMB (@lem1600580) (@lem1600579 _25243 _25244)). Qed.
Lemma lem1600582 (_25243 : real) (_25244 : real) : (real_le _25243 _25244) = (real_le _25243 _25244).
Proof. exact (eq_refl (real_le _25243 _25244)). Qed.
Lemma lem1600583 (_25243 : real) (_25244 : real) : (term186 _25243 _25244) = (term39 _25243 _25244).
Proof. exact (MK_COMB (@lem1600581 _25243 _25244) (@lem1600582 _25243 _25244)). Qed.
Lemma lem1600584 (_25243 : real) (_25244 : real) : (term182 _25243 _25244) = (term39 _25243 _25244).
Proof. exact (TRANS (@lem1600576 _25243 _25244) (@lem1600583 _25243 _25244)). Qed.
Lemma lem1600587 (_25243 : real) (_25244 : real) (h1 : term43) : term39 _25243 _25244.
Proof. exact (EQ_MP (@lem1600584 _25243 _25244) (@lem1600573 _25243 _25244 h1)). Qed.
Lemma lem1600588 (z : real) (h1 : term43) : term190 z.
Proof. exact (@lem1600587 term191 z h1). Qed.
Lemma lem1600591 (z : real) (x : real) (y : real) (h1 : term43) (h2 : term55 z x y) : term123 z.
Proof. exact (@lem1600588 z h1 (@lem1600544 z x y h2)). Qed.
Lemma lem1600592 (z : real) (x : real) (y : real) (h1 : term43) (h2 : term55 z x y) : term192 z.
Proof. exact (fun h0 : term152 z => @lem1600591 z x y h1 h2). Qed.
Lemma lem1600594 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1600595 (z : real) : (term192 z) = (term123 z).
Proof. exact (@lem1600594 (term123 z)). Qed.
Lemma lem1600596 (z : real) (x : real) (y : real) (h1 : term43) (h2 : term55 z x y) : term123 z.
Proof. exact (EQ_MP (@lem1600595 z) (@lem1600592 z x y h1 h2)). Qed.
Lemma lem1600612 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1600613 (_25248 : real) (_25249 : real) (_25250 : real) : (term193 _25248 _25249 _25250) = (term194 _25248 _25249 _25250).
Proof. exact (@lem1600612 (term52 _25248 _25249 _25250) (term152 _25250)). Qed.
Lemma lem1600619 (_25248 : real) (_25249 : real) : (term195 _25248 _25249) = (term195 _25248 _25249).
Proof. exact (eq_refl (term195 _25248 _25249)). Qed.
Lemma lem1600620 (_25248 : real) (_25249 : real) (_25250 : real) : (term151 _25248 _25249 _25250) = (term196 _25248 _25249 _25250).
Proof. exact (MK_COMB (@lem1600619 _25248 _25249) (@lem1600613 _25248 _25249 _25250)). Qed.
Lemma lem1600624 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1600625 (_25248 : real) (_25249 : real) (_25250 : real) : (term196 _25248 _25249 _25250) = (term197 _25248 _25249 _25250).
Proof. exact (@lem1600624 (term52 _25248 _25249 _25250) (term150 _25248 _25249) (term152 _25250)). Qed.
Lemma lem1600641 (_25248 : real) (_25249 : real) (_25250 : real) : (term151 _25248 _25249 _25250) = (term197 _25248 _25249 _25250).
Proof. exact (TRANS (@lem1600620 _25248 _25249 _25250) (@lem1600625 _25248 _25249 _25250)). Qed.
Lemma lem1600642 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1600643 (_25248 : real) (_25249 : real) (_25250 : real) : (term198 _25248 _25249 _25250) = (term199 _25248 _25249 _25250).
Proof. exact (MK_COMB (@lem1600642) (@lem1600641 _25248 _25249 _25250)). Qed.
Lemma lem1600659 (_25248 : real) (_25249 : real) (_25250 : real) : (term197 _25248 _25249 _25250) = (term197 _25248 _25249 _25250).
Proof. exact (eq_refl (term197 _25248 _25249 _25250)). Qed.
Lemma lem1600660 (_25248 : real) (_25249 : real) (_25250 : real) : ((term151 _25248 _25249 _25250) = (term197 _25248 _25249 _25250)) = ((term197 _25248 _25249 _25250) = (term197 _25248 _25249 _25250)).
Proof. exact (MK_COMB (@lem1600643 _25248 _25249 _25250) (@lem1600659 _25248 _25249 _25250)). Qed.
Lemma lem1600662 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1600663 (x : Prop) : (x = x) = True.
Proof. exact (@lem1600662 Prop x). Qed.
Lemma lem1600664 (_25248 : real) (_25249 : real) (_25250 : real) : ((term197 _25248 _25249 _25250) = (term197 _25248 _25249 _25250)) = True.
Proof. exact (@lem1600663 (term197 _25248 _25249 _25250)). Qed.
Lemma lem1600665 (_25248 : real) (_25249 : real) (_25250 : real) : ((term151 _25248 _25249 _25250) = (term197 _25248 _25249 _25250)) = True.
Proof. exact (TRANS (@lem1600660 _25248 _25249 _25250) (@lem1600664 _25248 _25249 _25250)). Qed.
Lemma lem1600666 (_25248 : real) (_25249 : real) (_25250 : real) : True = ((term151 _25248 _25249 _25250) = (term197 _25248 _25249 _25250)).
Proof. exact (SYM (@lem1600665 _25248 _25249 _25250)). Qed.
Lemma lem1600667 (_25248 : real) (_25249 : real) (_25250 : real) : (term151 _25248 _25249 _25250) = (term197 _25248 _25249 _25250).
Proof. exact (EQ_MP (@lem1600666 _25248 _25249 _25250) (@lem0)). Qed.
Lemma lem1600668 (_25248 : real) (_25249 : real) (_25250 : real) (h1 : term17) : term197 _25248 _25249 _25250.
Proof. exact (EQ_MP (@lem1600667 _25248 _25249 _25250) (@lem1600366 _25248 _25249 _25250 h1)). Qed.
Lemma lem1600670 (b : Prop) (a : Prop) : (a \/ b) = (term167 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1600671 (_25248 : real) (_25249 : real) (_25250 : real) : (term197 _25248 _25249 _25250) = (term200 _25248 _25249 _25250).
Proof. exact (@lem1600670 (term122 _25248 _25249 _25250) (term52 _25248 _25249 _25250)). Qed.
Lemma lem1600673 (a : Prop) (b : Prop) : (term169 a b) = (term170 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1600674 (_25248 : real) (_25249 : real) (_25250 : real) : (term201 _25248 _25249 _25250) = (term202 _25248 _25249 _25250).
Proof. exact (@lem1600673 (term150 _25248 _25249) (term152 _25250)). Qed.
Lemma lem1600676 (a : Prop) : (term173 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1600677 (_25248 : real) (_25249 : real) : (term203 _25248 _25249) = (real_le _25248 _25249).
Proof. exact (@lem1600676 (real_le _25248 _25249)). Qed.
Lemma lem1600678 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1600679 (_25248 : real) (_25249 : real) : (term204 _25248 _25249) = (term205 _25248 _25249).
Proof. exact (MK_COMB (@lem1600678) (@lem1600677 _25248 _25249)). Qed.
Lemma lem1600681 (a : Prop) : (term173 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1600682 (_25250 : real) : (term206 _25250) = (term123 _25250).
Proof. exact (@lem1600681 (term123 _25250)). Qed.
Lemma lem1600683 (_25248 : real) (_25249 : real) (_25250 : real) : (term202 _25248 _25249 _25250) = (term128 _25248 _25249 _25250).
Proof. exact (MK_COMB (@lem1600679 _25248 _25249) (@lem1600682 _25250)). Qed.
Lemma lem1600684 (_25248 : real) (_25249 : real) (_25250 : real) : (term201 _25248 _25249 _25250) = (term128 _25248 _25249 _25250).
Proof. exact (TRANS (@lem1600674 _25248 _25249 _25250) (@lem1600683 _25248 _25249 _25250)). Qed.
Lemma lem1600685 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1600686 (_25248 : real) (_25249 : real) (_25250 : real) : (term207 _25248 _25249 _25250) = (term208 _25248 _25249 _25250).
Proof. exact (MK_COMB (@lem1600685) (@lem1600684 _25248 _25249 _25250)). Qed.
Lemma lem1600687 (_25248 : real) (_25249 : real) (_25250 : real) : (term52 _25248 _25249 _25250) = (term52 _25248 _25249 _25250).
Proof. exact (eq_refl (term52 _25248 _25249 _25250)). Qed.
Lemma lem1600688 (_25248 : real) (_25249 : real) (_25250 : real) : (term200 _25248 _25249 _25250) = (term26 _25248 _25249 _25250).
Proof. exact (MK_COMB (@lem1600686 _25248 _25249 _25250) (@lem1600687 _25248 _25249 _25250)). Qed.
Lemma lem1600689 (_25248 : real) (_25249 : real) (_25250 : real) : (term197 _25248 _25249 _25250) = (term26 _25248 _25249 _25250).
Proof. exact (TRANS (@lem1600671 _25248 _25249 _25250) (@lem1600688 _25248 _25249 _25250)). Qed.
Lemma lem1600691 (z : real) (x : real) (y : real) (h1 : term43) (h2 : term136 z x y) (h3 : term55 z x y) : term128 x y z.
Proof. exact (conj (@lem1600537 z x y h2) (@lem1600596 z x y h1 h3)). Qed.
Lemma lem1600693 (_25248 : real) (_25249 : real) (_25250 : real) (h1 : term17) : term26 _25248 _25249 _25250.
Proof. exact (EQ_MP (@lem1600689 _25248 _25249 _25250) (@lem1600668 _25248 _25249 _25250 h1)). Qed.
Lemma lem1600694 (x : real) (y : real) (z : real) (h1 : term17) : term26 x y z.
Proof. exact (@lem1600693 x y z h1). Qed.
Lemma lem1600697 (z : real) (x : real) (y : real) (h1 : term17) (h2 : term43) (h3 : term136 z x y) (h4 : term55 z x y) : term52 x y z.
Proof. exact (@lem1600694 x y z h1 (@lem1600691 z x y h2 h3 h4)). Qed.
Lemma lem1600698 (z : real) (x : real) (y : real) (h1 : term17) (h2 : term43) (h3 : term136 z x y) (h4 : term55 z x y) : term155 x y z.
Proof. exact (fun h0 : term149 x y z => @lem1600697 z x y h1 h2 h3 h4). Qed.
Lemma lem1600700 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1600701 (x : real) (y : real) (z : real) : (term155 x y z) = (term52 x y z).
Proof. exact (@lem1600700 (term52 x y z)). Qed.
Lemma lem1600702 (z : real) (x : real) (y : real) (h1 : term17) (h2 : term43) (h3 : term136 z x y) (h4 : term55 z x y) : term52 x y z.
Proof. exact (EQ_MP (@lem1600701 x y z) (@lem1600698 z x y h1 h2 h3 h4)). Qed.
Lemma lem1600705 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1600707 (x : real) (y : real) (z : real) : (term149 x y z) = (term209 x y z).
Proof. exact (@lem1600705 (term52 x y z)). Qed.
Lemma lem1600710 (z : real) (x : real) (y : real) (h1 : term136 z x y) : term209 x y z.
Proof. exact (EQ_MP (@lem1600707 x y z) (@lem1600370 z x y h1)). Qed.
Lemma lem1600713 (z : real) (x : real) (y : real) (h1 : term17) (h2 : term43) (h3 : term136 z x y) (h4 : term55 z x y) : False.
Proof. exact (@lem1600710 z x y h3 (@lem1600702 z x y h1 h2 h3 h4)). Qed.
Lemma lem1600714 (z : real) (x : real) (y : real) (h1 : term17) (h2 : term43) (h3 : term136 z x y) (h4 : term55 z x y) : term181.
Proof. exact (fun h0 : ~ False => @lem1600713 z x y h1 h2 h3 h4). Qed.
Lemma lem1600716 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1600717 : term181 = False.
Proof. exact (@lem1600716 False). Qed.
Lemma lem1600718 (z : real) (x : real) (y : real) (h1 : term17) (h2 : term43) (h3 : term136 z x y) (h4 : term55 z x y) : False.
Proof. exact (EQ_MP (@lem1600717) (@lem1600714 z x y h1 h2 h3 h4)). Qed.
Lemma lem1600719 (z : real) (x : real) (y : real) (h1 : term17) (h2 : term38) (h3 : term43) (h4 : term55 z x y) : False.
Proof. exact (or_elim (@lem1600031 z x y h4) (fun h0 : term135 z x y => @lem1600530 z x y h2 h0 h4) (fun h0 : term136 z x y => @lem1600718 z x y h1 h3 h0 h4)). Qed.
Lemma lem1600720 (z : real) (x : real) (y : real) (h1 : term17) (h2 : term38) (h3 : term43) (h4 : term55 z x y) : (term55 z x y) = False.
Proof. exact (prop_ext (fun h5 : term55 z x y => @lem1600719 z x y h1 h2 h3 h4) (fun h5 : False => @lem1600030 z x y h4)). Qed.
Lemma lem1600721 (z : real) (x : real) (y : real) (h1 : term17) (h2 : term38) (h3 : term43) (h4 : term55 z x y) : False.
Proof. exact (EQ_MP (@lem1600720 z x y h1 h2 h3 h4) (@lem1600030 z x y h4)). Qed.
Lemma lem1600722 (x : real) (y : real) (h1 : term17) (h2 : term38) (h3 : term43) (h4 : term66 x y) : False.
Proof. exact (ex_elim (@lem1599851 x y h4) (fun z : real => fun h0 : term65 x y z => @lem1600721 z x y h1 h2 h3 h0)). Qed.
Lemma lem1600723 (x : real) (h1 : term17) (h2 : term38) (h3 : term43) (h4 : term73 x) : False.
Proof. exact (ex_elim (@lem1599850 x h4) (fun y : real => fun h0 : term72 x y => @lem1600722 x y h1 h2 h3 h0)). Qed.
Lemma lem1600724 (h1 : term17) (h2 : term38) (h3 : term43) (h4 : term10) : False.
Proof. exact (ex_elim (@lem1599512 h4) (fun x : real => fun h0 : term78 x => @lem1600723 x h1 h2 h3 h0)). Qed.
Lemma lem1600725 (h1 : term38) (h2 : term43) (h3 : term10) : term15.
Proof. exact (fun h0 : term17 => @lem1600724 h0 h1 h2 h3). Qed.
Lemma lem1600726 : term15 = term16.
Proof. exact (@lem69 term17). Qed.
Lemma lem1600727 (h1 : term38) (h2 : term43) (h3 : term10) : term16.
Proof. exact (EQ_MP (@lem1600726) (@lem1600725 h1 h2 h3)). Qed.
Lemma lem1600728 (h1 : term43) (h2 : term10) : term20.
Proof. exact (fun h0 : term38 => @lem1600727 h0 h1 h2). Qed.
Lemma lem1600729 (h1 : term10) : term23.
Proof. exact (fun h0 : term43 => @lem1600728 h0 h1). Qed.
Lemma lem1600730 : term25.
Proof. exact (fun h0 : term10 => @lem1600729 h0). Qed.
Lemma lem1600731 : term11.
Proof. exact (EQ_MP (@lem1599396) (@lem1600730)). Qed.
Lemma lem1600733 : term11.
Proof. exact (@lem1599149 (@lem1600731)). Qed.
Lemma lem1600734 (h1 : term10) : term22.
Proof. exact (@lem1600733 (@lem1599134 h1)). Qed.
Lemma lem1600735 (h1 : term10) : term19.
Proof. exact (@lem1600734 h1 (@lem1369133)). Qed.
Lemma lem1600736 (h1 : term10) : term15.
Proof. exact (@lem1600735 h1 (@lem1599119)). Qed.
Lemma lem1600737 (h1 : term10) : False.
Proof. exact (@lem1600736 h1 (@lem1584226)). Qed.
Lemma lem1600738 (h1 : term10) : term10 = False.
Proof. exact (prop_ext (fun h2 : term10 => @lem1600737 h1) (fun h2 : False => @lem1599134 h1)). Qed.
Lemma lem1600739 (h1 : term10) : False.
Proof. exact (EQ_MP (@lem1600738 h1) (@lem1599134 h1)). Qed.
Lemma lem1600740 : term9.
Proof. exact (fun h0 : term10 => @lem1600739 h0). Qed.
Lemma lem1600741 : term8.
Proof. exact (EQ_MP (@lem1599133) (@lem1600740)). Qed.
