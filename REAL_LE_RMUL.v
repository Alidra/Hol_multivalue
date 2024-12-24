Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LE_RMUL_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import REAL_LE_LMUL_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1338712_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
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
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm69_spec.
Lemma lem1583208 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1583209 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1583210 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1583209 t1) (@lem1583208 t1)). Qed.
Lemma lem1583211 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1583210 t1 t2). Qed.
Lemma lem1583212 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1583213 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1583212 t1 t2) (@lem1583211 t1 t2)). Qed.
Lemma lem1583214 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1583213 t1 t2 t3). Qed.
Lemma lem1583215 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1583216 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1583215 t1 t2 t3) (@lem1583214 t1 t2 t3)). Qed.
Lemma lem1583217 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1583216 t1 t2 t3)). Qed.
Lemma lem1583219 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1583220 : term8 = term9.
Proof. exact (@lem1583219 term8). Qed.
Lemma lem1583221 : term9 = term8.
Proof. exact (SYM (@lem1583220)). Qed.
Lemma lem1583222 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1583225 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1583226 : term12.
Proof. exact (fun h0 : term11 => @lem1583225 h0). Qed.
Lemma lem1583227 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1583228 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1583229 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem1583227 h2 (@lem1583228 h1)). Qed.
Lemma lem1583230 (h1 : term11) : term13.
Proof. exact (fun h0 : term12 => @lem1583229 h1 h0). Qed.
Lemma lem1583231 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1583232 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem1583230 h1 (@lem1583231 h2)). Qed.
Lemma lem1583233 (h1 : term12) : term12.
Proof. exact (fun h0 : term11 => @lem1583232 h0 h1). Qed.
Lemma lem1583234 : term14.
Proof. exact (fun h0 : term12 => @lem1583233 h0). Qed.
Lemma lem1583237 : term12.
Proof. exact (@lem1583234 (@lem1583226)). Qed.
Lemma lem1583275 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1583276 : term15 = term16.
Proof. exact (@lem1583275 term17). Qed.
Lemma lem1583285 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem1583286 : term19 = term20.
Proof. exact (MK_COMB (@lem1583285) (@lem1583276)). Qed.
Lemma lem1583289 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem1583296 : term11 = term22.
Proof. exact (MK_COMB (@lem1583289) (@lem1583286)). Qed.
Lemma lem1583297 (y : real) (x : real) : ((real_mul x y) = (real_mul y x)) = ((real_mul x y) = (real_mul y x)).
Proof. exact (eq_refl ((real_mul x y) = (real_mul y x))). Qed.
Lemma lem1583298 (x : real) : (term23 x) = (term23 x).
Proof. exact (fun_ext (fun y : real => @lem1583297 y x)). Qed.
Lemma lem1583299 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1583300 (x : real) : (term24 x) = (term24 x).
Proof. exact (MK_COMB (@lem1583299) (@lem1583298 x)). Qed.
Lemma lem1583301 : term25 = term25.
Proof. exact (fun_ext (fun x : real => @lem1583300 x)). Qed.
Lemma lem1583302 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1583303 : term17 = term17.
Proof. exact (MK_COMB (@lem1583302) (@lem1583301)). Qed.
Lemma lem1583304 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1583305 : term16 = term16.
Proof. exact (MK_COMB (@lem1583304) (@lem1583303)). Qed.
Lemma lem1583314 (y : real) (x : real) (z : real) : (term26 y x z) = (term26 y x z).
Proof. exact (eq_refl (term26 y x z)). Qed.
Lemma lem1583315 (y : real) (x : real) : (term27 y x) = (term27 y x).
Proof. exact (fun_ext (fun z : real => @lem1583314 y x z)). Qed.
Lemma lem1583316 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1583317 (y : real) (x : real) : (term28 y x) = (term28 y x).
Proof. exact (MK_COMB (@lem1583316) (@lem1583315 y x)). Qed.
Lemma lem1583318 (x : real) : (term29 x) = (term29 x).
Proof. exact (fun_ext (fun y : real => @lem1583317 y x)). Qed.
Lemma lem1583319 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1583320 (x : real) : (term30 x) = (term30 x).
Proof. exact (MK_COMB (@lem1583319) (@lem1583318 x)). Qed.
Lemma lem1583321 : term31 = term31.
Proof. exact (fun_ext (fun x : real => @lem1583320 x)). Qed.
Lemma lem1583322 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1583323 : term32 = term32.
Proof. exact (MK_COMB (@lem1583322) (@lem1583321)). Qed.
Lemma lem1583324 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1583325 : term18 = term18.
Proof. exact (MK_COMB (@lem1583324) (@lem1583323)). Qed.
Lemma lem1583326 : term20 = term20.
Proof. exact (MK_COMB (@lem1583325) (@lem1583305)). Qed.
Lemma lem1583335 (x : real) (y : real) (z : real) : (term33 x y z) = (term33 x y z).
Proof. exact (eq_refl (term33 x y z)). Qed.
Lemma lem1583336 (x : real) (y : real) : (term34 x y) = (term34 x y).
Proof. exact (fun_ext (fun z : real => @lem1583335 x y z)). Qed.
Lemma lem1583337 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1583338 (x : real) (y : real) : (term35 x y) = (term35 x y).
Proof. exact (MK_COMB (@lem1583337) (@lem1583336 x y)). Qed.
Lemma lem1583339 (x : real) : (term36 x) = (term36 x).
Proof. exact (fun_ext (fun y : real => @lem1583338 x y)). Qed.
Lemma lem1583340 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1583341 (x : real) : (term37 x) = (term37 x).
Proof. exact (MK_COMB (@lem1583340) (@lem1583339 x)). Qed.
Lemma lem1583342 : term38 = term38.
Proof. exact (fun_ext (fun x : real => @lem1583341 x)). Qed.
Lemma lem1583343 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1583344 : term8 = term8.
Proof. exact (MK_COMB (@lem1583343) (@lem1583342)). Qed.
Lemma lem1583345 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1583346 : term10 = term10.
Proof. exact (MK_COMB (@lem1583345) (@lem1583344)). Qed.
Lemma lem1583347 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1583348 : term21 = term21.
Proof. exact (MK_COMB (@lem1583347) (@lem1583346)). Qed.
Lemma lem1583349 : term22 = term22.
Proof. exact (MK_COMB (@lem1583348) (@lem1583326)). Qed.
Lemma lem1583412 : term11 = term22.
Proof. exact (TRANS (@lem1583296) (@lem1583349)). Qed.
Lemma lem1583413 : term22 = term11.
Proof. exact (SYM (@lem1583412)). Qed.
Lemma lem1583414 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1583415 (h1 : term32) : term32.
Proof. exact (h1). Qed.
Lemma lem1583416 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem1583427 (x : real) (y : real) (z : real) : (term39 x y z) = (term40 x y z).
Proof. exact (@lem17362 (term41 x y z) (term42 x y z)). Qed.
Lemma lem1583428 (P : real -> Prop) : (term43 P) = (term44 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1583429 (x : real) (y : real) : (term45 x y) = (term46 x y).
Proof. exact (@lem1583428 (term34 x y)). Qed.
Lemma lem1583430 (x : real) (y : real) (z : real) : (term47 x y z) = (term33 x y z).
Proof. exact (eq_refl (term47 x y z)). Qed.
Lemma lem1583431 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1583432 (x : real) (y : real) (z : real) : (term48 x y z) = (term39 x y z).
Proof. exact (MK_COMB (@lem1583431) (@lem1583430 x y z)). Qed.
Lemma lem1583433 (x : real) (y : real) (z : real) : (term48 x y z) = (term40 x y z).
Proof. exact (TRANS (@lem1583432 x y z) (@lem1583427 x y z)). Qed.
Lemma lem1583434 (x : real) (y : real) : (term49 x y) = (term50 x y).
Proof. exact (fun_ext (fun z : real => @lem1583433 x y z)). Qed.
Lemma lem1583435 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1583436 (x : real) (y : real) : (term46 x y) = (term51 x y).
Proof. exact (MK_COMB (@lem1583435) (@lem1583434 x y)). Qed.
Lemma lem1583437 (x : real) (y : real) : (term45 x y) = (term51 x y).
Proof. exact (TRANS (@lem1583429 x y) (@lem1583436 x y)). Qed.
Lemma lem1583438 (P : real -> Prop) : (term43 P) = (term44 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1583439 (x : real) : (term52 x) = (term53 x).
Proof. exact (@lem1583438 (term36 x)). Qed.
Lemma lem1583440 (x : real) (y : real) : (term54 x y) = (term35 x y).
Proof. exact (eq_refl (term54 x y)). Qed.
Lemma lem1583441 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1583442 (x : real) (y : real) : (term55 x y) = (term45 x y).
Proof. exact (MK_COMB (@lem1583441) (@lem1583440 x y)). Qed.
Lemma lem1583443 (x : real) (y : real) : (term55 x y) = (term51 x y).
Proof. exact (TRANS (@lem1583442 x y) (@lem1583437 x y)). Qed.
Lemma lem1583444 (x : real) : (term56 x) = (term57 x).
Proof. exact (fun_ext (fun y : real => @lem1583443 x y)). Qed.
Lemma lem1583445 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1583446 (x : real) : (term53 x) = (term58 x).
Proof. exact (MK_COMB (@lem1583445) (@lem1583444 x)). Qed.
Lemma lem1583447 (x : real) : (term52 x) = (term58 x).
Proof. exact (TRANS (@lem1583439 x) (@lem1583446 x)). Qed.
Lemma lem1583448 (P : real -> Prop) : (term43 P) = (term44 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1583449 : term10 = term59.
Proof. exact (@lem1583448 term38). Qed.
Lemma lem1583450 (x : real) : (term60 x) = (term37 x).
Proof. exact (eq_refl (term60 x)). Qed.
Lemma lem1583451 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1583452 (x : real) : (term61 x) = (term52 x).
Proof. exact (MK_COMB (@lem1583451) (@lem1583450 x)). Qed.
Lemma lem1583453 (x : real) : (term61 x) = (term58 x).
Proof. exact (TRANS (@lem1583452 x) (@lem1583447 x)). Qed.
Lemma lem1583454 : term62 = term63.
Proof. exact (fun_ext (fun x : real => @lem1583453 x)). Qed.
Lemma lem1583455 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1583456 : term59 = term64.
Proof. exact (MK_COMB (@lem1583455) (@lem1583454)). Qed.
Lemma lem1583517 : term10 = term64.
Proof. exact (TRANS (@lem1583449) (@lem1583456)). Qed.
Lemma lem1583518 (h1 : term10) : term64.
Proof. exact (EQ_MP (@lem1583517) (@lem1583414 h1)). Qed.
Lemma lem1583525 (x : real) (y : real) (z : real) : (term65 x y z) = (term66 x y z).
Proof. exact (@lem17045 (term67 x) (real_le y z)). Qed.
Lemma lem1583526 (y : real) (x : real) (z : real) : (term68 y x z) = (term68 y x z).
Proof. exact (eq_refl (term68 y x z)). Qed.
Lemma lem1583527 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1583528 (x : real) (y : real) (z : real) : (term69 x y z) = (term70 x y z).
Proof. exact (MK_COMB (@lem1583527) (@lem1583525 x y z)). Qed.
Lemma lem1583529 (y : real) (x : real) (z : real) : (term71 y x z) = (term72 y x z).
Proof. exact (MK_COMB (@lem1583528 x y z) (@lem1583526 y x z)). Qed.
Lemma lem1583530 (y : real) (x : real) (z : real) : (term26 y x z) = (term71 y x z).
Proof. exact (@lem17265 (term73 x y z) (term68 y x z)). Qed.
Lemma lem1583531 (y : real) (x : real) (z : real) : (term26 y x z) = (term72 y x z).
Proof. exact (TRANS (@lem1583530 y x z) (@lem1583529 y x z)). Qed.
Lemma lem1583532 (y : real) (x : real) : (term27 y x) = (term74 y x).
Proof. exact (fun_ext (fun z : real => @lem1583531 y x z)). Qed.
Lemma lem1583533 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1583534 (y : real) (x : real) : (term28 y x) = (term75 y x).
Proof. exact (MK_COMB (@lem1583533) (@lem1583532 y x)). Qed.
Lemma lem1583535 (x : real) : (term29 x) = (term76 x).
Proof. exact (fun_ext (fun y : real => @lem1583534 y x)). Qed.
Lemma lem1583536 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1583537 (x : real) : (term30 x) = (term77 x).
Proof. exact (MK_COMB (@lem1583536) (@lem1583535 x)). Qed.
Lemma lem1583538 : term31 = term78.
Proof. exact (fun_ext (fun x : real => @lem1583537 x)). Qed.
Lemma lem1583539 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1583600 : term32 = term79.
Proof. exact (MK_COMB (@lem1583539) (@lem1583538)). Qed.
Lemma lem1583601 (h1 : term32) : term79.
Proof. exact (EQ_MP (@lem1583600) (@lem1583415 h1)). Qed.
Lemma lem1583602 (y : real) (x : real) : ((real_mul x y) = (real_mul y x)) = ((real_mul x y) = (real_mul y x)).
Proof. exact (eq_refl ((real_mul x y) = (real_mul y x))). Qed.
Lemma lem1583603 (x : real) : (term23 x) = (term23 x).
Proof. exact (fun_ext (fun y : real => @lem1583602 y x)). Qed.
Lemma lem1583604 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1583605 (x : real) : (term24 x) = (term24 x).
Proof. exact (MK_COMB (@lem1583604) (@lem1583603 x)). Qed.
Lemma lem1583606 : term25 = term25.
Proof. exact (fun_ext (fun x : real => @lem1583605 x)). Qed.
Lemma lem1583607 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1583620 : term17 = term17.
Proof. exact (MK_COMB (@lem1583607) (@lem1583606)). Qed.
Lemma lem1583621 (h1 : term17) : term17.
Proof. exact (EQ_MP (@lem1583620) (@lem1583416 h1)). Qed.
Lemma lem1583622 (x : real) (h1 : term58 x) : term58 x.
Proof. exact (h1). Qed.
Lemma lem1583623 (x : real) (y : real) (h1 : term51 x y) : term51 x y.
Proof. exact (h1). Qed.
Lemma lem1583661 (y : real) (x : real) (z : real) : (term72 y x z) = (term72 y x z).
Proof. exact (eq_refl (term72 y x z)). Qed.
Lemma lem1583662 (y : real) (x : real) : (term74 y x) = (term74 y x).
Proof. exact (fun_ext (fun z : real => @lem1583661 y x z)). Qed.
Lemma lem1583663 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1583664 (y : real) (x : real) : (term75 y x) = (term75 y x).
Proof. exact (MK_COMB (@lem1583663) (@lem1583662 y x)). Qed.
Lemma lem1583665 (x : real) : (term76 x) = (term76 x).
Proof. exact (fun_ext (fun y : real => @lem1583664 y x)). Qed.
Lemma lem1583666 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1583667 (x : real) : (term77 x) = (term77 x).
Proof. exact (MK_COMB (@lem1583666) (@lem1583665 x)). Qed.
Lemma lem1583668 : term78 = term78.
Proof. exact (fun_ext (fun x : real => @lem1583667 x)). Qed.
Lemma lem1583669 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1583670 : term79 = term79.
Proof. exact (MK_COMB (@lem1583669) (@lem1583668)). Qed.
Lemma lem1583671 (h1 : term32) : term79.
Proof. exact (EQ_MP (@lem1583670) (@lem1583601 h1)). Qed.
Lemma lem1583684 (y : real) (x : real) : ((real_mul x y) = (real_mul y x)) = ((real_mul x y) = (real_mul y x)).
Proof. exact (eq_refl ((real_mul x y) = (real_mul y x))). Qed.
Lemma lem1583685 (x : real) : (term23 x) = (term23 x).
Proof. exact (fun_ext (fun y : real => @lem1583684 y x)). Qed.
Lemma lem1583686 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1583687 (x : real) : (term24 x) = (term24 x).
Proof. exact (MK_COMB (@lem1583686) (@lem1583685 x)). Qed.
Lemma lem1583688 : term25 = term25.
Proof. exact (fun_ext (fun x : real => @lem1583687 x)). Qed.
Lemma lem1583689 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1583690 : term17 = term17.
Proof. exact (MK_COMB (@lem1583689) (@lem1583688)). Qed.
Lemma lem1583691 (h1 : term17) : term17.
Proof. exact (EQ_MP (@lem1583690) (@lem1583621 h1)). Qed.
Lemma lem1583727 (x : real) (y : real) (z : real) (h1 : term40 x y z) : term40 x y z.
Proof. exact (h1). Qed.
Lemma lem1583729 (x : real) (y : real) (z : real) (h1 : term40 x y z) : term41 x y z.
Proof. exact (proj1 (@lem1583727 x y z h1)). Qed.
Lemma lem1583745 (y : real) (x : real) (z : real) : (term72 y x z) = (term72 y x z).
Proof. exact (eq_refl (term72 y x z)). Qed.
Lemma lem1583746 (y : real) (x : real) : (term74 y x) = (term74 y x).
Proof. exact (fun_ext (fun z : real => @lem1583745 y x z)). Qed.
Lemma lem1583747 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1583748 (y : real) (x : real) : (term75 y x) = (term75 y x).
Proof. exact (MK_COMB (@lem1583747) (@lem1583746 y x)). Qed.
Lemma lem1583749 (x : real) : (term76 x) = (term76 x).
Proof. exact (fun_ext (fun y : real => @lem1583748 y x)). Qed.
Lemma lem1583750 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1583751 (x : real) : (term77 x) = (term77 x).
Proof. exact (MK_COMB (@lem1583750) (@lem1583749 x)). Qed.
Lemma lem1583752 : term78 = term78.
Proof. exact (fun_ext (fun x : real => @lem1583751 x)). Qed.
Lemma lem1583753 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1583755 : term79 = term79.
Proof. exact (MK_COMB (@lem1583753) (@lem1583752)). Qed.
Lemma lem1583756 (h1 : term32) : term79.
Proof. exact (EQ_MP (@lem1583755) (@lem1583671 h1)). Qed.
Lemma lem1583758 (y : real) (x : real) : ((real_mul x y) = (real_mul y x)) = ((real_mul x y) = (real_mul y x)).
Proof. exact (eq_refl ((real_mul x y) = (real_mul y x))). Qed.
Lemma lem1583759 (x : real) : (term23 x) = (term23 x).
Proof. exact (fun_ext (fun y : real => @lem1583758 y x)). Qed.
Lemma lem1583760 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1583761 (x : real) : (term24 x) = (term24 x).
Proof. exact (MK_COMB (@lem1583760) (@lem1583759 x)). Qed.
Lemma lem1583762 : term25 = term25.
Proof. exact (fun_ext (fun x : real => @lem1583761 x)). Qed.
Lemma lem1583763 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1583765 : term17 = term17.
Proof. exact (MK_COMB (@lem1583763) (@lem1583762)). Qed.
Lemma lem1583766 (h1 : term17) : term17.
Proof. exact (EQ_MP (@lem1583765) (@lem1583691 h1)). Qed.
Lemma lem1583779 (_25009 : real) (h1 : term32) : term80 _25009.
Proof. exact (@lem1583756 h1 _25009). Qed.
Lemma lem1583780 (_25009 : real) : (term80 _25009) = (term77 _25009).
Proof. exact (eq_refl (term80 _25009)). Qed.
Lemma lem1583781 (_25009 : real) (h1 : term32) : term77 _25009.
Proof. exact (EQ_MP (@lem1583780 _25009) (@lem1583779 _25009 h1)). Qed.
Lemma lem1583782 (_25009 : real) (_25010 : real) (h1 : term32) : term81 _25009 _25010.
Proof. exact (@lem1583781 _25009 h1 _25010). Qed.
Lemma lem1583783 (_25010 : real) (_25009 : real) : (term81 _25009 _25010) = (term75 _25010 _25009).
Proof. exact (eq_refl (term81 _25009 _25010)). Qed.
Lemma lem1583784 (_25010 : real) (_25009 : real) (h1 : term32) : term75 _25010 _25009.
Proof. exact (EQ_MP (@lem1583783 _25010 _25009) (@lem1583782 _25009 _25010 h1)). Qed.
Lemma lem1583785 (_25010 : real) (_25009 : real) (_25011 : real) (h1 : term32) : term82 _25010 _25009 _25011.
Proof. exact (@lem1583784 _25010 _25009 h1 _25011). Qed.
Lemma lem1583786 (_25010 : real) (_25009 : real) (_25011 : real) : (term82 _25010 _25009 _25011) = (term72 _25010 _25009 _25011).
Proof. exact (eq_refl (term82 _25010 _25009 _25011)). Qed.
Lemma lem1583787 (_25010 : real) (_25009 : real) (_25011 : real) (h1 : term32) : term72 _25010 _25009 _25011.
Proof. exact (EQ_MP (@lem1583786 _25010 _25009 _25011) (@lem1583785 _25010 _25009 _25011 h1)). Qed.
Lemma lem1583788 (_25012 : real) (h1 : term17) : term83 _25012.
Proof. exact (@lem1583766 h1 _25012). Qed.
Lemma lem1583789 (_25012 : real) : (term83 _25012) = (term24 _25012).
Proof. exact (eq_refl (term83 _25012)). Qed.
Lemma lem1583790 (_25012 : real) (h1 : term17) : term24 _25012.
Proof. exact (EQ_MP (@lem1583789 _25012) (@lem1583788 _25012 h1)). Qed.
Lemma lem1583791 (_25012 : real) (_25013 : real) (h1 : term17) : term84 _25012 _25013.
Proof. exact (@lem1583790 _25012 h1 _25013). Qed.
Lemma lem1583792 (_25013 : real) (_25012 : real) : (term84 _25012 _25013) = ((real_mul _25012 _25013) = (real_mul _25013 _25012)).
Proof. exact (eq_refl (term84 _25012 _25013)). Qed.
Lemma lem1583804 (_25010 : real) (_25009 : real) (_25011 : real) : (term72 _25010 _25009 _25011) = (term85 _25010 _25009 _25011).
Proof. exact (@lem1583217 (term86 _25009) (term87 _25010 _25011) (term68 _25010 _25009 _25011)). Qed.
Lemma lem1583805 (_25010 : real) (_25009 : real) (_25011 : real) (h1 : term32) : term85 _25010 _25009 _25011.
Proof. exact (EQ_MP (@lem1583804 _25010 _25009 _25011) (@lem1583787 _25010 _25009 _25011 h1)). Qed.
Lemma lem1583809 (x : real) (y : real) (z : real) (h1 : term40 x y z) : term88 x y z.
Proof. exact (proj2 (@lem1583727 x y z h1)). Qed.
Lemma lem1583814 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1583815 (_25014 : real) (_25016 : real) (h1 : _25014 = _25016) : _25014 = _25016.
Proof. exact (h1). Qed.
Lemma lem1583816 (_25015 : real) (_25017 : real) (h1 : _25015 = _25017) : _25015 = _25017.
Proof. exact (h1). Qed.
Lemma lem1583817 (_25014 : real) (_25016 : real) (h1 : _25014 = _25016) : (real_le _25014) = (real_le _25016).
Proof. exact (MK_COMB (@lem1583814) (@lem1583815 _25014 _25016 h1)). Qed.
Lemma lem1583818 (_25014 : real) (_25016 : real) (_25015 : real) (_25017 : real) (h1 : _25014 = _25016) (h2 : _25015 = _25017) : (real_le _25014 _25015) = (real_le _25016 _25017).
Proof. exact (MK_COMB (@lem1583817 _25014 _25016 h1) (@lem1583816 _25015 _25017 h2)). Qed.
Lemma lem1583820 (b : Prop) (a : Prop) : term89 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem1583821 (_25016 : real) (_25017 : real) (_25014 : real) (_25015 : real) : term90 _25016 _25017 _25014 _25015.
Proof. exact (@lem1583820 (real_le _25016 _25017) (real_le _25014 _25015)). Qed.
Lemma lem1583822 (_25014 : real) (_25016 : real) (_25015 : real) (_25017 : real) (h1 : _25014 = _25016) (h2 : _25015 = _25017) : term91 _25016 _25017 _25014 _25015.
Proof. exact (@lem1583821 _25016 _25017 _25014 _25015 (@lem1583818 _25014 _25016 _25015 _25017 h1 h2)). Qed.
Lemma lem1583823 (_25017 : real) (_25015 : real) (_25014 : real) (_25016 : real) (h1 : _25014 = _25016) : term92 _25016 _25017 _25014 _25015.
Proof. exact (fun h0 : _25015 = _25017 => @lem1583822 _25014 _25016 _25015 _25017 h1 h0). Qed.
Lemma lem1583825 (a : Prop) (b : Prop) : (a -> b) = (term93 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1583826 (_25016 : real) (_25017 : real) (_25014 : real) (_25015 : real) : (term92 _25016 _25017 _25014 _25015) = (term94 _25016 _25017 _25014 _25015).
Proof. exact (@lem1583825 (_25015 = _25017) (term91 _25016 _25017 _25014 _25015)). Qed.
Lemma lem1583827 (_25017 : real) (_25015 : real) (_25014 : real) (_25016 : real) (h1 : _25014 = _25016) : term94 _25016 _25017 _25014 _25015.
Proof. exact (EQ_MP (@lem1583826 _25016 _25017 _25014 _25015) (@lem1583823 _25017 _25015 _25014 _25016 h1)). Qed.
Lemma lem1583828 (_25016 : real) (_25017 : real) (_25014 : real) (_25015 : real) : term95 _25016 _25017 _25014 _25015.
Proof. exact (fun h0 : _25014 = _25016 => @lem1583827 _25017 _25015 _25014 _25016 h0). Qed.
Lemma lem1583830 (a : Prop) (b : Prop) : (a -> b) = (term93 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1583831 (_25016 : real) (_25017 : real) (_25014 : real) (_25015 : real) : (term95 _25016 _25017 _25014 _25015) = (term96 _25016 _25017 _25014 _25015).
Proof. exact (@lem1583830 (_25014 = _25016) (term94 _25016 _25017 _25014 _25015)). Qed.
Lemma lem1583832 (_25016 : real) (_25017 : real) (_25014 : real) (_25015 : real) : term96 _25016 _25017 _25014 _25015.
Proof. exact (EQ_MP (@lem1583831 _25016 _25017 _25014 _25015) (@lem1583828 _25016 _25017 _25014 _25015)). Qed.
Lemma lem1583869 (_25013 : real) (_25012 : real) (h1 : term17) : (real_mul _25012 _25013) = (real_mul _25013 _25012).
Proof. exact (EQ_MP (@lem1583792 _25013 _25012) (@lem1583791 _25012 _25013 h1)). Qed.
Lemma lem1583870 (x : real) (z : real) (h1 : term17) : (real_mul z x) = (real_mul x z).
Proof. exact (@lem1583869 x z h1). Qed.
Lemma lem1583871 (x : real) (z : real) (h1 : term17) : term97 x z.
Proof. exact (fun h0 : term98 x z => @lem1583870 x z h1). Qed.
Lemma lem1583873 (p : Prop) : (term99 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1583874 (x : real) (z : real) : (term97 x z) = ((real_mul z x) = (real_mul x z)).
Proof. exact (@lem1583873 ((real_mul z x) = (real_mul x z))). Qed.
Lemma lem1583875 (x : real) (z : real) (h1 : term17) : (real_mul z x) = (real_mul x z).
Proof. exact (EQ_MP (@lem1583874 x z) (@lem1583871 x z h1)). Qed.
Lemma lem1583877 (_25013 : real) (_25012 : real) (h1 : term17) : (real_mul _25012 _25013) = (real_mul _25013 _25012).
Proof. exact (EQ_MP (@lem1583792 _25013 _25012) (@lem1583791 _25012 _25013 h1)). Qed.
Lemma lem1583878 (y : real) (z : real) (h1 : term17) : (real_mul z y) = (real_mul y z).
Proof. exact (@lem1583877 y z h1). Qed.
Lemma lem1583879 (y : real) (z : real) (h1 : term17) : term97 y z.
Proof. exact (fun h0 : term98 y z => @lem1583878 y z h1). Qed.
Lemma lem1583881 (p : Prop) : (term99 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1583882 (y : real) (z : real) : (term97 y z) = ((real_mul z y) = (real_mul y z)).
Proof. exact (@lem1583881 ((real_mul z y) = (real_mul y z))). Qed.
Lemma lem1583883 (y : real) (z : real) (h1 : term17) : (real_mul z y) = (real_mul y z).
Proof. exact (EQ_MP (@lem1583882 y z) (@lem1583879 y z h1)). Qed.
Lemma lem1583885 (x : real) (y : real) (z : real) (h1 : term40 x y z) : term67 z.
Proof. exact (proj2 (@lem1583729 x y z h1)). Qed.
Lemma lem1583886 (x : real) (y : real) (z : real) (h1 : term40 x y z) : term100 z.
Proof. exact (fun h0 : term86 z => @lem1583885 x y z h1). Qed.
Lemma lem1583888 (p : Prop) : (term99 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1583889 (z : real) : (term100 z) = (term67 z).
Proof. exact (@lem1583888 (term67 z)). Qed.
Lemma lem1583890 (x : real) (y : real) (z : real) (h1 : term40 x y z) : term67 z.
Proof. exact (EQ_MP (@lem1583889 z) (@lem1583886 x y z h1)). Qed.
Lemma lem1583892 (x : real) (y : real) (z : real) (h1 : term40 x y z) : real_le x y.
Proof. exact (proj1 (@lem1583729 x y z h1)). Qed.
Lemma lem1583893 (x : real) (y : real) (z : real) (h1 : term40 x y z) : term101 x y.
Proof. exact (fun h0 : term87 x y => @lem1583892 x y z h1). Qed.
Lemma lem1583895 (p : Prop) : (term99 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1583896 (x : real) (y : real) : (term101 x y) = (real_le x y).
Proof. exact (@lem1583895 (real_le x y)). Qed.
Lemma lem1583897 (x : real) (y : real) (z : real) (h1 : term40 x y z) : real_le x y.
Proof. exact (EQ_MP (@lem1583896 x y) (@lem1583893 x y z h1)). Qed.
Lemma lem1583903 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1583904 (_25010 : real) (_25009 : real) (_25011 : real) : (term85 _25010 _25009 _25011) = (term102 _25010 _25009 _25011).
Proof. exact (@lem1583903 (term87 _25010 _25011) (term86 _25009) (term68 _25010 _25009 _25011)). Qed.
Lemma lem1583918 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1583919 (_25010 : real) (_25011 : real) (_25009 : real) : (term103 _25010 _25009 _25011) = (term104 _25010 _25011 _25009).
Proof. exact (@lem1583918 (term68 _25010 _25009 _25011) (term86 _25009)). Qed.
Lemma lem1583925 (_25010 : real) (_25011 : real) : (term105 _25010 _25011) = (term105 _25010 _25011).
Proof. exact (eq_refl (term105 _25010 _25011)). Qed.
Lemma lem1583926 (_25010 : real) (_25011 : real) (_25009 : real) : (term102 _25010 _25009 _25011) = (term106 _25010 _25011 _25009).
Proof. exact (MK_COMB (@lem1583925 _25010 _25011) (@lem1583919 _25010 _25011 _25009)). Qed.
Lemma lem1583930 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1583931 (_25010 : real) (_25011 : real) (_25009 : real) : (term106 _25010 _25011 _25009) = (term107 _25010 _25011 _25009).
Proof. exact (@lem1583930 (term68 _25010 _25009 _25011) (term87 _25010 _25011) (term86 _25009)). Qed.
Lemma lem1583947 (_25010 : real) (_25011 : real) (_25009 : real) : (term102 _25010 _25009 _25011) = (term107 _25010 _25011 _25009).
Proof. exact (TRANS (@lem1583926 _25010 _25011 _25009) (@lem1583931 _25010 _25011 _25009)). Qed.
Lemma lem1583948 (_25010 : real) (_25011 : real) (_25009 : real) : (term85 _25010 _25009 _25011) = (term107 _25010 _25011 _25009).
Proof. exact (TRANS (@lem1583904 _25010 _25009 _25011) (@lem1583947 _25010 _25011 _25009)). Qed.
Lemma lem1583949 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1583950 (_25010 : real) (_25011 : real) (_25009 : real) : (term108 _25010 _25009 _25011) = (term109 _25010 _25011 _25009).
Proof. exact (MK_COMB (@lem1583949) (@lem1583948 _25010 _25011 _25009)). Qed.
Lemma lem1583964 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1583965 (_25010 : real) (_25011 : real) (_25009 : real) : (term66 _25009 _25010 _25011) = (term110 _25010 _25011 _25009).
Proof. exact (@lem1583964 (term87 _25010 _25011) (term86 _25009)). Qed.
Lemma lem1583971 (_25010 : real) (_25009 : real) (_25011 : real) : (term111 _25010 _25009 _25011) = (term111 _25010 _25009 _25011).
Proof. exact (eq_refl (term111 _25010 _25009 _25011)). Qed.
Lemma lem1583972 (_25010 : real) (_25011 : real) (_25009 : real) : (term112 _25009 _25010 _25011) = (term107 _25010 _25011 _25009).
Proof. exact (MK_COMB (@lem1583971 _25010 _25009 _25011) (@lem1583965 _25010 _25011 _25009)). Qed.
Lemma lem1583983 (_25010 : real) (_25011 : real) (_25009 : real) : ((term85 _25010 _25009 _25011) = (term112 _25009 _25010 _25011)) = ((term107 _25010 _25011 _25009) = (term107 _25010 _25011 _25009)).
Proof. exact (MK_COMB (@lem1583950 _25010 _25011 _25009) (@lem1583972 _25010 _25011 _25009)). Qed.
Lemma lem1583985 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1583986 (x : Prop) : (x = x) = True.
Proof. exact (@lem1583985 Prop x). Qed.
Lemma lem1583987 (_25010 : real) (_25011 : real) (_25009 : real) : ((term107 _25010 _25011 _25009) = (term107 _25010 _25011 _25009)) = True.
Proof. exact (@lem1583986 (term107 _25010 _25011 _25009)). Qed.
Lemma lem1583988 (_25009 : real) (_25010 : real) (_25011 : real) : ((term85 _25010 _25009 _25011) = (term112 _25009 _25010 _25011)) = True.
Proof. exact (TRANS (@lem1583983 _25010 _25011 _25009) (@lem1583987 _25010 _25011 _25009)). Qed.
Lemma lem1583989 (_25009 : real) (_25010 : real) (_25011 : real) : True = ((term85 _25010 _25009 _25011) = (term112 _25009 _25010 _25011)).
Proof. exact (SYM (@lem1583988 _25009 _25010 _25011)). Qed.
Lemma lem1583990 (_25009 : real) (_25010 : real) (_25011 : real) : (term85 _25010 _25009 _25011) = (term112 _25009 _25010 _25011).
Proof. exact (EQ_MP (@lem1583989 _25009 _25010 _25011) (@lem0)). Qed.
Lemma lem1583991 (_25009 : real) (_25010 : real) (_25011 : real) (h1 : term32) : term112 _25009 _25010 _25011.
Proof. exact (EQ_MP (@lem1583990 _25009 _25010 _25011) (@lem1583805 _25010 _25009 _25011 h1)). Qed.
Lemma lem1583993 (b : Prop) (a : Prop) : (a \/ b) = (term113 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1583994 (_25010 : real) (_25009 : real) (_25011 : real) : (term112 _25009 _25010 _25011) = (term114 _25010 _25009 _25011).
Proof. exact (@lem1583993 (term66 _25009 _25010 _25011) (term68 _25010 _25009 _25011)). Qed.
Lemma lem1583996 (a : Prop) (b : Prop) : (term115 a b) = (term116 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1583997 (_25009 : real) (_25010 : real) (_25011 : real) : (term117 _25009 _25010 _25011) = (term118 _25009 _25010 _25011).
Proof. exact (@lem1583996 (term86 _25009) (term87 _25010 _25011)). Qed.
Lemma lem1583999 (a : Prop) : (term119 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1584000 (_25009 : real) : (term120 _25009) = (term67 _25009).
Proof. exact (@lem1583999 (term67 _25009)). Qed.
Lemma lem1584001 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1584002 (_25009 : real) : (term121 _25009) = (term122 _25009).
Proof. exact (MK_COMB (@lem1584001) (@lem1584000 _25009)). Qed.
Lemma lem1584004 (a : Prop) : (term119 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1584005 (_25010 : real) (_25011 : real) : (term123 _25010 _25011) = (real_le _25010 _25011).
Proof. exact (@lem1584004 (real_le _25010 _25011)). Qed.
Lemma lem1584006 (_25009 : real) (_25010 : real) (_25011 : real) : (term118 _25009 _25010 _25011) = (term73 _25009 _25010 _25011).
Proof. exact (MK_COMB (@lem1584002 _25009) (@lem1584005 _25010 _25011)). Qed.
Lemma lem1584007 (_25009 : real) (_25010 : real) (_25011 : real) : (term117 _25009 _25010 _25011) = (term73 _25009 _25010 _25011).
Proof. exact (TRANS (@lem1583997 _25009 _25010 _25011) (@lem1584006 _25009 _25010 _25011)). Qed.
Lemma lem1584008 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1584009 (_25009 : real) (_25010 : real) (_25011 : real) : (term124 _25009 _25010 _25011) = (term125 _25009 _25010 _25011).
Proof. exact (MK_COMB (@lem1584008) (@lem1584007 _25009 _25010 _25011)). Qed.
Lemma lem1584010 (_25010 : real) (_25009 : real) (_25011 : real) : (term68 _25010 _25009 _25011) = (term68 _25010 _25009 _25011).
Proof. exact (eq_refl (term68 _25010 _25009 _25011)). Qed.
Lemma lem1584011 (_25010 : real) (_25009 : real) (_25011 : real) : (term114 _25010 _25009 _25011) = (term26 _25010 _25009 _25011).
Proof. exact (MK_COMB (@lem1584009 _25009 _25010 _25011) (@lem1584010 _25010 _25009 _25011)). Qed.
Lemma lem1584012 (_25010 : real) (_25009 : real) (_25011 : real) : (term112 _25009 _25010 _25011) = (term26 _25010 _25009 _25011).
Proof. exact (TRANS (@lem1583994 _25010 _25009 _25011) (@lem1584011 _25010 _25009 _25011)). Qed.
Lemma lem1584014 (x : real) (y : real) (z : real) (h1 : term40 x y z) : term73 z x y.
Proof. exact (conj (@lem1583890 x y z h1) (@lem1583897 x y z h1)). Qed.
Lemma lem1584016 (_25010 : real) (_25009 : real) (_25011 : real) (h1 : term32) : term26 _25010 _25009 _25011.
Proof. exact (EQ_MP (@lem1584012 _25010 _25009 _25011) (@lem1583991 _25009 _25010 _25011 h1)). Qed.
Lemma lem1584017 (x : real) (z : real) (y : real) (h1 : term32) : term26 x z y.
Proof. exact (@lem1584016 x z y h1). Qed.
Lemma lem1584020 (x : real) (y : real) (z : real) (h1 : term32) (h2 : term40 x y z) : term68 x z y.
Proof. exact (@lem1584017 x z y h1 (@lem1584014 x y z h2)). Qed.
Lemma lem1584021 (x : real) (y : real) (z : real) (h1 : term32) (h2 : term40 x y z) : term126 x z y.
Proof. exact (fun h0 : term127 x z y => @lem1584020 x y z h1 h2). Qed.
Lemma lem1584023 (p : Prop) : (term99 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1584024 (x : real) (z : real) (y : real) : (term126 x z y) = (term68 x z y).
Proof. exact (@lem1584023 (term68 x z y)). Qed.
Lemma lem1584025 (x : real) (y : real) (z : real) (h1 : term32) (h2 : term40 x y z) : term68 x z y.
Proof. exact (EQ_MP (@lem1584024 x z y) (@lem1584021 x y z h1 h2)). Qed.
Lemma lem1584043 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1584044 (_25016 : real) (_25017 : real) (_25014 : real) (_25015 : real) : (term94 _25016 _25017 _25014 _25015) = (term128 _25016 _25017 _25014 _25015).
Proof. exact (@lem1584043 (real_le _25016 _25017) (term129 _25015 _25017) (term87 _25014 _25015)). Qed.
Lemma lem1584062 (_25014 : real) (_25016 : real) : (term130 _25014 _25016) = (term130 _25014 _25016).
Proof. exact (eq_refl (term130 _25014 _25016)). Qed.
Lemma lem1584063 (_25016 : real) (_25017 : real) (_25014 : real) (_25015 : real) : (term96 _25016 _25017 _25014 _25015) = (term131 _25016 _25017 _25014 _25015).
Proof. exact (MK_COMB (@lem1584062 _25014 _25016) (@lem1584044 _25016 _25017 _25014 _25015)). Qed.
Lemma lem1584067 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1584068 (_25016 : real) (_25017 : real) (_25014 : real) (_25015 : real) : (term131 _25016 _25017 _25014 _25015) = (term132 _25016 _25017 _25014 _25015).
Proof. exact (@lem1584067 (real_le _25016 _25017) (term129 _25014 _25016) (term133 _25017 _25014 _25015)). Qed.
Lemma lem1584098 (_25016 : real) (_25017 : real) (_25014 : real) (_25015 : real) : (term96 _25016 _25017 _25014 _25015) = (term132 _25016 _25017 _25014 _25015).
Proof. exact (TRANS (@lem1584063 _25016 _25017 _25014 _25015) (@lem1584068 _25016 _25017 _25014 _25015)). Qed.
Lemma lem1584099 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1584100 (_25016 : real) (_25017 : real) (_25014 : real) (_25015 : real) : (term134 _25016 _25017 _25014 _25015) = (term135 _25016 _25017 _25014 _25015).
Proof. exact (MK_COMB (@lem1584099) (@lem1584098 _25016 _25017 _25014 _25015)). Qed.
Lemma lem1584130 (_25016 : real) (_25017 : real) (_25014 : real) (_25015 : real) : (term132 _25016 _25017 _25014 _25015) = (term132 _25016 _25017 _25014 _25015).
Proof. exact (eq_refl (term132 _25016 _25017 _25014 _25015)). Qed.
Lemma lem1584131 (_25016 : real) (_25017 : real) (_25014 : real) (_25015 : real) : ((term96 _25016 _25017 _25014 _25015) = (term132 _25016 _25017 _25014 _25015)) = ((term132 _25016 _25017 _25014 _25015) = (term132 _25016 _25017 _25014 _25015)).
Proof. exact (MK_COMB (@lem1584100 _25016 _25017 _25014 _25015) (@lem1584130 _25016 _25017 _25014 _25015)). Qed.
Lemma lem1584133 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1584134 (x : Prop) : (x = x) = True.
Proof. exact (@lem1584133 Prop x). Qed.
Lemma lem1584135 (_25016 : real) (_25017 : real) (_25014 : real) (_25015 : real) : ((term132 _25016 _25017 _25014 _25015) = (term132 _25016 _25017 _25014 _25015)) = True.
Proof. exact (@lem1584134 (term132 _25016 _25017 _25014 _25015)). Qed.
Lemma lem1584136 (_25016 : real) (_25017 : real) (_25014 : real) (_25015 : real) : ((term96 _25016 _25017 _25014 _25015) = (term132 _25016 _25017 _25014 _25015)) = True.
Proof. exact (TRANS (@lem1584131 _25016 _25017 _25014 _25015) (@lem1584135 _25016 _25017 _25014 _25015)). Qed.
Lemma lem1584137 (_25016 : real) (_25017 : real) (_25014 : real) (_25015 : real) : True = ((term96 _25016 _25017 _25014 _25015) = (term132 _25016 _25017 _25014 _25015)).
Proof. exact (SYM (@lem1584136 _25016 _25017 _25014 _25015)). Qed.
Lemma lem1584138 (_25016 : real) (_25017 : real) (_25014 : real) (_25015 : real) : (term96 _25016 _25017 _25014 _25015) = (term132 _25016 _25017 _25014 _25015).
Proof. exact (EQ_MP (@lem1584137 _25016 _25017 _25014 _25015) (@lem0)). Qed.
Lemma lem1584139 (_25016 : real) (_25017 : real) (_25014 : real) (_25015 : real) : term132 _25016 _25017 _25014 _25015.
Proof. exact (EQ_MP (@lem1584138 _25016 _25017 _25014 _25015) (@lem1583832 _25016 _25017 _25014 _25015)). Qed.
Lemma lem1584141 (b : Prop) (a : Prop) : (a \/ b) = (term113 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1584142 (_25014 : real) (_25015 : real) (_25016 : real) (_25017 : real) : (term132 _25016 _25017 _25014 _25015) = (term136 _25014 _25015 _25016 _25017).
Proof. exact (@lem1584141 (term137 _25016 _25017 _25014 _25015) (real_le _25016 _25017)). Qed.
Lemma lem1584144 (a : Prop) (b : Prop) : (term115 a b) = (term116 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1584145 (_25016 : real) (_25017 : real) (_25014 : real) (_25015 : real) : (term138 _25016 _25017 _25014 _25015) = (term139 _25016 _25017 _25014 _25015).
Proof. exact (@lem1584144 (term129 _25014 _25016) (term133 _25017 _25014 _25015)). Qed.
Lemma lem1584147 (a : Prop) : (term119 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1584148 (_25014 : real) (_25016 : real) : (term140 _25014 _25016) = (_25014 = _25016).
Proof. exact (@lem1584147 (_25014 = _25016)). Qed.
Lemma lem1584149 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1584150 (_25014 : real) (_25016 : real) : (term141 _25014 _25016) = (term142 _25014 _25016).
Proof. exact (MK_COMB (@lem1584149) (@lem1584148 _25014 _25016)). Qed.
Lemma lem1584152 (a : Prop) (b : Prop) : (term115 a b) = (term116 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1584153 (_25017 : real) (_25014 : real) (_25015 : real) : (term143 _25017 _25014 _25015) = (term144 _25017 _25014 _25015).
Proof. exact (@lem1584152 (term129 _25015 _25017) (term87 _25014 _25015)). Qed.
Lemma lem1584155 (a : Prop) : (term119 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1584156 (_25015 : real) (_25017 : real) : (term140 _25015 _25017) = (_25015 = _25017).
Proof. exact (@lem1584155 (_25015 = _25017)). Qed.
Lemma lem1584157 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1584158 (_25015 : real) (_25017 : real) : (term141 _25015 _25017) = (term142 _25015 _25017).
Proof. exact (MK_COMB (@lem1584157) (@lem1584156 _25015 _25017)). Qed.
Lemma lem1584160 (a : Prop) : (term119 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1584161 (_25014 : real) (_25015 : real) : (term123 _25014 _25015) = (real_le _25014 _25015).
Proof. exact (@lem1584160 (real_le _25014 _25015)). Qed.
Lemma lem1584162 (_25017 : real) (_25014 : real) (_25015 : real) : (term144 _25017 _25014 _25015) = (term145 _25017 _25014 _25015).
Proof. exact (MK_COMB (@lem1584158 _25015 _25017) (@lem1584161 _25014 _25015)). Qed.
Lemma lem1584163 (_25017 : real) (_25014 : real) (_25015 : real) : (term143 _25017 _25014 _25015) = (term145 _25017 _25014 _25015).
Proof. exact (TRANS (@lem1584153 _25017 _25014 _25015) (@lem1584162 _25017 _25014 _25015)). Qed.
Lemma lem1584164 (_25016 : real) (_25017 : real) (_25014 : real) (_25015 : real) : (term139 _25016 _25017 _25014 _25015) = (term146 _25016 _25017 _25014 _25015).
Proof. exact (MK_COMB (@lem1584150 _25014 _25016) (@lem1584163 _25017 _25014 _25015)). Qed.
Lemma lem1584165 (_25016 : real) (_25017 : real) (_25014 : real) (_25015 : real) : (term138 _25016 _25017 _25014 _25015) = (term146 _25016 _25017 _25014 _25015).
Proof. exact (TRANS (@lem1584145 _25016 _25017 _25014 _25015) (@lem1584164 _25016 _25017 _25014 _25015)). Qed.
Lemma lem1584166 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1584167 (_25016 : real) (_25017 : real) (_25014 : real) (_25015 : real) : (term147 _25016 _25017 _25014 _25015) = (term148 _25016 _25017 _25014 _25015).
Proof. exact (MK_COMB (@lem1584166) (@lem1584165 _25016 _25017 _25014 _25015)). Qed.
Lemma lem1584168 (_25016 : real) (_25017 : real) : (real_le _25016 _25017) = (real_le _25016 _25017).
Proof. exact (eq_refl (real_le _25016 _25017)). Qed.
Lemma lem1584169 (_25014 : real) (_25015 : real) (_25016 : real) (_25017 : real) : (term136 _25014 _25015 _25016 _25017) = (term149 _25014 _25015 _25016 _25017).
Proof. exact (MK_COMB (@lem1584167 _25016 _25017 _25014 _25015) (@lem1584168 _25016 _25017)). Qed.
Lemma lem1584170 (_25014 : real) (_25015 : real) (_25016 : real) (_25017 : real) : (term132 _25016 _25017 _25014 _25015) = (term149 _25014 _25015 _25016 _25017).
Proof. exact (TRANS (@lem1584142 _25014 _25015 _25016 _25017) (@lem1584169 _25014 _25015 _25016 _25017)). Qed.
Lemma lem1584172 (x : real) (y : real) (z : real) (h1 : term32) (h2 : term17) (h3 : term40 x y z) : term150 x z y.
Proof. exact (conj (@lem1583883 y z h2) (@lem1584025 x y z h1 h3)). Qed.
Lemma lem1584173 (x : real) (y : real) (z : real) (h1 : term32) (h2 : term17) (h3 : term40 x y z) : term151 x z y.
Proof. exact (conj (@lem1583875 x z h2) (@lem1584172 x y z h1 h2 h3)). Qed.
Lemma lem1584175 (_25014 : real) (_25015 : real) (_25016 : real) (_25017 : real) : term149 _25014 _25015 _25016 _25017.
Proof. exact (EQ_MP (@lem1584170 _25014 _25015 _25016 _25017) (@lem1584139 _25016 _25017 _25014 _25015)). Qed.
Lemma lem1584176 (x : real) (y : real) (z : real) : term152 x y z.
Proof. exact (@lem1584175 (real_mul z x) (real_mul z y) (real_mul x z) (real_mul y z)). Qed.
Lemma lem1584179 (x : real) (y : real) (z : real) (h1 : term32) (h2 : term17) (h3 : term40 x y z) : term42 x y z.
Proof. exact (@lem1584176 x y z (@lem1584173 x y z h1 h2 h3)). Qed.
Lemma lem1584180 (x : real) (y : real) (z : real) (h1 : term32) (h2 : term17) (h3 : term40 x y z) : term153 x y z.
Proof. exact (fun h0 : term88 x y z => @lem1584179 x y z h1 h2 h3). Qed.
Lemma lem1584182 (p : Prop) : (term99 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1584183 (x : real) (y : real) (z : real) : (term153 x y z) = (term42 x y z).
Proof. exact (@lem1584182 (term42 x y z)). Qed.
Lemma lem1584184 (x : real) (y : real) (z : real) (h1 : term32) (h2 : term17) (h3 : term40 x y z) : term42 x y z.
Proof. exact (EQ_MP (@lem1584183 x y z) (@lem1584180 x y z h1 h2 h3)). Qed.
Lemma lem1584187 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1584189 (x : real) (y : real) (z : real) : (term88 x y z) = (term154 x y z).
Proof. exact (@lem1584187 (term42 x y z)). Qed.
Lemma lem1584192 (x : real) (y : real) (z : real) (h1 : term40 x y z) : term154 x y z.
Proof. exact (EQ_MP (@lem1584189 x y z) (@lem1583809 x y z h1)). Qed.
Lemma lem1584195 (x : real) (y : real) (z : real) (h1 : term32) (h2 : term17) (h3 : term40 x y z) : False.
Proof. exact (@lem1584192 x y z h3 (@lem1584184 x y z h1 h2 h3)). Qed.
Lemma lem1584196 (x : real) (y : real) (z : real) (h1 : term32) (h2 : term17) (h3 : term40 x y z) : term155.
Proof. exact (fun h0 : ~ False => @lem1584195 x y z h1 h2 h3). Qed.
Lemma lem1584198 (p : Prop) : (term99 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1584199 : term155 = False.
Proof. exact (@lem1584198 False). Qed.
Lemma lem1584200 (x : real) (y : real) (z : real) (h1 : term32) (h2 : term17) (h3 : term40 x y z) : False.
Proof. exact (EQ_MP (@lem1584199) (@lem1584196 x y z h1 h2 h3)). Qed.
Lemma lem1584201 (x : real) (y : real) (z : real) (h1 : term32) (h2 : term17) (h3 : term40 x y z) : term17 = False.
Proof. exact (prop_ext (fun h4 : term17 => @lem1584200 x y z h1 h2 h3) (fun h4 : False => @lem1583766 h2)). Qed.
Lemma lem1584202 (x : real) (y : real) (z : real) (h1 : term32) (h2 : term17) (h3 : term40 x y z) : False.
Proof. exact (EQ_MP (@lem1584201 x y z h1 h2 h3) (@lem1583766 h2)). Qed.
Lemma lem1584203 (x : real) (y : real) (z : real) (h1 : term32) (h2 : term17) (h3 : term40 x y z) : (term40 x y z) = False.
Proof. exact (prop_ext (fun h4 : term40 x y z => @lem1584202 x y z h1 h2 h3) (fun h4 : False => @lem1583727 x y z h3)). Qed.
Lemma lem1584204 (x : real) (y : real) (z : real) (h1 : term32) (h2 : term17) (h3 : term40 x y z) : False.
Proof. exact (EQ_MP (@lem1584203 x y z h1 h2 h3) (@lem1583727 x y z h3)). Qed.
Lemma lem1584205 (x : real) (y : real) (z : real) (h1 : term32) (h2 : term17) (h3 : term40 x y z) : term17 = False.
Proof. exact (prop_ext (fun h4 : term17 => @lem1584204 x y z h1 h2 h3) (fun h4 : False => @lem1583691 h2)). Qed.
Lemma lem1584206 (x : real) (y : real) (z : real) (h1 : term32) (h2 : term17) (h3 : term40 x y z) : False.
Proof. exact (EQ_MP (@lem1584205 x y z h1 h2 h3) (@lem1583691 h2)). Qed.
Lemma lem1584207 (x : real) (y : real) (h1 : term32) (h2 : term17) (h3 : term51 x y) : False.
Proof. exact (ex_elim (@lem1583623 x y h3) (fun z : real => fun h0 : term50 x y z => @lem1584206 x y z h1 h2 h0)). Qed.
Lemma lem1584208 (x : real) (h1 : term32) (h2 : term17) (h3 : term58 x) : False.
Proof. exact (ex_elim (@lem1583622 x h3) (fun y : real => fun h0 : term57 x y => @lem1584207 x y h1 h2 h0)). Qed.
Lemma lem1584209 (h1 : term32) (h2 : term17) (h3 : term10) : False.
Proof. exact (ex_elim (@lem1583518 h3) (fun x : real => fun h0 : term63 x => @lem1584208 x h1 h2 h0)). Qed.
Lemma lem1584210 (h1 : term32) (h2 : term17) (h3 : term10) : term17 = False.
Proof. exact (prop_ext (fun h4 : term17 => @lem1584209 h1 h2 h3) (fun h4 : False => @lem1583621 h2)). Qed.
Lemma lem1584211 (h1 : term32) (h2 : term17) (h3 : term10) : False.
Proof. exact (EQ_MP (@lem1584210 h1 h2 h3) (@lem1583621 h2)). Qed.
Lemma lem1584212 (h1 : term32) (h2 : term10) : term15.
Proof. exact (fun h0 : term17 => @lem1584211 h1 h0 h2). Qed.
Lemma lem1584213 : term15 = term16.
Proof. exact (@lem69 term17). Qed.
Lemma lem1584214 (h1 : term32) (h2 : term10) : term16.
Proof. exact (EQ_MP (@lem1584213) (@lem1584212 h1 h2)). Qed.
Lemma lem1584215 (h1 : term10) : term20.
Proof. exact (fun h0 : term32 => @lem1584214 h0 h1). Qed.
Lemma lem1584216 : term22.
Proof. exact (fun h0 : term10 => @lem1584215 h0). Qed.
Lemma lem1584217 : term11.
Proof. exact (EQ_MP (@lem1583413) (@lem1584216)). Qed.
Lemma lem1584219 : term11.
Proof. exact (@lem1583237 (@lem1584217)). Qed.
Lemma lem1584220 (h1 : term10) : term19.
Proof. exact (@lem1584219 (@lem1583222 h1)). Qed.
Lemma lem1584221 (h1 : term10) : term15.
Proof. exact (@lem1584220 h1 (@lem1583207)). Qed.
Lemma lem1584222 (h1 : term10) : False.
Proof. exact (@lem1584221 h1 (@lem1338712)). Qed.
Lemma lem1584223 (h1 : term10) : term10 = False.
Proof. exact (prop_ext (fun h2 : term10 => @lem1584222 h1) (fun h2 : False => @lem1583222 h1)). Qed.
Lemma lem1584224 (h1 : term10) : False.
Proof. exact (EQ_MP (@lem1584223 h1) (@lem1583222 h1)). Qed.
Lemma lem1584225 : term9.
Proof. exact (fun h0 : term10 => @lem1584224 h0). Qed.
Lemma lem1584226 : term8.
Proof. exact (EQ_MP (@lem1583221) (@lem1584225)). Qed.
