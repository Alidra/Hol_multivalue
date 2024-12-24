Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_POS_EQ_0_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import SUM_POS_BOUND_spec.
Require Import SUM_POS_LE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1339379_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
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
Lemma lem7109271 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem7109272 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem7109273 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem7109272 t1) (@lem7109271 t1)). Qed.
Lemma lem7109274 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem7109273 t1 t2). Qed.
Lemma lem7109275 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem7109276 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem7109275 t1 t2) (@lem7109274 t1 t2)). Qed.
Lemma lem7109277 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem7109276 t1 t2 t3). Qed.
Lemma lem7109278 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem7109279 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem7109278 t1 t2 t3) (@lem7109277 t1 t2 t3)). Qed.
Lemma lem7109280 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem7109279 t1 t2 t3)). Qed.
Lemma lem7109281 {A : Type'} : term7 A.
Proof. exact (fun f : A -> real => @lem7085797 A f). Qed.
Lemma lem7109284 (x : real) (y : real) (h1 : (term8 y x) = (x = y)) : (term8 y x) = (x = y).
Proof. exact (h1). Qed.
Lemma lem7109285 (x : real) (y : real) (h1 : (term8 y x) = (x = y)) : (x = y) = (term8 y x).
Proof. exact (SYM (@lem7109284 x y h1)). Qed.
Lemma lem7109286 (y : real) (x : real) (h1 : (x = y) = (term8 y x)) : (x = y) = (term8 y x).
Proof. exact (h1). Qed.
Lemma lem7109287 (y : real) (x : real) (h1 : (x = y) = (term8 y x)) : (term8 y x) = (x = y).
Proof. exact (SYM (@lem7109286 y x h1)). Qed.
Lemma lem7109288 (y : real) (x : real) : ((term8 y x) = (x = y)) = ((x = y) = (term8 y x)).
Proof. exact (prop_ext (fun h1 : (term8 y x) = (x = y) => @lem7109285 x y h1) (fun h1 : (x = y) = (term8 y x) => @lem7109287 y x h1)). Qed.
Lemma lem7109289 (x : real) : (term9 x) = (term10 x).
Proof. exact (fun_ext (fun y : real => @lem7109288 y x)). Qed.
Lemma lem7109290 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7109291 (x : real) : (term11 x) = (term12 x).
Proof. exact (MK_COMB (@lem7109290) (@lem7109289 x)). Qed.
Lemma lem7109292 : term13 = term14.
Proof. exact (fun_ext (fun x : real => @lem7109291 x)). Qed.
Lemma lem7109293 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7109294 : term15 = term16.
Proof. exact (MK_COMB (@lem7109293) (@lem7109292)). Qed.
Lemma lem7109295 : term16.
Proof. exact (EQ_MP (@lem7109294) (@lem1339379)). Qed.
Lemma lem7109296 (x : real) : term17 x.
Proof. exact (@lem7109295 x). Qed.
Lemma lem7109297 (x : real) : (term17 x) = (term12 x).
Proof. exact (eq_refl (term17 x)). Qed.
Lemma lem7109298 (x : real) : term12 x.
Proof. exact (EQ_MP (@lem7109297 x) (@lem7109296 x)). Qed.
Lemma lem7109299 (x : real) (y : real) : term18 x y.
Proof. exact (@lem7109298 x y). Qed.
Lemma lem7109300 (y : real) (x : real) : (term18 x y) = ((x = y) = (term8 y x)).
Proof. exact (eq_refl (term18 x y)). Qed.
Lemma lem7109325 (y : real) (x : real) : (x = y) = (term8 y x).
Proof. exact (EQ_MP (@lem7109300 y x) (@lem7109299 x y)). Qed.
Lemma lem7109326 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : ((@sum _132718 s f) = term19) = (term20 _132718 s f).
Proof. exact (@lem7109325 term19 (@sum _132718 s f)). Qed.
Lemma lem7109329 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term21 _132718 s f) = (term21 _132718 s f).
Proof. exact (eq_refl (term21 _132718 s f)). Qed.
Lemma lem7109330 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term22 _132718 s f) = (term23 _132718 s f).
Proof. exact (MK_COMB (@lem7109329 _132718 s f) (@lem7109326 _132718 s f)). Qed.
Lemma lem7109333 {_132718 : Type'} (s : _132718 -> Prop) : (term24 _132718 s) = (term24 _132718 s).
Proof. exact (eq_refl (term24 _132718 s)). Qed.
Lemma lem7109334 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term25 _132718 s f) = (term26 _132718 s f).
Proof. exact (MK_COMB (@lem7109333 _132718 s) (@lem7109330 _132718 s f)). Qed.
Lemma lem7109337 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7109338 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term27 _132718 s f) = (term28 _132718 s f).
Proof. exact (MK_COMB (@lem7109337) (@lem7109334 _132718 s f)). Qed.
Lemma lem7109348 (y : real) (x : real) : (x = y) = (term8 y x).
Proof. exact (EQ_MP (@lem7109300 y x) (@lem7109299 x y)). Qed.
Lemma lem7109349 {_132718 : Type'} (f : _132718 -> real) (x : _132718) : ((f x) = term19) = (term29 _132718 f x).
Proof. exact (@lem7109348 term19 (f x)). Qed.
Lemma lem7109352 {_132718 : Type'} (x : _132718) (s : _132718 -> Prop) : (term30 _132718 x s) = (term30 _132718 x s).
Proof. exact (eq_refl (term30 _132718 x s)). Qed.
Lemma lem7109353 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) : (term31 _132718 s f x) = (term32 _132718 s f x).
Proof. exact (MK_COMB (@lem7109352 _132718 x s) (@lem7109349 _132718 f x)). Qed.
Lemma lem7109356 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term33 _132718 s f) = (term34 _132718 s f).
Proof. exact (fun_ext (fun x : _132718 => @lem7109353 _132718 s f x)). Qed.
Lemma lem7109357 {_132718 : Type'} : (@all _132718) = (@all _132718).
Proof. exact (eq_refl (@all _132718)). Qed.
Lemma lem7109358 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term35 _132718 s f) = (term36 _132718 s f).
Proof. exact (MK_COMB (@lem7109357 _132718) (@lem7109356 _132718 s f)). Qed.
Lemma lem7109363 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term37 _132718 s f) = (term38 _132718 s f).
Proof. exact (MK_COMB (@lem7109338 _132718 s f) (@lem7109358 _132718 s f)). Qed.
Lemma lem7109366 {_132718 : Type'} (f : _132718 -> real) : (term39 _132718 f) = (term40 _132718 f).
Proof. exact (fun_ext (fun s : _132718 -> Prop => @lem7109363 _132718 s f)). Qed.
Lemma lem7109367 {_132718 : Type'} : (@all (_132718 -> Prop)) = (@all (_132718 -> Prop)).
Proof. exact (eq_refl (@all (_132718 -> Prop))). Qed.
Lemma lem7109368 {_132718 : Type'} (f : _132718 -> real) : (term41 _132718 f) = (term42 _132718 f).
Proof. exact (MK_COMB (@lem7109367 _132718) (@lem7109366 _132718 f)). Qed.
Lemma lem7109373 {_132718 : Type'} : (term43 _132718) = (term44 _132718).
Proof. exact (fun_ext (fun f : _132718 -> real => @lem7109368 _132718 f)). Qed.
Lemma lem7109374 {_132718 : Type'} : (@all (_132718 -> real)) = (@all (_132718 -> real)).
Proof. exact (eq_refl (@all (_132718 -> real))). Qed.
Lemma lem7109375 {_132718 : Type'} : (term45 _132718) = (term46 _132718).
Proof. exact (MK_COMB (@lem7109374 _132718) (@lem7109373 _132718)). Qed.
Lemma lem7109380 {_132718 : Type'} : (term46 _132718) = (term45 _132718).
Proof. exact (SYM (@lem7109375 _132718)). Qed.
Lemma lem7109382 (p : Prop) : p = (term47 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7109383 {_132718 : Type'} : (term46 _132718) = (term48 _132718).
Proof. exact (@lem7109382 (term46 _132718)). Qed.
Lemma lem7109384 {_132718 : Type'} : (term48 _132718) = (term46 _132718).
Proof. exact (SYM (@lem7109383 _132718)). Qed.
Lemma lem7109385 {_132718 : Type'} (h1 : term49 _132718) : term49 _132718.
Proof. exact (h1). Qed.
Lemma lem7109386 {_132718 : Type'} : term50 _132718.
Proof. exact (@lem7109270 _132718). Qed.
Lemma lem7109389 {_132718 : Type'} : term7 _132718.
Proof. exact (@lem7109281 _132718). Qed.
Lemma lem7109390 {A : Type'} : term7 A.
Proof. exact (@lem7109281 A). Qed.
Lemma lem7109395 {_132718 A : Type'} (h1 : term51 _132718 A) : term51 _132718 A.
Proof. exact (h1). Qed.
Lemma lem7109396 {_132718 A : Type'} : term52 _132718 A.
Proof. exact (fun h0 : term51 _132718 A => @lem7109395 _132718 A h0). Qed.
Lemma lem7109397 {_132718 A : Type'} (h1 : term52 _132718 A) : term52 _132718 A.
Proof. exact (h1). Qed.
Lemma lem7109398 {_132718 A : Type'} (h1 : term51 _132718 A) : term51 _132718 A.
Proof. exact (h1). Qed.
Lemma lem7109399 {_132718 A : Type'} (h1 : term51 _132718 A) (h2 : term52 _132718 A) : term51 _132718 A.
Proof. exact (@lem7109397 _132718 A h2 (@lem7109398 _132718 A h1)). Qed.
Lemma lem7109400 {_132718 A : Type'} (h1 : term51 _132718 A) : term53 _132718 A.
Proof. exact (fun h0 : term52 _132718 A => @lem7109399 _132718 A h1 h0). Qed.
Lemma lem7109401 {_132718 A : Type'} (h1 : term52 _132718 A) : term52 _132718 A.
Proof. exact (h1). Qed.
Lemma lem7109402 {_132718 A : Type'} (h1 : term51 _132718 A) (h2 : term52 _132718 A) : term51 _132718 A.
Proof. exact (@lem7109400 _132718 A h1 (@lem7109401 _132718 A h2)). Qed.
Lemma lem7109403 {_132718 A : Type'} (h1 : term52 _132718 A) : term52 _132718 A.
Proof. exact (fun h0 : term51 _132718 A => @lem7109402 _132718 A h0 h1). Qed.
Lemma lem7109404 {_132718 A : Type'} : term54 _132718 A.
Proof. exact (fun h0 : term52 _132718 A => @lem7109403 _132718 A h0). Qed.
Lemma lem7109407 {_132718 A : Type'} : term52 _132718 A.
Proof. exact (@lem7109404 _132718 A (@lem7109396 _132718 A)). Qed.
Lemma lem7109408 {_132718 A : Type'} : term52 _132718 A.
Proof. exact (@lem7109407 _132718 A). Qed.
Lemma lem7109510 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7109511 {A : Type'} : (term55 A) = (term56 A).
Proof. exact (@lem7109510 (term50 A)). Qed.
Lemma lem7109542 {_132718 : Type'} : (term57 _132718) = (term57 _132718).
Proof. exact (eq_refl (term57 _132718)). Qed.
Lemma lem7109543 {_132718 A : Type'} : (term58 _132718 A) = (term59 _132718 A).
Proof. exact (MK_COMB (@lem7109542 _132718) (@lem7109511 A)). Qed.
Lemma lem7109546 {A : Type'} : (term60 A) = (term60 A).
Proof. exact (eq_refl (term60 A)). Qed.
Lemma lem7109547 {_132718 A : Type'} : (term61 _132718 A) = (term62 _132718 A).
Proof. exact (MK_COMB (@lem7109546 A) (@lem7109543 _132718 A)). Qed.
Lemma lem7109550 {_132718 : Type'} : (term60 _132718) = (term60 _132718).
Proof. exact (eq_refl (term60 _132718)). Qed.
Lemma lem7109551 {_132718 A : Type'} : (term63 _132718 A) = (term64 _132718 A).
Proof. exact (MK_COMB (@lem7109550 _132718) (@lem7109547 _132718 A)). Qed.
Lemma lem7109554 {_132718 : Type'} : (term65 _132718) = (term65 _132718).
Proof. exact (eq_refl (term65 _132718)). Qed.
Lemma lem7109561 {_132718 A : Type'} : (term51 _132718 A) = (term66 _132718 A).
Proof. exact (MK_COMB (@lem7109554 _132718) (@lem7109551 _132718 A)). Qed.
Lemma lem7109566 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term67 A s f x b) = (term67 A s f x b).
Proof. exact (eq_refl (term67 A s f x b)). Qed.
Lemma lem7109567 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term68 A s f b) = (term68 A s f b).
Proof. exact (fun_ext (fun x : A => @lem7109566 A s f x b)). Qed.
Lemma lem7109568 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7109569 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term69 A s f b) = (term69 A s f b).
Proof. exact (MK_COMB (@lem7109568 A) (@lem7109567 A s f b)). Qed.
Lemma lem7109570 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term70 A s f b) = (term70 A s f b).
Proof. exact (eq_refl (term70 A s f b)). Qed.
Lemma lem7109575 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term71 A s f x) = (term71 A s f x).
Proof. exact (eq_refl (term71 A s f x)). Qed.
Lemma lem7109576 {A : Type'} (s : A -> Prop) (f : A -> real) : (term72 A s f) = (term72 A s f).
Proof. exact (fun_ext (fun x : A => @lem7109575 A s f x)). Qed.
Lemma lem7109577 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7109578 {A : Type'} (s : A -> Prop) (f : A -> real) : (term73 A s f) = (term73 A s f).
Proof. exact (MK_COMB (@lem7109577 A) (@lem7109576 A s f)). Qed.
Lemma lem7109579 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7109580 {A : Type'} (s : A -> Prop) (f : A -> real) : (term21 A s f) = (term21 A s f).
Proof. exact (MK_COMB (@lem7109579) (@lem7109578 A s f)). Qed.
Lemma lem7109581 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term74 A s f b) = (term74 A s f b).
Proof. exact (MK_COMB (@lem7109580 A s f) (@lem7109570 A s f b)). Qed.
Lemma lem7109584 {A : Type'} (s : A -> Prop) : (term24 A s) = (term24 A s).
Proof. exact (eq_refl (term24 A s)). Qed.
Lemma lem7109585 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term75 A s f b) = (term75 A s f b).
Proof. exact (MK_COMB (@lem7109584 A s) (@lem7109581 A s f b)). Qed.
Lemma lem7109586 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7109587 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term76 A s f b) = (term76 A s f b).
Proof. exact (MK_COMB (@lem7109586) (@lem7109585 A s f b)). Qed.
Lemma lem7109588 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term77 A s f b) = (term77 A s f b).
Proof. exact (MK_COMB (@lem7109587 A s f b) (@lem7109569 A s f b)). Qed.
Lemma lem7109589 {A : Type'} (f : A -> real) (b : real) : (term78 A f b) = (term78 A f b).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7109588 A s f b)). Qed.
Lemma lem7109590 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7109591 {A : Type'} (f : A -> real) (b : real) : (term79 A f b) = (term79 A f b).
Proof. exact (MK_COMB (@lem7109590 A) (@lem7109589 A f b)). Qed.
Lemma lem7109592 {A : Type'} (f : A -> real) : (term80 A f) = (term80 A f).
Proof. exact (fun_ext (fun b : real => @lem7109591 A f b)). Qed.
Lemma lem7109593 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7109594 {A : Type'} (f : A -> real) : (term81 A f) = (term81 A f).
Proof. exact (MK_COMB (@lem7109593) (@lem7109592 A f)). Qed.
Lemma lem7109595 {A : Type'} : (term82 A) = (term82 A).
Proof. exact (fun_ext (fun f : A -> real => @lem7109594 A f)). Qed.
Lemma lem7109596 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7109597 {A : Type'} : (term50 A) = (term50 A).
Proof. exact (MK_COMB (@lem7109596 A) (@lem7109595 A)). Qed.
Lemma lem7109598 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7109599 {A : Type'} : (term56 A) = (term56 A).
Proof. exact (MK_COMB (@lem7109598) (@lem7109597 A)). Qed.
Lemma lem7109604 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) (b : real) : (term67 _132718 s f x b) = (term67 _132718 s f x b).
Proof. exact (eq_refl (term67 _132718 s f x b)). Qed.
Lemma lem7109605 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term68 _132718 s f b) = (term68 _132718 s f b).
Proof. exact (fun_ext (fun x : _132718 => @lem7109604 _132718 s f x b)). Qed.
Lemma lem7109606 {_132718 : Type'} : (@all _132718) = (@all _132718).
Proof. exact (eq_refl (@all _132718)). Qed.
Lemma lem7109607 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term69 _132718 s f b) = (term69 _132718 s f b).
Proof. exact (MK_COMB (@lem7109606 _132718) (@lem7109605 _132718 s f b)). Qed.
Lemma lem7109608 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term70 _132718 s f b) = (term70 _132718 s f b).
Proof. exact (eq_refl (term70 _132718 s f b)). Qed.
Lemma lem7109613 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) : (term71 _132718 s f x) = (term71 _132718 s f x).
Proof. exact (eq_refl (term71 _132718 s f x)). Qed.
Lemma lem7109614 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term72 _132718 s f) = (term72 _132718 s f).
Proof. exact (fun_ext (fun x : _132718 => @lem7109613 _132718 s f x)). Qed.
Lemma lem7109615 {_132718 : Type'} : (@all _132718) = (@all _132718).
Proof. exact (eq_refl (@all _132718)). Qed.
Lemma lem7109616 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term73 _132718 s f) = (term73 _132718 s f).
Proof. exact (MK_COMB (@lem7109615 _132718) (@lem7109614 _132718 s f)). Qed.
Lemma lem7109617 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7109618 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term21 _132718 s f) = (term21 _132718 s f).
Proof. exact (MK_COMB (@lem7109617) (@lem7109616 _132718 s f)). Qed.
Lemma lem7109619 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term74 _132718 s f b) = (term74 _132718 s f b).
Proof. exact (MK_COMB (@lem7109618 _132718 s f) (@lem7109608 _132718 s f b)). Qed.
Lemma lem7109622 {_132718 : Type'} (s : _132718 -> Prop) : (term24 _132718 s) = (term24 _132718 s).
Proof. exact (eq_refl (term24 _132718 s)). Qed.
Lemma lem7109623 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term75 _132718 s f b) = (term75 _132718 s f b).
Proof. exact (MK_COMB (@lem7109622 _132718 s) (@lem7109619 _132718 s f b)). Qed.
Lemma lem7109624 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7109625 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term76 _132718 s f b) = (term76 _132718 s f b).
Proof. exact (MK_COMB (@lem7109624) (@lem7109623 _132718 s f b)). Qed.
Lemma lem7109626 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term77 _132718 s f b) = (term77 _132718 s f b).
Proof. exact (MK_COMB (@lem7109625 _132718 s f b) (@lem7109607 _132718 s f b)). Qed.
Lemma lem7109627 {_132718 : Type'} (f : _132718 -> real) (b : real) : (term78 _132718 f b) = (term78 _132718 f b).
Proof. exact (fun_ext (fun s : _132718 -> Prop => @lem7109626 _132718 s f b)). Qed.
Lemma lem7109628 {_132718 : Type'} : (@all (_132718 -> Prop)) = (@all (_132718 -> Prop)).
Proof. exact (eq_refl (@all (_132718 -> Prop))). Qed.
Lemma lem7109629 {_132718 : Type'} (f : _132718 -> real) (b : real) : (term79 _132718 f b) = (term79 _132718 f b).
Proof. exact (MK_COMB (@lem7109628 _132718) (@lem7109627 _132718 f b)). Qed.
Lemma lem7109630 {_132718 : Type'} (f : _132718 -> real) : (term80 _132718 f) = (term80 _132718 f).
Proof. exact (fun_ext (fun b : real => @lem7109629 _132718 f b)). Qed.
Lemma lem7109631 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7109632 {_132718 : Type'} (f : _132718 -> real) : (term81 _132718 f) = (term81 _132718 f).
Proof. exact (MK_COMB (@lem7109631) (@lem7109630 _132718 f)). Qed.
Lemma lem7109633 {_132718 : Type'} : (term82 _132718) = (term82 _132718).
Proof. exact (fun_ext (fun f : _132718 -> real => @lem7109632 _132718 f)). Qed.
Lemma lem7109634 {_132718 : Type'} : (@all (_132718 -> real)) = (@all (_132718 -> real)).
Proof. exact (eq_refl (@all (_132718 -> real))). Qed.
Lemma lem7109635 {_132718 : Type'} : (term50 _132718) = (term50 _132718).
Proof. exact (MK_COMB (@lem7109634 _132718) (@lem7109633 _132718)). Qed.
Lemma lem7109636 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7109637 {_132718 : Type'} : (term57 _132718) = (term57 _132718).
Proof. exact (MK_COMB (@lem7109636) (@lem7109635 _132718)). Qed.
Lemma lem7109638 {_132718 A : Type'} : (term59 _132718 A) = (term59 _132718 A).
Proof. exact (MK_COMB (@lem7109637 _132718) (@lem7109599 A)). Qed.
Lemma lem7109639 {A : Type'} (s : A -> Prop) (f : A -> real) : (term83 A s f) = (term83 A s f).
Proof. exact (eq_refl (term83 A s f)). Qed.
Lemma lem7109644 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term71 A s f x) = (term71 A s f x).
Proof. exact (eq_refl (term71 A s f x)). Qed.
Lemma lem7109645 {A : Type'} (s : A -> Prop) (f : A -> real) : (term72 A s f) = (term72 A s f).
Proof. exact (fun_ext (fun x : A => @lem7109644 A s f x)). Qed.
Lemma lem7109646 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7109647 {A : Type'} (s : A -> Prop) (f : A -> real) : (term73 A s f) = (term73 A s f).
Proof. exact (MK_COMB (@lem7109646 A) (@lem7109645 A s f)). Qed.
Lemma lem7109648 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7109649 {A : Type'} (s : A -> Prop) (f : A -> real) : (term84 A s f) = (term84 A s f).
Proof. exact (MK_COMB (@lem7109648) (@lem7109647 A s f)). Qed.
Lemma lem7109650 {A : Type'} (s : A -> Prop) (f : A -> real) : (term85 A s f) = (term85 A s f).
Proof. exact (MK_COMB (@lem7109649 A s f) (@lem7109639 A s f)). Qed.
Lemma lem7109651 {A : Type'} (f : A -> real) : (term86 A f) = (term86 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7109650 A s f)). Qed.
Lemma lem7109652 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7109653 {A : Type'} (f : A -> real) : (term87 A f) = (term87 A f).
Proof. exact (MK_COMB (@lem7109652 A) (@lem7109651 A f)). Qed.
Lemma lem7109654 {A : Type'} : (term88 A) = (term88 A).
Proof. exact (fun_ext (fun f : A -> real => @lem7109653 A f)). Qed.
Lemma lem7109655 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7109656 {A : Type'} : (term7 A) = (term7 A).
Proof. exact (MK_COMB (@lem7109655 A) (@lem7109654 A)). Qed.
Lemma lem7109657 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7109658 {A : Type'} : (term60 A) = (term60 A).
Proof. exact (MK_COMB (@lem7109657) (@lem7109656 A)). Qed.
Lemma lem7109659 {_132718 A : Type'} : (term62 _132718 A) = (term62 _132718 A).
Proof. exact (MK_COMB (@lem7109658 A) (@lem7109638 _132718 A)). Qed.
Lemma lem7109660 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term83 _132718 s f) = (term83 _132718 s f).
Proof. exact (eq_refl (term83 _132718 s f)). Qed.
Lemma lem7109665 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) : (term71 _132718 s f x) = (term71 _132718 s f x).
Proof. exact (eq_refl (term71 _132718 s f x)). Qed.
Lemma lem7109666 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term72 _132718 s f) = (term72 _132718 s f).
Proof. exact (fun_ext (fun x : _132718 => @lem7109665 _132718 s f x)). Qed.
Lemma lem7109667 {_132718 : Type'} : (@all _132718) = (@all _132718).
Proof. exact (eq_refl (@all _132718)). Qed.
Lemma lem7109668 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term73 _132718 s f) = (term73 _132718 s f).
Proof. exact (MK_COMB (@lem7109667 _132718) (@lem7109666 _132718 s f)). Qed.
Lemma lem7109669 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7109670 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term84 _132718 s f) = (term84 _132718 s f).
Proof. exact (MK_COMB (@lem7109669) (@lem7109668 _132718 s f)). Qed.
Lemma lem7109671 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term85 _132718 s f) = (term85 _132718 s f).
Proof. exact (MK_COMB (@lem7109670 _132718 s f) (@lem7109660 _132718 s f)). Qed.
Lemma lem7109672 {_132718 : Type'} (f : _132718 -> real) : (term86 _132718 f) = (term86 _132718 f).
Proof. exact (fun_ext (fun s : _132718 -> Prop => @lem7109671 _132718 s f)). Qed.
Lemma lem7109673 {_132718 : Type'} : (@all (_132718 -> Prop)) = (@all (_132718 -> Prop)).
Proof. exact (eq_refl (@all (_132718 -> Prop))). Qed.
Lemma lem7109674 {_132718 : Type'} (f : _132718 -> real) : (term87 _132718 f) = (term87 _132718 f).
Proof. exact (MK_COMB (@lem7109673 _132718) (@lem7109672 _132718 f)). Qed.
Lemma lem7109675 {_132718 : Type'} : (term88 _132718) = (term88 _132718).
Proof. exact (fun_ext (fun f : _132718 -> real => @lem7109674 _132718 f)). Qed.
Lemma lem7109676 {_132718 : Type'} : (@all (_132718 -> real)) = (@all (_132718 -> real)).
Proof. exact (eq_refl (@all (_132718 -> real))). Qed.
Lemma lem7109677 {_132718 : Type'} : (term7 _132718) = (term7 _132718).
Proof. exact (MK_COMB (@lem7109676 _132718) (@lem7109675 _132718)). Qed.
Lemma lem7109678 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7109679 {_132718 : Type'} : (term60 _132718) = (term60 _132718).
Proof. exact (MK_COMB (@lem7109678) (@lem7109677 _132718)). Qed.
Lemma lem7109680 {_132718 A : Type'} : (term64 _132718 A) = (term64 _132718 A).
Proof. exact (MK_COMB (@lem7109679 _132718) (@lem7109659 _132718 A)). Qed.
Lemma lem7109689 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) : (term32 _132718 s f x) = (term32 _132718 s f x).
Proof. exact (eq_refl (term32 _132718 s f x)). Qed.
Lemma lem7109690 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term34 _132718 s f) = (term34 _132718 s f).
Proof. exact (fun_ext (fun x : _132718 => @lem7109689 _132718 s f x)). Qed.
Lemma lem7109691 {_132718 : Type'} : (@all _132718) = (@all _132718).
Proof. exact (eq_refl (@all _132718)). Qed.
Lemma lem7109692 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term36 _132718 s f) = (term36 _132718 s f).
Proof. exact (MK_COMB (@lem7109691 _132718) (@lem7109690 _132718 s f)). Qed.
Lemma lem7109697 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term20 _132718 s f) = (term20 _132718 s f).
Proof. exact (eq_refl (term20 _132718 s f)). Qed.
Lemma lem7109702 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) : (term71 _132718 s f x) = (term71 _132718 s f x).
Proof. exact (eq_refl (term71 _132718 s f x)). Qed.
Lemma lem7109703 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term72 _132718 s f) = (term72 _132718 s f).
Proof. exact (fun_ext (fun x : _132718 => @lem7109702 _132718 s f x)). Qed.
Lemma lem7109704 {_132718 : Type'} : (@all _132718) = (@all _132718).
Proof. exact (eq_refl (@all _132718)). Qed.
Lemma lem7109705 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term73 _132718 s f) = (term73 _132718 s f).
Proof. exact (MK_COMB (@lem7109704 _132718) (@lem7109703 _132718 s f)). Qed.
Lemma lem7109706 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7109707 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term21 _132718 s f) = (term21 _132718 s f).
Proof. exact (MK_COMB (@lem7109706) (@lem7109705 _132718 s f)). Qed.
Lemma lem7109708 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term23 _132718 s f) = (term23 _132718 s f).
Proof. exact (MK_COMB (@lem7109707 _132718 s f) (@lem7109697 _132718 s f)). Qed.
Lemma lem7109711 {_132718 : Type'} (s : _132718 -> Prop) : (term24 _132718 s) = (term24 _132718 s).
Proof. exact (eq_refl (term24 _132718 s)). Qed.
Lemma lem7109712 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term26 _132718 s f) = (term26 _132718 s f).
Proof. exact (MK_COMB (@lem7109711 _132718 s) (@lem7109708 _132718 s f)). Qed.
Lemma lem7109713 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7109714 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term28 _132718 s f) = (term28 _132718 s f).
Proof. exact (MK_COMB (@lem7109713) (@lem7109712 _132718 s f)). Qed.
Lemma lem7109715 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term38 _132718 s f) = (term38 _132718 s f).
Proof. exact (MK_COMB (@lem7109714 _132718 s f) (@lem7109692 _132718 s f)). Qed.
Lemma lem7109716 {_132718 : Type'} (f : _132718 -> real) : (term40 _132718 f) = (term40 _132718 f).
Proof. exact (fun_ext (fun s : _132718 -> Prop => @lem7109715 _132718 s f)). Qed.
Lemma lem7109717 {_132718 : Type'} : (@all (_132718 -> Prop)) = (@all (_132718 -> Prop)).
Proof. exact (eq_refl (@all (_132718 -> Prop))). Qed.
Lemma lem7109718 {_132718 : Type'} (f : _132718 -> real) : (term42 _132718 f) = (term42 _132718 f).
Proof. exact (MK_COMB (@lem7109717 _132718) (@lem7109716 _132718 f)). Qed.
Lemma lem7109719 {_132718 : Type'} : (term44 _132718) = (term44 _132718).
Proof. exact (fun_ext (fun f : _132718 -> real => @lem7109718 _132718 f)). Qed.
Lemma lem7109720 {_132718 : Type'} : (@all (_132718 -> real)) = (@all (_132718 -> real)).
Proof. exact (eq_refl (@all (_132718 -> real))). Qed.
Lemma lem7109721 {_132718 : Type'} : (term46 _132718) = (term46 _132718).
Proof. exact (MK_COMB (@lem7109720 _132718) (@lem7109719 _132718)). Qed.
Lemma lem7109722 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7109723 {_132718 : Type'} : (term49 _132718) = (term49 _132718).
Proof. exact (MK_COMB (@lem7109722) (@lem7109721 _132718)). Qed.
Lemma lem7109724 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7109725 {_132718 : Type'} : (term65 _132718) = (term65 _132718).
Proof. exact (MK_COMB (@lem7109724) (@lem7109723 _132718)). Qed.
Lemma lem7109726 {_132718 A : Type'} : (term66 _132718 A) = (term66 _132718 A).
Proof. exact (MK_COMB (@lem7109725 _132718) (@lem7109680 _132718 A)). Qed.
Lemma lem7109899 {_132718 A : Type'} : (term51 _132718 A) = (term66 _132718 A).
Proof. exact (TRANS (@lem7109561 _132718 A) (@lem7109726 _132718 A)). Qed.
Lemma lem7109900 {_132718 A : Type'} : (term66 _132718 A) = (term51 _132718 A).
Proof. exact (SYM (@lem7109899 _132718 A)). Qed.
Lemma lem7109901 {_132718 : Type'} (h1 : term49 _132718) : term49 _132718.
Proof. exact (h1). Qed.
Lemma lem7109902 {_132718 : Type'} (h1 : term7 _132718) : term7 _132718.
Proof. exact (h1). Qed.
Lemma lem7109903 {A : Type'} (h1 : term7 A) : term7 A.
Proof. exact (h1). Qed.
Lemma lem7109904 {_132718 : Type'} (h1 : term50 _132718) : term50 _132718.
Proof. exact (h1). Qed.
Lemma lem7109905 {A : Type'} (h1 : term50 A) : term50 A.
Proof. exact (h1). Qed.
Lemma lem7109913 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) : (term71 _132718 s f x) = (term89 _132718 s f x).
Proof. exact (@lem17265 (@IN _132718 x s) (term90 _132718 f x)). Qed.
Lemma lem7109914 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term72 _132718 s f) = (term91 _132718 s f).
Proof. exact (fun_ext (fun x : _132718 => @lem7109913 _132718 s f x)). Qed.
Lemma lem7109915 {_132718 : Type'} : (@all _132718) = (@all _132718).
Proof. exact (eq_refl (@all _132718)). Qed.
Lemma lem7109916 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term73 _132718 s f) = (term92 _132718 s f).
Proof. exact (MK_COMB (@lem7109915 _132718) (@lem7109914 _132718 s f)). Qed.
Lemma lem7109921 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term20 _132718 s f) = (term20 _132718 s f).
Proof. exact (eq_refl (term20 _132718 s f)). Qed.
Lemma lem7109922 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7109923 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term21 _132718 s f) = (term93 _132718 s f).
Proof. exact (MK_COMB (@lem7109922) (@lem7109916 _132718 s f)). Qed.
Lemma lem7109924 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term23 _132718 s f) = (term94 _132718 s f).
Proof. exact (MK_COMB (@lem7109923 _132718 s f) (@lem7109921 _132718 s f)). Qed.
Lemma lem7109926 {_132718 : Type'} (s : _132718 -> Prop) : (term24 _132718 s) = (term24 _132718 s).
Proof. exact (eq_refl (term24 _132718 s)). Qed.
Lemma lem7109927 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term26 _132718 s f) = (term95 _132718 s f).
Proof. exact (MK_COMB (@lem7109926 _132718 s) (@lem7109924 _132718 s f)). Qed.
Lemma lem7109935 {_132718 : Type'} (f : _132718 -> real) (x : _132718) : (term96 _132718 f x) = (term97 _132718 f x).
Proof. exact (@lem17045 (term98 _132718 f x) (term90 _132718 f x)). Qed.
Lemma lem7109937 {_132718 : Type'} (x : _132718) (s : _132718 -> Prop) : (term99 _132718 x s) = (term99 _132718 x s).
Proof. exact (eq_refl (term99 _132718 x s)). Qed.
Lemma lem7109938 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) : (term100 _132718 s f x) = (term101 _132718 s f x).
Proof. exact (MK_COMB (@lem7109937 _132718 x s) (@lem7109935 _132718 f x)). Qed.
Lemma lem7109939 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) : (term102 _132718 s f x) = (term100 _132718 s f x).
Proof. exact (@lem17362 (@IN _132718 x s) (term29 _132718 f x)). Qed.
Lemma lem7109940 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) : (term102 _132718 s f x) = (term101 _132718 s f x).
Proof. exact (TRANS (@lem7109939 _132718 s f x) (@lem7109938 _132718 s f x)). Qed.
Lemma lem7109941 {_132718 : Type'} (P : _132718 -> Prop) : (term103 _132718 P) = (term104 _132718 P).
Proof. exact (@lem18392 _132718 P). Qed.
Lemma lem7109942 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term105 _132718 s f) = (term106 _132718 s f).
Proof. exact (@lem7109941 _132718 (term34 _132718 s f)). Qed.
Lemma lem7109943 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) : (term107 _132718 s f x) = (term32 _132718 s f x).
Proof. exact (eq_refl (term107 _132718 s f x)). Qed.
Lemma lem7109944 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7109945 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) : (term108 _132718 s f x) = (term102 _132718 s f x).
Proof. exact (MK_COMB (@lem7109944) (@lem7109943 _132718 s f x)). Qed.
Lemma lem7109946 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) : (term108 _132718 s f x) = (term101 _132718 s f x).
Proof. exact (TRANS (@lem7109945 _132718 s f x) (@lem7109940 _132718 s f x)). Qed.
Lemma lem7109947 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term109 _132718 s f) = (term110 _132718 s f).
Proof. exact (fun_ext (fun x : _132718 => @lem7109946 _132718 s f x)). Qed.
Lemma lem7109948 {_132718 : Type'} : (@ex _132718) = (@ex _132718).
Proof. exact (eq_refl (@ex _132718)). Qed.
Lemma lem7109949 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term106 _132718 s f) = (term111 _132718 s f).
Proof. exact (MK_COMB (@lem7109948 _132718) (@lem7109947 _132718 s f)). Qed.
Lemma lem7109950 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term105 _132718 s f) = (term111 _132718 s f).
Proof. exact (TRANS (@lem7109942 _132718 s f) (@lem7109949 _132718 s f)). Qed.
Lemma lem7109951 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7109952 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term112 _132718 s f) = (term113 _132718 s f).
Proof. exact (MK_COMB (@lem7109951) (@lem7109927 _132718 s f)). Qed.
Lemma lem7109953 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term114 _132718 s f) = (term115 _132718 s f).
Proof. exact (MK_COMB (@lem7109952 _132718 s f) (@lem7109950 _132718 s f)). Qed.
Lemma lem7109954 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term116 _132718 s f) = (term114 _132718 s f).
Proof. exact (@lem17362 (term26 _132718 s f) (term36 _132718 s f)). Qed.
Lemma lem7109955 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term116 _132718 s f) = (term115 _132718 s f).
Proof. exact (TRANS (@lem7109954 _132718 s f) (@lem7109953 _132718 s f)). Qed.
Lemma lem7109956 {_132718 : Type'} (P : type686 _132718) : (term117 _132718 P) = (term118 _132718 P).
Proof. exact (@lem18392 (_132718 -> Prop) P). Qed.
Lemma lem7109957 {_132718 : Type'} (f : _132718 -> real) : (term119 _132718 f) = (term120 _132718 f).
Proof. exact (@lem7109956 _132718 (term40 _132718 f)). Qed.
Lemma lem7109958 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term121 _132718 f s) = (term38 _132718 s f).
Proof. exact (eq_refl (term121 _132718 f s)). Qed.
Lemma lem7109959 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7109960 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term122 _132718 f s) = (term116 _132718 s f).
Proof. exact (MK_COMB (@lem7109959) (@lem7109958 _132718 s f)). Qed.
Lemma lem7109961 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term122 _132718 f s) = (term115 _132718 s f).
Proof. exact (TRANS (@lem7109960 _132718 s f) (@lem7109955 _132718 s f)). Qed.
Lemma lem7109962 {_132718 : Type'} (f : _132718 -> real) : (term123 _132718 f) = (term124 _132718 f).
Proof. exact (fun_ext (fun s : _132718 -> Prop => @lem7109961 _132718 s f)). Qed.
Lemma lem7109963 {_132718 : Type'} : (@ex (_132718 -> Prop)) = (@ex (_132718 -> Prop)).
Proof. exact (eq_refl (@ex (_132718 -> Prop))). Qed.
Lemma lem7109964 {_132718 : Type'} (f : _132718 -> real) : (term120 _132718 f) = (term125 _132718 f).
Proof. exact (MK_COMB (@lem7109963 _132718) (@lem7109962 _132718 f)). Qed.
Lemma lem7109965 {_132718 : Type'} (f : _132718 -> real) : (term119 _132718 f) = (term125 _132718 f).
Proof. exact (TRANS (@lem7109957 _132718 f) (@lem7109964 _132718 f)). Qed.
Lemma lem7109966 {_132718 : Type'} (P : type716 _132718) : (term126 _132718 P) = (term127 _132718 P).
Proof. exact (@lem18392 (_132718 -> real) P). Qed.
Lemma lem7109967 {_132718 : Type'} : (term49 _132718) = (term128 _132718).
Proof. exact (@lem7109966 _132718 (term44 _132718)). Qed.
Lemma lem7109968 {_132718 : Type'} (f : _132718 -> real) : (term129 _132718 f) = (term42 _132718 f).
Proof. exact (eq_refl (term129 _132718 f)). Qed.
Lemma lem7109969 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7109970 {_132718 : Type'} (f : _132718 -> real) : (term130 _132718 f) = (term119 _132718 f).
Proof. exact (MK_COMB (@lem7109969) (@lem7109968 _132718 f)). Qed.
Lemma lem7109971 {_132718 : Type'} (f : _132718 -> real) : (term130 _132718 f) = (term125 _132718 f).
Proof. exact (TRANS (@lem7109970 _132718 f) (@lem7109965 _132718 f)). Qed.
Lemma lem7109972 {_132718 : Type'} : (term131 _132718) = (term132 _132718).
Proof. exact (fun_ext (fun f : _132718 -> real => @lem7109971 _132718 f)). Qed.
Lemma lem7109973 {_132718 : Type'} : (@ex (_132718 -> real)) = (@ex (_132718 -> real)).
Proof. exact (eq_refl (@ex (_132718 -> real))). Qed.
Lemma lem7109974 {_132718 : Type'} : (term128 _132718) = (term133 _132718).
Proof. exact (MK_COMB (@lem7109973 _132718) (@lem7109972 _132718)). Qed.
Lemma lem7109975 {_132718 : Type'} : (term49 _132718) = (term133 _132718).
Proof. exact (TRANS (@lem7109967 _132718) (@lem7109974 _132718)). Qed.
Lemma lem7110126 {A : Type'} (P : Prop) (Q : A -> Prop) : (term134 A P Q) = (term135 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem7110127 {_132718 : Type'} (P : Prop) (Q : _132718 -> Prop) : (term134 _132718 P Q) = (term135 _132718 P Q).
Proof. exact (@lem7110126 _132718 P Q). Qed.
Lemma lem7110128 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term136 _132718 s f) = (term137 _132718 s f).
Proof. exact (@lem7110127 _132718 (term95 _132718 s f) (term110 _132718 s f)). Qed.
Lemma lem7110129 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) : (term138 _132718 s f x) = (term101 _132718 s f x).
Proof. exact (eq_refl (term138 _132718 s f x)). Qed.
Lemma lem7110130 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term139 _132718 s f) = (term110 _132718 s f).
Proof. exact (fun_ext (fun x : _132718 => @lem7110129 _132718 s f x)). Qed.
Lemma lem7110131 {_132718 : Type'} : (@ex _132718) = (@ex _132718).
Proof. exact (eq_refl (@ex _132718)). Qed.
Lemma lem7110132 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term140 _132718 s f) = (term111 _132718 s f).
Proof. exact (MK_COMB (@lem7110131 _132718) (@lem7110130 _132718 s f)). Qed.
Lemma lem7110133 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term113 _132718 s f) = (term113 _132718 s f).
Proof. exact (eq_refl (term113 _132718 s f)). Qed.
Lemma lem7110134 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term136 _132718 s f) = (term115 _132718 s f).
Proof. exact (MK_COMB (@lem7110133 _132718 s f) (@lem7110132 _132718 s f)). Qed.
Lemma lem7110135 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7110136 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term141 _132718 s f) = (term142 _132718 s f).
Proof. exact (MK_COMB (@lem7110135) (@lem7110134 _132718 s f)). Qed.
Lemma lem7110137 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) : (term138 _132718 s f x) = (term101 _132718 s f x).
Proof. exact (eq_refl (term138 _132718 s f x)). Qed.
Lemma lem7110138 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term113 _132718 s f) = (term113 _132718 s f).
Proof. exact (eq_refl (term113 _132718 s f)). Qed.
Lemma lem7110139 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) : (term143 _132718 s f x) = (term144 _132718 s f x).
Proof. exact (MK_COMB (@lem7110138 _132718 s f) (@lem7110137 _132718 s f x)). Qed.
Lemma lem7110140 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term145 _132718 s f) = (term146 _132718 s f).
Proof. exact (fun_ext (fun x : _132718 => @lem7110139 _132718 s f x)). Qed.
Lemma lem7110141 {_132718 : Type'} : (@ex _132718) = (@ex _132718).
Proof. exact (eq_refl (@ex _132718)). Qed.
Lemma lem7110142 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term137 _132718 s f) = (term147 _132718 s f).
Proof. exact (MK_COMB (@lem7110141 _132718) (@lem7110140 _132718 s f)). Qed.
Lemma lem7110143 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : ((term136 _132718 s f) = (term137 _132718 s f)) = ((term115 _132718 s f) = (term147 _132718 s f)).
Proof. exact (MK_COMB (@lem7110136 _132718 s f) (@lem7110142 _132718 s f)). Qed.
Lemma lem7110144 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term115 _132718 s f) = (term147 _132718 s f).
Proof. exact (EQ_MP (@lem7110143 _132718 s f) (@lem7110128 _132718 s f)). Qed.
Lemma lem7110145 {_132718 : Type'} (f : _132718 -> real) : (term124 _132718 f) = (term148 _132718 f).
Proof. exact (fun_ext (fun s : _132718 -> Prop => @lem7110144 _132718 s f)). Qed.
Lemma lem7110146 {_132718 : Type'} : (@ex (_132718 -> Prop)) = (@ex (_132718 -> Prop)).
Proof. exact (eq_refl (@ex (_132718 -> Prop))). Qed.
Lemma lem7110147 {_132718 : Type'} (f : _132718 -> real) : (term125 _132718 f) = (term149 _132718 f).
Proof. exact (MK_COMB (@lem7110146 _132718) (@lem7110145 _132718 f)). Qed.
Lemma lem7110148 {_132718 : Type'} : (term132 _132718) = (term150 _132718).
Proof. exact (fun_ext (fun f : _132718 -> real => @lem7110147 _132718 f)). Qed.
Lemma lem7110149 {_132718 : Type'} : (@ex (_132718 -> real)) = (@ex (_132718 -> real)).
Proof. exact (eq_refl (@ex (_132718 -> real))). Qed.
Lemma lem7110151 {_132718 : Type'} : (term133 _132718) = (term151 _132718).
Proof. exact (MK_COMB (@lem7110149 _132718) (@lem7110148 _132718)). Qed.
Lemma lem7110152 {_132718 : Type'} : (term49 _132718) = (term151 _132718).
Proof. exact (TRANS (@lem7109975 _132718) (@lem7110151 _132718)). Qed.
Lemma lem7110153 {_132718 : Type'} (h1 : term49 _132718) : term151 _132718.
Proof. exact (EQ_MP (@lem7110152 _132718) (@lem7109901 _132718 h1)). Qed.
Lemma lem7110160 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) : (term152 _132718 s f x) = (term153 _132718 s f x).
Proof. exact (@lem17362 (@IN _132718 x s) (term90 _132718 f x)). Qed.
Lemma lem7110161 {_132718 : Type'} (P : _132718 -> Prop) : (term103 _132718 P) = (term104 _132718 P).
Proof. exact (@lem18392 _132718 P). Qed.
Lemma lem7110162 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term154 _132718 s f) = (term155 _132718 s f).
Proof. exact (@lem7110161 _132718 (term72 _132718 s f)). Qed.
Lemma lem7110163 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) : (term156 _132718 s f x) = (term71 _132718 s f x).
Proof. exact (eq_refl (term156 _132718 s f x)). Qed.
Lemma lem7110164 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7110165 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) : (term157 _132718 s f x) = (term152 _132718 s f x).
Proof. exact (MK_COMB (@lem7110164) (@lem7110163 _132718 s f x)). Qed.
Lemma lem7110166 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) : (term157 _132718 s f x) = (term153 _132718 s f x).
Proof. exact (TRANS (@lem7110165 _132718 s f x) (@lem7110160 _132718 s f x)). Qed.
Lemma lem7110167 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term158 _132718 s f) = (term159 _132718 s f).
Proof. exact (fun_ext (fun x : _132718 => @lem7110166 _132718 s f x)). Qed.
Lemma lem7110168 {_132718 : Type'} : (@ex _132718) = (@ex _132718).
Proof. exact (eq_refl (@ex _132718)). Qed.
Lemma lem7110169 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term155 _132718 s f) = (term160 _132718 s f).
Proof. exact (MK_COMB (@lem7110168 _132718) (@lem7110167 _132718 s f)). Qed.
Lemma lem7110170 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term154 _132718 s f) = (term160 _132718 s f).
Proof. exact (TRANS (@lem7110162 _132718 s f) (@lem7110169 _132718 s f)). Qed.
Lemma lem7110171 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term83 _132718 s f) = (term83 _132718 s f).
Proof. exact (eq_refl (term83 _132718 s f)). Qed.
Lemma lem7110172 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7110173 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term161 _132718 s f) = (term162 _132718 s f).
Proof. exact (MK_COMB (@lem7110172) (@lem7110170 _132718 s f)). Qed.
Lemma lem7110174 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term163 _132718 s f) = (term164 _132718 s f).
Proof. exact (MK_COMB (@lem7110173 _132718 s f) (@lem7110171 _132718 s f)). Qed.
Lemma lem7110175 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term85 _132718 s f) = (term163 _132718 s f).
Proof. exact (@lem17265 (term73 _132718 s f) (term83 _132718 s f)). Qed.
Lemma lem7110176 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term85 _132718 s f) = (term164 _132718 s f).
Proof. exact (TRANS (@lem7110175 _132718 s f) (@lem7110174 _132718 s f)). Qed.
Lemma lem7110177 {_132718 : Type'} (f : _132718 -> real) : (term86 _132718 f) = (term165 _132718 f).
Proof. exact (fun_ext (fun s : _132718 -> Prop => @lem7110176 _132718 s f)). Qed.
Lemma lem7110178 {_132718 : Type'} : (@all (_132718 -> Prop)) = (@all (_132718 -> Prop)).
Proof. exact (eq_refl (@all (_132718 -> Prop))). Qed.
Lemma lem7110179 {_132718 : Type'} (f : _132718 -> real) : (term87 _132718 f) = (term166 _132718 f).
Proof. exact (MK_COMB (@lem7110178 _132718) (@lem7110177 _132718 f)). Qed.
Lemma lem7110180 {_132718 : Type'} : (term88 _132718) = (term167 _132718).
Proof. exact (fun_ext (fun f : _132718 -> real => @lem7110179 _132718 f)). Qed.
Lemma lem7110181 {_132718 : Type'} : (@all (_132718 -> real)) = (@all (_132718 -> real)).
Proof. exact (eq_refl (@all (_132718 -> real))). Qed.
Lemma lem7110182 {_132718 : Type'} : (term7 _132718) = (term168 _132718).
Proof. exact (MK_COMB (@lem7110181 _132718) (@lem7110180 _132718)). Qed.
Lemma lem7110285 {A : Type'} (P : A -> Prop) (Q : Prop) : (term169 A P Q) = (term170 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7110286 {_132718 : Type'} (P : _132718 -> Prop) (Q : Prop) : (term169 _132718 P Q) = (term170 _132718 P Q).
Proof. exact (@lem7110285 _132718 P Q). Qed.
Lemma lem7110287 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term171 _132718 s f) = (term172 _132718 s f).
Proof. exact (@lem7110286 _132718 (term159 _132718 s f) (term83 _132718 s f)). Qed.
Lemma lem7110288 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) : (term173 _132718 s f x) = (term153 _132718 s f x).
Proof. exact (eq_refl (term173 _132718 s f x)). Qed.
Lemma lem7110289 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term174 _132718 s f) = (term159 _132718 s f).
Proof. exact (fun_ext (fun x : _132718 => @lem7110288 _132718 s f x)). Qed.
Lemma lem7110290 {_132718 : Type'} : (@ex _132718) = (@ex _132718).
Proof. exact (eq_refl (@ex _132718)). Qed.
Lemma lem7110291 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term175 _132718 s f) = (term160 _132718 s f).
Proof. exact (MK_COMB (@lem7110290 _132718) (@lem7110289 _132718 s f)). Qed.
Lemma lem7110292 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7110293 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term176 _132718 s f) = (term162 _132718 s f).
Proof. exact (MK_COMB (@lem7110292) (@lem7110291 _132718 s f)). Qed.
Lemma lem7110294 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term83 _132718 s f) = (term83 _132718 s f).
Proof. exact (eq_refl (term83 _132718 s f)). Qed.
Lemma lem7110295 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term171 _132718 s f) = (term164 _132718 s f).
Proof. exact (MK_COMB (@lem7110293 _132718 s f) (@lem7110294 _132718 s f)). Qed.
Lemma lem7110296 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7110297 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term177 _132718 s f) = (term178 _132718 s f).
Proof. exact (MK_COMB (@lem7110296) (@lem7110295 _132718 s f)). Qed.
Lemma lem7110298 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) : (term173 _132718 s f x) = (term153 _132718 s f x).
Proof. exact (eq_refl (term173 _132718 s f x)). Qed.
Lemma lem7110299 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7110300 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) : (term179 _132718 s f x) = (term180 _132718 s f x).
Proof. exact (MK_COMB (@lem7110299) (@lem7110298 _132718 s f x)). Qed.
Lemma lem7110301 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term83 _132718 s f) = (term83 _132718 s f).
Proof. exact (eq_refl (term83 _132718 s f)). Qed.
Lemma lem7110302 {_132718 : Type'} (x : _132718) (s : _132718 -> Prop) (f : _132718 -> real) : (term181 _132718 x s f) = (term182 _132718 x s f).
Proof. exact (MK_COMB (@lem7110300 _132718 s f x) (@lem7110301 _132718 s f)). Qed.
Lemma lem7110303 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term183 _132718 s f) = (term184 _132718 s f).
Proof. exact (fun_ext (fun x : _132718 => @lem7110302 _132718 x s f)). Qed.
Lemma lem7110304 {_132718 : Type'} : (@ex _132718) = (@ex _132718).
Proof. exact (eq_refl (@ex _132718)). Qed.
Lemma lem7110305 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term172 _132718 s f) = (term185 _132718 s f).
Proof. exact (MK_COMB (@lem7110304 _132718) (@lem7110303 _132718 s f)). Qed.
Lemma lem7110306 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : ((term171 _132718 s f) = (term172 _132718 s f)) = ((term164 _132718 s f) = (term185 _132718 s f)).
Proof. exact (MK_COMB (@lem7110297 _132718 s f) (@lem7110305 _132718 s f)). Qed.
Lemma lem7110307 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term164 _132718 s f) = (term185 _132718 s f).
Proof. exact (EQ_MP (@lem7110306 _132718 s f) (@lem7110287 _132718 s f)). Qed.
Lemma lem7110308 {_132718 : Type'} (f : _132718 -> real) : (term165 _132718 f) = (term186 _132718 f).
Proof. exact (fun_ext (fun s : _132718 -> Prop => @lem7110307 _132718 s f)). Qed.
Lemma lem7110309 {_132718 : Type'} : (@all (_132718 -> Prop)) = (@all (_132718 -> Prop)).
Proof. exact (eq_refl (@all (_132718 -> Prop))). Qed.
Lemma lem7110310 {_132718 : Type'} (f : _132718 -> real) : (term166 _132718 f) = (term187 _132718 f).
Proof. exact (MK_COMB (@lem7110309 _132718) (@lem7110308 _132718 f)). Qed.
Lemma lem7110312 {A B : Type'} (P : type1413 A B) : (term188 A B P) = (term189 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7110313 {_132718 : Type'} (P : type672 _132718) : (term190 _132718 P) = (term191 _132718 P).
Proof. exact (@lem7110312 (_132718 -> Prop) _132718 P). Qed.
Lemma lem7110314 {_132718 : Type'} (f : _132718 -> real) : (term192 _132718 f) = (term193 _132718 f).
Proof. exact (@lem7110313 _132718 (term194 _132718 f)). Qed.
Lemma lem7110315 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term195 _132718 f s) = (term184 _132718 s f).
Proof. exact (eq_refl (term195 _132718 f s)). Qed.
Lemma lem7110316 {_132718 : Type'} (x : _132718) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7110317 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) : (term196 _132718 f s x) = (term197 _132718 s f x).
Proof. exact (MK_COMB (@lem7110315 _132718 s f) (@lem7110316 _132718 x)). Qed.
Lemma lem7110318 {_132718 : Type'} (x : _132718) (s : _132718 -> Prop) (f : _132718 -> real) : (term197 _132718 s f x) = (term182 _132718 x s f).
Proof. exact (eq_refl (term197 _132718 s f x)). Qed.
Lemma lem7110319 {_132718 : Type'} (x : _132718) (s : _132718 -> Prop) (f : _132718 -> real) : (term196 _132718 f s x) = (term182 _132718 x s f).
Proof. exact (TRANS (@lem7110317 _132718 s f x) (@lem7110318 _132718 x s f)). Qed.
Lemma lem7110320 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term198 _132718 f s) = (term184 _132718 s f).
Proof. exact (fun_ext (fun x : _132718 => @lem7110319 _132718 x s f)). Qed.
Lemma lem7110321 {_132718 : Type'} : (@ex _132718) = (@ex _132718).
Proof. exact (eq_refl (@ex _132718)). Qed.
Lemma lem7110322 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term199 _132718 f s) = (term185 _132718 s f).
Proof. exact (MK_COMB (@lem7110321 _132718) (@lem7110320 _132718 s f)). Qed.
Lemma lem7110323 {_132718 : Type'} (f : _132718 -> real) : (term200 _132718 f) = (term186 _132718 f).
Proof. exact (fun_ext (fun s : _132718 -> Prop => @lem7110322 _132718 s f)). Qed.
Lemma lem7110324 {_132718 : Type'} : (@all (_132718 -> Prop)) = (@all (_132718 -> Prop)).
Proof. exact (eq_refl (@all (_132718 -> Prop))). Qed.
Lemma lem7110325 {_132718 : Type'} (f : _132718 -> real) : (term192 _132718 f) = (term187 _132718 f).
Proof. exact (MK_COMB (@lem7110324 _132718) (@lem7110323 _132718 f)). Qed.
Lemma lem7110326 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7110327 {_132718 : Type'} (f : _132718 -> real) : (term201 _132718 f) = (term202 _132718 f).
Proof. exact (MK_COMB (@lem7110326) (@lem7110325 _132718 f)). Qed.
Lemma lem7110328 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term195 _132718 f s) = (term184 _132718 s f).
Proof. exact (eq_refl (term195 _132718 f s)). Qed.
Lemma lem7110329 {_132718 : Type'} (x : type684 _132718) (s : _132718 -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem7110330 {_132718 : Type'} (f : _132718 -> real) (x : type684 _132718) (s : _132718 -> Prop) : (term203 _132718 f x s) = (term204 _132718 f x s).
Proof. exact (MK_COMB (@lem7110328 _132718 s f) (@lem7110329 _132718 x s)). Qed.
Lemma lem7110331 {_132718 : Type'} (x : type684 _132718) (s : _132718 -> Prop) (f : _132718 -> real) : (term204 _132718 f x s) = (term205 _132718 x s f).
Proof. exact (eq_refl (term204 _132718 f x s)). Qed.
Lemma lem7110332 {_132718 : Type'} (x : type684 _132718) (s : _132718 -> Prop) (f : _132718 -> real) : (term203 _132718 f x s) = (term205 _132718 x s f).
Proof. exact (TRANS (@lem7110330 _132718 f x s) (@lem7110331 _132718 x s f)). Qed.
Lemma lem7110333 {_132718 : Type'} (x : type684 _132718) (f : _132718 -> real) : (term206 _132718 f x) = (term207 _132718 x f).
Proof. exact (fun_ext (fun s : _132718 -> Prop => @lem7110332 _132718 x s f)). Qed.
Lemma lem7110334 {_132718 : Type'} : (@all (_132718 -> Prop)) = (@all (_132718 -> Prop)).
Proof. exact (eq_refl (@all (_132718 -> Prop))). Qed.
Lemma lem7110335 {_132718 : Type'} (x : type684 _132718) (f : _132718 -> real) : (term208 _132718 f x) = (term209 _132718 x f).
Proof. exact (MK_COMB (@lem7110334 _132718) (@lem7110333 _132718 x f)). Qed.
Lemma lem7110336 {_132718 : Type'} (f : _132718 -> real) : (term210 _132718 f) = (term211 _132718 f).
Proof. exact (fun_ext (fun x : type684 _132718 => @lem7110335 _132718 x f)). Qed.
Lemma lem7110337 {_132718 : Type'} : (@ex ((_132718 -> Prop) -> _132718)) = (@ex ((_132718 -> Prop) -> _132718)).
Proof. exact (eq_refl (@ex ((_132718 -> Prop) -> _132718))). Qed.
Lemma lem7110338 {_132718 : Type'} (f : _132718 -> real) : (term193 _132718 f) = (term212 _132718 f).
Proof. exact (MK_COMB (@lem7110337 _132718) (@lem7110336 _132718 f)). Qed.
Lemma lem7110339 {_132718 : Type'} (f : _132718 -> real) : ((term192 _132718 f) = (term193 _132718 f)) = ((term187 _132718 f) = (term212 _132718 f)).
Proof. exact (MK_COMB (@lem7110327 _132718 f) (@lem7110338 _132718 f)). Qed.
Lemma lem7110340 {_132718 : Type'} (f : _132718 -> real) : (term187 _132718 f) = (term212 _132718 f).
Proof. exact (EQ_MP (@lem7110339 _132718 f) (@lem7110314 _132718 f)). Qed.
Lemma lem7110341 {_132718 : Type'} (f : _132718 -> real) : (term166 _132718 f) = (term212 _132718 f).
Proof. exact (TRANS (@lem7110310 _132718 f) (@lem7110340 _132718 f)). Qed.
Lemma lem7110342 {_132718 : Type'} : (term167 _132718) = (term213 _132718).
Proof. exact (fun_ext (fun f : _132718 -> real => @lem7110341 _132718 f)). Qed.
Lemma lem7110343 {_132718 : Type'} : (@all (_132718 -> real)) = (@all (_132718 -> real)).
Proof. exact (eq_refl (@all (_132718 -> real))). Qed.
Lemma lem7110344 {_132718 : Type'} : (term168 _132718) = (term214 _132718).
Proof. exact (MK_COMB (@lem7110343 _132718) (@lem7110342 _132718)). Qed.
Lemma lem7110346 {A B : Type'} (P : type1413 A B) : (term188 A B P) = (term189 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7110347 {_132718 : Type'} (P : type707 _132718) : (term215 _132718 P) = (term216 _132718 P).
Proof. exact (@lem7110346 (_132718 -> real) (type684 _132718) P). Qed.
Lemma lem7110348 {_132718 : Type'} : (term217 _132718) = (term218 _132718).
Proof. exact (@lem7110347 _132718 (term219 _132718)). Qed.
Lemma lem7110349 {_132718 : Type'} (f : _132718 -> real) : (term220 _132718 f) = (term211 _132718 f).
Proof. exact (eq_refl (term220 _132718 f)). Qed.
Lemma lem7110350 {_132718 : Type'} (x : type684 _132718) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7110351 {_132718 : Type'} (f : _132718 -> real) (x : type684 _132718) : (term221 _132718 f x) = (term222 _132718 f x).
Proof. exact (MK_COMB (@lem7110349 _132718 f) (@lem7110350 _132718 x)). Qed.
Lemma lem7110352 {_132718 : Type'} (x : type684 _132718) (f : _132718 -> real) : (term222 _132718 f x) = (term209 _132718 x f).
Proof. exact (eq_refl (term222 _132718 f x)). Qed.
Lemma lem7110353 {_132718 : Type'} (x : type684 _132718) (f : _132718 -> real) : (term221 _132718 f x) = (term209 _132718 x f).
Proof. exact (TRANS (@lem7110351 _132718 f x) (@lem7110352 _132718 x f)). Qed.
Lemma lem7110354 {_132718 : Type'} (f : _132718 -> real) : (term223 _132718 f) = (term211 _132718 f).
Proof. exact (fun_ext (fun x : type684 _132718 => @lem7110353 _132718 x f)). Qed.
Lemma lem7110355 {_132718 : Type'} : (@ex ((_132718 -> Prop) -> _132718)) = (@ex ((_132718 -> Prop) -> _132718)).
Proof. exact (eq_refl (@ex ((_132718 -> Prop) -> _132718))). Qed.
Lemma lem7110356 {_132718 : Type'} (f : _132718 -> real) : (term224 _132718 f) = (term212 _132718 f).
Proof. exact (MK_COMB (@lem7110355 _132718) (@lem7110354 _132718 f)). Qed.
Lemma lem7110357 {_132718 : Type'} : (term225 _132718) = (term213 _132718).
Proof. exact (fun_ext (fun f : _132718 -> real => @lem7110356 _132718 f)). Qed.
Lemma lem7110358 {_132718 : Type'} : (@all (_132718 -> real)) = (@all (_132718 -> real)).
Proof. exact (eq_refl (@all (_132718 -> real))). Qed.
Lemma lem7110359 {_132718 : Type'} : (term217 _132718) = (term214 _132718).
Proof. exact (MK_COMB (@lem7110358 _132718) (@lem7110357 _132718)). Qed.
Lemma lem7110360 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7110361 {_132718 : Type'} : (term226 _132718) = (term227 _132718).
Proof. exact (MK_COMB (@lem7110360) (@lem7110359 _132718)). Qed.
Lemma lem7110362 {_132718 : Type'} (f : _132718 -> real) : (term220 _132718 f) = (term211 _132718 f).
Proof. exact (eq_refl (term220 _132718 f)). Qed.
Lemma lem7110363 {_132718 : Type'} (x : type710 _132718) (f : _132718 -> real) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem7110364 {_132718 : Type'} (x : type710 _132718) (f : _132718 -> real) : (term228 _132718 x f) = (term229 _132718 x f).
Proof. exact (MK_COMB (@lem7110362 _132718 f) (@lem7110363 _132718 x f)). Qed.
Lemma lem7110365 {_132718 : Type'} (x : type710 _132718) (f : _132718 -> real) : (term229 _132718 x f) = (term230 _132718 x f).
Proof. exact (eq_refl (term229 _132718 x f)). Qed.
Lemma lem7110366 {_132718 : Type'} (x : type710 _132718) (f : _132718 -> real) : (term228 _132718 x f) = (term230 _132718 x f).
Proof. exact (TRANS (@lem7110364 _132718 x f) (@lem7110365 _132718 x f)). Qed.
Lemma lem7110367 {_132718 : Type'} (x : type710 _132718) : (term231 _132718 x) = (term232 _132718 x).
Proof. exact (fun_ext (fun f : _132718 -> real => @lem7110366 _132718 x f)). Qed.
Lemma lem7110368 {_132718 : Type'} : (@all (_132718 -> real)) = (@all (_132718 -> real)).
Proof. exact (eq_refl (@all (_132718 -> real))). Qed.
Lemma lem7110369 {_132718 : Type'} (x : type710 _132718) : (term233 _132718 x) = (term234 _132718 x).
Proof. exact (MK_COMB (@lem7110368 _132718) (@lem7110367 _132718 x)). Qed.
Lemma lem7110370 {_132718 : Type'} : (term235 _132718) = (term236 _132718).
Proof. exact (fun_ext (fun x : type710 _132718 => @lem7110369 _132718 x)). Qed.
Lemma lem7110371 {_132718 : Type'} : (@ex ((_132718 -> real) -> (_132718 -> Prop) -> _132718)) = (@ex ((_132718 -> real) -> (_132718 -> Prop) -> _132718)).
Proof. exact (eq_refl (@ex ((_132718 -> real) -> (_132718 -> Prop) -> _132718))). Qed.
Lemma lem7110372 {_132718 : Type'} : (term218 _132718) = (term237 _132718).
Proof. exact (MK_COMB (@lem7110371 _132718) (@lem7110370 _132718)). Qed.
Lemma lem7110373 {_132718 : Type'} : ((term217 _132718) = (term218 _132718)) = ((term214 _132718) = (term237 _132718)).
Proof. exact (MK_COMB (@lem7110361 _132718) (@lem7110372 _132718)). Qed.
Lemma lem7110374 {_132718 : Type'} : (term214 _132718) = (term237 _132718).
Proof. exact (EQ_MP (@lem7110373 _132718) (@lem7110348 _132718)). Qed.
Lemma lem7110376 {_132718 : Type'} : (term168 _132718) = (term237 _132718).
Proof. exact (TRANS (@lem7110344 _132718) (@lem7110374 _132718)). Qed.
Lemma lem7110377 {_132718 : Type'} : (term7 _132718) = (term237 _132718).
Proof. exact (TRANS (@lem7110182 _132718) (@lem7110376 _132718)). Qed.
Lemma lem7110378 {_132718 : Type'} (h1 : term7 _132718) : term237 _132718.
Proof. exact (EQ_MP (@lem7110377 _132718) (@lem7109902 _132718 h1)). Qed.
Lemma lem7110385 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term152 A s f x) = (term153 A s f x).
Proof. exact (@lem17362 (@IN A x s) (term90 A f x)). Qed.
Lemma lem7110386 {A : Type'} (P : A -> Prop) : (term103 A P) = (term104 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem7110387 {A : Type'} (s : A -> Prop) (f : A -> real) : (term154 A s f) = (term155 A s f).
Proof. exact (@lem7110386 A (term72 A s f)). Qed.
Lemma lem7110388 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term156 A s f x) = (term71 A s f x).
Proof. exact (eq_refl (term156 A s f x)). Qed.
Lemma lem7110389 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7110390 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term157 A s f x) = (term152 A s f x).
Proof. exact (MK_COMB (@lem7110389) (@lem7110388 A s f x)). Qed.
Lemma lem7110391 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term157 A s f x) = (term153 A s f x).
Proof. exact (TRANS (@lem7110390 A s f x) (@lem7110385 A s f x)). Qed.
Lemma lem7110392 {A : Type'} (s : A -> Prop) (f : A -> real) : (term158 A s f) = (term159 A s f).
Proof. exact (fun_ext (fun x : A => @lem7110391 A s f x)). Qed.
Lemma lem7110393 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7110394 {A : Type'} (s : A -> Prop) (f : A -> real) : (term155 A s f) = (term160 A s f).
Proof. exact (MK_COMB (@lem7110393 A) (@lem7110392 A s f)). Qed.
Lemma lem7110395 {A : Type'} (s : A -> Prop) (f : A -> real) : (term154 A s f) = (term160 A s f).
Proof. exact (TRANS (@lem7110387 A s f) (@lem7110394 A s f)). Qed.
Lemma lem7110396 {A : Type'} (s : A -> Prop) (f : A -> real) : (term83 A s f) = (term83 A s f).
Proof. exact (eq_refl (term83 A s f)). Qed.
Lemma lem7110397 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7110398 {A : Type'} (s : A -> Prop) (f : A -> real) : (term161 A s f) = (term162 A s f).
Proof. exact (MK_COMB (@lem7110397) (@lem7110395 A s f)). Qed.
Lemma lem7110399 {A : Type'} (s : A -> Prop) (f : A -> real) : (term163 A s f) = (term164 A s f).
Proof. exact (MK_COMB (@lem7110398 A s f) (@lem7110396 A s f)). Qed.
Lemma lem7110400 {A : Type'} (s : A -> Prop) (f : A -> real) : (term85 A s f) = (term163 A s f).
Proof. exact (@lem17265 (term73 A s f) (term83 A s f)). Qed.
Lemma lem7110401 {A : Type'} (s : A -> Prop) (f : A -> real) : (term85 A s f) = (term164 A s f).
Proof. exact (TRANS (@lem7110400 A s f) (@lem7110399 A s f)). Qed.
Lemma lem7110402 {A : Type'} (f : A -> real) : (term86 A f) = (term165 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7110401 A s f)). Qed.
Lemma lem7110403 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7110404 {A : Type'} (f : A -> real) : (term87 A f) = (term166 A f).
Proof. exact (MK_COMB (@lem7110403 A) (@lem7110402 A f)). Qed.
Lemma lem7110405 {A : Type'} : (term88 A) = (term167 A).
Proof. exact (fun_ext (fun f : A -> real => @lem7110404 A f)). Qed.
Lemma lem7110406 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7110407 {A : Type'} : (term7 A) = (term168 A).
Proof. exact (MK_COMB (@lem7110406 A) (@lem7110405 A)). Qed.
Lemma lem7110510 {A : Type'} (P : A -> Prop) (Q : Prop) : (term169 A P Q) = (term170 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7110511 {A : Type'} (P : A -> Prop) (Q : Prop) : (term169 A P Q) = (term170 A P Q).
Proof. exact (@lem7110510 A P Q). Qed.
Lemma lem7110512 {A : Type'} (s : A -> Prop) (f : A -> real) : (term171 A s f) = (term172 A s f).
Proof. exact (@lem7110511 A (term159 A s f) (term83 A s f)). Qed.
Lemma lem7110513 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term173 A s f x) = (term153 A s f x).
Proof. exact (eq_refl (term173 A s f x)). Qed.
Lemma lem7110514 {A : Type'} (s : A -> Prop) (f : A -> real) : (term174 A s f) = (term159 A s f).
Proof. exact (fun_ext (fun x : A => @lem7110513 A s f x)). Qed.
Lemma lem7110515 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7110516 {A : Type'} (s : A -> Prop) (f : A -> real) : (term175 A s f) = (term160 A s f).
Proof. exact (MK_COMB (@lem7110515 A) (@lem7110514 A s f)). Qed.
Lemma lem7110517 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7110518 {A : Type'} (s : A -> Prop) (f : A -> real) : (term176 A s f) = (term162 A s f).
Proof. exact (MK_COMB (@lem7110517) (@lem7110516 A s f)). Qed.
Lemma lem7110519 {A : Type'} (s : A -> Prop) (f : A -> real) : (term83 A s f) = (term83 A s f).
Proof. exact (eq_refl (term83 A s f)). Qed.
Lemma lem7110520 {A : Type'} (s : A -> Prop) (f : A -> real) : (term171 A s f) = (term164 A s f).
Proof. exact (MK_COMB (@lem7110518 A s f) (@lem7110519 A s f)). Qed.
Lemma lem7110521 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7110522 {A : Type'} (s : A -> Prop) (f : A -> real) : (term177 A s f) = (term178 A s f).
Proof. exact (MK_COMB (@lem7110521) (@lem7110520 A s f)). Qed.
Lemma lem7110523 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term173 A s f x) = (term153 A s f x).
Proof. exact (eq_refl (term173 A s f x)). Qed.
Lemma lem7110524 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7110525 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term179 A s f x) = (term180 A s f x).
Proof. exact (MK_COMB (@lem7110524) (@lem7110523 A s f x)). Qed.
Lemma lem7110526 {A : Type'} (s : A -> Prop) (f : A -> real) : (term83 A s f) = (term83 A s f).
Proof. exact (eq_refl (term83 A s f)). Qed.
Lemma lem7110527 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : (term181 A x s f) = (term182 A x s f).
Proof. exact (MK_COMB (@lem7110525 A s f x) (@lem7110526 A s f)). Qed.
Lemma lem7110528 {A : Type'} (s : A -> Prop) (f : A -> real) : (term183 A s f) = (term184 A s f).
Proof. exact (fun_ext (fun x : A => @lem7110527 A x s f)). Qed.
Lemma lem7110529 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7110530 {A : Type'} (s : A -> Prop) (f : A -> real) : (term172 A s f) = (term185 A s f).
Proof. exact (MK_COMB (@lem7110529 A) (@lem7110528 A s f)). Qed.
Lemma lem7110531 {A : Type'} (s : A -> Prop) (f : A -> real) : ((term171 A s f) = (term172 A s f)) = ((term164 A s f) = (term185 A s f)).
Proof. exact (MK_COMB (@lem7110522 A s f) (@lem7110530 A s f)). Qed.
Lemma lem7110532 {A : Type'} (s : A -> Prop) (f : A -> real) : (term164 A s f) = (term185 A s f).
Proof. exact (EQ_MP (@lem7110531 A s f) (@lem7110512 A s f)). Qed.
Lemma lem7110533 {A : Type'} (f : A -> real) : (term165 A f) = (term186 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7110532 A s f)). Qed.
Lemma lem7110534 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7110535 {A : Type'} (f : A -> real) : (term166 A f) = (term187 A f).
Proof. exact (MK_COMB (@lem7110534 A) (@lem7110533 A f)). Qed.
Lemma lem7110537 {A B : Type'} (P : type1413 A B) : (term188 A B P) = (term189 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7110538 {A : Type'} (P : type672 A) : (term190 A P) = (term191 A P).
Proof. exact (@lem7110537 (A -> Prop) A P). Qed.
Lemma lem7110539 {A : Type'} (f : A -> real) : (term192 A f) = (term193 A f).
Proof. exact (@lem7110538 A (term194 A f)). Qed.
Lemma lem7110540 {A : Type'} (s : A -> Prop) (f : A -> real) : (term195 A f s) = (term184 A s f).
Proof. exact (eq_refl (term195 A f s)). Qed.
Lemma lem7110541 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7110542 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term196 A f s x) = (term197 A s f x).
Proof. exact (MK_COMB (@lem7110540 A s f) (@lem7110541 A x)). Qed.
Lemma lem7110543 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : (term197 A s f x) = (term182 A x s f).
Proof. exact (eq_refl (term197 A s f x)). Qed.
Lemma lem7110544 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : (term196 A f s x) = (term182 A x s f).
Proof. exact (TRANS (@lem7110542 A s f x) (@lem7110543 A x s f)). Qed.
Lemma lem7110545 {A : Type'} (s : A -> Prop) (f : A -> real) : (term198 A f s) = (term184 A s f).
Proof. exact (fun_ext (fun x : A => @lem7110544 A x s f)). Qed.
Lemma lem7110546 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7110547 {A : Type'} (s : A -> Prop) (f : A -> real) : (term199 A f s) = (term185 A s f).
Proof. exact (MK_COMB (@lem7110546 A) (@lem7110545 A s f)). Qed.
Lemma lem7110548 {A : Type'} (f : A -> real) : (term200 A f) = (term186 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7110547 A s f)). Qed.
Lemma lem7110549 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7110550 {A : Type'} (f : A -> real) : (term192 A f) = (term187 A f).
Proof. exact (MK_COMB (@lem7110549 A) (@lem7110548 A f)). Qed.
Lemma lem7110551 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7110552 {A : Type'} (f : A -> real) : (term201 A f) = (term202 A f).
Proof. exact (MK_COMB (@lem7110551) (@lem7110550 A f)). Qed.
Lemma lem7110553 {A : Type'} (s : A -> Prop) (f : A -> real) : (term195 A f s) = (term184 A s f).
Proof. exact (eq_refl (term195 A f s)). Qed.
Lemma lem7110554 {A : Type'} (x : type684 A) (s : A -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem7110555 {A : Type'} (f : A -> real) (x : type684 A) (s : A -> Prop) : (term203 A f x s) = (term204 A f x s).
Proof. exact (MK_COMB (@lem7110553 A s f) (@lem7110554 A x s)). Qed.
Lemma lem7110556 {A : Type'} (x : type684 A) (s : A -> Prop) (f : A -> real) : (term204 A f x s) = (term205 A x s f).
Proof. exact (eq_refl (term204 A f x s)). Qed.
Lemma lem7110557 {A : Type'} (x : type684 A) (s : A -> Prop) (f : A -> real) : (term203 A f x s) = (term205 A x s f).
Proof. exact (TRANS (@lem7110555 A f x s) (@lem7110556 A x s f)). Qed.
Lemma lem7110558 {A : Type'} (x : type684 A) (f : A -> real) : (term206 A f x) = (term207 A x f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7110557 A x s f)). Qed.
Lemma lem7110559 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7110560 {A : Type'} (x : type684 A) (f : A -> real) : (term208 A f x) = (term209 A x f).
Proof. exact (MK_COMB (@lem7110559 A) (@lem7110558 A x f)). Qed.
Lemma lem7110561 {A : Type'} (f : A -> real) : (term210 A f) = (term211 A f).
Proof. exact (fun_ext (fun x : type684 A => @lem7110560 A x f)). Qed.
Lemma lem7110562 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem7110563 {A : Type'} (f : A -> real) : (term193 A f) = (term212 A f).
Proof. exact (MK_COMB (@lem7110562 A) (@lem7110561 A f)). Qed.
Lemma lem7110564 {A : Type'} (f : A -> real) : ((term192 A f) = (term193 A f)) = ((term187 A f) = (term212 A f)).
Proof. exact (MK_COMB (@lem7110552 A f) (@lem7110563 A f)). Qed.
Lemma lem7110565 {A : Type'} (f : A -> real) : (term187 A f) = (term212 A f).
Proof. exact (EQ_MP (@lem7110564 A f) (@lem7110539 A f)). Qed.
Lemma lem7110566 {A : Type'} (f : A -> real) : (term166 A f) = (term212 A f).
Proof. exact (TRANS (@lem7110535 A f) (@lem7110565 A f)). Qed.
Lemma lem7110567 {A : Type'} : (term167 A) = (term213 A).
Proof. exact (fun_ext (fun f : A -> real => @lem7110566 A f)). Qed.
Lemma lem7110568 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7110569 {A : Type'} : (term168 A) = (term214 A).
Proof. exact (MK_COMB (@lem7110568 A) (@lem7110567 A)). Qed.
Lemma lem7110571 {A B : Type'} (P : type1413 A B) : (term188 A B P) = (term189 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7110572 {A : Type'} (P : type707 A) : (term215 A P) = (term216 A P).
Proof. exact (@lem7110571 (A -> real) (type684 A) P). Qed.
Lemma lem7110573 {A : Type'} : (term217 A) = (term218 A).
Proof. exact (@lem7110572 A (term219 A)). Qed.
Lemma lem7110574 {A : Type'} (f : A -> real) : (term220 A f) = (term211 A f).
Proof. exact (eq_refl (term220 A f)). Qed.
Lemma lem7110575 {A : Type'} (x : type684 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7110576 {A : Type'} (f : A -> real) (x : type684 A) : (term221 A f x) = (term222 A f x).
Proof. exact (MK_COMB (@lem7110574 A f) (@lem7110575 A x)). Qed.
Lemma lem7110577 {A : Type'} (x : type684 A) (f : A -> real) : (term222 A f x) = (term209 A x f).
Proof. exact (eq_refl (term222 A f x)). Qed.
Lemma lem7110578 {A : Type'} (x : type684 A) (f : A -> real) : (term221 A f x) = (term209 A x f).
Proof. exact (TRANS (@lem7110576 A f x) (@lem7110577 A x f)). Qed.
Lemma lem7110579 {A : Type'} (f : A -> real) : (term223 A f) = (term211 A f).
Proof. exact (fun_ext (fun x : type684 A => @lem7110578 A x f)). Qed.
Lemma lem7110580 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem7110581 {A : Type'} (f : A -> real) : (term224 A f) = (term212 A f).
Proof. exact (MK_COMB (@lem7110580 A) (@lem7110579 A f)). Qed.
Lemma lem7110582 {A : Type'} : (term225 A) = (term213 A).
Proof. exact (fun_ext (fun f : A -> real => @lem7110581 A f)). Qed.
Lemma lem7110583 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7110584 {A : Type'} : (term217 A) = (term214 A).
Proof. exact (MK_COMB (@lem7110583 A) (@lem7110582 A)). Qed.
Lemma lem7110585 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7110586 {A : Type'} : (term226 A) = (term227 A).
Proof. exact (MK_COMB (@lem7110585) (@lem7110584 A)). Qed.
Lemma lem7110587 {A : Type'} (f : A -> real) : (term220 A f) = (term211 A f).
Proof. exact (eq_refl (term220 A f)). Qed.
Lemma lem7110588 {A : Type'} (x : type710 A) (f : A -> real) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem7110589 {A : Type'} (x : type710 A) (f : A -> real) : (term228 A x f) = (term229 A x f).
Proof. exact (MK_COMB (@lem7110587 A f) (@lem7110588 A x f)). Qed.
Lemma lem7110590 {A : Type'} (x : type710 A) (f : A -> real) : (term229 A x f) = (term230 A x f).
Proof. exact (eq_refl (term229 A x f)). Qed.
Lemma lem7110591 {A : Type'} (x : type710 A) (f : A -> real) : (term228 A x f) = (term230 A x f).
Proof. exact (TRANS (@lem7110589 A x f) (@lem7110590 A x f)). Qed.
Lemma lem7110592 {A : Type'} (x : type710 A) : (term231 A x) = (term232 A x).
Proof. exact (fun_ext (fun f : A -> real => @lem7110591 A x f)). Qed.
Lemma lem7110593 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7110594 {A : Type'} (x : type710 A) : (term233 A x) = (term234 A x).
Proof. exact (MK_COMB (@lem7110593 A) (@lem7110592 A x)). Qed.
Lemma lem7110595 {A : Type'} : (term235 A) = (term236 A).
Proof. exact (fun_ext (fun x : type710 A => @lem7110594 A x)). Qed.
Lemma lem7110596 {A : Type'} : (@ex ((A -> real) -> (A -> Prop) -> A)) = (@ex ((A -> real) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> real) -> (A -> Prop) -> A))). Qed.
Lemma lem7110597 {A : Type'} : (term218 A) = (term237 A).
Proof. exact (MK_COMB (@lem7110596 A) (@lem7110595 A)). Qed.
Lemma lem7110598 {A : Type'} : ((term217 A) = (term218 A)) = ((term214 A) = (term237 A)).
Proof. exact (MK_COMB (@lem7110586 A) (@lem7110597 A)). Qed.
Lemma lem7110599 {A : Type'} : (term214 A) = (term237 A).
Proof. exact (EQ_MP (@lem7110598 A) (@lem7110573 A)). Qed.
Lemma lem7110601 {A : Type'} : (term168 A) = (term237 A).
Proof. exact (TRANS (@lem7110569 A) (@lem7110599 A)). Qed.
Lemma lem7110602 {A : Type'} : (term7 A) = (term237 A).
Proof. exact (TRANS (@lem7110407 A) (@lem7110601 A)). Qed.
Lemma lem7110603 {A : Type'} (h1 : term7 A) : term237 A.
Proof. exact (EQ_MP (@lem7110602 A) (@lem7109903 A h1)). Qed.
Lemma lem7110611 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) : (term152 _132718 s f x) = (term153 _132718 s f x).
Proof. exact (@lem17362 (@IN _132718 x s) (term90 _132718 f x)). Qed.
Lemma lem7110612 {_132718 : Type'} (P : _132718 -> Prop) : (term103 _132718 P) = (term104 _132718 P).
Proof. exact (@lem18392 _132718 P). Qed.
Lemma lem7110613 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term154 _132718 s f) = (term155 _132718 s f).
Proof. exact (@lem7110612 _132718 (term72 _132718 s f)). Qed.
Lemma lem7110614 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) : (term156 _132718 s f x) = (term71 _132718 s f x).
Proof. exact (eq_refl (term156 _132718 s f x)). Qed.
Lemma lem7110615 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7110616 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) : (term157 _132718 s f x) = (term152 _132718 s f x).
Proof. exact (MK_COMB (@lem7110615) (@lem7110614 _132718 s f x)). Qed.
Lemma lem7110617 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) : (term157 _132718 s f x) = (term153 _132718 s f x).
Proof. exact (TRANS (@lem7110616 _132718 s f x) (@lem7110611 _132718 s f x)). Qed.
Lemma lem7110618 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term158 _132718 s f) = (term159 _132718 s f).
Proof. exact (fun_ext (fun x : _132718 => @lem7110617 _132718 s f x)). Qed.
Lemma lem7110619 {_132718 : Type'} : (@ex _132718) = (@ex _132718).
Proof. exact (eq_refl (@ex _132718)). Qed.
Lemma lem7110620 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term155 _132718 s f) = (term160 _132718 s f).
Proof. exact (MK_COMB (@lem7110619 _132718) (@lem7110618 _132718 s f)). Qed.
Lemma lem7110621 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term154 _132718 s f) = (term160 _132718 s f).
Proof. exact (TRANS (@lem7110613 _132718 s f) (@lem7110620 _132718 s f)). Qed.
Lemma lem7110622 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term238 _132718 s f b) = (term238 _132718 s f b).
Proof. exact (eq_refl (term238 _132718 s f b)). Qed.
Lemma lem7110623 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7110624 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term161 _132718 s f) = (term162 _132718 s f).
Proof. exact (MK_COMB (@lem7110623) (@lem7110621 _132718 s f)). Qed.
Lemma lem7110625 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term239 _132718 s f b) = (term240 _132718 s f b).
Proof. exact (MK_COMB (@lem7110624 _132718 s f) (@lem7110622 _132718 s f b)). Qed.
Lemma lem7110626 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term241 _132718 s f b) = (term239 _132718 s f b).
Proof. exact (@lem17045 (term73 _132718 s f) (term70 _132718 s f b)). Qed.
Lemma lem7110627 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term241 _132718 s f b) = (term240 _132718 s f b).
Proof. exact (TRANS (@lem7110626 _132718 s f b) (@lem7110625 _132718 s f b)). Qed.
Lemma lem7110629 {_132718 : Type'} (s : _132718 -> Prop) : (term242 _132718 s) = (term242 _132718 s).
Proof. exact (eq_refl (term242 _132718 s)). Qed.
Lemma lem7110630 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term243 _132718 s f b) = (term244 _132718 s f b).
Proof. exact (MK_COMB (@lem7110629 _132718 s) (@lem7110627 _132718 s f b)). Qed.
Lemma lem7110631 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term245 _132718 s f b) = (term243 _132718 s f b).
Proof. exact (@lem17045 (@FINITE _132718 s) (term74 _132718 s f b)). Qed.
Lemma lem7110632 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term245 _132718 s f b) = (term244 _132718 s f b).
Proof. exact (TRANS (@lem7110631 _132718 s f b) (@lem7110630 _132718 s f b)). Qed.
Lemma lem7110639 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) (b : real) : (term67 _132718 s f x b) = (term246 _132718 s f x b).
Proof. exact (@lem17265 (@IN _132718 x s) (term247 _132718 f x b)). Qed.
Lemma lem7110640 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term68 _132718 s f b) = (term248 _132718 s f b).
Proof. exact (fun_ext (fun x : _132718 => @lem7110639 _132718 s f x b)). Qed.
Lemma lem7110641 {_132718 : Type'} : (@all _132718) = (@all _132718).
Proof. exact (eq_refl (@all _132718)). Qed.
Lemma lem7110642 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term69 _132718 s f b) = (term249 _132718 s f b).
Proof. exact (MK_COMB (@lem7110641 _132718) (@lem7110640 _132718 s f b)). Qed.
Lemma lem7110643 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7110644 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term250 _132718 s f b) = (term251 _132718 s f b).
Proof. exact (MK_COMB (@lem7110643) (@lem7110632 _132718 s f b)). Qed.
Lemma lem7110645 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term252 _132718 s f b) = (term253 _132718 s f b).
Proof. exact (MK_COMB (@lem7110644 _132718 s f b) (@lem7110642 _132718 s f b)). Qed.
Lemma lem7110646 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term77 _132718 s f b) = (term252 _132718 s f b).
Proof. exact (@lem17265 (term75 _132718 s f b) (term69 _132718 s f b)). Qed.
Lemma lem7110647 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term77 _132718 s f b) = (term253 _132718 s f b).
Proof. exact (TRANS (@lem7110646 _132718 s f b) (@lem7110645 _132718 s f b)). Qed.
Lemma lem7110648 {_132718 : Type'} (f : _132718 -> real) (b : real) : (term78 _132718 f b) = (term254 _132718 f b).
Proof. exact (fun_ext (fun s : _132718 -> Prop => @lem7110647 _132718 s f b)). Qed.
Lemma lem7110649 {_132718 : Type'} : (@all (_132718 -> Prop)) = (@all (_132718 -> Prop)).
Proof. exact (eq_refl (@all (_132718 -> Prop))). Qed.
Lemma lem7110650 {_132718 : Type'} (f : _132718 -> real) (b : real) : (term79 _132718 f b) = (term255 _132718 f b).
Proof. exact (MK_COMB (@lem7110649 _132718) (@lem7110648 _132718 f b)). Qed.
Lemma lem7110651 {_132718 : Type'} (f : _132718 -> real) : (term80 _132718 f) = (term256 _132718 f).
Proof. exact (fun_ext (fun b : real => @lem7110650 _132718 f b)). Qed.
Lemma lem7110652 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7110653 {_132718 : Type'} (f : _132718 -> real) : (term81 _132718 f) = (term257 _132718 f).
Proof. exact (MK_COMB (@lem7110652) (@lem7110651 _132718 f)). Qed.
Lemma lem7110654 {_132718 : Type'} : (term82 _132718) = (term258 _132718).
Proof. exact (fun_ext (fun f : _132718 -> real => @lem7110653 _132718 f)). Qed.
Lemma lem7110655 {_132718 : Type'} : (@all (_132718 -> real)) = (@all (_132718 -> real)).
Proof. exact (eq_refl (@all (_132718 -> real))). Qed.
Lemma lem7110656 {_132718 : Type'} : (term50 _132718) = (term259 _132718).
Proof. exact (MK_COMB (@lem7110655 _132718) (@lem7110654 _132718)). Qed.
Lemma lem7110811 {A : Type'} (P : A -> Prop) (Q : Prop) : (term169 A P Q) = (term170 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7110812 {_132718 : Type'} (P : _132718 -> Prop) (Q : Prop) : (term169 _132718 P Q) = (term170 _132718 P Q).
Proof. exact (@lem7110811 _132718 P Q). Qed.
Lemma lem7110813 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term260 _132718 s f b) = (term261 _132718 s f b).
Proof. exact (@lem7110812 _132718 (term159 _132718 s f) (term238 _132718 s f b)). Qed.
Lemma lem7110814 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) : (term173 _132718 s f x) = (term153 _132718 s f x).
Proof. exact (eq_refl (term173 _132718 s f x)). Qed.
Lemma lem7110815 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term174 _132718 s f) = (term159 _132718 s f).
Proof. exact (fun_ext (fun x : _132718 => @lem7110814 _132718 s f x)). Qed.
Lemma lem7110816 {_132718 : Type'} : (@ex _132718) = (@ex _132718).
Proof. exact (eq_refl (@ex _132718)). Qed.
Lemma lem7110817 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term175 _132718 s f) = (term160 _132718 s f).
Proof. exact (MK_COMB (@lem7110816 _132718) (@lem7110815 _132718 s f)). Qed.
Lemma lem7110818 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7110819 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term176 _132718 s f) = (term162 _132718 s f).
Proof. exact (MK_COMB (@lem7110818) (@lem7110817 _132718 s f)). Qed.
Lemma lem7110820 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term238 _132718 s f b) = (term238 _132718 s f b).
Proof. exact (eq_refl (term238 _132718 s f b)). Qed.
Lemma lem7110821 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term260 _132718 s f b) = (term240 _132718 s f b).
Proof. exact (MK_COMB (@lem7110819 _132718 s f) (@lem7110820 _132718 s f b)). Qed.
Lemma lem7110822 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7110823 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term262 _132718 s f b) = (term263 _132718 s f b).
Proof. exact (MK_COMB (@lem7110822) (@lem7110821 _132718 s f b)). Qed.
Lemma lem7110824 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) : (term173 _132718 s f x) = (term153 _132718 s f x).
Proof. exact (eq_refl (term173 _132718 s f x)). Qed.
Lemma lem7110825 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7110826 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) : (term179 _132718 s f x) = (term180 _132718 s f x).
Proof. exact (MK_COMB (@lem7110825) (@lem7110824 _132718 s f x)). Qed.
Lemma lem7110827 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term238 _132718 s f b) = (term238 _132718 s f b).
Proof. exact (eq_refl (term238 _132718 s f b)). Qed.
Lemma lem7110828 {_132718 : Type'} (x : _132718) (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term264 _132718 x s f b) = (term265 _132718 x s f b).
Proof. exact (MK_COMB (@lem7110826 _132718 s f x) (@lem7110827 _132718 s f b)). Qed.
Lemma lem7110829 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term266 _132718 s f b) = (term267 _132718 s f b).
Proof. exact (fun_ext (fun x : _132718 => @lem7110828 _132718 x s f b)). Qed.
Lemma lem7110830 {_132718 : Type'} : (@ex _132718) = (@ex _132718).
Proof. exact (eq_refl (@ex _132718)). Qed.
Lemma lem7110831 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term261 _132718 s f b) = (term268 _132718 s f b).
Proof. exact (MK_COMB (@lem7110830 _132718) (@lem7110829 _132718 s f b)). Qed.
Lemma lem7110832 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : ((term260 _132718 s f b) = (term261 _132718 s f b)) = ((term240 _132718 s f b) = (term268 _132718 s f b)).
Proof. exact (MK_COMB (@lem7110823 _132718 s f b) (@lem7110831 _132718 s f b)). Qed.
Lemma lem7110833 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term240 _132718 s f b) = (term268 _132718 s f b).
Proof. exact (EQ_MP (@lem7110832 _132718 s f b) (@lem7110813 _132718 s f b)). Qed.
Lemma lem7110834 {_132718 : Type'} (s : _132718 -> Prop) : (term242 _132718 s) = (term242 _132718 s).
Proof. exact (eq_refl (term242 _132718 s)). Qed.
Lemma lem7110835 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term244 _132718 s f b) = (term269 _132718 s f b).
Proof. exact (MK_COMB (@lem7110834 _132718 s) (@lem7110833 _132718 s f b)). Qed.
Lemma lem7110837 {A : Type'} (P : Prop) (Q : A -> Prop) : (term270 A P Q) = (term271 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7110838 {_132718 : Type'} (P : Prop) (Q : _132718 -> Prop) : (term270 _132718 P Q) = (term271 _132718 P Q).
Proof. exact (@lem7110837 _132718 P Q). Qed.
Lemma lem7110839 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term272 _132718 s f b) = (term273 _132718 s f b).
Proof. exact (@lem7110838 _132718 (term274 _132718 s) (term267 _132718 s f b)). Qed.
Lemma lem7110840 {_132718 : Type'} (x : _132718) (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term275 _132718 s f b x) = (term265 _132718 x s f b).
Proof. exact (eq_refl (term275 _132718 s f b x)). Qed.
Lemma lem7110841 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term276 _132718 s f b) = (term267 _132718 s f b).
Proof. exact (fun_ext (fun x : _132718 => @lem7110840 _132718 x s f b)). Qed.
Lemma lem7110842 {_132718 : Type'} : (@ex _132718) = (@ex _132718).
Proof. exact (eq_refl (@ex _132718)). Qed.
Lemma lem7110843 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term277 _132718 s f b) = (term268 _132718 s f b).
Proof. exact (MK_COMB (@lem7110842 _132718) (@lem7110841 _132718 s f b)). Qed.
Lemma lem7110844 {_132718 : Type'} (s : _132718 -> Prop) : (term242 _132718 s) = (term242 _132718 s).
Proof. exact (eq_refl (term242 _132718 s)). Qed.
Lemma lem7110845 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term272 _132718 s f b) = (term269 _132718 s f b).
Proof. exact (MK_COMB (@lem7110844 _132718 s) (@lem7110843 _132718 s f b)). Qed.
Lemma lem7110846 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7110847 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term278 _132718 s f b) = (term279 _132718 s f b).
Proof. exact (MK_COMB (@lem7110846) (@lem7110845 _132718 s f b)). Qed.
Lemma lem7110848 {_132718 : Type'} (x : _132718) (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term275 _132718 s f b x) = (term265 _132718 x s f b).
Proof. exact (eq_refl (term275 _132718 s f b x)). Qed.
Lemma lem7110849 {_132718 : Type'} (s : _132718 -> Prop) : (term242 _132718 s) = (term242 _132718 s).
Proof. exact (eq_refl (term242 _132718 s)). Qed.
Lemma lem7110850 {_132718 : Type'} (x : _132718) (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term280 _132718 s f b x) = (term281 _132718 x s f b).
Proof. exact (MK_COMB (@lem7110849 _132718 s) (@lem7110848 _132718 x s f b)). Qed.
Lemma lem7110851 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term282 _132718 s f b) = (term283 _132718 s f b).
Proof. exact (fun_ext (fun x : _132718 => @lem7110850 _132718 x s f b)). Qed.
Lemma lem7110852 {_132718 : Type'} : (@ex _132718) = (@ex _132718).
Proof. exact (eq_refl (@ex _132718)). Qed.
Lemma lem7110853 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term273 _132718 s f b) = (term284 _132718 s f b).
Proof. exact (MK_COMB (@lem7110852 _132718) (@lem7110851 _132718 s f b)). Qed.
Lemma lem7110854 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : ((term272 _132718 s f b) = (term273 _132718 s f b)) = ((term269 _132718 s f b) = (term284 _132718 s f b)).
Proof. exact (MK_COMB (@lem7110847 _132718 s f b) (@lem7110853 _132718 s f b)). Qed.
Lemma lem7110855 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term269 _132718 s f b) = (term284 _132718 s f b).
Proof. exact (EQ_MP (@lem7110854 _132718 s f b) (@lem7110839 _132718 s f b)). Qed.
Lemma lem7110856 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term244 _132718 s f b) = (term284 _132718 s f b).
Proof. exact (TRANS (@lem7110835 _132718 s f b) (@lem7110855 _132718 s f b)). Qed.
Lemma lem7110857 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7110858 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term251 _132718 s f b) = (term285 _132718 s f b).
Proof. exact (MK_COMB (@lem7110857) (@lem7110856 _132718 s f b)). Qed.
Lemma lem7110859 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term249 _132718 s f b) = (term249 _132718 s f b).
Proof. exact (eq_refl (term249 _132718 s f b)). Qed.
Lemma lem7110860 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term253 _132718 s f b) = (term286 _132718 s f b).
Proof. exact (MK_COMB (@lem7110858 _132718 s f b) (@lem7110859 _132718 s f b)). Qed.
Lemma lem7110862 {A : Type'} (P : A -> Prop) (Q : Prop) : (term169 A P Q) = (term170 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7110863 {_132718 : Type'} (P : _132718 -> Prop) (Q : Prop) : (term169 _132718 P Q) = (term170 _132718 P Q).
Proof. exact (@lem7110862 _132718 P Q). Qed.
Lemma lem7110864 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term287 _132718 s f b) = (term288 _132718 s f b).
Proof. exact (@lem7110863 _132718 (term283 _132718 s f b) (term249 _132718 s f b)). Qed.
Lemma lem7110865 {_132718 : Type'} (x : _132718) (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term289 _132718 s f b x) = (term281 _132718 x s f b).
Proof. exact (eq_refl (term289 _132718 s f b x)). Qed.
Lemma lem7110866 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term290 _132718 s f b) = (term283 _132718 s f b).
Proof. exact (fun_ext (fun x : _132718 => @lem7110865 _132718 x s f b)). Qed.
Lemma lem7110867 {_132718 : Type'} : (@ex _132718) = (@ex _132718).
Proof. exact (eq_refl (@ex _132718)). Qed.
Lemma lem7110868 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term291 _132718 s f b) = (term284 _132718 s f b).
Proof. exact (MK_COMB (@lem7110867 _132718) (@lem7110866 _132718 s f b)). Qed.
Lemma lem7110869 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7110870 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term292 _132718 s f b) = (term285 _132718 s f b).
Proof. exact (MK_COMB (@lem7110869) (@lem7110868 _132718 s f b)). Qed.
Lemma lem7110871 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term249 _132718 s f b) = (term249 _132718 s f b).
Proof. exact (eq_refl (term249 _132718 s f b)). Qed.
Lemma lem7110872 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term287 _132718 s f b) = (term286 _132718 s f b).
Proof. exact (MK_COMB (@lem7110870 _132718 s f b) (@lem7110871 _132718 s f b)). Qed.
Lemma lem7110873 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7110874 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term293 _132718 s f b) = (term294 _132718 s f b).
Proof. exact (MK_COMB (@lem7110873) (@lem7110872 _132718 s f b)). Qed.
Lemma lem7110875 {_132718 : Type'} (x : _132718) (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term289 _132718 s f b x) = (term281 _132718 x s f b).
Proof. exact (eq_refl (term289 _132718 s f b x)). Qed.
Lemma lem7110876 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7110877 {_132718 : Type'} (x : _132718) (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term295 _132718 s f b x) = (term296 _132718 x s f b).
Proof. exact (MK_COMB (@lem7110876) (@lem7110875 _132718 x s f b)). Qed.
Lemma lem7110878 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term249 _132718 s f b) = (term249 _132718 s f b).
Proof. exact (eq_refl (term249 _132718 s f b)). Qed.
Lemma lem7110879 {_132718 : Type'} (x : _132718) (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term297 _132718 x s f b) = (term298 _132718 x s f b).
Proof. exact (MK_COMB (@lem7110877 _132718 x s f b) (@lem7110878 _132718 s f b)). Qed.
Lemma lem7110880 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term299 _132718 s f b) = (term300 _132718 s f b).
Proof. exact (fun_ext (fun x : _132718 => @lem7110879 _132718 x s f b)). Qed.
Lemma lem7110881 {_132718 : Type'} : (@ex _132718) = (@ex _132718).
Proof. exact (eq_refl (@ex _132718)). Qed.
Lemma lem7110882 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term288 _132718 s f b) = (term301 _132718 s f b).
Proof. exact (MK_COMB (@lem7110881 _132718) (@lem7110880 _132718 s f b)). Qed.
Lemma lem7110883 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : ((term287 _132718 s f b) = (term288 _132718 s f b)) = ((term286 _132718 s f b) = (term301 _132718 s f b)).
Proof. exact (MK_COMB (@lem7110874 _132718 s f b) (@lem7110882 _132718 s f b)). Qed.
Lemma lem7110884 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term286 _132718 s f b) = (term301 _132718 s f b).
Proof. exact (EQ_MP (@lem7110883 _132718 s f b) (@lem7110864 _132718 s f b)). Qed.
Lemma lem7110885 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term253 _132718 s f b) = (term301 _132718 s f b).
Proof. exact (TRANS (@lem7110860 _132718 s f b) (@lem7110884 _132718 s f b)). Qed.
Lemma lem7110886 {_132718 : Type'} (f : _132718 -> real) (b : real) : (term254 _132718 f b) = (term302 _132718 f b).
Proof. exact (fun_ext (fun s : _132718 -> Prop => @lem7110885 _132718 s f b)). Qed.
Lemma lem7110887 {_132718 : Type'} : (@all (_132718 -> Prop)) = (@all (_132718 -> Prop)).
Proof. exact (eq_refl (@all (_132718 -> Prop))). Qed.
Lemma lem7110888 {_132718 : Type'} (f : _132718 -> real) (b : real) : (term255 _132718 f b) = (term303 _132718 f b).
Proof. exact (MK_COMB (@lem7110887 _132718) (@lem7110886 _132718 f b)). Qed.
Lemma lem7110890 {A B : Type'} (P : type1413 A B) : (term188 A B P) = (term189 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7110891 {_132718 : Type'} (P : type672 _132718) : (term190 _132718 P) = (term191 _132718 P).
Proof. exact (@lem7110890 (_132718 -> Prop) _132718 P). Qed.
Lemma lem7110892 {_132718 : Type'} (f : _132718 -> real) (b : real) : (term304 _132718 f b) = (term305 _132718 f b).
Proof. exact (@lem7110891 _132718 (term306 _132718 f b)). Qed.
Lemma lem7110893 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term307 _132718 f b s) = (term300 _132718 s f b).
Proof. exact (eq_refl (term307 _132718 f b s)). Qed.
Lemma lem7110894 {_132718 : Type'} (x : _132718) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7110895 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) (x : _132718) : (term308 _132718 f b s x) = (term309 _132718 s f b x).
Proof. exact (MK_COMB (@lem7110893 _132718 s f b) (@lem7110894 _132718 x)). Qed.
Lemma lem7110896 {_132718 : Type'} (x : _132718) (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term309 _132718 s f b x) = (term298 _132718 x s f b).
Proof. exact (eq_refl (term309 _132718 s f b x)). Qed.
Lemma lem7110897 {_132718 : Type'} (x : _132718) (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term308 _132718 f b s x) = (term298 _132718 x s f b).
Proof. exact (TRANS (@lem7110895 _132718 s f b x) (@lem7110896 _132718 x s f b)). Qed.
Lemma lem7110898 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term310 _132718 f b s) = (term300 _132718 s f b).
Proof. exact (fun_ext (fun x : _132718 => @lem7110897 _132718 x s f b)). Qed.
Lemma lem7110899 {_132718 : Type'} : (@ex _132718) = (@ex _132718).
Proof. exact (eq_refl (@ex _132718)). Qed.
Lemma lem7110900 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term311 _132718 f b s) = (term301 _132718 s f b).
Proof. exact (MK_COMB (@lem7110899 _132718) (@lem7110898 _132718 s f b)). Qed.
Lemma lem7110901 {_132718 : Type'} (f : _132718 -> real) (b : real) : (term312 _132718 f b) = (term302 _132718 f b).
Proof. exact (fun_ext (fun s : _132718 -> Prop => @lem7110900 _132718 s f b)). Qed.
Lemma lem7110902 {_132718 : Type'} : (@all (_132718 -> Prop)) = (@all (_132718 -> Prop)).
Proof. exact (eq_refl (@all (_132718 -> Prop))). Qed.
Lemma lem7110903 {_132718 : Type'} (f : _132718 -> real) (b : real) : (term304 _132718 f b) = (term303 _132718 f b).
Proof. exact (MK_COMB (@lem7110902 _132718) (@lem7110901 _132718 f b)). Qed.
Lemma lem7110904 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7110905 {_132718 : Type'} (f : _132718 -> real) (b : real) : (term313 _132718 f b) = (term314 _132718 f b).
Proof. exact (MK_COMB (@lem7110904) (@lem7110903 _132718 f b)). Qed.
Lemma lem7110906 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term307 _132718 f b s) = (term300 _132718 s f b).
Proof. exact (eq_refl (term307 _132718 f b s)). Qed.
Lemma lem7110907 {_132718 : Type'} (x : type684 _132718) (s : _132718 -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem7110908 {_132718 : Type'} (f : _132718 -> real) (b : real) (x : type684 _132718) (s : _132718 -> Prop) : (term315 _132718 f b x s) = (term316 _132718 f b x s).
Proof. exact (MK_COMB (@lem7110906 _132718 s f b) (@lem7110907 _132718 x s)). Qed.
Lemma lem7110909 {_132718 : Type'} (x : type684 _132718) (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term316 _132718 f b x s) = (term317 _132718 x s f b).
Proof. exact (eq_refl (term316 _132718 f b x s)). Qed.
Lemma lem7110910 {_132718 : Type'} (x : type684 _132718) (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term315 _132718 f b x s) = (term317 _132718 x s f b).
Proof. exact (TRANS (@lem7110908 _132718 f b x s) (@lem7110909 _132718 x s f b)). Qed.
Lemma lem7110911 {_132718 : Type'} (x : type684 _132718) (f : _132718 -> real) (b : real) : (term318 _132718 f b x) = (term319 _132718 x f b).
Proof. exact (fun_ext (fun s : _132718 -> Prop => @lem7110910 _132718 x s f b)). Qed.
Lemma lem7110912 {_132718 : Type'} : (@all (_132718 -> Prop)) = (@all (_132718 -> Prop)).
Proof. exact (eq_refl (@all (_132718 -> Prop))). Qed.
Lemma lem7110913 {_132718 : Type'} (x : type684 _132718) (f : _132718 -> real) (b : real) : (term320 _132718 f b x) = (term321 _132718 x f b).
Proof. exact (MK_COMB (@lem7110912 _132718) (@lem7110911 _132718 x f b)). Qed.
Lemma lem7110914 {_132718 : Type'} (f : _132718 -> real) (b : real) : (term322 _132718 f b) = (term323 _132718 f b).
Proof. exact (fun_ext (fun x : type684 _132718 => @lem7110913 _132718 x f b)). Qed.
Lemma lem7110915 {_132718 : Type'} : (@ex ((_132718 -> Prop) -> _132718)) = (@ex ((_132718 -> Prop) -> _132718)).
Proof. exact (eq_refl (@ex ((_132718 -> Prop) -> _132718))). Qed.
Lemma lem7110916 {_132718 : Type'} (f : _132718 -> real) (b : real) : (term305 _132718 f b) = (term324 _132718 f b).
Proof. exact (MK_COMB (@lem7110915 _132718) (@lem7110914 _132718 f b)). Qed.
Lemma lem7110917 {_132718 : Type'} (f : _132718 -> real) (b : real) : ((term304 _132718 f b) = (term305 _132718 f b)) = ((term303 _132718 f b) = (term324 _132718 f b)).
Proof. exact (MK_COMB (@lem7110905 _132718 f b) (@lem7110916 _132718 f b)). Qed.
Lemma lem7110918 {_132718 : Type'} (f : _132718 -> real) (b : real) : (term303 _132718 f b) = (term324 _132718 f b).
Proof. exact (EQ_MP (@lem7110917 _132718 f b) (@lem7110892 _132718 f b)). Qed.
Lemma lem7110919 {_132718 : Type'} (f : _132718 -> real) (b : real) : (term255 _132718 f b) = (term324 _132718 f b).
Proof. exact (TRANS (@lem7110888 _132718 f b) (@lem7110918 _132718 f b)). Qed.
Lemma lem7110920 {_132718 : Type'} (f : _132718 -> real) : (term256 _132718 f) = (term325 _132718 f).
Proof. exact (fun_ext (fun b : real => @lem7110919 _132718 f b)). Qed.
Lemma lem7110921 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7110922 {_132718 : Type'} (f : _132718 -> real) : (term257 _132718 f) = (term326 _132718 f).
Proof. exact (MK_COMB (@lem7110921) (@lem7110920 _132718 f)). Qed.
Lemma lem7110924 {A B : Type'} (P : type1413 A B) : (term188 A B P) = (term189 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7110925 {_132718 : Type'} (P : type1615 _132718) : (term327 _132718 P) = (term328 _132718 P).
Proof. exact (@lem7110924 real (type684 _132718) P). Qed.
Lemma lem7110926 {_132718 : Type'} (f : _132718 -> real) : (term329 _132718 f) = (term330 _132718 f).
Proof. exact (@lem7110925 _132718 (term331 _132718 f)). Qed.
Lemma lem7110927 {_132718 : Type'} (f : _132718 -> real) (b : real) : (term332 _132718 f b) = (term323 _132718 f b).
Proof. exact (eq_refl (term332 _132718 f b)). Qed.
Lemma lem7110928 {_132718 : Type'} (x : type684 _132718) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7110929 {_132718 : Type'} (f : _132718 -> real) (b : real) (x : type684 _132718) : (term333 _132718 f b x) = (term334 _132718 f b x).
Proof. exact (MK_COMB (@lem7110927 _132718 f b) (@lem7110928 _132718 x)). Qed.
Lemma lem7110930 {_132718 : Type'} (x : type684 _132718) (f : _132718 -> real) (b : real) : (term334 _132718 f b x) = (term321 _132718 x f b).
Proof. exact (eq_refl (term334 _132718 f b x)). Qed.
Lemma lem7110931 {_132718 : Type'} (x : type684 _132718) (f : _132718 -> real) (b : real) : (term333 _132718 f b x) = (term321 _132718 x f b).
Proof. exact (TRANS (@lem7110929 _132718 f b x) (@lem7110930 _132718 x f b)). Qed.
Lemma lem7110932 {_132718 : Type'} (f : _132718 -> real) (b : real) : (term335 _132718 f b) = (term323 _132718 f b).
Proof. exact (fun_ext (fun x : type684 _132718 => @lem7110931 _132718 x f b)). Qed.
Lemma lem7110933 {_132718 : Type'} : (@ex ((_132718 -> Prop) -> _132718)) = (@ex ((_132718 -> Prop) -> _132718)).
Proof. exact (eq_refl (@ex ((_132718 -> Prop) -> _132718))). Qed.
Lemma lem7110934 {_132718 : Type'} (f : _132718 -> real) (b : real) : (term336 _132718 f b) = (term324 _132718 f b).
Proof. exact (MK_COMB (@lem7110933 _132718) (@lem7110932 _132718 f b)). Qed.
Lemma lem7110935 {_132718 : Type'} (f : _132718 -> real) : (term337 _132718 f) = (term325 _132718 f).
Proof. exact (fun_ext (fun b : real => @lem7110934 _132718 f b)). Qed.
Lemma lem7110936 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7110937 {_132718 : Type'} (f : _132718 -> real) : (term329 _132718 f) = (term326 _132718 f).
Proof. exact (MK_COMB (@lem7110936) (@lem7110935 _132718 f)). Qed.
Lemma lem7110938 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7110939 {_132718 : Type'} (f : _132718 -> real) : (term338 _132718 f) = (term339 _132718 f).
Proof. exact (MK_COMB (@lem7110938) (@lem7110937 _132718 f)). Qed.
Lemma lem7110940 {_132718 : Type'} (f : _132718 -> real) (b : real) : (term332 _132718 f b) = (term323 _132718 f b).
Proof. exact (eq_refl (term332 _132718 f b)). Qed.
Lemma lem7110941 {_132718 : Type'} (x : type1616 _132718) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem7110942 {_132718 : Type'} (f : _132718 -> real) (x : type1616 _132718) (b : real) : (term340 _132718 f x b) = (term341 _132718 f x b).
Proof. exact (MK_COMB (@lem7110940 _132718 f b) (@lem7110941 _132718 x b)). Qed.
Lemma lem7110943 {_132718 : Type'} (x : type1616 _132718) (f : _132718 -> real) (b : real) : (term341 _132718 f x b) = (term342 _132718 x f b).
Proof. exact (eq_refl (term341 _132718 f x b)). Qed.
Lemma lem7110944 {_132718 : Type'} (x : type1616 _132718) (f : _132718 -> real) (b : real) : (term340 _132718 f x b) = (term342 _132718 x f b).
Proof. exact (TRANS (@lem7110942 _132718 f x b) (@lem7110943 _132718 x f b)). Qed.
Lemma lem7110945 {_132718 : Type'} (x : type1616 _132718) (f : _132718 -> real) : (term343 _132718 f x) = (term344 _132718 x f).
Proof. exact (fun_ext (fun b : real => @lem7110944 _132718 x f b)). Qed.
Lemma lem7110946 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7110947 {_132718 : Type'} (x : type1616 _132718) (f : _132718 -> real) : (term345 _132718 f x) = (term346 _132718 x f).
Proof. exact (MK_COMB (@lem7110946) (@lem7110945 _132718 x f)). Qed.
Lemma lem7110948 {_132718 : Type'} (f : _132718 -> real) : (term347 _132718 f) = (term348 _132718 f).
Proof. exact (fun_ext (fun x : type1616 _132718 => @lem7110947 _132718 x f)). Qed.
Lemma lem7110949 {_132718 : Type'} : (@ex (real -> (_132718 -> Prop) -> _132718)) = (@ex (real -> (_132718 -> Prop) -> _132718)).
Proof. exact (eq_refl (@ex (real -> (_132718 -> Prop) -> _132718))). Qed.
Lemma lem7110950 {_132718 : Type'} (f : _132718 -> real) : (term330 _132718 f) = (term349 _132718 f).
Proof. exact (MK_COMB (@lem7110949 _132718) (@lem7110948 _132718 f)). Qed.
Lemma lem7110951 {_132718 : Type'} (f : _132718 -> real) : ((term329 _132718 f) = (term330 _132718 f)) = ((term326 _132718 f) = (term349 _132718 f)).
Proof. exact (MK_COMB (@lem7110939 _132718 f) (@lem7110950 _132718 f)). Qed.
Lemma lem7110952 {_132718 : Type'} (f : _132718 -> real) : (term326 _132718 f) = (term349 _132718 f).
Proof. exact (EQ_MP (@lem7110951 _132718 f) (@lem7110926 _132718 f)). Qed.
Lemma lem7110953 {_132718 : Type'} (f : _132718 -> real) : (term257 _132718 f) = (term349 _132718 f).
Proof. exact (TRANS (@lem7110922 _132718 f) (@lem7110952 _132718 f)). Qed.
Lemma lem7110954 {_132718 : Type'} : (term258 _132718) = (term350 _132718).
Proof. exact (fun_ext (fun f : _132718 -> real => @lem7110953 _132718 f)). Qed.
Lemma lem7110955 {_132718 : Type'} : (@all (_132718 -> real)) = (@all (_132718 -> real)).
Proof. exact (eq_refl (@all (_132718 -> real))). Qed.
Lemma lem7110956 {_132718 : Type'} : (term259 _132718) = (term351 _132718).
Proof. exact (MK_COMB (@lem7110955 _132718) (@lem7110954 _132718)). Qed.
Lemma lem7110958 {A B : Type'} (P : type1413 A B) : (term188 A B P) = (term189 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7110959 {_132718 : Type'} (P : type712 _132718) : (term352 _132718 P) = (term353 _132718 P).
Proof. exact (@lem7110958 (_132718 -> real) (type1616 _132718) P). Qed.
Lemma lem7110960 {_132718 : Type'} : (term354 _132718) = (term355 _132718).
Proof. exact (@lem7110959 _132718 (term356 _132718)). Qed.
Lemma lem7110961 {_132718 : Type'} (f : _132718 -> real) : (term357 _132718 f) = (term348 _132718 f).
Proof. exact (eq_refl (term357 _132718 f)). Qed.
Lemma lem7110962 {_132718 : Type'} (x : type1616 _132718) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7110963 {_132718 : Type'} (f : _132718 -> real) (x : type1616 _132718) : (term358 _132718 f x) = (term359 _132718 f x).
Proof. exact (MK_COMB (@lem7110961 _132718 f) (@lem7110962 _132718 x)). Qed.
Lemma lem7110964 {_132718 : Type'} (x : type1616 _132718) (f : _132718 -> real) : (term359 _132718 f x) = (term346 _132718 x f).
Proof. exact (eq_refl (term359 _132718 f x)). Qed.
Lemma lem7110965 {_132718 : Type'} (x : type1616 _132718) (f : _132718 -> real) : (term358 _132718 f x) = (term346 _132718 x f).
Proof. exact (TRANS (@lem7110963 _132718 f x) (@lem7110964 _132718 x f)). Qed.
Lemma lem7110966 {_132718 : Type'} (f : _132718 -> real) : (term360 _132718 f) = (term348 _132718 f).
Proof. exact (fun_ext (fun x : type1616 _132718 => @lem7110965 _132718 x f)). Qed.
Lemma lem7110967 {_132718 : Type'} : (@ex (real -> (_132718 -> Prop) -> _132718)) = (@ex (real -> (_132718 -> Prop) -> _132718)).
Proof. exact (eq_refl (@ex (real -> (_132718 -> Prop) -> _132718))). Qed.
Lemma lem7110968 {_132718 : Type'} (f : _132718 -> real) : (term361 _132718 f) = (term349 _132718 f).
Proof. exact (MK_COMB (@lem7110967 _132718) (@lem7110966 _132718 f)). Qed.
Lemma lem7110969 {_132718 : Type'} : (term362 _132718) = (term350 _132718).
Proof. exact (fun_ext (fun f : _132718 -> real => @lem7110968 _132718 f)). Qed.
Lemma lem7110970 {_132718 : Type'} : (@all (_132718 -> real)) = (@all (_132718 -> real)).
Proof. exact (eq_refl (@all (_132718 -> real))). Qed.
Lemma lem7110971 {_132718 : Type'} : (term354 _132718) = (term351 _132718).
Proof. exact (MK_COMB (@lem7110970 _132718) (@lem7110969 _132718)). Qed.
Lemma lem7110972 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7110973 {_132718 : Type'} : (term363 _132718) = (term364 _132718).
Proof. exact (MK_COMB (@lem7110972) (@lem7110971 _132718)). Qed.
Lemma lem7110974 {_132718 : Type'} (f : _132718 -> real) : (term357 _132718 f) = (term348 _132718 f).
Proof. exact (eq_refl (term357 _132718 f)). Qed.
Lemma lem7110975 {_132718 : Type'} (x : type714 _132718) (f : _132718 -> real) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem7110976 {_132718 : Type'} (x : type714 _132718) (f : _132718 -> real) : (term365 _132718 x f) = (term366 _132718 x f).
Proof. exact (MK_COMB (@lem7110974 _132718 f) (@lem7110975 _132718 x f)). Qed.
Lemma lem7110977 {_132718 : Type'} (x : type714 _132718) (f : _132718 -> real) : (term366 _132718 x f) = (term367 _132718 x f).
Proof. exact (eq_refl (term366 _132718 x f)). Qed.
Lemma lem7110978 {_132718 : Type'} (x : type714 _132718) (f : _132718 -> real) : (term365 _132718 x f) = (term367 _132718 x f).
Proof. exact (TRANS (@lem7110976 _132718 x f) (@lem7110977 _132718 x f)). Qed.
Lemma lem7110979 {_132718 : Type'} (x : type714 _132718) : (term368 _132718 x) = (term369 _132718 x).
Proof. exact (fun_ext (fun f : _132718 -> real => @lem7110978 _132718 x f)). Qed.
Lemma lem7110980 {_132718 : Type'} : (@all (_132718 -> real)) = (@all (_132718 -> real)).
Proof. exact (eq_refl (@all (_132718 -> real))). Qed.
Lemma lem7110981 {_132718 : Type'} (x : type714 _132718) : (term370 _132718 x) = (term371 _132718 x).
Proof. exact (MK_COMB (@lem7110980 _132718) (@lem7110979 _132718 x)). Qed.
Lemma lem7110982 {_132718 : Type'} : (term372 _132718) = (term373 _132718).
Proof. exact (fun_ext (fun x : type714 _132718 => @lem7110981 _132718 x)). Qed.
Lemma lem7110983 {_132718 : Type'} : (@ex ((_132718 -> real) -> real -> (_132718 -> Prop) -> _132718)) = (@ex ((_132718 -> real) -> real -> (_132718 -> Prop) -> _132718)).
Proof. exact (eq_refl (@ex ((_132718 -> real) -> real -> (_132718 -> Prop) -> _132718))). Qed.
Lemma lem7110984 {_132718 : Type'} : (term355 _132718) = (term374 _132718).
Proof. exact (MK_COMB (@lem7110983 _132718) (@lem7110982 _132718)). Qed.
Lemma lem7110985 {_132718 : Type'} : ((term354 _132718) = (term355 _132718)) = ((term351 _132718) = (term374 _132718)).
Proof. exact (MK_COMB (@lem7110973 _132718) (@lem7110984 _132718)). Qed.
Lemma lem7110986 {_132718 : Type'} : (term351 _132718) = (term374 _132718).
Proof. exact (EQ_MP (@lem7110985 _132718) (@lem7110960 _132718)). Qed.
Lemma lem7110988 {_132718 : Type'} : (term259 _132718) = (term374 _132718).
Proof. exact (TRANS (@lem7110956 _132718) (@lem7110986 _132718)). Qed.
Lemma lem7110989 {_132718 : Type'} : (term50 _132718) = (term374 _132718).
Proof. exact (TRANS (@lem7110656 _132718) (@lem7110988 _132718)). Qed.
Lemma lem7110990 {_132718 : Type'} (h1 : term50 _132718) : term374 _132718.
Proof. exact (EQ_MP (@lem7110989 _132718) (@lem7109904 _132718 h1)). Qed.
Lemma lem7110998 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term152 A s f x) = (term153 A s f x).
Proof. exact (@lem17362 (@IN A x s) (term90 A f x)). Qed.
Lemma lem7110999 {A : Type'} (P : A -> Prop) : (term103 A P) = (term104 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem7111000 {A : Type'} (s : A -> Prop) (f : A -> real) : (term154 A s f) = (term155 A s f).
Proof. exact (@lem7110999 A (term72 A s f)). Qed.
Lemma lem7111001 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term156 A s f x) = (term71 A s f x).
Proof. exact (eq_refl (term156 A s f x)). Qed.
Lemma lem7111002 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7111003 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term157 A s f x) = (term152 A s f x).
Proof. exact (MK_COMB (@lem7111002) (@lem7111001 A s f x)). Qed.
Lemma lem7111004 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term157 A s f x) = (term153 A s f x).
Proof. exact (TRANS (@lem7111003 A s f x) (@lem7110998 A s f x)). Qed.
Lemma lem7111005 {A : Type'} (s : A -> Prop) (f : A -> real) : (term158 A s f) = (term159 A s f).
Proof. exact (fun_ext (fun x : A => @lem7111004 A s f x)). Qed.
Lemma lem7111006 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7111007 {A : Type'} (s : A -> Prop) (f : A -> real) : (term155 A s f) = (term160 A s f).
Proof. exact (MK_COMB (@lem7111006 A) (@lem7111005 A s f)). Qed.
Lemma lem7111008 {A : Type'} (s : A -> Prop) (f : A -> real) : (term154 A s f) = (term160 A s f).
Proof. exact (TRANS (@lem7111000 A s f) (@lem7111007 A s f)). Qed.
Lemma lem7111009 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term238 A s f b) = (term238 A s f b).
Proof. exact (eq_refl (term238 A s f b)). Qed.
Lemma lem7111010 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7111011 {A : Type'} (s : A -> Prop) (f : A -> real) : (term161 A s f) = (term162 A s f).
Proof. exact (MK_COMB (@lem7111010) (@lem7111008 A s f)). Qed.
Lemma lem7111012 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term239 A s f b) = (term240 A s f b).
Proof. exact (MK_COMB (@lem7111011 A s f) (@lem7111009 A s f b)). Qed.
Lemma lem7111013 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term241 A s f b) = (term239 A s f b).
Proof. exact (@lem17045 (term73 A s f) (term70 A s f b)). Qed.
Lemma lem7111014 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term241 A s f b) = (term240 A s f b).
Proof. exact (TRANS (@lem7111013 A s f b) (@lem7111012 A s f b)). Qed.
Lemma lem7111016 {A : Type'} (s : A -> Prop) : (term242 A s) = (term242 A s).
Proof. exact (eq_refl (term242 A s)). Qed.
Lemma lem7111017 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term243 A s f b) = (term244 A s f b).
Proof. exact (MK_COMB (@lem7111016 A s) (@lem7111014 A s f b)). Qed.
Lemma lem7111018 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term245 A s f b) = (term243 A s f b).
Proof. exact (@lem17045 (@FINITE A s) (term74 A s f b)). Qed.
Lemma lem7111019 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term245 A s f b) = (term244 A s f b).
Proof. exact (TRANS (@lem7111018 A s f b) (@lem7111017 A s f b)). Qed.
Lemma lem7111026 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (b : real) : (term67 A s f x b) = (term246 A s f x b).
Proof. exact (@lem17265 (@IN A x s) (term247 A f x b)). Qed.
Lemma lem7111027 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term68 A s f b) = (term248 A s f b).
Proof. exact (fun_ext (fun x : A => @lem7111026 A s f x b)). Qed.
Lemma lem7111028 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7111029 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term69 A s f b) = (term249 A s f b).
Proof. exact (MK_COMB (@lem7111028 A) (@lem7111027 A s f b)). Qed.
Lemma lem7111030 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7111031 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term250 A s f b) = (term251 A s f b).
Proof. exact (MK_COMB (@lem7111030) (@lem7111019 A s f b)). Qed.
Lemma lem7111032 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term252 A s f b) = (term253 A s f b).
Proof. exact (MK_COMB (@lem7111031 A s f b) (@lem7111029 A s f b)). Qed.
Lemma lem7111033 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term77 A s f b) = (term252 A s f b).
Proof. exact (@lem17265 (term75 A s f b) (term69 A s f b)). Qed.
Lemma lem7111034 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term77 A s f b) = (term253 A s f b).
Proof. exact (TRANS (@lem7111033 A s f b) (@lem7111032 A s f b)). Qed.
Lemma lem7111035 {A : Type'} (f : A -> real) (b : real) : (term78 A f b) = (term254 A f b).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7111034 A s f b)). Qed.
Lemma lem7111036 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7111037 {A : Type'} (f : A -> real) (b : real) : (term79 A f b) = (term255 A f b).
Proof. exact (MK_COMB (@lem7111036 A) (@lem7111035 A f b)). Qed.
Lemma lem7111038 {A : Type'} (f : A -> real) : (term80 A f) = (term256 A f).
Proof. exact (fun_ext (fun b : real => @lem7111037 A f b)). Qed.
Lemma lem7111039 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7111040 {A : Type'} (f : A -> real) : (term81 A f) = (term257 A f).
Proof. exact (MK_COMB (@lem7111039) (@lem7111038 A f)). Qed.
Lemma lem7111041 {A : Type'} : (term82 A) = (term258 A).
Proof. exact (fun_ext (fun f : A -> real => @lem7111040 A f)). Qed.
Lemma lem7111042 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7111043 {A : Type'} : (term50 A) = (term259 A).
Proof. exact (MK_COMB (@lem7111042 A) (@lem7111041 A)). Qed.
Lemma lem7111198 {A : Type'} (P : A -> Prop) (Q : Prop) : (term169 A P Q) = (term170 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7111199 {A : Type'} (P : A -> Prop) (Q : Prop) : (term169 A P Q) = (term170 A P Q).
Proof. exact (@lem7111198 A P Q). Qed.
Lemma lem7111200 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term260 A s f b) = (term261 A s f b).
Proof. exact (@lem7111199 A (term159 A s f) (term238 A s f b)). Qed.
Lemma lem7111201 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term173 A s f x) = (term153 A s f x).
Proof. exact (eq_refl (term173 A s f x)). Qed.
Lemma lem7111202 {A : Type'} (s : A -> Prop) (f : A -> real) : (term174 A s f) = (term159 A s f).
Proof. exact (fun_ext (fun x : A => @lem7111201 A s f x)). Qed.
Lemma lem7111203 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7111204 {A : Type'} (s : A -> Prop) (f : A -> real) : (term175 A s f) = (term160 A s f).
Proof. exact (MK_COMB (@lem7111203 A) (@lem7111202 A s f)). Qed.
Lemma lem7111205 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7111206 {A : Type'} (s : A -> Prop) (f : A -> real) : (term176 A s f) = (term162 A s f).
Proof. exact (MK_COMB (@lem7111205) (@lem7111204 A s f)). Qed.
Lemma lem7111207 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term238 A s f b) = (term238 A s f b).
Proof. exact (eq_refl (term238 A s f b)). Qed.
Lemma lem7111208 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term260 A s f b) = (term240 A s f b).
Proof. exact (MK_COMB (@lem7111206 A s f) (@lem7111207 A s f b)). Qed.
Lemma lem7111209 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7111210 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term262 A s f b) = (term263 A s f b).
Proof. exact (MK_COMB (@lem7111209) (@lem7111208 A s f b)). Qed.
Lemma lem7111211 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term173 A s f x) = (term153 A s f x).
Proof. exact (eq_refl (term173 A s f x)). Qed.
Lemma lem7111212 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7111213 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term179 A s f x) = (term180 A s f x).
Proof. exact (MK_COMB (@lem7111212) (@lem7111211 A s f x)). Qed.
Lemma lem7111214 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term238 A s f b) = (term238 A s f b).
Proof. exact (eq_refl (term238 A s f b)). Qed.
Lemma lem7111215 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term264 A x s f b) = (term265 A x s f b).
Proof. exact (MK_COMB (@lem7111213 A s f x) (@lem7111214 A s f b)). Qed.
Lemma lem7111216 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term266 A s f b) = (term267 A s f b).
Proof. exact (fun_ext (fun x : A => @lem7111215 A x s f b)). Qed.
Lemma lem7111217 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7111218 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term261 A s f b) = (term268 A s f b).
Proof. exact (MK_COMB (@lem7111217 A) (@lem7111216 A s f b)). Qed.
Lemma lem7111219 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : ((term260 A s f b) = (term261 A s f b)) = ((term240 A s f b) = (term268 A s f b)).
Proof. exact (MK_COMB (@lem7111210 A s f b) (@lem7111218 A s f b)). Qed.
Lemma lem7111220 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term240 A s f b) = (term268 A s f b).
Proof. exact (EQ_MP (@lem7111219 A s f b) (@lem7111200 A s f b)). Qed.
Lemma lem7111221 {A : Type'} (s : A -> Prop) : (term242 A s) = (term242 A s).
Proof. exact (eq_refl (term242 A s)). Qed.
Lemma lem7111222 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term244 A s f b) = (term269 A s f b).
Proof. exact (MK_COMB (@lem7111221 A s) (@lem7111220 A s f b)). Qed.
Lemma lem7111224 {A : Type'} (P : Prop) (Q : A -> Prop) : (term270 A P Q) = (term271 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7111225 {A : Type'} (P : Prop) (Q : A -> Prop) : (term270 A P Q) = (term271 A P Q).
Proof. exact (@lem7111224 A P Q). Qed.
Lemma lem7111226 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term272 A s f b) = (term273 A s f b).
Proof. exact (@lem7111225 A (term274 A s) (term267 A s f b)). Qed.
Lemma lem7111227 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term275 A s f b x) = (term265 A x s f b).
Proof. exact (eq_refl (term275 A s f b x)). Qed.
Lemma lem7111228 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term276 A s f b) = (term267 A s f b).
Proof. exact (fun_ext (fun x : A => @lem7111227 A x s f b)). Qed.
Lemma lem7111229 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7111230 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term277 A s f b) = (term268 A s f b).
Proof. exact (MK_COMB (@lem7111229 A) (@lem7111228 A s f b)). Qed.
Lemma lem7111231 {A : Type'} (s : A -> Prop) : (term242 A s) = (term242 A s).
Proof. exact (eq_refl (term242 A s)). Qed.
Lemma lem7111232 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term272 A s f b) = (term269 A s f b).
Proof. exact (MK_COMB (@lem7111231 A s) (@lem7111230 A s f b)). Qed.
Lemma lem7111233 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7111234 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term278 A s f b) = (term279 A s f b).
Proof. exact (MK_COMB (@lem7111233) (@lem7111232 A s f b)). Qed.
Lemma lem7111235 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term275 A s f b x) = (term265 A x s f b).
Proof. exact (eq_refl (term275 A s f b x)). Qed.
Lemma lem7111236 {A : Type'} (s : A -> Prop) : (term242 A s) = (term242 A s).
Proof. exact (eq_refl (term242 A s)). Qed.
Lemma lem7111237 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term280 A s f b x) = (term281 A x s f b).
Proof. exact (MK_COMB (@lem7111236 A s) (@lem7111235 A x s f b)). Qed.
Lemma lem7111238 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term282 A s f b) = (term283 A s f b).
Proof. exact (fun_ext (fun x : A => @lem7111237 A x s f b)). Qed.
Lemma lem7111239 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7111240 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term273 A s f b) = (term284 A s f b).
Proof. exact (MK_COMB (@lem7111239 A) (@lem7111238 A s f b)). Qed.
Lemma lem7111241 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : ((term272 A s f b) = (term273 A s f b)) = ((term269 A s f b) = (term284 A s f b)).
Proof. exact (MK_COMB (@lem7111234 A s f b) (@lem7111240 A s f b)). Qed.
Lemma lem7111242 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term269 A s f b) = (term284 A s f b).
Proof. exact (EQ_MP (@lem7111241 A s f b) (@lem7111226 A s f b)). Qed.
Lemma lem7111243 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term244 A s f b) = (term284 A s f b).
Proof. exact (TRANS (@lem7111222 A s f b) (@lem7111242 A s f b)). Qed.
Lemma lem7111244 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7111245 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term251 A s f b) = (term285 A s f b).
Proof. exact (MK_COMB (@lem7111244) (@lem7111243 A s f b)). Qed.
Lemma lem7111246 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term249 A s f b) = (term249 A s f b).
Proof. exact (eq_refl (term249 A s f b)). Qed.
Lemma lem7111247 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term253 A s f b) = (term286 A s f b).
Proof. exact (MK_COMB (@lem7111245 A s f b) (@lem7111246 A s f b)). Qed.
Lemma lem7111249 {A : Type'} (P : A -> Prop) (Q : Prop) : (term169 A P Q) = (term170 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7111250 {A : Type'} (P : A -> Prop) (Q : Prop) : (term169 A P Q) = (term170 A P Q).
Proof. exact (@lem7111249 A P Q). Qed.
Lemma lem7111251 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term287 A s f b) = (term288 A s f b).
Proof. exact (@lem7111250 A (term283 A s f b) (term249 A s f b)). Qed.
Lemma lem7111252 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term289 A s f b x) = (term281 A x s f b).
Proof. exact (eq_refl (term289 A s f b x)). Qed.
Lemma lem7111253 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term290 A s f b) = (term283 A s f b).
Proof. exact (fun_ext (fun x : A => @lem7111252 A x s f b)). Qed.
Lemma lem7111254 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7111255 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term291 A s f b) = (term284 A s f b).
Proof. exact (MK_COMB (@lem7111254 A) (@lem7111253 A s f b)). Qed.
Lemma lem7111256 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7111257 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term292 A s f b) = (term285 A s f b).
Proof. exact (MK_COMB (@lem7111256) (@lem7111255 A s f b)). Qed.
Lemma lem7111258 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term249 A s f b) = (term249 A s f b).
Proof. exact (eq_refl (term249 A s f b)). Qed.
Lemma lem7111259 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term287 A s f b) = (term286 A s f b).
Proof. exact (MK_COMB (@lem7111257 A s f b) (@lem7111258 A s f b)). Qed.
Lemma lem7111260 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7111261 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term293 A s f b) = (term294 A s f b).
Proof. exact (MK_COMB (@lem7111260) (@lem7111259 A s f b)). Qed.
Lemma lem7111262 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term289 A s f b x) = (term281 A x s f b).
Proof. exact (eq_refl (term289 A s f b x)). Qed.
Lemma lem7111263 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7111264 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term295 A s f b x) = (term296 A x s f b).
Proof. exact (MK_COMB (@lem7111263) (@lem7111262 A x s f b)). Qed.
Lemma lem7111265 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term249 A s f b) = (term249 A s f b).
Proof. exact (eq_refl (term249 A s f b)). Qed.
Lemma lem7111266 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term297 A x s f b) = (term298 A x s f b).
Proof. exact (MK_COMB (@lem7111264 A x s f b) (@lem7111265 A s f b)). Qed.
Lemma lem7111267 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term299 A s f b) = (term300 A s f b).
Proof. exact (fun_ext (fun x : A => @lem7111266 A x s f b)). Qed.
Lemma lem7111268 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7111269 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term288 A s f b) = (term301 A s f b).
Proof. exact (MK_COMB (@lem7111268 A) (@lem7111267 A s f b)). Qed.
Lemma lem7111270 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : ((term287 A s f b) = (term288 A s f b)) = ((term286 A s f b) = (term301 A s f b)).
Proof. exact (MK_COMB (@lem7111261 A s f b) (@lem7111269 A s f b)). Qed.
Lemma lem7111271 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term286 A s f b) = (term301 A s f b).
Proof. exact (EQ_MP (@lem7111270 A s f b) (@lem7111251 A s f b)). Qed.
Lemma lem7111272 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term253 A s f b) = (term301 A s f b).
Proof. exact (TRANS (@lem7111247 A s f b) (@lem7111271 A s f b)). Qed.
Lemma lem7111273 {A : Type'} (f : A -> real) (b : real) : (term254 A f b) = (term302 A f b).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7111272 A s f b)). Qed.
Lemma lem7111274 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7111275 {A : Type'} (f : A -> real) (b : real) : (term255 A f b) = (term303 A f b).
Proof. exact (MK_COMB (@lem7111274 A) (@lem7111273 A f b)). Qed.
Lemma lem7111277 {A B : Type'} (P : type1413 A B) : (term188 A B P) = (term189 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7111278 {A : Type'} (P : type672 A) : (term190 A P) = (term191 A P).
Proof. exact (@lem7111277 (A -> Prop) A P). Qed.
Lemma lem7111279 {A : Type'} (f : A -> real) (b : real) : (term304 A f b) = (term305 A f b).
Proof. exact (@lem7111278 A (term306 A f b)). Qed.
Lemma lem7111280 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term307 A f b s) = (term300 A s f b).
Proof. exact (eq_refl (term307 A f b s)). Qed.
Lemma lem7111281 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7111282 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) (x : A) : (term308 A f b s x) = (term309 A s f b x).
Proof. exact (MK_COMB (@lem7111280 A s f b) (@lem7111281 A x)). Qed.
Lemma lem7111283 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term309 A s f b x) = (term298 A x s f b).
Proof. exact (eq_refl (term309 A s f b x)). Qed.
Lemma lem7111284 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (b : real) : (term308 A f b s x) = (term298 A x s f b).
Proof. exact (TRANS (@lem7111282 A s f b x) (@lem7111283 A x s f b)). Qed.
Lemma lem7111285 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term310 A f b s) = (term300 A s f b).
Proof. exact (fun_ext (fun x : A => @lem7111284 A x s f b)). Qed.
Lemma lem7111286 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7111287 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term311 A f b s) = (term301 A s f b).
Proof. exact (MK_COMB (@lem7111286 A) (@lem7111285 A s f b)). Qed.
Lemma lem7111288 {A : Type'} (f : A -> real) (b : real) : (term312 A f b) = (term302 A f b).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7111287 A s f b)). Qed.
Lemma lem7111289 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7111290 {A : Type'} (f : A -> real) (b : real) : (term304 A f b) = (term303 A f b).
Proof. exact (MK_COMB (@lem7111289 A) (@lem7111288 A f b)). Qed.
Lemma lem7111291 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7111292 {A : Type'} (f : A -> real) (b : real) : (term313 A f b) = (term314 A f b).
Proof. exact (MK_COMB (@lem7111291) (@lem7111290 A f b)). Qed.
Lemma lem7111293 {A : Type'} (s : A -> Prop) (f : A -> real) (b : real) : (term307 A f b s) = (term300 A s f b).
Proof. exact (eq_refl (term307 A f b s)). Qed.
Lemma lem7111294 {A : Type'} (x : type684 A) (s : A -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem7111295 {A : Type'} (f : A -> real) (b : real) (x : type684 A) (s : A -> Prop) : (term315 A f b x s) = (term316 A f b x s).
Proof. exact (MK_COMB (@lem7111293 A s f b) (@lem7111294 A x s)). Qed.
Lemma lem7111296 {A : Type'} (x : type684 A) (s : A -> Prop) (f : A -> real) (b : real) : (term316 A f b x s) = (term317 A x s f b).
Proof. exact (eq_refl (term316 A f b x s)). Qed.
Lemma lem7111297 {A : Type'} (x : type684 A) (s : A -> Prop) (f : A -> real) (b : real) : (term315 A f b x s) = (term317 A x s f b).
Proof. exact (TRANS (@lem7111295 A f b x s) (@lem7111296 A x s f b)). Qed.
Lemma lem7111298 {A : Type'} (x : type684 A) (f : A -> real) (b : real) : (term318 A f b x) = (term319 A x f b).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7111297 A x s f b)). Qed.
Lemma lem7111299 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7111300 {A : Type'} (x : type684 A) (f : A -> real) (b : real) : (term320 A f b x) = (term321 A x f b).
Proof. exact (MK_COMB (@lem7111299 A) (@lem7111298 A x f b)). Qed.
Lemma lem7111301 {A : Type'} (f : A -> real) (b : real) : (term322 A f b) = (term323 A f b).
Proof. exact (fun_ext (fun x : type684 A => @lem7111300 A x f b)). Qed.
Lemma lem7111302 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem7111303 {A : Type'} (f : A -> real) (b : real) : (term305 A f b) = (term324 A f b).
Proof. exact (MK_COMB (@lem7111302 A) (@lem7111301 A f b)). Qed.
Lemma lem7111304 {A : Type'} (f : A -> real) (b : real) : ((term304 A f b) = (term305 A f b)) = ((term303 A f b) = (term324 A f b)).
Proof. exact (MK_COMB (@lem7111292 A f b) (@lem7111303 A f b)). Qed.
Lemma lem7111305 {A : Type'} (f : A -> real) (b : real) : (term303 A f b) = (term324 A f b).
Proof. exact (EQ_MP (@lem7111304 A f b) (@lem7111279 A f b)). Qed.
Lemma lem7111306 {A : Type'} (f : A -> real) (b : real) : (term255 A f b) = (term324 A f b).
Proof. exact (TRANS (@lem7111275 A f b) (@lem7111305 A f b)). Qed.
Lemma lem7111307 {A : Type'} (f : A -> real) : (term256 A f) = (term325 A f).
Proof. exact (fun_ext (fun b : real => @lem7111306 A f b)). Qed.
Lemma lem7111308 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7111309 {A : Type'} (f : A -> real) : (term257 A f) = (term326 A f).
Proof. exact (MK_COMB (@lem7111308) (@lem7111307 A f)). Qed.
Lemma lem7111311 {A B : Type'} (P : type1413 A B) : (term188 A B P) = (term189 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7111312 {A : Type'} (P : type1615 A) : (term327 A P) = (term328 A P).
Proof. exact (@lem7111311 real (type684 A) P). Qed.
Lemma lem7111313 {A : Type'} (f : A -> real) : (term329 A f) = (term330 A f).
Proof. exact (@lem7111312 A (term331 A f)). Qed.
Lemma lem7111314 {A : Type'} (f : A -> real) (b : real) : (term332 A f b) = (term323 A f b).
Proof. exact (eq_refl (term332 A f b)). Qed.
Lemma lem7111315 {A : Type'} (x : type684 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7111316 {A : Type'} (f : A -> real) (b : real) (x : type684 A) : (term333 A f b x) = (term334 A f b x).
Proof. exact (MK_COMB (@lem7111314 A f b) (@lem7111315 A x)). Qed.
Lemma lem7111317 {A : Type'} (x : type684 A) (f : A -> real) (b : real) : (term334 A f b x) = (term321 A x f b).
Proof. exact (eq_refl (term334 A f b x)). Qed.
Lemma lem7111318 {A : Type'} (x : type684 A) (f : A -> real) (b : real) : (term333 A f b x) = (term321 A x f b).
Proof. exact (TRANS (@lem7111316 A f b x) (@lem7111317 A x f b)). Qed.
Lemma lem7111319 {A : Type'} (f : A -> real) (b : real) : (term335 A f b) = (term323 A f b).
Proof. exact (fun_ext (fun x : type684 A => @lem7111318 A x f b)). Qed.
Lemma lem7111320 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem7111321 {A : Type'} (f : A -> real) (b : real) : (term336 A f b) = (term324 A f b).
Proof. exact (MK_COMB (@lem7111320 A) (@lem7111319 A f b)). Qed.
Lemma lem7111322 {A : Type'} (f : A -> real) : (term337 A f) = (term325 A f).
Proof. exact (fun_ext (fun b : real => @lem7111321 A f b)). Qed.
Lemma lem7111323 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7111324 {A : Type'} (f : A -> real) : (term329 A f) = (term326 A f).
Proof. exact (MK_COMB (@lem7111323) (@lem7111322 A f)). Qed.
Lemma lem7111325 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7111326 {A : Type'} (f : A -> real) : (term338 A f) = (term339 A f).
Proof. exact (MK_COMB (@lem7111325) (@lem7111324 A f)). Qed.
Lemma lem7111327 {A : Type'} (f : A -> real) (b : real) : (term332 A f b) = (term323 A f b).
Proof. exact (eq_refl (term332 A f b)). Qed.
Lemma lem7111328 {A : Type'} (x : type1616 A) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem7111329 {A : Type'} (f : A -> real) (x : type1616 A) (b : real) : (term340 A f x b) = (term341 A f x b).
Proof. exact (MK_COMB (@lem7111327 A f b) (@lem7111328 A x b)). Qed.
Lemma lem7111330 {A : Type'} (x : type1616 A) (f : A -> real) (b : real) : (term341 A f x b) = (term342 A x f b).
Proof. exact (eq_refl (term341 A f x b)). Qed.
Lemma lem7111331 {A : Type'} (x : type1616 A) (f : A -> real) (b : real) : (term340 A f x b) = (term342 A x f b).
Proof. exact (TRANS (@lem7111329 A f x b) (@lem7111330 A x f b)). Qed.
Lemma lem7111332 {A : Type'} (x : type1616 A) (f : A -> real) : (term343 A f x) = (term344 A x f).
Proof. exact (fun_ext (fun b : real => @lem7111331 A x f b)). Qed.
Lemma lem7111333 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7111334 {A : Type'} (x : type1616 A) (f : A -> real) : (term345 A f x) = (term346 A x f).
Proof. exact (MK_COMB (@lem7111333) (@lem7111332 A x f)). Qed.
Lemma lem7111335 {A : Type'} (f : A -> real) : (term347 A f) = (term348 A f).
Proof. exact (fun_ext (fun x : type1616 A => @lem7111334 A x f)). Qed.
Lemma lem7111336 {A : Type'} : (@ex (real -> (A -> Prop) -> A)) = (@ex (real -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex (real -> (A -> Prop) -> A))). Qed.
Lemma lem7111337 {A : Type'} (f : A -> real) : (term330 A f) = (term349 A f).
Proof. exact (MK_COMB (@lem7111336 A) (@lem7111335 A f)). Qed.
Lemma lem7111338 {A : Type'} (f : A -> real) : ((term329 A f) = (term330 A f)) = ((term326 A f) = (term349 A f)).
Proof. exact (MK_COMB (@lem7111326 A f) (@lem7111337 A f)). Qed.
Lemma lem7111339 {A : Type'} (f : A -> real) : (term326 A f) = (term349 A f).
Proof. exact (EQ_MP (@lem7111338 A f) (@lem7111313 A f)). Qed.
Lemma lem7111340 {A : Type'} (f : A -> real) : (term257 A f) = (term349 A f).
Proof. exact (TRANS (@lem7111309 A f) (@lem7111339 A f)). Qed.
Lemma lem7111341 {A : Type'} : (term258 A) = (term350 A).
Proof. exact (fun_ext (fun f : A -> real => @lem7111340 A f)). Qed.
Lemma lem7111342 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7111343 {A : Type'} : (term259 A) = (term351 A).
Proof. exact (MK_COMB (@lem7111342 A) (@lem7111341 A)). Qed.
Lemma lem7111345 {A B : Type'} (P : type1413 A B) : (term188 A B P) = (term189 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7111346 {A : Type'} (P : type712 A) : (term352 A P) = (term353 A P).
Proof. exact (@lem7111345 (A -> real) (type1616 A) P). Qed.
Lemma lem7111347 {A : Type'} : (term354 A) = (term355 A).
Proof. exact (@lem7111346 A (term356 A)). Qed.
Lemma lem7111348 {A : Type'} (f : A -> real) : (term357 A f) = (term348 A f).
Proof. exact (eq_refl (term357 A f)). Qed.
Lemma lem7111349 {A : Type'} (x : type1616 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7111350 {A : Type'} (f : A -> real) (x : type1616 A) : (term358 A f x) = (term359 A f x).
Proof. exact (MK_COMB (@lem7111348 A f) (@lem7111349 A x)). Qed.
Lemma lem7111351 {A : Type'} (x : type1616 A) (f : A -> real) : (term359 A f x) = (term346 A x f).
Proof. exact (eq_refl (term359 A f x)). Qed.
Lemma lem7111352 {A : Type'} (x : type1616 A) (f : A -> real) : (term358 A f x) = (term346 A x f).
Proof. exact (TRANS (@lem7111350 A f x) (@lem7111351 A x f)). Qed.
Lemma lem7111353 {A : Type'} (f : A -> real) : (term360 A f) = (term348 A f).
Proof. exact (fun_ext (fun x : type1616 A => @lem7111352 A x f)). Qed.
Lemma lem7111354 {A : Type'} : (@ex (real -> (A -> Prop) -> A)) = (@ex (real -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex (real -> (A -> Prop) -> A))). Qed.
Lemma lem7111355 {A : Type'} (f : A -> real) : (term361 A f) = (term349 A f).
Proof. exact (MK_COMB (@lem7111354 A) (@lem7111353 A f)). Qed.
Lemma lem7111356 {A : Type'} : (term362 A) = (term350 A).
Proof. exact (fun_ext (fun f : A -> real => @lem7111355 A f)). Qed.
Lemma lem7111357 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7111358 {A : Type'} : (term354 A) = (term351 A).
Proof. exact (MK_COMB (@lem7111357 A) (@lem7111356 A)). Qed.
Lemma lem7111359 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7111360 {A : Type'} : (term363 A) = (term364 A).
Proof. exact (MK_COMB (@lem7111359) (@lem7111358 A)). Qed.
Lemma lem7111361 {A : Type'} (f : A -> real) : (term357 A f) = (term348 A f).
Proof. exact (eq_refl (term357 A f)). Qed.
Lemma lem7111362 {A : Type'} (x : type714 A) (f : A -> real) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem7111363 {A : Type'} (x : type714 A) (f : A -> real) : (term365 A x f) = (term366 A x f).
Proof. exact (MK_COMB (@lem7111361 A f) (@lem7111362 A x f)). Qed.
Lemma lem7111364 {A : Type'} (x : type714 A) (f : A -> real) : (term366 A x f) = (term367 A x f).
Proof. exact (eq_refl (term366 A x f)). Qed.
Lemma lem7111365 {A : Type'} (x : type714 A) (f : A -> real) : (term365 A x f) = (term367 A x f).
Proof. exact (TRANS (@lem7111363 A x f) (@lem7111364 A x f)). Qed.
Lemma lem7111366 {A : Type'} (x : type714 A) : (term368 A x) = (term369 A x).
Proof. exact (fun_ext (fun f : A -> real => @lem7111365 A x f)). Qed.
Lemma lem7111367 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7111368 {A : Type'} (x : type714 A) : (term370 A x) = (term371 A x).
Proof. exact (MK_COMB (@lem7111367 A) (@lem7111366 A x)). Qed.
Lemma lem7111369 {A : Type'} : (term372 A) = (term373 A).
Proof. exact (fun_ext (fun x : type714 A => @lem7111368 A x)). Qed.
Lemma lem7111370 {A : Type'} : (@ex ((A -> real) -> real -> (A -> Prop) -> A)) = (@ex ((A -> real) -> real -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> real) -> real -> (A -> Prop) -> A))). Qed.
Lemma lem7111371 {A : Type'} : (term355 A) = (term374 A).
Proof. exact (MK_COMB (@lem7111370 A) (@lem7111369 A)). Qed.
Lemma lem7111372 {A : Type'} : ((term354 A) = (term355 A)) = ((term351 A) = (term374 A)).
Proof. exact (MK_COMB (@lem7111360 A) (@lem7111371 A)). Qed.
Lemma lem7111373 {A : Type'} : (term351 A) = (term374 A).
Proof. exact (EQ_MP (@lem7111372 A) (@lem7111347 A)). Qed.
Lemma lem7111375 {A : Type'} : (term259 A) = (term374 A).
Proof. exact (TRANS (@lem7111343 A) (@lem7111373 A)). Qed.
Lemma lem7111376 {A : Type'} : (term50 A) = (term374 A).
Proof. exact (TRANS (@lem7111043 A) (@lem7111375 A)). Qed.
Lemma lem7111377 {A : Type'} (h1 : term50 A) : term374 A.
Proof. exact (EQ_MP (@lem7111376 A) (@lem7109905 A h1)). Qed.
Lemma lem7111379 {_132718 : Type'} (x' : type714 _132718) (h1 : term371 _132718 x') : term371 _132718 x'.
Proof. exact (h1). Qed.
Lemma lem7111382 {_132718 : Type'} (f : _132718 -> real) (h1 : term149 _132718 f) : term149 _132718 f.
Proof. exact (h1). Qed.
Lemma lem7111383 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (h1 : term147 _132718 s f) : term147 _132718 s f.
Proof. exact (h1). Qed.
Lemma lem7111384 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term144 _132718 s f x'''') : term144 _132718 s f x''''.
Proof. exact (h1). Qed.
Lemma lem7111607 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7111612 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7111614 {_132718 : Type'} (f : _132718 -> real) (x : _132718) : (f x) = (@I (_132718 -> real) f x).
Proof. exact (@lem7111612 _132718 real f x). Qed.
Lemma lem7111615 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7111616 {_132718 : Type'} (f : _132718 -> real) (x : _132718) : (term375 _132718 f x) = (term376 _132718 f x).
Proof. exact (MK_COMB (@lem7111607) (@lem7111614 _132718 f x)). Qed.
Lemma lem7111617 {_132718 : Type'} (f : _132718 -> real) (x : _132718) (b : real) : (term247 _132718 f x b) = (term377 _132718 f x b).
Proof. exact (MK_COMB (@lem7111616 _132718 f x) (@lem7111615 b)). Qed.
Lemma lem7111619 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7111620 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7111619 real (real -> Prop) f x). Qed.
Lemma lem7111621 {_132718 : Type'} (f : _132718 -> real) (x : _132718) : (term376 _132718 f x) = (term378 _132718 f x).
Proof. exact (@lem7111620 real_le (@I (_132718 -> real) f x)). Qed.
Lemma lem7111622 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7111623 {_132718 : Type'} (f : _132718 -> real) (x : _132718) (b : real) : (term377 _132718 f x b) = (term379 _132718 f x b).
Proof. exact (MK_COMB (@lem7111621 _132718 f x) (@lem7111622 b)). Qed.
Lemma lem7111625 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7111626 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7111625 real Prop f x). Qed.
Lemma lem7111627 {_132718 : Type'} (f : _132718 -> real) (x : _132718) (b : real) : (term379 _132718 f x b) = (term380 _132718 f x b).
Proof. exact (@lem7111626 (term378 _132718 f x) b). Qed.
Lemma lem7111628 {_132718 : Type'} (f : _132718 -> real) (x : _132718) (b : real) : (term377 _132718 f x b) = (term380 _132718 f x b).
Proof. exact (TRANS (@lem7111623 _132718 f x b) (@lem7111627 _132718 f x b)). Qed.
Lemma lem7111629 {_132718 : Type'} (f : _132718 -> real) (x : _132718) (b : real) : (term247 _132718 f x b) = (term380 _132718 f x b).
Proof. exact (TRANS (@lem7111617 _132718 f x b) (@lem7111628 _132718 f x b)). Qed.
Lemma lem7111630 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7111637 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7111638 {_132718 : Type'} (f : type1364 _132718) (x : _132718) : (f x) = (@I (_132718 -> (_132718 -> Prop) -> Prop) f x).
Proof. exact (@lem7111637 _132718 (type686 _132718) f x). Qed.
Lemma lem7111639 {_132718 : Type'} (x : _132718) : (@IN _132718 x) = (@I (_132718 -> (_132718 -> Prop) -> Prop) (@IN _132718) x).
Proof. exact (@lem7111638 _132718 (@IN _132718) x). Qed.
Lemma lem7111640 {_132718 : Type'} (s : _132718 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7111641 {_132718 : Type'} (x : _132718) (s : _132718 -> Prop) : (@IN _132718 x s) = (@I (_132718 -> (_132718 -> Prop) -> Prop) (@IN _132718) x s).
Proof. exact (MK_COMB (@lem7111639 _132718 x) (@lem7111640 _132718 s)). Qed.
Lemma lem7111643 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7111644 {_132718 : Type'} (f : type686 _132718) (x : _132718 -> Prop) : (f x) = (@I ((_132718 -> Prop) -> Prop) f x).
Proof. exact (@lem7111643 (_132718 -> Prop) Prop f x). Qed.
Lemma lem7111645 {_132718 : Type'} (x : _132718) (s : _132718 -> Prop) : (@I (_132718 -> (_132718 -> Prop) -> Prop) (@IN _132718) x s) = (term381 _132718 x s).
Proof. exact (@lem7111644 _132718 (@I (_132718 -> (_132718 -> Prop) -> Prop) (@IN _132718) x) s). Qed.
Lemma lem7111647 {_132718 : Type'} (x : _132718) (s : _132718 -> Prop) : (@IN _132718 x s) = (term381 _132718 x s).
Proof. exact (TRANS (@lem7111641 _132718 x s) (@lem7111645 _132718 x s)). Qed.
Lemma lem7111648 {_132718 : Type'} (x : _132718) (s : _132718 -> Prop) : (term382 _132718 x s) = (term383 _132718 x s).
Proof. exact (MK_COMB (@lem7111630) (@lem7111647 _132718 x s)). Qed.
Lemma lem7111649 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7111650 {_132718 : Type'} (x : _132718) (s : _132718 -> Prop) : (term384 _132718 x s) = (term385 _132718 x s).
Proof. exact (MK_COMB (@lem7111649) (@lem7111648 _132718 x s)). Qed.
Lemma lem7111651 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) (b : real) : (term246 _132718 s f x b) = (term386 _132718 s f x b).
Proof. exact (MK_COMB (@lem7111650 _132718 x s) (@lem7111629 _132718 f x b)). Qed.
Lemma lem7111652 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term248 _132718 s f b) = (term387 _132718 s f b).
Proof. exact (fun_ext (fun x : _132718 => @lem7111651 _132718 s f x b)). Qed.
Lemma lem7111653 {_132718 : Type'} : (@all _132718) = (@all _132718).
Proof. exact (eq_refl (@all _132718)). Qed.
Lemma lem7111654 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term249 _132718 s f b) = (term388 _132718 s f b).
Proof. exact (MK_COMB (@lem7111653 _132718) (@lem7111652 _132718 s f b)). Qed.
Lemma lem7111655 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7111656 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7111663 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7111664 {_132718 : Type'} (f : type646 _132718) (x : _132718 -> Prop) : (f x) = (@I ((_132718 -> Prop) -> (_132718 -> real) -> real) f x).
Proof. exact (@lem7111663 (_132718 -> Prop) (type717 _132718) f x). Qed.
Lemma lem7111665 {_132718 : Type'} (s : _132718 -> Prop) : (@sum _132718 s) = (@I ((_132718 -> Prop) -> (_132718 -> real) -> real) (@sum _132718) s).
Proof. exact (@lem7111664 _132718 (@sum _132718) s). Qed.
Lemma lem7111666 {_132718 : Type'} (f : _132718 -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7111667 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (@sum _132718 s f) = (@I ((_132718 -> Prop) -> (_132718 -> real) -> real) (@sum _132718) s f).
Proof. exact (MK_COMB (@lem7111665 _132718 s) (@lem7111666 _132718 f)). Qed.
Lemma lem7111669 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7111670 {_132718 : Type'} (f : type717 _132718) (x : _132718 -> real) : (f x) = (@I ((_132718 -> real) -> real) f x).
Proof. exact (@lem7111669 (_132718 -> real) real f x). Qed.
Lemma lem7111671 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (@I ((_132718 -> Prop) -> (_132718 -> real) -> real) (@sum _132718) s f) = (term389 _132718 s f).
Proof. exact (@lem7111670 _132718 (@I ((_132718 -> Prop) -> (_132718 -> real) -> real) (@sum _132718) s) f). Qed.
Lemma lem7111673 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (@sum _132718 s f) = (term389 _132718 s f).
Proof. exact (TRANS (@lem7111667 _132718 s f) (@lem7111671 _132718 s f)). Qed.
Lemma lem7111674 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7111675 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term390 _132718 s f) = (term391 _132718 s f).
Proof. exact (MK_COMB (@lem7111656) (@lem7111673 _132718 s f)). Qed.
Lemma lem7111676 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term70 _132718 s f b) = (term392 _132718 s f b).
Proof. exact (MK_COMB (@lem7111675 _132718 s f) (@lem7111674 b)). Qed.
Lemma lem7111678 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7111679 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7111678 real (real -> Prop) f x). Qed.
Lemma lem7111680 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term391 _132718 s f) = (term393 _132718 s f).
Proof. exact (@lem7111679 real_le (term389 _132718 s f)). Qed.
Lemma lem7111681 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7111682 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term392 _132718 s f b) = (term394 _132718 s f b).
Proof. exact (MK_COMB (@lem7111680 _132718 s f) (@lem7111681 b)). Qed.
Lemma lem7111684 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7111685 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7111684 real Prop f x). Qed.
Lemma lem7111686 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term394 _132718 s f b) = (term395 _132718 s f b).
Proof. exact (@lem7111685 (term393 _132718 s f) b). Qed.
Lemma lem7111687 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term392 _132718 s f b) = (term395 _132718 s f b).
Proof. exact (TRANS (@lem7111682 _132718 s f b) (@lem7111686 _132718 s f b)). Qed.
Lemma lem7111688 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term70 _132718 s f b) = (term395 _132718 s f b).
Proof. exact (TRANS (@lem7111676 _132718 s f b) (@lem7111687 _132718 s f b)). Qed.
Lemma lem7111689 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term238 _132718 s f b) = (term396 _132718 s f b).
Proof. exact (MK_COMB (@lem7111655) (@lem7111688 _132718 s f b)). Qed.
Lemma lem7111690 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7111691 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7111692 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7111697 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7111698 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7111697 nat nat f x). Qed.
Lemma lem7111700 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem7111698 NUMERAL 0). Qed.
Lemma lem7111701 : term19 = term397.
Proof. exact (MK_COMB (@lem7111692) (@lem7111700)). Qed.
Lemma lem7111703 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7111704 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem7111703 nat real f x). Qed.
Lemma lem7111705 : term397 = term398.
Proof. exact (@lem7111704 real_of_num (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem7111706 : term19 = term398.
Proof. exact (TRANS (@lem7111701) (@lem7111705)). Qed.
Lemma lem7111707 {_132718 : Type'} (f : _132718 -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7111716 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7111717 {_132718 : Type'} (f : type714 _132718) (x : _132718 -> real) : (f x) = (@I ((_132718 -> real) -> real -> (_132718 -> Prop) -> _132718) f x).
Proof. exact (@lem7111716 (_132718 -> real) (type1616 _132718) f x). Qed.
Lemma lem7111718 {_132718 : Type'} (x' : type714 _132718) (f : _132718 -> real) : (x' f) = (@I ((_132718 -> real) -> real -> (_132718 -> Prop) -> _132718) x' f).
Proof. exact (@lem7111717 _132718 x' f). Qed.
Lemma lem7111719 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7111720 {_132718 : Type'} (x' : type714 _132718) (f : _132718 -> real) (b : real) : (x' f b) = (@I ((_132718 -> real) -> real -> (_132718 -> Prop) -> _132718) x' f b).
Proof. exact (MK_COMB (@lem7111718 _132718 x' f) (@lem7111719 b)). Qed.
Lemma lem7111722 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7111723 {_132718 : Type'} (f : type1616 _132718) (x : real) : (f x) = (@I (real -> (_132718 -> Prop) -> _132718) f x).
Proof. exact (@lem7111722 real (type684 _132718) f x). Qed.
Lemma lem7111724 {_132718 : Type'} (x' : type714 _132718) (f : _132718 -> real) (b : real) : (@I ((_132718 -> real) -> real -> (_132718 -> Prop) -> _132718) x' f b) = (term399 _132718 x' f b).
Proof. exact (@lem7111723 _132718 (@I ((_132718 -> real) -> real -> (_132718 -> Prop) -> _132718) x' f) b). Qed.
Lemma lem7111725 {_132718 : Type'} (x' : type714 _132718) (f : _132718 -> real) (b : real) : (x' f b) = (term399 _132718 x' f b).
Proof. exact (TRANS (@lem7111720 _132718 x' f b) (@lem7111724 _132718 x' f b)). Qed.
Lemma lem7111726 {_132718 : Type'} (s : _132718 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7111727 {_132718 : Type'} (x' : type714 _132718) (f : _132718 -> real) (b : real) (s : _132718 -> Prop) : (x' f b s) = (term400 _132718 x' f b s).
Proof. exact (MK_COMB (@lem7111725 _132718 x' f b) (@lem7111726 _132718 s)). Qed.
Lemma lem7111729 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7111730 {_132718 : Type'} (f : type684 _132718) (x : _132718 -> Prop) : (f x) = (@I ((_132718 -> Prop) -> _132718) f x).
Proof. exact (@lem7111729 (_132718 -> Prop) _132718 f x). Qed.
Lemma lem7111731 {_132718 : Type'} (x' : type714 _132718) (f : _132718 -> real) (b : real) (s : _132718 -> Prop) : (term400 _132718 x' f b s) = (term401 _132718 x' f b s).
Proof. exact (@lem7111730 _132718 (term399 _132718 x' f b) s). Qed.
Lemma lem7111733 {_132718 : Type'} (x' : type714 _132718) (f : _132718 -> real) (b : real) (s : _132718 -> Prop) : (x' f b s) = (term401 _132718 x' f b s).
Proof. exact (TRANS (@lem7111727 _132718 x' f b s) (@lem7111731 _132718 x' f b s)). Qed.
Lemma lem7111734 {_132718 : Type'} (x' : type714 _132718) (f : _132718 -> real) (b : real) (s : _132718 -> Prop) : (term402 _132718 x' f b s) = (term403 _132718 x' f b s).
Proof. exact (MK_COMB (@lem7111707 _132718 f) (@lem7111733 _132718 x' f b s)). Qed.
Lemma lem7111736 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7111737 {_132718 : Type'} (f : _132718 -> real) (x : _132718) : (f x) = (@I (_132718 -> real) f x).
Proof. exact (@lem7111736 _132718 real f x). Qed.
Lemma lem7111738 {_132718 : Type'} (x' : type714 _132718) (f : _132718 -> real) (b : real) (s : _132718 -> Prop) : (term403 _132718 x' f b s) = (term404 _132718 x' f b s).
Proof. exact (@lem7111737 _132718 f (term401 _132718 x' f b s)). Qed.
Lemma lem7111739 {_132718 : Type'} (x' : type714 _132718) (f : _132718 -> real) (b : real) (s : _132718 -> Prop) : (term402 _132718 x' f b s) = (term404 _132718 x' f b s).
Proof. exact (TRANS (@lem7111734 _132718 x' f b s) (@lem7111738 _132718 x' f b s)). Qed.
Lemma lem7111740 : term405 = term406.
Proof. exact (MK_COMB (@lem7111691) (@lem7111706)). Qed.
Lemma lem7111741 {_132718 : Type'} (x' : type714 _132718) (f : _132718 -> real) (b : real) (s : _132718 -> Prop) : (term407 _132718 x' f b s) = (term408 _132718 x' f b s).
Proof. exact (MK_COMB (@lem7111740) (@lem7111739 _132718 x' f b s)). Qed.
Lemma lem7111743 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7111744 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7111743 real (real -> Prop) f x). Qed.
Lemma lem7111745 : term406 = term409.
Proof. exact (@lem7111744 real_le term398). Qed.
Lemma lem7111746 {_132718 : Type'} (x' : type714 _132718) (f : _132718 -> real) (b : real) (s : _132718 -> Prop) : (term404 _132718 x' f b s) = (term404 _132718 x' f b s).
Proof. exact (eq_refl (term404 _132718 x' f b s)). Qed.
Lemma lem7111747 {_132718 : Type'} (x' : type714 _132718) (f : _132718 -> real) (b : real) (s : _132718 -> Prop) : (term408 _132718 x' f b s) = (term410 _132718 x' f b s).
Proof. exact (MK_COMB (@lem7111745) (@lem7111746 _132718 x' f b s)). Qed.
Lemma lem7111749 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7111750 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7111749 real Prop f x). Qed.
Lemma lem7111751 {_132718 : Type'} (x' : type714 _132718) (f : _132718 -> real) (b : real) (s : _132718 -> Prop) : (term410 _132718 x' f b s) = (term411 _132718 x' f b s).
Proof. exact (@lem7111750 term409 (term404 _132718 x' f b s)). Qed.
Lemma lem7111752 {_132718 : Type'} (x' : type714 _132718) (f : _132718 -> real) (b : real) (s : _132718 -> Prop) : (term408 _132718 x' f b s) = (term411 _132718 x' f b s).
Proof. exact (TRANS (@lem7111747 _132718 x' f b s) (@lem7111751 _132718 x' f b s)). Qed.
Lemma lem7111753 {_132718 : Type'} (x' : type714 _132718) (f : _132718 -> real) (b : real) (s : _132718 -> Prop) : (term407 _132718 x' f b s) = (term411 _132718 x' f b s).
Proof. exact (TRANS (@lem7111741 _132718 x' f b s) (@lem7111752 _132718 x' f b s)). Qed.
Lemma lem7111754 {_132718 : Type'} (x' : type714 _132718) (f : _132718 -> real) (b : real) (s : _132718 -> Prop) : (term412 _132718 x' f b s) = (term413 _132718 x' f b s).
Proof. exact (MK_COMB (@lem7111690) (@lem7111753 _132718 x' f b s)). Qed.
Lemma lem7111755 {_132718 : Type'} : (@IN _132718) = (@IN _132718).
Proof. exact (eq_refl (@IN _132718)). Qed.
Lemma lem7111764 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7111765 {_132718 : Type'} (f : type714 _132718) (x : _132718 -> real) : (f x) = (@I ((_132718 -> real) -> real -> (_132718 -> Prop) -> _132718) f x).
Proof. exact (@lem7111764 (_132718 -> real) (type1616 _132718) f x). Qed.
Lemma lem7111766 {_132718 : Type'} (x' : type714 _132718) (f : _132718 -> real) : (x' f) = (@I ((_132718 -> real) -> real -> (_132718 -> Prop) -> _132718) x' f).
Proof. exact (@lem7111765 _132718 x' f). Qed.
Lemma lem7111767 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem7111768 {_132718 : Type'} (x' : type714 _132718) (f : _132718 -> real) (b : real) : (x' f b) = (@I ((_132718 -> real) -> real -> (_132718 -> Prop) -> _132718) x' f b).
Proof. exact (MK_COMB (@lem7111766 _132718 x' f) (@lem7111767 b)). Qed.
Lemma lem7111770 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7111771 {_132718 : Type'} (f : type1616 _132718) (x : real) : (f x) = (@I (real -> (_132718 -> Prop) -> _132718) f x).
Proof. exact (@lem7111770 real (type684 _132718) f x). Qed.
Lemma lem7111772 {_132718 : Type'} (x' : type714 _132718) (f : _132718 -> real) (b : real) : (@I ((_132718 -> real) -> real -> (_132718 -> Prop) -> _132718) x' f b) = (term399 _132718 x' f b).
Proof. exact (@lem7111771 _132718 (@I ((_132718 -> real) -> real -> (_132718 -> Prop) -> _132718) x' f) b). Qed.
Lemma lem7111773 {_132718 : Type'} (x' : type714 _132718) (f : _132718 -> real) (b : real) : (x' f b) = (term399 _132718 x' f b).
Proof. exact (TRANS (@lem7111768 _132718 x' f b) (@lem7111772 _132718 x' f b)). Qed.
Lemma lem7111774 {_132718 : Type'} (s : _132718 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7111775 {_132718 : Type'} (x' : type714 _132718) (f : _132718 -> real) (b : real) (s : _132718 -> Prop) : (x' f b s) = (term400 _132718 x' f b s).
Proof. exact (MK_COMB (@lem7111773 _132718 x' f b) (@lem7111774 _132718 s)). Qed.
Lemma lem7111777 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7111778 {_132718 : Type'} (f : type684 _132718) (x : _132718 -> Prop) : (f x) = (@I ((_132718 -> Prop) -> _132718) f x).
Proof. exact (@lem7111777 (_132718 -> Prop) _132718 f x). Qed.
Lemma lem7111779 {_132718 : Type'} (x' : type714 _132718) (f : _132718 -> real) (b : real) (s : _132718 -> Prop) : (term400 _132718 x' f b s) = (term401 _132718 x' f b s).
Proof. exact (@lem7111778 _132718 (term399 _132718 x' f b) s). Qed.
Lemma lem7111781 {_132718 : Type'} (x' : type714 _132718) (f : _132718 -> real) (b : real) (s : _132718 -> Prop) : (x' f b s) = (term401 _132718 x' f b s).
Proof. exact (TRANS (@lem7111775 _132718 x' f b s) (@lem7111779 _132718 x' f b s)). Qed.
Lemma lem7111782 {_132718 : Type'} (s : _132718 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7111783 {_132718 : Type'} (x' : type714 _132718) (f : _132718 -> real) (b : real) (s : _132718 -> Prop) : (term414 _132718 x' f b s) = (term415 _132718 x' f b s).
Proof. exact (MK_COMB (@lem7111755 _132718) (@lem7111781 _132718 x' f b s)). Qed.
Lemma lem7111784 {_132718 : Type'} (x' : type714 _132718) (f : _132718 -> real) (b : real) (s : _132718 -> Prop) : (term416 _132718 x' f b s) = (term417 _132718 x' f b s).
Proof. exact (MK_COMB (@lem7111783 _132718 x' f b s) (@lem7111782 _132718 s)). Qed.
Lemma lem7111786 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7111787 {_132718 : Type'} (f : type1364 _132718) (x : _132718) : (f x) = (@I (_132718 -> (_132718 -> Prop) -> Prop) f x).
Proof. exact (@lem7111786 _132718 (type686 _132718) f x). Qed.
Lemma lem7111788 {_132718 : Type'} (x' : type714 _132718) (f : _132718 -> real) (b : real) (s : _132718 -> Prop) : (term415 _132718 x' f b s) = (term418 _132718 x' f b s).
Proof. exact (@lem7111787 _132718 (@IN _132718) (term401 _132718 x' f b s)). Qed.
Lemma lem7111789 {_132718 : Type'} (s : _132718 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7111790 {_132718 : Type'} (x' : type714 _132718) (f : _132718 -> real) (b : real) (s : _132718 -> Prop) : (term417 _132718 x' f b s) = (term419 _132718 x' f b s).
Proof. exact (MK_COMB (@lem7111788 _132718 x' f b s) (@lem7111789 _132718 s)). Qed.
Lemma lem7111792 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7111793 {_132718 : Type'} (f : type686 _132718) (x : _132718 -> Prop) : (f x) = (@I ((_132718 -> Prop) -> Prop) f x).
Proof. exact (@lem7111792 (_132718 -> Prop) Prop f x). Qed.
Lemma lem7111794 {_132718 : Type'} (x' : type714 _132718) (f : _132718 -> real) (b : real) (s : _132718 -> Prop) : (term419 _132718 x' f b s) = (term420 _132718 x' f b s).
Proof. exact (@lem7111793 _132718 (term418 _132718 x' f b s) s). Qed.
Lemma lem7111795 {_132718 : Type'} (x' : type714 _132718) (f : _132718 -> real) (b : real) (s : _132718 -> Prop) : (term417 _132718 x' f b s) = (term420 _132718 x' f b s).
Proof. exact (TRANS (@lem7111790 _132718 x' f b s) (@lem7111794 _132718 x' f b s)). Qed.
Lemma lem7111796 {_132718 : Type'} (x' : type714 _132718) (f : _132718 -> real) (b : real) (s : _132718 -> Prop) : (term416 _132718 x' f b s) = (term420 _132718 x' f b s).
Proof. exact (TRANS (@lem7111784 _132718 x' f b s) (@lem7111795 _132718 x' f b s)). Qed.
Lemma lem7111797 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7111798 {_132718 : Type'} (x' : type714 _132718) (f : _132718 -> real) (b : real) (s : _132718 -> Prop) : (term421 _132718 x' f b s) = (term422 _132718 x' f b s).
Proof. exact (MK_COMB (@lem7111797) (@lem7111796 _132718 x' f b s)). Qed.
Lemma lem7111799 {_132718 : Type'} (x' : type714 _132718) (f : _132718 -> real) (b : real) (s : _132718 -> Prop) : (term423 _132718 x' f b s) = (term424 _132718 x' f b s).
Proof. exact (MK_COMB (@lem7111798 _132718 x' f b s) (@lem7111754 _132718 x' f b s)). Qed.
Lemma lem7111800 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7111801 {_132718 : Type'} (x' : type714 _132718) (f : _132718 -> real) (b : real) (s : _132718 -> Prop) : (term425 _132718 x' f b s) = (term426 _132718 x' f b s).
Proof. exact (MK_COMB (@lem7111800) (@lem7111799 _132718 x' f b s)). Qed.
Lemma lem7111802 {_132718 : Type'} (x' : type714 _132718) (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term427 _132718 x' s f b) = (term428 _132718 x' s f b).
Proof. exact (MK_COMB (@lem7111801 _132718 x' f b s) (@lem7111689 _132718 s f b)). Qed.
Lemma lem7111803 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7111808 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7111809 {_132718 : Type'} (f : type686 _132718) (x : _132718 -> Prop) : (f x) = (@I ((_132718 -> Prop) -> Prop) f x).
Proof. exact (@lem7111808 (_132718 -> Prop) Prop f x). Qed.
Lemma lem7111811 {_132718 : Type'} (s : _132718 -> Prop) : (@FINITE _132718 s) = (@I ((_132718 -> Prop) -> Prop) (@FINITE _132718) s).
Proof. exact (@lem7111809 _132718 (@FINITE _132718) s). Qed.
Lemma lem7111812 {_132718 : Type'} (s : _132718 -> Prop) : (term274 _132718 s) = (term429 _132718 s).
Proof. exact (MK_COMB (@lem7111803) (@lem7111811 _132718 s)). Qed.
Lemma lem7111813 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7111814 {_132718 : Type'} (s : _132718 -> Prop) : (term242 _132718 s) = (term430 _132718 s).
Proof. exact (MK_COMB (@lem7111813) (@lem7111812 _132718 s)). Qed.
Lemma lem7111815 {_132718 : Type'} (x' : type714 _132718) (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term431 _132718 x' s f b) = (term432 _132718 x' s f b).
Proof. exact (MK_COMB (@lem7111814 _132718 s) (@lem7111802 _132718 x' s f b)). Qed.
Lemma lem7111816 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7111817 {_132718 : Type'} (x' : type714 _132718) (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term433 _132718 x' s f b) = (term434 _132718 x' s f b).
Proof. exact (MK_COMB (@lem7111816) (@lem7111815 _132718 x' s f b)). Qed.
Lemma lem7111818 {_132718 : Type'} (x' : type714 _132718) (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term435 _132718 x' s f b) = (term436 _132718 x' s f b).
Proof. exact (MK_COMB (@lem7111817 _132718 x' s f b) (@lem7111654 _132718 s f b)). Qed.
Lemma lem7111819 {_132718 : Type'} (x' : type714 _132718) (f : _132718 -> real) (b : real) : (term437 _132718 x' f b) = (term438 _132718 x' f b).
Proof. exact (fun_ext (fun s : _132718 -> Prop => @lem7111818 _132718 x' s f b)). Qed.
Lemma lem7111820 {_132718 : Type'} : (@all (_132718 -> Prop)) = (@all (_132718 -> Prop)).
Proof. exact (eq_refl (@all (_132718 -> Prop))). Qed.
Lemma lem7111821 {_132718 : Type'} (x' : type714 _132718) (f : _132718 -> real) (b : real) : (term439 _132718 x' f b) = (term440 _132718 x' f b).
Proof. exact (MK_COMB (@lem7111820 _132718) (@lem7111819 _132718 x' f b)). Qed.
Lemma lem7111822 {_132718 : Type'} (x' : type714 _132718) (f : _132718 -> real) : (term441 _132718 x' f) = (term442 _132718 x' f).
Proof. exact (fun_ext (fun b : real => @lem7111821 _132718 x' f b)). Qed.
Lemma lem7111823 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7111824 {_132718 : Type'} (x' : type714 _132718) (f : _132718 -> real) : (term367 _132718 x' f) = (term443 _132718 x' f).
Proof. exact (MK_COMB (@lem7111823) (@lem7111822 _132718 x' f)). Qed.
Lemma lem7111825 {_132718 : Type'} (x' : type714 _132718) : (term369 _132718 x') = (term444 _132718 x').
Proof. exact (fun_ext (fun f : _132718 -> real => @lem7111824 _132718 x' f)). Qed.
Lemma lem7111826 {_132718 : Type'} : (@all (_132718 -> real)) = (@all (_132718 -> real)).
Proof. exact (eq_refl (@all (_132718 -> real))). Qed.
Lemma lem7111827 {_132718 : Type'} (x' : type714 _132718) : (term371 _132718 x') = (term445 _132718 x').
Proof. exact (MK_COMB (@lem7111826 _132718) (@lem7111825 _132718 x')). Qed.
Lemma lem7111828 {_132718 : Type'} (x' : type714 _132718) (h1 : term371 _132718 x') : term445 _132718 x'.
Proof. exact (EQ_MP (@lem7111827 _132718 x') (@lem7111379 _132718 x' h1)). Qed.
Lemma lem7112127 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7112128 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7112129 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7112134 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7112135 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7112134 nat nat f x). Qed.
Lemma lem7112137 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem7112135 NUMERAL 0). Qed.
Lemma lem7112138 : term19 = term397.
Proof. exact (MK_COMB (@lem7112129) (@lem7112137)). Qed.
Lemma lem7112140 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7112141 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem7112140 nat real f x). Qed.
Lemma lem7112142 : term397 = term398.
Proof. exact (@lem7112141 real_of_num (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem7112143 : term19 = term398.
Proof. exact (TRANS (@lem7112138) (@lem7112142)). Qed.
Lemma lem7112148 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7112149 {_132718 : Type'} (f : _132718 -> real) (x : _132718) : (f x) = (@I (_132718 -> real) f x).
Proof. exact (@lem7112148 _132718 real f x). Qed.
Lemma lem7112151 {_132718 : Type'} (f : _132718 -> real) (x'''' : _132718) : (f x'''') = (@I (_132718 -> real) f x'''').
Proof. exact (@lem7112149 _132718 f x''''). Qed.
Lemma lem7112152 : term405 = term406.
Proof. exact (MK_COMB (@lem7112128) (@lem7112143)). Qed.
Lemma lem7112153 {_132718 : Type'} (f : _132718 -> real) (x'''' : _132718) : (term90 _132718 f x'''') = (term446 _132718 f x'''').
Proof. exact (MK_COMB (@lem7112152) (@lem7112151 _132718 f x'''')). Qed.
Lemma lem7112155 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7112156 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7112155 real (real -> Prop) f x). Qed.
Lemma lem7112157 : term406 = term409.
Proof. exact (@lem7112156 real_le term398). Qed.
Lemma lem7112158 {_132718 : Type'} (f : _132718 -> real) (x'''' : _132718) : (@I (_132718 -> real) f x'''') = (@I (_132718 -> real) f x'''').
Proof. exact (eq_refl (@I (_132718 -> real) f x'''')). Qed.
Lemma lem7112159 {_132718 : Type'} (f : _132718 -> real) (x'''' : _132718) : (term446 _132718 f x'''') = (term447 _132718 f x'''').
Proof. exact (MK_COMB (@lem7112157) (@lem7112158 _132718 f x'''')). Qed.
Lemma lem7112161 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7112162 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7112161 real Prop f x). Qed.
Lemma lem7112163 {_132718 : Type'} (f : _132718 -> real) (x'''' : _132718) : (term447 _132718 f x'''') = (term448 _132718 f x'''').
Proof. exact (@lem7112162 term409 (@I (_132718 -> real) f x'''')). Qed.
Lemma lem7112164 {_132718 : Type'} (f : _132718 -> real) (x'''' : _132718) : (term446 _132718 f x'''') = (term448 _132718 f x'''').
Proof. exact (TRANS (@lem7112159 _132718 f x'''') (@lem7112163 _132718 f x'''')). Qed.
Lemma lem7112165 {_132718 : Type'} (f : _132718 -> real) (x'''' : _132718) : (term90 _132718 f x'''') = (term448 _132718 f x'''').
Proof. exact (TRANS (@lem7112153 _132718 f x'''') (@lem7112164 _132718 f x'''')). Qed.
Lemma lem7112166 {_132718 : Type'} (f : _132718 -> real) (x'''' : _132718) : (term449 _132718 f x'''') = (term450 _132718 f x'''').
Proof. exact (MK_COMB (@lem7112127) (@lem7112165 _132718 f x'''')). Qed.
Lemma lem7112167 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7112168 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7112173 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7112174 {_132718 : Type'} (f : _132718 -> real) (x : _132718) : (f x) = (@I (_132718 -> real) f x).
Proof. exact (@lem7112173 _132718 real f x). Qed.
Lemma lem7112176 {_132718 : Type'} (f : _132718 -> real) (x'''' : _132718) : (f x'''') = (@I (_132718 -> real) f x'''').
Proof. exact (@lem7112174 _132718 f x''''). Qed.
Lemma lem7112177 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7112182 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7112183 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7112182 nat nat f x). Qed.
Lemma lem7112185 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem7112183 NUMERAL 0). Qed.
Lemma lem7112186 : term19 = term397.
Proof. exact (MK_COMB (@lem7112177) (@lem7112185)). Qed.
Lemma lem7112188 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7112189 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem7112188 nat real f x). Qed.
Lemma lem7112190 : term397 = term398.
Proof. exact (@lem7112189 real_of_num (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem7112191 : term19 = term398.
Proof. exact (TRANS (@lem7112186) (@lem7112190)). Qed.
Lemma lem7112192 {_132718 : Type'} (f : _132718 -> real) (x'''' : _132718) : (term375 _132718 f x'''') = (term376 _132718 f x'''').
Proof. exact (MK_COMB (@lem7112168) (@lem7112176 _132718 f x'''')). Qed.
Lemma lem7112193 {_132718 : Type'} (f : _132718 -> real) (x'''' : _132718) : (term98 _132718 f x'''') = (term451 _132718 f x'''').
Proof. exact (MK_COMB (@lem7112192 _132718 f x'''') (@lem7112191)). Qed.
Lemma lem7112195 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7112196 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7112195 real (real -> Prop) f x). Qed.
Lemma lem7112197 {_132718 : Type'} (f : _132718 -> real) (x'''' : _132718) : (term376 _132718 f x'''') = (term378 _132718 f x'''').
Proof. exact (@lem7112196 real_le (@I (_132718 -> real) f x'''')). Qed.
Lemma lem7112198 : term398 = term398.
Proof. exact (eq_refl term398). Qed.
Lemma lem7112199 {_132718 : Type'} (f : _132718 -> real) (x'''' : _132718) : (term451 _132718 f x'''') = (term452 _132718 f x'''').
Proof. exact (MK_COMB (@lem7112197 _132718 f x'''') (@lem7112198)). Qed.
Lemma lem7112201 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7112202 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7112201 real Prop f x). Qed.
Lemma lem7112203 {_132718 : Type'} (f : _132718 -> real) (x'''' : _132718) : (term452 _132718 f x'''') = (term453 _132718 f x'''').
Proof. exact (@lem7112202 (term378 _132718 f x'''') term398). Qed.
Lemma lem7112204 {_132718 : Type'} (f : _132718 -> real) (x'''' : _132718) : (term451 _132718 f x'''') = (term453 _132718 f x'''').
Proof. exact (TRANS (@lem7112199 _132718 f x'''') (@lem7112203 _132718 f x'''')). Qed.
Lemma lem7112205 {_132718 : Type'} (f : _132718 -> real) (x'''' : _132718) : (term98 _132718 f x'''') = (term453 _132718 f x'''').
Proof. exact (TRANS (@lem7112193 _132718 f x'''') (@lem7112204 _132718 f x'''')). Qed.
Lemma lem7112206 {_132718 : Type'} (f : _132718 -> real) (x'''' : _132718) : (term454 _132718 f x'''') = (term455 _132718 f x'''').
Proof. exact (MK_COMB (@lem7112167) (@lem7112205 _132718 f x'''')). Qed.
Lemma lem7112207 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7112208 {_132718 : Type'} (f : _132718 -> real) (x'''' : _132718) : (term456 _132718 f x'''') = (term457 _132718 f x'''').
Proof. exact (MK_COMB (@lem7112207) (@lem7112206 _132718 f x'''')). Qed.
Lemma lem7112209 {_132718 : Type'} (f : _132718 -> real) (x'''' : _132718) : (term97 _132718 f x'''') = (term458 _132718 f x'''').
Proof. exact (MK_COMB (@lem7112208 _132718 f x'''') (@lem7112166 _132718 f x'''')). Qed.
Lemma lem7112216 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7112217 {_132718 : Type'} (f : type1364 _132718) (x : _132718) : (f x) = (@I (_132718 -> (_132718 -> Prop) -> Prop) f x).
Proof. exact (@lem7112216 _132718 (type686 _132718) f x). Qed.
Lemma lem7112218 {_132718 : Type'} (x'''' : _132718) : (@IN _132718 x'''') = (@I (_132718 -> (_132718 -> Prop) -> Prop) (@IN _132718) x'''').
Proof. exact (@lem7112217 _132718 (@IN _132718) x''''). Qed.
Lemma lem7112219 {_132718 : Type'} (s : _132718 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7112220 {_132718 : Type'} (x'''' : _132718) (s : _132718 -> Prop) : (@IN _132718 x'''' s) = (@I (_132718 -> (_132718 -> Prop) -> Prop) (@IN _132718) x'''' s).
Proof. exact (MK_COMB (@lem7112218 _132718 x'''') (@lem7112219 _132718 s)). Qed.
Lemma lem7112222 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7112223 {_132718 : Type'} (f : type686 _132718) (x : _132718 -> Prop) : (f x) = (@I ((_132718 -> Prop) -> Prop) f x).
Proof. exact (@lem7112222 (_132718 -> Prop) Prop f x). Qed.
Lemma lem7112224 {_132718 : Type'} (x'''' : _132718) (s : _132718 -> Prop) : (@I (_132718 -> (_132718 -> Prop) -> Prop) (@IN _132718) x'''' s) = (term381 _132718 x'''' s).
Proof. exact (@lem7112223 _132718 (@I (_132718 -> (_132718 -> Prop) -> Prop) (@IN _132718) x'''') s). Qed.
Lemma lem7112226 {_132718 : Type'} (x'''' : _132718) (s : _132718 -> Prop) : (@IN _132718 x'''' s) = (term381 _132718 x'''' s).
Proof. exact (TRANS (@lem7112220 _132718 x'''' s) (@lem7112224 _132718 x'''' s)). Qed.
Lemma lem7112227 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7112228 {_132718 : Type'} (x'''' : _132718) (s : _132718 -> Prop) : (term99 _132718 x'''' s) = (term459 _132718 x'''' s).
Proof. exact (MK_COMB (@lem7112227) (@lem7112226 _132718 x'''' s)). Qed.
Lemma lem7112229 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) : (term101 _132718 s f x'''') = (term460 _132718 s f x'''').
Proof. exact (MK_COMB (@lem7112228 _132718 x'''' s) (@lem7112209 _132718 f x'''')). Qed.
Lemma lem7112230 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7112231 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7112236 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7112237 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7112236 nat nat f x). Qed.
Lemma lem7112239 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem7112237 NUMERAL 0). Qed.
Lemma lem7112240 : term19 = term397.
Proof. exact (MK_COMB (@lem7112231) (@lem7112239)). Qed.
Lemma lem7112242 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7112243 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem7112242 nat real f x). Qed.
Lemma lem7112244 : term397 = term398.
Proof. exact (@lem7112243 real_of_num (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem7112245 : term19 = term398.
Proof. exact (TRANS (@lem7112240) (@lem7112244)). Qed.
Lemma lem7112252 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7112253 {_132718 : Type'} (f : type646 _132718) (x : _132718 -> Prop) : (f x) = (@I ((_132718 -> Prop) -> (_132718 -> real) -> real) f x).
Proof. exact (@lem7112252 (_132718 -> Prop) (type717 _132718) f x). Qed.
Lemma lem7112254 {_132718 : Type'} (s : _132718 -> Prop) : (@sum _132718 s) = (@I ((_132718 -> Prop) -> (_132718 -> real) -> real) (@sum _132718) s).
Proof. exact (@lem7112253 _132718 (@sum _132718) s). Qed.
Lemma lem7112255 {_132718 : Type'} (f : _132718 -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7112256 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (@sum _132718 s f) = (@I ((_132718 -> Prop) -> (_132718 -> real) -> real) (@sum _132718) s f).
Proof. exact (MK_COMB (@lem7112254 _132718 s) (@lem7112255 _132718 f)). Qed.
Lemma lem7112258 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7112259 {_132718 : Type'} (f : type717 _132718) (x : _132718 -> real) : (f x) = (@I ((_132718 -> real) -> real) f x).
Proof. exact (@lem7112258 (_132718 -> real) real f x). Qed.
Lemma lem7112260 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (@I ((_132718 -> Prop) -> (_132718 -> real) -> real) (@sum _132718) s f) = (term389 _132718 s f).
Proof. exact (@lem7112259 _132718 (@I ((_132718 -> Prop) -> (_132718 -> real) -> real) (@sum _132718) s) f). Qed.
Lemma lem7112262 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (@sum _132718 s f) = (term389 _132718 s f).
Proof. exact (TRANS (@lem7112256 _132718 s f) (@lem7112260 _132718 s f)). Qed.
Lemma lem7112263 : term405 = term406.
Proof. exact (MK_COMB (@lem7112230) (@lem7112245)). Qed.
Lemma lem7112264 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term83 _132718 s f) = (term461 _132718 s f).
Proof. exact (MK_COMB (@lem7112263) (@lem7112262 _132718 s f)). Qed.
Lemma lem7112266 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7112267 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7112266 real (real -> Prop) f x). Qed.
Lemma lem7112268 : term406 = term409.
Proof. exact (@lem7112267 real_le term398). Qed.
Lemma lem7112269 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term389 _132718 s f) = (term389 _132718 s f).
Proof. exact (eq_refl (term389 _132718 s f)). Qed.
Lemma lem7112270 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term461 _132718 s f) = (term462 _132718 s f).
Proof. exact (MK_COMB (@lem7112268) (@lem7112269 _132718 s f)). Qed.
Lemma lem7112272 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7112273 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7112272 real Prop f x). Qed.
Lemma lem7112274 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term462 _132718 s f) = (term463 _132718 s f).
Proof. exact (@lem7112273 term409 (term389 _132718 s f)). Qed.
Lemma lem7112275 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term461 _132718 s f) = (term463 _132718 s f).
Proof. exact (TRANS (@lem7112270 _132718 s f) (@lem7112274 _132718 s f)). Qed.
Lemma lem7112276 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term83 _132718 s f) = (term463 _132718 s f).
Proof. exact (TRANS (@lem7112264 _132718 s f) (@lem7112275 _132718 s f)). Qed.
Lemma lem7112277 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7112284 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7112285 {_132718 : Type'} (f : type646 _132718) (x : _132718 -> Prop) : (f x) = (@I ((_132718 -> Prop) -> (_132718 -> real) -> real) f x).
Proof. exact (@lem7112284 (_132718 -> Prop) (type717 _132718) f x). Qed.
Lemma lem7112286 {_132718 : Type'} (s : _132718 -> Prop) : (@sum _132718 s) = (@I ((_132718 -> Prop) -> (_132718 -> real) -> real) (@sum _132718) s).
Proof. exact (@lem7112285 _132718 (@sum _132718) s). Qed.
Lemma lem7112287 {_132718 : Type'} (f : _132718 -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7112288 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (@sum _132718 s f) = (@I ((_132718 -> Prop) -> (_132718 -> real) -> real) (@sum _132718) s f).
Proof. exact (MK_COMB (@lem7112286 _132718 s) (@lem7112287 _132718 f)). Qed.
Lemma lem7112290 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7112291 {_132718 : Type'} (f : type717 _132718) (x : _132718 -> real) : (f x) = (@I ((_132718 -> real) -> real) f x).
Proof. exact (@lem7112290 (_132718 -> real) real f x). Qed.
Lemma lem7112292 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (@I ((_132718 -> Prop) -> (_132718 -> real) -> real) (@sum _132718) s f) = (term389 _132718 s f).
Proof. exact (@lem7112291 _132718 (@I ((_132718 -> Prop) -> (_132718 -> real) -> real) (@sum _132718) s) f). Qed.
Lemma lem7112294 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (@sum _132718 s f) = (term389 _132718 s f).
Proof. exact (TRANS (@lem7112288 _132718 s f) (@lem7112292 _132718 s f)). Qed.
Lemma lem7112295 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7112300 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7112301 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7112300 nat nat f x). Qed.
Lemma lem7112303 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem7112301 NUMERAL 0). Qed.
Lemma lem7112304 : term19 = term397.
Proof. exact (MK_COMB (@lem7112295) (@lem7112303)). Qed.
Lemma lem7112306 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7112307 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem7112306 nat real f x). Qed.
Lemma lem7112308 : term397 = term398.
Proof. exact (@lem7112307 real_of_num (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem7112309 : term19 = term398.
Proof. exact (TRANS (@lem7112304) (@lem7112308)). Qed.
Lemma lem7112310 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term390 _132718 s f) = (term391 _132718 s f).
Proof. exact (MK_COMB (@lem7112277) (@lem7112294 _132718 s f)). Qed.
Lemma lem7112311 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term464 _132718 s f) = (term465 _132718 s f).
Proof. exact (MK_COMB (@lem7112310 _132718 s f) (@lem7112309)). Qed.
Lemma lem7112313 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7112314 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7112313 real (real -> Prop) f x). Qed.
Lemma lem7112315 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term391 _132718 s f) = (term393 _132718 s f).
Proof. exact (@lem7112314 real_le (term389 _132718 s f)). Qed.
Lemma lem7112316 : term398 = term398.
Proof. exact (eq_refl term398). Qed.
Lemma lem7112317 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term465 _132718 s f) = (term466 _132718 s f).
Proof. exact (MK_COMB (@lem7112315 _132718 s f) (@lem7112316)). Qed.
Lemma lem7112319 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7112320 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7112319 real Prop f x). Qed.
Lemma lem7112321 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term466 _132718 s f) = (term467 _132718 s f).
Proof. exact (@lem7112320 (term393 _132718 s f) term398). Qed.
Lemma lem7112322 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term465 _132718 s f) = (term467 _132718 s f).
Proof. exact (TRANS (@lem7112317 _132718 s f) (@lem7112321 _132718 s f)). Qed.
Lemma lem7112323 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term464 _132718 s f) = (term467 _132718 s f).
Proof. exact (TRANS (@lem7112311 _132718 s f) (@lem7112322 _132718 s f)). Qed.
Lemma lem7112324 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7112325 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term468 _132718 s f) = (term469 _132718 s f).
Proof. exact (MK_COMB (@lem7112324) (@lem7112323 _132718 s f)). Qed.
Lemma lem7112326 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term20 _132718 s f) = (term470 _132718 s f).
Proof. exact (MK_COMB (@lem7112325 _132718 s f) (@lem7112276 _132718 s f)). Qed.
Lemma lem7112327 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7112328 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7112333 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7112334 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7112333 nat nat f x). Qed.
Lemma lem7112336 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem7112334 NUMERAL 0). Qed.
Lemma lem7112337 : term19 = term397.
Proof. exact (MK_COMB (@lem7112328) (@lem7112336)). Qed.
Lemma lem7112339 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7112340 (f : nat -> real) (x : nat) : (f x) = (@I (nat -> real) f x).
Proof. exact (@lem7112339 nat real f x). Qed.
Lemma lem7112341 : term397 = term398.
Proof. exact (@lem7112340 real_of_num (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem7112342 : term19 = term398.
Proof. exact (TRANS (@lem7112337) (@lem7112341)). Qed.
Lemma lem7112347 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7112349 {_132718 : Type'} (f : _132718 -> real) (x : _132718) : (f x) = (@I (_132718 -> real) f x).
Proof. exact (@lem7112347 _132718 real f x). Qed.
Lemma lem7112350 : term405 = term406.
Proof. exact (MK_COMB (@lem7112327) (@lem7112342)). Qed.
Lemma lem7112351 {_132718 : Type'} (f : _132718 -> real) (x : _132718) : (term90 _132718 f x) = (term446 _132718 f x).
Proof. exact (MK_COMB (@lem7112350) (@lem7112349 _132718 f x)). Qed.
Lemma lem7112353 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7112354 (f : type1626) (x : real) : (f x) = (@I (real -> real -> Prop) f x).
Proof. exact (@lem7112353 real (real -> Prop) f x). Qed.
Lemma lem7112355 : term406 = term409.
Proof. exact (@lem7112354 real_le term398). Qed.
Lemma lem7112356 {_132718 : Type'} (f : _132718 -> real) (x : _132718) : (@I (_132718 -> real) f x) = (@I (_132718 -> real) f x).
Proof. exact (eq_refl (@I (_132718 -> real) f x)). Qed.
Lemma lem7112357 {_132718 : Type'} (f : _132718 -> real) (x : _132718) : (term446 _132718 f x) = (term447 _132718 f x).
Proof. exact (MK_COMB (@lem7112355) (@lem7112356 _132718 f x)). Qed.
Lemma lem7112359 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7112360 (f : real -> Prop) (x : real) : (f x) = (@I (real -> Prop) f x).
Proof. exact (@lem7112359 real Prop f x). Qed.
Lemma lem7112361 {_132718 : Type'} (f : _132718 -> real) (x : _132718) : (term447 _132718 f x) = (term448 _132718 f x).
Proof. exact (@lem7112360 term409 (@I (_132718 -> real) f x)). Qed.
Lemma lem7112362 {_132718 : Type'} (f : _132718 -> real) (x : _132718) : (term446 _132718 f x) = (term448 _132718 f x).
Proof. exact (TRANS (@lem7112357 _132718 f x) (@lem7112361 _132718 f x)). Qed.
Lemma lem7112363 {_132718 : Type'} (f : _132718 -> real) (x : _132718) : (term90 _132718 f x) = (term448 _132718 f x).
Proof. exact (TRANS (@lem7112351 _132718 f x) (@lem7112362 _132718 f x)). Qed.
Lemma lem7112364 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7112371 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7112372 {_132718 : Type'} (f : type1364 _132718) (x : _132718) : (f x) = (@I (_132718 -> (_132718 -> Prop) -> Prop) f x).
Proof. exact (@lem7112371 _132718 (type686 _132718) f x). Qed.
Lemma lem7112373 {_132718 : Type'} (x : _132718) : (@IN _132718 x) = (@I (_132718 -> (_132718 -> Prop) -> Prop) (@IN _132718) x).
Proof. exact (@lem7112372 _132718 (@IN _132718) x). Qed.
Lemma lem7112374 {_132718 : Type'} (s : _132718 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7112375 {_132718 : Type'} (x : _132718) (s : _132718 -> Prop) : (@IN _132718 x s) = (@I (_132718 -> (_132718 -> Prop) -> Prop) (@IN _132718) x s).
Proof. exact (MK_COMB (@lem7112373 _132718 x) (@lem7112374 _132718 s)). Qed.
Lemma lem7112377 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7112378 {_132718 : Type'} (f : type686 _132718) (x : _132718 -> Prop) : (f x) = (@I ((_132718 -> Prop) -> Prop) f x).
Proof. exact (@lem7112377 (_132718 -> Prop) Prop f x). Qed.
Lemma lem7112379 {_132718 : Type'} (x : _132718) (s : _132718 -> Prop) : (@I (_132718 -> (_132718 -> Prop) -> Prop) (@IN _132718) x s) = (term381 _132718 x s).
Proof. exact (@lem7112378 _132718 (@I (_132718 -> (_132718 -> Prop) -> Prop) (@IN _132718) x) s). Qed.
Lemma lem7112381 {_132718 : Type'} (x : _132718) (s : _132718 -> Prop) : (@IN _132718 x s) = (term381 _132718 x s).
Proof. exact (TRANS (@lem7112375 _132718 x s) (@lem7112379 _132718 x s)). Qed.
Lemma lem7112382 {_132718 : Type'} (x : _132718) (s : _132718 -> Prop) : (term382 _132718 x s) = (term383 _132718 x s).
Proof. exact (MK_COMB (@lem7112364) (@lem7112381 _132718 x s)). Qed.
Lemma lem7112383 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7112384 {_132718 : Type'} (x : _132718) (s : _132718 -> Prop) : (term384 _132718 x s) = (term385 _132718 x s).
Proof. exact (MK_COMB (@lem7112383) (@lem7112382 _132718 x s)). Qed.
Lemma lem7112385 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) : (term89 _132718 s f x) = (term471 _132718 s f x).
Proof. exact (MK_COMB (@lem7112384 _132718 x s) (@lem7112363 _132718 f x)). Qed.
Lemma lem7112386 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term91 _132718 s f) = (term472 _132718 s f).
Proof. exact (fun_ext (fun x : _132718 => @lem7112385 _132718 s f x)). Qed.
Lemma lem7112387 {_132718 : Type'} : (@all _132718) = (@all _132718).
Proof. exact (eq_refl (@all _132718)). Qed.
Lemma lem7112388 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term92 _132718 s f) = (term473 _132718 s f).
Proof. exact (MK_COMB (@lem7112387 _132718) (@lem7112386 _132718 s f)). Qed.
Lemma lem7112389 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7112390 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term93 _132718 s f) = (term474 _132718 s f).
Proof. exact (MK_COMB (@lem7112389) (@lem7112388 _132718 s f)). Qed.
Lemma lem7112391 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term94 _132718 s f) = (term475 _132718 s f).
Proof. exact (MK_COMB (@lem7112390 _132718 s f) (@lem7112326 _132718 s f)). Qed.
Lemma lem7112396 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7112397 {_132718 : Type'} (f : type686 _132718) (x : _132718 -> Prop) : (f x) = (@I ((_132718 -> Prop) -> Prop) f x).
Proof. exact (@lem7112396 (_132718 -> Prop) Prop f x). Qed.
Lemma lem7112399 {_132718 : Type'} (s : _132718 -> Prop) : (@FINITE _132718 s) = (@I ((_132718 -> Prop) -> Prop) (@FINITE _132718) s).
Proof. exact (@lem7112397 _132718 (@FINITE _132718) s). Qed.
Lemma lem7112400 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7112401 {_132718 : Type'} (s : _132718 -> Prop) : (term24 _132718 s) = (term476 _132718 s).
Proof. exact (MK_COMB (@lem7112400) (@lem7112399 _132718 s)). Qed.
Lemma lem7112402 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term95 _132718 s f) = (term477 _132718 s f).
Proof. exact (MK_COMB (@lem7112401 _132718 s) (@lem7112391 _132718 s f)). Qed.
Lemma lem7112403 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7112404 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term113 _132718 s f) = (term478 _132718 s f).
Proof. exact (MK_COMB (@lem7112403) (@lem7112402 _132718 s f)). Qed.
Lemma lem7112405 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) : (term144 _132718 s f x'''') = (term479 _132718 s f x'''').
Proof. exact (MK_COMB (@lem7112404 _132718 s f) (@lem7112229 _132718 s f x'''')). Qed.
Lemma lem7112406 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term144 _132718 s f x'''') : term479 _132718 s f x''''.
Proof. exact (EQ_MP (@lem7112405 _132718 s f x'''') (@lem7111384 _132718 s f x'''' h1)). Qed.
Lemma lem7112407 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term144 _132718 s f x'''') : term460 _132718 s f x''''.
Proof. exact (proj2 (@lem7112406 _132718 s f x'''' h1)). Qed.
Lemma lem7112408 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term144 _132718 s f x'''') : term477 _132718 s f.
Proof. exact (proj1 (@lem7112406 _132718 s f x'''' h1)). Qed.
Lemma lem7112409 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term144 _132718 s f x'''') : term458 _132718 f x''''.
Proof. exact (proj2 (@lem7112407 _132718 s f x'''' h1)). Qed.
Lemma lem7112411 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term144 _132718 s f x'''') : term475 _132718 s f.
Proof. exact (proj2 (@lem7112408 _132718 s f x'''' h1)). Qed.
Lemma lem7112413 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term144 _132718 s f x'''') : term470 _132718 s f.
Proof. exact (proj2 (@lem7112411 _132718 s f x'''' h1)). Qed.
Lemma lem7112414 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term144 _132718 s f x'''') : term473 _132718 s f.
Proof. exact (proj1 (@lem7112411 _132718 s f x'''' h1)). Qed.
Lemma lem7112510 {A : Type'} (P : Prop) (Q : A -> Prop) : (term480 A P Q) = (term481 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem7112511 {_132718 : Type'} (P : Prop) (Q : _132718 -> Prop) : (term480 _132718 P Q) = (term481 _132718 P Q).
Proof. exact (@lem7112510 _132718 P Q). Qed.
Lemma lem7112512 {_132718 : Type'} (x' : type714 _132718) (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term482 _132718 x' s f b) = (term483 _132718 x' s f b).
Proof. exact (@lem7112511 _132718 (term432 _132718 x' s f b) (term387 _132718 s f b)). Qed.
Lemma lem7112513 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) (b : real) : (term484 _132718 s f b x) = (term386 _132718 s f x b).
Proof. exact (eq_refl (term484 _132718 s f b x)). Qed.
Lemma lem7112514 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term485 _132718 s f b) = (term387 _132718 s f b).
Proof. exact (fun_ext (fun x : _132718 => @lem7112513 _132718 s f x b)). Qed.
Lemma lem7112515 {_132718 : Type'} : (@all _132718) = (@all _132718).
Proof. exact (eq_refl (@all _132718)). Qed.
Lemma lem7112516 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term486 _132718 s f b) = (term388 _132718 s f b).
Proof. exact (MK_COMB (@lem7112515 _132718) (@lem7112514 _132718 s f b)). Qed.
Lemma lem7112517 {_132718 : Type'} (x' : type714 _132718) (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term434 _132718 x' s f b) = (term434 _132718 x' s f b).
Proof. exact (eq_refl (term434 _132718 x' s f b)). Qed.
Lemma lem7112518 {_132718 : Type'} (x' : type714 _132718) (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term482 _132718 x' s f b) = (term436 _132718 x' s f b).
Proof. exact (MK_COMB (@lem7112517 _132718 x' s f b) (@lem7112516 _132718 s f b)). Qed.
Lemma lem7112519 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7112520 {_132718 : Type'} (x' : type714 _132718) (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term487 _132718 x' s f b) = (term488 _132718 x' s f b).
Proof. exact (MK_COMB (@lem7112519) (@lem7112518 _132718 x' s f b)). Qed.
Lemma lem7112521 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) (b : real) : (term484 _132718 s f b x) = (term386 _132718 s f x b).
Proof. exact (eq_refl (term484 _132718 s f b x)). Qed.
Lemma lem7112522 {_132718 : Type'} (x' : type714 _132718) (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term434 _132718 x' s f b) = (term434 _132718 x' s f b).
Proof. exact (eq_refl (term434 _132718 x' s f b)). Qed.
Lemma lem7112523 {_132718 : Type'} (x' : type714 _132718) (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) (b : real) : (term489 _132718 x' s f b x) = (term490 _132718 x' s f x b).
Proof. exact (MK_COMB (@lem7112522 _132718 x' s f b) (@lem7112521 _132718 s f x b)). Qed.
Lemma lem7112524 {_132718 : Type'} (x' : type714 _132718) (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term491 _132718 x' s f b) = (term492 _132718 x' s f b).
Proof. exact (fun_ext (fun x : _132718 => @lem7112523 _132718 x' s f x b)). Qed.
Lemma lem7112525 {_132718 : Type'} : (@all _132718) = (@all _132718).
Proof. exact (eq_refl (@all _132718)). Qed.
Lemma lem7112526 {_132718 : Type'} (x' : type714 _132718) (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term483 _132718 x' s f b) = (term493 _132718 x' s f b).
Proof. exact (MK_COMB (@lem7112525 _132718) (@lem7112524 _132718 x' s f b)). Qed.
Lemma lem7112527 {_132718 : Type'} (x' : type714 _132718) (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : ((term482 _132718 x' s f b) = (term483 _132718 x' s f b)) = ((term436 _132718 x' s f b) = (term493 _132718 x' s f b)).
Proof. exact (MK_COMB (@lem7112520 _132718 x' s f b) (@lem7112526 _132718 x' s f b)). Qed.
Lemma lem7112528 {_132718 : Type'} (x' : type714 _132718) (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term436 _132718 x' s f b) = (term493 _132718 x' s f b).
Proof. exact (EQ_MP (@lem7112527 _132718 x' s f b) (@lem7112512 _132718 x' s f b)). Qed.
Lemma lem7112529 {_132718 : Type'} (x' : type714 _132718) (f : _132718 -> real) (b : real) : (term438 _132718 x' f b) = (term494 _132718 x' f b).
Proof. exact (fun_ext (fun s : _132718 -> Prop => @lem7112528 _132718 x' s f b)). Qed.
Lemma lem7112530 {_132718 : Type'} : (@all (_132718 -> Prop)) = (@all (_132718 -> Prop)).
Proof. exact (eq_refl (@all (_132718 -> Prop))). Qed.
Lemma lem7112531 {_132718 : Type'} (x' : type714 _132718) (f : _132718 -> real) (b : real) : (term440 _132718 x' f b) = (term495 _132718 x' f b).
Proof. exact (MK_COMB (@lem7112530 _132718) (@lem7112529 _132718 x' f b)). Qed.
Lemma lem7112532 {_132718 : Type'} (x' : type714 _132718) (f : _132718 -> real) : (term442 _132718 x' f) = (term496 _132718 x' f).
Proof. exact (fun_ext (fun b : real => @lem7112531 _132718 x' f b)). Qed.
Lemma lem7112533 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7112534 {_132718 : Type'} (x' : type714 _132718) (f : _132718 -> real) : (term443 _132718 x' f) = (term497 _132718 x' f).
Proof. exact (MK_COMB (@lem7112533) (@lem7112532 _132718 x' f)). Qed.
Lemma lem7112535 {_132718 : Type'} (x' : type714 _132718) : (term444 _132718 x') = (term498 _132718 x').
Proof. exact (fun_ext (fun f : _132718 -> real => @lem7112534 _132718 x' f)). Qed.
Lemma lem7112536 {_132718 : Type'} : (@all (_132718 -> real)) = (@all (_132718 -> real)).
Proof. exact (eq_refl (@all (_132718 -> real))). Qed.
Lemma lem7112537 {_132718 : Type'} (x' : type714 _132718) : (term445 _132718 x') = (term499 _132718 x').
Proof. exact (MK_COMB (@lem7112536 _132718) (@lem7112535 _132718 x')). Qed.
Lemma lem7112544 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) (b : real) : (term386 _132718 s f x b) = (term386 _132718 s f x b).
Proof. exact (eq_refl (term386 _132718 s f x b)). Qed.
Lemma lem7112561 {_132718 : Type'} (x' : type714 _132718) (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term428 _132718 x' s f b) = (term500 _132718 x' s f b).
Proof. exact (@lem19699 (term420 _132718 x' f b s) (term413 _132718 x' f b s) (term396 _132718 s f b)). Qed.
Lemma lem7112564 {_132718 : Type'} (s : _132718 -> Prop) : (term430 _132718 s) = (term430 _132718 s).
Proof. exact (eq_refl (term430 _132718 s)). Qed.
Lemma lem7112565 {_132718 : Type'} (x' : type714 _132718) (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term432 _132718 x' s f b) = (term501 _132718 x' s f b).
Proof. exact (MK_COMB (@lem7112564 _132718 s) (@lem7112561 _132718 x' s f b)). Qed.
Lemma lem7112572 {_132718 : Type'} (x' : type714 _132718) (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term501 _132718 x' s f b) = (term502 _132718 x' s f b).
Proof. exact (@lem19490 (term503 _132718 x' s f b) (term429 _132718 s) (term504 _132718 x' s f b)). Qed.
Lemma lem7112573 {_132718 : Type'} (x' : type714 _132718) (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term432 _132718 x' s f b) = (term502 _132718 x' s f b).
Proof. exact (TRANS (@lem7112565 _132718 x' s f b) (@lem7112572 _132718 x' s f b)). Qed.
Lemma lem7112574 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7112575 {_132718 : Type'} (x' : type714 _132718) (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term434 _132718 x' s f b) = (term505 _132718 x' s f b).
Proof. exact (MK_COMB (@lem7112574) (@lem7112573 _132718 x' s f b)). Qed.
Lemma lem7112576 {_132718 : Type'} (x' : type714 _132718) (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) (b : real) : (term490 _132718 x' s f x b) = (term506 _132718 x' s f x b).
Proof. exact (MK_COMB (@lem7112575 _132718 x' s f b) (@lem7112544 _132718 s f x b)). Qed.
Lemma lem7112583 {_132718 : Type'} (x' : type714 _132718) (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) (b : real) : (term506 _132718 x' s f x b) = (term507 _132718 x' s f x b).
Proof. exact (@lem19699 (term508 _132718 x' s f b) (term509 _132718 x' s f b) (term386 _132718 s f x b)). Qed.
Lemma lem7112584 {_132718 : Type'} (x' : type714 _132718) (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) (b : real) : (term490 _132718 x' s f x b) = (term507 _132718 x' s f x b).
Proof. exact (TRANS (@lem7112576 _132718 x' s f x b) (@lem7112583 _132718 x' s f x b)). Qed.
Lemma lem7112585 {_132718 : Type'} (x' : type714 _132718) (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term492 _132718 x' s f b) = (term510 _132718 x' s f b).
Proof. exact (fun_ext (fun x : _132718 => @lem7112584 _132718 x' s f x b)). Qed.
Lemma lem7112586 {_132718 : Type'} : (@all _132718) = (@all _132718).
Proof. exact (eq_refl (@all _132718)). Qed.
Lemma lem7112587 {_132718 : Type'} (x' : type714 _132718) (s : _132718 -> Prop) (f : _132718 -> real) (b : real) : (term493 _132718 x' s f b) = (term511 _132718 x' s f b).
Proof. exact (MK_COMB (@lem7112586 _132718) (@lem7112585 _132718 x' s f b)). Qed.
Lemma lem7112588 {_132718 : Type'} (x' : type714 _132718) (f : _132718 -> real) (b : real) : (term494 _132718 x' f b) = (term512 _132718 x' f b).
Proof. exact (fun_ext (fun s : _132718 -> Prop => @lem7112587 _132718 x' s f b)). Qed.
Lemma lem7112589 {_132718 : Type'} : (@all (_132718 -> Prop)) = (@all (_132718 -> Prop)).
Proof. exact (eq_refl (@all (_132718 -> Prop))). Qed.
Lemma lem7112590 {_132718 : Type'} (x' : type714 _132718) (f : _132718 -> real) (b : real) : (term495 _132718 x' f b) = (term513 _132718 x' f b).
Proof. exact (MK_COMB (@lem7112589 _132718) (@lem7112588 _132718 x' f b)). Qed.
Lemma lem7112591 {_132718 : Type'} (x' : type714 _132718) (f : _132718 -> real) : (term496 _132718 x' f) = (term514 _132718 x' f).
Proof. exact (fun_ext (fun b : real => @lem7112590 _132718 x' f b)). Qed.
Lemma lem7112592 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7112593 {_132718 : Type'} (x' : type714 _132718) (f : _132718 -> real) : (term497 _132718 x' f) = (term515 _132718 x' f).
Proof. exact (MK_COMB (@lem7112592) (@lem7112591 _132718 x' f)). Qed.
Lemma lem7112594 {_132718 : Type'} (x' : type714 _132718) : (term498 _132718 x') = (term516 _132718 x').
Proof. exact (fun_ext (fun f : _132718 -> real => @lem7112593 _132718 x' f)). Qed.
Lemma lem7112595 {_132718 : Type'} : (@all (_132718 -> real)) = (@all (_132718 -> real)).
Proof. exact (eq_refl (@all (_132718 -> real))). Qed.
Lemma lem7112596 {_132718 : Type'} (x' : type714 _132718) : (term499 _132718 x') = (term517 _132718 x').
Proof. exact (MK_COMB (@lem7112595 _132718) (@lem7112594 _132718 x')). Qed.
Lemma lem7112597 {_132718 : Type'} (x' : type714 _132718) : (term445 _132718 x') = (term517 _132718 x').
Proof. exact (TRANS (@lem7112537 _132718 x') (@lem7112596 _132718 x')). Qed.
Lemma lem7112598 {_132718 : Type'} (x' : type714 _132718) (h1 : term371 _132718 x') : term517 _132718 x'.
Proof. exact (EQ_MP (@lem7112597 _132718 x') (@lem7111828 _132718 x' h1)). Qed.
Lemma lem7112666 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) : (term471 _132718 s f x) = (term471 _132718 s f x).
Proof. exact (eq_refl (term471 _132718 s f x)). Qed.
Lemma lem7112667 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term472 _132718 s f) = (term472 _132718 s f).
Proof. exact (fun_ext (fun x : _132718 => @lem7112666 _132718 s f x)). Qed.
Lemma lem7112668 {_132718 : Type'} : (@all _132718) = (@all _132718).
Proof. exact (eq_refl (@all _132718)). Qed.
Lemma lem7112670 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term473 _132718 s f) = (term473 _132718 s f).
Proof. exact (MK_COMB (@lem7112668 _132718) (@lem7112667 _132718 s f)). Qed.
Lemma lem7112671 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term144 _132718 s f x'''') : term473 _132718 s f.
Proof. exact (EQ_MP (@lem7112670 _132718 s f) (@lem7112414 _132718 s f x'''' h1)). Qed.
Lemma lem7112683 {_132718 : Type'} (f : _132718 -> real) (x'''' : _132718) (h1 : term455 _132718 f x'''') : term455 _132718 f x''''.
Proof. exact (h1). Qed.
Lemma lem7112931 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x : _132718) : (term471 _132718 s f x) = (term471 _132718 s f x).
Proof. exact (eq_refl (term471 _132718 s f x)). Qed.
Lemma lem7112932 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term472 _132718 s f) = (term472 _132718 s f).
Proof. exact (fun_ext (fun x : _132718 => @lem7112931 _132718 s f x)). Qed.
Lemma lem7112933 {_132718 : Type'} : (@all _132718) = (@all _132718).
Proof. exact (eq_refl (@all _132718)). Qed.
Lemma lem7112935 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term473 _132718 s f) = (term473 _132718 s f).
Proof. exact (MK_COMB (@lem7112933 _132718) (@lem7112932 _132718 s f)). Qed.
Lemma lem7112936 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term144 _132718 s f x'''') : term473 _132718 s f.
Proof. exact (EQ_MP (@lem7112935 _132718 s f) (@lem7112414 _132718 s f x'''' h1)). Qed.
Lemma lem7112948 {_132718 : Type'} (f : _132718 -> real) (x'''' : _132718) (h1 : term450 _132718 f x'''') : term450 _132718 f x''''.
Proof. exact (h1). Qed.
Lemma lem7112961 {_132718 : Type'} (_95042 : _132718 -> real) (x' : type714 _132718) (h1 : term371 _132718 x') : term518 _132718 x' _95042.
Proof. exact (@lem7112598 _132718 x' h1 _95042). Qed.
Lemma lem7112962 {_132718 : Type'} (x' : type714 _132718) (_95042 : _132718 -> real) : (term518 _132718 x' _95042) = (term515 _132718 x' _95042).
Proof. exact (eq_refl (term518 _132718 x' _95042)). Qed.
Lemma lem7112963 {_132718 : Type'} (_95042 : _132718 -> real) (x' : type714 _132718) (h1 : term371 _132718 x') : term515 _132718 x' _95042.
Proof. exact (EQ_MP (@lem7112962 _132718 x' _95042) (@lem7112961 _132718 _95042 x' h1)). Qed.
Lemma lem7112964 {_132718 : Type'} (_95042 : _132718 -> real) (_95043 : real) (x' : type714 _132718) (h1 : term371 _132718 x') : term519 _132718 x' _95042 _95043.
Proof. exact (@lem7112963 _132718 _95042 x' h1 _95043). Qed.
Lemma lem7112965 {_132718 : Type'} (x' : type714 _132718) (_95042 : _132718 -> real) (_95043 : real) : (term519 _132718 x' _95042 _95043) = (term513 _132718 x' _95042 _95043).
Proof. exact (eq_refl (term519 _132718 x' _95042 _95043)). Qed.
Lemma lem7112966 {_132718 : Type'} (_95042 : _132718 -> real) (_95043 : real) (x' : type714 _132718) (h1 : term371 _132718 x') : term513 _132718 x' _95042 _95043.
Proof. exact (EQ_MP (@lem7112965 _132718 x' _95042 _95043) (@lem7112964 _132718 _95042 _95043 x' h1)). Qed.
Lemma lem7112967 {_132718 : Type'} (_95042 : _132718 -> real) (_95043 : real) (_95044 : _132718 -> Prop) (x' : type714 _132718) (h1 : term371 _132718 x') : term520 _132718 x' _95042 _95043 _95044.
Proof. exact (@lem7112966 _132718 _95042 _95043 x' h1 _95044). Qed.
Lemma lem7112968 {_132718 : Type'} (x' : type714 _132718) (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95043 : real) : (term520 _132718 x' _95042 _95043 _95044) = (term511 _132718 x' _95044 _95042 _95043).
Proof. exact (eq_refl (term520 _132718 x' _95042 _95043 _95044)). Qed.
Lemma lem7112969 {_132718 : Type'} (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95043 : real) (x' : type714 _132718) (h1 : term371 _132718 x') : term511 _132718 x' _95044 _95042 _95043.
Proof. exact (EQ_MP (@lem7112968 _132718 x' _95044 _95042 _95043) (@lem7112967 _132718 _95042 _95043 _95044 x' h1)). Qed.
Lemma lem7112970 {_132718 : Type'} (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95043 : real) (_95045 : _132718) (x' : type714 _132718) (h1 : term371 _132718 x') : term521 _132718 x' _95044 _95042 _95043 _95045.
Proof. exact (@lem7112969 _132718 _95044 _95042 _95043 x' h1 _95045). Qed.
Lemma lem7112971 {_132718 : Type'} (x' : type714 _132718) (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95045 : _132718) (_95043 : real) : (term521 _132718 x' _95044 _95042 _95043 _95045) = (term507 _132718 x' _95044 _95042 _95045 _95043).
Proof. exact (eq_refl (term521 _132718 x' _95044 _95042 _95043 _95045)). Qed.
Lemma lem7112972 {_132718 : Type'} (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95045 : _132718) (_95043 : real) (x' : type714 _132718) (h1 : term371 _132718 x') : term507 _132718 x' _95044 _95042 _95045 _95043.
Proof. exact (EQ_MP (@lem7112971 _132718 x' _95044 _95042 _95045 _95043) (@lem7112970 _132718 _95044 _95042 _95043 _95045 x' h1)). Qed.
Lemma lem7112985 {_132718 : Type'} (_95050 : _132718) (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term144 _132718 s f x'''') : term522 _132718 s f _95050.
Proof. exact (@lem7112671 _132718 s f x'''' h1 _95050). Qed.
Lemma lem7112986 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (_95050 : _132718) : (term522 _132718 s f _95050) = (term471 _132718 s f _95050).
Proof. exact (eq_refl (term522 _132718 s f _95050)). Qed.
Lemma lem7113024 {_132718 : Type'} (_95063 : _132718) (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term144 _132718 s f x'''') : term522 _132718 s f _95063.
Proof. exact (@lem7112936 _132718 s f x'''' h1 _95063). Qed.
Lemma lem7113025 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (_95063 : _132718) : (term522 _132718 s f _95063) = (term471 _132718 s f _95063).
Proof. exact (eq_refl (term522 _132718 s f _95063)). Qed.
Lemma lem7113031 {_132718 : Type'} (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95045 : _132718) (_95043 : real) (x' : type714 _132718) (h1 : term371 _132718 x') : term523 _132718 x' _95044 _95042 _95045 _95043.
Proof. exact (proj2 (@lem7112972 _132718 _95044 _95042 _95045 _95043 x' h1)). Qed.
Lemma lem7113032 {_132718 : Type'} (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95045 : _132718) (_95043 : real) (x' : type714 _132718) (h1 : term371 _132718 x') : term524 _132718 x' _95044 _95042 _95045 _95043.
Proof. exact (proj1 (@lem7112972 _132718 _95044 _95042 _95045 _95043 x' h1)). Qed.
Lemma lem7113052 {_132718 : Type'} (_95050 : _132718) (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term144 _132718 s f x'''') : term471 _132718 s f _95050.
Proof. exact (EQ_MP (@lem7112986 _132718 s f _95050) (@lem7112985 _132718 _95050 s f x'''' h1)). Qed.
Lemma lem7113058 {_132718 : Type'} (f : _132718 -> real) (x'''' : _132718) (h1 : term455 _132718 f x'''') : term455 _132718 f x''''.
Proof. exact (h1). Qed.
Lemma lem7113090 {_132718 : Type'} (x' : type714 _132718) (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95045 : _132718) (_95043 : real) : (term524 _132718 x' _95044 _95042 _95045 _95043) = (term525 _132718 x' _95044 _95042 _95045 _95043).
Proof. exact (@lem7109280 (term429 _132718 _95044) (term503 _132718 x' _95044 _95042 _95043) (term386 _132718 _95044 _95042 _95045 _95043)). Qed.
Lemma lem7113097 {_132718 : Type'} (x' : type714 _132718) (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95045 : _132718) (_95043 : real) : (term526 _132718 x' _95044 _95042 _95045 _95043) = (term527 _132718 x' _95044 _95042 _95045 _95043).
Proof. exact (@lem7109280 (term420 _132718 x' _95042 _95043 _95044) (term396 _132718 _95044 _95042 _95043) (term386 _132718 _95044 _95042 _95045 _95043)). Qed.
Lemma lem7113098 {_132718 : Type'} (_95044 : _132718 -> Prop) : (term430 _132718 _95044) = (term430 _132718 _95044).
Proof. exact (eq_refl (term430 _132718 _95044)). Qed.
Lemma lem7113101 {_132718 : Type'} (x' : type714 _132718) (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95045 : _132718) (_95043 : real) : (term525 _132718 x' _95044 _95042 _95045 _95043) = (term528 _132718 x' _95044 _95042 _95045 _95043).
Proof. exact (MK_COMB (@lem7113098 _132718 _95044) (@lem7113097 _132718 x' _95044 _95042 _95045 _95043)). Qed.
Lemma lem7113103 {_132718 : Type'} (x' : type714 _132718) (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95045 : _132718) (_95043 : real) : (term524 _132718 x' _95044 _95042 _95045 _95043) = (term528 _132718 x' _95044 _95042 _95045 _95043).
Proof. exact (TRANS (@lem7113090 _132718 x' _95044 _95042 _95045 _95043) (@lem7113101 _132718 x' _95044 _95042 _95045 _95043)). Qed.
Lemma lem7113104 {_132718 : Type'} (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95045 : _132718) (_95043 : real) (x' : type714 _132718) (h1 : term371 _132718 x') : term528 _132718 x' _95044 _95042 _95045 _95043.
Proof. exact (EQ_MP (@lem7113103 _132718 x' _95044 _95042 _95045 _95043) (@lem7113032 _132718 _95044 _95042 _95045 _95043 x' h1)). Qed.
Lemma lem7113112 {_132718 : Type'} (x' : type714 _132718) (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95045 : _132718) (_95043 : real) : (term523 _132718 x' _95044 _95042 _95045 _95043) = (term529 _132718 x' _95044 _95042 _95045 _95043).
Proof. exact (@lem7109280 (term429 _132718 _95044) (term504 _132718 x' _95044 _95042 _95043) (term386 _132718 _95044 _95042 _95045 _95043)). Qed.
Lemma lem7113119 {_132718 : Type'} (x' : type714 _132718) (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95045 : _132718) (_95043 : real) : (term530 _132718 x' _95044 _95042 _95045 _95043) = (term531 _132718 x' _95044 _95042 _95045 _95043).
Proof. exact (@lem7109280 (term413 _132718 x' _95042 _95043 _95044) (term396 _132718 _95044 _95042 _95043) (term386 _132718 _95044 _95042 _95045 _95043)). Qed.
Lemma lem7113120 {_132718 : Type'} (_95044 : _132718 -> Prop) : (term430 _132718 _95044) = (term430 _132718 _95044).
Proof. exact (eq_refl (term430 _132718 _95044)). Qed.
Lemma lem7113123 {_132718 : Type'} (x' : type714 _132718) (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95045 : _132718) (_95043 : real) : (term529 _132718 x' _95044 _95042 _95045 _95043) = (term532 _132718 x' _95044 _95042 _95045 _95043).
Proof. exact (MK_COMB (@lem7113120 _132718 _95044) (@lem7113119 _132718 x' _95044 _95042 _95045 _95043)). Qed.
Lemma lem7113125 {_132718 : Type'} (x' : type714 _132718) (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95045 : _132718) (_95043 : real) : (term523 _132718 x' _95044 _95042 _95045 _95043) = (term532 _132718 x' _95044 _95042 _95045 _95043).
Proof. exact (TRANS (@lem7113112 _132718 x' _95044 _95042 _95045 _95043) (@lem7113123 _132718 x' _95044 _95042 _95045 _95043)). Qed.
Lemma lem7113126 {_132718 : Type'} (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95045 : _132718) (_95043 : real) (x' : type714 _132718) (h1 : term371 _132718 x') : term532 _132718 x' _95044 _95042 _95045 _95043.
Proof. exact (EQ_MP (@lem7113125 _132718 x' _95044 _95042 _95045 _95043) (@lem7113031 _132718 _95044 _95042 _95045 _95043 x' h1)). Qed.
Lemma lem7113180 {_132718 : Type'} (_95063 : _132718) (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term144 _132718 s f x'''') : term471 _132718 s f _95063.
Proof. exact (EQ_MP (@lem7113025 _132718 s f _95063) (@lem7113024 _132718 _95063 s f x'''' h1)). Qed.
Lemma lem7113186 {_132718 : Type'} (f : _132718 -> real) (x'''' : _132718) (h1 : term450 _132718 f x'''') : term450 _132718 f x''''.
Proof. exact (h1). Qed.
Lemma lem7113300 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term144 _132718 s f x'''') : @I ((_132718 -> Prop) -> Prop) (@FINITE _132718) s.
Proof. exact (proj1 (@lem7112408 _132718 s f x'''' h1)). Qed.
Lemma lem7113301 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term144 _132718 s f x'''') : term533 _132718 s.
Proof. exact (fun h0 : term429 _132718 s => @lem7113300 _132718 s f x'''' h1). Qed.
Lemma lem7113303 (p : Prop) : (term534 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7113304 {_132718 : Type'} (s : _132718 -> Prop) : (term533 _132718 s) = (@I ((_132718 -> Prop) -> Prop) (@FINITE _132718) s).
Proof. exact (@lem7113303 (@I ((_132718 -> Prop) -> Prop) (@FINITE _132718) s)). Qed.
Lemma lem7113305 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term144 _132718 s f x'''') : @I ((_132718 -> Prop) -> Prop) (@FINITE _132718) s.
Proof. exact (EQ_MP (@lem7113304 _132718 s) (@lem7113301 _132718 s f x'''' h1)). Qed.
Lemma lem7113307 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term144 _132718 s f x'''') : @I ((_132718 -> Prop) -> Prop) (@FINITE _132718) s.
Proof. exact (proj1 (@lem7112408 _132718 s f x'''' h1)). Qed.
Lemma lem7113308 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term144 _132718 s f x'''') : term533 _132718 s.
Proof. exact (fun h0 : term429 _132718 s => @lem7113307 _132718 s f x'''' h1). Qed.
Lemma lem7113310 (p : Prop) : (term534 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7113311 {_132718 : Type'} (s : _132718 -> Prop) : (term533 _132718 s) = (@I ((_132718 -> Prop) -> Prop) (@FINITE _132718) s).
Proof. exact (@lem7113310 (@I ((_132718 -> Prop) -> Prop) (@FINITE _132718) s)). Qed.
Lemma lem7113312 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term144 _132718 s f x'''') : @I ((_132718 -> Prop) -> Prop) (@FINITE _132718) s.
Proof. exact (EQ_MP (@lem7113311 _132718 s) (@lem7113308 _132718 s f x'''' h1)). Qed.
Lemma lem7113314 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term144 _132718 s f x'''') : term467 _132718 s f.
Proof. exact (proj1 (@lem7112413 _132718 s f x'''' h1)). Qed.
Lemma lem7113315 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term144 _132718 s f x'''') : term535 _132718 s f.
Proof. exact (fun h0 : term536 _132718 s f => @lem7113314 _132718 s f x'''' h1). Qed.
Lemma lem7113317 (p : Prop) : (term534 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7113318 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term535 _132718 s f) = (term467 _132718 s f).
Proof. exact (@lem7113317 (term467 _132718 s f)). Qed.
Lemma lem7113319 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term144 _132718 s f x'''') : term467 _132718 s f.
Proof. exact (EQ_MP (@lem7113318 _132718 s f) (@lem7113315 _132718 s f x'''' h1)). Qed.
Lemma lem7113321 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term144 _132718 s f x'''') : term381 _132718 x'''' s.
Proof. exact (proj1 (@lem7112407 _132718 s f x'''' h1)). Qed.
Lemma lem7113322 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term144 _132718 s f x'''') : term537 _132718 x'''' s.
Proof. exact (fun h0 : term383 _132718 x'''' s => @lem7113321 _132718 s f x'''' h1). Qed.
Lemma lem7113324 (p : Prop) : (term534 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7113325 {_132718 : Type'} (x'''' : _132718) (s : _132718 -> Prop) : (term537 _132718 x'''' s) = (term381 _132718 x'''' s).
Proof. exact (@lem7113324 (term381 _132718 x'''' s)). Qed.
Lemma lem7113326 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term144 _132718 s f x'''') : term381 _132718 x'''' s.
Proof. exact (EQ_MP (@lem7113325 _132718 x'''' s) (@lem7113322 _132718 s f x'''' h1)). Qed.
Lemma lem7113329 {_132718 : Type'} (f : _132718 -> real) (x'''' : _132718) (h1 : term455 _132718 f x'''') : term455 _132718 f x''''.
Proof. exact (h1). Qed.
Lemma lem7113330 {_132718 : Type'} (f : _132718 -> real) (x'''' : _132718) (h1 : term455 _132718 f x'''') : term538 _132718 f x''''.
Proof. exact (fun h0 : term453 _132718 f x'''' => @lem7113329 _132718 f x'''' h1). Qed.
Lemma lem7113332 (p : Prop) : (term539 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7113333 {_132718 : Type'} (f : _132718 -> real) (x'''' : _132718) : (term538 _132718 f x'''') = (term455 _132718 f x'''').
Proof. exact (@lem7113332 (term453 _132718 f x'''')). Qed.
Lemma lem7113334 {_132718 : Type'} (f : _132718 -> real) (x'''' : _132718) (h1 : term455 _132718 f x'''') : term455 _132718 f x''''.
Proof. exact (EQ_MP (@lem7113333 _132718 f x'''') (@lem7113330 _132718 f x'''' h1)). Qed.
Lemma lem7113340 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7113341 {_132718 : Type'} (x' : type714 _132718) (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95045 : _132718) (_95043 : real) : (term528 _132718 x' _95044 _95042 _95045 _95043) = (term540 _132718 x' _95044 _95042 _95045 _95043).
Proof. exact (@lem7113340 (term420 _132718 x' _95042 _95043 _95044) (term429 _132718 _95044) (term541 _132718 _95044 _95042 _95045 _95043)). Qed.
Lemma lem7113365 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7113366 {_132718 : Type'} (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95045 : _132718) (_95043 : real) : (term541 _132718 _95044 _95042 _95045 _95043) = (term542 _132718 _95044 _95042 _95045 _95043).
Proof. exact (@lem7113365 (term383 _132718 _95045 _95044) (term396 _132718 _95044 _95042 _95043) (term380 _132718 _95042 _95045 _95043)). Qed.
Lemma lem7113380 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7113381 {_132718 : Type'} (_95045 : _132718) (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95043 : real) : (term543 _132718 _95044 _95042 _95045 _95043) = (term544 _132718 _95045 _95044 _95042 _95043).
Proof. exact (@lem7113380 (term380 _132718 _95042 _95045 _95043) (term396 _132718 _95044 _95042 _95043)). Qed.
Lemma lem7113387 {_132718 : Type'} (_95045 : _132718) (_95044 : _132718 -> Prop) : (term385 _132718 _95045 _95044) = (term385 _132718 _95045 _95044).
Proof. exact (eq_refl (term385 _132718 _95045 _95044)). Qed.
Lemma lem7113388 {_132718 : Type'} (_95045 : _132718) (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95043 : real) : (term542 _132718 _95044 _95042 _95045 _95043) = (term545 _132718 _95045 _95044 _95042 _95043).
Proof. exact (MK_COMB (@lem7113387 _132718 _95045 _95044) (@lem7113381 _132718 _95045 _95044 _95042 _95043)). Qed.
Lemma lem7113392 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7113393 {_132718 : Type'} (_95045 : _132718) (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95043 : real) : (term545 _132718 _95045 _95044 _95042 _95043) = (term546 _132718 _95045 _95044 _95042 _95043).
Proof. exact (@lem7113392 (term380 _132718 _95042 _95045 _95043) (term383 _132718 _95045 _95044) (term396 _132718 _95044 _95042 _95043)). Qed.
Lemma lem7113409 {_132718 : Type'} (_95045 : _132718) (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95043 : real) : (term542 _132718 _95044 _95042 _95045 _95043) = (term546 _132718 _95045 _95044 _95042 _95043).
Proof. exact (TRANS (@lem7113388 _132718 _95045 _95044 _95042 _95043) (@lem7113393 _132718 _95045 _95044 _95042 _95043)). Qed.
Lemma lem7113410 {_132718 : Type'} (_95045 : _132718) (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95043 : real) : (term541 _132718 _95044 _95042 _95045 _95043) = (term546 _132718 _95045 _95044 _95042 _95043).
Proof. exact (TRANS (@lem7113366 _132718 _95044 _95042 _95045 _95043) (@lem7113409 _132718 _95045 _95044 _95042 _95043)). Qed.
Lemma lem7113411 {_132718 : Type'} (_95044 : _132718 -> Prop) : (term430 _132718 _95044) = (term430 _132718 _95044).
Proof. exact (eq_refl (term430 _132718 _95044)). Qed.
Lemma lem7113412 {_132718 : Type'} (_95045 : _132718) (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95043 : real) : (term547 _132718 _95044 _95042 _95045 _95043) = (term548 _132718 _95045 _95044 _95042 _95043).
Proof. exact (MK_COMB (@lem7113411 _132718 _95044) (@lem7113410 _132718 _95045 _95044 _95042 _95043)). Qed.
Lemma lem7113416 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7113417 {_132718 : Type'} (_95045 : _132718) (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95043 : real) : (term548 _132718 _95045 _95044 _95042 _95043) = (term549 _132718 _95045 _95044 _95042 _95043).
Proof. exact (@lem7113416 (term380 _132718 _95042 _95045 _95043) (term429 _132718 _95044) (term550 _132718 _95045 _95044 _95042 _95043)). Qed.
Lemma lem7113443 {_132718 : Type'} (_95045 : _132718) (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95043 : real) : (term547 _132718 _95044 _95042 _95045 _95043) = (term549 _132718 _95045 _95044 _95042 _95043).
Proof. exact (TRANS (@lem7113412 _132718 _95045 _95044 _95042 _95043) (@lem7113417 _132718 _95045 _95044 _95042 _95043)). Qed.
Lemma lem7113444 {_132718 : Type'} (x' : type714 _132718) (_95042 : _132718 -> real) (_95043 : real) (_95044 : _132718 -> Prop) : (term551 _132718 x' _95042 _95043 _95044) = (term551 _132718 x' _95042 _95043 _95044).
Proof. exact (eq_refl (term551 _132718 x' _95042 _95043 _95044)). Qed.
Lemma lem7113445 {_132718 : Type'} (x' : type714 _132718) (_95045 : _132718) (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95043 : real) : (term540 _132718 x' _95044 _95042 _95045 _95043) = (term552 _132718 x' _95045 _95044 _95042 _95043).
Proof. exact (MK_COMB (@lem7113444 _132718 x' _95042 _95043 _95044) (@lem7113443 _132718 _95045 _95044 _95042 _95043)). Qed.
Lemma lem7113456 {_132718 : Type'} (x' : type714 _132718) (_95045 : _132718) (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95043 : real) : (term528 _132718 x' _95044 _95042 _95045 _95043) = (term552 _132718 x' _95045 _95044 _95042 _95043).
Proof. exact (TRANS (@lem7113341 _132718 x' _95044 _95042 _95045 _95043) (@lem7113445 _132718 x' _95045 _95044 _95042 _95043)). Qed.
Lemma lem7113457 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7113458 {_132718 : Type'} (x' : type714 _132718) (_95045 : _132718) (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95043 : real) : (term553 _132718 x' _95044 _95042 _95045 _95043) = (term554 _132718 x' _95045 _95044 _95042 _95043).
Proof. exact (MK_COMB (@lem7113457) (@lem7113456 _132718 x' _95045 _95044 _95042 _95043)). Qed.
Lemma lem7113482 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7113483 {_132718 : Type'} (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95045 : _132718) (_95043 : real) : (term541 _132718 _95044 _95042 _95045 _95043) = (term542 _132718 _95044 _95042 _95045 _95043).
Proof. exact (@lem7113482 (term383 _132718 _95045 _95044) (term396 _132718 _95044 _95042 _95043) (term380 _132718 _95042 _95045 _95043)). Qed.
Lemma lem7113497 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7113498 {_132718 : Type'} (_95045 : _132718) (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95043 : real) : (term543 _132718 _95044 _95042 _95045 _95043) = (term544 _132718 _95045 _95044 _95042 _95043).
Proof. exact (@lem7113497 (term380 _132718 _95042 _95045 _95043) (term396 _132718 _95044 _95042 _95043)). Qed.
Lemma lem7113504 {_132718 : Type'} (_95045 : _132718) (_95044 : _132718 -> Prop) : (term385 _132718 _95045 _95044) = (term385 _132718 _95045 _95044).
Proof. exact (eq_refl (term385 _132718 _95045 _95044)). Qed.
Lemma lem7113505 {_132718 : Type'} (_95045 : _132718) (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95043 : real) : (term542 _132718 _95044 _95042 _95045 _95043) = (term545 _132718 _95045 _95044 _95042 _95043).
Proof. exact (MK_COMB (@lem7113504 _132718 _95045 _95044) (@lem7113498 _132718 _95045 _95044 _95042 _95043)). Qed.
Lemma lem7113509 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7113510 {_132718 : Type'} (_95045 : _132718) (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95043 : real) : (term545 _132718 _95045 _95044 _95042 _95043) = (term546 _132718 _95045 _95044 _95042 _95043).
Proof. exact (@lem7113509 (term380 _132718 _95042 _95045 _95043) (term383 _132718 _95045 _95044) (term396 _132718 _95044 _95042 _95043)). Qed.
Lemma lem7113526 {_132718 : Type'} (_95045 : _132718) (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95043 : real) : (term542 _132718 _95044 _95042 _95045 _95043) = (term546 _132718 _95045 _95044 _95042 _95043).
Proof. exact (TRANS (@lem7113505 _132718 _95045 _95044 _95042 _95043) (@lem7113510 _132718 _95045 _95044 _95042 _95043)). Qed.
Lemma lem7113527 {_132718 : Type'} (_95045 : _132718) (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95043 : real) : (term541 _132718 _95044 _95042 _95045 _95043) = (term546 _132718 _95045 _95044 _95042 _95043).
Proof. exact (TRANS (@lem7113483 _132718 _95044 _95042 _95045 _95043) (@lem7113526 _132718 _95045 _95044 _95042 _95043)). Qed.
Lemma lem7113528 {_132718 : Type'} (_95044 : _132718 -> Prop) : (term430 _132718 _95044) = (term430 _132718 _95044).
Proof. exact (eq_refl (term430 _132718 _95044)). Qed.
Lemma lem7113529 {_132718 : Type'} (_95045 : _132718) (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95043 : real) : (term547 _132718 _95044 _95042 _95045 _95043) = (term548 _132718 _95045 _95044 _95042 _95043).
Proof. exact (MK_COMB (@lem7113528 _132718 _95044) (@lem7113527 _132718 _95045 _95044 _95042 _95043)). Qed.
Lemma lem7113533 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7113534 {_132718 : Type'} (_95045 : _132718) (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95043 : real) : (term548 _132718 _95045 _95044 _95042 _95043) = (term549 _132718 _95045 _95044 _95042 _95043).
Proof. exact (@lem7113533 (term380 _132718 _95042 _95045 _95043) (term429 _132718 _95044) (term550 _132718 _95045 _95044 _95042 _95043)). Qed.
Lemma lem7113560 {_132718 : Type'} (_95045 : _132718) (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95043 : real) : (term547 _132718 _95044 _95042 _95045 _95043) = (term549 _132718 _95045 _95044 _95042 _95043).
Proof. exact (TRANS (@lem7113529 _132718 _95045 _95044 _95042 _95043) (@lem7113534 _132718 _95045 _95044 _95042 _95043)). Qed.
Lemma lem7113561 {_132718 : Type'} (x' : type714 _132718) (_95042 : _132718 -> real) (_95043 : real) (_95044 : _132718 -> Prop) : (term551 _132718 x' _95042 _95043 _95044) = (term551 _132718 x' _95042 _95043 _95044).
Proof. exact (eq_refl (term551 _132718 x' _95042 _95043 _95044)). Qed.
Lemma lem7113562 {_132718 : Type'} (x' : type714 _132718) (_95045 : _132718) (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95043 : real) : (term540 _132718 x' _95044 _95042 _95045 _95043) = (term552 _132718 x' _95045 _95044 _95042 _95043).
Proof. exact (MK_COMB (@lem7113561 _132718 x' _95042 _95043 _95044) (@lem7113560 _132718 _95045 _95044 _95042 _95043)). Qed.
Lemma lem7113573 {_132718 : Type'} (x' : type714 _132718) (_95045 : _132718) (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95043 : real) : ((term528 _132718 x' _95044 _95042 _95045 _95043) = (term540 _132718 x' _95044 _95042 _95045 _95043)) = ((term552 _132718 x' _95045 _95044 _95042 _95043) = (term552 _132718 x' _95045 _95044 _95042 _95043)).
Proof. exact (MK_COMB (@lem7113458 _132718 x' _95045 _95044 _95042 _95043) (@lem7113562 _132718 x' _95045 _95044 _95042 _95043)). Qed.
Lemma lem7113575 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7113576 (x : Prop) : (x = x) = True.
Proof. exact (@lem7113575 Prop x). Qed.
Lemma lem7113577 {_132718 : Type'} (x' : type714 _132718) (_95045 : _132718) (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95043 : real) : ((term552 _132718 x' _95045 _95044 _95042 _95043) = (term552 _132718 x' _95045 _95044 _95042 _95043)) = True.
Proof. exact (@lem7113576 (term552 _132718 x' _95045 _95044 _95042 _95043)). Qed.
Lemma lem7113578 {_132718 : Type'} (x' : type714 _132718) (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95045 : _132718) (_95043 : real) : ((term528 _132718 x' _95044 _95042 _95045 _95043) = (term540 _132718 x' _95044 _95042 _95045 _95043)) = True.
Proof. exact (TRANS (@lem7113573 _132718 x' _95045 _95044 _95042 _95043) (@lem7113577 _132718 x' _95045 _95044 _95042 _95043)). Qed.
Lemma lem7113579 {_132718 : Type'} (x' : type714 _132718) (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95045 : _132718) (_95043 : real) : True = ((term528 _132718 x' _95044 _95042 _95045 _95043) = (term540 _132718 x' _95044 _95042 _95045 _95043)).
Proof. exact (SYM (@lem7113578 _132718 x' _95044 _95042 _95045 _95043)). Qed.
Lemma lem7113580 {_132718 : Type'} (x' : type714 _132718) (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95045 : _132718) (_95043 : real) : (term528 _132718 x' _95044 _95042 _95045 _95043) = (term540 _132718 x' _95044 _95042 _95045 _95043).
Proof. exact (EQ_MP (@lem7113579 _132718 x' _95044 _95042 _95045 _95043) (@lem0)). Qed.
Lemma lem7113581 {_132718 : Type'} (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95045 : _132718) (_95043 : real) (x' : type714 _132718) (h1 : term371 _132718 x') : term540 _132718 x' _95044 _95042 _95045 _95043.
Proof. exact (EQ_MP (@lem7113580 _132718 x' _95044 _95042 _95045 _95043) (@lem7113104 _132718 _95044 _95042 _95045 _95043 x' h1)). Qed.
Lemma lem7113583 (b : Prop) (a : Prop) : (a \/ b) = (term555 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7113584 {_132718 : Type'} (_95045 : _132718) (x' : type714 _132718) (_95042 : _132718 -> real) (_95043 : real) (_95044 : _132718 -> Prop) : (term540 _132718 x' _95044 _95042 _95045 _95043) = (term556 _132718 _95045 x' _95042 _95043 _95044).
Proof. exact (@lem7113583 (term547 _132718 _95044 _95042 _95045 _95043) (term420 _132718 x' _95042 _95043 _95044)). Qed.
Lemma lem7113586 (a : Prop) (b : Prop) : (term557 a b) = (term558 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7113587 {_132718 : Type'} (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95045 : _132718) (_95043 : real) : (term559 _132718 _95044 _95042 _95045 _95043) = (term560 _132718 _95044 _95042 _95045 _95043).
Proof. exact (@lem7113586 (term429 _132718 _95044) (term541 _132718 _95044 _95042 _95045 _95043)). Qed.
Lemma lem7113589 (a : Prop) : (term561 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7113590 {_132718 : Type'} (_95044 : _132718 -> Prop) : (term562 _132718 _95044) = (@I ((_132718 -> Prop) -> Prop) (@FINITE _132718) _95044).
Proof. exact (@lem7113589 (@I ((_132718 -> Prop) -> Prop) (@FINITE _132718) _95044)). Qed.
Lemma lem7113591 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7113592 {_132718 : Type'} (_95044 : _132718 -> Prop) : (term563 _132718 _95044) = (term476 _132718 _95044).
Proof. exact (MK_COMB (@lem7113591) (@lem7113590 _132718 _95044)). Qed.
Lemma lem7113594 (a : Prop) (b : Prop) : (term557 a b) = (term558 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7113595 {_132718 : Type'} (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95045 : _132718) (_95043 : real) : (term564 _132718 _95044 _95042 _95045 _95043) = (term565 _132718 _95044 _95042 _95045 _95043).
Proof. exact (@lem7113594 (term396 _132718 _95044 _95042 _95043) (term386 _132718 _95044 _95042 _95045 _95043)). Qed.
Lemma lem7113597 (a : Prop) : (term561 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7113598 {_132718 : Type'} (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95043 : real) : (term566 _132718 _95044 _95042 _95043) = (term395 _132718 _95044 _95042 _95043).
Proof. exact (@lem7113597 (term395 _132718 _95044 _95042 _95043)). Qed.
Lemma lem7113599 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7113600 {_132718 : Type'} (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95043 : real) : (term567 _132718 _95044 _95042 _95043) = (term568 _132718 _95044 _95042 _95043).
Proof. exact (MK_COMB (@lem7113599) (@lem7113598 _132718 _95044 _95042 _95043)). Qed.
Lemma lem7113602 (a : Prop) (b : Prop) : (term557 a b) = (term558 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7113603 {_132718 : Type'} (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95045 : _132718) (_95043 : real) : (term569 _132718 _95044 _95042 _95045 _95043) = (term570 _132718 _95044 _95042 _95045 _95043).
Proof. exact (@lem7113602 (term383 _132718 _95045 _95044) (term380 _132718 _95042 _95045 _95043)). Qed.
Lemma lem7113605 (a : Prop) : (term561 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7113606 {_132718 : Type'} (_95045 : _132718) (_95044 : _132718 -> Prop) : (term571 _132718 _95045 _95044) = (term381 _132718 _95045 _95044).
Proof. exact (@lem7113605 (term381 _132718 _95045 _95044)). Qed.
Lemma lem7113607 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7113608 {_132718 : Type'} (_95045 : _132718) (_95044 : _132718 -> Prop) : (term572 _132718 _95045 _95044) = (term459 _132718 _95045 _95044).
Proof. exact (MK_COMB (@lem7113607) (@lem7113606 _132718 _95045 _95044)). Qed.
Lemma lem7113609 {_132718 : Type'} (_95042 : _132718 -> real) (_95045 : _132718) (_95043 : real) : (term573 _132718 _95042 _95045 _95043) = (term573 _132718 _95042 _95045 _95043).
Proof. exact (eq_refl (term573 _132718 _95042 _95045 _95043)). Qed.
Lemma lem7113610 {_132718 : Type'} (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95045 : _132718) (_95043 : real) : (term570 _132718 _95044 _95042 _95045 _95043) = (term574 _132718 _95044 _95042 _95045 _95043).
Proof. exact (MK_COMB (@lem7113608 _132718 _95045 _95044) (@lem7113609 _132718 _95042 _95045 _95043)). Qed.
Lemma lem7113611 {_132718 : Type'} (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95045 : _132718) (_95043 : real) : (term569 _132718 _95044 _95042 _95045 _95043) = (term574 _132718 _95044 _95042 _95045 _95043).
Proof. exact (TRANS (@lem7113603 _132718 _95044 _95042 _95045 _95043) (@lem7113610 _132718 _95044 _95042 _95045 _95043)). Qed.
Lemma lem7113612 {_132718 : Type'} (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95045 : _132718) (_95043 : real) : (term565 _132718 _95044 _95042 _95045 _95043) = (term575 _132718 _95044 _95042 _95045 _95043).
Proof. exact (MK_COMB (@lem7113600 _132718 _95044 _95042 _95043) (@lem7113611 _132718 _95044 _95042 _95045 _95043)). Qed.
Lemma lem7113613 {_132718 : Type'} (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95045 : _132718) (_95043 : real) : (term564 _132718 _95044 _95042 _95045 _95043) = (term575 _132718 _95044 _95042 _95045 _95043).
Proof. exact (TRANS (@lem7113595 _132718 _95044 _95042 _95045 _95043) (@lem7113612 _132718 _95044 _95042 _95045 _95043)). Qed.
Lemma lem7113614 {_132718 : Type'} (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95045 : _132718) (_95043 : real) : (term560 _132718 _95044 _95042 _95045 _95043) = (term576 _132718 _95044 _95042 _95045 _95043).
Proof. exact (MK_COMB (@lem7113592 _132718 _95044) (@lem7113613 _132718 _95044 _95042 _95045 _95043)). Qed.
Lemma lem7113615 {_132718 : Type'} (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95045 : _132718) (_95043 : real) : (term559 _132718 _95044 _95042 _95045 _95043) = (term576 _132718 _95044 _95042 _95045 _95043).
Proof. exact (TRANS (@lem7113587 _132718 _95044 _95042 _95045 _95043) (@lem7113614 _132718 _95044 _95042 _95045 _95043)). Qed.
Lemma lem7113616 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7113617 {_132718 : Type'} (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95045 : _132718) (_95043 : real) : (term577 _132718 _95044 _95042 _95045 _95043) = (term578 _132718 _95044 _95042 _95045 _95043).
Proof. exact (MK_COMB (@lem7113616) (@lem7113615 _132718 _95044 _95042 _95045 _95043)). Qed.
Lemma lem7113618 {_132718 : Type'} (x' : type714 _132718) (_95042 : _132718 -> real) (_95043 : real) (_95044 : _132718 -> Prop) : (term420 _132718 x' _95042 _95043 _95044) = (term420 _132718 x' _95042 _95043 _95044).
Proof. exact (eq_refl (term420 _132718 x' _95042 _95043 _95044)). Qed.
Lemma lem7113619 {_132718 : Type'} (_95045 : _132718) (x' : type714 _132718) (_95042 : _132718 -> real) (_95043 : real) (_95044 : _132718 -> Prop) : (term556 _132718 _95045 x' _95042 _95043 _95044) = (term579 _132718 _95045 x' _95042 _95043 _95044).
Proof. exact (MK_COMB (@lem7113617 _132718 _95044 _95042 _95045 _95043) (@lem7113618 _132718 x' _95042 _95043 _95044)). Qed.
Lemma lem7113620 {_132718 : Type'} (_95045 : _132718) (x' : type714 _132718) (_95042 : _132718 -> real) (_95043 : real) (_95044 : _132718 -> Prop) : (term540 _132718 x' _95044 _95042 _95045 _95043) = (term579 _132718 _95045 x' _95042 _95043 _95044).
Proof. exact (TRANS (@lem7113584 _132718 _95045 x' _95042 _95043 _95044) (@lem7113619 _132718 _95045 x' _95042 _95043 _95044)). Qed.
Lemma lem7113622 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term455 _132718 f x'''') (h2 : term144 _132718 s f x'''') : term580 _132718 s f x''''.
Proof. exact (conj (@lem7113326 _132718 s f x'''' h2) (@lem7113334 _132718 f x'''' h1)). Qed.
Lemma lem7113623 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term455 _132718 f x'''') (h2 : term144 _132718 s f x'''') : term581 _132718 s f x''''.
Proof. exact (conj (@lem7113319 _132718 s f x'''' h2) (@lem7113622 _132718 s f x'''' h1 h2)). Qed.
Lemma lem7113624 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term455 _132718 f x'''') (h2 : term144 _132718 s f x'''') : term582 _132718 s f x''''.
Proof. exact (conj (@lem7113312 _132718 s f x'''' h2) (@lem7113623 _132718 s f x'''' h1 h2)). Qed.
Lemma lem7113626 {_132718 : Type'} (_95045 : _132718) (_95042 : _132718 -> real) (_95043 : real) (_95044 : _132718 -> Prop) (x' : type714 _132718) (h1 : term371 _132718 x') : term579 _132718 _95045 x' _95042 _95043 _95044.
Proof. exact (EQ_MP (@lem7113620 _132718 _95045 x' _95042 _95043 _95044) (@lem7113581 _132718 _95044 _95042 _95045 _95043 x' h1)). Qed.
Lemma lem7113627 {_132718 : Type'} (_95045 : _132718) (_95042 : _132718 -> real) (_95043 : real) (_95044 : _132718 -> Prop) (x' : type714 _132718) (h1 : term371 _132718 x') : term579 _132718 _95045 x' _95042 _95043 _95044.
Proof. exact (@lem7113626 _132718 _95045 _95042 _95043 _95044 x' h1). Qed.
Lemma lem7113628 {_132718 : Type'} (x'''' : _132718) (f : _132718 -> real) (s : _132718 -> Prop) (x' : type714 _132718) (h1 : term371 _132718 x') : term583 _132718 x'''' x' f s.
Proof. exact (@lem7113627 _132718 x'''' f term398 s x' h1). Qed.
Lemma lem7113631 {_132718 : Type'} (x' : type714 _132718) (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term371 _132718 x') (h2 : term455 _132718 f x'''') (h3 : term144 _132718 s f x'''') : term584 _132718 x' f s.
Proof. exact (@lem7113628 _132718 x'''' f s x' h1 (@lem7113624 _132718 s f x'''' h2 h3)). Qed.
Lemma lem7113632 {_132718 : Type'} (x' : type714 _132718) (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term371 _132718 x') (h2 : term455 _132718 f x'''') (h3 : term144 _132718 s f x'''') : term585 _132718 x' f s.
Proof. exact (fun h0 : term586 _132718 x' f s => @lem7113631 _132718 x' s f x'''' h1 h2 h3). Qed.
Lemma lem7113634 (p : Prop) : (term534 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7113635 {_132718 : Type'} (x' : type714 _132718) (f : _132718 -> real) (s : _132718 -> Prop) : (term585 _132718 x' f s) = (term584 _132718 x' f s).
Proof. exact (@lem7113634 (term584 _132718 x' f s)). Qed.
Lemma lem7113636 {_132718 : Type'} (x' : type714 _132718) (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term371 _132718 x') (h2 : term455 _132718 f x'''') (h3 : term144 _132718 s f x'''') : term584 _132718 x' f s.
Proof. exact (EQ_MP (@lem7113635 _132718 x' f s) (@lem7113632 _132718 x' s f x'''' h1 h2 h3)). Qed.
Lemma lem7113642 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7113643 {_132718 : Type'} (f : _132718 -> real) (_95050 : _132718) (s : _132718 -> Prop) : (term471 _132718 s f _95050) = (term587 _132718 f _95050 s).
Proof. exact (@lem7113642 (term448 _132718 f _95050) (term383 _132718 _95050 s)). Qed.
Lemma lem7113649 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7113650 {_132718 : Type'} (f : _132718 -> real) (_95050 : _132718) (s : _132718 -> Prop) : (term588 _132718 s f _95050) = (term589 _132718 f _95050 s).
Proof. exact (MK_COMB (@lem7113649) (@lem7113643 _132718 f _95050 s)). Qed.
Lemma lem7113656 {_132718 : Type'} (f : _132718 -> real) (_95050 : _132718) (s : _132718 -> Prop) : (term587 _132718 f _95050 s) = (term587 _132718 f _95050 s).
Proof. exact (eq_refl (term587 _132718 f _95050 s)). Qed.
Lemma lem7113657 {_132718 : Type'} (f : _132718 -> real) (_95050 : _132718) (s : _132718 -> Prop) : ((term471 _132718 s f _95050) = (term587 _132718 f _95050 s)) = ((term587 _132718 f _95050 s) = (term587 _132718 f _95050 s)).
Proof. exact (MK_COMB (@lem7113650 _132718 f _95050 s) (@lem7113656 _132718 f _95050 s)). Qed.
Lemma lem7113659 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7113660 (x : Prop) : (x = x) = True.
Proof. exact (@lem7113659 Prop x). Qed.
Lemma lem7113661 {_132718 : Type'} (f : _132718 -> real) (_95050 : _132718) (s : _132718 -> Prop) : ((term587 _132718 f _95050 s) = (term587 _132718 f _95050 s)) = True.
Proof. exact (@lem7113660 (term587 _132718 f _95050 s)). Qed.
Lemma lem7113662 {_132718 : Type'} (f : _132718 -> real) (_95050 : _132718) (s : _132718 -> Prop) : ((term471 _132718 s f _95050) = (term587 _132718 f _95050 s)) = True.
Proof. exact (TRANS (@lem7113657 _132718 f _95050 s) (@lem7113661 _132718 f _95050 s)). Qed.
Lemma lem7113663 {_132718 : Type'} (f : _132718 -> real) (_95050 : _132718) (s : _132718 -> Prop) : True = ((term471 _132718 s f _95050) = (term587 _132718 f _95050 s)).
Proof. exact (SYM (@lem7113662 _132718 f _95050 s)). Qed.
Lemma lem7113664 {_132718 : Type'} (f : _132718 -> real) (_95050 : _132718) (s : _132718 -> Prop) : (term471 _132718 s f _95050) = (term587 _132718 f _95050 s).
Proof. exact (EQ_MP (@lem7113663 _132718 f _95050 s) (@lem0)). Qed.
Lemma lem7113665 {_132718 : Type'} (_95050 : _132718) (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term144 _132718 s f x'''') : term587 _132718 f _95050 s.
Proof. exact (EQ_MP (@lem7113664 _132718 f _95050 s) (@lem7113052 _132718 _95050 s f x'''' h1)). Qed.
Lemma lem7113667 (b : Prop) (a : Prop) : (a \/ b) = (term555 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7113668 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (_95050 : _132718) : (term587 _132718 f _95050 s) = (term590 _132718 s f _95050).
Proof. exact (@lem7113667 (term383 _132718 _95050 s) (term448 _132718 f _95050)). Qed.
Lemma lem7113670 (a : Prop) : (term561 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7113671 {_132718 : Type'} (_95050 : _132718) (s : _132718 -> Prop) : (term571 _132718 _95050 s) = (term381 _132718 _95050 s).
Proof. exact (@lem7113670 (term381 _132718 _95050 s)). Qed.
Lemma lem7113672 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7113673 {_132718 : Type'} (_95050 : _132718) (s : _132718 -> Prop) : (term591 _132718 _95050 s) = (term592 _132718 _95050 s).
Proof. exact (MK_COMB (@lem7113672) (@lem7113671 _132718 _95050 s)). Qed.
Lemma lem7113674 {_132718 : Type'} (f : _132718 -> real) (_95050 : _132718) : (term448 _132718 f _95050) = (term448 _132718 f _95050).
Proof. exact (eq_refl (term448 _132718 f _95050)). Qed.
Lemma lem7113675 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (_95050 : _132718) : (term590 _132718 s f _95050) = (term593 _132718 s f _95050).
Proof. exact (MK_COMB (@lem7113673 _132718 _95050 s) (@lem7113674 _132718 f _95050)). Qed.
Lemma lem7113676 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (_95050 : _132718) : (term587 _132718 f _95050 s) = (term593 _132718 s f _95050).
Proof. exact (TRANS (@lem7113668 _132718 s f _95050) (@lem7113675 _132718 s f _95050)). Qed.
Lemma lem7113679 {_132718 : Type'} (_95050 : _132718) (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term144 _132718 s f x'''') : term593 _132718 s f _95050.
Proof. exact (EQ_MP (@lem7113676 _132718 s f _95050) (@lem7113665 _132718 _95050 s f x'''' h1)). Qed.
Lemma lem7113680 {_132718 : Type'} (_95050 : _132718) (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term144 _132718 s f x'''') : term593 _132718 s f _95050.
Proof. exact (@lem7113679 _132718 _95050 s f x'''' h1). Qed.
Lemma lem7113681 {_132718 : Type'} (x' : type714 _132718) (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term144 _132718 s f x'''') : term594 _132718 x' f s.
Proof. exact (@lem7113680 _132718 (term595 _132718 x' f s) s f x'''' h1). Qed.
Lemma lem7113684 {_132718 : Type'} (x' : type714 _132718) (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term371 _132718 x') (h2 : term455 _132718 f x'''') (h3 : term144 _132718 s f x'''') : term596 _132718 x' f s.
Proof. exact (@lem7113681 _132718 x' s f x'''' h3 (@lem7113636 _132718 x' s f x'''' h1 h2 h3)). Qed.
Lemma lem7113685 {_132718 : Type'} (x' : type714 _132718) (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term371 _132718 x') (h2 : term455 _132718 f x'''') (h3 : term144 _132718 s f x'''') : term597 _132718 x' f s.
Proof. exact (fun h0 : term598 _132718 x' f s => @lem7113684 _132718 x' s f x'''' h1 h2 h3). Qed.
Lemma lem7113687 (p : Prop) : (term534 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7113688 {_132718 : Type'} (x' : type714 _132718) (f : _132718 -> real) (s : _132718 -> Prop) : (term597 _132718 x' f s) = (term596 _132718 x' f s).
Proof. exact (@lem7113687 (term596 _132718 x' f s)). Qed.
Lemma lem7113689 {_132718 : Type'} (x' : type714 _132718) (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term371 _132718 x') (h2 : term455 _132718 f x'''') (h3 : term144 _132718 s f x'''') : term596 _132718 x' f s.
Proof. exact (EQ_MP (@lem7113688 _132718 x' f s) (@lem7113685 _132718 x' s f x'''' h1 h2 h3)). Qed.
Lemma lem7113691 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term144 _132718 s f x'''') : term467 _132718 s f.
Proof. exact (proj1 (@lem7112413 _132718 s f x'''' h1)). Qed.
Lemma lem7113692 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term144 _132718 s f x'''') : term535 _132718 s f.
Proof. exact (fun h0 : term536 _132718 s f => @lem7113691 _132718 s f x'''' h1). Qed.
Lemma lem7113694 (p : Prop) : (term534 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7113695 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) : (term535 _132718 s f) = (term467 _132718 s f).
Proof. exact (@lem7113694 (term467 _132718 s f)). Qed.
Lemma lem7113696 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term144 _132718 s f x'''') : term467 _132718 s f.
Proof. exact (EQ_MP (@lem7113695 _132718 s f) (@lem7113692 _132718 s f x'''' h1)). Qed.
Lemma lem7113698 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term144 _132718 s f x'''') : term381 _132718 x'''' s.
Proof. exact (proj1 (@lem7112407 _132718 s f x'''' h1)). Qed.
Lemma lem7113699 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term144 _132718 s f x'''') : term537 _132718 x'''' s.
Proof. exact (fun h0 : term383 _132718 x'''' s => @lem7113698 _132718 s f x'''' h1). Qed.
Lemma lem7113701 (p : Prop) : (term534 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7113702 {_132718 : Type'} (x'''' : _132718) (s : _132718 -> Prop) : (term537 _132718 x'''' s) = (term381 _132718 x'''' s).
Proof. exact (@lem7113701 (term381 _132718 x'''' s)). Qed.
Lemma lem7113703 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term144 _132718 s f x'''') : term381 _132718 x'''' s.
Proof. exact (EQ_MP (@lem7113702 _132718 x'''' s) (@lem7113699 _132718 s f x'''' h1)). Qed.
Lemma lem7113719 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7113720 {_132718 : Type'} (x' : type714 _132718) (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95045 : _132718) (_95043 : real) : (term531 _132718 x' _95044 _95042 _95045 _95043) = (term599 _132718 x' _95044 _95042 _95045 _95043).
Proof. exact (@lem7113719 (term396 _132718 _95044 _95042 _95043) (term413 _132718 x' _95042 _95043 _95044) (term386 _132718 _95044 _95042 _95045 _95043)). Qed.
Lemma lem7113734 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7113735 {_132718 : Type'} (x' : type714 _132718) (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95045 : _132718) (_95043 : real) : (term600 _132718 x' _95044 _95042 _95045 _95043) = (term601 _132718 x' _95044 _95042 _95045 _95043).
Proof. exact (@lem7113734 (term383 _132718 _95045 _95044) (term413 _132718 x' _95042 _95043 _95044) (term380 _132718 _95042 _95045 _95043)). Qed.
Lemma lem7113749 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7113750 {_132718 : Type'} (_95045 : _132718) (x' : type714 _132718) (_95042 : _132718 -> real) (_95043 : real) (_95044 : _132718 -> Prop) : (term602 _132718 x' _95044 _95042 _95045 _95043) = (term603 _132718 _95045 x' _95042 _95043 _95044).
Proof. exact (@lem7113749 (term380 _132718 _95042 _95045 _95043) (term413 _132718 x' _95042 _95043 _95044)). Qed.
Lemma lem7113756 {_132718 : Type'} (_95045 : _132718) (_95044 : _132718 -> Prop) : (term385 _132718 _95045 _95044) = (term385 _132718 _95045 _95044).
Proof. exact (eq_refl (term385 _132718 _95045 _95044)). Qed.
Lemma lem7113757 {_132718 : Type'} (_95045 : _132718) (x' : type714 _132718) (_95042 : _132718 -> real) (_95043 : real) (_95044 : _132718 -> Prop) : (term601 _132718 x' _95044 _95042 _95045 _95043) = (term604 _132718 _95045 x' _95042 _95043 _95044).
Proof. exact (MK_COMB (@lem7113756 _132718 _95045 _95044) (@lem7113750 _132718 _95045 x' _95042 _95043 _95044)). Qed.
Lemma lem7113761 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7113762 {_132718 : Type'} (_95045 : _132718) (x' : type714 _132718) (_95042 : _132718 -> real) (_95043 : real) (_95044 : _132718 -> Prop) : (term604 _132718 _95045 x' _95042 _95043 _95044) = (term605 _132718 _95045 x' _95042 _95043 _95044).
Proof. exact (@lem7113761 (term380 _132718 _95042 _95045 _95043) (term383 _132718 _95045 _95044) (term413 _132718 x' _95042 _95043 _95044)). Qed.
Lemma lem7113778 {_132718 : Type'} (_95045 : _132718) (x' : type714 _132718) (_95042 : _132718 -> real) (_95043 : real) (_95044 : _132718 -> Prop) : (term601 _132718 x' _95044 _95042 _95045 _95043) = (term605 _132718 _95045 x' _95042 _95043 _95044).
Proof. exact (TRANS (@lem7113757 _132718 _95045 x' _95042 _95043 _95044) (@lem7113762 _132718 _95045 x' _95042 _95043 _95044)). Qed.
Lemma lem7113779 {_132718 : Type'} (_95045 : _132718) (x' : type714 _132718) (_95042 : _132718 -> real) (_95043 : real) (_95044 : _132718 -> Prop) : (term600 _132718 x' _95044 _95042 _95045 _95043) = (term605 _132718 _95045 x' _95042 _95043 _95044).
Proof. exact (TRANS (@lem7113735 _132718 x' _95044 _95042 _95045 _95043) (@lem7113778 _132718 _95045 x' _95042 _95043 _95044)). Qed.
Lemma lem7113780 {_132718 : Type'} (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95043 : real) : (term606 _132718 _95044 _95042 _95043) = (term606 _132718 _95044 _95042 _95043).
Proof. exact (eq_refl (term606 _132718 _95044 _95042 _95043)). Qed.
Lemma lem7113781 {_132718 : Type'} (_95045 : _132718) (x' : type714 _132718) (_95042 : _132718 -> real) (_95043 : real) (_95044 : _132718 -> Prop) : (term599 _132718 x' _95044 _95042 _95045 _95043) = (term607 _132718 _95045 x' _95042 _95043 _95044).
Proof. exact (MK_COMB (@lem7113780 _132718 _95044 _95042 _95043) (@lem7113779 _132718 _95045 x' _95042 _95043 _95044)). Qed.
Lemma lem7113785 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7113786 {_132718 : Type'} (_95045 : _132718) (x' : type714 _132718) (_95042 : _132718 -> real) (_95043 : real) (_95044 : _132718 -> Prop) : (term607 _132718 _95045 x' _95042 _95043 _95044) = (term608 _132718 _95045 x' _95042 _95043 _95044).
Proof. exact (@lem7113785 (term380 _132718 _95042 _95045 _95043) (term396 _132718 _95044 _95042 _95043) (term609 _132718 _95045 x' _95042 _95043 _95044)). Qed.
Lemma lem7113800 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7113801 {_132718 : Type'} (_95045 : _132718) (x' : type714 _132718) (_95042 : _132718 -> real) (_95043 : real) (_95044 : _132718 -> Prop) : (term610 _132718 _95045 x' _95042 _95043 _95044) = (term611 _132718 _95045 x' _95042 _95043 _95044).
Proof. exact (@lem7113800 (term383 _132718 _95045 _95044) (term396 _132718 _95044 _95042 _95043) (term413 _132718 x' _95042 _95043 _95044)). Qed.
Lemma lem7113817 {_132718 : Type'} (_95042 : _132718 -> real) (_95045 : _132718) (_95043 : real) : (term612 _132718 _95042 _95045 _95043) = (term612 _132718 _95042 _95045 _95043).
Proof. exact (eq_refl (term612 _132718 _95042 _95045 _95043)). Qed.
Lemma lem7113818 {_132718 : Type'} (_95045 : _132718) (x' : type714 _132718) (_95042 : _132718 -> real) (_95043 : real) (_95044 : _132718 -> Prop) : (term608 _132718 _95045 x' _95042 _95043 _95044) = (term613 _132718 _95045 x' _95042 _95043 _95044).
Proof. exact (MK_COMB (@lem7113817 _132718 _95042 _95045 _95043) (@lem7113801 _132718 _95045 x' _95042 _95043 _95044)). Qed.
Lemma lem7113829 {_132718 : Type'} (_95045 : _132718) (x' : type714 _132718) (_95042 : _132718 -> real) (_95043 : real) (_95044 : _132718 -> Prop) : (term607 _132718 _95045 x' _95042 _95043 _95044) = (term613 _132718 _95045 x' _95042 _95043 _95044).
Proof. exact (TRANS (@lem7113786 _132718 _95045 x' _95042 _95043 _95044) (@lem7113818 _132718 _95045 x' _95042 _95043 _95044)). Qed.
Lemma lem7113830 {_132718 : Type'} (_95045 : _132718) (x' : type714 _132718) (_95042 : _132718 -> real) (_95043 : real) (_95044 : _132718 -> Prop) : (term599 _132718 x' _95044 _95042 _95045 _95043) = (term613 _132718 _95045 x' _95042 _95043 _95044).
Proof. exact (TRANS (@lem7113781 _132718 _95045 x' _95042 _95043 _95044) (@lem7113829 _132718 _95045 x' _95042 _95043 _95044)). Qed.
Lemma lem7113831 {_132718 : Type'} (_95045 : _132718) (x' : type714 _132718) (_95042 : _132718 -> real) (_95043 : real) (_95044 : _132718 -> Prop) : (term531 _132718 x' _95044 _95042 _95045 _95043) = (term613 _132718 _95045 x' _95042 _95043 _95044).
Proof. exact (TRANS (@lem7113720 _132718 x' _95044 _95042 _95045 _95043) (@lem7113830 _132718 _95045 x' _95042 _95043 _95044)). Qed.
Lemma lem7113832 {_132718 : Type'} (_95044 : _132718 -> Prop) : (term430 _132718 _95044) = (term430 _132718 _95044).
Proof. exact (eq_refl (term430 _132718 _95044)). Qed.
Lemma lem7113833 {_132718 : Type'} (_95045 : _132718) (x' : type714 _132718) (_95042 : _132718 -> real) (_95043 : real) (_95044 : _132718 -> Prop) : (term532 _132718 x' _95044 _95042 _95045 _95043) = (term614 _132718 _95045 x' _95042 _95043 _95044).
Proof. exact (MK_COMB (@lem7113832 _132718 _95044) (@lem7113831 _132718 _95045 x' _95042 _95043 _95044)). Qed.
Lemma lem7113837 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7113838 {_132718 : Type'} (_95045 : _132718) (x' : type714 _132718) (_95042 : _132718 -> real) (_95043 : real) (_95044 : _132718 -> Prop) : (term614 _132718 _95045 x' _95042 _95043 _95044) = (term615 _132718 _95045 x' _95042 _95043 _95044).
Proof. exact (@lem7113837 (term380 _132718 _95042 _95045 _95043) (term429 _132718 _95044) (term611 _132718 _95045 x' _95042 _95043 _95044)). Qed.
Lemma lem7113874 {_132718 : Type'} (_95045 : _132718) (x' : type714 _132718) (_95042 : _132718 -> real) (_95043 : real) (_95044 : _132718 -> Prop) : (term532 _132718 x' _95044 _95042 _95045 _95043) = (term615 _132718 _95045 x' _95042 _95043 _95044).
Proof. exact (TRANS (@lem7113833 _132718 _95045 x' _95042 _95043 _95044) (@lem7113838 _132718 _95045 x' _95042 _95043 _95044)). Qed.
Lemma lem7113875 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7113876 {_132718 : Type'} (_95045 : _132718) (x' : type714 _132718) (_95042 : _132718 -> real) (_95043 : real) (_95044 : _132718 -> Prop) : (term616 _132718 x' _95044 _95042 _95045 _95043) = (term617 _132718 _95045 x' _95042 _95043 _95044).
Proof. exact (MK_COMB (@lem7113875) (@lem7113874 _132718 _95045 x' _95042 _95043 _95044)). Qed.
Lemma lem7113900 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7113901 {_132718 : Type'} (x' : type714 _132718) (_95042 : _132718 -> real) (_95043 : real) (_95045 : _132718) (_95044 : _132718 -> Prop) : (term618 _132718 x' _95042 _95043 _95045 _95044) = (term619 _132718 x' _95042 _95043 _95045 _95044).
Proof. exact (@lem7113900 (term396 _132718 _95044 _95042 _95043) (term413 _132718 x' _95042 _95043 _95044) (term383 _132718 _95045 _95044)). Qed.
Lemma lem7113915 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7113916 {_132718 : Type'} (_95045 : _132718) (x' : type714 _132718) (_95042 : _132718 -> real) (_95043 : real) (_95044 : _132718 -> Prop) : (term620 _132718 x' _95042 _95043 _95045 _95044) = (term609 _132718 _95045 x' _95042 _95043 _95044).
Proof. exact (@lem7113915 (term383 _132718 _95045 _95044) (term413 _132718 x' _95042 _95043 _95044)). Qed.
Lemma lem7113922 {_132718 : Type'} (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95043 : real) : (term606 _132718 _95044 _95042 _95043) = (term606 _132718 _95044 _95042 _95043).
Proof. exact (eq_refl (term606 _132718 _95044 _95042 _95043)). Qed.
Lemma lem7113923 {_132718 : Type'} (_95045 : _132718) (x' : type714 _132718) (_95042 : _132718 -> real) (_95043 : real) (_95044 : _132718 -> Prop) : (term619 _132718 x' _95042 _95043 _95045 _95044) = (term610 _132718 _95045 x' _95042 _95043 _95044).
Proof. exact (MK_COMB (@lem7113922 _132718 _95044 _95042 _95043) (@lem7113916 _132718 _95045 x' _95042 _95043 _95044)). Qed.
Lemma lem7113927 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7113928 {_132718 : Type'} (_95045 : _132718) (x' : type714 _132718) (_95042 : _132718 -> real) (_95043 : real) (_95044 : _132718 -> Prop) : (term610 _132718 _95045 x' _95042 _95043 _95044) = (term611 _132718 _95045 x' _95042 _95043 _95044).
Proof. exact (@lem7113927 (term383 _132718 _95045 _95044) (term396 _132718 _95044 _95042 _95043) (term413 _132718 x' _95042 _95043 _95044)). Qed.
Lemma lem7113944 {_132718 : Type'} (_95045 : _132718) (x' : type714 _132718) (_95042 : _132718 -> real) (_95043 : real) (_95044 : _132718 -> Prop) : (term619 _132718 x' _95042 _95043 _95045 _95044) = (term611 _132718 _95045 x' _95042 _95043 _95044).
Proof. exact (TRANS (@lem7113923 _132718 _95045 x' _95042 _95043 _95044) (@lem7113928 _132718 _95045 x' _95042 _95043 _95044)). Qed.
Lemma lem7113945 {_132718 : Type'} (_95045 : _132718) (x' : type714 _132718) (_95042 : _132718 -> real) (_95043 : real) (_95044 : _132718 -> Prop) : (term618 _132718 x' _95042 _95043 _95045 _95044) = (term611 _132718 _95045 x' _95042 _95043 _95044).
Proof. exact (TRANS (@lem7113901 _132718 x' _95042 _95043 _95045 _95044) (@lem7113944 _132718 _95045 x' _95042 _95043 _95044)). Qed.
Lemma lem7113946 {_132718 : Type'} (_95044 : _132718 -> Prop) : (term430 _132718 _95044) = (term430 _132718 _95044).
Proof. exact (eq_refl (term430 _132718 _95044)). Qed.
Lemma lem7113947 {_132718 : Type'} (_95045 : _132718) (x' : type714 _132718) (_95042 : _132718 -> real) (_95043 : real) (_95044 : _132718 -> Prop) : (term621 _132718 x' _95042 _95043 _95045 _95044) = (term622 _132718 _95045 x' _95042 _95043 _95044).
Proof. exact (MK_COMB (@lem7113946 _132718 _95044) (@lem7113945 _132718 _95045 x' _95042 _95043 _95044)). Qed.
Lemma lem7113958 {_132718 : Type'} (_95042 : _132718 -> real) (_95045 : _132718) (_95043 : real) : (term612 _132718 _95042 _95045 _95043) = (term612 _132718 _95042 _95045 _95043).
Proof. exact (eq_refl (term612 _132718 _95042 _95045 _95043)). Qed.
Lemma lem7113959 {_132718 : Type'} (_95045 : _132718) (x' : type714 _132718) (_95042 : _132718 -> real) (_95043 : real) (_95044 : _132718 -> Prop) : (term623 _132718 x' _95042 _95043 _95045 _95044) = (term615 _132718 _95045 x' _95042 _95043 _95044).
Proof. exact (MK_COMB (@lem7113958 _132718 _95042 _95045 _95043) (@lem7113947 _132718 _95045 x' _95042 _95043 _95044)). Qed.
Lemma lem7113970 {_132718 : Type'} (_95045 : _132718) (x' : type714 _132718) (_95042 : _132718 -> real) (_95043 : real) (_95044 : _132718 -> Prop) : ((term532 _132718 x' _95044 _95042 _95045 _95043) = (term623 _132718 x' _95042 _95043 _95045 _95044)) = ((term615 _132718 _95045 x' _95042 _95043 _95044) = (term615 _132718 _95045 x' _95042 _95043 _95044)).
Proof. exact (MK_COMB (@lem7113876 _132718 _95045 x' _95042 _95043 _95044) (@lem7113959 _132718 _95045 x' _95042 _95043 _95044)). Qed.
Lemma lem7113972 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7113973 (x : Prop) : (x = x) = True.
Proof. exact (@lem7113972 Prop x). Qed.
Lemma lem7113974 {_132718 : Type'} (_95045 : _132718) (x' : type714 _132718) (_95042 : _132718 -> real) (_95043 : real) (_95044 : _132718 -> Prop) : ((term615 _132718 _95045 x' _95042 _95043 _95044) = (term615 _132718 _95045 x' _95042 _95043 _95044)) = True.
Proof. exact (@lem7113973 (term615 _132718 _95045 x' _95042 _95043 _95044)). Qed.
Lemma lem7113975 {_132718 : Type'} (x' : type714 _132718) (_95042 : _132718 -> real) (_95043 : real) (_95045 : _132718) (_95044 : _132718 -> Prop) : ((term532 _132718 x' _95044 _95042 _95045 _95043) = (term623 _132718 x' _95042 _95043 _95045 _95044)) = True.
Proof. exact (TRANS (@lem7113970 _132718 _95045 x' _95042 _95043 _95044) (@lem7113974 _132718 _95045 x' _95042 _95043 _95044)). Qed.
Lemma lem7113976 {_132718 : Type'} (x' : type714 _132718) (_95042 : _132718 -> real) (_95043 : real) (_95045 : _132718) (_95044 : _132718 -> Prop) : True = ((term532 _132718 x' _95044 _95042 _95045 _95043) = (term623 _132718 x' _95042 _95043 _95045 _95044)).
Proof. exact (SYM (@lem7113975 _132718 x' _95042 _95043 _95045 _95044)). Qed.
Lemma lem7113977 {_132718 : Type'} (x' : type714 _132718) (_95042 : _132718 -> real) (_95043 : real) (_95045 : _132718) (_95044 : _132718 -> Prop) : (term532 _132718 x' _95044 _95042 _95045 _95043) = (term623 _132718 x' _95042 _95043 _95045 _95044).
Proof. exact (EQ_MP (@lem7113976 _132718 x' _95042 _95043 _95045 _95044) (@lem0)). Qed.
Lemma lem7113978 {_132718 : Type'} (_95042 : _132718 -> real) (_95043 : real) (_95045 : _132718) (_95044 : _132718 -> Prop) (x' : type714 _132718) (h1 : term371 _132718 x') : term623 _132718 x' _95042 _95043 _95045 _95044.
Proof. exact (EQ_MP (@lem7113977 _132718 x' _95042 _95043 _95045 _95044) (@lem7113126 _132718 _95044 _95042 _95045 _95043 x' h1)). Qed.
Lemma lem7113980 (b : Prop) (a : Prop) : (a \/ b) = (term555 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7113981 {_132718 : Type'} (x' : type714 _132718) (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95045 : _132718) (_95043 : real) : (term623 _132718 x' _95042 _95043 _95045 _95044) = (term624 _132718 x' _95044 _95042 _95045 _95043).
Proof. exact (@lem7113980 (term621 _132718 x' _95042 _95043 _95045 _95044) (term380 _132718 _95042 _95045 _95043)). Qed.
Lemma lem7113983 (a : Prop) (b : Prop) : (term557 a b) = (term558 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7113984 {_132718 : Type'} (x' : type714 _132718) (_95042 : _132718 -> real) (_95043 : real) (_95045 : _132718) (_95044 : _132718 -> Prop) : (term625 _132718 x' _95042 _95043 _95045 _95044) = (term626 _132718 x' _95042 _95043 _95045 _95044).
Proof. exact (@lem7113983 (term429 _132718 _95044) (term618 _132718 x' _95042 _95043 _95045 _95044)). Qed.
Lemma lem7113986 (a : Prop) : (term561 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7113987 {_132718 : Type'} (_95044 : _132718 -> Prop) : (term562 _132718 _95044) = (@I ((_132718 -> Prop) -> Prop) (@FINITE _132718) _95044).
Proof. exact (@lem7113986 (@I ((_132718 -> Prop) -> Prop) (@FINITE _132718) _95044)). Qed.
Lemma lem7113988 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7113989 {_132718 : Type'} (_95044 : _132718 -> Prop) : (term563 _132718 _95044) = (term476 _132718 _95044).
Proof. exact (MK_COMB (@lem7113988) (@lem7113987 _132718 _95044)). Qed.
Lemma lem7113991 (a : Prop) (b : Prop) : (term557 a b) = (term558 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7113992 {_132718 : Type'} (x' : type714 _132718) (_95042 : _132718 -> real) (_95043 : real) (_95045 : _132718) (_95044 : _132718 -> Prop) : (term627 _132718 x' _95042 _95043 _95045 _95044) = (term628 _132718 x' _95042 _95043 _95045 _95044).
Proof. exact (@lem7113991 (term413 _132718 x' _95042 _95043 _95044) (term629 _132718 _95042 _95043 _95045 _95044)). Qed.
Lemma lem7113994 (a : Prop) : (term561 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7113995 {_132718 : Type'} (x' : type714 _132718) (_95042 : _132718 -> real) (_95043 : real) (_95044 : _132718 -> Prop) : (term630 _132718 x' _95042 _95043 _95044) = (term411 _132718 x' _95042 _95043 _95044).
Proof. exact (@lem7113994 (term411 _132718 x' _95042 _95043 _95044)). Qed.
Lemma lem7113996 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7113997 {_132718 : Type'} (x' : type714 _132718) (_95042 : _132718 -> real) (_95043 : real) (_95044 : _132718 -> Prop) : (term631 _132718 x' _95042 _95043 _95044) = (term632 _132718 x' _95042 _95043 _95044).
Proof. exact (MK_COMB (@lem7113996) (@lem7113995 _132718 x' _95042 _95043 _95044)). Qed.
Lemma lem7113999 (a : Prop) (b : Prop) : (term557 a b) = (term558 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7114000 {_132718 : Type'} (_95042 : _132718 -> real) (_95043 : real) (_95045 : _132718) (_95044 : _132718 -> Prop) : (term633 _132718 _95042 _95043 _95045 _95044) = (term634 _132718 _95042 _95043 _95045 _95044).
Proof. exact (@lem7113999 (term396 _132718 _95044 _95042 _95043) (term383 _132718 _95045 _95044)). Qed.
Lemma lem7114002 (a : Prop) : (term561 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7114003 {_132718 : Type'} (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95043 : real) : (term566 _132718 _95044 _95042 _95043) = (term395 _132718 _95044 _95042 _95043).
Proof. exact (@lem7114002 (term395 _132718 _95044 _95042 _95043)). Qed.
Lemma lem7114004 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7114005 {_132718 : Type'} (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95043 : real) : (term567 _132718 _95044 _95042 _95043) = (term568 _132718 _95044 _95042 _95043).
Proof. exact (MK_COMB (@lem7114004) (@lem7114003 _132718 _95044 _95042 _95043)). Qed.
Lemma lem7114007 (a : Prop) : (term561 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7114008 {_132718 : Type'} (_95045 : _132718) (_95044 : _132718 -> Prop) : (term571 _132718 _95045 _95044) = (term381 _132718 _95045 _95044).
Proof. exact (@lem7114007 (term381 _132718 _95045 _95044)). Qed.
Lemma lem7114009 {_132718 : Type'} (_95042 : _132718 -> real) (_95043 : real) (_95045 : _132718) (_95044 : _132718 -> Prop) : (term634 _132718 _95042 _95043 _95045 _95044) = (term635 _132718 _95042 _95043 _95045 _95044).
Proof. exact (MK_COMB (@lem7114005 _132718 _95044 _95042 _95043) (@lem7114008 _132718 _95045 _95044)). Qed.
Lemma lem7114010 {_132718 : Type'} (_95042 : _132718 -> real) (_95043 : real) (_95045 : _132718) (_95044 : _132718 -> Prop) : (term633 _132718 _95042 _95043 _95045 _95044) = (term635 _132718 _95042 _95043 _95045 _95044).
Proof. exact (TRANS (@lem7114000 _132718 _95042 _95043 _95045 _95044) (@lem7114009 _132718 _95042 _95043 _95045 _95044)). Qed.
Lemma lem7114011 {_132718 : Type'} (x' : type714 _132718) (_95042 : _132718 -> real) (_95043 : real) (_95045 : _132718) (_95044 : _132718 -> Prop) : (term628 _132718 x' _95042 _95043 _95045 _95044) = (term636 _132718 x' _95042 _95043 _95045 _95044).
Proof. exact (MK_COMB (@lem7113997 _132718 x' _95042 _95043 _95044) (@lem7114010 _132718 _95042 _95043 _95045 _95044)). Qed.
Lemma lem7114012 {_132718 : Type'} (x' : type714 _132718) (_95042 : _132718 -> real) (_95043 : real) (_95045 : _132718) (_95044 : _132718 -> Prop) : (term627 _132718 x' _95042 _95043 _95045 _95044) = (term636 _132718 x' _95042 _95043 _95045 _95044).
Proof. exact (TRANS (@lem7113992 _132718 x' _95042 _95043 _95045 _95044) (@lem7114011 _132718 x' _95042 _95043 _95045 _95044)). Qed.
Lemma lem7114013 {_132718 : Type'} (x' : type714 _132718) (_95042 : _132718 -> real) (_95043 : real) (_95045 : _132718) (_95044 : _132718 -> Prop) : (term626 _132718 x' _95042 _95043 _95045 _95044) = (term637 _132718 x' _95042 _95043 _95045 _95044).
Proof. exact (MK_COMB (@lem7113989 _132718 _95044) (@lem7114012 _132718 x' _95042 _95043 _95045 _95044)). Qed.
Lemma lem7114014 {_132718 : Type'} (x' : type714 _132718) (_95042 : _132718 -> real) (_95043 : real) (_95045 : _132718) (_95044 : _132718 -> Prop) : (term625 _132718 x' _95042 _95043 _95045 _95044) = (term637 _132718 x' _95042 _95043 _95045 _95044).
Proof. exact (TRANS (@lem7113984 _132718 x' _95042 _95043 _95045 _95044) (@lem7114013 _132718 x' _95042 _95043 _95045 _95044)). Qed.
Lemma lem7114015 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7114016 {_132718 : Type'} (x' : type714 _132718) (_95042 : _132718 -> real) (_95043 : real) (_95045 : _132718) (_95044 : _132718 -> Prop) : (term638 _132718 x' _95042 _95043 _95045 _95044) = (term639 _132718 x' _95042 _95043 _95045 _95044).
Proof. exact (MK_COMB (@lem7114015) (@lem7114014 _132718 x' _95042 _95043 _95045 _95044)). Qed.
Lemma lem7114017 {_132718 : Type'} (_95042 : _132718 -> real) (_95045 : _132718) (_95043 : real) : (term380 _132718 _95042 _95045 _95043) = (term380 _132718 _95042 _95045 _95043).
Proof. exact (eq_refl (term380 _132718 _95042 _95045 _95043)). Qed.
Lemma lem7114018 {_132718 : Type'} (x' : type714 _132718) (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95045 : _132718) (_95043 : real) : (term624 _132718 x' _95044 _95042 _95045 _95043) = (term640 _132718 x' _95044 _95042 _95045 _95043).
Proof. exact (MK_COMB (@lem7114016 _132718 x' _95042 _95043 _95045 _95044) (@lem7114017 _132718 _95042 _95045 _95043)). Qed.
Lemma lem7114019 {_132718 : Type'} (x' : type714 _132718) (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95045 : _132718) (_95043 : real) : (term623 _132718 x' _95042 _95043 _95045 _95044) = (term640 _132718 x' _95044 _95042 _95045 _95043).
Proof. exact (TRANS (@lem7113981 _132718 x' _95044 _95042 _95045 _95043) (@lem7114018 _132718 x' _95044 _95042 _95045 _95043)). Qed.
Lemma lem7114021 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term144 _132718 s f x'''') : term641 _132718 f x'''' s.
Proof. exact (conj (@lem7113696 _132718 s f x'''' h1) (@lem7113703 _132718 s f x'''' h1)). Qed.
Lemma lem7114022 {_132718 : Type'} (x' : type714 _132718) (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term371 _132718 x') (h2 : term455 _132718 f x'''') (h3 : term144 _132718 s f x'''') : term642 _132718 x' f x'''' s.
Proof. exact (conj (@lem7113689 _132718 x' s f x'''' h1 h2 h3) (@lem7114021 _132718 s f x'''' h3)). Qed.
Lemma lem7114023 {_132718 : Type'} (x' : type714 _132718) (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term371 _132718 x') (h2 : term455 _132718 f x'''') (h3 : term144 _132718 s f x'''') : term643 _132718 x' f x'''' s.
Proof. exact (conj (@lem7113305 _132718 s f x'''' h3) (@lem7114022 _132718 x' s f x'''' h1 h2 h3)). Qed.
Lemma lem7114025 {_132718 : Type'} (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95045 : _132718) (_95043 : real) (x' : type714 _132718) (h1 : term371 _132718 x') : term640 _132718 x' _95044 _95042 _95045 _95043.
Proof. exact (EQ_MP (@lem7114019 _132718 x' _95044 _95042 _95045 _95043) (@lem7113978 _132718 _95042 _95043 _95045 _95044 x' h1)). Qed.
Lemma lem7114026 {_132718 : Type'} (_95044 : _132718 -> Prop) (_95042 : _132718 -> real) (_95045 : _132718) (_95043 : real) (x' : type714 _132718) (h1 : term371 _132718 x') : term640 _132718 x' _95044 _95042 _95045 _95043.
Proof. exact (@lem7114025 _132718 _95044 _95042 _95045 _95043 x' h1). Qed.
Lemma lem7114027 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (x' : type714 _132718) (h1 : term371 _132718 x') : term644 _132718 x' s f x''''.
Proof. exact (@lem7114026 _132718 s f x'''' term398 x' h1). Qed.
Lemma lem7114030 {_132718 : Type'} (x' : type714 _132718) (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term371 _132718 x') (h2 : term455 _132718 f x'''') (h3 : term144 _132718 s f x'''') : term453 _132718 f x''''.
Proof. exact (@lem7114027 _132718 s f x'''' x' h1 (@lem7114023 _132718 x' s f x'''' h1 h2 h3)). Qed.
Lemma lem7114031 {_132718 : Type'} (x' : type714 _132718) (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term371 _132718 x') (h2 : term144 _132718 s f x'''') : term645 _132718 f x''''.
Proof. exact (fun h0 : term455 _132718 f x'''' => @lem7114030 _132718 x' s f x'''' h1 h0 h2). Qed.
Lemma lem7114033 (p : Prop) : (term534 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7114034 {_132718 : Type'} (f : _132718 -> real) (x'''' : _132718) : (term645 _132718 f x'''') = (term453 _132718 f x'''').
Proof. exact (@lem7114033 (term453 _132718 f x'''')). Qed.
Lemma lem7114035 {_132718 : Type'} (x' : type714 _132718) (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term371 _132718 x') (h2 : term144 _132718 s f x'''') : term453 _132718 f x''''.
Proof. exact (EQ_MP (@lem7114034 _132718 f x'''') (@lem7114031 _132718 x' s f x'''' h1 h2)). Qed.
Lemma lem7114038 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7114040 {_132718 : Type'} (f : _132718 -> real) (x'''' : _132718) : (term455 _132718 f x'''') = (term646 _132718 f x'''').
Proof. exact (@lem7114038 (term453 _132718 f x'''')). Qed.
Lemma lem7114043 {_132718 : Type'} (f : _132718 -> real) (x'''' : _132718) (h1 : term455 _132718 f x'''') : term646 _132718 f x''''.
Proof. exact (EQ_MP (@lem7114040 _132718 f x'''') (@lem7113058 _132718 f x'''' h1)). Qed.
Lemma lem7114046 {_132718 : Type'} (x' : type714 _132718) (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term371 _132718 x') (h2 : term455 _132718 f x'''') (h3 : term144 _132718 s f x'''') : False.
Proof. exact (@lem7114043 _132718 f x'''' h2 (@lem7114035 _132718 x' s f x'''' h1 h3)). Qed.
Lemma lem7114047 {_132718 : Type'} (x' : type714 _132718) (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term371 _132718 x') (h2 : term455 _132718 f x'''') (h3 : term144 _132718 s f x'''') : term647.
Proof. exact (fun h0 : ~ False => @lem7114046 _132718 x' s f x'''' h1 h2 h3). Qed.
Lemma lem7114049 (p : Prop) : (term534 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7114050 : term647 = False.
Proof. exact (@lem7114049 False). Qed.
Lemma lem7114051 {_132718 : Type'} (x' : type714 _132718) (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term371 _132718 x') (h2 : term455 _132718 f x'''') (h3 : term144 _132718 s f x'''') : False.
Proof. exact (EQ_MP (@lem7114050) (@lem7114047 _132718 x' s f x'''' h1 h2 h3)). Qed.
Lemma lem7114053 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term144 _132718 s f x'''') : term381 _132718 x'''' s.
Proof. exact (proj1 (@lem7112407 _132718 s f x'''' h1)). Qed.
Lemma lem7114054 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term144 _132718 s f x'''') : term537 _132718 x'''' s.
Proof. exact (fun h0 : term383 _132718 x'''' s => @lem7114053 _132718 s f x'''' h1). Qed.
Lemma lem7114056 (p : Prop) : (term534 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7114057 {_132718 : Type'} (x'''' : _132718) (s : _132718 -> Prop) : (term537 _132718 x'''' s) = (term381 _132718 x'''' s).
Proof. exact (@lem7114056 (term381 _132718 x'''' s)). Qed.
Lemma lem7114058 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term144 _132718 s f x'''') : term381 _132718 x'''' s.
Proof. exact (EQ_MP (@lem7114057 _132718 x'''' s) (@lem7114054 _132718 s f x'''' h1)). Qed.
Lemma lem7114064 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7114065 {_132718 : Type'} (f : _132718 -> real) (_95063 : _132718) (s : _132718 -> Prop) : (term471 _132718 s f _95063) = (term587 _132718 f _95063 s).
Proof. exact (@lem7114064 (term448 _132718 f _95063) (term383 _132718 _95063 s)). Qed.
Lemma lem7114071 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7114072 {_132718 : Type'} (f : _132718 -> real) (_95063 : _132718) (s : _132718 -> Prop) : (term588 _132718 s f _95063) = (term589 _132718 f _95063 s).
Proof. exact (MK_COMB (@lem7114071) (@lem7114065 _132718 f _95063 s)). Qed.
Lemma lem7114078 {_132718 : Type'} (f : _132718 -> real) (_95063 : _132718) (s : _132718 -> Prop) : (term587 _132718 f _95063 s) = (term587 _132718 f _95063 s).
Proof. exact (eq_refl (term587 _132718 f _95063 s)). Qed.
Lemma lem7114079 {_132718 : Type'} (f : _132718 -> real) (_95063 : _132718) (s : _132718 -> Prop) : ((term471 _132718 s f _95063) = (term587 _132718 f _95063 s)) = ((term587 _132718 f _95063 s) = (term587 _132718 f _95063 s)).
Proof. exact (MK_COMB (@lem7114072 _132718 f _95063 s) (@lem7114078 _132718 f _95063 s)). Qed.
Lemma lem7114081 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7114082 (x : Prop) : (x = x) = True.
Proof. exact (@lem7114081 Prop x). Qed.
Lemma lem7114083 {_132718 : Type'} (f : _132718 -> real) (_95063 : _132718) (s : _132718 -> Prop) : ((term587 _132718 f _95063 s) = (term587 _132718 f _95063 s)) = True.
Proof. exact (@lem7114082 (term587 _132718 f _95063 s)). Qed.
Lemma lem7114084 {_132718 : Type'} (f : _132718 -> real) (_95063 : _132718) (s : _132718 -> Prop) : ((term471 _132718 s f _95063) = (term587 _132718 f _95063 s)) = True.
Proof. exact (TRANS (@lem7114079 _132718 f _95063 s) (@lem7114083 _132718 f _95063 s)). Qed.
Lemma lem7114085 {_132718 : Type'} (f : _132718 -> real) (_95063 : _132718) (s : _132718 -> Prop) : True = ((term471 _132718 s f _95063) = (term587 _132718 f _95063 s)).
Proof. exact (SYM (@lem7114084 _132718 f _95063 s)). Qed.
Lemma lem7114086 {_132718 : Type'} (f : _132718 -> real) (_95063 : _132718) (s : _132718 -> Prop) : (term471 _132718 s f _95063) = (term587 _132718 f _95063 s).
Proof. exact (EQ_MP (@lem7114085 _132718 f _95063 s) (@lem0)). Qed.
Lemma lem7114087 {_132718 : Type'} (_95063 : _132718) (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term144 _132718 s f x'''') : term587 _132718 f _95063 s.
Proof. exact (EQ_MP (@lem7114086 _132718 f _95063 s) (@lem7113180 _132718 _95063 s f x'''' h1)). Qed.
Lemma lem7114089 (b : Prop) (a : Prop) : (a \/ b) = (term555 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7114090 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (_95063 : _132718) : (term587 _132718 f _95063 s) = (term590 _132718 s f _95063).
Proof. exact (@lem7114089 (term383 _132718 _95063 s) (term448 _132718 f _95063)). Qed.
Lemma lem7114092 (a : Prop) : (term561 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7114093 {_132718 : Type'} (_95063 : _132718) (s : _132718 -> Prop) : (term571 _132718 _95063 s) = (term381 _132718 _95063 s).
Proof. exact (@lem7114092 (term381 _132718 _95063 s)). Qed.
Lemma lem7114094 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7114095 {_132718 : Type'} (_95063 : _132718) (s : _132718 -> Prop) : (term591 _132718 _95063 s) = (term592 _132718 _95063 s).
Proof. exact (MK_COMB (@lem7114094) (@lem7114093 _132718 _95063 s)). Qed.
Lemma lem7114096 {_132718 : Type'} (f : _132718 -> real) (_95063 : _132718) : (term448 _132718 f _95063) = (term448 _132718 f _95063).
Proof. exact (eq_refl (term448 _132718 f _95063)). Qed.
Lemma lem7114097 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (_95063 : _132718) : (term590 _132718 s f _95063) = (term593 _132718 s f _95063).
Proof. exact (MK_COMB (@lem7114095 _132718 _95063 s) (@lem7114096 _132718 f _95063)). Qed.
Lemma lem7114098 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (_95063 : _132718) : (term587 _132718 f _95063 s) = (term593 _132718 s f _95063).
Proof. exact (TRANS (@lem7114090 _132718 s f _95063) (@lem7114097 _132718 s f _95063)). Qed.
Lemma lem7114101 {_132718 : Type'} (_95063 : _132718) (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term144 _132718 s f x'''') : term593 _132718 s f _95063.
Proof. exact (EQ_MP (@lem7114098 _132718 s f _95063) (@lem7114087 _132718 _95063 s f x'''' h1)). Qed.
Lemma lem7114102 {_132718 : Type'} (_95063 : _132718) (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term144 _132718 s f x'''') : term593 _132718 s f _95063.
Proof. exact (@lem7114101 _132718 _95063 s f x'''' h1). Qed.
Lemma lem7114103 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term144 _132718 s f x'''') : term593 _132718 s f x''''.
Proof. exact (@lem7114102 _132718 x'''' s f x'''' h1). Qed.
Lemma lem7114106 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term144 _132718 s f x'''') : term448 _132718 f x''''.
Proof. exact (@lem7114103 _132718 s f x'''' h1 (@lem7114058 _132718 s f x'''' h1)). Qed.
Lemma lem7114107 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term144 _132718 s f x'''') : term648 _132718 f x''''.
Proof. exact (fun h0 : term450 _132718 f x'''' => @lem7114106 _132718 s f x'''' h1). Qed.
Lemma lem7114109 (p : Prop) : (term534 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7114110 {_132718 : Type'} (f : _132718 -> real) (x'''' : _132718) : (term648 _132718 f x'''') = (term448 _132718 f x'''').
Proof. exact (@lem7114109 (term448 _132718 f x'''')). Qed.
Lemma lem7114111 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term144 _132718 s f x'''') : term448 _132718 f x''''.
Proof. exact (EQ_MP (@lem7114110 _132718 f x'''') (@lem7114107 _132718 s f x'''' h1)). Qed.
Lemma lem7114114 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7114116 {_132718 : Type'} (f : _132718 -> real) (x'''' : _132718) : (term450 _132718 f x'''') = (term649 _132718 f x'''').
Proof. exact (@lem7114114 (term448 _132718 f x'''')). Qed.
Lemma lem7114119 {_132718 : Type'} (f : _132718 -> real) (x'''' : _132718) (h1 : term450 _132718 f x'''') : term649 _132718 f x''''.
Proof. exact (EQ_MP (@lem7114116 _132718 f x'''') (@lem7113186 _132718 f x'''' h1)). Qed.
Lemma lem7114122 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term450 _132718 f x'''') (h2 : term144 _132718 s f x'''') : False.
Proof. exact (@lem7114119 _132718 f x'''' h1 (@lem7114111 _132718 s f x'''' h2)). Qed.
Lemma lem7114123 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term450 _132718 f x'''') (h2 : term144 _132718 s f x'''') : term647.
Proof. exact (fun h0 : ~ False => @lem7114122 _132718 s f x'''' h1 h2). Qed.
Lemma lem7114125 (p : Prop) : (term534 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7114126 : term647 = False.
Proof. exact (@lem7114125 False). Qed.
Lemma lem7114127 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term450 _132718 f x'''') (h2 : term144 _132718 s f x'''') : False.
Proof. exact (EQ_MP (@lem7114126) (@lem7114123 _132718 s f x'''' h1 h2)). Qed.
Lemma lem7114128 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term450 _132718 f x'''') (h2 : term144 _132718 s f x'''') : (term450 _132718 f x'''') = False.
Proof. exact (prop_ext (fun h3 : term450 _132718 f x'''' => @lem7114127 _132718 s f x'''' h1 h2) (fun h3 : False => @lem7113186 _132718 f x'''' h1)). Qed.
Lemma lem7114129 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term450 _132718 f x'''') (h2 : term144 _132718 s f x'''') : False.
Proof. exact (EQ_MP (@lem7114128 _132718 s f x'''' h1 h2) (@lem7113186 _132718 f x'''' h1)). Qed.
Lemma lem7114130 {_132718 : Type'} (x' : type714 _132718) (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term371 _132718 x') (h2 : term455 _132718 f x'''') (h3 : term144 _132718 s f x'''') : (term455 _132718 f x'''') = False.
Proof. exact (prop_ext (fun h4 : term455 _132718 f x'''' => @lem7114051 _132718 x' s f x'''' h1 h2 h3) (fun h4 : False => @lem7113058 _132718 f x'''' h2)). Qed.
Lemma lem7114131 {_132718 : Type'} (x' : type714 _132718) (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term371 _132718 x') (h2 : term455 _132718 f x'''') (h3 : term144 _132718 s f x'''') : False.
Proof. exact (EQ_MP (@lem7114130 _132718 x' s f x'''' h1 h2 h3) (@lem7113058 _132718 f x'''' h2)). Qed.
Lemma lem7114132 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term450 _132718 f x'''') (h2 : term144 _132718 s f x'''') : (term450 _132718 f x'''') = False.
Proof. exact (prop_ext (fun h3 : term450 _132718 f x'''' => @lem7114129 _132718 s f x'''' h1 h2) (fun h3 : False => @lem7112948 _132718 f x'''' h1)). Qed.
Lemma lem7114133 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term450 _132718 f x'''') (h2 : term144 _132718 s f x'''') : False.
Proof. exact (EQ_MP (@lem7114132 _132718 s f x'''' h1 h2) (@lem7112948 _132718 f x'''' h1)). Qed.
Lemma lem7114134 {_132718 : Type'} (x' : type714 _132718) (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term371 _132718 x') (h2 : term455 _132718 f x'''') (h3 : term144 _132718 s f x'''') : (term455 _132718 f x'''') = False.
Proof. exact (prop_ext (fun h4 : term455 _132718 f x'''' => @lem7114131 _132718 x' s f x'''' h1 h2 h3) (fun h4 : False => @lem7112683 _132718 f x'''' h2)). Qed.
Lemma lem7114135 {_132718 : Type'} (x' : type714 _132718) (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term371 _132718 x') (h2 : term455 _132718 f x'''') (h3 : term144 _132718 s f x'''') : False.
Proof. exact (EQ_MP (@lem7114134 _132718 x' s f x'''' h1 h2 h3) (@lem7112683 _132718 f x'''' h2)). Qed.
Lemma lem7114136 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term450 _132718 f x'''') (h2 : term144 _132718 s f x'''') : (term450 _132718 f x'''') = False.
Proof. exact (prop_ext (fun h3 : term450 _132718 f x'''' => @lem7114133 _132718 s f x'''' h1 h2) (fun h3 : False => @lem7112948 _132718 f x'''' h1)). Qed.
Lemma lem7114137 {_132718 : Type'} (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term450 _132718 f x'''') (h2 : term144 _132718 s f x'''') : False.
Proof. exact (EQ_MP (@lem7114136 _132718 s f x'''' h1 h2) (@lem7112948 _132718 f x'''' h1)). Qed.
Lemma lem7114138 {_132718 : Type'} (x' : type714 _132718) (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term371 _132718 x') (h2 : term455 _132718 f x'''') (h3 : term144 _132718 s f x'''') : (term455 _132718 f x'''') = False.
Proof. exact (prop_ext (fun h4 : term455 _132718 f x'''' => @lem7114135 _132718 x' s f x'''' h1 h2 h3) (fun h4 : False => @lem7112683 _132718 f x'''' h2)). Qed.
Lemma lem7114139 {_132718 : Type'} (x' : type714 _132718) (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term371 _132718 x') (h2 : term455 _132718 f x'''') (h3 : term144 _132718 s f x'''') : False.
Proof. exact (EQ_MP (@lem7114138 _132718 x' s f x'''' h1 h2 h3) (@lem7112683 _132718 f x'''' h2)). Qed.
Lemma lem7114140 {_132718 : Type'} (x' : type714 _132718) (s : _132718 -> Prop) (f : _132718 -> real) (x'''' : _132718) (h1 : term371 _132718 x') (h2 : term144 _132718 s f x'''') : False.
Proof. exact (or_elim (@lem7112409 _132718 s f x'''' h2) (fun h0 : term455 _132718 f x'''' => @lem7114139 _132718 x' s f x'''' h1 h0 h2) (fun h0 : term450 _132718 f x'''' => @lem7114137 _132718 s f x'''' h0 h2)). Qed.
Lemma lem7114141 {_132718 : Type'} (x' : type714 _132718) (s : _132718 -> Prop) (f : _132718 -> real) (h1 : term371 _132718 x') (h2 : term147 _132718 s f) : False.
Proof. exact (ex_elim (@lem7111383 _132718 s f h2) (fun x'''' : _132718 => fun h0 : term146 _132718 s f x'''' => @lem7114140 _132718 x' s f x'''' h1 h0)). Qed.
Lemma lem7114142 {_132718 : Type'} (x' : type714 _132718) (f : _132718 -> real) (h1 : term371 _132718 x') (h2 : term149 _132718 f) : False.
Proof. exact (ex_elim (@lem7111382 _132718 f h2) (fun s : _132718 -> Prop => fun h0 : term148 _132718 f s => @lem7114141 _132718 x' s f h1 h0)). Qed.
Lemma lem7114143 {_132718 : Type'} (x' : type714 _132718) (h1 : term371 _132718 x') (h2 : term49 _132718) : False.
Proof. exact (ex_elim (@lem7110153 _132718 h2) (fun f : _132718 -> real => fun h0 : term150 _132718 f => @lem7114142 _132718 x' f h1 h0)). Qed.
Lemma lem7114144 {_132718 : Type'} (x' : type714 _132718) (h1 : term7 _132718) (h2 : term371 _132718 x') (h3 : term49 _132718) : False.
Proof. exact (ex_elim (@lem7110378 _132718 h1) (fun x''' : type710 _132718 => fun h0 : term236 _132718 x''' => @lem7114143 _132718 x' h2 h3)). Qed.
Lemma lem7114145 {_132718 A : Type'} (x' : type714 _132718) (h1 : term7 _132718) (h2 : term371 _132718 x') (h3 : term7 A) (h4 : term49 _132718) : False.
Proof. exact (ex_elim (@lem7110603 A h3) (fun x'' : type710 A => fun h0 : term236 A x'' => @lem7114144 _132718 x' h1 h2 h4)). Qed.
Lemma lem7114146 {_132718 A : Type'} (h1 : term7 _132718) (h2 : term50 _132718) (h3 : term7 A) (h4 : term49 _132718) : False.
Proof. exact (ex_elim (@lem7110990 _132718 h2) (fun x' : type714 _132718 => fun h0 : term373 _132718 x' => @lem7114145 _132718 A x' h1 h0 h3 h4)). Qed.
Lemma lem7114147 {_132718 A : Type'} (h1 : term7 _132718) (h2 : term50 _132718) (h3 : term7 A) (h4 : term50 A) (h5 : term49 _132718) : False.
Proof. exact (ex_elim (@lem7111377 A h4) (fun x : type714 A => fun h0 : term373 A x => @lem7114146 _132718 A h1 h2 h3 h5)). Qed.
Lemma lem7114148 {_132718 A : Type'} (h1 : term7 _132718) (h2 : term50 _132718) (h3 : term7 A) (h4 : term49 _132718) : term55 A.
Proof. exact (fun h0 : term50 A => @lem7114147 _132718 A h1 h2 h3 h0 h4). Qed.
Lemma lem7114149 {A : Type'} : (term55 A) = (term56 A).
Proof. exact (@lem69 (term50 A)). Qed.
Lemma lem7114150 {_132718 A : Type'} (h1 : term7 _132718) (h2 : term50 _132718) (h3 : term7 A) (h4 : term49 _132718) : term56 A.
Proof. exact (EQ_MP (@lem7114149 A) (@lem7114148 _132718 A h1 h2 h3 h4)). Qed.
Lemma lem7114151 {_132718 A : Type'} (h1 : term7 _132718) (h2 : term7 A) (h3 : term49 _132718) : term59 _132718 A.
Proof. exact (fun h0 : term50 _132718 => @lem7114150 _132718 A h1 h0 h2 h3). Qed.
Lemma lem7114152 {_132718 A : Type'} (h1 : term7 _132718) (h2 : term49 _132718) : term62 _132718 A.
Proof. exact (fun h0 : term7 A => @lem7114151 _132718 A h1 h0 h2). Qed.
Lemma lem7114153 {_132718 A : Type'} (h1 : term49 _132718) : term64 _132718 A.
Proof. exact (fun h0 : term7 _132718 => @lem7114152 _132718 A h0 h1). Qed.
Lemma lem7114154 {_132718 A : Type'} : term66 _132718 A.
Proof. exact (fun h0 : term49 _132718 => @lem7114153 _132718 A h0). Qed.
Lemma lem7114155 {_132718 A : Type'} : term51 _132718 A.
Proof. exact (EQ_MP (@lem7109900 _132718 A) (@lem7114154 _132718 A)). Qed.
Lemma lem7114157 {_132718 A : Type'} : term51 _132718 A.
Proof. exact (@lem7109408 _132718 A (@lem7114155 _132718 A)). Qed.
Lemma lem7114158 {_132718 A : Type'} (h1 : term49 _132718) : term63 _132718 A.
Proof. exact (@lem7114157 _132718 A (@lem7109385 _132718 h1)). Qed.
Lemma lem7114159 {_132718 A : Type'} (h1 : term49 _132718) : term61 _132718 A.
Proof. exact (@lem7114158 _132718 A h1 (@lem7109389 _132718)). Qed.
Lemma lem7114160 {_132718 A : Type'} (h1 : term49 _132718) : term58 _132718 A.
Proof. exact (@lem7114159 _132718 A h1 (@lem7109390 A)). Qed.
Lemma lem7114161 {_132718 A : Type'} (h1 : term49 _132718) : term55 A.
Proof. exact (@lem7114160 _132718 A h1 (@lem7109386 _132718)). Qed.
Lemma lem7114162 {_132718 : Type'} (h1 : term49 _132718) : False.
Proof. exact (@lem7114161 _132718 Prop h1 (@lem7109270 Prop)). Qed.
Lemma lem7114163 {_132718 : Type'} (h1 : term49 _132718) : (term49 _132718) = False.
Proof. exact (prop_ext (fun h2 : term49 _132718 => @lem7114162 _132718 h1) (fun h2 : False => @lem7109385 _132718 h1)). Qed.
Lemma lem7114164 {_132718 : Type'} (h1 : term49 _132718) : False.
Proof. exact (EQ_MP (@lem7114163 _132718 h1) (@lem7109385 _132718 h1)). Qed.
Lemma lem7114165 {_132718 : Type'} : term48 _132718.
Proof. exact (fun h0 : term49 _132718 => @lem7114164 _132718 h0). Qed.
Lemma lem7114166 {_132718 : Type'} : term46 _132718.
Proof. exact (EQ_MP (@lem7109384 _132718) (@lem7114165 _132718)). Qed.
Lemma lem7114167 {_132718 : Type'} : term45 _132718.
Proof. exact (EQ_MP (@lem7109380 _132718) (@lem7114166 _132718)). Qed.
