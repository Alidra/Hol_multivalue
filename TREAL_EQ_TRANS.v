Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import TREAL_EQ_TRANS_term_abbrevs.
Require Import FORALL_PAIR_THM_spec.
Require Import HREAL_EQ_ADD_LCANCEL_spec.
Require Import HREAL_EQ_ADD_RCANCEL_spec.
Require Import thm1320004_spec.
Require Import thm1320203_spec.
Require Import treal_eq_spec.
Lemma lem1326360 (x : hreal) : term0 x.
Proof. exact (@lem1320004 x). Qed.
Lemma lem1326361 (x : hreal) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1326362 (x : hreal) : term1 x.
Proof. exact (EQ_MP (@lem1326361 x) (@lem1326360 x)). Qed.
Lemma lem1326363 (x : hreal) (y : hreal) : term2 x y.
Proof. exact (@lem1326362 x y). Qed.
Lemma lem1326364 (y : hreal) (x : hreal) : (term2 x y) = ((hreal_add x y) = (hreal_add y x)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1326366 (m : hreal) : term3 m.
Proof. exact (@lem1321459 m). Qed.
Lemma lem1326367 (m : hreal) : (term3 m) = (term4 m).
Proof. exact (eq_refl (term3 m)). Qed.
Lemma lem1326368 (m : hreal) : term4 m.
Proof. exact (EQ_MP (@lem1326367 m) (@lem1326366 m)). Qed.
Lemma lem1326369 (m : hreal) (n : hreal) : term5 m n.
Proof. exact (@lem1326368 m n). Qed.
Lemma lem1326370 (m : hreal) (n : hreal) : (term5 m n) = (term6 m n).
Proof. exact (eq_refl (term5 m n)). Qed.
Lemma lem1326371 (m : hreal) (n : hreal) : term6 m n.
Proof. exact (EQ_MP (@lem1326370 m n) (@lem1326369 m n)). Qed.
Lemma lem1326372 (m : hreal) (n : hreal) (p : hreal) : term7 m n p.
Proof. exact (@lem1326371 m n p). Qed.
Lemma lem1326373 (p : hreal) (m : hreal) (n : hreal) : (term7 m n p) = (((hreal_add m p) = (hreal_add n p)) = (m = n)).
Proof. exact (eq_refl (term7 m n p)). Qed.
Lemma lem1326375 (x : hreal) : term8 x.
Proof. exact (@lem1320203 x). Qed.
Lemma lem1326376 (x : hreal) : (term8 x) = (term9 x).
Proof. exact (eq_refl (term8 x)). Qed.
Lemma lem1326377 (x : hreal) : term9 x.
Proof. exact (EQ_MP (@lem1326376 x) (@lem1326375 x)). Qed.
Lemma lem1326378 (x : hreal) (y : hreal) : term10 x y.
Proof. exact (@lem1326377 x y). Qed.
Lemma lem1326379 (x : hreal) (y : hreal) : (term10 x y) = (term11 x y).
Proof. exact (eq_refl (term10 x y)). Qed.
Lemma lem1326380 (x : hreal) (y : hreal) : term11 x y.
Proof. exact (EQ_MP (@lem1326379 x y) (@lem1326378 x y)). Qed.
Lemma lem1326381 (x : hreal) (y : hreal) (z : hreal) : term12 x y z.
Proof. exact (@lem1326380 x y z). Qed.
Lemma lem1326382 (x : hreal) (y : hreal) (z : hreal) : (term12 x y z) = ((term13 x y z) = (term14 x y z)).
Proof. exact (eq_refl (term12 x y z)). Qed.
Lemma lem1326387 (x : hreal) (y : hreal) (z : hreal) (h1 : (term13 x y z) = (term14 x y z)) : (term13 x y z) = (term14 x y z).
Proof. exact (h1). Qed.
Lemma lem1326388 (x : hreal) (y : hreal) (z : hreal) (h1 : (term13 x y z) = (term14 x y z)) : (term14 x y z) = (term13 x y z).
Proof. exact (SYM (@lem1326387 x y z h1)). Qed.
Lemma lem1326389 (x : hreal) (y : hreal) (z : hreal) (h1 : (term14 x y z) = (term13 x y z)) : (term14 x y z) = (term13 x y z).
Proof. exact (h1). Qed.
Lemma lem1326390 (x : hreal) (y : hreal) (z : hreal) (h1 : (term14 x y z) = (term13 x y z)) : (term13 x y z) = (term14 x y z).
Proof. exact (SYM (@lem1326389 x y z h1)). Qed.
Lemma lem1326391 (x : hreal) (y : hreal) (z : hreal) : ((term13 x y z) = (term14 x y z)) = ((term14 x y z) = (term13 x y z)).
Proof. exact (prop_ext (fun h1 : (term13 x y z) = (term14 x y z) => @lem1326388 x y z h1) (fun h1 : (term14 x y z) = (term13 x y z) => @lem1326390 x y z h1)). Qed.
Lemma lem1326392 (x : hreal) (y : hreal) : (term15 x y) = (term16 x y).
Proof. exact (fun_ext (fun z : hreal => @lem1326391 x y z)). Qed.
Lemma lem1326393 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1326394 (x : hreal) (y : hreal) : (term11 x y) = (term17 x y).
Proof. exact (MK_COMB (@lem1326393) (@lem1326392 x y)). Qed.
Lemma lem1326395 (x : hreal) : (term18 x) = (term19 x).
Proof. exact (fun_ext (fun y : hreal => @lem1326394 x y)). Qed.
Lemma lem1326396 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1326397 (x : hreal) : (term9 x) = (term20 x).
Proof. exact (MK_COMB (@lem1326396) (@lem1326395 x)). Qed.
Lemma lem1326398 : term21 = term22.
Proof. exact (fun_ext (fun x : hreal => @lem1326397 x)). Qed.
Lemma lem1326399 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1326400 : term23 = term24.
Proof. exact (MK_COMB (@lem1326399) (@lem1326398)). Qed.
Lemma lem1326401 : term24.
Proof. exact (EQ_MP (@lem1326400) (@lem1320203)). Qed.
Lemma lem1326402 (m : hreal) : term25 m.
Proof. exact (@lem1321346 m). Qed.
Lemma lem1326403 (m : hreal) : (term25 m) = (term26 m).
Proof. exact (eq_refl (term25 m)). Qed.
Lemma lem1326404 (m : hreal) : term26 m.
Proof. exact (EQ_MP (@lem1326403 m) (@lem1326402 m)). Qed.
Lemma lem1326405 (m : hreal) (n : hreal) : term27 m n.
Proof. exact (@lem1326404 m n). Qed.
Lemma lem1326406 (m : hreal) (n : hreal) : (term27 m n) = (term28 m n).
Proof. exact (eq_refl (term27 m n)). Qed.
Lemma lem1326407 (m : hreal) (n : hreal) : term28 m n.
Proof. exact (EQ_MP (@lem1326406 m n) (@lem1326405 m n)). Qed.
Lemma lem1326408 (m : hreal) (n : hreal) (p : hreal) : term29 m n p.
Proof. exact (@lem1326407 m n p). Qed.
Lemma lem1326409 (m : hreal) (n : hreal) (p : hreal) : (term29 m n p) = (((hreal_add m n) = (hreal_add m p)) = (n = p)).
Proof. exact (eq_refl (term29 m n p)). Qed.
Lemma lem1326411 (x : hreal) : term30 x.
Proof. exact (@lem1326401 x). Qed.
Lemma lem1326412 (x : hreal) : (term30 x) = (term20 x).
Proof. exact (eq_refl (term30 x)). Qed.
Lemma lem1326413 (x : hreal) : term20 x.
Proof. exact (EQ_MP (@lem1326412 x) (@lem1326411 x)). Qed.
Lemma lem1326414 (x : hreal) (y : hreal) : term31 x y.
Proof. exact (@lem1326413 x y). Qed.
Lemma lem1326415 (x : hreal) (y : hreal) : (term31 x y) = (term17 x y).
Proof. exact (eq_refl (term31 x y)). Qed.
Lemma lem1326416 (x : hreal) (y : hreal) : term17 x y.
Proof. exact (EQ_MP (@lem1326415 x y) (@lem1326414 x y)). Qed.
Lemma lem1326417 (x : hreal) (y : hreal) (z : hreal) : term32 x y z.
Proof. exact (@lem1326416 x y z). Qed.
Lemma lem1326418 (x : hreal) (y : hreal) (z : hreal) : (term32 x y z) = ((term14 x y z) = (term13 x y z)).
Proof. exact (eq_refl (term32 x y z)). Qed.
Lemma lem1326420 (x : hreal) : term0 x.
Proof. exact (@lem1320004 x). Qed.
Lemma lem1326421 (x : hreal) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1326422 (x : hreal) : term1 x.
Proof. exact (EQ_MP (@lem1326421 x) (@lem1326420 x)). Qed.
Lemma lem1326423 (x : hreal) (y : hreal) : term2 x y.
Proof. exact (@lem1326422 x y). Qed.
Lemma lem1326424 (y : hreal) (x : hreal) : (term2 x y) = ((hreal_add x y) = (hreal_add y x)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1326426 : hreal_add = hreal_add.
Proof. exact (eq_refl hreal_add). Qed.
Lemma lem1326427 (x1 : hreal) : term33 x1.
Proof. exact (@lem1326116 x1). Qed.
Lemma lem1326428 (x1 : hreal) : (term33 x1) = (term34 x1).
Proof. exact (eq_refl (term33 x1)). Qed.
Lemma lem1326429 (x1 : hreal) : term34 x1.
Proof. exact (EQ_MP (@lem1326428 x1) (@lem1326427 x1)). Qed.
Lemma lem1326430 (x1 : hreal) (y2 : hreal) : term35 x1 y2.
Proof. exact (@lem1326429 x1 y2). Qed.
Lemma lem1326431 (x1 : hreal) (y2 : hreal) : (term35 x1 y2) = (term36 x1 y2).
Proof. exact (eq_refl (term35 x1 y2)). Qed.
Lemma lem1326432 (x1 : hreal) (y2 : hreal) : term36 x1 y2.
Proof. exact (EQ_MP (@lem1326431 x1 y2) (@lem1326430 x1 y2)). Qed.
Lemma lem1326433 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term37 x1 y2 x2.
Proof. exact (@lem1326432 x1 y2 x2). Qed.
Lemma lem1326434 (x1 : hreal) (y2 : hreal) (x2 : hreal) : (term37 x1 y2 x2) = (term38 x1 y2 x2).
Proof. exact (eq_refl (term37 x1 y2 x2)). Qed.
Lemma lem1326435 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term38 x1 y2 x2.
Proof. exact (EQ_MP (@lem1326434 x1 y2 x2) (@lem1326433 x1 y2 x2)). Qed.
Lemma lem1326436 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : term39 x1 y2 x2 y1.
Proof. exact (@lem1326435 x1 y2 x2 y1). Qed.
Lemma lem1326437 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term39 x1 y2 x2 y1) = ((term40 x1 y1 x2 y2) = ((hreal_add x1 y2) = (hreal_add x2 y1))).
Proof. exact (eq_refl (term39 x1 y2 x2 y1)). Qed.
Lemma lem1326439 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term41 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem1326440 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term41 _5106 _5107 P) = ((term42 _5106 _5107 P) = (term43 _5106 _5107 P)).
Proof. exact (eq_refl (term41 _5106 _5107 P)). Qed.
Lemma lem1326447 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term42 _5106 _5107 P) = (term43 _5106 _5107 P).
Proof. exact (EQ_MP (@lem1326440 _5106 _5107 P) (@lem1326439 _5106 _5107 P)). Qed.
Lemma lem1326448 (P : type1233) : (term44 P) = (term45 P).
Proof. exact (@lem1326447 hreal hreal P). Qed.
Lemma lem1326449 : term46 = term47.
Proof. exact (@lem1326448 term48). Qed.
Lemma lem1326450 (x : prod hreal hreal) : (term49 x) = (term50 x).
Proof. exact (eq_refl (term49 x)). Qed.
Lemma lem1326451 : term51 = term48.
Proof. exact (fun_ext (fun x : prod hreal hreal => @lem1326450 x)). Qed.
Lemma lem1326452 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1326453 : term46 = term52.
Proof. exact (MK_COMB (@lem1326452) (@lem1326451)). Qed.
Lemma lem1326454 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1326455 : term53 = term54.
Proof. exact (MK_COMB (@lem1326454) (@lem1326453)). Qed.
Lemma lem1326456 (p1 : hreal) (p2 : hreal) : (term55 p1 p2) = (term56 p1 p2).
Proof. exact (eq_refl (term55 p1 p2)). Qed.
Lemma lem1326457 (p1 : hreal) : (term57 p1) = (term58 p1).
Proof. exact (fun_ext (fun p2 : hreal => @lem1326456 p1 p2)). Qed.
Lemma lem1326458 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1326459 (p1 : hreal) : (term59 p1) = (term60 p1).
Proof. exact (MK_COMB (@lem1326458) (@lem1326457 p1)). Qed.
Lemma lem1326460 : term61 = term62.
Proof. exact (fun_ext (fun p1 : hreal => @lem1326459 p1)). Qed.
Lemma lem1326461 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1326462 : term47 = term63.
Proof. exact (MK_COMB (@lem1326461) (@lem1326460)). Qed.
Lemma lem1326463 : (term46 = term47) = (term52 = term63).
Proof. exact (MK_COMB (@lem1326455) (@lem1326462)). Qed.
Lemma lem1326464 : term52 = term63.
Proof. exact (EQ_MP (@lem1326463) (@lem1326449)). Qed.
Lemma lem1326482 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term42 _5106 _5107 P) = (term43 _5106 _5107 P).
Proof. exact (EQ_MP (@lem1326440 _5106 _5107 P) (@lem1326439 _5106 _5107 P)). Qed.
Lemma lem1326483 (P : type1233) : (term44 P) = (term45 P).
Proof. exact (@lem1326482 hreal hreal P). Qed.
Lemma lem1326484 (p1 : hreal) (p2 : hreal) : (term64 p1 p2) = (term65 p1 p2).
Proof. exact (@lem1326483 (term66 p1 p2)). Qed.
Lemma lem1326485 (y : prod hreal hreal) (p1 : hreal) (p2 : hreal) : (term67 p1 p2 y) = (term68 y p1 p2).
Proof. exact (eq_refl (term67 p1 p2 y)). Qed.
Lemma lem1326486 (p1 : hreal) (p2 : hreal) : (term69 p1 p2) = (term66 p1 p2).
Proof. exact (fun_ext (fun y : prod hreal hreal => @lem1326485 y p1 p2)). Qed.
Lemma lem1326487 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1326488 (p1 : hreal) (p2 : hreal) : (term64 p1 p2) = (term56 p1 p2).
Proof. exact (MK_COMB (@lem1326487) (@lem1326486 p1 p2)). Qed.
Lemma lem1326489 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1326490 (p1 : hreal) (p2 : hreal) : (term70 p1 p2) = (term71 p1 p2).
Proof. exact (MK_COMB (@lem1326489) (@lem1326488 p1 p2)). Qed.
Lemma lem1326491 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : (term72 p1 p2 p1' p2') = (term73 p1' p2' p1 p2).
Proof. exact (eq_refl (term72 p1 p2 p1' p2')). Qed.
Lemma lem1326492 (p1' : hreal) (p1 : hreal) (p2 : hreal) : (term74 p1 p2 p1') = (term75 p1' p1 p2).
Proof. exact (fun_ext (fun p2' : hreal => @lem1326491 p1' p2' p1 p2)). Qed.
Lemma lem1326493 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1326494 (p1' : hreal) (p1 : hreal) (p2 : hreal) : (term76 p1 p2 p1') = (term77 p1' p1 p2).
Proof. exact (MK_COMB (@lem1326493) (@lem1326492 p1' p1 p2)). Qed.
Lemma lem1326495 (p1 : hreal) (p2 : hreal) : (term78 p1 p2) = (term79 p1 p2).
Proof. exact (fun_ext (fun p1' : hreal => @lem1326494 p1' p1 p2)). Qed.
Lemma lem1326496 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1326497 (p1 : hreal) (p2 : hreal) : (term65 p1 p2) = (term80 p1 p2).
Proof. exact (MK_COMB (@lem1326496) (@lem1326495 p1 p2)). Qed.
Lemma lem1326498 (p1 : hreal) (p2 : hreal) : ((term64 p1 p2) = (term65 p1 p2)) = ((term56 p1 p2) = (term80 p1 p2)).
Proof. exact (MK_COMB (@lem1326490 p1 p2) (@lem1326497 p1 p2)). Qed.
Lemma lem1326499 (p1 : hreal) (p2 : hreal) : (term56 p1 p2) = (term80 p1 p2).
Proof. exact (EQ_MP (@lem1326498 p1 p2) (@lem1326484 p1 p2)). Qed.
Lemma lem1326517 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term42 _5106 _5107 P) = (term43 _5106 _5107 P).
Proof. exact (EQ_MP (@lem1326440 _5106 _5107 P) (@lem1326439 _5106 _5107 P)). Qed.
Lemma lem1326518 (P : type1233) : (term44 P) = (term45 P).
Proof. exact (@lem1326517 hreal hreal P). Qed.
Lemma lem1326519 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : (term81 p1' p2' p1 p2) = (term82 p1' p2' p1 p2).
Proof. exact (@lem1326518 (term83 p1' p2' p1 p2)). Qed.
Lemma lem1326520 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) (z : prod hreal hreal) : (term84 p1' p2' p1 p2 z) = (term85 p1' p2' p1 p2 z).
Proof. exact (eq_refl (term84 p1' p2' p1 p2 z)). Qed.
Lemma lem1326521 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : (term86 p1' p2' p1 p2) = (term83 p1' p2' p1 p2).
Proof. exact (fun_ext (fun z : prod hreal hreal => @lem1326520 p1' p2' p1 p2 z)). Qed.
Lemma lem1326522 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1326523 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : (term81 p1' p2' p1 p2) = (term73 p1' p2' p1 p2).
Proof. exact (MK_COMB (@lem1326522) (@lem1326521 p1' p2' p1 p2)). Qed.
Lemma lem1326524 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1326525 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : (term87 p1' p2' p1 p2) = (term88 p1' p2' p1 p2).
Proof. exact (MK_COMB (@lem1326524) (@lem1326523 p1' p2' p1 p2)). Qed.
Lemma lem1326526 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) (p1'' : hreal) (p2'' : hreal) : (term89 p1' p2' p1 p2 p1'' p2'') = (term90 p1' p2' p1 p2 p1'' p2'').
Proof. exact (eq_refl (term89 p1' p2' p1 p2 p1'' p2'')). Qed.
Lemma lem1326527 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) (p1'' : hreal) : (term91 p1' p2' p1 p2 p1'') = (term92 p1' p2' p1 p2 p1'').
Proof. exact (fun_ext (fun p2'' : hreal => @lem1326526 p1' p2' p1 p2 p1'' p2'')). Qed.
Lemma lem1326528 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1326529 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) (p1'' : hreal) : (term93 p1' p2' p1 p2 p1'') = (term94 p1' p2' p1 p2 p1'').
Proof. exact (MK_COMB (@lem1326528) (@lem1326527 p1' p2' p1 p2 p1'')). Qed.
Lemma lem1326530 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : (term95 p1' p2' p1 p2) = (term96 p1' p2' p1 p2).
Proof. exact (fun_ext (fun p1'' : hreal => @lem1326529 p1' p2' p1 p2 p1'')). Qed.
Lemma lem1326531 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1326532 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : (term82 p1' p2' p1 p2) = (term97 p1' p2' p1 p2).
Proof. exact (MK_COMB (@lem1326531) (@lem1326530 p1' p2' p1 p2)). Qed.
Lemma lem1326533 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : ((term81 p1' p2' p1 p2) = (term82 p1' p2' p1 p2)) = ((term73 p1' p2' p1 p2) = (term97 p1' p2' p1 p2)).
Proof. exact (MK_COMB (@lem1326525 p1' p2' p1 p2) (@lem1326532 p1' p2' p1 p2)). Qed.
Lemma lem1326534 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : (term73 p1' p2' p1 p2) = (term97 p1' p2' p1 p2).
Proof. exact (EQ_MP (@lem1326533 p1' p2' p1 p2) (@lem1326519 p1' p2' p1 p2)). Qed.
Lemma lem1326552 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term40 x1 y1 x2 y2) = ((hreal_add x1 y2) = (hreal_add x2 y1)).
Proof. exact (EQ_MP (@lem1326437 x1 y2 x2 y1) (@lem1326436 x1 y2 x2 y1)). Qed.
Lemma lem1326553 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) : (term40 p1 p2 p1' p2') = ((hreal_add p1 p2') = (hreal_add p1' p2)).
Proof. exact (@lem1326552 p1 p2' p1' p2). Qed.
Lemma lem1326556 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1326557 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) : (term98 p1 p2 p1' p2') = (term99 p1 p2' p1' p2).
Proof. exact (MK_COMB (@lem1326556) (@lem1326553 p1 p2' p1' p2)). Qed.
Lemma lem1326559 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term40 x1 y1 x2 y2) = ((hreal_add x1 y2) = (hreal_add x2 y1)).
Proof. exact (EQ_MP (@lem1326437 x1 y2 x2 y1) (@lem1326436 x1 y2 x2 y1)). Qed.
Lemma lem1326560 (p1' : hreal) (p2'' : hreal) (p1'' : hreal) (p2' : hreal) : (term40 p1' p2' p1'' p2'') = ((hreal_add p1' p2'') = (hreal_add p1'' p2')).
Proof. exact (@lem1326559 p1' p2'' p1'' p2'). Qed.
Lemma lem1326563 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2'' : hreal) (p1'' : hreal) (p2' : hreal) : (term100 p1 p2 p1' p2' p1'' p2'') = (term101 p1 p2 p1' p2'' p1'' p2').
Proof. exact (MK_COMB (@lem1326557 p1 p2' p1' p2) (@lem1326560 p1' p2'' p1'' p2')). Qed.
Lemma lem1326566 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1326567 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2'' : hreal) (p1'' : hreal) (p2' : hreal) : (term102 p1 p2 p1' p2' p1'' p2'') = (term103 p1 p2 p1' p2'' p1'' p2').
Proof. exact (MK_COMB (@lem1326566) (@lem1326563 p1 p2 p1' p2'' p1'' p2')). Qed.
Lemma lem1326569 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term40 x1 y1 x2 y2) = ((hreal_add x1 y2) = (hreal_add x2 y1)).
Proof. exact (EQ_MP (@lem1326437 x1 y2 x2 y1) (@lem1326436 x1 y2 x2 y1)). Qed.
Lemma lem1326570 (p1 : hreal) (p2'' : hreal) (p1'' : hreal) (p2 : hreal) : (term40 p1 p2 p1'' p2'') = ((hreal_add p1 p2'') = (hreal_add p1'' p2)).
Proof. exact (@lem1326569 p1 p2'' p1'' p2). Qed.
Lemma lem1326573 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2'' : hreal) (p1'' : hreal) (p2 : hreal) : (term90 p1' p2' p1 p2 p1'' p2'') = (term104 p1' p2' p1 p2'' p1'' p2).
Proof. exact (MK_COMB (@lem1326567 p1 p2 p1' p2'' p1'' p2') (@lem1326570 p1 p2'' p1'' p2)). Qed.
Lemma lem1326576 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p1'' : hreal) (p2 : hreal) : (term92 p1' p2' p1 p2 p1'') = (term105 p1' p2' p1 p1'' p2).
Proof. exact (fun_ext (fun p2'' : hreal => @lem1326573 p1' p2' p1 p2'' p1'' p2)). Qed.
Lemma lem1326577 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1326578 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p1'' : hreal) (p2 : hreal) : (term94 p1' p2' p1 p2 p1'') = (term106 p1' p2' p1 p1'' p2).
Proof. exact (MK_COMB (@lem1326577) (@lem1326576 p1' p2' p1 p1'' p2)). Qed.
Lemma lem1326585 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : (term96 p1' p2' p1 p2) = (term107 p1' p2' p1 p2).
Proof. exact (fun_ext (fun p1'' : hreal => @lem1326578 p1' p2' p1 p1'' p2)). Qed.
Lemma lem1326586 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1326587 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : (term97 p1' p2' p1 p2) = (term108 p1' p2' p1 p2).
Proof. exact (MK_COMB (@lem1326586) (@lem1326585 p1' p2' p1 p2)). Qed.
Lemma lem1326594 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : (term73 p1' p2' p1 p2) = (term108 p1' p2' p1 p2).
Proof. exact (TRANS (@lem1326534 p1' p2' p1 p2) (@lem1326587 p1' p2' p1 p2)). Qed.
Lemma lem1326595 (p1' : hreal) (p1 : hreal) (p2 : hreal) : (term75 p1' p1 p2) = (term109 p1' p1 p2).
Proof. exact (fun_ext (fun p2' : hreal => @lem1326594 p1' p2' p1 p2)). Qed.
Lemma lem1326596 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1326597 (p1' : hreal) (p1 : hreal) (p2 : hreal) : (term77 p1' p1 p2) = (term110 p1' p1 p2).
Proof. exact (MK_COMB (@lem1326596) (@lem1326595 p1' p1 p2)). Qed.
Lemma lem1326604 (p1 : hreal) (p2 : hreal) : (term79 p1 p2) = (term111 p1 p2).
Proof. exact (fun_ext (fun p1' : hreal => @lem1326597 p1' p1 p2)). Qed.
Lemma lem1326605 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1326606 (p1 : hreal) (p2 : hreal) : (term80 p1 p2) = (term112 p1 p2).
Proof. exact (MK_COMB (@lem1326605) (@lem1326604 p1 p2)). Qed.
Lemma lem1326613 (p1 : hreal) (p2 : hreal) : (term56 p1 p2) = (term112 p1 p2).
Proof. exact (TRANS (@lem1326499 p1 p2) (@lem1326606 p1 p2)). Qed.
Lemma lem1326614 (p1 : hreal) : (term58 p1) = (term113 p1).
Proof. exact (fun_ext (fun p2 : hreal => @lem1326613 p1 p2)). Qed.
Lemma lem1326615 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1326616 (p1 : hreal) : (term60 p1) = (term114 p1).
Proof. exact (MK_COMB (@lem1326615) (@lem1326614 p1)). Qed.
Lemma lem1326623 : term62 = term115.
Proof. exact (fun_ext (fun p1 : hreal => @lem1326616 p1)). Qed.
Lemma lem1326624 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1326625 : term63 = term116.
Proof. exact (MK_COMB (@lem1326624) (@lem1326623)). Qed.
Lemma lem1326632 : term52 = term116.
Proof. exact (TRANS (@lem1326464) (@lem1326625)). Qed.
Lemma lem1326633 : term116 = term52.
Proof. exact (SYM (@lem1326632)). Qed.
Lemma lem1326634 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2'' : hreal) (p1'' : hreal) (p2' : hreal) (h1 : term101 p1 p2 p1' p2'' p1'' p2') : term101 p1 p2 p1' p2'' p1'' p2'.
Proof. exact (h1). Qed.
Lemma lem1326635 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2'' : hreal) (p1'' : hreal) (p2' : hreal) (h1 : term101 p1 p2 p1' p2'' p1'' p2') : (hreal_add p1' p2'') = (hreal_add p1'' p2').
Proof. exact (proj2 (@lem1326634 p1 p2 p1' p2'' p1'' p2' h1)). Qed.
Lemma lem1326636 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2'' : hreal) (p1'' : hreal) (p2' : hreal) (h1 : term101 p1 p2 p1' p2'' p1'' p2') : (hreal_add p1 p2') = (hreal_add p1' p2).
Proof. exact (proj1 (@lem1326634 p1 p2 p1' p2'' p1'' p2' h1)). Qed.
Lemma lem1326637 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2'' : hreal) (p1'' : hreal) (p2' : hreal) (h1 : term101 p1 p2 p1' p2'' p1'' p2') : (term117 p1 p2') = (term117 p1' p2).
Proof. exact (MK_COMB (@lem1326426) (@lem1326636 p1 p2 p1' p2'' p1'' p2' h1)). Qed.
Lemma lem1326638 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2'' : hreal) (p1'' : hreal) (p2' : hreal) (h1 : term101 p1 p2 p1' p2'' p1'' p2') : (term118 p1 p2' p1' p2'') = (term118 p1' p2 p1'' p2').
Proof. exact (MK_COMB (@lem1326637 p1 p2 p1' p2'' p1'' p2' h1) (@lem1326635 p1 p2 p1' p2'' p1'' p2' h1)). Qed.
Lemma lem1326640 (y : hreal) (x : hreal) : (hreal_add x y) = (hreal_add y x).
Proof. exact (EQ_MP (@lem1326424 y x) (@lem1326423 x y)). Qed.
Lemma lem1326641 (p1' : hreal) (p2'' : hreal) (p1 : hreal) (p2' : hreal) : (term118 p1 p2' p1' p2'') = (term118 p1' p2'' p1 p2').
Proof. exact (@lem1326640 (hreal_add p1' p2'') (hreal_add p1 p2')). Qed.
Lemma lem1326642 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1326643 (p1' : hreal) (p2'' : hreal) (p1 : hreal) (p2' : hreal) : (term119 p1 p2' p1' p2'') = (term119 p1' p2'' p1 p2').
Proof. exact (MK_COMB (@lem1326642) (@lem1326641 p1' p2'' p1 p2')). Qed.
Lemma lem1326644 (p1' : hreal) (p2 : hreal) (p1'' : hreal) (p2' : hreal) : (term118 p1' p2 p1'' p2') = (term118 p1' p2 p1'' p2').
Proof. exact (eq_refl (term118 p1' p2 p1'' p2')). Qed.
Lemma lem1326645 (p2'' : hreal) (p1 : hreal) (p1' : hreal) (p2 : hreal) (p1'' : hreal) (p2' : hreal) : ((term118 p1 p2' p1' p2'') = (term118 p1' p2 p1'' p2')) = ((term118 p1' p2'' p1 p2') = (term118 p1' p2 p1'' p2')).
Proof. exact (MK_COMB (@lem1326643 p1' p2'' p1 p2') (@lem1326644 p1' p2 p1'' p2')). Qed.
Lemma lem1326646 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1326647 (p2'' : hreal) (p1 : hreal) (p1' : hreal) (p2 : hreal) (p1'' : hreal) (p2' : hreal) : (term120 p1 p2'' p1' p2 p1'' p2') = (term121 p2'' p1 p1' p2 p1'' p2').
Proof. exact (MK_COMB (@lem1326646) (@lem1326645 p2'' p1 p1' p2 p1'' p2')). Qed.
Lemma lem1326648 (p1 : hreal) (p2'' : hreal) (p1'' : hreal) (p2 : hreal) : ((hreal_add p1 p2'') = (hreal_add p1'' p2)) = ((hreal_add p1 p2'') = (hreal_add p1'' p2)).
Proof. exact (eq_refl ((hreal_add p1 p2'') = (hreal_add p1'' p2))). Qed.
Lemma lem1326649 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2'' : hreal) (p1'' : hreal) (p2 : hreal) : (term122 p1' p2' p1 p2'' p1'' p2) = (term123 p1' p2' p1 p2'' p1'' p2).
Proof. exact (MK_COMB (@lem1326647 p2'' p1 p1' p2 p1'' p2') (@lem1326648 p1 p2'' p1'' p2)). Qed.
Lemma lem1326650 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2'' : hreal) (p1'' : hreal) (p2 : hreal) : (term123 p1' p2' p1 p2'' p1'' p2) = (term122 p1' p2' p1 p2'' p1'' p2).
Proof. exact (SYM (@lem1326649 p1' p2' p1 p2'' p1'' p2)). Qed.
Lemma lem1326660 (x : hreal) (y : hreal) (z : hreal) : (term14 x y z) = (term13 x y z).
Proof. exact (EQ_MP (@lem1326418 x y z) (@lem1326417 x y z)). Qed.
Lemma lem1326661 (p1' : hreal) (p2'' : hreal) (p1 : hreal) (p2' : hreal) : (term118 p1' p2'' p1 p2') = (term124 p1' p2'' p1 p2').
Proof. exact (@lem1326660 p1' p2'' (hreal_add p1 p2')). Qed.
Lemma lem1326662 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1326663 (p1' : hreal) (p2'' : hreal) (p1 : hreal) (p2' : hreal) : (term119 p1' p2'' p1 p2') = (term125 p1' p2'' p1 p2').
Proof. exact (MK_COMB (@lem1326662) (@lem1326661 p1' p2'' p1 p2')). Qed.
Lemma lem1326665 (x : hreal) (y : hreal) (z : hreal) : (term14 x y z) = (term13 x y z).
Proof. exact (EQ_MP (@lem1326418 x y z) (@lem1326417 x y z)). Qed.
Lemma lem1326666 (p1' : hreal) (p2 : hreal) (p1'' : hreal) (p2' : hreal) : (term118 p1' p2 p1'' p2') = (term124 p1' p2 p1'' p2').
Proof. exact (@lem1326665 p1' p2 (hreal_add p1'' p2')). Qed.
Lemma lem1326667 (p2'' : hreal) (p1 : hreal) (p1' : hreal) (p2 : hreal) (p1'' : hreal) (p2' : hreal) : ((term118 p1' p2'' p1 p2') = (term118 p1' p2 p1'' p2')) = ((term124 p1' p2'' p1 p2') = (term124 p1' p2 p1'' p2')).
Proof. exact (MK_COMB (@lem1326663 p1' p2'' p1 p2') (@lem1326666 p1' p2 p1'' p2')). Qed.
Lemma lem1326669 (m : hreal) (n : hreal) (p : hreal) : ((hreal_add m n) = (hreal_add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1326409 m n p) (@lem1326408 m n p)). Qed.
Lemma lem1326670 (p1' : hreal) (p2'' : hreal) (p1 : hreal) (p2 : hreal) (p1'' : hreal) (p2' : hreal) : ((term124 p1' p2'' p1 p2') = (term124 p1' p2 p1'' p2')) = ((term13 p2'' p1 p2') = (term13 p2 p1'' p2')).
Proof. exact (@lem1326669 p1' (term13 p2'' p1 p2') (term13 p2 p1'' p2')). Qed.
Lemma lem1326675 (p1' : hreal) (p2'' : hreal) (p1 : hreal) (p2 : hreal) (p1'' : hreal) (p2' : hreal) : ((term118 p1' p2'' p1 p2') = (term118 p1' p2 p1'' p2')) = ((term13 p2'' p1 p2') = (term13 p2 p1'' p2')).
Proof. exact (TRANS (@lem1326667 p2'' p1 p1' p2 p1'' p2') (@lem1326670 p1' p2'' p1 p2 p1'' p2')). Qed.
Lemma lem1326676 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1326677 (p1' : hreal) (p2'' : hreal) (p1 : hreal) (p2 : hreal) (p1'' : hreal) (p2' : hreal) : (term121 p2'' p1 p1' p2 p1'' p2') = (term126 p2'' p1 p2 p1'' p2').
Proof. exact (MK_COMB (@lem1326676) (@lem1326675 p1' p2'' p1 p2 p1'' p2')). Qed.
Lemma lem1326682 (p1 : hreal) (p2'' : hreal) (p1'' : hreal) (p2 : hreal) : ((hreal_add p1 p2'') = (hreal_add p1'' p2)) = ((hreal_add p1 p2'') = (hreal_add p1'' p2)).
Proof. exact (eq_refl ((hreal_add p1 p2'') = (hreal_add p1'' p2))). Qed.
Lemma lem1326683 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2'' : hreal) (p1'' : hreal) (p2 : hreal) : (term123 p1' p2' p1 p2'' p1'' p2) = (term127 p2' p1 p2'' p1'' p2).
Proof. exact (MK_COMB (@lem1326677 p1' p2'' p1 p2 p1'' p2') (@lem1326682 p1 p2'' p1'' p2)). Qed.
Lemma lem1326688 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2'' : hreal) (p1'' : hreal) (p2 : hreal) : (term127 p2' p1 p2'' p1'' p2) = (term123 p1' p2' p1 p2'' p1'' p2).
Proof. exact (SYM (@lem1326683 p1' p2' p1 p2'' p1'' p2)). Qed.
Lemma lem1326698 (x : hreal) (y : hreal) (z : hreal) : (term13 x y z) = (term14 x y z).
Proof. exact (EQ_MP (@lem1326382 x y z) (@lem1326381 x y z)). Qed.
Lemma lem1326699 (p2'' : hreal) (p1 : hreal) (p2' : hreal) : (term13 p2'' p1 p2') = (term14 p2'' p1 p2').
Proof. exact (@lem1326698 p2'' p1 p2'). Qed.
Lemma lem1326700 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1326701 (p2'' : hreal) (p1 : hreal) (p2' : hreal) : (term128 p2'' p1 p2') = (term129 p2'' p1 p2').
Proof. exact (MK_COMB (@lem1326700) (@lem1326699 p2'' p1 p2')). Qed.
Lemma lem1326703 (x : hreal) (y : hreal) (z : hreal) : (term13 x y z) = (term14 x y z).
Proof. exact (EQ_MP (@lem1326382 x y z) (@lem1326381 x y z)). Qed.
Lemma lem1326704 (p2 : hreal) (p1'' : hreal) (p2' : hreal) : (term13 p2 p1'' p2') = (term14 p2 p1'' p2').
Proof. exact (@lem1326703 p2 p1'' p2'). Qed.
Lemma lem1326705 (p2'' : hreal) (p1 : hreal) (p2 : hreal) (p1'' : hreal) (p2' : hreal) : ((term13 p2'' p1 p2') = (term13 p2 p1'' p2')) = ((term14 p2'' p1 p2') = (term14 p2 p1'' p2')).
Proof. exact (MK_COMB (@lem1326701 p2'' p1 p2') (@lem1326704 p2 p1'' p2')). Qed.
Lemma lem1326707 (p : hreal) (m : hreal) (n : hreal) : ((hreal_add m p) = (hreal_add n p)) = (m = n).
Proof. exact (EQ_MP (@lem1326373 p m n) (@lem1326372 m n p)). Qed.
Lemma lem1326708 (p2' : hreal) (p2'' : hreal) (p1 : hreal) (p2 : hreal) (p1'' : hreal) : ((term14 p2'' p1 p2') = (term14 p2 p1'' p2')) = ((hreal_add p2'' p1) = (hreal_add p2 p1'')).
Proof. exact (@lem1326707 p2' (hreal_add p2'' p1) (hreal_add p2 p1'')). Qed.
Lemma lem1326713 (p2' : hreal) (p2'' : hreal) (p1 : hreal) (p2 : hreal) (p1'' : hreal) : ((term13 p2'' p1 p2') = (term13 p2 p1'' p2')) = ((hreal_add p2'' p1) = (hreal_add p2 p1'')).
Proof. exact (TRANS (@lem1326705 p2'' p1 p2 p1'' p2') (@lem1326708 p2' p2'' p1 p2 p1'')). Qed.
Lemma lem1326714 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1326715 (p2' : hreal) (p2'' : hreal) (p1 : hreal) (p2 : hreal) (p1'' : hreal) : (term126 p2'' p1 p2 p1'' p2') = (term130 p2'' p1 p2 p1'').
Proof. exact (MK_COMB (@lem1326714) (@lem1326713 p2' p2'' p1 p2 p1'')). Qed.
Lemma lem1326720 (p1 : hreal) (p2'' : hreal) (p1'' : hreal) (p2 : hreal) : ((hreal_add p1 p2'') = (hreal_add p1'' p2)) = ((hreal_add p1 p2'') = (hreal_add p1'' p2)).
Proof. exact (eq_refl ((hreal_add p1 p2'') = (hreal_add p1'' p2))). Qed.
Lemma lem1326721 (p2' : hreal) (p1 : hreal) (p2'' : hreal) (p1'' : hreal) (p2 : hreal) : (term127 p2' p1 p2'' p1'' p2) = (term131 p1 p2'' p1'' p2).
Proof. exact (MK_COMB (@lem1326715 p2' p2'' p1 p2 p1'') (@lem1326720 p1 p2'' p1'' p2)). Qed.
Lemma lem1326726 (p2' : hreal) (p1 : hreal) (p2'' : hreal) (p1'' : hreal) (p2 : hreal) : (term131 p1 p2'' p1'' p2) = (term127 p2' p1 p2'' p1'' p2).
Proof. exact (SYM (@lem1326721 p2' p1 p2'' p1'' p2)). Qed.
Lemma lem1326727 (p2'' : hreal) (p1 : hreal) (p2 : hreal) (p1'' : hreal) (h1 : (hreal_add p2'' p1) = (hreal_add p2 p1'')) : (hreal_add p2'' p1) = (hreal_add p2 p1'').
Proof. exact (h1). Qed.
Lemma lem1326731 (y : hreal) (x : hreal) : (hreal_add x y) = (hreal_add y x).
Proof. exact (EQ_MP (@lem1326364 y x) (@lem1326363 x y)). Qed.
Lemma lem1326732 (p1 : hreal) (p2'' : hreal) : (hreal_add p2'' p1) = (hreal_add p1 p2'').
Proof. exact (@lem1326731 p1 p2''). Qed.
Lemma lem1326733 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1326734 (p1 : hreal) (p2'' : hreal) : (term132 p2'' p1) = (term132 p1 p2'').
Proof. exact (MK_COMB (@lem1326733) (@lem1326732 p1 p2'')). Qed.
Lemma lem1326736 (y : hreal) (x : hreal) : (hreal_add x y) = (hreal_add y x).
Proof. exact (EQ_MP (@lem1326364 y x) (@lem1326363 x y)). Qed.
Lemma lem1326737 (p1'' : hreal) (p2 : hreal) : (hreal_add p2 p1'') = (hreal_add p1'' p2).
Proof. exact (@lem1326736 p1'' p2). Qed.
Lemma lem1326738 (p1 : hreal) (p2'' : hreal) (p1'' : hreal) (p2 : hreal) : ((hreal_add p2'' p1) = (hreal_add p2 p1'')) = ((hreal_add p1 p2'') = (hreal_add p1'' p2)).
Proof. exact (MK_COMB (@lem1326734 p1 p2'') (@lem1326737 p1'' p2)). Qed.
Lemma lem1326741 (p2'' : hreal) (p1 : hreal) (p2 : hreal) (p1'' : hreal) (h1 : (hreal_add p2'' p1) = (hreal_add p2 p1'')) : (hreal_add p1 p2'') = (hreal_add p1'' p2).
Proof. exact (EQ_MP (@lem1326738 p1 p2'' p1'' p2) (@lem1326727 p2'' p1 p2 p1'' h1)). Qed.
Lemma lem1326742 (p1 : hreal) (p2'' : hreal) (p1'' : hreal) (p2 : hreal) : term131 p1 p2'' p1'' p2.
Proof. exact (fun h0 : (hreal_add p2'' p1) = (hreal_add p2 p1'') => @lem1326741 p2'' p1 p2 p1'' h0). Qed.
Lemma lem1326743 (p2' : hreal) (p1 : hreal) (p2'' : hreal) (p1'' : hreal) (p2 : hreal) : term127 p2' p1 p2'' p1'' p2.
Proof. exact (EQ_MP (@lem1326726 p2' p1 p2'' p1'' p2) (@lem1326742 p1 p2'' p1'' p2)). Qed.
Lemma lem1326744 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2'' : hreal) (p1'' : hreal) (p2 : hreal) : term123 p1' p2' p1 p2'' p1'' p2.
Proof. exact (EQ_MP (@lem1326688 p1' p2' p1 p2'' p1'' p2) (@lem1326743 p2' p1 p2'' p1'' p2)). Qed.
Lemma lem1326745 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2'' : hreal) (p1'' : hreal) (p2 : hreal) : term122 p1' p2' p1 p2'' p1'' p2.
Proof. exact (EQ_MP (@lem1326650 p1' p2' p1 p2'' p1'' p2) (@lem1326744 p1' p2' p1 p2'' p1'' p2)). Qed.
Lemma lem1326746 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2'' : hreal) (p1'' : hreal) (p2' : hreal) (h1 : term101 p1 p2 p1' p2'' p1'' p2') : (hreal_add p1 p2'') = (hreal_add p1'' p2).
Proof. exact (@lem1326745 p1' p2' p1 p2'' p1'' p2 (@lem1326638 p1 p2 p1' p2'' p1'' p2' h1)). Qed.
Lemma lem1326747 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2'' : hreal) (p1'' : hreal) (p2 : hreal) : term104 p1' p2' p1 p2'' p1'' p2.
Proof. exact (fun h0 : term101 p1 p2 p1' p2'' p1'' p2' => @lem1326746 p1 p2 p1' p2'' p1'' p2' h0). Qed.
Lemma lem1326752 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p1'' : hreal) (p2 : hreal) : term106 p1' p2' p1 p1'' p2.
Proof. exact (fun p2'' : hreal => @lem1326747 p1' p2' p1 p2'' p1'' p2). Qed.
Lemma lem1326757 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : term108 p1' p2' p1 p2.
Proof. exact (fun p1'' : hreal => @lem1326752 p1' p2' p1 p1'' p2). Qed.
Lemma lem1326762 (p1' : hreal) (p1 : hreal) (p2 : hreal) : term110 p1' p1 p2.
Proof. exact (fun p2' : hreal => @lem1326757 p1' p2' p1 p2). Qed.
Lemma lem1326767 (p1 : hreal) (p2 : hreal) : term112 p1 p2.
Proof. exact (fun p1' : hreal => @lem1326762 p1' p1 p2). Qed.
Lemma lem1326772 (p1 : hreal) : term114 p1.
Proof. exact (fun p2 : hreal => @lem1326767 p1 p2). Qed.
Lemma lem1326777 : term116.
Proof. exact (fun p1 : hreal => @lem1326772 p1). Qed.
Lemma lem1326778 : term52.
Proof. exact (EQ_MP (@lem1326633) (@lem1326777)). Qed.
