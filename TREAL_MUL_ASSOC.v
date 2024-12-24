Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import TREAL_MUL_ASSOC_term_abbrevs.
Require Import FORALL_PAIR_THM_spec.
Require Import HREAL_ADD_AC_spec.
Require Import HREAL_ADD_RDISTRIB_spec.
Require Import TREAL_EQ_AP_spec.
Require Import thm0_spec.
Require Import thm1320816_spec.
Require Import thm1321091_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import treal_mul_spec.
Lemma lem1328393 (x : hreal) (y : hreal) (z : hreal) (h1 : (term0 x y z) = (term1 x y z)) : (term0 x y z) = (term1 x y z).
Proof. exact (h1). Qed.
Lemma lem1328394 (x : hreal) (y : hreal) (z : hreal) (h1 : (term0 x y z) = (term1 x y z)) : (term1 x y z) = (term0 x y z).
Proof. exact (SYM (@lem1328393 x y z h1)). Qed.
Lemma lem1328395 (x : hreal) (y : hreal) (z : hreal) (h1 : (term1 x y z) = (term0 x y z)) : (term1 x y z) = (term0 x y z).
Proof. exact (h1). Qed.
Lemma lem1328396 (x : hreal) (y : hreal) (z : hreal) (h1 : (term1 x y z) = (term0 x y z)) : (term0 x y z) = (term1 x y z).
Proof. exact (SYM (@lem1328395 x y z h1)). Qed.
Lemma lem1328397 (x : hreal) (y : hreal) (z : hreal) : ((term0 x y z) = (term1 x y z)) = ((term1 x y z) = (term0 x y z)).
Proof. exact (prop_ext (fun h1 : (term0 x y z) = (term1 x y z) => @lem1328394 x y z h1) (fun h1 : (term1 x y z) = (term0 x y z) => @lem1328396 x y z h1)). Qed.
Lemma lem1328398 (x : hreal) (y : hreal) : (term2 x y) = (term3 x y).
Proof. exact (fun_ext (fun z : hreal => @lem1328397 x y z)). Qed.
Lemma lem1328399 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1328400 (x : hreal) (y : hreal) : (term4 x y) = (term5 x y).
Proof. exact (MK_COMB (@lem1328399) (@lem1328398 x y)). Qed.
Lemma lem1328401 (x : hreal) : (term6 x) = (term7 x).
Proof. exact (fun_ext (fun y : hreal => @lem1328400 x y)). Qed.
Lemma lem1328402 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1328403 (x : hreal) : (term8 x) = (term9 x).
Proof. exact (MK_COMB (@lem1328402) (@lem1328401 x)). Qed.
Lemma lem1328404 : term10 = term11.
Proof. exact (fun_ext (fun x : hreal => @lem1328403 x)). Qed.
Lemma lem1328405 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1328406 : term12 = term13.
Proof. exact (MK_COMB (@lem1328405) (@lem1328404)). Qed.
Lemma lem1328407 : term13.
Proof. exact (EQ_MP (@lem1328406) (@lem1320816)). Qed.
Lemma lem1328408 (n : hreal) (m : hreal) (p : hreal) : term14 n m p.
Proof. exact (proj2 (@lem1322003 n m p)). Qed.
Lemma lem1328412 (x : hreal) : term15 x.
Proof. exact (@lem1328407 x). Qed.
Lemma lem1328413 (x : hreal) : (term15 x) = (term9 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1328414 (x : hreal) : term9 x.
Proof. exact (EQ_MP (@lem1328413 x) (@lem1328412 x)). Qed.
Lemma lem1328415 (x : hreal) (y : hreal) : term16 x y.
Proof. exact (@lem1328414 x y). Qed.
Lemma lem1328416 (x : hreal) (y : hreal) : (term16 x y) = (term5 x y).
Proof. exact (eq_refl (term16 x y)). Qed.
Lemma lem1328417 (x : hreal) (y : hreal) : term5 x y.
Proof. exact (EQ_MP (@lem1328416 x y) (@lem1328415 x y)). Qed.
Lemma lem1328418 (x : hreal) (y : hreal) (z : hreal) : term17 x y z.
Proof. exact (@lem1328417 x y z). Qed.
Lemma lem1328419 (x : hreal) (y : hreal) (z : hreal) : (term17 x y z) = ((term1 x y z) = (term0 x y z)).
Proof. exact (eq_refl (term17 x y z)). Qed.
Lemma lem1328421 (m : hreal) : term18 m.
Proof. exact (@lem1321767 m). Qed.
Lemma lem1328422 (m : hreal) : (term18 m) = (term19 m).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem1328423 (m : hreal) : term19 m.
Proof. exact (EQ_MP (@lem1328422 m) (@lem1328421 m)). Qed.
Lemma lem1328424 (m : hreal) (n : hreal) : term20 m n.
Proof. exact (@lem1328423 m n). Qed.
Lemma lem1328425 (m : hreal) (n : hreal) : (term20 m n) = (term21 m n).
Proof. exact (eq_refl (term20 m n)). Qed.
Lemma lem1328426 (m : hreal) (n : hreal) : term21 m n.
Proof. exact (EQ_MP (@lem1328425 m n) (@lem1328424 m n)). Qed.
Lemma lem1328427 (m : hreal) (n : hreal) (p : hreal) : term22 m n p.
Proof. exact (@lem1328426 m n p). Qed.
Lemma lem1328428 (m : hreal) (n : hreal) (p : hreal) : (term22 m n p) = ((term23 m n p) = (term24 m n p)).
Proof. exact (eq_refl (term22 m n p)). Qed.
Lemma lem1328430 (x : hreal) : term25 x.
Proof. exact (@lem1321091 x). Qed.
Lemma lem1328431 (x : hreal) : (term25 x) = (term26 x).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem1328432 (x : hreal) : term26 x.
Proof. exact (EQ_MP (@lem1328431 x) (@lem1328430 x)). Qed.
Lemma lem1328433 (x : hreal) (y : hreal) : term27 x y.
Proof. exact (@lem1328432 x y). Qed.
Lemma lem1328434 (y : hreal) (x : hreal) : (term27 x y) = (term28 y x).
Proof. exact (eq_refl (term27 x y)). Qed.
Lemma lem1328435 (y : hreal) (x : hreal) : term28 y x.
Proof. exact (EQ_MP (@lem1328434 y x) (@lem1328433 x y)). Qed.
Lemma lem1328436 (y : hreal) (x : hreal) (z : hreal) : term29 y x z.
Proof. exact (@lem1328435 y x z). Qed.
Lemma lem1328437 (y : hreal) (x : hreal) (z : hreal) : (term29 y x z) = ((term30 x y z) = (term31 y x z)).
Proof. exact (eq_refl (term29 y x z)). Qed.
Lemma lem1328439 (x1 : hreal) : term32 x1.
Proof. exact (@lem1324372 x1). Qed.
Lemma lem1328440 (x1 : hreal) : (term32 x1) = (term33 x1).
Proof. exact (eq_refl (term32 x1)). Qed.
Lemma lem1328441 (x1 : hreal) : term33 x1.
Proof. exact (EQ_MP (@lem1328440 x1) (@lem1328439 x1)). Qed.
Lemma lem1328442 (x1 : hreal) (y2 : hreal) : term34 x1 y2.
Proof. exact (@lem1328441 x1 y2). Qed.
Lemma lem1328443 (x1 : hreal) (y2 : hreal) : (term34 x1 y2) = (term35 x1 y2).
Proof. exact (eq_refl (term34 x1 y2)). Qed.
Lemma lem1328444 (x1 : hreal) (y2 : hreal) : term35 x1 y2.
Proof. exact (EQ_MP (@lem1328443 x1 y2) (@lem1328442 x1 y2)). Qed.
Lemma lem1328445 (x1 : hreal) (y2 : hreal) (y1 : hreal) : term36 x1 y2 y1.
Proof. exact (@lem1328444 x1 y2 y1). Qed.
Lemma lem1328446 (x1 : hreal) (y2 : hreal) (y1 : hreal) : (term36 x1 y2 y1) = (term37 x1 y2 y1).
Proof. exact (eq_refl (term36 x1 y2 y1)). Qed.
Lemma lem1328447 (x1 : hreal) (y2 : hreal) (y1 : hreal) : term37 x1 y2 y1.
Proof. exact (EQ_MP (@lem1328446 x1 y2 y1) (@lem1328445 x1 y2 y1)). Qed.
Lemma lem1328448 (x1 : hreal) (y2 : hreal) (y1 : hreal) (x2 : hreal) : term38 x1 y2 y1 x2.
Proof. exact (@lem1328447 x1 y2 y1 x2). Qed.
Lemma lem1328449 (x1 : hreal) (y2 : hreal) (y1 : hreal) (x2 : hreal) : (term38 x1 y2 y1 x2) = ((term39 x1 y1 x2 y2) = (term40 x1 y2 y1 x2)).
Proof. exact (eq_refl (term38 x1 y2 y1 x2)). Qed.
Lemma lem1328451 (x : prod hreal hreal) : term41 x.
Proof. exact (@lem1326851 x). Qed.
Lemma lem1328452 (x : prod hreal hreal) : (term41 x) = (term42 x).
Proof. exact (eq_refl (term41 x)). Qed.
Lemma lem1328453 (x : prod hreal hreal) : term42 x.
Proof. exact (EQ_MP (@lem1328452 x) (@lem1328451 x)). Qed.
Lemma lem1328454 (x : prod hreal hreal) (y : prod hreal hreal) : term43 x y.
Proof. exact (@lem1328453 x y). Qed.
Lemma lem1328455 (x : prod hreal hreal) (y : prod hreal hreal) : (term43 x y) = (term44 x y).
Proof. exact (eq_refl (term43 x y)). Qed.
Lemma lem1328456 (x : prod hreal hreal) (y : prod hreal hreal) : term44 x y.
Proof. exact (EQ_MP (@lem1328455 x y) (@lem1328454 x y)). Qed.
Lemma lem1328457 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem1328458 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : x = y) : treal_eq x y.
Proof. exact (@lem1328456 x y (@lem1328457 x y h1)). Qed.
Lemma lem1328459 (x : prod hreal hreal) (y : prod hreal hreal) : (treal_eq x y) = ((treal_eq x y) = True).
Proof. exact (@lem7 (treal_eq x y)). Qed.
Lemma lem1328460 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : x = y) : (treal_eq x y) = True.
Proof. exact (EQ_MP (@lem1328459 x y) (@lem1328458 x y h1)). Qed.
Lemma lem1328466 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term45 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem1328467 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term45 _5106 _5107 P) = ((term46 _5106 _5107 P) = (term47 _5106 _5107 P)).
Proof. exact (eq_refl (term45 _5106 _5107 P)). Qed.
Lemma lem1328474 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term46 _5106 _5107 P) = (term47 _5106 _5107 P).
Proof. exact (EQ_MP (@lem1328467 _5106 _5107 P) (@lem1328466 _5106 _5107 P)). Qed.
Lemma lem1328475 (P : type1233) : (term48 P) = (term49 P).
Proof. exact (@lem1328474 hreal hreal P). Qed.
Lemma lem1328476 : term50 = term51.
Proof. exact (@lem1328475 term52). Qed.
Lemma lem1328477 (x : prod hreal hreal) : (term53 x) = (term54 x).
Proof. exact (eq_refl (term53 x)). Qed.
Lemma lem1328478 : term55 = term52.
Proof. exact (fun_ext (fun x : prod hreal hreal => @lem1328477 x)). Qed.
Lemma lem1328479 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1328480 : term50 = term56.
Proof. exact (MK_COMB (@lem1328479) (@lem1328478)). Qed.
Lemma lem1328481 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1328482 : term57 = term58.
Proof. exact (MK_COMB (@lem1328481) (@lem1328480)). Qed.
Lemma lem1328483 (p1 : hreal) (p2 : hreal) : (term59 p1 p2) = (term60 p1 p2).
Proof. exact (eq_refl (term59 p1 p2)). Qed.
Lemma lem1328484 (p1 : hreal) : (term61 p1) = (term62 p1).
Proof. exact (fun_ext (fun p2 : hreal => @lem1328483 p1 p2)). Qed.
Lemma lem1328485 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1328486 (p1 : hreal) : (term63 p1) = (term64 p1).
Proof. exact (MK_COMB (@lem1328485) (@lem1328484 p1)). Qed.
Lemma lem1328487 : term65 = term66.
Proof. exact (fun_ext (fun p1 : hreal => @lem1328486 p1)). Qed.
Lemma lem1328488 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1328489 : term51 = term67.
Proof. exact (MK_COMB (@lem1328488) (@lem1328487)). Qed.
Lemma lem1328490 : (term50 = term51) = (term56 = term67).
Proof. exact (MK_COMB (@lem1328482) (@lem1328489)). Qed.
Lemma lem1328491 : term56 = term67.
Proof. exact (EQ_MP (@lem1328490) (@lem1328476)). Qed.
Lemma lem1328509 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term46 _5106 _5107 P) = (term47 _5106 _5107 P).
Proof. exact (EQ_MP (@lem1328467 _5106 _5107 P) (@lem1328466 _5106 _5107 P)). Qed.
Lemma lem1328510 (P : type1233) : (term48 P) = (term49 P).
Proof. exact (@lem1328509 hreal hreal P). Qed.
Lemma lem1328511 (p1 : hreal) (p2 : hreal) : (term68 p1 p2) = (term69 p1 p2).
Proof. exact (@lem1328510 (term70 p1 p2)). Qed.
Lemma lem1328512 (p1 : hreal) (p2 : hreal) (y : prod hreal hreal) : (term71 p1 p2 y) = (term72 p1 p2 y).
Proof. exact (eq_refl (term71 p1 p2 y)). Qed.
Lemma lem1328513 (p1 : hreal) (p2 : hreal) : (term73 p1 p2) = (term70 p1 p2).
Proof. exact (fun_ext (fun y : prod hreal hreal => @lem1328512 p1 p2 y)). Qed.
Lemma lem1328514 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1328515 (p1 : hreal) (p2 : hreal) : (term68 p1 p2) = (term60 p1 p2).
Proof. exact (MK_COMB (@lem1328514) (@lem1328513 p1 p2)). Qed.
Lemma lem1328516 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1328517 (p1 : hreal) (p2 : hreal) : (term74 p1 p2) = (term75 p1 p2).
Proof. exact (MK_COMB (@lem1328516) (@lem1328515 p1 p2)). Qed.
Lemma lem1328518 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : (term76 p1 p2 p1' p2') = (term77 p1 p2 p1' p2').
Proof. exact (eq_refl (term76 p1 p2 p1' p2')). Qed.
Lemma lem1328519 (p1 : hreal) (p2 : hreal) (p1' : hreal) : (term78 p1 p2 p1') = (term79 p1 p2 p1').
Proof. exact (fun_ext (fun p2' : hreal => @lem1328518 p1 p2 p1' p2')). Qed.
Lemma lem1328520 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1328521 (p1 : hreal) (p2 : hreal) (p1' : hreal) : (term80 p1 p2 p1') = (term81 p1 p2 p1').
Proof. exact (MK_COMB (@lem1328520) (@lem1328519 p1 p2 p1')). Qed.
Lemma lem1328522 (p1 : hreal) (p2 : hreal) : (term82 p1 p2) = (term83 p1 p2).
Proof. exact (fun_ext (fun p1' : hreal => @lem1328521 p1 p2 p1')). Qed.
Lemma lem1328523 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1328524 (p1 : hreal) (p2 : hreal) : (term69 p1 p2) = (term84 p1 p2).
Proof. exact (MK_COMB (@lem1328523) (@lem1328522 p1 p2)). Qed.
Lemma lem1328525 (p1 : hreal) (p2 : hreal) : ((term68 p1 p2) = (term69 p1 p2)) = ((term60 p1 p2) = (term84 p1 p2)).
Proof. exact (MK_COMB (@lem1328517 p1 p2) (@lem1328524 p1 p2)). Qed.
Lemma lem1328526 (p1 : hreal) (p2 : hreal) : (term60 p1 p2) = (term84 p1 p2).
Proof. exact (EQ_MP (@lem1328525 p1 p2) (@lem1328511 p1 p2)). Qed.
Lemma lem1328544 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term46 _5106 _5107 P) = (term47 _5106 _5107 P).
Proof. exact (EQ_MP (@lem1328467 _5106 _5107 P) (@lem1328466 _5106 _5107 P)). Qed.
Lemma lem1328545 (P : type1233) : (term48 P) = (term49 P).
Proof. exact (@lem1328544 hreal hreal P). Qed.
Lemma lem1328546 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : (term85 p1 p2 p1' p2') = (term86 p1 p2 p1' p2').
Proof. exact (@lem1328545 (term87 p1 p2 p1' p2')). Qed.
Lemma lem1328547 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) (z : prod hreal hreal) : (term88 p1 p2 p1' p2' z) = (term89 p1 p2 p1' p2' z).
Proof. exact (eq_refl (term88 p1 p2 p1' p2' z)). Qed.
Lemma lem1328548 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : (term90 p1 p2 p1' p2') = (term87 p1 p2 p1' p2').
Proof. exact (fun_ext (fun z : prod hreal hreal => @lem1328547 p1 p2 p1' p2' z)). Qed.
Lemma lem1328549 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1328550 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : (term85 p1 p2 p1' p2') = (term77 p1 p2 p1' p2').
Proof. exact (MK_COMB (@lem1328549) (@lem1328548 p1 p2 p1' p2')). Qed.
Lemma lem1328551 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1328552 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : (term91 p1 p2 p1' p2') = (term92 p1 p2 p1' p2').
Proof. exact (MK_COMB (@lem1328551) (@lem1328550 p1 p2 p1' p2')). Qed.
Lemma lem1328553 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) (p1'' : hreal) (p2'' : hreal) : (term93 p1 p2 p1' p2' p1'' p2'') = (term94 p1 p2 p1' p2' p1'' p2'').
Proof. exact (eq_refl (term93 p1 p2 p1' p2' p1'' p2'')). Qed.
Lemma lem1328554 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) (p1'' : hreal) : (term95 p1 p2 p1' p2' p1'') = (term96 p1 p2 p1' p2' p1'').
Proof. exact (fun_ext (fun p2'' : hreal => @lem1328553 p1 p2 p1' p2' p1'' p2'')). Qed.
Lemma lem1328555 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1328556 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) (p1'' : hreal) : (term97 p1 p2 p1' p2' p1'') = (term98 p1 p2 p1' p2' p1'').
Proof. exact (MK_COMB (@lem1328555) (@lem1328554 p1 p2 p1' p2' p1'')). Qed.
Lemma lem1328557 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : (term99 p1 p2 p1' p2') = (term100 p1 p2 p1' p2').
Proof. exact (fun_ext (fun p1'' : hreal => @lem1328556 p1 p2 p1' p2' p1'')). Qed.
Lemma lem1328558 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1328559 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : (term86 p1 p2 p1' p2') = (term101 p1 p2 p1' p2').
Proof. exact (MK_COMB (@lem1328558) (@lem1328557 p1 p2 p1' p2')). Qed.
Lemma lem1328560 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : ((term85 p1 p2 p1' p2') = (term86 p1 p2 p1' p2')) = ((term77 p1 p2 p1' p2') = (term101 p1 p2 p1' p2')).
Proof. exact (MK_COMB (@lem1328552 p1 p2 p1' p2') (@lem1328559 p1 p2 p1' p2')). Qed.
Lemma lem1328561 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : (term77 p1 p2 p1' p2') = (term101 p1 p2 p1' p2').
Proof. exact (EQ_MP (@lem1328560 p1 p2 p1' p2') (@lem1328546 p1 p2 p1' p2')). Qed.
Lemma lem1328575 (x : prod hreal hreal) (y : prod hreal hreal) : term102 x y.
Proof. exact (fun h0 : x = y => @lem1328460 x y h0). Qed.
Lemma lem1328576 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) (p1'' : hreal) (p2'' : hreal) : term103 p1 p2 p1' p2' p1'' p2''.
Proof. exact (@lem1328575 (term104 p1 p2 p1' p2' p1'' p2'') (term105 p1 p2 p1' p2' p1'' p2'')). Qed.
Lemma lem1328580 (x1 : hreal) (y2 : hreal) (y1 : hreal) (x2 : hreal) : (term39 x1 y1 x2 y2) = (term40 x1 y2 y1 x2).
Proof. exact (EQ_MP (@lem1328449 x1 y2 y1 x2) (@lem1328448 x1 y2 y1 x2)). Qed.
Lemma lem1328581 (p1' : hreal) (p2'' : hreal) (p2' : hreal) (p1'' : hreal) : (term39 p1' p2' p1'' p2'') = (term40 p1' p2'' p2' p1'').
Proof. exact (@lem1328580 p1' p2'' p2' p1''). Qed.
Lemma lem1328588 (p1 : hreal) (p2 : hreal) : (term106 p1 p2) = (term106 p1 p2).
Proof. exact (eq_refl (term106 p1 p2)). Qed.
Lemma lem1328589 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2'' : hreal) (p2' : hreal) (p1'' : hreal) : (term104 p1 p2 p1' p2' p1'' p2'') = (term107 p1 p2 p1' p2'' p2' p1'').
Proof. exact (MK_COMB (@lem1328588 p1 p2) (@lem1328581 p1' p2'' p2' p1'')). Qed.
Lemma lem1328591 (x1 : hreal) (y2 : hreal) (y1 : hreal) (x2 : hreal) : (term39 x1 y1 x2 y2) = (term40 x1 y2 y1 x2).
Proof. exact (EQ_MP (@lem1328449 x1 y2 y1 x2) (@lem1328448 x1 y2 y1 x2)). Qed.
Lemma lem1328592 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p1'' : hreal) (p2' : hreal) (p2'' : hreal) : (term107 p1 p2 p1' p2'' p2' p1'') = (term108 p1 p2 p1' p1'' p2' p2'').
Proof. exact (@lem1328591 p1 (term109 p1' p2'' p2' p1'') p2 (term109 p1' p1'' p2' p2'')). Qed.
Lemma lem1328597 (y : hreal) (x : hreal) (z : hreal) : (term30 x y z) = (term31 y x z).
Proof. exact (EQ_MP (@lem1328437 y x z) (@lem1328436 y x z)). Qed.
Lemma lem1328598 (p1' : hreal) (p1'' : hreal) (p1 : hreal) (p2' : hreal) (p2'' : hreal) : (term110 p1 p1' p1'' p2' p2'') = (term111 p1' p1'' p1 p2' p2'').
Proof. exact (@lem1328597 (hreal_mul p1' p1'') p1 (hreal_mul p2' p2'')). Qed.
Lemma lem1328602 : hreal_add = hreal_add.
Proof. exact (eq_refl hreal_add). Qed.
Lemma lem1328603 (p1' : hreal) (p1'' : hreal) (p1 : hreal) (p2' : hreal) (p2'' : hreal) : (term112 p1 p1' p1'' p2' p2'') = (term113 p1' p1'' p1 p2' p2'').
Proof. exact (MK_COMB (@lem1328602) (@lem1328598 p1' p1'' p1 p2' p2'')). Qed.
Lemma lem1328608 (y : hreal) (x : hreal) (z : hreal) : (term30 x y z) = (term31 y x z).
Proof. exact (EQ_MP (@lem1328437 y x z) (@lem1328436 y x z)). Qed.
Lemma lem1328609 (p1' : hreal) (p2'' : hreal) (p2 : hreal) (p2' : hreal) (p1'' : hreal) : (term110 p2 p1' p2'' p2' p1'') = (term111 p1' p2'' p2 p2' p1'').
Proof. exact (@lem1328608 (hreal_mul p1' p2'') p2 (hreal_mul p2' p1'')). Qed.
Lemma lem1328613 (p1 : hreal) (p1' : hreal) (p2'' : hreal) (p2 : hreal) (p2' : hreal) (p1'' : hreal) : (term114 p1 p2 p1' p2'' p2' p1'') = (term115 p1 p1' p2'' p2 p2' p1'').
Proof. exact (MK_COMB (@lem1328603 p1' p1'' p1 p2' p2'') (@lem1328609 p1' p2'' p2 p2' p1'')). Qed.
Lemma lem1328615 (m : hreal) (n : hreal) (p : hreal) : (term116 m n p) = (term117 m n p).
Proof. exact (proj1 (@lem1328408 n m p)). Qed.
Lemma lem1328616 (p1 : hreal) (p1' : hreal) (p2'' : hreal) (p2 : hreal) (p2' : hreal) (p1'' : hreal) : (term115 p1 p1' p2'' p2 p2' p1'') = (term118 p1 p1' p2'' p2 p2' p1'').
Proof. exact (@lem1328615 (term0 p1 p1' p1'') (term0 p1 p2' p2'') (term111 p1' p2'' p2 p2' p1'')). Qed.
Lemma lem1328632 (p1 : hreal) (p1' : hreal) (p2'' : hreal) (p2 : hreal) (p2' : hreal) (p1'' : hreal) : (term114 p1 p2 p1' p2'' p2' p1'') = (term118 p1 p1' p2'' p2 p2' p1'').
Proof. exact (TRANS (@lem1328613 p1 p1' p2'' p2 p2' p1'') (@lem1328616 p1 p1' p2'' p2 p2' p1'')). Qed.
Lemma lem1328633 : (@pair hreal hreal) = (@pair hreal hreal).
Proof. exact (eq_refl (@pair hreal hreal)). Qed.
Lemma lem1328634 (p1 : hreal) (p1' : hreal) (p2'' : hreal) (p2 : hreal) (p2' : hreal) (p1'' : hreal) : (term119 p1 p2 p1' p2'' p2' p1'') = (term120 p1 p1' p2'' p2 p2' p1'').
Proof. exact (MK_COMB (@lem1328633) (@lem1328632 p1 p1' p2'' p2 p2' p1'')). Qed.
Lemma lem1328654 (y : hreal) (x : hreal) (z : hreal) : (term30 x y z) = (term31 y x z).
Proof. exact (EQ_MP (@lem1328437 y x z) (@lem1328436 y x z)). Qed.
Lemma lem1328655 (p1' : hreal) (p2'' : hreal) (p1 : hreal) (p2' : hreal) (p1'' : hreal) : (term110 p1 p1' p2'' p2' p1'') = (term111 p1' p2'' p1 p2' p1'').
Proof. exact (@lem1328654 (hreal_mul p1' p2'') p1 (hreal_mul p2' p1'')). Qed.
Lemma lem1328659 : hreal_add = hreal_add.
Proof. exact (eq_refl hreal_add). Qed.
Lemma lem1328660 (p1' : hreal) (p2'' : hreal) (p1 : hreal) (p2' : hreal) (p1'' : hreal) : (term112 p1 p1' p2'' p2' p1'') = (term113 p1' p2'' p1 p2' p1'').
Proof. exact (MK_COMB (@lem1328659) (@lem1328655 p1' p2'' p1 p2' p1'')). Qed.
Lemma lem1328665 (y : hreal) (x : hreal) (z : hreal) : (term30 x y z) = (term31 y x z).
Proof. exact (EQ_MP (@lem1328437 y x z) (@lem1328436 y x z)). Qed.
Lemma lem1328666 (p1' : hreal) (p1'' : hreal) (p2 : hreal) (p2' : hreal) (p2'' : hreal) : (term110 p2 p1' p1'' p2' p2'') = (term111 p1' p1'' p2 p2' p2'').
Proof. exact (@lem1328665 (hreal_mul p1' p1'') p2 (hreal_mul p2' p2'')). Qed.
Lemma lem1328670 (p1 : hreal) (p1' : hreal) (p1'' : hreal) (p2 : hreal) (p2' : hreal) (p2'' : hreal) : (term114 p1 p2 p1' p1'' p2' p2'') = (term115 p1 p1' p1'' p2 p2' p2'').
Proof. exact (MK_COMB (@lem1328660 p1' p2'' p1 p2' p1'') (@lem1328666 p1' p1'' p2 p2' p2'')). Qed.
Lemma lem1328672 (m : hreal) (n : hreal) (p : hreal) : (term116 m n p) = (term117 m n p).
Proof. exact (proj1 (@lem1328408 n m p)). Qed.
Lemma lem1328673 (p1 : hreal) (p1' : hreal) (p1'' : hreal) (p2 : hreal) (p2' : hreal) (p2'' : hreal) : (term115 p1 p1' p1'' p2 p2' p2'') = (term118 p1 p1' p1'' p2 p2' p2'').
Proof. exact (@lem1328672 (term0 p1 p1' p2'') (term0 p1 p2' p1'') (term111 p1' p1'' p2 p2' p2'')). Qed.
Lemma lem1328689 (p1 : hreal) (p1' : hreal) (p1'' : hreal) (p2 : hreal) (p2' : hreal) (p2'' : hreal) : (term114 p1 p2 p1' p1'' p2' p2'') = (term118 p1 p1' p1'' p2 p2' p2'').
Proof. exact (TRANS (@lem1328670 p1 p1' p1'' p2 p2' p2'') (@lem1328673 p1 p1' p1'' p2 p2' p2'')). Qed.
Lemma lem1328690 (p1 : hreal) (p1' : hreal) (p1'' : hreal) (p2 : hreal) (p2' : hreal) (p2'' : hreal) : (term108 p1 p2 p1' p1'' p2' p2'') = (term121 p1 p1' p1'' p2 p2' p2'').
Proof. exact (MK_COMB (@lem1328634 p1 p1' p2'' p2 p2' p1'') (@lem1328689 p1 p1' p1'' p2 p2' p2'')). Qed.
Lemma lem1328721 (p1 : hreal) (p1' : hreal) (p1'' : hreal) (p2 : hreal) (p2' : hreal) (p2'' : hreal) : (term107 p1 p2 p1' p2'' p2' p1'') = (term121 p1 p1' p1'' p2 p2' p2'').
Proof. exact (TRANS (@lem1328592 p1 p2 p1' p1'' p2' p2'') (@lem1328690 p1 p1' p1'' p2 p2' p2'')). Qed.
Lemma lem1328722 (p1 : hreal) (p1' : hreal) (p1'' : hreal) (p2 : hreal) (p2' : hreal) (p2'' : hreal) : (term104 p1 p2 p1' p2' p1'' p2'') = (term121 p1 p1' p1'' p2 p2' p2'').
Proof. exact (TRANS (@lem1328589 p1 p2 p1' p2'' p2' p1'') (@lem1328721 p1 p1' p1'' p2 p2' p2'')). Qed.
Lemma lem1328723 : (@eq (prod hreal hreal)) = (@eq (prod hreal hreal)).
Proof. exact (eq_refl (@eq (prod hreal hreal))). Qed.
Lemma lem1328724 (p1 : hreal) (p1' : hreal) (p1'' : hreal) (p2 : hreal) (p2' : hreal) (p2'' : hreal) : (term122 p1 p2 p1' p2' p1'' p2'') = (term123 p1 p1' p1'' p2 p2' p2'').
Proof. exact (MK_COMB (@lem1328723) (@lem1328722 p1 p1' p1'' p2 p2' p2'')). Qed.
Lemma lem1328756 (x1 : hreal) (y2 : hreal) (y1 : hreal) (x2 : hreal) : (term39 x1 y1 x2 y2) = (term40 x1 y2 y1 x2).
Proof. exact (EQ_MP (@lem1328449 x1 y2 y1 x2) (@lem1328448 x1 y2 y1 x2)). Qed.
Lemma lem1328757 (p1 : hreal) (p2' : hreal) (p2 : hreal) (p1' : hreal) : (term39 p1 p2 p1' p2') = (term40 p1 p2' p2 p1').
Proof. exact (@lem1328756 p1 p2' p2 p1'). Qed.
Lemma lem1328764 : treal_mul = treal_mul.
Proof. exact (eq_refl treal_mul). Qed.
Lemma lem1328765 (p1 : hreal) (p2' : hreal) (p2 : hreal) (p1' : hreal) : (term124 p1 p2 p1' p2') = (term125 p1 p2' p2 p1').
Proof. exact (MK_COMB (@lem1328764) (@lem1328757 p1 p2' p2 p1')). Qed.
Lemma lem1328772 (p1'' : hreal) (p2'' : hreal) : (@pair hreal hreal p1'' p2'') = (@pair hreal hreal p1'' p2'').
Proof. exact (eq_refl (@pair hreal hreal p1'' p2'')). Qed.
Lemma lem1328773 (p1 : hreal) (p2' : hreal) (p2 : hreal) (p1' : hreal) (p1'' : hreal) (p2'' : hreal) : (term105 p1 p2 p1' p2' p1'' p2'') = (term126 p1 p2' p2 p1' p1'' p2'').
Proof. exact (MK_COMB (@lem1328765 p1 p2' p2 p1') (@lem1328772 p1'' p2'')). Qed.
Lemma lem1328775 (x1 : hreal) (y2 : hreal) (y1 : hreal) (x2 : hreal) : (term39 x1 y1 x2 y2) = (term40 x1 y2 y1 x2).
Proof. exact (EQ_MP (@lem1328449 x1 y2 y1 x2) (@lem1328448 x1 y2 y1 x2)). Qed.
Lemma lem1328776 (p2'' : hreal) (p1 : hreal) (p2' : hreal) (p2 : hreal) (p1' : hreal) (p1'' : hreal) : (term126 p1 p2' p2 p1' p1'' p2'') = (term127 p2'' p1 p2' p2 p1' p1'').
Proof. exact (@lem1328775 (term109 p1 p1' p2 p2') p2'' (term109 p1 p2' p2 p1') p1''). Qed.
Lemma lem1328781 (m : hreal) (n : hreal) (p : hreal) : (term23 m n p) = (term24 m n p).
Proof. exact (EQ_MP (@lem1328428 m n p) (@lem1328427 m n p)). Qed.
Lemma lem1328782 (p1 : hreal) (p1' : hreal) (p2 : hreal) (p2' : hreal) (p1'' : hreal) : (term128 p1 p1' p2 p2' p1'') = (term129 p1 p1' p2 p2' p1'').
Proof. exact (@lem1328781 (hreal_mul p1 p1') (hreal_mul p2 p2') p1''). Qed.
Lemma lem1328787 (x : hreal) (y : hreal) (z : hreal) : (term1 x y z) = (term0 x y z).
Proof. exact (EQ_MP (@lem1328419 x y z) (@lem1328418 x y z)). Qed.
Lemma lem1328788 (p1 : hreal) (p1' : hreal) (p1'' : hreal) : (term1 p1 p1' p1'') = (term0 p1 p1' p1'').
Proof. exact (@lem1328787 p1 p1' p1''). Qed.
Lemma lem1328789 : hreal_add = hreal_add.
Proof. exact (eq_refl hreal_add). Qed.
Lemma lem1328790 (p1 : hreal) (p1' : hreal) (p1'' : hreal) : (term130 p1 p1' p1'') = (term131 p1 p1' p1'').
Proof. exact (MK_COMB (@lem1328789) (@lem1328788 p1 p1' p1'')). Qed.
Lemma lem1328792 (x : hreal) (y : hreal) (z : hreal) : (term1 x y z) = (term0 x y z).
Proof. exact (EQ_MP (@lem1328419 x y z) (@lem1328418 x y z)). Qed.
Lemma lem1328793 (p2 : hreal) (p2' : hreal) (p1'' : hreal) : (term1 p2 p2' p1'') = (term0 p2 p2' p1'').
Proof. exact (@lem1328792 p2 p2' p1''). Qed.
Lemma lem1328794 (p1 : hreal) (p1' : hreal) (p2 : hreal) (p2' : hreal) (p1'' : hreal) : (term129 p1 p1' p2 p2' p1'') = (term132 p1 p1' p2 p2' p1'').
Proof. exact (MK_COMB (@lem1328790 p1 p1' p1'') (@lem1328793 p2 p2' p1'')). Qed.
Lemma lem1328798 (p1 : hreal) (p1' : hreal) (p2 : hreal) (p2' : hreal) (p1'' : hreal) : (term128 p1 p1' p2 p2' p1'') = (term132 p1 p1' p2 p2' p1'').
Proof. exact (TRANS (@lem1328782 p1 p1' p2 p2' p1'') (@lem1328794 p1 p1' p2 p2' p1'')). Qed.
Lemma lem1328799 : hreal_add = hreal_add.
Proof. exact (eq_refl hreal_add). Qed.
Lemma lem1328800 (p1 : hreal) (p1' : hreal) (p2 : hreal) (p2' : hreal) (p1'' : hreal) : (term133 p1 p1' p2 p2' p1'') = (term134 p1 p1' p2 p2' p1'').
Proof. exact (MK_COMB (@lem1328799) (@lem1328798 p1 p1' p2 p2' p1'')). Qed.
Lemma lem1328805 (m : hreal) (n : hreal) (p : hreal) : (term23 m n p) = (term24 m n p).
Proof. exact (EQ_MP (@lem1328428 m n p) (@lem1328427 m n p)). Qed.
Lemma lem1328806 (p1 : hreal) (p2' : hreal) (p2 : hreal) (p1' : hreal) (p2'' : hreal) : (term128 p1 p2' p2 p1' p2'') = (term129 p1 p2' p2 p1' p2'').
Proof. exact (@lem1328805 (hreal_mul p1 p2') (hreal_mul p2 p1') p2''). Qed.
Lemma lem1328811 (x : hreal) (y : hreal) (z : hreal) : (term1 x y z) = (term0 x y z).
Proof. exact (EQ_MP (@lem1328419 x y z) (@lem1328418 x y z)). Qed.
Lemma lem1328812 (p1 : hreal) (p2' : hreal) (p2'' : hreal) : (term1 p1 p2' p2'') = (term0 p1 p2' p2'').
Proof. exact (@lem1328811 p1 p2' p2''). Qed.
Lemma lem1328813 : hreal_add = hreal_add.
Proof. exact (eq_refl hreal_add). Qed.
Lemma lem1328814 (p1 : hreal) (p2' : hreal) (p2'' : hreal) : (term130 p1 p2' p2'') = (term131 p1 p2' p2'').
Proof. exact (MK_COMB (@lem1328813) (@lem1328812 p1 p2' p2'')). Qed.
Lemma lem1328816 (x : hreal) (y : hreal) (z : hreal) : (term1 x y z) = (term0 x y z).
Proof. exact (EQ_MP (@lem1328419 x y z) (@lem1328418 x y z)). Qed.
Lemma lem1328817 (p2 : hreal) (p1' : hreal) (p2'' : hreal) : (term1 p2 p1' p2'') = (term0 p2 p1' p2'').
Proof. exact (@lem1328816 p2 p1' p2''). Qed.
Lemma lem1328818 (p1 : hreal) (p2' : hreal) (p2 : hreal) (p1' : hreal) (p2'' : hreal) : (term129 p1 p2' p2 p1' p2'') = (term132 p1 p2' p2 p1' p2'').
Proof. exact (MK_COMB (@lem1328814 p1 p2' p2'') (@lem1328817 p2 p1' p2'')). Qed.
Lemma lem1328822 (p1 : hreal) (p2' : hreal) (p2 : hreal) (p1' : hreal) (p2'' : hreal) : (term128 p1 p2' p2 p1' p2'') = (term132 p1 p2' p2 p1' p2'').
Proof. exact (TRANS (@lem1328806 p1 p2' p2 p1' p2'') (@lem1328818 p1 p2' p2 p1' p2'')). Qed.
Lemma lem1328823 (p1'' : hreal) (p1 : hreal) (p2' : hreal) (p2 : hreal) (p1' : hreal) (p2'' : hreal) : (term135 p1'' p1 p2' p2 p1' p2'') = (term136 p1'' p1 p2' p2 p1' p2'').
Proof. exact (MK_COMB (@lem1328800 p1 p1' p2 p2' p1'') (@lem1328822 p1 p2' p2 p1' p2'')). Qed.
Lemma lem1328825 (m : hreal) (n : hreal) (p : hreal) : (term116 m n p) = (term117 m n p).
Proof. exact (proj1 (@lem1328408 n m p)). Qed.
Lemma lem1328826 (p1'' : hreal) (p1 : hreal) (p2' : hreal) (p2 : hreal) (p1' : hreal) (p2'' : hreal) : (term136 p1'' p1 p2' p2 p1' p2'') = (term137 p1'' p1 p2' p2 p1' p2'').
Proof. exact (@lem1328825 (term0 p1 p1' p1'') (term0 p2 p2' p1'') (term132 p1 p2' p2 p1' p2'')). Qed.
Lemma lem1328834 (n : hreal) (m : hreal) (p : hreal) : (term117 m n p) = (term117 n m p).
Proof. exact (proj2 (@lem1328408 n m p)). Qed.
Lemma lem1328835 (p1 : hreal) (p2' : hreal) (p1'' : hreal) (p2 : hreal) (p1' : hreal) (p2'' : hreal) : (term138 p1'' p1 p2' p2 p1' p2'') = (term139 p1 p2' p1'' p2 p1' p2'').
Proof. exact (@lem1328834 (term0 p1 p2' p2'') (term0 p2 p2' p1'') (term0 p2 p1' p2'')). Qed.
Lemma lem1328843 (n : hreal) (m : hreal) : (hreal_add m n) = (hreal_add n m).
Proof. exact (proj1 (@lem1322003 n m (@el hreal))). Qed.
Lemma lem1328844 (p1' : hreal) (p2'' : hreal) (p2 : hreal) (p2' : hreal) (p1'' : hreal) : (term111 p2' p1'' p2 p1' p2'') = (term111 p1' p2'' p2 p2' p1'').
Proof. exact (@lem1328843 (term0 p2 p1' p2'') (term0 p2 p2' p1'')). Qed.
Lemma lem1328848 (p1 : hreal) (p2' : hreal) (p2'' : hreal) : (term131 p1 p2' p2'') = (term131 p1 p2' p2'').
Proof. exact (eq_refl (term131 p1 p2' p2'')). Qed.
Lemma lem1328849 (p1 : hreal) (p1' : hreal) (p2'' : hreal) (p2 : hreal) (p2' : hreal) (p1'' : hreal) : (term139 p1 p2' p1'' p2 p1' p2'') = (term140 p1 p1' p2'' p2 p2' p1'').
Proof. exact (MK_COMB (@lem1328848 p1 p2' p2'') (@lem1328844 p1' p2'' p2 p2' p1'')). Qed.
Lemma lem1328859 (p1 : hreal) (p1' : hreal) (p2'' : hreal) (p2 : hreal) (p2' : hreal) (p1'' : hreal) : (term138 p1'' p1 p2' p2 p1' p2'') = (term140 p1 p1' p2'' p2 p2' p1'').
Proof. exact (TRANS (@lem1328835 p1 p2' p1'' p2 p1' p2'') (@lem1328849 p1 p1' p2'' p2 p2' p1'')). Qed.
Lemma lem1328860 (p1 : hreal) (p1' : hreal) (p1'' : hreal) : (term131 p1 p1' p1'') = (term131 p1 p1' p1'').
Proof. exact (eq_refl (term131 p1 p1' p1'')). Qed.
Lemma lem1328861 (p1 : hreal) (p1' : hreal) (p2'' : hreal) (p2 : hreal) (p2' : hreal) (p1'' : hreal) : (term137 p1'' p1 p2' p2 p1' p2'') = (term118 p1 p1' p2'' p2 p2' p1'').
Proof. exact (MK_COMB (@lem1328860 p1 p1' p1'') (@lem1328859 p1 p1' p2'' p2 p2' p1'')). Qed.
Lemma lem1328877 (p1 : hreal) (p1' : hreal) (p2'' : hreal) (p2 : hreal) (p2' : hreal) (p1'' : hreal) : (term136 p1'' p1 p2' p2 p1' p2'') = (term118 p1 p1' p2'' p2 p2' p1'').
Proof. exact (TRANS (@lem1328826 p1'' p1 p2' p2 p1' p2'') (@lem1328861 p1 p1' p2'' p2 p2' p1'')). Qed.
Lemma lem1328878 (p1 : hreal) (p1' : hreal) (p2'' : hreal) (p2 : hreal) (p2' : hreal) (p1'' : hreal) : (term135 p1'' p1 p2' p2 p1' p2'') = (term118 p1 p1' p2'' p2 p2' p1'').
Proof. exact (TRANS (@lem1328823 p1'' p1 p2' p2 p1' p2'') (@lem1328877 p1 p1' p2'' p2 p2' p1'')). Qed.
Lemma lem1328879 : (@pair hreal hreal) = (@pair hreal hreal).
Proof. exact (eq_refl (@pair hreal hreal)). Qed.
Lemma lem1328880 (p1 : hreal) (p1' : hreal) (p2'' : hreal) (p2 : hreal) (p2' : hreal) (p1'' : hreal) : (term141 p1'' p1 p2' p2 p1' p2'') = (term120 p1 p1' p2'' p2 p2' p1'').
Proof. exact (MK_COMB (@lem1328879) (@lem1328878 p1 p1' p2'' p2 p2' p1'')). Qed.
Lemma lem1328900 (m : hreal) (n : hreal) (p : hreal) : (term23 m n p) = (term24 m n p).
Proof. exact (EQ_MP (@lem1328428 m n p) (@lem1328427 m n p)). Qed.
Lemma lem1328901 (p1 : hreal) (p1' : hreal) (p2 : hreal) (p2' : hreal) (p2'' : hreal) : (term128 p1 p1' p2 p2' p2'') = (term129 p1 p1' p2 p2' p2'').
Proof. exact (@lem1328900 (hreal_mul p1 p1') (hreal_mul p2 p2') p2''). Qed.
Lemma lem1328906 (x : hreal) (y : hreal) (z : hreal) : (term1 x y z) = (term0 x y z).
Proof. exact (EQ_MP (@lem1328419 x y z) (@lem1328418 x y z)). Qed.
Lemma lem1328907 (p1 : hreal) (p1' : hreal) (p2'' : hreal) : (term1 p1 p1' p2'') = (term0 p1 p1' p2'').
Proof. exact (@lem1328906 p1 p1' p2''). Qed.
Lemma lem1328908 : hreal_add = hreal_add.
Proof. exact (eq_refl hreal_add). Qed.
Lemma lem1328909 (p1 : hreal) (p1' : hreal) (p2'' : hreal) : (term130 p1 p1' p2'') = (term131 p1 p1' p2'').
Proof. exact (MK_COMB (@lem1328908) (@lem1328907 p1 p1' p2'')). Qed.
Lemma lem1328911 (x : hreal) (y : hreal) (z : hreal) : (term1 x y z) = (term0 x y z).
Proof. exact (EQ_MP (@lem1328419 x y z) (@lem1328418 x y z)). Qed.
Lemma lem1328912 (p2 : hreal) (p2' : hreal) (p2'' : hreal) : (term1 p2 p2' p2'') = (term0 p2 p2' p2'').
Proof. exact (@lem1328911 p2 p2' p2''). Qed.
Lemma lem1328913 (p1 : hreal) (p1' : hreal) (p2 : hreal) (p2' : hreal) (p2'' : hreal) : (term129 p1 p1' p2 p2' p2'') = (term132 p1 p1' p2 p2' p2'').
Proof. exact (MK_COMB (@lem1328909 p1 p1' p2'') (@lem1328912 p2 p2' p2'')). Qed.
Lemma lem1328917 (p1 : hreal) (p1' : hreal) (p2 : hreal) (p2' : hreal) (p2'' : hreal) : (term128 p1 p1' p2 p2' p2'') = (term132 p1 p1' p2 p2' p2'').
Proof. exact (TRANS (@lem1328901 p1 p1' p2 p2' p2'') (@lem1328913 p1 p1' p2 p2' p2'')). Qed.
Lemma lem1328918 : hreal_add = hreal_add.
Proof. exact (eq_refl hreal_add). Qed.
Lemma lem1328919 (p1 : hreal) (p1' : hreal) (p2 : hreal) (p2' : hreal) (p2'' : hreal) : (term133 p1 p1' p2 p2' p2'') = (term134 p1 p1' p2 p2' p2'').
Proof. exact (MK_COMB (@lem1328918) (@lem1328917 p1 p1' p2 p2' p2'')). Qed.
Lemma lem1328924 (m : hreal) (n : hreal) (p : hreal) : (term23 m n p) = (term24 m n p).
Proof. exact (EQ_MP (@lem1328428 m n p) (@lem1328427 m n p)). Qed.
Lemma lem1328925 (p1 : hreal) (p2' : hreal) (p2 : hreal) (p1' : hreal) (p1'' : hreal) : (term128 p1 p2' p2 p1' p1'') = (term129 p1 p2' p2 p1' p1'').
Proof. exact (@lem1328924 (hreal_mul p1 p2') (hreal_mul p2 p1') p1''). Qed.
Lemma lem1328930 (x : hreal) (y : hreal) (z : hreal) : (term1 x y z) = (term0 x y z).
Proof. exact (EQ_MP (@lem1328419 x y z) (@lem1328418 x y z)). Qed.
Lemma lem1328931 (p1 : hreal) (p2' : hreal) (p1'' : hreal) : (term1 p1 p2' p1'') = (term0 p1 p2' p1'').
Proof. exact (@lem1328930 p1 p2' p1''). Qed.
Lemma lem1328932 : hreal_add = hreal_add.
Proof. exact (eq_refl hreal_add). Qed.
Lemma lem1328933 (p1 : hreal) (p2' : hreal) (p1'' : hreal) : (term130 p1 p2' p1'') = (term131 p1 p2' p1'').
Proof. exact (MK_COMB (@lem1328932) (@lem1328931 p1 p2' p1'')). Qed.
Lemma lem1328935 (x : hreal) (y : hreal) (z : hreal) : (term1 x y z) = (term0 x y z).
Proof. exact (EQ_MP (@lem1328419 x y z) (@lem1328418 x y z)). Qed.
Lemma lem1328936 (p2 : hreal) (p1' : hreal) (p1'' : hreal) : (term1 p2 p1' p1'') = (term0 p2 p1' p1'').
Proof. exact (@lem1328935 p2 p1' p1''). Qed.
Lemma lem1328937 (p1 : hreal) (p2' : hreal) (p2 : hreal) (p1' : hreal) (p1'' : hreal) : (term129 p1 p2' p2 p1' p1'') = (term132 p1 p2' p2 p1' p1'').
Proof. exact (MK_COMB (@lem1328933 p1 p2' p1'') (@lem1328936 p2 p1' p1'')). Qed.
Lemma lem1328941 (p1 : hreal) (p2' : hreal) (p2 : hreal) (p1' : hreal) (p1'' : hreal) : (term128 p1 p2' p2 p1' p1'') = (term132 p1 p2' p2 p1' p1'').
Proof. exact (TRANS (@lem1328925 p1 p2' p2 p1' p1'') (@lem1328937 p1 p2' p2 p1' p1'')). Qed.
Lemma lem1328942 (p2'' : hreal) (p1 : hreal) (p2' : hreal) (p2 : hreal) (p1' : hreal) (p1'' : hreal) : (term135 p2'' p1 p2' p2 p1' p1'') = (term136 p2'' p1 p2' p2 p1' p1'').
Proof. exact (MK_COMB (@lem1328919 p1 p1' p2 p2' p2'') (@lem1328941 p1 p2' p2 p1' p1'')). Qed.
Lemma lem1328944 (m : hreal) (n : hreal) (p : hreal) : (term116 m n p) = (term117 m n p).
Proof. exact (proj1 (@lem1328408 n m p)). Qed.
Lemma lem1328945 (p2'' : hreal) (p1 : hreal) (p2' : hreal) (p2 : hreal) (p1' : hreal) (p1'' : hreal) : (term136 p2'' p1 p2' p2 p1' p1'') = (term137 p2'' p1 p2' p2 p1' p1'').
Proof. exact (@lem1328944 (term0 p1 p1' p2'') (term0 p2 p2' p2'') (term132 p1 p2' p2 p1' p1'')). Qed.
Lemma lem1328953 (n : hreal) (m : hreal) (p : hreal) : (term117 m n p) = (term117 n m p).
Proof. exact (proj2 (@lem1328408 n m p)). Qed.
Lemma lem1328954 (p1 : hreal) (p2' : hreal) (p2'' : hreal) (p2 : hreal) (p1' : hreal) (p1'' : hreal) : (term138 p2'' p1 p2' p2 p1' p1'') = (term139 p1 p2' p2'' p2 p1' p1'').
Proof. exact (@lem1328953 (term0 p1 p2' p1'') (term0 p2 p2' p2'') (term0 p2 p1' p1'')). Qed.
Lemma lem1328962 (n : hreal) (m : hreal) : (hreal_add m n) = (hreal_add n m).
Proof. exact (proj1 (@lem1322003 n m (@el hreal))). Qed.
Lemma lem1328963 (p1' : hreal) (p1'' : hreal) (p2 : hreal) (p2' : hreal) (p2'' : hreal) : (term111 p2' p2'' p2 p1' p1'') = (term111 p1' p1'' p2 p2' p2'').
Proof. exact (@lem1328962 (term0 p2 p1' p1'') (term0 p2 p2' p2'')). Qed.
Lemma lem1328967 (p1 : hreal) (p2' : hreal) (p1'' : hreal) : (term131 p1 p2' p1'') = (term131 p1 p2' p1'').
Proof. exact (eq_refl (term131 p1 p2' p1'')). Qed.
Lemma lem1328968 (p1 : hreal) (p1' : hreal) (p1'' : hreal) (p2 : hreal) (p2' : hreal) (p2'' : hreal) : (term139 p1 p2' p2'' p2 p1' p1'') = (term140 p1 p1' p1'' p2 p2' p2'').
Proof. exact (MK_COMB (@lem1328967 p1 p2' p1'') (@lem1328963 p1' p1'' p2 p2' p2'')). Qed.
Lemma lem1328978 (p1 : hreal) (p1' : hreal) (p1'' : hreal) (p2 : hreal) (p2' : hreal) (p2'' : hreal) : (term138 p2'' p1 p2' p2 p1' p1'') = (term140 p1 p1' p1'' p2 p2' p2'').
Proof. exact (TRANS (@lem1328954 p1 p2' p2'' p2 p1' p1'') (@lem1328968 p1 p1' p1'' p2 p2' p2'')). Qed.
Lemma lem1328979 (p1 : hreal) (p1' : hreal) (p2'' : hreal) : (term131 p1 p1' p2'') = (term131 p1 p1' p2'').
Proof. exact (eq_refl (term131 p1 p1' p2'')). Qed.
Lemma lem1328980 (p1 : hreal) (p1' : hreal) (p1'' : hreal) (p2 : hreal) (p2' : hreal) (p2'' : hreal) : (term137 p2'' p1 p2' p2 p1' p1'') = (term118 p1 p1' p1'' p2 p2' p2'').
Proof. exact (MK_COMB (@lem1328979 p1 p1' p2'') (@lem1328978 p1 p1' p1'' p2 p2' p2'')). Qed.
Lemma lem1328996 (p1 : hreal) (p1' : hreal) (p1'' : hreal) (p2 : hreal) (p2' : hreal) (p2'' : hreal) : (term136 p2'' p1 p2' p2 p1' p1'') = (term118 p1 p1' p1'' p2 p2' p2'').
Proof. exact (TRANS (@lem1328945 p2'' p1 p2' p2 p1' p1'') (@lem1328980 p1 p1' p1'' p2 p2' p2'')). Qed.
Lemma lem1328997 (p1 : hreal) (p1' : hreal) (p1'' : hreal) (p2 : hreal) (p2' : hreal) (p2'' : hreal) : (term135 p2'' p1 p2' p2 p1' p1'') = (term118 p1 p1' p1'' p2 p2' p2'').
Proof. exact (TRANS (@lem1328942 p2'' p1 p2' p2 p1' p1'') (@lem1328996 p1 p1' p1'' p2 p2' p2'')). Qed.
Lemma lem1328998 (p1 : hreal) (p1' : hreal) (p1'' : hreal) (p2 : hreal) (p2' : hreal) (p2'' : hreal) : (term127 p2'' p1 p2' p2 p1' p1'') = (term121 p1 p1' p1'' p2 p2' p2'').
Proof. exact (MK_COMB (@lem1328880 p1 p1' p2'' p2 p2' p1'') (@lem1328997 p1 p1' p1'' p2 p2' p2'')). Qed.
Lemma lem1329029 (p1 : hreal) (p1' : hreal) (p1'' : hreal) (p2 : hreal) (p2' : hreal) (p2'' : hreal) : (term126 p1 p2' p2 p1' p1'' p2'') = (term121 p1 p1' p1'' p2 p2' p2'').
Proof. exact (TRANS (@lem1328776 p2'' p1 p2' p2 p1' p1'') (@lem1328998 p1 p1' p1'' p2 p2' p2'')). Qed.
Lemma lem1329030 (p1 : hreal) (p1' : hreal) (p1'' : hreal) (p2 : hreal) (p2' : hreal) (p2'' : hreal) : (term105 p1 p2 p1' p2' p1'' p2'') = (term121 p1 p1' p1'' p2 p2' p2'').
Proof. exact (TRANS (@lem1328773 p1 p2' p2 p1' p1'' p2'') (@lem1329029 p1 p1' p1'' p2 p2' p2'')). Qed.
Lemma lem1329031 (p1 : hreal) (p1' : hreal) (p1'' : hreal) (p2 : hreal) (p2' : hreal) (p2'' : hreal) : ((term104 p1 p2 p1' p2' p1'' p2'') = (term105 p1 p2 p1' p2' p1'' p2'')) = ((term121 p1 p1' p1'' p2 p2' p2'') = (term121 p1 p1' p1'' p2 p2' p2'')).
Proof. exact (MK_COMB (@lem1328724 p1 p1' p1'' p2 p2' p2'') (@lem1329030 p1 p1' p1'' p2 p2' p2'')). Qed.
Lemma lem1329033 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1329034 (x : prod hreal hreal) : (x = x) = True.
Proof. exact (@lem1329033 (prod hreal hreal) x). Qed.
Lemma lem1329035 (p1 : hreal) (p1' : hreal) (p1'' : hreal) (p2 : hreal) (p2' : hreal) (p2'' : hreal) : ((term121 p1 p1' p1'' p2 p2' p2'') = (term121 p1 p1' p1'' p2 p2' p2'')) = True.
Proof. exact (@lem1329034 (term121 p1 p1' p1'' p2 p2' p2'')). Qed.
Lemma lem1329036 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) (p1'' : hreal) (p2'' : hreal) : ((term104 p1 p2 p1' p2' p1'' p2'') = (term105 p1 p2 p1' p2' p1'' p2'')) = True.
Proof. exact (TRANS (@lem1329031 p1 p1' p1'' p2 p2' p2'') (@lem1329035 p1 p1' p1'' p2 p2' p2'')). Qed.
Lemma lem1329037 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) (p1'' : hreal) (p2'' : hreal) : True = ((term104 p1 p2 p1' p2' p1'' p2'') = (term105 p1 p2 p1' p2' p1'' p2'')).
Proof. exact (SYM (@lem1329036 p1 p2 p1' p2' p1'' p2'')). Qed.
Lemma lem1329038 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) (p1'' : hreal) (p2'' : hreal) : (term104 p1 p2 p1' p2' p1'' p2'') = (term105 p1 p2 p1' p2' p1'' p2'').
Proof. exact (EQ_MP (@lem1329037 p1 p2 p1' p2' p1'' p2'') (@lem0)). Qed.
Lemma lem1329039 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) (p1'' : hreal) (p2'' : hreal) : (term94 p1 p2 p1' p2' p1'' p2'') = True.
Proof. exact (@lem1328576 p1 p2 p1' p2' p1'' p2'' (@lem1329038 p1 p2 p1' p2' p1'' p2'')). Qed.
Lemma lem1329040 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) (p1'' : hreal) : (term96 p1 p2 p1' p2' p1'') = term142.
Proof. exact (fun_ext (fun p2'' : hreal => @lem1329039 p1 p2 p1' p2' p1'' p2'')). Qed.
Lemma lem1329041 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1329042 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) (p1'' : hreal) : (term98 p1 p2 p1' p2' p1'') = term143.
Proof. exact (MK_COMB (@lem1329041) (@lem1329040 p1 p2 p1' p2' p1'')). Qed.
Lemma lem1329044 {A : Type'} (t : Prop) : (term144 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1329045 (t : Prop) : (term145 t) = t.
Proof. exact (@lem1329044 hreal t). Qed.
Lemma lem1329046 : term143 = True.
Proof. exact (@lem1329045 True). Qed.
Lemma lem1329047 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) (p1'' : hreal) : (term98 p1 p2 p1' p2' p1'') = True.
Proof. exact (TRANS (@lem1329042 p1 p2 p1' p2' p1'') (@lem1329046)). Qed.
Lemma lem1329048 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : (term100 p1 p2 p1' p2') = term142.
Proof. exact (fun_ext (fun p1'' : hreal => @lem1329047 p1 p2 p1' p2' p1'')). Qed.
Lemma lem1329049 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1329050 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : (term101 p1 p2 p1' p2') = term143.
Proof. exact (MK_COMB (@lem1329049) (@lem1329048 p1 p2 p1' p2')). Qed.
Lemma lem1329052 {A : Type'} (t : Prop) : (term144 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1329053 (t : Prop) : (term145 t) = t.
Proof. exact (@lem1329052 hreal t). Qed.
Lemma lem1329054 : term143 = True.
Proof. exact (@lem1329053 True). Qed.
Lemma lem1329055 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : (term101 p1 p2 p1' p2') = True.
Proof. exact (TRANS (@lem1329050 p1 p2 p1' p2') (@lem1329054)). Qed.
Lemma lem1329056 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : (term77 p1 p2 p1' p2') = True.
Proof. exact (TRANS (@lem1328561 p1 p2 p1' p2') (@lem1329055 p1 p2 p1' p2')). Qed.
Lemma lem1329057 (p1 : hreal) (p2 : hreal) (p1' : hreal) : (term79 p1 p2 p1') = term142.
Proof. exact (fun_ext (fun p2' : hreal => @lem1329056 p1 p2 p1' p2')). Qed.
Lemma lem1329058 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1329059 (p1 : hreal) (p2 : hreal) (p1' : hreal) : (term81 p1 p2 p1') = term143.
Proof. exact (MK_COMB (@lem1329058) (@lem1329057 p1 p2 p1')). Qed.
Lemma lem1329061 {A : Type'} (t : Prop) : (term144 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1329062 (t : Prop) : (term145 t) = t.
Proof. exact (@lem1329061 hreal t). Qed.
Lemma lem1329063 : term143 = True.
Proof. exact (@lem1329062 True). Qed.
Lemma lem1329064 (p1 : hreal) (p2 : hreal) (p1' : hreal) : (term81 p1 p2 p1') = True.
Proof. exact (TRANS (@lem1329059 p1 p2 p1') (@lem1329063)). Qed.
Lemma lem1329065 (p1 : hreal) (p2 : hreal) : (term83 p1 p2) = term142.
Proof. exact (fun_ext (fun p1' : hreal => @lem1329064 p1 p2 p1')). Qed.
Lemma lem1329066 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1329067 (p1 : hreal) (p2 : hreal) : (term84 p1 p2) = term143.
Proof. exact (MK_COMB (@lem1329066) (@lem1329065 p1 p2)). Qed.
Lemma lem1329069 {A : Type'} (t : Prop) : (term144 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1329070 (t : Prop) : (term145 t) = t.
Proof. exact (@lem1329069 hreal t). Qed.
Lemma lem1329071 : term143 = True.
Proof. exact (@lem1329070 True). Qed.
Lemma lem1329072 (p1 : hreal) (p2 : hreal) : (term84 p1 p2) = True.
Proof. exact (TRANS (@lem1329067 p1 p2) (@lem1329071)). Qed.
Lemma lem1329073 (p1 : hreal) (p2 : hreal) : (term60 p1 p2) = True.
Proof. exact (TRANS (@lem1328526 p1 p2) (@lem1329072 p1 p2)). Qed.
Lemma lem1329074 (p1 : hreal) : (term62 p1) = term142.
Proof. exact (fun_ext (fun p2 : hreal => @lem1329073 p1 p2)). Qed.
Lemma lem1329075 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1329076 (p1 : hreal) : (term64 p1) = term143.
Proof. exact (MK_COMB (@lem1329075) (@lem1329074 p1)). Qed.
Lemma lem1329078 {A : Type'} (t : Prop) : (term144 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1329079 (t : Prop) : (term145 t) = t.
Proof. exact (@lem1329078 hreal t). Qed.
Lemma lem1329080 : term143 = True.
Proof. exact (@lem1329079 True). Qed.
Lemma lem1329081 (p1 : hreal) : (term64 p1) = True.
Proof. exact (TRANS (@lem1329076 p1) (@lem1329080)). Qed.
Lemma lem1329082 : term66 = term142.
Proof. exact (fun_ext (fun p1 : hreal => @lem1329081 p1)). Qed.
Lemma lem1329083 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1329084 : term67 = term143.
Proof. exact (MK_COMB (@lem1329083) (@lem1329082)). Qed.
Lemma lem1329086 {A : Type'} (t : Prop) : (term144 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1329087 (t : Prop) : (term145 t) = t.
Proof. exact (@lem1329086 hreal t). Qed.
Lemma lem1329088 : term143 = True.
Proof. exact (@lem1329087 True). Qed.
Lemma lem1329089 : term67 = True.
Proof. exact (TRANS (@lem1329084) (@lem1329088)). Qed.
Lemma lem1329090 : term56 = True.
Proof. exact (TRANS (@lem1328491) (@lem1329089)). Qed.
Lemma lem1329091 : True = term56.
Proof. exact (SYM (@lem1329090)). Qed.
Lemma lem1329092 : term56.
Proof. exact (EQ_MP (@lem1329091) (@lem0)). Qed.
